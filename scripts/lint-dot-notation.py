#!/usr/bin/env python3
"""Flag Mathlib namespaces recreated inside ``namespace TauCeti``.

The lint finds declarations under ``TauCeti.<Mathlib namespace>`` with an argument of the
corresponding type. Organisational namespaces, namespaces named by a declaration in the same
file, and explicitly rooted declarations are ignored. Existing findings are grandfathered by
``scripts/lint-dot-notation-baseline.txt``; update it with ``--write-baseline``.
"""

from __future__ import annotations

import argparse
import dataclasses
import hashlib
import pathlib
import re
import sys
from collections import Counter
from collections.abc import Iterable


ORGANISATIONAL = {
    "Algebra", "AlgebraicGeometry", "Analysis", "CategoryTheory", "Combinatorics", "Complex",
    "Filter", "Finset", "Function", "Geometry", "Int", "Lie", "LinearAlgebra", "List",
    "MeasureTheory", "Nat", "NumberTheory", "Order", "Polynomial", "ProbabilityTheory",
    "Real", "RingTheory", "Set", "Topology",
}

DECLARATION_KEYWORDS = {
    "abbrev", "class", "def", "inductive", "instance", "lemma", "opaque", "structure",
    "theorem",
}
OWN_DECLARATION_KEYWORDS = {"abbrev", "class", "def", "inductive", "structure"}
MODIFIERS = {
    "noncomputable", "nonrec", "partial", "private", "protected", "public", "scoped", "unsafe",
}
IDENTIFIER = re.compile(r"(?:_root_\.)?[\w'.]+")
WORD = re.compile(r"[A-Za-z_][\w']*")
NAMESPACE = re.compile(
    r"(?m)^(?:(?:public|private|protected|noncomputable)\s+)*namespace\s+([\w'.]+)"
)


@dataclasses.dataclass(frozen=True)
class Declaration:
    keyword: str
    name: str | None
    binders: tuple[str, ...]
    header: str
    position: int


@dataclasses.dataclass(frozen=True)
class Scope:
    kind: str
    name: str | None
    components: tuple[str, ...]

    def matches(self, end_name: str) -> bool:
        return self.name == end_name or (self.kind == "namespace" and bool(self.components)
                                         and self.components[-1] == end_name)


@dataclasses.dataclass(frozen=True)
class Finding:
    path: pathlib.Path
    line: int
    declaration: str

    def render(self) -> str:
        return f"{self.path}:{self.line}: {self.declaration}"


def strip_comments_and_strings(text: str) -> str:
    """Blank comments and strings while preserving offsets and newlines."""
    chars = list(text)
    i = 0
    block_depth = 0
    in_string = False
    while i < len(chars):
        if block_depth:
            if text.startswith("/-", i):
                chars[i] = chars[i + 1] = " "
                block_depth += 1
                i += 2
            elif text.startswith("-/", i):
                chars[i] = chars[i + 1] = " "
                block_depth -= 1
                i += 2
            else:
                if chars[i] != "\n":
                    chars[i] = " "
                i += 1
        elif in_string:
            if chars[i] == "\\" and i + 1 < len(chars):
                chars[i] = " "
                if chars[i + 1] != "\n":
                    chars[i + 1] = " "
                i += 2
            else:
                if chars[i] == '"':
                    in_string = False
                if chars[i] != "\n":
                    chars[i] = " "
                i += 1
        elif text.startswith("--", i):
            while i < len(chars) and chars[i] != "\n":
                chars[i] = " "
                i += 1
        elif text.startswith("/-", i):
            chars[i] = chars[i + 1] = " "
            block_depth = 1
            i += 2
        elif chars[i] == '"':
            chars[i] = " "
            in_string = True
            i += 1
        else:
            i += 1
    return "".join(chars)


def _skip_horizontal(text: str, position: int) -> int:
    while position < len(text) and text[position] in " \t\r":
        position += 1
    return position


def _skip_balanced(text: str, position: int) -> int:
    pairs = {"(": ")", "[": "]", "{": "}"}
    if position >= len(text) or text[position] not in pairs:
        return position
    stack = [pairs[text[position]]]
    position += 1
    while position < len(text) and stack:
        char = text[position]
        if char in pairs:
            stack.append(pairs[char])
        elif char == stack[-1]:
            stack.pop()
        position += 1
    return position


def _command_prefix(text: str, line_start: int) -> tuple[int, str] | None:
    """Return the declaration keyword position and keyword for a command at ``line_start``."""
    position = _skip_horizontal(text, line_start)
    saw_attribute = False
    while text.startswith("@[", position):
        saw_attribute = True
        position = _skip_balanced(text, position + 1)
        while position < len(text) and text[position].isspace():
            position += 1

    if not saw_attribute and "\n" in text[line_start:position]:
        return None

    while True:
        match = WORD.match(text, position)
        if not match or match.group() not in MODIFIERS:
            break
        position = _skip_horizontal(text, match.end())

    match = WORD.match(text, position)
    if match and match.group() in DECLARATION_KEYWORDS:
        return position, match.group()
    return None


def _top_level_colon(group: str) -> int | None:
    depth = 0
    pairs = {"(": ")", "[": "]", "{": "}"}
    closes = set(pairs.values())
    for i, char in enumerate(group):
        if char in pairs:
            depth += 1
        elif char in closes:
            depth -= 1
        elif char == ":" and depth == 0 and not group.startswith(":=", i):
            return i
    return None


def _declaration_tail(text: str, position: int) -> tuple[tuple[str, ...], str]:
    """Collect declaration binders and the header through its body introducer."""
    binders: list[str] = []
    start = position
    while position < len(text):
        position = _skip_horizontal(text, position)
        if text.startswith(":=", position):
            break
        word = WORD.match(text, position)
        if word and word.group() == "where":
            break
        char = text[position]
        if char == ":" or char == "|":
            header_end = position
            depth = 0
            while header_end < len(text):
                if text.startswith(":=", header_end) and depth == 0:
                    break
                next_word = WORD.match(text, header_end)
                if next_word and next_word.group() == "where" and depth == 0:
                    break
                current = text[header_end]
                if current in "([{":
                    depth += 1
                elif current in ")]}":
                    depth -= 1
                elif current == "|" and depth == 0:
                    break
                header_end += 1
            return tuple(binders), text[start:header_end]
        if char in "([{":
            end = _skip_balanced(text, position)
            group = text[position + 1:end - 1]
            if _top_level_colon(group) is not None:
                binders.append(group)
            position = end
        elif char == "\n":
            position += 1
        else:
            position += 1
    return tuple(binders), text[start:position]


def declarations(text: str) -> list[Declaration]:
    code = strip_comments_and_strings(text)
    found: dict[int, Declaration] = {}
    line_start = 0
    while line_start < len(code):
        prefix = _command_prefix(code, line_start)
        if prefix is not None:
            keyword_position, keyword = prefix
            position = _skip_horizontal(code, keyword_position + len(keyword))
            name: str | None = None
            if keyword == "instance" and code.startswith("(priority", position):
                position = _skip_horizontal(code, _skip_balanced(code, position))
            if keyword != "instance" or (position < len(code) and code[position] not in "({[:"):
                match = IDENTIFIER.match(code, position)
                if match:
                    name = match.group()
                    position = match.end()
            binders, header = _declaration_tail(code, position)
            found[keyword_position] = Declaration(keyword, name, binders, header, keyword_position)
        newline = code.find("\n", line_start)
        line_start = len(code) if newline == -1 else newline + 1
    return [found[position] for position in sorted(found)]


def scopes(text: str) -> list[tuple[int, str, str | None]]:
    code = strip_comments_and_strings(text)
    pattern = re.compile(
        r"(?m)^(?:(?:public|private|protected|noncomputable)\s+)*"
        r"(?P<kind>namespace|section|end)(?:\s+(?P<name>[\w'.]+))?[ \t]*$"
    )
    return [(m.start(), m.group("kind"), m.group("name")) for m in pattern.finditer(code)]


def mathlib_namespaces(root: pathlib.Path) -> set[str]:
    if not root.is_dir():
        raise FileNotFoundError(f"Mathlib source directory not found: {root}")
    names: set[str] = set()
    for path in root.rglob("*.lean"):
        text = strip_comments_and_strings(path.read_text(errors="ignore"))
        for match in NAMESPACE.finditer(text):
            names.update(part for part in match.group(1).split(".") if part != "_root_")
    return names


def own_declarations(parsed: Iterable[Declaration]) -> set[str]:
    return {
        declaration.name.removeprefix("_root_.").split(".")[-1]
        for declaration in parsed
        if declaration.keyword in OWN_DECLARATION_KEYWORDS and declaration.name is not None
    }


def _binder_has_type(binder: str, namespace: str) -> bool:
    colon = _top_level_colon(binder)
    if colon is None:
        return False
    binder_type = binder[colon + 1:].lstrip()
    qualified = rf"(?:_root_\.)?(?:[\w']+\.)*{re.escape(namespace)}\b"
    if re.match(rf"@?{qualified}", binder_type) is None:
        return False
    depth = 0
    for position, char in enumerate(binder_type):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif depth == 0 and (char == "→" or binder_type.startswith("->", position)):
            return False
    return True


def _result_has_argument_type(header: str, namespace: str) -> bool:
    """Whether a top-level arrow in the result type has a domain named ``namespace``."""
    depth = 0
    result_start: int | None = None
    for position, char in enumerate(header):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif char == ":" and depth == 0 and not header.startswith(":=", position):
            result_start = position + 1
            break
    if result_start is None:
        return False

    result = header[result_start:]
    depth = 0
    domain_start = 0
    domains: list[str] = []
    position = 0
    while position < len(result):
        char = result[position]
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif depth == 0 and (char == "→" or result.startswith("->", position)):
            domains.append(result[domain_start:position])
            position += 1 if char == "→" else 2
            domain_start = position
            continue
        position += 1
    return any(_binder_has_type(f"_ : {domain}", namespace) for domain in domains)


def find_violations(
    sources: dict[pathlib.Path, str], mathlib_namespace_names: set[str]
) -> list[Finding]:
    findings: list[Finding] = []
    for path, text in sorted(sources.items()):
        parsed = declarations(text)
        owned = own_declarations(parsed)
        events: list[tuple[int, str, object]] = [
            (position, "scope", (kind, name)) for position, kind, name in scopes(text)
        ]
        events.extend((declaration.position, "declaration", declaration) for declaration in parsed)
        events.sort(key=lambda event: event[0])

        stack: list[Scope] = []
        for _, event_kind, payload in events:
            if event_kind == "scope":
                kind, name = payload  # type: ignore[misc]
                if kind == "namespace":
                    assert name is not None
                    stack.append(Scope(kind, name, tuple(name.split("."))))
                elif kind == "section":
                    stack.append(Scope(kind, name, ()))
                elif name is None:
                    if stack:
                        stack.pop()
                else:
                    for index in range(len(stack) - 1, -1, -1):
                        if stack[index].matches(name):
                            del stack[index:]
                            break
                continue

            declaration = payload
            assert isinstance(declaration, Declaration)
            namespaces = [component for scope in stack for component in scope.components]
            if not namespaces or namespaces[0] != "TauCeti":
                continue
            if declaration.name is not None and declaration.name.startswith("_root_."):
                continue
            candidates = [
                namespace
                for namespace in namespaces[1:]
                if namespace in mathlib_namespace_names
                and namespace not in ORGANISATIONAL
                and namespace not in owned
            ]
            matching = [
                namespace
                for namespace in candidates
                if any(_binder_has_type(binder, namespace) for binder in declaration.binders)
                or _result_has_argument_type(declaration.header, namespace)
            ]
            if not matching:
                continue

            namespace = matching[-1]
            if declaration.name is None:
                normalized = " ".join(declaration.header.split())
                digest = hashlib.sha256(normalized.encode()).hexdigest()[:12]
                declared_name = f"<anonymous instance {digest}>"
            else:
                declared_name = declaration.name
            qualified_name = ".".join([*namespaces, declared_name])
            line = text.count("\n", 0, declaration.position) + 1
            findings.append(Finding(path, line, qualified_name))

    return sorted(findings, key=lambda finding: (str(finding.path), finding.line, finding.declaration))


def baseline_key(line: str) -> str:
    try:
        return line.split(": ", 1)[1]
    except IndexError as error:
        raise ValueError(f"malformed dot-notation baseline entry: {line}") from error


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--baseline", type=pathlib.Path, default=pathlib.Path(
        "scripts/lint-dot-notation-baseline.txt"))
    parser.add_argument("--mathlib-root", type=pathlib.Path, default=pathlib.Path(
        ".lake/packages/mathlib/Mathlib"))
    parser.add_argument("--source-root", type=pathlib.Path, default=pathlib.Path("TauCeti"))
    parser.add_argument("--write-baseline", action="store_true")
    args = parser.parse_args(argv)

    try:
        namespace_names = mathlib_namespaces(args.mathlib_root)
    except FileNotFoundError as error:
        print(f"lint-dot-notation: error: {error}", file=sys.stderr)
        return 2
    if not args.source_root.is_dir():
        print(f"lint-dot-notation: error: source directory not found: {args.source_root}",
              file=sys.stderr)
        return 2

    sources = {path: path.read_text(errors="ignore")
               for path in args.source_root.rglob("*.lean")}
    found = find_violations(sources, namespace_names)

    if args.write_baseline:
        args.baseline.write_text("".join(f"{finding.render()}\n" for finding in found))
        print(f"lint-dot-notation: wrote {len(found)} baseline entries")
        return 0
    if not args.baseline.is_file():
        print(f"lint-dot-notation: error: baseline not found: {args.baseline}", file=sys.stderr)
        return 2

    baseline_lines = [line.strip() for line in args.baseline.read_text().splitlines() if line.strip()]
    try:
        known = Counter(baseline_key(line) for line in baseline_lines)
    except ValueError as error:
        print(f"lint-dot-notation: error: {error}", file=sys.stderr)
        return 2
    current = Counter(finding.declaration for finding in found)
    new_counts = current - known
    new: list[Finding] = []
    for finding in found:
        if new_counts[finding.declaration]:
            new.append(finding)
            new_counts[finding.declaration] -= 1
    fixed = sum((known - current).values())

    print(
        f"lint-dot-notation: {len(found)} total, {sum(known.values())} grandfathered, "
        f"{len(new)} new, {fixed} ratchetable"
    )
    if fixed:
        print("lint-dot-notation: baseline entries no longer found; regenerate with --write-baseline")
    if not new:
        return 0

    print("\nA Mathlib type's namespace is nested inside `namespace TauCeti`, so dot")
    print("notation on that type does not elaborate. Move the declaration to the type's")
    print("root namespace. Watch for `open` and `variable` commands that must move with it.\n")
    for finding in new:
        print(f"  {finding.render()}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
