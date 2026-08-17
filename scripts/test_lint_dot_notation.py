#!/usr/bin/env python3
"""Regression tests for ``scripts/lint-dot-notation.py``."""

from __future__ import annotations

import contextlib
import importlib.util
import io
import pathlib
import sys
import tempfile
import unittest


SCRIPT = pathlib.Path(__file__).with_name("lint-dot-notation.py")
SPEC = importlib.util.spec_from_file_location("lint_dot_notation", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
lint = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = lint
SPEC.loader.exec_module(lint)


def findings(source: str, namespaces: set[str] | None = None):
    return lint.find_violations({pathlib.Path("TauCeti/Test.lean"): source}, namespaces or {"Foo"})


class DotNotationLintTests(unittest.TestCase):
    def test_named_section_does_not_corrupt_namespace_stack(self):
        source = """\
namespace TauCeti
namespace Foo
def before (x : Foo) := x
section Chain
def inside (x : Foo) := x
end Chain
def after (x : Foo) := x
end Foo
end TauCeti
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["TauCeti.Foo.before", "TauCeti.Foo.inside", "TauCeti.Foo.after"])

    def test_attribute_anonymous_instance_and_modifiers_are_detected(self):
        source = """\
namespace TauCeti
namespace Foo
@[expose] def attributed : Foo → Foo := fun x => x
@[simp,
  expose] theorem multilineAttribute (x : Foo) : True := True.intro
instance (x : Foo) : Inhabited Foo := ⟨x⟩
instance (priority := 100) (x : Foo) : Inhabited Foo := ⟨x⟩
nonrec def nonrecursive (x : Foo) := x
scoped instance namedInstance (x : Foo) : Inhabited Foo := ⟨x⟩
partial def partialDefinition (x : Foo) := x
unsafe def unsafeDefinition (x : Foo) := x
class ClassDeclaration (x : Foo) : Prop where
  property : True
structure StructureDeclaration (x : Foo) where
  field : True
end Foo
end TauCeti
"""
        result = findings(source)
        names = [finding.declaration for finding in result]
        self.assertEqual(len(result), 10)
        self.assertEqual(sum("<anonymous instance " in name for name in names), 2)
        for expected in ("attributed", "multilineAttribute", "nonrecursive", "namedInstance",
                         "partialDefinition", "unsafeDefinition", "ClassDeclaration",
                         "StructureDeclaration"):
            self.assertIn(f"TauCeti.Foo.{expected}", names)

    def test_root_declaration_is_not_flagged(self):
        source = """\
namespace TauCeti
namespace Foo
def _root_.Foo.correct (x : Foo) := x
def misplaced (x : Foo) := x
end Foo
end TauCeti
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["TauCeti.Foo.misplaced"])

    def test_only_binder_types_count(self):
        source = """\
namespace TauCeti
namespace Foo
def returnsFoo : Foo := by
  exact (default : Foo)
def takesFunction (f : Foo → Foo) := f
def takesFoo (x : Foo) := x
end Foo
end TauCeti
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["TauCeti.Foo.takesFoo"])

    def test_owned_names_are_lowercase_and_scoped_per_file(self):
        sources = {
            pathlib.Path("TauCeti/Own.lean"): """\
namespace TauCeti
def prod := Nat
namespace prod
def fst (x : prod) := x
end prod
end TauCeti
""",
            pathlib.Path("TauCeti/Other.lean"): """\
namespace TauCeti
namespace prod
def misplaced (x : prod) := x
end prod
end TauCeti
""",
        }
        self.assertEqual([finding.declaration for finding in lint.find_violations(sources, {"prod"})],
                         ["TauCeti.prod.misplaced"])

    def test_missing_mathlib_checkout_fails_loudly(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            source_root = root / "TauCeti"
            source_root.mkdir()
            baseline = root / "baseline.txt"
            baseline.write_text("")
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                result = lint.main(
                    ["--mathlib-root", str(root / "missing"), "--source-root", str(source_root),
                     "--baseline", str(baseline)])
        self.assertEqual(result, 2)
        self.assertIn("Mathlib source directory not found", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
