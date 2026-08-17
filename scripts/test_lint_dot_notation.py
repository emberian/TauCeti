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
public section
namespace TauCeti
namespace Foo
def before (x : Foo) := x
section Chain
def inside (x : Foo) := x
end Chain
def after (x : Foo) := x
mutual
def mutualOne (x : Foo) := x
def mutualTwo (x : Foo) := x
end
def afterMutual (x : Foo) := x
end Foo
end TauCeti
end
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         [f"TauCeti.Foo.{name}" for name in
                          ("before", "inside", "after", "mutualOne", "mutualTwo", "afterMutual")])

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
def implicitOnly {x : Foo} := x
def connective (x : Foo × Foo) := x
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

    def test_function_valued_binders_are_not_receivers(self):
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

    def test_scoped_variable_and_dotted_name_are_detected(self):
        source = """\
namespace TauCeti
namespace Foo
variable (x : Foo)
variable {y : Foo}
def fromVariable : x = x := rfl
def implicitVariable : y = y := rfl
end Foo
def Foo.dotted (x : Foo) := x
def Foo.termType (x : Foo.term) := x
end TauCeti
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["TauCeti.Foo.fromVariable", "TauCeti.Foo.dotted"])

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

    def test_main_rejects_new_and_reports_ratchetable_findings(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            mathlib = root / "Mathlib"
            source_root = root / "TauCeti"
            mathlib.mkdir()
            source_root.mkdir()
            (mathlib / "Foo.lean").write_text("namespace Foo\nend Foo\n")
            source = source_root / "Test.lean"
            source.write_text("namespace TauCeti\nnamespace Foo\ndef bar (x : Foo) := x\n"
                              "end Foo\nend TauCeti\n")
            baseline = pathlib.Path(directory) / "baseline.txt"
            baseline.write_text("")
            args = ["--mathlib-root", str(mathlib), "--source-root", str(source_root),
                    "--baseline", str(baseline)]
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                self.assertEqual(lint.main(args), 1)
                self.assertEqual(lint.main([*args, "--write-baseline"]), 0)
                source.write_text("namespace TauCeti\ndef _root_.Foo.bar (x : Foo) := x\nend TauCeti\n")
                self.assertEqual(lint.main(args), 0)
            self.assertIn("1 new", stdout.getvalue())
            self.assertIn("1 ratchetable", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
