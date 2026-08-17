import Mathlib.Tactic.Linter.Header

/-!
# `header-style`: enforce Mathlib's copyright-header checks on every Tau Ceti source file

Human-owned governance machinery. Mathlib's `linter.style.header` deliberately skips a module
unless the library root imports it. Tau Ceti's root is intentionally empty, so the ordinary
command linter never reaches these files. This audit calls the linter's public
`copyrightHeaderChecks` function on every `TauCeti/**/*.lean` source instead.

Run via `lake exe header-style`, as part of `scripts/lint-style.sh`.
-/

open Mathlib.Linter

/-- Mathlib's default required license line, also used by Tau Ceti. -/
def expectedLicense := "Released under Apache 2.0 license as described in the file LICENSE."

/-- Every `.lean` source under `dir`, recursively. -/
partial def collectLeanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut files := #[]
  for entry in (← dir.readDir) do
    if (← entry.path.isDir) then
      files := files ++ (← collectLeanFiles entry.path)
    else if entry.path.extension == some "lean" then
      files := files.push entry.path
  return files

def main : IO UInt32 := do
  let files ← collectLeanFiles "TauCeti"
  if files.isEmpty then
    IO.eprintln "header-style: found no TauCeti source files; the audit is miswired."
    return 1
  let mut failures : UInt32 := 0
  for file in files do
    let errors := copyrightHeaderChecks (← IO.FS.readFile file) expectedLicense
    unless errors.isEmpty do
      failures := failures + 1
      for (_, message) in errors do
        IO.eprintln s!"{file}: {message}"
  if failures == 0 then
    IO.println s!"header-style: all {files.size} TauCeti source file(s) have conforming headers."
    return 0
  else
    IO.eprintln s!"header-style: {failures} source file(s) have malformed copyright headers."
    return min failures 125
