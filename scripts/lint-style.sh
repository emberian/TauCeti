#!/usr/bin/env bash
# Run Mathlib's source-based style checks over every TauCeti/ module.
#
# lint-style treats its module arguments as import roots and lints only their imports. The
# library root TauCeti.lean is intentionally empty, so generate a temporary import-all module
# instead. It lives under .lake because that is the writable area in the PR build sandbox.
set -euo pipefail

lake exe header-style

lint_src="$(mktemp -d "$PWD/.lake/lint-style-src.XXXXXX")"
lint_module="$lint_src/TauCetiLint/All.lean"

mkdir -p "$(dirname "$lint_module")"
trap 'rm -rf "$lint_src"' EXIT

while IFS= read -r -d '' file; do
  module="${file%.lean}"
  printf 'import %s\n' "${module//\//.}"
done < <(find TauCeti -type f -name '*.lean' -print0 | sort -z) > "$lint_module"

# TauCetiLint.All supplies the imports to Mathlib's text-based linters. TauCeti makes lint-style's
# package-root filter retain those imports, while contributing none of its own because the root is
# empty. The copyright-header check above is separate because it is a command linter in this pin.
LEAN_SRC_PATH="$lint_src${LEAN_SRC_PATH:+:$LEAN_SRC_PATH}" \
  lake exe lint-style "$@" TauCetiLint.All TauCeti
