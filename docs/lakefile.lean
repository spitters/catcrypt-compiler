import Lake
open Lake DSL

-- Documentation package — SEPARATE from the `catcryptCompiler` library package so
-- the verso toolchain is NOT a transitive dependency of consumers of the library.
-- The manual transcribes declarations as text, so it needs only verso — not the
-- compiler library or mathlib. Build it with:
--   cd docs && lake update && lake build && lake exe compiler-manual --output _out
-- Open docs/_out/html-single/index.html (a single self-contained page).
require verso from git
  "https://github.com/leanprover/verso.git" @ "v4.32.0"

package catcryptCompilerDocs where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

@[default_target]
lean_lib CompilerManual where

lean_exe «compiler-manual» where
  root := `ManualMain
