import Lake
open Lake DSL

package catcryptCompiler where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]
  -- `-E <kind>` reports Lean messages of that kind as errors. `hasSorry` is the
  -- kind Lean attaches to a declaration whose proof term reaches `sorryAx`, so
  -- building this package refuses such a declaration and no separate step has to
  -- read the build's output. The word in a comment, a docstring or a string
  -- literal carries no such message; a declaration reaching `sorryAx` through a
  -- tactic carries one even though the word appears nowhere in its source.
  moreLeanArgs := #["-E", "hasSorry"]

@[default_target]
lean_lib CatCryptCompiler where
  -- The CatCrypt verified compiler: two fronts (hax/Rust → LowCT → `Com` IR) →
  -- one verified x86/ARM/RISC-V backend. The verified compiler proper is the
  -- subtree `SecureCompilation/` + `Jasmin/` + `Optimizer/`; the module set below
  -- adds its dependency closure over the workspace (the `catcryptCore` re-export
  -- shims and the foundational leaves it imports), the per-scheme emit endpoints,
  -- and their `*SecurityTie` bridges.
  --
  -- Namespaces match the CatCrypt workspace (`CatCrypt.Crypto.SecureCompilation.*`,
  -- `CatCrypt.Crypto.Jasmin.*`, `CatCrypt.Crypto.Optimizer.*`, and the foundational
  -- `CatCrypt.{Core,Deep,Relational,...}.*`), so the dev tree imports it unchanged.
  --
  -- Boundary: no scheme-level security proof is in the closure — the `*SecurityTie`
  -- modules stop at the abstract dependency record, and the scheme security chains
  -- that consume it live outside this package. The UC/advantage methodology is in
  -- the closure (`Crypto/UC.lean` and `Crypto/Advantage.lean` re-export
  -- `catcryptCore`; `Crypto/UCComposition.lean`, `UCAlg.lean`, `UCDSL.lean`,
  -- `UCAdmClass.lean` and `UCMonad/` are local). This package's axiom ledger owns
  -- the ISA / jasmin / byte-trust axioms; core's ledger stays clean because the
  -- edge direction is compiler → core, never the reverse.
  globs := #[.submodules `CatCrypt]

-- Imported from core: `Core.{Code,Heap,Location,SPTree}`,
-- `Crypto.{SDist,CryptoWord,UC,Advantage}`, `Deep.{RawCode,Eval}`,
-- `Relational.Rules`, `Tactics.FieldClear` — each behind a re-export shim under
-- `CatCrypt/`, so `import CatCrypt.…` paths keep resolving.
-- The sibling packages are pinned by commit on their `lean-upgrade-4.32`
-- branches; they carry no release label at Lean 4.32 yet.
require catcryptCore from git
  "https://github.com/spitters/CatCrypt-core.git" @ "b581de1fc429be83737ea2a27ca1092f9d5ee34f"

-- IR lowering target (`Com` → Veir / MLIR). Pinned to a private staging fork:
-- upstream Veir at Lean 4.32 plus the CatCrypt additions (the catcrypt/memref/
-- polynomial/vector/x86vector lowering dialects, `Func.call`, and the
-- `Veir.List.*` namespacing that avoids a Mathlib/Batteries name collision).
-- Building requires read access to `spitters/veir-catcrypt`.
require Veir from git
  "https://github.com/spitters/veir-catcrypt" @ "v4.32.0-catcrypt.2"

-- ParamTransfer (proof-transfer bridge) + CompPoly (NTT algebraic theory).
require paramTransfer from git
  "https://github.com/spitters/ParamTransfer.git" @ "e36404b34001d20ac9175a35fa16929ca72c66ad"
require CompPoly from git
  "https://github.com/Verified-zkEVM/CompPoly" @ "v4.32.2"

-- hax-lean: the typed haxpipeT front (`Hax.TExpr`).
require «hax-lean» from git
  "https://github.com/spitters/hax-lean.git" @ "7b407d1c296ca7fcbb336d56563b5075f9b34b6b"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.0"

-- API documentation (opt-in, dev only — not in the normal build closure).
--   lake -R -Kenv=doc build CatCryptCompiler:docs
-- generates a hyperlinked HTML reference from the module docstrings under
-- .lake/build/doc/. Heavy (one HTML unit per module) — run capped, like the
-- library build.
meta if get_config? env = some "doc" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.32.0"
