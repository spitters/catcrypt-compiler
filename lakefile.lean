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
  -- one verified owned x86/ARM/RISC-V backend. The verified compiler proper is the
  -- subtree `SecureCompilation/` + `Jasmin/` + `Optimizer/`; the module set below is
  -- its self-contained dependency closure over the workspace (the `catcryptCore`
  -- shims + foundational leaves it imports), computed to be free of every scheme
  -- security proof and of the `MPC`/`Examples` protocol proofs.
  --
  -- Namespaces are preserved (`CatCrypt.Crypto.SecureCompilation.*`,
  -- `CatCrypt.Crypto.Jasmin.*`, `CatCrypt.Crypto.Optimizer.*`, and the foundational
  -- `CatCrypt.{Core,Deep,Relational,...}.*`) so the dev tree consumes without churn.
  --
  -- The compiler-boundary carve severed the security/UC layer from the subtree: NO
  -- require on the SSProve security methodology beyond the foundational cost/monad
  -- leaves in `catcryptCore`. The closure reaches no scheme dir. This package's axiom
  -- ledger owns the ISA / jasmin / byte-trust axioms; core's ledger stays clean
  -- because the edge direction is compiler → core, never the reverse.
  globs := #[.submodules `CatCrypt]

-- Foundational methodology leaves only: `SDist`, `Deep.RawCode`, base `UCMonad`.
-- (Core also holds the security layer, but this package imports none of it.)
require catcryptCore from git
  "https://github.com/spitters/CatCrypt-core.git" @ "0.1.0-alpha.1"

-- IR lowering target (`Com` → Veir / MLIR). Pinned to the v4.29.0 tag (the only
-- Veir release; see the Veir-pin note in the carve plan).
require Veir from git
  "https://github.com/opencompl/veir.git" @ "v4.29.0"

-- ParamTransfer (proof-transfer bridge) + CompPoly (NTT algebraic theory).
require paramTransfer from git
  "https://github.com/spitters/ParamTransfer.git" @ "0.1.0-alpha.1"
require CompPoly from git
  "https://github.com/Verified-zkEVM/CompPoly" @ "v4.30.0-patch1"

-- hax-lean: the typed haxpipeT front (`Hax.TExpr`).
require «hax-lean» from git
  "https://github.com/spitters/hax-lean.git" @ "v0.1.0-alpha.1"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

-- API documentation (opt-in, dev only — not in the normal build closure).
--   lake -R -Kenv=doc build CatCryptCompiler:docs
-- generates a hyperlinked HTML reference from the module docstrings under
-- .lake/build/doc/. Heavy (one HTML unit per module) — run capped, like the
-- library build.
meta if get_config? env = some "doc" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.30.0"
