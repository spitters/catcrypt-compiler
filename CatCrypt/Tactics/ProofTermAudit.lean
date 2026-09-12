/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.ProofTermAudit

/-! Re-export of `CatCryptCore.Tactics.ProofTermAudit` from the CatCrypt-core package, so
`import CatCrypt.Tactics.ProofTermAudit` resolves to the upstream library. The commands that
tag a declaration by inspecting its elaborated proof term live in the
`CatCrypt.Tactic.ProofTermAudit` namespace provided by the upstream module.
`CatCrypt.Tactic.ProofTermAudit` re-exports the same module. -/

@[expose] public section
