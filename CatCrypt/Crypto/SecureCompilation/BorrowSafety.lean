/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim
public import CatCrypt.Crypto.Jasmin.LowCTBorrowCheck


@[expose] public section
set_option autoImplicit false

/-!
# Borrow-check ↔ no-alias bridge (#269 Part (a)) over the `CProg`-free front

`NoAliasVM vm` (in `RustStateSubstrate.lean`) is the *semantic*
no-aliasing-of-CryptoSSA-variables property: `vm.lookup` is injective on source
names. It is the side condition the dialect-front simulation theorem
`rustExecSimulatesDialect` silently carries inside the `noAlias` field of its
`hInv : RustStateInterp vm rs V` hypothesis. This file discharges that hypothesis
at its source, over the `catCryptDialect` front `translateDialectControl`.

## Finding

`NoAliasVM` is a structural invariant of *translator-built VarMaps* and is
**independent of `borrowOk`**. The dialect front extends the VarMap only through
`VarMap.bind` / `VarMap.weaken`, both of which preserve `NoAliasVM`
(`noAlias_bind`, `noAlias_weaken`), starting from the empty VarMap
(`noAlias_empty`). It never performs an aliasing construction. The carrier is the
Wave-1 dialect twin
`Dialects.CryptoDialectRustSim.translateDialectControl_preserves_noAlias`
(built by structural recursion on `IsCoveredCtl`, with no `borrowOk`
precondition). Therefore:

* `noAlias_of_translateDialect_empty` — a *top-level* dialect translation (entry
  VarMap `VarMap.empty`) over a control-covered `c` yields `NoAliasVM o.vm`.

`borrowOk` lives at a different layer: it is the *source-level* no-call-site-
aliasing checker that feeds the **memory**-model frame story in
`BorrowToMemoryBridge.lean` (mutable destinations mutually distinct + disjoint
from args; non-overlapping slice copies). The two no-aliasing notions are
orthogonal:

* `NoAliasVM` rules out two *source names* resolving to one CryptoSSA variable
  (a compile-time VarMap property, needed for the byte-layout simulation).
* `borrowOk` rules out two *mutable references at one call site* pointing at the
  same backing store (a source property, needed for the `array64` memory frame).

## Use-site discharge

`rustStateInterp_empty` already builds `RustStateInterp VarMap.empty rs HVec.nil`
(its `noAlias` field is `noAlias_empty`). For a top-level program the entry
`hInv` is exactly that, so the `NoAliasVM` side condition is discharged with no
assumption (`entry_interp`).

Neither the statements nor the proofs below name `CProg` / `CExpr` / `TransOut`
/ `translate`.
-/

namespace CatCrypt.Crypto.SecureCompilation.BorrowSafety

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectRustSim

/-- **Top-level entry corollary (dialect front).** A dialect translation whose
    entry VarMap is the empty VarMap always yields an alias-free output VarMap
    over the control-covered fragment — with no `borrowOk` or other
    precondition. Every translation pipeline starts from `VarMap.empty`, so this
    is the discharge for the `NoAliasVM` side condition the dialect simulation
    theorem `rustExecSimulatesDialect` carries. -/
theorem noAlias_of_translateDialect_empty (c : LowCT) (hc : IsCoveredCtl c)
    {o : DTransOut (Γ := ([] : Ctx))}
    (hT : translateDialectControl VarMap.empty c = some o) :
    NoAliasVM o.vm :=
  translateDialectControl_preserves_noAlias VarMap.empty hc hT noAlias_empty

/-- **Use-site discharge for the entry interpretation.** For a top-level
    program the entry `hInv : RustStateInterp VarMap.empty rs HVec.nil` (whose
    `noAlias` field is `noAlias_empty`) is supplied directly. This re-export
    names the canonical entry-state interpretation the dialect simulation theorem
    `rustExecSimulatesDialect` consumes as `hInv`. With it, the `NoAliasVM` side
    condition is discharged with no assumption. -/
theorem entry_interp (rs : RustState) :
    RustStateInterp VarMap.empty rs HVec.nil :=
  rustStateInterp_empty rs

/-! ## Borrow-check ↔ no-alias: orthogonality (documentation lemma)

`borrowOk` does **not** appear as a hypothesis of
`noAlias_of_translateDialect_empty` — it is genuinely unnecessary for
`NoAliasVM`. The lemma below records this by deriving `NoAliasVM o.vm` from a
`borrowOk` program *via the borrowOk hypothesis being unused* (`_hBorrow`),
making the independence explicit for readers and for the audit. -/

/-- For a borrow-checked, control-covered top-level program, the dialect output
    VarMap is alias-free. The `borrowOk` hypothesis is **unused** (`_hBorrow`):
    `NoAliasVM` is a structural property of the translation, independent of
    `borrowOk`. The pairing here documents that both no-aliasing notions hold
    simultaneously for a well-formed borrow-checked program — `NoAliasVM` for the
    byte-layout simulation (this file) and the memory-frame disjointness for the
    `array64` invariants (`BorrowToMemoryBridge`). -/
theorem borrowOk_noAlias_of_translateDialect_empty (c : LowCT) (hc : IsCoveredCtl c)
    (_hBorrow : borrowOk c = true)
    {o : DTransOut (Γ := ([] : Ctx))}
    (hT : translateDialectControl VarMap.empty c = some o) :
    NoAliasVM o.vm :=
  noAlias_of_translateDialect_empty c hc hT

/-! ## §2. Use-site discharge: top-level simulation with `NoAliasVM` discharged

`rustExecSimulatesDialect` carries `NoAliasVM` inside its `hInv` hypothesis.
For a *top-level* program the entry state is `(VarMap.empty, rs, HVec.nil)`, and
`entry_interp` builds the `RustStateInterp` (with `noAlias` discharged by
`noAlias_empty`). This wrapper consumes that and exposes the simulation
conclusion **without** the caller having to produce a `NoAliasVM` proof — the
side condition is discharged here. -/

/-- **Top-level byte-layout simulation, `NoAliasVM` discharged (dialect front).**
    From a top-level dialect translation (`translateDialectControl VarMap.empty c
    = some o`) over a control-covered `c` and a front `RustExec` starting at
    `rs`, there is a CryptoSSA valuation `V'` satisfying the byte-layout
    invariant at the post-state. The `NoAliasVM` side condition of
    `rustExecSimulatesDialect` is discharged internally via `entry_interp`
    (built on `noAlias_empty`); the caller supplies no aliasing hypothesis. -/
theorem topLevelSimulatesDialect_noAliasDischarged
    (c : LowCT) (hc : IsCoveredCtl c) (o : DTransOut ([] : Ctx)) (N : Nat)
    (leafSpec : LeafSpec) (rs rs' : RustState)
    (hT : translateDialectControl VarMap.empty c = some o)
    (hExec : RustExec N leafSpec c rs rs') :
    ∃ V' : HVec o.Γ', RustStateInterp o.vm rs' V' :=
  rustExecSimulatesDialect VarMap.empty c o N leafSpec rs rs'
    hc hT hExec HVec.nil (entry_interp rs)

end CatCrypt.Crypto.SecureCompilation.BorrowSafety
