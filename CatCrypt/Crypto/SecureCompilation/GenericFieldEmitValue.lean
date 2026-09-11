/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.RelationalFrontGenericEmit
public import CatCrypt.Crypto.SecureCompilation.AUCurvesImport.FieldLeafBridge

/-!
# The generic field-op emit → field-VALUE bridge

`RelationalFrontGenericEmit.lean` lowers the generic field-op emitter
(`emitFieldBinop leaf dest a b`) through the owned front and proves it is fully
lowered to **one `Ccall`** — but that is a purely **structural** claim: it says
nothing about *what value* the emitted call writes.  Separately, the per-curve
relational fronts (e.g. `c25519_add_commutes`) prove the **value** content:
`(a + b).val = bignumVal (mlAddModK …)` over the limb carrier.  The genuine
end-to-end gap is the **seam between them**: tying the emitted field-op program,
*evaluated under its operational denotation*, to the actual `ZMod q` field value.

This module bridges that seam.  It composes:

1. the **structural emit** `emitFieldBinop leaf dest a b`
   (= `.RCall leaf ⟨dest, .TFp⟩ [⟨a, .TFp⟩, ⟨b, .TFp⟩]`), with
2. the **operational denotation** of `LowCT` — the big-step relation
   `RustExec N leafSpec` (`Jasmin/LowCT.lean §6`), whose `.call` rule writes
   `leafSpec.call leaf .TFp [.TFp, .TFp] oldDestV argList` into `dest`, with
3. a **leaf-realization hypothesis** (`FieldEmitRealizes`) — the field-agnostic
   analogue of `FieldLeafBridge.FieldMulSpecAgrees`: the `leafSpec.call`
   oracle's value at `leaf` decodes (via an abstract `decode : RustVal .TFp →
   ZMod q`, the CatCrypt image of AUCurves' `feval`) to the
   **commuting-square value** `op (decode aVal) (decode bVal)` of the abstract
   field binop `op` (e.g. `(· + ·)` for `c25519_add_commutes`).

The payload — `emitFieldBinop_realizes_value` — is then the genuine emit→value
tie: under the leaf-realization hypothesis, *running* the emitted program from a
state holding the two operands writes a value into `dest` that **decodes to the
field-op value** `op (decode aVal) (decode bVal)`.  The structural lowering
(point 1) is *threaded through the actual `RustExec` denotation* (point 2), and
the residual that the leaf computes the field value (point 3) is localized as a
named hypothesis, in the exact `FieldLeafBridge` / `CrossProverBridge`
discipline (an inhabited cross-prover predicate, never a bare `axiom`).

## What is genuinely closed here vs. localized

* **Closed (Lean theorem):** the structural-emit ↔ operational-denotation
  composition.  `emitFieldBinop`'s `.RCall` form drives `RustExec.call`, and the
  resulting `dest` slot is exactly `leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
  argList`.  This is the LowCT-denotation thread the structural-only files
  omit — proved over the real big-step relation, no `rfl` shadow.
* **Localized (named hypothesis `FieldEmitRealizes`):** that this opaque
  leaf-call value decodes to the abstract `ZMod q` field-op value.  This is the
  same residual `FieldLeafBridge.FieldMulSpecAgrees` carries for the mul leaf,
  generalized over an arbitrary field binop `op` so the *add* commuting square
  (`c25519_add_commutes` & siblings) is also an instance.

## Non-vacuity

`fieldEmitRealizes_canonical` exhibits a concrete `LeafSpec` (built from the
`FieldLeafBridge`-style `fieldMulCallSpec`-shaped realizer, here for the binop
`op`) under which `FieldEmitRealizes` holds — so the hypothesis is satisfiable,
not an unsatisfiable over-constraint.  The genuine cross-prover content is the
gap between this canonical realizer and the emitted Rust leaf's real semantics,
which lives outside Lean (in the per-curve commuting square + the AUCurves
field-mul correctness).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.GenericFieldEmitValue

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.RelationalFrontGenericEmit

/-! ## §1  The leaf-realization predicate (the value content, localized)

`FieldEmitRealizes q decode op leaf leafSpec` is the field-agnostic analogue of
`FieldLeafBridge.FieldMulSpecAgrees`, generalized over an arbitrary field binop
`op : ZMod q → ZMod q → ZMod q` (so the **add** commuting square is an instance,
not only mul).  It asserts: the CatCrypt `leafSpec.call` oracle, applied at
`leaf` on the `.TFp` carrier to two field-element arguments `aVal`, `bVal`,
produces a destination value whose decoded residue is `op (decode aVal) (decode
bVal)` — the value the per-curve commuting square (`c25519_add_commutes`, …)
proves the emitted kernel computes. -/

/-- **The localized field-op leaf-realization predicate.**  For every operand
    pair `aVal`, `bVal` (and any prior dest value `oldDest`), the leaf-call value
    `leafSpec.call leaf .TFp [.TFp, .TFp] oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]`
    decodes to `op (decode aVal) (decode bVal)` in `ZMod q`.

    This is `FieldLeafBridge.FieldMulSpecAgrees`'s residual, generalized over the
    binop `op` (`(· + ·)` recovers the add commuting square, `(· * ·)` the mul).
    It is **not** a Lean theorem: that `leafSpec.call`'s opaque value coincides
    with the abstract field-op value is the cross-prover edge, named here. -/
def FieldEmitRealizes (q : Nat) (decode : RustVal .TFp → ZMod q)
    (op : ZMod q → ZMod q → ZMod q) (leaf : String) (leafSpec : LeafSpec) :
    Prop :=
  ∀ (aVal bVal oldDest : RustVal .TFp),
    decode
        (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
      = op (decode aVal) (decode bVal)

/-! ## §2  The structural emit drives the operational denotation

This is the part that is a genuine Lean theorem: the `.RCall` shape that
`emitFieldBinop` lowers to (point 1) is exactly the shape `RustExec.call`
consumes (point 2), and the resulting state's `dest` slot is the leaf-call
value.  No `rfl` shadow — this is over the real big-step relation. -/

/-- A `RustState` holding `aVal` in slot `a` and `bVal` in slot `b` (and an
    arbitrary `oldDest` in slot `dest`), with the three names distinct so the
    operands survive the dest write.  This is the minimal precondition state for
    running `emitFieldBinop leaf dest a b`. -/
def operandState (dest a b : String) (aVal bVal oldDest : RustVal .TFp) :
    RustState :=
  rsSetTower
    (rsSetTower
      (rsSetTower (default : RustState) dest ⟨.TFp, oldDest⟩)
      a ⟨.TFp, aVal⟩)
    b ⟨.TFp, bVal⟩

/-- **The structural-emit ↔ operational-denotation composition (the closed
    Lean part).**  Running the emitted field-op program `emitFieldBinop leaf
    dest a b` from `operandState …` under any `leafSpec` terminates in a state
    whose `dest` slot holds exactly `leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
    [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]`.

    This threads the structural lowering (`emitFieldBinop` is one `.RCall`)
    through the **actual** `RustExec.call` big-step rule — the LowCT denotation
    hook the structural-only `RelationalFrontGenericEmit` lemmas never touch.
    The names `dest`, `a`, `b` must be distinct (so the operand reads are not
    clobbered, and the dest write lands on the right slot). -/
theorem emitFieldBinop_exec
    (N : Nat) (leafSpec : LeafSpec) (leaf dest a b : String)
    (aVal bVal oldDest : RustVal .TFp)
    (hda : dest ≠ a) (hdb : dest ≠ b) (hab : a ≠ b) :
    RustExec N leafSpec (emitFieldBinop leaf dest a b)
      (operandState dest a b aVal bVal oldDest)
      (locatedUpdate (operandState dest a b aVal bVal oldDest) ⟨dest, .TFp⟩
        (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])) := by
  -- Lookups in `operandState`: `a`, `b` survive the later writes (distinct
  -- names), `dest` was written first.
  have ha : (operandState dest a b aVal bVal oldDest).rsTower a
      = some ⟨.TFp, aVal⟩ := by
    unfold operandState
    rw [rsSetTower_other _ _ _ _ (Ne.symm hab), rsSetTower_same]
  have hb : (operandState dest a b aVal bVal oldDest).rsTower b
      = some ⟨.TFp, bVal⟩ := by
    unfold operandState
    rw [rsSetTower_same]
  have hd : (operandState dest a b aVal bVal oldDest).rsTower dest
      = some ⟨.TFp, oldDest⟩ := by
    unfold operandState
    rw [rsSetTower_other _ _ _ _ (Ne.symm hdb),
        rsSetTower_other _ _ _ _ (Ne.symm hda), rsSetTower_same]
  -- The dest lookup as a `locatedLookup` (the type matches `.TFp`).
  have hlook : locatedLookup (operandState dest a b aVal bVal oldDest)
      ⟨dest, .TFp⟩ = some oldDest := by
    unfold locatedLookup
    show (match (operandState dest a b aVal bVal oldDest).rsTower dest with
      | some ⟨t, v⟩ => if h : t = .TFp then some (h ▸ v) else none
      | none => none) = some oldDest
    rw [hd]; simp
  -- The arg list filterMap reduces to the two stored values.
  have hargs :
      ([(⟨a, .TFp⟩ : Located), ⟨b, .TFp⟩].filterMap
        (fun x => (operandState dest a b aVal bVal oldDest).rsTower x.locVar))
        = [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩] := by
    simp only [List.filterMap_cons, List.filterMap_nil, ha, hb]
  -- Apply the `RustExec.call` rule.  Its dest write is
  -- `locatedUpdate rs dest (leafSpec.call f .TFp (args.map ·.locDst) old argList)`.
  have hstep := RustExec.call (N := N) (leafSpec := leafSpec) leaf
      (⟨dest, .TFp⟩ : Located) [⟨a, .TFp⟩, ⟨b, .TFp⟩]
      (operandState dest a b aVal bVal oldDest) oldDest
      ([(⟨a, .TFp⟩ : Located), ⟨b, .TFp⟩].filterMap
        (fun x => (operandState dest a b aVal bVal oldDest).rsTower x.locVar))
      hlook rfl
      (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with h | h
        · subst h; exact ⟨aVal, ha⟩
        · subst h; exact ⟨bVal, hb⟩)
  -- Rewrite `emitFieldBinop` to its `.RCall` form, the arg-list to its value,
  -- and `args.map (·.locDst)` to `[.TFp, .TFp]`.
  rw [hargs] at hstep
  have hmap : ([(⟨a, .TFp⟩ : Located), ⟨b, .TFp⟩].map (·.locDst))
      = [TowerType.TFp, TowerType.TFp] := by
    show [Located.locDst ⟨a, .TFp⟩, Located.locDst ⟨b, .TFp⟩] = _
    rfl
  rw [hmap] at hstep
  -- `emitFieldBinop leaf dest a b` unfolds definitionally to the `.RCall`.
  show RustExec N leafSpec (emitFieldBinop leaf dest a b) _ _
  unfold emitFieldBinop
  exact hstep

/-! ## §3  The payload: emit → field VALUE

Composing §2 (the closed structural↔operational step) with §1 (the localized
leaf-realization) gives the genuine emit→value tie: the emitted program's `dest`
slot, **read through `decode`**, equals the abstract field-op value
`op (decode aVal) (decode bVal)`. -/

/-- **The generic emit→value bridge.**  Given the localized leaf-realization
    `FieldEmitRealizes q decode op leaf leafSpec` (the residual the per-curve
    commuting square + AUCurves field-op correctness discharge outside Lean),
    *running* `emitFieldBinop leaf dest a b` under `leafSpec` from a state holding
    `aVal`, `bVal` writes into `dest` a value that **decodes to the field-op
    value** `op (decode aVal) (decode bVal)`.

    For `op = (· + ·)` and `decode` the radix-2^51 / Montgomery decoder, the
    right-hand side is exactly `c25519_add_commutes`' abstract `(a + b)` side;
    for `op = (· * ·)`, the mul commuting square.  This is the structural-emit ↔
    value-semantics seam, closed: the structural lowering threaded through
    `RustExec` (§2), conditioned only on the named cross-prover leaf-realization
    (§1). -/
theorem emitFieldBinop_realizes_value
    (N : Nat) (q : Nat) (decode : RustVal .TFp → ZMod q)
    (op : ZMod q → ZMod q → ZMod q) (leafSpec : LeafSpec) (leaf dest a b : String)
    (aVal bVal oldDest : RustVal .TFp)
    (hda : dest ≠ a) (hdb : dest ≠ b) (hab : a ≠ b)
    (hreal : FieldEmitRealizes q decode op leaf leafSpec) :
    ∃ rs',
      RustExec N leafSpec (emitFieldBinop leaf dest a b)
          (operandState dest a b aVal bVal oldDest) rs'
        ∧ (∀ v, locatedLookup rs' ⟨dest, .TFp⟩ = some v →
            decode v = op (decode aVal) (decode bVal)) := by
  refine ⟨_, emitFieldBinop_exec N leafSpec leaf dest a b aVal bVal oldDest
      hda hdb hab, ?_⟩
  intro v hv
  -- The post-state's `dest` slot is the leaf-call value (by `locatedUpdate_dest`),
  -- which `FieldEmitRealizes` decodes to the field-op value.
  have hdest : locatedLookup
      (locatedUpdate (operandState dest a b aVal bVal oldDest) ⟨dest, .TFp⟩
        (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])) ⟨dest, .TFp⟩
      = some (leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
          [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]) := by
    unfold locatedLookup
    rw [locatedUpdate_dest]
    simp
  rw [hdest] at hv
  -- `hv : some (leaf-call value) = some v`, so `v` is the leaf-call value.
  have : v = leafSpec.call leaf .TFp [.TFp, .TFp] oldDest
      [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩] := by
    exact (Option.some.injEq _ _).mp hv.symm
  rw [this]
  exact hreal aVal bVal oldDest

/-! ## §4  Non-vacuity: a canonical realizer satisfies `FieldEmitRealizes`

As in `FieldLeafBridge.fieldMulSpecAgrees_canonical`, we exhibit a concrete
`LeafSpec` under which `FieldEmitRealizes` holds — confirming the predicate is
the right shape (an inhabited cross-prover claim), generalized to an arbitrary
binop `op`. -/

/-- The canonical `CallSpec` realizing a generic field binop `op` at leaf
    `leaf`: at the target name it decodes the two positional `.TFp` arguments,
    applies `op` in `ZMod q`, and re-encodes via a section `encode`; off-target
    it returns `oldDest`.  The binop-generalized analogue of
    `FieldLeafBridge.fieldMulCallSpec`. -/
def fieldBinopCallSpec (q : Nat) (decode : RustVal .TFp → ZMod q)
    (op : ZMod q → ZMod q → ZMod q) (encode : ZMod q → RustVal .TFp)
    (leaf : String) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if fname = leaf then
      let pick : (Σ t : TowerType, RustVal t) → ZMod q := fun a =>
        if ht : a.1 = TowerType.TFp then decode (ht ▸ a.2) else 0
      match args with
      | a :: b :: _ =>
          if hd : _dt = TowerType.TFp then
            hd ▸ encode (op (pick a) (pick b))
          else oldDest
      | _ => oldDest
    else oldDest

/-- **Non-vacuity witness for `FieldEmitRealizes`.**  For the canonical
    `LeafSpec` built from `fieldBinopCallSpec` with a decoder section `encode`
    (`decode ∘ encode = id`), the leaf-realization holds — so the localized
    hypothesis is satisfiable, not an over-constraint.  The genuine cross-prover
    content is precisely the gap between this canonical realizer and the emitted
    Rust leaf's real semantics (the per-curve commuting square + AUCurves
    field-op correctness), which lives outside Lean. -/
theorem fieldEmitRealizes_canonical
    (q : Nat) (decode : RustVal .TFp → ZMod q)
    (op : ZMod q → ZMod q → ZMod q) (encode : ZMod q → RustVal .TFp)
    (hsection : ∀ z : ZMod q, decode (encode z) = z)
    (leaf : String) (limbStore : LimbStoreSpec) :
    FieldEmitRealizes q decode op leaf
      { call := fieldBinopCallSpec q decode op encode leaf, limbStore := limbStore } := by
  intro aVal bVal oldDest
  show decode (fieldBinopCallSpec q decode op encode leaf leaf .TFp [.TFp, .TFp]
      oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩]) = op (decode aVal) (decode bVal)
  simp only [fieldBinopCallSpec, ite_true, dite_true, hsection]

end CatCrypt.Crypto.SecureCompilation.GenericFieldEmitValue
