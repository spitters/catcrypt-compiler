/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.LowCTToHax
public import CatCrypt.Crypto.Hax.ImpRustHaxCheck

/-!
# `appendWipes`: overwriting secret slots before a program's tail

A `LowCT → Option LowCT` source-to-source pass that appends one leaf call per
named slot to the end of a straight-line program, each call overwriting its slot
with the default value of the slot's tower type. The printed Rust of the
transformed program ends in `x = f ( x ) ;` for each slot `x` and its clearing
leaf `f`, so the caller's own locals hold the default value when the function's
tail is reached.

The Rust-printer sibling of the asm-level pass
`CatCrypt.Crypto.SecureCompilation.X86Backend.StackZeroize`, which appends one
zero store per written frame cell before an export function's `Lret`.

## The slot list

A slot is given as a pair `(x, f)`: the slot name and the name of the leaf that
clears it. The printed Rust is monomorphic — `x = f ( x ) ;` resolves `f` at one
signature — so slots of different widths take different clearing leaves.

## Scope of the statement

The pass clears the slots named in `xs`, which are slots of the program the pass
transforms. A copy a leaf function made of an argument inside its own frame is
the leaf's responsibility; `wipeState` describes the caller's tower heap and says
nothing about leaf-local storage, about the machine registers the printed Rust
compiles to, or about slots the caller does not name in `xs`.

The clearing value is `default : RustVal t` and the behaviour of each clearing
leaf enters every semantic result as the hypothesis
`ls.call f t [t] old [⟨t, v⟩] = default`.

`appendWipes` is partial: it descends the chain of `RLetZero` and `RLetU64Zero`
bindings and `RSeq` sequencing into the tail and replaces an `RSkip` tail. On any
other tail it is `none`, so a program outside the chain shape is refused rather
than returned unwiped.

## Main definitions

* `wipeCall`, `wipeSeq`, `appendWipes` — the clearing call, the chain of clearing
  calls, and the pass.
* `impWipeSeq`, `impWipes` — the mirror transform on `Hax.ImpExpr`.
* `wipeState` — the tower heap with every named slot at the default value.

## Main results

* `appendWipes_toImp` — the translation `lowCTToImp` carries the pass to
  `impWipes`: the transformed program translates to the transformed hax
  expression.
* `tailUnit_impWipes` — `TailUnit` is unchanged, so `retOfUnit` still finds the
  tail of the transformed expression and `ppImpRustFnRet` prints it.
* `exec_appendWipes_inv` — a run of the transformed program is a run of the
  original followed by the clearing: the post-state is `wipeState` of a state the
  original reaches.
* `exec_appendWipes` — the converse, for a post-state whose named slots hold the
  tower type of the clearing calls.
* `wipeState_mem` / `wipeState_not_mem` — every named slot holds the default
  value, and every other slot reads as before.
* `frontNF_appendWipes` — the pass commutes with the front's located types when
  each clearing leaf is dispatched to the cleared slots' tower type.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpPat)
open CatCrypt.Crypto.Jasmin.LowCT

/-! ## §1  The pass -/

/-- The call overwriting slot `x` at tower type `t`: the leaf `wipeFn` with `x`
    as its destination and as its only argument, so the Rust leaf receives the
    old value by value. -/
def wipeCall (wipeFn : String) (t : TowerType) (x : String) : LowCT :=
  .RCall wipeFn ⟨x, t⟩ [⟨x, t⟩]

/-- The clearing calls for the slots `xs`, in list order, sequenced before `k`.
    Each pair is a slot name and the leaf that clears it. -/
def wipeSeq (t : TowerType) : List (String × String) → LowCT → LowCT
  | [], k => k
  | p :: xs, k => .RSeq (wipeCall p.2 t p.1) (wipeSeq t xs k)

/-- **The pass.** The straight-line chain of `RLetZero` and `RLetU64Zero`
    bindings and `RSeq` sequencing is descended into the tail, and an `RSkip`
    tail is replaced by the clearing calls for `xs`. A tail of any other shape
    yields `none`. -/
def appendWipes (t : TowerType) (xs : List (String × String)) :
    LowCT → Option LowCT
  | .RSkip => some (wipeSeq t xs .RSkip)
  | .RLetZero x ty b => (appendWipes t xs b).map (.RLetZero x ty)
  | .RLetU64Zero x b => (appendWipes t xs b).map (.RLetU64Zero x)
  | .RSeq a b => (appendWipes t xs b).map (.RSeq a)
  | _ => none

/-! ## §2  The mirror transform on `ImpExpr` -/

/-- The clearing statements for `xs` on the hax side: `x = f(x);` per slot,
    sequenced before the `unitVal` tail. -/
def impWipeSeq : List (String × String) → ImpExpr
  | [] => .unitVal
  | p :: xs => .seq (.assign p.1 (.app p.2 [.var p.1])) (impWipeSeq xs)

mutual

/-- The hax expression with the clearing statements for `xs` appended before its
    `unitVal` tail, descending through bindings, sequencing and match arms. -/
def impWipes (xs : List (String × String)) : ImpExpr → ImpExpr
  | .unitVal => impWipeSeq xs
  | .seq a b => .seq a (impWipes xs b)
  | .letBind x v b => .letBind x v (impWipes xs b)
  | .match_ s arms => .match_ s (impWipesArms xs arms)
  | e => e

/-- `impWipes` on every arm body. -/
def impWipesArms (xs : List (String × String)) :
    List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
  | [] => []
  | (p, b) :: r => (p, impWipes xs b) :: impWipesArms xs r

end

/-! ## §3  The translation carries the pass -/

/-- The translation of the clearing calls is the clearing statements. -/
theorem lowCTToImp_wipeSeq (t : TowerType) (xs : List (String × String)) :
    lowCTToImp (wipeSeq t xs .RSkip) = some (impWipeSeq xs) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp [wipeSeq, wipeCall, lowCTToImp, locArgsToImp, impWipeSeq, ih]

/-- The clearing statements are the transform of the `unitVal` tail. -/
theorem impWipes_unitVal (xs : List (String × String)) :
    impWipes xs .unitVal = impWipeSeq xs := rfl

/-- The pass on a sequencing node, given the transform of its tail. -/
theorem lowCTToImp_seq_wipe (xs : List (String × String)) (a b b' : LowCT) (e : ImpExpr)
    (h : lowCTToImp (.RSeq a b) = some e)
    (hb : ∀ eb, lowCTToImp b = some eb → lowCTToImp b' = some (impWipes xs eb)) :
    lowCTToImp (.RSeq a b') = some (impWipes xs e) := by
  cases a
  case RArrStore arr idx src =>
    simp only [lowCTToImp] at h ⊢
    cases hbb : lowCTToImp b with
    | none => simp [hbb] at h
    | some eb =>
      simp only [hbb, Option.map_some, Option.some.injEq] at h
      subst h
      simp [hb eb hbb, impWipes]
  all_goals
    rw [lowCTToImp.eq_3 _ _ (by intro arr idx src; simp)] at h
    rw [lowCTToImp.eq_3 _ _ (by intro arr idx src; simp)]
    cases ha : lowCTToImp _ with
    | none => simp [ha] at h
    | some ea =>
      cases hbb : lowCTToImp b with
      | none => simp [ha, hbb] at h
      | some eb =>
        simp only [ha, hbb, Option.some.injEq] at h
        subst h
        simp [hb eb hbb, impWipes]

/-- **The translation carries the pass.** The transformed program translates to
    the transformed hax expression, so the Rust the printer emits for the
    transformed program is the printed Rust of the original with the clearing
    statements before its tail. -/
theorem appendWipes_toImp (t : TowerType) (xs : List (String × String)) :
    ∀ (c c' : LowCT) (e : ImpExpr), lowCTToImp c = some e →
      appendWipes t xs c = some c' → lowCTToImp c' = some (impWipes xs e) := by
  intro c
  induction c using lowCTToImp.induct
  case case1 =>
    intro c' e h hc'
    simp only [lowCTToImp, Option.some.injEq] at h
    subst h
    simp only [appendWipes, Option.some.injEq] at hc'
    subst hc'
    rw [impWipes_unitVal]
    exact lowCTToImp_wipeSeq t xs
  case case2 arr idx src b ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      exact lowCTToImp_seq_wipe xs _ b b' e h (fun eb heb => ih b' eb heb hb)
  case case3 a b hna ea eb hbe hae iha ihb =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      exact lowCTToImp_seq_wipe xs a b b' e h (fun eb' heb' => ihb b' eb' heb' hb)
  case case7 x ty f d args b hc ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, if_pos hc] at h ⊢
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb =>
        simp only [hbe, Option.map_some, Option.some.injEq] at h
        subst h
        rw [ih b' eb hbe hb]
        simp [impWipes]
  case case9 ty d s idx b ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, ↓reduceIte] at h ⊢
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb =>
        simp only [hbe, Option.map_some, Option.some.injEq] at h
        subst h
        rw [ih b' eb hbe hb]
        simp [impWipes]
  case case11 ty d s i b ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, ↓reduceIte] at h ⊢
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb =>
        simp only [hbe, Option.map_some, Option.some.injEq] at h
        subst h
        rw [ih b' eb hbe hb]
        simp [impWipes]
  case case13 x ty y u f d el args b hc ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, if_pos hc] at h ⊢
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb =>
        simp only [hbe, Option.map_some, Option.some.injEq] at h
        subst h
        rw [ih b' eb hbe hb]
        simp [impWipes, impWipesArms]
  case case4 a b hna hnone _iha _ihb =>
    intro c' e h _hc'
    rw [lowCTToImp.eq_3 _ _ hna] at h
    cases ha : lowCTToImp a <;> cases hb : lowCTToImp b <;> simp only [ha, hb, reduceCtorEq] at h
    exact (hnone _ _ ha hb).elim
  case case8 x ty f d args b hc =>
    intro c' e h _hc'
    simp only [lowCTToImp, if_neg hc, reduceCtorEq] at h
  case case10 x ty d s idx b hc =>
    intro c' e h _hc'
    simp only [lowCTToImp, if_neg hc, reduceCtorEq] at h
  case case12 x ty d s i b hc =>
    intro c' e h _hc'
    simp only [lowCTToImp, if_neg hc, reduceCtorEq] at h
  case case14 x ty y u f d el args b hc =>
    intro c' e h _hc'
    simp only [lowCTToImp, if_neg hc, reduceCtorEq] at h
  case case15 y k b ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, ↓reduceIte] at h ⊢
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb =>
        simp only [hbe, Option.map_some, Option.some.injEq] at h
        subst h
        rw [ih b' eb hbe hb]
        simp [impWipes]
  case case17 y se b f a a2 hsc ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, hsc, ↓reduceIte] at h ⊢
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb =>
        simp only [hbe, Option.map_some, Option.some.injEq] at h
        subst h
        rw [ih b' eb hbe hb]
        simp [impWipes]
  case case19 y se b hsc v i hlr ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, hsc, hlr, ↓reduceIte] at h ⊢
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb =>
        simp only [hbe, Option.map_some, Option.some.injEq] at h
        subst h
        rw [ih b' eb hbe hb]
        simp [impWipes]
  case case21 x y b s hc _ _ ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, scalarCallOfSExpr, limbReadOfSExpr, if_pos hc] at h ⊢
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb =>
        simp only [hbe, Option.map_some, Option.some.injEq] at h
        subst h
        rw [ih b' eb hbe hb]
        simp [impWipes]
  case case31 x ty d s b hc ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, if_pos hc] at h ⊢
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb =>
        simp only [hbe, Option.map_some, Option.some.injEq] at h
        subst h
        rw [ih b' eb hbe hb]
        simp [impWipes]
  case case33 =>
    intro c' e h _hc'
    rw [lowCTToImp.eq_19] at h
    · simp only [reduceCtorEq] at h
    all_goals assumption
  all_goals
    intro c' e h hc'
    first
      | (simp [appendWipes] at hc'; done)
      | simp_all [lowCTToImp]

/-! ## §4  The printed tail -/

/-- Every clearing chain has a `unitVal` tail. -/
theorem tailUnit_impWipeSeq (xs : List (String × String)) :
    TailUnit (impWipeSeq xs) = true := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simpa [impWipeSeq, TailUnit] using ih

/-- **The tail is unchanged.** `retOfUnit` finds the tail of the transformed
    expression exactly where it finds the tail of the original, so the
    `ppImpRustFnRet` path prints the clearing statements before the returned
    expression. -/
theorem tailUnit_impWipes (xs : List (String × String)) (e : ImpExpr) :
    TailUnit (impWipes xs e) = TailUnit e := by
  induction e using _root_.Hax.ImpExpr.ind with
  | unitVal => simpa [impWipes, TailUnit] using tailUnit_impWipeSeq xs
  | seq a b _ ihb => simpa [impWipes, TailUnit] using ihb
  | letBind x v b _ ihb => simpa [impWipes, TailUnit] using ihb
  | _ => simp [impWipes, TailUnit]

/-! ## §5  The cleared state -/

/-- Two runtime states with the same tower heap and the same scalar heap are
    equal. -/
theorem rustState_eq {a b : RustState} (ht : ∀ y, a.rsTower y = b.rsTower y)
    (hs : ∀ y, a.rsScalar y = b.rsScalar y) : a = b := by
  obtain ⟨t1, s1⟩ := a
  obtain ⟨t2, s2⟩ := b
  simp only [RustState.mk.injEq]
  exact ⟨funext ht, funext hs⟩

/-- The state with every slot named in `xs` bound to the default value at tower
    type `t`. -/
def wipeState (t : TowerType) (xs : List (String × String)) (rs : RustState) : RustState :=
  { rs with
    rsTower := fun y => if y ∈ xs.map Prod.fst then some ⟨t, default⟩ else rs.rsTower y }

/-- **Erasure.** Every cleared slot holds the default value. -/
theorem wipeState_mem {t : TowerType} {xs : List (String × String)} {rs : RustState}
    {p : String × String} (h : p ∈ xs) :
    (wipeState t xs rs).rsTower p.1 = some ⟨t, default⟩ := by
  simp [wipeState, List.mem_map.2 ⟨p, h, rfl⟩]

/-- **Every other slot is untouched.** A slot outside `xs` — the returned slot
    and every public slot among them — reads as it did before the clearing. -/
theorem wipeState_not_mem {t : TowerType} {xs : List (String × String)} {rs : RustState}
    {y : String} (h : y ∉ xs.map Prod.fst) :
    (wipeState t xs rs).rsTower y = rs.rsTower y := by
  simp [wipeState, h]

/-- The clearing leaves the scalar heap alone. -/
theorem wipeState_rsScalar (t : TowerType) (xs : List (String × String)) (rs : RustState) :
    (wipeState t xs rs).rsScalar = rs.rsScalar := rfl

/-- Clearing no slot is the identity. -/
theorem wipeState_nil (t : TowerType) (rs : RustState) : wipeState t [] rs = rs := by
  refine rustState_eq (fun y => ?_) (fun _ => rfl)
  simp [wipeState]

/-- Clearing the head slot and then the rest is clearing the whole list. -/
theorem wipeState_cons (t : TowerType) (a : String × String) (xs : List (String × String))
    (rs : RustState) :
    wipeState t xs (rsSetTower rs a.1 ⟨t, default⟩) = wipeState t (a :: xs) rs := by
  refine rustState_eq (fun y => ?_) (fun _ => rfl)
  by_cases hy : y ∈ xs.map Prod.fst
  · simp [wipeState, hy]
  · by_cases ha : y = a.1
    · subst ha
      simp [wipeState, hy, rsSetTower]
    · simp [wipeState, hy, ha, rsSetTower]

/-! ## §6  Semantics -/

/-- The clearing call overwrites its slot with the default value. -/
theorem exec_wipeCall_inv {N : Nat} {ls : LeafSpec} {w : String} {t : TowerType}
    {x : String} {rs rs' : RustState}
    (hw : ∀ old v : RustVal t, ls.call w t [t] old [⟨t, v⟩] = default)
    (h : RustExec N ls (wipeCall w t x) rs rs') :
    rs' = rsSetTower rs x ⟨t, default⟩ := by
  cases h with
  | call f dest args rs0 oldDestV argList hlook hargs htys =>
    obtain ⟨v, hv⟩ := htys ⟨x, t⟩ (by simp)
    subst hargs
    simp only [List.filterMap_cons, List.filterMap_nil, hv, List.map_cons, List.map_nil,
      Located.locDst, hw]
    rfl

/-- The clearing chain takes the state to `wipeState`. -/
theorem exec_wipeSeq_inv {N : Nat} {ls : LeafSpec} {t : TowerType} :
    ∀ (xs : List (String × String)) (rs rs' : RustState),
      (∀ p ∈ xs, ∀ old v : RustVal t, ls.call p.2 t [t] old [⟨t, v⟩] = default) →
      RustExec N ls (wipeSeq t xs .RSkip) rs rs' → rs' = wipeState t xs rs := by
  intro xs
  induction xs with
  | nil =>
    intro rs rs' _ h
    cases h
    exact (wipeState_nil t rs).symm
  | cons a rest ih =>
    intro rs rs' hw h
    cases h with
    | seq c1 c2 rs0 r1 rs1 h1 h2 =>
      rw [exec_wipeCall_inv (hw a (by simp)) h1] at h2
      rw [ih _ _ (fun p hp => hw p (List.mem_cons_of_mem _ hp)) h2, wipeState_cons]

/-- The clearing chain runs when its slots are bound at the clearing type. -/
theorem exec_wipeSeq {N : Nat} {ls : LeafSpec} {t : TowerType} :
    ∀ (xs : List (String × String)) (rs : RustState),
      (∀ p ∈ xs, ∀ old v : RustVal t, ls.call p.2 t [t] old [⟨t, v⟩] = default) →
      (∀ p ∈ xs, ∃ v : RustVal t, rs.rsTower p.1 = some ⟨t, v⟩) →
      RustExec N ls (wipeSeq t xs .RSkip) rs (wipeState t xs rs) := by
  intro xs
  induction xs with
  | nil =>
    intro rs _ _
    rw [wipeState_nil]
    exact .skip rs
  | cons a rest ih =>
    intro rs hw hb
    obtain ⟨va, hva⟩ := hb a (by simp)
    have hstep : RustExec N ls (wipeCall a.2 t a.1) rs (rsSetTower rs a.1 ⟨t, default⟩) := by
      have hcall :=
        RustExec.call (N := N) (leafSpec := ls) a.2 ⟨a.1, t⟩ [⟨a.1, t⟩] rs va _ (by
            simp [locatedLookup, hva]) rfl (by
            intro b hbm
            simp only [List.mem_singleton] at hbm
            subst hbm
            exact ⟨va, hva⟩)
      simp only [List.filterMap_cons, List.filterMap_nil, hva, List.map_cons, List.map_nil,
        Located.locDst, hw a (by simp)] at hcall
      exact hcall
    have hrest : ∀ p ∈ rest, ∃ v : RustVal t,
        (rsSetTower rs a.1 ⟨t, default⟩).rsTower p.1 = some ⟨t, v⟩ := by
      intro p hp
      by_cases hpa : p.1 = a.1
      · exact ⟨default, by rw [hpa]; simp [rsSetTower]⟩
      · obtain ⟨v, hv⟩ := hb p (List.mem_cons_of_mem _ hp)
        exact ⟨v, by rw [rsSetTower_other _ _ _ _ (Ne.symm hpa), hv]⟩
    rw [← wipeState_cons]
    exact .seq _ _ _ _ _ hstep (ih _ (fun p hp => hw p (List.mem_cons_of_mem _ hp)) hrest)

/-- **A run of the transformed program is a run of the original followed by the
    clearing.** The post-state of the transformed program is `wipeState` of a
    state the original program reaches from the same start state. -/
theorem exec_appendWipes_inv {N : Nat} {ls : LeafSpec} {t : TowerType}
    {xs : List (String × String)}
    (hw : ∀ p ∈ xs, ∀ old v : RustVal t, ls.call p.2 t [t] old [⟨t, v⟩] = default) :
    ∀ (c c' : LowCT) (rs rs' : RustState),
      appendWipes t xs c = some c' → RustExec N ls c' rs rs' →
      ∃ rs'', RustExec N ls c rs rs'' ∧ rs' = wipeState t xs rs'' := by
  intro c
  induction c with
  | RSkip =>
    intro c' rs rs' hc' hex
    simp only [appendWipes, Option.some.injEq] at hc'
    subst hc'
    exact ⟨rs, .skip rs, exec_wipeSeq_inv xs rs rs' hw hex⟩
  | RSeq a b _ ihb =>
    intro c' rs rs' hc' hex
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      cases hex with
      | seq c1 c2 rs0 r1 rs1 h1 h2 =>
        obtain ⟨rs'', hrun, heq⟩ := ihb b' r1 rs' hb h2
        exact ⟨rs'', .seq _ _ _ _ _ h1 hrun, heq⟩
  | RLetZero x ty b ihb =>
    intro c' rs rs' hc' hex
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      cases hex with
      | letZero x0 t0 body0 rs0 rs1 h1 =>
        obtain ⟨rs'', hrun, heq⟩ := ihb b' _ rs' hb h1
        exact ⟨rs'', .letZero _ _ _ _ _ hrun, heq⟩
  | RLetU64Zero x b ihb =>
    intro c' rs rs' hc' hex
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      cases hex with
      | letU64Zero x0 body0 rs0 rs1 h1 =>
        obtain ⟨rs'', hrun, heq⟩ := ihb b' _ rs' hb h1
        exact ⟨rs'', .letU64Zero _ _ _ _ hrun, heq⟩
  | _ =>
    intro c' rs rs' hc' _
    simp [appendWipes] at hc'

/-- **The transformed program runs whenever the original does**, provided the
    cleared slots are bound at the clearing type in the state the original
    reaches. -/
theorem exec_appendWipes {N : Nat} {ls : LeafSpec} {t : TowerType}
    {xs : List (String × String)}
    (hw : ∀ p ∈ xs, ∀ old v : RustVal t, ls.call p.2 t [t] old [⟨t, v⟩] = default) :
    ∀ (c c' : LowCT) (rs rs'' : RustState),
      appendWipes t xs c = some c' → RustExec N ls c rs rs'' →
      (∀ p ∈ xs, ∃ v : RustVal t, rs''.rsTower p.1 = some ⟨t, v⟩) →
      RustExec N ls c' rs (wipeState t xs rs'') := by
  intro c
  induction c with
  | RSkip =>
    intro c' rs rs'' hc' hex hb
    simp only [appendWipes, Option.some.injEq] at hc'
    subst hc'
    cases hex
    exact exec_wipeSeq xs rs hw hb
  | RSeq a b _ ihb =>
    intro c' rs rs'' hc' hex hb
    simp only [appendWipes] at hc'
    cases hbb : appendWipes t xs b with
    | none => simp [hbb] at hc'
    | some b' =>
      simp only [hbb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      cases hex with
      | seq c1 c2 rs0 r1 rs1 h1 h2 => exact .seq _ _ _ _ _ h1 (ihb b' r1 rs'' hbb h2 hb)
  | RLetZero x ty b ihb =>
    intro c' rs rs'' hc' hex hb
    simp only [appendWipes] at hc'
    cases hbb : appendWipes t xs b with
    | none => simp [hbb] at hc'
    | some b' =>
      simp only [hbb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      cases hex with
      | letZero x0 t0 body0 rs0 rs1 h1 => exact .letZero _ _ _ _ _ (ihb b' _ rs'' hbb h1 hb)
  | RLetU64Zero x b ihb =>
    intro c' rs rs'' hc' hex hb
    simp only [appendWipes] at hc'
    cases hbb : appendWipes t xs b with
    | none => simp [hbb] at hc'
    | some b' =>
      simp only [hbb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      cases hex with
      | letU64Zero x0 body0 rs0 rs1 h1 => exact .letU64Zero _ _ _ _ (ihb b' _ rs'' hbb h1 hb)
  | _ =>
    intro c' rs rs'' hc' _ _
    simp [appendWipes] at hc'

/-! ## §7  The front's located types -/

/-- The clearing calls already carry the front's located types when each clearing
    leaf is dispatched to the cleared slots' tower type. -/
theorem frontNF_wipeSeq {t : TowerType} (xs : List (String × String))
    (hw : ∀ p ∈ xs, towerOfCallName p.2 = t) :
    frontNF (wipeSeq t xs .RSkip) = wipeSeq t xs .RSkip := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    have ha := hw a (by simp)
    simp [wipeSeq, wipeCall, frontNF, retypeArgs, ha,
      ih (fun p hp => hw p (List.mem_cons_of_mem _ hp))]

/-- **The pass commutes with the front's located types.** -/
theorem frontNF_appendWipes {t : TowerType} (xs : List (String × String))
    (hw : ∀ p ∈ xs, towerOfCallName p.2 = t) :
    ∀ (c c' : LowCT) (e : ImpExpr), lowCTToImp c = some e →
      appendWipes t xs c = some c' →
      appendWipes t xs (frontNF c) = some (frontNF c') := by
  intro c
  induction c using lowCTToImp.induct
  case case1 =>
    intro c' e h hc'
    simp only [appendWipes, Option.some.injEq] at hc'
    subst hc'
    rw [frontNF_wipeSeq xs hw]
    rfl
  case case2 arr idx src b ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      cases hbe : lowCTToImp b with
      | none => simp [lowCTToImp, hbe] at h
      | some eb => simp only [frontNF, appendWipes, ih b' eb hbe hb, Option.map_some]
  case case3 a b hna ea eb hbe hae iha ihb =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      rw [frontNF.eq_3 _ _ hna, frontNF.eq_3 _ _ hna]
      simp only [appendWipes, ihb b' eb hbe hb, Option.map_some]
  case case7 x ty f d args b hc ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, if_pos hc] at h
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb => simp only [frontNF, appendWipes, ih b' eb hbe hb, Option.map_some]
  case case9 ty d s idx b ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, ↓reduceIte] at h
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb => simp only [frontNF, appendWipes, ih b' eb hbe hb, Option.map_some]
  case case11 ty d s i b ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, ↓reduceIte] at h
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb => simp only [frontNF, appendWipes, ih b' eb hbe hb, Option.map_some]
  case case13 x ty y u f d el args b hc ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, if_pos hc] at h
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb => simp only [frontNF, appendWipes, ih b' eb hbe hb, Option.map_some]
  case case4 a b hna hnone _iha _ihb =>
    intro c' e h _hc'
    rw [lowCTToImp.eq_3 _ _ hna] at h
    cases ha : lowCTToImp a <;> cases hb : lowCTToImp b <;> simp only [ha, hb, reduceCtorEq] at h
    exact (hnone _ _ ha hb).elim
  case case8 x ty f d args b hc =>
    intro c' e h _hc'
    simp only [lowCTToImp, if_neg hc, reduceCtorEq] at h
  case case10 x ty d s idx b hc =>
    intro c' e h _hc'
    simp only [lowCTToImp, if_neg hc, reduceCtorEq] at h
  case case12 x ty d s i b hc =>
    intro c' e h _hc'
    simp only [lowCTToImp, if_neg hc, reduceCtorEq] at h
  case case14 x ty y u f d el args b hc =>
    intro c' e h _hc'
    simp only [lowCTToImp, if_neg hc, reduceCtorEq] at h
  case case15 y k b ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, ↓reduceIte] at h
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb => simp only [frontNF, appendWipes, ih b' eb hbe hb, Option.map_some]
  case case17 y se b f a a2 hsc ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, hsc, ↓reduceIte] at h
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb => simp only [frontNF, appendWipes, ih b' eb hbe hb, Option.map_some]
  case case19 y se b hsc v i hlr ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, hsc, hlr, ↓reduceIte] at h
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb => simp only [frontNF, appendWipes, ih b' eb hbe hb, Option.map_some]
  case case21 x y b s hc _ _ ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, scalarCallOfSExpr, limbReadOfSExpr, if_pos hc] at h
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb => simp only [frontNF, appendWipes, ih b' eb hbe hb, Option.map_some]
  case case31 x ty d s b hc ih =>
    intro c' e h hc'
    simp only [appendWipes] at hc'
    cases hb : appendWipes t xs b with
    | none => simp [hb] at hc'
    | some b' =>
      simp only [hb, Option.map_some, Option.some.injEq] at hc'
      subst hc'
      simp only [lowCTToImp, if_pos hc] at h
      cases hbe : lowCTToImp b with
      | none => simp [hbe] at h
      | some eb => simp only [frontNF, appendWipes, ih b' eb hbe hb, Option.map_some]
  case case33 =>
    intro c' e h _hc'
    rw [lowCTToImp.eq_19] at h
    · simp only [reduceCtorEq] at h
    all_goals assumption
  all_goals
    intro c' e h hc'
    first
      | (simp [appendWipes] at hc'; done)
      | simp_all [lowCTToImp]

end CatCrypt.Crypto.Hax
