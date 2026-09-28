/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CT.LowCTLeakage

/-!
# A flow-sensitive security-level checker for `LowCT`

`levelCheck M lt c` threads a public/secret level per slot through the program
`c`, starting from the split `lt`, and returns the split at exit or `none`.

* A slot's level after a write is the join of the levels of what the write
  reads: arithmetic (`RScalarSetExpr`, `RLimbStoreExpr`), `RSelect` (its
  selector and both sources), leaf calls (their arguments and the destination's
  old value), array and tuple loads and stores (the old value and the source),
  and `RCopy` (the source only, so a copy onto a secret slot from a public one
  makes the slot public).
* The checker rejects only the four observable positions of the `RustExecLeak`
  leakage model: the guard of `RIfNz` and `RWhileNz`, the index of `RArrLoad`
  and `RArrStore`, the bound of `RForRuntime`, and the operands of a
  scalar-expression node or a leaf call that the model classes variable time.
* Loops (`RWhileNz`, `RFor`, `RForRuntime`) take a loop-invariant split found by
  a bounded fixpoint iteration (`loopFix`): the split is joined with the body's
  output split until the output is below it.
* `RFnDef` and `RFnCall` have no `RustExec` rule and are rejected.

Levels are kept as override lists over the base split (`Levels`), with separate
lists for the scalar heap and the tower heap, so the order between two splits is
decidable. `levelCheck_sound` is the soundness theorem: an accepted program is
`LowCTConstantTime` for `lt`, and two runs from states agreeing on the public
slots of `lt` end in states agreeing on the public slots of the returned split.
It has no hypothesis on the program or on the leaves.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CT

open CatCrypt.Crypto.Jasmin.LowCT

namespace LevelCheck

/-! ## 1. Split override lists -/

/-- A level override list over a base split: `(x, true)` marks `x` secret and
    `(x, false)` public; the first entry for a name is the one read. -/
abbrev Overrides := List (String × Bool)

/-- The level of `x` (`true` = secret) under the override list `l` over the base
    split `β`. -/
def lk (β : String → Bool) : Overrides → String → Bool
  | [], x => β x
  | (y, b) :: l, x => if x = y then b else lk β l x

theorem lk_of_not_mem (β : String → Bool) :
    ∀ (l : Overrides) (x : String), x ∉ l.map Prod.fst → lk β l x = β x
  | [], _, _ => rfl
  | (y, b) :: l, x, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [lk, h.1, if_false]
    exact lk_of_not_mem β l x h.2

theorem lk_map (β : String → Bool) (f : String → Bool) :
    ∀ (ks : List String) (x : String),
      lk β (ks.map fun y => (y, f y)) x = if x ∈ ks then f x else β x
  | [], _ => by simp [lk]
  | k :: ks, x => by
    by_cases h : x = k
    · subst h; simp [lk]
    · simp [lk, h, lk_map β f ks x]

theorem lk_append_map (β : String → Bool) (b : Bool) :
    ∀ (ks : List String) (l : Overrides) (x : String),
      lk β (ks.map (fun y => (y, b)) ++ l) x = if x ∈ ks then b else lk β l x
  | [], _, _ => by simp
  | k :: ks, l, x => by
    by_cases h : x = k
    · subst h; simp [lk]
    · simp [lk, h, lk_append_map β b ks l x]

/-- The override list `a` is below `b`: every name secret under `a` is secret
    under `b`. Names in neither list read the base split in both. -/
def leO (β : String → Bool) (a b : Overrides) : Bool :=
  (a.map Prod.fst ++ b.map Prod.fst).all fun x => !lk β a x || lk β b x

theorem leO_spec {β : String → Bool} {a b : Overrides} (h : leO β a b = true) (x : String)
    (hx : lk β a x = true) : lk β b x = true := by
  by_cases hk : x ∈ a.map Prod.fst ++ b.map Prod.fst
  · have := List.all_eq_true.1 h x hk
    simpa [hx] using this
  · simp only [List.mem_append, not_or] at hk
    rw [lk_of_not_mem β a x hk.1] at hx
    rwa [lk_of_not_mem β b x hk.2]

/-- The pointwise join of two override lists. -/
def joinO (β : String → Bool) (a b : Overrides) : Overrides :=
  (a.map Prod.fst ++ b.map Prod.fst).map fun x => (x, lk β a x || lk β b x)

theorem lk_joinO (β : String → Bool) (a b : Overrides) (x : String) :
    lk β (joinO β a b) x = (lk β a x || lk β b x) := by
  unfold joinO
  rw [lk_map]
  split
  · rfl
  · rename_i hk
    simp only [List.mem_append, not_or] at hk
    rw [lk_of_not_mem β a x hk.1, lk_of_not_mem β b x hk.2, Bool.or_self]

/-! ## 2. Splits of the two heaps -/

/-- A split of the scalar heap and of the tower heap, as override lists over a
    common base split. -/
structure Levels where
  sc : Overrides := []
  tw : Overrides := []
  deriving Inhabited

namespace Levels

/-- Set the level of the scalar slot `x`. -/
def setSc (L : Levels) (x : String) (b : Bool) : Levels := { L with sc := (x, b) :: L.sc }

/-- Set the level of the tower slot `x`. -/
def setTw (L : Levels) (x : String) (b : Bool) : Levels := { L with tw := (x, b) :: L.tw }

/-- Set the level of every tower slot in `ds`. -/
def setManyTw (L : Levels) (ds : List Located) (b : Bool) : Levels :=
  { L with tw := (ds.map (·.locVar)).map (fun y => (y, b)) ++ L.tw }

/-- The pointwise join. -/
def join (β : String → Bool) (A B : Levels) : Levels := ⟨joinO β A.sc B.sc, joinO β A.tw B.tw⟩

/-- The decidable order: every slot secret under `A` is secret under `B`. -/
def le (β : String → Bool) (A B : Levels) : Bool := leO β A.sc B.sc && leO β A.tw B.tw

/-- The order as a proposition. -/
def Le (β : String → Bool) (A B : Levels) : Prop :=
  ∀ x, (lk β A.sc x = true → lk β B.sc x = true) ∧ (lk β A.tw x = true → lk β B.tw x = true)

theorem Le.refl (β : String → Bool) (A : Levels) : Le β A A := fun _ => ⟨id, id⟩

theorem Le.trans {β : String → Bool} {A B C : Levels} (h₁ : Le β A B) (h₂ : Le β B C) :
    Le β A C := fun x => ⟨fun h => (h₂ x).1 ((h₁ x).1 h), fun h => (h₂ x).2 ((h₁ x).2 h)⟩

theorem le_spec {β : String → Bool} {A B : Levels} (h : le β A B = true) : Le β A B := by
  simp only [le, Bool.and_eq_true] at h
  exact fun x => ⟨leO_spec h.1 x, leO_spec h.2 x⟩

theorem le_join_left (β : String → Bool) (A B : Levels) : Le β A (join β A B) := fun x =>
  ⟨fun h => by simp [join, lk_joinO, h], fun h => by simp [join, lk_joinO, h]⟩

theorem le_join_right (β : String → Bool) (A B : Levels) : Le β B (join β A B) := fun x =>
  ⟨fun h => by simp [join, lk_joinO, h], fun h => by simp [join, lk_joinO, h]⟩

end Levels

/-! ## 3. The state relation -/

/-- Two states agree on the public slots of `L`: equal scalar values at every
    public scalar name and equal tower values at every public tower name. -/
def Rel (β : String → Bool) (L : Levels) (rs₁ rs₂ : RustState) : Prop :=
  ∀ x, (lk β L.sc x = false → rs₁.rsScalar x = rs₂.rsScalar x) ∧
    (lk β L.tw x = false → rs₁.rsTower x = rs₂.rsTower x)

theorem Rel.mono {β : String → Bool} {A B : Levels} {rs₁ rs₂ : RustState}
    (hle : Levels.Le β A B) (h : Rel β A rs₁ rs₂) : Rel β B rs₁ rs₂ := fun x =>
  ⟨fun hb => (h x).1 (Bool.eq_false_iff.2 fun ha => by simp [(hle x).1 ha] at hb),
   fun hb => (h x).2 (Bool.eq_false_iff.2 fun ha => by simp [(hle x).2 ha] at hb)⟩

theorem Rel.setTower {β : String → Bool} {L : Levels} {rs₁ rs₂ : RustState}
    (h : Rel β L rs₁ rs₂) (x : String) (b : Bool) (v₁ v₂ : Σ t : TowerType, RustVal t)
    (hv : b = false → v₁ = v₂) :
    Rel β (L.setTw x b) (rsSetTower rs₁ x v₁) (rsSetTower rs₂ x v₂) := by
  intro y
  refine ⟨fun hy => (h y).1 hy, fun hy => ?_⟩
  by_cases hyx : y = x
  · subst hyx
    simp only [Levels.setTw, lk, if_true] at hy
    simp [rsSetTower, hv hy]
  · simp only [Levels.setTw, lk, hyx, if_false] at hy
    simp [rsSetTower, hyx, (h y).2 hy]

theorem Rel.setTower_secret {β : String → Bool} {L : Levels} {rs₁ rs₂ : RustState}
    (h : Rel β L rs₁ rs₂) {x : String} (hx : lk β L.tw x = true)
    (v₁ v₂ : Σ t : TowerType, RustVal t) :
    Rel β L (rsSetTower rs₁ x v₁) (rsSetTower rs₂ x v₂) := by
  intro y
  refine ⟨fun hy => (h y).1 hy, fun hy => ?_⟩
  by_cases hyx : y = x
  · subst hyx; simp [hx] at hy
  · simp [rsSetTower, hyx, (h y).2 hy]

theorem Rel.setTower_eq {β : String → Bool} {L : Levels} {rs₁ rs₂ : RustState}
    (h : Rel β L rs₁ rs₂) (x : String) (v : Σ t : TowerType, RustVal t) :
    Rel β L (rsSetTower rs₁ x v) (rsSetTower rs₂ x v) := by
  intro y
  refine ⟨fun hy => (h y).1 hy, fun hy => ?_⟩
  by_cases hyx : y = x
  · simp [rsSetTower, hyx]
  · simp [rsSetTower, hyx, (h y).2 hy]

theorem Rel.setScalar {β : String → Bool} {L : Levels} {rs₁ rs₂ : RustState}
    (h : Rel β L rs₁ rs₂) (x : String) (b : Bool) (v₁ v₂ : Nat) (hv : b = false → v₁ = v₂) :
    Rel β (L.setSc x b) (rsSetScalar rs₁ x v₁) (rsSetScalar rs₂ x v₂) := by
  intro y
  refine ⟨fun hy => ?_, fun hy => (h y).2 hy⟩
  by_cases hyx : y = x
  · subst hyx
    simp only [Levels.setSc, lk, if_true] at hy
    simp [rsSetScalar, hv hy]
  · simp only [Levels.setSc, lk, hyx, if_false] at hy
    simp [rsSetScalar, hyx, (h y).1 hy]

theorem lookup_eq {β : String → Bool} {L : Levels} {rs₁ rs₂ : RustState}
    (h : Rel β L rs₁ rs₂) {loc : Located} (hl : lk β L.tw loc.locVar = false) :
    locatedLookup rs₁ loc = locatedLookup rs₂ loc := by
  unfold locatedLookup; rw [(h loc.locVar).2 hl]

/-! ## 4. Levels of scalar expressions -/

/-- The level of a scalar expression: the join of the scalar slots and tower
    limbs it reads. -/
def sLvl (β : String → Bool) (L : Levels) : SExpr → Bool
  | .SVar x => lk β L.sc x
  | .SLit _ => false
  | .SLimb v _ => lk β L.tw v
  | .SAdd a b | .SSub a b | .SMul a b | .SShr a b | .SShl a b | .SAnd a b | .SXor a b
  | .SLt a b | .SAsr a b | .SMulS a b | .SMulHiU a b | .SMulHiS a b =>
      sLvl β L a || sLvl β L b

/-- The node `e` with operands `a` and `b` leaks nothing secret: either its
    mnemonic keeps operands unobservable in the regime, or both operands are
    public. -/
def nodeOk (M : LowCTLeakModel) (β : String → Bool) (L : Levels) (e a b : SExpr) : Bool :=
  match M.mnem e with
  | some m => !M.regime.leaksOperands m || (!sLvl β L a && !sLvl β L b)
  | none => true

/-- Every node of the scalar expression satisfies `nodeOk`. -/
def sVtOk (M : LowCTLeakModel) (β : String → Bool) (L : Levels) : SExpr → Bool
  | .SVar _ | .SLit _ | .SLimb _ _ => true
  | .SAdd a b => sVtOk M β L a && sVtOk M β L b && nodeOk M β L (.SAdd a b) a b
  | .SSub a b => sVtOk M β L a && sVtOk M β L b && nodeOk M β L (.SSub a b) a b
  | .SMul a b => sVtOk M β L a && sVtOk M β L b && nodeOk M β L (.SMul a b) a b
  | .SShr a b => sVtOk M β L a && sVtOk M β L b && nodeOk M β L (.SShr a b) a b
  | .SShl a b => sVtOk M β L a && sVtOk M β L b && nodeOk M β L (.SShl a b) a b
  | .SAnd a b => sVtOk M β L a && sVtOk M β L b && nodeOk M β L (.SAnd a b) a b
  | .SXor a b => sVtOk M β L a && sVtOk M β L b && nodeOk M β L (.SXor a b) a b
  | .SLt a b => sVtOk M β L a && sVtOk M β L b && nodeOk M β L (.SLt a b) a b
  | .SAsr a b => sVtOk M β L a && sVtOk M β L b && nodeOk M β L (.SAsr a b) a b
  | .SMulS a b => sVtOk M β L a && sVtOk M β L b && nodeOk M β L (.SMulS a b) a b
  | .SMulHiU a b => sVtOk M β L a && sVtOk M β L b && nodeOk M β L (.SMulHiU a b) a b
  | .SMulHiS a b => sVtOk M β L a && sVtOk M β L b && nodeOk M β L (.SMulHiS a b) a b

theorem sLvl_eval {β : String → Bool} {L : Levels} {rs₁ rs₂ : RustState}
    (h : Rel β L rs₁ rs₂) (e : SExpr) (he : sLvl β L e = false) :
    e.evalState rs₁ = e.evalState rs₂ := by
  induction e with
  | SVar x => exact (h x).1 he
  | SLit _ => rfl
  | SLimb v i => simp only [SExpr.evalState, rsTowerLimb, (h v).2 he]
  | _ a b iha ihb =>
    simp only [sLvl, Bool.or_eq_false_iff] at he
    simp only [SExpr.evalState, iha he.1, ihb he.2]

theorem nodeLeak_eq {M : LowCTLeakModel} {β : String → Bool} {L : Levels}
    {rs₁ rs₂ : RustState} (h : Rel β L rs₁ rs₂) (e a b : SExpr)
    (hok : nodeOk M β L e a b = true) : nodeLeak M rs₁ e a b = nodeLeak M rs₂ e a b := by
  unfold nodeOk at hok
  unfold nodeLeak
  cases hm : M.mnem e with
  | none => rfl
  | some m =>
    simp only [hm] at hok
    cases hl : M.regime.leaksOperands m with
    | false => simp [hl]
    | true =>
      simp only [hl, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hok
      simp [sLvl_eval h a hok.1, sLvl_eval h b hok.2]

theorem sexprLeak_eq {M : LowCTLeakModel} {β : String → Bool} {L : Levels}
    {rs₁ rs₂ : RustState} (h : Rel β L rs₁ rs₂) (e : SExpr) (he : sVtOk M β L e = true) :
    sexprLeak M rs₁ e = sexprLeak M rs₂ e := by
  induction e with
  | SVar _ => rfl
  | SLit _ => rfl
  | SLimb _ _ => rfl
  | _ a b iha ihb =>
    simp only [sVtOk, Bool.and_eq_true] at he
    simp only [sexprLeak, iha he.1.1, ihb he.1.2, nodeLeak_eq h _ a b he.2]

/-! ## 5. Leaf calls -/

/-- Some slot in `ls` is secret. -/
def secArgs (β : String → Bool) (L : Levels) (ls : List Located) : Bool :=
  ls.any fun a => lk β L.tw a.locVar

/-- A leaf call leaks nothing secret: the leaf is not variable time, or its
    arguments are public. -/
def vtCallOk (M : LowCTLeakModel) (β : String → Bool) (L : Levels) (f : String)
    (args : List Located) : Bool :=
  !M.leafVT f || !secArgs β L args

theorem secArgs_false {β : String → Bool} {L : Levels} {ls : List Located}
    (h : secArgs β L ls = false) : ∀ a ∈ ls, lk β L.tw a.locVar = false := by
  intro a ha
  unfold secArgs at h
  rw [List.any_eq_false] at h
  simpa using h a ha

theorem filterMap_tower_eq {rs₁ rs₂ : RustState} :
    ∀ (ls : List Located), (∀ a ∈ ls, rs₁.rsTower a.locVar = rs₂.rsTower a.locVar) →
      ls.filterMap (fun a => rs₁.rsTower a.locVar) = ls.filterMap (fun a => rs₂.rsTower a.locVar)
  | [], _ => rfl
  | a :: ls, h => by
    simp only [List.filterMap_cons, h a (by simp),
      filterMap_tower_eq ls (fun b hb => h b (by simp [hb]))]

theorem argList_eq {β : String → Bool} {L : Levels} {rs₁ rs₂ : RustState}
    (hR : Rel β L rs₁ rs₂) {ls : List Located} (h : secArgs β L ls = false) :
    ls.filterMap (fun a => rs₁.rsTower a.locVar) = ls.filterMap (fun a => rs₂.rsTower a.locVar) :=
  filterMap_tower_eq ls fun a ha => (hR a.locVar).2 (secArgs_false h a ha)

theorem callLeak_eq {M : LowCTLeakModel} {β : String → Bool} {L : Levels}
    {rs₁ rs₂ : RustState} (hR : Rel β L rs₁ rs₂) {f : String} {ls : List Located}
    (hvt : vtCallOk M β L f ls = true) :
    callLeak M f (ls.filterMap fun a => rs₁.rsTower a.locVar) =
      callLeak M f (ls.filterMap fun a => rs₂.rsTower a.locVar) := by
  unfold callLeak
  unfold vtCallOk at hvt
  cases hf : M.leafVT f with
  | false => rfl
  | true =>
    simp only [hf, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at hvt
    rw [argList_eq hR hvt]

/-- The check of a one-destination leaf call `dest := f(args)` whose value is a
    function of `dest`'s old value and `args`. -/
def callOne (β : String → Bool) (M : LowCTLeakModel) (f : String) (dest : Located)
    (args : List Located) (L : Levels) : Option Levels :=
  if vtCallOk M β L f args then some (L.setTw dest.locVar (secArgs β L (dest :: args)))
  else none

theorem callNUpdate_secret {β : String → Bool} {L : Levels} (lsp : LeafSpec) (f : String)
    (argTs : List TowerType) (a₁ a₂ : List (Σ t : TowerType, RustVal t)) :
    ∀ (ds : List Located) (i : Nat) (rs₁ rs₂ : RustState), Rel β L rs₁ rs₂ →
      (∀ d ∈ ds, lk β L.tw d.locVar = true) →
      Rel β L (callNUpdate lsp f argTs a₁ i ds rs₁) (callNUpdate lsp f argTs a₂ i ds rs₂)
  | [], _, _, _, h, _ => h
  | d :: ds, i, _, _, h, hd =>
    callNUpdate_secret lsp f argTs a₁ a₂ ds (i + 1) _ _
      (h.setTower_secret (hd d (by simp)) _ _) (fun d' hd' => hd d' (by simp [hd']))

theorem callNUpdate_public {β : String → Bool} {L : Levels} (lsp : LeafSpec) (f : String)
    (argTs : List TowerType) (a : List (Σ t : TowerType, RustVal t)) :
    ∀ (ds : List Located) (i : Nat) (rs₁ rs₂ : RustState), Rel β L rs₁ rs₂ →
      (∀ d ∈ ds, lk β L.tw d.locVar = false) →
      Rel β L (callNUpdate lsp f argTs a i ds rs₁) (callNUpdate lsp f argTs a i ds rs₂)
  | [], _, _, _, h, _ => h
  | d :: ds, i, rs₁, rs₂, h, hd => by
    have hl := lookup_eq h (hd d (by simp))
    simp only [callNUpdate, locatedUpdate, hl]
    exact callNUpdate_public lsp f argTs a ds (i + 1) _ _ (h.setTower_eq _ _)
      (fun d' hd' => hd d' (by simp [hd']))

theorem lk_setManyTw (β : String → Bool) (L : Levels) (ds : List Located) (b : Bool)
    (x : String) :
    lk β (L.setManyTw ds b).tw x = if x ∈ ds.map (·.locVar) then b else lk β L.tw x := by
  simp only [Levels.setManyTw]
  rw [lk_append_map]

/-! ## 6. Loops -/

/-- The fixpoint search for a loop-invariant split: from `I`, compute the body's
    output split `O`; stop with `I` when `O` is below `I`, else continue from
    the join. The search returns `none` when the body is rejected or the fuel
    is exhausted. -/
def loopFix (β : String → Bool) (step : Levels → Option Levels) : Nat → Levels → Option Levels
  | 0, _ => none
  | k + 1, I =>
    match step I with
    | none => none
    | some O => if Levels.le β O I then some I else loopFix β step k (Levels.join β I O)

theorem loopFix_spec {β : String → Bool} {step : Levels → Option Levels} :
    ∀ (k : Nat) (I₀ I : Levels), loopFix β step k I₀ = some I →
      Levels.Le β I₀ I ∧ ∃ O, step I = some O ∧ Levels.Le β O I
  | 0, _, _, h => by simp [loopFix] at h
  | k + 1, I₀, I, h => by
    simp only [loopFix] at h
    cases hs : step I₀ with
    | none => simp [hs] at h
    | some O =>
      simp only [hs] at h
      split at h
      · rename_i hle
        cases h
        exact ⟨Levels.Le.refl β _, O, hs, Levels.le_spec hle⟩
      · obtain ⟨hle, rest⟩ := loopFix_spec k _ _ h
        exact ⟨(Levels.le_join_left β I₀ O).trans hle, rest⟩

/-- The fuel of the fixpoint search of a loop: a count of the write sites of
    its body, plus one. -/
def loopFuel : LowCT → Nat
  | .RSeq a b => loopFuel a + loopFuel b
  | .RIfNz _ a b => loopFuel a + loopFuel b
  | .RFnDef _ _ _ a b => loopFuel a + loopFuel b
  | .RLetZero _ _ b => loopFuel b + 1
  | .RLetU64Zero _ b => loopFuel b + 1
  | .RWhileNz _ b => loopFuel b + 1
  | .RFor _ _ b => loopFuel b + 1
  | .RForRuntime _ _ b => loopFuel b + 1
  | .RBlock b => loopFuel b + 1
  | .RCallN _ ds _ => ds.length + 1
  | .RFnCall _ ds _ => ds.length + 1
  | .RCallSwap .. => 2
  | .RCloneCall .. => 2
  | _ => 1

/-! ## 7. The checker -/

/-- The flow-sensitive level checker over the base split `β`: the split at
    exit, or `none` when the program has a secret guard, a secret array index,
    a secret runtime loop bound, a secret operand of a variable-time node or
    leaf, or a loop for which the fixpoint search fails. -/
def check (β : String → Bool) (M : LowCTLeakModel) : LowCT → Levels → Option Levels
  | .RSkip, L => some L
  | .RSeq c1 c2, L => (check β M c1 L).bind (check β M c2)
  | .RLetZero x _ body, L => check β M body (L.setTw x false)
  | .RLetU64Zero x body, L => check β M body (L.setSc x false)
  | .RScalarSet x _, L => some (L.setSc x false)
  | .RCall f dest args, L => callOne β M f dest args L
  | .RCallSwap f d1 d2 args, L => (callOne β M f d1 args L).bind (callOne β M f d2 args)
  | .RCloneCall cv _ old f dest args, L =>
      callOne β M f dest args (L.setTw cv (lk β L.tw old.locVar))
  | .RIfNz e ct cf, L =>
      if lk β L.sc e then none
      else (check β M ct L).bind fun A => (check β M cf L).map fun B => Levels.join β A B
  | .RWhileNz e body, L =>
      loopFix β (fun I => if lk β I.sc e then none else check β M body I)
        (loopFuel body + 1) L
  | .RFor x _ body, L =>
      loopFix β (fun I => check β M body (I.setSc x false)) (loopFuel body + 1) L
  | .RLimbStore _ _ _, L => some L
  | .RLimbStoreExpr loc _ e, L =>
      if sVtOk M β L e then some (L.setTw loc.locVar (lk β L.tw loc.locVar || sLvl β L e))
      else none
  | .RCallN f dests args, L =>
      if vtCallOk M β L f args then some (L.setManyTw dests (secArgs β L (dests ++ args)))
      else none
  | .RSelect dst sel s0 s1, L =>
      some (L.setTw dst.locVar (lk β L.sc sel || lk β L.tw s0.locVar || lk β L.tw s1.locVar))
  | .RAssert _, L => some L
  | .RBlock body, L => check β M body L
  | .RFnDef .., _ => none
  | .RFnCall .., _ => none
  | .RTupleLoad dst src _, L =>
      some (L.setTw dst.locVar (lk β L.tw dst.locVar || lk β L.tw src.locVar))
  | .RArrStore arr i src, L =>
      if lk β L.sc i then none
      else some (L.setTw arr.locVar (lk β L.tw arr.locVar || lk β L.tw src.locVar))
  | .RArrLoad dst src i, L =>
      if lk β L.sc i then none
      else some (L.setTw dst.locVar (lk β L.tw dst.locVar || lk β L.tw src.locVar))
  | .RArrStoreLit arr _ src, L =>
      some (L.setTw arr.locVar (lk β L.tw arr.locVar || lk β L.tw src.locVar))
  | .RArrLoadLit dst src _, L =>
      some (L.setTw dst.locVar (lk β L.tw dst.locVar || lk β L.tw src.locVar))
  | .RScalarSetExpr x e, L =>
      if sVtOk M β L e then some (L.setSc x (sLvl β L e)) else none
  | .RCallDstThreaded f dst args, L => callOne β M f dst (dst :: args) L
  | .RForRuntime x bound body, L =>
      if sLvl β L bound || !sVtOk M β L bound then none
      else loopFix β (fun I => check β M body (I.setSc x false)) (loopFuel body + 1) L
  | .RCopy dst src, L => some (L.setTw dst.locVar (lk β L.tw src.locVar))

/-! ## 8. Soundness -/

variable {N : Nat} {leafSpec : LeafSpec} {M : LowCTLeakModel} {β : String → Bool}

/-- Two runs of `c` from states related by `L` have equal traces and end in
    states related by `L'`. -/
def Sound (N : Nat) (leafSpec : LeafSpec) (M : LowCTLeakModel) (β : String → Bool)
    (c : LowCT) (L L' : Levels) : Prop :=
  ∀ rs₁ rs₂ t₁ t₂ r₁ r₂, Rel β L rs₁ rs₂ →
    RustExecLeak N leafSpec M c rs₁ t₁ r₁ → RustExecLeak N leafSpec M c rs₂ t₂ r₂ →
    t₁ = t₂ ∧ Rel β L' r₁ r₂

theorem callOne_sound {f : String} {dest : Located} {args : List Located} {L L' : Levels}
    (hc : callOne β M f dest args L = some L') :
    Sound N leafSpec M β (.RCall f dest args) L L' := by
  intro rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
  unfold callOne at hc
  split at hc
  · rename_i hvt
    cases hc
    cases h₁ with
    | call _ _ _ _ o₁ al₁ hl₁ ha₁ _ =>
    cases h₂ with
    | call _ _ _ _ o₂ al₂ hl₂ ha₂ _ =>
    subst ha₁ ha₂
    refine ⟨callLeak_eq hR hvt, ?_⟩
    unfold locatedUpdate
    refine hR.setTower _ _ _ _ fun hs => ?_
    have hd := secArgs_false hs dest (by simp)
    have hargs : secArgs β L args = false := by
      unfold secArgs at hs ⊢; simp only [List.any_cons, Bool.or_eq_false_iff] at hs; exact hs.2
    rw [lookup_eq hR hd, hl₂] at hl₁
    cases hl₁
    rw [argList_eq hR hargs]
  · cases hc

theorem callDst_sound {f : String} {dst : Located} {args : List Located} {L L' : Levels}
    (hc : callOne β M f dst (dst :: args) L = some L') :
    Sound N leafSpec M β (.RCallDstThreaded f dst args) L L' := by
  intro rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
  unfold callOne at hc
  split at hc
  · rename_i hvt
    cases hc
    cases h₁ with
    | callDstThreaded _ _ _ _ o₁ al₁ hl₁ ha₁ _ =>
    cases h₂ with
    | callDstThreaded _ _ _ _ o₂ al₂ hl₂ ha₂ _ =>
    subst ha₁ ha₂
    refine ⟨callLeak_eq hR hvt, ?_⟩
    unfold locatedUpdate
    refine hR.setTower _ _ _ _ fun hs => ?_
    have hd := secArgs_false hs dst (by simp)
    have hargs : secArgs β L (dst :: args) = false := by
      unfold secArgs at hs ⊢; simp only [List.any_cons, Bool.or_eq_false_iff] at hs ⊢; exact hs.2
    rw [lookup_eq hR hd, hl₂] at hl₁
    cases hl₁
    rw [argList_eq hR hargs]
  · cases hc

theorem for_sound {x : String} {body : LowCT} {I O : Levels}
    (hb : Sound N leafSpec M β body (I.setSc x false) O) (hle : Levels.Le β O I) :
    ∀ (n : Nat) (rs₁ rs₂ : RustState) (t₁ t₂ : List CTLeak) (r₁ r₂ : RustState),
      Rel β I rs₁ rs₂ → RustExecLeak N leafSpec M (.RFor x n body) rs₁ t₁ r₁ →
      RustExecLeak N leafSpec M (.RFor x n body) rs₂ t₂ r₂ → t₁ = t₂ ∧ Rel β I r₁ r₂
  | 0, _, _, _, _, _, _, hR, h₁, h₂ => by
    cases h₁; cases h₂; exact ⟨rfl, hR⟩
  | n + 1, _, _, _, _, _, _, hR, h₁, h₂ => by
    cases h₁ with
    | forSucc _ _ _ _ m₁ _ u₁ v₁ a₁ b₁ =>
    cases h₂ with
    | forSucc _ _ _ _ m₂ _ u₂ v₂ a₂ b₂ =>
    obtain ⟨e₁, hm⟩ := for_sound hb hle n _ _ _ _ _ _ hR a₁ a₂
    obtain ⟨e₂, hr⟩ := hb _ _ _ _ _ _ (hm.setScalar x false n n fun _ => rfl) b₁ b₂
    exact ⟨by rw [e₁, e₂], hr.mono hle⟩

theorem while_sound {e : String} {body : LowCT} {I O : Levels}
    (he : lk β I.sc e = false) (hb : Sound N leafSpec M β body I O) (hle : Levels.Le β O I) :
    ∀ {c : LowCT} {rs₁ : RustState} {t₁ : List CTLeak} {r₁ : RustState},
      RustExecLeak N leafSpec M c rs₁ t₁ r₁ → c = .RWhileNz e body →
      ∀ rs₂ t₂ r₂, Rel β I rs₁ rs₂ → RustExecLeak N leafSpec M (.RWhileNz e body) rs₂ t₂ r₂ →
        t₁ = t₂ ∧ Rel β I r₁ r₂ := by
  intro c rs₁ t₁ r₁ h₁
  induction h₁ with
  | whileFalse e' body' rs hv =>
    intro hc rs₂ t₂ r₂ hR h₂
    cases hc
    cases h₂ with
    | whileFalse => exact ⟨rfl, hR⟩
    | whileTrue _ _ _ _ _ v _ _ hv₂ hv0 =>
      exact absurd (hv₂ ▸ ((hR e).1 he).symm.trans hv) hv0
  | whileTrue e' body' rs m₁ r₁ v u₁ w₁ hv hv0 hb₁ _ _ ih₂ =>
    intro hc rs₂ t₂ r₂ hR h₂
    cases hc
    cases h₂ with
    | whileFalse _ _ _ hv₂ => exact absurd (hv ▸ ((hR e).1 he).trans hv₂) hv0
    | whileTrue _ _ _ m₂ _ v₂ u₂ w₂ _ _ hb₂ hw₂ =>
      obtain ⟨e₁, hm⟩ := hb _ _ _ _ _ _ hR hb₁ hb₂
      obtain ⟨e₂, hr⟩ := ih₂ rfl _ _ _ (hm.mono hle) hw₂
      exact ⟨by rw [e₁, e₂], hr⟩
  | _ => intro hc; cases hc

theorem Sound.mono {c : LowCT} {L L' L'' : Levels} (h : Sound N leafSpec M β c L L')
    (hle : Levels.Le β L' L'') : Sound N leafSpec M β c L L'' := fun _ _ _ _ _ _ hR h₁ h₂ =>
  (h _ _ _ _ _ _ hR h₁ h₂).imp_right (Rel.mono hle)

/-- Soundness of the checker: an accepted program run twice from states related
    by the entry split has equal traces and ends in states related by the exit
    split. -/
theorem check_sound : ∀ (c : LowCT) (L L' : Levels), check β M c L = some L' →
    Sound N leafSpec M β c L L' := by
  intro c
  induction c with
  | RSkip =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check, Option.some.injEq] at hc; subst hc
    cases h₁; cases h₂; exact ⟨rfl, hR⟩
  | RSeq c1 c2 ih1 ih2 =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check] at hc
    cases hc1 : check β M c1 L with
    | none => simp [hc1] at hc
    | some L1 =>
      simp only [hc1, Option.bind_some] at hc
      cases h₁ with
      | seq _ _ _ m₁ _ u₁ v₁ a₁ b₁ =>
      cases h₂ with
      | seq _ _ _ m₂ _ u₂ v₂ a₂ b₂ =>
      obtain ⟨e₁, hm⟩ := ih1 L L1 hc1 _ _ _ _ _ _ hR a₁ a₂
      obtain ⟨e₂, hr⟩ := ih2 L1 L' hc _ _ _ _ _ _ hm b₁ b₂
      exact ⟨by rw [e₁, e₂], hr⟩
  | RLetZero x t body ih =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check] at hc
    cases h₁ with
    | letZero _ _ _ _ _ _ a₁ =>
    cases h₂ with
    | letZero _ _ _ _ _ _ a₂ =>
    exact ih _ _ hc _ _ _ _ _ _ (hR.setTower x false _ _ fun _ => rfl) a₁ a₂
  | RLetU64Zero x body ih =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check] at hc
    cases h₁ with
    | letU64Zero _ _ _ _ _ a₁ =>
    cases h₂ with
    | letU64Zero _ _ _ _ _ a₂ =>
    exact ih _ _ hc _ _ _ _ _ _ (hR.setScalar x false _ _ fun _ => rfl) a₁ a₂
  | RScalarSet x v =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check, Option.some.injEq] at hc; subst hc
    cases h₁; cases h₂
    exact ⟨rfl, hR.setScalar x false _ _ fun _ => rfl⟩
  | RCall f dest args =>
    intro L L' hc
    exact callOne_sound hc
  | RCallSwap f d1 d2 args =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check] at hc
    cases hc1 : callOne β M f d1 args L with
    | none => simp [hc1] at hc
    | some L1 =>
      simp only [hc1, Option.bind_some] at hc
      cases h₁ with
      | callSwap _ _ _ _ _ m₁ _ u₁ v₁ a₁ b₁ =>
      cases h₂ with
      | callSwap _ _ _ _ _ m₂ _ u₂ v₂ a₂ b₂ =>
      obtain ⟨e₁, hm⟩ := callOne_sound hc1 _ _ _ _ _ _ hR a₁ a₂
      obtain ⟨e₂, hr⟩ := callOne_sound hc _ _ _ _ _ _ hm b₁ b₂
      exact ⟨by rw [e₁, e₂], hr⟩
  | RCloneCall cv cty old f dest args =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check] at hc
    cases h₁ with
    | cloneCall _ _ _ _ _ _ _ c₁ _ _ hc₁ a₁ =>
    cases h₂ with
    | cloneCall _ _ _ _ _ _ _ c₂ _ _ hc₂ a₂ =>
    subst hc₁ hc₂
    refine callOne_sound hc _ _ _ _ _ _ ?_ a₁ a₂
    exact hR.setTower cv _ _ _ fun hb => by rw [(hR old.locVar).2 hb]
  | RIfNz e ct cf ih1 ih2 =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check] at hc
    split at hc
    · cases hc
    · rename_i he
      have he' : lk β L.sc e = false := by simpa using he
      have hg := (hR e).1 he'
      cases hA : check β M ct L with
      | none => simp [hA] at hc
      | some A =>
      cases hB : check β M cf L with
      | none => simp [hA, hB] at hc
      | some B =>
      simp only [hA, hB, Option.bind_some, Option.map_some, Option.some.injEq] at hc
      subst hc
      cases h₁ with
      | ifTrue _ _ _ _ _ v₁ _ hv₁ hv₁0 b₁ =>
        cases h₂ with
        | ifTrue _ _ _ _ _ v₂ _ hv₂ hv₂0 b₂ =>
          obtain ⟨e₁, hr⟩ := ih1 L A hA _ _ _ _ _ _ hR b₁ b₂
          exact ⟨by rw [e₁], hr.mono (Levels.le_join_left β A B)⟩
        | ifFalse _ _ _ _ _ _ hv₂ _ => exact absurd (hv₁ ▸ hg.trans hv₂) hv₁0
      | ifFalse _ _ _ _ _ _ hv₁ b₁ =>
        cases h₂ with
        | ifTrue _ _ _ _ _ v₂ _ hv₂ hv₂0 _ => exact absurd (hv₂ ▸ hg.symm.trans hv₁) hv₂0
        | ifFalse _ _ _ _ _ _ hv₂ b₂ =>
          obtain ⟨e₁, hr⟩ := ih2 L B hB _ _ _ _ _ _ hR b₁ b₂
          exact ⟨by rw [e₁], hr.mono (Levels.le_join_right β A B)⟩
  | RWhileNz e body ih =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check] at hc
    obtain ⟨hLI, O, hs, hOI⟩ := loopFix_spec _ _ _ hc
    split at hs
    · cases hs
    · rename_i he
      have he' : lk β L'.sc e = false := by simpa using he
      exact while_sound he' (ih _ _ hs) hOI h₁ rfl _ _ _ (hR.mono hLI) h₂
  | RFor x n body ih =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check] at hc
    obtain ⟨hLI, O, hs, hOI⟩ := loopFix_spec _ _ _ hc
    exact for_sound (ih _ _ hs) hOI n _ _ _ _ _ _ (hR.mono hLI) h₁ h₂
  | RLimbStore loc idx v =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check, Option.some.injEq] at hc; subst hc
    cases h₁ with
    | limbStore _ _ _ _ o₁ hl₁ =>
    cases h₂ with
    | limbStore _ _ _ _ o₂ hl₂ =>
    refine ⟨rfl, ?_⟩
    unfold locatedUpdate
    cases hs : lk β L.tw loc.locVar with
    | true => exact hR.setTower_secret hs _ _
    | false =>
      rw [lookup_eq hR hs, hl₂] at hl₁
      cases hl₁
      exact hR.setTower_eq _ _
  | RLimbStoreExpr loc idx e =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check] at hc
    split at hc
    · rename_i hok
      cases hc
      cases h₁ with
      | limbStoreExpr _ _ _ _ o₁ hl₁ =>
      cases h₂ with
      | limbStoreExpr _ _ _ _ o₂ hl₂ =>
      refine ⟨sexprLeak_eq hR e hok, ?_⟩
      unfold locatedUpdate
      refine hR.setTower _ _ _ _ fun hb => ?_
      simp only [Bool.or_eq_false_iff] at hb
      rw [lookup_eq hR hb.1, hl₂] at hl₁
      cases hl₁
      rw [sLvl_eval hR e hb.2]
    · cases hc
  | RCallN f dests args =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check] at hc
    split at hc
    · rename_i hvt
      cases hc
      cases h₁ with
      | callN _ _ _ _ al₁ ha₁ _ _ =>
      cases h₂ with
      | callN _ _ _ _ al₂ ha₂ _ _ =>
      subst ha₁ ha₂
      refine ⟨callLeak_eq hR hvt, ?_⟩
      cases hs : secArgs β L (dests ++ args) with
      | true =>
        have hle : Levels.Le β L (L.setManyTw dests true) := fun x =>
          ⟨id, fun h => by rw [lk_setManyTw]; split <;> simp [h]⟩
        exact callNUpdate_secret _ _ _ _ _ dests 0 _ _ (hR.mono hle)
          (fun d hd => by rw [lk_setManyTw, if_pos (List.mem_map_of_mem hd)])
      | false =>
        have hall := secArgs_false hs
        have hargs : secArgs β L args = false := by
          unfold secArgs at hs ⊢; rw [List.any_append, Bool.or_eq_false_iff] at hs; exact hs.2
        rw [argList_eq hR hargs]
        have hle : Levels.Le β L (L.setManyTw dests false) := fun x =>
          ⟨id, fun h => by
            rw [lk_setManyTw]; split
            · rename_i hx
              obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
              simp [hall d (List.mem_append_left _ hd)] at h
            · exact h⟩
        exact (callNUpdate_public _ _ _ _ dests 0 _ _ hR
          (fun d hd => hall d (List.mem_append_left _ hd))).mono hle
    · cases hc
  | RSelect dst sel s0 s1 =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check, Option.some.injEq] at hc; subst hc
    refine ⟨by cases h₁ <;> cases h₂ <;> rfl, ?_⟩
    cases h₁ with
    | selectFalse _ _ _ _ _ hh₁ sv₁ hsel₁ hl₁ =>
      cases h₂ with
      | selectFalse _ _ _ _ _ hh₂ sv₂ hsel₂ hl₂ =>
        unfold locatedUpdate
        refine hR.setTower _ _ _ _ fun hb => ?_
        simp only [Bool.or_eq_false_iff] at hb
        rw [lookup_eq hR hb.1.2, hl₂] at hl₁
        cases hl₁; rfl
      | selectTrue _ _ _ _ _ hh₂ v₂ sv₂ hsel₂ hv₂ hl₂ =>
        unfold locatedUpdate
        refine hR.setTower _ _ _ _ fun hb => ?_
        simp only [Bool.or_eq_false_iff] at hb
        exact absurd (hsel₂ ▸ ((hR sel).1 hb.1.1).symm.trans hsel₁) hv₂
    | selectTrue _ _ _ _ _ hh₁ v₁ sv₁ hsel₁ hv₁ hl₁ =>
      cases h₂ with
      | selectFalse _ _ _ _ _ hh₂ sv₂ hsel₂ hl₂ =>
        unfold locatedUpdate
        refine hR.setTower _ _ _ _ fun hb => ?_
        simp only [Bool.or_eq_false_iff] at hb
        exact absurd (hsel₁ ▸ ((hR sel).1 hb.1.1).trans hsel₂) hv₁
      | selectTrue _ _ _ _ _ hh₂ v₂ sv₂ hsel₂ hv₂ hl₂ =>
        unfold locatedUpdate
        refine hR.setTower _ _ _ _ fun hb => ?_
        simp only [Bool.or_eq_false_iff] at hb
        rw [lookup_eq hR hb.2, hl₂] at hl₁
        cases hl₁; rfl
  | RAssert label =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check, Option.some.injEq] at hc; subst hc
    cases h₁; cases h₂; exact ⟨rfl, hR⟩
  | RBlock body ih =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check] at hc
    cases h₁ with
    | block _ _ _ _ a₁ =>
    cases h₂ with
    | block _ _ _ _ a₂ =>
    exact ih _ _ hc _ _ _ _ _ _ hR a₁ a₂
  | RFnDef name params returns body cont _ _ =>
    intro L L' hc
    simp [check] at hc
  | RFnCall f dests args =>
    intro L L' hc
    simp [check] at hc
  | RTupleLoad dst src idx =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check, Option.some.injEq] at hc; subst hc
    cases h₁ with
    | tupleLoad _ _ _ _ o₁ s₁ ho₁ hs₁ =>
    cases h₂ with
    | tupleLoad _ _ _ _ o₂ s₂ ho₂ hs₂ =>
    refine ⟨rfl, ?_⟩
    unfold locatedUpdate
    refine hR.setTower _ _ _ _ fun hb => ?_
    simp only [Bool.or_eq_false_iff] at hb
    rw [lookup_eq hR hb.1, ho₂] at ho₁
    rw [lookup_eq hR hb.2, hs₂] at hs₁
    cases ho₁; cases hs₁; rfl
  | RArrStore arr i src =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check] at hc
    split at hc
    · cases hc
    · rename_i hi
      have hi' : lk β L.sc i = false := by simpa using hi
      cases hc
      cases h₁ with
      | arrStore _ _ _ _ x₁ o₁ s₁ hx₁ ho₁ hs₁ =>
      cases h₂ with
      | arrStore _ _ _ _ x₂ o₂ s₂ hx₂ ho₂ hs₂ =>
      have hx : x₁ = x₂ := hx₁ ▸ hx₂ ▸ (hR i).1 hi'
      subst hx
      refine ⟨rfl, ?_⟩
      unfold locatedUpdate
      refine hR.setTower _ _ _ _ fun hb => ?_
      simp only [Bool.or_eq_false_iff] at hb
      rw [lookup_eq hR hb.1, ho₂] at ho₁
      rw [lookup_eq hR hb.2, hs₂] at hs₁
      cases ho₁; cases hs₁; rfl
  | RArrLoad dst src i =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check] at hc
    split at hc
    · cases hc
    · rename_i hi
      have hi' : lk β L.sc i = false := by simpa using hi
      cases hc
      cases h₁ with
      | arrLoad _ _ _ _ x₁ o₁ s₁ hx₁ ho₁ hs₁ =>
      cases h₂ with
      | arrLoad _ _ _ _ x₂ o₂ s₂ hx₂ ho₂ hs₂ =>
      have hx : x₁ = x₂ := hx₁ ▸ hx₂ ▸ (hR i).1 hi'
      subst hx
      refine ⟨rfl, ?_⟩
      unfold locatedUpdate
      refine hR.setTower _ _ _ _ fun hb => ?_
      simp only [Bool.or_eq_false_iff] at hb
      rw [lookup_eq hR hb.1, ho₂] at ho₁
      rw [lookup_eq hR hb.2, hs₂] at hs₁
      cases ho₁; cases hs₁; rfl
  | RArrStoreLit arr idx src =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check, Option.some.injEq] at hc; subst hc
    cases h₁ with
    | arrStoreLit _ _ _ _ o₁ s₁ ho₁ hs₁ =>
    cases h₂ with
    | arrStoreLit _ _ _ _ o₂ s₂ ho₂ hs₂ =>
    refine ⟨rfl, ?_⟩
    unfold locatedUpdate
    refine hR.setTower _ _ _ _ fun hb => ?_
    simp only [Bool.or_eq_false_iff] at hb
    rw [lookup_eq hR hb.1, ho₂] at ho₁
    rw [lookup_eq hR hb.2, hs₂] at hs₁
    cases ho₁; cases hs₁; rfl
  | RArrLoadLit dst src idx =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check, Option.some.injEq] at hc; subst hc
    cases h₁ with
    | arrLoadLit _ _ _ _ o₁ s₁ ho₁ hs₁ =>
    cases h₂ with
    | arrLoadLit _ _ _ _ o₂ s₂ ho₂ hs₂ =>
    refine ⟨rfl, ?_⟩
    unfold locatedUpdate
    refine hR.setTower _ _ _ _ fun hb => ?_
    simp only [Bool.or_eq_false_iff] at hb
    rw [lookup_eq hR hb.1, ho₂] at ho₁
    rw [lookup_eq hR hb.2, hs₂] at hs₁
    cases ho₁; cases hs₁; rfl
  | RScalarSetExpr x e =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check] at hc
    split at hc
    · rename_i hok
      cases hc
      cases h₁; cases h₂
      exact ⟨sexprLeak_eq hR e hok, hR.setScalar x _ _ _ (sLvl_eval hR e)⟩
    · cases hc
  | RCallDstThreaded f dst args =>
    intro L L' hc
    exact callDst_sound hc
  | RForRuntime x bound body ih =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check] at hc
    split at hc
    · cases hc
    · rename_i hb
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_true] at hb
      obtain ⟨hLI, O, hs, hOI⟩ := loopFix_spec _ _ _ hc
      cases h₁ with
      | forRuntime _ _ _ _ _ u₁ a₁ =>
      cases h₂ with
      | forRuntime _ _ _ _ _ u₂ a₂ =>
      have hn := sLvl_eval hR bound hb.1
      rw [hn] at a₁
      obtain ⟨e₁, hr⟩ := for_sound (ih _ _ hs) hOI _ _ _ _ _ _ _ (hR.mono hLI) a₁ a₂
      exact ⟨by rw [sexprLeak_eq hR bound (by simpa using hb.2), hn, e₁], hr⟩
  | RCopy dst src =>
    intro L L' hc rs₁ rs₂ t₁ t₂ r₁ r₂ hR h₁ h₂
    simp only [check, Option.some.injEq] at hc; subst hc
    cases h₁ with
    | copy _ _ _ hh₁ s₁ hs₁ =>
    cases h₂ with
    | copy _ _ _ hh₂ s₂ hs₂ =>
    refine ⟨rfl, ?_⟩
    unfold locatedUpdate
    refine hR.setTower _ _ _ _ fun hb => ?_
    rw [lookup_eq hR hb, hs₂] at hs₁
    cases hs₁; rfl

end LevelCheck

open LevelCheck

/-! ## 9. The checker on `LevelTable` splits -/

/-- The base split of a level table: `true` at the secret names. -/
def secretBase (lt : LevelTable) (x : String) : Bool :=
  match lt x with
  | .Secret => true
  | .Public => false

/-- A split of the two heaps as one level table: a name is secret when its
    scalar slot or its tower slot is. -/
def LevelCheck.Levels.toTable (β : String → Bool) (L : Levels) : LevelTable :=
  fun x => if lk β L.sc x || lk β L.tw x then .Secret else .Public

/-- The flow-sensitive level checker: the split at the exit of `c` from the
    entry split `lt`, or `none` when `c` is rejected. -/
def levelCheck (M : LowCTLeakModel) (lt : LevelTable) (c : LowCT) : Option LevelTable :=
  (check (secretBase lt) M c {}).map (Levels.toTable (secretBase lt))

theorem rel_of_pubEqRS {lt : LevelTable} {rs₁ rs₂ : RustState} (h : PubEqRS lt rs₁ rs₂) :
    Rel (secretBase lt) {} rs₁ rs₂ := by
  intro x
  have hx : lk (secretBase lt) [] x = false → lt x = .Public := by
    simp only [lk, secretBase]
    cases lt x <;> simp
  exact ⟨fun h' => (h x (hx h')).1, fun h' => (h x (hx h')).2⟩

theorem pubEqRS_of_rel {β : String → Bool} {L : Levels} {rs₁ rs₂ : RustState}
    (h : Rel β L rs₁ rs₂) : PubEqRS (L.toTable β) rs₁ rs₂ := by
  intro x hx
  simp only [Levels.toTable] at hx
  split at hx
  · cases hx
  · rename_i hs
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hs
    exact ⟨(h x).1 hs.1, (h x).2 hs.2⟩

/-- **Soundness of `levelCheck`.** A program accepted from the split `lt` is
    constant time for `lt` in the `RustExecLeak` model `M`, and two runs from
    states agreeing on the public slots of `lt` end in states agreeing on the
    public slots of the returned split. No hypothesis on the program, its
    selects or its leaves. -/
theorem levelCheck_sound {N : Nat} {leafSpec : LeafSpec} {M : LowCTLeakModel}
    {lt lt' : LevelTable} {c : LowCT} (h : levelCheck M lt c = some lt') :
    LowCTConstantTime N leafSpec M lt c ∧
      ∀ rs₁ rs₂ t₁ t₂ r₁ r₂, PubEqRS lt rs₁ rs₂ →
        RustExecLeak N leafSpec M c rs₁ t₁ r₁ → RustExecLeak N leafSpec M c rs₂ t₂ r₂ →
        PubEqRS lt' r₁ r₂ := by
  unfold levelCheck at h
  cases hc : check (secretBase lt) M c {} with
  | none => simp [hc] at h
  | some L' =>
    simp only [hc, Option.map_some, Option.some.injEq] at h
    subst h
    have hs := check_sound (N := N) (leafSpec := leafSpec) c _ _ hc
    refine ⟨fun rs₁ rs₂ t₁ t₂ hp ⟨_, h₁⟩ ⟨_, h₂⟩ => (hs _ _ _ _ _ _ (rel_of_pubEqRS hp) h₁ h₂).1,
      fun rs₁ rs₂ t₁ t₂ r₁ r₂ hp h₁ h₂ =>
        pubEqRS_of_rel (hs _ _ _ _ _ _ (rel_of_pubEqRS hp) h₁ h₂).2⟩

/-! ## 10. Acceptance and rejection -/

/-- The three `LowCTLeakage` counterexamples are rejected: a secret guard, an
    arithmetic shift by a secret count (a `SARX`), and a secret runtime loop
    bound. -/
theorem levelCheck_rejects_secretGuard :
    levelCheck .owned kSecret (.RIfNz "k" .RSkip .RSkip) = none := by decide

theorem levelCheck_rejects_secretSarx :
    levelCheck .owned kSecret (.RScalarSetExpr "y" (.SAsr (.SVar "a") (.SVar "k"))) = none := by
  decide

theorem levelCheck_rejects_secretBound :
    levelCheck .owned kSecret (.RForRuntime "i" (.SVar "k") .RSkip) = none := by decide

/-- A secret array index is rejected, for every leakage model. -/
theorem levelCheck_rejects_secretIndex (M : LowCTLeakModel) (dst src : Located) :
    levelCheck M kSecret (.RArrLoad dst src "k") = none := by
  simp [levelCheck, check, lk, secretBase, kSecret]

/-- A secret-data loop with a literal trip count: `acc := acc ^ k` four times.
    Accepted, and `acc` is secret at exit. -/
def secretXorLoop : LowCT :=
  .RFor "i" 4 (.RScalarSetExpr "acc" (.SXor (.SVar "acc") (.SVar "k")))

theorem levelCheck_accepts_secretXorLoop :
    (levelCheck .owned kSecret secretXorLoop).map (· "acc") = some .Secret := by decide

/-- The same loop with a public runtime trip count `n`. -/
def secretXorLoopRt : LowCT :=
  .RForRuntime "i" (.SVar "n") (.RScalarSetExpr "acc" (.SXor (.SVar "acc") (.SVar "k")))

theorem levelCheck_accepts_secretXorLoopRt :
    (levelCheck .owned kSecret secretXorLoopRt).map (· "acc") = some .Secret := by decide

/-- A cmov-based select on the secret bit `k`, followed by a store of the
    result at the public index `j`: accepted, and the destination and the array
    are secret at exit. -/
def secretSelect : LowCT :=
  .RSeq (.RSelect ⟨"r", .TU64⟩ "k" ⟨"a", .TU64⟩ ⟨"b", .TU64⟩)
    (.RArrStore ⟨"out", .TArr 4 .TU64⟩ "j" ⟨"r", .TU64⟩)

theorem levelCheck_accepts_secretSelect :
    (levelCheck .owned kSecret secretSelect).map (fun lt => (lt "r", lt "out")) =
      some (.Secret, .Secret) := by decide

/-- A scalar computed from the secret `k` and then used as an array index is
    rejected: the level of `k` reaches `r` through the arithmetic. -/
theorem levelCheck_rejects_derivedIndex :
    levelCheck .owned kSecret
      (.RSeq (.RScalarSetExpr "r" (.SAnd (.SVar "k") (.SLit 1)))
        (.RArrLoad ⟨"d", .TU64⟩ ⟨"t", .TArr 4 .TU64⟩ "r")) = none := by decide

/-- A copy from a public tower slot onto the tower slot `s`, secret at entry,
    makes the tower slot `s` public. -/
theorem check_copy_overwrites_level :
    (check (secretBase fun x => if x = "s" then .Secret else .Public) .owned
      (.RCopy ⟨"s", .TU64⟩ ⟨"p", .TU64⟩) {}).map
        (fun L => lk (secretBase fun x => if x = "s" then .Secret else .Public) L.tw "s") =
      some false := by decide

/-- A `while` loop on the public counter `n` whose body mixes the secret `k`
    into `acc` is accepted; a `while` loop whose guard becomes secret after one
    iteration is rejected by the fixpoint. -/
theorem levelCheck_accepts_publicWhile :
    (levelCheck .owned kSecret
      (.RWhileNz "n" (.RSeq (.RScalarSetExpr "acc" (.SAdd (.SVar "acc") (.SVar "k")))
        (.RScalarSetExpr "n" (.SSub (.SVar "n") (.SLit 1)))))).map (· "acc") =
      some .Secret := by decide

theorem levelCheck_rejects_taintedWhileGuard :
    levelCheck .owned kSecret
      (.RWhileNz "n" (.RScalarSetExpr "n" (.SXor (.SVar "n") (.SVar "k")))) = none := by decide

end CatCrypt.Crypto.SecureCompilation.CT
