/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ProgramLit

/-!
# Program-level simulation with array loads and stores

`haxToLowCT` lowers `let name = index(arr, idx); body` to an `RArrLoad` of the
slot `arr` and `let name = array_update(arr, idx, src); body` to an `RArrStore`
into the slot `arr`, with the located types of the array and the stored value
left as `.TFp` and `.TBytes 0`.

`arrTower A` is a pass over the lowered program that gives these commands the
located types of an array table `A : TowerScope`: an array name `arr` recorded in
`A` at type `t` is located at `t`, and the value stored into it at
`t.elemType`.  Commands naming an array absent from `A`, and all other commands,
are unchanged.  `haxToLowCTA A e` is the lowering followed by the pass.

* `simScopeA tow S T A Γ e` is the scope checker of `simScopeL` with the tower
  type of a call named `f` given by `tow f`, in which `index(arr, idx)` and
  `array_update(arr, idx, src)` require `arr` to be recorded in `A` and in the
  scope at the same type `t`, the index `idx` to be a scalar name of `S`, and the
  stored value `src` to be in scope at `t.elemType`; an `array_update` must
  rebind its array name.  An `assign` of `index` or `array_update` is rejected.
* `IndexAgrees` and `ArrUpdateAgrees` are the leaf conditions for the array load
  and the array store.
* `ProgSimA` is the simulation predicate for `arrTower A (litTower T c)`.

## Main results

* `haxToLowCT_simulates_programA` — every program simulates under
  `envAgreesRustT`, from the leaf condition at every call name other than
  `index` and `array_update`, `TupleLoadAgrees`, `LitStoreAgrees`, `IndexAgrees`
  and `ArrUpdateAgrees`; no hypothesis requires the builtin table to leave
  `index` or `array_update` undefined.
* `arrTower_nil`, `haxToLowCTA_nil` — with the empty array table the pass is the
  identity and `haxToLowCTA [] = haxToLowCT`.
* `arrTower_of_arrFree`, `haxToLowCTA_of_arrFree` — on a program whose lowering
  has no array load or store the pass is the identity and `haxToLowCTA A` agrees
  with `haxToLowCT`.
* `simScopeA_lookup_mono` — the exit scope of the checker extends its entry
  scope.
* `LimbReadAgrees`, `limbRead_exec`, `limbRead_sim` — the limb read
  `let x = index(v, i)` at a literal `i`: the condition on the builtin table, the
  `RustExec` step of `RScalarSetExpr x (SLimb v i)`, and the simulation of the
  binding from a simulation of its body.  `simScopeA` rejects the binding.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit Value Env Builtins)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located RustVal
   rsSetTower rsSetScalar locatedUpdate locatedLookup)

/-! ## §1  The typing pass -/

/-- The located types of array loads and stores from the array table `A`. -/
def arrTower (A : TowerScope) : LowCT → LowCT
  | .RSeq a b => .RSeq (arrTower A a) (arrTower A b)
  | .RLetZero x t b => .RLetZero x t (arrTower A b)
  | .RLetU64Zero x b => .RLetU64Zero x (arrTower A b)
  | .RIfNz v t e => .RIfNz v (arrTower A t) (arrTower A e)
  | .RWhileNz v b => .RWhileNz v (arrTower A b)
  | .RFor x n b => .RFor x n (arrTower A b)
  | .RForRuntime x bound b => .RForRuntime x bound (arrTower A b)
  | .RArrStore arr idx src =>
      match List.lookup arr.locVar A with
      | some t => .RArrStore { locVar := arr.locVar, locSrc := t } idx
          { locVar := src.locVar, locSrc := t.elemType }
      | none => .RArrStore arr idx src
  | .RArrLoad dst src idx =>
      match List.lookup src.locVar A with
      | some t => .RArrLoad dst { locVar := src.locVar, locSrc := t } idx
      | none => .RArrLoad dst src idx
  | c => c

/-- The lowering of `haxToLowCT` with the array loads and stores typed by `A`. -/
def haxToLowCTA (A : TowerScope) (e : ImpExpr) : Option LowCT :=
  (haxToLowCT e).map (arrTower A)

/-- The program contains no array load or store. -/
def arrFree : LowCT → Bool
  | .RSeq a b => arrFree a && arrFree b
  | .RLetZero _ _ b => arrFree b
  | .RLetU64Zero _ b => arrFree b
  | .RIfNz _ t e => arrFree t && arrFree e
  | .RWhileNz _ b => arrFree b
  | .RFor _ _ b => arrFree b
  | .RForRuntime _ _ b => arrFree b
  | .RArrStore _ _ _ => false
  | .RArrLoad _ _ _ => false
  | _ => true

theorem arrTower_seq (A : TowerScope) (a b : LowCT) :
    arrTower A (.RSeq a b) = .RSeq (arrTower A a) (arrTower A b) := by
  simp [arrTower]

theorem arrTower_letZero (A : TowerScope) (x : String) (t : TowerType) (b : LowCT) :
    arrTower A (.RLetZero x t b) = .RLetZero x t (arrTower A b) := by
  simp [arrTower]

theorem arrTower_letU64Zero (A : TowerScope) (x : String) (b : LowCT) :
    arrTower A (.RLetU64Zero x b) = .RLetU64Zero x (arrTower A b) := by
  simp [arrTower]

theorem arrTower_ifNz (A : TowerScope) (v : String) (t e : LowCT) :
    arrTower A (.RIfNz v t e) = .RIfNz v (arrTower A t) (arrTower A e) := by
  simp [arrTower]

theorem arrTower_whileNz (A : TowerScope) (v : String) (b : LowCT) :
    arrTower A (.RWhileNz v b) = .RWhileNz v (arrTower A b) := by
  simp [arrTower]

theorem arrTower_for (A : TowerScope) (x : String) (n : Nat) (b : LowCT) :
    arrTower A (.RFor x n b) = .RFor x n (arrTower A b) := by
  simp [arrTower]

theorem arrTower_forRuntime (A : TowerScope) (x : String)
    (bound : CatCrypt.Crypto.Jasmin.LowCT.SExpr) (b : LowCT) :
    arrTower A (.RForRuntime x bound b) = .RForRuntime x bound (arrTower A b) := by
  simp [arrTower]

theorem arrTower_arrStore (A : TowerScope) (arr src : Located) (idx : String) (t : TowerType)
    (h : List.lookup arr.locVar A = some t) :
    arrTower A (.RArrStore arr idx src) =
      .RArrStore { locVar := arr.locVar, locSrc := t } idx
        { locVar := src.locVar, locSrc := t.elemType } := by
  simp [arrTower, h]

theorem arrTower_arrLoad (A : TowerScope) (dst src : Located) (idx : String) (t : TowerType)
    (h : List.lookup src.locVar A = some t) :
    arrTower A (.RArrLoad dst src idx) = .RArrLoad dst { locVar := src.locVar, locSrc := t } idx := by
  simp [arrTower, h]

/-- On a program without array loads and stores, `arrTower` is the identity. -/
theorem arrTower_of_arrFree (A : TowerScope) (c : LowCT) (h : arrFree c = true) :
    arrTower A c = c := by
  induction c with
  | RSeq a b iha ihb =>
    simp only [arrFree, Bool.and_eq_true] at h
    rw [arrTower_seq, iha h.1, ihb h.2]
  | RLetZero x t b ih => rw [arrTower_letZero, ih h]
  | RLetU64Zero x b ih => rw [arrTower_letU64Zero, ih h]
  | RIfNz v t e iht ihe =>
    simp only [arrFree, Bool.and_eq_true] at h
    rw [arrTower_ifNz, iht h.1, ihe h.2]
  | RWhileNz v b ih => rw [arrTower_whileNz, ih h]
  | RFor x n b ih => rw [arrTower_for, ih h]
  | RForRuntime x bound b ih => rw [arrTower_forRuntime, ih h]
  | RArrStore => simp [arrFree] at h
  | RArrLoad => simp [arrFree] at h
  | _ => simp [arrTower]

/-- With the empty array table, `arrTower` is the identity. -/
theorem arrTower_nil (c : LowCT) : arrTower [] c = c := by
  induction c with
  | RSeq a b iha ihb => rw [arrTower_seq, iha, ihb]
  | RLetZero x t b ih => rw [arrTower_letZero, ih]
  | RLetU64Zero x b ih => rw [arrTower_letU64Zero, ih]
  | RIfNz v t e iht ihe => rw [arrTower_ifNz, iht, ihe]
  | RWhileNz v b ih => rw [arrTower_whileNz, ih]
  | RFor x n b ih => rw [arrTower_for, ih]
  | RForRuntime x bound b ih => rw [arrTower_forRuntime, ih]
  | _ => simp [arrTower]

/-- With the empty array table, `haxToLowCTA` is `haxToLowCT`. -/
theorem haxToLowCTA_nil (e : ImpExpr) : haxToLowCTA [] e = haxToLowCT e := by
  unfold haxToLowCTA
  cases haxToLowCT e <;> simp [arrTower_nil]

/-- On a program whose lowering has no array load or store, `haxToLowCTA A` is
    `haxToLowCT`. -/
theorem haxToLowCTA_of_arrFree (A : TowerScope) (e : ImpExpr) (c : LowCT)
    (hc : haxToLowCT e = some c) (h : arrFree c = true) : haxToLowCTA A e = haxToLowCT e := by
  simp [haxToLowCTA, hc, arrTower_of_arrFree A c h]

theorem arrTower_limbStore (A : TowerScope) (loc : Located) (i : Nat) (w : BitVec 64) :
    arrTower A (.RLimbStore loc i w) = .RLimbStore loc i w := by
  simp [arrTower]

theorem arrTower_letBind_copy (A : TowerScope) (x src : String) (b : LowCT) :
    arrTower A (.RLetU64Zero x (.RSeq (.RScalarSetExpr x (.SVar src)) b)) =
      .RLetU64Zero x (.RSeq (.RScalarSetExpr x (.SVar src)) (arrTower A b)) := by
  simp [arrTower]

theorem arrTower_scalarSet (A : TowerScope) (x : String) (m : Nat) :
    arrTower A (.RScalarSet x m) = .RScalarSet x m := by
  simp [arrTower]

theorem arrTower_call (A : TowerScope) (f : String) (dest : Located) (args : List Located) :
    arrTower A (.RCall f dest args) = .RCall f dest args := by
  simp [arrTower]

theorem arrTower_tupleLoad (A : TowerScope) (dst src : Located) (i : Nat) :
    arrTower A (.RTupleLoad dst src i) = .RTupleLoad dst src i := by
  simp [arrTower]

theorem litTower_arrStore (T : List String) (arr src : Located) (idx : String) :
    litTower T (.RArrStore arr idx src) = .RArrStore arr idx src := by
  simp [litTower]

theorem litTower_arrLoad (T : List String) (dst src : Located) (idx : String) :
    litTower T (.RArrLoad dst src idx) = .RArrLoad dst src idx := by
  simp [litTower]

theorem litTower_call (T : List String) (f : String) (dest : Located) (args : List Located) :
    litTower T (.RCall f dest args) = .RCall f dest args := by
  simp [litTower]

theorem litTower_tupleLoad (T : List String) (dst src : Located) (i : Nat) :
    litTower T (.RTupleLoad dst src i) = .RTupleLoad dst src i := by
  simp [litTower]

/-- The names of an argument list of three variables. -/
def varArgs3 : List ImpExpr → Option (String × String × String)
  | [.var a, .var b, .var c] => some (a, b, c)
  | _ => none

/-- The names of an argument list of two variables. -/
def varArgs2 : List ImpExpr → Option (String × String)
  | [.var a, .var b] => some (a, b)
  | _ => none

theorem varArgs3_some {args : List ImpExpr} {a b c : String}
    (h : varArgs3 args = some (a, b, c)) : args = [.var a, .var b, .var c] := by
  unfold varArgs3 at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · cases h

theorem varArgs2_some {args : List ImpExpr} {a b : String}
    (h : varArgs2 args = some (a, b)) : args = [.var a, .var b] := by
  unfold varArgs2 at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  · cases h

/-! ## §2  The checker -/

/-- The scope checker of `simScopeL` with the tower type of a call named `f`
    given by `tow f`, and array loads and stores typed by the array table `A`. -/
def simScopeA (tow : String → TowerType) (S T : List String) (A Γ : TowerScope) :
    ImpExpr → Option TowerScope
  | .letBind name (.app f args) body =>
      if f = "array_update" then
        match args with
        | [.var arr, .var idx, .var src] =>
            match List.lookup arr A with
            | some t =>
                if decide (name = arr) && decide (List.lookup arr Γ = some t)
                    && decide (List.lookup src Γ = some t.elemType) && S.contains idx then
                  simScopeA tow S T A Γ body
                else none
            | none => none
        | _ => none
      else if f = "index" then
        match args with
        | [.var arr, .var idx] =>
            match List.lookup arr A with
            | some t =>
                if decide (List.lookup arr Γ = some t) && decide (arr ≠ name) && S.contains idx
                    && scopeCompat Γ name .TFp && !S.contains name then
                  simScopeA tow S T A ((name, .TFp) :: Γ) body
                else none
            | none => none
        | _ => none
      else
        let dt := tow f
        if !scalarCallName f && argsInScope Γ dt args && argsAvoid name args
            && scopeCompat Γ name dt && !S.contains name then
          simScopeA tow S T A ((name, dt) :: Γ) body
        else none
  | .letBind name (.lit l) body =>
      if T.contains name then
        if litWord l && scopeCompat Γ name .TFp && !S.contains name then
          simScopeA tow S T A ((name, .TFp) :: Γ) body
        else none
      else if S.contains name then simScopeA tow S T A Γ body else none
  | .letBind name (.var src) body =>
      if decide (name = src) || (S.contains name && S.contains src) then
        simScopeA tow S T A Γ body
      else none
  | .letBind name (.proj (.var t) _) body =>
      if decide (List.lookup t Γ = some .TFp) && decide (t ≠ name)
          && scopeCompat Γ name .TFp && !S.contains name then
        simScopeA tow S T A ((name, .TFp) :: Γ) body
      else none
  | .var _ => some Γ
  | .unitVal => some Γ
  | .seq a b =>
      match simScopeA tow S T A Γ a with
      | some Γ₁ => simScopeA tow S T A Γ₁ b
      | none => none
  | .ifThenElse (.var _) t e =>
      match simScopeA tow S T A Γ t, simScopeA tow S T A Γ e with
      | some _, some _ => some Γ
      | _, _ => none
  | .whileLoop (.var _) body =>
      match simScopeA tow S T A Γ body with
      | some _ => some Γ
      | none => none
  | .assign name (.lit _) => if S.contains name then some Γ else none
  | .assign name (.app f args) =>
      if f = "array_update" ∨ f = "index" then none
      else
        let dt := tow f
        if argsInScope Γ dt args && decide (List.lookup name Γ = some dt)
            && !S.contains name then some Γ else none
  | .tuple es => if es.all isVar then some Γ else none
  | .typeAscription e _ => simScopeA tow S T A Γ e
  | _ => none

/-- The exit scope of `simScopeA` extends the entry scope. -/
theorem simScopeA_lookup_mono (tow : String → TowerType) (S T : List String) (A : TowerScope)
    (e : ImpExpr) :
    ∀ (Γ Γ' : TowerScope), simScopeA tow S T A Γ e = some Γ' →
      ∀ m dt, List.lookup m Γ = some dt → List.lookup m Γ' = some dt := by
  induction e using ImpExpr.ind with
  | letBind name val body _ ihBody =>
    intro Γ Γ' h m dt hm
    cases val with
    | app f args =>
      simp only [simScopeA] at h
      split at h
      · split at h
        · split at h
          · split at h
            · exact ihBody Γ Γ' h m dt hm
            · cases h
          · cases h
        · cases h
      · split at h
        · split at h
          · split at h
            · split at h
              · rename_i hc
                simp only [Bool.and_eq_true] at hc
                exact ihBody _ Γ' h m dt
                  (lookup_cons_of_scopeCompat Γ name .TFp hc.1.2 m dt hm)
              · cases h
            · cases h
          · cases h
        · split at h
          · rename_i hc
            simp only [Bool.and_eq_true] at hc
            exact ihBody _ Γ' h m dt
              (lookup_cons_of_scopeCompat Γ name (tow f) hc.1.2 m dt hm)
          · cases h
    | lit l =>
      simp only [simScopeA] at h
      split at h
      · split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          exact ihBody _ Γ' h m dt
            (lookup_cons_of_scopeCompat Γ name .TFp hc.1.2 m dt hm)
        · cases h
      · split at h
        · exact ihBody Γ Γ' h m dt hm
        · cases h
    | var src =>
      simp only [simScopeA] at h
      split at h
      · exact ihBody Γ Γ' h m dt hm
      · cases h
    | proj pe i =>
      cases pe with
      | var t =>
        simp only [simScopeA] at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          exact ihBody _ Γ' h m dt
            (lookup_cons_of_scopeCompat Γ name .TFp hc.1.2 m dt hm)
        · cases h
      | _ => simp [simScopeA] at h
    | _ => simp [simScopeA] at h
  | var _ => intro Γ Γ' h m dt hm; simp only [simScopeA, Option.some.injEq] at h; subst h; exact hm
  | unitVal => intro Γ Γ' h m dt hm; simp only [simScopeA, Option.some.injEq] at h; subst h; exact hm
  | seq a b iha ihb =>
    intro Γ Γ' h m dt hm
    simp only [simScopeA] at h
    rcases hA : simScopeA tow S T A Γ a with _ | Γ₁
    · rw [hA] at h; cases h
    · rw [hA] at h
      exact ihb Γ₁ Γ' h m dt (iha Γ Γ₁ hA m dt hm)
  | ifThenElse c t e _ _ _ =>
    intro Γ Γ' h m dt hm
    cases c with
    | var _ =>
      simp only [simScopeA] at h
      split at h
      · rw [Option.some.injEq] at h; subst h; exact hm
      · cases h
    | _ => simp [simScopeA] at h
  | whileLoop c body _ _ =>
    intro Γ Γ' h m dt hm
    cases c with
    | var _ =>
      simp only [simScopeA] at h
      split at h
      · rw [Option.some.injEq] at h; subst h; exact hm
      · cases h
    | _ => simp [simScopeA] at h
  | assign name rhs _ =>
    intro Γ Γ' h m dt hm
    cases rhs with
    | lit _ =>
      simp only [simScopeA] at h
      split at h
      · rw [Option.some.injEq] at h; subst h; exact hm
      · cases h
    | app f args =>
      simp only [simScopeA] at h
      split at h
      · cases h
      · split at h
        · rw [Option.some.injEq] at h; subst h; exact hm
        · cases h
    | _ => simp [simScopeA] at h
  | tuple es _ =>
    intro Γ Γ' h m dt hm
    simp only [simScopeA] at h
    split at h
    · rw [Option.some.injEq] at h; subst h; exact hm
    · cases h
  | typeAscription e _ ih =>
    intro Γ Γ' h
    simp only [simScopeA] at h
    exact ih Γ Γ' h
  | _ => intro Γ Γ' h; simp [simScopeA] at h

/-! ## §3  Lowering of array loads and stores -/

theorem haxToLowCT_letBind_index_some (name f arr idx : String) (body : ImpExpr) (c : LowCT)
    (hArr : f ≠ "array_update") (hIdx : f = "index")
    (h : haxToLowCT (.letBind name (.app f [.var arr, .var idx]) body) = some c) :
    ∃ bodyC, haxToLowCT body = some bodyC ∧
      c = .RLetZero name .TFp
        (.RSeq (.RArrLoad { locVar := name, locSrc := .TFp } { locVar := arr, locSrc := .TFp } idx)
          bodyC) := by
  simp only [haxToLowCT, haxArgsToLocated, haxArgToLocated] at h
  cases hBody : haxToLowCT body with
  | none => simp [hBody] at h
  | some bodyC =>
    simp only [hBody, if_neg hArr, if_pos hIdx, Option.some.injEq] at h
    exact ⟨bodyC, rfl, h.symm⟩

theorem haxToLowCT_letBind_arrUpdate_some (name f arr idx src : String) (body : ImpExpr)
    (c : LowCT) (hArr : f = "array_update")
    (h : haxToLowCT (.letBind name (.app f [.var arr, .var idx, .var src]) body) = some c) :
    ∃ bodyC, haxToLowCT body = some bodyC ∧
      c = .RSeq (.RArrStore { locVar := arr, locSrc := .TBytes 0 } idx
        { locVar := src, locSrc := .TBytes 0 }) bodyC := by
  simp only [haxToLowCT, haxArgsToLocated, haxArgToLocated] at h
  cases hBody : haxToLowCT body with
  | none => simp [hBody] at h
  | some bodyC =>
    simp only [hBody, if_pos hArr, Option.some.injEq] at h
    exact ⟨bodyC, rfl, h.symm⟩

/-- The lowering of `arr = array_update(arr, idx, src)` on three variables is the
    array store `RArrStore arr idx src`. -/
theorem haxToLowCT_assign_arrUpdate_some (name f arr idx src : String) (c : LowCT)
    (hArr : f = "array_update")
    (h : haxToLowCT (.assign name (.app f [.var arr, .var idx, .var src])) = some c) :
    c = .RArrStore { locVar := arr, locSrc := .TBytes 0 } idx
      { locVar := src, locSrc := .TBytes 0 } := by
  simp only [haxToLowCT, haxArgsToLocated, haxArgToLocated, if_pos hArr, Option.some.injEq] at h
  exact h.symm

/-! ## §4  The simulation predicate -/

/-- The array load agrees with the builtin `index`: for an array value related by
    `bridge` to a slot of type `t` and an index value whose scalar decoding, when
    it has one, is `k`, the builtin's result is related at `.TFp` to the load of
    element `k` into a zero slot. -/
def IndexAgrees (bridge : ValueTowerBridge) (bi : Builtins) (leafSpec : LeafSpec) : Prop :=
  ∀ (name : String) (t : TowerType) (vArr vIdx vRes : Value) (arrV : RustVal t) (k : Nat),
    bridge t vArr arrV → (∀ n, valueToScalar vIdx = some n → n = k) →
    bi "index" [vArr, vIdx] = some vRes →
    bridge .TFp vRes (leafSpec.arrLoad { locVar := name, locSrc := .TFp } default ⟨t, arrV⟩ k)

/-- The array store agrees with the builtin `array_update`: for an array value
    related by `bridge` to a slot of type `t`, an index value whose scalar
    decoding, when it has one, is `k`, and a value related to a slot of type
    `t.elemType`, the builtin's result is related at `t` to the store of that slot
    at element `k`. -/
def ArrUpdateAgrees (bridge : ValueTowerBridge) (bi : Builtins) (leafSpec : LeafSpec) : Prop :=
  ∀ (arr : String) (t : TowerType) (vArr vIdx vSrc vRes : Value) (arrV : RustVal t)
    (srcV : RustVal t.elemType) (k : Nat),
    bridge t vArr arrV → (∀ n, valueToScalar vIdx = some n → n = k) →
    bridge t.elemType vSrc srcV →
    bi "array_update" [vArr, vIdx, vSrc] = some vRes →
    bridge t vRes (leafSpec.arrStore { locVar := arr, locSrc := t } arrV k ⟨t.elemType, srcV⟩)

/-- Simulation of `e` by `arrTower A (litTower T c)` for its lowering `c`, under
    the side conditions of `simScopeA towerOfCallName`. -/
def ProgSimA (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (S T : List String) (A : TowerScope) (e : ImpExpr) : Prop :=
  ∀ (fuel : Nat) (Γ Γ' : TowerScope) (c : LowCT) (env env' : Env) (rs : RustState) (v : Value),
    simScopeA towerOfCallName S T A Γ e = some Γ' → condsScalar S e = true →
    ScopeBound rs Γ → NamesFresh rs S →
    haxToLowCT e = some c →
    evalImp bi fuel e env = some (v, env') →
    envAgreesRustT bridge env rs →
    ∃ rs', RustExec N leafSpec (arrTower A (litTower T c)) rs rs' ∧
      envAgreesRustT bridge env' rs' ∧ ScopeBound rs' Γ' ∧ NamesFresh rs' S

section ArmsA

variable (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
  (S T : List String) (A : TowerScope)

theorem progSimA_of_simScopeA_none (e : ImpExpr)
    (h : ∀ Γ, simScopeA towerOfCallName S T A Γ e = none) :
    ProgSimA bridge bi N leafSpec S T A e := by
  intro fuel Γ Γ' c env env' rs v hScope
  rw [h Γ] at hScope
  cases hScope

theorem progSimA_var (name : String) : ProgSimA bridge bi N leafSpec S T A (.var name) := by
  intro fuel Γ Γ' c env env' rs v hScope _ hSB hSF hHax hEval hAgree
  simp only [simScopeA, Option.some.injEq] at hScope
  subst hScope
  rw [haxToLowCT_var_some] at hHax
  cases hHax
  obtain ⟨_, henv⟩ := evalImp_var_inv bi fuel name env v env' hEval
  subst henv
  exact ⟨rs, RustExec.skip rs, hAgree, hSB, hSF⟩

theorem progSimA_unitVal : ProgSimA bridge bi N leafSpec S T A .unitVal := by
  intro fuel Γ Γ' c env env' rs v hScope _ hSB hSF hHax hEval hAgree
  simp only [simScopeA, Option.some.injEq] at hScope
  subst hScope
  rw [haxToLowCT_unitVal_some] at hHax
  cases hHax
  obtain ⟨_, henv⟩ := evalImp_unitVal_inv bi fuel env v env' hEval
  subst henv
  exact ⟨rs, RustExec.skip rs, hAgree, hSB, hSF⟩

theorem progSimA_tuple (es : List ImpExpr) : ProgSimA bridge bi N leafSpec S T A (.tuple es) := by
  intro fuel Γ Γ' c env env' rs v hScope _ hSB hSF hHax hEval hAgree
  simp only [simScopeA] at hScope
  split at hScope
  · rename_i hAll
    rw [Option.some.injEq] at hScope
    subst hScope
    rw [haxToLowCT_tuple_of_vars es hAll] at hHax
    cases hHax
    have henv := evalImp_tuple_vars_inv bi fuel es env v env' hAll hEval
    subst henv
    exact ⟨rs, RustExec.skip rs, hAgree, hSB, hSF⟩
  · cases hScope

theorem progSimA_seq (a b : ImpExpr)
    (iha : ProgSimA bridge bi N leafSpec S T A a) (ihb : ProgSimA bridge bi N leafSpec S T A b) :
    ProgSimA bridge bi N leafSpec S T A (.seq a b) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar, Bool.and_eq_true] at hConds
  simp only [simScopeA] at hScope
  rcases hA : simScopeA towerOfCallName S T A Γ a with _ | Γ₁
  · rw [hA] at hScope; cases hScope
  rw [hA] at hScope
  obtain ⟨aC, bC, hAtrans, hBtrans, hC⟩ := haxToLowCT_seq_some a b c hHax
  subst hC
  obtain ⟨vA, env_mid, hAeval, hBeval⟩ := evalImp_seq_inv bi fuel a b env v env' hEval
  obtain ⟨rs_mid, hAexec, hAgreeMid, hSBmid, hSFmid⟩ :=
    iha fuel Γ Γ₁ aC env env_mid rs vA hA hConds.1 hSB hSF hAtrans hAeval hAgree
  obtain ⟨rs', hBexec, hAgree', hSB', hSF'⟩ :=
    ihb fuel Γ₁ Γ' bC env_mid env' rs_mid v hScope hConds.2 hSBmid hSFmid hBtrans hBeval
      hAgreeMid
  rw [litTower_seq, arrTower_seq]
  exact ⟨rs', rustExec_RSeq_chain N leafSpec _ _ rs rs_mid rs' hAexec hBexec,
         hAgree', hSB', hSF'⟩

theorem progSimA_ifThenElse (cond : String) (t e : ImpExpr)
    (iht : ProgSimA bridge bi N leafSpec S T A t) (ihe : ProgSimA bridge bi N leafSpec S T A e) :
    ProgSimA bridge bi N leafSpec S T A (.ifThenElse (.var cond) t e) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar, Bool.and_eq_true] at hConds
  obtain ⟨⟨hCondS, hCt⟩, hCe⟩ := hConds
  have hCondT : rs.rsTower cond = none := hSF cond (mem_of_contains S cond hCondS)
  simp only [simScopeA] at hScope
  rcases hT : simScopeA towerOfCallName S T A Γ t with _ | Γt
  · rw [hT] at hScope; cases hScope
  rcases hE : simScopeA towerOfCallName S T A Γ e with _ | Γe
  · rw [hT, hE] at hScope; cases hScope
  rw [hT, hE] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  obtain ⟨tC, eC, hTtrans, hEtrans, hC⟩ := haxToLowCT_ifThenElse_var_some cond t e c hHax
  subst hC
  rw [litTower_ifNz, arrTower_ifNz]
  rcases evalImp_ifThenElse_var_inv bi fuel cond t e env v env' hEval with
    ⟨hCond, hTeval⟩ | ⟨hCond, hEeval⟩
  · obtain ⟨rs', hTexec, hAgree', hSB', hSF'⟩ :=
      iht fuel Γ Γt tC env env' rs v hT hCt hSB hSF hTtrans hTeval hAgree
    have hScalar : rs.rsScalar cond = 1 :=
      envAgreesRustT_bool_to_scalar bridge env rs cond true hAgree hCondT hCond
    refine ⟨rs', rustExec_RIfNz_dispatch_true N leafSpec cond _ _ rs rs' 1 hScalar
      (by decide) hTexec, hAgree', ?_, hSF'⟩
    exact ScopeBound_of_lookup_mono rs' Γ Γt
      (simScopeA_lookup_mono towerOfCallName S T A t Γ Γt hT) hSB'
  · obtain ⟨rs', hEexec, hAgree', hSB', hSF'⟩ :=
      ihe fuel Γ Γe eC env env' rs v hE hCe hSB hSF hEtrans hEeval hAgree
    have hScalar : rs.rsScalar cond = 0 :=
      envAgreesRustT_bool_to_scalar bridge env rs cond false hAgree hCondT hCond
    refine ⟨rs', rustExec_RIfNz_dispatch_false N leafSpec cond _ _ rs rs' hScalar hEexec,
      hAgree', ?_, hSF'⟩
    exact ScopeBound_of_lookup_mono rs' Γ Γe
      (simScopeA_lookup_mono towerOfCallName S T A e Γ Γe hE) hSB'

theorem progSimA_whileLoop (cond : String) (body : ImpExpr)
    (ihBody : ProgSimA bridge bi N leafSpec S T A body) :
    ProgSimA bridge bi N leafSpec S T A (.whileLoop (.var cond) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar, Bool.and_eq_true] at hConds
  obtain ⟨hCondS, hCb⟩ := hConds
  simp only [simScopeA] at hScope
  rcases hB : simScopeA towerOfCallName S T A Γ body with _ | Γb
  · rw [hB] at hScope; cases hScope
  rw [hB] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  obtain ⟨bC, hBtrans, hC⟩ := haxToLowCT_whileLoop_var_some cond body c hHax
  subst hC
  rw [litTower_whileNz, arrTower_whileNz]
  have hMono := simScopeA_lookup_mono towerOfCallName S T A body Γ Γb hB
  induction fuel generalizing env env' rs v with
  | zero =>
    exact absurd hEval (fun h => evalImp_whileLoop_var_fuel_zero_inv bi cond body env v env' h)
  | succ n IH =>
    have hCondT : rs.rsTower cond = none := hSF cond (mem_of_contains S cond hCondS)
    rcases evalImp_whileLoop_var_step_inv bi n cond body env v env' hEval
        (denote_val_or_err_of_haxToLowCT bi (n+1) body bC hBtrans env) with
      ⟨hCondF, hv, henv⟩ | ⟨vB, env_mid, hCondTrue, hBodyEval, hLoopRec⟩
    · subst hv
      subst henv
      have hScalar : rs.rsScalar cond = 0 :=
        envAgreesRustT_bool_to_scalar bridge _ rs cond false hAgree hCondT hCondF
      exact ⟨rs, RustExec.whileFalse cond _ rs hScalar, hAgree, hSB, hSF⟩
    · have hScalar : rs.rsScalar cond = 1 :=
        envAgreesRustT_bool_to_scalar bridge env rs cond true hAgree hCondT hCondTrue
      obtain ⟨rs_mid, hBodyExec, hAgreeMid, hSBmid, hSFmid⟩ :=
        ihBody (n+1) Γ Γb bC env env_mid rs vB hB hCb hSB hSF hBtrans hBodyEval hAgree
      have hSBmid' : ScopeBound rs_mid Γ := ScopeBound_of_lookup_mono rs_mid Γ Γb hMono hSBmid
      obtain ⟨rs', hLoopExec, hAgree', hSB', hSF'⟩ :=
        IH env_mid env' rs_mid v hSBmid' hSFmid hLoopRec hAgreeMid
      exact ⟨rs', RustExec.whileTrue cond _ rs rs_mid rs' 1 hScalar (by decide)
               hBodyExec hLoopExec, hAgree', hSB', hSF'⟩

theorem progSimA_letBind_lit (name : String) (l : ImpLit) (body : ImpExpr)
    (hLit : LitStoreAgrees bridge leafSpec)
    (ihBody : ProgSimA bridge bi N leafSpec S T A body) :
    ProgSimA bridge bi N leafSpec S T A (.letBind name (.lit l) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar] at hConds
  simp only [simScopeA] at hScope
  obtain ⟨bodyC, m, hBodyTrans, hDecode, hC⟩ := haxToLowCT_letBind_lit_some name l body c hHax
  subst hC
  have hBodyEval := evalImp_letBind_lit_inv bi fuel name l body env v env' hEval
  by_cases hTm : T.contains name = true
  · rw [if_pos hTm] at hScope
    split at hScope
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hW, hCompat⟩, hNotS⟩ := hc
      have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
      obtain ⟨k, hk, hl, hm⟩ : ∃ k : Nat, k < 2 ^ 64 ∧ Value.ofLit l = .int (k : Int) ∧ k = m := by
        cases l with
        | int n =>
          simp only [litWord, Bool.and_eq_true, decide_eq_true_eq] at hW
          obtain ⟨h0, h1⟩ := hW
          refine ⟨n.toNat, by omega, by simp [Value.ofLit, Int.toNat_of_nonneg h0], ?_⟩
          simp only [Value.ofLit, valueToScalar, if_pos h0, Option.some.injEq] at hDecode
          exact hDecode
        | _ => simp [litWord] at hW
      subst hm
      rw [litTower_lit_mem T name k bodyC hTm, arrTower_letZero, arrTower_seq, arrTower_limbStore]
      set loc : Located := { locVar := name, locSrc := .TFp } with hloc
      set rs_init := rsSetTower rs name ⟨.TFp, default⟩ with hrs_init
      have hLookup : locatedLookup rs_init loc = some default := locatedLookup_letZero rs name .TFp
      set newVal := leafSpec.limbStore loc (default : RustVal .TFp) 0 (BitVec.ofNat 64 k)
        with hnewVal
      have hStore : RustExec N leafSpec (.RLimbStore loc 0 (BitVec.ofNat 64 k)) rs_init
          (locatedUpdate rs_init loc newVal) :=
        RustExec.limbStore loc 0 _ rs_init default hLookup
      have hRsMidEq : locatedUpdate rs_init loc newVal = rsSetTower rs name ⟨.TFp, newVal⟩ := by
        show rsSetTower (rsSetTower rs name ⟨.TFp, default⟩) name ⟨.TFp, newVal⟩
            = rsSetTower rs name ⟨.TFp, newVal⟩
        exact rsSetTower_collapse rs name ⟨.TFp, default⟩ ⟨.TFp, newVal⟩
      have hBridge : bridge .TFp (Value.ofLit l) newVal := by
        rw [hl]; exact hLit name k hk
      have hAgreeMid : envAgreesRustT bridge (env.extend name (Value.ofLit l))
          (locatedUpdate rs_init loc newVal) := by
        rw [hRsMidEq]
        exact envAgreesRustT_extend_tower bridge env rs name _ .TFp newVal hAgree hBridge
      have hSBmid : ScopeBound (locatedUpdate rs_init loc newVal) ((name, .TFp) :: Γ) := by
        rw [hRsMidEq]
        exact ScopeBound_rsSetTower_cons rs Γ name .TFp newVal hCompat hSB
      have hSFmid : NamesFresh (locatedUpdate rs_init loc newVal) S := by
        rw [hRsMidEq]
        exact NamesFresh_rsSetTower rs S name _ hNotMem hSF
      obtain ⟨rs', hBodyExec, hAgree', hSB', hSF'⟩ :=
        ihBody fuel ((name, .TFp) :: Γ) Γ' bodyC _ env' _ v hScope hConds hSBmid hSFmid
          hBodyTrans hBodyEval hAgreeMid
      exact ⟨rs', RustExec.letZero name .TFp _ rs rs'
        (RustExec.seq _ _ _ _ _ hStore hBodyExec), hAgree', hSB', hSF'⟩
    · cases hScope
  · rw [if_neg hTm] at hScope
    split at hScope
    · rename_i hIn
      rw [litTower_lit_not_mem T name m bodyC (by simpa using hTm), arrTower_letU64Zero,
        arrTower_seq, arrTower_scalarSet]
      have hFresh : TowerFresh rs name := hSF name (mem_of_contains S name hIn)
      have hAgreeExt : envAgreesRustT bridge (env.extend name (Value.ofLit l))
                        (rsSetScalar rs name m) :=
        envAgreesRustT_extend_scalar_fresh bridge env rs name (Value.ofLit l) m hFresh hDecode
          hAgree
      obtain ⟨rs', hBodyExec, hAgree', hSB', hSF'⟩ :=
        ihBody fuel Γ Γ' bodyC (env.extend name (Value.ofLit l)) env' (rsSetScalar rs name m) v
          hScope hConds hSB hSF hBodyTrans hBodyEval hAgreeExt
      exact ⟨rs', rustExec_RLetU64Zero_ScalarSet N leafSpec name m _ rs rs' hBodyExec,
             hAgree', hSB', hSF'⟩
    · cases hScope

theorem progSimA_letBind_var (name src : String) (body : ImpExpr)
    (ihBody : ProgSimA bridge bi N leafSpec S T A body) :
    ProgSimA bridge bi N leafSpec S T A (.letBind name (.var src) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar] at hConds
  simp only [simScopeA] at hScope
  split at hScope
  · rename_i hc
    obtain ⟨w, hw, hBodyEval⟩ := evalImp_letBind_var_inv bi fuel _ _ body env v env' hEval
    by_cases hEq : name = src
    · subst hEq
      rw [haxToLowCT_letBind_var_self] at hHax
      rw [Env.extend_self env _ w hw] at hBodyEval
      exact ihBody fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hBodyEval hAgree
    · have hIn : S.contains name = true ∧ S.contains src = true := by simp_all
      obtain ⟨bodyC, hBodyT, rfl⟩ := haxToLowCT_letBind_var_ne_some name src body c hEq hHax
      obtain ⟨rs', hExec, hAgree', hSB', hSF'⟩ :=
        ihBody fuel Γ Γ' bodyC (env.extend name w) env' (rsSetScalar rs name (rs.rsScalar src))
          v hScope hConds hSB hSF hBodyT hBodyEval
          (envAgreesRustT_extend_copy bridge env rs name src w
            (hSF name (mem_of_contains S name hIn.1)) (hSF src (mem_of_contains S src hIn.2))
            hw hAgree)
      rw [litTower_letBind_copy, arrTower_letBind_copy]
      exact ⟨rs', rustExec_letBind_copy N leafSpec name src _ rs rs' hEq hExec,
        hAgree', hSB', hSF'⟩
  · cases hScope

theorem progSimA_letBind_app (name f : String) (args : List ImpExpr) (body : ImpExpr)
    (hLeaf : LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hf_arr : f ≠ "array_update") (hf_idx : f ≠ "index")
    (ihBody : ProgSimA bridge bi N leafSpec S T A body) :
    ProgSimA bridge bi N leafSpec S T A (.letBind name (.app f args) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar] at hConds
  simp only [simScopeA, if_neg hf_arr, if_neg hf_idx] at hScope
  split at hScope
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨hNotSc, hArgsIn⟩, hAvoid⟩, hCompat⟩, hNotS⟩ := hc
    have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
    obtain ⟨args', bodyC, hArgsT, hBodyT, hC⟩ :=
      haxToLowCT_letBind_app_some name f args body c hf_arr hf_idx (by simpa using hNotSc) hHax
    subst hC
    rw [litTower_letZero, litTower_seq, litTower_call, arrTower_letZero, arrTower_seq, arrTower_call]
    have hArgsEnv := evalImp_letBind_app_argsDefined bi fuel name f args body env v env'
      (argsInScope_allVars Γ _ args hArgsIn) hEval
    obtain ⟨vals, vRes, hAV, hBi, hBodyEval⟩ :=
      evalImp_letBind_app_vars_inv bi fuel name f args body env v env' hArgsEnv hEval
    have hAB : ArgsTowerBound rs args' := argsInScope_bound Γ _ rs hSB args args' hArgsIn hArgsT
    have hAF : ∀ a ∈ args', a.locVar ≠ name := argsAvoid_fresh name _ args args' hAvoid hArgsT
    set dt := towerOfCallName f with hdt_def
    set dest : Located := { locVar := name, locSrc := dt } with hdest_def
    set rs_init := rsSetTower rs name ⟨dt, default⟩ with hrs_init_def
    have hABinit : ArgsTowerBound rs_init args' :=
      ArgsTowerBound_preserved_extend rs args' name ⟨dt, default⟩ hAF hAB
    have hLookup : locatedLookup rs_init dest = some default := locatedLookup_letZero rs name dt
    set argList := args'.filterMap (fun a => rs_init.rsTower a.locVar) with hargList_def
    set newVal := leafSpec.call f dt (args'.map (·.locDst)) default argList with hnewVal_def
    set rs_mid := locatedUpdate rs_init dest newVal with hrs_mid_def
    have hCallArgs : ∀ a ∈ args', ∃ vv, rs_init.rsTower a.locVar = some ⟨a.locDst, vv⟩ :=
      hABinit
    have hCall : RustExec N leafSpec (.RCall f dest args') rs_init rs_mid :=
      RustExec.call (N := N) (leafSpec := leafSpec)
        f dest args' rs_init default argList hLookup rfl hCallArgs
    have hArgsAgree :
        List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => bridge p.1 v p.2) vals argList := by
      rw [hargList_def, hrs_init_def, filterMap_rsSetTower_avoid rs name _ args' hAF]
      exact argsAgree_of_envAgrees bridge env rs dt hAgree.2 args args' vals hArgsT hAV hAB
    have hBridgeAgr : bridge dt vRes newVal := hLeaf args' vals argList default vRes hBi hArgsAgree
    have hRsMidEq : rs_mid = rsSetTower rs name ⟨dt, newVal⟩ := by
      show rsSetTower (rsSetTower rs name ⟨dt, default⟩) name ⟨dt, newVal⟩
           = rsSetTower rs name ⟨dt, newVal⟩
      exact rsSetTower_collapse rs name ⟨dt, default⟩ ⟨dt, newVal⟩
    have hAgreeMid : envAgreesRustT bridge (env.extend name vRes) rs_mid := by
      rw [hRsMidEq]
      exact envAgreesRustT_extend_tower bridge env rs name vRes dt newVal hAgree hBridgeAgr
    have hSBmid : ScopeBound rs_mid ((name, dt) :: Γ) := by
      rw [hRsMidEq]
      exact ScopeBound_rsSetTower_cons rs Γ name dt newVal hCompat hSB
    have hSFmid : NamesFresh rs_mid S := by
      rw [hRsMidEq]
      exact NamesFresh_rsSetTower rs S name _ hNotMem hSF
    obtain ⟨rs', hBodyExec, hAgreeFinal, hSB', hSF'⟩ :=
      ihBody fuel ((name, dt) :: Γ) Γ' bodyC (env.extend name vRes) env' rs_mid v
        hScope hConds hSBmid hSFmid hBodyT hBodyEval hAgreeMid
    refine ⟨rs', ?_, hAgreeFinal, hSB', hSF'⟩
    refine RustExec.letZero name dt _ rs rs' ?_
    exact RustExec.seq _ _ _ _ _ hCall hBodyExec
  · cases hScope

theorem progSimA_letBind_proj (name t : String) (i : Nat) (body : ImpExpr)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (ihBody : ProgSimA bridge bi N leafSpec S T A body) :
    ProgSimA bridge bi N leafSpec S T A (.letBind name (.proj (.var t) i) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar] at hConds
  simp only [simScopeA] at hScope
  split at hScope
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hLk, hNe⟩, hCompat⟩, hNotS⟩ := hc
    have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
    obtain ⟨bodyC, hBodyT, hC⟩ := haxToLowCT_letBind_proj_some name t i body c hHax
    subst hC
    rw [litTower_letZero, litTower_seq, litTower_tupleLoad, arrTower_letZero, arrTower_seq,
      arrTower_tupleLoad]
    obtain ⟨vTup, vi, hEnvT, hProjI, hBodyEval⟩ :=
      evalImp_letBind_proj_inv bi fuel name t i body env v env' hEval
    obtain ⟨srcV, hRawT⟩ := hSB t .TFp hLk
    have hSrcLook : locatedLookup rs { locVar := t, locSrc := .TFp } = some srcV :=
      locatedLookup_of_rsTower rs t .TFp srcV hRawT
    set dst : Located := { locVar := name, locSrc := .TFp } with hdst
    set src : Located := { locVar := t, locSrc := .TFp } with hsrc
    set rs_init := rsSetTower rs name ⟨.TFp, default⟩ with hrs_init
    have hDstLook : locatedLookup rs_init dst = some default :=
      locatedLookup_letZero rs name .TFp
    have hSrcLook' : locatedLookup rs_init src = some srcV := by
      rw [hrs_init,
          CatCrypt.Crypto.Jasmin.LowCT.locatedLookup_rsSetTower_other
            rs name ⟨.TFp, default⟩ src (Ne.symm hNe)]
      exact hSrcLook
    set newVal := leafSpec.tupleLoad dst default ⟨src.locDst, srcV⟩ i with hnewVal
    set rs_mid := locatedUpdate rs_init dst newVal with hrs_mid
    have hLoad : RustExec N leafSpec (.RTupleLoad dst src i) rs_init rs_mid :=
      RustExec.tupleLoad dst src i rs_init default srcV hDstLook hSrcLook'
    have hTupBridge : bridge .TFp vTup srcV := hAgree.2 t vTup hEnvT .TFp srcV hRawT
    have hCompBridge : bridge .TFp vi newVal := hProj name i vTup vi srcV hTupBridge hProjI
    have hRsMidEq : rs_mid = rsSetTower rs name ⟨.TFp, newVal⟩ := by
      show rsSetTower (rsSetTower rs name ⟨.TFp, default⟩) name ⟨.TFp, newVal⟩
          = rsSetTower rs name ⟨.TFp, newVal⟩
      exact rsSetTower_collapse rs name ⟨.TFp, default⟩ ⟨.TFp, newVal⟩
    have hAgreeMid : envAgreesRustT bridge (env.extend name vi) rs_mid := by
      rw [hRsMidEq]
      exact envAgreesRustT_extend_tower bridge env rs name vi .TFp newVal hAgree hCompBridge
    have hSBmid : ScopeBound rs_mid ((name, .TFp) :: Γ) := by
      rw [hRsMidEq]
      exact ScopeBound_rsSetTower_cons rs Γ name .TFp newVal hCompat hSB
    have hSFmid : NamesFresh rs_mid S := by
      rw [hRsMidEq]
      exact NamesFresh_rsSetTower rs S name _ hNotMem hSF
    obtain ⟨rs', hBodyExec, hAgreeFinal, hSB', hSF'⟩ :=
      ihBody fuel ((name, .TFp) :: Γ) Γ' bodyC (env.extend name vi) env' rs_mid v
        hScope hConds hSBmid hSFmid hBodyT hBodyEval hAgreeMid
    refine ⟨rs', ?_, hAgreeFinal, hSB', hSF'⟩
    refine RustExec.letZero name .TFp _ rs rs' ?_
    exact RustExec.seq _ _ _ _ _ hLoad hBodyExec
  · cases hScope

/-- A variable argument list of length two resolves to the values of its names. -/
theorem allVars_two {env : Env} {a b : String} {vals : List Value}
    (h : AllVars env [.var a, .var b] vals) :
    ∃ va vb, vals = [va, vb] ∧ env a = some va ∧ env b = some vb := by
  cases h with
  | cons _ va _ _ ha h2 =>
    cases h2 with
    | cons _ vb _ _ hb h3 =>
      cases h3
      exact ⟨va, vb, rfl, ha, hb⟩

/-- A variable argument list of length three resolves to the values of its names. -/
theorem allVars_three {env : Env} {a b d : String} {vals : List Value}
    (h : AllVars env [.var a, .var b, .var d] vals) :
    ∃ va vb vd, vals = [va, vb, vd] ∧ env a = some va ∧ env b = some vb ∧ env d = some vd := by
  cases h with
  | cons _ va _ _ ha h2 =>
    cases h2 with
    | cons _ vb _ _ hb h3 =>
      cases h3 with
      | cons _ vd _ _ hd h4 =>
        cases h4
        exact ⟨va, vb, vd, rfl, ha, hb, hd⟩

theorem progSimA_letBind_index (name f arr idx : String) (body : ImpExpr)
    (hf_arr : f ≠ "array_update") (hf_idx : f = "index")
    (hIdx : IndexAgrees bridge bi leafSpec)
    (ihBody : ProgSimA bridge bi N leafSpec S T A body) :
    ProgSimA bridge bi N leafSpec S T A (.letBind name (.app f [.var arr, .var idx]) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar] at hConds
  simp only [simScopeA, if_neg hf_arr, if_pos hf_idx] at hScope
  rcases hA : List.lookup arr A with _ | t
  · rw [hA] at hScope; cases hScope
  simp only [hA] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hLk, hNe⟩, hIdxS'⟩, hCompat⟩, hNotS⟩ := hc
  have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
  have hIdxS : idx ∈ S := mem_of_contains S idx hIdxS'
  obtain ⟨bodyC, hBodyT, hC⟩ := haxToLowCT_letBind_index_some name f arr idx body c hf_arr hf_idx hHax
  subst hC
  rw [litTower_letZero, litTower_seq, litTower_arrLoad, arrTower_letZero, arrTower_seq,
    arrTower_arrLoad A _ { locVar := arr, locSrc := .TFp } idx t hA]
  have hArgsEnv := evalImp_letBind_app_argsDefined bi fuel name f [.var arr, .var idx] body env v
    env' (by simp) hEval
  obtain ⟨vals, vRes, hAV, hBi, hBodyEval⟩ :=
    evalImp_letBind_app_vars_inv bi fuel name f _ body env v env' hArgsEnv hEval
  obtain ⟨vArr, vIdx, rfl, hvArr, hvIdx⟩ := allVars_two hAV
  subst hf_idx
  obtain ⟨arrV, hRawArr⟩ := hSB arr t hLk
  have hTIdx : rs.rsTower idx = none := hSF idx hIdxS
  have hk : ∀ n, valueToScalar vIdx = some n → n = rs.rsScalar idx :=
    fun n hn => (hAgree.1 idx vIdx n hvIdx hTIdx hn).symm
  set dst : Located := { locVar := name, locSrc := .TFp } with hdst
  set src : Located := { locVar := arr, locSrc := t } with hsrc
  set rs_init := rsSetTower rs name ⟨.TFp, default⟩ with hrs_init
  have hDstLook : locatedLookup rs_init dst = some default := locatedLookup_letZero rs name .TFp
  have hSrcLook : locatedLookup rs_init src = some arrV := by
    rw [hrs_init, CatCrypt.Crypto.Jasmin.LowCT.locatedLookup_rsSetTower_other
      rs name ⟨.TFp, default⟩ src (Ne.symm hNe)]
    exact locatedLookup_of_rsTower rs arr t arrV hRawArr
  set newVal := leafSpec.arrLoad dst default ⟨t, arrV⟩ (rs.rsScalar idx) with hnewVal
  set rs_mid := locatedUpdate rs_init dst newVal with hrs_mid
  have hLoad : RustExec N leafSpec (.RArrLoad dst src idx) rs_init rs_mid :=
    RustExec.arrLoad dst src idx rs_init (rs.rsScalar idx) default arrV rfl hDstLook hSrcLook
  have hB : bridge .TFp vRes newVal :=
    hIdx name t vArr vIdx vRes arrV (rs.rsScalar idx) (hAgree.2 arr vArr hvArr t arrV hRawArr)
      hk hBi
  have hRsMidEq : rs_mid = rsSetTower rs name ⟨.TFp, newVal⟩ := by
    show rsSetTower (rsSetTower rs name ⟨.TFp, default⟩) name ⟨.TFp, newVal⟩
        = rsSetTower rs name ⟨.TFp, newVal⟩
    exact rsSetTower_collapse rs name ⟨.TFp, default⟩ ⟨.TFp, newVal⟩
  have hAgreeMid : envAgreesRustT bridge (env.extend name vRes) rs_mid := by
    rw [hRsMidEq]
    exact envAgreesRustT_extend_tower bridge env rs name vRes .TFp newVal hAgree hB
  have hSBmid : ScopeBound rs_mid ((name, .TFp) :: Γ) := by
    rw [hRsMidEq]
    exact ScopeBound_rsSetTower_cons rs Γ name .TFp newVal hCompat hSB
  have hSFmid : NamesFresh rs_mid S := by
    rw [hRsMidEq]
    exact NamesFresh_rsSetTower rs S name _ hNotMem hSF
  obtain ⟨rs', hBodyExec, hAgreeFinal, hSB', hSF'⟩ :=
    ihBody fuel ((name, .TFp) :: Γ) Γ' bodyC (env.extend name vRes) env' rs_mid v
      hScope hConds hSBmid hSFmid hBodyT hBodyEval hAgreeMid
  refine ⟨rs', ?_, hAgreeFinal, hSB', hSF'⟩
  refine RustExec.letZero name .TFp _ rs rs' ?_
  exact RustExec.seq _ _ _ _ _ hLoad hBodyExec

theorem progSimA_letBind_arrUpdate (name f arr idx src : String) (body : ImpExpr)
    (hf_arr : f = "array_update")
    (hUpd : ArrUpdateAgrees bridge bi leafSpec)
    (ihBody : ProgSimA bridge bi N leafSpec S T A body) :
    ProgSimA bridge bi N leafSpec S T A
      (.letBind name (.app f [.var arr, .var idx, .var src]) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  simp only [condsScalar] at hConds
  simp only [simScopeA, if_pos hf_arr] at hScope
  rcases hA : List.lookup arr A with _ | t
  · rw [hA] at hScope; cases hScope
  simp only [hA] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hName, hLk⟩, hLkSrc⟩, hIdxS'⟩ := hc
  have hIdxS : idx ∈ S := mem_of_contains S idx hIdxS'
  subst hName
  obtain ⟨bodyC, hBodyT, hC⟩ :=
    haxToLowCT_letBind_arrUpdate_some name f name idx src body c hf_arr hHax
  subst hC
  rw [litTower_seq, litTower_arrStore, arrTower_seq,
    arrTower_arrStore A { locVar := name, locSrc := .TBytes 0 } { locVar := src, locSrc := .TBytes 0 }
      idx t hA]
  have hArgsEnv := evalImp_letBind_app_argsDefined bi fuel name f
    [.var name, .var idx, .var src] body env v env' (by simp) hEval
  obtain ⟨vals, vRes, hAV, hBi, hBodyEval⟩ :=
    evalImp_letBind_app_vars_inv bi fuel name f _ body env v env' hArgsEnv hEval
  obtain ⟨vArr, vIdx, vSrc, rfl, hvArr, hvIdx, hvSrc⟩ := allVars_three hAV
  subst hf_arr
  obtain ⟨arrV, hRawArr⟩ := hSB name t hLk
  obtain ⟨srcV, hRawSrc⟩ := hSB src t.elemType hLkSrc
  have hTIdx : rs.rsTower idx = none := hSF idx hIdxS
  have hk : ∀ n, valueToScalar vIdx = some n → n = rs.rsScalar idx :=
    fun n hn => (hAgree.1 idx vIdx n hvIdx hTIdx hn).symm
  have hNotMem : name ∉ S := by
    intro hm
    rw [hSF name hm] at hRawArr
    cases hRawArr
  set arrL : Located := { locVar := name, locSrc := t } with harrL
  set srcL : Located := { locVar := src, locSrc := t.elemType } with hsrcL
  have hArrLook : locatedLookup rs arrL = some arrV := locatedLookup_of_rsTower rs name t arrV hRawArr
  have hSrcLook : locatedLookup rs srcL = some srcV :=
    locatedLookup_of_rsTower rs src t.elemType srcV hRawSrc
  set newVal := leafSpec.arrStore arrL arrV (rs.rsScalar idx) ⟨t.elemType, srcV⟩ with hnewVal
  have hStore : RustExec N leafSpec (.RArrStore arrL idx srcL) rs (rsSetTower rs name ⟨t, newVal⟩) :=
    RustExec.arrStore arrL idx srcL rs (rs.rsScalar idx) arrV srcV rfl hArrLook hSrcLook
  have hB : bridge t vRes newVal :=
    hUpd name t vArr vIdx vSrc vRes arrV srcV (rs.rsScalar idx)
      (hAgree.2 name vArr hvArr t arrV hRawArr) hk (hAgree.2 src vSrc hvSrc _ srcV hRawSrc) hBi
  have hAgreeMid : envAgreesRustT bridge (env.extend name vRes) (rsSetTower rs name ⟨t, newVal⟩) :=
    envAgreesRustT_extend_tower bridge env rs name vRes t newVal hAgree hB
  have hSBmid : ScopeBound (rsSetTower rs name ⟨t, newVal⟩) Γ :=
    ScopeBound_rsSetTower_same rs Γ name t newVal hLk hSB
  have hSFmid : NamesFresh (rsSetTower rs name ⟨t, newVal⟩) S :=
    NamesFresh_rsSetTower rs S name _ hNotMem hSF
  obtain ⟨rs', hBodyExec, hAgreeFinal, hSB', hSF'⟩ :=
    ihBody fuel Γ Γ' bodyC (env.extend name vRes) env' _ v
      hScope hConds hSBmid hSFmid hBodyT hBodyEval hAgreeMid
  exact ⟨rs', RustExec.seq _ _ _ _ _ hStore hBodyExec, hAgreeFinal, hSB', hSF'⟩

/-- On an assignment that `simScopeA` accepts, the checker is `simScope`, and
    `arrTower A ∘ litTower T` fixes its lowering. -/
theorem progSimA_of_progSimT_assign (e : ImpExpr)
    (hScopeEq : ∀ Γ, simScopeA towerOfCallName S T A Γ e = simScope S Γ e)
    (hFix : ∀ c, haxToLowCT e = some c → arrTower A (litTower T c) = c)
    (h : ProgSimT bridge bi N leafSpec S e) : ProgSimA bridge bi N leafSpec S T A e := by
  intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  rw [hScopeEq] at hScope
  rw [hFix c hHax]
  exact h fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree

end ArmsA

/-! ## §5  The program-level theorem -/

/-- **Program-level simulation with array loads and stores.**  Every source
    program simulates by `arrTower A (litTower T c)` for its lowering `c` under
    `envAgreesRustT`, when every call name other than `index` and `array_update`
    satisfies `LeafCallAgreesArgs`, tuple loads agree with `Value.projIdx`,
    literal stores agree with `LitStoreAgrees`, and the array load and store
    agree with the builtins `index` and `array_update`. -/
theorem haxToLowCT_simulates_programA
    (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (S T : List String) (A : TowerScope)
    (hLeaf : ∀ f, f ≠ "array_update" → f ≠ "index" →
      LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (hLit : LitStoreAgrees bridge leafSpec)
    (hIdx : IndexAgrees bridge bi leafSpec)
    (hUpd : ArrUpdateAgrees bridge bi leafSpec)
    (e : ImpExpr) : ProgSimA bridge bi N leafSpec S T A e := by
  have noneArm := progSimA_of_simScopeA_none bridge bi N leafSpec S T A
  induction e using ImpExpr.ind with
  | var name => exact progSimA_var bridge bi N leafSpec S T A name
  | unitVal => exact progSimA_unitVal bridge bi N leafSpec S T A
  | seq a b iha ihb => exact progSimA_seq bridge bi N leafSpec S T A a b iha ihb
  | tuple es _ => exact progSimA_tuple bridge bi N leafSpec S T A es
  | letBind name val body _ ihBody =>
    cases val with
    | lit l => exact progSimA_letBind_lit bridge bi N leafSpec S T A name l body hLit ihBody
    | app f args =>
      by_cases hf_arr : f = "array_update"
      · rcases hSh : varArgs3 args with _ | ⟨arr, idx, src⟩
        · refine noneArm _ fun Γ => ?_
          simp only [simScopeA, if_pos hf_arr]
          split
          · simp [varArgs3] at hSh
          · rfl
        · rw [varArgs3_some hSh]
          exact progSimA_letBind_arrUpdate bridge bi N leafSpec S T A name f arr idx src body
            hf_arr hUpd ihBody
      by_cases hf_idx : f = "index"
      · rcases hSh : varArgs2 args with _ | ⟨arr, idx⟩
        · refine noneArm _ fun Γ => ?_
          simp only [simScopeA, if_neg hf_arr, if_pos hf_idx]
          split
          · simp [varArgs2] at hSh
          · rfl
        · rw [varArgs2_some hSh]
          exact progSimA_letBind_index bridge bi N leafSpec S T A name f arr idx body hf_arr
            hf_idx hIdx ihBody
      exact progSimA_letBind_app bridge bi N leafSpec S T A name f args body
        (hLeaf f hf_arr hf_idx) hf_arr hf_idx ihBody
    | var src => exact progSimA_letBind_var bridge bi N leafSpec S T A name src body ihBody
    | proj pe i =>
      cases pe with
      | var t =>
        exact progSimA_letBind_proj bridge bi N leafSpec S T A name t i body hProj ihBody
      | _ => exact noneArm _ fun Γ => by simp [simScopeA]
    | _ => exact noneArm _ fun Γ => by simp [simScopeA]
  | ifThenElse cond t e _ iht ihe =>
    cases cond with
    | var v_cond => exact progSimA_ifThenElse bridge bi N leafSpec S T A v_cond t e iht ihe
    | _ => exact noneArm _ fun Γ => by simp [simScopeA]
  | whileLoop cond body _ ihBody =>
    cases cond with
    | var v_cond => exact progSimA_whileLoop bridge bi N leafSpec S T A v_cond body ihBody
    | _ => exact noneArm _ fun Γ => by simp [simScopeA]
  | assign name rhs _ =>
    cases rhs with
    | lit l =>
      refine progSimA_of_progSimT_assign bridge bi N leafSpec S T A _ (fun Γ => rfl) ?_
        (progSimT_assign_lit bridge bi N leafSpec S name l)
      intro c hc
      obtain ⟨m, rfl⟩ := haxToLowCT_assign_lit_shape name l c hc
      simp [litTower, arrTower]
    | app f args =>
      by_cases hf : f = "array_update" ∨ f = "index"
      · exact noneArm _ fun Γ => by simp only [simScopeA, if_pos hf]
      have hf_arr : f ≠ "array_update" := fun h => hf (Or.inl h)
      have hf_idx : f ≠ "index" := fun h => hf (Or.inr h)
      refine progSimA_of_progSimT_assign bridge bi N leafSpec S T A _
        (fun Γ => by simp only [simScopeA, simScope, if_neg hf, if_neg hf_arr]) ?_
        (progSimT_assign_app bridge bi N leafSpec S name f args hf_arr (hLeaf f hf_arr hf_idx))
      intro c hc
      obtain ⟨_, _, rfl⟩ := haxToLowCT_assign_app_some name f args c hf_arr hc
      simp [litTower, arrTower]
    | _ => exact noneArm _ fun Γ => by simp [simScopeA]
  | typeAscription e _ ih =>
    intro fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
    simp only [simScopeA] at hScope
    simp only [condsScalar] at hConds
    rw [haxToLowCT_typeAscription_eq] at hHax
    rw [evalImp_typeAscription] at hEval
    exact ih fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree
  | _ => exact noneArm _ fun Γ => by simp [simScopeA]

/-! ## §6  The limb read of a tower slot into the scalar heap

`haxToLowCT` lowers a binding `let x = index(v, i)` of a variable `v` at a
non-negative integer literal `i` to
`RLetU64Zero x (RSeq (RScalarSetExpr x (SLimb v i)) body')`: limb `i` of the
tower slot `v`, the little-endian `u64` at byte offset `8 * i` (`towerLimb`),
is written to the scalar `x`.  The source run applies the builtin `index` to the
value of `v` and the integer `i`.  A container slot is indexed by element through
`RArrLoad`, with the stride of its element type; the limb read is that of a slot
whose type is not a container (`t.elemType = t`). -/

section LimbRead

open _root_.Hax (denoteArgs)
open CatCrypt.Crypto.Jasmin.LowCT (SExpr towerLimb rsTowerLimb)

/-- The limb read agrees with the builtin `index`: at a slot type that is not a
    container, for a value related by `bridge` to the slot, the builtin's result
    on the integer index `i` has the scalar reading `towerLimb` of the slot at
    `i`. -/
def LimbReadAgrees (bridge : ValueTowerBridge) (bi : Builtins) : Prop :=
  ∀ (t : TowerType) (vArr vRes : Value) (arrV : RustVal t) (i : Nat),
    t.elemType = t → bridge t vArr arrV →
    bi "index" [vArr, .int (i : Int)] = some vRes →
    valueToScalar vRes = some (towerLimb arrV i)

/-- The lowering of a limb read. -/
theorem haxToLowCT_letBind_limb_some (name v : String) (k : Int) (hk : 0 ≤ k) (body : ImpExpr)
    (c : LowCT)
    (h : haxToLowCT (.letBind name (.app "index" [.var v, .lit (.int k)]) body) = some c) :
    ∃ bodyC, haxToLowCT body = some bodyC ∧
      c = .RLetU64Zero name (.RSeq (.RScalarSetExpr name (.SLimb v k.toNat)) bodyC) := by
  simp only [haxToLowCT, haxArgsToLocated, haxArgToLocated] at h
  cases hB : haxToLowCT body with
  | none => simp [hB] at h
  | some bodyC =>
    refine ⟨bodyC, rfl, ?_⟩
    simp [hB, limbReadArgs, hk] at h
    exact h.symm

/-- The source run of a binding `let name = f(v, l)` of a variable and a literal:
    the builtin `f` on the value of `v` and the value of `l`, then the body from
    the extended environment. -/
theorem evalImp_letBind_app_var_lit_inv (bi : Builtins) (fuel : Nat) (name f v : String)
    (l : ImpLit) (body : ImpExpr) (env : Env) (w : Value) (env' : Env)
    (h : evalImp bi fuel (.letBind name (.app f [.var v, .lit l]) body) env = some (w, env')) :
    ∃ va r, env v = some va ∧ bi f [va, Value.ofLit l] = some r ∧
      evalImp bi fuel body (env.extend name r) = some (w, env') := by
  unfold evalImp at h ⊢
  have hNil : (denoteArgs bi fuel ([] : List ImpExpr)).run env = (some [], env) := by
    unfold denoteArgs; rfl
  rw [denote_letBind_run_eq, denote_app_run_eq, denoteArgs_cons_run_eq, denote_var_run_eq] at h
  cases ha : env v with
  | none => rw [ha] at h; simp at h
  | some va =>
    rw [ha] at h
    simp only at h
    rw [denoteArgs_cons_run_eq, denote_lit_eq] at h
    simp only at h
    rw [hNil] at h
    simp only [Option.map_some] at h
    cases hbi : bi f [va, Value.ofLit l] with
    | none => rw [hbi] at h; simp at h
    | some r =>
      rw [hbi] at h
      exact ⟨va, r, rfl, hbi, h⟩

/-- The `RustExec` step of a limb read: from the scalar `name` zeroed,
    `RScalarSetExpr name (SLimb v i)` sets it to limb `i` of the slot `v`. -/
theorem limbRead_exec (N : Nat) (leafSpec : LeafSpec) (name v : String) (i : Nat)
    (rs : RustState) (t : TowerType) (arrV : RustVal t) (hT : rs.rsTower v = some ⟨t, arrV⟩) :
    RustExec N leafSpec (.RScalarSetExpr name (.SLimb v i)) (rsSetScalar rs name 0)
      (rsSetScalar rs name (towerLimb arrV i)) := by
  have hS := RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) name (.SLimb v i)
    (rsSetScalar rs name 0)
  have hv : (SExpr.SLimb v i).evalState (rsSetScalar rs name 0) = towerLimb arrV i := by
    simp [SExpr.evalState, rsTowerLimb, rsSetScalar, hT]
  rw [hv, rsSetScalar_collapse] at hS
  exact hS

/-- **Simulation of a limb read.**  For a slot `v` of a type that is not a
    container, related by `bridge` to the value of `v`, and a scalar name `name`
    without a tower binding, the source run of `let name = index(v, k); body` is
    simulated by `RLetU64Zero name (RSeq (RScalarSetExpr name (SLimb v k)) bodyC)`
    when every run of `body` from the extended environment is simulated by
    `bodyC` from the scalar heap extended with the limb. -/
theorem limbRead_sim (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (hLimb : LimbReadAgrees bridge bi) (name v : String) (k : Int) (hk : 0 ≤ k)
    (body : ImpExpr) (bodyC : LowCT) (fuel : Nat) (env env' : Env) (rs : RustState) (w : Value)
    (t : TowerType) (arrV : RustVal t) (ht : t.elemType = t)
    (hT : rs.rsTower v = some ⟨t, arrV⟩) (hFresh : TowerFresh rs name)
    (hEval : evalImp bi fuel (.letBind name (.app "index" [.var v, .lit (.int k)]) body) env =
      some (w, env'))
    (hAgree : envAgreesRustT bridge env rs) (P : RustState → Prop)
    (hBody : ∀ (r : Value) (n : Nat), valueToScalar r = some n →
      evalImp bi fuel body (env.extend name r) = some (w, env') →
      envAgreesRustT bridge (env.extend name r) (rsSetScalar rs name n) →
      ∃ rs', RustExec N leafSpec bodyC (rsSetScalar rs name n) rs' ∧ P rs') :
    ∃ rs', RustExec N leafSpec
        (.RLetU64Zero name (.RSeq (.RScalarSetExpr name (.SLimb v k.toNat)) bodyC)) rs rs' ∧
      P rs' := by
  obtain ⟨va, r, hva, hbi, hBodyEval⟩ :=
    evalImp_letBind_app_var_lit_inv bi fuel name "index" v (.int k) body env w env' hEval
  have hkk : ((k.toNat : Nat) : Int) = k := Int.toNat_of_nonneg hk
  have hr : valueToScalar r = some (towerLimb arrV k.toNat) := by
    refine hLimb t va r arrV k.toNat ht (hAgree.2 v va hva t arrV hT) ?_
    rw [hkk]
    exact hbi
  obtain ⟨rs', hBodyExec, hP⟩ := hBody r _ hr hBodyEval
    (envAgreesRustT_extend_scalar_fresh bridge env rs name r _ hFresh hr hAgree)
  refine ⟨rs', ?_, hP⟩
  refine RustExec.letU64Zero name _ rs rs' ?_
  exact RustExec.seq _ _ _ _ _ (limbRead_exec N leafSpec name v k.toNat rs t arrV hT) hBodyExec

end LimbRead

end CatCrypt.Crypto.Hax
