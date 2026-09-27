/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTExec

/-!
# Bounded unrolling of `RWhileNz` and determinism of the scalar commands

`unrollNz n b k` is the `k`-fold unrolling of `RWhileNz n b` into nested
`RIfNz` conditionals: `unrollNz n b (k+1) = RIfNz n (RSeq b (unrollNz n b k)) RSkip`
and `unrollNz n b 0 = RSkip`.  A run of the loop with at most `k` guard trips is
a run of the unrolling, and a run of the unrolling that ends with the guard at
`0` is a run of the loop.

`WhileTrips N leafSpec n b j rs rs'` is the run of `RWhileNz n b` from `rs` to
`rs'` with exactly `j` executions of the body; every `RustExec` run of the loop
has such a trip count, and every trip-counted run is a `RustExec` run.

`IsScalarCmd` is the fragment of scalar-slot commands (`RSkip`, `RSeq`, `RBlock`,
`RLetU64Zero`, `RScalarSet`, `RScalarSetExpr`, `RIfNz`, `RWhileNz`); on it
`RustExec` is deterministic.

`runK k` interprets the scalar-slot commands with at most `k` trips per loop.
A successful run is a `RustExec` run of the command and of `unrollAll k` of the
command, the command with every loop unrolled `k` times. `runKL` is the same
interpreter over an association-list store, and `runK_storeState` relates the two.

## Main definitions

* `unrollNz`, `unrollAll`: the `k`-fold unrolling of a loop and of every loop
* `WhileTrips`: a loop run with its trip count
* `IsScalarCmd`: the scalar-slot command fragment
* `runK`, `runKL`: the trip-bounded interpreters over states and over stores

## Main results

* `rustExec_whileNz_trips`, `whileTrips_rustExec`: loop runs are the trip-counted runs
* `whileTrips_unrollNz`: a run with `j ≤ k` trips is a run of `unrollNz n b k`
* `rustExec_unrollNz`: a loop run with at most `k` trips is a run of `unrollNz n b k`
* `unrollNz_rustExec_whileNz`: a run of `unrollNz n b k` ending at guard `0` is a
  loop run
* `rustExec_deterministic`: `RustExec` is deterministic on `IsScalarCmd`
* `runK_rustExec`, `runK_unrollAll`: a `runK k` run is a run of the command and of
  its unrolling
* `runK_storeState`: `runK` on a store state is `runKL` on the store
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.GuardedUnroll

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## The unrolling -/

/-- The `k`-fold unrolling of `RWhileNz n b`. -/
def unrollNz (n : String) (b : LowCT) : Nat → LowCT
  | 0 => .RSkip
  | k + 1 => .RIfNz n (.RSeq b (unrollNz n b k)) .RSkip

/-- A run of `RWhileNz n b` from `rs` to `rs'` with exactly `j` body executions. -/
inductive WhileTrips (N : Nat) (leafSpec : LeafSpec) (n : String) (b : LowCT) :
    Nat → RustState → RustState → Prop where
  | done : ∀ rs, rs.rsScalar n = 0 → WhileTrips N leafSpec n b 0 rs rs
  | step : ∀ j rs r1 rs', rs.rsScalar n ≠ 0 → RustExec N leafSpec b rs r1 →
      WhileTrips N leafSpec n b j r1 rs' → WhileTrips N leafSpec n b (j + 1) rs rs'

variable {N : Nat} {leafSpec : LeafSpec}

/-- Every `RustExec` run of `RWhileNz n b` has a trip count. -/
theorem rustExec_whileNz_trips {n : String} {b : LowCT} {rs rs' : RustState}
    (h : RustExec N leafSpec (.RWhileNz n b) rs rs') :
    ∃ j, WhileTrips N leafSpec n b j rs rs' := by
  generalize hc : LowCT.RWhileNz n b = c at h
  induction h with
  | whileFalse e body rs he =>
      cases hc; exact ⟨0, .done rs he⟩
  | whileTrue e body rs r1 rs' v hv hv0 hb _ _ ih =>
      cases hc
      obtain ⟨j, hj⟩ := ih rfl
      exact ⟨j + 1, .step j rs r1 rs' (hv ▸ hv0) hb hj⟩
  | _ => cases hc

/-- Every trip-counted run is a `RustExec` run of the loop. -/
theorem whileTrips_rustExec {n : String} {b : LowCT} {j : Nat} {rs rs' : RustState}
    (h : WhileTrips N leafSpec n b j rs rs') :
    RustExec N leafSpec (.RWhileNz n b) rs rs' := by
  induction h with
  | done rs h0 => exact .whileFalse _ _ _ h0
  | step j rs r1 rs' hne hb _ ih => exact .whileTrue _ _ _ _ _ _ rfl hne hb ih

/-- A run with `j ≤ k` trips is a run of the `k`-fold unrolling. -/
theorem whileTrips_unrollNz {n : String} {b : LowCT} {j : Nat} {rs rs' : RustState}
    (h : WhileTrips N leafSpec n b j rs rs') :
    ∀ k, j ≤ k → RustExec N leafSpec (unrollNz n b k) rs rs' := by
  induction h with
  | done rs h0 =>
      intro k _
      cases k with
      | zero => exact .skip rs
      | succ k => exact .ifFalse _ _ _ _ _ h0 (.skip rs)
  | step j rs r1 rs' hne hb _ ih =>
      intro k hk
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact .ifTrue _ _ _ _ _ _ rfl hne (.seq _ _ _ _ _ hb (ih k (by omega)))

/-- A run of `RWhileNz n b` with at most `k` guard trips is a run of
    `unrollNz n b k`. -/
theorem rustExec_unrollNz {n : String} {b : LowCT} {rs rs' : RustState} {j k : Nat}
    (ht : WhileTrips N leafSpec n b j rs rs') (hjk : j ≤ k) :
    RustExec N leafSpec (.RWhileNz n b) rs rs' ∧
      RustExec N leafSpec (unrollNz n b k) rs rs' :=
  ⟨whileTrips_rustExec ht, whileTrips_unrollNz ht k hjk⟩

/-- A run of `unrollNz n b k` that ends with the guard slot at `0` is a run of
    `RWhileNz n b`. -/
theorem unrollNz_rustExec_whileNz {n : String} {b : LowCT} :
    ∀ (k : Nat) {rs rs' : RustState}, RustExec N leafSpec (unrollNz n b k) rs rs' →
      rs'.rsScalar n = 0 → RustExec N leafSpec (.RWhileNz n b) rs rs' := by
  intro k
  induction k with
  | zero =>
      intro rs rs' h h0
      cases h; exact .whileFalse _ _ _ h0
  | succ k ih =>
      intro rs rs' h h0
      cases h with
      | ifTrue _ _ _ _ _ v hv hv0 hs =>
          cases hs with
          | seq _ _ _ r1 _ hb hu => exact .whileTrue _ _ _ _ _ _ rfl (hv ▸ hv0) hb (ih hu h0)
      | ifFalse _ _ _ _ _ hz hs =>
          cases hs; exact .whileFalse _ _ _ hz

/-! ## Determinism on the scalar-slot commands -/

/-- The scalar-slot command fragment. -/
inductive IsScalarCmd : LowCT → Prop
  | rSkip : IsScalarCmd .RSkip
  | rSeq {c₁ c₂ : LowCT} : IsScalarCmd c₁ → IsScalarCmd c₂ → IsScalarCmd (.RSeq c₁ c₂)
  | rBlock {c : LowCT} : IsScalarCmd c → IsScalarCmd (.RBlock c)
  | rLetU64Zero (x : String) {c : LowCT} : IsScalarCmd c → IsScalarCmd (.RLetU64Zero x c)
  | rScalarSet (x : String) (v : Nat) : IsScalarCmd (.RScalarSet x v)
  | rScalarSetExpr (x : String) (e : SExpr) : IsScalarCmd (.RScalarSetExpr x e)
  | rIfNz (g : String) {t e : LowCT} : IsScalarCmd t → IsScalarCmd e →
      IsScalarCmd (.RIfNz g t e)
  | rWhileNz (g : String) {b : LowCT} : IsScalarCmd b → IsScalarCmd (.RWhileNz g b)

/-- `RustExec` is deterministic on `IsScalarCmd`. -/
theorem rustExec_deterministic {c : LowCT} {rs r₁ : RustState}
    (h₁ : RustExec N leafSpec c rs r₁) :
    IsScalarCmd c → ∀ {r₂ : RustState}, RustExec N leafSpec c rs r₂ → r₁ = r₂ := by
  induction h₁ with
  | skip rs => intro _ r₂ h₂; cases h₂; rfl
  | seq c₁ c₂ rs r1 rs' _ _ ih₁ ih₂ =>
      intro hc r₂ h₂
      cases hc with
      | rSeq hc₁ hc₂ =>
          cases h₂ with
          | seq _ _ _ r1' _ h₁' h₂' =>
              obtain rfl := ih₁ hc₁ h₁'
              exact ih₂ hc₂ h₂'
  | letU64Zero x body rs rs' _ ih =>
      intro hc r₂ h₂
      cases hc with
      | rLetU64Zero _ hb => cases h₂ with | letU64Zero _ _ _ _ hb' => exact ih hb hb'
  | scalarSet x v rs => intro _ r₂ h₂; cases h₂; rfl
  | scalarSetExpr x e rs => intro _ r₂ h₂; cases h₂; rfl
  | block body rs rs' _ ih =>
      intro hc r₂ h₂
      cases hc with
      | rBlock hb => cases h₂ with | block _ _ _ hb' => exact ih hb hb'
  | ifTrue e ct cf rs rs' v hv hv0 _ ih =>
      intro hc r₂ h₂
      cases hc with
      | rIfNz _ ht _ =>
          cases h₂ with
          | ifTrue _ _ _ _ _ _ _ _ h' => exact ih ht h'
          | ifFalse _ _ _ _ _ hz _ => exact absurd (hv ▸ hz) hv0
  | ifFalse e ct cf rs rs' hz _ ih =>
      intro hc r₂ h₂
      cases hc with
      | rIfNz _ _ he =>
          cases h₂ with
          | ifTrue _ _ _ _ _ v hv hv0 _ => exact absurd (hv ▸ hz) hv0
          | ifFalse _ _ _ _ _ _ h' => exact ih he h'
  | whileFalse e body rs hz =>
      intro _ r₂ h₂
      cases h₂ with
      | whileFalse => rfl
      | whileTrue _ _ _ _ _ v hv hv0 _ _ => exact absurd (hv ▸ hz) hv0
  | whileTrue e body rs r1 rs' v hv hv0 _ _ ihb ihw =>
      intro hc r₂ h₂
      cases hc with
      | rWhileNz _ hb =>
          cases h₂ with
          | whileFalse _ _ _ hz => exact absurd (hv ▸ hz) hv0
          | whileTrue _ _ _ r1' _ _ _ _ hb' hw' =>
              obtain rfl := ihb hb hb'
              exact ihw (.rWhileNz _ hb) hw'
  | _ => intro hc; cases hc

/-- The Boolean test for `IsScalarCmd`. -/
def isScalarCmdB : LowCT → Bool
  | .RSkip => true
  | .RSeq a b => isScalarCmdB a && isScalarCmdB b
  | .RBlock b => isScalarCmdB b
  | .RLetU64Zero _ b => isScalarCmdB b
  | .RScalarSet _ _ => true
  | .RScalarSetExpr _ _ => true
  | .RIfNz _ t e => isScalarCmdB t && isScalarCmdB e
  | .RWhileNz _ b => isScalarCmdB b
  | _ => false

theorem isScalarCmd_of_isScalarCmdB : ∀ c : LowCT, isScalarCmdB c = true → IsScalarCmd c := by
  intro c
  induction c with
  | RSkip => intro _; exact .rSkip
  | RSeq a b iha ihb =>
      intro h; simp only [isScalarCmdB, Bool.and_eq_true] at h; exact .rSeq (iha h.1) (ihb h.2)
  | RBlock b ih => intro h; exact .rBlock (ih h)
  | RLetU64Zero x b ih => intro h; exact .rLetU64Zero x (ih h)
  | RScalarSet x v => intro _; exact .rScalarSet x v
  | RScalarSetExpr x e => intro _; exact .rScalarSetExpr x e
  | RIfNz g t e iht ihe =>
      intro h; simp only [isScalarCmdB, Bool.and_eq_true] at h; exact .rIfNz g (iht h.1) (ihe h.2)
  | RWhileNz g b ih => intro h; exact .rWhileNz g (ih h)
  | _ => intro h; simp [isScalarCmdB] at h

/-! ## Unrolling every loop of a command -/

/-- Replace every `RWhileNz n b` of a command by `unrollNz n b' k`, with `b'` the
    unrolling of `b`. -/
def unrollAll (k : Nat) : LowCT → LowCT
  | .RSeq a b => .RSeq (unrollAll k a) (unrollAll k b)
  | .RBlock b => .RBlock (unrollAll k b)
  | .RLetU64Zero x b => .RLetU64Zero x (unrollAll k b)
  | .RIfNz g t e => .RIfNz g (unrollAll k t) (unrollAll k e)
  | .RWhileNz g b => unrollNz g (unrollAll k b) k
  | c => c

/-- At most `k` further trips of a loop with guard slot `g` and body `body`;
    `none` when the guard is still nonzero after `k` trips or the body fails. -/
def whileK (body : RustState → Option RustState) (g : String) :
    Nat → RustState → Option RustState
  | 0, rs => if rs.rsScalar g = 0 then some rs else none
  | j + 1, rs => if rs.rsScalar g = 0 then some rs else (body rs).bind (whileK body g j)

/-- `SExpr.limbFree` is decidable, by recursion on the expression. -/
instance decLimbFree : (e : SExpr) → Decidable e.limbFree
  | .SVar _ | .SLit _ => isTrue trivial
  | .SLimb _ _ => isFalse (fun h => h)
  | .SAdd a b | .SSub a b | .SMul a b | .SShr a b | .SShl a b | .SAnd a b
  | .SXor a b | .SLt a b | .SAsr a b | .SMulS a b | .SMulHiU a b | .SMulHiS a b =>
      have := decLimbFree a
      have := decLimbFree b
      inferInstanceAs (Decidable (a.limbFree ∧ b.limbFree))

/-- The interpreter of the scalar-slot commands in which every loop runs at most
    `k` trips.  An assignment `RScalarSetExpr x e` runs when `e` is
    `SExpr.limbFree`, where its value is `e.eval rs.rsScalar`
    (`SExpr.evalState_eq_eval`); a tower-limb read is outside the interpreter. -/
def runK (k : Nat) : LowCT → RustState → Option RustState
  | .RSkip, rs => some rs
  | .RSeq a b, rs => (runK k a rs).bind (runK k b)
  | .RBlock b, rs => runK k b rs
  | .RLetU64Zero x b, rs => runK k b (rsSetScalar rs x 0)
  | .RScalarSet x v, rs => some (rsSetScalar rs x v)
  | .RScalarSetExpr x e, rs =>
      if e.limbFree then some (rsSetScalar rs x (e.eval rs.rsScalar)) else none
  | .RIfNz g t e, rs => if rs.rsScalar g = 0 then runK k e rs else runK k t rs
  | .RWhileNz g b, rs => whileK (runK k b) g k rs
  | _, _ => none

theorem whileK_trips {g : String} {b : LowCT} {body : RustState → Option RustState}
    (hb : ∀ s s', body s = some s' → RustExec N leafSpec b s s') :
    ∀ (j : Nat) (rs rs' : RustState), whileK body g j rs = some rs' →
      ∃ i, i ≤ j ∧ WhileTrips N leafSpec g b i rs rs' := by
  intro j
  induction j with
  | zero =>
      intro rs rs' h
      simp only [whileK] at h
      split_ifs at h with h0
      cases h
      exact ⟨0, le_refl _, .done _ h0⟩
  | succ j ih =>
      intro rs rs' h
      simp only [whileK] at h
      split_ifs at h with h0
      · cases h; exact ⟨0, Nat.zero_le _, .done _ h0⟩
      · cases hbody : body rs with
        | none => rw [hbody] at h; cases h
        | some r1 =>
            rw [hbody, Option.bind_some] at h
            obtain ⟨i, hi, ht⟩ := ih r1 rs' h
            exact ⟨i + 1, by omega, .step i rs r1 rs' h0 (hb rs r1 hbody) ht⟩

/-- A successful run of `runK k` is a `RustExec` run. -/
theorem runK_rustExec (k : Nat) :
    ∀ (c : LowCT) (rs rs' : RustState), runK k c rs = some rs' → RustExec N leafSpec c rs rs' := by
  intro c
  induction c with
  | RSkip => intro rs rs' h; cases h; exact .skip rs
  | RSeq a b iha ihb =>
      intro rs rs' h
      simp only [runK] at h
      cases ha : runK k a rs with
      | none => rw [ha] at h; cases h
      | some r1 =>
          rw [ha, Option.bind_some] at h
          exact .seq _ _ _ _ _ (iha rs r1 ha) (ihb r1 rs' h)
  | RBlock b ih => intro rs rs' h; exact .block _ _ _ (ih rs rs' h)
  | RLetU64Zero x b ih => intro rs rs' h; exact .letU64Zero _ _ _ _ (ih _ rs' h)
  | RScalarSet x v => intro rs rs' h; cases h; exact .scalarSet _ _ _
  | RScalarSetExpr x e =>
      intro rs rs' h
      simp only [runK] at h
      split_ifs at h with hlf
      cases h
      rw [← SExpr.evalState_eq_eval rs e hlf]
      exact .scalarSetExpr _ _ _
  | RIfNz g t e iht ihe =>
      intro rs rs' h
      simp only [runK] at h
      split_ifs at h with h0
      · exact .ifFalse _ _ _ _ _ h0 (ihe rs rs' h)
      · exact .ifTrue _ _ _ _ _ _ rfl h0 (iht rs rs' h)
  | RWhileNz g b ih =>
      intro rs rs' h
      obtain ⟨i, _, ht⟩ := whileK_trips (b := b) (fun s s' hs => ih s s' hs) k rs rs' h
      exact whileTrips_rustExec ht
  | _ => intro rs rs' h; simp [runK] at h

/-- A successful run of `runK k` is a `RustExec` run of the `k`-fold unrolling of
    every loop. -/
theorem runK_unrollAll (k : Nat) :
    ∀ (c : LowCT) (rs rs' : RustState), runK k c rs = some rs' →
      RustExec N leafSpec (unrollAll k c) rs rs' := by
  intro c
  induction c with
  | RSkip => intro rs rs' h; cases h; exact .skip rs
  | RSeq a b iha ihb =>
      intro rs rs' h
      simp only [runK] at h
      cases ha : runK k a rs with
      | none => rw [ha] at h; cases h
      | some r1 =>
          rw [ha, Option.bind_some] at h
          exact .seq _ _ _ _ _ (iha rs r1 ha) (ihb r1 rs' h)
  | RBlock b ih => intro rs rs' h; exact .block _ _ _ (ih rs rs' h)
  | RLetU64Zero x b ih => intro rs rs' h; exact .letU64Zero _ _ _ _ (ih _ rs' h)
  | RScalarSet x v => intro rs rs' h; cases h; exact .scalarSet _ _ _
  | RScalarSetExpr x e =>
      intro rs rs' h
      simp only [runK] at h
      split_ifs at h with hlf
      cases h
      rw [← SExpr.evalState_eq_eval rs e hlf]
      exact .scalarSetExpr _ _ _
  | RIfNz g t e iht ihe =>
      intro rs rs' h
      simp only [runK] at h
      split_ifs at h with h0
      · exact .ifFalse _ _ _ _ _ h0 (ihe rs rs' h)
      · exact .ifTrue _ _ _ _ _ _ rfl h0 (iht rs rs' h)
  | RWhileNz g b ih =>
      intro rs rs' h
      obtain ⟨i, hi, ht⟩ := whileK_trips (b := unrollAll k b) (fun s s' hs => ih s s' hs) k rs rs' h
      exact whileTrips_unrollNz ht k hi
  | _ => intro rs rs' h; simp [runK] at h

/-! ## The interpreter over an association-list store -/

/-- The value of `y` in an association-list store, `0` when absent. -/
def lookupD : List (String × Nat) → String → Nat
  | [], _ => 0
  | (a, v) :: l, y => if y = a then v else lookupD l y

/-- Set `x` to `v` in an association-list store. -/
def insertL : List (String × Nat) → String → Nat → List (String × Nat)
  | [], x, v => [(x, v)]
  | (a, w) :: l, x, v => if x = a then (a, v) :: l else (a, w) :: insertL l x v

/-- The state with tower heap `tw` and the scalar slots of the store `l`. -/
def storeState (tw : String → Option (Σ t : TowerType, RustVal t)) (l : List (String × Nat)) :
    RustState :=
  { rsTower := tw, rsScalar := lookupD l }

/-- `whileK` over an association-list store. -/
def whileKL (body : List (String × Nat) → Option (List (String × Nat))) (g : String) :
    Nat → List (String × Nat) → Option (List (String × Nat))
  | 0, l => if lookupD l g = 0 then some l else none
  | j + 1, l => if lookupD l g = 0 then some l else (body l).bind (whileKL body g j)

/-- `runK` over an association-list store. -/
def runKL (k : Nat) : LowCT → List (String × Nat) → Option (List (String × Nat))
  | .RSkip, l => some l
  | .RSeq a b, l => (runKL k a l).bind (runKL k b)
  | .RBlock b, l => runKL k b l
  | .RLetU64Zero x b, l => runKL k b (insertL l x 0)
  | .RScalarSet x v, l => some (insertL l x v)
  | .RScalarSetExpr x e, l =>
      if e.limbFree then some (insertL l x (e.eval (lookupD l))) else none
  | .RIfNz g t e, l => if lookupD l g = 0 then runKL k e l else runKL k t l
  | .RWhileNz g b, l => whileKL (runKL k b) g k l
  | _, _ => none

theorem lookupD_insertL : ∀ (l : List (String × Nat)) (x y : String) (v : Nat),
    lookupD (insertL l x v) y = if y = x then v else lookupD l y := by
  intro l
  induction l with
  | nil => intro x y v; simp [insertL, lookupD]
  | cons p l ih =>
      intro x y v
      obtain ⟨a, w⟩ := p
      by_cases hxa : x = a
      · subst hxa; by_cases hy : y = x <;> simp [insertL, lookupD, hy]
      · simp only [insertL, if_neg hxa, lookupD, ih]
        by_cases hya : y = a
        · subst hya; simp [Ne.symm hxa]
        · simp [hya]

theorem rsSetScalar_storeState (tw : String → Option (Σ t : TowerType, RustVal t))
    (l : List (String × Nat)) (x : String) (v : Nat) :
    rsSetScalar (storeState tw l) x v = storeState tw (insertL l x v) := by
  simp only [rsSetScalar, storeState, RustState.mk.injEq, true_and]
  funext y
  rw [lookupD_insertL]
  by_cases h : y = x <;> simp [h]

theorem whileK_storeState (tw : String → Option (Σ t : TowerType, RustVal t)) (g : String)
    (body : RustState → Option RustState) (bodyL : List (String × Nat) → Option (List (String × Nat)))
    (hb : ∀ l, body (storeState tw l) = (bodyL l).map (storeState tw)) :
    ∀ (j : Nat) (l : List (String × Nat)),
      whileK body g j (storeState tw l) = (whileKL bodyL g j l).map (storeState tw) := by
  intro j
  induction j with
  | zero =>
      intro l
      have hs : (storeState tw l).rsScalar g = lookupD l g := rfl
      by_cases h0 : lookupD l g = 0 <;> simp [whileK, whileKL, hs, h0]
  | succ j ih =>
      intro l
      have hs : (storeState tw l).rsScalar g = lookupD l g := rfl
      by_cases h0 : lookupD l g = 0
      · simp [whileK, whileKL, hs, h0]
      · simp only [whileK, whileKL, hs, h0, if_false, hb]
        cases bodyL l with
        | none => rfl
        | some l1 => simp only [Option.map_some, Option.bind_some, ih]

theorem runK_storeState (k : Nat) (tw : String → Option (Σ t : TowerType, RustVal t)) :
    ∀ (c : LowCT) (l : List (String × Nat)),
      runK k c (storeState tw l) = (runKL k c l).map (storeState tw) := by
  intro c
  induction c with
  | RSkip => intro l; rfl
  | RSeq a b iha ihb =>
      intro l
      simp only [runK, runKL, iha]
      cases runKL k a l with
      | none => rfl
      | some l1 => simp only [Option.map_some, Option.bind_some, ihb]
  | RBlock b ih => intro l; exact ih l
  | RLetU64Zero x b ih => intro l; simp only [runK, runKL, rsSetScalar_storeState, ih]
  | RScalarSet x v => intro l; simp only [runK, runKL, rsSetScalar_storeState, Option.map_some]
  | RScalarSetExpr x e =>
      intro l
      simp only [runK, runKL]
      split_ifs
      · simp only [Option.map_some]; rw [← rsSetScalar_storeState]; rfl
      · rfl
  | RIfNz g t e iht ihe =>
      intro l
      simp only [runK, runKL]
      split_ifs with h0 <;> simp_all [storeState]
  | RWhileNz g b ih =>
      intro l
      exact whileK_storeState tw g _ _ ih k l
  | _ => intro l; rfl

/-- The default state is the empty store. -/
theorem default_eq_storeState : (default : RustState) = storeState (fun _ => none) [] := rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.GuardedUnroll
