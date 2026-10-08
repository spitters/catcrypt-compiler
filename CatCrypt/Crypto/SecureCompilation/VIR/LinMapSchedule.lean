/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.List.OfFn

/-!
# Linear maps by checked addition-chain schedules

A linear map with integer coefficients is computed by a straight-line program of
sums, differences, doublings, multiplications by an integer constant and copies. A
schedule is such a program, written as data. It is not trusted: the checker
`schedOk` runs it on the unit coefficient rows and compares the rows of its outputs
with the matrix, and `schedOk_sound` states that an accepted schedule computes the
matrix on every input vector over every commutative ring.

## Main results

* `Step`, `Sched`: the schedule language. Values are numbered in order: the inputs
  first, then the value of each step.
* `LinOps`, `Sched.run`: the value of a schedule over a carrier with a sum, a
  difference and a multiplication by an integer. `ringOps R` is the carrier `R`,
  `rowOps` the carrier of coefficient rows.
* `LinOps.Hom`, `Sched.run_map`: a map commuting with the three operations commutes
  with the value of every schedule.
* `schedOk`, `schedOk_sound`: the checker and its soundness.
* `Sched.lower`, `Sched.lower_denote`, `Sched.lower_linMap`: the program of
  `fieldDialect` of a schedule, in continuation form, and its denotation.
* `Sched.cost`: the number of modular operations of a schedule.
* `quadSched`, `externalSched`: the schedules of the 4 × 4 matrix of Poseidon2 and of
  the 16 × 16 external matrix built from it, with their costs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LinMapSchedule

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

universe u v

/-! ## 1. Schedules -/

/-- One step of a schedule. An index names an input or the value of an earlier
    step. -/
inductive Step where
  /-- The sum of the values `i` and `j`. -/
  | add (i j : Nat)
  /-- The difference of the values `i` and `j`. -/
  | sub (i j : Nat)
  /-- Twice the value `i`. -/
  | double (i : Nat)
  /-- The integer `c` times the value `i`. -/
  | scale (c : Int) (i : Nat)
  /-- The value `i`. -/
  | copy (i : Nat)
  deriving DecidableEq, Repr

/-- A schedule: its steps in order and the indices of its outputs. -/
structure Sched where
  /-- The steps. -/
  steps : List Step
  /-- The indices of the outputs. -/
  outs : List Nat
  deriving DecidableEq, Repr

/-- The operations of a carrier of schedule values. -/
structure LinOps (α : Type u) where
  /-- The sum. -/
  add : α → α → α
  /-- The difference. -/
  sub : α → α → α
  /-- The multiplication by an integer. -/
  smul : Int → α → α

/-- The operations of a ring. -/
def ringOps (R : Type u) [Ring R] : LinOps R where
  add a b := a + b
  sub a b := a - b
  smul c a := (c : R) * a

variable {α : Type u} {β : Type v}

/-- The value of a step over the values `vs`; `none` when an index is out of range. -/
def Step.val (o : LinOps α) (vs : List α) : Step → Option α
  | .add i j =>
    match vs[i]?, vs[j]? with
    | some a, some b => some (o.add a b)
    | _, _ => none
  | .sub i j =>
    match vs[i]?, vs[j]? with
    | some a, some b => some (o.sub a b)
    | _, _ => none
  | .double i =>
    match vs[i]? with
    | some a => some (o.add a a)
    | none => none
  | .scale c i =>
    match vs[i]? with
    | some a => some (o.smul c a)
    | none => none
  | .copy i => vs[i]?

/-- The values after the steps, starting from `vs`: each step appends its value, and a
    step with an index out of range appends nothing. -/
def runSteps (o : LinOps α) : List α → List Step → List α
  | vs, [] => vs
  | vs, st :: r => runSteps o (vs ++ (st.val o vs).toList) r

/-- The values at the indices `outs`. -/
def pick (vs : List α) (outs : List Nat) : List α :=
  outs.filterMap fun i => vs[i]?

/-- The outputs of a schedule on the inputs `ins`. -/
def Sched.run (o : LinOps α) (s : Sched) (ins : List α) : List α :=
  pick (runSteps o ins s.steps) s.outs

/-! ## 2. Maps commuting with the operations -/

/-- `φ` commutes with the operations of `o` and `o'`. -/
structure LinOps.Hom (o : LinOps α) (o' : LinOps β) (φ : α → β) : Prop where
  /-- `φ` commutes with the sum. -/
  add : ∀ a b, φ (o.add a b) = o'.add (φ a) (φ b)
  /-- `φ` commutes with the difference. -/
  sub : ∀ a b, φ (o.sub a b) = o'.sub (φ a) (φ b)
  /-- `φ` commutes with the multiplication by an integer. -/
  smul : ∀ c a, φ (o.smul c a) = o'.smul c (φ a)

theorem Step.val_map {o : LinOps α} {o' : LinOps β} {φ : α → β} (h : o.Hom o' φ)
    (vs : List α) (st : Step) : st.val o' (vs.map φ) = (st.val o vs).map φ := by
  cases st with
  | add i j =>
    simp only [Step.val, List.getElem?_map]
    cases vs[i]? <;> cases vs[j]? <;> simp [h.add]
  | sub i j =>
    simp only [Step.val, List.getElem?_map]
    cases vs[i]? <;> cases vs[j]? <;> simp [h.sub]
  | double i =>
    simp only [Step.val, List.getElem?_map]
    cases vs[i]? <;> simp [h.add]
  | scale c i =>
    simp only [Step.val, List.getElem?_map]
    cases vs[i]? <;> simp [h.smul]
  | copy i => simp only [Step.val, List.getElem?_map]

theorem runSteps_map {o : LinOps α} {o' : LinOps β} {φ : α → β} (h : o.Hom o' φ)
    (steps : List Step) (vs : List α) :
    runSteps o' (vs.map φ) steps = (runSteps o vs steps).map φ := by
  induction steps generalizing vs with
  | nil => rfl
  | cons st r ih =>
    simp only [runSteps, Step.val_map h]
    rw [← ih]
    congr 1
    cases st.val o vs <;> simp

theorem pick_map (φ : α → β) (vs : List α) (outs : List Nat) :
    pick (vs.map φ) outs = (pick vs outs).map φ := by
  induction outs with
  | nil => rfl
  | cons i r ih =>
    simp only [pick, List.filterMap_cons, List.getElem?_map] at ih ⊢
    cases vs[i]? <;> simp [ih]

/-- A map commuting with the operations commutes with the outputs of a schedule. -/
theorem Sched.run_map {o : LinOps α} {o' : LinOps β} {φ : α → β} (h : o.Hom o' φ)
    (s : Sched) (ins : List α) : s.run o' (ins.map φ) = (s.run o ins).map φ := by
  simp only [Sched.run, runSteps_map h, pick_map]

/-! ## 3. Coefficient rows -/

/-- The entrywise sum of two coefficient rows, the shorter one extended by zeros. -/
def rowAdd : List Int → List Int → List Int
  | [], b => b
  | a, [] => a
  | x :: a, y :: b => (x + y) :: rowAdd a b

/-- The entrywise difference of two coefficient rows, the shorter one extended by
    zeros. -/
def rowSub : List Int → List Int → List Int
  | [], b => b.map fun y => -y
  | a, [] => a
  | x :: a, y :: b => (x - y) :: rowSub a b

theorem getD_rowAdd (a b : List Int) (j : Nat) :
    (rowAdd a b).getD j 0 = a.getD j 0 + b.getD j 0 := by
  induction a generalizing b j with
  | nil => simp [rowAdd]
  | cons x a ih =>
    cases b with
    | nil => simp [rowAdd]
    | cons y b =>
      cases j with
      | zero => simp [rowAdd]
      | succ j => simpa [rowAdd] using ih b j

theorem getD_rowSub (a b : List Int) (j : Nat) :
    (rowSub a b).getD j 0 = a.getD j 0 - b.getD j 0 := by
  induction a generalizing b j with
  | nil =>
    simp only [rowSub, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases b[j]? <;> simp
  | cons x a ih =>
    cases b with
    | nil => simp [rowSub]
    | cons y b =>
      cases j with
      | zero => simp [rowSub]
      | succ j => simpa [rowSub] using ih b j

theorem getD_rowScale (c : Int) (a : List Int) (j : Nat) :
    (a.map fun y => c * y).getD j 0 = c * a.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases a[j]? <;> simp

/-- The operations on coefficient rows, entrywise. -/
def rowOps : LinOps (List Int) where
  add := rowAdd
  sub := rowSub
  smul c a := a.map fun y => c * y

/-- The coefficient rows of the `n` inputs: row `i` is `1` at `i` and `0` elsewhere. -/
def unitRows (n : Nat) : List (List Int) :=
  List.ofFn fun i : Fin n => List.ofFn fun j : Fin n => if j = i then 1 else 0

/-- The value of a coefficient row at the inputs `x`. -/
def dot {R : Type u} [Ring R] {n : Nat} (x : Fin n → R) (row : List Int) : R :=
  ∑ j : Fin n, (row.getD j 0 : R) * x j

theorem getD_ofFn {n : Nat} (f : Fin n → Int) (j : Fin n) : (List.ofFn f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD]

/-- The value of a row is a map commuting with the operations. -/
theorem dot_hom {R : Type u} [Ring R] {n : Nat} (x : Fin n → R) :
    rowOps.Hom (ringOps R) (dot x) where
  add a b := by
    simp only [rowOps, ringOps, dot, getD_rowAdd, Int.cast_add, add_mul,
      Finset.sum_add_distrib]
  sub a b := by
    simp only [rowOps, ringOps, dot, getD_rowSub, Int.cast_sub, sub_mul,
      Finset.sum_sub_distrib]
  smul c a := by
    simp only [rowOps, ringOps, dot, getD_rowScale, Int.cast_mul, mul_assoc, Finset.mul_sum]

theorem unitRows_map_dot {R : Type u} [Ring R] {n : Nat} (x : Fin n → R) :
    (unitRows n).map (dot x) = List.ofFn x := by
  simp [unitRows, List.map_ofFn, Function.comp_def, dot]

/-! ## 4. The checker -/

/-- The rows of a matrix, as lists. -/
def rowsOf {m n : Nat} (M : Matrix (Fin m) (Fin n) Int) : List (List Int) :=
  List.ofFn fun i => List.ofFn fun j => M i j

/-- The coefficient rows of the outputs of a schedule over `n` inputs. -/
def Sched.rows (n : Nat) (s : Sched) : List (List Int) :=
  s.run rowOps (unitRows n)

/-- The checker: the coefficient rows of the outputs of `s` are the rows `M`. -/
def schedOk (n : Nat) (M : List (List Int)) (s : Sched) : Bool :=
  decide (s.rows n = M)

/-- The outputs of a schedule are the values of its coefficient rows. -/
theorem Sched.run_eq_rows {R : Type u} [Ring R] {n : Nat} (s : Sched) (x : Fin n → R) :
    s.run (ringOps R) (List.ofFn x) = (s.rows n).map (dot x) := by
  rw [Sched.rows, ← Sched.run_map (dot_hom x), unitRows_map_dot]

/-- **Soundness of the checker.** A schedule accepted for the matrix `M` computes
    `M` applied to the inputs, over every commutative ring and at every input
    vector. -/
theorem schedOk_sound {m n : Nat} {M : Matrix (Fin m) (Fin n) Int} {s : Sched}
    (h : schedOk n (rowsOf M) s = true) {R : Type u} [CommRing R] (x : Fin n → R) :
    s.run (ringOps R) (List.ofFn x) = List.ofFn ((M.map (Int.cast : Int → R)).mulVec x) := by
  rw [Sched.run_eq_rows, of_decide_eq_true h]
  simp only [rowsOf, List.map_ofFn, Function.comp_def, dot, getD_ofFn]
  congr 1

/-! ## 5. The program of a schedule

The program is in continuation form, as `FieldExprCompile.emit`: the continuation
receives the renaming into its context and the variables holding the results. A sum,
a difference and a doubling are one `fAdd` or `fSub` binding, a multiplication by a
constant is an `fConst` binding and an `fMul` binding, and a copy is an `fCopy`
binding. -/

section Lower

variable {p : Nat}

/-- A renaming of variables from `Γ` to `Γ'`. -/
abbrev Shift (Γ Γ' : Ctxt fieldDialect) : Type :=
  ∀ {t : FieldTy}, Ctxt.Var Γ t → Ctxt.Var Γ' t

/-- The values of the variables `env` under `V`. -/
def inputVars {Γ : Ctxt fieldDialect} (V : Ctxt.Valuation Γ)
    (env : List (Ctxt.Var Γ (.fp p))) : List (ZMod p) :=
  env.map fun v => v.lookup V

/-- The bindings of one step over the variables `env`, then the continuation on the
    renaming into its context and the variable holding the value of the step. -/
def Step.emit {t : FieldTy} (st : Step) {Γ : Ctxt fieldDialect}
    (env : List (Ctxt.Var Γ (.fp p)))
    (k : {Γ' : Ctxt fieldDialect} → Shift Γ Γ' → Option (Ctxt.Var Γ' (.fp p)) →
      Com fieldDialect Γ' t) : Com fieldDialect Γ t :=
  match st with
  | .add i j =>
    match env[i]?, env[j]? with
    | some a, some b =>
      .var ⟨.fAdd p, rfl, .cons a (.cons b .nil)⟩ (k (fun v => v.there) (some .here))
    | _, _ => k (fun v => v) none
  | .sub i j =>
    match env[i]?, env[j]? with
    | some a, some b =>
      .var ⟨.fSub p, rfl, .cons a (.cons b .nil)⟩ (k (fun v => v.there) (some .here))
    | _, _ => k (fun v => v) none
  | .double i =>
    match env[i]? with
    | some a => .var ⟨.fAdd p, rfl, .cons a (.cons a .nil)⟩ (k (fun v => v.there) (some .here))
    | none => k (fun v => v) none
  | .scale c i =>
    match env[i]? with
    | some a =>
      .var ⟨.fConst p (c : ZMod p), rfl, .nil⟩
        (.var ⟨.fMul p, rfl, .cons .here (.cons a.there .nil)⟩
          (k (fun v => v.there.there) (some .here)))
    | none => k (fun v => v) none
  | .copy i =>
    match env[i]? with
    | some a => .var ⟨.fCopy p, rfl, .cons a .nil⟩ (k (fun v => v.there) (some .here))
    | none => k (fun v => v) none

/-- **Denotation of `Step.emit`.** If the continuation denotes `R` whenever its
    renaming preserves values and its variable holds the value of the step, then the
    program of the step denotes `R`. -/
theorem Step.emit_denote {t : FieldTy} (st : Step) {Γ : Ctxt fieldDialect}
    (env : List (Ctxt.Var Γ (.fp p)))
    (k : {Γ' : Ctxt fieldDialect} → Shift Γ Γ' → Option (Ctxt.Var Γ' (.fp p)) →
      Com fieldDialect Γ' t)
    (V : Ctxt.Valuation Γ) (R : TyDenote.denote t)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (ρ : Shift Γ Γ') (V' : Ctxt.Valuation Γ')
      (w : Option (Ctxt.Var Γ' (.fp p))),
      (∀ {u : FieldTy} (v : Ctxt.Var Γ u), (ρ v).lookup V' = v.lookup V) →
      w.map (fun v => (v.lookup V' : ZMod p)) = st.val (ringOps (ZMod p)) (inputVars V env) →
      (k ρ w).denote V' = R) :
    (st.emit env k).denote V = R := by
  cases st with
  | add i j =>
    simp only [Step.emit, Step.val, inputVars, List.getElem?_map] at hk ⊢
    cases hi : env[i]? <;> cases hj : env[j]? <;> simp only [hi, hj] at hk ⊢
    all_goals first
      | exact hk _ V none (fun _ => rfl) rfl
      | exact hk _ _ (some .here) (fun _ => rfl) rfl
  | sub i j =>
    simp only [Step.emit, Step.val, inputVars, List.getElem?_map] at hk ⊢
    cases hi : env[i]? <;> cases hj : env[j]? <;> simp only [hi, hj] at hk ⊢
    all_goals first
      | exact hk _ V none (fun _ => rfl) rfl
      | exact hk _ _ (some .here) (fun _ => rfl) rfl
  | double i =>
    simp only [Step.emit, Step.val, inputVars, List.getElem?_map] at hk ⊢
    cases hi : env[i]? <;> simp only [hi] at hk ⊢
    all_goals first
      | exact hk _ V none (fun _ => rfl) rfl
      | exact hk _ _ (some .here) (fun _ => rfl) rfl
  | scale c i =>
    simp only [Step.emit, Step.val, inputVars, List.getElem?_map] at hk ⊢
    cases hi : env[i]? <;> simp only [hi] at hk ⊢
    all_goals first
      | exact hk _ V none (fun _ => rfl) rfl
      | exact hk _ _ (some .here) (fun _ => rfl) rfl
  | copy i =>
    simp only [Step.emit, Step.val, inputVars, List.getElem?_map] at hk ⊢
    cases hi : env[i]? <;> simp only [hi] at hk ⊢
    all_goals first
      | exact hk _ V none (fun _ => rfl) rfl
      | exact hk _ _ (some .here) (fun _ => rfl) rfl

/-- The bindings of the steps over the variables `env`, then the continuation on the
    renaming into its context and the variables holding all values. -/
def lowerSteps {t : FieldTy} : List Step → {Γ : Ctxt fieldDialect} →
    List (Ctxt.Var Γ (.fp p)) →
    ({Γ' : Ctxt fieldDialect} → Shift Γ Γ' → List (Ctxt.Var Γ' (.fp p)) →
      Com fieldDialect Γ' t) → Com fieldDialect Γ t
  | [], _, env, k => k (fun v => v) env
  | st :: r, _, env, k =>
    st.emit env fun ρ w =>
      lowerSteps r (env.map (fun v => ρ v) ++ w.toList) fun ρ' e => k (fun v => ρ' (ρ v)) e

/-- **Denotation of `lowerSteps`.** -/
theorem lowerSteps_denote {t : FieldTy} (steps : List Step) {Γ : Ctxt fieldDialect}
    (env : List (Ctxt.Var Γ (.fp p)))
    (k : {Γ' : Ctxt fieldDialect} → Shift Γ Γ' → List (Ctxt.Var Γ' (.fp p)) →
      Com fieldDialect Γ' t)
    (V : Ctxt.Valuation Γ) (R : TyDenote.denote t)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (ρ : Shift Γ Γ') (V' : Ctxt.Valuation Γ')
      (e : List (Ctxt.Var Γ' (.fp p))),
      (∀ {u : FieldTy} (v : Ctxt.Var Γ u), (ρ v).lookup V' = v.lookup V) →
      inputVars V' e = runSteps (ringOps (ZMod p)) (inputVars V env) steps →
      (k ρ e).denote V' = R) :
    (lowerSteps steps env k).denote V = R := by
  induction steps generalizing Γ with
  | nil => exact hk _ V env (fun _ => rfl) rfl
  | cons st r ih =>
    refine Step.emit_denote st env _ V R fun ρ V₁ w hρ hw => ?_
    refine ih _ _ V₁ fun ρ' V₂ e hρ' he => ?_
    refine hk _ V₂ e (fun v => (hρ' (ρ v)).trans (hρ v)) ?_
    rw [he, runSteps, ← hw]
    congr 1
    cases w <;> simp [inputVars, hρ]

/-- The program of a schedule over the input variables `env`, then the continuation
    on the renaming into its context and the variables holding the outputs. -/
def Sched.lower {t : FieldTy} (s : Sched) {Γ : Ctxt fieldDialect}
    (env : List (Ctxt.Var Γ (.fp p)))
    (k : {Γ' : Ctxt fieldDialect} → Shift Γ Γ' → List (Ctxt.Var Γ' (.fp p)) →
      Com fieldDialect Γ' t) : Com fieldDialect Γ t :=
  lowerSteps s.steps env fun ρ e => k ρ (pick e s.outs)

/-- **Denotation of the program of a schedule.** If the continuation denotes `R`
    whenever its renaming preserves values and its variables hold the outputs of the
    schedule, then the program denotes `R`. -/
theorem Sched.lower_denote {t : FieldTy} (s : Sched) {Γ : Ctxt fieldDialect}
    (env : List (Ctxt.Var Γ (.fp p)))
    (k : {Γ' : Ctxt fieldDialect} → Shift Γ Γ' → List (Ctxt.Var Γ' (.fp p)) →
      Com fieldDialect Γ' t)
    (V : Ctxt.Valuation Γ) (R : TyDenote.denote t)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (ρ : Shift Γ Γ') (V' : Ctxt.Valuation Γ')
      (e : List (Ctxt.Var Γ' (.fp p))),
      (∀ {u : FieldTy} (v : Ctxt.Var Γ u), (ρ v).lookup V' = v.lookup V) →
      inputVars V' e = s.run (ringOps (ZMod p)) (inputVars V env) →
      (k ρ e).denote V' = R) :
    (s.lower env k).denote V = R := by
  refine lowerSteps_denote s.steps env _ V R fun ρ V' e hρ he => ?_
  refine hk ρ V' _ hρ ?_
  rw [Sched.run, ← he, inputVars, inputVars, pick_map]

/-- **The program of an accepted schedule computes the matrix.** If the input
    variables hold `x` and the continuation denotes `R` whenever its renaming
    preserves values and its variables hold `M` applied to `x`, then the program
    denotes `R`. -/
theorem Sched.lower_linMap {t : FieldTy} {m n : Nat} {M : Matrix (Fin m) (Fin n) Int}
    {s : Sched} (h : schedOk n (rowsOf M) s = true) {Γ : Ctxt fieldDialect}
    (env : List (Ctxt.Var Γ (.fp p)))
    (k : {Γ' : Ctxt fieldDialect} → Shift Γ Γ' → List (Ctxt.Var Γ' (.fp p)) →
      Com fieldDialect Γ' t)
    (V : Ctxt.Valuation Γ) (R : TyDenote.denote t) (x : Fin n → ZMod p)
    (hx : inputVars V env = List.ofFn x)
    (hk : ∀ {Γ' : Ctxt fieldDialect} (ρ : Shift Γ Γ') (V' : Ctxt.Valuation Γ')
      (e : List (Ctxt.Var Γ' (.fp p))),
      (∀ {u : FieldTy} (v : Ctxt.Var Γ u), (ρ v).lookup V' = v.lookup V) →
      inputVars V' e = List.ofFn ((M.map (Int.cast : Int → ZMod p)).mulVec x) →
      (k ρ e).denote V' = R) :
    (s.lower env k).denote V = R := by
  refine Sched.lower_denote s env k V R fun ρ V' e hρ he => hk ρ V' e hρ ?_
  rw [he, hx, schedOk_sound h]

end Lower

/-! ## 6. Operation count -/

/-- The modular operations of a step: one for a sum, a difference, a doubling and a
    multiplication by a constant, none for a copy. -/
def Step.cost : Step → Nat
  | .add _ _ => 1
  | .sub _ _ => 1
  | .double _ => 1
  | .scale _ _ => 1
  | .copy _ => 0

/-- The modular operations of a schedule. -/
def Sched.cost (s : Sched) : Nat :=
  (s.steps.map Step.cost).sum

/-! ## 7. The matrices of Poseidon2

`mdsQuad` is the 4 × 4 matrix with rows `(2,3,1,1)`, `(1,2,3,1)`, `(1,1,2,3)`,
`(3,1,1,2)`. `mdsExternal` is the 16 × 16 matrix of the external layer at width 16:
its 4 × 4 block at block row `a` and block column `b` is `2 · mdsQuad` for `a = b`
and `mdsQuad` otherwise. -/

/-- Entry `(i, j)` of the 4 × 4 matrix of Poseidon2, for `i, j < 4`. -/
def quadEntry (i j : Nat) : Int :=
  ([[2, 3, 1, 1], [1, 2, 3, 1], [1, 1, 2, 3], [3, 1, 1, 2]].getD i []).getD j 0

/-- The 4 × 4 matrix of Poseidon2. -/
def mdsQuad : Matrix (Fin 4) (Fin 4) Int :=
  Matrix.of fun i j => quadEntry i j

/-- The 16 × 16 external matrix of Poseidon2 at width 16. -/
def mdsExternal : Matrix (Fin 16) (Fin 16) Int :=
  Matrix.of fun i j =>
    (if i.val / 4 = j.val / 4 then 2 else 1) * quadEntry (i.val % 4) (j.val % 4)

/-- The steps of the 4 × 4 schedule on the inputs `inp, …, inp + 3`, its values at
    `base, …, base + 10`: seven sums, two doublings and two further sums. -/
def quadSteps (inp base : Nat) : List Step :=
  [ .add inp (inp + 1),            -- base      : x0 + x1
    .add (inp + 2) (inp + 3),      -- base + 1  : x2 + x3
    .add base (base + 1),          -- base + 2  : x0 + x1 + x2 + x3
    .add (base + 2) (inp + 1),     -- base + 3  : x0 + 2 x1 + x2 + x3
    .add (base + 2) (inp + 3),     -- base + 4  : x0 + x1 + x2 + 2 x3
    .double inp,                   -- base + 5  : 2 x0
    .double (inp + 2),             -- base + 6  : 2 x2
    .add (base + 4) (base + 5),    -- base + 7  : row 3
    .add (base + 3) (base + 6),    -- base + 8  : row 1
    .add (base + 3) base,          -- base + 9  : row 0
    .add (base + 4) (base + 1) ]   -- base + 10 : row 2

/-- The offset from `base` of row `c` of the 4 × 4 schedule. -/
def quadOut : Nat → Nat
  | 0 => 9
  | 1 => 8
  | 2 => 10
  | _ => 7

/-- The schedule of the 4 × 4 matrix. -/
def quadSched : Sched where
  steps := quadSteps 0 4
  outs := (List.range 4).map fun c => 4 + quadOut c

/-- The index of entry `c` of chunk `a` after the 4 × 4 schedules of the external
    schedule. -/
def chunkOut (a c : Nat) : Nat := 16 + 11 * a + quadOut c

/-- The schedule of the 16 × 16 external matrix: the 4 × 4 schedule on each of the
    four chunks (values `16, …, 59`), the four column sums (three sums each, column
    `c` at `62 + 3 c`), and the sum of each entry with its column sum (values
    `72, …, 87`). -/
def externalSched : Sched where
  steps :=
    ((List.range 4).flatMap fun a => quadSteps (4 * a) (16 + 11 * a)) ++
    ((List.range 4).flatMap fun c =>
      [ .add (chunkOut 0 c) (chunkOut 1 c),
        .add (chunkOut 2 c) (chunkOut 3 c),
        .add (60 + 3 * c) (61 + 3 * c) ]) ++
    ((List.range 16).map fun i => .add (chunkOut (i / 4) (i % 4)) (62 + 3 * (i % 4)))
  outs := (List.range 16).map fun i => 72 + i

/-- The checker accepts the 4 × 4 schedule. -/
theorem quadSched_ok : schedOk 4 (rowsOf mdsQuad) quadSched = true := by decide

/-- The 4 × 4 schedule has 11 modular operations. -/
theorem quadSched_cost : quadSched.cost = 11 := by decide

/-- The 4 × 4 schedule computes `mdsQuad`, over every commutative ring. -/
theorem quadSched_run {R : Type u} [CommRing R] (x : Fin 4 → R) :
    quadSched.run (ringOps R) (List.ofFn x) =
      List.ofFn ((mdsQuad.map (Int.cast : Int → R)).mulVec x) :=
  schedOk_sound quadSched_ok x

/-- The checker accepts the external schedule. -/
theorem externalSched_ok : schedOk 16 (rowsOf mdsExternal) externalSched = true := by
  decide +kernel

/-- The external schedule has 72 modular operations. -/
theorem externalSched_cost : externalSched.cost = 72 := by decide

/-- The external schedule computes `mdsExternal`, over every commutative ring. -/
theorem externalSched_run {R : Type u} [CommRing R] (x : Fin 16 → R) :
    externalSched.run (ringOps R) (List.ofFn x) =
      List.ofFn ((mdsExternal.map (Int.cast : Int → R)).mulVec x) :=
  schedOk_sound externalSched_ok x

end CatCrypt.Crypto.SecureCompilation.VIR.LinMapSchedule
