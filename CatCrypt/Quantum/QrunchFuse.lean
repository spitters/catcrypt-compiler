/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QrunchBasis
import Std.Data.TreeMap.Lemmas

/-!
# Exact fusion of one-qubit statements in the basis `{rx, ry, rz, cx, p}`

`fuseQ` scans a list of OpenQASM 2 statements and keeps, for each qubit, at most one
pending rotation `rx`, `ry`, `rz` or `p` with an exact angle. A rotation about the axis of
the pending one on its qubit is merged into it by adding the angles; a rotation about
another axis emits the pending one first. Pending rotations wait past statements on other
qubits. A `cx` emits the pending rotation on its target unless it is an `rx`, and the
one on its control unless it is diagonal (`p` or `rz`); every other statement emits all
pending rotations. An
emitted rotation is dropped when its matrix is the identity: angle zero, or a `p` whose
angle is a multiple of `2π`.

All rewrites are exact: rotations about one axis compose by adding angles, rotations on
distinct qubits commute, a diagonal rotation on the control of a `cx` commutes with it, and
an `rx` on its target commutes with it, since `rx` commutes with `X`.

## Main results

* `fuseQ` — the pass.
* `qelibListMatrix_fuseQ` — `qelibListMatrix (fuseQ l) = qelibListMatrix l`.
* `length_fuseQ_le` — the pass emits at most as many statements as it reads.
* `cxCount_fuseQ` — it emits exactly the `cx` statements it reads.
* `pauliQ` — the one-qubit Clifford frame pass: rotations by multiples of `π/2` are multiplied
  into a pending Clifford per qubit, kept as a shortest word of at most two rotations, and other
  rotations are emitted conjugated through it; `qelibListMatrix_pauliQ` (exact up to the phase
  it returns), `length_pauliQ_le`, `cxCount_pauliQ`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.OpenQASMImport
open CatCrypt.Quantum.OpenQASMImportGates
open CatCrypt.Quantum.Qelib
open CatCrypt.Quantum.ControlledGates (ctrlMatrix proj0 proj1 embedGate2_cnot)
open CatCrypt.Quantum.Programs.Qubit (pauliX)
open CatCrypt.Quantum.Synthesis.KAK (exp_I_mul_ofReal)

namespace CatCrypt.Quantum.QrunchFuse

variable {n : ℕ}

/-! ## Axes and their rotations -/

/-- The axis of a one-qubit rotation statement: `rx`, `ry`, `rz` or `p`. -/
inductive Axis where
  | x
  | y
  | z
  | p
  deriving DecidableEq, Repr

/-- The `2 × 2` matrix of the rotation by `θ` about an axis, as `qelib1.inc` defines it. -/
noncomputable def axisMat : Axis → ℝ → Matrix (Fin 2) (Fin 2) ℂ
  | .x, θ => rxMatrix θ
  | .y, θ => ryMatrix θ
  | .z, θ => rzMatrix θ
  | .p, θ => rzGate θ

/-- The rotation statement about an axis on a qubit. -/
def mkQ : Axis → Fin n → PiLin → QGate n
  | .x, q, a => .rx q a
  | .y, q, a => .ry q a
  | .z, q, a => .rz q a
  | .p, q, a => .p q a

/-- The qubit, axis and angle of a rotation statement; `none` for every other statement. -/
def axis? : QGate n → Option (Fin n × Axis × PiLin)
  | .rx q a => some (q, .x, a)
  | .ry q a => some (q, .y, a)
  | .rz q a => some (q, .z, a)
  | .p q a => some (q, .p, a)
  | _ => none

/-- A statement with an axis is the rotation statement of that axis. -/
theorem eq_mkQ_of_axis? {g : QGate n} {q : Fin n} {A : Axis} {a : PiLin}
    (h : axis? g = some (q, A, a)) : g = mkQ A q a := by
  cases g <;> simp only [axis?, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl, rfl⟩ := h <;> rfl

/-- The matrix of a rotation statement. -/
theorem qelibMatrix_mkQ (A : Axis) (q : Fin n) (a : PiLin) :
    qelibMatrix (mkQ A q a) = embedGate1 n q (axisMat A a.toReal) := by
  cases A <;> rfl

/-! ## Two-by-two identities -/

/-- `rx` is additive in its angle. -/
theorem rxMatrix_add (x y : ℝ) : rxMatrix (x + y) = rxMatrix x * rxMatrix y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rxMatrix, Matrix.mul_apply, Fin.sum_univ_two, add_div, Real.cos_add, Real.sin_add] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

/-- `ry` is additive in its angle. -/
theorem ryMatrix_add (x y : ℝ) : ryMatrix (x + y) = ryMatrix x * ryMatrix y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ryMatrix, Matrix.mul_apply, Fin.sum_univ_two, add_div, Real.cos_add, Real.sin_add] <;>
    ring

/-- `rz` is additive in its angle. -/
theorem rzMatrix_add (x y : ℝ) : rzMatrix (x + y) = rzMatrix x * rzMatrix y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rzMatrix, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add] <;> ring_nf

/-- `p` is additive in its angle. -/
theorem rzGate_add (x y : ℝ) : rzGate (x + y) = rzGate x * rzGate y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rzGate, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add]
  ring_nf

/-- A rotation is additive in its angle. -/
theorem axisMat_add (A : Axis) (x y : ℝ) : axisMat A (x + y) = axisMat A x * axisMat A y := by
  cases A
  · exact rxMatrix_add x y
  · exact ryMatrix_add x y
  · exact rzMatrix_add x y
  · exact rzGate_add x y

/-- The rotation by zero is the identity. -/
theorem axisMat_zero (A : Axis) : axisMat A 0 = 1 := by
  cases A <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [axisMat, rxMatrix, ryMatrix, rzMatrix, rzGate]

/-- `p(2kπ)` is the identity. -/
theorem rzGate_int_mul_two_pi (k : ℤ) : rzGate ((k : ℝ) * (2 * Real.pi)) = 1 := by
  have h : Complex.exp (Complex.I * ((k : ℂ) * (2 * (Real.pi : ℂ)))) = 1 := by
    rw [← Complex.exp_int_mul_two_pi_mul_I k]
    congr 1
    ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rzGate, h]

/-! ## Rotations that are the identity -/

/-- The rotation about `A` by `a` is recognised as the identity: `a = 0`, or `A = p` and `a`
is an even multiple of `π`. -/
def isId (A : Axis) (a : PiLin) : Bool :=
  decide (a = 0) || (decide (A = .p) && decide (a.a = 0) && decide ((a.b / 2).den = 1))

/-- A rotation recognised as the identity has the identity matrix. -/
theorem axisMat_of_isId {A : Axis} {a : PiLin} (h : isId A a = true) :
    axisMat A a.toReal = 1 := by
  simp only [isId, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨⟨rfl, ha⟩, hb⟩
  · subst h
    simp [axisMat_zero]
  · have hk : a.b = (((a.b / 2).num : ℚ)) * 2 := by
      rw [Rat.coe_int_num_of_den_eq_one hb]
      ring
    obtain ⟨m, hm⟩ : ∃ m : ℤ, a.b = m * 2 := ⟨_, hk⟩
    have : a.toReal = (m : ℝ) * (2 * Real.pi) := by
      rw [PiLin.toReal, ha, hm]
      push_cast
      ring
    rw [axisMat, this, rzGate_int_mul_two_pi]

/-! ## Pending rotations -/

/-- A pending rotation on a qubit: an axis and an angle, or none. -/
abbrev Pend := Option (Axis × PiLin)

/-- The matrix of the pending rotation on qubit `q`. -/
noncomputable def entryMat (q : Fin n) : Pend → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | none => 1
  | some (A, a) => embedGate1 n q (axisMat A a.toReal)

/-- The statements that emit the pending rotation on qubit `q`: none when it is absent or
recognised as the identity. -/
def emit (q : Fin n) : Pend → List (QGate n)
  | none => []
  | some (A, a) => if isId A a then [] else [mkQ A q a]

/-- The emitted statements realise the pending rotation. -/
theorem qelibListMatrix_emit (q : Fin n) (e : Pend) :
    qelibListMatrix (emit q e) = entryMat q e := by
  rcases e with _ | ⟨A, a⟩
  · rfl
  · by_cases h : isId A a = true
    · simp [emit, h, entryMat, qelibListMatrix, axisMat_of_isId h, embedGate1_one]
    · simp [emit, h, entryMat, qelibListMatrix, qelibMatrix_mkQ]

/-- Pending rotations on distinct qubits commute. -/
theorem commute_entryMat {i q : Fin n} (h : i ≠ q) (e e' : Pend) :
    Commute (entryMat q e) (entryMat i e') := by
  rcases e with _ | ⟨A, a⟩
  · exact Commute.one_left _
  rcases e' with _ | ⟨B, b⟩
  · exact Commute.one_right _
  exact Optimization.DisjointCommute.embedGate1_disjoint_comm (Ne.symm h) _ _

/-- The weight of a pending rotation: one if present. -/
def wt : Pend → ℕ
  | none => 0
  | some _ => 1

/-- At most one statement is emitted for a pending rotation. -/
theorem length_emit_le (q : Fin n) (e : Pend) : (emit q e).length ≤ wt e := by
  rcases e with _ | ⟨A, a⟩
  · simp [emit, wt]
  · by_cases h : isId A a = true <;> simp [emit, wt, h]

/-! ## Scan states -/

/-- The pending rotations of a state, qubit by qubit. -/
def stF (v : Vector Pend n) (q : Fin n) : Pend := v[q]

/-- The function `F` with value `x` at `q`. -/
def setF (q : Fin n) (x : Pend) (F : Fin n → Pend) (p : Fin n) : Pend :=
  if p = q then x else F p

/-- The state `v` with value `x` at `q`, updated in place. -/
def setQ (v : Vector Pend n) (q : Fin n) (x : Pend) : Vector Pend n :=
  v.set q x

/-- The pending rotations of an updated state. -/
theorem stF_setQ (v : Vector Pend n) (q : Fin n) (x : Pend) :
    stF (setQ v q x) = setF q x (stF v) := by
  funext p
  simp only [stF, setQ, setF]
  grind

/-- The empty state has no pending rotation. -/
theorem stF_replicate : stF (Vector.replicate n (none : Pend)) = fun _ => none := by
  funext p
  simp [stF]

/-- `setF q x F` takes the value `x` at `q`. -/
theorem setF_self (q : Fin n) (x : Pend) (F : Fin n → Pend) : setF q x F q = x := by
  simp [setF]

/-- The later of two updates at one qubit wins. -/
theorem setF_setF_self (q : Fin n) (x y : Pend) (F : Fin n → Pend) :
    setF q x (setF q y F) = setF q x F := by
  funext p
  simp only [setF]
  grind

/-- Updates at distinct qubits commute. -/
theorem setF_comm {c t : Fin n} (h : c ≠ t) (x y : Pend) (F : Fin n → Pend) :
    setF c x (setF t y F) = setF t y (setF c x F) := by
  funext p
  simp only [setF]
  grind

/-- The statements emitting the pending rotations `F q` for the qubits `q` of `L`. -/
def flushOn (F : Fin n → Pend) (L : List (Fin n)) : List (QGate n) :=
  L.flatMap fun q => emit q (F q)

/-- The product of the pending rotations `F q` for the qubits `q` of `L`, head applied
first. -/
noncomputable def prodOn (F : Fin n → Pend) :
    List (Fin n) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ
  | [] => 1
  | q :: L => prodOn F L * entryMat q (F q)

/-- The number of pending rotations `F q` for the qubits `q` of `L`. -/
def sizeOn (F : Fin n → Pend) : List (Fin n) → ℕ
  | [] => 0
  | q :: L => sizeOn F L + wt (F q)

/-- The flushed statements realise the product of the pending rotations. -/
theorem qelibListMatrix_flushOn (F : Fin n → Pend) (L : List (Fin n)) :
    qelibListMatrix (flushOn F L) = prodOn F L := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    rw [flushOn, List.flatMap_cons, QrunchBasis.qelibListMatrix_append, ← flushOn, ih,
      qelibListMatrix_emit, prodOn]

/-- At most one statement is flushed per pending rotation. -/
theorem length_flushOn_le (F : Fin n → Pend) (L : List (Fin n)) :
    (flushOn F L).length ≤ sizeOn F L := by
  induction L with
  | nil => simp [flushOn, sizeOn]
  | cons q L ih =>
    have := length_emit_le q (F q)
    simp only [flushOn, List.flatMap_cons, List.length_append, sizeOn] at ih ⊢
    omega

/-- No pending rotations multiply to the identity. -/
theorem prodOn_none (L : List (Fin n)) : prodOn (fun _ => none) L = 1 := by
  induction L with
  | nil => rfl
  | cons q L ih => simp [prodOn, ih, entryMat]

/-- No pending rotations count zero. -/
theorem sizeOn_none (L : List (Fin n)) : sizeOn (fun _ => none) L = 0 := by
  induction L with
  | nil => rfl
  | cons q L ih => simp [sizeOn, ih, wt]

/-- The product depends only on the pending rotations of the qubits of `L`. -/
theorem prodOn_congr {F G : Fin n → Pend} {L : List (Fin n)} (h : ∀ i ∈ L, F i = G i) :
    prodOn F L = prodOn G L := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    simp only [prodOn, h q (by simp), ih (fun i hi => h i (by simp [hi]))]

/-- The count depends only on the pending rotations of the qubits of `L`. -/
theorem sizeOn_congr {F G : Fin n → Pend} {L : List (Fin n)} (h : ∀ i ∈ L, F i = G i) :
    sizeOn F L = sizeOn G L := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    simp only [sizeOn, h q (by simp), ih (fun i hi => h i (by simp [hi]))]

/-- A matrix commuting with each pending rotation commutes with their product. -/
theorem commute_prodOn {X : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} {F : Fin n → Pend}
    {L : List (Fin n)} (h : ∀ i ∈ L, Commute X (entryMat i (F i))) :
    Commute X (prodOn F L) := by
  induction L with
  | nil => exact Commute.one_right _
  | cons q L ih =>
    exact (ih (fun i hi => h i (by simp [hi]))).mul_right (h q (by simp))

/-- A rotation on `q` commutes with the pending rotations once `q` is cleared. -/
theorem commute_prodOn_setF_none (q : Fin n) (e : Pend) (F : Fin n → Pend)
    (L : List (Fin n)) : Commute (entryMat q e) (prodOn (setF q none F) L) := by
  refine commute_prodOn fun i _ => ?_
  by_cases hi : i = q
  · subst hi
    rw [setF_self]
    exact Commute.one_right _
  · exact commute_entryMat hi _ _

/-- The pending rotation on `q` factors out of the product, applied first. -/
theorem prodOn_extract (F : Fin n → Pend) {q : Fin n} {L : List (Fin n)} (hL : L.Nodup)
    (hq : q ∈ L) : prodOn F L = prodOn (setF q none F) L * entryMat q (F q) := by
  induction L with
  | nil => simp at hq
  | cons i L ih =>
    rw [List.nodup_cons] at hL
    by_cases hi : i = q
    · subst hi
      have hc : prodOn F L = prodOn (setF i none F) L :=
        prodOn_congr fun p hp => by
          have : p ≠ i := fun h => hL.1 (h ▸ hp)
          simp [setF, this]
      simp [prodOn, hc, setF_self, entryMat]
    · have hq' : q ∈ L := by
        rcases List.mem_cons.mp hq with h | h
        · exact absurd h.symm hi
        · exact h
      rw [prodOn, ih hL.2 hq', prodOn, mul_assoc, mul_assoc,
        (commute_entryMat hi (F q) (F i)).eq]
      simp [setF, hi]

/-- The pending rotation on `q` contributes its weight to the count. -/
theorem sizeOn_extract (F : Fin n → Pend) {q : Fin n} {L : List (Fin n)} (hL : L.Nodup)
    (hq : q ∈ L) : sizeOn F L = sizeOn (setF q none F) L + wt (F q) := by
  induction L with
  | nil => simp at hq
  | cons i L ih =>
    rw [List.nodup_cons] at hL
    by_cases hi : i = q
    · subst hi
      have hc : sizeOn F L = sizeOn (setF i none F) L :=
        sizeOn_congr fun p hp => by
          have : p ≠ i := fun h => hL.1 (h ▸ hp)
          simp [setF, this]
      simp [sizeOn, hc, setF_self, wt]
    · have hq' : q ∈ L := by
        rcases List.mem_cons.mp hq with h | h
        · exact absurd h.symm hi
        · exact h
      rw [sizeOn, ih hL.2 hq', sizeOn]
      simp only [setF, hi, ite_false]
      omega

/-- The product over all qubits after setting the rotation on `q` to `x`. -/
theorem prodOn_setF (F : Fin n → Pend) (q : Fin n) (x : Pend) :
    prodOn (setF q x F) (List.finRange n)
      = prodOn (setF q none F) (List.finRange n) * entryMat q x := by
  rw [prodOn_extract _ (List.nodup_finRange n) (List.mem_finRange q), setF_setF_self,
    setF_self]

/-- The count over all qubits after setting the rotation on `q` to `x`. -/
theorem sizeOn_setF (F : Fin n → Pend) (q : Fin n) (x : Pend) :
    sizeOn (setF q x F) (List.finRange n)
      = sizeOn (setF q none F) (List.finRange n) + wt x := by
  rw [sizeOn_extract _ (List.nodup_finRange n) (List.mem_finRange q), setF_setF_self,
    setF_self]

/-! ## Diagonal rotations on the control of a `cx` -/

/-- The part of a pending rotation that passes the control of a `cx`: a `p` or an `rz`. -/
def ctrlKeep : Pend → Pend
  | some (.p, a) => some (.p, a)
  | some (.z, a) => some (.z, a)
  | _ => none

/-- The part of a pending rotation that a `cx` on its control emits. -/
def ctrlEmit : Pend → Pend
  | some (.p, _) => none
  | some (.z, _) => none
  | e => e

/-- A pending rotation is its kept part after its emitted part. -/
theorem entryMat_ctrl (c : Fin n) (e : Pend) :
    entryMat c e = entryMat c (ctrlKeep e) * entryMat c (ctrlEmit e) := by
  rcases e with _ | ⟨_ | _ | _ | _, a⟩ <;> simp [ctrlKeep, ctrlEmit, entryMat]

/-- The weight of a pending rotation splits into its kept and emitted parts. -/
theorem wt_ctrl (e : Pend) : wt e = wt (ctrlKeep e) + wt (ctrlEmit e) := by
  rcases e with _ | ⟨_ | _ | _ | _, a⟩ <;> simp [ctrlKeep, ctrlEmit, wt]

/-- A rotation on `c` commuting with both projections on `c` commutes with `cx c t`. -/
theorem commute_cx_embedGate1 {c t : Fin n} (hct : c ≠ t) {D : Matrix (Fin 2) (Fin 2) ℂ}
    (h0 : D * proj0 = proj0 * D) (h1 : D * proj1 = proj1 * D) :
    Commute (qelibMatrix (QGate.cx c t)) (embedGate1 n c D) := by
  have hcx : qelibMatrix (QGate.cx c t) = ctrlMatrix c (embedGate1 n t pauliX) := by
    simp [qelibMatrix, gateEmbedding, hct, embedGate2_cnot hct]
  have hX : embedGate1 n t pauliX * embedGate1 n c D = embedGate1 n c D * embedGate1 n t pauliX :=
    Optimization.DisjointCommute.embedGate1_disjoint_comm (Ne.symm hct) _ _
  rw [hcx]
  refine (?_ : embedGate1 n c D * _ = _ * embedGate1 n c D).symm
  simp only [ctrlMatrix, mul_add, add_mul, mul_assoc, hX]
  simp only [← mul_assoc, embedGate1_mul, h0, h1]

/-- The kept part of a rotation on the control of a `cx` commutes with it. -/
theorem commute_cx_ctrlKeep {c t : Fin n} (hct : c ≠ t) (e : Pend) :
    Commute (qelibMatrix (QGate.cx c t)) (entryMat c (ctrlKeep e)) := by
  rcases e with _ | ⟨_ | _ | _ | _, a⟩ <;> simp only [ctrlKeep, entryMat]
  all_goals first
    | exact Commute.one_right _
    | refine commute_cx_embedGate1 hct ?_ ?_ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [axisMat, rzGate, rzMatrix, proj0, proj1, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## `rx` rotations on the target of a `cx` -/

/-- The part of a pending rotation that passes the target of a `cx`: an `rx`. -/
def tgtKeep : Pend → Pend
  | some (.x, a) => some (.x, a)
  | _ => none

/-- The part of a pending rotation that a `cx` on its target emits. -/
def tgtEmit : Pend → Pend
  | some (.x, _) => none
  | e => e

/-- A pending rotation is its kept part after its emitted part. -/
theorem entryMat_tgt (t : Fin n) (e : Pend) :
    entryMat t e = entryMat t (tgtKeep e) * entryMat t (tgtEmit e) := by
  rcases e with _ | ⟨_ | _ | _ | _, a⟩ <;> simp [tgtKeep, tgtEmit, entryMat]

/-- The weight of a pending rotation splits into its kept and emitted parts. -/
theorem wt_tgt (e : Pend) : wt e = wt (tgtKeep e) + wt (tgtEmit e) := by
  rcases e with _ | ⟨_ | _ | _ | _, a⟩ <;> simp [tgtKeep, tgtEmit, wt]

/-- A rotation on `t` commuting with `X` commutes with `cx c t`. -/
theorem commute_cx_embedGate1_tgt {c t : Fin n} (hct : c ≠ t) {D : Matrix (Fin 2) (Fin 2) ℂ}
    (hD : D * pauliX = pauliX * D) :
    Commute (qelibMatrix (QGate.cx c t)) (embedGate1 n t D) := by
  have hcx : qelibMatrix (QGate.cx c t) = ctrlMatrix c (embedGate1 n t pauliX) := by
    simp [qelibMatrix, gateEmbedding, hct, embedGate2_cnot hct]
  have h0 : embedGate1 n t D * embedGate1 n c proj0 = embedGate1 n c proj0 * embedGate1 n t D :=
    Optimization.DisjointCommute.embedGate1_disjoint_comm (Ne.symm hct) _ _
  have h1 : embedGate1 n t D * embedGate1 n c proj1 = embedGate1 n c proj1 * embedGate1 n t D :=
    Optimization.DisjointCommute.embedGate1_disjoint_comm (Ne.symm hct) _ _
  rw [hcx]
  refine (?_ : embedGate1 n t D * _ = _ * embedGate1 n t D).symm
  rw [ctrlMatrix, mul_add, add_mul, h0, ← mul_assoc, h1, mul_assoc, mul_assoc, embedGate1_mul,
    embedGate1_mul, hD]

/-- The kept part of a rotation on the target of a `cx` commutes with it. -/
theorem commute_cx_tgtKeep {c t : Fin n} (hct : c ≠ t) (e : Pend) :
    Commute (qelibMatrix (QGate.cx c t)) (entryMat t (tgtKeep e)) := by
  rcases e with _ | ⟨_ | _ | _ | _, a⟩ <;> simp only [tgtKeep, entryMat]
  all_goals first
    | exact Commute.one_right _
    | refine commute_cx_embedGate1_tgt hct ?_
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [axisMat, rxMatrix, pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- A rotation on a qubit outside a `cx` commutes with it. -/
theorem commute_cx_entryMat {c t i : Fin n} (hct : c ≠ t) (hic : i ≠ c) (hit : i ≠ t)
    (e : Pend) : Commute (qelibMatrix (QGate.cx c t)) (entryMat i e) := by
  rcases e with _ | ⟨A, a⟩
  · exact Commute.one_right _
  · have : qelibMatrix (QGate.cx c t) = embedGate2 n c t Programs.Qubit.cnot hct := by
      simp [qelibMatrix, gateEmbedding, hct]
    rw [this]
    exact (Optimization.MixedCommute.embedGate1_embedGate2_disjoint_comm hic hit hct _ _).symm

/-- The unfolding of `entryMat` at a present rotation. -/
theorem entryMat_some (q : Fin n) (A : Axis) (a : PiLin) :
    entryMat q (some (A, a)) = embedGate1 n q (axisMat A a.toReal) := rfl

/-- Two pending rotations about one axis merge by adding the angles. -/
theorem entryMat_merge (q : Fin n) (A : Axis) (a b : PiLin) :
    entryMat q (some (A, b + a)) = entryMat q (some (A, a)) * entryMat q (some (A, b)) := by
  rw [entryMat_some, entryMat_some, entryMat_some, PiLin.toReal_add, add_comm, axisMat_add,
    embedGate1_mul]

/-! ## The scan -/

/-- The statements a scan step emits for one input statement, and the next state. -/
def step (v : Vector Pend n) (g : QGate n) : List (QGate n) × Vector Pend n :=
  match axis? g with
  | some (q, A, a) =>
    match v[q] with
    | some (B, b) =>
      if A = B then ([], setQ v q (some (A, b + a)))
      else (emit q (some (B, b)), setQ v q (some (A, a)))
    | none => ([], setQ v q (some (A, a)))
  | none =>
    match g with
    | .cx c t =>
      if c = t then (flushOn (stF v) (List.finRange n) ++ [g], Vector.replicate n none)
      else (emit t (tgtEmit v[t]) ++ emit c (ctrlEmit v[c]) ++ [g],
        setQ (setQ v t (tgtKeep v[t])) c (ctrlKeep v[c]))
    | _ => (flushOn (stF v) (List.finRange n) ++ [g], Vector.replicate n none)

/-- The scan from state `v`; at the end every pending rotation is emitted. -/
def fuseAux : Vector Pend n → List (QGate n) → List (QGate n)
  | v, [] => flushOn (stF v) (List.finRange n)
  | v, g :: gs =>
    let s := step v g
    s.1 ++ fuseAux s.2 gs

/-- Exact fusion of the one-qubit rotation statements of a statement list. -/
def fuseQ (l : List (QGate n)) : List (QGate n) := fuseAux (Vector.replicate n none) l

/-! ## The scan preserves the matrix -/

/-- One scan step: the next pending rotations after the emitted statements realise the
input statement after the pending rotations. -/
theorem step_spec (v : Vector Pend n) (g : QGate n) :
    prodOn (stF (step v g).2) (List.finRange n) * qelibListMatrix (step v g).1
      = qelibMatrix g * prodOn (stF v) (List.finRange n) := by
  have hL := List.nodup_finRange n
  unfold step
  split
  · next q A a hg =>
    rw [eq_mkQ_of_axis? hg, qelibMatrix_mkQ, ← entryMat_some]
    have hc := commute_prodOn_setF_none q (some (A, a)) (stF v) (List.finRange n)
    have hx := prodOn_extract (stF v) hL (List.mem_finRange q)
    split
    · next B b hv =>
      have hv' : stF v q = some (B, b) := hv
      split
      · next hAB =>
        subst hAB
        rw [qelibListMatrix, mul_one, stF_setQ, prodOn_setF, hx, hv', entryMat_merge,
          ← mul_assoc, ← mul_assoc, hc.eq]
      · rw [stF_setQ, prodOn_setF, qelibListMatrix_emit, hx, hv', ← mul_assoc, hc.eq]
    · next hv =>
      have hv' : stF v q = none := hv
      rw [qelibListMatrix, mul_one, stF_setQ, prodOn_setF, hx, hv', entryMat, mul_one, hc.eq]
  · next hg =>
    split
    · next c t =>
      split
      · simp [stF_replicate, prodOn_none, QrunchBasis.qelibListMatrix_append, qelibListMatrix,
          qelibListMatrix_flushOn]
      · next hct =>
        set F := stF v
        have hF : stF (setQ (setQ v t (tgtKeep v[t])) c (ctrlKeep v[c]))
            = setF c (ctrlKeep (F c)) (setF t (tgtKeep (F t)) F) := by
          rw [stF_setQ, stF_setQ]; rfl
        have hxc := prodOn_extract F hL (List.mem_finRange c)
        have hxt := prodOn_extract (setF c none F) hL (List.mem_finRange t)
        have htc : setF c none F t = F t := by simp [setF, Ne.symm hct]
        rw [htc] at hxt
        have hR := setF_comm hct none (tgtKeep (F t)) F
        set R2 := prodOn (setF t none (setF c none F)) (List.finRange n)
        set CX := qelibMatrix (QGate.cx c t)
        have hR2 : Commute CX R2 := commute_prodOn fun i _ => by
          by_cases hic : i = c
          · subst hic; simp [setF, entryMat]
          · by_cases hit : i = t
            · subst hit; simp [setF, entryMat]
            · exact commute_cx_entryMat hct hic hit _
        have hK : Commute CX _ := commute_cx_ctrlKeep hct (F c)
        have hKt : Commute CX _ := commute_cx_tgtKeep hct (F t)
        have hce := commute_entryMat (Ne.symm hct) (F c) (tgtEmit (F t))
        have hsplit := entryMat_ctrl c (F c)
        have htsplit := entryMat_tgt t (F t)
        rw [hF, prodOn_setF _ c, hR, prodOn_setF (setF c none F) t, hxc, hxt,
          QrunchBasis.qelibListMatrix_append, QrunchBasis.qelibListMatrix_append,
          qelibListMatrix_emit, qelibListMatrix_emit]
        change R2 * entryMat t (tgtKeep (F t)) * entryMat c (ctrlKeep (F c)) *
            (qelibListMatrix [QGate.cx c t] *
              (entryMat c (ctrlEmit (F c)) * entryMat t (tgtEmit (F t))))
          = CX * (R2 * entryMat t (F t) * entryMat c (F c))
        rw [show qelibListMatrix [QGate.cx c t] = CX by simp [qelibListMatrix, CX]]
        calc _ = R2 * entryMat t (tgtKeep (F t)) * (entryMat c (ctrlKeep (F c)) * CX) *
              (entryMat c (ctrlEmit (F c)) * entryMat t (tgtEmit (F t))) := by
              simp only [mul_assoc]
          _ = R2 * (entryMat t (tgtKeep (F t)) * CX) *
              (entryMat c (ctrlKeep (F c)) * entryMat c (ctrlEmit (F c))) *
              entryMat t (tgtEmit (F t)) := by rw [← hK.eq]; simp only [mul_assoc]
          _ = (R2 * CX) * entryMat t (tgtKeep (F t)) *
              (entryMat c (F c) * entryMat t (tgtEmit (F t))) := by
              rw [← hKt.eq, ← hsplit]; simp only [mul_assoc]
          _ = CX * (R2 * (entryMat t (tgtKeep (F t)) * entryMat t (tgtEmit (F t))) *
              entryMat c (F c)) := by rw [← hR2.eq, hce.eq]; simp only [mul_assoc]
          _ = _ := by rw [← htsplit]
    · simp [stF_replicate, prodOn_none, QrunchBasis.qelibListMatrix_append, qelibListMatrix,
        qelibListMatrix_flushOn]

/-- The scan from `v` realises the input after the pending rotations of `v`. -/
theorem qelibListMatrix_fuseAux (l : List (QGate n)) :
    ∀ v : Vector Pend n,
      qelibListMatrix (fuseAux v l) = qelibListMatrix l * prodOn (stF v) (List.finRange n) := by
  induction l with
  | nil => intro v; simp [fuseAux, qelibListMatrix, qelibListMatrix_flushOn]
  | cons g gs ih =>
    intro v
    simp only [fuseAux, QrunchBasis.qelibListMatrix_append, ih, qelibListMatrix, mul_assoc,
      step_spec]

/-- **The pass is exact**: the fused statements have the matrix of the input. -/
theorem qelibListMatrix_fuseQ (l : List (QGate n)) :
    qelibListMatrix (fuseQ l) = qelibListMatrix l := by
  rw [fuseQ, qelibListMatrix_fuseAux, stF_replicate, prodOn_none, mul_one]

/-! ## Counts -/

/-- One scan step emits and keeps pending at most one statement more than it held. -/
theorem step_length (v : Vector Pend n) (g : QGate n) :
    (step v g).1.length + sizeOn (stF (step v g).2) (List.finRange n)
      ≤ 1 + sizeOn (stF v) (List.finRange n) := by
  have hL := List.nodup_finRange n
  unfold step
  split
  · next q A a hg =>
    have hx := sizeOn_extract (stF v) hL (List.mem_finRange q)
    split
    · next B b hv =>
      have hv' : stF v q = some (B, b) := hv
      have he := length_emit_le q (some (B, b))
      split
      · rw [stF_setQ, sizeOn_setF, hx, hv']
        simp only [List.length_nil, wt]
        omega
      · rw [stF_setQ, sizeOn_setF, hx, hv']
        simp only [wt] at he ⊢
        omega
    · next hv =>
      have hv' : stF v q = none := hv
      rw [stF_setQ, sizeOn_setF, hx, hv']
      simp only [List.length_nil, wt]
      omega
  · next hg =>
    have hf := length_flushOn_le (stF v) (List.finRange n)
    split
    · next c t =>
      split
      · simp only [List.length_append, List.length_singleton, stF_replicate, sizeOn_none]
        omega
      · next hct =>
        set F := stF v
        have hF : stF (setQ (setQ v t (tgtKeep v[t])) c (ctrlKeep v[c]))
            = setF c (ctrlKeep (F c)) (setF t (tgtKeep (F t)) F) := by
          rw [stF_setQ, stF_setQ]; rfl
        have hxc := sizeOn_extract F hL (List.mem_finRange c)
        have hxt := sizeOn_extract (setF c none F) hL (List.mem_finRange t)
        have htc : setF c none F t = F t := by simp [setF, Ne.symm hct]
        rw [htc] at hxt
        have hR := setF_comm hct none (tgtKeep (F t)) F
        have h1 : (emit t (tgtEmit v[t])).length ≤ wt (tgtEmit (F t)) := length_emit_le t _
        have h2 : (emit c (ctrlEmit v[c])).length ≤ wt (ctrlEmit (F c)) := length_emit_le c _
        have hw := wt_ctrl (F c)
        have hwt := wt_tgt (F t)
        rw [hF, sizeOn_setF _ c, hR, sizeOn_setF (setF c none F) t]
        simp only [List.length_append, List.length_singleton]
        omega
    · simp only [List.length_append, List.length_singleton, stF_replicate, sizeOn_none]
      omega

/-- The scan from `v` emits at most the input and the pending rotations of `v`. -/
theorem length_fuseAux_le (l : List (QGate n)) :
    ∀ v : Vector Pend n,
      (fuseAux v l).length ≤ l.length + sizeOn (stF v) (List.finRange n) := by
  induction l with
  | nil => intro v; simpa [fuseAux] using length_flushOn_le _ _
  | cons g gs ih =>
    intro v
    have h1 := ih (step v g).2
    have h2 := step_length v g
    simp only [fuseAux, List.length_append, List.length_cons]
    omega

/-- **The pass does not lengthen the list.** -/
theorem length_fuseQ_le (l : List (QGate n)) : (fuseQ l).length ≤ l.length := by
  simpa [fuseQ, stF_replicate, sizeOn_none] using length_fuseAux_le l (Vector.replicate n none)

/-- Whether a statement is a `cx`. -/
def isCx : QGate n → Bool
  | .cx _ _ => true
  | _ => false

/-- The number of `cx` statements of a list. -/
def cxCount (l : List (QGate n)) : ℕ := l.countP isCx

/-- An emitted rotation is not a `cx`. -/
theorem cxCount_emit (q : Fin n) (e : Pend) : cxCount (emit q e) = 0 := by
  rcases e with _ | ⟨A, a⟩
  · rfl
  · by_cases h : isId A a = true
    · simp [emit, h, cxCount]
    · cases A <;> simp [emit, h, cxCount, mkQ, isCx]

/-- Flushed rotations hold no `cx`. -/
theorem cxCount_flushOn (F : Fin n → Pend) (L : List (Fin n)) : cxCount (flushOn F L) = 0 := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    have := cxCount_emit q (F q)
    simp only [flushOn, List.flatMap_cons, cxCount, List.countP_append] at ih this ⊢
    omega

/-- One scan step emits the `cx` of its input statement and no other. -/
theorem step_cxCount (v : Vector Pend n) (g : QGate n) :
    cxCount (step v g).1 = cxCount [g] := by
  unfold step
  split
  · next q A a hg =>
    have h0 : cxCount [g] = 0 := by rw [eq_mkQ_of_axis? hg]; cases A <;> rfl
    rw [h0]
    split
    · next B b _ =>
      split
      · rfl
      · exact cxCount_emit q (some (B, b))
    · rfl
  · next hg =>
    have hf := cxCount_flushOn (stF v) (List.finRange n)
    simp only [cxCount] at hf
    split
    · next c t =>
      have ht := cxCount_emit t (tgtEmit v[t])
      have hc := cxCount_emit c (ctrlEmit v[c])
      simp only [cxCount] at ht hc
      split <;> simp only [cxCount, List.countP_append, hf, ht, hc, zero_add]
    · simp only [cxCount, List.countP_append, hf, zero_add]

/-- The scan emits exactly the `cx` statements of its input. -/
theorem cxCount_fuseAux (l : List (QGate n)) :
    ∀ v : Vector Pend n, cxCount (fuseAux v l) = cxCount l := by
  induction l with
  | nil => intro v; rw [fuseAux, cxCount_flushOn]; rfl
  | cons g gs ih =>
    intro v
    have h1 := ih (step v g).2
    have h2 := step_cxCount v g
    simp only [fuseAux, cxCount, List.countP_append, List.countP_cons, List.countP_nil] at h1 h2 ⊢
    omega

/-- **The pass keeps every `cx` statement.** -/
theorem cxCount_fuseQ (l : List (QGate n)) : cxCount (fuseQ l) = cxCount l :=
  cxCount_fuseAux l _

/-! ## The one-qubit Clifford frame

`fuseQ` merges rotations about one axis only. A rotation by a multiple of `π/2` about `x`, `y`,
`z` or the `p` axis is a one-qubit Clifford up to phase: conjugation by it permutes the Pauli
matrices up to sign. The pass `pauliQ` keeps per qubit a pending Clifford, a word of at most two
such rotations about `x`, `y` and `p` held in two layers of `Pend` (the inner one applied
first). A rotation by a multiple of `π/2` is multiplied into it; every other rotation is emitted
conjugated through it, its axis permuted and its angle negated as the frame says.

Products and conjugations are computed exactly over `ℤ[ζ]`, `ζ = e^{iπ/4}`, where the rotation by
`m · π/2` has an exact matrix up to the factor `2^(m mod 4)` (`toM_repRot`, from one matrix fact
per generator, `toM_repQ`). The new frame is the first word of `cliffWords` whose exact matrix
is the product up to a power of `ζ`, so a shortest one; the axis of a conjugated rotation is the
Pauli `σ_B` with `F σ_B = ± σ_A F`. Both checks run in the pass and are proved sound
(`eq_smul_of_mem_rots`, `conj_spec`), so no table of the 24 elements is trusted. The output
carries the global phase of these rewrites; `qelibListMatrix_pauliQ` states the exactness with
it. -/

/-- `e^{ikπ} = cos (kπ)` for an integer `k`. -/
theorem exp_int_mul_pi (k : ℤ) :
    Complex.exp (Complex.I * (((k : ℝ) * Real.pi : ℝ) : ℂ)) =
      (Real.cos (k * Real.pi) : ℂ) := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.sin_int_mul_pi]
  simp

/-- A rotation by `k · 2π` is `(-1)^k` about `x`, `y`, `z` and the identity for `p`, as a
phase. -/
theorem axisMat_int_mul_two_pi (A : Axis) (k : ℤ) :
    axisMat A ((k : ℝ) * (2 * Real.pi)) =
      Complex.exp (Complex.I * (if A = .p then 0 else ((k : ℝ) * Real.pi : ℝ))) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h2 : (k : ℝ) * (2 * Real.pi) / 2 = k * Real.pi := by ring
  have hs := Real.sin_int_mul_pi k
  have he := exp_int_mul_pi k
  have hn : Complex.exp (-(Complex.I * (((k : ℝ) * Real.pi : ℝ) : ℂ))) =
      (Real.cos (k * Real.pi) : ℂ) := by
    rw [show -(Complex.I * (((k : ℝ) * Real.pi : ℝ) : ℂ)) =
        (((-k : ℤ) : ℝ) * Real.pi : ℝ) * Complex.I by
      push_cast; ring, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.sin_int_mul_pi]
    push_cast; simp
  push_cast at he hn
  cases A
  · ext i j; fin_cases i <;> fin_cases j <;> simp [axisMat, rxMatrix, h2, hs, he]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [axisMat, ryMatrix, h2, hs, he]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [axisMat, rzMatrix, h2, he, hn]
  · simpa [axisMat] using rzGate_int_mul_two_pi k

/-- The `2 × 2` matrix of a frame entry: the identity when absent. -/
noncomputable def frameMat : Pend → Matrix (Fin 2) (Fin 2) ℂ
  | none => 1
  | some (A, a) => axisMat A a.toReal
/-- A matrix on `q` commutes with the frames once `q` is cleared. -/
theorem commute_embedGate1_prodOn_setF_none (q : Fin n) (M : Matrix (Fin 2) (Fin 2) ℂ)
    (F : Fin n → Pend) (L : List (Fin n)) :
    Commute (embedGate1 n q M) (prodOn (setF q none F) L) := by
  refine commute_prodOn fun i _ => ?_
  by_cases hi : i = q
  · subst hi
    rw [setF_self]
    exact Commute.one_right _
  · rcases h : setF q none F i with _ | ⟨B, b⟩
    · exact Commute.one_right _
    · exact Optimization.DisjointCommute.embedGate1_disjoint_comm (Ne.symm hi) _ _

/-- The matrix of a frame entry on `q`. -/
theorem entryMat_eq_frameMat (q : Fin n) (e : Pend) :
    entryMat q e = embedGate1 n q (frameMat e) := by
  rcases e with _ | ⟨A, a⟩
  · simp [entryMat, frameMat, embedGate1_one]
  · rfl

section CliffordFrame

/-- The primitive eighth root of unity `ζ = e^{iπ/4}`. -/
noncomputable def zeta8 : ℂ := Complex.exp (Complex.I * (Real.pi / 4 : ℝ))

/-- `ζ^k = e^{i (k/4) π}`. -/
theorem zeta8_pow (k : ℕ) :
    zeta8 ^ k = Complex.exp (Complex.I * (((k : ℚ) / 4 : ℚ) * Real.pi : ℝ)) := by
  rw [zeta8, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `ζ² = i`. -/
theorem zeta8_sq : zeta8 ^ 2 = Complex.I := by
  rw [zeta8_pow, show (((2 : ℕ) : ℚ) / 4 : ℚ) = 1 / 2 by norm_num]
  rw [show Complex.I * ((((1 / 2 : ℚ) : ℝ) * Real.pi : ℝ) : ℂ) = Real.pi / 2 * Complex.I by
    push_cast; ring, Complex.exp_pi_div_two_mul_I]

/-- `ζ⁴ = -1`. -/
theorem zeta8_pow_four : zeta8 ^ 4 = -1 := by
  rw [show zeta8 ^ 4 = (zeta8 ^ 2) ^ 2 by ring, zeta8_sq, Complex.I_sq]

/-- `ζ = (1 + i) / √2`. -/
theorem zeta8_eq :
    zeta8 = ((Real.sqrt 2 / 2 : ℝ) : ℂ) + ((Real.sqrt 2 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [zeta8, mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]

/-- An element `a + b ζ + c ζ² + d ζ³` of `ℤ[ζ]`, `ζ = e^{iπ/4}`, with `ζ⁴ = -1`; the entries of
the exact matrices of Clifford rotations. -/
structure Zw where
  /-- The coefficient of `1`. -/
  a : ℤ
  /-- The coefficient of `ζ`. -/
  b : ℤ
  /-- The coefficient of `ζ²`. -/
  c : ℤ
  /-- The coefficient of `ζ³`. -/
  d : ℤ
  deriving DecidableEq

namespace Zw
instance : Zero Zw := ⟨⟨0, 0, 0, 0⟩⟩
instance : One Zw := ⟨⟨1, 0, 0, 0⟩⟩
instance : Add Zw := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩⟩
instance : Neg Zw := ⟨fun x => ⟨-x.a, -x.b, -x.c, -x.d⟩⟩
instance : Mul Zw := ⟨fun x y =>
  ⟨x.a * y.a - x.b * y.d - x.c * y.c - x.d * y.b, x.a * y.b + x.b * y.a - x.c * y.d - x.d * y.c,
    x.a * y.c + x.b * y.b + x.c * y.a - x.d * y.d, x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a⟩⟩
/-- Multiplication by an integer. -/
def zsmul (k : ℤ) (x : Zw) : Zw := ⟨k * x.a, k * x.b, k * x.c, k * x.d⟩
/-- Multiplication by `ζ`: a shift of the coefficients. -/
def mulW (x : Zw) : Zw := ⟨-x.d, x.a, x.b, x.c⟩
/-- The complex number of an element of `ℤ[ζ]`. -/
noncomputable def toC (x : Zw) : ℂ := x.a + x.b * zeta8 + x.c * zeta8 ^ 2 + x.d * zeta8 ^ 3

/-- `toC` maps `0` to `0`. -/
theorem toC_zero : toC 0 = 0 := by simp [toC, show (0 : Zw) = ⟨0, 0, 0, 0⟩ from rfl]
/-- `toC` maps `1` to `1`. -/
theorem toC_one : toC 1 = 1 := by simp [toC, show (1 : Zw) = ⟨1, 0, 0, 0⟩ from rfl]
/-- `toC` is additive. -/
theorem toC_add (x y : Zw) : toC (x + y) = toC x + toC y := by
  simp only [toC, show x + y = ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩ from rfl]
  push_cast; ring
/-- `toC` commutes with negation. -/
theorem toC_neg (x : Zw) : toC (-x) = -toC x := by
  simp only [toC, show -x = ⟨-x.a, -x.b, -x.c, -x.d⟩ from rfl]
  push_cast; ring
/-- `toC` is multiplicative, by `ζ⁴ = -1`. -/
theorem toC_mul (x y : Zw) : toC (x * y) = toC x * toC y := by
  simp only [toC, show x * y = ⟨x.a * y.a - x.b * y.d - x.c * y.c - x.d * y.b,
    x.a * y.b + x.b * y.a - x.c * y.d - x.d * y.c, x.a * y.c + x.b * y.b + x.c * y.a - x.d * y.d,
    x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a⟩ from rfl]
  push_cast
  linear_combination (-((x.b * y.d + x.c * y.c + x.d * y.b : ℂ) + (x.c * y.d + x.d * y.c) * zeta8 +
    x.d * y.d * zeta8 ^ 2)) * zeta8_pow_four
/-- `toC` commutes with integer multiples. -/
theorem toC_zsmul (k : ℤ) (x : Zw) : toC (zsmul k x) = k * toC x := by
  simp only [toC, zsmul]; push_cast; ring
/-- `mulW` multiplies by `ζ`. -/
theorem toC_mulW (x : Zw) : toC (mulW x) = zeta8 * toC x := by
  simp only [toC, mulW]; push_cast
  linear_combination (-(x.d : ℂ)) * zeta8_pow_four
/-- `k` applications of `mulW` multiply by `ζ^k`. -/
theorem toC_iterate_mulW (k : ℕ) (x : Zw) : toC (mulW^[k] x) = zeta8 ^ k * toC x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', toC_mulW, ih, pow_succ]; ring
end Zw

/-- A `2 × 2` matrix over `ℤ[ζ]`. -/
structure M2 where
  /-- Row 0, column 0. -/
  e00 : Zw
  /-- Row 0, column 1. -/
  e01 : Zw
  /-- Row 1, column 0. -/
  e10 : Zw
  /-- Row 1, column 1. -/
  e11 : Zw
  deriving DecidableEq

namespace M2
instance : One M2 := ⟨⟨1, 0, 0, 1⟩⟩
instance : Neg M2 := ⟨fun X => ⟨-X.e00, -X.e01, -X.e10, -X.e11⟩⟩
instance : Mul M2 := ⟨fun X Y => ⟨X.e00 * Y.e00 + X.e01 * Y.e10, X.e00 * Y.e01 + X.e01 * Y.e11,
  X.e10 * Y.e00 + X.e11 * Y.e10, X.e10 * Y.e01 + X.e11 * Y.e11⟩⟩
/-- An entrywise map. -/
def map (f : Zw → Zw) (X : M2) : M2 := ⟨f X.e00, f X.e01, f X.e10, f X.e11⟩
/-- The `k`-th power. -/
def npow (X : M2) : ℕ → M2
  | 0 => 1
  | k + 1 => X * npow X k
/-- The complex matrix of a matrix over `ℤ[ζ]`. -/
noncomputable def toM (X : M2) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![X.e00.toC, X.e01.toC; X.e10.toC, X.e11.toC]

/-- `toM` maps `1` to `1`. -/
theorem toM_one : toM 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [toM, show (1 : M2) = ⟨1, 0, 0, 1⟩ from rfl, Zw.toC_one, Zw.toC_zero]
/-- `toM` is multiplicative. -/
theorem toM_mul (X Y : M2) : toM (X * Y) = toM X * toM Y := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [toM, show X * Y = ⟨X.e00 * Y.e00 + X.e01 * Y.e10, X.e00 * Y.e01 + X.e01 * Y.e11,
      X.e10 * Y.e00 + X.e11 * Y.e10, X.e10 * Y.e01 + X.e11 * Y.e11⟩ from rfl, Matrix.mul_apply,
      Fin.sum_univ_two, Zw.toC_add, Zw.toC_mul]
/-- `toM` commutes with negation. -/
theorem toM_neg (X : M2) : toM (-X) = -toM X := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [toM, show -X = ⟨-X.e00, -X.e01, -X.e10, -X.e11⟩ from rfl, Zw.toC_neg]
/-- An entrywise map that multiplies by `c` multiplies the matrix by `c`. -/
theorem toM_map {f : Zw → Zw} {c : ℂ} (h : ∀ x, (f x).toC = c * x.toC) (X : M2) :
    toM (X.map f) = c • toM X := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toM, map, h]
/-- `toM` commutes with powers. -/
theorem toM_npow (X : M2) (k : ℕ) : toM (X.npow k) = toM X ^ k := by
  induction k with
  | zero => exact toM_one
  | succ k ih => rw [npow, toM_mul, ih, pow_succ']
end M2

open Zw M2

/-- The exact matrix of the rotation by `π/2` about an axis, times `2`. -/
def repQ : Axis → M2
  | .x => ⟨⟨0, 1, 0, -1⟩, ⟨0, -1, 0, -1⟩, ⟨0, -1, 0, -1⟩, ⟨0, 1, 0, -1⟩⟩
  | .y => ⟨⟨0, 1, 0, -1⟩, ⟨0, -1, 0, 1⟩, ⟨0, 1, 0, -1⟩, ⟨0, 1, 0, -1⟩⟩
  | .z => ⟨⟨0, 0, 0, -2⟩, 0, 0, ⟨0, 2, 0, 0⟩⟩
  | .p => ⟨⟨2, 0, 0, 0⟩, 0, 0, ⟨0, 0, 2, 0⟩⟩

/-- `ζ³ = i ζ`. -/
theorem zeta8_cube : zeta8 ^ 3 = Complex.I * zeta8 := by rw [pow_succ, zeta8_sq]

/-- `e^{iπ/4} = ζ`. -/
theorem exp_I_pi_four : Complex.exp (Complex.I * ((Real.pi / 2 / 2 : ℝ) : ℂ)) = zeta8 := by
  rw [zeta8]; congr 3; ring

/-- `e^{-iπ/4} = -ζ³`. -/
theorem exp_neg_I_pi_four :
    Complex.exp (-(Complex.I * ((Real.pi / 2 / 2 : ℝ) : ℂ))) = -zeta8 ^ 3 := by
  have h : zeta8 * -zeta8 ^ 3 = 1 := by linear_combination (-1 : ℂ) * zeta8_pow_four
  rw [Complex.exp_neg, exp_I_pi_four, inv_eq_of_mul_eq_one_right h]

/-- `e^{iπ/2} = i`. -/
theorem exp_I_half_pi : Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
  rw [show Complex.I * ((Real.pi / 2 : ℝ) : ℂ) = Real.pi / 2 * Complex.I by push_cast; ring,
    Complex.exp_pi_div_two_mul_I]

/-- **The matrix fact per generator**: `repQ A` is twice the rotation by `π/2` about `A`. -/
theorem toM_repQ (A : Axis) : toM (repQ A) = (2 : ℂ) • axisMat A (Real.pi / 2) := by
  have hc : Real.pi / 2 / 2 = Real.pi / 4 := by ring
  have h0 : (0 : Zw) = ⟨0, 0, 0, 0⟩ := rfl
  cases A
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [toM, repQ, toC, axisMat, rxMatrix, hc, Real.cos_pi_div_four, Real.sin_pi_div_four,
        zeta8_cube] <;> rw [zeta8_eq] <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [toM, repQ, toC, axisMat, ryMatrix, hc, Real.cos_pi_div_four, Real.sin_pi_div_four,
        zeta8_cube] <;> rw [zeta8_eq] <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  · simp only [axisMat, rzMatrix, exp_I_pi_four, exp_neg_I_pi_four]
    ext i j; fin_cases i <;> fin_cases j <;> simp [toM, repQ, toC, h0]
  · simp only [axisMat, rzGate, exp_I_half_pi]
    ext i j; fin_cases i <;> fin_cases j <;> simp [toM, repQ, toC, zeta8_sq, h0]
/-- An angle that is an integer multiple `m` of `π/2`: `some m`. -/
def halfPiMul? (a : PiLin) : Option ℤ :=
  if a.a = 0 ∧ (2 * a.b).den = 1 then some (2 * a.b).num else none

/-- An angle recognised by `halfPiMul?` is that multiple of `π/2`. -/
theorem toReal_of_halfPiMul? {a : PiLin} {m : ℤ} (h : halfPiMul? a = some m) :
    a.toReal = m * (Real.pi / 2) := by
  unfold halfPiMul? at h
  split_ifs at h with hc
  obtain ⟨ha, hb⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  have h2 : (((2 * a.b).num : ℚ) : ℝ) = ((2 * a.b : ℚ) : ℝ) := by
    rw [Rat.coe_int_num_of_den_eq_one hb]
  push_cast at h2
  rw [PiLin.toReal, ha, h2]
  push_cast
  ring

/-- The rotation by `j · π/2` is the `j`-th power of the rotation by `π/2`. -/
theorem axisMat_nat_mul (A : Axis) (j : ℕ) :
    axisMat A (j * (Real.pi / 2)) = axisMat A (Real.pi / 2) ^ j := by
  induction j with
  | zero => simp [axisMat_zero]
  | succ j ih => rw [Nat.cast_succ, add_mul, one_mul, add_comm, axisMat_add, ih, pow_succ']

/-- `e^{itπ} = ±1` by the parity of `t`. -/
theorem exp_int_mul_pi_eq (t : ℤ) :
    Complex.exp (Complex.I * ((t * Real.pi : ℝ) : ℂ)) = if t % 2 = 0 then 1 else -1 := by
  rw [show Complex.I * ((t * Real.pi : ℝ) : ℂ) = t * (Real.pi * Complex.I) by push_cast; ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]
  split_ifs with h
  · exact Even.neg_one_zpow (Int.even_iff.mpr h)
  · exact Odd.neg_one_zpow (Int.odd_iff.mpr (by omega))

/-- The exact matrix of the rotation about `A` by `m · π/2`, times `2^(m mod 4)`. -/
def repRot (A : Axis) (m : ℤ) : M2 :=
  if A = .p ∨ m / 4 % 2 = 0 then (repQ A).npow (m % 4).toNat else -(repQ A).npow (m % 4).toNat

/-- `repRot A m` is the rotation by `m · π/2` about `A`, times `2^(m mod 4)`. -/
theorem toM_repRot (A : Axis) (m : ℤ) :
    toM (repRot A m) = (2 : ℂ) ^ (m % 4).toNat • axisMat A (m * (Real.pi / 2)) := by
  have hm : (m : ℝ) * (Real.pi / 2) =
      ((m / 4 : ℤ) : ℝ) * (2 * Real.pi) + ((m % 4).toNat : ℕ) * (Real.pi / 2) := by
    have h1 : ((m % 4).toNat : ℤ) = m % 4 := Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num))
    have h2 : (m : ℝ) = 4 * ((m / 4 : ℤ) : ℝ) + (((m % 4).toNat : ℤ) : ℝ) := by
      rw [h1]; exact_mod_cast (show m = 4 * (m / 4) + m % 4 by omega)
    rw [h2]; push_cast; ring
  have hX : toM ((repQ A).npow (m % 4).toNat) =
      (2 : ℂ) ^ (m % 4).toNat • axisMat A (Real.pi / 2) ^ (m % 4).toNat := by
    rw [toM_npow, toM_repQ, smul_pow]
  rw [hm, axisMat_add, axisMat_int_mul_two_pi, axisMat_nat_mul, Matrix.smul_mul, Matrix.one_mul,
    smul_comm]
  unfold repRot
  cases A <;> simp only [reduceCtorEq, false_or, true_or, ite_true, ite_false] <;>
    first
    | (rw [exp_int_mul_pi_eq]; split_ifs <;> simp [toM_neg, hX])
    | simp [hX]

/-- The exact matrix of a frame entry and its power of `2`; `none` when the angle is not a
multiple of `π/2`. -/
def repPend : Pend → Option (M2 × ℕ)
  | none => some (1, 0)
  | some (A, a) => (halfPiMul? a).map fun m => (repRot A m, (m % 4).toNat)

/-- The exact matrix of a frame entry. -/
theorem toM_of_repPend {e : Pend} {X : M2} {s : ℕ} (h : repPend e = some (X, s)) :
    toM X = (2 : ℂ) ^ s • frameMat e := by
  rcases e with _ | ⟨A, a⟩
  · simp only [repPend, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [toM_one, frameMat]
  · simp only [repPend, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨m, hm, rfl, rfl⟩ := h
    rw [toM_repRot, frameMat, toReal_of_halfPiMul? hm]

/-- The exact matrix of a frame `(u, w)`, `u` after `w`, and its power of `2`. -/
def repPair (u w : Pend) : Option (M2 × ℕ) :=
  match repPend u, repPend w with
  | some (U, s), some (W, t) => some (U * W, s + t)
  | _, _ => none

/-- The exact matrix of a frame. -/
theorem toM_of_repPair {u w : Pend} {X : M2} {s : ℕ} (h : repPair u w = some (X, s)) :
    toM X = (2 : ℂ) ^ s • (frameMat u * frameMat w) := by
  unfold repPair at h
  split at h
  · next U su W sw hu hw =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [toM_mul, toM_of_repPend hu, toM_of_repPend hw, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, pow_add]
  · simp at h

/-- An exact matrix of `2^s • C` brought to the common scale `2^9`. -/
def scale9 (X : M2) (s : ℕ) : M2 := X.map (zsmul (2 ^ (9 - s)))

/-- `scale9` is an exact matrix of `2^9 • C`. -/
theorem toM_scale9 {X : M2} {s : ℕ} (hs : s ≤ 9) {C : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : toM X = (2 : ℂ) ^ s • C) : toM (scale9 X s) = (2 : ℂ) ^ 9 • C := by
  rw [scale9, toM_map (toC_zsmul _), hX, smul_smul]
  push_cast
  rw [← pow_add, Nat.sub_add_cancel hs]

/-- The eight phase rotations `ζ^k • Y`, with `k`. -/
def rots (Y : M2) : List (ℕ × M2) := (List.range 8).map fun k => (k, Y.map (mulW^[k]))

/-- **The phase check is sound**: exact matrices of `2^9 • C` and `2^9 • D` related by a phase
rotation relate the two matrices by that phase. -/
theorem eq_smul_of_mem_rots {X Y : M2} {r : ℕ × M2} (hr : r ∈ rots Y) (he : X = r.2)
    {C D : Matrix (Fin 2) (Fin 2) ℂ} (hX : toM X = (2 : ℂ) ^ 9 • C)
    (hY : toM Y = (2 : ℂ) ^ 9 • D) :
    C = Complex.exp (Complex.I * (PiLin.ofPi ((r.1 : ℚ) / 4)).toReal) • D := by
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hr
  have h := congrArg toM he
  rw [hX, toM_map (toC_iterate_mulW k), hY, smul_comm] at h
  rw [PiLin.toReal_ofPi, ← zeta8_pow]
  exact smul_right_injective _ (pow_ne_zero 9 two_ne_zero : (2 : ℂ) ^ 9 ≠ 0) h

/-- The rotations of frame words: by `π/2`, `π` and `-π/2` about `p`, `x` and `y`. -/
def cliffGens : List (Axis × PiLin) :=
  [Axis.p, .x, .y].flatMap fun A => [(A, PiLin.ofPi (1 / 2)), (A, 1), (A, PiLin.ofPi (-1 / 2))]

/-- The frame words of at most two rotations about distinct axes, as (outer, inner) pairs,
shorter first and, among two rotations, outer `p` first (a diagonal outer rotation passes the
control of a `cx`). Every one-qubit Clifford is one of them up to phase. -/
def cliffWords : List (Pend × Pend) :=
  (none, none) :: (cliffGens.map fun e => (some e, none)) ++
    cliffGens.flatMap fun e2 => cliffGens.filterMap fun e1 =>
      if e1.1 = e2.1 then none else some (some e2, some e1)

/-- The frame words with their exact matrices at the scale `2^9`, computed once. -/
def cliffReps : List (Pend × Pend × M2) :=
  cliffWords.filterMap fun c =>
    match repPair c.1 c.2 with
    | some (X, s) => if s ≤ 9 then some (c.1, c.2, scale9 X s) else none
    | none => none

/-- The matrices of `cliffReps` are exact matrices of their words at the scale `2^9`. -/
theorem toM_of_mem_cliffReps {c : Pend × Pend × M2} (h : c ∈ cliffReps) :
    toM c.2.2 = (2 : ℂ) ^ 9 • (frameMat c.1 * frameMat c.2.1) := by
  obtain ⟨d, -, hd⟩ := List.mem_filterMap.1 h
  split at hd
  · next X s hr =>
    split_ifs at hd with hs
    simp only [Option.some.injEq] at hd
    subst hd
    exact toM_scale9 hs (toM_of_repPair hr)
  · simp at hd

/-- The rotation about `A` by `m · π/2` multiplied into the frame `(u, w)`: the first word of
`cliffReps`, of weight at most one more than the frame's, whose exact matrix is the product up to
a phase `ζ^k`, with `k`. The product is brought to the scale `2^9` and rotated once, so each word
costs eight comparisons. -/
def absorb (u w : Pend) (A : Axis) (m : ℤ) : Option (Pend × Pend × ℕ) :=
  match repPair u w with
  | none => none
  | some (F, s) =>
    if (m % 4).toNat + s ≤ 9 then
      let Rs := rots (scale9 (repRot A m * F) ((m % 4).toNat + s))
      cliffReps.findSome? fun c =>
        if wt c.1 + wt c.2.1 ≤ 1 + wt u + wt w then
          (Rs.find? fun r => decide (c.2.2 = r.2)).map fun r => (c.1, c.2.1, r.1)
        else none
    else none

/-- A word found by `absorb` is the product up to its phase, and at most as long as allowed. -/
theorem absorb_spec {u w u' w' : Pend} {A : Axis} {m : ℤ} {k : ℕ}
    (h : absorb u w A m = some (u', w', k)) :
    frameMat u' * frameMat w' = Complex.exp (Complex.I * (PiLin.ofPi ((k : ℚ) / 4)).toReal) •
        (axisMat A (m * (Real.pi / 2)) * (frameMat u * frameMat w)) ∧
      wt u' + wt w' ≤ 1 + wt u + wt w := by
  unfold absorb at h
  split at h
  · simp at h
  · next F s hF =>
    split_ifs at h with ht
    obtain ⟨c, hc, hfc⟩ := List.exists_of_findSome?_eq_some h
    split_ifs at hfc with hwt
    obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.1 hfc
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hY : toM (repRot A m * F) = (2 : ℂ) ^ ((m % 4).toNat + s) •
        (axisMat A (m * (Real.pi / 2)) * (frameMat u * frameMat w)) := by
      rw [toM_mul, toM_repRot, toM_of_repPair hF, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        pow_add]
    exact ⟨eq_smul_of_mem_rots (List.mem_of_find?_eq_some hr)
      (of_decide_eq_true (List.find?_some (p := fun r : ℕ × M2 => decide (c.2.2 = r.2)) hr))
      (toM_of_mem_cliffReps hc) (toM_scale9 ht hY), hwt⟩

/-- The exact Pauli matrix of an axis (`Z` for `z` and `p`). -/
def sig : Axis → M2
  | .x => ⟨0, 1, 1, 0⟩
  | .y => ⟨0, ⟨0, 0, -1, 0⟩, ⟨0, 0, 1, 0⟩, 0⟩
  | .z | .p => ⟨1, 0, 0, ⟨-1, 0, 0, 0⟩⟩

/-- `rz(θ) = cos(θ/2) - i sin(θ/2) Z`. -/
theorem rzMatrix_eq_sig (θ : ℝ) :
    rzMatrix θ = (Real.cos (θ / 2) : ℂ) • 1 - (Complex.I * Real.sin (θ / 2)) • toM (sig .z) := by
  have h0 : (0 : Zw) = ⟨0, 0, 0, 0⟩ := rfl
  have h1 : (1 : Zw) = ⟨1, 0, 0, 0⟩ := rfl
  have hn : Complex.exp (-(Complex.I * ((θ / 2 : ℝ) : ℂ))) =
      Real.cos (θ / 2) - Real.sin (θ / 2) * Complex.I := by
    rw [show -(Complex.I * ((θ / 2 : ℝ) : ℂ)) = Complex.I * ((-(θ / 2) : ℝ) : ℂ) by push_cast; ring,
      exp_I_mul_ofReal, Real.cos_neg, Real.sin_neg]
    push_cast; ring
  simp only [rzMatrix, hn, exp_I_mul_ofReal]
  ext i j; fin_cases i <;> fin_cases j <;> simp [toM, sig, toC, h0, h1] <;> ring

/-- A rotation is `cos(θ/2) - i sin(θ/2) σ` for the Pauli `σ` of its axis, with the phase
`e^{iθ/2}` for `p`. -/
theorem axisMat_eq_sig (A : Axis) (θ : ℝ) :
    axisMat A θ = Complex.exp (Complex.I * (if A = .p then θ / 2 else 0 : ℝ)) •
      ((Real.cos (θ / 2) : ℂ) • 1 - (Complex.I * Real.sin (θ / 2)) • toM (sig A)) := by
  have h0 : (0 : Zw) = ⟨0, 0, 0, 0⟩ := rfl
  have h1 : (1 : Zw) = ⟨1, 0, 0, 0⟩ := rfl
  cases A
  · ext i j; fin_cases i <;> fin_cases j <;> simp [axisMat, rxMatrix, toM, sig, toC, h0, h1]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [axisMat, ryMatrix, toM, sig, toC, h0, zeta8_sq] <;> ring_nf <;>
      simp [Complex.I_sq]
  · simpa [axisMat] using rzMatrix_eq_sig θ
  · simp only [axisMat, ite_true, rzGate_eq_smul_rzMatrix, rzMatrix_eq_sig]
    rfl
/-- The Pauli of the frame matrix `F` conjugated: `(B, neg)` with `F σ_B = ± σ_A F`, the sign
negative when `neg`. -/
def conjAx? (F : M2) (A : Axis) : Option (Axis × Bool) :=
  let R := sig A * F
  [Axis.x, .y, .z].findSome? fun B =>
    let L := F * sig B
    if L = R then some (B, false) else if L = -R then some (B, true) else none

/-- The axis of an emitted rotation: `p` when a `p` rotation comes out about `z`. -/
def emAx (A B : Axis) : Axis := if B = .z ∧ A = .p then .p else B

/-- The emitted axis has the Pauli of the conjugated one. -/
theorem sig_emAx (A B : Axis) : sig (emAx A B) = sig B := by
  unfold emAx
  split_ifs with h
  · rw [h.1]; rfl
  · rfl

/-- The phase of `axisMat A a` against the Pauli form: `a/2` for `p`, else zero. -/
def pShift (A : Axis) (a : PiLin) : PiLin := if A = .p then a / PiLin.ofPi 2 else 0

/-- The real value of `pShift`. -/
theorem toReal_pShift (A : Axis) (a : PiLin) :
    (pShift A a).toReal = if A = .p then a.toReal / 2 else 0 := by
  unfold pShift
  split_ifs <;> simp [PiLin.toReal_div_ofPi]

/-- **A rotation passes the frame** as `conjAx?` says: about the conjugated axis, the angle
negated when the sign is, up to the phase of `pShift`. -/
theorem conj_spec {F : M2} {A B : Axis} {neg : Bool} (h : conjAx? F A = some (B, neg)) {s : ℕ}
    {W : Matrix (Fin 2) (Fin 2) ℂ} (hF : toM F = (2 : ℂ) ^ s • W) (a : PiLin) :
    W * axisMat (emAx A B) (if neg then -a else a).toReal =
      Complex.exp (Complex.I * (pShift (emAx A B) (if neg then -a else a) - pShift A a).toReal) •
        (axisMat A a.toReal * W) := by
  have hc : F * sig B = if neg then -(sig A * F) else sig A * F := by
    obtain ⟨B', -, hB'⟩ := List.exists_of_findSome?_eq_some h
    simp only at hB'
    split_ifs at hB' with h1 h2 <;> simp only [Option.some.injEq, Prod.mk.injEq] at hB' <;>
      obtain ⟨rfl, rfl⟩ := hB' <;> simpa
  have hW : W * toM (sig B) = (if neg then -1 else 1 : ℂ) • (toM (sig A) * W) := by
    have he := congrArg toM hc
    apply smul_right_injective _ (pow_ne_zero s two_ne_zero : (2 : ℂ) ^ s ≠ 0)
    cases neg <;>
      simpa [toM_mul, toM_neg, hF, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]
        using he
  rw [PiLin.toReal_sub, toReal_pShift, toReal_pShift, axisMat_eq_sig (emAx A B), sig_emAx,
    axisMat_eq_sig A]
  generalize (if A = .p then a.toReal / 2 else 0) = y
  have hx : ∀ x : ℝ, Complex.exp (Complex.I * x) =
      Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) * Complex.exp (Complex.I * y) := fun x => by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  cases neg
  · simp only [Bool.false_eq_true, ite_false, one_smul] at hW ⊢
    rw [hx]
    simp only [Matrix.mul_smul, Matrix.mul_sub, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, hW]
    module
  · simp only [ite_true, neg_smul, one_smul] at hW ⊢
    rw [hx]
    simp only [PiLin.toReal_neg, neg_div, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg,
      Matrix.mul_smul, Matrix.mul_sub, Matrix.smul_mul, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, hW]
    module

/-- The rotations of a frame entry. -/
def frameList : Pend → List (Axis × PiLin)
  | none => []
  | some e => [e]

/-- The `2 × 2` matrix of a list of rotations, head applied first. -/
noncomputable def listMat : List (Axis × PiLin) → Matrix (Fin 2) (Fin 2) ℂ
  | [] => 1
  | e :: l => listMat l * axisMat e.1 e.2.toReal

/-- The matrix of a concatenation. -/
theorem listMat_append (l₁ l₂ : List (Axis × PiLin)) :
    listMat (l₁ ++ l₂) = listMat l₂ * listMat l₁ := by
  induction l₁ with
  | nil => simp [listMat]
  | cons e l ih => rw [List.cons_append, listMat, ih, listMat, mul_assoc]

/-- The matrix of the rotations of a frame entry. -/
theorem listMat_frameList (e : Pend) : listMat (frameList e) = frameMat e := by
  rcases e with _ | ⟨A, a⟩ <;> simp [frameList, listMat, frameMat]

/-- One rotation about `A` by `a` against the frame `(u, w)` of its qubit: the rotations it
emits, the phase and the next frame. A rotation by a multiple of `π/2` is multiplied into the
frame (`absorb`); any other is emitted conjugated through the frame (`conjAx?`). When either
fails (it does not on frames the pass builds) the frame is emitted. -/
def frameLocal (u w : Pend) (A : Axis) (a : PiLin) :
    List (Axis × PiLin) × PiLin × Pend × Pend :=
  match halfPiMul? a with
  | some m =>
    match absorb u w A m with
    | some (u', w', k) => ([], PiLin.ofPi ((k : ℚ) / 4), u', w')
    | none => (frameList w ++ frameList u, 0, some (A, a), none)
  | none =>
    match repPair u w with
    | some (F, _) =>
      match conjAx? F A with
      | some (B, neg) =>
        ([(emAx A B, if neg then -a else a)],
          pShift (emAx A B) (if neg then -a else a) - pShift A a, u, w)
      | none => (frameList w ++ frameList u ++ [(A, a)], 0, none, none)
    | none => (frameList w ++ frameList u ++ [(A, a)], 0, none, none)

/-- One local frame step: the next frame after the emitted rotations is the rotation after
the frame, up to the phase of the step. -/
theorem frameLocal_spec (u w : Pend) (A : Axis) (a : PiLin) :
    frameMat (frameLocal u w A a).2.2.1 * frameMat (frameLocal u w A a).2.2.2 *
        listMat (frameLocal u w A a).1 =
      Complex.exp (Complex.I * (frameLocal u w A a).2.1.toReal) •
        (axisMat A a.toReal * (frameMat u * frameMat w)) := by
  have hfb : listMat (frameList w ++ frameList u ++ [(A, a)]) =
      axisMat A a.toReal * (frameMat u * frameMat w) := by
    simp [listMat_append, listMat_frameList, listMat, mul_assoc]
  unfold frameLocal
  split
  · next m hm =>
    split
    · next u' w' k hk =>
      rw [listMat, mul_one, (absorb_spec hk).1, toReal_of_halfPiMul? hm]
    · simp [listMat_append, listMat_frameList, frameMat]
  · split
    · next F s hF =>
      split
      · next B neg hB =>
        rw [listMat, listMat, Matrix.one_mul, conj_spec hB (toM_of_repPair hF)]
      · rw [hfb]; simp [frameMat]
    · rw [hfb]; simp [frameMat]

/-- One local frame step emits and keeps at most one rotation more than the frame held. -/
theorem frameLocal_length (u w : Pend) (A : Axis) (a : PiLin) :
    (frameLocal u w A a).1.length + wt (frameLocal u w A a).2.2.1 +
        wt (frameLocal u w A a).2.2.2 ≤ 1 + wt u + wt w := by
  have hl : ∀ e : Pend, (frameList e).length = wt e := by
    intro e; rcases e with _ | _ <;> rfl
  unfold frameLocal
  split
  · split
    · next u' w' k hk => simpa using (absorb_spec hk).2
    · simp [hl, wt]; omega
  · split
    · split
      · simp
      · simp [hl, wt]; omega
    · simp [hl, wt]; omega

end CliffordFrame

/-! ### The frame over all qubits

The frame state is two layers of `Pend`: the frame on `q` is `U[q]` after `W[q]`, its matrix
`prodOn U * prodOn W`. -/

/-- The statements of a list of rotations on qubit `q`. -/
def onQ (q : Fin n) (l : List (Axis × PiLin)) : List (QGate n) := l.map fun e => mkQ e.1 q e.2

/-- The statements of a list of rotations on `q` realise its `2 × 2` matrix on `q`. -/
theorem qelibListMatrix_onQ (q : Fin n) (l : List (Axis × PiLin)) :
    qelibListMatrix (onQ q l) = embedGate1 n q (listMat l) := by
  induction l with
  | nil => simp [onQ, qelibListMatrix, listMat, embedGate1_one]
  | cons e l ih =>
    simp only [onQ, List.map_cons, qelibListMatrix, listMat] at ih ⊢
    rw [ih, qelibMatrix_mkQ, embedGate1_mul]

/-- Rotation statements hold no `cx`. -/
theorem cxCount_onQ (q : Fin n) (l : List (Axis × PiLin)) : cxCount (onQ q l) = 0 := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨B, b⟩ := e
    cases B <;> simpa [onQ, cxCount, mkQ, isCx] using ih

/-- The two layers factor at `q`: the other qubits, then the frame on `q`. -/
theorem prodOn_layers (F G : Fin n → Pend) (q : Fin n) :
    prodOn F (List.finRange n) * prodOn G (List.finRange n) =
      prodOn (setF q none F) (List.finRange n) * prodOn (setF q none G) (List.finRange n) *
        embedGate1 n q (frameMat (F q) * frameMat (G q)) := by
  have hL := List.nodup_finRange n
  rw [prodOn_extract F hL (List.mem_finRange q), prodOn_extract G hL (List.mem_finRange q),
    entryMat_eq_frameMat, entryMat_eq_frameMat, ← embedGate1_mul, mul_assoc,
    ← mul_assoc (embedGate1 n q _), (commute_embedGate1_prodOn_setF_none q _ G _).eq]
  simp only [mul_assoc]

/-- One rotation statement about `A` by `a` on `q` against the frame `(U, W)` (`frameLocal`). -/
def frameRot (U W : Vector Pend n) (q : Fin n) (A : Axis) (a : PiLin) :
    List (QGate n) × PiLin × Vector Pend n × Vector Pend n :=
  let r := frameLocal (stF U q) (stF W q) A a
  (onQ q r.1, r.2.1, setQ U q r.2.2.1, setQ W q r.2.2.2)

/-- One step of `frameRot`: the next frames after the emitted statements realise the rotation
after the frames, up to the phase of the step. -/
theorem frameRot_spec (U W : Vector Pend n) (q : Fin n) (A : Axis) (a : PiLin) :
    prodOn (stF (frameRot U W q A a).2.2.1) (List.finRange n) *
        prodOn (stF (frameRot U W q A a).2.2.2) (List.finRange n) *
        qelibListMatrix (frameRot U W q A a).1 =
      Complex.exp (Complex.I * (frameRot U W q A a).2.1.toReal) •
        (embedGate1 n q (axisMat A a.toReal) *
          (prodOn (stF U) (List.finRange n) * prodOn (stF W) (List.finRange n))) := by
  set r := frameLocal (stF U q) (stF W q) A a with hr
  have h1 := prodOn_layers (setF q r.2.2.1 (stF U)) (setF q r.2.2.2 (stF W)) q
  rw [setF_setF_self, setF_setF_self, setF_self, setF_self] at h1
  have hc := (commute_embedGate1_prodOn_setF_none q (axisMat A a.toReal) (stF U)
    (List.finRange n)).mul_right
    (commute_embedGate1_prodOn_setF_none q (axisMat A a.toReal) (stF W) (List.finRange n))
  simp only [frameRot, ← hr]
  rw [stF_setQ, stF_setQ, h1, prodOn_layers (stF U) (stF W) q, qelibListMatrix_onQ, mul_assoc,
    embedGate1_mul, hr, frameLocal_spec, embedGate1_smul, ← hr, Matrix.mul_smul]
  congr 1
  rw [← mul_assoc (embedGate1 n q _), hc.eq, ← embedGate1_mul n q (axisMat A a.toReal)]
  simp only [mul_assoc]

/-- One step of `frameRot` emits and keeps at most one statement more than it held. -/
theorem frameRot_length (U W : Vector Pend n) (q : Fin n) (A : Axis) (a : PiLin) :
    (frameRot U W q A a).1.length + sizeOn (stF (frameRot U W q A a).2.2.1) (List.finRange n) +
        sizeOn (stF (frameRot U W q A a).2.2.2) (List.finRange n) ≤
      1 + sizeOn (stF U) (List.finRange n) + sizeOn (stF W) (List.finRange n) := by
  have hL := List.nodup_finRange n
  have hu := sizeOn_extract (stF U) hL (List.mem_finRange q)
  have hw := sizeOn_extract (stF W) hL (List.mem_finRange q)
  have h := frameLocal_length (stF U q) (stF W q) A a
  simp only [frameRot, onQ, List.length_map]
  rw [stF_setQ, stF_setQ, sizeOn_setF (stF U) q, sizeOn_setF (stF W) q]
  omega

/-- A matrix commuting with the entries off `c` and `t` commutes with a layer that is empty at
`c` and `t`. -/
theorem commute_prodOn_of_none {X : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} {F : Fin n → Pend}
    {c t : Fin n} (hc : F c = none) (ht : F t = none)
    (hX : ∀ i, i ≠ c → i ≠ t → ∀ e, Commute X (entryMat i e)) (L : List (Fin n)) :
    Commute X (prodOn F L) := by
  refine commute_prodOn fun i _ => ?_
  by_cases hic : i = c
  · subst hic; rw [hc]; exact Commute.one_right _
  by_cases hit : i = t
  · subst hit; rw [ht]; exact Commute.one_right _
  exact hX i hic hit _

/-- One step of the Clifford frame scan: a rotation goes through `frameRot`. Before a `cx` on
distinct qubits the inner frames on its qubits are emitted and the outer ones go through the
step of `fuseQ` (`step`), which keeps a diagonal frame on the control and an `rx` on the target;
before any other statement both layers are emitted. -/
def frameStep (U W : Vector Pend n) (g : QGate n) :
    List (QGate n) × PiLin × Vector Pend n × Vector Pend n :=
  match axis? g with
  | some (q, A, a) => frameRot U W q A a
  | none =>
    match g with
    | .cx c t =>
      if c = t then
        (flushOn (stF W) (List.finRange n) ++ (step U g).1, 0, (step U g).2,
          Vector.replicate n none)
      else
        (emit t (stF W t) ++ emit c (stF W c) ++ (step U g).1, 0, (step U g).2,
          setQ (setQ W t none) c none)
    | _ =>
      (flushOn (stF W) (List.finRange n) ++ (step U g).1, 0, (step U g).2,
        Vector.replicate n none)

/-- One step of the Clifford frame scan: the next frames after the emitted statements realise
the input statement after the frames, up to the phase of the step. -/
theorem frameStep_spec (U W : Vector Pend n) (g : QGate n) :
    prodOn (stF (frameStep U W g).2.2.1) (List.finRange n) *
        prodOn (stF (frameStep U W g).2.2.2) (List.finRange n) *
        qelibListMatrix (frameStep U W g).1 =
      Complex.exp (Complex.I * (frameStep U W g).2.1.toReal) •
        (qelibMatrix g *
          (prodOn (stF U) (List.finRange n) * prodOn (stF W) (List.finRange n))) := by
  have hL := List.nodup_finRange n
  unfold frameStep
  split
  · next q A a hg =>
    rw [eq_mkQ_of_axis? hg, qelibMatrix_mkQ]
    exact frameRot_spec U W q A a
  · next hg =>
    split
    · next c t =>
      have hs := step_spec U (.cx c t)
      split
      · simp only [stF_replicate, prodOn_none, mul_one, QrunchBasis.qelibListMatrix_append,
          qelibListMatrix_flushOn, PiLin.toReal_zero, Complex.ofReal_zero, mul_zero,
          Complex.exp_zero, one_smul]
        rw [← mul_assoc, hs, mul_assoc]
      · next hct =>
        set F := stF W
        have hxt := prodOn_extract F hL (List.mem_finRange t)
        have hxc := prodOn_extract (setF t none F) hL (List.mem_finRange c)
        have htc : setF t none F c = F c := by simp [setF, hct]
        rw [htc] at hxc
        have hW : stF (setQ (setQ W t none) c none) = setF c none (setF t none F) := by
          rw [stF_setQ, stF_setQ]
        have hstep : (step U (.cx c t)).1 =
            emit t (tgtEmit U[t]) ++ emit c (ctrlEmit U[c]) ++ [.cx c t] := by
          simp [step, axis?, hct]
        set P := prodOn (setF c none (setF t none F)) (List.finRange n)
        have hcP : Commute (qelibListMatrix (step U (.cx c t)).1) P := by
          have hn1 : setF c none (setF t none F) c = none := setF_self _ _ _
          have hn2 : setF c none (setF t none F) t = none := by
            simp [setF, Ne.symm hct]
          rw [hstep, QrunchBasis.qelibListMatrix_append, QrunchBasis.qelibListMatrix_append,
            qelibListMatrix_emit, qelibListMatrix_emit]
          simp only [qelibListMatrix, Matrix.one_mul]
          refine Commute.mul_left ?_ (Commute.mul_left ?_ ?_)
          · exact commute_prodOn_of_none hn1 hn2
              (fun i hic hit e => commute_cx_entryMat hct hic hit e) _
          · exact commute_prodOn_of_none hn1 hn2
              (fun i hic _ e => commute_entryMat hic _ _) _
          · exact commute_prodOn_of_none hn1 hn2
              (fun i _ hit e => commute_entryMat hit _ _) _
        simp only [PiLin.toReal_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul]
        rw [hW, hxt, hxc, QrunchBasis.qelibListMatrix_append, QrunchBasis.qelibListMatrix_append,
          qelibListMatrix_emit, qelibListMatrix_emit]
        calc _ = prodOn (stF (step U (.cx c t)).2) (List.finRange n) *
              (P * qelibListMatrix (step U (.cx c t)).1) * entryMat c (F c) * entryMat t (F t) := by
              simp only [mul_assoc]; rfl
          _ = prodOn (stF (step U (.cx c t)).2) (List.finRange n) *
              (qelibListMatrix (step U (.cx c t)).1 * P) * entryMat c (F c) * entryMat t (F t) := by
              rw [← hcP.eq]
          _ = _ := by rw [← mul_assoc, hs]; simp only [mul_assoc]
    · have hs := step_spec U g
      simp only [stF_replicate, prodOn_none, mul_one, QrunchBasis.qelibListMatrix_append,
        qelibListMatrix_flushOn, PiLin.toReal_zero, Complex.ofReal_zero, mul_zero,
        Complex.exp_zero, one_smul]
      rw [← mul_assoc, hs, mul_assoc]

/-- One step of the Clifford frame scan emits and keeps at most one statement more than it
held. -/
theorem frameStep_length (U W : Vector Pend n) (g : QGate n) :
    (frameStep U W g).1.length + sizeOn (stF (frameStep U W g).2.2.1) (List.finRange n) +
        sizeOn (stF (frameStep U W g).2.2.2) (List.finRange n) ≤
      1 + sizeOn (stF U) (List.finRange n) + sizeOn (stF W) (List.finRange n) := by
  have hL := List.nodup_finRange n
  unfold frameStep
  split
  · exact frameRot_length _ _ _ _ _
  · next hg =>
    have hf := length_flushOn_le (stF W) (List.finRange n)
    split
    · next c t =>
      have hs := step_length U (.cx c t)
      split
      · simp only [List.length_append, stF_replicate, sizeOn_none]
        omega
      · next hct =>
        have hxt := sizeOn_extract (stF W) hL (List.mem_finRange t)
        have hxc := sizeOn_extract (setF t none (stF W)) hL (List.mem_finRange c)
        have htc : setF t none (stF W) c = stF W c := by simp [setF, hct]
        rw [htc] at hxc
        have h1 := length_emit_le t (stF W t)
        have h2 := length_emit_le c (stF W c)
        rw [stF_setQ, stF_setQ]
        simp only [List.length_append]
        omega
    · have hs := step_length U g
      simp only [List.length_append, stF_replicate, sizeOn_none]
      omega

/-- One step of the Clifford frame scan emits the `cx` of its input statement and no other. -/
theorem frameStep_cxCount (U W : Vector Pend n) (g : QGate n) :
    cxCount (frameStep U W g).1 = cxCount [g] := by
  unfold frameStep
  split
  · next q A a hg =>
    rw [frameRot, cxCount_onQ, eq_mkQ_of_axis? hg]
    cases A <;> rfl
  · next hg =>
    have hf := cxCount_flushOn (stF W) (List.finRange n)
    simp only [cxCount] at hf
    split
    · next c t =>
      have hs := step_cxCount U (.cx c t)
      have ht := cxCount_emit t (stF W t)
      have hc := cxCount_emit c (stF W c)
      simp only [cxCount] at hs ht hc
      split <;> simp only [cxCount, List.countP_append, hf, ht, hc, hs, zero_add]
    · have hs := step_cxCount U g
      simp only [cxCount] at hs
      simp only [cxCount, List.countP_append, hf, hs, zero_add]

/-- The Clifford frame scan from the frame `(U, W)`: the statements and the sum of the phases of
its steps; at the end every frame is emitted. -/
def frameAux : Vector Pend n → Vector Pend n → List (QGate n) → List (QGate n) × PiLin
  | U, W, [] => (flushOn (stF W) (List.finRange n) ++ flushOn (stF U) (List.finRange n), 0)
  | U, W, g :: gs =>
    let s := frameStep U W g
    let r := frameAux s.2.2.1 s.2.2.2 gs
    (s.1 ++ r.1, s.2.1 + r.2)

/-- **The one-qubit Clifford frame pass.** It scans a statement list and keeps, for each qubit, a
pending Clifford as a word of at most two rotations by `±π/2` or `π` about `x`, `y` and `p`.
A rotation by a multiple of `π/2` is multiplied into it (the shortest word of the product), and
every other rotation is emitted conjugated through it: about the permuted axis, the angle
negated when the frame negates the axis. Before a `cx` the frame on each of its qubits is
emitted, except an outer diagonal rotation on the control and an outer `rx` on the target;
every other statement emits the frames. The second component is the global phase of the
rewrite. -/
def pauliQ (l : List (QGate n)) : List (QGate n) × PiLin :=
  frameAux (Vector.replicate n none) (Vector.replicate n none) l

/-- The scan from `(U, W)` realises the input after the frames, up to its phase. -/
theorem qelibListMatrix_frameAux (l : List (QGate n)) :
    ∀ U W : Vector Pend n, qelibListMatrix (frameAux U W l).1 =
      Complex.exp (Complex.I * (frameAux U W l).2.toReal) •
        (qelibListMatrix l *
          (prodOn (stF U) (List.finRange n) * prodOn (stF W) (List.finRange n))) := by
  induction l with
  | nil =>
    intro U W
    simp [frameAux, qelibListMatrix, qelibListMatrix_flushOn, QrunchBasis.qelibListMatrix_append]
  | cons g gs ih =>
    intro U W
    have hs := frameStep_spec U W g
    simp only [frameAux, QrunchBasis.qelibListMatrix_append, ih, qelibListMatrix,
      Matrix.smul_mul, mul_assoc] at hs ⊢
    rw [hs, Matrix.mul_smul, smul_smul, PiLin.toReal_add, Complex.ofReal_add, mul_add,
      Complex.exp_add, mul_comm (Complex.exp _)]

/-- **The pass is exact up to its phase**: the statements of `pauliQ l` have the matrix of `l`
times `e^{iφ}` for the phase `φ` it returns. -/
theorem qelibListMatrix_pauliQ (l : List (QGate n)) :
    qelibListMatrix (pauliQ l).1 =
      Complex.exp (Complex.I * (pauliQ l).2.toReal) • qelibListMatrix l := by
  rw [pauliQ, qelibListMatrix_frameAux, stF_replicate, prodOn_none, mul_one, mul_one]

/-- The scan from `(U, W)` emits at most the input and the frames. -/
theorem length_frameAux_le (l : List (QGate n)) :
    ∀ U W : Vector Pend n, (frameAux U W l).1.length ≤
      l.length + sizeOn (stF U) (List.finRange n) + sizeOn (stF W) (List.finRange n) := by
  induction l with
  | nil =>
    intro U W
    have h1 := length_flushOn_le (stF U) (List.finRange n)
    have h2 := length_flushOn_le (stF W) (List.finRange n)
    simp only [frameAux, List.length_append, List.length_nil]
    omega
  | cons g gs ih =>
    intro U W
    have h1 := ih (frameStep U W g).2.2.1 (frameStep U W g).2.2.2
    have h2 := frameStep_length U W g
    simp only [frameAux, List.length_append, List.length_cons]
    omega

/-- **The pass does not lengthen the list.** -/
theorem length_pauliQ_le (l : List (QGate n)) : (pauliQ l).1.length ≤ l.length := by
  simpa [pauliQ, stF_replicate, sizeOn_none] using
    length_frameAux_le l (Vector.replicate n none) (Vector.replicate n none)

/-- The scan emits exactly the `cx` statements of its input. -/
theorem cxCount_frameAux (l : List (QGate n)) :
    ∀ U W : Vector Pend n, cxCount (frameAux U W l).1 = cxCount l := by
  induction l with
  | nil =>
    intro U W
    simp only [frameAux, cxCount, List.countP_append]
    have h1 := cxCount_flushOn (stF U) (List.finRange n)
    have h2 := cxCount_flushOn (stF W) (List.finRange n)
    simp only [cxCount] at h1 h2
    simp [h1, h2]
  | cons g gs ih =>
    intro U W
    have h1 := ih (frameStep U W g).2.2.1 (frameStep U W g).2.2.2
    have h2 := frameStep_cxCount U W g
    simp only [frameAux, cxCount, List.countP_append, List.countP_cons,
      List.countP_nil] at h1 h2 ⊢
    omega

/-- **The pass keeps every `cx` statement.** -/
theorem cxCount_pauliQ (l : List (QGate n)) : cxCount (pauliQ l).1 = cxCount l :=
  cxCount_frameAux l _ _

/-! ## The scan over a sparse state

`fuseQ` keeps the pending rotations of all `n` qubits in a vector, which costs `n` to create
and to flush, so a short list on many qubits costs `n`. `fuseQM` keeps only the present
pending rotations, in a map ordered by qubit, and flushes its keys in increasing order. It
computes `fuseQ` (`fuseQ_eq_fuseQM`), which it replaces in compiled code. -/

/-- A sparse scan state: the present pending rotations, by qubit. -/
abbrev PendMap (n : ℕ) := Std.TreeMap (Fin n) (Axis × PiLin)

/-- The sparse state `m` with value `x` at `q`. -/
def putM (m : PendMap n) (q : Fin n) : Pend → PendMap n
  | none => m.erase q
  | some e => m.insert q e

/-- The statements emitting the pending rotations of a sparse state, in qubit order. -/
def flushM (m : PendMap n) : List (QGate n) := m.keys.flatMap fun q => emit q m[q]?

/-- `step` over a sparse state. -/
def stepM (m : PendMap n) (g : QGate n) : List (QGate n) × PendMap n :=
  match axis? g with
  | some (q, A, a) =>
    match m[q]? with
    | some (B, b) =>
      if A = B then ([], putM m q (some (A, b + a)))
      else (emit q (some (B, b)), putM m q (some (A, a)))
    | none => ([], putM m q (some (A, a)))
  | none =>
    match g with
    | .cx c t =>
      if c = t then (flushM m ++ [g], ∅)
      else (emit t (tgtEmit m[t]?) ++ emit c (ctrlEmit m[c]?) ++ [g],
        putM (putM m t (tgtKeep m[t]?)) c (ctrlKeep m[c]?))
    | _ => (flushM m ++ [g], ∅)

/-- The scan of `fuseQ` over a sparse state. -/
def fuseAuxM : PendMap n → List (QGate n) → List (QGate n)
  | m, [] => flushM m
  | m, g :: gs =>
    let s := stepM m g
    s.1 ++ fuseAuxM s.2 gs

/-- `fuseQ` over a sparse state. -/
def fuseQM (l : List (QGate n)) : List (QGate n) := fuseAuxM ∅ l

/-- The sparse state `m` holds the pending rotations of the state `v`. -/
def RelM (m : PendMap n) (v : Vector Pend n) : Prop := ∀ q, m[q]? = stF v q

theorem relM_empty : RelM (∅ : PendMap n) (Vector.replicate n none) := by
  intro q
  simp [stF]

theorem relM_putM {m : PendMap n} {v : Vector Pend n} (h : RelM m v) (q : Fin n) (x : Pend) :
    RelM (putM m q x) (setQ v q x) := by
  intro p
  rw [stF_setQ, setF, ← h p]
  cases x <;> simp only [putM, Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert,
    compare_eq_iff_eq] <;> grind

theorem flushOn_filter (F : Fin n → Pend) (p : Fin n → Bool) (L : List (Fin n))
    (h : ∀ q ∈ L, p q = false → F q = none) : flushOn F (L.filter p) = flushOn F L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have ih := ih fun q hq => h q (List.mem_cons_of_mem a hq)
    by_cases ha : p a = true
    · simp_all [flushOn]
    · simp_all [flushOn, h a List.mem_cons_self, emit]

theorem flushM_eq {m : PendMap n} {v : Vector Pend n} (h : RelM m v) :
    flushM m = flushOn (stF v) (List.finRange n) := by
  have hk : (List.finRange n).filter (fun q => decide (q ∈ m.keys)) = m.keys := by
    refine List.Pairwise.eq_of_mem_iff (r := (· < ·))
      ((List.sortedLT_finRange n).pairwise.filter _) ?_ fun q => by simp
    exact Std.TreeMap.ordered_keys.imp fun hab => by simpa [compare_lt_iff_lt] using hab
  rw [flushM, ← hk, ← flushOn_filter (stF v) (fun q => decide (q ∈ m.keys))]
  · simp only [flushOn, hk]
    exact List.flatMap_congr fun q _ => by rw [h q]
  · intro q _ hq
    rw [← h q]
    exact Std.TreeMap.getElem?_eq_none fun hm => by simp_all [Std.TreeMap.mem_keys]

theorem stepM_spec {m : PendMap n} {v : Vector Pend n} (h : RelM m v) (g : QGate n) :
    (stepM m g).1 = (step v g).1 ∧ RelM (stepM m g).2 (step v g).2 := by
  unfold stepM step
  split
  · next q A a _ =>
    rw [show m[q]? = v[q] from h q]
    generalize v[q] = e
    rcases e with _ | ⟨B, b⟩
    · exact ⟨rfl, relM_putM h _ _⟩
    · dsimp only
      split
      · exact ⟨rfl, relM_putM h _ _⟩
      · exact ⟨rfl, relM_putM h _ _⟩
  · split
    · next c t _ =>
      rw [show m[t]? = v[t] from h t, show m[c]? = v[c] from h c]
      split_ifs
      · exact ⟨by rw [flushM_eq h], relM_empty⟩
      · exact ⟨rfl, relM_putM (relM_putM h _ _) _ _⟩
    · exact ⟨by rw [flushM_eq h], relM_empty⟩

theorem fuseAuxM_eq (l : List (QGate n)) :
    ∀ (m : PendMap n) (v : Vector Pend n), RelM m v → fuseAuxM m l = fuseAux v l := by
  induction l with
  | nil => intro m v h; rw [fuseAuxM, fuseAux, flushM_eq h]
  | cons g gs ih =>
    intro m v h
    obtain ⟨h1, h2⟩ := stepM_spec h g
    rw [fuseAuxM, fuseAux, h1, ih _ _ h2]

/-- `fuseQM` computes `fuseQ`, and replaces it in compiled code. -/
@[csimp] theorem fuseQ_eq_fuseQM : @fuseQ = @fuseQM := by
  funext n l
  rw [fuseQ, fuseQM, fuseAuxM_eq l _ _ relM_empty]

end CatCrypt.Quantum.QrunchFuse
