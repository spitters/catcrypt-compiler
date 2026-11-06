/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QrunchFuse

/-!
# Exact shortening of three-gate one-qubit runs

`shortQ` scans a statement list in the basis `{rx, ry, rz, cx, p}` and keeps, for each qubit,
the last one or two rotations of its one-qubit run, as the two layers of the Clifford frame scan
of `QrunchFuse` (the outer one applied last). A new rotation about the axis of the outer pending
one is merged into it. Otherwise, when the outer pending rotation is a Clifford rotation (its
angle a multiple of `π/2`), the run of three rotations is rewritten into an Euler form of two:
the new rotation is pushed backward through the Clifford rotation, or the inner one forward,
and when its conjugated axis is that of the rotation on the far side the two merge. Otherwise
the inner pending rotation is emitted. Statements other than rotations go through the step of
the Clifford frame scan (`frameStep`), which emits the pending rotations they do not commute
with.

The rewrite is exact up to a global phase: a rotation conjugated by a Clifford rotation is a
rotation about the conjugated Pauli axis, the angle negated when the axis is (`conj_spec`;
`S Rx(θ) S† = Ry(θ)`, `X Rz(θ) X = Rz(−θ)`), and rotations about one axis compose by adding
angles. The conjugation is computed exactly over `ℤ[e^{iπ/4}]`, as in the Clifford frame pass.

## Main results

* `shortQ` — the pass, returning the statements and the global phase of the rewrite.
* `qelibListMatrix_shortQ` — exact up to the phase it returns.
* `length_shortQ_le` — the pass does not lengthen the list.
* `cxCount_shortQ` — it emits exactly the `cx` statements it reads.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.OpenQASMImport
open CatCrypt.Quantum.Qelib
open CatCrypt.Quantum.QrunchFuse
open CatCrypt.Quantum.QrunchFuse.M2

namespace CatCrypt.Quantum.QrunchShort

variable {n : ℕ}

/-! ## Rewrites of a one-qubit run -/

/-- The rotation about `A` by `a` after the rotation `e`, merged into one rotation when the axes
agree. -/
def mergeAx (e : Axis × PiLin) (A : Axis) (a : PiLin) : Option (Axis × PiLin) :=
  if e.1 = A then some (A, a + e.2) else none

/-- A merged rotation is the product of the two. -/
theorem mergeAx_spec {e r : Axis × PiLin} {A : Axis} {a : PiLin} (h : mergeAx e A a = some r) :
    axisMat r.1 r.2.toReal = axisMat A a.toReal * axisMat e.1 e.2.toReal := by
  unfold mergeAx at h
  split_ifs at h with he
  simp only [Option.some.injEq] at h
  subst h
  rw [PiLin.toReal_add, axisMat_add, he]

/-- The rotation about `A` by `a` after the Clifford rotation `c` after the rotation `e`: the
rotation is pushed backward through `c` and merged into `e`. The result is the merged rotation
and the phase. -/
def pushBack (e c : Axis × PiLin) (A : Axis) (a : PiLin) : Option (Axis × PiLin × PiLin) :=
  match halfPiMul? c.2 with
  | none => none
  | some m =>
    match conjAx? (repRot c.1 m) A with
    | none => none
    | some (B, neg) =>
      (mergeAx e (emAx A B) (if neg then -a else a)).map fun r =>
        (r.1, r.2, pShift (emAx A B) (if neg then -a else a) - pShift A a)

/-- **Pushing backward is exact up to its phase**: `c` after the merged rotation is the run. -/
theorem pushBack_spec {e c : Axis × PiLin} {A B : Axis} {a b φ : PiLin}
    (h : pushBack e c A a = some (B, b, φ)) :
    axisMat c.1 c.2.toReal * axisMat B b.toReal =
      Complex.exp (Complex.I * φ.toReal) •
        (axisMat A a.toReal * (axisMat c.1 c.2.toReal * axisMat e.1 e.2.toReal)) := by
  unfold pushBack at h
  split at h
  · simp at h
  · next m hm =>
    split at h
    · simp at h
    · next B' neg hB =>
      obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hF : toM (repRot c.1 m) = (2 : ℂ) ^ (m % 4).toNat • axisMat c.1 c.2.toReal := by
        rw [toM_repRot, toReal_of_halfPiMul? hm]
      rw [mergeAx_spec hr, ← mul_assoc, conj_spec hB hF a, Matrix.smul_mul, mul_assoc]

/-- The rotation about `A` by `a` after the Clifford rotation `c` after the rotation `e`: `e` is
pushed forward through `c` and merged into the rotation about `A`. The result is the merged
rotation and the phase. -/
def pushFwd (e c : Axis × PiLin) (A : Axis) (a : PiLin) : Option (Axis × PiLin × PiLin) :=
  match halfPiMul? c.2 with
  | none => none
  | some m =>
    match conjAx? (repRot c.1 (-m)) e.1 with
    | none => none
    | some (B, neg) =>
      (mergeAx (emAx e.1 B, if neg then -e.2 else e.2) A a).map fun r =>
        (r.1, r.2, pShift (emAx e.1 B) (if neg then -e.2 else e.2) - pShift e.1 e.2)

/-- **Pushing forward is exact up to its phase**: the merged rotation after `c` is the run. -/
theorem pushFwd_spec {e c : Axis × PiLin} {A B : Axis} {a b φ : PiLin}
    (h : pushFwd e c A a = some (B, b, φ)) :
    axisMat B b.toReal * axisMat c.1 c.2.toReal =
      Complex.exp (Complex.I * φ.toReal) •
        (axisMat A a.toReal * (axisMat c.1 c.2.toReal * axisMat e.1 e.2.toReal)) := by
  unfold pushFwd at h
  split at h
  · simp at h
  · next m hm =>
    split at h
    · simp at h
    · next B' neg hB =>
      obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hF := toM_repRot c.1 (-m)
      have hc := conj_spec hB hF e.2
      have hWV : axisMat c.1 c.2.toReal * axisMat c.1 (((-m : ℤ) : ℝ) * (Real.pi / 2)) = 1 := by
        rw [toReal_of_halfPiMul? hm, ← axisMat_add,
          show (m : ℝ) * (Real.pi / 2) + ((-m : ℤ) : ℝ) * (Real.pi / 2) = 0 by push_cast; ring,
          axisMat_zero]
      have hVW : axisMat c.1 (((-m : ℤ) : ℝ) * (Real.pi / 2)) * axisMat c.1 c.2.toReal = 1 := by
        rw [toReal_of_halfPiMul? hm, ← axisMat_add,
          show ((-m : ℤ) : ℝ) * (Real.pi / 2) + (m : ℝ) * (Real.pi / 2) = 0 by push_cast; ring,
          axisMat_zero]
      have hk : axisMat (emAx e.1 B') (if neg then -e.2 else e.2).toReal *
          axisMat c.1 c.2.toReal =
          Complex.exp (Complex.I * (pShift (emAx e.1 B') (if neg then -e.2 else e.2) -
            pShift e.1 e.2).toReal) • (axisMat c.1 c.2.toReal * axisMat e.1 e.2.toReal) := by
        calc _ = axisMat c.1 c.2.toReal * (axisMat c.1 (((-m : ℤ) : ℝ) * (Real.pi / 2)) *
              axisMat (emAx e.1 B') (if neg then -e.2 else e.2).toReal) *
              axisMat c.1 c.2.toReal := by
              rw [← mul_assoc (axisMat c.1 c.2.toReal), hWV, one_mul]
          _ = _ := by
              rw [hc, Matrix.mul_smul, Matrix.smul_mul]
              simp only [mul_assoc, hVW, mul_one]
      rw [mergeAx_spec hr, mul_assoc, hk, Matrix.mul_smul]

/-- One rotation about `A` by `a` against the pending run `(u, w)` of its qubit, `u` after `w`:
the rotations it emits, the phase and the next pending run. The rotation is merged into `u`
when the axes agree; else, with two pending rotations, the run of three is shortened to two by
`pushBack` or `pushFwd`; else the inner pending rotation is emitted. -/
def runLocal (u w : Pend) (A : Axis) (a : PiLin) :
    List (Axis × PiLin) × PiLin × Pend × Pend :=
  match u, w with
  | none, none => ([], 0, some (A, a), none)
  | some e, none =>
    match mergeAx e A a with
    | some r => ([], 0, some r, none)
    | none => ([], 0, some (A, a), some e)
  | none, some e =>
    match mergeAx e A a with
    | some r => ([], 0, some r, none)
    | none => ([], 0, some (A, a), some e)
  | some c, some e =>
    match mergeAx c A a with
    | some r => ([], 0, some r, some e)
    | none =>
      match pushBack e c A a with
      | some (B, b, φ) => ([], φ, some c, some (B, b))
      | none =>
        match pushFwd e c A a with
        | some (B, b, φ) => ([], φ, some (B, b), some c)
        | none => ([e], 0, some (A, a), some c)

/-- One local step: the next pending run after the emitted rotations is the rotation after the
pending run, up to the phase of the step. -/
theorem runLocal_spec (u w : Pend) (A : Axis) (a : PiLin) :
    frameMat (runLocal u w A a).2.2.1 * frameMat (runLocal u w A a).2.2.2 *
        listMat (runLocal u w A a).1 =
      Complex.exp (Complex.I * (runLocal u w A a).2.1.toReal) •
        (axisMat A a.toReal * (frameMat u * frameMat w)) := by
  unfold runLocal
  split
  · simp [frameMat, listMat]
  · split
    · next r hr => simp [frameMat, listMat, mergeAx_spec hr]
    · simp [frameMat, listMat]
  · split
    · next r hr => simp [frameMat, listMat, mergeAx_spec hr]
    · simp [frameMat, listMat]
  · split
    · next r hr => simp [frameMat, listMat, mergeAx_spec hr, mul_assoc]
    · split
      · next B b φ hp =>
        simp only [frameMat, listMat, mul_one]
        exact pushBack_spec hp
      · split
        · next B b φ hp =>
          simp only [frameMat, listMat, mul_one]
          exact pushFwd_spec hp
        · simp [frameMat, listMat, mul_assoc]

/-- One local step emits and keeps at most one rotation more than the pending run held. -/
theorem runLocal_length (u w : Pend) (A : Axis) (a : PiLin) :
    (runLocal u w A a).1.length + wt (runLocal u w A a).2.2.1 +
        wt (runLocal u w A a).2.2.2 ≤ 1 + wt u + wt w := by
  unfold runLocal
  split <;> (try split) <;> (try split) <;> (try split) <;> simp [wt]

/-! ## The scan over all qubits -/

/-- One rotation statement about `A` by `a` on `q` against the pending runs `(U, W)`
(`runLocal`). -/
def shortRot (U W : Vector Pend n) (q : Fin n) (A : Axis) (a : PiLin) :
    List (QGate n) × PiLin × Vector Pend n × Vector Pend n :=
  let r := runLocal (stF U q) (stF W q) A a
  (onQ q r.1, r.2.1, setQ U q r.2.2.1, setQ W q r.2.2.2)

/-- One step of `shortRot`: the next pending runs after the emitted statements realise the
rotation after the pending runs, up to the phase of the step. -/
theorem shortRot_spec (U W : Vector Pend n) (q : Fin n) (A : Axis) (a : PiLin) :
    prodOn (stF (shortRot U W q A a).2.2.1) (List.finRange n) *
        prodOn (stF (shortRot U W q A a).2.2.2) (List.finRange n) *
        qelibListMatrix (shortRot U W q A a).1 =
      Complex.exp (Complex.I * (shortRot U W q A a).2.1.toReal) •
        (embedGate1 n q (axisMat A a.toReal) *
          (prodOn (stF U) (List.finRange n) * prodOn (stF W) (List.finRange n))) := by
  set r := runLocal (stF U q) (stF W q) A a with hr
  have h1 := prodOn_layers (setF q r.2.2.1 (stF U)) (setF q r.2.2.2 (stF W)) q
  rw [setF_setF_self, setF_setF_self, setF_self, setF_self] at h1
  have hc := (commute_embedGate1_prodOn_setF_none q (axisMat A a.toReal) (stF U)
    (List.finRange n)).mul_right
    (commute_embedGate1_prodOn_setF_none q (axisMat A a.toReal) (stF W) (List.finRange n))
  simp only [shortRot, ← hr]
  rw [stF_setQ, stF_setQ, h1, prodOn_layers (stF U) (stF W) q, qelibListMatrix_onQ, mul_assoc,
    embedGate1_mul, hr, runLocal_spec, embedGate1_smul, ← hr, Matrix.mul_smul]
  congr 1
  rw [← mul_assoc (embedGate1 n q _), hc.eq, ← embedGate1_mul n q (axisMat A a.toReal)]
  simp only [mul_assoc]

/-- One step of `shortRot` emits and keeps at most one statement more than it held. -/
theorem shortRot_length (U W : Vector Pend n) (q : Fin n) (A : Axis) (a : PiLin) :
    (shortRot U W q A a).1.length + sizeOn (stF (shortRot U W q A a).2.2.1) (List.finRange n) +
        sizeOn (stF (shortRot U W q A a).2.2.2) (List.finRange n) ≤
      1 + sizeOn (stF U) (List.finRange n) + sizeOn (stF W) (List.finRange n) := by
  have hL := List.nodup_finRange n
  have hu := sizeOn_extract (stF U) hL (List.mem_finRange q)
  have hw := sizeOn_extract (stF W) hL (List.mem_finRange q)
  have h := runLocal_length (stF U q) (stF W q) A a
  simp only [shortRot, onQ, List.length_map]
  rw [stF_setQ, stF_setQ, sizeOn_setF (stF U) q, sizeOn_setF (stF W) q]
  omega

/-- One step of the scan: a rotation goes through `shortRot`, every other statement through the
step of the Clifford frame scan (`frameStep`). -/
def shortStep (U W : Vector Pend n) (g : QGate n) :
    List (QGate n) × PiLin × Vector Pend n × Vector Pend n :=
  match axis? g with
  | some (q, A, a) => shortRot U W q A a
  | none => frameStep U W g

/-- One step of the scan: the next pending runs after the emitted statements realise the input
statement after the pending runs, up to the phase of the step. -/
theorem shortStep_spec (U W : Vector Pend n) (g : QGate n) :
    prodOn (stF (shortStep U W g).2.2.1) (List.finRange n) *
        prodOn (stF (shortStep U W g).2.2.2) (List.finRange n) *
        qelibListMatrix (shortStep U W g).1 =
      Complex.exp (Complex.I * (shortStep U W g).2.1.toReal) •
        (qelibMatrix g *
          (prodOn (stF U) (List.finRange n) * prodOn (stF W) (List.finRange n))) := by
  unfold shortStep
  split
  · next q A a hg =>
    rw [eq_mkQ_of_axis? hg, qelibMatrix_mkQ]
    exact shortRot_spec U W q A a
  · exact frameStep_spec U W g

/-- One step of the scan emits and keeps at most one statement more than it held. -/
theorem shortStep_length (U W : Vector Pend n) (g : QGate n) :
    (shortStep U W g).1.length + sizeOn (stF (shortStep U W g).2.2.1) (List.finRange n) +
        sizeOn (stF (shortStep U W g).2.2.2) (List.finRange n) ≤
      1 + sizeOn (stF U) (List.finRange n) + sizeOn (stF W) (List.finRange n) := by
  unfold shortStep
  split
  · exact shortRot_length _ _ _ _ _
  · exact frameStep_length U W g

/-- One step of the scan emits the `cx` of its input statement and no other. -/
theorem shortStep_cxCount (U W : Vector Pend n) (g : QGate n) :
    cxCount (shortStep U W g).1 = cxCount [g] := by
  unfold shortStep
  split
  · next q A a hg =>
    rw [shortRot, cxCount_onQ, eq_mkQ_of_axis? hg]
    cases A <;> rfl
  · exact frameStep_cxCount U W g

/-- The scan from the pending runs `(U, W)`: the statements and the sum of the phases of its
steps; at the end every pending rotation is emitted. -/
def shortAux : Vector Pend n → Vector Pend n → List (QGate n) → List (QGate n) × PiLin
  | U, W, [] => (flushOn (stF W) (List.finRange n) ++ flushOn (stF U) (List.finRange n), 0)
  | U, W, g :: gs =>
    let s := shortStep U W g
    let r := shortAux s.2.2.1 s.2.2.2 gs
    (s.1 ++ r.1, s.2.1 + r.2)

/-- **The run-shortening pass.** It scans a statement list and keeps, for each qubit, the last
one or two rotations of its one-qubit run. A rotation about the axis of the outer one is merged
into it; a run of three rotations whose middle one is a Clifford rotation and whose outer ones
become rotations about one axis when one is conjugated through the middle one is rewritten into
two; otherwise the inner pending rotation is emitted. The second component is the global phase
of the rewrite. -/
def shortQ (l : List (QGate n)) : List (QGate n) × PiLin :=
  shortAux (Vector.replicate n none) (Vector.replicate n none) l

/-- The scan from `(U, W)` realises the input after the pending runs, up to its phase. -/
theorem qelibListMatrix_shortAux (l : List (QGate n)) :
    ∀ U W : Vector Pend n, qelibListMatrix (shortAux U W l).1 =
      Complex.exp (Complex.I * (shortAux U W l).2.toReal) •
        (qelibListMatrix l *
          (prodOn (stF U) (List.finRange n) * prodOn (stF W) (List.finRange n))) := by
  induction l with
  | nil =>
    intro U W
    simp [shortAux, qelibListMatrix, qelibListMatrix_flushOn, QrunchBasis.qelibListMatrix_append]
  | cons g gs ih =>
    intro U W
    have hs := shortStep_spec U W g
    simp only [shortAux, QrunchBasis.qelibListMatrix_append, ih, qelibListMatrix,
      Matrix.smul_mul, mul_assoc] at hs ⊢
    rw [hs, Matrix.mul_smul, smul_smul, PiLin.toReal_add, Complex.ofReal_add, mul_add,
      Complex.exp_add, mul_comm (Complex.exp _)]

/-- **The pass is exact up to its phase**: the statements of `shortQ l` have the matrix of `l`
times `e^{iφ}` for the phase `φ` it returns. -/
theorem qelibListMatrix_shortQ (l : List (QGate n)) :
    qelibListMatrix (shortQ l).1 =
      Complex.exp (Complex.I * (shortQ l).2.toReal) • qelibListMatrix l := by
  rw [shortQ, qelibListMatrix_shortAux, stF_replicate, prodOn_none, mul_one, mul_one]

/-- The scan from `(U, W)` emits at most the input and the pending runs. -/
theorem length_shortAux_le (l : List (QGate n)) :
    ∀ U W : Vector Pend n, (shortAux U W l).1.length ≤
      l.length + sizeOn (stF U) (List.finRange n) + sizeOn (stF W) (List.finRange n) := by
  induction l with
  | nil =>
    intro U W
    have h1 := length_flushOn_le (stF U) (List.finRange n)
    have h2 := length_flushOn_le (stF W) (List.finRange n)
    simp only [shortAux, List.length_append, List.length_nil]
    omega
  | cons g gs ih =>
    intro U W
    have h1 := ih (shortStep U W g).2.2.1 (shortStep U W g).2.2.2
    have h2 := shortStep_length U W g
    simp only [shortAux, List.length_append, List.length_cons]
    omega

/-- **The pass does not lengthen the list.** -/
theorem length_shortQ_le (l : List (QGate n)) : (shortQ l).1.length ≤ l.length := by
  simpa [shortQ, stF_replicate, sizeOn_none] using
    length_shortAux_le l (Vector.replicate n none) (Vector.replicate n none)

/-- The scan emits exactly the `cx` statements of its input. -/
theorem cxCount_shortAux (l : List (QGate n)) :
    ∀ U W : Vector Pend n, cxCount (shortAux U W l).1 = cxCount l := by
  induction l with
  | nil =>
    intro U W
    simp only [shortAux, cxCount, List.countP_append]
    have h1 := cxCount_flushOn (stF U) (List.finRange n)
    have h2 := cxCount_flushOn (stF W) (List.finRange n)
    simp only [cxCount] at h1 h2
    simp [h1, h2]
  | cons g gs ih =>
    intro U W
    have h1 := ih (shortStep U W g).2.2.1 (shortStep U W g).2.2.2
    have h2 := shortStep_cxCount U W g
    simp only [shortAux, cxCount, List.countP_append, List.countP_cons,
      List.countP_nil] at h1 h2 ⊢
    omega

/-- **The pass keeps every `cx` statement.** -/
theorem cxCount_shortQ (l : List (QGate n)) : cxCount (shortQ l).1 = cxCount l :=
  cxCount_shortAux l _ _

end CatCrypt.Quantum.QrunchShort
