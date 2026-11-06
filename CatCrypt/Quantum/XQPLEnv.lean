/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.HQPL
public import CatCrypt.Quantum.Uncomputation
public import CatCrypt.Quantum.QRegister
public import CatCrypt.Quantum.QrunchExport

/-!
# Program-level environments of XQPL

The environments of a Qrisp-like language on measurement-free XQPL programs. Each takes the
exact gate list `XQPL.toGates` of its block and returns a program `XQPL.ofGates l` (or a
program of reversible atoms), whose unitary `XQPL.unitary` is stated by the gate-level
theorem of the construct:

* `XQPL.mcontrolled cs a p h` — Qrisp's `control(qbs)`: the AND of the controls `cs` is
  computed into the ancilla `a` by a multi-controlled `X`, the block is controlled on `a`,
  and the AND is uncomputed (`AndAncilla.ancillaCtrlGates`);
* `XQPL.withEq r v a p h` — Qrisp's `with r == v:` (`QRegister.Reg.withEq`);
* `XQPL.uncompute C U hC hU` — compute; use; uncompute over the reversible atoms
  `Uncomputation.RevOp n`, on programs over `Ops ⊕ RevOp n`; `XQPL.toRevOps` reads such a
  program as a list of atoms, an operation of `Ops` as the gate atoms of its gate list.

The operation set of the language is `RegisterOps n ⊕ RevOp n`; `RevOp n` has the
`OpDenote`, `OpGateList` and `OpGates` instances of its gate lists here; the environments
need only `OpGateList`, so the gate lists of their programs are computable. `XQPL.seq` sequences two programs,
and its unitary is the product (`XQPL.unitary_seq`).

A measurement-free program whose gate list has no real-angle `Rz` (`QrunchBasis.NoRz`)
exports to OpenQASM 2 through `QrunchExport.exportQASM`: the text read back realises the
unitary of the program times the exact global phase (`XQPL.qelibListMatrix_export_xqpl`).
`noRz_ctrlList`, `noRz_mctrlGates` and `noRz_invGates` carry `NoRz` through the constructs,
and `XQPL.noRz_seq`, `XQPL.noRz_mcontrolled` and `XQPL.noRz_withEq` through the environments.

## Main results

* `XQPL.unitary_mcontrolled`, `XQPL.unitary_withEq`, `XQPL.unitary_uncompute` — the unitary
  of each environment on ancilla `|0⟩`;
* `noRz_ctrlList`, `noRz_invGates` — control and inversion keep exact angles;
* `XQPL.qelibListMatrix_export_xqpl` — the export of a measurement-free program.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped Matrix
open CatCrypt.Quantum CatCrypt.Quantum.QCircuit CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.ControlledGates CatCrypt.Quantum.AndAncilla
open CatCrypt.Quantum.Uncomputation CatCrypt.Quantum.QRegister
open CatCrypt.Quantum.OpenQASMImport CatCrypt.Quantum.Qelib CatCrypt.Quantum.QrunchBasis
open CatCrypt.Quantum.OpenQASMBytes CatCrypt.Quantum.QrunchExport
open CatCrypt.Quantum.QFT (listMatrix listMatrix_append invGate invGates)

namespace CatCrypt.Quantum.QPL

variable {n : ℕ}

/-! ## The reversible atoms as operations -/

/-- A reversible atom denotes the circuit of its gate list. -/
instance instOpDenoteRevOp : OpDenote (RevOp n) n where
  denote o := GateUnitarity.unitaryDenote (Circuit.ofList o.gates)

/-- The gate list of a reversible atom is `RevOp.gates`. -/
instance instOpGateListRevOp : OpGateList (RevOp n) n where
  gates := RevOp.gates

/-- The exact gate list of a reversible atom is `RevOp.gates`. -/
instance instOpGatesRevOp : OpGates (RevOp n) n where
  toOpGateList := instOpGateListRevOp
  denote_eq _ := rfl

/-- `Avoids c g` is decidable. -/
instance instDecidableAvoids (c : Fin n) : DecidablePred (Avoids c) := fun g => by
  cases g <;> unfold Avoids <;> infer_instance

/-! ## Exact angles through the constructs -/

/-- A controlled gate of an exact-angle gate has exact angles. -/
theorem noRz_ctrlGates (c : Fin n) {g : Gate n} (hg : NoRz g) : ∀ g' ∈ ctrlGates c g, NoRz g' := by
  cases g <;> simp only [ctrlGates] <;> (try split) <;>
    simp_all [NoRz, cphaseGates, toffoliGates, cczPhaseGates, cnotConj]

/-- **Control keeps exact angles.** -/
theorem noRz_ctrlList (c : Fin n) {l : List (Gate n)} (hl : ∀ g ∈ l, NoRz g) :
    ∀ g ∈ ctrlList c l, NoRz g := by
  intro g' hg'
  obtain ⟨g, hg, hg'⟩ := List.mem_flatMap.mp hg'
  exact noRz_ctrlGates c (hl g hg) g' hg'

/-- A multi-controlled exact-angle gate has exact angles. -/
theorem noRz_mctrlGates {g : Gate n} (hg : NoRz g) :
    ∀ cs : List (Fin n), ∀ g' ∈ mctrlGates cs g, NoRz g'
  | [] => by simpa [mctrlGates] using hg
  | c :: cs => noRz_ctrlList c (noRz_mctrlGates hg cs)

/-- The inverse of an exact-angle gate has exact angles. -/
theorem noRz_invGate {g : Gate n} (hg : NoRz g) : NoRz (invGate g) := by
  cases g <;> simp_all [invGate, NoRz]

/-- **Inversion keeps exact angles.** -/
theorem noRz_invGates {l : List (Gate n)} (hl : ∀ g ∈ l, NoRz g) : ∀ g ∈ invGates l, NoRz g := by
  intro g' hg'
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hg')
  exact noRz_invGate (hl g hg)

/-- The ancilla construction of exact-angle lists has exact angles. -/
theorem noRz_ancillaCtrlGates {V U : List (Gate n)} (a : Fin n) (hV : ∀ g ∈ V, NoRz g)
    (hU : ∀ g ∈ U, NoRz g) : ∀ g ∈ ancillaCtrlGates V a U, NoRz g := by
  intro g hg
  simp only [ancillaCtrlGates, List.mem_append] at hg
  rcases hg with (h | h) | h
  · exact hV g h
  · exact noRz_ctrlList a hU g h
  · exact noRz_invGates hV g h

namespace XQPL

variable {Ops : Type} [OpGateList Ops n] {α β : Type}

/-! ## Sequencing -/

/-- `p`, then `q`, discarding the value of `p`. -/
def seq (p : XQPL Ops n α) (q : XQPL Ops n β) : XQPL Ops n β := p.bind fun _ => q

omit [OpGateList Ops n] in
theorem isMeasFree_seq {p : XQPL Ops n α} {q : XQPL Ops n β} (hp : p.isMeasFree)
    (hq : q.isMeasFree) : (seq p q).isMeasFree := by
  induction p with
  | ret a => exact hq
  | gate g k ih => exact ih hp
  | meas i kt kf _ _ => exact hp.elim
  | custom op k ih => exact ih hp
  | fail => exact hp.elim

/-- The gate list of `seq p q` is that of `p` followed by that of `q`. -/
theorem toGates_seq {p : XQPL Ops n α} {q : XQPL Ops n β} (hp : p.isMeasFree)
    (hq : q.isMeasFree) :
    (seq p q).toGates (isMeasFree_seq hp hq) = p.toGates hp ++ q.toGates hq := by
  induction p with
  | ret a => rfl
  | gate g k ih => exact congrArg (List.cons g) (ih hp)
  | meas i kt kf _ _ => exact hp.elim
  | custom op k ih =>
    exact (congrArg (OpGateList.gates op ++ ·) (ih hp)).trans (List.append_assoc _ _ _).symm
  | fail => exact hp.elim

/-- The unitary of `seq p q` is the unitary of `q` times the unitary of `p`. -/
theorem unitary_seq {p : XQPL Ops n α} {q : XQPL Ops n β} (hp : p.isMeasFree)
    (hq : q.isMeasFree) :
    (seq p q).unitary (isMeasFree_seq hp hq) = q.unitary hq * p.unitary hp :=
  (congrArg listMatrix (toGates_seq hp hq)).trans (listMatrix_append _ _)

/-! ## `control(qbs)` with an AND ancilla -/

/-- The block `p` controlled on every qubit of `cs` through the ancilla `a`: the AND of `cs`
    into `a` by the multi-controlled `X`, the block controlled on `a`, the inverse. -/
def mcontrolled (cs : List (Fin n)) (a : Fin n) (p : XQPL Ops n Unit) (h : p.isMeasFree) :
    XQPL Ops n Unit :=
  ofGates (ancillaCtrlGates (mctrlGates cs (Gate.X a)) a (p.toGates h))

/-- On ancilla `|0⟩`, `mcontrolled cs a p` is the unitary of `p` controlled on every qubit
    of `cs`. -/
theorem unitary_mcontrolled {cs : List (Fin n)} {a : Fin n} {p : XQPL Ops n Unit}
    {h : p.isMeasFree} (hnd : cs.Nodup) (ha : a ∉ cs)
    (hU : ∀ g ∈ p.toGates h, Avoids a g ∧ ∀ c ∈ cs, Avoids c g) :
    (mcontrolled cs a p h).unitary (isMeasFree_ofGates _) * embedGate1 n a proj0
      = mctrlMatrix cs (p.unitary h) * embedGate1 n a proj0 :=
  (congrArg (· * embedGate1 n a proj0) (unitary_ofGates _ _)).trans
    (listMatrix_andAncilla_conj hnd ha hU)

/-! ## `with r == v` -/

/-- The block `p` under the condition `r == v`, with the ancilla `a`. -/
def withEq {w : ℕ} (r : Reg n w) (v : Fin (2 ^ w)) (a : Fin n) (p : XQPL Ops n Unit)
    (h : p.isMeasFree) : XQPL Ops n Unit :=
  ofGates (r.withEq v a (p.toGates h))

/-- On ancilla `|0⟩`, `withEq r v a p` applies the unitary of `p` exactly where `r` reads
    `v`. -/
theorem unitary_withEq {w : ℕ} {r : Reg n w} {v : Fin (2 ^ w)} {a : Fin n}
    {p : XQPL Ops n Unit} {h : p.isMeasFree} (ha : a ∉ Set.range r.q)
    (hb : ∀ g ∈ p.toGates h, Avoids a g ∧ ∀ i, Avoids (r.q i) g) :
    (withEq r v a p h).unitary (isMeasFree_ofGates _) * embedGate1 n a proj0
      = (1 + r.proj v * (p.unitary h - 1)) * embedGate1 n a proj0 :=
  (congrArg (· * embedGate1 n a proj0) (unitary_ofGates _ _)).trans (r.listMatrix_withEq ha hb)

/-! ## Programs of reversible atoms and uncomputation -/

/-- A measurement-free program over `Ops ⊕ RevOp n` as a list of atoms: a gate is a gate
    atom, an atom is itself, an operation of `Ops` is the gate atoms of its gate list. -/
def toRevOps : (p : XQPL (Ops ⊕ RevOp n) n α) → p.isMeasFree → List (RevOp n)
  | .ret _, _ => []
  | .gate g k, h => RevOp.gate g :: k.toRevOps h
  | .meas _ _ _, h => False.elim h
  | .custom (.inl op) k, h => (OpGateList.gates op).map RevOp.gate ++ k.toRevOps h
  | .custom (.inr o) k, h => o :: k.toRevOps h
  | .fail, h => False.elim h

/-- The atoms of a program lower to its gate list. -/
theorem revGates_toRevOps (p : XQPL (Ops ⊕ RevOp n) n α) (h : p.isMeasFree) :
    revGates (p.toRevOps h) = p.toGates h := by
  induction p with
  | ret a => rfl
  | gate g k ih => exact (revGates_cons _ _).trans (congrArg (List.cons g) (ih h))
  | meas i kt kf _ _ => exact h.elim
  | custom op k ih =>
    cases op with
    | inl op =>
      exact (revGates_append _ _).trans (by rw [revGates_map_gate, ih h]; rfl)
    | inr o => exact (revGates_cons _ _).trans (by rw [ih h]; rfl)
  | fail => exact h.elim

/-- A list of atoms as a program of atoms. -/
def ofRevOps (l : List (RevOp n)) : XQPL (Ops ⊕ RevOp n) n Unit :=
  l.foldr (fun o k => .custom (.inr o) k) (.ret ())

omit [OpGateList Ops n] in
theorem isMeasFree_ofRevOps (l : List (RevOp n)) :
    (ofRevOps l : XQPL (Ops ⊕ RevOp n) n Unit).isMeasFree := by
  induction l with
  | nil => trivial
  | cons o l ih => exact ih

/-- The gate list of a program of atoms is the lowering of the atoms. -/
theorem toGates_ofRevOps (l : List (RevOp n)) :
    (ofRevOps l : XQPL (Ops ⊕ RevOp n) n Unit).toGates (isMeasFree_ofRevOps l) = revGates l := by
  induction l with
  | nil => rfl
  | cons o l ih => exact (congrArg (o.gates ++ ·) ih).trans (revGates_cons o l).symm

/-- Compute; use; uncompute: the atoms of `C`, those of `U`, and the inverses of the atoms
    of `C` in reverse order. -/
def uncompute (C U : XQPL (Ops ⊕ RevOp n) n Unit) (hC : C.isMeasFree) (hU : U.isMeasFree) :
    XQPL (Ops ⊕ RevOp n) n Unit :=
  ofRevOps (C.toRevOps hC ++ U.toRevOps hU ++ (C.toRevOps hC).reverse.flatMap RevOp.inv)

/-- **Compute; use; uncompute on programs.** For blocks passing the check, `U` is a
    two-branch matrix on the ancilla `a`, and on ancilla `|0⟩` the program applies its
    branch `U₀` where the predicate `P` of the inputs computed by `C` fails and `U₁` where it
    holds, and returns the ancilla to `|0⟩`. -/
theorem unitary_uncompute {a : Fin n} {ins : List (Fin n)} {C U : XQPL (Ops ⊕ RevOp n) n Unit}
    {hC : C.isMeasFree} {hU : U.isMeasFree}
    (hchk : uncomputable a ins (C.toRevOps hC) (U.toRevOps hU) = true) :
    ∃ P U₀ U₁, IsPred ins P ∧ CommOn a U₀ ∧ CommOn a U₁ ∧ U.unitary hU = branchMatrix a U₀ U₁ ∧
      (uncompute C U hC hU).unitary (isMeasFree_ofRevOps _) * embedGate1 n a proj0
        = ((1 - P) * U₀ + P * U₁) * embedGate1 n a proj0 ∧
      embedGate1 n a proj1 * (uncompute C U hC hU).unitary (isMeasFree_ofRevOps _)
        * embedGate1 n a proj0 = 0 := by
  have hchk' := hchk
  simp only [uncomputable, Bool.and_eq_true, decide_eq_true_eq] at hchk'
  obtain ⟨⟨⟨⟨⟨ha, -⟩, hq⟩, hw⟩, hp⟩, hUp⟩ := hchk'
  obtain ⟨D, P, hD, hP, hV⟩ := computes_of_check ha hq hw hp
  obtain ⟨U₀, U₁, h₀, h₁, hB⟩ := branch_of_permeable fun o ho =>
    List.all_eq_true.mp (List.all_eq_true.mp hUp o ho) a List.mem_cons_self
  have hK : (uncompute C U hC hU).unitary (isMeasFree_ofRevOps _) = listMatrix (revGates
      (C.toRevOps hC ++ U.toRevOps hU ++ (C.toRevOps hC).reverse.flatMap RevOp.inv)) :=
    congrArg listMatrix (toGates_ofRevOps _)
  obtain ⟨e₁, e₂⟩ := listMatrix_uncompute hchk hD hP hV h₀ h₁ hB
  refine ⟨P, U₀, U₁, hP, h₀, h₁, ?_, ?_, ?_⟩
  · rw [unitary, ← revGates_toRevOps U hU, hB]
  · rw [hK, e₁]
  · rw [hK, e₂]

/-! ## Exact angles through the environments -/

/-- `seq` of exact-angle programs has exact angles. -/
theorem noRz_seq {p : XQPL Ops n α} {q : XQPL Ops n β} {hp : p.isMeasFree}
    {hq : q.isMeasFree} (h₁ : ∀ g ∈ p.toGates hp, NoRz g) (h₂ : ∀ g ∈ q.toGates hq, NoRz g) :
    ∀ g ∈ (seq p q).toGates (isMeasFree_seq hp hq), NoRz g := by
  intro g hg
  rw [toGates_seq hp hq, List.mem_append] at hg
  rcases hg with h | h
  · exact h₁ g h
  · exact h₂ g h

/-- `mcontrolled` of an exact-angle block has exact angles. -/
theorem noRz_mcontrolled {cs : List (Fin n)} {a : Fin n} {p : XQPL Ops n Unit}
    {h : p.isMeasFree} (hp : ∀ g ∈ p.toGates h, NoRz g) :
    ∀ g ∈ (mcontrolled cs a p h).toGates (isMeasFree_ofGates _), NoRz g := by
  intro g hg
  change g ∈ (ofGates _ : XQPL Ops n Unit).toGates _ at hg
  rw [toGates_ofGates] at hg
  exact noRz_ancillaCtrlGates a (noRz_mctrlGates (g := Gate.X a) trivial cs) hp g hg

/-- `withEq` of an exact-angle block has exact angles. -/
theorem noRz_withEq {w : ℕ} {r : Reg n w} {v : Fin (2 ^ w)} {a : Fin n} {p : XQPL Ops n Unit}
    {h : p.isMeasFree} (hp : ∀ g ∈ p.toGates h, NoRz g) :
    ∀ g ∈ (withEq r v a p h).toGates (isMeasFree_ofGates _), NoRz g := by
  intro g hg
  change g ∈ (ofGates _ : XQPL Ops n Unit).toGates _ at hg
  rw [toGates_ofGates] at hg
  have hX : ∀ g ∈ r.xPattern v, NoRz g := by
    intro g hg
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hg
    trivial
  have hE : ∀ g ∈ r.eqIntoGates v a, NoRz g := by
    intro g hg
    simp only [Reg.eqIntoGates, List.mem_append] at hg
    rcases hg with (h | h) | h
    · exact hX g h
    · exact noRz_mctrlGates (g := Gate.X a) trivial _ g h
    · exact hX g h
  exact noRz_ancillaCtrlGates a hE hp g hg

/-! ## Export -/

/-- **Export of a measurement-free program.** For a program whose gate list has no real-angle
    `Rz`, the statements read back from the OpenQASM 2 text `exportQASM` have the `qelib1.inc`
    matrix `exp (i · exportPhase) • unitary p h`. -/
theorem qelibListMatrix_export_xqpl (p : XQPL Ops n α) (h : p.isMeasFree)
    (hr : ∀ g ∈ p.toGates h, NoRz g) :
    (importQ n (exportQASM (p.toGates h))).map qelibListMatrix
      = some (Complex.exp (Complex.I * (exportPhase (p.toGates h)).toReal) • p.unitary h) :=
  qelibListMatrix_importQ_exportQASM _ hr

end XQPL

end CatCrypt.Quantum.QPL
