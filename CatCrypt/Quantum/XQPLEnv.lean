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
public import CatCrypt.Quantum.AndLadder

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
* `XQPL.mcontrolledLadder c cs as p h`, `XQPL.withEqLadder r v as p h` — the same
  environments with the AND ladder of relative-phase Toffolis (`AndLadder.andLadder`) on the
  clean ancillae `as` as the compute step, linear in the number of controls;
* `XQPL.computeUseUncompute C U hC hU` — compute; use; uncompute over the reversible atoms
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

* `XQPL.unitary_mcontrolled`, `XQPL.unitary_withEq`, `XQPL.unitary_computeUseUncompute` — the unitary
  of each environment on ancilla `|0⟩`;
* `XQPL.unitary_mcontrolledLadder`, `XQPL.unitary_withEqLadder` — the unitary of the ladder
  environments on clean ancillae;
* `noRz_ctrlList`, `noRz_invGates` — control and inversion keep exact angles;
* `XQPL.qelibListMatrix_export_xqpl` — the export of a measurement-free program.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped Matrix
open CatCrypt.Quantum CatCrypt.Quantum.QCircuit CatCrypt.Quantum.Programs.Qubit
open CatCrypt.Quantum.ControlledGates CatCrypt.Quantum.AndAncilla CatCrypt.Quantum.AndLadder
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

/-- The relative-phase Toffoli has exact angles. -/
theorem noRz_rtofGates (c₁ c₂ a : Fin n) : ∀ g ∈ rtofGates c₁ c₂ a, NoRz g := by
  intro g hg
  simp only [rtofGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

/-- The AND ladder has exact angles. -/
theorem noRz_andLadder : ∀ (c : Fin n) (cs as : List (Fin n)), ∀ g ∈ andLadder c cs as, NoRz g
  | _, [], _, g, hg => by simp [andLadder] at hg
  | _, _ :: _, [], g, hg => by simp [andLadder] at hg
  | c, c₁ :: cs, a :: as, g, hg => by
    have e : andLadder c (c₁ :: cs) (a :: as) = rtofGates c c₁ a ++ andLadder a cs as := rfl
    rw [e, List.mem_append] at hg
    rcases hg with h | h
    · exact noRz_rtofGates c c₁ a g h
    · exact noRz_andLadder a cs as g h

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
def computeUseUncompute (C U : XQPL (Ops ⊕ RevOp n) n Unit) (hC : C.isMeasFree) (hU : U.isMeasFree) :
    XQPL (Ops ⊕ RevOp n) n Unit :=
  ofRevOps (C.toRevOps hC ++ U.toRevOps hU ++ (C.toRevOps hC).reverse.flatMap RevOp.inv)

/-- **Compute; use; uncompute on programs.** For blocks passing the check, `U` is a
    two-branch matrix on the ancilla `a`, and on ancilla `|0⟩` the program applies its
    branch `U₀` where the predicate `P` of the inputs computed by `C` fails and `U₁` where it
    holds, and returns the ancilla to `|0⟩`. -/
theorem unitary_computeUseUncompute {a : Fin n} {ins : List (Fin n)} {C U : XQPL (Ops ⊕ RevOp n) n Unit}
    {hC : C.isMeasFree} {hU : U.isMeasFree}
    (hchk : uncomputable a ins (C.toRevOps hC) (U.toRevOps hU) = true) :
    ∃ P U₀ U₁, IsPred ins P ∧ CommOn a U₀ ∧ CommOn a U₁ ∧ U.unitary hU = branchMatrix a U₀ U₁ ∧
      (computeUseUncompute C U hC hU).unitary (isMeasFree_ofRevOps _) * embedGate1 n a proj0
        = ((1 - P) * U₀ + P * U₁) * embedGate1 n a proj0 ∧
      embedGate1 n a proj1 * (computeUseUncompute C U hC hU).unitary (isMeasFree_ofRevOps _)
        * embedGate1 n a proj0 = 0 := by
  have hchk' := hchk
  simp only [uncomputable, Bool.and_eq_true, decide_eq_true_eq] at hchk'
  obtain ⟨⟨⟨⟨⟨ha, -⟩, hq⟩, hw⟩, hp⟩, hUp⟩ := hchk'
  obtain ⟨D, P, hD, hP, hV⟩ := computes_of_check ha hq hw hp
  obtain ⟨U₀, U₁, h₀, h₁, hB⟩ := branch_of_permeable fun o ho =>
    List.all_eq_true.mp (List.all_eq_true.mp hUp o ho) a List.mem_cons_self
  have hK : (computeUseUncompute C U hC hU).unitary (isMeasFree_ofRevOps _) = listMatrix (revGates
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

/-! ## `control(qbs)` with an AND ladder -/

/-- The block `p` controlled on every qubit of `c :: cs` through the clean ancillae `as`: the
    AND of the controls into the last ancilla by the AND ladder of relative-phase Toffolis, the
    block controlled on it, and the inverse ladder. -/
def mcontrolledLadder (c : Fin n) (cs as : List (Fin n)) (p : XQPL Ops n Unit)
    (h : p.isMeasFree) : XQPL Ops n Unit :=
  ofGates (ancillaCtrlGates (andLadder c cs as) (ladderTarget c as) (p.toGates h))

/-- On clean ancillae, `mcontrolledLadder c cs as p` is the unitary of `p` controlled on every
    qubit of `c :: cs`. -/
theorem unitary_mcontrolledLadder {c : Fin n} {cs as : List (Fin n)} {p : XQPL Ops n Unit}
    {h : p.isMeasFree} (hlen : cs.length = as.length) (hnd : (c :: cs ++ as).Nodup)
    (hU : ∀ g ∈ p.toGates h, ∀ q ∈ c :: cs ++ as, Avoids q g) :
    (mcontrolledLadder c cs as p h).unitary (isMeasFree_ofGates _) * cleanProj as
      = mctrlMatrix (c :: cs) (p.unitary h) * cleanProj as :=
  (congrArg (· * cleanProj as) (unitary_ofGates _ _)).trans (listMatrix_ladderCtrl hlen hnd hU)

/-! ## `with r == v` with an AND ladder -/

/-- The block `p` under the condition `r == v` with the clean ancillae `as`: the `X` pattern
    of `v` and the AND ladder over the register compute `r = v` into the last ancilla, the
    block is controlled on it, and the computation is inverted. -/
def withEqLadder {w : ℕ} (r : Reg n (w + 1)) (v : Fin (2 ^ (w + 1))) (as : List (Fin n))
    (p : XQPL Ops n Unit) (h : p.isMeasFree) : XQPL Ops n Unit :=
  ofGates (ancillaCtrlGates
    (r.xPattern v ++ andLadder (r.q 0) (List.ofFn fun i : Fin w => r.q i.succ) as)
    (ladderTarget (r.q 0) as) (p.toGates h))

/-- On clean ancillae, `withEqLadder r v as p` applies the unitary of `p` exactly where `r`
    reads `v`. -/
theorem unitary_withEqLadder {w : ℕ} {r : Reg n (w + 1)} {v : Fin (2 ^ (w + 1))}
    {as : List (Fin n)} {p : XQPL Ops n Unit} {h : p.isMeasFree} (hlen : w = as.length)
    (hnd : (List.ofFn r.q ++ as).Nodup)
    (hU : ∀ g ∈ p.toGates h, ∀ q ∈ List.ofFn r.q ++ as, Avoids q g) :
    (withEqLadder r v as p h).unitary (isMeasFree_ofGates _) * cleanProj as
      = (1 + r.proj v * (p.unitary h - 1)) * cleanProj as := by
  have hofn : List.ofFn r.q = r.q 0 :: List.ofFn fun i : Fin w => r.q i.succ := List.ofFn_succ
  have hdis : ∀ q ∈ List.ofFn r.q, q ∉ as := fun q hq hq' =>
    List.disjoint_of_nodup_append hnd hq hq'
  have hxq : ∀ q ∈ r.xQubits v, q ∈ List.ofFn r.q := by
    intro q hq
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hq
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hXX := r.xPattern_mul_self v
  have hXh : (listMatrix (r.xPattern v))ᴴ = listMatrix (r.xPattern v) := by
    calc (listMatrix (r.xPattern v))ᴴ
        = (listMatrix (r.xPattern v))ᴴ
          * (listMatrix (r.xPattern v) * listMatrix (r.xPattern v)) := by
          rw [hXX, mul_one]
      _ = _ := by rw [← mul_assoc, listMatrix_conjTranspose_mul, one_mul]
  have hXQ : Commute (listMatrix (r.xPattern v)) (cleanProj as) :=
    (commute_of_phaseOn (phaseOn_cleanProj as) fun g hg q hq => by
      obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hg
      rintro rfl
      exact hdis q' (hxq q' hq') hq).symm
  have hXU : Commute (listMatrix (r.xPattern v)) (listMatrix (p.toGates h)) :=
    commute_listMatrix_X fun q hq => commOn_listMatrix fun g hg =>
      hU g hg q (List.mem_append_left _ (hxq q hq))
  have hL := listMatrix_ladderCtrl (U := p.toGates h) (c := r.q 0)
    (cs := List.ofFn fun i : Fin w => r.q i.succ) (as := as) (by simp [hlen])
    (by rw [← hofn]; exact hnd) (by rw [← hofn]; exact hU)
  refine (congrArg (· * cleanProj as) (unitary_ofGates _ _)).trans ?_
  rw [listMatrix_ancillaCtrlGates_append, hXh]
  calc _ = listMatrix (r.xPattern v) * (listMatrix (ancillaCtrlGates
          (andLadder (r.q 0) (List.ofFn fun i : Fin w => r.q i.succ) as)
          (ladderTarget (r.q 0) as) (p.toGates h)) * cleanProj as) * listMatrix (r.xPattern v) := by
        rw [mul_assoc _ (listMatrix (r.xPattern v)), hXQ.eq]
        simp only [mul_assoc]
    _ = listMatrix (r.xPattern v) * (mctrlMatrix (List.ofFn r.q) (listMatrix (p.toGates h))
          * cleanProj as) * listMatrix (r.xPattern v) := by rw [hL, hofn]
    _ = listMatrix (r.xPattern v) * mctrlMatrix (List.ofFn r.q) (listMatrix (p.toGates h))
          * listMatrix (r.xPattern v) * cleanProj as := by
        simp only [mul_assoc]
        rw [← hXQ.eq]
    _ = _ := by
        rw [mctrlMatrix_eq, conj_one_add hXX hXU, r.xPattern_conj_prod_proj1]
        rfl

/-- `mcontrolledLadder` of an exact-angle block has exact angles. -/
theorem noRz_mcontrolledLadder {c : Fin n} {cs as : List (Fin n)} {p : XQPL Ops n Unit}
    {h : p.isMeasFree} (hp : ∀ g ∈ p.toGates h, NoRz g) :
    ∀ g ∈ (mcontrolledLadder c cs as p h).toGates (isMeasFree_ofGates _), NoRz g := by
  intro g hg
  change g ∈ (ofGates _ : XQPL Ops n Unit).toGates _ at hg
  rw [toGates_ofGates] at hg
  exact noRz_ancillaCtrlGates _ (noRz_andLadder c cs as) hp g hg

/-- `withEqLadder` of an exact-angle block has exact angles. -/
theorem noRz_withEqLadder {w : ℕ} {r : Reg n (w + 1)} {v : Fin (2 ^ (w + 1))}
    {as : List (Fin n)} {p : XQPL Ops n Unit} {h : p.isMeasFree}
    (hp : ∀ g ∈ p.toGates h, NoRz g) :
    ∀ g ∈ (withEqLadder r v as p h).toGates (isMeasFree_ofGates _), NoRz g := by
  intro g hg
  change g ∈ (ofGates _ : XQPL Ops n Unit).toGates _ at hg
  rw [toGates_ofGates] at hg
  have hV : ∀ g ∈ r.xPattern v ++ andLadder (r.q 0) (List.ofFn fun i : Fin w => r.q i.succ) as,
      NoRz g := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · obtain ⟨q, -, rfl⟩ := List.mem_map.mp h
      trivial
    · exact noRz_andLadder _ _ _ g h
  exact noRz_ancillaCtrlGates _ hV hp g hg

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
