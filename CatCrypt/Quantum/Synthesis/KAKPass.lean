/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Synthesis.KAK
public import CatCrypt.Quantum.Optimization.Embed2Commute
public import CatCrypt.Quantum.Optimization.CommutationRules
public meta import CatCrypt.Quantum.Synthesis.KAK
public meta import CatCrypt.Quantum.Optimization.CommutationRules

/-!
# Two-qubit block resynthesis by the KAK template

`collectBlocks` cuts a gate list into maximal blocks on qubit pairs, with blocks open on
several disjoint pairs at once. One left-to-right pass keeps the open blocks, which own
pairwise disjoint pairs. A gate acting only on the pair of the one open block it touches
extends that block. Any other gate closes the open blocks it touches, which are emitted; a
two-qubit gate on distinct qubits `i ≠ j` then opens a block on `(i, j)`, and any other gate
is emitted plain. The blocks still open at the end are emitted in opening order. The output
reorders the input only by moving gates past gates on disjoint qubits, so it denotes the same
unitary (`listMatrix_collectBlocks`).

`kakPass` replaces each block with more than three CNOTs by the universal three-CNOT
template `kak3Gates i j θ` of `KAK.lean`, with symbolic angles: the `k`-th template takes
the angle vector `ρ k`. `realizeK ρ` instantiates the templates.

## Main results

* `kakPass_correct` — some valuation of the angles makes the realized circuit denote the
  channel of the input circuit (the matrices agree up to a global phase).
* `cnotCount_realizeK_kakPass_le` — under every valuation the realized circuit has at most
  as many CNOTs as the input.
-/

@[expose] public section

set_option autoImplicit false

open Matrix Complex
open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.GateUnitarity CatCrypt.Quantum.TensorProduct
open CatCrypt.Quantum.UnitaryChannel
open CatCrypt.Quantum.Synthesis.KAK
open CatCrypt.Quantum.QFT (listMatrix listMatrix_cons listMatrix_nil listMatrix_append)
open CatCrypt.Quantum.Optimization.CommutationRules (targetQubits)

namespace CatCrypt.Quantum.Synthesis.KAKPass

variable {n : ℕ}

/-! ## Qubit tests -/

/-- `g` acts only on the qubits `i` and `j`. -/
def onPair (i j : Fin n) (g : Gate n) : Bool :=
  (targetQubits g).all fun q => decide (q = i ∨ q = j)

/-- `g` acts on neither `i` nor `j`. -/
def avoids (i j : Fin n) (g : Gate n) : Bool :=
  (targetQubits g).all fun q => decide (q ≠ i ∧ q ≠ j)

/-- The qubit pair of a two-qubit gate on distinct qubits. -/
def pairOf? : Gate n → Option (Fin n × Fin n)
  | .CNOT a b => if a = b then none else some (a, b)
  | .CZ a b => if a = b then none else some (a, b)
  | _ => none

/-- `g` is a CNOT. -/
def isCNOT : Gate n → Bool
  | .CNOT _ _ => true
  | _ => false

/-- The number of CNOT gates of a gate list. -/
def cnotCount (l : List (Gate n)) : ℕ := l.countP isCNOT

/-- The exact ZYZ template has no CNOT. -/
theorem cnotCount_zyzGatesQ (q : Fin n) (θ : Fin 3 → PiLin) : cnotCount (zyzGatesQ q θ) = 0 := by
  simp [zyzGatesQ, cnotCount, isCNOT]

/-! ## Concatenations -/

/-- A pointwise bound on CNOT counts bounds the CNOT counts of the concatenations. -/
theorem cnotCount_flatMap_le {α : Type*} (L : List α) (F G : α → List (Gate n))
    (h : ∀ x ∈ L, cnotCount (F x) ≤ cnotCount (G x)) :
    cnotCount (L.flatMap F) ≤ cnotCount (L.flatMap G) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have h1 := h x List.mem_cons_self
    have h2 := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    simp only [List.flatMap_cons, cnotCount, List.countP_append] at h1 h2 ⊢
    omega

/-- Pointwise equal CNOT counts give equal CNOT counts of the concatenations. -/
theorem cnotCount_flatMap {α : Type*} (L : List α) (F G : α → List (Gate n))
    (h : ∀ x ∈ L, cnotCount (F x) = cnotCount (G x)) :
    cnotCount (L.flatMap F) = cnotCount (L.flatMap G) :=
  le_antisymm (cnotCount_flatMap_le L F G fun x hx => (h x hx).le)
    (cnotCount_flatMap_le L G F fun x hx => (h x hx).ge)

/-- Pointwise equality of matrices up to a global phase gives equality of the matrices of the
concatenations up to a global phase. -/
theorem exists_listMatrix_flatMap {α : Type*} (L : List α) (F G : α → List (Gate n))
    (h : ∀ x ∈ L, ∃ φ : ℝ, listMatrix (F x) = Complex.exp (φ * I) • listMatrix (G x)) :
    ∃ φ : ℝ, listMatrix (L.flatMap F) = Complex.exp (φ * I) • listMatrix (L.flatMap G) := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons x L ih =>
    obtain ⟨φ₁, h1⟩ := h x List.mem_cons_self
    obtain ⟨φ₂, h2⟩ := ih fun y hy => h y (List.mem_cons_of_mem x hy)
    refine ⟨φ₂ + φ₁, ?_⟩
    rw [List.flatMap_cons, List.flatMap_cons, listMatrix_append, listMatrix_append, h1, h2,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Complex.exp_add]
    push_cast
    ring_nf

/-! ## Blocks -/

/-- A segment of a gate list: a gate outside any block, or a block on the pair `(i, j)`. -/
inductive Block (n : ℕ) where
  | gate : Gate n → Block n
  | pair : Fin n → Fin n → List (Gate n) → Block n

/-- The gates of a segment. -/
def Block.gates : Block n → List (Gate n)
  | .gate g => [g]
  | .pair _ _ gs => gs

/-- An open block of the scan on the pair `(i, j)`; `blk` holds its gates in reverse order. -/
structure OpenBlk (n : ℕ) where
  /-- The first qubit of the pair. -/
  i : Fin n
  /-- The second qubit of the pair. -/
  j : Fin n
  /-- The gates of the block, last gate first. -/
  blk : List (Gate n)

/-- The segment emitted when an open block closes. -/
def OpenBlk.emit (b : OpenBlk n) : Block n := .pair b.i b.j b.blk.reverse

/-- The gate `g` acts on a qubit of the pair of the open block `b`. -/
def OpenBlk.touches (g : Gate n) (b : OpenBlk n) : Bool := !avoids b.i b.j g

/-- The open block that `g` extends: the only open block `g` touches, if `g` acts only on
its pair. -/
def joinable (g : Gate n) : List (OpenBlk n) → Option (OpenBlk n)
  | [b] => if onPair b.i b.j g then some b else none
  | _ => none

/-- The block scan over the open blocks `os`, which own disjoint pairs, in opening order. A
gate acting only on the pair of the one open block it touches extends that block. Otherwise
the open blocks it touches close and are emitted; a two-qubit gate on distinct qubits then
opens a block on its pair, and any other gate is emitted plain. -/
def collectAux : List (OpenBlk n) → List (Gate n) → List (Block n)
  | os, [] => os.map OpenBlk.emit
  | os, g :: gs =>
    match joinable g (os.filter (OpenBlk.touches g)) with
    | some b => collectAux (os.filter (fun c => !c.touches g) ++ [⟨b.i, b.j, g :: b.blk⟩]) gs
    | none =>
      (os.filter (OpenBlk.touches g)).map OpenBlk.emit ++
        match pairOf? g with
        | some (a, b) => collectAux (os.filter (fun c => !c.touches g) ++ [⟨a, b, [g]⟩]) gs
        | none => .gate g :: collectAux (os.filter (fun c => !c.touches g)) gs

/-- Maximal two-qubit blocks of a gate list, on several disjoint pairs at once. -/
def collectBlocks (l : List (Gate n)) : List (Block n) := collectAux [] l

/-! ## The pass -/

/-- An output item: a gate, or the KAK template on `(i, j)` replacing the block `gs`. -/
inductive KItem (n : ℕ) where
  | gate : Gate n → KItem n
  | kak : Fin n → Fin n → List (Gate n) → KItem n

/-- The items of a segment: a block with more than three CNOTs becomes a template. -/
def blockItems : Block n → List (KItem n)
  | .gate g => [.gate g]
  | .pair i j gs => if 3 < cnotCount gs then [.kak i j gs] else gs.map .gate

/-- The KAK pass on a circuit. -/
def kakPass (c : Circuit n) : List (KItem n) :=
  (collectBlocks (OpenQASM.toGateList c)).flatMap blockItems

/-- Instantiate the templates: the `k`-th template takes the angles `ρ k`, in the angle
order of `kak3Gates`. -/
noncomputable def realizeK (ρ : ℕ → Fin 15 → ℝ) : List (KItem n) → List (Gate n)
  | [] => []
  | .gate g :: l => g :: realizeK ρ l
  | .kak i j _ :: l => kak3Gates i j (ρ 0) ++ realizeK (fun k => ρ (k + 1)) l

/-- The gates an item stands for. -/
def KItem.orig : KItem n → List (Gate n)
  | .gate g => [g]
  | .kak _ _ gs => gs

/-! ## Gates on a pair as `4 × 4` matrices -/

/-- A single-qubit matrix on qubit `q ∈ {i, j}` as a matrix on the pair `(i, j)`. -/
def side (i q : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  if q = i then A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) else (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A

/-- The `4 × 4` matrix of a gate on the pair `(i, j)`. -/
noncomputable def pairMat (i _j : Fin n) : Gate n → Matrix (Fin 4) (Fin 4) ℂ
  | .H q => side i q Programs.Qubit.hadamard
  | .X q => side i q Programs.Qubit.pauliX
  | .Y q => side i q Programs.Qubit.pauliY
  | .Z q => side i q Programs.Qubit.pauliZ
  | .T q => side i q Programs.Qubit.tGate
  | .Tdg q => side i q tDaggerGate
  | .S q => side i q Programs.Qubit.phaseS
  | .Rz q θ => side i q (rzGate θ)
  | .RzQ q a => side i q (rzGate (PiLin.toReal a))
  | .CNOT a b => if a = b then 1 else if a = i then Programs.Qubit.cnot else cnotRev
  | .CZ a b =>
    if a = b then 1 else if a = i then czGate
    else Programs.Qubit.swap * czGate * Programs.Qubit.swap

theorem embedGate1_eq_embedGate2_side {i j q : Fin n} (hij : i ≠ j) (hq : q = i ∨ q = j)
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 n q A = embedGate2 n i j (side i q A) hij := by
  rcases hq with rfl | rfl
  · rw [embedGate1_eq_embedGate2_left hij, side, ite_eq_left rfl]
  · rw [embedGate1_eq_embedGate2_right hij, side, ite_eq_right (Ne.symm hij)]

theorem gateEmbedding_eq_embedGate2 {i j : Fin n} (hij : i ≠ j) {g : Gate n}
    (hg : onPair i j g = true) :
    gateEmbedding g = embedGate2 n i j (pairMat i j g) hij := by
  cases g <;> simp only [onPair, targetQubits, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, decide_eq_true_eq] at hg
  all_goals try exact embedGate1_eq_embedGate2_side hij hg _
  all_goals
    obtain ⟨ha | ha, hb | hb⟩ := hg <;> subst ha hb <;>
      simp [gateEmbedding, pairMat, hij, Ne.symm hij, embedGate2_one, embedGate2_cnot_rev hij,
        Optimization.SwapConj.embedGate2_swap_pair hij]

theorem kronecker_mem_unitaryGroup {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A * Aᴴ = 1) (hB : B * Bᴴ = 1) :
    (A ⊗ₖ B : Matrix (Fin 4) (Fin 4) ℂ) ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose,
    TensorProduct.conjTranspose_kronecker, TensorProduct.kronecker_mul_kronecker, hA, hB,
    TensorProduct.kronecker_one_one]

theorem side_mem_unitaryGroup (i q : Fin n) {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A * Aᴴ = 1) : side i q A ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have h1 : (1 : Matrix (Fin 2) (Fin 2) ℂ) * 1ᴴ = 1 := by
    rw [conjTranspose_one, Matrix.mul_one]
  unfold side
  split
  · exact kronecker_mem_unitaryGroup hA h1
  · exact kronecker_mem_unitaryGroup h1 hA

theorem swap_mem_unitaryGroup :
    Programs.Qubit.swap ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [Programs.Qubit.swap, Matrix.mul_apply, Fin.sum_univ_four, conjTranspose_apply]

theorem pairMat_mem_unitaryGroup (i j : Fin n) (g : Gate n) :
    pairMat i j g ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  have hcnot : Programs.Qubit.cnot ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]; exact cnot_unitary
  have hcz : czGate ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]; exact czGate_unitary
  cases g <;> simp only [pairMat]
  · exact side_mem_unitaryGroup _ _ hadamard_unitary
  · exact side_mem_unitaryGroup _ _ pauliX_unitary
  · exact side_mem_unitaryGroup _ _ pauliY_unitary
  · exact side_mem_unitaryGroup _ _ pauliZ_unitary
  · exact side_mem_unitaryGroup _ _ tGate_unitary
  · exact side_mem_unitaryGroup _ _ tDaggerGate_unitary
  · exact side_mem_unitaryGroup _ _ phaseS_unitary
  · split
    · exact one_mem _
    · split
      · exact hcnot
      · exact mul_mem (mul_mem swap_mem_unitaryGroup hcnot) swap_mem_unitaryGroup
  · split
    · exact one_mem _
    · split
      · exact hcz
      · exact mul_mem (mul_mem swap_mem_unitaryGroup hcz) swap_mem_unitaryGroup
  · exact side_mem_unitaryGroup _ _ (rzGate_unitary _)
  · exact side_mem_unitaryGroup _ _ (rzGate_unitary _)

/-- The `4 × 4` matrix of a gate list on the pair `(i, j)`; the head gate acts first. -/
noncomputable def blockMat (i j : Fin n) : List (Gate n) → Matrix (Fin 4) (Fin 4) ℂ
  | [] => 1
  | g :: l => blockMat i j l * pairMat i j g

theorem blockMat_mem_unitaryGroup (i j : Fin n) (l : List (Gate n)) :
    blockMat i j l ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  induction l with
  | nil => exact one_mem _
  | cons g l ih => exact mul_mem ih (pairMat_mem_unitaryGroup i j g)

theorem listMatrix_eq_embedGate2 {i j : Fin n} (hij : i ≠ j) {l : List (Gate n)}
    (hl : ∀ g ∈ l, onPair i j g = true) :
    listMatrix l = embedGate2 n i j (blockMat i j l) hij := by
  induction l with
  | nil => simp [listMatrix_nil, blockMat, embedGate2_one]
  | cons g l ih =>
    rw [listMatrix_cons, ih (fun x hx => hl x (List.mem_cons_of_mem g hx)),
      gateEmbedding_eq_embedGate2 hij (hl g List.mem_cons_self), embedGate2_mul, blockMat]

/-! ## Commutation past gates on other qubits -/

theorem commute_embedGate2_of_avoids {i j : Fin n} (hij : i ≠ j)
    (M : Matrix (Fin 4) (Fin 4) ℂ) {h : Gate n} (hh : avoids i j h = true) :
    Commute (embedGate2 n i j M hij) (gateEmbedding h) := by
  cases h <;> simp only [avoids, targetQubits, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, decide_eq_true_eq] at hh <;> simp only [gateEmbedding]
  all_goals first
    | exact (Optimization.MixedCommute.embedGate1_embedGate2_disjoint_comm hh.1 hh.2 hij _
        M).symm
    | split
  all_goals first
    | exact Commute.one_right _
    | exact Optimization.Embed2Commute.embedGate2_embedGate2_disjoint_comm hij _
        (Ne.symm hh.1.1) (Ne.symm hh.2.1) (Ne.symm hh.1.2) (Ne.symm hh.2.2) M _

theorem commute_listMatrix {g : Gate n} {L : List (Gate n)}
    (h : ∀ x ∈ L, Commute (gateEmbedding g) (gateEmbedding x)) :
    Commute (gateEmbedding g) (listMatrix L) := by
  induction L with
  | nil => exact Commute.one_right _
  | cons x L ih =>
    rw [listMatrix_cons]
    exact (ih fun y hy => h y (List.mem_cons_of_mem x hy)).mul_right (h x List.mem_cons_self)

theorem listMatrix_cons_eq_append {g : Gate n} {L : List (Gate n)}
    (h : ∀ x ∈ L, Commute (gateEmbedding g) (gateEmbedding x)) :
    listMatrix (g :: L) = listMatrix (L ++ [g]) := by
  rw [listMatrix_cons, listMatrix_append, listMatrix_cons, listMatrix_nil, Matrix.one_mul]
  exact (commute_listMatrix h).eq.symm

/-! ## The scan -/

/-- An open block on distinct qubits whose gates act only on its pair. -/
def OpenBlk.Valid (b : OpenBlk n) : Prop := b.i ≠ b.j ∧ ∀ g ∈ b.blk, onPair b.i b.j g = true

/-- The pairs of two open blocks are disjoint. -/
def OpenBlk.Disj (b c : OpenBlk n) : Prop := b.i ≠ c.i ∧ b.i ≠ c.j ∧ b.j ≠ c.i ∧ b.j ≠ c.j

theorem OpenBlk.Disj.symm {b c : OpenBlk n} (h : b.Disj c) : c.Disj b :=
  ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm, h.2.2.2.symm⟩

/-- The invariant of the scan: the open blocks are valid and own pairwise disjoint pairs. -/
def ScanInv (os : List (OpenBlk n)) : Prop := (∀ b ∈ os, b.Valid) ∧ os.Pairwise OpenBlk.Disj

/-- The gates held by the open blocks, in the order the scan emits them. -/
def stGates (os : List (OpenBlk n)) : List (Gate n) := os.flatMap fun b => b.blk.reverse

theorem pairOf?_spec {g : Gate n} {a b : Fin n} (h : pairOf? g = some (a, b)) :
    a ≠ b ∧ onPair a b g = true := by
  cases g <;> simp only [pairOf?, Option.ite_none_left_eq_some, reduceCtorEq,
    Option.some.injEq, Prod.mk.injEq] at h
  all_goals grind [onPair, targetQubits]

theorem stGates_nil : stGates ([] : List (OpenBlk n)) = [] := by
  simp [stGates]

theorem stGates_cons (b : OpenBlk n) (os : List (OpenBlk n)) :
    stGates (b :: os) = b.blk.reverse ++ stGates os := by
  simp [stGates]

theorem stGates_append (os os' : List (OpenBlk n)) :
    stGates (os ++ os') = stGates os ++ stGates os' := by
  simp [stGates]

theorem flatMap_emit (os : List (OpenBlk n)) :
    (os.map OpenBlk.emit).flatMap Block.gates = stGates os := by
  simp [stGates, OpenBlk.emit, Block.gates, List.flatMap_map]

theorem joinable_spec {g : Gate n} {T : List (OpenBlk n)} {b : OpenBlk n}
    (h : joinable g T = some b) : T = [b] ∧ onPair b.i b.j g = true := by
  unfold joinable at h
  split at h <;> grind

theorem mem_filter_not_touches {g : Gate n} {os : List (OpenBlk n)} {c : OpenBlk n} :
    c ∈ os.filter (fun c => !c.touches g) ↔ c ∈ os ∧ avoids c.i c.j g = true := by
  simp [List.mem_filter, OpenBlk.touches]

theorem avoids_of_onPair {i j k l : Fin n} {g : Gate n} (h : onPair k l g = true)
    (hk : k ≠ i ∧ k ≠ j) (hl : l ≠ i ∧ l ≠ j) : avoids i j g = true := by
  simp only [onPair, avoids, List.all_eq_true, decide_eq_true_eq] at h ⊢
  grind

theorem disj_of_avoids_pairOf? {c : OpenBlk n} {g : Gate n} {a b : Fin n}
    (hc : avoids c.i c.j g = true) (hp : pairOf? g = some (a, b)) :
    c.Disj ⟨a, b, [g]⟩ := by
  cases g <;> simp only [pairOf?, Option.ite_none_left_eq_some, reduceCtorEq,
    Option.some.injEq, Prod.mk.injEq] at hp
  all_goals grind [avoids, targetQubits, OpenBlk.Disj]

theorem disj_of_mem_filter (p : OpenBlk n → Bool) {os : List (OpenBlk n)}
    (h : os.Pairwise OpenBlk.Disj) {b c : OpenBlk n} (hb : b ∈ os.filter p)
    (hc : c ∈ os.filter fun x => !p x) : b.Disj c := by
  induction os with
  | nil => simp at hb
  | cons x r ih =>
    rw [List.pairwise_cons] at h
    by_cases hpx : p x = true
    · simp only [List.filter_cons, hpx, Bool.not_true, ite_true] at hb hc
      rcases List.mem_cons.mp hb with rfl | hb
      · exact h.1 c (List.mem_filter.mp hc).1
      · exact ih h.2 hb hc
    · simp only [List.filter_cons, hpx, Bool.not_false, ite_true] at hb hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact (h.1 b (List.mem_filter.mp hb).1).symm
      · exact ih h.2 hb hc

theorem scanInv_filter (p : OpenBlk n → Bool) {os : List (OpenBlk n)} (h : ScanInv os) :
    ScanInv (os.filter p) :=
  ⟨fun b hb => h.1 b (List.mem_filter.mp hb).1, h.2.filter p⟩

theorem scanInv_append_singleton {os : List (OpenBlk n)} {b : OpenBlk n} (h : ScanInv os)
    (hb : b.Valid) (hd : ∀ c ∈ os, c.Disj b) : ScanInv (os ++ [b]) := by
  refine ⟨fun c hc => ?_, List.pairwise_append.mpr ⟨h.2, List.pairwise_singleton _ _, ?_⟩⟩
  · grind [ScanInv]
  · grind

theorem commute_gate_of_disj {b c : OpenBlk n} (hb : b.Valid) (hbc : b.Disj c) {x y : Gate n}
    (hx : onPair b.i b.j x = true) (hy : onPair c.i c.j y = true) :
    Commute (gateEmbedding x) (gateEmbedding y) := by
  rw [gateEmbedding_eq_embedGate2 hb.1 hx]
  exact commute_embedGate2_of_avoids hb.1 _ (avoids_of_onPair hy
    ⟨hbc.1.symm, hbc.2.2.1.symm⟩ ⟨hbc.2.1.symm, hbc.2.2.2.symm⟩)

theorem commute_listMatrix_listMatrix {A B : List (Gate n)}
    (h : ∀ x ∈ A, ∀ y ∈ B, Commute (gateEmbedding x) (gateEmbedding y)) :
    Commute (listMatrix A) (listMatrix B) := by
  induction A with
  | nil => rw [listMatrix_nil]; exact Commute.one_left _
  | cons x A ih =>
    rw [listMatrix_cons]
    exact (ih fun x' hx' => h x' (List.mem_cons_of_mem x hx')).mul_left
      (commute_listMatrix (h x List.mem_cons_self))

theorem commute_stGates {b : OpenBlk n} {cs : List (OpenBlk n)} (hb : b.Valid)
    (hcs : ∀ c ∈ cs, c.Valid ∧ b.Disj c) :
    Commute (listMatrix b.blk.reverse) (listMatrix (stGates cs)) := by
  apply commute_listMatrix_listMatrix
  intro x hx y hy
  obtain ⟨c, hc, hyc⟩ := List.mem_flatMap.mp hy
  exact commute_gate_of_disj hb (hcs c hc).2 (hb.2 x (List.mem_reverse.mp hx))
    ((hcs c hc).1.2 y (List.mem_reverse.mp hyc))

theorem commute_stGates_of_avoids {g : Gate n} {cs : List (OpenBlk n)}
    (h : ∀ c ∈ cs, c.Valid ∧ avoids c.i c.j g = true) :
    Commute (gateEmbedding g) (listMatrix (stGates cs)) := by
  apply commute_listMatrix
  intro x hx
  obtain ⟨c, hc, hxc⟩ := List.mem_flatMap.mp hx
  have hv := (h c hc).1
  rw [gateEmbedding_eq_embedGate2 hv.1 (hv.2 x (List.mem_reverse.mp hxc))]
  exact (commute_embedGate2_of_avoids hv.1 _ (h c hc).2).symm

/-- The gates of the open blocks may be emitted in the order of any partition of the blocks,
since blocks on disjoint pairs commute. -/
theorem listMatrix_stGates_filter (p : OpenBlk n → Bool) {os : List (OpenBlk n)}
    (h : ScanInv os) :
    listMatrix (stGates os) =
      listMatrix (stGates (os.filter p) ++ stGates (os.filter fun b => !p b)) := by
  obtain ⟨hv, hp⟩ := h
  induction os with
  | nil => simp [stGates]
  | cons x r ih =>
    rw [List.pairwise_cons] at hp
    have ih' := ih (fun b hb => hv b (List.mem_cons_of_mem x hb)) hp.2
    have hx := hv x List.mem_cons_self
    by_cases hpx : p x = true
    · simp only [List.filter_cons, hpx, Bool.not_true, ite_true, stGates_cons,
        listMatrix_append] at ih' ⊢
      grind only
    · have hc := commute_stGates (cs := r.filter p) hx fun c hc =>
        ⟨hv c (List.mem_cons_of_mem x (List.mem_filter.mp hc).1),
          hp.1 c (List.mem_filter.mp hc).1⟩
      simp only [List.filter_cons, hpx, Bool.not_false, ite_true, stGates_cons,
        listMatrix_append] at ih' ⊢
      simp only [Bool.false_eq_true, ite_false]
      rw [ih', Matrix.mul_assoc, Matrix.mul_assoc, hc.eq]

theorem listMatrix_collectAux (l : List (Gate n)) :
    ∀ os : List (OpenBlk n), ScanInv os →
      listMatrix ((collectAux os l).flatMap Block.gates) = listMatrix (stGates os ++ l) := by
  induction l with
  | nil => intro os _; simp [collectAux, flatMap_emit]
  | cons g gs ih =>
    intro os hos
    have hpart := listMatrix_stGates_filter (OpenBlk.touches g) hos
    have hU := scanInv_filter (fun c => !c.touches g) hos
    simp only [collectAux]
    split
    · next b hj =>
      obtain ⟨hT, hon⟩ := joinable_spec hj
      have hbT : b ∈ os.filter (OpenBlk.touches g) := by
        rw [hT]; exact List.mem_singleton_self b
      have hb : b.Valid := hos.1 b (List.mem_filter.mp hbT).1
      have hdisj : ∀ c ∈ os.filter (fun c => !c.touches g), b.Disj c := fun c hc =>
        disj_of_mem_filter _ hos.2 hbT hc
      have hinv := scanInv_append_singleton (b := ⟨b.i, b.j, g :: b.blk⟩) hU
        ⟨hb.1, by simpa [hon] using hb.2⟩ fun c hc => (hdisj c hc).symm
      have hc := commute_stGates hb fun c hc => ⟨hU.1 c hc, hdisj c hc⟩
      rw [ih _ hinv]
      conv_rhs => rw [listMatrix_append, hpart, hT]
      simp only [stGates_append, stGates_cons, stGates_nil, List.append_nil,
        List.reverse_cons, listMatrix_append, listMatrix_cons, listMatrix_nil]
      rw [← hc.eq]
      simp only [Matrix.one_mul, Matrix.mul_assoc]
    · split
      · next a b' hp =>
        obtain ⟨hab, hg⟩ := pairOf?_spec hp
        have hinv := scanInv_append_singleton (b := ⟨a, b', [g]⟩) hU
          ⟨hab, by simpa using hg⟩ fun c hc =>
            disj_of_avoids_pairOf? (mem_filter_not_touches.mp hc).2 hp
        rw [List.flatMap_append, listMatrix_append, ih _ hinv, flatMap_emit]
        conv_rhs => rw [listMatrix_append, hpart]
        simp only [stGates_append, stGates_cons, stGates_nil, List.append_nil,
          List.reverse_cons, List.reverse_nil, List.nil_append, listMatrix_append,
          listMatrix_cons, listMatrix_nil]
        simp only [Matrix.one_mul, Matrix.mul_assoc]
      · have hc := commute_stGates_of_avoids (g := g)
          (cs := os.filter fun c => !c.touches g) fun c hc =>
            ⟨hU.1 c hc, (mem_filter_not_touches.mp hc).2⟩
        rw [List.flatMap_append, listMatrix_append, List.flatMap_cons, listMatrix_append,
          ih _ hU, flatMap_emit]
        conv_rhs => rw [listMatrix_append, hpart]
        simp only [Block.gates, listMatrix_append, listMatrix_cons, listMatrix_nil]
        rw [Matrix.one_mul, Matrix.mul_assoc (listMatrix gs), ← hc.eq]
        simp only [Matrix.mul_assoc]

theorem valid_emit {c : OpenBlk n} (hc : c.Valid) :
    ∀ i j gs, c.emit = .pair i j gs → i ≠ j ∧ ∀ g ∈ gs, onPair i j g = true := by
  intro i j gs h
  simp only [OpenBlk.emit, Block.pair.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨hc.1, fun g hg => hc.2 g (List.mem_reverse.mp hg)⟩

theorem valid_collectAux (l : List (Gate n)) :
    ∀ os : List (OpenBlk n), (∀ b ∈ os, b.Valid) →
      ∀ b ∈ collectAux os l, ∀ i j gs, b = .pair i j gs →
        i ≠ j ∧ ∀ g ∈ gs, onPair i j g = true := by
  induction l with
  | nil =>
    intro os hos b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    exact valid_emit (hos c hc)
  | cons g gs ih =>
    intro os hos
    have hU : ∀ c ∈ os.filter (fun c => !c.touches g), c.Valid := fun c hc =>
      hos c (List.mem_filter.mp hc).1
    simp only [collectAux]
    split
    · next b hj =>
      obtain ⟨hT, hon⟩ := joinable_spec hj
      have hbT : b ∈ os.filter (OpenBlk.touches g) := by
        rw [hT]; exact List.mem_singleton_self b
      have hb : b.Valid := hos b (List.mem_filter.mp hbT).1
      refine ih _ fun c hc => ?_
      rcases List.mem_append.mp hc with hc | hc
      · exact hU c hc
      · simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨hb.1, by simpa [hon] using hb.2⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        exact valid_emit (hos c (List.mem_filter.mp hc).1)
      · split at hx
        · next a b' hp =>
          obtain ⟨hab, hg⟩ := pairOf?_spec hp
          refine ih _ (fun c hc => ?_) x hx
          rcases List.mem_append.mp hc with hc | hc
          · exact hU c hc
          · simp only [List.mem_singleton] at hc
            subst hc
            exact ⟨hab, by simpa using hg⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · intro i j gs' h; cases h
          · exact ih _ hU x hx

theorem cnotCount_stGates_filter (p : OpenBlk n → Bool) (os : List (OpenBlk n)) :
    cnotCount (stGates os) =
      cnotCount (stGates (os.filter p)) + cnotCount (stGates (os.filter fun b => !p b)) := by
  induction os with
  | nil => simp [stGates, cnotCount]
  | cons x r ih =>
    by_cases hpx : p x = true <;>
      simp only [List.filter_cons, hpx, Bool.not_true, Bool.not_false, ite_true, ite_false,
        Bool.false_eq_true, stGates_cons, cnotCount, List.countP_append] at ih ⊢ <;> omega

theorem cnotCount_collectAux (l : List (Gate n)) :
    ∀ os : List (OpenBlk n),
      cnotCount ((collectAux os l).flatMap Block.gates) = cnotCount (stGates os ++ l) := by
  induction l with
  | nil => intro os; simp [collectAux, flatMap_emit]
  | cons g gs ih =>
    intro os
    have hpart := cnotCount_stGates_filter (OpenBlk.touches g) os
    simp only [collectAux]
    split
    · next b hj =>
      obtain ⟨hT, _⟩ := joinable_spec hj
      rw [ih]
      rw [hT] at hpart
      simp only [stGates_append, stGates_cons, stGates_nil, List.append_nil,
        List.reverse_cons, cnotCount, List.countP_append, List.countP_cons,
        List.countP_nil] at hpart ⊢
      omega
    · split
      · next a b' _ =>
        have ih' := ih (os.filter (fun c => !c.touches g) ++ [⟨a, b', [g]⟩])
        rw [List.flatMap_append, flatMap_emit]
        simp only [stGates_append, stGates_cons, stGates_nil, List.append_nil,
          List.reverse_cons, List.reverse_nil, List.nil_append, cnotCount, List.countP_append,
          List.countP_cons, List.countP_nil] at hpart ih' ⊢
        omega
      · have ih' := ih (os.filter (fun c => !c.touches g))
        rw [List.flatMap_append, List.flatMap_cons, flatMap_emit]
        simp only [Block.gates, cnotCount, List.countP_append, List.countP_cons,
          List.countP_nil] at hpart ih' ⊢
        omega

theorem listMatrix_collectBlocks (l : List (Gate n)) :
    listMatrix ((collectBlocks l).flatMap Block.gates) = listMatrix l := by
  rw [collectBlocks, listMatrix_collectAux l [] ⟨by simp, List.Pairwise.nil⟩]
  simp [stGates]

theorem valid_collectBlocks (l : List (Gate n)) :
    ∀ b ∈ collectBlocks l, ∀ i j gs, b = .pair i j gs →
      i ≠ j ∧ ∀ g ∈ gs, onPair i j g = true :=
  valid_collectAux l [] (by simp)

theorem cnotCount_collectBlocks (l : List (Gate n)) :
    cnotCount ((collectBlocks l).flatMap Block.gates) = cnotCount l := by
  rw [collectBlocks, cnotCount_collectAux]
  simp [stGates]

/-! ## The block scan over qubit owners

`collectAux` filters the list of open blocks at every gate, which costs the number of open
blocks, up to `n / 2` per gate. `collectBlocksF` keeps for each qubit the open block on it with
the stamp of its last extension, finds the blocks a gate touches from the qubits of the gate,
and orders them by stamp, the order of the open-block list. It computes `collectBlocks`
(`collectBlocks_eq_collectBlocksF`), which it replaces in compiled code. -/

/-- An open block with its stamp. -/
abbrev SBlk (n : ℕ) := ℕ × OpenBlk n

/-- A list of at most two stamped blocks in increasing stamp order, with a repeated stamp
kept once. -/
def ordPair : List (SBlk n) → List (SBlk n)
  | [x, y] => if x.1 = y.1 then [x] else if x.1 < y.1 then [x, y] else [y, x]
  | L => L

/-- The stamped open blocks on the qubits of `g`, in increasing stamp order. -/
def touchedS (v : Vector (Option (SBlk n)) n) (g : Gate n) : List (SBlk n) :=
  ordPair ((targetQubits g).filterMap fun q => v[q])

/-- The owners `v` with the stamped block `x` on the qubits of its pair. -/
def putS (v : Vector (Option (SBlk n)) n) (x : SBlk n) : Vector (Option (SBlk n)) n :=
  (v.set x.2.i (some x)).set x.2.j (some x)

/-- The owners `v` with the qubits of the pairs of `T` cleared. -/
def clearS (v : Vector (Option (SBlk n)) n) (T : List (SBlk n)) :
    Vector (Option (SBlk n)) n :=
  T.foldl (fun w (x : SBlk n) => (w.set x.2.i none).set x.2.j none) v

/-- The stamped open blocks of the owners `v`, each once, in increasing stamp order. -/
def allS (v : Vector (Option (SBlk n)) n) : List (SBlk n) :=
  ((List.finRange n).filterMap fun q => v[q].filter fun x => x.2.i = q).mergeSort
    fun x y => x.1 ≤ y.1

/-- The block scan over the owners `v`, with `k` the next stamp. -/
def collectAuxF : Vector (Option (SBlk n)) n → ℕ → List (Gate n) → List (Block n)
  | v, _, [] => (allS v).map fun x => x.2.emit
  | v, k, g :: gs =>
    let T := touchedS v g
    match joinable g (T.map Prod.snd) with
    | some b => collectAuxF (putS v (k, ⟨b.i, b.j, g :: b.blk⟩)) (k + 1) gs
    | none =>
      T.map (fun x => x.2.emit) ++
        match pairOf? g with
        | some (a, b) => collectAuxF (putS (clearS v T) (k, ⟨a, b, [g]⟩)) (k + 1) gs
        | none => .gate g :: collectAuxF (clearS v T) k gs

/-- `collectBlocks` over qubit owners. -/
def collectBlocksF (l : List (Gate n)) : List (Block n) :=
  collectAuxF (Vector.replicate n none) 0 l

/-- The stamped open blocks are valid, own disjoint pairs, and have increasing stamps. -/
def SInv (ss : List (SBlk n)) : Prop :=
  ScanInv (ss.map Prod.snd) ∧ ss.Pairwise fun x y => x.1 < y.1

/-- The owners `v` give, at each qubit, the stamped open block on it. -/
def SOwn (ss : List (SBlk n)) (v : Vector (Option (SBlk n)) n) : Prop :=
  ∀ q x, v[q] = some x ↔ x ∈ ss ∧ (q = x.2.i ∨ q = x.2.j)

theorem touches_iff {g : Gate n} {b : OpenBlk n} :
    b.touches g = true ↔ ∃ q ∈ targetQubits g, q = b.i ∨ q = b.j := by
  simp only [OpenBlk.touches, avoids, Bool.not_eq_true', List.all_eq_false]
  grind

theorem getElem_putS (v : Vector (Option (SBlk n)) n) (x : SBlk n) (q : Fin n) :
    (putS v x)[q] = if q = x.2.i ∨ q = x.2.j then some x else v[q] := by
  simp only [putS, Fin.getElem_fin, Vector.getElem_set]
  grind

theorem getElem_clearS (T : List (SBlk n)) :
    ∀ (v : Vector (Option (SBlk n)) n) (q : Fin n),
      (clearS v T)[q] = if ∃ x ∈ T, q = x.2.i ∨ q = x.2.j then none else v[q] := by
  induction T with
  | nil => intro v q; simp [clearS]
  | cons a T ih =>
    intro v q
    simp only [clearS, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [Fin.getElem_fin, Vector.getElem_set, Fin.val_inj, List.mem_cons,
      exists_eq_or_imp]
    split_ifs <;> grind

theorem SInv.eq_of_fst_eq {ss : List (SBlk n)} (h : SInv ss) {x y : SBlk n} (hx : x ∈ ss)
    (hy : y ∈ ss) (hxy : x.1 = y.1) : x = y := by
  by_contra hne
  have : Std.Symm (fun x y : SBlk n => x.1 ≠ y.1) := ⟨fun _ _ h => Ne.symm h⟩
  exact (h.2.imp ne_of_lt).forall hx hy hne hxy

theorem SInv.eq_of_on {ss : List (SBlk n)} (h : SInv ss) {x y : SBlk n} (hx : x ∈ ss)
    (hy : y ∈ ss) {q : Fin n} (hqx : q = x.2.i ∨ q = x.2.j) (hqy : q = y.2.i ∨ q = y.2.j) :
    x = y := by
  by_contra hne
  have : Std.Symm (fun x y : SBlk n => x.2.Disj y.2) := ⟨fun _ _ h => h.symm⟩
  have hd := (List.pairwise_map.mp h.1.2).forall hx hy hne
  simp only [OpenBlk.Disj] at hd
  grind

theorem ordPair_spec {L : List (SBlk n)} (hlen : L.length ≤ 2)
    (hL : ∀ x ∈ L, ∀ y ∈ L, x.1 = y.1 → x = y) :
    (ordPair L).Pairwise (fun x y => x.1 < y.1) ∧ ∀ z, z ∈ ordPair L ↔ z ∈ L := by
  match L, hlen with
  | [], _ => simp [ordPair]
  | [x], _ => simp [ordPair]
  | [x, y], _ =>
    simp only [ordPair]
    split
    · next h =>
      have := hL x (by simp) y (by simp) h
      subst this
      simp
    · split <;> simp <;> grind

theorem touchedS_eq {ss : List (SBlk n)} {v : Vector (Option (SBlk n)) n} (hI : SInv ss)
    (hO : SOwn ss v) (g : Gate n) :
    touchedS v g = ss.filter fun x => x.2.touches g := by
  have hmem : ∀ z, z ∈ (targetQubits g).filterMap (fun q => v[q]) ↔
      z ∈ ss ∧ z.2.touches g = true := by
    intro z
    simp only [List.mem_filterMap, touches_iff]
    constructor
    · rintro ⟨q, hq, hv⟩
      exact ⟨((hO q z).mp hv).1, q, hq, ((hO q z).mp hv).2⟩
    · rintro ⟨hz, q, hq, hqz⟩
      exact ⟨q, hq, (hO q z).mpr ⟨hz, hqz⟩⟩
  have hlen : ((targetQubits g).filterMap fun q => v[q]).length ≤ 2 :=
    (List.length_filterMap_le _ _).trans (by cases g <;> simp [targetQubits])
  obtain ⟨hp, hm⟩ := ordPair_spec hlen fun x hx y hy hxy =>
    hI.eq_of_fst_eq ((hmem x).mp hx).1 ((hmem y).mp hy).1 hxy
  have : Std.Irrefl (fun x y : SBlk n => x.1 < y.1) := ⟨fun x => lt_irrefl x.1⟩
  refine List.Pairwise.eq_of_mem_iff (r := fun x y : SBlk n => x.1 < y.1) hp
    (hI.2.filter _) fun z => ?_
  rw [touchedS, hm, hmem, List.mem_filter]

theorem allS_eq {ss : List (SBlk n)} {v : Vector (Option (SBlk n)) n} (hI : SInv ss)
    (hO : SOwn ss v) : allS v = ss := by
  have hmem : ∀ z, z ∈ allS v ↔ z ∈ ss := by
    intro z
    simp only [allS, List.mem_mergeSort, List.mem_filterMap, List.mem_finRange, true_and,
      Option.filter_eq_some_iff, decide_eq_true_eq]
    constructor
    · rintro ⟨q, hv, rfl⟩
      exact ((hO _ z).mp hv).1
    · intro hz
      exact ⟨z.2.i, (hO _ z).mpr ⟨hz, Or.inl rfl⟩, rfl⟩
  have : Std.Irrefl (fun x y : SBlk n => x.1 < y.1) := ⟨fun x => lt_irrefl x.1⟩
  refine List.Pairwise.eq_of_mem_iff (r := fun x y : SBlk n => x.1 < y.1) ?_ hI.2 hmem
  have hs := List.pairwise_mergeSort (le := fun x y : SBlk n => decide (x.1 ≤ y.1))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [decide_eq_true_eq, Bool.or_eq_true]; omega)
    ((List.finRange n).filterMap fun q => v[q].filter fun x => x.2.i = q)
  have hnd : (allS v).Nodup := by
    refine (List.mergeSort_perm _ _).nodup_iff.mpr
      (List.Nodup.filterMap (fun q q' x hq hq' => ?_) (List.nodup_finRange n))
    simp only [Option.mem_def, Option.filter_eq_some_iff, decide_eq_true_eq] at hq hq'
    rw [← hq.2, ← hq'.2]
  refine (hs.and hnd).imp_of_mem fun hx hy hxy => ?_
  simp only [decide_eq_true_eq] at hxy
  rcases Nat.lt_or_eq_of_le hxy.1 with h | h
  · exact h
  · exact absurd (hI.eq_of_fst_eq ((hmem _).mp hx) ((hmem _).mp hy) h) hxy.2

theorem sOwn_clear {ss : List (SBlk n)} {v : Vector (Option (SBlk n)) n} (hI : SInv ss)
    (hO : SOwn ss v) (g : Gate n) :
    SOwn (ss.filter fun x => !x.2.touches g) (clearS v (ss.filter fun x => x.2.touches g)) := by
  intro q x
  rw [getElem_clearS]
  split
  · next h =>
    obtain ⟨t, ht, hqt⟩ := h
    simp only [reduceCtorEq, false_iff, List.mem_filter, Bool.not_eq_true'] at ht ⊢
    intro ⟨⟨hx, hxt⟩, hqx⟩
    have := hI.eq_of_on hx ht.1 hqx hqt
    subst this
    simp_all
  · next h =>
    rw [hO]
    simp only [List.mem_filter, Bool.not_eq_true'] at h ⊢
    grind

theorem sOwn_put {ss : List (SBlk n)} {v : Vector (Option (SBlk n)) n} (x : SBlk n)
    (hO : ∀ q, ¬(q = x.2.i ∨ q = x.2.j) →
      ∀ y, v[q] = some y ↔ y ∈ ss ∧ (q = y.2.i ∨ q = y.2.j))
    (hd : ∀ y ∈ ss, y.2.Disj x.2) : SOwn (ss ++ [x]) (putS v x) := by
  intro q y
  rw [getElem_putS]
  split
  · next h =>
    simp only [Option.some.injEq, List.mem_append, List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨Or.inr rfl, h⟩
    · rintro ⟨hy | rfl, hqy⟩
      · have := hd y hy
        simp only [OpenBlk.Disj] at this
        grind
      · rfl
  · next h =>
    rw [hO q h]
    simp only [List.mem_append, List.mem_singleton]
    grind

theorem filter_map_snd (ss : List (SBlk n)) (p : OpenBlk n → Bool) :
    (ss.map Prod.snd).filter p = (ss.filter fun x => p x.2).map Prod.snd := by
  rw [List.filter_map]
  rfl

theorem collectAuxF_eq (l : List (Gate n)) :
    ∀ (ss : List (SBlk n)) (v : Vector (Option (SBlk n)) n) (k : ℕ), SInv ss → SOwn ss v →
      (∀ x ∈ ss, x.1 < k) → collectAuxF v k l = collectAux (ss.map Prod.snd) l := by
  induction l with
  | nil =>
    intro ss v k hI hO _
    rw [collectAuxF, collectAux, allS_eq hI hO, List.map_map]
    rfl
  | cons g gs ih =>
    intro ss v k hI hO hk
    have hT := touchedS_eq hI hO g
    have hU := sOwn_clear hI hO g
    have hIU : SInv (ss.filter fun x => !x.2.touches g) :=
      ⟨by rw [← filter_map_snd ss fun b => !b.touches g]; exact scanInv_filter _ hI.1,
        hI.2.filter _⟩
    have hdisj : ∀ b ∈ (ss.filter fun x => x.2.touches g),
        ∀ c ∈ (ss.filter fun x => !x.2.touches g), b.2.Disj c.2 := by
      intro b hb c hc
      refine disj_of_mem_filter (OpenBlk.touches g) hI.1.2 ?_ ?_
      · rw [filter_map_snd]; exact List.mem_map_of_mem hb
      · rw [filter_map_snd]; exact List.mem_map_of_mem hc
    have hpush : ∀ x : SBlk n, k ≤ x.1 → SInv (ss.filter fun x => !x.2.touches g) →
        (∀ y ∈ ss.filter (fun x => !x.2.touches g), y.2.Disj x.2) →
        x.2.Valid → SInv ((ss.filter fun x => !x.2.touches g) ++ [x]) := by
      intro x hx hI' hd hv
      refine ⟨?_, List.pairwise_append.mpr ⟨hI'.2, List.pairwise_singleton _ _, ?_⟩⟩
      · rw [List.map_append]
        exact scanInv_append_singleton hI'.1 hv fun c hc => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hc
          exact hd y hy
      · intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        exact lt_of_lt_of_le (hk a (List.mem_filter.mp ha).1) hx
    have hbound : ∀ x ∈ ss.filter (fun x => !x.2.touches g), x.1 < k + 1 :=
      fun x hx => Nat.lt_succ_of_lt (hk x (List.mem_filter.mp hx).1)
    simp only [collectAuxF, collectAux, hT, filter_map_snd]
    split
    · next b hj =>
      obtain ⟨hTb, hon⟩ := joinable_spec hj
      obtain ⟨t, ht, rfl⟩ : ∃ t, (ss.filter fun x => x.2.touches g) = [t] ∧ t.2 = b := by
        rcases h : (ss.filter fun x => x.2.touches g) with _ | ⟨t, _ | ⟨t', r⟩⟩ <;>
          simp_all
      have htm : t ∈ ss.filter (fun x => x.2.touches g) := by rw [ht]; simp
      have hv : t.2.Valid := hI.1.1 t.2 (List.mem_map_of_mem (List.mem_filter.mp htm).1)
      have hv' : (⟨t.2.i, t.2.j, g :: t.2.blk⟩ : OpenBlk n).Valid :=
        ⟨hv.1, by simpa [hon] using hv.2⟩
      have hd : ∀ y ∈ ss.filter (fun x => !x.2.touches g),
          y.2.Disj (⟨t.2.i, t.2.j, g :: t.2.blk⟩ : OpenBlk n) := fun y hy =>
        (hdisj t htm y hy).symm
      have := ih ((ss.filter fun x => !x.2.touches g) ++ [(k, ⟨t.2.i, t.2.j, g :: t.2.blk⟩)])
        (putS v (k, ⟨t.2.i, t.2.j, g :: t.2.blk⟩)) (k + 1)
        (hpush _ le_rfl hIU hd hv')
        (sOwn_put (k, ⟨t.2.i, t.2.j, g :: t.2.blk⟩) (fun q hq y => by
          rw [← hU q y, getElem_clearS, ht]
          simp only [List.mem_singleton, exists_eq_left]
          split_ifs with h
          · exact absurd h hq
          · exact Iff.rfl) hd)
        (by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hbound x hx
          · rw [List.mem_singleton] at hx; subst hx; exact Nat.lt_succ_self k)
      rw [this, List.map_append]
      rfl
    · rw [List.map_map]
      congr 1
      split
      · next a b hp =>
        obtain ⟨hab, hg⟩ := pairOf?_spec hp
        have hd : ∀ y ∈ ss.filter (fun x => !x.2.touches g),
            y.2.Disj (⟨a, b, [g]⟩ : OpenBlk n) := fun y hy =>
          disj_of_avoids_pairOf? (by
            have := (List.mem_filter.mp hy).2
            simpa [OpenBlk.touches] using this) hp
        have := ih ((ss.filter fun x => !x.2.touches g) ++ [(k, ⟨a, b, [g]⟩)])
          (putS (clearS v (ss.filter fun x => x.2.touches g)) (k, ⟨a, b, [g]⟩)) (k + 1)
          (hpush _ le_rfl hIU hd ⟨hab, by simpa using hg⟩)
          (sOwn_put (k, ⟨a, b, [g]⟩) (fun q _ y => hU q y) hd)
          (by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hbound x hx
            · rw [List.mem_singleton] at hx; subst hx; exact Nat.lt_succ_self k)
        rw [this, List.map_append]
        rfl
      · rw [ih _ _ k hIU hU fun x hx => hk x (List.mem_filter.mp hx).1]

/-- `collectBlocksF` computes `collectBlocks`, and replaces it in compiled code. -/
@[csimp] theorem collectBlocks_eq_collectBlocksF : @collectBlocks = @collectBlocksF := by
  funext n l
  rw [collectBlocks, collectBlocksF, collectAuxF_eq l [] _ 0 ⟨⟨by simp, by simp⟩, by simp⟩
    (fun q x => by simp) (by simp)]
  rfl

/-! ## Realization -/

/-- An item is valid when each template stands for a block on distinct qubits `(i, j)`
with more than three CNOTs. -/
def KItem.Valid : KItem n → Prop
  | .gate _ => True
  | .kak i j gs => i ≠ j ∧ (∀ g ∈ gs, onPair i j g = true) ∧ 3 < cnotCount gs

theorem exists_listMatrix_realizeK (l : List (KItem n)) (hl : ∀ x ∈ l, x.Valid) :
    ∃ (ρ : ℕ → Fin 15 → ℝ) (φ : ℝ),
      listMatrix (realizeK ρ l) = Complex.exp (φ * I) • listMatrix (l.flatMap KItem.orig) := by
  induction l with
  | nil => exact ⟨fun _ _ => 0, 0, by simp [realizeK, listMatrix_nil]⟩
  | cons x l ih =>
    obtain ⟨ρ, φ, h⟩ := ih fun y hy => hl y (List.mem_cons_of_mem x hy)
    cases x with
    | gate g =>
      refine ⟨ρ, φ, ?_⟩
      simp only [realizeK, List.flatMap_cons, KItem.orig, List.singleton_append,
        listMatrix_cons, h, Matrix.smul_mul]
    | kak i j gs =>
      obtain ⟨hij, hgs, _⟩ := hl _ List.mem_cons_self
      obtain ⟨ψ, θ, hθ⟩ := kak3_exists_listMatrix hij (blockMat_mem_unitaryGroup i j gs)
      refine ⟨fun k => Nat.casesOn k θ ρ, φ + ψ, ?_⟩
      simp only [realizeK, List.flatMap_cons, KItem.orig, listMatrix_append]
      change listMatrix (realizeK ρ l) * listMatrix (kak3Gates i j θ) = _
      rw [h, hθ, ← listMatrix_eq_embedGate2 hij hgs, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, ← Complex.exp_add]
      push_cast
      ring_nf

theorem cnotCount_kak3Gates (i j : Fin n) (θ : Fin 15 → ℝ) :
    cnotCount (kak3Gates i j θ) = 3 := by
  simp [cnotCount, kak3Gates, isCNOT, List.countP_cons]

theorem cnotCount_realizeK_le (l : List (KItem n)) (hl : ∀ x ∈ l, x.Valid)
    (ρ : ℕ → Fin 15 → ℝ) :
    cnotCount (realizeK ρ l) ≤ cnotCount (l.flatMap KItem.orig) := by
  induction l generalizing ρ with
  | nil => simp [realizeK]
  | cons x l ih =>
    have ih' := fun ρ' => ih (fun y hy => hl y (List.mem_cons_of_mem x hy)) ρ'
    cases x with
    | gate g =>
      have := ih' ρ
      simp only [realizeK, List.flatMap_cons, KItem.orig, cnotCount, List.countP_cons,
        List.singleton_append] at this ⊢
      omega
    | kak i j gs =>
      obtain ⟨_, _, h3⟩ := hl _ List.mem_cons_self
      have := ih' (fun k => ρ (k + 1))
      simp only [realizeK, List.flatMap_cons, KItem.orig, cnotCount,
        List.countP_append] at this h3 ⊢
      have hk := cnotCount_kak3Gates i j (ρ 0)
      simp only [cnotCount] at hk
      omega

/-! ## The pass on circuits -/

theorem flatMap_blockItems (l : List (Block n)) :
    (l.flatMap blockItems).flatMap KItem.orig = l.flatMap Block.gates := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.flatMap_cons, List.flatMap_append, ih, List.flatMap_cons]
    congr 1
    cases b with
    | gate g => simp [blockItems, KItem.orig, Block.gates]
    | pair i j gs =>
      by_cases h3 : 3 < cnotCount gs
      · simp [blockItems, h3, KItem.orig, Block.gates]
      · simp [blockItems, h3, List.flatMap_map, KItem.orig, Block.gates]

theorem valid_kakPass (c : Circuit n) : ∀ x ∈ kakPass c, x.Valid := by
  intro x hx
  obtain ⟨b, hb, hxb⟩ := List.mem_flatMap.mp hx
  have hv := valid_collectBlocks _ b hb
  cases b with
  | gate g =>
    simp only [blockItems, List.mem_singleton] at hxb
    subst hxb; trivial
  | pair i j gs =>
    obtain ⟨hij, hgs⟩ := hv i j gs rfl
    by_cases h3 : 3 < cnotCount gs
    · simp only [blockItems, h3, ite_true, List.mem_singleton] at hxb
      subst hxb; exact ⟨hij, hgs, h3⟩
    · simp only [blockItems, h3, ite_false, List.mem_map] at hxb
      obtain ⟨g, _, rfl⟩ := hxb
      trivial

theorem listMatrix_toGateList (c : Circuit n) :
    listMatrix (OpenQASM.toGateList c) = (Optimization.RoutingPerm.circuitUnitary c).val := by
  induction c with
  | empty => rfl
  | gate g c ih => rw [OpenQASM.toGateList, listMatrix_cons, ih]; rfl
  | seq c₁ c₂ ih₁ ih₂ => rw [OpenQASM.toGateList, listMatrix_append, ih₁, ih₂]; rfl

theorem listMatrix_flatMap_kakPass (c : Circuit n) :
    listMatrix ((kakPass c).flatMap KItem.orig) =
      (Optimization.RoutingPerm.circuitUnitary c).val := by
  rw [kakPass, flatMap_blockItems, listMatrix_collectBlocks, listMatrix_toGateList]

/-- **Correctness of the KAK pass.** Some valuation of the template angles makes the
realized circuit denote the channel of `c`. -/
theorem kakPass_correct (c : Circuit n) :
    ∃ ρ : ℕ → Fin 15 → ℝ,
      unitaryDenote (Circuit.ofList (realizeK ρ (kakPass c))) = unitaryDenote c := by
  obtain ⟨ρ, φ, h⟩ := exists_listMatrix_realizeK (kakPass c) (valid_kakPass c)
  refine ⟨ρ, ?_⟩
  rw [Optimization.RoutingPerm.unitaryDenote_eq_channel,
    Optimization.RoutingPerm.unitaryDenote_eq_channel]
  exact unitaryChannel_eq_of_val_eq_smul φ (h.trans (by rw [listMatrix_flatMap_kakPass]))

/-- **CNOT count of the KAK pass.** Under every valuation of the angles the realized
circuit has at most as many CNOTs as `c`. -/
theorem cnotCount_realizeK_kakPass_le (c : Circuit n) (ρ : ℕ → Fin 15 → ℝ) :
    cnotCount (realizeK ρ (kakPass c)) ≤ cnotCount (OpenQASM.toGateList c) := by
  refine (cnotCount_realizeK_le _ (valid_kakPass c) ρ).trans (le_of_eq ?_)
  rw [kakPass, flatMap_blockItems, cnotCount_collectBlocks]

/-- A four-CNOT block on qubits `0, 1` of a three-qubit circuit becomes a template, and the
two-CNOT block on qubits `1, 2` after it is kept. The gate `H 2` is emitted before the block,
which is open on another pair when it is read. -/
def kakPassExample : Circuit 3 :=
  Circuit.ofList [.CNOT 0 1, .CNOT 1 0, .H 2, .CNOT 0 1, .CNOT 1 0, .CNOT 1 2, .CNOT 1 2]

/-- Whether an item is a template. -/
def KItem.isKak : KItem n → Bool
  | .kak _ _ _ => true
  | .gate _ => false

-- `H 2`, the template on `(0, 1)`, then the two CNOTs on `(1, 2)`.
#guard (kakPass kakPassExample).map KItem.isKak == [false, true, false, false]

/-- Two four-CNOT blocks on the disjoint pairs `(0, 1)` and `(2, 3)`, with their gates
interleaved; both are open at once and both become templates. -/
def kakPassExampleMulti : Circuit 4 :=
  Circuit.ofList [.CNOT 0 1, .CNOT 2 3, .CNOT 1 0, .CNOT 3 2, .H 0, .CNOT 0 1, .CNOT 2 3,
    .CNOT 1 0, .CNOT 3 2]

#guard (kakPass kakPassExampleMulti).map KItem.isKak == [true, true]

end CatCrypt.Quantum.Synthesis.KAKPass
