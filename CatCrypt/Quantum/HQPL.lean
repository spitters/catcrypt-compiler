/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QPLExtended
public import CatCrypt.Quantum.Instrument
public import CatCrypt.Quantum.QFT.Inverse
public import CatCrypt.Quantum.ControlledGates

/-!
# HQPL: High-Level QPL with Register-Level Operations

HQPL extends QPL by register-level operations (`RegisterOps n`): the quantum
Fourier transform and its inverse on a window `[start, start + len)` of the
`n`-qubit register, phase estimation of a circuit `U` with a counting window,
amplitude amplification with an oracle circuit and a state-preparation circuit,
and a barrier. `HQPLProg n α` is `XQPL (RegisterOps n) n α`, so it inherits the
XQPL denotational semantics, gate count and bind.

## Semantics

An operation denotes the channel of the circuit of its lowering
(`lowerRegisterOp`): `qft start len` denotes the channel of the circuit
`qftGates len` placed on the qubits `[start, start + len)`, `iqft start len`
that of `qftInvGates len`, and `barrier` the identity (`qpure ()`). When the
window does not fit (`start + len > n`) the lowering is empty and the operation
denotes the identity. The content of this semantics is that the placed circuits
are the transforms on the window:

* `denote_qft_whole`, `denote_iqft_whole`: on the whole register `qft 0 n`
  denotes the channel of `qftUnitary n`, and `iqft 0 n` that of its inverse;
* `listMatrix_lowerRegisterOp_phaseEstimation`: for `U` not acting on the
  counting window, the lowered phase estimation realises the windowed inverse
  QFT after the controlled powers `C_{start+i}(U^(2^(len-1-i)))` after the
  Hadamards on the window;
* `listMatrix_lowerRegisterOp_amplitudeAmplification`: the lowered amplitude
  amplification with `k` iterations realises `G^k`, the Grover iterate
  `G = (2|ψ⟩⟨ψ| - I) O` with `|ψ⟩ = A|0…0⟩`.

## Main definitions

* `RegisterOps n` -- register-level operations for `n`-qubit systems
* `HQPLProg n α` -- `XQPL (RegisterOps n) n α`
* Smart constructors: `applyQFT`, `applyIQFT`, `phaseEst`, `amplitudeAmplify`,
  `addBarrier`
* Example programs: `barrierExample`, `qftRoundTrip`
* `registerGates` -- a circuit on `len` qubits placed on the qubits
  `[start, start + len)`
* `phaseEstimationGates`, `zeroReflectGates`, `groverIterateGates`,
  `amplitudeAmplificationGates` -- the gate lists of phase estimation, of the
  reflection about `|0…0⟩`, of one Grover iteration and of amplitude
  amplification; the controlled powers are `ControlledGates.ctrlList`
* `lowerRegisterOp` -- `qft` and `iqft` to the transform circuits `qftGates`
  and `qftInvGates` on the window, `phaseEstimation` and
  `amplitudeAmplification` to their gate lists, `barrier` to no gates
* `lowerHQPL` -- lowering from HQPL to standard QPL

## Main results

* `lowerHQPL_denote` -- every HQPL program and its lowering to QPL have the
  same denotation
* `denote_applyGates` -- a gate list in front of a QPL program denotes the
  circuit of the list followed by the program
* `unitaryDenote_lowerRegisterOp_qft`, `unitaryDenote_lowerRegisterOp_iqft` --
  on the whole register the lowered transforms denote the channels of
  `qftUnitary n` and its inverse

## References

* Shor, P. -- *Polynomial-Time Algorithms for Prime Factorization and
  Discrete Logarithms on a Quantum Computer*, SIAM J. Comput. 1997
* Kitaev, A.Y. -- *Quantum measurements and the Abelian Stabilizer Problem*, 1995
* Brassard, G., Høyer, P., Mosca, M., Tapp, A. -- *Quantum Amplitude
  Amplification and Estimation*, 2002
-/

@[expose] public section

set_option autoImplicit true

noncomputable section

namespace CatCrypt.Quantum.HQPL

open CatCrypt.Quantum CatCrypt.Quantum.QPLExtended CatCrypt.Quantum.QCircuit

/-! ## Register-Level Operations -/

/-- Register-level operations for `n`-qubit systems.

    * `qft start len` -- QFT on qubits `[start .. start+len)`
    * `iqft start len` -- inverse QFT on the same sub-register
    * `phaseEstimation start len U` -- phase estimation of the circuit `U` with the
      counting register `[start .. start+len)`
    * `amplitudeAmplification O A k` -- `k` Grover iterations with oracle circuit `O`
      and state-preparation circuit `A`
    * `barrier` -- no-op barrier (for circuit layout / scheduling) -/
inductive RegisterOps (n : ℕ) where
  | qft (start len : ℕ)
  | iqft (start len : ℕ)
  | phaseEstimation (start len : ℕ) (U : List (Gate n))
  | amplitudeAmplification (oracle prep : List (Gate n)) (iters : ℕ)
  | barrier

/-! ## Lowering of register operations -/

/-- A gate list on `len` qubits placed on the qubits `[start, start + len)` of
    `n`: qubit `i` of the list becomes qubit `start + i`. The result is empty
    when `start + len > n`. -/
def registerGates (start len : ℕ) (l : List (Gate len)) : List (Gate n) :=
  if h : start + len ≤ n then
    l.map (QFT.mapGate fun i =>
      ⟨start + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt start) h⟩)
  else []

/-- Placing a gate list on the whole register leaves it unchanged. -/
theorem registerGates_whole (l : List (Gate n)) : registerGates 0 n l = l := by
  rw [registerGates, dite_eq_left (Nat.zero_add n).le]
  have hf : (fun i : Fin n =>
      (⟨0 + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt 0)
        (Nat.zero_add n).le⟩ : Fin n)) = id := by
    funext i
    exact Fin.ext (Nat.zero_add i.val)
  rw [hf, QFT.map_mapGate_id]

/-- Qubit `i` of the window `[start, start + len)` of `n` qubits: the qubit
    `start + i`. -/
def windowQubit {start len : ℕ} (h : start + len ≤ n) (i : Fin len) : Fin n :=
  ⟨start + i.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt start) h⟩

/-- The gate list `l` repeated `k` times: its matrix is the `k`-th power of
    the matrix of `l`. -/
def powGates (l : List (Gate n)) (k : ℕ) : List (Gate n) := (List.replicate k l).flatten

/-- The gates of quantum phase estimation of the circuit `U` with counting
    register `[start, start + len)`: a Hadamard on each counting qubit; for each
    window position `i`, the circuit `U^(2^(len-1-i))` controlled on qubit
    `start + i` (the counting qubit of significance `2^(len-1-i)`, qubit `0`
    being the most significant); the inverse QFT on the counting register.
    No gates when the window does not fit. -/
def phaseEstimationGates (start len : ℕ) (U : List (Gate n)) : List (Gate n) :=
  if h : start + len ≤ n then
    (List.finRange len).map (fun i => Gate.H (windowQubit h i)) ++
      ((List.finRange len).flatMap fun i =>
        ControlledGates.ctrlList (windowQubit h i) (powGates U (2 ^ (len - 1 - i.val)))) ++
      registerGates start len (QFT.qftInvGates len)
  else []

/-- The reflection `2|0…0⟩⟨0…0| - I` about the all-zero state as a gate list:
    `X` on every qubit, `Z` on qubit `0` controlled on all other qubits, `X` on
    every qubit, and `X Z X Z = -I` on qubit `0`. On `0` qubits it is empty. -/
def zeroReflectGates : (n : ℕ) → List (Gate n)
  | 0 => []
  | m + 1 =>
    (List.finRange (m + 1)).map Gate.X ++
      (ControlledGates.mctrlGates ((List.finRange m).map Fin.succ) (Gate.Z 0) ++
      ((List.finRange (m + 1)).map Gate.X ++ [Gate.X 0, Gate.Z 0, Gate.X 0, Gate.Z 0]))

/-- One Grover iteration with oracle circuit `O` and state-preparation circuit
    `A`: the oracle, then the diffusion `A (2|0…0⟩⟨0…0| - I) A†`. -/
def groverIterateGates (O A : List (Gate n)) : List (Gate n) :=
  O ++ (QFT.invGates A ++ (zeroReflectGates n ++ A))

/-- Amplitude amplification: `k` Grover iterations with oracle circuit `O` and
    state-preparation circuit `A`. -/
def amplitudeAmplificationGates (O A : List (Gate n)) (k : ℕ) : List (Gate n) :=
  powGates (groverIterateGates O A) k

/-- Lowering of a register-level operation to standard gates.

    `qft start len` and `iqft start len` lower to the transform circuits
    `QFT.qftGates len` and `QFT.qftInvGates len` placed on the qubits
    `[start, start + len)` (no gates when the register does not fit);
    `phaseEstimation` to `phaseEstimationGates`, `amplitudeAmplification` to
    `amplitudeAmplificationGates`; `barrier` lowers to no gates. Concrete
    lowerings at two and four qubits are in `HQPL/ConcreteLowering.lean`. -/
def lowerRegisterOp : RegisterOps n → List (Gate n)
  | .qft start len => registerGates start len (QFT.qftGates len)
  | .iqft start len => registerGates start len (QFT.qftInvGates len)
  | .phaseEstimation start len U => phaseEstimationGates start len U
  | .amplitudeAmplification O A k => amplitudeAmplificationGates O A k
  | .barrier => []

/-! ## OpDenote Instance -/

/-- Denotational semantics of register-level operations: an operation denotes
    the unitary channel of the circuit of its lowering. -/
instance : OpDenote (RegisterOps n) n where
  denote op := GateUnitarity.unitaryDenote (Circuit.ofList (lowerRegisterOp op))

/-- Unfolding lemma of the `OpDenote` instance of `RegisterOps n`. -/
theorem denote_registerOp (op : RegisterOps n) :
    OpDenote.denote op = GateUnitarity.unitaryDenote (Circuit.ofList (lowerRegisterOp op)) :=
  rfl

/-! ## HQPLProg Type -/

/-- High-level QPL: XQPL instantiated with register-level operations. -/
def HQPLProg (n : ℕ) (α : Type) := XQPL (RegisterOps n) n α

/-! ## Smart Constructors -/

/-- Apply QFT on qubits `[start .. start+len)`, then continue with `k`. -/
def applyQFT (start len : ℕ) (k : HQPLProg n α) : HQPLProg n α :=
  .custom (.qft start len) k

/-- Apply inverse QFT on qubits `[start .. start+len)`, then continue with `k`. -/
def applyIQFT (start len : ℕ) (k : HQPLProg n α) : HQPLProg n α :=
  .custom (.iqft start len) k

/-- Phase estimation of the circuit `U` with counting register
    `[start .. start+len)`, then continue with `k`. -/
def phaseEst (start len : ℕ) (U : List (Gate n)) (k : HQPLProg n α) : HQPLProg n α :=
  .custom (.phaseEstimation start len U) k

/-- `iters` Grover iterations with oracle circuit `O` and state-preparation
    circuit `A`, then continue with `k`. -/
def amplitudeAmplify (O A : List (Gate n)) (iters : ℕ) (k : HQPLProg n α) : HQPLProg n α :=
  .custom (.amplitudeAmplification O A iters) k

/-- Insert a barrier (no-op, used for circuit layout). -/
def addBarrier (k : HQPLProg n α) : HQPLProg n α :=
  .custom .barrier k

/-! ## Example Programs -/

/-- Simple barrier example: gates separated by a barrier. -/
def barrierExample : HQPLProg 2 Unit :=
  .gate (.H 0) (addBarrier (.gate (.CNOT 0 1) (.ret ())))

/-! ## Lowering: HQPL to QPL -/

/-- Apply a list of gates in sequence, then continue with `k`. -/
def applyGates (gates : List (Gate n)) (k : CatCrypt.Quantum.QPL.QPL n α) :
    CatCrypt.Quantum.QPL.QPL n α :=
  gates.foldr (fun g acc => .gate g acc) k

/-- Lower an HQPL program to standard QPL, replacing each register-level
    operation by the gate list `lowerRegisterOp` of it. -/
def lowerHQPL : HQPLProg n α → CatCrypt.Quantum.QPL.QPL n α
  | .ret a => .ret a
  | .gate g k => .gate g (lowerHQPL k)
  | .meas i kt kf => .meas i (lowerHQPL kt) (lowerHQPL kf)
  | .custom op k => applyGates (lowerRegisterOp op) (lowerHQPL k)
  | .fail => .fail

/-! ## Properties -/

@[simp] theorem lowerHQPL_ret (a : α) :
    (lowerHQPL (XQPL.ret a : HQPLProg n α)) = .ret a := rfl

@[simp] theorem lowerHQPL_fail :
    (lowerHQPL (XQPL.fail : HQPLProg n α)) = .fail := rfl

/-- Barrier lowers to identity (no gates inserted). -/
theorem lowerHQPL_barrier (k : HQPLProg n α) :
    lowerHQPL (addBarrier k) = lowerHQPL k := by
  simp [addBarrier, lowerHQPL, lowerRegisterOp, applyGates]

/-- A gate list in front of a QPL program denotes the circuit of the list
    followed by the program. -/
theorem denote_applyGates (l : List (Gate n)) (k : CatCrypt.Quantum.QPL.QPL n α) :
    (applyGates l k).denote =
      QComp.qbind (GateUnitarity.unitaryDenote (Circuit.ofList l)) (fun _ => k.denote) := by
  induction l with
  | nil =>
    simp only [applyGates, List.foldr_nil, Circuit.ofList, GateUnitarity.unitaryDenote,
      QComp.qpure_qbind]
  | cons g l ih =>
    rw [Circuit.ofList, GateUnitarity.unitaryDenote, QComp.qbind_assoc, ← ih]
    rfl

/-- **Soundness of the lowering.** Every HQPL program and its lowering to QPL
    have the same denotation. -/
theorem lowerHQPL_denote (p : HQPLProg n α) : (lowerHQPL p).denote = XQPL.denote p := by
  induction p with
  | ret a => rfl
  | gate g k ih => simp only [lowerHQPL, QPL.QPL.denote, XQPL.denote, ih]
  | meas i kt kf iht ihf => simp only [lowerHQPL, QPL.QPL.denote, XQPL.denote, iht, ihf]
  | custom op k ih =>
    rw [lowerHQPL, denote_applyGates, ih]
    rfl
  | fail => rfl

/-- The lowered `qft` on the whole register is the transform circuit. -/
theorem lowerRegisterOp_qft_whole :
    lowerRegisterOp (.qft 0 n : RegisterOps n) = QFT.qftGates n :=
  registerGates_whole _

/-- The lowered `iqft` on the whole register is the inverse transform
    circuit. -/
theorem lowerRegisterOp_iqft_whole :
    lowerRegisterOp (.iqft 0 n : RegisterOps n) = QFT.qftInvGates n :=
  registerGates_whole _

/-- On the whole register the lowered `qft` has the matrix `qftMatrix n`. -/
theorem listMatrix_lowerRegisterOp_qft :
    QFT.listMatrix (lowerRegisterOp (.qft 0 n : RegisterOps n)) = QFT.qftMatrix n := by
  rw [lowerRegisterOp_qft_whole, QFT.qftGates_matrix]

/-- On the whole register the lowered `iqft` has the matrix `(qftMatrix n)ᴴ`. -/
theorem listMatrix_lowerRegisterOp_iqft :
    QFT.listMatrix (lowerRegisterOp (.iqft 0 n : RegisterOps n))
      = (QFT.qftMatrix n).conjTranspose := by
  rw [lowerRegisterOp_iqft_whole, QFT.qftInvGates_matrix]

/-- On the whole register the lowered `qft` denotes the channel of the
    quantum Fourier transform. -/
theorem unitaryDenote_lowerRegisterOp_qft :
    GateUnitarity.unitaryDenote (Circuit.ofList (lowerRegisterOp (.qft 0 n : RegisterOps n)))
      = UnitaryChannel.unitaryChannel (QFT.qftUnitary n) := by
  rw [lowerRegisterOp_qft_whole, QFT.unitaryDenote_qftGates]

/-- On the whole register the lowered `iqft` denotes the channel of the
    inverse of the quantum Fourier transform. -/
theorem unitaryDenote_lowerRegisterOp_iqft :
    GateUnitarity.unitaryDenote (Circuit.ofList (lowerRegisterOp (.iqft 0 n : RegisterOps n)))
      = UnitaryChannel.unitaryChannel (QFT.qftUnitary n)⁻¹ := by
  rw [lowerRegisterOp_iqft_whole, QFT.unitaryDenote_qftInvGates]

/-- On the whole register `qft 0 n` denotes the channel of the quantum Fourier
    transform. -/
theorem denote_qft_whole :
    OpDenote.denote (.qft 0 n : RegisterOps n)
      = UnitaryChannel.unitaryChannel (QFT.qftUnitary n) :=
  unitaryDenote_lowerRegisterOp_qft

/-- On the whole register `iqft 0 n` denotes the channel of the inverse
    quantum Fourier transform. -/
theorem denote_iqft_whole :
    OpDenote.denote (.iqft 0 n : RegisterOps n)
      = UnitaryChannel.unitaryChannel (QFT.qftUnitary n)⁻¹ :=
  unitaryDenote_lowerRegisterOp_iqft

/-- `barrier` denotes the identity (unfolding lemma of the instance). -/
theorem denote_barrier :
    (OpDenote.denote (.barrier : RegisterOps n) : QComp (2 ^ n) Unit) = QComp.qpure () :=
  rfl

/-- QFT on the window `[0, 3)` of 6 qubits, inverse QFT on the same window,
    measure qubit 0. -/
def qftRoundTrip : HQPLProg 6 Bool :=
  applyQFT 0 3 (applyIQFT 0 3 (.meas 0 (.ret true) (.ret false)))

/-- The QFT round trip and its lowering to QPL have the same denotation. -/
theorem lowerHQPL_qftRoundTrip_denote :
    (lowerHQPL qftRoundTrip).denote = XQPL.denote qftRoundTrip :=
  lowerHQPL_denote _

/-- Gate count of barrier example is 3 (barrier counts as custom op). -/
theorem barrierExample_gateCount : barrierExample.gateCount = 3 := rfl

/-! ## The matrices of phase estimation and amplitude amplification -/

section Matrices

open scoped Matrix
open CatCrypt.Quantum.ControlledGates CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Programs.Qubit CatCrypt.Quantum.Optimization
open CatCrypt.Quantum.QFT (listMatrix listMatrix_nil listMatrix_cons listMatrix_append)

/-- Every operation denotes the unitary channel of the circuit of its lowering,
    whose matrix is `QFT.listMatrix (lowerRegisterOp op)`. -/
theorem denote_eq_unitaryChannel (op : RegisterOps n) :
    OpDenote.denote op
      = UnitaryChannel.unitaryChannel
          (RoutingPerm.circuitUnitary (Circuit.ofList (lowerRegisterOp op))) :=
  QFT.unitaryDenote_ofList _

/-- The matrix of a gate list is unitary. -/
theorem listMatrix_mul_conjTranspose (l : List (Gate n)) :
    listMatrix l * (listMatrix l)ᴴ = 1 :=
  Matrix.mem_unitaryGroup_iff.mp (RoutingPerm.circuitUnitary (Circuit.ofList l)).2

/-- The matrix of `powGates l k` is the `k`-th power of the matrix of `l`. -/
theorem listMatrix_powGates (l : List (Gate n)) (k : ℕ) :
    listMatrix (powGates l k) = listMatrix l ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [powGates, List.replicate_succ, List.flatten_cons, listMatrix_append, ← powGates, ih,
      pow_succ]

/-- The matrix of a mapped list of gates is the product of the gate matrices,
    the head gate rightmost. -/
theorem listMatrix_map {β : Type} (f : β → Gate n) (xs : List β) :
    listMatrix (xs.map f) = (xs.map fun x => gateEmbedding (f x)).reverse.prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [listMatrix_cons, ih]

/-- The matrix of a flat-mapped list of gates is the product of the matrices of
    the pieces, the head piece rightmost. -/
theorem listMatrix_flatMap {β : Type} (f : β → List (Gate n)) (xs : List β) :
    listMatrix (xs.flatMap f) = (xs.map fun x => listMatrix (f x)).reverse.prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [listMatrix_append, ih]

/-- A gate of `powGates l k` is a gate of `l`. -/
theorem mem_powGates {l : List (Gate n)} {k : ℕ} {g : Gate n} (h : g ∈ powGates l k) :
    g ∈ l := by
  grind [powGates, List.mem_flatten]

/-- **Phase estimation.** For a target circuit `U` that does not act on the
    counting register `[start, start + len)`, the lowered phase estimation
    realises the Hadamards on the counting register, then the controlled powers
    `C_{start+i}(U^(2^(len-1-i)))` for `i = 0, …, len - 1`, then the inverse QFT on
    the counting register. -/
theorem listMatrix_phaseEstimationGates {start len : ℕ} (h : start + len ≤ n)
    {U : List (Gate n)} (hU : ∀ g ∈ U, ∀ i : Fin len, Avoids (windowQubit h i) g) :
    listMatrix (phaseEstimationGates start len U)
      = listMatrix (registerGates start len (QFT.qftInvGates len) : List (Gate n))
        * ((List.finRange len).map fun i =>
            ctrlMatrix (windowQubit h i) (listMatrix U ^ 2 ^ (len - 1 - i.val))).reverse.prod
        * ((List.finRange len).map fun i =>
            embedGate1 n (windowQubit h i) hadamard).reverse.prod := by
  rw [phaseEstimationGates, dite_eq_left h, listMatrix_append, listMatrix_append,
    listMatrix_flatMap, listMatrix_map, ← mul_assoc]
  congr 2
  · congr 2
    refine List.map_congr_left fun i _ => ?_
    rw [listMatrix_ctrlList (fun g hg => hU g (mem_powGates hg) i), listMatrix_powGates]

/-- The projector `|0…0⟩⟨0…0|` onto the all-zero state, as the product of the
    projectors `|0⟩⟨0|` on each qubit. -/
def zeroProj (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  ((List.finRange n).map fun q => embedGate1 n q proj0).prod

/-- The Grover iterate `G = (2|ψ⟩⟨ψ| - I) O` with `|ψ⟩⟨ψ| = A |0…0⟩⟨0…0| A†`. -/
def groverIterate (O A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  ((2 : ℂ) • (A * zeroProj n * Aᴴ) - 1) * O

/-- A product of single-qubit operators on qubits other than `c` commutes with
    every single-qubit operator on `c`. -/
theorem commOn_prod_embedGate1 {c : Fin n} (G : Matrix (Fin 2) (Fin 2) ℂ) :
    ∀ {qs : List (Fin n)}, (∀ q ∈ qs, q ≠ c) →
      CommOn c ((qs.map fun q => embedGate1 n q G).prod)
  | [], _ => commOn_one c
  | q :: qs, h => by
    rw [List.map_cons, List.prod_cons]
    exact (commOn_embedGate1 (h q List.mem_cons_self) G).mul
      (commOn_prod_embedGate1 G fun q' hq' => h q' (List.mem_cons_of_mem q hq'))

/-- Conjugating a product of single-qubit operators `G` on distinct qubits by
    `X` on those qubits gives the product of the operators `X G X`. -/
theorem listMatrix_X_conj :
    ∀ {qs : List (Fin n)}, qs.Nodup → ∀ G : Matrix (Fin 2) (Fin 2) ℂ,
      listMatrix (qs.map Gate.X) * (qs.map fun q => embedGate1 n q G).prod
          * listMatrix (qs.map Gate.X)
        = (qs.map fun q => embedGate1 n q (pauliX * G * pauliX)).prod
  | [], _, _ => by simp [listMatrix_nil]
  | q :: qs, hnd, G => by
    obtain ⟨hq, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons, listMatrix_cons, List.prod_cons]
    change _ * embedGate1 n q pauliX * _ * (_ * embedGate1 n q pauliX) = _
    have hL : CommOn q (listMatrix (qs.map Gate.X)) := commOn_listMatrix fun g hg => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg
      exact fun h => hq (h ▸ hr)
    have hP : CommOn q ((qs.map fun r => embedGate1 n r G).prod) :=
      commOn_prod_embedGate1 G fun r hr h => hq (h ▸ hr)
    set L := listMatrix (qs.map Gate.X)
    set P := (qs.map fun r => embedGate1 n r G).prod
    have key : P * (L * embedGate1 n q pauliX) = embedGate1 n q pauliX * (P * L) := by
      rw [← hL pauliX, ← mul_assoc, ← hP pauliX, mul_assoc]
    calc L * embedGate1 n q pauliX * (embedGate1 n q G * P) * (L * embedGate1 n q pauliX)
        = L * (embedGate1 n q pauliX * embedGate1 n q G * embedGate1 n q pauliX) * (P * L) := by
          rw [mul_assoc (L * _) (embedGate1 n q G * P), mul_assoc (embedGate1 n q G) P, key]
          simp only [mul_assoc]
      _ = embedGate1 n q (pauliX * G * pauliX) * (L * P * L) := by
          rw [embedGate1_mul, embedGate1_mul, ← hL]
          simp only [mul_assoc]
      _ = _ := by rw [listMatrix_X_conj hnd' G]

/-- The doubly-applied `X` layer is the identity. -/
theorem listMatrix_X_mul_self {qs : List (Fin n)} (hnd : qs.Nodup) :
    listMatrix (qs.map Gate.X) * listMatrix (qs.map Gate.X) = 1 := by
  have := listMatrix_X_conj hnd 1
  simp_all [embedGate1_one, pauliX_sq]

/-- The multi-controlled `Z` of `zeroReflectGates` is `I - 2 |1…1⟩⟨1…1|`. -/
theorem listMatrix_mctrlZ (m : ℕ) :
    listMatrix (mctrlGates ((List.finRange m).map Fin.succ) (Gate.Z (0 : Fin (m + 1))))
      = 1 + (-2 : ℂ) • ((List.finRange (m + 1)).map fun q => embedGate1 (m + 1) q proj1).prod := by
  have hnd : ((List.finRange m).map Fin.succ).Nodup :=
    (List.nodup_finRange m).map (Fin.succ_injective _)
  have hav : ∀ c ∈ (List.finRange m).map Fin.succ, Avoids c (Gate.Z (0 : Fin (m + 1))) := by
    intro c hc
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hc
    exact (Fin.succ_ne_zero j).symm
  have h0 : ∀ q ∈ (List.finRange m).map Fin.succ, q ≠ (0 : Fin (m + 1)) := by
    intro q hq
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hq
    exact Fin.succ_ne_zero j
  have hZ : pauliZ = 1 + (-2 : ℂ) • proj1 := by
    simp [pauliZ, proj1, ← Matrix.ext_iff, Fin.forall_fin_succ]
    norm_num
  rw [listMatrix_mctrlGates hnd hav, mctrlMatrix_eq]
  change 1 + _ * (embedGate1 (m + 1) 0 pauliZ - 1) = _
  rw [hZ, embedGate1_map_add, embedGate1_one, embedGate1_smul, add_sub_cancel_left,
    Matrix.mul_smul, ← commOn_prod_embedGate1 proj1 h0 proj1, List.finRange_succ, List.map_cons,
    List.prod_cons]

/-- The matrix of `zeroReflectGates n` is `2|0…0⟩⟨0…0| - I`. -/
theorem listMatrix_zeroReflectGates :
    ∀ n : ℕ, listMatrix (zeroReflectGates n) = (2 : ℂ) • zeroProj n - 1
  | 0 => by
    simp only [zeroReflectGates, zeroProj, listMatrix_nil, List.finRange_zero, List.map_nil,
      List.prod_nil]
    rw [two_smul]
    abel
  | m + 1 => by
    have hs : listMatrix [Gate.X (0 : Fin (m + 1)), Gate.Z 0, Gate.X 0, Gate.Z 0] = -1 := by
      simp only [listMatrix_cons, listMatrix_nil, one_mul]
      change embedGate1 _ 0 pauliZ * embedGate1 _ 0 pauliX * embedGate1 _ 0 pauliZ
        * embedGate1 _ 0 pauliX = -1
      have hm : pauliZ * pauliX * pauliZ * pauliX = (-1 : ℂ) • 1 := by
        simp [pauliZ, pauliX, ← Matrix.ext_iff, Fin.forall_fin_succ]
      rw [embedGate1_mul, embedGate1_mul, embedGate1_mul, hm, embedGate1_smul, embedGate1_one,
        neg_one_smul]
    have hLL := listMatrix_X_mul_self (List.nodup_finRange (m + 1))
    have hLPL := listMatrix_X_conj (List.nodup_finRange (m + 1)) proj1
    rw [pauliX_proj1_pauliX] at hLPL
    rw [zeroReflectGates, listMatrix_append, listMatrix_append, listMatrix_append, hs,
      listMatrix_mctrlZ, zeroProj, ← hLPL]
    set L := listMatrix ((List.finRange (m + 1)).map Gate.X)
    rw [mul_add, add_mul, mul_one, Matrix.mul_smul, Matrix.smul_mul, neg_one_mul, neg_mul,
      neg_mul, hLL, neg_mul]
    module

/-- The matrix of one lowered Grover iteration is the Grover iterate. -/
theorem listMatrix_groverIterateGates (O A : List (Gate n)) :
    listMatrix (groverIterateGates O A) = groverIterate (listMatrix O) (listMatrix A) := by
  rw [groverIterateGates, listMatrix_append, listMatrix_append, listMatrix_append,
    QFT.listMatrix_invGates, listMatrix_zeroReflectGates, groverIterate, mul_sub, sub_mul,
    mul_one, listMatrix_mul_conjTranspose, Matrix.mul_smul, Matrix.smul_mul]

/-- **Amplitude amplification.** The lowered amplitude amplification with
    oracle `O`, state preparation `A` and `k` iterations realises `G^k`, the
    `k`-th power of the Grover iterate `G = (2|ψ⟩⟨ψ| - I) O`, `|ψ⟩ = A|0…0⟩`. -/
theorem listMatrix_amplitudeAmplificationGates (O A : List (Gate n)) (k : ℕ) :
    listMatrix (amplitudeAmplificationGates O A k)
      = groverIterate (listMatrix O) (listMatrix A) ^ k := by
  rw [amplitudeAmplificationGates, listMatrix_powGates, listMatrix_groverIterateGates]

/-- The lowered `phaseEstimation` realises the matrix of
    `listMatrix_phaseEstimationGates`. -/
theorem listMatrix_lowerRegisterOp_phaseEstimation {start len : ℕ} (h : start + len ≤ n)
    {U : List (Gate n)} (hU : ∀ g ∈ U, ∀ i : Fin len, Avoids (windowQubit h i) g) :
    listMatrix (lowerRegisterOp (.phaseEstimation start len U : RegisterOps n))
      = listMatrix (registerGates start len (QFT.qftInvGates len) : List (Gate n))
        * ((List.finRange len).map fun i =>
            ctrlMatrix (windowQubit h i) (listMatrix U ^ 2 ^ (len - 1 - i.val))).reverse.prod
        * ((List.finRange len).map fun i =>
            embedGate1 n (windowQubit h i) hadamard).reverse.prod :=
  listMatrix_phaseEstimationGates h hU

/-- The lowered `amplitudeAmplification O A k` realises `G^k`. -/
theorem listMatrix_lowerRegisterOp_amplitudeAmplification (O A : List (Gate n)) (k : ℕ) :
    listMatrix (lowerRegisterOp (.amplitudeAmplification O A k : RegisterOps n))
      = groverIterate (listMatrix O) (listMatrix A) ^ k :=
  listMatrix_amplitudeAmplificationGates O A k

end Matrices

end CatCrypt.Quantum.HQPL
