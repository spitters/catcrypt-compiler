/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.Optimization.RoutingPerm
public import CatCrypt.Quantum.Optimization.DisjointCommute
public import CatCrypt.Quantum.Optimization.MixedCommute

/-!
# Qubit relabelling and SWAP-conjugation ("braiding")

This file provides the braiding lemmas that justify the corrected hardware
routing pass. The bug being fixed lives in `routeGate` (`HardwareRouting.lean`):
it wraps a non-adjacent two-qubit gate `g` on `(i, j)` as

    `swapGate i mid ; g ; swapGate i mid`

with the **same** middle gate `g`. Under the unitary semantics
(`unitaryDenote`) the SWAP unitary `S` is self-inverse, so the block realizes
`S · U_g · S` — gate `g` with qubits `i` and `mid` interchanged. The fix is to
emit the *relabelled* gate `g.relabel i mid` in the middle, so that
`S · U_{g.relabel} · S = U_g`.

## Main definitions

* `Gate.relabel g a b` — apply `Equiv.swap a b` to every qubit index of `g`.

## Main results

* `Gate.relabel_involutive`     — relabelling twice by the same pair is the identity.
* `swapBitPerm a b`             — the basis-index permutation that swaps the two
  bit positions `pos n a`, `pos n b` read by qubits `a`, `b` under the
  `embedGate` (MSB) convention.
* `swapGate_circuitUnitary`     — the 3-CNOT SWAP-gate unitary is the
  qubit-transposition permutation matrix `qubitPermUnitary (swapBitPerm a b)`.
* `gateEmbedding_relabel`       — relabelling a gate's qubits equals conjugating
  its embedding by the qubit-permutation, for the two-qubit (`CNOT`/`CZ`) gates
  that the routing pass relabels.
* `swapConj_relabel`            — the directly routing-useful corollary:
  `S · U_{g.relabel a b} · S = U_g` with `S := circuitUnitary (swapGate a b)`.

## A convention note (important)

`qubitPermUnitary` (in `RoutingPerm.lean`) realizes a qubit permutation through
`finFunctionFinEquiv`, under which qubit `k` is read at bit position `k.val`
(an LSB-first convention). The gate embeddings `embedGate1`/`embedGate2`
(in `QCircuit.lean`) read qubit `k` at bit position `pos n k = n - 1 - k.val`
(an MSB-first convention). These two conventions are *reversed* relative to one
another.

Consequently the literal identity `circuitUnitary (swapGate a b) =
qubitPermUnitary (Equiv.swap a b)` is **false** for `n ≥ 3` (e.g. `n = 3`,
`a = 0`, `b = 1`: the SWAP circuit swaps bit positions `{2, 1}` whereas
`qubitPermUnitary (swap 0 1)` swaps bit positions `{0, 1}`). The honest and
correct statement, proved here as `swapGate_circuitUnitary`, names the
permutation in the *embedding's* bit-position convention via
`swapBitPerm a b := Equiv.swap ⟨pos n a⟩ ⟨pos n b⟩`. The braiding corollary
`swapConj_relabel`, which is what the routing fix actually consumes, is stated
directly in terms of the SWAP-circuit unitary `S` and is convention-free.

## References

* Hietala et al. — A Verified Optimizer for Quantum Circuits (POPL 2021)
* Nielsen & Chuang — Quantum Computation and Quantum Information, §1.3 (SWAP)
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix
open CatCrypt.Quantum CatCrypt.Quantum.QCircuit
open CatCrypt.Quantum.UnitaryChannel CatCrypt.Quantum.GateUnitarity
open CatCrypt.Quantum.Optimization.HardwareRouting
open CatCrypt.Quantum.Optimization.RoutingPerm
open CatCrypt.Quantum.Optimization.DisjointCommute
open CatCrypt.Quantum.Optimization.MixedCommute

noncomputable section

namespace CatCrypt.Quantum.Optimization.SwapConj

variable {n : ℕ}

/-! ## Deliverable 1: `Gate.relabel` lemmas

(`Gate.relabel` itself is defined in `HardwareRouting.lean`, before `routeGate`,
which consumes it.) -/

@[simp]
theorem Gate.relabel_CNOT (i j a b : Fin n) :
    (Gate.CNOT i j).relabel a b = Gate.CNOT (Equiv.swap a b i) (Equiv.swap a b j) := rfl

@[simp]
theorem Gate.relabel_CZ (i j a b : Fin n) :
    (Gate.CZ i j).relabel a b = Gate.CZ (Equiv.swap a b i) (Equiv.swap a b j) := rfl

/-- Relabelling by the same transposition twice is the identity (`Equiv.swap` is
    an involution). -/
theorem Gate.relabel_involutive (g : Gate n) (a b : Fin n) :
    (g.relabel a b).relabel a b = g := by
  cases g <;>
    simp only [Gate.relabel, Equiv.swap_apply_self]

/-! ## Bit action of a qubit permutation

`qubitPermUnitary σ` is a permutation matrix; its `(r, c)` entry is `1` exactly
when `c = qubitBitPerm σ r`. We need to know how `qubitBitPerm σ` acts on the
*bits* of a basis index: relabelling coordinate `k` to `σ k`, i.e. bit position
`k.val` of the output reads bit position `(σ.symm k).val` of the input. -/

/-- Entry formula for the qubit-permutation unitary as a permutation matrix. -/
theorem qubitPermUnitary_apply (σ : Equiv.Perm (Fin n)) (r c : Fin (2 ^ n)) :
    (qubitPermUnitary σ : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) r c =
      if c = qubitBitPerm σ r then 1 else 0 := by
  show (qubitBitPerm σ).permMatrix ℂ r c = _
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  simp only [Option.mem_def, Option.some.injEq, eq_comm]

/-- The coordinate-`b` value of `finFunctionFinEquiv.symm x` is `x`'s bit at
    position `b.val`. -/
theorem finFunctionFinEquiv_symm_testBit (x : Fin (2 ^ n)) (b : Fin n) :
    (finFunctionFinEquiv.symm x b).val = (x.val.testBit b.val).toNat := by
  rw [finFunctionFinEquiv_symm_apply_val, Nat.toNat_testBit]

/-- The bit action of a qubit permutation: bit position `b.val` of
    `qubitBitPerm σ x` reads bit position `(σ.symm b).val` of `x`. This is the
    coordinate relabelling `f ↦ f ∘ σ.symm` of `bitFunPerm`, transported through
    `finFunctionFinEquiv`. -/
theorem qubitBitPerm_testBit (σ : Equiv.Perm (Fin n)) (x : Fin (2 ^ n)) (b : Fin n) :
    (qubitBitPerm σ x).val.testBit b.val = x.val.testBit ((σ.symm b).val) := by
  -- Compare `.toNat`s of both bits, which are equal coordinate values.
  have key : ((qubitBitPerm σ x).val.testBit b.val).toNat =
      (x.val.testBit ((σ.symm b).val)).toNat := by
    rw [← finFunctionFinEquiv_symm_testBit (qubitBitPerm σ x) b,
        ← finFunctionFinEquiv_symm_testBit x (σ.symm b)]
    -- Both are coordinate `b` of the relabelled bit-vector.
    show ((finFunctionFinEquiv.symm (qubitBitPerm σ x)) b).val = _
    rw [qubitBitPerm]
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    rw [bitFunPerm, Equiv.arrowCongr_apply]
    simp only [Equiv.coe_refl, id_eq, Function.comp]
  generalize (qubitBitPerm σ x).val.testBit b.val = L at key
  generalize x.val.testBit ((σ.symm b).val) = R at key
  cases L <;> cases R <;> simp_all

/-! ## Conjugation by a qubit-permutation matrix reindexes entries

Multiplying a matrix on the left by `P_σ` reindexes its row by `qubitBitPerm σ`;
on the right by `P_σ⁻¹` reindexes its column by `qubitBitPerm σ` (using that
`qubitBitPerm` is a homomorphism, so `qubitBitPerm σ⁻¹ = (qubitBitPerm σ)⁻¹`).
The two combine: conjugation reindexes both row and column by `qubitBitPerm σ`. -/

private theorem permMatrix_left_apply (σ : Equiv.Perm (Fin n))
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (r c : Fin (2 ^ n)) :
    ((qubitPermUnitary σ).val * M) r c = M (qubitBitPerm σ r) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (qubitBitPerm σ r)]
  · rw [qubitPermUnitary_apply, ite_eq_left rfl, one_mul]
  · intro k _ hk
    rw [qubitPermUnitary_apply, ite_eq_right hk, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

private theorem permMatrix_right_apply (σ : Equiv.Perm (Fin n))
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (r c : Fin (2 ^ n)) :
    (M * (qubitPermUnitary σ).val) r c = M r ((qubitBitPerm σ).symm c) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ((qubitBitPerm σ).symm c)]
  · rw [qubitPermUnitary_apply, Equiv.apply_symm_apply, ite_eq_left rfl, mul_one]
  · intro k _ hk
    rw [qubitPermUnitary_apply]
    rw [ite_eq_right (fun h => hk (by rw [h, Equiv.symm_apply_apply])), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `qubitBitPerm` of the inverse permutation is the inverse of `qubitBitPerm`. -/
theorem qubitBitPerm_inv (σ : Equiv.Perm (Fin n)) :
    qubitBitPerm σ⁻¹ = (qubitBitPerm σ)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← qubitBitPerm_mul, inv_mul_cancel, qubitBitPerm_one]

/-- **Conjugation reindexes both indices.** Conjugating a matrix by the
    qubit-permutation `σ` evaluates the original at row/column both relabelled by
    `qubitBitPerm σ`. -/
theorem conj_qubitPermUnitary_apply (σ : Equiv.Perm (Fin n))
    (M : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (r c : Fin (2 ^ n)) :
    ((qubitPermUnitary σ).val * M * (qubitPermUnitary σ⁻¹).val) r c =
      M (qubitBitPerm σ r) (qubitBitPerm σ c) := by
  rw [permMatrix_right_apply, permMatrix_left_apply, qubitBitPerm_inv, Equiv.Perm.inv_def,
    Equiv.symm_symm]

/-! ## The qubit transposition in the embedding's bit-position convention

The SWAP *circuit* `swapGate a b` swaps the two bit positions
`pos n a = n - 1 - a.val` and `pos n b = n - 1 - b.val` that qubits `a`, `b`
read under the `embedGate` (MSB-first) convention. The corresponding
basis-index permutation is `qubitPermUnitary (swapBitPerm a b)`, where
`swapBitPerm a b` is the transposition of the *position* indices. (See the
module convention note for why this is not `Equiv.swap a b` itself.) -/

/-- The `Fin n` index whose `finFunctionFinEquiv` bit position equals the
    `embedGate` position `pos n k = n - 1 - k.val` of qubit `k`. -/
def posIdx (k : Fin n) : Fin n := ⟨pos n k, pos_lt k⟩

/-- `posIdx` is injective (distinct qubits read distinct positions). -/
theorem posIdx_inj {a b : Fin n} (h : posIdx a = posIdx b) : a = b := by
  have hv := congrArg Fin.val h
  simp only [posIdx, pos, Fin.val_mk] at hv
  have ha := a.isLt; have hb := b.isLt
  apply Fin.ext; omega

/-- The qubit transposition realized by `swapGate a b`, named in the embedding's
    bit-position convention. -/
def swapBitPerm (a b : Fin n) : Equiv.Perm (Fin n) := Equiv.swap (posIdx a) (posIdx b)

/-- Applying the position transposition to `posIdx k` yields `posIdx (swap a b k)`.
    This is the bridge between the two conventions. -/
theorem swapBitPerm_posIdx (a b k : Fin n) :
    swapBitPerm a b (posIdx k) = posIdx (Equiv.swap a b k) := by
  unfold swapBitPerm
  rcases eq_or_ne k a with hka | hka
  · subst hka
    rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
  · rcases eq_or_ne k b with hkb | hkb
    · subst hkb
      rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne (fun h => hka (posIdx_inj h))
          (fun h => hkb (posIdx_inj h)),
        Equiv.swap_apply_of_ne_of_ne hka hkb]

/-- The transposition is an involution, so `swapBitPerm a b` is its own inverse. -/
@[simp]
theorem swapBitPerm_symm (a b : Fin n) : (swapBitPerm a b).symm = swapBitPerm a b :=
  Equiv.symm_swap _ _

/-- Bit action of `swapBitPerm a b` at an `embedGate` qubit position: the bit at
    `pos n k` of `qubitBitPerm (swapBitPerm a b) x` reads the bit at
    `pos n (swap a b k)` of `x`. -/
theorem qubitBitPerm_swapBitPerm_testBit_pos (a b : Fin n) (x : Fin (2 ^ n)) (k : Fin n) :
    (qubitBitPerm (swapBitPerm a b) x).val.testBit (pos n k) =
      x.val.testBit (pos n (Equiv.swap a b k)) := by
  have h := qubitBitPerm_testBit (swapBitPerm a b) x (posIdx k)
  rw [swapBitPerm_symm, swapBitPerm_posIdx] at h
  exact h

/-! ## Deliverable 3: the braiding identity for two-qubit gates

The routing pass only relabels two-qubit gates (`CNOT`/`CZ`). For these we prove
that relabelling the gate's qubits equals conjugating its embedding by the
qubit-permutation matrix. We work through the generic `embedGate2` entry formula
and the bit action `qubitBitPerm_swapBitPerm_testBit_pos`. -/

/-- `gbit` of the permuted index at qubit `k` reads `gbit` of the original at
    qubit `swap a b k`. -/
theorem gbit_qubitBitPerm_swap (a b : Fin n) (x : Fin (2 ^ n)) (k : Fin n) :
    gbit n k (qubitBitPerm (swapBitPerm a b) x).val =
      gbit n (Equiv.swap a b k) x.val := by
  apply Fin.ext
  rw [gbit_eq_testBit, gbit_eq_testBit, qubitBitPerm_swapBitPerm_testBit_pos]

/-- `idx4` of the permuted index at qubits `i, j` reads `idx4` of the original at
    qubits `swap a b i, swap a b j`. -/
theorem idx4_qubitBitPerm_swap (a b i j : Fin n) (x : Fin (2 ^ n)) :
    idx4 n i j (qubitBitPerm (swapBitPerm a b) x).val =
      idx4 n (Equiv.swap a b i) (Equiv.swap a b j) x.val := by
  simp only [idx4, gbit_qubitBitPerm_swap]

/-- The `Match2` predicate is equivalent to per-qubit agreement at all `pos n k`
    positions except `pos n i`, `pos n j`. (Positions `≥ n` carry no bits.) -/
theorem match2_iff_pos (i j : Fin n) (r c : Fin (2 ^ n)) :
    Match2 n i j r.val c.val ↔
      ∀ k : Fin n, k ≠ i → k ≠ j → r.val.testBit (pos n k) = c.val.testBit (pos n k) := by
  constructor
  · intro h k hki hkj; exact h (pos n k) (pos_ne hki) (pos_ne hkj)
  · intro h p hpi hpj
    by_cases hp : p < n
    · set k : Fin n := ⟨n - 1 - p, by omega⟩ with hk
      have hposk : pos n k = p := by simp only [pos, hk]; omega
      have hki : k ≠ i := fun hh => hpi (hposk ▸ congrArg (pos n) hh)
      have hkj : k ≠ j := fun hh => hpj (hposk ▸ congrArg (pos n) hh)
      have := h k hki hkj; rwa [hposk] at this
    · push_neg at hp
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le r.isLt (Nat.pow_le_pow_right (by omega) hp)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le c.isLt (Nat.pow_le_pow_right (by omega) hp))]

/-- The `Match2` predicate transports across the permutation: matching the
    permuted indices off `{i, j}` is the same as matching the originals off the
    relabelled pair `{swap a b i, swap a b j}`. -/
theorem match2_qubitBitPerm_swap (a b i j : Fin n) (r c : Fin (2 ^ n)) :
    Match2 n i j (qubitBitPerm (swapBitPerm a b) r).val
        (qubitBitPerm (swapBitPerm a b) c).val ↔
      Match2 n (Equiv.swap a b i) (Equiv.swap a b j) r.val c.val := by
  rw [match2_iff_pos, match2_iff_pos]
  constructor
  · intro h k hki hkj
    -- write k = swap a b m with m = swap a b k; then m ≠ i, m ≠ j and apply h at m
    have hmi : Equiv.swap a b k ≠ i := by
      intro hh
      apply hki
      have := congrArg (Equiv.swap a b) hh
      rwa [Equiv.swap_apply_self] at this
    have hmj : Equiv.swap a b k ≠ j := by
      intro hh
      apply hkj
      have := congrArg (Equiv.swap a b) hh
      rwa [Equiv.swap_apply_self] at this
    have hm := h (Equiv.swap a b k) hmi hmj
    simpa only [qubitBitPerm_swapBitPerm_testBit_pos, Equiv.swap_apply_self] using hm
  · intro h k hki hkj
    rw [qubitBitPerm_swapBitPerm_testBit_pos, qubitBitPerm_swapBitPerm_testBit_pos]
    have hmi : Equiv.swap a b k ≠ Equiv.swap a b i := by
      intro hh; exact hki ((Equiv.swap a b).injective hh)
    have hmj : Equiv.swap a b k ≠ Equiv.swap a b j := by
      intro hh; exact hkj ((Equiv.swap a b).injective hh)
    exact h (Equiv.swap a b k) hmi hmj

/-- **Braiding for `embedGate2`.** Embedding a two-qubit gate on the relabelled
    qubit pair `(swap a b i, swap a b j)` equals conjugating the embedding on the
    original pair `(i, j)` by the qubit-permutation matrix
    `qubitPermUnitary (swapBitPerm a b)`. -/
theorem embedGate2_relabel (a b : Fin n) (G : Matrix (Fin 4) (Fin 4) ℂ)
    {i j : Fin n} (hij : i ≠ j)
    (hij' : Equiv.swap a b i ≠ Equiv.swap a b j) :
    embedGate2 n (Equiv.swap a b i) (Equiv.swap a b j) G hij' =
      (qubitPermUnitary (swapBitPerm a b)).val *
        embedGate2 n i j G hij *
        (qubitPermUnitary (swapBitPerm a b)⁻¹).val := by
  ext r c
  rw [conj_qubitPermUnitary_apply, embedGate2_apply hij', embedGate2_apply hij]
  by_cases hM : Match2 n (Equiv.swap a b i) (Equiv.swap a b j) r.val c.val
  · rw [ite_eq_left hM, ite_eq_left ((match2_qubitBitPerm_swap a b i j r c).mpr hM),
      idx4_qubitBitPerm_swap, idx4_qubitBitPerm_swap]
  · rw [ite_eq_right hM, ite_eq_right (fun hc => hM ((match2_qubitBitPerm_swap a b i j r c).mp hc))]

/-! ## Deliverable 3 (assembled): `gateEmbedding_relabel` for `CNOT`/`CZ`

For the two-qubit gates the routing pass relabels, the gate embedding of the
relabelled gate is the conjugation of the embedding by the qubit-permutation. -/

/-- Relabelling a `CNOT`/`CZ` gate's qubits equals conjugating its embedding by
    the qubit-permutation `qubitPermUnitary (swapBitPerm a b)`. (This is the core
    braiding identity the routing fix consumes; single-qubit gates are handled by
    `gateEmbedding_relabel`.) -/
theorem gateEmbedding_relabel_two (g : Gate n) (a b : Fin n)
    (hg : (∃ i j, g = Gate.CNOT i j) ∨ (∃ i j, g = Gate.CZ i j)) :
    gateEmbedding (g.relabel a b) =
      (qubitPermUnitary (swapBitPerm a b)).val * gateEmbedding g *
        (qubitPermUnitary (swapBitPerm a b)⁻¹).val := by
  rcases hg with ⟨i, j, rfl⟩ | ⟨i, j, rfl⟩
  · -- CNOT
    simp only [Gate.relabel_CNOT, gateEmbedding]
    by_cases hij : i = j
    · subst hij
      simp only [dite_eq_left trivial, mul_one]
      have : (qubitPermUnitary (swapBitPerm a b)).val *
          (qubitPermUnitary (swapBitPerm a b)⁻¹).val = 1 := by
        rw [← UnitaryGroup.mul_val, ← qubitPermUnitary_mul, inv_mul_cancel,
          qubitPermUnitary_one, UnitaryGroup.one_val]
      rw [this]
    · have hij' : Equiv.swap a b i ≠ Equiv.swap a b j := fun h => hij (by
        have := congrArg (Equiv.swap a b) h
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_self] at this)
      rw [dite_eq_right hij', dite_eq_right hij]
      exact embedGate2_relabel a b Programs.Qubit.cnot hij hij'
  · -- CZ
    simp only [Gate.relabel_CZ, gateEmbedding]
    by_cases hij : i = j
    · subst hij
      simp only [dite_eq_left trivial, mul_one]
      have : (qubitPermUnitary (swapBitPerm a b)).val *
          (qubitPermUnitary (swapBitPerm a b)⁻¹).val = 1 := by
        rw [← UnitaryGroup.mul_val, ← qubitPermUnitary_mul, inv_mul_cancel,
          qubitPermUnitary_one, UnitaryGroup.one_val]
      rw [this]
    · have hij' : Equiv.swap a b i ≠ Equiv.swap a b j := fun h => hij (by
        have := congrArg (Equiv.swap a b) h
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_self] at this)
      rw [dite_eq_right hij', dite_eq_right hij]
      exact embedGate2_relabel a b czGate hij hij'

/-- **Deliverable 3.** Relabelling a gate's qubits equals conjugating its
    embedding by the qubit-permutation, stated for the two-qubit `CNOT`/`CZ`
    gates the routing pass relabels. The permutation is `swapBitPerm a b` (the
    transposition in the embedding's bit-position convention; see the module
    convention note). -/
theorem gateEmbedding_relabel_CNOT (i j a b : Fin n) :
    gateEmbedding ((Gate.CNOT i j).relabel a b) =
      (qubitPermUnitary (swapBitPerm a b)).val * gateEmbedding (Gate.CNOT i j) *
        (qubitPermUnitary (swapBitPerm a b)⁻¹).val :=
  gateEmbedding_relabel_two (Gate.CNOT i j) a b (Or.inl ⟨i, j, rfl⟩)

theorem gateEmbedding_relabel_CZ (i j a b : Fin n) :
    gateEmbedding ((Gate.CZ i j).relabel a b) =
      (qubitPermUnitary (swapBitPerm a b)).val * gateEmbedding (Gate.CZ i j) *
        (qubitPermUnitary (swapBitPerm a b)⁻¹).val :=
  gateEmbedding_relabel_two (Gate.CZ i j) a b (Or.inr ⟨i, j, rfl⟩)

/-! ## Deliverable 2: the SWAP-gate unitary is the qubit-transposition matrix

The 3-CNOT SWAP gate `swapGate a b` realizes, under `unitaryDenote`, the
permutation matrix `qubitPermUnitary (swapBitPerm a b)` that transposes the two
bit positions `pos n a`, `pos n b`. -/

/-- The Fin-4 bit transposition `x ↦ swap the two bits of x`: `0,1,2,3 ↦ 0,2,1,3`.
    This is the index action of the 4×4 `Programs.Qubit.swap` gate. -/
def qswap4 : Fin 4 → Fin 4 := ![0, 2, 1, 3]

/-- The 4×4 SWAP gate is the permutation matrix of `qswap4`. -/
theorem qubitSwap_apply (p q : Fin 4) :
    (Programs.Qubit.swap : Matrix (Fin 4) (Fin 4) ℂ) p q =
      if q = qswap4 p then 1 else 0 := by
  fin_cases p <;> fin_cases q <;>
    simp [Programs.Qubit.swap, qswap4, Matrix.of_apply]

/-- Conjugating a 4×4 matrix by `Programs.Qubit.swap` reindexes both indices by
    `qswap4`. -/
theorem qubitSwap_conj_apply (M : Matrix (Fin 4) (Fin 4) ℂ) (p q : Fin 4) :
    (Programs.Qubit.swap * M * Programs.Qubit.swap) p q = M (qswap4 p) (qswap4 q) := by
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases p <;> fin_cases q <;>
    simp [Programs.Qubit.swap, qswap4, Matrix.of_apply]

/-- `Match2` is symmetric in its two qubit arguments. -/
theorem match2_swap_pair (i j : Fin n) (r c : ℕ) :
    Match2 n j i r c ↔ Match2 n i j r c :=
  ⟨fun h p hpi hpj => h p hpj hpi, fun h p hpj hpi => h p hpi hpj⟩

/-- Flipping the two-qubit roles `(i, j) ↦ (j, i)` of an `embedGate2` conjugates
    the 4×4 gate matrix by the SWAP gate: `idx4` reverses its two bits. -/
theorem idx4_swap_pair (i j : Fin n) (v : ℕ) :
    idx4 n j i v = qswap4 (idx4 n i j v) := by
  have hi : (gbit n i v).val = 0 ∨ (gbit n i v).val = 1 := by
    have := (gbit n i v).isLt; omega
  have hj : (gbit n j v).val = 0 ∨ (gbit n j v).val = 1 := by
    have := (gbit n j v).isLt; omega
  apply Fin.ext
  simp only [idx4, qswap4]
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    simp only [hi, hj] <;> rfl

/-- **Pair-flip.** Embedding a two-qubit gate `G` on the role-swapped pair `(j, i)`
    equals embedding the SWAP-conjugate `swap₄ · G · swap₄` on the pair `(i, j)`. -/
theorem embedGate2_swap_pair {i j : Fin n} (hij : i ≠ j) (G : Matrix (Fin 4) (Fin 4) ℂ) :
    embedGate2 n j i G (Ne.symm hij) =
      embedGate2 n i j (Programs.Qubit.swap * G * Programs.Qubit.swap) hij := by
  ext r c
  rw [embedGate2_apply, embedGate2_apply]
  by_cases hM : Match2 n i j r.val c.val
  · rw [ite_eq_left ((match2_swap_pair i j r.val c.val).mpr hM), ite_eq_left hM,
      qubitSwap_conj_apply]
    rw [idx4_swap_pair i j r.val, idx4_swap_pair i j c.val]
  · rw [ite_eq_right (fun h => hM ((match2_swap_pair i j r.val c.val).mp h)), ite_eq_right hM]

/-- The textbook SWAP identity in the 4×4 gate algebra: `CNOT · (swap·CNOT·swap)
    · CNOT = swap`. -/
theorem cnot_swap_identity :
    Programs.Qubit.cnot *
        (Programs.Qubit.swap * Programs.Qubit.cnot * Programs.Qubit.swap) *
        Programs.Qubit.cnot = Programs.Qubit.swap := by
  ext p q
  fin_cases p <;> fin_cases q <;>
    simp [Programs.Qubit.cnot, Programs.Qubit.swap, Matrix.mul_apply,
      Fin.sum_univ_four, Matrix.of_apply]

/-- Decode the `idx4 = qswap4 ∘ idx4` equation into the two gate-bit equalities. -/
theorem idx4_eq_qswap4_iff (a b : Fin n) (r c : ℕ) :
    idx4 n a b c = qswap4 (idx4 n a b r) ↔
      (gbit n a c).val = (gbit n b r).val ∧ (gbit n b c).val = (gbit n a r).val := by
  rw [← idx4_swap_pair a b r]
  have hca := (gbit n a c).isLt; have hcb := (gbit n b c).isLt
  have hra := (gbit n a r).isLt; have hrb := (gbit n b r).isLt
  rw [Fin.ext_iff]
  simp only [idx4, Fin.val_mk]
  omega

/-- Membership in the bit-transposed image, decoded position-by-position: `c` is
    the `swapBitPerm a b`-relabel of `r` iff every `pos n k` bit of `c` reads the
    `pos n (swap a b k)` bit of `r`. -/
theorem eq_qubitBitPerm_swap_iff (a b : Fin n) (r c : Fin (2 ^ n)) :
    c = qubitBitPerm (swapBitPerm a b) r ↔
      ∀ k : Fin n, c.val.testBit (pos n k) = r.val.testBit (pos n (Equiv.swap a b k)) := by
  constructor
  · intro hc k
    rw [hc]; exact qubitBitPerm_swapBitPerm_testBit_pos a b r k
  · intro h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro p
    by_cases hpn : p < n
    · set k : Fin n := ⟨n - 1 - p, by omega⟩ with hk
      have hposk : pos n k = p := by simp only [pos, hk]; omega
      rw [← hposk, qubitBitPerm_swapBitPerm_testBit_pos]
      exact h k
    · push_neg at hpn
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le c.isLt
          (Nat.pow_le_pow_right (by omega) hpn)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (qubitBitPerm (swapBitPerm a b) r).isLt
          (Nat.pow_le_pow_right (by omega) hpn))]

/-- Two `gbit` values agree iff the corresponding `testBit`s agree. -/
theorem gbit_eq_iff_testBit (i j : Fin n) (v w : ℕ) :
    (gbit n i v).val = (gbit n j w).val ↔
      v.testBit (pos n i) = w.testBit (pos n j) := by
  rw [gbit_eq_testBit, gbit_eq_testBit]
  rcases v.testBit (pos n i) with _ | _ <;> rcases w.testBit (pos n j) with _ | _ <;>
    simp

/-- `embedGate2 a b swap₄` is the qubit-transposition permutation matrix
    `qubitPermUnitary (swapBitPerm a b)`: both are permutation matrices for the
    basis bijection swapping bit positions `pos n a`, `pos n b`. -/
theorem embedGate2_swap_eq_perm {a b : Fin n} (hab : a ≠ b) :
    embedGate2 n a b Programs.Qubit.swap hab =
      (qubitPermUnitary (swapBitPerm a b)).val := by
  ext r c
  rw [embedGate2_apply, qubitPermUnitary_apply]
  -- The swap-gate entry is `1` iff bits match off `{a,b}` and the gate bits are swapped.
  have hperm : c = qubitBitPerm (swapBitPerm a b) r ↔
      Match2 n a b r.val c.val ∧
        (gbit n a c.val).val = (gbit n b r.val).val ∧
        (gbit n b c.val).val = (gbit n a r.val).val := by
    rw [eq_qubitBitPerm_swap_iff]
    constructor
    · intro h
      refine ⟨?_, ?_, ?_⟩
      · intro p hpa hpb
        by_cases hpn : p < n
        · set k : Fin n := ⟨n - 1 - p, by omega⟩ with hk
          have hposk : pos n k = p := by simp only [pos, hk]; omega
          have hka : k ≠ a := fun hh => hpa (hposk ▸ congrArg (pos n) hh)
          have hkb : k ≠ b := fun hh => hpb (hposk ▸ congrArg (pos n) hh)
          rw [← hposk, h k, Equiv.swap_apply_of_ne_of_ne hka hkb]
        · push_neg at hpn
          rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le c.isLt
              (Nat.pow_le_pow_right (by omega) hpn)),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le r.isLt
              (Nat.pow_le_pow_right (by omega) hpn))]
      · rw [gbit_eq_testBit, gbit_eq_testBit, h a, Equiv.swap_apply_left]
      · rw [gbit_eq_testBit, gbit_eq_testBit, h b, Equiv.swap_apply_right]
    · rintro ⟨hMatch, hca, hcb⟩ k
      rcases eq_or_ne k a with rfl | hka
      · rw [Equiv.swap_apply_left]; exact (gbit_eq_iff_testBit k b c.val r.val).mp hca
      · rcases eq_or_ne k b with rfl | hkb
        · rw [Equiv.swap_apply_right]; exact (gbit_eq_iff_testBit k a c.val r.val).mp hcb
        · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]
          exact (hMatch (pos n k) (pos_ne hka) (pos_ne hkb)).symm
  by_cases hM : Match2 n a b r.val c.val
  · rw [ite_eq_left hM]
    show Programs.Qubit.swap (idx4 n a b r.val) (idx4 n a b c.val) = _
    rw [qubitSwap_apply]
    by_cases hc : c = qubitBitPerm (swapBitPerm a b) r
    · rw [ite_eq_left hc, ite_eq_left ((idx4_eq_qswap4_iff a b r.val c.val).mpr (hperm.mp hc).2)]
    · rw [ite_eq_right hc, ite_eq_right (fun hbits =>
        hc (hperm.mpr ⟨hM, (idx4_eq_qswap4_iff a b r.val c.val).mp hbits⟩))]
  · rw [ite_eq_right hM, ite_eq_right (fun hc => hM (hperm.mp hc).1)]

/-- **Deliverable 2.** The 3-CNOT SWAP-gate unitary is the qubit-transposition
    permutation matrix that swaps the two `embedGate` bit positions `pos n a`,
    `pos n b`.

    `circuitUnitary (swapGate a b)` unfolds to the product
    `E(CNOT a b) · E(CNOT b a) · E(CNOT a b)` of three `embedGate2 _ cnot`
    factors. The middle factor is on the role-swapped pair `(b, a)`, which by
    `embedGate2_swap_pair` equals `embedGate2 a b (swap₄ · cnot · swap₄)`;
    `embedGate2_mul` then collapses the same-pair product to
    `embedGate2 a b (cnot · (swap₄·cnot·swap₄) · cnot)`, whose 4×4 factor is the
    textbook SWAP identity `cnot_swap_identity`. Finally `embedGate2 a b swap₄`
    is the basis permutation `qubitPermUnitary (swapBitPerm a b)` by
    `embedGate2_swap_eq_perm`. -/
theorem swapGate_circuitUnitary (a b : Fin n) :
    circuitUnitary (swapGate a b) = qubitPermUnitary (swapBitPerm a b) := by
  apply Subtype.ext
  by_cases hab : a = b
  · -- degenerate: swapGate a a is three identity CNOTs; both sides are `1`.
    subst hab
    show (circuitUnitary (swapGate a a)).val = (qubitPermUnitary (swapBitPerm a a)).val
    rw [show swapBitPerm a a = 1 from by unfold swapBitPerm; rw [Equiv.swap_self]; rfl,
      qubitPermUnitary_one, UnitaryGroup.one_val]
    show (circuitUnitary (swapGate a a)).val = 1
    simp only [swapGate, circuitUnitary, Circuit.single,
      gateEmbedding_unitaryGroup, gateEmbedding, dite_eq_left trivial, UnitaryGroup.mul_val,
      mul_one, one_mul]
  · -- a ≠ b: the 3-CNOT computation.
    show (circuitUnitary (swapGate a b)).val = (qubitPermUnitary (swapBitPerm a b)).val
    have hcnot : gateEmbedding (Gate.CNOT a b) = embedGate2 n a b Programs.Qubit.cnot hab := by
      simp only [gateEmbedding, dite_eq_right hab]
    have hcnot' : gateEmbedding (Gate.CNOT b a) =
        embedGate2 n b a Programs.Qubit.cnot (Ne.symm hab) := by
      simp only [gateEmbedding, dite_eq_right (Ne.symm hab)]
    simp only [swapGate, circuitUnitary, Circuit.single, gateEmbedding_unitaryGroup,
      UnitaryGroup.mul_val, one_mul]
    rw [hcnot, hcnot', embedGate2_swap_pair hab Programs.Qubit.cnot]
    rw [embedGate2_mul, embedGate2_mul, cnot_swap_identity, embedGate2_swap_eq_perm hab]

/-! ## The routing-fix corollary -/

/-- **Routing identity.** With `S := circuitUnitary (swapGate a b)` self-inverse,
    conjugating the embedding of the *relabelled* two-qubit gate by `S` recovers
    the embedding of the original gate. This is exactly what the corrected
    `routeGate` (emitting `swapGate i mid ; g.relabel i mid ; swapGate i mid`)
    needs: the block realizes `U_g`. -/
theorem swapConj_relabel (g : Gate n) (a b : Fin n)
    (hg : (∃ i j, g = Gate.CNOT i j) ∨ (∃ i j, g = Gate.CZ i j)) :
    (circuitUnitary (swapGate a b)).val * gateEmbedding (g.relabel a b) *
        (circuitUnitary (swapGate a b)).val = gateEmbedding g := by
  rw [swapGate_circuitUnitary, gateEmbedding_relabel_two g a b hg]
  -- S = P, P self-inverse: P (P U P⁻¹) P = U.
  have hPinv : (qubitPermUnitary (swapBitPerm a b)⁻¹).val =
      (qubitPermUnitary (swapBitPerm a b)).val := by
    rw [Equiv.Perm.inv_def, swapBitPerm_symm]
  have hPP : (qubitPermUnitary (swapBitPerm a b)).val *
      (qubitPermUnitary (swapBitPerm a b)).val = 1 := by
    rw [← UnitaryGroup.mul_val, ← qubitPermUnitary_mul]
    rw [show swapBitPerm a b * swapBitPerm a b = 1 from by
      unfold swapBitPerm; exact Equiv.swap_mul_self _ _]
    rw [qubitPermUnitary_one, UnitaryGroup.one_val]
  calc (qubitPermUnitary (swapBitPerm a b)).val *
          ((qubitPermUnitary (swapBitPerm a b)).val * gateEmbedding g *
            (qubitPermUnitary (swapBitPerm a b)⁻¹).val) *
          (qubitPermUnitary (swapBitPerm a b)).val
      = ((qubitPermUnitary (swapBitPerm a b)).val *
            (qubitPermUnitary (swapBitPerm a b)).val) * gateEmbedding g *
          ((qubitPermUnitary (swapBitPerm a b)⁻¹).val *
            (qubitPermUnitary (swapBitPerm a b)).val) := by
            rw [hPinv]; noncomm_ring
    _ = gateEmbedding g := by rw [hPinv, hPP, one_mul, mul_one]

/-! ## Routing preserves the unitary semantics

With the braiding identity in hand, the corrected `routeGate` — which wraps a
non-adjacent two-qubit gate `g` on `(i, j)` as
`swapGate i mid ; g.relabel i mid ; swapGate i mid` — realizes exactly `U_g`.
Hence `insertSwaps` preserves the whole circuit's unitary and its
`unitaryDenote`, making the hardware-routing pass `UnitaryCorrectQ`. -/

/-- A two-qubit gate is `CNOT`/`CZ`: if `twoQubitPair g = some (i, j)` then `g`
    is `Gate.CNOT i j` or `Gate.CZ i j` on exactly those qubits. -/
theorem twoQubitPair_eq_some {g : Gate n} {i j : Fin n}
    (h : twoQubitPair g = some (i, j)) :
    g = Gate.CNOT i j ∨ g = Gate.CZ i j := by
  cases g <;>
    simp only [twoQubitPair, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    first
      | exact absurd h not_false
      | (obtain ⟨rfl, rfl⟩ := h; exact Or.inl rfl)
      | (obtain ⟨rfl, rfl⟩ := h; exact Or.inr rfl)

/-- **`routeGate` preserves each gate's unitary.** A single-qubit or already
    adjacent gate is emitted unchanged; a non-adjacent two-qubit gate is wrapped
    as `swapGate i mid ; g.relabel i mid ; swapGate i mid`, whose unitary is
    `S · U_{g.relabel} · S = U_g` by `swapConj_relabel`. -/
theorem routeGate_circuitUnitary (cg : CouplingGraph n) (g : Gate n) :
    circuitUnitary (routeGate cg g) = gateEmbedding_unitaryGroup g := by
  unfold routeGate
  cases h : twoQubitPair g with
  | none => simp only [circuitUnitary, Circuit.single, one_mul]
  | some p =>
    obtain ⟨i, j⟩ := p
    simp only []
    by_cases hadj : cg i j = true
    · rw [ite_eq_left hadj]; simp only [circuitUnitary, Circuit.single, one_mul]
    · rw [ite_eq_right hadj]
      apply Subtype.ext
      -- The block unitary is `S * gateEmbedding (g.relabel i mid) * S`.
      simp only [circuitUnitary, Circuit.single, UnitaryGroup.mul_val, one_mul]
      exact swapConj_relabel g i (findCloserNeighbor cg i j)
        ((twoQubitPair_eq_some h).imp (fun he => ⟨i, j, he⟩) (fun he => ⟨i, j, he⟩))

/-- **`insertSwaps` preserves the whole circuit's unitary.** Each routed gate
    preserves its unitary (`routeGate_circuitUnitary`), so the run-ordered
    product is unchanged. -/
theorem insertSwaps_circuitUnitary (c : Circuit n) (cg : CouplingGraph n) :
    circuitUnitary (insertSwaps c cg) = circuitUnitary c := by
  induction c with
  | empty => rfl
  | gate g c' ih =>
    show circuitUnitary (Circuit.seq (routeGate cg g) (insertSwaps c' cg)) = _
    simp only [circuitUnitary, ih, routeGate_circuitUnitary]
  | seq c₁ c₂ ih₁ ih₂ =>
    show circuitUnitary (Circuit.seq (insertSwaps c₁ cg) (insertSwaps c₂ cg)) = _
    simp only [circuitUnitary, ih₁, ih₂]

/-- **`insertSwaps` preserves `unitaryDenote`.** The routing pass is
    semantics-preserving under the unitary-channel denotation. -/
theorem insertSwaps_unitaryDenote (c : Circuit n) (cg : CouplingGraph n) :
    unitaryDenote (insertSwaps c cg) = unitaryDenote c := by
  rw [unitaryDenote_eq_channel, unitaryDenote_eq_channel, insertSwaps_circuitUnitary]

/-- **Hardware routing is unitary-correct.** `insertSwaps · cg` preserves the
    unitary semantics for every coupling graph `cg`. -/
theorem insertSwaps_unitaryCorrect (cg : CouplingGraph n) :
    UnitaryCorrectQ (insertSwaps · cg : Circuit n → Circuit n) := by
  intro c; exact (insertSwaps_unitaryDenote c cg).symm

end CatCrypt.Quantum.Optimization.SwapConj
