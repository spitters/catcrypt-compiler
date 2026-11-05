/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Quantum.QCircuit
public import CatCrypt.Quantum.UnitaryChannel
public import CatCrypt.Crypto.UCMonad.QuantumUC
public import CatCrypt.Tactic.NormSqrt


@[expose] public section
set_option autoImplicit false

/-!
# Gate Unitarity and Nontrivial Circuit Denotation

Proves that every gate in the Clifford+T gate set is unitary, and that
`embedGate1`/`embedGate2` preserve unitarity. Unitarity supports the gate
denotation `denoteGateU := unitaryChannel ∘ gateEmbedding` and the circuit
denotation `unitaryDenote` built on it.

## Strategy (Approach A — Algebraic)

Three algebraic properties of `embedGate1`:

1. `embedGate1_conjTranspose`: `(embedGate1 n i G)ᴴ = embedGate1 n i Gᴴ`
2. `embedGate1_mul`:  `embedGate1 n i G * embedGate1 n i H = embedGate1 n i (G * H)`
3. `embedGate1_one`:  `embedGate1 n i 1 = 1`

Unitarity follows: `embedGate1 G * (embedGate1 G)ᴴ = embedGate1 (G * Gᴴ) = embedGate1 1 = 1`

## Main results

* `embedGate1_unitary` — the embedding of a unitary one-qubit gate into `n` qubits is unitary.
* `embedGate2_unitary` — the embedding of a unitary two-qubit gate on distinct qubits is
  unitary.
* `gateEmbedding_unitaryGroup` — the embedding matrix of a gate as an element of the unitary
  group.
* `denoteGateU`, `unitaryDenote` — the unitary-channel denotation of a gate and of a circuit.
* `UnitaryCorrectQ` — a circuit pass preserves `unitaryDenote`; `unitaryCorrectQ_comp`
  states that such passes compose.
* `unitaryDenote_seq` — the denotation of a sequential composition is the bind of the
  denotations of its parts.
* `templateHH_correct`, `templateHXH_correct`, `templateHZH_correct` — the cancellation
  `H; H = empty` and the Hadamard conjugations `H; X; H = Z` and `H; Z; H = X` under
  `unitaryDenote`.
-/

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum
open CatCrypt.Quantum.QCircuit CatCrypt.Quantum.UnitaryChannel

noncomputable section

namespace CatCrypt.Quantum.GateUnitarity

variable {n : ℕ}

/-! The `√2` identities of the matrix proofs below (`ofReal_sqrt2_sq`, `ofReal_sqrt2_inv_sq`)
are in `CatCrypt.Tactic.NormSqrt`. -/

/-! ## embedGate1 Algebraic Properties -/

/-- Conjugate transpose commutes with `embedGate1`. -/
@[grind =]
theorem embedGate1_conjTranspose (n : ℕ) (i : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ) :
    (embedGate1 n i G)ᴴ = embedGate1 n i Gᴴ := by
  ext r c
  simp only [conjTranspose_apply, embedGate1, Matrix.of_apply]
  set ns := n - 1 - i.val
  by_cases h : c.val / 2 ^ (ns + 1) = r.val / 2 ^ (ns + 1) ∧
               c.val % 2 ^ ns = r.val % 2 ^ ns
  · rw [ite_eq_left h, ite_eq_left ⟨h.1.symm, h.2.symm⟩]
  · rw [ite_eq_right h, star_zero,
        ite_eq_right (fun ⟨h1, h2⟩ => h ⟨h1.symm, h2.symm⟩)]

/-- `embedGate1` of the identity matrix is the identity.

    Proof: when `r = c`, all components match so `I(r_gate, r_gate) = 1`.
    When `r ≠ c`, either left/right differ (→ 0) or gate bits differ (→ 0). -/
private theorem val_decomp_unique (ns a b : ℕ)
    (h_left : a / 2 ^ (ns + 1) = b / 2 ^ (ns + 1))
    (h_right : a % 2 ^ ns = b % 2 ^ ns)
    (h_gate : (a / 2 ^ ns) % 2 = (b / 2 ^ ns) % 2) :
    a = b := by
  -- Set P = 2^ns. Then a = P * (a/P) + a%P and a/P = 2*(a/P/2) + (a/P)%2
  set P := 2 ^ ns with hP
  have hPpos : 0 < P := Nat.pos_of_ne_zero (by positivity)
  -- a/P has the same quotient and remainder mod 2 as b/P
  have : a / P = b / P := by
    have ha := Nat.div_add_mod (a / P) 2
    have hb := Nat.div_add_mod (b / P) 2
    -- a/P/2 = a/(P*2) = a/2^(ns+1), same for b
    have haP : a / P / 2 = a / 2 ^ (ns + 1) := by
      rw [hP, show 2 ^ (ns + 1) = 2 ^ ns * 2 from by ring]
      exact Nat.div_div_eq_div_mul a (2 ^ ns) 2
    have hbP : b / P / 2 = b / 2 ^ (ns + 1) := by
      rw [hP, show 2 ^ (ns + 1) = 2 ^ ns * 2 from by ring]
      exact Nat.div_div_eq_div_mul b (2 ^ ns) 2
    omega
  -- Now a = P * (a/P) + a%P = P * (b/P) + b%P = b
  calc a = P * (a / P) + a % P := (Nat.div_add_mod a P).symm
    _ = P * (b / P) + b % P := by rw [this, h_right]
    _ = b := Nat.div_add_mod b P

@[grind =]
theorem embedGate1_one (n : ℕ) (i : Fin n) :
    embedGate1 n i (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext r c
  simp only [embedGate1, Matrix.of_apply, Matrix.one_apply]
  set ns := n - 1 - i.val
  by_cases hrc : r = c
  · subst hrc; simp
  · have hne : r.val ≠ c.val := Fin.val_ne_of_ne hrc
    rw [ite_eq_right hrc]
    -- After simp, the embedGate1 part may have multiple if-branches
    -- All should give 0 since r ≠ c
    split_ifs with h1 h2
    · -- left/right match AND gate bits match → r = c contradiction
      exfalso; apply hne
      exact val_decomp_unique ns r.val c.val h1.1 h1.2 (by
        simp only [Fin.ext_iff] at h2; exact h2)
    · rfl
    · rfl

/-- `embedGate1` is multiplicative: the sum over `k : Fin (2^n)` collapses
    to a sum over the gate bit because left/right components are fixed.

    Proof strategy: In the positive case, every summand with mismatching
    left/right is 0 (since one factor vanishes). The surviving terms are
    parametrized by `k_gate ∈ Fin 2` and contribute `G(rg,kg) * H(kg,cg)`.
    The negative case is handled by showing every summand is 0. -/
@[grind =]
theorem embedGate1_mul (n : ℕ) (i : Fin n) (G H : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 n i G * embedGate1 n i H = embedGate1 n i (G * H) := by
  ext r c
  simp only [embedGate1, Matrix.mul_apply, Matrix.of_apply]
  set ns := n - 1 - i.val with hns
  by_cases hrc : r.val / 2 ^ (ns + 1) = c.val / 2 ^ (ns + 1) ∧
                 r.val % 2 ^ ns = c.val % 2 ^ ns
  · -- Positive case: sum reduces to (G * H)(r_gate, c_gate)
    rw [ite_eq_left hrc]
    -- Each summand simplifies: when both conditions hold, product is
    -- G(rg, kg) * H(kg, cg); otherwise 0.
    have hsimpl : ∀ k : Fin (2 ^ n),
        (if r.val / 2 ^ (ns + 1) = k.val / 2 ^ (ns + 1) ∧ r.val % 2 ^ ns = k.val % 2 ^ ns
         then G ⟨(r.val / 2 ^ ns) % 2, by omega⟩ ⟨(k.val / 2 ^ ns) % 2, by omega⟩ else 0) *
        (if k.val / 2 ^ (ns + 1) = c.val / 2 ^ (ns + 1) ∧ k.val % 2 ^ ns = c.val % 2 ^ ns
         then H ⟨(k.val / 2 ^ ns) % 2, by omega⟩ ⟨(c.val / 2 ^ ns) % 2, by omega⟩ else 0) =
        if r.val / 2 ^ (ns + 1) = k.val / 2 ^ (ns + 1) ∧ r.val % 2 ^ ns = k.val % 2 ^ ns
        then G ⟨(r.val / 2 ^ ns) % 2, by omega⟩ ⟨(k.val / 2 ^ ns) % 2, by omega⟩ *
             H ⟨(k.val / 2 ^ ns) % 2, by omega⟩ ⟨(c.val / 2 ^ ns) % 2, by omega⟩
        else 0 := by
      intro k
      split_ifs with h1 h2
      · rfl
      · exfalso; exact h2 ⟨h1.1.symm ▸ hrc.1, h1.2.symm ▸ hrc.2⟩
      · simp [mul_zero]
      · simp [zero_mul]
    -- Rewrite each summand using hsimpl
    have : (∑ k : Fin (2 ^ n),
        (if r.val / 2 ^ (ns + 1) = k.val / 2 ^ (ns + 1) ∧ r.val % 2 ^ ns = k.val % 2 ^ ns
         then G ⟨(r.val / 2 ^ ns) % 2, by omega⟩ ⟨(k.val / 2 ^ ns) % 2, by omega⟩ else 0) *
        (if k.val / 2 ^ (ns + 1) = c.val / 2 ^ (ns + 1) ∧ k.val % 2 ^ ns = c.val % 2 ^ ns
         then H ⟨(k.val / 2 ^ ns) % 2, by omega⟩ ⟨(c.val / 2 ^ ns) % 2, by omega⟩ else 0)) =
      ∑ k : Fin (2 ^ n),
        (if r.val / 2 ^ (ns + 1) = k.val / 2 ^ (ns + 1) ∧ r.val % 2 ^ ns = k.val % 2 ^ ns
        then G ⟨(r.val / 2 ^ ns) % 2, by omega⟩ ⟨(k.val / 2 ^ ns) % 2, by omega⟩ *
             H ⟨(k.val / 2 ^ ns) % 2, by omega⟩ ⟨(c.val / 2 ^ ns) % 2, by omega⟩
        else 0) :=
      Finset.sum_congr rfl (fun k _ => hsimpl k)
    rw [this]; clear this hsimpl
    -- Goal: ∑_k (if matching(k) then f(k_gate) else 0) = (G*H)(rg,cg)
    change _ = ∑ b : Fin 2,
      G ⟨(r.val / 2 ^ ns) % 2, by omega⟩ b *
      H b ⟨(c.val / 2 ^ ns) % 2, by omega⟩
    -- Both sides are sums. The LHS filters over Fin (2^n); the RHS sums over Fin 2.
    -- They're equal because each matching k ↔ a unique b : Fin 2 (the gate bit).
    have hPpos : 0 < 2 ^ ns := Nat.pos_of_ne_zero (by positivity)
    have hi := i.isLt  -- i.val < n
    have hns1 : ns + 1 ≤ n := by omega
    -- Abbreviations for r's components
    set rl := r.val / 2 ^ (ns + 1)
    set rr := r.val % 2 ^ ns
    have hrr : rr < 2 ^ ns := Nat.mod_lt _ hPpos
    -- Use sum_bij_ne_zero: map k to its gate bit ⟨(k/2^ns)%2⟩
    apply Finset.sum_bij_ne_zero
      (fun k _ _ => (⟨(k.val / 2 ^ ns) % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2))
    · -- hi: gate bit ∈ Finset.univ
      intros; exact Finset.mem_univ _
    · -- injectivity (on the non-zero terms)
      intro k₁ _ hne₁ k₂ _ hne₂ heq
      -- Non-zero means the if-condition holds
      have hk₁ : rl = k₁.val / 2 ^ (ns + 1) ∧ rr = k₁.val % 2 ^ ns := by
        by_contra h; exact hne₁ (ite_eq_right h)
      have hk₂ : rl = k₂.val / 2 ^ (ns + 1) ∧ rr = k₂.val % 2 ^ ns := by
        by_contra h; exact hne₂ (ite_eq_right h)
      apply Fin.ext
      apply val_decomp_unique ns k₁.val k₂.val
      · exact hk₁.1.symm.trans hk₂.1
      · exact hk₁.2.symm.trans hk₂.2
      · exact congr_arg Fin.val heq
    · -- surjectivity: every b : Fin 2 with g(b) ≠ 0 is hit
      intro b _ hne
      -- Reconstruct k from r's left/right and b as gate bit
      have hb := b.isLt
      -- Bound: (rl * 2 + b) * 2^ns + rr < 2^n
      have hrl_le : rl * 2 ^ (ns + 1) ≤ r.val :=
        Nat.div_mul_le_self r.val (2 ^ (ns + 1))
      have hbound : (rl * 2 + b.val) * 2 ^ ns + rr < 2 ^ n := by
        have h2 : 2 ^ (ns + 1) = 2 * 2 ^ ns := by ring
        -- rl * 2^(ns+1) + b * 2^ns + rr < rl*2^(ns+1) + 2*2^ns = (rl+1)*2^(ns+1)
        -- and (rl+1)*2^(ns+1) ≤ 2^n since rl*2^(ns+1) ≤ r.val < 2^n
        -- More precisely: r.val = rl * 2^(ns+1) + r.val % 2^(ns+1) < (rl+1)*2^(ns+1)
        -- and rl * 2^(ns+1) ≤ r.val < 2^n, so rl ≤ (2^n - 1) / 2^(ns+1)
        -- Need: (rl*2+b)*2^ns+rr = rl*2^(ns+1)+b*2^ns+rr < (rl+1)*2^(ns+1) ≤ 2^n
        -- Since b*2^ns+rr < 2*2^ns = 2^(ns+1), we get the first inequality.
        -- For the second: (rl+1)*2^(ns+1) ≤ 2^n follows from rl < 2^(n-ns-1).
        suffices h : (rl + 1) * 2 ^ (ns + 1) ≤ 2 ^ n by nlinarith
        have : rl < 2 ^ (n - (ns + 1)) :=
          Nat.div_lt_of_lt_mul (show r.val < 2 ^ (ns + 1) * 2 ^ (n - (ns + 1)) by
            rw [← pow_add, show ns + 1 + (n - (ns + 1)) = n from by omega]; exact r.isLt)
        calc (rl + 1) * 2 ^ (ns + 1)
            ≤ 2 ^ (n - (ns + 1)) * 2 ^ (ns + 1) := Nat.mul_le_mul_right _ (by omega)
          _ = 2 ^ n := by rw [← pow_add, show n - (ns + 1) + (ns + 1) = n from by omega]
      let k : Fin (2 ^ n) := ⟨(rl * 2 + b.val) * 2 ^ ns + rr, hbound⟩
      -- Show the if-condition holds for k
      have h2ns : 2 ^ (ns + 1) = 2 * 2 ^ ns := by ring
      have hk_left : k.val / 2 ^ (ns + 1) = rl := by
        show ((rl * 2 + b.val) * 2 ^ ns + rr) / 2 ^ (ns + 1) = rl
        rw [h2ns]
        rw [show (rl * 2 + b.val) * 2 ^ ns + rr
              = 2 * 2 ^ ns * rl + (b.val * 2 ^ ns + rr) from by ring]
        rw [Nat.mul_add_div (by positivity : 0 < 2 * 2 ^ ns)]
        have : b.val * 2 ^ ns + rr < 2 * 2 ^ ns := by nlinarith
        rw [Nat.div_eq_of_lt this]; omega
      have hk_right : k.val % 2 ^ ns = rr := by
        show ((rl * 2 + b.val) * 2 ^ ns + rr) % 2 ^ ns = rr
        rw [show (rl * 2 + b.val) * 2 ^ ns = 2 ^ ns * (rl * 2 + b.val) from by ring]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrr]
      have hk_gate : (k.val / 2 ^ ns) % 2 = b.val := by
        show (((rl * 2 + b.val) * 2 ^ ns + rr) / 2 ^ ns) % 2 = b.val
        rw [show (rl * 2 + b.val) * 2 ^ ns = 2 ^ ns * (rl * 2 + b.val) from by ring]
        rw [show 2 ^ ns * (rl * 2 + b.val) + rr = 2 ^ ns * (rl * 2 + b.val) + rr from rfl]
        rw [Nat.mul_add_div hPpos, Nat.div_eq_of_lt hrr, add_zero]
        omega
      -- The if-condition is satisfied
      have hk_cond : rl = k.val / 2 ^ (ns + 1) ∧ rr = k.val % 2 ^ ns :=
        ⟨hk_left.symm, hk_right.symm⟩
      refine ⟨k, Finset.mem_univ _, ?_, ?_⟩
      · -- f(k) ≠ 0: the if-condition holds, so the term equals something (same as g(b))
        rw [ite_eq_left hk_cond]
        have hb_eq : (⟨(k.val / 2 ^ ns) % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2) = b :=
          Fin.ext hk_gate
        rw [hb_eq]
        exact hne
      · -- gate bit of k = b
        exact Fin.ext hk_gate
    · -- values match
      intro k _ hne
      -- f(k) ≠ 0 implies the condition holds
      have hk : rl = k.val / 2 ^ (ns + 1) ∧ rr = k.val % 2 ^ ns := by
        by_contra h
        exact hne (ite_eq_right h)
      rw [ite_eq_left hk]
  · -- Negative case: every term is zero
    rw [ite_eq_right hrc]
    apply Finset.sum_eq_zero; intro k _
    by_cases h1 : r.val / 2 ^ (ns + 1) = k.val / 2 ^ (ns + 1) ∧
                  r.val % 2 ^ ns = k.val % 2 ^ ns
    · rw [ite_eq_left h1]
      have h2 : ¬(k.val / 2 ^ (ns + 1) = c.val / 2 ^ (ns + 1) ∧
                   k.val % 2 ^ ns = c.val % 2 ^ ns) :=
        fun ⟨hk1, hk2⟩ => hrc ⟨h1.1.trans hk1, h1.2.trans hk2⟩
      rw [ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]

/-- `embedGate1` commutes with scalars in the gate matrix. -/
theorem embedGate1_smul (n : ℕ) (i : Fin n) (c : ℂ)
    (G : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 n i (c • G) = c • embedGate1 n i G := by
  ext r s
  simp only [embedGate1, Matrix.of_apply, Matrix.smul_apply]
  split_ifs <;> simp

/-- `embedGate1` sends the zero gate matrix to the zero matrix. -/
theorem embedGate1_map_zero (i : Fin n) :
    embedGate1 n i (0 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := by
  ext r c
  simp only [embedGate1, Matrix.of_apply, Matrix.zero_apply, ite_self]

/-- `embedGate1` is additive in the gate matrix. -/
theorem embedGate1_map_add (i : Fin n) (G H : Matrix (Fin 2) (Fin 2) ℂ) :
    embedGate1 n i (G + H) = embedGate1 n i G + embedGate1 n i H := by
  ext r c
  simp only [embedGate1, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

/-- Unitarity of `embedGate1`: if `G` is unitary, so is `embedGate1 n i G`. -/
theorem embedGate1_unitary (n : ℕ) (i : Fin n) (G : Matrix (Fin 2) (Fin 2) ℂ)
    (hG : G * Gᴴ = 1) :
    embedGate1 n i G * (embedGate1 n i G)ᴴ = 1 := by
  grind

/-! ## embedGate2 Algebraic Properties

Same structure as embedGate1 but with 2-bit extraction for 2-qubit gates. -/

@[grind =]
theorem embedGate2_conjTranspose (n : ℕ) (i j : Fin n) (G : Matrix (Fin 4) (Fin 4) ℂ)
    (hij : i ≠ j) :
    (embedGate2 n i j G hij)ᴴ = embedGate2 n i j Gᴴ hij := by
  ext r c; simp only [conjTranspose_apply, embedGate2, Matrix.of_apply]
  split_ifs <;> simp_all [star_zero]

private theorem bits_determine_val (n : ℕ) (a b : Fin (2 ^ n))
    (h : ∀ k : Fin n, (a.val / 2 ^ (n - 1 - k.val)) % 2 =
                       (b.val / 2 ^ (n - 1 - k.val)) % 2) :
    a = b := by
  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro m
  by_cases hm : m < n
  · have hk := h ⟨n - 1 - m, by omega⟩; simp only at hk
    rw [show n - 1 - (n - 1 - m) = m from by omega] at hk
    simp only [Nat.testBit_eq_decide_div_mod_eq]
    rw [decide_eq_decide]; constructor <;> (intro; omega)
  · have ha : a.val < 2 ^ m := lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by omega) (by omega))
    have hb : b.val < 2 ^ m := lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by omega) (by omega))
    simp [Nat.testBit_lt_two_pow ha, Nat.testBit_lt_two_pow hb]

@[grind =]
theorem embedGate2_one (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    embedGate2 n i j (1 : Matrix (Fin 4) (Fin 4) ℂ) hij = 1 := by
  ext r c; simp only [embedGate2, Matrix.of_apply, Matrix.one_apply]
  -- 3 nested ifs yield 6 branches: obm(r,c), r_2q=c_2q, r=c
  split_ifs with hobm hq hrc
  · rfl
  · exfalso; apply hrc; apply bits_determine_val n r c; intro k
    have hval := congrArg Fin.val hq; simp only [Fin.val_mk] at hval
    by_cases hki : (k : Fin n) = i
    · subst hki
      have := Nat.mod_lt (r.val / 2 ^ (n - 1 - k.val)) (show 0 < 2 by omega)
      have := Nat.mod_lt (c.val / 2 ^ (n - 1 - k.val)) (show 0 < 2 by omega)
      omega
    · by_cases hkj : k = j
      · subst hkj
        have := Nat.mod_lt (r.val / 2 ^ (n - 1 - k.val)) (show 0 < 2 by omega)
        have := Nat.mod_lt (c.val / 2 ^ (n - 1 - k.val)) (show 0 < 2 by omega)
        omega
      · exact congrArg Fin.val (hobm k hki hkj)
  · exfalso; rename_i heq; subst heq; exact hq rfl
  · rfl
  · exfalso; rename_i heq; subst heq; exact hobm (fun _ _ _ => rfl)
  · rfl

/-! ### XOR bit-mask helpers for embedGate2_mul surjectivity -/

/-- XOR with a single-bit mask `x * 2^p` (where `x < 2`) does not change
    the bit at position `q ≠ p`. -/
private theorem xor_mask_div_mod_ne (v x p q : ℕ) (hx : x < 2) (hpq : p ≠ q) :
    (v ^^^ x * 2 ^ p) / 2 ^ q % 2 = v / 2 ^ q % 2 := by
  -- Suffices to show testBit equality, then convert
  suffices h : (v ^^^ x * 2 ^ p).testBit q = v.testBit q by
    simp only [Nat.testBit_eq_decide_div_mod_eq] at h
    have h1 := Nat.mod_two_eq_zero_or_one ((v ^^^ x * 2 ^ p) / 2 ^ q)
    have h2 := Nat.mod_two_eq_zero_or_one (v / 2 ^ q)
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp_all
  rw [Nat.testBit_xor, Nat.testBit_mul_two_pow]
  by_cases hle : p ≤ q
  · simp only [hle, decide_true, Bool.true_and]
    have hqp : q - p ≥ 1 := by omega
    have : x < 2 ^ (q - p) := by
      calc x < 2 := hx
        _ = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (q - p) := Nat.pow_le_pow_right (by omega) hqp
    rw [Nat.testBit_lt_two_pow this]; simp
  · simp [hle]

/-- XOR with a single-bit mask `x * 2^p` (where `x < 2`) XORs the bit at position `p`:
    `(v ^^^ x * 2^p) / 2^p % 2 = (v / 2^p % 2) ^^^ x`. -/
private theorem xor_mask_div_mod_eq (v x p : ℕ) (hx : x < 2) :
    (v ^^^ x * 2 ^ p) / 2 ^ p % 2 = (v / 2 ^ p % 2) ^^^ x := by
  -- Work via testBit
  have htb : (v ^^^ x * 2 ^ p).testBit p = (v.testBit p ^^ x.testBit 0) := by
    rw [Nat.testBit_xor, Nat.testBit_mul_two_pow]
    simp [Nat.le_refl]
  -- Convert testBit to div/mod
  simp only [Nat.testBit_eq_decide_div_mod_eq] at htb
  have hvmod := Nat.mod_two_eq_zero_or_one (v / 2 ^ p)
  have hkmod := Nat.mod_two_eq_zero_or_one ((v ^^^ x * 2 ^ p) / 2 ^ p)
  -- x < 2, so x is 0 or 1
  interval_cases x <;> rcases hvmod with hv | hv <;> rcases hkmod with hk | hk <;>
    simp_all [Nat.zero_xor, Nat.xor_zero, Nat.testBit]

/-- `embedGate2` is multiplicative: `embedGate2 G * embedGate2 H = embedGate2 (G * H)`.

    The proof requires the same `Finset.sum_bij_ne_zero` machinery as `embedGate1_mul`
    (lines 108-250): non-zero summands biject with `Fin 4` via the 2-bit gate index
    at positions `i` and `j`. The positive case reconstructs `k` from `r`'s non-gate
    bits and a chosen `b : Fin 4`, while the negative case shows every summand is zero
    because `obm(r,k) ∧ obm(k,c)` would imply `obm(r,c)` by transitivity. -/
@[grind =]
theorem embedGate2_mul (n : ℕ) (i j : Fin n) (G H : Matrix (Fin 4) (Fin 4) ℂ)
    (hij : i ≠ j) :
    embedGate2 n i j G hij * embedGate2 n i j H hij = embedGate2 n i j (G * H) hij := by
  ext r c
  simp only [embedGate2, Matrix.mul_apply, Matrix.of_apply]
  -- Abbreviations for bit extraction
  set bit := fun (v : ℕ) (k : Fin n) =>
    (⟨(v / (2 ^ (n - 1 - k.val))) % 2, Nat.mod_lt _ (by omega)⟩ : Fin 2) with hbit
  set obm := fun (a b : Fin (2 ^ n)) =>
    ∀ k : Fin n, k ≠ i → k ≠ j → bit a.val k = bit b.val k with hobm_def
  set idx := fun (v : ℕ) =>
    (⟨(bit v i).val * 2 + (bit v j).val, by omega⟩ : Fin 4) with hidx
  -- Negative case: if ¬obm(r,c), every summand is 0
  by_cases hrc : obm r c
  · -- Positive case: obm(r,c) holds
    -- Each nonzero summand requires obm(r,k), so k must agree with r on non-gate bits.
    -- The surviving terms are parametrized by the 2-qubit gate index b : Fin 4.
    rw [ite_eq_left hrc]
    -- Goal: ∑_k ... = (G * H)(idx r, idx c) = ∑_b G(idx r, b) * H(b, idx c)
    change _ = ∑ b : Fin 4, G (idx r.val) b * H b (idx c.val)
    -- For each k with obm(r,k) and obm(k,c): the product contributes
    -- G(idx r, idx k) * H(idx k, idx c); otherwise 0.
    have hsimpl : ∀ k : Fin (2 ^ n),
        (if obm r k then G (idx r.val) (idx k.val) else 0) *
        (if obm k c then H (idx k.val) (idx c.val) else 0) =
        if obm r k then G (idx r.val) (idx k.val) * H (idx k.val) (idx c.val)
        else 0 := by
      intro k
      split_ifs with h1 h2
      · rfl
      · exfalso; exact h2 (fun l hl1 hl2 => by
          rw [← hrc l hl1 hl2, ← h1 l hl1 hl2])
      · simp [mul_zero]
      · simp [zero_mul]
    have : (∑ k : Fin (2 ^ n),
        (if obm r k then G (idx r.val) (idx k.val) else 0) *
        (if obm k c then H (idx k.val) (idx c.val) else 0)) =
      ∑ k : Fin (2 ^ n),
        (if obm r k then G (idx r.val) (idx k.val) * H (idx k.val) (idx c.val)
        else 0) :=
      Finset.sum_congr rfl (fun k _ => hsimpl k)
    rw [this]; clear this hsimpl
    -- Now reindex: ∑_k (if obm(r,k) then f(idx k) else 0) = ∑_b f(b)
    -- via the bijection k ↦ idx(k) restricted to the obm(r,·) fiber.
    apply Finset.sum_bij_ne_zero
      (fun k _ _ => idx k.val)
    · intros; exact Finset.mem_univ _
    · -- Injectivity on non-zero terms
      intro k₁ _ hne₁ k₂ _ hne₂ heq
      have hk₁ : obm r k₁ := by by_contra h; exact hne₁ (ite_eq_right h)
      have hk₂ : obm r k₂ := by by_contra h; exact hne₂ (ite_eq_right h)
      apply bits_determine_val n k₁ k₂
      intro l
      by_cases hli : l = i
      · subst hli; have h := congrArg Fin.val heq; simp [idx, bit] at h; omega
      · by_cases hlj : l = j
        · subst hlj; have h := congrArg Fin.val heq; simp [idx, bit] at h; omega
        · have h1 := congrArg Fin.val (hk₁ l hli hlj)
          have h2 := congrArg Fin.val (hk₂ l hli hlj)
          simp only [bit, Fin.val_mk] at h1 h2
          omega
    · -- Surjectivity: given b : Fin 4, construct k with obm(r,k) and idx(k) = b
      intro b _ hne
      have hb := b.isLt
      -- Desired bits at positions i and j
      set bi : Fin 2 := ⟨b.val / 2, by omega⟩ with hbi_def
      set bj : Fin 2 := ⟨b.val % 2, by omega⟩ with hbj_def
      -- Construct k by modifying r's bits at positions i and j
      -- k = r XOR ((ri XOR bi) << pos_i) XOR ((rj XOR bj) << pos_j)
      -- where pos_k = n - 1 - k.val
      -- Use Nat.bitFlip: flip bit at given position
      set pi := n - 1 - i.val with hpi
      set pj := n - 1 - j.val with hpj
      set ri := (r.val / 2 ^ pi) % 2 with hri
      set rj := (r.val / 2 ^ pj) % 2 with hrj
      -- Construct the new value by flipping needed bits
      set kval := (r.val ^^^ ((ri ^^^ bi.val) * 2 ^ pi) ^^^ ((rj ^^^ bj.val) * 2 ^ pj))
      -- Prove each XOR mask term < 2^n
      have hxor_i_lt : ri ^^^ bi.val < 2 := Nat.xor_lt_two_pow
        (show ri < 2 ^ 1 by have := Nat.mod_lt (r.val / 2 ^ pi) (show 0 < 2 by omega); omega)
        (show bi.val < 2 ^ 1 by omega)
      have hxor_j_lt : rj ^^^ bj.val < 2 := Nat.xor_lt_two_pow
        (show rj < 2 ^ 1 by have := Nat.mod_lt (r.val / 2 ^ pj) (show 0 < 2 by omega); omega)
        (show bj.val < 2 ^ 1 by omega)
      have hpi_lt : pi < n := by omega
      have hpj_lt : pj < n := by omega
      have hpi_ne_pj : pi ≠ pj := by intro h; apply hij; apply Fin.ext; omega
      have hmask_i_lt : (ri ^^^ bi.val) * 2 ^ pi < 2 ^ n := by
        calc (ri ^^^ bi.val) * 2 ^ pi
            ≤ 1 * 2 ^ pi := Nat.mul_le_mul_right _ (by omega)
          _ = 2 ^ pi := one_mul _
          _ < 2 ^ n := Nat.pow_lt_pow_right (by omega) hpi_lt
      have hmask_j_lt : (rj ^^^ bj.val) * 2 ^ pj < 2 ^ n := by
        calc (rj ^^^ bj.val) * 2 ^ pj
            ≤ 1 * 2 ^ pj := Nat.mul_le_mul_right _ (by omega)
          _ = 2 ^ pj := one_mul _
          _ < 2 ^ n := Nat.pow_lt_pow_right (by omega) hpj_lt
      have hkval_lt : kval < 2 ^ n :=
        Nat.xor_lt_two_pow (Nat.xor_lt_two_pow r.isLt hmask_i_lt) hmask_j_lt
      let k : Fin (2 ^ n) := ⟨kval, hkval_lt⟩
      -- Prove obm(r, k): bits at positions other than i,j are unchanged
      have hobm_rk : obm r k := by
        intro l hli hlj
        apply Fin.ext; simp only [bit, Fin.val_mk]
        set pl := n - 1 - l.val
        have hpl_ne_pi : pi ≠ pl := by intro h; apply hli; apply Fin.ext; omega
        have hpl_ne_pj : pj ≠ pl := by intro h; apply hlj; apply Fin.ext; omega
        show r.val / 2 ^ pl % 2 = kval / 2 ^ pl % 2
        show r.val / 2 ^ pl % 2 =
          (r.val ^^^ (ri ^^^ bi.val) * 2 ^ pi ^^^ (rj ^^^ bj.val) * 2 ^ pj) / 2 ^ pl % 2
        rw [xor_mask_div_mod_ne _ _ pj pl (by omega) hpl_ne_pj]
        rw [xor_mask_div_mod_ne _ _ pi pl (by omega) hpl_ne_pi]
      -- Prove idx(k) = b: bits at positions pi/pj are set to bi/bj
      have hk_pi : kval / 2 ^ pi % 2 = bi.val := by
        show (r.val ^^^ (ri ^^^ bi.val) * 2 ^ pi ^^^ (rj ^^^ bj.val) * 2 ^ pj) /
          2 ^ pi % 2 = bi.val
        rw [xor_mask_div_mod_ne _ _ pj pi (by omega) hpi_ne_pj.symm]
        rw [xor_mask_div_mod_eq _ _ pi (by omega)]
        show ri ^^^ (ri ^^^ bi.val) = bi.val
        rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      have hk_pj : kval / 2 ^ pj % 2 = bj.val := by
        show (r.val ^^^ (ri ^^^ bi.val) * 2 ^ pi ^^^ (rj ^^^ bj.val) * 2 ^ pj) /
          2 ^ pj % 2 = bj.val
        rw [xor_mask_div_mod_eq _ _ pj (by omega)]
        rw [xor_mask_div_mod_ne _ _ pi pj (by omega) hpi_ne_pj]
        show rj ^^^ (rj ^^^ bj.val) = bj.val
        rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
      have hidx_eq : idx k.val = b := by
        apply Fin.ext; simp only [idx, bit, Fin.val_mk]
        -- Goal: (kval / 2^pi % 2) * 2 + (kval / 2^pj % 2) = b.val
        rw [hk_pi, hk_pj]
        -- Goal: bi.val * 2 + bj.val = b.val
        simp only [hbi_def, hbj_def, Fin.val_mk]
        omega
      refine ⟨k, Finset.mem_univ _, ?_, hidx_eq⟩
      · -- Non-zero: obm holds so if-branch is taken, and the value matches hne
        rw [ite_eq_left hobm_rk]
        rw [show idx k.val = b from hidx_eq]
        exact hne
    · -- Value agreement
      intro k _ hne
      have hk : obm r k := by by_contra h; exact hne (ite_eq_right h)
      rw [ite_eq_left hk]
  · -- Negative case: ¬obm(r,c), so every product term is 0
    rw [ite_eq_right hrc]
    apply Finset.sum_eq_zero; intro k _
    -- If obm(r,k) holds, then obm(k,c) must fail (else transitivity gives obm(r,c))
    by_cases h1 : obm r k
    · rw [ite_eq_left h1]
      have h2 : ¬ obm k c := fun h2 => hrc (fun l hl1 hl2 =>
        (h1 l hl1 hl2).symm ▸ h2 l hl1 hl2)
      rw [ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]

theorem embedGate2_unitary (n : ℕ) (i j : Fin n) (G : Matrix (Fin 4) (Fin 4) ℂ)
    (hij : i ≠ j) (hG : G * Gᴴ = 1) :
    embedGate2 n i j G hij * (embedGate2 n i j G hij)ᴴ = 1 := by
  grind

/-! ## Base Gate Unitarity (2×2 and 4×4)

All gates in the Clifford+T set are unitary. Proved by entry-wise
computation using `fin_cases` and arithmetic. -/

section BaseGates

open CatCrypt.Quantum.Programs.Qubit

set_option linter.unusedSimpArgs false in
@[grind =]
theorem hadamard_sq :
    Programs.Qubit.hadamard * Programs.Qubit.hadamard = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Programs.Qubit.hadamard, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          neg_mul, mul_neg, neg_neg] <;>
    rw [ofReal_sqrt2_inv_sq] <;> ring

set_option linter.unusedSimpArgs false in
@[grind =]
theorem hadamard_unitary :
    Programs.Qubit.hadamard * Programs.Qubit.hadamardᴴ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Programs.Qubit.hadamard, Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_two,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          star_neg, star_trivial, neg_mul, mul_neg, neg_neg] <;>
    rw [ofReal_sqrt2_inv_sq] <;> ring

set_option linter.unusedSimpArgs false in
@[grind =]
theorem pauliX_unitary :
    pauliX * pauliXᴴ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_two,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

set_option linter.unusedSimpArgs false in
@[grind =]
theorem pauliY_unitary :
    pauliY * pauliYᴴ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_two,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          star_neg, star_mul', Complex.conj_I, Complex.I_mul_I]

set_option linter.unusedSimpArgs false in
@[grind =]
theorem pauliZ_unitary :
    pauliZ * pauliZᴴ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_two,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

set_option linter.unusedSimpArgs false in
@[grind =]
theorem phaseS_unitary :
    phaseS * phaseSᴴ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [phaseS, Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_two,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Complex.conj_I, Complex.I_mul_I]

set_option linter.unusedSimpArgs false in
@[grind =]
theorem tGate_unitary :
    tGate * tGateᴴ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tGate, Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_two,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  · change Complex.exp _ * (starRingEnd ℂ) (Complex.exp _) = 1
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp [map_mul, Complex.conj_I, Complex.conj_ofReal, map_div₀, map_ofNat]

set_option linter.unusedSimpArgs false in
@[grind =]
theorem tDaggerGate_unitary :
    tDaggerGate * tDaggerGateᴴ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tDaggerGate, Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_two,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  · change Complex.exp _ * (starRingEnd ℂ) (Complex.exp _) = 1
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, map_div₀, map_ofNat]

set_option linter.unusedSimpArgs false in
@[grind =]
theorem cnot_unitary :
    Programs.Qubit.cnot * Programs.Qubit.cnotᴴ = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Programs.Qubit.cnot, Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_four,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

set_option linter.unusedSimpArgs false in
@[grind =]
theorem czGate_unitary :
    czGate * czGateᴴ = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [czGate, Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_four,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

set_option linter.unusedSimpArgs false in
@[grind =]
theorem rzGate_unitary (θ : ℝ) :
    rzGate θ * (rzGate θ)ᴴ = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rzGate, Matrix.mul_apply, conjTranspose_apply, Fin.sum_univ_two,
          Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  · change Complex.exp _ * (starRingEnd ℂ) (Complex.exp _) = 1
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp [map_mul, Complex.conj_I, Complex.conj_ofReal]

/-! ### The Rz-family gates as `Rz` matrices -/

theorem tGate_eq_rzGate : tGate = rzGate (Real.pi / 4) := rfl

theorem tDaggerGate_eq_rzGate : tDaggerGate = rzGate (-(Real.pi / 4)) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tDaggerGate, rzGate]

theorem phaseS_eq_rzGate : phaseS = rzGate (Real.pi / 2) := by
  have h : Complex.exp (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) = Complex.I := by
    rw [mul_comm, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.exp_pi_div_two_mul_I]
  rw [rzGate, h, phaseS]

theorem pauliZ_eq_rzGate : pauliZ = rzGate Real.pi := by
  have h : Complex.exp (Complex.I * ↑Real.pi) = -1 := by
    rw [mul_comm, Complex.exp_pi_mul_I]
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauliZ, rzGate, h]

end BaseGates

/-! ## gateEmbedding Unitarity -/

/-- Every gate embedding is unitary: `gateEmbedding g * (gateEmbedding g)ᴴ = 1`. -/
@[grind =]
theorem gateEmbedding_mul_conjTranspose (g : Gate n) :
    gateEmbedding g * (gateEmbedding g)ᴴ = 1 := by
  match g with
  | .H i => exact embedGate1_unitary n i _ hadamard_unitary
  | .X i => exact embedGate1_unitary n i _ pauliX_unitary
  | .Y i => exact embedGate1_unitary n i _ pauliY_unitary
  | .Z i => exact embedGate1_unitary n i _ pauliZ_unitary
  | .S i => exact embedGate1_unitary n i _ phaseS_unitary
  | .T i => exact embedGate1_unitary n i _ tGate_unitary
  | .Tdg i => exact embedGate1_unitary n i _ tDaggerGate_unitary
  | .Rz i θ =>
    exact embedGate1_unitary n i _ (rzGate_unitary θ)
  | .RzQ i a =>
    exact embedGate1_unitary n i _ (rzGate_unitary (PiLin.toReal a))
  | .CNOT i j =>
    show (if h : i = j then 1 else embedGate2 n i j Programs.Qubit.cnot h) *
         (if h : i = j then 1 else embedGate2 n i j Programs.Qubit.cnot h)ᴴ = 1
    split
    · rw [conjTranspose_one, mul_one]
    · next h => exact embedGate2_unitary n i j _ h cnot_unitary
  | .CZ i j =>
    show (if h : i = j then 1 else embedGate2 n i j czGate h) *
         (if h : i = j then 1 else embedGate2 n i j czGate h)ᴴ = 1
    split
    · rw [conjTranspose_one, mul_one]
    · next h => exact embedGate2_unitary n i j czGate h czGate_unitary

/-- Every gate embedding is unitary (other direction). -/
@[grind =]
theorem gateEmbedding_conjTranspose_mul (g : Gate n) :
    (gateEmbedding g)ᴴ * gateEmbedding g = 1 :=
  mul_eq_one_comm.mp (gateEmbedding_mul_conjTranspose g)

/-- Package `gateEmbedding g` as a member of the unitary group. -/
def gateEmbedding_unitaryGroup (g : Gate n) : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  ⟨gateEmbedding g, by
    rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose]
    exact gateEmbedding_conjTranspose_mul g⟩

/-! ## Unitary-Channel Denotation -/

/-- Gate denotation: each gate maps to the unitary channel `ρ ↦ U ρ U†` of its
    embedding `U = gateEmbedding g`. -/
def denoteGateU (g : Gate n) : QComp (2 ^ n) Unit :=
  unitaryChannel (gateEmbedding_unitaryGroup g)

/-- Circuit denotation built from `denoteGateU`. -/
def unitaryDenote : Circuit n → QComp (2 ^ n) Unit
  | .empty      => QComp.qpure ()
  | .gate g c   => QComp.qbind (denoteGateU g) (fun _ => unitaryDenote c)
  | .seq c₁ c₂  => QComp.qbind (unitaryDenote c₁) (fun _ => unitaryDenote c₂)

/-- `unitaryChannel 1 = qpure ()`: the identity unitary channel is pure return. -/
theorem unitaryChannel_one_eq_qpure {d : ℕ} :
    unitaryChannel (1 : Matrix.unitaryGroup (Fin d) ℂ) = QComp.qpure (d := d) () := by
  apply QComp.ext_fun; intro () ρ
  show conjugate ((1 : Matrix.unitaryGroup (Fin d) ℂ) : Matrix _ _ ℂ) ρ =
    (QComp.qpure (d := d) ()).branch () ρ
  simp only [QComp.qpure, ite_true, UnitaryGroup.one_val, conjugate_apply,
    conjTranspose_one, Matrix.mul_one, Matrix.one_mul, LinearMap.id_apply]

/-- Composing `denoteGateU` via bind corresponds to multiplying unitaries. -/
theorem denoteGateU_compose (g₁ g₂ : Gate n) :
    QComp.qbind (denoteGateU g₁) (fun () => denoteGateU g₂) =
      unitaryChannel (gateEmbedding_unitaryGroup g₂ * gateEmbedding_unitaryGroup g₁) :=
  unitaryChannel_compose _ _

/-- Two circuits are equivalent under unitaryDenote iff they have the same denotation. -/
def unitaryEquiv (c₁ c₂ : Circuit n) : Prop :=
  unitaryDenote c₁ = unitaryDenote c₂

/-- A circuit pass is correct if it preserves unitary denotation. -/
def UnitaryCorrectQ (pass : Circuit n → Circuit n) : Prop :=
  ∀ c, unitaryEquiv c (pass c)

/-- The identity pass preserves unitary denotation. -/
theorem unitaryCorrectQ_id : UnitaryCorrectQ (id : Circuit n → Circuit n) :=
  fun _ => rfl

/-- Composing two unitary-correct passes yields a unitary-correct pass. -/
theorem unitaryCorrectQ_comp {pass₁ pass₂ : Circuit n → Circuit n}
    (h₁ : UnitaryCorrectQ pass₁) (h₂ : UnitaryCorrectQ pass₂) :
    UnitaryCorrectQ (pass₂ ∘ pass₁) :=
  fun c => (h₁ c).trans (h₂ (pass₁ c))

/-- A unitary-correct pass preserves quantum UC security bounds: if the source
    circuit is `ε`-close in `qdist` to an ideal functionality, so is its image
    under the pass. -/
theorem unitaryCorrect_preserves_quc {n : ℕ} {ε : ℝ≥0∞}
    (pass : Circuit n → Circuit n)
    (hpass : UnitaryCorrectQ pass)
    (F_ideal : QComp (2 ^ n) Unit)
    (c : Circuit n)
    (hsec : UCMonad.QuantumUC.qdist
              (fun () => unitaryDenote c) (fun () => F_ideal) ≤ ε) :
    UCMonad.QuantumUC.qdist
      (fun () => unitaryDenote (pass c)) (fun () => F_ideal) ≤ ε := by
  have heq : unitaryDenote (pass c) = unitaryDenote c := (hpass c).symm
  simp only [heq]
  exact hsec

/-! ## Template Correctness Under Unitary Denotation

A template correctness statement over `unitaryDenote` is a matrix equation
between the channels of the pattern and the replacement.

The key tool is `denoteGateU_compose`: sequential composition of gates
corresponds to multiplication of their unitary matrices.
-/

/-- Unitary-correct template: pattern and replacement have the same `unitaryDenote`. -/
def TemplateCorrectU {n : ℕ} (pattern replacement : Circuit n) : Prop :=
  unitaryDenote pattern = unitaryDenote replacement

/-- Empty circuit has `unitaryDenote = qpure ()`. -/
theorem unitaryDenote_empty : unitaryDenote (Circuit.empty : Circuit n) = QComp.qpure () :=
  rfl

/-- Single gate followed by empty = `denoteGateU g`. -/
theorem unitaryDenote_single (g : Gate n) :
    unitaryDenote (Circuit.single g) = denoteGateU g := by
  simp only [Circuit.single, unitaryDenote]
  show QComp.qbind (denoteGateU g) (fun _ => QComp.qpure ()) = denoteGateU g
  have : (fun (_ : Unit) => QComp.qpure (d := 2 ^ n) ()) = QComp.qpure :=
    funext (fun () => rfl)
  rw [this, QComp.qbind_qpure]

/-- Sequential composition under `unitaryDenote`. -/
theorem unitaryDenote_seq (c₁ c₂ : Circuit n) :
    unitaryDenote (Circuit.seq c₁ c₂) =
      QComp.qbind (unitaryDenote c₁) (fun _ => unitaryDenote c₂) := rfl

/-- Sequencing with `empty` on the left preserves `unitaryDenote`. -/
theorem unitaryDenote_seq_empty_left (c : Circuit n) :
    unitaryDenote (Circuit.seq .empty c) = unitaryDenote c := by
  rw [unitaryDenote_seq, unitaryDenote_empty, QComp.qpure_qbind]

/-- Sequencing with `empty` on the right preserves `unitaryDenote`. -/
theorem unitaryDenote_seq_empty_right (c : Circuit n) :
    unitaryDenote (Circuit.seq c .empty) = unitaryDenote c := by
  rw [unitaryDenote_seq]
  have : (fun (_ : Unit) => unitaryDenote (Circuit.empty : Circuit n)) =
      QComp.qpure := funext (fun () => rfl)
  rw [this, QComp.qbind_qpure]

/-- The gate embedding matrix for H squares to 1. -/
private theorem gateEmbedding_H_mul_self (q : Fin n) :
    gateEmbedding (.H q : Gate n) * gateEmbedding (.H q) = 1 := by
  show embedGate1 n q _ * embedGate1 n q _ = 1
  rw [embedGate1_mul, hadamard_sq, embedGate1_one]

/-- The unitary group element for H squared is 1. -/
private theorem gateEmbedding_H_sq (q : Fin n) :
    gateEmbedding_unitaryGroup (.H q) * gateEmbedding_unitaryGroup (.H q) =
      (1 : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) := by
  apply Subtype.ext
  exact gateEmbedding_H_mul_self q

/-- H;H = empty under unitary denotation: `H² = I`. -/
theorem templateHH_correct (q : Fin n) :
    TemplateCorrectU
      (Circuit.seq (Circuit.single (.H q)) (Circuit.single (.H q)))
      Circuit.empty := by
  -- Goal: unitaryDenote (seq (single H) (single H)) = unitaryDenote empty
  -- Unfold to: qbind (denoteGateU H) (fun _ => denoteGateU H) = qpure ()
  show unitaryDenote _ = unitaryDenote _
  simp only [unitaryDenote_seq, unitaryDenote_single, unitaryDenote_empty]
  -- Goal: qbind (denoteGateU H) (fun x => denoteGateU H) = qpure ()
  -- The binder is `fun x =>` (with unused variable), need to match `fun () =>`
  have heta : (fun (_ : Unit) => denoteGateU (n := n) (.H q)) =
      (fun () => denoteGateU (.H q)) := funext (fun () => rfl)
  rw [heta, denoteGateU_compose, gateEmbedding_H_sq, unitaryChannel_one_eq_qpure]

/-! ## Base Gate Composition Theorems (self-inverse, products) -/

section GateCompositions

open CatCrypt.Quantum.Programs.Qubit

set_option linter.unusedSimpArgs false in
/-- Pauli Y is self-inverse: Y² = I. -/
@[grind =]
theorem pauliY_sq :
    pauliY * pauliY = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [pauliY, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one,
          Complex.I_mul_I, neg_mul, mul_neg, neg_neg]

set_option linter.unusedSimpArgs false in
/-- CNOT is self-inverse: CNOT² = I. -/
@[grind =]
theorem cnot_sq :
    Programs.Qubit.cnot * Programs.Qubit.cnot = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Programs.Qubit.cnot, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_four,
          Matrix.cons_val_zero, Matrix.cons_val_one]

set_option linter.unusedSimpArgs false in
/-- T · T† = I. -/
@[grind =]
theorem tGate_mul_tDaggerGate :
    tGate * tDaggerGate = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tGate, tDaggerGate, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one]
  · change Complex.exp _ * Complex.exp _ = 1
    rw [← Complex.exp_add]; simp

set_option linter.unusedSimpArgs false in
/-- T† · T = I. -/
@[grind =]
theorem tDaggerGate_mul_tGate :
    tDaggerGate * tGate = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tGate, tDaggerGate, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one]
  · change Complex.exp _ * Complex.exp _ = 1
    rw [← Complex.exp_add]; simp

set_option linter.unusedSimpArgs false in
/-- S · S = Z: two phase gates compose to Pauli Z. -/
@[grind =]
theorem phaseS_sq_eq_pauliZ :
    phaseS * phaseS = (pauliZ : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [phaseS, pauliZ, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one,
          Complex.I_mul_I]

set_option linter.unusedSimpArgs false in
/-- T · T = S: two T gates compose to phase S. -/
@[grind =]
theorem tGate_sq_eq_phaseS :
    tGate * tGate = (phaseS : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tGate, phaseS, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one]
  · change Complex.exp _ * Complex.exp _ = Complex.I
    rw [← Complex.exp_add]
    have : Complex.I * (↑Real.pi / 4) + Complex.I * (↑Real.pi / 4) =
        Complex.I * ↑(Real.pi / 2) := by push_cast; ring
    rw [this]; clear this
    -- Goal: exp(I * ↑(pi/2)) = I
    -- Normalize: ↑(pi/2) to ↑pi / 2, then mul_comm, then exp_mul_I
    rw [Complex.ofReal_div, mul_comm, Complex.exp_mul_I]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

set_option linter.unusedSimpArgs false in
/-- H · X · H = Z: Hadamard conjugation of X gives Z. -/
@[grind =]
theorem hadamard_pauliX_hadamard :
    hadamard * pauliX * hadamard = (pauliZ : Matrix (Fin 2) (Fin 2) ℂ) := by
  -- Two-step: compute intermediate product then final
  have step : hadamard * pauliX = (Matrix.of ![![(↑(1/Real.sqrt 2) : ℂ), (↑(1/Real.sqrt 2) : ℂ)],
    ![-(↑(1/Real.sqrt 2) : ℂ), (↑(1/Real.sqrt 2) : ℂ)]]) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Programs.Qubit.hadamard, pauliX, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two,
            Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [step]; clear step
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Programs.Qubit.hadamard, pauliZ, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, neg_mul, mul_neg, neg_neg] <;>
    rw [ofReal_sqrt2_inv_sq] <;> ring

set_option linter.unusedSimpArgs false in
/-- H · Z · H = X: Hadamard conjugation of Z gives X. -/
@[grind =]
theorem hadamard_pauliZ_hadamard :
    hadamard * pauliZ * hadamard = (pauliX : Matrix (Fin 2) (Fin 2) ℂ) := by
  have step : hadamard * pauliZ = (Matrix.of ![![(↑(1/Real.sqrt 2) : ℂ), -(↑(1/Real.sqrt 2) : ℂ)],
    ![(↑(1/Real.sqrt 2) : ℂ), (↑(1/Real.sqrt 2) : ℂ)]]) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Programs.Qubit.hadamard, pauliZ, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two,
            Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [step]; clear step
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Programs.Qubit.hadamard, pauliX, Matrix.mul_apply, Matrix.of_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, neg_mul, mul_neg, neg_neg] <;>
    rw [ofReal_sqrt2_inv_sq] <;> ring

end GateCompositions

/-! ## Gate Embedding Composition Theorems -/

section EmbeddingCompositions

open CatCrypt.Quantum.Programs.Qubit

/-- X² = I at the gateEmbedding level. -/
private theorem gateEmbedding_X_mul_self (q : Fin n) :
    gateEmbedding (.X q : Gate n) * gateEmbedding (.X q) = 1 := by
  show embedGate1 n q _ * embedGate1 n q _ = 1
  rw [embedGate1_mul, pauliX_sq, embedGate1_one]

/-- X² = 1 at the unitaryGroup level. -/
private theorem gateEmbedding_X_sq (q : Fin n) :
    gateEmbedding_unitaryGroup (.X q) * gateEmbedding_unitaryGroup (.X q) =
      (1 : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) := by
  apply Subtype.ext; exact gateEmbedding_X_mul_self q

/-- Y² = I at the gateEmbedding level. -/
private theorem gateEmbedding_Y_mul_self (q : Fin n) :
    gateEmbedding (.Y q : Gate n) * gateEmbedding (.Y q) = 1 := by
  show embedGate1 n q _ * embedGate1 n q _ = 1
  rw [embedGate1_mul, pauliY_sq, embedGate1_one]

/-- Y² = 1 at the unitaryGroup level. -/
private theorem gateEmbedding_Y_sq (q : Fin n) :
    gateEmbedding_unitaryGroup (.Y q) * gateEmbedding_unitaryGroup (.Y q) =
      (1 : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) := by
  apply Subtype.ext; exact gateEmbedding_Y_mul_self q

/-- Z² = I at the gateEmbedding level. -/
private theorem gateEmbedding_Z_mul_self (q : Fin n) :
    gateEmbedding (.Z q : Gate n) * gateEmbedding (.Z q) = 1 := by
  show embedGate1 n q _ * embedGate1 n q _ = 1
  rw [embedGate1_mul, pauliZ_sq, embedGate1_one]

/-- Z² = 1 at the unitaryGroup level. -/
private theorem gateEmbedding_Z_sq (q : Fin n) :
    gateEmbedding_unitaryGroup (.Z q) * gateEmbedding_unitaryGroup (.Z q) =
      (1 : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) := by
  apply Subtype.ext; exact gateEmbedding_Z_mul_self q

/-- T · T† = I at the gateEmbedding level. -/
private theorem gateEmbedding_TTdg_mul (q : Fin n) :
    gateEmbedding (.T q : Gate n) * gateEmbedding (.Tdg q) = 1 := by
  show embedGate1 n q _ * embedGate1 n q _ = 1
  rw [embedGate1_mul, tGate_mul_tDaggerGate, embedGate1_one]

/-- T† · T = I at the gateEmbedding level. -/
private theorem gateEmbedding_TdgT_mul (q : Fin n) :
    gateEmbedding (.Tdg q : Gate n) * gateEmbedding (.T q) = 1 := by
  show embedGate1 n q _ * embedGate1 n q _ = 1
  rw [embedGate1_mul, tDaggerGate_mul_tGate, embedGate1_one]

/-- Tdg · T = 1 at the unitaryGroup level (for T;Tdg template: compose reverses). -/
private theorem gateEmbedding_TdgT_ug (q : Fin n) :
    gateEmbedding_unitaryGroup (.Tdg q) * gateEmbedding_unitaryGroup (.T q) =
      (1 : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) := by
  apply Subtype.ext; exact gateEmbedding_TdgT_mul q

/-- T · Tdg = 1 at the unitaryGroup level (for Tdg;T template: compose reverses). -/
private theorem gateEmbedding_TTdg_ug (q : Fin n) :
    gateEmbedding_unitaryGroup (.T q) * gateEmbedding_unitaryGroup (.Tdg q) =
      (1 : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) := by
  apply Subtype.ext; exact gateEmbedding_TTdg_mul q

/-- S · S = Z at the gateEmbedding level. -/
private theorem gateEmbedding_SS_eq_Z (q : Fin n) :
    gateEmbedding (.S q : Gate n) * gateEmbedding (.S q) = gateEmbedding (.Z q) := by
  show embedGate1 n q _ * embedGate1 n q _ = embedGate1 n q _
  rw [embedGate1_mul, phaseS_sq_eq_pauliZ]

/-- S · S = Z at the unitaryGroup level. -/
private theorem gateEmbedding_SS_eq_Z_ug (q : Fin n) :
    gateEmbedding_unitaryGroup (.S q) * gateEmbedding_unitaryGroup (.S q) =
      gateEmbedding_unitaryGroup (.Z q : Gate n) := by
  apply Subtype.ext; exact gateEmbedding_SS_eq_Z q

/-- T · T = S at the gateEmbedding level. -/
private theorem gateEmbedding_TT_eq_S (q : Fin n) :
    gateEmbedding (.T q : Gate n) * gateEmbedding (.T q) = gateEmbedding (.S q) := by
  show embedGate1 n q _ * embedGate1 n q _ = embedGate1 n q _
  rw [embedGate1_mul, tGate_sq_eq_phaseS]

/-- T · T = S at the unitaryGroup level. -/
private theorem gateEmbedding_TT_eq_S_ug (q : Fin n) :
    gateEmbedding_unitaryGroup (.T q) * gateEmbedding_unitaryGroup (.T q) =
      gateEmbedding_unitaryGroup (.S q : Gate n) := by
  apply Subtype.ext; exact gateEmbedding_TT_eq_S q

/-- H · X · H = Z at the gateEmbedding level (left-associated). -/
private theorem gateEmbedding_HXH_eq_Z (q : Fin n) :
    gateEmbedding (.H q : Gate n) * gateEmbedding (.X q) * gateEmbedding (.H q) =
      gateEmbedding (.Z q) := by
  show embedGate1 n q _ * embedGate1 n q _ * embedGate1 n q _ = embedGate1 n q _
  rw [embedGate1_mul, embedGate1_mul, hadamard_pauliX_hadamard]

/-- H · X · H = Z at the unitaryGroup level (left-associated). -/
private theorem gateEmbedding_HXH_eq_Z_ug (q : Fin n) :
    gateEmbedding_unitaryGroup (.H q) * gateEmbedding_unitaryGroup (.X q) *
      gateEmbedding_unitaryGroup (.H q) =
      gateEmbedding_unitaryGroup (.Z q : Gate n) := by
  apply Subtype.ext; exact gateEmbedding_HXH_eq_Z q

/-- H · Z · H = X at the gateEmbedding level (left-associated). -/
private theorem gateEmbedding_HZH_eq_X (q : Fin n) :
    gateEmbedding (.H q : Gate n) * gateEmbedding (.Z q) * gateEmbedding (.H q) =
      gateEmbedding (.X q) := by
  show embedGate1 n q _ * embedGate1 n q _ * embedGate1 n q _ = embedGate1 n q _
  rw [embedGate1_mul, embedGate1_mul, hadamard_pauliZ_hadamard]

/-- H · Z · H = X at the unitaryGroup level (left-associated). -/
private theorem gateEmbedding_HZH_eq_X_ug (q : Fin n) :
    gateEmbedding_unitaryGroup (.H q) * gateEmbedding_unitaryGroup (.Z q) *
      gateEmbedding_unitaryGroup (.H q) =
      gateEmbedding_unitaryGroup (.X q : Gate n) := by
  apply Subtype.ext; exact gateEmbedding_HZH_eq_X q

end EmbeddingCompositions

/-! ## Template Correctness Under Unitary Denotation (all templates) -/

section TemplateProofs

/-- Helper: eta-expand `fun _ => f` to `fun () => f` for Unit binders. -/
private theorem eta_unit {α : Type} (f : α) :
    (fun (_ : Unit) => f) = (fun () => f) := funext (fun () => rfl)

/-- X;X = empty under unitary denotation. -/
theorem templateXX_correct (q : Fin n) :
    TemplateCorrectU
      (Circuit.seq (Circuit.single (.X q)) (Circuit.single (.X q)))
      Circuit.empty := by
  show unitaryDenote _ = unitaryDenote _
  simp only [unitaryDenote_seq, unitaryDenote_single, unitaryDenote_empty]
  rw [eta_unit, denoteGateU_compose, gateEmbedding_X_sq, unitaryChannel_one_eq_qpure]

/-- Y;Y = empty under unitary denotation. -/
theorem templateYY_correct (q : Fin n) :
    TemplateCorrectU
      (Circuit.seq (Circuit.single (.Y q)) (Circuit.single (.Y q)))
      Circuit.empty := by
  show unitaryDenote _ = unitaryDenote _
  simp only [unitaryDenote_seq, unitaryDenote_single, unitaryDenote_empty]
  rw [eta_unit, denoteGateU_compose, gateEmbedding_Y_sq, unitaryChannel_one_eq_qpure]

/-- Z;Z = empty under unitary denotation. -/
theorem templateZZ_correct (q : Fin n) :
    TemplateCorrectU
      (Circuit.seq (Circuit.single (.Z q)) (Circuit.single (.Z q)))
      Circuit.empty := by
  show unitaryDenote _ = unitaryDenote _
  simp only [unitaryDenote_seq, unitaryDenote_single, unitaryDenote_empty]
  rw [eta_unit, denoteGateU_compose, gateEmbedding_Z_sq, unitaryChannel_one_eq_qpure]

/-- T;T† = empty under unitary denotation. -/
theorem templateTTdg_correct (q : Fin n) :
    TemplateCorrectU
      (Circuit.seq (Circuit.single (.T q)) (Circuit.single (.Tdg q)))
      Circuit.empty := by
  show unitaryDenote _ = unitaryDenote _
  simp only [unitaryDenote_seq, unitaryDenote_single, unitaryDenote_empty]
  rw [eta_unit, denoteGateU_compose, gateEmbedding_TdgT_ug, unitaryChannel_one_eq_qpure]

/-- T†;T = empty under unitary denotation. -/
theorem templateTdgT_correct (q : Fin n) :
    TemplateCorrectU
      (Circuit.seq (Circuit.single (.Tdg q)) (Circuit.single (.T q)))
      Circuit.empty := by
  show unitaryDenote _ = unitaryDenote _
  simp only [unitaryDenote_seq, unitaryDenote_single, unitaryDenote_empty]
  rw [eta_unit, denoteGateU_compose, gateEmbedding_TTdg_ug, unitaryChannel_one_eq_qpure]

/-- unitaryChannel for a single gate equals denoteGateU. -/
private theorem unitaryChannel_gateEmbedding_eq (g : Gate n) :
    unitaryChannel (gateEmbedding_unitaryGroup g) = denoteGateU g := rfl

/-- S;S = Z under unitary denotation. -/
theorem templateSS_correct (q : Fin n) :
    TemplateCorrectU
      (Circuit.seq (Circuit.single (.S q)) (Circuit.single (.S q)))
      (Circuit.single (.Z q)) := by
  show unitaryDenote _ = unitaryDenote _
  simp only [unitaryDenote_seq, unitaryDenote_single]
  rw [eta_unit, denoteGateU_compose, gateEmbedding_SS_eq_Z_ug,
      unitaryChannel_gateEmbedding_eq]

/-- T;T = S under unitary denotation. -/
theorem templateTT_correct (q : Fin n) :
    TemplateCorrectU
      (Circuit.seq (Circuit.single (.T q)) (Circuit.single (.T q)))
      (Circuit.single (.S q)) := by
  show unitaryDenote _ = unitaryDenote _
  simp only [unitaryDenote_seq, unitaryDenote_single]
  rw [eta_unit, denoteGateU_compose, gateEmbedding_TT_eq_S_ug,
      unitaryChannel_gateEmbedding_eq]

/-- Helper for triple-gate templates: unfold seq (single g1) (seq (single g2) (single g3)). -/
private theorem unitaryDenote_triple (g₁ g₂ g₃ : Gate n) :
    unitaryDenote (Circuit.seq (Circuit.single g₁)
      (Circuit.seq (Circuit.single g₂) (Circuit.single g₃))) =
    QComp.qbind (denoteGateU g₁)
      (fun _ => QComp.qbind (denoteGateU g₂) (fun _ => denoteGateU g₃)) := by
  simp only [unitaryDenote_seq, unitaryDenote_single]

/-- Compose three gates into a single unitaryChannel. -/
private theorem denoteGateU_compose3 (g₁ g₂ g₃ : Gate n) :
    QComp.qbind (denoteGateU g₁)
      (fun _ => QComp.qbind (denoteGateU g₂) (fun _ => denoteGateU g₃)) =
    unitaryChannel (gateEmbedding_unitaryGroup g₃ * gateEmbedding_unitaryGroup g₂ *
                     gateEmbedding_unitaryGroup g₁) := by
  have h1 : (fun (_ : Unit) => QComp.qbind (denoteGateU g₂)
      (fun _ => denoteGateU g₃)) =
    (fun () => QComp.qbind (denoteGateU g₂) (fun _ => denoteGateU g₃)) :=
    funext (fun () => rfl)
  rw [h1]
  have h2 : (fun (_ : Unit) => denoteGateU (n := n) g₃) =
    (fun () => denoteGateU g₃) := funext (fun () => rfl)
  rw [h2, denoteGateU_compose]
  rw [show denoteGateU g₁ = unitaryChannel (gateEmbedding_unitaryGroup g₁) from rfl]
  have h3 : (fun () => unitaryChannel
      (gateEmbedding_unitaryGroup g₃ * gateEmbedding_unitaryGroup g₂)) =
    (fun (_ : Unit) => unitaryChannel
      (gateEmbedding_unitaryGroup g₃ * gateEmbedding_unitaryGroup g₂)) :=
    funext (fun () => rfl)
  rw [h3, unitaryChannel_compose, mul_assoc]

/-- H;X;H = Z under unitary denotation. -/
theorem templateHXH_correct (q : Fin n) :
    TemplateCorrectU
      (Circuit.seq (Circuit.single (.H q))
        (Circuit.seq (Circuit.single (.X q)) (Circuit.single (.H q))))
      (Circuit.single (.Z q)) := by
  show unitaryDenote _ = unitaryDenote _
  rw [unitaryDenote_triple, denoteGateU_compose3, unitaryDenote_single]
  rw [gateEmbedding_HXH_eq_Z_ug, unitaryChannel_gateEmbedding_eq]

/-- H;Z;H = X under unitary denotation. -/
theorem templateHZH_correct (q : Fin n) :
    TemplateCorrectU
      (Circuit.seq (Circuit.single (.H q))
        (Circuit.seq (Circuit.single (.Z q)) (Circuit.single (.H q))))
      (Circuit.single (.X q)) := by
  show unitaryDenote _ = unitaryDenote _
  rw [unitaryDenote_triple, denoteGateU_compose3, unitaryDenote_single]
  rw [gateEmbedding_HZH_eq_X_ug, unitaryChannel_gateEmbedding_eq]

end TemplateProofs

end CatCrypt.Quantum.GateUnitarity
