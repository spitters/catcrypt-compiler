/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatBlocks
public meta import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatBlocks

/-!
# The unsaturated Solinas field template

The field operations of the unsaturated representation of `UnsatZ` as `jasminDialect`
blocks, each with an integer semantics stated without bounds and a word-level statement under
a bounds certificate `boundsOkMR … = true` (`ComRangeExact.denoteMR_eq_denoteZ_of_boundsOk`),
bundled with the carried product and square of `UnsatBlocks` into a template record.

The blocks are `add` (limbwise sum), `sub` (limbwise `a + 2p - b`), `carry` (the carry
schedule of `UnsatZ.carryChain` on 64-bit limbs), `freeze` (canonical reduction: a carry chain
adding the digits of `2^(b·n) - p`, whose final carry says whether the value is at least `p`,
then a carry chain adding the digits of `p` times the negation of that carry), `toBytes` (the
little-endian bytes of canonical limbs, by a buffer that loads a limb when fewer than eight
bits remain) and `fromBytes` (the limbs of little-endian bytes, by a buffer that loads bytes
until `b` bits are buffered). Limbs are 64-bit words and bytes are 8-bit words; every block
lies in the exact fragment of `ComRangeExact` read unsigned.

The integer layer works on lists of limbs with the Horner value `evalL b`; `evalZ_eq_evalL`
relates it to `UnsatParams.evalZ`. The template `FieldReprTemplate` records the loose/tight
discipline as certificates: `fromBytes` produces tight limbs, `add`/`sub` take tight and
produce loose limbs, `carry`, `carryMul` and `carrySquare` take loose and produce tight limbs,
`freeze` takes tight and produces canonical limbs `[0, 2^b - 1]`, and `toBytes` takes
canonical limbs. The bound `Σ tight_i · 2^(b·i) < 2p` is the precondition of `freeze`.

Instances: Curve25519 (`5 × 51`, fiat-crypto's carry schedule and bounds) and p448
(`8 × 56`). Poly1305 at uniform `3 × 44` has no instance: its top limb carries at 44 bits, so
tight limbs have value up to `2^132 > 2p` and the precondition of `freeze` fails.

## Main definitions

* `evalL`, `digits`, `cchainZ`, `freezeZ`, `loadZ`, `packZ`, `ldZ`, `unpackZ`: the integer
  layer.
* `addBlk`, `subBlk`, `carryBlk`, `freezeBlk`, `toBytesBlk`, `fromBytesBlk`,
  `fromBytes2Blk`: the blocks.
* `ivVec`, `ivsLe`: interval vectors and their inclusion.
* `FieldReprTemplate`, `FieldReprTemplate.val`, `FieldReprTemplate.Good`,
  `FieldReprTemplate.runBin`, `FieldReprTemplate.runSq`: the template and its byte-level runs.
* `curve25519Repr`, `p448Repr`: the instances.

## Main results

* `cchainZ_spec`, `freezeZ_spec`, `packZ_spec`, `unpackZ_spec`: the integer layer; `freeze`
  maps a value `X < 2p` on nonnegative limbs to the digits of `X mod p`.
* `addBlk_denoteZ`, `subBlk_denoteZ`, `carryBlk_denoteZ`, `freezeBlk_denoteZ`,
  `toBytesBlk_denoteZ`, `fromBytesBlk_denoteZ`, `fromBytes2Blk_denoteZ`: the integer semantics
  of each block; no bounds.
* `FieldReprTemplate.fromBytes_sem`, `fromBytes2_sem`, `body_sem`, `carry_sem`, `sq_sem`,
  `freeze_sem`, `toBytes_sem`: each block under its certificate.
* `FieldReprTemplate.runBin_abi`, `runSq_abi`, `runBin_abi_zmod`: bytes in, bytes out — the
  output bytes encode the canonical representative of the operation on the input values.
* `curve25519Repr_runBin_abi`, `p448Repr_runBin_abi`: the ABI at the instances.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatField

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange (hget JCtxt)
open CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (MC bindK)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatZ
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatBlocks

/-! ## 1. Values of limb lists -/

/-- The value `Σ l_i · 2^(b·i)` of a list of limbs of width `b`, in Horner form. -/
def evalL (b : ℕ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a + 2 ^ b * evalL b l

theorem evalL_nonneg (b : ℕ) : ∀ l : List ℤ, (∀ a ∈ l, 0 ≤ a) → 0 ≤ evalL b l
  | [], _ => le_rfl
  | a :: l, h => by
    simp only [evalL]
    have := evalL_nonneg b l fun x hx => h x (by simp [hx])
    have := h a (by simp)
    positivity

/-- A list of digits below `2^b` has value below `2^(b·length)`. -/
theorem evalL_lt (b : ℕ) : ∀ l : List ℤ, (∀ a ∈ l, 0 ≤ a ∧ a < 2 ^ b) →
    evalL b l < 2 ^ (b * l.length)
  | [], _ => by simp [evalL]
  | a :: l, h => by
    have ih := evalL_lt b l fun x hx => h x (by simp [hx])
    have ha := h a (by simp)
    simp only [evalL, List.length_cons, mul_add, mul_one, pow_add]
    have : 2 ^ b * evalL b l ≤ 2 ^ b * (2 ^ (b * l.length) - 1) :=
      mul_le_mul_of_nonneg_left (by omega) (by positivity)
    nlinarith

/-- The value of `List.ofFn f` is the weighted sum `Σ f i · 2^(b·i)`. -/
theorem evalL_ofFn (b : ℕ) : ∀ (m : ℕ) (f : Fin m → ℤ),
    evalL b (List.ofFn f) = ∑ i : Fin m, f i * 2 ^ (b * (i : ℕ))
  | 0, _ => by simp [evalL]
  | m + 1, f => by
    rw [List.ofFn_succ, evalL, evalL_ofFn b m, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, mul_zero, pow_zero, mul_one, Fin.val_succ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_add, mul_one, pow_add]; ring

theorem evalZ_eq_evalL (P : UnsatParams) (f : Fin P.n → ℤ) :
    P.evalZ f = evalL P.b (List.ofFn f) := (evalL_ofFn P.b P.n f).symm

/-- Bounds limbwise give bounds on the value. -/
theorem evalL_ofFn_mono (b : ℕ) : ∀ (m : ℕ) (x h : Fin m → ℤ), (∀ i, 0 ≤ x i ∧ x i ≤ h i) →
    evalL b (List.ofFn x) ≤ evalL b (List.ofFn h)
  | 0, _, _, _ => le_rfl
  | m + 1, x, h, hx => by
    rw [List.ofFn_succ, List.ofFn_succ, evalL, evalL]
    have := evalL_ofFn_mono b m (fun i => x i.succ) (fun i => h i.succ) fun i => hx i.succ
    have := (hx 0).2
    have : (0 : ℤ) < 2 ^ b := by positivity
    nlinarith

/-- The `m` digits of `v` in base `2^b`, least significant first. -/
def digits (b : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | m + 1, v => v % 2 ^ b :: digits b m (v / 2 ^ b)

theorem digits_length (b : ℕ) : ∀ m v, (digits b m v).length = m
  | 0, _ => rfl
  | m + 1, v => by simp [digits, digits_length b m]

theorem evalL_digits (b : ℕ) : ∀ m v,
    evalL b ((digits b m v).map (Nat.cast : ℕ → ℤ)) = ((v % 2 ^ (b * m) : ℕ) : ℤ)
  | 0, v => by simp [digits, evalL]
  | m + 1, v => by
    rw [digits, List.map_cons, evalL, evalL_digits b m, mul_add, mul_one, add_comm (b * m) b,
      pow_add, Nat.mod_mul]
    push_cast; ring

/-! ## 2. Carry chains with an addend -/

theorem lowZ_lt (b : ℕ) (x : ℤ) : lowZ b x < 2 ^ b := by
  unfold lowZ
  have : x.toNat % 2 ^ b < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)
  exact_mod_cast this

/-- The chain `t_i = x_i + M_i · f + c_i`, digit `t_i mod 2^b`, carry `c_{i+1} = ⌊t_i / 2^b⌋`;
    the digits and the final carry. -/
def cchainZ (b : ℕ) : List ℤ → List ℕ → ℤ → ℤ → List ℤ × ℤ
  | x :: xs, M :: Ms, f, c =>
    ((lowZ b (x + mulC M f + c)) :: (cchainZ b xs Ms f ((x + mulC M f + c) / 2 ^ b)).1,
      (cchainZ b xs Ms f ((x + mulC M f + c) / 2 ^ b)).2)
  | _, _, _, c => ([], c)

/-- **The value of a carry chain.** On nonnegative inputs of equal lengths, the digits lie in
    `[0, 2^b)`, the carry is nonnegative, and digits plus the carry at weight `b · length`
    equal the inputs plus `f` times the addends plus the carry in. -/
theorem cchainZ_spec (b : ℕ) : ∀ (xs : List ℤ) (Ms : List ℕ) (f c : ℤ),
    xs.length = Ms.length → (∀ x ∈ xs, 0 ≤ x) → 0 ≤ f → 0 ≤ c →
    evalL b (cchainZ b xs Ms f c).1 + 2 ^ (b * xs.length) * (cchainZ b xs Ms f c).2 =
        evalL b xs + f * evalL b (Ms.map (Nat.cast : ℕ → ℤ)) + c ∧
      (∀ d ∈ (cchainZ b xs Ms f c).1, 0 ≤ d ∧ d < 2 ^ b) ∧ 0 ≤ (cchainZ b xs Ms f c).2 ∧
      (cchainZ b xs Ms f c).1.length = xs.length
  | [], [], f, c, _, _, _, hc => by simp [cchainZ, evalL, hc]
  | [], _ :: _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _ => by simp at h
  | x :: xs, M :: Ms, f, c, hl, hx, hf, hc => by
    have hx0 : 0 ≤ x := hx x (by simp)
    have ht : 0 ≤ x + mulC M f + c := by
      rw [mulC_eq]; have : (0 : ℤ) ≤ M := Int.natCast_nonneg _; positivity
    obtain ⟨e, hd, hc', hlen⟩ := cchainZ_spec b xs Ms f ((x + mulC M f + c) / 2 ^ b)
      (by simpa using hl) (fun y hy => hx y (by simp [hy])) hf
      (Int.ediv_nonneg ht (by positivity))
    refine ⟨?_, ?_, hc', by simp [cchainZ, hlen]⟩
    · simp only [cchainZ, evalL, List.length_cons, List.map_cons]
      have hl2 := lowZ_add (b := b) ht
      have hM := mulC_eq M f
      rw [mul_add, mul_one, pow_add]
      linear_combination (2 : ℤ) ^ b * e + hl2 + hM
    · intro d hd'
      simp only [cchainZ, List.mem_cons] at hd'
      rcases hd' with rfl | hd'
      · exact ⟨lowZ_nonneg _ _, lowZ_lt _ _⟩
      · exact hd d hd'

/-! ## 3. Canonical reduction -/

/-- The integer canonical reduction: the chain adding the digits `md` of `2^(b·n) - p` with
    `f = 1`, whose carry `c` is `1` exactly when the value is at least `p`; then the chain
    adding the digits `pd` of `p` times `(c + 1) and 1`, the final carry dropped. -/
def freezeZ (b : ℕ) (md pd : List ℕ) (xs : List ℤ) : List ℤ :=
  (cchainZ b (cchainZ b xs md 1 0).1 pd (andZ ((cchainZ b xs md 1 0).2 + 1) 1) 0).1

theorem andZ_one_one : andZ (0 + 1) 1 = 1 := by decide
theorem andZ_two_one : andZ (1 + 1) 1 = 0 := by decide

/-- **The canonical reduction.** For `n` nonnegative limbs of value `X < 2p`, with `md` the
    digits of `2^(b·n) - p` and `pd` the digits of `p`, the output digits lie in `[0, 2^b)`
    and their value is `X mod p`. -/
theorem freezeZ_spec (b n : ℕ) (p : ℤ) (md pd : List ℕ) (xs : List ℤ) (hxl : xs.length = n)
    (hml : md.length = n) (hpl : pd.length = n)
    (hm : evalL b (md.map (Nat.cast : ℕ → ℤ)) = 2 ^ (b * n) - p)
    (hp : evalL b (pd.map (Nat.cast : ℕ → ℤ)) = p) (hp0 : 0 < p) (hpB : p ≤ 2 ^ (b * n))
    (hx : ∀ x ∈ xs, 0 ≤ x) (hX : evalL b xs < 2 * p) :
    evalL b (freezeZ b md pd xs) = evalL b xs % p ∧
      (∀ d ∈ freezeZ b md pd xs, 0 ≤ d ∧ d < 2 ^ b) ∧ (freezeZ b md pd xs).length = n := by
  have hX0 := evalL_nonneg b xs hx
  set B : ℤ := 2 ^ (b * n) with hB
  have hB0 : 0 < B := by positivity
  obtain ⟨e1, hd1, hc1, hl1⟩ := cchainZ_spec b xs md 1 0 (by omega) hx (by norm_num) le_rfl
  set D := (cchainZ b xs md 1 0).1 with hD
  set c1 := (cchainZ b xs md 1 0).2 with hc1d
  rw [hxl, hm] at e1
  have hDv := evalL_lt b D hd1
  rw [hl1, hxl] at hDv
  rw [← hB] at e1 hDv
  have hDn := evalL_nonneg b D fun d hd => (hd1 d hd).1
  have hc1le : c1 ≤ 1 := by
    by_contra hcon
    have : 2 * B ≤ c1 * B := by nlinarith
    nlinarith
  have hDl : D.length = n := by rw [hl1, hxl]
  have hDnn : ∀ d ∈ D, 0 ≤ d := fun d hd => (hd1 d hd).1
  unfold freezeZ
  rw [← hD, ← hc1d]
  rcases (show c1 = 0 ∨ c1 = 1 by omega) with h0 | h1
  · rw [h0, andZ_one_one]
    obtain ⟨e2, hd2, hc2, hl2⟩ := cchainZ_spec b D pd 1 0 (by omega) hDnn (by norm_num) le_rfl
    rw [hDl, hp] at e2
    rw [h0] at e1
    have hEv := evalL_lt b _ hd2
    have hEn := evalL_nonneg b _ fun d hd => (hd2 d hd).1
    rw [hl2, hDl] at hEv
    rw [← hB] at e2 hEv
    have hXp : evalL b xs < p := by linarith
    set c2 := (cchainZ b D pd 1 0).2
    have hc2 : c2 = 1 := by
      have h1 : 1 ≤ c2 := by
        by_contra hcon
        have : c2 = 0 := by omega
        rw [this] at e2; linarith
      have h2 : c2 ≤ 1 := by
        by_contra hcon
        have : 2 * B ≤ c2 * B := by nlinarith
        nlinarith
      omega
    rw [hc2] at e2
    refine ⟨?_, hd2, by rw [hl2, hDl]⟩
    rw [Int.emod_eq_of_lt hX0 hXp]
    linarith
  · rw [h1, andZ_two_one]
    obtain ⟨e2, hd2, hc2, hl2⟩ := cchainZ_spec b D pd 0 0 (by omega) hDnn le_rfl le_rfl
    rw [hDl] at e2
    rw [h1] at e1
    have hEv := evalL_lt b _ hd2
    have hEn := evalL_nonneg b _ fun d hd => (hd2 d hd).1
    rw [hl2, hDl] at hEv
    rw [← hB] at e2 hEv
    set c2 := (cchainZ b D pd 0 0).2
    have hpX : p ≤ evalL b xs := by linarith
    have hc2 : c2 = 0 := by
      by_contra hcon
      have h1c : 1 ≤ c2 := by omega
      have : B ≤ c2 * B := by nlinarith
      nlinarith
    rw [hc2] at e2
    refine ⟨?_, hd2, by rw [hl2, hDl]⟩
    have : evalL b xs % p = evalL b xs - p := by
      rw [← Int.emod_eq_of_lt (by linarith : 0 ≤ evalL b xs - p) (by linarith : evalL b xs - p < p),
        Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod_of_dvd _ (dvd_refl p)]
    rw [this]
    linarith

/-! ## 4. Packing limbs into bytes and bytes into limbs -/

/-- One load of the byte packer: when fewer than `8` bits are buffered in `acc` and a limb
    remains, the next limb is added at weight `2^bits` and `b` bits more are buffered. -/
def loadZ (b bits : ℕ) (acc : ℤ) : List ℤ → ℤ × ℕ × List ℤ
  | e :: r => if bits < 8 then (acc + e * 2 ^ bits, bits + b, r) else (acc, bits, e :: r)
  | [] => (acc, bits, [])

/-- The `N` bytes of the buffer `acc` of `bits` bits followed by the limbs `rest`: each byte
    is the low `8` bits of the buffer after a load, the buffer then shifted down by `8`. -/
def packZ (b : ℕ) : ℕ → ℤ → ℕ → List ℤ → List ℤ
  | 0, _, _, _ => []
  | N + 1, acc, bits, rest =>
    lowZ 8 (loadZ b bits acc rest).1 ::
      packZ b N ((loadZ b bits acc rest).1 / 2 ^ 8) ((loadZ b bits acc rest).2.1 - 8)
        (loadZ b bits acc rest).2.2

theorem loadZ_spec (b bits : ℕ) (hb : 8 ≤ b) (acc : ℤ) (rest : List ℤ) (ha : 0 ≤ acc)
    (hr : ∀ e ∈ rest, 0 ≤ e) :
    (loadZ b bits acc rest).1 + 2 ^ (loadZ b bits acc rest).2.1 *
        evalL b (loadZ b bits acc rest).2.2 = acc + 2 ^ bits * evalL b rest ∧
      0 ≤ (loadZ b bits acc rest).1 ∧ (∀ e ∈ (loadZ b bits acc rest).2.2, 0 ≤ e) ∧
      ((loadZ b bits acc rest).2.2 = [] ∨ 8 ≤ (loadZ b bits acc rest).2.1) := by
  cases rest with
  | nil => exact ⟨rfl, ha, by simp [loadZ], Or.inl rfl⟩
  | cons e r =>
    have he : 0 ≤ e := hr e (by simp)
    by_cases h : bits < 8
    · simp only [loadZ, h, ite_true]
      refine ⟨?_, by positivity, fun x hx => hr x (by simp [hx]), Or.inr (by omega)⟩
      simp only [evalL, pow_add]; ring
    · simp only [loadZ, h, ite_false]
      exact ⟨by simp, ha, hr, Or.inr (by omega)⟩

theorem emit_eq (k bits : ℕ) (b : ℕ) (a : ℤ) (r : List ℤ) (ha : 0 ≤ a) (h : r = [] ∨ k ≤ bits) :
    a + 2 ^ bits * evalL b r = lowZ k a + 2 ^ k * (a / 2 ^ k + 2 ^ (bits - k) * evalL b r) := by
  have hl := lowZ_add (b := k) ha
  rcases h with rfl | h
  · simp only [evalL, mul_zero, add_zero]; linarith
  · have : (2 : ℤ) ^ bits = 2 ^ k * 2 ^ (bits - k) := by rw [← pow_add, Nat.add_sub_cancel' h]
    rw [this]; linear_combination -hl

theorem packZ_length (b : ℕ) : ∀ N acc bits rest, (packZ b N acc bits rest).length = N
  | 0, _, _, _ => rfl
  | N + 1, _, _, _ => by simp [packZ, packZ_length b N]

/-- **The bytes of the packer.** The bytes lie in `[0, 256)`, and for a remainder `R ≥ 0`
    their little-endian value plus `R · 2^(8N)` is the buffer plus the limbs at weight
    `2^bits`. -/
theorem packZ_spec (b : ℕ) (hb : 8 ≤ b) : ∀ (N : ℕ) (acc : ℤ) (bits : ℕ) (rest : List ℤ),
    0 ≤ acc → (∀ e ∈ rest, 0 ≤ e) → ∃ R, 0 ≤ R ∧
      evalL 8 (packZ b N acc bits rest) + 2 ^ (8 * N) * R = acc + 2 ^ bits * evalL b rest ∧
      ∀ d ∈ packZ b N acc bits rest, 0 ≤ d ∧ d < 2 ^ 8
  | 0, acc, bits, rest, ha, hr => by
    refine ⟨acc + 2 ^ bits * evalL b rest, ?_, by simp [packZ, evalL], by simp [packZ]⟩
    have := evalL_nonneg b rest hr
    positivity
  | N + 1, acc, bits, rest, ha, hr => by
    obtain ⟨e1, ha1, hr1, hor⟩ := loadZ_spec b bits hb acc rest ha hr
    obtain ⟨R, hR, e2, hd⟩ := packZ_spec b hb N ((loadZ b bits acc rest).1 / 2 ^ 8)
      ((loadZ b bits acc rest).2.1 - 8) (loadZ b bits acc rest).2.2
      (Int.ediv_nonneg ha1 (by positivity)) hr1
    refine ⟨R, hR, ?_, ?_⟩
    · simp only [packZ, evalL]
      rw [← e1, emit_eq 8 _ b _ _ ha1 hor, ← e2, mul_add, pow_add]; ring
    · intro d hd'
      simp only [packZ, List.mem_cons] at hd'
      rcases hd' with rfl | hd'
      · exact ⟨lowZ_nonneg _ _, lowZ_lt _ _⟩
      · exact hd d hd'

/-- The byte loader: while bytes remain and fewer than `b` bits are buffered (or always, when
    `all`), the next byte is added to `acc` at weight `2^bits`. -/
def ldZ (b : ℕ) (all : Bool) : ℤ → ℕ → List ℤ → ℤ × ℕ × List ℤ
  | acc, bits, [] => (acc, bits, [])
  | acc, bits, y :: ys =>
    if all || decide (bits < b) then ldZ b all (acc + y * 2 ^ bits) (bits + 8) ys
    else (acc, bits, y :: ys)

/-- The `n` limbs of the buffer `acc` of `bits` bits followed by the bytes `rest`: each limb
    but the last is the low `b` bits of the buffer after a load, the buffer then shifted down
    by `b`; the last limb is the buffer after loading every remaining byte. -/
def unpackZ (b : ℕ) : ℕ → ℤ → ℕ → List ℤ → List ℤ
  | 0, _, _, _ => []
  | 1, acc, bits, rest => [(ldZ b true acc bits rest).1]
  | n + 2, acc, bits, rest =>
    lowZ b (ldZ b false acc bits rest).1 ::
      unpackZ b (n + 1) ((ldZ b false acc bits rest).1 / 2 ^ b)
        ((ldZ b false acc bits rest).2.1 - b) (ldZ b false acc bits rest).2.2

theorem ldZ_spec (b : ℕ) (all : Bool) : ∀ (acc : ℤ) (bits : ℕ) (rest : List ℤ), 0 ≤ acc →
    (∀ e ∈ rest, 0 ≤ e) →
    (ldZ b all acc bits rest).1 + 2 ^ (ldZ b all acc bits rest).2.1 *
        evalL 8 (ldZ b all acc bits rest).2.2 = acc + 2 ^ bits * evalL 8 rest ∧
      0 ≤ (ldZ b all acc bits rest).1 ∧ (∀ e ∈ (ldZ b all acc bits rest).2.2, 0 ≤ e) ∧
      ((ldZ b all acc bits rest).2.2 = [] ∨ b ≤ (ldZ b all acc bits rest).2.1) ∧
      (all = true → (ldZ b all acc bits rest).2.2 = [])
  | acc, bits, [], ha, _ => ⟨rfl, ha, by simp [ldZ], Or.inl rfl, fun _ => rfl⟩
  | acc, bits, y :: ys, ha, hr => by
    have hy : 0 ≤ y := hr y (by simp)
    unfold ldZ
    split_ifs with h
    · obtain ⟨e, h1, h2, h3, h4⟩ := ldZ_spec b all (acc + y * 2 ^ bits) (bits + 8) ys
        (by positivity) (fun x hx => hr x (by simp [hx]))
      refine ⟨?_, h1, h2, h3, h4⟩
      rw [e]; simp only [evalL, pow_add]; ring
    · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h
      exact ⟨rfl, ha, hr, Or.inr (show b ≤ bits by omega), fun h' => absurd h' (by simp [h.1])⟩

theorem unpackZ_length (b : ℕ) : ∀ n acc bits rest, (unpackZ b (n + 1) acc bits rest).length =
    n + 1
  | 0, _, _, _ => rfl
  | n + 1, _, _, _ => by simp [unpackZ, unpackZ_length b n]

/-- **The limbs of the loader.** The value of the `n + 1` limbs is the buffer plus the bytes
    at weight `2^bits`. -/
theorem unpackZ_spec (b : ℕ) : ∀ (n : ℕ) (acc : ℤ) (bits : ℕ) (rest : List ℤ), 0 ≤ acc →
    (∀ e ∈ rest, 0 ≤ e) →
    evalL b (unpackZ b (n + 1) acc bits rest) = acc + 2 ^ bits * evalL 8 rest
  | 0, acc, bits, rest, ha, hr => by
    obtain ⟨e, -, -, -, h4⟩ := ldZ_spec b true acc bits rest ha hr
    rw [h4 rfl] at e
    simp only [unpackZ, evalL] at e ⊢
    linarith
  | n + 1, acc, bits, rest, ha, hr => by
    obtain ⟨e1, ha1, hr1, hor, -⟩ := ldZ_spec b false acc bits rest ha hr
    have e2 := unpackZ_spec b n ((ldZ b false acc bits rest).1 / 2 ^ b)
      ((ldZ b false acc bits rest).2.1 - b) (ldZ b false acc bits rest).2.2
      (Int.ediv_nonneg ha1 (by positivity)) hr1
    simp only [unpackZ, evalL]
    rw [e2, ← e1, emit_eq b _ 8 _ _ ha1 hor]

/-! ## 5. Word combinators -/

/-- The 8-bit register type. -/
abbrev r8 : JasminTy := .reg 8

/-- The expression `shlImm w n` on `a`. -/
def eShl {Γ : JCtxt} (w n : ℕ) (a : Var Γ (.reg w)) : Expr jasminDialect Γ (.reg w) :=
  { op := .shlImm w n, retTy_eq := rfl, args := .cons a .nil }

theorem eShl_opZ {Γ : JCtxt} (Z : ZVec Γ) (w n : ℕ) (a : Var Γ (.reg w)) :
    opZ (eShl w n a).op (eShl w n a).args Z = hget Z a * 2 ^ n := rfl

/-- The integer values of the variables `xa`, in order. -/
def valsF {Γ : JCtxt} {t : JasminTy} (Z : ZVec Γ) {m : ℕ} (xa : Fin m → Var Γ t) : List ℤ :=
  List.ofFn fun i => hget Z (xa i)

theorem valsF_succ {Γ : JCtxt} {t : JasminTy} (Z : ZVec Γ) {m : ℕ} (xa : Fin (m + 1) → Var Γ t) :
    valsF Z xa = hget Z (xa 0) :: valsF Z (fun i => xa i.succ) := List.ofFn_succ

theorem valsF_map {Γ Δ : JCtxt} {t : JasminTy} {r : Ctxt.Hom Γ Δ} {Z : ZVec Γ} {Z' : ZVec Δ}
    (h : PresZ r Z Z') {m : ℕ} (xa : Fin m → Var Γ t) : valsF Z' (fun i => r (xa i)) = valsF Z xa :=
  by simp only [valsF, h]

/-- The variables of a list as a function on `Fin m`, `d` past the end of the list. -/
def lf {Δ : JCtxt} {t : JasminTy} (os : List (Var Δ t)) (d : Var Δ t) (m : ℕ) : Fin m → Var Δ t :=
  fun i => os.getD i d

theorem valsF_lf {Δ : JCtxt} {t : JasminTy} (Z : ZVec Δ) (os : List (Var Δ t)) (d : Var Δ t)
    (m : ℕ) (h : os.length = m) : valsF Z (lf os d m) = os.map fun v => hget Z v := by
  subst h
  apply List.ext_getElem (by simp [valsF])
  intro i h1 h2
  simp [valsF, lf]

/-- The sum of the limbs `xa` and `xb`, limb by limb at 64 bits. -/
def addLK {ts : List JasminTy} : (m : ℕ) → {Γ : JCtxt} → (Fin m → Var Γ r64) →
    (Fin m → Var Γ r64) → (∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → List (Var Δ r64) → MC Δ ts) → MC Γ ts
  | 0, _, _, _, k => k (fun u => u) []
  | m + 1, _, xa, xb, k =>
    bindK (eAr .add 64 (xa 0) (xb 0)) fun r s =>
    addLK m (fun i => r (xa i.succ)) (fun i => r (xb i.succ)) fun r' os =>
      k (fun u => r' (r u)) (r' s :: os)

theorem addLK_Q {ts : List JasminTy} : ∀ (m : ℕ) {Γ : JCtxt} (xa xb : Fin m → Var Γ r64)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → List (Var Δ r64) → MC Δ ts) (Z : ZVec Γ)
    (Q : ZVec ts → Prop)
    (_ : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (os : List (Var Δ r64)) (Z' : ZVec Δ), PresZ r Z Z' →
      os.map (fun v => hget Z' v) = List.ofFn (fun i => hget Z (xa i) + hget Z (xb i)) →
        Q ((k r os).denoteZ Z')),
    Q ((addLK m xa xb k).denoteZ Z)
  | 0, _, _, _, k, Z, Q, hk => hk _ _ _ (PresZ.id Z) rfl
  | m + 1, _, xa, xb, k, Z, Q, hk => by
    refine bindK_Q _ _ _ _ fun r s Z1 h1 hs => ?_
    refine addLK_Q m _ _ _ _ _ fun r' os Z2 h2 hos => hk _ _ _ (PresZ.comp h1 h2) ?_
    rw [List.map_cons, hos, List.ofFn_succ, h2, hs, eAr_opZ]
    simp only [h1]; rfl

/-- The limbs `xa + bal - xb`, limb by limb at 64 bits, with the constants `bal`. -/
def subLK {ts : List JasminTy} : (m : ℕ) → {Γ : JCtxt} → (Fin m → ℕ) → (Fin m → Var Γ r64) →
    (Fin m → Var Γ r64) → (∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → List (Var Δ r64) → MC Δ ts) → MC Γ ts
  | 0, _, _, _, _, k => k (fun u => u) []
  | m + 1, _, bal, xa, xb, k =>
    bindK (eK 64 (bal 0)) fun r1 c =>
    bindK (eAr .add 64 (r1 (xa 0)) c) fun r2 t =>
    bindK (eAr .sub 64 t (r2 (r1 (xb 0)))) fun r3 s =>
    subLK m (fun i => bal i.succ) (fun i => r3 (r2 (r1 (xa i.succ))))
      (fun i => r3 (r2 (r1 (xb i.succ)))) fun r' os =>
      k (fun u => r' (r3 (r2 (r1 u)))) (r' s :: os)

theorem subLK_Q {ts : List JasminTy} : ∀ (m : ℕ) {Γ : JCtxt} (bal : Fin m → ℕ)
    (_ : ∀ i, bal i < 2 ^ 64) (xa xb : Fin m → Var Γ r64)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → List (Var Δ r64) → MC Δ ts) (Z : ZVec Γ)
    (Q : ZVec ts → Prop)
    (_ : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (os : List (Var Δ r64)) (Z' : ZVec Δ), PresZ r Z Z' →
      os.map (fun v => hget Z' v) =
        List.ofFn (fun i => hget Z (xa i) + (bal i : ℤ) - hget Z (xb i)) →
        Q ((k r os).denoteZ Z')),
    Q ((subLK m bal xa xb k).denoteZ Z)
  | 0, _, _, _, _, _, k, Z, Q, hk => hk _ _ _ (PresZ.id Z) rfl
  | m + 1, _, bal, hbal, xa, xb, k, Z, Q, hk => by
    refine bindK_Q _ _ _ _ fun r1 c Z1 h1 hc => ?_
    refine bindK_Q _ _ _ _ fun r2 t Z2 h2 ht => ?_
    refine bindK_Q _ _ _ _ fun r3 s Z3 h3 hs => ?_
    refine subLK_Q m _ (fun i => hbal i.succ) _ _ _ _ _ fun r' os Z4 h4 hos =>
      hk _ _ _ (PresZ.comp (PresZ.comp (PresZ.comp h1 h2) h3) h4) ?_
    rw [List.map_cons, hos, List.ofFn_succ, h4, hs]
    simp only [eAr_opZ, ht, hc, eK_opZ, Nat.mod_eq_of_lt (hbal 0), binZ, h1, h2, h3]

/-- The carry chain of `cchainZ`: `t = x_i + M_i · f + c`, then `splitK b`. -/
def cchainK {ts : List JasminTy} (b : ℕ) : (m : ℕ) → {Γ : JCtxt} → (Fin m → ℕ) →
    (Fin m → Var Γ r64) → Var Γ r64 → Var Γ r64 →
    (∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → List (Var Δ r64) → Var Δ r64 → MC Δ ts) → MC Γ ts
  | 0, _, _, _, _, c, k => k (fun u => u) [] c
  | m + 1, _, Ms, xa, f, c, k =>
    mulCK (Ms 0) f fun r a =>
    bindK (eAr .add 64 (r (xa 0)) a) fun r1 t1 =>
    bindK (eAr .add 64 t1 (r1 (r c))) fun r2 t =>
    splitK b (.narrow t) fun r3 lo hi =>
    cchainK b m (fun i => Ms i.succ) (fun i => r3 (r2 (r1 (r (xa i.succ)))))
      (r3 (r2 (r1 (r f)))) hi fun r' os c' =>
      k (fun u => r' (r3 (r2 (r1 (r u))))) (r' lo :: os) c'

theorem cchainK_Q {ts : List JasminTy} (b : ℕ) (hb : b ≤ 64) : ∀ (m : ℕ) {Γ : JCtxt}
    (Ms : Fin m → ℕ) (_ : ∀ i, Ms i < 2 ^ 64) (xa : Fin m → Var Γ r64) (f c : Var Γ r64)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → List (Var Δ r64) → Var Δ r64 → MC Δ ts) (Z : ZVec Γ)
    (Q : ZVec ts → Prop)
    (_ : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (os : List (Var Δ r64)) (c' : Var Δ r64) (Z' : ZVec Δ),
      PresZ r Z Z' →
      os.map (fun v => hget Z' v) =
          (cchainZ b (valsF Z xa) (List.ofFn Ms) (hget Z f) (hget Z c)).1 →
        hget Z' c' = (cchainZ b (valsF Z xa) (List.ofFn Ms) (hget Z f) (hget Z c)).2 →
        Q ((k r os c').denoteZ Z')),
    Q ((cchainK b m Ms xa f c k).denoteZ Z)
  | 0, _, Ms, _, xa, f, c, k, Z, Q, hk => by
    refine hk _ _ _ _ (PresZ.id Z) ?_ ?_
    · simp [valsF, cchainZ]
    · simp [valsF, cchainZ]
  | m + 1, _, Ms, hM, xa, f, c, k, Z, Q, hk => by
    refine mulCK_Q _ (hM 0) _ _ _ _ fun r a Z1 h1 ha => ?_
    refine bindK_Q _ _ _ _ fun r1 t1 Z2 h2 ht1 => ?_
    refine bindK_Q _ _ _ _ fun r2 t Z3 h3 ht => ?_
    refine splitK_Q _ hb _ _ _ _ fun r3 lo hi Z4 h4 hlo hhi => ?_
    have hP : PresZ (fun u => r3 (r2 (r1 (r u)))) Z Z4 :=
      PresZ.comp (PresZ.comp (PresZ.comp h1 h2) h3) h4
    have htv : LV.z Z3 (.narrow t) = hget Z (xa 0) + mulC (Ms 0) (hget Z f) + hget Z c := by
      simp only [LV.z, ht, eAr_opZ, binZ, h2, ht1, ha, h1]
    refine cchainK_Q b hb m _ (fun i => hM i.succ) _ _ _ _ _ _ fun r' os c' Z5 h5 hos hc' =>
      hk _ _ _ _ (PresZ.comp hP h5) ?_ ?_
    · rw [List.map_cons, hos, h5, hlo, htv, valsF_succ, List.ofFn_succ]
      simp only [hP, cchainZ, hhi, htv]
      rw [valsF_map hP (fun i => xa i.succ)]
    · rw [hc', valsF_succ, List.ofFn_succ]
      simp only [hP, cchainZ, hhi, htv]
      rw [valsF_map hP (fun i => xa i.succ)]

/-- One load of `loadZ`: `acc + (x_0 << bits)` when `bits < 8` and a limb remains. -/
def loadK {ts : List JasminTy} (b bits : ℕ) : (m : ℕ) → {Γ : JCtxt} → Var Γ r64 →
    (Fin m → Var Γ r64) →
    (∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → Var Δ r64 → ℕ → (m' : ℕ) → (Fin m' → Var Δ r64) → MC Δ ts) →
    MC Γ ts
  | 0, _, acc, xa, k => k (fun u => u) acc bits 0 xa
  | m + 1, _, acc, xa, k =>
    if bits < 8 then
      bindK (eShl 64 bits (xa 0)) fun r1 s =>
      bindK (eAr .add 64 (r1 acc) s) fun r2 a =>
      k (fun u => r2 (r1 u)) a (bits + b) m (fun i => r2 (r1 (xa i.succ)))
    else k (fun u => u) acc bits (m + 1) xa

theorem loadK_Q {ts : List JasminTy} (b bits : ℕ) : ∀ (m : ℕ) {Γ : JCtxt} (acc : Var Γ r64)
    (xa : Fin m → Var Γ r64)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → Var Δ r64 → ℕ → (m' : ℕ) → (Fin m' → Var Δ r64) →
      MC Δ ts) (Z : ZVec Γ) (Q : ZVec ts → Prop)
    (_ : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (a : Var Δ r64) (bits' m' : ℕ)
      (xa' : Fin m' → Var Δ r64) (Z' : ZVec Δ), PresZ r Z Z' →
      hget Z' a = (loadZ b bits (hget Z acc) (valsF Z xa)).1 →
      bits' = (loadZ b bits (hget Z acc) (valsF Z xa)).2.1 →
      valsF Z' xa' = (loadZ b bits (hget Z acc) (valsF Z xa)).2.2 →
      Q ((k r a bits' m' xa').denoteZ Z')),
    Q ((loadK b bits m acc xa k).denoteZ Z)
  | 0, _, acc, xa, k, Z, Q, hk => hk _ _ _ _ _ _ (PresZ.id Z) rfl rfl (by simp [valsF, loadZ])
  | m + 1, _, acc, xa, k, Z, Q, hk => by
    unfold loadK
    split_ifs with h
    · refine bindK_Q _ _ _ _ fun r1 s Z1 h1 hs => ?_
      refine bindK_Q _ _ _ _ fun r2 a Z2 h2 ha => hk _ _ _ _ _ _ (PresZ.comp h1 h2) ?_ ?_ ?_
      · rw [ha, valsF_succ]
        simp only [eAr_opZ, binZ, hs, eShl_opZ, h1, loadZ, h, ite_true]
      · simp [valsF_succ, loadZ, h]
      · rw [valsF_succ, valsF_map (PresZ.comp h1 h2) (fun i => xa i.succ)]
        simp [loadZ, h]
    · refine hk _ _ _ _ _ _ (PresZ.id Z) ?_ ?_ ?_ <;> simp [valsF_succ, loadZ, h]

/-- The `N` bytes of `packZ` as `castW 64 8` of the low byte of the buffer. -/
def packK {ts : List JasminTy} (b : ℕ) : (N : ℕ) → {Γ : JCtxt} → Var Γ r64 → ℕ → (m : ℕ) →
    (Fin m → Var Γ r64) → (∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → List (Var Δ r8) → MC Δ ts) → MC Γ ts
  | 0, _, _, _, _, _, k => k (fun u => u) []
  | N + 1, _, acc, bits, m, xa, k =>
    loadK b bits m acc xa fun r a bits' m' xa' =>
    splitK 8 (.narrow a) fun r1 lo hi =>
    bindK (eCast 64 8 lo) fun r2 y =>
    packK b N (r2 hi) (bits' - 8) m' (fun i => r2 (r1 (xa' i))) fun r' ys =>
      k (fun u => r' (r2 (r1 (r u)))) (r' y :: ys)

theorem packK_Q {ts : List JasminTy} (b : ℕ) : ∀ (N : ℕ) {Γ : JCtxt} (acc : Var Γ r64)
    (bits m : ℕ) (xa : Fin m → Var Γ r64)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → List (Var Δ r8) → MC Δ ts) (Z : ZVec Γ)
    (Q : ZVec ts → Prop)
    (_ : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (ys : List (Var Δ r8)) (Z' : ZVec Δ), PresZ r Z Z' →
      ys.map (fun v => hget Z' v) = packZ b N (hget Z acc) bits (valsF Z xa) →
      Q ((k r ys).denoteZ Z')),
    Q ((packK b N acc bits m xa k).denoteZ Z)
  | 0, _, _, _, _, _, k, Z, Q, hk => hk _ _ _ (PresZ.id Z) rfl
  | N + 1, _, acc, bits, m, xa, k, Z, Q, hk => by
    refine loadK_Q b bits m acc xa _ Z Q fun r a bits' m' xa' Z1 h1 ha hb' hxa => ?_
    refine splitK_Q _ (by norm_num) _ _ _ _ fun r1 lo hi Z2 h2 hlo hhi => ?_
    refine bindK_Q _ _ _ _ fun r2 y Z3 h3 hy => ?_
    refine packK_Q b N _ _ _ _ _ _ _ fun r' ys Z4 h4 hys =>
      hk _ _ _ (PresZ.comp (PresZ.comp (PresZ.comp h1 h2) h3) h4) ?_
    rw [List.map_cons, hys, h4, hy, eCast_opZ, hlo, h3, hhi,
      valsF_map (PresZ.comp h2 h3) xa', hxa, hb']
    simp only [LV.z, ha, packZ]

/-- The byte loader of `ldZ`: `acc + (castW 8 64 y_0 << bits)` while bytes remain and
    `all` or `bits < b`. -/
def ldK {ts : List JasminTy} (b : ℕ) (all : Bool) : (m : ℕ) → {Γ : JCtxt} → Var Γ r64 → ℕ →
    (Fin m → Var Γ r8) →
    (∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → Var Δ r64 → ℕ → (m' : ℕ) → (Fin m' → Var Δ r8) → MC Δ ts) →
    MC Γ ts
  | 0, _, acc, bits, ya, k => k (fun u => u) acc bits 0 ya
  | m + 1, _, acc, bits, ya, k =>
    if all || decide (bits < b) then
      bindK (eCast 8 64 (ya 0)) fun r1 y =>
      bindK (eShl 64 bits y) fun r2 s =>
      bindK (eAr .add 64 (r2 (r1 acc)) s) fun r3 a =>
      ldK b all m a (bits + 8) (fun i => r3 (r2 (r1 (ya i.succ)))) fun r' a' bits' m' ya' =>
        k (fun u => r' (r3 (r2 (r1 u)))) a' bits' m' ya'
    else k (fun u => u) acc bits (m + 1) ya

theorem ldK_Q {ts : List JasminTy} (b : ℕ) (all : Bool) : ∀ (m : ℕ) {Γ : JCtxt}
    (acc : Var Γ r64) (bits : ℕ) (ya : Fin m → Var Γ r8)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → Var Δ r64 → ℕ → (m' : ℕ) → (Fin m' → Var Δ r8) →
      MC Δ ts) (Z : ZVec Γ) (Q : ZVec ts → Prop)
    (_ : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (a : Var Δ r64) (bits' m' : ℕ)
      (ya' : Fin m' → Var Δ r8) (Z' : ZVec Δ), PresZ r Z Z' →
      hget Z' a = (ldZ b all (hget Z acc) bits (valsF Z ya)).1 →
      bits' = (ldZ b all (hget Z acc) bits (valsF Z ya)).2.1 →
      valsF Z' ya' = (ldZ b all (hget Z acc) bits (valsF Z ya)).2.2 →
      Q ((k r a bits' m' ya').denoteZ Z')),
    Q ((ldK b all m acc bits ya k).denoteZ Z)
  | 0, _, acc, bits, ya, k, Z, Q, hk =>
    hk _ _ _ _ _ _ (PresZ.id Z) (by simp [valsF, ldZ]) (by simp [valsF, ldZ])
      (by simp [valsF, ldZ])
  | m + 1, _, acc, bits, ya, k, Z, Q, hk => by
    unfold ldK
    split_ifs with h
    · refine bindK_Q _ _ _ _ fun r1 y Z1 h1 hy => ?_
      refine bindK_Q _ _ _ _ fun r2 s Z2 h2 hs => ?_
      refine bindK_Q _ _ _ _ fun r3 a Z3 h3 ha => ?_
      have hP : PresZ (fun u => r3 (r2 (r1 u))) Z Z3 := PresZ.comp (PresZ.comp h1 h2) h3
      have hav : hget Z3 a = hget Z acc + hget Z (ya 0) * 2 ^ bits := by
        simp only [ha, eAr_opZ, binZ, hs, eShl_opZ, hy, eCast_opZ, h1, h2]
      refine ldK_Q b all m _ _ _ _ _ _ fun r' a' bits' m' ya' Z4 h4 ha' hb' hya' =>
        hk _ _ _ _ _ _ (PresZ.comp hP h4) ?_ ?_ ?_
      · rw [ha', valsF_succ, valsF_map hP (fun i => ya i.succ), hav]
        simp only [ldZ, h, ite_true]
      · rw [hb', valsF_succ, valsF_map hP (fun i => ya i.succ), hav]
        simp only [ldZ, h, ite_true]
      · rw [hya', valsF_succ, valsF_map hP (fun i => ya i.succ), hav]
        simp only [ldZ, h, ite_true]
    · refine hk _ _ _ _ _ _ (PresZ.id Z) ?_ ?_ ?_ <;> rw [valsF_succ] <;> simp [ldZ, h]

/-- The `n` limbs of `unpackZ`. -/
def unpackK {ts : List JasminTy} (b : ℕ) : (n : ℕ) → {Γ : JCtxt} → Var Γ r64 → ℕ → (m : ℕ) →
    (Fin m → Var Γ r8) → (∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → List (Var Δ r64) → MC Δ ts) → MC Γ ts
  | 0, _, _, _, _, _, k => k (fun u => u) []
  | 1, _, acc, bits, m, ya, k => ldK b true m acc bits ya fun r a _ _ _ => k r [a]
  | n + 2, _, acc, bits, m, ya, k =>
    ldK b false m acc bits ya fun r a bits' m' ya' =>
    splitK b (.narrow a) fun r1 lo hi =>
    unpackK b (n + 1) hi (bits' - b) m' (fun i => r1 (ya' i)) fun r' os =>
      k (fun u => r' (r1 (r u))) (r' lo :: os)

theorem unpackK_Q {ts : List JasminTy} (b : ℕ) (hb : b ≤ 64) : ∀ (n : ℕ) {Γ : JCtxt}
    (acc : Var Γ r64) (bits m : ℕ) (ya : Fin m → Var Γ r8)
    (k : ∀ {Δ : JCtxt}, Ctxt.Hom Γ Δ → List (Var Δ r64) → MC Δ ts) (Z : ZVec Γ)
    (Q : ZVec ts → Prop)
    (_ : ∀ {Δ : JCtxt} (r : Ctxt.Hom Γ Δ) (os : List (Var Δ r64)) (Z' : ZVec Δ), PresZ r Z Z' →
      os.map (fun v => hget Z' v) = unpackZ b n (hget Z acc) bits (valsF Z ya) →
      Q ((k r os).denoteZ Z')),
    Q ((unpackK b n acc bits m ya k).denoteZ Z)
  | 0, _, _, _, _, _, k, Z, Q, hk => hk _ _ _ (PresZ.id Z) rfl
  | 1, _, acc, bits, m, ya, k, Z, Q, hk =>
    ldK_Q b true m acc bits ya _ Z Q fun r a _ _ _ Z1 h1 ha _ _ =>
      hk _ _ _ h1 (by simp [unpackZ, ha])
  | n + 2, _, acc, bits, m, ya, k, Z, Q, hk => by
    refine ldK_Q b false m acc bits ya _ Z Q fun r a bits' m' ya' Z1 h1 ha hb' hya => ?_
    refine splitK_Q _ hb _ _ _ _ fun r1 lo hi Z2 h2 hlo hhi => ?_
    refine unpackK_Q b hb (n + 1) _ _ _ _ _ _ _ fun r' os Z3 h3 hos =>
      hk _ _ _ (PresZ.comp (PresZ.comp h1 h2) h3) ?_
    rw [List.map_cons, hos, h3, hlo, hhi, valsF_map h2 ya', hya, hb']
    simp only [LV.z, ha, unpackZ]

/-! ## 6. Contexts, inputs and outputs -/

/-- The context of `m` bytes. -/
abbrev BCtx (m : ℕ) : JCtxt := List.replicate m r8

/-- The context of `m` variables of type `t`. -/
abbrev TCtx (t : JasminTy) (m : ℕ) : JCtxt := List.replicate m t

/-- The variable at position `i` of a context of `m` variables of type `t`. -/
def rvT (t : JasminTy) : (m i : ℕ) → i < m → Var (TCtx t m) t
  | _ + 1, 0, _ => .here
  | m + 1, i + 1, h => .there (rvT t m i (by omega))

theorem hget_rvT (t : JasminTy) : ∀ (m i : ℕ) (h : i < m) (Z : ZVec (TCtx t m)),
    hget Z (rvT t m i h) = hvGetZ Z i
  | _ + 1, 0, _, .cons _ _ => rfl
  | m + 1, i + 1, h, .cons _ Z => hget_rvT t m i (by omega) Z

theorem hget_rv : ∀ (m i : ℕ) (h : i < m) (Z : ZVec (RCtx m)), hget Z (rv m i h) = hvGetZ Z i
  | _ + 1, 0, _, .cons _ _ => rfl
  | m + 1, i + 1, h, .cons _ Z => hget_rv m i (by omega) Z

/-- The readings at positions `off, …, off + len - 1` of an integer vector. -/
def rdL {l : List JasminTy} (Z : ZVec l) (off len : ℕ) : List ℤ :=
  List.ofFn fun i : Fin len => hvGetZ Z (off + i)

/-- Byte `i` of a one-operand byte context. -/
def b1Var (N : ℕ) (i : Fin N) : Var (BCtx N) r8 := rvT r8 N i i.isLt

/-- Byte `i` of the first operand of a two-operand byte context. -/
def b2aVar (N : ℕ) (i : Fin N) : Var (BCtx (2 * N)) r8 :=
  rvT r8 (2 * N) i (by have := i.isLt; omega)

/-- Byte `i` of the second operand of a two-operand byte context. -/
def b2bVar (N : ℕ) (i : Fin N) : Var (BCtx (2 * N)) r8 :=
  rvT r8 (2 * N) (N + i) (by have := i.isLt; omega)

theorem valsF_sVar (n : ℕ) (Z : ZVec (RCtx n)) : valsF Z (sVar n) = rdL Z 0 n := by
  simp [valsF, rdL, sVar, hget_rv]

theorem valsF_aVar (n : ℕ) (Z : ZVec (RCtx (2 * n))) : valsF Z (aVar n) = rdL Z 0 n := by
  simp [valsF, rdL, aVar, hget_rv]

theorem valsF_bVar (n : ℕ) (Z : ZVec (RCtx (2 * n))) : valsF Z (bVar n) = rdL Z n n := by
  simp [valsF, rdL, bVar, hget_rv]

theorem valsF_b1Var (N : ℕ) (Z : ZVec (BCtx N)) : valsF Z (b1Var N) = rdL Z 0 N := by
  simp [valsF, rdL, b1Var, hget_rvT]

theorem valsF_b2aVar (N : ℕ) (Z : ZVec (BCtx (2 * N))) : valsF Z (b2aVar N) = rdL Z 0 N := by
  simp [valsF, rdL, b2aVar, hget_rvT]

theorem valsF_b2bVar (N : ℕ) (Z : ZVec (BCtx (2 * N))) : valsF Z (b2bVar N) = rdL Z N N := by
  simp [valsF, rdL, b2bVar, hget_rvT]

/-- The output variables `f` as a return vector of type `t`. -/
def hvOfFnT {Δ : JCtxt} (t : JasminTy) : (n : ℕ) → (Fin n → Var Δ t) →
    HVector (fun ty => Var Δ ty) (List.replicate n t)
  | 0, _ => .nil
  | n + 1, f => .cons (f 0) (hvOfFnT t n fun i => f i.succ)

theorem hvGetZ_hvOfFnT {Δ : JCtxt} (t : JasminTy) (Z : ZVec Δ) : ∀ (n : ℕ) (f : Fin n → Var Δ t)
    (j : ℕ) (h : j < n), hvGetZ (lookupZ (hvOfFnT t n f) Z) j = hget Z (f ⟨j, h⟩)
  | 0, _, j, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, 0, _ => rfl
  | n + 1, f, j + 1, h => hvGetZ_hvOfFnT t Z n (fun i => f i.succ) j (by omega)

/-- The readings of a return vector built from a list `l` of `m` variables are the values of
    the corresponding segment of `l`. -/
theorem rdL_lf {Δ : JCtxt} (t : JasminTy) (Z : ZVec Δ) (l : List (Var Δ t)) (d : Var Δ t)
    (m off len : ℕ) (hl : l.length = m) (h : off + len ≤ m) :
    rdL (lookupZ (hvOfFnT t m (lf l d m)) Z) off len =
      ((l.map fun v => hget Z v).drop off).take len := by
  apply List.ext_getElem (by simp [rdL]; omega)
  intro i h1 h2
  simp only [rdL, List.getElem_ofFn]
  have hlt : off + i < l.length := by simp [rdL] at h1; omega
  rw [hvGetZ_hvOfFnT t Z m _ _ (by omega)]
  simp [lf, List.getElem?_eq_getElem hlt]

theorem rdL_lf_all {Δ : JCtxt} (t : JasminTy) (Z : ZVec Δ) (l : List (Var Δ t)) (d : Var Δ t)
    (m : ℕ) (hl : l.length = m) :
    rdL (lookupZ (hvOfFnT t m (lf l d m)) Z) 0 m = l.map fun v => hget Z v := by
  rw [rdL_lf t Z l d m 0 m hl (by omega), List.drop_zero, List.take_of_length_le (by simp [hl])]

theorem rdL_hvOfFn {Δ : JCtxt} (Z : ZVec Δ) (n : ℕ) (f : Fin n → Var Δ r64) :
    rdL (lookupZ (hvOfFn n f) Z) 0 n = List.ofFn fun j => hget Z (f j) := by
  simp [rdL, hvGetZ_lookupZ]

theorem cchainZ_length (b : ℕ) : ∀ (xs : List ℤ) (Ms : List ℕ) (f c : ℤ),
    xs.length = Ms.length → (cchainZ b xs Ms f c).1.length = xs.length
  | [], _, _, _, _ => by cases ‹List ℕ› <;> rfl
  | _ :: _, [], _, _, h => by simp at h
  | _ :: xs, _ :: Ms, f, c, h => by
    simp [cchainZ, cchainZ_length b xs Ms f _ (by simpa using h)]

theorem unpackZ_length' (b : ℕ) (n : ℕ) (acc : ℤ) (bits : ℕ) (rest : List ℤ) :
    (unpackZ b n acc bits rest).length = n := by
  cases n with
  | zero => rfl
  | succ n => exact unpackZ_length b n acc bits rest

theorem ofFn_getD (l : List ℕ) (m : ℕ) (h : l.length = m) :
    List.ofFn (fun i : Fin m => l.getD i 0) = l := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-! ## 7. The blocks and their integer semantics -/

section Blocks

variable (P : UnsatParams)

/-- The sum `Σ c·2^e` on `ℕ`. -/
def cSumN : ℕ := (P.cTerms.map fun ce => ce.1 * 2 ^ ce.2).sum

/-- The prime `2^k - Σ c·2^e` computed on `ℕ`. -/
def pN : ℕ := 2 ^ P.k - cSumN P

theorem pN_cast (h : cSumN P ≤ 2 ^ P.k) : (pN P : ℤ) = P.pZ := by
  unfold pN UnsatParams.pZ UnsatParams.cSum
  rw [Nat.cast_sub h, cSumN, Nat.cast_list_sum, List.map_map]
  push_cast
  rfl

/-- Digit `i` of `p` in base `2^b`. -/
def pD (i : Fin P.n) : ℕ := (digits P.b P.n (pN P)).getD i 0

/-- Digit `i` of `2^(b·n) - p` in base `2^b`. -/
def mD (i : Fin P.n) : ℕ := (digits P.b P.n (2 ^ (P.b * P.n) - pN P)).getD i 0

/-- Limb `i` of the balance `2p` added before a subtraction: twice digit `i` of `p`. -/
def balD (i : Fin P.n) : ℕ := 2 * pD P i

theorem ofFn_pD : List.ofFn (pD P) = digits P.b P.n (pN P) :=
  ofFn_getD _ _ (digits_length _ _ _)

theorem ofFn_mD : List.ofFn (mD P) = digits P.b P.n (2 ^ (P.b * P.n) - pN P) :=
  ofFn_getD _ _ (digits_length _ _ _)

/-- **The `add` block**: the limbwise sum of the operands `a` and `b`, no carry. -/
def addBlk : MC (RCtx (2 * P.n)) (RCtx P.n) :=
  bindK (eK 64 0) fun r z =>
  addLK P.n (fun i => r (aVar P.n i)) (fun i => r (bVar P.n i)) fun r' os =>
  .ret (hvOfFnT r64 P.n (lf os (r' z) P.n))

/-- **The `sub` block**: the limbwise `a + 2p - b`, with the limbs `balD` of `2p`. -/
def subBlk : MC (RCtx (2 * P.n)) (RCtx P.n) :=
  bindK (eK 64 0) fun r z =>
  subLK P.n (balD P) (fun i => r (aVar P.n i)) (fun i => r (bVar P.n i)) fun r' os =>
  .ret (hvOfFnT r64 P.n (lf os (r' z) P.n))

/-- **The `carry` block**: the carry schedule `sched` on 64-bit limbs. -/
def carryBlk (sched : List ℕ) : MC (RCtx P.n) (RCtx P.n) :=
  chainK P sched (fun j => .narrow (sVar P.n j)) fun r st =>
  finK (List.finRange P.n) st (fun j => r (sVar P.n j)) fun _ out => .ret (hvOfFn P.n out)

/-- **The `freeze` block**: the canonical reduction of `freezeZ`. -/
def freezeBlk : MC (RCtx P.n) (RCtx P.n) :=
  bindK (eK 64 0) fun r0 z =>
  bindK (eK 64 1) fun r1 o =>
  cchainK P.b P.n (mD P) (fun i => r1 (r0 (sVar P.n i))) o (r1 z) fun r2 ds c1 =>
  bindK (eAr .add 64 c1 (r2 o)) fun r3 c1p =>
  bindK (eAr .and 64 c1p (r3 (r2 o))) fun r4 fl =>
  cchainK P.b P.n (pD P) (fun i => r4 (r3 (lf ds (r2 (r1 z)) P.n i))) fl (r4 (r3 (r2 (r1 z))))
    fun r5 es _ => .ret (hvOfFnT r64 P.n (lf es (r5 (r4 (r3 (r2 (r1 z))))) P.n))

end Blocks

/-- **The `toBytes` block**: the `N` little-endian bytes of `n` canonical limbs of width
    `b`. -/
def toBytesBlk (b n N : ℕ) : MC (RCtx n) (BCtx N) :=
  bindK (eK 8 0) fun r0 d =>
  bindK (eK 64 0) fun r1 z =>
  packK b N z 0 n (fun i => r1 (r0 (sVar n i))) fun r ys =>
  .ret (hvOfFnT r8 N (lf ys (r (r1 d)) N))

/-- **The `fromBytes` block**: the `n` limbs of width `b` of `N` little-endian bytes. -/
def fromBytesBlk (b n N : ℕ) : MC (BCtx N) (RCtx n) :=
  bindK (eK 64 0) fun r z =>
  unpackK b n z 0 N (fun i => r (b1Var N i)) fun r' os =>
  .ret (hvOfFnT r64 n (lf os (r' z) n))

/-- **The two-operand `fromBytes` block**: the limbs of both operands of a binary
    operation, operand `a` from bytes `0 … N-1` and operand `b` from bytes `N … 2N-1`. -/
def fromBytes2Blk (b n N : ℕ) : MC (BCtx (2 * N)) (RCtx (2 * n)) :=
  bindK (eK 64 0) fun r z =>
  unpackK b n z 0 N (fun i => r (b2aVar N i)) fun r1 os1 =>
  unpackK b n (r1 z) 0 N (fun i => r1 (r (b2bVar N i))) fun r2 os2 =>
  .ret (hvOfFnT r64 (2 * n) (lf (os1.map (fun v => r2 v) ++ os2) (r2 (r1 z)) (2 * n)))

/-- The integer semantics of `addBlk` is the limbwise sum; no bounds. -/
theorem addBlk_denoteZ (P : UnsatParams) (Z : ZVec (RCtx (2 * P.n))) :
    rdL ((addBlk P).denoteZ Z) 0 P.n =
      List.ofFn fun i : Fin P.n => hvGetZ Z i + hvGetZ Z (P.n + i) := by
  refine bindK_Q _ _ _ (fun z => rdL z 0 P.n = _) fun r c Z1 h1 _ => ?_
  refine addLK_Q P.n _ _ _ _ (fun z => rdL z 0 P.n = _) fun r' os Z2 _ hos => ?_
  have hl : os.length = P.n := by simpa using congrArg List.length hos
  show rdL (lookupZ _ Z2) 0 P.n = _
  rw [rdL_lf_all _ _ _ _ _ hl, hos]
  simp only [h1, aVar, bVar, hget_rv]

/-- The integer semantics of `subBlk` is the limbwise `a + 2p - b`; no bounds. -/
theorem subBlk_denoteZ (P : UnsatParams) (hbal : ∀ i, balD P i < 2 ^ 64)
    (Z : ZVec (RCtx (2 * P.n))) :
    rdL ((subBlk P).denoteZ Z) 0 P.n =
      List.ofFn fun i : Fin P.n => hvGetZ Z i + (balD P i : ℤ) - hvGetZ Z (P.n + i) := by
  refine bindK_Q _ _ _ (fun z => rdL z 0 P.n = _) fun r c Z1 h1 _ => ?_
  refine subLK_Q P.n _ hbal _ _ _ _ (fun z => rdL z 0 P.n = _) fun r' os Z2 _ hos => ?_
  have hl : os.length = P.n := by simpa using congrArg List.length hos
  show rdL (lookupZ _ Z2) 0 P.n = _
  rw [rdL_lf_all _ _ _ _ _ hl, hos]
  simp only [h1, aVar, bVar, hget_rv]

/-- The integer semantics of `carryBlk` is the carry schedule; no bounds. -/
theorem carryBlk_denoteZ (P : UnsatParams) (sched : List ℕ) (hb : P.b ≤ 64)
    (hW : ∀ t ∈ P.wrapTerms, t.2 < 2 ^ 64) (Z : ZVec (RCtx P.n)) :
    rdL ((carryBlk P sched).denoteZ Z) 0 P.n =
      List.ofFn (P.carryChain sched fun i => hvGetZ Z i) := by
  refine chainK_Q P hb hW _ _ _ _ (fun z => rdL z 0 P.n = _) fun r st Z1 h1 hst => ?_
  refine finK_Q _ _ _ _ _ (fun z => rdL z 0 P.n = _) fun r' out Z2 _ ho => ?_
  show rdL (lookupZ (hvOfFn P.n out) Z2) 0 P.n = _
  rw [rdL_hvOfFn]
  congr 1
  funext j
  rw [congrFun ho j, updL_apply, ite_eq_left (List.mem_finRange j), congrFun hst j]
  simp only [LV.z, sVar, hget_rv]

/-- The integer semantics of `freezeBlk` is `freezeZ` on the digits of `2^(b·n) - p` and of
    `p`; no bounds. -/
theorem freezeBlk_denoteZ (P : UnsatParams) (hb : P.b ≤ 64) (hm : ∀ i, mD P i < 2 ^ 64)
    (hp : ∀ i, pD P i < 2 ^ 64) (Z : ZVec (RCtx P.n)) :
    rdL ((freezeBlk P).denoteZ Z) 0 P.n =
      freezeZ P.b (List.ofFn (mD P)) (List.ofFn (pD P)) (rdL Z 0 P.n) := by
  refine bindK_Q _ _ _ (fun z => rdL z 0 P.n = _) fun r0 z Z1 h1 hz => ?_
  refine bindK_Q _ _ _ (fun z => rdL z 0 P.n = _) fun r1 o Z2 h2 ho => ?_
  refine cchainK_Q P.b hb P.n _ hm _ _ _ _ _ (fun z => rdL z 0 P.n = _)
    fun r2 ds c1 Z3 h3 hds hc1 => ?_
  refine bindK_Q _ _ _ (fun z => rdL z 0 P.n = _) fun r3 c1p Z4 h4 hc1p => ?_
  refine bindK_Q _ _ _ (fun z => rdL z 0 P.n = _) fun r4 fl Z5 h5 hfl => ?_
  refine cchainK_Q P.b hb P.n _ hp _ _ _ _ _ (fun z => rdL z 0 P.n = _)
    fun r5 es c2 Z6 h6 hes _ => ?_
  have hxs : valsF Z2 (fun i => r1 (r0 (sVar P.n i))) = rdL Z 0 P.n := by
    rw [valsF_map (PresZ.comp h1 h2) (sVar P.n), valsF_sVar]
  have hov : hget Z2 o = 1 := by rw [ho, eK_opZ]; rfl
  have hzv : hget Z2 (r1 z) = 0 := by rw [h2, hz, eK_opZ]; rfl
  have hdl : ds.length = P.n := by
    have := congrArg List.length hds
    rw [List.length_map, cchainZ_length _ _ _ _ _ (by simp [valsF])] at this
    simpa [valsF] using this
  have hel : es.length = P.n := by
    have := congrArg List.length hes
    rw [List.length_map, cchainZ_length _ _ _ _ _ (by simp [valsF])] at this
    simpa [valsF] using this
  show rdL (lookupZ _ Z6) 0 P.n = _
  rw [rdL_lf_all _ _ _ _ _ hel, hes, valsF_map (PresZ.comp h4 h5) (lf ds (r2 (r1 z)) P.n),
    valsF_lf _ _ _ _ hdl, hds, hxs, hov, hzv]
  have hflv : hget Z5 fl = andZ (hget Z3 c1 + 1) 1 := by
    rw [hfl]
    simp only [eAr_opZ, binZ, hc1p, h4, h3, hov]
  rw [hflv, hc1, hxs, hov, hzv, h5, h4]
  simp only [h3, hzv]
  rfl

/-- The integer semantics of `toBytesBlk` is `packZ` from an empty buffer; no bounds. -/
theorem toBytesBlk_denoteZ (b n N : ℕ) (Z : ZVec (RCtx n)) :
    rdL ((toBytesBlk b n N).denoteZ Z) 0 N = packZ b N 0 0 (rdL Z 0 n) := by
  refine bindK_Q _ _ _ (fun z => rdL z 0 N = _) fun r0 d Z1 h1 _ => ?_
  refine bindK_Q _ _ _ (fun z => rdL z 0 N = _) fun r1 z Z2 h2 hz => ?_
  refine packK_Q b N _ _ _ _ _ _ (fun z => rdL z 0 N = _) fun r ys Z3 _ hys => ?_
  have hl : ys.length = N := by simpa [packZ_length] using congrArg List.length hys
  show rdL (lookupZ _ Z3) 0 N = _
  rw [rdL_lf_all _ _ _ _ _ hl, hys, hz, eK_opZ,
    valsF_map (PresZ.comp h1 h2) (sVar n), valsF_sVar]
  rfl

/-- The integer semantics of `fromBytesBlk` is `unpackZ` from an empty buffer; no bounds. -/
theorem fromBytesBlk_denoteZ (b n N : ℕ) (hb : b ≤ 64) (Z : ZVec (BCtx N)) :
    rdL ((fromBytesBlk b n N).denoteZ Z) 0 n = unpackZ b n 0 0 (rdL Z 0 N) := by
  refine bindK_Q _ _ _ (fun z => rdL z 0 n = _) fun r z Z1 h1 hz => ?_
  refine unpackK_Q b hb n _ _ _ _ _ _ (fun z => rdL z 0 n = _) fun r' os Z2 _ hos => ?_
  have hl : os.length = n := by simpa [unpackZ_length'] using congrArg List.length hos
  show rdL (lookupZ _ Z2) 0 n = _
  rw [rdL_lf_all _ _ _ _ _ hl, hos, hz, eK_opZ, valsF_map h1 (b1Var N), valsF_b1Var]
  rfl

/-- The integer semantics of `fromBytes2Blk`: the first `n` output limbs are `unpackZ` of the
    bytes of `a`, the next `n` that of the bytes of `b`; no bounds. -/
theorem fromBytes2Blk_denoteZ (b n N : ℕ) (hb : b ≤ 64) (Z : ZVec (BCtx (2 * N))) :
    rdL ((fromBytes2Blk b n N).denoteZ Z) 0 n = unpackZ b n 0 0 (rdL Z 0 N) ∧
      rdL ((fromBytes2Blk b n N).denoteZ Z) n n = unpackZ b n 0 0 (rdL Z N N) := by
  refine bindK_Q _ _ _ (fun z => rdL z 0 n = _ ∧ rdL z n n = _) fun r z Z1 h1 hz => ?_
  refine unpackK_Q b hb n _ _ _ _ _ _ (fun z => rdL z 0 n = _ ∧ rdL z n n = _)
    fun r1 os1 Z2 h2 hos1 => ?_
  refine unpackK_Q b hb n _ _ _ _ _ _ (fun z => rdL z 0 n = _ ∧ rdL z n n = _)
    fun r2 os2 Z3 h3 hos2 => ?_
  have hl1 : os1.length = n := by simpa [unpackZ_length'] using congrArg List.length hos1
  have hl2 : os2.length = n := by simpa [unpackZ_length'] using congrArg List.length hos2
  have hl : (os1.map (fun v => r2 v) ++ os2).length = 2 * n := by simp [hl1, hl2]; omega
  have hm1 : (os1.map (fun v => r2 v)).map (fun v => hget Z3 v) = os1.map (fun v => hget Z2 v) := by
    simp only [List.map_map, Function.comp_def, h3]
  show rdL (lookupZ _ Z3) 0 n = _ ∧ rdL (lookupZ _ Z3) n n = _
  rw [rdL_lf _ _ _ _ _ _ _ hl (by omega), rdL_lf _ _ _ _ _ _ _ hl (by omega), List.map_append,
    hm1, List.drop_zero, List.take_left' (by simp [hl1]), List.drop_left' (by simp [hl1]),
    List.take_of_length_le (by simp [hl2]), hos1, hos2, h2, hz, eK_opZ,
    valsF_map (PresZ.comp h1 h2) (b2bVar N), valsF_map h1 (b2aVar N), valsF_b2aVar, valsF_b2bVar]
  exact ⟨rfl, rfl⟩

/-! ## 8. Interval vectors and readings -/

/-- The interval vector of a context of `m` variables of type `t`: entry `i` of `l`, the
    interval `[0, 0]` past its end. -/
def ivVec (t : JasminTy) : List Iv → (m : ℕ) → HVector (fun _ => Iv) (TCtx t m)
  | _, 0 => .nil
  | [], m + 1 => .cons (0, 0) (ivVec t [] m)
  | i :: l, m + 1 => .cons i (ivVec t l m)

theorem ivVec_succ (t : JasminTy) (l : List Iv) (m : ℕ) :
    ivVec t l (m + 1) = .cons (l.headD (0, 0)) (ivVec t l.tail m) := by
  cases l <;> rfl

theorem valsIn_ivVec (w : ℕ) : ∀ (m : ℕ) (l : List Iv) (V : Valuation (TCtx (.reg w) m)),
    ValsIn false (ivVec (.reg w) l m) V ↔
      ∀ i < m, (l.getD i (0, 0)).1 ≤ hvGetZ (zvals false V) i ∧
        hvGetZ (zvals false V) i ≤ (l.getD i (0, 0)).2
  | 0, _, .nil => ⟨fun _ _ hi => absurd hi (Nat.not_lt_zero _), fun _ => trivial⟩
  | m + 1, l, .cons x V => by
    have e : ValsIn false (ivVec (.reg w) l (m + 1)) (HVector.cons x V) ↔
        ivZ false (.reg w) (l.headD (0, 0)) x ∧ ValsIn false (ivVec (.reg w) l.tail m) V := by
      rw [ivVec_succ]; exact Iff.rfl
    have hg : ∀ i, l.tail.getD i (0, 0) = l.getD (i + 1) (0, 0) := by
      intro i; cases l <;> simp
    rw [e, valsIn_ivVec w m l.tail V]
    constructor
    · rintro ⟨h0, h⟩ i hi
      cases i with
      | zero => cases l <;> exact h0
      | succ i => rw [← hg]; exact h i (by omega)
    · intro h
      refine ⟨by cases l <;> exact h 0 (by omega), fun i hi => ?_⟩
      rw [hg]; exact h (i + 1) (by omega)

/-- Every interval of `l` lies in the interval of `l'` at the same position, for the first
    `m` positions. -/
def ivsLe (l l' : List Iv) (m : ℕ) : Bool :=
  (List.range m).all fun i =>
    decide ((l'.getD i (0, 0)).1 ≤ (l.getD i (0, 0)).1 ∧ (l.getD i (0, 0)).2 ≤ (l'.getD i (0, 0)).2)

theorem valsIn_mono {w m : ℕ} {l l' : List Iv} {V : Valuation (TCtx (.reg w) m)}
    (hV : ValsIn false (ivVec (.reg w) l m) V) (h : ivsLe l l' m = true) :
    ValsIn false (ivVec (.reg w) l' m) V := by
  rw [valsIn_ivVec] at hV ⊢
  intro i hi
  have hle := List.all_eq_true.1 h i (List.mem_range.2 hi)
  simp only [decide_eq_true_eq] at hle
  have := hV i hi
  exact ⟨le_trans hle.1 this.1, le_trans this.2 hle.2⟩

theorem hvGetZ_zvals_nonneg : ∀ {l : List JasminTy} (V : HVector (fun t => ⟦t⟧) l) (i : ℕ),
    0 ≤ hvGetZ (zvals false V) i
  | [], .nil, _ => le_rfl
  | .reg _ :: _, .cons x _, 0 => by
    show 0 ≤ rd false x; simp [rd]
  | .stackArr _ _ :: _, .cons _ _, 0 => le_rfl
  | .inlineInt :: _, .cons _ _, 0 => le_rfl
  | .bool :: _, .cons _ _, 0 => le_rfl
  | _ :: _, .cons _ V, i + 1 => hvGetZ_zvals_nonneg V i

theorem rdL_nonneg {l : List JasminTy} (V : HVector (fun t => ⟦t⟧) l) (off len : ℕ) :
    ∀ x ∈ rdL (zvals false V) off len, 0 ≤ x := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact hvGetZ_zvals_nonneg V _

/-- The value of the limbwise sum of two limb functions. -/
theorem evalL_ofFn_add (b m : ℕ) (f g : Fin m → ℤ) :
    evalL b (List.ofFn fun i => f i + g i) = evalL b (List.ofFn f) + evalL b (List.ofFn g) := by
  simp only [evalL_ofFn, add_mul, Finset.sum_add_distrib]

theorem evalL_ofFn_sub (b m : ℕ) (f g : Fin m → ℤ) :
    evalL b (List.ofFn fun i => f i - g i) = evalL b (List.ofFn f) - evalL b (List.ofFn g) := by
  simp only [evalL_ofFn, sub_mul, Finset.sum_sub_distrib]

theorem evalL_rdL {l : List JasminTy} (P : UnsatParams) (Z : ZVec l) (off : ℕ) :
    evalL P.b (rdL Z off P.n) = P.evalZ fun i => hvGetZ Z (off + i) := by
  rw [evalZ_eq_evalL]; rfl

/-! ## 9. The template record -/

/-- The canonical limb intervals `[0, 2^b - 1]` of `n` limbs. -/
def canonIvs (P : UnsatParams) : List Iv := List.replicate P.n (0, 2 ^ P.b - 1)

/-- The byte intervals `[0, 255]` of `N` bytes. -/
def byteIvs (N : ℕ) : List Iv := List.replicate N (0, 255)

/-- **An unsaturated field representation template.** The parameters `P` of `UnsatZ`, the
    carry schedule `sched`, the byte length `nB`, the input byte intervals `byteIn`, and
    the loose and tight limb intervals. The discipline: `fromBytes` produces tight limbs,
    `add` and `sub` take tight limbs and produce loose limbs, `carry`, `carryMul` and
    `carrySquare` take loose limbs and produce tight limbs, `freeze` takes tight limbs and
    produces canonical limbs, `toBytes` takes canonical limbs. Each discipline step is a
    bounds certificate `boundsOkMR … = true` of its block; the other fields are decidable
    side conditions on the parameters. -/
structure FieldReprTemplate where
  /-- The representation parameters. -/
  P : UnsatParams
  /-- The carry schedule of `carry`, `carryMul` and `carrySquare`. -/
  sched : List ℕ
  /-- The length of the byte encoding. -/
  nB : ℕ
  /-- The intervals of the input bytes. -/
  byteIn : List Iv
  /-- The loose limb intervals. -/
  loose : List Iv
  /-- The tight limb intervals. -/
  tight : List Iv
  n_pos : 0 < P.n
  b_ge : 8 ≤ P.b
  wordOk : WordOk P
  placed : P.Placed
  cSum_le : cSumN P ≤ 2 ^ P.k
  p_pos : 0 < P.pZ
  p_lt : P.pZ < 2 ^ (P.b * P.n)
  p_bytes : P.pZ ≤ 2 ^ (8 * nB)
  bal_lt : ∀ i, balD P i < 2 ^ 64
  m_lt : ∀ i, mD P i < 2 ^ 64
  tight_lt : evalL P.b (List.ofFn fun i : Fin P.n => (tight.getD i (0, 0)).2) < 2 * P.pZ
  tight_loose : ivsLe tight loose P.n = true
  tight_loose2 : ivsLe (tight ++ tight) (loose ++ loose) (2 * P.n) = true
  fromBytes_ok : boundsOkMR false (ivVec r8 byteIn nB) (fromBytesBlk P.b P.n nB)
    (ivVec r64 tight P.n) = true
  fromBytes2_ok : boundsOkMR false (ivVec r8 (byteIn ++ byteIn) (2 * nB))
    (fromBytes2Blk P.b P.n nB) (ivVec r64 (tight ++ tight) (2 * P.n)) = true
  add_ok : boundsOkMR false (ivVec r64 (tight ++ tight) (2 * P.n)) (addBlk P)
    (ivVec r64 loose P.n) = true
  sub_ok : boundsOkMR false (ivVec r64 (tight ++ tight) (2 * P.n)) (subBlk P)
    (ivVec r64 loose P.n) = true
  carry_ok : boundsOkMR false (ivVec r64 loose P.n) (carryBlk P sched)
    (ivVec r64 tight P.n) = true
  mul_ok : boundsOkMR false (ivVec r64 (loose ++ loose) (2 * P.n)) (carryMulBlk P sched)
    (ivVec r64 tight P.n) = true
  sq_ok : boundsOkMR false (ivVec r64 loose P.n) (carrySquareBlk P sched)
    (ivVec r64 tight P.n) = true
  freeze_ok : boundsOkMR false (ivVec r64 tight P.n) (freezeBlk P)
    (ivVec r64 (canonIvs P) P.n) = true
  toBytes_ok : boundsOkMR false (ivVec r64 (canonIvs P) P.n) (toBytesBlk P.b P.n nB)
    (ivVec r8 (byteIvs nB) nB) = true

namespace FieldReprTemplate

variable (T : FieldReprTemplate)

/-- The value of a limb vector: its limbs at offset `off` in `ZMod p`. -/
def val {l : List JasminTy} (V : HVector (fun t => ⟦t⟧) l) (off : ℕ) : ZMod T.P.p :=
  (evalL T.P.b (rdL (zvals false V) off T.P.n) : ZMod T.P.p)

/-- A limb vector is good when its readings lie in the tight intervals. -/
def Good (V : Valuation (RCtx T.P.n)) : Prop := ValsIn false (ivVec r64 T.tight T.P.n) V

/-- The binary operations of the template. -/
inductive BinOp
  | add
  | sub
  | mul

/-- The integer operation of a binary operation. -/
def BinOp.evalZ : BinOp → ℤ → ℤ → ℤ
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y

/-- The body of a binary operation on tight limbs: `add` or `sub` followed by `carry`, or
    `carryMul`. -/
def bodyRun : BinOp → Valuation (RCtx (2 * T.P.n)) → Valuation (RCtx T.P.n)
  | .add, W => (carryBlk T.P T.sched).denote ((addBlk T.P).denote W)
  | .sub, W => (carryBlk T.P T.sched).denote ((subBlk T.P).denote W)
  | .mul, W => (carryMulBlk T.P T.sched).denote W

/-- **The byte-level run of a binary operation**: `fromBytes` of both operands, the body,
    `freeze`, `toBytes`. -/
def runBin (o : BinOp) (V : Valuation (BCtx (2 * T.nB))) : Valuation (BCtx T.nB) :=
  (toBytesBlk T.P.b T.P.n T.nB).denote
    ((freezeBlk T.P).denote (T.bodyRun o ((fromBytes2Blk T.P.b T.P.n T.nB).denote V)))

/-- **The byte-level run of the square**: `fromBytes`, `carrySquare`, `freeze`,
    `toBytes`. -/
def runSq (V : Valuation (BCtx T.nB)) : Valuation (BCtx T.nB) :=
  (toBytesBlk T.P.b T.P.n T.nB).denote ((freezeBlk T.P).denote
    ((carrySquareBlk T.P T.sched).denote ((fromBytesBlk T.P.b T.P.n T.nB).denote V)))

theorem pZ_nonneg : 0 ≤ T.P.pZ := le_of_lt T.p_pos

theorem p_cast : ((T.P.p : ℕ) : ℤ) = T.P.pZ := Int.toNat_of_nonneg T.pZ_nonneg

theorem evalL_pD : evalL T.P.b ((List.ofFn (pD T.P)).map (Nat.cast : ℕ → ℤ)) = T.P.pZ := by
  have hc := pN_cast T.P T.cSum_le
  rw [ofFn_pD, evalL_digits, Nat.mod_eq_of_lt, hc]
  have := T.p_lt
  rw [← hc] at this
  exact_mod_cast this

theorem evalL_mD : evalL T.P.b ((List.ofFn (mD T.P)).map (Nat.cast : ℕ → ℤ)) =
    2 ^ (T.P.b * T.P.n) - T.P.pZ := by
  have hc := pN_cast T.P T.cSum_le
  have hlt := T.p_lt
  have hpos := T.p_pos
  rw [← hc] at hlt hpos
  have hlt' : pN T.P < 2 ^ (T.P.b * T.P.n) := by exact_mod_cast hlt
  have hpos' : 0 < pN T.P := by exact_mod_cast hpos
  rw [ofFn_mD, evalL_digits, Nat.mod_eq_of_lt (by omega), Nat.cast_sub hlt'.le, ← hc]
  push_cast; ring

theorem pD_lt (i : Fin T.P.n) : pD T.P i < 2 ^ 64 := by
  have := T.bal_lt i; unfold balD at this; omega

/-- **`fromBytes` of two operands under its certificate.** The output limbs are tight and
    the value of each operand's limbs is the little-endian value of its bytes. -/
theorem fromBytes2_sem (V : Valuation (BCtx (2 * T.nB)))
    (hV : ValsIn false (ivVec r8 (T.byteIn ++ T.byteIn) (2 * T.nB)) V) :
    ValsIn false (ivVec r64 (T.tight ++ T.tight) (2 * T.P.n))
        ((fromBytes2Blk T.P.b T.P.n T.nB).denote V) ∧
      evalL T.P.b (rdL (zvals false ((fromBytes2Blk T.P.b T.P.n T.nB).denote V)) 0 T.P.n) =
        evalL 8 (rdL (zvals false V) 0 T.nB) ∧
      evalL T.P.b (rdL (zvals false ((fromBytes2Blk T.P.b T.P.n T.nB).denote V)) T.P.n T.P.n) =
        evalL 8 (rdL (zvals false V) T.nB T.nB) := by
  obtain ⟨e, hout⟩ := denoteMR_eq_denoteZ_of_boundsOk false _ _ _ T.fromBytes2_ok V hV
  obtain ⟨n', hn⟩ : ∃ n', T.P.n = n' + 1 := ⟨T.P.n - 1, by have := T.n_pos; omega⟩
  have hb : T.P.b ≤ 64 := T.wordOk.1
  obtain ⟨e1, e2⟩ := fromBytes2Blk_denoteZ T.P.b T.P.n T.nB hb (zvals false V)
  refine ⟨hout, ?_, ?_⟩
  · rw [e, e1, hn, unpackZ_spec _ _ _ _ _ le_rfl (rdL_nonneg V _ _)]; simp
  · rw [e, e2, hn, unpackZ_spec _ _ _ _ _ le_rfl (rdL_nonneg V _ _)]; simp

/-- **`fromBytes` of one operand under its certificate.** -/
theorem fromBytes_sem (V : Valuation (BCtx T.nB))
    (hV : ValsIn false (ivVec r8 T.byteIn T.nB) V) :
    ValsIn false (ivVec r64 T.tight T.P.n) ((fromBytesBlk T.P.b T.P.n T.nB).denote V) ∧
      evalL T.P.b (rdL (zvals false ((fromBytesBlk T.P.b T.P.n T.nB).denote V)) 0 T.P.n) =
        evalL 8 (rdL (zvals false V) 0 T.nB) := by
  obtain ⟨e, hout⟩ := denoteMR_eq_denoteZ_of_boundsOk false _ _ _ T.fromBytes_ok V hV
  obtain ⟨n', hn⟩ : ∃ n', T.P.n = n' + 1 := ⟨T.P.n - 1, by have := T.n_pos; omega⟩
  refine ⟨hout, ?_⟩
  rw [e, fromBytesBlk_denoteZ _ _ _ T.wordOk.1, hn,
    unpackZ_spec _ _ _ _ _ le_rfl (rdL_nonneg V _ _)]
  simp

/-- **`carry` under its certificate.** Loose limbs become tight limbs of the same value
    modulo `p`. -/
theorem carry_sem (W : Valuation (RCtx T.P.n)) (hW : ValsIn false (ivVec r64 T.loose T.P.n) W) :
    ValsIn false (ivVec r64 T.tight T.P.n) ((carryBlk T.P T.sched).denote W) ∧
      evalL T.P.b (rdL (zvals false ((carryBlk T.P T.sched).denote W)) 0 T.P.n) ≡
        evalL T.P.b (rdL (zvals false W) 0 T.P.n) [ZMOD T.P.pZ] := by
  obtain ⟨e, hout⟩ := denoteMR_eq_denoteZ_of_boundsOk false _ _ _ T.carry_ok W hW
  refine ⟨hout, ?_⟩
  rw [e, carryBlk_denoteZ _ _ T.wordOk.1 T.wordOk.2.2.2, ← evalZ_eq_evalL, evalL_rdL]
  simpa only [zero_add] using T.P.carryChain_cong T.placed.2.2 T.sched _
    (fun j => hvGetZ_zvals_nonneg W j)

/-- **The body of a binary operation under its certificates.** Tight limbs of both operands
    become tight limbs whose value is the operation on the operand values modulo `p`. -/
theorem body_sem (o : BinOp) (W : Valuation (RCtx (2 * T.P.n)))
    (hW : ValsIn false (ivVec r64 (T.tight ++ T.tight) (2 * T.P.n)) W) :
    ValsIn false (ivVec r64 T.tight T.P.n) (T.bodyRun o W) ∧
      evalL T.P.b (rdL (zvals false (T.bodyRun o W)) 0 T.P.n) ≡
        o.evalZ (evalL T.P.b (rdL (zvals false W) 0 T.P.n))
          (evalL T.P.b (rdL (zvals false W) T.P.n T.P.n)) [ZMOD T.P.pZ] := by
  cases o with
  | add =>
    obtain ⟨e, hout⟩ := denoteMR_eq_denoteZ_of_boundsOk false _ _ _ T.add_ok W hW
    obtain ⟨hc, hcv⟩ := T.carry_sem _ hout
    refine ⟨hc, hcv.trans ?_⟩
    show _ ≡ _ + _ [ZMOD _]
    rw [e, addBlk_denoteZ, evalL_ofFn_add]
    simp only [rdL, zero_add]
    exact Int.ModEq.refl _
  | sub =>
    obtain ⟨e, hout⟩ := denoteMR_eq_denoteZ_of_boundsOk false _ _ _ T.sub_ok W hW
    obtain ⟨hc, hcv⟩ := T.carry_sem _ hout
    refine ⟨hc, hcv.trans ?_⟩
    show _ ≡ _ - _ [ZMOD _]
    rw [e, subBlk_denoteZ _ T.bal_lt, evalL_ofFn_sub, evalL_ofFn_add]
    have hbal : evalL T.P.b (List.ofFn fun i => (balD T.P i : ℤ)) = 2 * T.P.pZ := by
      rw [← T.evalL_pD, List.map_ofFn]
      simp only [evalL_ofFn, balD, Function.comp_apply, Nat.cast_mul, Nat.cast_ofNat,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hbal]
    simp only [rdL, zero_add]
    exact Int.modEq_iff_dvd.2 ⟨-2, by ring⟩
  | mul =>
    have hW' := valsIn_mono hW T.tight_loose2
    obtain ⟨e, hout⟩ := denoteMR_eq_denoteZ_of_boundsOk false _ _ _ T.mul_ok W hW'
    refine ⟨hout, ?_⟩
    have hc := T.P.carryMulZ_cong T.placed T.sched (fun i => hget (zvals false W) (aVar T.P.n i))
      (fun i => hget (zvals false W) (bVar T.P.n i)) (fun i => hget_zvals_nonneg W _)
      (fun i => hget_zvals_nonneg W _)
    show evalL T.P.b (rdL (zvals false ((carryMulBlk T.P T.sched).denote W)) 0 T.P.n) ≡ _ [ZMOD _]
    rw [e, evalL_rdL, evalL_rdL, evalL_rdL]
    simp only [carryMulBlk_denoteZ T.P T.sched T.wordOk, zero_add, aVar, bVar, hget_rv]
    simp only [aVar, bVar, hget_rv] at hc
    exact hc

/-- **`carrySquare` under its certificate.** Tight limbs become tight limbs whose value is the
    square of the operand value modulo `p`. -/
theorem sq_sem (W : Valuation (RCtx T.P.n)) (hW : ValsIn false (ivVec r64 T.tight T.P.n) W) :
    ValsIn false (ivVec r64 T.tight T.P.n) ((carrySquareBlk T.P T.sched).denote W) ∧
      evalL T.P.b (rdL (zvals false ((carrySquareBlk T.P T.sched).denote W)) 0 T.P.n) ≡
        evalL T.P.b (rdL (zvals false W) 0 T.P.n) * evalL T.P.b (rdL (zvals false W) 0 T.P.n)
          [ZMOD T.P.pZ] := by
  obtain ⟨e, hout⟩ := denoteMR_eq_denoteZ_of_boundsOk false _ _ _ T.sq_ok W
    (valsIn_mono hW T.tight_loose)
  refine ⟨hout, ?_⟩
  have hc := T.P.carrySquareZ_cong T.placed T.sched (fun i => hget (zvals false W) (sVar T.P.n i))
    (fun i => hget_zvals_nonneg W _)
  rw [e, evalL_rdL, evalL_rdL]
  simp only [carrySquareBlk_denoteZ T.P T.sched T.wordOk, zero_add, sVar, hget_rv]
  simp only [sVar, hget_rv] at hc
  exact hc

/-- **`freeze` under its certificate.** Tight limbs become canonical limbs whose value is
    the value of the input limbs reduced modulo `p`. -/
theorem freeze_sem (W : Valuation (RCtx T.P.n)) (hW : ValsIn false (ivVec r64 T.tight T.P.n) W) :
    ValsIn false (ivVec r64 (canonIvs T.P) T.P.n) ((freezeBlk T.P).denote W) ∧
      evalL T.P.b (rdL (zvals false ((freezeBlk T.P).denote W)) 0 T.P.n) =
        evalL T.P.b (rdL (zvals false W) 0 T.P.n) % T.P.pZ := by
  obtain ⟨e, hout⟩ := denoteMR_eq_denoteZ_of_boundsOk false _ _ _ T.freeze_ok W hW
  refine ⟨hout, ?_⟩
  rw [e, freezeBlk_denoteZ _ T.wordOk.1 T.m_lt T.pD_lt]
  have hX : evalL T.P.b (rdL (zvals false W) 0 T.P.n) < 2 * T.P.pZ := by
    refine lt_of_le_of_lt (evalL_ofFn_mono _ _ _ _ fun i => ?_) T.tight_lt
    have := (valsIn_ivVec 64 T.P.n T.tight W).1 hW i i.isLt
    exact ⟨hvGetZ_zvals_nonneg W _, by simpa using this.2⟩
  exact (freezeZ_spec T.P.b T.P.n T.P.pZ _ _ _ (by simp [rdL]) (by simp) (by simp) T.evalL_mD
    T.evalL_pD T.p_pos (le_of_lt T.p_lt) (rdL_nonneg W _ _) hX).1

/-- **`toBytes` under its certificate.** Canonical limbs of value below `2^(8·nB)` become the
    bytes of the same little-endian value. -/
theorem toBytes_sem (W : Valuation (RCtx T.P.n))
    (hW : ValsIn false (ivVec r64 (canonIvs T.P) T.P.n) W)
    (hX : evalL T.P.b (rdL (zvals false W) 0 T.P.n) < 2 ^ (8 * T.nB)) :
    evalL 8 (rdL (zvals false ((toBytesBlk T.P.b T.P.n T.nB).denote W)) 0 T.nB) =
      evalL T.P.b (rdL (zvals false W) 0 T.P.n) := by
  obtain ⟨e, -⟩ := denoteMR_eq_denoteZ_of_boundsOk false _ _ _ T.toBytes_ok W hW
  rw [e, toBytesBlk_denoteZ]
  obtain ⟨R, hR, eR, hd⟩ := packZ_spec T.P.b T.b_ge T.nB 0 0 _ le_rfl (rdL_nonneg W _ _)
  have h0 := evalL_nonneg 8 _ fun d hd' => (hd d hd').1
  have hR0 : R = 0 := by
    by_contra hne
    have : 1 ≤ R := by omega
    have hpos : (0 : ℤ) < 2 ^ (8 * T.nB) := by positivity
    nlinarith
  rw [hR0] at eR
  simpa using eR

/-- **The byte-level ABI of a binary operation.** For input bytes in the template's
    intervals, operand `a` the little-endian value `A` of bytes `0 … nB-1` and operand `b`
    the value `B` of bytes `nB … 2nB-1`, the output bytes are the little-endian encoding of
    the canonical representative of `A ∘ B` modulo `p`. -/
theorem runBin_abi (o : BinOp) (V : Valuation (BCtx (2 * T.nB)))
    (hV : ValsIn false (ivVec r8 (T.byteIn ++ T.byteIn) (2 * T.nB)) V) :
    evalL 8 (rdL (zvals false (T.runBin o V)) 0 T.nB) =
      o.evalZ (evalL 8 (rdL (zvals false V) 0 T.nB)) (evalL 8 (rdL (zvals false V) T.nB T.nB)) %
        T.P.pZ := by
  obtain ⟨h1, eA, eB⟩ := T.fromBytes2_sem V hV
  obtain ⟨h2, e2⟩ := T.body_sem o _ h1
  obtain ⟨h3, e3⟩ := T.freeze_sem _ h2
  have hlt : evalL T.P.b (rdL (zvals false ((freezeBlk T.P).denote
      (T.bodyRun o ((fromBytes2Blk T.P.b T.P.n T.nB).denote V)))) 0 T.P.n) < 2 ^ (8 * T.nB) := by
    rw [e3]
    exact lt_of_lt_of_le (Int.emod_lt_of_pos _ T.p_pos) T.p_bytes
  rw [runBin, T.toBytes_sem _ h3 hlt, e3, ← eA, ← eB]
  exact e2

/-- **The byte-level ABI of the square.** -/
theorem runSq_abi (V : Valuation (BCtx T.nB)) (hV : ValsIn false (ivVec r8 T.byteIn T.nB) V) :
    evalL 8 (rdL (zvals false (T.runSq V)) 0 T.nB) =
      evalL 8 (rdL (zvals false V) 0 T.nB) * evalL 8 (rdL (zvals false V) 0 T.nB) % T.P.pZ := by
  obtain ⟨h1, eA⟩ := T.fromBytes_sem V hV
  obtain ⟨h2, e2⟩ := T.sq_sem _ h1
  obtain ⟨h3, e3⟩ := T.freeze_sem _ h2
  have hlt : evalL T.P.b (rdL (zvals false ((freezeBlk T.P).denote
      ((carrySquareBlk T.P T.sched).denote
      ((fromBytesBlk T.P.b T.P.n T.nB).denote V)))) 0 T.P.n) < 2 ^ (8 * T.nB) := by
    rw [e3]
    exact lt_of_lt_of_le (Int.emod_lt_of_pos _ T.p_pos) T.p_bytes
  rw [runSq, T.toBytes_sem _ h3 hlt, e3, ← eA]
  exact e2

/-- **The ABI in `ZMod p`.** The output bytes of a binary operation encode, as a natural
    number, the canonical representative of the operation on the input values in
    `ZMod p`. -/
theorem runBin_abi_zmod (o : BinOp) (V : Valuation (BCtx (2 * T.nB)))
    (hV : ValsIn false (ivVec r8 (T.byteIn ++ T.byteIn) (2 * T.nB)) V) :
    ((evalL 8 (rdL (zvals false (T.runBin o V)) 0 T.nB) : ℤ) : ZMod T.P.p) =
        ((o.evalZ (evalL 8 (rdL (zvals false V) 0 T.nB))
          (evalL 8 (rdL (zvals false V) T.nB T.nB)) : ℤ) : ZMod T.P.p) ∧
      0 ≤ evalL 8 (rdL (zvals false (T.runBin o V)) 0 T.nB) ∧
      evalL 8 (rdL (zvals false (T.runBin o V)) 0 T.nB) < T.P.pZ := by
  rw [T.runBin_abi o V hV]
  refine ⟨?_, Int.emod_nonneg _ (ne_of_gt T.p_pos), Int.emod_lt_of_pos _ T.p_pos⟩
  rw [ZMod.intCast_eq_intCast_iff, T.p_cast]
  exact Int.emod_emod_of_dvd _ (dvd_refl _)

end FieldReprTemplate

/-! ## 10. Curve25519 -/

/-- fiat-crypto's input bound of `curve25519_64` `from_bytes`: 31 bytes in `[0, 255]` and a
    top byte in `[0, 127]`. -/
def curve25519ByteIn : List Iv := List.replicate 31 (0, 255) ++ [(0, 127)]

/-- The tight limb intervals of Curve25519, `[0, 2^51]` (`UnsatBlocks.tightIv`). -/
def c25519Tight : List Iv := [tightIv, tightIv, tightIv, tightIv, tightIv]

/-- The loose limb intervals of Curve25519, `[0, 3·2^51]` (`UnsatBlocks.looseIv`). -/
def c25519Loose : List Iv := [looseIv, looseIv, looseIv, looseIv, looseIv]

section C25519

theorem c25519_shape : 0 < curve25519Unsat.n ∧ 8 ≤ curve25519Unsat.b ∧
    cSumN curve25519Unsat ≤ 2 ^ curve25519Unsat.k := by
  decide +kernel

theorem c25519_prime : 0 < curve25519Unsat.pZ ∧
    curve25519Unsat.pZ < 2 ^ (curve25519Unsat.b * curve25519Unsat.n) ∧
    curve25519Unsat.pZ ≤ 2 ^ (8 * 32) := by
  decide +kernel

theorem c25519_digits : (∀ i, balD curve25519Unsat i < 2 ^ 64) ∧
    ∀ i, mD curve25519Unsat i < 2 ^ 64 := by
  decide +kernel

theorem c25519_tight :
    evalL curve25519Unsat.b
        (List.ofFn fun i : Fin curve25519Unsat.n => (c25519Tight.getD i (0, 0)).2) <
      2 * curve25519Unsat.pZ ∧
    ivsLe c25519Tight c25519Loose curve25519Unsat.n = true ∧
    ivsLe (c25519Tight ++ c25519Tight) (c25519Loose ++ c25519Loose)
      (2 * curve25519Unsat.n) = true := by
  decide +kernel

theorem c25519_fromBytes_ok : boundsOkMR false (ivVec r8 curve25519ByteIn 32)
    (fromBytesBlk curve25519Unsat.b curve25519Unsat.n 32)
    (ivVec r64 c25519Tight curve25519Unsat.n) = true := by
  decide +kernel

theorem c25519_fromBytes2_ok : boundsOkMR false
    (ivVec r8 (curve25519ByteIn ++ curve25519ByteIn) (2 * 32))
    (fromBytes2Blk curve25519Unsat.b curve25519Unsat.n 32)
    (ivVec r64 (c25519Tight ++ c25519Tight) (2 * curve25519Unsat.n)) = true := by
  decide +kernel

theorem c25519_add_ok : boundsOkMR false
    (ivVec r64 (c25519Tight ++ c25519Tight) (2 * curve25519Unsat.n))
    (addBlk curve25519Unsat) (ivVec r64 c25519Loose curve25519Unsat.n) = true := by
  decide +kernel

theorem c25519_sub_ok : boundsOkMR false
    (ivVec r64 (c25519Tight ++ c25519Tight) (2 * curve25519Unsat.n))
    (subBlk curve25519Unsat) (ivVec r64 c25519Loose curve25519Unsat.n) = true := by
  decide +kernel

theorem c25519_carry_ok : boundsOkMR false (ivVec r64 c25519Loose curve25519Unsat.n)
    (carryBlk curve25519Unsat curve25519Chain)
    (ivVec r64 c25519Tight curve25519Unsat.n) = true := by
  decide +kernel

theorem c25519_mul_ok : boundsOkMR false
    (ivVec r64 (c25519Loose ++ c25519Loose) (2 * curve25519Unsat.n))
    (carryMulBlk curve25519Unsat curve25519Chain)
    (ivVec r64 c25519Tight curve25519Unsat.n) = true := by
  decide +kernel

theorem c25519_sq_ok : boundsOkMR false (ivVec r64 c25519Loose curve25519Unsat.n)
    (carrySquareBlk curve25519Unsat curve25519Chain)
    (ivVec r64 c25519Tight curve25519Unsat.n) = true := by
  decide +kernel

theorem c25519_freeze_ok : boundsOkMR false (ivVec r64 c25519Tight curve25519Unsat.n)
    (freezeBlk curve25519Unsat)
    (ivVec r64 (canonIvs curve25519Unsat) curve25519Unsat.n) = true := by
  decide +kernel

theorem c25519_toBytes_ok : boundsOkMR false
    (ivVec r64 (canonIvs curve25519Unsat) curve25519Unsat.n)
    (toBytesBlk curve25519Unsat.b curve25519Unsat.n 32) (ivVec r8 (byteIvs 32) 32) = true := by
  decide +kernel

end C25519

/-- **The Curve25519 template**: five 51-bit limbs, fiat-crypto's carry schedule, 32-byte
    encodings, fiat-crypto's loose and tight bounds. -/
def curve25519Repr : FieldReprTemplate where
  P := curve25519Unsat
  sched := curve25519Chain
  nB := 32
  byteIn := curve25519ByteIn
  loose := c25519Loose
  tight := c25519Tight
  n_pos := c25519_shape.1
  b_ge := c25519_shape.2.1
  wordOk := curve25519Unsat_wordOk
  placed := curve25519Unsat_placed
  cSum_le := c25519_shape.2.2
  p_pos := c25519_prime.1
  p_lt := c25519_prime.2.1
  p_bytes := c25519_prime.2.2
  bal_lt := c25519_digits.1
  m_lt := c25519_digits.2
  tight_lt := c25519_tight.1
  tight_loose := c25519_tight.2.1
  tight_loose2 := c25519_tight.2.2
  fromBytes_ok := c25519_fromBytes_ok
  fromBytes2_ok := c25519_fromBytes2_ok
  add_ok := c25519_add_ok
  sub_ok := c25519_sub_ok
  carry_ok := c25519_carry_ok
  mul_ok := c25519_mul_ok
  sq_ok := c25519_sq_ok
  freeze_ok := c25519_freeze_ok
  toBytes_ok := c25519_toBytes_ok

/-- **The byte-level ABI at Curve25519.** For input bytes within fiat-crypto's `from_bytes`
    bounds, the output bytes of a binary operation are the little-endian encoding of the
    canonical representative of the operation on the input values modulo `2^255 - 19`. -/
theorem curve25519Repr_runBin_abi (o : FieldReprTemplate.BinOp)
    (V : Valuation (BCtx (2 * 32)))
    (hV : ValsIn false (ivVec r8 (curve25519ByteIn ++ curve25519ByteIn) (2 * 32)) V) :
    evalL 8 (rdL (zvals false (curve25519Repr.runBin o V)) 0 32) =
      o.evalZ (evalL 8 (rdL (zvals false V) 0 32)) (evalL 8 (rdL (zvals false V) 32 32)) %
        (2 ^ 255 - 19) := by
  rw [← curve25519Unsat_pZ]
  exact curve25519Repr.runBin_abi o V hV

/-! ## 11. p448 -/

/-- p448 at eight limbs of 56 bits: `p = 2^448 - 2^224 - 1`. -/
def p448Unsat : UnsatParams := ⟨8, 56, 448, [(1, 224), (1, 0)]⟩

/-- The carry schedule of the p448 products: limbs `0` to `7`, the top carry into limbs `4`
    and `0`, then limbs `0` and `4`. -/
def p448Chain : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 0, 4]

/-- The tight limb intervals of p448, `[0, 2^56 + 2^9]`. -/
def p448Tight : List Iv := List.replicate 8 (0, 2 ^ 56 + 2 ^ 9)

/-- The loose limb intervals of p448, `[0, 3·2^56 + 2^10]`. -/
def p448Loose : List Iv := List.replicate 8 (0, 3 * 2 ^ 56 + 2 ^ 10)

theorem p448Unsat_wordOk : WordOk p448Unsat := by decide

theorem p448Unsat_placed : p448Unsat.Placed := by decide

theorem p448_shape : 0 < p448Unsat.n ∧ 8 ≤ p448Unsat.b ∧ cSumN p448Unsat ≤ 2 ^ p448Unsat.k := by
  decide +kernel

theorem p448_prime : 0 < p448Unsat.pZ ∧ p448Unsat.pZ < 2 ^ (p448Unsat.b * p448Unsat.n) ∧
    p448Unsat.pZ ≤ 2 ^ (8 * 56) := by
  decide +kernel

theorem p448_digits : (∀ i, balD p448Unsat i < 2 ^ 64) ∧ ∀ i, mD p448Unsat i < 2 ^ 64 := by
  decide +kernel

theorem p448_tight :
    evalL p448Unsat.b (List.ofFn fun i : Fin p448Unsat.n => (p448Tight.getD i (0, 0)).2) <
      2 * p448Unsat.pZ ∧
    ivsLe p448Tight p448Loose p448Unsat.n = true ∧
    ivsLe (p448Tight ++ p448Tight) (p448Loose ++ p448Loose) (2 * p448Unsat.n) = true := by
  decide +kernel

theorem p448_fromBytes_ok : boundsOkMR false (ivVec r8 (byteIvs 56) 56)
    (fromBytesBlk p448Unsat.b p448Unsat.n 56) (ivVec r64 p448Tight p448Unsat.n) = true := by
  native_decide

theorem p448_fromBytes2_ok : boundsOkMR false (ivVec r8 (byteIvs 56 ++ byteIvs 56) (2 * 56))
    (fromBytes2Blk p448Unsat.b p448Unsat.n 56)
    (ivVec r64 (p448Tight ++ p448Tight) (2 * p448Unsat.n)) = true := by
  native_decide

theorem p448_add_ok : boundsOkMR false (ivVec r64 (p448Tight ++ p448Tight) (2 * p448Unsat.n))
    (addBlk p448Unsat) (ivVec r64 p448Loose p448Unsat.n) = true := by
  decide +kernel

theorem p448_sub_ok : boundsOkMR false (ivVec r64 (p448Tight ++ p448Tight) (2 * p448Unsat.n))
    (subBlk p448Unsat) (ivVec r64 p448Loose p448Unsat.n) = true := by
  decide +kernel

theorem p448_carry_ok : boundsOkMR false (ivVec r64 p448Loose p448Unsat.n)
    (carryBlk p448Unsat p448Chain) (ivVec r64 p448Tight p448Unsat.n) = true := by
  decide +kernel

theorem p448_mul_ok : boundsOkMR false (ivVec r64 (p448Loose ++ p448Loose) (2 * p448Unsat.n))
    (carryMulBlk p448Unsat p448Chain) (ivVec r64 p448Tight p448Unsat.n) = true := by
  native_decide

theorem p448_sq_ok : boundsOkMR false (ivVec r64 p448Loose p448Unsat.n)
    (carrySquareBlk p448Unsat p448Chain) (ivVec r64 p448Tight p448Unsat.n) = true := by
  native_decide

theorem p448_freeze_ok : boundsOkMR false (ivVec r64 p448Tight p448Unsat.n) (freezeBlk p448Unsat)
    (ivVec r64 (canonIvs p448Unsat) p448Unsat.n) = true := by
  decide +kernel

theorem p448_toBytes_ok : boundsOkMR false (ivVec r64 (canonIvs p448Unsat) p448Unsat.n)
    (toBytesBlk p448Unsat.b p448Unsat.n 56) (ivVec r8 (byteIvs 56) 56) = true := by
  decide +kernel

/-- **The p448 template**: eight 56-bit limbs, 56-byte encodings. -/
def p448Repr : FieldReprTemplate where
  P := p448Unsat
  sched := p448Chain
  nB := 56
  byteIn := byteIvs 56
  loose := p448Loose
  tight := p448Tight
  n_pos := p448_shape.1
  b_ge := p448_shape.2.1
  wordOk := p448Unsat_wordOk
  placed := p448Unsat_placed
  cSum_le := p448_shape.2.2
  p_pos := p448_prime.1
  p_lt := p448_prime.2.1
  p_bytes := p448_prime.2.2
  bal_lt := p448_digits.1
  m_lt := p448_digits.2
  tight_lt := p448_tight.1
  tight_loose := p448_tight.2.1
  tight_loose2 := p448_tight.2.2
  fromBytes_ok := p448_fromBytes_ok
  fromBytes2_ok := p448_fromBytes2_ok
  add_ok := p448_add_ok
  sub_ok := p448_sub_ok
  carry_ok := p448_carry_ok
  mul_ok := p448_mul_ok
  sq_ok := p448_sq_ok
  freeze_ok := p448_freeze_ok
  toBytes_ok := p448_toBytes_ok

theorem p448Unsat_pZ : p448Unsat.pZ = 2 ^ 448 - 2 ^ 224 - 1 := by
  simp only [UnsatParams.pZ, UnsatParams.cSum, p448Unsat, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.cast_one, one_mul, pow_zero, add_zero]
  exact (sub_sub _ _ _).symm

/-- **The byte-level ABI at p448.** For any input bytes, the output bytes of a binary
    operation are the little-endian encoding of the canonical representative of the operation
    on the input values modulo `2^448 - 2^224 - 1`. -/
theorem p448Repr_runBin_abi (o : FieldReprTemplate.BinOp) (V : Valuation (BCtx (2 * 56)))
    (hV : ValsIn false (ivVec r8 (byteIvs 56 ++ byteIvs 56) (2 * 56)) V) :
    evalL 8 (rdL (zvals false (p448Repr.runBin o V)) 0 56) =
      o.evalZ (evalL 8 (rdL (zvals false V) 0 56)) (evalL 8 (rdL (zvals false V) 56 56)) %
        (2 ^ 448 - 2 ^ 224 - 1) := by
  rw [← p448Unsat_pZ]
  exact p448Repr.runBin_abi o V hV

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.UnsatField
