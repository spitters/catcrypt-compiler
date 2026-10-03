/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Montgomery field blocks over `n` 64-bit limbs for an odd modulus below `2^(64n)`

For a record `LimbParams n` of an odd modulus `p < 2^(64n)` and the constant
`nInv = -p⁻¹ mod 2^64`, an element `x` of `ZMod p` is represented by the `n`
little-endian 64-bit limbs of the canonical representative of its Montgomery form
`x · 2^(64n)` (`enc`). The module gives multi-result `jasminDialect` blocks for
addition, multiplication, constants, subtraction, negation and inversion, generic in
`n`, and one value theorem for each, proved once for every limb count and modulus.

The algorithm is the word-by-word Montgomery arithmetic of fiat-crypto
(`Arithmetic/WordByWordMontgomery.v`): the schoolbook product (`prodNK`), `n` words of
reduction by recursion on the number of steps (`redcChainK`, fiat's `redc_loop`), and a
carry-aware conditional subtraction on `n + 1` limbs (`csubPCK`, fiat's
`conditional_sub`). The reduction bound `redcChainK_denote` is proved by induction on
the number of steps, in the manner of fiat's `redc_loop_bound` and
`snd_redc_loop_mod_N`. None of the blocks branches or indexes on data.

## Main definitions

* `LimbParams n`: the modulus record; `Rn n`: the register types of an element.
* `digits`, `limbsN`, `retN`: radix-`2^64` digits, limb values and the limb return.
* `csubPCK`, `addMK`, `subMK`, `prodNK`, `sqrNK`, `redcStepK`, `redcChainK`, `redcFinK`,
  `mulMK`, `sqrMK`, `powK`: the list-level operations.
* `crossV`, `diagV`: the cross and diagonal sums of a square.
* `R`, `enc`: the Montgomery factor `2^(64n)` and the encoding.
* `addBlk`, `subBlk`, `negBlk`, `mulBlk`, `sqrBlk`, `constBlk`, `invBlk`: the blocks.

## Main results

* `csubPCK_denote`: the conditional subtraction on `n + 1` limbs.
* `prodNK_denote`: the schoolbook product of two limb lists.
* `sqrNK_denote`: the square of a limb list, with each cross product formed once and
  doubled (`nv_mul_self`: the square is the diagonal sum plus twice the cross sum).
* `redcChainK_denote`: `s` words of Montgomery reduction give `A · 2^(64s) = T + M p`
  with `M < 2^(64s)`; `redc_bound`: after `n` words from `T < p²`, `A < 2p`.
* `mulMK_denote`, `mulMK_denote_enc`: the Montgomery product; `sqrMK_denote`,
  `sqrMK_denote_enc`: the Montgomery square.
* `addBlk_denote`, `mulBlk_denote`, `sqrBlk_denote`, `constBlk_denote`, `subBlk_denote_enc`,
  `negBlk_denote_enc`: the value theorems of the blocks.
* `invBlk_denote_pow`, `invBlk_denote_inv`: the inversion block gives `enc (x^(p-2))`,
  and `enc x⁻¹` at a prime modulus.
* `enc_injective`: the encoding is injective.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
  (w64 w1 MC lk lk1 eBin eConst eBit eConst_denote eBit_denote eBin_denote Pres Pres.id
    Pres.comp bindK bindK_denote nv nv_nil nv_cons nv_map nv_append nv_lt selR selR_denote
    constsK constsK_denote limbsNat addK addK_denote mulRowK mulRowK_denote accK
    xorR xorR_denote adcR adcR_denote eMulhi eMulhi_denote mulx_toNat)

/-! ## 1. The modulus, digits and limb values -/

/-- An odd modulus below `2^(64n)` with the Montgomery constant `nInv = -p⁻¹ mod 2^64`. -/
structure LimbParams (n : Nat) where
  /-- The modulus. -/
  p : Nat
  /-- `-p⁻¹ mod 2^64`. -/
  nInv : Nat
  one_lt : 1 < p
  p_odd : p % 2 = 1
  p_lt : p < 2 ^ (64 * n)
  nInv_lt : nInv < 2 ^ 64
  nInv_spec : (p * nInv + 1) % 2 ^ 64 = 0

/-- The register types of an element: `n` 64-bit limbs. -/
abbrev Rn (n : Nat) : List JasminTy := List.replicate n w64

theorem two_pow_succ (k : Nat) : 2 ^ (64 * (k + 1)) = 2 ^ (64 * k) * 2 ^ 64 := by
  rw [Nat.mul_succ, Nat.pow_add]

variable {n : Nat} (P : LimbParams n)

/-- The limb radix is at most `2^(64n)`: a modulus above `1` needs at least one limb. -/
theorem two_pow_le {n : Nat} (P : LimbParams n) : 2 ^ 64 ≤ 2 ^ (64 * n) := by
  have h1 := P.one_lt
  have h2 := P.p_lt
  rcases n with _ | n
  · simp at h2
    omega
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem n_pos {n : Nat} (P : LimbParams n) : 0 < n := by
  have h1 := P.one_lt
  have h2 := P.p_lt
  rcases n with _ | n
  · simp at h2
    omega
  · omega

/-- The `k` little-endian 64-bit digits of `v`. -/
def digits : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, v => v % 2 ^ 64 :: digits k (v / 2 ^ 64)

theorem digits_length : ∀ k v, (digits k v).length = k
  | 0, _ => rfl
  | k + 1, v => by simp [digits, digits_length k]

theorem digits_lt : ∀ k v, ∀ d ∈ digits k v, d < 2 ^ 64
  | 0, _ => by simp [digits]
  | k + 1, v => by
      intro d hd
      simp only [digits, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact Nat.mod_lt _ (by norm_num)
      · exact digits_lt k _ d hd

theorem limbsNat_digits_mod : ∀ k v, limbsNat (digits k v) = v % 2 ^ (64 * k)
  | 0, v => by simp [digits, limbsNat, Nat.mod_one]
  | k + 1, v => by
      rw [digits, limbsNat, limbsNat_digits_mod k, show 64 * (k + 1) = 64 + 64 * k by ring,
        Nat.pow_add, Nat.mod_mul]

theorem limbsNat_digits (k v : Nat) (hv : v < 2 ^ (64 * k)) : limbsNat (digits k v) = v := by
  rw [limbsNat_digits_mod, Nat.mod_eq_of_lt hv]

theorem limbsNat_append : ∀ xs ys : List Nat,
    limbsNat (xs ++ ys) = limbsNat xs + 2 ^ (64 * xs.length) * limbsNat ys
  | [], ys => by simp [limbsNat]
  | x :: xs, ys => by
      simp only [List.cons_append, limbsNat, limbsNat_append xs ys, List.length_cons]
      rw [Nat.mul_succ, Nat.pow_add]
      ring

theorem limbsNat_replicate_zero : ∀ k, limbsNat (List.replicate k 0) = 0
  | 0 => rfl
  | k + 1 => by simp [List.replicate_succ, limbsNat, limbsNat_replicate_zero k]

/-- The `k` little-endian 64-bit limbs of `v`. -/
def limbsN : (k : Nat) → Nat → ListDenote (Rn k)
  | 0, _ => .nil
  | k + 1, v => .cons (BitVec.ofNat 64 v) (limbsN k (v / 2 ^ 64))

theorem limbsN_mod : ∀ k v, limbsN k (v % 2 ^ (64 * k)) = limbsN k v
  | 0, _ => rfl
  | k + 1, v => by
      have e : 2 ^ (64 * (k + 1)) = 2 ^ 64 * 2 ^ (64 * k) := by
        rw [two_pow_succ, Nat.mul_comm]
      have hb : BitVec.ofNat 64 (v % (2 ^ 64 * 2 ^ (64 * k))) = BitVec.ofNat 64 v :=
        BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat, Nat.mod_mul_right_mod])
      simp only [limbsN]
      rw [e, Nat.mod_mul_right_div_self, limbsN_mod k, hb]

theorem limbsN_injective : ∀ {k : Nat} {a b : Nat}, a < 2 ^ (64 * k) → b < 2 ^ (64 * k) →
    limbsN k a = limbsN k b → a = b
  | 0, a, b, ha, hb, _ => by simp at ha hb; omega
  | k + 1, a, b, ha, hb, h => by
      have h0 : BitVec.ofNat 64 a = BitVec.ofNat 64 b := (HVector.cons.inj h).1
      have h1 : limbsN k (a / 2 ^ 64) = limbsN k (b / 2 ^ 64) := (HVector.cons.inj h).2
      have e0 := congrArg BitVec.toNat h0
      simp only [BitVec.toNat_ofNat] at e0
      rw [two_pow_succ] at ha hb
      have hd := limbsN_injective (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm]))
        (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])) h1
      omega

/-- `(A + m p) ≡ 0 mod 2^64` for the Montgomery digit `m = (A mod 2^64) · nInv mod 2^64`. -/
theorem redc_digit (A : Nat) :
    (A + (A % 2 ^ 64 * P.nInv % 2 ^ 64) * P.p) % 2 ^ 64 = 0 := by
  have h : ((P.p * P.nInv + 1 : Nat) : ZMod (2 ^ 64)) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero P.nInv_spec)
  refine Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp ?_)
  push_cast at h ⊢
  simp only [ZMod.natCast_mod, Nat.cast_mul]
  linear_combination (A : ZMod (2 ^ 64)) * h

/-! ## 2. Limb-list lemmas and the limb return -/

theorem nv_replicate {Δ : Ctxt jasminDialect} (W : Valuation Δ) (z : Var Δ w64)
    (hz : (lk z W).toNat = 0) : ∀ k, nv W (List.replicate k z) = 0
  | 0 => rfl
  | k + 1 => by rw [List.replicate_succ, nv_cons, nv_replicate W z hz k, hz]; rfl

theorem nv_cons_mod {Δ : Ctxt jasminDialect} (W : Valuation Δ) (x : Var Δ w64)
    (xs : List (Var Δ w64)) : (lk x W).toNat = nv W (x :: xs) % 2 ^ 64 := by
  have := (lk x W).isLt
  rw [nv_cons]
  omega

theorem nv_take {Δ : Ctxt jasminDialect} (W : Valuation Δ) (xs : List (Var Δ w64)) (k : Nat)
    (hlen : k ≤ xs.length) (hv : nv W xs < 2 ^ (64 * k)) : nv W (xs.take k) = nv W xs := by
  have hsplit := nv_append W (xs.take k) (xs.drop k)
  rw [List.take_append_drop, List.length_take_of_le hlen] at hsplit
  have h0 : nv W (xs.drop k) = 0 := by
    by_contra hne
    have : 2 ^ (64 * k) ≤ 2 ^ (64 * k) * nv W (xs.drop k) :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
    omega
  rw [hsplit, h0]
  simp

/-- The variables of `out` as a tuple of `k` registers, padded with `fb`. -/
def varsPad {Δ : Ctxt jasminDialect} (fb : Var Δ w64) :
    (k : Nat) → List (Var Δ w64) → HVector (fun t => Var Δ t) (Rn k)
  | 0, _ => .nil
  | k + 1, [] => .cons fb (varsPad fb k [])
  | k + 1, a :: as => .cons a (varsPad fb k as)

/-- The return of the `k` variables of a list of length `k`; on an empty list, `k`
    copies of a zero constant. -/
def retN {Δ : Ctxt jasminDialect} (k : Nat) : List (Var Δ w64) → MC Δ (Rn k)
  | [] => .var (eConst 0) (.ret (varsPad .here k []))
  | a :: as => .ret (varsPad a k (a :: as))

theorem lookupVars_varsPad {Δ : Ctxt jasminDialect} (W : Valuation Δ) (fb : Var Δ w64) :
    ∀ out : List (Var Δ w64),
      MultiReturnCom.lookupVars (varsPad fb out.length out) W = limbsN out.length (nv W out)
  | [] => rfl
  | a :: as => by
      have ih := lookupVars_varsPad W fb as
      have ha := (lk a W).isLt
      have e0 : Var.lookup a W = BitVec.ofNat 64 (nv W (a :: as)) :=
        BitVec.eq_of_toNat_eq (by
          show (lk a W).toNat = _
          rw [BitVec.toNat_ofNat, nv_cons]
          omega)
      have e1 : nv W (a :: as) / 2 ^ 64 = nv W as := by
        rw [nv_cons]
        omega
      have h : (MultiReturnCom.lookupVars (varsPad fb (as.length + 1) (a :: as)) W :
          ListDenote (Rn (as.length + 1))) =
          HVector.cons (Var.lookup a W) (MultiReturnCom.lookupVars (varsPad fb as.length as) W) :=
        rfl
      have h' : limbsN (as.length + 1) (nv W (a :: as)) =
          (HVector.cons (BitVec.ofNat 64 (nv W (a :: as)))
            (limbsN as.length (nv W (a :: as) / 2 ^ 64)) : ListDenote (Rn (as.length + 1))) :=
        rfl
      show (MultiReturnCom.lookupVars (varsPad fb (as.length + 1) (a :: as)) W :
          ListDenote (Rn (as.length + 1))) = limbsN (as.length + 1) (nv W (a :: as))
      rw [h, h', ih, e0, e1]

theorem retN_denote {Δ : Ctxt jasminDialect} (k : Nat) (out : List (Var Δ w64))
    (W : Valuation Δ) (hlen : out.length = k) :
    (retN k out).denote W = limbsN k (nv W out) := by
  subst hlen
  cases out with
  | nil => rfl
  | cons a as => exact lookupVars_varsPad W a (a :: as)

/-! ## 3. Conditional subtraction and addition -/

/-- The `n + 1` digits of `2^(64(n+1)) - p`. -/
def negDigits : List Nat := digits n (2 ^ (64 * n) - P.p) ++ [2 ^ 64 - 1]

theorem negDigits_lt : ∀ d ∈ negDigits P, d < 2 ^ 64 := by
  intro d hd
  simp only [negDigits, List.mem_append, List.mem_singleton] at hd
  rcases hd with hd | rfl
  · exact digits_lt _ _ d hd
  · norm_num

theorem negDigits_length : (negDigits P).length = n + 1 := by
  simp [negDigits, digits_length]

theorem limbsNat_negDigits : limbsNat (negDigits P) = 2 ^ (64 * (n + 1)) - P.p := by
  have hp := P.p_lt
  have h1 := P.one_lt
  rw [negDigits, limbsNat_append, digits_length, limbsNat_digits _ _ (by omega), two_pow_succ]
  simp only [limbsNat]
  omega

/-- One conditional subtraction of `p` from `n + 1` limbs of value `V < p + 2^(64n)`
    (fiat-crypto's `conditional_sub`): the sum `V + (2^(64(n+1)) - p)` carries exactly
    when `p ≤ V`, and the carry selects between its low `n` limbs and the low `n` input
    limbs. -/
def csubPCK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  constsK (negDigits P) fun r₁ K =>
  addK (xs.map (fun v => r₁ v)) K fun r₂ T c =>
  selR (fun v => v) c (T.take n) ((xs.map (fun v => r₂ (r₁ v))).take n) fun r₃ out =>
    k (fun v => r₃ (r₂ (r₁ v))) out

theorem csubPCK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hlen : xs.length = n + 1)
    (hV : nv W xs < P.p + 2 ^ (64 * n))
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n →
      nv W' out = (if P.p ≤ nv W xs then nv W xs - P.p else nv W xs) →
      (k r out).denote W' = G) :
    (csubPCK P xs k).denote W = G := by
  have hp := P.p_lt
  have hB := two_pow_succ n
  refine constsK_denote _ _ W G (negDigits_lt P) fun r₁ K W₁ h₁ hK hKv => ?_
  rw [limbsNat_negDigits] at hKv
  rw [negDigits_length] at hK
  refine addK_denote _ K _ W₁ G (by simp [hlen, hK]) fun r₂ T c W₂ h₂ hT hTv => ?_
  rw [nv_map h₁ xs, hKv] at hTv
  simp only [List.length_map, hlen] at hTv hT
  have hTl := nv_lt W₂ T
  rw [hT] at hTl
  have hc2 := (lk1 c W₂).isLt
  refine selR_denote (fun v => v) c _ _ _ W₂ W₂ G (Pres.id W₂) (by simp [hT, hlen])
    fun r₃ out W₃ h₃ hout hval => ?_
  refine hk _ out W₃ (Pres.comp (Pres.comp h₁ h₂) h₃) (by simp [hout, hT]) ?_
  rw [hval]
  by_cases hc : lk1 c W₂ = 1#1
  · have h1 : (lk1 c W₂).toNat = 1 := by rw [hc]; rfl
    rw [if_pos hc]
    rw [h1] at hTv
    have hge : P.p ≤ nv W xs := by omega
    rw [if_pos hge, nv_take W₂ T n (by omega) (by omega)]
    omega
  · have h0 : (lk1 c W₂).toNat = 0 := by
      have : (lk1 c W₂).toNat ≠ 1 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
      omega
    rw [if_neg hc]
    rw [h0] at hTv
    have hlt : ¬ P.p ≤ nv W xs := by omega
    rw [if_neg hlt, nv_take W₂ _ n (by simp [hlen]) (by rw [nv_map (Pres.comp h₁ h₂)]; omega),
      nv_map (Pres.comp h₁ h₂)]

/-- `if p ≤ V then V - p else V` is `V % p` below `2p`. -/
theorem csub_eq_mod (V : Nat) (hV : V < 2 * P.p) :
    (if P.p ≤ V then V - P.p else V) = V % P.p := by
  split_ifs with h
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- Addition modulo `p` on `n` limbs: the carry chain over the operands extended by a
    zero limb, then the conditional subtraction on `n + 1` limbs. -/
def addMK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  bindK (eConst 0) fun r₀ z =>
  addK (xs.map (fun v => r₀ v) ++ [z]) (ys.map (fun v => r₀ v) ++ [z]) fun r₁ S _ =>
  csubPCK P S fun r₂ out => k (fun v => r₂ (r₁ (r₀ v))) out

theorem addMK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = n) (hys : ys.length = n)
    (hx : nv W xs < P.p) (hy : nv W ys < P.p)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n →
      nv W' out = (nv W xs + nv W ys) % P.p → (k r out).denote W' = G) :
    (addMK P xs ys k).denote W = G := by
  have hp := P.p_lt
  have hB := two_pow_succ n
  refine bindK_denote _ _ _ _ fun r₀ z W₀ h₀ hz => ?_
  have ez : (lk z W₀).toNat = 0 := by rw [show lk z W₀ = _ from hz, eConst_denote]; rfl
  refine addK_denote _ _ _ W₀ G (by simp [hxs, hys]) fun r₁ S c W₁ h₁ hS hSv => ?_
  simp only [nv_append, nv_map h₀, nv_cons, nv_nil, ez, List.length_append, List.length_map,
    List.length_singleton, hxs, hys, Nat.mul_zero, Nat.add_zero] at hSv hS
  have hS0 : nv W₁ S = nv W xs + nv W ys := by
    have hc := (lk1 c W₁).isLt
    have : (lk1 c W₁).toNat = 0 := by
      by_contra hne
      have : 2 ^ (64 * (n + 1)) * 1 ≤ 2 ^ (64 * (n + 1)) * (lk1 c W₁).toNat :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    rw [this] at hSv
    omega
  refine csubPCK_denote P S _ W₁ G hS (by omega) fun r₂ out W₂ h₂ hout hv => ?_
  refine hk _ out W₂ (Pres.comp (Pres.comp h₀ h₁) h₂) hout ?_
  rw [hv, hS0]
  exact csub_eq_mod P _ (by omega)

/-! ## 4. The schoolbook product -/

/-- One accumulation step of the schoolbook product, for operands of `n` limbs: the row
    `xs · y` is added to the limbs of `acc` from position `i` on. -/
theorem accK_denote_n {Γ : Ctxt jasminDialect} {ts : List JasminTy} (i : Nat)
    (xs : List (Var Γ w64)) (y : Var Γ w64) (acc : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = n) (hacc : acc.length = i + n)
    (hbound : nv W acc + 2 ^ (64 * i) * (nv W xs * (lk y W).toNat)
      < 2 ^ (64 * i) * 2 ^ (64 * (n + 1)))
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = i + n + 1 →
      nv W' out = nv W acc + 2 ^ (64 * i) * (nv W xs * (lk y W).toNat) →
      (k r out).denote W' = G) :
    (accK i xs y acc k).denote W = G := by
  refine mulRowK_denote xs y _ W G fun r₁ row W₁ h₁ hrow hrowv => ?_
  refine bindK_denote _ _ _ _ fun r₂ z W₂ h₂ hz => ?_
  have hdl : (acc.drop i).length = n := by simp [hacc]
  have htl : (acc.take i).length = i := by simp [hacc]
  refine addK_denote _ _ _ W₂ G (by simp [hrow, hxs, hacc]) fun r₃ s c W₃ h₃ hs hsv => ?_
  refine hk _ _ W₃ (Pres.comp (Pres.comp h₁ h₂) h₃) (by simp [hs, hacc]; omega) ?_
  have hzv : (lk z W₂).toNat = 0 := by rw [show lk z W₂ = _ from hz, eConst_denote]; rfl
  rw [nv_append, nv_map (Pres.comp h₁ h₂), nv_map h₂, hrowv] at hsv
  simp only [nv_cons, nv_nil, hzv, List.length_append, List.length_map, hdl,
    List.length_singleton, Nat.mul_zero, Nat.add_zero] at hsv hs
  rw [nv_append, nv_map (Pres.comp (Pres.comp h₁ h₂) h₃), List.length_map, htl]
  have hsplit := nv_append W (acc.take i) (acc.drop i)
  rw [List.take_append_drop, htl] at hsplit
  rw [hsplit] at hbound ⊢
  have hlt : nv W (acc.drop i) + nv W xs * (lk y W).toNat < 2 ^ (64 * (n + 1)) := by
    refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (64 * i)) ?_
    rw [Nat.mul_add]
    omega
  have hc : (lk1 c W₃).toNat = 0 := by
    have := (lk1 c W₃).isLt
    by_contra hne
    have h1 : (lk1 c W₃).toNat = 1 := by omega
    rw [h1] at hsv
    omega
  rw [hc] at hsv
  have hs' : nv W₃ s = nv W (acc.drop i) + nv W xs * (lk y W).toNat := by omega
  rw [hs', Nat.mul_add]
  omega

/-- The rows `xs · y` for `y` in `ys`, accumulated into `acc` from position `i` on; the
    words `ys` live in the source context of the renaming `ren`. -/
def prodAccK : {Γ Δ : Ctxt jasminDialect} → {ts : List JasminTy} → Ctxt.Hom Γ Δ → Nat →
    List (Var Δ w64) → List (Var Γ w64) → List (Var Δ w64) →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts) → MC Δ ts
  | _, _, _, _, _, _, [], acc, k => k (fun v => v) acc
  | _, _, _, ren, i, xs, y :: ys, acc, k =>
      accK i xs (ren y) acc fun r₁ a =>
      prodAccK (fun v => r₁ (ren v)) (i + 1) (xs.map (fun v => r₁ v)) ys a fun r₂ out =>
        k (fun v => r₂ (r₁ v)) out

theorem prodAccK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (W : Valuation Γ)
    (ys : List (Var Γ w64)) : ∀ {Δ : Ctxt jasminDialect}
    (ren : Ctxt.Hom Γ Δ) (i : Nat) (xs : List (Var Δ w64)) (acc : List (Var Δ w64))
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts)
    (W₀ : Valuation Δ) (G : ListDenote ts) (Y₀ : Nat),
    Pres ren W W₀ → xs.length = n → acc.length = i + n → Y₀ < 2 ^ (64 * i) →
    nv W₀ acc = nv W₀ xs * Y₀ →
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (out : List (Var Δ' w64))
      (W' : Valuation Δ'), Pres r W₀ W' → out.length = i + ys.length + n →
      nv W' out = nv W₀ xs * (Y₀ + 2 ^ (64 * i) * nv W ys) → (k r out).denote W' = G) →
    (prodAccK ren i xs ys acc k).denote W₀ = G := by
  induction ys with
  | nil =>
    intro Δ ren i xs acc k W₀ G Y₀ _ _ hacc _ hv hk
    rw [prodAccK]
    exact hk _ acc W₀ (Pres.id W₀) (by simp [hacc]) (by simp [hv, nv_nil])
  | cons y ys ih =>
    intro Δ ren i xs acc k W₀ G Y₀ hren hxs hacc hY hv hk
    rw [prodAccK]
    have hX := nv_lt W₀ xs
    rw [hxs] at hX
    have ey : (lk (ren y) W₀).toNat = (lk y W).toNat := by rw [show lk (ren y) W₀ = lk y W from hren y]
    have hy := (lk y W).isLt
    have hBi := two_pow_succ i
    have hstep : Y₀ + 2 ^ (64 * i) * (lk y W).toNat < 2 ^ (64 * (i + 1)) := by
      have : 2 ^ (64 * i) * (lk y W).toNat ≤ 2 ^ (64 * i) * (2 ^ 64 - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have hpow : 2 ^ (64 * n) * 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ (64 * (n + 1)) := by
      rw [← Nat.pow_add, ← Nat.pow_add]
      ring_nf
    refine accK_denote_n i xs (ren y) acc _ W₀ G hxs hacc ?_ fun r₁ a W₁ h₁ ha hav => ?_
    · rw [hv, ey, ← hpow]
      calc nv W₀ xs * Y₀ + 2 ^ (64 * i) * (nv W₀ xs * (lk y W).toNat)
          = nv W₀ xs * (Y₀ + 2 ^ (64 * i) * (lk y W).toNat) := by ring
        _ < 2 ^ (64 * n) * 2 ^ (64 * (i + 1)) := Nat.mul_lt_mul'' hX hstep
    · refine ih (fun v => r₁ (ren v)) (i + 1) _ a _ W₁ G (Y₀ + 2 ^ (64 * i) * (lk y W).toNat)
        (Pres.comp hren h₁) (by simp [hxs]) (by rw [ha]; ring) hstep ?_
        fun r₂ out W₂ h₂ hout hval => ?_
      · rw [hav, nv_map h₁, hv, ey]
        ring
      · refine hk _ out W₂ (Pres.comp h₁ h₂) (by rw [hout]; simp; ring) ?_
        rw [hval, nv_map h₁, nv_cons, hBi]
        ring

/-- The schoolbook product of the limb lists `xs` and `ys`, as
    `xs.length + ys.length` limbs. -/
def prodNK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  match ys with
  | [] => k (fun v => v) []
  | y :: ys =>
    mulRowK xs y fun r₁ a =>
    prodAccK r₁ 1 (xs.map (fun v => r₁ v)) ys a fun r₂ out => k (fun v => r₂ (r₁ v)) out

theorem prodNK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = n) (hys : 0 < ys.length)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n + ys.length →
      nv W' out = nv W xs * nv W ys → (k r out).denote W' = G) :
    (prodNK xs ys k).denote W = G := by
  obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_pos hys
  rw [prodNK]
  refine mulRowK_denote xs y _ W G fun r₁ a W₁ h₁ ha hav => ?_
  have hy := (lk y W).isLt
  refine prodAccK_denote (n := n) W ys r₁ 1 _ a _ W₁ G (lk y W).toNat h₁ (by simp [hxs])
    (by rw [ha, hxs]; ring) (by simpa using hy) (by rw [hav, nv_map h₁]) fun r₂ out W₂ h₂ hout
      hval => ?_
  refine hk _ out W₂ (Pres.comp h₁ h₂) (by rw [hout]; simp; ring) ?_
  rw [hval, nv_map h₁, nv_cons]

/-! ## 4a. The squaring product -/

/-- The cross sum `∑_{i<j} x_i x_j 2^(64(i+j))` of the limbs `xs` under `W`. -/
def crossV {Δ : Ctxt jasminDialect} (W : Valuation Δ) : List (Var Δ w64) → Nat
  | [] => 0
  | x :: xs => 2 ^ 64 * ((lk x W).toNat * nv W xs) + 2 ^ 128 * crossV W xs

/-- The diagonal sum `∑_i x_i² 2^(128 i)` of the limbs `xs` under `W`. -/
def diagV {Δ : Ctxt jasminDialect} (W : Valuation Δ) : List (Var Δ w64) → Nat
  | [] => 0
  | x :: xs => (lk x W).toNat * (lk x W).toNat + 2 ^ 128 * diagV W xs

/-- The square of a limb value is the diagonal sum plus twice the cross sum. -/
theorem nv_mul_self {Δ : Ctxt jasminDialect} (W : Valuation Δ) :
    ∀ xs : List (Var Δ w64), nv W xs * nv W xs = diagV W xs + 2 * crossV W xs
  | [] => rfl
  | x :: xs => by
      have ih := nv_mul_self W xs
      simp only [nv_cons, diagV, crossV]
      linear_combination 2 ^ 128 * ih

/-- The diagonal squares of the limbs `xs` (renamed by `ren`): for each limb `x`, the low
    and high words of `x · x`, as the `2 · xs.length` limbs `lo₀, hi₀, lo₁, hi₁, …`. -/
def diagK : {Γ Δ : Ctxt jasminDialect} → {ts : List JasminTy} → Ctxt.Hom Γ Δ →
    List (Var Γ w64) →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts) → MC Δ ts
  | _, _, _, _, [], k => k (fun v => v) []
  | _, _, _, ren, x :: xs, k =>
      bindK (eBin .mul (ren x) (ren x)) fun r₁ lo =>
      bindK (eMulhi (r₁ (ren x)) (r₁ (ren x))) fun r₂ hi =>
      diagK (fun v => r₂ (r₁ (ren v))) xs fun r₃ out =>
        k (fun v => r₃ (r₂ (r₁ v))) (r₃ (r₂ lo) :: r₃ hi :: out)

theorem diagK_denote : ∀ {Γ Δ : Ctxt jasminDialect} {ts : List JasminTy} (ren : Ctxt.Hom Γ Δ)
    (xs : List (Var Γ w64))
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts)
    (W : Valuation Γ) (W₀ : Valuation Δ) (G : ListDenote ts),
    Pres ren W W₀ →
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (out : List (Var Δ' w64))
        (W' : Valuation Δ'), Pres r W₀ W' → out.length = 2 * xs.length →
        nv W' out = diagV W xs → (k r out).denote W' = G) →
    (diagK ren xs k).denote W₀ = G
  | _, _, _, _, [], k, W, W₀, G, _, hk => by
      rw [diagK]
      exact hk _ [] W₀ (Pres.id W₀) rfl rfl
  | _, _, _, ren, x :: xs, k, W, W₀, G, hren, hk => by
      rw [diagK]
      refine bindK_denote _ _ _ _ fun r₁ lo W₁ h₁ hlo => ?_
      refine bindK_denote _ _ _ _ fun r₂ hi W₂ h₂ hhi => ?_
      have ex : lk (ren x) W₀ = lk x W := hren x
      have elo : lk lo W₁ = lk x W * lk x W := by
        rw [show lk lo W₁ = _ from hlo, eBin_denote, ex]; rfl
      have ehi : lk hi W₂ = mulHiW (lk x W) (lk x W) := by
        rw [show lk hi W₂ = _ from hhi, eMulhi_denote,
          show lk (r₁ (ren x)) W₁ = lk x W from (h₁ (ren x)).trans ex]
      have hmx := mulx_toNat (lk x W) (lk x W)
      rw [← elo, ← ehi] at hmx
      refine diagK_denote _ xs _ W W₂ G (Pres.comp (Pres.comp hren h₁) h₂)
        fun r₃ out W₃ h₃ hout hval => ?_
      refine hk _ _ W₃ (Pres.comp (Pres.comp h₁ h₂) h₃) (by simp [hout]; ring) ?_
      rw [nv_cons, nv_cons, show lk (r₃ (r₂ lo)) W₃ = lk lo W₁ from (h₃ _).trans (h₂ lo),
        show lk (r₃ hi) W₃ = lk hi W₂ from h₃ hi, hval, diagV]
      linear_combination hmx

/-- The cross rows of a square: for the limbs `xs` (renamed by `ren`) from position `i`
    of the operand on, the row `x · rest` of each limb `x` and its successors `rest` is
    accumulated into `acc` from position `2i + 1` on. -/
def crossAccK : {Γ Δ : Ctxt jasminDialect} → {ts : List JasminTy} → Ctxt.Hom Γ Δ → Nat →
    List (Var Γ w64) → List (Var Δ w64) →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts) → MC Δ ts
  | _, _, _, _, _, [], acc, k => k (fun v => v) acc
  | _, _, _, _, _, [_], acc, k => k (fun v => v) acc
  | _, _, _, ren, i, x :: y :: ys, acc, k =>
      accK (2 * i + 1) ((y :: ys).map (fun v => ren v)) (ren x) acc fun r₁ a =>
      crossAccK (fun v => r₁ (ren v)) (i + 1) (y :: ys) a fun r₂ out =>
        k (fun v => r₂ (r₁ v)) out

/-- The cross rows add `2^(128 i)` times the cross sum of `xs` to `acc`. The bound
    `acc ≤ L · (L + 2^(64 i) · xs)` with `L < 2^(64 i)` holds for the cross rows of the
    `i` limbs of value `L` before `xs`, and keeps every carry chain from overflowing. -/
theorem crossAccK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (W : Valuation Γ)
    (xs : List (Var Γ w64)) : ∀ {Δ : Ctxt jasminDialect}
    (ren : Ctxt.Hom Γ Δ) (i : Nat) (acc : List (Var Δ w64))
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → List (Var Δ' w64) → MC Δ' ts)
    (W₀ : Valuation Δ) (G : ListDenote ts) (L : Nat),
    Pres ren W W₀ → acc.length = 2 * i + xs.length → 0 < xs.length → L < 2 ^ (64 * i) →
    nv W₀ acc ≤ L * (L + 2 ^ (64 * i) * nv W xs) →
    (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (out : List (Var Δ' w64))
      (W' : Valuation Δ'), Pres r W₀ W' → out.length = acc.length + xs.length - 1 →
      nv W' out = nv W₀ acc + 2 ^ (64 * i) * 2 ^ (64 * i) * crossV W xs →
      (k r out).denote W' = G) →
    (crossAccK ren i xs acc k).denote W₀ = G := by
  induction xs with
  | nil =>
    intro Δ ren i acc k W₀ G L _ _ h0
    simp at h0
  | cons x xs ih =>
    intro Δ ren i acc k W₀ G L hren hacc _ hL hv hk
    cases xs with
    | nil =>
      rw [crossAccK]
      exact hk _ acc W₀ (Pres.id W₀) (by simp) (by simp [crossV, nv_nil])
    | cons y ys =>
      rw [crossAccK]
      have hX : (lk x W).toNat < 2 ^ 64 := (lk x W).isLt
      have hRl : nv W (y :: ys) < 2 ^ (64 * (ys.length + 1)) := by
        simpa using nv_lt W (y :: ys)
      have ex : (lk (ren x) W₀).toNat = (lk x W).toNat := by
        rw [show lk (ren x) W₀ = lk x W from hren x]
      have e1 : 2 ^ (64 * (2 * i + 1)) = 2 ^ (64 * i) * 2 ^ (64 * i) * 2 ^ 64 := by
        rw [← Nat.pow_add, ← Nat.pow_add]
        ring_nf
      have e2 : 2 ^ (64 * (ys.length + 1 + 1)) = 2 ^ (64 * (ys.length + 1)) * 2 ^ 64 :=
        two_pow_succ _
      have e3 : 2 ^ (64 * (i + 1)) = 2 ^ (64 * i) * 2 ^ 64 := two_pow_succ _
      have hcx : crossV W (x :: y :: ys)
          = 2 ^ 64 * ((lk x W).toNat * nv W (y :: ys)) + 2 ^ 128 * crossV W (y :: ys) := rfl
      rw [nv_cons] at hv
      generalize 2 ^ (64 * i) = B at hL hv e1 e3 hk
      generalize hR : nv W (y :: ys) = R at hRl hv hcx
      generalize (lk x W).toNat = xv at hX ex hv hcx
      have key : nv W₀ acc + B * B * 2 ^ 64 * (R * xv)
          ≤ (L + B * xv) * (L + B * xv + B * 2 ^ 64 * R) := by
        nlinarith [Nat.zero_le (B * xv * L), Nat.zero_le (B * B * xv * xv)]
      have hL' : L + B * xv < B * 2 ^ 64 := by
        have : B * xv ≤ B * (2 ^ 64 - 1) := Nat.mul_le_mul_left _ (by omega)
        omega
      refine accK_denote_n (n := ys.length + 1) (2 * i + 1) ((y :: ys).map (fun v => ren v))
        (ren x) acc _ W₀ G (by simp) (by simp at hacc ⊢; omega) ?_
        fun r₁ a W₁ h₁ ha hav => ?_
      · rw [nv_map hren, ex, e1, e2, hR]
        have hX' : L + B * xv + B * 2 ^ 64 * R < B * 2 ^ 64 * 2 ^ (64 * (ys.length + 1)) := by
          have : B * 2 ^ 64 * (R + 1) ≤ B * 2 ^ 64 * 2 ^ (64 * (ys.length + 1)) :=
            Nat.mul_le_mul_left _ hRl
          rw [Nat.mul_add, Nat.mul_one] at this
          omega
        have hlt := Nat.mul_lt_mul'' hL' hX'
        calc nv W₀ acc + B * B * 2 ^ 64 * (R * xv)
            ≤ (L + B * xv) * (L + B * xv + B * 2 ^ 64 * R) := key
          _ < B * 2 ^ 64 * (B * 2 ^ 64 * 2 ^ (64 * (ys.length + 1))) := hlt
          _ = B * B * 2 ^ 64 * (2 ^ (64 * (ys.length + 1)) * 2 ^ 64) := by ring
      · rw [nv_map hren, ex, e1, hR] at hav
        refine ih (fun v => r₁ (ren v)) (i + 1) a _ W₁ G (L + B * xv) (Pres.comp hren h₁)
          (by simp at ha hacc ⊢; omega) (by simp) (by rw [e3]; exact hL') ?_
          fun r₂ out W₂ h₂ hout hval => ?_
        · rw [hav, e3, hR]
          linarith [key]
        · refine hk _ out W₂ (Pres.comp h₁ h₂) ?_ ?_
          · rw [hout, ha, hacc]
            simp
            omega
          · rw [hval, hav, e3, hcx]
            ring

/-- The square of the limb list `xs`, as `2 · xs.length` limbs: each cross product
    `x_i · x_j` (`i < j`) is formed once by the cross rows, their sum is doubled by one
    carry chain, and the diagonal squares `x_i · x_i` are added by a second. -/
def sqrNK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  match xs with
  | [] => k (fun v => v) []
  | [x] => diagK (fun v => v) [x] fun r out => k r out
  | x :: y :: ys =>
    mulRowK (y :: ys) x fun r₁ row =>
    bindK (eConst 0) fun r₂ z =>
    crossAccK (fun v => r₂ (r₁ v)) 1 (y :: ys) (z :: row.map (fun v => r₂ v)) fun r₃ C =>
    addK (C ++ [r₃ z]) (C ++ [r₃ z]) fun r₄ D _ =>
    diagK (fun v => r₄ (r₃ (r₂ (r₁ v)))) (x :: y :: ys) fun r₅ S =>
    addK (D.map (fun v => r₅ v)) S fun r₆ T _ =>
    k (fun v => r₆ (r₅ (r₄ (r₃ (r₂ (r₁ v)))))) T

theorem sqrNK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = n)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n + n →
      nv W' out = nv W xs * nv W xs → (k r out).denote W' = G) :
    (sqrNK xs k).denote W = G := by
  subst hxs
  rcases xs with _ | ⟨x, _ | ⟨y, ys⟩⟩
  · exact hk _ [] W (Pres.id W) rfl (by simp [nv_nil])
  · refine diagK_denote (fun v => v) [x] _ W W G (Pres.id W)
      fun r out W' hr hout hv => hk r out W' hr (by simpa using hout) ?_
    rw [hv, nv_mul_self]
    simp [crossV, nv_nil]
  · rw [sqrNK]
    refine mulRowK_denote (y :: ys) x _ W G fun r₁ row W₁ h₁ hrow hrowv => ?_
    refine bindK_denote _ _ _ _ fun r₂ z W₂ h₂ hz => ?_
    have ez : (lk z W₂).toNat = 0 := by rw [show lk z W₂ = _ from hz, eConst_denote]; rfl
    have hX := (lk x W).isLt
    refine crossAccK_denote W (y :: ys) (fun v => r₂ (r₁ v)) 1 _ _ W₂ G (lk x W).toNat
      (Pres.comp h₁ h₂) (by simp [hrow]; omega) (by simp) (by simpa using hX) ?_
      fun r₃ C W₃ h₃ hC hCv => ?_
    · rw [nv_cons, ez, nv_map h₂, hrowv, Nat.mul_one]
      nlinarith [Nat.zero_le ((lk x W).toNat * (lk x W).toNat)]
    have hcross : nv W₃ C = crossV W (x :: y :: ys) := by
      rw [hCv, nv_cons, ez, nv_map h₂, hrowv]
      simp only [crossV]
      ring
    have hCl : C.length + 1 = 2 * (ys.length + 2) := by simp [hrow] at hC; omega
    have hsq := nv_mul_self W (x :: y :: ys)
    have hXl := nv_lt W (x :: y :: ys)
    have hsqlt := Nat.mul_lt_mul'' hXl hXl
    have hBB : 2 ^ (64 * (x :: y :: ys).length) * 2 ^ (64 * (x :: y :: ys).length)
        = 2 ^ (64 * (C.length + 1)) := by
      rw [← Nat.pow_add, hCl]
      simp only [List.length_cons]
      ring_nf
    rw [hBB] at hsqlt
    have ez3 : (lk (r₃ z) W₃).toNat = 0 := by rw [show lk (r₃ z) W₃ = lk z W₂ from h₃ z, ez]
    refine addK_denote (C ++ [r₃ z]) (C ++ [r₃ z]) _ W₃ G rfl
      fun r₄ D c W₄ h₄ hD hDv => ?_
    rw [nv_append, nv_cons, nv_nil, ez3, hcross] at hDv
    simp only [List.length_append, List.length_singleton, Nat.mul_zero, Nat.add_zero] at hDv hD
    have hc := (lk1 c W₄).isLt
    have hD2 : nv W₄ D = 2 * crossV W (x :: y :: ys) := by
      have : (lk1 c W₄).toNat = 0 := by
        by_contra hne
        have : 2 ^ (64 * (C.length + 1)) * 1 ≤ 2 ^ (64 * (C.length + 1)) * (lk1 c W₄).toNat :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      rw [this] at hDv
      omega
    refine diagK_denote _ (x :: y :: ys) _ W W₄ G
      (Pres.comp (Pres.comp (Pres.comp h₁ h₂) h₃) h₄)
      fun r₅ S W₅ h₅ hS hSv => ?_
    refine addK_denote (D.map (fun v => r₅ v)) S _ W₅ G (by simp [hD, hS]; omega)
      fun r₆ T c' W₆ h₆ hT hTv => ?_
    refine hk _ T W₆ (Pres.comp (Pres.comp (Pres.comp (Pres.comp (Pres.comp h₁ h₂) h₃) h₄) h₅) h₆)
      (by simp [hT, hD]; omega) ?_
    rw [nv_map h₅, hSv, hD2] at hTv
    simp only [List.length_map, hD] at hTv
    have hc' := (lk1 c' W₆).isLt
    have : (lk1 c' W₆).toNat = 0 := by
      by_contra hne
      have : 2 ^ (64 * (C.length + 1)) * 1 ≤ 2 ^ (64 * (C.length + 1)) * (lk1 c' W₆).toNat :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    rw [this] at hTv
    omega

/-! ## 5. Montgomery reduction -/

/-- One word of Montgomery reduction on `2n + 1` limbs `acc` of value `A`: the digit
    `m = (A mod 2^64) · nInv mod 2^64`, the sum `A + m p` (whose low limb is zero),
    and its upper `2n` limbs followed by a zero limb. -/
def redcStepK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (acc : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  bindK (eConst 0) fun r₁ z =>
  bindK (eConst P.nInv) fun r₂ ni =>
  bindK (eBin .mul ((acc.map fun v => r₂ (r₁ v)).headD (r₂ z)) ni) fun r₃ m =>
  constsK (digits n P.p) fun r₄ PL =>
  mulRowK PL (r₄ m) fun r₅ row =>
  addK (acc.map fun v => r₅ (r₄ (r₃ (r₂ (r₁ v)))))
    (row ++ List.replicate n (r₅ (r₄ (r₃ (r₂ z))))) fun r₆ S _ =>
  k (fun v => r₆ (r₅ (r₄ (r₃ (r₂ (r₁ v)))))) (S.tail ++ [r₆ (r₅ (r₄ (r₃ (r₂ z))))])

theorem redcStepK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (acc : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hlen : acc.length = 2 * n + 1)
    (hA : nv W acc < 2 ^ (64 * n) * 2 ^ (64 * n))
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 2 * n + 1 →
      (∃ m, m < 2 ^ 64 ∧ nv W' out * 2 ^ 64 = nv W acc + m * P.p) →
      (k r out).denote W' = G) :
    (redcStepK P acc k).denote W = G := by
  have hp := P.p_lt
  have hB := two_pow_le P
  obtain ⟨x, rest, rfl⟩ : ∃ x rest, acc = x :: rest := by
    cases acc with
    | nil => simp at hlen
    | cons x rest => exact ⟨x, rest, rfl⟩
  refine bindK_denote _ _ _ _ fun r₁ z W₁ h₁ hz => ?_
  refine bindK_denote _ _ _ _ fun r₂ ni W₂ h₂ hni => ?_
  refine bindK_denote _ _ _ _ fun r₃ m W₃ h₃ hm => ?_
  have ez : (lk z W₁).toNat = 0 := by rw [show lk z W₁ = _ from hz, eConst_denote]; rfl
  have eni : (lk ni W₂).toNat = P.nInv := by
    rw [show lk ni W₂ = _ from hni, eConst_denote, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt P.nInv_lt
  have ex : (lk (r₂ (r₁ x)) W₂).toNat = nv W (x :: rest) % 2 ^ 64 := by
    rw [show lk (r₂ (r₁ x)) W₂ = lk x W from (h₂ _).trans (h₁ x)]
    exact nv_cons_mod W x rest
  set M := nv W (x :: rest) % 2 ^ 64 * P.nInv % 2 ^ 64 with hM
  have em : (lk m W₃).toNat = M := by
    rw [show lk m W₃ = _ from hm, List.map_cons, List.headD_cons, eBin_denote]
    show (lk (r₂ (r₁ x)) W₂ * lk ni W₂).toNat = M
    rw [BitVec.toNat_mul, ex, eni]
  refine constsK_denote _ _ W₃ G (digits_lt _ _) fun r₄ PL W₄ h₄ hPL hPLv => ?_
  rw [limbsNat_digits _ _ hp] at hPLv
  rw [digits_length] at hPL
  refine mulRowK_denote PL (r₄ m) _ W₄ G fun r₅ row W₅ h₅ hrow hrowv => ?_
  rw [hPLv, show lk (r₄ m) W₄ = lk m W₃ from h₄ m, em] at hrowv
  have ez5 : (lk (r₅ (r₄ (r₃ (r₂ z)))) W₅).toNat = 0 := by
    rw [show lk (r₅ (r₄ (r₃ (r₂ z)))) W₅ = lk z W₁ from
      (h₅ _).trans ((h₄ _).trans ((h₃ _).trans (h₂ z))), ez]
  have h1to5 : Pres (fun v => r₅ (r₄ (r₃ (r₂ (r₁ v))))) W W₅ :=
    Pres.comp (Pres.comp (Pres.comp (Pres.comp h₁ h₂) h₃) h₄) h₅
  refine addK_denote _ _ _ W₅ G (by simp only [List.length_map, List.length_append,
    List.length_replicate, hrow, hPL]; omega) fun r₆ S c W₆ h₆ hS hSv => ?_
  rw [nv_map h1to5, nv_append, nv_replicate W₅ _ ez5, hrowv] at hSv
  simp only [List.length_map, hlen, Nat.mul_zero, Nat.add_zero] at hSv hS
  have hMlt : M < 2 ^ 64 := Nat.mod_lt _ (by norm_num)
  have hMp : P.p * M < 2 ^ (64 * n) * 2 ^ 64 := Nat.mul_lt_mul'' hp hMlt
  have hBB : 2 ^ (64 * n) * 2 ^ 64 ≤ 2 ^ (64 * n) * 2 ^ (64 * n) := Nat.mul_le_mul_left _ hB
  have hQ : 2 ^ (64 * (2 * n + 1)) = 2 ^ (64 * n) * 2 ^ (64 * n) * 2 ^ 64 := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    ring_nf
  have hc := (lk1 c W₆).isLt
  have hS0 : nv W₆ S = nv W (x :: rest) + P.p * M := by
    have : (lk1 c W₆).toNat = 0 := by
      by_contra hne
      have : 2 ^ (64 * (2 * n + 1)) * 1 ≤ 2 ^ (64 * (2 * n + 1)) * (lk1 c W₆).toNat :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    rw [this] at hSv
    omega
  obtain ⟨s₀, St, rfl⟩ : ∃ s₀ St, S = s₀ :: St := by
    cases S with
    | nil => simp at hS
    | cons s₀ St => exact ⟨s₀, St, rfl⟩
  have hdig : (nv W (x :: rest) + M * P.p) % 2 ^ 64 = 0 := redc_digit P _
  have hs₀ : (lk s₀ W₆).toNat = 0 := by
    rw [nv_cons_mod W₆ s₀ St, hS0, Nat.mul_comm P.p M, hdig]
  have hz6 : (lk (r₆ (r₅ (r₄ (r₃ (r₂ z))))) W₆).toNat = 0 := by
    rw [show lk (r₆ (r₅ (r₄ (r₃ (r₂ z))))) W₆ = lk (r₅ (r₄ (r₃ (r₂ z)))) W₅ from h₆ _, ez5]
  refine hk _ _ W₆ (Pres.comp h1to5 h₆) (by simp at hS ⊢; omega) ⟨M, hMlt, ?_⟩
  rw [List.tail_cons, nv_append, nv_cons, nv_nil, hz6]
  rw [nv_cons, hs₀] at hS0
  simp only [Nat.mul_zero, Nat.add_zero]
  rw [Nat.mul_comm M P.p]
  omega

/-- One reduction word keeps the accumulator below `B²` for a radix power `B ≥ 2^64`
    above `p`. -/
theorem redc_step_bound (B p A A' m : Nat) (hB : 2 ^ 64 ≤ B) (hp : p < B) (hA : A < B * B)
    (hm : m < 2 ^ 64) (e : A' * 2 ^ 64 = A + m * p) : A' < B * B := by
  have h1 : m * p < 2 ^ 64 * B := Nat.mul_lt_mul'' hm hp
  have h2 : 2 ^ 64 * B ≤ B * B := Nat.mul_le_mul_right _ hB
  by_contra h
  have h' : B * B * 2 ^ 64 ≤ A' * 2 ^ 64 := Nat.mul_le_mul_right _ (Nat.le_of_not_lt h)
  omega

/-- `s` words of Montgomery reduction (fiat-crypto's `redc_loop`). -/
def redcChainK : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → Nat →
    List (Var Γ w64) →
    (∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) → MC Γ ts
  | _, _, 0, acc, k => k (fun v => v) acc
  | _, _, s + 1, acc, k =>
      redcStepK P acc fun r₁ A =>
      redcChainK s A fun r₂ out => k (fun v => r₂ (r₁ v)) out

/-- `s` words of Montgomery reduction from `A < 2^(128n)` give `out · 2^(64s) = A + M p`
    with `M < 2^(64s)` (fiat-crypto's `snd_redc_loop_mod_N`). -/
theorem redcChainK_denote : ∀ (s : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (acc : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts),
    acc.length = 2 * n + 1 → nv W acc < 2 ^ (64 * n) * 2 ^ (64 * n) →
    (∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = 2 * n + 1 →
      nv W' out < 2 ^ (64 * n) * 2 ^ (64 * n) →
      (∃ M, M < 2 ^ (64 * s) ∧ nv W' out * 2 ^ (64 * s) = nv W acc + M * P.p) →
      (k r out).denote W' = G) →
    (redcChainK P s acc k).denote W = G
  | 0, _, _, acc, _, W, _, hlen, hA, hk => by
      rw [redcChainK]
      exact hk _ acc W (Pres.id W) hlen hA ⟨0, by simp, by simp⟩
  | s + 1, _, _, acc, k, W, G, hlen, hA, hk => by
      rw [redcChainK]
      refine redcStepK_denote P acc _ W G hlen hA fun r₁ A₁ W₁ h₁ hA₁ ⟨m, hm, e₁⟩ => ?_
      have hb := redc_step_bound _ _ _ _ _ (two_pow_le P) P.p_lt hA hm e₁
      refine redcChainK_denote s A₁ _ W₁ G hA₁ hb
        fun r₂ out W₂ h₂ hout hlt ⟨M, hM, e₂⟩ => ?_
      refine hk _ out W₂ (Pres.comp h₁ h₂) hout hlt ⟨m + 2 ^ 64 * M, ?_, ?_⟩
      · rw [two_pow_succ]
        omega
      · rw [two_pow_succ]
        linear_combination 2 ^ 64 * e₂ + e₁

/-- After `n` reduction words from `T < p²` the result is below `2p` (fiat-crypto's
    `redc_loop_bound`). -/
theorem redc_bound (B p T A M : Nat) (hT : T < p * p) (hp : p < B) (hM : M < B)
    (e : A * B = T + M * p) : A < 2 * p := by
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h; simp at hT
    · exact h
  have h1 : M * p < B * p := Nat.mul_lt_mul_of_pos_right hM hp0
  have h2 : p * p ≤ B * p := Nat.mul_le_mul_right _ hp.le
  have h3 : 2 * p * B = B * p + B * p := by ring
  have h4 : A * B < 2 * p * B := by omega
  exact Nat.lt_of_mul_lt_mul_right h4

/-- `n` words of Montgomery reduction of the `2n` limbs `T` extended by a zero limb, and
    one conditional subtraction on the low `n + 1` limbs. -/
def redcFinK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (T : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  bindK (eConst 0) fun r₂ z =>
  redcChainK P n (T.map (fun v => r₂ v) ++ [z]) fun r₃ A =>
  csubPCK P (A.take (n + 1)) fun r₄ out =>
  k (fun v => r₄ (r₃ (r₂ v))) out

theorem redcFinK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (T : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hT : T.length = 2 * n)
    (hTv : nv W T < P.p * P.p)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n → nv W' out < P.p →
      nv W' out * 2 ^ (64 * n) ≡ nv W T [MOD P.p] →
      (k r out).denote W' = G) :
    (redcFinK P T k).denote W = G := by
  have hp := P.p_lt
  have hB := two_pow_le P
  have hB1 := two_pow_succ n
  have hn := n_pos P
  have hTB : nv W T < 2 ^ (64 * n) * 2 ^ (64 * n) :=
    lt_of_lt_of_le hTv (Nat.mul_le_mul hp.le hp.le)
  refine bindK_denote _ _ _ _ fun r₂ z W₂ h₂ hz => ?_
  have ez : (lk z W₂).toNat = 0 := by rw [show lk z W₂ = _ from hz, eConst_denote]; rfl
  have hA0 : nv W₂ (T.map (fun v => r₂ v) ++ [z]) = nv W T := by
    rw [nv_append, nv_map h₂, nv_cons, nv_nil, ez]
    simp
  refine redcChainK_denote P n _ _ W₂ G (by simp [hT]) (by rw [hA0]; exact hTB)
    fun r₃ A W₃ h₃ hA _ ⟨M, hM, e⟩ => ?_
  rw [hA0] at e
  have hlt : nv W₃ A < 2 * P.p := redc_bound _ _ _ _ _ hTv hp hM e
  have htake : nv W₃ (A.take (n + 1)) = nv W₃ A :=
    nv_take W₃ A (n + 1) (by omega) (by omega)
  have hlt' : nv W₃ (A.take (n + 1)) < P.p + 2 ^ (64 * n) := by
    rw [htake]
    omega
  refine csubPCK_denote P (A.take (n + 1)) _ W₃ G (by simp [hA]; omega) hlt'
    fun r₄ out W₄ h₄ hout hv => ?_
  refine hk _ out W₄ (Pres.comp (Pres.comp h₂ h₃) h₄) hout ?_ ?_
  · rw [hv, htake, csub_eq_mod P _ hlt]
    exact Nat.mod_lt _ (Nat.lt_trans Nat.zero_lt_one P.one_lt)
  · rw [hv, htake, csub_eq_mod P _ hlt]
    unfold Nat.ModEq
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, e, Nat.add_mul_mod_self_right]

/-- Montgomery multiplication on `n` limbs: the schoolbook product, `n` words of
    Montgomery reduction, and one conditional subtraction on the low `n + 1` limbs. -/
def mulMK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  prodNK xs ys fun r₁ T =>
  bindK (eConst 0) fun r₂ z =>
  redcChainK P n (T.map (fun v => r₂ v) ++ [z]) fun r₃ A =>
  csubPCK P (A.take (n + 1)) fun r₄ out =>
  k (fun v => r₄ (r₃ (r₂ (r₁ v)))) out

theorem mulMK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = n) (hys : ys.length = n)
    (hx : nv W xs < P.p) (hy : nv W ys < P.p)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n → nv W' out < P.p →
      nv W' out * 2 ^ (64 * n) ≡ nv W xs * nv W ys [MOD P.p] →
      (k r out).denote W' = G) :
    (mulMK P xs ys k).denote W = G := by
  have hn := n_pos P
  refine prodNK_denote xs ys _ W G hxs (by omega) fun r₁ T W₁ h₁ hT hTv => ?_
  exact redcFinK_denote P T (fun r out => k (fun v => r (r₁ v)) out) W₁ G
    (by rw [hT, hys]; ring) (by rw [hTv]; exact Nat.mul_lt_mul'' hx hy)
    fun r out W' hr hout hlt hmod => hk _ out W' (Pres.comp h₁ hr) hout hlt (by rwa [hTv] at hmod)

/-- Montgomery squaring on `n` limbs: the squaring product, `n` words of Montgomery
    reduction, and one conditional subtraction on the low `n + 1` limbs. -/
def sqrMK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  sqrNK xs fun r₁ T => redcFinK P T fun r₂ out => k (fun v => r₂ (r₁ v)) out

theorem sqrMK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = n) (hx : nv W xs < P.p)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n → nv W' out < P.p →
      nv W' out * 2 ^ (64 * n) ≡ nv W xs * nv W xs [MOD P.p] →
      (k r out).denote W' = G) :
    (sqrMK P xs k).denote W = G :=
  sqrNK_denote xs _ W G hxs fun r₁ T W₁ h₁ hT hTv =>
    redcFinK_denote P T _ W₁ G (by rw [hT]; ring) (by rw [hTv]; exact Nat.mul_lt_mul'' hx hx)
      fun r₂ out W₂ h₂ hout hlt hmod =>
        hk _ out W₂ (Pres.comp h₁ h₂) hout hlt (by rwa [hTv] at hmod)

/-! ## 6. The Montgomery encoding -/

instance : NeZero P.p := ⟨by have := P.one_lt; omega⟩

/-- The Montgomery factor `2^(64n)` in `ZMod p`. -/
def R : ZMod P.p := 2 ^ (64 * n)

theorem isUnit_R : IsUnit (R P) := by
  have h2 : IsUnit ((2 : Nat) : ZMod P.p) :=
    (ZMod.isUnit_iff_coprime 2 P.p).mpr (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr P.p_odd))
  rw [Nat.cast_ofNat] at h2
  exact h2.pow (64 * n)

/-- The encoding of `ZMod p`: the `n` limbs of the canonical representative of the
    Montgomery form `x · 2^(64n)`. -/
def enc (x : ZMod P.p) : ListDenote (Rn n) := limbsN n (x * R P).val

theorem val_lt (x : ZMod P.p) : x.val < P.p := ZMod.val_lt x

theorem val_lt_two_pow (x : ZMod P.p) : x.val < 2 ^ (64 * n) :=
  lt_trans (ZMod.val_lt x) P.p_lt

theorem enc_injective : Function.Injective (enc P) := fun x y h => by
  have hv := limbsN_injective (val_lt_two_pow P _) (val_lt_two_pow P _) h
  have := ZMod.val_injective _ hv
  exact (isUnit_R P).mul_right_cancel this

/-- A value `V < p` with `V · 2^(64n) ≡ (x R).val · (y R).val (mod p)` is the canonical
    representative of the Montgomery form of `x * y`. -/
theorem mont_val_eq (x y : ZMod P.p) (V : Nat) (hlt : V < P.p)
    (hmod : V * 2 ^ (64 * n) ≡ (x * R P).val * (y * R P).val [MOD P.p]) :
    V = (x * y * R P).val := by
  have hc := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_val, ZMod.cast_id',
    id] at hc
  have hR : ((V : Nat) : ZMod P.p) = x * y * R P := by
    refine (isUnit_R P).mul_right_cancel ?_
    rw [show R P = 2 ^ (64 * n) from rfl] at hc ⊢
    rw [hc]
    ring
  rw [← hR, ZMod.val_natCast_of_lt hlt]

/-- On the Montgomery forms of `x` and `y`, `mulMK` gives the Montgomery form of
    `x * y`. -/
theorem mulMK_denote_enc {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = n) (hys : ys.length = n)
    (x y : ZMod P.p) (hx : nv W xs = (x * R P).val) (hy : nv W ys = (y * R P).val)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n → nv W' out = (x * y * R P).val →
      (k r out).denote W' = G) :
    (mulMK P xs ys k).denote W = G := by
  refine mulMK_denote P xs ys k W G hxs hys (by rw [hx]; exact val_lt P _)
    (by rw [hy]; exact val_lt P _) fun r out W' hr hout hlt hmod => hk r out W' hr hout ?_
  rw [hx, hy] at hmod
  exact mont_val_eq P x y _ hlt hmod

/-- On the Montgomery form of `x`, `sqrMK` gives the Montgomery form of `x * x`. -/
theorem sqrMK_denote_enc {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (xs : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = n)
    (x : ZMod P.p) (hx : nv W xs = (x * R P).val)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n → nv W' out = (x * x * R P).val →
      (k r out).denote W' = G) :
    (sqrMK P xs k).denote W = G := by
  refine sqrMK_denote P xs k W G hxs (by rw [hx]; exact val_lt P _)
    fun r out W' hr hout hlt hmod => hk r out W' hr hout ?_
  rw [hx] at hmod
  exact mont_val_eq P x x _ hlt hmod

/-! ## 7. The blocks -/

section Blocks

variable {Γ : Ctxt jasminDialect}

/-- The addition block over the limb lists `xs` and `ys`. -/
def addBlk (xs ys : List (Var Γ w64)) : MC Γ (Rn n) :=
  addMK P xs ys fun _ out => retN n out

/-- The Montgomery multiplication block. -/
def mulBlk (xs ys : List (Var Γ w64)) : MC Γ (Rn n) :=
  mulMK P xs ys fun _ out => retN n out

/-- The Montgomery squaring block. -/
def sqrBlk (xs : List (Var Γ w64)) : MC Γ (Rn n) :=
  sqrMK P xs fun _ out => retN n out

/-- The constant block: the `k` 64-bit digits of `v` as `regConst` bindings. -/
def constBlk (k v : Nat) : MC Γ (Rn k) :=
  constsK (digits k v) fun _ out => retN k out

variable (W : Valuation Γ)

theorem addBlk_denote (xs ys : List (Var Γ w64)) (hxs : xs.length = n) (hys : ys.length = n)
    (x y : ZMod P.p) (hx : nv W xs = (x * R P).val) (hy : nv W ys = (y * R P).val) :
    (addBlk P xs ys).denote W = enc P (x + y) := by
  refine addMK_denote P _ _ _ W _ hxs hys (by rw [hx]; exact val_lt P _)
    (by rw [hy]; exact val_lt P _) fun r out W' _ hout hv => ?_
  rw [retN_denote _ out W' hout, hv, hx, hy, enc, add_mul, ZMod.val_add]

theorem mulBlk_denote (xs ys : List (Var Γ w64)) (hxs : xs.length = n) (hys : ys.length = n)
    (x y : ZMod P.p) (hx : nv W xs = (x * R P).val) (hy : nv W ys = (y * R P).val) :
    (mulBlk P xs ys).denote W = enc P (x * y) := by
  refine mulMK_denote_enc P _ _ _ W _ hxs hys x y hx hy fun r out W' _ hout hv => ?_
  rw [retN_denote _ out W' hout, hv, enc]

theorem sqrBlk_denote (xs : List (Var Γ w64)) (hxs : xs.length = n) (x : ZMod P.p)
    (hx : nv W xs = (x * R P).val) :
    (sqrBlk P xs).denote W = enc P (x * x) := by
  refine sqrMK_denote_enc P _ _ W _ hxs x hx fun r out W' _ hout hv => ?_
  rw [retN_denote _ out W' hout, hv, enc]

theorem constBlk_denote (k v : Nat) : (constBlk (Γ := Γ) k v).denote W = limbsN k v := by
  refine constsK_denote _ _ W _ (digits_lt k v) fun r out W' _ hout hv => ?_
  rw [retN_denote _ out W' (hout.trans (digits_length k v)), hv, limbsNat_digits_mod,
    limbsN_mod]

end Blocks

/-! ## 8. Subtraction and negation -/

/-- The canonical representative of a difference: `b.val` subtracted from `a.val`,
    with `p` added when `b.val > a.val`. -/
theorem val_sub_eq (a b : ZMod P.p) :
    (a - b).val = if b.val ≤ a.val then a.val - b.val else a.val + P.p - b.val := by
  have ha := val_lt P a
  have hb := val_lt P b
  have key : ∀ m : Nat, m < P.p → (m : ZMod P.p) = a - b → (a - b).val = m :=
    fun m hm h => by rw [← h, ZMod.val_natCast_of_lt hm]
  split_ifs with h
  · refine key _ (by omega) ?_
    rw [Nat.cast_sub h, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  · refine key _ (by omega) ?_
    rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      ZMod.natCast_self, add_zero]

/-- Subtraction modulo `p` on `n` limbs: `xs + ¬ys + 1` by the carry chain; when the
    carry is clear, `p` is added, selected by the carry. -/
def subMK {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) : MC Γ ts :=
  bindK (eConst (2 ^ 64 - 1)) fun r₁ m =>
  xorR r₁ m ys fun r₂ ny =>
  bindK (eBit 1) fun r₃ one =>
  adcR (fun v => v) (xs.map (fun v => r₃ (r₂ (r₁ v)))) (ny.map (fun v => r₃ v)) one
    fun r₄ D c =>
  constsK (digits n P.p) fun r₅ PL =>
  addK (D.map (fun v => r₅ v)) PL fun r₆ E _ =>
  selR (fun v => v) (r₆ (r₅ c)) (D.map (fun v => r₆ (r₅ v))) E fun r₇ out =>
  k (fun v => r₇ (r₆ (r₅ (r₄ (r₃ (r₂ (r₁ v))))))) out

theorem subMK_denote {Γ : Ctxt jasminDialect} {ts : List JasminTy} (xs ys : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (hxs : xs.length = n) (hys : ys.length = n)
    (hy : nv W ys < P.p)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n →
      nv W' out = (if nv W ys ≤ nv W xs then nv W xs - nv W ys else nv W xs + P.p - nv W ys) →
      (k r out).denote W' = G) :
    (subMK P xs ys k).denote W = G := by
  have hp := P.p_lt
  refine bindK_denote _ _ _ _ fun r₁ m W₁ h₁ hm => ?_
  refine xorR_denote r₁ m ys _ W W₁ G h₁ hm fun r₂ ny W₂ h₂ hny hnyv => ?_
  refine bindK_denote _ _ _ _ fun r₃ one W₃ h₃ hone => ?_
  have h123 : Pres (fun v => r₃ (r₂ (r₁ v))) W W₃ := Pres.comp (Pres.comp h₁ h₂) h₃
  have eone : (lk1 one W₃).toNat = 1 := by rw [show lk1 one W₃ = _ from hone, eBit_denote]; rfl
  refine adcR_denote (fun v => v) _ _ one _ W₃ W₃ G (Pres.id W₃) (by simp [hxs, hny, hys])
    fun r₄ D c W₄ h₄ hD hDv => ?_
  rw [nv_map h123, nv_map h₃, eone] at hDv
  simp only [List.length_map, hxs] at hDv hD
  rw [hys] at hnyv
  have hX := nv_lt W xs
  rw [hxs] at hX
  refine constsK_denote _ _ W₄ G (digits_lt _ _) fun r₅ PL W₅ h₅ hPL hPLv => ?_
  rw [limbsNat_digits _ _ hp] at hPLv
  refine addK_denote _ PL _ W₅ G (by simp [hD, hPL, digits_length])
    fun r₆ E e W₆ h₆ hE hEv => ?_
  rw [nv_map h₅, hPLv] at hEv
  simp only [List.length_map, hD] at hEv hE
  refine selR_denote (fun v => v) _ _ E _ W₆ W₆ G (Pres.id W₆) (by simp [hE, hD])
    fun r₇ out W₇ h₇ hout hv => ?_
  refine hk _ out W₇ (Pres.comp (Pres.comp (Pres.comp (Pres.comp h123 h₄) h₅) h₆) h₇)
    (by simp [hout, hD]) ?_
  rw [hv, nv_map (Pres.comp h₅ h₆),
    show lk1 (r₆ (r₅ c)) W₆ = lk1 c W₄ from (h₆ _).trans (h₅ c)]
  have hDl := nv_lt W₄ D
  have hEl := nv_lt W₆ E
  rw [hD] at hDl
  rw [hE] at hEl
  have hc2 := (lk1 c W₄).isLt
  have he2 := (lk1 e W₆).isLt
  have he : (lk1 e W₆).toNat = 0 ∨ (lk1 e W₆).toNat = 1 := by omega
  by_cases hc : lk1 c W₄ = 1#1
  · have h1 : (lk1 c W₄).toNat = 1 := by rw [hc]; rfl
    rw [if_pos hc]
    rw [h1, Nat.mul_one] at hDv
    split_ifs <;> omega
  · have h0 : (lk1 c W₄).toNat = 0 := by
      have : (lk1 c W₄).toNat ≠ 1 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
      omega
    rw [if_neg hc]
    rw [h0, Nat.mul_zero, Nat.add_zero] at hDv
    rcases he with he | he <;> rw [he] at hEv <;> simp only [Nat.mul_zero, Nat.add_zero,
      Nat.mul_one] at hEv <;> split_ifs <;> omega

section SubBlocks

variable {Γ : Ctxt jasminDialect}

/-- The subtraction block over the limb lists `xs` and `ys`. -/
def subBlk (xs ys : List (Var Γ w64)) : MC Γ (Rn n) :=
  subMK P xs ys fun _ out => retN n out

/-- The negation block: the subtraction of `xs` from `n` zero limbs. -/
def negBlk (xs : List (Var Γ w64)) : MC Γ (Rn n) :=
  constsK (List.replicate n 0) fun r zs => subBlk P zs (xs.map (fun v => r v))

variable (W : Valuation Γ)

theorem subBlk_denote (xs ys : List (Var Γ w64)) (hxs : xs.length = n) (hys : ys.length = n)
    (a b : ZMod P.p) (hx : nv W xs = a.val) (hy : nv W ys = b.val) :
    (subBlk P xs ys).denote W = limbsN n (a - b).val := by
  refine subMK_denote P _ _ _ W _ hxs hys (by rw [hy]; exact val_lt P b)
    fun r out W' _ hout hv => ?_
  rw [retN_denote _ out W' hout, hv, hx, hy, val_sub_eq]

theorem negBlk_denote (xs : List (Var Γ w64)) (hxs : xs.length = n) (a : ZMod P.p)
    (hx : nv W xs = a.val) :
    (negBlk P xs).denote W = limbsN n (-a).val := by
  refine constsK_denote _ _ W _ (by simp) fun r zs W' hr hzs hzv => ?_
  rw [← zero_sub]
  refine subBlk_denote P W' _ _ (by simpa using hzs) (by simp [hxs]) 0 a ?_ ?_
  · rw [hzv, limbsNat_replicate_zero, ZMod.val_zero]
  · rw [nv_map hr, hx]

/-- On the Montgomery forms of `x` and `y`, the subtraction block gives the Montgomery
    form of `x - y`. -/
theorem subBlk_denote_enc (xs ys : List (Var Γ w64)) (hxs : xs.length = n)
    (hys : ys.length = n) (x y : ZMod P.p) (hx : nv W xs = (x * R P).val)
    (hy : nv W ys = (y * R P).val) :
    (subBlk P xs ys).denote W = enc P (x - y) := by
  rw [enc, sub_mul]
  exact subBlk_denote P W _ _ hxs hys _ _ hx hy

/-- On the Montgomery form of `x`, the negation block gives the Montgomery form of
    `-x`. -/
theorem negBlk_denote_enc (xs : List (Var Γ w64)) (hxs : xs.length = n) (x : ZMod P.p)
    (hx : nv W xs = (x * R P).val) :
    (negBlk P xs).denote W = enc P (-x) := by
  rw [enc, neg_mul]
  exact negBlk_denote P W _ hxs _ hx

end SubBlocks

/-! ## 9. The Montgomery power and the inversion block -/

/-- Left-to-right square-and-multiply over the bits `bs`, most significant first: each
    bit squares the accumulator `acc` and, on `true`, multiplies it by the base `xs`,
    all by Montgomery multiplication. -/
def powK : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → List Bool →
    List (Var Γ w64) → List (Var Γ w64) →
    (∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts) → MC Γ ts
  | _, _, [], _, acc, k => k (fun v => v) acc
  | _, _, b :: bs, xs, acc, k =>
      mulMK P acc acc fun r₁ sq =>
      bif b then
        mulMK P sq (xs.map (fun v => r₁ v)) fun r₂ m =>
        powK bs (xs.map (fun v => r₂ (r₁ v))) m fun r₃ out => k (fun v => r₃ (r₂ (r₁ v))) out
      else
        powK bs (xs.map (fun v => r₁ v)) sq fun r₃ out => k (fun v => r₃ (r₁ v)) out

/-- The value `powK` computes from the accumulator value `u` and the base value `x`. -/
def powVal (x : ZMod P.p) : List Bool → ZMod P.p → ZMod P.p
  | [], u => u
  | b :: bs, u => powVal x bs (bif b then u * u * x else u * u)

/-- The number whose binary digits, most significant first, are `bs`, read after the
    prefix value `m`. -/
def bitsNum : List Bool → Nat → Nat
  | [], m => m
  | b :: bs, m => bitsNum bs (2 * m + b.toNat)

theorem powVal_pow (x : ZMod P.p) : ∀ (bs : List Bool) (m : Nat),
    powVal P x bs (x ^ m) = x ^ bitsNum bs m
  | [], _ => rfl
  | b :: bs, m => by
      rw [powVal, bitsNum, ← powVal_pow x bs]
      congr 1
      cases b <;> simp only [cond_true, cond_false, Bool.toNat_true, Bool.toNat_false] <;> ring

theorem bitsNum_append_single : ∀ (l : List Bool) (b : Bool) (m : Nat),
    bitsNum (l ++ [b]) m = 2 * bitsNum l m + b.toNat
  | [], _, _ => rfl
  | a :: l, b, m => bitsNum_append_single l b (2 * m + a.toNat)

/-- The binary digits of `m`, most significant first. -/
def expBits : Nat → List Bool
  | 0 => []
  | m + 1 => expBits ((m + 1) / 2) ++ [(m + 1) % 2 == 1]
decreasing_by omega

theorem bitsNum_expBits (m : Nat) : bitsNum (expBits m) 0 = m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    cases m with
    | zero => rw [expBits]; rfl
    | succ m =>
      rw [expBits, bitsNum_append_single, ih _ (by omega)]
      rcases Nat.mod_two_eq_zero_or_one (m + 1) with h | h <;> simp [h] <;> omega

/-- On the Montgomery forms of `x` and `u`, `powK` gives the Montgomery form of
    `powVal x bs u`. -/
theorem powK_denote : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (bs : List Bool)
    (xs acc : List (Var Γ w64))
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → List (Var Δ w64) → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (x u : ZMod P.p),
    xs.length = n → acc.length = n → nv W xs = (x * R P).val → nv W acc = (u * R P).val →
    (∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (out : List (Var Δ w64))
      (W' : Valuation Δ), Pres r W W' → out.length = n →
      nv W' out = (powVal P x bs u * R P).val → (k r out).denote W' = G) →
    (powK P bs xs acc k).denote W = G
  | _, _, [], _, acc, _, W, _, _, _, _, hacc, _, hu, hk => hk _ acc W (Pres.id W) hacc hu
  | _, _, b :: bs, xs, acc, k, W, G, x, u, hxs, hacc, hx, hu, hk => by
      rw [powK]
      refine mulMK_denote_enc P acc acc _ W G hacc hacc u u hu hu
        fun r₁ sq W₁ h₁ hsq hsqv => ?_
      cases b with
      | false =>
        exact powK_denote bs _ sq _ W₁ G x (u * u) (by simp [hxs]) hsq
          (by rw [nv_map h₁, hx]) hsqv fun r₃ out W₃ h₃ hout hv =>
            hk _ out W₃ (Pres.comp h₁ h₃) hout hv
      | true =>
        rw [cond_true]
        refine mulMK_denote_enc P sq (xs.map (fun v => r₁ v)) _ W₁ G hsq (by simp [hxs]) (u * u) x hsqv
          (by rw [nv_map h₁, hx]) fun r₂ m W₂ h₂ hm hmv => ?_
        exact powK_denote bs _ m _ W₂ G x (u * u * x) (by simp [hxs]) hm
          (by rw [nv_map (Pres.comp h₁ h₂), hx]) hmv fun r₃ out W₃ h₃ hout hv =>
            hk _ out W₃ (Pres.comp (Pres.comp h₁ h₂) h₃) hout hv

/-- Fermat inversion: at a prime modulus, `x^(p-2) = x⁻¹`, including at `x = 0`. -/
theorem pow_sub_two_eq_inv (hp : P.p.Prime) (x : ZMod P.p) : x ^ (P.p - 2) = x⁻¹ := by
  have := Fact.mk hp
  have h3 : 3 ≤ P.p := by have := hp.two_le; have := P.p_odd; omega
  by_cases hx : x = 0
  · subst hx
    rw [zero_pow (by omega), ZMod.inv_zero]
  · refine (ZMod.inv_eq_of_mul_eq_one _ _ _ ?_).symm
    rw [← pow_succ', show P.p - 2 + 1 = P.p - 1 by omega]
    exact ZMod.pow_card_sub_one_eq_one hx

section Inv

variable {Γ : Ctxt jasminDialect}

/-- The Montgomery inversion block: the Montgomery power of `xs` to the exponent
    `p - 2`, from the Montgomery form of `1`. -/
def invBlk (xs : List (Var Γ w64)) : MC Γ (Rn n) :=
  constsK (digits n (R P).val) fun r₁ one =>
  powK P (expBits (P.p - 2)) (xs.map (fun v => r₁ v)) one fun _ out => retN n out

/-- On the Montgomery form of `x`, the inversion block gives the Montgomery form of
    `x^(p-2)`. -/
theorem invBlk_denote_pow (W : Valuation Γ) (xs : List (Var Γ w64)) (hxs : xs.length = n)
    (x : ZMod P.p) (hx : nv W xs = (x * R P).val) :
    (invBlk P xs).denote W = enc P (x ^ (P.p - 2)) := by
  refine constsK_denote _ _ W _ (digits_lt _ _) fun r₁ one W₁ h₁ hone hv => ?_
  rw [limbsNat_digits _ _ (val_lt_two_pow P _)] at hv
  refine powK_denote P (expBits (P.p - 2)) _ one _ W₁ _ x 1 (by simp [hxs])
    (hone.trans (digits_length _ _)) (by rw [nv_map h₁, hx]) (by rw [hv, one_mul])
    fun r₂ out W₂ _ hout hval => ?_
  rw [enc, retN_denote _ out W₂ hout, hval, ← pow_zero x, powVal_pow, bitsNum_expBits]

/-- At a prime modulus, on the Montgomery form of `x`, the inversion block gives the
    Montgomery form of `x⁻¹`. -/
theorem invBlk_denote_inv (hp : P.p.Prime) (W : Valuation Γ) (xs : List (Var Γ w64))
    (hxs : xs.length = n) (x : ZMod P.p) (hx : nv W xs = (x * R P).val) :
    (invBlk P xs).denote W = enc P x⁻¹ := by
  rw [invBlk_denote_pow P W xs hxs x hx, pow_sub_two_eq_inv P hp]

end Inv

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont
