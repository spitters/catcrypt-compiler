/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs

/-!
# Fixed-size mpn functions as closed limb programs

For a limb count `n`, the GMP functions `mpn_add_n`, `mpn_sub_n`, `mpn_mul_1`,
`mpn_addmul_1`, `mpn_mul` and `mpn_sqr` as closed `jasminDialect` multi-return programs
over `n`-limb operands. Each program is one block of `FieldLimbs.Curve25519` or
`FieldLimbs.Mont` followed by a return: the same blocks the Montgomery template composes.
Operands are the leading registers of the input context in order; results are returned
in the GMP layout, the result limbs first and then the carry, borrow or high word where
the function returns one. The value of a limb tuple is `limbsVal`, the little-endian
value `nv` of its registers.

| GMP function | program | block |
|---|---|---|
| `mpn_add_n` | `mpnAddN n` | `addK` |
| `mpn_sub_n` | `mpnSubN n` | `xorR` with an all-ones mask, `adcR` with carry-in `1` |
| `mpn_mul_1` | `mpnMul1 n` | `mulRowK` |
| `mpn_addmul_1` | `mpnAddmul1 n` | `accK` at position `0` |
| `mpn_mul` | `mpnMul n m` | `prodNK` |
| `mpn_sqr` | `mpnSqr n` | `sqrNK` |

These are straight-line programs for one fixed `n`; the looped variable-`n` mpn kernels
are separate programs.

## Main definitions

* `limbsVal`: the value of an `n`-limb tuple.
* `retNW`, `retHi`: the return of result limbs followed by one word.
* `mpnAddN`, `mpnSubN`, `mpnMul1`, `mpnAddmul1`, `mpnMul`, `mpnSqr`: the programs.

## Main results

* `mpnAddN_denote`: `limbsVal S + 2^(64n) · cy = limbsVal A + limbsVal B`, `cy ≤ 1`.
* `mpnSubN_denote`: `limbsVal S + limbsVal B = limbsVal A + 2^(64n) · bw`, `bw ≤ 1`.
* `mpnMul1_denote`: `limbsVal S + 2^(64n) · hi = limbsVal A · v`.
* `mpnAddmul1_denote`: `limbsVal S + 2^(64n) · hi = limbsVal R + limbsVal A · v`.
* `mpnMul_denote`: the `n + m` result limbs have value `limbsVal A · limbsVal B`.
* `mpnSqr_denote`: the `n + n` result limbs have value `limbsVal A · limbsVal A`.

Each holds for every `n` (and `m ≥ 1` for `mpn_mul`) and every input; the `_eq` forms give
the returned tuple explicitly.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mpn

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519
  (w64 w1 MC lk lk1 eConst eBit eConst_denote eBit_denote Pres Pres.id Pres.comp bindK
    bindK_denote nv nv_nil nv_cons nv_map nv_append nv_lt addK addK_denote mulRowK
    mulRowK_denote accK xorR xorR_denote adcR adcR_denote)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs

/-! ## 1. Limb values and returns -/

/-- The little-endian value of a tuple of `k` 64-bit limbs. -/
def limbsVal {k : Nat} (A : ListDenote (Rn k)) : Nat := nv A (limbVars k)

theorem limbsVal_lt {k : Nat} (A : ListDenote (Rn k)) : limbsVal A < 2 ^ (64 * k) := by
  have h := nv_lt A (limbVars k)
  rwa [limbVars_length] at h

theorem limbsVal_limbsN (k v : Nat) : limbsVal (limbsN k v) = v % 2 ^ (64 * k) :=
  nv_limbVars k v

theorem nv_opX_val {n : Nat} {Γ : Ctxt jasminDialect} (A : ListDenote (Rn n))
    (B : Valuation Γ) : nv (hvAppend A B) (opX n Γ) = limbsVal A := by
  rw [opX, nv_map (r := fun {_} w => inlHom Γ w) (W := A) (fun w => lookup_inlHom B w _)]
  rfl

/-- The limbs of an `m`-limb second operand of a context `Rn n ++ (Rn m ++ Γ)`. -/
def opSnd (n m : Nat) (Γ : Ctxt jasminDialect) :
    List (Var (d := jasminDialect) (Rn n ++ (Rn m ++ Γ)) w64) :=
  (opX m Γ).map fun v => inrHom (Rn n) v

theorem opSnd_length (n m : Nat) (Γ : Ctxt jasminDialect) : (opSnd n m Γ).length = m := by
  simp [opSnd, opX_length]

theorem nv_opSnd_val {n m : Nat} {Γ : Ctxt jasminDialect} (A : ListDenote (Rn n))
    (B : ListDenote (Rn m)) (C : Valuation Γ) :
    nv (hvAppend A (hvAppend B C)) (opSnd n m Γ) = limbsVal B := by
  rw [opSnd, nv_map (r := fun {_} w => inrHom (Rn n) w) (W := hvAppend B C)
    (fun w => lookup_inrHom _ A w), nv_opX_val]

/-- Looking up an appended vector of variables appends the lookups. -/
theorem lookupVars_hvAppend {Δ : Ctxt jasminDialect} (W : Valuation Δ) :
    ∀ {xs ys : List JasminTy} (r₁ : HVector (fun u => Var Δ u) xs)
      (r₂ : HVector (fun u => Var Δ u) ys),
      MultiReturnCom.lookupVars (hvAppend r₁ r₂) W
        = hvAppend (MultiReturnCom.lookupVars r₁ W) (MultiReturnCom.lookupVars r₂ W)
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons _ r₁, r₂ => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [lookupVars_hvAppend W r₁ r₂]

/-- The return of the `k` limbs `out` followed by the word `x`; on an empty list the limbs
    are copies of a zero constant. -/
def retNW {Δ : Ctxt jasminDialect} {t : JasminTy} (k : Nat) (out : List (Var Δ w64))
    (x : Var Δ t) : MC Δ (Rn k ++ [t]) :=
  match out with
  | [] => .var (eConst 0) (.ret (hvAppend (varsPad .here k []) (.cons x.there .nil)))
  | a :: as => .ret (hvAppend (varsPad a k (a :: as)) (.cons x .nil))

theorem retNW_denote {Δ : Ctxt jasminDialect} {t : JasminTy} (k : Nat)
    (out : List (Var Δ w64)) (x : Var Δ t) (W : Valuation Δ) (hlen : out.length = k) :
    (retNW k out x).denote W = hvAppend (limbsN k (nv W out)) (.cons (x.lookup W) .nil) := by
  subst hlen
  cases out with
  | nil => rfl
  | cons a as =>
    show MultiReturnCom.lookupVars _ W = _
    rw [lookupVars_hvAppend, lookupVars_varsPad W a (a :: as)]
    rfl

/-- `retHi` on the split of a list into its first `k` limbs and the rest. -/
def retHiAux {Δ : Ctxt jasminDialect} (k : Nat) (lo : List (Var Δ w64)) :
    List (Var Δ w64) → MC Δ (Rn k ++ [w64])
  | [] => .var (eConst 0) (.ret (hvAppend (varsPad .here k []) (.cons .here .nil)))
  | x :: _ => retNW k lo x

/-- The return of a list of `k + 1` limbs as `k` limbs followed by the high limb. -/
def retHi {Δ : Ctxt jasminDialect} (k : Nat) (out : List (Var Δ w64)) : MC Δ (Rn k ++ [w64]) :=
  retHiAux k (out.take k) (out.drop k)

theorem retHi_denote {Δ : Ctxt jasminDialect} (k : Nat) (out : List (Var Δ w64))
    (W : Valuation Δ) (hlen : out.length = k + 1) :
    (retHi k out).denote W = hvAppend (limbsN k (nv W out % 2 ^ (64 * k)))
      (.cons (BitVec.ofNat 64 (nv W out / 2 ^ (64 * k))) .nil) := by
  obtain ⟨x, hx⟩ : ∃ x, out.drop k = [x] :=
    List.length_eq_one_iff.mp (by simp [hlen])
  have htl : (out.take k).length = k := by simp [hlen]
  have hsplit := nv_append W (out.take k) (out.drop k)
  rw [List.take_append_drop, htl, hx, nv_cons, nv_nil] at hsplit
  have hlo := nv_lt W (out.take k)
  rw [htl] at hlo
  have hM : 0 < 2 ^ (64 * k) := Nat.two_pow_pos _
  have hmod : nv W out % 2 ^ (64 * k) = nv W (out.take k) := by
    rw [hsplit, Nat.mul_zero, Nat.add_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]
  have hdiv : nv W out / 2 ^ (64 * k) = (lk x W).toNat := by
    rw [hsplit, Nat.mul_zero, Nat.add_zero, Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hlo,
      Nat.zero_add]
  rw [retHi, hx, retHiAux, retNW_denote k _ x W htl, hmod, hdiv, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

/-- The value of `k` limbs followed by one `w`-bit word, for the explicit split of `v`. -/
theorem limbsVal_split (k w v : Nat) (hv : v < 2 ^ (64 * k) * 2 ^ w) :
    limbsVal (limbsN k (v % 2 ^ (64 * k)))
      + 2 ^ (64 * k) * (BitVec.ofNat w (v / 2 ^ (64 * k))).toNat = v := by
  have hq : v / 2 ^ (64 * k) < 2 ^ w := Nat.div_lt_of_lt_mul hv
  rw [limbsVal_limbsN, Nat.mod_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq, Nat.mod_add_div]

/-- A value `s` below `M` and a multiple of `M` determine the remainder and quotient of
    their sum. -/
theorem split_val {M s c v : Nat} (hs : s < M) (h : s + M * c = v) :
    s = v % M ∧ c = v / M := by
  subst h
  have hM : 0 < M := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  · rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hs, Nat.zero_add]

/-! ## 2. `mpn_add_n` -/

/-- `mpn_add_n`: the `n` sum limbs and the carry of two `n`-limb operands, by the carry
    chain `addK`. -/
def mpnAddN (n : Nat) : MC (Rn n ++ (Rn n ++ [])) (Rn n ++ [w1]) :=
  addK (opX n _) (opY n []) fun _ out c => retNW n out c

theorem mpnAddN_eq (n : Nat) (A B : ListDenote (Rn n)) :
    (mpnAddN n).denote (hvAppend A (hvAppend B .nil)) =
      hvAppend (limbsN n ((limbsVal A + limbsVal B) % 2 ^ (64 * n)))
        (.cons (BitVec.ofNat 1 ((limbsVal A + limbsVal B) / 2 ^ (64 * n))) .nil) := by
  refine addK_denote _ _ _ _ _ (by rw [opX_length, opY_length])
    fun r out c W' _ hout hv => ?_
  rw [opX_length] at hout hv
  rw [nv_opX_val, opY, nv_map (r := fun {_} w => inrHom (Rn n) w) (W := hvAppend B .nil)
    (fun w => lookup_inrHom _ A w), nv_opX_val] at hv
  obtain ⟨hs, hc⟩ := split_val (by simpa [hout] using nv_lt W' out) hv
  rw [retNW_denote n out c W' hout, ← hs, ← hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem mpnAddN_denote (n : Nat) (A B : ListDenote (Rn n)) :
    ∃ (S : ListDenote (Rn n)) (cy : BitVec 1),
      (mpnAddN n).denote (hvAppend A (hvAppend B .nil)) = hvAppend S (.cons cy .nil) ∧
      limbsVal S + 2 ^ (64 * n) * cy.toNat = limbsVal A + limbsVal B ∧ cy.toNat ≤ 1 := by
  refine ⟨_, _, mpnAddN_eq n A B, limbsVal_split n 1 _ ?_, ?_⟩
  · have := limbsVal_lt A
    have := limbsVal_lt B
    omega
  · have := (BitVec.ofNat 1 ((limbsVal A + limbsVal B) / 2 ^ (64 * n))).isLt
    omega

/-! ## 3. `mpn_sub_n` -/

/-- The exclusive or of two 1-bit registers. -/
def eXor1 {Γ : Ctxt jasminDialect} (a b : Var Γ w1) : Expr jasminDialect Γ w1 :=
  { op := .regArith .xor 1, retTy_eq := rfl, args := .cons a (.cons b .nil) }

theorem eXor1_denote {Γ : Ctxt jasminDialect} (a b : Var Γ w1) (W : Valuation Γ) :
    (eXor1 a b).denote W = lk1 a W ^^^ lk1 b W := rfl

theorem xor_one_toNat (c : BitVec 1) : (c ^^^ 1#1).toNat = 1 - c.toNat := by
  revert c
  decide

/-- `mpn_sub_n`: the `n` difference limbs and the borrow of two `n`-limb operands, as
    `a + ¬b + 1` by the carry chain `adcR` over the limbs `xorR` complements; the borrow
    is the complement of the carry. -/
def mpnSubN (n : Nat) : MC (Rn n ++ (Rn n ++ [])) (Rn n ++ [w1]) :=
  bindK (eConst (2 ^ 64 - 1)) fun r₁ m =>
  xorR r₁ m (opY n []) fun r₂ ny =>
  bindK (eBit 1) fun r₃ one =>
  adcR (fun v => v) ((opX n _).map (fun v => r₃ (r₂ (r₁ v)))) (ny.map (fun v => r₃ v)) one
    fun r₄ D c =>
  bindK (eXor1 c (r₄ one)) fun r₅ bw =>
  retNW n (D.map (fun v => r₅ v)) bw

theorem mpnSubN_eq (n : Nat) (A B : ListDenote (Rn n)) :
    (mpnSubN n).denote (hvAppend A (hvAppend B .nil)) =
      hvAppend (limbsN n ((limbsVal A + (2 ^ (64 * n) - limbsVal B)) % 2 ^ (64 * n)))
        (.cons (BitVec.ofNat 1
          (1 - (limbsVal A + (2 ^ (64 * n) - limbsVal B)) / 2 ^ (64 * n))) .nil) := by
  refine bindK_denote _ _ _ _ fun r₁ m W₁ h₁ hm => ?_
  refine xorR_denote r₁ m (opY n []) _ _ W₁ _ h₁ hm fun r₂ ny W₂ h₂ hny hnyv => ?_
  refine bindK_denote _ _ _ _ fun r₃ one W₃ h₃ hone => ?_
  have h123 : Pres (fun v => r₃ (r₂ (r₁ v))) (hvAppend A (hvAppend B .nil)) W₃ :=
    Pres.comp (Pres.comp h₁ h₂) h₃
  have eone : (lk1 one W₃).toNat = 1 := by rw [show lk1 one W₃ = _ from hone, eBit_denote]; rfl
  refine adcR_denote (fun v => v) _ _ one _ W₃ W₃ _ (Pres.id W₃)
    (by simp only [List.length_map]; rw [hny, opX_length, opY_length])
    fun r₄ D c W₄ h₄ hD hDv => ?_
  rw [nv_map h123, nv_map h₃, eone, nv_opX_val] at hDv
  simp only [List.length_map] at hDv hD
  rw [opX_length] at hDv hD
  rw [opY_length, opY, nv_map (r := fun {_} w => inrHom (Rn n) w) (W := hvAppend B .nil)
    (fun w => lookup_inrHom _ A w), nv_opX_val] at hnyv
  refine bindK_denote _ _ _ _ fun r₅ bw W₅ h₅ hbw => ?_
  rw [retNW_denote n _ bw W₅ (by simp [hD]), nv_map h₅]
  have hv : nv W₄ D + 2 ^ (64 * n) * (lk1 c W₄).toNat
      = limbsVal A + (2 ^ (64 * n) - limbsVal B) := by omega
  obtain ⟨hs, hc⟩ := split_val (by simpa [hD] using nv_lt W₄ D) hv
  have ebw : bw.lookup W₅ = lk1 c W₄ ^^^ 1#1 := by
    rw [hbw, eXor1_denote, show lk1 (r₄ one) W₄ = lk1 one W₃ from h₄ one,
      show lk1 one W₃ = _ from hone, eBit_denote]
  rw [← hs, ← hc, ebw]
  congr 2
  apply BitVec.eq_of_toNat_eq
  rw [xor_one_toNat, BitVec.toNat_ofNat]
  have := (lk1 c W₄).isLt
  omega

theorem mpnSubN_denote (n : Nat) (A B : ListDenote (Rn n)) :
    ∃ (S : ListDenote (Rn n)) (bw : BitVec 1),
      (mpnSubN n).denote (hvAppend A (hvAppend B .nil)) = hvAppend S (.cons bw .nil) ∧
      limbsVal S + limbsVal B = limbsVal A + 2 ^ (64 * n) * bw.toNat ∧ bw.toNat ≤ 1 := by
  refine ⟨_, _, mpnSubN_eq n A B, ?_, ?_⟩
  · have ha := limbsVal_lt A
    have hb := limbsVal_lt B
    rw [limbsVal_limbsN, Nat.mod_mod, BitVec.toNat_ofNat]
    generalize limbsVal A = a at *
    generalize limbsVal B = b at *
    generalize 2 ^ (64 * n) = M at *
    have hdm := Nat.mod_add_div (a + (M - b)) M
    have hq : (a + (M - b)) / M < 2 := Nat.div_lt_of_lt_mul (by omega)
    generalize (a + (M - b)) % M = r at *
    generalize (a + (M - b)) / M = q at *
    interval_cases q <;> simp at * <;> omega
  · have := (BitVec.ofNat 1
      (1 - (limbsVal A + (2 ^ (64 * n) - limbsVal B)) / 2 ^ (64 * n))).isLt
    omega

/-! ## 4. `mpn_mul_1` and `mpn_addmul_1` -/

/-- The scalar word of a context `Rn n ++ [w64]`. -/
def scal1 (n : Nat) : Var (d := jasminDialect) (Rn n ++ [w64]) w64 :=
  inrHom (Rn n) (Var.here (d := jasminDialect) (Γ := []) (t := w64))

theorem lk_scal1 (n : Nat) (A : ListDenote (Rn n)) (v : BitVec 64) :
    lk (scal1 n) (hvAppend A (.cons v .nil)) = v := by
  rw [scal1, lk, lookup_inrHom]
  rfl

/-- `mpn_mul_1`: the `n` low limbs and the high limb of an `n`-limb operand times a word,
    by the product row `mulRowK`. -/
def mpnMul1 (n : Nat) : MC (Rn n ++ [w64]) (Rn n ++ [w64]) :=
  mulRowK (opX n _) (scal1 n) fun _ out => retHi n out

theorem mpnMul1_eq (n : Nat) (A : ListDenote (Rn n)) (v : BitVec 64) :
    (mpnMul1 n).denote (hvAppend A (.cons v .nil)) =
      hvAppend (limbsN n (limbsVal A * v.toNat % 2 ^ (64 * n)))
        (.cons (BitVec.ofNat 64 (limbsVal A * v.toNat / 2 ^ (64 * n))) .nil) := by
  refine mulRowK_denote _ _ _ _ _ fun r out W' _ hout hv => ?_
  rw [opX_length] at hout
  rw [retHi_denote n out W' hout, hv, nv_opX_val, lk_scal1]

theorem mpnMul1_denote (n : Nat) (A : ListDenote (Rn n)) (v : BitVec 64) :
    ∃ (S : ListDenote (Rn n)) (hi : BitVec 64),
      (mpnMul1 n).denote (hvAppend A (.cons v .nil)) = hvAppend S (.cons hi .nil) ∧
      limbsVal S + 2 ^ (64 * n) * hi.toNat = limbsVal A * v.toNat :=
  ⟨_, _, mpnMul1_eq n A v,
    limbsVal_split n 64 _ (Nat.mul_lt_mul'' (limbsVal_lt A) v.isLt)⟩

/-- The scalar word of a context `Rn n ++ (Rn n ++ [w64])`. -/
def scal2 (n : Nat) : Var (d := jasminDialect) (Rn n ++ (Rn n ++ [w64])) w64 :=
  inrHom (Rn n) (scal1 n)

theorem lk_scal2 (n : Nat) (R A : ListDenote (Rn n)) (v : BitVec 64) :
    lk (scal2 n) (hvAppend R (hvAppend A (.cons v .nil))) = v := by
  rw [scal2, lk, lookup_inrHom]
  exact lk_scal1 n A v

/-- An `n`-limb value plus an `n`-limb value times a word is below `2^64 M` for
    `M = 2^(64n)`. -/
theorem addmul_lt {M r a v : Nat} (hr : r < M) (ha : a < M) (hv : v < 2 ^ 64) :
    r + a * v < M * 2 ^ 64 := by
  nlinarith

/-- `mpn_addmul_1`: the `n` low limbs and the high limb of `r + a · v` for `n`-limb `r`,
    `a` and a word `v`, by the accumulation step `accK` at position `0`. -/
def mpnAddmul1 (n : Nat) : MC (Rn n ++ (Rn n ++ [w64])) (Rn n ++ [w64]) :=
  accK 0 (opSnd n n [w64]) (scal2 n) (opX n _) fun _ out => retHi n out

theorem mpnAddmul1_eq (n : Nat) (R A : ListDenote (Rn n)) (v : BitVec 64) :
    (mpnAddmul1 n).denote (hvAppend R (hvAppend A (.cons v .nil))) =
      hvAppend (limbsN n ((limbsVal R + limbsVal A * v.toNat) % 2 ^ (64 * n)))
        (.cons (BitVec.ofNat 64 ((limbsVal R + limbsVal A * v.toNat) / 2 ^ (64 * n)))
          .nil) := by
  have hb := addmul_lt (limbsVal_lt R) (limbsVal_lt A) v.isLt
  refine accK_denote_n (n := n) 0 _ _ _ _ _ _ (opSnd_length n n _)
    (by rw [opX_length, Nat.zero_add]) ?_ fun r out W' _ hout hv => ?_
  · rw [nv_opX_val, nv_opSnd_val, lk_scal2, Nat.mul_zero, Nat.pow_zero, Nat.one_mul,
      Nat.one_mul, two_pow_succ]
    exact hb
  · rw [retHi_denote n out W' (by rw [hout, Nat.zero_add]), hv, nv_opX_val, nv_opSnd_val,
      lk_scal2, Nat.mul_zero, Nat.pow_zero, Nat.one_mul]

theorem mpnAddmul1_denote (n : Nat) (R A : ListDenote (Rn n)) (v : BitVec 64) :
    ∃ (S : ListDenote (Rn n)) (hi : BitVec 64),
      (mpnAddmul1 n).denote (hvAppend R (hvAppend A (.cons v .nil))) =
        hvAppend S (.cons hi .nil) ∧
      limbsVal S + 2 ^ (64 * n) * hi.toNat = limbsVal R + limbsVal A * v.toNat :=
  ⟨_, _, mpnAddmul1_eq n R A v,
    limbsVal_split n 64 _ (addmul_lt (limbsVal_lt R) (limbsVal_lt A) v.isLt)⟩

/-! ## 5. `mpn_mul` and `mpn_sqr` -/

/-- `mpn_mul`: the `n + m` product limbs of an `n`-limb and an `m`-limb operand, by the
    schoolbook product `prodNK`. -/
def mpnMul (n m : Nat) : MC (Rn n ++ (Rn m ++ [])) (Rn (n + m)) :=
  prodNK (opX n _) (opSnd n m []) fun _ out => retN (n + m) out

theorem mpnMul_eq (n m : Nat) (hm : 0 < m) (A : ListDenote (Rn n)) (B : ListDenote (Rn m)) :
    (mpnMul n m).denote (hvAppend A (hvAppend B .nil)) =
      limbsN (n + m) (limbsVal A * limbsVal B) := by
  refine prodNK_denote (n := n) _ _ _ _ _ (opX_length n _) (by rw [opSnd_length]; exact hm)
    fun r out W' _ hout hv => ?_
  rw [opSnd_length] at hout
  rw [retN_denote _ out W' hout, hv, nv_opX_val, nv_opSnd_val]

theorem mpnMul_denote (n m : Nat) (hm : 0 < m) (A : ListDenote (Rn n))
    (B : ListDenote (Rn m)) :
    limbsVal ((mpnMul n m).denote (hvAppend A (hvAppend B .nil))) =
      limbsVal A * limbsVal B := by
  rw [mpnMul_eq n m hm, limbsVal_limbsN, Nat.mod_eq_of_lt]
  rw [Nat.mul_add, Nat.pow_add]
  exact Nat.mul_lt_mul'' (limbsVal_lt A) (limbsVal_lt B)

/-- `mpn_sqr`: the `n + n` limbs of the square of an `n`-limb operand, by the squaring
    block `sqrNK`. -/
def mpnSqr (n : Nat) : MC (Rn n ++ []) (Rn (n + n)) :=
  sqrNK (opX n _) fun _ out => retN (n + n) out

theorem mpnSqr_eq (n : Nat) (A : ListDenote (Rn n)) :
    (mpnSqr n).denote (hvAppend A .nil) = limbsN (n + n) (limbsVal A * limbsVal A) := by
  refine sqrNK_denote (n := n) _ _ _ _ (opX_length n _) fun r out W' _ hout hv => ?_
  rw [retN_denote _ out W' hout, hv, nv_opX_val]

theorem mpnSqr_denote (n : Nat) (A : ListDenote (Rn n)) :
    limbsVal ((mpnSqr n).denote (hvAppend A .nil)) = limbsVal A * limbsVal A := by
  rw [mpnSqr_eq, limbsVal_limbsN, Nat.mod_eq_of_lt]
  rw [Nat.mul_add, Nat.pow_add]
  exact Nat.mul_lt_mul'' (limbsVal_lt A) (limbsVal_lt A)

end CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mpn
