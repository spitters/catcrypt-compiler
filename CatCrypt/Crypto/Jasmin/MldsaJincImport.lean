/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JincElab
public import CatCrypt.Crypto.Number.MontgomeryReduction

/-!
# ML-DSA Montgomery-reduction leaf on the `.jinc` import path

The per-coefficient Montgomery reduction at the ML-DSA parameters
(`q = 8380417`, radix `R = 2^32`) as a straight-line Jasmin `.jinc` leaf, taken
through `JincParser` / `JincToCom` / `JincElab` to a `Com jasminDialect` and
rendered to AT&T x86 by `Com.toLprogPhysAbi` / `renderLprogAtt`.

`mldsaMontRedWord` is the 64-bit word computation the leaf performs, and
`mldsaMontRedWord_toNat` identifies it with
`CatCrypt.Crypto.Number.montgomeryReduce q R q'` on inputs below `R * q`.
`mldsaMontRed_montgomery_law` reads the range and congruence facts off
`montgomeryReduce_correct`: the result lies in `[0, 2q)` and satisfies
`result * R ≡ t (mod q)`.

The parse, the elaboration shape and the rendering are checked by the executable
`mldsa-jinc-import-kat` (`MldsaJincImportKat.lean`). They evaluate `partial def`s
(`JincToCom.tokenize`, `JincElab.elabStmts`), which the kernel cannot unfold. For the
same reason the elaborated `Com`'s denotation is not tied to `mldsaMontRedWord` by a
theorem: `mldsaMontRedCom?` reduces only through those `partial def`s.

## Main definitions

* `mldsaMontRedWord`: the 64-bit word computation the leaf performs.
* `mldsaMontRedCom?`: the elaborated `Com jasminDialect` for the `.jinc` source.
* `mldsaMontRedAsm`: the AT&T x86 rendering through `Com.toLprogPhysAbi`.

## Main results

* `mldsaMontRedWord_toNat`: identifies `mldsaMontRedWord` with
  `montgomeryReduce q R q'` on inputs below `R * q`.
* `mldsaMontRed_montgomery_law`: the result lies in `[0, 2q)` and satisfies
  `result * R ≡ t (mod q)`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.MldsaJincImport

open CatCrypt.Crypto.Jasmin.JincToCom
open CatCrypt.Crypto.Jasmin.JincElab
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Parameters -/

/-- The ML-DSA modulus. -/
def mldsaQ : Nat := 8380417

/-- The Montgomery radix of ML-DSA's coefficient arithmetic. -/
def mldsaR : Nat := 4294967296

/-- The Montgomery constant `q'` with `q * q' ≡ -1 (mod 2^32)`, equal to
    `2^32 - (q⁻¹ mod 2^32)`. -/
def mldsaQNegInv : Nat := 4236238847

theorem mldsaQNegInv_spec : (mldsaQ * mldsaQNegInv) % mldsaR = mldsaR - 1 := by
  norm_num [mldsaQ, mldsaQNegInv, mldsaR]

/-! ## 2. The `.jinc` leaf -/

/-- The straight-line Montgomery-reduction leaf: with `m = (t * q') mod 2^32`,
    the result is `(t + m * q) / 2^32`. The `<< 32 ; >> 32` pair truncates
    `t * q'` to 32 bits. -/
def mldsaMontRedSrc : String :=
  "inline fn mldsa_montgomery_reduce(reg u64 t) -> reg u64 {
     reg u64 m;
     reg u64 p;
     reg u64 r;
     m = t * 4236238847;
     m = m << 32;
     m = m >> 32;
     p = m * 8380417;
     r = t + p;
     r = r >> 32;
     return r;
   }"

/-- The elaborated `Com` at its concrete type (`[t] → reg 64`). -/
def mldsaMontRedCom? : Option (Com jasminDialect [.reg 64] (.reg 64)) :=
  match elabFun ((parseJincFun mldsaMontRedSrc).toOption.getD default) with
  | some ⟨Γ, τ, com⟩ =>
      if hΓ : Γ = [.reg 64] then
        if hτ : τ = .reg 64 then some (hΓ ▸ hτ ▸ com) else none
      else none
  | none => none

/-! ## 3. The word computation and its Montgomery law -/

/-- The 64-bit word computation the leaf performs. -/
def mldsaMontRedWord (t : BitVec 64) : BitVec 64 :=
  (t + ((t * 4236238847) <<< 32 >>> 32) * 8380417) >>> 32

/-- The truncated Montgomery digit `m = (t * q') mod 2^32`. -/
theorem mldsaMontRed_digit (t : BitVec 64) :
    (((t * 4236238847) <<< 32 >>> 32 : BitVec 64)).toNat
      = (t.toNat * mldsaQNegInv) % mldsaR := by
  have ht := t.isLt
  have hc : ((4236238847 : BitVec 64)).toNat = 4236238847 := by simp
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_mul, hc,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  simp only [Nat.reducePow, mldsaQNegInv, mldsaR] at ht ⊢
  omega

/-- The word computation is the abstract Montgomery reduction at the ML-DSA
    parameters, for inputs below `R * q`. -/
theorem mldsaMontRedWord_toNat (t : BitVec 64) (ht : t.toNat < mldsaR * mldsaQ) :
    (mldsaMontRedWord t).toNat
      = CatCrypt.Crypto.Number.montgomeryReduce mldsaQ mldsaR mldsaQNegInv t.toNat := by
  have hq : ((8380417 : BitVec 64)).toNat = 8380417 := by simp
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  have hdig := mldsaMontRed_digit t
  obtain ⟨m, hmdef⟩ : ∃ m, (t.toNat * mldsaQNegInv) % mldsaR = m := ⟨_, rfl⟩
  have hmlt : m < 4294967296 := by
    rw [← hmdef]
    simpa [mldsaR] using
      Nat.mod_lt (t.toNat * mldsaQNegInv) (show 0 < mldsaR by norm_num [mldsaR])
  have ht' : t.toNat < 35993616941842432 := by simpa [mldsaQ, mldsaR] using ht
  have hmq : m * 8380417 ≤ 35993616933462015 := by
    have h1 : m * 8380417 ≤ 4294967295 * 8380417 :=
      Nat.mul_le_mul_right 8380417 (by omega)
    simpa using h1
  rw [hmdef] at hdig
  have hp : (((t * 4236238847) <<< 32 >>> 32 : BitVec 64) * 8380417).toNat = m * 8380417 := by
    rw [BitVec.toNat_mul, hdig, hq]
    exact Nat.mod_eq_of_lt (by rw [h64]; omega)
  have hsum : (t + ((t * 4236238847) <<< 32 >>> 32 : BitVec 64) * 8380417).toNat
      = t.toNat + m * 8380417 := by
    rw [BitVec.toNat_add, hp]
    exact Nat.mod_eq_of_lt (by rw [h64]; omega)
  have hspec : CatCrypt.Crypto.Number.montgomeryReduce mldsaQ mldsaR mldsaQNegInv t.toNat
      = (t.toNat + m * 8380417) / 4294967296 := by
    unfold CatCrypt.Crypto.Number.montgomeryReduce
    rw [hmdef]
    norm_num [mldsaQ, mldsaR]
  rw [hspec, mldsaMontRedWord, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hsum]

/-- The imported leaf is a Montgomery reduction: on an input below `R * q` the
    result lies in `[0, 2q)` and satisfies `result * R ≡ t (mod q)`. -/
theorem mldsaMontRed_montgomery_law (t : BitVec 64) (ht : t.toNat < mldsaR * mldsaQ) :
    (mldsaMontRedWord t).toNat < 2 * mldsaQ ∧
    (mldsaMontRedWord t).toNat * mldsaR ≡ t.toNat [MOD mldsaQ] := by
  rw [mldsaMontRedWord_toNat t ht]
  exact CatCrypt.Crypto.Number.montgomeryReduce_correct mldsaQ mldsaR mldsaQNegInv t.toNat
    (by norm_num [mldsaQ]) (by norm_num [mldsaR]) mldsaQNegInv_spec ht

/-! ## 4. x86 emission -/

/-- The AT&T `.s` for the leaf, through `Com.toLprogPhysAbi` / `renderLprogAtt`.
    The single `reg u64` argument lands in `RDI`. `Com.toLprogPhysAbi` emits its
    return-value materialisation into `RAX` only for bodies containing a call
    (`bodyStraightCall`), so for this call-free body the returned value stays in
    whichever register the allocator assigned. -/
def mldsaMontRedAsm : String :=
  emitJincAsm mldsaMontRedSrc "mldsa_montgomery_reduce"

end CatCrypt.Crypto.Jasmin.MldsaJincImport
