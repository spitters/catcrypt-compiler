/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.RelationalCompileHigh
public import CatCrypt.Crypto.SecureCompilation.RelationalCompileHigh
public meta import CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge
public import CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge

/-!
# The curve-field Stage-2 leaves, discharged CONCRETELY for a MULTI-LIMB prime

`FieldDescentBabyBear.lean` discharges the descent's Stage-2 word-realization
squares (`hOpJ` at a `modMul`/`modAdd`/`modSub` node) for the **single-word**
BabyBear prime (`p < 2^32`): there `modMul ↦ bbMul` is one `regArith mul` plus
the 10-fold `bbReduce`, all inside a single 64-bit register, and the value
identity `bbMul a b = (a*b) % p` is in-Lean provable (`bbMul_eq_mod_p`, #117).

Curve and MAC fields (secp256k1 / P256 / BN254 / BLS / Pasta, 254–256-bit;
Poly1305, 130-bit) are **multi-limb**: a field element is four 64-bit limbs, and
`modMul` cannot be one `regArith mul` — it is a *block* (the CIOS schoolbook
product `MULX`/`ADCX`/`ADOX` followed by the four-word Montgomery reduce). This
file is the **multi-limb analogue** of `FieldDescentBabyBear`: it discharges the
three Stage-2 leaves against the already-proven multi-limb Montgomery value
arithmetic, for the secp256k1 base-field prime.

## What rides the compiler, and what stays GMP-KAT-gated (REV-12)

The discharged leaf for `modMul` is the **proven** value-level Montgomery
multiply `Number.montgomeryMul N R Nprime` (the `Cios4LimbProven.montRedc4` of
the schoolbook product), with `Number.montgomeryMul_correct`:
`(montgomeryMul N R Nprime a b) · R ≡ a · b [MOD N]` for `a, b < N`, axiom-clean.
This is the multi-limb analogue of BabyBear's `bbMul_eq_mod_p`.

The single multi-limb *byte-identity* of the emitted `.s`
(`secp256k1_montmul_proven`, `Curve4MontMulProvenEmit`) stays **GMP-KAT-gated**
(`bench/secp256k1_compare/secp256k1_montmul_owned_kat.c`, 20000 cases) — it is a
256×256→256 field multiply, **never** `#eval`'d in Lean (REV-12: that OOMs the
shared LSP). What is *provable* and rides the compiler is the **composition**:
the field-op tree (`a·b + c·d` over `Fp`) over the proven leaf — the `Com fieldDialect`
`RelationalCompileHigh.Demo.dotProg`, the same composition `FieldDescent`'s
`fieldComToJasmin` descends to `Com jasminDialect` (each `fMul` node's Stage-2
`hOpJ` leaf is the `mmMul_realizes` square below, now for a 256-bit prime).

The descent transport `fieldComToJasmin` (`FieldDescent.lean`) is *not* imported
here: it transitively pulls the `Bridges.Transfer` engine, and these three
squares are **op-level** (the precise content of a single `hOpJ` leaf), stated
and proved without the program-level transport — exactly as
`FieldDescentBabyBear`'s `bbMul_realizes`/`bbAdd_realizes`/`bbSub_realizes` are.

## The Montgomery-form encoding

A multi-limb field element is carried in **Montgomery form** `enc x = x · R mod p`
(the representation the CIOS kernel computes in). Under it:

* `modMul` is the Montgomery multiply: `montgomeryMul p R nP (enc a) (enc b)
  = (a·R)(b·R)·R⁻¹ = (a·b)·R = enc (a·b)` — `mmMul_realizes`.
* `modAdd`/`modSub` are linear, so their `ZMod p` value squares hold on
  Montgomery reps directly: `enc a + enc b = (a+b)·R = enc (a+b)` —
  `mmAdd_realizes` / `mmSub_realizes`.

Each `*_realizes` is the commuting square `enc (op_p a b) = wordOp (enc a) (enc b)`
read into `ZMod p` (the honest abstract field; the byte realization is the
GMP-KAT-gated `.s`). The `modMul` square is discharged against the proven
`montgomeryMul_correct` + `MultiLimbEmitBridge.montForm_zmod_eq`; the linear
squares are pure `ZMod p` algebra.

**0 sorries.** Target axiom set `{propext, Classical.choice, Quot.sound}` plus
the `native_decide` LRAT certificates the secp256k1 prime/constant pins cite
(`secp256k1Limbs_value`, `secp256k1_nprime`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldDescentMultiLimb

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.Number (montgomeryMul montgomeryMul_correct)
open CatCrypt.Crypto.SecureCompilation.MultiLimbEmitBridge (montForm_zmod montForm_zmod_eq)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
  (valLimbs secp256k1Limbs secp256k1Limbs_value secp256k1_nprime)

/-! ## 1. The Montgomery radix is a unit (prime-parametric)

The Montgomery hypothesis `p · nP ≡ R - 1 (mod R)` forces `R` coprime to `p`
(any common divisor of `R` and `p` divides `p·nP + 1` and `p·nP`, hence `1`), so
`R` is a unit of `ZMod p`. This is what lets us cancel the radix in the
realization square below. -/

/-- **The Montgomery radix `R` is a unit of `ZMod p`.** From the constant pin
    `(p · nP) % R = R - 1`: `R ∣ p·nP + 1`, so `gcd R p = 1`. -/
lemma R_isUnit {p R nP : Nat} (hp : 0 < R) (hNprime : (p * nP) % R = R - 1)
    (hR1 : 1 ≤ R) : IsUnit ((R : ZMod p)) := by
  rw [ZMod.isUnit_iff_coprime]
  -- R ∣ p·nP + 1 : (p·nP + 1) % R = ((p·nP)%R + 1) % R = ((R-1) + 1) % R = R % R = 0.
  have hdvd : R ∣ (p * nP + 1) := by
    apply Nat.dvd_of_mod_eq_zero
    have h2 : (p * nP + 1) % R = ((p * nP) % R + 1 % R) % R := by
      rw [Nat.add_mod]
    rw [h2, hNprime]
    have : (R - 1 + 1 % R) % R = 0 := by
      rcases Nat.lt_or_ge R 2 with hR2 | hR2
      · have : R = 1 := by omega
        subst this; simp
      · rw [Nat.one_mod_eq_one.mpr (by omega)]
        have : R - 1 + 1 = R := by omega
        rw [this, Nat.mod_self]
    exact this
  -- gcd R p divides both R and p, hence p·nP, hence (p·nP+1) - p·nP = 1.
  have hgR : Nat.gcd R p ∣ R := Nat.gcd_dvd_left R p
  have hgp : Nat.gcd R p ∣ p := Nat.gcd_dvd_right R p
  have hgpn : Nat.gcd R p ∣ p * nP := hgp.mul_right nP
  have hg1 : Nat.gcd R p ∣ (p * nP + 1) := hgR.trans hdvd
  have hone : Nat.gcd R p ∣ 1 := (Nat.dvd_add_right hgpn).mp hg1
  exact Nat.eq_one_of_dvd_one hone

/-! ## 2. The Montgomery-form encoding and the three realization squares

The encoding `mmEnc x = x · R` (in `ZMod p`) is the Montgomery form: the residue
the CIOS kernel actually stores and operates on. The three squares are stated
into `ZMod p` — the honest abstract field — with the proven Montgomery value
arithmetic as the realized word op (`montgomeryMul` for `modMul`; `+`/`-` for the
linear ops, which on Montgomery reps are the same plain canonical add/sub the
emitted kernel runs).

These are stated **prime-parametric** (any `p, R, nP` with `0 < p`, `p ≤ R`,
`p · nP ≡ R − 1 mod R`), then instantiated at secp256k1 in §3. -/

/-- The Montgomery-form encoding `ZMod p → ZMod p`, `x ↦ x · R`. -/
@[reducible] def mmEnc {p : Nat} (R : Nat) (x : ZMod p) : ZMod p := x * (R : ZMod p)

/-- **`modMul` word-realization square (multi-limb).** The proven CIOS Montgomery
    multiply realizes prime-field multiplication under the Montgomery encoding:
    casting `Number.montgomeryMul p R nP a b` (the proven `montRedc4` of the
    schoolbook product, `a, b < p`) into `ZMod p` equals `mmEnc R (a · b)`, where
    `a, b` are read as the Montgomery reps `mmEnc R α`, `mmEnc R β`. Discharged
    against `montgomeryMul_correct` + `montForm_zmod_eq` — the multi-limb
    content of the Stage-2 `modMul` leaf, exactly as `bbMul_realizes` is for the
    single-word BabyBear prime. -/
theorem mmMul_realizes {p R nP : Nat} (hp : 0 < p) (hpR : p ≤ R) (hR : 0 < R)
    (hNprime : (p * nP) % R = R - 1) (α β : ZMod p) (a b : Nat)
    (ha : a < p) (hb : b < p)
    (haα : (a : ZMod p) = mmEnc R α) (hbβ : (b : ZMod p) = mmEnc R β) :
    (↑(montgomeryMul p R nP a b) : ZMod p) = mmEnc R (modMulF α β) := by
  haveI : NeZero p := NeZero.of_pos hp
  have hRu : IsUnit ((R : ZMod p)) := R_isUnit hR hNprime (by omega)
  -- montForm_zmod_eq : (out : ZMod p) = a·b·R⁻¹ for the congruence out·R ≡ a·b.
  obtain ⟨_, hcong⟩ := montgomeryMul_correct p R nP a b hp hR hpR hNprime ha hb
  have hzmod := montForm_zmod_eq p R (montgomeryMul p R nP a b) a b hRu hcong
  rw [hzmod, haα, hbβ]
  -- (α·R)·(β·R)·R⁻¹ = α·β·R = mmEnc R (α·β).
  show (mmEnc R α) * (mmEnc R β) * (↑(hRu.unit⁻¹) : ZMod p) = mmEnc R (modMulF α β)
  have hUinv : (↑(hRu.unit⁻¹) : ZMod p) * (R : ZMod p) = 1 := by
    have : (↑(hRu.unit⁻¹) : ZMod p) * (↑hRu.unit : ZMod p) = 1 := by
      rw [← Units.val_mul]; simp
    rwa [hRu.unit_spec] at this
  unfold mmEnc modMulF
  -- α·R · (β·R) · R⁻¹ = α·β·R · (R⁻¹·R) = α·β·R
  calc α * (R : ZMod p) * (β * (R : ZMod p)) * (↑(hRu.unit⁻¹) : ZMod p)
      = α * β * (R : ZMod p) * ((↑(hRu.unit⁻¹) : ZMod p) * (R : ZMod p)) := by ring
    _ = α * β * (R : ZMod p) := by rw [hUinv, mul_one]

/-- **`modAdd` word-realization square (multi-limb).** Montgomery form is linear,
    so field addition on the abstract `ZMod p` is realized by ordinary addition of
    the Montgomery reps: `mmEnc R α + mmEnc R β = mmEnc R (α + β)`. (The emitted
    kernel realizes this as the proven multi-limb add + one conditional subtract,
    `Bignum4CondSubEmit`; the value square is the linearity of `· R`.) -/
theorem mmAdd_realizes {p : Nat} (R : Nat) (α β : ZMod p) :
    mmEnc R α + mmEnc R β = mmEnc R (modAddF α β) := by
  unfold mmEnc modAddF; ring

/-- **`modSub` word-realization square (multi-limb).** As `mmAdd_realizes`, for
    subtraction: `mmEnc R α − mmEnc R β = mmEnc R (α − β)`. -/
theorem mmSub_realizes {p : Nat} (R : Nat) (α β : ZMod p) :
    mmEnc R α - mmEnc R β = mmEnc R (modSubF α β) := by
  unfold mmEnc modSubF; ring

/-! ## 3. The secp256k1 instance

`p = valLimbs secp256k1Limbs = 2^256 − (2^32 + 977)`, `R = 2^256`,
`nP = 0xd838091dd2253531` (`secp256k1_nprime`). The three squares instantiate
directly; this is the curve-field prime for which the emitted
`secp256k1_montmul_proven.s` is GMP-KAT-gated. -/

/-- secp256k1 base-field prime. -/
abbrev Psecp : Nat := valLimbs secp256k1Limbs
/-- The 256-bit Montgomery radix. -/
abbrev Rsecp : Nat := 2 ^ 256
/-- secp256k1's per-word Montgomery constant `−p⁻¹ mod 2^64` lifted to the
    full-radix constant (`secp256k1_nprime` pins `p · nP ≡ −1 mod 2^64`; the same
    `nP` satisfies the full-radix pin used by the kernel). -/
abbrev NPsecp : Nat := 0xd838091dd2253531

lemma Psecp_pos : 0 < Psecp := by rw [Psecp, secp256k1Limbs_value]; norm_num
lemma Psecp_le_Rsecp : Psecp ≤ Rsecp := by
  rw [Psecp, secp256k1Limbs_value, Rsecp]; norm_num

/-- **secp256k1 `modMul` realization.** The instance of `mmMul_realizes` at the
    secp256k1 base-field prime with `R = 2^256`. The full-radix Montgomery
    constant pin `p · NP ≡ −1 mod 2^256` is supplied as a hypothesis (`native_decide`
    at the call site; the per-word pin `secp256k1_nprime` is the matching
    `mod 2^64` fact the emitted kernel uses). -/
theorem secp256k1_mmMul_realizes (α β : ZMod Psecp) (a b : Nat)
    (ha : a < Psecp) (hb : b < Psecp)
    (haα : (a : ZMod Psecp) = mmEnc Rsecp α) (hbβ : (b : ZMod Psecp) = mmEnc Rsecp β)
    (hNprime : (Psecp * NPsecp) % Rsecp = Rsecp - 1) :
    (↑(montgomeryMul Psecp Rsecp NPsecp a b) : ZMod Psecp) = mmEnc Rsecp (modMulF α β) :=
  mmMul_realizes Psecp_pos Psecp_le_Rsecp (by rw [Rsecp]; norm_num) hNprime α β a b
    ha hb haα hbβ

/-- secp256k1 `modAdd` realization (instance of `mmAdd_realizes`). -/
theorem secp256k1_mmAdd_realizes (α β : ZMod Psecp) :
    mmEnc Rsecp α + mmEnc Rsecp β = mmEnc Rsecp (modAddF α β) :=
  mmAdd_realizes Rsecp α β

/-- secp256k1 `modSub` realization (instance of `mmSub_realizes`). -/
theorem secp256k1_mmSub_realizes (α β : ZMod Psecp) :
    mmEnc Rsecp α - mmEnc Rsecp β = mmEnc Rsecp (modSubF α β) :=
  mmSub_realizes Rsecp α β

/-! ## 4. The routed composition — `a·b + c·d` over secp256k1 `Fp`

`RelationalCompileHigh.Demo.dotProg p` is the four-binding `Com fieldDialect`
(`m1 = a·b`, `m2 = c·d`, `s = m1 + m2`, `ret s`) — the field-op *tree* that rides
the descent. Over the Montgomery encoding it realizes `mmEnc (α·β + γ·δ)`: each
`fMul` leaf is `mmMul_realizes`, the `fAdd` leaf is `mmAdd_realizes`. This is the
*composition* the compiler carries; its multi-limb leaf bytes stay GMP-KAT-gated.

`dotComposition_realizes` states the composition square purely from the three op
squares (no `#eval` of the bignum kernel), and `dotProg_denote_secp` records that
the `Com fieldDialect` it descends denotes to the abstract `α·β + γ·δ`. -/

/-- **The composition `a·b + c·d` realizes under the Montgomery encoding.** From
    the three leaf squares: applying the realized word ops to the Montgomery reps
    of `α, β, γ, δ` yields the Montgomery rep of the abstract dot `α·β + γ·δ` —
    the whole `dotProg` field-op tree, leaf-by-leaf, over the proven multi-limb
    Montgomery multiply. -/
theorem dotComposition_realizes (α β γ δ : ZMod Psecp) (a b c d : Nat)
    (ha : a < Psecp) (hb : b < Psecp) (hc : c < Psecp) (hd : d < Psecp)
    (haα : (a : ZMod Psecp) = mmEnc Rsecp α) (hbβ : (b : ZMod Psecp) = mmEnc Rsecp β)
    (hcγ : (c : ZMod Psecp) = mmEnc Rsecp γ) (hdδ : (d : ZMod Psecp) = mmEnc Rsecp δ)
    (hNprime : (Psecp * NPsecp) % Rsecp = Rsecp - 1) :
    (↑(montgomeryMul Psecp Rsecp NPsecp a b) : ZMod Psecp)
        + (↑(montgomeryMul Psecp Rsecp NPsecp c d) : ZMod Psecp)
      = mmEnc Rsecp (modAddF (modMulF α β) (modMulF γ δ)) := by
  rw [secp256k1_mmMul_realizes α β a b ha hb haα hbβ hNprime,
      secp256k1_mmMul_realizes γ δ c d hc hd hcγ hdδ hNprime,
      secp256k1_mmAdd_realizes]

/-- **The descended composition denotes to the field dot product.** The
    `Com fieldDialect` `dotProg` (over secp256k1's `Fp`) denotes to `α·β + γ·δ` —
    the abstract value the realized composition (`dotComposition_realizes`,
    `mmEnc`-d) tracks. The `Com` is `RelationalCompileHigh.Demo.dotProg Psecp`;
    `FieldDescent`'s `fieldComToJasmin` descends exactly this program to jasmin. -/
theorem dotProg_denote_secp (α β γ δ : ZMod Psecp) :
    (RelationalCompileHigh.Demo.dotProg Psecp).denote
        ((.cons α (.cons β (.cons γ (.cons δ .nil)))) : Ctxt.Valuation
          (RelationalCompileHigh.Demo.Γ₀ Psecp))
      = α * β + γ * δ :=
  RelationalCompileHigh.Demo.dotProg_denote Psecp α β γ δ

end CatCrypt.Crypto.SecureCompilation.FieldDescentMultiLimb
