/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.FieldDescentMultiLimb

/-!
# The multi-limb curve-field Stage-2 leaves, re-instantiated for P256 and BN254

`FieldDescentMultiLimb.lean` discharges the descent's three Stage-2 word-realization
squares (`mmMul_realizes` / `mmAdd_realizes` / `mmSub_realizes`) for the
**secp256k1** base-field prime, and routes the `a·b + c·d` field-op composition
(`RelationalCompileHigh.Demo.dotProg`) through them.

The three op-level squares there are stated **prime-parametric** (any `p, R, nP`
with `0 < p`, `p ≤ R`, `p · nP ≡ R − 1 mod R`). This file demonstrates that the
multi-limb skeleton is genuinely a **curve family** by re-instantiating those same
prime-parametric squares at two more 256-bit curve primes:

* **P256 / secp256r1** — `p = 2^256 − 2^224 + 2^192 + 2^96 − 1`
  (`Curve4LimbTierA.p256Limbs`, `p256Limbs_value`);
* **BN254** base field — `p = 21888242871839275222246405745257275088696311157297823662689037894645226208583`
  (`Curve4LimbTierA.bn254Limbs`, `bn254Limbs_value`).

For each curve we instantiate, exactly as the secp256k1 §3/§4 of
`FieldDescentMultiLimb`:

1. `P<curve> : Nat` / `R<curve> : Nat` — the prime (as the `valLimbs` of the
   curve's four little-endian limbs, pinned by the existing `native_decide`
   `*_value` lemma) and the 256-bit Montgomery radix `R = 2^256`;
2. the three realization squares `<curve>_mmMul_realizes` / `_mmAdd_realizes` /
   `_mmSub_realizes` (instances of the prime-parametric `mmMul_realizes` etc.);
3. the routed `a·b + c·d` composition `<curve>_dotComposition_realizes` and the
   denotation `<curve>_dotProg_denote`.

Nothing here is curve-specific beyond the prime constant and the `native_decide`
prime-pin (already discharged in `Curve4LimbTierA`): the *same* op-level proof
skeleton closes all of secp256k1 / P256 / BN254. This is the prime-parametric
claim made concrete for the curve family.

## What rides the compiler vs. GMP-KAT-gated (REV-12)

As in `FieldDescentMultiLimb`: the value-level Montgomery multiply
`Number.montgomeryMul p R nP` is proven (`montgomeryMul_correct`), and the
field-op *tree* (`a·b + c·d` over `ZMod p`) rides the compiler leaf-by-leaf over
that proven leaf. The single multi-limb *byte-identity* of the emitted `.s`
(`p256_montmul_proven` / `bn254_montmul_proven`, the `Curve4LimbTierA`
`*_emit_montmul_runBlock4` schoolbook+REDC block) stays **GMP-KAT-gated** — a
256×256→256 field multiply, **never** `#eval`'d in Lean (REV-12: that OOMs the
shared LSP).

**0 sorries.** Target axiom set `{propext, Classical.choice, Quot.sound}` plus
the `native_decide` LRAT certificates the per-curve prime pins cite
(`p256Limbs_value`, `bn254Limbs_value`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.FieldDescentCurves

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.Number (montgomeryMul)
open CatCrypt.Crypto.SecureCompilation.FieldDescentMultiLimb
  (mmEnc mmMul_realizes mmAdd_realizes mmSub_realizes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven (valLimbs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Curve4LimbTierA
  (p256Limbs p256Limbs_value bn254Limbs bn254Limbs_value)

/-! ## 1. P256 (secp256r1)

`p = valLimbs p256Limbs = 2^256 − 2^224 + 2^192 + 2^96 − 1`, `R = 2^256`. The
prime is pinned by the existing `native_decide` lemma `p256Limbs_value`
(`Curve4LimbTierA`), so the only curve-specific facts are `0 < p` and `p ≤ R`,
both `norm_num` after rewriting with `p256Limbs_value`. The full-radix
Montgomery constant pin `(p · nP) % 2^256 = 2^256 − 1` is threaded as a
hypothesis exactly as in secp256k1's instance. -/

/-- P256 base-field prime. -/
abbrev Pp256 : Nat := valLimbs p256Limbs
/-- The 256-bit Montgomery radix. -/
abbrev Rp256 : Nat := 2 ^ 256

lemma Pp256_pos : 0 < Pp256 := by rw [Pp256, p256Limbs_value]; norm_num
lemma Pp256_le_Rp256 : Pp256 ≤ Rp256 := by
  rw [Pp256, p256Limbs_value, Rp256]; norm_num

/-- **P256 `modMul` realization.** The instance of `mmMul_realizes` at the P256
    base-field prime with `R = 2^256`: casting the proven CIOS Montgomery product
    `montgomeryMul Pp256 Rp256 nP a b` into `ZMod Pp256` equals `mmEnc Rp256 (α·β)`
    on the Montgomery reps of `α, β`. -/
theorem p256_mmMul_realizes (nP : Nat) (α β : ZMod Pp256) (a b : Nat)
    (ha : a < Pp256) (hb : b < Pp256)
    (haα : (a : ZMod Pp256) = mmEnc Rp256 α) (hbβ : (b : ZMod Pp256) = mmEnc Rp256 β)
    (hNprime : (Pp256 * nP) % Rp256 = Rp256 - 1) :
    (↑(montgomeryMul Pp256 Rp256 nP a b) : ZMod Pp256) = mmEnc Rp256 (modMulF α β) :=
  mmMul_realizes Pp256_pos Pp256_le_Rp256 (by rw [Rp256]; norm_num) hNprime α β a b
    ha hb haα hbβ

/-- P256 `modAdd` realization (instance of `mmAdd_realizes`). -/
theorem p256_mmAdd_realizes (α β : ZMod Pp256) :
    mmEnc Rp256 α + mmEnc Rp256 β = mmEnc Rp256 (modAddF α β) :=
  mmAdd_realizes Rp256 α β

/-- P256 `modSub` realization (instance of `mmSub_realizes`). -/
theorem p256_mmSub_realizes (α β : ZMod Pp256) :
    mmEnc Rp256 α - mmEnc Rp256 β = mmEnc Rp256 (modSubF α β) :=
  mmSub_realizes Rp256 α β

/-- **The composition `a·b + c·d` realizes under the P256 Montgomery encoding.**
    From the three P256 leaf squares: the realized word ops on the Montgomery reps
    of `α, β, γ, δ` yield the Montgomery rep of `α·β + γ·δ` — the whole `dotProg`
    field-op tree, leaf-by-leaf, over the proven P256 multi-limb Montgomery
    multiply. -/
theorem p256_dotComposition_realizes (nP : Nat) (α β γ δ : ZMod Pp256)
    (a b c d : Nat)
    (ha : a < Pp256) (hb : b < Pp256) (hc : c < Pp256) (hd : d < Pp256)
    (haα : (a : ZMod Pp256) = mmEnc Rp256 α) (hbβ : (b : ZMod Pp256) = mmEnc Rp256 β)
    (hcγ : (c : ZMod Pp256) = mmEnc Rp256 γ) (hdδ : (d : ZMod Pp256) = mmEnc Rp256 δ)
    (hNprime : (Pp256 * nP) % Rp256 = Rp256 - 1) :
    (↑(montgomeryMul Pp256 Rp256 nP a b) : ZMod Pp256)
        + (↑(montgomeryMul Pp256 Rp256 nP c d) : ZMod Pp256)
      = mmEnc Rp256 (modAddF (modMulF α β) (modMulF γ δ)) := by
  rw [p256_mmMul_realizes nP α β a b ha hb haα hbβ hNprime,
      p256_mmMul_realizes nP γ δ c d hc hd hcγ hdδ hNprime,
      p256_mmAdd_realizes]

/-- **The descended composition denotes to the P256 field dot product.** The
    `Com fieldDialect` `dotProg` (over P256's `Fp`) denotes to `α·β + γ·δ` — the
    abstract value `p256_dotComposition_realizes` tracks under `mmEnc`. -/
theorem p256_dotProg_denote (α β γ δ : ZMod Pp256) :
    (RelationalCompileHigh.Demo.dotProg Pp256).denote
        ((.cons α (.cons β (.cons γ (.cons δ .nil)))) : Ctxt.Valuation
          (RelationalCompileHigh.Demo.Γ₀ Pp256))
      = α * β + γ * δ :=
  RelationalCompileHigh.Demo.dotProg_denote Pp256 α β γ δ

/-! ## 2. BN254 base field

`p = valLimbs bn254Limbs = 21888242871839275222246405745257275088696311157297823662689037894645226208583`,
`R = 2^256`. The prime is pinned by the existing `native_decide` lemma
`bn254Limbs_value` (`Curve4LimbTierA`). Same proof skeleton as P256 / secp256k1;
only the prime constant differs. -/

/-- BN254 base-field prime. -/
abbrev Pbn254 : Nat := valLimbs bn254Limbs
/-- The 256-bit Montgomery radix. -/
abbrev Rbn254 : Nat := 2 ^ 256

lemma Pbn254_pos : 0 < Pbn254 := by rw [Pbn254, bn254Limbs_value]; norm_num
lemma Pbn254_le_Rbn254 : Pbn254 ≤ Rbn254 := by
  rw [Pbn254, bn254Limbs_value, Rbn254]; norm_num

/-- **BN254 `modMul` realization.** The instance of `mmMul_realizes` at the BN254
    base-field prime with `R = 2^256`. -/
theorem bn254_mmMul_realizes (nP : Nat) (α β : ZMod Pbn254) (a b : Nat)
    (ha : a < Pbn254) (hb : b < Pbn254)
    (haα : (a : ZMod Pbn254) = mmEnc Rbn254 α) (hbβ : (b : ZMod Pbn254) = mmEnc Rbn254 β)
    (hNprime : (Pbn254 * nP) % Rbn254 = Rbn254 - 1) :
    (↑(montgomeryMul Pbn254 Rbn254 nP a b) : ZMod Pbn254) = mmEnc Rbn254 (modMulF α β) :=
  mmMul_realizes Pbn254_pos Pbn254_le_Rbn254 (by rw [Rbn254]; norm_num) hNprime α β a b
    ha hb haα hbβ

/-- BN254 `modAdd` realization (instance of `mmAdd_realizes`). -/
theorem bn254_mmAdd_realizes (α β : ZMod Pbn254) :
    mmEnc Rbn254 α + mmEnc Rbn254 β = mmEnc Rbn254 (modAddF α β) :=
  mmAdd_realizes Rbn254 α β

/-- BN254 `modSub` realization (instance of `mmSub_realizes`). -/
theorem bn254_mmSub_realizes (α β : ZMod Pbn254) :
    mmEnc Rbn254 α - mmEnc Rbn254 β = mmEnc Rbn254 (modSubF α β) :=
  mmSub_realizes Rbn254 α β

/-- **The composition `a·b + c·d` realizes under the BN254 Montgomery encoding.**
    From the three BN254 leaf squares: the realized word ops on the Montgomery
    reps of `α, β, γ, δ` yield the Montgomery rep of `α·β + γ·δ`. -/
theorem bn254_dotComposition_realizes (nP : Nat) (α β γ δ : ZMod Pbn254)
    (a b c d : Nat)
    (ha : a < Pbn254) (hb : b < Pbn254) (hc : c < Pbn254) (hd : d < Pbn254)
    (haα : (a : ZMod Pbn254) = mmEnc Rbn254 α) (hbβ : (b : ZMod Pbn254) = mmEnc Rbn254 β)
    (hcγ : (c : ZMod Pbn254) = mmEnc Rbn254 γ) (hdδ : (d : ZMod Pbn254) = mmEnc Rbn254 δ)
    (hNprime : (Pbn254 * nP) % Rbn254 = Rbn254 - 1) :
    (↑(montgomeryMul Pbn254 Rbn254 nP a b) : ZMod Pbn254)
        + (↑(montgomeryMul Pbn254 Rbn254 nP c d) : ZMod Pbn254)
      = mmEnc Rbn254 (modAddF (modMulF α β) (modMulF γ δ)) := by
  rw [bn254_mmMul_realizes nP α β a b ha hb haα hbβ hNprime,
      bn254_mmMul_realizes nP γ δ c d hc hd hcγ hdδ hNprime,
      bn254_mmAdd_realizes]

/-- **The descended composition denotes to the BN254 field dot product.** -/
theorem bn254_dotProg_denote (α β γ δ : ZMod Pbn254) :
    (RelationalCompileHigh.Demo.dotProg Pbn254).denote
        ((.cons α (.cons β (.cons γ (.cons δ .nil)))) : Ctxt.Valuation
          (RelationalCompileHigh.Demo.Γ₀ Pbn254))
      = α * β + γ * δ :=
  RelationalCompileHigh.Demo.dotProg_denote Pbn254 α β γ δ

end CatCrypt.Crypto.SecureCompilation.FieldDescentCurves
