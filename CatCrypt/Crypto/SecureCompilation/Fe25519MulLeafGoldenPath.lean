/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.FieldMul2x1GoldenPath
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.FieldMul2x1GoldenPath
public meta import CatCrypt.Crypto.SecureCompilation.Fe25519AddLeafGoldenPath
public import CatCrypt.Crypto.SecureCompilation.Fe25519AddLeafGoldenPath
public meta import CatCrypt.Crypto.SecureCompilation.VIR.KernelSyntax
public import CatCrypt.Crypto.SecureCompilation.VIR.KernelSyntax
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfFull
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OptimizedComToElfFull
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Grind
public import CatCrypt.Crypto.SecureCompilation.VIR.Grind
public import Std.Tactic.BVDecide

/-!
# Golden path: the fe25519 field-multiply leaf as a word-level `Com jasminDialect`

The multiply companion of `Fe25519AddLeafGoldenPath`. Unlike radix-2⁵¹ field *add*
(pointwise, carry-free, no reduction — one word op per limb), field *multiply* is the
5×5-limb schoolbook product with the `2²⁵⁵ ≡ 19` fold and carry propagation. Its
word-level realisation (the deployed HACL\* / ADX `fe25519_mul`) is a straight-line
chain of **multiply-accumulate columns**: for each output limb, five 64×64→128 widening
products (`MULX`) accumulated into a wide accumulator via the dual `ADCX`/`ADOX` carry
chains. `X86Backend.RunBlockLsemAgree.mac2_columns_lsem_agree` already bridges such an
unrolled MAC-column body `runBlock ↔ lsem`; this file supplies the **front side** — the
MAC-column unit as a front-generated `Com jasminDialect` (`denote = spec`), and the
reduction algebra as a proven congruence, so a byte-level `fe25519_mul` can be assembled
on the golden path (no hand-authored `Com`).

## What is proved (0 sorries)

### The reduction algebra (the `2²⁵⁵ ≡ 19` fold)

* `feMulR0 … feMulR4` — the five wide schoolbook column accumulators (the pre-reduction
  `MULX`/`ADCX`/`ADOX` targets), each a sum of five `19`-folded limb products.
* `feMulAccum` — the reconstructed integer `Σ rₖ · 2⁵¹ᵏ` of those columns.
* `feMul_accum_congr` — **the field-multiply correctness core**: the reconstructed column
  sum is congruent to the exact integer product mod `p = 2²⁵⁵ − 19`. The fold witness is
  `feMulFold` (the `i+j ≥ 5` limb products at their folded weight); the whole identity is
  a `ring` fact `feToNat51 a · feToNat51 b − feMulAccum a b = p · feMulFold a b`. This is
  the algebraic heart of the radix-2⁵¹ multiply — the reduction the carry-free add leaf
  never needed.

### The canonical carry reduction and the deployed 5-limb multiply

* `feCarryLimbNat` / `feCarryNat` — the radix-2⁵¹ carry chain (`/ 2⁵¹`, `% 2⁵¹`, top
  `c₄ · 19` fold, second short carry) propagating the wide column accumulators `rₖ` to the
  deployed 5-limb `BitVec 64` result. Mirrors `Curve25519AdxPrototype.feCarryNat`.
* `feCarry_balance` — the carry-balance identity (`omega`): the chain preserves the
  reconstructed value except the top-carry fold, `feMulAccum + 19·c₄ = feCarryVal + c₄·2²⁵⁵`.
* `feCarryVal_accum_congr` / `feCarryVal_congr` — the reduced value is congruent to
  `feMulAccum`, hence (chaining onto `feMul_accum_congr`) to the exact integer product mod `p`.
* `fe25519_mul_deployed_congr` — **the full multiply-mod-`p` correctness on the DEPLOYED
  5-limb result**: `feToNat51 (feCarryNat a b) ≡ feToNat51 a · feToNat51 b [ZMOD 2²⁵⁵−19]`,
  under the radix-2⁵¹ output limb bound `feCarryLimbNat a b i < 2⁶⁴`. Schoolbook columns +
  `2²⁵⁵ ≡ 19` fold + canonical carry reduction — the complete field-multiply arithmetic.

### The MAC-column unit as a `Com jasminDialect`

* `fe25519MacColLoCom` — one multiply-accumulate column's **low word**
  `acc_lo + a·b` as a `Com jasminDialect` over `[acc_lo, acc_hi, a, b]`, in the
  `regArith .mul` / `regArith .add` alphabet (the `MULX`+`ADCX` low-word write).
* `fe25519MacColLoCom_denote` — `denote = acc_lo + a * b`, by `rfl` (the golden-path
  value step).
* `fe25519_mac_column_reconstruct` — the widening MAC value law: the emitted low word,
  high word (`fieldAdcCom`), and carry reassemble the exact wide accumulate
  `new_lo + new_hi · 2⁶⁴ = acc_lo + acc_hi · 2⁶⁴ + a·b`, under the radix-2⁵¹
  no-top-overflow headroom bound (`acc_hi + hi(a·b) + c < 2⁶⁴`, which the five-column
  fe25519 accumulator satisfies). Built entirely from the emitted `FieldEmitGoldenPath`
  primitives (`fieldMulLoCom`/`fieldMulHiCom`/`fieldAddCom`/`fieldAddCarryCom`/
  `fieldAdcCom`) — the same `MULX`/`ADCX`/`ADOX` unit `mac2_columns_lsem_agree` composes.

### The whole schoolbook column, front-composed from the emitted primitives

* `macStep` / `macFold` — the `MULX`+`ADCX`/`ADOX` accumulate step and its fold over a
  product list, threading a 128-bit `(lo, hi)` accumulator, both expressed **entirely over
  the emitted `FieldEmitGoldenPath` primitives** (`fieldAddCom`/`fieldAddCarryCom`/
  `fieldAdcCom`/`mulHiW`) — no new op.
* `macFold_reconstruct` — **the multi-product column-accumulate value law**: the folded
  128-bit accumulator reconstructs the exact integer sum `Σ aₖ·bₖ` (under the running
  radix-2⁵¹ headroom `macFoldHeadroom`). Proved by induction from the single-product
  `fe25519_mac_column_reconstruct` — the composition of the emitted MAC unit into a whole
  column. This is the per-column re-tie the array `Com`'s `denote = feCarryNat` folds.
* `col0_reconstruct` — a concrete instance: folding column 0's five 19-folded products
  reconstructs exactly `feMulR0` (the §1 accumulator), tying the composed emitted
  primitives to the reduction algebra (`mul19_toNat`: the `19·aⱼ` prescale does not wrap).
  The other four columns are the same fold.

### The array-returning product `Com` and its correctness

* `fe25519MulProductCom` — the **array-assembly writeback** as a front-generated
  `Com jasminDialect (stackArr 64 5 :: reg 64 × 5) (stackArr 64 5)`: a `stackStore`-chain
  built by the generator `mulPackTail` (not a hand-authored de Bruijn literal), writing the
  five reduced limbs into one array and returning it — the same shape as
  `CompileFromHaxSha256CompressProductTie.packCom`.
* `fe25519MulProductCom_denote` — the writeback returns exactly the five supplied limbs
  (`mulPackTail_denote` / `mulPackFold_full`, by induction from the single-`stackStore`
  step).
* `fe25519MulProductCom_feCarryNat` — instantiated on the deployed reduced limbs
  `feCarryNat a b`, the product `Com` denotes to the whole deployed 5-limb `fe25519_mul`
  output as one `stackArr 64 5` value.
* `fe25519_mul_leaf_congr` — **the full multiply-mod-`p` correctness on the array leaf**:
  the reconstructed integer of the product-output array `Com` is congruent to
  `feToNat51 a · feToNat51 b` mod `p`, under the radix-2⁵¹ output bound — the deployed-result
  correctness (`fe25519_mul_deployed_congr`) transferred through the array writeback.

No `sorry`, no `native_decide`, no new axioms (beyond the `bv_decide`/`native_decide`
axioms the golden-path primitives it composes already carry).

### The word-level carry reduction as `Com` ops (§6)

* `carryWord_toNat` / `limbWord_toNat` — the two word-level carry-extraction bridges: the
  `shrImm 51`/`shlImm 13`/`|||` carry op realises `⌊(lo + hi·2⁶⁴) / 2⁵¹⌋` (under the
  radix-2⁵¹ high-word bound `hi < 2⁴⁴`) and the `&&& (2⁵¹−1)` limb op realises
  `(lo + hi·2⁶⁴) mod 2⁵¹`, connecting the deployed `carry_wide` word ops to the `Nat`
  `feCarryLimbNat` chain. `bv_decide`-clean.
* `wordExtract` / `wordExtract_limb` / `wordExtract_carry` / `wordExtract_reconstruct` —
  the two ops packaged as the atomic `(limb, carry)` extract on a `(lo, hi)` column
  accumulator, with the radix-2⁵¹ digit identity `limb + carry·2⁵¹ = lo + hi·2⁶⁴`.
* `carryAddStep` / `carryAddStep_reconstruct` — the forward carry-add `tₖ₊₁ = Rₖ₊₁ + cₖ`
  as a trivial-product `macStep _ _ c 1` (no new op), a corollary of the single-product MAC
  value law. So the whole `feCarryLimbNat` chain is expressible over §4's emitted MAC
  primitives plus §6's extract op.

## Residual (reported, not swept under)

The whole word-level reduction is closed as one model over the emitted primitives:
`feMulModel` (§7) runs the five column `macFold`s, the `colReduce` carry chain, the `c₄·19`
top fold, and the final short carry, and `feMulModel_eq_feCarryNat` proves it equals the
deployed 5-limb result `feCarryNat a b` under the radix-2⁵¹ column bounds — the straight-line
reduction unfold, threading `col0_reconstruct … col4_reconstruct` per column and
`colReduce_limb`/`colReduce_carry` per carry. Fed through the array writeback,
`fe25519MulProductCom_feMulModel` denotes to `feCarryNat a b` and `fe25519_mul_model_leaf_congr`
carries the full multiply-mod-`p` correctness to the front-generated computation. The reduction
algebra down to `fe25519_mul_deployed_congr` and the carry-word ops (§6) are all proved.

The remaining piece is purely **syntactic**: emitting `feMulModel` as inline `Com jasminDialect`
ops on the single `[stackArr 64 5, stackArr 64 5] → stackArr 64 5` context — a de Bruijn-threaded
generator that (i) loads `a`/`b` via `stackLoad`, (ii) runs the five column products via
`fieldMulLoCom`/`fieldMulHiCom` over the 128-bit `(lo, hi)` chains, (iii) runs the carry chain as
the §6 `Com` ops (`shrImm 51` / `&&& mask51` / `shlImm 13` / `|||` / the `c₄·19` fold via
`regConst 64 19` + `carryAddStep`), then (iv) chains into `fe25519MulProductCom`. Its
`denote = feMulModel` closes by the same per-op value laws (`macFold_reconstruct` per column,
`wordExtract`/`carryAddStep` per carry); composed with `feMulModel_eq_feCarryNat` that gives
`denote = feCarryNat`. The arithmetic is closed; what remains is the context-threading Com
generation (as `mulPackTail` is generated, not a hand-`Com` twin).

**Routing note (do NOT add a `jasminExtSem` arm for a width-64 leaf):** a non-default
`jasminExtSem` arm with a width-64 return (`.reg 64` / `.stackArr 64 _`) breaks the
`jasminExtSem_reg` / `jasminExtSem_stackArr64` invariants in `VIR/JasminValTransport.lean`
(all width-64 returns must be `JasminTy.default`), which are load-bearing for
`DialectToJasminComCorrect`. Only the width-16 `stackArr` lattice leaves may carry a
non-default arm. The named-call non-vacuous consumption of `fe25519_mul` must therefore go
through the separate `ComInlineCall` `FuncRegistryN` / `RegistryConsistentN` registry (or
the leaf's own `denote`), **not** `jasminExtSem`.

The reduction algebra, the MAC-column `Com`, the five per-column composition value laws
(`macFold_reconstruct` / `col0_reconstruct … col4_reconstruct`), the carry-reduction step
(`colReduce`), the whole-reduction model equal to the deployed result
(`feMulModel_eq_feCarryNat`), and the full multiply-mod-`p` correctness on the front-generated
computation (`fe25519_mul_model_leaf_congr`) are what this file lands.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Fe25519MulLeaf

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Fe25519AddLeaf (Fe51 feToNat51)
open CatCrypt.Crypto.SecureCompilation.FieldEmitGoldenPath
open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.ScalarLinFront
open CatCrypt.Crypto.SecureCompilation.ScalarLinDeBruijn
open CatCrypt.Crypto.SecureCompilation.ScalarLinNeutralDemo
open CatCrypt.Crypto.SecureCompilation.MultiBackendDemo
open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ComToArm
open CatCrypt.Crypto.SecureCompilation.RISCVBackend
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RegToRiscv

/-! ## 1. The wide schoolbook column accumulators and the reduction algebra

Radix-2⁵¹, HACL\* `Curve25519_51`. The `19·aⱼ` factors (for the limbs whose product
lands past `2²⁵⁵`) precompute the `2²⁵⁵ ≡ 19 (mod p)` wrap-around, exactly as the
`Curve25519AdxPrototype.feMul` reference does. -/

/-- Column 0 accumulator: `a₀b₀ + 19(a₄b₁ + a₃b₂ + a₂b₃ + a₁b₄)`. -/
def feMulR0 (a b : Fe51) : Nat :=
  (a 0).toNat * (b 0).toNat + 19 * (a 4).toNat * (b 1).toNat
    + 19 * (a 3).toNat * (b 2).toNat + 19 * (a 2).toNat * (b 3).toNat
    + 19 * (a 1).toNat * (b 4).toNat

/-- Column 1 accumulator: `a₀b₁ + a₁b₀ + 19(a₄b₂ + a₃b₃ + a₂b₄)`. -/
def feMulR1 (a b : Fe51) : Nat :=
  (a 0).toNat * (b 1).toNat + (a 1).toNat * (b 0).toNat
    + 19 * (a 4).toNat * (b 2).toNat + 19 * (a 3).toNat * (b 3).toNat
    + 19 * (a 2).toNat * (b 4).toNat

/-- Column 2 accumulator: `a₀b₂ + a₁b₁ + a₂b₀ + 19(a₄b₃ + a₃b₄)`. -/
def feMulR2 (a b : Fe51) : Nat :=
  (a 0).toNat * (b 2).toNat + (a 1).toNat * (b 1).toNat + (a 2).toNat * (b 0).toNat
    + 19 * (a 4).toNat * (b 3).toNat + 19 * (a 3).toNat * (b 4).toNat

/-- Column 3 accumulator: `a₀b₃ + a₁b₂ + a₂b₁ + a₃b₀ + 19 a₄b₄`. -/
def feMulR3 (a b : Fe51) : Nat :=
  (a 0).toNat * (b 3).toNat + (a 1).toNat * (b 2).toNat + (a 2).toNat * (b 1).toNat
    + (a 3).toNat * (b 0).toNat + 19 * (a 4).toNat * (b 4).toNat

/-- Column 4 accumulator: `a₀b₄ + a₁b₃ + a₂b₂ + a₃b₁ + a₄b₀`. -/
def feMulR4 (a b : Fe51) : Nat :=
  (a 0).toNat * (b 4).toNat + (a 1).toNat * (b 3).toNat + (a 2).toNat * (b 2).toNat
    + (a 3).toNat * (b 1).toNat + (a 4).toNat * (b 0).toNat

/-- The integer reconstructed from the five wide column accumulators, at radix-2⁵¹
    digit weights — the value the `MULX`/`ADCX`/`ADOX` column chain computes before the
    canonical carry reduction. -/
def feMulAccum (a b : Fe51) : Nat :=
  feMulR0 a b + feMulR1 a b * 2 ^ 51 + feMulR2 a b * 2 ^ 102
    + feMulR3 a b * 2 ^ 153 + feMulR4 a b * 2 ^ 204

/-- The fold witness: the `i+j ≥ 5` limb products at their post-fold weight `2⁵¹⁽ⁱ⁺ʲ⁻⁵⁾`.
    This is exactly the integer `S` with `feToNat51 a · feToNat51 b − feMulAccum a b = p·S`
    (each folded term differs from the direct product by `(2²⁵⁵ − 19)` times its weight). -/
def feMulFold (a b : Fe51) : Nat :=
  ((a 1).toNat * (b 4).toNat + (a 2).toNat * (b 3).toNat
      + (a 3).toNat * (b 2).toNat + (a 4).toNat * (b 1).toNat)
  + ((a 2).toNat * (b 4).toNat + (a 3).toNat * (b 3).toNat
      + (a 4).toNat * (b 2).toNat) * 2 ^ 51
  + ((a 3).toNat * (b 4).toNat + (a 4).toNat * (b 3).toNat) * 2 ^ 102
  + ((a 4).toNat * (b 4).toNat) * 2 ^ 153

/-- **The exact fold identity** (`ring`). Over the integers, the difference between the
    true product and the reconstructed column sum is `p = 2²⁵⁵ − 19` times the fold
    witness — the whole content of the `2²⁵⁵ ≡ 19` reduction, as a polynomial identity. -/
theorem feMul_fold_identity (a b : Fe51) :
    (feToNat51 a : ℤ) * (feToNat51 b) - (feMulAccum a b : ℤ)
      = ((2 : ℤ) ^ 255 - 19) * (feMulFold a b) := by
  simp only [feToNat51, feMulAccum, feMulR0, feMulR1, feMulR2, feMulR3, feMulR4, feMulFold]
  push_cast
  ring

/-- **The field-multiply reduction correctness (algebraic core).** The reconstructed
    column-accumulator sum is congruent to the exact integer product mod `p = 2²⁵⁵ − 19`.
    This is the radix-2⁵¹ schoolbook multiply's reduction, proved from the exact fold
    identity `feMul_fold_identity`. The remaining step to the canonical 5-limb result is
    the carry reduction `feCarryNat` (the reported residual). -/
theorem feMul_accum_congr (a b : Fe51) :
    (feMulAccum a b : ℤ) ≡ (feToNat51 a : ℤ) * (feToNat51 b) [ZMOD ((2 : ℤ) ^ 255 - 19)] := by
  refine Int.modEq_iff_dvd.mpr ⟨feMulFold a b, ?_⟩
  have h := feMul_fold_identity a b
  linarith [h]

/-! ## 1b. The canonical carry reduction to the deployed 5-limb result

`feCarryNat` is the radix-2⁵¹ carry chain that propagates the five wide column
accumulators `r₀..r₄` (`feMulR0..feMulR4`) down to five limbs, folding the top carry
`c₄·2²⁵⁵ ≡ c₄·19 (mod p)` back into limb 0 (a second short carry then lands the enlarged
limb 0 into limb 1). This mirrors `Curve25519AdxPrototype.feCarryNat` — the deployed
HACL\*/fiat `carry_wide` shape (`w >>> 51`, `w &&& (2⁵¹−1)`, i.e. `/ 2⁵¹`, `% 2⁵¹`).

The whole content is the **carry-balance** identity `feCarry_balance`: over `ℕ` the
carry chain redistributes value between limbs and the top-carry fold trades
`c₄·2²⁵⁵` for `c₄·19`, i.e. `feCarryVal + 19·c₄ = feMulAccum + c₄·2²⁵⁵`. Hence the
reconstructed reduced value is congruent to `feMulAccum` mod `p`, and composing with
`feMul_accum_congr` gives the full multiply-mod-`p` correctness on the deployed 5-limb
result (`fe25519_mul_deployed_congr`). -/

/-- The top carry `c₄` out of the five-limb carry chain (folded, times `19`, into
    limb 0 by the `2²⁵⁵ ≡ 19` trick). -/
def feCarryTop (a b : Fe51) : Nat :=
  let c0 := feMulR0 a b / 2 ^ 51
  let c1 := (feMulR1 a b + c0) / 2 ^ 51
  let c2 := (feMulR2 a b + c1) / 2 ^ 51
  let c3 := (feMulR3 a b + c2) / 2 ^ 51
  (feMulR4 a b + c3) / 2 ^ 51

/-- The reduced Nat limbs (`< 2⁵¹` except limb 1, which carries the tiny fold overflow).
    Element `i` of the deployed 5-limb result before the `BitVec` cast. Mirrors
    `Curve25519AdxPrototype.feCarryNat`. -/
def feCarryLimbNat (a b : Fe51) : Fin 5 → Nat :=
  let c0 := feMulR0 a b / 2 ^ 51
  let t1 := feMulR1 a b + c0; let c1 := t1 / 2 ^ 51
  let t2 := feMulR2 a b + c1; let c2 := t2 / 2 ^ 51
  let t3 := feMulR3 a b + c2; let c3 := t3 / 2 ^ 51
  let t4 := feMulR4 a b + c3; let c4 := t4 / 2 ^ 51
  let l0raw := feMulR0 a b % 2 ^ 51 + 19 * c4
  ![ l0raw % 2 ^ 51,
     t1 % 2 ^ 51 + l0raw / 2 ^ 51,
     t2 % 2 ^ 51,
     t3 % 2 ^ 51,
     t4 % 2 ^ 51 ]

/-- The integer reconstructed from the five **reduced** limbs (the value the deployed
    5-limb result denotes). The carry chain with the `c₄·19` top fold, in radix 2⁵¹. -/
def feCarryVal (a b : Fe51) : Nat :=
  feCarryLimbNat a b 0 + feCarryLimbNat a b 1 * 2 ^ 51 + feCarryLimbNat a b 2 * 2 ^ 102
    + feCarryLimbNat a b 3 * 2 ^ 153 + feCarryLimbNat a b 4 * 2 ^ 204

/-- **The carry-balance identity** (`omega`). Over `ℕ`: the carry chain preserves the
    reconstructed value except for the top-carry fold, which trades `c₄·2²⁵⁵` for `c₄·19`,
    i.e. `feMulAccum + 19·c₄ = feCarryVal + c₄·2²⁵⁵`. Purely linear over the wide
    accumulators (`feMulR0..feMulR4` are opaque atoms; the only nonlinearity is `/ 2⁵¹`,
    `% 2⁵¹`, which `omega` discharges after the `![·]` indices reduce). -/
theorem feCarry_balance (a b : Fe51) :
    feMulAccum a b + 19 * feCarryTop a b
      = feCarryVal a b + feCarryTop a b * 2 ^ 255 := by
  simp only [feCarryVal, feCarryLimbNat, feCarryTop, feMulAccum,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  omega

/-- **The deployed 5-limb field-multiply result** `fe25519_mul a b`: the schoolbook
    column accumulators reduced by the canonical carry chain, each limb cast to a
    `BitVec 64`. This is the radix-2⁵¹ HACL\* `Curve25519_51.fmul` output shape. -/
def feCarryNat (a b : Fe51) : Fe51 :=
  fun i => BitVec.ofNat 64 (feCarryLimbNat a b i)

/-- The reconstructed integer of the deployed 5-limb result equals `feCarryVal` when
    every reduced limb fits in a word (the radix-2⁵¹ output bound — limb 1 carries at
    most a tiny fold overflow, the rest are `< 2⁵¹`). Mirrors the add leaf's `hb`. -/
theorem feCarryNat_toNat (a b : Fe51)
    (hlt : ∀ i : Fin 5, feCarryLimbNat a b i < 2 ^ 64) :
    feToNat51 (feCarryNat a b) = feCarryVal a b := by
  have e : ∀ i : Fin 5, (feCarryNat a b i).toNat = feCarryLimbNat a b i := by
    intro i
    simp only [feCarryNat, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (hlt i)
  simp only [feToNat51, e, feCarryVal]

/-- **The reduced value is congruent to the column-accumulator sum mod `p`.** From the
    carry-balance identity: `feMulAccum − feCarryVal = c₄·(2²⁵⁵ − 19) = c₄·p`. -/
theorem feCarryVal_accum_congr (a b : Fe51) :
    (feCarryVal a b : ℤ) ≡ (feMulAccum a b : ℤ) [ZMOD ((2 : ℤ) ^ 255 - 19)] := by
  refine Int.modEq_iff_dvd.mpr ⟨feCarryTop a b, ?_⟩
  have h := feCarry_balance a b
  have hz : (feMulAccum a b : ℤ) + 19 * feCarryTop a b
      = (feCarryVal a b : ℤ) + feCarryTop a b * 2 ^ 255 := by exact_mod_cast h
  linarith [hz]

/-- **Field-multiply correctness on the reduced value** — the reconstructed value of the
    canonical carry reduction is congruent to the exact integer product mod `p`. Chains
    the carry reduction (`feCarryVal_accum_congr`) onto the reduction algebra
    (`feMul_accum_congr`): the whole radix-2⁵¹ schoolbook multiply, reduced. -/
theorem feCarryVal_congr (a b : Fe51) :
    (feCarryVal a b : ℤ) ≡ (feToNat51 a : ℤ) * feToNat51 b [ZMOD ((2 : ℤ) ^ 255 - 19)] :=
  (feCarryVal_accum_congr a b).trans (feMul_accum_congr a b)

/-- **The full multiply-mod-`p` correctness on the DEPLOYED 5-limb result.** For inputs
    whose reduced limbs fit in a word (the radix-2⁵¹ output bound `hlt`), the reconstructed
    integer of `feCarryNat a b` — the deployed `fe25519_mul` 5-limb output — is congruent
    to the exact integer product `feToNat51 a · feToNat51 b` mod `p = 2²⁵⁵ − 19`. This is
    the complete field-multiply correctness: schoolbook columns + `2²⁵⁵ ≡ 19` fold +
    canonical carry reduction. -/
theorem fe25519_mul_deployed_congr (a b : Fe51)
    (hlt : ∀ i : Fin 5, feCarryLimbNat a b i < 2 ^ 64) :
    (feToNat51 (feCarryNat a b) : ℤ) ≡ (feToNat51 a : ℤ) * feToNat51 b [ZMOD ((2 : ℤ) ^ 255 - 19)] := by
  rw [feCarryNat_toNat a b hlt]
  exact feCarryVal_congr a b

/-! ## 2. The multiply-accumulate column as a word-level `Com jasminDialect`

One MAC column's low-word write `acc_lo + a·b` (the `MULX` low + `ADCX` accumulate),
over `[acc_lo, acc_hi, a, b]` (de Bruijn: `acc_lo = .here`, `acc_hi = .there.here`,
`a = .there.there.here`, `b = .there.there.there.here`). Two ops — a `regArith .mul`
(the `MULX` low word) and a `regArith .add` (the `ADCX` accumulate) — both on the
golden-path all-`reg 64` alphabet, so `denote` is a cheap `rfl`. The high word and carry
that thread into the next column are the emitted `fieldMulHiCom` / `fieldAddCarryCom`
primitives, tied together by `fe25519_mac_column_reconstruct` below. -/

/-- The 4-input MAC-column context `[acc_lo, acc_hi, a, b]` is all-`reg 64`. -/
theorem allReg64_four :
    AllReg64 ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect) := by
  intro u hu
  rcases List.mem_cons.mp hu with h | h
  · exact h
  · rcases List.mem_cons.mp h with h | h
    · exact h
    · rcases List.mem_cons.mp h with h | h
      · exact h
      · rcases List.mem_cons.mp h with h | h
        · exact h
        · exact absurd h List.not_mem_nil

/-- **The MAC-column low-word source.** `p_lo := a * b ; s := acc_lo + p_lo ; ret s`
    over `[acc_lo, acc_hi, a, b]` — the `MULX` low word plus the `ADCX` accumulate. -/
def fe25519MacColLoCom : Com jasminDialect [.reg 64, .reg 64, .reg 64, .reg 64] (.reg 64) :=
  -- p_lo := a * b     (a = .there.there.here, b = .there.there.there.here)
  .var { op := .regArith .mul 64, retTy_eq := rfl,
         args := .cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil) }
  -- s := acc_lo + p_lo   (acc_lo = .there.here, p_lo = .here)
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here))

/-- `fe25519MacColLoCom` is in the supported straight-line fragment (`mul`, `add`). -/
theorem fe25519MacColLoCom_ok : ComOK fe25519MacColLoCom :=
  ComOK.var (by supported_op) (ComOK.var (by supported_op) (ComOK.ret _))

/-- **Step value — `rfl`.** The MAC-column source denotes the low-word accumulate
    `acc_lo + a·b` (the `MULX` low word added into the running accumulator). -/
theorem fe25519MacColLoCom_denote (acc_lo acc_hi a b : BitVec 64) :
    Com.denote fe25519MacColLoCom (.cons acc_lo (.cons acc_hi (.cons a (.cons b .nil))))
      = acc_lo + a * b := rfl

/-- **The MAC-column low word emits to AArch64** (`mul` + `add`), discharged by
    `com_arm_e2e` via the single `comToReg_faithful`. -/
theorem fe25519MacColLoCom_arm_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : BState) (hs : s.regs = envOf 4 V) :
    ((ComToArm.armTarget.runOps s
        (ComToArm.armTarget.compile (comToRegProg fe25519MacColLoCom 4))).regs)
        (comRetName fe25519MacColLoCom 4)
      = Com.denote fe25519MacColLoCom V :=
  com_arm_e2e fe25519MacColLoCom_ok allReg64_four V s hs

/-- **The same source emits to RISC-V** — one source, two backends, both discharged
    by the single `comToReg_faithful`. -/
theorem fe25519MacColLoCom_riscv_e2e
    (V : Ctxt.Valuation ([.reg 64, .reg 64, .reg 64, .reg 64] : Ctxt jasminDialect))
    (s : RState64) (hs : s.regs = envOf 4 V) :
    ((RegToRiscv.rvTarget.runOps s
        (RegToRiscv.rvTarget.compile (comToRegProg fe25519MacColLoCom 4))).regs)
        (comRetName fe25519MacColLoCom 4)
      = Com.denote fe25519MacColLoCom V :=
  com_riscv_e2e fe25519MacColLoCom_ok allReg64_four V s hs

/-- **The x86 owned-emit leg, via the optimized full-ELF entry.**
    Emits through `OptimizedComToElfFull.optimizedCompileComToElf`; correctness uses
    `optimizedCompileComToElf_sound` (the optimized block is `runBlock`-equal to the
    unoptimized gathered block on every input) together with the executed spec-KAT in
    `bench/x25519_fieldmul_compare/`, not byte identity with `compileComToElf`. -/
def fe25519MacColLoCom_x86_elf : ByteArray :=
  X86Backend.OptimizedComToElfFull.optimizedCompileComToElf fe25519MacColLoCom "fe25519_mac_col_lo"

/-! ## 3. The widening MAC value law — the two emitted words reassemble the accumulate

The MAC-column unit produces a two-word `(new_lo, new_hi)`: `new_lo = acc_lo + (a·b low)`
(emitted `fieldAddCom` on the `MULX` low word) and `new_hi = acc_hi + (a·b high) + c`
(emitted `fieldAdcCom` on the `MULX` high word plus the low-word carry-out `c` from
`fieldAddCarryCom`). They reassemble the exact wide accumulate. The `new_hi` step reuses
the `MULX` high word `mulHiW` and the carry chain — the `ADCX`/`ADOX` dual accumulation
at the value level. The bound `acc_hi + hi(a·b) + c < 2⁶⁴` is the radix-2⁵¹ headroom
(the fe25519 five-column accumulator never overflows the high word within a column). -/

/-- **The widening MAC value law.** For accumulator `acc = acc_lo + acc_hi · 2⁶⁴` and a
    single product `a·b` (as the `MULX` pair `mulHiW a b : a * b`), the emitted low word
    `new_lo = acc_lo + (a·b low)` (`fieldAddCom`) and high word
    `new_hi = acc_hi + mulHiW a b + c` (`fieldAdcCom`, `c` the low-word carry-out of
    `fieldAddCarryCom`) reassemble the exact wide accumulate
    `new_lo + new_hi · 2⁶⁴ = acc_lo + acc_hi · 2⁶⁴ + a·b`, under the radix-2⁵¹
    no-high-overflow headroom `acc_hi + mulHiW a b + c < 2⁶⁴`. Closes by the single-`MULX`
    widening law `mulx_reconstruct` and the limb-0 carry split `fieldAdd_carry_reconstruct`. -/
theorem fe25519_mac_column_reconstruct (acc_lo acc_hi a b : BitVec 64)
    (hhead : acc_hi.toNat
        + (Com.denote fieldAddCarryCom (.cons (a * b) (.cons acc_lo .nil))).toNat
        + (mulHiW a b).toNat < 2 ^ 64) :
    (Com.denote fieldAddCom (.cons (a * b) (.cons acc_lo .nil))).toNat
      + (Com.denote fieldAdcCom (.cons acc_hi (.cons (mulHiW a b)
          (.cons (Com.denote fieldAddCarryCom (.cons (a * b) (.cons acc_lo .nil))) .nil)))).toNat
          * 2 ^ 64
      = acc_lo.toNat + acc_hi.toNat * 2 ^ 64 + a.toNat * b.toNat := by
  -- name the low-word carry-out (the `ADCX` carry threaded into the high word)
  set c := Com.denote fieldAddCarryCom (.cons (a * b) (.cons acc_lo .nil)) with hc
  -- the `MULX` widening: (a·b low) + (a·b high)·2⁶⁴ = a·b
  have ew : (a * b).toNat + (mulHiW a b).toNat * 2 ^ 64 = a.toNat * b.toNat :=
    MontMulFragmentDemo.mulx_reconstruct a b
  -- the low-word split: new_lo + c·2⁶⁴ = acc_lo + (a·b low)   (emitted add low + carry)
  have elo : (Com.denote fieldAddCom (.cons (a * b) (.cons acc_lo .nil))).toNat
        + c.toNat * 2 ^ 64 = acc_lo.toNat + (a * b).toNat := by
    rw [hc]; exact fieldAdd_carry_reconstruct (a * b) acc_lo
  -- the high word never wraps (headroom): new_hi = acc_hi + mulHiW a b + c exactly
  have ehi : (Com.denote fieldAdcCom (.cons acc_hi (.cons (mulHiW a b) (.cons c .nil)))).toNat
        = acc_hi.toNat + (mulHiW a b).toNat + c.toNat := by
    rw [fieldAdcCom_denote]
    have h1 : (acc_hi + mulHiW a b).toNat = acc_hi.toNat + (mulHiW a b).toNat := by
      rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
  rw [ehi]
  -- make `c` opaque and abbreviate the deep denote / product atoms, so the final
  -- step is small & linear (avoids recursing into the nested `Com.denote` terms)
  clear hhead ehi hc
  clear_value c
  generalize hL : (Com.denote fieldAddCom (.cons (a * b) (.cons acc_lo .nil))).toNat = L at elo ⊢
  generalize hP : (a * b).toNat = P at elo ew
  generalize hH : (mulHiW a b).toNat = H at ew ⊢
  generalize hAB : a.toNat * b.toNat = AB at ew ⊢
  clear hL hP hH hAB
  -- linear over {L, c.toNat, H·2⁶⁴, acc_lo, acc_hi, P, AB} given elo, ew
  calc L + (acc_hi.toNat + H + c.toNat) * 2 ^ 64
      = (L + c.toNat * 2 ^ 64) + acc_hi.toNat * 2 ^ 64 + H * 2 ^ 64 := by ring
    _ = (acc_lo.toNat + P) + acc_hi.toNat * 2 ^ 64 + H * 2 ^ 64 := by rw [elo]
    _ = acc_lo.toNat + acc_hi.toNat * 2 ^ 64 + (P + H * 2 ^ 64) := by ring
    _ = acc_lo.toNat + acc_hi.toNat * 2 ^ 64 + AB := by rw [ew]

/-! ## 4. Composing the emitted MAC primitives into a whole schoolbook column

`fe25519_mac_column_reconstruct` (§3) is the value law of **one** product's
`MULX`+`ADCX`/`ADOX` accumulate step, threading a 128-bit `(lo, hi)` accumulator
through `a·b`. A schoolbook column is a *chain* of five such steps (its five
19-folded limb products), and the deployed ADX `fe25519_mul` runs exactly this
chain per column. This section composes the emitted primitives over an arbitrary
product list and proves the running 128-bit accumulator reconstructs the exact
integer column sum — the per-column re-tie a whole array-returning `fe25519MulCom`'s
`denote = feCarryNat` folds together (each `feMulRₖ` is one such fold). The step is
`fe25519_mac_column_reconstruct` (unchanged); the composition is by induction. -/

/-- One multiply-accumulate step over the emitted golden-path primitives: thread the
    128-bit accumulator `(lo, hi)` through the product `a·b`. The new low word is the
    emitted `fieldAddCom (a·b, lo)`, the new high word the emitted
    `fieldAdcCom (hi, mulHiW a b, carry)` with `carry = fieldAddCarryCom (a·b, lo)` — the
    same three sub-computations `fe25519_mac_column_reconstruct` reassembles. -/
def macStep (lo hi a b : BitVec 64) : BitVec 64 × BitVec 64 :=
  (Com.denote fieldAddCom (.cons (a * b) (.cons lo .nil)),
   Com.denote fieldAdcCom
     (.cons hi (.cons (mulHiW a b)
       (.cons (Com.denote fieldAddCarryCom (.cons (a * b) (.cons lo .nil))) .nil))))

/-- Fold the MAC step over a list of product operands, accumulating the whole column
    into a single 128-bit `(lo, hi)` running accumulator — the `MULX`/`ADCX`/`ADOX`
    column chain, expressed over the emitted primitives. -/
def macFold : List (BitVec 64 × BitVec 64) → BitVec 64 × BitVec 64 → BitVec 64 × BitVec 64
  | [], acc => acc
  | (a, b) :: ps, (lo, hi) => macFold ps (macStep lo hi a b)

/-- The per-step no-high-overflow headroom for the whole fold: the radix-2⁵¹ invariant
    that the running high word never wraps within a column (the fe25519 five-column
    accumulator has enough headroom). Carried as a hypothesis, exactly as
    `fe25519_mac_column_reconstruct` carries `hhead` and `fe25519_mul_deployed_congr`
    carries the output limb bound `hlt`. -/
def macFoldHeadroom : List (BitVec 64 × BitVec 64) → BitVec 64 × BitVec 64 → Prop
  | [], _ => True
  | (a, b) :: ps, (lo, hi) =>
      (hi.toNat + (Com.denote fieldAddCarryCom (.cons (a * b) (.cons lo .nil))).toNat
        + (mulHiW a b).toNat < 2 ^ 64)
      ∧ macFoldHeadroom ps (macStep lo hi a b)

/-- **The multi-product column-accumulate value law.** Folding the emitted
    `fieldAddCom`/`fieldAddCarryCom`/`fieldAdcCom` MAC primitives over a list of products,
    the resulting 128-bit accumulator reconstructs the exact integer sum `Σ aₖ·bₖ` added
    onto the starting accumulator — the whole schoolbook column threaded through the
    deployed `MULX`/`ADCX`/`ADOX` (lo, hi) chain. Proved by induction from the
    single-product `fe25519_mac_column_reconstruct`. This is the per-column re-tie the
    array-returning `fe25519MulCom`'s `denote = feCarryNat` composes (each `feMulRₖ` is one
    such fold over its five 19-folded products; the carry reduction then reduces the five
    columns — the reported residual). -/
theorem macFold_reconstruct (ps : List (BitVec 64 × BitVec 64)) :
    ∀ acc : BitVec 64 × BitVec 64, macFoldHeadroom ps acc →
      (macFold ps acc).1.toNat + (macFold ps acc).2.toNat * 2 ^ 64
        = acc.1.toNat + acc.2.toNat * 2 ^ 64
          + (ps.map (fun p => p.1.toNat * p.2.toNat)).sum := by
  induction ps with
  | nil => intro acc _; simp [macFold]
  | cons p ps ih =>
      intro acc h
      obtain ⟨a, b⟩ := p
      obtain ⟨lo, hi⟩ := acc
      simp only [macFoldHeadroom] at h
      obtain ⟨hstep, hrest⟩ := h
      have step := fe25519_mac_column_reconstruct lo hi a b hstep
      simp only [macFold]
      rw [ih (macStep lo hi a b) hrest]
      simp only [macStep, List.map_cons, List.sum_cons]
      omega

/-! ## 4b. A concrete column: the emitted primitives reconstruct `feMulR0`

Instantiating the general fold on column 0's five 19-folded products ties the composed
emitted primitives to the exact Nat column accumulator `feMulR0` (§1). The `19·aⱼ`
prescale is a `BitVec` multiply `(19 : BitVec 64) · aⱼ`; under the radix-2⁵¹ limb bound
it does not wrap, so its `.toNat` is `19·(aⱼ).toNat` (`mul19_toNat`). This is one column
of the five the full `fe25519MulCom` would assemble. -/

/-- The `19·aⱼ` prescale does not wrap under the radix-2⁵¹ limb headroom (`x < 2⁵⁹`, so
    `19·x < 2⁶⁴`): its word value is the exact `19·x`. -/
theorem mul19_toNat (x : BitVec 64) (hx : x.toNat < 2 ^ 59) :
    ((19 : BitVec 64) * x).toNat = 19 * x.toNat := by
  rw [BitVec.toNat_mul]
  have h19 : (19 : BitVec 64).toNat = 19 := by decide
  rw [h19]
  exact Nat.mod_eq_of_lt (by omega)

/-- Column 0's five schoolbook products, with the `19·aⱼ` fold prescaled into the operand
    (the deployed `MULX` reads `19·a₄` etc.): `a₀·b₀`, `(19·a₄)·b₁`, `(19·a₃)·b₂`,
    `(19·a₂)·b₃`, `(19·a₁)·b₄`. -/
def col0Products (a b : Fe51) : List (BitVec 64 × BitVec 64) :=
  [(a 0, b 0), ((19 : BitVec 64) * a 4, b 1), ((19 : BitVec 64) * a 3, b 2),
   ((19 : BitVec 64) * a 2, b 3), ((19 : BitVec 64) * a 1, b 4)]

/-- **A whole schoolbook column, front-composed, reconstructs its Nat accumulator.**
    Folding the emitted MAC primitives over column 0's five (19-folded) products from a
    zero accumulator reconstructs exactly `feMulR0 a b` (§1) — the deployed
    `MULX`/`ADCX`/`ADOX` column chain's value law, on the golden-path primitives, tied to
    the radix-2⁵¹ reduction algebra. Under the per-step headroom and the radix-2⁵¹ limb
    bound (`< 2⁵⁹`, so the `19·aⱼ` prescale does not wrap). The other four columns are the
    same fold on `feMulR1..feMulR4`'s products; the carry reduction over the five columns
    (`feCarryNat`) is the reported residual. -/
theorem col0_reconstruct (a b : Fe51)
    (hhead : macFoldHeadroom (col0Products a b) (0, 0))
    (hb1 : (a 1).toNat < 2 ^ 59) (hb2 : (a 2).toNat < 2 ^ 59)
    (hb3 : (a 3).toNat < 2 ^ 59) (hb4 : (a 4).toNat < 2 ^ 59) :
    (macFold (col0Products a b) (0, 0)).1.toNat
        + (macFold (col0Products a b) (0, 0)).2.toNat * 2 ^ 64
      = feMulR0 a b := by
  have h := macFold_reconstruct (col0Products a b) (0, 0) hhead
  simp only [col0Products] at h ⊢
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [mul19_toNat _ hb4, mul19_toNat _ hb3, mul19_toNat _ hb2, mul19_toNat _ hb1] at h
  rw [h]
  have hz : BitVec.toNat (0 : BitVec 64) = 0 := by decide
  simp only [hz, feMulR0, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
  ring

/-! ## 4c. The other four schoolbook columns, front-composed from the emitted primitives

`col1Products … col4Products` are the remaining four columns' five (19-folded) products,
`col1_reconstruct … col4_reconstruct` their value laws — each the same `macFold` of the
emitted MAC primitives reconstructing the exact Nat accumulator `feMulR1 … feMulR4` (§1),
by the identical proof shape as `col0_reconstruct`. Together with §4b these are the five
columns the full `fe25519MulCom` runs before the carry reduction. -/

/-- Column 1's five schoolbook products: `a₀·b₁`, `a₁·b₀`, `(19·a₄)·b₂`, `(19·a₃)·b₃`,
    `(19·a₂)·b₄`. -/
def col1Products (a b : Fe51) : List (BitVec 64 × BitVec 64) :=
  [(a 0, b 1), (a 1, b 0), ((19 : BitVec 64) * a 4, b 2), ((19 : BitVec 64) * a 3, b 3),
   ((19 : BitVec 64) * a 2, b 4)]

/-- Column 2's five schoolbook products: `a₀·b₂`, `a₁·b₁`, `a₂·b₀`, `(19·a₄)·b₃`,
    `(19·a₃)·b₄`. -/
def col2Products (a b : Fe51) : List (BitVec 64 × BitVec 64) :=
  [(a 0, b 2), (a 1, b 1), (a 2, b 0), ((19 : BitVec 64) * a 4, b 3),
   ((19 : BitVec 64) * a 3, b 4)]

/-- Column 3's five schoolbook products: `a₀·b₃`, `a₁·b₂`, `a₂·b₁`, `a₃·b₀`, `(19·a₄)·b₄`. -/
def col3Products (a b : Fe51) : List (BitVec 64 × BitVec 64) :=
  [(a 0, b 3), (a 1, b 2), (a 2, b 1), (a 3, b 0), ((19 : BitVec 64) * a 4, b 4)]

/-- Column 4's five schoolbook products: `a₀·b₄`, `a₁·b₃`, `a₂·b₂`, `a₃·b₁`, `a₄·b₀`
    (no `19`-fold — the direct diagonal). -/
def col4Products (a b : Fe51) : List (BitVec 64 × BitVec 64) :=
  [(a 0, b 4), (a 1, b 3), (a 2, b 2), (a 3, b 1), (a 4, b 0)]

/-- Column 1 reconstructs `feMulR1` (three `19`-prescaled operands: `a₄`, `a₃`, `a₂`). -/
theorem col1_reconstruct (a b : Fe51)
    (hhead : macFoldHeadroom (col1Products a b) (0, 0))
    (hb2 : (a 2).toNat < 2 ^ 59) (hb3 : (a 3).toNat < 2 ^ 59)
    (hb4 : (a 4).toNat < 2 ^ 59) :
    (macFold (col1Products a b) (0, 0)).1.toNat
        + (macFold (col1Products a b) (0, 0)).2.toNat * 2 ^ 64
      = feMulR1 a b := by
  have h := macFold_reconstruct (col1Products a b) (0, 0) hhead
  simp only [col1Products] at h ⊢
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [mul19_toNat _ hb4, mul19_toNat _ hb3, mul19_toNat _ hb2] at h
  rw [h]
  have hz : BitVec.toNat (0 : BitVec 64) = 0 := by decide
  simp only [hz, feMulR1, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
  ring

/-- Column 2 reconstructs `feMulR2` (two `19`-prescaled operands: `a₄`, `a₃`). -/
theorem col2_reconstruct (a b : Fe51)
    (hhead : macFoldHeadroom (col2Products a b) (0, 0))
    (hb3 : (a 3).toNat < 2 ^ 59) (hb4 : (a 4).toNat < 2 ^ 59) :
    (macFold (col2Products a b) (0, 0)).1.toNat
        + (macFold (col2Products a b) (0, 0)).2.toNat * 2 ^ 64
      = feMulR2 a b := by
  have h := macFold_reconstruct (col2Products a b) (0, 0) hhead
  simp only [col2Products] at h ⊢
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [mul19_toNat _ hb4, mul19_toNat _ hb3] at h
  rw [h]
  have hz : BitVec.toNat (0 : BitVec 64) = 0 := by decide
  simp only [hz, feMulR2, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
  ring

/-- Column 3 reconstructs `feMulR3` (one `19`-prescaled operand: `a₄`). -/
theorem col3_reconstruct (a b : Fe51)
    (hhead : macFoldHeadroom (col3Products a b) (0, 0))
    (hb4 : (a 4).toNat < 2 ^ 59) :
    (macFold (col3Products a b) (0, 0)).1.toNat
        + (macFold (col3Products a b) (0, 0)).2.toNat * 2 ^ 64
      = feMulR3 a b := by
  have h := macFold_reconstruct (col3Products a b) (0, 0) hhead
  simp only [col3Products] at h ⊢
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [mul19_toNat _ hb4] at h
  rw [h]
  have hz : BitVec.toNat (0 : BitVec 64) = 0 := by decide
  simp only [hz, feMulR3, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
  ring

/-- Column 4 reconstructs `feMulR4` (the direct diagonal — no `19`-fold). -/
theorem col4_reconstruct (a b : Fe51)
    (hhead : macFoldHeadroom (col4Products a b) (0, 0)) :
    (macFold (col4Products a b) (0, 0)).1.toNat
        + (macFold (col4Products a b) (0, 0)).2.toNat * 2 ^ 64
      = feMulR4 a b := by
  have h := macFold_reconstruct (col4Products a b) (0, 0) hhead
  simp only [col4Products] at h ⊢
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [h]
  have hz : BitVec.toNat (0 : BitVec 64) = 0 := by decide
  simp only [hz, feMulR4, Nat.zero_mul, Nat.zero_add, Nat.add_zero]
  ring

/-! ## 5. The array-assembly writeback: five reduced limbs → one `stackArr 64 5`

The reduction algebra (§1/§1b) and the per-column composition (§4) produce the five
reduced Nat limbs `feCarryLimbNat a b 0..4` — the deployed `fe25519_mul` output words.
This section supplies the **front-generated array assembly** that writes those five words
into one `stackArr 64 5` product value and **returns the array**, exactly as
`CompileFromHaxSha256CompressProductTie.packCom` returns the 8-word SHA-256 state: a
`stackStore`-chain built by a generator (`mulPackTail`), *not* a hand-authored de Bruijn
literal, with its `denote` proved by induction from the single-`stackStore` step.

Instantiating the assembly with the five reduced limbs `feCarryNat a b` yields an
array-returning `Com` whose `denote` is exactly `feCarryNat a b` — the deployed 5-limb
`fe25519_mul` output as one product value — and the full multiply-mod-`p` correctness
(`fe25519_mul_deployed_congr`) then transfers to the array leaf for free.

**Residual (reported):** the whole `[stackArr 64 5, stackArr 64 5] → stackArr 64 5` kernel
with the schoolbook + carry *arithmetic inline* (loading `a`/`b`, running the five column
`macFold`s, the canonical carry reduction as `Com` ops — `shrImm 51` / mask / `shlImm 13` /
`||| ` on the 128-bit `(lo, hi)` accumulators / the `c₄·19` fold) as the front prefix of
this assembly. That front prefix needs the word-level carry-extraction lemmas
`(lo + hi·2⁶⁴) >>> 51 = (lo >>> 51) ||| (hi <<< 13)` (under the radix-2⁵¹ high-word bound
`hi < 2⁴⁴`) and `(lo + hi·2⁶⁴) &&& (2⁵¹−1) = lo &&& (2⁵¹−1)`, per column — the reported
gap. The assembly + the product value + the correctness re-tie are what this section lands. -/

/-- The assembly context: an out-buffer scratch array (`stackArr 64 5`, the ABI return
    slot, overwritten in full) followed by the five reduced `reg 64` limbs. -/
abbrev mulPackCtxt : Ctxt jasminDialect := .stackArr 64 5 :: List.replicate 5 (.reg 64)

/-- The scratch out-array variable (de Bruijn 0 of `mulPackCtxt`). -/
def mulPackArrVar : Ctxt.Var mulPackCtxt (.stackArr 64 5) := .here

/-- The de Bruijn variable for reduced limb `i < 5` (the `i`-th `reg 64`, shifted under
    the leading scratch array). -/
def mulPackWordVar : (i : Fin 5) → Ctxt.Var mulPackCtxt (.reg 64)
  | 0 => .there .here
  | 1 => .there (.there .here)
  | 2 => .there (.there (.there .here))
  | 3 => .there (.there (.there (.there .here)))
  | 4 => .there (.there (.there (.there (.there .here))))

/-- The canonical `mulPackCtxt` valuation from a scratch array `s0` and five limbs. -/
def mulPackVal (s0 : Fin 5 → BitVec 64) (words : Fin 5 → BitVec 64) :
    Ctxt.Valuation mulPackCtxt :=
  .cons s0 (.cons (words 0) (.cons (words 1) (.cons (words 2)
    (.cons (words 3) (.cons (words 4) .nil)))))

/-- The index-const `Expr` (`regConst 64 i`) — the `stackStore` slot index. -/
def mkIdxConst64 (i : Nat) {Γ : Ctxt jasminDialect} : Expr jasminDialect Γ (.reg 64) :=
  { op := .regConst 64 i, retTy_eq := rfl, args := .nil }

/-- One slot's store `Expr` over context `Γ` with the array var `va`, index var `vi`,
    value var `vv` (`[stackArr 64 5, reg 64, reg 64] → stackArr 64 5`). -/
def mkStore64 {Γ : Ctxt jasminDialect}
    (va : Ctxt.Var Γ (.stackArr 64 5)) (vi : Ctxt.Var Γ (.reg 64))
    (vv : Ctxt.Var Γ (.reg 64)) : Expr jasminDialect Γ (.stackArr 64 5) :=
  { op := .stackStore 64 5, retTy_eq := rfl,
    args := .cons va (.cons vi (.cons vv .nil)) }

/-- **The store-chain generator.** Over a context `Γ = stackArr 64 5 :: rest` with the
    array at de Bruijn 0 (`av`) and a resolver `getW : Fin 5 → Var Γ (reg 64)`,
    `mulPackTail fuel start` writes `arr[start + j] := getW (start+j)` for `j < fuel`, then
    `ret`s the array. Each step binds a `regConst 64 start` index and a `stackStore`,
    growing the context by `reg 64 :: stackArr 64 5 ::`; the resolver and array-var are
    shifted under the two fresh bindings. Assembled by the generator, not hand-authored. -/
def mulPackTail {rest : Ctxt jasminDialect}
    (getW : Fin 5 → Ctxt.Var (JasminTy.stackArr 64 5 :: rest) (JasminTy.reg 64))
    (av : Ctxt.Var (JasminTy.stackArr 64 5 :: rest) (JasminTy.stackArr 64 5)) :
    (fuel start : Nat) →
    Com jasminDialect (JasminTy.stackArr 64 5 :: rest) (JasminTy.stackArr 64 5)
  | 0, _ => .ret av
  | fuel + 1, start =>
      .var (mkIdxConst64 start)
        (.var (mkStore64 av.there .here
                ((getW ⟨start % 5, Nat.mod_lt _ (by omega)⟩).there))
          (mulPackTail
            (rest := JasminTy.reg 64 :: JasminTy.stackArr 64 5 :: rest)
            (fun j => (getW j).there.there) .here fuel (start + 1)))

/-- The array a store-chain over slots `start .. start+fuel-1` produces from a base array
    `base`, reading limb values from `wval : Fin 5 → BitVec 64`. -/
def mulPackFold (wval : Fin 5 → BitVec 64) (base : Fin 5 → BitVec 64) :
    (fuel start : Nat) → (Fin 5 → BitVec 64)
  | 0, _ => base
  | fuel + 1, start =>
      mulPackFold wval (stackSet base start (wval ⟨start % 5, Nat.mod_lt _ (by omega)⟩))
        fuel (start + 1)

/-- One `mkStore64` step's denotation is the functional update `stackSet` at the index
    var's `.toNat`. Pure unfolding (`rfl`). -/
theorem mkStore64_denote {rest : Ctxt jasminDialect}
    (V : Ctxt.Valuation (JasminTy.reg 64 :: JasminTy.stackArr 64 5 :: rest))
    (av : Ctxt.Var (JasminTy.stackArr 64 5 :: rest) (.stackArr 64 5))
    (wv : Ctxt.Var (JasminTy.stackArr 64 5 :: rest) (.reg 64)) :
    (mkStore64 av.there Ctxt.Var.here wv.there).denote V
      = stackSet (av.there.lookup V)
          ((Ctxt.Var.here (Γ := JasminTy.stackArr 64 5 :: rest)
              (t := JasminTy.reg 64)).lookup V).toNat (wv.there.lookup V) := rfl

/-- `(BitVec.ofNat 64 start).toNat = start` for the small slot indices `< 5`. -/
theorem ofNat64_toNat_of_lt5 (start : Nat) (h : start < 5) :
    (BitVec.ofNat 64 start).toNat = start := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : start < 2 ^ 64)]

/-- **`mulPackTail` denotes to the store-fold `mulPackFold`.** Reducing the recursion one
    binding-pair at a time: the `start`-slot store is a `stackSet` at index `start`
    (`mkStore64_denote` + `ofNat64_toNat_of_lt5`), and the two fresh bindings drop out of
    every limb/array lookup. Induction on `fuel`, with `start + fuel ≤ 5`. -/
theorem mulPackTail_denote {rest : Ctxt jasminDialect}
    (getW : Fin 5 → Ctxt.Var (JasminTy.stackArr 64 5 :: rest) (.reg 64))
    (av : Ctxt.Var (JasminTy.stackArr 64 5 :: rest) (.stackArr 64 5)) :
    (fuel start : Nat) → (hb : start + fuel ≤ 5) →
    (V : Ctxt.Valuation (JasminTy.stackArr 64 5 :: rest)) →
    (mulPackTail getW av fuel start).denote V
      = mulPackFold (fun j => (getW j).lookup V) (av.lookup V) fuel start
  | 0, _, _, _ => rfl
  | fuel + 1, start, hb, V => by
      have hlt : start < 5 := by omega
      show (Com.denote
        (.var (mkIdxConst64 start)
          (.var (mkStore64 av.there Ctxt.Var.here
                  ((getW ⟨start % 5, Nat.mod_lt _ (by omega)⟩).there))
            (mulPackTail (fun j => (getW j).there.there) Ctxt.Var.here fuel (start + 1)))) V)
        = _
      rw [Com.denote_var]
      set V1 : Ctxt.Valuation (JasminTy.reg 64 :: JasminTy.stackArr 64 5 :: rest) :=
        V.extend ((mkIdxConst64 (Γ := JasminTy.stackArr 64 5 :: rest) start).denote V) with hV1
      rw [Com.denote_var, mkStore64_denote]
      have hidx : (Ctxt.Var.here (Γ := JasminTy.stackArr 64 5 :: rest)
          (t := JasminTy.reg 64)).lookup V1 = BitVec.ofNat 64 start := rfl
      rw [hidx, ofNat64_toNat_of_lt5 start hlt]
      rw [mulPackTail_denote (fun j => ((getW j).there.there)) Ctxt.Var.here fuel (start + 1)
        (by omega)]
      conv_rhs => rw [mulPackFold]
      rfl

/-- The full 5-slot store-fold from any base array writes every slot, yielding the limb
    vector `wval` exactly (the base is fully overwritten). -/
theorem mulPackFold_full (wval base : Fin 5 → BitVec 64) :
    mulPackFold wval base 5 0 = wval := by
  funext i
  fin_cases i <;>
    · simp only [mulPackFold, stackSet]
      norm_num [Fin.ext_iff]

/-- **The array-assembly `Com`.** A single `Com jasminDialect mulPackCtxt (stackArr 64 5)`
    that writes the five reduced limbs into one array and **returns the array** — the whole
    `fe25519_mul` output as one product value. The return type is the existing `stackArr`
    `Ty`; no `Com`-core change. Front-generated by `mulPackTail`, not hand-authored. -/
def fe25519MulProductCom : Com jasminDialect mulPackCtxt (.stackArr 64 5) :=
  mulPackTail mulPackWordVar mulPackArrVar 5 0

/-- **The assembly `Com` denotes to the five reduced limbs.** For any scratch array `s0`
    and five words, `fe25519MulProductCom` returns the array `fun i => words i` — the full
    5-limb result assembled into one `stackArr 64 5` value (the scratch `s0` is fully
    overwritten). One `Com` carrying all five limbs: the product output. -/
theorem fe25519MulProductCom_denote (s0 : Fin 5 → BitVec 64) (words : Fin 5 → BitVec 64) :
    fe25519MulProductCom.denote (mulPackVal s0 words) = words := by
  have h := mulPackTail_denote mulPackWordVar mulPackArrVar 5 0 (by omega) (mulPackVal s0 words)
  rw [fe25519MulProductCom, h]
  have hw : (fun j => (mulPackWordVar j).lookup (mulPackVal s0 words)) = words := by
    funext j; fin_cases j <;> rfl
  have hb : mulPackArrVar.lookup (mulPackVal s0 words) = s0 := rfl
  rw [hw, hb, mulPackFold_full]

/-! ## 5b. The deployed `fe25519_mul` output as one product `Com`, and its correctness

Feeding the five reduced limbs `feCarryNat a b` (the deployed 5-limb `fe25519_mul` output,
§1b) to the assembly, the single product-output `Com` denotes to the whole deployed result
`feCarryNat a b` as one `stackArr 64 5` value — and the full multiply-mod-`p` correctness
(`fe25519_mul_deployed_congr`) transfers to this array leaf verbatim. -/

/-- **The product-output `fe25519_mul` array `Com`.** With the reduced limbs `feCarryNat a b`
    supplied to the assembly, the single `Com … (stackArr 64 5)` denotes to the whole
    deployed 5-limb result `feCarryNat a b` — the deployed HACL\*/ADX `fmul` output as one
    product value (`fe25519MulProductCom_denote`). -/
theorem fe25519MulProductCom_feCarryNat (s0 : Fin 5 → BitVec 64) (a b : Fe51) :
    fe25519MulProductCom.denote (mulPackVal s0 (feCarryNat a b)) = feCarryNat a b :=
  fe25519MulProductCom_denote s0 (feCarryNat a b)

/-- **The full multiply-mod-`p` correctness on the array leaf.** The reconstructed integer
    of the product-output array `Com` (denoting the deployed 5-limb `feCarryNat a b`) is
    congruent to the exact integer product `feToNat51 a · feToNat51 b` mod `p = 2²⁵⁵−19`,
    under the radix-2⁵¹ output-limb bound `hlt`. The array assembly returns the deployed
    result (`fe25519MulProductCom_feCarryNat`); the deployed-result correctness
    (`fe25519_mul_deployed_congr`) then closes it — schoolbook columns + `2²⁵⁵ ≡ 19` fold +
    canonical carry reduction + array writeback, the complete field-multiply leaf. -/
theorem fe25519_mul_leaf_congr (s0 : Fin 5 → BitVec 64) (a b : Fe51)
    (hlt : ∀ i : Fin 5, feCarryLimbNat a b i < 2 ^ 64) :
    (feToNat51 (fe25519MulProductCom.denote (mulPackVal s0 (feCarryNat a b))) : ℤ)
      ≡ (feToNat51 a : ℤ) * feToNat51 b [ZMOD ((2 : ℤ) ^ 255 - 19)] := by
  rw [fe25519MulProductCom_feCarryNat]
  exact fe25519_mul_deployed_congr a b hlt

/-! ## 6. The word-level carry-extraction lemmas (the reported residual, closed)

The canonical carry reduction `feCarryLimbNat` (§1b) is Nat arithmetic (`/ 2⁵¹`, `% 2⁵¹`)
on the wide column accumulators `Rₖ`, each realised as a 128-bit `(lo, hi)` word pair with
`lo.toNat + hi.toNat · 2⁶⁴ = Rₖ` (the `macFold` reconstruction, §4). To run that reduction
as `Com` ops on the `(lo, hi)` pair, the deployed HACL\*/ADX shape extracts the carry
`⌊v / 2⁵¹⌋` and the limb `v mod 2⁵¹` of the 128-bit value `v = lo + hi·2⁶⁴` with the
word ops `shrImm 51` / `shlImm 13` / `|||` (carry) and `&&& (2⁵¹−1)` (limb). These two
lemmas are the word-level ⇄ Nat bridge that closes the reported residual:

* **carry** `(lo >>> 51) ||| (hi <<< 13)` realises `⌊v / 2⁵¹⌋` as a word (under the
  radix-2⁵¹ high-word bound `hi < 2⁴⁴`, which the fe25519 five-column accumulator meets),
* **limb** `lo &&& (2⁵¹−1)` realises `v mod 2⁵¹` (the high half contributes multiples of
  `2⁶⁴`, a multiple of `2⁵¹`, so only `lo` matters).

The `2⁶⁴ = 2¹³·2⁵¹` identity is the whole content — the carry combines the top 13 bits of
`lo` (`lo >>> 51`, disjoint low bits) with `hi` shifted up 13 (`hi <<< 13`), and OR = ADD
on those disjoint bit ranges (`bv_decide`, 64-bit, no hypothesis). -/

/-- The mask `2⁵¹ − 1` as a `BitVec 64` (the `AND` immediate for the limb extraction). -/
def mask51 : BitVec 64 := BitVec.ofNat 64 (2 ^ 51 - 1)

/-- The carry-extraction `OR` across the 128-bit `(lo, hi)` boundary is a disjoint-bit
    `ADD`: `lo >>> 51` occupies bits `0..12` and `hi <<< 13` has its low 13 bits zero, so
    the two never share a bit — `bv_decide`, 64-bit, no hypothesis. -/
theorem carryWord_or_eq_add (lo hi : BitVec 64) :
    (lo >>> (51 : Nat)) ||| (hi <<< (13 : Nat))
      = (lo >>> (51 : Nat)) + (hi <<< (13 : Nat)) := by
  bv_decide

/-- **The carry-extraction lemma.** `(lo >>> 51) ||| (hi <<< 13)` realises the 128-bit
    carry `⌊(lo + hi·2⁶⁴) / 2⁵¹⌋` as a word, under the radix-2⁵¹ high-word bound
    `hi < 2⁵¹`. The `2⁶⁴ = 2¹³·2⁵¹` split makes `(lo + hi·2⁶⁴)/2⁵¹ = lo/2⁵¹ + hi·2¹³`, and
    the `OR` of the disjoint pieces is that sum (no word wrap, since `hi < 2⁵¹ ⇒
    hi·2¹³ < 2⁶⁴`; the top-bit sum `lo>>>51 + hi·2¹³ ≤ 2¹³−1 + 2⁶⁴−2¹³ < 2⁶⁴` still fits).
    This is the `shrImm 51`/`shlImm 13`/`|||` carry op the front prefix runs on the
    `(lo, hi)` column accumulator. The `hi < 2⁵¹` headroom covers column 0's reconstructed
    high word (`< 2⁴⁶`). -/
theorem carryWord_toNat (lo hi : BitVec 64) (hhi : hi.toNat < 2 ^ 51) :
    ((lo >>> (51 : Nat)) ||| (hi <<< (13 : Nat))).toNat
      = (lo.toNat + hi.toNat * 2 ^ 64) / 2 ^ 51 := by
  rw [carryWord_or_eq_add, BitVec.toNat_add, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft]
  have hlo : lo.toNat < 2 ^ 64 := lo.isLt
  simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

/-- **The limb-extraction lemma.** `lo &&& (2⁵¹−1)` realises the 128-bit residue
    `(lo + hi·2⁶⁴) mod 2⁵¹`: masking the low 51 bits of `lo` gives `lo mod 2⁵¹`, and the
    high half `hi·2⁶⁴` is a multiple of `2⁵¹` (`2⁶⁴ = 2¹³·2⁵¹`), so it drops out of the
    residue. This is the `&&& mask51` limb op the front prefix runs on the `(lo, hi)`
    column accumulator. -/
theorem limbWord_toNat (lo hi : BitVec 64) :
    (lo &&& mask51).toNat = (lo.toNat + hi.toNat * 2 ^ 64) % 2 ^ 51 := by
  have hbv : lo &&& mask51 = lo % BitVec.ofNat 64 (2 ^ 51) := by
    unfold mask51; bv_decide
  rw [hbv, BitVec.toNat_umod]
  have hm : (BitVec.ofNat 64 (2 ^ 51)).toNat = 2 ^ 51 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num)]
  rw [hm]
  omega

/-! ### 6b. The atomic carry+limb extraction op on a `(lo, hi)` column accumulator

Packaging the two lemmas into the single word-level unit the front prefix's carry chain
runs per column: `wordExtract lo hi = (limb, carry)` with the two `shrImm`/`shlImm`/`|||`
and `&&& mask51` ops. `wordExtract_limb` / `wordExtract_carry` give its two components'
`.toNat` as the exact Nat `% 2⁵¹` / `/ 2⁵¹` of the reconstructed 128-bit accumulator —
the `feCarryLimbNat` (§1b) primitives, on words. This is the reduction op the residual
front prefix threads across the five column accumulators (each an `(lo, hi)` reconstructed
by `macFold_reconstruct` to `feMulRₖ`). -/

/-- **The atomic word carry+limb extraction** of a 128-bit `(lo, hi)` accumulator:
    `limb := lo &&& mask51` (the `AND` low-51-bits op) and
    `carry := (lo >>> 51) ||| (hi <<< 13)` (the `shrImm 51`/`shlImm 13`/`|||` op across
    the word boundary) — the deployed HACL\*/ADX `carry_wide` word shape. -/
def wordExtract (lo hi : BitVec 64) : BitVec 64 × BitVec 64 :=
  (lo &&& mask51, (lo >>> (51 : Nat)) ||| (hi <<< (13 : Nat)))

/-- The extracted limb is the exact 128-bit residue `(lo + hi·2⁶⁴) mod 2⁵¹`
    (`limbWord_toNat`). -/
theorem wordExtract_limb (lo hi : BitVec 64) :
    (wordExtract lo hi).1.toNat = (lo.toNat + hi.toNat * 2 ^ 64) % 2 ^ 51 :=
  limbWord_toNat lo hi

/-- The extracted carry is the exact 128-bit quotient `⌊(lo + hi·2⁶⁴) / 2⁵¹⌋`, under the
    radix-2⁵¹ high-word bound `hi < 2⁵¹` (`carryWord_toNat`). -/
theorem wordExtract_carry (lo hi : BitVec 64) (hhi : hi.toNat < 2 ^ 51) :
    (wordExtract lo hi).2.toNat = (lo.toNat + hi.toNat * 2 ^ 64) / 2 ^ 51 :=
  carryWord_toNat lo hi hhi

/-- **The extraction reconstructs the split.** `limb + carry·2⁵¹ = v` for the reconstructed
    128-bit accumulator value `v = lo + hi·2⁶⁴` (under the high-word bound) — the carry/limb
    the deployed reduction propagates satisfy the radix-2⁵¹ digit identity, so folding this
    op across the five columns reproduces the `feCarryLimbNat` chain exactly. -/
theorem wordExtract_reconstruct (lo hi : BitVec 64) (hhi : hi.toNat < 2 ^ 51) :
    (wordExtract lo hi).1.toNat + (wordExtract lo hi).2.toNat * 2 ^ 51
      = lo.toNat + hi.toNat * 2 ^ 64 := by
  rw [wordExtract_limb, wordExtract_carry lo hi hhi]
  omega

/-! ### 6c. The forward carry-add step reuses the MAC unit (no new op)

The `feCarryLimbNat` chain (§1b) threads each extracted carry `cₖ` into the next column:
`tₖ₊₁ = Rₖ₊₁ + cₖ`. On words this is a widening add of the single carry word `c` into the
next column's `(lo, hi)` accumulator — which is exactly a `macStep` with the trivial
product `(c, 1)` (`c·1 = c`, `mulHiW c 1 = 0`). So the whole reduction is expressible over
the already-emitted MAC primitives plus §6/§6b's extract op: the forward carry-add needs no
new op, and its value law is the single-product `fe25519_mac_column_reconstruct`. -/

/-- The forward carry-add: add the carry word `c` into the running `(lo, hi)` accumulator,
    as the trivial-product `macStep lo hi c 1` (`c·1 = c`) — the deployed `ADD`/`ADC` carry
    fold, over the emitted primitives, no new op. -/
def carryAddStep (lo hi c : BitVec 64) : BitVec 64 × BitVec 64 := macStep lo hi c 1

/-- **The forward carry-add value law.** `carryAddStep lo hi c` reconstructs
    `(lo + hi·2⁶⁴) + c` exactly — the `tₖ₊₁ = Rₖ₊₁ + cₖ` step of the carry chain, as a
    corollary of the single-product MAC value law `fe25519_mac_column_reconstruct` (the
    trivial product `c·1`). Under the same radix-2⁵¹ no-high-overflow headroom. -/
theorem carryAddStep_reconstruct (lo hi c : BitVec 64)
    (hhead : hi.toNat
        + (Com.denote fieldAddCarryCom (.cons (c * 1) (.cons lo .nil))).toNat
        + (mulHiW c 1).toNat < 2 ^ 64) :
    (carryAddStep lo hi c).1.toNat + (carryAddStep lo hi c).2.toNat * 2 ^ 64
      = lo.toNat + hi.toNat * 2 ^ 64 + c.toNat := by
  have h := fe25519_mac_column_reconstruct lo hi c 1 hhead
  have h1 : (1 : BitVec 64).toNat = 1 := by decide
  simpa only [carryAddStep, macStep, h1, Nat.mul_one] using h

/-! ### 6d. One carry-reduction step: fold a column, add the incoming carry, extract

`colReduce col cin` is the atomic carry-chain step the deployed reduction iterates over the
five columns: fold the column's products into a 128-bit `(lo, hi)` accumulator (`macFold`),
add the incoming carry `cin` (`carryAddStep`, §6c), then split off the radix-2⁵¹ limb and
outgoing carry (`wordExtract`, §6b). Its value law `colReduce_reconstruct` — the reconstructed
column value plus the incoming carry, split into `limb + carry·2⁵¹` — is exactly the
`tₖ = Rₖ + cₖ₋₁`, `cₖ = tₖ / 2⁵¹`, `limbₖ = tₖ % 2⁵¹` step of `feCarryLimbNat` (§1b), on words.
Composing this over the five columns (with the `c₄·19` top fold) is the carry reduction of the
assembled kernel; `colReduce_limb` / `colReduce_carry` give the two components as the exact Nat
`% 2⁵¹` / `/ 2⁵¹` the chain threads. -/

/-- **One carry-reduction step.** Fold a column into its 128-bit accumulator, add the
    incoming carry word, and extract `(limb, carry-out)` — the deployed `carry_wide` step. -/
def colReduce (col : List (BitVec 64 × BitVec 64)) (cin : BitVec 64) : BitVec 64 × BitVec 64 :=
  let acc := macFold col (0, 0)
  let acc' := carryAddStep acc.1 acc.2 cin
  wordExtract acc'.1 acc'.2

/-- **The carry-reduction step value law.** For a column reconstructing to `V`
    (`hV`, from `col0_reconstruct … col4_reconstruct`), adding the incoming carry `cin` and
    extracting gives `limb + carry·2⁵¹ = V + cin` — the radix-2⁵¹ digit identity of the
    `tₖ = Rₖ + cₖ₋₁` step. Under the `carryAddStep` no-high-overflow headroom `hhead` and the
    post-add high-word bound `hhi < 2⁵¹` (`wordExtract_carry`). -/
theorem colReduce_reconstruct (col : List (BitVec 64 × BitVec 64)) (cin : BitVec 64) (V : Nat)
    (hV : (macFold col (0, 0)).1.toNat + (macFold col (0, 0)).2.toNat * 2 ^ 64 = V)
    (hhead : (macFold col (0, 0)).2.toNat
        + (Com.denote fieldAddCarryCom
            (.cons (cin * 1) (.cons (macFold col (0, 0)).1 .nil))).toNat
        + (mulHiW cin 1).toNat < 2 ^ 64)
    (hhi : (carryAddStep (macFold col (0, 0)).1 (macFold col (0, 0)).2 cin).2.toNat < 2 ^ 51) :
    (colReduce col cin).1.toNat + (colReduce col cin).2.toNat * 2 ^ 51 = V + cin.toNat := by
  simp only [colReduce]
  rw [wordExtract_reconstruct _ _ hhi,
    carryAddStep_reconstruct (macFold col (0, 0)).1 (macFold col (0, 0)).2 cin hhead, hV]

/-- The extracted limb is the exact radix-2⁵¹ residue `(V + cin) % 2⁵¹` — `feCarryLimbNat`'s
    `tₖ % 2⁵¹`. -/
theorem colReduce_limb (col : List (BitVec 64 × BitVec 64)) (cin : BitVec 64) (V : Nat)
    (hV : (macFold col (0, 0)).1.toNat + (macFold col (0, 0)).2.toNat * 2 ^ 64 = V)
    (hhead : (macFold col (0, 0)).2.toNat
        + (Com.denote fieldAddCarryCom
            (.cons (cin * 1) (.cons (macFold col (0, 0)).1 .nil))).toNat
        + (mulHiW cin 1).toNat < 2 ^ 64)
    (hhi : (carryAddStep (macFold col (0, 0)).1 (macFold col (0, 0)).2 cin).2.toNat < 2 ^ 51) :
    (colReduce col cin).1.toNat = (V + cin.toNat) % 2 ^ 51 := by
  have hrec := colReduce_reconstruct col cin V hV hhead hhi
  have hlimb : (colReduce col cin).1.toNat < 2 ^ 51 := by
    simp only [colReduce, wordExtract_limb]
    exact Nat.mod_lt _ (by norm_num)
  omega

/-- The extracted carry-out is the exact radix-2⁵¹ quotient `(V + cin) / 2⁵¹` —
    `feCarryLimbNat`'s `cₖ = tₖ / 2⁵¹`. -/
theorem colReduce_carry (col : List (BitVec 64 × BitVec 64)) (cin : BitVec 64) (V : Nat)
    (hV : (macFold col (0, 0)).1.toNat + (macFold col (0, 0)).2.toNat * 2 ^ 64 = V)
    (hhead : (macFold col (0, 0)).2.toNat
        + (Com.denote fieldAddCarryCom
            (.cons (cin * 1) (.cons (macFold col (0, 0)).1 .nil))).toNat
        + (mulHiW cin 1).toNat < 2 ^ 64)
    (hhi : (carryAddStep (macFold col (0, 0)).1 (macFold col (0, 0)).2 cin).2.toNat < 2 ^ 51) :
    (colReduce col cin).2.toNat = (V + cin.toNat) / 2 ^ 51 := by
  have hrec := colReduce_reconstruct col cin V hV hhead hhi
  have hlimb : (colReduce col cin).1.toNat < 2 ^ 51 := by
    simp only [colReduce, wordExtract_limb]
    exact Nat.mod_lt _ (by norm_num)
  omega

/-! ### 6e. Deriving the per-step headroom from the radix-2⁵¹ accumulator bound

The `carryAddStep` / `colReduce` value laws carry a word-level no-high-overflow headroom.
These two facts (`mulHiW c 1 = 0`, the carry-out `≤ 1`) collapse that headroom to the single
pre-add high-word bound `hi < 2⁵¹`, so the assembled kernel's headroom obligations reduce to
the radix-2⁵¹ column bounds. -/

/-- The high word of `c · 1` is zero (`c < 2⁶⁴`). -/
theorem mulHiW_one_toNat (c : BitVec 64) : (mulHiW c 1).toNat = 0 := by
  rw [MontMulFragmentDemo.mulHiW_toNat]
  have h1 : (1 : BitVec 64).toNat = 1 := by decide
  rw [h1, Nat.mul_one, Nat.div_eq_of_lt c.isLt]

/-- The branchless carry-out is a single bit (`≤ 1`), from the add reconstruction. -/
theorem fieldAddCarry_le_one (x0 x1 : BitVec 64) :
    (Com.denote fieldAddCarryCom (.cons x0 (.cons x1 .nil))).toNat ≤ 1 := by
  have h := fieldAdd_carry_reconstruct x0 x1
  have hx0 := x0.isLt; have hx1 := x1.isLt
  omega

/-- **The `carryAddStep` headroom reduces to `hi < 2⁵¹`.** The two threaded terms (the
    high word of `c·1`, which is `0`, and the carry-out, which is `≤ 1`) never push the
    running high word over `2⁶⁴` once `hi < 2⁵¹`. -/
theorem carryAddStep_headroom_of (lo hi c : BitVec 64) (hhi : hi.toNat < 2 ^ 51) :
    hi.toNat + (Com.denote fieldAddCarryCom (.cons (c * 1) (.cons lo .nil))).toNat
      + (mulHiW c 1).toNat < 2 ^ 64 := by
  have h1 := fieldAddCarry_le_one (c * 1) lo
  have h2 := mulHiW_one_toNat c
  omega

/-! ## 7. The whole word-level reduction as one model, reconstructing `feCarryNat`

`feMulModel a b` runs the deployed reduction entirely over the emitted word primitives: fold
each of the five columns and thread the carry with `colReduce` (§6d), then apply the `c₄·19`
top fold (`regConst 64 19` prescale) and the final short carry (`>>> 51` into limb 1). This is
exactly the sequence of word ops the assembled `[stackArr,stackArr] → stackArr` kernel runs.
`feMulModel_eq_feCarryNat` proves it equals the deployed 5-limb result `feCarryNat a b` (§1b),
under the radix-2⁵¹ column bounds (the five `macFoldHeadroom`s, the `19`-prescale limb bounds,
and the `feMulRₖ < 2¹¹⁰` accumulator bounds — the deployed HW invariant, as `hlt` elsewhere).
The proof threads `col0_reconstruct … col4_reconstruct` per column and `colReduce_limb` /
`colReduce_carry` per carry — the straight-line reduction unfold, on the model. Composing with
`fe25519MulProductCom` (§5) then gives the array leaf's `denote = feCarryNat` (the residual is
only the de Bruijn Com generation of this model as `Com` ops; the arithmetic is closed here). -/

/-- **The word-level reduction model.** Five `colReduce` carry-chain steps, then the `c₄·19`
    top fold `l0raw = limb₀ + 19·c₄` and the final short carry `>>> 51` into limb 1 — the exact
    deployed `fe25519_mul` reduction over the emitted primitives. -/
def feMulModel (a b : Fe51) : Fe51 :=
  let r0 := colReduce (col0Products a b) 0
  let r1 := colReduce (col1Products a b) r0.2
  let r2 := colReduce (col2Products a b) r1.2
  let r3 := colReduce (col3Products a b) r2.2
  let r4 := colReduce (col4Products a b) r3.2
  let l0raw := r0.1 + (19 : BitVec 64) * r4.2
  ![ l0raw &&& mask51,
     r1.1 + (l0raw >>> (51 : Nat)),
     r2.1, r3.1, r4.1 ]

/-- A word equals `ofNat 64` of its own `toNat` reconstructed from a Nat witness. -/
theorem bitvec_eq_ofNat_of_toNat (x : BitVec 64) (n : Nat) (h : x.toNat = n) :
    x = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, ← h, Nat.mod_eq_of_lt x.isLt]

/-- **The generic carry-chain step, threaded by the radix-2⁵¹ bounds.** For a column
    reconstructing to `R < 2¹⁰⁹` and an incoming carry `cin < 2⁵⁹`, `colReduce col cin`
    extracts the limb `(R + cin) % 2⁵¹`, the carry-out `(R + cin) / 2⁵¹`, and the carry-out
    stays `< 2⁵⁹` (so the chain re-enters the same regime). All headroom obligations
    (`carryAddStep`, `wordExtract`) discharge from `R < 2¹⁰⁹` and `cin < 2⁵⁹`. -/
theorem colStep (col : List (BitVec 64 × BitVec 64)) (R : Nat) (cin : BitVec 64)
    (hV : (macFold col (0, 0)).1.toNat + (macFold col (0, 0)).2.toNat * 2 ^ 64 = R)
    (hR : R < 2 ^ 109) (hcin : cin.toNat < 2 ^ 59) :
    (colReduce col cin).1.toNat = (R + cin.toNat) % 2 ^ 51
      ∧ (colReduce col cin).2.toNat = (R + cin.toNat) / 2 ^ 51
      ∧ (colReduce col cin).2.toNat < 2 ^ 59 := by
  have hlo := (macFold col (0, 0)).1.isLt
  have hpre : (macFold col (0, 0)).2.toNat < 2 ^ 51 := by omega
  have hhead := carryAddStep_headroom_of (macFold col (0, 0)).1 (macFold col (0, 0)).2 cin hpre
  have hpost : (carryAddStep (macFold col (0, 0)).1 (macFold col (0, 0)).2 cin).2.toNat < 2 ^ 51 := by
    have hs := carryAddStep_reconstruct (macFold col (0, 0)).1 (macFold col (0, 0)).2 cin hhead
    have hlo' := (carryAddStep (macFold col (0, 0)).1 (macFold col (0, 0)).2 cin).1.isLt
    omega
  have hl := colReduce_limb col cin R hV hhead hpost
  have hc := colReduce_carry col cin R hV hhead hpost
  refine ⟨hl, hc, ?_⟩
  rw [hc]; omega

/-- **The word-level model reconstructs the deployed 5-limb `fe25519_mul` result.** Under the
    radix-2⁵¹ column bounds (the five `macFoldHeadroom`s, the `19`-prescale limb bounds
    `a₁..a₄ < 2⁵⁹`, and the wide-accumulator bounds `feMulRₖ < 2¹⁰⁹`), the emitted-primitive
    reduction model `feMulModel a b` equals the deployed reduced limbs `feCarryNat a b` (§1b).
    The proof threads `col0_reconstruct … col4_reconstruct` (per column) and `colStep`'s
    `colReduce_limb`/`colReduce_carry` (per carry) — the straight-line reduction unfold, on the
    model; the top `c₄·19` fold and the final short carry close by `limbWord_toNat` /
    `wordExtract`. Composing with `fe25519MulProductCom` (§5) transfers the full
    multiply-mod-`p` correctness (`fe25519_mul_leaf_congr`) to this front-generated computation. -/
theorem feMulModel_eq_feCarryNat (a b : Fe51)
    (h0 : macFoldHeadroom (col0Products a b) (0, 0))
    (h1 : macFoldHeadroom (col1Products a b) (0, 0))
    (h2 : macFoldHeadroom (col2Products a b) (0, 0))
    (h3 : macFoldHeadroom (col3Products a b) (0, 0))
    (h4 : macFoldHeadroom (col4Products a b) (0, 0))
    (ha1 : (a 1).toNat < 2 ^ 59) (ha2 : (a 2).toNat < 2 ^ 59)
    (ha3 : (a 3).toNat < 2 ^ 59) (ha4 : (a 4).toNat < 2 ^ 59)
    (hR0 : feMulR0 a b < 2 ^ 109) (hR1 : feMulR1 a b < 2 ^ 109)
    (hR2 : feMulR2 a b < 2 ^ 109) (hR3 : feMulR3 a b < 2 ^ 109)
    (hR4 : feMulR4 a b < 2 ^ 109) :
    feMulModel a b = feCarryNat a b := by
  have hV0 := col0_reconstruct a b h0 ha1 ha2 ha3 ha4
  have hV1 := col1_reconstruct a b h1 ha2 ha3 ha4
  have hV2 := col2_reconstruct a b h2 ha3 ha4
  have hV3 := col3_reconstruct a b h3 ha4
  have hV4 := col4_reconstruct a b h4
  have hcin0 : (0 : BitVec 64).toNat < 2 ^ 59 := by decide
  obtain ⟨hl0, hc0, hb0⟩ := colStep (col0Products a b) (feMulR0 a b) 0 hV0 hR0 hcin0
  obtain ⟨hl1, hc1, hb1⟩ := colStep (col1Products a b) (feMulR1 a b)
    (colReduce (col0Products a b) 0).2 hV1 hR1 hb0
  obtain ⟨hl2, hc2, hb2⟩ := colStep (col2Products a b) (feMulR2 a b)
    (colReduce (col1Products a b) (colReduce (col0Products a b) 0).2).2 hV2 hR2 hb1
  obtain ⟨hl3, hc3, hb3⟩ := colStep (col3Products a b) (feMulR3 a b)
    (colReduce (col2Products a b)
      (colReduce (col1Products a b) (colReduce (col0Products a b) 0).2).2).2 hV3 hR3 hb2
  obtain ⟨hl4, hc4, hb4⟩ := colStep (col4Products a b) (feMulR4 a b)
    (colReduce (col3Products a b) (colReduce (col2Products a b)
      (colReduce (col1Products a b) (colReduce (col0Products a b) 0).2).2).2).2 hV4 hR4 hb3
  have hlraw : ((colReduce (col0Products a b) 0).1
        + (19 : BitVec 64) * (colReduce (col4Products a b) (colReduce (col3Products a b)
            (colReduce (col2Products a b) (colReduce (col1Products a b)
              (colReduce (col0Products a b) 0).2).2).2).2).2).toNat
      = (colReduce (col0Products a b) 0).1.toNat
        + 19 * (colReduce (col4Products a b) (colReduce (col3Products a b)
            (colReduce (col2Products a b) (colReduce (col1Products a b)
              (colReduce (col0Products a b) 0).2).2).2).2).2.toNat := by
    have hno : (colReduce (col0Products a b) 0).1.toNat
        + 19 * (colReduce (col4Products a b) (colReduce (col3Products a b)
            (colReduce (col2Products a b) (colReduce (col1Products a b)
              (colReduce (col0Products a b) 0).2).2).2).2).2.toNat < 2 ^ 64 := by
      rw [hl0]; omega
    rw [BitVec.toNat_add, mul19_toNat _ hb4, Nat.mod_eq_of_lt hno]
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  funext i
  simp only [feCarryNat]
  apply bitvec_eq_ofNat_of_toNat
  fin_cases i
  · show (feMulModel a b 0).toNat = feCarryLimbNat a b 0
    simp only [feMulModel, feCarryLimbNat, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons]
    rw [limbWord_toNat _ 0, hlraw]
    omega
  · show (feMulModel a b 1).toNat = feCarryLimbNat a b 1
    simp only [feMulModel, feCarryLimbNat, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.tail_cons]
    rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, hlraw, Nat.shiftRight_eq_div_pow]
    omega
  · show (feMulModel a b 2).toNat = feCarryLimbNat a b 2
    simp only [feMulModel, feCarryLimbNat, Matrix.cons_val_two, Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons]
    omega
  · show (feMulModel a b 3).toNat = feCarryLimbNat a b 3
    simp only [feMulModel, feCarryLimbNat, Matrix.cons_val_three, Matrix.cons_val_two,
      Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons]
    omega
  · show (feMulModel a b 4).toNat = feCarryLimbNat a b 4
    simp only [feMulModel, feCarryLimbNat, Matrix.cons_val_four, Matrix.cons_val_three,
      Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.tail_cons]
    omega

/-! ## 7b. The front-generated reduction, fed through the array writeback

The word-level model `feMulModel` (the emitted-primitive reduction, §7) fed through the
array assembly `fe25519MulProductCom` (§5) yields one `stackArr 64 5` product value equal to
the deployed 5-limb `fe25519_mul` result — and the full multiply-mod-`p` correctness transfers
to this front-generated computation for free. This is the array leaf's `denote = feCarryNat` on
the composed front (model + writeback); the only remaining step to the single flat `Com` is the
syntactic de Bruijn generation of `feMulModel` as inline `Com` ops (its `denote = feMulModel` —
the arithmetic is already `feMulModel_eq_feCarryNat`). -/

/-- **The model fed through the writeback denotes the deployed result.** Under the radix-2⁵¹
    column bounds, `fe25519MulProductCom` applied to the emitted-primitive reduction model
    `feMulModel a b` denotes to the deployed 5-limb `fe25519_mul` output `feCarryNat a b` as one
    product array value (`fe25519MulProductCom_denote` + `feMulModel_eq_feCarryNat`). -/
theorem fe25519MulProductCom_feMulModel (s0 : Fin 5 → BitVec 64) (a b : Fe51)
    (h0 : macFoldHeadroom (col0Products a b) (0, 0))
    (h1 : macFoldHeadroom (col1Products a b) (0, 0))
    (h2 : macFoldHeadroom (col2Products a b) (0, 0))
    (h3 : macFoldHeadroom (col3Products a b) (0, 0))
    (h4 : macFoldHeadroom (col4Products a b) (0, 0))
    (ha1 : (a 1).toNat < 2 ^ 59) (ha2 : (a 2).toNat < 2 ^ 59)
    (ha3 : (a 3).toNat < 2 ^ 59) (ha4 : (a 4).toNat < 2 ^ 59)
    (hR0 : feMulR0 a b < 2 ^ 109) (hR1 : feMulR1 a b < 2 ^ 109)
    (hR2 : feMulR2 a b < 2 ^ 109) (hR3 : feMulR3 a b < 2 ^ 109)
    (hR4 : feMulR4 a b < 2 ^ 109) :
    fe25519MulProductCom.denote (mulPackVal s0 (feMulModel a b)) = feCarryNat a b := by
  rw [fe25519MulProductCom_denote]
  exact feMulModel_eq_feCarryNat a b h0 h1 h2 h3 h4 ha1 ha2 ha3 ha4 hR0 hR1 hR2 hR3 hR4

/-- **The full multiply-mod-`p` correctness on the front-generated reduction leaf.** The
    reconstructed integer of the model-fed product array is congruent to `feToNat51 a ·
    feToNat51 b` mod `p = 2²⁵⁵−19`, under the radix-2⁵¹ column bounds and the output-limb bound.
    The front reduction denotes to the deployed result (`fe25519MulProductCom_feMulModel`); the
    deployed-result correctness (`fe25519_mul_deployed_congr`) then closes it — the complete
    field-multiply leaf, arithmetic-closed on the emitted-primitive computation. -/
theorem fe25519_mul_model_leaf_congr (s0 : Fin 5 → BitVec 64) (a b : Fe51)
    (h0 : macFoldHeadroom (col0Products a b) (0, 0))
    (h1 : macFoldHeadroom (col1Products a b) (0, 0))
    (h2 : macFoldHeadroom (col2Products a b) (0, 0))
    (h3 : macFoldHeadroom (col3Products a b) (0, 0))
    (h4 : macFoldHeadroom (col4Products a b) (0, 0))
    (ha1 : (a 1).toNat < 2 ^ 59) (ha2 : (a 2).toNat < 2 ^ 59)
    (ha3 : (a 3).toNat < 2 ^ 59) (ha4 : (a 4).toNat < 2 ^ 59)
    (hR0 : feMulR0 a b < 2 ^ 109) (hR1 : feMulR1 a b < 2 ^ 109)
    (hR2 : feMulR2 a b < 2 ^ 109) (hR3 : feMulR3 a b < 2 ^ 109)
    (hR4 : feMulR4 a b < 2 ^ 109)
    (hlt : ∀ i : Fin 5, feCarryLimbNat a b i < 2 ^ 64) :
    (feToNat51 (fe25519MulProductCom.denote (mulPackVal s0 (feMulModel a b))) : ℤ)
      ≡ (feToNat51 a : ℤ) * feToNat51 b [ZMOD ((2 : ℤ) ^ 255 - 19)] := by
  rw [fe25519MulProductCom_feMulModel s0 a b h0 h1 h2 h3 h4 ha1 ha2 ha3 ha4 hR0 hR1 hR2 hR3 hR4]
  exact fe25519_mul_deployed_congr a b hlt

/-! ## 8. `kernel%` leaves over the `[stackArr 64 5, stackArr 64 5]` multiply context

The dialect-generic `kernel%` symbol-table elaborator (`VIR/KernelSyntax.lean`) authors a
straight-line `Com jasminDialect` from named let-bindings, resolving each name to its typed
de-Bruijn `Ctxt.Var` — the de-Bruijn threading a hand-authored leaf spells out by index. The two
leaves below are `kernel%`-authored over the fe25519 multiply's own
`[stackArr 64 5, stackArr 64 5] → stackArr 64 5` context: they load with `stackLoad`, compute in
the `regArith` / `regConst` alphabet, and write back with a `stackStore` chain, and their
denotations are cheap `rfl` (the elaborated `Com.var` / `Ctxt.Var.lookup` chain unfolds
structurally). The whole-multiply arithmetic — the five schoolbook columns, the `2²⁵⁵ ≡ 19` fold,
and the canonical carry reduction, all over these same emitted primitives — is closed as one
word-level model in §7 (`feMulModel_eq_feCarryNat`) and carried to the array leaf with full
multiply-mod-`p` correctness by `fe25519_mul_model_leaf_congr` (§7b). -/

open CatCrypt.Crypto.SecureCompilation.VIR.KernelSyntax in
/-- A `kernel%` leaf over the multiply context: load `A[0]`, `B[0]`, multiply, store the product
    into slot `0`, and return the array. -/
def fe25519MulLoadStoreCom :
    Com jasminDialect [.stackArr 64 5, .stackArr 64 5] (.stackArr 64 5) :=
  kernel% (A : .stackArr 64 5) (B : .stackArr 64 5) {
    i0 := (JasminOp.regConst 64 0) [];
    a0 := (JasminOp.stackLoad 64 5) [A, i0];
    b0 := (JasminOp.stackLoad 64 5) [B, i0];
    m0 := (JasminOp.regArith .mul 64) [a0, b0];
    A0 := (JasminOp.stackStore 64 5) [A, i0, m0];
    ret A0
  }

/-- **Denote — cheap `rfl`.** The generated leaf denotes `A` with slot `0` set to `A 0 · B 0`. -/
theorem fe25519MulLoadStoreCom_denote (A B : Fin 5 → BitVec 64) :
    Com.denote fe25519MulLoadStoreCom (.cons A (.cons B .nil))
      = stackSet A 0 (A 0 * B 0) := rfl

open CatCrypt.Crypto.SecureCompilation.VIR.KernelSyntax in
/-- A `kernel%` leaf running a full `stackStore` writeback chain: five per-slot products stored
    back into the first array, returning the fully-overwritten array. -/
def fe25519MulWritebackCom :
    Com jasminDialect [.stackArr 64 5, .stackArr 64 5] (.stackArr 64 5) :=
  kernel% (A : .stackArr 64 5) (B : .stackArr 64 5) {
    i0 := (JasminOp.regConst 64 0) [];
    i1 := (JasminOp.regConst 64 1) [];
    i2 := (JasminOp.regConst 64 2) [];
    i3 := (JasminOp.regConst 64 3) [];
    i4 := (JasminOp.regConst 64 4) [];
    a0 := (JasminOp.stackLoad 64 5) [A, i0];
    a1 := (JasminOp.stackLoad 64 5) [A, i1];
    a2 := (JasminOp.stackLoad 64 5) [A, i2];
    a3 := (JasminOp.stackLoad 64 5) [A, i3];
    a4 := (JasminOp.stackLoad 64 5) [A, i4];
    b0 := (JasminOp.stackLoad 64 5) [B, i0];
    m0 := (JasminOp.regArith .mul 64) [a0, b0];
    m1 := (JasminOp.regArith .mul 64) [a1, b0];
    m2 := (JasminOp.regArith .mul 64) [a2, b0];
    m3 := (JasminOp.regArith .mul 64) [a3, b0];
    m4 := (JasminOp.regArith .mul 64) [a4, b0];
    S0 := (JasminOp.stackStore 64 5) [A, i0, m0];
    S1 := (JasminOp.stackStore 64 5) [S0, i1, m1];
    S2 := (JasminOp.stackStore 64 5) [S1, i2, m2];
    S3 := (JasminOp.stackStore 64 5) [S2, i3, m3];
    S4 := (JasminOp.stackStore 64 5) [S3, i4, m4];
    ret S4
  }

/-- **Denote — `funext` + per-slot `rfl`.** The fully-overwritten array equals the `![…]` vector
    of the per-slot products — the `feMulModel`-shaped `Matrix.of` / `vecCons` writeback target. -/
theorem fe25519MulWritebackCom_denote (A B : Fin 5 → BitVec 64) :
    Com.denote fe25519MulWritebackCom (.cons A (.cons B .nil))
      = ![A 0 * B 0, A 1 * B 0, A 2 * B 0, A 3 * B 0, A 4 * B 0] := by
  funext i; fin_cases i <;> rfl

end CatCrypt.Crypto.SecureCompilation.Fe25519MulLeaf

