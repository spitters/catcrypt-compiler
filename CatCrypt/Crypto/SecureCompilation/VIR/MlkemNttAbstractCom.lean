/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ButterflyBlockCom
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Abstract FIPS-203 ZMod-q NTT-butterfly tie for the unified-`Com` butterfly (model-free)

`ButterflyBlockCom.lean` migrated the ML-KEM NTT radix-2 Cooley–Tukey butterfly
leaf off the bespoke `Avx512Model` (`ZInstr`/`ZState`/`runZBlock`) machine onto
the unified `Com jasminDialect`, and pinned the denotations of
`butterflyHiCom`/`butterflyLoCom` to the packed `zmmPackQ` (8×u64) expressions

```
hi = zmmPackQ .add a (zmmPackQ .mul w b)
lo = zmmPackQ .sub a (zmmPackQ .mul w b)
```

over `BitVec 512` — but it stopped at the packed-`BitVec` level: it does NOT tie
those packed expressions back to the abstract **FIPS-203 NTT butterfly value**
`t = a + w·b` (resp. `a − w·b`) over the ML-KEM coefficient field `ZMod q`.

The bespoke realization web carries that abstract content over the `runZBlock`
machine: `MontReducedButterflyRealization.montRedButterfly_zmod` proves the
**defining Montgomery property** `output · R = (a + w·b) (mod N)` for the real
ML-KEM prime `q = 3329`, built on the field-domain butterfly value
`butterflyValLane s i = laneAddQ (za i) (laneMullq (zw i) (zb i))`. The
*field-domain* input to that REDC chain — the per-lane butterfly value
`t = a + w·b` cast to `ZMod q` — is the abstract content that survives
`Avx512Model` deletion, and that this module **re-anchors** onto the unified
`Com jasminDialect` denotation.

## What is re-anchored (the abstract ZMod-q tie)

The bespoke butterfly value lane is `laneAddQ (za i) (laneMullq (zw i) (zb i))`,
which at the `BitVec 64` level is `(za i) + (zw i) * (zb i)` — the SAME per-lane
arithmetic the unified `zmmPackQ .add a (zmmPackQ .mul w b)` computes (since
`laneAddQ = JasminBinOp.apply .add` and `laneMullq = JasminBinOp.apply .mul` at
width 64). This module proves, on the unified denotation and with **no
`Avx512Model`** in the import set:

* `zmmOfLanes_zmmLane'` / `zmmPackQ_lane` — the 8×u64 lane round-trip and the
  per-lane characterization of `zmmPackQ` (reproved locally, no AVX-512 model).
* `butterflyHiCom_lane` / `butterflyLoCom_lane` — lane `k` of the unified
  butterfly denotation is `(a_k) + (w_k)·(b_k)` (resp. `−`), pure `BitVec 64`.
* `butterflyHiCom_zmod` — **THE ABSTRACT TIE.** Under the FIPS-203 no-wrap bound
  on the ML-KEM range (`a_k.toNat + w_k.toNat·b_k.toNat < 2⁶⁴`), the unified
  `butterflyHiCom` output lane `k` cast to `ZMod q` equals the FIPS-203 NTT
  butterfly value `(a_k : ZMod q) + (w_k : ZMod q)·(b_k : ZMod q)` — the
  field-domain `a + w·b`, the input the Montgomery REDC chain consumes. This is
  the field-domain seam `montRedButterfly_zmod` builds on, re-anchored.
* `butterflyLoCom_zmod` — the `lo` companion `(a_k) − (w_k)·(b_k)` over `ZMod q`.

There is no `runZBlock` / `ZInstr` / `ZState` / `jasminc` in any theorem's
`#print axioms`: the tie is between the verified `Com jasminDialect` denotation
and the abstract `ZMod q` FIPS-203 butterfly value.

## Scope — the field-domain butterfly value, not the reduced output

This re-anchors the **field-domain** butterfly value `t = a + w·b (mod q)` — the
input to the Montgomery REDC chain, NOT the post-REDC Montgomery-form residue.
The post-REDC ZMod-q tie (`montRedButterfly_zmod`'s `output · R = t (mod N)`)
additionally folds in `montDigitBlock`/`montFoldBlock`/`csubBlock`, whose unified
`Com` migration (the `vpmuludq`/`vpandq`/`vpsrlq`/csub ops) is the remaining NTT
web. This module is the **pilot lane** of that web: the butterfly value seam,
proved over the unified denotation, off the bespoke machine.

## References
* FIPS 203 — ML-KEM (the NTT, §4.3); the radix-2 butterfly value `t = a + ζ·b`.

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.VIR.MlkemNttAbstractCom`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MlkemNttAbstractCom

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.ButterflyBlockCom

/-! ## 0. The 8×u64 ZMM lane round-trip and per-lane `zmmPackQ`

The qword lane lemmas, reproved locally so this module imports no AVX-512 model —
only `JasminDialect`'s lane defs (transitively via `ButterflyBlockCom`) and
Mathlib. Mirrors `KeccakThetaPiAbstractCom.{zmmOfLanes_zmmLane',zmmPackQ_lane}`. -/

/-- Reading lane `k` (a 64-bit qword) of an assembled 8-lane ZMM register recovers
    the `k`-th lane function value: `zmmLane (zmmOfLanes f) k = f k`. -/
theorem zmmOfLanes_zmmLane' (f : Fin 8 → BitVec 64) (k : Fin 8) :
    zmmLane (zmmOfLanes f) k = f k := by
  fin_cases k <;>
    (unfold zmmLane zmmOfLanes
     norm_num [Fin.val_ofNat, BitVec.extractLsb'_append_eq_of_le,
       BitVec.extractLsb'_append_eq_of_add_le, BitVec.extractLsb'_append_eq_right,
       BitVec.extractLsb'_append_eq_left]) <;>
    rfl

/-- Lane `k` of `zmmPackQ bop a b` is `bop.applyLane (zmmLane a k) (zmmLane b k)`. -/
theorem zmmPackQ_lane (bop : JasminBinOp) (a b : BitVec 512) (k : Fin 8) :
    zmmLane (zmmPackQ bop a b) k = bop.applyLane (zmmLane a k) (zmmLane b k) := by
  unfold zmmPackQ
  rw [zmmOfLanes_zmmLane']

/-! ## 1. The per-lane butterfly value, pure `BitVec 64`

Lane `k` of the unified butterfly denotation, characterized as the scalar 64-bit
butterfly value. These are the unified successors of the bespoke
`butterflyValLane` (`laneAddQ (za i) (laneMullq (zw i) (zb i))`). -/

/-- **`hi` lane characterization.** Lane `k` of `butterflyHiCom`'s denotation on
    `⟨w, a, b⟩` is the scalar 64-bit butterfly value `(a_k) + (w_k)·(b_k)`. -/
theorem butterflyHiCom_lane (w a b : BitVec 512) (k : Fin 8) :
    zmmLane (butterflyHiCom.denote (.cons w (.cons a (.cons b .nil)))) k
      = zmmLane a k + zmmLane w k * zmmLane b k := by
  rw [butterflyHiCom_denote, zmmPackQ_lane, zmmPackQ_lane]
  simp only [JasminBinOp.applyLane]

/-- **`lo` lane characterization.** Lane `k` of `butterflyLoCom`'s denotation on
    `⟨w, a, b⟩` is the scalar 64-bit butterfly value `(a_k) − (w_k)·(b_k)`. -/
theorem butterflyLoCom_lane (w a b : BitVec 512) (k : Fin 8) :
    zmmLane (butterflyLoCom.denote (.cons w (.cons a (.cons b .nil)))) k
      = zmmLane a k - zmmLane w k * zmmLane b k := by
  rw [butterflyLoCom_denote, zmmPackQ_lane, zmmPackQ_lane]
  simp only [JasminBinOp.applyLane]

/-! ## 2. The abstract FIPS-203 ZMod-q butterfly value tie

Under the ML-KEM no-wrap bound (the operand range FIPS-203 keeps coefficients in:
`a_k.toNat + w_k.toNat·b_k.toNat < 2⁶⁴`), the unified butterfly output lane cast
to `ZMod q` equals the abstract field-domain butterfly value
`(a_k : ZMod q) + (w_k : ZMod q)·(b_k : ZMod q)`. This is the field-domain seam
the bespoke `montRedButterfly_zmod` is built on, re-anchored onto the unified
`Com` denotation. -/

/-- **THE ABSTRACT TIE — `hi`.** Under the FIPS-203 no-wrap bound
    `(a_k).toNat + (w_k).toNat·(b_k).toNat < 2⁶⁴` (the ML-KEM operand range), the
    unified `butterflyHiCom` output lane `k`, cast to the ML-KEM coefficient field
    `ZMod q`, equals the FIPS-203 NTT butterfly value
    `(a_k : ZMod q) + (w_k : ZMod q)·(b_k : ZMod q)` — the field-domain `a + w·b`,
    exactly the value the Montgomery REDC chain consumes (`montRedButterfly_zmod`'s
    `butterflyValLane`), now over the verified `Com jasminDialect` denotation. -/
theorem butterflyHiCom_zmod (w a b : BitVec 512) (k : Fin 8) (q : Nat)
    (hwrap : (zmmLane a k).toNat + (zmmLane w k).toNat * (zmmLane b k).toNat < 2 ^ 64) :
    (((zmmLane (butterflyHiCom.denote (.cons w (.cons a (.cons b .nil)))) k).toNat : ZMod q))
      = ((zmmLane a k).toNat : ZMod q)
          + ((zmmLane w k).toNat : ZMod q) * ((zmmLane b k).toNat : ZMod q) := by
  rw [butterflyHiCom_lane]
  -- toNat of the product (no wrap on the ML-KEM range).
  have hprod : ((zmmLane w k) * (zmmLane b k)).toNat
      = (zmmLane w k).toNat * (zmmLane b k).toNat := by
    rw [BitVec.toNat_mul]
    exact Nat.mod_eq_of_lt (by omega)
  -- toNat of the add (no wrap, given the hypothesis).
  rw [BitVec.toNat_add, hprod, Nat.mod_eq_of_lt hwrap, Nat.cast_add, Nat.cast_mul]

/-- **THE ABSTRACT TIE — `lo`.** Under the FIPS-203 no-wrap bound
    `(w_k).toNat·(b_k).toNat ≤ (a_k).toNat` (the borrow-free ML-KEM range, so the
    `BitVec 64` subtraction is the difference), the unified
    `butterflyLoCom` output lane `k`, cast to `ZMod q`, equals the FIPS-203 NTT
    butterfly value `(a_k : ZMod q) − (w_k : ZMod q)·(b_k : ZMod q)`. -/
theorem butterflyLoCom_zmod (w a b : BitVec 512) (k : Fin 8) (q : Nat)
    (hprodlt : (zmmLane w k).toNat * (zmmLane b k).toNat < 2 ^ 64)
    (hnoborrow : (zmmLane w k).toNat * (zmmLane b k).toNat ≤ (zmmLane a k).toNat) :
    (((zmmLane (butterflyLoCom.denote (.cons w (.cons a (.cons b .nil)))) k).toNat : ZMod q))
      = ((zmmLane a k).toNat : ZMod q)
          - ((zmmLane w k).toNat : ZMod q) * ((zmmLane b k).toNat : ZMod q) := by
  rw [butterflyLoCom_lane]
  -- toNat of the product (no wrap on the ML-KEM range).
  have hprod : ((zmmLane w k) * (zmmLane b k)).toNat
      = (zmmLane w k).toNat * (zmmLane b k).toNat := by
    rw [BitVec.toNat_mul]
    exact Nat.mod_eq_of_lt hprodlt
  -- The borrow-free order at the BitVec level (from the toNat hypothesis).
  have hle : (zmmLane w k) * (zmmLane b k) ≤ (zmmLane a k) := by
    rw [BitVec.le_def, hprod]; exact hnoborrow
  -- toNat of the borrow-free subtraction.
  have hsub : ((zmmLane a k) - (zmmLane w k) * (zmmLane b k)).toNat
      = (zmmLane a k).toNat - (zmmLane w k).toNat * (zmmLane b k).toNat := by
    rw [BitVec.toNat_sub_of_le hle, hprod]
  rw [hsub]
  -- Cast the truncated Nat subtraction to ZMod q, using a = (a - p) + p.
  have hcast : ((((zmmLane a k).toNat - (zmmLane w k).toNat * (zmmLane b k).toNat) : Nat) : ZMod q)
      = ((zmmLane a k).toNat : ZMod q)
          - ((zmmLane w k).toNat : ZMod q) * ((zmmLane b k).toNat : ZMod q) := by
    have heq : (zmmLane a k).toNat
        = ((zmmLane a k).toNat - (zmmLane w k).toNat * (zmmLane b k).toNat)
            + (zmmLane w k).toNat * (zmmLane b k).toNat := by omega
    rw [eq_sub_iff_add_eq, ← Nat.cast_mul, ← Nat.cast_add]
    exact congrArg _ heq.symm
  rw [hcast]

/-! ## 3. Both butterfly value seams packaged

The `hi`/`lo` field-domain ZMod-q ties together: the unified butterfly computes
both FIPS-203 butterfly values `a + w·b` and `a − w·b` over `ZMod q`, the pilot
lane of the ML-KEM NTT web re-anchored off the bespoke `Avx512Model` machine. -/

/-- **The pilot deliverable.** The unified `Com jasminDialect` butterfly computes
    **both** FIPS-203 NTT butterfly values over the ML-KEM field `ZMod q` —
    `hi = a + w·b` and `lo = a − w·b` per lane — under the ML-KEM no-wrap /
    borrow-free range bounds, with no dependence on the `Avx512Model`
    (`ZInstr`/`runZBlock`) machine. The field-domain seam the Montgomery REDC
    chain consumes, re-anchored onto the verified denotation. -/
theorem butterflyCom_zmod (w a b : BitVec 512) (k : Fin 8) (q : Nat)
    (hwrap : (zmmLane a k).toNat + (zmmLane w k).toNat * (zmmLane b k).toNat < 2 ^ 64)
    (hnoborrow : (zmmLane w k).toNat * (zmmLane b k).toNat ≤ (zmmLane a k).toNat) :
    (((zmmLane (butterflyHiCom.denote (.cons w (.cons a (.cons b .nil)))) k).toNat : ZMod q))
        = ((zmmLane a k).toNat : ZMod q)
            + ((zmmLane w k).toNat : ZMod q) * ((zmmLane b k).toNat : ZMod q)
      ∧ (((zmmLane (butterflyLoCom.denote (.cons w (.cons a (.cons b .nil)))) k).toNat : ZMod q))
        = ((zmmLane a k).toNat : ZMod q)
            - ((zmmLane w k).toNat : ZMod q) * ((zmmLane b k).toNat : ZMod q) :=
  ⟨butterflyHiCom_zmod w a b k q hwrap,
   butterflyLoCom_zmod w a b k q (by omega) hnoborrow⟩

end CatCrypt.Crypto.SecureCompilation.VIR.MlkemNttAbstractCom
