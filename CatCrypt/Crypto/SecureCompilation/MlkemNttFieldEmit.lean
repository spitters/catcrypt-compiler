/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2WholePermCom
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.FieldDescentMlkem

/-!
# ML-KEM (`q = 3329`) field-op word blocks + their `mkEnc` realizations

The arithmetic foundation for an ML-KEM forward-NTT owned emit: the three
`q = 3329` word blocks and the proofs that they realize the field ops under the
canonical encoding `mkEnc`. This is the lattice analogue of the per-op word
realizations `FieldDescentBabyBear.bb{Mul,Add,Sub}_realizes` use for BabyBear.

**Scope (read `## What this file does / does NOT contain` below).** This file is
the word-block layer ONLY. It does NOT author an NTT `Com`, does NOT emit any
`.s`, and there is NO KAT here — those are named residual.

## Why a Barrett reduce, not a single csub

The jasmin word alphabet (`JasminBinOp`: `add/sub/mul/and/or/xor/shl/shr/andn`)
has **no `div`/`mod` op**, so the scalar `modMul` reduce `(a·b) % q` cannot be a
single conditional subtract: the product `a·b < q² = 11 082 241 < 2^24` is up to
`~3329·q` past canonical. We realize `% q` by **Barrett reduction** with the
single precomputed constant `m = ⌊2^24 / q⌋ = 5039`:

    q̂ = (r · 5039) >>> 24      -- quotient estimate, exact to ±1 over [0, q²)
    t = r − q̂·q                -- remainder in [0, 2q)
    mkCsub t = t % q           -- one conditional subtract canonicalises

`mkBarrettW_eq` proves this equals `mkCsub r` (= `r % q`, the
`FieldDescentMlkem` spec) for every `r < q²`; coupled with `FieldDescentMlkem`'s
proved `mkMul_realizes`/`mkAdd_realizes`/`mkSub_realizes`, the emitted word
blocks realize the field ops under the canonical encoding `mkEnc`.

## What this file does / does NOT contain

**Proved here (the word-block layer):**
* `mkMulW`/`mkAddW`/`mkSubW` — the three `q = 3329` word blocks (Barrett
  mul-reduce, csub add, csub sub).
* `mkMulW_realizes`/`mkAddW_realizes`/`mkSubW_realizes` — each word block
  realizes the corresponding field op (`modMulF`/`modAddF`/`modSubF` on
  `ZMod Q`) under the canonical encoding `mkEnc`, via `mkBarrettW_eq` /
  `mkCsubW_eq` + the `FieldDescentMlkem` squares.

**NOT in this file (named residual — future work):**
* An NTT `Com`. There is no `Com jasminDialect` butterfly/NTT authored here, no
  `BState`/`emitMul`/`emitAdd` use — only the word-block defs + their proofs. An
  N = 8 (and ultimately N = 256) forward-NTT would COMPOSE these word blocks over
  the `Poseidon2WholePermCom` `BState` builder with the FIPS-203 twiddles as
  `regConst`. (Per the N=256 RA probe, `Com.toLprogPhysAbi` already spills over a
  `Nat` slot universe, so the widening is builder generalization + layer-fold
  authoring, not an RA gap. What remains is the butterfly Com and its denotation
  tie; the arithmetic is closed here.)
* Any `.s` emit (`Com.toLprogPhysAbi |> renderLprogAtt`) and any KAT. There is no
  `mlkem_ntt8_field_kat.c`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.MlkemNttFieldEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2WholePermCom
open CatCrypt.Crypto.SecureCompilation.FieldDescentMlkem
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect

/-- The jasmin word type. -/
abbrev r64 : JasminTy := JasminTy.reg 64

/-! ## 1. The mod-`q` conditional subtract `mkCsubW r = (r − q) + (q & mask)`

The branchless conditional subtract of `q = 3329`, identical in shape to
`Poseidon2WholePermCom.bbCsub` but at the ML-KEM prime: subtract `q`, broadcast
the sign bit of `r − q`, AND it back onto `q`, add. Canonicalises any `r < 2q`. -/

/-- The ML-KEM prime as a `Nat`. -/
abbrev cQ : Nat := 3329

/-- The Barrett multiplier `m = ⌊2^24 / 3329⌋`. -/
abbrev cM24 : Nat := 5039

/-- Branchless conditional subtract of `q` on a 64-bit word (mirrors `bbCsub`). -/
def mkCsubW (r : BitVec 64) : BitVec 64 :=
  let t := r - (3329 : BitVec 64)
  t + ((3329 : BitVec 64) &&& (0 - (t >>> (63 : Nat))))

/-- The Barrett mod-`q` reduce on a 64-bit word: `q̂ = (r·m)>>24`, `t = r − q̂·q`,
    one csub. Realizes `r % q` for every `r < q²`. -/
def mkBarrettW (r : BitVec 64) : BitVec 64 :=
  let qhat := (r * (5039 : BitVec 64)) >>> (24 : Nat)
  mkCsubW (r - qhat * (3329 : BitVec 64))

/-- The ML-KEM word multiply: full-width product then Barrett reduce. -/
def mkMulW (a b : BitVec 64) : BitVec 64 := mkBarrettW (a * b)

/-- The ML-KEM word add: `a + b` then one csub. -/
def mkAddW (a b : BitVec 64) : BitVec 64 := mkCsubW (a + b)

/-- The ML-KEM word subtract: `a + (q − b)` then one csub. -/
def mkSubW (a b : BitVec 64) : BitVec 64 := mkCsubW (a + ((3329 : BitVec 64) - b))

/-! ## 2. The word blocks realize the `FieldDescentMlkem` reduce ops

`mkCsubW` matches `FieldDescentMlkem.mkCsub` (`r % q`) for `r < 2q`; `mkBarrettW`
matches it for `r < q²`. Both are quantifier-free 64-bit BitVec facts under a
`toNat` bound, discharged by `bv_decide` (the range hypothesis lets the SAT
backend bound the high bits). -/

/-- **The branchless csub realizes `r % q` for `r < 2q`.** Stated with the bound
    as a `BitVec` comparison so `bv_decide`'s SAT backend can use it. -/
theorem mkCsubW_eq_bv (r : BitVec 64) (h : r < (6658 : BitVec 64)) :
    mkCsubW r = mkCsub r := by
  unfold mkCsubW mkCsub
  bv_decide

/-- `r.toNat < 2q ⇒ r < 6658#64` (the BitVec-comparison form). -/
theorem lt_bv_of_toNat {n : Nat} (r : BitVec 64) (h : r.toNat < n) (hn : n ≤ 6658) :
    r < (6658 : BitVec 64) := by
  rw [BitVec.lt_def]; show r.toNat < (6658 : BitVec 64).toNat
  have : (6658 : BitVec 64).toNat = 6658 := by decide
  omega

/-- **The branchless csub realizes `r % q` for `r < 2q`** (`toNat` form). -/
theorem mkCsubW_eq (r : BitVec 64) (h : r.toNat < 2 * 3329) :
    mkCsubW r = mkCsub r :=
  mkCsubW_eq_bv r (lt_bv_of_toNat r h (by omega))

/-- The Barrett remainder `t = r − q̂·q`. -/
def mkBarrettRem (r : BitVec 64) : BitVec 64 :=
  r - ((r * (5039 : BitVec 64)) >>> (24 : Nat)) * (3329 : BitVec 64)

/-- **The Barrett remainder is `< 2q`** for `r < q²` (the ±1 quotient estimate),
    a self-contained `bv_decide` fact (no `%` in the goal). -/
theorem mkBarrettRem_lt (r : BitVec 64) (h : r < (11082241 : BitVec 64)) :
    mkBarrettRem r < (6658 : BitVec 64) := by
  unfold mkBarrettRem
  bv_decide

/-- **The Barrett remainder has the same residue mod `q` as `r`**, for `r < q²`:
    a self-contained `bv_decide` fact on the two `umod`s (no extra arithmetic in
    the goal). -/
theorem mkBarrettRem_umod (r : BitVec 64) (h : r < (11082241 : BitVec 64)) :
    mkBarrettRem r % (3329 : BitVec 64) = r % (3329 : BitVec 64) := by
  unfold mkBarrettRem
  -- Deterministic structural proof (the two-`umod` `bv_decide` was wall-clock
  -- flaky under parallel build load). `mkBarrettRem r = r − qhat·q` with
  -- `qhat = (r·5039)>>>24`; the two heavy facts become SIMPLE inequalities
  -- (`qhat < q`, `qhat·q ≤ r`, no `umod` — fast/robust SAT), then the residue
  -- equality is pure `Nat` arithmetic (subtracting a multiple of `q`).
  have hq : ((r * (5039 : BitVec 64)) >>> (24 : Nat)) < (3329 : BitVec 64) := by bv_decide
  have hb : ((r * (5039 : BitVec 64)) >>> (24 : Nat)) * (3329 : BitVec 64) ≤ r := by bv_decide
  have hqn : (((r * (5039 : BitVec 64)) >>> (24 : Nat))).toNat < 3329 := by simpa using! hq
  have h3 : (3329 : BitVec 64).toNat = 3329 := by decide
  have hm : (((r * (5039 : BitVec 64)) >>> (24 : Nat))).toNat * 3329 < 2 ^ 64 := by nlinarith [hqn]
  have hbn : (((r * (5039 : BitVec 64)) >>> (24 : Nat))).toNat * 3329 ≤ r.toNat := by
    have h := hb; rw [BitVec.le_def, BitVec.toNat_mul, h3, Nat.mod_eq_of_lt hm] at h; exact h
  apply BitVec.toNat_injective
  rw [BitVec.toNat_umod, BitVec.toNat_umod, BitVec.toNat_sub_of_le hb, BitVec.toNat_mul]
  simp only [h3, Nat.mod_eq_of_lt hm]
  omega

/-- **The Barrett block realizes `r % q` for `r < q²`** (`toNat`/Nat form): the
    remainder is `< 2q` (so one csub canonicalises) and `≡ r (mod q)`. -/
theorem mkBarrettW_eq (r : BitVec 64) (h : r.toNat < 3329 * 3329) :
    mkBarrettW r = mkCsub r := by
  have hbv : r < (11082241 : BitVec 64) := by
    rw [BitVec.lt_def]; show r.toNat < (11082241 : BitVec 64).toNat
    have : (11082241 : BitVec 64).toNat = 11082241 := by decide
    omega
  -- mkBarrettW r = mkCsubW (mkBarrettRem r), and the remainder is < 2q.
  have hrem_lt : (mkBarrettRem r).toNat < 2 * 3329 := by
    have := mkBarrettRem_lt r hbv
    rw [BitVec.lt_def] at this; show (mkBarrettRem r).toNat < 2 * 3329
    have h6 : (6658 : BitVec 64).toNat = 6658 := by decide
    omega
  have hstep : mkBarrettW r = mkCsub (mkBarrettRem r) := by
    show mkCsubW (mkBarrettRem r) = mkCsub (mkBarrettRem r)
    exact mkCsubW_eq _ hrem_lt
  rw [hstep]
  -- mkCsub (mkBarrettRem r) = mkBarrettRem r % q = r % q  (same residue).
  show mkBarrettRem r % (3329 : BitVec 64) = r % (3329 : BitVec 64)
  exact mkBarrettRem_umod r hbv

/-- **`mkMulW` realizes the field multiply under `mkEnc`** (canonical encoding):
    the Barrett product block equals `mkEnc (a * b)`. Combines `mkBarrettW_eq`
    (the Barrett reduce = `%`) with `FieldDescentMlkem.mkMul_realizes`. -/
theorem mkMulW_realizes (a b : ZMod Q) :
    mkMulW (mkEnc a) (mkEnc b) = mkEnc (modMulF a b) := by
  have hab : (mkEnc a * mkEnc b).toNat < 3329 * 3329 := by
    have ha := mkEnc_lt a
    have hb := mkEnc_lt b
    rw [BitVec.toNat_mul]
    calc (mkEnc a).toNat * (mkEnc b).toNat % 2 ^ 64
        ≤ (mkEnc a).toNat * (mkEnc b).toNat := Nat.mod_le _ _
      _ < 3329 * 3329 := Nat.mul_lt_mul_of_lt_of_le ha (le_of_lt hb) (by omega)
  unfold mkMulW
  rw [mkBarrettW_eq _ hab]
  exact mkMul_realizes a b

/-- **`mkAddW` realizes the field add under `mkEnc`.** -/
theorem mkAddW_realizes (a b : ZMod Q) :
    mkAddW (mkEnc a) (mkEnc b) = mkEnc (modAddF a b) := by
  have hab : (mkEnc a + mkEnc b).toNat < 2 * 3329 := by
    have ha := mkEnc_lt a
    have hb := mkEnc_lt b
    rw [BitVec.toNat_add]
    calc ((mkEnc a).toNat + (mkEnc b).toNat) % 2 ^ 64
        ≤ (mkEnc a).toNat + (mkEnc b).toNat := Nat.mod_le _ _
      _ < 2 * 3329 := by omega
  unfold mkAddW
  rw [mkCsubW_eq _ hab]
  exact mkAdd_realizes a b

/-- **`mkSubW` realizes the field subtract under `mkEnc`.** -/
theorem mkSubW_realizes (a b : ZMod Q) :
    mkSubW (mkEnc a) (mkEnc b) = mkEnc (modSubF a b) := by
  have hab : (mkEnc a + ((3329 : BitVec 64) - mkEnc b)).toNat < 2 * 3329 := by
    have ha := mkEnc_lt a
    have hb := mkEnc_lt b
    have h3329 : (3329 : BitVec 64).toNat = 3329 := by decide
    have hble : mkEnc b ≤ (3329 : BitVec 64) := by
      rw [BitVec.le_def]; omega
    have hsub : ((3329 : BitVec 64) - mkEnc b).toNat ≤ 3329 := by
      rw [BitVec.toNat_sub_of_le hble]; omega
    rw [BitVec.toNat_add]
    calc ((mkEnc a).toNat + ((3329 : BitVec 64) - mkEnc b).toNat) % 2 ^ 64
        ≤ (mkEnc a).toNat + ((3329 : BitVec 64) - mkEnc b).toNat := Nat.mod_le _ _
      _ < 2 * 3329 := by omega
  unfold mkSubW
  rw [mkCsubW_eq _ hab]
  exact mkSub_realizes a b

end CatCrypt.Crypto.SecureCompilation.MlkemNttFieldEmit
