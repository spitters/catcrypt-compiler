/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.CryptoSSA


@[expose] public section
set_option autoImplicit false

/-!
# DR — randomness: the `sample` op as a deterministic entropy-read leaf

This file is the "DR (deterministic randomness) phase" of the MLIR-dialect-
alignment restructure. Its purpose is to keep **probability off** the
deterministic SSA stack.

The two CryptoSSA sampling expressions

* `CExpr.sampleBit : CExpr Γ .bit`            (probabilistic denote `SPComp.sample Bool`)
* `CExpr.sampleBv n : CExpr Γ (.sword n)`     (probabilistic denote `SPComp.sample (BitVec n)`)

are *probabilistic* in `CExpr.denote` (`CryptoSSA.lean`). When the pure lowering
`toVIRExpr` (`VIR/CryptoToVIR.lean`) meets them it **drops to `none`**
(`| .sampleBit => none` and `| .sampleBv _ => none`, at
`CryptoToVIR.lean:86,118`) because "sampling isn't representable in the
pure-only VIR denotation".

The DR principle says we can lower them after all, *deterministically*, by
modelling a sample as **"read `w` entropy bits"** — a total, deterministic
leaf over an externally-supplied entropy source `η`. The probabilistic meaning
is then a *separate interpretation*: it is recovered later by pushing a uniform
distribution forward through this deterministic op (the "realization theorem",
left as the next step — see the module-end note).

Concretely this file provides:

1. `Entropy` — a deterministic infinite bit stream `Nat → Bool` with a read
   offset, plus `readBit`/`readBv`/`advance`.
2. `SampleTy` / `sampleDet` — a deterministic, **total** denotation of exactly
   the two sample leaves as entropy reads (`sampleBit ↦ readBit`,
   `sampleBv n ↦ readBv n`). Totality is by construction (it is a function),
   which is the honest content of "does not drop to `none`".
3. Correctness lemmas that a later uniform-entropy realization will use:
   determinism, the `readBv … 0 = 0#0` and `readBv` range bound
   (`(readBv η n).toNat < 2^n`), agreement of the leaf with the underlying
   reads, and a few `rfl`/`decide` computed examples.

Nothing here imports probability; `SPComp`/`SDistr` are untouched. This is the
deterministic counterpart of the drop-to-`none` arms, in its own file, with no
modification to the existing lowering.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.Rng

open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-! ## The entropy source -/

/-- A deterministic, infinite source of entropy bits, with a read offset.

    `bits i` is the `i`-th raw bit of the stream; `offset` is the number of
    bits already consumed, so the next read starts at `bits offset`.
    Reads are **total and deterministic** — there is no probability here; the
    randomness lives entirely in the (later-quantified) choice of `bits`. -/
structure Entropy where
  /-- The raw, infinite bit stream. -/
  bits : Nat → Bool
  /-- Number of bits already consumed; the next read starts at `bits offset`. -/
  offset : Nat := 0

namespace Entropy

/-- The bit that the next read will consume (without advancing). -/
@[simp] def head (η : Entropy) : Bool := η.bits η.offset

/-- Advance the read offset by `k` bits (deterministic; pure bookkeeping). -/
def advance (η : Entropy) (k : Nat) : Entropy :=
  { η with offset := η.offset + k }

@[simp] theorem advance_bits (η : Entropy) (k : Nat) :
    (η.advance k).bits = η.bits := rfl

@[simp] theorem advance_offset (η : Entropy) (k : Nat) :
    (η.advance k).offset = η.offset + k := rfl

@[simp] theorem advance_zero (η : Entropy) : η.advance 0 = η := by
  cases η; simp [advance]

theorem advance_advance (η : Entropy) (j k : Nat) :
    (η.advance j).advance k = η.advance (j + k) := by
  cases η; simp [advance, Nat.add_assoc]

/-- Read a single entropy bit (the head of the stream). Deterministic, total. -/
@[simp] def readBit (η : Entropy) : Bool := η.head

/-- Read `n` entropy bits, packing bit `i` (taken from `bits (offset + i)`)
    into bit position `i` of the resulting `BitVec n`.  Total by construction:
    every `BitVec n` value is well-defined, so this never "drops to `none`". -/
def readBv (η : Entropy) (n : Nat) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : Fin n => η.bits (η.offset + i)))).cast (by simp)

@[simp] theorem readBv_getLsb (η : Entropy) (n : Nat) (i : Fin n) :
    (η.readBv n).getLsbD i = η.bits (η.offset + i) := by
  simp only [readBv, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem?_getD]
  simp

/-- Reading zero bits yields the empty bitvector. -/
@[simp] theorem readBv_zero (η : Entropy) : η.readBv 0 = 0#0 :=
  Subsingleton.elim _ _

/-- **Range correctness.**  A length-`n` entropy read is a genuine `n`-bit word,
    so its natural-number value is `< 2^n`.  This is the seam a later uniform-
    entropy realization uses to match the support of `SPComp.sample (BitVec n)`. -/
theorem readBv_toNat_lt (η : Entropy) (n : Nat) :
    (η.readBv n).toNat < 2 ^ n :=
  (η.readBv n).isLt

/-! ## Determinism

    Both reads are plain functions of `η`, hence deterministic: equal sources
    give equal reads.  We state this explicitly because it is exactly the
    property that distinguishes a *deterministic leaf* from the probabilistic
    `SPComp.sample`. -/

theorem readBit_deterministic {η₁ η₂ : Entropy} (h : η₁ = η₂) :
    η₁.readBit = η₂.readBit := by rw [h]

theorem readBv_deterministic {η₁ η₂ : Entropy} (h : η₁ = η₂) (n : Nat) :
    η₁.readBv n = η₂.readBv n := by rw [h]

/-- The single-bit read agrees with the length-1 read (modulo `BitVec`/`Bool`
    packing): the LSB of `readBv η 1` is exactly `readBit η`. -/
theorem readBit_eq_readBv_one (η : Entropy) :
    η.readBit = (η.readBv 1).getLsbD ((0 : Fin 1) : Nat) := by
  rw [readBv_getLsb]
  simp [readBit, head]

end Entropy

/-! ## The deterministic sample leaf

    `SampleTy` enumerates exactly the two CryptoSSA sampling leaves; `toCryptoTy`
    maps each to its result type so that the deterministic image lands in the
    SAME `CryptoTy.denote` as the probabilistic `CExpr.denote`. -/

/-- The result-shape of a sampling op: a single bit, or an `n`-bit word.
    These are precisely `CExpr.sampleBit` and `CExpr.sampleBv n`. -/
inductive SampleTy where
  /-- `CExpr.sampleBit`. -/
  | bit
  /-- `CExpr.sampleBv n`. -/
  | bv (n : Nat)
  deriving DecidableEq, Repr

/-- The CryptoSSA result type of a sampling op — matching the `CExpr` indices
    `CExpr Γ .bit` and `CExpr Γ (.sword n)`. -/
def SampleTy.toCryptoTy : SampleTy → CryptoTy
  | .bit => .bit
  | .bv n => .sword n

/-- **The deterministic entropy-read denotation of the sample leaves.**

    Total and deterministic: every `SampleTy` maps to a defined value in the
    same `CryptoTy.denote` that the probabilistic `CExpr.denote` targets
    (`Bool` for `.bit`, `BitVec n` for `.sword n`).  Contrast the pure lowering
    `toVIRExpr`, which sends both leaves to `none`.  Here there is no `none`:
    the function is total by construction. -/
def sampleDet (η : Entropy) : (s : SampleTy) → s.toCryptoTy.denote
  | .bit => η.readBit
  | .bv n => η.readBv n

@[simp] theorem sampleDet_bit (η : Entropy) :
    sampleDet η .bit = η.readBit := rfl

@[simp] theorem sampleDet_bv (η : Entropy) (n : Nat) :
    sampleDet η (.bv n) = η.readBv n := rfl

/-! ## Lowerability: the sample leaves have a total deterministic image

    The honest statement of "is lowerable / does not drop to `none`": for every
    entropy source and every sampling shape, `sampleDet` returns a value (it is
    total).  We phrase it via the `Option`-lowering twin to make the contrast
    with `toVIRExpr`'s `none` explicit. -/

/-- An `Option`-valued lowering of the sample leaves, mirroring the *shape* of
    `toVIRExpr` (which returns `Option …` and chooses `none`).  Here we always
    return `some (sampleDet …)` — i.e. the DR lowering never drops. -/
def lowerSample (η : Entropy) (s : SampleTy) : Option s.toCryptoTy.denote :=
  some (sampleDet η s)

/-- **Lowerability theorem.**  Unlike `toVIRExpr` — which sends `sampleBit` and
    `sampleBv _` to `none` (`CryptoToVIR.lean:86,118`) — the deterministic
    entropy lowering is defined on *both* sample shapes, for *every* source. -/
theorem lowerSample_isSome (η : Entropy) (s : SampleTy) :
    (lowerSample η s).isSome := rfl

/-- The defined value of `lowerSample` is exactly `sampleDet`. -/
@[simp] theorem lowerSample_eq_some (η : Entropy) (s : SampleTy) :
    lowerSample η s = some (sampleDet η s) := rfl

/-- Determinism of the leaf, inherited from the reads: equal sources lower to
    equal values. -/
theorem sampleDet_deterministic {η₁ η₂ : Entropy} (h : η₁ = η₂) (s : SampleTy) :
    sampleDet η₁ s = sampleDet η₂ s := by rw [h]

/-- The bit-vector sample lands in range — the support seam for a future
    uniform-entropy realization against `SPComp.sample (BitVec n)`. -/
theorem sampleDet_bv_toNat_lt (η : Entropy) (n : Nat) :
    (sampleDet η (.bv n)).toNat < 2 ^ n :=
  Entropy.readBv_toNat_lt η n

/-! ## Computed examples (sanity, by `rfl`/`decide`)

    A constant stream makes the deterministic reads computable; we check a few
    values to pin down the bit-packing convention. -/

/-- The all-ones constant stream. -/
def onesη : Entropy := { bits := fun _ => true }

/-- The all-zeros constant stream. -/
def zerosη : Entropy := { bits := fun _ => false }

/-- A small alternating stream: bit `i` is `true` iff `i` is even. -/
def altη : Entropy := { bits := fun i => i % 2 == 0 }

example : onesη.readBit = true := rfl
example : zerosη.readBit = false := rfl
example : altη.readBit = true := rfl

example : onesη.readBv 4 = 15#4 := by decide
example : zerosη.readBv 4 = 0#4 := by decide
example : (sampleDet onesη (.bv 8)).toNat = 255 := by decide
example : sampleDet zerosη .bit = false := rfl

/-- Range bound, checked concretely against the all-ones stream. -/
example : (sampleDet onesη (.bv 8)).toNat < 2 ^ 8 := by decide

/-- Reading more bits then advancing is consistent with the offset bookkeeping:
    after advancing past the first bit, the head is the original second bit. -/
example : (altη.advance 1).readBit = (altη.bits 1) := rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.Rng
