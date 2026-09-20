/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.PolyLowering
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-!
# `polyDialect` → `fieldDialect` per-coefficient lowering

`polyDialect` (`VIR/PolyDialect.lean`) has two value types, `polyC q n` and
`polyN q n`, denoting `CPolynomial (ZMod q)` and `Array (ZMod q)`.  Every
`fieldDialect` type (`VIR/FieldDialect.lean`) denotes a single field element or a
fixed-arity extension-tower value; the dialect has no array type, no index type
and no memory op.  A polynomial therefore has no single `fieldDialect` type, and
the 1:1 `mapTy` frameworks (`ComParametricityTransport.LoweringData`,
`FieldDialectBlockDescent.BlockLoweringData`) do not apply.

The representation used here is the one `EcConvertToFieldLowering` uses for
coordinate tuples: a `polyC q n` value is carried on the field side as its
coefficients `p.coeff k`, each an `fp q` binding, and a `polyN q n` value as its
lane entries `a.getD i 0`.  A polynomial op lowers to a lane program — a
`Com fieldDialect` schedule over the lanes it reads — applied once per output
index.  The coefficient-wise ops read lane `k` of each input, so a single lane
program serves every index.

## Main definitions

* `Γlane2`, `Γlane1` — the lane input contexts `[fp q, fp q]` and `[fp q]`.
* `laneVal2`, `laneVal1` — their valuations.
* `fpDenote` — a schedule's denotation at type `ZMod q`.
* `addLaneProg`, `subLaneProg`, `mulLaneProg` — the one-op lane schedules
  `fAdd`, `fSub`, `fMul`.
* `smulLaneProg` — the two-op scalar lane schedule `fConst c` then `fMul`.
* `Γbf`, `bfVal` — the butterfly input context `[fp q, fp q, fp q]` carrying
  `(ζ, a, b)`, and its valuation.
* `bfHiProg`, `bfLoProg` — the two output schedules of one Cooley–Tukey
  butterfly, `fMul` then `fAdd` / `fSub`.

## Main results

* `polyAdd_lane_denote`, `polySub_lane_denote`, `polySMul_lane_denote` — each
  coefficient-wise `polyDialect` op's denotation has `k`-th coefficient equal to
  the lane schedule run on the `k`-th coefficients of its inputs.
* `basemul_lane_denote` — the `basemul` denotation has `i`-th lane equal to
  `mulLaneProg` run on the `i`-th lanes of its inputs, for `i` below the NTT
  domain size.
* `basemul_size` — the `basemul` denotation has size `(ND.dom q).n`, the NTT
  domain size rather than the ring degree `n`.
* `bfHi_denote`, `bfLo_denote` — the butterfly schedules denote to the two
  components of `PolyLowering.ctButterfly`.
* `butterflyInnerStep_hi`, `butterflyInnerStep_lo` — the two array entries one
  CompPoly butterfly step writes equal the denotations of the two butterfly
  schedules on the entries it reads.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.PolyToField

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSemantic (NttDomains)
open CompPoly.CPolynomial.NTT (Domain)
open CompPoly.CPolynomial.NTT.Transform (butterflyInnerStep)
open CompPoly (CPolynomial)

variable {q n : Nat}

/-! ## 1. Lane contexts

A lane of a `polyC`/`polyN` value is a single `ZMod q`, so its field-side type is
`FieldTy.fp q`.  A binary coefficient-wise op reads one lane from each operand. -/

/-- The two-lane input context: one coefficient from each operand. -/
abbrev Γlane2 (q : Nat) : Ctxt fieldDialect := [FieldTy.fp q, FieldTy.fp q]

/-- The one-lane input context. -/
abbrev Γlane1 (q : Nat) : Ctxt fieldDialect := [FieldTy.fp q]

/-- The valuation `⟨a, b⟩` of `Γlane2`. -/
def laneVal2 (a b : ZMod q) : Ctxt.Valuation (Γlane2 q) := .cons a (.cons b .nil)

/-- The valuation `⟨a⟩` of `Γlane1`. -/
def laneVal1 (a : ZMod q) : Ctxt.Valuation (Γlane1 q) := .cons a .nil

/-- The denotation of a `Com fieldDialect` schedule ending in `fp q`, at type
    `ZMod q`.  `⟦FieldTy.fp q⟧` reduces to `ZMod q` for unification but not for
    instance search, so field arithmetic on a schedule's denotation is stated
    through this projection. -/
def fpDenote {Γ : Ctxt fieldDialect} (c : Com fieldDialect Γ (FieldTy.fp q))
    (V : Ctxt.Valuation Γ) : ZMod q := c.denote V

/-! ## 2. The lane schedules -/

/-- The lane schedule of `polyAdd`: one `fAdd` on the two input coefficients. -/
def addLaneProg : Com fieldDialect (Γlane2 q) (FieldTy.fp q) :=
  .var (.mk (.fAdd q) rfl (.cons .here (.cons (.there .here) .nil))) (.ret .here)

/-- The lane schedule of `polySub`: one `fSub` on the two input coefficients. -/
def subLaneProg : Com fieldDialect (Γlane2 q) (FieldTy.fp q) :=
  .var (.mk (.fSub q) rfl (.cons .here (.cons (.there .here) .nil))) (.ret .here)

/-- The lane schedule of `basemul`: one `fMul` on the two input lanes. -/
def mulLaneProg : Com fieldDialect (Γlane2 q) (FieldTy.fp q) :=
  .var (.mk (.fMul q) rfl (.cons .here (.cons (.there .here) .nil))) (.ret .here)

/-- The lane schedule of `polySMul c`: the scalar as an `fConst`, then one
    `fMul` against the input coefficient. -/
def smulLaneProg (c : ZMod q) : Com fieldDialect (Γlane1 q) (FieldTy.fp q) :=
  .var (.mk (.fConst q c) rfl .nil)
    (.var (.mk (.fMul q) rfl (.cons .here (.cons (.there .here) .nil)))
      (.ret .here))

/-! ## 3. Lane-schedule denotations -/

/-- `addLaneProg` denotes to the sum of its two lanes. -/
theorem addLane_denote (a b : ZMod q) :
    (addLaneProg (q := q)).denote (laneVal2 a b) = a + b := rfl

/-- `subLaneProg` denotes to the difference of its two lanes. -/
theorem subLane_denote (a b : ZMod q) :
    (subLaneProg (q := q)).denote (laneVal2 a b) = a - b := rfl

/-- `mulLaneProg` denotes to the product of its two lanes. -/
theorem mulLane_denote (a b : ZMod q) :
    (mulLaneProg (q := q)).denote (laneVal2 a b) = a * b := rfl

/-- `smulLaneProg c` denotes to `c` times its lane. -/
theorem smulLane_denote (c a : ZMod q) :
    (smulLaneProg c).denote (laneVal1 a) = c * a := rfl

/-! ## 4. Coefficient-wise ops

For each coefficient-wise `polyDialect` op, the `k`-th coefficient of its
denotation is the lane schedule run on the `k`-th coefficients of the operands.
The `polyC` denotation is `CPolynomial (ZMod q)`, whose `coeff` is additive and
subtractive, so each statement is the corresponding `CPolynomial` coefficient
lemma composed with the lane denotation. -/

section PolyOps

variable [NttDomains]

/-- The `k`-th coefficient of the `polyAdd` denotation is `addLaneProg` on the
    `k`-th coefficients of the operands. -/
theorem polyAdd_lane_denote (p r : CPolynomial (ZMod q)) (k : Nat) :
    (polyDenote.denote (.polyAdd q n) (.cons p (.cons r .nil))).coeff k
      = (addLaneProg (q := q)).denote (laneVal2 (p.coeff k) (r.coeff k)) := by
  rw [polyAdd_denote (q := q) (n := n) p r, addLane_denote]
  exact CPolynomial.coeff_add p r k

/-- The `k`-th coefficient of the `polySub` denotation is `subLaneProg` on the
    `k`-th coefficients of the operands. -/
theorem polySub_lane_denote (p r : CPolynomial (ZMod q)) (k : Nat) :
    (polyDenote.denote (.polySub q n) (.cons p (.cons r .nil))).coeff k
      = (subLaneProg (q := q)).denote (laneVal2 (p.coeff k) (r.coeff k)) := by
  rw [polySub_denote (q := q) (n := n) p r, subLane_denote]
  exact CPolynomial.coeff_sub p r k

/-- The `k`-th coefficient of the `polySMul c` denotation is `smulLaneProg c` on
    the `k`-th coefficient of the operand.  `Fact (1 < q)` supplies
    `Nontrivial (ZMod q)`, which `CPolynomial.coeff_C_mul` requires. -/
theorem polySMul_lane_denote [Fact (1 < q)] (c : ZMod q) (p : CPolynomial (ZMod q)) (k : Nat) :
    (polyDenote.denote (.polySMul q n c) (.cons p .nil)).coeff k
      = (smulLaneProg c).denote (laneVal1 (p.coeff k)) := by
  rw [polySMul_denote (q := q) (n := n) c p, smulLane_denote]
  exact CPolynomial.coeff_C_mul p c k

/-! ## 5. `basemul`

`basemul` denotes to `realBasemul`, which is CompPoly's `pointwiseMul`: an
`Array.ofFn` over the NTT domain index `Fin (ND.dom q).n`, whose `i`-th entry is
the product of the `i`-th entries of the operands.  The lane count is therefore
the NTT domain size `(ND.dom q).n`, not the ring degree `n`; on ML-KEM-768 with
the 512-point domain the op writes 512 lanes for a degree-256 ring. -/

/-- The `basemul` denotation has size `(ND.dom q).n`, the NTT domain size. -/
theorem basemul_size [Fact (Nat.Prime q)] (a b : Array (ZMod q)) :
    (polyDenote.denote (.basemul q n) (.cons a (.cons b .nil))).size = (NttDomains.dom q).n := by
  show (if h : Nat.Prime q then
          (haveI : Fact (Nat.Prime q) := ⟨h⟩
           basemulF (NttDomains.dom q) a b)
        else (#[] : Array (ZMod q))).size = (NttDomains.dom q).n
  rw [dif_pos (Fact.out : Nat.Prime q)]
  simp [basemulF, realBasemul]

/-- The `i`-th lane of the `basemul` denotation is `mulLaneProg` on the `i`-th
    lanes of the operands, for `i` below the NTT domain size. -/
theorem basemul_lane_denote [Fact (Nat.Prime q)] (a b : Array (ZMod q))
    {i : Nat} (hi : i < (NttDomains.dom q).n) :
    (polyDenote.denote (.basemul q n) (.cons a (.cons b .nil))).getD i 0
      = (mulLaneProg (q := q)).denote (laneVal2 (a.getD i 0) (b.getD i 0)) := by
  rw [mulLane_denote]
  show (if h : Nat.Prime q then
          (haveI : Fact (Nat.Prime q) := ⟨h⟩
           basemulF (NttDomains.dom q) a b)
        else (#[] : Array (ZMod q))).getD i 0 = a.getD i 0 * b.getD i 0
  rw [dif_pos (Fact.out : Nat.Prime q)]
  have hsize : i < (basemulF (NttDomains.dom q) a b).size := by
    simpa [basemulF, realBasemul] using hi
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsize]
  simp [basemulF, realBasemul, CompPoly.CPolynomial.NTT.FastMul.pointwiseMul,
    Array.getD_eq_getD_getElem?]

end PolyOps

/-! ## 6. The Cooley–Tukey butterfly as a field schedule

One radix-2 butterfly `(a, b) ↦ (a + ζ·b, a − ζ·b)` is two `Com fieldDialect`
schedules over the context `(ζ, a, b)`, sharing the twiddle product as their
first binding.  `PolyLowering.ctButterfly` is the same map at the `ZMod q`
level. -/

/-- The butterfly input context: the twiddle `ζ` and the two lanes `a`, `b`. -/
abbrev Γbf (q : Nat) : Ctxt fieldDialect := [FieldTy.fp q, FieldTy.fp q, FieldTy.fp q]

/-- The valuation `⟨ζ, a, b⟩` of `Γbf`. -/
def bfVal (z a b : ZMod q) : Ctxt.Valuation (Γbf q) := .cons z (.cons a (.cons b .nil))

/-- The high output of one butterfly: `t = fMul ζ b`, then `fAdd a t`. -/
def bfHiProg : Com fieldDialect (Γbf q) (FieldTy.fp q) :=
  .var (.mk (.fMul q) rfl (.cons .here (.cons (.there (.there .here)) .nil)))
    (.var (.mk (.fAdd q) rfl (.cons (.there (.there .here)) (.cons .here .nil)))
      (.ret .here))

/-- The low output of one butterfly: `t = fMul ζ b`, then `fSub a t`. -/
def bfLoProg : Com fieldDialect (Γbf q) (FieldTy.fp q) :=
  .var (.mk (.fMul q) rfl (.cons .here (.cons (.there (.there .here)) .nil)))
    (.var (.mk (.fSub q) rfl (.cons (.there (.there .here)) (.cons .here .nil)))
      (.ret .here))

/-- `bfHiProg` denotes to the first component of `ctButterfly`. -/
theorem bfHi_denote (z a b : ZMod q) :
    (bfHiProg (q := q)).denote (bfVal z a b) = (ctButterfly z a b).1 := rfl

/-- `bfLoProg` denotes to the second component of `ctButterfly`. -/
theorem bfLo_denote (z a b : ZMod q) :
    (bfLoProg (q := q)).denote (bfVal z a b) = (ctButterfly z a b).2 := rfl

/-! ## 7. The schedules against CompPoly's butterfly step

`CompPoly.CPolynomial.NTT.Transform.butterflyInnerStep` is the step the forward
NTT (`forwardImpl = runStages ∘ bitRevPermute`) iterates.  It reads the entries
at `i0 = block·blockSize + j` and `i1 = i0 + half` and writes `u + w·b` at `i0`
and `u − w·b` at `i1`.  Those two written entries are the denotations of the two
butterfly schedules on the entries it read.  `Fact (Nat.Prime q)` supplies the
`Field (ZMod q)` instance `butterflyInnerStep` is stated over. -/

variable [Fact (Nat.Prime q)]

/-- The entry `butterflyInnerStep` writes at `i0` is `bfHiProg` on the entries it
    reads. -/
theorem butterflyInnerStep_hi (blockSize half : Nat) (wm w : ZMod q) (block j : Nat)
    (acc : Array (ZMod q)) (hhalf : 0 < half)
    (h0 : block * blockSize + j < acc.size) :
    (butterflyInnerStep blockSize half wm block j (acc, w)).1.getD
        (block * blockSize + j) 0
      = (bfHiProg (q := q)).denote
          (bfVal w (acc.getD (block * blockSize + j) 0)
                   (acc.getD (block * blockSize + j + half) 0)) := by
  rw [bfHi_denote]
  have hne : block * blockSize + j + half ≠ block * blockSize + j := by omega
  simp only [butterflyInnerStep, Array.set!_eq_setIfInBounds]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hne,
    Array.getElem?_setIfInBounds_self_of_lt h0]
  simp [ctButterfly, Array.getD_eq_getD_getElem?]

/-- The entry `butterflyInnerStep` writes at `i1 = i0 + half` is `bfLoProg` on
    the entries it reads. -/
theorem butterflyInnerStep_lo (blockSize half : Nat) (wm w : ZMod q) (block j : Nat)
    (acc : Array (ZMod q))
    (h1 : block * blockSize + j + half < acc.size) :
    (butterflyInnerStep blockSize half wm block j (acc, w)).1.getD
        (block * blockSize + j + half) 0
      = (bfLoProg (q := q)).denote
          (bfVal w (acc.getD (block * blockSize + j) 0)
                   (acc.getD (block * blockSize + j + half) 0)) := by
  rw [bfLo_denote]
  simp only [butterflyInnerStep, Array.set!_eq_setIfInBounds]
  rw [Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_self_of_lt (by simpa using h1)]
  simp [ctButterfly, Array.getD_eq_getD_getElem?]

end CatCrypt.Crypto.SecureCompilation.VIR.PolyToField
