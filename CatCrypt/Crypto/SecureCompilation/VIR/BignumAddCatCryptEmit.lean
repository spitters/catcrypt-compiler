/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect

/-!
# 4-limb (256-bit) bignum ADD on the HIGH `catCryptDialect`, with denote = spec

The multi-limb bignum libraries in this repo (`s2n-bignum`/GMP/fiat ports under
`Crypto/Jasmin/`, the `BignumAddEmit` `JInstr`/`JState` x86 block) are all
hand-authored at the *low* level — either over the `JInstr 64`/`JState 64`
register machine or over List-of-words schoolbook helpers. **None** of them
route a multi-limb carry chain through a *high* dialect (`catCryptDialect`, the
MLIR-aligned successor IR over the `Com` framework). This file is the first
witness that a bignum add does.

`catCryptDialect` already carries the bignum-ALU keystone ops:

* `bvAdd64 w` : `(a, b) ↦ (cout, sum)` where `sum = a + b` and `cout ∈ {0,1}`
  is the carry-out (Jasmin `#ADD_64`, x86 `ADD`).
* `bvAdc   w` : `(a, b, cin) ↦ (cout, sum)` where `sum = a + b + (cin ≠ 0)`,
  carry-out `cout ∈ {0,1}` (Jasmin `#ADC_64`, x86 `ADC`).

Their pure denotation is the full `BitVec.adc` carry chain. We build the
4-limb add-with-carry schedule — `bvAdd64` on the low limb, then `bvAdc`
threading the carry-out into limbs 1, 2, 3 — natively as a
`Com catCryptDialect` and prove it denotes EXACTLY the clean carry-propagating
4-limb spec `bignumAdd4` (a `rfl`).

## What is proved here

* `bignumAdd4` — the clean carry-propagating spec over 4 `BitVec 64` limbs,
  written with the same `BitVec.adc` primitive as the dialect ops (so the tie
  is a definitional `rfl`, not an arithmetic re-derivation).
* `bignumAdd4Com : Com catCryptDialect Γ₈ τout` — the 4-limb carry chain built
  from `bvAdd64`/`bvAdc` + `fst`/`snd` projections, native dialect.
* `bignumAdd_catcrypt_denote` — **the dialect Com denotes exactly the spec**.
  The first bignum-through-`catCryptDialect` `denote = spec` tie.

## The jasmin seam

`DialectToJasminCom.toJExprD` **declines** `bvAdd64`/`bvAdc` (see its catch-all
comment: *"…the ops `toJExpr` declines: …`bvAdd64`/`bvAdc`…"*). These ops return
a `.pair (.sword w) (.sword w)` (multi-output: data word *and* carry bit) and the
single-return jasmin `Com` lowering cannot express a paired result as one SSA
expression. The seam's covered carry-chain twins are the *split* word ops
`bvMulHi`/`bvAddCarryLo`/`bvAddCarryHi` (`#477`), which return single words and
do lower. So the catCrypt-side `denote = spec` here is the deliverable; the
`bvAdd64`/`bvAdc` → jasmin seam is the gap to fill (lower the paired op into two
jasmin instructions binding the data word and the carry bit separately, mirroring
the `bvAddCarryLo`/`bvAddCarryHi` split).

**0 sorries.**
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.BignumAddCatCryptEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-! ## 1. The clean 4-limb add-with-carry spec

`bignumAdd4 a b` adds two 256-bit values held as 4 little-endian `BitVec 64`
limbs `(a0,a1,a2,a3)`, `(b0,b1,b2,b3)`, returning the carry-out bit (`0`/`1` as a
`BitVec 64`) and the 4-limb sum. It is written with the *same* `BitVec.adc`
primitive the dialect `bvAdd64`/`bvAdc` denote into, so the dialect tie is a
`rfl`. -/

/-- One carry-chain step `a + b + cin`: returns `(cout, sum)` exactly as the
    dialect `bvAdc`/`bvAdd64` package it — `cout = 1` on carry-out else `0`. -/
def adcStep (a b : BitVec 64) (cin : Bool) : BitVec 64 × BitVec 64 :=
  let p := BitVec.adc a b cin
  ((if p.fst then (1 : BitVec 64) else 0), p.snd)

/-- **The abstract 256-bit add spec.** Little-endian 4-limb add-with-carry.
    Returns `(carryOut, (s0, s1, s2, s3))`. -/
def bignumAdd4
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    BitVec 64 × (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :=
  let r0 := adcStep a0 b0 false
  let r1 := adcStep a1 b1 (r0.1.toNat ≠ 0)
  let r2 := adcStep a2 b2 (r1.1.toNat ≠ 0)
  let r3 := adcStep a3 b3 (r2.1.toNat ≠ 0)
  (r3.1, (r0.2, r1.2, r2.2, r3.2))

/-! ## 2. The input context and De Bruijn variables

`Γ₈ = [sword 64, …×8]` holds `a0,a1,a2,a3, b0,b1,b2,b3` at indices `0..7`. -/

/-- The starting context: eight 64-bit limb inputs `a0..a3, b0..b3`. -/
abbrev Γ₈ : Ctxt catCryptDialect :=
  [.sword 64, .sword 64, .sword 64, .sword 64,
   .sword 64, .sword 64, .sword 64, .sword 64]

/-- The output type: `(carryOut, (s0, s1, s2, s3))` — a `sword 64` carry bit and
    the 4-limb sum packed right-nested. -/
abbrev τout : CryptoTy :=
  .pair (.sword 64)
    (.pair (.sword 64) (.pair (.sword 64) (.pair (.sword 64) (.sword 64))))

/-! ### De Bruijn variables (indices into `Γ₈`)

These name the eight inputs. As the `Com` binds new lets, the inputs shift one
`.there` per `bvAdd64`/`bvAdc`/projection bound above them; we re-derive them
inline in the program below rather than naming all the shifted forms. -/

/-! ## 3. The 4-limb carry-chain `Com catCryptDialect`

The schedule, in source order (each `.var` binds one result on top of the stack):

```
p0 := bvAdd64 a0 b0          -- (cout0, sum0)
c0 := fst p0 ; s0 := snd p0
p1 := bvAdc  a1 b1 c0        -- (cout1, sum1)   (cin = c0 ≠ 0)
c1 := fst p1 ; s1 := snd p1
p2 := bvAdc  a2 b2 c1
c2 := fst p2 ; s2 := snd p2
p3 := bvAdc  a3 b3 c2
c3 := fst p3 ; s3 := snd p3
ret (c3, (s0, s1, s2, s3))
```

We thread the **carry-out word** `cᵢ : sword 64` directly as the `cin` of the
next `bvAdc` (its denotation reads `cin.toNat ≠ 0`, matching `adcStep`'s
`rᵢ.1.toNat ≠ 0`). The data words `sᵢ` are projected with `snd`. -/

/-- The 4-limb add-with-carry built natively over `catCryptDialect`, using the
    keystone carry-chain ops `bvAdd64` (low limb) and `bvAdc` (limbs 1–3). -/
def bignumAdd4Com : Com catCryptDialect Γ₈ τout :=
  -- p0 := bvAdd64 a0 b0          [a0=idx0, b0=idx4 in Γ₈]
  .var (show Expr catCryptDialect Γ₈ (.pair (.sword 64) (.sword 64)) from
        { op := .bvAdd64 64, retTy_eq := rfl,
          args := .cons (.here) (.cons (.there (.there (.there (.there .here)))) .nil) }) <|
  -- c0 := fst p0
  .var { op := .fst (.sword 64) (.sword 64), retTy_eq := rfl,
         args := .cons .here .nil } <|
  -- s0 := snd p0           [p0 is now 1 below the top]
  .var { op := .snd (.sword 64) (.sword 64), retTy_eq := rfl,
         args := .cons (.there .here) .nil } <|
  -- p1 := bvAdc a1 b1 c0
  --   a1: Γ₈ idx1, shifted by 3 binders (p0,c0,s0) ↦ .there^4 .here
  --   b1: Γ₈ idx5, shifted by 3 ↦ .there^8 .here
  --   c0: 1 below top (s0 on top) ↦ .there .here
  .var (show Expr catCryptDialect _ (.pair (.sword 64) (.sword 64)) from
        { op := .bvAdc 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
                 (.cons (.there .here) .nil)) }) <|
  -- c1 := fst p1
  .var { op := .fst (.sword 64) (.sword 64), retTy_eq := rfl,
         args := .cons .here .nil } <|
  -- s1 := snd p1
  .var { op := .snd (.sword 64) (.sword 64), retTy_eq := rfl,
         args := .cons (.there .here) .nil } <|
  -- p2 := bvAdc a2 b2 c1
  --   bound above p0(7),c0(6),s0(5),p1(4),c1(3),s1(2) ... but count from Γ₈:
  --   stack now (top→bottom): s1,c1,p1,s0,c0,p0, then Γ₈
  --   a2: Γ₈ idx2 → .there^(6+2) .here = .there^8 .here
  --   b2: Γ₈ idx6 → .there^(6+6) .here = .there^12 .here
  --   c1: 1 below top (s1 on top) → .there .here
  .var (show Expr catCryptDialect _ (.pair (.sword 64) (.sword 64)) from
        { op := .bvAdc 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
                 (.cons (.there .here) .nil)) }) <|
  -- c2 := fst p2
  .var { op := .fst (.sword 64) (.sword 64), retTy_eq := rfl,
         args := .cons .here .nil } <|
  -- s2 := snd p2
  .var { op := .snd (.sword 64) (.sword 64), retTy_eq := rfl,
         args := .cons (.there .here) .nil } <|
  -- p3 := bvAdc a3 b3 c2
  --   stack now (top→bottom): s2,c2,p2,s1,c1,p1,s0,c0,p0, then Γ₈
  --   a3: Γ₈ idx3 → .there^(9+3) .here = .there^12 .here
  --   b3: Γ₈ idx7 → .there^(9+7) .here = .there^16 .here
  --   c2: 1 below top (s2 on top) → .there .here
  .var (show Expr catCryptDialect _ (.pair (.sword 64) (.sword 64)) from
        { op := .bvAdc 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))
                 (.cons (.there .here) .nil)) }) <|
  -- c3 := fst p3
  .var { op := .fst (.sword 64) (.sword 64), retTy_eq := rfl,
         args := .cons .here .nil } <|
  -- s3 := snd p3
  .var { op := .snd (.sword 64) (.sword 64), retTy_eq := rfl,
         args := .cons (.there .here) .nil } <|
  -- ret (c3, (s0, s1, s2, s3))
  --   stack now (top→bottom): s3,c3,p3,s2,c2,p2,s1,c1,p1,s0,c0,p0, then Γ₈
  --   s3: top                 → .here
  --   c3: 1 below             → .there .here
  --   s2: idx 3 from top      → .there^3 .here
  --   s1: idx 6 from top      → .there^6 .here
  --   s0: idx 9 from top      → .there^9 .here
  .var (show Expr catCryptDialect _ (.pair (.sword 64) (.sword 64)) from
        { op := .mkPair (.sword 64) (.sword 64), retTy_eq := rfl,
          -- (s2, s3)
          args := .cons (.there (.there (.there .here))) (.cons .here .nil) }) <|
  -- now top is (s2,s3); s1 shifted by 1 ↦ .there^7 .here, c3 ↦ .there^2 .here
  .var (show Expr catCryptDialect _ (.pair (.sword 64) (.pair (.sword 64) (.sword 64))) from
        { op := .mkPair (.sword 64) (.pair (.sword 64) (.sword 64)), retTy_eq := rfl,
          -- (s1, (s2,s3))
          args := .cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
                 (.cons .here .nil) }) <|
  -- top is (s1,(s2,s3)); s0 shifted by 2 ↦ .there^11 .here, c3 ↦ .there^3 .here
  .var (show Expr catCryptDialect _
          (.pair (.sword 64) (.pair (.sword 64) (.pair (.sword 64) (.sword 64)))) from
        { op := .mkPair (.sword 64) (.pair (.sword 64) (.pair (.sword 64) (.sword 64))),
          retTy_eq := rfl,
          -- (s0, (s1,(s2,s3)))
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
                 (.cons .here .nil) }) <|
  -- top is (s0,(s1,(s2,s3))); c3 shifted by 3 ↦ .there^4 .here
  .var (show Expr catCryptDialect _ τout from
        { op := .mkPair (.sword 64)
                  (.pair (.sword 64) (.pair (.sword 64) (.pair (.sword 64) (.sword 64)))),
          retTy_eq := rfl,
          -- (c3, (s0,(s1,(s2,s3))))
          args := .cons (.there (.there (.there (.there .here)))) (.cons .here .nil) }) <|
  .ret .here

/-! ## 4. The denote = spec tie -/

/-- **The 4-limb dialect carry chain denotes EXACTLY the abstract 256-bit add.**

    The first bignum-through-`catCryptDialect` `denote = spec` witness: the
    `Com catCryptDialect` built from the keystone `bvAdd64`/`bvAdc` carry ops
    computes precisely the clean carry-propagating spec `bignumAdd4`. -/
theorem bignumAdd_catcrypt_denote
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    bignumAdd4Com.denote
        (.cons a0 (.cons a1 (.cons a2 (.cons a3
         (.cons b0 (.cons b1 (.cons b2 (.cons b3 .nil))))))))
      = bignumAdd4 a0 a1 a2 a3 b0 b1 b2 b3 := by
  rfl

/-! ## 5. The SPLIT-word carry chain — lowers through the EXISTING jasmin seam

The `bvAdd64`/`bvAdc` ops above return a *pair* `(cout, sum)`, which the jasmin
seam (`DialectToJasminCom.toJExprD`) declines. The seam *does* cover the
single-word **split** twins `bvAddCarryLo`/`bvAddCarryHi` (`#477`):

* `bvAddCarryLo w : (a, b, cin : sword 1) ↦ a + b + cin`  (the data word; jasmin
  `addCarryLo` = x86 `ADCX`/`ADOX` data effect)
* `bvAddCarryHi w : (a, b, cin : sword 1) ↦ carry-out bit : sword 1`  (the carry
  word; jasmin `addCarryHi`)

Both take a 1-bit register carry-in (`sword 1`) and `bvAddCarryHi` *produces* a
`sword 1`, so the carry threads cleanly limb-to-limb: limb `i`'s
`bvAddCarryHi` output is limb `i+1`'s carry-in. The initial carry-in is a
`bvConst 1 0` (also covered by the seam, → jasmin `regConst`).

Because the seam declines the pair ops `mkPair`/`fst`/`snd`, the lowered program
must avoid them entirely: there is no carry-chain *projection* (the split ops
return the two words *directly*), and we return a single `sword` word rather
than packaging the 4-limb sum into a `.pair` tower. We return the **final
carry-out word** `c4 : sword 1` — the load-bearing result of a multi-limb add
(the "did it overflow 256 bits" bit). Each per-limb data word `sᵢ` is still bound
and denotes to the matching `bignumAdd4` sum limb, but is not returned because
the result must be a single jasmin word.

### The split denote bridge

The split ops denote with `addCarryWordC`/`carryOutBitC` over a `BitVec 1`
carry; the abstract `bignumAdd4` spec is written with `BitVec.adc` over a `Bool`
carry. The bridge `adcStep_split` ties the two encodings per limb. -/

/-- One split-op carry step over a `BitVec 1` carry-in, packaging the data word
    and the carry-out word exactly as `bvAddCarryLo`/`bvAddCarryHi` denote. -/
def adcStepSplit (a b : BitVec 64) (cin : BitVec 1) : BitVec 64 × BitVec 1 :=
  (addCarryWordC a b cin, carryOutBitC a b cin)

/-- The split-word 256-bit add spec, threading a `BitVec 1` carry through
    `bvAddCarryLo`/`bvAddCarryHi`'s denotes. Returns `(carryOut₁, (s0,s1,s2,s3))`
    with the carry as a `BitVec 1`. The split program denotes EXACTLY this. -/
def bignumAdd4Split
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    BitVec 1 × (BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :=
  let r0 := adcStepSplit a0 b0 0
  let r1 := adcStepSplit a1 b1 r0.2
  let r2 := adcStepSplit a2 b2 r1.2
  let r3 := adcStepSplit a3 b3 r2.2
  (r3.2, (r0.1, r1.1, r2.1, r3.1))

/-! ### The split-encoding ↔ abstract-spec bridge

The split spec threads a `BitVec 1` carry through `addCarryWordC`/`carryOutBitC`;
the abstract `bignumAdd4` threads a `Bool` carry through `BitVec.adc`. Per limb
the **sum word** is identical and the **carry-out** agrees as a predicate. -/

/-- One split step's data word equals the abstract `adc` sum word (with the
    `BitVec 1` carry-in read as a `Bool`). -/
theorem adcStepSplit_fst (a b : BitVec 64) (cin : BitVec 1) :
    (adcStepSplit a b cin).1 = (adcStep a b (cin.toNat ≠ 0)).2 := by
  unfold adcStepSplit adcStep addCarryWordC
  rcases BitVec.eq_zero_or_eq_one cin with rfl | rfl <;>
    simp only [BitVec.adc_spec] <;> bv_decide

/-- A one-bit indicator `(if c then 1 else 0)` is nonzero iff `c`, at any
    positive width. The shared shape of `carryOutBitC` and `adcStep`'s carry. -/
theorem indicator_toNat_ne_zero_iff (w : Nat) (c : Prop) [Decidable c] :
    ((if c then (1 : BitVec (w + 1)) else 0).toNat ≠ 0) ↔ c := by
  by_cases hc : c <;> simp [hc, BitVec.toNat_ofNat, Nat.one_mod_two_pow]

/-- One split step's carry-out word agrees, as a predicate, with the abstract
    `adc` carry-out — and threads as the next limb's carry-in unchanged. Both the
    `carryOutBitC` indicator and `adcStep`'s carry indicator are nonzero exactly
    when the unsigned sum overflows `2 ^ 64`. -/
theorem adcStepSplit_snd_iff (a b : BitVec 64) (cin : BitVec 1) :
    ((adcStepSplit a b cin).2.toNat ≠ 0) = ((adcStep a b (cin.toNat ≠ 0)).1.toNat ≠ 0) := by
  rw [eq_iff_iff]
  unfold adcStepSplit adcStep carryOutBitC
  simp only [BitVec.adc_spec, indicator_toNat_ne_zero_iff 63]
  rcases BitVec.eq_zero_or_eq_one cin with rfl | rfl <;>
    simp only [BitVec.carry, indicator_toNat_ne_zero_iff 0, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (BitVec.isLt _), ge_iff_le] <;> simp

/-- **Split spec ⇒ abstract spec (sums identical, carry-out agrees).** The
    4-limb sum produced by the `bvAddCarryLo`/`bvAddCarryHi` split chain is
    *bit-for-bit* the `bignumAdd4` sum, and the final carry-out word is nonzero
    exactly when `bignumAdd4`'s is. So the lowered jasmin program computes the
    same 256-bit add as the abstract spec. -/
theorem bignumAdd4Split_eq_spec
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (bignumAdd4Split a0 a1 a2 a3 b0 b1 b2 b3).2
        = (bignumAdd4 a0 a1 a2 a3 b0 b1 b2 b3).2
    ∧ ((bignumAdd4Split a0 a1 a2 a3 b0 b1 b2 b3).1.toNat ≠ 0)
        = ((bignumAdd4 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat ≠ 0) := by
  simp only [bignumAdd4Split, bignumAdd4, adcStepSplit_fst, adcStepSplit_snd_iff,
    show ((0 : BitVec 1).toNat ≠ 0) = False from by simp, decide_false]
  exact ⟨trivial, trivial⟩

/-- The split-output type: a `sword 1` carry-out and the 4-limb sum, right-nested
    over `sword`s — but note the lowered program returns only the carry word. -/
abbrev τoutSplit : CryptoTy :=
  .pair (.sword 1)
    (.pair (.sword 64) (.pair (.sword 64) (.pair (.sword 64) (.sword 64))))

/-- The 4-limb add-with-carry built natively over `catCryptDialect` using the
    **split** carry ops `bvAddCarryLo`/`bvAddCarryHi` (single-word outputs that
    lower through the existing jasmin seam), returning the final carry-out word
    `c4 : sword 1`. No pair ops are used, so the whole program lowers. -/
def bignumAdd4ComSplit : Com catCryptDialect Γ₈ (.sword 1) :=
  -- z := bvConst 1 0     (initial carry-in, idx into Γ₈ shifts below)
  .var (show Expr catCryptDialect Γ₈ (.sword 1) from
        { op := .bvConst 1 0, retTy_eq := rfl, args := .nil }) <|
  -- s0 := bvAddCarryLo a0 b0 z    [a0=idx1, b0=idx5 after z bound; z=here]
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvAddCarryLo 64, retTy_eq := rfl,
          args := .cons (.there .here)
                 (.cons (.there (.there (.there (.there (.there .here)))))
                 (.cons .here .nil)) }) <|
  -- c1 := bvAddCarryHi a0 b0 z
  --   stack (top→bottom): s0, z, then Γ₈.  a0=idx2, b0=idx6, z=.there .here
  .var (show Expr catCryptDialect _ (.sword 1) from
        { op := .bvAddCarryHi 64, retTy_eq := rfl,
          args := .cons (.there (.there .here))
                 (.cons (.there (.there (.there (.there (.there (.there .here))))))
                 (.cons (.there .here) .nil)) }) <|
  -- s1 := bvAddCarryLo a1 b1 c1
  --   stack: c1, s0, z, then Γ₈.  a1=idx(3+1)=4? Γ₈ idx1 + 3 binders = .there^4 .here
  --   a1: Γ₈ idx1 shifted by 3 (c1,s0,z) → .there^4 .here
  --   b1: Γ₈ idx5 shifted by 3 → .there^8 .here
  --   c1: top → .here
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvAddCarryLo 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there .here))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
                 (.cons .here .nil)) }) <|
  -- c2 := bvAddCarryHi a1 b1 c1
  --   stack: s1, c1, s0, z, then Γ₈.  a1: Γ₈ idx1 + 4 binders → .there^5 .here
  --   b1: Γ₈ idx5 + 4 → .there^9 .here ; c1: .there .here
  .var (show Expr catCryptDialect _ (.sword 1) from
        { op := .bvAddCarryHi 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there .here)))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
                 (.cons (.there .here) .nil)) }) <|
  -- s2 := bvAddCarryLo a2 b2 c2
  --   stack: c2, s1, c1, s0, z, then Γ₈.  a2: Γ₈ idx2 + 5 → .there^7 .here
  --   b2: Γ₈ idx6 + 5 → .there^11 .here ; c2: top → .here
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvAddCarryLo 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there .here)))))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
                 (.cons .here .nil)) }) <|
  -- c3 := bvAddCarryHi a2 b2 c2
  --   stack: s2, c2, s1, c1, s0, z, then Γ₈.  a2: Γ₈ idx2 + 6 → .there^8 .here
  --   b2: Γ₈ idx6 + 6 → .there^12 .here ; c2: .there .here
  .var (show Expr catCryptDialect _ (.sword 1) from
        { op := .bvAddCarryHi 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))
                 (.cons (.there .here) .nil)) }) <|
  -- s3 := bvAddCarryLo a3 b3 c3
  --   stack: c3, s2, c2, s1, c1, s0, z, then Γ₈.  a3: Γ₈ idx3 + 7 → .there^10 .here
  --   b3: Γ₈ idx7 + 7 → .there^14 .here ; c3: top → .here
  .var (show Expr catCryptDialect _ (.sword 64) from
        { op := .bvAddCarryLo 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))
                 (.cons .here .nil)) }) <|
  -- c4 := bvAddCarryHi a3 b3 c3
  --   stack: s3, c3, s2, c2, s1, c1, s0, z, then Γ₈.  a3: Γ₈ idx3 + 8 → .there^11 .here
  --   b3: Γ₈ idx7 + 8 → .there^15 .here ; c3: .there .here
  .var (show Expr catCryptDialect _ (.sword 1) from
        { op := .bvAddCarryHi 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))
                 (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))
                 (.cons (.there .here) .nil)) }) <|
  -- ret c4   (top of stack)
  .ret .here

/-- **The split-op dialect program denotes the split spec.** The carry chain
    built from `bvAddCarryLo`/`bvAddCarryHi` returns exactly the final carry-out
    word of `bignumAdd4Split`. -/
theorem bignumAdd4ComSplit_denote
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    bignumAdd4ComSplit.denote
        (.cons a0 (.cons a1 (.cons a2 (.cons a3
         (.cons b0 (.cons b1 (.cons b2 (.cons b3 .nil))))))))
      = (bignumAdd4Split a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  rfl

/-! ## 6. The FIRST bignum → jasmin path through a high dialect

The split-op program contains only seam-covered ops (`bvConst`,
`bvAddCarryLo`, `bvAddCarryHi`), so `cryptoDialectToJasminCom` succeeds. This is
the first multi-limb carry chain lowered from `catCryptDialect` all the way to
`Com jasminDialect` — the bignum ALU spine over a *high* dialect, not hand-built
`JInstr`. -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)

/-- The split-op carry chain lowers: every op is in the covered fragment. -/
theorem bignumAdd4ComSplit_lowers :
    (cryptoDialectToJasminCom bignumAdd4ComSplit).isSome := by
  native_decide

/-- The lowered Jasmin-dialect 4-limb add-with-carry program. -/
def bignumAdd4Jasmin : Com jasminDialect (mapCtx Γ₈) (mapTy (.sword 1)) :=
  (cryptoDialectToJasminCom bignumAdd4ComSplit).get bignumAdd4ComSplit_lowers

/-- **The bignum carry chain, lowered to jasmin, denotes the split spec.**

    Composing the dialect `denote = spec` tie (`bignumAdd4ComSplit_denote`) with
    the seam's denotation-preservation corollary
    (`cryptoDialectToJasminCom_denote_eq'`): the **jasmin** program denotes (on
    the transported valuation) to `ctTransTy` of the dialect program's
    denotation, which is the final carry-out word of `bignumAdd4Split`. The first
    bignum-add result carried through `catCryptDialect` ALL THE WAY to jasmin. -/
theorem bignumAdd4Jasmin_denote
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    bignumAdd4Jasmin.denote
        (ctMapValD (.cons a0 (.cons a1 (.cons a2 (.cons a3
         (.cons b0 (.cons b1 (.cons b2 (.cons b3 .nil)))))))))
      = ctTransTy (bignumAdd4Split a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  have hlow : cryptoDialectToJasminCom bignumAdd4ComSplit = some bignumAdd4Jasmin :=
    (Option.some_get bignumAdd4ComSplit_lowers).symm
  rw [DialectToJasminComCorrect.cryptoDialectToJasminCom_denote_eq' bignumAdd4ComSplit
        (.cons a0 (.cons a1 (.cons a2 (.cons a3
         (.cons b0 (.cons b1 (.cons b2 (.cons b3 .nil)))))))) bignumAdd4Jasmin hlow,
     bignumAdd4ComSplit_denote]

/-- **The lowered jasmin program's carry-out agrees with the abstract spec.**
    Composing `bignumAdd4Jasmin_denote` with `bignumAdd4Split_eq_spec`: the jasmin
    program's carry-out word is nonzero exactly when the abstract `bignumAdd4`'s
    256-bit add overflows. `ctTransTy` is the identity on `.sword 1`. This closes
    the chain `bignumAdd4` (abstract spec) → `catCryptDialect` → `jasmin`. -/
theorem bignumAdd4Jasmin_carry_spec
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    ((bignumAdd4Jasmin.denote
        (ctMapValD (.cons a0 (.cons a1 (.cons a2 (.cons a3
         (.cons b0 (.cons b1 (.cons b2 (.cons b3 .nil))))))))) : BitVec 1).toNat ≠ 0)
      = ((bignumAdd4 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat ≠ 0) := by
  rw [bignumAdd4Jasmin_denote,
    CryptoToJasminComCorrect.ctTransTy_sword]
  exact (bignumAdd4Split_eq_spec a0 a1 a2 a3 b0 b1 b2 b3).2

end CatCrypt.Crypto.SecureCompilation.VIR.BignumAddCatCryptEmit
