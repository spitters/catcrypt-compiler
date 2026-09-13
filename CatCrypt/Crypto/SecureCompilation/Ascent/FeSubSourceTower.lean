/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.FeSubEndToEnd
public import CatCrypt.Crypto.SecureCompilation.Ascent.LegWeld
public import CatCrypt.Crypto.Hax.RustSubsetToLowCT

/-!
# `feSub` source tower: discharging `hSourceWord` for `r := a - b`

`FeSubEndToEnd.feSub_source_to_bytes` reads a source-evaluated word all the way
to the emitted bytes' clean `ZMod 2^64` subtraction spec, but takes the
source-word identification `hSourceWord : sourceWord = feVal` as an *explicit
interface hypothesis* — the fact the source→LowCT simulation tower is meant to
deliver.  This module instantiates that tower concretely for the feSub kernel
`r0 := a0 - b0` and discharges `hSourceWord`.

## The tower used: the verified `RustSubset → LowCT` lowering

The emitted kernel `feSubC` writes `r0` through a `RScalarSetExpr r0 (a0 - b0)`
node.  `RScalarSetExpr` with an arithmetic `SExpr` right-hand side is *not* in
the image of the generic `haxToLowCT` front (whose scalar-assignment arms
produce `RScalarSet` for literals or `RCall` for a leaf application), so the
`haxToLowCT` simulations do not reach this kernel.  The verified source leg for an
`RScalarSetExpr` straight-line kernel is
`RustSubsetToLowCT`: its `RRefines (RustSrc.exec src) (lower src)`
(`lowerRefines`) is a proved, non-optimizing `RustSubset → LowCT` lowering whose
`lower` arm for `assign x e` / `letE x e` is exactly `RScalarSetExpr x e`.

`feSubSrc` is the `RustSubset` encoding of `r0 := a0 - b0` (write the two literal
inputs, then subtract), and `feSubSrc_refines` is its source→LowCT simulation —
a proved fact, no free hypothesis: running the lowered LowCT program under
`RustExec` advances the scalar state by the source semantics `RustSrc.exec`.

## The identification

`feSubSourceWord` is the word the source semantics leaves at `r0`, cast into the
64-bit word type.  It coincides with the emitted kernel's tracked word `feVal`
(`feSubSourceWord_eq_feVal`, by evaluation of the two independently-defined
semantics).  `feSub_source_to_bytes_tower` does not go through that evaluation:
it is the instance of the generic weld `LegWeld.legWeld_lower`, which carries
the source semantics to the emitted bytes for any straight-line kernel from the
descent's refinement (`lowerRefines feSubSrc`, transported to the front's
spelling `feSubC` along `feSubC_litNorm`), the run `feSubC_run` and the ascent
correspondence `feSub_corres`.

Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (sgraf812/ascent).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 10000

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Hax.RustSubsetToLowCT (RustSrc lower lowerRefines RRefines)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (Ctx)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge (readsOK afterB varsBoundIn)
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecRoundAdeq (not_isTmp_short)

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## The `RustSubset` source kernel for `r0 := a0 - b0` -/

/-- The `RustSubset` encoding of the closed feSub kernel: write the two literal
    inputs `a0 := av`, `b0 := bv`, then assign `r0 := a0 - b0` (`subE`).  Each
    write is a scalar `let`/`assign`, matching the source straight-line form. -/
def feSubSrc : RustSrc :=
  .letE "a0" (.SLit av)
    (.letE "b0" (.SLit bv)
      (.assign "r0" subE))

/-- `feSubSrc` is in the `if`-free fragment, so `lowerRefines` applies. -/
theorem feSubSrc_ifFree : feSubSrc.ifFree = true := by decide

/-- **The feSub source→LowCT simulation.**  The verified non-optimizing lowering
    `lower feSubSrc` refines the source semantics `RustSrc.exec feSubSrc`: under
    any fuel and leaf spec, `RustExec` runs the lowered LowCT program from any
    state to one whose scalar map is the source program's.  No free hypothesis —
    this is the source-tower leg the emit + ascent legs are welded to. -/
theorem feSubSrc_refines : RRefines (RustSrc.exec feSubSrc) (lower feSubSrc) :=
  lowerRefines feSubSrc feSubSrc_ifFree

/-! ## The source word and its identification with the emitted `feVal` -/

/-- The word the source semantics leaves at `r0` (env-independent: the kernel
    writes both inputs as literals), cast into the 64-bit word type. -/
def feSubSourceWord : BitVec 64 :=
  BitVec.ofNat 64 (RustSrc.exec feSubSrc (fun _ => 0) "r0")

/-- The source-derived word coincides with the emitted kernel's tracked word
    `feVal`.  Both compute `a0 - b0` (`av - bv`); the equality is discharged by
    evaluating the two independently-defined semantics. -/
theorem feSubSourceWord_eq_feVal : feSubSourceWord = feVal := by
  unfold feSubSourceWord feSubSrc
  decide

/-! ## The end-to-end source-to-bytes theorem, `hSourceWord` discharged -/

/-! ## The weld instance -/

/-- The front's spelling `feSubC` is the lowering `lower feSubSrc` with its two
    literal assignments normalised. -/
theorem feSubC_litNorm : LitNorm (lower feSubSrc) feSubC :=
  .seq (.lit "a0" av) (.seq (.lit "b0" bv) (.refl _))

/-- The run of `feSubC` from the default state: both literals are `u64`, and the
    subtraction `a0 - b0` is in range at the state it reads (`bv ≤ av`). -/
theorem feSubC_run : AdeqRun feSubC frs0 frsF :=
  .rSeq (.rScalarSet (by decide))
    (.rSeq (.rScalarSet (by decide))
      (.rScalarSetExpr subE_srcClean (by simp only [subE, SExpr.inRange, SExpr.eval]; decide)))

/-- Every read of `feSubC` follows a write. -/
theorem feSubC_readsOK : readsOK (fun _ => False) feSubC := by
  simp [readsOK, afterB, varsBoundIn, feSubC, subE]

/-- `r0` is written by `feSubC`. -/
theorem feSubC_out : afterB (fun _ => False) feSubC "r0" := by
  simp [afterB, feSubC]

set_option linter.unusedVariables false in
/-- **`feSub_source_to_bytes_tower`.**  For the closed feSub kernel
    `r0 := a0 - b0`, the emitted jasmin program `feJcom` denotes to
    `ctTransTy feSubSourceWord` where `feSubSourceWord` is the *source*
    program's evaluated output word, and that word's clean `ZMod 2^64` spec is
    exactly `(av : ZMod 2^64) - (bv : ZMod 2^64)` — the ascent field spec.

    The instance of the generic weld `legWeld_lower`: the source word is delivered
    by the verified `RustSubset → LowCT` lowering `lowerRefines feSubSrc`,
    transported to `feSubC` along `feSubC_litNorm`; the ascent leg is
    `feSub_corres`; the front artifacts are those of `FeSubEndToEnd`. -/
theorem feSub_source_to_bytes_tower (N : Nat) (leafSpec : LeafSpec) :
    feJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy feSubSourceWord
      ∧ wEnc feSubSourceWord
          = ((av : Nat) : ZMod (2 ^ 64)) - ((bv : Nat) : ZMod (2 ^ 64)) := by
  have h := legWeld_lower feSubSrc feSubSrc_ifFree feSubC_litNorm ⟨frsF, feSubC_run⟩
    scalarInRange_default "r0" (not_isTmp_short "r0" (by decide)) feSubC_readsOK feSubC_out
    ⟨fO, fHTrans, fW, fHName, fCom, fHRet, feJcom, fHCom⟩ faSub (fun _ => True) feSub_corres
    trivial
  exact ⟨h.1, h.2.trans (faSub_at_r0 _)⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
