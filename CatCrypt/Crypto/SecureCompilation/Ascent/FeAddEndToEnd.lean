/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

-- The closed-kernel route reduces the front (`translateDialectControl`,
-- `semScalar`, `cryptoDialectToJasminCom`) by `rfl`/`decide`; under the module
-- system that reduction needs the front closure imported with `all`, and
-- `Nat.repr` (the front's slot names) exposed through `Init.Data.Repr`.
import all Init.Data.Repr
import all CatCrypt.Core.Code
import all CatCrypt.Crypto.CryptoWord
import all CatCrypt.Crypto.Jasmin.JasminAST
import all CatCrypt.Crypto.Jasmin.JasminTypes
import all CatCrypt.Crypto.Jasmin.LowCTExec
import all CatCrypt.Crypto.SDist
import all CatCrypt.Crypto.SecureCompilation.CryptoSSA
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
import all CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
import all CatCrypt.Crypto.SecureCompilation.Dialects.RustExecKernelAdeq
import all CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
import all CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.Core
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresScalar
public import CatCrypt.Crypto.SecureCompilation.Ascent.FeSubEndToEnd
public import CatCrypt.Crypto.SecureCompilation.Ascent.LegWeld
public import CatCrypt.Crypto.Hax.RustSubsetToLowCT

/-!
# `feAdd` end-to-end: the second closed source→bytes ascend capstone

This module proves the source→bytes ascent end to end for a real `feAdd`-shape kernel
`r := a + b` over a *closed* straight-line program (the two source words are
first written as literals, then added). It is the addition analogue of
`FeSubEndToEnd` / `FeSubSourceTower`: every leg is discharged with no leftover
`Corres`/`RustExec`/`hSourceWord` hypothesis.

* **Emit leg** — the verified front/back pipeline's emitted jasmin program
  `feAddJcom` denotes to `ctTransTy feAddVal`, where `feAddVal` is the word
  `semScalar` leaves at `r0`. Discharged through the SATISFIABLE closed-kernel
  route `rustToJasminCom_endToEnd_topLevel_unconditional`, welded to the ascent
  leg via the reused `keystone_emit_NT` (from `FeSubEndToEnd`).
* **Ascent leg** — the ascent correspondence `feAdd_ascends` (the `SAdd`
  analogue of `feSub_ascends`, built from the arithmetic value leaf
  `corres_setExpr` whose `SAdd` node transfers through the `RelatedBinOp wEnc`
  add square `wEncAdd`), sequenced (`corres_seq`) after the two literal-write
  leaves, pins `wEnc feAddVal` to the clean `ZMod 2^64` spec
  `(av : ZMod 2^64) + (bv : ZMod 2^64)`.
* **Source leg** — `feAddSrc : RustSrc` encodes `r0 := a0 + b0`; its
  source→LowCT simulation `feAddSrc_refines` is delivered by the verified
  non-optimizing `RustSubset → LowCT` lowering `RustSubsetToLowCT.lowerRefines`
  (the source leg for an `RScalarSetExpr` arithmetic kernel — the generic
  `haxToLowCT` front does not emit `RScalarSetExpr` from arithmetic). The
  source word coincides with the emitted kernel's tracked word
  (`feAddSourceWord_eq_feVal`, by `decide`). `feAdd_source_to_bytes_tower`, an
  instance of `LegWeld.legWeld_lower`, states the closed kernel from the `RustSrc`
  source word to the jasmin program's denotation as one statement.

## `SRwordNT`, not `SRword`

As in `FeSubEndToEnd`, the `RScalarSetExpr` value leaf holds only over the
non-temp restriction `SRwordNT` (the LowCT lowering scribbles the fresh-temp
namespace), so this module reuses the faithful `keystone_NT` / `keystone_emit_NT`
counterparts.

Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (sgraf812/ascent).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 10000

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy CVar Ctx)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap RustStateInterp)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect (DTransOut)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
  (translateDialectControl)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVar)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecRoundAdeq (not_isTmp_short)
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge (readsOK afterB varsBoundIn)
open CatCrypt.Crypto.Hax.RustSubsetToLowCT (RustSrc lower lowerRefines RRefines)

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## The `SAdd` ascent leaf (analogue of `feSub_ascends`) -/

/-- A real `feAdd`-shape kernel `r := a + b` (addition over word source
    variables) ascends, unconditionally, to its `ZMod 2^64` word spec
    `φa + φb` — via the arithmetic value leaf `corres_setExpr` (whose `SAdd`
    node transfers through the `RelatedBinOp wEnc` add square `wEncAdd`). -/
theorem feAdd_ascends (aName bName rName : String)
    (hna : ¬ isTmpName aName) (hnb : ¬ isTmpName bName) :
    Corres SRwordNT (fun _ => True)
      (fun φ s => if s = rName then φ aName + φ bName else φ s)
      (.RScalarSetExpr rName (.SAdd (.SVar aName) (.SVar bName))) := by
  have h := corres_setExpr rName (.SAdd (.SVar aName) (.SVar bName)) ⟨hna, hnb⟩
  simpa only [evalZMod] using h

/-! ## The concrete closed `feAdd` kernel `r0 := a0 + b0`

Literal inputs `av`, `bv` are reused from `FeSubEndToEnd`. -/

/-- The addition expression `a0 + b0`. -/
def addE : SExpr := .SAdd (.SVar "a0") (.SVar "b0")

/-- The closed `feAdd` kernel: write the two literal inputs, then add. SSA
    form (each write a fresh slot), matching the front's own output. -/
def feAddC : LowCT :=
  .RSeq (.RScalarSet "a0" av)
    (.RSeq (.RScalarSet "b0" bv)
      (.RScalarSetExpr "r0" addE))

theorem addE_srcClean : srcClean addE :=
  ⟨not_isTmp_short "a0" (by decide), not_isTmp_short "b0" (by decide)⟩

theorem addE_arithClean : IsArithClean addE :=
  ⟨not_isTmp_short "a0" (by decide), not_isTmp_short "b0" (by decide)⟩

theorem feAddC_coveredS : IsCoveredS feAddC :=
  .rSeq (.rScalarSet "a0" av)
    (.rSeq (.rScalarSet "b0" bv)
      (.rScalarSetExpr "r0" addE addE_srcClean))

theorem feAddC_covered : IsCoveredSCtl feAddC := .ofStraight feAddC_coveredS

/-! ### The `RustExec` reference run -/

def fars0 : RustState := default
def fars1 : RustState := rsSetScalar fars0 "a0" av
def fars2 : RustState := rsSetScalar fars1 "b0" bv
def farsF : RustState := rsSetScalar fars2 "r0" (addE.eval fars2.rsScalar)

theorem feAddC_exec (N : Nat) (leafSpec : LeafSpec) :
    RustExec N leafSpec feAddC fars0 farsF :=
  .seq _ _ fars0 fars1 farsF (.scalarSet "a0" av fars0)
    (.seq _ _ fars1 fars2 farsF (.scalarSet "b0" bv fars1)
      (.scalarSetExpr "r0" addE fars2))

/-! ### Front translation, semantics, output tracking — all by `.get`/`rfl` -/

theorem faTransSome : (translateDialectControl VarMap.empty feAddC).isSome := by rfl

noncomputable def faO : DTransOut ([] : Ctx) :=
  (translateDialectControl VarMap.empty feAddC).get faTransSome

theorem faHTrans : translateDialectControl VarMap.empty feAddC = some faO :=
  (Option.some_get faTransSome).symm

theorem faSemSome : (semScalar feAddC (fun _ => none)).isSome := by rfl

noncomputable def faEnv : SEnvScalar := (semScalar feAddC (fun _ => none)).get faSemSome

theorem faHSem : semScalar feAddC (fun _ => none) = some faEnv :=
  (Option.some_get faSemSome).symm

theorem faNameSome : (faO.vm.lookup "r0").isSome := by rfl

/-- The tracked slot's type is the 64-bit word: decided, since the slot name
    goes through `Nat.repr`, which the elaborator's definitional check does not
    reduce. -/
theorem faNameTy : ((faO.vm.lookup "r0").get faNameSome).1 = .sword 64 := by
  decide

/-- The tracked output slot for `r0`. -/
noncomputable def faW : CVar faO.Γ' (.sword 64) :=
  cast (congrArg (CVar faO.Γ') faNameTy) ((faO.vm.lookup "r0").get faNameSome).2

theorem faHName : faO.vm.lookup "r0" = some ⟨.sword 64, faW⟩ := by decide

theorem faValSome : (faEnv "r0").isSome := by rfl

theorem faValTy : ((faEnv "r0").get faValSome).1 = .sword 64 := by decide

/-- The word `semScalar` leaves in `r0`. -/
noncomputable def feAddVal : BitVec 64 :=
  cast (congrArg CryptoTy.denote faValTy) ((faEnv "r0").get faValSome).2

theorem faHVal : faEnv "r0" = some ⟨.sword 64, feAddVal⟩ :=
  envSlot_eq_some_sword faEnv "r0" faValSome faValTy feAddVal rfl

theorem faRetSome : (faO.cont (Com.ret (toVIRVar faW))).isSome := by rfl

noncomputable def faCom : Com catCryptDialect ([] : Ctx) (.sword 64) :=
  (faO.cont (Com.ret (toVIRVar faW))).get faRetSome

theorem faHRet : faO.cont (Com.ret (toVIRVar faW)) = some faCom :=
  (Option.some_get faRetSome).symm

theorem faComSome : (cryptoDialectToJasminCom faCom).isSome := by rfl

noncomputable def feAddJcom : Com jasminDialect (mapCtx ([] : Ctx)) (mapTy (.sword 64)) :=
  (cryptoDialectToJasminCom faCom).get faComSome

theorem faHCom : cryptoDialectToJasminCom faCom = some feAddJcom :=
  (Option.some_get faComSome).symm

/-! ### The abstraction leg: the composed ascent correspondence

`feAdd_ascends` for the terminal addition, sequenced (`corres_seq`) after the
two literal-write leaves (`corres_setScalar_NT`). The composite abstract map sets
`r0` to `(av : ZMod 2^64) + (bv : ZMod 2^64)`. -/

/-- The composite abstract map of the closed kernel. -/
def faAdd : (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64)) :=
  fun a =>
    (fun a =>
      (fun φ s => if s = "r0" then φ "a0" + φ "b0" else φ s)
        ((fun a s => if s = "b0" then ((bv : Nat) : ZMod (2 ^ 64)) else a s) a))
      ((fun a s => if s = "a0" then ((av : Nat) : ZMod (2 ^ 64)) else a s) a)

theorem feAdd_corres : Corres SRwordNT (fun _ => True) faAdd feAddC := by
  have h := corres_seq SRwordNT (corres_setScalar_NT "a0" av)
    (corres_seq SRwordNT (corres_setScalar_NT "b0" bv)
      (feAdd_ascends "a0" "b0" "r0"
        (not_isTmp_short "a0" (by decide)) (not_isTmp_short "b0" (by decide)))
      (fun _ _ => trivial))
    (fun _ _ => trivial)
  exact h

/-- The composite abstract map, evaluated at the output slot, is the clean field
    spec: `(av : ZMod 2^64) + (bv : ZMod 2^64)`. -/
theorem faAdd_at_r0 (a : String → ZMod (2 ^ 64)) :
    faAdd a "r0" = ((av : Nat) : ZMod (2 ^ 64)) + ((bv : Nat) : ZMod (2 ^ 64)) := by
  simp [faAdd]

/-! ### The `hAgree` closed-kernel adapter (zero-word entry `env₀` reused) -/

theorem faHAgree :
    ∀ e, semScalar feAddC env₀ = some e → e "r0" = some ⟨.sword 64, feAddVal⟩ := by
  intro e he
  have hstep : semScalar feAddC env₀
      = some ((semScalar feAddC env₀).get (by rfl)) := (Option.some_get (by rfl)).symm
  rw [hstep] at he
  obtain rfl := (Option.some.injEq _ _).mp he
  rfl

/-! ## The end-to-end theorem -/

/-- **`feAdd_endToEnd`.** For the closed `feAdd` kernel `r0 := a0 + b0` (literal
    inputs `av`, `bv`), the verified front/back pipeline's emitted jasmin program
    `feAddJcom` denotes to `ctTransTy feAddVal`, and the emitted output word's clean
    `ZMod 2^64` spec is exactly `(av : ZMod 2^64) + (bv : ZMod 2^64)` — the ascent
    (`feAdd_ascends`) field spec. No free `Corres`/`RustExec` hypothesis: the emit
    leg runs through `rustToJasminCom_endToEnd_topLevel_unconditional`, and the
    ascent leg is welded via `keystone_emit_NT`. -/
theorem feAdd_endToEnd (N : Nat) (leafSpec : LeafSpec) :
    feAddJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy feAddVal
      ∧ wEnc feAddVal = ((av : Nat) : ZMod (2 ^ 64)) + ((bv : Nat) : ZMod (2 ^ 64)) := by
  have h := keystone_emit_NT feAddC faO N leafSpec fars0 farsF faEnv "r0" faW feAddVal
    faCom feAddJcom faAdd (fun _ => True) env₀ (fun _ => (0 : ZMod (2 ^ 64)))
    feAddC_covered faHTrans (feAddC_exec N leafSpec) faHSem faHName faHVal faHRet faHCom
    feAdd_corres hSR₀ trivial faHAgree (not_isTmp_short "r0" (by decide))
  refine ⟨h.1, ?_⟩
  rw [h.2, faAdd_at_r0]

/-! ## The source word as an interface hypothesis -/

/-- **`feAdd_source_to_bytes`.** The `feAdd_endToEnd` chain read from a source
    program's evaluated output word, taking the source-word identification
    `hSourceWord : sourceWord = feAddVal` as an explicit interface hypothesis.
    Discharged concretely in `feAdd_source_to_bytes_tower` below. -/
theorem feAdd_source_to_bytes (N : Nat) (leafSpec : LeafSpec)
    (sourceWord : BitVec 64) (hSourceWord : sourceWord = feAddVal) :
    feAddJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy sourceWord
      ∧ wEnc sourceWord = ((av : Nat) : ZMod (2 ^ 64)) + ((bv : Nat) : ZMod (2 ^ 64)) := by
  subst hSourceWord
  exact feAdd_endToEnd N leafSpec

/-! ## The `feAdd` source tower: discharging `hSourceWord` for `r := a + b`

The emitted kernel `feAddC` writes `r0` through a `RScalarSetExpr r0 (a0 + b0)`
node, which is *not* in the image of the generic `haxToLowCT` front (whose scalar
arms emit `RScalarSet` for literals or `RCall` for a leaf, never `RScalarSetExpr`
from arithmetic). The faithful verified tower is `RustSubsetToLowCT`, whose
`lower` arm for `assign x e` / `letE x e` is exactly `RScalarSetExpr x e`. -/

/-- The `RustSubset` encoding of the closed feAdd kernel: write the two literal
    inputs `a0 := av`, `b0 := bv`, then assign `r0 := a0 + b0` (`addE`). -/
def feAddSrc : RustSrc :=
  .letE "a0" (.SLit av)
    (.letE "b0" (.SLit bv)
      (.assign "r0" addE))

/-- `feAddSrc` is in the `if`-free fragment, so `lowerRefines` applies. -/
theorem feAddSrc_ifFree : feAddSrc.ifFree = true := by decide

/-- `feAddSrc` reads no tower limb. -/
theorem feAddSrc_limbFree : feAddSrc.limbFree := by
  simp [feAddSrc, addE, RustSrc.limbFree, SExpr.limbFree]

/-- **The feAdd source→LowCT simulation.** The verified non-optimizing lowering
    `lower feAddSrc` refines the source semantics `RustSrc.exec feAddSrc` — no free
    hypothesis, delivered by `RustSubsetToLowCT.lowerRefines`. -/
theorem feAddSrc_refines : RRefines (RustSrc.exec feAddSrc) (lower feAddSrc) :=
  lowerRefines feAddSrc feAddSrc_ifFree feAddSrc_limbFree

/-- The word the source semantics leaves at `r0` (env-independent: the kernel
    writes both inputs as literals), cast into the 64-bit word type. -/
def feAddSourceWord : BitVec 64 :=
  BitVec.ofNat 64 (RustSrc.exec feAddSrc (fun _ => 0) "r0")

/-- The source-derived word coincides with the emitted kernel's tracked word
    `feAddVal`. Both compute `a0 + b0` (`av + bv`); the equality is discharged by
    evaluating the two independently-defined semantics. -/
theorem feAddSourceWord_eq_feVal : feAddSourceWord = feAddVal := by
  unfold feAddSourceWord feAddSrc
  decide

/-! ## The end-to-end source-to-bytes theorem, `hSourceWord` discharged -/

/-! ## The weld instance -/

/-- The front's spelling `feAddC` is the lowering `lower feAddSrc` with its two
    literal assignments normalised. -/
theorem feAddC_litNorm : LitNorm (lower feAddSrc) feAddC :=
  .seq (.lit "a0" av) (.seq (.lit "b0" bv) (.refl _))

/-- The run of `feAddC` from the default state: both literals are `u64`, and the
    addition `a0 + b0` is in range at the state it reads (`av + bv < 2^64`). -/
theorem feAddC_run : AdeqRun feAddC fars0 farsF :=
  .rSeq (.rScalarSet (by decide))
    (.rSeq (.rScalarSet (by decide))
      (.rScalarSetExpr addE_srcClean (by simp only [addE, SExpr.inRange, SExpr.eval]; decide)))

/-- Every read of `feAddC` follows a write. -/
theorem feAddC_readsOK : readsOK (fun _ => False) feAddC := by
  simp [readsOK, afterB, varsBoundIn, feAddC, addE]

/-- `r0` is written by `feAddC`. -/
theorem feAddC_out : afterB (fun _ => False) feAddC "r0" := by
  simp [afterB, feAddC]

set_option linter.unusedVariables false in
/-- **`feAdd_source_to_bytes_tower`.** For the closed feAdd kernel
    `r0 := a0 + b0`, the emitted jasmin program `feAddJcom` denotes to
    `ctTransTy feAddSourceWord` where `feAddSourceWord` is the *source* program's
    evaluated output word, and that word's clean `ZMod 2^64` spec is exactly
    `(av : ZMod 2^64) + (bv : ZMod 2^64)` — the ascent field spec.

    The instance of the generic weld `legWeld_lower`: the source word is delivered
    by the verified `RustSubset → LowCT` lowering `lowerRefines feAddSrc`,
    transported to `feAddC` along `feAddC_litNorm`; the ascent leg is
    `feAdd_corres`; the front artifacts are those of this module. -/
theorem feAdd_source_to_bytes_tower (N : Nat) (leafSpec : LeafSpec) :
    feAddJcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy feAddSourceWord
      ∧ wEnc feAddSourceWord
          = ((av : Nat) : ZMod (2 ^ 64)) + ((bv : Nat) : ZMod (2 ^ 64)) := by
  have h := legWeld_lower feAddSrc feAddSrc_ifFree feAddSrc_limbFree feAddC_litNorm
    ⟨farsF, feAddC_run⟩ scalarInRange_default "r0" (not_isTmp_short "r0" (by decide)) feAddC_readsOK feAddC_out
    ⟨faO, faHTrans, faW, faHName, faCom, faHRet, feAddJcom, faHCom⟩ faAdd (fun _ => True)
    feAdd_corres trivial
  exact ⟨h.1, h.2.trans (faAdd_at_r0 _)⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
