/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomFoldPos
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomHiFree
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomNop
import CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedAddrWEncodable

/-!
# Acceptance of `compileA` on the bounded field domain from the open stage facts

`fieldDomB''` is the field domain `fieldDomB'` restricted by the frame bound: the number `n`
of words of the operands is at most `121`, the bound under which the frame check `frameOkB`
(stage `G18`) holds for the sum, the difference and the product. `FieldDomOpen` collects the
stage facts of `compileA` on `fieldDomB''` that have no proof at the field domain: the fusion
check of the product (`G10`), the fold positions of the cell fold check (`G12`), the
translation validation `ownedCheckMC` (`G13`), the class `printedAddrWB` of the printed body
(`C2`), the physical image and image gates (`G16`, `G17`), the frame check (`G18`), the
save-slot readers of the entry check (`G19`) and the leak validation `ownedCheckML` (fifth
conjunct of `C1`). The printed class `G15` is `C2` (`fieldDom_regionPrintedB_open`), the
encoder `F10` follows from `C2` (`fieldDom_encode_open`), and the constant-time image gate `C3`
is a conjunct of the image gate of `G17` (`fieldDom_imgGateCW_open`). Every other stage is
filled from its theorem.

## Main definitions

* `fieldFrameBoundB` — the operands of a field expression have at most `121` words.
* `fieldDomB''` — the field domain `fieldDomB'` under the frame bound.
* `FieldDomOpen` — the stage facts of `compileA` on `fieldDomB''` that are not proved.

## Main results

* `fieldDom_regionCoStage_open` — the gate names no refusing stage on `fieldDomB''`.
* `fieldDom_regionCtB_open` — the constant-time gate passes on `fieldDomB''`.
* `compileA_isSome_of_fieldDom_open` — `compileA` accepts every member of `fieldDomB''`.
* `<row>_fieldDomB''` — the twenty field rows of `LeanFrontFields` are members of `fieldDomB''`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute (fieldAbi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (printedAddrWB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCidx (imgGateCW)
open CatCrypt.Crypto.Hax (HaxModule)

/-! ## 1. The bounded field domain -/

/-- **The frame bound of the field domain**: the field expression has operands of at most
    `121` words. -/
def fieldFrameBoundB (e : _root_.Hax.TExpr) : Bool :=
  match fieldDomE e with
  | some (_, n) => decide (n ≤ 121)
  | none => false

/-- **The bounded field domain**: a member of `fieldDomB'` whose operands have at most `121`
    words (`fieldFrameBoundB`). -/
def fieldDomB'' (e : _root_.Hax.TExpr) (σ : AbiLayout) : Bool :=
  fieldDomB' e σ && fieldFrameBoundB e

/-- A member of `fieldDomB''` is a member of `fieldDomB'`. -/
theorem fieldDomB'_of_fieldDomB'' {e : _root_.Hax.TExpr} {σ : AbiLayout}
    (h : fieldDomB'' e σ = true) : fieldDomB' e σ = true := by
  simp only [fieldDomB'', Bool.and_eq_true] at h
  exact h.1

/-- A member of `fieldDomB''` is a member of `fieldDomB`. -/
theorem fieldDomB_of_fieldDomB'' {e : _root_.Hax.TExpr} {σ : AbiLayout}
    (h : fieldDomB'' e σ = true) : fieldDomB e σ = true :=
  fieldDomB_of_fieldDomB' (fieldDomB'_of_fieldDomB'' h)

/-- A field expression with `k` operands of `n ≤ 121` words is in `fieldDomB''` under
    `fieldAbi k n`. -/
theorem fieldDomB''_fieldAbi {e : _root_.Hax.TExpr} {k n : Nat} (h : fieldDomE e = some (k, n))
    (hn : n ≤ 121) : fieldDomB'' e (fieldAbi k n) = true := by
  simp only [fieldDomB'', fieldDomB'_fieldAbi h (by omega), fieldFrameBoundB, h,
    decide_eq_true hn, Bool.and_self]

/-! ## 2. The open stage facts -/

/-- **The stage facts of `compileA` on the bounded field domain that are not proved.** Each
    field is a stage fact of `FieldDomStages` at a member of `fieldDomB''`, or the hypothesis
    of the theorem that proves that stage under a condition. -/
structure FieldDomOpen : Prop where
  /-- Stage `G10` for the product and the square: the fusion check `fuseOKL`. The sum and the
      difference are `fieldDom_fuseOKL_addSub`. -/
  fuseOKL_mul {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB'' e σ = true)
    (hA : ¬ FieldAddSub e) (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "fuseOKL"
  /-- Stage `G12`: the fold positions of the fused code, the hypothesis of
      `fieldDom_regionFoldB_of_foldPos`. -/
  foldPos {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    ∀ k i, ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
        (regionCoParts σ exportReg b t r.code r.res cert).pre.length)[k]? = some i →
      FoldPos (regionCoParts σ exportReg b t r.code r.res cert).cells
        ((regionCoParts σ exportReg b t r.code r.res cert).fused.drop
          (regionCoParts σ exportReg b t r.code r.res cert).pre.length) k i
  /-- Stage `G13`: the translation validation `ownedCheckMC`. -/
  ownedCheckMC {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "ownedCheckMC"
  /-- Stage `G14`: the index invariant check `idxInvCheckB`. -/
  idxInvCheckB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "idxInvCheckB"
  /-- Stage `C2`: the printed body passes `printedAddrWB`. -/
  printedAddrWB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) : printedAddrWB b = true
  /-- Stage `G16`: the physical image check `physImgB`. -/
  physImgB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "physImgB"
  /-- Stage `G17`: the image gate `calleeImgBT none`. -/
  regionImgB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "regionImgB"
  /-- Stage `G18`: the frame check `frameOkB`. -/
  frameOkB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "frameOkB"
  /-- Stage `G19`: the printed body reads the save slot of each parameter register, the
      hypothesis of `fieldDom_entryB_of_argReaders`. -/
  argReaders {e : _root_.Hax.TExpr} {σ : AbiLayout} (fname : String)
    (h : fieldDomB'' e σ = true) : ArgReaders e σ fname
  /-- The fifth conjunct of stage `C1`: the leak validation `ownedCheckML`. -/
  ownedCheckML {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    X86Backend.OwnedTVLeak.ownedCheckML (regionCoParts σ exportReg b t r.code r.res cert).outs
      (regionCoParts σ exportReg b t r.code r.res cert).ref
      (JasminLsemAddrImage.virtImg
        (regionSl σ exportReg (regionCoParts σ exportReg b t r.code r.res cert))
        (X86Backend.ImageAddrCells.cellBody
          (regionSl σ exportReg (regionCoParts σ exportReg b t r.code r.res cert)) b)) = true

/-! ## 3. The gates on the bounded field domain -/

section Gate

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- The gate does not refuse at `regionPrintedB` on a body of the class `printedAddrWB`. -/
theorem regionCoStage_ne_regionPrintedB {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} {fn : String} (h : printedAddrWB b = true) :
    regionCoStage σ nm b t code res cert none fn ≠ some "regionPrintedB" := by
  unfold regionCoStage
  dsimp only
  simp only [regionPrintedB, h, Option.isSome_none, Bool.false_or, Bool.true_eq_false,
    ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

/-- **The image gate of a body the gate accepts**: when `regionCoStage` names no refusing
    stage, the body passes `regionImgB` at the slot map `regionSl`, the cell arrays and the
    observed names of its parts (stage `G17`). -/
theorem regionImgB_of_regionCoStage_eq_none {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} {fn : String}
    (h : regionCoStage σ nm b t code res cert none fn = none) :
    regionImgB (regionSl σ nm (regionCoParts σ nm b t code res cert))
      (regionCoParts σ nm b t code res cert).cells
      ((regionCoParts σ nm b t code res cert).outs
        ++ (regionCoParts σ nm b t code res cert).cellOuts) b = true := by
  dsimp only [regionCoStage] at h
  iterate 18 obtain ⟨-, h⟩ := ite_false_eq_none h
  obtain ⟨h19, -⟩ := ite_false_eq_none h
  simpa only [calleeImgBT_none, calleeCodeT_none] using h19

/-- Stage `G15` on the bounded field domain, from stage `C2`. -/
theorem fieldDom_regionPrintedB_open (O : FieldDomOpen) (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "regionPrintedB" :=
  regionCoStage_ne_regionPrintedB (O.printedAddrWB h hB)

/-- Stage `F10` on the bounded field domain, from stage `C2`: the gated encoder accepts the
    printed body (`encodable_of_printedAddrWB`). -/
theorem fieldDom_encode_open (O : FieldDomOpen) (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    (X86Backend.LprogBytes.encodeLfundefBytesChecked b).isSome = true := by
  unfold X86Backend.LprogBytes.encodeLfundefBytesChecked
  rw [if_pos (X86Backend.DecodePrintedAddrW.encodable_of_printedAddrWB (O.printedAddrWB h hB))]
  rfl

/-- Stage `G10` on the bounded field domain: the sum and the difference by
    `fieldDom_fuseOKL_addSub`, the product and the square from `O`. -/
theorem fieldDom_fuseOKL_open (O : FieldDomOpen) (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "fuseOKL" := by
  by_cases hA : FieldAddSub e
  · exact fieldDom_fuseOKL_addSub (fieldDomB_of_fieldDomB'' h) hA hB
  · exact O.fuseOKL_mul h hA hB

/-- The gate names no refusing stage on the bounded field domain: stages `G1`-`G21`. -/
theorem fieldDom_regionCoStage_open (O : FieldDomOpen) (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname = none := by
  have h' := fieldDomB'_of_fieldDomB'' h
  have h0 := fieldDomB_of_fieldDomB' h'
  refine regionCoStage_eq_none_of_ne fun s hs => ?_
  simp only [gateStages, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [fieldDom_coClass h0 hB, fieldDom_coCfgB' h0 hB, fieldDom_coEntryFix' h0 hB,
    fieldDom_renB h0 hB, fieldDom_coResultName h0 hB, fieldDom_coResultCopy h0 hB,
    fieldDom_regionResultB h0 hB, fieldDom_regMerge h0 hB, fieldDom_regionNopB h0 hB,
    fieldDom_fuseOKL_open O h hB, fieldDom_fuseResultName h0 hB,
    fieldDom_regionFoldB_of_foldPos h0 hB (O.foldPos h hB),
    O.ownedCheckMC h hB, O.idxInvCheckB h hB, fieldDom_regionPrintedB_open O h hB,
    O.physImgB h hB, O.regionImgB h hB, O.frameOkB h hB,
    fieldDom_entryB_of_argReaders h' hB (O.argReaders fname h),
    fieldDom_cellNamesRB' h' hB, fieldDom_cellRegions h0 hB]

/-- Stage `C3` on the bounded field domain, from the gate: the cell body passes `imgGateCW`,
    a conjunct of the image gate `regionImgB` of stage `G17`. -/
theorem fieldDom_imgGateCW_open (O : FieldDomOpen) (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    imgGateCW (X86Backend.ImageStraightCells.frameMarkC
        (regionCoParts σ exportReg b t r.code r.res cert).cells b)
      (regionSl σ exportReg (regionCoParts σ exportReg b t r.code r.res cert))
      (X86Backend.ImageAddrCells.cellBody
        (regionSl σ exportReg (regionCoParts σ exportReg b t r.code r.res cert)) b)
      = true := by
  have hI := regionImgCoreB_of_regionImgB
    (regionImgB_of_regionCoStage_eq_none (fieldDom_regionCoStage_open O h hB))
  unfold regionImgCoreB at hI
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hI).1).2

/-- The constant-time gate passes on the bounded field domain: stages `C1`-`C3`. -/
theorem fieldDom_regionCtB_open (O : FieldDomOpen) (h : fieldDomB'' e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCtB σ exportReg b t r.code r.res cert = true := by
  have hL : regionLeakB σ exportReg b t r.code r.res cert = true := by
    dsimp only [regionLeakB]
    rw [fieldDom_regionLeakB_head (fieldDomB_of_fieldDomB'' h) hB, Bool.true_and]
    exact O.ownedCheckML h hB
  simp only [regionCtB, hL, O.printedAddrWB h hB, fieldDom_imgGateCW_open O h hB,
    Bool.and_self]

end Gate

/-! ## 4. The composition -/

/-- **`compileA` accepts every member of the bounded field domain under the open stage
    facts.** The stages in pipeline order as in `compileA_isSome_of_fieldDom`: the front
    `F1`-`F9` from their theorems, the encoder `F10` from `C2`, the gate `G1`-`G21`
    (`fieldDom_regionCoStage_open`) and the constant-time gate `C1`-`C3`
    (`fieldDom_regionCtB_open`), assembled by `compileRegion_isSome_of_stages`. -/
theorem compileA_isSome_of_fieldDom_open (O : FieldDomOpen) {e : _root_.Hax.TExpr}
    {σ : AbiLayout} (fname : String)
    (h : fieldDomB'' e σ = true) : (compileA e σ fname).isSome = true := by
  have h0 := fieldDomB_of_fieldDomB'' h
  rw [fieldDom_compileA_eq fname h0]
  unfold NFEntry.compileR
  have hr := fieldDom_refusal h0
  obtain ⟨⟨t0, q⟩, hq⟩ := fieldDom_chainNF hr
  rw [hq, Option.bind_some]
  have hE := fieldDom_exportable hr hq
  obtain ⟨q', hq', hE'⟩ := NarrowWords.narrowPrep_of_exportable q hE
  have hL := fieldDom_legalize hE'
  obtain ⟨r0, hr0⟩ := fieldDom_exportRSome hL ((nfCtx σ).map NarrowWords.wideTy).length fname
    ((nfCtx σ).map NarrowWords.wideTy).length 0
  obtain ⟨P, cert, hP⟩ := fieldDom_regionLprogCSome (a := nfAbiNames fname σ)
    (regionWebsEx σ exportReg) hr0
  obtain ⟨b, hb⟩ := fieldDom_firstBodySome hP
  have hB : FieldBody e σ fname b (NarrowWords.wideTy t0)
      (regionWebsAt (regionWebsEx σ exportReg) none r0) cert :=
    ⟨t0, q, q', r0, P, hq, hq', hr0, rfl, hP, hb, rfl⟩
  exact compileRegion_isSome_of_stages hE (fieldDom_callFree h0 hq) hq' hL hr0 hP hb
    (fieldDom_encode_open O h hB) (fieldDom_regionCoStage_open O h hB)
    (fieldDom_regionCtB_open O h hB)

/-! ## 5. The field rows of `LeanFrontFields` -/

section Rows

open CatCrypt.Crypto.SecureCompilation.Haxc.LeanFrontFields

/-- The product at the P-256 base prime is in the bounded field domain. -/
theorem p256Mul_fieldDomB'' : fieldDomB'' p256MulTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The square at the P-256 base prime is in the bounded field domain. -/
theorem p256Sqr_fieldDomB'' : fieldDomB'' p256SqrTE (fieldAbi 1 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The sum at the P-256 base prime is in the bounded field domain. -/
theorem p256Add_fieldDomB'' : fieldDomB'' p256AddTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The difference at the P-256 base prime is in the bounded field domain. -/
theorem p256Sub_fieldDomB'' : fieldDomB'' p256SubTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The product at the secp256k1 base prime is in the bounded field domain. -/
theorem secp256k1Mul_fieldDomB'' : fieldDomB'' secp256k1MulTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The square at the secp256k1 base prime is in the bounded field domain. -/
theorem secp256k1Sqr_fieldDomB'' : fieldDomB'' secp256k1SqrTE (fieldAbi 1 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The sum at the secp256k1 base prime is in the bounded field domain. -/
theorem secp256k1Add_fieldDomB'' : fieldDomB'' secp256k1AddTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The difference at the secp256k1 base prime is in the bounded field domain. -/
theorem secp256k1Sub_fieldDomB'' : fieldDomB'' secp256k1SubTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The product at the P-384 base prime is in the bounded field domain. -/
theorem p384Mul_fieldDomB'' : fieldDomB'' p384MulTE (fieldAbi 2 6) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The square at the P-384 base prime is in the bounded field domain. -/
theorem p384Sqr_fieldDomB'' : fieldDomB'' p384SqrTE (fieldAbi 1 6) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The sum at the P-384 base prime is in the bounded field domain. -/
theorem p384Add_fieldDomB'' : fieldDomB'' p384AddTE (fieldAbi 2 6) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The difference at the P-384 base prime is in the bounded field domain. -/
theorem p384Sub_fieldDomB'' : fieldDomB'' p384SubTE (fieldAbi 2 6) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The product at the BN254 base prime is in the bounded field domain. -/
theorem bn254Mul_fieldDomB'' : fieldDomB'' bn254MulTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The square at the BN254 base prime is in the bounded field domain. -/
theorem bn254Sqr_fieldDomB'' : fieldDomB'' bn254SqrTE (fieldAbi 1 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The sum at the BN254 base prime is in the bounded field domain. -/
theorem bn254Add_fieldDomB'' : fieldDomB'' bn254AddTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The difference at the BN254 base prime is in the bounded field domain. -/
theorem bn254Sub_fieldDomB'' : fieldDomB'' bn254SubTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The product at the BLS12-381 base prime is in the bounded field domain. -/
theorem bls12381Mul_fieldDomB'' : fieldDomB'' bls12381MulTE (fieldAbi 2 6) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The square at the BLS12-381 base prime is in the bounded field domain. -/
theorem bls12381Sqr_fieldDomB'' : fieldDomB'' bls12381SqrTE (fieldAbi 1 6) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The sum at the BLS12-381 base prime is in the bounded field domain. -/
theorem bls12381Add_fieldDomB'' : fieldDomB'' bls12381AddTE (fieldAbi 2 6) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

/-- The difference at the BLS12-381 base prime is in the bounded field domain. -/
theorem bls12381Sub_fieldDomB'' : fieldDomB'' bls12381SubTE (fieldAbi 2 6) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num)

end Rows

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
