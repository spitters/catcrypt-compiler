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

`fieldDomB''` is the field domain `fieldDomB'` restricted by three decidable conjuncts: the
number `n` of words of the operands is at most `121` (`fieldFrameBoundB`), the printed body of
the field pipeline passes the frame check `frameOkB` (`fieldFrameFitB`), and the allocated
body reads the save slot of the register of each parameter (`fieldArgReadersB`). The two
pipeline conjuncts compute the allocated function `fieldAllocFn?` of `e` under `σ` at the
symbol `""`; the allocation depends on the symbol only through the name of its one function
(`regionAllocC_fname`), so the function is the one of every symbol (`fieldAllocFn?_eq`). On
`fieldDomB''` the frame check `G18` (`fieldDom_frameOkB`) and the save-slot readers of the
entry check `G19` (`argReaders_of_fieldArgReadersB`) are theorems.

`FieldDomOpen` collects the stage facts of `compileA` on `fieldDomB''` that have no proof at
the field domain: the fusion check of the product (`G10`), the fold positions of the cell fold
check (`G12`), the translation validation `ownedCheckMC` (`G13`), the class `printedAddrWB` of
the printed body (`C2`), the physical image and image gates (`G16`, `G17`) and the leak
validation `ownedCheckML` (fifth conjunct of `C1`). The printed class `G15` is `C2`
(`fieldDom_regionPrintedB_open`), the encoder `F10` follows from `C2`
(`fieldDom_encode_open`), and the constant-time image gate `C3` is a conjunct of the image gate
of `G17` (`fieldDom_imgGateCW_open`). Every other stage is filled from its theorem.

## Main definitions

* `fieldFrameBoundB` — the operands of a field expression have at most `121` words.
* `fieldAllocFn?` — the allocated function of the field pipeline on `e` under `σ`.
* `fieldFrameFitB` — the printed body of the field pipeline passes `frameOkB`.
* `slotReaderB`, `fieldArgReadersB` — the allocated body reads the save slot of each parameter.
* `fieldDomB''` — the field domain `fieldDomB'` under the three conjuncts.
* `FieldDomOpen` — the stage facts of `compileA` on `fieldDomB''` that are not proved.

## Main results

* `exportR_fn_eq`, `regionAllocC_fname` — the export and the allocation stage depend on the
  function symbol only through the name of the allocated function.
* `fieldDom_frameOkB` — stage `G18` on `fieldDomB''`.
* `argReaders_of_fieldArgReadersB` — the hypothesis `ArgReaders` of stage `G19` on
  `fieldDomB''`.
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
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (slotOfReg)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPhysImgGate (printedBody)

/-! ## 1. The bounded field domain -/

/-- **The frame bound of the field domain**: the field expression has operands of at most
    `121` words. -/
def fieldFrameBoundB (e : _root_.Hax.TExpr) : Bool :=
  match fieldDomE e with
  | some (_, n) => decide (n ≤ 121)
  | none => false

/-- **The export does not depend on the function symbol**: the symbol enters only the frame
    `ifFrame` of a conditional, which ignores it. -/
theorem exportR_fn_eq (nArgs : Nat) (fn fn' : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ (d n : Nat) (I : LprogIsa.IsaData),
      exportR nArgs fn p d n I = exportR nArgs fn' p d n I := by
  induction p with
  | ret vs => intro d n I; rfl
  | var e k ih => intro d n I; simp only [exportR, ih]
  | forLoop count inits body k ihb ihk => intro d n I; simp only [exportR, ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro d n I; simp only [exportR, iht, ihe, ihk, ifFrame]
  | whileLoop inits body k ihb ihk => intro d n I; simp only [exportR, ihb, ihk]
  | call f args k ih => intro d n I; simp only [exportR, ih]

/-- **The allocation stage depends on the function symbol only through the name of its one
    function.** -/
theorem regionAllocC_fname (a : AbiNames) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (callee : Option CalleeTab)
    (ex : List String) :
    regionAllocC { a with fname := fn } p callee ex =
      (regionAllocC a p callee ex).map fun x =>
        ({ x.1 with lp_funcs := x.1.lp_funcs.map fun g => (fn, g.2) }, x.2) := by
  unfold regionAllocC exportRLfundef
  rw [exportR_fn_eq _ fn a.fname]
  cases exportR Γ.length a.fname p Γ.length 0 <;> rfl

/-- **The allocated function of the field pipeline** on `e` under `σ`: the function of the
    allocation stage `regionAllocC` on the legalised narrowed output of the chain, at the
    symbol `""`. -/
def fieldAllocFn? (e : _root_.Hax.TExpr) (σ : AbiLayout) : Option Lfundef :=
  (haxEntry.chainNF (HaxModule.single e) σ).bind fun x =>
    (NarrowWords.narrowPrep x.2).bind fun q' =>
      (regionAllocC (nfAbiNames "" σ) (legalizeRegion q') none (regionWebsEx σ exportReg)).bind
        fun y => y.1.lp_funcs.head?.map (·.2)

/-- The allocated function of `regionAllocC` at every symbol is `fieldAllocFn?`. -/
theorem fieldAllocFn?_eq {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String}
    {t0 : JasminTy} {q : NFProg jasminDialect (nfCtx σ) [t0]}
    {q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0]}
    {P0 : Lprog} {c : List (String × String)} {f : Lfundef}
    (hq : haxEntry.chainNF (HaxModule.single e) σ = some ⟨t0, q⟩)
    (hq' : NarrowWords.narrowPrep q = some q')
    (hx : regionAllocC (nfAbiNames fname σ) (legalizeRegion q') none (regionWebsEx σ exportReg)
      = some (P0, c))
    (hf : P0.lp_funcs = [(fname, f)]) : fieldAllocFn? e σ = some f := by
  have h1 : nfAbiNames "" σ = { nfAbiNames fname σ with fname := "" } := rfl
  simp only [fieldAllocFn?, hq, hq', Option.bind_some]
  rw [h1, regionAllocC_fname, hx]
  simp [hf]

/-- **The frame fit of an allocated function**: its printed body after the frame trim passes
    the frame check `frameOkB` of `σ`. -/
def fnFrameFitB (σ : AbiLayout) (f : Lfundef) : Bool :=
  X86Backend.ImageAddrFrame.frameOkB σ (frameTrim (printedBody f.lfd_res f.lfd_body))

/-- **The frame fit of the field pipeline**: the printed body of the allocated function
    `fieldAllocFn?` passes the frame check `frameOkB`. -/
def fieldFrameFitB (e : _root_.Hax.TExpr) (σ : AbiLayout) : Bool :=
  (fieldAllocFn? e σ).any (fnFrameFitB σ)

/-- **A reader of the save slot of `R`, decided**: a move `MOVQ` or `MOV:64` of `qsave.R`
    into a name other than `qsave.R`. -/
def slotReaderB (R : String) : LinstrR → Bool
  | .Lopn [.reg d] o [.reg s] =>
      s == slotOfReg R && (o == "MOVQ" || o == "MOV:64") && d != slotOfReg R
  | _ => false

/-- An instruction `slotReaderB` accepts is a `SlotReader`. -/
theorem slotReader_of_slotReaderB {R : String} {x : LinstrR} (h : slotReaderB R x = true) :
    SlotReader R x := by
  unfold slotReaderB at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨rfl, ho⟩, hd⟩ := h
    exact ⟨_, _, rfl, ho, hd⟩
  · cases h

/-- **The save-slot readers of an allocated function**: its printed body, before the frame
    trim, reads the save slot of the register of each parameter of `σ`. -/
def fnArgReadersB (σ : AbiLayout) (f : Lfundef) : Bool :=
  σ.args.all fun a =>
    (printedBody f.lfd_res f.lfd_body).any fun i => slotReaderB (exportReg a.reg) i.li_i

/-- **The save-slot readers of the field pipeline**: the printed body of the allocated
    function `fieldAllocFn?`, before the frame trim, reads the save slot of the register of
    each parameter. -/
def fieldArgReadersB (e : _root_.Hax.TExpr) (σ : AbiLayout) : Bool :=
  (fieldAllocFn? e σ).any (fnArgReadersB σ)

/-- **`ArgReaders` from `fieldArgReadersB`**, at every symbol. -/
theorem argReaders_of_fieldArgReadersB {e : _root_.Hax.TExpr} {σ : AbiLayout}
    (h : fieldArgReadersB e σ = true) (fname : String) : ArgReaders e σ fname := by
  intro t0 q q' P0 c f hq hq' hx hf a ha
  simp only [fieldArgReadersB, fnArgReadersB, fieldAllocFn?_eq hq hq' hx hf, Option.any_some,
    List.all_eq_true, List.any_eq_true] at h
  obtain ⟨i, hi, hr⟩ := h a ha
  exact ⟨i, hi, slotReader_of_slotReaderB hr⟩

/-- **The bounded field domain**: a member of `fieldDomB'` whose operands have at most `121`
    words (`fieldFrameBoundB`), whose printed body passes the frame check (`fieldFrameFitB`)
    and whose allocated body reads the save slot of each parameter (`fieldArgReadersB`). -/
def fieldDomB'' (e : _root_.Hax.TExpr) (σ : AbiLayout) : Bool :=
  fieldDomB' e σ && fieldFrameBoundB e && fieldFrameFitB e σ && fieldArgReadersB e σ

/-- A member of `fieldDomB''` is a member of `fieldDomB'`. -/
theorem fieldDomB'_of_fieldDomB'' {e : _root_.Hax.TExpr} {σ : AbiLayout}
    (h : fieldDomB'' e σ = true) : fieldDomB' e σ = true := by
  simp only [fieldDomB'', Bool.and_eq_true] at h
  exact h.1.1.1

/-- A member of `fieldDomB''` passes `fieldFrameFitB`. -/
theorem fieldFrameFitB_of_fieldDomB'' {e : _root_.Hax.TExpr} {σ : AbiLayout}
    (h : fieldDomB'' e σ = true) : fieldFrameFitB e σ = true := by
  simp only [fieldDomB'', Bool.and_eq_true] at h
  exact h.1.2

/-- A member of `fieldDomB''` passes `fieldArgReadersB`. -/
theorem fieldArgReadersB_of_fieldDomB'' {e : _root_.Hax.TExpr} {σ : AbiLayout}
    (h : fieldDomB'' e σ = true) : fieldArgReadersB e σ = true := by
  simp only [fieldDomB'', Bool.and_eq_true] at h
  exact h.2

/-- A member of `fieldDomB''` is a member of `fieldDomB`. -/
theorem fieldDomB_of_fieldDomB'' {e : _root_.Hax.TExpr} {σ : AbiLayout}
    (h : fieldDomB'' e σ = true) : fieldDomB e σ = true :=
  fieldDomB_of_fieldDomB' (fieldDomB'_of_fieldDomB'' h)

/-- A field expression with `k` operands of `n ≤ 121` words whose allocated function under
    `fieldAbi k n` passes `fnFrameFitB` and `fnArgReadersB` is in `fieldDomB''` under
    `fieldAbi k n`. The hypothesis computes the pipeline once. -/
theorem fieldDomB''_fieldAbi {e : _root_.Hax.TExpr} {k n : Nat} (h : fieldDomE e = some (k, n))
    (hn : n ≤ 121)
    (hP : (fieldAllocFn? e (fieldAbi k n)).any
      (fun f => fnFrameFitB (fieldAbi k n) f && fnArgReadersB (fieldAbi k n) f) = true) :
    fieldDomB'' e (fieldAbi k n) = true := by
  simp only [fieldDomB'', fieldDomB'_fieldAbi h (by omega), fieldFrameBoundB, h,
    decide_eq_true hn, Bool.and_self, Bool.true_and, fieldFrameFitB, fieldArgReadersB]
  cases hA : fieldAllocFn? e (fieldAbi k n) <;> simp_all

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

/-- The gate does not refuse at `frameOkB` on a body that passes the frame check. -/
theorem regionCoStage_ne_frameOkB {nm : String → String} {code : List LinstrRM}
    {res : List LOperand} {fn : String} (h : X86Backend.ImageAddrFrame.frameOkB σ b = true) :
    regionCoStage σ nm b t code res cert none fn ≠ some "frameOkB" := by
  unfold regionCoStage
  dsimp only
  simp only [h, Bool.true_eq_false, ite_false]
  repeat refine RegionCoComplete.ite_ne_some (by simp) ?_
  exact (Option.some_ne_none _).symm

/-- **Stage `G18` on the bounded field domain**: the printed body of a member is the body of
    `fieldAllocFn?` after the frame trim, which passes `frameOkB` by `fieldFrameFitB`. -/
theorem fieldDom_frameOkB (h : fieldDomB'' e σ = true) (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "frameOkB" := by
  obtain ⟨t0, q, q', P0, f, hq, hq', hx, hf, hb⟩ := fieldBody_printedBody hB
  have hF := fieldFrameFitB_of_fieldDomB'' h
  simp only [fieldFrameFitB, fnFrameFitB, fieldAllocFn?_eq hq hq' hx hf, Option.any_some,
    ← hb] at hF
  exact regionCoStage_ne_frameOkB hF

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
  rw [ite_eq_left (X86Backend.DecodePrintedAddrW.encodable_of_printedAddrWB
    (O.printedAddrWB h hB))]
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
    O.physImgB h hB, O.regionImgB h hB, fieldDom_frameOkB h hB,
    fieldDom_entryB_of_argReaders h' hB
      (argReaders_of_fieldArgReadersB (fieldArgReadersB_of_fieldDomB'' h) fname),
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

set_option linter.style.native false

/-- The product at the P-256 base prime is in the bounded field domain. -/
theorem p256Mul_fieldDomB'' : fieldDomB'' p256MulTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The square at the P-256 base prime is in the bounded field domain. -/
theorem p256Sqr_fieldDomB'' : fieldDomB'' p256SqrTE (fieldAbi 1 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The sum at the P-256 base prime is in the bounded field domain. -/
theorem p256Add_fieldDomB'' : fieldDomB'' p256AddTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The difference at the P-256 base prime is in the bounded field domain. -/
theorem p256Sub_fieldDomB'' : fieldDomB'' p256SubTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The product at the secp256k1 base prime is in the bounded field domain. -/
theorem secp256k1Mul_fieldDomB'' : fieldDomB'' secp256k1MulTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The square at the secp256k1 base prime is in the bounded field domain. -/
theorem secp256k1Sqr_fieldDomB'' : fieldDomB'' secp256k1SqrTE (fieldAbi 1 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The sum at the secp256k1 base prime is in the bounded field domain. -/
theorem secp256k1Add_fieldDomB'' : fieldDomB'' secp256k1AddTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The difference at the secp256k1 base prime is in the bounded field domain. -/
theorem secp256k1Sub_fieldDomB'' : fieldDomB'' secp256k1SubTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The product at the P-384 base prime is in the bounded field domain. -/
theorem p384Mul_fieldDomB'' : fieldDomB'' p384MulTE (fieldAbi 2 6) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The square at the P-384 base prime is in the bounded field domain. -/
theorem p384Sqr_fieldDomB'' : fieldDomB'' p384SqrTE (fieldAbi 1 6) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The sum at the P-384 base prime is in the bounded field domain. -/
theorem p384Add_fieldDomB'' : fieldDomB'' p384AddTE (fieldAbi 2 6) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The difference at the P-384 base prime is in the bounded field domain. -/
theorem p384Sub_fieldDomB'' : fieldDomB'' p384SubTE (fieldAbi 2 6) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The product at the BN254 base prime is in the bounded field domain. -/
theorem bn254Mul_fieldDomB'' : fieldDomB'' bn254MulTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The square at the BN254 base prime is in the bounded field domain. -/
theorem bn254Sqr_fieldDomB'' : fieldDomB'' bn254SqrTE (fieldAbi 1 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The sum at the BN254 base prime is in the bounded field domain. -/
theorem bn254Add_fieldDomB'' : fieldDomB'' bn254AddTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The difference at the BN254 base prime is in the bounded field domain. -/
theorem bn254Sub_fieldDomB'' : fieldDomB'' bn254SubTE (fieldAbi 2 4) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The product at the BLS12-381 base prime is in the bounded field domain. -/
theorem bls12381Mul_fieldDomB'' : fieldDomB'' bls12381MulTE (fieldAbi 2 6) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The square at the BLS12-381 base prime is in the bounded field domain. -/
theorem bls12381Sqr_fieldDomB'' : fieldDomB'' bls12381SqrTE (fieldAbi 1 6) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The sum at the BLS12-381 base prime is in the bounded field domain. -/
theorem bls12381Add_fieldDomB'' : fieldDomB'' bls12381AddTE (fieldAbi 2 6) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

/-- The difference at the BLS12-381 base prime is in the bounded field domain. -/
theorem bls12381Sub_fieldDomB'' : fieldDomB'' bls12381SubTE (fieldAbi 2 6) = true :=
  fieldDomB''_fieldAbi (by decide +kernel) (by norm_num) (by native_decide)

end Rows

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
