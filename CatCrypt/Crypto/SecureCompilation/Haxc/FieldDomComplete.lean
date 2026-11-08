/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.LeanFrontFields
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend
import CatCrypt.Crypto.SecureCompilation.Haxc.RegionStages

/-!
# Refusal completeness of `compileA` on the field domain

The field domain of the Lean front is the set of typed expressions that are one tagged call
`m#p<p>` of a prime-ir method on word-array operands, at a modulus `p ≥ 2^64` with a wide
template, under the layout `fieldAbi k n`. `fieldDomB` decides membership by reading the
expression and the layout; no stage of the compiler runs.

`compileA_isSome_of_fieldDom` states that `compileA` accepts every member, under the
hypothesis `S : FieldDomStages`. The fields of `FieldDomStages` are the stage facts, one per
refusing stage of the compiler; the docstring of each field names the row that proves it. The
proof composes them in pipeline order: the front stages `F1`-`F10`
(`haxToNF`, `extChain`, `regionExportableB`, `narrowPrep`, the legalised gate, `exportR`, the
callee table, the allocation `regionLprogC`, the first printed body, the gated encoder), the
conjuncts `G1`-`G21` of the gate `regionCoB` as named by `regionCoStage`, and the three
conjuncts `C1`-`C3` of the constant-time gate `regionCtB`. The two bridges
`regionCoB_of_regionCoStage_eq_none` and `compileRegion_isSome_of_stages` connect the stage
facts to the definitions of the gate and of the back half.

## Main definitions

* `fieldLit` — the tagged call of a method at a modulus on the operands of `ctxK k`.
* `fieldDomE` — the field expressions, with their numbers of operands and of words.
* `fieldDomB` — the field domain, as a decision on a typed expression and a layout.
* `FieldBody` — the printed body, the webs and the certificate that the stages of `compileA`
  produce on a member of the domain.

## Main results

* `fieldDomE_wide` — a field expression is the lift of `fieldLit` at a modulus with a wide
  template.
* `fieldDomB_fieldAbi` — a field expression is a member under its layout `fieldAbi k n`.
* `regionCoB_of_regionCoStage_eq_none` — no refusing stage of the gate means the gate passes.
* `compileRegion_isSome_of_stages` — the back half accepts when each of its stages does.
* `compileA_isSome_of_fieldDom` — `compileA` accepts every member of the field domain.
* `<row>_fieldDom` — the twenty field rows of `LeanFrontFields` are members.
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
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldWideInline (wideTemplateOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.LeanFrontFields (ctx1 ctx2)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (printedAddrWB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCidx (imgGateCW)
open CatCrypt.Crypto.Hax (HaxModule)
open _root_.Hax (ImpExpr ImpType)
open _root_.Hax.FieldTag (FieldMethod fieldHead fieldTag? fieldLimbs)

/-! ## 1. The field domain -/

/-- The operand types of a field call with `k` distinct operands of `n` words: `ctx2 n` for
    two operands, `ctx1 n` otherwise. -/
def ctxK (k n : Nat) : List (String × ImpType) := if k = 2 then ctx2 n else ctx1 n

/-- The literal of a tagged field call of the method `m` at the modulus `p` on the operands of
    `ctxK k`, as `reifyField%` reads it: `let t := m#p<p>(x, y); t` for two operands, and the
    call on `x, x` otherwise. -/
def fieldLit (m : FieldMethod) (p k : Nat) : ImpExpr :=
  .letBind "t"
    (.app (fieldHead m p) (if k = 2 then [.var "x", .var "y"] else [.var "x", .var "x"]))
    (.var "t")

/-- The methods of the field domain with their numbers of distinct operands: the sum, the
    difference and the product of two operands, and the square as the product of one operand
    with itself. -/
def fieldMethods : List (FieldMethod × Nat) := [(.add, 2), (.sub, 2), (.mul, 2), (.mul, 1)]

/-- The length of a word-array type. -/
def wordArrLen? : ImpType → Option Nat
  | .array (.uint .w64) n => some n
  | _ => none

/-- The register and the length of a result read back as words. -/
def resultWords? : ResultKind → Option (String × Nat)
  | .words r n => some (r, n)
  | _ => none

/-- The layout is `fieldAbi k n`, decided field by field. -/
def fieldAbiB (σ : AbiLayout) (k n : Nat) : Bool :=
  decide (σ.args = (fieldAbi k n).args) && σ.consts.isEmpty
    && resultWords? σ.result == some ("%rdi", n) && σ.bounds.isEmpty
    && σ.pubWords.isEmpty && σ.widths.isEmpty

/-- **The field expressions of the Lean front**, with their number `k` of distinct operands
    and their number `n` of words: the typed expression is `let t := f(x, y); t` (`k = 2`) or
    `let t := f(x, x); t` (`k = 1`) for a tagged head `f = m#p<p>` (with `p` in decimal,
    `fieldHead`), every node of type an array of `n = fieldLimbs p` words; the method and `k`
    are in `fieldMethods`; and `2^64 ≤ p`, `p` is odd and `n < 2^64`, so that `p` has a wide
    template (`fieldDomE_wide`). `none` on every other expression. -/
def fieldDomE (e : _root_.Hax.TExpr) : Option (Nat × Nat) :=
  match e with
  | ⟨.letBind v ⟨.app f [⟨.var a, ta⟩, ⟨.var b, tb⟩], tr⟩ ⟨.var w, tw⟩, te⟩ =>
      match fieldTag? f with
      | some (m, p) =>
          let n := fieldLimbs p
          let k := if b = "y" then 2 else 1
          if (fieldMethods.contains (m, k)
              && f.toList == m.nameChars ++ '#' :: 'p' :: _root_.Hax.FieldTag.decDigits p
              && v == "t" && w == "t" && a == "x" && (b == "y" || b == "x")
              && wordArrLen? ta == some n && wordArrLen? tb == some n
              && wordArrLen? tr == some n && wordArrLen? tw == some n
              && wordArrLen? te == some n
              && decide (2 ^ 64 ≤ p) && decide (p % 2 = 1) && decide (n < 2 ^ 64)) = true then
            some (k, n)
          else none
      | none => none
  | _ => none

/-- **The field domain of the Lean front**: a field expression (`fieldDomE`) with `k`
    distinct operands of `n` words, under the layout `fieldAbi k n`. -/
def fieldDomB (e : _root_.Hax.TExpr) (σ : AbiLayout) : Bool :=
  match fieldDomE e with
  | some (k, n) => fieldAbiB σ k n
  | none => false

/-- The layout `fieldAbi k n` passes `fieldAbiB` at `k` and `n`. -/
theorem fieldAbiB_fieldAbi (k n : Nat) : fieldAbiB (fieldAbi k n) k n = true := by
  simp [fieldAbiB, fieldAbi, resultWords?]

/-- A field expression with `k` operands of `n` words is in the field domain under
    `fieldAbi k n`. -/
theorem fieldDomB_fieldAbi {e : _root_.Hax.TExpr} {k n : Nat} (h : fieldDomE e = some (k, n)) :
    fieldDomB e (fieldAbi k n) = true := by
  simp only [fieldDomB, h, fieldAbiB_fieldAbi]

/-! ## 2. The bridges -/

/-- A step of the stage chain of the gate: when `if c = false then some s else x` is `none`,
    `c` holds and `x` is `none`. -/
theorem ite_false_eq_none {c : Bool} {s : String} {x : Option String}
    (h : (if c = false then some s else x) = none) : c = true ∧ x = none := by
  cases c <;> simp_all

/-- A step of the stage chain of the gate: when `if c = false then some s' else x` is
    `some s`, either `c` fails and `s` is `s'`, or `x` is `some s`. -/
theorem ite_false_eq_some {c : Bool} {s s' : String} {x : Option String}
    (h : (if c = false then some s' else x) = some s) : (c = false ∧ s' = s) ∨ x = some s := by
  cases c <;> simp_all

/-- **No refusing stage of the gate means the gate passes**: when `regionCoStage` names no
    conjunct, `regionCoB` holds. -/
theorem regionCoB_of_regionCoStage_eq_none {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {t : JasminTy} {code : List LinstrRM} {res : List LOperand} {cert : List (String × String)}
    {callee : Option CalleeTab} {fn : String}
    (h : regionCoStage σ nm body t code res cert callee fn = none) :
    regionCoB σ nm body t code res cert callee fn = true := by
  dsimp only [regionCoStage] at h
  obtain ⟨h1, h⟩ := ite_false_eq_none h
  obtain ⟨h2, h⟩ := ite_false_eq_none h
  obtain ⟨h3, h⟩ := ite_false_eq_none h
  obtain ⟨h4, h⟩ := ite_false_eq_none h
  obtain ⟨h5, h⟩ := ite_false_eq_none h
  obtain ⟨h6, h⟩ := ite_false_eq_none h
  obtain ⟨h7, h⟩ := ite_false_eq_none h
  obtain ⟨h8, h⟩ := ite_false_eq_none h
  obtain ⟨h9, h⟩ := ite_false_eq_none h
  obtain ⟨h10, h⟩ := ite_false_eq_none h
  obtain ⟨h11, h⟩ := ite_false_eq_none h
  obtain ⟨-, h⟩ := ite_false_eq_none h
  obtain ⟨h13, h⟩ := ite_false_eq_none h
  obtain ⟨h14, h⟩ := ite_false_eq_none h
  obtain ⟨h15, h⟩ := ite_false_eq_none h
  obtain ⟨h16, h⟩ := ite_false_eq_none h
  obtain ⟨-, h⟩ := ite_false_eq_none h
  obtain ⟨h18, h⟩ := ite_false_eq_none h
  obtain ⟨h19, h⟩ := ite_false_eq_none h
  obtain ⟨h20, h⟩ := ite_false_eq_none h
  obtain ⟨h21, h⟩ := ite_false_eq_none h
  obtain ⟨h22, h⟩ := ite_false_eq_none h
  obtain ⟨h23, -⟩ := ite_false_eq_none h
  simp only [regionCoB, renImageB, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h13, h14,
    h15, h16, h18, h19, h20, h21, h22, h23, Bool.and_self]

/-- The stages of the gate `regionCoStage` at no callee table, `G1`-`G21`, in the order of its
    definition. -/
def gateStages : List String :=
  ["coClass", "coCfgB", "coEntryFix", "renB", "coResultName", "coResultCopy", "regionResultB",
    "regMerge", "regionNopB", "fuseOKL", "fuseResultName", "regionFoldB", "ownedCheckMC",
    "idxInvCheckB", "regionPrintedB", "physImgB", "regionImgB", "frameOkB", "entryB",
    "cellNamesRB", "cellRegions"]

/-- At no callee table every stage `regionCoStage` names is in `gateStages`. -/
theorem regionCoStage_mem {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {t : JasminTy} {code : List LinstrRM} {res : List LOperand} {cert : List (String × String)}
    {fn : String} {s : String} (h : regionCoStage σ nm body t code res cert none fn = some s) :
    s ∈ gateStages := by
  dsimp only [regionCoStage] at h
  rcases ite_false_eq_some h with ⟨hc, -⟩ | h
  · simp only [Option.all_none, Bool.true_eq_false] at hc
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨hc, -⟩ | h
  · simp only [Option.all_none, Bool.true_eq_false] at hc
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  rcases ite_false_eq_some h with ⟨-, hs⟩ | h
  · simp [← hs, gateStages]
  cases h

/-- At no callee table, the gate names no refusing stage when it names none of `gateStages`. -/
theorem regionCoStage_eq_none_of_ne {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {t : JasminTy} {code : List LinstrRM} {res : List LOperand} {cert : List (String × String)}
    {fn : String} (h : ∀ s ∈ gateStages, regionCoStage σ nm body t code res cert none fn ≠ some s) :
    regionCoStage σ nm body t code res cert none fn = none := by
  cases hc : regionCoStage σ nm body t code res cert none fn with
  | none => rfl
  | some s => exact absurd hc (h s (regionCoStage_mem hc))

/-- **The back half accepts when each of its stages does**: on a program `p` that passes
    `regionExportableB`, has no `call`, and whose narrow-word stages return `q`, when the
    legalised `q` passes `regionExportableB`, its export is `r0`, its allocation is `(P, cert)`,
    the first printed body of `P` is `b`, the gated encoder accepts `b`, the gate names no
    refusing stage and the constant-time gate passes, `compileRegion` returns a result. -/
theorem compileRegion_isSome_of_stages {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    {q : NFProg jasminDialect (Γ.map NarrowWords.wideTy) [NarrowWords.wideTy t]} {r0 : Exported}
    {P : Lprog} {cert : List (String × String)} {b : Lcmd}
    (hE : regionExportableB p = true) (hcf : p.callFree = true)
    (hq : NarrowWords.narrowPrep p = some q)
    (hL : regionExportableB (legalizeRegion q) = true)
    (hr0 : exportR (Γ.map NarrowWords.wideTy).length a.fname (legalizeRegion q)
      (Γ.map NarrowWords.wideTy).length 0 = some r0)
    (hP : regionLprogC a (legalizeRegion q) none (regionWebsEx σ exportReg) = some (P, cert))
    (hb : firstBody (regionPrinted P) = some b)
    (hbs : (X86Backend.LprogBytes.encodeLfundefBytesChecked b).isSome = true)
    (hco : regionCoStage σ exportReg b (NarrowWords.wideTy t)
      (regionWebsAt (regionWebsEx σ exportReg) none r0).code
      (regionWebsAt (regionWebsEx σ exportReg) none r0).res cert none a.fname = none)
    (hct : regionCtB σ exportReg b (NarrowWords.wideTy t)
      (regionWebsAt (regionWebsEx σ exportReg) none r0).code
      (regionWebsAt (regionWebsEx σ exportReg) none r0).res cert = true) :
    (compileRegion σ a p).isSome = true := by
  have hcq : q.callFree = true := (NarrowWords.callFree_narrowPrep hq).trans hcf
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp hbs
  unfold compileRegion regionBack
  simp only [hE, hq, hL, hr0, ite_true, Option.bind_some,
    regionCallee_of_callFree (legalizeRegion_callFree hcq), hP, regionEncode, hb,
    calleeBytes_none, hbs, regionCoB_of_regionCoStage_eq_none hco, calleeCtB, hct,
    Bool.and_self, Option.isSome_some]

/-! ## 3. The front stages on the field domain -/

/-- On a member of the field domain the layout narrows no register and reads its result as
    words. -/
theorem fieldDomB_abi {e : _root_.Hax.TExpr} {σ : AbiLayout} (h : fieldDomB e σ = true) :
    σ.widths = [] ∧ ∃ r n, σ.result = .words r n := by
  unfold fieldDomB at h
  split at h
  · simp only [fieldAbiB, Bool.and_eq_true] at h
    refine ⟨List.isEmpty_iff.mp h.2, ?_⟩
    have hr := h.1.1.1.2
    cases hres : σ.result <;> simp [hres, resultWords?] at hr ⊢
  · cases h

/-- **A field expression is the call `fieldLit m p k` at a modulus with a wide template**,
    with `n = fieldLimbs p` words. -/
theorem fieldDomE_wide {e : _root_.Hax.TExpr} {k n : Nat} (h : fieldDomE e = some (k, n)) :
    ∃ m p, (m, k) ∈ fieldMethods ∧ 2 ^ 64 ≤ p ∧ (wideTemplateOf p).isSome = true
      ∧ n = fieldLimbs p ∧ e.erase = fieldLit m p k := by
  unfold fieldDomE at h
  split at h
  · rename_i v f a ta b tb tr w tw te
    split at h
    · rename_i m p hf
      simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq,
        Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_iff_mem,
        Bool.or_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm, hfl⟩, rfl⟩, rfl⟩, rfl⟩, hb⟩, -⟩, -⟩, -⟩, -⟩, -⟩, h64⟩, hp⟩, hn⟩,
        rfl, rfl⟩ := h
      obtain rfl : f = fieldHead m p :=
        String.toList_inj.mp (by rw [hfl]; simp [fieldHead])
      obtain ⟨W, hW⟩ := FieldWideInline.wideTemplateOf_isSome h64 hp hn
      refine ⟨m, p, hm, h64, by simp [hW], rfl, ?_⟩
      rcases hb with rfl | rfl <;> simp [_root_.Hax.TExpr.erase, fieldLit]
    · cases h
  · cases h

/-- Stage `F0`: on the field domain `compileA` is the hax entry at no linked function, since
    the layout narrows no register and has no pair tail. -/
theorem fieldDom_compileA_eq {e : _root_.Hax.TExpr} {σ : AbiLayout} (fname : String)
    (h : fieldDomB e σ = true) :
    compileA e σ fname = haxEntry.compileR (HaxModule.single e) σ fname := by
  obtain ⟨hw, r, n, hr⟩ := fieldDomB_abi h
  rw [pairTailOf_none_compileA_eq (by simp [pairTailOf, hr]) fname (by simp [narrowOk, hw])]
  exact linkedNil_compileARegion_eq rfl σ fname

/-- **The printed body of a member of the field domain**: `b` is the first printed body, `r`
    the webs of the export and `cert` the allocation certificate that the stages of `compileA`
    produce on `e` under `σ` and the symbol `fname`, at the result type `t` of the widened
    program. -/
def FieldBody (e : _root_.Hax.TExpr) (σ : AbiLayout) (fname : String) (b : Lcmd)
    (t : JasminTy) (r : Exported) (cert : List (String × String)) : Prop :=
  ∃ (t0 : JasminTy) (q : NFProg jasminDialect (nfCtx σ) [t0])
    (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy) [NarrowWords.wideTy t0])
    (r0 : Exported) (P : Lprog),
    haxEntry.chainNF (HaxModule.single e) σ = some ⟨t0, q⟩
      ∧ NarrowWords.narrowPrep q = some q'
      ∧ exportR ((nfCtx σ).map NarrowWords.wideTy).length fname (legalizeRegion q')
          ((nfCtx σ).map NarrowWords.wideTy).length 0 = some r0
      ∧ r = regionWebsAt (regionWebsEx σ exportReg) none r0
      ∧ regionLprogC (nfAbiNames fname σ) (legalizeRegion q') none (regionWebsEx σ exportReg)
          = some (P, cert)
      ∧ firstBody (regionPrinted P) = some b
      ∧ t = NarrowWords.wideTy t0

/-- **The stage facts of `compileA` on the field domain**, one field per refusing stage in
    pipeline order: the front stages `F1`-`F10`, the conjuncts `G1`-`G21` of the gate
    `regionCoB` as named by `regionCoStage`, and the conjuncts `C1`-`C3` of the constant-time
    gate `regionCtB`. The docstring of each field names the row that proves it. The fields
    `exportRSome`, `regionLprogCSome` and `firstBodySome` are the stages `F6`, `F8` and `F9`;
    their names carry a suffix because later field types mention `exportR`, `regionLprogC` and
    `firstBody`. -/
structure FieldDomStages : Prop where
  /-- Stage `F1`: the translation `haxToNF` refuses nothing on the field domain (`crateArrOk`,
      `haxFrontShapeOk`, `linkNameOk`). Proved by row R2. -/
  refusal {e : _root_.Hax.TExpr} {σ : AbiLayout} (h : fieldDomB e σ = true) :
    (HaxModule.single e).refusal? σ = none
  /-- Stage `F2`: on a module `refusal?` accepts, the translation and the chain `extChain`
      return a program. Proved by row R2 from `HaxModule.refusal?_eq_none_imp_extChain_isSome`. -/
  chainNF {m : HaxModule} {σ : AbiLayout} (hr : m.refusal? σ = none) :
    ∃ x, haxEntry.chainNF m σ = some x
  /-- Stage `F3`: the output of the chain on a module `refusal?` accepts passes
      `regionExportableB`. Proved by row R2 from `HaxModule.refusal?_eq_none_imp_export_isSome`. -/
  exportable {m : HaxModule} {σ : AbiLayout} {t : JasminTy}
    {q : NFProg jasminDialect (nfCtx σ) [t]} (hr : m.refusal? σ = none)
    (hq : haxEntry.chainNF m σ = some ⟨t, q⟩) : regionExportableB q = true
  /-- Stage `F4` is `NarrowWords.narrowPrep_of_exportable`. Stage `F5`: the legalised program
      passes `regionExportableB`. Proved by row R2 from `regionExportableB_legalizeRegion` and
      `regionExportableRorB_eq`. -/
  legalize {Γ : Ctxt jasminDialect} {t : JasminTy}
    {q : NFProg jasminDialect Γ [t]} (hq : regionExportableB q = true) :
    regionExportableB (legalizeRegion q) = true
  /-- Stage `F6`: the export returns code on a program that passes `regionExportableB`. Proved
      by row R2 from `exportR_isSome_of_regionExportableB`. -/
  exportRSome {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {q : NFProg jasminDialect Γ ts} (hq : regionExportableB q = true) (nArgs : Nat)
    (fn : String) (d n : Nat) : ∃ r0, exportR nArgs fn q d n = some r0
  /-- Stage `F7`: the output of the chain on the field domain has no `call`, so the callee
      table is empty (`regionCallee_of_callFree`). Proved by row R2. -/
  callFree {e : _root_.Hax.TExpr} {σ : AbiLayout} {t : JasminTy}
    {q : NFProg jasminDialect (nfCtx σ) [t]} (h : fieldDomB e σ = true)
    (hq : haxEntry.chainNF (HaxModule.single e) σ = some ⟨t, q⟩) : q.callFree = true
  /-- Stage `F8`: the allocation `regionLprogC` returns a program when the export does. Proved
      by row R2 from `regionLprog_isSome_iff_exportR`. -/
  regionLprogCSome {a : AbiNames} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {q : NFProg jasminDialect Γ [t]} {r0 : Exported} (ex : List String)
    (hr0 : exportR Γ.length a.fname q Γ.length 0 = some r0) :
    ∃ P cert, regionLprogC a q none ex = some (P, cert)
  /-- Stage `F9`: the printed program of an allocation has a first body. Proved by row R2. -/
  firstBodySome {a : AbiNames} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {q : NFProg jasminDialect Γ [t]} {ex : List String} {P : Lprog}
    {cert : List (String × String)} (hP : regionLprogC a q none ex = some (P, cert)) :
    ∃ b, firstBody (regionPrinted P) = some b
  /-- Stage `F10`: the gated encoder accepts the printed body of the field domain. Proved by row
      R5, from `encodable_of_printedAddrWB` at stage `G15`. -/
  encode {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    (X86Backend.LprogBytes.encodeLfundefBytesChecked b).isSome = true
  /-- Stage `G1`: the code with the result copies is in the class `clsB` and free of `mulx`.
      Proved by row R3, from `regionCoStage_ne_coClass`. -/
  coClass {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coClass"
  /-- Stage `G2`: the coalescing check `coCfgB`. Proved by row R3, from
      `regionCoStage_accept_of_classes`. -/
  coCfgB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coCfgB"
  /-- Stage `G3`: the entry names are fixed by the alias map. Proved by row R3, from
      `regionCoStage_accept_of_classes`. -/
  coEntryFix {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coEntryFix"
  /-- Stage `G4`: the renaming check `renB`. Proved by row R4. -/
  renB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "renB"
  /-- Stage `G5`: the observed arrays are names of the coalesced code. Proved by row R4. -/
  coResultName {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coResultName"
  /-- Stage `G6`: the result copy names are names of the coalesced code, fixed by the renaming.
      Proved by row R4. -/
  coResultCopy {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "coResultCopy"
  /-- Stage `G7`: the result check `regionResultB`. Proved by row R4. -/
  regionResultB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "regionResultB"
  /-- Stage `G8`: the merge check `regionMergeB`. Proved by row R4, from
      `mergeSep_regionLprogC_complete`. -/
  regMerge {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "regMerge"
  /-- Stage `G9`: the check `regionNopB`. Proved by row R4. -/
  regionNopB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "regionNopB"
  /-- Stage `G10`: the fusion check `fuseOKL`. Proved by row R4. -/
  fuseOKL {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "fuseOKL"
  /-- Stage `G11`: the fusion sites check `regionSitesB`. Proved by row R4. -/
  fuseResultName {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "fuseResultName"
  /-- Stage `G12`: the cell fold check `regionFoldB`. Proved by row R4. -/
  regionFoldB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "regionFoldB"
  /-- Stage `G13`: the translation validation `ownedCheckMC` of the reference against the cell
      image of the printed body. Proved by row R7b, from `ownedCheckMC_of_res` of row R7a. -/
  ownedCheckMC {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "ownedCheckMC"
  /-- Stage `G14`: the index invariant check `idxInvCheckB`. Proved by row R8. -/
  idxInvCheckB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "idxInvCheckB"
  /-- Stage `G15`: the printed body is in the class `regionPrintedB` (`printedAddrWB`). Proved by
      row R5, with the fixes of rows R5a and R6. -/
  regionPrintedB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "regionPrintedB"
  /-- Stage `G16`: the physical image check `physImgB`. Proved by row R9. -/
  physImgB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "physImgB"
  /-- Stage `G17`: the image gate `calleeImgBT none`. Proved by row R9, from
      `imgGateBW_of_legal`. -/
  regionImgB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "regionImgB"
  /-- Stage `G18`: the frame check `frameOkB`. Proved by row R4. -/
  frameOkB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "frameOkB"
  /-- Stage `G19`: the entry check `entryB`. Proved by row R4. -/
  entryB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "entryB"
  /-- Stage `G20`: the cell names check `cellNamesRB`. Proved by row R4. -/
  cellNamesRB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "cellNamesRB"
  /-- Stage `G21`: the cell regions check. Proved by row R4. -/
  cellRegions {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname ≠ some "cellRegions"
  /-- Stage `C1`: the leak check `regionLeakB`. Proved by row R3 (its first four conjuncts) and
      row R7c (`ownedCheckML`). -/
  regionLeakB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionLeakB σ exportReg b t r.code r.res cert = true
  /-- Stage `C2`: the printed body passes `printedAddrWB`. Proved by row R5. -/
  printedAddrWB {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd}
    {t : JasminTy} {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) : printedAddrWB b = true
  /-- Stage `C3`: the constant-time image gate `imgGateCW`. Proved by row R9, from
      `imgGateCW_of_imgGateBW`. -/
  imgGateCW {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
    {r : Exported} {cert : List (String × String)} (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    imgGateCW (X86Backend.ImageStraightCells.frameMarkC
        (regionCoParts σ exportReg b t r.code r.res cert).cells b)
      (regionSl σ exportReg (regionCoParts σ exportReg b t r.code r.res cert))
      (X86Backend.ImageAddrCells.cellBody
        (regionSl σ exportReg (regionCoParts σ exportReg b t r.code r.res cert)) b)
      = true

/-! ## 4. The gate stages on the field domain -/

section Gate

variable {e : _root_.Hax.TExpr} {σ : AbiLayout} {fname : String} {b : Lcmd} {t : JasminTy}
  {r : Exported} {cert : List (String × String)}

/-- The gate names no refusing stage on the field domain: stages `G1`-`G21`. -/
theorem fieldDom_regionCoStage (S : FieldDomStages) (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCoStage σ exportReg b t r.code r.res cert none fname = none := by
  refine regionCoStage_eq_none_of_ne fun s hs => ?_
  simp only [gateStages, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [S.coClass h hB, S.coCfgB h hB, S.coEntryFix h hB,
    S.renB h hB, S.coResultName h hB, S.coResultCopy h hB,
    S.regionResultB h hB, S.regMerge h hB, S.regionNopB h hB,
    S.fuseOKL h hB, S.fuseResultName h hB, S.regionFoldB h hB,
    S.ownedCheckMC h hB, S.idxInvCheckB h hB, S.regionPrintedB h hB,
    S.physImgB h hB, S.regionImgB h hB, S.frameOkB h hB,
    S.entryB h hB, S.cellNamesRB h hB, S.cellRegions h hB]

/-- The constant-time gate passes on the field domain: stages `C1`-`C3`. -/
theorem fieldDom_regionCtB (S : FieldDomStages) (h : fieldDomB e σ = true)
    (hB : FieldBody e σ fname b t r cert) :
    regionCtB σ exportReg b t r.code r.res cert = true := by
  simp only [regionCtB, S.regionLeakB h hB, S.printedAddrWB h hB,
    S.imgGateCW h hB, Bool.and_self]

end Gate

/-! ## 5. The composition -/

/-- **`compileA` accepts every member of the field domain.** The stages of `compileA` in
    pipeline order: `F0` (`fieldDom_compileA_eq`), the front `F1`-`F3`, the narrow-word stages
    `F4` (`NarrowWords.narrowPrep_of_exportable`), the legalised gate `F5`, the export `F6`,
    the empty callee table `F7`, the allocation `F8`, the first printed body `F9`, the encoder
    `F10`, the gate `G1`-`G21` (`fieldDom_regionCoStage`) and the constant-time gate `C1`-`C3`
    (`fieldDom_regionCtB`), assembled by `compileRegion_isSome_of_stages`. -/
theorem compileA_isSome_of_fieldDom (S : FieldDomStages) {e : _root_.Hax.TExpr}
    {σ : AbiLayout} (fname : String)
    (h : fieldDomB e σ = true) : (compileA e σ fname).isSome = true := by
  rw [fieldDom_compileA_eq fname h]
  unfold NFEntry.compileR
  have hr := S.refusal h
  obtain ⟨⟨t0, q⟩, hq⟩ := S.chainNF hr
  rw [hq, Option.bind_some]
  have hE := S.exportable hr hq
  obtain ⟨q', hq', hE'⟩ := NarrowWords.narrowPrep_of_exportable q hE
  have hL := S.legalize hE'
  obtain ⟨r0, hr0⟩ := S.exportRSome hL ((nfCtx σ).map NarrowWords.wideTy).length fname
    ((nfCtx σ).map NarrowWords.wideTy).length 0
  obtain ⟨P, cert, hP⟩ := S.regionLprogCSome (a := nfAbiNames fname σ)
    (regionWebsEx σ exportReg) hr0
  obtain ⟨b, hb⟩ := S.firstBodySome hP
  have hB : FieldBody e σ fname b (NarrowWords.wideTy t0)
      (regionWebsAt (regionWebsEx σ exportReg) none r0) cert :=
    ⟨t0, q, q', r0, P, hq, hq', hr0, rfl, hP, hb, rfl⟩
  exact compileRegion_isSome_of_stages hE (S.callFree h hq) hq' hL hr0 hP hb
    (S.encode h hB) (fieldDom_regionCoStage S h hB) (fieldDom_regionCtB S h hB)

/-! ## 6. The field rows of `LeanFrontFields` -/

section Rows

open CatCrypt.Crypto.SecureCompilation.Haxc.LeanFrontFields

/-- The product at the P-256 base prime is in the field domain. -/
theorem p256Mul_fieldDom : fieldDomB p256MulTE (fieldAbi 2 4) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The square at the P-256 base prime is in the field domain. -/
theorem p256Sqr_fieldDom : fieldDomB p256SqrTE (fieldAbi 1 4) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The sum at the P-256 base prime is in the field domain. -/
theorem p256Add_fieldDom : fieldDomB p256AddTE (fieldAbi 2 4) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The difference at the P-256 base prime is in the field domain. -/
theorem p256Sub_fieldDom : fieldDomB p256SubTE (fieldAbi 2 4) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The product at the secp256k1 base prime is in the field domain. -/
theorem secp256k1Mul_fieldDom : fieldDomB secp256k1MulTE (fieldAbi 2 4) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The square at the secp256k1 base prime is in the field domain. -/
theorem secp256k1Sqr_fieldDom : fieldDomB secp256k1SqrTE (fieldAbi 1 4) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The sum at the secp256k1 base prime is in the field domain. -/
theorem secp256k1Add_fieldDom : fieldDomB secp256k1AddTE (fieldAbi 2 4) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The difference at the secp256k1 base prime is in the field domain. -/
theorem secp256k1Sub_fieldDom : fieldDomB secp256k1SubTE (fieldAbi 2 4) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The product at the P-384 base prime is in the field domain. -/
theorem p384Mul_fieldDom : fieldDomB p384MulTE (fieldAbi 2 6) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The square at the P-384 base prime is in the field domain. -/
theorem p384Sqr_fieldDom : fieldDomB p384SqrTE (fieldAbi 1 6) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The sum at the P-384 base prime is in the field domain. -/
theorem p384Add_fieldDom : fieldDomB p384AddTE (fieldAbi 2 6) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The difference at the P-384 base prime is in the field domain. -/
theorem p384Sub_fieldDom : fieldDomB p384SubTE (fieldAbi 2 6) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The product at the BN254 base prime is in the field domain. -/
theorem bn254Mul_fieldDom : fieldDomB bn254MulTE (fieldAbi 2 4) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The square at the BN254 base prime is in the field domain. -/
theorem bn254Sqr_fieldDom : fieldDomB bn254SqrTE (fieldAbi 1 4) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The sum at the BN254 base prime is in the field domain. -/
theorem bn254Add_fieldDom : fieldDomB bn254AddTE (fieldAbi 2 4) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The difference at the BN254 base prime is in the field domain. -/
theorem bn254Sub_fieldDom : fieldDomB bn254SubTE (fieldAbi 2 4) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The product at the BLS12-381 base prime is in the field domain. -/
theorem bls12381Mul_fieldDom : fieldDomB bls12381MulTE (fieldAbi 2 6) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The square at the BLS12-381 base prime is in the field domain. -/
theorem bls12381Sqr_fieldDom : fieldDomB bls12381SqrTE (fieldAbi 1 6) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The sum at the BLS12-381 base prime is in the field domain. -/
theorem bls12381Add_fieldDom : fieldDomB bls12381AddTE (fieldAbi 2 6) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

/-- The difference at the BLS12-381 base prime is in the field domain. -/
theorem bls12381Sub_fieldDom : fieldDomB bls12381SubTE (fieldAbi 2 6) = true :=
  fieldDomB_fieldAbi (by decide +kernel)

end Rows

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
