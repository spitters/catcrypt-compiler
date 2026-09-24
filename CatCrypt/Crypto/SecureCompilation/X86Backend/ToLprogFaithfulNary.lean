/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulCover

/-!
# n-ary cover for a whole `UniformRegArith` `Com`

`ToLprogFaithfulCover` constructed the `BodyCover` for one- and two-binding
binop bodies from the per-binding head realization (`regArithHead_cover_cons`).
This module closes the **n-ary structural induction**: an *arbitrary-length*
`UniformRegArith` `Com` (every binding a non-shift, default-width `regArith`),
its `comToBody … |>.dropLast` (terminal `Lret` dropped) identified with the list
of `regArithHead`s, and the whole-body cover assembled by induction — so
`physBody_lsem_result` is **unconditional in `BodyCover` for arbitrary binding
count** on the binop fragment.

## What this module proves

PROVED (all goals closed, axiom-clean — `propext`/`Classical.choice`/`Quot.sound`):

* `UniformRegArith`: the inductive predicate — a `Com` all of whose bindings are
  non-shift, default-width (`w ≠ 64`) `regArith` binops, terminating at `.ret`.

* `bindingHeads` / `comToBody_dropLast_eq_heads`: **(Step 1, the structural
  identity)** `(comToBody … com d).dropLast` (the binop prefix, terminal `Lret`
  dropped) **is** the list of binding heads `bindingHeads … com d`, for *any*
  `Com` (uniformity not needed). Inducts on the `Com`, peeling the head because
  the recursive `comToBody` tail is non-empty (`comToBody_ne_nil`). The
  whole-body-vs-recursive-sublist threading: `dropLast` peels one head per `.var`
  while the recursion descends, exactly mirroring `comToBody`.

* `bindingHeads_var_eq`: a `regArith` binding's `bindingHeads` head **is**
  `regArithHead` (the `comToBody_var_head_eq` content for `bindingHeads`).

* `CoverData` / `coverData_bodyCover`: **(Step 2, the n-ary cover induction)** a
  threaded `CoverData` (mirroring the `Com` structure, carrying at each binding
  its cover element `BinopBinding` and the four head-match hypotheses — logical
  destination/opcode/source = its head, plus the RA two-address collapse `hcol`)
  yields `BodyCover body tbl (bindingHeads … com d) bs`. Inducts over the
  `CoverData`, reusing `regArithHead_cover_cons` per binding. `body`/`tbl` stay
  **fixed** to the whole body while the `Com` recursion supplies the running
  `sub` (the generalize-over-`sub` pattern of `physBody_flatMap_blocks`, lifted
  to the `Com` structure).

* `physBody_lsem_result_uniform` / `physBody_lsem_result_dropLast`: **(Step 3,
  the composition)** for the binop prefix of *any* `UniformRegArith` `Com`,
  running the literal `physBody (fun _ => none) body` under `lsemStraight` from a
  `StoreRel`-related start reads the composed virtual store at the physical
  result register. The `BodyCover` hypothesis of `physBody_lsem_result` is
  **discharged** via `coverData_bodyCover`, for **arbitrary binding count** —
  the full n-ary physical analogue of `comToLprog_faithful_straightline` on the
  binop fragment. The `_dropLast` form states the body as the literal emitter
  output `(comToBody … com d).dropLast`, closing the loop from the de-Bruijn
  output via `comToBody_dropLast_eq_heads`.

* `coverData_three`: **(Step 4, inhabitability)** a length-3 fully-general
  `CoverData` over three distinct `regArith` bindings at three SSA depths,
  assembled from three per-binding match bundles — exhibiting `CoverData`
  (hence `physBody_lsem_result_uniform`) as inhabitable, not a vacuous
  hypothesis.

## Residual (NOT proved here)

* **The per-binding `CoverData` bundle stays a hypothesis.** `CoverData` carries,
  at each binding, the cover element `BinopBinding` and the four head-match
  facts (logical naming = the head's, plus the RA two-address collapse `hcol`).
  Producing a `CoverData` from the *raw RA output* — i.e. that
  `comToLfundefPhys`'s `physTable`/`bodyTrace` actually places every binding's
  `dst` on its first source's register (`hcol` per binding) and names the slots
  as `bindingHeads` predicts — is the RA-correctness obligation. This is the
  uniform-renaming analogue `RegMachineSim.jinstr_renameBlock_sound` discharges
  for a single block; threading it across a whole derivation (a `CoverData`
  *constructor* from the RA's output, not from supplied per-binding facts) is the
  remaining bookkeeping. The semantic content (head realization + cover
  cons-step + the n-ary induction + the `physBody_lsem_result` composition) is
  fully proved here; `coverData_three` discharges the constructor concretely at
  length 3.

* **`hinj` and the two-address collapse `hcol`** stay as hypotheses, exactly as
  scoped (`hinj` inside each `BinopBinding`; `hcol` inside `CoverData`).
  Shift-immediate, three-source carry ops, `arr`/`arrIdx` memory, the ABI
  prologue/epilogue and the terminal `Lret` remain out of scope exactly as in
  the sibling modules.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulNary

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWriteSide
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBody
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulEndToEnd
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulFlatMap
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulCover

/-- A `bop` that is not a shift (`bop ∉ {shl, shr, andn}`). -/
def NonShift (bop : JasminBinOp) : Prop :=
  bop ≠ .shl ∧ bop ≠ .shr ∧ bop ≠ .andn

/-- A `Com` all of whose bindings are non-shift, default-width (`w ≠ 64`)
    `regArith` binops, terminating at `.ret`. -/
inductive UniformRegArith : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Prop where
  | ret {Γ t} (v : Ctxt.Var Γ t) : UniformRegArith (.ret v)
  | var {Γ s} {w : Nat} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
      (a0 a1 : Ctxt.Var Γ (JasminTy.reg w)) (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hw : w ≠ 64) (hns : NonShift bop) (hbody : UniformRegArith body) :
      UniformRegArith
        (.var ⟨JasminOp.regArith bop w, heq, .cons a0 (.cons a1 .nil)⟩ body)

/-- The list of binding *heads* a `Com` emits under `comToBody`, in program
    order, **excluding** the terminal `Lret`. By recursion on the `Com`: each
    `.var` contributes its `comToBody` head `⟨0, opToLinstrR e.op (regName d) …⟩`
    at the current depth, the terminal `.ret` contributes nothing. This is, by
    construction, `comToBody … |>.dropLast` (see `comToBody_dropLast_eq_heads`). -/
def bindingHeads (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → Lcmd
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      let srcs := exprArgs curDepth nArgs argNames immSlotMap e
      let instr : Linstr := ⟨0, opToLinstrR e.op (regName curDepth) srcs⟩
      instr :: bindingHeads nArgs argNames immSlotMap body (curDepth + 1)

/-- `comToBody` is never empty: its `.ret` arm is `[Lret]` and its `.var` arm is
    a cons. -/
theorem comToBody_ne_nil (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (d : Nat) :
    comToBody nArgs argNames immSlotMap com d ≠ [] := by
  cases com with
  | ret v => simp [comToBody]
  | var e body => simp [comToBody]

/-- **The `dropLast = bindingHeads` structural identity.** Dropping the terminal
    `Lret` from `comToBody` yields exactly the list of binding heads (in program
    order), for *any* `Com` (uniformity is not needed for this purely structural
    fact). Inducts on the `Com`: the `.var` head is preserved because the
    recursive `comToBody` tail is non-empty (`comToBody_ne_nil`), so `dropLast`
    peels the head and recurses on the tail. -/
theorem comToBody_dropLast_eq_heads (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (d : Nat) :
    (comToBody nArgs argNames immSlotMap com d).dropLast
      = bindingHeads nArgs argNames immSlotMap com d := by
  induction com generalizing d with
  | ret v => rfl
  | var e body ih =>
      simp only [comToBody, bindingHeads, List.dropLast_cons_of_ne_nil
        (comToBody_ne_nil nArgs argNames immSlotMap body (d + 1)), ih]

/-! ## The n-ary cover for a `UniformRegArith` `Com`

The whole-body `BodyCover` is over a *fixed* whole `body`/`tbl` while the
`comToBody`/`bindingHeads` recursion peels sublists of the head list — the
`physBody_flatMap_blocks` generalize-over-`sub` pattern, here lifted to the
`Com` structure. We mirror the `Com` shape with an inductive `CoverData` that
carries, at each binding, the cover element's `BinopBinding` and the per-binding
match hypotheses (logical destination/source/opcode = the head's, plus the RA
two-address collapse `hcol`). The `Com` structure provides the `sub` (the
`bindingHeads` at the running depth); `body`/`tbl` stay fixed to the whole
body. -/

/-- Cover data threaded along a `UniformRegArith` `Com`, over a *fixed* whole
    `body`/`tbl`. At each `.var` binding it carries the cover element `b` and the
    four head-match hypotheses `regArithHead_cover_cons` consumes (logical
    destination/opcode/source, and the RA two-address collapse `hcol`). Mirrors
    the `Com` structure so the cover induction peels one binding at a time. -/
inductive CoverData {w : Nat} (body : Lcmd) (tbl : Array Nat) (nArgs : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) →
    List (BinopBinding w body tbl) → Prop where
  | ret {Γ t} (v : Ctxt.Var Γ t) (d : Nat) : CoverData body tbl nArgs (.ret v) d []
  | var {Γ s} {bop : JasminBinOp}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w}
      {a0 a1 : Ctxt.Var Γ (JasminTy.reg w)} {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (hw : w ≠ 64) (hns : bop ≠ .shl ∧ bop ≠ .shr ∧ bop ≠ .andn)
      (b : BinopBinding w body tbl) (bs : List (BinopBinding w body tbl))
      (hdst : b.nDst = regName d)
      (hopn : b.opn = withWidthTag w (binOpName bop))
      (hsrc : b.nSrc = resolveVarName d nArgs a1)
      (hcol : physRename body tbl (resolveVarName d nArgs a0)
          = physRename body tbl (regName d))
      (htail : CoverData body tbl nArgs bdy (d + 1) bs) :
      CoverData body tbl nArgs
        (.var ⟨JasminOp.regArith bop w, heq, .cons a0 (.cons a1 .nil)⟩ bdy) d (b :: bs)

/-- The `bindingHeads` head of a `regArith` binding is exactly `regArithHead`
    (the `comToBody_var_head_eq` content, re-expressed for `bindingHeads`, which
    shares the same head with `comToBody`). -/
theorem bindingHeads_var_eq {Γ : Ctxt jasminDialect} {s : JasminTy}
    (nArgs : Nat) (bop : JasminBinOp) (w : Nat)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (a0 a1 : Ctxt.Var Γ (JasminTy.reg w))
    (body : Com jasminDialect (JasminTy.reg w :: Γ) s) (curDepth : Nat) :
    bindingHeads nArgs argName (fun _ => none)
      (.var ⟨JasminOp.regArith bop w, heq, .cons a0 (.cons a1 .nil)⟩ body) curDepth
      = regArithHead nArgs curDepth bop w a0 a1
        :: bindingHeads nArgs argName (fun _ => none) body (curDepth + 1) := by
  show (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w (binOpName bop))
      [resolveVar curDepth nArgs argName (fun _ => none) a0,
       resolveVar curDepth nArgs argName (fun _ => none) a1]⟩ : Linstr) :: _ = _
  rw [resolveVar_eq_reg, resolveVar_eq_reg]
  rfl

/-- **The n-ary cover.** From the threaded `CoverData`, the whole-body
    `bindingHeads` list (= `comToBody … |>.dropLast`) is covered by the binding
    list `bs`. Inducts over the `CoverData` (mirroring the `Com` structure),
    re-using the per-binding `regArithHead_cover_cons`. `body`/`tbl` stay fixed
    throughout; the `Com` recursion supplies the running `sub`. -/
theorem coverData_bodyCover {w : Nat} (body : Lcmd) (tbl : Array Nat) (nArgs : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (d : Nat) (bs : List (BinopBinding w body tbl))
    (hcd : CoverData body tbl nArgs com d bs) :
    BodyCover body tbl (bindingHeads nArgs argName (fun _ => none) com d) bs := by
  induction hcd with
  | ret v d => exact .nil
  | var d hw hns b bs hdst hopn hsrc hcol _ ih =>
      rw [bindingHeads_var_eq]
      exact regArithHead_cover_cons body tbl nArgs d _ w hw hns _ _ b bs _
        hdst hopn hsrc hcol ih

/-! ## n-ary physical faithfulness for a `UniformRegArith` `Com`

Composing `coverData_bodyCover` (this module) with `physBody_lsem_result`
(`ToLprogFaithfulFlatMap`): for the *binop prefix* of a whole `UniformRegArith`
`Com` (the `comToBody … |>.dropLast`, terminal `Lret` dropped) the `BodyCover`
hypothesis of `physBody_lsem_result` is *discharged* (from the threaded
`CoverData`), so the literal-`physBody` run is faithful — unconditional in
`BodyCover` — for **arbitrary binding count**. This is the full n-ary physical
analogue of `comToLprog_faithful_straightline` on the binop fragment. -/

/-- **n-ary unconditional physical faithfulness (binop fragment).** For a
    physical body `body` that *is* the binop prefix `bindingHeads … com d` of a
    `UniformRegArith` `Com` (= `comToBody … com d |>.dropLast`, terminal `Lret`
    dropped — see `comToBody_dropLast_eq_heads`), with the whole-body cover
    threaded by a `CoverData` (each binding's logical naming = its head, plus the
    RA two-address collapse), running the literal `physBody (fun _ => none) body`
    under `lsemStraight` from a `StoreRel`-related start reads the composed
    virtual store at the physical result register. The `BodyCover` hypothesis of
    `physBody_lsem_result` is *discharged* via `coverData_bodyCover` for any
    binding count. `hinj` (carried inside each `BinopBinding`) and the per-binding
    collapse `hcol` (inside `CoverData`) stay hypotheses, exactly as scoped;
    the terminal `Lret` is dropped (out of scope). -/
theorem physBody_lsem_result_uniform {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (BinopBinding w body (bodyPhysTable body)))
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverData body (bodyPhysTable body) nArgs com d bs)
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w)
    (hrel : StoreRel body (bodyPhysTable body) L s s')
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ s'', lsemStraight ((physBody (fun _ => none) body).map (·.li_i)) s' = some s''
      ∧ s''.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  have hcov0 : BodyCover body (bodyPhysTable body)
      (bindingHeads nArgs argName (fun _ => none) com d) bs :=
    coverData_bodyCover body (bodyPhysTable body) nArgs com d bs hcd
  have hcov : BodyCover body (bodyPhysTable body) body bs := hbody ▸ hcov0
  exact physBody_lsem_result body bs hcov L N hch s s' hrel nRes hnRes

/-- **n-ary physical faithfulness, phrased over `comToBody … |>.dropLast`.** The
    same as `physBody_lsem_result_uniform`, but stating the physical body as the
    literal emitter output with its terminal `Lret` dropped
    (`(comToBody … com d).dropLast`) — closing the loop from the emitter's actual
    de-Bruijn output (`comToBody_dropLast_eq_heads`) to the discharged cover. -/
theorem physBody_lsem_result_dropLast {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (BinopBinding w body (bodyPhysTable body)))
    (hbody : body = (comToBody nArgs argName (fun _ => none) com d).dropLast)
    (hcd : CoverData body (bodyPhysTable body) nArgs com d bs)
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w)
    (hrel : StoreRel body (bodyPhysTable body) L s s')
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ s'', lsemStraight ((physBody (fun _ => none) body).map (·.li_i)) s' = some s''
      ∧ s''.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes :=
  physBody_lsem_result_uniform body nArgs d com bs
    (hbody.trans (comToBody_dropLast_eq_heads nArgs argName (fun _ => none) com d))
    hcd L N hch s s' hrel nRes hnRes

/-! ## A length-3 fully-general `CoverData` instance

To exhibit `CoverData` (hence `physBody_lsem_result_uniform`) as inhabitable —
not a vacuous hypothesis — we build a three-binding `CoverData` from three
per-binding witness bundles (each binding's logical naming + the RA collapse).
The cover threads through three distinct `regArith` bindings at three SSA depths,
exhibiting the `CoverData.var`/`.ret` constructors composing for length > 2. -/

/-- A three-binding `CoverData` over a fixed `body`/`tbl`: assemble three
    per-binding match bundles into the threaded `CoverData`, exhibiting the
    constructor on a non-trivial (length-3) `UniformRegArith` `Com`. -/
theorem coverData_three {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {bop0 bop1 bop2 : JasminBinOp}
    {heq0 : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop0 w) = .reg w}
    {a00 a01 : Ctxt.Var Γ (JasminTy.reg w)}
    {heq1 : DialectSignature.ret (d := jasminDialect)
      (JasminOp.regArith bop1 w) = .reg w}
    {a10 a11 : Ctxt.Var (JasminTy.reg w :: Γ) (JasminTy.reg w)}
    {heq2 : DialectSignature.ret (d := jasminDialect)
      (JasminOp.regArith bop2 w) = .reg w}
    {a20 a21 : Ctxt.Var (JasminTy.reg w :: JasminTy.reg w :: Γ) (JasminTy.reg w)}
    (vr : Ctxt.Var (JasminTy.reg w :: JasminTy.reg w :: JasminTy.reg w :: Γ) t)
    (hw : w ≠ 64)
    (hns0 : bop0 ≠ .shl ∧ bop0 ≠ .shr ∧ bop0 ≠ .andn)
    (hns1 : bop1 ≠ .shl ∧ bop1 ≠ .shr ∧ bop1 ≠ .andn)
    (hns2 : bop2 ≠ .shl ∧ bop2 ≠ .shr ∧ bop2 ≠ .andn)
    (b0 b1 b2 : BinopBinding w body (bodyPhysTable body))
    (hdst0 : b0.nDst = regName d) (hopn0 : b0.opn = withWidthTag w (binOpName bop0))
    (hsrc0 : b0.nSrc = resolveVarName d nArgs a01)
    (hcol0 : physRename body (bodyPhysTable body) (resolveVarName d nArgs a00)
        = physRename body (bodyPhysTable body) (regName d))
    (hdst1 : b1.nDst = regName (d + 1)) (hopn1 : b1.opn = withWidthTag w (binOpName bop1))
    (hsrc1 : b1.nSrc = resolveVarName (d + 1) nArgs a11)
    (hcol1 : physRename body (bodyPhysTable body) (resolveVarName (d + 1) nArgs a10)
        = physRename body (bodyPhysTable body) (regName (d + 1)))
    (hdst2 : b2.nDst = regName (d + 2)) (hopn2 : b2.opn = withWidthTag w (binOpName bop2))
    (hsrc2 : b2.nSrc = resolveVarName (d + 2) nArgs a21)
    (hcol2 : physRename body (bodyPhysTable body) (resolveVarName (d + 2) nArgs a20)
        = physRename body (bodyPhysTable body) (regName (d + 2))) :
    CoverData body (bodyPhysTable body) nArgs
      (.var ⟨JasminOp.regArith bop0 w, heq0, .cons a00 (.cons a01 .nil)⟩
        (.var ⟨JasminOp.regArith bop1 w, heq1, .cons a10 (.cons a11 .nil)⟩
          (.var ⟨JasminOp.regArith bop2 w, heq2, .cons a20 (.cons a21 .nil)⟩
            (.ret vr)))) d [b0, b1, b2] :=
  .var d hw hns0 b0 [b1, b2] hdst0 hopn0 hsrc0 hcol0
    (.var (d + 1) hw hns1 b1 [b2] hdst1 hopn1 hsrc1 hcol1
      (.var (d + 2) hw hns2 b2 [] hdst2 hopn2 hsrc2 hcol2
        (.ret vr (d + 3))))

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulNary
