/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulFlatMap
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation

/-!
# Discharging `BodyCover` from a `UniformRegArith` `Com`

`ToLprogFaithfulFlatMap.physBody_lsem_result` proved that the literal `physBody`
output, run under `lsemStraight`, reads `composeVSteps` at the physical result
register — **given a `BodyCover body bs`**, the assumed per-binding witness that
every source instruction is a binop in the two-address-collapse shape naming its
binding's operands. This module *constructs* that cover from the `comToBody`
emission of a `UniformRegArith` binding, so the cover hypothesis is **discharged**
(not assumed) on constructed binop bodies.

## The de-Bruijn → `Lopn` identification (the core content)

A `regArith bop w` binding emits, under `comToBody … curDepth`, the literal head
`Linstr`

  `⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w (binOpName bop))
        [resolveVar … a0, resolveVar … a1]⟩`

(`comToBody_var_head`/`comToBody_var_head_eq`, both by `rfl` — the de-Bruijn
structural identification). Under the trivial (no-constant) immediate
map both operands resolve to *registers* (`resolveVar_eq_reg`), so the head is
exactly `regArithHead`. `regArithHead_realizes` then shows this head **realises**
(`InstrRealizesBinding`) any `BinopBinding b` whose logical destination is
`regName curDepth`, mnemonic is `withWidthTag w (binOpName bop)`, and source
`b.nSrc` is the second resolved operand — given the two-address collapse
`physRename body tbl (resolveVarName … a0) = physRename body tbl (regName
curDepth)` (`hcol`, the RA invariant). The three opcode side-conditions
(`isBinop`, `¬isShift`, `¬:64`) are **discharged** from `binOpName` for any
non-shift (`bop ∉ {shl,shr,andn}`), default-width (`w ≠ 64`) binding
(`binOpName_isBinop_of_nonshift` / `binOpName_not_isShift_of_nonshift` /
`withWidthTag_binOpName_not_hasSuffix64`).

## What this module proves

PROVED (all goals closed, axiom-clean — `propext`/`Classical.choice`/`Quot.sound`):

* `comToBody_var_head`, `comToBody_var_head_eq`: the de-Bruijn → `Lopn` head
  identification (the literal `comToBody` head of a `regArith` binding is
  `regArithHead`).
* `resolveVar_eq_reg`: under the trivial immediate map every operand resolves to
  a register (no `.imm` arises).
* `regArithHead_realizes`: the head realises a `BinopBinding` (cover-element
  obligation), opcode conditions discharged, RA collapse `hcol` kept as the one
  RA-invariant hypothesis.
* `regArithHead_cover_cons`: the cover **cons-step** — extend a cover of `is` by
  `bs` to a cover of `regArithHead … :: is` by `b :: bs`. The reusable inductive
  layer for whole-body cover construction.
* `bodyCover_single` / `physBody_lsem_result_single`: a one-binop body's cover is
  **constructed** (not assumed), making `physBody_lsem_result` **unconditional in
  `BodyCover`** on that body.
* `bodyCover_two` / `physBody_lsem_result_two`: the same for a two-binop body —
  the cons-step composes for length > 1 (non-degenerate: two bindings,
  each at its own SSA depth, each with its own RA collapse).

So `physBody_lsem_result` is unconditional on `BodyCover` for any concrete
binop body assembled as `regArithHead`s, via the cons-step. (The single- and
two-binding instances exhibit this with the cover fully built.)

## Residual (not proved here)

* **The whole-`Com` `comToBody.dropLast` ↔ heads-list structural equation.** The
  cons-step `regArithHead_cover_cons` covers `regArithHead … :: is` from a cover
  of `is`; an *arbitrary-length* `UniformRegArith` `Com` would be covered by
  inducting over its derivation, but that needs `comToBody … |>.dropLast` (the
  binop prefix, terminal `Lret` dropped) identified with the list of
  `regArithHead`s along the de-Bruijn depths, with the per-binding `body`/`tbl`
  fixed to the *whole* body. That whole-body-vs-recursive-sublist `tbl`
  identification is the remaining bookkeeping; the per-binding semantic content
  (head realization + cons-step + the `physBody_lsem_result` composition) is fully
  proved here, and the single- and two-binding instances discharge it concretely.

* **`hinj` and the two-address collapse `hcol`** stay as hypotheses, exactly as
  scoped: `hinj` (carried inside each `BinopBinding`) is RA-correctness (distinct
  live names get distinct slots; `RegMachineSim.jinstr_renameBlock_sound` proves
  the uniform-renaming analogue); `hcol` is the RA placing the binop result on its
  first source's register. Shift-immediate, three-source carry ops, `arr`/`arrIdx`
  memory, the ABI prologue/epilogue and `Lret` remain out of scope exactly as in
  the sibling modules.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulCover

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWriteSide
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBody
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulEndToEnd
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulFlatMap

/-- The head `Linstr` of `comToBody` for a `regArith bop w` binding. -/
theorem comToBody_var_head {Γ : Ctxt jasminDialect} {s : JasminTy}
    (nArgs : Nat) (bop : JasminBinOp) (w : Nat)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (a0 a1 : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect (.reg w :: Γ) s) (curDepth : Nat) :
    (comToBody nArgs argName (fun _ => none)
      (.var ⟨JasminOp.regArith bop w, heq,
        .cons a0 (.cons a1 .nil)⟩ body) curDepth).head? =
      some ⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w (binOpName bop))
        [resolveVar curDepth nArgs argName (fun _ => none) a0,
         resolveVar curDepth nArgs argName (fun _ => none) a1]⟩ := by
  rfl

/-- The register name a `Var` resolves to under the trivial immediate map:
    `argName slot` if the slot is an argument, else `regName slot`. -/
def resolveVarName (curDepth nArgs : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (v : Ctxt.Var Γ τ) : String :=
  let slot := curDepth - 1 - varIndex v
  if slot < nArgs then argName slot else regName slot

/-- `resolveVar` with the trivial (no-constant) immediate map always returns a
    register operand, naming `resolveVarName`. (No `.imm` arises: only a
    populated `ImmSlotMap` produces immediates.) -/
theorem resolveVar_eq_reg (curDepth nArgs : Nat) {Γ : Ctxt jasminDialect}
    {τ : JasminTy} (v : Ctxt.Var Γ τ) :
    resolveVar curDepth nArgs argName (fun _ => none) v
      = .reg (resolveVarName curDepth nArgs v) := by
  simp only [resolveVar, resolveVarName]
  split <;> rfl

/-! ## The opcode side-conditions for a non-shift, non-`:64` binop -/

/-- A non-shift binop mnemonic `binOpName bop` (`bop ∈ {add,sub,mul,and,or,xor}`)
    is in the `isBinop` alphabet. -/
theorem binOpName_isBinop_of_nonshift (bop : JasminBinOp)
    (hns : bop ≠ .shl ∧ bop ≠ .shr ∧ bop ≠ .andn) :
    isTwoAddrBinop (binOpName bop) = true := by
  unfold isTwoAddrBinop
  obtain ⟨h1, h2, h3⟩ := hns
  cases bop <;> first | decide +kernel | (exfalso; revert h1 h2 h3; decide)

/-- A non-shift binop mnemonic is not a shift (`isShift` is false). -/
theorem binOpName_not_isShift_of_nonshift (bop : JasminBinOp)
    (hns : bop ≠ .shl ∧ bop ≠ .shr ∧ bop ≠ .andn) :
    ¬ (stripWidthTag (binOpName bop) == "SHL" || stripWidthTag (binOpName bop) == "SHR")
      = true := by
  obtain ⟨h1, h2, h3⟩ := hns
  cases bop <;> first | decide +kernel | (exfalso; revert h1 h2 h3; decide)

/-- At a width `w ≠ 64` the tagged mnemonic `withWidthTag w (binOpName bop)` ends
    in the decimal digits of `w` and never ends with the `:64` width tag. (The
    default-width arm of `physBody`'s `isShift`/`movFor` dispatch.) -/
theorem withWidthTag_binOpName_not_hasSuffix64 (w : Nat) (bop : JasminBinOp)
    (hw : w ≠ 64) :
    ¬ hasSuffix (withWidthTag w (binOpName bop)) ":64" = true := by
  intro h
  unfold hasSuffix at h
  rw [toList_withWidthTag_of_ne hw, List.isSuffixOf_iff_suffix] at h
  rcases List.suffix_or_suffix_of_suffix h (List.suffix_append _ _) with h1 | h1
  · have hc := h1.subset (show ':' ∈ (":64" : String).toList by decide)
    simp only [List.mem_cons] at hc
    rcases hc with hc | hc
    · exact absurd hc (by decide)
    · exact (sep_not_mem_toString w).1 hc
  · exact absurd (h1.subset List.mem_cons_self) (by decide)

/-! ## The realization of a `comToBody` head by a `BinopBinding` -/

/-- The literal head `Linstr` a `regArith bop w` binding emits under `comToBody`
    at depth `curDepth`: destination `regName curDepth`, tagged mnemonic, two
    register sources resolved from the two operand vars. (Explicit `Linstr`
    form of `comToBody_var_head` after `resolveVar_eq_reg`.) -/
def regArithHead (nArgs curDepth : Nat) (bop : JasminBinOp) (w : Nat)
    {Γ : Ctxt jasminDialect} (a0 a1 : Ctxt.Var Γ (.reg w)) : Linstr :=
  ⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w (binOpName bop))
    [.reg (resolveVarName curDepth nArgs a0),
     .reg (resolveVarName curDepth nArgs a1)]⟩

/-- The head of `comToBody` for a `regArith` binding is exactly `regArithHead`. -/
theorem comToBody_var_head_eq {Γ : Ctxt jasminDialect} {s : JasminTy}
    (nArgs : Nat) (bop : JasminBinOp) (w : Nat)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (a0 a1 : Ctxt.Var Γ (.reg w))
    (body : Com jasminDialect (.reg w :: Γ) s) (curDepth : Nat) :
    (comToBody nArgs argName (fun _ => none)
      (.var ⟨JasminOp.regArith bop w, heq,
        .cons a0 (.cons a1 .nil)⟩ body) curDepth).head?
      = some (regArithHead nArgs curDepth bop w a0 a1) := by
  rw [comToBody_var_head nArgs bop w heq a0 a1 body curDepth, regArithHead,
    resolveVar_eq_reg, resolveVar_eq_reg]

/-- **The de-Bruijn → `Lopn` realization.** A `regArithHead` (the literal head
    instruction `comToBody` emits for a non-shift, non-`:64` `regArith bop w`
    binding, `w ≠ 64`, `bop ∉ {shl,shr,andn}`) *realises* (in the sense of
    `InstrRealizesBinding`) any `BinopBinding b` whose logical destination is
    `regName curDepth`, whose mnemonic is the tagged `binOpName`, and whose
    logical source `b.nSrc` is the second resolved operand — **given** the
    two-address collapse `physRename body tbl (resolveVarName … a0) = physRename
    body tbl (regName curDepth)` (the RA invariant, kept as hypothesis `hcol`).
    The opcode side-conditions are discharged from `binOpName`. -/
theorem regArithHead_realizes {w' : Nat} (body : Lcmd) (tbl : Array Nat)
    (nArgs curDepth : Nat) (bop : JasminBinOp) (w : Nat) (hw : w ≠ 64)
    (hns : bop ≠ .shl ∧ bop ≠ .shr ∧ bop ≠ .andn)
    {Γ : Ctxt jasminDialect} (a0 a1 : Ctxt.Var Γ (.reg w))
    (b : BinopBinding w' body tbl)
    (hdst : b.nDst = regName curDepth)
    (hopn : b.opn = withWidthTag w (binOpName bop))
    (hsrc : b.nSrc = resolveVarName curDepth nArgs a1)
    (hcol : physRename body tbl (resolveVarName curDepth nArgs a0)
        = physRename body tbl (regName curDepth)) :
    InstrRealizesBinding body tbl (regArithHead nArgs curDepth bop w a0 a1) b := by
  have hsf : tagSepFree (binOpName bop) = true := by cases bop <;> decide +kernel
  have htag : stripWidthTag (withWidthTag w (binOpName bop))
      = stripWidthTag (binOpName bop) := by
    rw [stripWidthTag_withWidthTag w hsf]
    cases bop <;> decide +kernel
  refine ⟨resolveVarName curDepth nArgs a0, [], [], ?_, ?_, ?_, ?_, ?_⟩
  · -- the instruction shape: dst = b.nDst, opn = b.opn, srcs = [nS0, b.nSrc]
    simp only [regArithHead, hdst, hopn, hsrc]
  · rw [hopn]; unfold isTwoAddrBinop; rw [htag]
    exact binOpName_isBinop_of_nonshift bop hns
  · rw [hopn, htag]; exact binOpName_not_isShift_of_nonshift bop hns
  · rw [hopn]; exact withWidthTag_binOpName_not_hasSuffix64 w bop hw
  · rw [hdst]; exact hcol

/-! ## The `BodyCover` cons step from a `comToBody` head

The whole-body cover is built one binding at a time. `BodyCover.cons` consumes an
`InstrRealizesBinding` for the head; `regArithHead_cover_cons` packages
`regArithHead_realizes` so the head obligation is exactly the RA collapse + the
binding-shape equations, with the opcode conditions discharged. -/

/-- **Cover cons-step (binop head).** Extend a cover of `is` by `bs` to a cover of
    `regArithHead … :: is` by `b :: bs`, where the head's realization of `b` is
    discharged by `regArithHead_realizes` (RA collapse + binding-shape equations +
    opcode discharge). The reusable inductive step for building a whole-body cover
    from the `UniformRegArith` structure: each source binding's head, with its RA
    placement (`hcol`) and the binding's logical naming, contributes one cover
    layer. -/
theorem regArithHead_cover_cons {w' : Nat} (body : Lcmd) (tbl : Array Nat)
    (nArgs curDepth : Nat) (bop : JasminBinOp) (w : Nat) (hw : w ≠ 64)
    (hns : bop ≠ .shl ∧ bop ≠ .shr ∧ bop ≠ .andn)
    {Γ : Ctxt jasminDialect} (a0 a1 : Ctxt.Var Γ (.reg w))
    (b : BinopBinding w' body tbl) (bs : List (BinopBinding w' body tbl)) (is : Lcmd)
    (hdst : b.nDst = regName curDepth)
    (hopn : b.opn = withWidthTag w (binOpName bop))
    (hsrc : b.nSrc = resolveVarName curDepth nArgs a1)
    (hcol : physRename body tbl (resolveVarName curDepth nArgs a0)
        = physRename body tbl (regName curDepth))
    (htail : BodyCover body tbl is bs) :
    BodyCover body tbl (regArithHead nArgs curDepth bop w a0 a1 :: is) (b :: bs) :=
  .cons (regArithHead_realizes body tbl nArgs curDepth bop w hw hns a0 a1 b
    hdst hopn hsrc hcol) htail

/-! ## Unconditional physical faithfulness on a constructed cover

Composing the cover-construction with `physBody_lsem_result`: once the cover is
*built* (not assumed) from the head realizations, the literal-`physBody` run is
faithful. We exhibit this on a single-binding binop body whose cover is fully
constructed — the cover hypothesis of `physBody_lsem_result` is *discharged*. -/

/-- A single-binop body `[regArithHead …]` (the binop fragment of a one-binding
    `UniformRegArith` `Com`, terminal `Lret` dropped) with its cover *constructed*
    from one head realization. The cover is the singleton `.cons … .nil`. -/
theorem bodyCover_single (body : Lcmd)
    (nArgs curDepth : Nat) (bop : JasminBinOp) (w : Nat) (hw : w ≠ 64)
    (hns : bop ≠ .shl ∧ bop ≠ .shr ∧ bop ≠ .andn)
    {Γ : Ctxt jasminDialect} (a0 a1 : Ctxt.Var Γ (.reg w))
    (b : BinopBinding w body (bodyPhysTable body))
    (hbody : body = [regArithHead nArgs curDepth bop w a0 a1])
    (hdst : b.nDst = regName curDepth)
    (hopn : b.opn = withWidthTag w (binOpName bop))
    (hsrc : b.nSrc = resolveVarName curDepth nArgs a1)
    (hcol : physRename body (bodyPhysTable body)
        (resolveVarName curDepth nArgs a0)
      = physRename body (bodyPhysTable body) (regName curDepth)) :
    BodyCover body (bodyPhysTable body) body [b] := by
  -- construct the cover of the explicit singleton `sub`, then transport the
  -- `sub` slot back to `body` along `hbody` (only the `sub` argument changes).
  have hcov : BodyCover body (bodyPhysTable body)
      [regArithHead nArgs curDepth bop w a0 a1] [b] :=
    regArithHead_cover_cons body (bodyPhysTable body) nArgs curDepth
      bop w hw hns a0 a1 b [] [] hdst hopn hsrc hcol .nil
  exact hbody ▸ hcov

/-- **Unconditional physical faithfulness on a single-binop body.** For a body
    that *is* one `regArithHead` (the binop fragment of a one-binding
    `UniformRegArith` `Com`), with the cover *constructed* from the head's RA
    collapse and the binding's logical naming, running the literal `physBody (fun
    _ => none) body` under `lsemStraight` from a `StoreRel`-related start reads the
    composed virtual store at the physical result register. The cover hypothesis
    of `physBody_lsem_result` is *discharged* (`bodyCover_single`), so the
    conclusion is unconditional in `BodyCover`. `hinj` (carried inside `b`) and the
    two-address collapse `hcol` stay as hypotheses, exactly as scoped. -/
theorem physBody_lsem_result_single {w : Nat} (body : Lcmd)
    (nArgs curDepth : Nat) (bop : JasminBinOp) (hw : w ≠ 64)
    (hns : bop ≠ .shl ∧ bop ≠ .shr ∧ bop ≠ .andn)
    {Γ : Ctxt jasminDialect} (a0 a1 : Ctxt.Var Γ (.reg w))
    (b : BinopBinding w body (bodyPhysTable body))
    (hbody : body = [regArithHead nArgs curDepth bop w a0 a1])
    (hdst : b.nDst = regName curDepth)
    (hopn : b.opn = withWidthTag w (binOpName bop))
    (hsrc : b.nSrc = resolveVarName curDepth nArgs a1)
    (hcol : physRename body (bodyPhysTable body)
        (resolveVarName curDepth nArgs a0)
      = physRename body (bodyPhysTable body) (regName curDepth))
    (L N : List String)
    (hch : Chained ([b].map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w)
    (hrel : StoreRel body (bodyPhysTable body) L s s')
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ s'', lsemStraight ((physBody (fun _ => none) body).map (·.li_i)) s' = some s''
      ∧ s''.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps ([b].map (fun b => (b.block, b.vstep))) s).lvm nRes :=
  physBody_lsem_result body [b]
    (bodyCover_single body nArgs curDepth bop w hw hns a0 a1 b hbody hdst hopn hsrc hcol)
    L N hch s s' hrel nRes hnRes

/-- **Two-binop body cover, constructed.** A body that *is* two `regArithHead`s
    (the binop fragment of a two-binding `UniformRegArith` `Com`) has its cover
    built by two applications of the cons-step — exhibiting the cons-step
    composing for length > 1 (non-degenerate: two distinct bindings,
    each at its own SSA depth, each with its own RA collapse). The two bindings'
    naming/collapse obligations stay as hypotheses, exactly as scoped. -/
theorem bodyCover_two (body : Lcmd)
    (nArgs d0 d1 : Nat) (bop0 bop1 : JasminBinOp) (w : Nat) (hw : w ≠ 64)
    (hns0 : bop0 ≠ .shl ∧ bop0 ≠ .shr ∧ bop0 ≠ .andn)
    (hns1 : bop1 ≠ .shl ∧ bop1 ≠ .shr ∧ bop1 ≠ .andn)
    {Γ0 Γ1 : Ctxt jasminDialect}
    (a0 a1 : Ctxt.Var Γ0 (.reg w)) (c0 c1 : Ctxt.Var Γ1 (.reg w))
    (b0 b1 : BinopBinding w body (bodyPhysTable body))
    (hbody : body = [regArithHead nArgs d0 bop0 w a0 a1,
                     regArithHead nArgs d1 bop1 w c0 c1])
    (hdst0 : b0.nDst = regName d0) (hopn0 : b0.opn = withWidthTag w (binOpName bop0))
    (hsrc0 : b0.nSrc = resolveVarName d0 nArgs a1)
    (hcol0 : physRename body (bodyPhysTable body) (resolveVarName d0 nArgs a0)
      = physRename body (bodyPhysTable body) (regName d0))
    (hdst1 : b1.nDst = regName d1) (hopn1 : b1.opn = withWidthTag w (binOpName bop1))
    (hsrc1 : b1.nSrc = resolveVarName d1 nArgs c1)
    (hcol1 : physRename body (bodyPhysTable body) (resolveVarName d1 nArgs c0)
      = physRename body (bodyPhysTable body) (regName d1)) :
    BodyCover body (bodyPhysTable body) body [b0, b1] := by
  have hcov : BodyCover body (bodyPhysTable body)
      [regArithHead nArgs d0 bop0 w a0 a1, regArithHead nArgs d1 bop1 w c0 c1]
      [b0, b1] :=
    regArithHead_cover_cons body (bodyPhysTable body) nArgs d0 bop0 w hw hns0
      a0 a1 b0 [b1] [regArithHead nArgs d1 bop1 w c0 c1] hdst0 hopn0 hsrc0 hcol0
      (regArithHead_cover_cons body (bodyPhysTable body) nArgs d1 bop1 w hw hns1
        c0 c1 b1 [] [] hdst1 hopn1 hsrc1 hcol1 .nil)
  exact hbody ▸ hcov

/-- **Unconditional physical faithfulness on a two-binop body.** The two-binding
    composition of `physBody_lsem_result_single`: a body that *is* two
    `regArithHead`s, with the cover *constructed* (`bodyCover_two`), runs faithfully
    — the literal `physBody` output reads the composed virtual store at the
    physical result register, with the cover hypothesis of `physBody_lsem_result`
    discharged. `hinj` (inside each `bᵢ`) and the two collapses stay hypotheses. -/
theorem physBody_lsem_result_two {w : Nat} (body : Lcmd)
    (nArgs d0 d1 : Nat) (bop0 bop1 : JasminBinOp) (hw : w ≠ 64)
    (hns0 : bop0 ≠ .shl ∧ bop0 ≠ .shr ∧ bop0 ≠ .andn)
    (hns1 : bop1 ≠ .shl ∧ bop1 ≠ .shr ∧ bop1 ≠ .andn)
    {Γ0 Γ1 : Ctxt jasminDialect}
    (a0 a1 : Ctxt.Var Γ0 (.reg w)) (c0 c1 : Ctxt.Var Γ1 (.reg w))
    (b0 b1 : BinopBinding w body (bodyPhysTable body))
    (hbody : body = [regArithHead nArgs d0 bop0 w a0 a1,
                     regArithHead nArgs d1 bop1 w c0 c1])
    (hdst0 : b0.nDst = regName d0) (hopn0 : b0.opn = withWidthTag w (binOpName bop0))
    (hsrc0 : b0.nSrc = resolveVarName d0 nArgs a1)
    (hcol0 : physRename body (bodyPhysTable body) (resolveVarName d0 nArgs a0)
      = physRename body (bodyPhysTable body) (regName d0))
    (hdst1 : b1.nDst = regName d1) (hopn1 : b1.opn = withWidthTag w (binOpName bop1))
    (hsrc1 : b1.nSrc = resolveVarName d1 nArgs c1)
    (hcol1 : physRename body (bodyPhysTable body) (resolveVarName d1 nArgs c0)
      = physRename body (bodyPhysTable body) (regName d1))
    (L N : List String)
    (hch : Chained ([b0, b1].map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w)
    (hrel : StoreRel body (bodyPhysTable body) L s s')
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ s'', lsemStraight ((physBody (fun _ => none) body).map (·.li_i)) s' = some s''
      ∧ s''.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps ([b0, b1].map (fun b => (b.block, b.vstep))) s).lvm nRes :=
  physBody_lsem_result body [b0, b1]
    (bodyCover_two body nArgs d0 d1 bop0 bop1 w hw hns0 hns1 a0 a1 c0 c1 b0 b1 hbody
      hdst0 hopn0 hsrc0 hcol0 hdst1 hopn1 hsrc1 hcol1)
    L N hch s s' hrel nRes hnRes

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulCover
