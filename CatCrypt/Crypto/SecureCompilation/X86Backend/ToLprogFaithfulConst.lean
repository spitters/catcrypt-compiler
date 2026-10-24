/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.String.TakeDrop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulAssembled

/-!
# Whole-function register-allocation faithfulness with constant bindings

`ToLprogFaithfulAssembled.toLprogPhysAbi_faithful_uniform` covers a `Com` whose
bindings are all binary same-width `regArith`. This module extends it to a
`Com` whose bindings are binary same-width `regArith` or `regConst`.

A `regConst w n` binding at depth `d` is emitted by `opToLinstrR` as
`Lopn [.reg (regName d)] (withWidthTag w "MOV") [.imm n]`. Under `physBody` this
single-source instruction takes the `MOV` arm: `remapOperand` renames the
destination and leaves the immediate unchanged, and `legalizeMov` emits the
single instruction `MOV ρ(regName d), #n`, since an immediate is never a spill
operand. Under `lsemStep` that instruction writes `BitVec.ofNat w n` at the
physical destination, which is the denotation of `regConst w n`.

The proof reuses the binop development unchanged and adds three pieces:

* `ConstBinding` with its block, its virtual transformer and
  `ConstBinding.maintains`, the store-relation maintenance of the constant load
  under the destination injectivity `hinj`;
* `physBodyElem_regConst`, the `physBody` expansion of the constant head;
* `ArithConstBinding`, the sum of a binop and a constant binding, with the
  cover `BodyCoverAC` and the threaded `CoverDataConst`, whose binop arm carries
  the same data as `ToLprogFaithfulNary.CoverData`.

The whole-function statements compose the binding-independent legs of
`ToLprogFaithfulAssembled` (prologue run and frame, argument materialization,
`Lret` peel, callee-save restore epilogue) with the new body theorem.

## Main results

* `ConstBinding.maintains`: a constant load re-establishes `StoreRel` against
  `s ↦ s.setReg nDst (BitVec.ofNat w n)`.
* `physBodyElem_regConst`: `physBody` expands the constant head to
  `[MOV ρdst, #n]`.
* `UniformRegArithConst`: the `Com` fragment of non-shift, non-64-bit binary
  `regArith` bindings and `regConst` bindings.
* `CoverDataConst.uniformRegArithConst`: cover data exists only for that
  fragment; `CoverData.toConst` embeds the binop-only cover data.
* `physBody_lsem_result_uniformConst`: the physical body run of such a `Com`
  reads the composed virtual store at the physical result register.
* `toLprogPhysAbi_faithful_uniformConst`: the whole emitted function body
  `prologue ++ argMatSeq pairs ++ physBody ++ Lret :: rest`, run under `lsemRun`,
  leaves the composed virtual store's result in the physical result register.
* `toLprogPhysAbi_faithful_uniformConst_twoPtr`: the same at the canonical
  `[RDI, RSI]` materialization pairs.
* `toLprogPhysAbi_faithful_uniformConst_epilogue`: the same with the callee-save
  restore epilogue before the `Lret`.

## Scope

Immediate shifts are not covered. With the empty immediate map and the empty
shift oracle that `bindingHeads` and `physBody (fun _ => none)` use, a binary
`regArith` shift never carries an immediate count, and the unary `shlImm` /
`shrImm` ops lower through `lowerNativeShiftRotate` with count-tagged mnemonics,
a different block from the constant load. The hypotheses on the emitted body are
those of `toLprogPhysAbi_faithful_uniform`: the body is the head list
`bindingHeads … com d`, and the identification of `buildArgPtrMaterialize` and
`(physBodyWithStores …).dropLast` with `argMatSeq` and `physBody` is not proved
here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulConst

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWriteSide
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBody
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulFlatMap
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulCover
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulNary
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWholeFn
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulProlog
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulAssembled

/-! ## 1. The constant binding and its maintenance -/

/-- The width-tagged `MOV` mnemonic strips to `MOV`. -/
theorem stripWidthTag_withWidthTag_MOV (w : Nat) :
    stripWidthTag (withWidthTag w "MOV") = "MOV" :=
  stripWidthTag_withWidthTag w (by decide +kernel)

/-- A constant binding along the renaming `physRename body tbl`: the logical
    destination `nDst` receives the literal `n`, and no other logical name is
    renamed onto the physical register of `nDst`. -/
structure ConstBinding (w : Nat) (body : Lcmd) (tbl : Array Nat) where
  nDst : String
  n : Nat
  /-- The logical names live before the binding. -/
  Lin : List String
  /-- The logical names live after the binding. -/
  Lout : List String
  /-- No other name live after the binding shares the destination's physical
      register. -/
  hinj : ∀ m ∈ Lout, physRename body tbl m = physRename body tbl nDst → m = nDst
  /-- Every name live after the binding other than its destination was already
      live before it. -/
  hcarry : ∀ m ∈ Lout, m ≠ nDst → m ∈ Lin

/-- The physical block of a constant binding: `MOV ρ nDst, #n` at width `w`. -/
def ConstBinding.block {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (c : ConstBinding w body tbl) : List LinstrR :=
  [.Lopn [.reg (physRename body tbl c.nDst)] (withWidthTag w "MOV") [.imm c.n]]

/-- The virtual transformer of a constant binding: write `BitVec.ofNat w n` at
    `nDst`. -/
def ConstBinding.vstep {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (c : ConstBinding w body tbl) : Lstate w → Lstate w :=
  fun s => s.setReg c.nDst (BitVec.ofNat w c.n)

/-- A constant binding's block re-establishes `StoreRel` against its virtual
    transformer. The load writes only `ρ nDst`, and `hinj` confines that write to
    the `nDst` fibre. -/
theorem ConstBinding.maintains {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (c : ConstBinding w body tbl) :
    BlockMaintains body tbl c.Lin c.Lout c.block c.vstep := by
  intro s s' hrel
  have hstep : lsemStep (LinstrR.Lopn [.reg (physRename body tbl c.nDst)]
      (withWidthTag w "MOV") [.imm c.n]) s'
      = some ((s'.setReg (physRename body tbl c.nDst) (BitVec.ofNat w c.n)).nextPc) := by
    simp only [lsemStep, List.map_cons, List.map_nil, evalOperand,
      stripWidthTag_withWidthTag_MOV, applyOpn]
  refine ⟨(s'.setReg (physRename body tbl c.nDst) (BitVec.ofNat w c.n)).nextPc,
    by rw [ConstBinding.block, lsemStraight_cons, hstep]; rfl, ?_⟩
  intro m hmL
  by_cases hm : physRename body tbl m = physRename body tbl c.nDst
  · have hmd : m = c.nDst := c.hinj m hmL hm
    subst hmd
    simp [ConstBinding.vstep]
  · have hmne : m ≠ c.nDst := fun he => hm (by rw [he])
    simp only [ConstBinding.vstep, Lstate.lvm_nextPc, Lstate.lvm_setReg, ite_eq_right hm, ite_eq_right hmne]
    exact hrel m (c.hcarry m hmL hmne)

/-! ## 2. The `physBody` expansion of a constant head -/

/-- `String.isPrefixOf` is `hasPrefix` with the arguments swapped; the same
    statement as `WellFormedX86.isPrefixOf_eq_hasPrefix`, which lies outside this
    module's imports. -/
theorem string_isPrefixOf_eq_hasPrefix (p s : String) :
    p.isPrefixOf s = hasPrefix s p := by
  rw [hasPrefix, String.isPrefixOf, Bool.eq_iff_iff,
    String.startsWith_string_iff, List.isPrefixOf_iff_prefix]

/-- The width-tagged `MOV` mnemonic is not a native shift or rotate. -/
theorem isNativeShiftRotate_withWidthTag_MOV (w : Nat) :
    isNativeShiftRotate (withWidthTag w "MOV") = false := by
  simp only [isNativeShiftRotate, stripWidthTag_withWidthTag_MOV,
    string_isPrefixOf_eq_hasPrefix]
  decide

/-- The width-tagged `MOV` mnemonic is not a memory load. -/
theorem isMemLoad_withWidthTag_MOV (w : Nat) :
    isMemLoad (withWidthTag w "MOV") = false := by
  simp only [isMemLoad, stripWidthTag_withWidthTag_MOV]
  decide

/-- `physBody` expands the constant head `MOV nDst, #n` to the single renamed
    instruction `MOV ρ nDst, #n`. -/
theorem physBodyElem_regConst (body : Lcmd) (tbl : Array Nat) (ii : Nat)
    (nDst : String) (w n : Nat) :
    (physBodyElem body tbl ⟨ii, .Lopn [.reg nDst] (withWidthTag w "MOV") [.imm n]⟩).map (·.li_i)
      = [.Lopn [.reg (physRename body tbl nDst)] (withWidthTag w "MOV") [.imm n]] := by
  simp only [physBodyElem, isNativeShiftRotate_withWidthTag_MOV, isMemLoad_withWidthTag_MOV,
    stripWidthTag_withWidthTag_MOV, Bool.false_eq_true, ite_false, beq_self_eq_true,
    Bool.true_or, ite_true, legalizeMov, LOperand.isSpill]
  simp [remapOperand, physRename]

/-! ## 3. Binop-or-constant bindings and their cover -/

/-- A binding of the binop-or-constant fragment. -/
inductive ArithConstBinding (w : Nat) (body : Lcmd) (tbl : Array Nat) where
  | binop (b : BinopBinding w body tbl)
  | const (c : ConstBinding w body tbl)

/-- The physical block of a binding. -/
def ArithConstBinding.block {w : Nat} {body : Lcmd} {tbl : Array Nat} :
    ArithConstBinding w body tbl → List LinstrR
  | .binop b => b.block
  | .const c => c.block

/-- The virtual transformer of a binding. -/
def ArithConstBinding.vstep {w : Nat} {body : Lcmd} {tbl : Array Nat} :
    ArithConstBinding w body tbl → Lstate w → Lstate w
  | .binop b => b.vstep
  | .const c => c.vstep

/-- The logical names live before a binding. -/
def ArithConstBinding.Lin {w : Nat} {body : Lcmd} {tbl : Array Nat} :
    ArithConstBinding w body tbl → List String
  | .binop b => b.Lin
  | .const c => c.Lin

/-- The logical names live after a binding. -/
def ArithConstBinding.Lout {w : Nat} {body : Lcmd} {tbl : Array Nat} :
    ArithConstBinding w body tbl → List String
  | .binop b => b.Lout
  | .const c => c.Lout

/-- Every binding's block is a `BlockMaintains` witness across its live sets. -/
theorem ArithConstBinding.maintains {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : ArithConstBinding w body tbl) :
    BlockMaintains body tbl b.Lin b.Lout b.block b.vstep := by
  cases b with
  | binop b => exact b.maintains
  | const c => exact c.maintains

/-- A cover of a source body by a binding list: the `physBody` expansion of the
    `i`-th instruction, projected to `LinstrR`, is the `i`-th binding's block. -/
inductive BodyCoverAC {w : Nat} (body : Lcmd) (tbl : Array Nat) :
    Lcmd → List (ArithConstBinding w body tbl) → Prop where
  | nil : BodyCoverAC body tbl [] []
  | cons {i : Linstr} {b : ArithConstBinding w body tbl} {is : Lcmd}
      {bs : List (ArithConstBinding w body tbl)} :
      (physBodyElem body tbl i).map (·.li_i) = b.block → BodyCoverAC body tbl is bs →
      BodyCoverAC body tbl (i :: is) (b :: bs)

/-- The `physBody` expansion of a covered sub-body is the flattened block list. -/
theorem physBody_flatMap_blocksAC {w : Nat} (body : Lcmd) (sub : Lcmd)
    (bs : List (ArithConstBinding w body (bodyPhysTable body)))
    (hcover : BodyCoverAC body (bodyPhysTable body) sub bs) :
    sub.flatMap (fun i => (physBodyElem body (bodyPhysTable body) i).map (·.li_i))
      = (bs.map (·.block)).flatten := by
  induction hcover with
  | nil => rfl
  | cons hib _ ih => rw [List.flatMap_cons, List.map_cons, List.flatten_cons, ih, hib]

/-- The literal `physBody` of a covered body, projected to `LinstrR`, is the
    flattened block list. -/
theorem physBody_map_li_iAC {w : Nat} (body : Lcmd)
    (bs : List (ArithConstBinding w body (bodyPhysTable body)))
    (hcover : BodyCoverAC body (bodyPhysTable body) body bs) :
    (physBody (fun _ => none) body).map (·.li_i) = (bs.map (·.block)).flatten := by
  rw [physBody_eq_flatMap, List.map_flatMap]
  exact physBody_flatMap_blocksAC body body bs hcover

/-- Running the flattened block list of a binding list from a `StoreRel`-related
    start reads the composed virtual store at every renamed register. -/
theorem arithConstBody_lsem_result {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (bs : List (ArithConstBinding w body tbl)) (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w)
    (hrel : StoreRel body tbl L s s') (nRes : String) (hnRes : nRes ∈ N) :
    ∃ s'', lsemStraight ((bs.map (·.block)).flatten) s' = some s''
      ∧ s''.lvm (physRename body tbl nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  have hmaint : BlocksMaintain body tbl L N (bs.map (fun b => (b.block, b.vstep))) :=
    blocksMaintain_of_chained body tbl bs N (·.Lin) (·.Lout) (·.block) (·.vstep)
      L (fun b _ => b.maintains) hch
  have hkey := physBlocks_storeRel_result body tbl L N
    (bs.map (fun b => (b.block, b.vstep))) hmaint s s' hrel nRes hnRes
  have hreidx : ((bs.map (fun b => (b.block, b.vstep))).map Prod.fst) = bs.map (·.block) := by
    rw [List.map_map]; rfl
  rw [hreidx] at hkey
  exact hkey

/-- Physical faithfulness of the literal `physBody` on a covered body. -/
theorem physBody_lsem_resultAC {w : Nat} (body : Lcmd)
    (bs : List (ArithConstBinding w body (bodyPhysTable body)))
    (hcover : BodyCoverAC body (bodyPhysTable body) body bs)
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w) (hrel : StoreRel body (bodyPhysTable body) L s s')
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ s'', lsemStraight ((physBody (fun _ => none) body).map (·.li_i)) s' = some s''
      ∧ s''.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  rw [physBody_map_li_iAC body bs hcover]
  exact arithConstBody_lsem_result body (bodyPhysTable body) bs L N hch s s' hrel nRes hnRes

/-! ## 4. The `Com` fragment and its threaded cover data -/

/-- A `Com` all of whose bindings are non-shift, non-64-bit binary `regArith`
    binops or `regConst` loads, terminating at `.ret`. -/
inductive UniformRegArithConst : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Prop where
  | ret {Γ t} (v : Ctxt.Var Γ t) : UniformRegArithConst (.ret v)
  | var {Γ s} {w : Nat} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
      (a0 a1 : Ctxt.Var Γ (JasminTy.reg w)) (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hw : w ≠ 64) (hns : NonShift bop) (hbody : UniformRegArithConst body) :
      UniformRegArithConst
        (.var ⟨JasminOp.regArith bop w, heq, .cons a0 (.cons a1 .nil)⟩ body)
  | const {Γ s} {w n : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
      (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hbody : UniformRegArithConst body) :
      UniformRegArithConst (.var ⟨JasminOp.regConst w n, heq, .nil⟩ body)

/-- The binop-only fragment is contained in the binop-or-constant fragment. -/
theorem UniformRegArith.toConst {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (h : UniformRegArith com) : UniformRegArithConst com := by
  induction h with
  | ret v => exact .ret v
  | var bop heq a0 a1 body hw hns _ ih => exact .var bop heq a0 a1 body hw hns ih

/-- Cover data threaded along a binop-or-constant `Com` over a fixed whole
    `body`/`tbl`. The binop arm carries the data of `CoverData.var`; the constant
    arm carries a `ConstBinding` whose destination is `regName d` and whose
    literal is the op's literal. -/
inductive CoverDataConst {w : Nat} (body : Lcmd) (tbl : Array Nat) (nArgs : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) →
    List (ArithConstBinding w body tbl) → Prop where
  | ret {Γ t} (v : Ctxt.Var Γ t) (d : Nat) : CoverDataConst body tbl nArgs (.ret v) d []
  | var {Γ s} {bop : JasminBinOp}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w}
      {a0 a1 : Ctxt.Var Γ (JasminTy.reg w)} {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (hw : w ≠ 64) (hns : bop ≠ .shl ∧ bop ≠ .shr ∧ bop ≠ .andn)
      (b : BinopBinding w body tbl) (bs : List (ArithConstBinding w body tbl))
      (hdst : b.nDst = regName d)
      (hopn : b.opn = withWidthTag w (binOpName bop))
      (hsrc : b.nSrc = resolveVarName d nArgs a1)
      (hcol : physRename body tbl (resolveVarName d nArgs a0)
          = physRename body tbl (regName d))
      (htail : CoverDataConst body tbl nArgs bdy (d + 1) bs) :
      CoverDataConst body tbl nArgs
        (.var ⟨JasminOp.regArith bop w, heq, .cons a0 (.cons a1 .nil)⟩ bdy) d (.binop b :: bs)
  | const {Γ s} {n : Nat}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w}
      {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (c : ConstBinding w body tbl) (bs : List (ArithConstBinding w body tbl))
      (hdst : c.nDst = regName d) (hn : c.n = n)
      (htail : CoverDataConst body tbl nArgs bdy (d + 1) bs) :
      CoverDataConst body tbl nArgs
        (.var ⟨JasminOp.regConst w n, heq, .nil⟩ bdy) d (.const c :: bs)

/-- Cover data exists only for a binop-or-constant `Com`. -/
theorem CoverDataConst.uniformRegArithConst {w : Nat} {body : Lcmd} {tbl : Array Nat}
    {nArgs : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy} {com : Com jasminDialect Γ t}
    {d : Nat} {bs : List (ArithConstBinding w body tbl)}
    (h : CoverDataConst body tbl nArgs com d bs) : UniformRegArithConst com := by
  induction h with
  | ret v d => exact .ret v
  | var d hw hns b bs _ _ _ _ _ ih => exact .var _ _ _ _ _ hw hns ih
  | const d c bs _ _ _ ih => exact .const _ _ ih

/-- Binop-only cover data is cover data of the binop-or-constant fragment, with
    every binding tagged `binop`. -/
theorem CoverData.toConst {w : Nat} {body : Lcmd} {tbl : Array Nat} {nArgs : Nat}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {com : Com jasminDialect Γ t} {d : Nat}
    {bs : List (BinopBinding w body tbl)}
    (h : CoverData body tbl nArgs com d bs) :
    CoverDataConst body tbl nArgs com d (bs.map .binop) := by
  induction h with
  | ret v d => exact .ret v d
  | var d hw hns b bs hdst hopn hsrc hcol _ ih => exact .var d hw hns b _ hdst hopn hsrc hcol ih

/-- The `bindingHeads` head of a `regConst w n` binding at depth `curDepth` is
    `MOV[:w] regName curDepth, #n`. -/
theorem bindingHeads_const_eq {Γ : Ctxt jasminDialect} {s : JasminTy}
    (nArgs w n : Nat)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (body : Com jasminDialect (JasminTy.reg w :: Γ) s) (curDepth : Nat) :
    bindingHeads nArgs argName (fun _ => none)
      (.var ⟨JasminOp.regConst w n, heq, .nil⟩ body) curDepth
      = (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w "MOV") [.imm n]⟩ : Linstr)
        :: bindingHeads nArgs argName (fun _ => none) body (curDepth + 1) := rfl

/-- The threaded cover data yields a cover of the head list `bindingHeads … com d`. -/
theorem coverDataConst_bodyCover {w : Nat} (body : Lcmd) (tbl : Array Nat) (nArgs : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (d : Nat) (bs : List (ArithConstBinding w body tbl))
    (hcd : CoverDataConst body tbl nArgs com d bs) :
    BodyCoverAC body tbl (bindingHeads nArgs argName (fun _ => none) com d) bs := by
  induction hcd with
  | ret v d => exact .nil
  | var d hw hns b bs hdst hopn hsrc hcol _ ih =>
      rw [bindingHeads_var_eq]
      exact .cons (physBodyElem_of_realizes body tbl _ b
        (regArithHead_realizes body tbl nArgs d _ w hw hns _ _ b hdst hopn hsrc hcol)) ih
  | const d c bs hdst hn _ ih =>
      rw [bindingHeads_const_eq]
      refine .cons ?_ ih
      rw [physBodyElem_regConst, ArithConstBinding.block, ConstBinding.block, hdst, hn]

/-- **Physical body faithfulness, binop-or-constant fragment.** For a body that
    is the head list `bindingHeads … com d` of a `Com` with threaded
    `CoverDataConst`, running the literal `physBody (fun _ => none) body` from a
    `StoreRel`-related start reads the composed virtual store at the physical
    result register. -/
theorem physBody_lsem_result_uniformConst {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (ArithConstBinding w body (bodyPhysTable body)))
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverDataConst body (bodyPhysTable body) nArgs com d bs)
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w)
    (hrel : StoreRel body (bodyPhysTable body) L s s')
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ s'', lsemStraight ((physBody (fun _ => none) body).map (·.li_i)) s' = some s''
      ∧ s''.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  have hcov0 := coverDataConst_bodyCover body (bodyPhysTable body) nArgs com d bs hcd
  have hcov : BodyCoverAC body (bodyPhysTable body) body bs := hbody ▸ hcov0
  exact physBody_lsem_resultAC body bs hcov L N hch s s' hrel nRes hnRes

/-! ## 5. The assembled whole-function theorems -/

/-- The straight-line core: `prologue ++ argMatSeq pairs ++ physBody` runs under
    `lsemStraight` from the entry state to a state whose physical result register
    reads the composed virtual store, and the list is `Lret`-free. -/
theorem prologue_argMat_body_lsemStraightConst {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (ArithConstBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverDataConst body (bodyPhysTable body) nArgs com d bs)
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (sEntry s : Lstate w)
    (hdisjFrame : PrologueFrameDisjoint body (bodyPhysTable body) L)
    (hoff : StoreRelOff body (bodyPhysTable body) L (pairs.map Prod.fst) s sEntry)
    (habi : ArgMatAbi body (bodyPhysTable body) L pairs s (prologueState sEntry))
    (nRes : String) (hnRes : nRes ∈ N) :
    .Lret ∉ ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
        ++ (physBody (fun _ => none) body).map (·.li_i))
    ∧ ∃ sEnd,
      lsemStraight
        ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
          ++ (physBody (fun _ => none) body).map (·.li_i)) sEntry
        = some sEnd
      ∧ sEnd.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  have hoffP :=
    buildPrologue_preserves_StoreRelOff body (bodyPhysTable body) L _ s sEntry
      hdisjFrame hoff
  obtain ⟨sMat, hrunMat, _⟩ := argMatSeq_reads pairs hfresh hdist (prologueState sEntry)
  have hrelMat : StoreRel body (bodyPhysTable body) L s sMat :=
    argMatSeq_establishes_StoreRel body (bodyPhysTable body) L pairs hfresh hdist s _ sMat
      hoffP habi hrunMat
  obtain ⟨sB, hrunBody, hread⟩ :=
    physBody_lsem_result_uniformConst body nArgs d com bs hbody hcd L N hch s sMat
      hrelMat nRes hnRes
  refine ⟨?_, sB, ?_, hread⟩
  · intro hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · rcases List.mem_append.mp hmem with hmem | hmem
      · exact Lret_not_mem_of_lsemStraight_some _ _ _
          (buildPrologue_lsem virt tbl0 inLoadMap sEntry) hmem
      · exact Lret_not_mem_of_lsemStraight_some _ _ _ hrunMat hmem
    · exact Lret_not_mem_of_lsemStraight_some _ _ _ hrunBody hmem
  · rw [lsemStraight_append, lsemStraight_append, buildPrologue_lsem, Option.bind_some,
      hrunMat, Option.bind_some, hrunBody]

/-- **Whole-function register-allocation faithfulness, binop-or-constant
    fragment.** For a `Com` of non-shift binary `regArith` and `regConst` bindings
    whose head list is `body`, with the threaded `CoverDataConst`, running
    `buildPrologue ++ argMatSeq pairs ++ physBody ++ Lret :: rest` under `lsemRun`
    from an entry state related to the virtual store off the materialization
    destinations (`hoff`), whose renaming avoids the prologue cells
    (`hdisjFrame`) and whose materialization sources carry the argument values
    (`habi`), reaches a state whose physical result register reads the composed
    virtual store. -/
theorem toLprogPhysAbi_faithful_uniformConst {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (ArithConstBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (rest : List LinstrR) (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverDataConst body (bodyPhysTable body) nArgs com d bs)
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (sEntry s : Lstate w)
    (hdisjFrame : PrologueFrameDisjoint body (bodyPhysTable body) L)
    (hoff : StoreRelOff body (bodyPhysTable body) L (pairs.map Prod.fst) s sEntry)
    (habi : ArgMatAbi body (bodyPhysTable body) L pairs s (prologueState sEntry))
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ sEnd,
      lsemRun
        ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
          ++ (physBody (fun _ => none) body).map (·.li_i) ++ .Lret :: rest) sEntry
        = some sEnd
      ∧ sEnd.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  obtain ⟨hnoLret, sEnd, hrun, hread⟩ :=
    prologue_argMat_body_lsemStraightConst body nArgs d com bs virt tbl0 inLoadMap pairs
      hfresh hdist hbody hcd L N hch sEntry s hdisjFrame hoff habi nRes hnRes
  rw [lsemRun_body_ret _ _ _ hnoLret]
  exact ⟨sEnd, hrun, hread⟩

/-- **Whole-function faithfulness at the two-pointer ABI, binop-or-constant
    fragment.** The instance of `toLprogPhysAbi_faithful_uniformConst` at
    `twoPtrPairs`: `RDI` holds the virtual value of every name renamed onto
    `argName 0`'s register, and `RSI` that of every name renamed onto
    `argName 1`'s register. -/
theorem toLprogPhysAbi_faithful_uniformConst_twoPtr {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (ArithConstBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (rest : List LinstrR)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverDataConst body (bodyPhysTable body) nArgs com d bs)
    (hmemref : MemrefPtrsDistinct body (bodyPhysTable body))
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (sEntry s : Lstate w)
    (hdisjFrame : PrologueFrameDisjoint body (bodyPhysTable body) L)
    (hm0 : argName 0 ∈ L) (hm1 : argName 1 ∈ L)
    (hoff : StoreRelOff body (bodyPhysTable body) L
      [physRename body (bodyPhysTable body) (argName 0),
       physRename body (bodyPhysTable body) (argName 1)] s sEntry)
    (hRdi : ∀ m ∈ L, physRename body (bodyPhysTable body) m
      = physRename body (bodyPhysTable body) (argName 0) → sEntry.lvm "RDI" = s.lvm m)
    (hRsi : ∀ m ∈ L, physRename body (bodyPhysTable body) m
      = physRename body (bodyPhysTable body) (argName 1) → sEntry.lvm "RSI" = s.lvm m)
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ sEnd,
      lsemRun
        ((buildPrologue virt tbl0 inLoadMap).map (·.li_i)
          ++ argMatSeq (twoPtrPairs body (bodyPhysTable body))
          ++ (physBody (fun _ => none) body).map (·.li_i) ++ .Lret :: rest) sEntry
        = some sEnd
      ∧ sEnd.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  refine toLprogPhysAbi_faithful_uniformConst body nArgs d com bs virt tbl0 inLoadMap rest _
    (twoPtrPairs_sourcesFresh _ _ L hdisjFrame hm0 hm1)
    (twoPtrPairs_destsDistinct _ _ hmemref)
    hbody hcd L N hch sEntry s hdisjFrame hoff ?_ nRes hnRes
  intro p hp m hmL hpm
  simp only [twoPtrPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · dsimp only
    rw [prologueState_lvm_abiSaveRdi]
    exact hRdi m hmL hpm
  · dsimp only
    rw [prologueState_lvm_abiSaveRsi]
    exact hRsi m hmL hpm

/-- **Whole-function faithfulness with the callee-save restore epilogue,
    binop-or-constant fragment.** The function body `buildPrologue ++ argMatSeq
    pairs ++ physBody ++ calleeSaveRestoreEpilogue ++ Lret :: rest` run under
    `lsemRun`; the physical result register is read after the restore, so it is
    not one of the six callee-saved registers (`hResFree`). -/
theorem toLprogPhysAbi_faithful_uniformConst_epilogue {w : Nat} (body : Lcmd)
    (nArgs d : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (ArithConstBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (rest : List LinstrR) (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverDataConst body (bodyPhysTable body) nArgs com d bs)
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (sEntry s : Lstate w)
    (hdisjFrame : PrologueFrameDisjoint body (bodyPhysTable body) L)
    (hoff : StoreRelOff body (bodyPhysTable body) L (pairs.map Prod.fst) s sEntry)
    (habi : ArgMatAbi body (bodyPhysTable body) L pairs s (prologueState sEntry))
    (nRes : String) (hnRes : nRes ∈ N)
    (hResFree : physRename body (bodyPhysTable body) nRes ∉ epilogueWritten) :
    ∃ sEnd,
      lsemRun
        ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
          ++ (physBody (fun _ => none) body).map (·.li_i)
          ++ calleeSaveRestoreEpilogue.map (·.li_i) ++ .Lret :: rest) sEntry
        = some sEnd
      ∧ sEnd.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  obtain ⟨hnoLret, sB, hrun, hread⟩ :=
    prologue_argMat_body_lsemStraightConst body nArgs d com bs virt tbl0 inLoadMap pairs
      hfresh hdist hbody hcd L N hch sEntry s hdisjFrame hoff habi nRes hnRes
  have hnoLretEpi : .Lret ∉ calleeSaveRestoreEpilogue.map (·.li_i) :=
    Lret_not_mem_of_lsemStraight_some _ _ _ (calleeSaveRestoreEpilogue_lsem sB)
  have hnoLret' : .Lret ∉
      ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
        ++ (physBody (fun _ => none) body).map (·.li_i)
        ++ calleeSaveRestoreEpilogue.map (·.li_i)) := by
    intro hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hnoLret hmem
    · exact hnoLretEpi hmem
  rw [lsemRun_body_ret _ _ _ hnoLret', lsemStraight_append, hrun, Option.bind_some,
    calleeSaveRestoreEpilogue_lsem]
  exact ⟨epilogueState sB, rfl,
    by rw [calleeSaveRestoreEpilogue_frame sB _ hResFree]; exact hread⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulConst
