/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.String.TakeDrop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBinopWide
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBinopMov

/-!
# Whole-function register-allocation faithfulness with widening-multiply, carry-chain and select bindings

`ToLprogFaithfulConst.toLprogPhysAbi_faithful_uniformConst` covers a `Com` whose
bindings are binary same-width `regArith` or `regConst`. This module covers a
`Com` whose bindings are those together with `mulhi`, `addCarryLo`, `addCarryHi`
and `select`.

The four added ops are emitted by `opToLinstrR` as width-tagged single-`Lopn`
heads with their operands in source order: `mulhi w` as `MULXHI[:w] dst, a, b`,
`addCarryLo w` as `ADCX[:w] dst, a, b, cin`, `addCarryHi w` as
`ADCXHI[:w] dst, a, b, cin` and `select w` as `CMOV[:w] dst, cond, a, b`. None of
the four mnemonics is in `physBody`'s
two-address `isBinop` alphabet, is a native shift or rotate, or is a memory
load or store, so each takes the general `physBodyElem` arm: every operand is
renamed by `remapOperand` and the single instruction is emitted unchanged. There
is no injected legalization move, hence no leading two-address `mov` and no
two-address collapse obligation `hcol` on the register allocation — the
allocator obligations are the live-out interference condition `hinj` and the
carry condition `hcarry` that every binding kind carries.

`JasminLsem.applyOpn` models all four opcodes and ties each to the dialect
denotation it lowers from (`applyOpn_mulhi`, `applyOpn_addCarryLo`,
`applyOpn_addCarryHi`, `applyOpn_select`), so each binding's store step is one
`lsemStep` whose written value is the dialect's `mulHiW` / `addCarryWord` /
`carryOutBit` / `selectW` of the virtual operand values.

The proof reuses the binop and constant development unchanged and adds:

* `remapBlockMaintains2` / `remapBlockMaintains3`, the store-relation maintenance
  of a two- resp. three-source single-instruction binding under the destination
  injectivity `hinj`, parametric in the mnemonic and the value oracle;
* `MulHiBinding`, `AddCarryLoBinding`, `AddCarryHiBinding`, `SelectBinding` and
  their `physBodyElem` expansions;
* `MulCarryBinding`, the sum of these with `ArithConstBinding`, with the cover
  `BodyCoverMCS` and the threaded `CoverDataMCS`, into which
  `ToLprogFaithfulConst.CoverDataConst` embeds by `CoverDataConst.toMCS`.

## Main results

* `remapBlockMaintains2`, `remapBlockMaintains3`: a single-instruction two- resp.
  three-source binding re-establishes `StoreRel` against
  `s ↦ s.setReg nDst (vval s)`.
* `physBodyElem_mulhi`, `physBodyElem_addCarry3`: `physBody` expands the heads to
  the single renamed instruction.
* `UniformRegArithMCS`: the `Com` fragment of non-shift binary `regArith`
  bindings at a default width and at width 64, `regConst` bindings, and
  `mulhi` / `addCarryLo` / `addCarryHi` / `select` bindings.
* `CoverDataMCS.uniformRegArithMCS`: cover data exists only for that fragment;
  `CoverDataConst.toMCS` embeds the binop-or-constant cover data.
* `physBody_lsem_result_uniformMCS`: the physical body run of such a `Com` reads
  the composed virtual store at the physical result register.
* `toLprogPhysAbi_faithful_uniformMCS`: the whole emitted function body
  `prologue ++ argMatSeq pairs ++ physBody ++ Lret :: rest`, run under `lsemRun`,
  leaves the composed virtual store's result in the physical result register.
* `toLprogPhysAbi_faithful_uniformMCS_twoPtr`: the same at the canonical
  `[RDI, RSI]` materialization pairs.
* `toLprogPhysAbi_faithful_uniformMCS_epilogue`: the same with the callee-save
  restore epilogue before the `Lret`.
* `lsemStep_select`: the `select` head writes the dialect's `selectW` of its
  three operand values.

## `select`

`opToLinstrR` emits `select w` as `CMOV[:w] dst, cond, a, b` — the condition
first, then the word taken when the condition bit is one and the word taken when
it is zero. `JasminLsem.applyOpn` models that mnemonic as
`applyOpn "CMOV" [c, a, b] = some (selectW (BitVec.setWidth 1 c) a b)`, reading
the `reg 1` condition off the low bit of the condition register as the carry-in
of `ADCX` is read. `SelectBinding` is the binding kind of such a head; its
`maintains` step goes through `remapBlockMaintains3` at the operand order
`cond, a, b`.

## Scope

The `%rdx` pin and the two-output form of `mulx` are below this layer. At the
`physBody` / `lsem` layer `MULXHI` is a single-destination three-operand word op
that writes only its renamed destination; the `%rdx`-homed multiplicand and the
paired low word appear only after the `fuseMulHiLprog` post-pass, whose machine
model is `JasminModel`'s `runBlock` (`FheMontMulEmit.mulx_computes`).
`JasminLsem` carries no two-output instruction, so the agreement of a fused
`mulx` with the unfused low/high pair is not statable here. The carry-in and
carry-out of `ADCX` / `ADCXHI` are explicit `reg 1` operands on the value path,
not machine flags, so no flag-liveness condition on the allocation arises at this
layer either.

The hypotheses on the emitted body are those of
`toLprogPhysAbi_faithful_uniformConst`: the body is the head list
`bindingHeads … com d`, and the identification of `buildArgPtrMaterialize` and
`(physBodyWithStores …).dropLast` with `argMatSeq` and `physBody` is not proved
here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulMulCarrySel

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulConst
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBinopMov

/-! ## 1. Mnemonic facts -/

/-- The width-tagged `MULXHI` mnemonic strips to `MULXHI`. -/
theorem stripWidthTag_withWidthTag_MULXHI (w : Nat) :
    stripWidthTag (withWidthTag w "MULXHI") = "MULXHI" := by
  unfold withWidthTag
  split <;> decide +kernel

/-- The width-tagged `ADCX` mnemonic strips to `ADCX`. -/
theorem stripWidthTag_withWidthTag_ADCX (w : Nat) :
    stripWidthTag (withWidthTag w "ADCX") = "ADCX" := by
  unfold withWidthTag
  split <;> decide +kernel

/-- The width-tagged `ADCXHI` mnemonic strips to `ADCXHI`. -/
theorem stripWidthTag_withWidthTag_ADCXHI (w : Nat) :
    stripWidthTag (withWidthTag w "ADCXHI") = "ADCXHI" := by
  unfold withWidthTag
  split <;> decide +kernel

/-- The width-tagged `CMOV` mnemonic strips to `CMOV`. -/
theorem stripWidthTag_withWidthTag_CMOV (w : Nat) :
    stripWidthTag (withWidthTag w "CMOV") = "CMOV" := by
  unfold withWidthTag
  split <;> decide +kernel

/-- `MULXHI` is outside `physBody`'s two-address binop alphabet. -/
theorem not_isBinop_MULXHI (w : Nat) :
    isTwoAddrBinop (withWidthTag w "MULXHI") = false := by
  rw [isTwoAddrBinop, stripWidthTag_withWidthTag_MULXHI]
  decide +kernel

/-- `ADCX` is outside `physBody`'s two-address binop alphabet. -/
theorem not_isBinop_ADCX (w : Nat) :
    isTwoAddrBinop (withWidthTag w "ADCX") = false := by
  rw [isTwoAddrBinop, stripWidthTag_withWidthTag_ADCX]
  decide +kernel

/-- `ADCXHI` is outside `physBody`'s two-address binop alphabet. -/
theorem not_isBinop_ADCXHI (w : Nat) :
    isTwoAddrBinop (withWidthTag w "ADCXHI") = false := by
  rw [isTwoAddrBinop, stripWidthTag_withWidthTag_ADCXHI]
  decide +kernel

/-- `CMOV` is outside `physBody`'s two-address binop alphabet. -/
theorem not_isBinop_CMOV (w : Nat) :
    isTwoAddrBinop (withWidthTag w "CMOV") = false := by
  rw [isTwoAddrBinop, stripWidthTag_withWidthTag_CMOV]
  decide +kernel

/-- The width-tagged `MULXHI` mnemonic is not a memory store. -/
theorem isMemStore_withWidthTag_MULXHI (w : Nat) :
    isMemStore (withWidthTag w "MULXHI") = false := by
  simp only [isMemStore, stripWidthTag_withWidthTag_MULXHI]
  decide +kernel

/-! ## 2. Single-instruction bindings and their maintenance

A `mulhi` / `addCarryLo` / `addCarryHi` head expands to one renamed instruction,
so its store step is one `lsemStep`. The two lemmas below carry that step through
`StoreRel`, parametric in the mnemonic and the value oracle: the operand reads
transfer by `StoreRel`, and the destination injectivity `hinj` confines the
single physical write to the destination's fibre. -/

/-- A two-source single-instruction step: when the modeled opcode applies to the
    two evaluated register sources, the instruction writes that value at the
    destination and advances the pc. -/
theorem lsemStep_src2 {w : Nat} (nD nA nB opn : String) (s : Lstate w) (v : BitVec w)
    (hv : applyOpn (stripWidthTag opn) [s.lvm nA, s.lvm nB] = some v) :
    lsemStep (.Lopn [.reg nD] opn [.reg nA, .reg nB]) s = some ((s.setReg nD v).nextPc) := by
  simp only [lsemStep, List.map_cons, List.map_nil, evalOperand, hv]

/-- A three-source single-instruction step: when the modeled opcode applies to the
    three evaluated register sources, the instruction writes that value at the
    destination and advances the pc. -/
theorem lsemStep_src3 {w : Nat} (nD nA nB nC opn : String) (s : Lstate w) (v : BitVec w)
    (hv : applyOpn (stripWidthTag opn) [s.lvm nA, s.lvm nB, s.lvm nC] = some v) :
    lsemStep (.Lopn [.reg nD] opn [.reg nA, .reg nB, .reg nC]) s
      = some ((s.setReg nD v).nextPc) := by
  simp only [lsemStep, List.map_cons, List.map_nil, evalOperand, hv]

/-- **Maintenance of a two-source single-instruction binding.** The renamed
    instruction `opn ρ nDst, ρ nA, ρ nB` re-establishes `StoreRel` against
    `s ↦ s.setReg nDst (vval s)`, given the modeled-opcode premise `hop` at every
    virtual store and the destination injectivity `hinj`. -/
theorem remapBlockMaintains2 {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (Lin Lout : List String)
    (nDst nA nB opn : String) (vval : Lstate w → BitVec w)
    (hAIn : nA ∈ Lin) (hBIn : nB ∈ Lin)
    (hinj : ∀ m ∈ Lout, physRename body tbl m = physRename body tbl nDst → m = nDst)
    (hcarry : ∀ m ∈ Lout, m ≠ nDst → m ∈ Lin)
    (hop : ∀ s : Lstate w, applyOpn (stripWidthTag opn) [s.lvm nA, s.lvm nB] = some (vval s)) :
    BlockMaintains body tbl Lin Lout
      [.Lopn [.reg (physRename body tbl nDst)] opn
        [.reg (physRename body tbl nA), .reg (physRename body tbl nB)]]
      (fun s => s.setReg nDst (vval s)) := by
  intro s s' hrel
  have hop' : applyOpn (stripWidthTag opn)
      [s'.lvm (physRename body tbl nA), s'.lvm (physRename body tbl nB)] = some (vval s) := by
    rw [hrel nA hAIn, hrel nB hBIn]; exact hop s
  refine ⟨(s'.setReg (physRename body tbl nDst) (vval s)).nextPc, ?_, ?_⟩
  · rw [lsemStraight_cons,
      lsemStep_src2 (physRename body tbl nDst) (physRename body tbl nA)
        (physRename body tbl nB) opn s' (vval s) hop']
    rfl
  · intro m hmL
    by_cases hm : physRename body tbl m = physRename body tbl nDst
    · have hmd : m = nDst := hinj m hmL hm
      subst hmd
      simp
    · have hmne : m ≠ nDst := fun he => hm (by rw [he])
      simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg, if_neg hm, if_neg hmne]
      exact hrel m (hcarry m hmL hmne)

/-- **Maintenance of a three-source single-instruction binding.** The renamed
    instruction `opn ρ nDst, ρ nA, ρ nB, ρ nC` re-establishes `StoreRel` against
    `s ↦ s.setReg nDst (vval s)`, given the modeled-opcode premise `hop` at every
    virtual store and the destination injectivity `hinj`. -/
theorem remapBlockMaintains3 {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (Lin Lout : List String)
    (nDst nA nB nC opn : String) (vval : Lstate w → BitVec w)
    (hAIn : nA ∈ Lin) (hBIn : nB ∈ Lin) (hCIn : nC ∈ Lin)
    (hinj : ∀ m ∈ Lout, physRename body tbl m = physRename body tbl nDst → m = nDst)
    (hcarry : ∀ m ∈ Lout, m ≠ nDst → m ∈ Lin)
    (hop : ∀ s : Lstate w,
      applyOpn (stripWidthTag opn) [s.lvm nA, s.lvm nB, s.lvm nC] = some (vval s)) :
    BlockMaintains body tbl Lin Lout
      [.Lopn [.reg (physRename body tbl nDst)] opn
        [.reg (physRename body tbl nA), .reg (physRename body tbl nB),
         .reg (physRename body tbl nC)]]
      (fun s => s.setReg nDst (vval s)) := by
  intro s s' hrel
  have hop' : applyOpn (stripWidthTag opn)
      [s'.lvm (physRename body tbl nA), s'.lvm (physRename body tbl nB),
       s'.lvm (physRename body tbl nC)] = some (vval s) := by
    rw [hrel nA hAIn, hrel nB hBIn, hrel nC hCIn]; exact hop s
  refine ⟨(s'.setReg (physRename body tbl nDst) (vval s)).nextPc, ?_, ?_⟩
  · rw [lsemStraight_cons,
      lsemStep_src3 (physRename body tbl nDst) (physRename body tbl nA)
        (physRename body tbl nB) (physRename body tbl nC) opn s' (vval s) hop']
    rfl
  · intro m hmL
    by_cases hm : physRename body tbl m = physRename body tbl nDst
    · have hmd : m = nDst := hinj m hmL hm
      subst hmd
      simp
    · have hmne : m ≠ nDst := fun he => hm (by rw [he])
      simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg, if_neg hm, if_neg hmne]
      exact hrel m (hcarry m hmL hmne)

/-! ## 3. The three binding kinds -/

/-- A `mulhi` binding along the renaming `physRename body tbl`: the logical
    destination `nDst` receives the high word of the product of the values at
    `nA` and `nB`, and no other logical name is renamed onto the physical
    register of `nDst`. -/
structure MulHiBinding (w : Nat) (body : Lcmd) (tbl : Array Nat) where
  nDst : String
  nA : String
  nB : String
  /-- The logical names live before the binding. -/
  Lin : List String
  /-- The logical names live after the binding. -/
  Lout : List String
  /-- The binding reads its first operand. -/
  hAIn : nA ∈ Lin
  /-- The binding reads its second operand. -/
  hBIn : nB ∈ Lin
  /-- No other name live after the binding shares the destination's physical
      register. -/
  hinj : ∀ m ∈ Lout, physRename body tbl m = physRename body tbl nDst → m = nDst
  /-- Every name live after the binding other than its destination was already
      live before it. -/
  hcarry : ∀ m ∈ Lout, m ≠ nDst → m ∈ Lin

/-- The physical block of a `mulhi` binding: `MULXHI ρ nDst, ρ nA, ρ nB` at
    width `w`. -/
def MulHiBinding.block {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : MulHiBinding w body tbl) : List LinstrR :=
  [.Lopn [.reg (physRename body tbl b.nDst)] (withWidthTag w "MULXHI")
    [.reg (physRename body tbl b.nA), .reg (physRename body tbl b.nB)]]

/-- The virtual transformer of a `mulhi` binding: write `mulHiW` of the operand
    values at `nDst`. -/
def MulHiBinding.vstep {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : MulHiBinding w body tbl) : Lstate w → Lstate w :=
  fun s => s.setReg b.nDst (mulHiW (s.lvm b.nA) (s.lvm b.nB))

/-- A `mulhi` binding's block re-establishes `StoreRel` against its virtual
    transformer. -/
theorem MulHiBinding.maintains {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : MulHiBinding w body tbl) :
    BlockMaintains body tbl b.Lin b.Lout b.block b.vstep :=
  remapBlockMaintains2 body tbl b.Lin b.Lout b.nDst b.nA b.nB (withWidthTag w "MULXHI")
    (fun s => mulHiW (s.lvm b.nA) (s.lvm b.nB)) b.hAIn b.hBIn b.hinj b.hcarry
    (fun s => by rw [stripWidthTag_withWidthTag_MULXHI]; exact applyOpn_mulhi _ _)

/-- An `addCarryLo` binding along the renaming `physRename body tbl`: the logical
    destination `nDst` receives the data word of the carry-chain add of the
    values at `nA`, `nB` with carry-in the low bit of the value at `nC`. -/
structure AddCarryLoBinding (w : Nat) (body : Lcmd) (tbl : Array Nat) where
  nDst : String
  nA : String
  nB : String
  nC : String
  /-- The logical names live before the binding. -/
  Lin : List String
  /-- The logical names live after the binding. -/
  Lout : List String
  /-- The binding reads its first addend. -/
  hAIn : nA ∈ Lin
  /-- The binding reads its second addend. -/
  hBIn : nB ∈ Lin
  /-- The binding reads its carry-in. -/
  hCIn : nC ∈ Lin
  /-- No other name live after the binding shares the destination's physical
      register. -/
  hinj : ∀ m ∈ Lout, physRename body tbl m = physRename body tbl nDst → m = nDst
  /-- Every name live after the binding other than its destination was already
      live before it. -/
  hcarry : ∀ m ∈ Lout, m ≠ nDst → m ∈ Lin

/-- The physical block of an `addCarryLo` binding: `ADCX ρ nDst, ρ nA, ρ nB,
    ρ nC` at width `w`. -/
def AddCarryLoBinding.block {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : AddCarryLoBinding w body tbl) : List LinstrR :=
  [.Lopn [.reg (physRename body tbl b.nDst)] (withWidthTag w "ADCX")
    [.reg (physRename body tbl b.nA), .reg (physRename body tbl b.nB),
     .reg (physRename body tbl b.nC)]]

/-- The virtual transformer of an `addCarryLo` binding: write `addCarryWord` of
    the operand values at `nDst`. -/
def AddCarryLoBinding.vstep {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : AddCarryLoBinding w body tbl) : Lstate w → Lstate w :=
  fun s => s.setReg b.nDst
    (addCarryWord (s.lvm b.nA) (s.lvm b.nB) (BitVec.setWidth 1 (s.lvm b.nC)))

/-- An `addCarryLo` binding's block re-establishes `StoreRel` against its virtual
    transformer. -/
theorem AddCarryLoBinding.maintains {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : AddCarryLoBinding w body tbl) :
    BlockMaintains body tbl b.Lin b.Lout b.block b.vstep :=
  remapBlockMaintains3 body tbl b.Lin b.Lout b.nDst b.nA b.nB b.nC (withWidthTag w "ADCX")
    (fun s => addCarryWord (s.lvm b.nA) (s.lvm b.nB) (BitVec.setWidth 1 (s.lvm b.nC)))
    b.hAIn b.hBIn b.hCIn b.hinj b.hcarry
    (fun s => by rw [stripWidthTag_withWidthTag_ADCX]; exact applyOpn_addCarryLo _ _ _)

/-- An `addCarryHi` binding along the renaming `physRename body tbl`: the logical
    destination `nDst` receives the carry-out bit of the same add, packaged at the
    uniform word width. -/
structure AddCarryHiBinding (w : Nat) (body : Lcmd) (tbl : Array Nat) where
  nDst : String
  nA : String
  nB : String
  nC : String
  /-- The logical names live before the binding. -/
  Lin : List String
  /-- The logical names live after the binding. -/
  Lout : List String
  /-- The binding reads its first addend. -/
  hAIn : nA ∈ Lin
  /-- The binding reads its second addend. -/
  hBIn : nB ∈ Lin
  /-- The binding reads its carry-in. -/
  hCIn : nC ∈ Lin
  /-- No other name live after the binding shares the destination's physical
      register. -/
  hinj : ∀ m ∈ Lout, physRename body tbl m = physRename body tbl nDst → m = nDst
  /-- Every name live after the binding other than its destination was already
      live before it. -/
  hcarry : ∀ m ∈ Lout, m ≠ nDst → m ∈ Lin

/-- The physical block of an `addCarryHi` binding: `ADCXHI ρ nDst, ρ nA, ρ nB,
    ρ nC` at width `w`. -/
def AddCarryHiBinding.block {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : AddCarryHiBinding w body tbl) : List LinstrR :=
  [.Lopn [.reg (physRename body tbl b.nDst)] (withWidthTag w "ADCXHI")
    [.reg (physRename body tbl b.nA), .reg (physRename body tbl b.nB),
     .reg (physRename body tbl b.nC)]]

/-- The virtual transformer of an `addCarryHi` binding: write the width-extended
    `carryOutBit` of the operand values at `nDst`. -/
def AddCarryHiBinding.vstep {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : AddCarryHiBinding w body tbl) : Lstate w → Lstate w :=
  fun s => s.setReg b.nDst
    (BitVec.setWidth w (carryOutBit (s.lvm b.nA) (s.lvm b.nB) (BitVec.setWidth 1 (s.lvm b.nC))))

/-- An `addCarryHi` binding's block re-establishes `StoreRel` against its virtual
    transformer. -/
theorem AddCarryHiBinding.maintains {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : AddCarryHiBinding w body tbl) :
    BlockMaintains body tbl b.Lin b.Lout b.block b.vstep :=
  remapBlockMaintains3 body tbl b.Lin b.Lout b.nDst b.nA b.nB b.nC (withWidthTag w "ADCXHI")
    (fun s => BitVec.setWidth w
      (carryOutBit (s.lvm b.nA) (s.lvm b.nB) (BitVec.setWidth 1 (s.lvm b.nC))))
    b.hAIn b.hBIn b.hCIn b.hinj b.hcarry
    (fun s => by rw [stripWidthTag_withWidthTag_ADCXHI]; exact applyOpn_addCarryHi _ _ _)

/-- A `select` binding along the renaming `physRename body tbl`: the logical
    destination `nDst` receives the value at `nA` when the low bit of the value
    at `nCond` is one and the value at `nB` when it is zero. -/
structure SelectBinding (w : Nat) (body : Lcmd) (tbl : Array Nat) where
  nDst : String
  nCond : String
  nA : String
  nB : String
  /-- The logical names live before the binding. -/
  Lin : List String
  /-- The logical names live after the binding. -/
  Lout : List String
  /-- The binding reads its condition. -/
  hCondIn : nCond ∈ Lin
  /-- The binding reads the word taken when the condition bit is one. -/
  hAIn : nA ∈ Lin
  /-- The binding reads the word taken when the condition bit is zero. -/
  hBIn : nB ∈ Lin
  /-- No other name live after the binding shares the destination's physical
      register. -/
  hinj : ∀ m ∈ Lout, physRename body tbl m = physRename body tbl nDst → m = nDst
  /-- Every name live after the binding other than its destination was already
      live before it. -/
  hcarry : ∀ m ∈ Lout, m ≠ nDst → m ∈ Lin

/-- The physical block of a `select` binding: `CMOV ρ nDst, ρ nCond, ρ nA,
    ρ nB` at width `w`. -/
def SelectBinding.block {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : SelectBinding w body tbl) : List LinstrR :=
  [.Lopn [.reg (physRename body tbl b.nDst)] (withWidthTag w "CMOV")
    [.reg (physRename body tbl b.nCond), .reg (physRename body tbl b.nA),
     .reg (physRename body tbl b.nB)]]

/-- The virtual transformer of a `select` binding: write `selectW` of the
    condition bit and the two operand values at `nDst`. -/
def SelectBinding.vstep {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : SelectBinding w body tbl) : Lstate w → Lstate w :=
  fun s => s.setReg b.nDst
    (selectW (BitVec.setWidth 1 (s.lvm b.nCond)) (s.lvm b.nA) (s.lvm b.nB))

/-- A `select` binding's block re-establishes `StoreRel` against its virtual
    transformer. -/
theorem SelectBinding.maintains {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : SelectBinding w body tbl) :
    BlockMaintains body tbl b.Lin b.Lout b.block b.vstep :=
  remapBlockMaintains3 body tbl b.Lin b.Lout b.nDst b.nCond b.nA b.nB
    (withWidthTag w "CMOV")
    (fun s => selectW (BitVec.setWidth 1 (s.lvm b.nCond)) (s.lvm b.nA) (s.lvm b.nB))
    b.hCondIn b.hAIn b.hBIn b.hinj b.hcarry
    (fun s => by rw [stripWidthTag_withWidthTag_CMOV]; exact applyOpn_select _ _ _)

/-! ## 4. The step of the `select` head

`opToLinstrR` emits `select w` as `CMOV[:w] dst, cond, a, b`, and `applyOpn`
models that mnemonic as the dialect's `selectW`. -/

/-- The `select` head writes the dialect's `selectW` of the condition register's
    low bit and the two data registers, and advances the pc. -/
theorem lsemStep_select {w : Nat} (nD nC nA nB : String) (wOp : Nat)
    (s : Lstate w) :
    lsemStep (.Lopn [.reg nD] (withWidthTag wOp "CMOV")
      [.reg nC, .reg nA, .reg nB]) s
      = some ((s.setReg nD
          (selectW (BitVec.setWidth 1 (s.lvm nC)) (s.lvm nA) (s.lvm nB))).nextPc) :=
  lsemStep_src3 nD nC nA nB (withWidthTag wOp "CMOV") s _
    (by rw [stripWidthTag_withWidthTag_CMOV]; exact applyOpn_select _ _ _)

/-! ## 5. The `physBody` expansion of the three heads -/

/-- `physBody` expands the `mulhi` head to the single renamed instruction. -/
theorem physBodyElem_mulhi (body : Lcmd) (tbl : Array Nat) (ii : Nat)
    (nDst nA nB : String) (w : Nat) :
    (physBodyElem body tbl ⟨ii, .Lopn [.reg nDst] (withWidthTag w "MULXHI")
        [.reg nA, .reg nB]⟩).map (·.li_i)
      = [.Lopn [.reg (physRename body tbl nDst)] (withWidthTag w "MULXHI")
          [.reg (physRename body tbl nA), .reg (physRename body tbl nB)]] := by
  simp only [physBodyElem, not_isBinop_MULXHI, Bool.false_eq_true, if_false,
    isMemStore_withWidthTag_MULXHI]
  simp [remapOperand, physRename]

/-- `physBody` expands a three-source width-tagged head outside the two-address
    binop alphabet to the single renamed instruction. -/
theorem physBodyElem_src3 (body : Lcmd) (tbl : Array Nat) (ii : Nat)
    (nDst nA nB nC opn : String)
    (hbin : isTwoAddrBinop opn = false) :
    (physBodyElem body tbl ⟨ii, .Lopn [.reg nDst] opn
        [.reg nA, .reg nB, .reg nC]⟩).map (·.li_i)
      = [.Lopn [.reg (physRename body tbl nDst)] opn
          [.reg (physRename body tbl nA), .reg (physRename body tbl nB),
           .reg (physRename body tbl nC)]] := by
  simp only [physBodyElem, hbin, Bool.false_eq_true, if_false]
  simp [remapOperand, physRename]

/-! ## 6. The sum of binding kinds -/

/-- A binding of the binop-or-constant-or-widening-or-carry-or-select
    fragment. -/
inductive MulCarryBinding (w : Nat) (body : Lcmd) (tbl : Array Nat) where
  | arith (b : ArithConstBinding w body tbl)
  | binopWide (b : ToLprogFaithfulBinopWide.BinopWideBinding w body tbl)
  | binopMov (b : ToLprogFaithfulBinopMov.BinopMovBinding w body tbl)
  | binopMovWide (b : ToLprogFaithfulBinopMov.BinopMovWideBinding w body tbl)
  | mulhi (m : MulHiBinding w body tbl)
  | addCarryLo (c : AddCarryLoBinding w body tbl)
  | addCarryHi (c : AddCarryHiBinding w body tbl)
  | select (c : SelectBinding w body tbl)

/-- The physical block of a binding. -/
def MulCarryBinding.block {w : Nat} {body : Lcmd} {tbl : Array Nat} :
    MulCarryBinding w body tbl → List LinstrR
  | .arith b => b.block
  | .binopWide b => b.block
  | .binopMov b => b.block
  | .binopMovWide b => b.block
  | .mulhi m => m.block
  | .addCarryLo c => c.block
  | .addCarryHi c => c.block
  | .select c => c.block

/-- The virtual transformer of a binding. -/
def MulCarryBinding.vstep {w : Nat} {body : Lcmd} {tbl : Array Nat} :
    MulCarryBinding w body tbl → Lstate w → Lstate w
  | .arith b => b.vstep
  | .binopWide b => b.vstep
  | .binopMov b => b.vstep
  | .binopMovWide b => b.vstep
  | .mulhi m => m.vstep
  | .addCarryLo c => c.vstep
  | .addCarryHi c => c.vstep
  | .select c => c.vstep

/-- The logical names live before a binding. -/
def MulCarryBinding.Lin {w : Nat} {body : Lcmd} {tbl : Array Nat} :
    MulCarryBinding w body tbl → List String
  | .arith b => b.Lin
  | .binopWide b => b.Lin
  | .binopMov b => b.Lin
  | .binopMovWide b => b.Lin
  | .mulhi m => m.Lin
  | .addCarryLo c => c.Lin
  | .addCarryHi c => c.Lin
  | .select c => c.Lin

/-- The logical names live after a binding. -/
def MulCarryBinding.Lout {w : Nat} {body : Lcmd} {tbl : Array Nat} :
    MulCarryBinding w body tbl → List String
  | .arith b => b.Lout
  | .binopWide b => b.Lout
  | .binopMov b => b.Lout
  | .binopMovWide b => b.Lout
  | .mulhi m => m.Lout
  | .addCarryLo c => c.Lout
  | .addCarryHi c => c.Lout
  | .select c => c.Lout

/-- Every binding's block is a `BlockMaintains` witness across its live sets. -/
theorem MulCarryBinding.maintains {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : MulCarryBinding w body tbl) :
    BlockMaintains body tbl b.Lin b.Lout b.block b.vstep := by
  cases b with
  | arith b => exact b.maintains
  | binopWide b => exact b.maintains
  | binopMov b => exact b.maintains
  | binopMovWide b => exact b.maintains
  | mulhi m => exact m.maintains
  | addCarryLo c => exact c.maintains
  | addCarryHi c => exact c.maintains
  | select c => exact c.maintains

/-- A cover of a source body by a binding list: the `physBody` expansion of the
    `i`-th instruction, projected to `LinstrR`, is the `i`-th binding's block. -/
inductive BodyCoverMCS {w : Nat} (body : Lcmd) (tbl : Array Nat) :
    Lcmd → List (MulCarryBinding w body tbl) → Prop where
  | nil : BodyCoverMCS body tbl [] []
  | cons {i : Linstr} {b : MulCarryBinding w body tbl} {is : Lcmd}
      {bs : List (MulCarryBinding w body tbl)} :
      (physBodyElem body tbl i).map (·.li_i) = b.block → BodyCoverMCS body tbl is bs →
      BodyCoverMCS body tbl (i :: is) (b :: bs)

/-- The `physBody` expansion of a covered sub-body is the flattened block list. -/
theorem physBody_flatMap_blocksMCS {w : Nat} (body : Lcmd) (sub : Lcmd)
    (bs : List (MulCarryBinding w body (bodyPhysTable body)))
    (hcover : BodyCoverMCS body (bodyPhysTable body) sub bs) :
    sub.flatMap (fun i => (physBodyElem body (bodyPhysTable body) i).map (·.li_i))
      = (bs.map (·.block)).flatten := by
  induction hcover with
  | nil => rfl
  | cons hib _ ih => rw [List.flatMap_cons, List.map_cons, List.flatten_cons, ih, hib]

/-- The literal `physBody` of a covered body, projected to `LinstrR`, is the
    flattened block list. -/
theorem physBody_map_li_iMCS {w : Nat} (body : Lcmd)
    (bs : List (MulCarryBinding w body (bodyPhysTable body)))
    (hcover : BodyCoverMCS body (bodyPhysTable body) body bs) :
    (physBody (fun _ => none) body).map (·.li_i) = (bs.map (·.block)).flatten := by
  rw [physBody_eq_flatMap, List.map_flatMap]
  exact physBody_flatMap_blocksMCS body body bs hcover

/-- Running the flattened block list of a binding list from a `StoreRel`-related
    start reads the composed virtual store at every renamed register. -/
theorem mulCarryBody_lsem_result {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (bs : List (MulCarryBinding w body tbl)) (L N : List String)
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
theorem physBody_lsem_resultMCS {w : Nat} (body : Lcmd)
    (bs : List (MulCarryBinding w body (bodyPhysTable body)))
    (hcover : BodyCoverMCS body (bodyPhysTable body) body bs)
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w) (hrel : StoreRel body (bodyPhysTable body) L s s')
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ s'', lsemStraight ((physBody (fun _ => none) body).map (·.li_i)) s' = some s''
      ∧ s''.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  rw [physBody_map_li_iMCS body bs hcover]
  exact mulCarryBody_lsem_result body (bodyPhysTable body) bs L N hch s s' hrel nRes hnRes

/-! ## 7. The `Com` fragment and its threaded cover data -/

/-- A `Com` all of whose bindings are non-shift binary `regArith` binops at a
    default width (`var`) or at width 64 (`var64`), `regConst` loads, or
    `mulhi` / `addCarryLo` / `addCarryHi` / `select` bindings, terminating at
    `.ret`. -/
inductive UniformRegArithMCS : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Prop where
  | ret {Γ t} (v : Ctxt.Var Γ t) : UniformRegArithMCS (.ret v)
  | var {Γ s} {w : Nat} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
      (a0 a1 : Ctxt.Var Γ (JasminTy.reg w)) (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hw : w ≠ 64) (hns : NonShift bop) (hbody : UniformRegArithMCS body) :
      UniformRegArithMCS
        (.var ⟨JasminOp.regArith bop w, heq, .cons a0 (.cons a1 .nil)⟩ body)
  | var64 {Γ s} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop 64) = .reg 64)
      (a0 a1 : Ctxt.Var Γ (JasminTy.reg 64))
      (body : Com jasminDialect (JasminTy.reg 64 :: Γ) s)
      (hns : NonShift bop) (hbody : UniformRegArithMCS body) :
      UniformRegArithMCS
        (.var ⟨JasminOp.regArith bop 64, heq, .cons a0 (.cons a1 .nil)⟩ body)
  | const {Γ s} {w n : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
      (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hbody : UniformRegArithMCS body) :
      UniformRegArithMCS (.var ⟨JasminOp.regConst w n, heq, .nil⟩ body)
  | mulhi {Γ s} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
      (a0 a1 : Ctxt.Var Γ (JasminTy.reg w)) (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hbody : UniformRegArithMCS body) :
      UniformRegArithMCS (.var ⟨JasminOp.mulhi w, heq, .cons a0 (.cons a1 .nil)⟩ body)
  | addCarryLo {Γ s} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
      (a0 a1 : Ctxt.Var Γ (JasminTy.reg w)) (a2 : Ctxt.Var Γ (JasminTy.reg 1))
      (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hbody : UniformRegArithMCS body) :
      UniformRegArithMCS
        (.var ⟨JasminOp.addCarryLo w, heq, .cons a0 (.cons a1 (.cons a2 .nil))⟩ body)
  | addCarryHi {Γ s} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
      (a0 a1 : Ctxt.Var Γ (JasminTy.reg w)) (a2 : Ctxt.Var Γ (JasminTy.reg 1))
      (body : Com jasminDialect (JasminTy.reg 1 :: Γ) s)
      (hbody : UniformRegArithMCS body) :
      UniformRegArithMCS
        (.var ⟨JasminOp.addCarryHi w, heq, .cons a0 (.cons a1 (.cons a2 .nil))⟩ body)
  | select {Γ s} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
      (c : Ctxt.Var Γ (JasminTy.reg 1)) (a0 a1 : Ctxt.Var Γ (JasminTy.reg w))
      (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hbody : UniformRegArithMCS body) :
      UniformRegArithMCS
        (.var ⟨JasminOp.select w, heq, .cons c (.cons a0 (.cons a1 .nil))⟩ body)

/-- The binop-or-constant fragment is contained in the extended fragment. -/
theorem UniformRegArithConst.toMCS {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (h : UniformRegArithConst com) :
    UniformRegArithMCS com := by
  induction h with
  | ret v => exact .ret v
  | var bop heq a0 a1 body hw hns _ ih => exact .var bop heq a0 a1 body hw hns ih
  | const heq body _ ih => exact .const heq body ih

/-- Cover data threaded along an extended `Com` over a fixed whole `body`/`tbl`.
    The binop and constant arms carry the data of `CoverDataConst`; the three new
    arms carry a binding whose destination is `regName d` and whose sources are
    the resolved operand names. -/
inductive CoverDataMCS {w : Nat} (body : Lcmd) (tbl : Array Nat) (nArgs : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) →
    List (MulCarryBinding w body tbl) → Prop where
  | ret {Γ t} (v : Ctxt.Var Γ t) (d : Nat) : CoverDataMCS body tbl nArgs (.ret v) d []
  | var {Γ s} {bop : JasminBinOp}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w}
      {a0 a1 : Ctxt.Var Γ (JasminTy.reg w)} {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (hw : w ≠ 64) (hns : bop ≠ .shl ∧ bop ≠ .shr ∧ bop ≠ .andn)
      (b : BinopBinding w body tbl) (bs : List (MulCarryBinding w body tbl))
      (hdst : b.nDst = regName d)
      (hopn : b.opn = withWidthTag w (binOpName bop))
      (hsrc : b.nSrc = resolveVarName d nArgs a1)
      (hcol : physRename body tbl (resolveVarName d nArgs a0)
          = physRename body tbl (regName d))
      (htail : CoverDataMCS body tbl nArgs bdy (d + 1) bs) :
      CoverDataMCS body tbl nArgs
        (.var ⟨JasminOp.regArith bop w, heq, .cons a0 (.cons a1 .nil)⟩ bdy) d
        (.arith (.binop b) :: bs)
  | var64 {Γ s} {bop : JasminBinOp}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop 64) = .reg 64}
      {a0 a1 : Ctxt.Var Γ (JasminTy.reg 64)}
      {bdy : Com jasminDialect (JasminTy.reg 64 :: Γ) s}
      (d : Nat) (hns : NonShift bop)
      (b : ToLprogFaithfulBinopWide.BinopWideBinding w body tbl)
      (bs : List (MulCarryBinding w body tbl))
      (hdst : b.nDst = regName d)
      (hbop : b.bop = bop)
      (hsrc : b.nSrc = resolveVarName d nArgs a1)
      (hcol : physRename body tbl (resolveVarName d nArgs a0)
          = physRename body tbl (regName d))
      (htail : CoverDataMCS body tbl nArgs bdy (d + 1) bs) :
      CoverDataMCS body tbl nArgs
        (.var ⟨JasminOp.regArith bop 64, heq, .cons a0 (.cons a1 .nil)⟩ bdy) d
        (.binopWide b :: bs)
  | varMov {Γ s} {bop : JasminBinOp}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w}
      {a0 a1 : Ctxt.Var Γ (JasminTy.reg w)} {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (hw : w ≠ 64) (hns : NonShift bop)
      (b : ToLprogFaithfulBinopMov.BinopMovBinding w body tbl)
      (bs : List (MulCarryBinding w body tbl))
      (hdst : b.nDst = regName d)
      (hopn : b.opn = withWidthTag w (binOpName bop))
      (hS0 : b.nS0 = resolveVarName d nArgs a0)
      (hsrc : b.nSrc = resolveVarName d nArgs a1)
      (htail : CoverDataMCS body tbl nArgs bdy (d + 1) bs) :
      CoverDataMCS body tbl nArgs
        (.var ⟨JasminOp.regArith bop w, heq, .cons a0 (.cons a1 .nil)⟩ bdy) d
        (.binopMov b :: bs)
  | var64Mov {Γ s} {bop : JasminBinOp}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop 64) = .reg 64}
      {a0 a1 : Ctxt.Var Γ (JasminTy.reg 64)}
      {bdy : Com jasminDialect (JasminTy.reg 64 :: Γ) s}
      (d : Nat) (hns : NonShift bop)
      (b : ToLprogFaithfulBinopMov.BinopMovWideBinding w body tbl)
      (bs : List (MulCarryBinding w body tbl))
      (hdst : b.nDst = regName d)
      (hbop : b.bop = bop)
      (hS0 : b.nS0 = resolveVarName d nArgs a0)
      (hsrc : b.nSrc = resolveVarName d nArgs a1)
      (htail : CoverDataMCS body tbl nArgs bdy (d + 1) bs) :
      CoverDataMCS body tbl nArgs
        (.var ⟨JasminOp.regArith bop 64, heq, .cons a0 (.cons a1 .nil)⟩ bdy) d
        (.binopMovWide b :: bs)
  | const {Γ s} {n : Nat}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w}
      {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (c : ConstBinding w body tbl) (bs : List (MulCarryBinding w body tbl))
      (hdst : c.nDst = regName d) (hn : c.n = n)
      (htail : CoverDataMCS body tbl nArgs bdy (d + 1) bs) :
      CoverDataMCS body tbl nArgs
        (.var ⟨JasminOp.regConst w n, heq, .nil⟩ bdy) d (.arith (.const c) :: bs)
  | mulhi {Γ s}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w}
      {a0 a1 : Ctxt.Var Γ (JasminTy.reg w)} {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (m : MulHiBinding w body tbl) (bs : List (MulCarryBinding w body tbl))
      (hdst : m.nDst = regName d)
      (hA : m.nA = resolveVarName d nArgs a0)
      (hB : m.nB = resolveVarName d nArgs a1)
      (htail : CoverDataMCS body tbl nArgs bdy (d + 1) bs) :
      CoverDataMCS body tbl nArgs
        (.var ⟨JasminOp.mulhi w, heq, .cons a0 (.cons a1 .nil)⟩ bdy) d (.mulhi m :: bs)
  | addCarryLo {Γ s}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w}
      {a0 a1 : Ctxt.Var Γ (JasminTy.reg w)} {a2 : Ctxt.Var Γ (JasminTy.reg 1)}
      {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (c : AddCarryLoBinding w body tbl) (bs : List (MulCarryBinding w body tbl))
      (hdst : c.nDst = regName d)
      (hA : c.nA = resolveVarName d nArgs a0)
      (hB : c.nB = resolveVarName d nArgs a1)
      (hC : c.nC = resolveVarName d nArgs a2)
      (htail : CoverDataMCS body tbl nArgs bdy (d + 1) bs) :
      CoverDataMCS body tbl nArgs
        (.var ⟨JasminOp.addCarryLo w, heq, .cons a0 (.cons a1 (.cons a2 .nil))⟩ bdy) d
        (.addCarryLo c :: bs)
  | addCarryHi {Γ s}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1}
      {a0 a1 : Ctxt.Var Γ (JasminTy.reg w)} {a2 : Ctxt.Var Γ (JasminTy.reg 1)}
      {bdy : Com jasminDialect (JasminTy.reg 1 :: Γ) s}
      (d : Nat) (c : AddCarryHiBinding w body tbl) (bs : List (MulCarryBinding w body tbl))
      (hdst : c.nDst = regName d)
      (hA : c.nA = resolveVarName d nArgs a0)
      (hB : c.nB = resolveVarName d nArgs a1)
      (hC : c.nC = resolveVarName d nArgs a2)
      (htail : CoverDataMCS body tbl nArgs bdy (d + 1) bs) :
      CoverDataMCS body tbl nArgs
        (.var ⟨JasminOp.addCarryHi w, heq, .cons a0 (.cons a1 (.cons a2 .nil))⟩ bdy) d
        (.addCarryHi c :: bs)
  | select {Γ s}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w}
      {a0 : Ctxt.Var Γ (JasminTy.reg 1)} {a1 a2 : Ctxt.Var Γ (JasminTy.reg w)}
      {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (c : SelectBinding w body tbl) (bs : List (MulCarryBinding w body tbl))
      (hdst : c.nDst = regName d)
      (hCond : c.nCond = resolveVarName d nArgs a0)
      (hA : c.nA = resolveVarName d nArgs a1)
      (hB : c.nB = resolveVarName d nArgs a2)
      (htail : CoverDataMCS body tbl nArgs bdy (d + 1) bs) :
      CoverDataMCS body tbl nArgs
        (.var ⟨JasminOp.select w, heq, .cons a0 (.cons a1 (.cons a2 .nil))⟩ bdy) d
        (.select c :: bs)

/-- Cover data exists only for an extended `Com`. -/
theorem CoverDataMCS.uniformRegArithMCS {w : Nat} {body : Lcmd} {tbl : Array Nat}
    {nArgs : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy} {com : Com jasminDialect Γ t}
    {d : Nat} {bs : List (MulCarryBinding w body tbl)}
    (h : CoverDataMCS body tbl nArgs com d bs) : UniformRegArithMCS com := by
  induction h with
  | ret v d => exact .ret v
  | var d hw hns b bs _ _ _ _ _ ih => exact .var _ _ _ _ _ hw hns ih
  | var64 d hns b bs _ _ _ _ _ ih => exact .var64 _ _ _ _ _ hns ih
  | varMov d hw hns b bs _ _ _ _ _ ih => exact .var _ _ _ _ _ hw hns ih
  | var64Mov d hns b bs _ _ _ _ _ ih => exact .var64 _ _ _ _ _ hns ih
  | const d c bs _ _ _ ih => exact .const _ _ ih
  | mulhi d m bs _ _ _ _ ih => exact .mulhi _ _ _ _ ih
  | addCarryLo d c bs _ _ _ _ _ ih => exact .addCarryLo _ _ _ _ _ ih
  | addCarryHi d c bs _ _ _ _ _ ih => exact .addCarryHi _ _ _ _ _ ih
  | select d c bs _ _ _ _ _ ih => exact .select _ _ _ _ _ ih

/-- Binop-or-constant cover data is cover data of the extended fragment, with
    every binding tagged `arith`. -/
theorem CoverDataConst.toMCS {w : Nat} {body : Lcmd} {tbl : Array Nat} {nArgs : Nat}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {com : Com jasminDialect Γ t} {d : Nat}
    {bs : List (ArithConstBinding w body tbl)}
    (h : CoverDataConst body tbl nArgs com d bs) :
    CoverDataMCS body tbl nArgs com d (bs.map .arith) := by
  induction h with
  | ret v d => exact .ret v d
  | var d hw hns b bs hdst hopn hsrc hcol _ ih => exact .var d hw hns b _ hdst hopn hsrc hcol ih
  | const d c bs hdst hn _ ih => exact .const d c _ hdst hn ih

/-! ## 8. The head shapes -/

/-- The `bindingHeads` head of a `mulhi w` binding at depth `curDepth` is
    `MULXHI[:w] regName curDepth, a0, a1`. -/
theorem bindingHeads_mulhi_eq {Γ : Ctxt jasminDialect} {s : JasminTy}
    (nArgs w : Nat)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
    (a0 a1 : Ctxt.Var Γ (JasminTy.reg w))
    (body : Com jasminDialect (JasminTy.reg w :: Γ) s) (curDepth : Nat) :
    bindingHeads nArgs argName (fun _ => none)
      (.var ⟨JasminOp.mulhi w, heq, .cons a0 (.cons a1 .nil)⟩ body) curDepth
      = (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w "MULXHI")
          [.reg (resolveVarName curDepth nArgs a0),
           .reg (resolveVarName curDepth nArgs a1)]⟩ : Linstr)
        :: bindingHeads nArgs argName (fun _ => none) body (curDepth + 1) := by
  show (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w "MULXHI")
      [resolveVar curDepth nArgs argName (fun _ => none) a0,
       resolveVar curDepth nArgs argName (fun _ => none) a1]⟩ : Linstr) :: _ = _
  rw [resolveVar_eq_reg, resolveVar_eq_reg]

/-- The `bindingHeads` head of an `addCarryLo w` binding at depth `curDepth` is
    `ADCX[:w] regName curDepth, a0, a1, a2`. -/
theorem bindingHeads_addCarryLo_eq {Γ : Ctxt jasminDialect} {s : JasminTy}
    (nArgs w : Nat)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
    (a0 a1 : Ctxt.Var Γ (JasminTy.reg w)) (a2 : Ctxt.Var Γ (JasminTy.reg 1))
    (body : Com jasminDialect (JasminTy.reg w :: Γ) s) (curDepth : Nat) :
    bindingHeads nArgs argName (fun _ => none)
      (.var ⟨JasminOp.addCarryLo w, heq, .cons a0 (.cons a1 (.cons a2 .nil))⟩ body) curDepth
      = (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w "ADCX")
          [.reg (resolveVarName curDepth nArgs a0),
           .reg (resolveVarName curDepth nArgs a1),
           .reg (resolveVarName curDepth nArgs a2)]⟩ : Linstr)
        :: bindingHeads nArgs argName (fun _ => none) body (curDepth + 1) := by
  show (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w "ADCX")
      [resolveVar curDepth nArgs argName (fun _ => none) a0,
       resolveVar curDepth nArgs argName (fun _ => none) a1,
       resolveVar curDepth nArgs argName (fun _ => none) a2]⟩ : Linstr) :: _ = _
  rw [resolveVar_eq_reg, resolveVar_eq_reg, resolveVar_eq_reg]

/-- The `bindingHeads` head of an `addCarryHi w` binding at depth `curDepth` is
    `ADCXHI[:w] regName curDepth, a0, a1, a2`. -/
theorem bindingHeads_addCarryHi_eq {Γ : Ctxt jasminDialect} {s : JasminTy}
    (nArgs w : Nat)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
    (a0 a1 : Ctxt.Var Γ (JasminTy.reg w)) (a2 : Ctxt.Var Γ (JasminTy.reg 1))
    (body : Com jasminDialect (JasminTy.reg 1 :: Γ) s) (curDepth : Nat) :
    bindingHeads nArgs argName (fun _ => none)
      (.var ⟨JasminOp.addCarryHi w, heq, .cons a0 (.cons a1 (.cons a2 .nil))⟩ body) curDepth
      = (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w "ADCXHI")
          [.reg (resolveVarName curDepth nArgs a0),
           .reg (resolveVarName curDepth nArgs a1),
           .reg (resolveVarName curDepth nArgs a2)]⟩ : Linstr)
        :: bindingHeads nArgs argName (fun _ => none) body (curDepth + 1) := by
  show (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w "ADCXHI")
      [resolveVar curDepth nArgs argName (fun _ => none) a0,
       resolveVar curDepth nArgs argName (fun _ => none) a1,
       resolveVar curDepth nArgs argName (fun _ => none) a2]⟩ : Linstr) :: _ = _
  rw [resolveVar_eq_reg, resolveVar_eq_reg, resolveVar_eq_reg]

/-- The `bindingHeads` head of a `select w` binding at depth `curDepth` is
    `CMOV[:w] regName curDepth, a0, a1, a2`. -/
theorem bindingHeads_select_eq {Γ : Ctxt jasminDialect} {s : JasminTy}
    (nArgs w : Nat)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (a0 : Ctxt.Var Γ (JasminTy.reg 1)) (a1 a2 : Ctxt.Var Γ (JasminTy.reg w))
    (body : Com jasminDialect (JasminTy.reg w :: Γ) s) (curDepth : Nat) :
    bindingHeads nArgs argName (fun _ => none)
      (.var ⟨JasminOp.select w, heq, .cons a0 (.cons a1 (.cons a2 .nil))⟩ body) curDepth
      = (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w "CMOV")
          [.reg (resolveVarName curDepth nArgs a0),
           .reg (resolveVarName curDepth nArgs a1),
           .reg (resolveVarName curDepth nArgs a2)]⟩ : Linstr)
        :: bindingHeads nArgs argName (fun _ => none) body (curDepth + 1) := by
  show (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w "CMOV")
      [resolveVar curDepth nArgs argName (fun _ => none) a0,
       resolveVar curDepth nArgs argName (fun _ => none) a1,
       resolveVar curDepth nArgs argName (fun _ => none) a2]⟩ : Linstr) :: _ = _
  rw [resolveVar_eq_reg, resolveVar_eq_reg, resolveVar_eq_reg]

/-- The threaded cover data yields a cover of the head list `bindingHeads … com d`. -/
theorem coverDataMCS_bodyCover {w : Nat} (body : Lcmd) (tbl : Array Nat) (nArgs : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (d : Nat) (bs : List (MulCarryBinding w body tbl))
    (hcd : CoverDataMCS body tbl nArgs com d bs) :
    BodyCoverMCS body tbl (bindingHeads nArgs argName (fun _ => none) com d) bs := by
  induction hcd with
  | ret v d => exact .nil
  | var d hw hns b bs hdst hopn hsrc hcol _ ih =>
      rw [bindingHeads_var_eq]
      exact .cons (physBodyElem_of_realizes body tbl _ b
        (regArithHead_realizes body tbl nArgs d _ w hw hns _ _ b hdst hopn hsrc hcol)) ih
  | var64 d hns b bs hdst hbop hsrc hcol _ ih =>
      rw [bindingHeads_var_eq]
      exact .cons (ToLprogFaithfulBinopWide.regArithHead64_cover body tbl nArgs d _ hns _ _ b
        hdst hbop hsrc hcol) ih
  | varMov d hw hns b bs hdst hopn hS0 hsrc _ ih =>
      rw [bindingHeads_var_eq]
      exact .cons (ToLprogFaithfulBinopMov.regArithHeadMov_cover body tbl nArgs d _ w hw hns _ _ b
        hdst hopn hS0 hsrc) ih
  | var64Mov d hns b bs hdst hbop hS0 hsrc _ ih =>
      rw [bindingHeads_var_eq]
      exact .cons (ToLprogFaithfulBinopMov.regArithHeadMov64_cover body tbl nArgs d _ hns _ _ b
        hdst hbop hS0 hsrc) ih
  | const d c bs hdst hn _ ih =>
      rw [bindingHeads_const_eq]
      refine .cons ?_ ih
      rw [physBodyElem_regConst, MulCarryBinding.block, ArithConstBinding.block,
        ConstBinding.block, hdst, hn]
  | mulhi d m bs hdst hA hB _ ih =>
      rw [bindingHeads_mulhi_eq]
      refine .cons ?_ ih
      rw [physBodyElem_mulhi, MulCarryBinding.block, MulHiBinding.block, hdst, hA, hB]
  | addCarryLo d c bs hdst hA hB hC _ ih =>
      rw [bindingHeads_addCarryLo_eq]
      refine .cons ?_ ih
      rw [physBodyElem_src3 body tbl 0 _ _ _ _ _ (not_isBinop_ADCX _),
        MulCarryBinding.block, AddCarryLoBinding.block, hdst, hA, hB, hC]
  | addCarryHi d c bs hdst hA hB hC _ ih =>
      rw [bindingHeads_addCarryHi_eq]
      refine .cons ?_ ih
      rw [physBodyElem_src3 body tbl 0 _ _ _ _ _ (not_isBinop_ADCXHI _),
        MulCarryBinding.block, AddCarryHiBinding.block, hdst, hA, hB, hC]
  | select d c bs hdst hCond hA hB _ ih =>
      rw [bindingHeads_select_eq]
      refine .cons ?_ ih
      rw [physBodyElem_src3 body tbl 0 _ _ _ _ _ (not_isBinop_CMOV _),
        MulCarryBinding.block, SelectBinding.block, hdst, hCond, hA, hB]

/-- **Physical body faithfulness, extended fragment.** For a body that is the head
    list `bindingHeads … com d` of a `Com` with threaded `CoverDataMCS`, running
    the literal `physBody (fun _ => none) body` from a `StoreRel`-related start
    reads the composed virtual store at the physical result register. -/
theorem physBody_lsem_result_uniformMCS {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (MulCarryBinding w body (bodyPhysTable body)))
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverDataMCS body (bodyPhysTable body) nArgs com d bs)
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w)
    (hrel : StoreRel body (bodyPhysTable body) L s s')
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ s'', lsemStraight ((physBody (fun _ => none) body).map (·.li_i)) s' = some s''
      ∧ s''.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  have hcov0 := coverDataMCS_bodyCover body (bodyPhysTable body) nArgs com d bs hcd
  have hcov : BodyCoverMCS body (bodyPhysTable body) body bs := hbody ▸ hcov0
  exact physBody_lsem_resultMCS body bs hcov L N hch s s' hrel nRes hnRes

/-! ## 9. The assembled whole-function theorems -/

/-- The straight-line core: `prologue ++ argMatSeq pairs ++ physBody` runs under
    `lsemStraight` from the entry state to a state whose physical result register
    reads the composed virtual store, and the list is `Lret`-free. -/
theorem prologue_argMat_body_lsemStraightMCS {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (MulCarryBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverDataMCS body (bodyPhysTable body) nArgs com d bs)
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
    physBody_lsem_result_uniformMCS body nArgs d com bs hbody hcd L N hch s sMat
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

/-- **Whole-function register-allocation faithfulness, extended fragment.** For a
    `Com` of non-shift binary `regArith`, `regConst`, `mulhi`, `addCarryLo` and
    `addCarryHi` bindings whose head list is `body`, with the threaded
    `CoverDataMCS`, running `buildPrologue ++ argMatSeq pairs ++ physBody ++
    Lret :: rest` under `lsemRun` from an entry state related to the virtual store
    off the materialization destinations (`hoff`), whose renaming avoids the
    prologue cells (`hdisjFrame`) and whose materialization sources carry the
    argument values (`habi`), reaches a state whose physical result register reads
    the composed virtual store. -/
theorem toLprogPhysAbi_faithful_uniformMCS {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (MulCarryBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (rest : List LinstrR) (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverDataMCS body (bodyPhysTable body) nArgs com d bs)
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
    prologue_argMat_body_lsemStraightMCS body nArgs d com bs virt tbl0 inLoadMap pairs
      hfresh hdist hbody hcd L N hch sEntry s hdisjFrame hoff habi nRes hnRes
  rw [lsemRun_body_ret _ _ _ hnoLret]
  exact ⟨sEnd, hrun, hread⟩

/-- **Whole-function faithfulness at the two-pointer ABI, extended fragment.** The
    instance of `toLprogPhysAbi_faithful_uniformMCS` at `twoPtrPairs`: `RDI` holds
    the virtual value of every name renamed onto `argName 0`'s register, and `RSI`
    that of every name renamed onto `argName 1`'s register. -/
theorem toLprogPhysAbi_faithful_uniformMCS_twoPtr {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (MulCarryBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (rest : List LinstrR)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverDataMCS body (bodyPhysTable body) nArgs com d bs)
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
  refine toLprogPhysAbi_faithful_uniformMCS body nArgs d com bs virt tbl0 inLoadMap rest _
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

/-- **Whole-function faithfulness with the callee-save restore epilogue, extended
    fragment.** The function body `buildPrologue ++ argMatSeq pairs ++ physBody ++
    calleeSaveRestoreEpilogue ++ Lret :: rest` run under `lsemRun`; the physical
    result register is read after the restore, so it is not one of the six
    callee-saved registers (`hResFree`). -/
theorem toLprogPhysAbi_faithful_uniformMCS_epilogue {w : Nat} (body : Lcmd)
    (nArgs d : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (MulCarryBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (rest : List LinstrR) (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverDataMCS body (bodyPhysTable body) nArgs com d bs)
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
    prologue_argMat_body_lsemStraightMCS body nArgs d com bs virt tbl0 inLoadMap pairs
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

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulMulCarrySel
