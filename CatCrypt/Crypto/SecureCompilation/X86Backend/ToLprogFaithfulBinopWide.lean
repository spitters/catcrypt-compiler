/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulConst

/-!
# Width-64 binary `regArith` bindings in the physical faithfulness fragment

A width-64 `regArith bop` binding emits the head mnemonic
`withWidthTag 64 (binOpName bop)`, which carries the `:64` tag, and
`physBodyElem` expands it through `lowerTwoAddr` with the legalization move
`MOV:64`. `ToLprogFaithfulBody.BinopBinding` carries an untagged mnemonic
(`hstrip`) and a block whose move is `MOV`, so it is the binding kind of the
default-width heads.

This module gives the width-64 binding kind. `lsemStep` reads an `Lopn`
mnemonic only through `stripWidthTag` on the register arm, so two instructions
that differ only in a width tag take the same step (`lsemStep_congr1`,
`lsemStep_congr2`). Lifting that over the four shapes of `legalizeBinop`
(`legalizeBinop_mnem_congr`) identifies the run of the `:64`-tagged block with
the run of the untagged one, and `BinopWideBinding.maintains` transfers
`ToLprogFaithfulWriteSide.legalizeBinop_storeRel_step` across that identity.

The binding carries the operator `bop` rather than a mnemonic string, so the tag
equations are the two computations `stripWidthTag (withWidthTag 64 (binOpName
bop)) = binOpName bop` and `stripWidthTag (binOpName bop) = binOpName bop`.

## Main definitions

* `BinopWideBinding`: a width-64 binop binding, with `block` the `:64`-tagged
  `legalizeBinop` at the move `MOV:64`.

## Main results

* `lsemStep_congr1`, `lsemStep_congr2`: a register-arm `Lopn` steps the same
  under two mnemonics with the same `stripWidthTag`.
* `legalizeBinop_mnem_congr`: the same for a whole `legalizeBinop` block.
* `BinopWideBinding.maintains`: the width-64 block re-establishes `StoreRel`
  against the binding's virtual transformer.
* `physBodyElem_binopCollapse64`: the `physBodyElem` expansion of a width-64
  binop head in the two-address-collapse shape.
* `regArithHead64_cover`: that expansion is the binding's block.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBinopWide

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWriteSide
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBody
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulFlatMap
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulNary
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulCover

/-! ## 1. Width-tag computations -/

/-- `stripWidthTag` removes the `:64` tag of the width-64 move mnemonic. -/
theorem stripWidthTag_MOV64 : stripWidthTag "MOV:64" = "MOV" := by decide +kernel

/-- The untagged move mnemonic is its own `stripWidthTag`. -/
theorem stripWidthTag_MOV : stripWidthTag "MOV" = "MOV" := by decide +kernel

/-- A binary register-arithmetic mnemonic carries no width tag. -/
theorem stripWidthTag_binOpName (bop : JasminBinOp) :
    stripWidthTag (binOpName bop) = binOpName bop := by
  cases bop <;> decide +kernel

/-- The width tag round-trips on a binary register-arithmetic mnemonic. -/
theorem stripWidthTag_withWidthTag64_binOpName (bop : JasminBinOp) :
    stripWidthTag (withWidthTag 64 (binOpName bop)) = binOpName bop := by
  rw [show withWidthTag 64 (binOpName bop) = binOpName bop ++ ":64" from by
    simp [withWidthTag]]
  cases bop <;> decide +kernel

/-- The width-64 binop mnemonic carries the `:64` tag. -/
theorem hasSuffix_withWidthTag64_binOpName (bop : JasminBinOp) :
    hasSuffix (withWidthTag 64 (binOpName bop)) ":64" = true := by
  rw [show withWidthTag 64 (binOpName bop) = binOpName bop ++ ":64" from by
    simp [withWidthTag]]
  cases bop <;> decide +kernel

/-- A non-shift binary mnemonic is in the two-address binop alphabet. -/
theorem isBinop_withWidthTag64_binOpName (bop : JasminBinOp) (hns : NonShift bop) :
    ["ADD", "SUB", "MUL", "AND", "OR", "XOR", "SHL", "SHR"].contains
      (stripWidthTag (withWidthTag 64 (binOpName bop))) = true := by
  rw [stripWidthTag_withWidthTag64_binOpName]
  obtain ⟨-, -, h3⟩ := hns
  cases bop <;> first | rfl | exact absurd rfl h3

/-- A non-shift binary mnemonic is not a shift mnemonic. -/
theorem not_isShift_withWidthTag64_binOpName (bop : JasminBinOp) (hns : NonShift bop) :
    ¬ (stripWidthTag (withWidthTag 64 (binOpName bop)) == "SHL"
      || stripWidthTag (withWidthTag 64 (binOpName bop)) == "SHR") = true := by
  rw [stripWidthTag_withWidthTag64_binOpName]
  obtain ⟨h1, h2, -⟩ := hns
  cases bop <;> first | decide | exact absurd rfl h1 | exact absurd rfl h2

/-- A register operand needs no wide-immediate materialization. -/
theorem materializeWideImm_reg (n : String) (mov : String) :
    materializeWideImm (.reg n) mov = ([], .reg n) := rfl

/-! ## 2. The mnemonic congruence of `lsemStep` -/

/-- A single-source register-arm `Lopn` steps the same under two mnemonics with
    the same `stripWidthTag`. -/
theorem lsemStep_congr1 {w : Nat} {o1 o2 : String} (h : stripWidthTag o1 = stripWidthTag o2)
    {nD nA : String} (s : Lstate w) :
    lsemStep (LinstrR.Lopn [.reg nD] o1 [.reg nA]) s
      = lsemStep (LinstrR.Lopn [.reg nD] o2 [.reg nA]) s := by
  simp only [lsemStep, h]

/-- A two-source register-arm `Lopn` steps the same under two mnemonics with the
    same `stripWidthTag`. -/
theorem lsemStep_congr2 {w : Nat} {o1 o2 : String} (h : stripWidthTag o1 = stripWidthTag o2)
    {nD nA nB : String} (s : Lstate w) :
    lsemStep (LinstrR.Lopn [.reg nD] o1 [.reg nA, .reg nB]) s
      = lsemStep (LinstrR.Lopn [.reg nD] o2 [.reg nA, .reg nB]) s := by
  simp only [lsemStep, h]

/-- **Mnemonic congruence of a `legalizeBinop` block.** Two blocks over the same
    register operands whose op mnemonics and whose move mnemonics have equal
    `stripWidthTag` run to the same state. -/
theorem legalizeBinop_mnem_congr {w : Nat} (nD nS : String) (opn1 opn2 mov1 mov2 : String)
    (hop : stripWidthTag opn1 = stripWidthTag opn2)
    (hmov : stripWidthTag mov1 = stripWidthTag mov2) (s : Lstate w) :
    lsemStraight (legalizeBinop (.reg nD) (.reg nS) opn1 mov1) s
      = lsemStraight (legalizeBinop (.reg nD) (.reg nS) opn2 mov2) s := by
  unfold legalizeBinop
  cases h1 : (LOperand.reg nD).isSpill <;> cases h2 : (LOperand.reg nS).isSpill <;>
    simp only [lsemStraight_cons, lsemStraight_nil, lsemStep_congr1 hmov,
      lsemStep_congr2 hop]

/-! ## 3. The width-64 binding kind -/

/-- A width-64 binary `regArith` binding: the logical destination and second
    source, the operator, the value it writes, the destination injectivity of the
    register allocation, and the value equation on the untagged mnemonic. -/
structure BinopWideBinding (w : Nat) (body : Lcmd) (tbl : Array Nat) where
  /-- The logical destination name. -/
  nDst : String
  /-- The logical second-source name. -/
  nSrc : String
  /-- The binary operator. -/
  bop : JasminBinOp
  /-- The value written at the destination. -/
  vval : Lstate w → BitVec w
  /-- Distinct live names get distinct slots at the destination's fibre. -/
  hinj : ∀ m, physRename body tbl m = physRename body tbl nDst → m = nDst
  /-- The operator's value at the two operand reads. -/
  hop : ∀ s : Lstate w, applyOpn (binOpName bop) [s.lvm nDst, s.lvm nSrc] = some (vval s)

/-- The physical block of a width-64 binop binding: `legalizeBinop` over the
    renamed operands at the `:64`-tagged mnemonic and the `MOV:64` move. -/
def BinopWideBinding.block {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : BinopWideBinding w body tbl) : List LinstrR :=
  legalizeBinop (.reg (physRename body tbl b.nDst))
    (.reg (physRename body tbl b.nSrc)) (withWidthTag 64 (binOpName b.bop)) "MOV:64"

/-- The virtual transformer of a width-64 binop binding: write the value at the
    destination. -/
def BinopWideBinding.vstep {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : BinopWideBinding w body tbl) : Lstate w → Lstate w :=
  fun s => s.setReg b.nDst (b.vval s)

/-- **The width-64 block re-establishes the store relation.** The `:64`-tagged
    block runs as the untagged one does (`legalizeBinop_mnem_congr`), so the
    default-width step theorem applies. -/
theorem BinopWideBinding.maintains {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : BinopWideBinding w body tbl) :
    BlockMaintains body tbl b.block b.vstep := by
  intro s s' hrel
  obtain ⟨s'', hrun, hst⟩ :=
    legalizeBinop_storeRel_step body tbl s s' b.nDst b.nSrc (binOpName b.bop) hrel b.hinj
      (stripWidthTag_binOpName b.bop) (b.vval s) (b.hop s)
  refine ⟨s'', ?_, hst⟩
  rw [BinopWideBinding.block,
    legalizeBinop_mnem_congr (physRename body tbl b.nDst) (physRename body tbl b.nSrc)
      (withWidthTag 64 (binOpName b.bop)) (binOpName b.bop) "MOV:64" "MOV"
      (by rw [stripWidthTag_withWidthTag64_binOpName, stripWidthTag_binOpName])
      (by rw [stripWidthTag_MOV64, stripWidthTag_MOV]) s']
  exact hrun

/-! ## 4. The expansion of a width-64 binop head -/

/-- **Per-instruction expansion, width-64 two-address collapse.** A width-64
    non-shift binop head whose renamed destination coincides with its renamed
    first source expands to the `legalizeBinop` block at the move `MOV:64`. -/
theorem physBodyElem_binopCollapse64 (body : Lcmd) (tbl : Array Nat) (ii : Nat)
    (nD nS0 nS1 : String) (ds ss : List LOperand) (bop : JasminBinOp) (hns : NonShift bop)
    (hcol : physRename body tbl nS0 = physRename body tbl nD) :
    (physBodyElem body tbl ⟨ii, .Lopn (.reg nD :: ds) (withWidthTag 64 (binOpName bop))
        (.reg nS0 :: .reg nS1 :: ss)⟩).map (·.li_i)
      = legalizeBinop (.reg (physRename body tbl nD)) (.reg (physRename body tbl nS1))
          (withWidthTag 64 (binOpName bop)) "MOV:64" := by
  have hcol' : remapOperand body tbl (.reg nD) = remapOperand body tbl (.reg nS0) := by
    rw [remapOperand_reg, remapOperand_reg, hcol]
  simp only [physBodyElem, isBinop_withWidthTag64_binOpName bop hns,
    not_isShift_withWidthTag64_binOpName bop hns, hasSuffix_withWidthTag64_binOpName bop,
    Bool.false_eq_true, if_false, lowerTwoAddr]
  rw [if_pos hcol']
  simp only [if_true, remapOperand_reg, materializeWideImm_reg, List.nil_append,
    List.map_map, Function.comp_def, List.map_id_fun', id_eq]

/-- **The width-64 head is covered by its binding.** The `physBodyElem`
    expansion of the head `comToBody` emits for a width-64 non-shift binop
    binding is the block of a `BinopWideBinding` naming the same destination,
    operator and second source, under the two-address collapse. -/
theorem regArithHead64_cover {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (nArgs curDepth : Nat) (bop : JasminBinOp) (hns : NonShift bop)
    {Γ : Ctxt jasminDialect} (a0 a1 : Ctxt.Var Γ (JasminTy.reg 64))
    (b : BinopWideBinding w body tbl)
    (hdst : b.nDst = regName curDepth) (hbop : b.bop = bop)
    (hsrc : b.nSrc = resolveVarName curDepth nArgs a1)
    (hcol : physRename body tbl (resolveVarName curDepth nArgs a0)
        = physRename body tbl (regName curDepth)) :
    (physBodyElem body tbl (regArithHead nArgs curDepth bop 64 a0 a1)).map (·.li_i)
      = b.block := by
  rw [regArithHead,
    physBodyElem_binopCollapse64 body tbl 0 (regName curDepth)
      (resolveVarName curDepth nArgs a0) (resolveVarName curDepth nArgs a1) [] [] bop hns hcol,
    BinopWideBinding.block, hdst, hbop, hsrc]

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBinopWide
