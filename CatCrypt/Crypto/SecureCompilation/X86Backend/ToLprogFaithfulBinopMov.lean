/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulTwoAddr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBinopWide

/-!
# Mov-prefixed two-address binop bindings

`ToLprogFaithfulBody.BinopBinding` and
`ToLprogFaithfulBinopWide.BinopWideBinding` are the binding kinds of a binop head
whose renamed destination coincides with its renamed first source, so that
`lowerTwoAddr` collapses to the bare `legalizeBinop`. Their covers carry that
coincidence as the side condition `hcol`.

This module gives the binding kinds of the other branch of
`ToLprogFaithfulRA.lowerTwoAddr_dichotomy`: a binop head whose renamed
destination differs from its renamed first source, whose block is the literal
`lowerTwoAddr` output `legalizeMov ρ nDst, ρ nS0 ++ legalizeBinop ρ nDst, ρ nSrc`
and whose cover carries no `hcol`. The store-relation maintenance of that block
is `ToLprogFaithfulTwoAddr.lowerTwoAddr_blockMaintains`.

## Main definitions

* `BinopMovBinding`: a default-width (`w ≠ 64`) mov-prefixed binop binding.
* `BinopMovWideBinding`: the width-64 mov-prefixed binop binding, whose move
  mnemonic is `MOV:64` and whose op mnemonic carries the `:64` tag.

## Main results

* `physBodyElem_binopTwoAddr`, `physBodyElem_binopTwoAddr64`: the `physBodyElem`
  expansion of a binop head is the literal `lowerTwoAddr` output, with no
  condition on the register allocation.
* `lowerTwoAddr_regReg_ne`: `lowerTwoAddr` over register operands at any move
  mnemonic is `legalizeMov ++ legalizeBinop` when destination and first source
  differ.
* `legalizeMov_mnem_congr`, `lsemStraight_append_congr`: two blocks whose
  mnemonics agree under `stripWidthTag` run to the same state.
* `BinopMovBinding.maintains`, `BinopMovWideBinding.maintains`: each block
  re-establishes `StoreRel` against `s ↦ s.setReg nDst (vval s)`.
* `regArithHeadMov_cover`, `regArithHeadMov64_cover`: the `physBodyElem`
  expansion of the head `comToBody` emits for a binop binding is the binding's
  block.
* `physRename_of_not_mem`: every name outside the body's slot universe renames
  to one and the same physical register.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBinopMov

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulTwoAddr
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBinopWide

/-! ## 1. The `lowerTwoAddr` output over register operands -/

/-- `lowerTwoAddr` over register operands whose destination and first source
    differ is `legalizeMov dst s0 mov ++ legalizeBinop dst s1 opn mov`, at any
    move mnemonic: a register second source needs no wide-immediate
    materialization. -/
theorem lowerTwoAddr_regReg_ne (dst s0 s1 opn mov : String) (hne : dst ≠ s0) :
    lowerTwoAddr (.reg dst) (.reg s0) (.reg s1) opn mov
      = legalizeMov (.reg dst) (.reg s0) mov
        ++ legalizeBinop (.reg dst) (.reg s1) opn mov := by
  have hneOp : (LOperand.reg dst) ≠ (LOperand.reg s0) := fun h => hne (by injection h)
  unfold lowerTwoAddr
  simp only [materializeWideImm_reg, List.nil_append, List.append_nil, if_neg hneOp]

/-! ## 2. The `physBodyElem` expansion of a binop head

`physBodyElem` sends a non-shift binop head to the `lowerTwoAddr` of its renamed
operands, whichever branch of the two-address dichotomy that lowering takes. The
expansion therefore needs no condition on the register allocation. -/

/-- The `physBodyElem` expansion of a default-width non-shift binop head is the
    `lowerTwoAddr` of its renamed operands at the move `MOV`. -/
theorem physBodyElem_binopTwoAddr (body : Lcmd) (tbl : Array Nat) (ii : Nat)
    (d s0 s1 : LOperand) (ds ss : List LOperand) (opn : String)
    (hbin : isTwoAddrBinop opn = true)
    (hsh : ¬ (stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR") = true)
    (h64 : ¬ hasSuffix opn ":64" = true) :
    (physBodyElem body tbl ⟨ii, .Lopn (d :: ds) opn (s0 :: s1 :: ss)⟩).map (·.li_i)
      = lowerTwoAddr (remapOperand body tbl d) (remapOperand body tbl s0)
          (remapOperand body tbl s1) opn "MOV" := by
  simp only [physBodyElem, hbin, hsh, h64, Bool.false_eq_true, if_false, if_true,
    List.map_map, Function.comp_def, List.map_id_fun', id_eq]

/-- The `physBodyElem` expansion of a width-64 non-shift binop head is the
    `lowerTwoAddr` of its renamed operands at the move `MOV:64`. -/
theorem physBodyElem_binopTwoAddr64 (body : Lcmd) (tbl : Array Nat) (ii : Nat)
    (d s0 s1 : LOperand) (ds ss : List LOperand) (opn : String)
    (hbin : isTwoAddrBinop opn = true)
    (hsh : ¬ (stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR") = true)
    (h64 : hasSuffix opn ":64" = true) :
    (physBodyElem body tbl ⟨ii, .Lopn (d :: ds) opn (s0 :: s1 :: ss)⟩).map (·.li_i)
      = lowerTwoAddr (remapOperand body tbl d) (remapOperand body tbl s0)
          (remapOperand body tbl s1) opn "MOV:64" := by
  simp only [physBodyElem, hbin, hsh, h64, Bool.false_eq_true, if_false, if_true,
    List.map_map, Function.comp_def, List.map_id_fun', id_eq]

/-! ## 3. Mnemonic congruence of a move and of a concatenation

`lsemStep` reads an `Lopn` mnemonic on the register arm only through
`stripWidthTag`, so the `MOV:64` move of the width-64 lowering runs as the `MOV`
move of the default-width lowering does. -/

/-- A `legalizeMov` block over register operands runs the same under two move
    mnemonics with equal `stripWidthTag`. -/
theorem legalizeMov_mnem_congr {w : Nat} (nD nS : String) (mov1 mov2 : String)
    (h : stripWidthTag mov1 = stripWidthTag mov2) (s : Lstate w) :
    lsemStraight (legalizeMov (.reg nD) (.reg nS) mov1) s
      = lsemStraight (legalizeMov (.reg nD) (.reg nS) mov2) s := by
  unfold legalizeMov
  cases h1 : ((LOperand.reg nD).isSpill && (LOperand.reg nS).isSpill) <;>
    simp only [if_true, if_false, Bool.false_eq_true, lsemStraight_cons, lsemStraight_nil,
      lsemStep_congr1 h]

/-- Two concatenations whose corresponding halves run alike run alike. -/
theorem lsemStraight_append_congr {w : Nat} (A A' B B' : List LinstrR)
    (hA : ∀ t : Lstate w, lsemStraight A t = lsemStraight A' t)
    (hB : ∀ t : Lstate w, lsemStraight B t = lsemStraight B' t) (s : Lstate w) :
    lsemStraight (A ++ B) s = lsemStraight (A' ++ B') s := by
  rw [lsemStraight_append, lsemStraight_append, hA]
  cases lsemStraight A' s with
  | none => rfl
  | some t => simpa using hB t

/-! ## 4. The default-width mov-prefixed binding kind -/

/-- A default-width binop binding whose renamed destination differs from its
    renamed first source: the block is the mov-prefixed `lowerTwoAddr` output.
    The two-address collapse `hcol` is absent; in its place the binding carries
    the branch condition `hne` and the non-spill condition `hnsp` of the leading
    move. -/
structure BinopMovBinding (w : Nat) (body : Lcmd) (tbl : Array Nat) where
  /-- The logical destination name. -/
  nDst : String
  /-- The logical first-source name. -/
  nS0 : String
  /-- The logical second-source name. -/
  nSrc : String
  /-- The untagged op mnemonic. -/
  opn : String
  /-- The value written at the destination. -/
  vval : Lstate w → BitVec w
  /-- The logical names live before the binding. -/
  Lin : List String
  /-- The logical names live after the binding. -/
  Lout : List String
  /-- The binding reads its first source. -/
  hs0In : nS0 ∈ Lin
  /-- No name live between the leading move and the binop, other than the
      destination itself, shares the destination's physical register. -/
  hinj : ∀ m ∈ nDst :: nSrc :: Lout,
    physRename body tbl m = physRename body tbl nDst → m = nDst
  /-- Every such name other than the destination was already live before the
      binding. -/
  hcarry : ∀ m ∈ nDst :: nSrc :: Lout, m ≠ nDst → m ∈ Lin
  /-- The register allocation did not place the destination on its first
      source's register. -/
  hne : physRename body tbl nDst ≠ physRename body tbl nS0
  /-- The second source is not the destination. -/
  hsrcNe : nSrc ≠ nDst
  /-- The leading move has at most one spill operand. -/
  hnsp : ¬ ((LOperand.reg (physRename body tbl nDst)).isSpill
      && (LOperand.reg (physRename body tbl nS0)).isSpill) = true
  /-- The op mnemonic carries no width tag. -/
  hstrip : stripWidthTag opn = opn
  /-- The operator's value at the two operand reads. -/
  hop : ∀ s : Lstate w, applyOpn opn [s.lvm nS0, s.lvm nSrc] = some (vval s)

/-- The physical block of a mov-prefixed binop binding: the literal
    `lowerTwoAddr` output over the renamed operands at the move `MOV`. -/
def BinopMovBinding.block {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : BinopMovBinding w body tbl) : List LinstrR :=
  lowerTwoAddr (.reg (physRename body tbl b.nDst)) (.reg (physRename body tbl b.nS0))
    (.reg (physRename body tbl b.nSrc)) b.opn "MOV"

/-- The virtual transformer of a mov-prefixed binop binding: write the value at
    the destination. -/
def BinopMovBinding.vstep {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : BinopMovBinding w body tbl) : Lstate w → Lstate w :=
  fun s => s.setReg b.nDst (b.vval s)

/-- A mov-prefixed binop binding's block re-establishes `StoreRel` against its
    virtual transformer. -/
theorem BinopMovBinding.maintains {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : BinopMovBinding w body tbl) :
    BlockMaintains body tbl b.Lin b.Lout b.block b.vstep :=
  lowerTwoAddr_blockMaintains body tbl b.Lin b.Lout b.nDst b.nS0 b.nSrc b.opn b.vval
    b.hs0In b.hinj b.hcarry b.hne b.hsrcNe b.hnsp b.hstrip b.hop

/-! ## 5. The width-64 mov-prefixed binding kind -/

/-- A width-64 binop binding whose renamed destination differs from its renamed
    first source: the block is the mov-prefixed `lowerTwoAddr` output at the
    `:64`-tagged op mnemonic and the move `MOV:64`. -/
structure BinopMovWideBinding (w : Nat) (body : Lcmd) (tbl : Array Nat) where
  /-- The logical destination name. -/
  nDst : String
  /-- The logical first-source name. -/
  nS0 : String
  /-- The logical second-source name. -/
  nSrc : String
  /-- The binary operator. -/
  bop : JasminBinOp
  /-- The value written at the destination. -/
  vval : Lstate w → BitVec w
  /-- The logical names live before the binding. -/
  Lin : List String
  /-- The logical names live after the binding. -/
  Lout : List String
  /-- The binding reads its first source. -/
  hs0In : nS0 ∈ Lin
  /-- No name live between the leading move and the binop, other than the
      destination itself, shares the destination's physical register. -/
  hinj : ∀ m ∈ nDst :: nSrc :: Lout,
    physRename body tbl m = physRename body tbl nDst → m = nDst
  /-- Every such name other than the destination was already live before the
      binding. -/
  hcarry : ∀ m ∈ nDst :: nSrc :: Lout, m ≠ nDst → m ∈ Lin
  /-- The register allocation did not place the destination on its first
      source's register. -/
  hne : physRename body tbl nDst ≠ physRename body tbl nS0
  /-- The second source is not the destination. -/
  hsrcNe : nSrc ≠ nDst
  /-- The leading move has at most one spill operand. -/
  hnsp : ¬ ((LOperand.reg (physRename body tbl nDst)).isSpill
      && (LOperand.reg (physRename body tbl nS0)).isSpill) = true
  /-- The operator's value at the two operand reads. -/
  hop : ∀ s : Lstate w, applyOpn (binOpName bop) [s.lvm nS0, s.lvm nSrc] = some (vval s)

/-- The physical block of a width-64 mov-prefixed binop binding. -/
def BinopMovWideBinding.block {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : BinopMovWideBinding w body tbl) : List LinstrR :=
  lowerTwoAddr (.reg (physRename body tbl b.nDst)) (.reg (physRename body tbl b.nS0))
    (.reg (physRename body tbl b.nSrc)) (withWidthTag 64 (binOpName b.bop)) "MOV:64"

/-- The virtual transformer of a width-64 mov-prefixed binop binding. -/
def BinopMovWideBinding.vstep {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : BinopMovWideBinding w body tbl) : Lstate w → Lstate w :=
  fun s => s.setReg b.nDst (b.vval s)

/-- A width-64 mov-prefixed binop binding's block re-establishes `StoreRel`
    against its virtual transformer: the `:64`-tagged block runs as the untagged
    one does, so the default-width composition step applies. -/
theorem BinopMovWideBinding.maintains {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : BinopMovWideBinding w body tbl) :
    BlockMaintains body tbl b.Lin b.Lout b.block b.vstep := by
  intro s s' hrel
  obtain ⟨s'', hrun, hst⟩ :=
    movThenBinop_storeRel_step body tbl b.Lin b.Lout s s' b.nDst b.nS0 b.nSrc
      (binOpName b.bop) hrel b.hs0In b.hinj b.hcarry b.hsrcNe b.hnsp
      (stripWidthTag_binOpName b.bop) (b.vval s) (b.hop s)
  refine ⟨s'', ?_, hst⟩
  rw [BinopMovWideBinding.block,
    lowerTwoAddr_regReg_ne _ _ _ _ _ b.hne,
    lsemStraight_append_congr
      (legalizeMov (.reg (physRename body tbl b.nDst))
        (.reg (physRename body tbl b.nS0)) "MOV:64")
      (legalizeMov (.reg (physRename body tbl b.nDst))
        (.reg (physRename body tbl b.nS0)) "MOV")
      (legalizeBinop (.reg (physRename body tbl b.nDst))
        (.reg (physRename body tbl b.nSrc)) (withWidthTag 64 (binOpName b.bop)) "MOV:64")
      (legalizeBinop (.reg (physRename body tbl b.nDst))
        (.reg (physRename body tbl b.nSrc)) (binOpName b.bop) "MOV")
      (fun t => legalizeMov_mnem_congr _ _ "MOV:64" "MOV"
        (by rw [stripWidthTag_MOV64, stripWidthTag_MOV]) t)
      (fun t => legalizeBinop_mnem_congr _ _ _ _ "MOV:64" "MOV"
        (by rw [stripWidthTag_withWidthTag64_binOpName, stripWidthTag_binOpName])
        (by rw [stripWidthTag_MOV64, stripWidthTag_MOV]) t)]
  exact hrun

/-! ## 6. The covers of the two head shapes

The head `comToBody` emits for a binop binding is `regArithHead`; its
`physBodyElem` expansion is the `lowerTwoAddr` of the renamed operands, which is
the mov-prefixed binding's block. Unlike the collapse covers
(`regArithHead_realizes`, `regArithHead64_cover`) these carry no `hcol`. -/

/-- The default-width binop head is covered by a mov-prefixed binding naming the
    same destination, mnemonic and sources. -/
theorem regArithHeadMov_cover {w' : Nat} (body : Lcmd) (tbl : Array Nat)
    (nArgs curDepth : Nat) (bop : JasminBinOp) (w : Nat) (hw : w ≠ 64)
    (hns : NonShift bop) {Γ : Ctxt jasminDialect} (a0 a1 : Ctxt.Var Γ (.reg w))
    (b : BinopMovBinding w' body tbl)
    (hdst : b.nDst = regName curDepth)
    (hopn : b.opn = withWidthTag w (binOpName bop))
    (hS0 : b.nS0 = resolveVarName curDepth nArgs a0)
    (hsrc : b.nSrc = resolveVarName curDepth nArgs a1) :
    (physBodyElem body tbl (regArithHead nArgs curDepth bop w a0 a1)).map (·.li_i)
      = b.block := by
  have hsf : tagSepFree (binOpName bop) = true := by cases bop <;> decide +kernel
  have htag : stripWidthTag (withWidthTag w (binOpName bop))
      = stripWidthTag (binOpName bop) := by
    rw [stripWidthTag_withWidthTag w hsf]
    cases bop <;> decide +kernel
  rw [regArithHead,
    physBodyElem_binopTwoAddr body tbl 0 (.reg (regName curDepth))
      (.reg (resolveVarName curDepth nArgs a0)) (.reg (resolveVarName curDepth nArgs a1))
      [] [] (withWidthTag w (binOpName bop))
      (by unfold isTwoAddrBinop; rw [htag]; exact binOpName_isBinop_of_nonshift bop hns)
      (by rw [htag]; exact binOpName_not_isShift_of_nonshift bop hns)
      (withWidthTag_binOpName_not_hasSuffix64 w bop hw),
    BinopMovBinding.block, hdst, hopn, hS0, hsrc, remapOperand_reg, remapOperand_reg,
    remapOperand_reg]

/-- The width-64 binop head is covered by a width-64 mov-prefixed binding naming
    the same destination, operator and sources. -/
theorem regArithHeadMov64_cover {w' : Nat} (body : Lcmd) (tbl : Array Nat)
    (nArgs curDepth : Nat) (bop : JasminBinOp) (hns : NonShift bop)
    {Γ : Ctxt jasminDialect} (a0 a1 : Ctxt.Var Γ (.reg 64))
    (b : BinopMovWideBinding w' body tbl)
    (hdst : b.nDst = regName curDepth) (hbop : b.bop = bop)
    (hS0 : b.nS0 = resolveVarName curDepth nArgs a0)
    (hsrc : b.nSrc = resolveVarName curDepth nArgs a1) :
    (physBodyElem body tbl (regArithHead nArgs curDepth bop 64 a0 a1)).map (·.li_i)
      = b.block := by
  rw [regArithHead,
    physBodyElem_binopTwoAddr64 body tbl 0 (.reg (regName curDepth))
      (.reg (resolveVarName curDepth nArgs a0)) (.reg (resolveVarName curDepth nArgs a1))
      [] [] (withWidthTag 64 (binOpName bop))
      (isBinop_withWidthTag64_binOpName bop hns)
      (not_isShift_withWidthTag64_binOpName bop hns)
      (hasSuffix_withWidthTag64_binOpName bop),
    BinopMovWideBinding.block, hdst, hbop, hS0, hsrc, remapOperand_reg, remapOperand_reg,
    remapOperand_reg]

/-! ## 7. The fibre of the names outside the slot universe

`nameSlot` sends every name absent from `bodyNames` to the single index
`(bodyNames body).length`, so all such names share one physical location. The
destination injectivity `hinj` a binding carries is quantified over all strings,
so it holds at a destination `nDst` only if that shared location differs from
`nDst`'s. -/

/-- A name outside the body's slot universe renames to the physical location of
    the index `(bodyNames body).length`. -/
theorem physRename_of_not_mem (body : Lcmd) (tbl : Array Nat) {n : String}
    (hn : n ∉ bodyNames body) :
    physRename body tbl n = physRegName (physMapTabled tbl (bodyNames body).length) := by
  unfold physRename nameSlot
  rw [List.idxOf_eq_length_iff.mpr hn]

/-- Any two names outside the body's slot universe rename to the same physical
    location. -/
theorem physRename_eq_of_not_mem (body : Lcmd) (tbl : Array Nat) {m n : String}
    (hm : m ∉ bodyNames body) (hn : n ∉ bodyNames body) :
    physRename body tbl m = physRename body tbl n := by
  rw [physRename_of_not_mem body tbl hm, physRename_of_not_mem body tbl hn]

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBinopMov
