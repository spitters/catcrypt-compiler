/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.String.TakeDrop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1DecodedNode

@[expose] public section

set_option autoImplicit false

/-!
# The physical-ABI export of a single loop node, its `MULX` fusion and its bytes

`MpnMul1DecodedNode` pins the physical body of `mpn_mul_1` to a literal by compiled
evaluation and decodes the literal by kernel evaluation. This module states the three
steps between the typed loop node and the decoded bytes as lemmas over every program
of the same shape.

## The export

`ComL.toLfundefPhysAbi` allocates the virtual body `abiBody1`: the argument-liveness
pin, then the virtual body with the loop accumulator aliased onto the out-array name
and the store thread canonicalised. Its physical body is the red-zone prologue, the
saves of the further argument registers, the argument materialization, the
register-allocated body with the callee-saved restores before the return
(`toLfundefPhysAbi_body`). Without argument loads, output stores and calls, the
register-allocated body is the flat map of the per-instruction expansion `physExpand`
(`physBodyWithStores_eq_physExpand`): the two-address lowering of a binop, the
reload of a memory base from its red-zone slot into `R14` before a `LOADIDX` or
`STOREIDX`, the lowering of a native shift, and the operand renaming of every other
instruction.

The statement covers one runtime-count loop node with nothing after it
(`singleLoop`). A chain of loop nodes is outside it: the exporter aliases every
accumulator of the chain onto one name, and the chain's later nodes are not
reloaded from their own slots.

## The fusion

`fuseMulHiAux` recurses well-foundedly on the body; its equation lemmas give the
fusion instruction by instruction. A body with one low `MUL` and one `MULXHI` on the
same multiplicand, with no other multiply site, fuses to the save of `RDX`, the pin of
the other factor, the two-output `MULX` and the restore of `RDX`
(`fuseMulHiBody_oneSite`).

## The bytes

`DShape` generalises `LprogBytesDecode.Shape` to a run of decoded instructions per
body instruction: the bytes of the instruction split into pieces that each decode,
in front of every continuation, to one straight-line instruction.
`decodeLprog_encodeLfundefBytes_shapes` is the function round trip over such shapes,
and `decodeLprog_node` its instance at a guarded loop node, whose decoded program is
`DecodedLsemLoop.nodeLayout`. The branch condition `branchOK` of the item list, which
depends on the label offsets the encoder's relaxation computes, is a hypothesis.

## Main results

* `physBodyWithStores_eq_physExpand`: the register-allocated body without loads,
  stores and calls is `body.flatMap (physExpand …)`.
* `arrChainAlias_spec`, `bodyVecSlots_noVec`, `physTableClassed_eq` and the prefix tests
  on character lists (`isSpill_eq`, `bodyHasMulHi_eq`, …): restatements of exporter steps
  that do not reduce in the kernel.
* `bodyTrace_of_bodyNames`, `physRmap_of_bodyNames`, `physNameForBody_of_bodyNames`: the
  trace and the operand renaming of a call-free body over a name universe computed once.
* `toLfundefPhysAbi_singleLoop`: the physical body of the single-loop export is the
  prologue, the argument saves and materialization, the flat map of `physExpand`
  over the node renamed by `κ` after the accumulator alias, the restores and `Lret`.
* `fuseMulHiBody_oneSite`: the looped-body `MULX` fusion of a body with one multiply
  site.
* `decodeLprog_encodeLfundefBytes_shapes`: the function bytes of a body with
  list-valued shapes decode to the program of its item list.
* `expectedFrom_node`, `decodeLprog_node`: the item list, and the function bytes, of
  a guarded loop node decode to `nodeLayout`.
* `mul1RtProgOpt_eq`: the front-compiled `mpn_mul_1` is `singleLoop mul1Update`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The per-position expansion -/

/-- The operand renaming `physBodyWithStores` applies to `body` under the reserved
    vector indices `rv`: the post-RA lookup through the allocation table, through
    the caller-save barrier when the body issues a call. -/
def physRmap (body : Lcmd) (rv : List Nat) : LOperand → LOperand :=
  let tbl := straightCallComposeTable body (physTableOut body [] rv)
  if bodyHasCall body then remapOperandCalleeSave body tbl else remapOperand body tbl

/-- The register-allocated expansion of one virtual instruction: the two-address
    lowering of a binop, the base reload and legalization of a memory access, the
    lowering of a native shift, and the operand renaming of every other `Lopn`,
    with the 64-bit move `spillImmMovMnem` selects for a small immediate stored to a
    spill slot of a body with 8-byte slots (`u64`), a copy between two spill slots
    through `R15` (`legalizeOneSrc`), and a `CMOV:64` or a comparison `SET<cc>` with
    spilled operands computed on the scratch registers (`legalizeSpillDst`). -/
def physExpand (shiftImm : ShiftImmOracle) (u64 : Bool) (rmap : LOperand → LOperand)
    (memrefBaseReload : String → Option String) (i : Linstr) : Lcmd :=
  let isBinop (opn : String) : Bool := isTwoAddrBinop opn
  let isShift (opn : String) : Bool :=
    stripWidthTag opn == "SHL" || stripWidthTag opn == "SHR"
  let movFor (opn : String) : String :=
    if hasSuffix opn ":64" then "MOV:64" else "MOV"
  let shiftImmVal (s1 : LOperand) : Option Nat :=
    match s1 with
    | .imm v => some v
    | .reg n => shiftImm n
    | _ => none
  match i.li_i with
  | .Lopn (d :: _) opn (s0 :: s1 :: _) =>
      if isBinop opn then
        match (if isShift opn then shiftImmVal s1 else none) with
        | some v =>
            (lowerTwoAddrShiftImm (rmap d) (rmap s0) v opn (movFor opn)).map
              (fun r => ⟨i.li_ii, r⟩)
        | none =>
            (lowerTwoAddr (rmap d) (rmap s0) (rmap s1) opn (movFor opn)).map
              (fun r => ⟨i.li_ii, r⟩)
      else
        match i.li_i with
        | .Lopn [d'] opn' [addr, val] =>
            if isMemStore opn' then
              let (baseReload, addr') := reloadMemrefBase memrefBaseReload (rmap addr)
              (baseReload.map (fun r => ⟨i.li_ii, r⟩)) ++
              (legalizeMemStoreK (idxConst shiftImm addr) (rmap d') addr' (rmap val) opn'
                 (movFor opn')).map (fun r => ⟨i.li_ii, r⟩)
            else
              (legalizeSpillDst [rmap d'] opn' [rmap addr, rmap val]).map
                (fun r => ⟨i.li_ii, r⟩)
        | .Lopn dsts opn srcs =>
            (legalizeSpillDst (dsts.map rmap) opn (srcs.map rmap)).map
              (fun r => ⟨i.li_ii, r⟩)
        | other => [⟨i.li_ii, other⟩]
  | .Lopn [d] opn [s] =>
      if isNativeShiftRotate opn then
        (lowerNativeShiftRotate (rmap d) (rmap s) opn (movFor opn)).map
          (fun r => ⟨i.li_ii, r⟩)
      else if isMemLoad opn then
        let (baseReload, s') := reloadMemrefBase memrefBaseReload (rmap s)
        (baseReload.map (fun r => ⟨i.li_ii, r⟩)) ++
        (legalizeMemLoad (rmap d) s' opn (movFor opn)).map
          (fun r => ⟨i.li_ii, r⟩)
      else
        (legalizeOneSrc u64 opn (rmap d) (rmap s)).map (fun r => ⟨i.li_ii, r⟩)
  | .Lopn dsts opn srcs =>
      [⟨i.li_ii, .Lopn (dsts.map rmap) opn (srcs.map rmap)⟩]
  | other => [⟨i.li_ii, other⟩]

/-- Without argument loads, output stores and calls, a position of
    `physBodyWithStores` contributes its register-allocated expansion, whatever its
    index. -/
theorem physPositionEmit_eq_physExpand (shiftImm : ShiftImmOracle) (body : Lcmd)
    (loadBase storeBase : String) (abiW : Nat)
    (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (rv : List Nat) (i : Linstr) (k : Nat)
    (hi : ∀ a b, i.li_i ≠ .Lcall a b) :
    physPositionEmit shiftImm body (fun _ => none) loadBase [] storeBase abiW
        memrefBaseReload callArgBaseReload rv (i, k)
      = physExpand shiftImm (LprogAsmPrinter.bodyIsU64 body) (physRmap body rv)
          memrefBaseReload i := by
  unfold physPositionEmit
  dsimp only
  rw [List.filterMap_eq_nil_iff.mpr (fun s _ => by split <;> (try split) <;> rfl)]
  simp only [List.flatMap_nil, List.nil_append, List.length_nil, Nat.sub_zero]
  have hst : ∀ (b t : Nat), ¬ (b ≥ t ∧ b < t) := fun b t h => by omega
  simp only [hst, if_false]
  obtain ⟨ii, w⟩ := i
  cases w with
  | Lopn ds o ss => cases ds <;> simp only [List.append_nil] <;> rfl
  | _ => rfl

/-- **The register-allocated body is the flat map of the expansion.** Without
    argument loads, output stores and calls, `physBodyWithStores` is the
    concatenation of the register-allocated expansions of the body's instructions. -/
theorem physBodyWithStores_eq_physExpand (shiftImm : ShiftImmOracle) (body : Lcmd)
    (loadBase storeBase : String) (abiW : Nat)
    (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (rv : List Nat)
    (hcall : ∀ i ∈ body, ∀ a b, i.li_i ≠ .Lcall a b) :
    physBodyWithStores shiftImm body (fun _ => none) loadBase [] storeBase abiW
        memrefBaseReload callArgBaseReload rv
      = body.flatMap (physExpand shiftImm (LprogAsmPrinter.bodyIsU64 body) (physRmap body rv)
          memrefBaseReload) := by
  rw [physBodyWithStores_eq_flatMap]
  have h : ∀ p ∈ body.zipIdx, physPositionEmit shiftImm body (fun _ => none) loadBase []
      storeBase abiW memrefBaseReload callArgBaseReload rv p
        = physExpand shiftImm (LprogAsmPrinter.bodyIsU64 body) (physRmap body rv)
            memrefBaseReload p.1 := by
    rintro ⟨i, k⟩ hp
    exact physPositionEmit_eq_physExpand _ _ _ _ _ _ _ _ i k
      (hcall i (List.fst_mem_of_mem_zipIdx hp))
  rw [List.flatMap_congr h, ← List.flatMap_map (f := Prod.fst), List.zipIdx_map_fst]

/-! ## 2. The components of the physical-ABI export -/

section Components

variable {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t) (outArg : String)
  (inArgs : List String) (immSlotMap : ImmSlotMap) (abiArgs : List String)

/-- The out-array and in-array base names `ComL.toLfundefPhysAbi` derives. -/
def abiDerived : String × List String :=
  match ComL.loopArgBaseNames Γ.length immSlotMap c Γ.length with
  | some (o, ins) => (o, ins)
  | none => (outArg, inArgs)

/-- The argument-liveness pin `ComL.toLfundefPhysAbi` puts in front of the virtual
    body of a signature with four or more arguments. -/
def abiLivePin : Lcmd :=
  if abiArgs.length ≥ 4 then
    [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
          ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
  else []

/-- The virtual body `ComL.toLfundefPhysAbi` allocates: the liveness pin, then the
    loop accumulators aliased onto the out-array name and the store thread
    canonicalised. -/
def abiBody1 : Lcmd :=
  abiLivePin abiArgs
    ++ canonicalizeMemrefThread
         (((ComL.loopAccRegs c Γ.length).map regName).foldl
            (fun b r => aliasRegBody r (abiDerived c outArg inArgs immSlotMap).1 b)
            (ComL.toLfundef c immSlotMap).lfd_body)

/-- The virtual function `ComL.toLfundefPhysAbi` allocates. -/
def abiVirt : Lfundef :=
  { ComL.toLfundef c immSlotMap with
    lfd_body := abiBody1 c outArg inArgs immSlotMap abiArgs }

/-- The allocation table of the physical-ABI export. -/
def abiTbl : Array Nat := physTableOut (abiBody1 c outArg inArgs immSlotMap abiArgs) []

/-- The shift-count oracle of the physical-ABI export: the caller's, then the
    constant-move table of the virtual body. -/
def abiShiftImm (shiftImm : ShiftImmOracle) : ShiftImmOracle := fun nm =>
  match shiftImm nm with
  | some v => some v
  | none => movImmLookup (movImmTable (abiBody1 c outArg inArgs immSlotMap abiArgs)) nm

/-- The memref-base reload map of the physical-ABI export: each array argument's
    allocated register to its red-zone save slot. -/
def abiReload : String → Option String := fun base =>
  let d := abiDerived c outArg inArgs immSlotMap
  let argAbi : List (String × String) := (d.1, abiArgs.headD "RDI") :: (d.2.zip (abiArgs.drop 1))
  let reloadPairs : List (String × String) :=
    argAbi.filterMap (fun (argNm, abiReg) =>
      match abiSaveOfExt abiReg with
      | some saveName =>
          some (physNameForBody (abiBody1 c outArg inArgs immSlotMap abiArgs)
            (abiTbl c outArg inArgs immSlotMap abiArgs) argNm, saveName)
      | none => none)
  (reloadPairs.find? (fun p => p.1 == base)).map Prod.snd

/-- The post-call base reload list of the physical-ABI export. -/
def abiCallReload : List (String × String) :=
  (abiArgs.zipIdx).filterMap (fun (abiReg, j) =>
    match abiSaveOfExt abiReg with
    | some saveName =>
        let phys := physNameForBody (abiBody1 c outArg inArgs immSlotMap abiArgs)
          (abiTbl c outArg inArgs immSlotMap abiArgs) (argName j)
        if isCallerSavedAllocGPR phys then some (phys, saveName) else none
    | none => none)

/-- The saves of the third and later argument registers other than `RDI` and `RSI` to their
    red-zone slots (`extraSaveRegs`). -/
def abiExtraSaves : Lcmd :=
  (extraSaveRegs abiArgs).filterMap (fun abiReg =>
    match abiSaveOfExt abiReg with
    | some saveName => some (⟨0, .Lopn [.reg saveName] "MOVQ" [.reg abiReg]⟩ : Linstr)
    | none => none)

/-- A position that is not the argument-liveness pin. -/
def notLivePin (i : Linstr) : Bool :=
  match i.li_i with | .Lopn _ opn _ => opn != "LIVEPIN" | _ => true

theorem toLfundefPhysAbi_body (shiftImm : ShiftImmOracle) (abiTyin : List Nat) :
    (ComL.toLfundefPhysAbi c outArg inArgs shiftImm immSlotMap abiArgs abiTyin).lfd_body
      = buildPrologue (abiVirt c outArg inArgs immSlotMap abiArgs)
            (abiTbl c outArg inArgs immSlotMap abiArgs) (fun _ => none)
          ++ abiExtraSaves abiArgs
          ++ buildArgPtrMaterialize (abiVirt c outArg inArgs immSlotMap abiArgs)
            (abiTbl c outArg inArgs immSlotMap abiArgs) abiArgs (fun _ => none)
          ++ insertEpilogue
            ((physBodyWithStores (abiShiftImm c outArg inArgs immSlotMap abiArgs shiftImm)
              (abiBody1 c outArg inArgs immSlotMap abiArgs) (fun _ => none) reloadScratch2 []
              reloadScratch2 0 (abiReload c outArg inArgs immSlotMap abiArgs)
              (abiCallReload c outArg inArgs immSlotMap abiArgs)).filter notLivePin)
            calleeSaveRestoreEpilogue := rfl

end Components

/-! ## 2a. The two pairings of array bases with argument registers -/

/-- The entry of `l.zipIdx k` whose index names the argument `k + j` is the `j`-th. -/
theorem zipIdx_find_argName : ∀ (l : List String) (k j : Nat) (hj : j < l.length),
    (l.zipIdx k).find? (fun q => argName q.2 == argName (k + j)) = some (l[j], k + j)
  | [], _, _, hj => by simp at hj
  | a :: l, k, 0, _ => by simp [List.zipIdx_cons]
  | a :: l, k, j + 1, hj => by
    have hne : (argName k == argName (k + (j + 1))) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      have := JasminLsemSimulation.argName_injective h
      omega
    rw [List.zipIdx_cons, List.find?_cons, hne]
    have := zipIdx_find_argName l (k + 1) j (by simpa using hj)
    rw [show k + 1 + j = k + (j + 1) by omega] at this
    simpa using this

/-- The pairs by slot of argument names below the length of `abiArgs`: each name
    `argName j` with the register `abiArgs[j]`. -/
theorem argBasePairsPos_map_argName (abiArgs : List String) :
    ∀ js : List Nat, (∀ j ∈ js, j < abiArgs.length) →
      argBasePairsPos (js.map argName) abiArgs
        = js.map fun j => (argName j, abiArgs[j]?.getD "")
  | [], _ => rfl
  | j :: js, h => by
    have hj : j < abiArgs.length := h j (by simp)
    have hf := zipIdx_find_argName abiArgs 0 j hj
    rw [Nat.zero_add] at hf
    have ih := argBasePairsPos_map_argName abiArgs js fun i hi => h i (by simp [hi])
    unfold argBasePairsPos at ih ⊢
    rw [List.map_cons, List.filterMap_cons, hf, ih]
    simp [List.getElem?_eq_getElem hj]

/-- **Each array base takes the register of its own argument slot** at
    `posBind = true`: for the out base `argName o` and the in bases `argName j`,
    `j ∈ ins`, all below the length of `abiArgs`, the pairs are `(argName j, abiArgs[j])`
    for `j` in `o :: ins`. -/
theorem argBasePairs_true_argName (abiArgs : List String) (o : Nat) (ins : List Nat)
    (h : ∀ j ∈ o :: ins, j < abiArgs.length) :
    argBasePairs true (argName o) (ins.map argName) abiArgs
      = (o :: ins).map fun j => (argName j, abiArgs[j]?.getD "") :=
  argBasePairsPos_map_argName abiArgs (o :: ins) h

/-- A loop with the output array at argument `2`, an input array at argument `1` and
    the registers `RDI`, `RSI`, `RDX`: the output base takes `RDX` and the input base
    `RSI`, so the scalar at argument `0` is alone on `RDI`. -/
theorem argBasePairs_true_out2 :
    argBasePairs true (argName 2) [argName 1] ["RDI", "RSI", "RDX"]
      = [(argName 2, "RDX"), (argName 1, "RSI")] :=
  argBasePairs_true_argName ["RDI", "RSI", "RDX"] 2 [1] (by simp)

/-- The pairs by slot of the argument names `s, …, s + n - 1` below the length of
    `abiArgs` are the names zipped with the registers from slot `s`. -/
theorem argBasePairsPos_range' (abiArgs : List String) :
    ∀ (n s : Nat), s + n ≤ abiArgs.length →
      argBasePairsPos ((List.range' s n).map argName) abiArgs
        = ((List.range' s n).map argName).zip (abiArgs.drop s)
  | 0, _, _ => by simp [argBasePairsPos]
  | n + 1, s, h => by
    have hs : s < abiArgs.length := by omega
    have hf := zipIdx_find_argName abiArgs 0 s hs
    rw [Nat.zero_add] at hf
    have ih := argBasePairsPos_range' abiArgs n (s + 1) (by omega)
    unfold argBasePairsPos at ih ⊢
    rw [List.range'_succ, List.map_cons, List.filterMap_cons, hf, List.drop_eq_getElem_cons hs]
    simp only [Option.map_some, List.zip_cons_cons]
    rw [ih]

/-- **The two pairings agree when the output array is argument `0`.** With the out
    base `argName 0` and the in bases `argName 1, …, argName m`, all below the length
    of `abiArgs`, the pairs by slot are the pairs by role. -/
theorem argBasePairs_true_eq_false (m : Nat) (abiArgs : List String)
    (hm : m < abiArgs.length) :
    argBasePairs true (argName 0) ((List.range m).map fun i => argName (i + 1)) abiArgs
      = argBasePairs false (argName 0) ((List.range m).map fun i => argName (i + 1))
          abiArgs := by
  have h := argBasePairsPos_range' abiArgs (m + 1) 0 (by omega)
  have hr : (List.range m).map (fun i => argName (i + 1)) = (List.range' 1 m).map argName := by
    rw [List.range'_eq_map_range, List.map_map]
    apply List.map_congr_left
    intro i _
    simp [Nat.add_comm]
  rw [List.range'_succ, List.map_cons] at h
  show argBasePairsPos _ _ = _ :: _
  rw [hr, h]
  cases abiArgs with
  | nil => simp at hm
  | cons a l => simp

/-- **The export by slot of a program with the output array at argument `0`** is its
    export by role: for a loop node with the out base `argName 0` and the in bases
    `argName 1, …, argName m` below the length of `abiArgs`, `ComL.toLfundefPhysAbi`
    at `posBind = true` is `ComL.toLfundefPhysAbi` at `posBind = false`. -/
theorem toLfundefPhysAbi_posBind_of_out0 {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : ComL Γ t) (outArg : String) (inArgs : List String) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) (abiArgs : List String) (abiTyin : List Nat) (m : Nat)
    (hd : ComL.loopArgBaseNames Γ.length immSlotMap c Γ.length
      = some (argName 0, (List.range m).map fun i => argName (i + 1)))
    (hm : m < abiArgs.length) :
    ComL.toLfundefPhysAbi c outArg inArgs shiftImm immSlotMap abiArgs abiTyin
        LprogAsmPrinter.x86Abi true
      = ComL.toLfundefPhysAbi c outArg inArgs shiftImm immSlotMap abiArgs abiTyin :=
  ComL.toLfundefPhysAbi_posBind_congr c outArg inArgs shiftImm immSlotMap abiArgs abiTyin _ _ _
    hd (argBasePairs_true_eq_false m abiArgs hm)

/-- `String.startsWith` is the list prefix test on the characters, which the kernel
    evaluates on literals. -/
theorem startsWith_eq_isPrefixOf (s p : String) :
    s.startsWith p = p.toList.isPrefixOf s.toList := by
  rw [Bool.eq_iff_iff, String.startsWith_string_iff, List.isPrefixOf_iff_prefix]

/-- `String.isPrefixOf` is the list prefix test on the characters. -/
theorem isPrefixOf_eq_list (p s : String) :
    p.isPrefixOf s = p.toList.isPrefixOf s.toList :=
  startsWith_eq_isPrefixOf s p

theorem isNativeShiftRotate_livepin : isNativeShiftRotate "LIVEPIN" = false := by
  have h : stripWidthTag "LIVEPIN" = "LIVEPIN" := by decide +kernel
  simp only [isNativeShiftRotate, h, isPrefixOf_eq_list]
  decide +kernel

theorem physExpand_livepin (shiftImm : ShiftImmOracle) (u64 : Bool)
    (rmap : LOperand → LOperand)
    (rl : String → Option String) (ii : Nat) (ds ss : List LOperand) :
    (physExpand shiftImm u64 rmap rl ⟨ii, .Lopn ds "LIVEPIN" ss⟩).filter notLivePin = [] := by
  have hs : isMemStore "LIVEPIN" = false := by decide +kernel
  have hl : isMemLoad "LIVEPIN" = false := by decide +kernel
  have hb : isTwoAddrBinop "LIVEPIN" = false := by decide +kernel
  have hm : ∀ d s, legalizeOneSrc u64 "LIVEPIN" d s = [.Lopn [d] "LIVEPIN" [s]] := fun d s =>
    legalizeOneSrc_of_ne d s (by decide +kernel) (by decide +kernel)
  have hc : ∀ ds ss, legalizeSpillDst ds "LIVEPIN" ss = [.Lopn ds "LIVEPIN" ss] := fun ds ss =>
    legalizeSpillDst_of_ne ds ss (by decide +kernel) (by decide +kernel)
  rcases ds with _ | ⟨d, _ | ⟨d', ds⟩⟩ <;> rcases ss with _ | ⟨s0, _ | ⟨s1, _ | ⟨s2, ss⟩⟩⟩ <;>
    simp [physExpand, hs, hl, hb, hm, hc, isNativeShiftRotate_livepin, notLivePin]

/-- The expansions of the argument-liveness pin are all dropped by the pin filter. -/
theorem abiLivePin_flatMap_filter (shiftImm : ShiftImmOracle) (u64 : Bool)
    (rmap : LOperand → LOperand)
    (rl : String → Option String) (abiArgs : List String) :
    ((abiLivePin abiArgs).flatMap (physExpand shiftImm u64 rmap rl)).filter notLivePin = [] := by
  unfold abiLivePin
  split
  · rw [List.flatMap_singleton]; exact physExpand_livepin _ _ _ _ _ _ _
  · rfl

/-- A return appended to a body adds no entry to the store-thread alias map. -/
theorem arrChainAlias_append_ret (x : Lcmd) (ii : Nat) :
    arrChainAlias (x ++ [⟨ii, .Lret⟩]) = arrChainAlias x := by
  unfold arrChainAlias
  simp only [Id.run]
  generalize (∅ : Std.HashMap String String) = m
  induction x generalizing m with
  | nil => rfl
  | cons a x ih =>
    rw [List.cons_append, List.forIn_cons, List.forIn_cons]
    split <;> (try split) <;> exact ih _

/-- One step of the store-thread alias map as an association list, newest entry first:
    a memory store `dst ← (base, …)` binds `dst` to the resolution of `base`. -/
def aliasStepL (l : List (String × String)) (i : Linstr) : List (String × String) :=
  match i.li_i with
  | .Lopn [.reg dst] opn (.arrIdx base _ _ :: _) =>
      if isMemStore opn then (dst, (l.lookup base).getD base) :: l else l
  | _ => l

/-- **The store-thread alias map as an association list.** `arrChainAlias` resolves every
    name as the association list `aliasStepL` builds, and is empty exactly when that
    list is. -/
theorem arrChainAlias_spec (body : Lcmd) :
    (∀ n, (arrChainAlias body).getD n n = ((body.foldl aliasStepL []).lookup n).getD n)
      ∧ (arrChainAlias body).isEmpty = (body.foldl aliasStepL []).isEmpty := by
  unfold arrChainAlias
  simp only [Id.run, bind_pure]
  have h0 : ∀ n, (∅ : Std.HashMap String String).getD n n
      = (([] : List (String × String)).lookup n).getD n := by simp
  have h1 : (∅ : Std.HashMap String String).isEmpty = ([] : List (String × String)).isEmpty := by
    simp
  revert h0 h1
  generalize (∅ : Std.HashMap String String) = m
  generalize ([] : List (String × String)) = l
  induction body generalizing m l with
  | nil => intro h0 h1; exact ⟨h0, h1⟩
  | cons a x ih =>
    intro h0 h1
    rw [List.forIn_cons, List.foldl_cons]
    rw [aliasStepL]
    split
    next dst opn base _ _ _ heq =>
      rw [heq]
      dsimp only
      split
      · refine ih _ _ (fun n => ?_) (by simp)
        rw [Std.HashMap.getD_insert, h0, List.lookup_cons]
        by_cases h : n = dst
        · subst h; simp
        · have hb : (n == dst) = false := by simp [h]
          have hb' : (dst == n) = false := by simp [Ne.symm h]
          simp only [hb, hb', Bool.false_eq_true, if_false]
          exact h0 n
      · exact ih _ _ h0 h1
    next heq =>
      split
      next heq2 => exact absurd heq2 (heq _ _ _ _ _ _)
      exact ih _ _ h0 h1

/-- A position that is not a call. -/
def notCall (i : Linstr) : Bool := match i.li_i with | .Lcall _ _ => false | _ => true

/-- A body every position of which passes `notCall` issues no call. -/
theorem noCall_of_all (body : Lcmd) (h : body.all notCall = true) :
    ∀ i ∈ body, ∀ a b, i.li_i ≠ .Lcall a b := by
  intro i hi a b he
  have := List.all_eq_true.mp h i hi
  simp [notCall, he] at this

/-- `bodyHasMulHi` with the prefix test on the character lists. -/
theorem bodyHasMulHi_eq (body : Lcmd) :
    bodyHasMulHi body = body.any (fun i => match i.li_i with
      | .Lopn _ opn _ => hasPrefix opn "MULXHI"
      | _ => false) := by
  unfold bodyHasMulHi
  congr 1
  funext i
  rcases i with ⟨ii, w⟩
  cases w <;> simp [startsWith_eq_isPrefixOf, hasPrefix]

/-- `isVectorMnem` with the prefix test on the character lists. -/
theorem isVectorMnem_eq (opn : String) : isVectorMnem opn = hasPrefix (stripWidthTag opn) "V" := by
  simp [isVectorMnem, startsWith_eq_isPrefixOf, hasPrefix]

/-- A class-aware table over `Array.range` is the array of the list map. -/
theorem physTableClassed_eq (tr : List PhysEvent) (v : Array Bool) (r rv : List Nat) :
    physTableClassed tr v r rv =
      ((List.range (physUniverse tr)).map (fun s =>
        match (physAssignClassed tr v r rv).find? (fun p => p.1 == s) with
        | some (_, ph) => ph
        | none => s)).toArray := by
  unfold physTableClassed
  apply Array.toList_inj.mp
  simp only [Array.toList_map, Array.toList_range]
  rfl

/-- A body without a vector mnemonic classifies every slot general-purpose. -/
theorem bodyVecSlots_noVec (body : Lcmd)
    (h : body.all (fun i => match i.li_i with
      | .Lopn _ opn _ => !hasPrefix (stripWidthTag opn) "V"
      | _ => true) = true) :
    bodyVecSlots body = Array.replicate ((bodyNames body).length + 1) false := by
  have hconst : ∀ {α β : Type} (l : List α) (f : α → β → Id (ForInStep β)),
      (∀ x ∈ l, ∀ b, f x b = pure (.yield b)) → ∀ b, forIn l b f = pure b := by
    intro α β l f hf b
    induction l generalizing b with
    | nil => rfl
    | cons x l ih =>
      rw [List.forIn_cons, hf x (List.mem_cons_self ..) b]
      exact ih (fun y hy => hf y (List.mem_cons_of_mem _ hy)) b
  have hv : bodyHasVecOp body = false := by
    rw [bodyHasVecOp, List.any_eq_false]
    intro x hx
    have hx' := List.all_eq_true.mp h x hx
    rcases x with ⟨ii, w⟩
    cases w <;> simp_all [isVectorMnem_eq]
  unfold bodyVecSlots
  simp only [Id.run]
  rw [hconst]
  · rfl
  intro x hx b
  have hx' := List.all_eq_true.mp h x hx
  rcases x with ⟨ii, w⟩
  cases w <;> simp_all [isVectorMnem_eq]

/-- `nameSlot` over a body whose name universe is `ns` is the index in `ns`. -/
theorem nameSlot_of_bodyNames {body : Lcmd} {ns : List String} (h : bodyNames body = ns) :
    nameSlot body = fun n => ns.idxOf n := by
  funext n
  rw [nameSlot, h]

/-- The trace of a body whose name universe is `ns`, with every slot an index in `ns`. -/
theorem bodyTrace_of_bodyNames {body : Lcmd} {ns : List String} (h : bodyNames body = ns) :
    bodyTrace body = (bodyOpNames body).map (fun p =>
      { wr := (p.1.map ns.idxOf).getD 0, rds := p.2.map ns.idxOf }) := by
  rw [bodyTrace, nameSlot_of_bodyNames h]

/-- The operand renaming of a call-free body whose name universe is `ns`, with every slot
    an index in `ns`. -/
theorem physRmap_of_bodyNames {body : Lcmd} {ns : List String} (h : bodyNames body = ns)
    (hc : bodyHasCall body = false) (rv : List Nat) :
    physRmap body rv = fun o => match o with
      | .reg n => .reg (physRegName (physMapTabled (physTableOut body [] rv) (ns.idxOf n)))
      | .arrIdx base idx scale =>
          .arrIdx (physRegName (physMapTabled (physTableOut body [] rv) (ns.idxOf base)))
            (physRegName (physMapTabled (physTableOut body [] rv) (ns.idxOf idx))) scale
      | o => o := by
  have hs : bodyStraightCall body = false := by simp [bodyStraightCall, hc]
  funext o
  cases o <;> simp [physRmap, hc, straightCallComposeTable, hs, remapOperand,
    nameSlot_of_bodyNames h]

/-- The physical name of a register of a call-free body whose name universe is `ns`. -/
theorem physNameForBody_of_bodyNames {body : Lcmd} {ns : List String} (h : bodyNames body = ns)
    (hc : bodyHasCall body = false) (tbl : Array Nat) (n : String) :
    physNameForBody body tbl n
      = if isFrameSlotName n then n else physRegName (physMapTabled tbl (ns.idxOf n)) := by
  simp [physNameForBody, hc, nameSlot_of_bodyNames h]

/-- `LOperand.isSpill` with the prefix test on the character lists. -/
theorem isSpill_eq (o : LOperand) :
    o.isSpill = (match o with | .reg n => hasPrefix n "k." | _ => false) := by
  cases o <;> simp [LOperand.isSpill, isPrefixOf_eq_list, hasPrefix]

/-- `sibNameSpill` with the prefix test on the character lists. -/
theorem sibNameSpill_eq (n : String) : sibNameSpill n = hasPrefix n "k." := by
  simp [sibNameSpill, isPrefixOf_eq_list, hasPrefix]

/-- `isNativeShiftRotate` with the prefix test on the character lists. -/
theorem isNativeShiftRotate_eq (opn : String) :
    isNativeShiftRotate opn
      = ["ROR:", "ROL:", "SHL:", "SHR:", "SAR:"].any (fun p => hasPrefix (stripWidthTag opn) p) := by
  simp [isNativeShiftRotate, isPrefixOf_eq_list, hasPrefix]

/-! ## 3. The single-loop export -/

section SingleLoop

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (renLcmd renLinstr
  canonicalizeMemrefThread_eq_renLcmd aliasRegBody_eq_renLcmd)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renLinstrR)

variable {Γ : Ctxt jasminDialect} {accTy : JasminTy} {invTys : Ctxt jasminDialect}
  (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
  (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ accTy)
  (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (immSlotMap : ImmSlotMap)

/-- The program with one runtime-count loop node and nothing after it. -/
abbrev singleLoop : ComL Γ accTy := ComL.forLoopNRt update count init invs (.ret .here)

/-- The virtual loop node `comLToBody` emits for `singleLoop`. -/
def loopNode : Lcmd :=
  forLoopLcmdNRt Γ.length (regName Γ.length)
    (resolveVar Γ.length Γ.length argName immSlotMap init)
    (resolveVar Γ.length Γ.length argName immSlotMap count) update
    (exprArgsHV Γ.length Γ.length argName immSlotMap invs) immSlotMap

theorem toLfundef_singleLoop_body :
    (ComL.toLfundef (singleLoop update count init invs) immSlotMap).lfd_body
      = loopNode update count init invs immSlotMap ++ [⟨0, .Lret⟩] := rfl

theorem renLcmd_append_ret (σ : String → String) (x : Lcmd) :
    renLcmd σ (x ++ [⟨0, .Lret⟩]) = renLcmd σ x ++ [⟨0, .Lret⟩] := by
  simp [renLcmd, renLinstr, renLinstrR]

/-- **The allocated virtual body of the single-loop export.** When the store thread
    of the aliased node is not empty and its alias map resolves as `κ`, the body
    `ComL.toLfundefPhysAbi` allocates is the liveness pin, the node renamed by `κ`
    after the accumulator alias, and the return. -/
theorem abiBody1_singleLoop (outArg : String) (inArgs abiArgs : List String)
    (κ : String → String)
    (hne : (arrChainAlias (aliasRegBody (regName Γ.length)
      (abiDerived (singleLoop update count init invs) outArg inArgs immSlotMap).1
      (loopNode update count init invs immSlotMap))).isEmpty = false)
    (hκ : canonMemrefName (arrChainAlias (aliasRegBody (regName Γ.length)
      (abiDerived (singleLoop update count init invs) outArg inArgs immSlotMap).1
      (loopNode update count init invs immSlotMap))) = κ) :
    abiBody1 (singleLoop update count init invs) outArg inArgs immSlotMap abiArgs
      = abiLivePin abiArgs
        ++ (renLcmd κ (aliasRegBody (regName Γ.length)
            (abiDerived (singleLoop update count init invs) outArg inArgs immSlotMap).1
            (loopNode update count init invs immSlotMap)) ++ [⟨0, .Lret⟩]) := by
  have hacc : ComL.loopAccRegs (singleLoop update count init invs) Γ.length = [Γ.length] :=
    rfl
  unfold abiBody1
  rw [toLfundef_singleLoop_body, hacc, List.map_singleton, List.foldl_cons, List.foldl_nil]
  have hal : aliasRegBody (regName Γ.length)
      (abiDerived (singleLoop update count init invs) outArg inArgs immSlotMap).1
      (loopNode update count init invs immSlotMap ++ [⟨0, .Lret⟩])
      = aliasRegBody (regName Γ.length)
          (abiDerived (singleLoop update count init invs) outArg inArgs immSlotMap).1
          (loopNode update count init invs immSlotMap) ++ [⟨0, .Lret⟩] := by
    simp [aliasRegBody]
  rw [hal, canonicalizeMemrefThread_eq_renLcmd, arrChainAlias_append_ret, if_neg (by simp [hne]),
    hκ, renLcmd_append_ret]

/-- **The physical-ABI export of a single loop node.** For the program with one
    runtime-count loop node and nothing after it, whose node issues no call, whose
    aliased store thread is not empty and resolves as `κ`, the physical body is the
    qsave prologue, the saves of the further argument registers, the argument
    materialization, the register-allocated expansion (`physExpand`) of each
    instruction of the node renamed by `κ` after the accumulator alias, with the
    liveness pin dropped, the callee-saved restores and the return.

    A continuation after the loop node is outside the statement: the exporter
    aliases every loop accumulator of a chain onto one name. -/
theorem toLfundefPhysAbi_singleLoop (outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle) (abiArgs : List String) (abiTyin : List Nat)
    (κ : String → String)
    (hne : (arrChainAlias (aliasRegBody (regName Γ.length)
      (abiDerived (singleLoop update count init invs) outArg inArgs immSlotMap).1
      (loopNode update count init invs immSlotMap))).isEmpty = false)
    (hκ : canonMemrefName (arrChainAlias (aliasRegBody (regName Γ.length)
      (abiDerived (singleLoop update count init invs) outArg inArgs immSlotMap).1
      (loopNode update count init invs immSlotMap))) = κ)
    (hcall : ∀ i ∈ loopNode update count init invs immSlotMap, ∀ a b, i.li_i ≠ .Lcall a b) :
    (ComL.toLfundefPhysAbi (singleLoop update count init invs) outArg inArgs shiftImm
        immSlotMap abiArgs abiTyin).lfd_body
      = buildPrologue (abiVirt (singleLoop update count init invs) outArg inArgs
            immSlotMap abiArgs)
          (abiTbl (singleLoop update count init invs) outArg inArgs immSlotMap abiArgs)
          (fun _ => none)
        ++ abiExtraSaves abiArgs
        ++ buildArgPtrMaterialize (abiVirt (singleLoop update count init invs) outArg inArgs
            immSlotMap abiArgs)
          (abiTbl (singleLoop update count init invs) outArg inArgs immSlotMap abiArgs)
          abiArgs (fun _ => none)
        ++ (renLcmd κ (aliasRegBody (regName Γ.length)
              (abiDerived (singleLoop update count init invs) outArg inArgs immSlotMap).1
              (loopNode update count init invs immSlotMap))).flatMap
            (fun i => (physExpand
              (abiShiftImm (singleLoop update count init invs) outArg inArgs immSlotMap
                abiArgs shiftImm)
              (LprogAsmPrinter.bodyIsU64 (abiBody1 (singleLoop update count init invs) outArg
                inArgs immSlotMap abiArgs))
              (physRmap (abiBody1 (singleLoop update count init invs) outArg inArgs
                immSlotMap abiArgs) [])
              (abiReload (singleLoop update count init invs) outArg inArgs immSlotMap
                abiArgs) i).filter notLivePin)
        ++ calleeSaveRestoreEpilogue ++ [⟨0, .Lret⟩] := by
  have hb1 := abiBody1_singleLoop update count init invs immSlotMap outArg inArgs abiArgs κ
    hne hκ
  have hc1 : ∀ i ∈ abiBody1 (singleLoop update count init invs) outArg inArgs immSlotMap
      abiArgs, ∀ a b, i.li_i ≠ .Lcall a b := by
    rw [hb1]
    intro i hi a b
    rw [List.mem_append, List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | hi | hi
    · by_cases h4 : abiArgs.length ≥ 4
      · simp only [abiLivePin, h4, if_true, List.mem_singleton] at hi; subst hi; simp
      · simp [abiLivePin, h4] at hi
    · simp only [renLcmd, aliasRegBody, List.map_map, List.mem_map] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      have := hcall j hj
      obtain ⟨jj, w⟩ := j
      cases w <;> simp_all [renLinstr, renLinstrR]
    · subst hi; simp
  rw [toLfundefPhysAbi_body, physBodyWithStores_eq_physExpand _ _ _ _ _ _ _ _ hc1]
  rw [hb1, List.flatMap_append, List.filter_append, abiLivePin_flatMap_filter,
    List.nil_append, List.flatMap_append, List.filter_append, List.flatMap_singleton]
  have hret : ∀ sh u rm rl, (physExpand sh u rm rl ⟨0, .Lret⟩).filter notLivePin
      = [⟨0, .Lret⟩] := fun _ _ _ _ => rfl
  rw [hret, insertEpilogue, List.dropLast_concat, List.filter_flatMap]
  simp only [List.append_assoc]

end SingleLoop

/-! ## 4. The `MULX` fusion on a body with one multiply site -/

section Fuser

open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi

/-- An instruction that is neither a low `MUL` nor a `MULXHI` of the
    three-register form `fuseMulHiAux` matches. -/
def NoMulSite (i : Linstr) : Prop :=
  ∀ d opn s1 s2, i.li_i = .Lopn [.reg d] opn [.reg s1, .reg s2] →
    isLowMulMnem opn = false ∧ isMulHiMnem opn = false

open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi in
/-- The Boolean test for `NoMulSite`. -/
def noMulSiteB (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn [.reg _] opn [.reg _, .reg _] => !isLowMulMnem opn && !isMulHiMnem opn
  | _ => true

/-- A body every position of which passes `noMulSiteB` has no multiply site. -/
theorem noMulSite_of_all (xs : Lcmd) (h : xs.all noMulSiteB = true) : ∀ i ∈ xs, NoMulSite i := by
  intro i hi d opn s1 s2 he
  have := List.all_eq_true.mp h i hi
  simp only [noMulSiteB, he, Bool.and_eq_true, Bool.not_eq_true'] at this
  exact this

theorem fuseMulHiAux_cons_noSite (s : Bool) (env : ScratchEnv) (pend : List (String × String))
    (i : Linstr) (rest : Lcmd) (h : NoMulSite i) :
    fuseMulHiAux s env pend (i :: rest) = i :: fuseMulHiAux s (scratchStep env i) pend rest := by
  rw [fuseMulHiAux]
  split
  · rename_i d opn s1 s2 heq
    obtain ⟨h1, h2⟩ := h d opn s1 s2 heq
    simp [h1, h2]
  · rfl

theorem fuseMulHiAux_nil (s : Bool) (env : ScratchEnv) (pend : List (String × String)) :
    fuseMulHiAux s env pend [] = [] := by
  rw [fuseMulHiAux]

/-- A run of instructions without a multiply site passes through the fusion. -/
theorem fuseMulHiAux_append_noSite (s : Bool) (pend : List (String × String)) (xs ys : Lcmd)
    (h : ∀ i ∈ xs, NoMulSite i) (env : ScratchEnv) :
    fuseMulHiAux s env pend (xs ++ ys)
      = xs ++ fuseMulHiAux s (xs.foldl scratchStep env) pend ys := by
  induction xs generalizing env with
  | nil => rfl
  | cons i xs ih =>
    rw [List.cons_append, fuseMulHiAux_cons_noSite _ _ _ _ _ (h i (by simp)),
      ih (fun j hj => h j (by simp [hj]))]
    rfl

theorem fuseMulHiAux_noSite (s : Bool) (pend : List (String × String)) (xs : Lcmd)
    (h : ∀ i ∈ xs, NoMulSite i) (env : ScratchEnv) :
    fuseMulHiAux s env pend xs = xs := by
  simpa [fuseMulHiAux_nil] using fuseMulHiAux_append_noSite s pend xs [] h env

/-- A low `MUL` whose multiplicand is no reload scratch is kept and recorded as
    pending at its destination, keyed on its resolved multiplicand. -/
theorem fuseMulHiAux_cons_lowMul (s : Bool) (env : ScratchEnv) (pend : List (String × String))
    (ii : Nat) (d opn s1 s2 : String) (rest : Lcmd) (hlo : isLowMulMnem opn = true)
    (hs2 : fuseReloadScratches.contains s2 = false) :
    fuseMulHiAux s env pend (⟨ii, .Lopn [.reg d] opn [.reg s1, .reg s2]⟩ :: rest)
      = ⟨ii, .Lopn [.reg d] opn [.reg s1, .reg s2]⟩
        :: fuseMulHiAux s (scratchStep env ⟨ii, .Lopn [.reg d] opn [.reg s1, .reg s2]⟩)
          ((d, scratchResolve env s2) :: pend) rest := by
  rw [fuseMulHiAux]
  simp [hlo, lowHome_of_not_scratch env hs2]

/-- **The fused site in the looped-body mode.** A `MULXHI` whose resolved
    multiplicand matches a pending low `MUL` with register destinations, with a
    register high destination other than `RDX` and a register multiplicand other
    than `RDX`, becomes the save of `RDX` to `R15`, the pin of the other factor in
    `RDX`, the two-output `MULX` and the restore of `RDX`. -/
theorem fuseMulHiAux_cons_mulHi_saveRdx (env : ScratchEnv)
    (pend before after : List (String × String)) (loDst k : String)
    (jj : Nat) (d opn s1 s2 : String) (rest : Lcmd)
    (hnlo : isLowMulMnem opn = false) (hhi : isMulHiMnem opn = true)
    (hspan : pend.span (fun p => p.2 != scratchResolve env s2)
      = (before, (loDst, k) :: after))
    (hd : (LOperand.reg d).isSpill = false) (hdR : (d == "RDX") = false)
    (hs2 : (LOperand.reg s2).isSpill = false) (hs2R : (s2 == "RDX") = false)
    (hlo : (LOperand.reg loDst).isSpill = false) :
    fuseMulHiAux true env pend (⟨jj, .Lopn [.reg d] opn [.reg s1, .reg s2]⟩ :: rest)
      = ⟨jj, .Lopn [.reg "R15"] "MOVQ" [.reg "RDX"]⟩
        :: ⟨jj, .Lopn [.reg "RDX"] "MOV:64" [.reg s1]⟩
        :: ⟨jj, .Lopn [.reg loDst, .reg d] "MULX" [.reg s2]⟩
        :: ((if (loDst != "RDX") = true then [⟨jj, .Lopn [.reg "RDX"] "MOVQ" [.reg "R15"]⟩]
              else [])
          ++ fuseMulHiAux true
            ([reloadScratch, reloadScratch2, loDst, d].foldl scratchKill
              (scratchStep env ⟨jj, .Lopn [.reg d] opn [.reg s1, .reg s2]⟩))
            (before ++ after) rest) := by
  rw [fuseMulHiAux]
  simp only [hspan]
  simp [hnlo, hhi, hd, hdR, hs2, hs2R, hlo]

/-- A scratch environment that records only the reserved reload scratches. -/
def EnvScratch (env : ScratchEnv) : Prop := ∀ p ∈ env, p.1 ∈ fuseReloadScratches

theorem scratchResolve_of_envScratch {env : ScratchEnv} (h : EnvScratch env) {r : String}
    (hr : r ∉ fuseReloadScratches) : scratchResolve env r = r := by
  unfold scratchResolve
  split
  · rename_i p v hp
    obtain ⟨hmem, heq⟩ := List.mem_of_find?_eq_some hp, List.find?_some hp
    have : p = r := by simpa using heq
    exact absurd (this ▸ h _ hmem) hr
  · rfl

theorem EnvScratch.kill {env : ScratchEnv} (h : EnvScratch env) (dst : String) :
    EnvScratch (scratchKill env dst) := fun p hp =>
  h p (List.mem_of_mem_filter hp)

theorem EnvScratch.step {env : ScratchEnv} (h : EnvScratch env) (i : Linstr) :
    EnvScratch (scratchStep env i) := by
  have hfold : ∀ (f : ScratchEnv → LOperand → ScratchEnv),
      (∀ e d, EnvScratch e → EnvScratch (f e d)) →
      ∀ (ds : List LOperand) (e : ScratchEnv), EnvScratch e → EnvScratch (ds.foldl f e) := by
    intro f hf ds
    induction ds with
    | nil => exact fun _ he => he
    | cons d ds ih => exact fun e he => ih _ (hf e d he)
  have hbind : ∀ (e : ScratchEnv) (dn v : String), EnvScratch e →
      fuseReloadScratches.contains dn = true → EnvScratch (scratchBind e dn v) := by
    intro e dn v he hc p hp
    simp only [scratchBind, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simpa using hc
    · exact he p (List.mem_of_mem_filter hp)
  unfold scratchStep
  split
  · refine hfold _ ?_ _ _ h
    intro e d he
    cases d with
    | reg dn =>
      dsimp only
      by_cases hc : fuseReloadScratches.contains dn = true
      · rw [if_pos hc]
        split
        · split
          · exact hbind _ _ _ he hc
          · exact he.kill _
        · exact he.kill _
      · rw [if_neg hc]; exact he
    | _ => exact he
  · exact h

theorem EnvScratch.foldl {env : ScratchEnv} (h : EnvScratch env) (xs : Lcmd) :
    EnvScratch (xs.foldl scratchStep env) := by
  induction xs generalizing env with
  | nil => exact h
  | cons i xs ih => exact ih (h.step i)

/-- **The fusion on a body with one multiply site.** In the looped-body mode, a body
    that carries exactly one low `MUL` followed, after a run without multiply sites,
    by a `MULXHI` on the same multiplicand, with register operands, a high
    destination other than `RDX` and a multiplicand that is neither `RDX` nor a
    reload scratch, keeps the low `MUL` and replaces the `MULXHI` by the save of
    `RDX`, the pin of the other factor, the two-output `MULX` and the restore of
    `RDX`; every other instruction passes through. -/
theorem fuseMulHiBody_oneSite (xs ys zs : Lcmd) (ii jj : Nat) (d opn s1 s2 hd hopn h1 : String)
    (hxs : ∀ i ∈ xs, NoMulSite i) (hys : ∀ i ∈ ys, NoMulSite i) (hzs : ∀ i ∈ zs, NoMulSite i)
    (hlo : isLowMulMnem opn = true) (hnlo : isLowMulMnem hopn = false)
    (hhi : isMulHiMnem hopn = true) (hs2 : s2 ∉ fuseReloadScratches)
    (hhd : (LOperand.reg hd).isSpill = false) (hhdR : (hd == "RDX") = false)
    (hs2S : (LOperand.reg s2).isSpill = false) (hs2R : (s2 == "RDX") = false)
    (hdS : (LOperand.reg d).isSpill = false) :
    fuseMulHiBody (xs ++ ⟨ii, .Lopn [.reg d] opn [.reg s1, .reg s2]⟩
        :: (ys ++ ⟨jj, .Lopn [.reg hd] hopn [.reg h1, .reg s2]⟩ :: zs)) true
      = xs ++ ⟨ii, .Lopn [.reg d] opn [.reg s1, .reg s2]⟩
        :: (ys ++ ⟨jj, .Lopn [.reg "R15"] "MOVQ" [.reg "RDX"]⟩
          :: ⟨jj, .Lopn [.reg "RDX"] "MOV:64" [.reg h1]⟩
          :: ⟨jj, .Lopn [.reg d, .reg hd] "MULX" [.reg s2]⟩
          :: ((if (d != "RDX") = true then [⟨jj, .Lopn [.reg "RDX"] "MOVQ" [.reg "R15"]⟩]
                else []) ++ zs)) := by
  have he0 : EnvScratch [] := fun _ h => absurd h (List.not_mem_nil)
  unfold fuseMulHiBody
  rw [fuseMulHiAux_append_noSite _ _ xs _ hxs, fuseMulHiAux_cons_lowMul _ _ _ _ _ _ _ s2 _ hlo
    (by simpa using hs2),
    fuseMulHiAux_append_noSite _ _ ys _ hys]
  have hE1 := (he0.foldl xs)
  have hE2 := (hE1.step ⟨ii, .Lopn [.reg d] opn [.reg s1, .reg s2]⟩).foldl ys
  rw [scratchResolve_of_envScratch hE1 hs2,
    fuseMulHiAux_cons_mulHi_saveRdx _ _ [] [] d s2 _ _ _ _ _ _ hnlo hhi
      (by rw [scratchResolve_of_envScratch hE2 hs2]; simp [List.span, List.span.loop])
      hhd hhdR hs2S hs2R hdS,
    fuseMulHiAux_noSite _ _ zs hzs]

end Fuser

/-! ## 5. Decoding a body with list-valued shapes -/

section Decode

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemLoop (nodeLayout guardedLayout)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow (XLoop XLoop.cmpInstr)

set_option genSizeOfSpec false in
/-- What one body instruction decodes to, as a list: a single shape (nothing, a
    straight-line instruction or a branch), or a run of straight-line instructions
    whose byte pieces concatenate to the instruction's bytes. -/
inductive DShape where
  | one (sh : Shape)
  | ops (pcs : List (List (BitVec 8) × JInstr 64))

/-- An instruction has a list-valued shape: a single shape as `ShapeOK`, or a run
    of pieces that each decode, in front of every continuation, to their
    instruction, whose concatenation is the instruction's bytes under every
    resolver, at an instruction that defines no label. -/
def DShapeOK (P : Params) (i : LinstrR) : DShape → Prop
  | .one sh => ShapeOK P i sh
  | .ops pcs => labelOf i = none
      ∧ (∀ d, encodeLinstrR P.frame P.spillW d i P.qsaveB = pcs.flatMap Prod.fst)
      ∧ ∀ p ∈ pcs, ItemOK ⟨p.1, some (.op p.2), none, none, none⟩

/-- The items of one instruction laid out at offset `off`. -/
def dItems (P : Params) (off : Nat) (instr : Linstr) : DShape → List Item
  | .one sh =>
      [{ bytes := P.encAt off instr.li_i, dec := sh.dec (P.dispAt off instr.li_i),
         label := labelOf instr.li_i, target := sh.target }]
  | .ops pcs => pcs.map (fun p => { bytes := p.1, dec := some (.op p.2) })

/-- The item of an instruction with a single shape, laid out at offset `off`. -/
def oneItem (P : Params) (off : Nat) (instr : Linstr) (sh : Shape) : Item :=
  { bytes := P.encAt off instr.li_i, dec := sh.dec (P.dispAt off instr.li_i),
    label := labelOf instr.li_i, target := sh.target }

theorem dItems_one (P : Params) (off : Nat) (instr : Linstr) (sh : Shape) :
    dItems P off instr (.one sh) = [oneItem P off instr sh] := rfl

/-- The item list of a body with list-valued shapes, laid out from offset `off`. -/
def itemsFromL (P : Params) : Nat → Lcmd → List DShape → List Item
  | off, instr :: body, sh :: shs =>
      dItems P off instr sh ++ itemsFromL P (off + P.lenAt off instr.li_i) body shs
  | _, _, _ => []

theorem itemBytes_dItems (P : Params) (off : Nat) (instr : Linstr) (sh : DShape)
    (h : DShapeOK P instr.li_i sh) :
    itemBytes (dItems P off instr sh) = P.encAt off instr.li_i := by
  cases sh with
  | one sh => simp [dItems, itemBytes]
  | ops pcs =>
    obtain ⟨_, hb, _⟩ := h
    rw [Params.encAt, hb]
    simp [dItems, itemBytes, List.flatMap_map]

theorem dItems_ok (P : Params) (off : Nat) (instr : Linstr) (sh : DShape)
    (h : DShapeOK P instr.li_i sh) : ∀ it ∈ dItems P off instr sh, ItemOK it := by
  cases sh with
  | one sh =>
    intro it hit
    simp only [dItems, List.mem_singleton] at hit
    subst hit
    exact h _
  | ops pcs =>
    intro it hit
    simp only [dItems, List.mem_map] at hit
    obtain ⟨p, hp, rfl⟩ := hit
    exact h.2.2 p hp

theorem itemBytes_itemsFromL (P : Params) {body : Lcmd} {shs : List DShape}
    (h : List.Forall₂ (fun instr sh => DShapeOK P instr.li_i sh) body shs) :
    ∀ off, itemBytes (itemsFromL P off body shs) = encodeFrom P off body := by
  induction h with
  | nil => intro off; rfl
  | cons hab _ ih =>
    intro off
    simp only [itemsFromL, encodeFrom, itemBytes, List.flatMap_append]
    rw [← itemBytes, ← itemBytes, itemBytes_dItems _ _ _ _ hab, ih]

theorem itemsFromL_ok (P : Params) {body : Lcmd} {shs : List DShape}
    (h : List.Forall₂ (fun instr sh => DShapeOK P instr.li_i sh) body shs) :
    ∀ off, ∀ it ∈ itemsFromL P off body shs, ItemOK it := by
  induction h with
  | nil => intro off it hit; cases hit
  | cons hab _ ih =>
    intro off it hit
    simp only [itemsFromL, List.mem_append] at hit
    rcases hit with hit | hit
    · exact dItems_ok _ _ _ _ hab it hit
    · exact ih _ it hit

/-- The item list of a function that saves no register by `push`: the frame
    `leaq`, the body items, the closing `leaq` and `ret`. -/
def fundefItemsL (body : Lcmd) (shs : List DShape) : List Item :=
  mkLea (-(Int.ofNat (Params.ofBody body).frame))
    :: (itemsFromL (Params.ofBody body) 0 body shs
      ++ [mkLea (Int.ofNat (Params.ofBody body).frame), mkRet])

/-- **Function round trip with list-valued shapes.** A body that saves no register
    by `push`, with a non-zero frame in `rel32` range, whose instructions have
    list-valued shapes and whose branches are well formed, decodes to the program
    its item list denotes. Generalises `LprogBytesDecode.decodeLprog_encodeLcmd`
    from one decoded instruction per body instruction to a run of them. -/
theorem decodeLprog_encodeLfundefBytes_shapes (body : Lcmd) (shs : List DShape)
    (hsaves : calleeSavedToSave body = [])
    (hF0 : (Int.ofNat (Params.ofBody body).frame) ≠ 0)
    (hF : dispOk32 (Int.ofNat (Params.ofBody body).frame) = true)
    (hF' : dispOk32 (-(Int.ofNat (Params.ofBody body).frame)) = true)
    (h : List.Forall₂ (fun instr sh => DShapeOK (Params.ofBody body) instr.li_i sh) body shs)
    (hbr : branchOK (fundefItemsL body shs) 0 (fundefItemsL body shs) = true) :
    decodeLprog (encodeLfundefBytes body)
      = expectedFrom (fundefItemsL body shs) (fundefItemsL body shs) := by
  have hbytes : encodeLfundefBytes body = itemBytes (fundefItemsL body shs) := by
    rw [encodeLfundefBytes_eq body hsaves, fundefBytes, fundefItemsL, itemBytes,
      List.flatMap_cons, List.flatMap_append, ← itemBytes, itemBytes_itemsFromL _ h 0]
    show _ = encLeaRspFrame _ ++ (encodeFrom _ 0 body
      ++ (encLeaRspFrame _ ++ (mkRet.bytes ++ [])))
    simp only [List.append_nil, List.append_assoc]
    rfl
  rw [hbytes]
  refine decodeLprog_items _ ?_ hbr
  intro it hit
  simp only [fundefItemsL, List.mem_cons, List.mem_append, List.not_mem_nil,
    or_false] at hit
  rcases hit with rfl | hit | rfl | rfl
  · exact mkLea_ok _ (by simpa using hF0) hF'
  · exact itemsFromL_ok _ h 0 it hit
  · exact mkLea_ok _ hF0 hF
  · exact mkRet_ok

/-! ### Item lists of a guarded loop node -/

/-- Items that define no label, target no label, and decode to nothing or to a
    straight-line instruction. -/
def OpItems (xs : List Item) : Prop :=
  ∀ it ∈ xs, it.label = none ∧ it.target = none ∧ (it.dec = none ∨ ∃ i, it.dec = some (.op i))

/-- The straight-line instructions an item list decodes to. -/
def opsOf (xs : List Item) : List (JInstr 64) :=
  xs.filterMap (fun it => match it.dec with | some (.op i) => some i | _ => none)

theorem OpItems.append {xs ys : List Item} (hx : OpItems xs) (hy : OpItems ys) :
    OpItems (xs ++ ys) := by
  intro it hit
  rcases List.mem_append.mp hit with h | h
  · exact hx it h
  · exact hy it h

theorem OpItems.of_cons {x : Item} {xs : List Item} (h : OpItems (x :: xs)) : OpItems xs :=
  fun it hit => h it (List.mem_cons_of_mem _ hit)

theorem decCount_opItems {xs : List Item} (h : OpItems xs) : decCount xs = (opsOf xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨_, _, hd⟩ := h x (by simp)
    rcases hd with hd | ⟨i, hd⟩
    · have := ih h.of_cons
      simp only [opsOf] at this
      simp [decCount, opsOf, hd, this]
    · have := ih h.of_cons
      simp only [opsOf] at this
      simp [decCount, opsOf, hd, this]; omega

theorem decCount_append (xs ys : List Item) :
    decCount (xs ++ ys) = decCount xs + decCount ys := by
  induction xs with
  | nil => simp [decCount]
  | cons x xs ih => simp only [List.cons_append, decCount, ih]; omega

/-- A label search behind items that do not define the label continues past them,
    with the instruction count and the offset advanced. -/
theorem labelPos_append_of_ne (l : LLabel) (xs ys : List Item)
    (h : ∀ it ∈ xs, it.label ≠ some l) (j off : Nat) :
    labelPos l j off (xs ++ ys)
      = labelPos l (j + decCount xs) (off + (itemBytes xs).length) ys := by
  induction xs generalizing j off with
  | nil => simp [decCount, itemBytes]
  | cons x xs ih =>
    rw [List.cons_append, labelPos, if_neg (h x (by simp)),
      ih (fun it hit => h it (List.mem_cons_of_mem _ hit))]
    congr 1
    · simp only [decCount]; split <;> omega
    · simp [itemBytes, List.flatMap_cons]; omega

/-- The expected program of straight-line items followed by more items. -/
theorem expectedFrom_opItems_append (all xs ys : List Item) (h : OpItems xs) :
    expectedFrom all (xs ++ ys) = (expectedFrom all ys).map ((opsOf xs).map .op ++ ·) := by
  induction xs with
  | nil => simp [opsOf]
  | cons x xs ih =>
    obtain ⟨_, _, hd⟩ := h x (by simp)
    rw [List.cons_append, expectedFrom]
    rcases hd with hd | ⟨i, hd⟩
    · rw [hd, ih h.of_cons]; simp [opsOf, hd]
    · rw [hd, ih h.of_cons]; simp [opsOf, hd, Option.map_map, Function.comp_def]

theorem OpItems.noLabel {xs : List Item} (h : OpItems xs) (l : LLabel) :
    ∀ it ∈ xs, it.label ≠ some l := fun it hit => by simp [(h it hit).1]

/-- **The program of a guarded loop node's item list.** Straight-line items `A`,
    the guard compare and the skip branch to `endL`, the label `top`, straight-line
    items `B`, the back-edge compare and the branch to `top`, the label `endL`,
    straight-line items `C` and `ret` denote `nodeLayout (opsOf A) l (opsOf C)` for
    the loop `l` on `ctr` with body `opsOf B`. -/
theorem expectedFrom_node (A B C : List Item) (c1 j1 lt c2 j2 le rt : Item)
    (top endL : LLabel) (ctr : String) (d1 d2 : Int)
    (hA : OpItems A) (hB : OpItems B) (hC : OpItems C)
    (hc1 : c1.dec = some (.op (.cmp ctr (.imm 0)))) (hc1l : c1.label = none)
    (hj1 : j1.dec = some (.jcc 4 d1)) (hj1t : j1.target = some endL) (hj1l : j1.label = none)
    (hlt : lt.dec = none) (hltl : lt.label = some top)
    (hc2 : c2.dec = some (.op (.cmp ctr (.imm 0)))) (hc2l : c2.label = none)
    (hj2 : j2.dec = some (.jcc 5 d2)) (hj2t : j2.target = some top) (hj2l : j2.label = none)
    (hle : le.dec = none) (hlel : le.label = some endL)
    (hrt : rt.dec = some .ret) (htop : top ≠ endL) :
    expectedFrom (A ++ c1 :: j1 :: lt :: (B ++ c2 :: j2 :: le :: (C ++ [rt])))
        (A ++ c1 :: j1 :: lt :: (B ++ c2 :: j2 :: le :: (C ++ [rt])))
      = some (nodeLayout (opsOf A) ⟨top, ctr, opsOf B⟩ (opsOf C)) := by
  set all := A ++ c1 :: j1 :: lt :: (B ++ c2 :: j2 :: le :: (C ++ [rt])) with hall
  have hpt : ∃ o, labelPos top 0 0 all = some ((opsOf A).length + 2, o) := by
    rw [hall, labelPos_append_of_ne _ _ _ (hA.noLabel _), decCount_opItems hA]
    simp [labelPos, hc1l, hj1l, hltl, hc1, hj1]
  have hpe : ∃ o, labelPos endL 0 0 all
      = some ((opsOf A).length + (opsOf B).length + 4, o) := by
    rw [hall, labelPos_append_of_ne _ _ _ (hA.noLabel _), decCount_opItems hA]
    simp only [labelPos, hc1l, hj1l, hltl, reduceCtorEq, if_false, hc1, hj1, hlt,
      Option.isSome_some, Option.isSome_none, if_true, Option.some.injEq, htop,
      Bool.false_eq_true]
    rw [labelPos_append_of_ne _ _ _ (hB.noLabel _), decCount_opItems hB]
    simp [labelPos, hc2l, hj2l, hlel, hc2, hj2]
    omega
  obtain ⟨ot, hot⟩ := hpt
  obtain ⟨oe, hoe⟩ := hpe
  conv_lhs => arg 2; rw [hall]
  rw [expectedFrom_opItems_append _ _ _ hA]
  simp only [expectedFrom, hc1, hj1, hj1t, hlt, Option.bind_some, hoe]
  rw [expectedFrom_opItems_append _ _ _ hB]
  simp only [expectedFrom, hj2, hj2t, hc2, hle, Option.bind_some, hot]
  rw [expectedFrom_opItems_append _ _ _ hC]
  simp [expectedFrom, hrt, nodeLayout, guardedLayout, XLoop.cmpInstr, List.map_append]

/-- A list-valued shape that decodes to straight-line instructions only. -/
def DShape.Straight : DShape → Prop
  | .one .skip => True
  | .one (.op _) => True
  | .one (.jcc _ _) => False
  | .one (.call _) => False
  | .ops _ => True

/-- The straight-line instructions of a list-valued shape. -/
def DShape.ops' : DShape → List (JInstr 64)
  | .one (.op i) => [i]
  | .ops pcs => pcs.map Prod.snd
  | _ => []

/-- The byte length the encoder gives a run of instructions from offset `off`. -/
def lenFrom (P : Params) : Nat → Lcmd → Nat
  | _, [] => 0
  | off, i :: rest => P.lenAt off i.li_i + lenFrom P (off + P.lenAt off i.li_i) rest

theorem itemsFromL_append (P : Params) (b1 b2 : Lcmd) (s1 s2 : List DShape)
    (hl : b1.length = s1.length) (off : Nat) :
    itemsFromL P off (b1 ++ b2) (s1 ++ s2)
      = itemsFromL P off b1 s1 ++ itemsFromL P (off + lenFrom P off b1) b2 s2 := by
  induction b1 generalizing s1 off with
  | nil =>
    cases s1 with
    | nil => simp [itemsFromL, lenFrom]
    | cons _ _ => simp at hl
  | cons i b1 ih =>
    cases s1 with
    | nil => simp at hl
    | cons sh s1 =>
      simp only [List.cons_append, itemsFromL, lenFrom, List.append_assoc]
      rw [ih s1 (by simpa using hl), Nat.add_assoc]

theorem itemsFromL_opItems (P : Params) {b : Lcmd} {s : List DShape}
    (h : List.Forall₂ (fun instr sh => DShapeOK P instr.li_i sh ∧ sh.Straight
      ∧ labelOf instr.li_i = none) b s) (off : Nat) :
    OpItems (itemsFromL P off b s) ∧ opsOf (itemsFromL P off b s) = s.flatMap DShape.ops' := by
  induction h generalizing off with
  | nil => exact ⟨fun _ h => absurd h List.not_mem_nil, rfl⟩
  | @cons i sh b s hab _ ih =>
    obtain ⟨ihO, ihE⟩ := ih (off + P.lenAt off i.li_i)
    obtain ⟨_, hst, hlab⟩ := hab
    have hd : OpItems (dItems P off i sh) ∧ opsOf (dItems P off i sh) = sh.ops' := by
      cases sh with
      | one sh =>
        cases sh with
        | skip => exact ⟨by simp [OpItems, dItems, hlab, Shape.dec, Shape.target], by
            simp [opsOf, dItems, Shape.dec, DShape.ops']⟩
        | op x => exact ⟨by simp [OpItems, dItems, hlab, Shape.dec, Shape.target], by
            simp [opsOf, dItems, Shape.dec, DShape.ops']⟩
        | jcc _ _ => exact absurd hst id
        | call _ => exact absurd hst id
      | ops pcs =>
        refine ⟨?_, ?_⟩
        · intro it hit
          simp only [dItems, List.mem_map] at hit
          obtain ⟨p, _, rfl⟩ := hit
          exact ⟨rfl, rfl, Or.inr ⟨_, rfl⟩⟩
        · simp [opsOf, dItems, DShape.ops', List.filterMap_map]
    simp only [itemsFromL, List.flatMap_cons]
    refine ⟨hd.1.append ihO, ?_⟩
    rw [opsOf, List.filterMap_append, ← opsOf, ← opsOf, hd.2, ihE]

theorem itemsFromL_cons (P : Params) (off : Nat) (i : Linstr) (b : Lcmd) (sh : DShape)
    (s : List DShape) :
    ∃ o, itemsFromL P off (i :: b) (sh :: s) = dItems P off i sh ++ itemsFromL P o b s :=
  ⟨_, rfl⟩

theorem itemsFromL_append' (P : Params) (b1 b2 : Lcmd) (s1 s2 : List DShape)
    (hl : b1.length = s1.length) (off : Nat) :
    ∃ o, itemsFromL P off (b1 ++ b2) (s1 ++ s2) = itemsFromL P off b1 s1 ++ itemsFromL P o b2 s2 :=
  ⟨_, itemsFromL_append P b1 b2 s1 s2 hl off⟩

/-- The items of a guarded loop node body split at the guard, the loop body, the
    back-edge and the suffix, at some offsets. -/
theorem itemsFromL_node (P : Params) (P1 L P2 : Lcmd) (s1 sL s2 : List DShape)
    (g1 g2 g3 b1 b2 b3 r : Linstr) (x1 x2 x3 y1 y2 y3 z : DShape)
    (l1 : P1.length = s1.length) (lL : L.length = sL.length) (l2 : P2.length = s2.length) :
    ∃ o1 o2 o3 o4 o5 o6 o7 o8 o9,
      itemsFromL P 0 (P1 ++ g1 :: g2 :: g3 :: (L ++ b1 :: b2 :: b3 :: (P2 ++ [r])))
          (s1 ++ x1 :: x2 :: x3 :: (sL ++ y1 :: y2 :: y3 :: (s2 ++ [z])))
        = itemsFromL P 0 P1 s1 ++ (dItems P o1 g1 x1 ++ (dItems P o2 g2 x2 ++ (dItems P o3 g3 x3
          ++ (itemsFromL P o4 L sL ++ (dItems P o5 b1 y1 ++ (dItems P o6 b2 y2
          ++ (dItems P o7 b3 y3 ++ (itemsFromL P o8 P2 s2 ++ dItems P o9 r z)))))))) := by
  obtain ⟨o0, e0⟩ := itemsFromL_append' P P1 _ s1 _ l1 0
  obtain ⟨o1', e1⟩ := itemsFromL_cons P o0 g1 _ x1 _
  obtain ⟨o2', e2⟩ := itemsFromL_cons P o1' g2 _ x2 _
  obtain ⟨o3', e3⟩ := itemsFromL_cons P o2' g3 _ x3 _
  obtain ⟨o4', e4⟩ := itemsFromL_append' P L _ sL _ lL o3'
  obtain ⟨o5', e5⟩ := itemsFromL_cons P o4' b1 _ y1 _
  obtain ⟨o6', e6⟩ := itemsFromL_cons P o5' b2 _ y2 _
  obtain ⟨o7', e7⟩ := itemsFromL_cons P o6' b3 _ y3 _
  obtain ⟨o8', e8⟩ := itemsFromL_append' P P2 [r] s2 [z] l2 o7'
  obtain ⟨o9', e9⟩ := itemsFromL_cons P o8' r [] z []
  refine ⟨o0, o1', o2', o3', o4', o5', o6', o7', o8', ?_⟩
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9]
  simp [itemsFromL]

/-- The frame `leaq disp(%rsp), %rsp` as a decoded instruction. -/
def leaFrame (disp : Int) : JInstr 64 := .lea "%rsp" "%rsp" "%rsp" 0 disp

/-- **The decoded bytes of a guarded loop node.** A body that saves no register by
    `push`, with a non-zero frame in `rel32` range, laid out as a straight-line
    prefix `P1`, the guard `CMP ctr,#0 ; Lcond Z endL ; Llabel top`, a straight-line
    loop body `L`, the back-edge `CMP ctr,#0 ; Lcond NZ top ; Llabel endL`, a
    straight-line suffix `P2` and the return, whose instructions have list-valued
    shapes and whose branches are well formed, decodes to the node layout: the frame
    `leaq` and the decoded prefix, the guarded loop over the decoded loop body, and
    the decoded suffix with the closing `leaq`. -/
theorem decodeLprog_node (body : Lcmd) (shs : List DShape) (P1 L P2 : Lcmd)
    (s1 sL s2 : List DShape) (g1 g2 g3 b1 b2 b3 r : Linstr)
    (top endL : LLabel) (ctr : String) (k1 k2 : LabelKind)
    (hbody : body = P1 ++ g1 :: g2 :: g3 :: (L ++ b1 :: b2 :: b3 :: (P2 ++ [r])))
    (hshs : shs = s1 ++ .one (.op (.cmp ctr (.imm 0))) :: .one (.jcc 4 endL) :: .one .skip
      :: (sL ++ .one (.op (.cmp ctr (.imm 0))) :: .one (.jcc 5 top) :: .one .skip
        :: (s2 ++ [.one .skip])))
    (h1 : List.Forall₂ (fun instr sh => DShapeOK (Params.ofBody body) instr.li_i sh
      ∧ sh.Straight ∧ labelOf instr.li_i = none) P1 s1)
    (hL : List.Forall₂ (fun instr sh => DShapeOK (Params.ofBody body) instr.li_i sh
      ∧ sh.Straight ∧ labelOf instr.li_i = none) L sL)
    (h2 : List.Forall₂ (fun instr sh => DShapeOK (Params.ofBody body) instr.li_i sh
      ∧ sh.Straight ∧ labelOf instr.li_i = none) P2 s2)
    (hg1 : DShapeOK (Params.ofBody body) g1.li_i (.one (.op (.cmp ctr (.imm 0)))))
    (hg1l : labelOf g1.li_i = none)
    (hg2 : DShapeOK (Params.ofBody body) g2.li_i (.one (.jcc 4 endL)))
    (hg2l : labelOf g2.li_i = none)
    (hg3 : g3.li_i = .Llabel k1 top)
    (hb1 : DShapeOK (Params.ofBody body) b1.li_i (.one (.op (.cmp ctr (.imm 0)))))
    (hb1l : labelOf b1.li_i = none)
    (hb2 : DShapeOK (Params.ofBody body) b2.li_i (.one (.jcc 5 top)))
    (hb2l : labelOf b2.li_i = none)
    (hb3 : b3.li_i = .Llabel k2 endL) (hr : r.li_i = .Lret) (htop : top ≠ endL)
    (hsaves : calleeSavedToSave body = [])
    (hF0 : (Int.ofNat (Params.ofBody body).frame) ≠ 0)
    (hF : dispOk32 (Int.ofNat (Params.ofBody body).frame) = true)
    (hF' : dispOk32 (-(Int.ofNat (Params.ofBody body).frame)) = true)
    (hbr : branchOK (fundefItemsL body shs) 0 (fundefItemsL body shs) = true) :
    decodeLprog (encodeLfundefBytes body)
      = some (nodeLayout
          (leaFrame (-(Int.ofNat (Params.ofBody body).frame)) :: s1.flatMap DShape.ops')
          ⟨top, ctr, sL.flatMap DShape.ops'⟩
          (s2.flatMap DShape.ops' ++ [leaFrame (Int.ofNat (Params.ofBody body).frame)])) := by
  set P := Params.ofBody body with hP
  have hlab3 : ∀ PP, DShapeOK PP g3.li_i (.one .skip) := fun PP => by
    rw [hg3]; exact shapeOK_label PP _ _
  have hlabE : ∀ PP, DShapeOK PP b3.li_i (.one .skip) := fun PP => by
    rw [hb3]; exact shapeOK_label PP _ _
  have hret : ∀ PP, DShapeOK PP r.li_i (.one .skip) := fun PP => by
    rw [hr]; exact shapeOK_ret PP
  have hall : List.Forall₂ (fun instr sh => DShapeOK P instr.li_i sh) body shs := by
    rw [hbody, hshs]
    refine List.rel_append (h1.imp fun _ _ h => h.1) ?_
    refine .cons hg1 (.cons hg2 (.cons (hlab3 P) ?_))
    refine List.rel_append (hL.imp fun _ _ h => h.1) ?_
    refine .cons hb1 (.cons hb2 (.cons (hlabE P) ?_))
    exact List.rel_append (h2.imp fun _ _ h => h.1) (.cons (hret P) .nil)
  rw [decodeLprog_encodeLfundefBytes_shapes body _ hsaves hF0 hF hF' hall hbr, fundefItemsL]
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, e⟩ := itemsFromL_node P P1 L P2 s1 sL s2
    g1 g2 g3 b1 b2 b3 r _ _ _ _ _ _ _ h1.length_eq hL.length_eq h2.length_eq
  rw [← hP]
  conv_lhs => rw [hbody, hshs, e]
  obtain ⟨hA, eA⟩ := itemsFromL_opItems P h1 0
  obtain ⟨hB, eB⟩ := itemsFromL_opItems P hL o4
  obtain ⟨hC, eC⟩ := itemsFromL_opItems P h2 o8
  have hlea : ∀ d : Int, OpItems [mkLea d] := fun d it hit => by
    rw [List.mem_singleton] at hit; subst hit; exact ⟨rfl, rfl, Or.inr ⟨_, rfl⟩⟩
  have hrI : OpItems (dItems P o9 r (.one .skip)) := by
    intro it hit
    simp only [dItems, List.mem_singleton] at hit
    subst hit
    exact ⟨by simp [hr, labelOf], rfl, Or.inl rfl⟩
  have hA' : OpItems (mkLea (-(Int.ofNat P.frame)) :: itemsFromL P 0 P1 s1) :=
    (hlea _).append hA
  have key := expectedFrom_node (mkLea (-(Int.ofNat P.frame)) :: itemsFromL P 0 P1 s1)
    (itemsFromL P o4 L sL)
    (itemsFromL P o8 P2 s2 ++ (dItems P o9 r (.one .skip) ++ [mkLea (Int.ofNat P.frame)]))
    (oneItem P o1 g1 (.op (.cmp ctr (.imm 0)))) (oneItem P o2 g2 (.jcc 4 endL))
    (oneItem P o3 g3 .skip) (oneItem P o5 b1 (.op (.cmp ctr (.imm 0))))
    (oneItem P o6 b2 (.jcc 5 top)) (oneItem P o7 b3 .skip) mkRet top endL ctr _ _
    hA' hB (hC.append (hrI.append (hlea _)))
    rfl hg1l rfl rfl hg2l rfl (by simp [oneItem, hg3, labelOf])
    rfl hb1l rfl rfl hb2l rfl (by simp [oneItem, hb3, labelOf]) rfl htop
  simp only [dItems_one, List.cons_append, List.nil_append, List.append_assoc] at key ⊢
  rw [key]
  have hoa : ∀ xs ys : List Item, opsOf (xs ++ ys) = opsOf xs ++ opsOf ys := fun xs ys => by
    simp [opsOf, List.filterMap_append]
  have hoc : ∀ (d : Int) (xs : List Item), opsOf (mkLea d :: xs) = leaFrame d :: opsOf xs :=
    fun _ _ => rfl
  have hot : opsOf [oneItem P o9 r .skip, mkLea (Int.ofNat P.frame)]
      = [leaFrame (Int.ofNat P.frame)] := rfl
  rw [hoa, hoc, hot, eA, eB, eC]

end Decode

/-! ## 6. At `mpn_mul_1` -/

section Mul1

open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontDenote (mul1Update mul1Update_eq)

/-- The front-compiled `mpn_mul_1` is the single-loop program over its limb body. -/
theorem mul1RtProgOpt_eq :
    mul1RtProgOpt () = some (singleLoop mul1Update mul1Count mul1Init mul1Invs) := by
  unfold mul1RtProgOpt Dialects.TranslateDialectRuntimeLoop.rolledForLoopNRt
    Dialects.TranslateDialectRuntimeLoop.rolledForLoopNRtCont
  erw [mul1Update_eq]

end Mul1

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
