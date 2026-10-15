/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard

@[expose] public section

set_option autoImplicit false

/-!
# Lifting exported `Lcmd` streams to the typed instruction list `LinstrRM`

The typed machines over `LstateM` (`lsemFuelMemL`, `lsemFuelMemF`) run lists of
`LinstrRM = LinstrR × MemTag`: the emitted wire paired with the typed-environment
descriptor (`MemTag`) that carries the array shape `(w, n)` of a
`LOADIDX`/`STOREIDX` and the width of a cast. The export `comLToBody` produces an
untyped `Lcmd`. This module supplies the lift.

* `liftLcmdRM tag c` — the lift of an `Lcmd` under a descriptor oracle `tag`; its
  wire projection is the `Lcmd`'s instruction stream (`liftLcmdRM_wire`).
* `memTagOfOp` — the descriptor a `JasminOp` binding carries: the array shape of
  a `stackLoad`/`stackStore`, the target width of a `castW`, `.reg none`
  otherwise. It is the descriptor `straightOpsMem` attaches
  (`straightOpsMem_snd_memTagOfOp`).
* `loopBodyWalkNM` — the typed loop-body walk: the wire of `loopBodyWalkN`
  (`loopBodyWalkNM_wire`) with each binding tagged by `memTagOfOp`.
* `forLoopLcmdNRtRM` — the typed image of the runtime-count loop node
  `forLoopLcmdNRt`, stated as the three seed moves followed by the zero-trip
  guarded flag loop `guardedFlagLoopLinstrRM` over the body walk, the feedback
  move, the index/counter updates and the invariant touches. Its wire projection
  is `forLoopLcmdNRt` instruction for instruction (`forLoopLcmdNRtRM_wire`), so
  the typed program the flag machine runs is the export's own stream.
* `forLoopLcmdNRtRM_loopBody_isLopn` — every instruction of the looped segment
  is an `Lopn`, the side condition of the flag-machine loop theorems.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard

/-! ## 1. The oracle lift of an `Lcmd` -/

/-- The lift of one exported instruction under a descriptor oracle: the wire is
    the instruction's `li_i`, the descriptor is `tag` of the instruction. -/
def liftLinstrRM (tag : Linstr → MemTag) (i : Linstr) : LinstrRM := (i.li_i, tag i)

/-- The lift of an exported `Lcmd` under a descriptor oracle. -/
def liftLcmdRM (tag : Linstr → MemTag) (c : Lcmd) : List LinstrRM :=
  c.map (liftLinstrRM tag)

/-- The register-binding oracle: every instruction carries `.reg none`. -/
def regTag : Linstr → MemTag := fun _ => MemTag.reg none

/-- The wire projection of the lift is the exported instruction stream. -/
theorem liftLcmdRM_wire (tag : Linstr → MemTag) (c : Lcmd) :
    (liftLcmdRM tag c).map Prod.fst = c.map Linstr.li_i := by
  simp [liftLcmdRM, liftLinstrRM]

@[simp] theorem liftLcmdRM_nil (tag : Linstr → MemTag) : liftLcmdRM tag [] = [] := rfl

@[simp] theorem liftLcmdRM_cons (tag : Linstr → MemTag) (i : Linstr) (c : Lcmd) :
    liftLcmdRM tag (i :: c) = (i.li_i, tag i) :: liftLcmdRM tag c := rfl

@[simp] theorem liftLcmdRM_append (tag : Linstr → MemTag) (c₁ c₂ : Lcmd) :
    liftLcmdRM tag (c₁ ++ c₂) = liftLcmdRM tag c₁ ++ liftLcmdRM tag c₂ := by
  simp [liftLcmdRM]

@[simp] theorem liftLcmdRM_length (tag : Linstr → MemTag) (c : Lcmd) :
    (liftLcmdRM tag c).length = c.length := by
  simp [liftLcmdRM]

/-- An exported instruction whose wire is an `Lopn` lifts to an `IsLopn`
    instruction, whatever its descriptor. -/
theorem liftLinstrRM_isLopn (tag : Linstr → MemTag) (i : Linstr)
    (h : ∃ d o s, i.li_i = LinstrR.Lopn d o s) : IsLopn (liftLinstrRM tag i) := h

/-! ## 2. The descriptor of a binding -/

/-- The typed-environment descriptor of a `JasminOp` binding: the array shape of
    a `stackLoad`/`stackStore`/`stackZero`/`stackStoreImm`, the target width of a `castW`, the descriptor
    `regConstDescr w` of a `regConst w`, and `.reg none` for every other op. -/
def memTagOfOp : JasminOp → MemTag
  | .stackLoad w n => .load w n
  | .stackStore w n => .store w n
  | .stackZero w n => .zero w n
  | .stackStoreImm w n _ => .storeImm w n
  | .castW _ w' => .reg (some w')
  | .regConst w _ => .reg (JasminLsemCast.regConstDescr w)
  | _ => .reg none

/-- The descriptors of a `Com`'s bindings, in program order. -/
def comMemTags : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → List MemTag
  | _, _, .ret _ => []
  | _, _, .var e body => memTagOfOp e.op :: comMemTags body

/-- `straightOpsMem` attaches `memTagOfOp` to every binding. -/
theorem straightOpsMem_tags (nArgs : Nat) {Γ : Ctxt jasminDialect}
    {t : JasminTy} (com : Com jasminDialect Γ t) (curDepth : Nat) :
    (straightOpsMem nArgs com curDepth).map Prod.snd = comMemTags com := by
  induction com generalizing curDepth with
  | ret v => rfl
  | var e body ih =>
      simp only [straightOpsMem, List.map_cons, ih, comMemTags]
      congr 1
      split <;> (try split) <;> simp_all [memTagOfOp]

/-- Every `opToLinstrR` image is an `Lopn`, so it lifts to an `IsLopn`
    instruction under any descriptor. -/
theorem opToLinstrR_isLopn (op : JasminOp) (dst : String) (srcs : List LOperand)
    (tag : MemTag) : IsLopn (opToLinstrR op dst srcs, tag) := by
  show ∃ d o s, opToLinstrR op dst srcs = LinstrR.Lopn d o s
  unfold opToLinstrR
  split <;> (repeat' (first | exact ⟨_, _, _, rfl⟩ | split | dsimp only))

/-! ## 3. The typed loop-body walk -/

/-- The typed loop-body walk: each binding emits the `loopBodyWalkN` wire
    `opToLinstrR e.op (loopReg d curDepth) (loopExprArgsN …)` paired with the
    binding's descriptor `memTagOfOp e.op`. -/
def loopBodyWalkNM (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (immSlotMap : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → List LinstrRM
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      (opToLinstrR e.op (loopReg d curDepth)
          (loopExprArgsN d accReg idxReg invRegs curDepth immSlotMap e), memTagOfOp e.op)
        :: loopBodyWalkNM d accReg idxReg invRegs immSlotMap body (curDepth + 1)

/-- **Wire tie of the typed walk.** The wire projection of `loopBodyWalkNM` is
    the instruction stream of `loopBodyWalkN`. -/
theorem loopBodyWalkNM_wire (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    (loopBodyWalkNM d accReg idxReg invRegs immSlotMap com curDepth).map Prod.fst
      = (loopBodyWalkN d accReg idxReg invRegs immSlotMap com curDepth).1.map
          Linstr.li_i := by
  induction com generalizing curDepth with
  | ret v => rfl
  | var e body ih =>
      simp only [loopBodyWalkNM, loopBodyWalkN, List.map_cons, ih]

/-- The typed walk has one instruction per binding, as `loopBodyWalkN`. -/
theorem loopBodyWalkNM_length (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    (loopBodyWalkNM d accReg idxReg invRegs immSlotMap com curDepth).length
      = (loopBodyWalkN d accReg idxReg invRegs immSlotMap com curDepth).1.length := by
  have h := congrArg List.length
    (loopBodyWalkNM_wire d accReg idxReg invRegs immSlotMap com curDepth)
  simpa using h

/-- Every instruction of the typed walk is an `Lopn`. -/
theorem loopBodyWalkNM_isLopn (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    ∀ i ∈ loopBodyWalkNM d accReg idxReg invRegs immSlotMap com curDepth, IsLopn i := by
  induction com generalizing curDepth with
  | ret v => intro i hi; simp [loopBodyWalkNM] at hi
  | var e body ih =>
      intro i hi
      simp only [loopBodyWalkNM, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact opToLinstrR_isLopn _ _ _ _
      · exact ih (curDepth + 1) i hi

/-! ## 4. The typed runtime-count loop node -/

/-- The invariant base register names of a loop node: the `.reg` entries of the
    resolved invariant operands (the `invRegs` of `forLoopLcmdNRt`). -/
def invRegsOf (invOps : List LOperand) : List String :=
  invOps.filterMap (fun o => match o with | .reg n => some n | _ => none)

/-- The three seed moves of the loop node: accumulator, index and counter. -/
def loopSeedsRM (d : Nat) (accReg : String) (initOp countOp : LOperand) :
    List LinstrRM :=
  [ (.Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp], MemTag.reg none)
  , (.Lopn [.reg (loopIdx d)] (withWidthTag 64 "MOV") [.imm 0], MemTag.reg none)
  , (.Lopn [.reg (loopCtr d)] (withWidthTag 64 "MOV") [countOp], MemTag.reg none) ]

/-- The feedback move `MOV acc, ret` (empty when the body returns in `acc`). -/
def loopFeedbackRM (accReg retReg : String) : List LinstrRM :=
  if retReg == accReg then []
  else [(.Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg retReg], MemTag.reg none)]

/-- The index advance and counter decrement `ADD Lidx,#1 ; SUB Lctr,#1`. -/
def loopAdvanceRM (d : Nat) : List LinstrRM :=
  [ (.Lopn [.reg (loopIdx d)] (withWidthTag 64 "ADD") [.reg (loopIdx d), .imm 1],
      MemTag.reg none)
  , (.Lopn [.reg (loopCtr d)] (withWidthTag 64 "SUB") [.reg (loopCtr d), .imm 1],
      MemTag.reg none) ]

/-- The invariant touches `CMP Lctr, inv` (one per invariant base register). -/
def loopTouchRM (d : Nat) (invRegs : List String) : List LinstrRM :=
  invRegs.map (fun r =>
    (.Lopn [.reg (loopCtr d)] (withWidthTag 64 "CMP") [.reg (loopCtr d), .reg r],
      MemTag.reg none))

/-- The looped segment of the node: the typed body walk, the feedback move, the
    index/counter updates and the invariant touches. -/
def forLoopBodyNRtRM (d : Nat) (accReg : String) {accTy : JasminTy}
    {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) : List LinstrRM :=
  loopBodyWalkNM d accReg (loopIdx d) (invRegsOf invOps) immSlotMap update
      (2 + invTys.length)
    ++ loopFeedbackRM accReg
        (loopBodyWalkN d accReg (loopIdx d) (invRegsOf invOps) immSlotMap update
          (2 + invTys.length)).2
    ++ loopAdvanceRM d
    ++ loopTouchRM d (invRegsOf invOps)

/-- **The typed image of the runtime-count loop node**: the seed moves, then the
    zero-trip guarded flag loop (`guardedFlagLoopLinstrRM`, top label `d`, skip
    label `d + 0x40000000`, counter `Lctr<d>`) over the looped segment. -/
def forLoopLcmdNRtRM (d : Nat) (accReg : String) (initOp countOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) : List LinstrRM :=
  loopSeedsRM d accReg initOp countOp
    ++ guardedFlagLoopLinstrRM d (d + 0x40000000) (loopCtr d)
        (forLoopBodyNRtRM d accReg update invOps immSlotMap)

/-- `forLoopLcmdNRt` with the body-walk pair projected rather than matched. -/
theorem forLoopLcmdNRt_unfold (d : Nat) (accReg : String) (initOp countOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) :
    forLoopLcmdNRt d accReg initOp countOp update invOps immSlotMap
      = let W := loopBodyWalkN d accReg (loopIdx d) (invRegsOf invOps) immSlotMap update
            (2 + invTys.length)
        [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
        , ⟨0, .Lopn [.reg (loopIdx d)] (withWidthTag 64 "MOV") [.imm 0]⟩
        , ⟨0, .Lopn [.reg (loopCtr d)] (withWidthTag 64 "MOV") [countOp]⟩
        , ⟨0, .Lopn [.reg (loopCtr d)] (withWidthTag 64 "CMP") [.reg (loopCtr d), .imm 0]⟩
        , ⟨0, .Lcond (.reg "Z") (d + 0x40000000)⟩
        , ⟨0, .Llabel .internal d⟩ ]
        ++ W.1
        ++ (if W.2 == accReg then []
            else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg W.2]⟩])
        ++ [ ⟨0, .Lopn [.reg (loopIdx d)] (withWidthTag 64 "ADD") [.reg (loopIdx d), .imm 1]⟩
           , ⟨0, .Lopn [.reg (loopCtr d)] (withWidthTag 64 "SUB") [.reg (loopCtr d), .imm 1]⟩ ]
        ++ (invRegsOf invOps).map (fun r =>
             ⟨0, .Lopn [.reg (loopCtr d)] (withWidthTag 64 "CMP") [.reg (loopCtr d), .reg r]⟩)
        ++ [ ⟨0, .Lopn [.reg (loopCtr d)] (withWidthTag 64 "CMP") [.reg (loopCtr d), .imm 0]⟩
           , ⟨0, .Lcond (.reg "NZ") d⟩
           , ⟨0, .Llabel .internal (d + 0x40000000)⟩ ] := rfl

/-- **Wire tie of the loop node.** The wire projection of `forLoopLcmdNRtRM` is
    the instruction stream of the export's `forLoopLcmdNRt`: the typed program
    is a lift of the emitted `Lcmd`, instruction for instruction. -/
theorem forLoopLcmdNRtRM_wire (d : Nat) (accReg : String) (initOp countOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) :
    (forLoopLcmdNRtRM d accReg initOp countOp update invOps immSlotMap).map Prod.fst
      = (forLoopLcmdNRt d accReg initOp countOp update invOps immSlotMap).map
          Linstr.li_i := by
  unfold forLoopLcmdNRtRM forLoopBodyNRtRM guardedFlagLoopLinstrRM
    flagLoopLinstrRM flagBackedge loopSeedsRM loopFeedbackRM loopAdvanceRM loopTouchRM
  rw [forLoopLcmdNRt_unfold]
  simp only [List.map_append, List.map_cons, List.map_nil, List.map_map,
    loopBodyWalkNM_wire]
  split <;> simp [Function.comp_def]

/-- Every instruction of the looped segment is an `Lopn`. -/
theorem forLoopBodyNRtRM_isLopn (d : Nat) (accReg : String) {accTy : JasminTy}
    {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) :
    ∀ i ∈ forLoopBodyNRtRM d accReg update invOps immSlotMap, IsLopn i := by
  intro i hi
  simp only [forLoopBodyNRtRM, List.mem_append] at hi
  rcases hi with ((hi | hi) | hi) | hi
  · exact loopBodyWalkNM_isLopn _ _ _ _ _ _ _ i hi
  · unfold loopFeedbackRM at hi
    split at hi
    · simp at hi
    · simp only [List.mem_singleton] at hi; subst hi; exact ⟨_, _, _, rfl⟩
  · simp only [loopAdvanceRM, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> exact ⟨_, _, _, rfl⟩
  · simp only [loopTouchRM, List.mem_map] at hi
    obtain ⟨r, _, rfl⟩ := hi
    exact ⟨_, _, _, rfl⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLift
