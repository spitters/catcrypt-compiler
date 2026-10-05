/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportLoopsJ

@[expose] public section

set_option autoImplicit false

/-!
# The export of carried-register loops over an instruction-set data record

The frames `regsLoopFrame` and `whileRegsFrame` of `ExportLoopsJ` fix the zero-trip guard,
the back edge and the invariant touch of a loop to the x86 compare forms. This module
states the same frames, the body walk and the virtual and physical exports of a `ComLJ`
program with these three instruction groups read from a record `I : IsaData`, as
`ExportLoops.blockLoopFrame` reads them for a `ComL` loop. At `I = x86Data` each definition
is the definition of `ExportLoopsJ`.

A frame depends on the record through `zeroTripGuard`, `loopGuard` and `invTouch` only
(`regsLoopFrameI_congr`, `whileRegsFrameI_congr`). At a record whose invariant touch is the
keep marker `LprogIsa.keepTouch`, removing the keep markers of a counted frame gives the
frame with no invariant register around the body without its keep markers
(`dropKeep_regsLoopFrameI`).

## Main definitions

* `regsLoopFrameI`, `whileRegsFrameI`: the counted and the do-while frame over `I`.
* `forLoopRegsLcmdI`, `whileRegsLcmdI`, `comLJToBodyI`: the loop nodes and the body walk.
* `ComLJ.toLfundefI`, `ComLJ.toLfundefPhysAbiI`, `ComLJ.toLprogPhysAbiI`: the virtual and
  the physical export.
* `ComL.toLfundefPhysAbiI`, `ComL.toLprogPhysAbiI`: the physical export of a `ComL` program
  at the virtual export `ComL.toLfundef c immSlotMap I`.
* `dropKeep`: a body without its keep markers.

## Main results

* `regsLoopFrameI_x86`, `whileRegsFrameI_x86`, `comLJToBodyI_x86`, `ComLJ.toLfundefI_x86`,
  `ComLJ.toLprogPhysAbiI_x86`: at `x86Data` the definitions are those of `ExportLoopsJ`.
* `regsLoopFrameI_congr`, `whileRegsFrameI_congr`: the dependence on the record.
* `dropKeep_regsLoopFrameI`, `dropKeep_regsLoopFrameI_x86`: the counted frame without its
  keep markers, at any record and at a record with the x86 guards.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaData IsaAbi keepTouch isKeep)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)

/-! ## 1. The frames -/

/-- The counted back-edge frame of a carried-register loop over the record `I`:
    `regsLoopFrame` with the zero-trip guard `I.zeroTripGuard`, the back edge `I.loopGuard`
    and one invariant touch `I.invTouch ctr r` per invariant base register. -/
def regsLoopFrameI (d : Nat) (accs : List (String × LOperand × LOperand))
    (idxReg ctr : String) (countOp : LOperand) (invRegs : List String) (bodyW : Lcmd)
    (tmp0 : Nat) (I : IsaData := x86Data) : Lcmd :=
  let targets := accs.map (·.1)
  let stage := feedbackStage d tmp0 targets (accs.map (·.2.2)) 0
  let feedback : Lcmd := stage.1 ++ feedbackMoves targets stage.2
  let seeds : Lcmd := accs.map fun a => ⟨0, .Lopn [.reg a.1] (withWidthTag 64 "MOV") [a.2.1]⟩
  let top : LLabel := d
  let endL : LLabel := d + 0x40000000
  let invTouch : Lcmd := invRegs.map (fun r => ⟨0, I.invTouch ctr r⟩)
  seeds ++
  ([ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
   , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [countOp]⟩ ]
    ++ (I.zeroTripGuard ctr top endL).map (⟨0, ·⟩)
    ++ [ ⟨0, .Llabel .internal top⟩ ])
  ++ bodyW ++ feedback
  ++ [ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "ADD") [.reg idxReg, .imm 1]⟩
     , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ ]
  ++ invTouch
  ++ ((I.loopGuard ctr top).map (⟨0, ·⟩) ++ [ ⟨0, .Llabel .internal endL⟩ ])

/-- The do-while back-edge frame of a carried-register loop over the record `I`:
    `whileRegsFrame` with the back edge `I.loopGuard` on the continue-bit register and one
    invariant touch `I.invTouch` on that register per invariant base register. -/
def whileRegsFrameI (d : Nat) (accs : List (String × LOperand × LOperand))
    (flagOp : LOperand) (invRegs : List String) (bodyW : Lcmd) (tmp0 : Nat)
    (I : IsaData := x86Data) : Lcmd :=
  let targets := accs.map (·.1)
  let stage := feedbackStage d tmp0 targets (accs.map (·.2.2) ++ [flagOp]) 0
  let flagSrc := stage.2.getD accs.length flagOp
  let feedback : Lcmd := stage.1 ++ feedbackMoves targets stage.2
  let flagMat : String × Lcmd :=
    let r := loopReg d (tmp0 + accs.length + 1)
    match flagSrc with
    | .reg f =>
        let z := loopReg d (tmp0 + accs.length + 2)
        (r, [ ⟨0, .Lopn [.reg r] (withWidthTag 64 "MOV") [.imm 1]⟩
            , ⟨0, .Lopn [.reg z] (withWidthTag 64 "MOV") [.imm 0]⟩
            , ⟨0, .Lopn [.reg r] (withWidthTag 64 "CMOV") [.reg f, .reg r, .reg z]⟩ ])
    | op => (r, [⟨0, .Lopn [.reg r] (withWidthTag 64 "MOV") [op]⟩])
  let flagReg := flagMat.1
  let seeds : Lcmd := accs.map fun a => ⟨0, .Lopn [.reg a.1] (withWidthTag 64 "MOV") [a.2.1]⟩
  let top : LLabel := d
  let invTouch : Lcmd := invRegs.map (fun r => ⟨0, I.invTouch flagReg r⟩)
  seeds ++ [⟨0, .Llabel .internal top⟩]
  ++ bodyW ++ feedback ++ flagMat.2
  ++ invTouch
  ++ (I.loopGuard flagReg top).map (⟨0, ·⟩)

/-- At `x86Data` the counted frame is `regsLoopFrame`. -/
theorem regsLoopFrameI_x86 (d : Nat) (accs : List (String × LOperand × LOperand))
    (idxReg ctr : String) (countOp : LOperand) (invRegs : List String) (bodyW : Lcmd)
    (tmp0 : Nat) :
    regsLoopFrameI d accs idxReg ctr countOp invRegs bodyW tmp0 x86Data =
      regsLoopFrame d accs idxReg ctr countOp invRegs bodyW tmp0 := rfl

/-- At `x86Data` the do-while frame is `whileRegsFrame`. -/
theorem whileRegsFrameI_x86 (d : Nat) (accs : List (String × LOperand × LOperand))
    (flagOp : LOperand) (invRegs : List String) (bodyW : Lcmd) (tmp0 : Nat) :
    whileRegsFrameI d accs flagOp invRegs bodyW tmp0 x86Data =
      whileRegsFrame d accs flagOp invRegs bodyW tmp0 := rfl

/-- The counted frame reads the record through its two guards and its invariant touch. -/
theorem regsLoopFrameI_congr {I J : IsaData} (hz : I.zeroTripGuard = J.zeroTripGuard)
    (hg : I.loopGuard = J.loopGuard) (ht : I.invTouch = J.invTouch) (d : Nat)
    (accs : List (String × LOperand × LOperand)) (idxReg ctr : String) (countOp : LOperand)
    (invRegs : List String) (bodyW : Lcmd) (tmp0 : Nat) :
    regsLoopFrameI d accs idxReg ctr countOp invRegs bodyW tmp0 I =
      regsLoopFrameI d accs idxReg ctr countOp invRegs bodyW tmp0 J := by
  simp only [regsLoopFrameI, hz, hg, ht]

/-- The do-while frame reads the record through its back edge and its invariant touch. -/
theorem whileRegsFrameI_congr {I J : IsaData} (hg : I.loopGuard = J.loopGuard)
    (ht : I.invTouch = J.invTouch) (d : Nat) (accs : List (String × LOperand × LOperand))
    (flagOp : LOperand) (invRegs : List String) (bodyW : Lcmd) (tmp0 : Nat) :
    whileRegsFrameI d accs flagOp invRegs bodyW tmp0 I =
      whileRegsFrameI d accs flagOp invRegs bodyW tmp0 J := by
  simp only [whileRegsFrameI, hg, ht]

/-! ## 2. The loop nodes and the body walk -/

/-- The `Lcmd` of a counted carried-register loop node over the record `I`:
    `forLoopRegsLcmd` with the frame `regsLoopFrameI`. -/
def forLoopRegsLcmdI (d : Nat) (initOps : List LOperand) (countOp : LOperand)
    {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ JasminTy.reg 64 :: invTys) cs)
    (invOps : List LOperand) (I : IsaData := x86Data) : Lcmd :=
  let nCar := cs.length
  let idxReg := loopIdx d
  let invRegs : List String := invOps.filterMap (fun o =>
    match o with | .reg n => some n | _ => none)
  let w := loopBodyWalkR d d nCar (some idxReg) invOps update (invTys.length + 1 + nCar)
  regsLoopFrameI d ((carriedRegs d nCar).zip (initOps.zip w.2.1)) idxReg (loopCtr d) countOp
    invRegs w.1 w.2.2 I

/-- The `Lcmd` of a do-while carried-register loop node over the record `I`:
    `whileRegsLcmd` with the frame `whileRegsFrameI`. -/
def whileRegsLcmdI (d : Nat) (initOps : List LOperand) {cs invTys : Ctxt jasminDialect}
    (update : MultiReturnCom jasminDialect (cs ++ invTys) (JasminTy.reg 1 :: cs))
    (invOps : List LOperand) (I : IsaData := x86Data) : Lcmd :=
  let nCar := cs.length
  let invRegs : List String := invOps.filterMap (fun o =>
    match o with | .reg n => some n | _ => none)
  let w := loopBodyWalkR d d nCar none invOps update (invTys.length + nCar)
  whileRegsFrameI d ((carriedRegs d nCar).zip (initOps.zip w.2.1.tail))
    (w.2.1.headD (.imm 0)) invRegs w.1 w.2.2 I

/-- Walk a `ComLJ` program into its `Lcmd` body over the record `I`: `comLJToBody` with a
    lifted program walked by `comLToBody` at `I` and the loop nodes `forLoopRegsLcmdI`,
    `whileRegsLcmdI`. -/
def comLJToBodyI (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → ComLJ Γ t → (curDepth : Nat) →
    (I : IsaData := x86Data) → Lcmd
  | _, _, .lift c, curDepth, I => comLToBody nArgs argNames immSlotMap c curDepth I
  | _, _, .var e body, curDepth, I =>
      ⟨0, opToLinstrR e.op (regName curDepth)
            (exprArgs curDepth nArgs argNames immSlotMap e)⟩
        :: comLJToBodyI nArgs argNames immSlotMap body (curDepth + 1) I
  | _, _, .forLoopRegs (cs := cs) update count inits invs body, curDepth, I =>
      forLoopRegsLcmdI curDepth (exprArgsHV curDepth nArgs argNames immSlotMap inits)
          (resolveVar curDepth nArgs argNames immSlotMap count) update
          (exprArgsHV curDepth nArgs argNames immSlotMap invs) I
        ++ comLJToBodyI nArgs argNames immSlotMap body (curDepth + cs.length) I
  | _, _, .whileRegs (cs := cs) update inits invs body, curDepth, I =>
      whileRegsLcmdI curDepth (exprArgsHV curDepth nArgs argNames immSlotMap inits) update
          (exprArgsHV curDepth nArgs argNames immSlotMap invs) I
        ++ comLJToBodyI nArgs argNames immSlotMap body (curDepth + cs.length) I

/-- At `x86Data` the body walk is `comLJToBody`. -/
theorem comLJToBodyI_x86 (nArgs : Nat) (argNames : Nat → String) (immSlotMap : ImmSlotMap) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComLJ Γ t) (curDepth : Nat),
      comLJToBodyI nArgs argNames immSlotMap c curDepth x86Data =
        comLJToBody nArgs argNames immSlotMap c curDepth
  | _, _, .lift _, _ => rfl
  | _, _, .var _ body, curDepth => by
      simp only [comLJToBodyI, comLJToBody,
        comLJToBodyI_x86 nArgs argNames immSlotMap body (curDepth + 1)]
  | _, _, .forLoopRegs (cs := cs) _ _ _ _ body, curDepth => by
      simp only [comLJToBodyI, comLJToBody,
        comLJToBodyI_x86 nArgs argNames immSlotMap body (curDepth + cs.length)]
      rfl
  | _, _, .whileRegs (cs := cs) _ _ _ body, curDepth => by
      simp only [comLJToBodyI, comLJToBody,
        comLJToBodyI_x86 nArgs argNames immSlotMap body (curDepth + cs.length)]
      rfl

/-! ## 3. The virtual and the physical export -/

/-- The virtual `lfundef` of a `ComLJ` program over the record `I`: `ComLJ.toLfundef` with
    the body `comLJToBodyI` at `I`. -/
def ComLJ.toLfundefI {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComLJ Γ t)
    (immSlotMap : ImmSlotMap := fun _ => none) (I : IsaData := x86Data) : Lfundef :=
  { ComLJ.toLfundef c immSlotMap with
    lfd_body := comLJToBodyI Γ.length argName immSlotMap c Γ.length I }

/-- At `x86Data` the virtual export is `ComLJ.toLfundef`. -/
theorem ComLJ.toLfundefI_x86 {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComLJ Γ t)
    (immSlotMap : ImmSlotMap) :
    ComLJ.toLfundefI c immSlotMap x86Data = ComLJ.toLfundef c immSlotMap := by
  simp only [ComLJ.toLfundefI, comLJToBodyI_x86]
  rfl

/-- The physical `lfundef` of a `ComLJ` program over the record `I`:
    `ComLJ.toLfundefPhysAbi` at the virtual export `ComLJ.toLfundefI`. The register file
    and calling convention `abi` is a separate argument, as in `lfundefPhysAbiOfVirt`. -/
def ComLJ.toLfundefPhysAbiI {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComLJ Γ t)
    (outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) (posBind : Bool := false)
    (I : IsaData := x86Data) (abi : IsaAbi := x86Abi) : Lfundef :=
  let nArgs := Γ.length
  let derived : String × List String :=
    match ComLJ.loopArgBaseNames nArgs immSlotMap c nArgs with
    | some (o, ins) => (o, ins)
    | none => (outArg, inArgs)
  lfundefPhysAbiOfVirt (ComLJ.toLfundefI c immSlotMap I) derived.1 derived.2
    ((ComLJ.loopAccRegs c nArgs).map regName) shiftImm abiArgs abiTyin abi posBind

/-- Export a `ComLJ` program over the record `I` to a physical `Lprog` with one
    function. -/
def ComLJ.toLprogPhysAbiI {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComLJ Γ t)
    (fname outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) (posBind : Bool := false)
    (I : IsaData := x86Data) (abi : IsaAbi := x86Abi) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs :=
      [(fname, ComLJ.toLfundefPhysAbiI c outArg inArgs shiftImm immSlotMap abiArgs abiTyin
                 posBind I abi)] }

/-- At `x86Data` and `x86Abi` the physical export is `ComLJ.toLprogPhysAbi`. -/
theorem ComLJ.toLprogPhysAbiI_x86 {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComLJ Γ t)
    (fname outArg : String) (inArgs : List String) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) (abiArgs : List String) (abiTyin : List Nat) (posBind : Bool) :
    ComLJ.toLprogPhysAbiI c fname outArg inArgs shiftImm immSlotMap abiArgs abiTyin posBind
        x86Data x86Abi =
      ComLJ.toLprogPhysAbi c fname outArg inArgs shiftImm immSlotMap abiArgs abiTyin
        posBind := by
  simp only [ComLJ.toLprogPhysAbiI, ComLJ.toLfundefPhysAbiI, ComLJ.toLfundefI_x86]
  rfl

/-- The physical `lfundef` of a `ComL` program over the record `I`: `ComL.toLfundefPhysAbi`
    at the virtual export `ComL.toLfundef c immSlotMap I`. -/
def ComL.toLfundefPhysAbiI {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) (abi : IsaAbi := x86Abi)
    (posBind : Bool := false) (I : IsaData := x86Data) : Lfundef :=
  let nArgs := Γ.length
  let derived : String × List String :=
    match ComL.loopArgBaseNames nArgs immSlotMap c nArgs with
    | some (o, ins) => (o, ins)
    | none => (outArg, inArgs)
  lfundefPhysAbiOfVirt (ComL.toLfundef c immSlotMap I) derived.1 derived.2
    ((ComL.loopAccRegs c nArgs).map regName) shiftImm abiArgs abiTyin abi posBind

/-- Export a `ComL` program over the record `I` to a physical `Lprog` with one function. -/
def ComL.toLprogPhysAbiI {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (fname outArg : String) (inArgs : List String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64]) (abi : IsaAbi := x86Abi)
    (posBind : Bool := false) (I : IsaData := x86Data) : Lprog :=
  { lp_rip := "RIP"
    lp_rsp := "RSP"
    lp_globs := []
    lp_glob_names := []
    lp_funcs :=
      [(fname, ComL.toLfundefPhysAbiI c outArg inArgs shiftImm immSlotMap abiArgs abiTyin
                 abi posBind I)] }

/-- At `x86Data` the physical export of a `ComL` program is `ComL.toLprogPhysAbi`. -/
theorem ComL.toLprogPhysAbiI_x86 {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (fname outArg : String) (inArgs : List String) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) (abiArgs : List String) (abiTyin : List Nat) (abi : IsaAbi)
    (posBind : Bool) :
    ComL.toLprogPhysAbiI c fname outArg inArgs shiftImm immSlotMap abiArgs abiTyin abi
        posBind x86Data =
      ComL.toLprogPhysAbi c fname outArg inArgs shiftImm immSlotMap abiArgs abiTyin abi
        posBind := rfl

/-! ## 4. A frame without its keep markers -/

/-- A body without its keep markers. -/
def dropKeep (body : Lcmd) : Lcmd := body.filter fun i => !isKeep i.li_i

@[simp] theorem dropKeep_nil : dropKeep [] = [] := rfl

theorem dropKeep_append (a b : Lcmd) : dropKeep (a ++ b) = dropKeep a ++ dropKeep b :=
  List.filter_append ..

/-- A body none of whose instructions is a keep marker is its own `dropKeep`. -/
theorem dropKeep_of_forall {body : Lcmd} (h : ∀ i ∈ body, isKeep i.li_i = false) :
    dropKeep body = body :=
  List.filter_eq_self.mpr fun i hi => by simp [h i hi]

/-- A list of keep markers has the empty `dropKeep`. -/
theorem dropKeep_keepTouch (ctr : String) (rs : List String) :
    dropKeep (rs.map fun r => (⟨0, keepTouch ctr r⟩ : Linstr)) = [] :=
  List.filter_eq_nil_iff.mpr fun i hi => by
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hi
    simp

/-- A copy at the `64`-bit tag is not a keep marker. -/
theorem isKeep_mov64 (dsts srcs : List LOperand) :
    isKeep (.Lopn dsts (withWidthTag 64 "MOV") srcs) = false :=
  show (withWidthTag 64 "MOV" == "KEEP") = false by decide +kernel

/-- No staging copy of `feedbackStage` is a keep marker. -/
theorem feedbackStage_not_keep (d tmp0 : Nat) (targets : List String) :
    ∀ (ops : List LOperand) (i : Nat),
      ∀ x ∈ (feedbackStage d tmp0 targets ops i).1, isKeep x.li_i = false
  | [], _ => by simp [feedbackStage]
  | op :: ops, i => by
      intro x hx
      have ih := feedbackStage_not_keep d tmp0 targets ops (i + 1)
      unfold feedbackStage at hx
      cases op with
      | reg y =>
          simp only at hx
          split at hx
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact isKeep_mov64 _ _
            · exact ih x hx
          · exact ih x hx
      | _ => exact ih x hx

/-- No move of `feedbackMoves` is a keep marker. -/
theorem feedbackMoves_not_keep :
    ∀ (ts : List String) (ss : List LOperand),
      ∀ x ∈ feedbackMoves ts ss, isKeep x.li_i = false
  | [], _ => by simp [feedbackMoves]
  | _ :: _, [] => by simp [feedbackMoves]
  | t :: ts, s :: ss => by
      intro x hx
      have ih := feedbackMoves_not_keep ts ss
      unfold feedbackMoves at hx
      cases s with
      | reg y =>
          simp only at hx
          split at hx
          · exact ih x hx
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact isKeep_mov64 _ _
            · exact ih x hx
      | _ =>
          rcases List.mem_cons.mp hx with rfl | hx
          · exact isKeep_mov64 _ _
          · exact ih x hx

/-- **The counted frame without its keep markers.** At a record `I` whose invariant touch
    is the keep marker and whose two guards hold no keep marker, the frame
    `regsLoopFrameI` without its keep markers is the frame with no invariant register
    around the body without its keep markers. -/
theorem dropKeep_regsLoopFrameI {I : IsaData} (ht : I.invTouch = keepTouch)
    (hz : ∀ ctr top endL, ∀ i ∈ I.zeroTripGuard ctr top endL, isKeep i = false)
    (hg : ∀ ctr top, ∀ i ∈ I.loopGuard ctr top, isKeep i = false)
    (d : Nat) (accs : List (String × LOperand × LOperand)) (idxReg ctr : String)
    (countOp : LOperand) (invRegs : List String) (bodyW : Lcmd) (tmp0 : Nat) :
    dropKeep (regsLoopFrameI d accs idxReg ctr countOp invRegs bodyW tmp0 I) =
      regsLoopFrameI d accs idxReg ctr countOp [] (dropKeep bodyW) tmp0 I := by
  have hseeds : ∀ i ∈ (accs.map fun a =>
      (⟨0, .Lopn [.reg a.1] (withWidthTag 64 "MOV") [a.2.1]⟩ : Linstr)),
      isKeep i.li_i = false := by
    intro i hi
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hi
    exact isKeep_mov64 _ _
  have hzt : ∀ top endL, ∀ i ∈ (I.zeroTripGuard ctr top endL).map
      (fun x => (⟨0, x⟩ : Linstr)), isKeep i.li_i = false := by
    intro top endL i hi
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
    exact hz ctr top endL x hx
  have hlg : ∀ top, ∀ i ∈ (I.loopGuard ctr top).map (fun x => (⟨0, x⟩ : Linstr)),
      isKeep i.li_i = false := by
    intro top i hi
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
    exact hg ctr top x hx
  have h2 : ∀ (a b : LinstrR), isKeep a = false → isKeep b = false →
      dropKeep [(⟨0, a⟩ : Linstr), ⟨0, b⟩] = [⟨0, a⟩, ⟨0, b⟩] := by
    intro a b ha hb
    exact dropKeep_of_forall (by simp [ha, hb])
  have h1 : ∀ (a : LinstrR), isKeep a = false → dropKeep [(⟨0, a⟩ : Linstr)] = [⟨0, a⟩] := by
    intro a ha
    exact dropKeep_of_forall (by simp [ha])
  simp only [regsLoopFrameI, dropKeep_append, ht, dropKeep_keepTouch, List.map_nil,
    List.append_nil, dropKeep_of_forall hseeds, dropKeep_of_forall (hzt _ _),
    dropKeep_of_forall (hlg _), dropKeep_of_forall (feedbackStage_not_keep _ _ _ _ _),
    dropKeep_of_forall (feedbackMoves_not_keep _ _),
    h2 _ _ (isKeep_mov64 _ _) (isKeep_mov64 _ _),
    h2 (.Lopn [.reg idxReg] (withWidthTag 64 "ADD") [.reg idxReg, .imm 1])
      (.Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1])
      (show (withWidthTag 64 "ADD" == "KEEP") = false by decide +kernel)
      (show (withWidthTag 64 "SUB" == "KEEP") = false by decide +kernel),
    h1 _ (show isKeep (.Llabel .internal _) = false from rfl)]

/-- The x86 zero-trip guard holds no keep marker. -/
theorem x86Data_zeroTripGuard_not_keep (ctr : String) (top endL : LLabel) :
    ∀ i ∈ x86Data.zeroTripGuard ctr top endL, isKeep i = false := by
  intro i hi
  have h : (withWidthTag 64 "CMP" == "KEEP") = false := by decide +kernel
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact h
  · rfl

/-- The x86 back edge holds no keep marker. -/
theorem x86Data_loopGuard_not_keep (ctr : String) (top : LLabel) :
    ∀ i ∈ x86Data.loopGuard ctr top, isKeep i = false := by
  intro i hi
  have h : (withWidthTag 64 "CMP" == "KEEP") = false := by decide +kernel
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact h
  · rfl

/-- **The counted frame with the x86 guards and the keep marker, without its keep
    markers**, is the x86 frame `regsLoopFrame` with no invariant register around the body
    without its keep markers. -/
theorem dropKeep_regsLoopFrameI_x86 {I : IsaData} (ht : I.invTouch = keepTouch)
    (hz : I.zeroTripGuard = x86Data.zeroTripGuard) (hg : I.loopGuard = x86Data.loopGuard)
    (d : Nat) (accs : List (String × LOperand × LOperand)) (idxReg ctr : String)
    (countOp : LOperand) (invRegs : List String) (bodyW : Lcmd) (tmp0 : Nat) :
    dropKeep (regsLoopFrameI d accs idxReg ctr countOp invRegs bodyW tmp0 I) =
      regsLoopFrame d accs idxReg ctr countOp [] (dropKeep bodyW) tmp0 := by
  rw [dropKeep_regsLoopFrameI ht (by rw [hz]; exact x86Data_zeroTripGuard_not_keep)
    (by rw [hg]; exact x86Data_loopGuard_not_keep)]
  simp only [regsLoopFrameI, hz, hg]
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
