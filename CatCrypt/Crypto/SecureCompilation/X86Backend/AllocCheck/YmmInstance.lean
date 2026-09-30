/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.Check
public import CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAllocSound

/-!
# The vector register instance of the allocation checker

`ymmSig` describes a straight-line `List YmmInstr` over virtual vector names to the
generic checker `Check.allocCheck`, and `ymmAlloc` turns a decision list of
`YmmRegAlloc` (`Slot.resident reg | Slot.spilled off`) and its scratch registers into an
`Alloc`, placing operands and spill traffic exactly as `YmmRegAlloc.ymmMaterializeInstr`
does.

Locations. A vector register (resident or scratch) is a `ymm` location and the 32-byte
frame cell at offset `off` from `ymmFrameBase` is the `frame` location `off`. Memory off
the frame is outside the fact.

Signature. An instruction reads `ymmReadNames` and writes `ymmWrittenNames`, every operand
in a vector register; `vpternlogq` writes the register of its first input; a register
move is a copy; a store is the only impure instruction; a load or store at base
`ymmFrameBase` names a frame cell as memory and is rejected.

Adapter. The `j`-th distinct spilled name of an instruction (`spilledNamesOf`) is in the
`j`-th scratch register; a spilled read is preceded by the move from its frame cell to its
scratch register and a spilled write followed by the move back. `ymmAlloc` is `none` when a
name has no decision or an instruction touches more spilled names than there are scratch
registers, the two conditions of `YmmRegAllocSound.instrAllocOk` the generic checker
cannot see.

## Main definitions

* `ymmSig`: the signature.
* `ymmAlloc`: the adapter from a decision list.
* `ymmVerdicts`: the results of `ymmAllocValidClosed` and of `allocCheck ymmSig` on a
  closed program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.YmmInstance

open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.Check
open CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint
open CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAllocSound
open CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-- A vector register. -/
def ymmLoc (r : String) : Loc := ⟨.ymm, r⟩

/-- The frame cell at offset `off`. -/
def frameLoc (off : Int) : Loc := ⟨.frame, toString off⟩

/-- A location a vector move can read or write. -/
def vecLoc (ℓ : Loc) : Bool := ℓ.kind == .ymm || ℓ.kind == .frame

/-- **The signature of the vector instance.** -/
def ymmSig : Sig YmmInstr where
  uses := fun i => (ymmReadNames i).map (fun n => ⟨n, .kind .ymm⟩)
  defs := fun i => (ymmWrittenNames i).map (fun n => ⟨n, .kind .ymm⟩)
  ties := fun i => match i with
    | .ternlog .. => [(0, 0)]
    | _ => []
  clobbers := fun _ => []
  isCopy := fun i => match i with
    | .ymov .. => true
    | _ => false
  isPure := fun i => match i with
    | .ystore .. => false
    | _ => true
  frameRef := fun i => !memOffFrame i
  atHome := fun _ => []
  anyOk := fun _ ℓ => ℓ.kind == .ymm
  homeOnly := fun _ => false
  home := fun ℓ => ℓ.id
  moveOk := fun a b => vecLoc a && vecLoc b && (a.kind == .ymm || b.kind == .ymm)

/-- The operand locations and spill moves of one instruction under decisions `m` and
    scratch registers `scratch`: `(use locations, definition locations, moves before,
    moves after)`. `none` when a name has no decision or the scratch registers run out. -/
def instrPlan (m : Std.HashMap String Slot) (scratch : List String) (i : YmmInstr) :
    Option (Array Loc × Array Loc × List Edit × List Edit) := do
  if !(ymmNamesOf i).all (fun n => m.contains n) then none
  let spilled := ((ymmReadNames i) ++ (ymmWrittenNames i)).eraseDups.filter
    (fun n => isSpilledSlot m[n]?)
  if spilled.length > scratch.length then none
  let scr : String → Option String := fun n =>
    (spilled.findIdx? (· == n)).bind (fun k => scratch[k]?)
  let loc : String → Loc := fun n =>
    match m[n]? with
    | some (.resident r) => ymmLoc r
    | _ => ymmLoc ((scr n).getD n)
  let off : String → Option Int := fun n =>
    match m[n]? with
    | some (.spilled o) => some o
    | _ => none
  let reloads := (ymmReadNames i).eraseDups.filterMap (fun n =>
    (off n).bind (fun o => (scr n).map (fun s => Edit.move (ymmLoc s) (frameLoc o))))
  let stores := (ymmWrittenNames i).eraseDups.filterMap (fun n =>
    (off n).bind (fun o => (scr n).map (fun s => Edit.move (frameLoc o) (ymmLoc s))))
  return (((ymmReadNames i).map loc).toArray, ((ymmWrittenNames i).map loc).toArray,
    reloads, stores)

/-- **The adapter** from a decision list and its scratch registers. -/
def ymmAlloc (d : List (String × Slot)) (scratch : List String) (p : List YmmInstr) :
    Option Alloc := do
  let m := decisionMap d
  let plans ← p.toArray.mapM (instrPlan m scratch)
  return {
    useLoc := fun k j => ((plans[k]?).bind (fun x => x.1[j]?)).getD ⟨.pinned, ""⟩
    defLoc := fun k j => ((plans[k]?).bind (fun x => x.2.1[j]?)).getD ⟨.pinned, ""⟩
    before := fun k => ((plans[k]?).map (fun x => x.2.2.1)).getD []
    after := fun k => ((plans[k]?).map (fun x => x.2.2.2)).getD []
    onEdge := fun _ _ => []
    deleted := fun _ => false }

/-- The check of a closed program (no live-in, no live-out name) with the generic
    checker, with its failure. -/
def ymmCheckClosedE (d : List (String × Slot)) (scratch : List String) (p : List YmmInstr) :
    Option (Except AllocFailure Unit) :=
  (ymmAlloc d scratch p).map fun A => allocCheckE ymmSig (lineCFG p.length) p.toArray A [] []

/-- The results of `ymmAllocValidClosed` and of `allocCheck ymmSig` on a closed
    program. -/
def ymmVerdicts (d : List (String × Slot)) (scratch : List String) (p : List YmmInstr) :
    Bool × Bool :=
  (ymmAllocValidClosed d scratch p,
   ((ymmCheckClosedE d scratch p).map Except.toBool).getD false)

end CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.YmmInstance
