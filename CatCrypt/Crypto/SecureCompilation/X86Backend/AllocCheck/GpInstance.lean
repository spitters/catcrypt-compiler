/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.Check
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc

/-!
# The general-purpose register instance of the allocation checker

`gpSig` describes the instructions of a physical-register `Lcmd` body to the generic
checker `Check.allocCheck`, and `replayRun` turns the per-instruction decisions of
`LprogGpRealloc` into an `Alloc`.

Locations. A general-purpose register other than `R14`/`R15` is a `gp` location, `R14`
and `R15` are `scratch`, a frame cell `k.N` is a `frame` location, and every other name
(flags, memory cells `mem.<B>.<off>`, sentinels) is `pinned`. Only a pool register admits
a name other than its home name.

Signatures. A fragment instruction (`LprogGpRealloc.fragOf?`) reads its register sources
at any admitted location (at their own names in the `fixed` shape) and the base registers
of its memory names at their own names; it writes its destination at any admitted
location, tied to its first source in the `tied` shape; a 64-bit register copy is a copy
and a move is pure. A conditional branch reads the locations its operand names. Any other
`Lopn` reads and writes its operands at their own names; one whose mnemonic is outside the
recognised alphabet (`LcmdCopyPropagate.isRecognizedOpn`, which excludes every mnemonic
with an implicit register operand) also requires every general-purpose register to hold
its home name.

Adapter. `replayRun lend is cs` follows `LprogGpRealloc.goAcc` on the decisions `cs` of a
run: it carries the same name-to-location map, places each use where the map says, each
definition at its decision, and deletes the moves `goAcc` drops as dead. It performs no
check; the checker does.

## Main definitions

* `gpLoc`, `gpSig`: the locations and the signature.
* `replayRun`, `allocOfDecs`: the adapter from `goAcc`'s decisions.
* `runVerdicts`: the results of `goAcc` and of `allocCheck gpSig` on one run and one
  decision list.
* `runLends`: the runs of a body with the live-out sets `reallocBody` gives them, with the
  two fixes of that computation (`labelLiveFrames`, the branch operand in `instrFrames`)
  selectable.
* `bodyCheckE`: `allocCheckE gpSig` over the graph of a whole body, on the decisions the
  pass selects under the chosen live-out computation.

## Main results

* `gpAgreement`: the number of runs, of accepted candidates and of disagreements
  between `goAcc` and `allocCheck gpSig` over every candidate of every run of a body.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.GpInstance

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.Check
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
  (isPhysGP physGPs isRecognizedOpn)

/-! ## 1. Locations and the signature -/

/-- The location of a name. -/
def gpLoc (n : String) : Loc :=
  if isFrame n then ⟨.frame, n⟩
  else if n == "R14" || n == "R15" then ⟨.scratch, n⟩
  else if isPhysGP n then ⟨.gp, n⟩
  else ⟨.pinned, n⟩

/-- An operand at its own name. -/
def atSelf (n : String) : Check.Operand := ⟨n, .at (gpLoc n)⟩

/-- The locations an operand of an instruction outside the fragment names. -/
def opLocs : LOperand → List String
  | .reg n => if isLoc n then [n] else baseRegs n
  | .arr b _ => if isLoc b then [b] else []
  | .arrIdx b x _ => [b, x].filter (isLoc ·)
  | .imm _ => []

/-- The fragment view of an instruction. -/
def fragR? (i : LinstrR) : Option FI := fragOf? ⟨0, i⟩

/-- The uses of a fragment instruction. -/
def fiUses (i : FI) : List Check.Operand :=
  let fixed := shapeOf i == .fixed
  let srcOps := i.srcs.flatMap fun
    | .reg s =>
        if isLoc s then [⟨s, if fixed then .at (gpLoc s) else .any⟩]
        else (baseRegs s).map atSelf
    | _ => []
  srcOps ++ (baseRegs i.d).map atSelf

/-- The definitions of a fragment instruction. -/
def fiDefs (i : FI) : List Check.Operand :=
  if isLoc i.d && shapeOf i != .fixed then [⟨i.d, .any⟩] else [atSelf i.d]

/-- The uses of an instruction. -/
def gpUses (i : LinstrR) : List Check.Operand :=
  match fragR? i with
  | some f => fiUses f
  | none =>
      match i with
      | .Lopn dsts _ srcs => ((srcs.flatMap opLocs) ++ (dsts.flatMap opLocs)).eraseDups.map atSelf
      | .Lcond c _ => (opLocs c).map atSelf
      | _ => []

/-- The definitions of an instruction. -/
def gpDefs (i : LinstrR) : List Check.Operand :=
  match fragR? i with
  | some f => fiDefs f
  | none =>
      match i with
      | .Lopn dsts _ _ =>
          (dsts.flatMap fun | .reg n => (if isLoc n then [n] else []) | _ => []).eraseDups.map
            atSelf
      | _ => []

/-- The ties of an instruction: a tied fragment instruction writes where its first
    source is. -/
def gpTies (i : LinstrR) : List (Nat × Nat) :=
  match fragR? i with
  | some f => if isLoc f.d && shapeOf f == .tied then [(0, 0)] else []
  | none => []

/-- A 64-bit copy of a register location. -/
def gpIsCopy (i : LinstrR) : Bool :=
  match fragR? i with
  | some f =>
      isCopy64 f.opn && (match f.srcs with | [.reg s] => isLoc s | _ => false)
  | none => false

/-- A fragment move. -/
def gpIsPure (i : LinstrR) : Bool :=
  match fragR? i with
  | some f => movClass f.opn
  | none => false

/-- An instruction whose register reads are not all named: an `Lopn` outside the
    recognised alphabet, a call, a system call, an indirect jump or a label store. -/
def gpOpaque (i : LinstrR) : Bool :=
  match i with
  | .Lopn _ opn _ => !isRecognizedOpn opn
  | .Lcall _ _ | .Lsyscall _ | .Ligoto _ | .LstoreLabel _ _ => true
  | _ => false

/-- **The signature of the general-purpose instance.** -/
def gpSig : Sig LinstrR where
  uses := gpUses
  defs := gpDefs
  ties := gpTies
  clobbers := fun _ => []
  isCopy := gpIsCopy
  isPure := gpIsPure
  frameRef := fun _ => false
  atHome := fun i => if gpOpaque i then physGPs.map gpLoc else []
  anyOk := fun n ℓ => okLoc n ℓ.id
  homeOnly := fun ℓ => ℓ.kind != .gp
  home := fun ℓ => ℓ.id
  moveOk := fun a b =>
    a.kind != .pinned && b.kind != .pinned && !(a.kind == .frame && b.kind == .frame)

/-! ## 2. The adapter -/

/-- The locations of the uses and definitions of one instruction, and whether it is
    deleted. -/
abbrev Dec := Array Loc × Array Loc × Bool

/-- The decision placing every operand at its own name. -/
def selfDec (i : LinstrR) : Dec :=
  (((gpUses i).map (fun o => gpLoc o.name)).toArray,
   ((gpDefs i).map (fun o => gpLoc o.name)).toArray, false)

/-- The decisions of `goAcc` on a run, replayed: the use locations under the current map,
    the decided definition location, and the dead moves `goAcc` drops. `none` when the
    decision list and the run differ in length. -/
def replayRun (lend : List String) (is : List FI) (cs : List String) : Option (Array Dec) :=
  if is.length != cs.length then none
  else some <| Id.run do
    let mut m : Cur := {}
    let mut out : Array Dec := Array.mkEmpty is.length
    for ((i, la), c) in (annotate lend is).1.zip cs do
      let us := ((fiUses i).map (fun o => gpLoc (look m o.name))).toArray
      if isLoc i.d then
        if isCopy64 i.opn && i.srcs.map (fun o => renOp m o) == [.reg c] then
          out := out.push (us, #[gpLoc c], false)
          m := m.insert i.d c
        else if movClass i.opn && !la.contains i.d then
          out := out.push (us, #[gpLoc c], true)
        else
          out := out.push (us, #[gpLoc c], false)
          m := m.insert i.d c
      else
        out := out.push (us, #[gpLoc i.d], false)
    return out

/-- The allocation of an array of per-instruction decisions; no moves. -/
def allocOfDecs (ds : Array Dec) : Alloc where
  useLoc k j := ((ds[k]?).bind (fun d => d.1[j]?)).getD ⟨.pinned, ""⟩
  defLoc k j := ((ds[k]?).bind (fun d => d.2.1[j]?)).getD ⟨.pinned, ""⟩
  before _ := []
  after _ := []
  onEdge _ _ := []
  deleted k := ((ds[k]?).map (fun d => d.2.2)).getD false

/-- Every location name of a body and the general-purpose registers, each at its home. -/
def homeEntry (body : List LinstrR) (extra : List String) : List (Loc × String) :=
  let ns := (physGPs ++ extra ++ body.flatMap (fun i =>
    ((gpUses i).map (·.name)) ++ ((gpDefs i).map (·.name)))).filter (isLoc ·)
  (({} : Std.HashSet String).insertMany ns).toList.map (fun n => (gpLoc n, n))

/-- The results of `goAcc` and of `allocCheck gpSig` on run `is` with live-out set `lend`
    and decisions `cs`. -/
def runVerdicts (lend : List String) (is : List FI) (cs : List String) : Bool × Bool :=
  let old := (goAcc lend {} (annotate lend is).1 cs []).isSome
  let body := is.map FI.toR
  let new := match replayRun lend is cs with
    | some ds =>
        allocCheck gpSig (lineCFG body.length) body.toArray (allocOfDecs ds)
          (homeEntry body lend) (lend.map (fun n => (n, gpLoc n)))
    | none => false
  (old, new)

/-! ## 3. Runs and their live-out sets -/

/-- The frame cells an instruction names; the operand of a conditional branch counts when
    `cond`. -/
def framesOf (cond : Bool) (i : LinstrR) : List String :=
  match i with
  | .Lcond _ _ => if cond then instrFrames i else []
  | _ => instrFrames i

/-- The frame cells a piece names. -/
def pieceFrames (cond : Bool) : Piece → List String
  | .run is => is.flatMap (fun i => framesOf cond i.toR)
  | .bar li => framesOf cond li.li_i

/-- The runs of a body, each with its live-out set as `reallocBody` computes it, in body
    order. `label` adds every frame cell of a body with a label (`labelLiveFrames`);
    `cond` counts a conditional branch's operand among the frame cells an instruction
    names. With both set this is the computation of `reallocBody`. -/
def runLends (label cond : Bool) (res : List String) (body : Lcmd) :
    List (List FI × List String) :=
  let init : Std.HashSet String :=
    if label && body.any (fun li => match li.li_i with | .Llabel _ _ => true | _ => false) then
      ({} : Std.HashSet String).insertMany (body.flatMap (fun li => framesOf cond li.li_i))
    else {}
  let r := (pieces body).foldr
    (fun p (acc : List (List FI × List String) × Option LinstrR × Std.HashSet String) =>
      let out := match p with
        | .run is =>
            let regs := match acc.2.1 with
              | some .Lret => retLive res
              | _ => physGPs
            (is, regs ++ acc.2.2.toList) :: acc.1
        | .bar _ => acc.1
      let nxt := match p with
        | .run is => (is.head?.map FI.toR)
        | .bar li => some li.li_i
      (out, nxt, acc.2.2.insertMany (pieceFrames cond p))) ([], none, init)
  r.1

/-- The decisions the pass selects for a run: the first candidate `goAcc` accepts. -/
def selected (lend : List String) (is : List FI) : Option (List String) :=
  (runCands lend is).find? (fun cs => (goAcc lend {} (annotate lend is).1 cs []).isSome)

/-- **Agreement of the two checks over a body.** For every run (with the live-out set of
    `reallocBody`) and every candidate of `runCands`: the number of runs, the number of
    candidates `goAcc` accepts, and the number of candidates on which `goAcc` and
    `allocCheck gpSig` disagree. -/
def gpAgreement (res : List String) (body : Lcmd) : Nat × Nat × Nat := Id.run do
  let mut runs := 0
  let mut acc := 0
  let mut dis := 0
  for (is, lend) in runLends true true res body do
    runs := runs + 1
    for cs in runCands lend is do
      let (o, n) := runVerdicts lend is cs
      if o then acc := acc + 1
      if o != n then dis := dis + 1
  return (runs, acc, dis)

/-! ## 4. The whole body -/

/-- The per-instruction decisions of a whole body: each run at its selected candidate (at
    its own names when no candidate passes), every other instruction at its own names. -/
def bodyDecs (label cond : Bool) (res : List String) (body : Lcmd) : Array Dec := Id.run do
  let mut runs := runLends label cond res body
  let mut out : Array Dec := Array.mkEmpty body.length
  for p in pieces body do
    match p with
    | .bar li => out := out.push (selfDec li.li_i)
    | .run is =>
        match runs with
        | (is', lend) :: rest =>
            runs := rest
            let ds := match selected lend is' with
              | some cs => replayRun lend is' cs
              | none => none
            match ds with
            | some ds => out := out ++ ds
            | none => out := out ++ (is.map (fun i => selfDec i.toR)).toArray
        | [] => out := out ++ (is.map (fun i => selfDec i.toR)).toArray
  return out

/-- **The whole-body check** of the decisions the pass selects under the chosen live-out
    computation, over the control-flow graph of the body. The exit requirement is
    `retLive res` for a body with a return and the fifteen registers otherwise. `none`
    when the body has no graph. -/
def bodyCheckE (label cond : Bool) (res : List String) (body : Lcmd) :
    Option (Except AllocFailure Unit) :=
  let wl := body.map Linstr.li_i
  (cfgOf wl).map fun G =>
    let outN := if wl.any (fun i => match i with | .Lret => true | _ => false) then
      retLive res else physGPs
    allocCheckE gpSig G wl.toArray (allocOfDecs (bodyDecs label cond res body))
      (homeEntry wl []) (outN.map (fun n => (n, gpLoc n)))

end CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.GpInstance
