/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.Decompile

/-!
# An untrusted proposer of candidates for the ascent of bytes

`proposeCand` reads given bytes as a candidate `DecompCand Γ t` of the check `decompileB`:
the printed body, an allocation certificate and a region program. Nothing here is trusted;
a candidate is accepted only by `decompileB`, and `checkCand` reports the result of each of
its conjuncts.

The three steps:

* **Body.** The bytes are decoded instruction by instruction (`decodeAt`); the frame of
  `encodeLfundefBytes` (the pushes of callee-saved registers, the `lea` that opens and
  closes the frame, the pops and `ret`) is removed, and each instruction of the body is read
  as an instruction `LinstrR` of the printed body over the export names of the registers.
  A conditional jump is read as `Lcond` to a label placed in front of its target, the labels
  numbered as the export numbers the labels of its loops.
* **Program.** The body is executed symbolically: each location holds a de Bruijn level of
  the program under construction (the parameters at the levels `0, …, n - 1`) or an
  immediate, a move copies the value of its source, and every other instruction is the
  binding of the operation of the Jasmin dialect whose export it is. A counted loop of the
  shape of `forArrFrame` (the zero-trip guard, the top label, the body, the steps of the
  trip index and the counter, the back edge and the exit label) is read as a `forLoop`. The
  untyped program `UProg` is elaborated to `NFProg jasminDialect Γ [t]` with the types
  checked (`elabProg`).
* **Certificate.** The export names that a loop boundary crosses (the counter `loopCtr n`,
  the trip index, the carried names of `forArrFrame` and the names the loop or the code after
  it reads) are paired with the register that holds them there; each parameter is paired
  with the register an operation first reads it from, or the register of the layout.

## Main definitions

* `UProg`, `elabProg`: untyped region programs and their typed elaboration.
* `liftBody`: the printed body of the bytes.
* `readProg`: the untyped program of a printed body.
* `proposeCand`: the candidate of the bytes, or the first step that fails.
* `checkCand`: the candidate followed by the conjuncts of `decompileB`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.DecompilePropose

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.Haxc

/-! ## 1. Untyped programs and their elaboration -/

/-- An untyped region program over de Bruijn indices: the arguments of a binding, the
    returned variables, the counter and the seeds of a loop are indices into the context. -/
inductive UProg where
  /-- Return the variables at the indices. -/
  | ret (vs : List Nat)
  /-- Bind the operation `op` on the variables at the indices `args`. -/
  | var (op : JasminOp) (args : List Nat) (k : UProg)
  /-- A counted loop on the counter at the index `count`, carrying values of the types `cs`
      seeded from the indices `inits`. -/
  | forLoop (count : Nat) (cs : List JasminTy) (inits : List Nat) (body k : UProg)
  deriving Inhabited

/-- The variable of type `t` at the index `i` of `Γ`, when the type at `i` is `t`. -/
def mkVar : (Γ : Ctxt jasminDialect) → (t : JasminTy) → Nat → Option (Ctxt.Var Γ t)
  | [], _, _ => none
  | s :: _, t, 0 => if h : s = t then some (by subst h; exact Ctxt.Var.here) else none
  | _ :: Γ, t, i + 1 => (mkVar Γ t i).map Ctxt.Var.there

/-- The variables of the types `ts` at the indices `is` of `Γ`. -/
def mkVars (Γ : Ctxt jasminDialect) :
    (ts : List JasminTy) → List Nat → Option (HVector (fun t => Ctxt.Var Γ t) ts)
  | [], [] => some .nil
  | t :: ts, i :: is => do
      let v ← mkVar Γ t i
      let vs ← mkVars Γ ts is
      pure (.cons v vs)
  | _, _ => none

/-- **The elaboration of an untyped program** at the context `Γ` and the result types
    `ts`, with the types of every variable checked; the error names the node that fails. -/
def elabProg : (Γ : Ctxt jasminDialect) → (ts : List JasminTy) → UProg →
    Except String (NFProg jasminDialect Γ ts)
  | Γ, ts, .ret vs =>
      match mkVars Γ ts vs with
      | some hv => .ok (.ret hv)
      | none => .error s!"ret: the returned indices {vs} do not have the result types"
  | Γ, ts, .var op args k =>
      match mkVars Γ (DialectSignature.sig (d := jasminDialect) op) args with
      | some hv => do
          let k' ← elabProg (DialectSignature.ret (d := jasminDialect) op :: Γ) ts k
          pure (.var ⟨op, rfl, hv⟩ k')
      | none => .error s!"var: the argument indices {args} do not have the operand types"
  | Γ, ts, .forLoop count cs inits body k =>
      match mkVar Γ (.reg 64) count, mkVars Γ cs inits with
      | some c, some iv => do
          let b ← elabProg (cs ++ JasminTy.reg 64 :: Γ) cs body
          let k' ← elabProg (cs ++ Γ) ts k
          pure (.forLoop c iv b k')
      | _, _ => .error s!"forLoop: the counter {count} or the seeds {inits} are ill-typed"

/-! ## 2. The printed body of the bytes -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (DInstr decodeAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
  (encodeLinstrR encodeLfundefBytesChecked jccOpcode spillQsaveOff)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)

/-- The sixteen general-purpose registers under their export names. -/
def gpNames : List String :=
  ["RAX", "RCX", "RDX", "RBX", "RSP", "RBP", "RSI", "RDI",
   "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15"]

/-- The operand of a decoded source operand, under the export names of the registers. -/
def opOf : JOperand → LOperand
  | .reg r => .reg (exportReg r)
  | .imm v => .imm v

/-- The forms of a two-address operation `mn` writing `d` from the source `s`: the
    destination as first source, then the destination alone, each with and without the
    width tag `:64`. -/
def aluCands (mn d : String) (s : JOperand) : List LinstrR :=
  let D := exportReg d
  [.Lopn [.reg D] (mn ++ ":64") [.reg D, opOf s], .Lopn [.reg D] (mn ++ ":64") [opOf s],
   .Lopn [.reg D] mn [.reg D, opOf s], .Lopn [.reg D] mn [opOf s]]

/-- The frame-slot names whose offset under the frame `frame` is `off`: the spill cells
    `k.N` and the save cells `qsave.R` of `spillQsaveOff`. -/
def slotsAt (frame : Nat) (off : Int) : List String :=
  ((List.range (frame / 8 + 1)).map (fun i => "k." ++ toString i)
      ++ gpNames.map ("qsave." ++ ·)).filter
    fun n => spillQsaveOff frame 64 n == some off

/-- The candidate instructions of the printed body for one decoded instruction, at the
    frame `frame`: the forms of the operation whose encoding is that instruction. -/
def candsOf (frame : Nat) : JInstr 64 → List LinstrR
  | .mov d s =>
      [.Lopn [.reg (exportReg d)] "MOV:64" [opOf s], .Lopn [.reg (exportReg d)] "MOVQ" [opOf s],
       .Lopn [.reg (exportReg d)] "MOV" [opOf s]]
  | .add d s => aluCands "ADD" d s
  | .sub d s => aluCands "SUB" d s
  | .and_ d s => aluCands "AND" d s
  | .or_ d s => aluCands "OR" d s
  | .xor_ d s => aluCands "XOR" d s
  | .imul d s => aluCands "MUL" d s
  | .cmp a s => aluCands "CMP" a s
  | .shl d (.imm n) =>
      aluCands "SHL" d (.imm n) ++ [.Lopn [.reg (exportReg d)] ("SHL:" ++ toString n ++ ":64")
        [.reg (exportReg d)]]
  | .shr d (.imm n) =>
      aluCands "SHR" d (.imm n) ++ [.Lopn [.reg (exportReg d)] ("SHR:" ++ toString n ++ ":64")
        [.reg (exportReg d)]]
  | .sar d (.imm n) =>
      aluCands "SAR" d (.imm n) ++ [.Lopn [.reg (exportReg d)] ("SAR:" ++ toString n ++ ":64")
        [.reg (exportReg d)]]
  | .neg d => [.Lopn [.reg (exportReg d)] "NEG:64" [.reg (exportReg d)]]
  | .not_ d => [.Lopn [.reg (exportReg d)] "NOT:64" [.reg (exportReg d)]]
  | .loadMem d "%rsp" off =>
      (slotsAt frame off).flatMap fun n =>
        [.Lopn [.reg (exportReg d)] "MOV:64" [.reg n], .Lopn [.reg (exportReg d)] "MOV" [.reg n]]
  | .storeMem "%rsp" off s =>
      (slotsAt frame off).flatMap fun n =>
        [.Lopn [.reg n] "MOV:64" [opOf s], .Lopn [.reg n] "MOV" [opOf s]]
  | _ => []

/-- The condition names of the conditional jumps, in the order the proposer tries them:
    the spellings of the loop guards of the export first. -/
def ccNames : List String :=
  ["Z", "NZ", "B", "AE", "BE", "A", "S", "NS", "L", "GE", "LE", "G", "O", "NO",
   "E", "NE", "C", "NC"]

/-- The name of the condition whose jump opcode has the low nibble `cc`. -/
def ccName? (cc : Nat) : Option String :=
  ccNames.find? fun s => jccOpcode s == 0x80 + cc

/-- A decoded instruction with its byte range in the stream. -/
abbrev DItem := Nat × Nat × DInstr

/-- The frame of `encodeLfundefBytes` around the decoded stream: the registers pushed in
    front, the frame size of the opening `lea`, the decoded instructions of the body, and
    the registers popped behind. -/
structure Framed where
  /-- The registers pushed in front of the frame. -/
  pushes : List String
  /-- The frame size. -/
  frame : Nat
  /-- The decoded instructions of the body. -/
  body : List DItem
  /-- The byte offset of the end of the body. -/
  bodyEnd : Nat
  /-- The registers popped behind the frame. -/
  pops : List String

/-- The `lea disp(%rsp), %rsp` of the frame, with its displacement. -/
def leaRsp? : DInstr → Option Int
  | .op (.lea "%rsp" "%rsp" _ _ off) => some off
  | _ => none

/-- **The frame of the decoded stream**: pushes, the opening `lea` of displacement `-F`,
    the body, the closing `lea` of displacement `F`, pops and `ret`. -/
def splitFrame (xs : List DItem) : Except String Framed := do
  let pushes := xs.takeWhile fun x => match x.2.2 with | .push _ => true | _ => false
  let rest := xs.drop pushes.length
  let (open_, rest) ← match rest with
    | x :: r => pure (x, r)
    | [] => throw "frame: no opening lea"
  let off ← match leaRsp? open_.2.2 with
    | some off => pure off
    | none => throw "frame: the instruction after the pushes is not lea disp(%rsp), %rsp"
  let rev := rest.reverse
  let rev ← match rev with
    | x :: r => match x.2.2 with
      | .ret => pure r
      | _ => throw "frame: the stream does not end in ret"
    | [] => throw "frame: empty stream"
  let pops := rev.takeWhile fun x => match x.2.2 with | .pop _ => true | _ => false
  let rev := rev.drop pops.length
  let (close, rev) ← match rev with
    | x :: r => pure (x, r)
    | [] => throw "frame: no closing lea"
  let off' ← match leaRsp? close.2.2 with
    | some o => pure o
    | none => throw "frame: the instruction before the pops is not lea disp(%rsp), %rsp"
  if off' != -off || off > 0 then throw s!"frame: the displacements {off} and {off'} differ"
  let regOfItem : DItem → String := fun x =>
    match x.2.2 with | .push r => exportReg r | .pop r => exportReg r | _ => ""
  pure { pushes := pushes.map regOfItem, frame := off.natAbs, body := rev.reverse,
         bodyEnd := close.1, pops := (pops.map regOfItem).reverse }

/-- The byte offsets that a conditional jump of the body targets. -/
def jumpTargets (xs : List DItem) : List Nat :=
  (xs.filterMap fun x => match x.2.2 with
    | .jcc _ d => some ((x.2.1 : Int) + d).toNat
    | _ => none).eraseDups

/-- **The labels of the jump targets**, numbered as `forArrFrame` numbers them: the target
    of the `k`-th backward jump (in the order of the targets) is the label `2 k` and the
    offset behind that jump the label `2 k + 1`; every other target follows. -/
def labelTable (xs : List DItem) : List (Nat × LLabel) :=
  let backs := (xs.filterMap fun x => match x.2.2 with
    | .jcc _ d => if (x.2.1 : Int) + d ≤ x.1 then some (((x.2.1 : Int) + d).toNat, x.2.1)
        else none
    | _ => none).mergeSort (fun a b => decide (a.1 ≤ b.1))
  let tbl := backs.zipIdx.flatMap fun p => [(p.1.1, 2 * p.2), (p.1.2, 2 * p.2 + 1)]
  let rest := (jumpTargets xs).filter fun o => !(tbl.any (·.1 == o))
  tbl ++ rest.zipIdx.map fun p => (p.1, 2 * backs.length + p.2)

/-- The label of the target offset `o` in the table `ts`. -/
def labelAt (ts : List (Nat × LLabel)) (o : Nat) : LLabel :=
  ((ts.find? (·.1 == o)).map (·.2)).getD 0

/-- **The instruction of the printed body for one decoded instruction**: the first
    candidate whose encoding at the frame is the bytes of the instruction, or a conditional
    jump to the label of its target. -/
def liftItem (bytes : List (BitVec 8)) (frame : Nat) (ts : List (Nat × LLabel)) (x : DItem) :
    Except String LinstrR :=
  let (s, e, d) := x
  match d with
  | .jcc cc disp =>
      match ccName? cc with
      | some n => .ok (.Lcond (.reg n) (labelAt ts ((e : Int) + disp).toNat))
      | none => .error s!"body: condition {cc} at byte {s} has no name"
  | .op i =>
      let seg := (bytes.drop s).take (e - s)
      match (candsOf frame i).find? (fun c => encodeLinstrR frame 64 (fun _ => 0) c == seg) with
      | some c => .ok c
      | none => .error s!"body: no instruction of the printed body encodes the bytes at {s}"
  | _ => .error s!"body: a push, pop, call or ret inside the body at byte {s}"

/-- **The printed body of the bytes**: the decoded body read instruction by instruction
    (`liftItem`), with a label in front of each jump target and at the end, and the return
    of the body. -/
def liftBody (bytes : List (BitVec 8)) : Except String Lcmd := do
  let xs ← match decodeAt bytes.length 0 bytes with
    | some xs => pure xs
    | none => throw "decode: the bytes do not decode"
  let F ← splitFrame xs
  let ts := labelTable F.body
  let lab : Nat → Lcmd := fun o =>
    if ts.any (·.1 == o) then [⟨0, .Llabel .internal (labelAt ts o)⟩] else []
  let mut out : Lcmd := []
  for x in F.body do
    let i ← liftItem bytes F.frame ts x
    out := out ++ lab x.1 ++ [⟨0, i⟩]
  pure (out ++ lab F.bodyEnd ++ [⟨0, .Lret⟩])

/-! ## 3. The program of a printed body -/

/-- The value a location holds in the symbolic reading: a variable of the program, at its
    de Bruijn level, or an immediate not yet bound. -/
inductive Val where
  /-- The variable at the level. -/
  | lvl (n : Nat)
  /-- The immediate. -/
  | imm (v : Nat)
  deriving BEq

/-- An item of the program read so far, over de Bruijn levels: a binding of an operation
    on the levels of its arguments, or a counted loop on the level of its counter, carrying
    values of the types `cs` from the levels `inits`, with the items of its body and the
    levels its body returns. -/
inductive RItem where
  /-- A binding. -/
  | bind (op : JasminOp) (args : List Nat)
  /-- A counted loop. -/
  | loop (count : Nat) (cs : List JasminTy) (inits : List Nat) (body : List RItem)
      (ret : List Nat)
  deriving Inhabited

/-- The state of the symbolic reading: the value each location holds, the number of
    variables in scope, and the items read so far. -/
structure RSt where
  /-- The value each location holds. -/
  loc : List (String × Val)
  /-- The number of variables in scope. -/
  depth : Nat
  /-- The items, in order. -/
  items : List RItem
  /-- The number of parameters. -/
  nArgs : Nat := 0
  /-- The export names read at a loop boundary, each with the location that holds it. -/
  pairs : List (String × String) := []
  /-- The parameters read by an operation, a loop counter or a seed, each with the
      location it is read from. -/
  uses : List (String × String) := []

/-- The value a location holds. -/
def RSt.get? (s : RSt) (x : String) : Option Val := (s.loc.find? (·.1 == x)).map (·.2)

/-- The state with the location `x` holding the value `v`. -/
def RSt.set (s : RSt) (x : String) (v : Val) : RSt :=
  { s with loc := (x, v) :: s.loc.filter (·.1 != x) }

/-- The state with the location `x` holding no value. -/
def RSt.kill (s : RSt) (x : String) : RSt := { s with loc := s.loc.filter (·.1 != x) }

/-- The binding of `op` on the levels `args`, written to the location `x`. -/
def RSt.bind (s : RSt) (x : String) (op : JasminOp) (args : List Nat) : RSt :=
  { s with items := s.items ++ [RItem.bind op args], depth := s.depth + 1 }.set x
    (.lvl s.depth)

/-- A frame-slot name: a spill cell `k.N` or a save cell `qsave.R`. -/
def isSlot (x : String) : Bool := hasPrefix x "k." || hasPrefix x "qsave."

/-- The state that records the general-purpose register `x` as the location of the
    parameter whose level `v` is, when no location of that parameter is recorded yet. -/
def RSt.noteArg (s : RSt) (x : String) : Val → RSt
  | .lvl l =>
      if l < s.nArgs && gpNames.contains x && !s.uses.any (·.1 == argName l) then
        { s with uses := s.uses ++ [(argName l, x)] }
      else s
  | .imm _ => s

/-- The level of a value at the width `w`: a variable's level, or the level of a fresh
    `regConst` binding of an immediate. -/
def RSt.level (s : RSt) (w : Nat) : Val → RSt × Nat
  | .lvl l => (s, l)
  | .imm v => ({ s with items := s.items ++ [RItem.bind (.regConst w v) []], depth := s.depth + 1 },
      s.depth)

/-- The operator of a two-address register mnemonic. -/
def binOpOf? : String → Option JasminBinOp
  | "ADD" => some .add | "SUB" => some .sub | "MUL" => some .mul | "AND" => some .and
  | "OR" => some .or | "XOR" => some .xor | _ => none

/-- The width tag of a mnemonic, `64` for a tagged one and `32` otherwise, and the
    mnemonic without it. -/
def widthOf (opn : String) : Nat × String :=
  if hasSuffix opn ":64" then (64, String.ofList (opn.toList.take (opn.length - 3)))
  else (32, opn)

/-- The level of an operand: a location's level, or a fresh `regConst` binding of an
    immediate at the width `w`. -/
def RSt.operand (s : RSt) (w : Nat) : LOperand → Except String (RSt × Nat)
  | .reg x => match s.get? x with
    | some v => .ok ((s.noteArg x v).level w v)
    | none => .error s!"program: the location {x} is read before it holds a value"
  | .imm v => .ok (s.level w (.imm v))
  | _ => .error "program: an array operand"

/-- The immediate shift of a mnemonic `SHR:<n>`, `SHL:<n>` or `SAR:<n>` and its count. -/
def tagShift? (base : String) : Option (String × Nat) :=
  match base.splitOn ":" with
  | [mn, n] => n.toNat?.map (mn, ·)
  | _ => none

/-- The immediate shift operation of the mnemonic `mn` at the width `w` and the count `n`. -/
def shiftOp? (mn : String) (w n : Nat) : Option JasminOp :=
  match mn with
  | "SHR" => some (.shrImm w n) | "SHL" => some (.shlImm w n) | "SAR" => some (.sarImm w n)
  | _ => none

/-- **One instruction of a straight-line printed body read symbolically**: a move copies
    the level of its source, every other operation is the binding of the operation of the
    Jasmin dialect whose export it is. -/
def readInstr (s : RSt) : LinstrR → Except String RSt
  | .Lopn [.reg d] opn srcs =>
      let (w, base) := widthOf opn
      let base := if base == "MOVQ" then "MOV" else base
      match base, srcs with
      | "MOV", [.reg x] => .ok (match s.get? x with
          | some v => s.set d v
          | none => s.kill d)
      | "MOV", [.imm v] => .ok (s.set d (.imm v))
      | "MOV", _ => .error s!"program: move of the form {repr srcs}"
      | _, _ =>
        match binOpOf? base, srcs with
        | some bop, [a, b] => do
            let (s, la) ← s.operand w a
            let (s, lb) ← s.operand w b
            pure (s.bind d (.regArith bop w) [la, lb])
        | some bop, [b] => do
            let (s, la) ← s.operand w (.reg d)
            let (s, lb) ← s.operand w b
            pure (s.bind d (.regArith bop w) [la, lb])
        | _, _ =>
          match shiftOp? base w 0, srcs with
          | some _, [a, .imm n] => do
              let (s, la) ← s.operand w a
              match shiftOp? base w n with
              | some op => pure (s.bind d op [la])
              | none => throw "program: shift"
          | _, _ =>
            match tagShift? base, srcs with
            | some (mn, n), [a] =>
                match shiftOp? mn w n with
                | some op => do
                    let (s, la) ← s.operand w a
                    pure (s.bind d op [la])
                | none => .error s!"program: no operation of the mnemonic {opn}"
            | _, _ => .error s!"program: no operation of the mnemonic {opn}"
  | .Llabel _ _ => .ok s
  | .Lret => .ok s
  | i => .error s!"program: instruction {repr i} outside the straight-line class"

/-- **The untyped program of the items** `xs` at the depth `d`, returning the levels `rs`:
    each level is turned into the de Bruijn index at the depth where it is read. The body of
    a loop at the depth `d` starts at the depth `d + 1 + cs.length` and its continuation at
    the depth `d + cs.length`. -/
def toUProg (d : Nat) (xs : List RItem) (rs : List Nat) : UProg :=
  match xs with
  | [] => .ret (rs.map fun l => d - 1 - l)
  | .bind op args :: xs => .var op (args.map fun l => d - 1 - l) (toUProg (d + 1) xs rs)
  | .loop c cs inits body bret :: xs =>
      .forLoop (d - 1 - c) cs (inits.map fun l => d - 1 - l)
        (toUProg (d + 1 + cs.length) body bret) (toUProg (d + cs.length) xs rs)

/-- The register destinations of an instruction. -/
def dstsOf : LinstrR → List String
  | .Lopn ds _ _ => ds.filterMap fun | .reg d => some d | _ => none
  | _ => []

/-- The registers an instruction reads: its register sources, and its destination for a
    two-address form with one source other than a move or a tagged shift. -/
def srcsOf : LinstrR → List String
  | .Lopn ds opn ss =>
      let base := (widthOf opn).2
      ss.filterMap (fun | .reg x => some x | _ => none)
        ++ (if ss.length == 1 && (binOpOf? base).isSome then dstsOf (.Lopn ds opn ss) else [])
  | _ => []

/-- The registers a list of instructions reads before it writes them, in order. -/
def readsFirst (is : List LinstrR) : List String :=
  (is.foldl (fun (acc : List String × List String) i =>
    let rs := (srcsOf i).filter fun x => !acc.2.contains x && !acc.1.contains x
    (acc.1 ++ rs, acc.2 ++ dstsOf i)) ([], [])).1

/-- The registers a list of instructions writes, without repetition. -/
def writesOf (is : List LinstrR) : List String := (is.flatMap dstsOf).eraseDups

/-- The guard `CMP ctr, 0` of a counted loop on the counter `ctr`. -/
def cmpZero? : LinstrR → Option String
  | .Lopn [.reg c] opn [.reg c', .imm 0] =>
      if c == c' && opn == "CMP:64" then some c else none
  | _ => none

/-- The back edge `jnz top` to the label `top`. -/
def backEdge? (top : LLabel) : LinstrR → Bool
  | .Lcond (.reg c) l => c == "NZ" && l == top
  | _ => false

/-- The head of a counted loop at the instruction `g` followed by `rest`: the zero-trip
    guard `CMP ctr, 0; jz exit` and the top label, with the counter, the exit label, the top
    label and the instructions behind the top label. -/
def loopHead? (g : LinstrR) : List LinstrR → Option (String × LLabel × LLabel × List LinstrR)
  | .Lcond (.reg c) ex :: .Llabel _ top :: rest =>
      if c == "Z" then (cmpZero? g).map fun ctr => (ctr, ex, top, rest) else none
  | _ => none

/-- The step `op r, 1` of the mnemonic `op` on the register `r`. -/
def stepOne? (mn : String) : LinstrR → Option String
  | .Lopn [.reg c] opn [.reg c', .imm 1] => if c == c' && opn == mn then some c else none
  | _ => none

/-- The split of `xs` at the first instruction satisfying `p`: the instructions in front of
    it, the instruction, and the instructions behind it. -/
def splitAt? (p : LinstrR → Bool) (xs : List LinstrR) :
    Option (List LinstrR × LinstrR × List LinstrR) :=
  match xs.findIdx? p with
  | some k => xs[k]?.map fun i => (xs.take k, i, xs.drop (k + 1))
  | none => none

/-- The level of the location `x` at the width `64`, materialising an immediate. -/
def RSt.levelOf (s : RSt) (x : String) : Except String (RSt × Nat) :=
  match s.get? x with
  | some v => .ok ((s.noteArg x v).level 64 v)
  | none => .error s!"program: the location {x} holds no value at a loop boundary"

/-- The levels of the locations `xs` at the width `64`, materialising immediates. -/
def RSt.levelList (s : RSt) : List String → Except String (RSt × List Nat)
  | [] => .ok (s, [])
  | x :: xs => do
      let (s, l) ← s.levelOf x
      let (s, ls) ← s.levelList xs
      pure (s, l :: ls)

/-- **The symbolic reading of a printed body** from the state `s`, with the registers `out`
    read after the code. A counted loop of the shape of `forArrFrame` (the zero-trip guard
    `CMP ctr, 0; jz exit`, the top label, the body, the steps `ADD idx, 1` and
    `SUB ctr, 1`, the guard `CMP ctr, 0; jnz top`, the exit label) is read as a loop item:
    its carried registers are the registers its body writes and that the body or the code
    after the loop reads before writing, other than the counter and the trip index; they are
    seeded from their values in front of the loop, the trip index is the level `d`, and the
    carried register `j` the level `d + |cs| - j` in the body. Every other instruction is
    read by `readInstr`. Each call reads a strictly shorter list than its caller, so the
    fuel `fuel` reads every list of fewer than `fuel` instructions. -/
def readCode (out : List String) (s : RSt) : Nat → List LinstrR → Except String RSt
  | _, [] => .ok s
  | 0, _ :: _ => .error "program: out of fuel"
  | fuel + 1, g :: rest =>
    match loopHead? g rest with
    | none => do
        let s ← readInstr s g
        readCode out s fuel rest
    | some (ctr, ex, top, rest) => do
          let (region, _, after) ← match splitAt? (backEdge? top) rest with
            | some r => pure r
            | none => throw s!"program: no back edge to the label {top}"
          let after ← match after with
            | .Llabel _ l :: a =>
                (if l == ex then pure a
                  else throw "program: the exit label does not follow the back edge")
            | _ => throw "program: the exit label does not follow the back edge"
          let rrev := region.reverse
          let (rrev, ctr') ← match rrev with
            | c :: r =>
                (match cmpZero? c with
                  | some c' => pure (r, c')
                  | none => throw "program: no guard in front of the back edge")
            | [] => throw "program: empty loop"
          let rrev ← match rrev with
            | i :: r =>
                (if stepOne? "SUB:64" i == some ctr then pure r
                  else throw "program: the counter is not decremented in front of the guard")
            | [] => throw "program: no counter step"
          let (rrev, idx) := match rrev with
            | i :: r =>
                (match stepOne? "ADD:64" i with
                  | some x => (r, some x)
                  | none => (rrev, none))
            | [] => (rrev, none)
          if ctr' != ctr then
            throw "program: the two guards test different counters"
          let body := rrev.reverse
          let skip := ctr :: idx.toList
          let W := (writesOf body).filter fun r => !skip.contains r
          let rb := readsFirst body
          let ra := readsFirst after ++ out
          let C := W.filter fun r => rb.contains r || ra.contains r
          let (s, cl) ← s.levelOf ctr
          let (s, inits) ← s.levelList C
          let D := s.depth
          let n := C.length
          let outerPairs : List String → List (String × String) := fun rs =>
            rs.filterMap fun r => match s.get? r with
              | some (.lvl l) =>
                  if C.contains r then none
                  else some (if l < s.nArgs then argName l else regName l, r)
              | _ => none
          let entry := (loopCtr top, ctr) :: idx.toList.map (regName D, ·)
            ++ C.zipIdx.map (fun p => (regName (D + n - p.2), p.1)) ++ outerPairs rb
          let exit := outerPairs ra
          let sb0 : RSt :=
            { loc := ((s.loc.filter fun p => !(skip ++ W).contains p.1)
                ++ idx.toList.map (·, Val.lvl D))
                ++ C.zipIdx.map (fun p => (p.1, Val.lvl (D + n - p.2))),
              depth := D + 1 + n, items := [], nArgs := s.nArgs, pairs := [], uses := [] }
          let sb ← readCode C sb0 fuel body
          let (sb, bret) ← sb.levelList C
          let s' : RSt :=
            { loc := (s.loc.filter fun p => !(skip ++ W).contains p.1)
                ++ C.zipIdx.map (fun p => (p.1, Val.lvl (D + n - 1 - p.2))),
              depth := D + n,
              items := s.items ++ [.loop cl (C.map fun _ => JasminTy.reg 64) inits sb.items bret],
              nArgs := s.nArgs, pairs := s.pairs ++ entry ++ sb.pairs ++ exit,
              uses := s.uses ++ sb.uses }
          readCode out s' fuel after

/-- The location the layout `σ` reads a register result from, under its export name. -/
def resultLoc? (σ : AbiLayout) : Option String :=
  match σ.result with
  | .reg r => some (exportReg r)
  | _ => none

/-- **The untyped program of a printed body** at the layout `σ`: the parameter `j` of `σ`
    is the level `j`, held in the export name of its register; the result is the level of
    the result register of `σ` at the end. The second component is the export names read
    at a loop boundary, each with the location that holds it. -/
def readProg (σ : AbiLayout) (body : Lcmd) :
    Except String (UProg × List (String × String)) := do
  let r ← match resultLoc? σ with
    | some r => pure r
    | none => throw "program: the result of the layout is not a register"
  let s0 : RSt := { loc := σ.args.zipIdx.map (fun p => (exportReg p.1.reg, Val.lvl p.2)),
                    depth := σ.args.length, items := [], nArgs := σ.args.length }
  let s ← readCode [r] s0 (body.length + 1) (body.map (·.li_i))
  let (s, l) ← s.levelOf r
  pure (toUProg σ.args.length s.items [l], s.pairs ++ s.uses)

/-! ## 4. The candidate and its check -/

/-- **The certificate of the proposer**: the first location of each export name of `ps`, the
    pairs the reading records, followed by each parameter `j` of the layout that `ps` does
    not name at the export name of its register. -/
def certOf (σ : AbiLayout) (ps : List (String × String)) : List (String × String) :=
  let firsts := ps.foldl (fun acc p => if acc.any (·.1 == p.1) then acc else acc ++ [p]) []
  firsts ++ (σ.args.zipIdx.map fun p => (argName p.2, exportReg p.1.reg)).filter
    fun p => !firsts.any (·.1 == p.1)

/-- **The candidate of the bytes** at the layout `σ`, the context `Γ` and the result type
    `t`: the printed body `liftBody`, the program `readProg` elaborated at `Γ` and `[t]`, and
    the certificate `certOf`; the error names the first step that fails. -/
def proposeCand (σ : AbiLayout) (_fn : String) (Γ : Ctxt jasminDialect) (t : JasminTy)
    (bytes : List (BitVec 8)) : Except String (DecompCand Γ t) := do
  let body ← liftBody bytes
  let (u, ps) ← readProg σ body
  let p ← elabProg Γ [t] u
  pure ⟨p, body, certOf σ ps⟩

/-- The conjuncts of `decompileB` on a candidate, each with its name, in the order of the
    check. -/
def candConjuncts (σ : AbiLayout) (fn : String) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : DecompCand Γ t) (bytes : List (BitVec 8)) : List (String × Bool) :=
  let r := exportR Γ.length fn c.p Γ.length 0
  [("regionExportableB", regionExportableB c.p), ("callFree", c.p.callFree),
   ("exportR", r.isSome),
   ("regionCoB", match r with
      | some r => regionCoB σ exportReg c.body t r.code r.res c.cert | none => false),
   ("regionCtB", match r with
      | some r => regionCtB σ exportReg c.body t r.code r.res c.cert | none => false),
   ("encodeLfundefBytesChecked", decide (encodeLfundefBytesChecked c.body = some bytes))]

/-- **The check of the proposer's candidate**: `accept` when `decompileB` accepts the
    candidate of `proposeCand`, otherwise the failing step of the proposer or the first
    conjunct of `decompileB` that refuses. -/
def checkCand (σ : AbiLayout) (fn : String) (Γ : Ctxt jasminDialect) (t : JasminTy)
    (bytes : List (BitVec 8)) : String :=
  match proposeCand σ fn Γ t bytes with
  | .error e => "propose: " ++ e
  | .ok c =>
      if decompileB σ fn c bytes then "accept"
      else
        match (candConjuncts σ fn c bytes).find? (fun q => !q.2) with
        | some q => "refused at " ++ q.1
        | none => "refused"

end CatCrypt.Crypto.SecureCompilation.Haxc.DecompilePropose
