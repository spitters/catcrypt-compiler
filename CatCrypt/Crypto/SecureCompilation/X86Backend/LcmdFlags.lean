/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Export
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# The flag effect of an owned-RA instruction

`Lstate` carries no flags, so the store theorems of the `Lcmd` passes say nothing
about them. A pass that moves, deletes or rewrites a flag writer therefore needs a
side condition stated on the printed instructions. This module classifies each
`Linstr` by its effect on the x86 flags as `LprogAsmPrinter.renderLinstrR` prints it,
and derives from that one classification the forward liveness scan used by the
segmenting of `LprogOptPipeline.optimizeBasicBlocks` and the backward liveness step
used by `LcmdLea.leaBody`.

## The classification

* readers of an earlier instruction's flags: `ADC`, `SBB`, `RCL`, `RCR`, a two-source
  `CMOV<cc>`, a single-source `SET<cc>`, an `ADOX`/`ADOXHI`, a two-source `ADCX`, an
  `ADCX` whose carry-in is `LprogAsmPrinter.cfCarrySentinel`, an `ADCXHI` (printed as
  `setc`), and the conditional branch `Lcond`. The `ADCX` family and `ADCXHI` read
  only the carry flag.
* writers of every flag a reader consumes: the two-operand ALU class, `CMP`, `TEST`,
  `NEG`, `MUL`, `IMUL`, the three-source `CMOV` (printed after its own `test`) and the
  two-source `SET<cc>` (printed after its own `cmp`). `MUL` and `IMUL` leave the sign
  and zero flags undefined, so no earlier value of them is observable after.
* the three-source `ADCX` with a value carry-in, printed as `bt $0, cin; adcx`: it
  rewrites the carry flag and reads no earlier flag.
* flag-neutral: moves, loads, stores, `LEA`, `MULX`.
* other known writers that read no flag: shifts and rotates, `ANDN`, `MULXHI`, `BT`,
  `NOT`, `TRUNC`, the vector mnemonics and the frame annotations.
* every other `Lopn` is unclassified and is treated as a possible reader.

## Main results

* `flagEffect` — the classification.
* `readsPrevFlags`, `flagKill`, `flagNeutral` — the reader, full-writer and neutral
  tests derived from it.
* `flagsLive` — the forward scan: an earlier flag value may be read at the start of a
  list.
* `flagHold` — a run that may write a flag still live at the start of a list.
* `flagsLiveStep` — one backward step of the flags-live bit.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdFlags

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (cfCarrySentinel)

/-- The effect of one printed instruction on the x86 flags. -/
inductive FlagEffect where
  /-- Reads a flag an earlier instruction set (any flag). -/
  | reads
  /-- Reads the carry flag an earlier instruction set, and no other flag. -/
  | readsCF
  /-- Overwrites every flag a reader consumes, reading none. -/
  | kills
  /-- Overwrites the carry flag, reading none. -/
  | writesCF
  /-- May write some flags, reading none. -/
  | writes
  /-- Reads and writes no flag. -/
  | neutral
  /-- An `Lopn` outside the classified alphabet. -/
  | unknown
  /-- A code label: the fall-through path continues past it. -/
  | label
  /-- The return. -/
  | ret
  /-- Any other control transfer or barrier (jump, call, system call). -/
  | barrier
  deriving DecidableEq, Repr

/-- The mnemonic bases that read and write no flag. -/
def neutralBases : List String :=
  ["MOV", "MOVQ", "MOV:8", "MOV:16", "LOADIDX", "STOREIDX", "LOAD", "STORE", "LOADSYM",
   "MULX", "MULXMEM", "LEA"]

/-- The mnemonic bases that overwrite every flag a reader consumes. -/
def killBases : List String :=
  ["ADD", "SUB", "AND", "OR", "XOR", "CMP", "TEST", "NEG", "MUL", "IMUL"]

/-- The known mnemonic bases that may write flags and read none, beyond the full
    writers: shifts and rotates (with or without a count tag), `ANDN`, `MULXHI`, `BT`,
    `NOT`, `TRUNC`, the vector mnemonics and the frame annotations. -/
def writerBase (b : String) : Bool :=
  b.startsWith "SHL" || b.startsWith "SHR" || b.startsWith "SAR" || b.startsWith "ROL"
    || b.startsWith "ROR" || b.startsWith "V"
    || ["ANDN", "MULXHI", "BT", "NOT", "TRUNC", "FRAME", "FRAMEADD"].contains b

/-- The flag effect of an `Lopn` with mnemonic `opn` and sources `srcs`. -/
def opnEffect (opn : String) (srcs : List LOperand) : FlagEffect :=
  let b := stripWidthTag opn
  let n := srcs.length
  let fusedCin := srcs.getLast? == some (LOperand.reg cfCarrySentinel)
  if b == "ADCXHI" then .readsCF
  else if b == "ADOXHI" || b == "ADOX" then .reads
  else if b == "ADCX" then (if n < 3 || fusedCin then .readsCF else .writesCF)
  else if (b.startsWith "CMOV" && n < 3) || b == "ADC" || b == "SBB" || b == "RCL"
      || b == "RCR" || (b.startsWith "SET" && n < 2) then .reads
  else if killBases.contains b || (b.startsWith "CMOV" && n == 3)
      || (b.startsWith "SET" && n == 2) then .kills
  else if neutralBases.contains b then .neutral
  else if writerBase b then .writes
  else .unknown

/-- The flag effect of a printed instruction. -/
def flagEffect (i : Linstr) : FlagEffect :=
  match i.li_i with
  | .Lopn _ opn srcs => opnEffect opn srcs
  | .Lcond _ _ => .reads
  | .Llabel _ _ => .label
  | .Lret => .ret
  | .Lalign => .neutral
  | _ => .barrier

/-- The instruction reads a flag an earlier instruction set. -/
def readsPrevFlags (i : Linstr) : Bool :=
  match flagEffect i with
  | .reads | .readsCF => true
  | _ => false

/-- The instruction overwrites every flag a later reader can consume. -/
def flagKill (i : Linstr) : Bool := flagEffect i == .kills

/-- The instruction writes no flag: a flag-neutral `Lopn`, or an instruction that is
    not an `Lopn`. A run of such instructions leaves the flags as it found them. -/
def flagNeutral (i : Linstr) : Bool :=
  match i.li_i with
  | .Lopn _ _ _ => flagEffect i == .neutral
  | _ => true

/-- The forward scan behind `flagsLive`. `cfFresh` records that the carry flag has
    been overwritten since the start of the scan; a carry-only reader then reads the
    overwritten carry, not the value present at the start. -/
def flagsLiveAux (cfFresh : Bool) : List Linstr → Bool
  | [] => false
  | i :: rest =>
      match flagEffect i with
      | .reads => true
      | .readsCF => if cfFresh then flagsLiveAux cfFresh rest else true
      | .kills => false
      | .writesCF => flagsLiveAux true rest
      | .writes | .neutral | .label => flagsLiveAux cfFresh rest
      | .unknown | .barrier => true
      | .ret => false

/-- A flag value present at the start of `l` may be read: a reader comes before any
    instruction that overwrites it and before the return. A label is passed through
    along the fall-through path; a jump, a call and an unclassified `Lopn` count as
    readers. -/
def flagsLive (l : List Linstr) : Bool := flagsLiveAux false l

/-- The run `cur` may write a flag that is live at the start of `l`. -/
def flagHold (cur l : List Linstr) : Bool := cur.any (fun i => !flagNeutral i) && flagsLive l

/-- One backward step of the flags-live bit: `live` is the bit after `i`, the result
    the bit before it. A reader, an unclassified `Lopn` and every instruction that is
    not an `Lopn` leave the flags live; a full writer clears the bit; any other `Lopn`
    passes it through. -/
def flagsLiveStep (i : Linstr) (live : Bool) : Bool :=
  match i.li_i with
  | .Lopn _ _ _ =>
      match flagEffect i with
      | .kills => false
      | .writesCF | .writes | .neutral => live
      | _ => true
  | _ => true

end CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdFlags
