/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.SpillSlotEncode
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SpillSlotEncode
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrMnemDispatch
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrMnemDispatch

/-!
# `GatherMemOps` — the array-ABI memory-operand gather arms

The framed array ABI (`JasminLprogExport.framedAbiLowerBody`,
`ComL.toLfundefPhysFramedAbi`) lowers a register-indexed element access to a
constant-offset word move whose memory side is a `mem.<base>.<off>` operand
name carried in an `LOperand.reg`:

* `Lopn [.reg (mem.<base>.<off>)] "STORE:64" [.reg src]` — `movq %src, off(%base)`;
* `Lopn [.reg dst] "LOAD:64" [.reg (mem.<base>.<off>)]` — `movq off(%base), %dst`.

`LprogBytes.encodeLopn` encodes both: the mnemonic dispatch resolves
`STORE`/`LOAD` through `aluOpcode` to `0x89`/`0x8b` at `REX.W = 1` (the `:64`
tag) and lands in `encTwoAddr`, whose memory arms parse the operand name with
`parseMemName` and emit `encMemMovw`. The `JInstr` side has the matching
constructors `storeMem` / `loadMem`, which `ScalarEncoder.encodeJInstr` encodes
through `encMemMov` at a hardcoded `REX.W = 1` — the same bytes at `w = 1`.

## Main results

* `memNameParts` — the `mem.<base>.<off>` operand-name parse that keeps the base
  as a NAME (the form `JInstr.storeMem` / `JInstr.loadMem` take), with
  `parseMemName_of_memNameParts` relating it to `LprogBytes.parseMemName`.
* `lowerMemOp` — the two gather arms, `none` on every other shape.
* `lowerCov6` / `gatherJBlock6` — `SpillSlotEncode.lowerCov5` with `lowerMemOp`
  as the fallback, and the whole-body gather over it.
* `encodeLopn_store64` / `encodeLopn_load64` — the closed-mnemonic dispatch of
  `STORE:64` / `LOAD:64` down to `encTwoAddr` at `w = 1`.
* `store64_gather_bytes_agree` / `load64_gather_bytes_agree` — the byte
  agreement: the gathered block encodes to exactly the bytes `encodeLopn` gives
  for the same `Lopn`, under the resolver-agreement side conditions.
* `encJStoreMem_RSP24` / `encJLoadMem_RSP24` — the same agreement at concrete
  operands under `physAlloc`, by `decide +kernel`.

## Scope

The arms fire only on the `:64`-tagged mnemonics. An untagged `STORE`/`LOAD`
carries `mnemWidth = 32`, so `encodeLopn` encodes it at `REX.W = 0` while
`encMemMov` is fixed at `REX.W = 1`; those shapes stay rejected. A base or
source name outside the sixteen `isGpName` names is rejected as well, rather
than lowered to a block that would address `%rax`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.GatherMemOps

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter (GpAlloc regOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (frameSize bodyIsU64 qsaveBytes qsaveBytesFor)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended (isLret)
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpillSlotEncode
  (lowerCov5 isFrameDirective)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrBytesAgree
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrMnemDispatch
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather (physAlloc)

/-! ## 1. The memory-operand name parse -/

/-- Parse a `mem.<base>.<off>` operand name to its base register NAME and
    offset. `LprogBytes.parseMemName` returns the base's SDM number; the `JInstr`
    memory constructors take the base as a name (resolved through the
    allocation), so this variant keeps the name. `none` when the name is not a
    `mem.*` operand or its offset is not a digit string. -/
def memNameParts (n : String) : Option (String × Int) :=
  if hasPrefix n "mem." then
    match (n.toList.drop 4).span (· != '.') with
    | (base, '.' :: off) =>
        match natOfDigits? off with
        | some o => some (String.ofList base, Int.ofNat o)
        | none => none
    | _ => none
  else none

/-- `memNameParts` and `LprogBytes.parseMemName` split the same name the same
    way: the base name `memNameParts` returns numbers to the base
    `parseMemName` returns, at the same offset. -/
theorem parseMemName_of_memNameParts {n b : String} {off : Int}
    (h : memNameParts n = some (b, off)) :
    parseMemName n = some (gpNumU b, off) := by
  unfold memNameParts at h
  unfold parseMemName
  split at h
  · rename_i hp
    rw [if_pos hp]
    split at h
    · split at h
      · simp_all
      · simp at h
    · simp at h
  · simp at h

/-! ## 2. The gather arms

`lowerMemOp` lowers the two array-ABI memory shapes and returns `none` on
everything else, so it composes below an existing lowering as a fallback. The
`frame` / `spillW` / `qsaveB` parameters are not read: a `mem.*` operand carries
its own base and offset, unlike a `k.`/`qsave.` slot, whose offset
`SpillSlotEncode.lowerCov5` resolves from the frame. They are in the signature
so the arm composes at the same type as the rest of the chain. -/

/-- The array-ABI memory-operand lowering. A `STORE:64` whose destination is a
    `mem.<base>.<off>` name lowers to `JInstr.storeMem base off (.reg src)`; a
    `LOAD:64` whose source is one lowers to `JInstr.loadMem dst base off`. Both
    arms require the base and the register operand to be among the sixteen
    `isGpName` names. Every other shape is `none`. -/
def lowerMemOp (_frame _spillW : Nat) (i : LinstrR)
    (_qsaveB : Nat := qsaveBytes) : Option (List (JInstr 64)) :=
  match i with
  | .Lopn [.reg dn] "STORE:64" [.reg sn] =>
      match memNameParts dn with
      | some (b, off) =>
          if isGpName b && isGpName sn then some [JInstr.storeMem b off (.reg sn)]
          else none
      | none => none
  | .Lopn [.reg dn] "LOAD:64" [.reg sn] =>
      match memNameParts sn with
      | some (b, off) =>
          if isGpName b && isGpName dn then some [JInstr.loadMem dn b off]
          else none
      | none => none
  | _ => none

/-- The `STORE:64` arm's output. -/
theorem lowerMemOp_store (frame spillW qsaveB : Nat) (dn sn b : String) (off : Int)
    (h : memNameParts dn = some (b, off))
    (hb : isGpName b = true) (hs : isGpName sn = true) :
    lowerMemOp frame spillW (.Lopn [.reg dn] "STORE:64" [.reg sn]) qsaveB
      = some [JInstr.storeMem b off (.reg sn)] := by
  simp [lowerMemOp, h, hb, hs]

/-- The `LOAD:64` arm's output. -/
theorem lowerMemOp_load (frame spillW qsaveB : Nat) (dn sn b : String) (off : Int)
    (h : memNameParts sn = some (b, off))
    (hb : isGpName b = true) (hd : isGpName dn = true) :
    lowerMemOp frame spillW (.Lopn [.reg dn] "LOAD:64" [.reg sn]) qsaveB
      = some [JInstr.loadMem dn b off] := by
  simp [lowerMemOp, h, hb, hd]

/-- `SpillSlotEncode.lowerCov5` with the array-ABI memory arms underneath: the
    spill-slot-aware lowering first, `lowerMemOp` on the shapes it declines. -/
def lowerCov6 (frame spillW : Nat) (i : LinstrR)
    (qsaveB : Nat := qsaveBytes) : Option (List (JInstr 64)) :=
  match lowerCov5 frame spillW i qsaveB with
  | some js => some js
  | none => lowerMemOp frame spillW i qsaveB

/-- Lower a full `Linstr` (drops the position tag) through `lowerCov6`. -/
def lowerCov6L (frame spillW : Nat) (i : Linstr)
    (qsaveB : Nat := qsaveBytes) : Option (List (JInstr 64)) :=
  lowerCov6 frame spillW i.li_i qsaveB

/-- `lowerCov5` declines the array-ABI store, so `lowerCov6` reaches the new
    arm: the `mem.*` destination is not a `k.`/`qsave.` slot and `STORE:64` is in
    none of the ALU, shift or flag tables the chain below it dispatches on. -/
theorem lowerCov6_store_RSP24 :
    lowerCov6 64 64 (.Lopn [.reg "mem.RSP.24"] "STORE:64" [.reg "RAX"])
      = some [JInstr.storeMem "RSP" (24 : Int) (.reg "RAX")] := by
  with_unfolding_all rfl

/-- `lowerCov5` declines the array-ABI load, so `lowerCov6` reaches the new arm. -/
theorem lowerCov6_load_RSP24 :
    lowerCov6 64 64 (.Lopn [.reg "RAX"] "LOAD:64" [.reg "mem.RSP.24"])
      = some [JInstr.loadMem "RAX" "RSP" (24 : Int)] := by
  with_unfolding_all rfl

/-- The whole-body gather over `lowerCov6`: `SpillSlotEncode.gatherJBlock5` with
    the array-ABI memory arms added. The trailing `Lret` and the frame-size
    directives are dropped and the frame size, spill width and qsave block size
    are read from the body the way `LprogBytes.encodeLcmd` reads them. -/
def gatherJBlock6 (body : List Linstr) : Option (List (JInstr 64)) :=
  let frame := frameSize body
  let spillW := if bodyIsU64 body then 64 else 32
  let qsaveB := qsaveBytesFor body
  ((body.filter (fun i => !isLret i && !isFrameDirective i)).mapM
    (fun i => lowerCov6L frame spillW i qsaveB)).map List.flatten

/-! ## 3. The mnemonic dispatch on the tagged memory mnemonics

`LprogJInstrMnemDispatch.dispatch_alu_one` at the two closed mnemonics. Both
carry the `:64` tag, so `rexW (mnemWidth _) = 1`, and `aluOpcode` resolves
`STORE` to `0x89` and `LOAD` to `0x8b`; each dispatch guard is a closed-string
fact the kernel reduces. -/

/-- `STORE:64` (opcode `0x89`, `w = 1`) dispatches to `encTwoAddr`. -/
theorem encodeLopn_store64 (frame spillW : Nat) (dn sn : String) (qsaveB : Nat) :
    encodeLopn frame spillW (.Lopn [.reg dn] "STORE:64" [.reg sn]) qsaveB
      = encTwoAddr frame spillW 1 0x89 (.reg dn) (.reg sn) qsaveB :=
  dispatch_alu_one frame spillW 0x89 "STORE:64" "STORE" dn sn qsaveB
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `LOAD:64` (opcode `0x8b`, `w = 1`) dispatches to `encTwoAddr`. -/
theorem encodeLopn_load64 (frame spillW : Nat) (dn sn : String) (qsaveB : Nat) :
    encodeLopn frame spillW (.Lopn [.reg dn] "LOAD:64" [.reg sn]) qsaveB
      = encTwoAddr frame spillW 1 0x8b (.reg dn) (.reg sn) qsaveB :=
  dispatch_alu_one frame spillW 0x8b "LOAD:64" "LOAD" dn sn qsaveB
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! ## 4. The byte agreement

Each arm's gathered block encodes to exactly the bytes `encodeLopn` gives for
the same `Lopn`. The side conditions are the covered-domain ones the rest of the
byte agreement carries (`LprogJInstrBytesAgree` §2b): the operand that is not
the memory side is neither a spill/qsave nor a `mem.*` name, and the allocation
resolves each `JInstr` name to the SDM number the Lprog side reads off the
operand name. -/

/-- `encodeJBlock` on a one-instruction block is that instruction's encoding. -/
theorem encodeJBlock_singleton (alloc : GpAlloc) (i : JInstr 64) :
    encodeJBlock alloc [i] = encodeJInstr alloc i := by
  simp [encodeJBlock]

/-- **The `STORE:64` byte agreement.** The gathered `storeMem` block encodes to
    the bytes `encodeLopn` gives for the array-ABI store. -/
theorem store64_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dn sn b : String) (off : Int) (qsaveB : Nat)
    (hd : memNameParts dn = some (b, off))
    (hb : isGpName b = true) (hs : isGpName sn = true)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hr : gpNum (regOf alloc sn) = gpNumU sn)
    (hbr : gpNum (regOf alloc b) = gpNumU b) :
    (lowerMemOp frame spillW (.Lopn [.reg dn] "STORE:64" [.reg sn]) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW (.Lopn [.reg dn] "STORE:64" [.reg sn]) qsaveB) := by
  rw [lowerMemOp_store frame spillW qsaveB dn sn b off hd hb hs, Option.map_some,
    encodeJBlock_singleton, encodeLopn_store64,
    store_bytes_agree alloc frame spillW 0x89 b off sn dn sn (gpNumU b) qsaveB
      hdk hsk (parseMemName_of_memNameParts hd) hsm hdsp hssp hr hbr]

/-- **The `LOAD:64` byte agreement.** The gathered `loadMem` block encodes to the
    bytes `encodeLopn` gives for the array-ABI load. -/
theorem load64_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dn sn b : String) (off : Int) (qsaveB : Nat)
    (hs : memNameParts sn = some (b, off))
    (hb : isGpName b = true) (hd : isGpName dn = true)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemName dn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hr : gpNum (regOf alloc dn) = gpNumU dn)
    (hbr : gpNum (regOf alloc b) = gpNumU b) :
    (lowerMemOp frame spillW (.Lopn [.reg dn] "LOAD:64" [.reg sn]) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW (.Lopn [.reg dn] "LOAD:64" [.reg sn]) qsaveB) := by
  rw [lowerMemOp_load frame spillW qsaveB dn sn b off hs hb hd, Option.map_some,
    encodeJBlock_singleton, encodeLopn_load64,
    load_bytes_agree alloc frame spillW 0x8b dn b off dn sn (gpNumU b) qsaveB
      hdk hsk hdm (parseMemName_of_memNameParts hs) hdsp hssp hr hbr]

/-! ## 5. The agreement at concrete operands

The same two statements with every name and offset closed, under the physical
allocation `PhysBodyGather.physAlloc`, so the side conditions are discharged by
reduction rather than assumed. `movq %rax, 24(%rsp)` and its reload are the
shapes `framedAbiLowerBody` emits for a frame-local array element. -/

/-- The gathered `movq %rax, 24(%rsp)` store byte-matches `encodeLopn`. -/
theorem encJStoreMem_RSP24 :
    encodeJBlock physAlloc [JInstr.storeMem "RSP" (24 : Int) (.reg "RAX")]
      = encodeLopn 64 64 (.Lopn [.reg "mem.RSP.24"] "STORE:64" [.reg "RAX"]) := by
  decide +kernel

/-- The gathered `movq 24(%rsp), %rax` load byte-matches `encodeLopn`. -/
theorem encJLoadMem_RSP24 :
    encodeJBlock physAlloc [JInstr.loadMem "RAX" "RSP" (24 : Int)]
      = encodeLopn 64 64 (.Lopn [.reg "RAX"] "LOAD:64" [.reg "mem.RSP.24"]) := by
  decide +kernel

/-- The gathered `movq %r13, 8(%rdi)` store byte-matches `encodeLopn` (an
    extended base and an extended source, so both REX bits are exercised). -/
theorem encJStoreMem_RDI8_R13 :
    encodeJBlock physAlloc [JInstr.storeMem "RDI" (8 : Int) (.reg "R13")]
      = encodeLopn 64 64 (.Lopn [.reg "mem.RDI.8"] "STORE:64" [.reg "R13"]) := by
  decide +kernel

/-- The gathered `movq 8(%rdi), %r13` load byte-matches `encodeLopn`. -/
theorem encJLoadMem_RDI8_R13 :
    encodeJBlock physAlloc [JInstr.loadMem "R13" "RDI" (8 : Int)]
      = encodeLopn 64 64 (.Lopn [.reg "R13"] "LOAD:64" [.reg "mem.RDI.8"]) := by
  decide +kernel

end CatCrypt.Crypto.SecureCompilation.X86Backend.GatherMemOps
