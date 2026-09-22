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
# `GatherMemOps` — the array-ABI memory-operand and carry-chain gather arms

The framed array ABI (`JasminLprogExport.framedAbiLowerBody`,
`ComL.toLfundefPhysFramedAbi`) lowers a register-indexed element access to a
constant-offset word move whose memory side is a `mem.<base>.<off>` operand
name carried in an `LOperand.reg`:

* `Lopn [.reg (mem.<base>.<off>)] "STORE:64" [.reg src]` — `movq %src, off(%base)`;
* `Lopn [.reg dst] "LOAD:64" [.reg (mem.<base>.<off>)]` — `movq off(%base), %dst`;
* `Lopn [.reg dst] "LEA:64" [.reg (mem.<base>.<off>)]` — `leaq off(%base), %dst`,
  the address itself, with no memory access.

`LprogBytes.encodeLopn` encodes both moves: the mnemonic dispatch resolves
`STORE`/`LOAD` through `aluOpcode` to `0x89`/`0x8b` at `REX.W = 1` (the `:64`
tag) and lands in `encTwoAddr`, whose memory arms parse the operand name with
`parseMemName` and emit `encMemMovw`. The `JInstr` side has the matching
constructors `storeMem` / `loadMem`, which `ScalarEncoder.encodeJInstr` encodes
through `encMemMov` at a hardcoded `REX.W = 1` — the same bytes at `w = 1`.
`LEA` is in none of the ALU, shift or `0F`-map tables, so it falls through the
whole mnemonic dispatch to `encodeLopn`'s last one-source arm, which resolves the
source name with `parseMemNameGp` and emits `encMemMovw w 0x8d`. The matching
`JInstr` constructor is `lea` at scale `0`, which `ScalarEncoder.encodeJInstr`
encodes as `encMemMov 0x8d` — the index-free `[base + disp]` form.

The same module carries the two in-place carry-chain mnemonics
`Lopn [.reg dst] "ADC:64" [.reg dst, s]` and its `SBB:64` dual, the shapes the
Curve25519 ladder step's carry chains are exported in. They are the two entries
of `LprogBytes.aluOpcode` (`ADC` at `0x11`, `SBB` at `0x19`) that
`LoweringExtended.lowerAluJ`, the mnemonic table the lowering below this gather
dispatches on, has no row for; every other entry of `aluOpcode` is either in that
table or is a memory mnemonic covered by the arms above. The two-source dispatch
resolves both to `encTwoAddr` at `REX.W = 1` exactly as `ADD:64` and `SUB:64`
resolve, and the matching `JInstr` constructors `adc` / `sbb` encode as
`encAluRR 0x11` / `encAluRR 0x19` on a register source. Both are distinct from
the ADX carry chains `ADCX`/`ADOX`, which `LprogBytes.adxPrefix` routes to
`encAdxCarry` above the `aluOpcode` dispatch.

An immediate second source is gated on `aluImmGathers`, the signed 32-bit field
the group-1 immediate form carries.

The ADX carry chains are the mnemonics `LprogBytes.adxPrefix` routes: `ADCX` at
the mandatory prefix `0x66` and `ADOX` at `0xf3`, both to
`ScalarEncoder.encAdxCarry` on a branch of their own. Their carry-in is the CF or
OF flag rather than an operand, and the encoders hardcode `REX.W`, so the
dispatch does not read the width tag. The one-source and two-source shapes are
the arms here; on the two-source shape the first source is matched by a wildcard
and contributes no bytes, so the arm requires it to be the destination.

The three-source shape `[a, src, cin]`, which carries the carry-in as an explicit
value, is lowered above this module by
`LoweringExtendedCoverage.lowerLinstrExtCov`. `encodeLopn` gives it a three-
instruction sequence whose middle instruction is `encBtImm`, and `BT` is outside
the fragment `ScalarEncoder.encodableJInstr` admits, so no gather of that shape
agrees with it byte for byte.

The mem-folded widening multiply `Lopn [.reg lo, .reg hi] "MULXMEM:64" [.reg
(mem.<base>.<off>)]` is the one two-destination shape here. `encodeLopn` matches
`MULXMEM` by name above the ADX and ALU tables and emits
`ScalarEncoder.encMulxMem`, which takes the high word first, so the dispatch
transposes the destination pair; the multiplier is not an operand, since `MULX`
reads it implicitly in `%rdx`. `LoweringCoverageMulxMemSym.lowerLinstrExtCovMS`
carries a `MULXMEM` arm of a different shape — the untagged mnemonic over
`[a, .reg base, .imm off]`, with the destination pair in the opposite order —
which is the forward-compatible form for an exporter arm that does not exist;
neither its mnemonic nor its operand list nor its destination order matches what
`encodeLopn` reads.

## Main results

* `memNameParts` — the `mem.<base>.<off>` operand-name parse that keeps the base
  as a NAME (the form `JInstr.storeMem` / `JInstr.loadMem` take), with
  `parseMemName_of_memNameParts` relating it to `LprogBytes.parseMemName`.
* `lowerMemOp` — the four gather arms, `none` on every other shape.
* `lowerCov6` / `gatherJBlock6` — `SpillSlotEncode.lowerCov5` with `lowerMemOp`
  as the fallback, and the whole-body gather over it.
* `encodeLopn_store64` / `encodeLopn_load64` — the closed-mnemonic dispatch of
  `STORE:64` / `LOAD:64` down to `encTwoAddr` at `w = 1`.
* `dispatch_lea` / `encodeLopn_lea64` — the fall-through dispatch of `LEA:64`
  down to `encMemMovw 1 0x8d`.
* `store64_gather_bytes_agree` / `load64_gather_bytes_agree` /
  `lea64_gather_bytes_agree` — the byte agreement: the gathered block encodes to
  exactly the bytes `encodeLopn` gives for the same `Lopn`, under the
  resolver-agreement side conditions.
* `encJStoreMem_RSP24` / `encJLoadMem_RSP24` — the same agreement at concrete
  operands under `physAlloc`, by `decide +kernel`.
* `encJLea_RSP0_bytes` / `encJLea_R13_8_bytes` — the gathered `LEA:64` block's
  bytes at concrete operands, by `decide +kernel`.
* `encodeLopn_adc64₂` / `encodeLopn_sbb64₂` — the two-source dispatch of `ADC:64`
  and `SBB:64` down to `encTwoAddr` at opcodes `0x11` / `0x19`, `w = 1`.
* `dispatch_alu_imm₂` / `encImmOp_aluImm32` — the immediate two-source dispatch
  down to `encImmOp`, and its group-1 `81 /digit id` arm.
* `adc_bytes_agree` / `sbb_bytes_agree` and the four `*_gather_bytes_agree`
  theorems — the `JInstr`-side reductions and the byte agreement of each gathered
  block with `encodeLopn`.
* `encJAdc_RCX_RDX`, `encJSbb_R10_R11`, `encJAdcImm_RCX_1000`,
  `encJSbbImm_R10_1000` — the same agreements at concrete operands under
  `physAlloc`, by `decide +kernel`.
* `lowerMemOp_sbbImm0` — the gather at a small immediate, whose bytes agree with
  `encodeLopn` under `GatherImmForms.encodeJInstr7`.
* `dispatch_adx_two` / `dispatch_adx_one` and the four `encodeLopn_ad*64` — the
  ADX carry-chain dispatch of `ADCX:64` and `ADOX:64` down to `encAdxCarry`.
* `jinstr_adcx` / `jinstr_adox` and the four `ad*64*_gather_bytes_agree` — the
  carry-chain byte agreements.
* `encJAdcx_RSI_R9` / `encJAdox_RSI_R9` — the same at concrete operands.
* `dispatch_mulxmem` / `encodeLopn_mulxmem64` — the by-name dispatch of
  `MULXMEM:64` down to `encMulxMem`, with the destination pair transposed.
* `jinstr_mulxMem` / `mulxmem64_gather_bytes_agree` / `encJMulxMem_RDI160` — the
  mem-folded widening multiply's byte agreement, and it at concrete operands.

## What a byte agreement does not establish

A byte agreement compares this module's lowering against `encodeLopn`, so an arm
that reproduces `encodeLopn`'s own treatment of an operand satisfies it while
denoting something else. `encodeLopn` discards the first source of a two-address
ALU instruction and transposes the destination pair of `MULXMEM`; an arm that
discarded or transposed the same way would be byte-equal at every operand and
would say nothing about the instruction it lowers. Each arm below is written
from `encodeLopn`'s argument order and from the hardware's contract for an
operand the encoder does not read, and constrains the operands the encoder drops
rather than dropping them as well.

## Scope

The arms fire only on the `:64`-tagged mnemonics. An untagged `STORE`/`LOAD`
carries `mnemWidth = 32`, so `encodeLopn` encodes it at `REX.W = 0` while
`encMemMov` is fixed at `REX.W = 1`; those shapes stay rejected. A base or
source name outside the sixteen `isGpName` names is rejected as well, rather
than lowered to a block that would address `%rax`.

The `LEA:64` arm covers the register-base displacement form only: a source that
is a `mem.<base>.<off>` name over a tabulated base. An index-scaled address and
a `.rodata` symbol base are rejected, since neither is spelled as a `mem.*`
operand name on the Lprog side.

The `ADC:64` and `SBB:64` arms cover the in-place two-source form only: the first
source must be the destination name. `encodeLopn` discards the first source on
its `[d], [a, s]` ALU route, so at `a ≠ d` its bytes are the in-place instruction
while the `Lopn` denotes `d := a ± s ± CF`; the arms reject that shape rather
than lowering it to a block whose first source is dropped. Operands outside the
sixteen `isGpName` names are rejected as well.

An immediate second source is admitted over the whole signed 32-bit field
`aluImmGathers` names. Inside the sign-extended-imm8 range the live
`ScalarEncoder.encodeJInstr` and `LprogBytes.encImmOp` select different group-1
encodings of that instruction; both are valid and compute the same result, and
`GatherImmForms.encodeJInstr7` is the encoder that makes the same selection as
`encImmOp` and so agrees on bytes there. The agreements stated here against the
live encoder carry `fitsImm8S 1 v = false` for that reason.
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
  (frameSize bodyIsU64 qsaveBytes qsaveBytesFor mnemWidth isCarryOutBinding isMulHiBinding)
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
so the arm composes at the same type as the rest of the chain.

The two-source arms require the first source to be the destination, which the
physical export establishes by construction:
`JasminLprogExport.legalizeBinop` writes the destination as the binop's first
source in each of its four spill combinations, and `lowerTwoAddr` prepends
`legalizeMov dst s0` exactly on the branch where the two differ. The pre-register-
allocation form is the stated exception — `opToLinstrR`'s `regArith` arm binds a
fresh destination, so its first source is some other name — and it is not what
the byte encoders read. -/

/-- Is an immediate second source inside the signed 32-bit field the group-1
    `81 /digit id` form carries? This is `ScalarEncoder.encodableJInstr`'s own
    gate on an ALU immediate, so an arm admitting exactly these values lowers
    only to instructions that encoder encodes faithfully.

    Which of the two legal group-1 encodings each side then selects is a separate
    question from which values gather: `LprogBytes.encImmOp` takes the 4-byte
    `83 /digit ib` form inside the sign-extended-imm8 range and
    `ScalarEncoder.encodeJInstr` the 7-byte `81 /digit id` form at every value.
    Both encodings are valid and compute the same result; what differs inside
    that range is the agreement of the two byte streams, which
    `GatherImmForms.encodeJInstr7` reconciles by making the same selection. -/
def aluImmGathers (v : Nat) : Bool := fitsImm32S v

/-- The register the BMI2 widening multiply reads as its first multiplicand.
    `MULX` takes that operand implicitly in `%rdx`, so the `Lopn` source list
    does not carry it and the physical allocation pins the multiplier there. The
    `JInstr.mulxMem` constructor carries it as an explicit field, which
    `ScalarEncoder.encodeJInstr` does not read and `evalInstr` does, so naming it
    here is what keeps the lowered instruction's denotation the hardware's. -/
def mulxMultiplier : String := "RDX"

/-- The array-ABI memory-operand lowering. A `STORE:64` whose destination is a
    `mem.<base>.<off>` name lowers to `JInstr.storeMem base off (.reg src)`; a
    `LOAD:64` whose source is one lowers to `JInstr.loadMem dst base off`; a
    `LEA:64` whose source is one lowers to `JInstr.lea dst base base 0 off`, the
    address computation at scale `0`, where the index register contributes
    `idx * 0` to the address and neither `encodeJInstr` nor `evalInstr` reads its
    name, so the base name stands in for it. An `ADC:64` or `SBB:64` whose first
    source is its destination lowers to the in-place `JInstr.adc` / `JInstr.sbb`
    over a register second source, and over an immediate second source inside
    `aluImmGathers`. A `MULXMEM:64`, whose destination list is the low word then
    the high word and whose single source is a `mem.<base>.<off>` name, lowers to
    `JInstr.mulxMem` over the high word first, the order that constructor takes.
    An `ADCX:64` or `ADOX:64` over one register source, or over two whose first is
    the destination, lowers to the in-place `JInstr.adcx` / `JInstr.adox`. Every
    arm requires the base and the register operands to be among the sixteen
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
  | .Lopn [.reg dn] "LEA:64" [.reg sn] =>
      match memNameParts sn with
      | some (b, off) =>
          if isGpName b && isGpName dn then some [JInstr.lea dn b b 0 off]
          else none
      | none => none
  | .Lopn [.reg dn] "ADC:64" [.reg an, .reg sn] =>
      if an == dn && isGpName dn && isGpName sn then some [JInstr.adc dn (.reg sn)]
      else none
  | .Lopn [.reg dn] "SBB:64" [.reg an, .reg sn] =>
      if an == dn && isGpName dn && isGpName sn then some [JInstr.sbb dn (.reg sn)]
      else none
  | .Lopn [.reg dn] "ADC:64" [.reg an, .imm v] =>
      if an == dn && isGpName dn && aluImmGathers v then some [JInstr.adc dn (.imm v)]
      else none
  | .Lopn [.reg dn] "SBB:64" [.reg an, .imm v] =>
      if an == dn && isGpName dn && aluImmGathers v then some [JInstr.sbb dn (.imm v)]
      else none
  | .Lopn [.reg dn] "ADCX:64" [.reg an, .reg sn] =>
      if an == dn && isGpName dn && isGpName sn then some [JInstr.adcx dn (.reg sn)]
      else none
  | .Lopn [.reg dn] "ADOX:64" [.reg an, .reg sn] =>
      if an == dn && isGpName dn && isGpName sn then some [JInstr.adox dn (.reg sn)]
      else none
  | .Lopn [.reg dn] "ADCX:64" [.reg sn] =>
      if isGpName dn && isGpName sn then some [JInstr.adcx dn (.reg sn)] else none
  | .Lopn [.reg dn] "ADOX:64" [.reg sn] =>
      if isGpName dn && isGpName sn then some [JInstr.adox dn (.reg sn)] else none
  | .Lopn [.reg dlN, .reg dhN] "MULX:64" [.reg s2] =>
      if isGpName dlN && isGpName dhN && isGpName s2 then
        some [JInstr.mulx dhN dlN (.reg mulxMultiplier) (.reg s2)]
      else none
  | .Lopn [.reg dlN, .reg dhN] "MULXMEM:64" [.reg mn] =>
      match memNameParts mn with
      | some (b, off) =>
          if isGpName b && isGpName dlN && isGpName dhN then
            some [JInstr.mulxMem dhN dlN (.reg mulxMultiplier) b off]
          else none
      | none => none
  | .Lopn [.reg dn] "SETC:64" [] =>
      if isGpName dn then some [JInstr.setc dn] else none
  | .Lopn [.reg dn] "CMOVE:64" [.reg an, .reg sn] =>
      if an == dn && isGpName dn && isGpName sn then some [JInstr.cmove dn (.reg sn)]
      else none
  | .Lopn [.reg dn] "CMOVNE:64" [.reg an, .reg sn] =>
      if an == dn && isGpName dn && isGpName sn then some [JInstr.cmovne dn (.reg sn)]
      else none
  | .Lopn [.reg dn] "CMOVB:64" [.reg an, .reg sn] =>
      if an == dn && isGpName dn && isGpName sn then some [JInstr.cmovb dn (.reg sn)]
      else none
  | _ => none

/-- The `SETC:64` arm's output. The mnemonic takes no source: the flag it reads
    is CF. -/
theorem lowerMemOp_setc (frame spillW qsaveB : Nat) (dn : String)
    (hd : isGpName dn = true) :
    lowerMemOp frame spillW (.Lopn [.reg dn] "SETC:64" []) qsaveB
      = some [JInstr.setc dn] := by
  simp [lowerMemOp, hd]

/-- The `CMOVE:64` arm's output. -/
theorem lowerMemOp_cmove (frame spillW qsaveB : Nat) (dn sn : String)
    (hd : isGpName dn = true) (hs : isGpName sn = true) :
    lowerMemOp frame spillW (.Lopn [.reg dn] "CMOVE:64" [.reg dn, .reg sn]) qsaveB
      = some [JInstr.cmove dn (.reg sn)] := by
  simp [lowerMemOp, hd, hs]

/-- The `CMOVNE:64` arm's output. -/
theorem lowerMemOp_cmovne (frame spillW qsaveB : Nat) (dn sn : String)
    (hd : isGpName dn = true) (hs : isGpName sn = true) :
    lowerMemOp frame spillW (.Lopn [.reg dn] "CMOVNE:64" [.reg dn, .reg sn]) qsaveB
      = some [JInstr.cmovne dn (.reg sn)] := by
  simp [lowerMemOp, hd, hs]

/-- The `CMOVB:64` arm's output. -/
theorem lowerMemOp_cmovb (frame spillW qsaveB : Nat) (dn sn : String)
    (hd : isGpName dn = true) (hs : isGpName sn = true) :
    lowerMemOp frame spillW (.Lopn [.reg dn] "CMOVB:64" [.reg dn, .reg sn]) qsaveB
      = some [JInstr.cmovb dn (.reg sn)] := by
  simp [lowerMemOp, hd, hs]

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

/-- The `LEA:64` arm's output. -/
theorem lowerMemOp_lea (frame spillW qsaveB : Nat) (dn sn b : String) (off : Int)
    (h : memNameParts sn = some (b, off))
    (hb : isGpName b = true) (hd : isGpName dn = true) :
    lowerMemOp frame spillW (.Lopn [.reg dn] "LEA:64" [.reg sn]) qsaveB
      = some [JInstr.lea dn b b 0 off] := by
  simp [lowerMemOp, h, hb, hd]

/-- The `ADC:64` arm's output on the in-place shape. -/
theorem lowerMemOp_adc (frame spillW qsaveB : Nat) (dn sn : String)
    (hd : isGpName dn = true) (hs : isGpName sn = true) :
    lowerMemOp frame spillW (.Lopn [.reg dn] "ADC:64" [.reg dn, .reg sn]) qsaveB
      = some [JInstr.adc dn (.reg sn)] := by
  simp [lowerMemOp, hd, hs]

/-- The `SBB:64` arm's output on the in-place shape. -/
theorem lowerMemOp_sbb (frame spillW qsaveB : Nat) (dn sn : String)
    (hd : isGpName dn = true) (hs : isGpName sn = true) :
    lowerMemOp frame spillW (.Lopn [.reg dn] "SBB:64" [.reg dn, .reg sn]) qsaveB
      = some [JInstr.sbb dn (.reg sn)] := by
  simp [lowerMemOp, hd, hs]

/-- The `ADC:64` arm's output on the in-place immediate shape. -/
theorem lowerMemOp_adc_imm (frame spillW qsaveB : Nat) (dn : String) (v : Nat)
    (hd : isGpName dn = true) (hv : aluImmGathers v = true) :
    lowerMemOp frame spillW (.Lopn [.reg dn] "ADC:64" [.reg dn, .imm v]) qsaveB
      = some [JInstr.adc dn (.imm v)] := by
  simp [lowerMemOp, hd, hv]

/-- The `ADCX:64` arm's output on the two-source shape. -/
theorem lowerMemOp_adcx₂ (frame spillW qsaveB : Nat) (dn sn : String)
    (hd : isGpName dn = true) (hs : isGpName sn = true) :
    lowerMemOp frame spillW (.Lopn [.reg dn] "ADCX:64" [.reg dn, .reg sn]) qsaveB
      = some [JInstr.adcx dn (.reg sn)] := by
  simp [lowerMemOp, hd, hs]

/-- The `ADOX:64` arm's output on the two-source shape. -/
theorem lowerMemOp_adox₂ (frame spillW qsaveB : Nat) (dn sn : String)
    (hd : isGpName dn = true) (hs : isGpName sn = true) :
    lowerMemOp frame spillW (.Lopn [.reg dn] "ADOX:64" [.reg dn, .reg sn]) qsaveB
      = some [JInstr.adox dn (.reg sn)] := by
  simp [lowerMemOp, hd, hs]

/-- The `ADCX:64` arm's output on the one-source shape. -/
theorem lowerMemOp_adcx₁ (frame spillW qsaveB : Nat) (dn sn : String)
    (hd : isGpName dn = true) (hs : isGpName sn = true) :
    lowerMemOp frame spillW (.Lopn [.reg dn] "ADCX:64" [.reg sn]) qsaveB
      = some [JInstr.adcx dn (.reg sn)] := by
  simp [lowerMemOp, hd, hs]

/-- The `ADOX:64` arm's output on the one-source shape. -/
theorem lowerMemOp_adox₁ (frame spillW qsaveB : Nat) (dn sn : String)
    (hd : isGpName dn = true) (hs : isGpName sn = true) :
    lowerMemOp frame spillW (.Lopn [.reg dn] "ADOX:64" [.reg sn]) qsaveB
      = some [JInstr.adox dn (.reg sn)] := by
  simp [lowerMemOp, hd, hs]

/-- The `MULX:64` arm's output. Like its memory-folded sibling, the destination
    list is read low word first and the `JInstr` takes the high word first. -/
theorem lowerMemOp_mulx (frame spillW qsaveB : Nat) (dlN dhN s2 : String)
    (hl : isGpName dlN = true) (hh : isGpName dhN = true) (hs : isGpName s2 = true) :
    lowerMemOp frame spillW (.Lopn [.reg dlN, .reg dhN] "MULX:64" [.reg s2]) qsaveB
      = some [JInstr.mulx dhN dlN (.reg mulxMultiplier) (.reg s2)] := by
  simp [lowerMemOp, hl, hh, hs]

/-- The `MULXMEM:64` arm's output. The destination list is read low word first
    and the `JInstr` takes the high word first. -/
theorem lowerMemOp_mulxmem (frame spillW qsaveB : Nat) (dlN dhN mn b : String)
    (off : Int) (h : memNameParts mn = some (b, off))
    (hb : isGpName b = true) (hl : isGpName dlN = true) (hh : isGpName dhN = true) :
    lowerMemOp frame spillW (.Lopn [.reg dlN, .reg dhN] "MULXMEM:64" [.reg mn]) qsaveB
      = some [JInstr.mulxMem dhN dlN (.reg mulxMultiplier) b off] := by
  simp [lowerMemOp, h, hb, hl, hh]

/-- The `SBB:64` arm's output on the in-place immediate shape. -/
theorem lowerMemOp_sbb_imm (frame spillW qsaveB : Nat) (dn : String) (v : Nat)
    (hd : isGpName dn = true) (hv : aluImmGathers v = true) :
    lowerMemOp frame spillW (.Lopn [.reg dn] "SBB:64" [.reg dn, .imm v]) qsaveB
      = some [JInstr.sbb dn (.imm v)] := by
  simp [lowerMemOp, hd, hv]

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

/-- `lowerCov5` declines the array-ABI address computation, so `lowerCov6`
    reaches the new arm. `leaq (%rsp), %rdi` is the frame-base materialisation the
    array ABI emits ahead of the element accesses. -/
theorem lowerCov6_lea_RSP0 :
    lowerCov6 64 64 (.Lopn [.reg "RDI"] "LEA:64" [.reg "mem.RSP.0"])
      = some [JInstr.lea "RDI" "RSP" "RSP" 0 (0 : Int)] := by
  with_unfolding_all rfl

/-- `lowerCov5` declines the in-place add-with-carry, so `lowerCov6` reaches the
    new arm: `LoweringExtended.lowerAluJ`, which the two-source route below
    `lowerCov5` dispatches on, has no `ADC` row. -/
theorem lowerCov6_adc_RCX_RDX :
    lowerCov6 64 64 (.Lopn [.reg "RCX"] "ADC:64" [.reg "RCX", .reg "RDX"])
      = some [JInstr.adc "RCX" (.reg "RDX")] := by
  with_unfolding_all rfl

/-- `lowerCov5` declines the in-place subtract-with-borrow, so `lowerCov6` reaches
    the new arm: `LoweringExtended.lowerAluJ` has no `SBB` row either. -/
theorem lowerCov6_sbb_R10_R11 :
    lowerCov6 64 64 (.Lopn [.reg "R10"] "SBB:64" [.reg "R10", .reg "R11"])
      = some [JInstr.sbb "R10" (.reg "R11")] := by
  with_unfolding_all rfl

/-- `lowerCov5` declines the two-source ADX carry-chain add, so `lowerCov6`
    reaches the new arm: `LoweringExtendedCoverage.lowerLinstrExtCov`'s ADX arms
    match three sources, and the tables below it hold no `ADCX` row. -/
theorem lowerCov6_adcx_RSI_R9 :
    lowerCov6 64 64 (.Lopn [.reg "RSI"] "ADCX:64" [.reg "RSI", .reg "R9"])
      = some [JInstr.adcx "RSI" (.reg "R9")] := by
  with_unfolding_all rfl

/-- `lowerCov5` declines the two-source OF-chain add likewise. -/
theorem lowerCov6_adox_RSI_R9 :
    lowerCov6 64 64 (.Lopn [.reg "RSI"] "ADOX:64" [.reg "RSI", .reg "R9"])
      = some [JInstr.adox "RSI" (.reg "R9")] := by
  with_unfolding_all rfl

/-- `lowerCov5` declines the zero-source flag materialisation, so `lowerCov6`
    reaches the new arm. -/
theorem lowerCov6_setc_RSI :
    lowerCov6 64 64 (.Lopn [.reg "RSI"] "SETC:64" [])
      = some [JInstr.setc "RSI"] := by
  with_unfolding_all rfl

/-- `lowerCov5` declines the two-source conditional move: the chain's arm above
    matches the three-source `CMOV:64` select, not the `CMOVcc` forms. -/
theorem lowerCov6_cmovb_RSI_R9 :
    lowerCov6 64 64 (.Lopn [.reg "RSI"] "CMOVB:64" [.reg "RSI", .reg "R9"])
      = some [JInstr.cmovb "RSI" (.reg "R9")] := by
  with_unfolding_all rfl

/-- `lowerCov5` declines the register widening multiply, so `lowerCov6` reaches
    the new arm: every arm of the chain below it matches a single-element
    destination list. -/
theorem lowerCov6_mulx_RCX_RSI_R9 :
    lowerCov6 64 64 (.Lopn [.reg "RCX", .reg "RSI"] "MULX:64" [.reg "R9"])
      = some [JInstr.mulx "RSI" "RCX" (.reg "RDX") (.reg "R9")] := by
  with_unfolding_all rfl

/-- `lowerCov5` declines the mem-folded widening multiply, so `lowerCov6` reaches
    the new arm: every arm of the chain below it matches a single-element
    destination list, which a `MULXMEM` binding is not. -/
theorem lowerCov6_mulxmem_RDI160 :
    lowerCov6 64 64 (.Lopn [.reg "RCX", .reg "RSI"] "MULXMEM:64" [.reg "mem.RDI.160"])
      = some [JInstr.mulxMem "RSI" "RCX" (.reg "RDX") "RDI" (160 : Int)] := by
  with_unfolding_all rfl

/-- `lowerCov5` declines the immediate in-place carry-chain shapes as well. -/
theorem lowerCov6_sbbImm_R10_1000 :
    lowerCov6 64 64 (.Lopn [.reg "R10"] "SBB:64" [.reg "R10", .imm 1000])
      = some [JInstr.sbb "R10" (.imm 1000)] := by
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

/-- **The `LEA` fall-through dispatch.** `LEA` is in none of the `tagShiftExt`,
    `aluOpcode` and `twoByteOpcode` tables, so on the one-source form
    `Lopn [.reg dn] "<MNEM>" [.reg sn]` the `encodeLopn` dispatch falls through to
    its last arm, which resolves the source with `parseMemNameGp` and emits the
    `8D /r` effective-address bytes at the mnemonic's width. -/
theorem dispatch_lea (frame spillW bb : Nat) (mnem base : String)
    (dn sn : String) (off : Int) (qsaveB : Nat)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hw : rexW (mnemWidth mnem) = 1)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = false)
    (hadx : adxPrefix base = none) (htag : tagShiftExt base = none)
    (halu : aluOpcode base = none) (h2b : twoByteOpcode base = none)
    (hlea : (base == "LEA") = true)
    (hd : isGpName dn = true) (hgp : parseMemNameGp sn = some (bb, off)) :
    encodeLopn frame spillW (.Lopn [.reg dn] mnem [.reg sn]) qsaveB
      = encMemMovw 1 0x8d (gpNumU dn) bb off := by
  simp only [encodeLopn, hbind, hstrip, hw, hmulx, hmulxmem, hadx, htag, halu, h2b,
    hlea, hd, hgp, Bool.false_eq_true, if_false, if_true]

/-- `LEA:64` (opcode `0x8d`, `w = 1`) dispatches to the effective-address bytes. -/
theorem encodeLopn_lea64 (frame spillW bb : Nat) (dn sn : String) (off : Int)
    (qsaveB : Nat) (hd : isGpName dn = true)
    (hgp : parseMemNameGp sn = some (bb, off)) :
    encodeLopn frame spillW (.Lopn [.reg dn] "LEA:64" [.reg sn]) qsaveB
      = encMemMovw 1 0x8d (gpNumU dn) bb off :=
  dispatch_lea frame spillW bb "LEA:64" "LEA" dn sn off qsaveB
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hd hgp

/-- `ADC:64` (opcode `0x11`, `w = 1`) two-source dispatch: the `[d], [a, s]` ALU
    route to `encTwoAddr`, which carries the destination and the second source. -/
theorem encodeLopn_adc64₂ (frame spillW : Nat) (dn an sn : String) (qsaveB : Nat) :
    encodeLopn frame spillW (.Lopn [.reg dn] "ADC:64" [.reg an, .reg sn]) qsaveB
      = encTwoAddr frame spillW 1 0x11 (.reg dn) (.reg sn) qsaveB :=
  dispatch_alu_two frame spillW 0x11 "ADC:64" "ADC" dn an sn qsaveB
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `SBB:64` (opcode `0x19`, `w = 1`) two-source dispatch. -/
theorem encodeLopn_sbb64₂ (frame spillW : Nat) (dn an sn : String) (qsaveB : Nat) :
    encodeLopn frame spillW (.Lopn [.reg dn] "SBB:64" [.reg an, .reg sn]) qsaveB
      = encTwoAddr frame spillW 1 0x19 (.reg dn) (.reg sn) qsaveB :=
  dispatch_alu_two frame spillW 0x19 "SBB:64" "SBB" dn an sn qsaveB
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-! ### The ADX carry-chain dispatch

`adxPrefix` routes `ADCX` and `ADOX` to `encAdxCarry` on a branch of its own,
below the `MULX` names and above the `aluOpcode` table. Its one-source and
two-source arms emit the single two-address carry-chain add, whose carry-in is
the CF or OF flag rather than an operand. On the two-source arm the first source
is a wildcard pattern that contributes nothing to the bytes. -/

/-- **The two-source ADX dispatch.** `Lopn [.reg dn] "<MNEM>:64" [_, .reg sn]`
    reduces to `encAdxCarry pfx (gpNumU dn) (gpNumU sn)`; the first source is
    matched by a wildcard and does not reach the bytes. -/
theorem dispatch_adx_two (frame spillW pfx : Nat) (mnem base : String)
    (dn an sn : String) (qsaveB : Nat)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = false)
    (hadx : adxPrefix base = some pfx) :
    encodeLopn frame spillW (.Lopn [.reg dn] mnem [.reg an, .reg sn]) qsaveB
      = encAdxCarry pfx (gpNumU dn) (gpNumU sn) := by
  simp only [encodeLopn, hbind, hstrip, hmulx, hmulxmem, hadx,
    Bool.false_eq_true, if_false]

/-- **The one-source ADX dispatch.** -/
theorem dispatch_adx_one (frame spillW pfx : Nat) (mnem base : String)
    (dn sn : String) (qsaveB : Nat)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = false)
    (hadx : adxPrefix base = some pfx) :
    encodeLopn frame spillW (.Lopn [.reg dn] mnem [.reg sn]) qsaveB
      = encAdxCarry pfx (gpNumU dn) (gpNumU sn) := by
  simp only [encodeLopn, hbind, hstrip, hmulx, hmulxmem, hadx,
    Bool.false_eq_true, if_false]

/-- `ADCX:64` (prefix `0x66`, the CF chain) two-source dispatch. -/
theorem encodeLopn_adcx64₂ (frame spillW : Nat) (dn an sn : String) (qsaveB : Nat) :
    encodeLopn frame spillW (.Lopn [.reg dn] "ADCX:64" [.reg an, .reg sn]) qsaveB
      = encAdxCarry 0x66 (gpNumU dn) (gpNumU sn) :=
  dispatch_adx_two frame spillW 0x66 "ADCX:64" "ADCX" dn an sn qsaveB
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- `ADOX:64` (prefix `0xf3`, the OF chain) two-source dispatch. -/
theorem encodeLopn_adox64₂ (frame spillW : Nat) (dn an sn : String) (qsaveB : Nat) :
    encodeLopn frame spillW (.Lopn [.reg dn] "ADOX:64" [.reg an, .reg sn]) qsaveB
      = encAdxCarry 0xf3 (gpNumU dn) (gpNumU sn) :=
  dispatch_adx_two frame spillW 0xf3 "ADOX:64" "ADOX" dn an sn qsaveB
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- `ADCX:64` one-source dispatch. -/
theorem encodeLopn_adcx64₁ (frame spillW : Nat) (dn sn : String) (qsaveB : Nat) :
    encodeLopn frame spillW (.Lopn [.reg dn] "ADCX:64" [.reg sn]) qsaveB
      = encAdxCarry 0x66 (gpNumU dn) (gpNumU sn) :=
  dispatch_adx_one frame spillW 0x66 "ADCX:64" "ADCX" dn sn qsaveB
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- `ADOX:64` one-source dispatch. -/
theorem encodeLopn_adox64₁ (frame spillW : Nat) (dn sn : String) (qsaveB : Nat) :
    encodeLopn frame spillW (.Lopn [.reg dn] "ADOX:64" [.reg sn]) qsaveB
      = encAdxCarry 0xf3 (gpNumU dn) (gpNumU sn) :=
  dispatch_adx_one frame spillW 0xf3 "ADOX:64" "ADOX" dn sn qsaveB
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-! ### The `0F`-map and flag-materialisation dispatch

`twoByteOpcode` holds the conditional moves, reached on the two-source route
below the shift and `aluOpcode` tables; `SETC` is matched by name on the
zero-source route. Both sit under the `adxPrefix` branch. -/

/-- **The two-source `0F`-map dispatch.** `Lopn [.reg dn] "<MNEM>:64" [_, .reg sn]`
    over a `twoByteOpcode` mnemonic reduces to `enc0FRRw 1 op`; as on the
    `aluOpcode` route the first source does not reach the bytes. -/
theorem dispatch_2b_two (frame spillW op : Nat) (mnem base : String)
    (dn an sn : String) (qsaveB : Nat)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hw : rexW (mnemWidth mnem) = 1)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = false)
    (hadx : adxPrefix base = none) (htag : tagShiftExt base = none)
    (halu : aluOpcode base = none) (h2b : twoByteOpcode base = some op) :
    encodeLopn frame spillW (.Lopn [.reg dn] mnem [.reg an, .reg sn]) qsaveB
      = enc0FRRw 1 op (gpNumU dn) (gpNumU sn) := by
  simp only [encodeLopn, hbind, hstrip, hw, hmulx, hmulxmem, hadx, htag, halu, h2b,
    Bool.false_eq_true, if_false]

/-- `CMOVE:64` (`0F 44`) two-source dispatch. -/
theorem encodeLopn_cmove64 (frame spillW : Nat) (dn an sn : String) (qsaveB : Nat) :
    encodeLopn frame spillW (.Lopn [.reg dn] "CMOVE:64" [.reg an, .reg sn]) qsaveB
      = enc0FRRw 1 0x44 (gpNumU dn) (gpNumU sn) :=
  dispatch_2b_two frame spillW 0x44 "CMOVE:64" "CMOVE" dn an sn qsaveB
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- `CMOVNE:64` (`0F 45`) two-source dispatch. -/
theorem encodeLopn_cmovne64 (frame spillW : Nat) (dn an sn : String) (qsaveB : Nat) :
    encodeLopn frame spillW (.Lopn [.reg dn] "CMOVNE:64" [.reg an, .reg sn]) qsaveB
      = enc0FRRw 1 0x45 (gpNumU dn) (gpNumU sn) :=
  dispatch_2b_two frame spillW 0x45 "CMOVNE:64" "CMOVNE" dn an sn qsaveB
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- `CMOVB:64` (`0F 42`) two-source dispatch. -/
theorem encodeLopn_cmovb64 (frame spillW : Nat) (dn an sn : String) (qsaveB : Nat) :
    encodeLopn frame spillW (.Lopn [.reg dn] "CMOVB:64" [.reg an, .reg sn]) qsaveB
      = enc0FRRw 1 0x42 (gpNumU dn) (gpNumU sn) :=
  dispatch_2b_two frame spillW 0x42 "CMOVB:64" "CMOVB" dn an sn qsaveB
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

/-- **The flag-materialisation dispatch.** A zero-source `SETC` reduces to the
    `setc`/`movzbq` pair at the CF opcode `0x92`. -/
theorem dispatch_setc (frame spillW : Nat) (mnem base : String) (dn : String)
    (qsaveB : Nat)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = false)
    (hadx : adxPrefix base = none) (hsetc : (base == "SETC") = true) :
    encodeLopn frame spillW (.Lopn [.reg dn] mnem []) qsaveB
      = encSetccMovzx 0x92 (gpNumU dn) := by
  simp only [encodeLopn, hbind, hstrip, hmulx, hmulxmem, hadx, hsetc,
    Bool.false_eq_true, if_false, if_true]

/-- `SETC:64` dispatches to the CF materialisation pair. -/
theorem encodeLopn_setc64 (frame spillW : Nat) (dn : String) (qsaveB : Nat) :
    encodeLopn frame spillW (.Lopn [.reg dn] "SETC:64" []) qsaveB
      = encSetccMovzx 0x92 (gpNumU dn) :=
  dispatch_setc frame spillW "SETC:64" "SETC" dn qsaveB
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **The register widening-multiply dispatch.** `MULX` is matched by name first
    of all, on a two-destination `Lopn` with a single register source. As on the
    memory-folded form the destination list is `[low, high]` and `encMulxRR` takes
    the high word first, so the dispatch transposes them. -/
theorem dispatch_mulx (frame spillW : Nat) (mnem base : String)
    (dlN dhN s2 : String) (qsaveB : Nat)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base) (hmulx : (base == "MULX") = true)
    (hne : (dlN == dhN) = false) :
    encodeLopn frame spillW (.Lopn [.reg dlN, .reg dhN] mnem [.reg s2]) qsaveB
      = encMulxRR (gpNumU dhN) (gpNumU dlN) (gpNumU s2) := by
  simp only [encodeLopn, hbind, hstrip, hmulx, hne, Bool.false_eq_true, if_false,
    if_true]

/-- The register widening multiply carries no bytes when its two destinations are
    the same register: `mulx` keeps only the high half there, so the encoder
    declines the shape instead of emitting bytes the rendered text disagrees
    with. -/
theorem encodeLopn_mulx_same (frame spillW : Nat) (mnem base : String)
    (dN s2 : String) (qsaveB : Nat)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base) (hmulx : (base == "MULX") = true) :
    encodeLopn frame spillW (.Lopn [.reg dN, .reg dN] mnem [.reg s2]) qsaveB = [] := by
  simp only [encodeLopn, hbind, hstrip, hmulx, BEq.rfl, Bool.false_eq_true, if_false,
    if_true]

/-- `MULX:64` dispatches to the VEX register-form widening multiply. -/
theorem encodeLopn_mulx64 (frame spillW : Nat) (dlN dhN s2 : String) (qsaveB : Nat)
    (hne : (dlN == dhN) = false) :
    encodeLopn frame spillW (.Lopn [.reg dlN, .reg dhN] "MULX:64" [.reg s2]) qsaveB
      = encMulxRR (gpNumU dhN) (gpNumU dlN) (gpNumU s2) :=
  dispatch_mulx frame spillW "MULX:64" "MULX" dlN dhN s2 qsaveB
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hne

/-- **The mem-folded widening-multiply dispatch.** `MULXMEM` is matched by name
    above the ADX and ALU tables, on a two-destination `Lopn` with a single
    `mem.*` source. The destination list is `[low, high]` and `encMulxMem` takes
    the high word first, so the dispatch transposes them. -/
theorem dispatch_mulxmem (frame spillW : Nat) (mnem base : String)
    (dlN dhN mn : String) (bb : Nat) (off : Int) (qsaveB : Nat)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = true)
    (hmem : parseMemName mn = some (bb, off)) :
    encodeLopn frame spillW (.Lopn [.reg dlN, .reg dhN] mnem [.reg mn]) qsaveB
      = encMulxMem (gpNumU dhN) (gpNumU dlN) bb off := by
  simp only [encodeLopn, hbind, hstrip, hmulx, hmulxmem, hmem,
    Bool.false_eq_true, if_false, if_true]

/-- `MULXMEM:64` dispatches to the VEX memory-form widening multiply. -/
theorem encodeLopn_mulxmem64 (frame spillW : Nat) (dlN dhN mn : String) (bb : Nat)
    (off : Int) (qsaveB : Nat) (hmem : parseMemName mn = some (bb, off)) :
    encodeLopn frame spillW (.Lopn [.reg dlN, .reg dhN] "MULXMEM:64" [.reg mn]) qsaveB
      = encMulxMem (gpNumU dhN) (gpNumU dlN) bb off :=
  dispatch_mulxmem frame spillW "MULXMEM:64" "MULXMEM" dlN dhN mn bb off qsaveB
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) hmem

/-- **The immediate two-source dispatch.** On `Lopn [.reg dn] "<MNEM>" [.reg an,
    .imm v]` the `[d], [a, s]` route takes its immediate branch before any of the
    shift and ALU opcode tables, so the whole `encodeLopn` dispatch reduces to
    `encImmOp`, which makes its own `83`-versus-`81` form selection. -/
theorem dispatch_alu_imm₂ (frame spillW : Nat) (mnem base : String)
    (dn an : String) (v qsaveB : Nat)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hw : rexW (mnemWidth mnem) = 1)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = false)
    (hadx : adxPrefix base = none) :
    encodeLopn frame spillW (.Lopn [.reg dn] mnem [.reg an, .imm v]) qsaveB
      = encImmOp 1 base (.reg dn) v := by
  simp only [encodeLopn, hbind, hstrip, hw, hmulx, hmulxmem, hadx,
    Bool.false_eq_true, if_false]

/-- **The group-1 immediate byte function.** Outside the sign-extended-imm8 range
    `encImmOp` emits the `81 /digit id` form over the mnemonic's `aluImmDigit`,
    which is `LprogJInstrBytesAgree` §1's width-threaded `encAluImmw`. The
    `MOV`, `MOVQ` and `MUL` arms sit above the group-1 one and are excluded by
    hypothesis, since the mnemonic stays a variable here. -/
theorem encImmOp_aluImm32 (w digit : Nat) (base dn : String) (v : Nat)
    (hsp : isSpillOrQsave dn = false)
    (hmov : ¬ base = "MOV") (hmovq : ¬ base = "MOVQ") (hmul : ¬ base = "MUL")
    (hsh : shiftImmExt base = none) (hdig : aluImmDigit base = some digit)
    (hfit : fitsImm8S w v = false) :
    encImmOp w base (.reg dn) v = encAluImmw w digit (gpNumU dn) v := by
  simp [encImmOp, hsp, hsh, hdig, hfit]

/-- `ADC:64` over an immediate outside the imm8 range (`81 /2 id`). -/
theorem encodeLopn_adcImm (frame spillW : Nat) (dn an : String) (v qsaveB : Nat)
    (hsp : isSpillOrQsave dn = false) (hfit : fitsImm8S 1 v = false) :
    encodeLopn frame spillW (.Lopn [.reg dn] "ADC:64" [.reg an, .imm v]) qsaveB
      = encAluImmw 1 2 (gpNumU dn) v := by
  rw [dispatch_alu_imm₂ frame spillW "ADC:64" "ADC" dn an v qsaveB
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
    encImmOp_aluImm32 1 2 "ADC" dn v hsp (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) hfit]

/-- `SBB:64` over an immediate outside the imm8 range (`81 /3 id`). -/
theorem encodeLopn_sbbImm (frame spillW : Nat) (dn an : String) (v qsaveB : Nat)
    (hsp : isSpillOrQsave dn = false) (hfit : fitsImm8S 1 v = false) :
    encodeLopn frame spillW (.Lopn [.reg dn] "SBB:64" [.reg an, .imm v]) qsaveB
      = encAluImmw 1 3 (gpNumU dn) v := by
  rw [dispatch_alu_imm₂ frame spillW "SBB:64" "SBB" dn an v qsaveB
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel),
    encImmOp_aluImm32 1 3 "SBB" dn v hsp (by decide) (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) hfit]

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

/-- **The `LEA:64` byte agreement.** The gathered `lea` block encodes to the bytes
    `encodeLopn` gives for the array-ABI address computation. The source name's
    `parseMemNameGp` image is a hypothesis: `memNameParts` and `parseMemNameGp`
    split a `mem.*` name by different string primitives (`String.span` against
    `String.splitOn`), and the two parses are not related by a lemma here. -/
theorem lea64_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dn sn b : String) (off : Int) (qsaveB : Nat)
    (hs : memNameParts sn = some (b, off))
    (hb : isGpName b = true) (hd : isGpName dn = true)
    (hgp : parseMemNameGp sn = some (gpNumU b, off))
    (hr : gpNum (regOf alloc dn) = gpNumU dn)
    (hbr : gpNum (regOf alloc b) = gpNumU b) :
    (lowerMemOp frame spillW (.Lopn [.reg dn] "LEA:64" [.reg sn]) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW (.Lopn [.reg dn] "LEA:64" [.reg sn]) qsaveB) := by
  rw [lowerMemOp_lea frame spillW qsaveB dn sn b off hs hb hd, Option.map_some,
    encodeJBlock_singleton, encodeLopn_lea64 frame spillW (gpNumU b) dn sn off qsaveB hd hgp]
  simp [encodeJInstr, hr, hbr, encMemMovw_one]

/-- `JInstr` `adc` over a register source reduces to `encAluRR 0x11`, the shape
    encoder `LprogJInstrBytesAgree` §1 relates to the width-threaded
    `encAluRRw`. -/
theorem jinstr_adc (alloc : GpAlloc) (d r : String) :
    encodeJInstr alloc (.adc d (.reg r))
      = encAluRR 0x11 (gpNum (regOf alloc d)) (gpNum (regOf alloc r)) := rfl

/-- **`ADC` bytes agree.** The `JInstr` `adc` encoding equals the Lprog reg-reg
    two-address byte function at opcode `0x11`, U64 width, under resolver
    agreement. The side conditions are the reg-reg ones of
    `LprogJInstrBytesAgree` §2b: neither operand is a spill/qsave slot or a
    `mem.*` name. -/
theorem adc_bytes_agree (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String)
    (qsaveB : Nat)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    encodeJInstr alloc (.adc d (.reg r))
      = encTwoAddr frame spillW 1 0x11 (.reg dn) (.reg sn) qsaveB := by
  rw [jinstr_adc,
    encTwoAddr_regReg frame spillW 1 0x11 dn sn qsaveB hdk hsk hdm hsm hdsp hssp,
    encAluRRw_one, hd, hs]

/-- **The `ADC:64` byte agreement.** The gathered `adc` block encodes to the bytes
    `encodeLopn` gives for the in-place add-with-carry. -/
theorem adc64_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dn sn : String) (qsaveB : Nat)
    (hd : isGpName dn = true) (hs : isGpName sn = true)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hr : gpNum (regOf alloc dn) = gpNumU dn)
    (hsr : gpNum (regOf alloc sn) = gpNumU sn) :
    (lowerMemOp frame spillW (.Lopn [.reg dn] "ADC:64" [.reg dn, .reg sn]) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW
          (.Lopn [.reg dn] "ADC:64" [.reg dn, .reg sn]) qsaveB) := by
  rw [lowerMemOp_adc frame spillW qsaveB dn sn hd hs, Option.map_some,
    encodeJBlock_singleton, encodeLopn_adc64₂,
    adc_bytes_agree alloc frame spillW dn sn dn sn qsaveB
      hdk hsk hdm hsm hdsp hssp hr hsr]

/-- `JInstr` `adcx` over a register source reduces to `encAdxCarry 0x66`. -/
theorem jinstr_adcx (alloc : GpAlloc) (d r : String) :
    encodeJInstr alloc (.adcx d (.reg r))
      = encAdxCarry 0x66 (gpNum (regOf alloc d)) (gpNum (regOf alloc r)) := rfl

/-- `JInstr` `adox` over a register source reduces to `encAdxCarry 0xf3`. -/
theorem jinstr_adox (alloc : GpAlloc) (d r : String) :
    encodeJInstr alloc (.adox d (.reg r))
      = encAdxCarry 0xf3 (gpNum (regOf alloc d)) (gpNum (regOf alloc r)) := rfl

/-- **The two-source `ADCX:64` byte agreement.** The gathered `adcx` block encodes
    to the bytes `encodeLopn` gives for the CF-chain add. The `an == dn` condition
    the arm carries is not what makes the bytes equal — the encoder reads neither
    operand on that position — it is what makes the gathered instruction the one
    the `Lopn` denotes. -/
theorem adcx64₂_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dn sn : String) (qsaveB : Nat)
    (hd : isGpName dn = true) (hs : isGpName sn = true)
    (hr : gpNum (regOf alloc dn) = gpNumU dn)
    (hsr : gpNum (regOf alloc sn) = gpNumU sn) :
    (lowerMemOp frame spillW (.Lopn [.reg dn] "ADCX:64" [.reg dn, .reg sn]) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW
          (.Lopn [.reg dn] "ADCX:64" [.reg dn, .reg sn]) qsaveB) := by
  rw [lowerMemOp_adcx₂ frame spillW qsaveB dn sn hd hs, Option.map_some,
    encodeJBlock_singleton, encodeLopn_adcx64₂, jinstr_adcx, hr, hsr]

/-- **The two-source `ADOX:64` byte agreement** (the OF chain, prefix `0xf3`). -/
theorem adox64₂_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dn sn : String) (qsaveB : Nat)
    (hd : isGpName dn = true) (hs : isGpName sn = true)
    (hr : gpNum (regOf alloc dn) = gpNumU dn)
    (hsr : gpNum (regOf alloc sn) = gpNumU sn) :
    (lowerMemOp frame spillW (.Lopn [.reg dn] "ADOX:64" [.reg dn, .reg sn]) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW
          (.Lopn [.reg dn] "ADOX:64" [.reg dn, .reg sn]) qsaveB) := by
  rw [lowerMemOp_adox₂ frame spillW qsaveB dn sn hd hs, Option.map_some,
    encodeJBlock_singleton, encodeLopn_adox64₂, jinstr_adox, hr, hsr]

/-- **The one-source `ADCX:64` byte agreement.** -/
theorem adcx64₁_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dn sn : String) (qsaveB : Nat)
    (hd : isGpName dn = true) (hs : isGpName sn = true)
    (hr : gpNum (regOf alloc dn) = gpNumU dn)
    (hsr : gpNum (regOf alloc sn) = gpNumU sn) :
    (lowerMemOp frame spillW (.Lopn [.reg dn] "ADCX:64" [.reg sn]) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW (.Lopn [.reg dn] "ADCX:64" [.reg sn]) qsaveB) := by
  rw [lowerMemOp_adcx₁ frame spillW qsaveB dn sn hd hs, Option.map_some,
    encodeJBlock_singleton, encodeLopn_adcx64₁, jinstr_adcx, hr, hsr]

/-- **The one-source `ADOX:64` byte agreement.** -/
theorem adox64₁_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dn sn : String) (qsaveB : Nat)
    (hd : isGpName dn = true) (hs : isGpName sn = true)
    (hr : gpNum (regOf alloc dn) = gpNumU dn)
    (hsr : gpNum (regOf alloc sn) = gpNumU sn) :
    (lowerMemOp frame spillW (.Lopn [.reg dn] "ADOX:64" [.reg sn]) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW (.Lopn [.reg dn] "ADOX:64" [.reg sn]) qsaveB) := by
  rw [lowerMemOp_adox₁ frame spillW qsaveB dn sn hd hs, Option.map_some,
    encodeJBlock_singleton, encodeLopn_adox64₁, jinstr_adox, hr, hsr]

/-- `JInstr` `setc` reduces to the `ScalarEncoder` CF materialisation pair, which
    is `LprogBytes.encSetccMovzx` at the CF opcode
    (`LprogBytes.encSetccMovzx_setc_agree`). -/
theorem jinstr_setc (alloc : GpAlloc) (d : String) :
    encodeJInstr alloc (.setc d) = encSetccMovzx 0x92 (gpNum (regOf alloc d)) :=
  (encSetccMovzx_setc_agree (gpNum (regOf alloc d))).symm

/-- **The `SETC:64` byte agreement.** -/
theorem setc64_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dn : String) (qsaveB : Nat) (hd : isGpName dn = true)
    (hr : gpNum (regOf alloc dn) = gpNumU dn) :
    (lowerMemOp frame spillW (.Lopn [.reg dn] "SETC:64" []) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW (.Lopn [.reg dn] "SETC:64" []) qsaveB) := by
  rw [lowerMemOp_setc frame spillW qsaveB dn hd, Option.map_some,
    encodeJBlock_singleton, encodeLopn_setc64, jinstr_setc, hr]

/-- `JInstr` `cmove` over a register source reduces to `enc0FRR 0x44`. -/
theorem jinstr_cmove (alloc : GpAlloc) (d r : String) :
    encodeJInstr alloc (.cmove d (.reg r))
      = enc0FRR 0x44 (gpNum (regOf alloc d)) (gpNum (regOf alloc r)) := rfl

/-- `JInstr` `cmovne` over a register source reduces to `enc0FRR 0x45`. -/
theorem jinstr_cmovne (alloc : GpAlloc) (d r : String) :
    encodeJInstr alloc (.cmovne d (.reg r))
      = enc0FRR 0x45 (gpNum (regOf alloc d)) (gpNum (regOf alloc r)) := rfl

/-- `JInstr` `cmovb` over a register source reduces to `enc0FRR 0x42`. -/
theorem jinstr_cmovb (alloc : GpAlloc) (d r : String) :
    encodeJInstr alloc (.cmovb d (.reg r))
      = enc0FRR 0x42 (gpNum (regOf alloc d)) (gpNum (regOf alloc r)) := rfl

/-- **The `CMOVE:64` byte agreement.** -/
theorem cmove64_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dn sn : String) (qsaveB : Nat)
    (hd : isGpName dn = true) (hs : isGpName sn = true)
    (hr : gpNum (regOf alloc dn) = gpNumU dn)
    (hsr : gpNum (regOf alloc sn) = gpNumU sn) :
    (lowerMemOp frame spillW (.Lopn [.reg dn] "CMOVE:64" [.reg dn, .reg sn]) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW
          (.Lopn [.reg dn] "CMOVE:64" [.reg dn, .reg sn]) qsaveB) := by
  rw [lowerMemOp_cmove frame spillW qsaveB dn sn hd hs, Option.map_some,
    encodeJBlock_singleton, encodeLopn_cmove64, jinstr_cmove, enc0FRRw_one, hr, hsr]

/-- **The `CMOVNE:64` byte agreement.** -/
theorem cmovne64_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dn sn : String) (qsaveB : Nat)
    (hd : isGpName dn = true) (hs : isGpName sn = true)
    (hr : gpNum (regOf alloc dn) = gpNumU dn)
    (hsr : gpNum (regOf alloc sn) = gpNumU sn) :
    (lowerMemOp frame spillW (.Lopn [.reg dn] "CMOVNE:64" [.reg dn, .reg sn]) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW
          (.Lopn [.reg dn] "CMOVNE:64" [.reg dn, .reg sn]) qsaveB) := by
  rw [lowerMemOp_cmovne frame spillW qsaveB dn sn hd hs, Option.map_some,
    encodeJBlock_singleton, encodeLopn_cmovne64, jinstr_cmovne, enc0FRRw_one, hr, hsr]

/-- **The `CMOVB:64` byte agreement.** -/
theorem cmovb64_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dn sn : String) (qsaveB : Nat)
    (hd : isGpName dn = true) (hs : isGpName sn = true)
    (hr : gpNum (regOf alloc dn) = gpNumU dn)
    (hsr : gpNum (regOf alloc sn) = gpNumU sn) :
    (lowerMemOp frame spillW (.Lopn [.reg dn] "CMOVB:64" [.reg dn, .reg sn]) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW
          (.Lopn [.reg dn] "CMOVB:64" [.reg dn, .reg sn]) qsaveB) := by
  rw [lowerMemOp_cmovb frame spillW qsaveB dn sn hd hs, Option.map_some,
    encodeJBlock_singleton, encodeLopn_cmovb64, jinstr_cmovb, enc0FRRw_one, hr, hsr]

/-- `JInstr` `mulx` over a register source reduces to `encMulxRR`. The multiplier
    field is not read, as on the memory-folded form. -/
theorem jinstr_mulx (alloc : GpAlloc) (dh dl r : String) (a : JOperand) :
    encodeJInstr alloc (.mulx dh dl a (.reg r))
      = encMulxRR (gpNum (regOf alloc dh)) (gpNum (regOf alloc dl))
          (gpNum (regOf alloc r)) := rfl

/-- **The `MULX:64` byte agreement.** The gathered `mulx` block encodes to the
    bytes `encodeLopn` gives for the register widening multiply. -/
theorem mulx64_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dlN dhN s2 : String) (qsaveB : Nat)
    (hl : isGpName dlN = true) (hh : isGpName dhN = true) (hs : isGpName s2 = true)
    (hrh : gpNum (regOf alloc dhN) = gpNumU dhN)
    (hrl : gpNum (regOf alloc dlN) = gpNumU dlN)
    (hsr : gpNum (regOf alloc s2) = gpNumU s2)
    (hne : (dlN == dhN) = false) :
    (lowerMemOp frame spillW
        (.Lopn [.reg dlN, .reg dhN] "MULX:64" [.reg s2]) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW
          (.Lopn [.reg dlN, .reg dhN] "MULX:64" [.reg s2]) qsaveB) := by
  rw [lowerMemOp_mulx frame spillW qsaveB dlN dhN s2 hl hh hs, Option.map_some,
    encodeJBlock_singleton, encodeLopn_mulx64 frame spillW dlN dhN s2 qsaveB hne,
    jinstr_mulx, hrh, hrl, hsr]

/-- `JInstr` `mulxMem` reduces to `encMulxMem` over its high-word, low-word and
    base numbers. The multiplier field is not read: `MULX` takes that operand
    implicitly in `%rdx`, so it contributes no bytes. -/
theorem jinstr_mulxMem (alloc : GpAlloc) (dh dl base : String) (a : JOperand)
    (off : Int) :
    encodeJInstr alloc (.mulxMem dh dl a base off)
      = encMulxMem (gpNum (regOf alloc dh)) (gpNum (regOf alloc dl))
          (gpNum (regOf alloc base)) off := rfl

/-- **The `MULXMEM:64` byte agreement.** The gathered `mulxMem` block encodes to
    the bytes `encodeLopn` gives for the mem-folded widening multiply. Both sides
    transpose the destination pair the same way, so the low word stays in the
    `vvvv` field and the high word in `ModRM.reg`. -/
theorem mulxmem64_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dlN dhN mn b : String) (off : Int) (qsaveB : Nat)
    (h : memNameParts mn = some (b, off))
    (hb : isGpName b = true) (hl : isGpName dlN = true) (hh : isGpName dhN = true)
    (hrh : gpNum (regOf alloc dhN) = gpNumU dhN)
    (hrl : gpNum (regOf alloc dlN) = gpNumU dlN)
    (hbr : gpNum (regOf alloc b) = gpNumU b) :
    (lowerMemOp frame spillW
        (.Lopn [.reg dlN, .reg dhN] "MULXMEM:64" [.reg mn]) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW
          (.Lopn [.reg dlN, .reg dhN] "MULXMEM:64" [.reg mn]) qsaveB) := by
  rw [lowerMemOp_mulxmem frame spillW qsaveB dlN dhN mn b off h hb hl hh,
    Option.map_some, encodeJBlock_singleton,
    encodeLopn_mulxmem64 frame spillW dlN dhN mn (gpNumU b) off qsaveB
      (parseMemName_of_memNameParts h),
    jinstr_mulxMem, hrh, hrl, hbr]

/-- `JInstr` `sbb` over a register source reduces to `encAluRR 0x19`. -/
theorem jinstr_sbb (alloc : GpAlloc) (d r : String) :
    encodeJInstr alloc (.sbb d (.reg r))
      = encAluRR 0x19 (gpNum (regOf alloc d)) (gpNum (regOf alloc r)) := rfl

/-- **`SBB` bytes agree** (opcode `0x19`), under the same reg-reg side conditions
    as `adc_bytes_agree`. -/
theorem sbb_bytes_agree (alloc : GpAlloc) (frame spillW : Nat) (d r dn sn : String)
    (qsaveB : Nat)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hd : gpNum (regOf alloc d) = gpNumU dn) (hs : gpNum (regOf alloc r) = gpNumU sn) :
    encodeJInstr alloc (.sbb d (.reg r))
      = encTwoAddr frame spillW 1 0x19 (.reg dn) (.reg sn) qsaveB := by
  rw [jinstr_sbb,
    encTwoAddr_regReg frame spillW 1 0x19 dn sn qsaveB hdk hsk hdm hsm hdsp hssp,
    encAluRRw_one, hd, hs]

/-- **The `SBB:64` byte agreement.** The gathered `sbb` block encodes to the bytes
    `encodeLopn` gives for the in-place subtract-with-borrow. -/
theorem sbb64_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dn sn : String) (qsaveB : Nat)
    (hd : isGpName dn = true) (hs : isGpName sn = true)
    (hdk : spillQsaveOff frame spillW dn qsaveB = none)
    (hsk : spillQsaveOff frame spillW sn qsaveB = none)
    (hdm : parseMemName dn = none) (hsm : parseMemName sn = none)
    (hdsp : isSpillOrQsave dn = false) (hssp : isSpillOrQsave sn = false)
    (hr : gpNum (regOf alloc dn) = gpNumU dn)
    (hsr : gpNum (regOf alloc sn) = gpNumU sn) :
    (lowerMemOp frame spillW (.Lopn [.reg dn] "SBB:64" [.reg dn, .reg sn]) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW
          (.Lopn [.reg dn] "SBB:64" [.reg dn, .reg sn]) qsaveB) := by
  rw [lowerMemOp_sbb frame spillW qsaveB dn sn hd hs, Option.map_some,
    encodeJBlock_singleton, encodeLopn_sbb64₂,
    sbb_bytes_agree alloc frame spillW dn sn dn sn qsaveB
      hdk hsk hdm hsm hdsp hssp hr hsr]

/-! ### The immediate second source

The gathered `JInstr` carries the immediate unchanged and `encodeJInstr` gives it
the `81 /digit id` form; `aluImmGathers` restricts the arm to the values on which
`encImmOp` selects that same form, so the agreement needs no reasoning about the
`83 /digit ib` short form beyond the gate. -/

/-- **The `ADC:64` immediate byte agreement**, at the values where the live
    `encodeJInstr` makes the same group-1 form selection `encImmOp` makes. Inside
    the sign-extended-imm8 range the two byte streams differ and
    `GatherImmForms.encodeJInstr7` is the encoder that agrees there. -/
theorem adcImm_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dn : String) (v qsaveB : Nat)
    (hd : isGpName dn = true) (hv : aluImmGathers v = true)
    (hfit : fitsImm8S 1 v = false)
    (hdsp : isSpillOrQsave dn = false)
    (hr : gpNum (regOf alloc dn) = gpNumU dn) :
    (lowerMemOp frame spillW (.Lopn [.reg dn] "ADC:64" [.reg dn, .imm v]) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW
          (.Lopn [.reg dn] "ADC:64" [.reg dn, .imm v]) qsaveB) := by
  rw [lowerMemOp_adc_imm frame spillW qsaveB dn v hd hv, Option.map_some,
    encodeJBlock_singleton,
    encodeLopn_adcImm frame spillW dn dn v qsaveB hdsp hfit, encAluImmw_one]
  simp [encodeJInstr, hr]

/-- **The `SBB:64` immediate byte agreement**, under the same form-selection
    condition as its `ADC:64` dual. -/
theorem sbbImm_gather_bytes_agree (alloc : GpAlloc) (frame spillW : Nat)
    (dn : String) (v qsaveB : Nat)
    (hd : isGpName dn = true) (hv : aluImmGathers v = true)
    (hfit : fitsImm8S 1 v = false)
    (hdsp : isSpillOrQsave dn = false)
    (hr : gpNum (regOf alloc dn) = gpNumU dn) :
    (lowerMemOp frame spillW (.Lopn [.reg dn] "SBB:64" [.reg dn, .imm v]) qsaveB).map
        (encodeJBlock alloc)
      = some (encodeLopn frame spillW
          (.Lopn [.reg dn] "SBB:64" [.reg dn, .imm v]) qsaveB) := by
  rw [lowerMemOp_sbb_imm frame spillW qsaveB dn v hd hv, Option.map_some,
    encodeJBlock_singleton,
    encodeLopn_sbbImm frame spillW dn dn v qsaveB hdsp hfit, encAluImmw_one]
  simp [encodeJInstr, hr]

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

/-- The gathered `adcq %rdx, %rcx` byte-matches `encodeLopn` (the carry-chain add
    the Curve25519 ladder step's limb accumulation is exported as). -/
theorem encJAdc_RCX_RDX :
    encodeJBlock physAlloc [JInstr.adc "RCX" (.reg "RDX")]
      = encodeLopn 64 64 (.Lopn [.reg "RCX"] "ADC:64" [.reg "RCX", .reg "RDX"]) := by
  decide +kernel

/-- The gathered `sbbq %r11, %r10` byte-matches `encodeLopn`. -/
theorem encJSbb_R10_R11 :
    encodeJBlock physAlloc [JInstr.sbb "R10" (.reg "R11")]
      = encodeLopn 64 64 (.Lopn [.reg "R10"] "SBB:64" [.reg "R10", .reg "R11"]) := by
  decide +kernel

/-- The gathered `adcq $1000, %rcx` byte-matches `encodeLopn`: `1000` is outside
    the sign-extended-imm8 range, so both sides take the `81 /2 id` form. -/
theorem encJAdcImm_RCX_1000 :
    encodeJBlock physAlloc [JInstr.adc "RCX" (.imm 1000)]
      = encodeLopn 64 64 (.Lopn [.reg "RCX"] "ADC:64" [.reg "RCX", .imm 1000]) := by
  decide +kernel

/-- The gathered `sbbq $1000, %r10` byte-matches `encodeLopn`. -/
theorem encJSbbImm_R10_1000 :
    encodeJBlock physAlloc [JInstr.sbb "R10" (.imm 1000)]
      = encodeLopn 64 64 (.Lopn [.reg "R10"] "SBB:64" [.reg "R10", .imm 1000]) := by
  decide +kernel

/-- The gathered `adcxq %r9, %rsi` byte-matches `encodeLopn`, at the operands the
    Curve25519 ladder step's CF carry chain carries. -/
theorem encJAdcx_RSI_R9 :
    encodeJBlock physAlloc [JInstr.adcx "RSI" (.reg "R9")]
      = encodeLopn 64 64 (.Lopn [.reg "RSI"] "ADCX:64" [.reg "RSI", .reg "R9"]) := by
  decide +kernel

/-- The gathered `adoxq %r9, %rsi` byte-matches `encodeLopn` (the OF chain, whose
    mandatory prefix is `0xf3` where the CF chain's is `0x66`). -/
theorem encJAdox_RSI_R9 :
    encodeJBlock physAlloc [JInstr.adox "RSI" (.reg "R9")]
      = encodeLopn 64 64 (.Lopn [.reg "RSI"] "ADOX:64" [.reg "RSI", .reg "R9"]) := by
  decide +kernel

/-- The gathered `setc %sil; movzbq %sil, %rsi` pair byte-matches `encodeLopn`.
    `%rsi` is in the band that takes a bare `REX` on the `SETcc`, so this pin
    exercises the prefix case the two encoders had to be reconciled on. -/
theorem encJSetc_RSI :
    encodeJBlock physAlloc [JInstr.setc "RSI"]
      = encodeLopn 64 64 (.Lopn [.reg "RSI"] "SETC:64" []) := by
  decide +kernel

/-- The gathered `cmovbq %r9, %rsi` byte-matches `encodeLopn`, the conditional
    move a constant-time reduction step selects with. -/
theorem encJCmovb_RSI_R9 :
    encodeJBlock physAlloc [JInstr.cmovb "RSI" (.reg "R9")]
      = encodeLopn 64 64 (.Lopn [.reg "RSI"] "CMOVB:64" [.reg "RSI", .reg "R9"]) := by
  decide +kernel

/-- The gathered `mulxq %r9, %rcx, %rsi` byte-matches `encodeLopn`. The register
    pair is the one the mem-folded pin uses, so the two pins differ only in where
    the second multiplicand comes from. -/
theorem encJMulx_RCX_RSI_R9 :
    encodeJBlock physAlloc [JInstr.mulx "RSI" "RCX" (.reg "RDX") (.reg "R9")]
      = encodeLopn 64 64 (.Lopn [.reg "RCX", .reg "RSI"] "MULX:64" [.reg "R9"]) := by
  decide +kernel

/-- The gathered `mulxq 160(%rdi), %rcx, %rsi` byte-matches `encodeLopn`, at the
    operands the Curve25519 ladder step's mem-folded multiply carries. -/
theorem encJMulxMem_RDI160 :
    encodeJBlock physAlloc [JInstr.mulxMem "RSI" "RCX" (.reg "RDX") "RDI" (160 : Int)]
      = encodeLopn 64 64
          (.Lopn [.reg "RCX", .reg "RSI"] "MULXMEM:64" [.reg "mem.RDI.160"]) := by
  decide +kernel

/-- The in-place carry-chain mnemonics gather at a small immediate as at any
    other value inside the signed 32-bit field. The bytes of this block match
    `encodeLopn` under `GatherImmForms.encodeJInstr7`, which makes the same
    group-1 form selection (`GatherImmForms.encJ7SbbImm0_eq_lopn`). -/
theorem lowerMemOp_sbbImm0 :
    lowerMemOp 64 64 (.Lopn [.reg "R10"] "SBB:64" [.reg "R10", .imm 0])
      = some [JInstr.sbb "R10" (.imm 0)] := by
  with_unfolding_all rfl

/-! ### The `LEA:64` arm's bytes

The `encodeLopn` side of this arm resolves its operand name with
`LprogBytes.parseMemNameGp`, which is built on `String.splitOn` and `String.drop`,
whose bodies the module system does not expose; the kernel reduces neither, so the
`encodeLopn` side of a closed `LEA:64` does not reduce and the concrete agreement
is out of reach by `decide +kernel`. The gathered side does reduce, and is pinned
against its bytes here; `lea64_gather_bytes_agree` carries the agreement
symbolically, with the `parseMemNameGp` value as a hypothesis. -/

/-- The gathered `leaq (%rsp), %rdi` bytes: `REX.W`, the `8D /r` opcode, a
    `mod = 00` ModRM with the `%rsp`-base SIB escape, and the `0x24` SIB byte. -/
theorem encJLea_RSP0_bytes :
    encodeJBlock physAlloc [JInstr.lea "RDI" "RSP" "RSP" 0 (0 : Int)]
      = [0x48#8, 0x8d#8, 0x3c#8, 0x24#8] := by
  decide +kernel

/-- The gathered `leaq 8(%r13), %rax` bytes: `REX.W` with `REX.B` for the extended
    base, the `8D /r` opcode, and the forced `disp8` the `%r13` base takes. -/
theorem encJLea_R13_8_bytes :
    encodeJBlock physAlloc [JInstr.lea "RAX" "R13" "R13" 0 (8 : Int)]
      = [0x49#8, 0x8d#8, 0x45#8, 0x08#8] := by
  decide +kernel

end CatCrypt.Crypto.SecureCompilation.X86Backend.GatherMemOps
