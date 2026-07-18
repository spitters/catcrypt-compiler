/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
import CatCrypt.Crypto.SecureCompilation.X86Backend.LeafBytes

/-!
# A verified `Lprog → bytes` encoder for the LOOPED owned backend (task #658)

`ScalarEncoder.lean` (`encodeJInstr`/`encodeJBlock`) byte-encodes the *straight-line*
`JInstr` block — it has **no control-flow arm**. The looped / scheduled kernels
(Keccak, SHA-256/512-linear, Poseidon2, the `mpn` inner passes) are emitted as an
owned-RA `Lprog`/`Lcmd` carrying labels + `Lcond`/`Lgoto` back-edges (#538's
`loopLcmd`), and the **only** consumer of that form is `LprogAsmPrinter.renderLprogAtt`
→ AT&T text → `gas`. That keeps every looped kernel on the text+`gas` critical path.

This module is the byte analogue of `LprogAsmPrinter`: it encodes a looped owned-RA
`Lcmd`/`Lprog` directly to x86-64 machine bytes, with the control-flow arms
`ScalarEncoder` lacks:

* `jmp rel32` (`0xE9 cd`), `jcc rel32` (`0x0F 0x8x cd`) for the `Lcond` conditions,
  `call rel32` (`0xE8 cd`), `ret` (`0xC3`), `push`/`pop reg` (`0x50+r` / `0x58+r`);
* the straight-line body `Lopn` arms are encoded by **reusing** `ScalarEncoder`'s
  shape encoders (`encAluRR`/`encAluImm`/`encMemMov`/…) via a `LinstrR → JInstr 64`
  bridge over the operand-resolution `LprogAsmPrinter` already defines.

## Two-pass label resolution

`encodeLcmd` is a **two-pass** assembler over the looped body:

* **pass 1** computes each `Llabel`'s byte offset by encoding every instruction with
  a placeholder (`0`) displacement. The rel32 forms have a **displacement-independent
  length** (`jmp`/`jcc`/`call` are always 5/6/5 bytes regardless of the target), so a
  placeholder pass measures every label offset exactly.
* **pass 2** re-encodes, backpatching each `jmp`/`jcc`/`call` rel32 to
  `target_offset − insn_end_offset` (the x86 rel32 is relative to the **end** of the
  branch instruction). The label table from pass 1 supplies `target_offset`.

The whole looped body's bytes are then wrapped by `LeafBytes`/`ElfObject` into a
linkable `.o` (`encodeLfundefObject`) — the same multi-symbol stitcher the
straight-line leaves use, now over a body with internal control flow.

## Trust edge

The straight-line `Lopn` arms inherit `SailX86Decoder`'s `decode (encode i) = id`
round-trip (they reduce to `ScalarEncoder` shape encoders). The new control-flow
arms get their own decode round-trips here (`roundtrip_jmp32`/`roundtrip_jcc32`/
`roundtrip_call32`/`roundtrip_ret`): the rel32 displacement is recovered exactly.
`push`/`pop` are the trusted leaf-ABI scaffold (no Sail-x86 GP-stack semantics in
the ACL2 model — the existing `LeafBytes` tier), marked gas-pinned honestly in the
`trust_edge_cf` tally.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-! ## 1. Uppercase physical-register name → GP number

The owned-RA body names registers uppercase (`"RAX"`, `"R8"`), unlike the `%rN`
names `ScalarEncoder.gpNum` reads. This is the `LprogAsmPrinter.gpReg64` table
collapsed to a number. Spill / qsave / mem names are handled separately (they are
memory operands). An out-of-table name reads as `0`. -/

/-- The SDM register number `0..15` of an uppercase physical GP name. -/
def gpNumU (r : String) : Nat :=
  match r with
  | "RAX" => 0  | "RCX" => 1  | "RDX" => 2  | "RBX" => 3
  | "RSP" => 4  | "RBP" => 5  | "RSI" => 6  | "RDI" => 7
  | "R8"  => 8  | "R9"  => 9  | "R10" => 10 | "R11" => 11
  | "R12" => 12 | "R13" => 13 | "R14" => 14 | "R15" => 15
  | _     => 0

/-- `gpNumU` always lands in the GP range `0..15` (16-way table, `0` fallback). -/
theorem gpNumU_lt_16 (r : String) : gpNumU r < 16 := by
  unfold gpNumU; split <;> omega

/-! ## 1b. Width-aware REX with elision (task #660)

The `ScalarEncoder` shape encoders (`encAluRR`/`encMemMov`/`encMovImm`/…) hardcode
`rex 1 …` (always `REX.W=1`, the 64-bit operand size) because the straight-line
`JInstr` scalar path is U64 throughout. The **looped** owned-RA bodies carry a
per-`Lopn` width tag (`LprogAsmPrinter.mnemWidth`: `64` iff the mnemonic ends `:64`
or is `MOVQ`, else `32`) — SHA-256-linear is a U32 body, where every reg-reg /
imm / shift op must encode `REX.W=0`. And on x86-64, a `REX.W=0` prefix whose
extension bits `R`/`X`/`B` are all clear is **redundant** — `gas` (and every
assembler) **omits** the `0x40` byte entirely (a bare `89 d8` for `movl %ebx,%eax`,
not `40 89 d8`). For a U32 op that *does* touch `r8`–`r15`, the REX byte is present
but `W=0` (`41`/`44`/`45`, never `48`+).

`rexW` is the op-width `W` bit (`1` for U64, `0` for U32). `rexOpt` builds the REX
**prefix list**: empty when `W=0` ∧ `R=X=B=0` (the elision), else the single REX
byte. For `W=1` it is always present (the U64 path is byte-identical to the old
`rex 1 …`, since `0x48`+ is never elided). -/

/-- The `W` bit for an op width in bits (`64 → 1`, anything else → `0`). -/
def rexW (width : Nat) : Nat := if width = 64 then 1 else 0

/-- The width-aware REX **prefix list**: `[]` (elided) iff `w = 0 ∧ r = x = b = 0`,
    else the single REX byte `rex w r x b`. For `w = 1` always a singleton (`0x48`+
    is never elided), so the U64 path reproduces the hardcoded `rex 1 …` byte
    exactly; for `w = 0` low-reg ops the `0x40` byte is omitted (gas-identical),
    and `r8`–`r15` ops keep a `41`/`44`/`45` byte. -/
def rexOpt (w r x b : Nat) : List (BitVec 8) :=
  if w = 0 ∧ r = 0 ∧ x = 0 ∧ b = 0 then []
  else [BitVec.ofNat 8 (rex w r x b)]

/-- Width-aware reg-reg ALU/MOV (`op %src,%dst`), the width-threading analogue of
    `ScalarEncoder.encAluRR`: `reg`=src, `rm`=dst, REX elided per `rexOpt`. -/
def encAluRRw (w op d s : Nat) : List (BitVec 8) :=
  rexOpt w (bit s 3) 0 (bit d 3) ++ [BitVec.ofNat 8 op, BitVec.ofNat 8 (modRMReg s d)]

/-- Width-aware `0F`-map reg-reg (`IMUL`/`CMOVcc`): `reg`=dst, `rm`=src. -/
def enc0FRRw (w op d s : Nat) : List (BitVec 8) :=
  rexOpt w (bit d 3) 0 (bit s 3)
    ++ [BitVec.ofNat 8 0x0f, BitVec.ofNat 8 op, BitVec.ofNat 8 (modRMReg d s)]

/-- Width-aware `MOV $imm32, %dst` (`C7 /0 id`). -/
def encMovImmw (w d v : Nat) : List (BitVec 8) :=
  rexOpt w 0 0 (bit d 3) ++ [BitVec.ofNat 8 0xc7, BitVec.ofNat 8 (modRMReg 0 d)] ++ imm32LE v

/-- Width-aware imm-source ALU (`81 /digit id`): `reg`=digit, `rm`=dst, `imm32`. -/
def encAluImmw (w digit d v : Nat) : List (BitVec 8) :=
  rexOpt w 0 0 (bit d 3) ++ [BitVec.ofNat 8 0x81, BitVec.ofNat 8 (modRMReg digit d)] ++ imm32LE v

/-- Width-aware shift-by-`imm8` (`C1 /ext ib`): `reg`=ext, `rm`=dst, then `imm8`. -/
def encShiftImmw (w ext d imm : Nat) : List (BitVec 8) :=
  rexOpt w 0 0 (bit d 3)
    ++ [BitVec.ofNat 8 0xc1, BitVec.ofNat 8 (modRMReg ext d), BitVec.ofNat 8 (imm &&& 0xff)]

/-- Width-aware `MOV` between a register and `[base + off]`: `op` = `0x8B`/`0x89`,
    `reg`=`r`. The width-threading analogue of `encMemMov`; the ModRM/SIB/disp tail
    is the shared base-aware `ScalarEncoder.memTail`, so the SIB escape (base low-3
    = 4) and forced-disp8 RIP escape (base low-3 = 5) are handled for all bases. -/
def encMemMovw (w op r base : Nat) (off : Int) : List (BitVec 8) :=
  let pfx := rexOpt w (bit r 3) 0 (bit base 3) ++ [BitVec.ofNat 8 op]
  pfx ++ memTail r base off

/-! ## 2. The control-flow byte encoders (the arms `ScalarEncoder` lacks)

These are the rel32 / single-byte forms. The rel32 displacement `d` is the signed
distance from the **end** of the branch instruction to the target (`disp32LE` is the
two's-complement LE image, already in `ScalarEncoder`). `cd` is always 4 bytes, so
each form has a fixed length independent of `d` — the property pass-1 measurement
relies on. -/

/-- `jmp rel32` (`E9 cd`): 5 bytes. -/
def encJmp32 (d : Int) : List (BitVec 8) :=
  BitVec.ofNat 8 0xe9 :: disp32LE d

/-- The second opcode byte of a `jcc rel32` (`0F 8x`) for an x86 condition-code
    name — the byte-level analogue of `LprogAsmPrinter.attCC`'s Jcc map. The
    `0F 8x` tower: `JO 80 JNO 81 JB 82 JAE 83 JE 84 JNE 85 JBE 86 JA 87 JS 88
    JNS 89 … JL 8C JGE 8D JLE 8E JG 8F`. Mirrors the same condition synonyms
    `attCC` accepts (`Z→E`, `NZ→NE`, `C→B`, `NC→AE`). Unknown ⇒ `0x85` (`JNE`),
    the safe never-silently-wrong fallback (a bad cc would also fail the diff KAT). -/
def jccOpcode : String → Nat
  | "O"  => 0x80 | "NO" => 0x81
  | "B"  => 0x82 | "C"  => 0x82 | "AE" => 0x83 | "NC" => 0x83
  | "E"  => 0x84 | "Z"  => 0x84 | "NE" => 0x85 | "NZ" => 0x85
  | "BE" => 0x86 | "A"  => 0x87
  | "S"  => 0x88 | "NS" => 0x89
  | "L"  => 0x8c | "GE" => 0x8d | "LE" => 0x8e | "G" => 0x8f
  | _    => 0x85

/-- `jcc rel32` (`0F 8x cd`): 6 bytes. `cc` is the condition-code name. -/
def encJcc32 (cc : String) (d : Int) : List (BitVec 8) :=
  BitVec.ofNat 8 0x0f :: BitVec.ofNat 8 (jccOpcode cc) :: disp32LE d

/-- `call rel32` (`E8 cd`): 5 bytes. -/
def encCall32 (d : Int) : List (BitVec 8) :=
  BitVec.ofNat 8 0xe8 :: disp32LE d

/-- `ret` (`C3`): 1 byte. -/
def encRetCF : List (BitVec 8) := [BitVec.ofNat 8 0xc3]

/-! ## 3. Straight-line `Lopn` → bytes via a `JInstr 64` bridge

The two-address owned-RA body `Lopn` arms (`MOV`/`ADD`/`SUB`/`ADC`/`SBB`/`AND`/`OR`/
`XOR`/`MUL`/shifts/`CMOVcc`/`LOAD`/`STORE`) denote exactly the straight-line
`JInstr 64` forms `ScalarEncoder` already encodes. We bridge each arm to its
`JInstr 64` and reuse `encodeJInstr` under the identity allocation — the register
names are already physical, so the allocation is name-as-itself.

`LprogAsmPrinter`'s renderer resolves `mem.<base>.<off>` to `off(%base)`, a spill
`k.N` / qsave `qsave.X` to `off(%rsp)`, and a bare reg to `%rN`; here the `mem.*`
operand becomes `encMemMov`'s `(base, off)`, the spill/qsave operand becomes
`encRspMem`'s `(%rsp, off)` (with the mandatory SIB byte `0x24`) at the SAME offset
`LprogAsmPrinter.spillFrameOff`/`qsaveFrameOff` compute (the frame size + body-uniform
spill width are threaded through `encodeLcmd`), and the bare reg becomes its `gpNumU`.
A genuinely uncovered form (mem-mem, or an immediate written directly to a spill) is
left as a visible empty byte list flagged in the residual rather than mis-encoded. -/

/-- Parse a `mem.<base>.<off>` operand name to `(baseRegNum, offset)`. `none` if the
    name is not a memory operand. Bare physical registers are encoded directly off
    `gpNumU`, bypassing the string-allocation `regOf`/`gpNum` the `JInstr` encoder
    threads. -/
def parseMemName (n : String) : Option (Nat × Int) :=
  if "mem.".isPrefixOf n then
    let rest := (n.drop 4).toString
    match rest.splitOn "." with
    | [base, off] =>
        match String.toNat? off with
        | some o => some (gpNumU base, Int.ofNat o)
        | none => none
    | _ => none
  else none

/-- A `%rsp`-relative spill (`k.N`) or ABI save (`qsave.X`) operand name. These ARE
    memory operands (`[%rsp + frameOffset]`). They are now byte-encoded (the frame
    size + body-uniform spill width are threaded through `encodeLcmd`), via
    `spillQsaveOff` + the RSP-SIB memory encoder `encRspMem`. A name that is neither a
    recognised spill/qsave NOR a `mem.*` NOR a bare GP register is still NOT covered;
    `encTwoAddr` keeps the visible-empty guard for those residual forms only. -/
def isSpillOrQsave (n : String) : Bool :=
  "k.".isPrefixOf n || "qsave.".isPrefixOf n

/-- The `%rsp`-relative frame offset of a spill (`k.N`) or ABI-save (`qsave.X`)
    operand name, **matching `LprogAsmPrinter.resolveName` exactly**: a spill `k.idx`
    resolves to `spillFrameOff frame spillW idx`, a save `qsave.X` to
    `qsaveFrameOff frame X`. `none` for an unparseable spill/qsave name (so the
    caller surfaces it rather than mis-resolving). The base register is always `%rsp`
    (SDM number 4). -/
def spillQsaveOff (frame spillW : Nat) (n : String) : Option Int :=
  if "k.".isPrefixOf n then
    match String.toNat? (n.drop 2).toString with
    | some idx => some (spillFrameOff frame spillW idx)
    | none => none
  else if "qsave.".isPrefixOf n then
    qsaveFrameOff frame ((n.drop 6).toString)
  else none

/-- A `MOV` between a register and `[%rsp + off]`. `%rsp` (SDM number 4) has
    `r/m = 100` in the ModRM, which x86 reserves as the **SIB escape** — so a base of
    `%rsp` REQUIRES a SIB byte. The SIB for `[%rsp + disp]` (no index) is `0x24`
    (`scale=0`, `index=100` = "no index", `base=100` = `%rsp`); `encMemMov` does NOT
    emit it (its `modRMMem` would mis-decode `%rsp` as the SIB escape with a missing
    SIB), so this is the dedicated RSP-base encoder. `op` = `0x8B` (load `r ← m`) or
    `0x89` (store `m ← r`); `r` is the register operand. The `mod`/disp selection is
    the same as `encMemMov` (disp0 / signed disp8 / disp32), but with the SIB byte
    inserted after the ModRM. (`off = 0` still emits a `mod=00` SIB form, which is a
    valid `[%rsp]` no-displacement address; the frame offsets here are always
    positive and non-zero, but the arm is kept total.) -/
def encRspMem (w op r : Nat) (off : Int) : List (BitVec 8) :=
  let pfx := rexOpt w (bit r 3) 0 0 ++ [BitVec.ofNat 8 op]
  let sib : BitVec 8 := BitVec.ofNat 8 0x24
  if off = 0 then
    pfx ++ [BitVec.ofNat 8 (modRMMem 0 r 4), sib]
  else if -128 ≤ off ∧ off ≤ 127 then
    pfx ++ [BitVec.ofNat 8 (modRMMem 1 r 4), sib, disp8 off]
  else
    pfx ++ (BitVec.ofNat 8 (modRMMem 2 r 4) :: sib :: disp32LE off)

/-- Encode a two-address binop / move whose AT&T form is `op<sz> src, dst`, given the
    one-byte ALU opcode `op`, the frame size + body-uniform spill width (to resolve
    `%rsp`-relative spill/qsave operands to their offset, matching
    `LprogAsmPrinter`), and the resolved dst/src operands. Each operand may be a bare
    register, a `mem.*` (base-pointer-relative), or a spill/qsave (`%rsp`-relative).

    The owned looped bodies pair a register with at most one memory operand
    (`LOAD`/`STORE`/spill reload/spill store): a reg-reg pair uses `encAluRR`, a
    `mem.*` source/dest uses `encMemMov`, and a spill/qsave source/dest uses the
    RSP-SIB encoder `encRspMem` (base `%rsp`, the SIB byte `0x24` form). A genuinely
    uncovered shape (mem-mem, or a name that is neither reg / `mem.*` / spill / qsave)
    still returns `[]` (visible, KAT-catchable) rather than mis-resolving. The arm only
    encodes the **move** opcode for a memory operand (`op` is `0x89`/`0x8b` for
    `STORE`/`LOAD`); an ALU op against a spill (`add k.N, %rN`) is not produced by the
    owned bodies (the reload is materialised first) and is left to the residual. -/
def encTwoAddr (frame spillW w : Nat) (op : Nat) (d s : LOperand) : List (BitVec 8) :=
  match d, s with
  | .reg dn, .reg sn =>
      match spillQsaveOff frame spillW dn, spillQsaveOff frame spillW sn with
      -- store to a spill/qsave slot: dst is `%rsp`-relative, src is a register.
      | some off, none =>
          if isSpillOrQsave sn then []  -- mem,mem (spill→spill) not emitted
          else encRspMem w 0x89 (gpNumU sn) off
      -- reload from a spill/qsave slot: src is `%rsp`-relative, dst is a register.
      | none, some off =>
          if isSpillOrQsave dn then []
          else encRspMem w 0x8b (gpNumU dn) off
      | some _, some _ => []  -- spill,spill not emitted (residual)
      | none, none =>
          if isSpillOrQsave dn || isSpillOrQsave sn then []  -- unparseable spill name
          else
            match parseMemName dn, parseMemName sn with
            | none, none => encAluRRw w op (gpNumU dn) (gpNumU sn)
            -- store: dst is memory, op = 0x89 (MOV r/m←r). `reg`=src, base=dst mem.
            | some (bb, off), none => encMemMovw w 0x89 (gpNumU sn) bb off
            -- load: src is memory, op = 0x8B (MOV r←r/m). `reg`=dst, base=src mem.
            | none, some (bb, off) => encMemMovw w 0x8b (gpNumU dn) bb off
            | some _, some _ => []  -- mem,mem not emitted (residual)
  | _, _ => []

/-- The group-1 opcode-extension `/digit` for an ALU mnemonic (ADD=/0 … CMP=/7),
    the SDM group-1 table both the `81 /digit id` and `83 /digit ib` forms select. -/
def aluImmDigit : String → Option Nat
  | "ADD" => some 0 | "OR" => some 1 | "ADC" => some 2 | "SBB" => some 3
  | "AND" => some 4 | "SUB" => some 5 | "XOR" => some 6 | "CMP" => some 7
  | _ => none

/-- The group-2 opcode-extension `/ext` for a shift mnemonic (the `C1 /ext ib`
    shift-by-imm8 form): `SHL = /4`, `SHR = /5`, `SAR = /7`. The owned hash bodies
    rotate via `SHL`/`SHR` + `OR` (the σ/Σ sigma functions), so the shift-by-imm8
    `encShiftImm` form is exactly what gas emits for `shl<sz> $n, %d` / `shr<sz>`. -/
def shiftImmExt : String → Option Nat
  | "SHL" => some 4 | "SHR" => some 5 | "SAR" => some 7
  | _ => none

/-- The **shift-by-1 short form** `D1 /ext` (`shl/shr/sar $1, %d`): `REX.W`, opcode
    `0xD1`, `ModRM(11, ext, d)` — three bytes, NO immediate byte (the count of 1 is
    implicit in the opcode). This is the form gas (and the SDM) selects for a shift
    count of exactly 1, where the generic `C1 /ext ib` form would waste an `imm8`
    byte. Matching it is required for byte-identity: the σ/Σ sigma rotates include
    single-bit shifts (`shrq $1`). -/
def encShift1 (w ext d : Nat) : List (BitVec 8) :=
  rexOpt w 0 0 (bit d 3) ++ [BitVec.ofNat 8 0xd1, BitVec.ofNat 8 (modRMReg ext d)]

/-- The **short** sign-extended-imm8 ALU form `op $imm8, %dst` (`83 /digit ib`):
    `REX.W`, opcode `0x83`, `ModRM(11, digit, dst)`, one `imm8` byte. This is the
    encoding `gas` (and every assembler) picks for an immediate that fits a signed
    byte (`-128 ≤ v ≤ 127`), where the CPU sign-extends the byte to 64 bits — 4 bytes
    vs the 7 of `81 /digit id`. Emitting it matches the gas baseline byte-for-byte. -/
def encAluImm8 (w digit d v : Nat) : List (BitVec 8) :=
  rexOpt w 0 0 (bit d 3)
    ++ [BitVec.ofNat 8 0x83, BitVec.ofNat 8 (modRMReg digit d), BitVec.ofNat 8 (v &&& 0xff)]

/-- Does the immediate `v` (the operand-width-image of the value) fit the
    **sign-extended imm8** short ALU form (`83 /digit ib`) under op width `w`?
    `gas` picks that 4-byte form whenever the operand-size value is in
    `[-128, 127]`, i.e. small-positive (`v < 128`) OR small-negative whose
    width-`W` two's-complement image is `≥ 2^W - 128`. The U32 mask `-1`
    (`v = 0xffffffff`) hits the negative branch with `W = 32`
    (`2^32 - 128 ≤ 0xffffffff`), so gas emits `83 /6 FF` not `81 /6 FF FF FF FF`.
    The bit width is `64` iff `w = 1`, else `32`. -/
def fitsImm8S (w v : Nat) : Bool :=
  let bits := if w = 1 then 64 else 32
  v < 128 || (2 ^ bits - 128 ≤ v && v < 2 ^ bits)

/-- `IMUL $imm8, %dst, %dst` (`6B /r ib`): the sign-extended-imm8 three-operand
    self-multiply `REX.W`, opcode `0x6B`, `ModRM(11, dst, dst)`, one `imm8`. gas
    picks this 4-byte form for an immediate that fits a signed byte (the fe25519
    Solinas folds `imul $19` / `imul $38`), where the `69 /r id` imm32 form would
    waste three bytes. Width-aware REX (always `W=1` here — the field IMUL is U64). -/
def encImulImm8w (w d v : Nat) : List (BitVec 8) :=
  rexOpt w (bit d 3) 0 (bit d 3)
    ++ [BitVec.ofNat 8 0x6b, BitVec.ofNat 8 (modRMReg d d), BitVec.ofNat 8 (v &&& 0xff)]

/-- `IMUL $imm32, %dst, %dst` (`69 /r id`): the imm32 three-operand self-multiply,
    the form gas selects when the immediate does NOT fit a signed byte. -/
def encImulImm32w (w d v : Nat) : List (BitVec 8) :=
  rexOpt w (bit d 3) 0 (bit d 3)
    ++ [BitVec.ofNat 8 0x69, BitVec.ofNat 8 (modRMReg d d)] ++ imm32LE v

/-- Encode an immediate-source ALU/MOV op (`op $imm, %dst`). For ALU mnemonics this
    mirrors the assembler's form selection: the **short** `83 /digit ib` (sign-
    extended imm8) when the value fits a signed byte at the op width (`fitsImm8S w v`
    — the common small-stride / counter case `+8`, `cmp $0`, and the U32 mask `-1`),
    else the `81 /digit id` imm32 form. `MOV` uses `C7 /0`/`B8+r` (it has no
    `83`-style short form). The width `w` is the op's `REX.W` bit; for a U32 op the
    REX prefix is `REX.W=0` and is elided when no extension bit is set. This selection
    is what makes the encoder's bytes byte-identical to `renderLprogAtt → gas`. -/
def encImmOp (w : Nat) (base : String) (d : LOperand) (v : Nat) : List (BitVec 8) :=
  match d with
  | .reg dn =>
      -- An immediate written to a `%rsp`-relative spill/qsave slot (`mov $v, k.N`)
      -- uses the SDM imm-to-*memory* forms (`C7 /0` / `81 /digit` with a mem ModRM +
      -- SIB), a distinct encoder family the owned hash bodies do not produce (an
      -- immediate is loaded into a register, then spilled). Leave it as a visible
      -- residual rather than mis-encode it as an imm-to-register op against `%rax`.
      if isSpillOrQsave dn then []
      else
      let n := gpNumU dn
      -- gas picks the compact `C7 /0 id` (sign-extended imm32) `MOV` form whenever
      -- the 64-bit value fits a SIGNED 32-bit immediate — i.e. a small positive
      -- (`v < 2^31`) OR a small negative whose 64-bit two's-complement image is
      -- `≥ 2^64 - 2^31` (e.g. the all-ones mask `2^64-1` = `-1`, which gas emits as
      -- `movq $-1` → `C7 /0 FF FF FF FF`, 7 bytes). Only a value that genuinely needs
      -- all 64 bits falls to the 10-byte `B8+r io` `movabs` form. `JasminModel`'s
      -- `MOV $imm` semantics is width-agnostic on the stored value, so this is purely
      -- a gas-matching form selection (the decoded value is identical either way).
      let fitsImm32S : Bool := v < 2 ^ 31 || 2 ^ 64 - 2 ^ 31 ≤ v
      match base with
      -- `MOVQ` is 64-bit-only (`mnemWidth "MOVQ" = 64`), so its `w` is `1`; a plain
      -- `MOV` carries the body width `w` (U32 ⇒ `REX.W=0`, elided for low regs).
      | "MOV" => if fitsImm32S then encMovImmw w n v else encMovImm64 n v
      | "MOVQ" => if fitsImm32S then encMovImmw 1 n v else encMovImm64 n v
      -- `IMUL $imm, %d` (the `MUL` mnemonic with an immediate source): gas picks
      -- the `6B /r ib` sign-extended-imm8 form when the value fits a signed byte
      -- (the fe25519 Solinas `imul $19`/`imul $38`), else the `69 /r id` imm32 form.
      | "MUL" => if fitsImm8S w v then encImulImm8w w n v else encImulImm32w w n v
      | _ =>
        match shiftImmExt base with
        -- gas picks the `D1 /ext` 1-bit short form for a shift count of exactly 1
        -- (no imm byte), else the generic `C1 /ext ib` shift-by-imm8.
        | some ext => if v = 1 then encShift1 w ext n else encShiftImmw w ext n v
        | none =>
          match aluImmDigit base with
          | some digit =>
              if fitsImm8S w v then encAluImm8 w digit n v else encAluImmw w digit n v
          | none => []
  | _ => []

/-- The one-byte ALU opcode for a stripped two-address mnemonic (the same set
    `LprogAsmPrinter.attBase` renders, here as opcode bytes). `MUL` → `IMUL`
    (`0F AF`, handled separately via `enc0FRR`); `CMOVcc` likewise `0F`-map. -/
def aluOpcode : String → Option Nat
  | "ADD" => some 0x01 | "OR"  => some 0x09 | "ADC" => some 0x11
  | "SBB" => some 0x19 | "AND" => some 0x21 | "SUB" => some 0x29
  | "XOR" => some 0x31 | "MOV" => some 0x89
  -- `MOVQ` is the 64-bit-only move the ABI prologue/epilogue emits for the qsave
  -- park/restore (`MOVQ qsave.X, X` / `MOVQ X, qsave.X`) and the wide spill traffic
  -- (`stripWidthTag` leaves it intact — it carries no `:64` tag). Same opcode as
  -- `MOV` (`0x89` r/m←r); the encoders below always set `REX.W`, so the byte width
  -- is 64 regardless. Matches `LprogAsmPrinter.attBase`'s `"MOVQ" => "mov"`. -/
  | "MOVQ" => some 0x89
  | "LOAD" => some 0x8b | "STORE" => some 0x89
  | _ => none

/-- The `0F`-map opcode for the two-byte two-address forms. -/
def twoByteOpcode : String → Option Nat
  | "MUL"    => some 0xaf
  | "CMOVE"  => some 0x44 | "CMOVNE" => some 0x45
  | "CMOVB"  => some 0x42 | "CMOVAE" => some 0x43
  | "CMOVL"  => some 0x4c | "CMOVGE" => some 0x4d
  | _ => none

/-! ### BMI2/ADX byte arms — DELEGATE to the `ScalarEncoder` 3-operand encoders

The owned field/bignum bodies (`fe25519` mul/sqr/mul121666, BLS-Fp Montgomery,
safegcd accumulate) issue the BMI2 widening multiply `MULX` and the two
independent carry chains `ADCX`/`ADOX`. `ScalarEncoder` already byte-encodes these
faithfully (`encMulxRR`/`encMulxMem`/`encAdxCarry`, with their length lemmas and
the VEX `C4` / mandatory-prefix `66`/`F3 0F38 F6` byte layout). The `LinstrR` path
**reuses** those verbatim, bridging the owned-RA `Lopn` operand shapes to the
register/base numbers the `ScalarEncoder` encoders take. The implicit `MULX` src1
is `%rdx` (pinned by the kernel allocation, `yd → %rdx`), so it is NOT an operand
here — exactly as the hardware `mulx` reads `%rdx` as a side input.

* `MULX:64` — `Lopn [dstLo, dstHi] [src2]` → `encMulxRR (gpNumU dstHi) (gpNumU dstLo) (gpNumU src2)`;
* `MULXMEM:64` — `Lopn [dstLo, dstHi] [mem.base.off]` → `encMulxMem (gpNumU dstHi) (gpNumU dstLo) base off`;
* `ADCX:64` / `ADOX:64` two-source bridge — `Lopn [dst] [dst, src]` →
  `encAdxCarry (0x66/0xf3) (gpNumU dst) (gpNumU src)` (carry-in already in CF/OF);
* `ADCX:64` / `ADOX:64` three-source Com-front form — `Lopn [dst] [a, src, cin]`
  (`opToLinstrR .addCarryLo`, the explicit-carry-in VALUE form) →
  `mov a,dst`? ++ `bt $0, cin` ++ `adcx/adox src,dst` (`encAluRRw`/`encBtImm`/
  `encAdxCarry`), mirroring `renderLopn`'s ADX data arm arm-for-arm;
* `ADCXHI:64` / `ADOXHI:64` carry-out bindings — `Lopn [dst] [a, src, cin]`
  (`opToLinstrR .addCarryHi`) → `setc/seto dst8` + `movzbq` (`encSetccMovzx`),
  mirroring `renderLinstrR`'s carry-out materialisation arm;
* `SETC` — `Lopn [dst] []` → `setb dst8` + `movzbq` (`encSetccMovzx 0x92`),
  mirroring `renderLopn`'s SETC arm.

`MULX` is U64-only (the widening multiply is `W=1`), so `encMulxRR`/`encMulxMem`
hardcode `W=1`; `ADCX`/`ADOX` likewise hardcode `REX.W` in `encAdxCarry`. The width
tag (`:64`) is always present on these mnemonics in the field bodies. -/

/-- The mandatory prefix byte for an ADX carry mnemonic: `0x66` (`ADCX`, CF chain),
    `0xF3` (`ADOX`, OF chain). `none` for a non-ADX mnemonic. -/
def adxPrefix : String → Option Nat
  | "ADCX" => some 0x66 | "ADOX" => some 0xf3
  | _ => none

/-- The `SETcc` second opcode byte for a carry-out binding base: `0x90` (`SETO`,
    reads OF — the `ADOXHI` chain) else `0x92` (`SETC`/`SETB`, reads CF — `ADCXHI`
    and the standalone `SETC`). Mirrors `renderLinstrR`'s `setc`/`seto` selection. -/
def carryOutSetccOp (base : String) : Nat :=
  if base == "ADOXHI" then 0x90 else 0x92

/-- `SETcc %d8` + `MOVZBQ %d8, %d64`: the flag→GPR materialisation pair, generalised
    over the `SETcc` opcode byte `op` (`0x92` = `setc`/`setb`, CF; `0x90` = `seto`,
    OF). The byte image of the text path's `setc/seto %d8; movzbq %d8, %d64` lines
    (`renderLinstrR`'s carry-out arm and `renderLopn`'s `SETC` arm). Gas-pinned:
    `setc %r8b; movzbq %r8b,%r8` = `41 0F 92 C0  4D 0F B6 C0`,
    `seto %al;  movzbq %al,%rax` = `0F 90 C0  48 0F B6 C0`,
    `setc %bpl; movzbq %bpl,%rbp` = `40 0F 92 C5  48 0F B6 ED`.
    The `SETcc` REX is `0x41` (`REX.B`) for `d ≥ 8`, and the BARE `0x40` for
    `d ∈ {4..7}` (`%spl/%bpl/%sil/%dil` — without REX the ModRM would select
    `AH/CH/DH/BH`); low regs `d < 4` need none. The `MOVZBQ` always carries `REX.W`,
    so its byte source is the REX-selected low byte for all 16 GPs.
    `encSetccMovzx 0x92 d = ScalarEncoder.encSetcMovzx d` off the `{4..7}` band
    (`encSetccMovzx_setc_agree`). -/
def encSetccMovzx (op d : Nat) : List (BitVec 8) :=
  let setcc : List Nat :=
    (if bit d 3 = 1 then [rex 0 0 0 1] else if 4 ≤ d ∧ d < 8 then [rex 0 0 0 0] else [])
      ++ [0x0f, op, modRMReg 0 d]
  let movzx : List Nat := [rex 1 (bit d 3) 0 (bit d 3), 0x0f, 0xb6, modRMReg d d]
  (setcc ++ movzx).map (BitVec.ofNat 8)

/-- `BT $imm8, %reg` (group-8 `0F BA /4 ib`): copy bit `imm` of the register into
    `CF`. The carry-in materialisation of the three-source ADX data arm
    (`bt $0, cin` — the IR passes the carry-in as a VALUE, `renderLopn` prints the
    same line). Width-aware REX with elision per `rexOpt`. Gas-pinned:
    `btq $0,%rcx` = `48 0F BA E1 00`, `btq $0,%r12` = `49 0F BA E4 00`,
    `btl $0,%ecx` = `0F BA E1 00` (REX elided). -/
def encBtImm (w d imm : Nat) : List (BitVec 8) :=
  rexOpt w 0 0 (bit d 3)
    ++ [BitVec.ofNat 8 0x0f, BitVec.ofNat 8 0xba, BitVec.ofNat 8 (modRMReg 4 d),
        BitVec.ofNat 8 (imm &&& 0xff)]

/-! ### Count-in-tag register-source shift arm (rotation correctness, task track-A #5)

The `Com.toLprogPhysAbi` physical body emits the σ/Σ rotate shifts as a
**count-in-mnemonic-tag, register-source** `Lopn`: `Lopn [d] "SHR:19:64" [reg s]`
(and the `SHL` dual). The count `n` lives in the mnemonic (`stripWidthTag` of it is
`"SHR:19"`), the source is a register — NOT a separate `.imm` operand. The
`encImmOp` shift arm (`shiftImmExt`) fires only on an `.imm`-source `SHL`/`SHR`, so
this count-in-tag form matched no `aluOpcode`/`twoByteOpcode`/`shiftImmExt` and
`encodeLopn` returned `[]` — **silently dropping every rotation** in the
rotation-heavy GoldenPath kernels (asconSigma0's four Σ₀ rotations, SipHash, Sha512,
…). This arm closes that correctness bug: it emits the exact `shr/shl r64, imm8`
bytes the `.imm`-source arm would for the same count, reading `n` from the tag.

`tagShiftExt` is the **prefix-only** detector (`group-2 /ext`: `SHL = /4`,
`SHR = /5`) — it does NOT touch the decimal count, so it is **kernel-reducible**
(`decide +kernel`) on a closed tag, unlike the `String.toNat?`-bearing
`shiftCountOf`. The count is recovered independently by `tagShiftCount` (mirroring
`LoweringExtended.shiftCountOf` exactly: `(String.ofList (base.toList.drop 4)).toNat?`),
which the dispatch never needs to reduce to *select* the arm — only to fill the
`imm8`. This split keeps the arm-selection dispatch `decide +kernel`-clean while the
emitted count is the same `n` the gather's `lowerShiftImmJ` lowers. -/

/-- The group-2 shift `/ext` of a count-in-tag base (`"SHL:<n>"` → `/4`,
    `"SHR:<n>"` → `/5`), by the **4-character prefix only** (`take 4 == "SHL:"/"SHR:"`
    over `List Char`, so it kernel-reduces on a closed base — no `toNat?`). `none`
    for any non-shift base. `SAR` has no count-in-tag exporter form (the physical
    body's arithmetic-right shifts also carry the count in the tag, but the σ/Σ
    rotates that need this fix are logical `SHR`/`SHL`); add `"SAR:"` here if a
    count-in-tag `SAR` body is ever emitted. -/
def tagShiftExt (base : String) : Option Nat :=
  let p := base.toList.take 4
  if p == "SHL:".toList then some 4
  else if p == "SHR:".toList then some 5
  else none

/-- The shift count of a count-in-tag base (`"SHR:19"` → `19`), the decimal suffix
    after the 4-char `"SHL:"`/`"SHR:"` prefix. Mirrors
    `LoweringExtended.shiftCountOf` exactly, so the byte encoder emits the SAME count
    `n` the JInstr gather's `lowerShiftImmJ`/`parseShiftMnem` lowers — the two sides'
    shift counts coincide definitionally. (`String.toNat?` is not kernel-reducible,
    so the *value* of `n` is `#eval`/`native_decide`-only; the arm SELECTION above is
    kernel-clean, which is what the dispatch lemmas need.) `0` for an unparseable
    suffix (never the case for an exporter-emitted mnemonic). -/
def tagShiftCount (base : String) : Nat :=
  ((String.ofList (base.toList.drop 4)).toNat?).getD 0

/-- The bytes of a count-in-tag register-source shift, given the op width bit `w`,
    the group-2 `/ext` (`tagShiftExt`), the destination GP number `dn`, and the
    tag-stripped base `base` (to read the count). Picks the `D1 /ext` 1-bit short
    form (no `imm8`) for a count of exactly `1`, else the generic `C1 /ext ib`
    shift-by-`imm8` — the SAME `encShift1`/`encShiftImmw` form-selection `encImmOp`
    applies to an `.imm`-source shift, so a count-in-tag shift and an `.imm`-source
    shift of the same count encode to identical bytes. -/
def encTagShift (w ext dn : Nat) (base : String) : List (BitVec 8) :=
  let n := tagShiftCount base
  if n = 1 then encShift1 w ext dn else encShiftImmw w ext dn n

/-! ## 4. `encodeLinstrR` — the per-instruction byte encoder

One `LinstrR` → its bytes. The straight-line `Lopn` arms reuse the `ScalarEncoder`
shape encoders (via the bridges above); the control-flow arms use the rel32 / single-
byte encoders of §2. The displacement for a `Lgoto`/`Lcond` is supplied by the
caller (the two-pass resolver); a standalone encode uses placeholder `0`. -/

/-- The **short** `jmp rel8` form (`EB cb`): 2 bytes. The assembler picks it when the
    displacement fits a signed byte (`-128 ≤ d ≤ 127`). -/
def encJmp8 (d : Int) : List (BitVec 8) :=
  [BitVec.ofNat 8 0xeb, disp8 d]

/-- The **short** `jcc rel8` form (`70+cc cb`): 2 bytes. The short-form condition
    tower is `0x70 + (jccOpcode cc − 0x80)` (the `0F 8x` long opcode minus the `0x80`
    base, added to the `0x70` one-byte base), so `JNE` (`0F 85`) ↔ `75`. -/
def encJcc8 (cc : String) (d : Int) : List (BitVec 8) :=
  [BitVec.ofNat 8 (0x70 + (jccOpcode cc - 0x80)), disp8 d]

/-- Does a signed displacement fit the rel8 short form? (`-128 ≤ d ≤ 127`.) -/
def fitsRel8 (d : Int) : Bool := -128 ≤ d ∧ d ≤ 127

/-- The straight-line (non-control-flow) `Lopn` byte encoding. Independent of any
    displacement; the control-flow arms are handled by `encodeCF`. -/
def encodeLopn (frame spillW : Nat) : LinstrR → List (BitVec 8)
  | .Lopn dsts opn srcs =>
      if isCarryOutBinding opn || isMulHiBinding opn then
        -- ADX carry-out binding (`ADCXHI`/`ADOXHI`): materialise the post-add flag
        -- into the destination GPR — the `setc`/`seto %d8` + `movzbq %d8, %d64`
        -- pair `renderLinstrR`'s carry-out arm prints (a standalone widening
        -- consumes the carry as a `reg 1` DATA value, so it MUST be materialised;
        -- dropping it silently corrupts the next limb). The MULX high-word binding
        -- (`MULXHI`) stays nil — a fused body has none (`fuseMulHiLprog` consumed
        -- the pair), and the flag/high word is the data op's side effect.
        if isCarryOutBinding opn then
          match dsts with
          | [.reg dn] => encSetccMovzx (carryOutSetccOp (stripWidthTag opn)) (gpNumU dn)
          | _ => []
        else []
      else
      let base := stripWidthTag opn
      -- The op width `w` is the `REX.W` bit of this `Lopn`: `1` iff the mnemonic
      -- carries the `:64` tag (or is `MOVQ`), else `0`. This is exactly the width
      -- `LprogAsmPrinter.mnemWidth` reads for the AT&T `l`/`q` size suffix, so the
      -- bytes track the text path's operand size — and a U32 op (`SHA-256-linear`)
      -- encodes `REX.W=0`, with the `0x40` byte elided for low registers.
      let w := rexW (mnemWidth opn)
      -- BMI2 `MULX` (two destinations `[dstLo, dstHi]`) — DELEGATE to
      -- `ScalarEncoder.encMulxRR`/`encMulxMem`. The implicit src1 (`%rdx`) is not
      -- an operand; `src2` is the single reg source (reg form) or a `mem.*` (mem
      -- form). Always U64 (`W=1` is baked into the `ScalarEncoder` encoders).
      if base == "MULX" then
        match dsts, srcs with
        | [.reg dlN, .reg dhN], [.reg s2] =>
            encMulxRR (gpNumU dhN) (gpNumU dlN) (gpNumU s2)
        | _, _ => []
      else if base == "MULXMEM" then
        match dsts, srcs with
        | [.reg dlN, .reg dhN], [.reg memName] =>
            match parseMemName memName with
            | some (bb, off) => encMulxMem (gpNumU dhN) (gpNumU dlN) bb off
            | none => []
        | _, _ => []
      else
      match adxPrefix base with
      -- ADX carry chains `ADCX`/`ADOX` (`Lopn [dst] [dst, src]`) — DELEGATE to
      -- `ScalarEncoder.encAdxCarry`. The carry-in is the implicit CF/OF flag (a
      -- side input, not an operand); the dst self-source `srcs[0]` is dropped.
      | some pfx =>
          match dsts, srcs with
          -- three-source IR form `[dst] [a, src, cin]` (`opToLinstrR .addCarryLo`):
          -- `d := a + src + cin` with the carry-in an explicit VALUE. Mirror
          -- `renderLopn`'s ADX data arm arm-for-arm: `mov a, d` (when `a ≠ d` —
          -- real x86 adcx/adox is two-address), `bt $0, cin` (materialise the
          -- carry-in into CF/OF; `mov` preserves flags, so the `bt → adcx`
          -- dependency is intact), then the two-address `adcx`/`adox src, d`.
          -- Register-resident operands only (the field/bignum rows keep the ADX
          -- chain in registers); a spill/qsave/`mem.*` operand is left as the
          -- visible empty byte list (KAT-catchable), never mis-encoded as `%rax`.
          | [.reg dn], [.reg an, .reg sn, .reg cn] =>
              if isSpillOrQsave dn || isSpillOrQsave an || isSpillOrQsave sn
                  || isSpillOrQsave cn || (parseMemName dn).isSome
                  || (parseMemName an).isSome || (parseMemName sn).isSome
                  || (parseMemName cn).isSome then []
              else
                (if an == dn then [] else encAluRRw w 0x89 (gpNumU dn) (gpNumU an))
                  ++ encBtImm w (gpNumU cn) 0
                  ++ encAdxCarry pfx (gpNumU dn) (gpNumU sn)
          -- two-source bridge form `[dst, src]` (`jinstrToLinstrR .adcx`/`.adox`):
          -- dst self-source, carry-in already IN the flag (the chained idiom).
          | [.reg dn], [_, .reg sn] => encAdxCarry pfx (gpNumU dn) (gpNumU sn)
          | [.reg dn], [.reg sn]    => encAdxCarry pfx (gpNumU dn) (gpNumU sn)
          | _, _ => []
      | none =>
      match dsts, srcs with
      -- `SETcc` (`SETC`) — one destination, ZERO data sources (the carry-in is the
      -- implicit CF flag): the `setb %d8; movzbq %d8, %d64` flag-materialisation
      -- pair, the byte image of `renderLopn`'s SETC arm (the open-coded carry
      -- chain `add; setc cy` keeps the carry across the loop back-edge).
      | [.reg dn], [] =>
          if base == "SETC" then encSetccMovzx 0x92 (gpNumU dn) else []
      | [d], [s] =>
          match s with
          | .imm v => encImmOp w base d v
          | _ =>
            -- Count-in-tag register-source shift (`SHR:<n>:64 [reg s]`): the rotate
            -- form `Com.toLprogPhysAbi` emits. The count is in `base` (the tag), the
            -- source a register — the destructive in-place `shr/shl %d, $n` (`d == s`,
            -- the gather materialises any `mov d, s` separately). Emits the SAME bytes
            -- the `.imm`-source shift arm would (was silently `[]` — dropped rotation).
            match tagShiftExt base, d with
            | some ext, .reg dn => encTagShift w ext (gpNumU dn) base
            | _, _ =>
              match aluOpcode base with
              | some op => encTwoAddr frame spillW w op d s
              | none =>
                match twoByteOpcode base, d, s with
                | some op, .reg dn, .reg sn => enc0FRRw w op (gpNumU dn) (gpNumU sn)
                | _, _, _ => []
      | [d], [_, s] =>
          match s with
          | .imm v => encImmOp w base d v
          | _ =>
            match tagShiftExt base, d with
            | some ext, .reg dn => encTagShift w ext (gpNumU dn) base
            | _, _ =>
              match aluOpcode base with
              | some op => encTwoAddr frame spillW w op d s
              | none =>
                match twoByteOpcode base, d, s with
                | some op, .reg dn, .reg sn => enc0FRRw w op (gpNumU dn) (gpNumU sn)
                | _, _, _ => []
      | _, _ => []
  | _ => []

/-- Encode one `LinstrR` given a resolver `dispOf` from a label to the signed rel32
    displacement from the **end of the LONG form** of this instruction, and the
    long-form-relative-to-short adjustment is folded in by `branchDisp`. Straight-line
    arms ignore `dispOf`; control-flow arms pick the short (`rel8`) form when the
    displacement fits a signed byte (matching the assembler), else the long form.
    Carry-out / MULX-high bindings and `Lret`/`Lalign`/`Llabel` produce no data bytes. -/
def encodeLinstrR (frame spillW : Nat) (dispOf : LLabel → Int) : LinstrR → List (BitVec 8)
  | .Lopn dsts opn srcs => encodeLopn frame spillW (.Lopn dsts opn srcs)
  | .Lret => []
  | .Lalign => []
  | .Llabel _ _ => []
  -- Local `Lgoto ("", l)` is an intra-function `jmp`. A *remote* `Lgoto (f, l)`
  -- would need an ELF relocation against `f` (out of scope: the looped POC kernels
  -- are single-function); it is encoded as a `jmp` to the in-table label offset.
  | .Lgoto (_, l) =>
      let d := dispOf l
      if fitsRel8 d then encJmp8 d else encJmp32 d
  | .Lcond (.reg cc) l =>
      let d := dispOf l
      if fitsRel8 d then encJcc8 cc d else encJcc32 cc d
  | .Lcond _ _ => []
  -- `call` is always rel32 (the assembler does not short-form a near call).
  | .Lcall _ (_, l) => encCall32 (dispOf l)
  | _ => []

/-! ## 5. Two-pass label resolution with branch relaxation

`jcc`/`jmp` have a short (`rel8`, 2-byte) and long (`rel32`, 5/6-byte) form, and the
assembler picks the short one when the target is in range. The length of a branch
therefore depends on its displacement, which depends on label offsets, which depend
on branch lengths — the classic assembler **relaxation** fixpoint. We model it
exactly: start from a length estimate, recompute the offset table and the resulting
branch lengths, and iterate to a fixpoint (bounded by a fuel that is the instruction
count — each relaxation pass can only shorten, so it converges in `≤ #branches`
passes). This is what makes the bytes match `gas`, which performs the same
relaxation. -/

/-- The length (in bytes) of an instruction's encoding under a resolved-displacement
    function `dispOf`. For a branch this reflects the short/long choice; for a
    straight-line op it is the fixed encoding length. -/
def instrLenAt (frame spillW : Nat) (dispOf : LLabel → Int) (i : LinstrR) : Nat :=
  (encodeLinstrR frame spillW dispOf i).length

/-- One relaxation pass: given the *current* label-offset table `tbl`, fold over the
    body computing each instruction's length under the displacements `tbl` induces
    (`disp l = tbl[l] − instrEnd`), and record the NEW offset of each label. Returns
    the new `(label ↦ offset)` table. A fixpoint of `relaxPass` is a consistent
    layout: every branch's length matches the offsets its displacement produces. -/
def lookupLabel (tbl : List (LLabel × Nat)) (l : LLabel) : Nat :=
  (tbl.find? (fun p => p.1 == l)).elim 0 (·.2)

def relaxPass (frame spillW : Nat) (tbl : List (LLabel × Nat)) (body : Lcmd) :
    List (LLabel × Nat) :=
  (body.foldl (fun (acc : (Nat × List (LLabel × Nat))) instr =>
      let (off, out) := acc
      match instr.li_i with
      | .Llabel _ l => (off, out ++ [(l, off)])
      | i =>
          -- length of `i` under the displacements the CURRENT table induces; the
          -- displacement is target − (off + thisLen), but the length under the short/
          -- long choice only flips at the rel8 boundary, so we estimate with the LONG
          -- instrEnd (conservative-stable: the assembler relaxes from long to short).
          let dispOf : LLabel → Int := fun t =>
            Int.ofNat (lookupLabel tbl t) - Int.ofNat (off + instrLenAt frame spillW (fun _ => 0) i)
          (off + instrLenAt frame spillW dispOf i, out)) (0, [])).2

/-- Iterate `relaxPass` to a fixpoint (or until `fuel` runs out). Each pass can only
    keep or shorten branch lengths (a branch that fit rel8 stays short), so the
    offsets are monotone and converge; `fuel = body.length + 1` is more than enough. -/
def relaxFix (frame spillW : Nat) : Nat → List (LLabel × Nat) → Lcmd → List (LLabel × Nat)
  | 0, tbl, _ => tbl
  | fuel + 1, tbl, body =>
      let tbl' := relaxPass frame spillW tbl body
      if tbl' == tbl then tbl else relaxFix frame spillW fuel tbl' body

/-- The label → byte-offset table after relaxation: start from the all-long-form
    layout (`relaxPass []` seeds every label, then iterate). -/
def labelOffsets (frame spillW : Nat) (body : Lcmd) : List (LLabel × Nat) :=
  relaxFix frame spillW (body.length + 1) (relaxPass frame spillW [] body) body

/-- **Encode the whole body**, backpatching each branch to its resolved displacement
    under the relaxed layout. For each instruction, `instrEnd = off + instrLenAt …`,
    and `dispOf l = lookupLabel tbl l − instrEnd` (target relative to the end of THIS
    instruction's encoding, per x86). Concatenates the per-instruction bytes. -/
def encodeLcmd (body : Lcmd) : List (BitVec 8) :=
  -- The frame size + body-uniform spill width are computed from the body EXACTLY as
  -- `LprogAsmPrinter.renderLfundef` does (`frameSize`, `bodyIsU64`), so a spill `k.N`
  -- byte-resolves to the same `off(%rsp)` the text path renders.
  let frame := frameSize body
  let spillW := if bodyIsU64 body then 64 else 32
  let tbl := labelOffsets frame spillW body
  (body.foldl (fun (acc : (Nat × List (BitVec 8))) instr =>
      let (off, bytes) := acc
      let i := instr.li_i
      -- displacement is computed against THIS instruction's end; for a branch the
      -- length under the relaxed table is stable, so use it directly.
      let dispLong : LLabel → Int := fun l =>
        Int.ofNat (lookupLabel tbl l) - Int.ofNat (off + instrLenAt frame spillW (fun _ => 0) i)
      let len := instrLenAt frame spillW dispLong i
      let instrEnd := off + len
      let dispOf : LLabel → Int := fun l => Int.ofNat (lookupLabel tbl l) - Int.ofNat instrEnd
      (instrEnd, bytes ++ encodeLinstrR frame spillW dispOf i)) (0, [])).2

/-! ## 5b. Cross-function calls: intra-object direct resolution + external relocations
   (task #658-continuation)

`encodeLcmd` resolves only *intra-function* labels (`Lgoto/Lcond/Lcall ("", l)` whose
target is in THIS body's label table). A **remote** `Lgoto/Lcall (f, l)` with `f ≠ ""`
targets another function `f`; its rel32 cannot be resolved from this body alone:

* **intra-object** — `f` is another function IN THE SAME `Lprog`/object: once the
  multi-leaf layout fixes every function's `.text` base, the rel32 is
  `targetBase − callSiteEnd`, resolved DIRECTLY at encode time. No relocation needed
  (this is the preferred, minimal-metadata path).
* **truly-external** — `f` is NOT in the object (a libc / C-harness symbol): the
  target address is unknown until link time. Emit a `0`-placeholder rel32 and record a
  `.rela.text` relocation (`R_X86_64_PLT32`, addend `-4`) against the UNDEF symbol `f`,
  which the linker patches.

`symBase : String → Option Int` gives the `.text` byte offset of a same-object symbol
`f`'s entry RELATIVE TO THE START OF THIS FUNCTION'S BODY bytes (so a forward callee is
positive, a backward callee negative). `none` ⇒ external. We force the rel32 long form
for remote targets (the linker reloc and cross-function distances both need 4-byte
displacements), so the rel32 field always sits at a fixed offset after the opcode
prefix (1 byte for `E8`/`E9`, 2 for `0F 8x`). -/

/-- The remote symbol name of a control-flow instr, or `none` if it is local /
    not a control-transfer (`f = ""` is local, handled by the intra-function path). -/
def remoteSym : LinstrR → Option String
  | .Lgoto (f, _) => if f.isEmpty then none else some f
  | .Lcall _ (f, _) => if f.isEmpty then none else some f
  | _ => none

/-- The byte offset of the rel32 displacement field WITHIN a remote control-flow
    instr's encoding: 1 (after the `E8`/`E9` opcode) for `call`/`jmp`. (Remote `jcc`
    is not produced by the owned bodies — conditional back-edges are always local.) -/
def remoteRel32FieldOff : LinstrR → Nat
  | .Lgoto _ => 1
  | .Lcall _ _ => 1
  | _ => 0

/-- Encode a remote control-flow instr to its 5-byte rel32 form given the resolved
    signed displacement `d` (intra-object) or `0` (external placeholder). -/
def encodeRemoteCF (d : Int) : LinstrR → List (BitVec 8)
  | .Lgoto _ => encJmp32 d
  | .Lcall _ _ => encCall32 d
  | _ => []

/-- **Encode the body, collecting external relocations.** Like `encodeLcmd`, but a
    remote `Lgoto/Lcall (f, _)` is resolved against `symBase`:
    * `symBase f = some delta` (intra-object) ⇒ rel32 = `delta − instrEnd`, resolved
      directly, NO relocation;
    * `symBase f = none` (external) ⇒ `0`-placeholder rel32 + a relocation
      `(fieldOffset, f)` (`fieldOffset` = the rel32-field byte offset within the body).

    Returns `(bodyBytes, relocs)` where each reloc's offset is RELATIVE TO THE BODY
    START; the caller shifts by the function's prologue length + `.text` base. Local
    control flow and straight-line `Lopn` are encoded exactly as `encodeLcmd`. -/
def encodeLcmdReloc (symBase : String → Option Int) (body : Lcmd) :
    List (BitVec 8) × List (Nat × String) :=
  let frame := frameSize body
  let spillW := if bodyIsU64 body then 64 else 32
  let tbl := labelOffsets frame spillW body
  let res := body.foldl (fun (acc : Nat × List (BitVec 8) × List (Nat × String)) instr =>
      let (off, bytes, relocs) := acc
      let i := instr.li_i
      match remoteSym i with
      | some f =>
          -- remote target: 5-byte rel32 form, field at `off + 1`.
          let fieldOff := off + remoteRel32FieldOff i
          let instrEnd := off + 5
          match symBase f with
          | some delta =>
              -- intra-object: resolve directly, no relocation.
              let d := delta - Int.ofNat instrEnd
              (instrEnd, bytes ++ encodeRemoteCF d i, relocs)
          | none =>
              -- external: placeholder rel32 + relocation against UNDEF symbol `f`.
              (instrEnd, bytes ++ encodeRemoteCF 0 i, relocs ++ [(fieldOff, f)])
      | none =>
          -- local / straight-line: identical to `encodeLcmd`.
          let dispLong : LLabel → Int := fun l =>
            Int.ofNat (lookupLabel tbl l) - Int.ofNat (off + instrLenAt frame spillW (fun _ => 0) i)
          let len := instrLenAt frame spillW dispLong i
          let instrEnd := off + len
          let dispOf : LLabel → Int := fun l => Int.ofNat (lookupLabel tbl l) - Int.ofNat instrEnd
          (instrEnd, bytes ++ encodeLinstrR frame spillW dispOf i, relocs)) (0, [], [])
  (res.2.1, res.2.2)

/-! ## 6. Wrapping a looped function as bytes / an ELF object

`encodeLfundefBytes` wraps the looped body bytes in the trusted leaf-ABI framing
(`pushq` callee-saved / `popq` + `ret`), reusing `LeafBytes.prologueBytes` /
`epilogueBytes`. The callee-saved set is the printer's `calleeSavedToSave` (the
registers the hand-built body clobbers without `qsave`-parking), keeping the bytes
ABI-identical to the `renderLfundef` text path's push/pop framing. -/

/-- `leaq disp(%rsp), %rsp` (the frame open/close idiom `renderLfundef` uses):
    `REX.W` (`0x48`), `LEA` opcode (`0x8D`), then a `%rsp`-base memory operand. Since
    `%rsp` is the base, the ModRM `r/m = 100` is the SIB escape, so a `SIB = 0x24`
    (`%rsp` base, no index) byte always follows. The displacement form matches what
    `gas` selects: **disp8** (`ModRM mod=01 = 0x64`, one signed byte) when the
    displacement fits a signed byte (`-128 ≤ disp ≤ 127`), else **disp32**
    (`ModRM mod=10 = 0xa4`, four LE bytes). Used to allocate the spill/qsave frame on
    entry (`disp = -frame`) and release it before `ret` (`disp = +frame`), so the
    body's `<off>(%rsp)` slots address the lowered frame exactly as the text path
    intends. Small frames (`frame ≤ 127`) hit the 5-byte disp8 form `gas` emits, so
    this is byte-identical to `renderLfundef`'s `leaq` lines for both small and large
    frames. (`disp = 0` would be the disp0 SIB form, but the frame open/close always
    uses a non-zero `±frame` for a non-empty frame; a zero frame emits no `leaq`.) -/
def encLeaRspFrame (disp : Int) : List (BitVec 8) :=
  if -128 ≤ disp ∧ disp ≤ 127 then
    [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8d, BitVec.ofNat 8 0x64, BitVec.ofNat 8 0x24,
     disp8 disp]
  else
    [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x8d, BitVec.ofNat 8 0xa4, BitVec.ofNat 8 0x24]
      ++ disp32LE disp

/-- The looped function's `.text` bytes, **byte-identical to `renderLfundef`**:
    `pushq` the callee-saved regs the body clobbers without `qsave`-parking, open the
    spill/qsave frame with `leaq -F(%rsp), %rsp` (`F = frameSize body`), the
    two-pass-encoded body (whose `<off>(%rsp)` slots address this lowered frame),
    close the frame with `leaq F(%rsp), %rsp`, `popq …`, then `ret`. The frame
    `leaq` is what makes the whole-function `.o` not just text-identical but
    FUNCTIONALLY correct (the spill offsets land in the allocated frame, not the
    caller's). The save list is `LprogAsmPrinter.calleeSavedToSave` (the same set the
    text renderer push/pops); the names are uppercased physical regs, so
    `LeafBytes.encPushReg` (which reads `%rN`) gets the `%`-prefixed form via
    `gpReg64`. -/
def encodeLfundefBytes (body : Lcmd) : List (BitVec 8) :=
  let saves := calleeSavedToSave body
  let frame := frameSize body
  let pushB := saves.flatMap (fun r => LeafBytes.encPushReg (gpReg64 r))
  let popB := saves.reverse.flatMap (fun r => LeafBytes.encPopReg (gpReg64 r))
  pushB ++ encLeaRspFrame (-(Int.ofNat frame)) ++ encodeLcmd body
    ++ encLeaRspFrame (Int.ofNat frame) ++ popB ++ LeafBytes.encRet

/-- A looped function as an `ElfObject.Leaf`. -/
def encodeLfundefLeaf (name : String) (body : Lcmd) : ElfObject.Leaf :=
  { name := name, text := encodeLfundefBytes body }

/-- The complete single-function ELF64 `.o` bytes for a looped owned-RA function:
    the `gas -o foo.o` analogue with `gas` removed, over a body with control flow. -/
def encodeLfundefObject (name : String) (body : Lcmd) : List (BitVec 8) :=
  ElfObject.buildElfObjectMulti [encodeLfundefLeaf name body]

/-- The byte length of the leaf-ABI prologue (`pushq` callee-saves + `leaq -F(%rsp)`)
    that `encodeLfundefBytes` lays down BEFORE the body. A relocation whose offset is
    body-relative is shifted by this much to become function-relative. (`encPushReg`
    is 1 or 2 bytes per reg; `encLeaRspFrame` is 5 bytes for a small frame
    `F ≤ 127` (disp8), else 8 bytes (disp32).) The prologue `leaq` uses `disp = -F`,
    so the length is measured against the SAME displacement `encodeLfundefBytes`
    emits (NOT `0`), keeping the reloc offset shift exact for small frames. -/
def prologueLen (body : Lcmd) : Nat :=
  let saves := calleeSavedToSave body
  let frame := frameSize body
  (saves.flatMap (fun r => LeafBytes.encPushReg (gpReg64 r))).length
    + (encLeaRspFrame (-(Int.ofNat frame))).length

/-! ## 6b. Reloc-aware whole-`Lprog` object (the cross-function-call linker path)

`encodeLprogReloc` encodes a whole owned-RA `Lprog` to ONE multi-symbol ELF object,
resolving cross-function `Lcall/Lgoto` either intra-object (directly, when the callee
is another function in `p.lp_funcs`) or via a `.rela.text` relocation (when the callee
is external — e.g. a libc / C-harness symbol the linker supplies).

Two passes over the functions:
1. **layout** — encode each function (with intra-object calls resolved against a
   running base map) to get its `.text` byte length, accumulating each function's base
   offset within `.text`;
2. **emit** — re-encode with the now-complete base map, collecting any external
   relocations (offset shifted by the function's prologue length + its `.text` base),
   and stitch the leaves + externs + relocs via `buildElfObjectMultiReloc`. -/

/-- The full function bytes under the reloc encoder, given a `symBase` resolver. The
    prologue/epilogue framing is identical to `encodeLfundefBytes`, but the body uses
    `encodeLcmdReloc` (every remote call/jmp is a fixed 5-byte rel32, so the LENGTH is
    independent of `symBase` — guaranteeing the layout and emit passes agree). -/
def encodeLfundefBytesReloc (symBase : String → Option Int) (body : Lcmd) :
    List (BitVec 8) :=
  let saves := calleeSavedToSave body
  let frame := frameSize body
  let pushB := saves.flatMap (fun r => LeafBytes.encPushReg (gpReg64 r))
  let popB := saves.reverse.flatMap (fun r => LeafBytes.encPopReg (gpReg64 r))
  pushB ++ encLeaRspFrame (-(Int.ofNat frame)) ++ (encodeLcmdReloc symBase body).1
    ++ encLeaRspFrame (Int.ofNat frame) ++ popB ++ LeafBytes.encRet

/-- The `.text` base offset of each function within the stitched `.text`, as a
    `name ↦ base` association list. Computed by encoding each body in order under the
    reloc encoder (with NO cross-function resolution — `symBase := fun _ => none`).
    The body byte LENGTH is independent of resolved displacements because every remote
    form is the fixed 5-byte rel32, so this base map matches the emit pass exactly. -/
def funcBases (p : Lprog) : List (String × Nat) :=
  (p.lp_funcs.foldl (fun (acc : Nat × List (String × Nat)) (nf : String × Lfundef) =>
      let (base, out) := acc
      let len := (encodeLfundefBytesReloc (fun _ => none) nf.2.lfd_body).length
      (base + len, out ++ [(nf.1, base)])) (0, [])).2

/-- The list of external symbols referenced by any function's remote calls but NOT
    defined in `p.lp_funcs` (deduplicated, in first-seen order). -/
def externSyms (p : Lprog) : List String :=
  let defined := p.lp_funcs.map Prod.fst
  let all := p.lp_funcs.flatMap (fun nf =>
    nf.2.lfd_body.filterMap (fun i => remoteSym i.li_i))
  all.foldl (fun acc s =>
    if defined.contains s || acc.contains s then acc else acc ++ [s]) []

/-- A whole owned-RA `Lprog` as one multi-symbol ELF object WITH cross-function-call
    linkage. Each export function's looped body is byte-encoded; an intra-object remote
    call is resolved directly against `funcBases`, a truly-external call gets a
    `.rela.text` `R_X86_64_PLT32` relocation against an UNDEF symbol the linker
    resolves. The no-cross-call case is byte-identical to `encodeLprog` modulo the
    (zero-length) `.rela.text` section the relocatable form always carries. -/
def encodeLprogReloc (p : Lprog) : List (BitVec 8) :=
  let bases := funcBases p
  let externs := externSyms p
  -- `symBase` for a function `nf`: the callee `f`'s `.text` base MINUS this function's
  -- `.text` base MINUS this function's prologue length (so the delta is relative to
  -- the start of THIS body's bytes, matching `encodeLcmdReloc`'s convention).
  let lookupBase : String → Option Nat := fun f =>
    (bases.find? (fun p => p.1 == f)).map Prod.snd
  let leavesRelocs := p.lp_funcs.map (fun nf =>
    let myBase := (lookupBase nf.1).getD 0
    let pre := prologueLen nf.2.lfd_body
    let symBase : String → Option Int := fun f =>
      (lookupBase f).map (fun b => Int.ofNat b - Int.ofNat myBase - Int.ofNat pre)
    let rs := (encodeLcmdReloc symBase nf.2.lfd_body).2
    -- the full function bytes (prologue ++ resolved body ++ epilogue); shift each
    -- body-relative reloc offset by `myBase + pre` to make it `.text`-relative.
    let full := encodeLfundefBytesReloc symBase nf.2.lfd_body
    let relocs := rs.map (fun (o, f) =>
      ({ offset := myBase + pre + o, symName := f } : ElfObject.Reloc))
    (({ name := nf.1, text := full } : ElfObject.Leaf), relocs))
  let leaves := leavesRelocs.map Prod.fst
  let relocs := (leavesRelocs.map Prod.snd).flatten
  ElfObject.buildElfObjectMultiReloc leaves externs relocs

/-- A whole owned-RA `Lprog` as one multi-symbol ELF object: each export function's
    looped body byte-encoded and stitched as its own `STT_FUNC` symbol. -/
def encodeLprog (p : Lprog) : List (BitVec 8) :=
  ElfObject.buildElfObjectMulti
    (p.lp_funcs.map (fun (n, f) => encodeLfundefLeaf n f.lfd_body))

/-! ## 7. Length invariants -/

/-- `jmp rel32` is always 5 bytes, independent of the displacement. -/
@[simp] theorem encJmp32_length (d : Int) : (encJmp32 d).length = 5 := by
  simp [encJmp32, disp32LE, imm32LE]

/-- `jcc rel32` is always 6 bytes, independent of the displacement. -/
@[simp] theorem encJcc32_length (cc : String) (d : Int) : (encJcc32 cc d).length = 6 := by
  simp [encJcc32, disp32LE, imm32LE]

/-- `call rel32` is always 5 bytes, independent of the displacement. -/
@[simp] theorem encCall32_length (d : Int) : (encCall32 d).length = 5 := by
  simp [encCall32, disp32LE, imm32LE]

/-- `jmp rel8` is always 2 bytes (opcode + signed byte). -/
@[simp] theorem encJmp8_length (d : Int) : (encJmp8 d).length = 2 := by simp [encJmp8]

/-- `jcc rel8` is always 2 bytes (opcode + signed byte). -/
@[simp] theorem encJcc8_length (cc : String) (d : Int) : (encJcc8 cc d).length = 2 := by
  simp [encJcc8]

/-- `ret` is 1 byte. -/
@[simp] theorem encRetCF_length : encRetCF.length = 1 := by simp [encRetCF]

/-- **The encoding length depends only on the resolved displacements, not on the
    resolver function.** Two resolvers that agree on every label this instruction
    targets give the same encoding length. For a straight-line `Lopn` the resolver is
    ignored entirely; for a branch the length is the short/long choice, which is a
    function of `dispOf l` alone. This is what makes the relaxation fixpoint
    well-defined: the layout depends only on the displacements it induces. -/
theorem instrLen_depends_only_on_disp (frame spillW : Nat) (f g : LLabel → Int) (i : LinstrR)
    (h : ∀ l, f l = g l) :
    (encodeLinstrR frame spillW f i).length = (encodeLinstrR frame spillW g i).length := by
  cases i with
  | Lgoto t => obtain ⟨fn, l⟩ := t; simp only [encodeLinstrR, h l]
  | Lcond c l =>
      cases c with
      | reg cc => simp only [encodeLinstrR, h l]
      | _ => rfl
  | Lcall ra t => obtain ⟨fn, l⟩ := t; simp only [encodeLinstrR, h l]
  | _ => rfl

/-- A straight-line `Lopn`'s encoding length is fully independent of the displacement
    resolver (it never consults it). -/
theorem encodeLinstrR_Lopn_length_const (frame spillW : Nat) (f g : LLabel → Int)
    (dsts : List LOperand) (opn : String) (srcs : List LOperand) :
    (encodeLinstrR frame spillW f (.Lopn dsts opn srcs)).length
      = (encodeLinstrR frame spillW g (.Lopn dsts opn srcs)).length := rfl

/-! ## 7b. Cross-function reloc length invariants (#658-continuation)

A remote `call`/`jmp` is always the fixed 5-byte rel32 form regardless of whether it
resolves intra-object or via a relocation, so a function's `.text` LENGTH (and hence
the multi-leaf layout) is independent of the `symBase` resolver — the property the
two-pass `funcBases`/emit split relies on. -/

/-- `encodeRemoteCF` is always 5 bytes for a `call`/`jmp`, independent of the
    resolved displacement (intra-object `d` or external placeholder `0`). -/
theorem encodeRemoteCF_length_call (d : Int) (ra : Option String) (t : String × LLabel) :
    (encodeRemoteCF d (.Lcall ra t)).length = 5 := by
  simp [encodeRemoteCF, encCall32, disp32LE, imm32LE]

theorem encodeRemoteCF_length_goto (d : Int) (t : String × LLabel) :
    (encodeRemoteCF d (.Lgoto t)).length = 5 := by
  simp [encodeRemoteCF, encJmp32, disp32LE, imm32LE]

/-! ## 7c. ADX/BMI2-class arm invariants (task A-b6)

The `MULX`/`MULXMEM` and two-source `ADCX`/`ADOX` arms delegate verbatim to
`ScalarEncoder.encMulxRR`/`encMulxMem`/`encAdxCarry` (their length lemmas live
there). Here: the invariants of the NEW arms — the three-source Com-front ADX
data form, the `ADCXHI`/`ADOXHI` carry-out materialisation, and the `SETC`
flag-to-GPR pair — plus the gas pins for each new byte sequence and the
kernel-clean dispatch equations (the `LprogJInstrMnemDispatch` lemma style). -/

/-- `bt $imm8, %r64` is always 5 bytes (`REX.W 0F BA /4 ib`; `W=1` is never
    elided). -/
@[simp] theorem encBtImm_length_w1 (d imm : Nat) : (encBtImm 1 d imm).length = 5 := by
  simp [encBtImm, rexOpt]

/-- The `SETcc`+`MOVZBQ` pair is 8 bytes when the `SETcc` needs a REX byte
    (`d ≥ 8`, or the `%spl/%bpl/%sil/%dil` band `4 ≤ d < 8`), else 7. -/
theorem encSetccMovzx_length (op d : Nat) :
    (encSetccMovzx op d).length
      = if bit d 3 = 1 ∨ (4 ≤ d ∧ d < 8) then 8 else 7 := by
  unfold encSetccMovzx
  by_cases h1 : d >>> 3 % 2 = 1 <;> by_cases h2 : 4 ≤ d ∧ d < 8 <;>
    simp [bit, h1, h2]

/-- Off the bare-REX band (`d < 4` or `d ≥ 8`), the generalised pair at the
    `SETC` opcode `0x92` is byte-identical to `ScalarEncoder.encSetcMovzx` —
    the `JInstr .setc` byte image, so the two paths' `setc` materialisations
    coincide. (On `4 ≤ d < 8` this encoder adds the bare `0x40` REX gas emits
    for `%spl/%bpl/%sil/%dil`.) -/
theorem encSetccMovzx_setc_agree (d : Nat) (hd : d < 16) (hband : d < 4 ∨ 8 ≤ d) :
    encSetccMovzx 0x92 d = encSetcMovzx d := by
  interval_cases d <;> first | rfl | omega

/-! ### Gas pins for the new arms (reference: `as` + `objdump -d`)

```
41 0f 92 c0             setc   %r8b        \ encSetccMovzx 0x92 8
4d 0f b6 c0             movzbq %r8b,%r8    /
0f 90 c0                seto   %al         \ encSetccMovzx 0x90 0
48 0f b6 c0             movzbq %al,%rax    /
40 0f 92 c5             setc   %bpl        \ encSetccMovzx 0x92 5
48 0f b6 ed             movzbq %bpl,%rbp   /
48 0f ba e1 00          btq    $0x0,%rcx     encBtImm 1 1 0
49 0f ba e4 00          btq    $0x0,%r12     encBtImm 1 12 0
0f ba e1 00             btl    $0x0,%ecx     encBtImm 0 1 0
4d 89 d3                mov    %r10,%r11   \
49 0f ba e4 00          btq    $0x0,%r12    > the three-source ADCX arm
66 4d 0f 38 f6 d9       adcx   %r9,%r11    /
``` -/

theorem encSetccMovzx_pin_setc_r8 :
    encSetccMovzx 0x92 8
      = [0x41, 0x0f, 0x92, 0xc0, 0x4d, 0x0f, 0xb6, 0xc0].map (BitVec.ofNat 8) := rfl

theorem encSetccMovzx_pin_seto_rax :
    encSetccMovzx 0x90 0
      = [0x0f, 0x90, 0xc0, 0x48, 0x0f, 0xb6, 0xc0].map (BitVec.ofNat 8) := rfl

theorem encSetccMovzx_pin_setc_rbp :
    encSetccMovzx 0x92 5
      = [0x40, 0x0f, 0x92, 0xc5, 0x48, 0x0f, 0xb6, 0xed].map (BitVec.ofNat 8) := rfl

theorem encBtImm_pin_rcx :
    encBtImm 1 1 0 = [0x48, 0x0f, 0xba, 0xe1, 0x00].map (BitVec.ofNat 8) := rfl

theorem encBtImm_pin_r12 :
    encBtImm 1 12 0 = [0x49, 0x0f, 0xba, 0xe4, 0x00].map (BitVec.ofNat 8) := rfl

theorem encBtImm_pin_ecx :
    encBtImm 0 1 0 = [0x0f, 0xba, 0xe1, 0x00].map (BitVec.ofNat 8) := rfl

/-! ### Kernel-clean dispatch equations for the new arms -/

/-- `SETC` (one destination, zero sources) dispatches to the `setb`+`movzbq`
    pair. Every guard is a `decide +kernel` fact on the closed mnemonic. -/
theorem encodeLopn_setc (frame spillW : Nat) (dn : String) :
    encodeLopn frame spillW (.Lopn [.reg dn] "SETC:64" [])
      = encSetccMovzx 0x92 (gpNumU dn) := by
  simp only [encodeLopn,
    show (isCarryOutBinding "SETC:64" || isMulHiBinding "SETC:64") = false from by
      decide +kernel,
    show stripWidthTag "SETC:64" = "SETC" from by decide +kernel,
    show ("SETC" == "MULX") = false from by decide +kernel,
    show ("SETC" == "MULXMEM") = false from by decide +kernel,
    show adxPrefix "SETC" = none from by decide +kernel,
    show ("SETC" == "SETC") = true from by decide +kernel,
    Bool.false_eq_true, if_false, if_true]

/-- `ADCXHI` (the CF carry-out binding) materialises through `setc`+`movzbq`
    (`0x92`), for ANY source list — the sources are the SSA operands of the
    matching data add, not x86 operands. -/
theorem encodeLopn_adcxhi (frame spillW : Nat) (dn : String) (srcs : List LOperand) :
    encodeLopn frame spillW (.Lopn [.reg dn] "ADCXHI:64" srcs)
      = encSetccMovzx 0x92 (gpNumU dn) := by
  simp only [encodeLopn,
    show isCarryOutBinding "ADCXHI:64" = true from by decide +kernel,
    show carryOutSetccOp (stripWidthTag "ADCXHI:64") = 0x92 from by decide +kernel,
    Bool.true_or, reduceIte]

/-- `ADOXHI` (the OF carry-out binding) materialises through `seto`+`movzbq`
    (`0x90`). -/
theorem encodeLopn_adoxhi (frame spillW : Nat) (dn : String) (srcs : List LOperand) :
    encodeLopn frame spillW (.Lopn [.reg dn] "ADOXHI:64" srcs)
      = encSetccMovzx 0x90 (gpNumU dn) := by
  simp only [encodeLopn,
    show isCarryOutBinding "ADOXHI:64" = true from by decide +kernel,
    show carryOutSetccOp (stripWidthTag "ADOXHI:64") = 0x90 from by decide +kernel,
    Bool.true_or, reduceIte]

/-- The `MULXHI` high-word binding still encodes to NO bytes (the fused body's
    two-output `mulx` already wrote the high word) — the carry-out
    materialisation did not disturb the `MULXHI` nil arm. -/
theorem encodeLopn_mulxhi_nil (frame spillW : Nat) (dsts srcs : List LOperand) :
    encodeLopn frame spillW (.Lopn dsts "MULXHI:64" srcs) = [] := by
  simp only [encodeLopn,
    show isCarryOutBinding "MULXHI:64" = false from by decide +kernel,
    show isMulHiBinding "MULXHI:64" = true from by decide +kernel,
    Bool.false_or, Bool.false_eq_true, reduceIte]

/-- The three-source Com-front `ADCX:64 [R11] [R10, R9, R12]` dispatches to the
    full `mov a,d ; bt $0,cin ; adcx s,d` byte sequence — matching `renderLopn`'s
    text lines `movq %r10, %r11 ; btq $0, %r12 ; adcxq %r9, %r11` byte-for-byte
    (the §gas-pin block above). -/
theorem encodeLopn_adcx3_pin (frame spillW : Nat) :
    encodeLopn frame spillW
        (.Lopn [.reg "R11"] "ADCX:64" [.reg "R10", .reg "R9", .reg "R12"])
      = encAluRRw 1 0x89 11 10 ++ encBtImm 1 12 0 ++ encAdxCarry 0x66 11 9 := by
  simp only [encodeLopn,
    show (isCarryOutBinding "ADCX:64" || isMulHiBinding "ADCX:64") = false from by
      decide +kernel,
    show stripWidthTag "ADCX:64" = "ADCX" from by decide +kernel,
    show rexW (mnemWidth "ADCX:64") = 1 from by decide +kernel,
    show ("ADCX" == "MULX") = false from by decide +kernel,
    show ("ADCX" == "MULXMEM") = false from by decide +kernel,
    show adxPrefix "ADCX" = some 0x66 from by decide +kernel,
    Bool.false_eq_true, if_false]
  norm_num [show isSpillOrQsave "R11" = false from by decide +kernel,
    show isSpillOrQsave "R10" = false from by decide +kernel,
    show isSpillOrQsave "R9" = false from by decide +kernel,
    show isSpillOrQsave "R12" = false from by decide +kernel,
    show parseMemName "R11" = none from by decide +kernel,
    show parseMemName "R10" = none from by decide +kernel,
    show parseMemName "R9" = none from by decide +kernel,
    show parseMemName "R12" = none from by decide +kernel,
    show ("R10" == "R11") = false from by decide +kernel,
    show gpNumU "R11" = 11 from by decide +kernel,
    show gpNumU "R10" = 10 from by decide +kernel,
    show gpNumU "R9" = 9 from by decide +kernel,
    show gpNumU "R12" = 12 from by decide +kernel]

/-- The gas byte image of the pinned three-source `ADCX` dispatch: exactly the
    `4D 89 D3 | 49 0F BA E4 00 | 66 4D 0F 38 F6 D9` reference sequence. -/
theorem adcx3_bytes_gas_pin :
    encAluRRw 1 0x89 11 10 ++ encBtImm 1 12 0 ++ encAdxCarry 0x66 11 9
      = [0x4d, 0x89, 0xd3, 0x49, 0x0f, 0xba, 0xe4, 0x00,
         0x66, 0x4d, 0x0f, 0x38, 0xf6, 0xd9].map (BitVec.ofNat 8) := rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

/-! ## 8. Decode round-trip for the control-flow arms (`decode (encode) = id`)

The straight-line `Lopn` arms inherit `SailX86Decoder`'s GP-ALU round-trip (they are
`ScalarEncoder` shape encoders). Here we add the decode discipline for the rel32
control-flow forms: a decoder that recovers the opcode + signed rel32 displacement,
and a round-trip proving the displacement is recovered exactly. `push`/`pop` are the
trusted leaf-ABI scaffold (no ACL2 x86isa GP-stack model), kept gas-pinned. -/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder

/-- The signed 32-bit value a little-endian `cd` field decodes to: the inverse of
    `disp32LE` on the `[-2^31, 2^31)` range. We recover it as the `BitVec 32` then
    `.toInt` (two's complement). -/
def decodeDisp32 (b0 b1 b2 b3 : BitVec 8) : Int :=
  (BitVec.ofNat 32 (b0.toNat + b1.toNat * 0x100 + b2.toNat * 0x10000
    + b3.toNat * 0x1000000)).toInt

/-- A decoded control-flow instruction: the (first) opcode byte and the recovered
    signed rel32 displacement. -/
structure DecCF where
  opcode : Nat
  disp : Int
  deriving DecidableEq, Repr

/-- Decode a `jmp rel32` (`E9 cd`). -/
def decodeJmp32 : List (BitVec 8) → Option DecCF
  | [op, b0, b1, b2, b3] =>
      if op.toNat = 0xe9 then some { opcode := 0xe9, disp := decodeDisp32 b0 b1 b2 b3 }
      else none
  | _ => none

/-- Decode a `jcc rel32` (`0F 8x cd`): the opcode field carries the second byte. -/
def decodeJcc32 : List (BitVec 8) → Option DecCF
  | [esc, op, b0, b1, b2, b3] =>
      if esc.toNat = 0x0f ∧ 0x80 ≤ op.toNat ∧ op.toNat ≤ 0x8f then
        some { opcode := op.toNat, disp := decodeDisp32 b0 b1 b2 b3 }
      else none
  | _ => none

/-- Decode a `call rel32` (`E8 cd`). -/
def decodeCall32 : List (BitVec 8) → Option DecCF
  | [op, b0, b1, b2, b3] =>
      if op.toNat = 0xe8 then some { opcode := 0xe8, disp := decodeDisp32 b0 b1 b2 b3 }
      else none
  | _ => none

/-- The `disp32LE`/`decodeDisp32` round-trip on the signed-32 range: a displacement
    in `[-2^31, 2^31)` is recovered exactly. `disp32LE o = imm32LE (BitVec.ofInt 32 o).toNat`,
    and `decodeDisp32` recomposes the four LE bytes into a `BitVec 32` then `.toInt`,
    which is `o` for `o` in range. -/
theorem decodeDisp32_disp32LE (o : Int) (hlo : -(2^31) ≤ o) (hhi : o < 2^31) :
    (fun bs => match bs with
      | [b0, b1, b2, b3] => decodeDisp32 b0 b1 b2 b3
      | _ => 0) (disp32LE o) = o := by
  have hv : ((BitVec.ofInt 32 o).toNat) < 2 ^ 32 := (BitVec.ofInt 32 o).isLt
  simp only [disp32LE, imm32LE, decodeDisp32, List.map_cons, List.map_nil]
  have hrecomp := imm32LE_recompose (BitVec.ofInt 32 o).toNat hv
  -- rebuild the BitVec 32 from its toNat, then .toInt = o
  have hbv : (BitVec.ofNat 32 ((BitVec.ofNat 8 ((BitVec.ofInt 32 o).toNat &&& 0xff)).toNat
      + (BitVec.ofNat 8 (((BitVec.ofInt 32 o).toNat >>> 8) &&& 0xff)).toNat * 0x100
      + (BitVec.ofNat 8 (((BitVec.ofInt 32 o).toNat >>> 16) &&& 0xff)).toNat * 0x10000
      + (BitVec.ofNat 8 (((BitVec.ofInt 32 o).toNat >>> 24) &&& 0xff)).toNat * 0x1000000))
      = BitVec.ofInt 32 o := by
    rw [hrecomp, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hbv]
  exact BitVec.toInt_ofInt_eq_self (by norm_num) hlo hhi

/-- **Round-trip for `jmp rel32`** (`encJmp32`): the displacement is recovered
    exactly for any in-range signed-32 displacement. -/
theorem roundtrip_jmp32 (o : Int) (hlo : -(2^31) ≤ o) (hhi : o < 2^31) :
    decodeJmp32 (encJmp32 o) = some { opcode := 0xe9, disp := o } := by
  have hd := decodeDisp32_disp32LE o hlo hhi
  simp only [encJmp32, disp32LE, imm32LE, decodeJmp32, List.map_cons, List.map_nil] at *
  rw [if_pos (by simp [BitVec.toNat_ofNat])]
  simp only [decodeDisp32] at hd ⊢
  rw [hd]

/-- **Round-trip for `call rel32`** (`encCall32`): displacement recovered exactly. -/
theorem roundtrip_call32 (o : Int) (hlo : -(2^31) ≤ o) (hhi : o < 2^31) :
    decodeCall32 (encCall32 o) = some { opcode := 0xe8, disp := o } := by
  have hd := decodeDisp32_disp32LE o hlo hhi
  simp only [encCall32, disp32LE, imm32LE, decodeCall32, List.map_cons, List.map_nil] at *
  rw [if_pos (by simp [BitVec.toNat_ofNat])]
  simp only [decodeDisp32] at hd ⊢
  rw [hd]

/-- **Round-trip for `jcc rel32`** (`encJcc32`): both the condition opcode `0F 8x`
    and the displacement are recovered. The opcode is `jccOpcode cc` (a known
    `0x80..0x8f`), and the displacement is recovered exactly. -/
theorem roundtrip_jcc32 (cc : String) (o : Int)
    (hcc : 0x80 ≤ jccOpcode cc ∧ jccOpcode cc ≤ 0x8f)
    (hlo : -(2^31) ≤ o) (hhi : o < 2^31) :
    decodeJcc32 (encJcc32 cc o) = some { opcode := jccOpcode cc, disp := o } := by
  have hd := decodeDisp32_disp32LE o hlo hhi
  simp only [encJcc32, disp32LE, imm32LE, decodeJcc32, List.map_cons, List.map_nil] at *
  have hmod : jccOpcode cc % 2 ^ 8 = jccOpcode cc :=
    Nat.mod_eq_of_lt (by rw [show (2:Nat)^8 = 256 from rfl]; omega)
  rw [if_pos]
  · simp only [decodeDisp32] at hd ⊢
    rw [BitVec.toNat_ofNat, hmod, hd]
  · refine ⟨by simp [BitVec.toNat_ofNat], ?_, ?_⟩
    · rw [BitVec.toNat_ofNat, hmod]; omega
    · rw [BitVec.toNat_ofNat, hmod]; omega

/-- Every `jccOpcode` output is a valid `0F 8x` condition opcode (`0x80..0x8f`),
    so `roundtrip_jcc32` applies to every condition-code name. -/
theorem jccOpcode_range (cc : String) : 0x80 ≤ jccOpcode cc ∧ jccOpcode cc ≤ 0x8f := by
  unfold jccOpcode; split <;> omega

/-! ### Honest trust tally for the control-flow arms

* **decode-round-trip-proved** (gas pin not load-bearing): `jmp rel32`
  (`roundtrip_jmp32`), `jcc rel32` for every condition code (`roundtrip_jcc32` +
  `jccOpcode_range`), `call rel32` (`roundtrip_call32`). The rel32 displacement —
  the part a wrong jump would get wrong — is proved recovered exactly.
* **straight-line `Lopn` arms**: inherit `SailX86Decoder.roundtrip_jinstr_all`
  (GP-ALU reg-reg), `roundtrip_0FRR` (`IMUL`/`CMOVcc`), `roundtrip_AluImm`,
  `roundtrip_MovImm`, and the memory-MOV structural decode — they reduce to the
  `ScalarEncoder` shape encoders verbatim.
* **gas-pinned-only (honest residual)**: `push`/`pop reg` (the `LeafBytes`
  leaf-ABI scaffold — ACL2 x86isa has no GP-stack semantics we transcribe, the
  existing trust tier); `ret` is the single `0xC3` byte (trivially correct, but
  no executed-effect Sail tie here). -/
theorem trust_edge_cf_jmp (o : Int) (hlo : -(2^31) ≤ o) (hhi : o < 2^31) :
    decodeJmp32 (encJmp32 o) = some { opcode := 0xe9, disp := o } :=
  roundtrip_jmp32 o hlo hhi

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
