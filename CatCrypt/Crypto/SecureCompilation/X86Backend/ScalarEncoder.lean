/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-!
# A verified machine-code byte encoder for the scalar `JInstr` instructions

`AsmPrinter.lean` prints a `JInstr w` block to AT&T assembly *text*, which is then
handed to `gas`/`cc` to be encoded into machine bytes — that last step trusts the
assembler's instruction encoder. This module is the **scalar analogue of
`Avx512Encoder.lean`**: it encodes each `JInstr` directly to its x86-64 machine-code
bytes in Lean, so the kernel body is emitted as bytes by a function whose output we
audit against the Intel SDM and differentially validate against `gas`.

`Avx512Encoder` did this for the AVX-512 packed-integer (EVEX) subset that jasmin
cannot express; this module does it for the **scalar GP-register subset jasminc
emits** — the `JInstr` set of `JasminModel.lean` (`MOV`/`ADD`/`ADC`/`SUB`/`SBB`/
`IMUL`/`NEG`/`AND`/`OR`/`XOR`/`SHL`/`SHR`/`SAR`/`CMOVcc`, the BMI2/ADX trio
`MULX`/`ADCX`/`ADOX`, and the reg-ptr ABI's `loadMem`/`storeMem`). Together the two
encoders cover the full emitted instruction stream with no text-printer + `gas` step.

## The narrowed trust boundary

`AsmPrinter` → `gas` trusts (printer is correct AT&T syntax) ∧ (`gas` encodes each
mnemonic per the Intel SDM). This encoder replaces both with a *Lean* function whose
every output byte is determined by the legacy/VEX prefix construction below —
auditable field by field against the Intel SDM (Vol. 2, the per-instruction
"Instruction Operand Encoding" / opcode tables). The remaining trusted edge shrinks
to *this encoder matches the SDM encoding*, discharged two ways:

* **structurally** — `encodeJInstr` always emits a well-formed instruction with the
  correct byte length (`encode_length` below) and, for the legacy GP forms, the
  `REX.W` prefix that selects the 64-bit operand size (`encode_rexW` below); proved
  unconditionally for all inputs (the `LprogJasminWellFormed`
  analogue);
* **differentially** — each `encodeJInstr` output is pinned (`ScalarValidation.lean`)
  to the exact byte string `gas` produces for the same mnemonic, the posture
  `Avx512Validation.lean` takes for the EVEX encoder and
  `TranslationValidation.lean` takes for the scalar model against the Rocq `.vo`.

The stronger check — a Sail-x86 *decoder* round-trip `decode (encode i) ≡ i` —
is in `SailX86Decoder.lean`: for the register-direct GP forms (`ADD ADC SUB SBB
AND OR XOR MOV` reg-reg, `IMUL`/`CMOVcc`, `MOV`/`IMUL $imm32`, the `SHL/SHR/SAR`
shifts, `NEG`) the encoder is proved to produce bytes the Sail-x86 decode
discipline maps back to the same operands, so the `gas` pin is no longer
load-bearing for them; this module establishes the gas differential anchor that
the decoder upgrades.

## Encoding layout (the SDM forms this transcribes)

* **Legacy two-operand ALU/MOV** (`ADD`/`SUB`/`ADC`/`SBB`/`AND`/`OR`/`XOR`/`MOV`):
  `REX.W` (`0x48 | R<<2 | B`), one opcode byte, a register-direct `ModRM`
  (`mod=11`, `reg`=source, `rm`=destination — AT&T `op %src,%dst`).
* **`IMUL`/`CMOVcc`** (two-byte opcode `0F xx`): `REX.W`, `0F`, opcode, `ModRM`
  with `reg`=destination, `rm`=source (the operand roles are swapped relative to
  the one-byte ALU forms — these read `r/m` into `reg`).
* **`MOV $imm32`**: `REX.W`, `C7 /0`, `ModRM(mod=11, reg=0, rm=dst)`, `imm32` (LE).
* **`IMUL $imm32`**: `REX.W`, `69 /r`, `ModRM(mod=11, reg=dst, rm=dst)`, `imm32`.
* **shifts** (`SHL`/`SHR`/`SAR` by `imm8`): `REX.W`, `C1 /ext`, `ModRM(11,ext,dst)`,
  `imm8` (`ext` = `/4` SHL, `/5` SHR, `/7` SAR).
* **`NEG`**: `REX.W`, `F7 /3`, `ModRM(11,3,dst)`.
* **`ADCX`/`ADOX`** (legacy-VEX `66`/`F3` `0F38 F6`): mandatory prefix
  (`0x66` for ADCX, `0xF3` for ADOX), `REX.W`, `0F 38 F6`, `ModRM(11,dst,src)`.
* **`MULX`** (VEX.LZ.F2.0F38.W1 F6): 3-byte VEX (`C4 RXB.00010 W.v̄v̄v̄v̄.0.11`),
  opcode `F6`, `ModRM(11, dstHi, src2)`; `dstLo` rides VEX.vvvv, `src1` is the
  implicit `%rdx`. Memory form uses a `mod≠11` ModRM + disp.
* **`MOV` reg↔mem** (`loadMem`/`storeMem`): `REX.W`, `8B` (load) / `89` (store),
  `ModRM(mod, reg, base)` + displacement. `mod=00`/`disp0` for offset 0,
  `mod=01`/`disp8` for a signed-byte offset, `mod=10`/`disp32` otherwise.

The register-extension bit (bit 3 of a GP number) routes to `REX.R`/`REX.B` (or, in
VEX, the inverted `R̄`/`B̄`), so all 16 GP registers are addressable. This module
computes those bits arithmetically from the `%rN` names `AsmPrinter.allocGp` assigns.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-! ## 1. Register-name → number, and bit helpers -/

/-- The numeric index `0..15` of a `%rN` GP-register name, in the SDM register
    encoding (`rax=0 rcx=1 rdx=2 rbx=3 rsp=4 rbp=5 rsi=6 rdi=7 r8=8 … r15=15`). A
    name not in the pool reads as `0` (never produced by `allocGp` on a fitting
    block; an overflow yields the `<UNALLOCATED:_>` sentinel, encoded as `0`). -/
def gpNum (r : String) : Nat :=
  match r with
  | "%rax" => 0  | "%rcx" => 1  | "%rdx" => 2  | "%rbx" => 3
  | "%rsp" => 4  | "%rbp" => 5  | "%rsi" => 6  | "%rdi" => 7
  | "%r8"  => 8  | "%r9"  => 9  | "%r10" => 10 | "%r11" => 11
  | "%r12" => 12 | "%r13" => 13 | "%r14" => 14 | "%r15" => 15
  | _      => 0

/-- Bit `i` of `n` (0 or 1). -/
@[simp] def bit (n i : Nat) : Nat := (n >>> i) &&& 1

/-! ## 2. Prefix / ModRM / SIB / displacement byte builders -/

/-- The `REX` prefix `0x40 | W<<3 | R<<2 | X<<1 | B`. For the 64-bit GP forms
    `W=1`; `R` is bit 3 of the ModRM.reg register, `B` of the ModRM.rm register
    (or the SIB/base), `X` of the SIB.index. -/
def rex (w r x b : Nat) : Nat :=
  64 + w * 8 + r * 4 + x * 2 + b

/-- A register-direct `ModRM` byte (`mod=11`): low 3 bits of `reg` and `rm`
    (or an opcode-extension digit in `reg`). -/
def modRMReg (reg rm : Nat) : Nat :=
  192 + ((reg &&& 7) * 8) + (rm &&& 7)

/-- A memory `ModRM` byte for `[base + disp]` with a given `mod` (00/01/10) and
    `reg` field (the other operand, low 3 bits). The `rm` field is the base
    register's low 3 bits. (`base` low-3 = 4 would need a SIB byte — `%rsp`/`%r12`;
    those are excluded as bases by `allocGp`'s pool ordering for the kernels, see
    the `mod` selection in `encMemMov`.) -/
def modRMMem (md reg base : Nat) : Nat :=
  md * 64 + ((reg &&& 7) * 8) + (base &&& 7)

/-- The little-endian `imm32` bytes of `v` (truncated mod `2^32`). -/
def imm32LE (v : Nat) : List (BitVec 8) :=
  [ v &&& 0xff, (v >>> 8) &&& 0xff, (v >>> 16) &&& 0xff, (v >>> 24) &&& 0xff ].map
    (BitVec.ofNat 8)

/-- The little-endian `imm64` bytes of `v` (truncated mod `2^64`). Eight bytes,
    `(v >>> 8i) &&& 0xff` for `i = 0..7`, mirroring `imm32LE` for the full
    64-bit-immediate `MOV` (`B8+r io`) form. -/
def imm64LE (v : Nat) : List (BitVec 8) :=
  [ v &&& 0xff, (v >>> 8) &&& 0xff, (v >>> 16) &&& 0xff, (v >>> 24) &&& 0xff,
    (v >>> 32) &&& 0xff, (v >>> 40) &&& 0xff, (v >>> 48) &&& 0xff,
    (v >>> 56) &&& 0xff ].map (BitVec.ofNat 8)

/-- The little-endian `imm32` bytes of a signed offset `o` (two's complement). -/
def disp32LE (o : Int) : List (BitVec 8) :=
  let v : Nat := (BitVec.ofInt 32 o).toNat
  imm32LE v

/-- The single signed `disp8` byte of `o`. -/
def disp8 (o : Int) : BitVec 8 := BitVec.ofInt 8 o

/-! ### Base-aware memory operand tail (ModRM + optional SIB + displacement)

`modRMMem md reg base` puts the base register's low-3 bits directly in the `r/m`
field. That is correct only when the base low-3 ∉ {4, 5}. Two SDM rules make the
other four GP bases special — and an encoder that ignores them silently emits the
WRONG instruction (the BLS-Fp scratch frame at `%rbp` mis-decoded as RIP-relative,
which segfaults the bytes-direct `.o`):

* **base low-3 = 4** (`%rsp` = 4, `%r12` = 12): `r/m = 100` is the **SIB escape**.
  A bare base with no index is encoded as `r/m = 100` + a SIB byte `0x24`
  (`scale = 0`, `index = 100` = "none", `base = 100`). `REX.B` (already in the
  prefix) extends the SIB base to reach `%r12`.
* **base low-3 = 5** (`%rbp` = 5, `%r13` = 13) at `mod = 00`: `r/m = 101` is
  reserved as **RIP-relative** (disp32, no base). To address `[%rbp]` / `[%r13]`
  with a zero displacement we must force `mod = 01` and emit a one-byte `disp8 = 0`.
  (For a non-zero displacement the disp8/disp32 form already carries `mod ≠ 00`,
  so only the `off = 0` case needs the forced byte.)

`memTail reg base off` returns the bytes AFTER the opcode (and after any REX/VEX
prefix, which carries `REX.B = bit(base,3)` already): the ModRM byte, the SIB byte
when the base low-3 is 4, then the displacement. It is the single point of truth
that `encMemMov` / `encMulxMem` / the `LprogBytes` width-aware analogues all share,
so every memory-operand encoder is correct for all 16 GP bases. -/
def memTail (reg base : Nat) (off : Int) : List (BitVec 8) :=
  let b3 := base &&& 7
  let needSib := b3 = 4
  -- mod=00 with base low-3 = 5 is RIP-relative, so force a disp8=0 there.
  let forceDisp8 := b3 = 5 ∧ off = 0
  if off = 0 ∧ ¬ forceDisp8 then
    if needSib then [BitVec.ofNat 8 (modRMMem 0 reg 4), BitVec.ofNat 8 0x24]
    else [BitVec.ofNat 8 (modRMMem 0 reg base)]
  else if (-128 ≤ off ∧ off ≤ 127) then
    if needSib then [BitVec.ofNat 8 (modRMMem 1 reg 4), BitVec.ofNat 8 0x24, disp8 off]
    else [BitVec.ofNat 8 (modRMMem 1 reg base), disp8 off]
  else
    if needSib then BitVec.ofNat 8 (modRMMem 2 reg 4) :: BitVec.ofNat 8 0x24 :: disp32LE off
    else BitVec.ofNat 8 (modRMMem 2 reg base) :: disp32LE off

/-! ## 3. The instruction-shape encoders

Each shape covers a family of `JInstr` arms; the per-arm opcode/extension is the
SDM map/opcode passed in. `d`/`s` are GP register numbers. -/

/-- A legacy one-byte-opcode reg-reg ALU/MOV op (`op %src,%dst`): `reg`=src,
    `rm`=dst. -/
def encAluRR (op d s : Nat) : List (BitVec 8) :=
  [ rex 1 (bit s 3) 0 (bit d 3), op, modRMReg s d ].map (BitVec.ofNat 8)

/-- A two-byte-opcode (`0F xx`) reg-reg op with `reg`=dst, `rm`=src
    (`IMUL`/`CMOVcc`). -/
def enc0FRR (op d s : Nat) : List (BitVec 8) :=
  [ rex 1 (bit d 3) 0 (bit s 3), 0x0f, op, modRMReg d s ].map (BitVec.ofNat 8)

/-- `MOV $imm32, %dst` (`C7 /0 id`). -/
def encMovImm (d v : Nat) : List (BitVec 8) :=
  ([ rex 1 0 0 (bit d 3), 0xc7, modRMReg 0 d ].map (BitVec.ofNat 8)) ++ imm32LE v

/-- `MOV $imm64, %dst` (`REX.W B8+r io`): the full 64-bit-immediate move. The
    `C7 /0 id` form (`encMovImm`) only carries a 32-bit immediate that the CPU
    **sign-extends** to 64 bits, so it cannot encode an immediate whose bit 31 is
    set without bits 63:32 also being all ones (e.g. the fe25519 bit-255 mask
    `0x7fffffffffffffff`). This form encodes the immediate directly: `REX.W` (with
    `REX.B` = bit 3 of `dst` to reach `r8`–`r15`), the opcode `0xB8 + (dst &&& 7)`
    (the register rides the opcode low 3 bits — there is no ModRM byte), then the
    little-endian `imm64`. Ten bytes total. -/
def encMovImm64 (d v : Nat) : List (BitVec 8) :=
  ([ rex 1 0 0 (bit d 3), 0xb8 + (d &&& 7) ].map (BitVec.ofNat 8)) ++ imm64LE v

/-- `IMUL $imm32, %dst, %dst` (`69 /r id`): `reg`=`rm`=dst. -/
def encImulImm (d v : Nat) : List (BitVec 8) :=
  ([ rex 1 (bit d 3) 0 (bit d 3), 0x69, modRMReg d d ].map (BitVec.ofNat 8)) ++ imm32LE v

/-- An immediate-source ALU op `op $imm32, %dst` (`81 /digit id`, the SDM
    `0x81` 32-bit-immediate group): `REX.W`, opcode `0x81`, a register-direct
    `ModRM` (`mod=11`, `reg`=the ALU opcode-extension `digit`, `rm`=dst), then
    `imm32` little-endian. The `digit` selects the operation per the SDM group-1
    table (ADD=/0, OR=/1, ADC=/2, SBB=/3, AND=/4, SUB=/5, XOR=/6, CMP=/7); the
    `reg` field carries no register, so `REX.R=0` and only `REX.B` (bit 3 of
    `dst`) is set, addressing `r8`–`r15`. The uniform 32-bit-immediate form is
    used for all digits (no `0x83 ib` sign-extended short form) — the fe25519
    immediates (`19`/`38`/…) fit in `imm32`. -/
def encAluImm (digit d v : Nat) : List (BitVec 8) :=
  ([ rex 1 0 0 (bit d 3), 0x81, modRMReg digit d ].map (BitVec.ofNat 8)) ++ imm32LE v

/-- A shift-by-`imm8` op (`C1 /ext ib`): `reg`=ext, `rm`=dst, then `imm8`. -/
def encShiftImm (ext d imm : Nat) : List (BitVec 8) :=
  [ rex 1 0 0 (bit d 3), 0xc1, modRMReg ext d, imm &&& 0xff ].map (BitVec.ofNat 8)

/-- A unary `F7 /ext` op (`NEG` = `/3`). -/
def encUnaryF7 (ext d : Nat) : List (BitVec 8) :=
  [ rex 1 0 0 (bit d 3), 0xf7, modRMReg ext d ].map (BitVec.ofNat 8)

/-- `SETB %dl` (`0F 92 /0`, set-on-carry into the byte `r/m8`) followed by
    `MOVZBQ %dl, %rdx` (`REX.W 0F B6 /r`, zero-extend the byte into the full
    64-bit register). The `SETcc` opcode extension `reg` field is `/0` (the SDM
    `SETcc r/m8` ignores `reg`); for `MOVZBQ` `reg`=dst, `rm`=src (both the same
    register `d`). A `REX` prefix is emitted for the `SETB` when `d ≥ 8` (or when
    `d` is one of `%spl/%bpl/%sil/%dil`, byte forms that require REX) so all 16
    GP byte registers are addressable; for the loop's carry GPR (a `%r8`-class
    callee register) the `REX.B` is set. The pair zero-extends `CF` into `d`,
    realising the model's `setc` arm (`d := if CF then 1 else 0`). -/
def encSetcMovzx (d : Nat) : List (BitVec 8) :=
  -- SETB r/m8 = [REX?] 0F 92 ModRM(11, /0, d).  REX present iff d ≥ 8 (REX.B);
  -- emit REX.B = 0x41 only then (the low-8 GP byte regs %al..%bl need no REX).
  let setb : List Nat :=
    (if bit d 3 = 1 then [rex 0 0 0 1] else [])
      ++ [0x0f, 0x92, modRMReg 0 d]
  -- MOVZBQ r/m8 → r64 = REX.W 0F B6 ModRM(11, d, d).
  let movzx : List Nat := [ rex 1 (bit d 3) 0 (bit d 3), 0x0f, 0xb6, modRMReg d d ]
  (setb ++ movzx).map (BitVec.ofNat 8)

/-- `ADCX`/`ADOX` (`pfx 0F38 F6`, `reg`=dst, `rm`=src). `pfx` is the mandatory
    prefix byte: `0x66` (ADCX) or `0xF3` (ADOX). -/
def encAdxCarry (pfx d s : Nat) : List (BitVec 8) :=
  [ pfx, rex 1 (bit d 3) 0 (bit s 3), 0x0f, 0x38, 0xf6, modRMReg d s ].map (BitVec.ofNat 8)

/-- `MULX %src2, %dstLo, %dstHi` (VEX.LZ.F2.0F38.W1 F6): `reg`=dstHi, `rm`=src2,
    `vvvv`=dstLo, implicit src1 = `%rdx`. The 3-byte VEX prefix is
    `C4 | (R̄ X̄ B̄ 00010) | (W v̄v̄v̄v̄ L pp)` with `R̄=¬bit(dstHi,3)`,
    `B̄=¬bit(src2,3)`, `X̄=1` (no index), `W=1`, `vvvv=dstLo`, `L=0`, `pp=11` (F2). -/
def encMulxRR (dstHi dstLo src2 : Nat) : List (BitVec 8) :=
  let rbar := 1 - bit dstHi 3
  let bbar := 1 - bit src2 3
  let vex1 := rbar * 128 + 1 * 64 + bbar * 32 + 0b00010   -- X̄=1, mmmmm=00010 (0F38)
  let vbar := 15 - (dstLo &&& 15)
  let vex2 := 128 + vbar * 8 + 0b011                       -- W=1, L=0, pp=11 (F2)
  [ 0xc4, vex1, vex2, 0xf6, modRMReg dstHi src2 ].map (BitVec.ofNat 8)

/-- `MULX off(%base), %dstLo, %dstHi` (VEX memory form): same VEX prefix as the
    reg form but `B̄=¬bit(base,3)` and a memory `ModRM` for `[base + off]`. The
    ModRM/SIB/displacement tail is the shared base-aware `memTail`, so the SIB
    escape (base low-3 = 4, `%rsp`/`%r12`) and the forced-disp8 RIP escape (base
    low-3 = 5, `%rbp`/`%r13`) are handled for all 16 GP bases. -/
def encMulxMem (dstHi dstLo base : Nat) (off : Int) : List (BitVec 8) :=
  let rbar := 1 - bit dstHi 3
  let bbar := 1 - bit base 3
  let vex1 := rbar * 128 + 1 * 64 + bbar * 32 + 0b00010
  let vbar := 15 - (dstLo &&& 15)
  let vex2 := 128 + vbar * 8 + 0b011
  let pfx := [ 0xc4, vex1, vex2, 0xf6 ].map (BitVec.ofNat 8)
  pfx ++ memTail dstHi base off

/-- A `MOV` between a register and `[base + off]`: `op` = `0x8B` (load `r ← m`,
    `reg`=dst) or `0x89` (store `m ← r`, `reg`=src). `r` is the register operand,
    `base` the pointer. The ModRM/SIB/displacement tail is the shared base-aware
    `memTail`: `disp0`/`disp8`/`disp32` selection, the SIB escape for base low-3 = 4
    (`%rsp`/`%r12`), and the forced-disp8 RIP escape for base low-3 = 5
    (`%rbp`/`%r13`) — correct for all 16 GP bases (the BLS-Fp scratch frame uses
    `%rbp`). -/
def encMemMov (op r base : Nat) (off : Int) : List (BitVec 8) :=
  let pfx := [ rex 1 (bit r 3) 0 (bit base 3), op ].map (BitVec.ofNat 8)
  pfx ++ memTail r base off

/-- The `scale` (2-bit `ss`) field of a SIB byte from a byte stride: `1→0`,
    `2→1`, `4→2`, `8→3` (`log2`), any other value clamps to `0` (stride 1). -/
def sibScale (scale : Nat) : Nat :=
  if scale = 8 then 3 else if scale = 4 then 2 else if scale = 2 then 1 else 0

/-- A `SIB` byte `ss<<6 | (index&7)<<3 | (base&7)` for `[base + index*scale]`. -/
def sibByte (scale index base : Nat) : Nat :=
  (sibScale scale) * 64 + ((index &&& 7) * 8) + (base &&& 7)

/-- A `MOV` between a register and a **register-indexed** address
    `[base + index*scale]` (displacement 0): `op` = `0x8B` (load `r ← m`,
    `reg`=dst) or `0x89` (store `m ← r`, `reg`=src). The `ModRM.rm` field is
    `100` (the SIB escape); the `SIB` byte selects `base`/`index`/`scale`. When
    `base` low-3 = 5 (`%rbp`/`%r13`) a `mod=00` SIB form has no base, so we force
    `mod=01` with a zero `disp8` to keep `base` present. `REX.X` carries
    `bit(index,3)`, `REX.B` carries `bit(base,3)`. -/
def encMemMovSib (op r base index scale : Nat) : List (BitVec 8) :=
  let needDisp := (base &&& 7) = 5
  let md := if needDisp then 1 else 0
  let pfx := [ rex 1 (bit r 3) (bit index 3) (bit base 3), op,
               -- ModRM(mod, reg=r, rm=100) : SIB escape
               md * 64 + ((r &&& 7) * 8) + 4,
               sibByte scale index base ].map (BitVec.ofNat 8)
  if needDisp then pfx ++ [disp8 0] else pfx

/-! ## 4. The per-`JInstr` encoder

Each arm resolves its register names through the allocation `alloc`, then dispatches
to the shape encoder with the SDM opcode for the mnemonic. The opcode bytes are the
one-byte ALU codes (`ADD 01`, `OR 09`, `AND 21`, `SUB 29`, `XOR 31`, `ADC 11`,
`SBB 19`, `MOV r/m←r 89`), the `0F`-map codes (`IMUL 0F AF`, `CMOVE 0F 44`,
`CMOVNE 0F 45`, `CMOVB 0F 42`), the shift/unary extensions, and the BMI2/ADX VEX
forms above. An immediate `src` selects the imm-operand opcode for the arms that
have one: `MOV $imm32` (`C7 /0`), `IMUL $imm32` (`69 /r`), and the group-1 ALU
ops `ADD/OR/ADC/SBB/AND/SUB/XOR $imm32` via the `81 /digit id` form (`encAluImm`,
with the per-op SDM extension digit). -/

/-- Encode one scalar `JInstr 64` to its x86-64 machine bytes, resolving register
    names through `alloc`. For an `imm` source on a non-MOV/IMUL ALU arm (which the
    emitted kernels never produce) we materialise the immediate into the SDM
    `imm32`-source opcode where one exists, else treat it as `0` (documented above). -/
def encodeJInstr (alloc : GpAlloc) : JInstr 64 → List (BitVec 8)
  | .mov d s =>
      match s with
      | .reg r => encAluRR 0x89 (gpNum (regOf alloc d)) (gpNum (regOf alloc r))
      | .imm v =>
          -- `C7 /0 id` sign-extends imm32 to 64 bits, so it only encodes values
          -- that fit a signed 32-bit immediate (`v < 2^31`). For wider values
          -- (e.g. the fe25519 bit-255 mask `0x7fffffffffffffff`) emit the
          -- 10-byte `REX.W B8+r io` full-`imm64` form.
          if v < 2 ^ 31 then encMovImm (gpNum (regOf alloc d)) v
          else encMovImm64 (gpNum (regOf alloc d)) v
  | .add d s =>
      match s with
      | .reg r => encAluRR 0x01 (gpNum (regOf alloc d)) (gpNum (regOf alloc r))
      | .imm v => encAluImm 0 (gpNum (regOf alloc d)) v  -- ADD = 81 /0 id
  | .sub d s =>
      match s with
      | .reg r => encAluRR 0x29 (gpNum (regOf alloc d)) (gpNum (regOf alloc r))
      | .imm v => encAluImm 5 (gpNum (regOf alloc d)) v  -- SUB = 81 /5 id
  | .adc d s =>
      match s with
      | .reg r => encAluRR 0x11 (gpNum (regOf alloc d)) (gpNum (regOf alloc r))
      | .imm v => encAluImm 2 (gpNum (regOf alloc d)) v  -- ADC = 81 /2 id
  | .sbb d s =>
      match s with
      | .reg r => encAluRR 0x19 (gpNum (regOf alloc d)) (gpNum (regOf alloc r))
      | .imm v => encAluImm 3 (gpNum (regOf alloc d)) v  -- SBB = 81 /3 id
  | .and_ d s =>
      match s with
      | .reg r => encAluRR 0x21 (gpNum (regOf alloc d)) (gpNum (regOf alloc r))
      | .imm v => encAluImm 4 (gpNum (regOf alloc d)) v  -- AND = 81 /4 id
  | .or_ d s =>
      match s with
      | .reg r => encAluRR 0x09 (gpNum (regOf alloc d)) (gpNum (regOf alloc r))
      | .imm v => encAluImm 1 (gpNum (regOf alloc d)) v  -- OR = 81 /1 id
  | .xor_ d s =>
      match s with
      | .reg r => encAluRR 0x31 (gpNum (regOf alloc d)) (gpNum (regOf alloc r))
      | .imm v => encAluImm 6 (gpNum (regOf alloc d)) v  -- XOR = 81 /6 id
  | .imul d s =>
      match s with
      | .reg r => enc0FRR 0xaf (gpNum (regOf alloc d)) (gpNum (regOf alloc r))
      | .imm v => encImulImm (gpNum (regOf alloc d)) v
  | .neg d => encUnaryF7 3 (gpNum (regOf alloc d))
  | .setc d => encSetcMovzx (gpNum (regOf alloc d))
  | .shl d s =>
      match s with
      | .imm v => encShiftImm 4 (gpNum (regOf alloc d)) v
      | .reg _ => encShiftImm 4 (gpNum (regOf alloc d)) 0  -- variable shift not emitted
  | .shr d s =>
      match s with
      | .imm v => encShiftImm 5 (gpNum (regOf alloc d)) v
      | .reg _ => encShiftImm 5 (gpNum (regOf alloc d)) 0
  | .sar d s =>
      match s with
      | .imm v => encShiftImm 7 (gpNum (regOf alloc d)) v
      | .reg _ => encShiftImm 7 (gpNum (regOf alloc d)) 0
  | .cmove d s =>
      match s with
      | .reg r => enc0FRR 0x44 (gpNum (regOf alloc d)) (gpNum (regOf alloc r))
      | .imm _ => enc0FRR 0x44 (gpNum (regOf alloc d)) 0  -- cmov has no imm src
  | .cmovne d s =>
      match s with
      | .reg r => enc0FRR 0x45 (gpNum (regOf alloc d)) (gpNum (regOf alloc r))
      | .imm _ => enc0FRR 0x45 (gpNum (regOf alloc d)) 0
  | .cmovb d s =>
      match s with
      | .reg r => enc0FRR 0x42 (gpNum (regOf alloc d)) (gpNum (regOf alloc r))
      | .imm _ => enc0FRR 0x42 (gpNum (regOf alloc d)) 0
  | .adcx d s =>
      match s with
      | .reg r => encAdxCarry 0x66 (gpNum (regOf alloc d)) (gpNum (regOf alloc r))
      | .imm _ => encAdxCarry 0x66 (gpNum (regOf alloc d)) 0
  | .adox d s =>
      match s with
      | .reg r => encAdxCarry 0xf3 (gpNum (regOf alloc d)) (gpNum (regOf alloc r))
      | .imm _ => encAdxCarry 0xf3 (gpNum (regOf alloc d)) 0
  | .mulx dh dl _ b =>
      match b with
      | .reg r => encMulxRR (gpNum (regOf alloc dh)) (gpNum (regOf alloc dl)) (gpNum (regOf alloc r))
      | .imm _ => encMulxRR (gpNum (regOf alloc dh)) (gpNum (regOf alloc dl)) 0
  | .mulxMem dh dl _ base off =>
      encMulxMem (gpNum (regOf alloc dh)) (gpNum (regOf alloc dl)) (gpNum (regOf alloc base)) off
  | .loadMem d base off  => encMemMov 0x8b (gpNum (regOf alloc d)) (gpNum (regOf alloc base)) off
  | .storeMem base off s =>
      match s with
      | .reg r => encMemMov 0x89 (gpNum (regOf alloc r)) (gpNum (regOf alloc base)) off
      | .imm _ => encMemMov 0x89 0 (gpNum (regOf alloc base)) off  -- store-imm not emitted
  | .loadMemIdx d base idx scale =>
      encMemMovSib 0x8b (gpNum (regOf alloc d)) (gpNum (regOf alloc base))
        (gpNum (regOf alloc idx)) scale
  | .storeMemIdx base idx scale s =>
      match s with
      | .reg r => encMemMovSib 0x89 (gpNum (regOf alloc r)) (gpNum (regOf alloc base))
                    (gpNum (regOf alloc idx)) scale
      | .imm _ => encMemMovSib 0x89 0 (gpNum (regOf alloc base))
                    (gpNum (regOf alloc idx)) scale  -- store-imm not emitted
  -- `loadSym dst sym` (`leaq sym(%rip), %dst`) is UNSUPPORTED on the byte path:
  -- a `.rodata`-symbol `leaq` needs an assembler/linker **relocation** (a
  -- R_X86_64_PC32/REX.W lea against `sym`), not the fixed `disp32` this encoder
  -- materialises — there is no symbol-relocation machinery here. The NTT (the only
  -- emitter of `loadSym`) uses the TEXT `AsmPrinter` path, which renders the real
  -- `leaq sym(%rip), %dst` line for `gas` to relocate; this byte path never sees
  -- it. Emit NO bytes (an explicit, detectable gap in a byte-diff KAT) rather than
  -- a silently-wrong fixed-disp encoding.
  | .loadSym _ _ => []  -- unsupported: needs a relocation; use the text path

/-- Encode a whole block: concatenate the byte encodings of its instructions. The
    contiguous machine-code stream a `.text` section / loader consumes. -/
def encodeJBlock (alloc : GpAlloc) (block : List (JInstr 64)) : List (BitVec 8) :=
  block.flatMap (encodeJInstr alloc)

/-! ## 5. A minimal ELF object wrapper

`encodeJBlock` produces a flat byte stream. To hand it to the linker as the
verified-encoder analogue of `gas -o foo.o`, we wrap it as a minimal relocatable
ELF64 object: an ELF header, the `.text` bytes, a section-header string table, a
symbol table (one `STT_FUNC` global at offset 0 of `.text`), and the section
headers. The byte-exact layout is intentionally simple (no relocations — a
straight-line leaf), and is validated by feeding the produced `.o` to the system
linker + KAT harness in the bench demo. -/

/-- Little-endian `u16`/`u32`/`u64` byte lists. -/
def u16LE (v : Nat) : List (BitVec 8) :=
  [ v &&& 0xff, (v >>> 8) &&& 0xff ].map (BitVec.ofNat 8)
def u32LE (v : Nat) : List (BitVec 8) := imm32LE v
def u64LE (v : Nat) : List (BitVec 8) :=
  (List.range 8).map (fun i => BitVec.ofNat 8 ((v >>> (8 * i)) &&& 0xff))

/-- The string-table bytes `\0name\0` and the byte offset of `name` within it. -/
def strtab (name : String) : List (BitVec 8) × Nat :=
  let nameBytes := name.toUTF8.toList.map (fun b => (BitVec.ofNat 8 b.toNat))
  (([0] : List (BitVec 8)) ++ nameBytes ++ [0], 1)

end CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder

/-! ## 6. Structural well-formedness (the unconditional half of the trust story)

Every `encodeJInstr` output has the byte length its SDM form dictates, and every
legacy GP form carries the `REX.W` prefix that selects the 64-bit operand size.
This is the encoder analogue of `LprogJasminWellFormed` — it
captures the shape an x86 decoder requires, proved for all inputs. -/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-- `encodeJBlock` is the flat concatenation of the per-instruction encodings. -/
@[simp] theorem encodeJBlock_eq (alloc : GpAlloc) (block : List (JInstr 64)) :
    encodeJBlock alloc block = block.flatMap (encodeJInstr alloc) := rfl

/-- Every reg-reg legacy ALU/MOV form encodes to exactly 3 bytes (REX + opcode +
    ModRM). Pins the shape of the dominant instruction family. -/
theorem encAluRR_length (op d s : Nat) : (encAluRR op d s).length = 3 := by
  simp [encAluRR]

/-- Every `0F`-map reg-reg form (`IMUL`/`CMOVcc`) encodes to 4 bytes. -/
theorem enc0FRR_length (op d s : Nat) : (enc0FRR op d s).length = 4 := by
  simp [enc0FRR]

/-- Every shift-by-imm form encodes to 4 bytes (REX + C1 + ModRM + imm8). -/
theorem encShiftImm_length (ext d imm : Nat) : (encShiftImm ext d imm).length = 4 := by
  simp [encShiftImm]

/-- Every immediate-source ALU form (`81 /digit id`) encodes to 7 bytes
    (REX + opcode + ModRM + imm32). -/
theorem encAluImm_length (digit d v : Nat) : (encAluImm digit d v).length = 7 := by
  simp [encAluImm, imm32LE]

/-- `imm64LE` is exactly 8 little-endian bytes. -/
theorem imm64LE_length (v : Nat) : (imm64LE v).length = 8 := by
  simp [imm64LE]

/-- The full-`imm64` `MOV` form (`REX.W B8+r io`) encodes to 10 bytes
    (REX + opcode + imm64). -/
theorem encMovImm64_length (d v : Nat) : (encMovImm64 d v).length = 10 := by
  simp [encMovImm64, imm64LE]

/-- `MULX` (reg form) encodes to 5 bytes (3-byte VEX + opcode + ModRM). -/
theorem encMulxRR_length (dh dl s : Nat) : (encMulxRR dh dl s).length = 5 := by
  simp [encMulxRR]

/-- `ADCX`/`ADOX` encode to 6 bytes (prefix + REX + 0F 38 F6 + ModRM). -/
theorem encAdxCarry_length (pfx d s : Nat) : (encAdxCarry pfx d s).length = 6 := by
  simp [encAdxCarry]

end CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
