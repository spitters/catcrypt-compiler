/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

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

* **structurally** — every shape encoder emits exactly the byte length its SDM form
  dictates, proved unconditionally for all inputs by the §6 family (`encAluRR_length`
  3, `enc0FRR_length` 4, `encShiftImm_length` 4, `encAluImm_length` 7,
  `encMovImm64_length` 10, `encMulxRR_length` 5, `encAdxCarry_length` 6) — the
  `LprogJasminWellFormed` analogue. There is **no** aggregate `encodeJInstr`-level
  length lemma (the memory arms' length depends on the displacement form `memTail`
  selects), and **no** `REX.W` lemma: the `REX.W` prefix that selects the 64-bit
  operand size is carried *by construction* — every legacy GP shape encoder below
  literally builds `rex 1 …`, readable off the definition;
* **differentially** — each `encodeJInstr` output is pinned (`ScalarValidation.lean`)
  to the exact byte string `gas` produces for the same mnemonic, the posture
  `Avx512Validation.lean` takes for the EVEX encoder and
  `TranslationValidation.lean` takes for the scalar model against the Rocq `.vo`.

The stronger check — a Sail-x86 *decoder* round-trip `decode (encode i) ≡ i` —
is in `SailX86Decoder.lean`: for the register-direct GP forms (`ADD ADC SUB SBB
AND OR XOR MOV` reg-reg, `IMUL`/`CMOVcc`, `MOV`/`IMUL $imm32`, the `SHL/SHR/SAR`
shifts, `NEG`) the encoder is proved to produce bytes the Sail-x86 decode
discipline maps back to the same operands, so those forms rest on the round-trip
rather than on the `gas` pin; this module establishes the gas differential anchor
the decoder strengthens.

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

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-! ## 1. Register-name → number, and bit helpers -/

/-- The numeric index `0..15` of a `%rN` GP-register name, in the SDM register
    encoding (`rax=0 rcx=1 rdx=2 rbx=3 rsp=4 rbp=5 rsi=6 rdi=7 r8=8 … r15=15`), or
    `none` on any other string. Register-number resolution is total with failure
    here: the two strings that reach the encoder without naming a canonical
    register — `regOf`'s `<UNALLOCATED:n>` sentinel for a name the allocation does
    not cover, and a pinned register spelled outside the sixteen — are both
    `none`, and `encodeJBlock?` refuses to encode a block containing either. -/
def gpNum? (r : String) : Option Nat :=
  match r with
  | "%rax" => some 0  | "%rcx" => some 1  | "%rdx" => some 2  | "%rbx" => some 3
  | "%rsp" => some 4  | "%rbp" => some 5  | "%rsi" => some 6  | "%rdi" => some 7
  | "%r8"  => some 8  | "%r9"  => some 9  | "%r10" => some 10 | "%r11" => some 11
  | "%r12" => some 12 | "%r13" => some 13 | "%r14" => some 14 | "%r15" => some 15
  | _      => none

/-- The numeric index `0..15` of a `%rN` GP-register name, in the SDM register
    encoding (`rax=0 rcx=1 rdx=2 rbx=3 rsp=4 rbp=5 rsi=6 rdi=7 r8=8 … r15=15`),
    with any other string reading as `0`. This is `gpNum?` with its failure case
    defaulted (`gpNum_eq_getD`); the encoder arms read it, and `encodeJBlock?`'s
    gate is what keeps a defaulted value out of the byte stream. -/
def gpNum (r : String) : Nat :=
  match r with
  | "%rax" => 0  | "%rcx" => 1  | "%rdx" => 2  | "%rbx" => 3
  | "%rsp" => 4  | "%rbp" => 5  | "%rsi" => 6  | "%rdi" => 7
  | "%r8"  => 8  | "%r9"  => 9  | "%r10" => 10 | "%r11" => 11
  | "%r12" => 12 | "%r13" => 13 | "%r14" => 14 | "%r15" => 15
  | _      => 0

/-- `gpNum` is `gpNum?` with the unresolvable case defaulted to `0` — the number
    of `%rax`. -/
theorem gpNum_eq_getD (r : String) : gpNum r = (gpNum? r).getD 0 := by
  unfold gpNum gpNum?
  split <;> rfl

/-- The sixteen canonical `%rN` names, the domain on which `gpNum?` is defined. -/
def gpNames : List String :=
  [ "%rax", "%rcx", "%rdx", "%rbx", "%rsp", "%rbp", "%rsi", "%rdi",
    "%r8", "%r9", "%r10", "%r11", "%r12", "%r13", "%r14", "%r15" ]

/-- A string `gpNum?` resolves is one of the sixteen canonical `%rN` names. -/
theorem mem_gpNames_of_gpNum?_isSome (r : String) (h : (gpNum? r).isSome = true) :
    r ∈ gpNames := by
  unfold gpNum? at h
  split at h <;> simp_all [gpNames]

/-- Every canonical `%rN` name is resolved by `gpNum?`. -/
theorem gpNum?_isSome_of_mem_gpNames (r : String) (h : r ∈ gpNames) :
    (gpNum? r).isSome = true := by
  simp only [gpNames, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

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

/-- A one-byte-opcode reg-reg op with `reg`=dst, `rm`=src — the operand order of
    `MOVSXD` (`63 /r`), opposite to `encAluRR`'s.
    Gas-pinned: `movslq %ecx,%rax` = `48 63 C1`. -/
def encAluRRrev (op d s : Nat) : List (BitVec 8) :=
  [ rex 1 (bit d 3) 0 (bit s 3), op, modRMReg d s ].map (BitVec.ofNat 8)

/-- A shift/rotate by exactly one (`D1 /ext`), the form the assembler picks over
    `C1 /ext 01`.  Gas-pinned: `rolq $1,%rcx` = `48 D1 C1`.  Named apart from
    `LprogBytes.encShift1`, which is the same form on the other byte route and
    carries an operand width; a shared name makes both ambiguous in the modules
    that open the two namespaces together. -/
def encShiftByOne (ext d : Nat) : List (BitVec 8) :=
  [ rex 1 0 0 (bit d 3), 0xd1, modRMReg ext d ].map (BitVec.ofNat 8)

/-- A shift by the count in `%cl` (`REX.W D3 /ext`), the only register-count form
    of the group-2 shifts: `shl/shr/sar %cl, %d`. The count is the low byte of
    `%rcx` masked to six bits, the count semantics of the `JState` shift words.
    SDM Vol 2B, `SAL/SAR/SHL/SHR`: `shrq %cl, %rdx` = `48 D3 EA`. -/
def encShiftCl (ext d : Nat) : List (BitVec 8) :=
  [ rex 1 0 0 (bit d 3), 0xd3, modRMReg ext d ].map (BitVec.ofNat 8)

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
    immediates (`19`/`38`/…) fit in `imm32`.

    **PRECONDITION on `v` (unchecked — this is a total function that TRUNCATES).**
    x86-64 has no 64-bit-immediate ALU form: `81 /digit id` carries 32 immediate
    bits which the CPU **sign-extends** to the 64-bit operand. So the encoding is
    faithful exactly on the values whose 64-bit two's-complement image fits a
    signed 32-bit immediate:

    `v < 2^31  ∨  2^64 - 2^31 ≤ v`   (`LprogBytes.fitsImm32S`, `GatherImmForms.fitsImm32S`)

    Outside that set the emitted instruction computes with a DIFFERENT value than
    the model's `.imm v`, and nothing here reports it: `v ∈ [2^31, 2^32)` is
    sign-extended to `v - 2^64 + 2^32` (negative), and `v ≥ 2^32` additionally
    loses its high bits to `imm32LE`'s `mod 2^32` truncation. The `MOV $imm` arm of
    `encodeJInstr` escapes this by falling back to the 10-byte `REX.W B8+r io`
    `movabs` form (`encMovImm64`) — there is no such escape for an ALU op, whose
    only wide-immediate lowering is "materialise into a scratch GPR first", a
    register-allocation decision this encoder cannot make.

    No caller is guarded: every `encodeJInstr` ALU-with-`.imm` arm (`add`/`sub`/
    `adc`/`sbb`/`and_`/`or_`/`xor_`) calls straight through. The in-repo emitters
    only produce small immediates (fe25519 `19`/`38`, mpn strides `1`/`8`, shift
    counts), so the precondition holds in practice but is NOT enforced. No theorem
    in this file constrains `v`: `encAluImm_length` is `v`-independent (always 7
    bytes), and the `ScalarValidation` gas pins are per-value. The decode
    round-trips in `SailX86Decoder` (`roundtrip_AluImm`) recover the `imm32`
    FIELD, not the 64-bit value it denotes, so they carry the same caveat. -/
def encAluImm (digit d v : Nat) : List (BitVec 8) :=
  ([ rex 1 0 0 (bit d 3), 0x81, modRMReg digit d ].map (BitVec.ofNat 8)) ++ imm32LE v

/-- A shift-by-`imm8` op (`C1 /ext ib`): `reg`=ext, `rm`=dst, then `imm8`. -/
def encShiftImm (ext d imm : Nat) : List (BitVec 8) :=
  [ rex 1 0 0 (bit d 3), 0xc1, modRMReg ext d, imm &&& 0xff ].map (BitVec.ofNat 8)

/-- `TEST r/m64, imm32` is `REX.W F7 /0 id` — group 3, NOT the group-1 `81 /ext`
    that `encAluImm` emits, whose `/0` digit is `ADD`.  For `RAX` the assembler
    picks the accumulator short form `REX.W A9 id`, one byte shorter because it
    carries no ModRM; matched here so the bytes agree with the printer's
    rendering assembled by `as` (`testq $0x12345678,%rax` = `48 a9 78 56 34 12`,
    `testq $0x12345678,%r11` = `49 f7 c3 78 56 34 12`). -/
def encTestImm (d v : Nat) : List (BitVec 8) :=
  if d == 0 then
    ([ rex 1 0 0 0, 0xa9 ].map (BitVec.ofNat 8)) ++ imm32LE v
  else
    ([ rex 1 0 0 (bit d 3), 0xf7, modRMReg 0 d ].map (BitVec.ofNat 8)) ++ imm32LE v

/-- A unary `F7 /ext` op (`NEG` = `/3`). -/
def encUnaryF7 (ext d : Nat) : List (BitVec 8) :=
  [ rex 1 0 0 (bit d 3), 0xf7, modRMReg ext d ].map (BitVec.ofNat 8)

/-- `SETB %dl` (`0F 92 /0`, set-on-carry into the byte `r/m8`) followed by
    `MOVZBQ %dl, %rdx` (`REX.W 0F B6 /r`, zero-extend the byte into the full
    64-bit register). The `SETcc` opcode extension `reg` field is `/0` (the SDM
    `SETcc r/m8` ignores `reg`); for `MOVZBQ` `reg`=dst, `rm`=src (both the same
    register `d`). The `SETB` byte destination needs a `REX` prefix in **two**
    disjoint bands, and the encoder emits one in each:

    * `d ≥ 8` (`%r8b`–`%r15b`) — `REX.B` routes bit 3 of the register number, so
      the prefix is `0x41` (gas: `setb %r8b` = `41 0f 92 c0`);
    * `4 ≤ d < 8` (`%spl/%bpl/%sil/%dil`) — WITHOUT a `REX` prefix the ModRM `rm`
      values `100..111` name the legacy high-byte registers `AH/CH/DH/BH`, so a
      **bare** `REX` (`0x40`, all of `W R X B` clear) is required to reinterpret
      them as the low bytes of `%rsp/%rbp/%rsi/%rdi` (gas: `setb %spl` =
      `40 0f 92 c4`). Dropping it writes `AH`-class bits while the `REX.W` `MOVZBQ`
      below reads `SPL` — a silently wrong register pair.

    `d < 4` (`%al/%cl/%dl/%bl`) needs no prefix. The `MOVZBQ` always carries
    `REX.W`, so its byte source is the REX-selected low byte for all 16 GPs. The
    pair zero-extends `CF` into `d`, realising the model's `setc` arm
    (`d := if CF then 1 else 0`), and is byte-identical to the looped path's
    `LprogBytes.encSetccMovzx 0x92` for every `d`
    (`LprogBytes.encSetccMovzx_setc_agree`). -/
def encSetcMovzx (d : Nat) : List (BitVec 8) :=
  -- SETB r/m8 = [REX?] 0F 92 ModRM(11, /0, d).  REX.B = 0x41 for d ≥ 8; the BARE
  -- REX 0x40 for d ∈ {4..7} (%spl/%bpl/%sil/%dil — else the ModRM names AH/CH/DH/BH);
  -- none for d < 4 (the low-8 GP byte regs %al..%bl need no REX).
  let setb : List Nat :=
    (if bit d 3 = 1 then [rex 0 0 0 1] else if 4 ≤ d ∧ d < 8 then [rex 0 0 0 0] else [])
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

/-- `MOV $imm32, off(%base)` (`REX.W C7 /0 id` with a **memory** ModRM): the
    store-immediate form. This is `encMemMov` at opcode `0xC7` with the ModRM `reg`
    field holding the opcode-extension digit `/0` instead of a register (so
    `REX.R = 0`), followed by the little-endian `imm32`. The ModRM/SIB/displacement
    tail is therefore the same shared base-aware `memTail`, correct for all 16 GP
    bases. gas: `movq $0, (%rdi)` = `48 c7 07 00 00 00 00`,
    `movq $2, 24(%rsp)` = `48 c7 44 24 18 02 00 00 00` (the SIB-escape base).

    **PRECONDITION on `v`: `v < 2^31 ∨ 2^64 - 2^31 ≤ v`** — the same
    sign-extended-`imm32` constraint `encAluImm` documents at length (the CPU
    sign-extends the 32-bit field to the 64-bit memory operand, and `imm32LE`
    truncates `mod 2^32`). Unlike the register-destination `MOV`, there is no
    `movabs`-to-memory escape: a wide store-immediate must go through a scratch
    GPR. The one in-repo emitter of a store-immediate is
    `MpnLoopEmit`/`MpnLoopOwnedEmit.zeroLoopBody` (`storeMem "r" 0 (.imm 0)`), well
    inside the range. -/
def encMemMovImm (base : Nat) (off : Int) (v : Nat) : List (BitVec 8) :=
  encMemMov 0xc7 0 base off ++ imm32LE v

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
    `bit(index,3)`, `REX.B` carries `bit(base,3)`.

    **PRECONDITION: `index ≠ 4`** (the index register must not be `%rsp`).
    `SIB.index = 100` with `REX.X = 0` is the SDM's "**no index**" encoding — the
    address degrades to `[base]` and the index register is silently dropped, with
    no diagnostic. `index = 4` is the ONLY bad value: `index = 12` (`%r12`) sets
    `REX.X = 1`, which lifts `100` out of the escape and names `%r12` normally, and
    every other low-3 is a plain index.

    The precondition holds for every caller, because an index register only ever
    arrives here through `gpNum (regOf alloc idx)`:
    * `AsmPrinter.gpPool` — the pool `allocGp` draws from — **excludes `%rsp`**
      (and `%rbp`) by construction, so an allocator-assigned index is never `4`;
    * an *overflowed* name resolves to the `<UNALLOCATED:_>` sentinel, which
      `gpNum` maps to `0` (`%rax`), not `4`;
    * the one emitter that pins a name to `"%rsp"` (`FheNttLoopOwnedEmit`'s
      red-zone spill base `("rsp", "%rsp")`) uses it only as a `loadMem`/`storeMem`
      **base**, never as a `loadMemIdx`/`storeMemIdx` index.

    Nothing enforces this, so a future pinned allocation putting an index name on
    `%rsp` would miscompile silently; the guard is the pool, not a check. -/
def encMemMovSib (op r base index scale : Nat) : List (BitVec 8) :=
  let needDisp := (base &&& 7) = 5
  let md := if needDisp then 1 else 0
  let pfx := [ rex 1 (bit r 3) (bit index 3) (bit base 3), op,
               -- ModRM(mod, reg=r, rm=100) : SIB escape
               md * 64 + ((r &&& 7) * 8) + 4,
               sibByte scale index base ].map (BitVec.ofNat 8)
  if needDisp then pfx ++ [disp8 0] else pfx

/-- A three-byte-VEX register-register form, `W=1` (64-bit), `L=0`.  `mm` is the
    opcode map (`0b00010` = `0F38`, `0b00011` = `0F3A`), `pp` the mandatory-prefix
    field (`00` none, `01` `66`, `10` `F3`, `11` `F2`), `vvvv` the register the
    `~vvvv` field carries, `dst` the `ModRM.reg` operand and `rm` the `ModRM.rm`
    one.  `encMulxRR` is this shape at `mm=0F38, pp=F2, op=F6`.
    Gas-pinned: `andn %rcx,%rbx,%rax` = `C4 E2 E0 F2 C1`,
    `shlx %rbx,%rcx,%rax` = `C4 E2 E1 F7 C1`. -/
def encVex3RR (mm pp op dst vvvv rm : Nat) : List (BitVec 8) :=
  let rbar := 1 - bit dst 3
  let bbar := 1 - bit rm 3
  let vex1 := rbar * 128 + 1 * 64 + bbar * 32 + mm     -- X̄ = 1
  let vbar := 15 - (vvvv &&& 15)
  let vex2 := 128 + vbar * 8 + pp                       -- W = 1, L = 0
  [ 0xc4, vex1, vex2, op, modRMReg dst rm ].map (BitVec.ofNat 8)

/-- The VEX `pp` field of the BMI2 variable shift at group-2 extension `ext`:
    `SHLX` (`/4`) is `VEX.66` (`01`), `SHRX` (`/5`) is `VEX.F2` (`11`), `SARX`
    (`/7`) is `VEX.F3` (`10`). SDM Vol 2B, `SARX/SHLX/SHRX`. -/
def shiftXpp (ext : Nat) : Nat :=
  if ext = 4 then 0b01 else if ext = 7 then 0b10 else 0b11

/-- `SHLX`/`SHRX`/`SARX r64a, r/m64, r64b` (`VEX.LZ.{66,F2,F3}.0F38.W1 F7 /r`):
    `dst := src` shifted by the low six bits of `cnt`, no flag written. The
    destination is `ModRM.reg`, the shifted value `ModRM.rm`, the count the
    `~vvvv` register; `ext` selects the mnemonic as for the group-2 form
    (`SHL = /4`, `SHR = /5`, `SAR = /7`), so a register-count group-2 shift and its
    BMI2 image share one extension argument. Five bytes: `C4`, then
    `R̄ X̄ B̄ 0_0010`, then `W=1 ~vvvv L=0 pp`, then `F7`, then the register-direct
    ModRM. AT&T `shrx %rcx, %rax, %rdx` (count `%rcx`, value `%rax`, destination
    `%rdx`) is `encShiftX 5 2 0 1` = `C4 E2 F3 F7 D0`, pinned in
    `encShiftX_shrx_rcx_rax_rdx`. -/
def encShiftX (ext dst src cnt : Nat) : List (BitVec 8) :=
  encVex3RR 0b00010 (shiftXpp ext) 0xf7 dst cnt src

/-- The bytes of a register-count shift `sh d, c` at group-2 extension `ext`:
    the `%cl` form `encShiftCl` (`REX.W D3 /ext`, which writes the flags
    `x86_SHL`/`x86_SHR`/`x86_SAR` write) when the count register `c` is allocated
    to `%rcx`, and no bytes otherwise: the group-2 shift reads its count from
    `%cl` only, and the BMI2 `encShiftX` writes no flag where `evalInstr` writes
    them. The flag-free register-count shift at the `JInstr` level is
    `.shlx`/`.shrx`/`.sarx`. -/
def encShiftRegCount (alloc : GpAlloc) (ext : Nat) (d c : String) : List (BitVec 8) :=
  if regOf alloc c = "%rcx" then encShiftCl ext (gpNum (regOf alloc d)) else []

/-- `RORX $imm8, %rm, %dst` — the VEX form above with no `vvvv` operand and a
    trailing `imm8`.  Gas-pinned: `rorx $7,%rcx,%rax` = `C4 E3 FB F0 C1 07`. -/
def encRorx (dst rm imm : Nat) : List (BitVec 8) :=
  encVex3RR 0b00011 0b11 0xf0 dst 0 rm ++ [BitVec.ofNat 8 (imm &&& 0xff)]

/-- `LEA off(%base,%index,scale), %dst` — the address itself, no memory access.
    `8D /r` with the SIB escape; a nonzero displacement (or a `%rbp`/`%r13` base,
    which has no `mod=00` form) forces a `disp8`/`disp32`.
    Gas-pinned: `leaq 24(%rbx,%rcx,8),%rax` = `48 8D 44 CB 18`,
    `leaq (%rbx,%rcx,1),%rax` = `48 8D 04 0B`. -/
def encLeaSib (dst base index scale : Nat) (off : Int) : List (BitVec 8) :=
  let needDisp := off ≠ 0 || (base &&& 7) = 5
  let short := -128 ≤ off && off ≤ 127
  let md := if !needDisp then 0 else if short then 1 else 2
  let pfx := [ rex 1 (bit dst 3) (bit index 3) (bit base 3), 0x8d,
               md * 64 + ((dst &&& 7) * 8) + 4,
               sibByte scale index base ].map (BitVec.ofNat 8)
  if !needDisp then pfx
  else if short then pfx ++ [disp8 off]
  else pfx ++ disp32LE off

/-- `MOV $imm32, (%base, %index, scale)` (`REX.W C7 /0 id` with a **SIB** ModRM):
    the register-indexed store-immediate. `encMemMovSib` at opcode `0xC7` with the
    ModRM `reg` field holding the extension digit `/0` (so `REX.R = 0`), then the
    little-endian `imm32`; the `mod=01`/`disp8=0` forcing for a `%rbp`/`%r13` base
    is inherited, and the `imm32` follows the displacement. gas:
    `movq $0, (%rdi,%rsi,8)` = `48 c7 04 f7 00 00 00 00`.

    Carries BOTH preconditions of the forms it composes: `index ≠ 4`
    (`encMemMovSib`) and `v < 2^31 ∨ 2^64 - 2^31 ≤ v` (`encMemMovImm`). -/
def encMemMovSibImm (base index scale v : Nat) : List (BitVec 8) :=
  encMemMovSib 0xc7 0 base index scale ++ imm32LE v

/-! ## 4. The per-`JInstr` encoder

Each arm resolves its register names through the allocation `alloc`, then dispatches
to the shape encoder with the SDM opcode for the mnemonic. The opcode bytes are the
one-byte ALU codes (`ADD 01`, `OR 09`, `AND 21`, `SUB 29`, `XOR 31`, `ADC 11`,
`SBB 19`, `MOV r/m←r 89`), the `0F`-map codes (`IMUL 0F AF`, `CMOVE 0F 44`,
`CMOVNE 0F 45`, `CMOVB 0F 42`), the shift/unary extensions, and the BMI2/ADX VEX
forms above. An immediate `src` selects the imm-operand opcode for the arms that
have one: `MOV $imm32` (`C7 /0`), `IMUL $imm32` (`69 /r`), the group-1 ALU
ops `ADD/OR/ADC/SBB/AND/SUB/XOR $imm32` via the `81 /digit id` form (`encAluImm`,
with the per-op SDM extension digit), and the two store-immediate forms
`MOV $imm32, mem` (`C7 /0` with a memory / SIB ModRM — `encMemMovImm`,
`encMemMovSibImm`). -/

/-- Encode one scalar `JInstr 64` to its x86-64 machine bytes, resolving register
    names through `alloc`.

    **Immediate sources.** Where the SDM has an imm-operand form the arm uses it:
    `MOV $imm32` (`C7 /0`) with the `movabs` fallback, `IMUL $imm32` (`69 /r`), the
    group-1 ALU `81 /digit id` (`encAluImm` — read its precondition), and the two
    store-immediate forms `C7 /0` to memory (`encMemMovImm`/`encMemMovSibImm`).

    **The four `.imm`-source arms x86 has NO encoding for.** `CMOVcc`, `ADCX`,
    `ADOX` and `MULX` take no immediate operand at all, so their `.imm` arms cannot
    be encoded faithfully; they fall back to register `0` (`%rax`) as the source.
    The `AsmPrinter` TEXT path does not agree: it renders `cmoveq $v, %d` /
    `adcx $v, %d` / `mulx $v, …`, which `gas` **rejects** (no such operand form), so
    the text path fails loudly where the byte path silently emits a well-formed but
    different instruction.

    **The register-count `SHL`/`SHR`/`SAR` arms.** x86's group-2 variable shift
    reads its count from `%cl` only. A count register allocated to `%rcx` encodes
    as `REX.W D3 /ext` (`encShiftCl`); any other count register carries no bytes
    (`encShiftRegCount`), and `encodableJInstr` is `false` on the shape, so
    `encodeJInstr?` refuses it. `evalInstr` runs `.shr d (.reg c)` as `x86_SHR`,
    which writes `CF`/`SF`/`ZF`/`PF`; the BMI2 `shrx` (`encShiftX`) computes the
    same data word (`x86_SHR_word_eq_SHRX` and its duals: both mask the count to
    six bits) but writes no flag, so it is not a byte image of this `JInstr`.
    The flag-free register-count shift at the `JInstr` level is `.shlx`/`.shrx`/
    `.sarx`, which `LoweringExtended.lowerAluJ2` emits for the gather's
    two-source `regArith .shl`/`.shr`/`.sar` export over two register sources
    (`LoweringExtended.lowerShiftRegJ`), so a variable shift such as the P-256
    ladder's per-trip bit load reaches this encoder as `encShiftX`. The `Lopn`
    route (`LprogBytes.encodeLopn`), whose two-source shift semantics is
    value-only, encodes the same export as `encShiftX`. The `.shl`/`.shr`/`.sar`
    register-count shape itself is reached only by a hand-built `JInstr` block.

    The `.imm` divergence is unreachable from the compiler: no lowering constructs
    those shapes. `LoweringExtended.lowerJOperand` only puts an `.imm` where the
    mnemonic has an imm form, and a repo-wide search finds `.adcx _ (.imm _)` /
    `.adox _ (.imm _)` only inside `evalInstr` semantics tests, never on a byte
    path. Both sites are commented; if a lowering ever starts producing one, the
    text path's gas error is the detector, not this encoder. -/
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
  -- TEST = REX.W 85 /r register form, REX.W F7 /0 id immediate form. The
  -- ModRM `reg` field carries the second operand, so the two register numbers
  -- go in the same order as `and_`'s; `test` writes no register.
  | .test a b =>
      match b with
      | .reg r => encAluRR 0x85 (gpNum (regOf alloc a)) (gpNum (regOf alloc r))
      | .imm v => encTestImm (gpNum (regOf alloc a)) v
  -- CMP = 39 /r register form, 81 /7 id immediate form; the difference is
  -- discarded, so like `test` this writes no register.
  | .cmp a b =>
      match b with
      | .reg r => encAluRR 0x39 (gpNum (regOf alloc a)) (gpNum (regOf alloc r))
      | .imm v => encAluImm 7 (gpNum (regOf alloc a)) v
  -- NOT = F7 /2.
  | .not_ d => encUnaryF7 2 (gpNum (regOf alloc d))
  -- ANDN = VEX.LZ.0F38.W1 F2 /r; `vvvv` carries the complemented source.
  | .andn d a b =>
      encVex3RR 0b00010 0b00 0xf2 (gpNum (regOf alloc d))
        (gpNum (regOf alloc a)) (gpNum (regOf alloc b))
  -- ROL/ROR = C1 /0 and /1 with an imm8, D1 /0 and /1 at a count of one.
  | .rol d amt =>
      match amt with
      | .imm 1 => encShiftByOne 0 (gpNum (regOf alloc d))
      | .imm v => encShiftImm 0 (gpNum (regOf alloc d)) v
      | .reg _ => []
  | .ror d amt =>
      match amt with
      | .imm 1 => encShiftByOne 1 (gpNum (regOf alloc d))
      | .imm v => encShiftImm 1 (gpNum (regOf alloc d)) v
      | .reg _ => []
  -- RORX = VEX.LZ.F2.0F3A.W1 F0 /r ib, non-destructive and flag-free.
  | .rorx d src amt =>
      match amt with
      | .imm v => encRorx (gpNum (regOf alloc d)) (gpNum (regOf alloc src)) v
      | .reg _ => []
  -- SHLX/SHRX/SARX = VEX.LZ.{66,F2,F3}.0F38.W1 F7 /r (`encShiftX`); `vvvv`
  -- carries the count.
  | .shlx d src c =>
      encShiftX 4 (gpNum (regOf alloc d)) (gpNum (regOf alloc src)) (gpNum (regOf alloc c))
  | .shrx d src c =>
      encShiftX 5 (gpNum (regOf alloc d)) (gpNum (regOf alloc src)) (gpNum (regOf alloc c))
  | .sarx d src c =>
      encShiftX 7 (gpNum (regOf alloc d)) (gpNum (regOf alloc src)) (gpNum (regOf alloc c))
  -- MOVZX from 8/16 is `0F B6`/`0F B7`; from 32 the plain 32-bit `MOV` (89 /r,
  -- no REX.W) already zeroes the upper half, which is why gas emits `movl`.
  | .movzx d sw src =>
      let dn := gpNum (regOf alloc d); let sn := gpNum (regOf alloc src)
      if sw = 8 then enc0FRR 0xb6 dn sn
      else if sw = 16 then enc0FRR 0xb7 dn sn
      else if sw = 32 then
        (if bit dn 3 = 0 && bit sn 3 = 0 then [] else [BitVec.ofNat 8 (rex 0 (bit dn 3) 0 (bit sn 3))])
          ++ [BitVec.ofNat 8 0x89, BitVec.ofNat 8 (modRMReg sn dn)]
      else []
  -- MOVSX from 8/16 is `0F BE`/`0F BF`; from 32 it is MOVSXD `63 /r`.
  | .movsx d sw src =>
      let dn := gpNum (regOf alloc d); let sn := gpNum (regOf alloc src)
      if sw = 8 then enc0FRR 0xbe dn sn
      else if sw = 16 then enc0FRR 0xbf dn sn
      else if sw = 32 then encAluRRrev 0x63 dn sn
      else []
  -- LEA = 8D /r with the SIB escape; no memory is touched.
  | .lea d base idx scale off =>
      encLeaSib (gpNum (regOf alloc d)) (gpNum (regOf alloc base))
        (gpNum (regOf alloc idx)) scale off
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
      -- x86's variable shift (`D3 /ext`) reads the count from `%cl` only: a
      -- register count allocated to `%rcx` encodes as that form and any other
      -- count register carries no bytes (`encShiftRegCount`), since the BMI2
      -- form writes no flag where `x86_SHL` does. The gather's two-source
      -- `regArith .shr`/`.shl` export (`LoweringExtended.lowerAluJ2`) lowers
      -- to the BMI2 `.shlx`/`.shrx` instead; `encodableJInstr` excludes this
      -- shape, so `encodeJInstr?` refuses it.
      | .reg c => encShiftRegCount alloc 4 d c
  | .shr d s =>
      match s with
      | .imm v => encShiftImm 5 (gpNum (regOf alloc d)) v
      | .reg c => encShiftRegCount alloc 5 d c
  | .sar d s =>
      match s with
      | .imm v => encShiftImm 7 (gpNum (regOf alloc d)) v
      | .reg c => encShiftRegCount alloc 7 d c
  -- The `.imm` arms of `CMOVcc`/`ADCX`/`ADOX`/`MULX` below fall back to source
  -- register `0` (`%rax`): x86 gives these opcodes NO immediate operand form, so
  -- there is nothing faithful to emit. `AsmPrinter` diverges here — it prints
  -- `cmoveq $v, %d` / `adcx $v, %d` / `mulx $v, …`, which gas rejects. Unreachable
  -- from any lowering; see the `encodeJInstr` docstring.
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
      -- Store-immediate: the SDM `C7 /0 id` imm-to-memory form, matching what
      -- `AsmPrinter` prints (`movq $v, off(%base)`) and gas encodes. (This arm used
      -- to reuse `89 /r` with source register 0, i.e. `movq %rax, off(%base)` —
      -- storing whatever happened to be in `%rax` instead of `v`, and diverging
      -- from the text path. `MpnLoopEmit`/`MpnLoopOwnedEmit.zeroLoopBody` emits
      -- exactly this shape: `storeMem "r" 0 (.imm 0)`.)
      | .imm v => encMemMovImm (gpNum (regOf alloc base)) off v
  | .loadMemIdx d base idx scale =>
      encMemMovSib 0x8b (gpNum (regOf alloc d)) (gpNum (regOf alloc base))
        (gpNum (regOf alloc idx)) scale
  | .storeMemIdx base idx scale s =>
      match s with
      | .reg r => encMemMovSib 0x89 (gpNum (regOf alloc r)) (gpNum (regOf alloc base))
                    (gpNum (regOf alloc idx)) scale
      -- Store-immediate to a SIB address: the `C7 /0 id` form (same fix as the
      -- constant-offset `storeMem` arm above; `GatherInPlace.lowerLinstrExtCov3`'s
      -- `STOREIDX` arm passes `lowerJOperand val` through, so an `.imm` value
      -- reaches here whenever the IR scatters a constant).
      | .imm v => encMemMovSibImm (gpNum (regOf alloc base))
                    (gpNum (regOf alloc idx)) scale v
  -- `loadSym dst sym` (`leaq sym(%rip), %dst`) is UNSUPPORTED on the byte path:
  -- a `.rodata`-symbol `leaq` needs an assembler/linker **relocation** (a
  -- R_X86_64_PC32/REX.W lea against `sym`), not the fixed `disp32` this encoder
  -- materialises — there is no symbol-relocation machinery here. The NTT (the only
  -- emitter of `loadSym`) uses the TEXT `AsmPrinter` path, which renders the real
  -- `leaq sym(%rip), %dst` line for `gas` to relocate; this byte path never sees
  -- it. Emit NO bytes (an explicit, detectable gap in a byte-diff KAT) rather than
  -- a silently-wrong fixed-disp encoding.
  | .loadSym _ _ => []  -- unsupported: needs a relocation; use the text path
  -- The memory-operand arithmetic, with the shared base-aware `memTail`:
  -- `ADD r64, r/m64` = `REX.W 03 /r`; `ADD r/m64, r64` = `REX.W 01 /r`;
  -- `ADD r/m64, imm32` = `REX.W 81 /0 id` (the `encAluImm` precondition on the
  -- immediate, gated by `encodableJInstr`); `ADCX`/`ADOX r64, r/m64` =
  -- `66`/`F3 REX.W 0F 38 F6 /r`; `IMUL r64, r/m64` = `REX.W 0F AF /r`;
  -- `IMUL r64, r/m64, imm32` = `REX.W 69 /r id`.
  | .addMem d base off => encMemMov 0x03 (gpNum (regOf alloc d)) (gpNum (regOf alloc base)) off
  | .addToMem base off s =>
      match s with
      | .reg r => encMemMov 0x01 (gpNum (regOf alloc r)) (gpNum (regOf alloc base)) off
      | .imm v => encMemMov 0x81 0 (gpNum (regOf alloc base)) off ++ imm32LE v
  | .adcxMem d base off =>
      let dn := gpNum (regOf alloc d); let bn := gpNum (regOf alloc base)
      ([ 0x66, rex 1 (bit dn 3) 0 (bit bn 3), 0x0f, 0x38, 0xf6 ].map (BitVec.ofNat 8))
        ++ memTail dn bn off
  | .adoxMem d base off =>
      let dn := gpNum (regOf alloc d); let bn := gpNum (regOf alloc base)
      ([ 0xf3, rex 1 (bit dn 3) 0 (bit bn 3), 0x0f, 0x38, 0xf6 ].map (BitVec.ofNat 8))
        ++ memTail dn bn off
  | .imulMem d base off =>
      let dn := gpNum (regOf alloc d); let bn := gpNum (regOf alloc base)
      ([ rex 1 (bit dn 3) 0 (bit bn 3), 0x0f, 0xaf ].map (BitVec.ofNat 8)) ++ memTail dn bn off
  | .imulriMem d base off imm =>
      encMemMov 0x69 (gpNum (regOf alloc d)) (gpNum (regOf alloc base)) off ++ imm32LE imm
  -- BZHI = VEX.LZ.0F38.W1 F5 /r; `vvvv` carries the index. Gas-pinned:
  -- `bzhi %rbx,%rcx,%rax` = `C4 E2 E0 F5 C1`, `bzhi %r11,%rbx,%r13` = `C4 62 A0 F5 EB`.
  | .bzhi d src idx =>
      encVex3RR 0b00010 0b00 0xf5 (gpNum (regOf alloc d))
        (gpNum (regOf alloc idx)) (gpNum (regOf alloc src))
  -- Not yet encoded: `INC`, `DEC`, `CLC`, `STC`, `XCHG`, `IMUL $imm, %src, %dst`, the
  -- one-operand `MUL`/`IMUL`, `SHLD`/`SHRD`, `RCL`/`RCR`, the general `CMOVcc`/`SETcc`,
  -- the sized `TEST` and `BT`/`BTR`/`BTS`. They emit no bytes and `encodableJInstr`
  -- refuses them, so `encodeJInstr?` returns `none`; the text `AsmPrinter` path
  -- renders them.
  | .inc _ | .dec _ | .clc | .stc | .xchg _ _ | .imulri _ _ _ | .mul _ _ _
  | .imulWide _ _ _ | .shld _ _ _ | .shrd _ _ _ | .rcl _ _ | .rcr _ _
  | .cmovcc _ _ _ | .setcc _ _ | .testN _ _ _ | .bt _ _ | .btr _ _ | .bts _ _ => []

/-- Encode a whole block: concatenate the byte encodings of its instructions. The
    contiguous machine-code stream a `.text` section / loader consumes. -/
def encodeJBlock (alloc : GpAlloc) (block : List (JInstr 64)) : List (BitVec 8) :=
  block.flatMap (encodeJInstr alloc)

/-! ## 4b. The encodable gate and the checked entry point

Two allocations put a register name into the encoder that names no register.
`regOf` returns the sentinel `<UNALLOCATED:n>` for a name the allocation does not
cover — the state `allocOverflow` reports — and `gpNum` defaults it to `0`, the
number of `%rax`. `gpPool` contains `%rax`, so on a block whose distinct name count
exceeds the pool two block names share one physical register. A pinned register
spelled outside the canonical sixteen defaults the same way, and `allocOverflow`
reports nothing, because the name *is* mapped; so does a `pinned` list sending two
names to one register.

`encodableJBlock` is the decidable gate that excludes all three: every register
name the block mentions resolves through the allocation to a canonical `%rN`
(`gpNum? ≠ none`), and distinct names resolve to distinct registers.
`encodeJBlock?` is the entry point that fails rather than encoding, so pool
exhaustion or a bad spelling is an emit failure and not a wrong instruction. -/

/-- The name resolves through the allocation to one of the sixteen canonical
    `%rN` register names. -/
def regResolvable (alloc : GpAlloc) (n : String) : Bool :=
  (gpNum? (regOf alloc n)).isSome

/-- Every register name the block mentions resolves through the allocation. -/
def blockRegsResolvable (alloc : GpAlloc) (block : List (JInstr 64)) : Bool :=
  (blockNames block).all (regResolvable alloc)

/-- The allocation sends the block's distinct register names to distinct physical
    registers. -/
def blockRegsDistinct (alloc : GpAlloc) (block : List (JInstr 64)) : Bool :=
  decide (((blockNames block).map (regOf alloc)).Nodup)

/-- The allocation resolves every register name of the block, and resolves
    distinct names to distinct registers. -/
def encodableJBlock (alloc : GpAlloc) (block : List (JInstr 64)) : Bool :=
  blockRegsResolvable alloc block && blockRegsDistinct alloc block

/-- Encode a block, or fail: `none` when the allocation leaves a register name of
    the block unresolvable, or sends two of its names to one register. -/
def encodeJBlock? (alloc : GpAlloc) (block : List (JInstr 64)) :
    Option (List (BitVec 8)) :=
  if encodableJBlock alloc block then some (encodeJBlock alloc block) else none

/-- On a block the gate accepts, the checked entry point returns the encoder's
    bytes. -/
theorem encodeJBlock?_eq_some (alloc : GpAlloc) (block : List (JInstr 64))
    (h : encodableJBlock alloc block = true) :
    encodeJBlock? alloc block = some (encodeJBlock alloc block) := by
  simp [encodeJBlock?, h]

/-- The checked entry point succeeds exactly on the blocks the gate accepts. -/
theorem encodeJBlock?_isSome (alloc : GpAlloc) (block : List (JInstr 64)) :
    (encodeJBlock? alloc block).isSome = encodableJBlock alloc block := by
  unfold encodeJBlock?
  split <;> simp_all

/-- Every byte stream the checked entry point returns is an `encodeJBlock`
    stream, so the encoder's structural and round-trip results carry over
    unchanged to it. -/
theorem eq_encodeJBlock_of_encodeJBlock?_eq_some (alloc : GpAlloc)
    (block : List (JInstr 64)) {bs : List (BitVec 8)}
    (h : encodeJBlock? alloc block = some bs) : bs = encodeJBlock alloc block := by
  unfold encodeJBlock? at h
  split at h <;> simp_all

/-- A name the gate accepts resolves to a canonical `%rN`. -/
theorem regResolvable_of_encodable {alloc : GpAlloc} {block : List (JInstr 64)}
    (h : encodableJBlock alloc block = true) {n : String}
    (hn : n ∈ blockNames block) : regResolvable alloc n = true := by
  unfold encodableJBlock blockRegsResolvable at h
  exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp h).1 n hn

/-- The registers the gate's allocation assigns the block's distinct names are
    themselves distinct. -/
theorem regOf_nodup_of_encodable {alloc : GpAlloc} {block : List (JInstr 64)}
    (h : encodableJBlock alloc block = true) :
    ((blockNames block).map (regOf alloc)).Nodup := by
  unfold encodableJBlock blockRegsDistinct at h
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).2

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

/-! ## §7. The encodable fragment

`encodeJInstr` is total: where x86-64 has no encoding for an operand shape it
emits bytes anyway, and those bytes denote something other than the instruction.
Two shapes are affected, both described in the docstrings above; a third class,
the instructions not yet encoded, emits no bytes at all.

* The group-1 ALU forms `ADD/OR/ADC/SBB/AND/SUB/XOR/CMP $imm`. Their
  `81 /digit id` field is a signed 32-bit immediate that the CPU sign-extends to
  the 64-bit operand, so the encoding denotes `v` exactly on `fitsImm32S`.
  Outside it, `v ∈ [2^31, 2^32)` is sign-extended to a negative value and
  `v ≥ 2^32` additionally loses its high bits to `imm32LE`'s truncation.
* `CMOVcc`, `ADCX`, `ADOX` and `MULX`, which take no immediate operand at all
  and whose `.imm` arms fall back to register `0` (`%rax`).
* `INC`, `DEC`, `CLC`, `STC`, `XCHG`, `IMULri`, `MUL`, the one-operand `IMUL`,
  `SHLD`, `SHRD`, `RCL`, `RCR`, the general `CMOVcc`/`SETcc`, the sized `TEST` and
  `BT`/`BTR`/`BTS`, which are not yet encoded and whose arms return no bytes.

`encodableJInstr` decides membership of the faithful fragment and
`encodeJInstr?` refuses outside it, so an emitter reaching an unencodable
immediate gets `none` rather than wrong bytes. The wide-immediate ALU case has
no local repair — x86-64's only lowering is to materialise the value into a
scratch register first, which is a register-allocation decision this encoder
cannot make — so refusal is the correct behaviour here. -/

/-- Does `v`'s 64-bit two's-complement image fit the signed 32-bit immediate
    field that `81 /digit id` carries and the CPU sign-extends? -/
def fitsImm32S (v : Nat) : Bool := v < 2 ^ 31 || 2 ^ 64 - 2 ^ 31 ≤ v

/-- The instruction and immediate operand shapes `encodeJInstr` encodes faithfully.
    The instructions `INC`, `DEC`, `CLC`, `STC`, `XCHG`, `IMULri`, `MUL`, the
    one-operand `IMUL`, `SHLD`, `SHRD`, `RCL`, `RCR`, `CMOVcc`/`SETcc` at a general
    condition, the sized `TEST` and `BT`/`BTR`/`BTS` are not yet encoded and are
    outside the fragment. -/
def encodableJInstr : JInstr 64 → Bool
  | .add _ (.imm v) | .sub _ (.imm v) | .adc _ (.imm v) | .sbb _ (.imm v)
  | .and_ _ (.imm v) | .or_ _ (.imm v) | .xor_ _ (.imm v) | .cmp _ (.imm v)
  | .addToMem _ _ (.imm v) | .imulriMem _ _ _ v =>
      fitsImm32S v
  | .cmove _ (.imm _) | .adcx _ (.imm _) | .adox _ (.imm _) => false
  | .mulx _ _ (.imm _) _ | .mulx _ _ _ (.imm _) => false
  -- a register-count shift encodes only when its count register is `%rcx`, a
  -- fact of the allocation this gate does not see; the flag-free BMI2 form is
  -- the separate `.shlx`/`.shrx`/`.sarx`.
  | .shl _ (.reg _) | .shr _ (.reg _) | .sar _ (.reg _) => false
  -- the instructions `encodeJInstr` does not yet encode.
  | .inc _ | .dec _ | .clc | .stc | .xchg _ _ | .imulri _ _ _ | .mul _ _ _
  | .imulWide _ _ _ | .shld _ _ _ | .shrd _ _ _ | .rcl _ _ | .rcr _ _
  | .cmovcc _ _ _ | .setcc _ _ | .testN _ _ _ | .bt _ _ | .btr _ _ | .bts _ _ => false
  | _ => true

/-- `encodeJInstr` restricted to the fragment it encodes faithfully. -/
def encodeJInstr? (alloc : GpAlloc) (i : JInstr 64) : Option (List (BitVec 8)) :=
  if encodableJInstr i then some (encodeJInstr alloc i) else none

/-- Every block instruction encodable, or the first one that is not. -/
def firstUnencodable : List (JInstr 64) → Option (JInstr 64)
  | [] => none
  | i :: rest => if encodableJInstr i then firstUnencodable rest else some i

theorem encodeJInstr?_isSome (alloc : GpAlloc) (i : JInstr 64) :
    (encodeJInstr? alloc i).isSome = encodableJInstr i := by
  unfold encodeJInstr?
  split <;> simp_all

theorem encodeJInstr?_eq_some (alloc : GpAlloc) (i : JInstr 64)
    (h : encodableJInstr i = true) :
    encodeJInstr? alloc i = some (encodeJInstr alloc i) := by
  unfold encodeJInstr?; simp [h]

theorem encodeJInstr?_eq_none (alloc : GpAlloc) (i : JInstr 64)
    (h : encodableJInstr i = false) : encodeJInstr? alloc i = none := by
  unfold encodeJInstr?; simp [h]

/-- A wide ALU immediate is refused rather than truncated. -/
theorem encodeJInstr?_add_imm_wide (alloc : GpAlloc) (d : String) (v : Nat)
    (h : fitsImm32S v = false) : encodeJInstr? alloc (.add d (.imm v)) = none :=
  encodeJInstr?_eq_none alloc _ (by simp [encodableJInstr, h])

/-- `CMOVcc $imm` has no x86 encoding and is refused. -/
theorem encodeJInstr?_cmove_imm (alloc : GpAlloc) (d : String) (v : Nat) :
    encodeJInstr? alloc (.cmove d (.imm v)) = none :=
  encodeJInstr?_eq_none alloc _ rfl

/-! ### Register-count shifts

The group-2 shifts take a register count only in `%cl`. The bytes of
`.shl`/`.shr`/`.sar d (.reg c)` are the `REX.W D3 /ext` form when `c` is
allocated to `%rcx` and empty otherwise, and the gated encoder refuses the shape
outright; the flag-free BMI2 form is the separate `.shlx`/`.shrx`/`.sarx`
(`encShiftX`), whose bytes are pinned against the SDM encoding below, since
`SailX86Decoder` has no VEX decode path. -/

/-- A BMI2 variable shift is five bytes. -/
@[simp] theorem encShiftX_length (ext dst src cnt : Nat) :
    (encShiftX ext dst src cnt).length = 5 := by
  simp [encShiftX, encVex3RR]

/-- `shrx %rcx, %rax, %rdx` (count `%rcx`, value `%rax`, destination `%rdx`) is
    `C4 E2 F3 F7 D0`: `C4`; `R̄=1 X̄=1 B̄=1 mm=00010` = `E2` (no extended register);
    `W=1`, `~vvvv = ~0001 = 1110`, `L=0`, `pp=11` (`F2`) = `F3`; opcode `F7`;
    ModRM `11 010 000` (`reg = %rdx`, `rm = %rax`) = `D0`. -/
theorem encShiftX_shrx_rcx_rax_rdx :
    encShiftX 5 2 0 1 = [0xc4, 0xe2, 0xf3, 0xf7, 0xd0] := by decide

/-- `shlx %rbx, %rcx, %rax` is `C4 E2 E1 F7 C1` (the `encVex3RR` gas pin):
    `~vvvv = ~0011 = 1100`, `pp=01` (`66`) = `E1`; ModRM `11 000 001` = `C1`. -/
theorem encShiftX_shlx_rbx_rcx_rax :
    encShiftX 4 0 1 3 = [0xc4, 0xe2, 0xe1, 0xf7, 0xc1] := by decide

/-- `sarx %r11, %rbx, %r13` is `C4 62 A2 F7 EB`: `R̄=0` (`%r13`), `B̄=1`,
    so the second byte is `62`; `~vvvv = ~1011 = 0100`, `pp=10` (`F3`) = `A2`;
    ModRM `11 101 011` = `EB`. -/
theorem encShiftX_sarx_r11_rbx_r13 :
    encShiftX 7 13 3 11 = [0xc4, 0x62, 0xa2, 0xf7, 0xeb] := by decide

/-- The bytes of a register-count logical right shift: the `%cl` form
    `D3 /5` when the count is allocated to `%rcx`, none otherwise. -/
theorem encodeJInstr_shr_reg (alloc : GpAlloc) (d c : String) :
    encodeJInstr alloc (.shr d (.reg c))
      = if regOf alloc c = "%rcx" then encShiftCl 5 (gpNum (regOf alloc d)) else [] := rfl

/-- The bytes of a register-count left shift: the `%cl` form `D3 /4` when the
    count is allocated to `%rcx`, none otherwise. -/
theorem encodeJInstr_shl_reg (alloc : GpAlloc) (d c : String) :
    encodeJInstr alloc (.shl d (.reg c))
      = if regOf alloc c = "%rcx" then encShiftCl 4 (gpNum (regOf alloc d)) else [] := rfl

/-- The bytes of a register-count arithmetic right shift: the `%cl` form
    `D3 /7` when the count is allocated to `%rcx`, none otherwise. -/
theorem encodeJInstr_sar_reg (alloc : GpAlloc) (d c : String) :
    encodeJInstr alloc (.sar d (.reg c))
      = if regOf alloc c = "%rcx" then encShiftCl 7 (gpNum (regOf alloc d)) else [] := rfl

/-- A register-count shift whose count is not in `%rcx` carries no bytes. -/
theorem encodeJInstr_shr_reg_ne_rcx (alloc : GpAlloc) (d c : String)
    (h : regOf alloc c ≠ "%rcx") : encodeJInstr alloc (.shr d (.reg c)) = [] := by
  rw [encodeJInstr_shr_reg, if_neg h]

/-- A register-count shift whose count is in `%rcx` is the `D3 /5` form. -/
theorem encodeJInstr_shr_reg_rcx (alloc : GpAlloc) (d c : String)
    (h : regOf alloc c = "%rcx") :
    encodeJInstr alloc (.shr d (.reg c)) = encShiftCl 5 (gpNum (regOf alloc d)) := by
  rw [encodeJInstr_shr_reg, if_pos h]

/-- The gated encoder refuses a register-count logical right shift. -/
theorem encodeJInstr?_shr_reg (alloc : GpAlloc) (d c : String) :
    encodeJInstr? alloc (.shr d (.reg c)) = none :=
  encodeJInstr?_eq_none alloc _ rfl

/-- The gated encoder refuses a register-count left shift. -/
theorem encodeJInstr?_shl_reg (alloc : GpAlloc) (d c : String) :
    encodeJInstr? alloc (.shl d (.reg c)) = none :=
  encodeJInstr?_eq_none alloc _ rfl

/-- The gated encoder refuses a register-count arithmetic right shift. -/
theorem encodeJInstr?_sar_reg (alloc : GpAlloc) (d c : String) :
    encodeJInstr? alloc (.sar d (.reg c)) = none :=
  encodeJInstr?_eq_none alloc _ rfl

/-- The gated encoder accepts the BMI2 `shrx`, the flag-free register-count
    shift at the `JInstr` level. -/
theorem encodeJInstr?_shrx (alloc : GpAlloc) (d src c : String) :
    encodeJInstr? alloc (.shrx d src c)
      = some (encShiftX 5 (gpNum (regOf alloc d)) (gpNum (regOf alloc src))
          (gpNum (regOf alloc c))) :=
  encodeJInstr?_eq_some alloc _ rfl

/-! ### The two encodings compute one data word

`JasminModel.evalInstr` runs `.shr d (.reg c)` as `x86_SHR`, whose count is
`shiftCount c = c.toNat % 64`, and `.shrx d src c` as `x86_SHRX` with the same
mask. The data words coincide for every count, so `shr %cl, %d` (`encShiftCl`)
and `shrx %c, %d, %d` (`encShiftX`) write the same destination; the flags
`x86_SHR` writes at a nonzero count are the difference between the two
instructions, which is why only `.shrx` is encoded as `encShiftX`. -/

/-- The `x86_SHR` data word is the `x86_SHRX` word at every count. -/
theorem x86_SHR_word_eq_SHRX {w : Nat} (v c : BitVec w) :
    (x86_SHR v c).word = x86_SHRX v c := by
  unfold x86_SHR x86_SHRX
  by_cases h : shiftCount c = 0 <;> simp [rflags_None, rflags_OF, wshr, h]

/-- The `x86_SHL` data word is the `x86_SHLX` word at every count. -/
theorem x86_SHL_word_eq_SHLX {w : Nat} (v c : BitVec w) :
    (x86_SHL v c).word = x86_SHLX v c := by
  unfold x86_SHL x86_SHLX
  by_cases h : shiftCount c = 0 <;> simp [rflags_None, rflags_OF, wshl, h]

/-- The `x86_SAR` data word is the `x86_SARX` word at every count. -/
theorem x86_SAR_word_eq_SARX {w : Nat} (v c : BitVec w) :
    (x86_SAR v c).word = x86_SARX v c := by
  unfold x86_SAR x86_SARX
  by_cases h : shiftCount c = 0 <;> simp [rflags_None, rflags_OF, wsar, h]

end CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
