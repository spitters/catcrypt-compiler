/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder

/-!
# A64 ABI / scaffolding-instruction byte encoder (the whole-function residual, #552-obj)

`ArmEncoder.lean` encodes the verified *body* `AInst`/`BInst` instructions (the
GP-ALU and the 64-bit bignum forms) plus the branch alphabet. To emit a **whole
AArch64 function** as machine-code bytes — prologue, body, epilogue, and an
in-`.text` `_start` driver, with NO `as`/gas anywhere on the object-build path —
the remaining instructions are the AAPCS64 frame scaffolding and the freestanding
KAT driver alphabet:

* `STP`/`LDP` (store/load register pair) — signed-offset, pre-index, post-index
  forms (the callee-save bank + the argument-buffer load/store prologue/epilogue);
* `RET` — the function return (`RET X30`);
* `ADD`/`SUB` (immediate) — frame-pointer / stack-pointer adjustment, argument
  address computation;
* `LDR`/`STR` (unsigned-offset immediate, `W` form) — the RA spill/reload + the
  ABI-pinned state-buffer traffic;
* `CMP` (immediate) = `SUBS XZR, Xn, #imm` — the KAT comparison;
* `BL` (branch-with-link) — the driver's call into the emitted function (a
  PC-relative `imm26`, resolved locally when both sit in one `.text`);
* `SVC #imm` — the `exit` syscall the freestanding driver issues.

Each builder places the register numbers / immediate at the exact bit positions
the Arm Architecture Reference Manual C4.1 tables specify; the differential pins
at the foot anchor every word to `aarch64-linux-gnu-as`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmAbiEncoder

open CatCrypt.Crypto.SecureCompilation.ARMBackend
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder

/-! ## 1. Load/store register pair (STP/LDP), 64-bit `X` form

C4.1 "Load/store register pair": `opc(2) 101 V 0 idx(2) L imm7 Rt2 Rn Rt`.
For the `X` (64-bit) GP form, `opc=10`, `V=0`. `L=1` ⇒ LDP, `L=0` ⇒ STP. The
addressing-mode index field selects: post-index `01`, signed-offset `10`,
pre-index `11`. `imm7` is the offset scaled by 8 (a signed 7-bit field). -/

/-- The three LDP/STP addressing modes. -/
inductive PairMode where
  /-- `[Rn], #imm` — post-index (write-back after). -/
  | post
  /-- `[Rn, #imm]` — signed-offset (no write-back). -/
  | signed
  /-- `[Rn, #imm]!` — pre-index (write-back before). -/
  | pre
  deriving Repr, DecidableEq

/-- The 24-bit base opcode word for a given mode and `L` (load=1/store=0),
    `X` form (`opc=10`, `V=0`). Bits [31:30]=`opc`=10, [29:27]=101, [26]=`V`=0,
    [25:23] mode-dependent, [22]=`L`. -/
def pairBase : PairMode → Nat → Nat
  | .post,   l => 0xa8800000 + (l % 2) * 0x400000   -- 1010 1000 1L0…
  | .signed, l => 0xa9000000 + (l % 2) * 0x400000   -- 1010 1001 0L0…
  | .pre,    l => 0xa9800000 + (l % 2) * 0x400000   -- 1010 1001 1L0…

/-- `STP/LDP Xt, Xt2, [Xn{, #imm}]{!}` — 64-bit pair. `imm` is the BYTE offset
    (must be a multiple of 8); the encoded `imm7` field is `imm/8` as a signed
    7-bit value. Word: `pairBase + imm7(7)<<15 + Rt2(5)<<10 + Rn(5)<<5 + Rt(5)`. -/
def encLdStPair (mode : PairMode) (l t t2 n : Nat) (imm : Int) : List (BitVec 8) :=
  let imm7 := (BitVec.ofInt 7 (imm / 8)).toNat       -- scaled-by-8, signed 7-bit
  let w := pairBase mode l + imm7 * 0x8000 + (t2 % 32) * 0x400
           + (n % 32) * 0x20 + (t % 32)
  wordLE w

/-- `STP Xt, Xt2, [Xn, #imm]` (signed-offset store pair). -/
def encStpOff (t t2 n : Nat) (imm : Int) : List (BitVec 8) := encLdStPair .signed 0 t t2 n imm
/-- `LDP Xt, Xt2, [Xn, #imm]` (signed-offset load pair). -/
def encLdpOff (t t2 n : Nat) (imm : Int) : List (BitVec 8) := encLdStPair .signed 1 t t2 n imm
/-- `STP Xt, Xt2, [Xn, #imm]!` (pre-index store pair, the callee-save push). -/
def encStpPre (t t2 n : Nat) (imm : Int) : List (BitVec 8) := encLdStPair .pre 0 t t2 n imm
/-- `LDP Xt, Xt2, [Xn], #imm` (post-index load pair, the callee-save pop). -/
def encLdpPost (t t2 n : Nat) (imm : Int) : List (BitVec 8) := encLdStPair .post 1 t t2 n imm

/-! ## 2. Load/store register, unsigned-offset immediate, `W` (32-bit) form

C4.1 "Load/store register (unsigned immediate)": `size(2) 111 V 01 opc(2) imm12 Rn Rt`.
For the `W` (32-bit) GP form, `size=10`, `V=0`. `STR`=`opc=00` (`0xb9000000`),
`LDR`=`opc=01` (`0xb9400000`). `imm12` is the offset scaled by 4 (the access size). -/

/-- `STR/LDR Wt, [Xn, #imm]` — 32-bit unsigned-offset. `imm` is the BYTE offset
    (a multiple of 4); the `imm12` field is `imm/4`. `l=1` ⇒ LDR, `l=0` ⇒ STR.
    Word: `0xb9000000 + L<<22 + imm12(12)<<10 + Rn(5)<<5 + Rt(5)`. -/
def encLdStWord (l t n : Nat) (imm : Nat) : List (BitVec 8) :=
  let imm12 := (imm / 4) % 0x1000
  let w := 0xb9000000 + (l % 2) * 0x400000 + imm12 * 0x400 + (n % 32) * 0x20 + (t % 32)
  wordLE w

/-- `STR Wt, [Xn, #imm]`. -/
def encStrW (t n : Nat) (imm : Nat) : List (BitVec 8) := encLdStWord 0 t n imm
/-- `LDR Wt, [Xn, #imm]`. -/
def encLdrW (t n : Nat) (imm : Nat) : List (BitVec 8) := encLdStWord 1 t n imm

/-! ## 3. Add/subtract (immediate), `X` (64-bit) form

C4.1 "Add/subtract (immediate)": `sf op S 100010 sh imm12 Rn Rd`. `X` form `sf=1`.
`ADD`=`op=0` (`0x91000000`), `SUB`=`op=1` (`0xd1000000`); `S=1` sets flags
(`SUBS`/`ADDS`, used by `CMP`). `sh=0` ⇒ no 12-bit left shift on the immediate.
`Rd=Rn=31` denotes the stack pointer `SP` in this encoding class (not XZR). -/

/-- `ADD/SUB(S) Xd, Xn, #imm12` (immediate, no shift). `op=0` ADD / `op=1` SUB;
    `s=1` ⇒ flag-setting (`ADDS`/`SUBS`). Word:
    `1(sf) op S 100010 0(sh) imm12(12) Rn(5) Rd(5)`. -/
def encAddSubImm (op s d n : Nat) (imm12 : Nat) : List (BitVec 8) :=
  let w := 0x91000000 + (op % 2) * 0x40000000 + (s % 2) * 0x20000000
           + (imm12 % 0x1000) * 0x400 + (n % 32) * 0x20 + (d % 32)
  wordLE w

/-- `ADD Xd, Xn, #imm`. -/
def encAddImm (d n : Nat) (imm12 : Nat) : List (BitVec 8) := encAddSubImm 0 0 d n imm12
/-- `SUB Xd, Xn, #imm`. -/
def encSubImm (d n : Nat) (imm12 : Nat) : List (BitVec 8) := encAddSubImm 1 0 d n imm12
/-- `CMP Xn, #imm` = `SUBS XZR, Xn, #imm` (`Rd=31`=XZR, `S=1`). -/
def encCmpImm (n : Nat) (imm12 : Nat) : List (BitVec 8) := encAddSubImm 1 1 31 n imm12

/-! ## 4. The flat scaffolding words: RET, SVC, BL -/

/-- `RET {Xn}` (default `Xn=X30`). Fixed word `0xd65f03c0` (`Rn=30`).
    Word: `1101011 0 0 10 11111 0000 0 0 Rn(5) 00000`. -/
def encRet : List (BitVec 8) := wordLE (0xd65f0000 + 30 * 0x20)

/-- `SVC #imm16` — supervisor call. Word: `11010100 000 imm16 00001`.
    `0xd4000001 + imm16<<5`. -/
def encSvc (imm16 : Nat) : List (BitVec 8) :=
  wordLE (0xd4000001 + (imm16 % 0x10000) * 0x20)

/-- `BL label` — branch-with-link (the function call). `imm26` is the signed
    PC-relative word offset `(target − here)/4`. Word: `100101 imm26(26)`,
    base `0x94000000`. -/
def encBl (imm26 : Nat) : List (BitVec 8) :=
  wordLE (0x94000000 + (imm26 % 0x4000000))

/-- `CBNZ Xt, label` / `CBZ Xt, label`, **64-bit `X` form** (`sf=1`). The
    `ArmEncoder.encCmpBranch` covers only the `W` (32-bit) form (`sf=0`); a faithful
    64-bit-register compare-and-branch (e.g. checking a 64-bit limb is non-zero)
    needs `sf=1`. `op=1` CBNZ / `op=0` CBZ; `imm19` is the signed PC-relative word
    offset. Word: `1(sf) 011010 op imm19(19) Rt(5)`, base `0xb4000000`. -/
def encCmpBranchX (op t imm19 : Nat) : List (BitVec 8) :=
  wordLE (0xb4000000 + (op % 2) * 0x1000000 + (imm19 % 0x80000) * 0x20 + (t % 32))

/-! ## 5. Structural well-formedness — every scaffolding word is one 4-byte A64 word -/

@[simp] theorem encLdStPair_length (mode : PairMode) (l t t2 n : Nat) (imm : Int) :
    (encLdStPair mode l t t2 n imm).length = 4 := by simp [encLdStPair]
@[simp] theorem encLdStWord_length (l t n imm : Nat) :
    (encLdStWord l t n imm).length = 4 := by simp [encLdStWord]
@[simp] theorem encAddSubImm_length (op s d n imm12 : Nat) :
    (encAddSubImm op s d n imm12).length = 4 := by simp [encAddSubImm]
@[simp] theorem encRet_length : encRet.length = 4 := by simp [encRet]
@[simp] theorem encSvc_length (i : Nat) : (encSvc i).length = 4 := by simp [encSvc]
@[simp] theorem encBl_length (i : Nat) : (encBl i).length = 4 := by simp [encBl]
@[simp] theorem encCmpBranchX_length (op t i : Nat) :
    (encCmpBranchX op t i).length = 4 := by simp [encCmpBranchX]

/-! ## 6. Differential pins against `aarch64-linux-gnu-as` (the scaffolding gas anchor)

Every word below is pinned to the exact little-endian bytes
`aarch64-linux-gnu-as` produces (see `/tmp/armref.s` disassembly transcribed into
the bench Makefile's `abi-bytes-diff` target). `objdump` prints the big-endian
word; the `.text` stores it little-endian. -/

-- `stp x29, x30, [sp, #-16]!` → 0xa9bf7bfd
#guard encStpPre 29 30 31 (-16) == wordLE 0xa9bf7bfd
-- `ldp x29, x30, [sp], #16` → 0xa8c17bfd
#guard encLdpPost 29 30 31 16 == wordLE 0xa8c17bfd
-- `stp x19, x20, [sp, #-80]!` → 0xa9bb53f3
#guard encStpPre 19 20 31 (-80) == wordLE 0xa9bb53f3
-- `stp x21, x22, [sp, #16]` → 0xa9015bf5
#guard encStpOff 21 22 31 16 == wordLE 0xa9015bf5
-- `ldp x21, x22, [sp, #16]` → 0xa9415bf5
#guard encLdpOff 21 22 31 16 == wordLE 0xa9415bf5
-- `ldp x19, x20, [sp], #80` → 0xa8c553f3
#guard encLdpPost 19 20 31 80 == wordLE 0xa8c553f3
-- `ret` → 0xd65f03c0
#guard encRet == wordLE 0xd65f03c0
-- `ldp x4, x5, [x1]` → 0xa9401424
#guard encLdpOff 4 5 1 0 == wordLE 0xa9401424
-- `ldp x6, x7, [x1, #16]` → 0xa9411c26
#guard encLdpOff 6 7 1 16 == wordLE 0xa9411c26
-- `ldp x8, x9, [x2]` → 0xa9402448
#guard encLdpOff 8 9 2 0 == wordLE 0xa9402448
-- `ldp x10, x11, [x2, #16]` → 0xa9412c4a
#guard encLdpOff 10 11 2 16 == wordLE 0xa9412c4a
-- `stp x4, x5, [x0]` → 0xa9001404
#guard encStpOff 4 5 0 0 == wordLE 0xa9001404
-- `stp x6, x7, [x0, #16]` → 0xa9011c06
#guard encStpOff 6 7 0 16 == wordLE 0xa9011c06
-- `add x1, sp, #32` → 0x910083e1
#guard encAddImm 1 31 32 == wordLE 0x910083e1
-- `add x2, sp, #64` → 0x910103e2
#guard encAddImm 2 31 64 == wordLE 0x910103e2
-- `sub sp, sp, #96` → 0xd10183ff
#guard encSubImm 31 31 96 == wordLE 0xd10183ff
-- `add sp, sp, #96` → 0x910183ff
#guard encAddImm 31 31 96 == wordLE 0x910183ff
-- `mov x0, sp` (= `add x0, sp, #0`) → 0x910003e0
#guard encAddImm 0 31 0 == wordLE 0x910003e0
-- `cmp x10, #1` → 0xf100055f
#guard encCmpImm 10 1 == wordLE 0xf100055f
-- `cmp x10, #7` → 0xf1001d5f
#guard encCmpImm 10 7 == wordLE 0xf1001d5f
-- `svc #0` → 0xd4000001
#guard encSvc 0 == wordLE 0xd4000001
-- `bl .` (offset 0) → 0x94000000
#guard encBl 0 == wordLE 0x94000000
-- `ldr w16, [x1, #4]` → 0xb9400430
#guard encLdrW 16 1 4 == wordLE 0xb9400430
-- `str w16, [x1, #4]` → 0xb9000430
#guard encStrW 16 1 4 == wordLE 0xb9000430
-- `ldr w0, [x1, #576]` → 0xb9424020
#guard encLdrW 0 1 576 == wordLE 0xb9424020
-- `cbnz x11, .` (64-bit X form, offset 0) → 0xb500000b
#guard encCmpBranchX 1 11 0 == wordLE 0xb500000b
-- `cbz x9, .` (64-bit X form, offset −1) → 0xb4ffffe9
#guard encCmpBranchX 0 9 (0x80000 - 1) == wordLE 0xb4ffffe9

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmAbiEncoder
