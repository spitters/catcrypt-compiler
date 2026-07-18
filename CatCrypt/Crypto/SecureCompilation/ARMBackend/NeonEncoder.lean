/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.ARMBackend.NeonAsmPrinter
import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder

/-!
# A verified machine-code byte encoder for the NEON/ASIMD `NInst` instructions (#548)

`NeonAsmPrinter.lean` prints an `NInst` block to GAS AArch64 ASIMD assembly *text*,
handed to `as`/`clang` to be encoded — that last step trusts the assembler's
encoder. This module is the **NEON/ASIMD analogue of `ArmEncoder.lean`** (the
scalar GP-ALU byte encoder): it encodes each `NInst` directly to its AArch64
fixed-width 32-bit machine-code word in Lean, so the kernel body is emitted as
bytes by a function whose output we audit against the Arm ARM and round-trip
against the official `rems-project/sail-arm` ASIMD `decode64` tables
(`SailNeonDecoder.lean`).

A64 is a **fixed-width** ISA: every NEON instruction is exactly one little-endian
32-bit word (4 bytes), the same shape as the scalar subset — there are no
prefixes; the arrangement (`.4s`/`.16b`), the `Q` bit (always `1` here: 128-bit
`v` registers), `U`/`size` and the opcode field sit in fixed bit positions, with
the register numbers and shift immediate at fixed positions. We compute the word
arithmetically and reuse the scalar `wordLE` little-endian splitter.

## The narrowed trust boundary (same posture as the scalar encoder)

`NeonAsmPrinter` → `as` trusts (printer is correct GAS ASIMD syntax) ∧ (`as`
encodes each mnemonic per the Arm ARM). This encoder replaces both with a *Lean*
function whose every output word is determined by the fixed ASIMD field
construction below — auditable field by field against the Arm ARM C7 (Advanced
SIMD) tables. The remaining trusted edge shrinks to *this encoder matches the
ARM*, discharged structurally (`encodeNInst_length`: always a well-formed 4-byte
word) and by the `SailNeonDecoder.lean` round-trip `decode (encode i) = i`. The
bench differential (`bench/arm_compare`, `qr-neon-bytes-diff`) cross-checks the
emitted words against `aarch64-linux-gnu-as` output and runs the qemu KAT.

## Encoding layout (the C7 ASIMD forms this transcribes, 128-bit `Q=1`)

All register/immediate fields are at the bit positions the sail-arm `decode64`
ASIMD clauses read (`op_code[hi..lo]`).

* **ADD/SUB/MUL (vector, `same`)** — base word + `Rm[20:16] Rn[9:5] Rd[4:0]`:
  `ADD.4S = 0x4ea08400`, `SUB.4S = 0x6ea08400`, `MUL.4S = 0x4ea09c00`.
* **AND/ORR/EOR (vector logical, `16B`)** — `AND = 0x4e201c00`,
  `ORR = 0x4ea01c00`, `EOR = 0x6e201c00`.
* **SHL (vector, by immediate)** — `0x4f005400 + (32+sh)[22:16]·0x10000 …`
  (the `immh:immb` shift field is `32+sh` for the `4S` element, `Q=1`).
* **USHR (vector, by immediate)** — `0x6f000400 + (64-sh)[22:16]·0x10000 …`
  (the `immh:immb` field is `64-sh` for `4S`).
* **MOV (vector)** — the alias `ORR Vd.16B, Vn.16B, Vn.16B` (`Rm=Rn`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon.NeonEncoder

open CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon
open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmEncoder (wordLE wordLE_length)

/-! ## 1. Register-name → number -/

/-- The numeric index `0..31` of a `vN` register name (`v0=0 … v31=31`). A name
    not in the pool reads as `0` (never produced by `allocV` on a fitting block;
    an overflow yields the `<UNALLOCATED:_>` sentinel, encoded as `0`). -/
def vNum (r : String) : Nat :=
  (List.range 32).findIdx? (fun i => r = "v" ++ toString i) |>.getD 0

/-! ## 2. The fixed-field A64 ASIMD word builders

Each builder places the register numbers / shift immediate at the exact bit
positions the sail-arm `decode64` ASIMD clause reads them from. `Q=1` (128-bit
`v` registers) and the arrangement (`size`/`immh`) are baked into the base word. -/

/-- ADD/SUB/MUL (vector, same), 128-bit `4S`. `base` carries the opcode +
    `U`/`size`/`Q` bits; the register fields are added at `Rm[20:16] Rn[9:5]
    Rd[4:0]`. Word: `base + Rm·0x10000 + Rn·0x20 + Rd`. -/
def encVecRRR (base d n m : Nat) : List (BitVec 8) :=
  wordLE (base + (m % 32) * 0x10000 + (n % 32) * 0x20 + (d % 32))

/-- SHL (vector, by immediate), 128-bit `4S`. The `immh:immb` shift field is
    `32+sh` (for the `4S`/word element), placed at `[22:16]`.
    Word: `0x4f005400 + (32+sh)·0x10000 + Rn·0x20 + Rd`. -/
def encShl (d n sh : Nat) : List (BitVec 8) :=
  wordLE (0x4f005400 + ((32 + sh % 32) % 128) * 0x10000 + (n % 32) * 0x20 + (d % 32))

/-- USHR (vector, by immediate), 128-bit `4S`. The `immh:immb` shift field is
    `64-sh` (for the `4S` element), placed at `[22:16]`.
    Word: `0x6f000400 + (64-sh)·0x10000 + Rn·0x20 + Rd`. -/
def encUshr (d n sh : Nat) : List (BitVec 8) :=
  wordLE (0x6f000400 + ((64 - sh % 32) % 128) * 0x10000 + (n % 32) * 0x20 + (d % 32))

/-! ## 3. The per-`NInst` encoder

Each arm resolves its register names through the allocation `alloc`, then
dispatches to the fixed-field builder with the C7 ASIMD base word for the
mnemonic. `MOV Vd.16B, Vn.16B` is emitted as the canonical alias
`ORR Vd.16B, Vn.16B, Vn.16B` (`Rm=Rn`). -/

/-- The ADD.4S base word (`0x4ea08400`). -/
def baseAdd : Nat := 0x4ea08400
/-- The SUB.4S base word (`0x6ea08400`). -/
def baseSub : Nat := 0x6ea08400
/-- The MUL.4S base word (`0x4ea09c00`). -/
def baseMul : Nat := 0x4ea09c00
/-- The AND.16B base word (`0x4e201c00`). -/
def baseAnd : Nat := 0x4e201c00
/-- The ORR.16B base word (`0x4ea01c00`). -/
def baseOrr : Nat := 0x4ea01c00
/-- The EOR.16B base word (`0x6e201c00`). -/
def baseEor : Nat := 0x6e201c00
/-- The SQDMULH.8H base word (`0x4e60b400`) — signed saturating doubling multiply
    returning the high half, 8 × i16 (the ML-KEM NTT high-mul mnemonic, #4):
    `0 Q=1 U=0 01110 size=01 1 Rm 101101 Rn Rd`. -/
def baseSqdmulh : Nat := 0x4e60b400

/-- Encode one NEON `NInst` to its AArch64 machine bytes (a single 4-byte word),
    resolving register names through `alloc`. `MOV` is the `ORR Vd, Vn, Vn`
    alias. -/
def encodeNInst (alloc : VAlloc) : NInst → List (BitVec 8)
  | .add d a b => encVecRRR baseAdd (vNum (vOf alloc d)) (vNum (vOf alloc a)) (vNum (vOf alloc b))
  | .sub d a b => encVecRRR baseSub (vNum (vOf alloc d)) (vNum (vOf alloc a)) (vNum (vOf alloc b))
  | .mul d a b => encVecRRR baseMul (vNum (vOf alloc d)) (vNum (vOf alloc a)) (vNum (vOf alloc b))
  | .and d a b => encVecRRR baseAnd (vNum (vOf alloc d)) (vNum (vOf alloc a)) (vNum (vOf alloc b))
  | .orr d a b => encVecRRR baseOrr (vNum (vOf alloc d)) (vNum (vOf alloc a)) (vNum (vOf alloc b))
  | .eor d a b => encVecRRR baseEor (vNum (vOf alloc d)) (vNum (vOf alloc a)) (vNum (vOf alloc b))
  | .shl d a imm => encShl (vNum (vOf alloc d)) (vNum (vOf alloc a)) imm
  | .ushr d a imm => encUshr (vNum (vOf alloc d)) (vNum (vOf alloc a)) imm
  | .mov d s   => encVecRRR baseOrr (vNum (vOf alloc d)) (vNum (vOf alloc s)) (vNum (vOf alloc s)) -- ORR Vd,Vn,Vn

/-- Encode one 8 × i16 NEON instruction (`NInst8x16`, the ML-KEM NTT op) to its
    AArch64 machine bytes. `MULHS` is emitted as the `SQDMULH Vd.8H, Vn.8H, Vm.8H`
    mnemonic (the architectural high-mul; see `NeonModel §5` for the exact-Montgomery
    `SMULL/SMULL2/UZP2` realization note). -/
def encodeNInst8x16 (alloc : VAlloc) : NInst8x16 → List (BitVec 8)
  | .mulhs d a b =>
      encVecRRR baseSqdmulh (vNum (vOf alloc d)) (vNum (vOf alloc a)) (vNum (vOf alloc b))

/-- Encode a whole block: concatenate the 4-byte word encodings of its
    instructions. The contiguous machine-code stream a `.text` section consumes. -/
def encodeNBlock (alloc : VAlloc) (block : List NInst) : List (BitVec 8) :=
  block.flatMap (encodeNInst alloc)

/-! ## 3b. 128-bit `V`-register load/store (the `ldr q` / `str q` forms)

The freestanding NEON ELF driver materialises the four 4-way state vectors into a
stack buffer (4×u32 lanes, broadcast) with scalar stores, then `ldr q` them into
`v0..v3`, calls the kernel, and `str q` the four results back to memory to be
GP-compared lane-by-lane — so the object stays a single self-contained `.text`
with no NEON→GP move. These are the C7 "Load/store register (unsigned immediate),
SIMD&FP, 128-bit `Q`" forms: `size=00 V=1 opc=11` (`ldr q`) / `opc=10` (`str q`),
`imm12` scaled by 16 (the 128-bit access size).

* `LDR Qt, [Xn, #imm]` — base `0x3dc00000`, word
  `0x3dc00000 + (imm/16)·0x400 + Xn·0x20 + Qt`.
* `STR Qt, [Xn, #imm]` — base `0x3d800000`, word
  `0x3d800000 + (imm/16)·0x400 + Xn·0x20 + Qt`. -/

/-- `LDR/STR Qt, [Xn, #imm]` — 128-bit `V`-register load/store, unsigned-offset.
    `imm` is the BYTE offset (a multiple of 16); the `imm12` field is `imm/16`.
    `l=1` ⇒ `LDR Q`, `l=0` ⇒ `STR Q`.
    Word: `0x3d800000 + L·0x400000 + (imm/16)·0x400 + Xn·0x20 + Qt`. -/
def encLdStQ (l t n imm : Nat) : List (BitVec 8) :=
  let imm12 := (imm / 16) % 0x1000
  wordLE (0x3d800000 + (l % 2) * 0x400000 + imm12 * 0x400 + (n % 32) * 0x20 + (t % 32))

/-- `LDR Qt, [Xn, #imm]`. -/
def encLdrQ (t n imm : Nat) : List (BitVec 8) := encLdStQ 1 t n imm
/-- `STR Qt, [Xn, #imm]`. -/
def encStrQ (t n imm : Nat) : List (BitVec 8) := encLdStQ 0 t n imm

@[simp] theorem encLdStQ_length (l t n imm : Nat) : (encLdStQ l t n imm).length = 4 := by
  simp [encLdStQ, wordLE_length]
@[simp] theorem encLdrQ_length (t n imm : Nat) : (encLdrQ t n imm).length = 4 := by
  simp [encLdrQ]
@[simp] theorem encStrQ_length (t n imm : Nat) : (encStrQ t n imm).length = 4 := by
  simp [encStrQ]

/-- `ldr q0, [x0]` — gas word `0x3dc00000`. -/
example : encLdrQ 0 0 0 = wordLE 0x3dc00000 := by native_decide
/-- `ldr q1, [x0, #16]` — gas word `0x3dc00401`. -/
example : encLdrQ 1 0 16 = wordLE 0x3dc00401 := by native_decide
/-- `ldr q3, [x1, #48]` — gas word `0x3dc00c23`. -/
example : encLdrQ 3 1 48 = wordLE 0x3dc00c23 := by native_decide
/-- `str q0, [x2]` — gas word `0x3d800040`. -/
example : encStrQ 0 2 0 = wordLE 0x3d800040 := by native_decide
/-- `str q2, [x2, #16]` — gas word `0x3d800442`. -/
example : encStrQ 2 2 16 = wordLE 0x3d800442 := by native_decide
/-- `str q5, [x19, #240]` — gas word `0x3d803e65`. -/
example : encStrQ 5 19 240 = wordLE 0x3d803e65 := by native_decide

/-! ## 4. Structural well-formedness (the unconditional half of the trust story)

Every `encodeNInst` output is exactly one 4-byte A64 word — the fixed-width shape
the decoder requires, proved for all inputs. -/

/-- Every `NInst` encodes to exactly 4 bytes (one fixed-width A64 word). -/
theorem encodeNInst_length (alloc : VAlloc) (i : NInst) :
    (encodeNInst alloc i).length = 4 := by
  cases i <;> simp [encodeNInst, encVecRRR, encShl, encUshr, wordLE_length]

/-- `encodeNBlock` produces `4 * |block|` bytes (a fixed-width stream). -/
theorem encodeNBlock_length (alloc : VAlloc) (block : List NInst) :
    (encodeNBlock alloc block).length = 4 * block.length := by
  induction block with
  | nil => rfl
  | cons i is ih =>
      simp only [encodeNBlock, List.flatMap_cons, List.length_append, List.length_cons]
      rw [show encodeNBlock alloc is = is.flatMap (encodeNInst alloc) from rfl] at ih
      rw [encodeNInst_length, ih]; omega

/-! ## 5. Differential pins against `aarch64-linux-gnu-as` (the gas anchor)

These pin the emitted 32-bit word to the exact little-endian bytes
`aarch64-linux-gnu-as` produces for the ChaCha 4-way quarter-round NEON
mnemonics. The bytes are little-endian, so e.g. `add v0.4s, v1.4s, v2.4s`
(gas word `0x4ea28420`) is `[0x20,0x84,0xa2,0x4e]`. Together with
`SailNeonDecoder`'s `decode (encode i) = i`, the encoder is both gas-matched and
decode-round-trip-proved. -/

/-- A helper allocation pinning `a b c d` (and a temp `t`) to `v0 v1 v2 v3 v4`. -/
def qrAlloc : VAlloc :=
  [("a","v0"), ("b","v1"), ("c","v2"), ("d","v3"), ("t","v4")]

/-- `add v0.4s, v1.4s, v2.4s` — gas word `0x4ea28420`, little-endian `20 84 a2 4e`. -/
example : encodeNInst [("d","v0"),("a","v1"),("b","v2")] (.add "d" "a" "b")
    = [0x20, 0x84, 0xa2, 0x4e].map (BitVec.ofNat 8) := by native_decide

/-- `sub v0.4s, v1.4s, v2.4s` — gas word `0x6ea28420`, little-endian `20 84 a2 6e`. -/
example : encodeNInst [("d","v0"),("a","v1"),("b","v2")] (.sub "d" "a" "b")
    = [0x20, 0x84, 0xa2, 0x6e].map (BitVec.ofNat 8) := by native_decide

/-- `mul v0.4s, v1.4s, v2.4s` — gas word `0x4ea29c20`, little-endian `20 9c a2 4e`. -/
example : encodeNInst [("d","v0"),("a","v1"),("b","v2")] (.mul "d" "a" "b")
    = [0x20, 0x9c, 0xa2, 0x4e].map (BitVec.ofNat 8) := by native_decide

/-- `and v0.16b, v1.16b, v2.16b` — gas word `0x4e221c20`, little-endian `20 1c 22 4e`. -/
example : encodeNInst [("d","v0"),("a","v1"),("b","v2")] (.and "d" "a" "b")
    = [0x20, 0x1c, 0x22, 0x4e].map (BitVec.ofNat 8) := by native_decide

/-- `orr v0.16b, v1.16b, v2.16b` — gas word `0x4ea21c20`, little-endian `20 1c a2 4e`. -/
example : encodeNInst [("d","v0"),("a","v1"),("b","v2")] (.orr "d" "a" "b")
    = [0x20, 0x1c, 0xa2, 0x4e].map (BitVec.ofNat 8) := by native_decide

/-- `eor v0.16b, v1.16b, v2.16b` — gas word `0x6e221c20`, little-endian `20 1c 22 6e`. -/
example : encodeNInst [("d","v0"),("a","v1"),("b","v2")] (.eor "d" "a" "b")
    = [0x20, 0x1c, 0x22, 0x6e].map (BitVec.ofNat 8) := by native_decide

/-- `shl v0.4s, v1.4s, #7` — gas word `0x4f275420`, little-endian `20 54 27 4f`. -/
example : encodeNInst [("d","v0"),("a","v1")] (.shl "d" "a" 7)
    = [0x20, 0x54, 0x27, 0x4f].map (BitVec.ofNat 8) := by native_decide

/-- `ushr v0.4s, v1.4s, #25` — gas word `0x6f270420`, little-endian `20 04 27 6f`. -/
example : encodeNInst [("d","v0"),("a","v1")] (.ushr "d" "a" 25)
    = [0x20, 0x04, 0x27, 0x6f].map (BitVec.ofNat 8) := by native_decide

/-- `shl v5.4s, v3.4s, #12` — gas word `0x4f2c5465`, little-endian `65 54 2c 4f`. -/
example : encodeNInst [("d","v5"),("a","v3")] (.shl "d" "a" 12)
    = [0x65, 0x54, 0x2c, 0x4f].map (BitVec.ofNat 8) := by native_decide

/-- `sqdmulh v0.8h, v1.8h, v2.8h` — gas word `0x4e62b420`, little-endian
    `20 b4 62 4e` (the ML-KEM NTT signed high-mul, #4). -/
example : encodeNInst8x16 [("d","v0"),("a","v1"),("b","v2")] (.mulhs "d" "a" "b")
    = [0x20, 0xb4, 0x62, 0x4e].map (BitVec.ofNat 8) := by native_decide

/-- `ushr v6.4s, v3.4s, #20` — gas word `0x6f2c0466`, little-endian `66 04 2c 6f`. -/
example : encodeNInst [("d","v6"),("a","v3")] (.ushr "d" "a" 20)
    = [0x66, 0x04, 0x2c, 0x6f].map (BitVec.ofNat 8) := by native_decide

/-- `mov v3.16b, v5.16b` (= `ORR v3.16b, v5.16b, v5.16b`) — gas word `0x4ea51ca3`,
    little-endian `a3 1c a5 4e`. -/
example : encodeNInst [("d","v3"),("s","v5")] (.mov "d" "s")
    = [0xa3, 0x1c, 0xa5, 0x4e].map (BitVec.ofNat 8) := by native_decide

end CatCrypt.Crypto.SecureCompilation.ARMBackend.Neon.NeonEncoder
