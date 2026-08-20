/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RvvAsmPrinter
import CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder

/-!
# A verified machine-code byte encoder for the packed-u32 RVV `VInst` (#549 RVV residual)

`ARMBackend/NeonEncoder.lean` encodes the AArch64 NEON `NInst` packed subset; this
module is its **RISC-V RVV** counterpart, encoding the OPIVV/OPIVI subset the owned
RVV backend emits — `vadd.vv`/`vand.vv`/`vor.vv`/`vxor.vv` (OPIVV, funct3 `0b000`),
`vsll.vi`/`vsrl.vi` (OPIVI, funct3 `0b011`, 5-bit `simm`), and `vmv.v.v` (OPIVV
MOVETYPEV form) — all opcode `0b1010111 = 0x57` (OP-V).

The `funct6`/`funct3`/`vm`/opcode constants are exactly the sail-riscv `encdec`
clauses (`model/extensions/V/vext_arith_insts.sail`):

```
VVTYPE(funct6,vm,vs2,vs1,vd)  <-> funct6 @ vm @ vs2 @ vs1 @ 0b000 @ vd @ 0b1010111
VITYPE(funct6,vm,vs2,simm,vd) <-> funct6 @ vm @ vs2 @ simm @ 0b011 @ vd @ 0b1010111
MOVETYPEV(vs1,vd)             <-> 0b010111 @ 0b1 @ 0b00000 @ vs1 @ 0b000 @ vd @ 0b1010111
```
with `vm = 1` (unmasked) on the masked arithmetic forms, and the funct6 values
`VV_VADD=0b000000`, `VV_VAND=0b001001`, `VV_VOR=0b001010`, `VV_VXOR=0b001011`,
`VI_VSLL=0b100101`, `VI_VSRL=0b101000` (`vmv.v.v` is the special OPIVV funct6
`0b010111`, `vm=1`, `vs2=0`).

## The `vsetvli` / `vle32.v` / `vse32.v` prelude left to the assembler

The fixed-config prelude (`li`, `vsetvli`, `mv`, `addi`, `vle32.v`, `vse32.v`) is
**not** byte-encoded here: `li` is the variable-length pseudo-op (the same as the
scalar `RInst64.li`), and the `vsetvli`/`vle`/`vse` are the trusted lane-config /
memory scaffolding (outside the verified packed-ALU body), the RVV analogue of the
prologue. `encodeWord` returns `none` for nothing here — the verified subset is
exactly the OPIVV/OPIVI ALU forms; the byte-diff (`bench/riscv_compare`,
`qr-rvv-bytes-diff`) is run on the **packed-ALU body** (the verified `VInst`
block), with the prelude/epilogue factored out, exactly as the NEON QR byte-diff
spans the ASIMD body.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RISCVBackend.Rvv.RvvEncoder

open CatCrypt.Crypto.SecureCompilation.RISCVBackend.Rvv
open CatCrypt.Crypto.SecureCompilation.RISCVBackend.RiscvEncoder (wordLE reg5)

/-! ## 1. Register-name → 5-bit number (`encdec_vreg`)

The RVV `vN` register name → 5-bit number (`v0=0 … v31=31`). A name not in the
pool reads as `0` (never produced by `allocV` on a fitting block; an overflow
yields the `<UNALLOCATED:_>` sentinel, encoded as `0`). -/
def vNum (r : String) : Nat :=
  (List.range 32).findIdx? (fun i => r = "v" ++ toString i) |>.getD 0

/-- The 5-bit register field for a `vN` register name. -/
def vreg5 (r : String) : BitVec 5 := BitVec.ofNat 5 (vNum r)

/-! ## 2. The fixed-field OP-V word builders (sail `encdec` clauses)

Each builder is the **bit-concatenation** of the sail bitfields read MSB-first —
exactly the sail `@` operator (`BitVec.append`). The OP-V word is
`funct6[6] @ vm[1] @ vs2[5] @ vs1/simm[5] @ funct3[3] @ vd[5] @ opcode[7]`
(6+1+5+5+3+5+7 = 32). Using `++` (append) makes each field's inverse slice exact,
so `SailRvvDecoder.rvvDecode` recovers the operands with no side condition. -/

/-- An OP-V word: the sail concat `funct6 @ vm @ vs2 @ vs1 @ funct3 @ vd @ opcode`,
    as a `BitVec 32`. The fields are width-typed `BitVec`s (the sail `@` operator
    is `BitVec.append`), so the round-trip decoder slices them back exactly. -/
def encV (funct6 : BitVec 6) (vm : BitVec 1) (vs2 vs1 : BitVec 5) (funct3 : BitVec 3)
    (vd : BitVec 5) (opcode : BitVec 7) : BitVec 32 :=
  (funct6 ++ vm ++ vs2 ++ vs1 ++ funct3 ++ vd ++ opcode).cast rfl

/-- The OP-V opcode `0b1010111 = 0x57`. -/
def opV : BitVec 7 := 0x57

/-! ## 3. The per-`VInst` word encoder (sail constants quoted inline)

The OPIVV arithmetic forms use `funct3 = 0b000`, `vm = 1` (unmasked); the OPIVI
shift forms use `funct3 = 0b011` with the 5-bit shift count in the `vs1`/`simm`
slot. `vmv.v.v` is the OPIVV `MOVETYPEV` form (`funct6 = 0b010111`, `vm = 1`,
`vs2 = 0`). -/

/-- Encode one `VInst` to its 32-bit RV64 RVV instruction word (the value objdump
    prints). The arithmetic forms are unmasked (`vm = 1`); the shifts place the
    5-bit immediate in the `simm` slot. -/
def encodeWord : VInst → BitVec 32
  | .vadd d a b => encV 0b000000 1 (vreg5 a) (vreg5 b) 0b000 (vreg5 d) opV
  | .vand d a b => encV 0b001001 1 (vreg5 a) (vreg5 b) 0b000 (vreg5 d) opV
  | .vor  d a b => encV 0b001010 1 (vreg5 a) (vreg5 b) 0b000 (vreg5 d) opV
  | .vxor d a b => encV 0b001011 1 (vreg5 a) (vreg5 b) 0b000 (vreg5 d) opV
  | .vsll d a m => encV 0b100101 1 (vreg5 a) (BitVec.ofNat 5 m) 0b011 (vreg5 d) opV
  | .vsrl d a m => encV 0b101000 1 (vreg5 a) (BitVec.ofNat 5 m) 0b011 (vreg5 d) opV
  | .vmv  d s   => encV 0b010111 1 0 (vreg5 s) 0b000 (vreg5 d) opV

/-- Encode one `VInst` to its 4 little-endian machine-code bytes. -/
def encodeVInst (i : VInst) : List (BitVec 8) := wordLE (encodeWord i)

/-- Encode one 8 × i16 RVV instruction (`VInst8x16`, the ML-KEM NTT op) to its
    32-bit word. `vmulh.vv` is OPMVV (`funct3 = 0b010`), `funct6 = 0b100111`
    (`MULH`), unmasked (`vm = 1`); the active lane shape (`SEW = 16, VL = 8`) is
    selected by the `vsetvli e16,m1` prelude, not encoded in this word. -/
def encodeWord8x16 : VInst8x16 → BitVec 32
  | .vmulh d a b => encV 0b100111 1 (vreg5 a) (vreg5 b) 0b010 (vreg5 d) opV

/-- Encode one `VInst8x16` to its 4 little-endian machine-code bytes. -/
def encodeVInst8x16 (i : VInst8x16) : List (BitVec 8) := wordLE (encodeWord8x16 i)

/-- Encode a whole block: concatenate the per-instruction LE byte encodings — the
    contiguous `.text` machine-code stream of the packed-ALU body. -/
def encodeVBlock (block : List VInst) : List (BitVec 8) :=
  block.flatMap encodeVInst

/-! ## 3b. The RVV config / unit-stride memory scaffolding encoders (`vsetvli`,
        `vle32.v`, `vse32.v`)

For a *whole-function byte-direct* RVV `.o` (no `as`/gas on the artifact path)
the lane-config + load/store prelude must be byte-produced by Lean too. These are
the RVV analogue of the scalar ABI scaffolding in `RiscvElfObject`; each is the
sail-riscv `encdec` clause, pinned to `riscv64-linux-gnu-as -march=rv64gcv` in §5.

* **`vsetvli rd, rs1, vtypei`** (sail `VSETTYPE`): opcode `0x57`, funct3 `0b111`,
  `zimm11[31:20] @ rs1[19:15] @ 0b111[14:12] @ rd[11:7] @ 0b1010111`. The `vtypei`
  field for `e32, m1, ta, ma` is `0x0d0` (`vlmul=000`, `vsew=010`, `vta=1`,
  `vma=1`).
* **`vle32.v vd, (rs1)`** (sail `VLUNITTYPE`, unit-stride load): opcode `0x07`,
  width `0b110` (32-bit) in funct3, `vm=1`, `mop=00`, `nf=000`, `lumop=00000` →
  the fixed top field `0x020`. Word = `0x02000000 | rs1<<15 | 0b110<<12 | vd<<7 | 0x07`.
* **`vse32.v vs3, (rs1)`** (sail `VSUNITTYPE`, unit-stride store): opcode `0x27`,
  same fixed top field; the stored vector is in the `vd` slot (`vs3`).
  Word = `0x02000000 | rs1<<15 | 0b110<<12 | vs3<<7 | 0x27`. -/

/-- The `vtypei` zimm for `e32, m1, ta, ma` (the fixed config the model selects). -/
def vtypeE32M1TaMa : BitVec 12 := 0x0d0

/-- The `vtypei` zimm for `e16, m1, ta, ma` (the ML-KEM NTT config, #4): `vlmul=000`,
    `vsew=001`, `vta=1`, `vma=1` ⇒ `0x0c8`. -/
def vtypeE16M1TaMa : BitVec 12 := 0x0c8

/-- `vsetvli rd, rs1, e16,m1,ta,ma` — the ML-KEM NTT lane-config prelude. -/
def encVsetvliE16 (rd rs1 : String) : BitVec 32 :=
  (vtypeE16M1TaMa ++ reg5 rs1 ++ (0b111 : BitVec 3) ++ reg5 rd ++ opV).cast rfl

/-- `vsetvli rd, rs1, e32,m1,ta,ma` — VSETTYPE word
    `vtypei[12] @ rs1[5] @ 0b111 @ rd[5] @ 0b1010111`. `rd`/`rs1` are *scalar*
    x-register names (reuse `RiscvEncoder.reg5`). -/
def encVsetvli (rd rs1 : String) : BitVec 32 :=
  (vtypeE32M1TaMa ++ reg5 rs1 ++ (0b111 : BitVec 3) ++ reg5 rd ++ opV).cast rfl

/-- The fixed top field of the unit-stride `e32` load/store (`nf=0,mew=0,mop=0,
    vm=1,lumop/sumop=0`): bits[31:20] = `0b0000_0010_0000` = `0x020`. -/
def vMemTop : BitVec 12 := 0x020

/-- `vle32.v vd, (rs1)` — unit-stride 32-bit vector load. `rs1` is a scalar
    x-register base; `vd` is the destination vector register. -/
def encVle32 (vd rs1 : String) : BitVec 32 :=
  (vMemTop ++ reg5 rs1 ++ (0b110 : BitVec 3) ++ vreg5 vd ++ (0x07 : BitVec 7)).cast rfl

/-- `vse32.v vs3, (rs1)` — unit-stride 32-bit vector store. `rs1` is a scalar
    x-register base; `vs3` (in the `vd` slot) is the source vector register. -/
def encVse32 (vs3 rs1 : String) : BitVec 32 :=
  (vMemTop ++ reg5 rs1 ++ (0b110 : BitVec 3) ++ vreg5 vs3 ++ (0x27 : BitVec 7)).cast rfl

/-! ## 4. Structural well-formedness (the unconditional half of the trust story)

Every `encodeVInst` output is exactly one 4-byte RV64 word (fixed instruction
width), proved for all inputs. -/

/-- Every `VInst` encodes to exactly 4 bytes (RV64 base instruction width). -/
@[simp] theorem encodeVInst_length (i : VInst) : (encodeVInst i).length = 4 := by
  cases i <;> simp [encodeVInst, wordLE]

/-- `encodeVBlock` produces `4 * |block|` bytes. -/
theorem encodeVBlock_length (block : List VInst) :
    (encodeVBlock block).length = 4 * block.length := by
  induction block with
  | nil => rfl
  | cons i is ih =>
      simp only [encodeVBlock, List.flatMap_cons, List.length_append,
        encodeVInst_length] at *
      simp only [List.length_cons]; omega

/-! ## 5. Differential-validation pins against `riscv64-linux-gnu-as`

The encoder's instruction words pinned to the exact 32-bit words
`riscv64-linux-gnu-as -march=rv64gcv` produces for the same mnemonic (the
`objdump -d` value, the bench `riscv_compare` oracle). The `decode(encode)=i`
round-trip in `SailRvvDecoder.lean` upgrades these gas pins to a proof against the
official sail-riscv RVV `encdec` clauses. -/

-- `vadd.vv v4, v0, v1` → `as`/objdump word `0x02008257`.
#guard encodeWord (.vadd "v4" "v0" "v1") == 0x02008257
-- `vxor.vv v4, v0, v1` → `0x2e008257`.
#guard encodeWord (.vxor "v4" "v0" "v1") == 0x2e008257
-- `vor.vv v4, v0, v1` → `0x2a008257`.
#guard encodeWord (.vor "v4" "v0" "v1") == 0x2a008257
-- `vand.vv v4, v0, v1` → `0x26008257`.
#guard encodeWord (.vand "v4" "v0" "v1") == 0x26008257
-- `vsll.vi v4, v0, 7` → `0x9603b257`.
#guard encodeWord (.vsll "v4" "v0" 7) == 0x9603b257
-- `vsrl.vi v4, v0, 25` → `0xa20cb257`.
#guard encodeWord (.vsrl "v4" "v0" 25) == 0xa20cb257
-- `vmv.v.v v4, v0` → `0x5e000257`.
#guard encodeWord (.vmv "v4" "v0") == 0x5e000257
-- `vmulh.vv v4, v0, v1` → `0x9e00a257` (OPMVV `funct3=010`, `funct6=100111`;
-- the ML-KEM NTT signed high-mul, #4).
#guard encodeWord8x16 (.vmulh "v4" "v0" "v1") == 0x9e00a257

-- The first little-endian byte of `vadd.vv v4,v0,v1` is `0x57` (the OP-V opcode
-- byte that leads the LE word in `.text`).
#guard (encodeVInst (.vadd "v4" "v0" "v1")).head? == some 0x57

/-! ### Config / memory scaffolding pins (`vsetvli`/`vle32.v`/`vse32.v`)

The three RVV prelude/epilogue scaffolding words, pinned to the exact
`riscv64-linux-gnu-as -march=rv64gcv` objdump value. -/

-- `vsetvli t0, t0, e32,m1,ta,ma` → `0x0d02f2d7`.
#guard encVsetvli "t0" "t0" == 0x0d02f2d7
-- `vsetvli t1, t0, e32,m1,ta,ma` → `0x0d02f357`.
#guard encVsetvli "t1" "t0" == 0x0d02f357
-- `vsetvli t0, t0, e16,m1,ta,ma` → `0x0c82f2d7` (the ML-KEM NTT lane config, #4).
#guard encVsetvliE16 "t0" "t0" == 0x0c82f2d7
-- `vle32.v v0, (t1)` → `0x02036007`.
#guard encVle32 "v0" "t1" == 0x02036007
-- `vle32.v v3, (t1)` → `0x02036187`.
#guard encVle32 "v3" "t1" == 0x02036187
-- `vle32.v v0, (a0)` → `0x02056007`.
#guard encVle32 "v0" "a0" == 0x02056007
-- `vse32.v v0, (t1)` → `0x02036027`.
#guard encVse32 "v0" "t1" == 0x02036027
-- `vse32.v v3, (t1)` → `0x020361a7`.
#guard encVse32 "v3" "t1" == 0x020361a7
-- `vse32.v v2, (t1)` → `0x02036127`.
#guard encVse32 "v2" "t1" == 0x02036127

end CatCrypt.Crypto.SecureCompilation.RISCVBackend.Rvv.RvvEncoder
