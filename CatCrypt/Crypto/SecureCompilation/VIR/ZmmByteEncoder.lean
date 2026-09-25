/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.YmmByteEncoder
public import CatCrypt.Crypto.SecureCompilation.VIR.YmmByteEncoder
public meta import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint

/-!
# EVEX.512 machine bytes of the `%zmm` instructions of `VpackZmmAsmPrint`

`encodeZmmPackInst bop d a b` is the x86-64 machine encoding of the line
`VpackZmmAsmPrint.renderVpackZmmInstr` prints for a `JasminOp.vpackZMM bop`
binding `d := bop-packed(a, b)`, namely `mnem %zmmB, %zmmA, %zmmD`, and
`encodeZmmPermInst name d ctrl src` is the encoding of the permute line
`name %zmmCtrl, %zmmSrc, %zmmD` that the printer emits for the `extCall` leaves
`vpermq`, `vpermt2q` and `vpermpd`. In both, the last AT&T operand is
`ModRM.reg`, the middle one is `EVEX.vvvv` and the first one is `ModRM.rm`.

Every instruction is register-only and of the form `EVEX.512.66.0F.W1 op /r`
or `EVEX.512.66.0F38.W1 op /r`, with no masking (`aaa = 000`, `z = 0`) and no
broadcast or rounding (`b = 0`). EVEX addresses 32 vector registers: bit 3 of
`ModRM.reg` is `R`, bit 4 is `R'`; bit 3 of `ModRM.rm` is `B`, bit 4 is `X`; bit 4
of `vvvv` is `V'`. All of these fields are stored inverted.

A register numbered 32 or higher, and a permute leaf name other than the three
above, encode as `UD2` (`0F 0B`).

## Main results

* `evexP0`, `evexP1`, `evexP2`, `encEvexRR`: the EVEX prefix bytes and the
  register-direct EVEX instruction.
* `encodeZmmPackInst`: the encoding of every `vpackZMM` op the printer names.
* `encodeZmmPermInst`: the encoding of the printer's three permute leaves.
* `encodeZmm*_eq_gas`: per-family pins against GNU as 2.42 (`as --64` +
  `objdump -d`), over register triples that put a register numbered 16 or higher
  in each of `ModRM.reg`, `vvvv` and `ModRM.rm`.
* `renderVpackZmmInstr_phys`: on physical register names the printer's line is
  `mnem rb, ra, rd`.
* `renderVpackZmmInstr_vpaddq_bytes`: the printer's line
  `vpaddq %zmm26, %zmm5, %zmm17` and the encoder's bytes for
  `(d, a, b) = (17, 5, 26)` are the text and the bytes of one gas instruction.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ZmmByteEncoder

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CryptoExt (bit cbit modRMReg)
open CatCrypt.Crypto.SecureCompilation.VIR.VsimdByteEncoder (encUd2)
open CatCrypt.Crypto.SecureCompilation.VIR.YmmByteEncoder (ymmBytes)
open CatCrypt.Crypto.SecureCompilation.VIR.VpackZmmAsmPrint
  (renderVpackZmmInstr zmmReg JasminBinOp.zmmAttMnemonic)

/-! ## 1. The EVEX prefix -/

/-- EVEX payload byte `P0 = R̄ X̄ B̄ R̄' 0 m m m`, for a `ModRM.reg` register
    `r` and a register-direct `ModRM.rm` register `rm`: `R`/`R'` are bits 3/4 of
    `r`, `B`/`X` are bits 3/4 of `rm`, all stored inverted; `mm` is the opcode
    map (`1` = `0F`, `2` = `0F38`, `3` = `0F3A`). -/
def evexP0 (r rm mm : Nat) : Nat :=
  cbit (bit r 3) * 128 + cbit (bit rm 4) * 64 + cbit (bit rm 3) * 32
    + cbit (bit r 4) * 16 + (mm &&& 7)

/-- EVEX payload byte `P1 = W v̄3 v̄2 v̄1 v̄0 1 p p`: the operand-size bit `w`,
    the low four bits of the `vvvv` register `v` inverted, and the implied
    prefix `pp` (`1` = `66`, `2` = `F3`, `3` = `F2`). -/
def evexP1 (w v pp : Nat) : Nat :=
  (w &&& 1) * 128 + (15 - (v &&& 15)) * 8 + 4 + (pp &&& 3)

/-- EVEX payload byte `P2 = z L' L b V̄' a a a`: zeroing bit `z`, vector length
    `ll` (`0` = 128, `1` = 256, `2` = 512 bits), broadcast/rounding bit `b`, bit 4
    of the `vvvv` register `v` inverted, and the opmask register `aaa`. -/
def evexP2 (z ll b v aaa : Nat) : Nat :=
  (z &&& 1) * 128 + (ll &&& 3) * 32 + (b &&& 1) * 16 + cbit (bit v 4) * 8 + (aaa &&& 7)

/-- The register-direct EVEX instruction `62 P0 P1 P2 op ModRM` with map `mm`,
    implied prefix `pp`, `W = w`, vector length `ll`, `ModRM.reg = reg`,
    `vvvv = v`, `ModRM.rm = rm`, no masking, no zeroing and `b = 0`. -/
def encEvexRR (mm pp w ll op reg v rm : Nat) : List (BitVec 8) :=
  [0x62, evexP0 reg rm mm, evexP1 w v pp, evexP2 0 ll 0 v 0, op, modRMReg reg rm].map
    (BitVec.ofNat 8)

/-- The `EVEX.512.66.<map>.W1 op /r` instruction with `ModRM.reg = reg`,
    `vvvv = v` and `ModRM.rm = rm`. -/
def encEvex512W1 (mm op reg v rm : Nat) : List (BitVec 8) :=
  encEvexRR mm 1 1 2 op reg v rm

/-- The three registers of an instruction are EVEX-addressable: each is below 32. -/
def zmmRegsOk (d a b : Nat) : Bool := d < 32 && a < 32 && b < 32

/-! ## 2. The `vpackZMM` ops -/

/-- The opcode map and opcode byte of the `EVEX.512.66.W1` form of the
    mnemonic `JasminBinOp.zmmAttMnemonic bop`. -/
def zmmPackOpcode : JasminBinOp → Nat × Nat
  | .add  => (1, 0xd4)   -- vpaddq
  | .sub  => (1, 0xfb)   -- vpsubq
  | .mul  => (2, 0x40)   -- vpmullq
  | .and  => (1, 0xdb)   -- vpandq
  | .or   => (1, 0xeb)   -- vporq
  | .xor  => (1, 0xef)   -- vpxorq
  | .shl  => (2, 0x47)   -- vpsllvq
  | .shr  => (2, 0x45)   -- vpsrlvq
  | .andn => (1, 0xdf)   -- vpandnq

/-- The machine encoding of the printed line `mnem %zmmB, %zmmA, %zmmD` of the
    binding `d := bop-packed(a, b)`: `d` is `ModRM.reg`, `a` is `vvvv` and `b` is
    `ModRM.rm`. A register numbered 32 or higher gives `UD2`. -/
def encodeZmmPackInst (bop : JasminBinOp) (d a b : Nat) : List (BitVec 8) :=
  if zmmRegsOk d a b then
    encEvex512W1 (zmmPackOpcode bop).1 (zmmPackOpcode bop).2 d a b
  else encUd2

/-! ## 3. The permute leaves -/

/-- The `EVEX.512.66.0F38.W1` opcode byte of a permute leaf name: `vpermq` is
    `36`, `vpermpd` is `16`, `vpermt2q` is `7E`; any other name has none. -/
def zmmPermOpcode (name : String) : Option Nat :=
  if name == "vpermq" then some 0x36
  else if name == "vpermpd" then some 0x16
  else if name == "vpermt2q" then some 0x7e
  else none

/-- The machine encoding of the printed permute line
    `name %zmmCtrl, %zmmSrc, %zmmD`: `d` is `ModRM.reg`, `src` is `vvvv` and
    `ctrl` is `ModRM.rm`. The index vector of all three instructions is `vvvv`,
    so the instruction selects lanes of `ctrl` (and, for `vpermt2q`, of the
    previous `d`) by the indices in `src`. An unknown leaf name or a register
    numbered 32 or higher gives `UD2`. -/
def encodeZmmPermInst (name : String) (d ctrl src : Nat) : List (BitVec 8) :=
  match zmmPermOpcode name with
  | some op => if zmmRegsOk d src ctrl then encEvex512W1 2 op d src ctrl else encUd2
  | none => encUd2

/-! ## 4. Gas pins

Each theorem is the encoder's output against `objdump -d` of the object GNU as
2.42 (`as --64`) assembles from the AT&T lines in its docstring. -/

/-- The `66 0F` ops against the gas lines `vpaddq %zmm7, %zmm5, %zmm3`,
    `vpaddq %zmm7, %zmm5, %zmm17`, `vpaddq %zmm7, %zmm21, %zmm3`,
    `vpaddq %zmm26, %zmm5, %zmm3`, `vpaddq %zmm10, %zmm9, %zmm12`,
    `vpaddq %zmm29, %zmm30, %zmm31`, `vpaddq %zmm26, %zmm5, %zmm17`,
    `vpsubq|vpandq|vporq|vpxorq|vpandnq %zmm7, %zmm5, %zmm3` and
    `vpxorq %zmm29, %zmm30, %zmm31`. -/
theorem encodeZmmPack_map0F_eq_gas :
    encodeZmmPackInst .add 3 5 7 = ymmBytes [0x62, 0xf1, 0xd5, 0x48, 0xd4, 0xdf] ∧
    encodeZmmPackInst .add 17 5 7 = ymmBytes [0x62, 0xe1, 0xd5, 0x48, 0xd4, 0xcf] ∧
    encodeZmmPackInst .add 3 21 7 = ymmBytes [0x62, 0xf1, 0xd5, 0x40, 0xd4, 0xdf] ∧
    encodeZmmPackInst .add 3 5 26 = ymmBytes [0x62, 0x91, 0xd5, 0x48, 0xd4, 0xda] ∧
    encodeZmmPackInst .add 12 9 10 = ymmBytes [0x62, 0x51, 0xb5, 0x48, 0xd4, 0xe2] ∧
    encodeZmmPackInst .add 31 30 29 = ymmBytes [0x62, 0x01, 0x8d, 0x40, 0xd4, 0xfd] ∧
    encodeZmmPackInst .add 17 5 26 = ymmBytes [0x62, 0x81, 0xd5, 0x48, 0xd4, 0xca] ∧
    encodeZmmPackInst .sub 3 5 7 = ymmBytes [0x62, 0xf1, 0xd5, 0x48, 0xfb, 0xdf] ∧
    encodeZmmPackInst .and 3 5 7 = ymmBytes [0x62, 0xf1, 0xd5, 0x48, 0xdb, 0xdf] ∧
    encodeZmmPackInst .or 3 5 7 = ymmBytes [0x62, 0xf1, 0xd5, 0x48, 0xeb, 0xdf] ∧
    encodeZmmPackInst .xor 3 5 7 = ymmBytes [0x62, 0xf1, 0xd5, 0x48, 0xef, 0xdf] ∧
    encodeZmmPackInst .andn 3 5 7 = ymmBytes [0x62, 0xf1, 0xd5, 0x48, 0xdf, 0xdf] ∧
    encodeZmmPackInst .xor 31 30 29 = ymmBytes [0x62, 0x01, 0x8d, 0x40, 0xef, 0xfd] := by
  decide

/-- The `66 0F38` ops against the gas lines `vpmullq %zmm7, %zmm5, %zmm3`,
    `vpmullq %zmm7, %zmm5, %zmm17`, `vpmullq %zmm7, %zmm21, %zmm3`,
    `vpmullq %zmm26, %zmm5, %zmm3`, `vpmullq %zmm10, %zmm9, %zmm12`,
    `vpmullq %zmm29, %zmm30, %zmm31`, `vpsllvq|vpsrlvq %zmm7, %zmm5, %zmm3` and
    `vpsrlvq %zmm29, %zmm30, %zmm31`. -/
theorem encodeZmmPack_map0F38_eq_gas :
    encodeZmmPackInst .mul 3 5 7 = ymmBytes [0x62, 0xf2, 0xd5, 0x48, 0x40, 0xdf] ∧
    encodeZmmPackInst .mul 17 5 7 = ymmBytes [0x62, 0xe2, 0xd5, 0x48, 0x40, 0xcf] ∧
    encodeZmmPackInst .mul 3 21 7 = ymmBytes [0x62, 0xf2, 0xd5, 0x40, 0x40, 0xdf] ∧
    encodeZmmPackInst .mul 3 5 26 = ymmBytes [0x62, 0x92, 0xd5, 0x48, 0x40, 0xda] ∧
    encodeZmmPackInst .mul 12 9 10 = ymmBytes [0x62, 0x52, 0xb5, 0x48, 0x40, 0xe2] ∧
    encodeZmmPackInst .mul 31 30 29 = ymmBytes [0x62, 0x02, 0x8d, 0x40, 0x40, 0xfd] ∧
    encodeZmmPackInst .shl 3 5 7 = ymmBytes [0x62, 0xf2, 0xd5, 0x48, 0x47, 0xdf] ∧
    encodeZmmPackInst .shr 3 5 7 = ymmBytes [0x62, 0xf2, 0xd5, 0x48, 0x45, 0xdf] ∧
    encodeZmmPackInst .shr 31 30 29 = ymmBytes [0x62, 0x02, 0x8d, 0x40, 0x45, 0xfd] := by
  decide

/-- The permute leaves against the gas lines
    `vpermq|vpermpd|vpermt2q %zmm7, %zmm5, %zmm3`, `vpermq %zmm30, %zmm0, %zmm1`,
    `vpermt2q %zmm26, %zmm21, %zmm17` and `vpermpd %zmm10, %zmm9, %zmm12`. -/
theorem encodeZmmPerm_eq_gas :
    encodeZmmPermInst "vpermq" 3 7 5 = ymmBytes [0x62, 0xf2, 0xd5, 0x48, 0x36, 0xdf] ∧
    encodeZmmPermInst "vpermpd" 3 7 5 = ymmBytes [0x62, 0xf2, 0xd5, 0x48, 0x16, 0xdf] ∧
    encodeZmmPermInst "vpermt2q" 3 7 5 = ymmBytes [0x62, 0xf2, 0xd5, 0x48, 0x7e, 0xdf] ∧
    encodeZmmPermInst "vpermq" 1 30 0 = ymmBytes [0x62, 0x92, 0xfd, 0x48, 0x36, 0xce] ∧
    encodeZmmPermInst "vpermt2q" 17 26 21 =
      ymmBytes [0x62, 0x82, 0xd5, 0x40, 0x7e, 0xca] ∧
    encodeZmmPermInst "vpermpd" 12 10 9 = ymmBytes [0x62, 0x52, 0xb5, 0x48, 0x16, 0xe2] := by
  decide

/-- A register numbered 32 or higher in any position, and a leaf name outside
    the three permutes, encode as `UD2` (`0F 0B`). -/
theorem encodeZmm_ud2 :
    encodeZmmPackInst .add 32 5 7 = ymmBytes [0x0f, 0x0b] ∧
    encodeZmmPackInst .add 3 32 7 = ymmBytes [0x0f, 0x0b] ∧
    encodeZmmPackInst .add 3 5 40 = ymmBytes [0x0f, 0x0b] ∧
    encodeZmmPermInst "vpermq" 3 33 5 = ymmBytes [0x0f, 0x0b] ∧
    encodeZmmPermInst "vpshufb" 3 7 5 = ymmBytes [0x0f, 0x0b] := by
  decide

/-! ## 5. Printer and encoder agree on operand order -/

/-- On names that are physical registers (`%`-prefixed), the printer's line for
    `dst := bop-packed(a, b)` is `mnem b, a, dst`, whatever the allocation. -/
theorem renderVpackZmmInstr_phys (alloc : List (String × String)) (bop : JasminBinOp)
    (d a b : String) (hd : d.startsWith "%" = true) (ha : a.startsWith "%" = true)
    (hb : b.startsWith "%" = true) :
    renderVpackZmmInstr alloc bop d a b
      = "\t" ++ JasminBinOp.zmmAttMnemonic bop ++ " " ++ b ++ ", " ++ a ++ ", " ++ d := by
  simp [renderVpackZmmInstr, zmmReg, hd, ha, hb]

/-- The printer renders `d := add-packed(a, b)` with `d`, `a`, `b` allocated to
    `%zmm17`, `%zmm5`, `%zmm26` as the line `vpaddq %zmm26, %zmm5, %zmm17`, and the
    encoder's bytes for `(d, a, b) = (17, 5, 26)` are `62 81 d5 48 d4 ca`, the bytes
    GNU as 2.42 assembles from that line. -/
theorem renderVpackZmmInstr_vpaddq_bytes :
    renderVpackZmmInstr [("d", "%zmm17"), ("a", "%zmm5"), ("b", "%zmm26")] .add "d" "a" "b"
        = "\tvpaddq %zmm26, %zmm5, %zmm17" ∧
      encodeZmmPackInst .add 17 5 26 = ymmBytes [0x62, 0x81, 0xd5, 0x48, 0xd4, 0xca] := by
  refine ⟨?_, by decide⟩
  simp (config := { decide := true }) [renderVpackZmmInstr, zmmReg, List.lookup]

end CatCrypt.Crypto.SecureCompilation.VIR.ZmmByteEncoder

end
