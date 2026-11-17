/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# x86 vector instructions over a lane view of the register file

`VInstr` is the alphabet of x86 vector instructions of the machine model: the VEX register
forms at `VEX.L = 0` (XMM, 128 bits) and `VEX.L = 1` (YMM, 256 bits), the `VMOVDQU` and
`VMOVDQA` loads at `base + disp` and `base + 8·index + disp`, the `VMOVDQA` register move,
`VZEROUPPER`, and the legacy-encoded SHA-NI register forms.

## Lane view

The machine state keeps one register file `String → BitVec 64`. Vector register `r < 16` is
the four names `laneName r k = "%ymmR.K"`, `k < 4`, lane `k` holding bits `64k` to `64k + 63`
of `%ymmR`. `readX` and `readY` assemble the XMM and YMM values from the lanes. The semantics
of an instruction is the list of lane writes `VInstr.writes rd ld v` over a register-read
function `rd` and a word-read function `ld base off` (the word at the address held in `base`
plus the byte offset `off`), and `VInstr.exec` is the register file after those writes. A
VEX.128 write sets lanes 2 and 3 to zero; a legacy SHA-NI write sets lanes 0 and 1 and keeps
lanes 2 and 3; a VEX.256 write sets all four. No vector instruction reads or writes a name
other than a lane name, or the flags, and none writes memory.

## Denotations

`VOp.denote128` is `SimdOp.denote` of `jasminDialect` for every operation `SimdOp` has
(`wAESENCW`, `wAESKEYGENASSISTW`, `clmul128W`, …). The unpack and word-blend operations are
the low half of the YMM operations of `YmmOpCore` on zero-extended operands, and `VPALIGNR`
and the three SHA-256 operations are defined here after the Intel SDM. `VOp.denote256`
applies `VOp.denote128` to each 128-bit half, which is the VEX.256 meaning of every
operation of the alphabet except the cross-half `VPERM2I128`.

## Main definitions

* `VOp`, `VLen`, `VAddr`, `ShaOp`, `VInstr`: the instruction alphabet.
* `laneName`, `readX`, `readY`: the lane view.
* `VOp.denote128`, `VOp.denote256`, `ShaOp.denote`: the operation denotations.
* `VInstr.writes`, `VInstr.dstLanes`, `VInstr.exec`: the instruction semantics.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect (yHalfW)

/-! ## The lane view -/

/-- The register-file name `%ymmR.K` of lane `k` (bits `64k` to `64k + 63`) of vector
    register `r`. -/
def laneName (r : Fin 16) (k : Fin 4) : String :=
  String.ofList ('%' :: 'y' :: 'm' :: 'm' :: (Nat.toDigits 10 r.val ++ ['.', Nat.digitChar k.val]))

/-- The XMM value of vector register `r`: lanes 1 and 0. -/
def readX (rd : String → BitVec 64) (r : Fin 16) : BitVec 128 :=
  rd (laneName r 1) ++ rd (laneName r 0)

/-- The YMM value of vector register `r`: lanes 3 to 0. -/
def readY (rd : String → BitVec 64) (r : Fin 16) : BitVec 256 :=
  rd (laneName r 3) ++ rd (laneName r 2) ++ rd (laneName r 1) ++ rd (laneName r 0)

/-- The lane writes of a VEX.128 result: lanes 0 and 1 from `v`, lanes 2 and 3 zero. -/
def writesVex128 (r : Fin 16) (v : BitVec 128) : List (String × BitVec 64) :=
  [(laneName r 0, v.extractLsb' 0 64), (laneName r 1, v.extractLsb' 64 64),
   (laneName r 2, 0), (laneName r 3, 0)]

/-- The lane writes of a legacy SSE result: lanes 0 and 1 from `v`; lanes 2 and 3 are kept. -/
def writesLegacy128 (r : Fin 16) (v : BitVec 128) : List (String × BitVec 64) :=
  [(laneName r 0, v.extractLsb' 0 64), (laneName r 1, v.extractLsb' 64 64)]

/-- The lane writes of a VEX.256 result: all four lanes from `v`. -/
def writesVex256 (r : Fin 16) (v : BitVec 256) : List (String × BitVec 64) :=
  [(laneName r 0, v.extractLsb' 0 64), (laneName r 1, v.extractLsb' 64 64),
   (laneName r 2, v.extractLsb' 128 64), (laneName r 3, v.extractLsb' 192 64)]

/-! ## Operations defined here -/

/-- `VPALIGNR a, b, imm8` on one 128-bit lane: the low 128 bits of the 256-bit
    concatenation `a : b` (`a` high) shifted right by `imm8` bytes (Intel SDM `PALIGNR`;
    `a` is `SRC1`, `b` is `SRC2`). A count of 32 or more gives zero. -/
def palignr128W (a b : BitVec 128) (imm : Nat) : BitVec 128 :=
  ((a ++ b) >>> (8 * imm)).setWidth 128

/-- The low 128 bits of a 256-bit two-operand operation applied to zero-extended operands:
    the VEX.128 form of an operation that acts on each 128-bit half separately. -/
def lowOfYmm (f : BitVec 256 → BitVec 256 → BitVec 256) (a b : BitVec 128) : BitVec 128 :=
  (f (a.setWidth 256) (b.setWidth 256)).setWidth 128

namespace VSha

/-- Dword `k` (bits `32k` to `32k + 31`) of a 128-bit value. -/
def dw (v : BitVec 128) (k : Nat) : BitVec 32 := v.extractLsb' (32 * k) 32

/-- The 128-bit value with dwords `d3` (high) to `d0` (low). -/
def pack (d3 d2 d1 d0 : BitVec 32) : BitVec 128 := d3 ++ d2 ++ d1 ++ d0

/-- Rotation right of a 32-bit word. -/
def rotr (x : BitVec 32) (n : Nat) : BitVec 32 := x.rotateRight n

/-- FIPS 180-4 `Ch`. -/
def ch (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ ((~~~x) &&& z)

/-- FIPS 180-4 `Maj`. -/
def maj (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- FIPS 180-4 `Σ0` of SHA-256. -/
def bigSigma0 (x : BitVec 32) : BitVec 32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

/-- FIPS 180-4 `Σ1` of SHA-256. -/
def bigSigma1 (x : BitVec 32) : BitVec 32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

/-- FIPS 180-4 `σ0` of SHA-256. -/
def smallSigma0 (x : BitVec 32) : BitVec 32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)

/-- FIPS 180-4 `σ1` of SHA-256. -/
def smallSigma1 (x : BitVec 32) : BitVec 32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- The state `(a, b, c, d, e, f, g, h)` of the SHA-256 compression function. -/
abbrev State := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 ×
  BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32

/-- One SHA-256 round (FIPS 180-4 §6.2.2, step 3) with `wk = W[t] + K[t]`. -/
def round (s : State) (wk : BitVec 32) : State :=
  let (a, b, c, d, e, f, g, h) := s
  let t1 := h + bigSigma1 e + ch e f g + wk
  let t2 := bigSigma0 a + maj a b c
  (t1 + t2, a, b, c, d + t1, e, f, g)

end VSha

open VSha in
/-- `SHA256RNDS2 xmm1, xmm2, <XMM0>` (Intel SDM): two SHA-256 rounds on the state
    `(C, D, G, H)` of `cdgh` (the destination `SRC1`, dwords 3 to 0) and `(A, B, E, F)` of
    `abef` (`SRC2`, dwords 3 to 0), with `W + K` of the two rounds in dwords 0 and 1 of `wk`
    (the implicit `XMM0`). The result is the new `(A, B, E, F)`. -/
def sha256rnds2X (cdgh abef wk : BitVec 128) : BitVec 128 :=
  let s0 : State := (dw abef 3, dw abef 2, dw cdgh 3, dw cdgh 2,
    dw abef 1, dw abef 0, dw cdgh 1, dw cdgh 0)
  let (a, b, _, _, e, f, _, _) := round (round s0 (dw wk 0)) (dw wk 1)
  pack a b e f

open VSha in
/-- `SHA256MSG1 xmm1, xmm2` (Intel SDM): with `W0` to `W3` the dwords of `s1` and `W4`
    dword 0 of `s2`, dword `j` of the result is `Wj + σ0(W(j+1))`. -/
def sha256msg1X (s1 s2 : BitVec 128) : BitVec 128 :=
  pack (dw s1 3 + smallSigma0 (dw s2 0)) (dw s1 2 + smallSigma0 (dw s1 3))
    (dw s1 1 + smallSigma0 (dw s1 2)) (dw s1 0 + smallSigma0 (dw s1 1))

open VSha in
/-- `SHA256MSG2 xmm1, xmm2` (Intel SDM): with `W14`, `W15` dwords 2 and 3 of `s2`,
    `W16 = s1[0] + σ1(W14)`, `W17 = s1[1] + σ1(W15)`, `W18 = s1[2] + σ1(W16)` and
    `W19 = s1[3] + σ1(W17)`; the result has dwords `W19` (high) to `W16` (low). -/
def sha256msg2X (s1 s2 : BitVec 128) : BitVec 128 :=
  let w16 := dw s1 0 + smallSigma1 (dw s2 2)
  let w17 := dw s1 1 + smallSigma1 (dw s2 3)
  let w18 := dw s1 2 + smallSigma1 w16
  let w19 := dw s1 3 + smallSigma1 w17
  pack w19 w18 w17 w16

/-! ## The instruction alphabet -/

/-- The vector length of a VEX form: `VEX.L = 0` (XMM) or `VEX.L = 1` (YMM). -/
inductive VLen where
  /-- `VEX.L = 0`: 128-bit operands; the destination's lanes 2 and 3 are zeroed. -/
  | l128
  /-- `VEX.L = 1`: 256-bit operands. -/
  | l256
  deriving DecidableEq, Repr

/-- The operation of a VEX register form. Operands are `SRC1` (`VEX.vvvv`, or `ModRM.rm` for
    an operation with one register operand) and `SRC2` (`ModRM.rm`); the immediate is a
    field of the instruction. An operation with one register operand reads `SRC1` only. -/
inductive VOp where
  /-- `VPXOR`. -/
  | vpxor
  /-- `VPAND`. -/
  | vpand
  /-- `VPOR`. -/
  | vpor
  /-- `VPANDN`: `(¬SRC1) ∧ SRC2`. -/
  | vpandn
  /-- `VPADDD`. -/
  | vpaddd
  /-- `VPADDQ`. -/
  | vpaddq
  /-- `VPSUBD`. -/
  | vpsubd
  /-- `VPSUBQ`. -/
  | vpsubq
  /-- `VPSLLD` by the immediate. -/
  | vpslld
  /-- `VPSRLD` by the immediate. -/
  | vpsrld
  /-- `VPSLLQ` by the immediate. -/
  | vpsllq
  /-- `VPSRLQ` by the immediate. -/
  | vpsrlq
  /-- `VPSLLDQ`: byte shift left of each 128-bit half by the immediate. -/
  | vpslldq
  /-- `VPSRLDQ`: byte shift right of each 128-bit half by the immediate. -/
  | vpsrldq
  /-- `VPSHUFB`: bytes of `SRC1` selected by the control bytes of `SRC2`. -/
  | vpshufb
  /-- `VPSHUFD`: dword shuffle of `SRC1` under the immediate. -/
  | vpshufd
  /-- `VPUNPCKLDQ`. -/
  | vpunpckldq
  /-- `VPUNPCKHDQ`. -/
  | vpunpckhdq
  /-- `VPUNPCKLQDQ`. -/
  | vpunpcklqdq
  /-- `VPUNPCKHQDQ`. -/
  | vpunpckhqdq
  /-- `VPALIGNR`: byte shift right of `SRC1 : SRC2` by the immediate. -/
  | vpalignr
  /-- `VPBLENDW`: word `i` of `SRC2` where bit `i mod 8` of the immediate is set. -/
  | vpblendw
  /-- `VAESENC`: state `SRC1`, round key `SRC2`. -/
  | vaesenc
  /-- `VAESENCLAST`: state `SRC1`, round key `SRC2`. -/
  | vaesenclast
  /-- `VAESKEYGENASSIST`: `SRC1` and the round constant in the immediate (VEX.128 only). -/
  | vaeskeygenassist
  /-- `VPCLMULQDQ`: carry-less product of the qwords the immediate selects. -/
  | vpclmulqdq
  /-- `VGF2P8MULB`. -/
  | vgf2p8mulb
  /-- `VGF2P8AFFINEQB`: data `SRC1`, matrix `SRC2`, constant in the immediate. -/
  | vgf2p8affineqb
  /-- `VPERM2I128`: 128-bit half select from `SRC1` and `SRC2` (VEX.256 only). -/
  | vperm2i128
  deriving DecidableEq, Repr

/-- The address of a vector load: `base + disp`, or `base + 8·idx + disp`. -/
inductive VAddr where
  /-- `[base + disp]`. -/
  | baseDisp (base : String) (disp : Int)
  /-- `[base + 8·idx + disp]`. -/
  | baseIdx (base idx : String) (disp : Int)
  deriving DecidableEq, Repr

/-- The three SHA-NI operations. Each has the legacy register form `op xmm1, xmm2` with
    `xmm1` source and destination; `SHA256RNDS2` reads `XMM0` as a third operand. -/
inductive ShaOp where
  /-- `SHA256RNDS2`. -/
  | rnds2
  /-- `SHA256MSG1`. -/
  | msg1
  /-- `SHA256MSG2`. -/
  | msg2
  deriving DecidableEq, Repr

/-- An x86 vector instruction of the machine model. -/
inductive VInstr where
  /-- A VEX register form `op dst, src1, src2, imm` at length `len`. -/
  | vex (op : VOp) (len : VLen) (dst src1 src2 : Fin 16) (imm : BitVec 8)
  /-- `VMOVDQU dst, [addr]` (`aligned = false`) or `VMOVDQA dst, [addr]` (`aligned = true`),
      reading `len / 64` consecutive words. -/
  | vload (aligned : Bool) (len : VLen) (dst : Fin 16) (addr : VAddr)
  /-- `VMOVDQA dst, src`: register move at length `len`. -/
  | vmov (len : VLen) (dst src : Fin 16)
  /-- `VZEROUPPER`: lanes 2 and 3 of every vector register set to zero. -/
  | vzeroupper
  /-- A legacy SHA-NI register form `op dst, src`. -/
  | sha (op : ShaOp) (dst src : Fin 16)
  deriving DecidableEq, Repr

/-! ## Denotations -/

/-- The 128-bit denotation of a VEX operation at immediate `imm` on `SRC1 = a`,
    `SRC2 = b`. `VPERM2I128` has no 128-bit form and denotes zero. -/
def VOp.denote128 (op : VOp) (imm : BitVec 8) (a b : BitVec 128) : BitVec 128 :=
  match op with
  | .vpxor => SimdOp.denote (.bitwise .xor) a b
  | .vpand => SimdOp.denote (.bitwise .and) a b
  | .vpor => SimdOp.denote (.bitwise .or) a b
  | .vpandn => SimdOp.denote (.bitwise .andn) a b
  | .vpaddd => SimdOp.denote (.packed .add 32) a b
  | .vpaddq => SimdOp.denote (.packed .add 64) a b
  | .vpsubd => SimdOp.denote (.packed .sub 32) a b
  | .vpsubq => SimdOp.denote (.packed .sub 64) a b
  | .vpslld => SimdOp.denote (.packedImm .shl 32 imm.toNat) a b
  | .vpsrld => SimdOp.denote (.packedImm .shr 32 imm.toNat) a b
  | .vpsllq => SimdOp.denote (.packedImm .shl 64 imm.toNat) a b
  | .vpsrlq => SimdOp.denote (.packedImm .shr 64 imm.toNat) a b
  | .vpslldq => a <<< (imm.toNat * 8)
  | .vpsrldq => a >>> (imm.toNat * 8)
  | .vpshufb => SimdOp.denote .vpshufb a b
  | .vpshufd => SimdOp.denote (.vpshufd imm.toNat) a b
  | .vpunpckldq => lowOfYmm VIR.YmmDialect.vpunpckldqW a b
  | .vpunpckhdq => lowOfYmm VIR.YmmDialect.vpunpckhdqW a b
  | .vpunpcklqdq => lowOfYmm VIR.YmmDialect.vpunpcklqdqW a b
  | .vpunpckhqdq => lowOfYmm VIR.YmmDialect.vpunpckhqdqW a b
  | .vpalignr => palignr128W a b imm.toNat
  | .vpblendw => lowOfYmm (fun x y => VIR.YmmDialect.vpblendwW x y imm.toNat) a b
  | .vaesenc => SimdOp.denote .vaesenc a b
  | .vaesenclast => SimdOp.denote .vaesenclast a b
  | .vaeskeygenassist => SimdOp.denote (.vaeskeygen imm) a b
  | .vpclmulqdq => SimdOp.denote (.clmul imm.toNat) a b
  | .vgf2p8mulb => SimdOp.denote .gf2p8mulb a b
  | .vgf2p8affineqb => SimdOp.denote (.affineqb imm) a b
  | .vperm2i128 => 0

/-- The 256-bit denotation of a VEX operation: `VPERM2I128` by `vperm2i128W`, every other
    operation by `VOp.denote128` on each 128-bit half. -/
def VOp.denote256 (op : VOp) (imm : BitVec 8) (a b : BitVec 256) : BitVec 256 :=
  match op with
  | .vperm2i128 => VIR.YmmDialect.vperm2i128W a b imm.toNat
  | _ => op.denote128 imm (yHalfW a 1) (yHalfW b 1) ++ op.denote128 imm (yHalfW a 0) (yHalfW b 0)

/-- Whether a VEX operation has an encoding at length `len`: `VAESKEYGENASSIST` only at
    `VEX.L = 0`, `VPERM2I128` only at `VEX.L = 1`, every other operation at both. -/
def VOp.validAt : VOp → VLen → Bool
  | .vaeskeygenassist, .l256 => false
  | .vperm2i128, .l128 => false
  | _, _ => true

/-- The denotation of a SHA-NI operation on the destination `d`, the source `s` and the
    value `x0` of `XMM0`, which only `SHA256RNDS2` reads. -/
def ShaOp.denote (op : ShaOp) (d s x0 : BitVec 128) : BitVec 128 :=
  match op with
  | .rnds2 => sha256rnds2X d s x0
  | .msg1 => sha256msg1X d s
  | .msg2 => sha256msg2X d s

/-! ## Instruction semantics -/

/-- The base register of a load address. -/
def VAddr.base : VAddr → String
  | .baseDisp b _ => b
  | .baseIdx b _ _ => b

/-- The byte offset from the base register of a load address, under the register read
    `rd`. -/
def VAddr.offset (rd : String → BitVec 64) : VAddr → Int
  | .baseDisp _ d => d
  | .baseIdx _ i d => d + ((8 * (rd i).toNat : Nat) : Int)

/-- The 128-bit value at a load address: the words at offsets `0` and `8` (little-endian). -/
def loadX (rd : String → BitVec 64) (ld : String → Int → BitVec 64) (a : VAddr) :
    BitVec 128 :=
  ld a.base (a.offset rd + 8) ++ ld a.base (a.offset rd)

/-- The 256-bit value at a load address: the words at offsets `0`, `8`, `16`, `24`. -/
def loadY (rd : String → BitVec 64) (ld : String → Int → BitVec 64) (a : VAddr) :
    BitVec 256 :=
  ld a.base (a.offset rd + 24) ++ ld a.base (a.offset rd + 16) ++
    ld a.base (a.offset rd + 8) ++ ld a.base (a.offset rd)

/-- The lane writes of a vector instruction under the register read `rd` and the word read
    `ld base off`. -/
def VInstr.writes (rd : String → BitVec 64) (ld : String → Int → BitVec 64) :
    VInstr → List (String × BitVec 64)
  | .vex op .l128 d s1 s2 imm => writesVex128 d (op.denote128 imm (readX rd s1) (readX rd s2))
  | .vex op .l256 d s1 s2 imm => writesVex256 d (op.denote256 imm (readY rd s1) (readY rd s2))
  | .vload _ .l128 d a => writesVex128 d (loadX rd ld a)
  | .vload _ .l256 d a => writesVex256 d (loadY rd ld a)
  | .vmov .l128 d s => writesVex128 d (readX rd s)
  | .vmov .l256 d s => writesVex256 d (readY rd s)
  | .vzeroupper =>
      (List.finRange 16).flatMap fun r => [(laneName r 2, 0), (laneName r 3, 0)]
  | .sha op d s => writesLegacy128 d (op.denote (readX rd d) (readX rd s) (readX rd 0))

/-- The lane names a vector instruction writes. -/
def VInstr.dstLanes : VInstr → List String
  | .vex _ _ d _ _ _ | .vload _ _ d _ | .vmov _ d _ =>
      [laneName d 0, laneName d 1, laneName d 2, laneName d 3]
  | .vzeroupper => (List.finRange 16).flatMap fun r => [laneName r 2, laneName r 3]
  | .sha _ d _ => [laneName d 0, laneName d 1]

/-- The register file after a vector instruction: each written lane name holds its written
    word, every other name keeps its value. -/
def VInstr.exec (rd : String → BitVec 64) (ld : String → Int → BitVec 64) (v : VInstr) :
    String → BitVec 64 :=
  fun n => ((v.writes rd ld).lookup n).getD (rd n)

/-- The names of the lane writes are `dstLanes`, whatever the reads. -/
theorem VInstr.writes_map_fst (rd : String → BitVec 64) (ld : String → Int → BitVec 64)
    (v : VInstr) : (v.writes rd ld).map Prod.fst = v.dstLanes := by
  cases v with
  | vex op len d s1 s2 imm => cases len <;> rfl
  | vload al len d a => cases len <;> rfl
  | vmov len d s => cases len <;> rfl
  | vzeroupper => simp [VInstr.writes, VInstr.dstLanes, List.map_flatMap]
  | sha op d s => rfl

/-- A name a vector instruction does not write keeps its value. -/
theorem VInstr.exec_of_not_mem (rd : String → BitVec 64) (ld : String → Int → BitVec 64)
    (v : VInstr) (n : String) (h : n ∉ v.dstLanes) : v.exec rd ld n = rd n := by
  rw [← VInstr.writes_map_fst rd ld v] at h
  have hl : (v.writes rd ld).lookup n = none := by
    generalize v.writes rd ld = l at h
    induction l with
    | nil => rfl
    | cons p l ih =>
      obtain ⟨m, x⟩ := p
      simp only [List.map_cons, List.mem_cons, not_or] at h
      simp only [List.lookup_cons]
      grind
  simp [VInstr.exec, hl]

/-! ## Lane lemmas -/

/-- Two lane names of one vector register are equal exactly when their lane indices are. -/
theorem laneName_eq_iff (r : Fin 16) (j k : Fin 4) : laneName r j = laneName r k ↔ j = k := by
  simp only [laneName, String.ofList_inj, List.cons.injEq, List.append_cancel_left_eq, true_and,
    and_true]
  constructor
  · intro h
    have h' := congrArg Char.toNat h
    rw [Nat.toNat_digitChar_of_lt_ten (by omega), Nat.toNat_digitChar_of_lt_ten (by omega)] at h'
    exact Fin.ext (by omega)
  · rintro rfl
    rfl

/-- The Boolean equality of two lane names of one vector register. -/
theorem laneName_beq (r : Fin 16) (j k : Fin 4) :
    (laneName r j == laneName r k) = decide (j = k) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  exact laneName_eq_iff r j k

/-- The four lane names of a vector register are distinct. -/
theorem laneName_ne (r : Fin 16) (j k : Fin 4) (h : j ≠ k) : laneName r j ≠ laneName r k := by
  intro heq
  have := laneName_beq r j k
  simp_all

/-- A 128-bit value is the concatenation of its two qwords. -/
theorem qwords_append_128 (v : BitVec 128) : v.extractLsb' 64 64 ++ v.extractLsb' 0 64 = v := by
  ext i hi
  grind

/-- A 256-bit value is the concatenation of its four qwords. -/
theorem qwords_append_256 (v : BitVec 256) :
    v.extractLsb' 192 64 ++ v.extractLsb' 128 64 ++ v.extractLsb' 64 64 ++
      v.extractLsb' 0 64 = v := by
  ext i hi
  simp only [BitVec.getElem_append, BitVec.getElem_extractLsb']
  grind

/-- The XMM value of the destination after a VEX.128 register form is the operation's
    128-bit denotation of the XMM values of the sources. -/
theorem readX_exec_vex128 (rd : String → BitVec 64) (ld : String → Int → BitVec 64)
    (op : VOp) (d s1 s2 : Fin 16) (imm : BitVec 8) :
    readX ((VInstr.vex op .l128 d s1 s2 imm).exec rd ld) d =
      op.denote128 imm (readX rd s1) (readX rd s2) := by
  simp [readX, VInstr.exec, VInstr.writes, writesVex128, List.lookup, laneName_beq,
    qwords_append_128]

/-- After a VEX.128 form, lanes 2 and 3 of the destination are zero. -/
theorem upper_exec_vex128 (rd : String → BitVec 64) (ld : String → Int → BitVec 64)
    (op : VOp) (d s1 s2 : Fin 16) (imm : BitVec 8) (k : Fin 4) (hk : 2 ≤ k.val) :
    (VInstr.vex op .l128 d s1 s2 imm).exec rd ld (laneName d k) = 0 := by
  have hk' : k = 2 ∨ k = 3 := by omega
  rcases hk' with rfl | rfl <;>
    simp [VInstr.exec, VInstr.writes, writesVex128, List.lookup, laneName_beq]

/-- The YMM value of the destination after a VEX.256 register form is the operation's
    256-bit denotation of the YMM values of the sources. -/
theorem readY_exec_vex256 (rd : String → BitVec 64) (ld : String → Int → BitVec 64)
    (op : VOp) (d s1 s2 : Fin 16) (imm : BitVec 8) :
    readY ((VInstr.vex op .l256 d s1 s2 imm).exec rd ld) d =
      op.denote256 imm (readY rd s1) (readY rd s2) := by
  simp [readY, VInstr.exec, VInstr.writes, writesVex256, List.lookup, laneName_beq,
    qwords_append_256]

/-- The XMM value of the destination after a 128-bit load is the value at the address. -/
theorem readX_exec_vload128 (rd : String → BitVec 64) (ld : String → Int → BitVec 64)
    (al : Bool) (d : Fin 16) (a : VAddr) :
    readX ((VInstr.vload al .l128 d a).exec rd ld) d = loadX rd ld a := by
  simp [readX, VInstr.exec, VInstr.writes, writesVex128, List.lookup, laneName_beq,
    qwords_append_128]

end CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
