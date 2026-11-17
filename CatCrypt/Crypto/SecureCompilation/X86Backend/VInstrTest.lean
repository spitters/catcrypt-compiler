/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.VInstr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Lean
public import CatCrypt.Crypto.SecureCompilation.VIR.ShaNiEmit
public import CatCryptCore.Tactics.KatGuard
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.VInstr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Lean
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ShaNiEmit

/-!
# Known-answer checks of the vector instruction denotations

Checks of `VOp.denote128`, `VOp.denote256` and the SHA-NI denotations of `VInstr` against
the outputs of the Sail transcription recorded in `SailX86Lean` (AES-NI, PCLMULQDQ), the
SHA-NI model of `ShaNiEmit`, the YMM operations of `YmmOpCore`, and the FIPS 180-4 message
schedule.

## Main results

* Known-answer checks (`#kat`) of VAESENC, VAESENCLAST, VAESKEYGENASSIST and VPCLMULQDQ
  against the recorded Sail outputs.
* SHA256RNDS2 and SHA256MSG2 against `ShaNiEmit`; SHA256MSG1, which follows the Intel SDM,
  against `sha256msg1_lane` after `VPALIGNR $4`, and a FIPS 180-4 schedule step.
* The VEX.256 operations against the per-half functions of `YmmOpCore`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.VInstrTest

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Lean (fipsBlk fipsKey)
open CatCrypt.Crypto.SecureCompilation.VIR.ShaNiEmit
  (sha256rnds2_lane sha256msg1_lane sha256msg2_lane)
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect

/-! ## AES-NI and PCLMULQDQ against the recorded Sail outputs -/

#kat VOp.denote128 .vaesenc 0 fipsBlk fipsKey == 0xe7bbd0de82cc798722c5e80b9f93215b#128
#kat VOp.denote128 .vaesenclast 0 fipsBlk fipsKey == 0xefb9d0d4ef3490fb4aed11b22a710924#128
#kat VOp.denote128 .vaeskeygenassist 1 fipsKey 0 == 0xf35947f0626859c4f35947f0626859c4#128
#kat VOp.denote128 .vpclmulqdq 0 3 3 == 5#128
#kat VOp.denote128 .vpclmulqdq 0x11 (0xFF#128 <<< 64) (0xFF#128 <<< 64) == 0x5555#128
#kat VOp.denote128 .vpclmulqdq 0x10 0xFFFFFFFFFFFFFFFF#128 (0xFFFFFFFFFFFFFFFF#128 <<< 64)
  == BitVec.ofNat 128 113427455640312821154458202477256070485

/-! ## SHA-NI against `ShaNiEmit` -/

/-- A first sample operand. -/
def xa : BitVec 128 := 0x6a09e667bb67ae853c6ef372a54ff53a#128
/-- A second sample operand. -/
def xb : BitVec 128 := 0x510e527f9b05688c1f83d9ab5be0cd19#128
/-- A third sample operand. -/
def xc : BitVec 128 := 0x428a2f9871374491b5c0fbcfe9b5dba5#128

#kat sha256rnds2X xa xb xc == sha256rnds2_lane xb xa xc
#kat sha256msg2X xa xb == sha256msg2_lane xa xb
-- `SHA256MSG1` reads `W4` from dword 0 of its second operand; `sha256msg1_lane` takes the
-- window `W1..W4` as its second operand.
#kat sha256msg1X xa xb == sha256msg1_lane xa (palignr128W xb xa 4)

/-! ## The SHA-256 message schedule -/

/-- Words `W0` to `W15` of a sample message block. -/
def wBlk (t : Nat) : BitVec 32 := BitVec.ofNat 32 (0x9e3779b9 * (t + 1) + 0x7f4a7c15 * t * t)

/-- The FIPS 180-4 schedule word `W t` of the sample block. -/
def wFips (t : Nat) : BitVec 32 :=
  if t < 16 then wBlk t else
    VSha.smallSigma1 (wFips (t - 2)) + wFips (t - 7) + VSha.smallSigma0 (wFips (t - 15)) +
      wFips (t - 16)
termination_by t
decreasing_by all_goals omega

/-- The words `W4q` to `W4q + 3` as one 128-bit value. -/
def quad (q : Nat) : BitVec 128 :=
  VSha.pack (wBlk (4 * q + 3)) (wBlk (4 * q + 2)) (wBlk (4 * q + 1)) (wBlk (4 * q))

/-- `W16` to `W19` by `SHA256MSG1`, `VPALIGNR $4`, `VPADDD` and `SHA256MSG2`. -/
def nextQuad : BitVec 128 :=
  let t := sha256msg1X (quad 0) (quad 1)
  let t := VOp.denote128 .vpaddd 0 t (VOp.denote128 .vpalignr 4 (quad 3) (quad 2))
  sha256msg2X t (quad 3)

#kat nextQuad == VSha.pack (wFips 19) (wFips 18) (wFips 17) (wFips 16)

/-! ## VEX.256 per-half denotations against `YmmOpCore` -/

/-- A first 256-bit sample operand. -/
def ya : BitVec 256 := xa ++ xb
/-- A second 256-bit sample operand. -/
def yb : BitVec 256 := xc ++ xa

#kat VOp.denote256 .vpunpckldq 0 ya yb == vpunpckldqW ya yb
#kat VOp.denote256 .vpunpckhdq 0 ya yb == vpunpckhdqW ya yb
#kat VOp.denote256 .vpunpcklqdq 0 ya yb == vpunpcklqdqW ya yb
#kat VOp.denote256 .vpunpckhqdq 0 ya yb == vpunpckhqdqW ya yb
#kat VOp.denote256 .vpblendw 0xA5 ya yb == vpblendwW ya yb 0xA5
#kat VOp.denote256 .vpshufd 0x1B ya yb == vpshufdW ya 0x1B
#kat VOp.denote256 .vpaddd 0 ya yb == vpadddW ya yb
#kat VOp.denote256 .vpxor 0 ya yb == vpxorW ya yb
#kat VOp.denote256 .vpslldq 3 ya yb == vpslldqW ya 3
#kat VOp.denote256 .vpsrldq 5 ya yb == vpsrldqW ya 5
#kat VOp.denote256 .vpshufb 0 ya yb == vpshufbW ya yb
#kat VOp.denote256 .vpslld 7 ya yb == vpslldW ya 7
#kat VOp.denote256 .vpsrlq 13 ya yb == vpsrlqW ya 13

end CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin.VInstrTest
