/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public meta import CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore
public import CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore
public import Mathlib.Data.Fin.VecNotation

/-!
# The 256-bit YMM op family: `JasminTy` routing and smoke pins

The `JasminTy`-carrying part of the 256-bit YMM op family. `YmmOp` and its
`BitVec 256` denotation are in `YmmOpCore.lean`; this module adds the routing of
each op's operand/result arity into `JasminTy` (`YmmOp.argTys` / `YmmOp.retTy`)
and the lane-KAT smoke pins.

`YmmOp.argTys` / `YmmOp.retTy` are what the `Com` integration reads to project
each op's arity: every register operand/result is a `reg 256`, unary ops take a
single operand, binary ops take two.

## RESIDUAL scoped OUT of this family

The SIMD→GPR **extract** `vpmovmskb` (`X86Backend/MpnSimdExtractEmit.lean`) is NOT
modelled here. It leaves the vector register file: it reads a `BitVec 256` and
writes a `BitVec 32` *into a GPR*, so its result type is **not** `reg 256`
(it is `reg 32`, a cross-file move). The whole `YmmOp` family is closed under
`reg 256 → reg 256` (`argTys`/`retTy` below), so adding `vpmovmskb` would break
that uniformity and needs a `reg 32` return arm.

The **memory-broadcast** `vpbroadcastq` is likewise not an arm here. Every use in
the emitted 4-way/8-way artifacts sources it from memory
(`vpbroadcastq disp(%base), %ymm` / `sym(%rip), %ymm`), so it is a load, not a
`reg 256 → reg 256` op. Its register form `vpbroadcastq %xmm, %ymm` takes a
`reg 128` source and breaks the family's closure for the same reason
`vpmovmskb` does.

The **data movement** mnemonics `vmovdqu`/`vmovdqu64`/`vmovdqa64` and the
`vzeroupper` prologue hygiene are not ops either: they cross the
register/memory boundary or act on the whole vector state. `vmovdqu` lives at
the instruction level as `YmmAsmPrint.YmmInstr.ymov`/`.yload`/`.ystore`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 5. `JasminTy` routing -/

/-- Argument types: every register operand is a `reg 256`. Unary ops take a
    single `reg 256`, binary ops take two. (When wired into `Com`, this drives
    the per-op arity — the unary arms have a 1-element `argTys`.) -/
def YmmOp.argTys : YmmOp → List JasminTy
  | .vpmuldq => [.reg 256, .reg 256]
  | .vmovshdup => [.reg 256]
  | .vpsubq => [.reg 256, .reg 256]
  | .vpaddd => [.reg 256, .reg 256]
  | .vpsubd => [.reg 256, .reg 256]
  | .vpblendd _ => [.reg 256, .reg 256]
  | .vpshufd _ => [.reg 256]
  | .vpermq _ => [.reg 256]
  | .vpmuludq => [.reg 256, .reg 256]
  | .vpaddq => [.reg 256, .reg 256]
  | .vpmullq => [.reg 256, .reg 256]
  | .vpand => [.reg 256, .reg 256]
  | .vpor => [.reg 256, .reg 256]
  | .vpxor => [.reg 256, .reg 256]
  | .vpshufb => [.reg 256, .reg 256]
  | .vpsrlq _ => [.reg 256]
  | .vpsllq _ => [.reg 256]
  | .vpsrld _ => [.reg 256]
  | .vpslld _ => [.reg 256]
  | .vpsrlvd => [.reg 256, .reg 256]
  | .vpsllvd => [.reg 256, .reg 256]
  | .vpandn => [.reg 256, .reg 256]
  | .vprolq _ => [.reg 256]
  | .vpmulld => [.reg 256, .reg 256]
  | .vpsrad _ => [.reg 256]
  | .vpaddw => [.reg 256, .reg 256]
  | .vpsubw => [.reg 256, .reg 256]
  | .vpmullw => [.reg 256, .reg 256]
  | .vpmulhw => [.reg 256, .reg 256]
  | .vpmaddwd => [.reg 256, .reg 256]
  | .vpcmpgtw => [.reg 256, .reg 256]
  | .vpcmpgtd => [.reg 256, .reg 256]
  | .vpcmpeqd => [.reg 256, .reg 256]
  | .vpsllw _ => [.reg 256]
  | .vpsrlw _ => [.reg 256]
  | .vpsraw _ => [.reg 256]
  | .vpabsd => [.reg 256]
  | .vpsignd => [.reg 256, .reg 256]
  | .vpacksswb => [.reg 256, .reg 256]
  | .vpackssdw => [.reg 256, .reg 256]
  | .vpermd => [.reg 256, .reg 256]
  | .vpunpckldq => [.reg 256, .reg 256]
  | .vpunpckhdq => [.reg 256, .reg 256]
  | .vpunpcklqdq => [.reg 256, .reg 256]
  | .vpunpckhqdq => [.reg 256, .reg 256]
  | .vpblendw _ => [.reg 256, .reg 256]
  | .vpsrldq _ => [.reg 256]
  | .vperm2i128 _ => [.reg 256, .reg 256]

/-- Result type: every `YmmOp` produces a single `reg 256`.
    (The SIMD→GPR `vpmovmskb` extract, which would return `reg 32`, is the
    residual scoped OUT of this family — see the module docstring.) -/
def YmmOp.retTy : YmmOp → JasminTy
  | _ => .reg 256

/-! ## 6. Smoke pins (matching `Avx2YmmModel`'s lane KATs)

These re-run the model's lane KATs against the `W`-suffixed copies through the
`YmmOp.denote` dispatch, so the standalone op family is pinned to the same lane
semantics as the bespoke model before any migration. -/

/-- `vpmuldq` POSITIVE pin (matches the model's positive lane KAT): even dword 0
    of `a = 7`, of `b = 3`, product `21` in qword lane 0; odd dwords ignored. -/
example :
    yQwordW (YmmOp.denote .vpmuldq
      (yOfDwordsW ![7, 999, 0, 0, 0, 0, 0, 0])
      (yOfDwordsW ![3, 888, 0, 0, 0, 0, 0, 0])) 0 = (21 : BitVec 64) := by native_decide

/-- `vpmuldq` NEGATIVE pin (signedness required): `-2` (`0xFFFFFFFE`) times
    `3` is the SIGNED product `-6` (`0xFFFFFFFFFFFFFFFA`). -/
example :
    yQwordW (YmmOp.denote .vpmuldq
      (yOfDwordsW ![BitVec.ofNat 32 0xFFFFFFFE, 0, 0, 0, 0, 0, 0, 0])
      (yOfDwordsW ![3, 0, 0, 0, 0, 0, 0, 0])) 0
    = BitVec.ofNat 64 0xFFFFFFFFFFFFFFFA := by native_decide

/-- `vmovshdup` pin (unary): source dwords `[0,1,2,3,4,5,6,7]` ⇒ `[1,1,3,3,5,5,7,7]`. -/
example :
    let r := YmmOp.denote .vmovshdup (yOfDwordsW ![0, 1, 2, 3, 4, 5, 6, 7]) 0;
    (yDwordW r 0 = 1) ∧ (yDwordW r 1 = 1) ∧ (yDwordW r 2 = 3) ∧ (yDwordW r 3 = 3) ∧
    (yDwordW r 6 = 7) ∧ (yDwordW r 7 = 7) := by native_decide

/-- `vpsubq` pin: `0 − 1 = 2⁶⁴−1` in lane 0 with NO borrow into lane 1. -/
example :
    let r := YmmOp.denote .vpsubq (yOfQwordsW ![0, 5, 0, 0]) (yOfQwordsW ![1, 2, 0, 0]);
    (yQwordW r 0 = BitVec.allOnes 64) ∧ (yQwordW r 1 = 3) := by native_decide

/-- `vpaddd` pin: `(2³²−1) + 1 = 0` in dword 0, independent of the other dwords. -/
example :
    yDwordW (YmmOp.denote .vpaddd (yOfDwordsW ![BitVec.allOnes 32, 0, 0, 0, 0, 0, 0, 0])
                   (yOfDwordsW ![1, 0, 0, 0, 0, 0, 0, 0])) 0 = 0 := by native_decide

/-- `vpsubd` pin: `0 − 1 = 2³²−1` in dword 0, 32-bit-lane wrap. -/
example :
    yDwordW (YmmOp.denote .vpsubd (yOfDwordsW ![0, 0, 0, 0, 0, 0, 0, 0])
                   (yOfDwordsW ![1, 0, 0, 0, 0, 0, 0, 0])) 0 = BitVec.allOnes 32 := by
  native_decide

/-- `vpblendd $0xAA` pin: `0xAA = 0b10101010` selects `b` for odd dwords, `a` for
    even ⇒ `[a0,b1,a2,b3,a4,b5,a6,b7]` (the exact `$170` blend the NTT uses). -/
example :
    let a := yOfDwordsW ![0, 0, 0, 0, 0, 0, 0, 0];
    let b := yOfDwordsW ![1, 1, 1, 1, 1, 1, 1, 1];
    let r := YmmOp.denote (.vpblendd 0xAA) a b;
    (yDwordW r 0 = 0) ∧ (yDwordW r 1 = 1) ∧ (yDwordW r 2 = 0) ∧ (yDwordW r 3 = 1) ∧
    (yDwordW r 4 = 0) ∧ (yDwordW r 5 = 1) ∧ (yDwordW r 6 = 0) ∧ (yDwordW r 7 = 1) := by
  native_decide

/-- `vpshufd $0xFF` pin (unary): broadcast dword 3 within each 128-bit lane ⇒
    `[a3,a3,a3,a3, a7,a7,a7,a7]`. -/
example :
    let r := YmmOp.denote (.vpshufd 0xFF) (yOfDwordsW ![0, 1, 2, 3, 4, 5, 6, 7]) 0;
    (yDwordW r 0 = 3) ∧ (yDwordW r 3 = 3) ∧ (yDwordW r 4 = 7) ∧ (yDwordW r 7 = 7) := by
  native_decide

/-- `vpermq $0x4E` pin (unary, `0b01_00_11_10`): output qwords `[a2,a3,a0,a1]`
    (the 128-bit halves swapped). -/
example :
    let r := YmmOp.denote (.vpermq 0x4E) (yOfQwordsW ![0, 1, 2, 3]) 0;
    (yQwordW r 0 = 2) ∧ (yQwordW r 1 = 3) ∧ (yQwordW r 2 = 0) ∧ (yQwordW r 3 = 1) := by
  native_decide

/-- Cross-check: `YmmOp.denote` agrees with `Avx2YmmModel`'s lane ops on the
    Montgomery-mul fragment head — `vpmuldq` then `vmovshdup`, with a negative
    coefficient in the even-lane product. -/
example :
    let a := yOfDwordsW ![5, 0, BitVec.ofNat 32 0xFFFFFFFF, 0, 0, 0, 0, 0];
    let b := yOfDwordsW ![3, 11, 7, 22, 0, 0, 0, 0];
    let prod := YmmOp.denote .vpmuldq a b;
    let dup := YmmOp.denote .vmovshdup b 0;
    -- lane 0 = 5 * 3 = 15 (signed, positive)
    (yQwordW prod 0 = (15 : BitVec 64)) ∧
    -- lane 1 = (-1) * 7 = -7 (signed; even dword 2 of a = 0xFFFFFFFF = -1)
    (yQwordW prod 1 = BitVec.ofNat 64 0xFFFFFFFFFFFFFFF9) ∧
    -- vmovshdup of b: odd-dup ⇒ [11,11,22,22,0,0,0,0]
    (yDwordW dup 0 = 11) ∧ (yDwordW dup 1 = 11) ∧
    (yDwordW dup 2 = 22) ∧ (yDwordW dup 3 = 22) := by native_decide

/-! ## 6b. Smoke pins for the added ALU ops

One pin per added op whose denotation could plausibly be mis-stated: the
signedness of `vpmuludq`, the lane boundary of `vpaddq`/`vpslld`, the low-product
truncation of `vpmullq`, the over-shift-to-zero of `vpsrlq`, and the byte gather
plus high-bit zeroing of `vpshufb`. The bitwise trio `vpand`/`vpor`/`vpxor` is
definitionally the whole-register operation, so a value pin adds nothing. -/

/-- `vpmuludq` UNSIGNED pin (this is what distinguishes it from `vpmuldq`):
    `0xFFFFFFFE` zero-extends to `4294967294`, so the product with `3` is
    `0x2FFFFFFFA`, not the signed `-6`. -/
example :
    yQwordW (YmmOp.denote .vpmuludq
      (yOfDwordsW ![BitVec.ofNat 32 0xFFFFFFFE, 0, 0, 0, 0, 0, 0, 0])
      (yOfDwordsW ![3, 0, 0, 0, 0, 0, 0, 0])) 0
    = BitVec.ofNat 64 0x2FFFFFFFA := by native_decide

/-- `vpaddq` pin: `(2⁶⁴−1) + 1 = 0` in lane 0 with NO carry into lane 1. -/
example :
    let r := YmmOp.denote .vpaddq (yOfQwordsW ![BitVec.allOnes 64, 5, 0, 0])
                                  (yOfQwordsW ![1, 2, 0, 0]);
    (yQwordW r 0 = 0) ∧ (yQwordW r 1 = 7) := by native_decide

/-- `vpmullq` pin: `2³³ · 2³³ = 2⁶⁶`, whose low 64 bits are zero. -/
example :
    yQwordW (YmmOp.denote .vpmullq (yOfQwordsW ![BitVec.ofNat 64 (2 ^ 33), 0, 0, 0])
      (yOfQwordsW ![BitVec.ofNat 64 (2 ^ 33), 0, 0, 0])) 0 = 0 := by native_decide

/-- `vpsrlq` pin: `2³⁰ >>> 26 = 2⁴` per qword lane, and a count at the lane width
    yields zero (the x86 `imm8 ≥ 64` behaviour). -/
example :
    let r := YmmOp.denote (.vpsrlq 26) (yOfQwordsW ![BitVec.ofNat 64 (2 ^ 30), 0, 0, 0]) 0;
    let z := YmmOp.denote (.vpsrlq 64) (yOfQwordsW ![BitVec.allOnes 64, 0, 0, 0]) 0;
    (yQwordW r 0 = BitVec.ofNat 64 (2 ^ 4)) ∧ (yQwordW z 0 = 0) := by native_decide

/-- `vpslld` pin: `0xF0000001 <<< 4` truncates within the 32-bit lane to
    `0x00000010`, with no bleed into dword lane 1. -/
example :
    let r := YmmOp.denote (.vpslld 4)
      (yOfDwordsW ![BitVec.ofNat 32 0xF0000001, 0, 0, 0, 0, 0, 0, 0]) 0;
    (yDwordW r 0 = BitVec.ofNat 32 0x00000010) ∧ (yDwordW r 1 = 0) := by native_decide

/-- `vpshufb` pin: with data byte `j = j`, control byte 0 = `3` gathers `a`'s byte
    3; control byte 1 = `0x80` zeroes the byte; control byte 16 = `0` gathers
    within the HIGH 128-bit lane, giving `a`'s byte 16 (not byte 0). -/
example :
    let a := yOfBytesW (fun i => BitVec.ofNat 8 i.val);
    let ctl := yOfBytesW (fun i => if i.val = 0 then 3 else if i.val = 1 then 0x80 else 0);
    let r := YmmOp.denote .vpshufb a ctl;
    (yByteW r 0 = 3) ∧ (yByteW r 1 = 0) ∧ (yByteW r 16 = 16) := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
