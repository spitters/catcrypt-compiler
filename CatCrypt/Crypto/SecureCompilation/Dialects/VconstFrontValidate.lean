/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd
public meta import CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint
public import CatCrypt.Crypto.SecureCompilation.VIR.VsimdAsmPrint


@[expose] public section
set_option autoImplicit false

/-!
# End-to-end validate: a BAKED 128-bit XMM constant through the `vsimd` front

Capability G1 — the `vconst128` op — lets a SIMD kernel bake a compile-time
128-bit immediate (the FAEST GF(2^128) reduction modulus / `alpha_i`, an AES
round constant, a `vpshufb` shuffle mask) directly into the emitted `.s`, instead
of ABI-loading it as a `.sword 128` parameter. Before this op, `bvConst 128`
lowered to a scalar `regConst` (a GP `MOV` of a 128-bit immediate) that the owned
`vsimd` printer could not render (`# <unsupported …>`), so a 128-bit constant had
to enter through the ABI.

This file is the front-arm correctness gate for that op, the baked-constant twin
of `TranslateDialectVsimd`'s `vBody` validate. A one-input body
(`out := inp ⊕ 0x0102030405060708090a0b0c0d0e0f87`) written with the dedicated
vector node `RVsimdSetExpr` — the constant carried in the `"vsimd.vconst.<hex>"`
tag, NO operand — is pushed through the vector front and shown to:

1. **translate** through `translateDialectControlV`;
2. **lower** end-to-end to `Com jasminDialect` through the verified
   `cryptoDialectToJasminCom` (reaching owned `.s`);
3. **render** through `renderVsimdComAuto` to owned AT&T `.s` whose constant load
   is the real `movabsq`/`vmovq`/`vpinsrq` two-64-bit-half XMM build (NOT a scalar
   `# <unsupported …>` line); and
4. **denote = spec** on sample 128-bit inputs (`inp ⊕ const`).
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.VconstFrontValidate

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
  (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 1. The baked-constant body -/

/-- The baked 128-bit constant, as a hex tag. `0x0102030405060708090a0b0c0d0e0f87`
    exercises BOTH 64-bit halves of the `movabsq`/`vpinsrq` build (hi =
    `0x0102030405060708`, lo = `0x090a0b0c0d0e0f87`); the low byte `0x87` is the
    GF(2^128) reduction-polynomial byte the FAEST/GHASH kernels need. -/
def cTag : String := "vsimd.vconst.0x0102030405060708090a0b0c0d0e0f87"

/-- The same constant as a `BitVec 128` (for the spec side). -/
def cVal : BitVec 128 := 0x0102030405060708090a0b0c0d0e0f87

/-- One 128-bit vector param `inp` (`.here`). -/
def cΓ : Ctx := [.sword 128]

/-- `VarMap` binding the single input `inp`. -/
def cVM : VarMap cΓ := VarMap.empty.bind "inp"

/-- A baked-constant body: `c := 0x…0f87` (nullary vconst); `out := inp ⊕ c`. -/
def cBody : LowCT :=
  .RSeq (LowCT.RVsimdSetExpr "c"   cTag         [])
        (LowCT.RVsimdSetExpr "out" "vsimd.xor"  ["inp", "c"])

/-- Both ops are vsimd-tagged (the `vconst` hex parses, `xor` parses). -/
theorem cBody_covered : IsCoveredV cBody :=
  .rSeq (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))
        (isCoveredV_RVsimdSetExpr _ _ _ (by native_decide))

/-! ## 2. Translate + lower -/

/-- (1) The body translates through the vector front. -/
theorem cBody_translates : (translateDialectControlV cVM cBody).isSome := by
  native_decide

/-- The front-emitted result program (returns the `.sword 128` slot `out`). -/
def cProg : Option (Com catCryptDialect cΓ (.sword 128)) :=
  vsimdResultProg cVM cBody "out"

/-- The front actually emits a result program. -/
theorem cProg_isSome : cProg.isSome := by native_decide

/-- The lowered Jasmin-dialect program (through the verified
    `cryptoDialectToJasminCom`, reaching owned `.s`). -/
def cProgJ : Option (Com jasminDialect (mapCtx cΓ) (mapTy (.sword 128))) :=
  cProg.bind cryptoDialectToJasminCom

/-- (2) It lowers end-to-end to `Com jasminDialect`. -/
theorem cProg_lowers : cProgJ.isSome := by native_decide

/-! ## 3. Render to owned AT&T `.s`: the real constant load -/

/-- The owned AT&T `.s` body lines, register-allocated automatically. -/
def cAsm : List String :=
  match cProgJ with
  | some j => (VsimdAsmPrint.renderVsimdComAuto j).1
  | none => []

/-- (3a) The rendered `.s` contains a REAL 128-bit constant load — the
    `movabsq`/`vmovq`/`vpinsrq` two-64-bit-half XMM build — for both halves. -/
example : cAsm.any (fun l => strContains l "movabsq") = true := by native_decide
example : cAsm.any (fun l => strContains l "vmovq") = true := by native_decide
example : cAsm.any (fun l => strContains l "vpinsrq $1") = true := by native_decide

/-- (3b) The two constant halves are the real hi/lo 64-bit words of `cVal`
    (`hi = 0x0102030405060708 = 72623859790382856`, `lo = 0x090a0b0c0d0e0f87 =
    651345242494996359`). -/
example : cAsm.any (fun l => strContains l "651345242494996359") = true := by
  native_decide
example : cAsm.any (fun l => strContains l "72623859790382856") = true := by
  native_decide

/-- (3c) Nothing rendered as the scalar-GP `# <unsupported …>` fragment-boundary
    comment — the const lowered and was not declined. -/
example : cAsm.any (fun l => strContains l "unsupported") = false := by
  native_decide

/-- (3d) The XOR of the input with the baked constant renders too
    (`vpxor …`). -/
example : cAsm.any (fun l => strContains l "vpxor") = true := by native_decide

/-! ## 4. `denote = spec` on sample 128-bit inputs -/

/-- The pure-Lean spec: `inp ⊕ const`. -/
def cSpec (a : BitVec 128) : BitVec 128 := a ^^^ cVal

/-- Denote the front-emitted program at input `a` (slot `inp`). -/
def cDenote (a : BitVec 128) : Option (BitVec 128) :=
  cProg.map (fun com => com.denote (.cons a .nil))

example : cDenote 0 = some (cSpec 0) := by native_decide

example : cDenote 0xffffffffffffffffffffffffffffffff
    = some (cSpec 0xffffffffffffffffffffffffffffffff) := by native_decide

example : cDenote 0x00112233445566778899aabbccddeeff
    = some (cSpec 0x00112233445566778899aabbccddeeff) := by native_decide

/-- Sanity: the front bakes the constant itself — denoting at input `0` returns
    exactly the baked value `cVal` (`0 ⊕ const = const`). -/
example : cDenote 0 = some cVal := by native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.VconstFrontValidate
