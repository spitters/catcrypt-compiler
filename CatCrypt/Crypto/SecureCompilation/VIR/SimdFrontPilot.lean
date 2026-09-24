/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect

/-!
# SIMD ext-op FRONT: inlined `vsimd` op validate (Route B)

The front carries vector values and SIMD ops:
`CatCryptOp.vsimd (op : SimdOp)` (binary) + the unary `vpshufdC`/`vaeskeygenC`/
`vpsrldqC`/`vpslldqC` front ops carry a 128-bit vector value as `.sword 128`
(`mapTy → reg 128`), denote via the backend `SimdOp.denote` waist, and lower 1:1
through `DialectToJasminCom.toJExprD` to the matching `JasminOp.vsimd`/`vpsrldq`/
`vpslldq` — the same owned x86 backend the 128-bit vsimd kernels render through.

This module validates the OWNED route: a
`.vsimd .gf2p8mulb` op in a `Com catCryptDialect` body that

  1. TRANSLATES + LOWERS: `cryptoDialectToJasminCom` returns `some`
     (`.vsimd .gf2p8mulb` maps to jasmin `.vsimd .gf2p8mulb`, an INLINED GFNI
     instruction — not a `call gf2p8mulb` leaf as the `extCall` Route A gave); and
  2. DENOTE = SPEC: the front body denotes to the 16-lane GF(256) product
     `gf2p8mulbW` (`= SimdOp.denote .gf2p8mulb`), the AES-poly GFNI multiply.

The lowering is the VERIFIED `cryptoDialectToJasminCom` map
(`cryptoDialectToJasminCom_denote_eq'` proves it preserves denotation on this
fragment), so the Com is authored in the FRONT dialect and lowered by the
verified map — no hand-authored `Com jasminDialect`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.SimdFrontPilot

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect SimdOp gf2p8mulbW)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-- Context `[a, b]`, each a 128-bit vector carried as `.sword 128`. -/
abbrev gfCtx : Ctx := [.sword 128, .sword 128]

def vA : Ctxt.Var (d := catCryptDialect) gfCtx (.sword 128) := .here
def vB : Ctxt.Var (d := catCryptDialect) gfCtx (.sword 128) := .there .here

/-- The GFNI 16-lane GF(256) multiply expressed as a real FRONT-dialect
    `.vsimd .gf2p8mulb` op (the OWNED inlined route, not an `extCall` leaf). -/
def eMulV : Expr catCryptDialect gfCtx (.sword 128) :=
  .mk (.vsimd .gf2p8mulb) rfl (.cons vA (.cons vB .nil))

/-- A one-op front body: `prod := gf2p8mulb(a, b)` then return. -/
def gfMulComCD : Com catCryptDialect gfCtx (.sword 128) :=
  .var eMulV (.ret .here)

/-! ## 1. Translates + lowers (the OWNED inlined route) -/

/-- The front body lowers through the VERIFIED `cryptoDialectToJasminCom` map. -/
theorem gfMulComCD_isSome : (cryptoDialectToJasminCom gfMulComCD).isSome := by
  native_decide

/-- The lowered Jasmin-dialect program (in the `mapTy`-mapped context). -/
def gfMulComJ : Com jasminDialect (mapCtx gfCtx) (mapTy (.sword 128)) :=
  (cryptoDialectToJasminCom gfMulComCD).get gfMulComCD_isSome

/-! ## 2. Denote = spec -/

/-- A concrete valuation builder for `gfCtx`. -/
def gfVal (a b : BitVec 128) : Ctxt.Valuation (d := catCryptDialect) gfCtx :=
  .cons a (.cons b .nil)

/-- **Front `denote = spec` (symbolic).** On `[a, b]` the front body denotes to the
    16-lane GF(256) product `gf2p8mulbW a b` — the AES-poly GFNI multiply. `rfl`
    (the `.vsimd .gf2p8mulb` denote IS the `SimdOp.denote .gf2p8mulb = gf2p8mulbW`
    waist). -/
theorem gfMulComCD_denote (a b : BitVec 128) :
    gfMulComCD.denote (gfVal a b) = gf2p8mulbW a b := rfl

end CatCrypt.Crypto.SecureCompilation.VIR.SimdFrontPilot
