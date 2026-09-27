/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

-- The closed-kernel route reduces the front (`translateDialectControl`,
-- `semScalar`, `cryptoDialectToJasminCom`) by `rfl`/`decide`; under the module
-- system that reduction needs the front closure imported with `all`, and
-- `Nat.repr` (the front's slot names) exposed through `Init.Data.Repr`.
import all Init.Data.Repr
import all CatCrypt.Core.Code
import all CatCrypt.Crypto.CryptoWord
import all CatCrypt.Crypto.Jasmin.JasminAST
import all CatCrypt.Crypto.Jasmin.JasminTypes
import all CatCrypt.Crypto.Jasmin.LowCT
import all CatCrypt.Crypto.SDist
import all CatCrypt.Crypto.SecureCompilation.CryptoSSA
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
import all CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
import all CatCrypt.Crypto.SecureCompilation.Dialects.RustExecKernelAdeq
import all CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
import all CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.Core
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecKernelAdeq
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecRoundAdeq

/-!
# A 64-bit ARX kernel and its coverage by the straight-line front

The kernel is

```
a := 0x12345678 ; b := 0x11111111
s := ((a ≪ 8) ⊕ (a ≫ 56)) + b
```

where `(a ≪ 8) ⊕ (a ≫ 56)` is `rotl64(a, 8)` in XOR form and `+ b` is addition
modulo `2^64`. `arxC_covered` states `IsCoveredSCtl arxC`: the front
`translateDialectControl` accepts the kernel, and its `RScalarSetExpr` arm requires
only `srcClean`.

The value of this kernel on arbitrary 64-bit inputs is the value under `semScalar`,
which wraps at the width. `RustExec` evaluates `SShl` and `SAdd` over unbounded
naturals; for `a ≥ 2^56` its value is not the rotation, and for sums `≥ 2^64` it is
not the modular sum. `RustExec` agrees with `semScalar` only under the in-range
hypothesis of `SExpr.evalBV_eq_ofNat_eval`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.VIR.CompilerCorrectnessExtracted
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecRoundAdeq (not_isTmp_short)

namespace CatCrypt.Crypto.SecureCompilation.Dialects.RustExecARXAdeq

/-! ## The ARX round expression: `rotl64(a,8) ⊕-form + b` -/

/-- `((a ≪ 8) ⊕ (a ≫ 56)) + b` — one rotate (in `⊕`-form) and one modular add,
    the two residual ARX arms of a SHA-2 round. -/
def arxE : SExpr :=
  .SAdd (.SXor (.SShl (.SVar "a") (.SLit 8)) (.SShr (.SVar "a") (.SLit 56)))
    (.SVar "b")

/-! ## The closed kernel -/

/-- The closed ARX kernel: write the two inputs as literals (`a` the SHA-256 IV
    word `0x12345678`-shaped, `b` a round constant), then compute the ARX round
    core `s`. -/
def arxC : LowCT :=
  .RSeq (.RScalarSet "a" 305419896)
    (.RSeq (.RScalarSet "b" 286331153)
      (.RScalarSetExpr "s" arxE))

/-! ## Coverage: `IsCoveredSCtl arxC` (needs only `srcClean` — no `inRange`) -/

theorem arxE_srcClean : srcClean arxE :=
  ⟨⟨⟨not_isTmp_short "a" (by decide), by norm_num [srcClean]⟩,
      ⟨not_isTmp_short "a" (by decide), by norm_num [srcClean]⟩⟩,
    not_isTmp_short "b" (by decide)⟩

theorem arxC_coveredS : IsCoveredS arxC :=
  .rSeq (.rScalarSet "a" _)
    (.rSeq (.rScalarSet "b" _)
      (.rScalarSetExpr "s" arxE arxE_srcClean))

theorem arxC_covered : IsCoveredSCtl arxC := .ofStraight arxC_coveredS

end CatCrypt.Crypto.SecureCompilation.Dialects.RustExecARXAdeq
