/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

-- The closed-kernel route reduces the front (`translateDialectControl`,
-- `cryptoDialectToJasminCom`) by `rfl`/`decide`; under the module system that
-- reduction needs the front closure imported with `all`, and `Nat.repr` (the
-- front's slot names) exposed through `Init.Data.Repr`.
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
import all CatCrypt.Crypto.Hax.RustSubsetToLowCT
public import CatCrypt.Crypto.SecureCompilation.Ascent.LegWeld
public import CatCrypt.Crypto.SecureCompilation.Dialects.RustExecRoundAdeq

/-!
# A kernel through the generic leg weld: `r0 := a0 + b0 - c0`

The closed straight-line kernel `r0 := a0 + b0 - c0`, written as a `RustSrc`
source with its three inputs as literals, welded from the source semantics to
the emitted jasmin bytes by `LegWeld.legWeld_lower`. The `LowCT` term is the
verified lowering `lower demoSrc` itself, so the program identity to the
descent's term is `LitNorm.refl`.

The per-kernel data is: the source `demoSrc`; its run `demo_run` (each literal a
`u64`, the arithmetic in range at the state it reads); the closed-kernel scoping
`demoC_readsOK` / `demoC_out`; the front's artifacts `demoFront` from the five
success facts; and the ascent correspondence `demo_corres`, assembled from the
value leaf `corres_setExpr` by `corres_seq`. `demo_source_to_bytes` is the weld
instance.

## Main definitions

* `demoSrc`, `demoC` — the source and its lowering
* `demoFront` — the front's artifacts
* `demo_corres` — the ascent correspondence
* `demo_source_to_bytes` — the closed capstone
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 10000

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (Ctx)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
  (translateDialectControl)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVar)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge (readsOK afterB varsBoundIn)
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecRoundAdeq (not_isTmp_short)
open CatCrypt.Crypto.Hax.RustSubsetToLowCT (RustSrc lower)

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## The source and its lowering -/

/-- First literal input `a0`. -/
def dav : Nat := 1634760805
/-- Second literal input `b0`. -/
def dbv : Nat := 857760878
/-- Third literal input `c0`. -/
def dcv : Nat := 2036477234

/-- The expression `a0 + b0 - c0`. -/
def demoE : SExpr := .SSub (.SAdd (.SVar "a0") (.SVar "b0")) (.SVar "c0")

/-- The source: write the three literal inputs, then `r0 := a0 + b0 - c0`. -/
def demoSrc : RustSrc :=
  .letE "a0" (.SLit dav)
    (.letE "b0" (.SLit dbv)
      (.letE "c0" (.SLit dcv)
        (.assign "r0" demoE)))

/-- The `LowCT` term: the verified lowering of the source. -/
def demoC : LowCT := lower demoSrc

theorem demoE_arithClean : IsArithClean demoE :=
  ⟨⟨not_isTmp_short "a0" (by decide), not_isTmp_short "b0" (by decide)⟩,
    not_isTmp_short "c0" (by decide)⟩

/-- The run from the default state: the three literals are `u64`, and
    `a0 + b0 - c0` is in range at the state it reads. -/
theorem demo_run : ∃ rs', AdeqRun demoC default rs' :=
  ⟨_, .rSeq (.lit (by decide))
    (.rSeq (.lit (by decide))
      (.rSeq (.lit (by decide))
        (.rScalarSetExpr (isArithClean_srcClean _ demoE_arithClean)
          (by simp only [demoE, SExpr.inRange, SExpr.eval]; decide))))⟩

/-- Every read of `demoC` follows a write. -/
theorem demoC_readsOK : readsOK (fun _ => False) demoC := by
  simp [readsOK, afterB, varsBoundIn, demoC, demoSrc, lower, demoE]

/-- `r0` is written by `demoC`. -/
theorem demoC_out : afterB (fun _ => False) demoC "r0" := by
  simp [afterB, demoC, demoSrc, lower]

/-! ## The front's artifacts -/

theorem demoTrans : (translateDialectControl VarMap.empty demoC).isSome := by rfl

theorem demoName : ((frontO demoC demoTrans).vm.lookup "r0").isSome := by rfl

/-- The tracked slot's type is the 64-bit word, decided since the slot name goes
    through `Nat.repr`. -/
theorem demoNameTy : (((frontO demoC demoTrans).vm.lookup "r0").get demoName).1 = .sword 64 := by
  decide

theorem demoRet :
    ((frontO demoC demoTrans).cont
      (Com.ret (toVIRVar (frontW demoC "r0" demoTrans demoName demoNameTy)))).isSome := by
  rfl

theorem demoJcom :
    (cryptoDialectToJasminCom (frontCom demoC "r0" demoTrans demoName demoNameTy demoRet)).isSome := by
  rfl

/-- The front's artifacts for `demoC` closed at `r0`. -/
noncomputable def demoFront : FrontOut demoC "r0" :=
  .ofSome demoC "r0" demoTrans demoName demoNameTy demoRet demoJcom

/-! ## The ascent correspondence -/

/-- The composite abstract map: the three literal writes, then `r0 := a0 + b0 - c0`
    on `ZMod 2^64`. -/
def demoFa : (String → ZMod (2 ^ 64)) → (String → ZMod (2 ^ 64)) :=
  fun a =>
    (fun φ s => if s = "r0" then evalZMod φ demoE else φ s)
      ((fun φ s => if s = "c0" then evalZMod φ (.SLit dcv) else φ s)
        ((fun φ s => if s = "b0" then evalZMod φ (.SLit dbv) else φ s)
          ((fun φ s => if s = "a0" then evalZMod φ (.SLit dav) else φ s) a)))

theorem demo_corres : Corres SRwordNT (fun _ => True) demoFa demoC := by
  have h := corres_seq SRwordNT (corres_setExpr "a0" (.SLit dav) (show dav < 2 ^ 64 by decide))
    (corres_seq SRwordNT (corres_setExpr "b0" (.SLit dbv) (show dbv < 2 ^ 64 by decide))
      (corres_seq SRwordNT (corres_setExpr "c0" (.SLit dcv) (show dcv < 2 ^ 64 by decide))
        (corres_setExpr "r0" demoE demoE_arithClean)
        (fun _ _ => trivial))
      (fun _ _ => trivial))
    (fun _ _ => trivial)
  exact h

/-- The composite abstract map at `r0` is the field expression on the literals. -/
theorem demoFa_at_r0 (a : String → ZMod (2 ^ 64)) :
    demoFa a "r0"
      = ((dav : Nat) : ZMod (2 ^ 64)) + ((dbv : Nat) : ZMod (2 ^ 64))
        - ((dcv : Nat) : ZMod (2 ^ 64)) := by
  simp [demoFa, demoE, evalZMod]

/-! ## The capstone -/

/-- **`demo_source_to_bytes`.** For the kernel `r0 := a0 + b0 - c0` with literal
    inputs, the emitted jasmin program denotes to the `ctTransTy` image of the
    source semantics' output word, and that word's `ZMod 2^64` readout is
    `dav + dbv - dcv`. The instance of `legWeld_lower` at `demoSrc`. -/
theorem demo_source_to_bytes :
    demoFront.jcom.denote (ctMapValD (.nil : Ctxt.Valuation (d := catCryptDialect) ([] : Ctx)))
        = ctTransTy (BitVec.ofNat 64 (RustSrc.exec demoSrc (fun _ => 0) "r0"))
      ∧ wEnc (BitVec.ofNat 64 (RustSrc.exec demoSrc (fun _ => 0) "r0"))
          = ((dav : Nat) : ZMod (2 ^ 64)) + ((dbv : Nat) : ZMod (2 ^ 64))
            - ((dcv : Nat) : ZMod (2 ^ 64)) := by
  have h := legWeld_lower demoSrc (by decide)
    (by simp [demoSrc, demoE, RustSrc.limbFree, SExpr.limbFree])
    (.refl _) demo_run scalarInRange_default "r0"
    (not_isTmp_short "r0" (by decide)) demoC_readsOK demoC_out demoFront demoFa (fun _ => True)
    demo_corres trivial
  exact ⟨h.1, h.2.trans (demoFa_at_r0 _)⟩

end CatCrypt.Crypto.SecureCompilation.Ascent

#print axioms CatCrypt.Crypto.SecureCompilation.Ascent.demo_source_to_bytes
