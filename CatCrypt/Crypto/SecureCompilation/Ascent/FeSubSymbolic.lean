/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

-- The front (`translateDialectControl`, `cryptoDialectToJasminCom`) is reduced by
-- `rfl`/`decide` on the kernel below; under the module system that reduction
-- needs the front closure imported with `all`, and `Nat.repr` (the front's slot
-- names) exposed through `Init.Data.Repr`.
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
import all CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
import all CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.Core
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresScalar

/-!
# A word kernel with symbolic inputs, from `LowCT` to `Com jasminDialect`

The scalar weld `corresScalar_frontDenote` concludes a `Com catCryptDialect`
denotation at an arbitrary entry valuation. This module lowers it one step, through
`cryptoDialectToJasminCom`, and instantiates it for the subtraction kernel
`r := a - b` whose inputs `a` and `b` are read from the entry valuation.

## The entry environment

`corresScalar_frontDenote` asks for one scalar environment that is consistent with
the entry valuation through the entry map (`ConsistentS`) and related to the
abstract state on every non-temp name (`SRwordBV`). `valEnv vm V` is the
environment the valuation induces through the map, so `ConsistentS` holds by
definition; `SRwordBV` then holds when the map resolves every non-temp name to a
word slot carrying the abstract value (`srwordBV_valEnv`).

For the kernel, the map `vmSubAll` sends `b` to the second slot and every other
name to the first. The front's output for it coincides with its output at the map
`vmAB`, which tracks only `a` and `b` (`comSubAll_eq`, by `rfl`), so the capstone is
stated at `vmAB`.

## Main definitions

* `valEnv` — the scalar environment a valuation induces through an entry map
* `feSubSymC` — the kernel `r := a - b` over two input names
* `vmAB`, `valAB` — the entry map and valuation holding `a`, `b`
* `feSubSymCom`, `feSubSymJcom` — the front's `Com catCryptDialect` and
  `Com jasminDialect` programs for `feSubSymC` at `vmAB`, returning `r`

## Main results

* `corresScalar_jasminDenote` — `corresScalar_frontDenote` lowered through
  `cryptoDialectToJasminCom`, with the entry environment `valEnv vm V`
* `feSub_symbolic_frontDenote` — `feSubSymCom.denote (valAB a b) = a - b`
* `feSub_symbolic_source_to_jasmin` —
  `feSubSymJcom.denote (ctMapValD (valAB a b)) = ctTransTy (a - b)`, for all `a`, `b`
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 10000

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy CVar Ctx)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect (DTransOut)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
  (translateDialectControl)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVar)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
  (ctMapValD cryptoDialectToJasminCom_denote_eq')

namespace CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## 1. The weld lowered to `Com jasminDialect` -/

/-- The scalar environment a valuation `V` induces through the entry map `vm`: each
    name resolved by `vm` holds the value of its slot in `V`, and every other name is
    unbound. -/
def valEnv {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ) :
    SEnvScalar :=
  fun s => (vm.lookup s).map
    (fun p => (⟨p.1, (toVIRVar p.2).lookup V⟩ : (t : CryptoTy) × ⟦t⟧))

/-- The induced environment is consistent with the valuation through the map. -/
theorem consistentS_valEnv {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) : ConsistentS vm V (valEnv vm V) :=
  fun _ => rfl

/-- The induced environment is `SRwordBV`-related to `a` when `vm` resolves every
    non-temp name `x` to a word slot whose value in `V` is `a x`. -/
theorem srwordBV_valEnv {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (a : String → BitVec 64)
    (hA : ∀ x, ¬ isTmpName x → ∃ w : CVar Γ (.sword 64),
      vm.lookup x = some ⟨.sword 64, w⟩ ∧ (toVIRVar w).lookup V = a x) :
    SRwordBV (valEnv vm V) a := by
  intro x hx
  obtain ⟨w, hw, hv⟩ := hA x hx
  simp only [valEnv, hw, Option.map_some, hv]

/-- **The scalar weld at `Com jasminDialect`.** For an `IsCoveredSCtl` kernel `c`
    with a `Corres SRwordBV` result `fa`, an entry map `vm` resolving every non-temp
    name `x` to a word slot whose value in the entry valuation `V` is `a x`, and the
    front's translation of `c` at `vm` closed at the non-temp name `dst` and lowered
    to `jcom`: the jasmin program denotes, at the transported valuation
    `ctMapValD V`, the transport of the abstract value `fa a dst`.
    `corresScalar_frontDenote` at the entry environment `valEnv vm V`, composed with
    `cryptoDialectToJasminCom_denote_eq'`. -/
theorem corresScalar_jasminDenote
    {c : LowCT} (hcov : IsCoveredSCtl c)
    {fa : (String → BitVec 64) → (String → BitVec 64)}
    (hcorr : Corres SRwordBV (fun _ => True) fa c)
    {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (a : String → BitVec 64)
    (hA : ∀ x, ¬ isTmpName x → ∃ w : CVar Γ (.sword 64),
      vm.lookup x = some ⟨.sword 64, w⟩ ∧ (toVIRVar w).lookup V = a x)
    (o : DTransOut Γ) (htr : translateDialectControl vm c = some o)
    (dst : String) (hdst : ¬ isTmpName dst)
    (w : CVar o.Γ' (.sword 64)) (hw : o.vm.lookup dst = some ⟨.sword 64, w⟩)
    (com : Com catCryptDialect Γ (.sword 64))
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy (.sword 64)))
    (hCom : cryptoDialectToJasminCom com = some jcom) :
    jcom.denote (ctMapValD V) = ctTransTy (fa a dst) := by
  rw [cryptoDialectToJasminCom_denote_eq' com V jcom hCom,
    corresScalar_frontDenote hcov hcorr vm V (valEnv vm V) a (consistentS_valEnv vm V)
      (srwordBV_valEnv vm V a hA) o htr dst hdst w hw com hRet]

/-! ## 2. The kernel `r := a - b` and its front artifacts -/

/-- The subtraction kernel `r := a - b`, reading its inputs `a`, `b`. -/
def feSubSymC : LowCT := .RScalarSetExpr "r" (.SSub (.SVar "a") (.SVar "b"))

theorem feSubSymC_covered : IsCoveredSCtl feSubSymC :=
  .ofStraight (.rScalarSetExpr _ _
    ⟨notTmp_of_short "a" (by decide), notTmp_of_short "b" (by decide)⟩)

/-- The entry context of two words. -/
abbrev ctxAB : Ctx := [.sword 64, .sword 64]

/-- The entry map tracking `a` at the first slot and `b` at the second. -/
def vmAB : VarMap ctxAB :=
  ⟨fun s => if s = "a" then some ⟨.sword 64, .here⟩
    else if s = "b" then some ⟨.sword 64, .there .here⟩ else none⟩

/-- The entry map sending `b` to the second slot and every other name to the first. -/
def vmSubAll : VarMap ctxAB :=
  ⟨fun s => if s = "b" then some ⟨.sword 64, .there .here⟩ else some ⟨.sword 64, .here⟩⟩

/-- The entry valuation holding `a` at the first slot and `b` at the second. -/
def valAB (a b : BitVec 64) : Ctxt.Valuation (d := catCryptDialect) ctxAB :=
  .cons a (.cons b .nil)

/-- The transported jasmin valuation holds the transported inputs at the same slots. -/
theorem ctMapValD_valAB (a b : BitVec 64) :
    ctMapValD (valAB a b) = .cons (ctTransTy a) (.cons (ctTransTy b) .nil) := rfl

theorem feSubSymTransSome : (translateDialectControl vmAB feSubSymC).isSome := by rfl

theorem feSubSymAllTransSome : (translateDialectControl vmSubAll feSubSymC).isSome := by rfl

/-- The front's translation output of `feSubSymC` at `vmAB`. -/
noncomputable def feSubSymO : DTransOut ctxAB :=
  (translateDialectControl vmAB feSubSymC).get feSubSymTransSome

/-- The front's translation output of `feSubSymC` at `vmSubAll`. -/
noncomputable def feSubSymAllO : DTransOut ctxAB :=
  (translateDialectControl vmSubAll feSubSymC).get feSubSymAllTransSome

theorem feSubSymNameSome : (feSubSymO.vm.lookup "r").isSome := by rfl

theorem feSubSymNameTy : ((feSubSymO.vm.lookup "r").get feSubSymNameSome).1 = .sword 64 := by
  decide

theorem feSubSymAllNameSome : (feSubSymAllO.vm.lookup "r").isSome := by rfl

theorem feSubSymAllNameTy :
    ((feSubSymAllO.vm.lookup "r").get feSubSymAllNameSome).1 = .sword 64 := by
  decide

/-- The slot of `r` in the translation output at `vmAB`. -/
noncomputable def feSubSymW : CVar feSubSymO.Γ' (.sword 64) :=
  cast (congrArg (CVar feSubSymO.Γ') feSubSymNameTy)
    ((feSubSymO.vm.lookup "r").get feSubSymNameSome).2

/-- The slot of `r` in the translation output at `vmSubAll`. -/
noncomputable def feSubSymAllW : CVar feSubSymAllO.Γ' (.sword 64) :=
  cast (congrArg (CVar feSubSymAllO.Γ') feSubSymAllNameTy)
    ((feSubSymAllO.vm.lookup "r").get feSubSymAllNameSome).2

theorem feSubSymHName : feSubSymO.vm.lookup "r" = some ⟨.sword 64, feSubSymW⟩ := by decide

theorem feSubSymAllHName :
    feSubSymAllO.vm.lookup "r" = some ⟨.sword 64, feSubSymAllW⟩ := by decide

theorem feSubSymRetSome : (feSubSymO.cont (Com.ret (toVIRVar feSubSymW))).isSome := by rfl

theorem feSubSymAllRetSome :
    (feSubSymAllO.cont (Com.ret (toVIRVar feSubSymAllW))).isSome := by rfl

/-- The front's `Com catCryptDialect` program for `feSubSymC` at `vmAB`, returning `r`. -/
noncomputable def feSubSymCom : Com catCryptDialect ctxAB (.sword 64) :=
  (feSubSymO.cont (Com.ret (toVIRVar feSubSymW))).get feSubSymRetSome

/-- The front's `Com catCryptDialect` program for `feSubSymC` at `vmSubAll`, returning
    `r`. -/
noncomputable def feSubSymAllCom : Com catCryptDialect ctxAB (.sword 64) :=
  (feSubSymAllO.cont (Com.ret (toVIRVar feSubSymAllW))).get feSubSymAllRetSome

/-- The front produces the same program at `vmSubAll` as at `vmAB`. -/
theorem comSubAll_eq : feSubSymAllCom = feSubSymCom := by rfl

theorem feSubSymComSome : (cryptoDialectToJasminCom feSubSymCom).isSome := by rfl

/-- The jasmin lowering of `feSubSymCom`. -/
noncomputable def feSubSymJcom : Com jasminDialect (mapCtx ctxAB) (mapTy (.sword 64)) :=
  (cryptoDialectToJasminCom feSubSymCom).get feSubSymComSome

theorem feSubSymHCom : cryptoDialectToJasminCom feSubSymCom = some feSubSymJcom :=
  (Option.some_get feSubSymComSome).symm

/-! ## 3. The capstone for all inputs -/

/-- The word correspondence of `feSubSymC`: `r` is set to `a - b` evaluated over the
    abstract state. -/
theorem feSubSym_corres :
    Corres SRwordBV (fun _ => True)
      (fun a s => if s = "r" then SExpr.evalBV a (.SSub (.SVar "a") (.SVar "b")) else a s)
      feSubSymC := by
  unfold feSubSymC
  corres_solve_scalar

/-- `vmSubAll` resolves every name to a word slot whose value in `valAB a b` is `b`
    at the name `b` and `a` elsewhere. -/
theorem vmSubAll_resolves (a b : BitVec 64) :
    ∀ x, ¬ isTmpName x → ∃ w : CVar ctxAB (.sword 64),
      vmSubAll.lookup x = some ⟨.sword 64, w⟩ ∧
        (toVIRVar w).lookup (valAB a b) = (fun s => if s = "b" then b else a) x := by
  intro x _
  by_cases hx : x = "b"
  · subst hx
    exact ⟨.there .here, rfl, rfl⟩
  · exact ⟨.here, by simp only [vmSubAll, if_neg hx], by simp only [if_neg hx]; rfl⟩

/-- **The kernel at the `Com jasminDialect` level, for all inputs.** The jasmin
    program the front and `cryptoDialectToJasminCom` produce for `r := a - b` at the
    entry map `vmAB` denotes, at the transported valuation holding `a` and `b`, the
    transport of the wrapping difference `a - b`. -/
theorem feSub_symbolic_source_to_jasmin (a b : BitVec 64) :
    feSubSymJcom.denote (ctMapValD (valAB a b)) = ctTransTy (a - b) := by
  have h := corresScalar_jasminDenote feSubSymC_covered feSubSym_corres vmSubAll
    (valAB a b) _ (vmSubAll_resolves a b) feSubSymAllO
    (Option.some_get feSubSymAllTransSome).symm "r" (notTmp_of_short "r" (by decide))
    feSubSymAllW feSubSymAllHName feSubSymCom
    (comSubAll_eq ▸ (Option.some_get feSubSymAllRetSome).symm) feSubSymJcom feSubSymHCom
  rw [h]
  simp [SExpr.evalBV]

/-- **The kernel at the `Com catCryptDialect` level, for all inputs.** The front's
    program for `r := a - b` at `vmAB` denotes `a - b` at the valuation holding `a`
    and `b`. -/
theorem feSub_symbolic_frontDenote (a b : BitVec 64) :
    feSubSymCom.denote (valAB a b) = a - b := by
  rw [← comSubAll_eq,
    corresScalar_frontDenote feSubSymC_covered feSubSym_corres vmSubAll (valAB a b)
      (valEnv vmSubAll (valAB a b)) _ (consistentS_valEnv _ _)
      (srwordBV_valEnv _ _ _ (vmSubAll_resolves a b)) feSubSymAllO
      (Option.some_get feSubSymAllTransSome).symm "r" (notTmp_of_short "r" (by decide))
      feSubSymAllW feSubSymAllHName feSubSymAllCom (Option.some_get feSubSymAllRetSome).symm]
  simp [SExpr.evalBV]

end CatCrypt.Crypto.SecureCompilation.Ascent
