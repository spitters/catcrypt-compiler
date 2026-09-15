/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

-- The closed instance reduces the front (`transU`, `semU`) by `rfl`/`decide`; under
-- the module system that reduction needs the front closure imported with `all`, and
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
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhileDenote
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectCondDenote
import all CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectUnifiedDenote
import all CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
import all CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
import all CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.Core
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
import all CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore
public import CatCrypt.Crypto.SecureCompilation.Ascent.WhileFunEmit
public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.WhileFunSum

/-!
# Demo: the summation do-while compiled to a jasmin `Com`

The kernel is `sumLoop` (`Ascent/Demos/WhileFunSum.lean`), the `LowCT` do-while
`do { acc := acc + k; k := k - 1 } while (k != 0)`. The front's unified descent
`transU` compiles it from an entry map that tracks `k` at the first slot and `acc`
at the second, and `cryptoDialectToJasminCom` lowers the result to a jasmin `Com`.
The statements below are about the denotation of that `Com`; they say nothing
about emitted assembly or bytes.

`sumLoop_jasminDenote` is `corresU_whileFun_jasminDenote_word` at `sumLoop`: for
every entry `k ≠ 0` and `acc`, and every front output at that entry, the jasmin
program returning the `acc` slot denotes `acc + k (k + 1) / 2`, the value
`sum_loopFun` gives for the abstract loop. The trip count and the front output
depend on `k`, so the theorem takes the front's output as hypotheses, as
`legWeld` does. `sumLoop3_jasminDenote` closes them at `k = 3`, `acc = 0`: the
front and the lowering are run by kernel evaluation, and the value `6` is read
off `sumLoop_jasminDenote`, not off a run of the jasmin program.

## Main results

* `sumBody_coveredSU`: the loop body lies in the unified fragment `IsCoveredSU`
* `sumLoop_jasminDenote`: the jasmin program of `sumLoop` at entry `(k, acc)` with
  `k ≠ 0` denotes `acc + k (k + 1) / 2`
* `sumLoop3_jasminDenote`: at `k = 3`, `acc = 0` the front-compiled and lowered
  program `sum3Jcom` denotes `6`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (Ctx CVar)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVar)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect (DTransOut)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Ascent

/-! ## 1. The entry: two word slots, `k` first and `acc` second -/

/-- The entry context of two words. -/
abbrev ctxKA : Ctx := [.sword 64, .sword 64]

/-- The entry map sending `acc` to the second slot and every other name to the first. -/
def vmSumAll : VarMap ctxKA :=
  ⟨fun s => if s = "acc" then some ⟨.sword 64, .there .here⟩ else some ⟨.sword 64, .here⟩⟩

/-- The entry valuation holding `k` at the first slot and `acc` at the second. -/
def valKA (k acc : BitVec 64) : Ctxt.Valuation (d := catCryptDialect) ctxKA :=
  .cons k (.cons acc .nil)

/-- The abstract entry state: `acc` at the name `acc`, `k` at every other name. -/
def sumEntry (k acc : BitVec 64) : String → BitVec 64 :=
  fun s => if s = "acc" then acc else k

/-- `vmSumAll` resolves every name to a word slot whose value in `valKA k acc` is
    `sumEntry k acc` at that name. -/
theorem vmSumAll_resolves (k acc : BitVec 64) :
    ∀ x, ¬ isTmpName x → ∃ w : CVar ctxKA (.sword 64),
      vmSumAll.lookup x = some ⟨.sword 64, w⟩ ∧
        (toVIRVar w).lookup (valKA k acc) = sumEntry k acc x := by
  intro x _
  by_cases hx : x = "acc"
  · subst hx
    exact ⟨.there .here, rfl, rfl⟩
  · exact ⟨.here, by simp [vmSumAll, hx], by simp [sumEntry, hx]; rfl⟩

/-- The loop body lies in the unified fragment: two scalar assignments over
    non-temp names. -/
theorem sumBody_coveredSU : IsCoveredSU sumBody :=
  .rSeq
    (.ofCtl (.ofStraight (.rScalarSetExpr _ _
      ⟨notTmp_of_short "acc" (by decide), notTmp_of_short "k" (by decide)⟩)) rfl)
    (.ofCtl (.ofStraight (.rScalarSetExpr _ _
      ⟨notTmp_of_short "k" (by decide), (by norm_num : (1 : ℕ) < 2 ^ 64)⟩)) rfl)

/-! ## 2. The weld at every entry -/

/-- **The jasmin program of `sumLoop` computes the triangular sum.** For an entry
    `k ≠ 0` and `acc`, fuel above `(k - 1).toNat`, and the front's unified descent
    of `sumLoop` from `valEnv vmSumAll (valKA k acc)` with the `acc` slot `w`, the
    continuation `com` closed at `w` and its jasmin lowering `jcom`: `jcom` denotes
    at the transported entry valuation `acc + k (k + 1) / 2`. -/
theorem sumLoop_jasminDenote (fuel : Nat) (k acc : BitVec 64) (hk : k ≠ 0)
    (hfuel : (k - 1).toNat < fuel)
    (o : DTransOut ctxKA)
    (hTrans : transU fuel vmSumAll (valEnv vmSumAll (valKA k acc)) sumLoop = some o)
    (w : CVar o.Γ' (.sword 64)) (hw : o.vm.lookup "acc" = some ⟨.sword 64, w⟩)
    (com : Com catCryptDialect ctxKA (.sword 64))
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (jcom : Com jasminDialect (mapCtx ctxKA) (mapTy (.sword 64)))
    (hCom : cryptoDialectToJasminCom com = some jcom) :
    jcom.denote (ctMapValD (valKA k acc))
      = acc + BitVec.ofNat 64 (k.toNat * (k.toNat + 1) / 2) := by
  have htrips : loopTrips sumGuard sumStep (sumStep (sumEntry k acc)) (sum_terminates _)
      = (k - 1).toNat :=
    loopTrips_eq_of_loopRecIn (sum_loopRecIn _ _ (by simp [sumStep, sumEntry])) _
  rw [corresU_whileFun_jasminDenote_word sumBody_coveredSU (sumBody_corresU fuel)
    (fun _ _ => trivial) sum_guard vmSumAll (valKA k acc) (sumEntry k acc)
    (vmSumAll_resolves k acc) trivial (sum_terminates _) (by rw [htrips]; exact hfuel)
    "acc" (notTmp_of_short "acc" (by decide)) o hTrans w hw com hRet jcom hCom]
  rw [sum_loopFun, sumExit_sumStep _ (by simpa [sumEntry] using hk)]
  simp [sumExit, sumEntry]

/-! ## 3. The closed instance at `k = 3`, `acc = 0`

The front's descent and the lowering are run by kernel evaluation and their
outputs named; the value of the jasmin program is then read off
`sumLoop_jasminDenote`. Each evaluation is a fixed closed term whose check takes
about a tenth of a second. -/

/-- The entry environment at `k = 3`, `acc = 0`. -/
noncomputable def sum3Env : SEnvScalar := valEnv vmSumAll (valKA 3 0)

theorem sum3TransSome : (transU 4 vmSumAll sum3Env sumLoop).isSome := by rfl

/-- The front's unified descent of `sumLoop` at `k = 3`, `acc = 0`. -/
noncomputable def sum3O : DTransOut ctxKA :=
  (transU 4 vmSumAll sum3Env sumLoop).get sum3TransSome

theorem sum3HTrans : transU 4 vmSumAll sum3Env sumLoop = some sum3O :=
  (Option.some_get sum3TransSome).symm

theorem sum3NameSome : (sum3O.vm.lookup "acc").isSome := by rfl

theorem sum3NameTy : ((sum3O.vm.lookup "acc").get sum3NameSome).1 = .sword 64 := by
  decide

/-- The slot of `acc` in the descent output. -/
noncomputable def sum3W : CVar sum3O.Γ' (.sword 64) :=
  cast (congrArg (CVar sum3O.Γ') sum3NameTy) ((sum3O.vm.lookup "acc").get sum3NameSome).2

theorem sum3HName : sum3O.vm.lookup "acc" = some ⟨.sword 64, sum3W⟩ := by decide

theorem sum3RetSome : (sum3O.cont (Com.ret (toVIRVar sum3W))).isSome := by rfl

/-- The front's `Com catCryptDialect` program for `sumLoop` at `k = 3`, `acc = 0`,
    returning `acc`. -/
noncomputable def sum3Com : Com catCryptDialect ctxKA (.sword 64) :=
  (sum3O.cont (Com.ret (toVIRVar sum3W))).get sum3RetSome

theorem sum3HRet : sum3O.cont (Com.ret (toVIRVar sum3W)) = some sum3Com :=
  (Option.some_get sum3RetSome).symm

theorem sum3ComSome : (cryptoDialectToJasminCom sum3Com).isSome := by rfl

/-- The jasmin lowering of `sum3Com`. -/
noncomputable def sum3Jcom : Com jasminDialect (mapCtx ctxKA) (mapTy (.sword 64)) :=
  (cryptoDialectToJasminCom sum3Com).get sum3ComSome

theorem sum3HCom : cryptoDialectToJasminCom sum3Com = some sum3Jcom :=
  (Option.some_get sum3ComSome).symm

/-- **The closed instance.** The jasmin program of `sumLoop` at `k = 3`, `acc = 0`
    denotes `6`, by `sumLoop_jasminDenote`; the closing step is the numeral
    `0 + 3 · 4 / 2 = 6`. -/
theorem sumLoop3_jasminDenote : sum3Jcom.denote (ctMapValD (valKA 3 0)) = 6#64 := by
  rw [sumLoop_jasminDenote 4 3 0 (by decide) (by decide) sum3O sum3HTrans sum3W sum3HName
    sum3Com sum3HRet sum3Jcom sum3HCom]
  rfl

/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.sumLoop_jasminDenote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sumLoop_jasminDenote
/-- info: 'CatCrypt.Crypto.SecureCompilation.Ascent.Demos.sumLoop3_jasminDenote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sumLoop3_jasminDenote

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
