/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.WhileFun
public import CatCrypt.Crypto.SecureCompilation.Ascent.FeSubSymbolic
public import CatCrypt.Crypto.SecureCompilation.VIR.RustToJasminComWhile

/-!
# The functional `while` rule at `Com jasminDialect`

`corresU_whileFun` (`Ascent/WhileFun.lean`) relates a terminating run of the loop
node `.RWhileNz name body` at the unified waist `semU` to the exit state
`loopFun guardA fb (fb a)` of the abstract loop. The front compiles the same node
through the unified descent `transU fuel vm env`
(`Dialects/TranslateDialectUnifiedDenote.lean`), which unrolls the loop to the trip
count `scalarWhileTrips … fuel env` of the run from the entry environment `env`,
and `transU_to_jasminCom_endToEnd` (`VIR/RustToJasminComWhile.lean`) carries the
value at a tracked output slot of that `Com catCryptDialect` through
`cryptoDialectToJasminCom` to the jasmin `Com`.

This module composes the two: the jasmin program the front emits for the loop node
from the entry environment denotes, at the transported entry valuation, the
projection of `loopFun guardA fb (fb a)` to the output name.

The `Com jasminDialect` in these statements is the front's unrolling of the loop at
the entry environment's trip count; the rolled back-edge is emitted below the
dialect, at `Lcmd` (`TranslateDialectDataWhile.rolledWhileNz`), and is not the
object of these theorems.

## Main results

* `corresU_whileFun_jasminDenote` — for a `LoopRecIn`-certified body over any state
  relation `SR`, a terminating run and the front's output at the entry environment,
  the jasmin program denotes the projection of `loopFun` to the output name
* `corresU_whileFun_jasminDenote_of_fuel` — the same without a run: the abstract
  trip count below the fuel makes the run terminate
* `corresU_whileFun_jasminDenote_word` — the form over `SRwordBV`, with the entry
  environment `valEnv vm V` induced by the entry map and valuation
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (Ctx CVar)
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (VarMap)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge (toVIRVar)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom (cryptoDialectToJasminCom)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.RustToJasminComWhile (transU_to_jasminCom_endToEnd)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect (DTransOut)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

variable {AState : Type} (SR : SEnvScalar → AState → Prop)

/-- **The functional `while` rule at `Com jasminDialect`.** For the loop node
    `.RWhileNz name body` with an `IsCoveredSU` body, a body correspondence
    `CorresU fuel SR P fb body` whose abstract step preserves `P`, and an abstract
    guard `guardA` agreeing with `guardNz name` on related states: from an entry
    environment `env` consistent with the entry valuation `V` through the entry map
    `vm`, related to an abstract state `a` satisfying `P`, and a terminating run of
    the node to `env'`, if the front's unified descent `transU fuel vm env` of the
    node succeeds with output `o`, the output name `dst` resolves in `o.vm` to the
    word slot `w`, the continuation closed at `w` is `com` and its jasmin lowering
    is `jcom`, then `jcom` denotes at `ctMapValD V` the transport of
    `proj (loopFun guardA fb (fb a) hterm)`, where `proj` reads the output name off
    the abstract state (`hproj`: on related states `env dst` holds `proj a`).
    `corresU_whileFun_terminates` supplies `hterm` from the run. -/
theorem corresU_whileFun_jasminDenote {fuel : Nat} {P : AState → Prop}
    {guardA : AState → Bool} {fb : AState → AState} {name : String} {body : LowCT}
    (hcov : IsCoveredSU body)
    (hbody : CorresU fuel SR P fb body) (hinv : ∀ a, P a → P (fb a))
    (hguard : ∀ env a, SR env a → P a → guardNz name env = guardA a)
    {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env : SEnvScalar) (a : AState) (hCons : ConsistentS vm V env) (hSR : SR env a) (hP : P a)
    (env' : SEnvScalar) (hrun : semU fuel (.RWhileNz name body) env = some env')
    (hterm : LoopTerminates guardA fb (fb a))
    (dst : String) (proj : AState → BitVec 64)
    (hproj : ∀ env a, SR env a → env dst = some ⟨.sword 64, proj a⟩)
    (o : DTransOut Γ) (hTrans : transU fuel vm env (.RWhileNz name body) = some o)
    (w : CVar o.Γ' (.sword 64)) (hw : o.vm.lookup dst = some ⟨.sword 64, w⟩)
    (com : Com catCryptDialect Γ (.sword 64))
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy (.sword 64)))
    (hCom : cryptoDialectToJasminCom com = some jcom) :
    jcom.denote (ctMapValD V) = ctTransTy (proj (loopFun guardA fb (fb a) hterm)) :=
  transU_to_jasminCom_endToEnd fuel vm (.RWhileNz name body) o V env env' dst w _ com jcom
    (.rWhile hcov) hTrans hCons hrun hw
    (hproj env' _ (corresU_whileFun SR hbody hinv hguard env a env' hSR hP hrun hterm)) hRet hCom

/-- The rule without a run hypothesis: when the abstract loop terminates from `fb a`
    in fewer trips than `fuel`, the run of the node terminates
    (`corresU_whileFun_total`) and the conclusion of
    `corresU_whileFun_jasminDenote` follows. -/
theorem corresU_whileFun_jasminDenote_of_fuel {fuel : Nat} {P : AState → Prop}
    {guardA : AState → Bool} {fb : AState → AState} {name : String} {body : LowCT}
    (hcov : IsCoveredSU body)
    (hbody : CorresU fuel SR P fb body) (hinv : ∀ a, P a → P (fb a))
    (hguard : ∀ env a, SR env a → P a → guardNz name env = guardA a)
    {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env : SEnvScalar) (a : AState) (hCons : ConsistentS vm V env) (hSR : SR env a) (hP : P a)
    (hterm : LoopTerminates guardA fb (fb a)) (hfuel : loopTrips guardA fb (fb a) hterm < fuel)
    (dst : String) (proj : AState → BitVec 64)
    (hproj : ∀ env a, SR env a → env dst = some ⟨.sword 64, proj a⟩)
    (o : DTransOut Γ) (hTrans : transU fuel vm env (.RWhileNz name body) = some o)
    (w : CVar o.Γ' (.sword 64)) (hw : o.vm.lookup dst = some ⟨.sword 64, w⟩)
    (com : Com catCryptDialect Γ (.sword 64))
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy (.sword 64)))
    (hCom : cryptoDialectToJasminCom com = some jcom) :
    jcom.denote (ctMapValD V) = ctTransTy (proj (loopFun guardA fb (fb a) hterm)) := by
  obtain ⟨env', hrun, -⟩ :=
    corresU_whileFun_total SR hbody hinv hguard env a hSR hP hterm hfuel
  exact corresU_whileFun_jasminDenote SR hcov hbody hinv hguard vm V env a hCons hSR hP env'
    hrun hterm dst proj hproj o hTrans w hw com hRet jcom hCom

/-- The rule over the identity word relation `SRwordBV`. The entry environment is
    `valEnv vm V`, induced by an entry map `vm` that resolves every non-temp name
    `x` to a word slot whose value in `V` is `a x`; the output name `dst` is a
    non-temp name, and the abstract state is read at `dst`. The jasmin program
    denotes `loopFun guardA fb (fb a) hterm dst`. -/
theorem corresU_whileFun_jasminDenote_word {fuel : Nat} {P : (String → BitVec 64) → Prop}
    {guardA : (String → BitVec 64) → Bool}
    {fb : (String → BitVec 64) → (String → BitVec 64)} {name : String} {body : LowCT}
    (hcov : IsCoveredSU body)
    (hbody : CorresU fuel SRwordBV P fb body) (hinv : ∀ a, P a → P (fb a))
    (hguard : ∀ env a, SRwordBV env a → P a → guardNz name env = guardA a)
    {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (a : String → BitVec 64)
    (hA : ∀ x, ¬ isTmpName x → ∃ w : CVar Γ (.sword 64),
      vm.lookup x = some ⟨.sword 64, w⟩ ∧ (toVIRVar w).lookup V = a x)
    (hP : P a)
    (hterm : LoopTerminates guardA fb (fb a)) (hfuel : loopTrips guardA fb (fb a) hterm < fuel)
    (dst : String) (hdst : ¬ isTmpName dst)
    (o : DTransOut Γ) (hTrans : transU fuel vm (valEnv vm V) (.RWhileNz name body) = some o)
    (w : CVar o.Γ' (.sword 64)) (hw : o.vm.lookup dst = some ⟨.sword 64, w⟩)
    (com : Com catCryptDialect Γ (.sword 64))
    (hRet : o.cont (Com.ret (toVIRVar w)) = some com)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy (.sword 64)))
    (hCom : cryptoDialectToJasminCom com = some jcom) :
    jcom.denote (ctMapValD V) = loopFun guardA fb (fb a) hterm dst :=
  corresU_whileFun_jasminDenote_of_fuel SRwordBV hcov hbody hinv hguard vm V (valEnv vm V) a
    (consistentS_valEnv vm V) (srwordBV_valEnv vm V a hA) hP hterm hfuel dst (fun a => a dst)
    (fun _ _ hSR => hSR dst hdst) o hTrans w hw com hRet jcom hCom

end CatCrypt.Crypto.SecureCompilation.Ascent
