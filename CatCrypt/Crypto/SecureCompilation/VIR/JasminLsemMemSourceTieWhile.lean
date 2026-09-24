/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTie
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTie

@[expose] public section

set_option autoImplicit false

/-!
# The A3 while → source-`ComL` tie (`whileMem_export_faithful_comL`)

`JasminLsemMemSourceTie` ties the counter-loop export theorems to the source
nodes `ComL.forLoopNRt` / `ComL.forLoopNRtNested` (`loopMem_export_faithful_comL`
and the nested runners). The A3 **data-dependent while** had no source node:
`whileMem_export_faithful` (`JasminLsemMemChainBridge`) ends at the spec fold
`runWhileMem`, and the front (`TranslateDialectDataWhile.rolledWhileNz`) emits
`whileLinstrRM` directly at the instruction level. `ComL.whileNz`
(`JasminLprogExport`) is the source node for the committed countdown idiom
(`while (n != 0) { …; n -= 1 }`); this file supplies its tie:

1. **`runWhileMem_decodes_denote`** (§1): a halting `runWhileMem` — the
   data-dependent do-while, trip `whileTripsMem` read off the run — decodes at
   the accumulator register to `JLoopBodyN.denote ⟨whileTripsMem …, update⟩`,
   by composing `runWhileMem_halts_schedule` (the run reconstructs the
   fixed-trip `runBoundedLoopMemC` schedule) with §4b's fold induction
   `runBoundedLoopMemC_decodes_denote` (never re-proved).
2. **`comL_whileNz_ret_denote`** (§2): the front-emitted
   `ComL.whileNz update guard init invs (.ret .here)` denotes the
   `(guard.lookup V).toNat`-fold — the trip count the countdown guard exit
   realises.
3. **`whileMem_export_faithful_comL`** (§3): the composed export theorem — the
   emitted `whileLinstrRM top gReg [] body` machine run (`lsemFuelMemLC`, fuel
   `whileTripsMem … * (fuelCostC … + 1)`, the trip read off the run) halts at a
   state whose accumulator register decodes to **`ComL.whileNz`'s
   `ComL.denote`**. The trip identification `htrip` (`whileTripsMem … =
   (guard.lookup V).toNat`) is the countdown-idiom content: the data-dependent
   trip equals the seed. Combined with the run-halting hypothesis it also
   excludes the `guard = 0` underflow entry (a halting do-while has trip
   `≥ 1`).

The end-to-end concrete witness (front-compile → `ComL.whileNz` → rendered
back-edge → machine run = `ComL.denote`) lives in
`Dialects/TranslateDialectWhileNode.lean` (`native_decide` validates).

**All goals closed; axioms = {propext, Classical.choice, Quot.sound}.**
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieWhile

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestWhile
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChainBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTie

variable {invTys : Ctxt jasminDialect}

/-! ## 1. The halting do-while decodes to the source fold -/

/-- **A halting `runWhileMem` decodes to `JLoopBodyN.denote` at the
    data-dependent trip.** If the do-while `runWhileMem (condNZ gReg) body fuel`
    halts to `bfin`, the seed decodes (`hinit`), and each of the
    `whileTripsMem …` trips of the emitted body computes one
    `JLoopBodyN.stepC` under the `decodeM` correspondence (`hsim`), then `bfin`
    decodes at the accumulator register to the source loop's
    `whileTripsMem …`-fold denotation. Composes
    `runWhileMem_halts_schedule` (the run reconstructs the fixed-trip
    `runBoundedLoopMemC` schedule) with the §4b fold induction
    `runBoundedLoopMemC_decodes_denote`; nothing is re-proved. -/
theorem runWhileMem_decodes_denote {w : Nat} (env : LeafEnvM)
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (invs : Ctxt.Valuation invTys) (body : List LinstrRM) (gReg accReg : String)
    (s0 : LstateM) (acc0 : BitVec w)
    (hinit : decodeM s0 accReg w = some acc0)
    (fuel : Nat) (bfin : LstateM)
    (hhalt : runWhileMem env (fun b => condNZ b (.reg gReg)) body fuel s0 = some bfin)
    (hsim : ∀ t, t < whileTripsMem env (fun b => condNZ b (.reg gReg)) body fuel s0 →
      ∀ (bt : LstateM) (acct : BitVec w),
      runBoundedLoopMemC env body t s0 = some bt →
      decodeM bt accReg w = some acct →
      ∃ bt', lsemStraightMemC env body bt = some bt'
        ∧ decodeM bt' accReg w = some (JLoopBodyN.stepC update invs t acct)) :
    decodeM bfin accReg w
      = some (JLoopBodyN.denote
          ⟨whileTripsMem env (fun b => condNZ b (.reg gReg)) body fuel s0, update⟩
          invs acc0) := by
  have hgpc : ∀ (b : LstateM) (pc : Nat),
      (fun b => condNZ b (.reg gReg)) (b.setLpc pc)
        = (fun b => condNZ b (.reg gReg)) b :=
    fun b pc => condNZ_setLpc b pc (.reg gReg)
  obtain ⟨_, _, _, hbfin1, _⟩ :=
    runWhileMem_halts_schedule env (fun b => condNZ b (.reg gReg)) body hgpc
      fuel s0 bfin hhalt
  have hdec1 := runBoundedLoopMemC_decodes_denote env update invs body accReg s0
    acc0 hinit (whileTripsMem env (fun b => condNZ b (.reg gReg)) body fuel s0)
    hsim (bfin.setLpc 1) hbfin1
  rwa [decodeM_setLpc] at hdec1

/-! ## 2. The source node's denotation is the seed-count fold -/

/-- **The source node's denotation is the countdown fold.** The front-emitted
    `ComL.whileNz update guard init invs (.ret .here)` — the data-dependent
    do-while node returning its final accumulator — denotes exactly
    `JLoopBodyN.denote ⟨(guard.lookup V).toNat, update⟩` over the looked-up
    invariants and seed: the trip count the countdown guard exit realises. -/
theorem comL_whileNz_ret_denote {Γ : Ctxt jasminDialect} {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (guard : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ (JasminTy.reg w))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ) :
    (ComL.whileNz update guard init invs (.ret .here)).denote V
      = JLoopBodyN.denote ⟨(guard.lookup V).toNat, update⟩
          (Expr.lookupArgs invs V) (init.lookup V) := rfl

/-! ## 3. The composed export theorem: machine run decodes to `ComL.denote` -/

/-- **A3 export faithfulness, concluded at `ComL.denote`.** The composed
    "emitted while executes as the source denotation" statement for the
    data-dependent do-while: for the emitted `whileLinstrRM top gReg [] body`
    run by `lsemFuelMemLC` from the loop top, if the do-while `runWhileMem`
    halts within `fuel` (`hhalt` — the trip `whileTripsMem …` **read off the
    run**, not supplied), the data-dependent trip equals the countdown seed
    (`htrip` — the countdown-idiom identification; with `hhalt` it forces
    `0 < guard.lookup V`, excluding the underflow entry), the seed decodes
    (`hinit`) and each trip computes one `JLoopBodyN.stepC` under the `decodeM`
    correspondence (`hsim`), then the machine run halts at a state whose
    accumulator register decodes to the front node
    `ComL.whileNz update guardV initV invsV (.ret .here)`'s **`ComL.denote`** —
    the source semantics of the data-dependent while. Composes
    `whileMem_export_faithful` (B3, never re-proved) with §1 and §2. -/
theorem whileMem_export_faithful_comL {Γ : Ctxt jasminDialect} {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (guardV : Ctxt.Var Γ (JasminTy.reg 64)) (initV : Ctxt.Var Γ (JasminTy.reg w))
    (invsV : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ)
    (env : LeafEnvM) (fn : String) (top : LLabel) (gReg : String)
    (body : List LinstrRM)
    (hok : ∀ i ∈ body, BodyStepOK env (singletonProgM fn (whileLinstrRM top gReg [] body)) i)
    (s : LstatePMC) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (fuel : Nat) (bfin : LstateM)
    (hhalt : runWhileMem env (fun b => condNZ b (.reg gReg)) body fuel s.base = some bfin)
    (htrip : whileTripsMem env (fun b => condNZ b (.reg gReg)) body fuel s.base
        = (guardV.lookup V).toNat)
    (accReg : String)
    (hinit : decodeM s.base accReg w = some (initV.lookup V))
    (hsim : ∀ t, t < (guardV.lookup V).toNat → ∀ (bt : LstateM) (acct : BitVec w),
      runBoundedLoopMemC env body t s.base = some bt →
      decodeM bt accReg w = some acct →
      ∃ bt', lsemStraightMemC env body bt = some bt'
        ∧ decodeM bt' accReg w
            = some (JLoopBodyN.stepC update (Expr.lookupArgs invsV V) t acct)) :
    ∃ t : LstatePMC,
      lsemFuelMemLC env (singletonProgM fn (whileLinstrRM top gReg [] body))
          (whileTripsMem env (fun b => condNZ b (.reg gReg)) body fuel s.base
            * (fuelCostC env body + 1)) s = some t
        ∧ decodeM t.base accReg w
            = some ((ComL.whileNz update guardV initV invsV (.ret .here)).denote V) := by
  obtain ⟨t, ht, hdec⟩ := whileMem_export_faithful env fn top gReg body hok s hfn hpc
    fuel bfin hhalt accReg w
  refine ⟨t, ht, hdec.trans ?_⟩
  rw [comL_whileNz_ret_denote, ← htrip]
  exact runWhileMem_decodes_denote env update (Expr.lookupArgs invsV V) body gReg
    accReg s.base (initV.lookup V) hinit fuel bfin hhalt
    (htrip ▸ hsim)

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieWhile
