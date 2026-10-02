/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectLoopCallLink
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectLoopCallLink
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestWhile
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestWhile

@[expose] public section

set_option autoImplicit false

/-!
# Front-lowering a data-dependent `RWhileNz` to A3's guard-driven `whileLinstrRM`

`TranslateDialectRolledLoop.rolledForLoopN` / `TranslateDialectRuntimeLoop.rolledForLoopNRt`
front-compile a covered loop body and wrap it in a **count-driven** back-edge
(`ComL.forLoopN` / `ComL.forLoopNRt` — `MOV Lctr, #N` / `MOV Lctr, <argReg>`). A
`while` whose trip is **not** known at entry — a `while (name != 0)` whose guard is
re-read from state each iteration and whose body decrements the counter — is
*data-dependent*: the number of iterations is fixed only at run time by the values
the body produces. This is the `honest_prove` PoW-grind and the `ConvertToVole`
`sd0_bot` conditional-spine shape.

The **backend** already supports it (capability A3,
`JasminLsemMemLoopNestWhile`): `runWhileMem` is the fuel-bounded do-while
denotation over `LstateM` (guard read off the out-state), `whileLinstrRM` is the
emitted guard-driven back-edge (`Llabel; body; guardCompute; Lcond gReg top`), and
`whileMem_realizes` / `whileMem_runWhile` prove the emitted counter-loop run by
`lsemFuelMemLC` realises `runWhileMem` — the trip *read off the run*, the consumer
supplying only a fuel/variant bound. `RWhileNz` is not a straight-line `ComCont`.

This module supplies the front for it, mirroring `TranslateDialectRuntimeLoop`'s
structure but targeting `whileLinstrRM` (guard-driven) instead of `forLoopNRt`
(count-driven):

```
  bodyLowCT  (covered per-iteration body over the loop counter `name`)
    --(frontLoopBodyJ)---------------------------------->  Com jasminDialect = JLoopBodyN.update
    --(straightOpsMemCall ++ counter-mgmt tail `extra`)->  List LinstrRM        (front body; leaf RCall → real Lcall)
    --(whileLinstrRM top gReg [] fullBody)-------------->  List LinstrRM        (ONE body copy + real Lcond back-edge)
    --(singletonProgM fn / lsemFuelMemLC)--------------->  runWhileMem          (data-dependent trip, guard-driven)
```

## Design: the guard-driven analogue of `rolledForLoopNRt`

Everything is shared with the loop path:

* no new `LowCT` constructor (`RWhileNz` already exists);
* no new `catCryptDialect` op;
* the loop body reuses `frontLoopBodyJ` and `straightOpsMemCall` verbatim (so a
  body-`RCall` to a known leaf lowers to a **real** `Lcall`, composing with
  `TranslateDialectLoopCallLink` — the `while`-body-with-call shape);
* the denote bridge reuses A3's `whileMem_realizes` **verbatim** — not re-proved.

The **only** delta versus `rolledForLoopNRt` is: the count-driven `ComL.forLoopNRt
update count` is replaced by A3's guard-driven `whileLinstrRM top gReg [] fullBody`,
and the denotation is the data-dependent `runWhileMem` fold (guard `name != 0`,
trip read off the run) rather than the `N`-fold `JLoopBodyN.denote`. The counter
register `gReg` is the `RWhileNz` guard variable `name`; the body's own
`name -= 1` (the `RScalarSetExpr "ctr" (SExpr.subOne "ctr")` countdown idiom) makes
the guard eventually false — the termination the consumer's fuel/variant bound
witnesses.

## Validation

`§ Validate` front-compiles a real covered body that CALLS a leaf per iteration
(`acc := sum(acc, a[i])`, reusing `TranslateDialectLoopCallLink`'s validate body),
wraps it in a data-dependent `while (n != 0)` (`n` decremented by the body's tail),
and checks by `native_decide` that: the body front-compiles; the emitted program
carries a real `Lcond` back-edge and a real leaf `Lcall`; A3's `lsemFuelMemLC` run
equals the `runWhileMem` do-while denotation (guard `n != 0`) and decodes to
`10 + 20 + 30 = 60`; and the data-dependent trip count `whileTripsMem = 3` is read
off the run (the initial `n`), not supplied.

**All goals closed; axioms ⊆ {propext, Classical.choice, Quot.sound} (+ `Lean.ofReduceBool`
for the `native_decide` validates).**
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDataWhile

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectLoopCallLink
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestWhile
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 1. The front while lowering

`rolledWhileNzBody` front-compiles the covered while body to the front instruction
list (the `straightOpsMemCall` image of `frontLoopBodyJ`, followed by the
counter-management/accumulator-feedback tail `extra` A3's counter-loop shape
carries — the `idx += 1` / `name -= 1` the guard reads). `rolledWhileNz` wraps it
in A3's guard-driven `whileLinstrRM`; `rolledWhileNzProg` packages it as an
`LprogM` A2/A3's `lsemFuelMemLC` runs. -/

/-- Front-compile the covered while body to the front instruction list: the
    `straightOpsMemCall` image of `frontLoopBodyJ` (so a body-`RCall` to a known
    leaf becomes a real `Lcall`), followed by the counter-management tail `extra`.
    `none` if the front declines. Identical to `TranslateDialectRuntimeLoop`'s body
    front-compile, only the wrapper differs. -/
def rolledWhileNzBody (nArgs : Nat) (leafGen : LeafGen)
    {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT)
    (cd : Nat) (extra : List LinstrRM) : Option (List LinstrRM) :=
  (frontLoopBodyJ (accCTy := accCTy) vmBody accName body).map
    (fun update => frontLoopFullBody nArgs leafGen update cd extra)

/-- Wrap the front-lowered while body in A3's **guard-driven** `whileLinstrRM`
    back-edge: `Llabel top; fullBody; guardCompute; Lcond gReg top`. For the
    countdown idiom (`while (name != 0)` with the body decrementing `name`),
    `gReg = name` and `guardCompute = []` (the body already leaves the counter in
    `name`). `none` if the front declines. The guard-driven analogue of
    `TranslateDialectRuntimeLoop.rolledForLoopNRt`. -/
def rolledWhileNz (nArgs : Nat) (leafGen : LeafGen)
    {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT)
    (cd : Nat) (extra : List LinstrRM)
    (top : LLabel) (gReg : String) (guardCompute : List LinstrRM) :
    Option (List LinstrRM) :=
  (rolledWhileNzBody nArgs leafGen (accCTy := accCTy) vmBody accName body cd extra).map
    (fun fullBody => whileLinstrRM top gReg guardCompute fullBody)

/-- The owned data-dependent-while `LprogM` for a front-compiled body: package the
    `rolledWhileNz` instruction list as a single-function program A2/A3's
    `lsemFuelMemLC` runs (following the real `Lcond` back-edge). `none` if the front
    declines. -/
def rolledWhileNzProg (nArgs : Nat) (leafGen : LeafGen)
    {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT)
    (cd : Nat) (extra : List LinstrRM)
    (fn : String) (top : LLabel) (gReg : String) (guardCompute : List LinstrRM) :
    Option LprogM :=
  (rolledWhileNz nArgs leafGen (accCTy := accCTy) vmBody accName body cd extra
      top gReg guardCompute).map (singletonProgM fn)

/-! ## 2. The denote bridge: reuse A3's `whileMem_realizes`

The front-emitted while body `frontLoopFullBody nArgs leafGen update cd extra`,
wrapped in the countdown-idiom `whileLinstrRM top gReg [] …` and run by
`lsemFuelMemLC`, realises the data-dependent do-while `runWhileMem` (guard
`condNZ · gReg`) — A3's `whileMem_realizes` proves exactly this for **any**
`List LinstrRM` body. `rolledWhileNz_realizes` is that theorem specialised to the
front-emitted body: the trip is `whileTripsMem` (read off the run), the consumer
supplies only `fuel` (a termination/variant bound) and the `BodyStepOK` structural
hypothesis (`straightOpsMemCall_elems` supplies its front half — every front
instruction is a `.Lopn` or the real leaf `Lcall`). No part of A3's while bridge is
re-proved. -/

/-- **Denote bridge (front data-dependent while ⇒ `runWhileMem` fold).** For the
    countdown-idiom program `whileLinstrRM top gReg []` over the front-emitted body
    `frontLoopFullBody nArgs leafGen update cd extra`, if the data-dependent
    do-while `runWhileMem (condNZ · gReg)` halts within `fuel` to `bfin`, then the
    interpreter — given `whileTripsMem … * (fuelCostC … + 1)` steps (the trip read
    off the run) — halts in a state agreeing with `bfin` on the register store and
    array carrier. A thin specialisation of A3's `whileMem_realizes` to the
    front-emitted body — reused verbatim, not re-proved. `hupd` witnesses that the
    body front-compiles (so `update` is the front image); `hok` is A3's `BodyStepOK`
    precondition (its structural half is `straightOpsMemCall_elems`). -/
theorem rolledWhileNz_realizes (nArgs : Nat) (leafGen : LeafGen)
    {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT)
    (cd : Nat) (extra : List LinstrRM)
    {update : Com jasminDialect (mapCtx Γbody) (mapTy accCTy)}
    (_hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update)
    (env : LeafEnvM) (fn : String) (top : LLabel) (gReg : String)
    (hok : ∀ i ∈ frontLoopFullBody nArgs leafGen update cd extra,
      BodyStepOK env (singletonProgM fn
        (whileLinstrRM top gReg [] (frontLoopFullBody nArgs leafGen update cd extra))) i)
    (s : LstatePMC) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (fuel : Nat) (bfin : LstateM)
    (hhalt : runWhileMem env (fun b => condNZ b (.reg gReg))
        (frontLoopFullBody nArgs leafGen update cd extra) fuel s.base = some bfin) :
    ∃ t : LstatePMC,
      lsemFuelMemLC env (singletonProgM fn
          (whileLinstrRM top gReg [] (frontLoopFullBody nArgs leafGen update cd extra)))
          (whileTripsMem env (fun b => condNZ b (.reg gReg))
            (frontLoopFullBody nArgs leafGen update cd extra) fuel s.base
            * (fuelCostC env (frontLoopFullBody nArgs leafGen update cd extra) + 1)) s = some t
        ∧ t.base.reg.lvm = bfin.reg.lvm ∧ t.base.larr = bfin.larr :=
  whileMem_realizes env fn top gReg (frontLoopFullBody nArgs leafGen update cd extra)
    hok s hfn hpc fuel bfin hhalt

/-! ## 3. Validate: a front-compiled data-dependent `while (n != 0)` that CALLS a
    leaf per iteration

Reuse `TranslateDialectLoopCallLink`'s validate body (`acc := sum(acc, a[i])`, the
leaf `RCall sum`) and its front lowering (`validateLoopBody` = the front body
`Lcall` + the accumulator feedback / `idx += 1` / `n -= 1` counter tail), here
wrapped in A3's **data-dependent** `whileLinstrRM 0 "n" []` (guard `n != 0`) rather
than the fixed-trip `loopLinstrRM`. The trip is fixed at run time by the initial
`n = 3` (the body decrements it), matched against `runWhileMem`. -/

/-- The owned data-dependent-while program: the front body + counter tail wrapped in
    the guard-driven `whileLinstrRM 0 "n" []`. Note `whileLinstrRM 0 "n" []
    validateLoopBody = loopLinstrRM 0 "n" (validateLoopBody ++ [])` — the same real
    `Lcond (.reg "n") 0` back-edge, *interpreted* as the data-dependent `while`
    whose trip is read off the run. -/
def whileValidateProg (_ : Unit) : LprogM :=
  singletonProgM "f" (whileLinstrRM 0 "n" [] (validateLoopBody ()))

/-- **(a) The leaf-calling while body front-compiles** (same front output as the
    loop body — `frontLoopBodyJ` is reused verbatim). -/
theorem whileValidate_frontJ_isSome : (validateFrontJ ()).isSome := by native_decide

/-- Predicate: a `LinstrRM` list contains a real `Lcond` back-edge. -/
def hasBackEdge (body : List LinstrRM) : Bool :=
  body.any (fun i => match i.fst with | .Lcond _ _ => true | _ => false)

/-- **(b) The emitted program carries a REAL `Lcond` back-edge and a REAL leaf
    `Lcall`** — a guard-driven loop over a real linked leaf, not a
    straight-line unroll or an opaque `CALL:` shadow. -/
theorem whileValidate_realBackEdge_realCall :
    hasBackEdge (whileValidateProg ()).body = true
      ∧ hasRealCall (whileValidateProg ()).body = true
      ∧ hasCallShadow (whileValidateProg ()).body = false := by native_decide

/-- **(c) denote = `runWhileMem` do-while fold via A3's interpreter.** A3's
    `lsemFuelMemLC` follows the counter-guarded `Lcond` back-edge until `n` reaches
    `0` — the trip fixed at run time by the initial `n = 3` — and the accumulator
    decodes equal to the `runWhileMem` (guard `n != 0`) do-while denotation of the
    same body over the same start. -/
theorem whileValidate_denote_eq_runWhileMem :
    (lsemFuelMemLC (validateEnv ()) (whileValidateProg ()) 60 validateStart).map
        (fun t => decodeM t.base "a2" 64)
      = (runWhileMem (validateEnv ()) (fun b => condNZ b (.reg "n")) (validateLoopBody ()) 10
          validateStart.base).map (fun b => decodeM b "a2" 64) := by native_decide

/-- **(c′) The decoded result is `10 + 20 + 30 = 60`** — the real linked leaf
    invoked per data-dependent iteration. -/
theorem whileValidate_denote_eq_60 :
    (lsemFuelMemLC (validateEnv ()) (whileValidateProg ()) 60 validateStart).map
        (fun t => decodeM t.base "a2" 64) = some (some (60#64)) := by native_decide

/-- **(c″) The data-dependent trip count is read off the run.** `whileTripsMem` for
    the while body equals `3` — determined by the initial `n = 3`, not supplied as a
    proof parameter. -/
theorem whileValidate_trips :
    whileTripsMem (validateEnv ()) (fun b => condNZ b (.reg "n")) (validateLoopBody ()) 10
        validateStart.base = 3 := by native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDataWhile
