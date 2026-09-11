/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDataWhile
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDataWhile

@[expose] public section

set_option autoImplicit false

/-!
# Front-lowering a GENERAL comparison guard to A3's `whileLinstrRM` guardCompute

`TranslateDialectDataWhile.rolledWhileNz` front-compiles a data-dependent
`while (name != 0)` whose guard is the *countdown idiom* — the body leaves the
counter in a named register `gReg` and the guard-compute segment is **empty**
(`whileLinstrRM top gReg [] fullBody`), so the `Lcond` reads that counter
directly.  Its denote bridge (`rolledWhileNz_realizes`) is A3's `whileMem_realizes`,
the empty-guardCompute corollary of `whileMem_runWhile`.

This module lifts that to a **general comparison guard** — a `while (x < target)` /
`while (hash >= target)` PoW-grind whose loop condition is a comparison
recomputed each pass — by front-compiling the comparison into a **non-empty**
guardCompute segment and bridging through A3's general `whileMem_runWhile`.

```
  guardSExpr  (a comparison expressed over the loop scalars)
    --(RScalarSetExpr gAccName · ; frontLoopBodyJ)-------->  Com jasminDialect
    --(straightOpsMemCall ++ land-in-gReg tail `gextra`)-->  guardCompute : List LinstrRM
  whileLinstrRM top gReg guardCompute fullBody
    = loopLinstrRM top gReg (fullBody ++ guardCompute)        -- guardCompute runs INSIDE the loop
    --(lsemFuelMemLC)------------------------------------->  runWhileMem over (fullBody ++ guardCompute)
```

Because `whileLinstrRM top gReg guardCompute body = loopLinstrRM top gReg
(body ++ guardCompute)` (A3, definitional), the guardCompute segment runs on each
pass right before the back-edge, materialising the comparison into `gReg`, and the
`Lcond (.reg gReg)` reads it fresh — per-iteration re-evaluation is free.  A3's
`whileMem_runWhile` (the general, NON-empty-guardCompute bridge) proves the
emitted counter-loop over `fullBody ++ guardCompute` realises `runWhileMem` with
the guard `condNZ · gReg` recomputed each pass; `rolledWhileGuard_realizes` is that
theorem specialised to the front-emitted body + front-compiled guard, reused
verbatim — not re-proved.

## The comparison fragment

The scalar `SExpr → Com` front (`TranslateDialectDirectArms.lowerSExpr`) covers
`SVar`/`SLit`/`SAdd`/`SSub`/`SMul`/`SShr`/`SShl`/`SAnd`/`SXor`/`SMulHiU`.  It does
**not** cover the `SLt` constructor (the dialect has no scalar `<` word op — see the
`| _ => none` arm of `lowerSExpr`), and there are no `SGe`/`SEq` constructors at
all.  Comparisons are therefore expressed **branch-free** over the covered ops, the
same eq-mask / sign-bit idiom the field-reduce emitters use, valid for operands
`< 2^63`:

* `x < y`   ⇒  `SShr (SSub x y) (SLit 63)`                    (`1` iff `x < y`)
* `x ≥ y`   ⇒  `SXor (SShr (SSub x y) (SLit 63)) (SLit 1)`    (`1` iff `x ≥ y`, the PoW `hash ≥ target` shape)
* `x ≠ y`   ⇒  `SSub x y`                                     (nonzero iff `x ≠ y`; `y = 0` recovers the countdown)

`guardComputeOfSExpr` front-compiles any such guard `SExpr`; it returns `none`
exactly when the guard falls outside `lowerSExpr`'s fragment (e.g. a raw `SLt`).

## Validation

`§ Validate` front-compiles a genuine general-guard while — `while (x < 100)
{ x := x + step }`, `x = 0`, `step = 25` — where the guard is a comparison
(`x < 100`, branch-free), NOT a `name != 0` countdown, and the trip is
data-dependent (fixed at run time by when `x` reaches `100`).  `native_decide`
confirms: the guard front-compiles; the emitted program carries a real `Lcond`
back-edge and a NON-empty front-compiled guardCompute; A3's `lsemFuelMemLC` run
equals the `runWhileMem` do-while denotation (guard `x < 100`) with the guard
recomputed each pass and decodes to `x = 100`; and the data-dependent trip count
`whileTripsMem = 4` is read off the run.

**0 sorries; axioms ⊆ {propext, Classical.choice, Quot.sound} (+ `Lean.ofReduceBool`
for the `native_decide` validates).**
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuardWhile

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectLoopCallLink
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDataWhile
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopCall
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestWhile
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 1. The front guard lowering -/

/-- **Front-compile a comparison guard `SExpr` into the guardCompute segment.**
    Wrap the guard as `RScalarSetExpr gAccName guard`, front-compile it via
    `frontLoopBodyJ` (the SAME `translateDialectControl` → `cryptoDialectToJasminCom`
    path the loop body uses), lower via `straightOpsMemCall` (so a body-`RCall` to a
    known leaf becomes a real `Lcall`), and append the small landing tail `gextra`
    (a rename move dropping the SSA guard result into the register `gReg` the
    `Lcond` reads).  Returns `none` exactly when the guard falls outside
    `lowerSExpr`'s covered word fragment (`SVar`/`SLit`/`SAdd`/`SSub`/`SMul`/`SShr`/
    `SShl`/`SAnd`/`SXor`/`SMulHiU`) — in particular a raw `SLt` (no scalar `<` word
    op in the dialect); comparisons are expressed branch-free over the covered ops.
    Structurally identical to `rolledWhileNzBody` — only the LowCT it front-compiles
    is a guard assignment rather than the loop body. -/
def guardComputeOfSExpr (nArgs : Nat) (leafGen : LeafGen)
    {Γg : Ctx} (vmG : VarMap Γg) (gAccName : String) (guard : SExpr)
    (cd : Nat) (gextra : List LinstrRM) : Option (List LinstrRM) :=
  (frontLoopBodyJ (accCTy := .sword 64) vmG gAccName (.RScalarSetExpr gAccName guard)).map
    (fun gc => frontLoopFullBody nArgs leafGen gc cd gextra)

/-- Wrap a front-compiled body (`rolledWhileNzBody`) and a front-compiled
    comparison guard (`guardComputeOfSExpr`) into A3's guard-driven `whileLinstrRM`:
    `Llabel top; fullBody; guardCompute; Lcond gReg top`.  Unlike
    `rolledWhileNz` (which takes a caller-supplied `guardCompute`, empty for the
    countdown), the guardCompute here is FRONT-COMPILED from the comparison
    `guard`, so the loop condition is a general comparison recomputed each pass.
    `none` if either front declines. -/
def rolledWhileGuard (nArgs : Nat) (leafGen : LeafGen)
    {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT)
    (cd : Nat) (extra : List LinstrRM)
    {Γg : Ctx} (vmG : VarMap Γg) (gAccName : String) (guard : SExpr)
    (gcd : Nat) (gextra : List LinstrRM)
    (top : LLabel) (gReg : String) : Option (List LinstrRM) :=
  match rolledWhileNzBody nArgs leafGen (accCTy := accCTy) vmBody accName body cd extra,
        guardComputeOfSExpr nArgs leafGen vmG gAccName guard gcd gextra with
  | some fullBody, some guardCompute => some (whileLinstrRM top gReg guardCompute fullBody)
  | _, _ => none

/-! ## 2. The denote bridge: reuse A3's `whileMem_runWhile`

`whileLinstrRM top gReg guardCompute fullBody = loopLinstrRM top gReg
(fullBody ++ guardCompute)` (A3, `whileLinstrRM_eq`), so the guardCompute segment
runs INSIDE the loop each pass and the `Lcond (.reg gReg)` reads the freshly-
computed comparison.  A3's `whileMem_runWhile` proves the emitted counter-loop over
ANY body — here `fullBody ++ guardCompute` — run by `lsemFuelMemLC` realises the
data-dependent `runWhileMem` with the guard `condNZ · gReg` recomputed each pass.
`rolledWhileGuard_realizes` is that theorem instantiated at the front-emitted
`fullBody` + front-compiled `guardCompute` — reused verbatim, not re-proved. -/

/-- **Denote bridge (front general-guard while ⇒ `runWhileMem` fold).** For the
    guard-driven program `whileLinstrRM top gReg guardCompute fullBody`, if the
    data-dependent do-while `runWhileMem (condNZ · gReg)` over `fullBody ++
    guardCompute` (body then the freshly-recomputed guard) halts within `fuel` to
    `bfin`, then the interpreter — given `whileTripsMem … * (fuelCostC … + 1)` steps
    (the trip read off the run) — halts in a state agreeing with `bfin` on the
    register store and the array carrier.  A thin specialisation of A3's
    `whileMem_runWhile` to the front-emitted body and the NON-empty front-compiled
    guardCompute — reused verbatim, not re-proved.  `hok` is A3's `BodyStepOK`
    precondition (its structural half is `straightOpsMemCall_elems`). -/
theorem rolledWhileGuard_realizes (env : LeafEnvM) (fn : String) (top : LLabel)
    (gReg : String) (fullBody guardCompute : List LinstrRM)
    (hok : ∀ i ∈ (fullBody ++ guardCompute),
      BodyStepOK env (singletonProgM fn
        (whileLinstrRM top gReg guardCompute fullBody)) i)
    (s : LstatePMC) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (fuel : Nat) (bfin : LstateM)
    (hhalt : runWhileMem env (fun b => condNZ b (.reg gReg)) (fullBody ++ guardCompute)
        fuel s.base = some bfin) :
    ∃ t : LstatePMC,
      lsemFuelMemLC env (singletonProgM fn
          (whileLinstrRM top gReg guardCompute fullBody))
          (whileTripsMem env (fun b => condNZ b (.reg gReg)) (fullBody ++ guardCompute)
            fuel s.base * (fuelCostC env (fullBody ++ guardCompute) + 1)) s = some t
        ∧ t.base.reg.lvm = bfin.reg.lvm ∧ t.base.larr = bfin.larr :=
  whileMem_runWhile env fn top gReg (fullBody ++ guardCompute) hok s hfn hpc fuel bfin hhalt

/-! ## 3. Validate: a front-compiled general-guard `while (x < 100)`

`while (x < 100) { x := x + step }`, `x = 0`, `step = 25`.  The guard is a genuine
comparison — `x < 100`, expressed branch-free as `SShr (SSub x 100) 63` — NOT a
`name != 0` countdown, and the trip is data-dependent (fixed at run time by when
`x` reaches `100`).  The loop threads `x` through the argument register `a1` (the
`gextra`/`extra` tails persist the SSA result into it); `step` stays in `a0`. -/

/-- The per-iteration body `x := x + step` (over scalars `x`, `step`). -/
def vBody : LowCT := .RScalarSetExpr "x2" (.SAdd (.SVar "x") (.SVar "step"))

/-- The comparison guard `x < 100`, branch-free: `(x - 100) >>> 63` is `1` iff
    `x < 100` (for `x < 2^63`). -/
def vGuard : SExpr := .SShr (.SSub (.SVar "x") (.SLit 100)) (.SLit 63)

/-- Body context `[x, step]` (both `u64`). -/
def vΓ : Ctx := [.sword 64, .sword 64]

/-- Body VarMap: `x ↦ .here`, `step`. -/
def vVm : VarMap vΓ := (VarMap.empty.bind (t := .sword 64) "step").bind (t := .sword 64) "x"

/-- No leaf calls in this validate. -/
def vLeafGen : LeafGen := fun _ _ _ => none

/-- Body tail: persist the fresh `x` (SSA result `r3`) into `a1` for the next pass.
    A reg-to-reg copy is emitted as `ADD dst, src, #0` (the model's `regArith` move;
    a single-source `MOV` reads an immediate only). -/
def vBodyExtra : List LinstrRM :=
  [(LinstrR.Lopn [.reg "a1"] "ADD:64" [.reg "r3", .imm 0], MemTag.reg none)]

/-- Guard tail: land the SSA guard result (`r6`) into the register `g` the `Lcond`
    reads (`g := r6 + 0`). -/
def vGuardExtra : List LinstrRM :=
  [(LinstrR.Lopn [.reg "g"] "ADD:64" [.reg "r6", .imm 0], MemTag.reg none)]

/-- The front-compiled body `Com` (or `none`). -/
def vBodyCom : Option (Com jasminDialect (mapCtx vΓ) (mapTy (.sword 64))) :=
  frontLoopBodyJ (accCTy := .sword 64) vVm "x2" vBody

/-- The front-emitted full loop body: `straightOpsMemCall` image + the `x`-persist
    tail. -/
def vFullBody : List LinstrRM :=
  (vBodyCom.map (fun c => frontLoopFullBody 2 vLeafGen c 2 vBodyExtra)).getD []

/-- The front-compiled guardCompute segment (`x < 100` into `g`). -/
def vGuardCompute : List LinstrRM :=
  (guardComputeOfSExpr 2 vLeafGen vVm "g" vGuard 2 vGuardExtra).getD []

/-- The emitted general-guard while program: `whileLinstrRM 0 "g" guardCompute
    fullBody` = `loopLinstrRM 0 "g" (fullBody ++ guardCompute)` — the guardCompute
    recomputes `x < 100` into `g` each pass, then `Lcond (.reg "g") 0`. -/
def vWhileProg : LprogM :=
  singletonProgM "f" (whileLinstrRM 0 "g" vGuardCompute vFullBody)

/-- Start: `x = 0` (in `a1`), `step = 25` (in `a0`). -/
def vStart : LstatePMC :=
  { base := ((({} : LstateM).setReg "a0" (25#64)).setReg "a1" (0#64))
    lfn := "f"
    rstack := [] }

/-- **(a) The comparison guard front-compiles** (to a non-empty guardCompute). -/
theorem vGuard_frontCompiles :
    (guardComputeOfSExpr 2 vLeafGen vVm "g" vGuard 2 vGuardExtra).isSome = true
      ∧ vBodyCom.isSome = true := by native_decide

/-- **(a′) A raw `SLt` guard is DECLINED** (no scalar `<` word op in the dialect;
    comparisons must be expressed branch-free). -/
theorem vSLt_declined :
    (guardComputeOfSExpr 2 vLeafGen vVm "g" (.SLt (.SVar "x") (.SLit 100)) 2 vGuardExtra).isSome
      = false := by native_decide

/-- **(b) The emitted program carries a REAL `Lcond` back-edge and a NON-empty
    front-compiled guardCompute** — a genuine general-guard loop, not a `name != 0`
    countdown with an empty guard segment. -/
theorem vWhile_realBackEdge_nonemptyGuard :
    hasBackEdge vWhileProg.body = true ∧ vGuardCompute ≠ [] := by native_decide

/-- **(c) denote = `runWhileMem` do-while fold via A3's interpreter.** A3's
    `lsemFuelMemLC` follows the guard-driven `Lcond` back-edge, the guardCompute
    recomputing `x < 100` into `g` each pass, until the comparison flips at
    `x = 100`, and `x` decodes equal to the `runWhileMem` (guard `x < 100`)
    do-while denotation of `fullBody ++ guardCompute` over the same start. -/
theorem vWhile_denote_eq_runWhileMem :
    (lsemFuelMemLC (fun _ => none) vWhileProg 200 vStart).map
        (fun t => decodeM t.base "a1" 64)
      = (runWhileMem (fun _ => none) (fun b => condNZ b (.reg "g"))
          (vFullBody ++ vGuardCompute) 20 vStart.base).map
          (fun b => decodeM b "a1" 64) := by native_decide

/-- **(c′) The decoded result is `x = 100`** — the loop ran until the comparison
    `x < 100` went false. -/
theorem vWhile_denote_eq_100 :
    (lsemFuelMemLC (fun _ => none) vWhileProg 200 vStart).map
        (fun t => decodeM t.base "a1" 64) = some (some (100#64)) := by native_decide

/-- **(c″) The data-dependent trip count is read off the run.** `whileTripsMem` for
    the general-guard body equals `4` — determined at run time by when `x` reaches
    `100` (`0 → 25 → 50 → 75 → 100`), not supplied as a proof parameter. -/
theorem vWhile_trips :
    whileTripsMem (fun _ => none) (fun b => condNZ b (.reg "g"))
        (vFullBody ++ vGuardCompute) 20 vStart.base = 4 := by native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuardWhile
