/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDataWhile
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDataWhile
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieWhile
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieWhile

@[expose] public section

set_option autoImplicit false

/-!
# Front-compiling a data-dependent `while (n != 0)` into a `ComL.whileNz`

`TranslateDialectDataWhile.rolledWhileNz` front-compiles a covered while body
and wraps it in A3's `whileLinstrRM` **at the instruction level** — there is no
`ComL` value on that route, so the export chain has a spec-fold endpoint
(`whileMem_export_faithful` ends at `runWhileMem`) but no source tie. This
module is the source-node half, mirroring
`TranslateDialectRuntimeLoop.rolledForLoopNRt`: the SAME `frontLoopBodyJ` body
front-compile, wrapped in the `ComL.whileNz` node (`JasminLprogExport`) — the
committed `RWhileNz` countdown idiom `while (n != 0) { …body…; n -= 1 }`, whose
lowering is the runtime counted loop `forLoopLcmdNRt` seeded from the guard (a
zero-trip top guard, one body copy, a bottom-test back-edge) and whose source tie
for the instruction-level `whileLinstrRM` shape is
`JasminLsemMemSourceTieWhile.whileMem_export_faithful_comL`.

```
  bodyLowCT  (RArrLoad / RScalarSetExpr over the loop counter `idx`)
    --(frontLoopBodyJ)------------------------>  Com jasminDialect = JLoopBodyN.update
    --(ComL.whileNz update guard init invs)--->  ComL   (countdown node, seed `guard`)
    --(comLToBody / forLoopLcmdNRt)----------->  Lcmd   (`Lcond Z` skip, ONE body copy,
                                                          bottom-test `Lcond NZ`)
```

## Design: the guard-driven analogue of `rolledForLoopNRt`

* no new `LowCT` constructor (`RWhileNz` already exists) and no new
  `catCryptDialect` op;
* the loop body reuses `frontLoopBodyJ` verbatim (nothing hand-authored);
* the export node `ComL.whileNz`, its denotation and its lowering arm live in
  `JasminLprogExport`;
* the **only** delta versus `rolledForLoopNRt` is: the count-driven
  `ComL.forLoopNRt update count` is replaced by the guard-driven
  `ComL.whileNz update guard`, whose counter is seeded from the guard register;
  the machine trip is data-dependent (A3's `whileTripsMem`, read off the run),
  and for the countdown idiom it equals the seed, the count `denote` folds.

## Validation (`native_decide`)

The residual shape `while (n != 0) { n -= 1; acc += a[i] }` (scalar accumulate
over a 3-element array, countdown guard `n`):

* `whileAccum_isSome` — the body front-compiles and wraps into ONE `ComL.whileNz`;
* `whileAccum_is_whileNz_node` — the spine is the while node;
* `whileAccum_denote_n3` / `_n2` — `ComL.denote = 60` at seed `n = 3` and `= 30`
  at `n = 2` (SAME program — the trip is read off the seed, not baked in);
* `whileAccum_machine_matches_denote` — A3's `lsemFuelMemLC` run of the emitted
  `whileLinstrRM 0 "n" []` do-while over the SAME front body decodes the
  accumulator to `ComL.denote` — machine run = source denotation at a concrete
  seed;
* `whileAccum_trips_data_dependent` — the machine trip `whileTripsMem = 3` is
  read off the run (the initial `n`), not supplied;
* `whileAccum_lowering_guarded` — the `comLToBody` lowering carries exactly ONE
  `Lcond NZ` back-edge and ONE `Lcond Z` zero-trip guard, `forLoopNRt`'s
  top-guarded shape.

**All goals closed; axioms ⊆ {propext, Classical.choice, Quot.sound} (+
`Lean.ofReduceBool` for the `native_decide` validates).**
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhileNode

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
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)

/-! ## 1. Wrapping the front body into a `ComL.whileNz`

The continuation is the primitive parameter: `rolledWhileNzComL` is
`rolledWhileNzComLCont` at `cont := .ret .here`. -/

/-- Build a **data-dependent do-while** `ComL.whileNz` from a
    front-compiled loop body. Identical to
    `TranslateDialectRuntimeLoop.rolledForLoopNRtCont` except the wrapper: the
    count-driven `forLoopNRt` is replaced by the guard-driven `whileNz` (the
    `RWhileNz` countdown idiom, lowered through `forLoopLcmdNRt` with the counter
    seeded from the guard).

    * `guard` is the in-scope runtime countdown seed (`.reg 64`) — the guard
      register's initial value, the data-dependent trip the run realises;
    * `init` is the in-scope accumulator seed variable;
    * `invs` are the in-scope loop-invariant seed variables (input array bases);
    * the loop body is `frontLoopBodyJ vmBody accName body` over
      `Γbody = accCTy :: .sword 64 :: invCTys` (its jasmin image is definitionally
      the `whileNz` `update` over `accTy := mapTy accCTy`,
      `invTys := invCTys.map mapTy`).

    `cont : ComL (mapTy accCTy :: Γouter) s` runs after the sweep, with the
    sweep's final accumulator bound at `.here`, so a sweep can sit mid-chain with
    further phases as its continuation. `none` if the front declines. -/
def rolledWhileNzComLCont {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx} {s : JasminTy}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (guard : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s) :
    Option (ComL Γouter s) :=
  match frontLoopBodyJ (accCTy := accCTy) vmBody accName body with
  | some update => some (ComL.whileNz update guard init invs cont)
  | none => none

/-- Build a **data-dependent do-while** `ComL.whileNz` from a front-compiled loop
    body, binding the loop result and returning it — `rolledWhileNzComLCont` at
    `cont := .ret .here`. `none` if the front declines. -/
def rolledWhileNzComL {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (guard : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy)) :=
  rolledWhileNzComLCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
    vmBody accName body guard init invs (.ret .here)

/-- **While-node-wrapper denotation = the countdown fold at the seed.** When the
    body front-compiles to `update`, the `ComL.whileNz`'s denotation at any
    valuation is the `(guard.lookup V).toNat`-fold `JLoopBodyN.denote` of
    `update` — the trip count the countdown guard exit realises, seeded by
    `init` and threading the invariants `invs`. Structural (`ComL.denote` on
    `whileNz`), no open goals. -/
theorem rolledWhileNzComL_denote {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (guard : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update)
    (V : Ctxt.Valuation Γouter) :
    (rolledWhileNzComL (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        vmBody accName body guard init invs).map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨(guard.lookup V).toNat, update⟩
                (Expr.lookupArgs invs V) (init.lookup V)) := by
  unfold rolledWhileNzComL rolledWhileNzComLCont
  rw [hupd]
  rfl

/-! ## 2. Validate: the countdown accumulate `while (n != 0) { n--; acc += a[i] }` -/

/-- `RSeq`-chain a list of `LowCT`. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-- The covered while body: `ai := a[idx]; acc2 := acc + ai` — one per-iteration
    accumulate over the array at the up-counting index (the countdown `n -= 1` is
    the node-managed guard tail, exactly as A3's emitted `extra`). -/
def whileBody : LowCT := seqAll [
  .RArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes 24⟩ "idx",
  .RScalarSetExpr "acc2" (.SAdd (.SVar "acc") (.SVar "ai")) ]

/-- Body context `[acc, idx, a]`: scalar accumulator, loop index, input array. -/
def whileΓ : Ctx := [.sword 64, .sword 64, .memref 3]

/-- Body VarMap: `acc ↦ .here`, `idx`, `a`. -/
def whileVm : VarMap whileΓ :=
  (((VarMap.empty.bind (t := .memref 3) "a").bind
      (t := .sword 64) "idx").bind (t := .sword 64) "acc")

/-- The outer (kernel-argument) jasmin context: `[n (guard), acc, a]`. -/
def Γouter : Ctxt jasminDialect := [.reg 64, .reg 64, .stackArr 64 3]

/-- The front-compiled data-dependent while: guard seed `n`, accumulator `acc`,
    invariant array `a`. ONE `ComL.whileNz` spine, the body front-compiled. -/
def whileAccum (_ : Unit) : Option (ComL Γouter (.reg 64)) :=
  rolledWhileNzComL (Γouter := Γouter) (accCTy := .sword 64) (invCTys := [.memref 3])
    whileVm "acc2" whileBody
    (guard := .here)                             -- n
    (init := .there .here)                       -- acc
    (invs := .cons (.there (.there .here)) .nil) -- a

/-- The body front-compiles and wraps into ONE `ComL.whileNz`. -/
theorem whileAccum_isSome : (whileAccum ()).isSome := by native_decide

/-- The spine is the data-dependent while node. -/
theorem whileAccum_is_whileNz_node :
    ((whileAccum ()).map (fun c => match c with
      | .whileNz _ _ _ _ _ => true
      | _ => false))
      = some true := by native_decide

/-- Outer valuation at guard seed `n`: `n`, `acc = 0`, `a = [10, 20, 30]`. -/
def valAt (n : Nat) : Ctxt.Valuation Γouter :=
  .cons (BitVec.ofNat 64 n)
    (.cons (0 : BitVec 64) (.cons (![10#64, 20#64, 30#64] : Fin 3 → BitVec 64) .nil))

/-- **denote at seed `n = 3` is `10 + 20 + 30 = 60`** — three data-dependent
    trips, the accumulate over `a[0..2]`. -/
theorem whileAccum_denote_n3 :
    ((whileAccum ()).map (fun c => BitVec.toNat (ComL.denote c (valAt 3)))) = some 60 := by
  native_decide

/-- **denote at seed `n = 2` is `10 + 20 = 30`** (SAME program): the trip count
    is read off the guard seed, not baked in. -/
theorem whileAccum_denote_n2 :
    ((whileAccum ()).map (fun c => BitVec.toNat (ComL.denote c (valAt 2)))) = some 30 := by
  native_decide

/-! ## 3. Machine run = `ComL.denote`

The SAME front body, lowered by `straightOpsMemCall` and wrapped in A3's
emitted do-while `whileLinstrRM 0 "n" []` (the `rolledWhileNz` route — real
bottom-test `Lcond` back-edge on the countdown register `n`), run by A3's
`lsemFuelMemLC`: the accumulator register decodes to the front node's
`ComL.denote` at the matching seed, and the trip is read off the run. -/

/-- The front-compiled `JLoopBodyN.update` for the while body (or `none`). -/
def whileFrontJ (_ : Unit) :
    Option (Com jasminDialect (mapCtx whileΓ) (mapTy (.sword 64))) :=
  frontLoopBodyJ (accCTy := .sword 64) whileVm "acc2" whileBody

/-- The front-lowered per-iteration body (`straightOpsMemCall`, no leaf calls);
    `[]` if the front declined. `nArgs = 3` (the update body's context slots). -/
def whileFrontBody (_ : Unit) : List LinstrRM :=
  ((whileFrontJ ()).map (fun c => straightOpsMemCall 3 (fun _ _ _ => none) c 3)).getD []

/-- The front body's result register (the next-accumulator slot the feedback
    copies back), read off the front image. -/
def whileFrontRet (_ : Unit) : String :=
  ((whileFrontJ ()).map (fun c => comRetReg 3 argName c 3)).getD "r0"

/-- The full A3 do-while body: the front body, then the accumulator feedback
    (`a2 := <ret>`), the index advance (`a1 += 1`), and the countdown
    (`n -= 1`) — the `extra` tail of the committed `rolledWhileNz` shape. -/
def whileMachineBody (_ : Unit) : List LinstrRM :=
  whileFrontBody () ++
  [ (LinstrR.Lopn [.reg "a2"] "ADD:64" [.reg (whileFrontRet ()), .imm 0], MemTag.reg none)
  , (LinstrR.Lopn [.reg "a1"] "ADD:64" [.reg "a1", .imm 1], MemTag.reg none)
  , (LinstrR.Lopn [.reg "n"]  "SUB:64" [.reg "n", .imm 1], MemTag.reg none) ]

/-- The emitted data-dependent do-while program (`whileLinstrRM 0 "n" []` — the
    bottom-test back-edge on the countdown register). -/
def whileMachineProg (_ : Unit) : LprogM :=
  singletonProgM "f" (whileLinstrRM 0 "n" [] (whileMachineBody ()))

/-- Machine start at seed `n`: `acc = 0` (`a2`), `idx = 0` (`a1`), the countdown
    `n`, array `a0 = [10, 20, 30]`. -/
def whileMachineStart (n : Nat) : LstatePMC :=
  { base :=
      ((((({} : LstateM).setReg "a2" (0#64)).setReg "a1" (0#64)).setReg
        "n" (BitVec.ofNat 64 n)).setArr
        "a0" (![10#64, 20#64, 30#64] : Fin 3 → BitVec 64))
    lfn := "f"
    rstack := [] }

/-- **Machine run = `ComL.denote` at a concrete seed.** A3's `lsemFuelMemLC`
    follows the bottom-test `Lcond` back-edge until the countdown reaches `0` —
    the trip fixed at run time by the seed `n = 3` — and the accumulator decodes
    to the front-compiled `ComL.whileNz` node's `ComL.denote` at the same seed
    (both `= 60`). -/
theorem whileAccum_machine_matches_denote :
    (lsemFuelMemLC (fun _ => none) (whileMachineProg ()) 60 (whileMachineStart 3)).map
        (fun t => decodeM t.base "a2" 64)
      = ((whileAccum ()).map (fun c => some (ComL.denote c (valAt 3)))) := by
  native_decide

/-- **The data-dependent trip is read off the run:** `whileTripsMem = 3` — the
    number of do-while iterations before the countdown register hits `0`,
    determined by the initial `n = 3`, not supplied as a proof parameter. -/
theorem whileAccum_trips_data_dependent :
    whileTripsMem (fun _ => none) (fun b => condNZ b (.reg "n"))
        (whileMachineBody ()) 10 (whileMachineStart 3).base = 3 := by
  native_decide

/-! ## 4. The lowering is the zero-trip-guarded counted loop -/

/-- Collect the `Lcond` labels of an `Lcmd` by flag condition name. -/
def condEdges (cc : String) (body : Lcmd) : List LLabel :=
  body.filterMap (fun i =>
    match i.li_i with
    | .Lcond (.reg c) lbl => if c = cc then some lbl else none
    | _ => none)

/-- The `comLToBody` lowering of the while node carries exactly **one**
    `Lcond NZ` back-edge (the bottom test at the loop top label) and exactly
    **one** `Lcond Z`, the zero-trip top guard that skips the loop at seed `0`. -/
theorem whileAccum_lowering_guarded :
    ((whileAccum ()).map (fun c =>
        let body := comLToBody 3 argName (fun _ => none) c 3
        (condEdges "NZ" body).length == 1 && (condEdges "Z" body).length == 1))
      = some true := by native_decide

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhileNode
