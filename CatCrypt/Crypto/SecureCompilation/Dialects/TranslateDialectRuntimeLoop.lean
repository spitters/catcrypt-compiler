/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop

@[expose] public section

set_option autoImplicit false

/-!
# Front-compiling a LowCT loop body to a `ComL.forLoopNRt` (runtime-trip emit)

`TranslateDialectRolledLoop.rolledForLoopN` front-compiles a covered LowCT loop
body and wraps it in a `ComL.forLoopN` whose trip count is a **compile-time**
`Nat` (`MOV Lctr, #N`). Several deployed kernels — the FAEST `ConvertToVole`
family (`num`/`depth`/`nblk` come from `cfg`), the `poly1305_mac_hacl(out, inp,
nblk)` shape — need the trip count to be a **runtime argument** instead: the
back-edge must be seeded `MOV Lctr, <argReg>` (a register read at run time), not
`MOV Lctr, #N` (an immediate).

This module adds the **runtime-count** front path. It reuses
`TranslateDialectRolledLoop.frontLoopBodyJ` verbatim (the loop body is plain
covered LowCT, front-compiled by the existing `translateDialectControl` →
`cryptoDialectToJasminCom`), and wraps the front body in a `ComL.forLoopNRt`
instead of a `ComL.forLoopN`: the same `JLoopBodyN.update`-shaped body, but folded
`(count.lookup V).toNat` times from an in-scope `.reg 64` variable `count`.

```
  bodyLowCT  (RArrLoad / RScalarSetExpr / RArrStore over the loop counter `idx`)
    --(translateDialectControl on Γbody = accCTy :: .sword 64 :: invCTys)-->  Com catCryptDialect
    --(cryptoDialectToJasminCom)-------------------------------------------->  Com jasminDialect = JLoopBodyN.update
    --(ComL.forLoopNRt update count init invs (ret acc))-------------------->  ComL  (ONE body copy + back-edge)
    --(ComL.toLprogPhysAbi / renderLprogAtt)------------------------------->  .s     (MOV Lctr, <argReg>, `jne .L<d>`)
```

## Design: the runtime-count analogue of `rolledForLoopN`

Everything that is compile-time-`N`-independent is shared with the fixed-trip
path:

* no new `LowCT` constructor (the unrolling `RFor` is untouched);
* no new `catCryptDialect` op;
* the loop body reuses the already-proven `IsCovered`/simulation/leak-factoring
  fragment verbatim (`frontLoopBodyJ`);
* the export node `ComL.forLoopNRt`, its denotation, and its lowering
  (`forLoopLcmdNRt`, which seeds `MOV Lctr, <countReg>`) already exist in
  `JasminLprogExport`.

The **only** delta versus `rolledForLoopN` is: the static `N : Nat` is replaced by
a runtime `count : Ctxt.Var Γouter (.reg 64)`, and `ComL.forLoopN ⟨N, update⟩` by
`ComL.forLoopNRt update count`. The `count` variable never passes through the
front (only the loop body does); it is an outer-context argument threaded straight
into the export node. This unblocks FAEST `ConvertToVole`, whose trip counts
(`num`, `depth`, `nblk`) are runtime `cfg` values.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 1. Wrapping the front body into a `ComL.forLoopNRt`

`ComL.forLoopNRt` needs the body as a `Com jasminDialect (accTy :: .reg 64 ::
invTys) accTy` — exactly the `JLoopBodyN.update` shape `frontLoopBodyJ` produces.
When the body context is `Γbody = accCTy :: .sword 64 :: invCTys`,
`mapCtx Γbody = mapTy accCTy :: .reg 64 :: invCTys.map mapTy` reduces by `rfl`
(`mapCtx = List.map mapTy`, `mapTy (.sword 64) = .reg 64`), so the front body is
*definitionally* a runtime-loop `update` over `accTy := mapTy accCTy`,
`invTys := invCTys.map mapTy`. -/

/-- Build a **runtime-trip** rolled `ComL.forLoopNRt` from a front-compiled loop
    body, with a caller-supplied continuation. Identical to
    `TranslateDialectRolledLoop.rolledForLoopNCont` except the trip count is an
    in-scope `.reg 64` variable `count` (read at run time), not a static `Nat`.

    * `Γouter` is the outer context (the kernel's argument slots, jasmin types);
    * `count` is the in-scope runtime trip-count variable (`.reg 64`); the lowering
      seeds the loop counter `MOV Lctr, <count-reg>` from it, not `MOV Lctr, #N`;
    * `init` is the in-scope accumulator seed variable;
    * `invs` are the in-scope loop-invariant seed variables (input array bases);
    * the loop body is `frontLoopBodyJ vmBody accName body` over
      `Γbody = accCTy :: .sword 64 :: invCTys` (so its jasmin image matches
      `accTy :: .reg 64 :: invTys`);
    * `cont : ComL (mapTy accCTy :: Γouter) s` runs after the loop, with the
      loop's final accumulator bound at `.here` — passing the front-compiled next
      phase sequences the phases.

    `none` iff the front declines the body. -/
def rolledForLoopNRtCont {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx} {s : JasminTy}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (count : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s) :
    Option (ComL Γouter s) :=
  match frontLoopBodyJ (accCTy := accCTy) vmBody accName body with
  | some update =>
      -- `mapCtx (accCTy :: .sword 64 :: invCTys)` reduces to
      -- `mapTy accCTy :: .reg 64 :: invCTys.map mapTy` definitionally, so `update`
      -- is directly the `ComL.forLoopNRt` body over `invTys := invCTys.map mapTy`.
      some (ComL.forLoopNRt update count init invs cont)
  | none => none

/-- Build a **runtime-trip** rolled `ComL.forLoopNRt` from a front-compiled
    loop body. Identical to `TranslateDialectRolledLoop.rolledForLoopN` except the
    trip count is an in-scope `.reg 64` variable `count` (read at run time), not a
    static `Nat`.

    * `Γouter` is the outer context (the kernel's argument slots, jasmin types);
    * `count` is the in-scope runtime trip-count variable (`.reg 64`); the lowering
      seeds the loop counter `MOV Lctr, <count-reg>` from it, not `MOV Lctr, #N`;
    * `init` is the in-scope accumulator seed variable;
    * `invs` are the in-scope loop-invariant seed variables (input array bases);
    * the loop body is `frontLoopBodyJ vmBody accName body` over
      `Γbody = accCTy :: .sword 64 :: invCTys` (so its jasmin image matches
      `accTy :: .reg 64 :: invTys`).

    Returns a `ComL Γouter accTy` that binds the loop result and returns it —
    `rolledForLoopNRtCont` at `cont := .ret .here`. `none` if the front
    declines. -/
def rolledForLoopNRt {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (count : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy)) :=
  rolledForLoopNRtCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
    vmBody accName body count init invs (.ret .here)

/-! ## 2. Loop-wrapper simulation skeleton

The runtime-loop structure is a pure `ComL.forLoopNRt` wrapper over the
front-compiled body `update`. Its denotation is, by `ComL.denote`'s definition,
exactly the `JLoopBodyN.denote` fold of `update` over the *runtime* trip count
`(count.lookup V).toNat` — the mathematical ground truth the rolled back-edge
realises (`forLoopLcmdNRt` seeds the counter from the `count` register and drives
the same `jne`-loop step-for-step). This ties the loop wrapper to the (separately
covered) body fragment with no open goals: the body's own correctness is the
`IsCovered` / `rustExecSimulatesDialect` story for `translateDialectControl`,
reused verbatim; the wrapper contributes only the fold. -/

/-- **Runtime-loop-wrapper denotation = `JLoopBodyN.denote` fold at the runtime
    count.** When the body front-compiles to `update`, the runtime-trip
    `ComL.forLoopNRt`'s denotation at any valuation is the
    `(count.lookup V).toNat`-fold `JLoopBodyN.denote` of `update` over the loop
    index, seeded by `init` and threading the invariants `invs`. Structural
    (`ComL.denote` on `forLoopNRt`), no open goals. -/
theorem rolledForLoopNRt_denote {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (count : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update)
    (V : Ctxt.Valuation Γouter) :
    (rolledForLoopNRt (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        vmBody accName body count init invs).map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨(count.lookup V).toNat, update⟩
                (Expr.lookupArgs invs V) (init.lookup V)) := by
  unfold rolledForLoopNRt rolledForLoopNRtCont
  rw [hupd]
  rfl

/-! ## 3. Top-level: runtime-count loop body → owned `Lprog` via the committed export

`rolledForLoopNRtLprog` composes `rolledForLoopNRt` with the committed multi-pointer
memref ABI export `ComL.toLprogPhysAbi`, which routes a runtime count through the
3rd+ SysV integer register. The result is a runtime-trip rolled `Lprog` — ONE body
copy, a real `jne .L<d>` back-edge, a `MOV Lctr, <argReg>` counter seed — with NO
hand-built body `Com`. -/

/-- The owned runtime-trip rolled `Lprog` for a front-compiled loop body, via the
    committed memref ABI looped export. `abiArgs` carries the runtime count in a
    trailing integer register (e.g. `["RDI", "RSI", "RDX"]` with `RDX = count`). -/
def rolledForLoopNRtLprog {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (count : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (fname outArg : String) (inArgs : List String)
    (abiArgs : List String) (abiTyin : List Nat) : Option Lprog :=
  (rolledForLoopNRt (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
      vmBody accName body count init invs).map
    (fun c =>
      ComL.toLprogPhysAbi c fname outArg inArgs
        (fun _ => none) (fun _ => none) abiArgs abiTyin)

/-! ## 4. Front-compiling a **nested** runtime loop (`ComL.forLoopNRtNested`)

`rolledForLoopNRt` above rolls a single runtime loop. Several kernels need a
runtime loop whose per-iteration body is *itself* a runtime loop with a trip
count **recomputed per outer pass** — the FAEST `ConvertToVole` GGM Phase-3
`num >> (jd+1)` shape, `fri_proof`'s layer→query nest, `honest_prove`. The
`ComL.forLoopNRtNested` node makes the inner loop first-class; this combinator is
its front half.

Both the inner-count body and the inner-update body are front-compiled by
`frontLoopBodyJ` verbatim — nothing is hand-authored:

* the **inner-count** body runs over `Γcount = .sword 64 (outer index) :: invCTys`
  and returns a `.sword 64` value (the per-outer inner trip, `num >> (jd+1)`);
  `frontLoopBodyJ` lowers it to `Com jasminDialect (.reg 64 :: invTys) (.reg 64)`;
* the **inner-update** body runs over
  `Γbody = accCTy :: .sword 64 (inner index) :: .sword 64 (outer index) :: invCTys`
  and returns `accCTy`; `frontLoopBodyJ` lowers it to
  `Com jasminDialect (accTy :: .reg 64 :: .reg 64 :: invTys) accTy`.

`mapCtx (.sword 64 :: invCTys) = .reg 64 :: invCTys.map mapTy` and
`mapCtx (accCTy :: .sword 64 :: .sword 64 :: invCTys) =
 mapTy accCTy :: .reg 64 :: .reg 64 :: invCTys.map mapTy` both reduce by `rfl`, so
the two front bodies are *definitionally* the `forLoopNRtNested` fields over
`invTys := invCTys.map mapTy`. -/

/-- Build a **nested runtime-trip** `ComL.forLoopNRtNested` from two
    front-compiled bodies — the inner-count body (per-outer recompute) and the
    inner-update body — with a runtime outer count and a caller-supplied
    continuation. The inner loop is first-class: its trip count is recomputed from
    the outer index each outer pass. `cont : ComL (mapTy accCTy :: Γouter) s` runs
    after the nest, with its final accumulator bound at `.here`, so a nest can sit
    mid-chain with further phases as its continuation. `none` if either body's
    front declines. -/
def rolledForLoopNRtNestedCont {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx} {s : JasminTy}
    (vmCount : VarMap (.sword 64 :: invCTys)) (countName : String) (countBody : LowCT)
    (vmBody : VarMap (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (accName : String)
    (updateBody : LowCT)
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s) :
    Option (ComL Γouter s) :=
  match frontLoopBodyJ (accCTy := .sword 64) (Γbody := .sword 64 :: invCTys)
          vmCount countName countBody,
        frontLoopBodyJ (accCTy := accCTy)
          (Γbody := accCTy :: .sword 64 :: .sword 64 :: invCTys) vmBody accName updateBody with
  | some innerCount, some innerUpdate =>
      some (ComL.forLoopNRtNested innerCount innerUpdate outerCount init invs cont)
  | _, _ => none

/-- Build a **nested runtime-trip** `ComL.forLoopNRtNested` from two
    front-compiled bodies — the inner-count body (per-outer recompute) and the
    inner-update body — with a runtime outer count. The inner loop is first-class:
    its trip count is recomputed from the outer index each outer pass.
    `rolledForLoopNRtNestedCont` at `cont := .ret .here`. `none` if either body's
    front declines. -/
def rolledForLoopNRtNested {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (vmCount : VarMap (.sword 64 :: invCTys)) (countName : String) (countBody : LowCT)
    (vmBody : VarMap (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (accName : String)
    (updateBody : LowCT)
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy)) :=
  rolledForLoopNRtNestedCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
    vmCount countName countBody vmBody accName updateBody outerCount init invs
    (.ret .here)

/-- **Nested-runtime-loop-wrapper denotation = `JLoopBodyN.nestedDenote` fold.**
    When both bodies front-compile, the `ComL.forLoopNRtNested`'s denotation at any
    valuation is the outer×inner double fold `JLoopBodyN.nestedDenote` — the outer
    loop over `(outerCount.lookup V).toNat`, the inner trip recomputed per outer
    pass via `innerCount`, applying `innerUpdate` innermost. Structural
    (`ComL.denote` on `forLoopNRtNested`), no open goals. -/
theorem rolledForLoopNRtNested_denote {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (vmCount : VarMap (.sword 64 :: invCTys)) (countName : String) (countBody : LowCT)
    (vmBody : VarMap (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (accName : String)
    (updateBody : LowCT)
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {innerCount : Com jasminDialect (mapCtx (.sword 64 :: invCTys)) (mapTy (.sword 64))}
    {innerUpdate : Com jasminDialect
      (mapCtx (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hcnt : frontLoopBodyJ (accCTy := .sword 64) (Γbody := .sword 64 :: invCTys)
              vmCount countName countBody = some innerCount)
    (hupd : frontLoopBodyJ (accCTy := accCTy)
              (Γbody := accCTy :: .sword 64 :: .sword 64 :: invCTys)
              vmBody accName updateBody = some innerUpdate)
    (V : Ctxt.Valuation Γouter) :
    (rolledForLoopNRtNested (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        vmCount countName countBody vmBody accName updateBody outerCount init invs).map
        (fun c => ComL.denote c V)
      = some (JLoopBodyN.nestedDenote innerCount innerUpdate (outerCount.lookup V).toNat
                (Expr.lookupArgs invs V) (init.lookup V)) := by
  unfold rolledForLoopNRtNested rolledForLoopNRtNestedCont
  rw [hcnt, hupd]
  rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
