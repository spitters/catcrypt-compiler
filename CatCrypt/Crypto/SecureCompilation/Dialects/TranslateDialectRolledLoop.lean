/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd
public import CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect

@[expose] public section

set_option autoImplicit false

/-!
# Front-compiling a LowCT loop body to a `ComL.forLoopN` (rolled emit)

The straight-line front (`TranslateDialectDirectControl.translateDialectControl`
→ `DialectToJasminCom.cryptoDialectToJasminCom`) lowers a `LowCT` to a
**straight-line** `Com jasminDialect`. Its `RFor` arm is a *static unroll*
(`loopRForD` emits one body copy per trip), which overflows at deployed sizes and
produces `N` copies of the body in the `.s`.

This module adds the **rolled** front path: it front-compiles a single LowCT loop
*body* (the covered fragment — `RArrLoad`/`RScalarSetExpr`/`RArrStore` over memref
arrays, with the loop counter as the array index) into the
`JLoopBodyN.update`-shaped straight-line `Com jasminDialect`, then wraps it in a
`ComL.forLoopN` node (ONE body copy + a real back-edge). The
loop-counter variable feeds `RArrLoad`/`RArrStore` as a per-trip dynamic index
(`memrefGetDyn`/`memrefSetDyn` → `stackLoad`/`stackStore` SIB `LOADIDX`/`STOREIDX`
at the runtime trip counter), exactly the `N = 4` PoC pattern of
`MAYO/KernelFromRustcmdFrontEmit.lean`, except that the index is the *loop binder*,
not a materialised constant, and the trip is a real counted loop.

```
  bodyLowCT  (RArrLoad acc/in[idx] … RArrStore out[idx] … over the loop counter `idx`)
    --(translateDialectControl on Γbody = [acc, idx, *invs])-->  Com catCryptDialect
    --(cryptoDialectToJasminCom)----------------------------->  Com jasminDialect = JLoopBodyN.update
    --(ComL.forLoopN ⟨N, update⟩ init invs (ret acc))-------->  ComL  (ONE body copy + back-edge)
    --(ComL.toLprogPhysAbi / renderLprogAtt)---------------->  .s     (a real `jne .L<d>`)
```

## Design: an export-level wrapper, not a new LowCT constructor

The rolled-loop structure is an **export-level** `ComL.forLoopN` wrapper (the
loop nodes live in `ComL`, an extension of `Com jasminDialect`, not in `LowCT` or
`catCryptDialect`). Every existing rolled emit (QRUOV/SDitH/MAYO `*RolledEmit`)
is built by hand-authoring exactly such a `ComL.forLoopN` over a hand-built body
`Com`. In this module the body is produced by the **verified front** instead:
the loop body is plain covered LowCT, front-compiled by the existing
`translateDialectControl`, so:

* no new `LowCT` constructor (the unrolling `RFor` is untouched);
* no new `catCryptDialect` op;
* the loop body reuses the already-proven `IsCovered`/simulation/leak-factoring
  fragment verbatim — the loop is a pure structural wrapper over it.

A covered LowCT loop body front-compiles to the `JLoopBodyN.update` Com that the
committed `ComL.forLoopN` export consumes, so the 5 deployed GF-MQ kernels
(MAYO/SNOVA/UOV/QRUOV/SDitH) are front-compilable at deployed sizes (rolled,
bounded depth) rather than hand-built.

## Main results

* `LoopBodyFront` / `frontLoopBodyCDWith` / `frontLoopBodyJWith` — the loop-body
  front as a parameter: a `LowCT → catCryptDialect` translator, the capped
  `Com catCryptDialect`, and its `JLoopBodyN.update`-shaped jasmin image.
* `frontLoopBodyCD` / `frontLoopBodyJ` — the scalar front loop body, capped with
  `ret accName` and lowered to the `JLoopBodyN.update` shape.
* `rolledForLoopN` / `rolledForLoopN_denote` — the fixed-trip `ComL.forLoopN`
  wrapper and its denotation as the `JLoopBodyN.denote` fold.
* `frontLoopBodyCDV` / `frontLoopBodyJV` / `rolledForLoopNV` /
  `rolledForLoopNV_denote` — the vsimd twins.
* `frontLoopBodyCDC` / `frontLoopBodyJC` / `rolledForLoopNC` /
  `rolledForLoopNC_denote` — the carry-select twins, whose body front is
  `CarryChainSelect.translateDialectCarrySelect`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd (translateDialectControlV)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (translateDialectCarrySelect)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 1. The loop body front-compilation

The loop body runs over the catCryptDialect context

```
  Γbody = accCTy :: .sword 64 :: invCTys      -- accumulator, loop index, invariants
```

with a `VarMap` binding the accumulator name (`.here`), the loop-index name
(`.there .here`), and the invariant names (the tail). The front then translates
the body LowCT and we cap it with `ret <accName>` — selecting the (post-store)
accumulator slot, which is the value `JLoopBodyN.update` must return.

`frontLoopBodyCD` is the catCryptDialect image (the front output capped with the
accumulator return); `frontLoopBodyJ` lowers it to the `JLoopBodyN.update`-shaped
`Com jasminDialect`. -/

/-- A `LowCT → catCryptDialect` translator usable as a loop-body front: it maps a
    `VarMap` over any body context and a `LowCT` to the extended context, the
    `Com`-prefix and the updated `VarMap` (`DTransOut`).
    `TranslateDialectDirectControl.translateDialectControl`,
    `CarryChainSelect.translateDialectCarrySelect` and
    `TranslateDialectVsimd.translateDialectControlV` all have this shape. -/
abbrev LoopBodyFront :=
  ∀ {Γ : Ctx}, VarMap Γ → LowCT → Option (TranslateDialectDirect.DTransOut Γ)

/-- Front-compile a loop body LowCT over the body context `Γbody` through the
    front `F`, returning the `Com catCryptDialect` that ends with `ret accName`
    (the value the loop must carry). `vmBody` binds the accumulator/index/
    invariant names to their `Γbody` slots. `none` if `F` declines or `accName`
    is unbound at the final context. -/
def frontLoopBodyCDWith (F : LoopBodyFront) {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT) :
    Option (Com catCryptDialect Γbody accCTy) :=
  match F vmBody body with
  | some r =>
      match r.vm.lookup accName with
      | some ⟨t, v⟩ =>
          if h : t = accCTy then
            r.cont (Com.ret (h ▸ toVIRVar v))
          else none
      | none => none
  | none => none

/-- Lower the `F`-front loop body to the `JLoopBodyN.update`-shaped
    `Com jasminDialect` over `mapCtx Γbody` returning `mapTy accCTy`, via the
    verified `cryptoDialectToJasminCom`. -/
def frontLoopBodyJWith (F : LoopBodyFront) {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT) :
    Option (Com jasminDialect (mapCtx Γbody) (mapTy accCTy)) :=
  match frontLoopBodyCDWith F (accCTy := accCTy) vmBody accName body with
  | some com => DialectToJasminCom.cryptoDialectToJasminCom com
  | none => none

/-- Front-compile a loop body LowCT over the body context `Γbody`, returning the
    `Com catCryptDialect` that ends with `ret accName` (the value the loop must
    carry). `vmBody` binds the accumulator/index/invariant names to their
    `Γbody` slots. `none` if the front declines or `accName` is unbound at the
    final context. -/
def frontLoopBodyCD {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT) :
    Option (Com catCryptDialect Γbody accCTy) :=
  match translateDialectControl vmBody body with
  | some r =>
      match r.vm.lookup accName with
      | some ⟨t, v⟩ =>
          if h : t = accCTy then
            r.cont (Com.ret (h ▸ toVIRVar v))
          else none
      | none => none
  | none => none

/-- Lower the front loop body to the `JLoopBodyN.update`-shaped `Com jasminDialect`
    over `mapCtx Γbody` returning `mapTy accCTy`. -/
def frontLoopBodyJ {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT) :
    Option (Com jasminDialect (mapCtx Γbody) (mapTy accCTy)) :=
  frontLoopBodyJWith translateDialectControl (accCTy := accCTy) vmBody accName body

/-- The scalar instance lowers `frontLoopBodyCD` through
    `cryptoDialectToJasminCom`. -/
theorem frontLoopBodyJ_eq {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT) :
    frontLoopBodyJ (accCTy := accCTy) vmBody accName body
      = (match frontLoopBodyCD (accCTy := accCTy) vmBody accName body with
         | some com => DialectToJasminCom.cryptoDialectToJasminCom com
         | none => none) := rfl

/-! ## 2. Wrapping the front body into a `ComL.forLoopN`

`ComL.forLoopN` needs the body as a `Com jasminDialect (accTy :: .reg 64 :: invTys)
accTy`. When the body context is `Γbody = accCTy :: .sword 64 :: invCTys`,
`mapCtx Γbody = mapTy accCTy :: .reg 64 :: invCTys.map mapTy` reduces by `rfl`
(`mapCtx = List.map mapTy`, `mapTy (.sword 64) = .reg 64`), so the front body is
*definitionally* a `JLoopBodyN.update` over `accTy := mapTy accCTy`,
`invTys := invCTys.map mapTy`. We wrap it in `ComL.forLoopN ⟨N, update⟩ init invs
cont`, with `init`/`invs` the in-scope seeds in the *outer* context and `cont` the
continuation the loop's final accumulator flows into.

The continuation is the primitive parameter: `rolledForLoopN` is
`rolledForLoopNCont` at `cont := .ret .here`. -/

/-- Build a rolled `ComL.forLoopN` from a front-compiled loop body, with a
    caller-supplied continuation.

    * `Γouter` is the outer context (the kernel's argument slots, jasmin types);
    * `init` is the in-scope accumulator seed variable;
    * `invs` are the in-scope loop-invariant seed variables (input array bases);
    * the loop body is `frontLoopBodyJ vmBody accName body` over
      `Γbody = accCTy :: .sword 64 :: invCTys` (so its jasmin image matches
      `accTy :: .reg 64 :: invTys`);
    * `cont : ComL (mapTy accCTy :: Γouter) s` runs after the loop, with the
      loop's final accumulator bound at `.here`.

    The trip count `N` is compile-time, so the loop consumes no count-argument
    register. `none` if the front declines. -/
def rolledForLoopNCont {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx} {s : JasminTy}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s) :
    Option (ComL Γouter s) :=
  match frontLoopBodyJ (accCTy := accCTy) vmBody accName body with
  | some update =>
      -- `mapCtx (accCTy :: .sword 64 :: invCTys)` reduces to
      -- `mapTy accCTy :: .reg 64 :: invCTys.map mapTy` definitionally.
      some (ComL.forLoopN ⟨N, update⟩ init invs cont)
  | none => none

/-- Build a rolled `ComL.forLoopN` from a front-compiled loop body.

    * `Γouter` is the outer context (the kernel's argument slots, jasmin types);
    * `init` is the in-scope accumulator seed variable;
    * `invs` are the in-scope loop-invariant seed variables (input array bases);
    * the loop body is `frontLoopBodyJ vmBody accName body` over
      `Γbody = accCTy :: .sword 64 :: invCTys` (so its jasmin image matches
      `accTy :: .reg 64 :: invTys`).

    Returns a `ComL Γouter accTy` that binds the loop result and returns it —
    `rolledForLoopNCont` at `cont := .ret .here`. `none` if the front
    declines. -/
def rolledForLoopN {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy)) :=
  rolledForLoopNCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
    N vmBody accName body init invs (.ret .here)

/-! ## 2b. Loop-wrapper simulation skeleton

The rolled-loop structure is a pure `ComL.forLoopN` wrapper over the
front-compiled body `update`. Its denotation is, by `ComL.denote`'s definition,
exactly the `JLoopBodyN.denote` fold of `update` over the trip count `N` — the
mathematical ground truth the rolled back-edge realises (`forLoopLcmd`/
`JLoopBodyN.denote_succ` prove the emitted `jne`-loop matches this fold
step-for-step). This ties the loop wrapper to the (separately covered) body
fragment with no open goals: the body's own correctness is the `IsCovered` /
`rustExecSimulatesDialect` story for `translateDialectControl`, reused verbatim;
the wrapper contributes only the fold. -/

/-- **Loop-wrapper denotation = `JLoopBodyN.denote` fold.** When the body
    front-compiles to `update`, the rolled `ComL.forLoopN`'s denotation at any
    valuation is the `N`-fold `JLoopBodyN.denote` of `update` over the loop index,
    seeded by `init` and threading the invariants `invs`. Structural (`ComL.denote`
    on `forLoopN`), no open goals. -/
theorem rolledForLoopN_denote {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update)
    (V : Ctxt.Valuation Γouter) :
    (rolledForLoopN (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        N vmBody accName body init invs).map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨N, update⟩ (Expr.lookupArgs invs V) (init.lookup V)) := by
  unfold rolledForLoopN rolledForLoopNCont
  rw [hupd]
  rfl

/-! ## 2c. The **vsimd** rolled loop body (CAPABILITY G2)

The scalar `rolledForLoopN` routes its body through `translateDialectControl`,
which is the SCALAR front: it has no `.sword 128` binding and does not intercept
`vsimd`-tagged `RCall`s, so a loop whose body is a 128-bit SIMD op at the loop
index (e.g. `acc ^= bf128_mul(x[i], alpha_i)` — a `.sword 128` accumulator XORed
with a `vsimd` product at the runtime index `i`) cannot be rolled.

The fix is purely which front the body flows through: the vsimd-aware
`TranslateDialectVsimd.translateDialectControlV` handles `.sword 128` slots and
the `vsimd.*` / `vpsrldq.*` / `clmul.*` intercepts, and *delegates every
non-vsimd arm* (including `RArrLoad`/`memrefGetDyn` at the loop counter, the
array indexing that feeds the SIMD op) to `translateDialectControl` unchanged.
So the loop body's covered fragment is a strict *superset* of the scalar body's:
scalar arms behave identically, and the SIMD arms are caught as well.

Everything downstream is shared verbatim with the scalar path: the front output
is capped with `ret accName` (`frontLoopBodyCDV`), lowered by the SAME verified
`cryptoDialectToJasminCom` (`frontLoopBodyJV`), and wrapped in the SAME
`ComL.forLoopN` node. When `accCTy = .sword 128`, `mapTy accCTy = .reg 128`, so
the accumulator carried across the back-edge is a 128-bit register — a vsimd
rolled loop with ONE body copy and a real `jne` back-edge. -/

/-- Vsimd twin of `frontLoopBodyCD`: front-compile a loop body LowCT over the body
    context `Γbody` through the **vsimd-aware** `translateDialectControlV`,
    returning the `Com catCryptDialect` that ends with `ret accName`. Identical to
    `frontLoopBodyCD` except the front is `translateDialectControlV`, so a body
    that is (or contains) a `.sword 128` `vsimd`-tagged op at the loop index is
    covered; a purely scalar body front-compiles identically (the vsimd front
    delegates every non-vsimd arm to `translateDialectControl`). -/
def frontLoopBodyCDV {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT) :
    Option (Com catCryptDialect Γbody accCTy) :=
  match translateDialectControlV vmBody body with
  | some r =>
      match r.vm.lookup accName with
      | some ⟨t, v⟩ =>
          if h : t = accCTy then
            r.cont (Com.ret (h ▸ toVIRVar v))
          else none
      | none => none
  | none => none

/-- Vsimd twin of `frontLoopBodyJ`: lower the vsimd front loop body to the
    `JLoopBodyN.update`-shaped `Com jasminDialect` over `mapCtx Γbody` returning
    `mapTy accCTy`, via the SAME verified `cryptoDialectToJasminCom`. -/
def frontLoopBodyJV {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT) :
    Option (Com jasminDialect (mapCtx Γbody) (mapTy accCTy)) :=
  frontLoopBodyJWith translateDialectControlV (accCTy := accCTy) vmBody accName body

/-- The vsimd instance lowers `frontLoopBodyCDV` through
    `cryptoDialectToJasminCom`. -/
theorem frontLoopBodyJV_eq {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT) :
    frontLoopBodyJV (accCTy := accCTy) vmBody accName body
      = (match frontLoopBodyCDV (accCTy := accCTy) vmBody accName body with
         | some com => DialectToJasminCom.cryptoDialectToJasminCom com
         | none => none) := rfl

/-- **CAPABILITY G2** — vsimd twin of `rolledForLoopNCont`: build a rolled
    `ComL.forLoopN` whose body is front-compiled through the vsimd-aware
    `translateDialectControlV` (`frontLoopBodyJV`) rather than the scalar
    `translateDialectControl`. Everything else — the `ComL.forLoopN` wrapper, the
    `mapCtx` context reduction, the `init`/`invs` threading, the continuation
    slot — is identical to the scalar `rolledForLoopNCont`. When
    `accCTy = .sword 128` the loop carries a `.reg 128` accumulator across a real
    back-edge with ONE vsimd body copy.

    * `Γouter` is the outer context (jasmin types);
    * `init` is the in-scope accumulator seed (`.sword 128` for a vsimd loop);
    * `invs` are the in-scope loop-invariant seeds (input array bases);
    * the body is `frontLoopBodyJV vmBody accName body` over
      `Γbody = accCTy :: .sword 64 :: invCTys`;
    * `cont : ComL (mapTy accCTy :: Γouter) s` runs after the loop, with the
      loop's final accumulator bound at `.here`.

    `none` if the vsimd front declines. -/
def rolledForLoopNVCont {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx} {s : JasminTy}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s) :
    Option (ComL Γouter s) :=
  match frontLoopBodyJV (accCTy := accCTy) vmBody accName body with
  | some update =>
      -- `mapCtx (accCTy :: .sword 64 :: invCTys)` reduces to
      -- `mapTy accCTy :: .reg 64 :: invCTys.map mapTy` definitionally.
      some (ComL.forLoopN ⟨N, update⟩ init invs cont)
  | none => none

/-- **CAPABILITY G2** — vsimd twin of `rolledForLoopN`: the rolled
    `ComL.forLoopN` over the vsimd-front body, binding and returning the loop
    result. `rolledForLoopNVCont` at `cont := .ret .here`. -/
def rolledForLoopNV {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy)) :=
  rolledForLoopNVCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
    N vmBody accName body init invs (.ret .here)

/-- **Vsimd loop-wrapper denotation = `JLoopBodyN.denote` fold.** When the vsimd
    body front-compiles to `update`, the rolled `ComL.forLoopN`'s denotation at any
    valuation is the `N`-fold `JLoopBodyN.denote` of `update` over the loop index,
    seeded by `init` and threading the invariants `invs`. Structural
    (`ComL.denote` on `forLoopN`), no open goals — the vsimd twin of
    `rolledForLoopN_denote`. -/
theorem rolledForLoopNV_denote {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJV (accCTy := accCTy) vmBody accName body = some update)
    (V : Ctxt.Valuation Γouter) :
    (rolledForLoopNV (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        N vmBody accName body init invs).map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨N, update⟩ (Expr.lookupArgs invs V) (init.lookup V)) := by
  unfold rolledForLoopNV rolledForLoopNVCont
  rw [hupd]
  rfl

/-! ## 2d. The **carry-select** rolled loop body

`translateDialectControl` has no carry-flag surface: a multi-limb loop body
synthesises each carry bit branch-free through the `bSltu` window
(`(~x & y) | (~(x ^ y) & (x − y)) >> 63`), around 25 dialect ops per limb.
`CarryChainSelect.translateDialectCarrySelect` recognises those windows on the
flattened LowCT spine and emits `bvAddCarryLo`/`bvAddCarryHi` pairs, which
`cryptoDialectToJasminCom` lowers 1:1 to jasmin `addCarryLo`/`addCarryHi` and
the owned backend renders as `adcx`/`adox`. Every command the selector does not
match falls through to `translateDialectControl` unchanged, so the covered
fragment of a carry-selecting loop body is the scalar fragment plus the
recognised carry/borrow windows.

Downstream is shared verbatim with the scalar path: the front output is capped
with `ret accName` (`frontLoopBodyCDC`), lowered by the same
`cryptoDialectToJasminCom` (`frontLoopBodyJC`), and wrapped in the same
`ComL.forLoopN` node (`rolledForLoopNC`). The carry bits the selection
introduces are `.sword 1` bindings *inside* the body, so the loop-carried
accumulator type and the `mapCtx` context reduction are unchanged. -/

/-- Carry-select twin of `frontLoopBodyCD`: front-compile a loop body LowCT over
    the body context `Γbody` through `translateDialectCarrySelect`, returning the
    `Com catCryptDialect` that ends with `ret accName`. Identical to
    `frontLoopBodyCD` except the front is the carry-selecting one, so a body
    whose carry chain is written as `bSltu` windows compiles to
    `bvAddCarryLo`/`bvAddCarryHi` pairs; a body with no recognised window
    front-compiles identically (every unmatched command falls through to
    `translateDialectControl`). -/
def frontLoopBodyCDC {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT) :
    Option (Com catCryptDialect Γbody accCTy) :=
  match translateDialectCarrySelect vmBody body with
  | some r =>
      match r.vm.lookup accName with
      | some ⟨t, v⟩ =>
          if h : t = accCTy then
            r.cont (Com.ret (h ▸ toVIRVar v))
          else none
      | none => none
  | none => none

/-- Carry-select twin of `frontLoopBodyJ`: lower the carry-selecting front loop
    body to the `JLoopBodyN.update`-shaped `Com jasminDialect` over
    `mapCtx Γbody` returning `mapTy accCTy`, via the SAME verified
    `cryptoDialectToJasminCom`. -/
def frontLoopBodyJC {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT) :
    Option (Com jasminDialect (mapCtx Γbody) (mapTy accCTy)) :=
  frontLoopBodyJWith translateDialectCarrySelect (accCTy := accCTy) vmBody accName body

/-- The carry-select instance lowers `frontLoopBodyCDC` through
    `cryptoDialectToJasminCom`. -/
theorem frontLoopBodyJC_eq {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT) :
    frontLoopBodyJC (accCTy := accCTy) vmBody accName body
      = (match frontLoopBodyCDC (accCTy := accCTy) vmBody accName body with
         | some com => DialectToJasminCom.cryptoDialectToJasminCom com
         | none => none) := rfl

/-- Carry-select twin of `rolledForLoopNCont`: build a rolled `ComL.forLoopN`
    whose body is front-compiled through `translateDialectCarrySelect`
    (`frontLoopBodyJC`) rather than `translateDialectControl`. Everything else —
    the `ComL.forLoopN` wrapper, the `mapCtx` context reduction, the
    `init`/`invs` threading, the continuation slot — is identical to the scalar
    `rolledForLoopNCont`.

    * `Γouter` is the outer context (jasmin types);
    * `init` is the in-scope accumulator seed;
    * `invs` are the in-scope loop-invariant seeds (input array bases);
    * the body is `frontLoopBodyJC vmBody accName body` over
      `Γbody = accCTy :: .sword 64 :: invCTys`;
    * `cont : ComL (mapTy accCTy :: Γouter) s` runs after the loop, with the
      loop's final accumulator bound at `.here`.

    `none` if the carry-selecting front declines. -/
def rolledForLoopNCCont {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx} {s : JasminTy}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s) :
    Option (ComL Γouter s) :=
  match frontLoopBodyJC (accCTy := accCTy) vmBody accName body with
  | some update =>
      -- `mapCtx (accCTy :: .sword 64 :: invCTys)` reduces to
      -- `mapTy accCTy :: .reg 64 :: invCTys.map mapTy` definitionally.
      some (ComL.forLoopN ⟨N, update⟩ init invs cont)
  | none => none

/-- Carry-select twin of `rolledForLoopN`: the rolled `ComL.forLoopN` over the
    carry-selecting front body, binding and returning the loop result.
    `rolledForLoopNCCont` at `cont := .ret .here`. -/
def rolledForLoopNC {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy)) :=
  rolledForLoopNCCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
    N vmBody accName body init invs (.ret .here)

/-- **Carry-select loop-wrapper denotation = `JLoopBodyN.denote` fold.** When the
    carry-selecting body front-compiles to `update`, the rolled `ComL.forLoopN`'s
    denotation at any valuation is the `N`-fold `JLoopBodyN.denote` of `update`
    over the loop index, seeded by `init` and threading the invariants `invs`.
    Structural (`ComL.denote` on `forLoopN`), no open goals — the carry-select twin
    of `rolledForLoopN_denote`. -/
theorem rolledForLoopNC_denote {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJC (accCTy := accCTy) vmBody accName body = some update)
    (V : Ctxt.Valuation Γouter) :
    (rolledForLoopNC (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        N vmBody accName body init invs).map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨N, update⟩ (Expr.lookupArgs invs V) (init.lookup V)) := by
  unfold rolledForLoopNC rolledForLoopNCCont
  rw [hupd]
  rfl

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
