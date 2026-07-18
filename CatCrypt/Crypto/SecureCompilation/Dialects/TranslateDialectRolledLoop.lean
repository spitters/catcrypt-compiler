/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd

set_option autoImplicit false

/-!
# Front-compiling a LowCT loop body to a genuine `ComL.forLoopN` (rolled emit)

The straight-line front (`TranslateDialectDirectControl.translateDialectControl`
→ `DialectToJasminCom.cryptoDialectToJasminCom`) lowers a `LowCT` to a
**straight-line** `Com jasminDialect`. Its `RFor` arm is a *static unroll*
(`loopRForD` emits one body copy per trip), which overflows at deployed sizes and
produces `N` copies of the body in the `.s`.

This module adds the **rolled** front path: it front-compiles a single LowCT loop
*body* (the covered fragment — `RArrLoad`/`RScalarSetExpr`/`RArrStore` over memref
arrays, with the loop counter as the array index) into the
`JLoopBodyN.update`-shaped straight-line `Com jasminDialect`, then wraps it in a
genuine `ComL.forLoopN` node (ONE body copy + a real back-edge). The
loop-counter variable feeds `RArrLoad`/`RArrStore` as a per-trip dynamic index
(`memrefGetDyn`/`memrefSetDyn` → `stackLoad`/`stackStore` SIB `LOADIDX`/`STOREIDX`
at the runtime trip counter), exactly the `N = 4` PoC pattern of
`MAYO/KernelFromRustcmdFrontEmit.lean` — only now the index is the *loop binder*,
not a materialised constant, and the trip is a real counted loop.

```
  bodyLowCT  (RArrLoad acc/in[idx] … RArrStore out[idx] … over the loop counter `idx`)
    --(translateDialectControl on Γbody = [acc, idx, *invs])-->  Com catCryptDialect
    --(cryptoDialectToJasminCom)----------------------------->  Com jasminDialect = JLoopBodyN.update
    --(ComL.forLoopN ⟨N, update⟩ init invs (ret acc))-------->  ComL  (ONE body copy + back-edge)
    --(ComL.toLprogPhysAbi / renderLprogAtt)---------------->  .s     (genuine `jne .L<d>`)
```

## Design: an export-level wrapper, not a new LowCT constructor

The genuine-loop structure is an **export-level** `ComL.forLoopN` wrapper (the
loop nodes live in `ComL`, an extension of `Com jasminDialect`, not in `LowCT` or
`catCryptDialect`). Every existing rolled emit (QRUOV/SDitH/MAYO `*RolledEmit`)
is built by hand-authoring exactly such a `ComL.forLoopN` over a hand-built body
`Com`. This module replaces the *hand-built body* with the **verified front**:
the loop body is plain covered LowCT, front-compiled by the existing
`translateDialectControl`, so:

* no new `LowCT` constructor (the unrolling `RFor` is untouched);
* no new `catCryptDialect` op;
* the loop body reuses the already-proven `IsCovered`/simulation/leak-factoring
  fragment verbatim — the loop is a pure structural wrapper over it.

The keystone delivered is: a covered LowCT loop body now front-compiles to the
`JLoopBodyN.update` Com that the committed `ComL.forLoopN` export consumes, so the
5 deployed GF-MQ kernels (MAYO/SNOVA/UOV/QRUOV/SDitH) can be front-compiled at
deployed sizes (rolled, bounded depth) instead of hand-built.
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
  match frontLoopBodyCD (accCTy := accCTy) vmBody accName body with
  | some com => DialectToJasminCom.cryptoDialectToJasminCom com
  | none => none

/-! ## 2. Wrapping the front body into a genuine `ComL.forLoopN`

`ComL.forLoopN` needs the body as a `Com jasminDialect (accTy :: .reg 64 :: invTys)
accTy`. When the body context is `Γbody = accCTy :: .sword 64 :: invCTys`,
`mapCtx Γbody = mapTy accCTy :: .reg 64 :: invCTys.map mapTy` reduces by `rfl`
(`mapCtx = List.map mapTy`, `mapTy (.sword 64) = .reg 64`), so the front body is
*definitionally* a `JLoopBodyN.update` over `accTy := mapTy accCTy`,
`invTys := invCTys.map mapTy`. We wrap it in `ComL.forLoopN ⟨N, update⟩ init invs
(.ret .here)`, with `init`/`invs` the in-scope seeds in the *outer* context. -/

/-- Build a genuine rolled `ComL.forLoopN` from a front-compiled loop body.

    * `Γouter` is the outer context (the kernel's argument slots, jasmin types);
    * `init` is the in-scope accumulator seed variable;
    * `invs` are the in-scope loop-invariant seed variables (input array bases);
    * the loop body is `frontLoopBodyJ vmBody accName body` over
      `Γbody = accCTy :: .sword 64 :: invCTys` (so its jasmin image matches
      `accTy :: .reg 64 :: invTys`).

    Returns a `ComL Γouter accTy` that binds the loop result and returns it
    (`.ret .here`). `none` if the front declines. -/
def rolledForLoopN {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy)) :=
  match frontLoopBodyJ (accCTy := accCTy) vmBody accName body with
  | some update =>
      -- `mapCtx (accCTy :: .sword 64 :: invCTys)` reduces to
      -- `mapTy accCTy :: .reg 64 :: invCTys.map mapTy` definitionally.
      some (ComL.forLoopN ⟨N, update⟩ init invs (.ret .here))
  | none => none

/-! ## 2b. Loop-wrapper simulation skeleton

The genuine-loop structure is a pure `ComL.forLoopN` wrapper over the
front-compiled body `update`. Its denotation is, by `ComL.denote`'s definition,
exactly the `JLoopBodyN.denote` fold of `update` over the trip count `N` — the
mathematical ground truth the rolled back-edge realises (`forLoopLcmd`/
`JLoopBodyN.denote_succ` prove the emitted `jne`-loop matches this fold
step-for-step). This ties the loop wrapper to the (separately covered) body
fragment with no `sorry`: the body's own correctness is the `IsCovered` /
`rustExecSimulatesDialect` story for `translateDialectControl`, reused verbatim;
the wrapper contributes only the fold. -/

/-- **Loop-wrapper denotation = `JLoopBodyN.denote` fold.** When the body
    front-compiles to `update`, the rolled `ComL.forLoopN`'s denotation at any
    valuation is the `N`-fold `JLoopBodyN.denote` of `update` over the loop index,
    seeded by `init` and threading the invariants `invs`. Structural (`ComL.denote`
    on `forLoopN`), no `sorry`. -/
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
  unfold rolledForLoopN
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
scalar arms behave identically, plus the SIMD arms are now caught.

Everything downstream is shared verbatim with the scalar path: the front output
is capped with `ret accName` (`frontLoopBodyCDV`), lowered by the SAME verified
`cryptoDialectToJasminCom` (`frontLoopBodyJV`), and wrapped in the SAME
`ComL.forLoopN` node. When `accCTy = .sword 128`, `mapTy accCTy = .reg 128`, so
the accumulator carried across the back-edge is a 128-bit register — a genuine
vsimd rolled loop with ONE body copy and a real `jne` back-edge. -/

/-- Vsimd twin of `frontLoopBodyCD`: front-compile a loop body LowCT over the body
    context `Γbody` through the **vsimd-aware** `translateDialectControlV`,
    returning the `Com catCryptDialect` that ends with `ret accName`. Identical to
    `frontLoopBodyCD` except the front is `translateDialectControlV`, so a body
    that is (or contains) a `.sword 128` `vsimd`-tagged op at the loop index is
    now covered; a purely scalar body front-compiles identically (the vsimd front
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
  match frontLoopBodyCDV (accCTy := accCTy) vmBody accName body with
  | some com => DialectToJasminCom.cryptoDialectToJasminCom com
  | none => none

/-- **CAPABILITY G2** — vsimd twin of `rolledForLoopN`: build a genuine rolled
    `ComL.forLoopN` whose body is front-compiled through the vsimd-aware
    `translateDialectControlV` (`frontLoopBodyJV`) rather than the scalar
    `translateDialectControl`. Everything else — the `ComL.forLoopN` wrapper, the
    `mapCtx` context reduction, the `init`/`invs` threading — is identical to the
    scalar `rolledForLoopN`. When `accCTy = .sword 128` the loop carries a
    `.reg 128` accumulator across a real back-edge with ONE vsimd body copy.

    * `Γouter` is the outer context (jasmin types);
    * `init` is the in-scope accumulator seed (`.sword 128` for a vsimd loop);
    * `invs` are the in-scope loop-invariant seeds (input array bases);
    * the body is `frontLoopBodyJV vmBody accName body` over
      `Γbody = accCTy :: .sword 64 :: invCTys`.

    Returns a `ComL Γouter (mapTy accCTy)` binding and returning the loop result
    (`.ret .here`). `none` if the vsimd front declines. -/
def rolledForLoopNV {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy)) :=
  match frontLoopBodyJV (accCTy := accCTy) vmBody accName body with
  | some update =>
      -- `mapCtx (accCTy :: .sword 64 :: invCTys)` reduces to
      -- `mapTy accCTy :: .reg 64 :: invCTys.map mapTy` definitionally.
      some (ComL.forLoopN ⟨N, update⟩ init invs (.ret .here))
  | none => none

/-- **Vsimd loop-wrapper denotation = `JLoopBodyN.denote` fold.** When the vsimd
    body front-compiles to `update`, the rolled `ComL.forLoopN`'s denotation at any
    valuation is the `N`-fold `JLoopBodyN.denote` of `update` over the loop index,
    seeded by `init` and threading the invariants `invs`. Structural
    (`ComL.denote` on `forLoopN`), no `sorry` — the vsimd twin of
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
  unfold rolledForLoopNV
  rw [hupd]
  rfl

/-- The owned rolled vsimd `Lprog` for a front-compiled loop body, via the
    committed memref ABI looped export — vsimd twin of `rolledForLoopNLprog`. -/
def rolledForLoopNVLprog {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (fname outArg : String) (inArgs : List String)
    (abiArgs : List String) (abiTyin : List Nat) : Option Lprog :=
  (rolledForLoopNV (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
      N vmBody accName body init invs).map
    (fun c =>
      ComL.toLprogPhysAbi c fname outArg inArgs
        (fun _ => none) (fun _ => none) abiArgs abiTyin)

/-! ## 3. Top-level: rolled loop body → owned `Lprog` via the committed export

`rolledForLoopNLprog` composes `rolledForLoopN` with the committed multi-pointer
memref ABI export `ComL.toLprogPhysAbi`. The result is a genuine rolled
`Lprog` — ONE body copy, a real `jne .L<d>` back-edge — with NO hand-built body
`Com`. -/

/-- The owned rolled `Lprog` for a front-compiled loop body, via the committed
    memref ABI looped export. -/
def rolledForLoopNLprog {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (fname outArg : String) (inArgs : List String)
    (abiArgs : List String) (abiTyin : List Nat) : Option Lprog :=
  (rolledForLoopN (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
      N vmBody accName body init invs).map
    (fun c =>
      ComL.toLprogPhysAbi c fname outArg inArgs
        (fun _ => none) (fun _ => none) abiArgs abiTyin)

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
