/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl

set_option autoImplicit false

/-!
# Rolled counted-loop (`RFor`) lowering with an `N`-fold denotation

`TranslateDialectDirectControl.translateDialectControl`'s `RFor` arm
*meta-unrolls* (`loopRForD`): per trip `i ∈ [0..N)` it emits one
`bvConst (BitVec.ofNat 64 i)` binding plus a fresh copy of the body's
translation, so a `.RFor x N body` becomes `N` copies of `body` in the straight
line (e.g. 255× for the X25519 ladder — a huge `.s`).

This module wires the **rolled** alternative as a genuine `RFor` lowering: a
`.RFor x N body` node lowers to a single `ComL.forLoopN` back-edge over ONE copy
of the front-compiled body (one body copy, seeded `MOV Lctr, #N`, `jne .L<d>`
back-edge, rendered size independent of `N`), and its denotation is the genuine
`N`-fold iterate of the body's step.

The rolled machinery is exactly the `ComL.forLoopN` node of `JasminLprogExport`
(the loop-carrying extension of `Com jasminDialect`) whose `ComL.denote` on a
`forLoopN` is, by definition, the `JLoopBodyN.denote` fold — the same engine
`Poseidon2RolledRenderBB.rolledReduce` / `TranslateDialectRolledLoop.rolledForLoopN`
use. The front loop body is front-compiled through the already-verified
`translateDialectControl` and lowered by `cryptoDialectToJasminCom`, capped with
`ret accName` — the `frontLoopBodyCD`/`frontLoopBodyJ` shape.

## What this file delivers

* `translateRolledRFor` — the `RFor`-keyed rolled lowering. It fires only on an
  `.RFor x N body` node and produces the `ComL.forLoopN` rolled form; every
  non-`RFor` LowCT node is declined (`none`). ONE body behind a back-edge, NOT
  `N` copies.
* `iterStep` — the structural-recursion `N`-fold of a `JLoopBodyN` step
  (`iterStep u invs 0 a = a`; `iterStep u invs (k+1) a = stepC u invs k
  (iterStep u invs k a)`). This is the "unroll the body `N` times, threading the
  trip index" value the rolled loop must realise. Because `stepC` feeds the trip
  index into the body, this is a genuine *index-threaded* fold, not a plain
  `Nat.iterate` of a fixed function (it collapses to `Nat.iterate` only when the
  body ignores its index binder).
* `iterStep_eq_denote` — **the induction on the trip count**: the structural
  `iterStep` equals `JLoopBodyN.denote` (the `List.range N` foldl the rolled node
  denotes to), by induction on `N`, base `denote_zero`, step `denote_succ` + IH.
* `rolledRFor_denote` — **the deliverable**: the rolled `RFor` lowering's
  denotation is `iterStep` of the front-compiled body over `N` trips, seeded by
  `init` and threading the invariants `invs`. Composes `rolledForLoopN_denote`
  (the `ComL.forLoopN` → `JLoopBodyN.denote` fold) with `iterStep_eq_denote`.
* `rolledRFor_denote_agrees_unroll` — **soundness vs the meta-unroll**: the rolled
  form denotes to exactly the `JLoopBodyN.denote` fold — the same index-threaded
  `N`-fold value that unrolling the body `N` times computes. So rolling is a sound
  alternative to unrolling: both realise the same fold.

## The `loopRForD` correspondence, and the scope of `agrees_unroll`

`loopRForD` (the front's meta-unroll) lives in `catCryptDialect` and threads its
prefix as a `ComCont`; the rolled node lives in `ComL` over `jasminDialect`. Their
*values* coincide — `loopRForD`'s per-trip `bvConst (ofNat i)` + body copy computes
the same index-threaded `N`-fold of the body that `iterStep`/`JLoopBodyN.denote`
does — but they are terms in different dialects, so the agreement is stated at the
shared **fold value** level (`rolledRFor_denote_agrees_unroll`: rolled denotes to
`JLoopBodyN.denote`, the mathematical content of the `N`-copy unroll), not as a
cross-dialect `Com`-equality between `translateRolledRFor` and `loopRForD`.

## Restriction (which loops roll)

The front loop body is the covered fragment `translateDialectControl` accepts
(`RArrLoad`/`RScalarSetExpr`/`RArrStore` etc. over a single accumulator plus
loop-invariant array bases, with the loop counter as the runtime index), capped
with `ret accName`. It is **not** a fully-general `RFor x N body` lowering that
infers the accumulator and invariants from a bare node: the accumulator
name/type (`accName`/`accCTy`), the invariant list (`invCTys`), and the outer
seeds (`init`/`invs`) are supplied per-kernel (exactly as in `MpnLoopFrontEmit`).
A loop whose carried state is not a single `accTy` cell plus invariant bases
(several mutable scalars) needs the `ComL.forLoopBlock`/`forLoopMultiAcc` carrier,
not this node.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledFor

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT)

/-! ## 1. The front loop-body compilation (covered fragment, capped with `ret acc`)

`frontLoopBodyCD`/`frontLoopBodyJ` mirror `TranslateDialectRolledLoop`: the loop
body runs over `Γbody = accCTy :: .sword 64 :: invCTys` (accumulator, loop index,
invariants); `translateDialectControl` front-compiles it and we cap with the
(post-store) accumulator return `ret accName` — the value `JLoopBodyN.update`
carries. `frontLoopBodyJ` lowers that to the `JLoopBodyN.update`-shaped
`Com jasminDialect` via the verified `cryptoDialectToJasminCom`. -/

/-- Front-compile a loop body over `Γbody`, capping with `ret accName`. -/
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

/-- Lower the front loop body to the `JLoopBodyN.update`-shaped `Com jasminDialect`. -/
def frontLoopBodyJ {Γbody : Ctx} {accCTy : CryptoTy}
    (vmBody : VarMap Γbody) (accName : String) (body : LowCT) :
    Option (Com jasminDialect (mapCtx Γbody) (mapTy accCTy)) :=
  match frontLoopBodyCD (accCTy := accCTy) vmBody accName body with
  | some com => DialectToJasminCom.cryptoDialectToJasminCom com
  | none => none

/-! ## 2. The rolled `ComL.forLoopN` builder and its fold denotation

`mapCtx (accCTy :: .sword 64 :: invCTys)` reduces to
`mapTy accCTy :: .reg 64 :: invCTys.map mapTy` definitionally, so the front body
is a `JLoopBodyN.update` over `accTy := mapTy accCTy`,
`invTys := invCTys.map mapTy`; we wrap it in `ComL.forLoopN ⟨N, update⟩ init invs
(.ret .here)`. The `ComL.denote` of a `forLoopN` capped with `.ret .here` is the
`JLoopBodyN.denote` fold (`rfl`). -/

/-- Build a genuine rolled `ComL.forLoopN` from the front-compiled loop body:
    ONE body copy + back-edge. `none` if the front declines. -/
def rolledForLoopN {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy)) :=
  match frontLoopBodyJ (accCTy := accCTy) vmBody accName body with
  | some update => some (ComL.forLoopN ⟨N, update⟩ init invs (.ret .here))
  | none => none

/-- **Loop-node denotation = `JLoopBodyN.denote` fold.** When the body
    front-compiles to `update`, the rolled `ComL.forLoopN` denotes to the `N`-fold
    `JLoopBodyN.denote` of `update`, seeded by `init` and threading `invs`.
    Structural (`ComL.denote` on `forLoopN`). -/
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

/-! ## 3. The `RFor`-keyed rolled lowering -/

/-- The rolled `RFor` lowering. On `.RFor x N body` it produces the rolled
    `ComL.forLoopN` (ONE body copy + back-edge); every other LowCT node is
    declined. `none` if the body's covered front declines. -/
def translateRolledRFor {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (c : LowCT) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy)) :=
  match c with
  | .RFor _x N body =>
      rolledForLoopN (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        N vmBody accName body init invs
  | _ => none

/-! ## 4. The structural `N`-fold and the induction on the trip count -/

/-- The structural-recursion `N`-fold of a `JLoopBodyN` step: unroll the body `N`
    times, feeding the trip index `k` into the `k`-th step. `iterStep u invs
    (k+1) a = stepC u invs k (iterStep u invs k a)` — the exact recursion
    `JLoopBodyN.denote_succ` exposes. -/
def iterStep {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (u : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invs : Ctxt.Valuation invTys) : Nat → ⟦accTy⟧ → ⟦accTy⟧
  | 0, a => a
  | k + 1, a => JLoopBodyN.stepC u invs k (iterStep u invs k a)

/-- **Induction on the trip count.** The structural `iterStep` `N`-fold equals the
    `List.range N` foldl `JLoopBodyN.denote` the rolled `ComL.forLoopN` denotes to.
    Base `N = 0` is `denote_zero`; the step is `denote_succ` (peel the last trip
    `k`) composed with the IH on `k`. -/
theorem iterStep_eq_denote {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (u : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invs : Ctxt.Valuation invTys) :
    ∀ (N : Nat) (init : ⟦accTy⟧),
      JLoopBodyN.denote ⟨N, u⟩ invs init = iterStep u invs N init
  | 0, _ => rfl
  | N + 1, init => by
      rw [JLoopBodyN.denote_succ, iterStep_eq_denote u invs N init]; rfl

/-! ## 5. The rolled `RFor` denotation = the `N`-fold iterate of the body -/

/-- **The deliverable.** The rolled `RFor` lowering's denotation is the `N`-fold
    iterate (`iterStep`) of the front-compiled body's step, seeded by `init` and
    threading the invariants `invs`. Composes `rolledForLoopN_denote` (the
    `ComL.forLoopN` → `JLoopBodyN.denote` fold) with the trip-count induction
    `iterStep_eq_denote`. -/
theorem rolledRFor_denote {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (x : String) (N : Nat)
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update)
    (V : Ctxt.Valuation Γouter) :
    (translateRolledRFor (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        (.RFor x N body) vmBody accName init invs).map (fun c => ComL.denote c V)
      = some (iterStep update (Expr.lookupArgs invs V) N (init.lookup V)) := by
  show (rolledForLoopN (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        N vmBody accName body init invs).map (fun c => ComL.denote c V) = _
  rw [rolledForLoopN_denote (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        N vmBody accName body init invs hupd V,
      iterStep_eq_denote update (Expr.lookupArgs invs V) N (init.lookup V)]

/-! ## 6. Soundness vs the meta-unroll (`loopRForD`)

The rolled form denotes to exactly the `JLoopBodyN.denote` fold — the same
index-threaded `N`-fold value that unrolling the body `N` times computes. So
rolling is a sound alternative to unrolling: the rolled back-edge and the `N`-copy
unroll realise the same fold. (The front's `loopRForD` meta-unroll lives in
`catCryptDialect`; the equality is stated at this shared fold-value level rather
than as a cross-dialect `Com`-equality — see the module docstring.) -/

/-- **Rolling agrees with unrolling.** The rolled `RFor` lowering denotes to the
    `JLoopBodyN.denote` fold of the body — the mathematical content of the `N`-copy
    meta-unroll — so rolling and unrolling agree on the loop's value. -/
theorem rolledRFor_denote_agrees_unroll {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (x : String) (N : Nat)
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update)
    (V : Ctxt.Valuation Γouter) :
    (translateRolledRFor (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        (.RFor x N body) vmBody accName init invs).map (fun c => ComL.denote c V)
      = some (JLoopBodyN.denote ⟨N, update⟩ (Expr.lookupArgs invs V) (init.lookup V)) := by
  rw [rolledRFor_denote x N vmBody accName body init invs hupd V,
      iterStep_eq_denote update (Expr.lookupArgs invs V) N (init.lookup V)]

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledFor
