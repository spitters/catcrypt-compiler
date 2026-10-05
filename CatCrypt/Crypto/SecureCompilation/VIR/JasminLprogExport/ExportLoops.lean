/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.List.Sort.Basic
import all Init.Data.String.Slice
import all Init.Data.String.Search
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Core
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import Std.Data.HashMap
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Export
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Export
public meta import CatCrypt.Crypto.SecureCompilation.VIR.X86IsaData
public import CatCrypt.Crypto.SecureCompilation.VIR.X86IsaData

/-!
# Loop export of `ComL` to `Linear.lprog`

Fixed-trip, multi-binder, runtime-trip, nested and block-body loops at the `Com`
level (`ComL`), their denotations, and their lowering to linear bodies with a
back-edge, including leaf calls (`Lcall`) inside a loop body. Every loop lowering takes
the instruction-set data `I : IsaData`, with default the x86 data `x86Data`, and emits its
back edge as `I.loopGuard` and the skip of a zero runtime count as `I.zeroTripGuard`; at
`x86Data` these are `CMP ctr, 0; jne top` and `CMP ctr, 0; je endL`. The instruction that
touches an invariant register `r` is `I.invTouch ctr r`; at `x86Data` it is `CMP ctr, r`.

## Main definitions

* `JLoopBody`, `JLoopBodyN`: loop bodies and their denotations.
* `ComL`: `Com` extended with loop nodes.
* `forLoopLcmd`, `forLoopLcmdN`, `forLoopLcmdNCall`: loop lowering.
* `comLToBody`: the linear body of a `ComL` term.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaData)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data)

/-! ## 3b. Fixed-trip loops at the `Com` level (`ComL` / `comLToBody`)

`comToBody` (§3) walks a *straight-line* A-normal `Com jasminDialect`: only
`.var` (let) and `.ret`. A front `Com` carrying a **fixed-trip counted loop** in
the middle of its chain (`mayo_encode`'s `RWhileNz`, the `*_sign_rwhile` kernels)
has no node to express that loop, so it either falls back to jasminc or is
unrolled to `n` copies. This section closes that gap **additively**: the pure
`.var`/`.ret` path is untouched (`comToBody` is byte-identical), and the loop is
a new node in a sibling walk.

A fixed-trip loop cannot be a `JasminOp` constructor: `jasminDialect.Op` is
`JasminOp`, and a loop body is a `Com jasminDialect [accTy] accTy`, so embedding
it in `JasminOp` is a definitional cycle (`jasminDialect` is defined *from*
`JasminOp`). We instead carry the loop body as a separate `JLoopBody` structure
and extend the `Com` walk with a `forLoop` node in a new `ComL` inductive.

The lowering reuses the verified back-edge shape `LprogControlFlow.loopLcmd`
proves (`Llabel ; body ; SUB ; CMP ; Lcond NZ → top` = `runBoundedLoop`), but
spelled inline here (this module is upstream of `LprogControlFlow`, so it cannot
import `loopLcmd`). The emitted loop is **one** body copy (not `n`), with a real

`Lcond`/`Llabel` back-edge — the renderer emits `.L<d>: … ; jne .L<d>`. The
body's SSA temporaries live in a disjoint per-loop register namespace
(`L<d>_r<k>`), so they never collide with the enclosing straight-line chain
(`r<curDepth>`); the trip counter is `Lctr<d>`. The counter / back-edge are
public (a configuration count), so the loop is CT-admissible. -/

/-- A fixed-trip counted loop body over a single accumulator type. `update` maps
    an `[accTy]`-context to an `accTy`: one iteration's accumulator transform.
    The `Com jasminDialect`-level analogue of `JasminPrint.JForProg` (kept here,
    not imported, so `comToBody`'s module owns it). -/
structure JLoopBody (accTy : JasminTy) where
  /-- Static iteration count (the public trip count). -/
  n : Nat
  /-- The accumulator-update body: `acc ↦ update(acc)`. -/
  update : Com jasminDialect [accTy] accTy

/-- One iteration: run `update` on a singleton valuation `[acc]`. Indexed by the
    body `Com`, not the whole `JLoopBody`, so it is `n`-independent (lets the
    `denote_succ` unfolding close by `rfl`/`simp`). -/
def JLoopBody.stepC {accTy : JasminTy} (u : Com jasminDialect [accTy] accTy)
    (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  u.denote (.cons acc .nil)

/-- Total `n`-fold denotation: iterate `stepC` `n` times from the initial
    accumulator. No fuel — `n` is the static trip count. This is the
    mathematical ground truth the lowered back-edge realises. -/
def JLoopBody.denote {accTy : JasminTy} (p : JLoopBody accTy) (init : ⟦accTy⟧) :
    ⟦accTy⟧ :=
  (List.range p.n).foldl (fun acc _ => JLoopBody.stepC p.update acc) init

/-! ### 3b′. Multi-binder loop body (`JLoopBodyN`) — indexed array load/store

`JLoopBody` (above) carries a body `Com jasminDialect [accTy] accTy` over a
**single** accumulator binder, so one iteration can only transform a scalar
accumulator — it cannot do a per-iteration *indexed* array load/store
(`out[i] := f(in[i])`), the shape `mayo_encode`/`*_sign_rwhile` need to roll.

`JLoopBodyN` is the additive multi-binder generalisation: its body runs over the
context `accTy :: .reg 64 :: invTys`, i.e. **three** roles of binder:

* the **accumulator** `accTy` (`.here`, newest) — loop-carried, the body returns
  the updated value each trip (e.g. the output array, threaded through
  `stackStore`);
* the **loop index** `.reg 64` (`.there .here`) — the trip number `i`, which the
  body reads as the *runtime* index of a `stackLoad`/`stackStore` (so the op
  lowers to a SIB `LOADIDX`/`STOREIDX` `base[idx*scale]`), advanced `0,1,…,n-1`;
* the **loop-invariant binders** `invTys` (the input array base pointers and any
  constants) — read every trip, fixed across the loop.

So a body `out[i] := in[i] + 1` is a `Com jasminDialect
[stackArr w n, reg 64, stackArr w n] (stackArr w n)`: `stackLoad in[idx]`,
`+1`, `stackStore acc[idx]`, return the new array. The `JLoopBody` accumulator
loop is the `invTys = []`, index-unused special case. -/

/-- A fixed-trip counted loop body with **multiple binders**: an accumulator
    `accTy`, a `reg 64` loop index, and a list of loop-invariant binders
    `invTys`. `update` maps the `accTy :: .reg 64 :: invTys` context to `accTy`:
    one iteration's accumulator transform, with the trip index and the invariants
    in scope (so the body can index an array at the runtime loop counter). -/
structure JLoopBodyN (accTy : JasminTy) (invTys : Ctxt jasminDialect) where
  /-- Static iteration count (the public trip count). -/
  n : Nat
  /-- The accumulator-update body over `[accTy, reg 64, *invTys]`. -/
  update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy

/-- One iteration at trip index `t`: run `update` on the valuation
    `[acc, ofNat t, *invs]` (the accumulator, the trip number as the `reg 64`
    index, then the invariants). Indexed by the body `Com`, not the whole
    `JLoopBodyN`, so it is `n`-independent. -/
def JLoopBodyN.stepC {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (u : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invs : Ctxt.Valuation invTys) (t : Nat) (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  u.denote (.cons acc (.cons (BitVec.ofNat 64 t) invs))

/-- Total `n`-fold denotation: iterate `stepC` over the trip indices `0,…,n-1`
    from the initial accumulator, threading the fixed invariants `invs`. No
    fuel — `n` is the static trip count. The mathematical ground truth the
    lowered indexed-load/store back-edge realises. -/
def JLoopBodyN.denote {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (p : JLoopBodyN accTy invTys) (invs : Ctxt.Valuation invTys)
    (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range p.n).foldl (fun acc t => JLoopBodyN.stepC p.update invs t acc) init

/-- The per-outer-recomputed **inner trip count** of a nested runtime loop at
    outer index `jd`: run the inner-count body `innerCount` on `[ofNat jd, *invs]`
    (the outer index, then the invariants) and read the result as a `Nat`. This is
    the GGM `num >> (jd+1)` shape — the inner bound is *recomputed* from the outer
    index each outer pass, not a baked-in schedule. -/
def JLoopBodyN.innerTripAtC {invTys : Ctxt jasminDialect}
    (innerCount : Com jasminDialect (.reg 64 :: invTys) (JasminTy.reg 64))
    (invs : Ctxt.Valuation invTys) (jd : Nat) : Nat :=
  (innerCount.denote (.cons (BitVec.ofNat 64 jd) invs)).toNat

/-- One **inner** iteration of a nested runtime loop at outer index `jd`, inner
    index `t`: run `innerUpdate` on `[acc, ofNat t, ofNat jd, *invs]` (accumulator,
    inner index, outer index, invariants). The `stepC` analogue with the extra
    outer-index binder in scope. -/
def JLoopBodyN.stepCNested {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (innerUpdate : Com jasminDialect (accTy :: .reg 64 :: .reg 64 :: invTys) accTy)
    (invs : Ctxt.Valuation invTys) (jd t : Nat) (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  innerUpdate.denote
    (.cons acc (.cons (BitVec.ofNat 64 t) (.cons (BitVec.ofNat 64 jd) invs)))

/-- The **nested runtime fold**: an outer loop `jd ∈ 0..outerN` whose per-iteration
    work is an inner loop `t ∈ 0..innerTripAtC(jd)` (the inner trip recomputed per
    outer pass via `innerCount`), applying `innerUpdate` at each innermost step.
    This is the `JLoopBodyN` analogue of
    `JasminLsemMemLoopNestDepth.runNestedVarLoopMem` (the proven varying-bound
    nested-loop semantics): with `innerCount` computing `num >> (jd+1)` it is the
    GGM Phase-3 `ggmNestedFold` (per-outer-halved middle trip). The mathematical
    ground truth the emitted nested back-edges realise. -/
def JLoopBodyN.nestedDenote {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (innerCount : Com jasminDialect (.reg 64 :: invTys) (JasminTy.reg 64))
    (innerUpdate : Com jasminDialect (accTy :: .reg 64 :: .reg 64 :: invTys) accTy)
    (outerN : Nat) (invs : Ctxt.Valuation invTys) (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range outerN).foldl
    (fun acc jd =>
      (List.range (JLoopBodyN.innerTripAtC innerCount invs jd)).foldl
        (fun acc2 t => JLoopBodyN.stepCNested innerUpdate invs jd t acc2) acc)
    init

/-- `Com jasminDialect` extended with **fixed-trip loop nodes**. The `.ret`/`.var`
    constructors mirror `Com` exactly; `.forLoop`/`.forLoopN` bind the loop result
    (the final accumulator) into scope for the continuation, so a loop sits inline
    in the straight-line chain. -/
inductive ComL : Ctxt jasminDialect → JasminTy → Type _ where
  /-- Return a variable (same as `Com.ret`). -/
  | ret {Γ t} (v : Ctxt.Var Γ t) : ComL Γ t
  /-- Let-bind a straight-line expression (same as `Com.var`). -/
  | var {Γ t s} (e : Expr jasminDialect Γ t) (body : ComL (t :: Γ) s) : ComL Γ s
  /-- A fixed-trip loop `acc := loop.denote(init)`, with the final accumulator
      bound into scope for `body`. `init` is the in-scope seed variable. -/
  | forLoop {Γ accTy s} (loop : JLoopBody accTy) (init : Ctxt.Var Γ accTy)
      (body : ComL (accTy :: Γ) s) : ComL Γ s
  /-- A fixed-trip **multi-binder** loop `acc := loop.denote(invs, init)` whose
      body indexes arrays at the runtime trip counter. `init` is the in-scope
      accumulator seed; `invs` are the in-scope invariant seeds (input array
      bases, constants). The final accumulator is bound into scope for `body`. -/
  | forLoopN {Γ accTy s} {invTys : Ctxt jasminDialect}
      (loop : JLoopBodyN accTy invTys) (init : Ctxt.Var Γ accTy)
      (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
      (body : ComL (accTy :: Γ) s) : ComL Γ s
  /-- A **runtime-trip** multi-binder loop: identical to `forLoopN` except the
      trip count is *not* a static `Nat` but an in-scope `.reg 64` variable
      `count` read at run time. The body `update` runs over
      `accTy :: .reg 64 :: invTys` (accumulator, loop index, invariants) exactly
      as `JLoopBodyN.update`, but folded `(count.lookup V).toNat` times. This is
      the node a `poly1305_mac_hacl(out, inp, nblk)`-shaped kernel needs: `nblk`
      is a runtime argument, so the back-edge is seeded `MOV Lctr, <countReg>`
      (a register), not `MOV Lctr, #n` (an immediate). -/
  | forLoopNRt {Γ accTy s} {invTys : Ctxt jasminDialect}
      (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
      (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ accTy)
      (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
      (body : ComL (accTy :: Γ) s) : ComL Γ s
  /-- A **nested runtime-trip** loop: a runtime outer loop whose per-iteration body
      is *itself* a runtime loop, with the inner trip **recomputed per outer pass**.
      This is the type wall `forLoopNRt` hits — its `update` is a straight-line
      `Com` (a loop is not a `JasminOp`), so it cannot carry an inner loop; this
      constructor makes the inner loop first-class.

      * `innerCount : Com jasminDialect (.reg 64 :: invTys) (.reg 64)` computes the
        inner trip count from the outer index (`.reg 64`, `.here`) and the
        invariants — the GGM `num >> (jd+1)` per-outer-recomputed bound;
      * `innerUpdate : Com jasminDialect (accTy :: .reg 64 :: .reg 64 :: invTys) accTy`
        is one innermost-iteration body over accumulator, inner index, outer index,
        invariants;
      * `outerCount` is the in-scope runtime outer trip count;
      * `init`/`invs` are the accumulator seed and invariant bases;
      * `body` is the continuation, with the final accumulator bound.

      Denotes to `JLoopBodyN.nestedDenote` (the double fold matching
      `JasminLsemMemLoopNestDepth.runNestedVarLoopMem`); lowers to nested
      back-edges (an inner `forLoopLcmdNRt` inside the outer body, with a per-outer
      inner-count recompute) — the shape of `JasminLsemMemLoopNestDepth.ggmProg`. -/
  | forLoopNRtNested {Γ accTy s} {invTys : Ctxt jasminDialect}
      (innerCount : Com jasminDialect (.reg 64 :: invTys) (JasminTy.reg 64))
      (innerUpdate : Com jasminDialect (accTy :: .reg 64 :: .reg 64 :: invTys) accTy)
      (outerCount : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ accTy)
      (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
      (body : ComL (accTy :: Γ) s) : ComL Γ s
  /-- A **data-dependent do-while** — the `RWhileNz` countdown idiom
      (`while (n != 0) { …body…; n -= 1 }`), the A3 `whileLinstrRM` shape. The
      loop body runs FIRST and the guard counter is bottom-tested (`Lcond NZ` on
      the counter register), so the lowering is a do-while back-edge with
      **no zero-trip top guard** — unlike `forLoopNRt`'s top-guarded skip. `guard`
      is the in-scope runtime countdown seed: the emitted loop re-reads the
      counter each pass and exits when it reaches `0`, so the trip count is fixed
      only at run time (A3's `whileTripsMem`, read off the run); for this
      committed countdown form the data-dependent trip provably equals the seed
      value, and `denote` folds exactly that many trips — the fold at the trip
      count the guard exit realises (a total denotation; no fuel parameter).
      Entered with `guard = 0` the machine do-while underflows the counter (the
      body runs at least once); the source tie
      (`JasminLsemMemSourceTieWhile.whileMem_export_faithful_comL`) carries the
      run-halting + trip-identification hypotheses that exclude that case.
      `update` has the `JLoopBodyN.update` shape (accumulator, up-counting index,
      invariants) — the front-compiled per-iteration body `frontLoopBodyJ`
      produces (`TranslateDialectWhileNode.rolledWhileNzComL`). -/
  | whileNz {Γ accTy s} {invTys : Ctxt jasminDialect}
      (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
      (guard : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ accTy)
      (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
      (body : ComL (accTy :: Γ) s) : ComL Γ s
  /-- A **block-body** runtime-trip loop: identical seed/count/invariant plumbing
      to `forLoopNRt`, but the per-iteration body is a *recursive* `ComL` over
      `accTy :: .reg 64 :: invTys` (accumulator, loop index, invariants) rather
      than a straight-line `Com`. So one iteration can be a **multi-phase** body
      (a sequence of lets and stores), can contain **nested loop nodes** to
      arbitrary depth, and ends in a `.ret acc` returning the updated
      accumulator. This is the node MAYO/SolveGf16 need: their inner `RWhileNz`
      body is itself a loop over a sub-phase (G1 multi-phase body, G2 3-deep
      nesting), which `forLoopNRt`'s `Com`-shaped `update` cannot carry (a loop is
      not a `JasminOp`).

      * `loopBody : ComL (accTy :: .reg 64 :: invTys) accTy` is one iteration —
        the accumulator, the trip index (`.reg 64`), and the invariants are in
        scope, exactly the `JLoopBodyN.update` context, but now a full `ComL`;
      * `count`/`init`/`invs` are the in-scope runtime trip count, accumulator
        seed and invariant bases, as in `forLoopNRt`;
      * `body` is the continuation, with the final accumulator bound.

      Denotes to the `count`-fold of `loopBody`'s `ComL.denote` (the multi-binder
      analogue of `forLoopNRt`'s `stepC` fold, but with a recursive body);
      lowers to the runtime back-edge frame (`forLoopBlockLcmd`) whose one body
      copy is the recursively-lowered `loopBody` (`comLLoopBodyWalk`, which may
      carry inner back-edges). Subsumes `forLoopNRtNested` (a 2-deep special
      case) and, on a straight-line `loopBody`, lowers byte-identically to
      `forLoopNRt`. -/
  | forLoopBlock {Γ accTy s} {invTys : Ctxt jasminDialect}
      (loopBody : ComL (accTy :: .reg 64 :: invTys) accTy)
      (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ accTy)
      (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
      (body : ComL (accTy :: Γ) s) : ComL Γ s

/-- Denotation of a `ComL`: straight-line `var`/`ret` plus loop nodes folded `n`
    times via `JLoopBody.denote` / `JLoopBodyN.denote`. The mathematical ground
    truth the lowered body (with its real back-edge) realises. -/
def ComL.denote : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    ComL Γ t → Ctxt.Valuation Γ → ⟦t⟧
  | _, _, .ret v, V => v.lookup V
  | _, _, .var e body, V => body.denote (V.extend (e.denote V))
  | _, _, .forLoop loop init body, V =>
      body.denote (V.extend (loop.denote (init.lookup V)))
  | _, _, .forLoopN loop init invs body, V =>
      body.denote (V.extend (loop.denote (Expr.lookupArgs invs V) (init.lookup V)))
  | _, _, .forLoopNRt update count init invs body, V =>
      body.denote (V.extend
        ((List.range (count.lookup V).toNat).foldl
          (fun acc t => JLoopBodyN.stepC update (Expr.lookupArgs invs V) t acc)
          (init.lookup V)))
  | _, _, .forLoopNRtNested innerCount innerUpdate outerCount init invs body, V =>
      body.denote (V.extend
        (JLoopBodyN.nestedDenote innerCount innerUpdate (outerCount.lookup V).toNat
          (Expr.lookupArgs invs V) (init.lookup V)))
  | _, _, .whileNz update guard init invs body, V =>
      -- The countdown do-while: the guard exit fires exactly when the counter —
      -- seeded `guard`, decremented once per pass — reaches `0`, so the realised
      -- trip count is the seed value and the denotation is that fold.
      body.denote (V.extend
        ((List.range (guard.lookup V).toNat).foldl
          (fun acc t => JLoopBodyN.stepC update (Expr.lookupArgs invs V) t acc)
          (init.lookup V)))
  | _, _, .forLoopBlock loopBody count init invs body, V =>
      -- Block-body runtime loop: fold the RECURSIVE `loopBody`'s own `ComL.denote`
      -- `count` times, threading the accumulator and passing the trip index as the
      -- `.reg 64` binder and the invariants after it — the multi-binder analogue of
      -- `forLoopNRt`'s `stepC` fold with `loopBody.denote` in place of `Com.denote`.
      body.denote (V.extend
        ((List.range (count.lookup V).toNat).foldl
          (fun acc t =>
            loopBody.denote
              (.cons acc (.cons (BitVec.ofNat 64 t) (Expr.lookupArgs invs V))))
          (init.lookup V)))

/-- **Multi-accumulator counted loop** (task #20): a runtime-trip loop carrying
    `N` loop-carried `w`-bit cells — an imperative kernel's several mutable
    scalars (MAYO/SolveGf16's `i, j, acc, prow, pivot, …`) threaded together
    across the back-edge, which the single-`accTy` loop nodes cannot hold.

    The carrier is the **product type the dialect already has**: `stackArr w N`, a
    an `N`-cell product (`⟦stackArr w N⟧ = Fin N → BitVec w`). Each cell is a
    frame slot; the loop body reads any cell (`stackLoad`), updates it, and
    `stackStore`s it back — the functional `stackStore` returns the whole updated
    array, so all `N` cells are loop-carried through the one `forLoopBlock`
    back-edge. So this is `forLoopBlock` at `accTy = stackArr w N`: no new
    constructor, no `JasminTy.prod`, the recursive block body + the array product
    already express the multi-accumulator state.

    * `loopBody : ComL (stackArr w N :: .reg 64 :: invTys) (stackArr w N)` is one
      iteration over the `N`-cell array, the trip index, and the invariants,
      returning the updated array;
    * `count`/`init`/`invs` are the runtime trip count, the `N`-cell seed array,
      and the invariant bases;
    * `body` is the continuation, with the final `N`-cell array bound.

    Denotes to the `count`-fold of `loopBody`'s `ComL.denote` over the packed
    `Fin N → BitVec w` state (definitionally the `forLoopBlock` fold); lowers to
    the block-body back-edge frame threading the array base + per-cell
    `LOADIDX`/`STOREIDX`, and exports (`ComL.toLfundefPhys`) to real GP registers.
    `forLoopMultiAcc_denote` records the definitional characterization. -/
def ComL.forLoopMultiAcc {Γ : Ctxt jasminDialect} {w N : Nat} {s : JasminTy}
    {invTys : Ctxt jasminDialect}
    (loopBody : ComL (JasminTy.stackArr w N :: JasminTy.reg 64 :: invTys)
      (JasminTy.stackArr w N))
    (count : Ctxt.Var Γ (JasminTy.reg 64))
    (init : Ctxt.Var Γ (JasminTy.stackArr w N))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (body : ComL (JasminTy.stackArr w N :: Γ) s) : ComL Γ s :=
  .forLoopBlock loopBody count init invs body

/-- A loop body's SSA-temporary register name: a disjoint per-loop namespace
    keyed by the enclosing loop's depth `d`, so body temporaries (`L<d>_r<k>`)
    never collide with the straight-line chain's `r<curDepth>` slots. -/
def loopReg (d k : Nat) : String := "L" ++ toString d ++ "_r" ++ toString k

/-- A loop's trip-counter register name (`Lctr<d>`): the register `MOV Lctr,#n`
    initialises and `SUB Lctr,#1`/`CMP Lctr,#0`/`jne` drive the back-edge. -/
def loopCtr (d : Nat) : String := "Lctr" ++ toString d

/-- Resolve a loop-body `Var`: slot `0` (the accumulator arg) is the accumulator
    register `accReg`; any deeper slot is the body temporary `loopReg d slot`. -/
def loopResolveVar (d : Nat) (accReg : String) (curDepth : Nat)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (v : Ctxt.Var Γ τ) : LOperand :=
  let slot := curDepth - 1 - varIndex v
  if slot == 0 then
    match immSlotMap slot with | some w => .imm w | none => .reg accReg
  else .reg (loopReg d slot)

/-- Collect a loop-body `Expr`'s operands (the `loopResolveVar` analogue of
    `exprArgs`). -/
def loopExprArgs (d : Nat) (accReg : String) (curDepth : Nat)
    (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (e : Expr jasminDialect Γ τ) : List LOperand :=
  let rec go {tys : List JasminTy}
      (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) : List LOperand :=
    match tys, hv with
    | [], _ => []
    | _ :: _, .cons v rest =>
        loopResolveVar d accReg curDepth immSlotMap v :: go rest
  go e.args

/-- Walk one loop-body `Com [accTy] accTy` into a single-iteration `Lcmd` (binders
    in the disjoint `loopReg d` namespace) plus its result register name. The
    `comToBody` analogue scoped to a loop body. -/
def loopBodyWalk (d : Nat) (accReg : String) (immSlotMap : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → (Lcmd × String)
  | _, _, .ret v, curDepth =>
      ([], match loopResolveVar d accReg curDepth immSlotMap v with
            | .reg n => n
            | .imm m => toString m
            | .arr b i => b ++ "[" ++ toString i ++ "]"
            | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]")
  | _, _, .var e body, curDepth =>
      let (rest, ret) := loopBodyWalk d accReg immSlotMap body (curDepth + 1)
      (⟨0, opToLinstrR e.op (loopReg d curDepth)
            (loopExprArgs d accReg curDepth immSlotMap e)⟩ :: rest, ret)

/-- The inline looped `Lcmd` for one `forLoop` node at depth `d`, accumulator
    register `accReg`, seed operand `initOp`. Emits

    ```
        MOV  accReg, initOp        -- seed the accumulator
        MOV  Lctr<d>, #n           -- trip counter init
      .L<d>:
        <one body copy>            -- loopBodyWalk (disjoint L<d>_r* temps)
        <feedback accReg ← retReg> -- thread result back (no-op if reused)
        SUB  Lctr<d>, #1           -- counter down
        CMP  Lctr<d>, #0
        jne  .L<d>                 -- back-edge while counter != 0
    ```

    This is the verified back-edge shape `LprogControlFlow.loopLcmd` proves
    (`= runBoundedLoop`), spelled inline (this module is upstream of
    `LprogControlFlow`). **One** body copy, independent of the trip count. -/
def forLoopLcmd (d : Nat) (accReg : String) (initOp : LOperand)
    {accTy : JasminTy} (p : JLoopBody accTy) (immSlotMap : ImmSlotMap)
    (I : IsaData := x86Data) : Lcmd :=
  let (bodyW, retReg) := loopBodyWalk d accReg immSlotMap p.update 1
  let feedback : Lcmd :=
    if retReg == accReg then []
    else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg retReg]⟩]
  let ctr := loopCtr d
  let top : LLabel := d
  [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [.imm p.n]⟩
  , ⟨0, .Llabel .internal top⟩ ]
  ++ bodyW ++ feedback
  ++ (⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩
        :: (I.loopGuard ctr top).map (⟨0, ·⟩))

/-! ### 3b″. Lowering the multi-binder loop (`loopBodyWalkN` / `forLoopLcmdN`)

The `JLoopBodyN` body walk mirrors `loopBodyWalk`, but its `loopResolveVarN`
dispatches the **three roles** of binder by root slot (`slot = curDepth-1-deBruijn`,
0 = first-bound = bottom of the body context `accTy :: .reg 64 :: invTys`):

* root slot `nInv+1` (the **newest** binder, `.here` = `accTy`) → the
  accumulator register `accReg`;
* root slot `nInv` (`.reg 64`) → the loop **index** register `loopIdx d`, which
  a `stackLoad`/`stackStore` uses as the SIB index — so the op lowers to the
  register-indexed `LOADIDX`/`STOREIDX` `base[idx*scale]` (the index advances each
  trip, giving `out[i] := f(in[i])`);
* root slots `0 … nInv-1` (the **invariant** binders) → the invariant base
  registers `invRegs[nInv-1-slot]` (the input array bases, resolved at the
  `forLoopN` node — root slot `s` is the `(nInv-1-s)`-th of `invTys` because the
  context lists newest-first while the root slot counts from the bottom);
* deeper slots → the disjoint body temporary `loopReg d slot` (`L<d>_r<k>`).

`forLoopLcmdN` emits one body copy with an index init (`MOV Lidx,#0`), an index
advance each trip (`ADD Lidx,#1`), and the verified `Lctr`/`CMP`/`Lcond` back-edge
— plus one synthetic invariant-base **touch** (`CMP Lctr, invBase`) at the loop
tail per invariant base, which extends each invariant base's live range across the
whole loop (the `bodyTraceOut` liveness-extension trick) so the linear scan keeps
the array bases pinned in fixed registers and never clobbers them mid-loop. -/

/-- The loop **index** register name (`Lidx<d>`): the register the body reads as
    the runtime index of a `stackLoad`/`stackStore` (the SIB index of the emitted
    `LOADIDX`/`STOREIDX`). `MOV Lidx,#0` initialises it and `ADD Lidx,#1` advances
    it once per trip — the index thread parallel to the trip counter `Lctr<d>`. -/
def loopIdx (d : Nat) : String := "Lidx" ++ toString d

/-- Resolve a multi-binder loop-body `Var` to its `LOperand`, dispatching by root
    slot (`nInv = invRegs.length`): the accumulator (slot `nInv+1`) is `accReg`,
    the loop index (slot `nInv`) is `idxReg`, an invariant binder (slot `< nInv`)
    is its base register from `invRegs`, and a deeper slot is a body temporary
    `loopReg d slot`. The `JLoopBodyN` analogue of `loopResolveVar`. -/
def loopResolveVarN (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (curDepth : Nat) (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect}
    {τ : JasminTy} (v : Ctxt.Var Γ τ) : LOperand :=
  let nInv := invRegs.length
  let slot := curDepth - 1 - varIndex v
  if slot == nInv + 1 then
    match immSlotMap 0 with | some w => .imm w | none => .reg accReg
  else if slot == nInv then .reg idxReg
  else if slot < nInv then
    .reg (invRegs.getD (nInv - 1 - slot) ("Linv" ++ toString d ++ "_" ++ toString slot))
  else .reg (loopReg d slot)

/-- Collect a multi-binder loop-body `Expr`'s operands (the `loopResolveVarN`
    analogue of `loopExprArgs`). -/
def loopExprArgsN (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (curDepth : Nat) (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect}
    {τ : JasminTy} (e : Expr jasminDialect Γ τ) : List LOperand :=
  let rec go {tys : List JasminTy}
      (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) : List LOperand :=
    match tys, hv with
    | [], _ => []
    | _ :: _, .cons v rest =>
        loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap v :: go rest
  go e.args

/-- Resolve a bare `HVector` of in-scope variables in the multi-binder loop-body
    context (the `loopResolveVarN` analogue of `exprArgsHV`). Used to resolve a
    *nested* loop node's invariant seeds when that node sits inside a
    `forLoopBlock`'s recursive body. -/
def loopExprArgsHVN (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (curDepth : Nat) (immSlotMap : ImmSlotMap) {Γ : Ctxt jasminDialect} :
    {tys : Ctxt jasminDialect} → HVector (fun ty => Ctxt.Var Γ ty) tys →
    List LOperand
  | [], _ => []
  | _ :: _, .cons v rest =>
      loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap v
        :: loopExprArgsHVN d accReg idxReg invRegs curDepth immSlotMap rest

/-- Walk one multi-binder loop-body `Com` into a single-iteration `Lcmd` (binders
    in the disjoint `loopReg d` namespace) plus its result register name. The
    `loopBodyWalk` analogue scoped to a `JLoopBodyN` body — the walk starts at
    `curDepth = 2 + nInv` (the accumulator, index and invariants are already in
    scope). A `stackLoad`/`stackStore` at the index binder lowers to a
    register-indexed `LOADIDX`/`STOREIDX`. -/
def loopBodyWalkN (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (immSlotMap : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → (Lcmd × String)
  | _, _, .ret v, curDepth =>
      ([], match loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap v with
            | .reg n => n
            | .imm m => toString m
            | .arr b i => b ++ "[" ++ toString i ++ "]"
            | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]")
  | _, _, .var e body, curDepth =>
      let (rest, ret) := loopBodyWalkN d accReg idxReg invRegs immSlotMap body (curDepth + 1)
      (⟨0, opToLinstrR e.op (loopReg d curDepth)
            (loopExprArgsN d accReg idxReg invRegs curDepth immSlotMap e)⟩ :: rest, ret)

/-- The inline looped `Lcmd` for one `forLoopN` node at depth `d`, accumulator
    register `accReg`, seed operand `initOp`, and invariant base operands `invOps`
    (resolved at the node against the enclosing context). Emits

    ```
        MOV  accReg, initOp        -- seed the accumulator
        MOV  Lidx<d>, #0           -- index init
        MOV  Lctr<d>, #n           -- trip counter init
      .L<d>:
        <one body copy>            -- loopBodyWalkN: LOADIDX/STOREIDX at Lidx<d>
        <feedback accReg ← retReg> -- thread result back (no-op if reused)
        ADD  Lidx<d>, #1           -- index advance
        SUB  Lctr<d>, #1           -- counter down
        CMP  Lctr<d>, invBase…     -- touch each invariant base (keep it live)
        CMP  Lctr<d>, #0
        jne  .L<d>                 -- back-edge while counter != 0
    ```

    The `CMP Lctr, invBase` touches extend each invariant base's live range over
    the whole loop (so the RA keeps the array bases pinned). **One** body copy,
    independent of the trip count. -/
def forLoopLcmdN (d : Nat) (accReg : String) (initOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect} (p : JLoopBodyN accTy invTys)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) (I : IsaData := x86Data) : Lcmd :=
  let idxReg := loopIdx d
  -- Invariant base register names (the `.reg` operands; non-register seeds — an
  -- immediate constant invariant — carry no register to pin, so contribute no
  -- touch and the body refers to them by their `Linv` fallback name).
  let invRegs : List String := invOps.filterMap (fun o =>
    match o with | .reg n => some n | _ => none)
  let (bodyW, retReg) := loopBodyWalkN d accReg idxReg invRegs immSlotMap p.update
                            (2 + invTys.length)
  let feedback : Lcmd :=
    if retReg == accReg then []
    else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg retReg]⟩]
  let ctr := loopCtr d
  let top : LLabel := d
  -- One touch `I.invTouch Lctr invBase` per invariant base register: a read of the base that
  -- extends its live range across the back-edge (it is otherwise dead after its
  -- last in-body use, and the linear scan would reclaim its register mid-loop).
  let invTouch : Lcmd := invRegs.map (fun r =>
    ⟨0, I.invTouch ctr r⟩)
  [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
  , ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [.imm p.n]⟩
  , ⟨0, .Llabel .internal top⟩ ]
  ++ bodyW ++ feedback
  ++ [ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "ADD") [.reg idxReg, .imm 1]⟩
     , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ ]
  ++ invTouch
  ++ (I.loopGuard ctr top).map (⟨0, ·⟩)

/-! ### 3b‴. A real-`Lcall` leaf call inside a (multi-binder) loop body

The loop-body walks (`loopBodyWalk`/`loopBodyWalkN`) already lower an `extCall`/
`callN` `JasminOp` — via the shared `opToLinstrR` — to a single
`Lopn "CALL:<sym>" [args…]` *shadow* instruction. That shadow defers the SysV
calling convention (arg marshalling, the `RAX` return, caller-saved spilling)
to the downstream `read_linear` reassembly, which is adequate for the existing
single-leaf kernels but does **not** place a real `LinstrR.Lcall`.

`loopBodyCallLcmd` is the explicit-ABI alternative used when a loop body must
`call` an opaque leaf (MSM's Straus inner loop calling
`ed_point_add`/`ed_point_double`; the GGM real node calling an AES round): it
emits the **System V AMD64** sequence around a real `Lcall`:

```
    MOV  RDI, arg0          -- marshal call args into the SysV arg registers
    MOV  RSI, arg1          --   [RDI, RSI, RDX, RCX, R8, R9]
    …
    Lcall - <sym>:0         -- the real call (return address managed by jasmin)
    MOV  dst, RAX           -- capture the SysV integer return value
```

The marshalling `MOV`s name the ABI arg registers literally, so they survive
the physical RA (the linear scan never reassigns a literal hardware register).

**Caller-save / frame requirement (the live-across-the-call obligation).** A
real `call` clobbers all SysV *caller-saved* registers
(`RAX RCX RDX RSI RDI R8 R9 R10 R11`). Any loop-carried value (the accumulator,
the loop index `Lidx<d>`, the trip counter `Lctr<d>`, and every pinned invariant
base) that is live across the call must therefore sit in a *callee-saved*
register (`RBX RBP R12 R13 R14 R15`) or be spilled around the call. This helper
emits only the call-site marshalling; **pinning the loop-carried values into
callee-saved registers is the register allocator's obligation** — the RA must be
told that a `loopBodyCallLcmd` site is a clobber barrier for the caller-saved
class. Until the RA models that barrier, a body using this helper is correct
only when the loop-carried set already lands in callee-saved registers.

The registers `sysvArgRegs`, `sysvRetReg` and `sysvCallerSaved` are defined in
`VIR.X86IsaData`. -/

/-- Emit a real-`Lcall` SysV call to the opaque leaf `sym`, marshalling the
    resolved call-argument operands `argOps` into the SysV arg registers, then
    capturing the integer return value into `dst`. The body of a loop that must
    `call` a leaf splices this in place of the `CALL:` shadow.

    Shape: one `MOV <argReg>, <argOp>` per argument (up to 6), then the `Lcall`,
    then `MOV dst, RAX`. The `Lcall`'s `ra` (return-address slot) is `none`
    (jasmin's export path manages it); the remote label is `(sym, 0)`. -/
def loopBodyCallLcmd (dst : String) (sym : String) (argOps : List LOperand) :
    Lcmd :=
  let marshal : Lcmd :=
    (argOps.zip sysvArgRegs).map (fun ⟨op, areg⟩ =>
      ⟨0, .Lopn [.reg areg] (withWidthTag 64 "MOV") [op]⟩)
  marshal
  ++ [ ⟨0, .Lcall none (sym, 0)⟩
     , ⟨0, .Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg sysvRetReg]⟩ ]

/-! ### 3b‴′. 128-bit (SSE-class) leaf-call marshalling

`loopBodyCallLcmd` above marshals every argument as a 64-bit GP `MOV` into
`RDI…R9` and reads the result from `RAX` — the GP-only ABI class. A leaf that
takes/returns a `reg 128` value (e.g. a `bf128_mul` over two `__m128i`s) needs
the **SSE class**: System V AMD64 passes 128/256-bit SSE-class arguments in
`xmm0…xmm7` — a *separate* register sequence from the GP one — and returns a
128-bit result in `xmm0`. A mixed GP+SSE argument list draws each argument from
its own class's next register (so `f(a:reg64, b:reg128, c:reg64)` marshals
`a→RDI, b→XMM0, c→RSI`).

The move used for a 128-bit slot is `vmovdqu` (`vecMovMnem`, V-prefixed so
`isVectorMnem` classifies the touched xmm slots vector and the printer renders
the SSE move); the GP slots keep the 64-bit `MOV`.

**Cross-call-live xmm — the frame obligation.** A real `call` clobbers *all* SSE
registers too: System V has **no callee-saved xmm registers on Linux**
(`xmm0…xmm15` are all volatile). So a 128-bit value that is live *across* the
call cannot be parked in a surviving vector register — it **must be stack-spilled
around the call** (there is no callee-saved xmm slot to route it to, unlike the
GP case where `calleeFirstPhys` can place a loop-carried GP value in
`RBX/RBP/R12/R13`). This helper emits only the call-site marshalling; a body that
holds a vector value across the call needs the vector-RA to insert the spill/
reload pair. The pinning of the literal `XMM0…XMM7` marshalling names against the
RA is provided by `isHwRegName` (extended below to include the SSE arg regs).

The registers `sysvSseArgRegs` and `sysvSseRetReg` are defined in `VIR.X86IsaData`. -/

/-- The 128-bit unaligned vector move mnemonic (`vmovdqu`) used to marshal a
    `reg 128` argument into an xmm arg register and to capture a 128-bit result
    from `xmm0`. V-prefixed so `isVectorMnem` classifies the touched slots as
    vector (the production vector-RA path) and the AT&T printer renders the SSE
    move — never a GP `movq`. -/
def vecMovMnem : String := "VMOVDQU"

/-- Marshal a *classed* argument list into the SysV registers, threading the two
    per-class next-register counters (GP → `sysvArgRegs` from `gpIdx`; SSE →
    `sysvSseArgRegs` from `sseIdx`). Each `(op, isSse)` produces one move:
    `VMOVDQU <xmm>, op` for an SSE (`isSse = true`, `reg 128`) argument,
    `MOV <gp>, op` for a GP argument. The two counters advance independently, so
    a mixed list places each argument in its own class's next register (SysV). -/
def marshalClassedArgs : List (LOperand × Bool) → Nat → Nat → Lcmd
  | [], _, _ => []
  | (op, isSse) :: rest, gpIdx, sseIdx =>
      if isSse then
        match sysvSseArgRegs[sseIdx]? with
        | some xreg =>
            ⟨0, .Lopn [.reg xreg] vecMovMnem [op]⟩
              :: marshalClassedArgs rest gpIdx (sseIdx + 1)
        | none => marshalClassedArgs rest gpIdx (sseIdx + 1)
      else
        match sysvArgRegs[gpIdx]? with
        | some greg =>
            ⟨0, .Lopn [.reg greg] (withWidthTag 64 "MOV") [op]⟩
              :: marshalClassedArgs rest (gpIdx + 1) sseIdx
        | none => marshalClassedArgs rest (gpIdx + 1) sseIdx

/-- The class-aware analogue of `loopBodyCallLcmd`: marshal a mixed GP+SSE
    argument list (`marshalClassedArgs`), a real `Lcall`, then capture the result
    from `xmm0` (`VMOVDQU`, when `dstIsVec`) or `RAX` (`MOV`, otherwise).

    Byte-compatible degeneracy: with every `isSse = false` and `dstIsVec = false`
    this is exactly `loopBodyCallLcmd` (`MOV RDI…`, `Lcall`, `MOV dst, RAX`), so
    the widened path collapses to the GP path on an all-GP call. -/
def loopBodyCallLcmdClassed (dst : String) (dstIsVec : Bool) (sym : String)
    (argOps : List (LOperand × Bool)) : Lcmd :=
  marshalClassedArgs argOps 0 0
  ++ [ ⟨0, .Lcall none (sym, 0)⟩
     , ⟨0, if dstIsVec then .Lopn [.reg dst] vecMovMnem [.reg sysvSseRetReg]
           else .Lopn [.reg dst] (withWidthTag 64 "MOV") [.reg sysvRetReg]⟩ ]

/-- Parse a widened leaf-call shadow mnemonic
    (`CALLW:<retW>;<w0,w1,…>;<name>` or the multi-result `CALLNW:` variant) into
    `(retW, argWs, name)`. Returns `none` for a plain `CALL:`/`CALLN:` shadow (or
    any non-call op), so the caller falls through to the GP path. The name may
    itself contain `;`-free identifier characters; any trailing `;` segments are
    re-joined into the name (defensive — leaf names are `;`-free). -/
def parseCallW (opn : String) : Option (Nat × List Nat × String) :=
  let body? :=
    if hasPrefix opn "CALLNW:" then some (strDrop opn 7)
    else if hasPrefix opn "CALLW:" then some (strDrop opn 6)
    else none
  match body? with
  | none => none
  | some s =>
      match splitOnChar ';' s with
      | retStr :: argStr :: nameParts =>
          match strToNat? retStr with
          | some retW =>
              let argWs := (splitOnChar ',' argStr).filterMap strToNat?
              some (retW, argWs, String.intercalate ";" nameParts)
          | none => none
      | _ => none

/-- The marshalling sequence for one in-body leaf call (`extCall`/`callN`),
    dispatched by the declared arg/ret widths: an all-GP call (`callHasWide`
    `false`) is the byte-identical `loopBodyCallLcmd` GP path; a call with a
    `reg 128` argument or result routes each argument to its SysV class and takes
    the result from `xmm0` (`loopBodyCallLcmdClassed`). Shared by the straight-
    line and loop-body lowerings so both express a 128-bit leaf call. -/
def callMarshalHere (dst name : String) (argTys : List JasminTy) (retTy : JasminTy)
    (srcs : List LOperand) : Lcmd :=
  let argWs := argTys.map callMarshalWidth
  let retW := callMarshalWidth retTy
  if callHasWide retW argWs then
    loopBodyCallLcmdClassed dst (retW > 64) name
      ((srcs.zip argWs).map (fun ⟨op, w⟩ => (op, w > 64)))
  else loopBodyCallLcmd dst name srcs

/-! ### 3b‴″. Buffer-returning leaf calls in a loop body

`callMarshalHere` dispatches a leaf call between the GP and SSE register classes
by `callMarshalWidth`, which sends every non-`reg` type to 64. A leaf whose
result is a `stackArr` returns it through an **out-pointer** instead, so its
result belongs to no register class: the caller passes the address of a
destination buffer as the first argument and the leaf writes through it.

The declarations below give such a call a home inside a rolled loop body. Each
buffer-typed binding of the body gets a frame slot at a fixed byte offset from
the bottom of the frame; the call marshals that slot's address into `RDI` ahead
of its operands and captures no `RAX`. Offsets are assigned by a pre-pass over
the body `Com` (`loopBufBindings`), so they are fixed when the body is walked and
need no knowledge of the spill count the register allocator settles later. The
bytes are declared to `LprogAsmPrinter.frameSize` by a `FRAMEADD` directive. -/

/-- The `stackArr` result type of a leaf-call op, and `none` for a call whose
    result marshals in a register and for every non-call op. A `callN`'s result is
    its head return type, the slot the loop-body walk binds. -/
def callResultBufferTy : JasminOp → Option JasminTy
  | .extCall _ _ (.stackArr w n) => some (.stackArr w n)
  | .callN _ _ retTys =>
      match retTys.headD (.reg 0) with
      | .stackArr w n => some (.stackArr w n)
      | _ => none
  | _ => none

/-- The byte size of a buffer operand: a `stackArr w n` is `n` elements of `w`
    bits. Every other type is a register value and occupies no buffer. -/
def bufTyBytes : JasminTy → Nat
  | .stackArr w n => n * w / 8
  | _ => 0

/-- The operand name of a loop-body scratch buffer at byte offset `off`: the
    `mem.RSP.<off>` reference the printer renders as `off(%rsp)`, addressed from
    the post-`leaq` `%rsp`. Agrees with `memName "RSP"`, which is defined further
    down this file than the loop-body walk that needs this name. -/
def frameBufName (off : Nat) : String := "mem.RSP." ++ toString off

/-- The buffer-typed call bindings of a loop-body `Com`, as `(binder slot, result
    byte size)` in program order. A binding's slot is the `curDepth` at which it is
    made, which is the number `loopResolveVarN` resolves a reference to it to. -/
def loopBufBindings :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → List (Nat × Nat)
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      let rest := loopBufBindings body (curDepth + 1)
      match callResultBufferTy e.op with
      | some ty => (curDepth, bufTyBytes ty) :: rest
      | none => rest

/-- The byte offset of the buffer bound at slot `s`, from the bottom of the frame:
    the prefix sum of the preceding buffer sizes, each rounded up to eight bytes.
    `none` when `s` binds no buffer. The loop-body analogue of
    `ArrAbiOrch.binBufOff`. -/
def loopBufOff (bs : List (Nat × Nat)) (s : Nat) : Option Nat :=
  let rec go (l : List (Nat × Nat)) (acc : Nat) : Option Nat :=
    match l with
    | [] => none
    | (slot, sz) :: t =>
        if slot == s then some acc else go t (acc + (sz + 7) / 8 * 8)
  go bs 0

/-- The total scratch bytes a loop body's buffer bindings occupy, each 8-aligned:
    the `FRAMEADD` the body declares. The loop-body analogue of
    `ArrAbiOrch.scratchTotal`. -/
def loopBufTotal (bs : List (Nat × Nat)) : Nat :=
  bs.foldl (fun acc p => acc + (p.2 + 7) / 8 * 8) 0

-- Static checks pinning the buffer layout against silent change: a body with no
-- buffer binding reserves nothing and resolves no slot, and consecutive buffers
-- are placed at 8-aligned offsets in program order.
#guard loopBufOff [] 3 = none
#guard loopBufTotal [] = 0
#guard loopBufOff [(3, 96), (5, 12)] 3 = some 0
#guard loopBufOff [(3, 96), (5, 12)] 5 = some 96
#guard loopBufOff [(3, 96), (5, 12)] 4 = none
#guard loopBufTotal [(3, 96), (5, 12)] = 112

/-! #### The in-place accumulator case

A buffer-returning leaf call whose destination is the accumulator's own storage
— `acc := madd(acc, sel)` — takes the accumulator's base as its out-pointer
instead of a scratch slot, which is the `framedAbiCallMarshal` marshalling
(`RDI` and `RSI` both the base) at a loop-body call site. The binding that
carries it is identified from the body `Com` alone: its op returns a `stackArr`
(`callResultBufferTy`), its first operand is the accumulator binder (root slot
`startDepth - 1`, the slot `loopResolveVarN` resolves to `accReg`), and it is
the binding the body's terminal `.ret` names. A reference to such a binding
resolves to `accReg`, so the call writes the accumulator and the loop's feedback
move is absent by the `retReg == accReg` test that already governs it. -/

/-- The root binder slot a loop-body `Com`'s terminal `.ret` names, walking from
    a walk start depth `curDepth`. The slot arithmetic is `loopResolveVarN`'s:
    `curDepth - 1 - varIndex v`. -/
def comBodyRetSlot :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → Nat
  | _, _, .ret v, curDepth => curDepth - 1 - varIndex v
  | _, _, .var _ body, curDepth => comBodyRetSlot body (curDepth + 1)

/-- The root binder slot of an operand vector's first entry, at context depth
    `curDepth`, and `none` for an empty vector. -/
def hvecArg0Slot {Γ : Ctxt jasminDialect} (curDepth : Nat) :
    {tys : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) tys → Option Nat
  | [], _ => none
  | _ :: _, .cons v _ => some (curDepth - 1 - varIndex v)

/-- The root binder slot of an `Expr`'s first operand at context depth
    `curDepth`, and `none` for a nullary op. -/
def exprArg0Slot {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (e : Expr jasminDialect Γ τ) (curDepth : Nat) : Option Nat :=
  hvecArg0Slot curDepth e.args

/-- Scan a loop-body `Com` from `curDepth` for the binding that updates the
    accumulator in place: a buffer-typed call binding whose first operand is the
    accumulator (root slot `startDepth - 1`) and whose own slot is `retSlot`. -/
def loopInPlaceBufSlotAt (startDepth retSlot : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → Option Nat
  | _, _, .ret _, _ => none
  | _, _, .var e body, curDepth =>
      if (callResultBufferTy e.op).isSome
          && exprArg0Slot e curDepth == some (startDepth - 1)
          && curDepth == retSlot then
        some curDepth
      else loopInPlaceBufSlotAt startDepth retSlot body (curDepth + 1)

/-- The slot of the loop body's in-place accumulator update, and `none` when the
    body has none: the body's returned binding, when that binding is a
    buffer-typed call taking the accumulator as its first operand. -/
def loopInPlaceBufSlot {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (startDepth : Nat) : Option Nat :=
  loopInPlaceBufSlotAt startDepth (comBodyRetSlot c startDepth) c startDepth

/-- The buffer bindings that need a frame scratch slot: `loopBufBindings` without
    the in-place accumulator update, whose result goes to the accumulator's own
    storage. Equal to `loopBufBindings` on a body with no in-place update. -/
def loopScratchBufBindings {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (startDepth : Nat) : List (Nat × Nat) :=
  match loopInPlaceBufSlot c startDepth with
  | none => loopBufBindings c startDepth
  | some s => (loopBufBindings c startDepth).filter (fun b => b.1 != s)

/-- Marshal one loop-body call operand into SysV argument register `areg`: a
    memory operand by its address (`LEA`), every other operand by its value
    (`MOV`). -/
def loopBufMarshalArg (areg : String) (op : LOperand) : Linstr :=
  match op with
  | .reg n =>
      if hasPrefix n "mem." then ⟨0, .Lopn [.reg areg] "LEA:64" [.reg n]⟩
      else ⟨0, .Lopn [.reg areg] (withWidthTag 64 "MOV") [op]⟩
  | _ => ⟨0, .Lopn [.reg areg] (withWidthTag 64 "MOV") [op]⟩

/-- Marshal one buffer-returning leaf call: each operand into its SysV argument
    register from `RSI` on — a buffer operand by its address (`LEA`), a register
    operand by its value (`MOV`) — then the destination buffer's address into
    `RDI` (the out-pointer), then the real `Lcall`. No `RAX` capture: the leaf
    returns through the out-pointer. The `ArrAbiOrch.emitOneCall` shape at a
    loop-body call site.

    The out-pointer is written last because its own source is a frame slot, which
    no argument marshal can clobber, while `RDI` is an allocatable register that
    an argument's source may occupy: writing it after every argument source has
    been read is what keeps such an argument readable. -/
def loopBodyCallLcmdBuf (dstMem sym : String) (argOps : List LOperand) : Lcmd :=
  let outLea : Linstr := ⟨0, .Lopn [.reg "RDI"] "LEA:64" [.reg dstMem]⟩
  let argMarshal : Lcmd :=
    (argOps.zip (sysvArgRegs.drop 1)).map (fun ⟨op, areg⟩ => loopBufMarshalArg areg op)
  argMarshal ++ [outLea, ⟨0, .Lcall none (sym, 0)⟩]

/-- Marshal one buffer-returning leaf call that writes the accumulator in place:
    the operands into the SysV argument registers from `RSI` on, the first of
    which is the accumulator, then the accumulator operand into `RDI` (the
    out-pointer), then the real `Lcall`. The `framedAbiCallMarshal` shape — one
    base in both the out-pointer and its own argument register — at a loop-body
    call site. No `RAX` capture and no scratch slot.

    The out-pointer is written last for the reason `loopBodyCallLcmdBuf` states:
    `RDI` is allocatable, so an argument whose source the allocator places there
    is read before the out-pointer overwrites it. The accumulator itself is
    loop-carried, which the looped-call barrier places in a callee-saved register
    (`calleeFirstPhys`), so it survives the argument marshalling. -/
def loopBodyCallLcmdBufInPlace (accOp : LOperand) (sym : String)
    (argOps : List LOperand) : Lcmd :=
  let argMarshal : Lcmd :=
    (argOps.zip (sysvArgRegs.drop 1)).map (fun ⟨op, areg⟩ => loopBufMarshalArg areg op)
  argMarshal ++ [loopBufMarshalArg "RDI" accOp, ⟨0, .Lcall none (sym, 0)⟩]

-- Static checks pinning the marshalling order: the argument registers are
-- written in SysV order from `RSI` on and the out-pointer `RDI` last, so an
-- argument whose source the register allocator places in `RDI` is read before
-- the out-pointer overwrites it.
#guard (loopBodyCallLcmdBuf "mem.RSP.0" "madd" [.reg "L0_r3", .reg "L0_r4"]).filterMap
    (fun i => match i.li_i with | .Lopn [.reg d] _ _ => some d | _ => none)
  = ["RSI", "RDX", "RDI"]
#guard (loopBodyCallLcmdBufInPlace (.reg "L0_r1") "madd"
    [.reg "L0_r1", .reg "L0_r4"]).filterMap
    (fun i => match i.li_i with | .Lopn [.reg d] _ _ => some d | _ => none)
  = ["RSI", "RDX", "RDI"]

/-- Resolve a multi-binder loop-body `Var` with the buffer bindings in scope: a
    reference to the in-place accumulator update (`ipSlot`) is `accReg`, a
    reference to a scratch buffer binding is its frame slot `mem.RSP.<off>`, and
    every other reference is exactly `loopResolveVarN`'s. -/
def loopResolveVarNBuf (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (bufs : List (Nat × Nat)) (ipSlot : Option Nat) (curDepth : Nat)
    (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (v : Ctxt.Var Γ τ) : LOperand :=
  let slot := curDepth - 1 - varIndex v
  if ipSlot == some slot then .reg accReg
  else
    match loopBufOff bufs slot with
    | some off => .reg (frameBufName off)
    | none => loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap v

/-- Collect a loop-body `Expr`'s operands with the buffer bindings in scope (the
    `loopResolveVarNBuf` analogue of `loopExprArgsN`). -/
def loopExprArgsNBuf (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (bufs : List (Nat × Nat)) (ipSlot : Option Nat) (curDepth : Nat)
    (immSlotMap : ImmSlotMap)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (e : Expr jasminDialect Γ τ) :
    List LOperand :=
  let rec go {tys : List JasminTy}
      (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) : List LOperand :=
    match tys, hv with
    | [], _ => []
    | _ :: _, .cons v rest =>
        loopResolveVarNBuf d accReg idxReg invRegs bufs ipSlot curDepth immSlotMap v
          :: go rest
  go e.args

/-- The `loopBodyWalkNCall` body walk, but lowering a leaf call whose result is a
    `stackArr` to an out-pointer sequence: the in-place accumulator update
    (`ipSlot`) writes through `accReg` (`loopBodyCallLcmdBufInPlace`) and every
    other buffer-typed call writes into its frame slot
    (`loopBodyCallLcmdBuf`), with a reference to such a binding resolving to that
    destination. A body with no buffer-typed call binding has an empty `bufs` and
    `ipSlot = none`, so every op lowers exactly as `loopBodyWalkNCall` lowers
    it. -/
def loopBodyWalkNBuf (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (bufs : List (Nat × Nat)) (ipSlot : Option Nat) (immSlotMap : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → (Lcmd × String)
  | _, _, .ret v, curDepth =>
      ([], match loopResolveVarNBuf d accReg idxReg invRegs bufs ipSlot curDepth
              immSlotMap v with
            | .reg n => n
            | .imm m => toString m
            | .arr b i => b ++ "[" ++ toString i ++ "]"
            | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]")
  | _, _, .var e body, curDepth =>
      let (rest, ret) :=
        loopBodyWalkNBuf d accReg idxReg invRegs bufs ipSlot immSlotMap body (curDepth + 1)
      let dstReg := loopReg d curDepth
      let srcs := loopExprArgsNBuf d accReg idxReg invRegs bufs ipSlot curDepth immSlotMap e
      let here : Lcmd :=
        match e.op with
        | .extCall name argTys retTy =>
            if ipSlot == some curDepth then
              loopBodyCallLcmdBufInPlace (.reg accReg) name srcs
            else
              match loopBufOff bufs curDepth with
              | some off => loopBodyCallLcmdBuf (frameBufName off) name srcs
              | none => callMarshalHere dstReg name argTys retTy srcs
        | .callN name argTys retTys =>
            if ipSlot == some curDepth then
              loopBodyCallLcmdBufInPlace (.reg accReg) name srcs
            else
              match loopBufOff bufs curDepth with
              | some off => loopBodyCallLcmdBuf (frameBufName off) name srcs
              | none => callMarshalHere dstReg name argTys (retTys.headD (.reg 0)) srcs
        | _ => [⟨0, opToLinstrR e.op dstReg srcs⟩]
      (here ++ rest, ret)

/-! ### 3b⁗. Straight-line `CALL:`/`CALLN:` shadow → real `Lcall` expansion

The straight-line body walk (`comToBody`, via `opToLinstrR`) lowers a
non-reserved `extCall`/`callN` leaf to a single `Lopn "CALL:<sym>"/"CALLN:<sym>"`
*shadow* (the same shadow the loop walk used before `loopBodyWalkNCall`). The
owned AT&T printer (`LprogAsmPrinter.renderLinstrR`) has no arm for that
mnemonic, so it surfaces `# UNHANDLED-OP CALL:<sym>` — a straight-line body that
mixes arithmetic/memref with a named-leaf call cannot front-compile.

`expandCallShadows` is the straight-line analogue of `loopBodyWalkNCall`: a
post-`comToBody` pass that rewrites every `CALL:`/`CALLN:` shadow into the
`loopBodyCallLcmd` System V AMD64 sequence (marshal args into `RDI…R9`, a real
`Lcall`, capture `RAX` into the result), leaving every other instruction
untouched. A body with no call shadow is returned verbatim (identity), so the
call-free straight-line export is byte-identical. Because the expanded body now
carries a real `LinstrR.Lcall`, `bodyHasCall` fires, and the ABI export's
`physBodyWithStores` selects the caller-save clobber barrier
(`remapOperandCalleeSave` — literal SysV hardware names pinned, other GP slots
routed callee-saved-first through `calleeFirstPhys`) exactly as the value-return
path (`comToLfundefPhys`) and the looped call path already do. -/

/-- Rewrite each straight-line leaf-call *shadow* `Lopn` (`CALL:<sym>` from
    `extCall`, `CALLN:<sym>` from `callN`) into the real-`Lcall` System V
    marshalling sequence `loopBodyCallLcmd`. Every non-shadow instruction passes
    through unchanged; a body with no shadow is the identity image (byte-identical
    call-free export). The `CALLN:` (multi-result) head slot captures `RAX` (the
    single-output linstr layer names the head result only). -/
def expandCallShadows (body : Lcmd) : Lcmd :=
  body.flatMap (fun i =>
    match i.li_i with
    | .Lopn [.reg dst] opn argOps =>
        match parseCallW opn with
        -- Widened (`CALLW:`/`CALLNW:`) shadow: dispatch each argument to its SysV
        -- register class by the declared width (`> 64` ⇒ SSE/xmm), and take the
        -- result from `xmm0` when the return width is SSE-class.
        | some (retW, argWs, sym) =>
            let classed := (argOps.zip argWs).map (fun ⟨op, w⟩ => (op, w > 64))
            loopBodyCallLcmdClassed dst (retW > 64) sym classed
        | none =>
          if hasPrefix opn "CALLN:" then loopBodyCallLcmd dst (strDrop opn 6) argOps
          else if hasPrefix opn "CALL:" then loopBodyCallLcmd dst (strDrop opn 5) argOps
          else [i]
    | _ => [i])

/-- The `loopBodyWalkN` body walk, but lowering an `extCall` leaf in the body to a
    **real `Lcall`** (via `loopBodyCallLcmd`) instead of the `CALL:` shadow
    `Lopn`. Every other op (`regArith`, `stackLoad/Store`, `regConst`, shifts)
    lowers byte-identically to `loopBodyWalkN`, so a call-free body is unchanged.

    This is the `JLoopBodyN`-body variant that makes MSM's Straus inner loop and
    the GGM real AES-PRG node expressible with an in-loop call: the body's
    `extCall in[idx]`/`extCall acc` lowers to the marshalled SysV call sequence,
    spliced inside the rolled back-edge. -/
def loopBodyWalkNCall (d : Nat) (accReg idxReg : String) (invRegs : List String)
    (immSlotMap : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → (Lcmd × String)
  | _, _, .ret v, curDepth =>
      ([], match loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap v with
            | .reg n => n
            | .imm m => toString m
            | .arr b i => b ++ "[" ++ toString i ++ "]"
            | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]")
  | _, _, .var e body, curDepth =>
      let (rest, ret) := loopBodyWalkNCall d accReg idxReg invRegs immSlotMap body (curDepth + 1)
      let dstReg := loopReg d curDepth
      let srcs := loopExprArgsN d accReg idxReg invRegs curDepth immSlotMap e
      -- A leaf call (`extCall`/`callN`) lowers to a real `Lcall` with SysV
      -- marshalling; every other op keeps the straight `opToLinstrR` lowering.
      let here : Lcmd :=
        match e.op with
        | .extCall name argTys retTy => callMarshalHere dstReg name argTys retTy srcs
        | .callN name argTys retTys =>
            callMarshalHere dstReg name argTys (retTys.headD (.reg 0)) srcs
        | _ => [⟨0, opToLinstrR e.op dstReg srcs⟩]
      (here ++ rest, ret)

/-- Does a `Com` body issue a leaf call (`extCall`/`callN`)? Used to decide, per
    `forLoopN` node, whether the loop body must be lowered via `loopBodyWalkNCall`
    (a real `Lcall`) rather than the `CALL:` shadow `loopBodyWalkN`. A body with
    no call op returns `false`, so the call-walk selection is a no-op there and
    the loop lowers byte-identically. -/
def comBodyHasCall :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Bool
  | _, _, .ret _ => false
  | _, _, .var e body =>
      (match e.op with
        | .extCall _ _ _ => true
        | .callN _ _ _ => true
        | _ => false) || comBodyHasCall body

/-- Does a `ComL` contain any `forLoopN` node whose body issues a leaf call? When
    `false`, the call-aware lowering is a no-op and the program lowers
    byte-identically to the shadow path. -/
def comLHasLoopCall :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → ComL Γ t → Bool
  | _, _, .ret _ => false
  | _, _, .var _ body => comLHasLoopCall body
  | _, _, .forLoop _ _ body => comLHasLoopCall body
  | _, _, .forLoopN loop _ _ body =>
      comBodyHasCall loop.update || comLHasLoopCall body
  | _, _, .forLoopNRt update _ _ _ body =>
      comBodyHasCall update || comLHasLoopCall body
  | _, _, .forLoopNRtNested innerCount innerUpdate _ _ _ body =>
      comBodyHasCall innerCount || comBodyHasCall innerUpdate || comLHasLoopCall body
  | _, _, .whileNz update _ _ _ body =>
      comBodyHasCall update || comLHasLoopCall body
  | _, _, .forLoopBlock loopBody _ _ _ body =>
      comLHasLoopCall loopBody || comLHasLoopCall body

/-- `forLoopLcmdN`, but lowering the loop body with `loopBodyWalkNCall` so an
    in-body `extCall`/`callN` becomes a **real `Lcall`** (the SysV marshalling
    sequence) rather than the `CALL:` shadow `Lopn`. Every other field — the seed
    `MOV`, the index/counter init, the invariant-base touches, and the back-edge —
    is identical to `forLoopLcmdN`, and on a call-free body `loopBodyWalkNCall`
    equals `loopBodyWalkN` (`loopBodyWalkNCall_callfree_eq_loopBodyWalkN`), so a
    call-free loop is byte-identical. -/
def forLoopLcmdNCall (d : Nat) (accReg : String) (initOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect} (p : JLoopBodyN accTy invTys)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) (I : IsaData := x86Data) : Lcmd :=
  let idxReg := loopIdx d
  let invRegs : List String := invOps.filterMap (fun o =>
    match o with | .reg n => some n | _ => none)
  -- The slot of the body's in-place accumulator update, if it has one, and the
  -- buffer-typed call bindings that need frame scratch. With no in-place update
  -- and no scratch buffer the walk is `loopBodyWalkNCall`, so a body with no
  -- buffer-returning call emits exactly the instructions the call walk emits.
  let startDepth := 2 + invTys.length
  let ipSlot := loopInPlaceBufSlot p.update startDepth
  let bufs := loopScratchBufBindings p.update startDepth
  let (bodyW, retReg) :=
    if bufs.isEmpty && ipSlot.isNone then
      loopBodyWalkNCall d accReg idxReg invRegs immSlotMap p.update startDepth
    else
      loopBodyWalkNBuf d accReg idxReg invRegs bufs ipSlot immSlotMap p.update startDepth
  -- A scratch buffer result lives in its frame slot, not a register, so there is
  -- no register to thread back into the accumulator and no `MOV` is emitted; an
  -- in-place update returns `accReg` itself, which the `retReg == accReg` test
  -- already leaves alone.
  let feedback : Lcmd :=
    if retReg == accReg || hasPrefix retReg "mem." then []
    else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg retReg]⟩]
  -- The scratch bytes the body's buffers need, declared to
  -- `LprogAsmPrinter.frameSize`. Absent when the body lays no buffer.
  let frameAdd : Lcmd :=
    if bufs.isEmpty then []
    else [⟨0, .Lopn [] "FRAMEADD" [.imm (loopBufTotal bufs)]⟩]
  let ctr := loopCtr d
  let top : LLabel := d
  let invTouch : Lcmd := invRegs.map (fun r =>
    ⟨0, I.invTouch ctr r⟩)
  frameAdd ++
  [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
  , ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [.imm p.n]⟩
  , ⟨0, .Llabel .internal top⟩ ]
  ++ bodyW ++ feedback
  ++ [ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "ADD") [.reg idxReg, .imm 1]⟩
     , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ ]
  ++ invTouch
  ++ (I.loopGuard ctr top).map (⟨0, ·⟩)

/-- `forLoopLcmdN`, but the trip counter is seeded from a **runtime operand**
    `countOp` (`MOV Lctr, countOp`) instead of the static immediate `#p.n`. The
    body walk, index/counter advance, invariant-base touches, and the verified
    `Lctr`/`CMP`/`Lcond` back-edge are otherwise identical to `forLoopLcmdN`, so a
    fixed-count loop and a runtime-count loop differ in exactly one instruction
    (the counter seed). The loop body is taken directly as `update` (the
    `JLoopBodyN`-shaped `Com` over `accTy :: .reg 64 :: invTys`); `nInv` is read
    off the implicit `invTys`. The runtime count `countOp` is read once at the
    seed, before the loop label, so it need only be live entry→seed (the counter
    `Lctr<d>` carries the value across the back-edge). -/
def forLoopLcmdNRt (d : Nat) (accReg : String) (initOp countOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) (I : IsaData := x86Data) : Lcmd :=
  let idxReg := loopIdx d
  let invRegs : List String := invOps.filterMap (fun o =>
    match o with | .reg n => some n | _ => none)
  let (bodyW, retReg) := loopBodyWalkN d accReg idxReg invRegs immSlotMap update
                            (2 + invTys.length)
  let feedback : Lcmd :=
    if retReg == accReg then []
    else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg retReg]⟩]
  let ctr := loopCtr d
  let top : LLabel := d
  -- Zero-trip skip target. `count` is a RUNTIME value that may be 0; the back-edge
  -- below is a do-while (bottom test), so without this top guard `count = 0` would
  -- decrement the counter to `2^64-1` and loop until an OOB access. The guard makes
  -- the emitted loop run exactly `count` times, matching the `List.range count` fold
  -- denotation. High offset so it never collides with any loop-depth `top`.
  let endL : LLabel := d + 0x40000000
  let invTouch : Lcmd := invRegs.map (fun r =>
    ⟨0, I.invTouch ctr r⟩)
  [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
  , ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [countOp]⟩ ]
  ++ (I.zeroTripGuard ctr top endL).map (⟨0, ·⟩)
  ++ [ ⟨0, .Llabel .internal top⟩ ]
  ++ bodyW ++ feedback
  ++ [ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "ADD") [.reg idxReg, .imm 1]⟩
     , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ ]
  ++ invTouch
  ++ ((I.loopGuard ctr top).map (⟨0, ·⟩) ++ [ ⟨0, .Llabel .internal endL⟩ ])

/-! ### 3b⁗. Lowering the nested runtime loop (`forLoopLcmdNRtNested`)

The nested runtime loop's per-outer inner-count body `innerCount` runs over
`.reg 64 (outer index) :: invTys` — no accumulator/inner-index binder. Its walk
`nestCountWalk` resolves the outer-index binder (root slot `nInv`) to the outer
loop's index register and the invariant binders (root slots `< nInv`) to their
base registers, mirroring the invariant dispatch of `loopResolveVarN`. -/

/-- Resolve an inner-count-body `Var` (context `.reg 64 (outer) :: invTys`): the
    outer index (root slot `nInv`) is `outerIdxReg`, an invariant (slot `< nInv`)
    is its base register, a deeper slot is a body temporary `loopReg d slot`. -/
def nestCountResolveVar (d : Nat) (outerIdxReg : String) (invRegs : List String)
    (curDepth : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (v : Ctxt.Var Γ τ) : LOperand :=
  let nInv := invRegs.length
  let slot := curDepth - 1 - varIndex v
  if slot == nInv then .reg outerIdxReg
  else if slot < nInv then
    .reg (invRegs.getD (nInv - 1 - slot) ("Linv" ++ toString d ++ "_" ++ toString slot))
  else .reg (loopReg d slot)

/-- Collect an inner-count-body `Expr`'s operands (the `nestCountResolveVar`
    analogue of `loopExprArgsN`). -/
def nestCountExprArgs (d : Nat) (outerIdxReg : String) (invRegs : List String)
    (curDepth : Nat) {Γ : Ctxt jasminDialect} {τ : JasminTy}
    (e : Expr jasminDialect Γ τ) : List LOperand :=
  let rec go {tys : List JasminTy}
      (hv : HVector (fun ty => Ctxt.Var Γ ty) tys) : List LOperand :=
    match tys, hv with
    | [], _ => []
    | _ :: _, .cons v rest =>
        nestCountResolveVar d outerIdxReg invRegs curDepth v :: go rest
  go e.args

/-- Walk one inner-count body `Com (.reg 64 :: invTys) (.reg 64)` into a
    single-copy `Lcmd` (binders in the disjoint `loopReg d` namespace) plus its
    result register name — the per-outer inner-trip recompute (`num >> (jd+1)` in
    the GGM shape). The `loopBodyWalk` analogue for the accumulator-free count
    body; the walk starts at `curDepth = 1 + nInv` (outer index + invariants in
    scope). -/
def nestCountWalk (d : Nat) (outerIdxReg : String) (invRegs : List String) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → (Lcmd × String)
  | _, _, .ret v, curDepth =>
      ([], match nestCountResolveVar d outerIdxReg invRegs curDepth v with
            | .reg n => n
            | .imm m => toString m
            | .arr b i => b ++ "[" ++ toString i ++ "]"
            | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]")
  | _, _, .var e body, curDepth =>
      let (rest, ret) := nestCountWalk d outerIdxReg invRegs body (curDepth + 1)
      (⟨0, opToLinstrR e.op (loopReg d curDepth)
            (nestCountExprArgs d outerIdxReg invRegs curDepth e)⟩ :: rest, ret)

/-- The inline **nested** runtime-loop `Lcmd` for one `forLoopNRtNested` node at
    depth `d`: a runtime outer loop (top label `d`, counter `Lctr<d>`, index
    `Lidx<d>`) whose body **recomputes** the inner trip (`nestCountWalk innerCount`
    into the inner counter) and then runs an inner runtime loop (top label `d+1`,
    counter `Lctr<d+1>`, index `Lidx<d+1>`). Two nested back-edges plus the
    per-outer inner-count recompute — the `Lcmd` image of
    `JasminLsemMemLoopNestDepth.ggmProg`'s structure (outer/inner `loopLinstrRM`
    with the `mid := num >> sa` seed). The inner body is walked with the outer
    index threaded in as the first invariant (`outerIdxReg :: invRegs`), so
    `innerUpdate`'s outer-index binder resolves to `Lidx<d>`. Both loops carry a
    `count = 0` top-guard skip (runtime counts may be 0). -/
def forLoopLcmdNRtNested (d : Nat) (accReg : String) (initOp outerCountOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (innerCount : Com jasminDialect (.reg 64 :: invTys) (JasminTy.reg 64))
    (innerUpdate : Com jasminDialect (accTy :: .reg 64 :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) (I : IsaData := x86Data) : Lcmd :=
  let outerIdxReg := loopIdx d
  let outerCtr := loopCtr d
  let innerD := d + 1
  let innerIdxReg := loopIdx innerD
  let innerCtr := loopCtr innerD
  let invRegs : List String := invOps.filterMap (fun o =>
    match o with | .reg n => some n | _ => none)
  -- Per-outer inner-count recompute (over `.reg 64 (outer) :: invTys`).
  let (cntW, cntRet) := nestCountWalk d outerIdxReg invRegs innerCount (1 + invTys.length)
  -- Inner body walk: the outer index is threaded as the FIRST invariant, so the
  -- inner-body context `accTy :: .reg 64 (inner) :: .reg 64 (outer) :: invTys`
  -- reads the outer index at `Lidx<d>` and the invariants after it.
  let (bodyW, retReg) := loopBodyWalkN innerD accReg innerIdxReg (outerIdxReg :: invRegs)
                            immSlotMap innerUpdate (2 + (invTys.length + 1))
  let feedback : Lcmd :=
    if retReg == accReg then []
    else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg retReg]⟩]
  let outerTop : LLabel := d
  let outerEnd : LLabel := d + 0x40000000
  let innerTop : LLabel := innerD
  let innerEnd : LLabel := innerD + 0x40000000
  let outerInvTouch : Lcmd := invRegs.map (fun r =>
    ⟨0, I.invTouch outerCtr r⟩)
  -- Seed accumulator + outer index/counter, guard the runtime outer count.
  [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
  , ⟨0, .Lopn [.reg outerIdxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
  , ⟨0, .Lopn [.reg outerCtr] (withWidthTag 64 "MOV") [outerCountOp]⟩ ]
  ++ (I.zeroTripGuard outerCtr outerTop outerEnd).map (⟨0, ·⟩)
  ++ [ ⟨0, .Llabel .internal outerTop⟩ ]
  -- Outer body: recompute inner count, seed inner index/counter, guard.
  ++ cntW
  ++ (⟨0, .Lopn [.reg innerIdxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
        :: ⟨0, .Lopn [.reg innerCtr] (withWidthTag 64 "MOV") [.reg cntRet]⟩
        :: ((I.zeroTripGuard innerCtr innerTop innerEnd).map (⟨0, ·⟩)
              ++ [ ⟨0, .Llabel .internal innerTop⟩ ]))
  -- Inner body copy + accumulator feedback.
  ++ bodyW ++ feedback
  -- Inner index advance, counter down, inner back-edge.
  ++ (⟨0, .Lopn [.reg innerIdxReg] (withWidthTag 64 "ADD") [.reg innerIdxReg, .imm 1]⟩
        :: ⟨0, .Lopn [.reg innerCtr] (withWidthTag 64 "SUB") [.reg innerCtr, .imm 1]⟩
        :: ((I.loopGuard innerCtr innerTop).map (⟨0, ·⟩)
              ++ [ ⟨0, .Llabel .internal innerEnd⟩ ]))
  -- Outer index advance, counter down, invariant touches, outer back-edge.
  ++ [ ⟨0, .Lopn [.reg outerIdxReg] (withWidthTag 64 "ADD") [.reg outerIdxReg, .imm 1]⟩
     , ⟨0, .Lopn [.reg outerCtr] (withWidthTag 64 "SUB") [.reg outerCtr, .imm 1]⟩ ]
  ++ outerInvTouch
  ++ ((I.loopGuard outerCtr outerTop).map (⟨0, ·⟩) ++ [ ⟨0, .Llabel .internal outerEnd⟩ ])

/-- The inline **do-while** `Lcmd` for one `whileNz` node at depth `d` — the
    `Lcmd` image of A3's `whileLinstrRM top gReg [] (body ++ tail)` shape
    (`Llabel top; body; guard-compute; Lcond NZ top`, the
    `TranslateDialectDataWhile.rolledWhileNz` emission): seed the accumulator,
    the up-counting index and the countdown counter (`MOV Lctr<d>, guardOp` — a
    runtime register read), then ONE body copy, the accumulator feedback, the
    index advance, the counter decrement (the body's own `n -= 1` of the
    countdown idiom), the invariant touches, and the **bottom-test** back-edge
    `CMP Lctr,0; Lcond NZ top`. Identical to `forLoopLcmdNRt` MINUS the zero-trip
    top guard (`CMP;Lcond Z endL` and the `endL` label): the body runs at least
    once — a do-while, not a top-guarded counted loop. -/
def whileLcmdNz (d : Nat) (accReg : String) (initOp guardOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) (I : IsaData := x86Data) : Lcmd :=
  let idxReg := loopIdx d
  let invRegs : List String := invOps.filterMap (fun o =>
    match o with | .reg n => some n | _ => none)
  let (bodyW, retReg) := loopBodyWalkN d accReg idxReg invRegs immSlotMap update
                            (2 + invTys.length)
  let feedback : Lcmd :=
    if retReg == accReg then []
    else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg retReg]⟩]
  let ctr := loopCtr d
  let top : LLabel := d
  let invTouch : Lcmd := invRegs.map (fun r =>
    ⟨0, I.invTouch ctr r⟩)
  [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
  , ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [guardOp]⟩
  , ⟨0, .Llabel .internal top⟩ ]
  ++ bodyW ++ feedback
  ++ [ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "ADD") [.reg idxReg, .imm 1]⟩
     , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ ]
  ++ invTouch
  ++ (I.loopGuard ctr top).map (⟨0, ·⟩)

/-! ### 3b⁗′. Lowering the block-body runtime loop (`forLoopBlock`)

The block-body loop's per-iteration body is a *recursive* `ComL` (not a
straight-line `Com`), so its walk `comLLoopBodyWalk` must handle nested loop
nodes — it is the `comLToBody` analogue scoped to a loop body: `.var` binders use
the disjoint `loopReg d` namespace and the three roles (accumulator/index/
invariants) resolve via `loopResolveVarN`, exactly as `loopBodyWalkN`; a nested
loop node splices the corresponding `forLoopLcmd*` frame at a **fresh disjoint
depth** `nestBlockLoopD`; the terminal `.ret` returns the feedback register (the
caller emits the accumulator feedback `MOV`), NOT an `Lret`. The frame around the
one body copy (`blockLoopFrame`) is exactly `forLoopLcmdNRt`'s runtime back-edge
(seed/index/counter, zero-trip guard, `Lctr`/`CMP`/`Lcond NZ` back-edge). -/

/-- A fresh, disjoint loop depth for a nested loop node sitting at body position
    `curDepth` inside a `forLoopBlock` body at outer depth `d`.

    **Positional (mixed-radix) encoding, not additive.** The old
    `d + 0x1000·(curDepth+1)` was *additive along the nesting path*, so at 3-deep
    nesting a two-step path (curDepths `a` then `b`) landed on
    `d + 0x1000·(a+b+2)`, colliding with a one-step sibling at curDepth
    `c = a+b+1` — two distinct nesting paths get the SAME top label, and the
    assembler rejects the duplicate `.Llabel`. This surfaces only at 3-deep
    nesting (MAYO's whole-solve `pcol × row × dot`); 1- and 2-deep never trigger it.

    The fix is a base-`BASE` positional numeral: `d' = (d+1)·BASE + (curDepth+1)·K`.
    Along a nesting path the successive `curDepth` digits become the low-order
    positions of a mixed-radix number whose most-significant part is the outer
    `d`, so **distinct nesting paths give distinct values** (the map
    `d ↦ (d+1)·BASE + digit` is injective while `digit < BASE`: `digit =
    d' mod BASE`, `d+1 = d' div BASE`). The `(d+1)` (not `d`) lifts every nested
    label to `≥ BASE`, keeping it clear of the top-level loops' labels (their
    `d = curDepth < BASE`). The per-position stride `K = 8` leaves a gap after
    each label so a node that consumes two consecutive slots (the nested
    `forLoopNRtNested`, which uses `d'` and `d'+1`) cannot alias the next
    sibling's top label.

    `BASE = 0x400` (1024), `K = 8`. Ranges for the covered fragment
    (top-level bindings `N < 1024`, body positions `curDepth < 127`, outer
    top-level depth `C0 < 1022`): every nested top label stays `< 0x40000000`
    (max at 3-deep ≈ `(C0+1)·1024²` ≈ 2.6·10⁸ ≪ 2³⁰), so it stays disjoint from
    every loop's zero-trip guard band `endL = d' + 0x40000000` (`≥ 2³⁰`). MAYO's
    3-deep nest with ≤ ~19 body phases sits far inside all three bounds. -/
def nestBlockLoopD (d curDepth : Nat) : Nat := (d + 1) * 0x400 + (curDepth + 1) * 8

/-- The runtime back-edge **frame** around one pre-walked loop-body copy `bodyW`
    (result in `retReg`): seed the accumulator/index/counter, a zero-trip top
    guard on the runtime `countOp`, the loop label, the body copy, the
    accumulator feedback, the index advance, the counter decrement, the
    invariant-base touches and the `Lctr`/`CMP`/`Lcond NZ` back-edge. Byte-equal
    to `forLoopLcmdNRt`'s frame — factored out so both `forLoopLcmdNRt` (with a
    `loopBodyWalkN` body) and `forLoopBlockLcmd` (with a `comLLoopBodyWalk` body)
    share one back-edge shape. -/
def blockLoopFrame (d : Nat) (accReg idxReg ctr : String)
    (initOp countOp : LOperand) (invRegs : List String)
    (bodyW : Lcmd) (retReg : String) (I : IsaData := x86Data) : Lcmd :=
  let feedback : Lcmd :=
    if retReg == accReg then []
    else [⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [.reg retReg]⟩]
  let top : LLabel := d
  let endL : LLabel := d + 0x40000000
  let invTouch : Lcmd := invRegs.map (fun r =>
    ⟨0, I.invTouch ctr r⟩)
  [ ⟨0, .Lopn [.reg accReg] (withWidthTag 64 "MOV") [initOp]⟩
  , ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "MOV") [.imm 0]⟩
  , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "MOV") [countOp]⟩ ]
  ++ (I.zeroTripGuard ctr top endL).map (⟨0, ·⟩)
  ++ [ ⟨0, .Llabel .internal top⟩ ]
  ++ bodyW ++ feedback
  ++ [ ⟨0, .Lopn [.reg idxReg] (withWidthTag 64 "ADD") [.reg idxReg, .imm 1]⟩
     , ⟨0, .Lopn [.reg ctr] (withWidthTag 64 "SUB") [.reg ctr, .imm 1]⟩ ]
  ++ invTouch
  ++ ((I.loopGuard ctr top).map (⟨0, ·⟩) ++ [ ⟨0, .Llabel .internal endL⟩ ])

/-- Walk a `forLoopBlock`'s recursive loop **body** `ComL` at outer depth `d`
    into one single-iteration `Lcmd` plus its result register name. Mirrors
    `loopBodyWalkN` for `.var`/`.ret`, but a nested loop node is lowered by
    splicing the matching `forLoopLcmd*` frame at a fresh disjoint depth
    (`nestBlockLoopD`), threading the outer loop's roles into the nested node's
    resolved operands. On a straight-line body (`.var`/`.ret` only) this is
    byte-identical to `loopBodyWalkN`, so a `forLoopBlock` with a straight-line
    body lowers exactly like `forLoopNRt`. -/
def comLLoopBodyWalk (immSlotMap : ImmSlotMap) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    ComL Γ t → (d : Nat) → (accReg idxReg : String) → (invRegs : List String) →
    (curDepth : Nat) → (I : IsaData := x86Data) → (Lcmd × String)
  | _, _, .ret v, d, accReg, idxReg, invRegs, curDepth, _ =>
      ([], match loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap v with
            | .reg n => n
            | .imm m => toString m
            | .arr b i => b ++ "[" ++ toString i ++ "]"
            | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]")
  | _, _, .var e body, d, accReg, idxReg, invRegs, curDepth, I =>
      let (rest, ret) := comLLoopBodyWalk immSlotMap body d accReg idxReg invRegs (curDepth + 1) I
      (⟨0, opToLinstrR e.op (loopReg d curDepth)
            (loopExprArgsN d accReg idxReg invRegs curDepth immSlotMap e)⟩ :: rest, ret)
  | _, _, .forLoop loop init body, d, accReg, idxReg, invRegs, curDepth, I =>
      let d' := nestBlockLoopD d curDepth
      let initOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap init
      let inner := forLoopLcmd d' (loopReg d curDepth) initOp loop immSlotMap I
      let (rest, ret) := comLLoopBodyWalk immSlotMap body d accReg idxReg invRegs (curDepth + 1) I
      (inner ++ rest, ret)
  | _, _, .forLoopN loop init invs body, d, accReg, idxReg, invRegs, curDepth, I =>
      let d' := nestBlockLoopD d curDepth
      let initOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap init
      let invOps := loopExprArgsHVN d accReg idxReg invRegs curDepth immSlotMap invs
      let inner := forLoopLcmdN d' (loopReg d curDepth) initOp loop invOps immSlotMap I
      let (rest, ret) := comLLoopBodyWalk immSlotMap body d accReg idxReg invRegs (curDepth + 1) I
      (inner ++ rest, ret)
  | _, _, .forLoopNRt update count init invs body, d, accReg, idxReg, invRegs, curDepth, I =>
      let d' := nestBlockLoopD d curDepth
      let initOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap init
      let countOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap count
      let invOps := loopExprArgsHVN d accReg idxReg invRegs curDepth immSlotMap invs
      let inner :=
        forLoopLcmdNRt d' (loopReg d curDepth) initOp countOp update invOps immSlotMap I
      let (rest, ret) := comLLoopBodyWalk immSlotMap body d accReg idxReg invRegs (curDepth + 1) I
      (inner ++ rest, ret)
  | _, _, .forLoopNRtNested innerCount innerUpdate outerCount init invs body,
      d, accReg, idxReg, invRegs, curDepth, I =>
      let d' := nestBlockLoopD d curDepth
      let initOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap init
      let outerCountOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap outerCount
      let invOps := loopExprArgsHVN d accReg idxReg invRegs curDepth immSlotMap invs
      let inner := forLoopLcmdNRtNested d' (loopReg d curDepth) initOp outerCountOp
                      innerCount innerUpdate invOps immSlotMap I
      let (rest, ret) := comLLoopBodyWalk immSlotMap body d accReg idxReg invRegs (curDepth + 1) I
      (inner ++ rest, ret)
  | _, _, .whileNz update guard init invs body, d, accReg, idxReg, invRegs, curDepth, I =>
      let d' := nestBlockLoopD d curDepth
      let initOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap init
      let guardOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap guard
      let invOps := loopExprArgsHVN d accReg idxReg invRegs curDepth immSlotMap invs
      let inner :=
        whileLcmdNz d' (loopReg d curDepth) initOp guardOp update invOps immSlotMap I
      let (rest, ret) := comLLoopBodyWalk immSlotMap body d accReg idxReg invRegs (curDepth + 1) I
      (inner ++ rest, ret)
  | _, _, .forLoopBlock loopBody count init invs body, d, accReg, idxReg, invRegs, curDepth, I =>
      let d' := nestBlockLoopD d curDepth
      let initOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap init
      let countOp := loopResolveVarN d accReg idxReg invRegs curDepth immSlotMap count
      let invOps := loopExprArgsHVN d accReg idxReg invRegs curDepth immSlotMap invs
      let invRegs' : List String := invOps.filterMap (fun o =>
        match o with | .reg n => some n | _ => none)
      let (bw, br) := comLLoopBodyWalk immSlotMap loopBody d' (loopReg d curDepth) (loopIdx d')
                        invRegs' (2 + invOps.length) I
      let inner := blockLoopFrame d' (loopReg d curDepth) (loopIdx d') (loopCtr d')
                      initOp countOp invRegs' bw br I
      let (rest, ret) := comLLoopBodyWalk immSlotMap body d accReg idxReg invRegs (curDepth + 1) I
      (inner ++ rest, ret)

/-- The inline block-body runtime-loop `Lcmd` for one `forLoopBlock` node at depth
    `d`: the runtime back-edge frame (`blockLoopFrame` — identical to
    `forLoopLcmdNRt`) around ONE copy of the recursively-lowered loop body
    (`comLLoopBodyWalk`, which may itself carry inner back-edges). On a
    straight-line `loopBody` this is byte-identical to `forLoopLcmdNRt`; with a
    nested loop node in the body it emits nested back-edges. -/
def forLoopBlockLcmd (d : Nat) (accReg : String) (initOp countOp : LOperand)
    {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (loopBody : ComL (accTy :: .reg 64 :: invTys) accTy)
    (invOps : List LOperand) (immSlotMap : ImmSlotMap) (I : IsaData := x86Data) : Lcmd :=
  let idxReg := loopIdx d
  let invRegs : List String := invOps.filterMap (fun o =>
    match o with | .reg n => some n | _ => none)
  let (bodyW, retReg) := comLLoopBodyWalk immSlotMap loopBody d accReg idxReg invRegs
                            (2 + invTys.length) I
  blockLoopFrame d accReg idxReg (loopCtr d) initOp countOp invRegs bodyW retReg I

/-- Walk a `ComL`, producing the `Lcmd` body. The `.var`/`.ret` arms are
    identical to `comToBody` (so a loop-free `ComL` emits the same straight-line
    body); the `.forLoop` arm splices `forLoopLcmd` (the inline back-edge) into
    the chain, leaving the loop result in `regName curDepth` for the continuation.
    Additive: a loop-free program is byte-identical to its `comToBody` image. -/
def comLToBody (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    ComL Γ t → (curDepth : Nat) → (I : IsaData := x86Data) → Lcmd
  | _, _, .ret _, _, _ => [⟨0, .Lret⟩]
  | _, _, .var e body, curDepth, I =>
      ⟨0, opToLinstrR e.op (regName curDepth)
            (exprArgs curDepth nArgs argNames immSlotMap e)⟩
        :: comLToBody nArgs argNames immSlotMap body (curDepth + 1) I
  | _, _, .forLoop loop init body, curDepth, I =>
      forLoopLcmd curDepth (regName curDepth)
          (resolveVar curDepth nArgs argNames immSlotMap init) loop immSlotMap I
        ++ comLToBody nArgs argNames immSlotMap body (curDepth + 1) I
  | _, _, .forLoopN loop init invs body, curDepth, I =>
      -- Resolve the accumulator seed and every invariant base against the
      -- enclosing context (the loop body's index is internal: `loopIdx curDepth`).
      -- A loop body that issues a leaf call (`extCall`/`callN`) is lowered with
      -- `forLoopLcmdNCall` (a real `Lcall`); a call-free body takes
      -- `forLoopLcmdN` (the `CALL:` shadow path) and is byte-identical.
      (if comBodyHasCall loop.update then
          forLoopLcmdNCall curDepth (regName curDepth)
            (resolveVar curDepth nArgs argNames immSlotMap init) loop
            (exprArgsHV curDepth nArgs argNames immSlotMap invs) immSlotMap I
        else
          forLoopLcmdN curDepth (regName curDepth)
            (resolveVar curDepth nArgs argNames immSlotMap init) loop
            (exprArgsHV curDepth nArgs argNames immSlotMap invs) immSlotMap I)
        ++ comLToBody nArgs argNames immSlotMap body (curDepth + 1) I
  | _, _, .forLoopNRt update count init invs body, curDepth, I =>
      -- Runtime-trip loop: the counter is seeded from the resolved `count`
      -- operand (`MOV Lctr, <countReg>`); the accumulator seed and invariant
      -- bases are resolved against the enclosing context exactly as `forLoopN`.
      forLoopLcmdNRt curDepth (regName curDepth)
          (resolveVar curDepth nArgs argNames immSlotMap init)
          (resolveVar curDepth nArgs argNames immSlotMap count) update
          (exprArgsHV curDepth nArgs argNames immSlotMap invs) immSlotMap I
        ++ comLToBody nArgs argNames immSlotMap body (curDepth + 1) I
  | _, _, .forLoopNRtNested innerCount innerUpdate outerCount init invs body, curDepth, I =>
      -- Nested runtime loop: an inner runtime loop (top label `curDepth+1`) inside
      -- the outer runtime loop (top label `curDepth`), with the inner trip
      -- recomputed per outer pass (`nestCountWalk innerCount`). Two nested
      -- back-edges — the `Lcmd` image of `ggmProg`.
      forLoopLcmdNRtNested curDepth (regName curDepth)
          (resolveVar curDepth nArgs argNames immSlotMap init)
          (resolveVar curDepth nArgs argNames immSlotMap outerCount)
          innerCount innerUpdate
          (exprArgsHV curDepth nArgs argNames immSlotMap invs) immSlotMap I
        ++ comLToBody nArgs argNames immSlotMap body (curDepth + 1) I
  | _, _, .whileNz update guard init invs body, curDepth, I =>
      -- Data-dependent do-while: the countdown counter is seeded from the
      -- resolved `guard` operand and bottom-tested (`whileLcmdNz` — the
      -- `whileLinstrRM` image, no zero-trip top guard).
      whileLcmdNz curDepth (regName curDepth)
          (resolveVar curDepth nArgs argNames immSlotMap init)
          (resolveVar curDepth nArgs argNames immSlotMap guard) update
          (exprArgsHV curDepth nArgs argNames immSlotMap invs) immSlotMap I
        ++ comLToBody nArgs argNames immSlotMap body (curDepth + 1) I
  | _, _, .forLoopBlock loopBody count init invs body, curDepth, I =>
      -- Block-body runtime loop: the runtime back-edge frame around ONE copy of
      -- the recursively-lowered `loopBody` (`forLoopBlockLcmd` →
      -- `comLLoopBodyWalk`), which may itself carry inner back-edges — the general
      -- multi-phase / arbitrary-depth loop body. Seed/count/invariant resolution
      -- against the enclosing context is exactly as `forLoopNRt`.
      forLoopBlockLcmd curDepth (regName curDepth)
          (resolveVar curDepth nArgs argNames immSlotMap init)
          (resolveVar curDepth nArgs argNames immSlotMap count)
          loopBody
          (exprArgsHV curDepth nArgs argNames immSlotMap invs) immSlotMap I
        ++ comLToBody nArgs argNames immSlotMap body (curDepth + 1) I

/-- The register name of a `ComL`'s final return value (the binder the terminal
    `.ret` points at). Skips both `.var` and `.forLoop` binders. -/
def comLRetReg (nArgs : Nat) (argNames : Nat → String) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    ComL Γ t → (curDepth : Nat) → String
  | _, _, .ret v, curDepth =>
      (match resolveVar curDepth nArgs argNames (fun _ => none) v with
        | .reg n => n
        | .arr b i => b ++ "[" ++ toString i ++ "]"
        | .imm n => toString n
        | .arrIdx b i s => b ++ "[" ++ i ++ "*" ++ toString s ++ "]")
  | _, _, .var _ body, curDepth => comLRetReg nArgs argNames body (curDepth + 1)
  | _, _, .forLoop _ _ body, curDepth =>
      comLRetReg nArgs argNames body (curDepth + 1)
  | _, _, .forLoopN _ _ _ body, curDepth =>
      comLRetReg nArgs argNames body (curDepth + 1)
  | _, _, .forLoopNRt _ _ _ _ body, curDepth =>
      comLRetReg nArgs argNames body (curDepth + 1)
  | _, _, .forLoopNRtNested _ _ _ _ _ body, curDepth =>
      comLRetReg nArgs argNames body (curDepth + 1)
  | _, _, .whileNz _ _ _ _ body, curDepth =>
      comLRetReg nArgs argNames body (curDepth + 1)
  | _, _, .forLoopBlock _ _ _ _ body, curDepth =>
      comLRetReg nArgs argNames body (curDepth + 1)

/-- Build the `lfundef` for a `ComL` over argument context `Γ` — the loop-aware
    analogue of `comToLfundef`. The body is `comLToBody`, so a loop-free `ComL`
    yields the same `lfundef` as `comToLfundef` on its `Com` image. -/
def ComL.toLfundef {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t)
    (immSlotMap : ImmSlotMap := fun _ => none) (I : IsaData := x86Data) : Lfundef :=
  let nArgs := Γ.length
  { lfd_info := 0
    lfd_align := 1
    lfd_tyin := Γ.reverse.map tyWidth
    lfd_arg := (List.range nArgs).map argName
    lfd_body := comLToBody nArgs argName immSlotMap c nArgs I
    lfd_tyout := [tyWidth t]
    lfd_res := [comLRetReg nArgs argName c nArgs]
    lfd_export := true
    lfd_callee_saved := []
    lfd_stk_max := 0
    lfd_frame_size := 0
    lfd_align_args := [] }

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
