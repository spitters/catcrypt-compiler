/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhileNode
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectPhaseCompose

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# Recursive `LowCT → ComL.forLoopBlock` lowering (nested loops without unrolling)

Every existing `LowCT → ComL` front (`rolledForLoopN`, `rolledForLoopNRt`,
`rolledWhileNzComL`) front-compiles a **straight-line** loop body: the body flows
through `frontLoopBodyJ`, which produces a `Com jasminDialect` — and a loop is not
a `JasminOp`, so a body that itself *contains* an inner `RWhileNz`/`RFor` cannot be
produced by them.  They can only unroll an inner sweep straight-line.

`ComL.forLoopBlock` (`JasminLprogExport`) is the loop node whose per-iteration body
is a **recursive** `ComL (accTy :: .reg 64 :: invTys) accTy` — so one iteration may
itself carry an inner loop NODE to arbitrary depth.  The node, its denotation, and
its lowering (`forLoopBlockLcmd` → `comLLoopBodyWalk`, one body copy + real
back-edges) already exist; what was missing is the **lowering that puts a nested
LowCT loop into it**: a `LowCT → ComL.forLoopBlock` front whose outer arm emits an
inner loop node instead of unrolling.

This module builds that lowering — `lowerNestedLoop` — and proves it denotes to the
nested fold of its body.

## The lowering

`lowerNestedLoop` composes the front at two levels with **no `Com`↔`ComL`
embedding**:

* the **inner** (leaf) loop is front-compiled by the SAME verified
  `rolledWhileNzComL`, but hosted at the *outer block's loop-body context*
  `Γblk = mapCtx (accCTy :: .sword 64 :: outerInvCTys)
        = mapTy accCTy :: .reg 64 :: outerInvCTys.map mapTy`.
  Because that is *definitionally* the `forLoopBlock` loop-body context
  `accTy :: .reg 64 :: invTys` (`accTy := mapTy accCTy`,
  `invTys := outerInvCTys.map mapTy`), the front's output
  `ComL Γblk (mapTy accCTy)` — a `whileNz` / do-while NODE, its own inner
  index at slot `1` — IS the recursive body the block node wants;
* the **outer** loop wraps that inner node with `ComL.forLoopBlock`, threading the
  outer trip count / accumulator seed / invariants.  The outer loop's index binder
  (`Γblk` slot `1`) is in scope inside the inner node, so an inner sweep that
  depends on the outer index (e.g. MAYO's `A[row·AC + j]`) reaches it as an inner
  invariant.

The result is a `forLoopBlock`-over-`whileNz` `ComL`: two bottom-test
back-edges (outer + inner), no unrolling.  Nesting is recursive — feed a
`lowerNestedLoop` result as the inner of another `lowerNestedLoop` for 3-deep, and
so on (the outer block context is uniform in shape at every level).

## Denote-preservation

`lowerNestedLoop_denote`: the lowered nested loop denotes to the `count`-fold of
the inner node's own `ComL.denote` — the outer fold of the inner denotation, i.e.
the **nested (double) fold** of the body.  Composed with
`rolledWhileNzComL_denote` (inner node = inner `JLoopBodyN.denote` fold) this is the
literal double fold of the front-compiled per-iteration update.  Proved
structurally (`rfl`); axioms ⊆ {propext, Classical.choice, Quot.sound}.

## Count-from-state sweeps (§6–§8)

§4/§5's combinators source the inner trip/guard from a **pre-set count register**
(`innerGuard` / `guard` / `count` `Var`s).  §6's `rolledForLoopNRtCountedCont` lifts
the `ComL.forLoopNRtNested` `countBody` mechanism onto this front: the inner trip is a
**`LowCT` `SExpr` computed from the outer loop index**, front-compiled into the node's
`innerCount` (re-evaluated per outer pass by `JLoopBodyN.innerTripAtC`), so the inner
sweep runs `f(outerIdx)` times — the shape of MAYO's `efBody` `rc`/`rc4`/`rc6` sweeps
(`rc = up-lb+1`, …, `f(pcol)`).  `rolledForLoopNRtCountedCont_denote` proves
`denote = cont` on the state-dependent double fold `JLoopBodyN.nestedDenote` (same
axiom footprint as the committed nested front).  §7 is the triangular demo (inner
trip = the outer index, `Σ_{i<N} i`); §8 splices a counted sweep mid-chain (a further
phase runs on its result).

Invoke (in-model gate):
  lake env lean CatCrypt/Crypto/SecureCompilation/VIR/RecursiveForLoopBlockFront.lean
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.RecursiveForLoopBlockFront

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhileNode
  (rolledWhileNzComL rolledWhileNzComL_denote seqAll)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop (frontLoopBodyJ)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectPhaseCompose
  (rolledForLoopNCont rolledForLoopNCont_denote
   rolledForLoopNRtNestedCont rolledForLoopNRtNestedCont_denote
   rolledForLoopNRtNestedCont_ret_here)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
  (rolledForLoopNRtNested)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)

/-! ## 1. The recursive lowering -/

/-- Lower a **nested** LowCT loop — an outer runtime-trip loop whose per-iteration
    body is itself an inner `RWhileNz` sweep — into a
    `ComL.forLoopBlock`-over-`ComL.whileNz`, with **no unrolling** of either level.

    * the inner (leaf) loop's straight-line body `innerBody` front-compiles through
      the verified `rolledWhileNzComL`, hosted at the outer block's loop-body
      context `mapCtx (accCTy :: .sword 64 :: outerInvCTys)`; its output is a
      `whileNz` NODE — the recursive `ComL` body the block node carries;
    * the outer loop wraps it with `ComL.forLoopBlock`, threading `outerCount`
      (runtime trips), `outerInit` (accumulator seed), and `outerInvs`.

    The inner node's guard/init/invariant `Var`s live in the outer block context,
    so the outer loop index (that context's slot `1`) is available to the inner
    sweep.  `none` iff the inner front declines. -/
def lowerNestedLoop {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {outerInvCTys innerInvCTys : Ctx}
    (vmInner : VarMap (accCTy :: .sword 64 :: innerInvCTys)) (innerAccName : String)
    (innerBody : LowCT)
    (innerGuard : Ctxt.Var (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) (JasminTy.reg 64))
    (innerInit  : Ctxt.Var (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) (mapTy accCTy))
    (innerInvs  : HVector
      (fun ty => Ctxt.Var (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) ty)
      (innerInvCTys.map mapTy))
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (outerInit  : Ctxt.Var Γouter (mapTy accCTy))
    (outerInvs  : HVector (fun ty => Ctxt.Var Γouter ty) (outerInvCTys.map mapTy)) :
    Option (ComL Γouter (mapTy accCTy)) :=
  match rolledWhileNzComL
          (Γouter := mapCtx (accCTy :: .sword 64 :: outerInvCTys))
          (accCTy := accCTy) (invCTys := innerInvCTys)
          vmInner innerAccName innerBody innerGuard innerInit innerInvs with
  | some inner => some (ComL.forLoopBlock inner outerCount outerInit outerInvs (.ret .here))
  | none => none

/-! ## 2. Denote-preservation: the nested fold of the body

`lowerNestedLoop` denotes to the `outerCount`-fold of the **inner node's own**
`ComL.denote` — threading the accumulator, passing the outer trip index as the
`.reg 64` binder and the outer invariants after it.  This is exactly the outer
fold of the inner denotation (the nested/double fold), the `forLoopBlock` fold with
a recursive body in place of a straight-line `stepC`. -/

/-- **Denote-preservation.** When the inner front produces `inner`, the lowered
    nested loop denotes to the `outerCount`-fold of `inner`'s own `ComL.denote` —
    the outer fold of the inner denotation. Structural (`rfl`). -/
theorem lowerNestedLoop_denote {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {outerInvCTys innerInvCTys : Ctx}
    (vmInner : VarMap (accCTy :: .sword 64 :: innerInvCTys)) (innerAccName : String)
    (innerBody : LowCT)
    (innerGuard : Ctxt.Var (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) (JasminTy.reg 64))
    (innerInit  : Ctxt.Var (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) (mapTy accCTy))
    (innerInvs  : HVector
      (fun ty => Ctxt.Var (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) ty)
      (innerInvCTys.map mapTy))
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (outerInit  : Ctxt.Var Γouter (mapTy accCTy))
    (outerInvs  : HVector (fun ty => Ctxt.Var Γouter ty) (outerInvCTys.map mapTy))
    {inner : ComL (mapCtx (accCTy :: .sword 64 :: outerInvCTys)) (mapTy accCTy)}
    (hinner : rolledWhileNzComL
          (Γouter := mapCtx (accCTy :: .sword 64 :: outerInvCTys))
          (accCTy := accCTy) (invCTys := innerInvCTys)
          vmInner innerAccName innerBody innerGuard innerInit innerInvs = some inner)
    (V : Ctxt.Valuation Γouter) :
    (lowerNestedLoop vmInner innerAccName innerBody innerGuard innerInit innerInvs
        outerCount outerInit outerInvs).map (fun c => ComL.denote c V)
      = some
        ((List.range (outerCount.lookup V).toNat).foldl
          (fun acc t =>
            ComL.denote inner
              (.cons acc (.cons (BitVec.ofNat 64 t) (Expr.lookupArgs outerInvs V))))
          (outerInit.lookup V)) := by
  unfold lowerNestedLoop
  rw [hinner]
  rfl

/-! ## 3. A 2-deep demo: an inner accumulate sweep inside an outer loop

The inner leaf body is `ai := a[idx]; acc2 := acc + ai` — one covered per-iteration
accumulate over the array `a` at the inner up-counter `idx` (reused verbatim from
`TranslateDialectWhileNode.whileBody`).  The outer loop runs that whole inner sweep
`M` times, re-seeding the inner accumulator from the running total each pass — the
`for i in 0..M { for j in 0..n { acc += a[j] } }` shape (MAYO's row × pcol
structure, minus the GF(16) leaf).  `lowerNestedLoop` produces a
`forLoopBlock`-over-`whileNz` `ComL`. -/

/-- Inner leaf body context `[acc, idx, a]` (accumulator, inner index, array). -/
def demoInnerΓ : Ctx := [.sword 64, .sword 64, .memref 3]

/-- Inner leaf body VarMap: `acc ↦ .here`, `idx`, `a`. -/
def demoInnerVm : VarMap demoInnerΓ :=
  (((VarMap.empty.bind (t := .memref 3) "a").bind
      (t := .sword 64) "idx").bind (t := .sword 64) "acc")

/-- The covered inner leaf body: `ai := a[idx]; acc2 := acc + ai`. -/
def demoInnerBody : LowCT := seqAll [
  .RArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes 24⟩ "idx",
  .RScalarSetExpr "acc2" (.SAdd (.SVar "acc") (.SVar "ai")) ]

/-- Outer (kernel-argument) context `[M (outer count), acc, a, n (inner count)]`. -/
def demoΓouter : Ctxt jasminDialect :=
  [.reg 64, .reg 64, .stackArr 64 3, .reg 64]

/-- The front-generated 2-deep nested loop.  Outer block context is
    `mapCtx (.sword 64 :: .sword 64 :: [.memref 3, .sword 64])
      = [reg 64 (acc), reg 64 (outerIdx), stackArr 64 3 (a), reg 64 (n)]`; the inner
    `whileNz`'s guard is `n` (slot 3), init is `acc` (slot 0), its one invariant is
    `a` (slot 2).  The outer `forLoopBlock` trips `M` (slot 0 of `demoΓouter`),
    seeds `acc` (slot 1), invariants `a` (slot 2), `n` (slot 3). -/
def demoNested : Option (ComL demoΓouter (.reg 64)) :=
  lowerNestedLoop
    (Γouter := demoΓouter) (accCTy := .sword 64)
    (outerInvCTys := [.memref 3, .sword 64]) (innerInvCTys := [.memref 3])
    demoInnerVm "acc2" demoInnerBody
    (innerGuard := .there (.there (.there .here)))          -- n  (outer-block slot 3)
    (innerInit  := .here)                                   -- acc (outer-block slot 0)
    (innerInvs  := .cons (.there (.there .here)) .nil)      -- a  (outer-block slot 2)
    (outerCount := .here)                                   -- M
    (outerInit  := .there .here)                            -- acc
    (outerInvs  := .cons (.there (.there .here))            -- a
                   (.cons (.there (.there (.there .here))) .nil))  -- n

/-- **The front generates the nested loop** (the inner leaf body front-compiles). -/
theorem demoNested_isSome : demoNested.isSome := by native_decide

/-- **The outer spine is the block-body loop node** `forLoopBlock`. -/
theorem demoNested_is_forLoopBlock_node :
    (demoNested.map (fun c => match c with
      | .forLoopBlock _ _ _ _ _ => true
      | _ => false)) = some true := by native_decide

/-- **The inner (recursive) body is a `whileNz` do-while NODE**, not an
    unrolled straight-line chain — the block node carries a real inner loop. -/
theorem demoNested_inner_is_whileNz_node :
    (demoNested.map (fun c => match c with
      | .forLoopBlock (.whileNz _ _ _ _ _) _ _ _ _ => true
      | _ => false)) = some true := by native_decide

/-- Outer valuation: `M` outer trips, `acc = 0`, `a = [10, 20, 30]`, `n` inner
    trips. -/
def demoVal (M n : Nat) : Ctxt.Valuation demoΓouter :=
  .cons (BitVec.ofNat 64 M)
    (.cons (0 : BitVec 64)
      (.cons (![10#64, 20#64, 30#64] : Fin 3 → BitVec 64)
        (.cons (BitVec.ofNat 64 n) .nil)))

/-- The independent **double-fold** spec: `M` outer passes, each adding
    `Σ_{j<n} a[j]` to the running accumulator. -/
def demoDoubleRef (M n : Nat) : Nat :=
  (List.range M).foldl
    (fun acc _ =>
      (List.range n).foldl (fun b j => b + [10, 20, 30].getD j 0) acc)
    0

/-- **denote = double fold.**  At `M = 2` outer trips and `n = 3` inner trips, the
    front-generated `forLoopBlock`-over-`whileNz` denotes to
    `2 · (10+20+30) = 120` — the outer fold of the inner accumulate. -/
theorem demoNested_denote_double :
    (demoNested.map (fun c => BitVec.toNat (ComL.denote c (demoVal 2 3))))
      = some (demoDoubleRef 2 3) := by native_decide

/-- **Same program, different trip counts** — the trip counts are read off the
    seed valuation, not baked in: `M = 3`, `n = 2` → `3 · (10+20) = 90`. -/
theorem demoNested_denote_double' :
    (demoNested.map (fun c => BitVec.toNat (ComL.denote c (demoVal 3 2))))
      = some (demoDoubleRef 3 2) := by native_decide

/-- **Two bottom-test back-edges** (outer + inner): the `comLToBody`
    lowering of the nested loop carries exactly **two** `Lcond NZ` conditional
    jumps — real nested control flow, not an unrolled chain. -/
theorem demoNested_two_backedges :
    (demoNested.map (fun c =>
        let body := comLToBody 4 argName (fun _ => none) c 4
        (body.filter (fun i => match i.li_i with
            | .Lcond (.reg "NZ") _ => true | _ => false)).length == 2))
      = some true := by native_decide

/-- **The inner loop is a bottom-test do-while:** the inner `whileNz`
    contributes its back-edge with no zero-trip top guard of its own — the only
    `Lcond Z` in the lowering is the outer block's counted zero-trip skip (the
    `forLoopBlock` frame), so there is exactly **one** `Lcond Z`, not two. -/
theorem demoNested_inner_dowhile :
    (demoNested.map (fun c =>
        let body := comLToBody 4 argName (fun _ => none) c 4
        (body.filter (fun i => match i.li_i with
            | .Lcond (.reg "Z") _ => true | _ => false)).length == 1))
      = some true := by native_decide

/-- **The lowered nested body ends with `Lret`** — the two loop back-edges are
    interior control flow; the outer continuation's `.ret` is last. -/
theorem demoNested_ends_Lret :
    (demoNested.map (fun c =>
        match (comLToBody 4 argName (fun _ => none) c 4).getLast? with
        | some i => (match i.li_i with | .Lret => true | _ => false)
        | none => false))
      = some true := by native_decide

/-! ## 4. The multi-phase splice: `prefix ; inner-loop ; suffix` in ONE `forLoopBlock`

`lowerNestedLoop` (§1) handles an outer loop whose per-iteration body is a *bare*
inner sweep.  MAYO's real `pcol`/`row` bodies are **multi-phase**: a sequence
`pre-straightline ; sweep₁ ; mid-straightline ; sweep₂ ; post-straightline` per
outer pass.  `ComL` is *already* structurally sequential — every loop node carries a
continuation `body` — so a multi-phase body is a **chain of phase-continuation
combinators** closed by `.ret`, then wrapped once in `ComL.forLoopBlock`.

The two phase kinds this needs:

* an **inner countdown sweep** mid-chain — `rolledWhileNzComLCont`, the `whileNz`
  analogue of `TranslateDialectPhaseCompose.rolledForLoopNRtCont`: a
  front-compiled do-while whose accumulator result is bound at `.here` for the
  caller-supplied continuation `cont`;
* a **straight-line glue phase** — `TranslateDialectPhaseCompose.rolledForLoopNCont`
  at `N = 1`: the front-compiled straight-line body run exactly once over the
  accumulator (the trip index is unused), its result bound at `.here`.  This is
  the `Com jasminDialect → ComL` prefix-embedding, obtained for free from the
  fixed-trip phase combinator at trip count `1` — no hand-authored `Com`.

Chaining `glue(1) → sweep → glue(1) → … → .ret .here` builds the whole multi-phase
`ComL (accTy :: .reg 64 :: invTys) accTy`; `ComL.forLoopBlock` wraps it as the
outer loop's recursive body.  With `accTy = stackArr 64 N` the whole kernel state
(the ~20 scalars + 6 arrays) threads as the one `forLoopMultiAcc` product
accumulator.  §5 exhibits the splice on a `prefix ; sweep ; suffix` GF-flavoured
body; its `denote` equals the sequential composition of the phases. -/

export CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhileNode
  (rolledWhileNzComLCont)

/-- Passing `cont := .ret .here` recovers `rolledWhileNzComL` exactly: the
    continuation-carrying combinator is the primitive and the fixed one is its
    instance. -/
theorem rolledWhileNzComLCont_ret_here {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (guard : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    rolledWhileNzComLCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        vmBody accName body guard init invs (.ret .here)
      = rolledWhileNzComL (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
          vmBody accName body guard init invs := rfl

/-- **While-sweep phase-compose denotation.** When the body front-compiles to
    `update`, the spliced `ComL` denotes to the continuation `cont` evaluated on the
    valuation extended by the countdown fold of `update` (seed `init`, invariants
    `invs`, trip `(guard.lookup V).toNat`) — the sweep runs, its result is bound at
    `.here`, and the next phase runs on it.  Structural (`unfold`; `rw`; `rfl`);
    same axiom footprint as the committed reference `rolledWhileNzComL_denote` /
    `rolledForLoopNRtCont_denote` (`propext`, `Quot.sound` — no
    `Classical.choice`). -/
theorem rolledWhileNzComLCont_denote {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx} {s : JasminTy}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (guard : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s)
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update)
    (V : Ctxt.Valuation Γouter) :
    (rolledWhileNzComLCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        vmBody accName body guard init invs cont).map (fun c => ComL.denote c V)
      = some (ComL.denote cont
          (V.extend (JLoopBodyN.denote ⟨(guard.lookup V).toNat, update⟩
            (Expr.lookupArgs invs V) (init.lookup V)))) := by
  unfold rolledWhileNzComLCont
  rw [hupd]
  rfl

/-! ## 5. A multi-phase splice demo: `prefix ; inner-sweep ; suffix` in ONE block body

The outer loop runs, per pass, a **three-phase** body — `acc += 100` (straight-line
prefix), `for j in 0..n { acc += a[j] }` (an inner countdown sweep), `acc += 1`
(straight-line suffix) — the exact `pre ; sweep ; post` shape of MAYO's `pcol`/`row`
bodies (minus the GF(16) leaf and the extra sweeps).  Every phase is front-compiled:
the two glue phases through `rolledForLoopNCont` at trip `1` (the `Com → ComL`
prefix-embedding), the sweep through `rolledWhileNzComLCont`.  The three chain
through their continuations into ONE `ComL (accTy :: .reg 64 :: invTys) accTy`, which
`ComL.forLoopBlock` wraps as the outer loop's recursive body — nothing hand-authored
at the `Com`/`Lcmd` level. -/

/-- Outer block-body context `[acc, idx, a, n]` (accumulator, outer index, array
    invariant, inner trip-count invariant) — the `accTy :: .reg 64 :: invTys` of the
    `forLoopBlock` node with `accTy = .reg 64`, `invTys = [.stackArr 64 3, .reg 64]`. -/
def spliceΓblk : Ctxt jasminDialect := [.reg 64, .reg 64, .stackArr 64 3, .reg 64]

/-- Glue body context `[acc, gidx]` (accumulator, unused 1-trip index). -/
def spliceGlueVm : VarMap [CryptoTy.sword 64, CryptoTy.sword 64] :=
  (VarMap.empty.bind (t := .sword 64) "gidx").bind (t := .sword 64) "acc"

/-- Straight-line prefix glue `acc += 100`. -/
def splicePrefixBody : LowCT :=
  seqAll [.RScalarSetExpr "acc2" (.SAdd (.SVar "acc") (.SLit 100))]

/-- Straight-line suffix glue `acc += 1`. -/
def spliceSuffixBody : LowCT :=
  seqAll [.RScalarSetExpr "acc2" (.SAdd (.SVar "acc") (.SLit 1))]

/-- Kernel (outer) context `[M (outer count), acc seed, a, n]`. -/
def spliceΓkern : Ctxt jasminDialect := [.reg 64, .reg 64, .stackArr 64 3, .reg 64]

/-- The extended outer-block context after the prefix glue binds its result. -/
abbrev spliceΓ2 : Ctxt jasminDialect := (.reg 64) :: spliceΓblk
/-- The extended outer-block context after the inner sweep binds its result. -/
abbrev spliceΓ3 : Ctxt jasminDialect := (.reg 64) :: spliceΓ2

/-- Suffix glue phase (`acc += 1`), continuation `.ret .here`. -/
def splicePhase3 : Option (ComL spliceΓ3 (.reg 64)) :=
  rolledForLoopNCont (Γouter := spliceΓ3) (accCTy := .sword 64) (invCTys := [])
    1 spliceGlueVm "acc2" spliceSuffixBody
    (init := .here)                                   -- inner-sweep result
    (invs := .nil)
    (cont := .ret .here)

/-- Inner countdown sweep (`for j in 0..n { acc += a[j] }`), continuation = suffix. -/
def splicePhase2 : Option (ComL spliceΓ2 (.reg 64)) :=
  match splicePhase3 with
  | some p3 =>
      rolledWhileNzComLCont (Γouter := spliceΓ2) (accCTy := .sword 64)
        (invCTys := [.memref 3])
        demoInnerVm "acc2" demoInnerBody
        (guard := .there (.there (.there (.there .here))))   -- n  (block slot 4)
        (init := .here)                                      -- prefix-glue result
        (invs := .cons (.there (.there (.there .here))) .nil) -- a (block slot 3)
        (cont := p3)
  | none => none

/-- The whole multi-phase block body: prefix glue → inner sweep → suffix glue → ret.
    ONE `ComL spliceΓblk (.reg 64)`, three front-compiled phases glued only through
    the `ComL` continuations. -/
def spliceBodyChain : Option (ComL spliceΓblk (.reg 64)) :=
  match splicePhase2 with
  | some p2 =>
      rolledForLoopNCont (Γouter := spliceΓblk) (accCTy := .sword 64) (invCTys := [])
        1 spliceGlueVm "acc2" splicePrefixBody
        (init := .here)                                  -- acc (block slot 0)
        (invs := .nil)
        (cont := p2)
  | none => none

/-- The outer loop wraps the multi-phase body with `ComL.forLoopBlock`: a runtime
    outer trip `M`, seeding `acc`, invariants `a`, `n`. -/
def spliceDemo : Option (ComL spliceΓkern (.reg 64)) :=
  match spliceBodyChain with
  | some b =>
      some (ComL.forLoopBlock b
        (count := .here)                                          -- M
        (init := .there .here)                                    -- acc seed
        (invs := .cons (.there (.there .here))                    -- a
                 (.cons (.there (.there (.there .here))) .nil))   -- n
        (.ret .here))
  | none => none

/-- **The three-phase block body front-compiles** (all three phases + the block
    wrapper produced by the front). -/
theorem spliceDemo_isSome : spliceDemo.isSome := by native_decide

/-- **The outer spine is the block-body loop node** whose recursive body's *first*
    phase is a `forLoopN` (the 1-trip prefix glue) — a multi-phase body,
    not a bare inner sweep. -/
theorem spliceDemo_is_block_over_multiphase :
    (spliceDemo.map (fun c => match c with
      | .forLoopBlock (.forLoopN _ _ _ _) _ _ _ _ => true
      | _ => false)) = some true := by native_decide

/-- **The block body splices an inner `whileNz` sweep after the prefix
    glue**: the recursive body is `forLoopN (prefix) … (forLoopN? no — whileNz sweep …)`.
    We witness the sweep node sitting as the prefix glue's continuation. -/
theorem spliceDemo_splices_whileNz :
    (spliceDemo.map (fun c => match c with
      | .forLoopBlock (.forLoopN _ _ _ (.whileNz _ _ _ _ _)) _ _ _ _ => true
      | _ => false)) = some true := by native_decide

/-- Outer valuation: `M` outer trips, `acc = 0`, `a = [10, 20, 30]`, `n` inner
    trips. -/
def spliceVal (M n : Nat) : Ctxt.Valuation spliceΓkern :=
  .cons (BitVec.ofNat 64 M)
    (.cons (0 : BitVec 64)
      (.cons (![10#64, 20#64, 30#64] : Fin 3 → BitVec 64)
        (.cons (BitVec.ofNat 64 n) .nil)))

/-- The independent **sequential-composition** spec: `M` outer passes, each applying
    `acc ↦ (acc + 100) + Σ_{j<n} a[j] + 1` — prefix, then the inner sweep, then the
    suffix, in order. -/
def spliceRef (M n : Nat) : Nat :=
  (List.range M).foldl
    (fun acc _ =>
      let a1 := acc + 100
      let a2 := (List.range n).foldl (fun b j => b + [10, 20, 30].getD j 0) a1
      a2 + 1)
    0

/-- **denote = the sequential composition of the three phases**, folded over the
    outer loop.  At `M = 2`, `n = 3`: `2 · (100 + 60 + 1) = 322` — witnessing that
    the prefix, the inner sweep, and the suffix all ran, in order, per outer pass. -/
theorem spliceDemo_denote_seq :
    (spliceDemo.map (fun c => BitVec.toNat (ComL.denote c (spliceVal 2 3))))
      = some (spliceRef 2 3) := by native_decide

/-- **Same program, different trip counts** — `M = 3`, `n = 2` → `3 · (100+30+1) = 393`;
    both trip counts are read off the seed valuation, not baked in. -/
theorem spliceDemo_denote_seq' :
    (spliceDemo.map (fun c => BitVec.toNat (ComL.denote c (spliceVal 3 2))))
      = some (spliceRef 3 2) := by native_decide

/-- **Four bottom-test back-edges** for the spliced body: the outer block
    loop, the inner countdown sweep, and the two 1-trip glue phases are all counted
    loops, so the `comLToBody` lowering carries exactly **four** `Lcond NZ`
    back-edges — real nested + sequential control flow, no unrolling. -/
theorem spliceDemo_backedges :
    (spliceDemo.map (fun c =>
        let body := comLToBody 4 argName (fun _ => none) c 4
        (body.filter (fun i => match i.li_i with
            | .Lcond (.reg "NZ") _ => true | _ => false)).length == 4))
      = some true := by native_decide

/-! ## 6. `rolledForLoopNRtCountedCont` — a counted sweep whose trip is a **LowCT
    expression computed from the outer loop index**, not a pre-set count register

§4/§5's combinators source their loop trip/guard from a **context-register `Var`**
(a count register the caller must already hold in scope): `lowerNestedLoop`'s inner
`whileNz` reads `innerGuard`, `rolledWhileNzComLCont` reads `guard`,
`TranslateDialectPhaseCompose.rolledForLoopNRtCont` reads `count`.  MAYO's `efBody`
sweeps (`rc`/`rc4`/`rc6`) and `backsubBody`'s (`cc`/`ic2`) have trip counts
**computed from the outer loop index** — `rc = up-lb+1`, `rc4 = ub-lb+1`,
`rc6 = m-lb`, `cc = ko-row+1`, `ic2 = row`, where `lb`/`ub`/`up` are branch-free
clamped functions of the block index `pcol` — so no pre-set register holds them; the
count is a value that must be *materialised* from state each outer pass.

The `ComL.forLoopNRtNested` node already carries exactly that mechanism: its
`innerCount : Com jasminDialect (.reg 64 :: invTys) (.reg 64)` is **re-evaluated per
outer pass** on `[outerIdx, invs]` (`JLoopBodyN.innerTripAtC`), so the inner trip is
`f(outerIdx)`, not a fixed register.  That is what
`TranslateDialectPhaseCompose.rolledForLoopNRtNestedCont` builds, and
`rolledForLoopNRtCountedCont` is the name this module uses for it.

This is the last control shape `efBody`/`backsubBody` need: a nested loop whose
inner trip is a state-dependent computed count. -/

/-- A **counted nested sweep with a caller-supplied continuation** — the
    `TranslateDialectPhaseCompose.rolledForLoopNRtNestedCont` combinator under the
    name this module's counted-sweep clients use.  The inner trip count is a
    `LowCT` expression `countBody` over the outer loop index (+ invariants),
    front-compiled into the `ComL.forLoopNRtNested` `innerCount` slot, which
    `JLoopBodyN.innerTripAtC` re-evaluates per outer pass, so the inner sweep runs
    `f(outerIdx)` times on outer pass `outerIdx` — *not* a pre-set count register. -/
abbrev rolledForLoopNRtCountedCont {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx} {s : JasminTy}
    (vmCount : VarMap (.sword 64 :: invCTys)) (countName : String) (countBody : LowCT)
    (vmBody : VarMap (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (accName : String)
    (updateBody : LowCT)
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s) :
    Option (ComL Γouter s) :=
  rolledForLoopNRtNestedCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
    vmCount countName countBody vmBody accName updateBody outerCount init invs cont

/-- Passing `cont := .ret .here` recovers `rolledForLoopNRtNested` exactly. -/
theorem rolledForLoopNRtCountedCont_ret_here {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (vmCount : VarMap (.sword 64 :: invCTys)) (countName : String) (countBody : LowCT)
    (vmBody : VarMap (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (accName : String)
    (updateBody : LowCT)
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    rolledForLoopNRtCountedCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        vmCount countName countBody vmBody accName updateBody outerCount init invs
        (.ret .here)
      = rolledForLoopNRtNested (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
          vmCount countName countBody vmBody accName updateBody outerCount init invs :=
  rolledForLoopNRtNestedCont_ret_here (Γouter := Γouter) (accCTy := accCTy)
    (invCTys := invCTys) vmCount countName countBody vmBody accName updateBody
    outerCount init invs

/-- **Denote-preservation: the state-dependent double fold.** When both bodies
    front-compile, the counted sweep denotes to the continuation `cont` evaluated on
    the valuation extended by `JLoopBodyN.nestedDenote` — the outer×inner double fold
    whose inner trip at outer pass `jd` is `(innerCount.denote [ofNat jd, invs]).toNat`
    (`JLoopBodyN.innerTripAtC`), i.e. the count materialised from the outer index by
    the front-compiled `countBody`.  Structural (`unfold`; `rw`; `rfl`); same axiom
    footprint as the committed `rolledForLoopNRtNestedCont_denote`. -/
theorem rolledForLoopNRtCountedCont_denote {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx} {s : JasminTy}
    (vmCount : VarMap (.sword 64 :: invCTys)) (countName : String) (countBody : LowCT)
    (vmBody : VarMap (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (accName : String)
    (updateBody : LowCT)
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s)
    {innerCount : Com jasminDialect (mapCtx (.sword 64 :: invCTys)) (mapTy (.sword 64))}
    {innerUpdate : Com jasminDialect
      (mapCtx (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hcnt : frontLoopBodyJ (accCTy := .sword 64) (Γbody := .sword 64 :: invCTys)
              vmCount countName countBody = some innerCount)
    (hupd : frontLoopBodyJ (accCTy := accCTy)
              (Γbody := accCTy :: .sword 64 :: .sword 64 :: invCTys)
              vmBody accName updateBody = some innerUpdate)
    (V : Ctxt.Valuation Γouter) :
    (rolledForLoopNRtCountedCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        vmCount countName countBody vmBody accName updateBody outerCount init invs
        cont).map (fun c => ComL.denote c V)
      = some (ComL.denote cont
          (V.extend (JLoopBodyN.nestedDenote innerCount innerUpdate
            (outerCount.lookup V).toNat (Expr.lookupArgs invs V) (init.lookup V)))) := by
  unfold rolledForLoopNRtCountedCont rolledForLoopNRtNestedCont
  rw [hcnt, hupd]
  rfl

/-! ## 7. A triangular-loop demo: inner trip = the outer index (`for i<N { for j<i }`)

The canonical state-dependent double fold: on outer pass `i`, the inner sweep runs
exactly `i` times — the trip is the outer index itself, materialised by the covered
`countBody` `cnt := SVar "jd"` (the front reads the outer index binder as the count).
The inner body increments the accumulator, so the whole loop computes
`Σ_{i<N} i = N(N-1)/2` — the count varies per outer pass (the MAYO `rc`
shape, with the clamped bound replaced by the bare index for a closed-form check). -/

/-- Count body: `cnt := jd` (the inner trip = the outer index). `countName = "cnt"`. -/
def triCountBody : LowCT := seqAll [.RScalarSetExpr "cnt" (.SVar "jd")]

/-- Count VarMap over `[jd]` (the outer index is the count body's only input). -/
def triCountVm : VarMap [CryptoTy.sword 64] :=
  VarMap.empty.bind (t := .sword 64) "jd"

/-- Sweep body: `acc2 := acc + 1` (count-only accumulate; neither the inner nor the
    outer index is read, so `acc` counts total inner iterations). -/
def triUpdateBody : LowCT := seqAll [.RScalarSetExpr "acc2" (.SAdd (.SVar "acc") (.SLit 1))]

/-- Sweep VarMap over `[acc, ti (inner idx), jd (outer idx)]`. -/
def triUpdateVm : VarMap [CryptoTy.sword 64, CryptoTy.sword 64, CryptoTy.sword 64] :=
  (((VarMap.empty.bind (t := .sword 64) "jd").bind
      (t := .sword 64) "ti").bind (t := .sword 64) "acc")

/-- Outer (kernel-argument) context `[N (outer count), acc]`. -/
def triΓouter : Ctxt jasminDialect := [.reg 64, .reg 64]

/-- The front-generated triangular counted loop — a `ComL.forLoopNRtNested`
    whose inner trip is recomputed as the outer index each pass, or `none`. -/
def triCounted : Option (ComL triΓouter (.reg 64)) :=
  rolledForLoopNRtCountedCont
    (Γouter := triΓouter) (accCTy := .sword 64) (invCTys := [])
    triCountVm "cnt" triCountBody
    triUpdateVm "acc2" triUpdateBody
    (outerCount := .here)          -- N
    (init := .there .here)         -- acc
    (invs := .nil)
    (cont := .ret .here)

/-- **The front generates the triangular loop.** -/
theorem triCounted_isSome : triCounted.isSome := by native_decide

/-- **The spine is the nested runtime-loop node** — a real recomputed-count
    2-deep loop, not an unrolled chain. -/
theorem triCounted_is_nested_node :
    (triCounted.map (fun c => match c with
      | .forLoopNRtNested _ _ _ _ _ _ => true
      | _ => false)) = some true := by native_decide

/-- Outer valuation: `N` outer trips, `acc = 0`. -/
def triVal (N : Nat) : Ctxt.Valuation triΓouter :=
  .cons (BitVec.ofNat 64 N) (.cons (0 : BitVec 64) .nil)

/-- The independent **state-dependent double fold**: `Σ_{i<N} (Σ_{j<i} 1) = Σ_{i<N} i`.
    The inner range's length is the outer index `i` — the trip varies per pass. -/
def triRef (N : Nat) : Nat :=
  (List.range N).foldl
    (fun acc i => (List.range i).foldl (fun b _ => b + 1) acc) 0

/-- **denote = the triangular double fold.** At `N = 6`, `Σ_{i<6} i = 0+1+2+3+4+5 = 15`
    — the inner sweep ran `i` times on pass `i`, the count materialised from the outer
    index by the front-compiled `countBody`. -/
theorem triCounted_denote_triangular :
    (triCounted.map (fun c => BitVec.toNat (ComL.denote c (triVal 6)))) = some (triRef 6) := by
  native_decide

/-- **Same program, different outer count** — `N = 5` → `0+1+2+3+4 = 10`; the trips
    are read off the seed valuation and recomputed per pass, not baked in. -/
theorem triCounted_denote_triangular' :
    (triCounted.map (fun c => BitVec.toNat (ComL.denote c (triVal 5)))) = some (triRef 5) := by
  native_decide

/-- **Two bottom-test back-edges** (outer + the recomputed-count inner): the
    `comLToBody` lowering carries exactly **two** `Lcond NZ` conditional jumps — real
    nested control flow with a per-outer-pass recomputed inner trip. -/
theorem triCounted_two_backedges :
    (triCounted.map (fun c =>
        let body := comLToBody 2 argName (fun _ => none) c 2
        (body.filter (fun i => match i.li_i with
            | .Lcond (.reg "NZ") _ => true | _ => false)).length == 2))
      = some true := by native_decide

/-! ## 8. The counted sweep splices mid-chain — a phase after it

The counted combinator carries a continuation (`cont`), so a further phase runs after
the whole nested sweep with its accumulator bound at `.here`.  Here the counted
triangular sweep is followed by a straight-line `acc += 100` glue phase
(`rolledForLoopNCont` at trip `1`), showing the state-dependent counted loop composes
in the §5 phase chain exactly like the fixed-count / guard-count phases do. -/

/-- Glue VarMap `[acc, gidx]` for the 1-trip suffix. -/
def triGlueVm : VarMap [CryptoTy.sword 64, CryptoTy.sword 64] :=
  (VarMap.empty.bind (t := .sword 64) "gidx").bind (t := .sword 64) "acc"

/-- Suffix glue body `acc += 100`. -/
def triSuffixBody : LowCT := seqAll [.RScalarSetExpr "acc2" (.SAdd (.SVar "acc") (.SLit 100))]

/-- The counted triangular sweep with a `acc += 100` suffix phase spliced after it. -/
def triCountedChain : Option (ComL triΓouter (.reg 64)) :=
  rolledForLoopNRtCountedCont
    (Γouter := triΓouter) (accCTy := .sword 64) (invCTys := [])
    triCountVm "cnt" triCountBody
    triUpdateVm "acc2" triUpdateBody
    (outerCount := .here) (init := .there .here) (invs := .nil)
    (cont :=
      match rolledForLoopNCont (Γouter := (.reg 64) :: triΓouter) (accCTy := .sword 64)
              (invCTys := []) 1 triGlueVm "acc2" triSuffixBody
              (init := .here) (invs := .nil) (cont := .ret .here) with
      | some g => g
      | none => .ret .here)

/-- **The counted sweep splices mid-chain.** `denote = triangular fold + 100`: the
    suffix phase ran on the nested-sweep result, witnessing the counted loop as a
    phase in the multi-phase chain (`N = 6` → `15 + 100 = 115`). -/
theorem triCountedChain_denote_seq :
    (triCountedChain.map (fun c => BitVec.toNat (ComL.denote c (triVal 6))))
      = some (triRef 6 + 100) := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.RecursiveForLoopBlockFront
