/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

set_option autoImplicit false

/-!
# Multi-phase composition: front-compile a *sequence* of loop phases into ONE `ComL`

The committed runtime-trip front (`TranslateDialectRuntimeLoop.rolledForLoopNRt`)
emits exactly ONE loop node and hardcodes its continuation to `body := .ret .here`
(return the accumulator, stop). That is the wall gap 1 of
`ConvertToVoleV204FrontEmit` records: no committed front produces
`forLoopNRt … (body := <next phase>)`, so a whole-function *sequence* of phases
(fill ; reduce ; …) could only be assembled by hand-building the `ComL` nesting —
the emit anti-pattern.

`ComL` is *already* structurally sequential: every loop node
(`forLoop`/`forLoopN`/`forLoopNRt`) carries a continuation
`body : ComL (accTy :: Γ) s`, and `forLoopNRt` binds its final accumulator into
that continuation before it runs. So the missing piece is not a new IR node — it is
a *front combinator* that threads the front-compiled next phase into the `body`
slot instead of `.ret .here`. This module adds it.

## What this module builds

* `rolledForLoopNRtCont` — the additive generalisation of `rolledForLoopNRt`: it
  takes a caller-supplied continuation `cont : ComL (mapTy accCTy :: Γouter) s`
  and emits `ComL.forLoopNRt update count init invs cont`. Setting
  `cont := .ret .here` recovers `rolledForLoopNRt` exactly; setting `cont` to the
  front-compiled *next phase* is the lynchpin — **`.ret .here` is replaced by the
  next phase**. No hand-authored raw `Com`: each phase's body is still produced by
  the committed front (`frontLoopBodyJ`), and the phases are glued only through the
  `ComL` constructor's `body` continuation. Folding a *list* of phases into one
  `ComL` is a right-fold of `rolledForLoopNRtCont` calls whose innermost `cont` is
  `.ret v` (§1); the concrete two-phase spine in §3 is that fold at length 2.

* `rolledForLoopNRtCont_denote` — the denote bridge: the composed node denotes to
  `cont.denote (V.extend (fold …))`, i.e. **phase-1's fold result is bound into the
  valuation and phase-2 runs on it**. Iterating this is exactly the sequential
  composition of the phases (§2).

* `rolledForLoopNCont` (§2b) — the **fixed-trip** twin: the same continuation lift
  applied to `TranslateDialectRolledLoop.rolledForLoopN` / `ComL.forLoopN`. A phase
  whose trip count is a compile-time `Nat` consumes **no count argument register**,
  so a long chain of phases with distinct compile-time counts (the fri_proof spine's
  `32,16,8,5,4,3,2,1,…`) no longer exhausts the 6 SysV integer registers — mixed
  fixed/runtime chains compose freely (a fixed-trip phase's `cont` can be a
  runtime-trip phase and vice versa, both live in the same `ComL`).

* `rolledForLoopNRtNestedCont` (§2c) — the same lift for the genuine nested
  runtime loop (`ComL.forLoopNRtNested`), so a per-outer-recomputed inner-trip
  nest (a flat Merkle level-compress) can sit mid-chain with further phases as
  its continuation.

## Sequential (continuation) composition vs. nested (per-iteration) loops

The `ComL` continuation `body` runs *once, after* its loop finishes, so nesting two
loop nodes via `body` is **sequential** composition (phase-1's whole fold, then
phase-2's whole fold reading phase-1's result) — a fold-after-fold `f₂ ∘ f₁`, not a
double fold `Σⱼ Σᵢ`. That is exactly what the four-phase `convert_to_vole_v`
orchestration (PRG-expand ; zero ; GGM-tree ; `u = R`) needs at the phase seam, and
what this module supplies.

A **genuine per-iteration nested runtime loop** (`for jd<D: for idx<trip(jd): …`, the
GGM Phase-3 shape) is a *different* structure and is **NOT** `ComL`-typeable through
the committed alphabet: `ComL.forLoopNRt`'s per-iteration body is
`update : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy`, a **straight-line**
`Com`. A loop cannot live inside a `Com jasminDialect` — `JasminLprogExport`
(§3b, lines ~775–778) records precisely that "a fixed-trip loop cannot be a
`JasminOp` constructor … a loop body is a `Com jasminDialect [accTy] accTy`", so the
only place a loop node exists is `ComL`, and `update` is `Com`, not `ComL`. Making
the outer per-iteration body itself a loop would require either a new `ComL`
constructor (`update : ComL …`) or a loop `JasminOp` — both forbidden here (no edits
to the `ComL` semantics), and the latter impossible by construction.

So the honest split is:
* the **front** for the double-fold nested runtime loop is a real structural gap
  (reported precisely above — needs a `ComL` node whose per-iteration body is a
  `ComL`, not a `Com`);
* the **interpreter/state half** of that double fold is *already* discharged, at the
  `LinstrRM` level, in `JasminLsemMemLoopNestDepth` (commit 28f486d47): its
  `ggmNestedFold` / `runNestedVarLoopMem` are the two-level fold with a per-outer
  recomputed inner trip, `native_decide`-validated there (`ggm_depth3_validate`).
  §4 re-exports that spec (does not re-prove it) and states the front residual
  crisply against it.

## Validate (`native_decide`)

§3 authors a two-phase kernel — phase 1 `for i<n: buf[i] := a[i]` (fill), phase 2
`for i<n: acc += buf[i]` (reduce) — front-compiles it to ONE `ComL` spine
(`forLoopNRt … (body := forLoopNRt … (body := .ret …))`), and pins
`ComL.denote = Σ_{i<n} a[i]` at three runtime counts. Because phase 2 reads the
*phase-1 loop result* (the filled `buf`, bound at `.here` by the outer
continuation), `acc = Σ a` holds only if the fill phase actually ran — so the single
denote transitively witnesses **both** phases. §3.4 additionally pins the fill
phase's own result (`buf[i] = a[i]`).

Invoke (in-model gate):
  lake env lean CatCrypt/Crypto/SecureCompilation/Dialects/TranslateDialectPhaseCompose.lean
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectPhaseCompose

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRolledLoop
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectRuntimeLoop
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType)

/-! ## 1. The phase-sequencing combinator

`rolledForLoopNRtCont` is `rolledForLoopNRt` with its hardcoded `.ret .here`
continuation lifted to a parameter `cont`. The loop body is still front-compiled
by the committed `frontLoopBodyJ`; the *only* new freedom is what runs after the
loop — the caller passes the front-compiled next phase there. -/

/-- Build a runtime-trip rolled `ComL.forLoopNRt` from a front-compiled loop body,
    **with a caller-supplied continuation** `cont` in place of `.ret .here`.

    `cont : ComL (mapTy accCTy :: Γouter) s` runs after the loop, with the loop's
    final accumulator bound at `.here`. Passing `cont := .ret .here` recovers
    `TranslateDialectRuntimeLoop.rolledForLoopNRt`; passing the front-compiled next
    phase sequences the phases. Returns `none` iff the front declines the body. -/
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
  | some update => some (ComL.forLoopNRt update count init invs cont)
  | none => none

/-- Passing `cont := .ret .here` recovers `rolledForLoopNRt` exactly: the generic
    combinator is a faithful generalisation, not a divergent path. -/
theorem rolledForLoopNRtCont_ret_here {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (count : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    rolledForLoopNRtCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        vmBody accName body count init invs (.ret .here)
      = rolledForLoopNRt (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
          vmBody accName body count init invs := by
  unfold rolledForLoopNRtCont rolledForLoopNRt
  cases frontLoopBodyJ (accCTy := accCTy) vmBody accName body <;> rfl

/-! ## 2. Denote bridge — the continuation runs on the fold result

The composed node denotes to `cont.denote (V.extend (fold …))`: phase-1's fold
result is bound at `.here` and the continuation (the next phase) runs on it. This
is the exact statement that `.ret .here` was replaced by the next phase and the
data threads through — iterating it is the sequential composition of the phases. -/

/-- **Phase-compose denotation.** When the body front-compiles to `update`, the
    composed `ComL` denotes to the continuation `cont` evaluated on the valuation
    extended by the runtime-trip fold of `update` (seed `init`, invariants `invs`,
    trip `(count.lookup V).toNat`). Structural on `ComL.denote`; no `sorry`. -/
theorem rolledForLoopNRtCont_denote {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx} {s : JasminTy}
    (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (count : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s)
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update)
    (V : Ctxt.Valuation Γouter) :
    (rolledForLoopNRtCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        vmBody accName body count init invs cont).map (fun c => ComL.denote c V)
      = some (ComL.denote cont
          (V.extend (JLoopBodyN.denote ⟨(count.lookup V).toNat, update⟩
            (Expr.lookupArgs invs V) (init.lookup V)))) := by
  unfold rolledForLoopNRtCont
  rw [hupd]
  rfl

/-! ## 2b. The fixed-trip phase combinator (`ComL.forLoopN` with a continuation)

`rolledForLoopNCont` is `TranslateDialectRolledLoop.rolledForLoopN` with its
hardcoded `.ret .here` continuation lifted to a parameter — exactly the §1 lift,
applied to the **compile-time-count** loop node. A fixed-trip phase reads no count
register, which is what keeps a many-phase chain inside the SysV integer-register
budget. -/

/-- Build a fixed-trip rolled `ComL.forLoopN` from a front-compiled loop body,
    **with a caller-supplied continuation** `cont` in place of `.ret .here`.

    `cont : ComL (mapTy accCTy :: Γouter) s` runs after the loop, with the loop's
    final accumulator bound at `.here`. Passing `cont := .ret .here` recovers
    `TranslateDialectRolledLoop.rolledForLoopN`; passing the front-compiled next
    phase sequences the phases. The trip count `N` is compile-time, so the phase
    consumes no count-argument register. Returns `none` iff the front declines. -/
def rolledForLoopNCont {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx} {s : JasminTy}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s) :
    Option (ComL Γouter s) :=
  match frontLoopBodyJ (accCTy := accCTy) vmBody accName body with
  | some update => some (ComL.forLoopN ⟨N, update⟩ init invs cont)
  | none => none

/-- Passing `cont := .ret .here` recovers `rolledForLoopN` exactly: the generic
    combinator is a faithful generalisation, not a divergent path. -/
theorem rolledForLoopNCont_ret_here {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    rolledForLoopNCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        N vmBody accName body init invs (.ret .here)
      = rolledForLoopN (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
          N vmBody accName body init invs := by
  unfold rolledForLoopNCont rolledForLoopN
  cases frontLoopBodyJ (accCTy := accCTy) vmBody accName body <;> rfl

/-- **Fixed-trip phase-compose denotation.** When the body front-compiles to
    `update`, the composed `ComL` denotes to the continuation `cont` evaluated on
    the valuation extended by the `N`-fold `JLoopBodyN.denote` of `update` (seed
    `init`, invariants `invs`). Structural on `ComL.denote`; no `sorry`. -/
theorem rolledForLoopNCont_denote {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx} {s : JasminTy}
    (N : Nat) (vmBody : VarMap (accCTy :: .sword 64 :: invCTys)) (accName : String)
    (body : LowCT)
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy))
    (cont : ComL (mapTy accCTy :: Γouter) s)
    {update : Com jasminDialect (mapCtx (accCTy :: .sword 64 :: invCTys)) (mapTy accCTy)}
    (hupd : frontLoopBodyJ (accCTy := accCTy) vmBody accName body = some update)
    (V : Ctxt.Valuation Γouter) :
    (rolledForLoopNCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        N vmBody accName body init invs cont).map (fun c => ComL.denote c V)
      = some (ComL.denote cont
          (V.extend (JLoopBodyN.denote ⟨N, update⟩ (Expr.lookupArgs invs V)
            (init.lookup V)))) := by
  unfold rolledForLoopNCont
  rw [hupd]
  rfl

/-! ## 2c. The nested-runtime-loop phase combinator (`ComL.forLoopNRtNested` with a
continuation)

`rolledForLoopNRtNestedCont` is `TranslateDialectRuntimeLoop.rolledForLoopNRtNested`
with the same continuation lift: a genuine nested runtime loop (inner trip
recomputed per outer pass) can now sit **mid-chain** — e.g. a flat Merkle
level-compress whose continuation is the query/auth-path walk phases. -/

/-- Build a genuine **nested runtime-trip** `ComL.forLoopNRtNested` from two
    front-compiled bodies, **with a caller-supplied continuation** `cont` in place
    of `.ret .here`. Passing `cont := .ret .here` recovers
    `TranslateDialectRuntimeLoop.rolledForLoopNRtNested`. `none` if either body's
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

/-- Passing `cont := .ret .here` recovers `rolledForLoopNRtNested` exactly. -/
theorem rolledForLoopNRtNestedCont_ret_here {Γouter : Ctxt jasminDialect}
    {accCTy : CryptoTy} {invCTys : Ctx}
    (vmCount : VarMap (.sword 64 :: invCTys)) (countName : String) (countBody : LowCT)
    (vmBody : VarMap (accCTy :: .sword 64 :: .sword 64 :: invCTys)) (accName : String)
    (updateBody : LowCT)
    (outerCount : Ctxt.Var Γouter (JasminTy.reg 64))
    (init : Ctxt.Var Γouter (mapTy accCTy))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invCTys.map mapTy)) :
    rolledForLoopNRtNestedCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        vmCount countName countBody vmBody accName updateBody outerCount init invs
        (.ret .here)
      = rolledForLoopNRtNested (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
          vmCount countName countBody vmBody accName updateBody outerCount init invs := by
  unfold rolledForLoopNRtNestedCont rolledForLoopNRtNested
  cases frontLoopBodyJ (accCTy := .sword 64) (Γbody := .sword 64 :: invCTys)
      vmCount countName countBody <;>
    cases frontLoopBodyJ (accCTy := accCTy)
        (Γbody := accCTy :: .sword 64 :: .sword 64 :: invCTys) vmBody accName updateBody <;>
    rfl

/-- **Nested phase-compose denotation.** When both bodies front-compile, the
    composed `ComL` denotes to the continuation `cont` evaluated on the valuation
    extended by the outer×inner double fold `JLoopBodyN.nestedDenote`. Structural
    on `ComL.denote`; no `sorry`. -/
theorem rolledForLoopNRtNestedCont_denote {Γouter : Ctxt jasminDialect}
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
    (rolledForLoopNRtNestedCont (Γouter := Γouter) (accCTy := accCTy) (invCTys := invCTys)
        vmCount countName countBody vmBody accName updateBody outerCount init invs
        cont).map (fun c => ComL.denote c V)
      = some (ComL.denote cont
          (V.extend (JLoopBodyN.nestedDenote innerCount innerUpdate
            (outerCount.lookup V).toNat (Expr.lookupArgs invs V) (init.lookup V)))) := by
  unfold rolledForLoopNRtNestedCont
  rw [hcnt, hupd]
  rfl

/-! ## 3. Validate: a two-phase fill-then-reduce kernel, one `ComL` spine

Phase 1 fills a scratch buffer `buf[i] := a[i]`; phase 2 reduces `acc += buf[i]`.
The composed spine is `forLoopNRt (fill) … (body := forLoopNRt (reduce) … (.ret))`,
where phase 2's *invariant* is the phase-1 loop **result** (the filled `buf`, bound
at `.here` by phase 1's continuation) — the data thread from one phase to the next. -/

/-- Row capacity in 64-bit words; runtime count `cnt ≤ N`. Small for `native_decide`. -/
def paramN : Nat := 8

/-- Sequence a list of `LowCT` into an `RSeq` chain. -/
def seqAll : List LowCT → LowCT
  | [] => .RSkip
  | [c] => c
  | c :: cs => .RSeq c (seqAll cs)

/-! ### 3.1 Phase bodies (covered LowCT) -/

/-- Phase 1 body — `buf[idx] := a[idx]` at the runtime loop counter (dynamic load +
    dynamic store, both `memrefGetDyn`/`memrefSetDyn`). Accumulator `buf`. -/
def fillBody : LowCT := seqAll [
  .RArrLoad ⟨"w", .TU64⟩ ⟨"a", .TBytes (8 * paramN)⟩ "idx",
  .RArrStore ⟨"buf", .TBytes (8 * paramN)⟩ "idx" ⟨"w", .TU64⟩ ]

/-- Phase 2 body — `acc[0] := acc[0] + buf[idx]`. Accumulator `acc` (a size-1
    memref); `buf` is the invariant (phase-1's result). `z := 0` is the constant
    index for the scalar `acc[0]` slot. -/
def reduceBody : LowCT := seqAll [
  .RScalarSetExpr "z" (.SLit 0),
  .RArrLoad ⟨"bi", .TU64⟩ ⟨"buf", .TBytes (8 * paramN)⟩ "idx",
  .RArrLoad ⟨"a0", .TU64⟩ ⟨"acc", .TBytes 8⟩ "z",
  .RScalarSetExpr "s" (.SAdd (.SVar "a0") (.SVar "bi")),
  .RArrStore ⟨"acc", .TBytes 8⟩ "z" ⟨"s", .TU64⟩ ]

/-! ### 3.2 Body contexts + VarMaps -/

/-- Phase-1 body context: accumulator `buf`, loop index `idx`, invariant `a`. -/
def Γbody1 : Ctx := [.memref paramN, .sword 64, .memref paramN]

/-- Phase-1 VarMap: `buf ↦ .here`, `idx ↦ .there .here`, `a ↦ .there² .here`. -/
def vmBody1 : VarMap Γbody1 :=
  (((VarMap.empty.bind (t := .memref paramN) "a").bind
      (t := .sword 64) "idx").bind (t := .memref paramN) "buf")

/-- Phase-2 body context: accumulator `acc`, loop index `idx`, invariant `buf`. -/
def Γbody2 : Ctx := [.memref 1, .sword 64, .memref paramN]

/-- Phase-2 VarMap: `acc ↦ .here`, `idx ↦ .there .here`, `buf ↦ .there² .here`. -/
def vmBody2 : VarMap Γbody2 :=
  (((VarMap.empty.bind (t := .memref paramN) "buf").bind
      (t := .sword 64) "idx").bind (t := .memref 1) "acc")

/-! ### 3.3 The composed program

Outer context `Γouter = [count, a, buf, acc]` (newest-first): `count ↦ .here`,
`a ↦ .there .here`, `buf ↦ .there² .here`, `acc ↦ .there³ .here`. Phase 2 runs in
the extended context `mapTy (.memref N) :: Γouter` where the filled `buf` result is
`.here`; the original slots shift by one. -/

/-- The outer (kernel-argument) jasmin context: `[count, a, buf, acc]`. -/
def Γouter : Ctxt jasminDialect :=
  [.reg 64, .stackArr 64 paramN, .stackArr 64 paramN, .stackArr 64 1]

/-- The extended outer context inside phase 1's continuation: the filled `buf`
    result is `.here`; `count`/`a`/`buf`/`acc` shift by one. -/
abbrev Γouter1 : Ctxt jasminDialect := (mapTy (CryptoTy.memref paramN)) :: Γouter

/-- Phase 2 (reduce), front-compiled over `Γouter1`. Its invariant is the phase-1
    loop **result** — `buf_filled` at `.here` — so the reduce reads the freshly
    filled buffer. Continuation `.ret .here` returns the reduced accumulator. -/
def phase2 : Option (ComL Γouter1 (.stackArr 64 1)) :=
  rolledForLoopNRtCont (Γouter := Γouter1) (accCTy := .memref 1)
    (invCTys := [.memref paramN])
    vmBody2 "acc" reduceBody
    (count := .there .here)                                   -- count
    (init := .there (.there (.there (.there .here))))         -- acc
    (invs := .cons .here .nil)                                -- buf_filled (phase-1 result)
    (cont := .ret .here)

/-- The full two-phase kernel: phase 1 (fill) with **phase 2 as its continuation**
    (the `.ret .here` replaced by the front-compiled next phase). ONE `ComL` spine,
    two rolled runtime loops, no hand-authored `Com`. -/
def composeComL : Option (ComL Γouter (.stackArr 64 1)) :=
  match phase2 with
  | some p2 =>
      rolledForLoopNRtCont (Γouter := Γouter) (accCTy := .memref paramN)
        (invCTys := [.memref paramN])
        vmBody1 "buf" fillBody
        (count := .here)                          -- count
        (init := .there (.there .here))           -- buf (scratch, phase-1 accumulator)
        (invs := .cons (.there .here) .nil)       -- a (phase-1 invariant)
        (cont := p2)
  | none => none

/-! ### 3.4 Gates + denote validates -/

/-- The two-phase kernel front-compiles to a single `ComL` spine. -/
theorem composeComL_isSome : composeComL.isSome := by native_decide

/-- The composed spine is genuinely a loop-inside-a-continuation: the outer loop's
    body continuation is itself a `forLoopNRt` (not `.ret`). -/
theorem composeComL_body_is_loop :
    (composeComL.map (fun c => match c with
      | .forLoopNRt _ _ _ _ (.forLoopNRt _ _ _ _ _) => true
      | _ => false))
      = some true := by native_decide

/-- INDEPENDENT plain-`Nat` reference: `Σ_{i<cnt} a[i]` (fill-then-reduce spec). -/
def natSumRt (a : Fin paramN → BitVec 64) (cnt : Nat) : Nat :=
  (List.range cnt).foldl
    (fun acc i => acc + (a ⟨i % paramN, Nat.mod_lt _ (by decide)⟩).toNat) 0

/-- Deterministic sample stream `a[i] = 7i + 3`. -/
def sampleA : Fin paramN → BitVec 64 := fun i => BitVec.ofNat 64 (i.val * 7 + 3)

/-- Valuation at runtime count `cnt`: `count = cnt`, `a = sampleA`, scratch `buf`
    and `acc` zeroed. -/
def valAt (cnt : Nat) : Ctxt.Valuation Γouter :=
  .cons (BitVec.ofNat 64 cnt)
    (.cons sampleA (.cons (fun _ => (0 : BitVec 64)) (.cons (fun _ => (0 : BitVec 64)) .nil)))

/-- **denote = Σ_{i<5} a[i].** The composed kernel runs both phases: `acc` equals
    the sum of the filled `buf`, which equals `Σ a` — so a correct value here
    witnesses BOTH the fill (phase 1) and the reduce (phase 2). -/
theorem composeComL_denote_count5 :
    (composeComL.map (fun c => (ComL.denote c (valAt 5) ⟨0, by decide⟩).toNat))
      = some (natSumRt sampleA 5) := by native_decide

/-- **denote = Σ_{i<8} a[i]** (SAME program, different runtime count). -/
theorem composeComL_denote_count8 :
    (composeComL.map (fun c => (ComL.denote c (valAt 8) ⟨0, by decide⟩).toNat))
      = some (natSumRt sampleA 8) := by native_decide

/-- **denote = 0 at count 0** (both phases empty). -/
theorem composeComL_denote_count0 :
    (composeComL.map (fun c => (ComL.denote c (valAt 0) ⟨0, by decide⟩).toNat))
      = some 0 := by native_decide

/-! ### 3.5 The fill phase in isolation (phase-1 result witnessed directly)

`fillOnly` is phase 1 with `cont := .ret .here` (i.e. `rolledForLoopNRt`, by
`rolledForLoopNRtCont_ret_here`). Its denote is the filled `buf`; we pin
`buf[i] = a[i]` for indices `< count`, confirming the fill phase does its job (so
the composed kernel's `Σ a` genuinely rests on a real fill, not a coincidence). -/

/-- Phase 1 alone (fill), returning the filled buffer. -/
def fillOnly : Option (ComL Γouter (.stackArr 64 paramN)) :=
  rolledForLoopNRtCont (Γouter := Γouter) (accCTy := .memref paramN)
    (invCTys := [.memref paramN])
    vmBody1 "buf" fillBody
    (count := .here)
    (init := .there (.there .here))
    (invs := .cons (.there .here) .nil)
    (cont := .ret .here)

/-- **Phase 1 fills `buf[3] = a[3]`** at runtime count 5 (`3 < 5`). -/
theorem fillOnly_denote_idx3_count5 :
    (fillOnly.map (fun c => (ComL.denote c (valAt 5) ⟨3, by decide⟩).toNat))
      = some (sampleA ⟨3, by decide⟩).toNat := by native_decide

/-- **Phase 1 leaves `buf[6]` at its scratch value 0** at runtime count 5
    (`6 ≥ 5`, so the fill never wrote it) — the count genuinely bounds the fill. -/
theorem fillOnly_denote_idx6_count5 :
    (fillOnly.map (fun c => (ComL.denote c (valAt 5) ⟨6, by decide⟩).toNat))
      = some 0 := by native_decide

/-! ### 3.6 Mixed fixed/runtime chain (the register-pressure shape)

The same two-phase kernel with the fill phase at a **compile-time** trip count
(`N = paramN`, via `rolledForLoopNCont`) and the reduce phase still runtime-count:
the fixed phase consumes no count register, and both loop flavours live in one
`ComL` spine. -/

/-- Fill fixed at `N = paramN`, reduce at the runtime count (phase 2 reused
    verbatim): a mixed fixed/runtime two-phase spine. -/
def composeFixedComL : Option (ComL Γouter (.stackArr 64 1)) :=
  match phase2 with
  | some p2 =>
      rolledForLoopNCont (Γouter := Γouter) (accCTy := .memref paramN)
        (invCTys := [.memref paramN])
        paramN vmBody1 "buf" fillBody
        (init := .there (.there .here))           -- buf (scratch, phase-1 accumulator)
        (invs := .cons (.there .here) .nil)       -- a (phase-1 invariant)
        (cont := p2)
  | none => none

/-- The mixed spine front-compiles, and is a fixed-trip loop whose continuation is
    a runtime-trip loop. -/
theorem composeFixedComL_shape :
    (composeFixedComL.map (fun c => match c with
      | .forLoopN _ _ _ (.forLoopNRt _ _ _ _ _) => true
      | _ => false))
      = some true := by native_decide

/-- **denote = Σ_{i<5} a[i]** for the mixed spine: the fixed-`N` fill populates all
    `paramN` slots, the runtime reduce sums the first 5. -/
theorem composeFixedComL_denote_count5 :
    (composeFixedComL.map (fun c => (ComL.denote c (valAt 5) ⟨0, by decide⟩).toNat))
      = some (natSumRt sampleA 5) := by native_decide

/-! ## 4. Nested runtime loop: the front residual, stated against the (done) spec

The GGM Phase-3 double fold (`for jd<D: for idx<trip(jd): …`) is realised as a
genuine two-level fold in `JasminLsemMemLoopNestDepth` — `ggmNestedFold` /
`runNestedVarLoopMem`, with the inner trip recomputed per outer step (`num >>>
(jd+1)`), `native_decide`-validated at the `LinstrRM` level (real back-edges at
three distinct labels). We re-export that spec (no re-proof) to state the front
residual precisely. -/

/-- Re-export of the interpreter-level GGM double-fold spec (proved in
    `JasminLsemMemLoopNestDepth`). The *state half* of a nested runtime loop is
    thus already discharged. -/
abbrev ggmDoubleFold : Nat → Nat → Nat → Nat :=
  CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth.ggmNestedFold

/-- Sanity re-check of the committed nested spec at the GGM Phase-3 sizes
    (`D=3`, `num=8`, `outlen=1`): the double fold equals the per-outer-varying
    inner-trip fold. (`native_decide`; the substantive proof lives upstream.) -/
theorem ggmDoubleFold_matches_var :
    ggmDoubleFold 3 8 1
      = CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestDepth.runNestedVarLoopMem
          (fun jd => 8 >>> (jd + 1)) 3 1 := by native_decide

/-!
### Nested runtime loop — the `forLoopNRtNested` node (this file: sequential only)

The continuation nesting of §3 gives `f₂ ∘ f₁` (sequential), never `Σⱼ Σᵢ`
(nested): `ComL.forLoopNRt`'s per-iteration body is a straight-line `Com`, so the
outer loop's per-iteration work cannot itself be a runtime loop *through the
`forLoopNRt` node*.

The genuine per-iteration nested runtime loop is the separate `ComL` constructor
`ComL.forLoopNRtNested` (`JasminLprogExport`): a runtime outer loop whose
per-iteration body is itself a runtime loop, with the inner trip recomputed per
outer pass. Its denote is `JLoopBodyN.nestedDenote` (the double fold matching
`runNestedVarLoopMem`), its lowering emits genuine nested back-edges (an inner
`forLoopLcmdNRt` inside the outer body), and the front combinator
`TranslateDialectRuntimeLoop.rolledForLoopNRtNested` front-compiles both the
inner-count and inner-update bodies via `frontLoopBodyJ`. See
`NestedRuntimeLoopFrontValidate`: it front-compiles the GGM Phase-3 shape and pins
`ComL.denote = ggmNestedFold` (= the proven `ggmProg` interpreter execution). This
module's `rolledForLoopNRtCont` remains the *sequential* (phase-seam) combinator.
-/

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectPhaseCompose
