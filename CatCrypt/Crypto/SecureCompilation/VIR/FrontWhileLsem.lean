/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FrontControlLsem

/-!
# Tying the front `RWhileNz` (PUBLIC-guard while loop) to the program-level `lsem`
loop simulation

`FrontControlLsem.lean` ties the front *counted* loop `RFor x n body`
— a loop with a **static** trip count `n` — to the program-level `lsem` loop run
(`JasminLsemLoop.lean`). This module covers the other
front loop construct `RWhileNz x body` — a `while` loop whose trip count
is **not statically fixed** but is the length of the *public guard's trajectory*
(the number of body iterations until the guard scalar `x` hits `0`).

## What `RWhileNz` means, and why the public-guard case is the deliverable

`RWhileNz e body` runs `body` while the scalar `e ≠ 0` (`RustExec.whileFalse` /
`whileTrue`, `Jasmin/LowCT.lean`). Unlike `RFor`, the `whileTrue` rule does **not**
set the loop counter before each body run — the *body itself* is responsible for
driving the guard `e` toward `0`. So one iteration's front effect is captured by an
**index-free** transformer `frontStep : RustState → RustState` (running `body` once),
and the whole loop's post-state is the **`n`-fold iterate** `frontStep^[n] rs`, where
`n` is the number of iterations until the guard hits `0`.

That iteration count `n` is **data-determined but PUBLIC**: it is fixed by the
trajectory of the guard scalar `e`, and the CT analysis (`cmdCT_RWhileNz`) admits the
loop precisely when `lt e = .Public`. The public-guard hypothesis here is the exact
analogue of the public *static* trip count of `FrontControlLsem`.

Note: A
`RWhileNz` whose guard `e` is *secret*-classified leaks the iteration count `n`
through the back-edge decision trace (the number of `branch` leaks = the number of
iterations), and is therefore **not** constant-time. We do not model or
claim CT for that case; `cmdCT_RWhileNz`'s `lt e = .Public` requirement excludes it,
and our robustness conjunct is stated only under the public-guard discipline. The
deliverable is exactly the **public-guard** while loop.

## How the iteration count is bounded by the public guard trajectory

The "public trip count" of `RFor` is the static `n`. Here it is supplied as a
hypothesis on the front trajectory:

* `hguard_nz : ∀ k < n, ((frontStep^[k]) rs).rsScalar e ≠ 0` — the guard is nonzero
  for the first `n` iterations (each fires `RustExec.whileTrue`);
* `hguard_z : ((frontStep^[n]) rs).rsScalar e = 0` — the guard hits `0` at iteration
  `n` (fires `RustExec.whileFalse`, terminating the loop).

`n` is the **public trajectory length**: it is determined by the (public) guard
scalar `e`'s evolution, never by a secret. This is the public-guard analogue of
`LoopTerminatesIn` (the back-edge counter `"NZ"` being a public count).

## Reuse of the `JasminLsemLoop` / `FrontControlLsem` machinery

The emitted loop side is the one of `FrontControlLsem`: the real emitted form is `loopProg`
/ `loopLR` (the `loopLcmd` shape modulo the dropped flag-`CMP`,
`loopLR_eq_loopLcmd_dropCmp`), driven by the labeled `lsemFuel`, with the public
back-edge `Lcond (.reg "NZ") top`. We reuse `front_loop_lsem_correct` verbatim —
instantiating its *indexed* per-iteration transformer `frontStep' : Nat → RustState →
RustState` at the **index-ignoring** `fun _ rs => frontStep rs` (the while body takes
no counter), and its static trip count `c+1` at the public trajectory length `n =
c+1`. The `FrontLoopEncodes` commuting square (one front iteration ↔ one `lsem`
`bodyStep`) is reused exactly. The front denotation side is the `n`-fold
`Function.iterate` characterisation of `RWhileNz` proved here.

**0 sorries; axioms ⊆ {propext, Classical.choice, Quot.sound}; no
`jasminc_preserves_ct`, no `JasminIRToX86` edge.**
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FrontWhileLsem

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.FrontControlLsem

/-! ## 1. The front `RWhileNz`'s `RustExec` denotation as an `n`-fold iterate

`RWhileNz e body` runs `body` repeatedly while the public scalar `e ≠ 0`. One
iteration's effect on the front state is the *index-free* transformer
`frontStep : RustState → RustState` (one body run). The whole loop's post-state is the
`n`-fold iterate `frontStep^[n] rs`, where `n` is the number of iterations until the
guard `e` hits `0` (the public guard trajectory length). -/

/-- **The front `RWhileNz`'s `RustExec` denotation is the `n`-fold `frontStep`
    iterate.** Given:

    * the single-iteration body edge `hbody` — running `body` from `rs` lands in
      `frontStep rs` (the named front edge, the while analogue of `RFor`'s per-iteration
      `hbody`, NOT a `sorry`);
    * the **public guard trajectory** `hnz`/`hz` — the guard `e` is nonzero for the
      first `n` iterations and hits `0` at iteration `n`;

    the big-step `RustExec` of `RWhileNz e body` from `rs` reaches exactly the `n`-fold
    iterate `(frontStep^[n]) rs`. Proof by induction on the public trajectory length
    `n` via the `whileFalse` / `whileTrue` rules. The guard scalar `e` being PUBLIC is
    what makes `n` a public, data-determined number (a secret guard would leak `n`). -/
theorem rustExec_rwhilenz_iterate {N : Nat} {leafSpec : LeafSpec}
    (e : String) (body : LowCT) (frontStep : RustState → RustState)
    (hbody : ∀ (rs : RustState), RustExec N leafSpec body rs (frontStep rs)) :
    ∀ (n : Nat) (rs : RustState),
      (∀ k < n, ((frontStep^[k]) rs).rsScalar e ≠ 0) →
      ((frontStep^[n]) rs).rsScalar e = 0 →
      RustExec N leafSpec (.RWhileNz e body) rs ((frontStep^[n]) rs) := by
  intro n
  induction n with
  | zero =>
      intro rs _ hz
      -- n = 0: guard already 0, the loop does not run (whileFalse).
      simp only [Function.iterate_zero, id_eq] at hz ⊢
      exact RustExec.whileFalse e body rs hz
  | succ m ih =>
      intro rs hnz hz
      -- guard at rs (= iterate 0) is nonzero, so we fire whileTrue once.
      have h0 : rs.rsScalar e ≠ 0 := by
        have := hnz 0 (Nat.succ_pos m)
        simpa using this
      -- one body run: rs → frontStep rs; then the loop on `frontStep rs` for `m` more.
      refine RustExec.whileTrue e body rs (frontStep rs) ((frontStep^[m + 1]) rs)
        (rs.rsScalar e) rfl h0 (hbody rs) ?_
      -- the tail loop on `frontStep rs` runs `m` iterations: its post-state is
      -- `frontStep^[m] (frontStep rs) = frontStep^[m+1] rs`.
      have htail : ((frontStep^[m]) (frontStep rs)) = (frontStep^[m + 1]) rs := by
        rw [← Function.iterate_succ_apply]
      rw [← htail]
      apply ih (frontStep rs)
      · intro k hk
        rw [← Function.iterate_succ_apply]
        exact hnz (k + 1) (by omega)
      · rw [← Function.iterate_succ_apply]
        exact hz

/-! ## 2. Bridging the `n`-fold iterate to the `frontForRun` fold

The `RFor` loop simulation (`enc_frontForRun_eq_reentry`, `front_loop_lsem_correct`) is
phrased over the *indexed* fold `frontForRun frontStep' n` (the `RFor` shape, where
each iteration is handed the loop counter `i`). The `RWhileNz` body takes no counter,
so its per-iteration transformer is index-free; the index-ignoring fold
`frontForRun (fun _ acc => frontStep acc) n` is exactly the `n`-fold iterate
`frontStep^[n]`. This bridge lets us drive the `RFor` emitted-loop
simulation from the while-loop's iterate denotation. -/

/-- The index-ignoring `frontForRun` fold is the `n`-fold `Function.iterate`: when the
    per-iteration transformer discards the loop counter (as the `RWhileNz` body does),
    `frontForRun` collapses to `frontStep^[n]`. -/
theorem frontForRun_const_eq_iterate (frontStep : RustState → RustState) (n : Nat)
    (rs : RustState) :
    frontForRun (fun _ acc => frontStep acc) n rs = (frontStep^[n]) rs := by
  induction n generalizing rs with
  | zero => rfl
  | succ m ih => rw [frontForRun_succ, Function.iterate_succ_apply', ih]

/-! ## 3. Capstone: the front `RWhileNz`'s lsem run = its `RustExec` denotation +
constant-time (for a PUBLIC guard)

We combine, for a front `while` loop `RWhileNz e body` with public guard `e`:

* `rustExec_rwhilenz_iterate` (§1): the front loop's big-step `RustExec` post-state is
  the `n`-fold iterate `frontStep^[n] rs`, where `n = c+1` is the **public guard
  trajectory length** (the guard nonzero for the first `c+1` iterations, zero at the
  `(c+1)`-th);
* the `RFor` emitted-loop simulation `front_loop_lsem_correct`, instantiated
  at the index-ignoring transformer `fun _ rs => frontStep rs` (the while body takes no
  counter). Its `lsem`-run half does not depend on the front construct being `RFor`
  rather than `RWhileNz` — it is the real emitted loop `loopProg` (the `loopLcmd`
  shape) run by `lsemFuel`, halting at the encoded `frontForRun` data, which by
  `frontForRun_const_eq_iterate` is the encoded iterate `frontStep^[c+1] rs`.

The public-guard CT hypothesis is the trajectory length being public (`n = c+1` fixed
by the public guard `e`), corresponding to `RFor`'s public static trip count and to
`cmdCT_RWhileNz`'s `lt e = .Public`. A SECRET guard leaks `n` and is NOT
constant-time — excluded by construction (out of scope). -/

/-- **`front_while_lsem_correct`.** For a front `while` loop `RWhileNz e body` with a
    **public guard** `e`, single-iteration body edge `frontStep` (`hbody`), encoded
    into the `JasminLsemLoop` loop simulation
    (`E : FrontLoopEncodes spec (fun _ rs => frontStep rs)`,
    starting at the loop entry data `enc rs = { sb with lpc := 1 }`), whose **public
    guard trajectory** has length `c+1` (`hnz`: the guard is nonzero for the first
    `c+1` iterations; `hz`: the guard hits `0` at the `(c+1)`-th) and whose emitted
    back-edge counter terminates after `c+1` body runs (`hterm`):

    * *(front denotation)* the front `RWhileNz`'s `RustExec` post-state is the
      `(c+1)`-fold iterate `frontStep^[c+1] rs` — the source `while`-loop meaning,
      driven by the public guard trajectory;
    * *(emitted lsem run)* the program-level `lsemFuel` trace of the **real emitted
      loop** `loopProg` (the `loopLR` / `loopLcmd` shape) from the loop entry halts at
      the `lsem` data whose lvm/lmem is the encoding of that front post-state — i.e.
      *the emitted loop computes the `while`-loop's source meaning*.

    The iteration count is bounded by the **public** guard trajectory length `c+1`
    (`hnz`/`hz`), never a secret. No `JasminIRToX86` edge, no `jasminc_preserves_ct`.

    Note: a SECRET guard `e` leaks `c+1` through the back-edge decision trace and is
    not constant-time; that case is out of scope — `cmdCT_RWhileNz`'s
    `lt e = .Public` excludes it. -/
theorem front_while_lsem_correct {N : Nat} {leafSpec : LeafSpec}
    (e : String) (body : LowCT) (frontStep : RustState → RustState)
    (hbody : ∀ (rs : RustState), RustExec N leafSpec body rs (frontStep rs))
    (fn : String) {w : Nat} (top : LLabel) {lbody : List LinstrR}
    (spec : LoopBodySpec w lbody) (sb : Lstate w) (c : Nat)
    (hterm : LoopTerminatesIn spec sb c)
    (E : FrontLoopEncodes spec (fun _ rs => frontStep rs)) (rs : RustState)
    (hstart : E.enc rs = { sb with lpc := 1 })
    (hnz : ∀ k < c + 1, ((frontStep^[k]) rs).rsScalar e ≠ 0)
    (hz : ((frontStep^[c + 1]) rs).rsScalar e = 0) :
    -- (front denotation) the front `RWhileNz`'s `RustExec` post-state is the iterate
    RustExec N leafSpec (.RWhileNz e body) rs ((frontStep^[c + 1]) rs)
    ∧
    -- (emitted lsem run) the real emitted loop halts at the lsem data whose lvm/lmem
    -- encodes that front post-state.
    (∃ t : Lstate w,
        lsemFuel (loopProg fn top lbody) ((c + 1) * (lbody.length + 1) + 1)
            { base := { sb with lpc := 0 }, lfn := fn }
          = some { base := t, lfn := fn }
      ∧ t.lvm = (E.enc ((frontStep^[c + 1]) rs)).lvm
      ∧ t.lmem = (E.enc ((frontStep^[c + 1]) rs)).lmem) := by
  refine ⟨rustExec_rwhilenz_iterate e body frontStep hbody (c + 1) rs hnz hz, ?_⟩
  -- the lsem run reuses the `RFor` emitted-loop machinery: the real emitted
  -- loop `loopProg` halts at the encoded reentry data (`loop_lsem_correct`), and the
  -- encoding of the front `frontForRun` post-state is that reentry data
  -- (`enc_frontForRun_eq_reentry`). The front fold here is the index-ignoring
  -- `frontForRun (fun _ rs => frontStep rs)`, which collapses to the `n`-fold iterate
  -- `frontStep^[c+1]` (`frontForRun_const_eq_iterate`). The while body takes no
  -- counter, so this does NOT require the (RFor-specific, here-unprovable) indexed
  -- body edge — only the shared lsem-run lemmas.
  refine ⟨{ spec.bodyStep ((reentry spec sb c).base) with lpc := 2 + lbody.length },
    loop_lsem_correct fn top spec sb c hterm, ?_, ?_⟩
  · rw [← frontForRun_const_eq_iterate frontStep (c + 1) rs,
      enc_frontForRun_eq_reentry E sb rs hstart (c + 1), reentry_succ_data]
  · rw [← frontForRun_const_eq_iterate frontStep (c + 1) rs,
      enc_frontForRun_eq_reentry E sb rs hstart (c + 1), reentry_succ_data]

/-! ### While-loop CT (robust): the front `RWhileNz`'s emitted leak is
state-independent — for a PUBLIC guard

The emitted loop's constant-time statement is the one for `RFor`: the back-edge
`Lcond (.reg "NZ") top` tests only the public counter (its leak is the constant
`branch`), and the body leaks only syntax — so the whole `loopLR` leak is the same
from any two states (`front_loop_lsem_robust` / `loopLR_lsemLeak_state_independent`).

This realises the source-level fact that the `while`-loop's guard is **public**
(`cmdCT_RWhileNz`'s `lt e = .Public`): the public guard makes the trip count, and the
per-iteration back-edge decision, a public observation. A SECRET guard would make the
number of back-edge `branch` leaks (= the iteration count `c+1`) secret-dependent —
not constant-time, and out of scope. -/

/-- **`front_while_lsem_robust`.** The front `while` loop's emitted leak is
    state-independent (constant-time): the real emitted loop `loopLR` leaks the same
    trace from any two `lsem` states, given the body's leak is state-independent
    (`hbodyLeak`) and always completes (`hbodySucc`). This is
    `loopLR_lsemLeak_state_independent` — the back-edge tests only the public guard
    counter. CT holds **precisely because the guard is public** (`cmdCT_RWhileNz`); a
    secret guard leaks the iteration count and is out of scope. -/
theorem front_while_lsem_robust {w : Nat} (top : LLabel) (lbody : List LinstrR)
    (hbodyLeak : ∀ (sb₁ sb₂ : Lstate w), lsemLeak lbody sb₁ = lsemLeak lbody sb₂)
    (hbodySucc : ∀ s : Lstate w, (lsemStraight lbody s).isSome) :
    ∀ s₁ s₂ : Lstate w,
      lsemLeak (loopLR "NZ" top lbody) s₁ = lsemLeak (loopLR "NZ" top lbody) s₂ :=
  fun s₁ s₂ => front_loop_lsem_robust top lbody hbodyLeak hbodySucc s₁ s₂

/-! ## 4. Combined capstone: the front `RWhileNz` — correct AND robust (constant-time)
for a PUBLIC guard

A single statement packaging the functional tie (§3) and the constant-time statement:
the front `while` loop `RWhileNz e body`'s emitted control flow, run by the real
labeled `lsem`, realises its `RustExec` source meaning AND is constant-time **under
the public-guard hypothesis** (the guard trajectory length `c+1` is public, the
analogue of `RFor`'s public static trip count and of `cmdCT_RWhileNz`'s `lt e = .Public`),
with no `JasminIRToX86` edge and no `jasminc_preserves_ct`. -/

/-- **`front_while_lsem_correct_and_robust`.** The front `while`-loop control-flow
    capstone, for a `RWhileNz e body` with a **PUBLIC guard** `e`:

    1. *(functional)* the front loop's `RustExec` post-state is the `(c+1)`-fold
       iterate `frontStep^[c+1] rs` — the source `while`-loop meaning — and the real
       emitted loop `loopProg`'s `lsem` run halts at the `lsem` data encoding it
       (`front_while_lsem_correct`). The iteration count `c+1` is bounded by the
       **public guard trajectory** (`hnz`: guard nonzero for the first `c+1` runs;
       `hz`: guard `0` at the `(c+1)`-th);
    2. *(robust / constant-time)* the emitted loop's leak is state-independent
       (`front_while_lsem_robust`) — the back-edge tests only the public guard
       counter.

    Both reuse the REAL emitted form (`loopLR` / `loopProg` = `loopLcmd` modulo the
    dropped `CMP`). The public-guard hypothesis (stated, not hidden) is the public
    trajectory length `c+1` (`LoopTerminatesIn` + `hnz`/`hz` on the public guard `e`).

    Note: A SECRET guard `e` leaks the iteration
    count `c+1` through the back-edge `branch` decision trace and is **not**
    constant-time; `cmdCT_RWhileNz`'s `lt e = .Public` requirement excludes it, and the
    robustness conjunct is asserted only under the public-guard discipline. No
    `JasminIRToX86` edge, no `jasminc_preserves_ct`. -/
theorem front_while_lsem_correct_and_robust {N : Nat} {leafSpec : LeafSpec}
    (e : String) (body : LowCT) (frontStep : RustState → RustState)
    (hbody : ∀ (rs : RustState), RustExec N leafSpec body rs (frontStep rs))
    (fn : String) {w : Nat} (top : LLabel) {lbody : List LinstrR}
    (spec : LoopBodySpec w lbody) (sb : Lstate w) (c : Nat)
    (hterm : LoopTerminatesIn spec sb c)
    (E : FrontLoopEncodes spec (fun _ rs => frontStep rs)) (rs : RustState)
    (hstart : E.enc rs = { sb with lpc := 1 })
    (hnz : ∀ k < c + 1, ((frontStep^[k]) rs).rsScalar e ≠ 0)
    (hz : ((frontStep^[c + 1]) rs).rsScalar e = 0)
    (hbodyLeak : ∀ (sb₁ sb₂ : Lstate w), lsemLeak lbody sb₁ = lsemLeak lbody sb₂)
    (hbodySucc : ∀ s : Lstate w, (lsemStraight lbody s).isSome) :
    -- (1) functional: front denotation = iterate, emitted lsem run encodes it
    (RustExec N leafSpec (.RWhileNz e body) rs ((frontStep^[c + 1]) rs)
      ∧ ∃ t : Lstate w,
          lsemFuel (loopProg fn top lbody) ((c + 1) * (lbody.length + 1) + 1)
              { base := { sb with lpc := 0 }, lfn := fn }
            = some { base := t, lfn := fn }
        ∧ t.lvm = (E.enc ((frontStep^[c + 1]) rs)).lvm
        ∧ t.lmem = (E.enc ((frontStep^[c + 1]) rs)).lmem)
    ∧
    -- (2) robust / constant-time (public guard): the emitted leak is state-independent
    (∀ s₁ s₂ : Lstate w,
      lsemLeak (loopLR "NZ" top lbody) s₁ = lsemLeak (loopLR "NZ" top lbody) s₂) :=
  ⟨front_while_lsem_correct e body frontStep hbody fn top spec sb c hterm E rs hstart hnz hz,
   front_while_lsem_robust top lbody hbodyLeak hbodySucc⟩

end CatCrypt.Crypto.SecureCompilation.VIR.FrontWhileLsem

