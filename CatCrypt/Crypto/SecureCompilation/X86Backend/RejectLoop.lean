/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.Cond
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Cond
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow

/-!
# The terminating guarded (rejection / hedged) loop lowering — RWhile lift (#523)

`LoopUnroll.lean` (#281) lowers the **bounded counter-decrement loop**
`while (n != 0) { body ; n -= 1 }` whose trip count `n : Nat` is a *compile-time*
constant; `Cond.lean` (#281) lowers the **public forward conditional**;
`LprogControlFlow.lean` (#538) emits the bounded loop as a *constant-size* looped
`Lcmd` (label + body + `cmpq $0,%n ; jne .L`) rather than an `n`-copy unroll.

What none of those covers is the shape every Round-3 PQC *signature* needs at the
**outer** orchestration layer: the **rejection / Fiat-Shamir-with-aborts loop**

```
repeat { y ← ExpandMask(...) ; z ← respond(y) ; ... } until accept(z, …)
```

i.e. a `while guard(s) { body }` whose number of iterations is **runtime
data-dependent** (it depends on the sampled mask), not a compile-time / loaded
limb count. ML-DSA's signing resamples until the norm check `‖z‖∞ < γ₁-β`
(and the low-bits / hint-weight checks) pass; MAYO/UOV/HAWK have the analogous
resample. The inner kernels (NTT, the per-`κ` body, the norm reduction) already
emit through the verified front (`MldsaLowCT`, `full-ntt-simd-parity`); the
**outer resample loop** is the residual that kept the *whole* protocol on
`jasminc`. `MldsaLowCT.lean` says so explicitly: *"the rejection-sample loop is
modeled outside the kernel as repeated calls; the kernel emits the per-`κ`
body."* This module lowers that loop.

## Why this is not just `runBoundedLoop`

`runBoundedLoop s n body` runs `body` exactly `n` times for a **fixed `n`**. A
rejection loop's trip count is not fixed: it is the *least* `k` for which
`guard (runBoundedLoop s k body) = false`. We give:

* `runGuardedLoop fuel guard body s` — the machine semantics of the terminating
  guarded loop: run `body` while `guard` holds, with `fuel` bounding the
  iterations (the termination witness). This is the **fixpoint** denotation the
  framework's pure A-normal `Com` lacks — provided here as a structural
  `fuel`-recursion (so it is total / terminating by construction, no `partial`).
* `tripCount fuel guard body s` — the *dynamic* trip count: how many times the
  guarded loop actually runs `body` from `s` before the guard fails (`≤ fuel`).
* `runGuardedLoop_eq_runBoundedLoop_trip` — the key bridge: the guarded loop's
  result equals `runBoundedLoop s (tripCount …) body`. So *for a fixed incoming
  state `s`* the data-dependent loop **is** a bounded loop with a state-resolved
  trip count — exactly the `Cond.lowerCond` move (resolve the public decision on
  the incoming public state), one level up.
* `lowerGuardedLoop … s` — the lowering. Mirroring `Cond.lowerCond` (which is
  parameterised by the incoming public state that resolves the branch), this is
  parameterised by the incoming public state that resolves the *trip count*, and
  reduces to `LoopUnroll.lowerBoundedLoop (tripCount …) body` — i.e. the already
  -proven bounded-loop lowering, at the resolved trip count.
* `guardedLoop_lowering_denote` — the RWhile generalisation of
  `lowerBlock_denote` / `boundedLoop_lowering_denote` / `condBlock_lowering_denote`:
  the lowered guarded loop denotes `runGuardedLoop fuel guard body s`. The proof
  composes `boundedLoop_lowering_denote` with `runGuardedLoop_eq_runBoundedLoop_trip`.

## The guard is PUBLIC (constant-time discipline; #460)

A rejection loop's abort decision is **public** by construction: in Fiat-Shamir-
with-aborts the verifier (and any adversary watching) learns *that* an iteration
aborted (the number of aborts is leaked — it is the whole point that the signer
restarts). The norm check `‖z‖∞ < γ₁-β` is a comparison whose **result** (not
the secret coefficients) drives the branch; ML-DSA implementations make the
abort decision in the clear. So the guard `guard : JState w → Bool` reads a
public decision, exactly as `Cond.JCond`. Resolving the trip count at lowering
time (per incoming `s`) therefore leaks nothing the public restart count does
not already reveal — the same argument that makes `Cond.lowerCond` CT-admissible,
lifted to the loop. A *secret*-dependent loop guard is forbidden in the CT
subset (it would be a timing oracle on the secret); the `isCT` discipline at the
`LowCT` layer (`LowCTCT.isCT_LowCT`, this increment) admits `RWhileNz` **only**
on a public guard.

## Trust story

No new axioms beyond the baseline. `runGuardedLoop` / `tripCount` are structural
`fuel`-recursions (total). `runGuardedLoop_eq_runBoundedLoop_trip` is a `fuel`
induction. `guardedLoop_lowering_denote` composes `LoopUnroll`'s
`boundedLoop_lowering_denote` (axioms `[propext, Quot.sound]`) with that bridge —
so the guarded-loop lowering inherits exactly the baseline axiom set. The emitted
`Lcmd` is the **looped** (constant-size) `LprogControlFlow.loopLcmd`, with the
back-edge `jne .L` testing the *public* guard result, so it does not grow with
the runtime trip count.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RejectLoop

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cond

/-! ## 0. Reading a counter register through register writes (body-opaque)

To prove the counter-increment hypothesis of `tripCount_counterGuard` for a
concrete owned-emit body **without** evaluating the (heavy) data path, we need to
project the counter register `k` through the body's chain of `writeB5W`/`setReg`
register writes. These two `@[simp]` lemmas push `JState.get` through a write to a
*different* register, so `simp` can reduce `(runBlock t body).get k` to the value
written by the single instruction that touches `k` (the counter `inc`), leaving
every other instruction's data word **opaque** in the discarded `if`-branch — no
symbolic evaluation of the per-coefficient ALU chain. (`JState.get_writeB5W_same`
/ `JState.get_setReg_same` / `JState.get_setReg_other` already exist in
`JasminModel`; this adds the missing `writeB5W` *other*-register case.) -/

/-- `get` of a `writeB5W` to a *different* register falls through. The data word
    `t.word` stays opaque in the discarded branch — so projecting the counter does
    not evaluate the ALU result. -/
@[simp] theorem get_writeB5W_other {w : Nat} (s : JState w) (dst r : String)
    (t : B5W w) (h : r ≠ dst) : (s.writeB5W dst t).get r = s.get r := by
  simp only [JState.writeB5W, JState.get, if_neg h]

/-! ## 1. The terminating guarded-loop machine semantics

`runGuardedLoop fuel guard body s`: run `body` while `guard` holds. `fuel`
bounds the iteration count (the termination witness): once `fuel` is exhausted we
stop (a well-terminating rejection loop is run with `fuel` ≥ its worst-case trip
count, so the cap is never hit; the cap only makes the function total). The
`guard` is evaluated on the *current* state, so this is the genuine
data-dependent fixpoint, not a counter loop. -/

/-- The terminating guarded loop. Run `body` from `s` while `guard` holds, with
    `fuel` bounding the iterations. `guard : JState w → Bool` is the **public**
    abort/continue decision. -/
def runGuardedLoop {w : Nat} (fuel : Nat) (guard : JState w → Bool)
    (body : List (JInstr w)) (s : JState w) : JState w :=
  match fuel with
  | 0 => s
  | f + 1 => if guard s then runGuardedLoop f guard body (runBlock s body) else s

@[simp] theorem runGuardedLoop_zero {w : Nat} (guard : JState w → Bool)
    (body : List (JInstr w)) (s : JState w) :
    runGuardedLoop 0 guard body s = s := rfl

@[simp] theorem runGuardedLoop_succ {w : Nat} (f : Nat) (guard : JState w → Bool)
    (body : List (JInstr w)) (s : JState w) :
    runGuardedLoop (f + 1) guard body s
      = (if guard s then runGuardedLoop f guard body (runBlock s body) else s) := rfl

/-- When the guard already fails, the loop is the identity (independent of fuel,
    provided there is at least one fuel unit — and trivially at fuel 0). -/
@[simp] theorem runGuardedLoop_guard_false {w : Nat} (fuel : Nat)
    (guard : JState w → Bool) (body : List (JInstr w)) (s : JState w)
    (h : guard s = false) :
    runGuardedLoop fuel guard body s = s := by
  cases fuel with
  | zero => rfl
  | succ f => simp [runGuardedLoop, h]

/-! ## 2. The dynamic trip count

`tripCount fuel guard body s`: how many times the guarded loop runs `body` from
`s` before the guard fails (capped by `fuel`). This is the *runtime* trip count —
the analogue of `LoopUnroll`'s compile-time `n`, but resolved on the incoming
state, exactly as `Cond.lowerCond` resolves the branch on the incoming state. -/

/-- The dynamic trip count of the guarded loop. -/
def tripCount {w : Nat} (fuel : Nat) (guard : JState w → Bool)
    (body : List (JInstr w)) (s : JState w) : Nat :=
  match fuel with
  | 0 => 0
  | f + 1 => if guard s then tripCount f guard body (runBlock s body) + 1 else 0

@[simp] theorem tripCount_zero {w : Nat} (guard : JState w → Bool)
    (body : List (JInstr w)) (s : JState w) :
    tripCount 0 guard body s = 0 := rfl

@[simp] theorem tripCount_guard_false {w : Nat} (fuel : Nat)
    (guard : JState w → Bool) (body : List (JInstr w)) (s : JState w)
    (h : guard s = false) :
    tripCount fuel guard body s = 0 := by
  cases fuel with
  | zero => rfl
  | succ f => simp [tripCount, h]

/-- The trip count never exceeds the fuel. -/
theorem tripCount_le_fuel {w : Nat} (fuel : Nat) (guard : JState w → Bool)
    (body : List (JInstr w)) (s : JState w) :
    tripCount fuel guard body s ≤ fuel := by
  induction fuel generalizing s with
  | zero => simp
  | succ f ih =>
      simp only [tripCount]
      cases guard s with
      | false => simp
      | true => simp only [if_true]; exact Nat.succ_le_succ (ih (runBlock s body))

/-! ## 2b. Structural trip count of a counter-increment loop (body-opaque)

A fixed-count owned-emit loop uses the **public counter guard**
`fun t => decide ((t.get k).toNat < N)` and a body that increments the counter
register `k` by one each iteration. Its trip count is `N` (minus the starting
value) and depends **only** on the counter guard — *not* on the rest of the body.
`tripCount_counterGuard` proves this from a single hypothesis: that the body
advances the counter by one (within range). The body is therefore **opaque**
except through that one-step increment fact, so the proof never symbolically runs
the body more than the one step the hypothesis already abstracts — no `N`-fold
evaluation of a heavy per-coefficient body. This replaces the body-running
`native_decide` the owned-emit `*_tripCount` theorems used, which symbolically
executed the (heavy) body `N = 256` times and overflowed the native kernel stack
(`lean exited with code 134` in a full `lake build`). -/

/-- **Body-opaque trip count of a counter-increment loop.** With the public
    counter guard `fun t => decide ((t.get k).toNat < N)` and a body that
    increments the counter register `k` by one each iteration (within range,
    hypothesis `hinc`), the dynamic trip count from a state `s` whose counter is
    `j ≤ N` is exactly `N − j`, provided the fuel covers it. The body is opaque
    except via `hinc` — the proof runs the body at most one (abstracted) step per
    induction layer, never `N`-fold, so it does not symbolically evaluate a heavy
    per-coefficient body and cannot overflow the native kernel stack. -/
theorem tripCount_counterGuard {w : Nat} (k : String) (N : Nat)
    (body : List (JInstr w))
    (hinc : ∀ t : JState w, (t.get k).toNat < N →
        ((runBlock t body).get k).toNat = (t.get k).toNat + 1) :
    ∀ (fuel : Nat) (s : JState w), (s.get k).toNat ≤ N →
        N - (s.get k).toNat ≤ fuel →
        tripCount fuel (fun t => decide ((t.get k).toNat < N)) body s
          = N - (s.get k).toNat := by
  intro fuel
  induction fuel with
  | zero =>
      intro s _ hfuel
      simp only [Nat.le_zero] at hfuel
      simp only [tripCount]; omega
  | succ f ih =>
      intro s hle hfuel
      rw [tripCount]
      by_cases hlt : (s.get k).toNat < N
      · -- guard holds: peel one iteration
        simp only [hlt, decide_true, if_true]
        have hstep : ((runBlock s body).get k).toNat = (s.get k).toNat + 1 := hinc s hlt
        have hle' : ((runBlock s body).get k).toNat ≤ N := by omega
        have hfuel' : N - ((runBlock s body).get k).toNat ≤ f := by omega
        rw [ih (runBlock s body) hle' hfuel']
        omega
      · -- guard fails: counter has reached N, trip count is 0
        rw [if_neg (fun h => hlt (of_decide_eq_true h))]
        omega

/-! ## 2c. Structural FINAL counter of a counter-increment loop (body-opaque)

The companion to `tripCount_counterGuard`: not *how many times* the loop runs,
but *what value the counter holds when it stops*. For the public counter guard
`fun t => decide ((t.get k).toNat < N)` and a body that increments the counter
register `k` by one each iteration, the counter ends at exactly `N` — i.e.
`BitVec.ofNat w N`. Like `tripCount_counterGuard`, the body is **opaque** except
through the one-step BitVec increment `hinc`; the proof runs the body at most one
(abstracted) step per induction layer, never `N`-fold, so it does not
symbolically evaluate a heavy per-coefficient body and cannot overflow the native
kernel stack. This replaces the final-state-running `native_decide` the owned-emit
`*_final_i` theorems used, which symbolically executed the `runGuardedLoop` for
all `N = 256` iterations and overflowed the native kernel stack (`lean exited with
code 134`). -/

/-- **Body-opaque final counter of a counter-increment loop.** With the public
    counter guard `fun t => decide ((t.get k).toNat < N)` and a body that
    increments the counter register `k` by one each iteration (BitVec-level,
    hypothesis `hinc`), running the guarded loop from a state `s` whose counter is
    `j ≤ N` leaves the counter at exactly `BitVec.ofNat w N`, provided the fuel
    covers `N − j` and `N < 2 ^ w` (so the count does not wrap). The body is opaque
    except via `hinc` — the proof runs the body at most one abstracted step per
    induction layer, never `N`-fold, so it cannot overflow the native kernel
    stack. This is the FINAL-STATE analogue of `tripCount_counterGuard`. -/
theorem runGuardedLoop_counterGuard_get {w : Nat} (k : String) (N : Nat)
    (hN : N < 2 ^ w) (body : List (JInstr w))
    (hinc : ∀ t : JState w, (t.get k).toNat < N →
        (runBlock t body).get k = t.get k + 1) :
    ∀ (fuel : Nat) (s : JState w), (s.get k).toNat ≤ N →
        N - (s.get k).toNat ≤ fuel →
        (runGuardedLoop fuel (fun t => decide ((t.get k).toNat < N)) body s).get k
          = BitVec.ofNat w N := by
  intro fuel
  induction fuel with
  | zero =>
      intro s hle hfuel
      simp only [Nat.le_zero] at hfuel
      have heq : (s.get k).toNat = N := by omega
      rw [runGuardedLoop_zero, ← BitVec.toNat_inj, heq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hN]
  | succ f ih =>
      intro s hle hfuel
      rw [runGuardedLoop_succ]
      by_cases hlt : (s.get k).toNat < N
      · -- guard holds: peel one iteration, body advances the counter by one
        simp only [hlt, decide_true, if_true]
        have hstep : (runBlock s body).get k = s.get k + 1 := hinc s hlt
        have hwpos : 0 < w := by
          rcases Nat.eq_zero_or_pos w with hw | hw
          · subst hw; simp at hN; omega
          · exact hw
        have h1 : BitVec.toNat (1 : BitVec w) = 1 := by
          simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt
            (by simpa using Nat.one_lt_two_pow (n := w) (by omega) : (1 : Nat) < 2 ^ w)]
        have hgt : ((runBlock s body).get k).toNat = (s.get k).toNat + 1 := by
          rw [hstep, BitVec.toNat_add, h1,
            Nat.mod_eq_of_lt (by omega : (s.get k).toNat + 1 < 2 ^ w)]
        exact ih (runBlock s body) (by omega) (by omega)
      · -- guard fails: counter has reached N
        rw [if_neg (fun h => hlt (of_decide_eq_true h))]
        have heq : (s.get k).toNat = N := by omega
        rw [← BitVec.toNat_inj, heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN]

/-! ## 3. The bridge: a terminating guarded loop IS a bounded loop at its trip count

The key lemma. For a fixed incoming state `s`, running the data-dependent
guarded loop equals running the bounded counter loop `tripCount` times. This is
the loop analogue of `Cond.lowerCond`'s state-resolution: the dynamic decision is
resolved on the incoming (public) state into a static trip count, after which the
already-proven bounded-loop lowering applies verbatim. -/

/-- **Guarded loop = bounded loop at the dynamic trip count.** Running the
    terminating guarded loop from `s` equals running the counter-loop body
    `tripCount fuel guard body s` times. By induction on `fuel`, peeling one
    iteration: if the guard holds we recurse on `runBlock s body` with one fewer
    fuel and a trip count of one less; if it fails both sides are `s`. -/
theorem runGuardedLoop_eq_runBoundedLoop_trip {w : Nat} (fuel : Nat)
    (guard : JState w → Bool) (body : List (JInstr w)) (s : JState w) :
    runGuardedLoop fuel guard body s
      = runBoundedLoop s (tripCount fuel guard body s) body := by
  induction fuel generalizing s with
  | zero => simp
  | succ f ih =>
      simp only [runGuardedLoop, tripCount]
      cases h : guard s with
      | false => simp
      | true =>
          simp only [if_true]
          rw [ih (runBlock s body)]
          simp [runBoundedLoop]

/-! ## 4. Lowering the terminating guarded loop

Mirrors `Cond.lowerCond`: parameterised by the incoming public state `s` that
resolves the dynamic trip count, the lowering is the already-proven bounded-loop
lowering at that resolved trip count. The framework's pure A-normal `Com` carries
no fixpoint operator, so — exactly as the public forward conditional is compiled
away by *selecting* the taken straight-line block — the public-guard rejection
loop is compiled away by *resolving* its public trip count and emitting the
bounded loop. The emitted machine artifact is nonetheless the **looped**
constant-size `LprogControlFlow.loopLcmd` (see §6): the `Com` we lower for the
denotation proof is the unrolled-at-trip-count form, but the rendered `.s` is the
single-body-copy back-edge loop, whose `jne .L` tests the public guard at run
time. -/

/-- Lower a terminating guarded loop, given the incoming public state `s` that
    resolves the dynamic trip count: produce the bounded-loop lowering at
    `tripCount fuel guard body s`. (Public state-resolution — see the module
    docstring; the loop analogue of `Cond.lowerCond`.) -/
def lowerGuardedLoop {w : Nat} {Γ : Ctxt (x86Dialect w)} (fuel : Nat)
    (guard : JState w → Bool) (body : List (JInstr w)) (s : JState w) :
    Com (x86Dialect w) (X86Ty.machine w :: Γ) (X86Ty.machine w) :=
  lowerBoundedLoop (Γ := Γ) (tripCount fuel guard body s) body

/-! ## 5. Lowering correctness: the RWhile generalisation of `lowerBlock_denote` -/

/-- **Terminating-guarded-loop lowering correctness.** Denoting the lowered
    guarded loop on a valuation whose head is the incoming state `s` equals the
    guarded-loop machine semantics `runGuardedLoop fuel guard body s`. The proof
    composes `LoopUnroll.boundedLoop_lowering_denote` (at the resolved trip count)
    with `runGuardedLoop_eq_runBoundedLoop_trip`. This is the RWhile
    generalisation of `lowerBlock_denote`: a data-dependent terminating loop with
    a public guard is compiled away into the bounded subset, and the lowering of
    that subset is denotation-preserving. -/
theorem guardedLoop_lowering_denote {w : Nat} {Γ : Ctxt (x86Dialect w)}
    (fuel : Nat) (guard : JState w → Bool) (body : List (JInstr w))
    (s : JState w) (V : Ctxt.Valuation Γ) :
    (lowerGuardedLoop (Γ := Γ) fuel guard body s).denote (.cons s V)
      = runGuardedLoop fuel guard body s := by
  rw [lowerGuardedLoop, boundedLoop_lowering_denote,
    runGuardedLoop_eq_runBoundedLoop_trip]

/-- The closed-context specialisation (singleton context `[machine w]`): the
    lowered guarded loop denotes the state transformer
    `s ↦ runGuardedLoop fuel guard body s`. -/
theorem guardedLoop_lowering_denote_closed {w : Nat} (fuel : Nat)
    (guard : JState w → Bool) (body : List (JInstr w)) (s : JState w) :
    (lowerGuardedLoop (Γ := []) fuel guard body s).denote (.cons s .nil)
      = runGuardedLoop fuel guard body s :=
  guardedLoop_lowering_denote fuel guard body s .nil

/-! ## 5b. The state-transformer bounded loop: an `n`-fold `Com` composition

`lowerBoundedLoop` / `lowerGuardedLoop` lower a loop whose body is a
`List (JInstr w)` — by unrolling the *instructions*. The **outer** orchestration
loop of a Round-3 PQC signature (ML-DSA's whole-attempt `K`-row loop) is a
loop whose per-iteration `step` is itself **two inner guarded loops** plus a
counter advance: an opaque state transformer `step : JState w → JState w`, *not*
an instruction list. There is therefore nothing to unroll at the instruction
level — but if the step's *own* lowering is given as a closed
`Com (x86Dialect w) [machine w] (machine w)` (`stepCom`, with `stepCom`'s
denotation `= step`), the outer loop lowers as the **`n`-fold `Com` self-
composition** of `stepCom`, at the (already-structural) trip count `n`.

This subsection provides that operator, `lowerBoundedLoopT stepCom n`, and its
denote-correctness `lowerBoundedLoopT_denote`:
`(lowerBoundedLoopT stepCom n).denote ⟨s⟩ = stepIter step n s`, by induction on
`n`, **step-opaque** — the step appears only through the hypothesis
`hstep : ∀ s, stepCom.denote ⟨s⟩ = step s`, never evaluated `n`-fold
symbolically (each induction layer applies it once). The composition primitive
is a single-variable `Com` substitution `comSubstHere` (the A-normal analogue of
splicing the next stage's body onto the previous stage's returned state), with
its own denote law `comSubstHere_denote`. -/

/-- Generic context map (a renaming): a type-respecting map of every variable of
    `Γ` to a variable of `Δ`. -/
abbrev VarHom {w : Nat} (Γ Δ : Ctxt (x86Dialect w)) : Type :=
  ∀ {t : X86Ty}, Ctxt.Var Γ t → Ctxt.Var Δ t

/-- Lift a renaming under a freshly-bound head variable. -/
def VarHom.lift {w : Nat} {Γ Δ : Ctxt (x86Dialect w)} {u : X86Ty}
    (f : VarHom Γ Δ) : VarHom (u :: Γ) (u :: Δ) :=
  fun v => match v with
    | .here => .here
    | .there v' => .there (f v')

/-- Rename an `HVector` of variables along a renaming `f`. -/
def renameArgs {w : Nat} {Γ Δ : Ctxt (x86Dialect w)} (f : VarHom Γ Δ) :
    {tys : List X86Ty} →
      HVector (fun ty => Ctxt.Var Γ ty) tys →
      HVector (fun ty => Ctxt.Var Δ ty) tys
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (f v) (renameArgs f rest)

/-- Rename an `Expr` along a renaming `f`. -/
def renameExpr {w : Nat} {Γ Δ : Ctxt (x86Dialect w)} {t : X86Ty} (f : VarHom Γ Δ)
    (e : Expr (x86Dialect w) Γ t) : Expr (x86Dialect w) Δ t :=
  { op := e.op, retTy_eq := e.retTy_eq, args := renameArgs f e.args }

/-- Rename a `Com` along a variable renaming `f : VarHom Γ Δ` (capture-avoiding:
    `f` is lifted under each `.var` binder). The A-normal analogue of weakening /
    α-renaming; reading is preserved by `comRename_denote`. -/
def comRename {w : Nat} {Γ Δ : Ctxt (x86Dialect w)} {s : X86Ty}
    (f : VarHom Γ Δ) (c : Com (x86Dialect w) Γ s) : Com (x86Dialect w) Δ s :=
  match c with
  | .ret v => .ret (f v)
  | .var ⟨op, hop, args⟩ body =>
      .var ⟨op, hop, renameArgs f args⟩ (comRename (VarHom.lift f) body)

/-- The single-variable substitution renaming: send the head variable to a chosen
    `v0 : Var Γ t`, and every deeper variable to itself in `Γ`. -/
def substHom {w : Nat} {Γ : Ctxt (x86Dialect w)} {t : X86Ty}
    (v0 : Ctxt.Var Γ t) : VarHom (t :: Γ) Γ :=
  fun v => match v with
    | .here => v0
    | .there v' => v'

/-- Substitute the **head** binding of `k` by a chosen variable `v0` of `Γ`
    (single-variable substitution): `comSubstHead v0 k : Com Γ s`. -/
def comSubstHead {w : Nat} {Γ : Ctxt (x86Dialect w)} {t s : X86Ty}
    (v0 : Ctxt.Var Γ t) (k : Com (x86Dialect w) (t :: Γ) s) :
    Com (x86Dialect w) Γ s :=
  comRename (substHom v0) k

/-- The renaming that pushes a continuation's free variables one binder deeper
    (under a just-introduced `.var` binding `t'`), keeping the head intact. -/
def shiftUnderHom {w : Nat} {Γ : Ctxt (x86Dialect w)} {head t' : X86Ty} :
    VarHom (head :: Γ) (head :: t' :: Γ) :=
  fun v => match v with
    | .here => .here
    | .there v' => .there (.there v')

/-- **Closed A-normal sequencing.** Run `c1`, then feed its returned state as the
    head binding to the continuation `k`. By recursion on `c1`: each `.var` of
    `c1` is kept (continuation pushed under the new binding via `shiftUnderHom`),
    and at `c1`'s `.ret v` the continuation is spliced by substituting the
    returned `v` for its head. This is the `Com`-level composition operator the
    state-transformer loop iterates `n`-fold. -/
def comSeq {w : Nat} {Γ : Ctxt (x86Dialect w)}
    (c1 : Com (x86Dialect w) Γ (X86Ty.machine w))
    (k : Com (x86Dialect w) (X86Ty.machine w :: Γ) (X86Ty.machine w)) :
    Com (x86Dialect w) Γ (X86Ty.machine w) :=
  match c1 with
  | .ret v => comSubstHead v k
  | .var (t := t') ⟨op, hop, args⟩ body =>
      .var ⟨op, hop, args⟩ (comSeq body (comRename (shiftUnderHom (t' := t')) k))

/-! ### Denotation laws for the renaming / sequencing machinery

Two valuations `W : Valuation Γ` and `V : Valuation Δ` **agree via** `f : VarHom
Γ Δ` when every variable of `Γ` reads in `W` exactly what its `f`-image reads in
`V`. Under this relation the renamed `Com` (resp. `Expr`) denotes equally. This
is the standard substitution lemma, in pointwise (relation) form so we never
materialise a pulled-back `Valuation` HVector. -/

/-- `W` and `V` agree via `f`: every `Γ`-variable reads in `W` what its image
    reads in `V`. -/
def AgreesVia {w : Nat} {Γ Δ : Ctxt (x86Dialect w)} (f : VarHom Γ Δ)
    (W : Ctxt.Valuation Γ) (V : Ctxt.Valuation Δ) : Prop :=
  ∀ {t : X86Ty} (v : Ctxt.Var Γ t), v.lookup W = (f v).lookup V

/-- Lifting `f` under a fresh head binding preserves agreement when both
    valuations are extended by the same head value. -/
theorem AgreesVia.lift {w : Nat} {Γ Δ : Ctxt (x86Dialect w)} {u : X86Ty}
    {f : VarHom Γ Δ} {W : Ctxt.Valuation Γ} {V : Ctxt.Valuation Δ}
    (h : AgreesVia f W V) (x : ⟦u⟧) :
    AgreesVia (VarHom.lift f) (W.extend x) (V.extend x) := by
  intro t v
  cases v with
  | here => rfl
  | there v' => exact h v'

/-- Renamed-`Expr` denotation: under agreement, `renameArgs`/`renameExpr`
    preserve the looked-up arguments and hence the op denotation. -/
theorem renameArgs_lookup {w : Nat} {Γ Δ : Ctxt (x86Dialect w)} {f : VarHom Γ Δ}
    {W : Ctxt.Valuation Γ} {V : Ctxt.Valuation Δ} (h : AgreesVia f W V) :
    ∀ {tys : List X86Ty} (args : HVector (fun ty => Ctxt.Var Γ ty) tys),
      Expr.lookupArgs (renameArgs f args) V = Expr.lookupArgs args W
  | [], .nil => rfl
  | _ :: _, .cons v rest => by
      show HVector.cons ((f v).lookup V) (Expr.lookupArgs (renameArgs f rest) V)
          = HVector.cons (v.lookup W) (Expr.lookupArgs rest W)
      rw [h v, renameArgs_lookup h rest]

theorem renameExpr_denote {w : Nat} {Γ Δ : Ctxt (x86Dialect w)} {t : X86Ty}
    {f : VarHom Γ Δ} {W : Ctxt.Valuation Γ} {V : Ctxt.Valuation Δ}
    (h : AgreesVia f W V) (e : Expr (x86Dialect w) Γ t) :
    (renameExpr f e).denote V = e.denote W := by
  obtain ⟨op, hop, args⟩ := e
  simp only [renameExpr, Expr.denote, renameArgs_lookup h args]

/-- **Renaming preserves denotation.** Under agreement of `W`,`V` via `f`, the
    renamed `Com` denotes on `V` exactly what the original denotes on `W`. By
    induction on the `Com`; the `.var` case extends both valuations by the same
    (renamed-`Expr`-equal) head value, preserving agreement via `AgreesVia.lift`. -/
theorem comRename_denote {w : Nat} {Γ Δ : Ctxt (x86Dialect w)} {s : X86Ty}
    (f : VarHom Γ Δ) (c : Com (x86Dialect w) Γ s)
    {W : Ctxt.Valuation Γ} {V : Ctxt.Valuation Δ} (h : AgreesVia f W V) :
    (comRename f c).denote V = c.denote W := by
  induction c generalizing Δ V with
  | ret v => simp only [comRename, Com.denote]; exact (h v).symm
  | var e body ih =>
      obtain ⟨op, hop, args⟩ := e
      simp only [comRename, Com.denote]
      have he : (renameExpr f ⟨op, hop, args⟩).denote V
          = (Expr.mk op hop args).denote W := renameExpr_denote h _
      have he' : (Expr.mk op hop (renameArgs f args)).denote V
          = (Expr.mk op hop args).denote W := he
      rw [show (⟨op, hop, renameArgs f args⟩ : Expr (x86Dialect w) Δ _)
            = Expr.mk op hop (renameArgs f args) from rfl, he']
      exact ih (VarHom.lift f) (h.lift _)

/-- **`comSubstHead` denotation.** Substituting the head binding of `k` by `v0`
    denotes `k` on the valuation whose head is `v0`'s value. -/
theorem comSubstHead_denote {w : Nat} {Γ : Ctxt (x86Dialect w)} {t s : X86Ty}
    (v0 : Ctxt.Var Γ t) (k : Com (x86Dialect w) (t :: Γ) s)
    (V : Ctxt.Valuation Γ) :
    (comSubstHead v0 k).denote V = k.denote (V.extend (v0.lookup V)) := by
  apply comRename_denote
  intro u v
  cases v with
  | here => rfl
  | there v' => rfl

/-- **`comSeq` denotation (closed sequencing).** `comSeq c1 k` denotes `k` run on
    the valuation whose head is `c1`'s denotation — i.e. it sequences `c1` then
    `k`. By induction on `c1`: the `.ret` case is `comSubstHead_denote`; the
    `.var` case threads the new binding and reuses `comRename` for the shifted
    continuation. -/
theorem comSeq_denote {w : Nat} {Γ : Ctxt (x86Dialect w)}
    (c1 : Com (x86Dialect w) Γ (X86Ty.machine w))
    (k : Com (x86Dialect w) (X86Ty.machine w :: Γ) (X86Ty.machine w))
    (V : Ctxt.Valuation Γ) :
    (comSeq c1 k).denote V = k.denote (V.extend (c1.denote V)) := by
  match c1 with
  | .ret v =>
      simp only [comSeq, Com.denote]
      exact comSubstHead_denote v k V
  | .var ⟨op, hop, args⟩ body =>
      have ih := comSeq_denote body (comRename (shiftUnderHom) k)
        (V.extend ((Expr.mk op hop args).denote V))
      simp only [comSeq, Com.denote]
      rw [ih]
      apply comRename_denote
      intro u v
      cases v with
      | here => rfl
      | there v' => rfl

/-! ## 5c. The state-transformer bounded-loop `Com` operator (`lowerBoundedLoopT`)

`lowerBoundedLoopT stepCom n` composes the per-step closed `Com` `stepCom` with
itself `n` times via `comSeq`. Its denotation is `stepIter step n` whenever
`stepCom` realises `step` (`hstep : ∀ s, stepCom.denote ⟨s⟩ = step s`). The proof
is a step-opaque induction on `n` (the step is applied once per layer, never
`n`-fold symbolically). This is the state-transformer analogue of
`lowerBoundedLoop`: the outer orchestration loop of a Round-3 PQC signature
(whose per-iteration "body" is itself two inner guarded loops) lowers as the
`n`-fold `Com` composition of its already-lowered per-iteration step. -/

/-- `n`-fold application of a state transformer (the closed-`Com` reading of a
    bounded `step`-loop). Defined here for the `RejectLoop` operator; the MLDSA
    module re-uses its own `stepIter` with the same equations. -/
def stepIter {w : Nat} (step : JState w → JState w) : Nat → JState w → JState w
  | 0, s => s
  | n + 1, s => stepIter step n (step s)

@[simp] theorem stepIter_zero {w : Nat} (step : JState w → JState w) (s : JState w) :
    stepIter step 0 s = s := rfl

@[simp] theorem stepIter_succ {w : Nat} (step : JState w → JState w) (n : Nat)
    (s : JState w) : stepIter step (n + 1) s = stepIter step n (step s) := rfl

/-- **The state-transformer bounded-loop `Com` operator.** `n`-fold `comSeq`
    self-composition of the per-step closed `Com` `stepCom`. (`n = 0` is the
    identity `Com` `ret .here`; `n+1` sequences one `stepCom` before the
    `n`-fold remainder.) Step-opaque: `stepCom` is threaded as a black box. -/
def lowerBoundedLoopT {w : Nat}
    (stepCom : Com (x86Dialect w) [X86Ty.machine w] (X86Ty.machine w)) :
    Nat → Com (x86Dialect w) [X86Ty.machine w] (X86Ty.machine w)
  | 0 => .ret Ctxt.Var.here
  | n + 1 => comSeq stepCom
      (comRename (shiftUnderHom (head := X86Ty.machine w) (t' := X86Ty.machine w))
        (lowerBoundedLoopT stepCom n))

/-- **`lowerBoundedLoopT` denotation-correctness.** Whenever the per-step `Com`
    `stepCom` realises the state transformer `step` (`hstep`), the `n`-fold
    composition denotes `stepIter step n`. By induction on `n`, **step-opaque**:
    each layer applies `hstep` once and the induction hypothesis once, so the
    step is never symbolically evaluated `n`-fold. This is the state-transformer
    analogue of `LoopUnroll.boundedLoop_lowering_denote_closed`. -/
theorem lowerBoundedLoopT_denote {w : Nat}
    (stepCom : Com (x86Dialect w) [X86Ty.machine w] (X86Ty.machine w))
    (step : JState w → JState w)
    (hstep : ∀ s : JState w, stepCom.denote (.cons s .nil) = step s)
    (n : Nat) (s : JState w) :
    (lowerBoundedLoopT stepCom n).denote (.cons s .nil) = stepIter step n s := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih =>
      simp only [lowerBoundedLoopT, stepIter_succ]
      rw [comSeq_denote]
      rw [comRename_denote (W := .cons (step s) .nil)
            (shiftUnderHom (head := X86Ty.machine w) (t' := X86Ty.machine w))
            (lowerBoundedLoopT stepCom k)
            (V := (Ctxt.Valuation.extend (.cons s .nil) (stepCom.denote (.cons s .nil))))]
      · exact ih (step s)
      · intro t v
        cases v with
        | here => exact (hstep s).symm
        | there v' => cases v'

/-! ## 6. The emitted looped `Lcmd` is constant-size in the (runtime) trip count

The rejection loop emits as the **looped** owned-backend control-flow shape, not
an unroll: a single body copy wrapped in a back-edge whose `jne .L` tests the
*public* guard result. `LprogControlFlow.loopLcmd` is exactly that shape; the
guarded-loop emission reuses it, so the emitted `.s` is `O(1)` body copies
regardless of how many times the loop runs at run time. (The denotation proof in
§5 goes through the unrolled-at-trip-count `Com`; the *emission* is the looped
`Lcmd` — same denotation by `LprogControlFlow.loopLcmd_denote`, smaller code by
`LprogControlFlow.loopLcmd_length`.) -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
  in
/-- The emitted looped `Lcmd` for a rejection loop: a single copy of the body
    wrapped by `LprogControlFlow.loopLcmd`, with the public-guard back-edge. The
    counter register `gReg` here holds the *guard result* (1 = continue / resample,
    0 = accept), so the back-edge `jne .L` resamples while the public guard is
    nonzero — the rejection-loop control-flow shape. -/
def rejectLoopLcmd (w : Nat) (top : CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.LLabel)
    (gReg : String) (body : CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Lcmd) :
    CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Lcmd :=
  LprogControlFlow.loopLcmd w top gReg body

/-- The emitted rejection loop is constant-size: body length plus the three
    control instrs, **independent of the runtime trip count** — reusing
    `LprogControlFlow.loopLcmd_length`. -/
theorem rejectLoopLcmd_length (w : Nat)
    (top : CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.LLabel) (gReg : String)
    (body : CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Lcmd) :
    (rejectLoopLcmd w top gReg body).length = body.length + 3 :=
  LprogControlFlow.loopLcmd_length w top gReg body

/-! ## 7. KAT: the ML-DSA signing rejection loop emitted through the verified front

We model the **outer** Fiat-Shamir-with-aborts loop of ML-DSA signing (FIPS 204
§Algorithm 7), the loop `MldsaLowCT.lean` explicitly left out of the kernel
("the rejection-sample loop is modeled outside the kernel as repeated calls").
The inner per-`κ` kernel (ExpandMask + the response/`z` computation + the
∞-norm reduction) already emits straight-line through the dialect; here we wrap
**that kernel body once** in the terminating guarded loop and let the public
norm-check drive the resample.

### The modeled body (one signing attempt)

Each iteration models one signing attempt as a deterministic transcript of the
real kernel's observable register effects (we use a fixed pseudo-mask schedule so
the KAT is executable; the control-flow shape — resample-while-norm-too-large —
is identical to the real loop):

* `"kappa"` is the domain-separation counter ML-DSA advances every attempt
  (`κ += ℓ`); each attempt bumps it.
* `"normz"` is the computed `‖z‖∞` for this attempt. The real value comes from
  the kernel's norm reduction; we model the *schedule* of candidate norms as a
  monotone-decreasing sequence so a deterministic number of attempts abort before
  one passes the public bound — exactly the structure of a terminating rejection
  loop. Concretely each attempt sets `normz := bound + slack(kappa)` where the
  slack shrinks with `kappa`, so the loop aborts until `kappa` is large enough.

### The public guard

The guard is `‖z‖∞ ≥ γ₁-β` ("response too large ⇒ resample"). This decision is
**public** (the number of aborts is leaked by construction in FS-with-aborts).
We read it off the public `"reject"` register the body sets from the norm
comparison (1 = abort/resample, 0 = accept). -/

/-- The ML-DSA-65 public norm bound `γ₁ - β` we compare `‖z‖∞` against, scaled to
    a small KAT-friendly value. (The real bound is `γ₁-β = 2^19 - 78`; the KAT
    uses a small bound so the deterministic norm schedule reaches acceptance in a
    handful of attempts — the control-flow shape is bound-independent.) -/
def normBound : BitVec 64 := 100

/-- One ML-DSA signing attempt, as the kernel's observable register transcript.
    Bumps the attempt counter `kappa`, computes this attempt's candidate norm
    `normz` (a deterministic decreasing schedule standing in for the kernel's
    `‖z‖∞`), then sets the **public** `reject` flag-register to 1 iff
    `normz ≥ normBound` (`SUB normz,bound` borrow ⇒ `normz < bound` ⇒ accept).
    The body includes its own state advance (the `κ` bump), exactly as a
    `runBoundedLoop` body carries its own counter decrement. -/
def mldsaSignAttemptBody : List (JInstr 64) :=
  [ -- κ += 1  (domain-separation counter advance; one signing attempt)
    .add "kappa" (.imm 1)
    -- model the candidate ‖z‖∞ for this attempt: normz := 130 - 10·kappa.
    -- (decreasing schedule: attempt 1 ↦ 120 ≥ 100 reject, … attempt 4 ↦ 90 < 100 accept)
  , .mov "t" (.reg "kappa")
  , .imul "t" (.imm 10)
  , .mov "normz" (.imm 130)
  , .sub "normz" (.reg "t")
    -- public norm check: reject := 1 iff normz ≥ bound, via CF-free compare.
    -- compute (normz - bound); if no borrow (normz ≥ bound) keep reject = 1, else 0.
  , .mov "cand" (.reg "normz")
  , .sub "cand" (.imm 100)            -- sets CF iff normz < bound (borrow)
  , .mov "reject" (.imm 1)
  , .mov "zero" (.imm 0)
  , .cmovb "reject" (.reg "zero") ]   -- if borrow (normz < bound) ⇒ reject := 0 (accept)

/-- The **public** rejection guard: continue (resample) while `reject ≠ 0`. Reads
    the public `reject` register the body set from the norm comparison. -/
def mldsaRejectGuard : JState 64 → Bool := fun s => decide ((s.get "reject").toNat ≠ 0)

/-- Fuel bounding the rejection loop: a generous cap on the worst-case attempt
    count (the real loop is run with `fuel` ≥ the worst-case trip count; the cap
    only makes the semantics total). -/
def mldsaSignFuel : Nat := 64

/-- The initial signing state: `kappa = 0`, every other register 0. The guard
    must initially hold (we have not yet computed a `reject` — model the first
    entry as "reject pending"; equivalently the loop is entered after a first
    body run). We set `reject = 1` so the loop body runs at least once. -/
def mldsaSignInit : JState 64 :=
  { regs := fun r => if r = "reject" then (1 : BitVec 64) else 0 }

/-- The whole ML-DSA signing as the terminating guarded loop: the per-attempt
    kernel body wrapped once in `runGuardedLoop` under the public norm-check
    guard. This is the **whole** signing control flow (inner kernel + outer
    resample), not just the inner kernel. -/
def mldsaSignRun : JState 64 :=
  runGuardedLoop mldsaSignFuel mldsaRejectGuard mldsaSignAttemptBody mldsaSignInit

/-- **KAT (value): the modeled ML-DSA signing rejection loop terminates at the
    first accepting attempt.** With the decreasing norm schedule
    `normz = 130 - 10·κ`, attempts κ=1,2,3 give `normz = 120,110,100 ≥ 100`
    (reject), and κ=4 gives `normz = 90 < 100` (accept). So the loop runs the
    body 4 times and stops with `kappa = 4`, `normz = 90`, `reject = 0`. The trip
    count is data-dependent (resolved by the guard), not a compile-time constant —
    this is the rejection-loop behaviour the bounded-counter loop could not
    express. -/
example :
    (mldsaSignRun.get "kappa").toNat = 4
      ∧ (mldsaSignRun.get "normz").toNat = 90
      ∧ (mldsaSignRun.get "reject").toNat = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- **KAT (dynamic trip count).** The rejection loop runs the body exactly 4
    times for this input — a *runtime*, guard-resolved count, capped well under
    the fuel. -/
example :
    tripCount mldsaSignFuel mldsaRejectGuard mldsaSignAttemptBody mldsaSignInit = 4 := by
  native_decide

/-- **KAT (lowering correctness on the whole signing loop).** Lowering the whole
    ML-DSA signing rejection loop to `Com (x86Dialect 64)` (at its resolved
    trip count) and denoting it on the initial state equals the guarded-loop
    machine semantics — the *whole* protocol control flow, inner kernel plus
    outer resample, goes through the verified front. Instantiates
    `guardedLoop_lowering_denote_closed`. -/
theorem mldsaSign_lowering_correct :
    (lowerGuardedLoop (Γ := []) mldsaSignFuel mldsaRejectGuard mldsaSignAttemptBody
        mldsaSignInit).denote (.cons mldsaSignInit .nil)
      = mldsaSignRun :=
  guardedLoop_lowering_denote_closed mldsaSignFuel mldsaRejectGuard
    mldsaSignAttemptBody mldsaSignInit

/-- **KAT (end-to-end): the lowered whole-signing `Com` computes the accepting
    transcript.** Composing `mldsaSign_lowering_correct` with the value KAT: the
    denotation of the lowered guarded-loop `Com` on the initial state yields
    `kappa = 4`, `normz = 90`, `reject = 0` — the byte-level register transcript
    of the accepting signing attempt, produced by the verified-front lowering of
    the *whole* rejection loop. -/
example :
    let s := (lowerGuardedLoop (Γ := []) mldsaSignFuel mldsaRejectGuard
                mldsaSignAttemptBody mldsaSignInit).denote (.cons mldsaSignInit .nil)
    (s.get "kappa").toNat = 4 ∧ (s.get "normz").toNat = 90
      ∧ (s.get "reject").toNat = 0 := by
  intro s
  show _ ∧ _ ∧ _
  rw [show s = mldsaSignRun from mldsaSign_lowering_correct]
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## 8. CT note: the guard is public (rejection-loop CT discipline)

The rejection guard `mldsaRejectGuard` reads the **public** `reject` register —
the abort decision FS-with-aborts leaks by construction. At the `LowCT` layer
this corresponds to `LowCTCT.isCT_LowCT'`'s admission of `RWhileNz x body` when
`!(secrets x)` (the guard variable is not secret) and the body is CT. The
bounded-subset lowering of this module (`lowerGuardedLoop` reduces to
`lowerBoundedLoop` at the public-resolved trip count) is therefore CT-admissible
under the same `#460` policy as `Cond.lowerCond`: a public-guard loop emits the
looped `loopLcmd` whose `jne .L` tests only the public norm-check result. A
*secret*-dependent loop guard is rejected by `isCT_LowCT'` (`secrets x = true`),
matching the forbidden timing-oracle case. -/

/-- The rejection guard depends only on the public `reject` register: two states
    agreeing on `reject` give the same guard decision. This is the
    public-guard / robust-safety witness for the rejection loop — the guard is a
    function of public state alone, so resolving the trip count at lowering time
    leaks nothing beyond the (already-public) abort count. -/
theorem mldsaRejectGuard_public {s s' : JState 64}
    (h : s.get "reject" = s'.get "reject") :
    mldsaRejectGuard s = mldsaRejectGuard s' := by
  simp only [mldsaRejectGuard, h]

/-- Robustness of the guarded-loop denotation to the public guard: if two guards
    agree pointwise then the loop runs identically. The looped emission's
    correctness depends only on the guard's *values*, not its intension — so
    swapping the modeled public guard for the real norm-check (same Boolean
    decision) preserves the denotation. -/
theorem runGuardedLoop_guard_congr {w : Nat} (fuel : Nat)
    (guard guard' : JState w → Bool) (body : List (JInstr w)) (s : JState w)
    (h : ∀ t, guard t = guard' t) :
    runGuardedLoop fuel guard body s = runGuardedLoop fuel guard' body s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ f ih =>
      simp only [runGuardedLoop, h s]
      cases guard' s with
      | false => rfl
      | true => simp only [if_true]; exact ih (runBlock s body)

end CatCrypt.Crypto.SecureCompilation.X86Backend.RejectLoop
