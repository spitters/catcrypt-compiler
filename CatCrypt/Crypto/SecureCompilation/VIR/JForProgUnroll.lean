/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp

/-!
# Verified loop unrolling for `JForProg`

`JForProgMultiOp.loop_denote_eq_multiOp` (task #92) is the bounded-loop keystone:
the emitted `for i = 0 to n { acc = body(acc) }` denotes the `n`-fold
semantics for *any* straight-line body. This file adds a **verified
loop-unrolling pass** at the `JForProg` (Com) level — the canonical
verified-compiler-internal optimisation that closes the residual ILP gap behind
HACL*'s SHA-2 1.64×, Keccak SIMD 3.04×, and ChaCha 4-way 4.2-4.6× speedups
without touching the emitted-asm story.

## The pass at a glance

Given a bounded-loop program `p : JForProg accTy` and an unroll factor `N`, an
"unrolled" program runs the same accumulator transform but performs `N` body
applications per iteration:

* `n` shrinks from `p.n` to `p.n / N` (when `N ∣ p.n`);
* the new body's per-iteration semantics is the `N`-fold composition of
  `p.step`;
* the total denotation is preserved: `(unrolled).denote init = p.denote init`.

The body's *Com* is provided by an external emit pass — e.g. concatenating
`N` copies of `p.update` (which is straight-line, hence still straight-line
after concatenation). This file's responsibility is the **mathematical /
denotation-level glue**: given any candidate unrolled body whose `step` agrees
with the `N`-fold composition, the resulting `JForProg` denotes the same total
function as the original. So unrolling commutes with the verified emit chain
(`JForProgMultiOp.loop_denote_eq_multiOp`) — no re-proving of emit correctness.

## Contents

* `JForProg.stepN p N` — the `N`-fold composition of `p.step`. The
  per-iteration semantics of an `N`-unrolled body.
* `foldl_step_split_dvd` — the mathematical core: `q*N` iterations of `f`
  equals `q` iterations of `(f^N)`. The "split" lemma underlying loop
  unrolling.
* `JForProg.UnrolledBy` — a structure packaging an unrolled `JForProg` plus a
  proof that its per-iteration step is the `N`-fold composition of the
  original's step.
* `JForProg.UnrolledBy.denote_eq` — the denotation-preservation theorem (the
  divisibility-only form). When `N ∣ p.n`, the unrolled program's denotation
  equals the original's.
* `foldl_step_split_general` — the general split: `q*N + r` iterations of `f`
  equals `q` iterations of `(f^N)` followed by `r` extra iterations of `f`.
* `JForProg.UnrolledByWithTail` and `denote_eq_with_tail` — the tail-handling
  generalisation: arbitrary `p.n`, composing `q` iterations of the `N`-unrolled
  body with `r` iterations of the original body.
* Concrete corollaries naming the unroll factors used by HACL* kernels:
  ChaCha `N=2` (10 column/diagonal pairs from 20 rounds), SHA-2 `N=4`
  (16 = 64/4), Keccak `N=4` (6 = 24/4).

No `sorry`, no `native_decide`, no new axioms — the split lemmas are closed by
structural induction on the iteration count and standard `Nat`-arithmetic
identities (`omega`, `Nat.div_mul_cancel`, `List.foldl_append`,
`List.range_add`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JForProgUnroll

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgMultiOp

/-! ## 1. `N`-fold composition of a per-iteration step -/

/-- `N`-fold composition of an accumulator step. The per-iteration semantics
    of a body unrolled `N` times. -/
def iterFn {accTy : JasminTy} (f : ⟦accTy⟧ → ⟦accTy⟧) :
    Nat → ⟦accTy⟧ → ⟦accTy⟧
  | 0, acc => acc
  | N+1, acc => iterFn f N (f acc)

/-- `iterFn f 0` is the identity. -/
@[simp] theorem iterFn_zero {accTy : JasminTy} (f : ⟦accTy⟧ → ⟦accTy⟧)
    (acc : ⟦accTy⟧) : iterFn f 0 acc = acc := rfl

/-- `iterFn f 1` is just `f`. -/
@[simp] theorem iterFn_one {accTy : JasminTy} (f : ⟦accTy⟧ → ⟦accTy⟧)
    (acc : ⟦accTy⟧) : iterFn f 1 acc = f acc := rfl

/-- Successor unfolding (left form): `iterFn f (N+1) acc = iterFn f N (f acc)`. -/
theorem iterFn_succ_left {accTy : JasminTy} (f : ⟦accTy⟧ → ⟦accTy⟧)
    (N : Nat) (acc : ⟦accTy⟧) :
    iterFn f (N + 1) acc = iterFn f N (f acc) := rfl

/-- Successor unfolding (right form): `iterFn f (N+1) acc = f (iterFn f N acc)`. -/
theorem iterFn_succ_right {accTy : JasminTy} (f : ⟦accTy⟧ → ⟦accTy⟧)
    (N : Nat) (acc : ⟦accTy⟧) :
    iterFn f (N + 1) acc = f (iterFn f N acc) := by
  induction N generalizing acc with
  | zero => rfl
  | succ N ih =>
      -- LHS: iterFn f (N+2) acc = iterFn f (N+1) (f acc) by def
      -- Apply ih at (f acc): iterFn f (N+1) (f acc) = f (iterFn f N (f acc))
      -- Apply ih at acc (used in reverse to identify iterFn f N (f acc)
      --   with the alternative form): iterFn f (N+1) acc = f (iterFn f N acc),
      --   and iterFn f (N+1) acc = iterFn f N (f acc) by def, hence
      --   iterFn f N (f acc) = f (iterFn f N acc).
      have h1 : iterFn f (N + 1 + 1) acc = f (iterFn f N (f acc)) := ih (f acc)
      have h2 : iterFn f N (f acc) = f (iterFn f N acc) := ih acc
      rw [h1, h2, ih acc]

/-- Addition unfolding: `iterFn f (a + b) = iterFn f b ∘ iterFn f a`. -/
theorem iterFn_add {accTy : JasminTy} (f : ⟦accTy⟧ → ⟦accTy⟧)
    (a b : Nat) (acc : ⟦accTy⟧) :
    iterFn f (a + b) acc = iterFn f b (iterFn f a acc) := by
  induction b generalizing acc with
  | zero => simp [iterFn]
  | succ b ih =>
      -- a + (b+1) = (a + b) + 1; both sides peel one f off the outside
      -- via iterFn_succ_right.
      have hSum : a + (b + 1) = (a + b) + 1 := by omega
      rw [hSum, iterFn_succ_right f (a + b), ih, ← iterFn_succ_right f b]

/-- `JForProg`-level alias: the `N`-fold composition of `p.step`. The
    per-iteration semantics that an `N`-unrolled body should denote.
    (Defined as a free function rather than a method on `JForProg` to avoid
    dot-notation lookup collisions with the upstream `JasminPrint.JForProg`
    namespace.) -/
def stepN {accTy : JasminTy} (p : JForProg accTy) (N : Nat)
    (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  iterFn (p.step) N acc

@[simp] theorem stepN_zero {accTy : JasminTy} (p : JForProg accTy)
    (acc : ⟦accTy⟧) : stepN p 0 acc = acc := rfl

@[simp] theorem stepN_one {accTy : JasminTy} (p : JForProg accTy)
    (acc : ⟦accTy⟧) : stepN p 1 acc = p.step acc := rfl

/-! ## 2. The fold-split lemma: the math core of loop unrolling -/

/-- **Folding `f` over `range (a + b)` from `init` equals folding `f` over
    `range b` from `(range a).foldl f init`.** A list-flavoured restatement of
    `List.range_add` + `List.foldl_append`. -/
theorem foldl_range_add {α : Type _}
    (f : α → Nat → α) (a b : Nat) (init : α) :
    (List.range (a + b)).foldl f init
      = (List.range b).foldl
          (fun acc i => f acc (a + i))
          ((List.range a).foldl f init) := by
  rw [List.range_add, List.foldl_append, List.foldl_map]

/-- A `foldl` over a `List.range` whose function ignores the index. The body
    function is essentially a unary step. (Used to discard the index-rewrite
    introduced by `foldl_range_add`.) -/
theorem foldl_range_const {accTy : JasminTy}
    (step : ⟦accTy⟧ → ⟦accTy⟧) (n : Nat) (init : ⟦accTy⟧) :
    (List.range n).foldl (fun acc _ => step acc) init
      = iterFn step n init := by
  induction n generalizing init with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih, iterFn_succ_right]
      rfl

/-- A re-indexed `foldl_range_const`: folding `step` over `range b` from any
    seed equals `iterFn step b` of the seed, *regardless* of how the indices
    are re-mapped (since the function ignores them). -/
theorem foldl_range_reindexed_const {accTy : JasminTy}
    (step : ⟦accTy⟧ → ⟦accTy⟧) (g : Nat → Nat) (n : Nat) (init : ⟦accTy⟧) :
    (List.range n).foldl (fun acc i => (fun acc' _ => step acc') acc (g i)) init
      = iterFn step n init := by
  -- The g-reindex is a no-op because the body discards its second argument.
  induction n generalizing init with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih, iterFn_succ_right]
      rfl

/-- **Loop-unrolling math core (multiplicative form).** Folding `step` over
    `range (q * N)` equals folding the `N`-fold composition `iterFn step N`
    over `range q`. The semantic skeleton of unrolling: `q*N` body
    applications equal `q` applications of an `N`-unrolled body. -/
theorem foldl_step_split_mul {accTy : JasminTy}
    (step : ⟦accTy⟧ → ⟦accTy⟧) (q N : Nat) (init : ⟦accTy⟧) :
    (List.range (q * N)).foldl (fun acc _ => step acc) init
      = (List.range q).foldl (fun acc _ => iterFn step N acc) init := by
  induction q generalizing init with
  | zero => simp
  | succ q ih =>
      -- range ((q+1)*N) = range (q*N + N)
      have hcount : (q + 1) * N = q * N + N := by ring
      rw [hcount, foldl_range_add, ih]
      -- range (q+1) on RHS: foldl over [range q ++ [q]]
      rw [List.range_succ, List.foldl_append]
      -- Inner fold over range N (with re-indexed body) computes iterFn step N
      have hinner :
          (List.range N).foldl
              (fun acc i => (fun acc' _ => step acc') acc (q * N + i))
              ((List.range q).foldl (fun acc _ => iterFn step N acc) init)
            = iterFn step N
                ((List.range q).foldl (fun acc _ => iterFn step N acc) init) :=
        foldl_range_reindexed_const step (fun i => q * N + i) N _
      rw [hinner]
      rfl

/-- **Loop-unrolling math core (divisibility form).** When `N ∣ n`, folding
    `step` over `range n` equals folding the `N`-fold composition
    `iterFn step N` over `range (n / N)`. This is the form a divisibility-only
    unrolling pass uses. -/
theorem foldl_step_split_dvd {accTy : JasminTy}
    (step : ⟦accTy⟧ → ⟦accTy⟧) (n N : Nat) (h : N ∣ n) (init : ⟦accTy⟧) :
    (List.range n).foldl (fun acc _ => step acc) init
      = (List.range (n / N)).foldl (fun acc _ => iterFn step N acc) init := by
  obtain ⟨q, hq⟩ := h
  -- n = N * q = q * N
  have hcount : n = q * N := by rw [hq]; ring
  -- n / N = q (whenever the unroll factor is nonzero; the N=0 case is degenerate
  -- but still handled because `n/0 = 0` and `q*0 = 0`, so both sides are init.
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : n = 0 := by rw [hcount]; ring
    subst this
    rfl
  · have hq' : n / N = q := by
      rw [hcount]
      exact Nat.mul_div_cancel _ hN
    -- Rewrite n/N → q first, THEN n → q*N (rewriting n first eliminates the n
    -- the hq' rewrite is targeting).
    rw [hq', hcount, foldl_step_split_mul]

/-- **General split (quotient/remainder form).** Folding `step` over
    `range (q * N + r)` equals folding `iterFn step N` over `range q` followed
    by folding `step` over `range r`. The "tail body" handles the leftover
    iterations that don't fit a full unrolled block. -/
theorem foldl_step_split_general {accTy : JasminTy}
    (step : ⟦accTy⟧ → ⟦accTy⟧) (q N r : Nat) (init : ⟦accTy⟧) :
    (List.range (q * N + r)).foldl (fun acc _ => step acc) init
      = (List.range r).foldl (fun acc _ => step acc)
          ((List.range q).foldl (fun acc _ => iterFn step N acc) init) := by
  rw [foldl_range_add]
  -- After foldl_range_add: the inner fold over range r has body
  -- `(fun acc i => step acc)` with reindex (q*N + i) — but body discards `i`,
  -- so the fold's only dependence on the outer is via its seed. Rewriting
  -- the seed by foldl_step_split_mul closes the goal up to reflexivity of the
  -- (constant-in-index) tail fold.
  rw [foldl_step_split_mul]

/-! ## 3. Denotation-preserving unrolling — divisibility form -/

/-- **An unrolled `JForProg` plus its semantic witness (divisibility form).**

    `unrolled : JForProg accTy` is a candidate `N`-unrolled program: its body
    Com performs `N` of the original's body applications per iteration. We do
    *not* prescribe how the body Com is constructed (e.g. literal
    concatenation, fusion, post-optimisation) — only its denotational
    behaviour. The witness `step_eq` says: running the unrolled body once
    equals running the original body `N` times.

    The structure also records `factor_correct`: `unrolled.n * N = p.n` (so
    `unrolled.n = p.n / N` when `N ∣ p.n`). This is the divisibility-only
    contract; for arbitrary `p.n`, use `UnrolledByWithTail` below. -/
structure UnrolledBy {accTy : JasminTy} (p : JForProg accTy) (N : Nat)
    where
  /-- The unrolled program: same accumulator type, smaller `n`, body
      performing `N` of the original's steps per iteration. -/
  unrolled : JForProg accTy
  /-- The unrolled iteration count times the factor equals the original. -/
  factor_correct : unrolled.n * N = p.n
  /-- The unrolled body's per-iteration semantics is the `N`-fold composition
      of the original's. -/
  step_eq : ∀ acc : ⟦accTy⟧, unrolled.step acc = stepN p N acc

/-- A `foldl`-congruence lemma: two folds over `range n` whose bodies agree
    pointwise (regardless of index) coincide on every initial value. -/
theorem foldl_step_congr {accTy : JasminTy}
    {f g : ⟦accTy⟧ → ⟦accTy⟧} (hfg : ∀ acc, f acc = g acc) (n : Nat) :
    ∀ (init : ⟦accTy⟧),
      (List.range n).foldl (fun acc _ => f acc) init
        = (List.range n).foldl (fun acc _ => g acc) init := by
  induction n with
  | zero => intro init; rfl
  | succ n ih =>
      intro init
      rw [List.range_succ, List.foldl_append, List.foldl_append,
          ih init]
      simp [hfg]

/-- **Denotation preservation, divisibility form.** When an unrolled JForProg
    satisfies the `UnrolledBy p N` contract, its total denotation equals the
    original's. Proof: by the multiplicative fold-split lemma, folding the
    original step over `range (q*N) = range p.n` equals folding the unrolled
    step over `range q = range unrolled.n`. -/
theorem UnrolledBy.denote_eq {accTy : JasminTy} {p : JForProg accTy}
    {N : Nat} (u : UnrolledBy p N) (init : ⟦accTy⟧) :
    u.unrolled.denote init = p.denote init := by
  unfold JForProg.denote
  -- LHS: foldl over range u.unrolled.n with u.unrolled.step
  -- RHS: foldl over range p.n with p.step
  -- Step 1: rewrite p.n using factor_correct
  rw [← u.factor_correct]
  -- Step 2: invoke foldl_step_split_mul on the RHS (going LHS ← RHS direction)
  rw [foldl_step_split_mul]
  -- Step 3: align the inner step
  exact foldl_step_congr (fun acc => u.step_eq acc) u.unrolled.n init

/-! ## 4. Denotation-preserving unrolling — general (tail-handling) form -/

/-- **An unrolled `JForProg` plus its semantic witness (general form).** For
    arbitrary `p.n`, the unrolled program runs `q = p.n / N` blocks of
    `N`-unrolled body followed by `r = p.n % N` tail iterations of the
    original body. Captured as: two `JForProg`s (the unrolled-block program
    and the tail program), with the contract that their *combined* denotation
    equals the original's. -/
structure UnrolledByWithTail {accTy : JasminTy} (p : JForProg accTy)
    (N : Nat) where
  /-- The unrolled-block program: `unrolled.n = p.n / N`, body performs `N` of
      the original's steps per iteration. -/
  unrolled : JForProg accTy
  /-- The tail program: `tail.n = p.n % N`, body is the original (or
      semantically equivalent to the original). -/
  tail : JForProg accTy
  /-- Iteration counts decompose `p.n` as `q*N + r`. -/
  count_decomp : unrolled.n * N + tail.n = p.n
  /-- The unrolled body's per-iteration semantics is the `N`-fold composition
      of the original's. -/
  step_eq : ∀ acc : ⟦accTy⟧, unrolled.step acc = stepN p N acc
  /-- The tail body's per-iteration semantics matches the original's. -/
  tail_step_eq : ∀ acc : ⟦accTy⟧, tail.step acc = p.step acc

/-- **Denotation preservation, general (tail-handling) form.** When an
    `UnrolledByWithTail p N` contract holds, the original's denotation equals
    the unrolled-block program's denotation followed by the tail program's
    denotation. Proof: by `foldl_step_split_general`. -/
theorem UnrolledByWithTail.denote_eq {accTy : JasminTy}
    {p : JForProg accTy} {N : Nat} (u : UnrolledByWithTail p N)
    (init : ⟦accTy⟧) :
    u.tail.denote (u.unrolled.denote init) = p.denote init := by
  unfold JForProg.denote
  rw [← u.count_decomp]
  -- Apply the general split lemma to the RHS
  rw [foldl_step_split_general]
  -- Step A: unrolled fold congruence
  have hUnrolled :
      (List.range u.unrolled.n).foldl (fun acc _ => u.unrolled.step acc) init
        = (List.range u.unrolled.n).foldl
            (fun acc _ => iterFn (p.step) N acc) init := by
    have := foldl_step_congr (f := u.unrolled.step) (g := fun acc => stepN p N acc)
              (fun acc => u.step_eq acc) u.unrolled.n init
    exact this
  -- Step B: tail fold congruence
  have hTail :
      (List.range u.tail.n).foldl (fun acc _ => u.tail.step acc)
          ((List.range u.unrolled.n).foldl
            (fun acc _ => iterFn (p.step) N acc) init)
        = (List.range u.tail.n).foldl (fun acc _ => p.step acc)
            ((List.range u.unrolled.n).foldl
              (fun acc _ => iterFn (p.step) N acc) init) :=
    foldl_step_congr (fun acc => u.tail_step_eq acc) u.tail.n _
  rw [hUnrolled, hTail]

/-! ## 5. Commuting with the verified emit chain

The verified emit keystone (`JForProgMultiOp.loop_denote_eq_multiOp`) says: for
any straight-line body, the emitted `Cfor` loop's word-level run equals
`JForProg.denote`. Combining this with `UnrolledBy.denote_eq` yields the
end-to-end statement: **the emitted loop of the unrolled program denotes the
same function as the emitted loop of the original program.** -/

/-- **Unrolling commutes with the verified emit chain.** When `u : p.UnrolledBy N`,
    and the unrolled body is straight-line (`hSL : StraightLine u.unrolled.update`),
    the emitted bounded loop of `u.unrolled` produces the same word-level
    result as the emitted bounded loop of `p`. So loop unrolling is a sound
    verified optimisation: it preserves emit-level behaviour with no separate
    proof of emit correctness for the unrolled body — the multi-op keystone
    handles it. -/
theorem UnrolledBy.emit_denote_eq {accTy : JasminTy} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) {p : JForProg accTy} {N : Nat}
    (u : UnrolledBy p N) (hSL_p : StraightLine p.update)
    (hSL_u : StraightLine u.unrolled.update) (init : ⟦accTy⟧) :
    JForProgCT.loopRun u.unrolled (bodyStepRun leafSem u.unrolled) init
      = JForProgCT.loopRun p (bodyStepRun leafSem p) init := by
  rw [loop_denote_eq_multiOp hLeaf u.unrolled hSL_u init,
      loop_denote_eq_multiOp hLeaf p hSL_p init]
  exact u.denote_eq init

/-- **Unrolling with tail commutes with the verified emit chain.** Analogue of
    `emit_denote_eq` for `UnrolledByWithTail`: the unrolled-block loop followed
    by the tail loop (both emitted) produces the same word-level result as the
    emitted original loop. -/
theorem UnrolledByWithTail.emit_denote_eq {accTy : JasminTy}
    {leafSem : LeafSem} (hLeaf : LeafAgrees leafSem)
    {p : JForProg accTy} {N : Nat} (u : UnrolledByWithTail p N)
    (hSL_p : StraightLine p.update) (hSL_u : StraightLine u.unrolled.update)
    (hSL_t : StraightLine u.tail.update) (init : ⟦accTy⟧) :
    JForProgCT.loopRun u.tail (bodyStepRun leafSem u.tail)
        (JForProgCT.loopRun u.unrolled (bodyStepRun leafSem u.unrolled) init)
      = JForProgCT.loopRun p (bodyStepRun leafSem p) init := by
  rw [loop_denote_eq_multiOp hLeaf u.unrolled hSL_u init,
      loop_denote_eq_multiOp hLeaf u.tail hSL_t (u.unrolled.denote init),
      loop_denote_eq_multiOp hLeaf p hSL_p init]
  exact u.denote_eq init

/-! ## 6. Concrete corollaries: HACL* unroll factors

We *name* the unroll factors used by the HACL* kernels behind the ILP residual.
Each corollary states: assuming the emit pass produces an `UnrolledBy p N`
witness for the given factor, the denotation is preserved. No re-emitting
needed — just a named entry point future emit work can target. -/

namespace HACLCorollaries

/-- **ChaCha 4-way `N = 2`.** ChaCha20 has 20 rounds, structured as 10
    (column, diagonal) pairs. Unrolling by `N = 2` gives a 10-iteration loop
    over a doubled body (one column + one diagonal). This is the kernel
    geometry behind HACL*'s 4.2-4.6× ChaCha 4-way speedup; the unroll factor
    is exactly 2. -/
theorem chacha_unroll_2 {accTy : JasminTy} {p : JForProg accTy}
    (h20 : p.n = 20) (u : UnrolledBy p 2) (init : ⟦accTy⟧) :
    u.unrolled.n = 10 ∧ u.unrolled.denote init = p.denote init := by
  refine ⟨?_, u.denote_eq init⟩
  -- unrolled.n * 2 = p.n = 20  ⇒  unrolled.n = 10
  have := u.factor_correct
  omega

/-- **SHA-2 64 rounds, `N = 4`.** SHA-2's compression has 64 rounds. Unrolling
    by `N = 4` yields a 16-iteration loop over a 4-round unrolled body — the
    same batching #120 explored, but verified at the loop-unroll layer (not
    just the SIMD-lane layer). HACL*'s SHA-2 1.64× speedup is largely driven
    by this kind of round-batching. -/
theorem sha2_unroll_4 {accTy : JasminTy} {p : JForProg accTy}
    (h64 : p.n = 64) (u : UnrolledBy p 4) (init : ⟦accTy⟧) :
    u.unrolled.n = 16 ∧ u.unrolled.denote init = p.denote init := by
  refine ⟨?_, u.denote_eq init⟩
  have := u.factor_correct
  omega

/-- **Keccak 24 rounds, `N = 4`.** Keccak-f[1600] has 24 rounds. Unrolling by
    `N = 4` gives a 6-iteration loop over a 4-round unrolled body. This is
    the unroll factor behind HACL*'s Keccak SIMD 3.04× lane gap; the
    inter-lane reordering opportunities come from the unrolled body, not the
    loop. -/
theorem keccak_unroll_4 {accTy : JasminTy} {p : JForProg accTy}
    (h24 : p.n = 24) (u : UnrolledBy p 4) (init : ⟦accTy⟧) :
    u.unrolled.n = 6 ∧ u.unrolled.denote init = p.denote init := by
  refine ⟨?_, u.denote_eq init⟩
  have := u.factor_correct
  omega

end HACLCorollaries

end CatCrypt.Crypto.SecureCompilation.VIR.JForProgUnroll
