/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterReduction
public import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReduction
public import Lean

/-!
# A denotational relational-compilation layer (Rupicola-style core)

This module provides a small, composable, proof-producing framework for the
recurring obligation "the emitted `Com jasminDialect` program denotes its
spec." It is the reusable generalization of the per-primitive
emit-denotes-closed-form proofs: instead of writing a bespoke
~70-line / 46-step `Com.denote` blast per kernel, a kernel's denotes-spec
proof is **assembled** from a fixed set of compilation lemmas, driven by a
structural tactic.

## Foundation: denotational refinement

The relation is *denotational* (matching the existing infrastructure, not a
WP/separation logic): a fragment refines a spec when "running the fragment's
continuation denotes the same as running the continuation on a transformed
environment+valuation, AND the transform realizes the spec's state-step."

The CatCrypt jasmin emitters are written in **continuation-passing style**:
`emitOp e op dst a b k`, `cp e dst src k`, `emitRotr … k`, … each take a
continuation `k : SCont w s` and produce a `Com jasminDialect Γ s`. The
existing per-helper rewrites (`Sha2EmitterReduction.emitOp_denote`,
`cp_denote'`, `emitRotr_denote`) already establish, for each fragment,

    (emit … k).denote V = (k envF).denote VF

for a concrete `(envF, VF)`. The framework packages exactly this shape and
makes it **composable** in `Γ` (the De Bruijn context grows as bindings are
emitted, so the building blocks must be context-polymorphic).

## The `StateStep` abstraction

A `StateStep w` is a "what one emitted fragment does to the abstract machine
state" : a function transforming a *readout view* `(slot : Nat → BitVec w,
inp : Nat → BitVec w)` to a new readout view. The atomic building blocks are:

* `arithStep op dst a b` — a scalar `RScalarSetExpr`-style binding: writes
  `op (read a) (read b)` to `slot dst`.
* `copyStep dst src` — a literal-index slot move (the load/store analogue).
* sequencing `s₁ >> s₂`.

A `Refines spec frag` says: `frag`, run on any faithful environment, denotes
to its continuation applied to a state transformed by `spec`. The compilation
lemmas (`Refines.arith`, `Refines.copy`, `Refines.seq`, `Refines.leafRotr`,
`Refines.forUnrolled`) say "if the sub-specs refine the sub-fragments, the
composite spec refines the composite fragment." The `scont_peel` splitter and
the `rupicola` driver apply them by structural decomposition (§6).

## Validation

`Sha2RoundRupicola.lean` re-derives the SHA-2 round emit's denotes-spec
result (the fact `EmitRoundDenotesClosedFormFaithful_holds`
establishes) through this framework, and measures the proof-size delta.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.RelationalCompile

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2EmitterReduction

/-! ## 1. Readout views and state-steps

A *readout view* is the abstract machine state visible through the emitter's
slot/input maps: a function from slot/input index to its current `BitVec w`.
`readView e V` extracts it from an `(Env, Valuation)` pair. A `StateStep w`
acts on a view. This is the denotational counterpart of a Rupicola
"compilation goal": the spec is a state-to-state function. -/

/-- The abstract machine state visible to the emitter: the current value at
    every register-file slot and input word. This is the denotational view
    that a spec function transforms. -/
structure View (w : Nat) where
  /-- Current value at register-file slot `i`. -/
  slot : Nat → BitVec w
  /-- Current value at input word `i` (inputs are read-only). -/
  inp  : Nat → BitVec w

/-- Extensionality for `View`: two views are equal when their slot and input
    maps agree. -/
@[ext] theorem View.ext {w : Nat} {vw₁ vw₂ : View w}
    (hslot : vw₁.slot = vw₂.slot) (hinp : vw₁.inp = vw₂.inp) : vw₁ = vw₂ := by
  cases vw₁; cases vw₂; cases hslot; cases hinp; rfl

/-- Extract the readout view from an environment + valuation. -/
def readView {w : Nat} {Γ : Ctxt jasminDialect}
    (e : Env w Γ) (V : Ctxt.Valuation Γ) : View w where
  slot i := readSlot e V i
  inp  i := readInp e V i

/-- Read a `Src` operand through a view (the spec-level operand resolver,
    mirroring `Sha2EmitterReduction.readSrc`). -/
def View.readSrc {w : Nat} (vw : View w) : Src → BitVec w
  | .sl i => vw.slot i
  | .iw i => vw.inp i

/-- A `StateStep` is a spec-level transformation of the machine view: what one
    emitted fragment does to the abstract state. Building blocks below; the
    composite of a whole kernel is built by `>>>`. -/
abbrev StateStep (w : Nat) := View w → View w

/-- The scalar-arithmetic step: write `op (read a) (read b)` to slot `dst`,
    leaving every other slot and all inputs unchanged. This is the spec of an
    `RScalarSetExpr`-style binding (`emitOp`). -/
def arithStep {w : Nat} (op : JasminBinOp) (dst : Nat) (a b : Src) : StateStep w :=
  fun vw => { vw with slot := fun i => if i = dst then op.apply (vw.readSrc a) (vw.readSrc b) else vw.slot i }

/-- The slot-copy step: write `slot src` to `slot dst` (a literal-index load
    then store). This is the spec of `cp`. -/
def copyStep {w : Nat} (dst src : Nat) : StateStep w :=
  fun vw => { vw with slot := fun i => if i = dst then vw.slot src else vw.slot i }

/-! ## 2. The `Refines` relation (denotational)

`Refines spec frag` says: for the spec `StateStep`, and the emitted CPS
fragment `frag`, running `frag k` on any `(e, V)` denotes the same as running
`k` on *some* `(envF, VF)` whose readout view is exactly `spec (readView e V)`.

This is the precise denotational refinement: the fragment's effect on the
denotation is to advance the abstract view by `spec`. It is **composable**:
sequencing two fragments composes their `StateStep`s, and the existential
`(envF, VF)` is threaded automatically. -/

/-- `Refines spec frag`: the emitted continuation-passing fragment `frag`
    denotes its spec `StateStep`.

    `frag : ∀ Γ (e : Env w Γ), SCont w s → Com jasminDialect Γ s` is a
    fragment builder taking an environment and a continuation. The relation
    says that for every context, environment, valuation, and continuation,
    the fragment's denotation equals the continuation applied to a final
    `(envF, VF)` whose readout view is `spec` applied to the starting view. -/
def Refines {w : Nat} {s : JasminTy}
    (spec : StateStep w)
    (frag : {Γ : Ctxt jasminDialect} → Env w Γ → SCont w s → Com jasminDialect Γ s) : Prop :=
  ∀ {Γ : Ctxt jasminDialect} (e : Env w Γ) (V : Ctxt.Valuation Γ) (k : SCont w s),
    ∃ (Γ' : Ctxt jasminDialect) (envF : Env w Γ') (VF : Ctxt.Valuation Γ'),
      (frag e k).denote V = (k envF).denote VF ∧
      readView envF VF = spec (readView e V)

/-! ## 3. Compilation lemmas — one per fragment shape

Each lemma is "the atomic fragment refines its atomic spec." `Refines.seq`
is the key composition rule: sequencing fragments composes specs. These are
the reusable building blocks the tactic stitches together. -/

/-- **Scalar-arith compilation lemma** (`RScalarSetExpr`). A single `emitOp`
    fragment refines `arithStep`. -/
theorem Refines.arith {w : Nat} {s : JasminTy}
    (op : JasminBinOp) (dst : Nat) (a b : Src) :
    Refines (s := s) (arithStep (w := w) op dst a b)
      (fun {Γ} (e : Env w Γ) k => emitOp e op dst a b k) := by
  intro Γ e V k
  refine ⟨_, _, _, emitOp_denote e op dst a b k V, ?_⟩
  unfold readView arithStep View.readSrc
  ext1
  · funext i
    dsimp only
    by_cases h : i = dst
    · subst h
      cases a <;> cases b <;>
        simp [readSlot_envAfterOp_eq, readSrc]
    · rw [readSlot_envAfterOp_ne _ _ _ _ _ h]
      simp [h]
  · funext i
    dsimp only
    simp [readInp_envAfterOp]

/-- **Slot-copy compilation lemma** (literal-index load/store). A single `cp`
    fragment refines `copyStep`. -/
theorem Refines.copy {w : Nat} {s : JasminTy} (dst src : Nat) :
    Refines (s := s) (copyStep (w := w) dst src)
      (fun {Γ} (e : Env w Γ) k => cp e dst src k) := by
  intro Γ e V k
  refine ⟨_, _, _, cp_denote' e dst src k V, ?_⟩
  unfold readView copyStep
  ext1
  · funext i
    dsimp only
    by_cases h : i = dst
    · subst h; simp [readSlot_envAfterOp_eq]
    · rw [readSlot_envAfterOp_ne _ _ _ _ _ h]; simp [h]
  · funext i; dsimp only; simp [readInp_envAfterOp]

/-- **Sequencing compilation lemma** — the composition rule. If `frag₁`
    refines `spec₁` and (for every starting environment) `frag₂` refines
    `spec₂`, then sequencing them refines `spec₂ ∘ spec₁`.

    Because the emitter is CPS, "sequencing" is `frag₁ e (fun e' => frag₂ e' k)`
    — `frag₂` runs in the context `frag₁` produced, so its refinement must hold
    over an arbitrary environment (which is exactly what `Refines` quantifies). -/
theorem Refines.seq {w : Nat} {s : JasminTy}
    {spec₁ spec₂ : StateStep w}
    {frag₁ frag₂ : {Γ : Ctxt jasminDialect} → Env w Γ → SCont w s → Com jasminDialect Γ s}
    (h₁ : Refines spec₁ frag₁) (h₂ : Refines spec₂ frag₂) :
    Refines (fun vw => spec₂ (spec₁ vw))
      (fun e k => frag₁ e (fun e' => frag₂ e' k)) := by
  intro Γ e V k
  obtain ⟨Γ₁, env₁, V₁, hden₁, hview₁⟩ := h₁ e V (fun e' => frag₂ e' k)
  obtain ⟨Γ₂, env₂, V₂, hden₂, hview₂⟩ := h₂ env₁ V₁ k
  refine ⟨Γ₂, env₂, V₂, ?_, ?_⟩
  · rw [hden₁, hden₂]
  · rw [hview₂, hview₁]

/-- **Identity/skip compilation lemma**. The empty fragment (apply the
    continuation directly) refines the identity step. Useful as the base case
    of a `seq`-fold and for closing a `rupicola` recursion. -/
theorem Refines.skip {w : Nat} {s : JasminTy} :
    Refines (s := s) (fun (vw : View w) => vw)
      (fun {Γ} (e : Env w Γ) k => k e) := by
  intro Γ e V k
  exact ⟨Γ, e, V, rfl, rfl⟩

/-! ### Head-split "cons" lemmas (the tactic-friendly form of `seq`)

`Refines.seq` is the mathematical composition rule, but `apply Refines.seq`
relies on higher-order unification to split a CPS chain `head e (fun e' =>
rest)` into `frag₁ ∘ frag₂` — which Lean's unifier cannot do (the head emitter
`emitOp`/`cp`/`emitRotr` is not a metavariable-headed application).

The **cons** lemmas below restate `seq` with the head emitter *explicit*, so
the goal's syntactic head matches the lemma's conclusion directly. They peel one
emitter per step, leaving the tail `Refines` as the single subgoal. The
`SCont`-splitter (`scont_peel`, §6) applies `Refines.consOp` against an emitter
fragment without any higher-order unification by constructing the re-associated
tail explicitly. The cons lemmas are each a one-line specialisation of
`Refines.seq` composed with the matching atomic lemma — no new denotational
reasoning. -/

/-- Peel one `emitOp` head: if the tail fragment refines `specTail`, the whole
    chain refines `specTail ∘ arithStep op dst a b`. -/
theorem Refines.consOp {w : Nat} {s : JasminTy}
    (op : JasminBinOp) (dst : Nat) (a b : Src) {specTail : StateStep w}
    {tail : {Γ : Ctxt jasminDialect} → Env w Γ → SCont w s → Com jasminDialect Γ s}
    (htail : Refines specTail tail) :
    Refines (fun vw => specTail (arithStep op dst a b vw))
      (fun {Γ} (e : Env w Γ) k =>
        emitOp e op dst a b (fun e' => tail e' k)) :=
  Refines.seq (Refines.arith op dst a b) htail

/-- Peel one `cp` head. -/
theorem Refines.consCp {w : Nat} {s : JasminTy}
    (dst src : Nat) {specTail : StateStep w}
    {tail : {Γ : Ctxt jasminDialect} → Env w Γ → SCont w s → Com jasminDialect Γ s}
    (htail : Refines specTail tail) :
    Refines (fun vw => specTail (copyStep dst src vw))
      (fun {Γ} (e : Env w Γ) k =>
        cp e dst src (fun e' => tail e' k)) :=
  Refines.seq (Refines.copy dst src) htail

/-! ## 4. A derived leaf-call lemma (`emitRotr`)

A leaf call is a fragment that internally emits several bindings but is
treated as one spec step. `emitRotr` is the representative: it emits three
`emitOp`s (`scA = src>>>n; scB = src<<<(w-n); out = scA|scB`) but its spec is
the single rotate value at `out`. The leaf lemma is *derived* from the atomic
lemmas via `seq` — demonstrating the framework composes its own leaves. -/

/-- The spec `StateStep` of `emitRotr e out src n scA scB`: the three
    intermediate writes `scA, scB, out`, expressed compositionally. (We keep
    the intermediate scratch writes in the spec — they are observable slot
    writes; downstream `rupicola` proofs discharge their values when needed.) -/
def rotrStep {w : Nat} (out src n scA scB : Nat) : StateStep w :=
  fun vw =>
    (arithStep .or out (.sl scA) (.sl scB))
      ((arithStep .shl scB (.sl src) (amt (w - n)))
        ((arithStep .shr scA (.sl src) (amt n)) vw))

/-- **Leaf-call compilation lemma** (`emitRotr`). Derived purely from
    `Refines.arith` + `Refines.seq` — no new `Com.denote` reasoning. This is
    the proof that the framework's leaf lemmas are *assembled*, not bespoke. -/
theorem Refines.leafRotr {w : Nat} {s : JasminTy} (out src n scA scB : Nat) :
    Refines (s := s) (rotrStep (w := w) out src n scA scB)
      (fun {Γ} (e : Env w Γ) k => emitRotr e out src n scA scB k) := by
  -- `emitRotr` unfolds (definitionally) to three nested `emitOp`s, and
  -- `rotrStep` to the same three `arithStep`s composed. We expose the
  -- explicit fragments/specs to `seq` so higher-order unification succeeds.
  show Refines
    (fun vw =>
      (arithStep (w := w) .or out (.sl scA) (.sl scB))
        ((arithStep (w := w) .shl scB (.sl src) (amt (w - n)))
          ((arithStep (w := w) .shr scA (.sl src) (amt n)) vw)))
    (fun {Γ} (e : Env w Γ) k =>
      emitOp e .shr scA (.sl src) (amt n) (fun e1 =>
      emitOp e1 .shl scB (.sl src) (amt (w - n)) (fun e2 =>
      emitOp e2 .or out (.sl scA) (.sl scB) k)))
  refine Refines.seq (spec₁ := fun vw =>
        (arithStep (w := w) .shl scB (.sl src) (amt (w - n)))
          ((arithStep (w := w) .shr scA (.sl src) (amt n)) vw))
      (spec₂ := arithStep (w := w) .or out (.sl scA) (.sl scB))
      (frag₁ := fun {Γ} (e : Env w Γ) k =>
        emitOp e .shr scA (.sl src) (amt n) (fun e1 =>
        emitOp e1 .shl scB (.sl src) (amt (w - n)) k))
      (frag₂ := fun {Γ} (e : Env w Γ) k =>
        emitOp e .or out (.sl scA) (.sl scB) k)
      ?_ (Refines.arith .or out (.sl scA) (.sl scB))
  exact Refines.seq (Refines.arith .shr scA (.sl src) (amt n))
    (Refines.arith .shl scB (.sl src) (amt (w - n)))

/-- Peel one `emitRotr` leaf head (the rotate analogue of `consOp`/`consCp`). -/
theorem Refines.consRotr {w : Nat} {s : JasminTy}
    (out src n scA scB : Nat) {specTail : StateStep w}
    {tail : {Γ : Ctxt jasminDialect} → Env w Γ → SCont w s → Com jasminDialect Γ s}
    (htail : Refines specTail tail) :
    Refines (fun vw => specTail (rotrStep out src n scA scB vw))
      (fun {Γ} (e : Env w Γ) k =>
        emitRotr e out src n scA scB (fun e' => tail e' k)) :=
  Refines.seq (Refines.leafRotr out src n scA scB) htail

/-! ## 5. Bounded-loop (`RFor`) compilation lemma

A bounded loop is a fixed-count `Nat.rec`/`List.foldr` over a body fragment.
The emitters realize this by *unrolling* (e.g. `emitSched`, `emitRounds`
recurse over a `List Nat`). The compilation lemma: if the body refines a
per-iteration step, the unrolled loop refines the fold of that step. -/

/-- A list-driven unrolled loop builder: fold the body fragment over `xs`,
    threading the environment. This is the shape `emitSched` / `emitRounds`
    use. -/
def forFold {w : Nat} {s : JasminTy}
    (body : Nat → {Γ : Ctxt jasminDialect} → Env w Γ → SCont w s → Com jasminDialect Γ s) :
    List Nat → {Γ : Ctxt jasminDialect} → Env w Γ → SCont w s → Com jasminDialect Γ s
  | [],      _, e, k => k e
  | x :: xs, _, e, k => body x e (fun e' => forFold body xs e' k)

/-- The corresponding spec-level fold over views. -/
def stepFold {w : Nat} (step : Nat → StateStep w) : List Nat → StateStep w
  | []      => fun vw => vw
  | x :: xs => fun vw => stepFold step xs (step x vw)

/-- **Bounded-loop compilation lemma** (`RFor`, unrolled). If for every index
    `x` the body fragment refines `step x`, the unrolled loop over `xs` refines
    the fold of the per-iteration steps. Proven by induction on `xs`, using
    `Refines.seq` at each unrolling step — i.e. the loop lemma is itself
    assembled from `seq`. -/
theorem Refines.forUnrolled {w : Nat} {s : JasminTy}
    {body : Nat → {Γ : Ctxt jasminDialect} → Env w Γ → SCont w s → Com jasminDialect Γ s}
    {step : Nat → StateStep w}
    (hbody : ∀ x, Refines (step x) (body x)) :
    ∀ (xs : List Nat), Refines (stepFold step xs) (forFold body xs) := by
  intro xs
  induction xs with
  | nil => exact Refines.skip
  | cons x xs ih =>
      -- one unrolling = seq of (body x) and (the rest). `stepFold step (x::xs)`
      -- reduces to `(stepFold step xs) ∘ (step x)` and `forFold body (x::xs)`
      -- to `fun e k => body x e (fun e' => forFold body xs e' k)`, both by `rfl`.
      show Refines (fun vw => stepFold step xs (step x vw))
        (fun e k => body x e (fun e' => forFold body xs e' k))
      exact Refines.seq (hbody x) ih

/-! ## 6. The `SCont` continuation splitter and the driving tactic

`rupicola` discharges a `Refines ?spec frag` goal by structural decomposition:
peel the head emitter, recurse on the continuation, close the base case with
`skip`. The composite spec is left as a metavariable and synthesized bottom-up.

### Why a custom splitter is needed

The naive driver `apply Refines.consOp` relies on higher-order unification to
split the goal's CPS chain `emitOp e op dst a b (fun {Γ'} e' => REST)` at the
head emitter. After the emitter is unfolded to its literal output, the
continuation carries an explicit-implicit De Bruijn context binder
`fun {Γ'} (e' : Env w Γ') => REST`. `apply Refines.consOp` must then solve
`?tail e' k =?= REST` where `?tail`'s own implicit context argument is the
*bound* `Γ'`; Lean's HO pattern unification cannot assign a metavariable to a
bound variable in that position, so `apply` diverges (whnf heartbeat blow-up).

### What the splitter does instead

`scont_peel` performs the split *by term construction*, not unification. On a
goal `Refines ?spec (fun {Γ} e k => HEAD … (fun {Γ'} e' => REST))` it:

1. enters the fragment's binders `{Γ} e k`, whnf-reduces the body (collapsing
   the `cp`/`emitRotr`/`emitSigma` wrappers and the `r3IsShr` `if`) until the
   head is a bare `emitOp e op dst a b cont`;
2. opens the continuation `cont = fun {Γ'} e' => REST`;
3. builds the tail fragment `tail := fun {Γ'} e' kt => REST[k ↦ kt]` — i.e. the
   continuation with the *outer* `k` re-abstracted as the tail's own
   continuation argument. This is the re-association the unifier cannot
   guess, produced explicitly;
4. `refine`s `Refines.consOp op dst a b (tail := tail) ?_`, leaving the tail
   `Refines ?specTail tail` as the single subgoal (`specTail`/`spec` stay
   metavariables, synthesized as the recursion unwinds).

The base case `fun {Γ} e k => k e` is closed by `Refines.skip`. Everything is
the compilation lemmas from §3–§5 — the splitter only re-associates binders so
those lemmas apply without HO unification. -/

open Lean Elab Tactic Meta in
/-- Peel one emitter head off a `Refines ?spec frag` goal by explicit tail
    construction (no higher-order unification). Reduces the head to a bare
    `emitOp` (collapsing the `cp`/`emitRotr`/`emitSigma`/`emitShr` wrappers and
    the `r3IsShr` `if`), splits the continuation, re-abstracts the outer
    continuation `k`, and refines `Refines.consOp`. Closes a `fun e k => k e`
    base case with `Refines.skip`. Fails cleanly otherwise so callers can
    `repeat` it. -/
elab "scont_peel" : tactic => do
  let g ← getMainGoal
  let ty ← g.getType
  unless ty.isAppOfArity ``Refines 4 do
    throwError "scont_peel: goal is not `Refines _ _`{indentExpr ty}"
  let tyArgs := ty.getAppArgs
  let frag := tyArgs[3]!
  let emitOpName := ``CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit.emitOp
  -- η-expand the fragment to its full `{Γ} → Env → SCont → Com` arity, so the
  -- binders `{Γ} e k` are *literal* lambdas. (A peeled tail is a metavariable
  -- value that may be η-contracted to a single leading `fun {Γ} => …`; without
  -- this expansion `lambdaTelescope` would enter only one binder.)
  let frag ← forallBoundedTelescope (← inferType frag) (some 3) fun xs _ =>
    mkLambdaFVars xs (mkAppN frag xs)
  -- Enter the fragment binders `{Γ} (e) (k)`.
  lambdaTelescope frag fun fragArgs body => do
    unless fragArgs.size == 3 do
      throwError "scont_peel: fragment is not `fun \{Γ} e k => …`"
    let kFVar := fragArgs[2]!
    -- Reduce the body head *only* through the CPS wrapper definitions
    -- (`cp`/`emitRotr`/`emitSigma`/`emitShr`) and the `r3IsShr` `if`, stopping
    -- as soon as the head is a bare `emitOp` or the continuation `k`. (Plain
    -- `whnf` would unfold `emitOp` itself down to `Com.var`.)
    let body ← whnfHeadPred body fun e => do
      let h := e.getAppFn
      pure <| !(h.isConstOf emitOpName || h == kFVar)
    let fn := body.getAppFn
    let args := body.getAppArgs
    -- Base case: `fun {Γ} e k => k e` → `body` is `k e`. Close with `skip`.
    if fn == kFVar then
      let skipPrf ← mkConstWithFreshMVarLevels ``Refines.skip
      let (skMVars, _, skConcl) ← forallMetaTelescope (← inferType skipPrf)
      unless ← withAssignableSyntheticOpaque (isDefEq skConcl ty) do
        throwError "scont_peel: skip conclusion does not match goal{indentExpr ty}"
      g.assign (mkAppN skipPrf skMVars)
      return
    -- Head case: `emitOp {w}{Γ}{s} e op dst a b cont` (9 args).
    unless fn.isConstOf ``CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit.emitOp
        && args.size == 9 do
      throwError "scont_peel: head is not `emitOp _ _ _ _ _ cont` after whnf (got {fn}, {args.size} args)"
    let op := args[4]!; let dst := args[5]!; let a := args[6]!; let b := args[7]!
    -- η-expand the continuation to its full `{Γ'} → Env → Com` arity. The last
    -- emitter in a chain passes the bare continuation `k` (not a `fun e' => …`
    -- lambda); η-expanding it to `fun {Γ'} e' => k e'` lets the uniform peel
    -- below produce a `fun e k => k e` tail, closed by `skip`.
    let cont ← forallBoundedTelescope (← inferType args[8]!) (some 2) fun xs _ =>
      mkLambdaFVars xs (mkAppN args[8]! xs)
    -- cont = fun {Γ'} (e') => REST.  Re-abstract `k` as the tail's continuation.
    lambdaTelescope cont fun contArgs rest => do
      unless contArgs.size == 2 do
        throwError "scont_peel: continuation is not `fun \{Γ'} e' => …`"
      -- tail := fun {Γ'} e' kt => REST  (with the outer `k` now the 3rd binder).
      -- This is the re-association the unifier could not guess: the
      -- continuation `cont = fun {Γ'} e' => REST` with the *outer* continuation
      -- `k` re-abstracted as the tail's own continuation argument.
      -- η-reduce *implicit*-binder lambdas in `rest` (the emitter wraps each
      -- threaded continuation as `fun {Γ'} => …`; those spurious context binders
      -- otherwise misalign the conclusion against the goal). Explicit binders
      -- (`fun e' => …`, the real environment continuations) are left intact —
      -- a blanket η-reduction would collapse `tail`'s own `e'`/`kt` binders.
      let restEta ← Meta.transform rest (post := fun e => do
        match e with
        | .lam _ _ _ bi => if bi.isImplicit then return .done e.eta else return .done e
        | _ => return .done e)
      let tail ← mkLambdaFVars (contArgs ++ #[kFVar]) restEta
      -- Instantiate `Refines.consOp`'s parameter telescope as metavariables,
      -- unify its `op/dst/a/b/tail` slots with our extracted/constructed values,
      -- and unify its conclusion with the (folded) goal — full `isDefEq` handles
      -- the `emitSigma`/`emitRotr`/`cp`/`if`/η reductions the `apply` unifier
      -- balked at. The last metavariable (`htail : Refines ?specTail tail`) is
      -- the residual goal; `specTail`/`spec` are synthesized by the unification.
      let consConst ← mkConstWithFreshMVarLevels ``Refines.consOp
      let (mvars, _, concl) ← forallMetaTelescope (← inferType consConst)
      unless mvars.size == 9 do
        throwError "scont_peel: unexpected Refines.consOp arity {mvars.size}"
      -- mvars = [w, s, op, dst, a, b, specTail, tail, htail]
      let assign (m v : Expr) : MetaM Unit := do
        unless ← isDefEq m v do throwError "scont_peel: could not set consOp argument"
      assign mvars[2]! op; assign mvars[3]! dst; assign mvars[4]! a
      assign mvars[5]! b;  assign mvars[7]! tail
      -- Unify the conclusion with the goal. `withAssignableSyntheticOpaque` so
      -- the goal's spec slot — a synthetic-opaque metavariable when the caller
      -- leaves the composite spec to be synthesized (`Refines ?spec frag`) — is
      -- assignable to the synthesized `fun vw => ?specTail (arithStep …)`.
      unless ← withAssignableSyntheticOpaque (isDefEq concl ty) do
        throwError "scont_peel: consOp conclusion{indentExpr (← instantiateMVars concl)}\ndoes not match goal{indentExpr ty}"
      g.assign (mkAppN consConst mvars)
      replaceMainGoal [mvars[8]!.mvarId!]

/-- Fully lower a `Refines ?spec frag` goal: `repeat`-apply the `scont_peel`
    splitter until the base case `fun e k => k e` is reached and closed by
    `Refines.skip`. The kernel author states `Refines ?spec frag` (the composite
    `?spec` is synthesized bottom-up as `scont_peel` unwinds) and writes neither
    the spec nor any `Com.denote` / slot-disjointness reasoning. -/
syntax "rupicola" : tactic
macro_rules
  | `(tactic| rupicola) => `(tactic| repeat scont_peel)

/-! ## 7. The Keccak instance of the framework (`KRefines` / `rupicola_keccak`)

§1–§6 are wired to the SHA-2 emitter's `Env`/`SCont`/`readSlot`/`emitOp`
substrate. The Keccak-p[1600,24] emitter (`KeccakEmit.lean`) is a structurally
parallel but **distinct** CPS layer: its bindings carry a `BState`+`immVar`
continuation (`KeccakEmit.Cont`, a *two*-argument continuation, not SHA-2's
single `Env`), its `Src` splits as `st`/`imm` (slot or literal immediate, not
`sl`/`iw`), and its denotation substrate lives in `KeccakEmitterReduction`
(`emitOp_denote`, `bsAfterOp`, `readSlot`, `readImm`, `readSlot_bsAfterOp_*`).

The Keccak round's op alphabet (FIPS 202 θρπχι) is **xor-heavy** with the χ
AND-NOT and fixed rotations: `xor`, `and`, `shl`, `shr`, `or` — all standard
`JasminBinOp`, NOT being `xor` with the all-ones mask immediate. So no new
*operator* is needed; what the framework needs is a port of the `Refines`
relation + compilation lemmas + the continuation splitter to the Keccak
substrate. That port is below: `KView`/`KStateStep`/`KRefines`, the atomic
lemmas `KRefines.arith`/`.mov`/`.rotL`, the composition rule `KRefines.seq`
with its cons forms, and a Keccak-specialised `scont_peel_keccak` elaborator
(the §6 one hardcodes `Sha2Emit.emitOp` by name) driven by `rupicola_keccak`.

The leaf lemmas — `KRefines.rotL` (the 3-binding rotate, or skip at `n=0`) and
`KRefines.mov` (the idempotent-or copy) — are *derived* from `KRefines.arith` +
`KRefines.seq`, exactly as §4's `Refines.leafRotr` is for SHA-2: the framework
assembles its own Keccak leaves. -/

namespace Keccak

open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmitterReduction

/-- The Keccak machine view: the value at every state slot and every immediate
    word. The denotational counterpart of a Keccak compilation goal. -/
structure KView where
  /-- Current value at register-file slot `i`. -/
  slot : Fin numSlots → BitVec 64
  /-- Current value at immediate word `n` (immediates are read-only). -/
  imm  : Nat → BitVec 64

/-- Extensionality for `KView`. -/
@[ext] theorem KView.ext {vw₁ vw₂ : KView}
    (hslot : vw₁.slot = vw₂.slot) (himm : vw₁.imm = vw₂.imm) : vw₁ = vw₂ := by
  cases vw₁; cases vw₂; cases hslot; cases himm; rfl

/-- Extract the Keccak readout view from a builder state + immediate resolver +
    valuation. -/
def kreadView {Γ : Ctxt jasminDialect}
    (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64) (V : Ctxt.Valuation Γ) : KView where
  slot i := readSlot bs V i
  imm  n := readImm immVar V n

/-- Resolve a Keccak `Src` operand through a view (mirrors
    `KeccakEmitterReduction.readSrc`: an immediate `.imm n` reads word
    `immIdx n`). -/
def KView.readSrc (vw : KView) : KeccakEmit.Src → BitVec 64
  | .st i  => vw.slot i
  | .imm n => vw.imm (immIdx n)

/-- A Keccak state step: a transformation of the machine view. -/
abbrev KStateStep := KView → KView

/-- The Keccak scalar-arith step: write `op (read a) (read b)` to slot `dst`. -/
def kArithStep (op : JasminBinOp) (dst : Fin numSlots) (a b : KeccakEmit.Src) : KStateStep :=
  fun vw => { vw with slot := fun i => if i = dst then op.apply (vw.readSrc a) (vw.readSrc b) else vw.slot i }

/-- The Keccak immediate-count shift step: write slot `src` shifted left (`left`)
    or right by the masked literal count `shiftMask 64 n` to slot `dst`. -/
def kShiftImmStep (left : Bool) (dst src : Fin numSlots) (n : Nat) : KStateStep :=
  fun vw => { vw with slot := (fun i =>
      if i = dst then cond left (vw.slot src <<< shiftMask 64 n) (vw.slot src >>> shiftMask 64 n)
      else vw.slot i) }

/-- `KRefines spec frag`: the emitted Keccak CPS fragment `frag` denotes its
    spec `KStateStep`. `frag` takes a builder state, an immediate resolver, and
    a `Cont`. (The Keccak analogue of §2's `Refines`, over the
    `KeccakEmit`/`KeccakEmitterReduction` substrate.) -/
def KRefines {t : JasminTy}
    (spec : KStateStep)
    (frag : {Γ : Ctxt jasminDialect} → BState Γ → (Nat → Ctxt.Var Γ r64) →
              Cont t → Com jasminDialect Γ t) : Prop :=
  ∀ {Γ : Ctxt jasminDialect} (bs : BState Γ) (immVar : Nat → Ctxt.Var Γ r64)
    (V : Ctxt.Valuation Γ) (k : Cont t),
    ∃ (Γ' : Ctxt jasminDialect) (bsF : BState Γ') (immVF : Nat → Ctxt.Var Γ' r64)
      (VF : Ctxt.Valuation Γ'),
      (frag bs immVar k).denote V = (k bsF immVF).denote VF ∧
      kreadView bsF immVF VF = spec (kreadView bs immVar V)

/-- **Keccak scalar-arith compilation lemma.** One `emitOp` refines
    `kArithStep`. The immediate words are never written, so they are preserved
    by `readImm_immVarAfter`; slot reads are pushed past `bsAfterOp` by
    `readSlot_bsAfterOp_eq/_ne`. -/
theorem KRefines.arith {t : JasminTy}
    (op : JasminBinOp) (dst : Fin numSlots) (a b : KeccakEmit.Src) :
    KRefines (t := t) (kArithStep op dst a b)
      (fun {Γ} (bs : BState Γ) immVar k => emitOp bs immVar op dst a b k) := by
  intro Γ bs immVar V k
  refine ⟨_, bsAfterOp bs dst, immVarAfter immVar,
    V.extend (op.apply (KeccakEmitterReduction.readSrc bs immVar V a)
                       (KeccakEmitterReduction.readSrc bs immVar V b)), ?_, ?_⟩
  · -- `show` normalises the goal's eta-expanded continuation (`fun {Γ'} ↦ k`)
    -- back to the bare `k` the substrate lemma is stated with.
    show (emitOp bs immVar op dst a b k).denote V = _
    exact KeccakEmitterReduction.emitOp_denote bs immVar op dst a b k V
  unfold kreadView kArithStep KView.readSrc
  ext1
  · funext i
    dsimp only
    by_cases h : i = dst
    · subst h
      cases a <;> cases b <;>
        simp [readSlot_bsAfterOp_eq, KeccakEmitterReduction.readSrc]
    · rw [readSlot_bsAfterOp_ne _ _ _ _ _ h]
      simp [h]
  · funext n
    dsimp only
    simp [readImm_immVarAfter]

/-- **Keccak sequencing compilation lemma** — the composition rule, identical
    in shape to §3's `Refines.seq` but over the two-argument Keccak
    continuation. -/
theorem KRefines.seq {t : JasminTy}
    {spec₁ spec₂ : KStateStep}
    {frag₁ frag₂ : {Γ : Ctxt jasminDialect} → BState Γ → (Nat → Ctxt.Var Γ r64) →
                     Cont t → Com jasminDialect Γ t}
    (h₁ : KRefines spec₁ frag₁) (h₂ : KRefines spec₂ frag₂) :
    KRefines (fun vw => spec₂ (spec₁ vw))
      (fun bs immVar k => frag₁ bs immVar (fun b iv => frag₂ b iv k)) := by
  intro Γ bs immVar V k
  obtain ⟨Γ₁, bs₁, iv₁, V₁, hden₁, hview₁⟩ := h₁ bs immVar V (fun b iv => frag₂ b iv k)
  obtain ⟨Γ₂, bs₂, iv₂, V₂, hden₂, hview₂⟩ := h₂ bs₁ iv₁ V₁ k
  refine ⟨Γ₂, bs₂, iv₂, V₂, ?_, ?_⟩
  · rw [hden₁, hden₂]
  · rw [hview₂, hview₁]

/-- **Keccak identity/skip compilation lemma** (the base case). -/
theorem KRefines.skip {t : JasminTy} :
    KRefines (t := t) (fun (vw : KView) => vw)
      (fun {Γ} (bs : BState Γ) immVar k => k bs immVar) := by
  intro Γ bs immVar V k
  exact ⟨Γ, bs, immVar, V, rfl, rfl⟩

/-- Peel one `emitOp` head: if the tail refines `specTail`, the chain refines
    `specTail ∘ kArithStep op dst a b`. -/
theorem KRefines.consOp {t : JasminTy}
    (op : JasminBinOp) (dst : Fin numSlots) (a b : KeccakEmit.Src) {specTail : KStateStep}
    {tail : {Γ : Ctxt jasminDialect} → BState Γ → (Nat → Ctxt.Var Γ r64) →
              Cont t → Com jasminDialect Γ t}
    (htail : KRefines specTail tail) :
    KRefines (fun vw => specTail (kArithStep op dst a b vw))
      (fun {Γ} (bs : BState Γ) immVar k =>
        emitOp bs immVar op dst a b (fun b' iv' => tail b' iv' k)) :=
  KRefines.seq (KRefines.arith op dst a b) htail

/-- **Keccak immediate-shift compilation lemma.** One `emitShImm` refines
    `kShiftImmStep`. -/
theorem KRefines.shImm {t : JasminTy}
    (left : Bool) (dst src : Fin numSlots) (n : Nat) :
    KRefines (t := t) (kShiftImmStep left dst src n)
      (fun {Γ} (bs : BState Γ) immVar k => emitShImm bs immVar left dst src n k) := by
  intro Γ bs immVar V k
  refine ⟨_, bsAfterOp bs dst, immVarAfter immVar,
    V.extend (cond left (KeccakEmitterReduction.readSlot bs V src <<< shiftMask 64 n)
      (KeccakEmitterReduction.readSlot bs V src >>> shiftMask 64 n)), ?_, ?_⟩
  · show (emitShImm bs immVar left dst src n k).denote V = _
    exact KeccakEmitterReduction.emitShImm_denote bs immVar left dst src n k V
  unfold kreadView kShiftImmStep
  ext1
  · funext i
    dsimp only
    by_cases h : i = dst
    · subst h
      simp [readSlot_bsAfterOp_eq]
    · rw [readSlot_bsAfterOp_ne _ _ _ _ _ h]
      simp [h]
  · funext m
    dsimp only
    simp [readImm_immVarAfter]

/-- Peel one `emitShImm` head: if the tail refines `specTail`, the chain refines
    `specTail ∘ kShiftImmStep left dst src n`. -/
theorem KRefines.consShImm {t : JasminTy}
    (left : Bool) (dst src : Fin numSlots) (n : Nat) {specTail : KStateStep}
    {tail : {Γ : Ctxt jasminDialect} → BState Γ → (Nat → Ctxt.Var Γ r64) →
              Cont t → Com jasminDialect Γ t}
    (htail : KRefines specTail tail) :
    KRefines (fun vw => specTail (kShiftImmStep left dst src n vw))
      (fun {Γ} (bs : BState Γ) immVar k =>
        emitShImm bs immVar left dst src n (fun b' iv' => tail b' iv' k)) :=
  KRefines.seq (KRefines.shImm left dst src n) htail

/-! ### Derived Keccak leaves (`emitMov`, `emitRotL`)

`emitMov` is one `emitOp` and the `n ≠ 0` branch of `emitRotL` is two
`emitShImm`s and one `emitOp`, so their `KRefines` facts are *assembled* from
`KRefines.arith`, `KRefines.shImm` and `KRefines.seq`. The `n = 0` branch of
`emitRotL` is the identity (`KRefines.skip`). The driver below collapses these
wrappers via whnf, so it reaches the bare `emitOp`s and `emitShImm`s directly;
these derived lemmas document the leaf
specs and are the assembled-leaf evidence (the Keccak analogue of §4's
`Refines.leafRotr`). -/

/-- The `emitMov` leaf: a slot copy `dst ← src`, realized as `or dst src src`. -/
theorem KRefines.mov {t : JasminTy} (dst src : Fin numSlots) :
    KRefines (t := t) (kArithStep .or dst (.st src) (.st src))
      (fun {Γ} (bs : BState Γ) immVar k => emitMov bs immVar dst src k) :=
  KRefines.arith .or dst (.st src) (.st src)

/-- The `n = 0` `emitRotL` leaf: the identity (no-op rotate). Proven directly
    (the fragment is *definitionally* `k bs immVar`). -/
theorem KRefines.rotL_zero {t : JasminTy} (dst : Fin numSlots) :
    KRefines (t := t) (fun vw => vw)
      (fun {Γ} (bs : BState Γ) immVar k => emitRotL bs immVar dst 0 k) := by
  intro Γ bs immVar V k
  exact ⟨Γ, bs, immVar, V, rfl, rfl⟩

/-- The `n ≠ 0` `emitRotL` leaf. The driver collapses `emitRotL` through whnf
    to its two `emitShImm`s and one `emitOp` and peels them with
    `KRefines.consShImm` / `KRefines.consOp`. This leaf lemma records the
    composite spec — `rotScr = dst >>> (64-n); dst = dst <<< n; dst = dst | rotScr`
    as two `kShiftImmStep`s and one `kArithStep` — and is discharged directly
    through the substrate denotation lemma `emitRotL_denote_pos` (the
    slot-disjointness side condition `dst ≠ rotScr` is the same one the
    substrate carries). -/
theorem KRefines.rotL_pos {t : JasminTy} (dst : Fin numSlots) (n : Nat)
    (hn : n ≠ 0) (hDst : dst ≠ rotScr) :
    KRefines (t := t)
      (fun vw =>
        (kArithStep .or dst (.st dst) (.st rotScr))
          ((kShiftImmStep true dst dst n)
            ((kShiftImmStep false rotScr dst (64 - n)) vw)))
      (fun {Γ} (bs : BState Γ) immVar k => emitRotL bs immVar dst n k) := by
  intro Γ bs immVar V k
  refine ⟨_, bsAfterRotLPos bs dst, immVarAfter (immVarAfter (immVarAfter immVar)),
    (let dstVal := KeccakEmitterReduction.readSlot bs V dst
     let scrVal := dstVal >>> shiftMask 64 (64 - n)
     let dstShl := dstVal <<< shiftMask 64 n
     let dstOut := JasminBinOp.or.apply dstShl scrVal
     ((V.extend scrVal).extend dstShl).extend dstOut), ?_, ?_⟩
  · show (emitRotL bs immVar dst n k).denote V = _
    exact emitRotL_denote_pos bs immVar dst n k V hn hDst
  · -- The final read view: `rotScr ← (slot dst) >>> (64-n)`,
    -- `dst ← or ((slot dst) <<< n) (that scrVal)` — exactly the composite
    -- step triple. All reads of unmodified slots pass through `bsAfterOp`.
    unfold kreadView kArithStep kShiftImmStep KView.readSrc bsAfterRotLPos
    have hRD : rotScr ≠ dst := fun h => hDst h.symm
    ext1
    · funext i
      dsimp only
      by_cases h1 : i = dst
      · subst h1
        simp only [readSlot_bsAfterOp_eq,
          if_neg hDst, if_neg hRD, ite_true, cond_true, cond_false]
      · by_cases h2 : i = rotScr
        · subst h2
          simp only [readSlot_bsAfterOp_ne _ _ _ _ _ hRD, readSlot_bsAfterOp_eq,
            if_neg h1, ite_true, cond_false]
        · simp only [readSlot_bsAfterOp_ne _ _ _ _ _ h1,
            readSlot_bsAfterOp_ne _ _ _ _ _ h2, if_neg h1, if_neg h2]
    · funext m
      dsimp only
      simp [readImm_immVarAfter]

/-! ### The Keccak continuation splitter (`scont_peel_keccak`)

`scont_peel` (§6) hardcodes `Sha2Emit.emitOp` and enters a *3*-binder fragment
(`{Γ} e k`). The Keccak fragment is a *4*-binder `{Γ} bs immVar k` whose head,
after collapsing the `emitMov`/`emitRotL`/`emitThetaCCol`/`emitRhoPiLane`/
`emitChiLane`/`emitIota`/`emit{Theta_C,Theta_D,RhoPi,Chi,Rounds}` wrappers and
the `if n == 0` rotate guard, is a bare `KeccakEmit.emitOp bs immVar op dst a b
cont` or `KeccakEmit.emitShImm bs immVar left dst src n cont` (9 args each), or
the base continuation `k bs immVar`. The splitter mirrors §6 exactly but for this
shape: it re-abstracts the outer `k` as the tail's own continuation and refines
`KRefines.consOp` or `KRefines.consShImm` by `isDefEq` (no HO unification). -/

open Lean Elab Tactic Meta in
/-- Peel one Keccak `emitOp` or `emitShImm` head off a `KRefines ?spec frag` goal
    by explicit tail construction. Collapses the CPS wrappers + the rotate `if`,
    splits the continuation, re-abstracts the outer `k`, and refines
    `KRefines.consOp` or `KRefines.consShImm`.
    Closes a `fun bs immVar k => k bs immVar` base case with `KRefines.skip`. -/
elab "scont_peel_keccak" : tactic => do
  let g ← getMainGoal
  let ty ← g.getType
  unless ty.isAppOfArity ``KRefines 3 do
    throwError "scont_peel_keccak: goal is not `KRefines _ _`{indentExpr ty}"
  let tyArgs := ty.getAppArgs
  let frag := tyArgs[2]!
  let emitOpName := ``CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit.emitOp
  let emitShImmName := ``CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit.emitShImm
  -- η-expand the fragment to its full `{Γ} → BState → immVar → Cont → Com` arity
  -- (4 binders), so `{Γ} bs immVar k` are literal lambdas.
  let frag ← forallBoundedTelescope (← inferType frag) (some 4) fun xs _ =>
    mkLambdaFVars xs (mkAppN frag xs)
  lambdaTelescope frag fun fragArgs body => do
    unless fragArgs.size == 4 do
      throwError "scont_peel_keccak: fragment is not `fun \{Γ} bs immVar k => …`"
    let kFVar := fragArgs[3]!
    -- Reduce the body head through the CPS wrapper definitions + the rotate `if`,
    -- stopping at a bare `emitOp`, a bare `emitShImm` or the continuation `k`.
    let body ← whnfHeadPred body fun e => do
      let h := e.getAppFn
      pure <| !(h.isConstOf emitOpName || h.isConstOf emitShImmName || h == kFVar)
    let fn := body.getAppFn
    let args := body.getAppArgs
    -- Base case: `fun {Γ} bs immVar k => k bs immVar`. Close with `skip`.
    if fn == kFVar then
      let skipPrf ← mkConstWithFreshMVarLevels ``KRefines.skip
      let (skMVars, _, skConcl) ← forallMetaTelescope (← inferType skipPrf)
      unless ← withAssignableSyntheticOpaque (isDefEq skConcl ty) do
        throwError "scont_peel_keccak: skip conclusion does not match goal{indentExpr ty}"
      g.assign (mkAppN skipPrf skMVars)
      return
    -- Head case: `emitOp {Γ}{t} bs immVar op dst a b cont` or
    -- `emitShImm {Γ}{t} bs immVar left dst src n cont` (9 args: 2 implicit
    -- `{Γ}{t}` + 7 explicit). The four step arguments sit at positions 4..7.
    unless (fn.isConstOf emitOpName || fn.isConstOf emitShImmName) && args.size == 9 do
      throwError "scont_peel_keccak: head is not `emitOp`/`emitShImm` with a continuation after whnf (got {fn}, {args.size} args)"
    let consName := if fn.isConstOf emitShImmName then ``KRefines.consShImm else ``KRefines.consOp
    let op := args[4]!; let dst := args[5]!; let a := args[6]!; let b := args[7]!
    -- η-expand the continuation to its full `{Γ'} → BState → immVar → Com` arity
    -- (3 binders). The last emitter in a chain passes the bare `k` (not a lambda);
    -- η-expanding produces a `fun bs immVar k => k bs immVar` tail, closed by `skip`.
    let cont ← forallBoundedTelescope (← inferType args[8]!) (some 3) fun xs _ =>
      mkLambdaFVars xs (mkAppN args[8]! xs)
    -- cont = fun {Γ'} (bs') (immVar') => REST. Re-abstract `k` as the tail's cont.
    lambdaTelescope cont fun contArgs rest => do
      unless contArgs.size == 3 do
        throwError "scont_peel_keccak: continuation is not `fun \{Γ'} bs' immVar' => …`"
      -- η-reduce *implicit*-binder lambdas (the emitter wraps threaded
      -- continuations as `fun {Γ'} => …`); leave explicit binders intact.
      let restEta ← Meta.transform rest (post := fun e => do
        match e with
        | .lam _ _ _ bi => if bi.isImplicit then return .done e.eta else return .done e
        | _ => return .done e)
      let tail ← mkLambdaFVars (contArgs ++ #[kFVar]) restEta
      let consConst ← mkConstWithFreshMVarLevels consName
      let (mvars, _, concl) ← forallMetaTelescope (← inferType consConst)
      unless mvars.size == 8 do
        throwError "scont_peel_keccak: unexpected {consName} arity {mvars.size}"
      -- mvars = [t, op, dst, a, b, specTail, tail, htail] for `consOp` and
      -- [t, left, dst, src, n, specTail, tail, htail] for `consShImm`.
      let assign (m v : Expr) : MetaM Unit := do
        unless ← isDefEq m v do throwError "scont_peel_keccak: could not set consOp argument"
      assign mvars[1]! op; assign mvars[2]! dst; assign mvars[3]! a
      assign mvars[4]! b;  assign mvars[6]! tail
      unless ← withAssignableSyntheticOpaque (isDefEq concl ty) do
        throwError "scont_peel_keccak: consOp conclusion{indentExpr (← instantiateMVars concl)}\ndoes not match goal{indentExpr ty}"
      g.assign (mkAppN consConst mvars)
      replaceMainGoal [mvars[7]!.mvarId!]

/-- Fully lower a Keccak `KRefines ?spec frag` goal: `repeat`-apply
    `scont_peel_keccak` until the base case is reached and closed by
    `KRefines.skip`. The composite `?spec` is synthesized bottom-up. -/
syntax "rupicola_keccak" : tactic
macro_rules
  | `(tactic| rupicola_keccak) => `(tactic| repeat scont_peel_keccak)

end Keccak

end CatCrypt.Crypto.SecureCompilation.RelationalCompile
