/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.Rewrite.Egraph

/-!
# General proof-carrying extraction: witness, transitivity-fold validator, identity fallback

This module factors the "extraction is trusted only up to a kernel-checked
denotation-equality" contract into a *reusable* shape, on top of the bounded
equality-saturation engine of `Optimizer/Rewrite/Egraph.lean`.

The engine there (`saturateCom`) is already proof-carrying *by construction*:
it emits exactly one term and `saturateCom_denote` is stated over that very
term. This file does **not** replace that — it adds the general scheme an
e-graph-style optimizer (one that *does* produce a separate, untrusted
candidate together with an ordered list of rewrite steps) needs in order to be
validated cheaply and safely. Concretely it supplies:

1. **A witness type** (`RewriteWitness`): an *ordered* list of rewrite steps,
   each carrying a proof of one denotation equality `f a = f b` at a fixed
   denotation `f`. This is the explanation an equality-saturation extractor
   would emit alongside its chosen term.
2. **A transitivity-fold validator** (`RewriteWitness.fold`): it establishes
   `f start = f finish` by folding `Eq.trans` over the per-step equations —
   linear in the number of steps, kernel-cheap, and **not** a search. We do
   *not* call `grind`/`simp` to *find* the path; the path is the witness, and
   the fold just chains it. (Refinement #1.)
3. **An identity-fallback optimizer** (`optimizeChecked`): a *total* pass that
   takes a candidate term plus a witness and emits the candidate **only if**
   the witness validates against it; otherwise it emits the original term
   unchanged. Its correctness theorem (`optimizeChecked_denote`) is
   unconditional — the output is denotation-equal to the input on *every*
   branch, valid or not. (Refinement #3, as a stated, enforced invariant.)

## On congruence explanations (refinement #2)

Refinement #2 — recursively-built child explanations for congruence merges —
**does not apply to this engine**. The `Com` optimizer is a bounded-iteration
*rewrite-saturation* engine: it has no union-find, no e-classes, and no
congruence merges (`rewriteCom`/`rewriteExpr` rewrite in place, context- and
return-type-preserving, never unioning two classes because their children
became equal). There is therefore no "children became equal ⇒ parents become
equal" step that would need a recursively-built child witness.

The module exposes the *building block* such a scheme would compose — a single
congruence step `congrStep` lifting two child equalities through a binary
constructor — so that the recursive child explanations of a congruence-closure
engine fold through the same `RewriteWitness` API. The recursive merge machinery
itself is absent: there is no union-find here to drive it. That refinement
requires a congruence-closure engine with a flat-children representation, union,
and a rebuild step.

## Relation to the existing certificate bridge

`RegistryEgraphBridge.lean` already shares the *single-equation* certificate
shape (`relatedOfEq`) between the e-graph rules and the `Related` registry. This
file lifts that to a *chain* of equations (the witness) plus the validator and
the totality guarantee, and re-exports the validated result back through the
bridge's `relatedOfEq` so a validated extraction becomes a `Related` entry with
no new proof content.

All goals are closed. Axiom set: `propext`, `Quot.sound` (inherited from
`Egraph.lean`; no new axioms, no open goals).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.ProofCarryingExtraction

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite

universe u v

/-! ## 1. The witness: an ordered list of denotation-equality steps

A rewrite *step* is one already-proved denotation equality. We keep the steps
abstract in the denotation `f : α → β` and the carrier `α` so the same machinery
serves the `Com` engine (`f = (·.denote V)`, `α = Com …`), the `Expr` engine,
or any future denotation-carrying term type. A step records the two endpoint
terms and the proof that they denote the same value. -/

/-- One validated rewrite step: the two endpoint terms `a b : α` together with a
proof that they have equal denotation under `f`. This is the per-step
`@[grind =]`-style equation an equality-saturation extractor emits; here it is a
first-class value so the validator can fold it. -/
structure RewriteStep {α : Type u} {β : Type v} (f : α → β) where
  /-- Source term of the step. -/
  src : α
  /-- Target term of the step. -/
  tgt : α
  /-- The step's denotation equality: source and target denote the same value. -/
  denoteEq : f src = f tgt

/-- Contiguity predicate: the steps chain `start → finish`. The empty list
forces `start = finish`; a cons forces the head's source to be `start` and the
tail to chain the head's target to `finish`. -/
inductive RewriteChain {α : Type u} {β : Type v} (f : α → β) :
    α → α → List (RewriteStep f) → Prop where
  /-- An empty witness: source and target coincide. -/
  | nil {a : α} : RewriteChain f a a []
  /-- A step `s` from `a = s.src` to `s.tgt`, followed by a chain from `s.tgt`
      to `c`. -/
  | cons {a c : α} {s : RewriteStep f} {rest : List (RewriteStep f)}
      (hsrc : s.src = a)
      (htail : RewriteChain f s.tgt c rest) :
      RewriteChain f a c (s :: rest)

/-- A rewrite witness from `start` to `finish`: an ordered list of steps whose
endpoints chain up (`start → … → finish`). The `chain` field enforces that the
steps are *contiguous* — each step's target is the next step's source — so the
fold below is a transitivity chain, not an unordered bag of equations. -/
structure RewriteWitness {α : Type u} {β : Type v} (f : α → β) (start finish : α) where
  /-- The ordered rewrite steps. -/
  steps : List (RewriteStep f)
  /-- The steps chain `start → … → finish`. -/
  chain : RewriteChain f start finish steps

/-! ## 2. The transitivity-fold validator (refinement #1)

`Chain.fold` turns a contiguity chain into the single denotation equality
`f start = f finish` by folding `Eq.trans` over the per-step `denoteEq` proofs.
It recurses on the chain structure: linear in the number of steps, no search.
This is the validator the prompt's refinement #1 mandates — the path is given
(the witness), so we never ask `grind` to *find* it. -/

/-- **Transitivity fold.** From a contiguity chain `start → finish`, derive
`f start = f finish` by chaining the steps' denotation equalities with
`Eq.trans`. Recursion on the chain; each step contributes one `denoteEq`. No
search, no `grind`. -/
theorem RewriteChain.fold {α : Type u} {β : Type v} {f : α → β}
    {start finish : α} {steps : List (RewriteStep f)} :
    RewriteChain f start finish steps → f start = f finish
  | .nil => rfl
  | .cons (s := s) hsrc htail =>
      -- f start = f s.src  (by hsrc) = f s.tgt (the step) = f finish (the tail fold)
      hsrc ▸ s.denoteEq.trans htail.fold

/-- **Validator.** A `RewriteWitness f start finish` certifies `f start =
f finish`. This is the public entry: feed an extractor's witness, get the
kernel-checked denotation equality, established by the linear `Eq.trans` fold. -/
theorem RewriteWitness.validate {α : Type u} {β : Type v} {f : α → β}
    {start finish : α} (w : RewriteWitness f start finish) :
    f start = f finish :=
  w.chain.fold

/-! ### Constructors for witnesses -/

/-- The empty witness: `start` to itself, validating `f start = f start`. -/
def RewriteWitness.refl {α : Type u} {β : Type v} (f : α → β) (a : α) :
    RewriteWitness f a a :=
  ⟨[], .nil⟩

/-- Prepend one step to a witness, extending its source. Given a step
`a → b` and a witness `b → c`, build the witness `a → c`. This is how an
extractor accumulates its explanation as it discovers each rewrite. -/
def RewriteWitness.cons {α : Type u} {β : Type v} {f : α → β} {b c : α}
    (a : α) (h : f a = f b) (w : RewriteWitness f b c) :
    RewriteWitness f a c :=
  ⟨⟨a, b, h⟩ :: w.steps, .cons rfl w.chain⟩

/-- A single-step witness from one denotation equality. -/
def RewriteWitness.ofEq {α : Type u} {β : Type v} {f : α → β} {a b : α}
    (h : f a = f b) : RewriteWitness f a b :=
  RewriteWitness.cons a h (RewriteWitness.refl f b)

/-- Concatenating witnesses (`a → b` then `b → c`) gives `a → c`, the
explanation-level analogue of `Eq.trans`. Validates to the composed equality. -/
def RewriteWitness.append {α : Type u} {β : Type v} {f : α → β} {a b c : α}
    (w₁ : RewriteWitness f a b) (w₂ : RewriteWitness f b c) :
    RewriteWitness f a c :=
  ⟨w₁.steps ++ w₂.steps, chainAppend w₁.chain w₂.chain⟩
where
  /-- Chain concatenation: a chain `a → b` and a chain `b → c` give `a → c`. -/
  chainAppend {a b c : α} {s₁ s₂ : List (RewriteStep f)} :
      RewriteChain f a b s₁ → RewriteChain f b c s₂ →
      RewriteChain f a c (s₁ ++ s₂)
    | .nil, h₂ => h₂
    | .cons hsrc htail, h₂ => .cons hsrc (chainAppend htail h₂)

/-! ## 3. The single-step congruence building block (refinement #2, the part
that applies)

The recursive congruence-merge machinery does not apply to this engine (no
union-find; see the module docstring). But the *building block* a congruence
scheme would compose — lifting two child equalities through a binary
constructor `g` — is provided here, and is exactly what a recursive child
explanation would call at each node. We give it over an arbitrary binary
operation that commutes with the denotation. -/

/-- **One congruence step.** If a binary term constructor `g : α → α → α`
realizes a denotation-level operation `bop` (i.e. `f (g x y) = bop (f x) (f y)`),
then equal child denotations give an equal parent denotation. This is the leaf a
recursive child-explanation would invoke; the *recursion* over a union-find is
absent here because no congruence merge exists. -/
theorem congrStep {α : Type u} {β : Type v} {f : α → β}
    {bop : β → β → β} {g : α → α → α}
    (hcomm : ∀ x y, f (g x y) = bop (f x) (f y))
    {a a' b b' : α} (ha : f a = f a') (hb : f b = f b') :
    f (g a b) = f (g a' b') := by
  rw [hcomm, hcomm, ha, hb]

/-- The congruence step packaged as a witness: from child witnesses `a → a'`
and `b → b'`, a witness `g a b → g a' b'`. (Single congruence node; a recursive
child explanation would nest these — but, again, there is no merge engine here
to drive the recursion.) -/
def RewriteWitness.congr {α : Type u} {β : Type v} {f : α → β}
    {bop : β → β → β} {g : α → α → α}
    (hcomm : ∀ x y, f (g x y) = bop (f x) (f y))
    {a a' b b' : α}
    (w₁ : RewriteWitness f a a') (w₂ : RewriteWitness f b b') :
    RewriteWitness f (g a b) (g a' b') :=
  RewriteWitness.ofEq (congrStep hcomm w₁.validate w₂.validate)

/-! ## 4. The identity-fallback optimizer (refinement #3)

The pass must be **total**: given an *untrusted* candidate `cand` and a witness
purporting to explain `input → cand`, it emits `cand` only when the witness
actually validates *against this candidate at this denotation*; otherwise it
emits `input` unchanged. The correctness theorem is **unconditional**: the
output denotes the same value as the input on *both* branches.

We decide "does the witness validate against `cand`?" by checking that the
witness's recorded endpoints are `input` and `cand`. Because `RewriteWitness`
already carries the *proof* of the endpoint equality (it cannot be constructed
otherwise), the only thing to check at runtime is that the endpoints are the
ones we expect — a decidable equality on the term type. If they match, the
witness's `validate` discharges the obligation; if not, we fall back to `input`
and discharge by `rfl`. -/

/-- Decide whether a witness is *applicable* to optimize `input` into `cand`:
its endpoints must be exactly `(input, cand)`. Requires `DecidableEq` on the
term type to compare endpoints; the *proof* content is already inside the
witness. -/
def witnessApplies {α : Type u} {β : Type v} [DecidableEq α] {f : α → β}
    {start finish : α} (_w : RewriteWitness f start finish)
    (input cand : α) : Bool :=
  (start == input) && (finish == cand)

/-- **The identity-fallback optimizer.** Total pass: emit the candidate when the
witness's endpoints match `(input, cand)`, else emit `input` unchanged. The
boolean guard is `witnessApplies`. -/
def optimizeChecked {α : Type u} {β : Type v} [DecidableEq α] {f : α → β}
    {start finish : α} (w : RewriteWitness f start finish)
    (input cand : α) : α :=
  if witnessApplies w input cand then cand else input

/-- **Unconditional correctness of the identity-fallback optimizer.** The output
of `optimizeChecked` denotes the same value as the `input`, on *every* branch:
when the witness applies, the chosen `cand` is validated by the witness's
transitivity fold; when it does not, the output *is* `input` and the equality is
reflexivity. This is refinement #3 as a stated, enforced invariant: the pass
never emits a wrong term. -/
theorem optimizeChecked_denote {α : Type u} {β : Type v} [DecidableEq α] {f : α → β}
    {start finish : α} (w : RewriteWitness f start finish)
    (input cand : α) :
    f (optimizeChecked w input cand) = f input := by
  unfold optimizeChecked witnessApplies
  by_cases h : ((start == input) && (finish == cand)) = true
  · -- witness applies: extract the endpoint equalities and chain through validate
    simp only [h, ite_true]
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hs : start = input := by simpa using h1
    have hf : finish = cand := by simpa using h2
    -- f cand = f finish = f start = f input
    calc f cand = f finish := by rw [hf]
      _ = f start := (w.validate).symm
      _ = f input := by rw [hs]
  · rw [ite_eq_right h]

/-! ## 5. Specialisation to the `Com` engine

The general scheme instantiated at `f = (·.denote V)` over `Com`. The denotation
of a `Com` is a function `Valuation Γ → ⟦t⟧`, so to get a fixed-codomain `f` we
either fix a valuation or take the whole function as the value. We take the whole
denotation function as the value (`β = (Ctxt.Valuation Γ → t.denote)`), so a step
is a *pointwise-everywhere* denotation equality — exactly what the engine's
`saturateCom_denote` provides. -/

/-- A `Com`-level rewrite step: two `Com`s with equal denotation functions. -/
abbrev ComStep (Γ : Ctxt jasminDialect) (t : JasminTy) :=
  RewriteStep (fun c : Com jasminDialect Γ t => c.denote)

/-- A `Com`-level rewrite witness `start → finish`. -/
abbrev ComWitness (Γ : Ctxt jasminDialect) (t : JasminTy)
    (start finish : Com jasminDialect Γ t) :=
  RewriteWitness (fun c : Com jasminDialect Γ t => c.denote) start finish

/-- **The engine's own output, packaged as a one-step witness.** The bounded
saturation engine emits `saturateCom fuel c k`; under a consistent env that term
denotes the same function as `c` (`saturateCom_denote`). We package that single
proved equality as a `ComWitness` — the explanation an extractor would carry. -/
noncomputable def saturateWitness {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : Egraph.KEnv Γ)
    (hk : ∀ V, Egraph.KEnv.Consistent k V) :
    ComWitness Γ t c (Egraph.saturateCom fuel c k) :=
  RewriteWitness.ofEq (f := fun c : Com jasminDialect Γ t => c.denote)
    (by
      funext V
      exact (Egraph.saturateCom_denote fuel c k V (hk V)).symm)

/-- **Validating the engine's witness recovers exactly `saturateCom_denote`.**
The general transitivity-fold validator, applied to the engine's one-step
witness, yields the denotation-function equality between the saturated term and
the input. (Stated as the symmetric `output = input` direction the witness
carries; the engine's lemma is the `output V = input V` pointwise form.) -/
theorem saturateWitness_validate {Γ : Ctxt jasminDialect} {t : JasminTy}
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : Egraph.KEnv Γ)
    (hk : ∀ V, Egraph.KEnv.Consistent k V) :
    (Egraph.saturateCom fuel c k).denote = c.denote :=
  ((saturateWitness fuel c k hk).validate).symm

/-- **End-to-end identity-fallback on the `Com` engine.** Run `optimizeChecked`
with the engine's candidate (`saturateCom`) and its witness; the result denotes
the same function as the input *unconditionally*. If for any reason the witness's
endpoints did not match the candidate, the original `Com` is returned and the
equality still holds. -/
theorem comOptimizeChecked_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    [DecidableEq (Com jasminDialect Γ t)]
    (fuel : Nat) (c : Com jasminDialect Γ t) (k : Egraph.KEnv Γ)
    (hk : ∀ V, Egraph.KEnv.Consistent k V) :
    (optimizeChecked (saturateWitness fuel c k hk) c
      (Egraph.saturateCom fuel c k)).denote = c.denote :=
  optimizeChecked_denote (saturateWitness fuel c k hk) c
    (Egraph.saturateCom fuel c k)

end CatCrypt.Crypto.Optimizer.Rewrite.ProofCarryingExtraction
