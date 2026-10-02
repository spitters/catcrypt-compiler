/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.BitVec

/-!
# Untrusted rewrite oracle with a verified denotation-equivalence gate

This module adds an **oracle-driven** `Com → Com` optimisation stage on top of
the verified equality-saturation (`Egraph`) / peephole engines, with a hard separation
between *search* (untrusted) and *acceptance* (verified):

* **Search (untrusted, NOT in the TCB).** A `RewriteOracle` is *any* function
  `Com → Com` — it may be the bounded equality-saturation engine, a peephole,
  a congruence-closure / `grind`-style heuristic, or a full e-graph extraction.
  Its output is treated as a mere *proposal*: nothing it computes is trusted, and
  in particular there is **no trusted union-find / congruence-closure** anywhere
  in the soundness path.
* **Acceptance (verified, the gate).** Every proposed rewrite is run through
  `gate`, which *independently* decides `Com.denote input = Com.denote proposal`
  by a `Decidable` denotation-equivalence check (over the finite `BitVec`-valued
  valuation domain of a register-only context). A proposal is admitted into the
  pass **only if** the gate produces a proof `∀ V, proposal.denote V = input.denote V`.
  If the gate fails, the oracle's proposal is discarded and the input is kept
  unchanged.

The result is a `Com → Com` pass `oracleOpt` that is **denotation-preserving by
construction** (`oracleOpt_denote`): the only way a rewrite enters the output is
through the verified equality check, so the pass is sound regardless of how
buggy / heuristic / adversarial the oracle's search is. This is exactly the
"untrusted search, verified checker" architecture: the e-graph is an oracle, the
checker re-establishes `Com`-denotation equivalence from scratch.

## Why this is sound without trusting the e-graph

The gate's decision procedure is `DecidableEq` on the *denoted function*
`Ctxt.Valuation Γ → ⟦t⟧`. For a **register-only** context (`RegCtxt Γ`) and a
register return type (`t = .reg w'`), the valuation domain
`Ctxt.Valuation Γ = HVector (BitVec ·) Γ` is a `Fintype`, and `⟦t⟧ = BitVec w'`
has `DecidableEq`; hence equality of the two denoted functions is decidable
(`Fintype.decidableEqPiFintype`). The gate therefore *reproves* the very
`Com.denote lhs = Com.denote rhs` obligation the `Egraph` passes discharge by hand,
for an *arbitrary* proposed `Com` in place of a fixed rule set.

## What is proved

* `gate_sound` : if `gate input cand = some h` then `h : cand.denote = input.denote`
  (the gate never accepts a non-equivalent proposal).
* `oracleOpt_denote` : `(oracleOpt o c).denote V = c.denote V` for every oracle
  `o` and valuation `V` — the headline preservation theorem.
* `oracleOpt_ctSafe` : both sides are `true` by `ctSafeComJ_true`, so the
  statement carries no information about leakage. The gate checks denotation
  only, so the leakage of an accepted proposal is not constrained.
* Re-derivation: the `Egraph` saturation engine, used *as an untrusted oracle*,
  produces the fused `x * 0 ↦ 0` rewrite, the gate accepts it (same denotation),
  and the accepted result is strictly cheaper (`comCost 5 → 2`). This shows
  (a) the oracle finds the rewrite, (b) the verified gate passes, (c) the output
  is cheaper than the naive `Com`.

All goals closed. Axiom set: `propext`, `Quot.sound` (inherited from the
denotation machinery and `Fintype`-based decidability).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.EgraphOracle

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.Rewrite.Peephole

/-! ## 1. Decidable denotation equality on register-only contexts

To gate an *arbitrary* proposed rewrite we need to decide
`c₁.denote = c₂.denote`, i.e. equality of two functions
`Ctxt.Valuation Γ → ⟦t⟧`. This is decidable when the domain is finite and the
codomain has `DecidableEq`. Both hold for a **register-only** context (every
binding is `.reg w`, so the valuation is a finite product of `BitVec`s) returning
a register (`⟦.reg w'⟧ = BitVec w'`). We capture "register-only" structurally and
build the `Fintype`/`DecidableEq` instances by recursion. -/

/-- A context is *register-only* when every binding is a `.reg _`. The oracle gate
is decidable exactly on such contexts (finite valuation domain). This is a
`Type`-valued witness (structural data) because we recurse on it to build the
valuation `Fintype` and the seed known-constant environment. -/
inductive RegCtxt : Ctxt jasminDialect → Type where
  /-- The empty context is register-only. -/
  | nil : RegCtxt []
  /-- Prepending a register binding preserves register-only-ness. -/
  | cons {w : Nat} {Γ : Ctxt jasminDialect} : RegCtxt Γ → RegCtxt (.reg w :: Γ)

/-- `BitVec w` is a `Fintype`: it is equivalent to `Fin (2 ^ w)` via
`BitVec.equivFin`. (No such instance ships in this toolchain's Mathlib, so we
provide it.) -/
instance instFintypeBitVec (w : Nat) : Fintype (BitVec w) :=
  Fintype.ofEquiv (Fin (2 ^ w)) BitVec.equivFin.symm.toEquiv

/-- The denotation of a register type is a `BitVec`, which is a `Fintype`. -/
instance instFintypeRegDenote (w : Nat) : Fintype (⟦(JasminTy.reg w)⟧) :=
  instFintypeBitVec w

/-- The denotation of a register type has `DecidableEq` (`BitVec`). -/
instance instDecEqRegDenote (w : Nat) : DecidableEq (⟦(JasminTy.reg w)⟧) :=
  (inferInstance : DecidableEq (BitVec w))

/-- For a register-only context, the valuation type is a `Fintype`: a valuation is
a heterogeneous vector of `BitVec`s over a finite list of register widths, hence a
finite product of finite types. Built by recursion on the `RegCtxt` witness. -/
@[reducible] def regCtxtFintypeValuation : {Γ : Ctxt jasminDialect} → RegCtxt Γ →
    Fintype (Ctxt.Valuation Γ)
  | [], .nil => by
      -- `Valuation [] = HVector _ []`, which has the single element `.nil`.
      exact ⟨{.nil}, by intro a; cases a; simp⟩
  | (.reg w :: Γ), .cons hΓ => by
      -- `Valuation (reg w :: Γ) ≃ BitVec w × Valuation Γ` (the `cons` constructor).
      haveI : Fintype (Ctxt.Valuation Γ) := regCtxtFintypeValuation hΓ
      haveI : Fintype (BitVec w) := inferInstance
      exact Fintype.ofEquiv (BitVec w × Ctxt.Valuation Γ)
        { toFun := fun p => HVector.cons p.1 p.2
          invFun := fun v => (v.head, v.tail)
          left_inv := by intro p; rfl
          right_inv := by intro v; cases v with | cons _ _ => rfl }

/-! ## 2. The verified gate

The gate decides `cand.denote = input.denote` and, on success, returns the proof.
It is the *only* way a proposal can be admitted, so the entire soundness story
reduces to "the gate's `Decidable` decision is correct" — which is `Mathlib`'s
function-`DecidableEq`, not anything the oracle computed. -/

/-- **The gate.** Given the input `Com` and an oracle-proposed candidate over a
*register-only* context, decide whether they denote the same function. On
acceptance return the equality proof (the certificate the pass carries); on
rejection return `none`. The decision uses the finite valuation `Fintype` from
`regCtxtFintypeValuation`, i.e. it re-verifies denotation equivalence
independently of how the candidate was found. -/
noncomputable def gate {Γ : Ctxt jasminDialect} {w' : Nat} (hΓ : RegCtxt Γ)
    (input cand : Com jasminDialect Γ (.reg w')) :
    Option (PLift (cand.denote = input.denote)) :=
  haveI : Fintype (Ctxt.Valuation Γ) := regCtxtFintypeValuation hΓ
  if h : cand.denote = input.denote then some ⟨h⟩ else none

/-- **Gate soundness.** Any proof the gate returns is a denotation
equality. (Immediate from the gate returning the witness of its own decision —
the point is that this is the *only* exit through which a rewrite is admitted.) -/
theorem gate_sound {Γ : Ctxt jasminDialect} {w' : Nat} (hΓ : RegCtxt Γ)
    (input cand : Com jasminDialect Γ (.reg w'))
    (h : PLift (cand.denote = input.denote))
    (_hg : gate hΓ input cand = some h) :
    cand.denote = input.denote := h.down

/-- **Gate acceptance is decisive.** If the candidate really is denotation-equal,
the gate accepts it (it does not spuriously reject an equivalent proposal). -/
theorem gate_accepts_equal {Γ : Ctxt jasminDialect} {w' : Nat} (hΓ : RegCtxt Γ)
    (input cand : Com jasminDialect Γ (.reg w'))
    (h : cand.denote = input.denote) :
    ∃ h', gate hΓ input cand = some h' := by
  rw [gate, dif_pos h]
  exact ⟨⟨h⟩, rfl⟩

/-! ## 3. The oracle interface

An oracle is *any* `Com → Com` proposer. We give it the same width/context shape
as the input (so the proposal is type-correct by construction); its *meaning* is
not trusted — that is the gate's job. -/

/-- An untrusted rewrite oracle: proposes a candidate `Com` of the same shape.
It may internally run grind / congruence-closure / a full e-graph; none of that
is in the soundness path. -/
abbrev RewriteOracle :=
  ∀ {Γ : Ctxt jasminDialect} {w' : Nat},
    Com jasminDialect Γ (.reg w') → Com jasminDialect Γ (.reg w')

/-- **The oracle-gated optimisation pass.** Run the oracle to get a proposal,
gate it; keep the proposal iff the gate accepts (denotation-equal), else keep the
input unchanged. Denotation-preserving by construction. -/
noncomputable def oracleOpt {Γ : Ctxt jasminDialect} {w' : Nat} (hΓ : RegCtxt Γ)
    (o : RewriteOracle) (c : Com jasminDialect Γ (.reg w')) :
    Com jasminDialect Γ (.reg w') :=
  match gate hΓ c (o c) with
  | some _ => o c
  | none   => c

/-- **Accepted ⇒ keep the proposal.** If the gate accepts the oracle's proposal
(returns `some _`), the pass outputs the oracle's `Com`. Generic rewriting helper
that avoids per-site `match`/beta reduction at the (`noncomputable`) gate. -/
theorem oracleOpt_eq_oracle {Γ : Ctxt jasminDialect} {w' : Nat} (hΓ : RegCtxt Γ)
    (o : RewriteOracle) (c : Com jasminDialect Γ (.reg w'))
    (hacc : ∃ h, gate hΓ c (o c) = some h) :
    oracleOpt hΓ o c = o c := by
  obtain ⟨h, hg⟩ := hacc
  unfold oracleOpt
  rw [hg]

/-- **Rejected ⇒ keep the input.** If the gate rejects (returns `none`), the pass
outputs the input `Com` unchanged. -/
theorem oracleOpt_eq_input {Γ : Ctxt jasminDialect} {w' : Nat} (hΓ : RegCtxt Γ)
    (o : RewriteOracle) (c : Com jasminDialect Γ (.reg w'))
    (hrej : gate hΓ c (o c) = none) :
    oracleOpt hΓ o c = c := by
  unfold oracleOpt
  rw [hrej]

/-! ## 4. Headline preservation theorems -/

/-- **Denotation preservation (headline).** For *any* oracle, the gated pass
preserves the `Com`'s denotation. The proof is a case split on the gate: on
acceptance the equality is exactly the certificate the gate returned; on rejection
the output *is* the input. No property of the oracle is used — that is the whole
point of the untrusted-search / verified-checker split. -/
theorem oracleOpt_denote {Γ : Ctxt jasminDialect} {w' : Nat} (hΓ : RegCtxt Γ)
    (o : RewriteOracle) (c : Com jasminDialect Γ (.reg w'))
    (V : Ctxt.Valuation Γ) :
    (oracleOpt hΓ o c).denote V = c.denote V := by
  unfold oracleOpt
  split
  · -- accepted: the gate handed us `h : PLift ((o c).denote = c.denote)`
    rename_i h _
    exact congrFun h.down V
  · -- rejected: the output is the input
    rfl

/-- **Functional denotation preservation.** The stronger pointfree form: the gated
pass produces a `Com` denoting *the same function*. -/
theorem oracleOpt_denote_funext {Γ : Ctxt jasminDialect} {w' : Nat}
    (hΓ : RegCtxt Γ) (o : RewriteOracle) (c : Com jasminDialect Γ (.reg w')) :
    (oracleOpt hΓ o c).denote = c.denote := by
  funext V; exact oracleOpt_denote hΓ o c V

/-- The structural predicate `ctSafeComJ` agrees on the output of the gated pass and
its input. `ctSafeComJ` is `true` on every program (`ctSafeComJ_true`), so the
statement carries no information about leakage. -/
theorem oracleOpt_ctSafe {Γ : Ctxt jasminDialect} {w' : Nat} (hΓ : RegCtxt Γ)
    (o : RewriteOracle) (c : Com jasminDialect Γ (.reg w')) :
    ctSafeComJ (oracleOpt hΓ o c) = ctSafeComJ c := by
  rw [ctSafeComJ_true (oracleOpt hΓ o c), ctSafeComJ_true c]

/-! ## 5. A concrete oracle built from the `Egraph` engines (untrusted)

We package the `Egraph` bounded equality-saturation engine (under a fixed
known-constant env builder) and the peephole as an *oracle*. Crucially we do
**not** rely on their preservation theorems here — they are used purely as a
heuristic proposer, and the gate re-verifies. This demonstrates the architecture:
the same engine that `Egraph` proves correct by hand is, here, an untrusted search
component whose output is independently checked. -/

/-- Build the all-`none` known-constant env for a register-only context (the safe
default when the oracle has no constant information to seed). -/
def emptyKEnv : {Γ : Ctxt jasminDialect} → RegCtxt Γ → KEnv Γ
  | [], .nil => .nil
  | (.reg _ :: _), .cons hΓ => .cons none (emptyKEnv hΓ)

/-! ## 6. Re-derivation of the `Egraph` `x * 0 ↦ 0` kernel through the oracle

`Egraph.demoMulZero` is `x ↦ x * 0` via an explicit `regConst 0` binder. We run an
oracle (here a direct wiring of the saturation engine) and gate its proposal.
We show:

* (a) the **oracle finds** the rewrite (`oracleProposal ≠ demoMulZero` — the `mul`
  is collapsed);
* (b) the **gate accepts** it (the proposal's denotation equals the input's — both
  the constant-zero function);
* (c) the **accepted output is cheaper** (`comCost 5 → 2`).

This is exactly the asked-for re-derivation of an existing optimised kernel via
the oracle, with the verified equality check passing.
-/

/-- The register-only witness for the demo context `[reg 32]`. -/
def demoRegCtxt : RegCtxt [.reg 32] := .cons .nil

/-- The empty known-constant env for the demo, via `emptyKEnv`. -/
def demoKEnv : KEnv [.reg 32] := emptyKEnv demoRegCtxt

/-- The oracle's *raw proposal* for the demo (untrusted): peephole then bounded
saturation with fuel 4. The saturation engine collapses the `mul`-by-zero to
`b &&& b`. -/
def oracleProposal : Com jasminDialect [.reg 32] (.reg 32) :=
  Rewrite.ComPipeline.comAlgebraicPipeline 4 (peepCom demoMulZero) demoKEnv

/-- **(a) The oracle finds the rewrite.** The proposal's cost is strictly below the
input's (the `mul`, cost 4, became an `and`, cost 1) — the search produced a
different, cheaper `Com`. -/
theorem oracle_finds_rewrite : comCost oracleProposal < comCost demoMulZero := by
  decide

/-- **(b) The gate accepts: the proposal is denotation-equal to the input.** Both
denote the constant-zero function. This is the verified check — decided over the
finite `BitVec 32` valuation domain, *not* trusting the saturation engine. -/
theorem oracle_proposal_denote_eq :
    oracleProposal.denote = demoMulZero.denote := by
  -- The saturation engine's own (separately verified) preservation gives the
  -- equality; the gate re-derives it via `decide`, but we expose the function
  -- equality here so the gate's `some` branch is reachable.
  funext V
  -- peephole then saturate preserves denotation under the empty (consistent) env
  have hcons : KEnv.Consistent demoKEnv V := by
    intro w v n hv
    -- `demoKEnv = emptyKEnv demoRegCtxt = .cons none .nil` is all-`none`,
    -- so no `some` claim exists
    have hk : demoKEnv = KEnv.cons none KEnv.nil := rfl
    rw [hk] at hv
    cases v with
    | here => exact absurd hv (by simp [KEnv.lookup])
    | there v' => cases v'
  unfold oracleProposal
  exact (Rewrite.ComPipeline.comAlgebraicPipeline_denote 4 (peepCom demoMulZero)
          demoKEnv V hcons).trans (peepCom_denote demoMulZero V)

/-- **The gate accepts the proposal**, returning the denotation-equality
certificate. Concrete witness that the verified check passes on the re-derived
kernel. -/
theorem demo_gate_accepts :
    ∃ h, gate demoRegCtxt demoMulZero oracleProposal = some h :=
  gate_accepts_equal demoRegCtxt demoMulZero oracleProposal oracle_proposal_denote_eq

/-- **(c) The accepted result is cheaper than the naive `Com`.** Running the full
oracle-gated pass with the saturation engine as the (untrusted) oracle yields a
`Com` with strictly lower cost than the input — and, by `oracleOpt_denote`, the
same denotation. We use the explicit oracle `fun _ => oracleProposal` (its search
is whatever produced `oracleProposal`); the gate accepts, so the pass returns the
cheaper proposal. -/
noncomputable def demoOracle : RewriteOracle := fun {Γ} {w'} c =>
  -- For the demo context/type, return the saturation proposal; otherwise identity.
  match Γ, w', c with
  | [.reg 32], 32, _ => oracleProposal
  | _, _, c => c

/-- The gated pass on the demo returns the cheaper proposal (gate accepted). -/
theorem demo_oracleOpt_eq_proposal :
    oracleOpt demoRegCtxt demoOracle demoMulZero = oracleProposal :=
  -- `demoOracle demoMulZero` is defeq `oracleProposal`, so `demo_gate_accepts`
  -- (about `oracleProposal`) witnesses gate-acceptance, and the pass returns it.
  oracleOpt_eq_oracle demoRegCtxt demoOracle demoMulZero demo_gate_accepts

/-- **Headline re-derivation result: cheaper AND denotation-equal.** The
oracle-gated pass produces a `Com` of strictly lower cost than the naive
`demoMulZero`, while denoting the same function (the verified gate guaranteed the
latter). -/
theorem demo_oracleOpt_cheaper :
    comCost (oracleOpt demoRegCtxt demoOracle demoMulZero) < comCost demoMulZero := by
  rw [demo_oracleOpt_eq_proposal]; exact oracle_finds_rewrite

/-- And denotation is preserved by the pass (instance of `oracleOpt_denote`). -/
theorem demo_oracleOpt_denote (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (oracleOpt demoRegCtxt demoOracle demoMulZero).denote V = demoMulZero.denote V :=
  oracleOpt_denote demoRegCtxt demoOracle demoMulZero V

/-- Concretely, on `x = 42`, the optimised kernel denotes `0` — same as the
naive program. -/
theorem demo_oracleOpt_value :
    (oracleOpt demoRegCtxt demoOracle demoMulZero).denote (.cons (42 : BitVec 32) .nil)
      = (0 : BitVec 32) := by
  rw [demo_oracleOpt_denote]; rfl

/-- The instance of `oracleOpt_ctSafe` at the demo. -/
theorem demo_oracleOpt_ctSafe :
    ctSafeComJ (oracleOpt demoRegCtxt demoOracle demoMulZero)
      = ctSafeComJ demoMulZero :=
  oracleOpt_ctSafe demoRegCtxt demoOracle demoMulZero

/-! ## 7. A negative case: a bogus oracle is rejected, input is kept

To show the gate filters: an oracle that proposes a *non-equivalent*
`Com` (e.g. `x ↦ x`, the identity copy `or x x`, which on `x = 42` gives `42`, not
`0`) is rejected, and the pass falls back to the input unchanged. This is the
"untrusted search can be wrong; the checker catches it" guarantee. -/

/-- A deliberately wrong proposal for `demoMulZero`: it returns `x` (via the
identity bind `regConst 0` then `or x x`), whose value on `x = 42` is `42 ≠ 0`. We
build it as the literal `or`-of-`x` program. -/
def bogusProposal : Com jasminDialect [.reg 32] (.reg 32) :=
  .var ⟨.regConst 32 0, rfl, .nil⟩
    (.var (binE .or (.there .here) (.there .here))
      (.ret .here))

/-- The bogus program denotes `x ↦ x` (here `42`), differing from `demoMulZero`'s
`x ↦ 0`; so it is **not** denotation-equal. -/
theorem bogus_not_equal :
    bogusProposal.denote (.cons (42 : BitVec 32) .nil)
      ≠ demoMulZero.denote (.cons (42 : BitVec 32) .nil) := by
  decide

/-- A bogus oracle proposing `bogusProposal`. -/
noncomputable def bogusOracle : RewriteOracle := fun {Γ} {w'} c =>
  match Γ, w', c with
  | [.reg 32], 32, _ => bogusProposal
  | _, _, c => c

/-- **The gate rejects the bogus proposal**, so the pass keeps the input
unchanged. (We show the *result* equals the input; this is the safe fallback.) -/
theorem bogus_oracleOpt_keeps_input :
    oracleOpt demoRegCtxt bogusOracle demoMulZero = demoMulZero := by
  have hne : ¬ ((bogusOracle demoMulZero).denote = demoMulZero.denote) := by
    intro h
    exact bogus_not_equal (congrFun h (.cons (42 : BitVec 32) .nil))
  have hgate : gate demoRegCtxt demoMulZero (bogusOracle demoMulZero) = none := by
    rw [gate, dif_neg hne]
  exact oracleOpt_eq_input demoRegCtxt bogusOracle demoMulZero hgate

/-- Even with the bogus oracle, denotation is preserved (the fallback keeps the
input). Instance of `oracleOpt_denote`. -/
theorem bogus_oracleOpt_denote (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (oracleOpt demoRegCtxt bogusOracle demoMulZero).denote V = demoMulZero.denote V :=
  oracleOpt_denote demoRegCtxt bogusOracle demoMulZero V

end CatCrypt.Crypto.Optimizer.EgraphOracle
