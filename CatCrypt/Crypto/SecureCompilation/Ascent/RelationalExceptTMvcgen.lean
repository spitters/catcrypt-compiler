/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RelationalProductMvcgen


@[expose] public section
set_option autoImplicit false

/-!
# Leakage internalized into relational Hoare over `ExceptT` (claim (b))

`Ascent/RelationalProductMvcgen.lean` (Route A) shows that a **relational** Hoare
judgment about two deterministic state programs *is* a **unary** `Std.Do`
weakest-precondition triple over their **product program** `prod`, discharged by
`mvcgen` with no new framework. This module is the `ExceptT` analogue, aimed at a
different point: **where the two programs' *leakage* lives in the relational
logic.**

A **leaky** computation is modeled in `ExceptT I m`: it either produces a normal
result (the `Except.ok`/success branch) or emits an **interface / leakage value**
of type `I` (the `Except.error` branch). For a *relational* statement about two
such programs, the postcondition is a relation on the pair of outcomes
`Except I α × Except I β`. The `Std.Do` metatheory splits any `ExceptT` triple
into a **success barrel** and an **exception barrel** (`PostShape.except`); the
central observation here is:

> the **exception barrel** of the relational postcondition **is exactly the
> leakage relation** — "when both programs leak, their interface values are
> related by `Rleak`" is not an external side-condition, it is the `.except`
> component of the relational Hoare postcondition.

So leakage is *internalized*: it is reasoned about inside the same relational
weakest-precondition calculus as the results, on the exception branch.

## Why a *product* and not a `bind`

The native `ExceptT` `bind` short-circuits on the **first** error, so a naive
`do let a ← c₁; let b ← c₂; pure (a, b)` observes at most one leakage value and
throws away the other. A relational leakage statement must observe **both**
exception branches independently. Hence the product `prodEx` explicitly combines
the two outcomes: it succeeds with `(a, b)` when **both** succeed, and otherwise
carries the **full pair** of outcomes on its own exception branch — no leakage
value is fabricated or discarded.

## The construction

* `prodExRun` / `prodEx` — the leakage-observing product of two `ExceptT I Id`
  programs, an `ExceptT (Except I α × Except I β) Id (α × β)`.
* `wp_prodEx_eq` / `Spec.wp_prodEx` — the `@[spec]` weakest precondition of the
  product (both `rfl`), so `mvcgen` walks it.
* `RelExTriple` — the relational Hoare judgment: for related inputs, the paired
  outcomes are related by `Ψ : Except I α → Except I β → Prop`.
* `relExTriple_iff_stddo` — **the bridge**: `RelExTriple` *is* the unary `Std.Do`
  triple over `prodEx`, whose postcondition is split into the success barrel
  (`fun p => Ψ (.ok p.1) (.ok p.2)`) and the exception barrel
  (`fun e => Ψ e.1 e.2`).
* `relPost` / `relExPostCond` — a relational postcondition built from a **result**
  relation `Rres` and a **leakage** relation `Rleak`.
* `relExPostCond_except_leak` — **the point of (b)**: the exception-barrel
  component of the relational postcondition, at a *both-leak* outcome
  `(.error i, .error j)`, is exactly `Rleak i j`.
* `relExTriple_relPost_leak_branch` — the interface-branch reading of the whole
  triple: whenever the two programs leak `i`/`j`, `RelExTriple` forces
  `Rleak i j`.
* `prodEx_leak_demo` — `mvcgen` discharges a relational-`ExceptT` goal for two
  concrete programs that leak related interface values.

The external-`coPara`-vs-internal-`ExceptT` *equivalence at the construction
level* and the UC simulator existential are separate concerns, out of scope
here; this module machine-checks only that leakage internalizes into relational
Hoare — the `.except` branch of the relational postcondition **is** the leakage
relation.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Std.Do

variable {I α β : Type}

/-! ## 1. Two leaky programs and their leakage-observing product

A leaky program is an `ExceptT I Id` computation: `Except.ok` is a normal result,
`Except.error` is an emitted interface / leakage value of type `I`. The product
`prodEx c₁ c₂` observes **both** exception branches: it succeeds only when both
succeed, and otherwise carries the complete pair of outcomes on its own exception
branch (so nothing is fabricated or short-circuited away). -/

/-- **The leakage-observing combine.** Both succeed ⇒ pair the results; otherwise
    carry the **full pair** of outcomes on the error branch. This is what the
    native `ExceptT` `bind` cannot do — `bind` would drop the second leakage. -/
def prodExRun (r₁ : Except I α) (r₂ : Except I β) :
    Except (Except I α × Except I β) (α × β) :=
  match r₁, r₂ with
  | .ok a, .ok b => .ok (a, b)
  | e₁, e₂ => .error (e₁, e₂)

/-- **The product of two leaky programs.** Runs both and combines the outcomes via
    `prodExRun`. Success value `α × β`; exception value the full outcome pair. -/
def prodEx (c₁ : ExceptT I Id α) (c₂ : ExceptT I Id β) :
    ExceptT (Except I α × Except I β) Id (α × β) :=
  prodExRun c₁.run c₂.run

/-! ## 2. The product weakest precondition and its `@[spec]` triple

The `PostShape` of `ExceptT (Except I α × Except I β) Id = Except (…)` is
`.except (Except I α × Except I β) .pure`: a success barrel `α × β → Prop` and one
exception barrel `(Except I α × Except I β) → Prop`. The product WP evaluates the
post on the appropriate barrel — both sides reduce definitionally (`rfl`). -/

/-- **The product WP equation.** The weakest precondition of `prodEx c₁ c₂` at
    post `Q` selects the success barrel `Q.1` when the combined outcome succeeds
    and the exception barrel `Q.2.1` when it carries a leakage pair. `rfl` (the
    product is an `ExceptT … Id` atom, so its WP is the `pushExcept` case split). -/
theorem wp_prodEx_eq (c₁ : ExceptT I Id α) (c₂ : ExceptT I Id β)
    (Q : PostCond (α × β) (.except (Except I α × Except I β) .pure)) :
    wp⟦prodEx c₁ c₂ : ExceptT (Except I α × Except I β) Id (α × β)⟧ Q
      = (match (prodEx c₁ c₂ : Except (Except I α × Except I β) (α × β)) with
          | .ok p => Q.1 p
          | .error e => Q.2.1 e) := by
  simp only [wp, ExceptT.run, Id.run, PredTrans.apply_pushExcept, PredTrans.apply_Pure_pure]
  cases (prodEx c₁ c₂) <;> rfl

/-- **The product `@[spec]` triple.** The Hoare triple for `prodEx c₁ c₂`: its
    precondition is the weakest precondition (`Q` at the selected barrel).
    `mvcgen` fires this to walk a product goal — the unary WP of the product IS
    the relational reasoning step. Proved by reflexivity of the WP. -/
@[spec]
theorem Spec.wp_prodEx (c₁ : ExceptT I Id α) (c₂ : ExceptT I Id β)
    (Q : PostCond (α × β) (.except (Except I α × Except I β) .pure)) :
    Triple (prodEx c₁ c₂ : ExceptT (Except I α × Except I β) Id (α × β))
      (match (prodEx c₁ c₂ : Except (Except I α × Except I β) (α × β)) with
        | .ok p => Q.1 p
        | .error e => Q.2.1 e)
      Q := by
  refine Triple.iff.mpr ?_
  rw [wp_prodEx_eq]

/-! ## 3. The relational triple as a unary `Std.Do` triple

`RelExTriple P c₁ c₂ Ψ` is the relational Hoare judgment on two leaky programs:
under precondition `P`, the paired outcomes are related by
`Ψ : Except I α → Except I β → Prop`. `relExTriple_iff_stddo` shows it **is** the
unary `Std.Do` triple over `prodEx c₁ c₂`, with `Ψ` split across the success and
exception barrels. -/

/-- **The relational Hoare judgment on leaky programs.** Under precondition `P`,
    the two programs' outcomes `c₁.run` and `c₂.run` are related by `Ψ` — a
    relation on `Except I α × Except I β` that can constrain both the success
    values and the leakage values. -/
def RelExTriple (P : Prop) (c₁ : ExceptT I Id α) (c₂ : ExceptT I Id β)
    (Ψ : Except I α → Except I β → Prop) : Prop :=
  P → Ψ c₁.run c₂.run

/-- **The product WP at the relational postcondition.** Splitting `Ψ` into a
    success barrel `fun p => Ψ (.ok p.1) (.ok p.2)` and an exception barrel
    `fun e => Ψ e.1 e.2`, the product weakest precondition is exactly
    `⌜Ψ c₁.run c₂.run⌝` — case analysis on the two outcomes recombines the two
    barrels into the single relation on the pair. -/
theorem wp_prodEx_post (c₁ : ExceptT I Id α) (c₂ : ExceptT I Id β)
    (Ψ : Except I α → Except I β → Prop) :
    wp⟦prodEx c₁ c₂ : ExceptT (Except I α × Except I β) Id (α × β)⟧
        (post⟨fun p => ⌜Ψ (.ok p.1) (.ok p.2)⌝, fun e => ⌜Ψ e.1 e.2⌝⟩)
      = ⌜Ψ c₁.run c₂.run⌝ := by
  rw [wp_prodEx_eq]
  simp only [prodEx, prodExRun]
  rcases hc₁ : (c₁.run : Except I α) with a | e₁ <;>
    rcases hc₂ : (c₂.run : Except I β) with b | e₂ <;> rfl

/-- **The bridge (Route A, `ExceptT` instance).** The relational Hoare judgment
    `RelExTriple P c₁ c₂ Ψ` IS the unary `Std.Do` weakest-precondition triple over
    the leakage-observing product `prodEx c₁ c₂`, whose postcondition is `Ψ` split
    across the success barrel (`fun p => Ψ (.ok p.1) (.ok p.2)`) and the exception
    barrel (`fun e => Ψ e.1 e.2`). Both sides reduce to `P → Ψ c₁.run c₂.run` via
    `wp_prodEx_post` and the nil-state entailment. So `mvcgen`, which discharges
    the right-hand triple, proves relational goals about leaky programs — with the
    leakage relation carried on the exception barrel. -/
theorem relExTriple_iff_stddo (P : Prop) (c₁ : ExceptT I Id α) (c₂ : ExceptT I Id β)
    (Ψ : Except I α → Except I β → Prop) :
    RelExTriple P c₁ c₂ Ψ ↔
      (⦃⌜P⌝⦄ (prodEx c₁ c₂ : ExceptT (Except I α × Except I β) Id (α × β))
        ⦃post⟨fun p => ⌜Ψ (.ok p.1) (.ok p.2)⌝, fun e => ⌜Ψ e.1 e.2⌝⟩⦄) := by
  rw [Triple.iff, wp_prodEx_post]
  exact Iff.rfl

/-! ## 4. Leakage lives on the exception branch (the point of (b))

A relational postcondition built from a **result** relation `Rres` and a
**leakage** relation `Rleak`. `relExPostCond_except_leak` isolates the interface
content: the exception-barrel component of the relational postcondition, at a
both-leak outcome, IS the leakage relation. -/

/-- **A relational postcondition from a result relation and a leakage relation.**
    Both succeed ⇒ relate results by `Rres`; both leak ⇒ relate leakage by
    `Rleak`; a success/leak mismatch is unrelated (`False`). -/
def relPost (Rres : α → β → Prop) (Rleak : I → I → Prop) :
    Except I α → Except I β → Prop
  | .ok a, .ok b => Rres a b
  | .error i, .error j => Rleak i j
  | _, _ => False

/-- The `Std.Do` postcondition induced by `relPost Rres Rleak`: `Rres` on the
    success barrel, and — the crux — `relPost` (hence `Rleak` on both-leak
    outcomes) on the exception barrel. -/
abbrev relExPostCond (Rres : α → β → Prop) (Rleak : I → I → Prop) :
    PostCond (α × β) (.except (Except I α × Except I β) .pure) :=
  post⟨fun p => ⌜relPost Rres Rleak (.ok p.1) (.ok p.2)⌝,
       fun e => ⌜relPost Rres Rleak e.1 e.2⌝⟩

/-- **Leakage IS the exception barrel.** The exception-barrel component of the
    relational postcondition, evaluated at a both-leak outcome
    `(.error i, .error j)`, is exactly the leakage relation `Rleak i j`. This is
    claim (b): leakage-agreement is not an external side-condition, it is the
    `.except` branch of the relational Hoare postcondition. -/
theorem relExPostCond_except_leak (Rres : α → β → Prop) (Rleak : I → I → Prop)
    (i j : I) :
    ((relExPostCond Rres Rleak).2.1 (.error i, .error j)).down ↔ Rleak i j :=
  Iff.rfl

/-- **Results ARE the success barrel.** The success-barrel component of the
    relational postcondition, evaluated at `(a, b)`, is the result relation
    `Rres a b`. The dual of `relExPostCond_except_leak`. -/
theorem relExPostCond_success_res (Rres : α → β → Prop) (Rleak : I → I → Prop)
    (a : α) (b : β) :
    ((relExPostCond Rres Rleak).1 (a, b)).down ↔ Rres a b :=
  Iff.rfl

/-- **The interface-branch reading of the whole triple.** If the two leaky
    programs both leak — `c₁` emits `i` and `c₂` emits `j` — then a `RelExTriple`
    for `relPost Rres Rleak` forces the leakage values to satisfy `Rleak i j`.
    Leakage-agreement is a *consequence* of the relational triple, extracted from
    its exception branch. -/
theorem relExTriple_relPost_leak_branch (P : Prop)
    (c₁ : ExceptT I Id α) (c₂ : ExceptT I Id β)
    (Rres : α → β → Prop) (Rleak : I → I → Prop) (i j : I)
    (h₁ : c₁.run = .error i) (h₂ : c₂.run = .error j)
    (h : RelExTriple P c₁ c₂ (relPost Rres Rleak)) (hP : P) :
    Rleak i j := by
  have hΨ := h hP
  rw [h₁, h₂] at hΨ
  exact hΨ

/-! ## 5. Demonstration: `mvcgen` discharges a relational-`ExceptT` goal

Two concrete leaky programs `c₁ = throw 3`, `c₂ = throw 5` (they leak the
interface values `3` and `5`), with the relational postcondition requiring the
leakage values to satisfy `Rleak i j := j = i + 2`. The `RelExTriple` is proved by
rewriting through the bridge `relExTriple_iff_stddo` to the unary product triple
and firing `mvcgen`: it walks `prodEx` via the `@[spec]` product WP
`Spec.wp_prodEx`, reduces the combined outcome to the leakage barrel, and
discharges the concrete leakage VC (`5 = 3 + 2`). This is the concrete witness
that unary `mvcgen` proves a relational leakage goal with the leakage relation
carried on the exception branch. -/

/-- **`mvcgen` discharges a relational leakage goal.** The relational Hoare triple
    "both programs leak, and their leakage values `3`, `5` satisfy `j = i + 2`" is
    proved by rewriting to the unary product triple (`relExTriple_iff_stddo`) and
    firing `mvcgen`. `mvcgen` walks the product program through `Spec.wp_prodEx`,
    selects the exception (leakage) barrel of the relational postcondition, and
    closes the concrete leakage VC. Route A on `ExceptT`: unary `mvcgen` proves a
    relational goal whose content lives on the exception (leakage) branch. -/
theorem prodEx_leak_demo :
    RelExTriple True
      (Except.error 3 : ExceptT Nat Id Nat)
      (Except.error 5 : ExceptT Nat Id Nat)
      (relPost (fun a b => a = b) (fun i j => j = i + 2)) := by
  rw [relExTriple_iff_stddo]
  mvcgen [prodEx, prodExRun, relPost]

end CatCrypt.Crypto.SecureCompilation.Ascent
