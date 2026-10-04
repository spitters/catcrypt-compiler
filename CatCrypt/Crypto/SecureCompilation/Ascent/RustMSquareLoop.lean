/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RustMSquare

/-!
# Counted loops in the `RustM` correspondence square

This module gives the loop rule for the square `CorresM P G p V Q` of
`Ascent/RustMSquare.lean` and derives it from the total-correctness invariant rule
`Aeneas.Std.loop.spec_decr_nat` of hax-lean.

## The loop form

The concrete loop is hax-lean's `loop` combinator, iterating a body
`α → RustM (ControlFlow α β)` until it returns `.done`. A counted loop of `N` trips over
a state-passing body `body : Nat → C → RustM (Unit × C)` is `loopK N body`: the loop
state is a pair `(i, c)` of a counter and a concrete state, and one trip `countedBody`
runs `body i c` and continues with `(i + 1, c')` while `i < N`, and stops with `((), c)`
once `i = N`. This is the shape of the loop hax emits for a `while` loop over a counter.

The abstract side is `ifold fa N σ`, the `N`-fold application of an index-dependent step
`fa : Nat → S → S`, peeling the last trip. It is the recursion of `ifold` in
`Ascent/MlkemPolyFoldCorres.lean`, restated here so that this module depends on
`RustMSquare` alone.

## The rules

* `corresM_loop` is the square for an arbitrary `loop` from an invariant `inv σ x` on the
  loop state and a natural-number measure, indexed by the abstract state `σ`. Its proof
  is one instance of `loop.spec_decr_nat` at each abstract state, followed by
  `spec_imp_exists`.
* `corresM_loopK` is the counted-loop rule: if at every trip `i < N` the body is in the
  square from the invariant relation `R` to `R` after the step `fa i`, under a per-trip
  guard `Gb i`, and the loop guard `G σ` implies `Gb i (ifold fa i σ)` for every trip,
  then `loopK N body` is in the square from `R` to `R` at `ifold fa N σ`. It is
  `corresM_loop` at the invariant `i ≤ N ∧ R c (ifold fa i σ)` and the measure `N - i`;
  `countedBody_spec` discharges the premise of the invariant rule from the body squares.
* `corresM_loop_iff_spec` states the converse reading: a square over a `loop` program is
  exactly a `spec` of `loop` at every entry state, with the postcondition pinning the
  value and relating the exit state by `Q`.

## Main definitions

* `ifold` — the index-dependent iterate of the abstract step
* `countedBody`, `loopK` — one trip of the counted loop and the loop itself
* `corresM_loop` — the square of a `loop` from the invariant rule
* `corresM_loopK` — the counted-loop rule
* `corresM_loop_iff_spec` — the square of a `loop` as a `spec` of `loop`
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent.RustM

open Aeneas.Std

variable {C S A : Type}

/-! ## The counted loop -/

/-- `N`-fold application of the index-dependent step `fa`, peeling the last trip
    (`n + 1 ↦ fa n ∘ ifold fa n`). -/
def ifold (fa : Nat → S → S) : Nat → S → S
  | 0, a => a
  | n + 1, a => fa n (ifold fa n a)

/-- One trip of the counted loop of `N` trips: below the bound run `body i` and continue
    with the next counter, at the bound stop with the current concrete state. -/
def countedBody (N : Nat) (body : Nat → C → Aeneas.Std.RustM (Unit × C)) (x : Nat × C) :
    Aeneas.Std.RustM (ControlFlow (Nat × C) (Unit × C)) :=
  if x.1 < N then
    (body x.1 x.2) >>= fun r => .ok (.cont (x.1 + 1, r.2))
  else .ok (.done ((), x.2))

/-- The counted loop of `N` trips over `body`, written with hax-lean's `loop`, starting
    the counter at `0`. -/
def loopK (N : Nat) (body : Nat → C → Aeneas.Std.RustM (Unit × C)) :
    C → Aeneas.Std.RustM (Unit × C) :=
  fun c => loop (countedBody N body) (0, c)

/-! ## The square of a `loop` from the invariant rule -/

/-- **The square of a `loop` from the invariant rule.** At each abstract state `σ` under
    the guard, an invariant `inv σ` on the loop state holding initially and preserved by
    every `.cont` trip with a decreasing measure, and a `.done` trip returning
    `(V σ, c')` with `Q c' σ`, give the square for the loop. The proof instantiates
    `loop.spec_decr_nat` at `inv σ` and `measure σ`. -/
theorem corresM_loop {α : Type} {P Q : C → S → Prop} {G : S → Prop} {V : S → A}
    {body : α → Aeneas.Std.RustM (ControlFlow α (A × C))} {init : C → α}
    (inv : S → α → Prop) (measure : S → α → Nat)
    (hinit : ∀ c σ, P c σ → G σ → inv σ (init c))
    (hbody : ∀ σ, G σ → ∀ x, inv σ x → WP.spec (body x) (fun r => match r with
      | .done y => ∃ c', y = (V σ, c') ∧ Q c' σ
      | .cont x' => inv σ x' ∧ measure σ x' < measure σ x)) :
    CorresM P G (fun c => loop body (init c)) V Q := by
  intro c σ hP hG
  have hspec := loop.spec_decr_nat (measure σ) (inv σ)
    (fun y => ∃ c', y = (V σ, c') ∧ Q c' σ) body (init c) (fun x hx => by
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (hbody σ hG x hx)
      exact WP.exists_imp_spec ⟨r, hr, by cases r <;> exact hp⟩) (hinit c σ hP hG)
  obtain ⟨y, hy, c', rfl, hQ⟩ := WP.spec_imp_exists hspec
  exact ⟨c', hy, hQ⟩

/-- **The square of a `loop` as a `spec` of `loop`.** The square over the program
    `fun c => loop body (init c)` holds exactly when, from every entry state, `loop`
    returns `(V σ, c')` for a `c'` related to `σ` by `Q`. -/
theorem corresM_loop_iff_spec {α : Type} {P Q : C → S → Prop} {G : S → Prop} {V : S → A}
    {body : α → Aeneas.Std.RustM (ControlFlow α (A × C))} {init : C → α} :
    CorresM P G (fun c => loop body (init c)) V Q ↔
      ∀ c σ, P c σ → G σ →
        WP.spec (loop body (init c)) (fun y => ∃ c', y = (V σ, c') ∧ Q c' σ) := by
  constructor
  · intro h c σ hP hG
    obtain ⟨c', hc, hQ⟩ := h c σ hP hG
    exact WP.exists_imp_spec ⟨_, hc, c', rfl, hQ⟩
  · intro h c σ hP hG
    obtain ⟨y, hy, c', rfl, hQ⟩ := WP.spec_imp_exists (h c σ hP hG)
    exact ⟨c', hy, hQ⟩

/-! ## The counted-loop rule -/

/-- **The premise of the invariant rule for the counted loop.** From the body squares,
    one trip of `countedBody N body` from a state `(i, c)` with `i ≤ N` and
    `R c (ifold fa i σ)` either continues with the invariant at `i + 1` and a smaller
    measure `N - i`, or stops at `i = N` returning `((), c)` with `R c (ifold fa N σ)`. -/
theorem countedBody_spec {R : C → S → Prop} {Gb : Nat → S → Prop} {G : S → Prop}
    {fa : Nat → S → S} {N : Nat} {body : Nat → C → Aeneas.Std.RustM (Unit × C)}
    (hbody : ∀ i, i < N →
      CorresM R (Gb i) (body i) (fun _ => ()) (fun c σ => R c (fa i σ)))
    (hG : ∀ σ, G σ → ∀ i, i < N → Gb i (ifold fa i σ))
    (σ : S) (hGσ : G σ) (x : Nat × C) (hx : x.1 ≤ N ∧ R x.2 (ifold fa x.1 σ)) :
    WP.spec (countedBody N body x) (fun r => match r with
      | .done y => ∃ c', y = ((), c') ∧ R c' (ifold fa N σ)
      | .cont x' => (x'.1 ≤ N ∧ R x'.2 (ifold fa x'.1 σ)) ∧ N - x'.1 < N - x.1) := by
  obtain ⟨i, c₀⟩ := x
  obtain ⟨hi, hR₀⟩ := hx
  unfold countedBody
  by_cases hlt : i < N
  · obtain ⟨c₁, h₁, hR₁⟩ := hbody i hlt c₀ (ifold fa i σ) hR₀ (hG σ hGσ i hlt)
    simp only [hlt, if_true, h₁, bind_tc_ok, WP.spec_ok]
    exact ⟨⟨hlt, hR₁⟩, by omega⟩
  · have hiN : i = N := by omega
    subst hiN
    simp only [hlt, if_false, WP.spec_ok]
    exact ⟨c₀, rfl, hR₀⟩

/-- **The counted-loop rule.** If at every trip `i < N` the body is in the square from the
    invariant relation `R` to `R` after the step `fa i` under the guard `Gb i`, and the
    loop guard implies each trip's guard at the intermediate abstract state
    `ifold fa i σ`, then the counted loop `loopK N body` is in the square from `R` to `R`
    at `ifold fa N σ`. It is `corresM_loop` at the invariant `i ≤ N ∧ R c (ifold fa i σ)`
    and the measure `N - i`. -/
theorem corresM_loopK {R : C → S → Prop} {Gb : Nat → S → Prop} {G : S → Prop}
    {fa : Nat → S → S} {N : Nat} {body : Nat → C → Aeneas.Std.RustM (Unit × C)}
    (hbody : ∀ i, i < N →
      CorresM R (Gb i) (body i) (fun _ => ()) (fun c σ => R c (fa i σ)))
    (hG : ∀ σ, G σ → ∀ i, i < N → Gb i (ifold fa i σ)) :
    CorresM R G (loopK N body) (fun _ => ()) (fun c σ => R c (ifold fa N σ)) :=
  corresM_loop (fun σ x => x.1 ≤ N ∧ R x.2 (ifold fa x.1 σ)) (fun _ x => N - x.1)
    (fun _ _ hR _ => ⟨Nat.zero_le N, hR⟩) (fun σ hGσ x hx => by
      obtain ⟨r, hr, hp⟩ := WP.spec_imp_exists (countedBody_spec hbody hG σ hGσ x hx)
      exact WP.exists_imp_spec ⟨r, hr, by cases r <;> exact hp⟩)

end Hax.Ascent.RustM
