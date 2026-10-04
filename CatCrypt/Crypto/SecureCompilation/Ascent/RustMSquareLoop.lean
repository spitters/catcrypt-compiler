/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RustMSquare
public import HaxLean.HaxBackendPrelude

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
`Ascent/MlkemPolyFoldCorres.lean`, restated here because that module imports the LowCT
`Corres` closure (through `MlkemPolyAddCapstone` and `KeystoneControl`), while this one
imports `RustMSquare` and hax-lean's `HaxBackendPrelude` only.

## The extracted range loop

hax-lean's `fold_range s e inv init body` (`HaxBackendPrelude`) runs
`body : α → UScalar ty → RustM α` on the indices `s, …, e - 1`, each index encoded as
`⟨BitVec.ofNat _ i⟩`; the invariant `inv` is not evaluated. Its square program
`foldRangeK s e inv body` takes the accumulator `α` as the concrete state `C` and `()` as
the value (`A = Unit`), and trip `i` of the counted loop is `foldRangeTrip s body i`,
`body` at the index `s + i`. `foldRangeK_eq_loopK` identifies `foldRangeK` with
`loopK (e - s) (foldRangeTrip s body)`, so the counted-loop rule applies to an extracted
`for i in s..e` loop. The index encoding does not wrap because `e < 2 ^ ty.numBits` holds
for every `e : UScalar ty` (`foldRange_index_val`).

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
* `unitAccK`, `foldRangeTrip`, `foldRangeK` — `fold_range` and its trips as square programs
* `foldRange_index_val` — the value of the index of trip `i`
* `foldRangeK_eq_loopK` — `fold_range` is the counted loop of `e - s` trips
* `corresM_foldRange` — the square rule for `fold_range`
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

/-! ## The extracted range loop `fold_range` -/

/-- An accumulator-passing program `C → RustM C` as a program of the square: the value
    is `()` and the concrete state is the accumulator. -/
def unitAccK (p : C → Aeneas.Std.RustM C) : C → Aeneas.Std.RustM (Unit × C) :=
  fun c => p c >>= fun c' => .ok ((), c')

/-- `unitAccK p` returns `((), c')` exactly when `p` returns `c'`. -/
theorem unitAccK_eq_ok {p : C → Aeneas.Std.RustM C} {c c' : C} :
    unitAccK p c = .ok ((), c') ↔ p c = .ok c' := by
  unfold unitAccK
  cases p c <;> simp

/-- Trip `i` of `fold_range s e inv init body` as a body of the counted loop: `body` at
    the index `s + i`, encoded as `⟨BitVec.ofNat _ (s.val + i)⟩` as in `foldRangeAux`. -/
def foldRangeTrip {ty : UScalarTy} (s : UScalar ty) (body : C → UScalar ty → Aeneas.Std.RustM C)
    (i : Nat) : C → Aeneas.Std.RustM (Unit × C) :=
  unitAccK fun c => body c ⟨BitVec.ofNat _ (s.val + i)⟩

/-- hax-lean's `fold_range s e inv init body` as a program of the square, with value `()`
    and the accumulator as the concrete state. -/
def foldRangeK {ty : UScalarTy} (s e : UScalar ty)
    (inv : C → UScalar ty → Aeneas.Std.RustM Bool)
    (body : C → UScalar ty → Aeneas.Std.RustM C) : C → Aeneas.Std.RustM (Unit × C) :=
  unitAccK fun c => HaxBackend.Rust_primitives.Hax.Folds.fold_range s e inv c body

/-- The index of trip `i < e - s` of `fold_range s e` has the value `s + i`: the encoding
    `BitVec.ofNat` does not wrap, since `s + i < e < 2 ^ ty.numBits`. -/
theorem foldRange_index_val {ty : UScalarTy} {s e : UScalar ty} {i : Nat}
    (hi : i < e.val - s.val) :
    (⟨BitVec.ofNat _ (s.val + i)⟩ : UScalar ty).val = s.val + i := by
  have he := e.hBounds
  simp only [UScalar.val, BitVec.toNat_ofNat] at he hi ⊢
  exact Nat.mod_eq_of_lt (by omega)

/-- The counted loop from trip `i` with `k = N - i` trips left is `foldRangeAux` of `k`
    trips from the index `s + i`. -/
theorem loop_countedBody_foldRangeTrip {ty : UScalarTy} (s : UScalar ty)
    (body : C → UScalar ty → Aeneas.Std.RustM C) (N : Nat) :
    ∀ k i c, i + k = N →
      loop (countedBody N (foldRangeTrip s body)) (i, c) =
        unitAccK (fun c => HaxBackend.foldRangeAux body k (s.val + i) c) c := by
  intro k
  induction k with
  | zero =>
    intro i c hk
    rw [loop]
    have hlt : ¬ i < N := by omega
    simp [countedBody, hlt, unitAccK, HaxBackend.foldRangeAux]
  | succ k ih =>
    intro i c hk
    rw [loop]
    have hlt : i < N := by omega
    simp only [countedBody, hlt, if_true, foldRangeTrip, unitAccK, HaxBackend.foldRangeAux]
    cases hb : body c ⟨BitVec.ofNat _ (s.val + i)⟩ with
    | ok c₁ =>
      have := ih (i + 1) c₁ (by omega)
      simp only [unitAccK] at this
      simp only [bind_tc_ok, this, show s.val + (i + 1) = s.val + i + 1 by omega]
    | fail e => simp
    | div => simp

/-- **`fold_range` is the counted loop.** For `N = e - s`, the program `foldRangeK` of
    `fold_range s e inv · body` is the counted loop `loopK N` over the trips
    `foldRangeTrip s body`, trip `i` running `body` at the index `s + i`. -/
theorem foldRangeK_eq_loopK {ty : UScalarTy} (s e : UScalar ty)
    (inv : C → UScalar ty → Aeneas.Std.RustM Bool)
    (body : C → UScalar ty → Aeneas.Std.RustM C) :
    foldRangeK s e inv body = loopK (e.val - s.val) (foldRangeTrip s body) := by
  funext c
  rw [loopK, loop_countedBody_foldRangeTrip s body (e.val - s.val) (e.val - s.val) 0 c
    (Nat.zero_add _)]
  simp only [foldRangeK, HaxBackend.Rust_primitives.Hax.Folds.fold_range, Nat.add_zero]

/-- **The square rule for `fold_range`.** The counted-loop rule `corresM_loopK` at
    `N = e - s` through `foldRangeK_eq_loopK`: if at every trip `i < e - s` the body at
    the index `s + i` is in the square from `R` to `R` after the step `fa i` under the
    guard `Gb i`, and the loop guard implies each trip's guard at `ifold fa i σ`, then
    `fold_range s e inv · body` is in the square from `R` to `R` at
    `ifold fa (e - s) σ`. The accumulator is the concrete state and the value is `()`. -/
theorem corresM_foldRange {R : C → S → Prop} {Gb : Nat → S → Prop} {G : S → Prop}
    {fa : Nat → S → S} {ty : UScalarTy} {s e : UScalar ty}
    {inv : C → UScalar ty → Aeneas.Std.RustM Bool}
    {body : C → UScalar ty → Aeneas.Std.RustM C}
    (hbody : ∀ i, i < e.val - s.val →
      CorresM R (Gb i) (foldRangeTrip s body i) (fun _ => ()) (fun c σ => R c (fa i σ)))
    (hG : ∀ σ, G σ → ∀ i, i < e.val - s.val → Gb i (ifold fa i σ)) :
    CorresM R G (foldRangeK s e inv body) (fun _ => ())
      (fun c σ => R c (ifold fa (e.val - s.val) σ)) := by
  rw [foldRangeK_eq_loopK]
  exact corresM_loopK hbody hG

end Hax.Ascent.RustM
