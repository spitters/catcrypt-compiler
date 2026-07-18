/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib
import CatCrypt.Crypto.SecureCompilation.VIR.FieldExpChain
import CatCrypt.Crypto.Jasmin.Ed25519.InvP25519Algo

/-!
# Algebraic semantics of `bernsteinInvChain`

`FieldExpChain.lean` defines `bernsteinInvChain : List Block` and proves its
*shape* (254 squarings + 11 multiplications).  This file adds an **algebraic
semantics** `applyChain : List Block → α → α` over any commutative monoid
`α`, and proves that running the Bernstein chain on a base `z` produces
`z^(p − 2)` — i.e. the chain computes Fermat inversion in `ZMod p_25519`.

## Strategy

To avoid an unrolling explosion from `List.foldl` over a 27-element list,
we abstract the chain into an **exponent trace**: track only the exponent
of the accumulator and stash (starting from exponent 1 for the base).

* `Block.expStep : Block → (Nat × List Nat) → (Nat × List Nat)`
  — the exponent counterpart of `Block.step`.
* `chainExponent blocks` — the final exponent that `bernsteinInvChain`
  computes; provable by `native_decide` to equal `p25519 - 2`.

We then show by induction on the chain that
`applyChain blocks z = z^(chainExponent blocks)`, so the abstract
algebraic theorem reduces to a `native_decide` on a 12-step Nat
recursion.

## Status

* Algebraic theorem `bernsteinInvChain_eq_pow_p_minus_2` — proved.
* Fermat corollary `bernsteinInvChain_eq_inv` — proved.

This is the load-bearing piece for `CompressEmitCorrect.lean`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FieldExpChain

open CatCrypt.Crypto.Jasmin.Ed25519.InvP25519Algo

/-! ## §1  Algebraic chain state

The Bernstein chain is most cleanly modelled as a `(accumulator, stash)`
pair, where each `Block` advances the state. -/

variable {α : Type*}

/-- Safe indexed access into a `List α`, defaulting to a caller-supplied
    value on out-of-range index.  We use this so `Block.step` is total. -/
def listIdx (xs : List α) (i : Nat) (default : α) : α :=
  (xs[i]?).getD default

/-- Apply one block to a chain state `(acc, stash)`.  For `mulStash`,
    out-of-range indices multiply by `1` (the monoid identity) — but
    the chain never references out-of-range indices, so this default
    is purely defensive. -/
def Block.step [CommMonoid α] : Block → α × List α → α × List α
  | .run n,       (acc, st) => (acc^(2^n), st)
  | .mulStash i,  (acc, st) => (acc * listIdx st i 1, st)
  | .stash,       (acc, st) => (acc, st ++ [acc])

/-- Apply a chain `blocks` to a base `z`.  The initial stash is `[z]` so
    that `stash[0] = z`. -/
def applyChain [CommMonoid α] (blocks : List Block) (z : α) : α :=
  (blocks.foldl (fun s b => Block.step b s) (z, [z])).1

/-! ## §2  Exponent abstraction

If the base `z` has "exponent 1" (a formal marker), then after applying
the chain, the accumulator has some exponent `e ∈ ℕ`, and each stash
slot has some exponent.  Tracking only the exponents reduces the chain
computation to plain Nat arithmetic. -/

/-- Exponent counterpart of `Block.step`: same logic, but on `Nat`
    exponents.  `mulStash i` becomes addition of exponents; `run n`
    becomes multiplication by `2^n`.  Out-of-range index defaults to
    `0` (additive identity), matching the `1` default on the algebraic
    side. -/
def Block.expStep : Block → Nat × List Nat → Nat × List Nat
  | .run n,       (e, st) => (e * 2^n, st)
  | .mulStash i,  (e, st) => (e + listIdx st i 0, st)
  | .stash,       (e, st) => (e, st ++ [e])

/-- Final exponent of the accumulator after running `blocks` from the
    base. -/
def chainExponent (blocks : List Block) : Nat :=
  (blocks.foldl (fun s b => Block.expStep b s) (1, [1])).1

/-! ## §3  `applyChain` factors through the exponent abstraction

Generalising over the *invariant* that every accumulator and stash entry
is `z^e_*` for some `e_*` tracked by `expStep`, we can show that the
algebraic chain output equals `z^(chainExponent blocks)`. -/

/-- Compatibility relation between algebraic state `(acc, st)` and
    exponent state `(e, est)` over a fixed base `z`: every element is
    `z` raised to the corresponding exponent.  The stash invariant is
    stated **only at in-bounds indices** (using a fixed default of `1`
    on both sides), so it survives any change to the accumulator. -/
private def compat [CommMonoid α] (z : α) : (α × List α) → (Nat × List Nat) → Prop
  | (acc, st), (e, est) =>
    acc = z^e ∧ st.length = est.length ∧
    ∀ i, i < st.length →
      listIdx st i 1 = z^(listIdx est i 0)

/-- Helper: `listIdx` on a singleton-appended list at a smaller index
    is just `listIdx` on the original list. -/
private lemma listIdx_append_lt {α : Type*} (xs : List α) (x default : α)
    {i : Nat} (h : i < xs.length) :
    listIdx (xs ++ [x]) i default = listIdx xs i default := by
  simp only [listIdx, List.getElem?_append_left h]

/-- Helper: `listIdx` on a singleton-appended list at the new slot
    returns the appended element. -/
private lemma listIdx_append_eq {α : Type*} (xs : List α) (x default : α) :
    listIdx (xs ++ [x]) xs.length default = x := by
  simp [listIdx]

/-- Helper: `listIdx` out of range returns the default. -/
private lemma listIdx_oob {α : Type*} (xs : List α) (default : α) {i : Nat}
    (h : xs.length ≤ i) :
    listIdx xs i default = default := by
  simp only [listIdx]
  rw [List.getElem?_eq_none h]
  rfl

/-- One step preserves the compat relation. -/
private lemma compat_step [CommMonoid α] (z : α) (b : Block)
    (s : α × List α) (es : Nat × List Nat) (h : compat z s es) :
    compat z (Block.step b s) (Block.expStep b es) := by
  rcases s with ⟨acc, st⟩
  rcases es with ⟨e, est⟩
  obtain ⟨h_acc, h_len, h_idx⟩ := h
  cases b with
  | run n =>
    refine ⟨?_, h_len, ?_⟩
    · subst h_acc; rw [← pow_mul]
    · intro i hi
      exact h_idx i hi
  | mulStash i =>
    refine ⟨?_, h_len, ?_⟩
    · subst h_acc
      by_cases hi : i < st.length
      · have h_idx_i := h_idx i hi
        rw [h_idx_i, ← pow_add]
      · push_neg at hi
        have hi' : est.length ≤ i := by rw [← h_len]; exact hi
        rw [listIdx_oob st (1 : α) hi, listIdx_oob est 0 hi']
        simp
    · intro j hj
      exact h_idx j hj
  | stash =>
    refine ⟨h_acc, by simp [h_len], ?_⟩
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases h_lt : i < st.length
    · -- old slot: index unchanged
      rw [listIdx_append_lt st acc 1 h_lt]
      have h_lt' : i < est.length := by rw [← h_len]; exact h_lt
      rw [listIdx_append_lt est e 0 h_lt']
      exact h_idx i h_lt
    · -- new slot: i = st.length, returns acc / e
      push_neg at h_lt
      have h_eq : i = st.length := by omega
      rw [h_eq, listIdx_append_eq st acc 1]
      -- est.length = st.length, so listIdx (est ++ [e]) st.length 0 = e
      rw [show st.length = est.length from h_len, listIdx_append_eq est e 0]
      exact h_acc

/-- `foldl` preserves compatibility for the whole chain. -/
private lemma compat_foldl [CommMonoid α] (z : α) :
    ∀ (blocks : List Block) (s : α × List α) (es : Nat × List Nat),
    compat z s es →
    compat z (blocks.foldl (fun s b => Block.step b s) s)
            (blocks.foldl (fun s b => Block.expStep b s) es) := by
  intro blocks
  induction blocks with
  | nil => intro s es h; exact h
  | cons b rest ih =>
    intro s es h
    simp only [List.foldl_cons]
    exact ih _ _ (compat_step z b s es h)

/-- **Bridge theorem**: applying the chain algebraically equals raising
    the base to the chain's tracked exponent. -/
theorem applyChain_eq_pow [CommMonoid α] (z : α) (blocks : List Block) :
    applyChain blocks z = z^(chainExponent blocks) := by
  have h_init : compat z (z, [z]) (1, [1]) := by
    refine ⟨by simp, by simp, ?_⟩
    intro i hi
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    subst hi
    -- listIdx [z] 0 1 = z, listIdx [1] 0 0 = 1, z^1 = z
    simp [listIdx]
  have h := compat_foldl z blocks _ _ h_init
  exact h.1

/-! ## §4  The Bernstein chain's final exponent is `p25519 − 2` -/

/-- Computational check: `chainExponent bernsteinInvChain = p25519 - 2`.
    Closed by `native_decide` — the exponent computation is decidable
    over `Nat` but the literals `2^255` make it expensive at compile
    time.  Use `native_decide` to fall through to the compiled kernel. -/
theorem chainExponent_bernsteinInvChain_eq :
    chainExponent bernsteinInvChain = p25519 - 2 := by
  native_decide

/-- **Main algebraic theorem.**  Applying the Bernstein chain to a base
    `z : ZMod p25519` yields `z^(p25519 − 2)`. -/
theorem bernsteinInvChain_eq_pow_p_minus_2 (z : ZMod p25519) :
    applyChain bernsteinInvChain z = z^(p25519 - 2) := by
  rw [applyChain_eq_pow z bernsteinInvChain, chainExponent_bernsteinInvChain_eq]

/-! ## §5  Fermat bridge: `applyChain bernsteinInvChain z = z⁻¹` -/

/-- **Fermat-inversion corollary.**  Over `ZMod p25519` with primality
    available, applying the Bernstein chain to a nonzero base `z` gives
    `z⁻¹`. -/
theorem bernsteinInvChain_eq_inv [Fact (Nat.Prime p25519)]
    (z : ZMod p25519) (hz : z ≠ 0) :
    applyChain bernsteinInvChain z = z⁻¹ := by
  rw [bernsteinInvChain_eq_pow_p_minus_2]
  exact zmod_pow_p_sub_two_eq_inv z hz

/-! ## §6  Smoke tests

The `chainExponent` decides at `p25519 - 2`; for a concrete `Nat` base
we can also `native_decide` that `applyChain bernsteinInvChain 2 = 2 ^
(p25519 - 2)` as a `Nat`-level equality (since `Nat` is a
`CommMonoid`).  We do **not** force this at build time because the
right-hand side `2^(2^255 - 21)` is astronomical; we instead test the
chainExponent count and a small Nat-level smoke test. -/

/-- Smoke test: chainExponent computes via `native_decide` to a Nat
    whose value is `2^255 - 21`. -/
example : chainExponent bernsteinInvChain = 2^255 - 21 := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.FieldExpChain
