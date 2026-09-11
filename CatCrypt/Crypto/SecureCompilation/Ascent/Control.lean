/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Corres

/-!
# The ascent refinement calculus over LowCT — control phase

Phase-4 control `Corres` lemmas dual to the straight-line leaves in `Corres.lean`,
resting on the **real** `semScalar` control arms (`RFor`, `RIfNz`) rather than on a
re-axiomatised loop/conditional semantics.

* **`corres_for`** — the bounded-loop rule for `RFor x N body`.  `semScalar`'s
  `RFor` arm is the structural `Nat`-recursion `semRForD` (peel the LAST trip,
  binding the counter `x := n` before each body run).  The abstract side is the
  `N`-fold iteration `nfold fa` of a loop-invariant abstract step `fa`; the body
  hypothesis is phrased on the **counter-bound body** `RSeq (RScalarSet x n) body`
  because that is definitionally the per-trip transition `semRForD` performs.
  Generic in the state relation `SR` / abstract state `AState`.

* **`corres_if`** — the genuine φ-merge conditional `RIfNz name thenBr elseBr`
  where both branches are a single `RScalarSet` on the SAME name (the only shape
  the front compiles as a real conditional — the (C′) cmov arm).  Over the word
  state relation `SRword`, the concrete guard's zero-test is exactly the abstract
  guard `a name = 0`, so the `phiSelect` cmov denotes the abstract branch select.

`corres_while` (`RWhileNz`) is deferred: `semScalar` has NO `RWhileNz` arm — it
falls to the catch-all `none`, so `Corres SR _ _ (.RWhileNz …)` cannot hold
non-vacuously.  The real do-while denotation is the separate transformer
`semScalarWhile` (`TranslateDialectWhileDenote`), whose fuel/trip bridge
`semScalarWhile_eq_iter` reduces it to the unconditional `semWhileIter`; a while
rule belongs against THAT transformer, not `Corres`-over-`semScalar`, and is left
to the while-denote layer.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA

variable {AState : Type} (SR : SEnvScalar → AState → Prop)

/-! ## The bounded-loop rule `corres_for` -/

/-- `N`-fold iteration of the abstract step, peeling the LAST application — the
    exact mirror of `semRForD`'s structural recursion. -/
def nfold {A : Type} (f : A → A) : Nat → A → A
  | 0, a => a
  | n + 1, a => f (nfold f n a)

/-- `nfold` preserves any `f`-invariant predicate. -/
theorem nfold_invariant {A : Type} {f : A → A} {P : A → Prop}
    (hinv : ∀ a, P a → P (f a)) : ∀ (n : Nat) (a : A), P a → P (nfold f n a) := by
  intro n
  induction n with
  | zero => intro a ha; exact ha
  | succ n ih => intro a ha; exact hinv _ (ih a ha)

/-- **The bounded for-loop rule.**  `semScalar (RFor x N body)` is the structural
    `Nat`-recursion `semRForD`, which per trip binds the counter `x := n` then runs
    the body — i.e. the transition `semScalar (RSeq (RScalarSet x n) body)`.  From a
    per-trip-index body `Corres` realizing the loop-invariant abstract step `fa`,
    and `fa` preserving the precondition `P`, the `N`-fold loop realizes `nfold fa N`.
    Generic in `SR` / `AState`. -/
theorem corres_for (x : String) (body : LowCT) {P : AState → Prop} {fa : AState → AState}
    (hbody : ∀ n : Nat, Corres SR P fa (.RSeq (.RScalarSet x n) body))
    (hinv : ∀ a, P a → P (fa a)) :
    ∀ N : Nat, Corres SR P (nfold fa N) (.RFor x N body) := by
  intro N
  induction N with
  | zero =>
      intro env a hSR hP
      exact ⟨env, rfl, hSR⟩
  | succ n ih =>
      intro env a hSR hP
      obtain ⟨envPre, hstepPre, hSRPre⟩ := ih env a hSR hP
      have hPpre : P (nfold fa n a) := nfold_invariant hinv n a hP
      obtain ⟨env', hstep', hSR'⟩ := hbody n envPre (nfold fa n a) hSRPre hPpre
      refine ⟨env', ?_, hSR'⟩
      -- `semScalar (RFor x (n+1) body) env = semRForD semBody x (n+1) env`
      -- peels the last trip: run trips `0..n-1` (= `hstepPre`), bind `x := n`, run body.
      have hstepPre' : semRForD (fun e => semScalar body e) x n env = some envPre := hstepPre
      have hstep'' : semScalar body (envPre.upd x (t := .sword 64) (BitVec.ofNat 64 n))
          = some env' := by
        have := hstep'
        simpa only [semScalar, Option.bind_some] using this
      show semRForD (fun e => semScalar body e) x (n + 1) env = some env'
      simp only [semRForD, hstepPre', hstep'']

/-! ## The φ-merge conditional rule `corres_if` -/

/-- A `BitVec 64` is zero iff its `wEnc`-encoding vanishes in `ZMod 2^64`
    (`wEnc` is injective on the word range). -/
theorem wEnc_eq_zero_iff (w : BitVec 64) : wEnc w = 0 ↔ w = 0#64 := by
  rw [wEnc, ZMod.natCast_eq_zero_iff]
  constructor
  · intro hdvd
    have h0 : w.toNat = 0 := Nat.eq_zero_of_dvd_of_lt hdvd w.isLt
    exact BitVec.eq_of_toNat_eq (by simpa using h0)
  · rintro rfl; simp

/-- **The φ-merge conditional rule.**  For `RIfNz name (RScalarSet nv thenVal)
    (RScalarSet nv elseVal)` — both branches a single scalar-set on the SAME name
    `nv`, the (C′) cmov shape `semScalar` compiles as a genuine conditional — the
    concrete `phiSelect` cmov (guard `condv = 0` ↦ else, else ↦ then) denotes the
    abstract branch select on the abstract zero-test `a name = 0`, over the word
    state relation `SRword`. -/
theorem corres_if (name nv : String) (thenVal elseVal : Nat) :
    Corres SRword (fun _ => True)
      (fun a s => if s = nv then
          (if a name = 0 then (elseVal : ZMod (2 ^ 64)) else (thenVal : ZMod (2 ^ 64)))
        else a s)
      (.RIfNz name (.RScalarSet nv thenVal) (.RScalarSet nv elseVal)) := by
  intro env a hSR _
  obtain ⟨cw, hcw, hcwEnc⟩ := hSR name
  -- The (C′) φ-merge result the `RIfNz` arm returns.
  refine ⟨env.upd nv (t := .sword 64)
      (phiSelect (w := 64) cw (BitVec.ofNat 64 thenVal) (BitVec.ofNat 64 elseVal)), ?_, ?_⟩
  · -- Match the real `semScalar` `RIfNz` arm.
    simp only [semScalar, hcw, asSingleScalarSet, if_true]
  · -- The state relation on the φ-merged env.
    intro s
    by_cases hs : s = nv
    · subst hs
      refine ⟨phiSelect (w := 64) cw (BitVec.ofNat 64 thenVal) (BitVec.ofNat 64 elseVal),
        by simp [SEnvScalar.upd], ?_⟩
      by_cases hz : cw = 0#64
      · have haz : a name = 0 := hcwEnc ▸ (wEnc_eq_zero_iff cw).mpr hz
        simp only [phiSelect, if_pos hz, if_pos haz, if_true, wEnc, BitVec.toNat_ofNat,
          ZMod.natCast_mod]
      · have haz : ¬ a name = 0 := fun h => hz ((wEnc_eq_zero_iff cw).mp (hcwEnc ▸ h))
        simp only [phiSelect, if_neg hz, if_neg haz, if_true, wEnc, BitVec.toNat_ofNat,
          ZMod.natCast_mod]
    · obtain ⟨w, hw, hwn⟩ := hSR s
      exact ⟨w, by simp [SEnvScalar.upd, hs, hw], by simp [hs, hwn]⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
