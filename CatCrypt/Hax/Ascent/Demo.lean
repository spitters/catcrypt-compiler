/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.Ascent.Corres
public import CatCrypt.Hax.Ascent.Square

/-!
# A worked correspondence: comparing two arrays

`keyEqLit` is a post-pipeline literal of the shape haxpipeT emits for a 32-entry array
comparison: the parameters are rebound, a `Bool` accumulator `eq` is bound to `true`,
a `forFold` over `[0, 32)` rebinds `eq` to `false` when the entries at the index differ,
and the result is the final `eq`. The accumulator is carried by the environment.
`demoBuiltins` interprets `Ne` on integers and `index` on arrays.

`keyEq` is the shallow function: `foldRangeSpec 0 32 true` of the step that clears the
accumulator on a mismatch. `keyEq_corres` proves the correspondence with the rules of
`CatCrypt/Hax/Ascent/Corres.lean` for arrays of at least 32 entries, `keyEq_fnCorres` states it
as a `FnCorres` from the entry environment binding `a` and `b`, and `keyEq_refinesO` reads
it as `RefinesO`.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent.Demo

/-- The builtin table of the example: `Ne` on integers, `index` on arrays. -/
def demoBuiltins : Builtins
  | "Ne", [.int x, .int y] => some (.bool (x != y))
  | "index", [.array vs, .int i] => if 0 ≤ i then vs[i.toNat]? else none
  | _, _ => none

/-- The loop body: clear `eq` when `a[i]` and `b[i]` differ. -/
def keyEqBody : ImpExpr :=
  .ifThenElse
    (.app "Ne" [.app "index" [.var "a", .var "i"], .app "index" [.var "b", .var "i"]])
    (.seq (.seq (.letBind "eq" (.lit (.bool false)) (.var "eq")) .unitVal) .unitVal)
    .unitVal

/-- The comparison of two 32-entry arrays, in the shape of a haxpipeT literal. -/
def keyEqLit : ImpExpr :=
  .letBind "a" (.var "a") (.letBind "b" (.var "b") (.letBind "eq" (.lit (.bool true))
    (.seq (.forFold "i" (.lit (.int 0)) (.lit (.int 32)) keyEqBody) (.var "eq"))))

/-- The step of the comparison at index `i`. -/
def keyEqStep (a b : Array Int) (i : Int) (eq : Bool) : Bool :=
  if a.getD i.toNat 0 != b.getD i.toNat 0 then false else eq

/-- The shallow comparison of the first 32 entries. -/
def keyEq (a b : Array Int) : Bool :=
  foldRangeSpec 0 32 true (keyEqStep a b)

/-- The abstract state: the two arrays. -/
abbrev KS := Array Int × Array Int

/-- The guard: both arrays have at least 32 entries. -/
def keyEqGuard (σ : KS) : Prop := 32 ≤ σ.1.size ∧ 32 ≤ σ.2.size

/-- The entry environment binding the two parameters. -/
def keyEqEntry (σ : KS) : Env := bindParams [("a", enc σ.1), ("b", enc σ.2)]

/-- The environment binds `a` and `b` to the two arrays. -/
def RA (env : Env) (σ : KS) : Prop := env "a" = some (enc σ.1) ∧ env "b" = some (enc σ.2)

/-- The loop invariant: the arrays are bound and `eq` holds the accumulator. -/
def KInv (env : Env) (σ : KS) (_i : Int) (acc : Bool) : Prop :=
  RA env σ ∧ env "eq" = some (.bool acc)

theorem RA_extend {env : Env} {σ : KS} (h : RA env σ) (x : String) (v : Value)
    (ha : x ≠ "a") (hb : x ≠ "b") : RA (env.extend x v) σ := by
  refine ⟨?_, ?_⟩
  · rw [Env.extend_other _ _ _ _ (Ne.symm ha)]; exact h.1
  · rw [Env.extend_other _ _ _ _ (Ne.symm hb)]; exact h.2

theorem index_enc (xs : Array Int) {i : Int} (h0 : 0 ≤ i) (hi : i.toNat < xs.size) :
    demoBuiltins "index" [enc xs, .int i] = some (.int (xs.getD i.toNat 0)) := by
  simp [demoBuiltins, h0, hi, Array.getD]

/-- The body entry relation of the loop. -/
def BodyP (env : Env) (t : KS × Int × Bool) : Prop :=
  KInv env t.1 t.2.1 t.2.2 ∧ env "i" = some (.int t.2.1)

/-- The body guard of the loop. -/
def BodyG (t : KS × Int × Bool) : Prop := keyEqGuard t.1 ∧ 0 ≤ t.2.1 ∧ t.2.1 < 32

/-- The body exit relation of the loop. -/
def BodyQ (env : Env) (t : KS × Int × Bool) : Prop :=
  KInv env t.1 (t.2.1 + 1) (keyEqStep t.1.1 t.1.2 t.2.1 t.2.2)

/-- The `index` call on the array bound to `arr` at the loop index. -/
theorem index_corres (arr : String) (get : KS → Array Int)
    (hget : ∀ env t, BodyP env t → env arr = some (enc (get t.1)))
    (hsize : ∀ t, BodyG t → 32 ≤ (get t.1).size) :
    Corres demoBuiltins BodyP BodyG (.app "index" [.var arr, .var "i"])
      (fun t => .int ((get t.1).getD t.2.1.toNat 0)) BodyP := by
  refine corres_app (Vs := fun t => [enc (get t.1), .int t.2.1]) ?_ ?_
  · refine corresArgs_cons (corres_var (fun env t hP _ => hget env t hP)) (fun _ _ => rfl) ?_
    refine corresArgs_cons (corres_var (fun env t hP _ => hP.2)) (fun _ _ => rfl) ?_
    exact corresArgs_nil _ _
  · intro t hG
    have := hsize t hG
    exact index_enc _ hG.2.1 (by have := hG.2.2; omega)

/-- The comparison `a[i] != b[i]`. -/
theorem cond_corres :
    Corres demoBuiltins BodyP BodyG
      (.app "Ne" [.app "index" [.var "a", .var "i"], .app "index" [.var "b", .var "i"]])
      (fun t => .bool (t.1.1.getD t.2.1.toNat 0 != t.1.2.getD t.2.1.toNat 0)) BodyP := by
  refine corres_app
    (Vs := fun t => [.int (t.1.1.getD t.2.1.toNat 0), .int (t.1.2.getD t.2.1.toNat 0)]) ?_
    (fun _ _ => rfl)
  refine corresArgs_cons (index_corres "a" Prod.fst (fun _ _ hP => hP.1.1.1)
    (fun _ hG => hG.1.1)) (fun _ _ => rfl) ?_
  refine corresArgs_cons (index_corres "b" Prod.snd (fun _ _ hP => hP.1.1.2)
    (fun _ hG => hG.1.2)) (fun _ _ => rfl) ?_
  exact corresArgs_nil _ _

/-- The loop body. -/
theorem body_corres :
    Corres demoBuiltins BodyP BodyG keyEqBody (fun _ => .unit) BodyQ := by
  refine corres_ifThenElse cond_corres ?_ ?_
  · -- the entries differ: `eq` becomes `false`
    have hlet : Corres demoBuiltins BodyP
        (fun t => BodyG t ∧ (t.1.1.getD t.2.1.toNat 0 != t.1.2.getD t.2.1.toNat 0) = true)
        (.letBind "eq" (.lit (.bool false)) (.var "eq")) (fun _ => .bool false)
        (fun env t => RA env t.1 ∧ env "eq" = some (.bool false)) :=
      corres_letBind (P₂ := fun env t => RA env t.1 ∧ env "eq" = some (.bool false))
        (corres_lit _ _ _) (fun _ _ => rfl)
        (fun env t hP _ => ⟨RA_extend hP.1.1 "eq" _ (by decide) (by decide),
          Env.extend_same _ _ _⟩)
        (corres_var (fun _ _ hP _ => hP.2))
    have hseq : Corres demoBuiltins BodyP
        (fun t => BodyG t ∧ (t.1.1.getD t.2.1.toNat 0 != t.1.2.getD t.2.1.toNat 0) = true)
        (.seq (.seq (.letBind "eq" (.lit (.bool false)) (.var "eq")) .unitVal) .unitVal)
        (fun _ => .unit) (fun env t => RA env t.1 ∧ env "eq" = some (.bool false)) := by
      weld
      · weld
        · exact hlet
        · exact fun _ _ => rfl
        · exact corres_unitVal _ _
      · exact fun _ _ => rfl
      · exact corres_unitVal _ _
    refine corres_conseq hseq (fun _ _ h _ => h) (fun _ h => h) (fun _ _ => rfl) ?_
    intro env t hG hQ
    refine ⟨hQ.1, ?_⟩
    simp only [keyEqStep, hG.2, if_true]
    exact hQ.2
  · -- the entries agree: `eq` is unchanged
    refine corres_conseq (corres_unitVal BodyP _) (fun _ _ h _ => h) (fun _ h => h)
      (fun _ _ => rfl) ?_
    intro env t hG hQ
    refine ⟨hQ.1.1, ?_⟩
    simp only [keyEqStep, hG.2, Bool.false_eq_true, if_false]
    exact hQ.1.2

/-- The entry environment binds the two arrays. -/
theorem keyEqEntry_RA (σ : KS) : RA (keyEqEntry σ) σ := by
  simp only [keyEqEntry, bindParams]
  refine ⟨Env.extend_same _ _ _, ?_⟩
  rw [Env.extend_other _ _ _ _ (by decide)]
  exact Env.extend_same _ _ _

/-- **The correspondence of the comparison.** From the entry environment, for arrays of
    at least 32 entries, the literal returns `enc (keyEq a b)`. -/
theorem keyEq_corres :
    Corres demoBuiltins (fun env σ => env = keyEqEntry σ) keyEqGuard keyEqLit
      (fun σ => enc (keyEq σ.1 σ.2)) (fun env σ => KInv env σ 32 (keyEq σ.1 σ.2)) := by
  have hloop := corres_forFold (bi := demoBuiltins) (P := fun env σ => KInv env σ 0 true)
    (Q₁ := fun env σ => KInv env σ 0 true) (Q₂ := fun env σ => KInv env σ 0 true)
    (G := keyEqGuard) (var := "i") (lo := .lit (.int 0)) (hi := .lit (.int 32))
    (body := keyEqBody) (loF := fun _ => 0) (hiF := fun _ => 32) (a₀ := fun _ => true)
    (g := fun σ => keyEqStep σ.1 σ.2) (Inv := KInv) (Vb := fun _ => .unit)
    (corres_lit _ _ (.int 0)) (corres_lit _ _ (.int 32)) (fun _ _ h _ => h)
    (fun _ _ => by decide) body_corres (fun _ _ _ _ _ h => Value.noConfusion h)
    (fun _ _ _ _ h => ⟨RA_extend h.1 "i" _ (by decide) (by decide),
      by rw [Env.extend_other _ _ _ _ (by decide)]; exact h.2⟩)
  have hbody3 : Corres demoBuiltins (fun env σ => KInv env σ 0 true) keyEqGuard
      (.seq (.forFold "i" (.lit (.int 0)) (.lit (.int 32)) keyEqBody) (.var "eq"))
      (fun σ => enc (keyEq σ.1 σ.2)) (fun env σ => KInv env σ 32 (keyEq σ.1 σ.2)) :=
    corres_seq hloop (fun _ _ => rfl) (corres_var (fun _ _ h _ => h.2))
  have hbody2 : Corres demoBuiltins RA keyEqGuard
      (.letBind "eq" (.lit (.bool true))
        (.seq (.forFold "i" (.lit (.int 0)) (.lit (.int 32)) keyEqBody) (.var "eq")))
      (fun σ => enc (keyEq σ.1 σ.2)) (fun env σ => KInv env σ 32 (keyEq σ.1 σ.2)) :=
    corres_letBind (corres_lit _ _ _) (fun _ _ => rfl)
      (fun _ _ h _ => ⟨RA_extend h "eq" _ (by decide) (by decide), Env.extend_same _ _ _⟩)
      hbody3
  have hbody1 := corres_letBind (x := "b") (corres_var (P := RA) (G := keyEqGuard)
      (V := fun σ => enc σ.2) (fun _ _ h _ => h.2)) (fun _ _ => rfl)
    (fun env σ h _ => ⟨by rw [Env.extend_other _ _ _ _ (by decide)]; exact h.1,
      Env.extend_same _ _ _⟩) hbody2
  have hbody0 := corres_letBind (x := "a") (corres_var (P := RA) (G := keyEqGuard)
      (V := fun σ => enc σ.1) (fun _ _ h _ => h.1)) (fun _ _ => rfl)
    (fun env σ h _ => ⟨Env.extend_same _ _ _,
      by rw [Env.extend_other _ _ _ _ (by decide)]; exact h.2⟩) hbody1
  exact corres_conseq hbody0 (fun env σ h _ => h ▸ keyEqEntry_RA σ) (fun _ h => h)
    (fun _ _ => rfl) (fun _ _ _ h => h)

/-- The comparison as a function correspondence. -/
theorem keyEq_fnCorres :
    FnCorres demoBuiltins keyEqLit keyEqEntry keyEqGuard (fun σ => keyEq σ.1 σ.2) :=
  fnCorres_of_corres keyEq_corres

instance : DecidablePred keyEqGuard := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The comparison as the `Option`-level refinement of the guarded shallow function by
    the eventual value of the literal. -/
theorem keyEq_refinesO :
    RefinesO (haxEval demoBuiltins keyEqLit) (fun env σ => env = keyEqEntry σ)
      (fun v b => v = enc b) (optGuard keyEqGuard (fun σ => keyEq σ.1 σ.2)) :=
  fnCorres_refinesO keyEq_fnCorres

end Hax.Ascent.Demo
