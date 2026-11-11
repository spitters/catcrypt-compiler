/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeANorm2

/-!
# `aNormalizeTotal` refines the reading at the level of call trees

At every tree table and fuel, under the source condition `aNormTDenoteOk e`, the call tree of
`e` from an environment is related by `RuttS` at equal events and answers to the call tree of
`aNormalizeTotal e` from the same environment: a leaf of `e` whose outcome is an error is a
failed leaf, and every other leaf of `e` is matched by a leaf with the same outcome. The
normaliser binds the arguments of a call before the call and reads a variable argument after
the arguments to its right; the source condition keeps that variable unchanged by them, and a
source leaf that reads an unbound variable is an error, so the target performs no event before
a source leaf that is not an error.

## Main definitions

* `ANormDSimT` — the simulation of an expression by its hoisted form.
* `RuttO` — trees of outcomes related at equal events and answers with error leaves failed.

## Main results

* `aNormTArgs_relT` — the hoisted bindings of the arguments of a call followed by the call
  are related to the reading of the arguments followed by the call.
* `loopNorm_relT` — the hoisting pass on a counted loop refines the loop.
* `aNormTBody_relT` — the hoisting pass refines the reading.
* `bindTails_relT` — tail binding keeps the outcome of every leaf.
* `aNormalizeTotal_relT` — under `aNormTDenoteOk e`, the call trees of `e` and of
  `aNormalizeTotal e` are related; `match_` is excluded by the condition.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeANorm

open _root_.Hax
open _root_.Hax.InlineLocalClosures (IsErr frameOk)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeRepeatCount (tm_bind_run tm_pure_run
  denoteT_var_run denoteT_var_run_none)
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree (Rutt)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open CatCrypt.Crypto.Hax (prependBindings splitLetBinds bindRhs floatLet hoistAt anormName
  prependBindings_append prependBindings_cons prependBindings_nil splitLetBinds_letBind ARel
  AnormBelow anormName_below anormName_inj isVar isVar_eq_true aNormTBody aNormTArgs
  aNormTArgs_le_of aNormTBody_le argsOrderOk varKept ANormDOk ANormDOkList_mem loopNorm
  hoistsLo hoistsBound ite_bound_sim aNormTBody_forLoop_loopNorm aNormTBody_forLoopRev_loopNorm
  aNormTBody_forFold_loopNorm aNormTBody_forFoldRev_loopNorm bindTails isTailBindable retName
  aNormalizeTotal aNormalizeTotalCount aNormTDenoteOk)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick (bind_assoc bind_ret
  denoteT_seq_run denoteT_ifThenElse_run denoteT_letBind_run')

variable {E : EventSig}

/-! ## Readings in sequenced form -/

section Forms

variable (bt : TreeTable E) (fuel : Nat)

/-- The reading of the empty argument list. -/
theorem denoteArgsT_nil_run (env : Env) : denoteArgsT bt fuel [] env = .ret (some [], env) := by
  rw [denoteArgsT]; rfl

/-- The reading of a non-empty argument list: the first argument, then the rest when the first
    is a plain value. -/
theorem denoteArgsT_cons_run (a : ImpExpr) (as : List ImpExpr) (env : Env) :
    denoteArgsT bt fuel (a :: as) env = (denoteT bt fuel a env).bind fun p =>
      match p with
      | (.val v, e1) => if v.isControlFlow then .ret (none, e1)
          else (denoteArgsT bt fuel as e1).bind fun q => .ret (q.1.map (v :: ·), q.2)
      | (_, e1) => .ret (none, e1) := by
  rw [denoteArgsT, tm_bind_run]
  congr 1
  funext p
  rcases p with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _
  · cases v <;> rfl
  all_goals rfl

/-- The reading of a binding, with the control-flow test of the bound value. -/
theorem denoteT_letBind_runIf (n : String) (v b : ImpExpr) (env : Env) :
    denoteT bt fuel (.letBind n v b) env = (denoteT bt fuel v env).bind fun p =>
      match p with
      | (.val w, e1) => if w.isControlFlow then .ret (.val w, e1)
          else denoteT bt fuel b (e1.extend n w)
      | (o, e1) => .ret (o, e1) := by
  rw [denoteT_letBind_run']
  congr 1
  funext p
  rcases p with ⟨o, e1⟩
  rcases o with w | _ | _ | _ | _
  · cases w <;> rfl
  all_goals rfl

/-- The loop tail at a plain value of the lower bound. -/
theorem anfLoopTailT_val (hi : ImpExpr) (T : Value → Outcome → TM E Outcome) (w : Value)
    (hw : w.isControlFlow = false) :
    anfLoopTailT bt fuel hi T (.val w) = denoteT bt fuel hi >>= T w := by
  simp only [anfLoopTailT, hw, Bool.false_eq_true, ite_false]

/-- The continuation of a call after its arguments. -/
def appKT (f : String) (mvals : Option (List Value)) : TM E Outcome :=
  match mvals with
  | some vals => do
    let r ← StateT.lift (bt f vals)
    match r with
    | some v => pure (.val v)
    | none => pure (.err s!"unknown function or bad args: {f}")
  | none => pure (.err "non-value in function arguments")

/-- The reading of a call: the arguments, then `appKT`. -/
theorem denoteT_app_run (f : String) (args : List ImpExpr) (env : Env) :
    denoteT bt fuel (.app f args) env =
      (denoteArgsT bt fuel args env).bind fun p => appKT bt f p.1 p.2 := by
  rw [denoteT, denoteAppT, tm_bind_run]
  rfl

/-- The continuation of a tuple after its elements. -/
def tupleKT (mvals : Option (List Value)) : TM E Outcome :=
  match mvals with
  | some vals => pure (.val (.tuple vals))
  | none => pure (.err "non-value in tuple elements")

/-- The reading of a tuple: the elements, then `tupleKT`. -/
theorem denoteT_tuple_run (es : List ImpExpr) (env : Env) :
    denoteT bt fuel (.tuple es) env =
      (denoteArgsT bt fuel es env).bind fun p => tupleKT p.1 p.2 := by
  rw [denoteT, tm_bind_run]
  rfl

end Forms

/-- A property of every leaf holds of the leaves of every tree. -/
theorem leafP_of_forall {R : Type} {P : R → Prop} (h : ∀ r, P r) (t : CallTree E R) :
    LeafP P t := by
  induction t with
  | ret r => exact .ret (h r)
  | vis e c ih => exact .vis ih

/-- Equal prefixes followed by related continuations are related. -/
theorem rutt_bind_same {S R₁ R₂ : Type} {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop}
    (t : CallTree E S) {k₁ : S → CallTree E R₁} {k₂ : S → CallTree E R₂}
    (hk : ∀ s, Rutt (fun e₁ e₂ : E.Event => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) RR Fail
      (k₁ s) (k₂ s)) :
    Rutt (fun e₁ e₂ : E.Event => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) RR Fail
      (t.bind k₁) (t.bind k₂) :=
  rutt_bind (RR' := fun s₁ s₂ => s₁ = s₂) (Fail' := fun _ => False)
    (rutt_refl (fun _ => rfl) t) (fun s₁ _ hs => hs ▸ hk s₁) (fun _ hf => hf.elim)

/-- Trees of outcomes related at equal events and answers, an error being a failed source
    leaf. -/
abbrev RuttO (RR : Outcome × Env → Outcome × Env → Prop)
    (t₁ t₂ : CallTree E (Outcome × Env)) : Prop :=
  Rutt (fun e₁ e₂ : E.Event => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) RR (fun r => IsErr r.1) t₁ t₂

/-! ## The simulation -/

/-- The simulation of `e` by its hoisted form at the level of call trees: for every counter
    `k` whose normal form mints fresh names below `K`, the normal form refines `e` under
    `ARel K k g`, for every `g` and fuel. -/
def ANormDSimT (bt : TreeTable E) (K : Nat) (e : ImpExpr) : Prop :=
  ∀ k, (aNormTBody e k).2 ≤ K → ∀ (g : Env) (fuel : Nat),
    RefET (ARel K k g) (denoteT bt fuel (aNormTBody e k).1) (denoteT bt fuel e)

section Sim

variable (bt : TreeTable E) {ok : String → Bool} {K : Nat}
  (hok : ∀ n, ok n = true → ¬ AnormBelow K n)

/-- A simulation from a counter `k'` at every counter `k ≤ k'`. -/
theorem ANormDSimT.at {e : ImpExpr} (h : ANormDSimT bt K e) {k k' : Nat} (hk : k ≤ k')
    (hK : (aNormTBody e k').2 ≤ K) (g : Env) (fuel : Nat) :
    RefET (ARel K k g) (denoteT bt fuel (aNormTBody e k').1) (denoteT bt fuel e) :=
  refET_widen hk (fun g => h k' hK g fuel) g

include hok in
/-- An expression in `frameOk ok ok` refines itself under `ARel`. -/
theorem refET_frameOk {k : Nat} (hkK : k ≤ K) (e : ImpExpr)
    (h : frameOk ok ok (fun _ => true) e = true) (g : Env) (fuel : Nat) :
    RefET (ARel K k g) (denoteT bt fuel e) (denoteT bt fuel e) :=
  denoteT_frame bt ok ok (fun _ => true) (fun _ _ x hR hx => hR.read (hok x hx))
    (fun _ _ n w hR hn => hR.extend hkK (hok n hn) w) e h fuel

include hok in
/-- **The hoisted arguments.** The reading of the arguments followed by a continuation `Ks` is
    related to the reading of the hoisted bindings followed by `B`, when `Ks` fails at `none`
    and is related to `B` at every list of values that the argument list of the normal form
    reads to in the target environment. The predicate `Q` of the source environment, kept by
    every argument, holds at the environments where the continuations are related. -/
theorem aNormTArgs_relT (args : List ImpExpr) (ih : ∀ a ∈ args, ANormDSimT bt K a)
    (hOrd : argsOrderOk args = true) (hA : ∀ a ∈ args, ANormDOk ok a = true) :
    ∀ k, (aNormTArgs args k).2.2 ≤ K → ∀ (g : Env) (fuel : Nat) (Q : Env → Prop),
      (∀ a ∈ args, ∀ s, Q s →
        LeafP (fun r : Outcome × Env => ¬ IsErr r.1 → Q r.2) (denoteT bt fuel a s)) →
      ∀ (B : ImpExpr) (Ks : Option (List Value) × Env → CallTree E (Outcome × Env))
        (RR : Outcome × Env → Outcome × Env → Prop) (e₁ e₂ : Env),
      ARel K k g e₁ e₂ → Q e₂ →
      (∀ s₂ t, RuttO RR (Ks (none, s₂)) t) →
      (∀ vals s₁ s₂, ARel K k g s₁ s₂ → Q s₂ →
        denoteArgsT bt fuel (aNormTArgs args k).2.1 s₁ = .ret (some vals, s₁) →
        RuttO RR (Ks (some vals, s₂)) (denoteT bt fuel B s₁)) →
      RuttO RR ((denoteArgsT bt fuel args e₂).bind Ks)
        (denoteT bt fuel (prependBindings (aNormTArgs args k).1 B) e₁) := by
  induction args with
  | nil =>
    intro k _ g fuel Q _ B Ks RR e₁ e₂ hR hQ _ hsome
    rw [denoteArgsT_nil_run]
    exact hsome [] e₁ e₂ hR hQ (denoteArgsT_nil_run bt fuel e₁)
  | cons a rest ihr =>
    intro k hK g fuel Q hQ B Ks RR e₁ e₂ hR hQe hnone hsome
    simp only [argsOrderOk, Bool.and_eq_true] at hOrd
    have ihr' := ihr (fun b hb => ih b (List.mem_cons_of_mem _ hb)) hOrd.2
      (fun b hb => hA b (List.mem_cons_of_mem _ hb))
    rw [denoteArgsT_cons_run, bind_assoc]
    by_cases hv : isVar a = true
    · obtain ⟨x, rfl⟩ := isVar_eq_true hv
      simp only [aNormTArgs, hv, ite_true, List.nil_append] at hK ⊢
      have hxok : ¬ AnormBelow K x := hok x (by simpa [ANormDOk] using hA _ List.mem_cons_self)
      cases hex : e₂ x with
      | none =>
        rw [denoteT_var_run_none bt fuel x e₂ hex]
        exact hnone e₂ _
      | some w =>
        rw [denoteT_var_run bt fuel x e₂ w hex]
        cases hwc : w.isControlFlow
        · simp only [CallTree.bind, hwc, Bool.false_eq_true, ite_false]
          rw [bind_assoc]
          refine ihr' k hK g fuel (fun s => Q s ∧ s x = some w) ?_ B _ RR e₁ e₂ hR ⟨hQe, hex⟩
            (fun s₂ t => hnone s₂ t) ?_
          · intro b hb s hs
            have hkeep : frameOk (fun _ => true) (fun n => n != x) (fun _ => true) b = true := by
              have := List.all_eq_true.mp hOrd.1 b hb
              simpa [varKept] using this
            refine LeafP.mono ?_ ((hQ b (List.mem_cons_of_mem _ hb) s hs.1).and
              (denoteT_keeps bt b hkeep fuel s))
            rintro r ⟨h1, h2⟩ hne
            exact ⟨h1 hne, (h2 hne).trans hs.2⟩
          · intro rv s₁ s₂ hR' hQ' hD
            refine hsome (w :: rv) s₁ s₂ hR' hQ'.1 ?_
            simp only [aNormTArgs, hv, ite_true]
            rw [denoteArgsT_cons_run, denoteT_var_run bt fuel x s₁ w
              ((hR'.read hxok).trans hQ'.2)]
            simp only [CallTree.bind, hwc, Bool.false_eq_true, ite_false]
            rw [hD]
            rfl
        · simp only [CallTree.bind, hwc, ite_true]
          exact hnone e₂ _
    · have hvf : isVar a = false := by simpa using hv
      rcases hr1 : aNormTBody a k with ⟨r1, r2⟩
      simp only [aNormTArgs, hvf, hr1, Bool.false_eq_true, ite_false] at hK ⊢
      have hr2K : r2 + 1 ≤ K :=
        Nat.le_trans (aNormTArgs_le_of rest (fun b _ => aNormTBody_le b) (r2 + 1)) hK
      have hkr : k ≤ r2 := by have := aNormTBody_le a k; rw [hr1] at this; exact this
      have iha := ih a List.mem_cons_self k (by rw [hr1]; omega) g fuel
      rw [hr1] at iha
      rw [prependBindings_append, hoistBind_runT, denoteT_letBind_runIf]
      refine rutt_bind (rutt_withLeaf (iha e₁ e₂ hR) (hQ a List.mem_cons_self e₂ hQe))
        (fun r₁ r₂ hr => ?_) (fun r₁ hf t => ?_)
      · obtain ⟨⟨h1, hRm⟩, hQm⟩ := hr
        rcases r₁ with ⟨o, m₂⟩
        rcases r₂ with ⟨o', m₁⟩
        dsimp only at h1 hRm hQm ⊢
        subst h1
        rcases o' with w | _ | _ | _ | _
        · cases hwc : w.isControlFlow
          · simp only [hwc, Bool.false_eq_true, ite_false]
            rw [bind_assoc]
            have hR0 : ARel K (r2 + 1) (m₁.extend (anormName r2) w)
                (m₁.extend (anormName r2) w) m₂ :=
              ⟨hRm.1.extend_right (anormName_below (by omega)) w, fun _ _ => rfl⟩
            refine ihr' (r2 + 1) hK _ fuel Q (fun b hb => hQ b (List.mem_cons_of_mem _ hb)) B _
              RR _ m₂ hR0 (hQm (fun ⟨_, h'⟩ => by cases h')) (fun s₂ t => hnone s₂ t) ?_
            intro rv s₁ s₂ hR' hQ' hD
            have hs₁ : s₁ (anormName r2) = some w := by
              rw [hR'.2 r2 (Nat.lt_succ_self _), Env.extend_same]
            refine hsome (w :: rv) s₁ s₂ ⟨hR'.1, fun j hj => ?_⟩ hQ' ?_
            · have hne : anormName j ≠ anormName r2 := fun h' => by
                have := anormName_inj h'; omega
              rw [hR'.2 j (by omega), Env.extend_other _ _ _ _ hne]
              exact hRm.2 j hj
            · simp only [aNormTArgs, hvf, hr1, Bool.false_eq_true, ite_false,
                CatCrypt.Crypto.Hax.hoistAt]
              rw [denoteArgsT_cons_run, denoteT_var_run bt fuel _ s₁ w hs₁]
              simp only [CallTree.bind, hwc, Bool.false_eq_true, ite_false]
              rw [hD]
              rfl
          · simp only [hwc, ite_true, CallTree.bind]
            exact hnone m₂ _
        all_goals exact hnone m₂ _
      · rcases r₁ with ⟨o, s⟩
        obtain ⟨m, hm⟩ := hf
        dsimp only at hm
        subst hm
        exact hnone s t

include hok in
/-- **The hoisting pass on a counted loop refines the loop.** For a loop constructor `mk`
    that reads its lower bound, then `anfLoopTailT` with the tail `T`, a counter in `ok`, a
    lower bound simulated by its hoisted form when `hoistsLo` holds and in `frameOk ok ok`
    otherwise, the same for the upper bound under `hoistsBound`, and a simulated body, the form
    `loopNorm` refines the loop. -/
theorem loopNorm_relT (mk : String → ImpExpr → ImpExpr → ImpExpr → ImpExpr)
    (T : Nat → String → ImpExpr → Value → Outcome → TM E Outcome)
    (hrun : ∀ fuel v lo hi b, denoteT bt fuel (mk v lo hi b) =
      denoteT bt fuel lo >>= anfLoopTailT bt fuel hi (T fuel v b))
    (hcf : ∀ fuel v b vlo w m, w.isControlFlow = true →
      T fuel v b vlo (.val w) m = .ret (.val w, m) ∨
        ∃ r, T fuel v b vlo (.val w) m = .ret r ∧ IsErr r.1)
    (hoth : ∀ fuel v b vlo o m, (∀ w, o ≠ .val w) → T fuel v b vlo o m = .ret (o, m))
    (hrel : ∀ {R : Env → Env → Prop} (v : String) (b₁ b₂ : ImpExpr),
      (∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v w) (e₂.extend v w)) →
      (∀ fuel, RefET R (denoteT bt fuel b₁) (denoteT bt fuel b₂)) →
      ∀ fuel vlo rhi, RefET R (T fuel v b₁ vlo rhi) (T fuel v b₂ vlo rhi))
    (v : String) (lo hi b : ImpExpr) (hv : ok v = true)
    (hl : if hoistsLo lo hi = true then ANormDSimT bt K lo
      else frameOk ok ok (fun _ => true) lo = true)
    (hh : if hoistsBound hi = true then ANormDSimT bt K hi
      else frameOk ok ok (fun _ => true) hi = true)
    (hb : ANormDSimT bt K b) :
    ∀ k, (loopNorm mk v lo hi b k).2 ≤ K → ∀ (g : Env) (fuel : Nat),
      RefET (ARel K k g) (denoteT bt fuel (loopNorm mk v lo hi b k).1)
        (denoteT bt fuel (mk v lo hi b)) := by
  intro k hK g fuel
  have hvx : ∀ {k' : Nat} {g' : Env}, k' ≤ K → ∀ e₁ e₂ w, ARel K k' g' e₁ e₂ →
      ARel K k' g' (e₁.extend v w) (e₂.extend v w) :=
    fun hkK e₁ e₂ w h => h.extend hkK (hok v hv) w
  have hbody : ∀ {k' k'' : Nat} (g' : Env), k' ≤ k'' → (aNormTBody b k'').2 ≤ K →
      ∀ fuel, RefET (ARel K k' g') (denoteT bt fuel (aNormTBody b k'').1) (denoteT bt fuel b) :=
    fun g' hk hK' fuel => ANormDSimT.at bt hb hk hK' g' fuel
  have hcfL : ∀ w m, w.isControlFlow = true →
      anfLoopTailT bt fuel hi (T fuel v b) (.val w) m = .ret (.val w, m) ∨
        ∃ r, anfLoopTailT bt fuel hi (T fuel v b) (.val w) m = .ret r ∧ IsErr r.1 :=
    fun w m hw => by simp only [anfLoopTailT, hw, ite_true]; exact Or.inl rfl
  have hothL : ∀ o m, (∀ w, o ≠ .val w) →
      anfLoopTailT bt fuel hi (T fuel v b) o m = .ret (o, m) :=
    fun o m ho => by
      cases o with
      | val w => exact absurd rfl (ho w)
      | _ => rfl
  by_cases hlo : hoistsLo lo hi = true
  · rw [ite_eq_left hlo] at hl
    rcases hr1 : aNormTBody lo k with ⟨r1, r2⟩
    have hkr : k ≤ r2 := by have := aNormTBody_le lo k; rw [hr1] at this; exact this
    refine RefT.congr_src ?_ (fun env => congrFun (hrun fuel v lo hi b) env)
    by_cases hhb : hoistsBound hi = true
    · rw [ite_eq_left hhb] at hh
      rcases hq : aNormTBody hi (r2 + 1) with ⟨q1, q2⟩
      have hrq : r2 + 1 ≤ q2 := by
        have := aNormTBody_le hi (r2 + 1); rw [hq] at this; exact this
      simp only [loopNorm, hlo, hhb, hr1, hq, ite_true] at hK ⊢
      have hqb := aNormTBody_le b (q2 + 1)
      have hlr := hl k (by rw [hr1]; omega) g fuel
      rw [hr1] at hlr
      refine RefT.congr_tgt ?_ (fun env => (congrArg (fun x => denoteT bt fuel x env)
        (prependBindings_append _ _ _)).trans (hoistBind_runT bt fuel r1 _ r2 env))
      refine letBind_hoist_contT (Rw := fun w e₁ e₂ => ARel K k g e₁ e₂ ∧
          e₁ (anormName r2) = some w)
        (fun e₁ e₂ w h => ⟨h.extend_tmp hkr (by omega) w, Env.extend_same _ _ _⟩) hlr ?_
        hcfL hothL
      intro w hw e₁ e₂ ⟨hR, hs⟩
      rw [anfLoopTailT_val bt fuel hi _ w hw, hoistBind_runT]
      have hhq := hh (r2 + 1) (by rw [hq]; omega) e₁ fuel
      rw [hq] at hhq
      have key := letBind_hoist_contT (R := ARel K (r2 + 1) e₁) (tmp := anormName q2)
        (C := mk v (hoistAt r1 r2).2 (hoistAt q1 q2).2 (aNormTBody b (q2 + 1)).1)
        (Rw := fun w2 e e' => ARel K (r2 + 1) e₁ e e' ∧ e (anormName q2) = some w2)
        (fun e e' w2 h => ⟨h.extend_tmp hrq (by omega) w2, Env.extend_same _ _ _⟩) hhq
        (fun w2 hw2 e e' hP => by
          obtain ⟨hR', ht⟩ := hP
          have hse : e (anormName r2) = some w := by
            rw [hR'.2 r2 (Nat.lt_succ_self _)]; exact hs
          have heq : denoteT bt fuel (mk v (hoistAt r1 r2).2 (hoistAt q1 q2).2
              (aNormTBody b (q2 + 1)).1) e =
              T fuel v (aNormTBody b (q2 + 1)).1 w (.val w2) e := by
            simp only [CatCrypt.Crypto.Hax.hoistAt]
            rw [hrun, tm_bind_run, denoteT_var_run bt fuel _ e w hse]
            change anfLoopTailT bt fuel _ _ (.val w) e = _
            rw [anfLoopTailT_val bt fuel _ _ w hw, tm_bind_run, denoteT_var_run bt fuel _ e w2 ht]
            rfl
          rw [heq]
          exact hrel v _ b (hvx (by omega)) (hbody e₁ (by omega) hK) fuel w (.val w2)
            e e' hR')
        (hcf fuel v b w) (hoth fuel v b w)
      exact rutt_mono (fun r₁ r₂ h => ⟨h.1, h.2.1, fun j hj => (h.2.2 j (by omega)).trans
        (hR.2 j hj)⟩) (key e₁ e₂ ⟨hR.1, fun _ _ => rfl⟩)
    · rw [ite_eq_right hhb] at hh
      have hhf : hoistsBound hi = false := by simpa using hhb
      simp only [loopNorm, hlo, hhf, hr1, ite_true, Bool.false_eq_true, ite_false,
        List.append_nil] at hK ⊢
      have hrb := aNormTBody_le b (r2 + 1)
      have hlr := hl k (by rw [hr1]; omega) g fuel
      rw [hr1] at hlr
      refine RefT.congr_tgt ?_ (hoistBind_runT bt fuel r1 _ r2)
      refine letBind_hoist_relT
        (Tt := anfLoopTailT bt fuel hi (T fuel v (aNormTBody b (r2 + 1)).1))
        (fun e₁ e₂ w h => h.extend_tmp hkr (by omega) w) hlr ?_ ?_ hcfL hothL
      · intro env w hw _
        simp only [CatCrypt.Crypto.Hax.hoistAt]
        rw [hrun, tm_bind_run, denoteT_var_run bt fuel _ env w hw]
        rfl
      · intro w _
        exact anfLoopTailT_rel fuel (refET_frameOk bt hok (by omega) hi hh g fuel)
          (fun vlo rhi => hrel v _ b (hvx (by omega)) (hbody g (by omega) hK) fuel vlo rhi)
          (hoth fuel v b) _
  · rw [ite_eq_right hlo] at hl
    have hlf : hoistsLo lo hi = false := by simpa using hlo
    by_cases hhb : hoistsBound hi = true
    · rw [ite_eq_left hhb] at hh
      obtain ⟨l, rfl⟩ : ∃ l, lo = .lit l := by
        cases lo
        case lit l => exact ⟨l, rfl⟩
        all_goals simp [hoistsLo, hhb] at hlf
      rcases hq : aNormTBody hi k with ⟨q1, q2⟩
      have hkq : k ≤ q2 := by have := aNormTBody_le hi k; rw [hq] at this; exact this
      simp only [loopNorm, hlf, hhb, hq, ite_true, Bool.false_eq_true, ite_false,
        List.nil_append] at hK ⊢
      have hqb := aNormTBody_le b (q2 + 1)
      have hhq := hh k (by rw [hq]; omega) g fuel
      rw [hq] at hhq
      have hl0 := Value.ofLit_not_isControlFlow l
      refine RefT.congr_tgt ?_ (hoistBind_runT bt fuel q1 _ q2)
      refine RefT.congr_src
        (s₂ := denoteT bt fuel hi >>= T fuel v b (Value.ofLit l)) ?_
        (fun env => by
          rw [hrun, tm_bind_run, NFCallTreeRepeatCount.denoteT_lit_run]
          exact congrFun (anfLoopTailT_val bt fuel hi _ _ hl0) env)
      refine letBind_hoist_relT (Tt := T fuel v (aNormTBody b (q2 + 1)).1 (Value.ofLit l))
        (fun e₁ e₂ w h => h.extend_tmp hkq (by omega) w) hhq ?_ ?_
        (hcf fuel v b _) (hoth fuel v b _)
      · intro env w hw _
        simp only [CatCrypt.Crypto.Hax.hoistAt]
        rw [hrun, tm_bind_run, NFCallTreeRepeatCount.denoteT_lit_run]
        change anfLoopTailT bt fuel _ _ (.val (Value.ofLit l)) env = _
        rw [anfLoopTailT_val bt fuel _ _ _ hl0, tm_bind_run, denoteT_var_run bt fuel _ env w hw]
        rfl
      · intro w _
        exact hrel v _ b (hvx (k' := k) (by omega)) (hbody g (by omega) hK) fuel _ _
    · rw [ite_eq_right hhb] at hh
      have hhf : hoistsBound hi = false := by simpa using hhb
      simp only [loopNorm, hlf, hhf, Bool.false_eq_true, ite_false, List.append_nil,
        prependBindings_nil] at hK ⊢
      have hkb := aNormTBody_le b k
      refine RefT.congr_tgt ?_ (fun env => congrFun (hrun fuel v lo hi _) env)
      refine RefT.congr_src ?_ (fun env => congrFun (hrun fuel v lo hi b) env)
      refine RefT.bind (refET_frameOk bt hok (by omega) lo hl g fuel) (fun o _ => ?_)
        (fun a ha s => ?_)
      · exact anfLoopTailT_rel fuel (refET_frameOk bt hok (by omega) hi hh g fuel)
          (fun vlo rhi => hrel v _ b (hvx (by omega)) (hbody g (Nat.le_refl _) hK) fuel vlo rhi)
          (hoth fuel v b) o
      · obtain ⟨m, rfl⟩ := ha
        exact ⟨_, rfl, m, rfl⟩

include hok in
/-- **The hoisting pass refines the reading at the level of call trees.** For an expression
    satisfying `ANormDOk ok`, with no admissible name among the first `K` fresh names, the
    hoisted form from every counter `k` refines the expression under `ARel K k g`. -/
theorem aNormTBody_relT (e : ImpExpr) : ANormDOk ok e = true → ANormDSimT bt K e := by
  have ext : ∀ {k : Nat} {g : Env}, k ≤ K → ∀ n, ok n = true → ∀ e₁ e₂ w,
      ARel K k g e₁ e₂ → ARel K k g (e₁.extend n w) (e₂.extend n w) :=
    fun hkK n hn e₁ e₂ w h => h.extend hkK (hok n hn) w
  induction e using ImpExpr.ind with
  | lit l =>
    intro _ k hK g fuel
    simp only [aNormTBody] at hK ⊢
    exact refET_frameOk bt hok hK _ rfl g fuel
  | unitVal =>
    intro _ k hK g fuel
    simp only [aNormTBody] at hK ⊢
    exact refET_frameOk bt hok hK _ rfl g fuel
  | continue_ =>
    intro _ k hK g fuel
    simp only [aNormTBody] at hK ⊢
    exact refET_frameOk bt hok hK _ rfl g fuel
  | break_none =>
    intro _ k hK g fuel
    simp only [aNormTBody] at hK ⊢
    exact refET_frameOk bt hok hK _ rfl g fuel
  | var n =>
    intro hD k hK g fuel
    simp only [aNormTBody] at hK ⊢
    exact refET_frameOk bt hok hK _ (by simpa [ANormDOk, frameOk] using hD) g fuel
  | lam ps b _ =>
    intro _ k _ g fuel
    exact RefT.of_bad fun _ => by simp only [denoteT]; exact ⟨_, rfl, _, rfl⟩
  | match_ => intro hD; simp [ANormDOk] at hD
  | typeAscription e ty ih =>
    intro hD k hK g fuel
    simp only [ANormDOk] at hD
    simp only [aNormTBody] at hK ⊢
    exact RefT.congr_src (ih hD k hK g fuel) (fun env => by rw [denoteT])
  | proj e _ ih | borrow e ih | deref e ih | break_some e ih | earlyReturn e ih
  | questionMark e ih | cfBreak e ih | cfContinue e ih | cfBreakContinue e ih =>
    intro hD k hK g fuel
    simp only [ANormDOk] at hD
    simp only [aNormTBody] at hK ⊢
    have h := ANormDSimT.at bt (ih hD) (k := k) (k' := k) (Nat.le_refl _) hK g
    simp only [denoteT]
    relT_step
  | assign n r ih =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    have hkr := aNormTBody_le r k
    have h := ANormDSimT.at bt (ih hD.2) (k := k) (k' := k) (Nat.le_refl _) hK g
    have hn := ext (k := k) (g := g) (by omega) n hD.1
    simp only [denoteT]
    relT_step
  | seq a b iha ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    have hka := aNormTBody_le a k
    have hab := aNormTBody_le b (aNormTBody a k).2
    have h1 := ANormDSimT.at bt (iha hD.1) (k := k) (k' := k) (Nat.le_refl _) (by omega) g
    have h2 := ANormDSimT.at bt (ihb hD.2) hka hK g
    simp only [denoteT]
    relT_step
  | whileLoop c b ihc ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    have hkc := aNormTBody_le c k
    have hcb := aNormTBody_le b (aNormTBody c k).2
    have h1 := ANormDSimT.at bt (ihc hD.1) (k := k) (k' := k) (Nat.le_refl _) (by omega) g
    have h2 := ANormDSimT.at bt (ihb hD.2) hkc hK g
    simp only [denoteT]
    exact denoteWhileOrigT_rel h1 h2 fuel
  | whileFold c b ihc ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    have hkc := aNormTBody_le c k
    have hcb := aNormTBody_le b (aNormTBody c k).2
    have h1 := ANormDSimT.at bt (ihc hD.1) (k := k) (k' := k) (Nat.le_refl _) (by omega) g
    have h2 := ANormDSimT.at bt (ihb hD.2) hkc hK g
    simp only [denoteT]
    exact denoteWhileT_rel h1 h2 fuel
  | whileFoldReturn c b ihc ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    have hkc := aNormTBody_le c k
    have hcb := aNormTBody_le b (aNormTBody c k).2
    have h1 := ANormDSimT.at bt (ihc hD.1) (k := k) (k' := k) (Nat.le_refl _) (by omega) g
    have h2 := ANormDSimT.at bt (ihb hD.2) hkc hK g
    simp only [denoteT]
    exact denoteWhileReturnT_rel h1 h2 fuel
  | letBind n v b ihv ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    have hkv := aNormTBody_le v k
    have hvb := aNormTBody_le b (aNormTBody v k).2
    have hv := ANormDSimT.at bt (ihv hD.1.2) (k := k) (k' := k) (Nat.le_refl _) (by omega) g
    have hb := ANormDSimT.at bt (ihb hD.2) hkv hK g
    have hn := ext (k := k) (g := g) (by omega) n hD.1.1
    refine RefT.congr_tgt ?_ (letBindNorm_runT bt fuel n _ _)
    simp only [denoteT]
    relT_step
  | app f args ih =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    intro e₁ e₂ hR
    rw [denoteT_app_run]
    refine aNormTArgs_relT bt hok args (fun a ha => ih a ha (ANormDOkList_mem hD.2 a ha)) hD.1
      (ANormDOkList_mem hD.2) k hK g fuel (fun _ => True)
      (fun _ _ _ _ => leafP_of_forall (fun _ _ => trivial) _) _ _ _ e₁ e₂ hR trivial
      (fun s₂ t => .fail ⟨_, rfl⟩) (fun vals s₁ s₂ hR' _ hDv => ?_)
    rw [denoteT_app_run, hDv]
    exact (RefT.bind (badα := fun _ => False) (RefT.lift _)
      (fun r _ => by split <;> exact RefT.pure _) (fun _ h => h.elim)) s₁ s₂ hR'
  | tuple es ih =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    intro e₁ e₂ hR
    rw [denoteT_tuple_run]
    refine aNormTArgs_relT bt hok es (fun a ha => ih a ha (ANormDOkList_mem hD.2 a ha)) hD.1
      (ANormDOkList_mem hD.2) k hK g fuel (fun _ => True)
      (fun _ _ _ _ => leafP_of_forall (fun _ _ => trivial) _) _ _ _ e₁ e₂ hR trivial
      (fun s₂ t => .fail ⟨_, rfl⟩) (fun vals s₁ s₂ hR' _ hDv => ?_)
    rw [denoteT_tuple_run, hDv]
    exact .ret ⟨rfl, hR'⟩
  | ifThenElse c t e ihc iht ihe =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    by_cases hv : isVar c = true
    · obtain ⟨x, rfl⟩ := isVar_eq_true hv
      simp only [aNormTBody, hv, ite_true, prependBindings_nil] at hK ⊢
      have hkt := aNormTBody_le t k
      have hte := aNormTBody_le e (aNormTBody t k).2
      have h1 := refET_frameOk bt hok (k := k) (by omega) (.var x)
        (by simpa [ANormDOk, frameOk] using hD.1.1) g
      have h2 := ANormDSimT.at bt (iht hD.1.2) (k := k) (k' := k) (Nat.le_refl _) (by omega) g
      have h3 := ANormDSimT.at bt (ihe hD.2) hkt hK g
      refine RefT.congr_tgt ?_ (fun env => congrFun (ifThenElse_run_tailT bt fuel _ _ _) env)
      refine RefT.congr_src ?_ (fun env => congrFun (ifThenElse_run_tailT bt fuel _ _ _) env)
      exact RefT.bind (h1 fuel) (fun o _ => iteTailT_rel fuel (h2 fuel) (h3 fuel) o)
        (fun a ha s => by obtain ⟨m, rfl⟩ := ha; exact ⟨_, rfl, m, rfl⟩)
    · have hvf : isVar c = false := by simpa using hv
      rcases hr1 : aNormTBody c k with ⟨r1, r2⟩
      simp only [aNormTBody, hvf, hr1, Bool.false_eq_true, ite_false] at hK ⊢
      have hkr : k ≤ r2 := by have := aNormTBody_le c k; rw [hr1] at this; exact this
      have hrt := aNormTBody_le t (r2 + 1)
      have hte := aNormTBody_le e (aNormTBody t (r2 + 1)).2
      have hc := ihc hD.1.1 k (by rw [hr1]; omega) g fuel
      rw [hr1] at hc
      have h2 := ANormDSimT.at bt (iht hD.1.2) (k := k) (k' := r2 + 1) (by omega) (by omega) g
        fuel
      have h3 := ANormDSimT.at bt (ihe hD.2) (k := k) (by omega) hK g fuel
      refine RefT.congr_tgt ?_ (hoistBind_runT bt fuel r1 _ r2)
      refine RefT.congr_src ?_ (fun env => congrFun (ifThenElse_run_tailT bt fuel c t e) env)
      refine letBind_hoist_relT (Tt := iteTailT bt fuel (aNormTBody t (r2 + 1)).1
          (aNormTBody e (aNormTBody t (r2 + 1)).2).1)
        (fun e₁ e₂ w h => h.extend_tmp hkr (by omega) w) hc ?_ ?_ (iteTailT_cf bt fuel t e)
        (iteTailT_other bt fuel t e)
      · intro env w hw _
        simp only [CatCrypt.Crypto.Hax.hoistAt]
        rw [ifThenElse_run_tailT, tm_bind_run, denoteT_var_run bt fuel _ env w hw]
        rfl
      · intro w _
        exact iteTailT_rel fuel h2 h3 _
  | forLoop v lo hi b ihl ihh ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    rw [aNormTBody_forLoop_loopNorm] at hK ⊢
    exact loopNorm_relT bt hok .forLoop (fun fuel v b => forTailOrigT bt fuel v b)
      (fun fuel v lo hi b => forLoop_run_tailT bt fuel v b lo hi)
      (fun fuel v b => forTailOrigT_cf bt fuel v b)
      (fun fuel v b => forTailOrigT_other bt fuel v b)
      (fun _ _ _ hv h fuel => forTailOrigT_rel hv h fuel) v lo hi b hD.1.1.1
      (ite_bound_sim ihl hD.1.1.2) (ite_bound_sim ihh hD.1.2) (ihb hD.2) k hK g fuel
  | forFold v lo hi b ihl ihh ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    rw [aNormTBody_forFold_loopNorm] at hK ⊢
    exact loopNorm_relT bt hok .forFold (fun fuel v b => forTailFoldT bt fuel v b)
      (fun fuel v lo hi b => forFold_run_tailT bt fuel v b lo hi)
      (fun fuel v b => forTailFoldT_cf bt fuel v b)
      (fun fuel v b => forTailFoldT_other bt fuel v b)
      (fun _ _ _ hv h fuel => forTailFoldT_rel hv h fuel) v lo hi b hD.1.1.1
      (ite_bound_sim ihl hD.1.1.2) (ite_bound_sim ihh hD.1.2) (ihb hD.2) k hK g fuel
  | forLoopRev v lo hi b ihl ihh ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    rw [aNormTBody_forLoopRev_loopNorm] at hK ⊢
    exact loopNorm_relT bt hok .forLoopRev (fun fuel v b => forTailRevOrigT bt fuel v b)
      (fun fuel v lo hi b => forLoopRev_run_tailT bt fuel v b lo hi)
      (fun fuel v b => forTailRevOrigT_cf bt fuel v b)
      (fun fuel v b => forTailRevOrigT_other bt fuel v b)
      (fun _ _ _ hv h fuel => forTailRevOrigT_rel hv h fuel) v lo hi b hD.1.1.1
      (ite_bound_sim ihl hD.1.1.2) (ite_bound_sim ihh hD.1.2) (ihb hD.2) k hK g fuel
  | forFoldRev v lo hi b ihl ihh ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    rw [aNormTBody_forFoldRev_loopNorm] at hK ⊢
    exact loopNorm_relT bt hok .forFoldRev (fun fuel v b => forTailFoldRevT bt fuel v b)
      (fun fuel v lo hi b => forFoldRev_run_tailT bt fuel v b lo hi)
      (fun fuel v b => forTailFoldRevT_cf bt fuel v b)
      (fun fuel v b => forTailFoldRevT_other bt fuel v b)
      (fun _ _ _ hv h fuel => forTailFoldRevT_rel hv h fuel) v lo hi b hD.1.1.1
      (ite_bound_sim ihl hD.1.1.2) (ite_bound_sim ihh hD.1.2) (ihb hD.2) k hK g fuel
  | forFoldReturn v lo hi b _ _ ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    have hkb := aNormTBody_le b k
    have hl := refET_frameOk bt hok (k := k) (by omega) lo hD.1.1.2 g
    have hhi := refET_frameOk bt hok (k := k) (by omega) hi hD.1.2 g
    have hb := ANormDSimT.at bt (ihb hD.2) (k := k) (k' := k) (Nat.le_refl _) hK g
    have hvx := ext (k := k) (g := g) (by omega) v hD.1.1.1
    have := denoteForLoopReturnT_rel (bt := bt) hvx hb
    simp only [denoteT]
    loop_head_step
  | forFoldRevReturn v lo hi b _ _ ihb =>
    intro hD k hK g fuel
    simp only [ANormDOk, Bool.and_eq_true] at hD
    simp only [aNormTBody] at hK ⊢
    have hkb := aNormTBody_le b k
    have hl := refET_frameOk bt hok (k := k) (by omega) lo hD.1.1.2 g
    have hhi := refET_frameOk bt hok (k := k) (by omega) hi hD.1.2 g
    have hb := ANormDSimT.at bt (ihb hD.2) (k := k) (k' := k) (Nat.le_refl _) hK g
    have hvx := ext (k := k) (g := g) (by omega) v hD.1.1.1
    have := denoteForLoopRevReturnT_rel (bt := bt) hvx hb
    simp only [denoteT]
    loop_head_step

end Sim


/-! ## Tail binding and the composed pass -/

section Tails

variable (bt : TreeTable E) (fuel : Nat)

/-- Binding a tail to the return slot keeps the outcome of every leaf. -/
theorem bindTail_relT {Fail : Outcome × Env → Prop} (e : ImpExpr) (env : Env) :
    Rutt (fun e₁ e₂ : E.Event => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
      (fun r₁ r₂ => r₂.1 = r₁.1) Fail (denoteT bt fuel e env)
      (denoteT bt fuel (if isTailBindable e then .letBind retName e (.var retName) else e)
        env) := by
  split
  · rw [denoteT_letBind_runIf]
    have := rutt_bind_same (RR := fun (r₁ r₂ : Outcome × Env) => r₂.1 = r₁.1) (Fail := Fail)
      (denoteT bt fuel e env) (k₁ := CallTree.ret)
      (k₂ := fun p => match p with
        | (.val w, e1) => if w.isControlFlow then .ret (.val w, e1)
            else denoteT bt fuel (.var retName) (e1.extend retName w)
        | (o, e1) => .ret (o, e1)) (fun p => ?_)
    · rwa [bind_ret] at this
    rcases p with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases hw : w.isControlFlow
      · simp only [hw, Bool.false_eq_true, ite_false]
        rw [denoteT_var_run bt fuel _ _ w (Env.extend_same _ _ _)]
        exact .ret rfl
      · simp only [hw, ite_true]
        exact .ret rfl
    all_goals exact .ret rfl
  · exact rutt_refl (RR := fun (r₁ r₂ : Outcome × Env) => r₂.1 = r₁.1) (fun _ => rfl) _

/-- **Tail binding keeps the outcome of every leaf** of the call tree. -/
theorem bindTails_relT {Fail : Outcome × Env → Prop} (e : ImpExpr) :
    ∀ env : Env, Rutt (fun e₁ e₂ : E.Event => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
      (fun r₁ r₂ => r₂.1 = r₁.1) Fail (denoteT bt fuel e env)
      (denoteT bt fuel (bindTails e) env) := by
  induction e using ImpExpr.ind
  case letBind n v b _ ihb =>
    intro env
    simp only [bindTails]
    rw [denoteT_letBind_run', denoteT_letBind_run']
    refine rutt_bind_same _ fun q => ?_
    rcases q with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w with
      | controlFlow kk w => exact .ret rfl
      | _ => exact ihb _
    all_goals exact .ret rfl
  case seq a b _ ihb =>
    intro env
    simp only [bindTails]
    rw [denoteT_seq_run, denoteT_seq_run]
    refine rutt_bind_same _ fun q => ?_
    rcases q with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w with
      | controlFlow kk w => exact .ret rfl
      | _ => exact ihb _
    all_goals exact .ret rfl
  case ifThenElse c t e _ iht ihe =>
    intro env
    simp only [bindTails]
    rw [denoteT_ifThenElse_run, denoteT_ifThenElse_run]
    refine rutt_bind_same _ fun q => ?_
    rcases q with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w with
      | controlFlow kk w => exact .ret rfl
      | bool bb =>
        cases bb
        · exact ihe _
        · exact iht _
      | _ => exact .ret rfl
    all_goals exact .ret rfl
  all_goals
    intro env
    exact bindTail_relT bt fuel _ env

/-- **`aNormalizeTotal` refines the reading at the level of call trees.** Under
    `aNormTDenoteOk e`, from every environment, the call tree of `e` is related to the call tree
    of `aNormalizeTotal e` at equal events and answers: a leaf of `e` whose outcome is an error
    is a failed leaf, and every other leaf of `e` is matched by a leaf with the same outcome. -/
theorem aNormalizeTotal_relT (h₁ : ∀ e : E.Event, E.Resp e) (bt : TreeTable E) (fuel : Nat)
    (e : ImpExpr) (h : aNormTDenoteOk e = true) (env : Env) :
    RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) (fun r₁ r₂ => r₂.1 = r₁.1)
      (fun r => ∃ m, r.1 = .err m)
      (denoteT bt fuel e env) (denoteT bt fuel (aNormalizeTotal e) env) := by
  have hok : ∀ n, (fun n => (List.range (aNormalizeTotalCount e)).all
      (fun j => n != anormName j)) n = true → ¬ AnormBelow (aNormalizeTotalCount e) n := by
    rintro n hn ⟨j, hj, rfl⟩
    simp only [List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hn
    exact hn j hj rfl
  have hN := aNormTBody_relT bt hok (bindTails e) h 0 (Nat.le_refl _) env fuel env env
    ⟨fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  have hB := bindTails_relT bt fuel (Fail := fun r : Outcome × Env => ∃ m, r.1 = .err m) e env
  refine NFProgCallTreeExt.RuttS.mono ?_ (NFProgCallTreeFlat.ruttS_eqTrans
    (fun r₀ r₁ h01 hf => ?_) (RuttS.of_rutt hB) (RuttS.of_rutt hN))
  · rintro r₀ r₂ ⟨r₁, h01, h12⟩
    exact h12.1.trans h01
  · obtain ⟨m, hm⟩ := hf
    exact ⟨m, h01 ▸ hm⟩

end Tails

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeANorm
