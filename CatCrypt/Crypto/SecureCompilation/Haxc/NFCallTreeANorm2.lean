/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeANorm
public import CatCrypt.Crypto.Hax.ANormCoreDenote

/-!
# Bindings and loop tails of the A-normaliser at the level of call trees

The bindings the A-normaliser `aNormalizeTotal` introduces read, at every tree table, as the
bindings they replace: floating the leading bindings of a right-hand side outwards, binding a
conditional right-hand side in each branch, and binding a hoisted subterm to a fresh name have
the call tree of the plain binding. A counted loop and a conditional read as their first
operand followed by a tail, and binding that operand to a fresh name refines the source under
a relation of target and source environments (`ARel`).

## Main definitions

* `forTailOrigT`, `forTailFoldT`, `forTailRevOrigT`, `forTailFoldRevT`, `anfLoopTailT`,
  `iteTailT` — the readings after the first operand of a counted loop or a conditional.

## Main results

* `letBindNorm_runT`, `hoistBind_runT` — floating the leading bindings of a right-hand side,
  binding a conditional right-hand side in each branch and binding a hoisted subterm keep the
  call tree.
* `refET_widen` — a simulation from counter `k'` is a simulation from every `k ≤ k'`.
* `letBind_hoist_contT`, `letBind_hoist_relT` — binding a subterm to a fresh name refines the
  source.
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

/-! ## Runs of bindings -/

section Runs

variable (bt : TreeTable E) (fuel : Nat)

/-- Floating the leading bindings of `x` outwards: for a context `F` that reads as
    `let n = c; B` on every `c`, the bindings of `x` followed by `F` applied to its core read
    as `let n = x; B`. -/
theorem floatCtx_runT (n : String) (B : ImpExpr) (F : ImpExpr → ImpExpr)
    (hF : ∀ c env, denoteT bt fuel (F c) env = denoteT bt fuel (.letBind n c B) env) :
    ∀ (x : ImpExpr) (env : Env),
      denoteT bt fuel (prependBindings (splitLetBinds x).1 (F (splitLetBinds x).2)) env =
        denoteT bt fuel (.letBind n x B) env := by
  intro x
  induction x using ImpExpr.ind
  case letBind a v t _ iht =>
    intro env
    rw [splitLetBinds_letBind, prependBindings_cons, denoteT_letBind_run',
      denoteT_letBind_run', denoteT_letBind_run', bind_assoc]
    congr 1
    funext p
    rcases p with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w
      case controlFlow b w => rfl
      all_goals (dsimp only; rw [iht, denoteT_letBind_run'])
    all_goals rfl
  all_goals intro env; exact hF _ env

/-- `bindRhs` reads as `letBind`. -/
theorem bindRhs_runT (x : String) (r body : ImpExpr) (env : Env) :
    denoteT bt fuel (bindRhs x r body) env = denoteT bt fuel (.letBind x r body) env := by
  cases r
  case ifThenElse c t e =>
    have hfl : ∀ (s : ImpExpr) (env' : Env),
        denoteT bt fuel (floatLet x s .unitVal) env' =
          denoteT bt fuel (.letBind x s .unitVal) env' :=
      fun s env' => floatCtx_runT bt fuel x .unitVal (fun c => .letBind x c .unitVal)
        (fun _ _ => rfl) s env'
    simp only [bindRhs]
    rw [denoteT_seq_run, denoteT_ifThenElse_run, denoteT_letBind_run', denoteT_ifThenElse_run,
      bind_assoc, bind_assoc]
    congr 1
    funext p
    rcases p with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w
      case bool b =>
        cases b <;>
        · dsimp only
          rw [hfl, denoteT_letBind_run', bind_assoc]
          congr 1
          funext q
          rcases q with ⟨o2, e2⟩
          rcases o2 with w2 | _ | _ | _ | _
          · cases w2 <;> first | rfl | (dsimp only; rw [denoteT]; rfl)
          all_goals rfl
      all_goals rfl
    all_goals rfl
  all_goals rfl

/-- The normal form of `let n = x; B`: the leading bindings of `x` floated outwards and its
    core bound by `bindRhs`, reads as `let n = x; B`. -/
theorem letBindNorm_runT (n : String) (x B : ImpExpr) (env : Env) :
    denoteT bt fuel (prependBindings (splitLetBinds x).1 (bindRhs n (splitLetBinds x).2 B)) env =
      denoteT bt fuel (.letBind n x B) env :=
  floatCtx_runT bt fuel n B (fun c => bindRhs n c B) (fun c env => bindRhs_runT bt fuel n c B env)
    x env

/-- The bindings `hoistAt x j` followed by `C` read as `let __anorm_j = x; C`. -/
theorem hoistBind_runT (x C : ImpExpr) (j : Nat) (env : Env) :
    denoteT bt fuel (prependBindings (hoistAt x j).1 C) env =
      denoteT bt fuel (.letBind (anormName j) x C) env := by
  simp only [hoistAt]
  rw [prependBindings_append]
  exact floatCtx_runT bt fuel (anormName j) C (fun c => prependBindings [(anormName j, c)] C)
    (fun _ _ => rfl) x env

end Runs


/-! ## The relation between target and source environments -/

/-- A simulation from counter `k'` is a simulation from every counter `k ≤ k'`. -/
theorem refET_widen {K k k' : Nat} (hk : k ≤ k') {t s : TM E Outcome}
    (h : ∀ g, RefET (ARel K k' g) t s) : ∀ g, RefET (ARel K k g) t s := by
  intro g e₁ e₂ hR
  exact rutt_mono (fun r₁ r₂ hr => ⟨hr.1, hr.2.1, fun j hj => (hr.2.2 j (by omega)).trans
    (hR.2 j hj)⟩) (h e₁ e₁ e₂ ⟨hR.1, fun _ _ => rfl⟩)

/-- A refinement with a target of equal readings. -/
theorem RefT.congr_tgt {α : Type} {P Q : Env → Env → Prop} {bad : α → Prop}
    {t₁ t₂ s : TM E α} (h : RefT P Q bad t₂ s) (he : ∀ env, t₁ env = t₂ env) :
    RefT P Q bad t₁ s := by
  intro e₁ e₂ hP
  rw [he e₁]
  exact h e₁ e₂ hP

/-- A refinement of a source of equal readings. -/
theorem RefT.congr_src {α : Type} {P Q : Env → Env → Prop} {bad : α → Prop}
    {t s₁ s₂ : TM E α} (h : RefT P Q bad t s₂) (he : ∀ env, s₁ env = s₂ env) :
    RefT P Q bad t s₁ := by
  intro e₁ e₂ hP
  rw [he e₂]
  exact h e₁ e₂ hP

/-! ## Counted loops and conditionals after their first operand -/

section Tail

variable (bt : TreeTable E) (fuel : Nat) (var : String) (body : ImpExpr)

/-- The reading of `forLoop var lo hi body` after `lo` evaluates to the value `vlo` and `hi`
    to the outcome `rhi`. -/
def forTailOrigT (vlo : Value) (rhi : Outcome) : TM E Outcome :=
  match vlo, rhi with
  | .int lo_val, .val (.int hi_val) => denoteForLoopOrigT bt fuel var lo_val hi_val body
  | .int lo_val, .val (.uint _ hi_val) => denoteForLoopOrigT bt fuel var lo_val hi_val body
  | .uint _ lo_val, .val (.int hi_val) => denoteForLoopOrigT bt fuel var lo_val hi_val body
  | .uint _ lo_val, .val (.uint _ hi_val) => denoteForLoopOrigT bt fuel var lo_val hi_val body
  | _, .val _ => pure (.err "for loop bounds must be integers")
  | _, other => pure other

/-- The reading of `forFold var lo hi body` after `lo` evaluates to the value `vlo` and `hi`
    to the outcome `rhi`. -/
def forTailFoldT (vlo : Value) (rhi : Outcome) : TM E Outcome :=
  match vlo, rhi with
  | .int lo_val, .val (.int hi_val) => denoteForLoopT bt fuel var lo_val hi_val body
  | .int lo_val, .val (.uint _ hi_val) => denoteForLoopT bt fuel var lo_val hi_val body
  | .uint _ lo_val, .val (.int hi_val) => denoteForLoopT bt fuel var lo_val hi_val body
  | .uint _ lo_val, .val (.uint _ hi_val) => denoteForLoopT bt fuel var lo_val hi_val body
  | _, .val (.controlFlow _ _) => pure rhi
  | _, .val _ => pure (.err "for loop bounds must be integers")
  | _, other => pure other

/-- The reading of `forLoopRev var lo hi body` after `lo` evaluates to the value `vlo` and
    `hi` to the outcome `rhi`. -/
def forTailRevOrigT (vlo : Value) (rhi : Outcome) : TM E Outcome :=
  match vlo, rhi with
  | .int lo_val, .val (.int hi_val) => denoteForLoopRevOrigT bt fuel var lo_val hi_val body
  | .int lo_val, .val (.uint _ hi_val) => denoteForLoopRevOrigT bt fuel var lo_val hi_val body
  | .uint _ lo_val, .val (.int hi_val) => denoteForLoopRevOrigT bt fuel var lo_val hi_val body
  | .uint _ lo_val, .val (.uint _ hi_val) =>
      denoteForLoopRevOrigT bt fuel var lo_val hi_val body
  | _, .val _ => pure (.err "for loop bounds must be integers")
  | _, other => pure other

/-- The reading of `forFoldRev var lo hi body` after `lo` evaluates to the value `vlo` and
    `hi` to the outcome `rhi`. -/
def forTailFoldRevT (vlo : Value) (rhi : Outcome) : TM E Outcome :=
  match vlo, rhi with
  | .int lo_val, .val (.int hi_val) => denoteForLoopRevT bt fuel var lo_val hi_val body
  | .int lo_val, .val (.uint _ hi_val) => denoteForLoopRevT bt fuel var lo_val hi_val body
  | .uint _ lo_val, .val (.int hi_val) => denoteForLoopRevT bt fuel var lo_val hi_val body
  | .uint _ lo_val, .val (.uint _ hi_val) => denoteForLoopRevT bt fuel var lo_val hi_val body
  | _, .val (.controlFlow _ _) => pure rhi
  | _, .val _ => pure (.err "for loop bounds must be integers")
  | _, other => pure other

/-- The reading of a counted loop after its lower bound evaluates to the outcome `rlo`: a
    control-flow value or a non-value is the result, and a plain value `vlo` is followed by the
    reading of `hi` and the tail `T vlo`. -/
def anfLoopTailT (hi : ImpExpr) (T : Value → Outcome → TM E Outcome) (rlo : Outcome) :
    TM E Outcome :=
  match rlo with
  | .val w => if w.isControlFlow then pure (.val w) else denoteT bt fuel hi >>= T w
  | other => pure other

/-- The reading of `ifThenElse c t e` after `c` evaluates to the outcome `rc`. -/
def iteTailT (t e : ImpExpr) (rc : Outcome) : TM E Outcome :=
  match rc with
  | .val (.controlFlow k v) => pure (.val (.controlFlow k v))
  | .val (.bool true) => denoteT bt fuel t
  | .val (.bool false) => denoteT bt fuel e
  | .val _ => pure (.err "if condition not a bool")
  | other => pure other

/-- The reading of `forLoop` as its lower bound followed by the tail. -/
theorem forLoop_run_tailT (lo hi : ImpExpr) :
    denoteT bt fuel (.forLoop var lo hi body) =
      denoteT bt fuel lo >>= anfLoopTailT bt fuel hi (forTailOrigT bt fuel var body) := by
  rw [denoteT]
  congr 1
  funext rlo
  rcases rlo with w | _ | _ | _ | _
  · cases w <;> rfl
  all_goals rfl

/-- The reading of `forLoopRev` as its lower bound followed by the tail. -/
theorem forLoopRev_run_tailT (lo hi : ImpExpr) :
    denoteT bt fuel (.forLoopRev var lo hi body) =
      denoteT bt fuel lo >>= anfLoopTailT bt fuel hi (forTailRevOrigT bt fuel var body) := by
  rw [denoteT]
  congr 1
  funext rlo
  rcases rlo with w | _ | _ | _ | _
  · cases w <;> rfl
  all_goals rfl

/-- The reading of `forFold` as its lower bound followed by the tail. -/
theorem forFold_run_tailT (lo hi : ImpExpr) :
    denoteT bt fuel (.forFold var lo hi body) =
      denoteT bt fuel lo >>= anfLoopTailT bt fuel hi (forTailFoldT bt fuel var body) := by
  rw [denoteT]
  congr 1
  funext rlo
  rcases rlo with w | _ | _ | _ | _
  · cases w <;> rfl
  all_goals rfl

/-- The reading of `forFoldRev` as its lower bound followed by the tail. -/
theorem forFoldRev_run_tailT (lo hi : ImpExpr) :
    denoteT bt fuel (.forFoldRev var lo hi body) =
      denoteT bt fuel lo >>= anfLoopTailT bt fuel hi (forTailFoldRevT bt fuel var body) := by
  rw [denoteT]
  congr 1
  funext rlo
  rcases rlo with w | _ | _ | _ | _
  · cases w <;> rfl
  all_goals rfl

/-- The reading of a conditional as its condition followed by the tail. -/
theorem ifThenElse_run_tailT (c t e : ImpExpr) :
    denoteT bt fuel (.ifThenElse c t e) = denoteT bt fuel c >>= iteTailT bt fuel t e := by
  rw [denoteT]
  rfl

end Tail


/-! ## Refinement after the first operand -/

section TailRel

variable {bt : TreeTable E} {R : Env → Env → Prop}

/-- The tails of `forLoop` refine each other when the bodies do. -/
theorem forTailOrigT_rel {var : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend var w) (e₂.extend var w))
    (h : ∀ fuel, RefET R (denoteT bt fuel b₁) (denoteT bt fuel b₂)) (fuel : Nat) (vlo : Value)
    (rhi : Outcome) :
    RefET R (forTailOrigT bt fuel var b₁ vlo rhi) (forTailOrigT bt fuel var b₂ vlo rhi) := by
  have hL := denoteForLoopOrigT_rel (bt := bt) hv h fuel
  unfold forTailOrigT
  split <;> first | exact hL _ _ | exact RefT.pure _

/-- The tails of `forFold` refine each other when the bodies do. -/
theorem forTailFoldT_rel {var : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend var w) (e₂.extend var w))
    (h : ∀ fuel, RefET R (denoteT bt fuel b₁) (denoteT bt fuel b₂)) (fuel : Nat) (vlo : Value)
    (rhi : Outcome) :
    RefET R (forTailFoldT bt fuel var b₁ vlo rhi) (forTailFoldT bt fuel var b₂ vlo rhi) := by
  have hL := denoteForLoopT_rel (bt := bt) hv h fuel
  unfold forTailFoldT
  split <;> first | exact hL _ _ | exact RefT.pure _

/-- The tails of `forLoopRev` refine each other when the bodies do. -/
theorem forTailRevOrigT_rel {var : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend var w) (e₂.extend var w))
    (h : ∀ fuel, RefET R (denoteT bt fuel b₁) (denoteT bt fuel b₂)) (fuel : Nat) (vlo : Value)
    (rhi : Outcome) :
    RefET R (forTailRevOrigT bt fuel var b₁ vlo rhi) (forTailRevOrigT bt fuel var b₂ vlo rhi) := by
  have hL := denoteForLoopRevOrigT_rel (bt := bt) hv h fuel
  unfold forTailRevOrigT
  split <;> first | exact hL _ _ | exact RefT.pure _

/-- The tails of `forFoldRev` refine each other when the bodies do. -/
theorem forTailFoldRevT_rel {var : String} {b₁ b₂ : ImpExpr}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend var w) (e₂.extend var w))
    (h : ∀ fuel, RefET R (denoteT bt fuel b₁) (denoteT bt fuel b₂)) (fuel : Nat) (vlo : Value)
    (rhi : Outcome) :
    RefET R (forTailFoldRevT bt fuel var b₁ vlo rhi) (forTailFoldRevT bt fuel var b₂ vlo rhi) := by
  have hL := denoteForLoopRevT_rel (bt := bt) hv h fuel
  unfold forTailFoldRevT
  split <;> first | exact hL _ _ | exact RefT.pure _

/-- The loop tails after the lower bound refine each other when the upper bound refines itself
    and the tails after both bounds refine each other. -/
theorem anfLoopTailT_rel {hi : ImpExpr} {T₁ T₂ : Value → Outcome → TM E Outcome} (fuel : Nat)
    (hhi : RefET R (denoteT bt fuel hi) (denoteT bt fuel hi))
    (hT : ∀ vlo rhi, RefET R (T₁ vlo rhi) (T₂ vlo rhi))
    (hoth : ∀ vlo o m, (∀ w, o ≠ .val w) → T₂ vlo o m = .ret (o, m)) (rlo : Outcome) :
    RefET R (anfLoopTailT bt fuel hi T₁ rlo) (anfLoopTailT bt fuel hi T₂ rlo) := by
  unfold anfLoopTailT
  split
  · split
    · exact RefT.pure _
    · refine RefT.bind hhi (fun a _ => hT _ a) (fun a ha s => ?_)
      obtain ⟨m, rfl⟩ := ha
      exact ⟨_, hoth _ _ s (fun w h' => by cases h'), m, rfl⟩
  · exact RefT.pure _

/-- The conditional tails refine each other when the branches do. -/
theorem iteTailT_rel {t₁ t₂ e₁ e₂ : ImpExpr} (fuel : Nat)
    (ht : RefET R (denoteT bt fuel t₁) (denoteT bt fuel t₂))
    (he : RefET R (denoteT bt fuel e₁) (denoteT bt fuel e₂)) (rc : Outcome) :
    RefET R (iteTailT bt fuel t₁ e₁ rc) (iteTailT bt fuel t₂ e₂ rc) := by
  unfold iteTailT
  split <;> first | exact ht | exact he | exact RefT.pure _

/-- **Binding a subterm to a fresh name, with the bound value in the relation.** Let the
    source read `hi` and continue with `Ts`, and the target bind `tmp` to `hi'` and read `C`.
    If `hi'` refines `hi`, binding `tmp` to `w` takes `R` to `Rw w`, `C` refines `Ts` on the
    plain value `w` from `Rw w` back to `R`, `Ts` returns a control-flow value or fails on it,
    and `Ts` passes non-values, then `let tmp = hi'; C` refines the source. -/
theorem letBind_hoist_contT {tmp : String} {hi hi' C : ImpExpr}
    {Ts : Outcome → TM E Outcome} {fuel : Nat} {Rw : Value → Env → Env → Prop}
    (hext : ∀ e₁ e₂ w, R e₁ e₂ → Rw w (e₁.extend tmp w) e₂)
    (hhi : RefET R (denoteT bt fuel hi') (denoteT bt fuel hi))
    (hT : ∀ w, w.isControlFlow = false → RefT (Rw w) R IsErr (denoteT bt fuel C) (Ts (.val w)))
    (hcf : ∀ w m, w.isControlFlow = true →
      Ts (.val w) m = .ret (.val w, m) ∨ ∃ r, Ts (.val w) m = .ret r ∧ IsErr r.1)
    (hother : ∀ o m, (∀ w, o ≠ .val w) → Ts o m = .ret (o, m)) :
    RefET R (denoteT bt fuel (.letBind tmp hi' C)) (denoteT bt fuel hi >>= Ts) := by
  intro e₁ e₂ hR
  rw [tm_bind_run, denoteT_letBind_run']
  refine rutt_bind (hhi e₁ e₂ hR) (fun r₁ r₂ hr => ?_) (fun r₁ hf t => ?_)
  · obtain ⟨h1, hR'⟩ := hr
    rcases r₁ with ⟨o, m₂⟩
    rcases r₂ with ⟨o', m₁⟩
    dsimp only at h1 hR' ⊢
    subst h1
    rcases o' with w | _ | _ | _ | _
    · cases w with
      | controlFlow kk v =>
        rcases hcf (.controlFlow kk v) m₂ rfl with h | ⟨r, h, hb⟩
        · rw [h]; exact .ret ⟨rfl, hR'⟩
        · rw [h]; exact .fail hb
      | _ => exact hT _ rfl _ _ (hext _ _ _ hR')
    all_goals rw [hother _ _ (fun w h' => by cases h')]; exact .ret ⟨rfl, hR'⟩
  · obtain ⟨m, hm⟩ := hf
    rcases r₁ with ⟨o, s⟩
    dsimp only at hm
    subst hm
    rw [hother _ _ (fun w h' => by cases h')]
    exact .fail ⟨m, rfl⟩

/-- **Binding a subterm to a fresh name.** Let the source read `hi` and continue with `Ts`,
    and the target bind `tmp` to `hi'` and read `C`, which continues as `Tt` on the value of
    `tmp`. If `hi'` refines `hi`, binding `tmp` alone in the target keeps `R`, `Tt` refines `Ts`
    on plain values, `Ts` returns a control-flow value or fails on it, and `Ts` passes
    non-values, then `let tmp = hi'; C` refines the source. -/
theorem letBind_hoist_relT {tmp : String} {hi hi' C : ImpExpr}
    {Ts Tt : Outcome → TM E Outcome} {fuel : Nat}
    (hext : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend tmp w) e₂)
    (hhi : RefET R (denoteT bt fuel hi') (denoteT bt fuel hi))
    (hC : ∀ e w, e tmp = some w → w.isControlFlow = false → denoteT bt fuel C e = Tt (.val w) e)
    (hT : ∀ w, w.isControlFlow = false → RefET R (Tt (.val w)) (Ts (.val w)))
    (hcf : ∀ w m, w.isControlFlow = true →
      Ts (.val w) m = .ret (.val w, m) ∨ ∃ r, Ts (.val w) m = .ret r ∧ IsErr r.1)
    (hother : ∀ o m, (∀ w, o ≠ .val w) → Ts o m = .ret (o, m)) :
    RefET R (denoteT bt fuel (.letBind tmp hi' C)) (denoteT bt fuel hi >>= Ts) :=
  letBind_hoist_contT (Rw := fun w e₁ e₂ => R e₁ e₂ ∧ e₁ tmp = some w)
    (fun e₁ e₂ w h => ⟨hext e₁ e₂ w h, Env.extend_same _ _ _⟩) hhi
    (fun w hw e₁ e₂ hR => by
      rw [hC e₁ w hR.2 hw]
      exact hT w hw e₁ e₂ hR.1)
    hcf hother

variable (bt) (fuel : Nat)

/-- The tail of `forLoop` passes non-values. -/
theorem forTailOrigT_other (var : String) (b : ImpExpr) (vlo : Value) (o : Outcome) (m : Env)
    (h : ∀ w, o ≠ .val w) : forTailOrigT bt fuel var b vlo o m = .ret (o, m) := by
  cases o with
  | val w => exact absurd rfl (h w)
  | _ => cases vlo <;> rfl

/-- The tail of `forLoop` fails on a control-flow upper bound. -/
theorem forTailOrigT_cf (var : String) (b : ImpExpr) (vlo w : Value) (m : Env)
    (hw : w.isControlFlow = true) :
    forTailOrigT bt fuel var b vlo (.val w) m = .ret (.val w, m) ∨
      ∃ r, forTailOrigT bt fuel var b vlo (.val w) m = .ret r ∧ IsErr r.1 := by
  cases w <;> simp [Value.isControlFlow] at hw
  right
  cases vlo <;> exact ⟨_, rfl, _, rfl⟩

/-- The tail of `forFold` passes non-values. -/
theorem forTailFoldT_other (var : String) (b : ImpExpr) (vlo : Value) (o : Outcome) (m : Env)
    (h : ∀ w, o ≠ .val w) : forTailFoldT bt fuel var b vlo o m = .ret (o, m) := by
  cases o with
  | val w => exact absurd rfl (h w)
  | _ => cases vlo <;> rfl

/-- The tail of `forFold` returns a control-flow upper bound. -/
theorem forTailFoldT_cf (var : String) (b : ImpExpr) (vlo w : Value) (m : Env)
    (hw : w.isControlFlow = true) :
    forTailFoldT bt fuel var b vlo (.val w) m = .ret (.val w, m) ∨
      ∃ r, forTailFoldT bt fuel var b vlo (.val w) m = .ret r ∧ IsErr r.1 := by
  cases w <;> simp [Value.isControlFlow] at hw
  left
  cases vlo <;> rfl

/-- The tail of `forLoopRev` passes non-values. -/
theorem forTailRevOrigT_other (var : String) (b : ImpExpr) (vlo : Value) (o : Outcome)
    (m : Env) (h : ∀ w, o ≠ .val w) : forTailRevOrigT bt fuel var b vlo o m = .ret (o, m) := by
  cases o with
  | val w => exact absurd rfl (h w)
  | _ => cases vlo <;> rfl

/-- The tail of `forLoopRev` fails on a control-flow upper bound. -/
theorem forTailRevOrigT_cf (var : String) (b : ImpExpr) (vlo w : Value) (m : Env)
    (hw : w.isControlFlow = true) :
    forTailRevOrigT bt fuel var b vlo (.val w) m = .ret (.val w, m) ∨
      ∃ r, forTailRevOrigT bt fuel var b vlo (.val w) m = .ret r ∧ IsErr r.1 := by
  cases w <;> simp [Value.isControlFlow] at hw
  right
  cases vlo <;> exact ⟨_, rfl, _, rfl⟩

/-- The tail of `forFoldRev` passes non-values. -/
theorem forTailFoldRevT_other (var : String) (b : ImpExpr) (vlo : Value) (o : Outcome)
    (m : Env) (h : ∀ w, o ≠ .val w) : forTailFoldRevT bt fuel var b vlo o m = .ret (o, m) := by
  cases o with
  | val w => exact absurd rfl (h w)
  | _ => cases vlo <;> rfl

/-- The tail of `forFoldRev` returns a control-flow upper bound. -/
theorem forTailFoldRevT_cf (var : String) (b : ImpExpr) (vlo w : Value) (m : Env)
    (hw : w.isControlFlow = true) :
    forTailFoldRevT bt fuel var b vlo (.val w) m = .ret (.val w, m) ∨
      ∃ r, forTailFoldRevT bt fuel var b vlo (.val w) m = .ret r ∧ IsErr r.1 := by
  cases w <;> simp [Value.isControlFlow] at hw
  left
  cases vlo <;> rfl

/-- The conditional tail passes non-values. -/
theorem iteTailT_other (t e : ImpExpr) (o : Outcome) (m : Env) (h : ∀ w, o ≠ .val w) :
    iteTailT bt fuel t e o m = .ret (o, m) := by
  cases o with
  | val w => exact absurd rfl (h w)
  | _ => rfl

/-- The conditional tail returns a control-flow condition. -/
theorem iteTailT_cf (t e : ImpExpr) (w : Value) (m : Env) (hw : w.isControlFlow = true) :
    iteTailT bt fuel t e (.val w) m = .ret (.val w, m) ∨
      ∃ r, iteTailT bt fuel t e (.val w) m = .ret r ∧ IsErr r.1 := by
  cases w <;> simp [Value.isControlFlow] at hw
  exact Or.inl rfl

end TailRel

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeANorm
