/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick
public import HaxLean.Phase.InlineMapClosure

/-!
# `map` over a closure literal at the level of call trees

The front rewrites a binding `let y = collect(map(iter(src), |p| body)); k` on the statement
spine to a counted loop, its source first bound to a variable when it is not one
(`inlineMapClosures`). The reading `denoteT` does not evaluate closures: on such a binding it
reads `src`, calls `iter` on its value, and errs on the closure. So from every environment the
reading of `e` is related to the reading of `inlineMapClosures e` by `RuttS` at equal events and
answers and equal leaves, the error leaves of `e` failed: the two trees agree up to the first
`map` site of the spine, where both read `src` alike and the source then answers the events of
`iter` by the source handler and errs.

## Main results

* `SrcFails`: a source tree related to every target tree, its events answered by the source
  handler up to a failed leaf.
* `srcFails_mapSite`: after the source of a `map` site, the reading of the binding fails.
* `inlineMapClosures_relT`: the call trees of `e` and of `inlineMapClosures e` are related.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeMapClosure

open _root_.Hax
open _root_.Hax.InlineLocalClosures (IsErr)
open _root_.Hax.InlineMap (mapSrc? mapSite? mapS nameMapSources inlineMaps inlineMapClosures
  mapOk mapStmt mapI mapX mapN)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeRepeatCount (tm_bind_run tm_pure_run)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick (bind_assoc bind_ret denoteT_seq_run
  denoteT_letBind_run' ruttS_bind_same)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)

variable {E : EventSig} (h₁ : ∀ e : E.Event, E.Resp e)

/-- The relation of the stage: equal events and answers, equal leaves, the error leaves of the
    source failed. -/
abbrev MapRel (t₁ t₂ : CallTree E (Outcome × Env)) : Prop :=
  RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) (fun r₁ r₂ => r₂ = r₁)
    (fun r => IsErr r.1) t₁ t₂

/-- **A failing source tree**: related to every target tree, its events answered by the source
    handler up to a failed leaf. -/
def SrcFails (t : CallTree E (Outcome × Env)) : Prop := ∀ t₂, MapRel h₁ t t₂

variable {h₁}

/-- An error leaf fails. -/
theorem srcFails_err (m : String) (s : Env) : SrcFails h₁ (.ret (.err m, s)) :=
  fun _ => .fail ⟨m, rfl⟩

/-- A sequence fails when its continuation at the interpretation of the prefix fails. -/
theorem srcFails_bind {S : Type} (t : CallTree E S) {k : S → CallTree E (Outcome × Env)}
    (h : SrcFails h₁ (k (interp h₁ t))) : SrcFails h₁ (t.bind k) :=
  fun t₂ => NFProgCallTree.RuttS.skip_bind t (h t₂)

/-- **Every leaf of a tree satisfies `P`.** -/
inductive LeavesP {R : Type} (P : R → Prop) : CallTree E R → Prop
  | ret {r : R} (h : P r) : LeavesP P (.ret r)
  | vis {e : E.Event} {k : E.Resp e → CallTree E R} (h : ∀ a, LeavesP P (k a)) :
      LeavesP P (.vis e k)

/-- Every tree has leaves satisfying the true predicate. -/
theorem leavesP_true {R : Type} (t : CallTree E R) : LeavesP (fun _ => True) t := by
  induction t with
  | ret r => exact .ret trivial
  | vis e k ih => exact .vis ih

/-- The leaves of a sequence satisfy `Q` when the continuation at every leaf of the prefix
    satisfying `P` has leaves satisfying `Q`. -/
theorem LeavesP.bind {S R : Type} {P : S → Prop} {Q : R → Prop} {t : CallTree E S}
    {k : S → CallTree E R} (h : LeavesP P t) (hk : ∀ s, P s → LeavesP Q (k s)) :
    LeavesP Q (t.bind k) := by
  induction h with
  | ret h => exact hk _ h
  | vis _ ih => exact .vis ih

/-- A tree whose leaves are all errors fails. -/
theorem srcFails_of_leaves {t : CallTree E (Outcome × Env)} (h : LeavesP (fun r => IsErr r.1) t) :
    SrcFails h₁ t := by
  induction h with
  | ret h => exact fun _ => .fail h
  | vis _ ih => exact fun t₂ => .skip (ih _ t₂)

/-! ## The reading errs at a `map` site -/

/-- The reading of a closure literal errs. -/
theorem denoteT_lam_run (bt : TreeTable E) (fuel : Nat) (ps : List String) (b : ImpExpr)
    (s : Env) :
    denoteT bt fuel (.lam ps b) s =
      .ret (.err "closures are not evaluated by the reference semantics", s) := by
  rw [denoteT]; rfl

/-- The arguments of a call whose last argument is a closure literal have no values. -/
theorem denoteArgsT_lam_none (bt : TreeTable E) (fuel : Nat) (a : ImpExpr) (ps : List String)
    (b : ImpExpr) (s : Env) :
    LeavesP (fun q : Option (List Value) × Env => q.1 = none)
      (denoteArgsT bt fuel [a, .lam ps b] s) := by
  rw [denoteArgsT, tm_bind_run]
  refine LeavesP.bind (leavesP_true _) fun q _ => ?_
  rcases q with ⟨o, s'⟩
  rcases o with v | _ | _ | _ | _
  · cases v <;> first
      | exact .ret rfl
      | (dsimp only; rw [denoteArgsT, tm_bind_run, tm_bind_run, denoteT_lam_run]; exact .ret rfl)
  all_goals exact .ret rfl

/-- The reading of a call whose arguments have no values errs. -/
theorem denoteT_app_errs (bt : TreeTable E) (fuel : Nat) (f : String) (args : List ImpExpr)
    (s : Env) (h : LeavesP (fun q : Option (List Value) × Env => q.1 = none)
      (denoteArgsT bt fuel args s)) :
    LeavesP (fun r : Outcome × Env => IsErr r.1) (denoteT bt fuel (.app f args) s) := by
  rw [denoteT, denoteAppT, tm_bind_run]
  refine LeavesP.bind h fun q hq => ?_
  rcases q with ⟨o, s'⟩
  dsimp only at hq
  subst hq
  exact .ret ⟨_, rfl⟩

/-- The arguments of a call on one argument whose reading errs have no values. -/
theorem denoteArgsT_err_none (bt : TreeTable E) (fuel : Nat) (x : ImpExpr) (s : Env)
    (h : LeavesP (fun r : Outcome × Env => IsErr r.1) (denoteT bt fuel x s)) :
    LeavesP (fun q : Option (List Value) × Env => q.1 = none) (denoteArgsT bt fuel [x] s) := by
  rw [denoteArgsT, tm_bind_run]
  refine LeavesP.bind h fun q hq => ?_
  rcases q with ⟨o, s'⟩
  obtain ⟨m, hm⟩ := hq
  dsimp only at hm
  subst hm
  exact .ret rfl

/-- **The reading of a `map` site errs**: every leaf of the reading of
    `collect(map(iter(src), |p| body))` is an error. -/
theorem denoteT_mapSite_errs (bt : TreeTable E) (fuel : Nat) (src : ImpExpr) (p : String)
    (body : ImpExpr) (s : Env) :
    LeavesP (fun r : Outcome × Env => IsErr r.1)
      (denoteT bt fuel (.app "collect" [.app "map" [.app "iter" [src], .lam [p] body]]) s) :=
  denoteT_app_errs bt fuel _ _ s (denoteArgsT_err_none bt fuel _ s
    (denoteT_app_errs bt fuel _ _ s (denoteArgsT_lam_none bt fuel _ _ _ s)))

/-- The reading of a binding whose right-hand side errs everywhere errs everywhere. -/
theorem denoteT_letBind_errs (bt : TreeTable E) (fuel : Nat) (y : String) (v k : ImpExpr)
    (s : Env) (h : LeavesP (fun r : Outcome × Env => IsErr r.1) (denoteT bt fuel v s)) :
    LeavesP (fun r : Outcome × Env => IsErr r.1) (denoteT bt fuel (.letBind y v k) s) := by
  rw [denoteT_letBind_run']
  refine LeavesP.bind h fun q hq => ?_
  rcases q with ⟨o, s'⟩
  obtain ⟨m, hm⟩ := hq
  dsimp only at hm
  subst hm
  exact .ret ⟨_, rfl⟩

/-! ## The stage -/

/-- **The call trees of `e` and of `inlineMapClosures e` are related**, from every environment,
    at equal events and answers and equal leaves, the error leaves of `e` failed. -/
theorem inlineMapClosures_relT (bt : TreeTable E) (fuel : Nat) (e : ImpExpr) (env : Env) :
    MapRel h₁ (denoteT bt fuel e env) (denoteT bt fuel (inlineMapClosures e) env) := by
  unfold inlineMapClosures
  induction e using ImpExpr.ind generalizing env with
  | letBind y v k _ ihk =>
    cases hv : mapSrc? v with
    | some t =>
      obtain ⟨src, p, body⟩ := t
      have hv' := CatCrypt.Crypto.Hax.mapSrc?_eq_some hv
      subst hv'
      exact srcFails_of_leaves (denoteT_letBind_errs bt fuel y _ k env
        (denoteT_mapSite_errs bt fuel src p body env)) _
    | none =>
      simp only [nameMapSources, hv, inlineMaps, CatCrypt.Crypto.Hax.mapSite?_eq_none hv]
      rw [denoteT_letBind_run', denoteT_letBind_run']
      refine ruttS_bind_same _ fun q => ?_
      rcases q with ⟨o, e1⟩
      rcases o with w | _ | _ | _ | _
      · cases w <;> first | exact .ret rfl | exact ihk _
      all_goals exact .ret rfl
  | seq a b _ ihb =>
    simp only [nameMapSources, inlineMaps]
    rw [denoteT_seq_run, denoteT_seq_run]
    refine ruttS_bind_same _ fun q => ?_
    rcases q with ⟨o, e1⟩
    rcases o with w | _ | _ | _ | _
    · cases w <;> first | exact .ret rfl | exact ihb _
    all_goals exact .ret rfl
  | _ =>
    simp only [nameMapSources, inlineMaps]
    exact NFProgCallTree.RuttS.refl (RR := fun r₁ r₂ : Outcome × Env => r₂ = r₁) (fun _ => rfl) _

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeMapClosure
