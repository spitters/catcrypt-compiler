/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeInlineSpinePure

/-!
# Inlining the closures of the statement spine at the level of call trees

The theorems `denote'_frame`, `denote'_body`, `callBlock_rel`, `denote'_inlineBlocks` and
`denote'_inlineSpine` of `InlineLocalClosures` at the level of call trees: the call tree of the
reference reading `denoteSpineT` of a function body is related to the call tree of the reading of
`inlineSpine` of the body by `RuttS` at equal events and answers, an error leaf of the reference
reading being a failed leaf. The arguments of a call of a pure closure are substituted into its
body, so a call in an argument is performed once per read of its parameter, in the order of the
body; the relation holds when the inlined pure closures have calls whose arguments have no calls
(`spineArgsOk`).

## Main definitions

* `spineArgsOk`: the inlined pure closures of the spine have calls with arguments without calls.

## Main results

* `denoteT_frame`: an expression read through a renaming of its reads is related to itself from
  environments related so that each read agrees.
* `denoteT_inlineBlocks`: the call trees of a continuation and of `inlineBlocks` of it are related.
* `inlineSpine_relT_gen`, `inlineSpine_relT`: the call trees of `denoteSpineT bt fuel e` and of
  `inlineSpine e` read at `bt` are related, the final environments agreeing off `spineW e`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeInlineSpine

open _root_.Hax
open _root_.Hax.InlineLocalClosures
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeRepeatCount (tm_bind_run tm_pure_run
  denoteT_lit_run denoteT_var_run denoteT_var_run_none)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick (bind_assoc)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeWhileTrue (lift_bind_run)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)

variable {E : EventSig} {h₁ : ∀ e : E.Event, E.Resp e}

/-! ## The frame of an expression -/

section Frame

variable {R : Env → Env → Prop} {bt₁ bt₂ : TreeTable E} (σ : String → String)
  (rd bd ok : String → Bool)

/-- **The frame of an expression.** Let `R` relate environments so that a variable `x` with
    `rd x` reads in the right environment what `σ x` reads in the left one, and so that extending
    both at a name with `bd` by one value keeps `R`; let `bt₁` and `bt₂` agree on the names with
    `ok`. For `e` in `frameOk rd bd ok`, the call tree of `e` read with `bt₂` is related to the
    call tree of `renameReads σ e` read with `bt₁` from `R`-related environments. -/
theorem denoteT_frame
    (hrd : ∀ e₁ e₂ x, R e₁ e₂ → rd x = true → e₁ (σ x) = e₂ x)
    (hbd : ∀ e₁ e₂ n w, R e₁ e₂ → bd n = true → R (e₁.extend n w) (e₂.extend n w))
    (hok : ∀ g, ok g = true → bt₁ g = bt₂ g) (e : ImpExpr) :
    frameOk rd bd ok e = true → ∀ fuel,
      RelT h₁ R R IsErr (denoteT bt₁ fuel (renameReads σ e)) (denoteT bt₂ fuel e) := by
  have ext : ∀ n, bd n = true → ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend n w) (e₂.extend n w) :=
    fun n hn e₁ e₂ w h => hbd e₁ e₂ n w h hn
  induction e using ImpExpr.ind with
  | var x =>
    intro hK fuel e₁ e₂ hR
    simp only [frameOk] at hK
    simp only [renameReads]
    rw [denoteT_var_eq, denoteT_var_eq, hrd e₁ e₂ x hR hK]
    rcases e₂ x with _ | v
    · exact .fail ⟨_, rfl⟩
    · exact .ret ⟨rfl, hR⟩
  | app g args ih =>
    intro hK fuel
    simp only [frameOk, frameOk.okList_eq, Bool.and_eq_true, List.all_eq_true] at hK
    have ih' := fun a ha => ih a ha (hK.2 a ha)
    simp only [renameReads, renameReads.mapE_eq, denoteT]
    unfold denoteAppT
    refine RelT.bind (badα := fun o => o = none) (argsT_rel _ args fuel fun a ha => ih' a ha fuel)
      (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, _, rfl, _, rfl⟩)
    rw [hok g hK.1]
    split
    · exact RelT.bind_lift _ fun r => by split <;> exact RelT.pure _
    · exact absurd rfl hr
  | tuple es ih =>
    intro hK fuel
    simp only [frameOk, frameOk.okList_eq, List.all_eq_true] at hK
    have ih' := fun a ha => ih a ha (hK a ha)
    simp only [renameReads, renameReads.mapE_eq, denoteT]
    refine RelT.bind (badα := fun o => o = none) (argsT_rel _ es fuel fun a ha => ih' a ha fuel)
      (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, _, rfl, _, rfl⟩)
    split <;> exact RelT.pure _
  | match_ scrut arms _ _ => intro hK; simp [frameOk] at hK
  | lam qs b _ =>
    intro _ fuel
    exact RelT.of_bad fun _ => by rw [denoteT]; exact ⟨_, _, rfl, _, rfl⟩
  | forLoop v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := forLoopOrigT_rel (bt₁ := bt₁) (ext v hK.1.1.1) (ihb hK.2)
    simp only [renameReads, denoteT]
    relt_step
  | forLoopRev v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := forLoopRevOrigT_rel (bt₁ := bt₁) (ext v hK.1.1.1) (ihb hK.2)
    simp only [renameReads, denoteT]
    relt_step
  | forFold v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := forLoopT_rel (bt₁ := bt₁) (ext v hK.1.1.1) (ihb hK.2)
    simp only [renameReads, denoteT]
    relt_step
  | forFoldRev v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := forLoopRevT_rel (bt₁ := bt₁) (ext v hK.1.1.1) (ihb hK.2)
    simp only [renameReads, denoteT]
    relt_step
  | forFoldReturn v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := forLoopReturnT_rel (bt₁ := bt₁) (ext v hK.1.1.1) (ihb hK.2)
    simp only [renameReads, denoteT]
    relt_step
  | forFoldRevReturn v lo hi b ihl ihh ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hl := ihl hK.1.1.2
    have hh := ihh hK.1.2
    have := forLoopRevReturnT_rel (bt₁ := bt₁) (ext v hK.1.1.1) (ihb hK.2)
    simp only [renameReads, denoteT]
    relt_step
  | whileLoop c b ihc ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    simp only [renameReads, denoteT]
    exact whileOrigT_rel (ihc hK.1) (ihb hK.2) fuel
  | whileFold c b ihc ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    simp only [renameReads, denoteT]
    exact whileT_rel (ihc hK.1) (ihb hK.2) fuel
  | whileFoldReturn c b ihc ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    simp only [renameReads, denoteT]
    exact whileReturnT_rel (ihc hK.1) (ihb hK.2) fuel
  | letBind n v b ihv ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hn := ext n hK.1.1
    have hv := ihv hK.1.2
    have hb := ihb hK.2
    simp only [renameReads, denoteT]
    relt_step
  | assign n rhs ih =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have hn := ext n hK.1
    have hr := ih hK.2
    simp only [renameReads, denoteT]
    relt_step
  | seq a b iha ihb =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have ha := iha hK.1
    have hb := ihb hK.2
    simp only [renameReads, denoteT]
    relt_step
  | ifThenElse c t e ihc iht ihe =>
    intro hK fuel
    simp only [frameOk, Bool.and_eq_true] at hK
    have h1 := ihc hK.1.1
    have h2 := iht hK.1.2
    have h3 := ihe hK.2
    simp only [renameReads, denoteT]
    relt_step
  | proj e _ ih | borrow e ih | deref e ih | break_some e ih | earlyReturn e ih
  | questionMark e ih | cfBreak e ih | cfContinue e ih | cfBreakContinue e ih
  | typeAscription e _ ih =>
    intro hK fuel
    simp only [frameOk] at hK
    have h := ih hK
    simp only [renameReads, denoteT]
    relt_step
  | _ =>
    intro _ fuel
    simp only [renameReads, denoteT]
    relt_step


end Frame

/-! ## A run of the body of a statement closure -/

section Body

variable {σ : String → String} {W ps : List String} {Ev : Env}

/-- **A run of the body.** For a body in `bodyOk W ps D`, the call tree of the body read with
    `bt` is related to the call tree of the renamed body read with `bt` from environments related
    by `BodyRel`, and the left run ends in an environment agreeing with `Ev` off `W`. -/
theorem denoteT_body (bt : TreeTable E) (hσ : ∀ x, σ x = x ∨ W.contains (σ x) = false)
    (hσps : ∀ x, ps.contains x = false → σ x = x) (body : ImpExpr) :
    ∀ D, bodyOk W ps D body = true → ∀ fuel,
      RelT h₁ (BodyRel σ W D Ev) (fun s₁ _ => ∀ x, W.contains x = false → s₁ x = Ev x) IsErr
        (denoteT bt fuel (renameReads σ body)) (denoteT bt fuel body) := by
  have frame : ∀ D e, frameOk D.contains (bodyBd W ps) (fun _ => true) e = true → ∀ fuel,
      RelT h₁ (BodyRel σ W D Ev) (fun s₁ _ => ∀ x, W.contains x = false → s₁ x = Ev x) IsErr
        (denoteT bt fuel (renameReads σ e)) (denoteT bt fuel e) := fun D e h fuel =>
    (denoteT_frame (bt₁ := bt) (bt₂ := bt) σ D.contains (bodyBd W ps) (fun _ => true)
      (fun _ _ x hR hx => hR.1 x hx)
      (fun _ _ n w hR hn => (hR.extend_cons hσ hσps hn w).of_cons)
      (fun _ _ => rfl) e h fuel).mono (fun _ _ h => h) (fun _ _ h => h.2)
  intro D h fuel
  induction body using ImpExpr.ind generalizing D with
  | letBind n v b _ ihb =>
    simp only [bodyOk, Bool.and_eq_true] at h
    have hv : RelT h₁ (BodyRel σ W D Ev) (BodyRel σ W D Ev) IsErr
        (denoteT bt fuel (renameReads σ v)) (denoteT bt fuel v) :=
      denoteT_frame σ D.contains (bodyBd W ps) (fun _ => true)
        (fun _ _ x hR hx => hR.1 x hx)
        (fun _ _ n w hR hn => (hR.extend_cons hσ hσps hn w).of_cons)
        (fun _ _ => rfl) v h.1.1 fuel
    simp only [renameReads, denoteT]
    refine RelT.bind (badα := IsErr) hv (fun o ho => ?_)
      (fun a ha s => by obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨_, _, rfl, m, rfl⟩)
    split
    · exact RelT.pure_mono _ fun _ _ (hR : BodyRel σ W D Ev _ _) => hR.2
    · exact RelT.modify_mono (fun _ _ hR => hR.extend_cons hσ hσps h.1.2 _)
        (fun _ => ihb (n :: D) h.2)
    · exact RelT.pure_mono _ fun _ _ (hR : BodyRel σ W D Ev _ _) => hR.2
  | _ => exact frame D _ (by simpa only [bodyOk] using h) fuel

end Body

/-! ## Statement closures -/

/-- Binding the literal arguments over `b` reads as `b` from the environment extended by them. -/
theorem bindArgs_runT (bt : TreeTable E) (fuel : Nat) (b : ImpExpr) :
    ∀ (ps : List String) (args : List ImpExpr) (e : Env),
      denoteT bt fuel (bindArgs ps args b) e = denoteT bt fuel b (bindLits ps args e)
  | [], _, _ => by simp only [bindArgs, bindLits]
  | _ :: _, [], _ => by simp only [bindArgs, bindLits]
  | p :: ps, a :: as, e => by
    cases a
    case lit l =>
      simp only [bindArgs, bindLits]
      rw [NFCallTreeAnfPick.denoteT_letBind_run', denoteT_lit_run]
      cases l <;> exact bindArgs_runT bt fuel b ps as _
    all_goals (simp only [bindArgs, bindLits]; exact bindArgs_runT bt fuel b ps as e)

section Blocks

variable (bt : TreeTable E) (fuel₀ : Nat) (f : String) (ps : List String) (body : ImpExpr)
  (ρ : Env) {W K : List String}

/-- **A call of a statement closure.** From environments related by `ContRel`, the call tree of
    a call of `f` on atoms reading no variable of `W` under the closure table is related to the
    call tree of the call block, a leaf that is an error being a failed leaf and the final
    environments related by `ContRel`. -/
theorem callBlockT_rel (hW : ∀ p, p ∈ ps → W.contains p = true)
    (hKW : ∀ x, x ∈ K → W.contains x = false) (hnd : ps.Nodup)
    (hbody : bodyOk W ps (ps ++ K) body = true) (args : List ImpExpr)
    (hat : ∀ a, a ∈ args → isAtom a = true ∧
      frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun _ => true) a = true) :
    RelT h₁ (ContRel W K ρ) (ContRel W K ρ) IsErr
      (denoteT bt fuel₀ (inlineBlocks f ps body (.app f args)))
      (denoteT (closureTableT bt fuel₀ f ps body ρ) fuel₀ (.app f args)) := by
  have hnc : ∀ a, a ∈ args → noCalls a = true := fun a ha => by
    have := (hat a ha).1
    cases a <;> simp_all [isAtom, noCalls]
  by_cases hl : args.length = ps.length
  case neg =>
    simp only [inlineBlocks, hl, and_false, ite_false]
    exact RelT.of_bad (callT_arity_err bt fuel₀ f ps body ρ args hnc hl fuel₀)
  simp only [inlineBlocks, hl, and_self, ite_true, callBlock]
  intro e₁ e₂ hR
  obtain ⟨ov, hov⟩ := noCallsArgs_aux e₂ args (fun a ha => noCalls_runT a (hnc a ha) e₂)
  rw [denoteT, denoteAppT, tm_bind_run, hov]
  rcases ov with _ | vals
  · exact .fail ⟨_, rfl⟩
  obtain ⟨-, hvlen, hz⟩ := noCallsArgs_vals bt fuel₀ e₂ args vals e₂ hnc (hov bt fuel₀)
  have hvl : vals.length = ps.length := hvlen.trans hl
  have hy : ∀ y, ImpExpr.var y ∈ args → W.contains y = false := fun y hy' => by
    simpa [frameOk] using (hat _ hy').2
  have hzv : ∀ av, av ∈ args.zip vals → atomVal e₁ av.1 = some av.2 := by
    intro av hav
    have hmem := (List.of_mem_zip hav).1
    have hrun := hz av hav bt fuel₀
    have ha := (hat _ hmem).1
    obtain ⟨a, v⟩ := av
    cases a with
    | var y =>
      rw [denoteT_var_eq] at hrun
      simp only [atomVal]
      rw [hR.1 y (hy y hmem)]
      cases h : e₂ y with
      | none => simp only [h, Option.elim] at hrun; cases hrun
      | some u =>
        simp only [h, Option.elim, CallTree.ret.injEq, Prod.mk.injEq, Outcome.val.injEq] at hrun
        rw [hrun.1]
    | lit l =>
      rw [denoteT_lit_run] at hrun
      simp only [CallTree.ret.injEq, Prod.mk.injEq, Outcome.val.injEq] at hrun
      simp only [atomVal, hrun.1]
    | _ => simp [isAtom] at ha
  have hσps : ∀ x, ps.contains x = false → argRen ps args x = x := fun x hx => by
    simp only [argRen, argFor_none x ps args (by simpa using hx)]
  have hσ : ∀ x, argRen ps args x = x ∨ W.contains (argRen ps args x) = false := by
    intro x
    simp only [argRen]
    split
    · rename_i y hy'
      exact Or.inr (hy y (argFor_mem x ps args _ hy'))
    · exact Or.inl rfl
  have hpre : BodyRel (argRen ps args) W (ps ++ K) e₁ (bindLits ps args e₁)
      (bindAll ρ ps vals) := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [List.contains_append, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · exact bindLits_param ρ ps args vals e₁ hnd hl hvl (fun a ha => (hat a ha).1)
          (fun y hy' hyp => by have := hW y hyp; rw [hy y hy'] at this; cases this) hzv x
          (by simpa using hx)
      · have hxK : x ∈ K := by simpa using hx
        have hxW := hKW x hxK
        have hxps : x ∉ ps := fun h => by rw [hW x h] at hxW; cases hxW
        rw [hσps x (by simpa using hxps), bindLits_other x ps args e₁ hxps, hR.1 x hxW,
          hR.2 x hxK, bindAll_other ρ x ps vals hxps]
    · have hxps : x ∉ ps := fun h => by rw [hW x h] at hx; cases hx
      exact bindLits_other x ps args e₁ hxps
  have hb := denoteT_body (h₁ := h₁) (Ev := e₁) bt hσ hσps body (ps ++ K) hbody fuel₀ _ _ hpre
  dsimp only [CallTree.bind]
  rw [lift_bind_run, bindArgs_runT]
  simp only [closureTableT, ite_true, hvl, bind_assoc]
  rw [← NFCallTreeAnfPick.bind_ret (denoteT bt fuel₀ (renameReads (argRen ps args) body)
    (bindLits ps args e₁))]
  refine NFProgCallTree.RuttS.bind hb (fun r₁ r₂ hr => ?_) (fun r₁ hf t => ?_)
  · obtain ⟨o, s₂⟩ := r₁
    obtain ⟨o', s₁⟩ := r₂
    obtain ⟨ho, hpost⟩ := hr
    dsimp only at ho hpost
    subst ho
    rcases o' with w | _ | _ | _ | _
    · exact .ret ⟨rfl, fun x hx => (hpost x hx).trans (hR.1 x hx), hR.2⟩
    all_goals exact .fail ⟨_, rfl⟩
  · obtain ⟨o, s₂⟩ := r₁
    obtain ⟨m, hm⟩ := hf
    dsimp only at hm
    subst hm
    exact .fail ⟨_, rfl⟩

/-- **Inlining a statement closure.** Let `W` contain the parameters, `K` be disjoint from `W`,
    the parameters be distinct and the body be in `bodyOk W ps (ps ++ K)`. For a continuation in
    `contOk`, reading no variable of `W` and binding none of `K`, the call tree of `e` read with
    the closure table of `f` defined in `ρ` is related to the call tree of
    `inlineBlocks f ps body e` read with `bt`, at the fuel of the table, from environments related
    by `ContRel W K ρ`. -/
theorem denoteT_inlineBlocks (hW : ∀ p, p ∈ ps → W.contains p = true)
    (hKW : ∀ x, x ∈ K → W.contains x = false) (hnd : ps.Nodup)
    (hbody : bodyOk W ps (ps ++ K) body = true) (e : ImpExpr) :
    contOk f (fun x => !W.contains x) (fun n => !K.contains n) e = true →
      RelT h₁ (ContRel W K ρ) (ContRel W K ρ) IsErr
        (denoteT bt fuel₀ (inlineBlocks f ps body e))
        (denoteT (closureTableT bt fuel₀ f ps body ρ) fuel₀ e) := by
  have hrd : ∀ e₁ e₂ x, ContRel W K ρ e₁ e₂ → (!W.contains x) = true → e₁ (id x) = e₂ x :=
    fun _ _ x h hx => h.1 x (by simpa using hx)
  have hbd : ∀ e₁ e₂ n w, ContRel W K ρ e₁ e₂ → (!K.contains n) = true →
      ContRel W K ρ (e₁.extend n w) (e₂.extend n w) := by
    intro e₁ e₂ n w h hn
    refine ⟨fun x hx => ?_, Agree.extend h.2 (by simpa using hn) w⟩
    by_cases hxn : x = n
    · subst hxn; simp
    · rw [Env.extend_other _ _ _ _ hxn, Env.extend_other _ _ _ _ hxn]; exact h.1 x hx
  have hok : ∀ g, (g != f) = true → bt g = closureTableT bt fuel₀ f ps body ρ g := fun g hg => by
    have hgf : g ≠ f := by simpa using hg
    funext vals; simp [closureTableT, hgf]
  have free : ∀ e, frameOk (fun x => !W.contains x) (fun n => !K.contains n)
      (fun g => g != f) e = true →
      RelT h₁ (ContRel W K ρ) (ContRel W K ρ) IsErr (denoteT bt fuel₀ (inlineBlocks f ps body e))
        (denoteT (closureTableT bt fuel₀ f ps body ρ) fuel₀ e) := by
    intro e h
    rw [inlineBlocks_free f ps body e
      (frameOk_mono (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h) e h)]
    have := denoteT_frame (h₁ := h₁) (bt₁ := bt) (bt₂ := closureTableT bt fuel₀ f ps body ρ) id
      _ _ _
      hrd hbd hok e h fuel₀
    rwa [renameReads_id e (frameOk_mono (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) e h)]
      at this
  have ext : ∀ n, (!K.contains n) = true → ∀ e₁ e₂ w, ContRel W K ρ e₁ e₂ →
      ContRel W K ρ (e₁.extend n w) (e₂.extend n w) := fun n hn e₁ e₂ w h => hbd e₁ e₂ n w h hn
  induction e using ImpExpr.ind with
  | app g args ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.app g args)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    by_cases hgf : g = f
    · subst hgf
      simp only [ite_true, List.all_eq_true, Bool.and_eq_true] at h
      exact callBlockT_rel bt fuel₀ g ps body ρ hW hKW hnd hbody args h
    · simp only [hgf, ite_false, contOk.contOkList_eq, List.all_eq_true] at h
      have ih' := fun a ha => ih a ha (h a ha)
      simp only [inlineBlocks, hgf, false_and, ite_false, inlineBlocks.mapExpr_eq, denoteT]
      unfold denoteAppT
      refine RelT.bind (badα := fun o => o = none) (argsT_rel _ args fuel₀ ih')
        (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, _, rfl, _, rfl⟩)
      rw [← hok g (by simpa using hgf)]
      split
      · exact RelT.bind_lift _ fun r => by split <;> exact RelT.pure _
      · exact absurd rfl hr
  | tuple es ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.tuple es)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or, contOk.contOkList_eq, List.all_eq_true] at h
    have ih' := fun a ha => ih a ha (h a ha)
    simp only [inlineBlocks, inlineBlocks.mapExpr_eq, denoteT]
    refine RelT.bind (badα := fun o => o = none) (argsT_rel _ es fuel₀ ih')
      (fun r hr => ?_) (fun r hr s => by subst hr; exact ⟨_, _, rfl, _, rfl⟩)
    split <;> exact RelT.pure _
  | letBind n v b ihv ihb =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.letBind n v b)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or, Bool.and_eq_true] at h
    have hn := ext n h.1.1
    have hv := ihv h.1.2
    have hb := ihb h.2
    simp only [inlineBlocks, denoteT]
    relt_step
  | assign n rhs ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.assign n rhs)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or, Bool.and_eq_true] at h
    have hn := ext n h.1
    have hr := ih h.2
    simp only [inlineBlocks, denoteT]
    relt_step
  | seq a b iha ihb =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.seq a b)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or, Bool.and_eq_true] at h
    have ha := iha h.1
    have hb := ihb h.2
    simp only [inlineBlocks, denoteT]
    relt_step
  | ifThenElse c t e ihc iht ihe =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.ifThenElse c t e)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or, Bool.and_eq_true] at h
    have h1 := ihc h.1.1
    have h2 := iht h.1.2
    have h3 := ihe h.2
    simp only [inlineBlocks, denoteT]
    relt_step
  | proj e i ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.proj e i)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denoteT]
    relt_step
  | borrow e ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.borrow e)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denoteT]
    relt_step
  | deref e ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.deref e)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denoteT]
    relt_step
  | break_some e ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.break_ (some e))
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denoteT]
    relt_step
  | earlyReturn e ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.earlyReturn e)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denoteT]
    relt_step
  | questionMark e ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.questionMark e)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denoteT]
    relt_step
  | cfBreak e ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.cfBreak e)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denoteT]
    relt_step
  | cfContinue e ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.cfContinue e)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denoteT]
    relt_step
  | cfBreakContinue e ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.cfBreakContinue e)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denoteT]
    relt_step
  | typeAscription e ty ih =>
    intro h
    cases hfr : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
      (.typeAscription e ty)
    case true => exact free _ hfr
    simp only [contOk, hfr, Bool.false_or] at h
    have h' := ih h
    simp only [inlineBlocks, denoteT]
    relt_step
  | _ => intro h; exact free _ (by simpa only [contOk] using h)

end Blocks

/-! ## The statement spine -/

/-- Every binding of a pure closure on the statement spine that `inlineSpine` inlines has
    calls whose arguments have no calls, in the continuation with the inner bindings inlined. -/
def spineArgsOk : ImpExpr → Bool
  | .letBind f (.lam ps body) cont =>
    (!closureOk f ps body (inlineSpine cont) || argsFree f (inlineSpine cont)) && spineArgsOk cont
  | .letBind _ _ cont => spineArgsOk cont
  | .seq _ b => spineArgsOk b
  | _ => true

/-- The reading of a binding of a closure is an error leaf. -/
theorem denoteT_letBind_lam_run (bt : TreeTable E) (fuel : Nat) (f : String) (ps : List String)
    (body cont : ImpExpr) (env : Env) :
    denoteT bt fuel (.letBind f (.lam ps body) cont) env =
      .ret (.err "closures are not evaluated by the reference semantics", env) := by
  rw [NFCallTreeAnfPick.denoteT_letBind_run', denoteT]
  rfl

/-- **The spine, from related environments.** For `e` whose inlined pure closures have calls
    with arguments without calls (`spineArgsOk`), from equal environments, the call tree of the
    reference reading `denoteSpineT bt fuel e` is related to the call tree of `inlineSpine e` read
    with `bt`: a leaf that is an error is a failed leaf, and every other leaf is matched by a leaf
    with the same outcome whose environment agrees off `spineW e`. -/
theorem inlineSpine_relT_gen (e : ImpExpr) (hs : spineArgsOk e = true) :
    ∀ (bt : TreeTable E) (fuel : Nat),
      RelT h₁ (fun e₁ e₂ => e₁ = e₂) (EqOff (spineW e)) IsErr
        (denoteT bt fuel (inlineSpine e)) (denoteSpineT bt fuel e) := by
  induction e using ImpExpr.ind with
  | letBind x v cont ihv ihc =>
    intro bt fuel
    clear ihv
    cases v
    case lam ps body =>
      simp only [spineArgsOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hs
      simp only [inlineSpine, denoteSpineT, spineW]
      cases hp : closureOk x ps body (inlineSpine cont)
      case true =>
        simp only [ite_true, Bool.true_or]
        have hargs : argsFree x (inlineSpine cont) = true := hs.1.resolve_left (by simp [hp])
        intro env _ heq
        subst heq
        have h01 := ihc hs.2 (closureTableT bt fuel x ps body env) fuel env env rfl
        simp only [closureOk, Bool.and_eq_true] at hp
        have h12 := denoteT_inlineCalls (h₁ := h₁) bt fuel x ps body env hp.1.1 (inlineSpine cont)
          hp.2 hargs fuel env env ⟨rfl, fun _ _ => rfl⟩
        refine NFProgCallTreeExt.RuttS.mono ?_ (NFProgCallTreeFlat.ruttS_eqTrans
          (fun r₀ r₁ h hf => by rw [← h.1]; exact hf) h01 h12)
        rintro r₀ r₂ ⟨r₁, ⟨h1, hQ⟩, ⟨h2, hA⟩⟩
        exact ⟨h2.trans h1, fun y hy => (congrFun hA.1 y).trans (hQ y hy)⟩
      cases hb : blockOk x ps body (inlineSpine cont)
      case false =>
        simp only [Bool.false_or, Bool.false_eq_true, ite_false]
        exact RelT.of_bad fun env => ⟨_, _, denoteT_letBind_lam_run bt fuel x ps body cont env,
          _, rfl⟩
      simp only [Bool.false_or, Bool.false_eq_true, ite_false, ite_true]
      intro env _ heq
      subst heq
      have h01 := ihc hs.2 (closureTableT bt fuel x ps body env) fuel env env rfl
      simp only [blockOk, Bool.and_eq_true, decide_eq_true_eq] at hb
      have h12 := denoteT_inlineBlocks (h₁ := h₁) bt fuel x ps body env
        (fun p hp' => by simp [blockW, hp'])
        (fun y hy => by simp only [blockK, List.mem_filter] at hy; simpa using hy.2)
        hb.1.1 hb.1.2 (inlineSpine cont) hb.2 env env ⟨fun _ _ => rfl, fun _ _ => rfl⟩
      refine NFProgCallTreeExt.RuttS.mono ?_ (NFProgCallTreeFlat.ruttS_eqTrans
        (fun r₀ r₁ h hf => by rw [← h.1]; exact hf) h01 h12)
      rintro r₀ r₂ ⟨r₁, ⟨h1, hQ⟩, ⟨h2, hR⟩⟩
      refine ⟨h2.trans h1, fun y hy => ?_⟩
      simp only [List.contains_append, Bool.or_eq_false_iff] at hy
      exact (hR.1 y hy.1).trans (hQ y hy.2)
    all_goals
      simp only [spineArgsOk] at hs
      simp only [inlineSpine, spineW]
      rw [denoteT]
      simp only [denoteSpineT]
      refine RelT.bind (badα := IsErr) (RelT.refl _) (fun o _ => ?_)
        (fun a ha s => by obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨_, _, rfl, m, rfl⟩)
      rcases o with w | _ | _ | _ | _
      · cases w <;> dsimp only <;> first
          | exact RelT.pure_mono _ (fun _ _ h => EqOff.of_eq _ _ _ h)
          | exact RelT.modify_mono (P := fun e₁ e₂ => e₁ = e₂) (Q := fun e₁ e₂ => e₁ = e₂)
              (fun _ _ h => by rw [h]) (fun _ => ihc hs bt fuel)
      all_goals (dsimp only; exact RelT.pure_mono _ (fun _ _ h => EqOff.of_eq _ _ _ h))
  | seq a b _ ihb =>
    intro bt fuel
    simp only [spineArgsOk] at hs
    simp only [inlineSpine, spineW]
    rw [denoteT]
    simp only [denoteSpineT]
    refine RelT.bind (badα := IsErr) (RelT.refl _) (fun o _ => ?_)
      (fun a ha s => by obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨_, _, rfl, m, rfl⟩)
    rcases o with w | _ | _ | _ | _
    · cases w <;> dsimp only <;> first
        | exact RelT.pure_mono _ (fun _ _ h => EqOff.of_eq _ _ _ h)
        | exact ihb hs bt fuel
    all_goals (dsimp only; exact RelT.pure_mono _ (fun _ _ h => EqOff.of_eq _ _ _ h))
  | _ =>
    intro bt fuel
    simp only [inlineSpine, denoteSpineT, spineW]
    exact (RelT.refl _).mono (fun _ _ h => h) (fun _ _ h => EqOff.of_eq _ _ _ h)

/-- **Inlining the closures of the statement spine at the level of call trees.** For `e` whose
    inlined pure closures have calls with arguments without calls, from one environment, the call
    tree of the reference reading `denoteSpineT bt fuel e` is related to the call tree of
    `inlineSpine e` read with `bt` by `RuttS` at equal events and answers: a leaf that is an error
    is a failed leaf, and every other leaf is matched by a leaf with the same outcome whose
    environment agrees off `spineW e`. -/
theorem inlineSpine_relT (h₁ : ∀ e : E.Event, E.Resp e) (bt : TreeTable E) (e : ImpExpr)
    (fuel : Nat) (env : Env) (hs : spineArgsOk e = true) :
    RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
      (fun r₁ r₂ => r₂.1 = r₁.1 ∧ EqOff (spineW e) r₂.2 r₁.2)
      (fun r => IsErr r.1)
      (denoteSpineT bt fuel e env) (denoteT bt fuel (inlineSpine e) env) :=
  inlineSpine_relT_gen (h₁ := h₁) e hs bt fuel env env rfl

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeInlineSpine
