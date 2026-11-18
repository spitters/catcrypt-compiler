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
`inlineSpine` of the body by `RuttSA` at equal events and answers, an error leaf of the reference
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
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRuttSA (RuttSA ruttSA_eqTrans)

variable {E : EventSig} {Sk : (e : E.Event) → E.Resp e → Prop}

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
      RelT Sk R R IsErr (denoteT bt₁ fuel (renameReads σ e)) (denoteT bt₂ fuel e) := by
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
      RelT Sk (BodyRel σ W D Ev) (fun s₁ _ => ∀ x, W.contains x = false → s₁ x = Ev x) IsErr
        (denoteT bt fuel (renameReads σ body)) (denoteT bt fuel body) := by
  have frame : ∀ D e, frameOk D.contains (bodyBd W ps) (fun _ => true) e = true → ∀ fuel,
      RelT Sk (BodyRel σ W D Ev) (fun s₁ _ => ∀ x, W.contains x = false → s₁ x = Ev x) IsErr
        (denoteT bt fuel (renameReads σ e)) (denoteT bt fuel e) := fun D e h fuel =>
    (denoteT_frame (bt₁ := bt) (bt₂ := bt) σ D.contains (bodyBd W ps) (fun _ => true)
      (fun _ _ x hR hx => hR.1 x hx)
      (fun _ _ n w hR hn => (hR.extend_cons hσ hσps hn w).of_cons)
      (fun _ _ => rfl) e h fuel).mono (fun _ _ h => h) (fun _ _ h => h.2)
  intro D h fuel
  induction body using ImpExpr.ind generalizing D with
  | letBind n v b _ ihb =>
    simp only [bodyOk, Bool.and_eq_true] at h
    have hv : RelT Sk (BodyRel σ W D Ev) (BodyRel σ W D Ev) IsErr
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

/-- A pure expression reads as one tree of outcomes with every leaf at the environment it starts
    from. -/
theorem denoteT_pure_atEnv (bt : TreeTable E) (a : ImpExpr) (ha : isPure a = true) (e : Env) :
    ∃ t : CallTree E Outcome, ∀ fuel, denoteT bt fuel a e = atEnv t e := by
  obtain ⟨t, h1, -⟩ := subst_runT bt [] [] e e a ha fun x _ =>
    ⟨_, fun fuel => denoteT_var_eq bt fuel x e, fun fuel => denoteT_var_eq bt fuel x e⟩
  exact ⟨t, h1⟩

/-- A continuation of a tree at an environment reads every leaf at that environment. -/
theorem atEnv_bind_fst {α β : Type} (t : CallTree E α) (env : Env)
    (g : α × Env → CallTree E β) :
    (atEnv t env).bind g = (atEnv t env).bind fun p => g (p.1, env) := by
  rw [atEnv, bind_assoc, bind_assoc]
  rfl

/-- The argument readings over related arguments, followed by continuations related at every list
    of values of the length of the arguments, the source continuation at no list ending in a bad
    leaf. -/
theorem argsT_relK {R S : Env → Env → Prop} {bt₁ bt₂ : TreeTable E} {β : Type} {bad : β → Prop}
    (fuel : Nat) (args : List ImpExpr)
    (ih : ∀ a, a ∈ args → RelT Sk R R IsErr (denoteT bt₁ fuel a) (denoteT bt₂ fuel a))
    (k₁ k₂ : Option (List Value) → TM E β)
    (hk : ∀ vals, vals.length = args.length → RelT Sk R S bad (k₁ (some vals)) (k₂ (some vals)))
    (hb : ∀ s, ∃ b s', k₂ none s = .ret (b, s') ∧ bad b) :
    RelT Sk R S bad (denoteArgsT bt₁ fuel args >>= k₁) (denoteArgsT bt₂ fuel args >>= k₂) := by
  induction args generalizing k₁ k₂ with
  | nil =>
    intro e₁ e₂ hR
    rw [tm_bind_run, tm_bind_run, argsT_nil_run, argsT_nil_run]
    exact hk [] rfl e₁ e₂ hR
  | cons a as iha =>
    intro e₁ e₂ hR
    rw [tm_bind_run, tm_bind_run, argsT_cons_run, argsT_cons_run, bind_assoc, bind_assoc]
    have fl : ∀ s (t : CallTree E (β × Env)), RuttSA Sk (fun e₁ e₂ => e₁ = e₂)
        (fun _ _ a₁ a₂ => a₁ ≍ a₂) (fun r₁ r₂ => r₂.1 = r₁.1 ∧ S r₂.2 r₁.2) (fun r => bad r.1)
        (k₂ none s) t := by
      intro s t
      obtain ⟨b, s', hs, hbb⟩ := hb s
      rw [hs]
      exact .fail hbb
    refine RuttSA.bind
      (RR' := fun (r₁ r₂ : Outcome × Env) => r₂.1 = r₁.1 ∧ R r₂.2 r₁.2)
      (Fail' := fun (r : Outcome × Env) => IsErr r.1) (ih a List.mem_cons_self e₁ e₂ hR)
      (fun r₁ r₂ hr => ?_) (fun r₁ hf t => ?_)
    · obtain ⟨o, s₂⟩ := r₁
      obtain ⟨o', s₁⟩ := r₂
      obtain ⟨ho, hR'⟩ := hr
      dsimp only at ho hR'
      subst ho
      have key : ∀ v : Value, RuttSA Sk (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
          (fun r₁ r₂ => r₂.1 = r₁.1 ∧ S r₂.2 r₁.2) (fun r => bad r.1)
          (((denoteArgsT bt₂ fuel as s₂).bind fun q => .ret (q.1.map (v :: ·), q.2)).bind
            fun p => k₂ p.1 p.2)
          (((denoteArgsT bt₁ fuel as s₁).bind fun q => .ret (q.1.map (v :: ·), q.2)).bind
            fun p => k₁ p.1 p.2) := fun v => by
        have := iha (fun b hb => ih b (List.mem_cons_of_mem a hb))
          (fun ov => k₁ (ov.map (v :: ·))) (fun ov => k₂ (ov.map (v :: ·)))
          (fun vals hl => hk (v :: vals) (by simp [hl])) (fun s => hb s) s₁ s₂ hR'
        rw [tm_bind_run, tm_bind_run] at this
        rw [bind_assoc, bind_assoc]
        exact this
      rcases o' with v | _ | _ | _ | _
      · cases v
        case controlFlow => exact fl _ _
        all_goals exact key _
      all_goals exact fl _ _
    · obtain ⟨o, s₂⟩ := r₁
      obtain ⟨m, hm⟩ := hf
      dsimp only at hm
      subst hm
      exact fl _ _

/-- **The argument bindings of a call block.** Let `bt` and `bt₂` agree off `f`, the parameters lie
    in `W`, and the arguments be pure, read no variable of `W` and call no `f`. From environments
    agreeing off `W`, the arguments read at `bt₂` followed by `k` are related to
    `bindArgs ps args b` read at `bt`, when `k` at no list is a failed leaf and `k` at the values
    of the arguments is related to `b` read from the environment `bindVals` gives: each argument
    tree is performed once on both sides, in the same order. -/
theorem bindArgsT_rel (bt bt₂ : TreeTable E) (f : String) {W K : List String} (fuel : Nat)
    (hok : ∀ g, (g != f) = true → bt g = bt₂ g) (b : ImpExpr)
    {RR : Outcome × Env → Outcome × Env → Prop} {Fail : Outcome × Env → Prop} :
    ∀ (ps : List String) (args : List ImpExpr) (e₁ e₂ : Env)
      (k : Option (List Value) → TM E Outcome),
      (∀ p, p ∈ ps → W.contains p = true) → args.length = ps.length →
      (∀ a, a ∈ args → isPure a = true ∧
        frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f) a = true) →
      (∀ x, W.contains x = false → e₁ x = e₂ x) →
      (∀ s, ∃ r, k none s = .ret r ∧ Fail r) →
      (∀ vals, vals.length = ps.length →
        (∀ av, av ∈ args.zip vals → ∀ y, av.1 = .var y → e₂ y = some av.2) →
        RuttSA Sk (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) RR Fail (k (some vals) e₂)
          (denoteT bt fuel b (bindVals ps args vals e₁))) →
      RuttSA Sk (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) RR Fail
        ((denoteArgsT bt₂ fuel args >>= k) e₂) (denoteT bt fuel (bindArgs ps args b) e₁)
  | [], args, e₁, e₂, k, _, hl, _, _, _, hK => by
    obtain rfl : args = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    rw [tm_bind_run, argsT_nil_run]
    exact hK [] rfl (by simp)
  | _ :: _, [], _, _, _, _, hl, _, _, _, _ => by simp at hl
  | p :: ps, a :: as, e₁, e₂, k, hW, hl, hat, he, hnone, hK => by
    have hW' : ∀ q, q ∈ ps → W.contains q = true := fun q hq => hW q (List.mem_cons_of_mem p hq)
    have hat' := fun c hc => hat c (List.mem_cons_of_mem a hc)
    have hl' : as.length = ps.length := by simpa using hl
    have fl : ∀ s t, RuttSA Sk (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) RR Fail
        (k none s) t := by
      intro s t
      obtain ⟨r, hr, hf⟩ := hnone s
      rw [hr]
      exact .fail hf
    have key : ∀ (v : Value) (e₁' : Env), (∀ x, W.contains x = false → e₁' x = e₂ x) →
        (∀ vals, vals.length = ps.length →
          (∀ av, av ∈ as.zip vals → ∀ y, av.1 = .var y → e₂ y = some av.2) →
          RuttSA Sk (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) RR Fail
            (k (some (v :: vals)) e₂) (denoteT bt fuel b (bindVals ps as vals e₁'))) →
        RuttSA Sk (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂) RR Fail
          (((denoteArgsT bt₂ fuel as e₂).bind fun q => .ret (q.1.map (v :: ·), q.2)).bind
            fun p => k p.1 p.2)
          (denoteT bt fuel (bindArgs ps as b) e₁') := by
      intro v e₁' he' hK'
      have := bindArgsT_rel bt bt₂ f fuel hok b ps as e₁' e₂ (fun ov => k (ov.map (v :: ·)))
        hW' hl' hat' he' (fun s => hnone s) hK'
      rw [tm_bind_run] at this
      rw [bind_assoc]
      exact this
    rw [tm_bind_run, argsT_cons_run, bind_assoc]
    by_cases hav : ∃ y, a = .var y
    · obtain ⟨y, rfl⟩ := hav
      rw [denoteT_var_eq]
      rcases h : e₂ y with _ | v
      · exact fl _ _
      · have hv := key v e₁ he fun vals hvl hz =>
          hK (v :: vals) (by simp [hvl]) fun av hav y' hy' => by
            simp only [List.zip_cons_cons, List.mem_cons] at hav
            rcases hav with rfl | hav
            · obtain rfl : y = y' := by simpa using hy'
              exact h
            · exact hz av hav y' hy'
        cases v
        case controlFlow => exact fl _ _
        all_goals exact hv
    · have hnv : ∀ y, a ≠ .var y := fun y h => hav ⟨y, h⟩
      obtain ⟨hpa, hfa⟩ := hat a List.mem_cons_self
      rw [bindArgs_cons_nonvar p ps a as b hnv, NFCallTreeAnfPick.denoteT_letBind_run']
      obtain ⟨t₁, ht₁⟩ := denoteT_pure_atEnv bt a hpa e₁
      obtain ⟨t₂, ht₂⟩ := denoteT_pure_atEnv bt₂ a hpa e₂
      have hfr := denoteT_frame (Sk := Sk)
        (R := fun s₁ s₂ => ∀ x, W.contains x = false → s₁ x = s₂ x) (bt₁ := bt) (bt₂ := bt₂) id
        (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
        (fun _ _ x h hx => h x (by simpa using hx))
        (fun _ _ n _ h _ z hz => by
          by_cases hzn : z = n
          · subst hzn; simp
          · rw [Env.extend_other _ _ _ _ hzn, Env.extend_other _ _ _ _ hzn]; exact h z hz)
        hok a hfa fuel e₁ e₂ he
      rw [renameReads_id a (frameOk_mono (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) a hfa),
        ht₁, ht₂] at hfr
      rw [ht₁, ht₂, atEnv_bind_fst t₂ e₂, atEnv_bind_fst t₁ e₁]
      refine RuttSA.bind hfr (fun r₁ r₂ hr => ?_) (fun r₁ hf t => ?_)
      · obtain ⟨o, s₂⟩ := r₁
        obtain ⟨o', s₁⟩ := r₂
        obtain ⟨ho, -⟩ := hr
        dsimp only at ho
        subst ho
        rcases o' with v | _ | _ | _ | _
        · have he' : ∀ x, W.contains x = false → (e₁.extend p v) x = e₂ x := fun x hx => by
            have hxp : x ≠ p := fun h => by rw [h, hW p List.mem_cons_self] at hx; cases hx
            rw [Env.extend_other _ _ _ _ hxp]
            exact he x hx
          have hv := key v (e₁.extend p v) he' fun vals hvl hz => by
            rw [← bindVals_cons_nonvar p ps a as v vals e₁ hnv]
            refine hK (v :: vals) (by simp [hvl]) fun av hav y hy => ?_
            simp only [List.zip_cons_cons, List.mem_cons] at hav
            rcases hav with rfl | hav
            · exact absurd hy (hnv y)
            · exact hz av hav y hy
          cases v
          case controlFlow => exact fl _ _
          all_goals exact hv
        all_goals exact fl _ _
      · obtain ⟨o, s₂⟩ := r₁
        obtain ⟨m, hm⟩ := hf
        dsimp only at hm
        subst hm
        exact fl _ _

section Blocks

variable (bt : TreeTable E) (fuel₀ : Nat) (f : String) (ps : List String) (body : ImpExpr)
  (ρ : Env) {W K : List String}

/-- An expression reading no variable of `W`, binding no name of `K` and calling no `f` has
    related call trees at `bt` and at the closure table of `f`, from environments related by
    `ContRel W K ρ`. -/
theorem denoteT_contRel (e : ImpExpr)
    (h : frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f) e = true) :
    RelT Sk (ContRel W K ρ) (ContRel W K ρ) IsErr (denoteT bt fuel₀ e)
      (denoteT (closureTableT bt fuel₀ f ps body ρ) fuel₀ e) := by
  have := denoteT_frame (Sk := Sk) (R := ContRel W K ρ) (bt₁ := bt)
    (bt₂ := closureTableT bt fuel₀ f ps body ρ) id
    (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f)
    (fun _ _ x hR hx => hR.1 x (by simpa using hx))
    (fun _ _ n w hR hn => ⟨fun x hx => by
      by_cases hxn : x = n
      · subst hxn; simp
      · rw [Env.extend_other _ _ _ _ hxn, Env.extend_other _ _ _ _ hxn]; exact hR.1 x hx,
      Agree.extend hR.2 (by simpa using hn) w⟩)
    (fun g hg => by
      have hgf : g ≠ f := by simpa using hg
      funext vals; simp [closureTableT, hgf]) e h fuel₀
  rwa [renameReads_id e (frameOk_mono (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) e h)]
    at this

/-- **A call of a statement closure.** From environments related by `ContRel`, the call tree of
    a call of `f` on pure arguments without a call of `f` reading no variable of `W` under the
    closure table is related to the call tree of the call block, which performs each argument
    tree once, a leaf that is an error being a failed leaf and the final environments related by
    `ContRel`. -/
theorem callBlockT_rel (hW : ∀ p, p ∈ ps → W.contains p = true)
    (hKW : ∀ x, x ∈ K → W.contains x = false) (hnd : ps.Nodup)
    (hbody : bodyOk W ps (ps ++ K) body = true) (args : List ImpExpr)
    (hat : ∀ a, a ∈ args → isPure a = true ∧
      frameOk (fun x => !W.contains x) (fun n => !K.contains n) (fun g => g != f) a = true) :
    RelT Sk (ContRel W K ρ) (ContRel W K ρ) IsErr
      (denoteT bt fuel₀ (inlineBlocks f ps body (.app f args)))
      (denoteT (closureTableT bt fuel₀ f ps body ρ) fuel₀ (.app f args)) := by
  have hok : ∀ g, (g != f) = true → bt g = closureTableT bt fuel₀ f ps body ρ g := fun g hg => by
    have hgf : g ≠ f := by simpa using hg
    funext vals; simp [closureTableT, hgf]
  by_cases hl : args.length = ps.length
  case neg =>
    have hmap : args.map (inlineBlocks f ps body) = args :=
      (List.map_congr_left fun a ha => inlineBlocks_free f ps body a
        (frameOk_mono (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h) a (hat a ha).2)).trans
        (by simp)
    simp only [inlineBlocks, hl, and_false, ite_false, inlineBlocks.mapExpr_eq, hmap, denoteT]
    unfold denoteAppT
    refine argsT_relK fuel₀ args
      (fun a ha => denoteT_contRel bt fuel₀ f ps body ρ a (hat a ha).2) _ _
      (fun vals hvl => RelT.of_bad fun env => ?_) (fun s => ⟨_, _, rfl, _, rfl⟩)
    have hvl' : vals.length ≠ ps.length := hvl ▸ hl
    dsimp only
    rw [lift_bind_run]
    simp only [closureTableT, ite_true, hvl', ite_false]
    exact ⟨_, _, rfl, _, rfl⟩
  simp only [inlineBlocks, hl, and_self, ite_true, callBlock]
  intro e₁ e₂ hR
  rw [denoteT, denoteAppT]
  have hy : ∀ y, ImpExpr.var y ∈ args → W.contains y = false := fun y hy' => by
    simpa [frameOk] using (hat _ hy').2
  refine bindArgsT_rel bt _ f fuel₀ hok _ ps args e₁ e₂ _ hW hl hat hR.1
    (fun s => ⟨_, rfl, _, rfl⟩) fun vals hvl hz => ?_
  have hzv : ∀ av, av ∈ args.zip vals → ∀ y, av.1 = .var y → e₁ y = some av.2 := by
    intro av hav y hay
    rw [hR.1 y (hy y (hay ▸ (List.of_mem_zip hav).1))]
    exact hz av hav y hay
  have hσps : ∀ x, ps.contains x = false → argRen ps args x = x := fun x hx => by
    simp only [argRen, argFor_none x ps args (by simpa using hx)]
  have hσ : ∀ x, argRen ps args x = x ∨ W.contains (argRen ps args x) = false := by
    intro x
    simp only [argRen]
    split
    · rename_i y hy'
      exact Or.inr (hy y (argFor_mem x ps args _ hy'))
    · exact Or.inl rfl
  have hpre : BodyRel (argRen ps args) W (ps ++ K) e₁ (bindVals ps args vals e₁)
      (bindAll ρ ps vals) := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [List.contains_append, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · exact bindVals_param ρ ps args vals e₁ hnd hl hvl
          (fun y hy' hyp => by have := hW y hyp; rw [hy y hy'] at this; cases this) hzv x
          (by simpa using hx)
      · have hxK : x ∈ K := by simpa using hx
        have hxW := hKW x hxK
        have hxps : x ∉ ps := fun h => by rw [hW x h] at hxW; cases hxW
        rw [hσps x (by simpa using hxps), bindVals_other x ps args vals e₁ hxps, hR.1 x hxW,
          hR.2 x hxK, bindAll_other ρ x ps vals hxps]
    · have hxps : x ∉ ps := fun h => by rw [hW x h] at hx; cases hx
      exact bindVals_other x ps args vals e₁ hxps
  have hb := denoteT_body (Sk := Sk) (Ev := e₁) bt hσ hσps body (ps ++ K) hbody fuel₀ _ _ hpre
  dsimp only
  rw [lift_bind_run]
  simp only [closureTableT, ite_true, hvl, NFCallTreeAnfPick.bind_assoc]
  rw [← NFCallTreeAnfPick.bind_ret (denoteT bt fuel₀ (renameReads (argRen ps args) body)
    (bindVals ps args vals e₁))]
  refine RuttSA.bind hb (fun r₁ r₂ hr => ?_) (fun r₁ hf t => ?_)
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
      RelT Sk (ContRel W K ρ) (ContRel W K ρ) IsErr
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
      RelT Sk (ContRel W K ρ) (ContRel W K ρ) IsErr (denoteT bt fuel₀ (inlineBlocks f ps body e))
        (denoteT (closureTableT bt fuel₀ f ps body ρ) fuel₀ e) := by
    intro e h
    rw [inlineBlocks_free f ps body e
      (frameOk_mono (fun _ _ => rfl) (fun _ _ => rfl) (fun _ h => h) e h)]
    have := denoteT_frame (Sk := Sk) (bt₁ := bt) (bt₂ := closureTableT bt fuel₀ f ps body ρ) id
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

/-- Every expression passes `spineArgsOk`: a pure closure that `inlineSpine` inlines has
    arguments without calls at its calls (`closureOk`). -/
theorem spineArgsOk_eq_true (e : ImpExpr) : spineArgsOk e = true := by
  induction e using ImpExpr.ind with
  | letBind x v cont ihv ihc =>
    clear ihv
    cases v
    case lam ps body =>
      simp only [spineArgsOk, ihc, Bool.and_true, argsFree_eq_callsOk]
      cases h : closureOk x ps body (inlineSpine cont)
      · rfl
      · simp only [closureOk, Bool.and_eq_true] at h
        simp [h.1.2]
    all_goals simpa [spineArgsOk] using ihc
  | seq a b _ ihb => simpa [spineArgsOk] using ihb
  | _ => simp [spineArgsOk]

/-- The reading of a binding of a closure is an error leaf. -/
theorem denoteT_letBind_lam_run (bt : TreeTable E) (fuel : Nat) (f : String) (ps : List String)
    (body cont : ImpExpr) (env : Env) :
    denoteT bt fuel (.letBind f (.lam ps body) cont) env =
      .ret (.err "closures are not evaluated by the reference semantics", env) := by
  rw [NFCallTreeAnfPick.denoteT_letBind_run', denoteT]
  rfl

/-- **The spine, from related environments.** For every `e`, from equal environments, the call
    tree of the reference reading `denoteSpineT bt fuel e` is related to the call tree of
    `inlineSpine e` read with `bt`: a leaf that is an error is a failed leaf, and every other leaf
    is matched by a leaf with the same outcome whose environment agrees off `spineW e`. -/
theorem inlineSpine_relT_gen (e : ImpExpr) :
    ∀ (bt : TreeTable E) (fuel : Nat),
      RelT Sk (fun e₁ e₂ => e₁ = e₂) (EqOff (spineW e)) IsErr
        (denoteT bt fuel (inlineSpine e)) (denoteSpineT bt fuel e) := by
  induction e using ImpExpr.ind with
  | letBind x v cont ihv ihc =>
    intro bt fuel
    clear ihv
    cases v
    case lam ps body =>
      have hs := spineArgsOk_eq_true (.letBind x (.lam ps body) cont)
      simp only [spineArgsOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hs
      simp only [inlineSpine, denoteSpineT, spineW]
      cases hp : closureOk x ps body (inlineSpine cont)
      case true =>
        simp only [ite_true, Bool.true_or]
        have hargs : argsFree x (inlineSpine cont) = true := hs.1.resolve_left (by simp [hp])
        intro env _ heq
        subst heq
        have h01 := ihc (closureTableT bt fuel x ps body env) fuel env env rfl
        simp only [closureOk, Bool.and_eq_true] at hp
        have h12 := denoteT_inlineCalls (Sk := Sk) bt fuel x ps body env hp.1.1 (inlineSpine cont)
          hp.2 hargs fuel env env ⟨rfl, fun _ _ => rfl⟩
        refine RuttSA.mono ?_ (ruttSA_eqTrans
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
      have h01 := ihc (closureTableT bt fuel x ps body env) fuel env env rfl
      simp only [blockOk,Bool.and_eq_true, decide_eq_true_eq] at hb
      have h12 := denoteT_inlineBlocks (Sk := Sk) bt fuel x ps body env
        (fun p hp' => by simp [blockW, hp'])
        (fun y hy => by simp only [blockK, List.mem_filter] at hy; simpa using hy.2)
        hb.1.1 hb.1.2 (inlineSpine cont) hb.2 env env ⟨fun _ _ => rfl, fun _ _ => rfl⟩
      refine RuttSA.mono ?_ (ruttSA_eqTrans
        (fun r₀ r₁ h hf => by rw [← h.1]; exact hf) h01 h12)
      rintro r₀ r₂ ⟨r₁, ⟨h1, hQ⟩, ⟨h2, hR⟩⟩
      refine ⟨h2.trans h1, fun y hy => ?_⟩
      simp only [List.contains_append, Bool.or_eq_false_iff] at hy
      exact (hR.1 y hy.1).trans (hQ y hy.2)
    all_goals
      simp only [inlineSpine, spineW]
      rw [denoteT]
      simp only [denoteSpineT]
      refine RelT.bind (badα := IsErr) (RelT.refl _) (fun o _ => ?_)
        (fun a ha s => by obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨_, _, rfl, m, rfl⟩)
      rcases o with w | _ | _ | _ | _
      · cases w <;> dsimp only <;> first
          | exact RelT.pure_mono _ (fun _ _ h => EqOff.of_eq _ _ _ h)
          | exact RelT.modify_mono (P := fun e₁ e₂ => e₁ = e₂) (Q := fun e₁ e₂ => e₁ = e₂)
              (fun _ _ h => by rw [h]) (fun _ => ihc bt fuel)
      all_goals (dsimp only; exact RelT.pure_mono _ (fun _ _ h => EqOff.of_eq _ _ _ h))
  | seq a b _ ihb =>
    intro bt fuel
    simp only [inlineSpine, spineW]
    rw [denoteT]
    simp only [denoteSpineT]
    refine RelT.bind (badα := IsErr) (RelT.refl _) (fun o _ => ?_)
      (fun a ha s => by obtain ⟨m, hm⟩ := ha; subst hm; exact ⟨_, _, rfl, m, rfl⟩)
    rcases o with w | _ | _ | _ | _
    · cases w <;> dsimp only <;> first
        | exact RelT.pure_mono _ (fun _ _ h => EqOff.of_eq _ _ _ h)
        | exact ihb bt fuel
    all_goals (dsimp only; exact RelT.pure_mono _ (fun _ _ h => EqOff.of_eq _ _ _ h))
  | _ =>
    intro bt fuel
    simp only [inlineSpine, denoteSpineT, spineW]
    exact (RelT.refl _).mono (fun _ _ h => h) (fun _ _ h => EqOff.of_eq _ _ _ h)

/-- **Inlining the closures of the statement spine at the level of call trees.** For every `e`,
    from one environment, the call tree of the reference reading `denoteSpineT bt fuel e` is
    related to the call tree of `inlineSpine e` read with `bt` by `RuttSA` at equal events and
    answers: a leaf that is an error is a failed leaf, and every other leaf is matched by a leaf
    with the same outcome whose environment agrees off `spineW e`. -/
theorem inlineSpine_relT (Sk : (e : E.Event) → E.Resp e → Prop) (bt : TreeTable E) (e : ImpExpr)
    (fuel : Nat) (env : Env) :
    RuttSA Sk (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
      (fun r₁ r₂ => r₂.1 = r₁.1 ∧ EqOff (spineW e) r₂.2 r₁.2)
      (fun r => IsErr r.1)
      (denoteSpineT bt fuel e env) (denoteT bt fuel (inlineSpine e) env) :=
  inlineSpine_relT_gen (Sk := Sk) e bt fuel env env rfl

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeInlineSpine
