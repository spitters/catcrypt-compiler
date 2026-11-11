/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick
public import HaxLean.Phase.WhileTrueFlag

/-!
# The rewriting of `while true` at the level of call trees

The rewriting `wtFn g` replaces each `whileFold (lit (bool true)) body` and each
`whileFoldReturn (lit (bool true)) body` by the loop on a flag variable `g` bound to `true`. At the
level of call trees, the reading `denoteT` of an expression of the fragment `wtOk g` from an
environment is related by `RuttS` at equal events and answers to the reading of its rewriting
from an environment agreeing off `g`: the leaves have the same outcome and agreeing environments
(`WtRel`), and no leaf of the first reading is a failed leaf. A right-hand side or an atom of the
fragment reads as a tree whose events are those of one call with equal arguments, and whose leaves
differ only in the environment.

## Main results

* `val_runT`: a value of the fragment reads as the same tree of one call, with leaves in each
  environment, in environments agreeing off `g`.
* `wtFn_relT`: the call trees of `e` and `wtFn g e` are related by `WtRel` from environments
  agreeing off `g`.
* `wtFn_relT_same`: from one environment, the leaves have the same outcome.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeWhileTrue

open _root_.Hax
open _root_.Hax.WhileTrueFlag (wtFn wtOk WtRel valOk wtLoop wtLoopR)
open _root_.Hax.ContinueFlag (AgreeOff atomOk rhsOk extend_ne)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeRepeatCount (tm_bind_run tm_pure_run
  denoteT_lit_run denoteT_var_run denoteT_var_run_none)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeAnfPick (bind_assoc ruttS_bind_same
  denoteT_seq_run denoteT_ifThenElse_run denoteT_letBind_run' denoteT_cfBreak_run)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)

variable {E : EventSig}

/-- Running a lifted tree followed by a continuation: the continuation runs at each answer. -/
theorem lift_bind_run {α β : Type} (t : CallTree E α) (f : α → TM E β) (s : Env) :
    (StateT.lift t >>= f) s = t.bind (fun a => f a s) := by
  rw [tm_bind_run]
  change (t.bind (fun a => CallTree.ret (a, s))).bind _ = _
  rw [bind_assoc]
  rfl

/-! ## Atoms and values -/

/-- An atom reads as a leaf with the same outcome in environments agreeing off `g`. -/
theorem atom_runT (bt : TreeTable E) (fuel : Nat) {g : String} {a : ImpExpr}
    (ha : atomOk g a = true) {env1 env2 : Env} (hag : AgreeOff g env1 env2) :
    ∃ o, denoteT bt fuel a env1 = .ret (o, env1) ∧ denoteT bt fuel a env2 = .ret (o, env2) := by
  cases a with
  | var x =>
    have hx : x ≠ g := by simpa [atomOk] using ha
    rcases h2 : env2 x with _ | v
    · have h1 : env1 x = none := (hag x hx).trans h2
      exact ⟨_, denoteT_var_run_none bt fuel x env1 h1, denoteT_var_run_none bt fuel x env2 h2⟩
    · have h1 : env1 x = some v := (hag x hx).trans h2
      exact ⟨_, denoteT_var_run bt fuel x env1 v h1, denoteT_var_run bt fuel x env2 v h2⟩
  | lit l => exact ⟨_, denoteT_lit_run bt fuel l env1, denoteT_lit_run bt fuel l env2⟩
  | unitVal => exact ⟨_, by rw [denoteT]; rfl, by rw [denoteT]; rfl⟩
  | _ => simp [atomOk] at ha

/-- A list of atoms reads as a leaf with the same result in environments agreeing off `g`. -/
theorem args_runT (bt : TreeTable E) (fuel : Nat) {g : String} {args : List ImpExpr}
    (hs : args.all (atomOk g) = true) {env1 env2 : Env} (hag : AgreeOff g env1 env2) :
    ∃ ov, denoteArgsT bt fuel args env1 = .ret (ov, env1) ∧
      denoteArgsT bt fuel args env2 = .ret (ov, env2) := by
  induction args with
  | nil => exact ⟨_, by rw [denoteArgsT]; rfl, by rw [denoteArgsT]; rfl⟩
  | cons a as ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hs
    obtain ⟨o, h1, h2⟩ := atom_runT bt fuel hs.1 hag
    obtain ⟨ov, i1, i2⟩ := ih hs.2
    rw [denoteArgsT, tm_bind_run, tm_bind_run, h1, h2]
    rcases o with v | _ | _ | _ | _
    · by_cases hcf : ∃ k w, v = .controlFlow k w
      · obtain ⟨k, w, rfl⟩ := hcf
        exact ⟨_, rfl, rfl⟩
      · refine ⟨ov.map (v :: ·), ?_, ?_⟩
        · cases v <;> first
            | exact (hcf ⟨_, _, rfl⟩).elim
            | (simp only [CallTree.bind]; rw [tm_bind_run, i1]; rfl)
        · cases v <;> first
            | exact (hcf ⟨_, _, rfl⟩).elim
            | (simp only [CallTree.bind]; rw [tm_bind_run, i2]; rfl)
    all_goals exact ⟨_, rfl, rfl⟩

/-- A value of the fragment reads, in environments agreeing off `g`, as the same tree followed by
    leaves with the same outcome and the respective environments. -/
theorem val_runT (bt : TreeTable E) (fuel : Nat) {g : String} {v : ImpExpr}
    (hv : valOk g v = true) {env1 env2 : Env} (hag : AgreeOff g env1 env2) :
    ∃ (t : CallTree E (Option Value)) (k : Option Value → Outcome),
      denoteT bt fuel v env1 = t.bind (fun a => .ret (k a, env1)) ∧
      denoteT bt fuel v env2 = t.bind (fun a => .ret (k a, env2)) := by
  have atomCase : atomOk g v = true →
      ∃ (t : CallTree E (Option Value)) (k : Option Value → Outcome),
        denoteT bt fuel v env1 = t.bind (fun a => .ret (k a, env1)) ∧
        denoteT bt fuel v env2 = t.bind (fun a => .ret (k a, env2)) := fun ha => by
    obtain ⟨o, h1, h2⟩ := atom_runT bt fuel ha hag
    exact ⟨.ret none, fun _ => o, h1, h2⟩
  cases v with
  | tuple es =>
    obtain ⟨ov, h1, h2⟩ := args_runT bt fuel (by simpa [valOk] using hv) hag
    refine ⟨.ret none, fun _ => ov.elim (.err "non-value in tuple elements")
      (fun vals => .val (.tuple vals)), ?_, ?_⟩
    · rw [denoteT, tm_bind_run, h1]
      cases ov <;> rfl
    · rw [denoteT, tm_bind_run, h2]
      cases ov <;> rfl
  | app f args =>
    obtain ⟨ov, h1, h2⟩ := args_runT bt fuel (by simpa [valOk, rhsOk] using hv) hag
    rcases ov with _ | vals
    · refine ⟨.ret none, fun _ => .err "non-value in function arguments", ?_, ?_⟩
      · rw [denoteT, denoteAppT, tm_bind_run, h1]; rfl
      · rw [denoteT, denoteAppT, tm_bind_run, h2]; rfl
    · refine ⟨bt f vals, fun r => match r with
        | some v => .val v
        | none => .err s!"unknown function or bad args: {f}", ?_, ?_⟩
      · rw [denoteT, denoteAppT, tm_bind_run, h1]
        dsimp only [CallTree.bind]
        rw [lift_bind_run]
        congr 1
        funext r
        cases r <;> rfl
      · rw [denoteT, denoteAppT, tm_bind_run, h2]
        dsimp only [CallTree.bind]
        rw [lift_bind_run]
        congr 1
        funext r
        cases r <;> rfl
  | var x => exact atomCase (by simpa [valOk, rhsOk] using hv)
  | lit l => exact atomCase (by simpa [valOk, rhsOk] using hv)
  | unitVal => exact atomCase (by simpa [valOk, rhsOk] using hv)
  | _ => simp [valOk, rhsOk, atomOk] at hv

/-! ## The relation of the call trees -/

variable (h₁ : ∀ e : E.Event, E.Resp e)

/-- The hypothesis of the rewriting of `e`, over every fuel and every pair of environments
    agreeing off `g`: the call trees are related by `RuttS` at equal events and answers, with the
    leaves related by `WtRel` and no failed leaf. -/
def WtIHT (bt : TreeTable E) (g : String) (e : ImpExpr) : Prop :=
  ∀ fuel env1 env2, AgreeOff g env1 env2 →
    RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
      (fun r₁ r₂ => WtRel g env2 r₁ r₂) (fun _ => False)
      (denoteT bt fuel e env1) (denoteT bt fuel (wtFn g e) env2)

variable {h₁}

/-- A relation of leaves at `env2.extend n w` gives one at `env2`, for a name other than `g`. -/
theorem wtRel_of_extend {g n : String} {env2 : Env} {w : Value} {r1 r2 : Outcome × Env}
    (hn : n ≠ g) (s : WtRel g (env2.extend n w) r1 r2) : WtRel g env2 r1 r2 :=
  ⟨s.out, s.agree, fun h => s.keep (by rw [extend_ne _ (Ne.symm hn)]; exact h)⟩

/-- A relation of leaves at `e2` gives one at `env2` when `e2` keeps `g` bound to `true`. -/
theorem wtRel_of_keep {g : String} {env2 e2 : Env} {r1 r2 : Outcome × Env}
    (r3 : env2 g = some (.bool true) → e2 g = some (.bool true)) (s : WtRel g e2 r1 r2) :
    WtRel g env2 r1 r2 :=
  ⟨s.out, s.agree, fun h => s.keep (r3 h)⟩

section Body

variable {bt : TreeTable E} {g : String}

/-- A value of the fragment that the rewriting leaves unchanged. -/
theorem val_relT {a : ImpExpr} (ha : valOk g a = true) (hw : wtFn g a = a) :
    WtIHT h₁ bt g a := by
  intro fuel env1 env2 hag
  rw [hw]
  obtain ⟨t, k, e1, e2⟩ := val_runT bt fuel ha hag
  rw [e1, e2]
  exact ruttS_bind_same t fun _ => .ret (WtRel.refl hag)

/-- A binding of a value of the fragment. -/
theorem letBind_relT {n : String} {v b : ImpExpr} (hn : n ≠ g) (hv : valOk g v = true)
    (ihb : WtIHT h₁ bt g b) : WtIHT h₁ bt g (.letBind n v b) := by
  intro fuel env1 env2 hag
  obtain ⟨t, k, e1, e2⟩ := val_runT bt fuel hv hag
  simp only [wtFn]
  rw [denoteT_letBind_run', denoteT_letBind_run', e1, e2, bind_assoc, bind_assoc]
  refine ruttS_bind_same t fun a => ?_
  dsimp only [CallTree.bind]
  generalize k a = o
  rcases o with w | _ | _ | _ | _
  · cases w with
    | controlFlow k u => exact .ret (WtRel.refl hag)
    | _ =>
      all_goals
        exact NFProgCallTreeExt.RuttS.mono (fun _ _ s => wtRel_of_extend hn s)
          (ihb fuel _ _ (hag.extend n _))
  all_goals exact .ret (WtRel.refl hag)

/-- A sequence. -/
theorem seq_relT {a b : ImpExpr} (iha : WtIHT h₁ bt g a) (ihb : WtIHT h₁ bt g b) :
    WtIHT h₁ bt g (.seq a b) := by
  intro fuel env1 env2 hag
  simp only [wtFn]
  rw [denoteT_seq_run, denoteT_seq_run]
  refine NFProgCallTree.RuttS.bind (RR' := WtRel g env2) (Fail' := fun _ => False)
    (iha fuel env1 env2 hag) ?_ (fun _ hf => hf.elim)
  rintro ⟨o1, e1⟩ ⟨o2, e2⟩ ⟨r1, r2, r3⟩
  dsimp only at r1 r2 r3
  subst r1
  rcases o2 with v | _ | _ | _ | _
  · cases v with
    | controlFlow k w => exact .ret ⟨rfl, r2, r3⟩
    | _ =>
      all_goals
        exact NFProgCallTreeExt.RuttS.mono (fun _ _ s => wtRel_of_keep r3 s) (ihb fuel e1 e2 r2)
  all_goals exact .ret ⟨rfl, r2, r3⟩

/-- A conditional on a variable. -/
theorem ifThenElse_relT {x : String} {t e : ImpExpr} (hx : x ≠ g) (iht : WtIHT h₁ bt g t)
    (ihe : WtIHT h₁ bt g e) : WtIHT h₁ bt g (.ifThenElse (.var x) t e) := by
  intro fuel env1 env2 hag
  simp only [wtFn]
  rw [denoteT_ifThenElse_run, denoteT_ifThenElse_run]
  obtain ⟨o, h1, h2⟩ := atom_runT bt fuel (a := .var x) (by simpa [atomOk] using hx) hag
  rw [h1, h2]
  dsimp only [CallTree.bind]
  rcases o with v | _ | _ | _ | _
  · cases v with
    | bool bv =>
      cases bv
      · exact ihe fuel env1 env2 hag
      · exact iht fuel env1 env2 hag
    | _ => exact .ret (WtRel.refl hag)
  all_goals exact .ret (WtRel.refl hag)

/-- A function-level return of an atom. -/
theorem cfBreak_relT {a : ImpExpr} (ha : atomOk g a = true) :
    WtIHT h₁ bt g (.cfBreak a) := by
  intro fuel env1 env2 hag
  obtain ⟨o, h1, h2⟩ := atom_runT bt fuel ha hag
  simp only [wtFn]
  rw [denoteT_cfBreak_run, denoteT_cfBreak_run, h1, h2]
  dsimp only [CallTree.bind]
  rcases o with w | _ | _ | _ | _
  · cases w <;> exact .ret (WtRel.refl hag)
  all_goals exact .ret (WtRel.refl hag)

end Body

/-! ## Loops -/

section Loops

variable {bt : TreeTable E} {g : String}

/-- A `forFold` loop at `lo ≥ hi` is a leaf. -/
theorem forLoopT_ge_run (fuel : Nat) (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : hi ≤ lo) : denoteForLoopT bt fuel i lo hi body env = .ret (.val .unit, env) := by
  rw [denoteForLoopT, ite_eq_left h]; rfl

/-- A `forFold` loop at `lo < hi` without fuel is a leaf. -/
theorem forLoopT_zero_run (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : lo < hi) : denoteForLoopT bt 0 i lo hi body env = .ret (.err "out of fuel", env) := by
  rw [denoteForLoopT, ite_eq_right (Int.not_le.mpr h), ite_eq_left rfl]; rfl

/-- One trip of a `forFold` loop at `lo < hi`. -/
theorem forLoopT_succ_run (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : lo < hi) :
    denoteForLoopT bt (n + 1) i lo hi body env =
      (denoteT bt (n + 1) body (env.extend i (.int lo))).bind fun p =>
        match p with
        | (.val (.controlFlow true v), e2) => .ret (.val v, e2)
        | (.val (.controlFlow false _), e2) => denoteForLoopT bt n i (lo + 1) hi body e2
        | (.val _, e2) => denoteForLoopT bt n i (lo + 1) hi body e2
        | (o, e2) => .ret (o, e2) := by
  rw [denoteForLoopT, ite_eq_right (Int.not_le.mpr h), ite_eq_right (Nat.add_one_ne_zero n)]
  change (denoteT bt (n + 1) body (env.extend i (.int lo))).bind _ = _
  congr 1
  funext p
  rcases p with ⟨o, e2⟩
  rcases o with v | _ | _ | _ | _
  · cases v with
    | controlFlow k w => cases k <;> rfl
    | _ => rfl
  all_goals rfl

/-- **`forFold` over the rewritten body.** -/
theorem forLoop_relT {i : String} {body : ImpExpr} (hig : i ≠ g) (ihb : WtIHT h₁ bt g body)
    (fuel : Nat) :
    ∀ (lo hi : Int) (env1 env2 : Env), AgreeOff g env1 env2 →
      RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
        (fun r₁ r₂ => WtRel g env2 r₁ r₂) (fun _ => False)
        (denoteForLoopT bt fuel i lo hi body env1)
        (denoteForLoopT bt fuel i lo hi (wtFn g body) env2) := by
  induction fuel with
  | zero =>
    intro lo hi env1 env2 hag
    by_cases h : hi ≤ lo
    · rw [forLoopT_ge_run _ _ _ _ _ _ h, forLoopT_ge_run _ _ _ _ _ _ h]
      exact .ret (WtRel.refl hag)
    · have h' : lo < hi := Int.lt_of_not_ge h
      rw [forLoopT_zero_run _ _ _ _ _ h', forLoopT_zero_run _ _ _ _ _ h']
      exact .ret (WtRel.refl hag)
  | succ n ih =>
    intro lo hi env1 env2 hag
    by_cases h : hi ≤ lo
    · rw [forLoopT_ge_run _ _ _ _ _ _ h, forLoopT_ge_run _ _ _ _ _ _ h]
      exact .ret (WtRel.refl hag)
    have h' : lo < hi := Int.lt_of_not_ge h
    rw [forLoopT_succ_run _ _ _ _ _ _ h', forLoopT_succ_run _ _ _ _ _ _ h']
    have hk0 : env2 g = some (.bool true) →
        (env2.extend i (.int lo)) g = some (.bool true) :=
      fun hg => by rw [extend_ne _ (Ne.symm hig)]; exact hg
    refine NFProgCallTree.RuttS.bind (RR' := WtRel g (env2.extend i (.int lo)))
      (Fail' := fun _ => False) (ihb (n + 1) _ _ (hag.extend i _)) ?_ (fun _ hf => hf.elim)
    rintro ⟨o1, e1⟩ ⟨o2, e2⟩ ⟨r1, r2, r3⟩
    dsimp only at r1 r2 r3
    subst r1
    rcases o2 with v | _ | _ | _ | _
    · cases v with
      | controlFlow k w =>
        cases k with
        | true => exact .ret ⟨rfl, r2, fun hg => r3 (hk0 hg)⟩
        | false =>
          exact NFProgCallTreeExt.RuttS.mono (fun _ _ s => wtRel_of_keep (fun hg => r3 (hk0 hg)) s)
            (ih (lo + 1) hi e1 e2 r2)
      | _ =>
        all_goals
          exact NFProgCallTreeExt.RuttS.mono (fun _ _ s => wtRel_of_keep (fun hg => r3 (hk0 hg)) s)
            (ih (lo + 1) hi e1 e2 r2)
    all_goals exact .ret ⟨rfl, r2, fun hg => r3 (hk0 hg)⟩

/-- A `forFold` with atomic bounds. -/
theorem forFold_relT {i : String} {lo hi body : ImpExpr} (hig : i ≠ g)
    (hlo : atomOk g lo = true) (hhi : atomOk g hi = true) (ihb : WtIHT h₁ bt g body) :
    WtIHT h₁ bt g (.forFold i lo hi body) := by
  intro fuel env1 env2 hag
  obtain ⟨ol, hl1, hl2⟩ := atom_runT bt fuel hlo hag
  obtain ⟨oh, hh1, hh2⟩ := atom_runT bt fuel hhi hag
  simp only [wtFn]
  conv_lhs => rw [denoteT, tm_bind_run, hl1]
  conv_rhs => rw [denoteT, tm_bind_run, hl2]
  dsimp only [CallTree.bind]
  rcases ol with vlo | _ | _ | _ | _
  · cases vlo
    all_goals
      dsimp only
      first
        | exact .ret (WtRel.refl hag)
        | (rw [tm_bind_run, tm_bind_run, hh1, hh2]
           dsimp only [CallTree.bind]
           rcases oh with vhi | _ | _ | _ | _
           · cases vhi <;>
               first
                 | exact .ret (WtRel.refl hag)
                 | exact forLoop_relT hig ihb fuel _ _ _ _ hag
           all_goals exact .ret (WtRel.refl hag))
  all_goals exact .ret (WtRel.refl hag)

/-- The reading of a `whileFold`. -/
theorem denoteT_whileFold (fuel : Nat) (c body : ImpExpr) :
    denoteT bt fuel (.whileFold c body) = denoteWhileT bt fuel c body := by
  rw [denoteT]

/-- The reading of a `whileFoldReturn`. -/
theorem denoteT_whileFoldReturn (fuel : Nat) (c body : ImpExpr) :
    denoteT bt fuel (.whileFoldReturn c body) = denoteWhileReturnT bt fuel c body := by
  rw [denoteT]

/-- A `whileFold` loop without fuel is a leaf. -/
theorem whileT_zero_run (c body : ImpExpr) (env : Env) :
    denoteWhileT bt 0 c body env = .ret (.err "out of fuel", env) := by
  rw [denoteWhileT, ite_eq_left rfl]; rfl

/-- One trip of a `whileFold` loop. -/
theorem whileT_succ_run (n : Nat) (c body : ImpExpr) (env : Env) :
    denoteWhileT bt (n + 1) c body env =
      (denoteT bt (n + 1) c env).bind fun p =>
        match p with
        | (.val (.controlFlow k v), e1) => .ret (.val (.controlFlow k v), e1)
        | (.val (.bool true), e1) =>
          (denoteT bt (n + 1) body e1).bind fun q =>
            match q with
            | (.val (.controlFlow true v), e2) => .ret (.val v, e2)
            | (.val (.controlFlow false _), e2) => denoteWhileT bt n c body e2
            | (.val _, e2) => denoteWhileT bt n c body e2
            | (o, e2) => .ret (o, e2)
        | (.val (.bool false), e1) => .ret (.val .unit, e1)
        | (.val _, e1) => .ret (.err "while condition not a bool", e1)
        | (o, e1) => .ret (o, e1) := by
  rw [denoteWhileT, ite_eq_right (Nat.add_one_ne_zero n)]
  change (denoteT bt (n + 1) c env).bind _ = _
  congr 1
  funext p
  rcases p with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _
  · cases v with
    | controlFlow k w => rfl
    | bool b =>
      cases b
      · rfl
      · change (denoteT bt (n + 1) body e1).bind _ = _
        congr 1
        funext q
        rcases q with ⟨o2, e2⟩
        rcases o2 with w | _ | _ | _ | _
        · cases w with
          | controlFlow k u => cases k <;> rfl
          | _ => rfl
        all_goals rfl
    | _ => rfl
  all_goals rfl

/-- A `whileFoldReturn` loop without fuel is a leaf. -/
theorem whileRT_zero_run (c body : ImpExpr) (env : Env) :
    denoteWhileReturnT bt 0 c body env = .ret (.err "out of fuel", env) := by
  rw [denoteWhileReturnT, ite_eq_left rfl]; rfl

/-- One trip of a `whileFoldReturn` loop. -/
theorem whileRT_succ_run (n : Nat) (c body : ImpExpr) (env : Env) :
    denoteWhileReturnT bt (n + 1) c body env =
      (denoteT bt (n + 1) c env).bind fun p =>
        match p with
        | (.val (.controlFlow k v), e1) => .ret (.val (.controlFlow k v), e1)
        | (.val (.bool true), e1) =>
          (denoteT bt (n + 1) body e1).bind fun q =>
            match q with
            | (.val (.controlFlow true (.controlFlow false v)), e2) => .ret (.val v, e2)
            | (.val (.controlFlow true v), e2) => .ret (.val (.controlFlow true v), e2)
            | (.val (.controlFlow false _), e2) => denoteWhileReturnT bt n c body e2
            | (.val _, e2) => denoteWhileReturnT bt n c body e2
            | (o, e2) => .ret (o, e2)
        | (.val (.bool false), e1) => .ret (.val .unit, e1)
        | (.val _, e1) => .ret (.err "while condition not a bool", e1)
        | (o, e1) => .ret (o, e1) := by
  rw [denoteWhileReturnT, ite_eq_right (Nat.add_one_ne_zero n)]
  change (denoteT bt (n + 1) c env).bind _ = _
  congr 1
  funext p
  rcases p with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _
  · cases v with
    | controlFlow k w => rfl
    | bool b =>
      cases b
      · rfl
      · change (denoteT bt (n + 1) body e1).bind _ = _
        congr 1
        funext q
        rcases q with ⟨o2, e2⟩
        rcases o2 with w | _ | _ | _ | _
        · cases w with
          | controlFlow k u =>
            cases k
            · rfl
            · cases u with
              | controlFlow k' u' => cases k' <;> rfl
              | _ => rfl
          | _ => rfl
        all_goals rfl
    | _ => rfl
  all_goals rfl

/-- **A `whileFold` over the rewritten body.** For guards `c1` and `c2` that read as the same leaf
    on environments agreeing off `g` and satisfying `Q` on the rewritten side, where `Q` persists
    across a run that keeps `g` bound to `true`, the loops over `body` and `wtFn g body` are
    related. -/
theorem whileLoop_relT {c1 c2 body : ImpExpr} (Q : Env → Prop)
    (hQ : ∀ e e' : Env, Q e → (e g = some (.bool true) → e' g = some (.bool true)) → Q e')
    (hc : ∀ (n : Nat) (env1 env2 : Env), AgreeOff g env1 env2 → Q env2 →
      ∃ o, denoteT bt n c1 env1 = .ret (o, env1) ∧ denoteT bt n c2 env2 = .ret (o, env2))
    (ihb : WtIHT h₁ bt g body) (fuel : Nat) :
    ∀ (env1 env2 : Env), AgreeOff g env1 env2 → Q env2 →
      RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
        (fun r₁ r₂ => WtRel g env2 r₁ r₂) (fun _ => False)
        (denoteWhileT bt fuel c1 body env1) (denoteWhileT bt fuel c2 (wtFn g body) env2) := by
  induction fuel with
  | zero =>
    intro env1 env2 hag _
    rw [whileT_zero_run, whileT_zero_run]
    exact .ret (WtRel.refl hag)
  | succ n ih =>
    intro env1 env2 hag hq
    obtain ⟨o, hc1, hc2⟩ := hc (n + 1) env1 env2 hag hq
    rw [whileT_succ_run, whileT_succ_run, hc1, hc2]
    dsimp only [CallTree.bind]
    rcases o with v | _ | _ | _ | _
    · cases v with
      | bool bv =>
        cases bv with
        | false => exact .ret (WtRel.refl hag)
        | true =>
          dsimp only
          refine NFProgCallTree.RuttS.bind (RR' := WtRel g env2) (Fail' := fun _ => False)
            (ihb (n + 1) env1 env2 hag) ?_ (fun _ hf => hf.elim)
          rintro ⟨o1, e1⟩ ⟨o2, e2⟩ ⟨r1, r2, r3⟩
          dsimp only at r1 r2 r3
          subst r1
          have hq2 : Q e2 := hQ env2 e2 hq r3
          rcases o2 with w | _ | _ | _ | _
          · cases w with
            | controlFlow k u =>
              cases k with
              | true => exact .ret ⟨rfl, r2, r3⟩
              | false =>
                exact NFProgCallTreeExt.RuttS.mono (fun _ _ s => wtRel_of_keep r3 s)
                  (ih e1 e2 r2 hq2)
            | _ =>
              all_goals
                exact NFProgCallTreeExt.RuttS.mono (fun _ _ s => wtRel_of_keep r3 s)
                  (ih e1 e2 r2 hq2)
          all_goals exact .ret ⟨rfl, r2, r3⟩
      | _ => exact .ret (WtRel.refl hag)
    all_goals exact .ret (WtRel.refl hag)

/-- **`while true` on the flag.** -/
theorem whileTrue_relT {body : ImpExpr} (ihb : WtIHT h₁ bt g body) :
    WtIHT h₁ bt g (.whileFold (.lit (.bool true)) body) := by
  intro fuel env1 env2 hag
  simp only [wtFn, wtLoop]
  rw [denoteT_letBind_run', denoteT_lit_run]
  dsimp only [CallTree.bind, Value.ofLit]
  rw [denoteT_whileFold, denoteT_whileFold]
  have hag' : AgreeOff g env1 (env2.extend g (.bool true)) := hag.extend_right _
  have hq : (env2.extend g (.bool true)) g = some (.bool true) := Env.extend_same _ _ _
  exact NFProgCallTreeExt.RuttS.mono (fun _ _ s => wtRel_of_keep (fun _ => hq) s)
    (whileLoop_relT (h₁ := h₁) (bt := bt) (g := g) (c1 := .lit (.bool true)) (c2 := .var g)
      (fun e => e g = some (.bool true)) (fun _ _ h k => k h)
      (fun n e1 e2 _ h => ⟨.val (.bool true), denoteT_lit_run bt n _ e1,
        denoteT_var_run bt n g e2 _ h⟩) ihb fuel env1 _ hag' hq)

/-- A `whileFold` on a variable other than `g`. -/
theorem whileVar_relT {x : String} {body : ImpExpr} (hx : x ≠ g) (ihb : WtIHT h₁ bt g body) :
    WtIHT h₁ bt g (.whileFold (.var x) body) := by
  intro fuel env1 env2 hag
  simp only [wtFn, wtLoop]
  rw [denoteT_whileFold, denoteT_whileFold]
  have hxa : atomOk g (.var x) = true := by simpa [atomOk] using hx
  refine whileLoop_relT (fun _ => True) (fun _ _ _ _ => trivial) (fun n e1 e2 h _ => ?_) ihb
    fuel env1 env2 hag trivial
  obtain ⟨o, h1, h2⟩ := atom_runT bt n hxa h
  exact ⟨o, h1, h2⟩

/-- **A `whileFoldReturn` over the rewritten body.** -/
theorem whileLoopR_relT {c1 c2 body : ImpExpr} (Q : Env → Prop)
    (hQ : ∀ e e' : Env, Q e → (e g = some (.bool true) → e' g = some (.bool true)) → Q e')
    (hc : ∀ (n : Nat) (env1 env2 : Env), AgreeOff g env1 env2 → Q env2 →
      ∃ o, denoteT bt n c1 env1 = .ret (o, env1) ∧ denoteT bt n c2 env2 = .ret (o, env2))
    (ihb : WtIHT h₁ bt g body) (fuel : Nat) :
    ∀ (env1 env2 : Env), AgreeOff g env1 env2 → Q env2 →
      RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
        (fun r₁ r₂ => WtRel g env2 r₁ r₂) (fun _ => False)
        (denoteWhileReturnT bt fuel c1 body env1)
        (denoteWhileReturnT bt fuel c2 (wtFn g body) env2) := by
  induction fuel with
  | zero =>
    intro env1 env2 hag _
    rw [whileRT_zero_run, whileRT_zero_run]
    exact .ret (WtRel.refl hag)
  | succ n ih =>
    intro env1 env2 hag hq
    obtain ⟨o, hc1, hc2⟩ := hc (n + 1) env1 env2 hag hq
    rw [whileRT_succ_run, whileRT_succ_run, hc1, hc2]
    dsimp only [CallTree.bind]
    rcases o with v | _ | _ | _ | _
    · cases v with
      | bool bv =>
        cases bv with
        | false => exact .ret (WtRel.refl hag)
        | true =>
          dsimp only
          refine NFProgCallTree.RuttS.bind (RR' := WtRel g env2) (Fail' := fun _ => False)
            (ihb (n + 1) env1 env2 hag) ?_ (fun _ hf => hf.elim)
          rintro ⟨o1, e1⟩ ⟨o2, e2⟩ ⟨r1, r2, r3⟩
          dsimp only at r1 r2 r3
          subst r1
          have hq2 : Q e2 := hQ env2 e2 hq r3
          rcases o2 with w | _ | _ | _ | _
          · cases w with
            | controlFlow k u =>
              cases k with
              | true =>
                cases u with
                | controlFlow k' u' =>
                  cases k' with
                  | false => exact .ret ⟨rfl, r2, r3⟩
                  | true => exact .ret ⟨rfl, r2, r3⟩
                | _ => exact .ret ⟨rfl, r2, r3⟩
              | false =>
                exact NFProgCallTreeExt.RuttS.mono (fun _ _ s => wtRel_of_keep r3 s)
                  (ih e1 e2 r2 hq2)
            | _ =>
              all_goals
                exact NFProgCallTreeExt.RuttS.mono (fun _ _ s => wtRel_of_keep r3 s)
                  (ih e1 e2 r2 hq2)
          all_goals exact .ret ⟨rfl, r2, r3⟩
      | _ => exact .ret (WtRel.refl hag)
    all_goals exact .ret (WtRel.refl hag)

/-- **`while true` with early return on the flag.** -/
theorem whileTrueR_relT {body : ImpExpr} (ihb : WtIHT h₁ bt g body) :
    WtIHT h₁ bt g (.whileFoldReturn (.lit (.bool true)) body) := by
  intro fuel env1 env2 hag
  simp only [wtFn, wtLoopR]
  rw [denoteT_letBind_run', denoteT_lit_run]
  dsimp only [CallTree.bind, Value.ofLit]
  rw [denoteT_whileFoldReturn, denoteT_whileFoldReturn]
  have hag' : AgreeOff g env1 (env2.extend g (.bool true)) := hag.extend_right _
  have hq : (env2.extend g (.bool true)) g = some (.bool true) := Env.extend_same _ _ _
  exact NFProgCallTreeExt.RuttS.mono (fun _ _ s => wtRel_of_keep (fun _ => hq) s)
    (whileLoopR_relT (h₁ := h₁) (bt := bt) (g := g) (c1 := .lit (.bool true)) (c2 := .var g)
      (fun e => e g = some (.bool true)) (fun _ _ h k => k h)
      (fun n e1 e2 _ h => ⟨.val (.bool true), denoteT_lit_run bt n _ e1,
        denoteT_var_run bt n g e2 _ h⟩) ihb fuel env1 _ hag' hq)

/-- A `whileFoldReturn` on a variable other than `g`. -/
theorem whileVarR_relT {x : String} {body : ImpExpr} (hx : x ≠ g) (ihb : WtIHT h₁ bt g body) :
    WtIHT h₁ bt g (.whileFoldReturn (.var x) body) := by
  intro fuel env1 env2 hag
  simp only [wtFn, wtLoopR]
  rw [denoteT_whileFoldReturn, denoteT_whileFoldReturn]
  have hxa : atomOk g (.var x) = true := by simpa [atomOk] using hx
  refine whileLoopR_relT (fun _ => True) (fun _ _ _ _ => trivial) (fun n e1 e2 h _ => ?_) ihb
    fuel env1 env2 hag trivial
  obtain ⟨o, h1, h2⟩ := atom_runT bt n hxa h
  exact ⟨o, h1, h2⟩

end Loops

/-! ## The rewritten expression -/

section Fn

variable {bt : TreeTable E} {g : String}

/-- The hypothesis `WtIHT` of the rewriting of an expression of `wtOk g`. -/
theorem wtFn_ihT (e : ImpExpr) (h : wtOk g e = true) : WtIHT h₁ bt g e := by
  induction e using ImpExpr.ind with
  | letBind n v b _ ihb =>
    simp only [wtOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact letBind_relT h.1.1 h.1.2 (ihb h.2)
  | seq a b iha ihb =>
    simp only [wtOk, Bool.and_eq_true] at h
    exact seq_relT (iha h.1) (ihb h.2)
  | ifThenElse cnd t e _ iht ihe =>
    cases cnd with
    | var x =>
      simp only [wtOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact ifThenElse_relT h.1.1 (iht h.1.2) (ihe h.2)
    | _ => simp [wtOk, valOk, rhsOk, atomOk] at h
  | forFold i lo hi b _ _ ihb =>
    simp only [wtOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    exact forFold_relT h.1.1.1 h.1.1.2 h.1.2 (ihb h.2)
  | whileFold c b _ ihb =>
    cases c with
    | lit l =>
      cases l with
      | bool bv =>
        cases bv with
        | true => exact whileTrue_relT (ihb (by simpa [wtOk] using h))
        | false => simp [wtOk, valOk, rhsOk, atomOk] at h
      | _ => simp [wtOk, valOk, rhsOk, atomOk] at h
    | var x =>
      simp only [wtOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact whileVar_relT h.1 (ihb h.2)
    | _ => simp [wtOk, valOk, rhsOk, atomOk] at h
  | whileFoldReturn c b _ ihb =>
    cases c with
    | lit l =>
      cases l with
      | bool bv =>
        cases bv with
        | true => exact whileTrueR_relT (ihb (by simpa [wtOk] using h))
        | false => simp [wtOk, valOk, rhsOk, atomOk] at h
      | _ => simp [wtOk, valOk, rhsOk, atomOk] at h
    | var x =>
      simp only [wtOk, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      exact whileVarR_relT h.1 (ihb h.2)
    | _ => simp [wtOk, valOk, rhsOk, atomOk] at h
  | cfBreak a _ => exact cfBreak_relT (by simpa [wtOk] using h)
  | var x => exact val_relT (by simpa [wtOk] using h) rfl
  | lit l => exact val_relT (by simpa [wtOk] using h) rfl
  | unitVal => exact val_relT (by simpa [wtOk] using h) rfl
  | app f args _ => exact val_relT (by simpa [wtOk] using h) rfl
  | tuple es _ => exact val_relT (by simpa [wtOk] using h) rfl
  | _ => simp [wtOk, valOk, rhsOk, atomOk] at h

end Fn

/-- **The call trees of an expression and of its rewriting.** For an expression of `wtOk g`, from
    environments agreeing off `g`, the call tree of the rewritten expression has the events of
    the call tree of the expression, and its leaves end in the outcome of the expression, in an
    environment agreeing off `g`, with `g` kept bound to `true`. -/
theorem wtFn_relT (h₁ : ∀ e : E.Event, E.Resp e) (bt : TreeTable E) {g : String} {e : ImpExpr}
    (h : wtOk g e = true) (fuel : Nat) (env1 env2 : Env) (hag : AgreeOff g env1 env2) :
    RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
      (fun r₁ r₂ => WtRel g env2 r₁ r₂) (fun _ => False)
      (denoteT bt fuel e env1) (denoteT bt fuel (wtFn g e) env2) :=
  wtFn_ihT e h fuel env1 env2 hag

/-- **The call trees of an expression and of its rewriting from one environment.** The leaves end
    in the same outcome. -/
theorem wtFn_relT_same (h₁ : ∀ e : E.Event, E.Resp e) (bt : TreeTable E) {g : String}
    {e : ImpExpr} (h : wtOk g e = true) (fuel : Nat) (env : Env) :
    RuttS h₁ (fun e₁ e₂ => e₁ = e₂) (fun _ _ a₁ a₂ => a₁ ≍ a₂)
      (fun r₁ r₂ => r₂.1 = r₁.1) (fun _ => False)
      (denoteT bt fuel e env) (denoteT bt fuel (wtFn g e) env) :=
  NFProgCallTreeExt.RuttS.mono (fun _ _ s => s.out)
    (wtFn_relT h₁ bt h fuel env env (fun _ _ => rfl))

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeWhileTrue
