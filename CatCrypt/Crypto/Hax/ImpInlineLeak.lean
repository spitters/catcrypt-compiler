/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpInline
public import CatCrypt.Crypto.Hax.ImpToNFLeak
public import CatCrypt.Crypto.Hax.NFInline

/-!
# The source leakage of the inlining of a crate

The source leakage `srcLeakNF` of the term `inlineCrate fs n e` is related to the source
leakage of `e` run at the builtins with the crate. At a call of a function of the crate,
`srcLeakNF` leaves the event `op (callLeak f vals)` of the call on the argument values; in
the inlined term the call is the call block of the body of the function, whose leakage is the
leakage of the arguments followed by the leakage of the body.

`srcLeakCl bi cl` (`ImpToNFLeak`) is the source leakage with the leakage of a call `f` on the
values `vals` given by `cl f vals`; `srcLeakNF bi` is `srcLeakCl bi nfCallLeak`. The expanded
call leakage `expLeak fs bi fuelC n` gives, at the depth
`n + 1`, a call of a function `c` of `fs` the leakage of the run of its body at the depth `n`
and the fuel `fuelC` from the environment of its parameters, and every other call the event
of `srcLeakNF`. `srcLeakX fs bi fuelC n` is the source leakage at the builtins with the crate
`crateBi fs bi fuelC n` with the expanded call leakage.

## Main definitions

* `expLeak`, `srcLeakX` — the expanded call leakage of a crate and the source leakage with it.
* `expCallLeak` — the expanded call leakage as a call leakage `CallLeak`.
* `TraceEq` — equal events `nfTrace` of two leakages from related environments, on the runs
  of a computation that do not end in a bad result.

## Main results

* `args_leak`, `forLeak_off`, `forRevLeak_off` — the events of the arguments of a call and
  of the trips of a counted loop, at a fuel offset.
* `xf_leak`, `callBlock_leak`, `inl_leak` — the events of the transformation, of a call
  block and of the inliner, under the relations `InlRel`.
* `inlineCrate_srcLeak` — for a term `e` accepted by `inlOk fs n` and a run of `e` at the
  builtins with the crate that does not end in an error, the events `nfTrace` of the source
  leakage of `inlineCrate fs n e` at the builtins `bi` and the fuel `F + D` are those of
  `srcLeakX fs bi fuelC n e F`, for `D ≥ n * fuelC`.
* `expCallLeak_agrees`, `impToNF_leak_inlineCrate` — the program `impToNF` emits for `e` at
  the builtins with the crate, run with the expanded call leakage `expCallLeak`, has the
  events `nfTrace` of the source leakage of `inlineCrate fs n e`.
* `crateOp_leak`, `crateLib_leakSoundStep` — a call of a function of the crate at the depth
  `m + 1` with its expanded events is a leakage run of its body at the depth `m`.
* `nfLeakRunE_inline?_crate`, `nfLeakRunE_inlineIter_crate`, `nfLeakRun_inlineIter_crate` — a
  round, and the rounds, of the NF inlining at the library of the crate keep the leakage run
  with the expanded call leakage, down to the leakage run `nfLeakRun` at the builtins `bi`
  under `crateInlineOk`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.ImpInline

open _root_.Hax (ImpExpr ImpLit Value Env Builtins Outcome denote' denoteArgs' denoteApp'
  denoteForLoop' denoteForLoopRev')
open _root_.Hax.InlineLocalClosures (RefR RefE IsErr run_bind)
open _root_.Hax.ContinueFlag (letBind_run seq_run ifThenElse_run app_run args_cons_run
  forLoop_succ_run forLoop_zero_run)
open CatCrypt.Crypto.Hax (SrcLeak SrcEv contLeak boundsLeak forLeak forRevLeak tripCont
  boundInt)
open CatCrypt.Crypto.Hax.ImpToNF (CrateFn crateBi paramsEnv crateBi_of_find_none srcLeakNF
  srcArgsLeakNF srcLeakCl srcArgsLeakCl nfCallLeak nfTrace nfEv callLeak CallLeak nfLeakRunE
  impToNF_leakE_all impToNF TypedCalls Out NfEnv EnvRel enc encAll RepeatCalls crateBi_repeatCalls)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Valuation)

/-! ## The expanded call leakage -/

/-- **The expanded call leakage of a crate** at the depth `n`: at the depth `n + 1`, a call
    of a function `c` of `fs` on the values `vals` leaks the leakage `srcLeakCl` of the run of
    its body at the builtins `crateBi fs bi fuelC n` and the fuel `fuelC` from the environment
    of its parameters, with the expanded call leakage of the depth `n`; every other call leaks
    the event `op (callLeak f vals)` of `srcLeakNF`. -/
def expLeak (fs : List CrateFn) (bi : Builtins) (fuelC : Nat) :
    Nat → String → List Value → SrcLeak
  | 0, f, vals => .ev (.op (callLeak f vals))
  | n + 1, f, vals =>
      match fs.find? (·.name == f) with
      | some c => srcLeakCl (crateBi fs bi fuelC n) (expLeak fs bi fuelC n) c.body fuelC
          (paramsEnv (c.params.map (·.1)) vals)
      | none => .ev (.op (callLeak f vals))

/-- **The source leakage with the expanded calls of a crate**: the leakage `srcLeakCl` at the
    builtins with the crate `crateBi fs bi fuelC n` and the expanded call leakage of the
    depth `n`. -/
def srcLeakX (fs : List CrateFn) (bi : Builtins) (fuelC n : Nat) (e : ImpExpr) (fuel : Nat)
    (env : Env) : SrcLeak :=
  srcLeakCl (crateBi fs bi fuelC n) (expLeak fs bi fuelC n) e fuel env

theorem expLeak_of_find_none (fs : List CrateFn) (bi : Builtins) (fuelC : Nat) {f : String}
    (hf : fs.find? (·.name == f) = none) (n : Nat) (vals : List Value) :
    expLeak fs bi fuelC n f vals = .ev (.op (callLeak f vals)) := by
  cases n with
  | zero => rfl
  | succ n => simp only [expLeak, hf]

/-! ## Equal events -/

/-- **Equal events of two leakages** from environments related by `R`, on the runs of `m`
    from the right environment that do not end in a `bad` result. -/
def TraceEq {α : Type} (R : Env → Env → Prop) (bad : α → Prop) (L₁ L₂ : Env → SrcLeak)
    (m : StateM Env α) : Prop :=
  ∀ e₁ e₂, R e₁ e₂ → ¬ bad (m.run e₂).1 → nfTrace (L₁ e₁) = nfTrace (L₂ e₂)

theorem nfTrace_cat (a b : SrcLeak) : nfTrace (.cat a b) = nfTrace a ++ nfTrace b := rfl

/-- The events after a part that ran to the same outcome are equal when the continuations
    have equal events at every value that is not a control-flow value. -/
theorem contLeak_trace {o : Outcome} {s₁ s₂ : Env} {k₁ k₂ : Value → Env → SrcLeak}
    (h : ∀ w, o = .val w → (∀ b u, w ≠ .controlFlow b u) →
      nfTrace (k₁ w s₁) = nfTrace (k₂ w s₂)) :
    nfTrace (contLeak (o, s₁) k₁) = nfTrace (contLeak (o, s₂) k₂) := by
  cases o with
  | val w =>
    cases w <;> first
      | rfl
      | exact h _ rfl (fun b u hh => by cases hh)
  | _ => rfl

/-- The events after a loop trip that ran to the same outcome are equal when the
    continuations have equal events after every value that does not end the loop. -/
theorem tripCont_trace {o : Outcome} {s₁ s₂ : Env} {k₁ k₂ : Env → SrcLeak}
    (h : ∀ w, o = .val w → (∀ u, w ≠ .controlFlow true u) → nfTrace (k₁ s₁) = nfTrace (k₂ s₂)) :
    nfTrace (tripCont (o, s₁) k₁) = nfTrace (tripCont (o, s₂) k₂) := by
  cases o with
  | val w =>
    cases w with
    | controlFlow b u =>
      cases b
      · exact h _ rfl (fun u hh => by cases hh)
      · rfl
    | _ => exact h _ rfl (fun u hh => by cases hh)
  | _ => rfl

/-- The leakage of the bounds of a counted loop, with the leakage after the lower bound as a
    continuation `contLeak`. -/
theorem boundsLeak_eq (bi : Builtins) (lo hi : ImpExpr) (llo lhi : Env → SrcLeak) (fuel : Nat)
    (trips : Int → Int → Env → SrcLeak) (env : Env) :
    boundsLeak bi lo hi llo lhi fuel trips env =
      .cat (llo env) (contLeak ((denote' bi fuel lo).run env) fun vlo e1 =>
        .cat (lhi e1)
          (match (denote' bi fuel hi).run e1 with
           | (.val vhi, e2) =>
             match boundInt vlo, boundInt vhi with
             | some l, some h => .cat (.ev (.bound l h)) (trips l h e2)
             | _, _ => .nil
           | _ => .nil)) := rfl

/-! ## The runs of a counted loop -/

theorem forFold_run_lo {bi : Builtins} {F : Nat} {i : String} {lo hi b : ImpExpr} {e e1 : Env}
    {o : Outcome} (hlo : (denote' bi F lo).run e = (o, e1)) (ho : ∀ w, o ≠ .val w) :
    (denote' bi F (.forFold i lo hi b)).run e = (o, e1) := by
  simp only [StateT.run] at hlo
  cases o <;> first
    | exact absurd rfl (ho _)
    | (simp only [denote', StateT.run, bind, StateT.bind, hlo]; rfl)

theorem forFold_run_hi {bi : Builtins} {F : Nat} {i : String} {lo hi b : ImpExpr}
    {e e1 e2 : Env} {vlo : Value} {o : Outcome} (hlo : (denote' bi F lo).run e = (.val vlo, e1))
    (hcf : ∀ b u, vlo ≠ .controlFlow b u) (hhi : (denote' bi F hi).run e1 = (o, e2))
    (ho : ∀ w, o ≠ .val w) :
    (denote' bi F (.forFold i lo hi b)).run e = (o, e2) := by
  simp only [StateT.run] at hlo hhi
  cases o <;> first | exact absurd rfl (ho _) |
    (cases vlo <;> first | exact absurd rfl (hcf _ _) |
      (simp only [denote', StateT.run, bind, StateT.bind, hlo, hhi]; rfl))

theorem forFold_run_loop {bi : Builtins} {F : Nat} {i : String} {lo hi b : ImpExpr}
    {e e1 e2 : Env} {vlo vhi : Value} {l h : Int}
    (hlo : (denote' bi F lo).run e = (.val vlo, e1))
    (hhi : (denote' bi F hi).run e1 = (.val vhi, e2))
    (hl : boundInt vlo = some l) (hh : boundInt vhi = some h) :
    (denote' bi F (.forFold i lo hi b)).run e = (denoteForLoop' bi F i l h b).run e2 := by
  simp only [StateT.run] at hlo hhi
  cases vlo <;> simp only [boundInt, reduceCtorEq, Option.some.injEq] at hl <;>
    cases vhi <;> simp only [boundInt, reduceCtorEq, Option.some.injEq] at hh <;>
    subst hl hh <;> simp only [denote', StateT.run, bind, StateT.bind, hlo, hhi]

theorem forFoldRev_run_lo {bi : Builtins} {F : Nat} {i : String} {lo hi b : ImpExpr}
    {e e1 : Env} {o : Outcome} (hlo : (denote' bi F lo).run e = (o, e1))
    (ho : ∀ w, o ≠ .val w) :
    (denote' bi F (.forFoldRev i lo hi b)).run e = (o, e1) := by
  simp only [StateT.run] at hlo
  cases o <;> first
    | exact absurd rfl (ho _)
    | (simp only [denote', StateT.run, bind, StateT.bind, hlo]; rfl)

theorem forFoldRev_run_hi {bi : Builtins} {F : Nat} {i : String} {lo hi b : ImpExpr}
    {e e1 e2 : Env} {vlo : Value} {o : Outcome} (hlo : (denote' bi F lo).run e = (.val vlo, e1))
    (hcf : ∀ b u, vlo ≠ .controlFlow b u) (hhi : (denote' bi F hi).run e1 = (o, e2))
    (ho : ∀ w, o ≠ .val w) :
    (denote' bi F (.forFoldRev i lo hi b)).run e = (o, e2) := by
  simp only [StateT.run] at hlo hhi
  cases o <;> first | exact absurd rfl (ho _) |
    (cases vlo <;> first | exact absurd rfl (hcf _ _) |
      (simp only [denote', StateT.run, bind, StateT.bind, hlo, hhi]; rfl))

theorem forFoldRev_run_loop {bi : Builtins} {F : Nat} {i : String} {lo hi b : ImpExpr}
    {e e1 e2 : Env} {vlo vhi : Value} {l h : Int}
    (hlo : (denote' bi F lo).run e = (.val vlo, e1))
    (hhi : (denote' bi F hi).run e1 = (.val vhi, e2))
    (hl : boundInt vlo = some l) (hh : boundInt vhi = some h) :
    (denote' bi F (.forFoldRev i lo hi b)).run e = (denoteForLoopRev' bi F i l h b).run e2 := by
  simp only [StateT.run] at hlo hhi
  cases vlo <;> simp only [boundInt, reduceCtorEq, Option.some.injEq] at hl <;>
    cases vhi <;> simp only [boundInt, reduceCtorEq, Option.some.injEq] at hh <;>
    subst hl hh <;> simp only [denote', StateT.run, bind, StateT.bind, hlo, hhi]

theorem forLoopRev_zero_run (bi : Builtins) (i : String) (lo hi : Int) (body : ImpExpr)
    (env : Env) (h : lo < hi) :
    (denoteForLoopRev' bi 0 i lo hi body).run env = (.err "out of fuel", env) := by
  rw [denoteForLoopRev', if_neg (Int.not_le.mpr h), if_pos rfl]; rfl

theorem forLoopRev_succ_run (bi : Builtins) (n : Nat) (i : String) (lo hi : Int)
    (body : ImpExpr) (env : Env) (h : lo < hi) :
    (denoteForLoopRev' bi (n + 1) i lo hi body).run env =
      match (denote' bi (n + 1) body).run (env.extend i (.int (hi - 1))) with
      | (.val (.controlFlow true v), e2) => (.val v, e2)
      | (.val (.controlFlow false _), e2) => (denoteForLoopRev' bi n i lo (hi - 1) body).run e2
      | (.val _, e2) => (denoteForLoopRev' bi n i lo (hi - 1) body).run e2
      | (o, e2) => (o, e2) := by
  rw [denoteForLoopRev', if_neg (Int.not_le.mpr h)]
  simp only [Nat.add_one_ne_zero, if_false, StateT.run, bind, StateT.bind, pure, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Nat.add_sub_cancel]
  rcases (denote' bi (n + 1) body) (env.extend i (.int (hi - 1))) with ⟨o2, e2⟩
  rcases o2 with v2 | _ | _ | _ | _ <;> try rfl
  cases v2 with
  | controlFlow k w => cases k <;> rfl
  | _ => rfl

/-! ## The arguments and the counted loops -/

section Steps

variable {R : Env → Env → Prop} {bi₁ bi₂ : Builtins} {cl : String → List Value → SrcLeak}

/-- **The events of the arguments** of a call, transformed by `g`, when each argument
    refines and has equal events. -/
theorem args_leak (g : ImpExpr → ImpExpr) (args : List ImpExpr) (F₁ F₂ : Nat)
    (ihR : ∀ a, a ∈ args → RefE R (denote' bi₁ F₁ (g a)) (denote' bi₂ F₂ a))
    (ihL : ∀ a, a ∈ args → TraceEq R IsErr (srcLeakNF bi₁ (g a) F₁) (srcLeakCl bi₂ cl a F₂)
      (denote' bi₂ F₂ a)) :
    TraceEq R (fun o => o = none) (srcArgsLeakNF bi₁ (args.map g) F₁)
      (srcArgsLeakCl bi₂ cl args F₂) (denoteArgs' bi₂ F₂ args) := by
  induction args with
  | nil => intro _ _ _ _; rfl
  | cons a as iha =>
    intro e₁ e₂ hP hnb
    simp only [List.map_cons, srcArgsLeakNF, srcArgsLeakCl, nfTrace_cat]
    rw [args_cons_run] at hnb
    generalize ha : (denote' bi₂ F₂ a).run e₂ = A at hnb
    obtain ⟨oa, sa⟩ := A
    have hoa : ¬ IsErr oa := by rintro ⟨m, rfl⟩; exact hnb rfl
    obtain ⟨s₁, ha₁, hs⟩ := ihR a List.mem_cons_self e₁ e₂ hP oa sa ha hoa
    rw [ihL a List.mem_cons_self e₁ e₂ hP (by rw [ha]; exact hoa), ha₁]
    congr 1
    refine contLeak_trace fun w hw hcf => ?_
    subst hw
    refine iha (fun b hb => ihR b (List.mem_cons_of_mem a hb))
      (fun b hb => ihL b (List.mem_cons_of_mem a hb)) s₁ sa hs ?_
    intro hn
    apply hnb
    cases w <;> first | exact absurd rfl (hcf _ _) | simp [hn]

/-- **The events of the trips of a counted loop** at the fuel offset `D`. -/
theorem forLeak_off {v₁ v₂ : String} {b₁ b₂ : ImpExpr} {D : Nat}
    {lb₁ lb₂ : Nat → Env → SrcLeak}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v₁ w) (e₂.extend v₂ w))
    (h : ∀ F, RefE R (denote' bi₁ (F + D) b₁) (denote' bi₂ F b₂))
    (hL : ∀ F, TraceEq R IsErr (lb₁ (F + D)) (lb₂ F) (denote' bi₂ F b₂)) :
    ∀ F lo hi, TraceEq R IsErr (forLeak bi₁ v₁ b₁ lb₁ (F + D) lo hi)
      (forLeak bi₂ v₂ b₂ lb₂ F lo hi) (denoteForLoop' bi₂ F v₂ lo hi b₂) := by
  intro F
  induction F with
  | zero =>
    intro lo hi e₁ e₂ hP hnb
    by_cases hl : lo ≥ hi
    · rw [Nat.zero_add]
      cases D with
      | zero => rfl
      | succ k => simp only [forLeak, hl, if_true]
    · rw [forLoop_zero_run _ _ _ _ _ _ (by omega)] at hnb
      exact absurd ⟨_, rfl⟩ hnb
  | succ n ih =>
    intro lo hi e₁ e₂ hP hnb
    have hfu : n + 1 + D = n + D + 1 := by omega
    by_cases hl : lo ≥ hi
    · rw [hfu]; simp only [forLeak, hl, if_true]
    · rw [forLoop_succ_run _ _ _ _ _ _ _ (by omega)] at hnb
      rw [hfu]
      simp only [forLeak, hl, if_false, nfTrace_cat]
      generalize hb : (denote' bi₂ (n + 1) b₂).run (e₂.extend v₂ (.int lo)) = B at hnb
      obtain ⟨ob, sb⟩ := B
      have hob : ¬ IsErr ob := by rintro ⟨m, rfl⟩; exact hnb ⟨_, rfl⟩
      have hP' := hv e₁ e₂ (.int lo) hP
      obtain ⟨s₁, hb₁, hs⟩ := h (n + 1) _ _ hP' ob sb hb hob
      rw [← hfu, hL (n + 1) _ _ hP' (by rw [hb]; exact hob), hb₁]
      congr 1
      refine tripCont_trace fun w hw hcf => ?_
      subst hw
      refine ih (lo + 1) hi s₁ sb hs ?_
      cases w with
      | controlFlow k u =>
        cases k
        · exact hnb
        · exact absurd rfl (hcf u)
      | _ => exact hnb

/-- **The events of the trips of a counted loop counting down** at the fuel offset `D`. -/
theorem forRevLeak_off {v₁ v₂ : String} {b₁ b₂ : ImpExpr} {D : Nat}
    {lb₁ lb₂ : Nat → Env → SrcLeak}
    (hv : ∀ e₁ e₂ w, R e₁ e₂ → R (e₁.extend v₁ w) (e₂.extend v₂ w))
    (h : ∀ F, RefE R (denote' bi₁ (F + D) b₁) (denote' bi₂ F b₂))
    (hL : ∀ F, TraceEq R IsErr (lb₁ (F + D)) (lb₂ F) (denote' bi₂ F b₂)) :
    ∀ F lo hi, TraceEq R IsErr (forRevLeak bi₁ v₁ b₁ lb₁ (F + D) lo hi)
      (forRevLeak bi₂ v₂ b₂ lb₂ F lo hi) (denoteForLoopRev' bi₂ F v₂ lo hi b₂) := by
  intro F
  induction F with
  | zero =>
    intro lo hi e₁ e₂ hP hnb
    by_cases hl : lo ≥ hi
    · rw [Nat.zero_add]
      cases D with
      | zero => rfl
      | succ k => simp only [forRevLeak, hl, if_true]
    · rw [forLoopRev_zero_run _ _ _ _ _ _ (by omega)] at hnb
      exact absurd ⟨_, rfl⟩ hnb
  | succ n ih =>
    intro lo hi e₁ e₂ hP hnb
    have hfu : n + 1 + D = n + D + 1 := by omega
    by_cases hl : lo ≥ hi
    · rw [hfu]; simp only [forRevLeak, hl, if_true]
    · rw [forLoopRev_succ_run _ _ _ _ _ _ _ (by omega)] at hnb
      rw [hfu]
      simp only [forRevLeak, hl, if_false, nfTrace_cat]
      generalize hb : (denote' bi₂ (n + 1) b₂).run (e₂.extend v₂ (.int (hi - 1))) = B at hnb
      obtain ⟨ob, sb⟩ := B
      have hob : ¬ IsErr ob := by rintro ⟨m, rfl⟩; exact hnb ⟨_, rfl⟩
      have hP' := hv e₁ e₂ (.int (hi - 1)) hP
      obtain ⟨s₁, hb₁, hs⟩ := h (n + 1) _ _ hP' ob sb hb hob
      rw [← hfu, hL (n + 1) _ _ hP' (by rw [hb]; exact hob), hb₁]
      congr 1
      refine tripCont_trace fun w hw hcf => ?_
      subst hw
      refine ih lo (hi - 1) s₁ sb hs ?_
      cases w with
      | controlFlow k u =>
        cases k
        · exact hnb
        · exact absurd rfl (hcf u)
      | _ => exact hnb

/-- **The events of a call** whose call leakage is the event of `srcLeakNF`, on arguments
    that refine and have equal events. -/
theorem app_leak {g : String}
    (hcl : ∀ vals, cl g vals = .ev (.op (callLeak g vals))) {F₁ F₂ : Nat}
    {args₁ args₂ : List ImpExpr}
    (hargs : RefR R R (fun o => o = none) (denoteArgs' bi₁ F₁ args₁) (denoteArgs' bi₂ F₂ args₂))
    (hargsL : TraceEq R (fun o => o = none) (srcArgsLeakNF bi₁ args₁ F₁)
      (srcArgsLeakCl bi₂ cl args₂ F₂) (denoteArgs' bi₂ F₂ args₂)) :
    TraceEq R IsErr (srcLeakNF bi₁ (.app g args₁) F₁) (srcLeakCl bi₂ cl (.app g args₂) F₂)
      (denote' bi₂ F₂ (.app g args₂)) := by
  intro e₁ e₂ hP hnb
  rw [app_run] at hnb
  generalize hA : (denoteArgs' bi₂ F₂ args₂).run e₂ = A at hnb
  obtain ⟨mv, s₂⟩ := A
  cases mv with
  | none => exact absurd ⟨_, rfl⟩ hnb
  | some vals =>
    obtain ⟨s₁, hA₁, -⟩ := hargs e₁ e₂ hP (some vals) s₂ hA (by simp)
    simp only [srcLeakNF, srcLeakCl, nfTrace_cat, hA, hA₁, hcl, nfCallLeak]
    rw [hargsL e₁ e₂ hP (by rw [hA]; simp)]

end Steps

/-! ## The events of the transformation -/

/-- **The transformation has the events of the source term** under `InlRel`, at the fuel
    offset `D`, when the site function refines each call the check `call` accepts and has
    its events, on arguments that refine and have equal events. -/
theorem xf_leak {bi B : Builtins} {n : Nat} {ρ : String → String} {R : Env → Env → Prop}
    (hR : InlRel n ρ R) {D : Nat} {site : String → List ImpExpr → Option ImpExpr}
    {call : String → List ImpExpr → Bool} {cl : String → List Value → SrcLeak}
    (hsite : ∀ g args args' F, call g args = true →
      RefR R R (fun o => o = none) (denoteArgs' bi (F + D) args') (denoteArgs' B F args) →
      RefE R (denote' bi (F + D) ((site g args').getD (.app g args'))) (denote' B F (.app g args)))
    (hsiteL : ∀ g args args' F, call g args = true →
      RefR R R (fun o => o = none) (denoteArgs' bi (F + D) args') (denoteArgs' B F args) →
      TraceEq R (fun o => o = none) (srcArgsLeakNF bi args' (F + D)) (srcArgsLeakCl B cl args F)
        (denoteArgs' B F args) →
      TraceEq R IsErr (srcLeakNF bi ((site g args').getD (.app g args')) (F + D))
        (srcLeakCl B cl (.app g args) F) (denote' B F (.app g args))) :
    ∀ e, okX call e = true → ∀ F, TraceEq R IsErr (srcLeakNF bi (xf ρ site e) (F + D))
      (srcLeakCl B cl e F) (denote' B F e) := by
  intro e
  induction e using ImpExpr.ind with
  | lit l => intro _ F _ _ _ _; rfl
  | unitVal => intro _ F _ _ _ _; rfl
  | var x => intro _ F _ _ _ _; rfl
  | letBind x v b ihv ihb =>
    intro hK F e₁ e₂ hP hnb
    simp only [okX, Bool.and_eq_true] at hK
    simp only [xf, srcLeakNF, srcLeakCl, nfTrace_cat]
    rw [letBind_run] at hnb
    generalize hv : (denote' B F v).run e₂ = A at hnb
    obtain ⟨ov, sv⟩ := A
    have hov : ¬ IsErr ov := by rintro ⟨m, rfl⟩; exact hnb ⟨m, rfl⟩
    obtain ⟨s₁, hv₁, hs⟩ := xf_ref hR hsite v hK.1.2 F e₁ e₂ hP ov sv hv hov
    rw [ihv hK.1.2 F e₁ e₂ hP (by rw [hv]; exact hov), hv₁]
    congr 1
    refine contLeak_trace fun w hw hcf => ?_
    subst hw
    refine ihb hK.2 F _ _ (hR.ext _ _ x w hs hK.1.1) ?_
    cases w <;> first | exact absurd rfl (hcf _ _) | exact hnb
  | assign x r ih =>
    intro hK F e₁ e₂ hP hnb
    simp only [okX, Bool.and_eq_true] at hK
    simp only [xf, srcLeakNF, srcLeakCl]
    refine ih hK.2 F e₁ e₂ hP ?_
    intro ho
    apply hnb
    obtain ⟨m, hm⟩ := ho
    simp only [denote', StateT.run, bind, StateT.bind] at hm ⊢
    revert hm
    generalize denote' B F r e₂ = q
    obtain ⟨o, s⟩ := q
    rintro hm
    simp only at hm
    subst hm
    exact ⟨m, rfl⟩
  | app g args ih =>
    intro hK F
    simp only [okX, okX.okXList_eq, List.all_eq_true, Bool.and_eq_true] at hK
    simp only [xf, xf.xfList_eq]
    exact hsiteL g args _ F hK.2
      (args_off _ args _ _ fun a ha => xf_ref hR hsite a (hK.1 a ha) F)
      (args_leak _ args _ _ (fun a ha => xf_ref hR hsite a (hK.1 a ha) F)
        (fun a ha => ih a ha (hK.1 a ha) F))
  | tuple es ih =>
    intro hK F e₁ e₂ hP hnb
    simp only [okX, okX.okXList_eq, List.all_eq_true] at hK
    simp only [xf, xf.xfList_eq, srcLeakNF, srcLeakCl]
    refine args_leak _ es _ _ (fun a ha => xf_ref hR hsite a (hK a ha) F)
      (fun a ha => ih a ha (hK a ha) F) e₁ e₂ hP ?_
    intro hn
    apply hnb
    rw [_root_.Hax.InlineLocalClosures.tuple_run]
    generalize (denoteArgs' B F es).run e₂ = A at hn
    obtain ⟨o, s⟩ := A
    simp only at hn
    subst hn
    exact ⟨_, rfl⟩
  | ifThenElse c t e ihc iht ihe =>
    intro hK F e₁ e₂ hP hnb
    simp only [okX, Bool.and_eq_true] at hK
    simp only [xf, srcLeakNF, srcLeakCl, nfTrace_cat]
    rw [ifThenElse_run] at hnb
    generalize hc : (denote' B F c).run e₂ = A at hnb
    obtain ⟨oc, sc⟩ := A
    have hoc : ¬ IsErr oc := by rintro ⟨m, rfl⟩; exact hnb ⟨m, rfl⟩
    obtain ⟨s₁, hc₁, hs⟩ := xf_ref hR hsite c hK.1.1 F e₁ e₂ hP oc sc hc hoc
    rw [ihc hK.1.1 F e₁ e₂ hP (by rw [hc]; exact hoc), hc₁]
    congr 1
    cases oc with
    | val w =>
      cases w with
      | bool bb =>
        cases bb
        · simp only [nfTrace_cat]
          rw [ihe hK.2 F s₁ sc hs hnb]
        · simp only [nfTrace_cat]
          rw [iht hK.1.2 F s₁ sc hs hnb]
      | _ => rfl
    | _ => rfl
  | seq a b iha ihb =>
    intro hK F e₁ e₂ hP hnb
    simp only [okX, Bool.and_eq_true] at hK
    simp only [xf, srcLeakNF, srcLeakCl, nfTrace_cat]
    rw [seq_run] at hnb
    generalize ha : (denote' B F a).run e₂ = A at hnb
    obtain ⟨oa, sa⟩ := A
    have hoa : ¬ IsErr oa := by rintro ⟨m, rfl⟩; exact hnb ⟨m, rfl⟩
    obtain ⟨s₁, ha₁, hs⟩ := xf_ref hR hsite a hK.1 F e₁ e₂ hP oa sa ha hoa
    rw [iha hK.1 F e₁ e₂ hP (by rw [ha]; exact hoa), ha₁]
    congr 1
    refine contLeak_trace fun w hw hcf => ?_
    subst hw
    refine ihb hK.2 F _ _ hs ?_
    cases w <;> first | exact absurd rfl (hcf _ _) | exact hnb
  | typeAscription e s ih =>
    intro hK F e₁ e₂ hP hnb
    simp only [okX] at hK
    simp only [xf, srcLeakNF, srcLeakCl]
    exact ih hK F e₁ e₂ hP (by simpa only [denote'] using hnb)
  | forFold i lo hi b ihl ihh ihb =>
    intro hK F e₁ e₂ hP hnb
    simp only [okX, Bool.and_eq_true] at hK
    simp only [xf, srcLeakNF, srcLeakCl]
    rw [boundsLeak_eq, boundsLeak_eq, nfTrace_cat, nfTrace_cat]
    generalize hlo : (denote' B F lo).run e₂ = A
    obtain ⟨olo, slo⟩ := A
    have holo : ¬ IsErr olo := by
      rintro ⟨m, rfl⟩
      exact hnb (by rw [forFold_run_lo hlo (fun _ h => by cases h)]; exact ⟨m, rfl⟩)
    obtain ⟨s₁, hlo₁, hs⟩ := xf_ref hR hsite lo hK.1.1.2 F e₁ e₂ hP olo slo hlo holo
    rw [ihl hK.1.1.2 F e₁ e₂ hP (by rw [hlo]; exact holo), hlo₁]
    congr 1
    refine contLeak_trace fun vlo hw hcf' => ?_
    subst hw
    simp only [nfTrace_cat]
    generalize hhi : (denote' B F hi).run slo = A
    obtain ⟨ohi, shi⟩ := A
    have hohi : ¬ IsErr ohi := by
      rintro ⟨m, rfl⟩
      exact hnb (by rw [forFold_run_hi hlo hcf' hhi (fun _ h => by cases h)]; exact ⟨m, rfl⟩)
    obtain ⟨s₂, hhi₁, hs₂⟩ := xf_ref hR hsite hi hK.1.2 F s₁ slo hs ohi shi hhi hohi
    rw [ihh hK.1.2 F s₁ slo hs (by rw [hhi]; exact hohi), hhi₁]
    congr 1
    cases ohi with
    | val vhi =>
      simp only
      cases hl : boundInt vlo with
      | none => rfl
      | some l =>
        cases hh : boundInt vhi with
        | none => rfl
        | some h =>
          simp only [nfTrace_cat]
          congr 1
          refine forLeak_off (fun e₁ e₂ w h => hR.ext e₁ e₂ i w h hK.1.1.1)
            (fun F => xf_ref hR hsite b hK.2 F) (fun F => ihb hK.2 F) F l h s₂ shi hs₂ ?_
          rwa [← forFold_run_loop hlo hhi hl hh]
    | _ => rfl
  | forFoldRev i lo hi b ihl ihh ihb =>
    intro hK F e₁ e₂ hP hnb
    simp only [okX, Bool.and_eq_true] at hK
    simp only [xf, srcLeakNF, srcLeakCl]
    rw [boundsLeak_eq, boundsLeak_eq, nfTrace_cat, nfTrace_cat]
    generalize hlo : (denote' B F lo).run e₂ = A
    obtain ⟨olo, slo⟩ := A
    have holo : ¬ IsErr olo := by
      rintro ⟨m, rfl⟩
      exact hnb (by rw [forFoldRev_run_lo hlo (fun _ h => by cases h)]; exact ⟨m, rfl⟩)
    obtain ⟨s₁, hlo₁, hs⟩ := xf_ref hR hsite lo hK.1.1.2 F e₁ e₂ hP olo slo hlo holo
    rw [ihl hK.1.1.2 F e₁ e₂ hP (by rw [hlo]; exact holo), hlo₁]
    congr 1
    refine contLeak_trace fun vlo hw hcf' => ?_
    subst hw
    simp only [nfTrace_cat]
    generalize hhi : (denote' B F hi).run slo = A
    obtain ⟨ohi, shi⟩ := A
    have hohi : ¬ IsErr ohi := by
      rintro ⟨m, rfl⟩
      exact hnb (by
        rw [forFoldRev_run_hi hlo hcf' hhi (fun _ h => by cases h)]; exact ⟨m, rfl⟩)
    obtain ⟨s₂, hhi₁, hs₂⟩ := xf_ref hR hsite hi hK.1.2 F s₁ slo hs ohi shi hhi hohi
    rw [ihh hK.1.2 F s₁ slo hs (by rw [hhi]; exact hohi), hhi₁]
    congr 1
    cases ohi with
    | val vhi =>
      simp only
      cases hl : boundInt vlo with
      | none => rfl
      | some l =>
        cases hh : boundInt vhi with
        | none => rfl
        | some h =>
          simp only [nfTrace_cat]
          congr 1
          refine forRevLeak_off (fun e₁ e₂ w h => hR.ext e₁ e₂ i w h hK.1.1.1)
            (fun F => xf_ref hR hsite b hK.2 F) (fun F => ihb hK.2 F) F l h s₂ shi hs₂ ?_
          rwa [← forFoldRev_run_loop hlo hhi hl hh]
    | _ => rfl
  | _ =>
    intro hK
    simp [okX] at hK

/-! ## The call block and the inliner -/

/-- The run and the events of the bindings of the parameters `ps` from the position `i` of
    the tuple bound to `tmpName n`: the run and the events of `b` from an environment that
    reads the level name of each parameter as `paramsEnv` reads the parameter, and agrees
    with the environment before at every name that is not a level name of the level `n`. -/
theorem bindParams_run_leak (bi : Builtins) (F n : Nat) (vals : List Value)
    (hcf : ∀ v ∈ vals, ∀ b w, v ≠ .controlFlow b w) :
    ∀ (ps : List String) (i : Nat) (b : ImpExpr) (e : Env),
      e (tmpName n) = some (.tuple vals) → i + ps.length ≤ vals.length →
      ∃ e', (denote' bi F (bindParams n i ps b)).run e = (denote' bi F b).run e' ∧
        nfTrace (srcLeakNF bi (bindParams n i ps b) F e) = nfTrace (srcLeakNF bi b F e') ∧
        (∀ x v, paramsEnv ps (vals.drop i) x = some v → e' (lvlName n x) = some v) ∧
        (∀ y, (∀ x, y ≠ lvlName n x) → e' y = e y)
  | [], i, b, e, _, _ => ⟨e, rfl, rfl, fun x v h => by simp [paramsEnv] at h, fun _ _ => rfl⟩
  | p :: ps, i, b, e, ht, hl => by
      simp only [List.length_cons] at hl
      obtain ⟨e'', hrun, hleak, hpar, hfr⟩ := bindParams_run_leak bi F n vals hcf ps (i + 1)
        (.letBind (lvlName n p) (.proj (.var (tmpName n)) i) b) e ht (by omega)
      have hi : i < vals.length := by omega
      have ht' : e'' (tmpName n) = some (.tuple vals) := by
        rw [hfr _ (fun x h => lvlName_ne_tmpName n n x h.symm)]; exact ht
      have hproj : (denote' bi F (.proj (.var (tmpName n)) i)).run e'' =
          (.val vals[i], e'') := by
        simp only [denote', StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
          StateT.get, pure, StateT.pure, ht', Value.projIdx, List.getElem?_eq_getElem hi]
      have hv := hcf vals[i] (List.getElem_mem hi)
      refine ⟨e''.extend (lvlName n p) vals[i], ?_, ?_, ?_, ?_⟩
      · rw [bindParams, hrun, Hax.ContinueFlag.letBind_run, hproj]
        generalize vals[i] = v at hv ⊢
        cases v <;> first | rfl | exact absurd rfl (hv _ _)
      · rw [bindParams, hleak]
        simp only [srcLeakNF, srcLeakCl, nfTrace_cat, hproj]
        rw [show nfTrace SrcLeak.nil = [] from rfl, List.nil_append]
        generalize vals[i] = v at hv ⊢
        cases v <;> first | rfl | exact absurd rfl (hv _ _)
      · intro x v hx
        rw [List.drop_eq_getElem_cons hi] at hx
        simp only [paramsEnv] at hx
        by_cases hxp : x = p
        · subst hxp
          simp only [if_true] at hx
          cases hx
          exact Env.extend_same _ _ _
        · rw [if_neg hxp] at hx
          rw [Env.extend_other _ _ _ _ (fun h => hxp (lvlName_inj h).2)]
          exact hpar x v hx
      · intro y hy
        rw [Env.extend_other _ _ _ _ (hy p), hfr y hy]

/-- **The call block has the events of the call** of a function `c` of `fs` at the depth
    `n + 1` with the expanded call leakage, on arguments that refine and have equal events,
    when the inlined body has the events of the body at the depth `n` under every relation
    of the level `n`, for a fuel offset `D ≥ (n + 1) * fuelC`. -/
theorem callBlock_leak {fs : List CrateFn} {bi : Builtins} {fuelC n : Nat} {c : CrateFn}
    {g : String} (hc : fs.find? (·.name == g) = some c) (hg : g ≠ "repeat")
    {R : Env → Env → Prop} {args args' : List ImpExpr}
    (hlen : args.length = c.params.length) {D F : Nat} (hD : (n + 1) * fuelC ≤ D)
    (hargs : RefR R R (fun o => o = none) (denoteArgs' bi (F + D) args')
      (denoteArgs' (crateBi fs bi fuelC (n + 1)) F args))
    (hargsL : TraceEq R (fun o => o = none) (srcArgsLeakNF bi args' (F + D))
      (srcArgsLeakCl (crateBi fs bi fuelC (n + 1)) (expLeak fs bi fuelC (n + 1)) args F)
      (denoteArgs' (crateBi fs bi fuelC (n + 1)) F args))
    (hbodyL : ∀ R', InlRel n (lvlName n) R' → ∀ D', n * fuelC ≤ D' → ∀ F₀,
      TraceEq R' IsErr (srcLeakNF bi (inl fs n (lvlName n) c.body) (F₀ + D'))
        (srcLeakCl (crateBi fs bi fuelC n) (expLeak fs bi fuelC n) c.body F₀)
        (denote' (crateBi fs bi fuelC n) F₀ c.body)) :
    TraceEq R IsErr (srcLeakNF bi (callBlock n (c.params.map (·.1)) args'
        (inl fs n (lvlName n) c.body)) (F + D))
      (srcLeakCl (crateBi fs bi fuelC (n + 1)) (expLeak fs bi fuelC (n + 1)) (.app g args) F)
      (denote' (crateBi fs bi fuelC (n + 1)) F (.app g args)) := by
  intro e₁ e₂ hP hnb
  rw [app_run] at hnb
  generalize hA : (denoteArgs' (crateBi fs bi fuelC (n + 1)) F args).run e₂ = A at hnb
  obtain ⟨mv, e₂'⟩ := A
  cases mv with
  | none => exact absurd ⟨_, rfl⟩ hnb
  | some vals =>
  simp only [crateBi, hc] at hnb
  generalize hB : (denote' (crateBi fs bi fuelC n) fuelC c.body).run
    (paramsEnv (c.params.map (·.1)) vals) = Bd at hnb
  obtain ⟨ob, sb⟩ := Bd
  have hob : ¬ IsErr ob := by
    rintro ⟨m, rfl⟩
    exact hnb ⟨_, rfl⟩
  obtain ⟨e₁', hA₁, -⟩ := hargs e₁ e₂ hP (some vals) e₂' hA (by simp)
  obtain ⟨hvl, hcf⟩ := denoteArgs'_some _ _ args e₂ e₂' vals hA
  have hT : (denote' bi (F + D) (.tuple args')).run e₁ = (.val (.tuple vals), e₁') := by
    simp only [denote']
    rw [run_bind, hA₁]
    rfl
  obtain ⟨eB, -, hleakB, hpar, -⟩ := bindParams_run_leak bi (F + D) n vals hcf
    (c.params.map (·.1)) 0 (inl fs n (lvlName n) c.body)
    (e₁'.extend (tmpName n) (.tuple vals)) (Env.extend_same _ _ _) (by simp [hvl, hlen])
  let R' : Env → Env → Prop := fun a b =>
    (∀ x w, okName x = true → b x = some w → a (lvlName n x) = some w) ∧
      ∀ y, ¬ IsLow (n + 1) y → a y = eB y
  have hR'rel : InlRel n (lvlName n) R' := by
    refine ⟨fun a b x w h hx hb => h.1 x w hx hb, fun a b x w h hx => ⟨?_, ?_⟩,
      fun a a' b h hlo => ⟨?_, ?_⟩⟩
    · intro z u hz hb
      by_cases hzx : z = x
      · subst hzx
        rw [Env.extend_same] at hb ⊢
        exact hb
      · rw [Env.extend_other _ _ _ _ hzx] at hb
        rw [Env.extend_other _ _ _ _ (fun h' => hzx (lvlName_inj h').2)]
        exact h.1 z u hz hb
    · intro y hy
      rw [Env.extend_other _ _ _ _ (fun h' => hy (by rw [h']; exact isLow_lvlName (by omega) x))]
      exact h.2 y hy
    · intro z u hz hb
      rw [hlo _ (not_isLow_lvlName n z)]
      exact h.1 z u hz hb
    · intro y hy
      rw [hlo _ (fun h' => hy (h'.mono (by omega)))]
      exact h.2 y hy
  have hstart : R' eB (paramsEnv (c.params.map (·.1)) vals) :=
    ⟨fun x w _ hb => hpar x w (by simpa using hb), fun _ _ => rfl⟩
  have hDle : n * fuelC ≤ F + D - fuelC := by
    have : (n + 1) * fuelC = n * fuelC + fuelC := Nat.succ_mul n fuelC
    omega
  have hfe : fuelC + (F + D - fuelC) = F + D := by
    have : (n + 1) * fuelC = n * fuelC + fuelC := Nat.succ_mul n fuelC
    omega
  have hbL := hbodyL R' hR'rel (F + D - fuelC) hDle fuelC eB
    (paramsEnv (c.params.map (·.1)) vals) hstart (by rw [hB]; exact hob)
  rw [hfe] at hbL
  rw [callBlock]
  simp only [srcLeakNF, srcLeakCl, nfTrace_cat, hA, hT, contLeak, hg, if_false]
  rw [hargsL e₁ e₂ hP (by rw [hA]; simp), hleakB, hbL]
  simp only [expLeak, hc]

/-- **The inliner has the events of the source term with the expanded calls.** Under a
    relation `InlRel n ρ R`, a term `e` accepted by `inlOk fs n` inlined at the depth `n`, run
    at the builtins `bi` and the fuel `F + D`, has the events `nfTrace` of its source leakage
    equal to those of the leakage of `e` with the expanded call leakage at the builtins with
    the crate `crateBi fs bi fuelC n` and the fuel `F`, from related environments on which the
    source run does not end in an error, for every fuel offset `D ≥ n * fuelC`, when no
    function of the crate is named `repeat`. -/
theorem inl_leak (fs : List CrateFn) (bi : Builtins) (fuelC : Nat)
    (hfR : fs.find? (·.name == "repeat") = none) :
    ∀ (n : Nat) (ρ : String → String) (R : Env → Env → Prop), InlRel n ρ R →
      ∀ e, inlOk fs n e = true → ∀ D, n * fuelC ≤ D → ∀ F,
        TraceEq R IsErr (srcLeakNF bi (inl fs n ρ e) (F + D))
          (srcLeakCl (crateBi fs bi fuelC n) (expLeak fs bi fuelC n) e F)
          (denote' (crateBi fs bi fuelC n) F e)
  | 0, ρ, R, hR, e, he, D, _, F => by
      rw [inl]
      refine xf_leak hR (call := fun g _ => (fs.find? (·.name == g)).isNone) ?_ ?_ e
        (by simpa only [inlOk] using he) F
      · intro g args args' F' hg hargs
        simp only [Option.getD_none]
        exact app_ref (fun vals => (crateBi_of_find_none fs bi fuelC 0
          (Option.isNone_iff_eq_none.mp hg) vals).symm) hargs
      · intro g args args' F' hg hargs hargsL
        simp only [Option.getD_none]
        exact app_leak (fun vals => rfl) hargs hargsL
  | n + 1, ρ, R, hR, e, he, D, hD, F => by
      rw [inl]
      rw [inlOk] at he
      refine xf_leak hR ?_ ?_ e he F
      · intro g args args' F' hg hargs
        cases hf : fs.find? (·.name == g) with
        | none =>
          simp only [Option.map_none, Option.getD_none]
          exact app_ref (fun vals => (crateBi_of_find_none fs bi fuelC (n + 1) hf vals).symm)
            hargs
        | some c =>
          simp only [hf, Bool.and_eq_true, beq_iff_eq] at hg
          simp only [Option.map_some, Option.getD_some]
          exact callBlock_ref hf hR hg.1 hD hargs
            (fun R' hR' D' hD' F₀ => inl_ref fs bi fuelC n (lvlName n) R' hR' c.body hg.2 D' hD' F₀)
      · intro g args args' F' hg hargs hargsL
        cases hf : fs.find? (·.name == g) with
        | none =>
          simp only [Option.map_none, Option.getD_none]
          exact app_leak (expLeak_of_find_none fs bi fuelC hf (n + 1)) hargs hargsL
        | some c =>
          simp only [hf, Bool.and_eq_true, beq_iff_eq] at hg
          simp only [Option.map_some, Option.getD_some]
          have hne : g ≠ "repeat" := by
            rintro rfl
            rw [hfR] at hf
            cases hf
          exact callBlock_leak hf hne hg.1 hD hargs hargsL
            (fun R' hR' D' hD' F₀ =>
              inl_leak fs bi fuelC hfR n (lvlName n) R' hR' c.body hg.2 D' hD' F₀)

/-- **The source leakage of the inlining of a crate.** For a term `e` accepted by
    `inlOk fs n` and a run of `e` at the builtins with the crate `crateBi fs bi fuelC n` and
    the fuel `F` from `env` that does not end in an error, the events `nfTrace` of the source
    leakage of `inlineCrate fs n e` at the builtins `bi` and the fuel `F + D` from `env` are
    the events of `srcLeakX fs bi fuelC n e F env`, in which each call of a function of the
    crate leaks the expanded leakage of its body, for every `D ≥ n * fuelC`, when no function
    of the crate is named `repeat`. -/
theorem inlineCrate_srcLeak (fs : List CrateFn) (bi : Builtins) (fuelC n : Nat) {e : ImpExpr}
    (hfR : fs.find? (·.name == "repeat") = none) (he : inlOk fs n e = true) {F D : Nat} (hD : n * fuelC ≤ D) {env s : Env} {o : Outcome}
    (hrun : (denote' (crateBi fs bi fuelC n) F e).run env = (o, s)) (ho : ¬ IsErr o) :
    nfTrace (srcLeakNF bi (inlineCrate fs n e) (F + D) env) =
      nfTrace (srcLeakX fs bi fuelC n e F env) :=
  inl_leak fs bi fuelC hfR n id _ (inlRel_srcAgree n) e he D hD F env env (fun _ _ _ h => h)
    (by rw [hrun]; exact ho)

/-! ## The program of the front with the expanded calls -/

/-- **The expanded call leakage of a crate as a call leakage**: the source call leakage
    `expLeak fs bi fuelC n`, and at a binding of a call the events `nfTrace` of that leakage
    on the encoded arguments. -/
def expCallLeak (fs : List CrateFn) (bi : Builtins) (fuelC n : Nat) : CallLeak where
  cl := expLeak fs bi fuelC n
  ce f as _ x := nfTrace (expLeak fs bi fuelC n f (encAll as x))

/-- The expanded call leakage agrees with every builtins. -/
theorem expCallLeak_agrees (fs : List CrateFn) (bi : Builtins) (fuelC n : Nat) (B : Builtins) :
    (expCallLeak fs bi fuelC n).Agrees B :=
  fun _ _ _ _ _ _ => rfl

/-- **The program the front emits for a term of a crate, run with the expanded calls, has the
    events of the inlined term.** Let `impToNF` translate `e` from `σ` under typed builtins
    with the crate `crateBi fs bi fuelC n`, where `RepeatCalls bi` holds and no function of the
    crate is named `repeat`, `inlOk fs n` accept `e`, `e` contain no `whileFold`, and `e` run at those
    builtins and the fuel `F` from an environment related to `V` to a value. Then the leakage
    run of the emitted program at those builtins with the expanded call leakage
    `expCallLeak fs bi fuelC n` returns the encoding of the value and the events
    `nfTrace` of the source leakage of `inlineCrate fs n e` at the builtins `bi` and the fuel
    `F + D`, for every `D ≥ n * fuelC`. -/
theorem impToNF_leak_inlineCrate (fs : List CrateFn) (bi : Builtins) (fuelC n : Nat)
    (sigOf : String → List NfTy → Option NfTy)
    (hT : TypedCalls (crateBi fs bi fuelC n) sigOf) (hR : RepeatCalls bi)
    (hfR : fs.find? (·.name == "repeat") = none) {e : ImpExpr} (he : inlOk fs n e = true)
    {tgt : Option String} {Γ : Ctxt nfDialect} {σ : NfEnv Γ} {o : Out Γ}
    (h : impToNF sigOf tgt σ e = some o) (hw : ImpToNF.whileFoldFree e = true) {F D : Nat}
    (hD : n * fuelC ≤ D) {env : Env}
    {V : Valuation Γ} {v : Value} {env' : Env} (hrel : EnvRel σ env V)
    (hrun : (denote' (crateBi fs bi fuelC n) F e).run env = (.val v, env')) (tf : Nat) :
    ∃ x : o.t.denote,
      nfLeakRunE (crateBi fs bi fuelC n) (expCallLeak fs bi fuelC n) tf o.prog V =
        some (HVector.cons (f := fun t => ⟦t⟧) x .nil,
          nfTrace (srcLeakNF bi (inlineCrate fs n e) (F + D) env)) ∧
      v = enc o.t x := by
  rw [inlineCrate_srcLeak fs bi fuelC n hfR he hD hrun (by rintro ⟨m, hm⟩; cases hm)]
  exact impToNF_leakE_all (crateBi fs bi fuelC n) sigOf hT (crateBi_repeatCalls fs bi hR hfR fuelC n)
    (expCallLeak_agrees fs bi fuelC n _) h hw hrel hrun tf

/-! ## The rounds of the NF inlining keep the leakage run -/

open CatCrypt.Crypto.Hax.NFInline (crateOp crateBody crateLib crateCallOp crateInlineOk
  noCrateCall entryEnv_rel_paramsEnv enc_inj nfDenoteOp_crateBi)
open CatCrypt.Crypto.Hax.ImpToNF (crateSigOf hax64SigOf crateBi_typedCalls dec_sound tableOf
  nfLeakRunE_nf)
open CatCrypt.Crypto.Hax.NFToCat (nfLeakRun)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)

/-- **A call of a function of the crate at depth `m + 1`, with its expanded events, is a
    leakage run of its body at depth `m`.** Under the typing of the builtins `bi`, a
    successful run of an operation `crateOp fs` has a body for, at the builtins with the
    crate to the call depth `m + 1`, is a leakage run of the body at the builtins with the
    crate to the call depth `m` with the expanded call leakage of the depth `m`, at every
    fuel `tf`, with the same result and the events of the operation under the expanded call
    leakage of the depth `m + 1`, under `RepeatCalls bi` and no function of the crate named
    `repeat`. -/
theorem crateOp_leak (fs : List CrateFn) (bi : Builtins) (hT : TypedCalls bi hax64SigOf)
    (hR : RepeatCalls bi) (hfR : fs.find? (·.name == "repeat") = none) (fuelC m tf : Nat) :
    ∀ (o : NfOp) (b : NFProg nfDialect o.sig [o.ret]), crateOp fs o = some b → ∀ x y,
      nfDenoteOp (tableOf (crateBi fs bi fuelC (m + 1))) o x = some y →
        nfLeakRunE (crateBi fs bi fuelC m) (expCallLeak fs bi fuelC m) tf b x =
          some (.cons y .nil, (expCallLeak fs bi fuelC (m + 1)).opEv o x) := by
  intro o
  induction o with
  | call f as r =>
      intro b hb x y hy
      simp only [crateOp, Option.bind_eq_some_iff] at hb
      obtain ⟨c, hc, hb⟩ := hb
      have hwf := NFInline.whileFoldFree_of_crateBody hb
      simp only [crateBody, hwf, if_true, Option.bind_eq_some_iff] at hb
      obtain ⟨o', ho', hb⟩ := hb
      split at hb
      · rename_i hty
        cases hb
        obtain ⟨rfl, rfl⟩ := hty
        simp only [nfDenoteOp, tableOf, crateBi, hc, Option.bind_eq_some_iff] at hy
        obtain ⟨v, hv, hd⟩ := hy
        split at hv
        · rename_i v' hrun
          split at hv
          · cases hv
            obtain ⟨x', hx', hvx⟩ := impToNF_leakE_all (C := expCallLeak fs bi fuelC m)
              (crateBi fs bi fuelC m) (crateSigOf fs hax64SigOf)
              (crateBi_typedCalls fs bi hax64SigOf hT fuelC m)
              (crateBi_repeatCalls fs bi hR hfR fuelC m)
              (expCallLeak_agrees fs bi fuelC m _) ho' hwf (entryEnv_rel_paramsEnv c.params x)
              (Prod.ext hrun rfl) tf
            have hy' : y = x' := enc_inj _ _ _ ((dec_sound _ _ _ hd).symm.trans hvx)
            subst hy'
            change nfLeakRunE (crateBi fs bi fuelC m) (expCallLeak fs bi fuelC m) tf o'.prog x = _
            rw [hx']
            simp only [CallLeak.opEv, expCallLeak, expLeak, hc]
          · cases hv
        · cases hv
      · cases hb
  | named _ o ih =>
      intro b hb x y hy
      exact ih b hb x y hy
  | _ =>
      intro b hb
      cases hb

/-- The events of an operation that calls no function of the crate are the same under the
    expanded call leakage of every two depths. -/
theorem expCallLeak_opEv_of_crateCallOp (fs : List CrateFn) (bi : Builtins) (fuelC j k : Nat) :
    ∀ (o : NfOp), crateCallOp fs o = false → ∀ x,
      (expCallLeak fs bi fuelC j).opEv o x = (expCallLeak fs bi fuelC k).opEv o x := by
  intro o
  induction o with
  | call f as r =>
      intro h x
      simp only [crateCallOp, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
      simp only [CallLeak.opEv, expCallLeak, expLeak_of_find_none fs bi fuelC h]
  | named _ o ih =>
      intro h x
      exact ih h x
  | _ =>
      intro _ _
      rfl

/-- The expanded call leakage of the depth `0` gives every operation the events of the call
    leakage `CallLeak.nf` of the front. -/
theorem expCallLeak_zero_opEv (fs : List CrateFn) (bi : Builtins) (fuelC : Nat) :
    ∀ (o : NfOp) x, (expCallLeak fs bi fuelC 0).opEv o x = CallLeak.nf.opEv o x := by
  intro o
  induction o with
  | call f as r => intro x; rfl
  | named _ o ih =>
      intro x
      exact ih x
  | _ => intro _; rfl

/-- **The library of a crate is sound for the leakage run from the call depth `m + 1` to the
    call depth `m`**, with the expanded call leakage of each depth, for the operations that
    call no function of the crate, under the typing of the builtins `bi`, `RepeatCalls bi`
    and no function of the crate named `repeat`, at every fuel `tf`. -/
theorem crateLib_leakSoundStep (fs : List CrateFn) (bi : Builtins)
    (hT : TypedCalls bi hax64SigOf) (hR : RepeatCalls bi)
    (hfR : fs.find? (·.name == "repeat") = none) (fuelC m tf : Nat) :
    (crateLib fs).LeakSoundStep (nfDenote (tableOf (crateBi fs bi fuelC (m + 1))))
      (nfDenote (tableOf (crateBi fs bi fuelC m))) (expCallLeak fs bi fuelC (m + 1)).opEv
      (expCallLeak fs bi fuelC m).opEv CallEnv.empty (fun o => !crateCallOp fs o) tf where
  op o b hb x y h := by
    simp only [nfDenote_denoteM] at h
    exact crateOp_leak fs bi hT hR hfR fuelC m tf o b hb x y h
  keep o ho x y h := by
    simp only [Bool.not_eq_true'] at ho
    simp only [nfDenote_denoteM] at h ⊢
    refine ⟨?_, expCallLeak_opEv_of_crateCallOp fs bi fuelC m (m + 1) o ho x⟩
    rw [nfDenoteOp_crateBi fs bi fuelC m o ho]
    rwa [nfDenoteOp_crateBi fs bi fuelC (m + 1) o ho] at h
  call _ _ _ _ hb := by cases hb

/-- **One round of inlining at the library of a crate keeps the leakage run, from the call
    depth `k + 1` to the call depth `k`.** Under the typing of the builtins `bi`,
    `RepeatCalls bi` and no function of the crate named `repeat`, on a program each of whose operations has a body in `crateLib fs` or calls no function of the
    crate, a leakage run at the builtins with the crate to the depth `k + 1` with the
    expanded call leakage of that depth is a leakage run of the program after one round at
    the depth `k` with the expanded call leakage of the depth `k`, with the same results and
    events. -/
theorem nfLeakRunE_inline?_crate (fs : List CrateFn) (bi : Builtins)
    (hT : TypedCalls bi hax64SigOf) (hR : RepeatCalls bi)
    (hfR : fs.find? (·.name == "repeat") = none) (fuelC k tf : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    {p p' : NFProg nfDialect Γ ts}
    (ha : p.allOps (fun o => ((crateLib fs).op o).isSome || !crateCallOp fs o) = true)
    (hq : NFProg.inline? (crateLib fs) p = some p') {V : Valuation Γ}
    {r : Valuation (d := nfDialect) ts × List CTLeak}
    (h : nfLeakRunE (crateBi fs bi fuelC (k + 1)) (expCallLeak fs bi fuelC (k + 1)) tf p V =
      some r) :
    nfLeakRunE (crateBi fs bi fuelC k) (expCallLeak fs bi fuelC k) tf p' V = some r :=
  NFProg.leakRunMC_inline?_step (crateLib_leakSoundStep fs bi hT hR hfR fuelC k tf) p ha hq h

/-- **The rounds of inlining at the library of a crate keep the leakage run.** On a program
    accepted by `inlineIterOk` at `n` rounds, a leakage run at the builtins with the crate to
    the depth `n` with the expanded call leakage of that depth is a leakage run of the
    program after the `n` rounds at the depth `0` with the expanded call leakage of the
    depth `0`, under `RepeatCalls bi` and no function of the crate named `repeat`. -/
theorem nfLeakRunE_inlineIter_crate (fs : List CrateFn) (bi : Builtins)
    (hT : TypedCalls bi hax64SigOf) (hR : RepeatCalls bi)
    (hfR : fs.find? (·.name == "repeat") = none) (fuelC tf : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy} :
    ∀ (n : Nat) (p : NFProg nfDialect Γ ts) {V : Valuation Γ}
      {r : Valuation (d := nfDialect) ts × List CTLeak},
      p.inlineIterOk (crateLib fs) (fun o => !crateCallOp fs o) n = true →
      nfLeakRunE (crateBi fs bi fuelC n) (expCallLeak fs bi fuelC n) tf p V = some r →
      nfLeakRunE (crateBi fs bi fuelC 0) (expCallLeak fs bi fuelC 0) tf
        (p.inlineIter (crateLib fs) n) V = some r
  | 0, _, _, _, _, hp => hp
  | n + 1, p, V, r, hok, hp => by
      simp only [NFProg.inlineIterOk, Bool.and_eq_true] at hok
      obtain ⟨ha, hok⟩ := hok
      simp only [NFProg.inlineIter]
      split at hok
      · rename_i q hq
        exact nfLeakRunE_inlineIter_crate fs bi hT hR hfR fuelC tf n q hok
          (nfLeakRunE_inline?_crate fs bi hT hR hfR fuelC n tf ha hq hp)
      · cases hok

/-- **A program without calls of the crate has, at the depth `0` with the expanded call
    leakage, the leakage run `nfLeakRun` at the builtins `bi`.** -/
theorem nfLeakRunE_crateBi_zero (fs : List CrateFn) (bi : Builtins) (fuelC tf : Nat)
    {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts)
    (hp : noCrateCall fs p = true) (V : Valuation Γ) :
    nfLeakRunE (crateBi fs bi fuelC 0) (expCallLeak fs bi fuelC 0) tf p V =
      nfLeakRun bi tf p V := by
  rw [← nfLeakRunE_nf]
  have hp' : p.allOps (fun o => !crateCallOp fs o) = true := hp
  exact NFProg.leakRunMC_congr_ops _ _ _ _ (fun o => !crateCallOp fs o)
    (fun o ho x => ⟨by
      simp only [Bool.not_eq_true'] at ho
      simp only [nfDenote_denoteM]
      exact nfDenoteOp_crateBi fs bi fuelC 0 o ho x, expCallLeak_zero_opEv fs bi fuelC o x⟩)
    CallEnv.empty tf p hp' V

/-- **The leakage run of the inlined program of a crate.** Under the typing of the builtins
    `bi`, `RepeatCalls bi` and no function of the crate named `repeat`, on a program accepted
    by `crateInlineOk fs n`, a leakage run at the builtins with
    the crate to the depth `n` with the expanded call leakage of that depth is the leakage run
    `nfLeakRun` at the builtins `bi` of the program after the `n` rounds of inlining. -/
theorem nfLeakRun_inlineIter_crate (fs : List CrateFn) (bi : Builtins)
    (hT : TypedCalls bi hax64SigOf) (hR : RepeatCalls bi)
    (hfR : fs.find? (·.name == "repeat") = none) (fuelC tf n : Nat) {Γ : Ctxt nfDialect} {ts : List NfTy}
    (p : NFProg nfDialect Γ ts) (hok : crateInlineOk fs n p = true) {V : Valuation Γ}
    {r : Valuation (d := nfDialect) ts × List CTLeak}
    (hp : nfLeakRunE (crateBi fs bi fuelC n) (expCallLeak fs bi fuelC n) tf p V = some r) :
    nfLeakRun bi tf (p.inlineIter (crateLib fs) n) V = some r := by
  obtain ⟨hit, hno⟩ := Bool.and_eq_true_iff.mp hok
  rw [← nfLeakRunE_crateBi_zero fs bi fuelC tf _ hno V]
  exact nfLeakRunE_inlineIter_crate fs bi hT hR hfR fuelC tf n p hit hp

end CatCrypt.Crypto.Hax.ImpInline
