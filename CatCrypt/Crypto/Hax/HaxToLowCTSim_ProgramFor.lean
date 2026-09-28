/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ProgramArr

/-!
# Program-level simulation with counted loops

`haxToLowCT` lowers a hax `forFold i lo hi body` with non-negative integer
literal bounds to `RFor i (hi - lo) body'`, where `body'` is the lowered body,
preceded for `lo ≠ 0` by the shift `i := i + lo` (`forShift`).  `RFor` sets the
scalar `i` to `0, 1, …, hi - lo - 1` before the successive trips.  The reference
semantics `denote` gives `forFold` no meaning (it evaluates to an error), since
`forFold` is the output of the loop-functionalisation phase applied to `forLoop`;
the source semantics of a program with counted loops is here `denote` of
`forToLoop e`, which reads every `forFold` as the `forLoop` with the same range
and body.  `denoteForLoop` binds `i` to `lo, lo + 1, …, hi - 1` in the
environment before the successive trips.

* `simScopeF tow S T A Γ e` is the checker of `simScopeA` in which every
  `ifThenElse` and `whileLoop` condition is a name of `S`, and a `forFold` with
  non-negative integer literal bounds is accepted when its counter is a name of
  `S` and its body is accepted from the loop's entry scope; the loop's exit
  scope is its entry scope.
* `ProgSimF` is the simulation predicate for `arrTower A (litTower T c)` against
  the source run of `forToLoop e`.
* The loop invariant, at the start of trip `j`, is the invariant of the whole
  program: the environment agrees with the state (`envAgreesRustT`), the state
  is bound on the loop's entry scope (`ScopeBound`), and the names of `S` have no
  tower binding (`NamesFresh`).  The environment binds `i` to `lo + j` and the
  state holds `lo + j` in the scalar `i`, which agree because `i` is in `S`.

## Main results

* `haxToLowCT_simulates_programF` — every program simulates, from the
  hypotheses of `haxToLowCT_simulates_programA`.
* `progSimF_forFold` — the counted-loop arm, by induction on the trips left
  (`TripsFrom`, `rustExec_rFor_of_tripsFrom`).
* `anfShaped_forToLoop_val_or_err` — a program in the image of `haxToLowCT`,
  read through `forToLoop`, runs to a value or an error.
* `simScopeF_lookup_mono`, `simScopeF_eq_tow` — the exit scope extends the entry
  scope, and the checker depends on the tower dispatch only at the call names
  `scopeCallNamesF` collects.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpPat Value Env Outcome Builtins denote denoteForLoop denoteArgs)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT RustState RustExec LeafSpec Located RustVal SExpr
   rsSetTower rsSetScalar locatedUpdate locatedLookup)

/-! ## §1  The source semantics of counted loops -/

mutual

/-- Every `forFold v lo hi body`, `forFoldRev v lo hi body` and `whileFold c body`
    of a program replaced by `forLoop v lo hi body`, `forLoopRev v lo hi body`
    and `whileLoop c body`, recursively. -/
def forToLoop : ImpExpr → ImpExpr
  | .lit l => .lit l
  | .var n => .var n
  | .letBind n v b => .letBind n (forToLoop v) (forToLoop b)
  | .lam ps b => .lam ps (forToLoop b)
  | .app f args => .app f (forToLoopArgs args)
  | .tuple es => .tuple (forToLoopArgs es)
  | .proj e i => .proj (forToLoop e) i
  | .ifThenElse c t e => .ifThenElse (forToLoop c) (forToLoop t) (forToLoop e)
  | .match_ s arms => .match_ (forToLoop s) (forToLoopArms arms)
  | .unitVal => .unitVal
  | .seq a b => .seq (forToLoop a) (forToLoop b)
  | .borrow e => .borrow (forToLoop e)
  | .deref e => .deref (forToLoop e)
  | .assign n r => .assign n (forToLoop r)
  | .forLoop v lo hi b => .forLoop v (forToLoop lo) (forToLoop hi) (forToLoop b)
  | .forLoopRev v lo hi b => .forLoopRev v (forToLoop lo) (forToLoop hi) (forToLoop b)
  | .whileLoop c b => .whileLoop (forToLoop c) (forToLoop b)
  | .break_ none => .break_ none
  | .break_ (some e) => .break_ (some (forToLoop e))
  | .continue_ => .continue_
  | .earlyReturn e => .earlyReturn (forToLoop e)
  | .questionMark e => .questionMark (forToLoop e)
  | .forFold v lo hi b => .forLoop v (forToLoop lo) (forToLoop hi) (forToLoop b)
  | .forFoldRev v lo hi b => .forLoopRev v (forToLoop lo) (forToLoop hi) (forToLoop b)
  | .whileFold c b => .whileLoop (forToLoop c) (forToLoop b)
  | .forFoldReturn v lo hi b => .forFoldReturn v (forToLoop lo) (forToLoop hi) (forToLoop b)
  | .forFoldRevReturn v lo hi b =>
      .forFoldRevReturn v (forToLoop lo) (forToLoop hi) (forToLoop b)
  | .whileFoldReturn c b => .whileFoldReturn (forToLoop c) (forToLoop b)
  | .cfBreak e => .cfBreak (forToLoop e)
  | .cfContinue e => .cfContinue (forToLoop e)
  | .cfBreakContinue e => .cfBreakContinue (forToLoop e)
  | .typeAscription e ty => .typeAscription (forToLoop e) ty

/-- `forToLoop` on every element of a list. -/
def forToLoopArgs : List ImpExpr → List ImpExpr
  | [] => []
  | a :: as => forToLoop a :: forToLoopArgs as

/-- `forToLoop` on every arm body. -/
def forToLoopArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
  | [] => []
  | (p, e) :: rest => (p, forToLoop e) :: forToLoopArms rest

end

theorem forToLoopArgs_of_allVar :
    ∀ (args : List ImpExpr), args.all isVar = true → forToLoopArgs args = args
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨n, rfl⟩ : ∃ n, a = .var n := by
      cases a <;> simp_all [isVar]
    simp only [forToLoopArgs, forToLoop, forToLoopArgs_of_allVar as h.2]

theorem forToLoopArgs_of_vars (args : List ImpExpr) (h : ∀ a ∈ args, ∃ n, a = .var n) :
    forToLoopArgs args = args :=
  forToLoopArgs_of_allVar args (List.all_eq_true.mpr fun a ha => by
    obtain ⟨n, rfl⟩ := h a ha; rfl)

/-- A variable, literal or call runs to a value or an error. -/
theorem denote_atom_val_or_err (bi : Builtins) (fuel : Nat) (e : ImpExpr)
    (h : (∃ n, e = .var n) ∨ (∃ l, e = .lit l) ∨ (∃ f args, e = .app f args)) (env : Env) :
    (∃ w env', (denote bi fuel e).run env = (.val w, env'))
      ∨ (∃ msg env', (denote bi fuel e).run env = (.err msg, env')) := by
  rcases h with ⟨n, rfl⟩ | ⟨l, rfl⟩ | ⟨f, args, rfl⟩
  · exact denote_var_outcome bi fuel n env
  · exact Or.inl ⟨_, _, denote_lit_eq bi fuel l env⟩
  · exact denote_app_outcome bi fuel f args env

theorem impBoundToSExpr_atom (hi : ImpExpr) (h : (impBoundToSExpr hi).isSome = true) :
    (∃ n, forToLoop hi = .var n) ∨ (∃ l, forToLoop hi = .lit l) ∨
      (∃ f args, forToLoop hi = .app f args) := by
  cases hi with
  | var n => exact Or.inl ⟨n, rfl⟩
  | lit l => exact Or.inr (Or.inl ⟨l, rfl⟩)
  | app f args => exact Or.inr (Or.inr ⟨f, _, rfl⟩)
  | _ => simp [impBoundToSExpr] at h

/-- The shape of a `forFold` that `AnfShaped` accepts: a literal start, a
    literal or convertible bound, and an `AnfShaped` body. -/
theorem anfShaped_forFold_inv (v : String) (lo hi body : ImpExpr)
    (h : AnfShaped (.forFold v lo hi body) = true) :
    AnfShaped body = true ∧ (∃ l, lo = .lit l) ∧
      ((∃ l, hi = .lit l) ∨ (impBoundToSExpr hi).isSome = true) := by
  unfold AnfShaped at h
  split at h <;> simp_all

/-- The shape of a `forFoldRev` that `AnfShaped` accepts: literal bounds and an
    `AnfShaped` body. -/
theorem anfShaped_forFoldRev_inv (v : String) (lo hi body : ImpExpr)
    (h : AnfShaped (.forFoldRev v lo hi body) = true) :
    AnfShaped body = true ∧ (∃ l, lo = .lit l) ∧ (∃ l, hi = .lit l) := by
  unfold AnfShaped at h
  split at h <;> simp_all

/-- The shape of a `match_` that `AnfShaped` accepts: one arm destructuring a
    pair into two variables, with an `AnfShaped` body. -/
theorem anfShaped_match_inv (f : String) (args : List ImpExpr) (arms : List (ImpPat × ImpExpr))
    (h : AnfShaped (.match_ (.app f args) arms) = true) :
    ∃ n1 n2 body, arms = [(.tuplePat [.varPat n1, .varPat n2], body)] ∧
      AnfShaped body = true := by
  unfold AnfShaped at h
  split at h <;> simp_all

/-- A program in the image of `haxToLowCT`, with its counted loops read as
    `forLoop`, runs to a value or an error. -/
theorem anfShaped_forToLoop_val_or_err (bi : Builtins) (e : ImpExpr) (h : AnfShaped e = true) :
    ∀ fuel env,
      (∃ w env', (denote bi fuel (forToLoop e)).run env = (.val w, env'))
        ∨ (∃ msg env', (denote bi fuel (forToLoop e)).run env = (.err msg, env')) := by
  induction e using ImpExpr.ind with
  | var n => intro fuel env; exact denote_var_outcome bi fuel n env
  | unitVal => intro fuel env; exact Or.inl ⟨_, _, denote_unitVal_eq bi fuel env⟩
  | app f args _ => intro fuel env; exact denote_app_outcome bi fuel f _ env
  | tuple es _ =>
    intro fuel env
    simp only [forToLoop]
    rw [denote_tuple_run_eq]
    rcases (denoteArgs bi fuel (forToLoopArgs es)).run env with ⟨mvals, env_a⟩
    cases mvals with
    | some vals => exact Or.inl ⟨_, _, rfl⟩
    | none => exact Or.inr ⟨_, _, rfl⟩
  | letBind n val body _ ihbody =>
    intro fuel env
    simp only [forToLoop]
    rw [denote_letBind_run_eq]
    have hbody : AnfShaped body = true := by
      unfold AnfShaped at h; split at h <;> simp_all
    have hval : (∃ m, forToLoop val = .var m) ∨ (∃ l, forToLoop val = .lit l) ∨
        (∃ f args, forToLoop val = .app f args) ∨ (∃ t i, forToLoop val = .proj (.var t) i) := by
      cases val with
      | var m => exact Or.inl ⟨m, rfl⟩
      | lit l => exact Or.inr (Or.inl ⟨l, rfl⟩)
      | app f args => exact Or.inr (Or.inr (Or.inl ⟨f, _, rfl⟩))
      | proj pe i =>
        cases pe with
        | var t => exact Or.inr (Or.inr (Or.inr ⟨t, i, rfl⟩))
        | _ => simp [AnfShaped] at h
      | _ => simp [AnfShaped] at h
    rcases hval with hv | hv | hv | ⟨t, i, hv⟩
    · rcases denote_atom_val_or_err bi fuel _ (Or.inl hv) env with ⟨w, e1, hw⟩ | ⟨m, e1, hw⟩
      · rw [hw]; exact ihbody hbody fuel _
      · rw [hw]; exact Or.inr ⟨m, e1, rfl⟩
    · rcases denote_atom_val_or_err bi fuel _ (Or.inr (Or.inl hv)) env with
        ⟨w, e1, hw⟩ | ⟨m, e1, hw⟩
      · rw [hw]; exact ihbody hbody fuel _
      · rw [hw]; exact Or.inr ⟨m, e1, rfl⟩
    · rcases denote_atom_val_or_err bi fuel _ (Or.inr (Or.inr hv)) env with
        ⟨w, e1, hw⟩ | ⟨m, e1, hw⟩
      · rw [hw]; exact ihbody hbody fuel _
      · rw [hw]; exact Or.inr ⟨m, e1, rfl⟩
    · rw [hv]
      cases hEnvT : env t with
      | none =>
        rw [denote_proj_var_run_err_of_env_none bi fuel t i env hEnvT]
        exact Or.inr ⟨_, env, rfl⟩
      | some vTup =>
        cases hProj : vTup.projIdx i with
        | none =>
          rw [denote_proj_var_run_err_of_proj_none bi fuel t i env vTup hEnvT hProj]
          exact Or.inr ⟨_, env, rfl⟩
        | some vi =>
          rw [denote_proj_var_run_some bi fuel t i env vTup vi hEnvT hProj]
          exact ihbody hbody fuel _
  | seq a b iha ihb =>
    intro fuel env
    simp only [AnfShaped, Bool.and_eq_true] at h
    simp only [forToLoop]
    rw [denote_seq_run_eq]
    rcases iha h.1 fuel env with ⟨w, e1, hw⟩ | ⟨m, e1, hw⟩
    · rw [hw]; exact ihb h.2 fuel e1
    · rw [hw]; exact Or.inr ⟨m, e1, rfl⟩
  | ifThenElse c t e _ iht ihe =>
    intro fuel env
    cases c with
    | var name =>
      simp only [AnfShaped, Bool.and_eq_true] at h
      simp only [forToLoop]
      rw [denote_ifThenElse_run_eq]
      rcases denote_var_outcome bi fuel name env with ⟨vc, e1, hc⟩ | ⟨m, e1, hc⟩
      · rw [hc]
        cases vc with
        | bool b => cases b
                    · exact ihe h.2 fuel e1
                    · exact iht h.1 fuel e1
        | _ => exact Or.inr ⟨_, e1, rfl⟩
      · rw [hc]; exact Or.inr ⟨m, e1, rfl⟩
    | _ => simp [AnfShaped] at h
  | whileLoop c body _ ihbody =>
    intro fuel env
    cases c with
    | var name =>
      simp only [AnfShaped] at h
      simp only [forToLoop]
      rw [denote_whileLoop_run_eq]
      exact denoteWhile_outcome_val_or_err bi (.var name) _
        (fun f e => denote_var_outcome bi f name e) (fun f e => ihbody h f e) fuel env
    | _ => simp [AnfShaped] at h
  | assign n rhs _ =>
    intro fuel env
    simp only [forToLoop]
    rw [denote_assign_run_eq]
    have hr : (∃ l, forToLoop rhs = .lit l) ∨ (∃ f args, forToLoop rhs = .app f args) := by
      cases rhs with
      | lit l => exact Or.inl ⟨l, rfl⟩
      | app f args => exact Or.inr ⟨f, _, rfl⟩
      | _ => simp [AnfShaped] at h
    rcases hr with hr | hr
    · rcases denote_atom_val_or_err bi fuel _ (Or.inr (Or.inl hr)) env with
        ⟨w, e1, hw⟩ | ⟨m, e1, hw⟩
      · rw [hw]; exact Or.inl ⟨_, _, rfl⟩
      · rw [hw]; exact Or.inr ⟨m, e1, rfl⟩
    · rcases denote_atom_val_or_err bi fuel _ (Or.inr (Or.inr hr)) env with
        ⟨w, e1, hw⟩ | ⟨m, e1, hw⟩
      · rw [hw]; exact Or.inl ⟨_, _, rfl⟩
      · rw [hw]; exact Or.inr ⟨m, e1, rfl⟩
  | match_ scrut arms _ iharms =>
    intro fuel env
    cases scrut with
    | app f args =>
      obtain ⟨n1, n2, body, rfl, hb⟩ := anfShaped_match_inv f args arms h
      simp only [forToLoop, forToLoopArms]
      exact AnfShaped_match_outcome bi fuel f _ n1 n2 _ env
        (fun env' => iharms _ (List.mem_singleton.mpr rfl) hb fuel env')
    | _ => simp [AnfShaped] at h
  | forFold v lo hi body _ _ ihbody =>
    intro fuel env
    obtain ⟨hb, ⟨l, rfl⟩, hhi⟩ := anfShaped_forFold_inv v lo hi body h
    simp only [forToLoop]
    refine denote_forLoop_val_or_err bi fuel v _ _ _ env
      (fun env => Or.inl ⟨_, _, denote_lit_eq bi fuel l env⟩) ?_ (ihbody hb)
    intro env
    rcases hhi with ⟨l', rfl⟩ | hs
    · exact Or.inl ⟨_, _, denote_lit_eq bi fuel l' env⟩
    · exact denote_atom_val_or_err bi fuel _ (impBoundToSExpr_atom hi hs) env
  | forFoldRev v lo hi body _ _ ihbody =>
    intro fuel env
    obtain ⟨hb, ⟨l, rfl⟩, ⟨l', rfl⟩⟩ := anfShaped_forFoldRev_inv v lo hi body h
    simp only [forToLoop]
    exact denote_forLoopRev_val_or_err bi fuel v _ _ _ env
      (fun env => Or.inl ⟨_, _, denote_lit_eq bi fuel l env⟩)
      (fun env => Or.inl ⟨_, _, denote_lit_eq bi fuel l' env⟩) (ihbody hb)
  | whileFold c body _ ihbody =>
    intro fuel env
    cases c with
    | var name =>
      simp only [AnfShaped] at h
      simp only [forToLoop]
      rw [denote_whileLoop_run_eq]
      exact denoteWhile_outcome_val_or_err bi (.var name) _
        (fun f e => denote_var_outcome bi f name e) (fun f e => ihbody h f e) fuel env
    | _ => simp [AnfShaped] at h
  | typeAscription e ty ih =>
    intro fuel env
    simp only [AnfShaped] at h
    simp only [forToLoop]
    rcases ih h fuel env with ⟨w, e1, hw⟩ | ⟨m, e1, hw⟩
    · exact Or.inl ⟨w, e1, by rw [denote_typeAscription]; exact hw⟩
    · exact Or.inr ⟨m, e1, by rw [denote_typeAscription]; exact hw⟩
  | _ => simp [AnfShaped] at h

/-! ## §2  Trips of a counted loop -/

/-- `d` trips of `body` with the counter `x` set to `k`, `k + 1`, …, `k + d - 1`
    in turn, from `rs` to `rs'`. -/
def TripsFrom (N : Nat) (leafSpec : LeafSpec) (x : String) (body : LowCT) :
    Nat → Nat → RustState → RustState → Prop
  | _, 0, rs, rs' => rs' = rs
  | k, d + 1, rs, rs' => ∃ r, RustExec N leafSpec body (rsSetScalar rs x k) r ∧
      TripsFrom N leafSpec x body (k + 1) d r rs'

/-- A run of the first `k` trips of `RFor x _ body` followed by `d` further trips
    is a run of `RFor x (k + d) body`. -/
theorem rustExec_rFor_of_tripsFrom (N : Nat) (leafSpec : LeafSpec) (x : String) (body : LowCT) :
    ∀ (d k : Nat) (rs r1 rs' : RustState), RustExec N leafSpec (.RFor x k body) rs r1 →
      TripsFrom N leafSpec x body k d r1 rs' → RustExec N leafSpec (.RFor x (k + d) body) rs rs' := by
  intro d
  induction d with
  | zero => intro k rs r1 rs' h1 h2; simp only [TripsFrom] at h2; subst h2; exact h1
  | succ d ih =>
    intro k rs r1 rs' h1 h2
    obtain ⟨r, hb, hr⟩ := h2
    have := ih (k + 1) rs r rs' (RustExec.forSucc x k body rs r1 r h1 hb) hr
    rwa [show k + 1 + d = k + (d + 1) by omega] at this

/-! ## §3  The checker -/

/-- The scope checker of `simScopeA`, in which every `ifThenElse` and
    `whileLoop` condition is a name of `S`, and a `forFold` with non-negative
    integer literal bounds and a counter in `S` is accepted when its body is;
    its exit scope is its entry scope. -/
def simScopeF (tow : String → TowerType) (S T : List String) (A Γ : TowerScope) :
    ImpExpr → Option TowerScope
  | .letBind name (.app f args) body =>
      if f = "array_update" then
        match args with
        | [.var arr, .var idx, .var src] =>
            match List.lookup arr A with
            | some t =>
                if decide (name = arr) && decide (List.lookup arr Γ = some t)
                    && decide (List.lookup src Γ = some t.elemType) && S.contains idx then
                  simScopeF tow S T A Γ body
                else none
            | none => none
        | _ => none
      else if f = "index" then
        match args with
        | [.var arr, .var idx] =>
            match List.lookup arr A with
            | some t =>
                if decide (List.lookup arr Γ = some t) && decide (arr ≠ name) && S.contains idx
                    && scopeCompat Γ name .TFp && !S.contains name then
                  simScopeF tow S T A ((name, .TFp) :: Γ) body
                else none
            | none => none
        | _ => none
      else
        let dt := tow f
        if !scalarCallName f && argsInScope Γ dt args && argsAvoid name args
            && scopeCompat Γ name dt && !S.contains name then
          simScopeF tow S T A ((name, dt) :: Γ) body
        else none
  | .letBind name (.lit l) body =>
      if T.contains name then
        if litWord l && scopeCompat Γ name .TFp && !S.contains name then
          simScopeF tow S T A ((name, .TFp) :: Γ) body
        else none
      else if S.contains name then simScopeF tow S T A Γ body else none
  | .letBind name (.var src) body =>
      if decide (name = src) || (S.contains name && S.contains src) then
        simScopeF tow S T A Γ body
      else none
  | .letBind name (.proj (.var t) _) body =>
      if decide (List.lookup t Γ = some .TFp) && decide (t ≠ name)
          && scopeCompat Γ name .TFp && !S.contains name then
        simScopeF tow S T A ((name, .TFp) :: Γ) body
      else none
  | .var _ => some Γ
  | .unitVal => some Γ
  | .seq a b =>
      match simScopeF tow S T A Γ a with
      | some Γ₁ => simScopeF tow S T A Γ₁ b
      | none => none
  | .ifThenElse (.var c) t e =>
      if S.contains c then
        match simScopeF tow S T A Γ t, simScopeF tow S T A Γ e with
        | some _, some _ => some Γ
        | _, _ => none
      else none
  | .whileLoop (.var c) body =>
      if S.contains c then
        match simScopeF tow S T A Γ body with
        | some _ => some Γ
        | none => none
      else none
  | .forFold i (.lit (.int lo)) (.lit (.int hi)) body =>
      if decide (0 ≤ lo) && decide (0 ≤ hi) && S.contains i then
        match simScopeF tow S T A Γ body with
        | some _ => some Γ
        | none => none
      else none
  | .assign name (.lit _) => if S.contains name then some Γ else none
  | .assign name (.app f args) =>
      if f = "array_update" ∨ f = "index" then none
      else
        let dt := tow f
        if argsInScope Γ dt args && decide (List.lookup name Γ = some dt)
            && !S.contains name then some Γ else none
  | .tuple es => if es.all isVar then some Γ else none
  | .typeAscription e _ => simScopeF tow S T A Γ e
  | _ => none

/-- The loop body `haxToLowCT` produces for a `forFold` starting at `lo`: the
    lowered body for `lo = 0`, and otherwise the lowered body after the counter
    is shifted by `lo`. -/
def forShift (i : String) (lo : Nat) (bodyC : LowCT) : LowCT :=
  if lo = 0 then bodyC else .RSeq (.RScalarSetExpr i (.SAdd (.SVar i) (.SLit lo))) bodyC

/-- The lowering of a `forFold` with non-negative integer literal bounds. -/
theorem haxToLowCT_forFold_lit_some (i : String) (lo hi : Int) (body : ImpExpr) (c : LowCT)
    (hlo : 0 ≤ lo) (hhi : 0 ≤ hi)
    (h : haxToLowCT (.forFold i (.lit (.int lo)) (.lit (.int hi)) body) = some c) :
    ∃ bodyC, haxToLowCT body = some bodyC ∧
      c = .RFor i (hi.toNat - lo.toNat) (forShift i lo.toNat bodyC) := by
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hlo
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hhi
  cases hB : haxToLowCT body with
  | none =>
    cases a with
    | zero => simp [haxToLowCT, hB] at h
    | succ a =>
      rw [show ((a + 1 : Nat) : Int) = Int.ofNat (a + 1) from rfl] at h
      simp only [haxToLowCT, hB, impLitNat] at h
      simp_all
  | some bodyC =>
    refine ⟨bodyC, rfl, ?_⟩
    cases a with
    | zero => simp [haxToLowCT, hB] at h; simp [forShift, h]
    | succ a =>
      rw [show ((a + 1 : Nat) : Int) = Int.ofNat (a + 1) from rfl] at h
      simp only [haxToLowCT, hB, impLitNat] at h
      simp_all [forShift]

/-- `simScopeF` rejects a `forFold` whose bounds are not both integer literals. -/
theorem simScopeF_forFold_none (tow : String → TowerType) (S T : List String) (A Γ : TowerScope)
    (i : String) (lo hi body : ImpExpr)
    (hs : ¬ ∃ a b : Int, lo = .lit (.int a) ∧ hi = .lit (.int b)) :
    simScopeF tow S T A Γ (.forFold i lo hi body) = none := by
  unfold simScopeF
  split <;> simp_all

/-- The exit scope of `simScopeF` extends the entry scope. -/
theorem simScopeF_lookup_mono (tow : String → TowerType) (S T : List String) (A : TowerScope)
    (e : ImpExpr) :
    ∀ (Γ Γ' : TowerScope), simScopeF tow S T A Γ e = some Γ' →
      ∀ m dt, List.lookup m Γ = some dt → List.lookup m Γ' = some dt := by
  induction e using ImpExpr.ind with
  | letBind name val body _ ihBody =>
    intro Γ Γ' h m dt hm
    cases val with
    | app f args =>
      simp only [simScopeF] at h
      split at h
      · split at h
        · split at h
          · split at h
            · exact ihBody Γ Γ' h m dt hm
            · cases h
          · cases h
        · cases h
      · split at h
        · split at h
          · split at h
            · split at h
              · rename_i hc
                simp only [Bool.and_eq_true] at hc
                exact ihBody _ Γ' h m dt
                  (lookup_cons_of_scopeCompat Γ name .TFp hc.1.2 m dt hm)
              · cases h
            · cases h
          · cases h
        · split at h
          · rename_i hc
            simp only [Bool.and_eq_true] at hc
            exact ihBody _ Γ' h m dt
              (lookup_cons_of_scopeCompat Γ name (tow f) hc.1.2 m dt hm)
          · cases h
    | lit l =>
      simp only [simScopeF] at h
      split at h
      · split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          exact ihBody _ Γ' h m dt
            (lookup_cons_of_scopeCompat Γ name .TFp hc.1.2 m dt hm)
        · cases h
      · split at h
        · exact ihBody Γ Γ' h m dt hm
        · cases h
    | var src =>
      simp only [simScopeF] at h
      split at h
      · exact ihBody Γ Γ' h m dt hm
      · cases h
    | proj pe i =>
      cases pe with
      | var t =>
        simp only [simScopeF] at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          exact ihBody _ Γ' h m dt
            (lookup_cons_of_scopeCompat Γ name .TFp hc.1.2 m dt hm)
        · cases h
      | _ => simp [simScopeF] at h
    | _ => simp [simScopeF] at h
  | var _ => intro Γ Γ' h m dt hm; simp only [simScopeF, Option.some.injEq] at h; subst h; exact hm
  | unitVal => intro Γ Γ' h m dt hm; simp only [simScopeF, Option.some.injEq] at h; subst h; exact hm
  | seq a b iha ihb =>
    intro Γ Γ' h m dt hm
    simp only [simScopeF] at h
    rcases hA : simScopeF tow S T A Γ a with _ | Γ₁
    · rw [hA] at h; cases h
    · rw [hA] at h
      exact ihb Γ₁ Γ' h m dt (iha Γ Γ₁ hA m dt hm)
  | ifThenElse c t e _ _ _ =>
    intro Γ Γ' h m dt hm
    cases c with
    | var _ =>
      simp only [simScopeF] at h
      split at h
      · split at h
        · rw [Option.some.injEq] at h; subst h; exact hm
        · cases h
      · cases h
    | _ => simp [simScopeF] at h
  | whileLoop c body _ _ =>
    intro Γ Γ' h m dt hm
    cases c with
    | var _ =>
      simp only [simScopeF] at h
      split at h
      · split at h
        · rw [Option.some.injEq] at h; subst h; exact hm
        · cases h
      · cases h
    | _ => simp [simScopeF] at h
  | forFold i lo hi body _ _ _ =>
    intro Γ Γ' h m dt hm
    by_cases hs : ∃ a b : Int, lo = .lit (.int a) ∧ hi = .lit (.int b)
    · obtain ⟨a, b, rfl, rfl⟩ := hs
      simp only [simScopeF] at h
      split at h
      · split at h
        · rw [Option.some.injEq] at h; subst h; exact hm
        · cases h
      · cases h
    · rw [simScopeF_forFold_none tow S T A Γ i lo hi body hs] at h
      cases h
  | assign name rhs _ =>
    intro Γ Γ' h m dt hm
    cases rhs with
    | lit _ =>
      simp only [simScopeF] at h
      split at h
      · rw [Option.some.injEq] at h; subst h; exact hm
      · cases h
    | app f args =>
      simp only [simScopeF] at h
      split at h
      · cases h
      · split at h
        · rw [Option.some.injEq] at h; subst h; exact hm
        · cases h
    | _ => simp [simScopeF] at h
  | tuple es _ =>
    intro Γ Γ' h m dt hm
    simp only [simScopeF] at h
    split at h
    · rw [Option.some.injEq] at h; subst h; exact hm
    · cases h
  | typeAscription e _ ih =>
    intro Γ Γ' h
    simp only [simScopeF] at h
    exact ih Γ Γ' h
  | _ => intro Γ Γ' h; simp [simScopeF] at h

/-! ## §4  The simulation predicate -/

/-- Simulation of `e` by `arrTower A (litTower T c)` for its lowering `c`, under
    the side conditions of `simScopeF towerOfCallName`, with the source run of
    `forToLoop e`. -/
def ProgSimF (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (S T : List String) (A : TowerScope) (e : ImpExpr) : Prop :=
  ∀ (fuel : Nat) (Γ Γ' : TowerScope) (c : LowCT) (env env' : Env) (rs : RustState) (v : Value),
    simScopeF towerOfCallName S T A Γ e = some Γ' →
    ScopeBound rs Γ → NamesFresh rs S →
    haxToLowCT e = some c →
    evalImp bi fuel (forToLoop e) env = some (v, env') →
    envAgreesRustT bridge env rs →
    ∃ rs', RustExec N leafSpec (arrTower A (litTower T c)) rs rs' ∧
      envAgreesRustT bridge env' rs' ∧ ScopeBound rs' Γ' ∧ NamesFresh rs' S

theorem litTower_scalarSetExpr (T : List String) (x : String) (e : SExpr) :
    litTower T (.RScalarSetExpr x e) = .RScalarSetExpr x e := by
  simp [litTower]

theorem arrTower_scalarSetExpr (A : TowerScope) (x : String) (e : SExpr) :
    arrTower A (.RScalarSetExpr x e) = .RScalarSetExpr x e := by
  simp [arrTower]

/-- A trip of the lowered loop body: from the counter set to `j`, the shifted
    body runs as the body from the counter set to `lo + j`. -/
theorem forShift_exec (N : Nat) (leafSpec : LeafSpec) (T : List String) (A : TowerScope)
    (i : String) (lo j : Nat) (bodyC : LowCT) (rs r : RustState)
    (h : RustExec N leafSpec (arrTower A (litTower T bodyC)) (rsSetScalar rs i (lo + j)) r) :
    RustExec N leafSpec (arrTower A (litTower T (forShift i lo bodyC))) (rsSetScalar rs i j) r := by
  unfold forShift
  split
  · rename_i h0
    subst h0
    simpa using h
  · rw [litTower_seq, arrTower_seq, litTower_scalarSetExpr, arrTower_scalarSetExpr]
    refine RustExec.seq _ _ _ (rsSetScalar rs i (lo + j)) _ ?_ h
    have hS := RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) i
      (.SAdd (.SVar i) (.SLit lo)) (rsSetScalar rs i j)
    have hv : (SExpr.SAdd (.SVar i) (.SLit lo)).evalState (rsSetScalar rs i j) = lo + j := by
      simp [SExpr.evalState, rsSetScalar]; omega
    rw [hv, rsSetScalar_collapse] at hS
    exact hS

section ArmsF

variable (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
  (S T : List String) (A : TowerScope)

theorem progSimF_of_simScopeF_none (e : ImpExpr)
    (h : ∀ Γ, simScopeF towerOfCallName S T A Γ e = none) :
    ProgSimF bridge bi N leafSpec S T A e := by
  intro fuel Γ Γ' c env env' rs v hScope
  rw [h Γ] at hScope
  cases hScope

/-- On a program without subprograms that `simScopeF` accepts as `simScopeA` does,
    whose conditions are trivially scalar and which `forToLoop` fixes, the
    simulation of `ProgSimA` gives that of `ProgSimF`. -/
theorem progSimF_of_progSimA (e : ImpExpr)
    (hScopeEq : ∀ Γ, simScopeF towerOfCallName S T A Γ e = simScopeA towerOfCallName S T A Γ e)
    (hConds : condsScalar S e = true)
    (hLoop : ∀ Γ Γ', simScopeF towerOfCallName S T A Γ e = some Γ' → forToLoop e = e)
    (h : ProgSimA bridge bi N leafSpec S T A e) : ProgSimF bridge bi N leafSpec S T A e := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  rw [hLoop Γ Γ' hScope] at hEval
  rw [hScopeEq] at hScope
  exact h fuel Γ Γ' c env env' rs v hScope hConds hSB hSF hHax hEval hAgree

theorem progSimF_seq (a b : ImpExpr)
    (iha : ProgSimF bridge bi N leafSpec S T A a) (ihb : ProgSimF bridge bi N leafSpec S T A b) :
    ProgSimF bridge bi N leafSpec S T A (.seq a b) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScopeF] at hScope
  rcases hA : simScopeF towerOfCallName S T A Γ a with _ | Γ₁
  · rw [hA] at hScope; cases hScope
  rw [hA] at hScope
  obtain ⟨aC, bC, hAtrans, hBtrans, hC⟩ := haxToLowCT_seq_some a b c hHax
  subst hC
  simp only [forToLoop] at hEval
  obtain ⟨vA, env_mid, hAeval, hBeval⟩ := evalImp_seq_inv bi fuel _ _ env v env' hEval
  obtain ⟨rs_mid, hAexec, hAgreeMid, hSBmid, hSFmid⟩ :=
    iha fuel Γ Γ₁ aC env env_mid rs vA hA hSB hSF hAtrans hAeval hAgree
  obtain ⟨rs', hBexec, hAgree', hSB', hSF'⟩ :=
    ihb fuel Γ₁ Γ' bC env_mid env' rs_mid v hScope hSBmid hSFmid hBtrans hBeval hAgreeMid
  rw [litTower_seq, arrTower_seq]
  exact ⟨rs', rustExec_RSeq_chain N leafSpec _ _ rs rs_mid rs' hAexec hBexec,
         hAgree', hSB', hSF'⟩

theorem progSimF_ifThenElse (cond : String) (t e : ImpExpr)
    (iht : ProgSimF bridge bi N leafSpec S T A t) (ihe : ProgSimF bridge bi N leafSpec S T A e) :
    ProgSimF bridge bi N leafSpec S T A (.ifThenElse (.var cond) t e) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScopeF] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hCondS
  have hCondT : rs.rsTower cond = none := hSF cond (mem_of_contains S cond hCondS)
  rcases hT : simScopeF towerOfCallName S T A Γ t with _ | Γt
  · rw [hT] at hScope; cases hScope
  rcases hE : simScopeF towerOfCallName S T A Γ e with _ | Γe
  · rw [hT, hE] at hScope; cases hScope
  rw [hT, hE] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  obtain ⟨tC, eC, hTtrans, hEtrans, hC⟩ := haxToLowCT_ifThenElse_var_some cond t e c hHax
  subst hC
  rw [litTower_ifNz, arrTower_ifNz]
  simp only [forToLoop] at hEval
  rcases evalImp_ifThenElse_var_inv bi fuel cond _ _ env v env' hEval with
    ⟨hCond, hTeval⟩ | ⟨hCond, hEeval⟩
  · obtain ⟨rs', hTexec, hAgree', hSB', hSF'⟩ :=
      iht fuel Γ Γt tC env env' rs v hT hSB hSF hTtrans hTeval hAgree
    have hScalar : rs.rsScalar cond = 1 :=
      envAgreesRustT_bool_to_scalar bridge env rs cond true hAgree hCondT hCond
    refine ⟨rs', rustExec_RIfNz_dispatch_true N leafSpec cond _ _ rs rs' 1 hScalar
      (by decide) hTexec, hAgree', ?_, hSF'⟩
    exact ScopeBound_of_lookup_mono rs' Γ Γt
      (simScopeF_lookup_mono towerOfCallName S T A t Γ Γt hT) hSB'
  · obtain ⟨rs', hEexec, hAgree', hSB', hSF'⟩ :=
      ihe fuel Γ Γe eC env env' rs v hE hSB hSF hEtrans hEeval hAgree
    have hScalar : rs.rsScalar cond = 0 :=
      envAgreesRustT_bool_to_scalar bridge env rs cond false hAgree hCondT hCond
    refine ⟨rs', rustExec_RIfNz_dispatch_false N leafSpec cond _ _ rs rs' hScalar hEexec,
      hAgree', ?_, hSF'⟩
    exact ScopeBound_of_lookup_mono rs' Γ Γe
      (simScopeF_lookup_mono towerOfCallName S T A e Γ Γe hE) hSB'

theorem progSimF_whileLoop (cond : String) (body : ImpExpr)
    (ihBody : ProgSimF bridge bi N leafSpec S T A body) :
    ProgSimF bridge bi N leafSpec S T A (.whileLoop (.var cond) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScopeF] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hCondS
  rcases hB : simScopeF towerOfCallName S T A Γ body with _ | Γb
  · rw [hB] at hScope; cases hScope
  rw [hB] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  obtain ⟨bC, hBtrans, hC⟩ := haxToLowCT_whileLoop_var_some cond body c hHax
  subst hC
  rw [litTower_whileNz, arrTower_whileNz]
  have hAnf : AnfShaped body = true := (haxToLowCT_isSome_iff_anf body).mp (by rw [hBtrans]; rfl)
  have hMono := simScopeF_lookup_mono towerOfCallName S T A body Γ Γb hB
  simp only [forToLoop] at hEval
  induction fuel generalizing env env' rs v with
  | zero =>
    exact absurd hEval (fun h => evalImp_whileLoop_var_fuel_zero_inv bi cond _ env v env' h)
  | succ n IH =>
    have hCondT : rs.rsTower cond = none := hSF cond (mem_of_contains S cond hCondS)
    rcases evalImp_whileLoop_var_step_inv bi n cond _ env v env' hEval
        (anfShaped_forToLoop_val_or_err bi body hAnf (n+1) env) with
      ⟨hCondF, hv, henv⟩ | ⟨vB, env_mid, hCondTrue, hBodyEval, hLoopRec⟩
    · subst hv
      subst henv
      have hScalar : rs.rsScalar cond = 0 :=
        envAgreesRustT_bool_to_scalar bridge _ rs cond false hAgree hCondT hCondF
      exact ⟨rs, RustExec.whileFalse cond _ rs hScalar, hAgree, hSB, hSF⟩
    · have hScalar : rs.rsScalar cond = 1 :=
        envAgreesRustT_bool_to_scalar bridge env rs cond true hAgree hCondT hCondTrue
      obtain ⟨rs_mid, hBodyExec, hAgreeMid, hSBmid, hSFmid⟩ :=
        ihBody (n+1) Γ Γb bC env env_mid rs vB hB hSB hSF hBtrans hBodyEval hAgree
      have hSBmid' : ScopeBound rs_mid Γ := ScopeBound_of_lookup_mono rs_mid Γ Γb hMono hSBmid
      obtain ⟨rs', hLoopExec, hAgree', hSB', hSF'⟩ :=
        IH env_mid env' rs_mid v hSBmid' hSFmid hLoopRec hAgreeMid
      exact ⟨rs', RustExec.whileTrue cond _ rs rs_mid rs' 1 hScalar (by decide)
               hBodyExec hLoopExec, hAgree', hSB', hSF'⟩

/-- The counted-loop arm: by induction on the number of trips left, each trip
    binds the counter to its value in the environment and in the scalar heap and
    runs the body's simulation, whose exit scope extends the loop's scope. -/
theorem progSimF_forFold (i : String) (lo hi : Int) (body : ImpExpr)
    (ihBody : ProgSimF bridge bi N leafSpec S T A body) :
    ProgSimF bridge bi N leafSpec S T A (.forFold i (.lit (.int lo)) (.lit (.int hi)) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScopeF] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hlo, hhi⟩, hiS⟩ := hc
  rcases hB : simScopeF towerOfCallName S T A Γ body with _ | Γb
  · rw [hB] at hScope; cases hScope
  rw [hB] at hScope
  simp only [Option.some.injEq] at hScope
  subst hScope
  have hMono := simScopeF_lookup_mono towerOfCallName S T A body Γ Γb hB
  obtain ⟨bodyC, hBtrans, rfl⟩ := haxToLowCT_forFold_lit_some i lo hi body c hlo hhi hHax
  have hAnf : AnfShaped body = true := (haxToLowCT_isSome_iff_anf body).mp (by rw [hBtrans]; rfl)
  rw [litTower_for, arrTower_for]
  have hRun : (denoteForLoop bi fuel i lo hi (forToLoop body)).run env = (.val v, env') := by
    simp only [forToLoop] at hEval
    unfold evalImp at hEval
    rw [denote_forLoop_lit_run] at hEval
    split at hEval
    · rename_i w e1 hw
      simp only [Option.some.injEq, Prod.mk.injEq] at hEval
      obtain ⟨rfl, rfl⟩ := hEval
      exact hw
    · cases hEval
  have hloN := Int.toNat_of_nonneg hlo
  have hhiN := Int.toNat_of_nonneg hhi
  have key : ∀ (d j fuel : Nat) (env env'' : Env) (rs : RustState) (w : Value),
      j + d = hi.toNat - lo.toNat → ScopeBound rs Γ → NamesFresh rs S →
      envAgreesRustT bridge env rs →
      (denoteForLoop bi fuel i (lo + j) hi (forToLoop body)).run env = (.val w, env'') →
      ∃ rs', TripsFrom N leafSpec i (arrTower A (litTower T (forShift i lo.toNat bodyC))) j d rs rs' ∧
        envAgreesRustT bridge env'' rs' ∧ ScopeBound rs' Γ ∧ NamesFresh rs' S := by
    intro d
    induction d with
    | zero =>
      intro j fuel env env'' rs w hj hSB hSF hAgree hRun
      rw [denoteForLoop_ge_run bi fuel i (lo + j) hi _ env (by omega)] at hRun
      injection hRun with _ h2
      subst h2
      exact ⟨rs, rfl, hAgree, hSB, hSF⟩
    | succ d ih =>
      intro j fuel env env'' rs w hj hSB hSF hAgree hRun
      have hlt : lo + j < hi := by omega
      cases fuel with
      | zero =>
        rw [denoteForLoop_zero_run bi i (lo + j) hi _ env hlt] at hRun
        injection hRun with h1
        cases h1
      | succ m =>
        rw [denoteForLoop_succ_run bi m i (lo + j) hi _ env hlt] at hRun
        rcases anfShaped_forToLoop_val_or_err bi body hAnf (m + 1)
            (env.extend i (.int (lo + j))) with ⟨vB, envB, hb⟩ | ⟨msg, envB, hb⟩
        swap
        · rw [hb] at hRun
          injection hRun with h1
          cases h1
        rw [hb] at hRun
        have hTi : rs.rsTower i = none := hSF i (mem_of_contains S i hiS)
        have hAgree1 : envAgreesRustT bridge (env.extend i (.int (lo + j)))
            (rsSetScalar rs i (lo.toNat + j)) :=
          envAgreesRustT_extend_scalar_fresh bridge env rs i _ _ hTi
            (by simp only [valueToScalar]; rw [if_pos (by omega)]; congr 1; omega) hAgree
        obtain ⟨rs_mid, hBodyExec, hAgreeMid, hSBmid, hSFmid⟩ :=
          ihBody (m + 1) Γ Γb bodyC _ envB (rsSetScalar rs i (lo.toNat + j)) vB hB hSB hSF hBtrans
            (by unfold evalImp; rw [hb]) hAgree1
        have hStep := forShift_exec N leafSpec T A i lo.toNat j bodyC rs rs_mid hBodyExec
        have hRun' : (denoteForLoop bi m i (lo + ((j + 1 : Nat) : Int)) hi (forToLoop body)).run envB =
            (.val w, env'') := by
          rw [show lo + ((j + 1 : Nat) : Int) = lo + j + 1 by push_cast; ring]
          exact hRun
        obtain ⟨rs', hTrips, hA', hSB', hSF'⟩ :=
          ih (j + 1) m envB env'' rs_mid w (by omega)
            (ScopeBound_of_lookup_mono rs_mid Γ Γb hMono hSBmid) hSFmid hAgreeMid hRun'
        exact ⟨rs', ⟨rs_mid, hStep, hTrips⟩, hA', hSB', hSF'⟩
  obtain ⟨rs', hTrips, hA', hSB', hSF'⟩ :=
    key (hi.toNat - lo.toNat) 0 fuel env env' rs v (by omega) hSB hSF hAgree (by simpa using hRun)
  have hExec := rustExec_rFor_of_tripsFrom N leafSpec i _ (hi.toNat - lo.toNat) 0 rs rs rs'
    (RustExec.forZero i _ rs) hTrips
  rw [Nat.zero_add] at hExec
  exact ⟨rs', hExec, hA', hSB', hSF'⟩

theorem progSimF_letBind_lit (name : String) (l : ImpLit) (body : ImpExpr)
    (hLit : LitStoreAgrees bridge leafSpec)
    (ihBody : ProgSimF bridge bi N leafSpec S T A body) :
    ProgSimF bridge bi N leafSpec S T A (.letBind name (.lit l) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScopeF] at hScope
  obtain ⟨bodyC, m, hBodyTrans, hDecode, hC⟩ := haxToLowCT_letBind_lit_some name l body c hHax
  subst hC
  simp only [forToLoop] at hEval
  have hBodyEval := evalImp_letBind_lit_inv bi fuel name l _ env v env' hEval
  by_cases hTm : T.contains name = true
  · rw [if_pos hTm] at hScope
    split at hScope
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨⟨hW, hCompat⟩, hNotS⟩ := hc
      have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
      obtain ⟨k, hk, hl, hm⟩ : ∃ k : Nat, k < 2 ^ 64 ∧ Value.ofLit l = .int (k : Int) ∧ k = m := by
        cases l with
        | int n =>
          simp only [litWord, Bool.and_eq_true, decide_eq_true_eq] at hW
          obtain ⟨h0, h1⟩ := hW
          refine ⟨n.toNat, by omega, by simp [Value.ofLit, Int.toNat_of_nonneg h0], ?_⟩
          simp only [Value.ofLit, valueToScalar, if_pos h0, Option.some.injEq] at hDecode
          exact hDecode
        | _ => simp [litWord] at hW
      subst hm
      rw [litTower_lit_mem T name k bodyC hTm, arrTower_letZero, arrTower_seq, arrTower_limbStore]
      set loc : Located := { locVar := name, locSrc := .TFp } with hloc
      set rs_init := rsSetTower rs name ⟨.TFp, default⟩ with hrs_init
      have hLookup : locatedLookup rs_init loc = some default := locatedLookup_letZero rs name .TFp
      set newVal := leafSpec.limbStore loc (default : RustVal .TFp) 0 (BitVec.ofNat 64 k)
        with hnewVal
      have hStore : RustExec N leafSpec (.RLimbStore loc 0 (BitVec.ofNat 64 k)) rs_init
          (locatedUpdate rs_init loc newVal) :=
        RustExec.limbStore loc 0 _ rs_init default hLookup
      have hRsMidEq : locatedUpdate rs_init loc newVal = rsSetTower rs name ⟨.TFp, newVal⟩ := by
        show rsSetTower (rsSetTower rs name ⟨.TFp, default⟩) name ⟨.TFp, newVal⟩
            = rsSetTower rs name ⟨.TFp, newVal⟩
        exact rsSetTower_collapse rs name ⟨.TFp, default⟩ ⟨.TFp, newVal⟩
      have hBridge : bridge .TFp (Value.ofLit l) newVal := by
        rw [hl]; exact hLit name k hk
      have hAgreeMid : envAgreesRustT bridge (env.extend name (Value.ofLit l))
          (locatedUpdate rs_init loc newVal) := by
        rw [hRsMidEq]
        exact envAgreesRustT_extend_tower bridge env rs name _ .TFp newVal hAgree hBridge
      have hSBmid : ScopeBound (locatedUpdate rs_init loc newVal) ((name, .TFp) :: Γ) := by
        rw [hRsMidEq]
        exact ScopeBound_rsSetTower_cons rs Γ name .TFp newVal hCompat hSB
      have hSFmid : NamesFresh (locatedUpdate rs_init loc newVal) S := by
        rw [hRsMidEq]
        exact NamesFresh_rsSetTower rs S name _ hNotMem hSF
      obtain ⟨rs', hBodyExec, hAgree', hSB', hSF'⟩ :=
        ihBody fuel ((name, .TFp) :: Γ) Γ' bodyC _ env' _ v hScope hSBmid hSFmid
          hBodyTrans hBodyEval hAgreeMid
      exact ⟨rs', RustExec.letZero name .TFp _ rs rs'
        (RustExec.seq _ _ _ _ _ hStore hBodyExec), hAgree', hSB', hSF'⟩
    · cases hScope
  · rw [if_neg hTm] at hScope
    split at hScope
    · rename_i hIn
      rw [litTower_lit_not_mem T name m bodyC (by simpa using hTm), arrTower_letU64Zero,
        arrTower_seq, arrTower_scalarSet]
      have hFresh : TowerFresh rs name := hSF name (mem_of_contains S name hIn)
      have hAgreeExt : envAgreesRustT bridge (env.extend name (Value.ofLit l))
                        (rsSetScalar rs name m) :=
        envAgreesRustT_extend_scalar_fresh bridge env rs name (Value.ofLit l) m hFresh hDecode
          hAgree
      obtain ⟨rs', hBodyExec, hAgree', hSB', hSF'⟩ :=
        ihBody fuel Γ Γ' bodyC (env.extend name (Value.ofLit l)) env' (rsSetScalar rs name m) v
          hScope hSB hSF hBodyTrans hBodyEval hAgreeExt
      exact ⟨rs', rustExec_RLetU64Zero_ScalarSet N leafSpec name m _ rs rs' hBodyExec,
             hAgree', hSB', hSF'⟩
    · cases hScope

theorem progSimF_letBind_var (name src : String) (body : ImpExpr)
    (ihBody : ProgSimF bridge bi N leafSpec S T A body) :
    ProgSimF bridge bi N leafSpec S T A (.letBind name (.var src) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScopeF] at hScope
  split at hScope
  · rename_i hc
    simp only [forToLoop] at hEval
    obtain ⟨w, hw, hBodyEval⟩ := evalImp_letBind_var_inv bi fuel _ _ _ env v env' hEval
    by_cases hEq : name = src
    · subst hEq
      rw [haxToLowCT_letBind_var_self] at hHax
      rw [Env.extend_self env _ w hw] at hBodyEval
      exact ihBody fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hBodyEval hAgree
    · have hIn : S.contains name = true ∧ S.contains src = true := by simp_all
      obtain ⟨bodyC, hBodyT, rfl⟩ := haxToLowCT_letBind_var_ne_some name src body c hEq hHax
      obtain ⟨rs', hExec, hAgree', hSB', hSF'⟩ :=
        ihBody fuel Γ Γ' bodyC (env.extend name w) env' (rsSetScalar rs name (rs.rsScalar src))
          v hScope hSB hSF hBodyT hBodyEval
          (envAgreesRustT_extend_copy bridge env rs name src w
            (hSF name (mem_of_contains S name hIn.1)) (hSF src (mem_of_contains S src hIn.2))
            hw hAgree)
      rw [litTower_letBind_copy, arrTower_letBind_copy]
      exact ⟨rs', rustExec_letBind_copy N leafSpec name src _ rs rs' hEq hExec,
        hAgree', hSB', hSF'⟩
  · cases hScope

theorem progSimF_letBind_app (name f : String) (args : List ImpExpr) (body : ImpExpr)
    (hLeaf : LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hf_arr : f ≠ "array_update") (hf_idx : f ≠ "index")
    (ihBody : ProgSimF bridge bi N leafSpec S T A body) :
    ProgSimF bridge bi N leafSpec S T A (.letBind name (.app f args) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScopeF, if_neg hf_arr, if_neg hf_idx] at hScope
  split at hScope
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨hNotSc, hArgsIn⟩, hAvoid⟩, hCompat⟩, hNotS⟩ := hc
    have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
    obtain ⟨args', bodyC, hArgsT, hBodyT, hC⟩ :=
      haxToLowCT_letBind_app_some name f args body c hf_arr hf_idx (by simpa using hNotSc) hHax
    subst hC
    rw [litTower_letZero, litTower_seq, litTower_call, arrTower_letZero, arrTower_seq, arrTower_call]
    have hAllVar := argsInScope_allVars Γ _ args hArgsIn
    simp only [forToLoop] at hEval
    rw [forToLoopArgs_of_vars args hAllVar] at hEval
    have hArgsEnv := evalImp_letBind_app_argsDefined bi fuel name f args _ env v env'
      hAllVar hEval
    obtain ⟨vals, vRes, hAV, hBi, hBodyEval⟩ :=
      evalImp_letBind_app_vars_inv bi fuel name f args _ env v env' hArgsEnv hEval
    have hAB : ArgsTowerBound rs args' := argsInScope_bound Γ _ rs hSB args args' hArgsIn hArgsT
    have hAF : ∀ a ∈ args', a.locVar ≠ name := argsAvoid_fresh name _ args args' hAvoid hArgsT
    set dt := towerOfCallName f with hdt_def
    set dest : Located := { locVar := name, locSrc := dt } with hdest_def
    set rs_init := rsSetTower rs name ⟨dt, default⟩ with hrs_init_def
    have hABinit : ArgsTowerBound rs_init args' :=
      ArgsTowerBound_preserved_extend rs args' name ⟨dt, default⟩ hAF hAB
    have hLookup : locatedLookup rs_init dest = some default := locatedLookup_letZero rs name dt
    set argList := args'.filterMap (fun a => rs_init.rsTower a.locVar) with hargList_def
    set newVal := leafSpec.call f dt (args'.map (·.locDst)) default argList with hnewVal_def
    set rs_mid := locatedUpdate rs_init dest newVal with hrs_mid_def
    have hCallArgs : ∀ a ∈ args', ∃ vv, rs_init.rsTower a.locVar = some ⟨a.locDst, vv⟩ :=
      hABinit
    have hCall : RustExec N leafSpec (.RCall f dest args') rs_init rs_mid :=
      RustExec.call (N := N) (leafSpec := leafSpec)
        f dest args' rs_init default argList hLookup rfl hCallArgs
    have hArgsAgree :
        List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => bridge p.1 v p.2) vals argList := by
      rw [hargList_def, hrs_init_def, filterMap_rsSetTower_avoid rs name _ args' hAF]
      exact argsAgree_of_envAgrees bridge env rs dt hAgree.2 args args' vals hArgsT hAV hAB
    have hBridgeAgr : bridge dt vRes newVal := hLeaf args' vals argList default vRes hBi hArgsAgree
    have hRsMidEq : rs_mid = rsSetTower rs name ⟨dt, newVal⟩ := by
      show rsSetTower (rsSetTower rs name ⟨dt, default⟩) name ⟨dt, newVal⟩
           = rsSetTower rs name ⟨dt, newVal⟩
      exact rsSetTower_collapse rs name ⟨dt, default⟩ ⟨dt, newVal⟩
    have hAgreeMid : envAgreesRustT bridge (env.extend name vRes) rs_mid := by
      rw [hRsMidEq]
      exact envAgreesRustT_extend_tower bridge env rs name vRes dt newVal hAgree hBridgeAgr
    have hSBmid : ScopeBound rs_mid ((name, dt) :: Γ) := by
      rw [hRsMidEq]
      exact ScopeBound_rsSetTower_cons rs Γ name dt newVal hCompat hSB
    have hSFmid : NamesFresh rs_mid S := by
      rw [hRsMidEq]
      exact NamesFresh_rsSetTower rs S name _ hNotMem hSF
    obtain ⟨rs', hBodyExec, hAgreeFinal, hSB', hSF'⟩ :=
      ihBody fuel ((name, dt) :: Γ) Γ' bodyC (env.extend name vRes) env' rs_mid v
        hScope hSBmid hSFmid hBodyT hBodyEval hAgreeMid
    refine ⟨rs', ?_, hAgreeFinal, hSB', hSF'⟩
    refine RustExec.letZero name dt _ rs rs' ?_
    exact RustExec.seq _ _ _ _ _ hCall hBodyExec
  · cases hScope

theorem progSimF_letBind_proj (name t : String) (i : Nat) (body : ImpExpr)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (ihBody : ProgSimF bridge bi N leafSpec S T A body) :
    ProgSimF bridge bi N leafSpec S T A (.letBind name (.proj (.var t) i) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScopeF] at hScope
  split at hScope
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hLk, hNe⟩, hCompat⟩, hNotS⟩ := hc
    have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
    obtain ⟨bodyC, hBodyT, hC⟩ := haxToLowCT_letBind_proj_some name t i body c hHax
    subst hC
    rw [litTower_letZero, litTower_seq, litTower_tupleLoad, arrTower_letZero, arrTower_seq,
      arrTower_tupleLoad]
    simp only [forToLoop] at hEval
    obtain ⟨vTup, vi, hEnvT, hProjI, hBodyEval⟩ :=
      evalImp_letBind_proj_inv bi fuel name t i _ env v env' hEval
    obtain ⟨srcV, hRawT⟩ := hSB t .TFp hLk
    have hSrcLook : locatedLookup rs { locVar := t, locSrc := .TFp } = some srcV :=
      locatedLookup_of_rsTower rs t .TFp srcV hRawT
    set dst : Located := { locVar := name, locSrc := .TFp } with hdst
    set src : Located := { locVar := t, locSrc := .TFp } with hsrc
    set rs_init := rsSetTower rs name ⟨.TFp, default⟩ with hrs_init
    have hDstLook : locatedLookup rs_init dst = some default :=
      locatedLookup_letZero rs name .TFp
    have hSrcLook' : locatedLookup rs_init src = some srcV := by
      rw [hrs_init,
          CatCrypt.Crypto.Jasmin.LowCT.locatedLookup_rsSetTower_other
            rs name ⟨.TFp, default⟩ src (Ne.symm hNe)]
      exact hSrcLook
    set newVal := leafSpec.tupleLoad dst default ⟨src.locDst, srcV⟩ i with hnewVal
    set rs_mid := locatedUpdate rs_init dst newVal with hrs_mid
    have hLoad : RustExec N leafSpec (.RTupleLoad dst src i) rs_init rs_mid :=
      RustExec.tupleLoad dst src i rs_init default srcV hDstLook hSrcLook'
    have hTupBridge : bridge .TFp vTup srcV := hAgree.2 t vTup hEnvT .TFp srcV hRawT
    have hCompBridge : bridge .TFp vi newVal := hProj name i vTup vi srcV hTupBridge hProjI
    have hRsMidEq : rs_mid = rsSetTower rs name ⟨.TFp, newVal⟩ := by
      show rsSetTower (rsSetTower rs name ⟨.TFp, default⟩) name ⟨.TFp, newVal⟩
          = rsSetTower rs name ⟨.TFp, newVal⟩
      exact rsSetTower_collapse rs name ⟨.TFp, default⟩ ⟨.TFp, newVal⟩
    have hAgreeMid : envAgreesRustT bridge (env.extend name vi) rs_mid := by
      rw [hRsMidEq]
      exact envAgreesRustT_extend_tower bridge env rs name vi .TFp newVal hAgree hCompBridge
    have hSBmid : ScopeBound rs_mid ((name, .TFp) :: Γ) := by
      rw [hRsMidEq]
      exact ScopeBound_rsSetTower_cons rs Γ name .TFp newVal hCompat hSB
    have hSFmid : NamesFresh rs_mid S := by
      rw [hRsMidEq]
      exact NamesFresh_rsSetTower rs S name _ hNotMem hSF
    obtain ⟨rs', hBodyExec, hAgreeFinal, hSB', hSF'⟩ :=
      ihBody fuel ((name, .TFp) :: Γ) Γ' bodyC (env.extend name vi) env' rs_mid v
        hScope hSBmid hSFmid hBodyT hBodyEval hAgreeMid
    refine ⟨rs', ?_, hAgreeFinal, hSB', hSF'⟩
    refine RustExec.letZero name .TFp _ rs rs' ?_
    exact RustExec.seq _ _ _ _ _ hLoad hBodyExec
  · cases hScope

theorem progSimF_letBind_index (name f arr idx : String) (body : ImpExpr)
    (hf_arr : f ≠ "array_update") (hf_idx : f = "index")
    (hIdx : IndexAgrees bridge bi leafSpec)
    (ihBody : ProgSimF bridge bi N leafSpec S T A body) :
    ProgSimF bridge bi N leafSpec S T A (.letBind name (.app f [.var arr, .var idx]) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScopeF, if_neg hf_arr, if_pos hf_idx] at hScope
  rcases hA : List.lookup arr A with _ | t
  · rw [hA] at hScope; cases hScope
  simp only [hA] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hLk, hNe⟩, hIdxS'⟩, hCompat⟩, hNotS⟩ := hc
  have hNotMem : name ∉ S := not_mem_of_not_contains S name hNotS
  have hIdxS : idx ∈ S := mem_of_contains S idx hIdxS'
  obtain ⟨bodyC, hBodyT, hC⟩ := haxToLowCT_letBind_index_some name f arr idx body c hf_arr hf_idx hHax
  subst hC
  rw [litTower_letZero, litTower_seq, litTower_arrLoad, arrTower_letZero, arrTower_seq,
    arrTower_arrLoad A _ { locVar := arr, locSrc := .TFp } idx t hA]
  simp only [forToLoop, forToLoopArgs] at hEval
  have hArgsEnv := evalImp_letBind_app_argsDefined bi fuel name f [.var arr, .var idx] _ env v
    env' (by simp) hEval
  obtain ⟨vals, vRes, hAV, hBi, hBodyEval⟩ :=
    evalImp_letBind_app_vars_inv bi fuel name f _ _ env v env' hArgsEnv hEval
  obtain ⟨vArr, vIdx, rfl, hvArr, hvIdx⟩ := allVars_two hAV
  subst hf_idx
  obtain ⟨arrV, hRawArr⟩ := hSB arr t hLk
  have hTIdx : rs.rsTower idx = none := hSF idx hIdxS
  have hk : ∀ n, valueToScalar vIdx = some n → n = rs.rsScalar idx :=
    fun n hn => (hAgree.1 idx vIdx n hvIdx hTIdx hn).symm
  set dst : Located := { locVar := name, locSrc := .TFp } with hdst
  set src : Located := { locVar := arr, locSrc := t } with hsrc
  set rs_init := rsSetTower rs name ⟨.TFp, default⟩ with hrs_init
  have hDstLook : locatedLookup rs_init dst = some default := locatedLookup_letZero rs name .TFp
  have hSrcLook : locatedLookup rs_init src = some arrV := by
    rw [hrs_init, CatCrypt.Crypto.Jasmin.LowCT.locatedLookup_rsSetTower_other
      rs name ⟨.TFp, default⟩ src (Ne.symm hNe)]
    exact locatedLookup_of_rsTower rs arr t arrV hRawArr
  set newVal := leafSpec.arrLoad dst default ⟨t, arrV⟩ (rs.rsScalar idx) with hnewVal
  set rs_mid := locatedUpdate rs_init dst newVal with hrs_mid
  have hLoad : RustExec N leafSpec (.RArrLoad dst src idx) rs_init rs_mid :=
    RustExec.arrLoad dst src idx rs_init (rs.rsScalar idx) default arrV rfl hDstLook hSrcLook
  have hB : bridge .TFp vRes newVal :=
    hIdx name t vArr vIdx vRes arrV (rs.rsScalar idx) (hAgree.2 arr vArr hvArr t arrV hRawArr)
      hk hBi
  have hRsMidEq : rs_mid = rsSetTower rs name ⟨.TFp, newVal⟩ := by
    show rsSetTower (rsSetTower rs name ⟨.TFp, default⟩) name ⟨.TFp, newVal⟩
        = rsSetTower rs name ⟨.TFp, newVal⟩
    exact rsSetTower_collapse rs name ⟨.TFp, default⟩ ⟨.TFp, newVal⟩
  have hAgreeMid : envAgreesRustT bridge (env.extend name vRes) rs_mid := by
    rw [hRsMidEq]
    exact envAgreesRustT_extend_tower bridge env rs name vRes .TFp newVal hAgree hB
  have hSBmid : ScopeBound rs_mid ((name, .TFp) :: Γ) := by
    rw [hRsMidEq]
    exact ScopeBound_rsSetTower_cons rs Γ name .TFp newVal hCompat hSB
  have hSFmid : NamesFresh rs_mid S := by
    rw [hRsMidEq]
    exact NamesFresh_rsSetTower rs S name _ hNotMem hSF
  obtain ⟨rs', hBodyExec, hAgreeFinal, hSB', hSF'⟩ :=
    ihBody fuel ((name, .TFp) :: Γ) Γ' bodyC (env.extend name vRes) env' rs_mid v
      hScope hSBmid hSFmid hBodyT hBodyEval hAgreeMid
  refine ⟨rs', ?_, hAgreeFinal, hSB', hSF'⟩
  refine RustExec.letZero name .TFp _ rs rs' ?_
  exact RustExec.seq _ _ _ _ _ hLoad hBodyExec

theorem progSimF_letBind_arrUpdate (name f arr idx src : String) (body : ImpExpr)
    (hf_arr : f = "array_update")
    (hUpd : ArrUpdateAgrees bridge bi leafSpec)
    (ihBody : ProgSimF bridge bi N leafSpec S T A body) :
    ProgSimF bridge bi N leafSpec S T A
      (.letBind name (.app f [.var arr, .var idx, .var src]) body) := by
  intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  simp only [simScopeF, if_pos hf_arr] at hScope
  rcases hA : List.lookup arr A with _ | t
  · rw [hA] at hScope; cases hScope
  simp only [hA] at hScope
  split at hScope
  swap
  · cases hScope
  rename_i hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hName, hLk⟩, hLkSrc⟩, hIdxS'⟩ := hc
  have hIdxS : idx ∈ S := mem_of_contains S idx hIdxS'
  subst hName
  obtain ⟨bodyC, hBodyT, hC⟩ :=
    haxToLowCT_letBind_arrUpdate_some name f name idx src body c hf_arr hHax
  subst hC
  rw [litTower_seq, litTower_arrStore, arrTower_seq,
    arrTower_arrStore A { locVar := name, locSrc := .TBytes 0 } { locVar := src, locSrc := .TBytes 0 }
      idx t hA]
  simp only [forToLoop, forToLoopArgs] at hEval
  have hArgsEnv := evalImp_letBind_app_argsDefined bi fuel name f
    [.var name, .var idx, .var src] _ env v env' (by simp) hEval
  obtain ⟨vals, vRes, hAV, hBi, hBodyEval⟩ :=
    evalImp_letBind_app_vars_inv bi fuel name f _ _ env v env' hArgsEnv hEval
  obtain ⟨vArr, vIdx, vSrc, rfl, hvArr, hvIdx, hvSrc⟩ := allVars_three hAV
  subst hf_arr
  obtain ⟨arrV, hRawArr⟩ := hSB name t hLk
  obtain ⟨srcV, hRawSrc⟩ := hSB src t.elemType hLkSrc
  have hTIdx : rs.rsTower idx = none := hSF idx hIdxS
  have hk : ∀ n, valueToScalar vIdx = some n → n = rs.rsScalar idx :=
    fun n hn => (hAgree.1 idx vIdx n hvIdx hTIdx hn).symm
  have hNotMem : name ∉ S := by
    intro hm
    rw [hSF name hm] at hRawArr
    cases hRawArr
  set arrL : Located := { locVar := name, locSrc := t } with harrL
  set srcL : Located := { locVar := src, locSrc := t.elemType } with hsrcL
  have hArrLook : locatedLookup rs arrL = some arrV := locatedLookup_of_rsTower rs name t arrV hRawArr
  have hSrcLook : locatedLookup rs srcL = some srcV :=
    locatedLookup_of_rsTower rs src t.elemType srcV hRawSrc
  set newVal := leafSpec.arrStore arrL arrV (rs.rsScalar idx) ⟨t.elemType, srcV⟩ with hnewVal
  have hStore : RustExec N leafSpec (.RArrStore arrL idx srcL) rs (rsSetTower rs name ⟨t, newVal⟩) :=
    RustExec.arrStore arrL idx srcL rs (rs.rsScalar idx) arrV srcV rfl hArrLook hSrcLook
  have hB : bridge t vRes newVal :=
    hUpd name t vArr vIdx vSrc vRes arrV srcV (rs.rsScalar idx)
      (hAgree.2 name vArr hvArr t arrV hRawArr) hk (hAgree.2 src vSrc hvSrc _ srcV hRawSrc) hBi
  have hAgreeMid : envAgreesRustT bridge (env.extend name vRes) (rsSetTower rs name ⟨t, newVal⟩) :=
    envAgreesRustT_extend_tower bridge env rs name vRes t newVal hAgree hB
  have hSBmid : ScopeBound (rsSetTower rs name ⟨t, newVal⟩) Γ :=
    ScopeBound_rsSetTower_same rs Γ name t newVal hLk hSB
  have hSFmid : NamesFresh (rsSetTower rs name ⟨t, newVal⟩) S :=
    NamesFresh_rsSetTower rs S name _ hNotMem hSF
  obtain ⟨rs', hBodyExec, hAgreeFinal, hSB', hSF'⟩ :=
    ihBody fuel Γ Γ' bodyC (env.extend name vRes) env' _ v
      hScope hSBmid hSFmid hBodyT hBodyEval hAgreeMid
  exact ⟨rs', RustExec.seq _ _ _ _ _ hStore hBodyExec, hAgreeFinal, hSB', hSF'⟩

end ArmsF

/-! ## §5  The checker at a given tower dispatch -/

/-- The call names `simScopeF` reads the tower dispatch of: those of `letBind`s
    and `assign`s on the statement path, including counted-loop bodies. -/
def scopeCallNamesF : ImpExpr → List String
  | .letBind _ (.app f _) body => f :: scopeCallNamesF body
  | .letBind _ _ body => scopeCallNamesF body
  | .seq a b => scopeCallNamesF a ++ scopeCallNamesF b
  | .ifThenElse _ t e => scopeCallNamesF t ++ scopeCallNamesF e
  | .whileLoop _ body => scopeCallNamesF body
  | .forFold _ _ _ body => scopeCallNamesF body
  | .assign _ (.app f _) => [f]
  | .typeAscription e _ => scopeCallNamesF e
  | _ => []

/-- `simScopeF` at two tower dispatches that agree on the call names it reads
    coincide. -/
theorem simScopeF_eq_tow (tow tow' : String → TowerType) (S T : List String) (A : TowerScope)
    (e : ImpExpr) :
    (∀ f ∈ scopeCallNamesF e, tow f = tow' f) →
      ∀ Γ, simScopeF tow S T A Γ e = simScopeF tow' S T A Γ e := by
  induction e using ImpExpr.ind with
  | letBind name val body _ ihBody =>
    intro h Γ
    cases val with
    | app f args =>
      simp only [scopeCallNamesF, List.mem_cons] at h
      have hf := h f (Or.inl rfl)
      have hb := ihBody fun g hg => h g (Or.inr hg)
      simp only [simScopeF, hf, hb]
    | lit l =>
      simp only [scopeCallNamesF] at h
      simp only [simScopeF, ihBody h]
    | var src =>
      simp only [scopeCallNamesF] at h
      simp only [simScopeF, ihBody h]
    | proj pe i =>
      simp only [scopeCallNamesF] at h
      cases pe <;> simp only [simScopeF, ihBody h]
    | _ => simp only [simScopeF]
  | seq a b iha ihb =>
    intro h Γ
    simp only [scopeCallNamesF, List.mem_append] at h
    have ha := iha fun g hg => h g (Or.inl hg)
    have hb := ihb fun g hg => h g (Or.inr hg)
    simp only [simScopeF, ha, hb]
  | ifThenElse c t e _ iht ihe =>
    intro h Γ
    simp only [scopeCallNamesF, List.mem_append] at h
    have ht := iht fun g hg => h g (Or.inl hg)
    have he := ihe fun g hg => h g (Or.inr hg)
    cases c <;> simp only [simScopeF, ht, he]
  | whileLoop c body _ ih =>
    intro h Γ
    simp only [scopeCallNamesF] at h
    cases c <;> simp only [simScopeF, ih h]
  | forFold i lo hi body _ _ ih =>
    intro h Γ
    simp only [scopeCallNamesF] at h
    by_cases hs : ∃ a b : Int, lo = .lit (.int a) ∧ hi = .lit (.int b)
    · obtain ⟨a, b, rfl, rfl⟩ := hs
      simp only [simScopeF, ih h]
    · rw [simScopeF_forFold_none _ S T A Γ i lo hi body hs,
        simScopeF_forFold_none _ S T A Γ i lo hi body hs]
  | typeAscription e _ ih =>
    intro h Γ
    simp only [scopeCallNamesF] at h
    simp only [simScopeF, ih h]
  | assign name rhs _ =>
    intro h Γ
    cases rhs with
    | app f args =>
      simp only [scopeCallNamesF, List.mem_singleton] at h
      simp only [simScopeF, h f rfl]
    | _ => simp only [simScopeF]
  | _ => intro _ Γ; rfl

/-! ## §6  The program-level theorem -/

/-- **Program-level simulation with counted loops.**  Every source program
    simulates by `arrTower A (litTower T c)` for its lowering `c` under
    `envAgreesRustT`, with the counted loops of the source read as `forLoop`
    (`forToLoop`), from the hypotheses of `haxToLowCT_simulates_programA`. -/
theorem haxToLowCT_simulates_programF
    (bridge : ValueTowerBridge) (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (S T : List String) (A : TowerScope)
    (hLeaf : ∀ f, f ≠ "array_update" → f ≠ "index" →
      LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) bridge)
    (hProj : TupleLoadAgrees bridge leafSpec)
    (hLit : LitStoreAgrees bridge leafSpec)
    (hIdx : IndexAgrees bridge bi leafSpec)
    (hUpd : ArrUpdateAgrees bridge bi leafSpec)
    (e : ImpExpr) : ProgSimF bridge bi N leafSpec S T A e := by
  have noneArm := progSimF_of_simScopeF_none bridge bi N leafSpec S T A
  have hA := haxToLowCT_simulates_programA bridge bi N leafSpec S T A hLeaf hProj hLit hIdx hUpd
  induction e using ImpExpr.ind with
  | var name =>
    exact progSimF_of_progSimA bridge bi N leafSpec S T A _ (fun _ => rfl) rfl
      (fun _ _ _ => rfl) (hA _)
  | unitVal =>
    exact progSimF_of_progSimA bridge bi N leafSpec S T A _ (fun _ => rfl) rfl
      (fun _ _ _ => rfl) (hA _)
  | tuple es _ =>
    refine progSimF_of_progSimA bridge bi N leafSpec S T A _ (fun _ => rfl) rfl ?_ (hA _)
    intro Γ Γ' h
    simp only [simScopeF] at h
    split at h
    · rename_i hAll
      simp only [forToLoop, forToLoopArgs_of_allVar es hAll]
    · cases h
  | seq a b iha ihb => exact progSimF_seq bridge bi N leafSpec S T A a b iha ihb
  | letBind name val body _ ihBody =>
    cases val with
    | lit l => exact progSimF_letBind_lit bridge bi N leafSpec S T A name l body hLit ihBody
    | app f args =>
      by_cases hf_arr : f = "array_update"
      · rcases hSh : varArgs3 args with _ | ⟨arr, idx, src⟩
        · refine noneArm _ fun Γ => ?_
          simp only [simScopeF, if_pos hf_arr]
          split
          · simp [varArgs3] at hSh
          · rfl
        · rw [varArgs3_some hSh]
          exact progSimF_letBind_arrUpdate bridge bi N leafSpec S T A name f arr idx src body
            hf_arr hUpd ihBody
      by_cases hf_idx : f = "index"
      · rcases hSh : varArgs2 args with _ | ⟨arr, idx⟩
        · refine noneArm _ fun Γ => ?_
          simp only [simScopeF, if_neg hf_arr, if_pos hf_idx]
          split
          · simp [varArgs2] at hSh
          · rfl
        · rw [varArgs2_some hSh]
          exact progSimF_letBind_index bridge bi N leafSpec S T A name f arr idx body hf_arr
            hf_idx hIdx ihBody
      exact progSimF_letBind_app bridge bi N leafSpec S T A name f args body
        (hLeaf f hf_arr hf_idx) hf_arr hf_idx ihBody
    | var src => exact progSimF_letBind_var bridge bi N leafSpec S T A name src body ihBody
    | proj pe i =>
      cases pe with
      | var t =>
        exact progSimF_letBind_proj bridge bi N leafSpec S T A name t i body hProj ihBody
      | _ => exact noneArm _ fun Γ => by simp [simScopeF]
    | _ => exact noneArm _ fun Γ => by simp [simScopeF]
  | ifThenElse cond t e _ iht ihe =>
    cases cond with
    | var v_cond => exact progSimF_ifThenElse bridge bi N leafSpec S T A v_cond t e iht ihe
    | _ => exact noneArm _ fun Γ => by simp [simScopeF]
  | whileLoop cond body _ ihBody =>
    cases cond with
    | var v_cond => exact progSimF_whileLoop bridge bi N leafSpec S T A v_cond body ihBody
    | _ => exact noneArm _ fun Γ => by simp [simScopeF]
  | forFold i lo hi body _ _ ihBody =>
    by_cases hs : ∃ a b : Int, lo = .lit (.int a) ∧ hi = .lit (.int b)
    · obtain ⟨a, b, rfl, rfl⟩ := hs
      exact progSimF_forFold bridge bi N leafSpec S T A i a b body ihBody
    · exact noneArm _ fun Γ => simScopeF_forFold_none _ S T A Γ i lo hi body hs
  | assign name rhs _ =>
    cases rhs with
    | lit l =>
      exact progSimF_of_progSimA bridge bi N leafSpec S T A _ (fun _ => rfl) rfl
        (fun _ _ _ => rfl) (hA _)
    | app f args =>
      refine progSimF_of_progSimA bridge bi N leafSpec S T A _ (fun _ => rfl) rfl ?_ (hA _)
      intro Γ Γ' h
      simp only [simScopeF] at h
      split at h
      · cases h
      · split at h
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          simp only [forToLoop, forToLoopArgs_of_vars args (argsInScope_allVars Γ _ args hc.1.1)]
        · cases h
    | _ => exact noneArm _ fun Γ => by simp [simScopeF]
  | typeAscription e _ ih =>
    intro fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
    simp only [simScopeF] at hScope
    rw [haxToLowCT_typeAscription_eq] at hHax
    simp only [forToLoop] at hEval
    rw [evalImp_typeAscription] at hEval
    exact ih fuel Γ Γ' c env env' rs v hScope hSB hSF hHax hEval hAgree
  | _ => exact noneArm _ fun Γ => by simp [simScopeF]

end CatCrypt.Crypto.Hax
