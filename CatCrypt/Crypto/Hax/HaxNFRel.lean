/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.NF
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ProgramLoops -- deprecated_module: ignore
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_Exit -- deprecated_module: ignore

/-!
# The front's checked fragments lie in the normal form `NF`

Each shape predicate and scope checker of the `ImpExpr` front accepts only
expressions in the monadic A-normal form `Hax.NF`: `NF` is an upper bound of every
checked fragment. The scope checkers return an exit scope; an accepted expression is
one on which the checker returns `some`.

## Main results

* `isNFK_of_anfShaped`, `nf_of_haxToLowCT_isSome` — the shape of `haxToLowCT`
* `isNFK_of_anfShapedK`, `nf_of_haxToLowCTK_isSome` — the shape of the exit-flag
  lowering `haxToLowCTK`
* `isNFK_of_exitSimOk` — the fragment of the exit-flag simulation
* `nf_of_simScope`, `nf_of_simScopeL`, `nf_of_simScopeA`, `nf_of_simScopeF`,
  `nf_of_simScopeW` — the scope checkers
-/

@[expose] public section

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpPat nfAtom nfVar nfLit nfBound nfBoundOp nfRhs nfAssignRhs
  nfBreakArg isNFK isNF NF isNFK_of_isNF isNFK_true_of_false)
open CatCrypt.Crypto.Jasmin.LowCT (TowerType)

/-! ## Arguments and bounds -/

theorem nfAtom_of_isVar {e : ImpExpr} (h : isVar e = true) : nfAtom e = true := by
  cases e <;> simp_all [isVar, nfAtom]

theorem nfVar_of_isVar {e : ImpExpr} (h : isVar e = true) : nfVar e = true := by
  cases e <;> simp_all [isVar, nfVar]

theorem all_nfAtom_of_all_isVar {args : List ImpExpr} (h : args.all isVar = true) :
    args.all nfAtom = true := by
  simp only [List.all_eq_true] at h ⊢
  exact fun a ha => nfAtom_of_isVar (h a ha)

theorem all_nfVar_of_all_isVar {args : List ImpExpr} (h : args.all isVar = true) :
    args.all nfVar = true := by
  simp only [List.all_eq_true] at h ⊢
  exact fun a ha => nfVar_of_isVar (h a ha)

/-- The arguments of a limb read are atoms. -/
theorem all_nfAtom_of_limbReadArgs {f : String} {args : List ImpExpr}
    (h : (limbReadArgs f args).isSome = true) : args.all nfAtom = true := by
  unfold limbReadArgs at h
  split at h
  · split at h
    · simp [nfAtom]
    · simp at h
  · simp at h

/-- The argument condition of `AnfShaped` on a call gives atom arguments. -/
theorem all_nfAtom_of_anfArgs {f : String} {args : List ImpExpr}
    (h : args.all isVar = true ∨ (limbReadArgs f args).isSome = true) :
    args.all nfAtom = true := by
  rcases h with h | h
  · exact all_nfAtom_of_all_isVar h
  · exact all_nfAtom_of_limbReadArgs h

/-- Arguments in scope are atoms. -/
theorem all_nfAtom_of_argsInScope {Γ : TowerScope} {dt : TowerType} {args : List ImpExpr}
    (h : argsInScope Γ dt args = true) : args.all nfAtom = true := by
  induction args with
  | nil => rfl
  | cons a as ih =>
    cases a <;> simp_all [argsInScope, nfAtom]

/-- A bound `impBoundToSExpr` converts is a counted-loop bound. -/
theorem nfBound_of_impBoundToSExpr {e : ImpExpr} (h : (impBoundToSExpr e).isSome = true) :
    nfBound e = true := by
  fun_induction impBoundToSExpr e <;> simp_all [nfBound, nfBoundOp]

/-! ## The shape of `haxToLowCT` -/

/-- An expression of the shape `AnfShaped` is in normal form in every loop context. -/
theorem isNFK_of_anfShaped (e : ImpExpr) (h : AnfShaped e = true) (il : Bool) :
    isNFK il e = true := by
  refine isNFK_of_isNF e il (show isNFK false e = true from ?_)
  fun_induction AnfShaped e <;>
    simp_all [-List.all_eq_true, isNFK, nfRhs, nfAssignRhs, nfLit, nfBound,
      all_nfAtom_of_all_isVar, all_nfVar_of_all_isVar, nfBound_of_impBoundToSExpr,
      isNFK_true_of_false]
  exact all_nfAtom_of_anfArgs h.1

/-- An expression `haxToLowCT` lowers is in normal form. -/
theorem nf_of_haxToLowCT_isSome (e : ImpExpr) (h : (haxToLowCT e).isSome = true) : NF e :=
  isNFK_of_anfShaped e ((haxToLowCT_isSome_iff_anf e).mp h) false

/-! ## The shape of the exit-flag lowering -/

/-- A right-hand side `letHead` lowers is a normal-form right-hand side. -/
theorem nfRhs_of_letHead {name : String} {val : ImpExpr}
    (h : (letHead name val).isSome = true) : nfRhs val = true := by
  unfold letHead at h
  split at h
  · rename_i f args
    simp only [nfRhs]
    cases hargs : haxArgsToLocated (towerOfCallName f) args with
    | some _ =>
      exact all_nfAtom_of_all_isVar
        ((haxArgsToLocated_isSome_iff_all_isVar (towerOfCallName f) args).mp (by simp [hargs]))
    | none =>
      simp only [hargs] at h
      exact all_nfAtom_of_limbReadArgs (by simpa using h)
  all_goals simp_all [nfRhs]

/-- A right-hand side `letHeadK` lowers is a normal-form right-hand side. -/
theorem nfRhs_of_letHeadK {sc : Bool} {name : String} {val : ImpExpr}
    (h : (letHeadK sc name val).isSome = true) : nfRhs val = true := by
  unfold letHeadK at h
  split at h
  · split at h
    · simp [nfRhs, nfAtom]
    · exact nfRhs_of_letHead h
  · exact nfRhs_of_letHead h

/-- A value `storeScalar` writes is an atom or `unitVal`. -/
theorem nfBreakArg_of_storeScalar {slot : String} {e : ImpExpr}
    (h : (storeScalar slot e).isSome = true) : nfBreakArg e = true := by
  cases e <;> simp_all [storeScalar, nfBreakArg]

/-- The payload of a `cfBreak` `exitStore` lowers is an atom or `unitVal`. -/
theorem nfBreakArg_of_exitStore {e : ImpExpr} (h : (exitStore e).isSome = true) :
    nfBreakArg e = true :=
  nfBreakArg_of_storeScalar (by simpa [exitStore] using h)

/-- A tail value `resultStore` lowers is in normal form in every loop context. -/
theorem isNFK_of_resultStore {il : Bool} {e : ImpExpr} (h : (resultStore e).isSome = true) :
    isNFK il e = true := by
  have hb := nfBreakArg_of_storeScalar (slot := exitResName) (e := e) h
  cases e <;> simp_all [nfBreakArg, isNFK]

/-- The bounds `forBounds` accepts are literals. -/
theorem nfLit_of_forBounds {lo hi : ImpExpr} (h : (forBounds lo hi).isSome = true) :
    nfLit lo = true ∧ nfLit hi = true := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨rfl, rfl, _⟩ := forBounds_some hp
  exact ⟨rfl, rfl⟩

/-- The bounds `forBounds` or `forBoundsRt` accepts are a literal and a counted-loop
    bound. -/
theorem nfBound_of_forBoundsK {lo hi : ImpExpr}
    (h : ((forBounds lo hi).isSome || (forBoundsRt lo hi).isSome) = true) :
    nfLit lo = true ∧ nfBound hi = true := by
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨rfl, rfl, _⟩ := forBounds_some hp
    exact ⟨rfl, rfl⟩
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨rfl, rfl⟩ := forBoundsRt_some hp
    exact ⟨rfl, rfl⟩

/-- The bounds of a `forFoldReturn` in the fragment `exitSimOk` are a literal and a
    counted-loop bound. -/
theorem nfBound_of_exitForOk {lo hi : ImpExpr}
    (h : ((forBounds lo hi).isSome || forBoundsRtOk lo hi) = true) :
    nfLit lo = true ∧ nfBound hi = true := by
  refine nfBound_of_forBoundsK ?_
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with h | h
  · exact Or.inl h
  · right
    unfold forBoundsRtOk at h
    cases hb : forBoundsRt lo hi <;> simp_all

/-- An expression of the shape `AnfShapedK sc tl il` is in normal form in loop
    context `il`. -/
theorem isNFK_of_anfShapedK (sc tl il : Bool) (e : ImpExpr) (h : AnfShapedK sc tl il e = true) :
    isNFK il e = true := by
  fun_induction AnfShapedK sc tl il e <;>
    simp_all [isNFK, nfBreakArg_of_exitStore,
      isNFK_of_resultStore, isNFK_of_anfShaped]
  all_goals first
    | exact nfRhs_of_letHeadK h.1
    | exact nfLit_of_forBounds h.1
    | exact nfBound_of_forBoundsK (by simpa using h.1)
    | exact nfBound_of_forBoundsK (by simp_all)
    | simpa [isNFK] using isNFK_of_anfShaped _ h true

/-- An expression `haxToLowCTK sc tl none` lowers is in normal form. -/
theorem nf_of_haxToLowCTK_isSome (sc tl : Bool) (e : ImpExpr)
    (h : (haxToLowCTK sc tl none e).isSome = true) : NF e :=
  isNFK_of_anfShapedK sc tl false e ((haxToLowCTK_isSome_iff_anfK sc tl none e).mp h)

/-- An expression of the fragment `exitSimOk tl il` is in normal form in loop context
    `il`. -/
theorem isNFK_of_exitSimOk (tl il : Bool) (e : ImpExpr) (h : exitSimOk tl il e = true) :
    isNFK il e = true := by
  fun_induction exitSimOk tl il e <;>
    simp_all [isNFK, nfRhs, nfAtom, nfBreakArg]
  all_goals first
    | exact nfLit_of_forBounds h.1.1
    | exact nfBound_of_exitForOk (by simpa using h.1.1)
    | exact nfBound_of_exitForOk (by simp_all)

/-! ## The scope checkers

Each theorem states that an expression the checker accepts, from any entry scope
and name sets, is in `NF`. -/

theorem nf_of_simScope (S : List String) (Γ : TowerScope) (e : ImpExpr)
    (h : (simScope S Γ e).isSome = true) : NF e := by
  show isNFK false e = true
  fun_induction simScope S Γ e <;>
    simp_all [-List.all_eq_true, isNFK, nfRhs, nfAssignRhs, all_nfAtom_of_all_isVar,
      all_nfVar_of_all_isVar]
  all_goals
    casesm* _ ∧ _
    exact all_nfAtom_of_argsInScope (by assumption)

theorem nf_of_simScopeL (S T : List String) (Γ : TowerScope) (e : ImpExpr)
    (h : (simScopeL S T Γ e).isSome = true) : NF e := by
  show isNFK false e = true
  fun_induction simScopeL S T Γ e <;>
    simp_all [-List.all_eq_true, isNFK, nfRhs, nfAssignRhs, all_nfAtom_of_all_isVar,
      all_nfVar_of_all_isVar]
  all_goals
    casesm* _ ∧ _
    exact all_nfAtom_of_argsInScope (by assumption)

theorem nf_of_simScopeA (tow : String → TowerType) (S T : List String) (A Γ : TowerScope)
    (e : ImpExpr) (h : (simScopeA tow S T A Γ e).isSome = true) : NF e := by
  show isNFK false e = true
  fun_induction simScopeA tow S T A Γ e <;>
    simp_all [-List.all_eq_true, isNFK, nfRhs, nfAssignRhs, all_nfVar_of_all_isVar]
  all_goals
    casesm* _ ∧ _
    exact all_nfAtom_of_argsInScope (by assumption)

theorem nf_of_simScopeF (tow : String → TowerType) (S T : List String) (A Γ : TowerScope)
    (e : ImpExpr) (h : (simScopeF tow S T A Γ e).isSome = true) : NF e := by
  show isNFK false e = true
  fun_induction simScopeF tow S T A Γ e <;>
    simp_all [-List.all_eq_true, isNFK, nfRhs, nfAssignRhs, nfLit, nfBound,
      all_nfVar_of_all_isVar, isNFK_true_of_false]
  all_goals
    casesm* _ ∧ _
    exact all_nfAtom_of_argsInScope (by assumption)

theorem nf_of_simScopeW (tow : String → TowerType) (D S T : List String) (A Γ : TowerScope)
    (e : ImpExpr) (h : (simScopeW tow D S T A Γ e).isSome = true) : NF e := by
  show isNFK false e = true
  fun_induction simScopeW tow D S T A Γ e <;>
    simp_all [-List.all_eq_true, isNFK, nfRhs, nfAssignRhs, nfLit, nfBound,
      all_nfVar_of_all_isVar, isNFK_true_of_false]
  all_goals
    casesm* _ ∧ _
    exact all_nfAtom_of_argsInScope (by assumption)

end CatCrypt.Crypto.Hax
