/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTStruct
public import CatCrypt.Hax.Ascent.EarlyExit
public import CatCrypt.Hax.Ascent.Structs

/-!
# The descent relations over the ascent judgment

The descent (`haxToLowCTK`, the struct flattening `flatE`, the renaming
`renameVar`) and the ascent (`Hax.Ascent.Corres`) describe runs of the same
evaluator `Hax.denote'`.  This module states the descent relations in terms of
the ascent judgment.

**Transport.**  `corres_transport` carries a `Corres` statement across any
relation `R` between environments that a pair of programs preserves at every
fuel, with the same outcome on both sides: the second program corresponds to
the same value from every environment `R`-related to an entry environment of
the first.  The exit environment is fixed by fuel monotonicity
(`Hax.Ascent.denote'_val_mono`).  `corres_renameVar` is its instance at the
renaming relation `RenRel` (`denote'_renameVar`), and `corres_flatProj` at the
flattening relation `StructFlatAt` for a field call (`flatProj_sim`).

**Leaves.**  The builtin premises `FieldSound` and `UpdateSound` of the struct
arms hold for a table whose field and update calls are the ascent leaves
`projLeaf` and `updateLeaf` of a struct with at least two fields
(`fieldSound_of_projLeaf`, `updateSound_of_updateLeaf`).  `structUpdateName` is hax-lean's
`structUpdateHead` (`structUpdateName_eq`).

**Exit.**  `ExitSim` takes a `denote'` run ending in a value; a `CorresX`
statement supplies one, with the value `excVal (R σ)`.  `exitSim_corresX` is the
composite for an expression, `haxToLowCTFn_corresX` and
`haxToLowCTFn_fnCorresX` for a function body: the result slot of the lowered
function holds the decoding of the thrown or returned value (`excPayload`).

## Main results

* `corres_transport` — `Corres` across an environment relation preserved at every
  fuel
* `corres_renameVar`, `corres_flatProj` — its instances at `RenRel` and
  `StructFlatAt`
* `fieldSound_of_projLeaf`, `updateSound_of_updateLeaf` — the struct builtin
  premises from the ascent leaves
* `exitSim_corresX` — an `ExitSim` expression under a `CorresX` statement
* `haxToLowCTFn_corresX`, `haxToLowCTFn_fnCorresX` — the lowered function's result
  slot under `CorresX` and `FnCorresX`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit Value Env Outcome Builtins denote')
open _root_.Hax.Ascent (Corres CorresX excVal ExcPlain FnCorresX encExc projLeaf updateLeaf)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT RustState RustExec LeafSpec)

/-! ## Transport along an environment relation -/

section Transport

variable {S : Type} {bi : Builtins}

/-- **Transport.**  When from `R`-related environments the runs of `e` and `e'`
    have the same outcome and end in `R`-related environments at every fuel, a
    `Corres` statement for `e` gives one for `e'` with the same value, from and to
    the environments `R`-related to the entry and exit environments of `e`. -/
theorem corres_transport {R : Env → Env → Prop} {e e' : ImpExpr}
    {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (hsim : ∀ fuel env envF, R env envF →
      ((denote' bi fuel e).run env).1 = ((denote' bi fuel e').run envF).1 ∧
        R ((denote' bi fuel e).run env).2 ((denote' bi fuel e').run envF).2)
    (h : Corres bi P G e V Q) :
    Corres bi (fun envF σ => ∃ env, P env σ ∧ R env envF) G e' V
      (fun envF σ => ∃ env, Q env σ ∧ R env envF) := by
  rintro envF σ ⟨env, hP, hR⟩ hG
  obtain ⟨f₀, env', hQ, hrun⟩ := h env σ hP hG
  obtain ⟨h1, h2⟩ := hsim f₀ env envF hR
  have r₀ : denote' bi f₀ e env = (.val (V σ), env') := hrun f₀ (Nat.le_refl _)
  have hv : (denote' bi f₀ e' envF).1 = .val (V σ) := by
    have : ((denote' bi f₀ e).run env).1 = .val (V σ) := by
      show (denote' bi f₀ e env).1 = _; rw [r₀]
    rw [← this]; exact h1.symm
  refine ⟨f₀, (denote' bi f₀ e' envF).2, ⟨env', hQ, ?_⟩, fun fuel hf => ?_⟩
  · have : ((denote' bi f₀ e).run env).2 = env' := by
      show (denote' bi f₀ e env).2 = _; rw [r₀]
    rw [← this]; exact h2
  · rw [_root_.Hax.Ascent.denote'_val_mono bi hv hf]
    exact Prod.ext hv rfl

/-- **Renaming.**  Under the side conditions of `denote'_renameVar`, a `Corres`
    statement for `e` holds for `renameVar v w e` from the `RenRel v w`-related
    environments. -/
theorem corres_renameVar {v w : String} {e : ImpExpr} (hs : renameSafe v w e = true)
    (ha : varAbsent w e = true) {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (h : Corres bi P G e V Q) :
    Corres bi (fun envF σ => ∃ env, P env σ ∧ RenRel v w env envF) G (renameVar v w e) V
      (fun envF σ => ∃ env, Q env σ ∧ RenRel v w env envF) :=
  corres_transport (fun fuel env envF hR => denote'_renameVar bi v w e hs ha fuel env envF hR) h

/-- **Flattened projection.**  A `Corres` statement for the field call `c` on the
    struct variable `s` holds for the component variable `comp` the projection
    arm produces, from the environments in which `s` is flattened. -/
theorem corres_flatProj {L : StructLayout} {sv : StructVars} {c s comp : String}
    {fs : List String} (hp : projArm L sv c s = some comp)
    (hfs : structFields L sv s = some fs) (hF : FieldSound bi fs)
    {P Q : Env → S → Prop} {G : S → Prop} {V : S → Value}
    (h : Corres bi P G (.app c [.var s]) V Q) :
    Corres bi (fun envF σ => ∃ env, P env σ ∧ StructFlatAt fs s env envF) G (.var comp) V
      (fun envF σ => ∃ env, Q env σ ∧ StructFlatAt fs s env envF) := by
  refine corres_transport (fun fuel env envF hR => ?_) h
  obtain ⟨v, h1, h2⟩ := flatProj_sim bi fuel L sv c s comp fs env envF hp hfs hR hF
  rw [h1, h2]; exact ⟨rfl, hR⟩

end Transport

/-! ## The struct builtins as ascent leaves -/

section Leaves

/-- The field calls of a struct with at least two fields, interpreted by the
    ascent leaves `projLeaf`, satisfy `FieldSound`. -/
theorem fieldSound_of_projLeaf {bi : Builtins} {fs : List String} (hn : 2 ≤ fs.length)
    (h : ∀ i f, fs[i]? = some f → ∀ vs, bi ("." ++ f) vs = projLeaf i fs.length vs) :
    FieldSound bi fs := by
  intro vs i f _ hi
  rw [h i f hi]
  simp [projLeaf, show ¬ fs.length ≤ 1 by omega]

/-- The update calls of a struct with at least two fields, interpreted by the
    ascent leaves `updateLeaf`, satisfy `UpdateSound`. -/
theorem updateSound_of_updateLeaf {bi : Builtins} {S : String} {fs : List String}
    (hn : 2 ≤ fs.length)
    (h : ∀ i, i < fs.length → ∀ vs,
      bi (structUpdateName S i fs.length) vs = updateLeaf i fs.length vs) :
    UpdateSound bi S fs := by
  intro vs i v hlen hi
  rw [h i hi]
  simp [updateLeaf, show ¬ fs.length ≤ 1 by omega, hlen, hi]

/-- The update call name of the descent is hax-lean's `structUpdateHead`. -/
theorem structUpdateName_eq (S : String) (i n : Nat) :
    structUpdateName S i n = _root_.Hax.structUpdateHead S i n := rfl

end Leaves

/-! ## The exit-flag lowering under `CorresX` -/

section Exit

variable {S : Type} {bi : Builtins} {N : Nat} {leafSpec : LeafSpec}

/-- **Expression.**  For an expression the lowering simulates, a `CorresX`
    statement gives, from every related entry environment and agreeing state, a
    related exit environment and a `RustExec` run of the lowered command ending in
    agreement with the outcome `val (excVal (R σ))`. -/
theorem exitSim_corresX {e : ImpExpr} (hsim : ExitSim bi N leafSpec e)
    {P Q : Env → S → Prop} {G : S → Prop} {R : S → Except Value Value}
    (hX : CorresX bi P G e R Q) {tl : Bool} {fl : Option String} {c : LowCT} {x : Bool}
    (hok : exitSimOk tl fl.isSome e = true) (hctx : RunCtx fl)
    (hK : haxToLowCTK true tl fl e = some (c, x)) {env : Env} {σ : S} (hP : P env σ)
    (hG : G σ) {rs : RustState} (hag : envAgreesOff env rs)
    (h0 : rs.rsScalar exitRetName = 0) :
    ∃ env', Q env' σ ∧ ∃ rs', RustExec N leafSpec c rs rs' ∧
      envAgreesExit tl (.val (excVal (R σ))) env' rs' ∧
      (x = false → rs'.rsScalar exitRetName = 0) := by
  obtain ⟨f₀, env', hQ, hrun⟩ := hX env σ hP hG
  obtain ⟨rs', h1, h2, h3⟩ := hsim tl fl f₀ env env' _ rs c x hok hctx hK
    (hrun f₀ (Nat.le_refl _)) ⟨_, rfl⟩ hag h0
  exact ⟨env', hQ, rs', h1, h2, h3⟩

/-- The value an exception result carries: the thrown value or the normal result. -/
def excPayload : Except Value Value → Value
  | .error w => w
  | .ok u => u

/-- The scalar of a value outcome is the scalar of the value its exception reading
    carries. -/
theorem outcomeScalar_val_cfExcept (v : Value) :
    outcomeScalar (.val v) = valueToScalar (excPayload (_root_.Hax.Ascent.cfExcept v)) := by
  cases v with
  | controlFlow b w => cases b <;> rfl
  | _ => rfl

/-- The scalar of the outcome `val (excVal r)` is the scalar of the value `r`
    carries. -/
theorem outcomeScalar_excVal {r : Except Value Value} (h : ExcPlain r) :
    outcomeScalar (.val (excVal r)) = valueToScalar (excPayload r) := by
  rw [outcomeScalar_val_cfExcept, _root_.Hax.Ascent.cfExcept_excVal h]

/-- **Function.**  For a function body in the fragment, a `CorresX` statement with
    plain normal results gives a run of the lowered function whose result slot
    holds the decoding of the thrown or returned value. -/
theorem haxToLowCTFn_corresX (hs : ScalarOpsSound bi) {e : ImpExpr} {c : LowCT}
    (hok : exitSimOk true true e = true) (hK : haxToLowCTFn e = some c)
    {P Q : Env → S → Prop} {G : S → Prop} {R : S → Except Value Value}
    (hX : CorresX bi P G e R Q) (hplain : ∀ σ, G σ → ExcPlain (R σ)) {env : Env} {σ : S}
    (hP : P env σ) (hG : G σ) {rs : RustState} (hag : envAgreesOff env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧
      valueToScalar (excPayload (R σ)) = some (rs'.rsScalar exitResName) := by
  obtain ⟨f₀, env', _, hrun⟩ := hX env σ hP hG
  obtain ⟨rs', h1, h2⟩ := haxToLowCTFn_simulates_exit bi N leafSpec hs e c hok hK f₀ env env'
    _ rs (hrun f₀ (Nat.le_refl _)) ⟨_, rfl⟩ hag
  exact ⟨rs', h1, by rw [← outcomeScalar_excVal (hplain σ hG)]; exact h2⟩

/-- **Function, top-level form.**  A `FnCorresX` statement for a function body in
    the fragment gives, for every argument meeting the guard, a run of the lowered
    function whose result slot holds the decoding of the encoded thrown or returned
    value. -/
theorem haxToLowCTFn_fnCorresX {A Rt β : Type} [_root_.Hax.Ascent.HaxEnc Rt]
    [_root_.Hax.Ascent.HaxEnc β] (hs : ScalarOpsSound bi) {e : ImpExpr} {c : LowCT}
    (hok : exitSimOk true true e = true) (hK : haxToLowCTFn e = some c)
    {entry : A → Env} {G : A → Prop} {f : A → Except Rt β}
    (h : FnCorresX bi e entry G f) {a : A} (hG : G a) {rs : RustState}
    (hag : envAgreesOff (entry a) rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧
      valueToScalar (excPayload (encExc (f a))) = some (rs'.rsScalar exitResName) := by
  obtain ⟨f₀, hrun⟩ := h a hG
  have h₀ := hrun f₀ (Nat.le_refl _)
  rcases ho : denote' bi f₀ e (entry a) with ⟨o, env'⟩
  rw [ho] at h₀
  cases o with
  | val v =>
    obtain ⟨rs', h1, h2⟩ := haxToLowCTFn_simulates_exit bi N leafSpec hs e c hok hK f₀
      (entry a) env' (.val v) rs ho ⟨_, rfl⟩ hag
    refine ⟨rs', h1, ?_⟩
    have hc : _root_.Hax.Ascent.cfExcept v = encExc (f a) := Option.some.inj h₀
    rw [← hc, ← outcomeScalar_val_cfExcept]; exact h2
  | _ => cases h₀

end Exit

end CatCrypt.Crypto.Hax
