/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.Ascent.ExtTable
public import CatCrypt.Hax.Ascent.AscendHax
public import CatCrypt.Hax.Ascent.AscentOption

/-!
# The rules of the surface generator

The generator of `CatCrypt/Hax/Ascent/Generate.lean` derives the correspondence of a
literal over binding lists (`CorresB`, `CatCrypt/Hax/Ascent/AscendHax.lean`) and states
every value and binding list it produces explicitly, so that each side condition is a
closed equation, a lookup or a `BindsSub` over explicit lists.

## Exits

`CorresG bi Γ G e C W V T N` is `CorresB` with a guarded exit: when `C σ` holds the run
returns `controlFlow true (W σ)` and binds `T σ`, otherwise it returns `V σ` and binds
`N σ`. At the top of a function an exit is an early return, inside a loop body a break.
A derivation without exit is a `CorresG` with `C = fun _ => false` (`CorresG.ofPlain`).
The rules `corresG_seq`, `corresG_letBind`, `corresG_ifThenElse` and `corresG_cfBreak`
compose exits; `corresG_castVW`, `corresG_subN`, `corresG_subT` and `corresG_congrC`
replace values, binding lists and the exit condition by equal ones.

## Loops

The loop rules take an invariant `Λ σ a` that binds the variables the body assigns to the
components of the accumulator `a` and is independent of the index, and state the loop
result with the runtime's combinators:

| literal | rule | result |
|---|---|---|
| `forFold` without break | `corresB_forFoldP` | `Hax.foldRange` |
| `forFoldRev` without break | `corresB_forFoldRevP` | `Hax.foldRangeRev` |
| `forFold` with break | `corresB_forFoldG` | `Hax.forFold` with `stepCF` |
| `whileFold` | `corresB_whileFoldG` | `Hax.whileFold` with `stepCF`, on stopping states |
| `forFoldReturn` without loop break | `corresG_forFoldReturnG` | `Hax.forFoldReturn` with `stepRet` |

A body exit of a `forFoldReturn` is a return from the function: the loop exits with the
returned value (`retC`, `retOut`) and otherwise binds the final accumulator (`retAcc`).

A tuple whose last component has a product type is typed with that component under
`Boxed`, whose encoding is the component's own, so that the pair encodes as a pair.

The counted rules hold for all bounds: an empty range is a separate case
(`corres_guard_cases`). A break carries its value and the accumulator at the break
(`stepCF`); `cfState` and `cfVal` read the accumulator and the value of the loop.

## Functions

`fnCorres_of_corresB` and `fnCorresX_of_corresG` turn a derivation from the entry bindings
into `FnCorres` and, for a function with early return, `FnCorresX` of
`fun a => if C a then .error (w a) else .ok (v a)`.

## Main definitions

* `BList`, `CorresG`, `cfState`, `cfVal`, `stepCF`
* `stepRet`, `retC`, `retOut`, `retAcc`, `Boxed`

## Main results

* `corresG_seq`, `corresG_letBind`, `corresG_seqL`, `corresG_letBindL`,
  `corresG_ifThenElse`, `corresG_cfBreak`
* `corresB_forFoldP`, `corresB_forFoldRevP`, `corresB_forFoldG`, `corresB_whileFoldG`,
  `corresG_forFoldReturnG`
* `corresG_optMatch` — the `Option` match with guarded exits in the arms
* `whileFoldStops_of_measure` — termination of a while-fold from a decreasing measure
* `fnCorres_of_corresB`, `fnCorresX_of_corresG`
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-! ## The judgment with a guarded exit -/

section CorresG

/-- Binding lists. -/
abbrev BList := List (String × Value)

variable {S : Type} {bi : Builtins}

/-- **Correspondence with a guarded exit.** When `C σ` holds the run exits with
    `controlFlow true (W σ)` and binds `T σ`; otherwise it returns `V σ` and binds
    `N σ`. -/
def CorresG (bi : Builtins) (Γ : S → BList) (G : S → Prop) (e : ImpExpr) (C : S → Bool)
    (W V : S → Value) (T N : S → BList) : Prop :=
  CorresB bi Γ G e (fun σ => if C σ = true then .controlFlow true (W σ) else V σ)
    (fun σ => if C σ = true then T σ else N σ)

theorem CorresG.plain {Γ N T : S → BList} {G : S → Prop} {e : ImpExpr} {W V : S → Value}
    (h : CorresG bi Γ G e (fun _ => false) W V T N) : CorresB bi Γ G e V N := h

theorem CorresG.ofPlain {Γ N : S → BList} {G : S → Prop} {e : ImpExpr} {V : S → Value}
    (W : S → Value) (T : S → BList) (h : CorresB bi Γ G e V N) :
    CorresG bi Γ G e (fun _ => false) W V T N := h

/-- Consequence: weaken the entry bindings, strengthen the guard, and replace the exit
    values and bindings by equal ones and sub-bindings. -/
theorem corresG_conseq {Γ Γ' N N' T T' : S → BList} {G G' : S → Prop} {e : ImpExpr}
    {C : S → Bool} {W W' V V' : S → Value} (h : CorresG bi Γ G e C W V T N)
    (hΓ : ∀ σ, G' σ → BindsSub (Γ' σ) (Γ σ)) (hG : ∀ σ, G' σ → G σ)
    (hW : ∀ σ, G' σ → C σ = true → W σ = W' σ) (hV : ∀ σ, G' σ → C σ = false → V σ = V' σ)
    (hT : ∀ σ, G' σ → C σ = true → BindsSub (T σ) (T' σ))
    (hN : ∀ σ, G' σ → C σ = false → BindsSub (N σ) (N' σ)) :
    CorresG bi Γ' G' e C W' V' T' N' := by
  refine corres_conseq h (fun env σ hb hg => binds_of_sub hb (hΓ σ hg)) hG
    (fun σ hg => ?_) (fun env σ hg hb => ?_)
  · cases hC : C σ
    · simp only [Bool.false_eq_true, if_false]; exact hV σ hg hC
    · simp only [if_true]; rw [hW σ hg hC]
  · cases hC : C σ
    · simp only [hC, Bool.false_eq_true, if_false] at hb ⊢; exact binds_of_sub hb (hN σ hg hC)
    · simp only [hC, if_true] at hb ⊢; exact binds_of_sub hb (hT σ hg hC)

/-- **Sequence with a guarded exit.** An exit of the first expression is the exit of the
    sequence; otherwise the second runs. -/
theorem corresG_seq {Γ N₁ T₁ N₂ T₂ : S → BList} {G : S → Prop} {e1 e2 : ImpExpr}
    {C₁ C₂ : S → Bool} {W₁ V₁ W₂ V₂ : S → Value}
    (h1 : CorresG bi Γ G e1 C₁ W₁ V₁ T₁ N₁)
    (hp : ∀ σ, G σ → C₁ σ = false → (V₁ σ).isControlFlow = false)
    (h2 : CorresG bi N₁ (fun σ => G σ ∧ C₁ σ = false) e2 C₂ W₂ V₂ T₂ N₂) :
    CorresG bi Γ G (.seq e1 e2) (fun σ => C₁ σ || C₂ σ)
      (fun σ => if C₁ σ = true then W₁ σ else W₂ σ) V₂
      (fun σ => if C₁ σ = true then T₁ σ else T₂ σ) N₂ := by
  intro env σ hP hG
  obtain ⟨f₁, e₁, hQ₁, r₁⟩ := h1 env σ hP hG
  cases hC : C₁ σ with
  | true =>
    simp only [hC, if_true] at hQ₁ r₁
    refine ⟨f₁, e₁, ?_, fun fuel hf => ?_⟩
    · simp only [hC, Bool.true_or, if_true]; exact hQ₁
    · simp only [hC, Bool.true_or, if_true]
      exact denote'_seq_cf bi fuel (r₁ fuel hf)
  | false =>
    simp only [hC, Bool.false_eq_true, if_false] at hQ₁ r₁
    obtain ⟨f₂, e₂, hQ₂, r₂⟩ := h2 e₁ σ hQ₁ ⟨hG, hC⟩
    refine ⟨max f₁ f₂, e₂, ?_, fun fuel hf => ?_⟩
    · simp only [hC, Bool.false_or, Bool.false_eq_true, if_false]; exact hQ₂
    · simp only [hC, Bool.false_or, Bool.false_eq_true, if_false]
      rw [denote'_seq bi fuel (r₁ fuel (by omega)) (hp σ hG hC)]
      exact r₂ fuel (by omega)

/-- **`let` with a guarded exit.** -/
theorem corresG_letBind {Γ N₁ T₁ N₂ T₂ : S → BList} {G : S → Prop} {x : String}
    {val body : ImpExpr} {C₁ C₂ : S → Bool} {W₁ V₁ W₂ V₂ : S → Value}
    (h1 : CorresG bi Γ G val C₁ W₁ V₁ T₁ N₁)
    (hp : ∀ σ, G σ → C₁ σ = false → (V₁ σ).isControlFlow = false)
    (h2 : CorresG bi (fun σ => (x, V₁ σ) :: N₁ σ) (fun σ => G σ ∧ C₁ σ = false) body C₂ W₂ V₂
      T₂ N₂) :
    CorresG bi Γ G (.letBind x val body) (fun σ => C₁ σ || C₂ σ)
      (fun σ => if C₁ σ = true then W₁ σ else W₂ σ) V₂
      (fun σ => if C₁ σ = true then T₁ σ else T₂ σ) N₂ := by
  intro env σ hP hG
  obtain ⟨f₁, e₁, hQ₁, r₁⟩ := h1 env σ hP hG
  cases hC : C₁ σ with
  | true =>
    simp only [hC, if_true] at hQ₁ r₁
    refine ⟨f₁, e₁, ?_, fun fuel hf => ?_⟩
    · simp only [hC, Bool.true_or, if_true]; exact hQ₁
    · simp only [hC, Bool.true_or, if_true]
      exact denote'_letBind_cf bi fuel (r₁ fuel hf)
  | false =>
    simp only [hC, Bool.false_eq_true, if_false] at hQ₁ r₁
    obtain ⟨f₂, e₂, hQ₂, r₂⟩ := h2 _ σ (binds_extend hQ₁ x _) ⟨hG, hC⟩
    refine ⟨max f₁ f₂, e₂, ?_, fun fuel hf => ?_⟩
    · simp only [hC, Bool.false_or, Bool.false_eq_true, if_false]; exact hQ₂
    · simp only [hC, Bool.false_or, Bool.false_eq_true, if_false]
      rw [denote'_letBind bi fuel (r₁ fuel (by omega)) (hp σ hG hC)]
      exact r₂ fuel (by omega)

/-- **Conditional with guarded exits in the branches.** -/
theorem corresG_ifThenElse {Γ N₀ Nt Tt Ne Te : S → BList} {G : S → Prop} {c t e : ImpExpr}
    {B Ct Ce : S → Bool} {Wt Vt We Ve : S → Value}
    (hc : CorresB bi Γ G c (fun σ => .bool (B σ)) N₀)
    (ht : CorresG bi N₀ (fun σ => G σ ∧ B σ = true) t Ct Wt Vt Tt Nt)
    (he : CorresG bi N₀ (fun σ => G σ ∧ B σ = false) e Ce We Ve Te Ne) :
    CorresG bi Γ G (.ifThenElse c t e) (fun σ => if B σ = true then Ct σ else Ce σ)
      (fun σ => if B σ = true then Wt σ else We σ) (fun σ => if B σ = true then Vt σ else Ve σ)
      (fun σ => if B σ = true then Tt σ else Te σ)
      (fun σ => if B σ = true then Nt σ else Ne σ) := by
  refine corres_ifThenElse hc ?_ ?_
  · refine corres_conseq ht (fun _ _ h _ => h) (fun _ h => h) (fun σ hG => ?_)
      (fun env σ hG h => ?_)
    · simp only [hG.2, if_true]
    · simp only [hG.2, if_true]; exact h
  · refine corres_conseq he (fun _ _ h _ => h) (fun _ h => h) (fun σ hG => ?_)
      (fun env σ hG h => ?_)
    · simp only [hG.2, Bool.false_eq_true, if_false]
    · simp only [hG.2, Bool.false_eq_true, if_false]; exact h

/-- **`return` and `break`.** The value of the expression is the exit value. -/
theorem corresG_cfBreak {Γ N : S → BList} {G : S → Prop} {e : ImpExpr} {V : S → Value}
    (h : CorresB bi Γ G e V N) (hp : ∀ σ, G σ → (V σ).isControlFlow = false) :
    CorresG bi Γ G (.cfBreak e) (fun _ => true) V (fun _ => .unit) N N :=
  corresB_cfBreak h hp

/-- A case split of the guard. -/
theorem corres_guard_cases {P Q : Env → S → Prop} {G : S → Prop} (D : S → Prop) {e : ImpExpr}
    {V : S → Value} (h₁ : Corres bi P (fun σ => G σ ∧ D σ) e V Q)
    (h₂ : Corres bi P (fun σ => G σ ∧ ¬ D σ) e V Q) : Corres bi P G e V Q := by
  intro env σ hP hG
  by_cases hD : D σ
  · exact h₁ env σ hP ⟨hG, hD⟩
  · exact h₂ env σ hP ⟨hG, hD⟩

/-- The lookup in a conditional binding list is the conditional of the two lookups. -/
theorem bindLookup_ite_of {c : Bool} {Γt Γe : BList} {x : String} {v₁ v₂ v : Value}
    (h₁ : bindLookup Γt x = some v₁) (h₂ : bindLookup Γe x = some v₂)
    (h : (if c = true then v₁ else v₂) = v) :
    bindLookup (if c = true then Γt else Γe) x = some v := by
  cases c
  · simp only [Bool.false_eq_true, if_false] at h ⊢; rw [h₂, h]
  · simp only [if_true] at h ⊢; rw [h₁, h]

theorem ite_enc {α : Type} [HaxEnc α] (c : Bool) (a b : α) :
    (if c = true then enc a else enc b) = enc (if c = true then a else b) := by
  cases c <;> rfl

/-! ### Functions -/

/-- **A function without exit.** -/
theorem fnCorres_of_corresB {A β : Type} [HaxEnc β] {Γ₀ N : A → BList} {G : A → Prop}
    {e : ImpExpr} {V : A → Value} {entry : A → Env} {f : A → β}
    (h : CorresB bi Γ₀ G e V N) (hentry : ∀ a, G a → Binds (entry a) (Γ₀ a))
    (hV : ∀ a, G a → V a = enc (f a)) : FnCorres bi e entry G f := by
  intro a hG
  obtain ⟨f₀, e₀, _, r⟩ := h (entry a) a (hentry a hG) hG
  exact ⟨f₀, fun fuel hf => by rw [r fuel hf, hV a hG]⟩

/-- **A function with early return.** -/
theorem fnCorresX_of_corresG {A β : Type} [HaxEnc β] [HaxEnc.Plain β] {Γ₀ N T : A → BList}
    {G : A → Prop} {e : ImpExpr} {C : A → Bool} {W V : A → Value} {entry : A → Env}
    {w v : A → β} (h : CorresG bi Γ₀ G e C W V T N)
    (hentry : ∀ a, G a → Binds (entry a) (Γ₀ a))
    (hW : ∀ a, G a → C a = true → W a = enc (w a))
    (hV : ∀ a, G a → C a = false → V a = enc (v a)) :
    FnCorresX bi e entry G (fun a => if C a = true then .error (w a) else .ok (v a)) := by
  intro a hG
  obtain ⟨f₀, e₀, _, r⟩ := h (entry a) a (hentry a hG) hG
  refine ⟨f₀, fun fuel hf => ?_⟩
  rw [r fuel hf]
  cases hC : C a
  · simp only [hC, Bool.false_eq_true, if_false, hV a hG hC, outcomeExceptCF, encExc]
    congr 1
    have := HaxEnc.Plain.not_cf (v a)
    generalize enc (v a) = x at this ⊢
    cases x with
    | controlFlow b y => cases b <;> simp_all [Value.isControlFlow]
    | _ => rfl
  · simp only [hC, if_true, hW a hG hC, outcomeExceptCF, encExc, cfExcept_break]

theorem mergeExcept_ite {β : Type} (c : Bool) (w v : β) :
    mergeExcept (if c = true then (.error w : Except β β) else .ok v) =
      if c = true then w else v := by
  cases c <;> rfl

end CorresG

/-! ## Loops over binding lists -/

section GenLoops

variable {S A B : Type} {bi : Builtins}

/-- The accumulator after a loop that may break: the state carried by the break, or the
    final accumulator. -/
def cfState : ControlFlow (B × A) A → A
  | .Break p => p.2
  | .Continue a => a

/-- The value of a loop that may break: the encoded break value, or `.unit`. -/
def cfVal [HaxEnc B] : ControlFlow (B × A) A → Value
  | .Break p => enc p.1
  | .Continue _ => .unit

/-- One step of a loop that may break: break with `(b, ab)` when `c` holds, continue
    with `a` otherwise. -/
def stepCF (c : Bool) (b : B) (ab a : A) : ControlFlow (B × A) A :=
  if c = true then .Break (b, ab) else .Continue a

theorem cfToExcept_forFold (lo hi : Int) (a : A) (g : Int → A → ControlFlow B A) :
    cfToExcept (Hax.forFold lo hi a g) = foldRangeE lo hi a (fun i a => cfToExcept (g i a)) := by
  unfold Hax.forFold foldRangeE
  suffices H : ∀ n i a, cfToExcept (Hax.forFold.go g n i a) =
      foldFromE (fun i a => cfToExcept (g i a)) n i a from H _ _ _
  intro n
  induction n with
  | zero => intro i a; rfl
  | succ n ih =>
    intro i a
    simp only [Hax.forFold.go, foldFromE]
    cases g i a with
    | Break b => rfl
    | Continue a' => exact ih (i + 1) a'

theorem foldRange_of_lt {lo hi : Int} (h : hi < lo) (a : A) (g : Int → A → A) :
    Hax.foldRange lo hi a g = a := by
  rw [foldRange_eq_foldRangeSpec]
  simp only [foldRangeSpec, show (hi - lo).toNat = 0 by omega, foldFrom]

theorem forFold_of_lt {lo hi : Int} (h : hi < lo) (a : A) (g : Int → A → ControlFlow B A) :
    Hax.forFold lo hi a g = .Continue a := by
  unfold Hax.forFold
  rw [show (hi - lo).toNat = 0 by omega]
  rfl

theorem loopVal_cfToExcept [HaxEnc B] (σ : S) (r : ControlFlow (B × A) A) :
    loopVal (fun _ p => enc p.1) σ (cfToExcept r) = cfVal r := by
  cases r <;> rfl

/-- The loop body of a counted loop over binding lists with a guarded exit, in the form
    of `LoopBody`. -/
theorem loopBody_of_corresG {var : String} {body : ImpExpr} {G : S → Prop} {loF hiF : S → Int}
    [HaxEnc B] {Λ : S → A → BList} {Cb : S × Int × A → Bool} {Wb Vb : S × Int × A → Value}
    {Tb Nb : S × Int × A → BList} {w : S → Int → A → B} {g gb : S → Int → A → A}
    (hbody : CorresG bi (fun t : S × Int × A => (var, .int t.2.1) :: Λ t.1 t.2.2)
      (fun t => G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1) body Cb Wb Vb Tb Nb)
    (hT : ∀ t : S × Int × A, G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1 → Cb t = true →
      BindsSub (Tb t) (Λ t.1 (gb t.1 t.2.1 t.2.2)))
    (hN : ∀ t : S × Int × A, G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1 → Cb t = false →
      BindsSub (Nb t) (Λ t.1 (g t.1 t.2.1 t.2.2))) :
    LoopBody bi var body G loF hiF
      (fun σ i a => cfToExcept (stepCF (Cb (σ, i, a)) (w σ i a) (gb σ i a) (g σ i a)))
      (fun env σ _ a => Binds env (Λ σ a)) (fun env σ p => Binds env (Λ σ p.2))
      (fun t => if Cb t = true then .controlFlow true (Wb t) else Vb t) := by
  refine corres_conseq hbody (fun env t h _ => binds_cons_of h.2 h.1) (fun _ h => h)
    (fun _ _ => rfl) (fun env t hG hb => ?_)
  obtain ⟨σ, i, a⟩ := t
  cases hC : Cb (σ, i, a)
  · simp only [hC, Bool.false_eq_true, if_false, stepCF, cfToExcept] at hb ⊢
    exact binds_of_sub hb (hN _ hG hC)
  · simp only [hC, if_true, stepCF, cfToExcept] at hb ⊢
    exact binds_of_sub hb (hT _ hG hC)

/-- **Counted loop with a plain body.** The invariant binds `Λ σ a`, independent of the
    index; the loop corresponds to `Hax.foldRange`, for all bounds. -/
theorem corresB_forFoldP {Γ N₁ N₂ : S → BList} {G : S → Prop} {var : String}
    {lo hi body : ImpExpr} {loF hiF : S → Int} {a₀ : S → A} {g : S → Int → A → A}
    {Λ : S → A → BList} {Vb : S × Int × A → Value} {Nb : S × Int × A → BList}
    (hlo : CorresB bi Γ G lo (fun σ => .int (loF σ)) N₁)
    (hhi : CorresB bi N₁ G hi (fun σ => .int (hiF σ)) N₂)
    (hinit : ∀ σ, G σ → BindsSub (N₂ σ) (Λ σ (a₀ σ)))
    (hfresh : ∀ σ a, bindLookup (Λ σ a) var = none)
    (hbody : CorresB bi (fun t : S × Int × A => (var, .int t.2.1) :: Λ t.1 t.2.2)
      (fun t => G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1) body Vb Nb)
    (hV : ∀ t : S × Int × A, G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1 →
      (Vb t).isControlFlow = false)
    (hstep : ∀ t : S × Int × A, G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1 →
      BindsSub (Nb t) (Λ t.1 (g t.1 t.2.1 t.2.2))) :
    CorresB bi Γ G (.forFold var lo hi body) (fun _ => .unit)
      (fun σ => Λ σ (Hax.foldRange (loF σ) (hiF σ) (a₀ σ) (g σ))) := by
  refine corres_guard_cases (fun σ => loF σ ≤ hiF σ) ?_ ?_
  · have h := corresB_forFold (bi := bi) (G := fun σ => G σ ∧ loF σ ≤ hiF σ)
      (Λ := fun σ _ a => Λ σ a) (g := g) (a₀ := a₀) (Vb := Vb) (Γb := Nb) (var := var)
      (body := body)
      (corres_conseq hlo (fun _ _ h _ => h) (fun _ h => h.1) (fun _ _ => rfl)
        (fun _ _ _ h => h))
      (corres_conseq hhi (fun _ _ h _ => h) (fun _ h => h.1) (fun _ _ => rfl)
        (fun _ _ _ h => h))
      (fun σ hG => hinit σ hG.1) (fun σ hG => hG.2) (fun t => hfresh t.1 t.2.2)
      (corres_conseq hbody (fun _ _ h _ => h) (fun _ hG => ⟨hG.1.1, hG.2⟩) (fun _ _ => rfl)
        (fun _ _ _ h => h))
      (fun t hG => hV t ⟨hG.1.1, hG.2⟩) (fun t hG => hstep t ⟨hG.1.1, hG.2⟩)
    refine corres_conseq h (fun _ _ h _ => h) (fun _ h => h) (fun _ _ => rfl)
      (fun env σ _ hb => ?_)
    dsimp only at hb ⊢
    rw [foldRange_eq_foldRangeSpec]
    exact hb
  · intro env σ hP hG
    obtain ⟨f₁, e₁, hQ₁, r₁⟩ := hlo env σ hP hG.1
    obtain ⟨f₂, e₂, hQ₂, r₂⟩ := hhi e₁ σ hQ₁ hG.1
    have hlt : hiF σ < loF σ := by have := hG.2; omega
    refine ⟨max f₁ f₂, e₂, ?_, fun fuel hf => ?_⟩
    · show Binds e₂ (Λ σ (Hax.foldRange (loF σ) (hiF σ) (a₀ σ) (g σ)))
      rw [foldRange_of_lt hlt]
      exact binds_of_sub hQ₂ (hinit σ hG.1)
    · rw [denote'_forFold bi fuel (r₁ fuel (by omega)) (r₂ fuel (by omega))]
      exact denoteForLoop'_done bi fuel var body e₂ (by omega)

/-- **Counted loop whose body may break.** A break of the body carries the break value
    `w` and the accumulator `gb`; the loop corresponds to `Hax.forFold`, for all
    bounds. -/
theorem corresB_forFoldG [HaxEnc B] {Γ N₁ N₂ : S → BList} {G : S → Prop} {var : String}
    {lo hi body : ImpExpr} {loF hiF : S → Int} {a₀ : S → A} {g gb : S → Int → A → A}
    {w : S → Int → A → B} {Λ : S → A → BList} {Cb : S × Int × A → Bool}
    {Wb Vb : S × Int × A → Value} {Tb Nb : S × Int × A → BList}
    (hlo : CorresB bi Γ G lo (fun σ => .int (loF σ)) N₁)
    (hhi : CorresB bi N₁ G hi (fun σ => .int (hiF σ)) N₂)
    (hinit : ∀ σ, G σ → BindsSub (N₂ σ) (Λ σ (a₀ σ)))
    (hfresh : ∀ σ a, bindLookup (Λ σ a) var = none)
    (hbody : CorresG bi (fun t : S × Int × A => (var, .int t.2.1) :: Λ t.1 t.2.2)
      (fun t => G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1) body Cb Wb Vb Tb Nb)
    (hW : ∀ t : S × Int × A, G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1 → Cb t = true →
      Wb t = enc (w t.1 t.2.1 t.2.2))
    (hV : ∀ t : S × Int × A, G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1 → Cb t = false →
      (Vb t).isControlFlow = false)
    (hT : ∀ t : S × Int × A, G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1 → Cb t = true →
      BindsSub (Tb t) (Λ t.1 (gb t.1 t.2.1 t.2.2)))
    (hN : ∀ t : S × Int × A, G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1 → Cb t = false →
      BindsSub (Nb t) (Λ t.1 (g t.1 t.2.1 t.2.2))) :
    CorresB bi Γ G (.forFold var lo hi body)
      (fun σ => cfVal (Hax.forFold (loF σ) (hiF σ) (a₀ σ)
        (fun i a => stepCF (Cb (σ, i, a)) (w σ i a) (gb σ i a) (g σ i a))))
      (fun σ => Λ σ (cfState (Hax.forFold (loF σ) (hiF σ) (a₀ σ)
        (fun i a => stepCF (Cb (σ, i, a)) (w σ i a) (gb σ i a) (g σ i a))))) := by
  refine corres_guard_cases (fun σ => loF σ ≤ hiF σ) ?_ ?_
  · have hb := loopBody_of_corresG (w := w) (g := g) (gb := gb) hbody hT hN
    have hb' : LoopBody bi var body (fun σ => G σ ∧ loF σ ≤ hiF σ) loF hiF
        (fun σ i a => cfToExcept (stepCF (Cb (σ, i, a)) (w σ i a) (gb σ i a) (g σ i a)))
        (fun env σ _ a => Binds env (Λ σ a)) (fun env σ p => Binds env (Λ σ p.2))
        (fun t => if Cb t = true then .controlFlow true (Wb t) else Vb t) := by
      unfold LoopBody at hb ⊢
      exact corres_conseq hb (fun _ _ h _ => h) (fun _ hG => ⟨hG.1.1, hG.2⟩) (fun _ _ => rfl)
        (fun _ _ _ h => h)
    have h := corres_forFoldE (bi := bi) (G := fun σ => G σ ∧ loF σ ≤ hiF σ)
      (W := fun _ (p : B × A) => enc p.1) (a₀ := a₀)
      (corres_conseq hlo (fun _ _ h _ => h) (fun _ h => h.1) (fun _ _ => rfl)
        (fun _ _ _ h => h))
      (corres_conseq hhi (fun _ _ h _ => h) (fun _ h => h.1) (fun _ _ => rfl)
        (fun _ _ _ h => h))
      (fun env σ hb hG => binds_of_sub hb (hinit σ hG.1)) (fun σ hG => hG.2)
      hb'
      (fun t hG hl hh => ?_)
      (fun env σ i a h => binds_extend_fresh h (hfresh σ a) _)
    · refine corres_conseq h (fun _ _ h _ => h) (fun _ h => h) (fun σ _ => ?_)
        (fun env σ _ hq => ?_)
      · simp only [← cfToExcept_forFold, loopVal_cfToExcept]
      · dsimp only at hq ⊢
        simp only [← cfToExcept_forFold] at hq
        generalize Hax.forFold _ _ _ _ = r at hq ⊢
        cases r <;> exact hq
    · obtain ⟨σ, i, a⟩ := t
      have hG' : G σ ∧ loF σ ≤ i ∧ i < hiF σ := ⟨hG.1, hl, hh⟩
      cases hC : Cb (σ, i, a)
      · simp only [stepCF, Bool.false_eq_true, if_false, cfToExcept]
        intro x hx
        have := hV _ hG' hC
        rw [hx] at this
        cases this
      · simp only [stepCF, if_true, cfToExcept]
        rw [hW _ hG' hC]
  · intro env σ hP hG
    obtain ⟨f₁, e₁, hQ₁, r₁⟩ := hlo env σ hP hG.1
    obtain ⟨f₂, e₂, hQ₂, r₂⟩ := hhi e₁ σ hQ₁ hG.1
    have hlt : hiF σ < loF σ := by have := hG.2; omega
    refine ⟨max f₁ f₂, e₂, ?_, fun fuel hf => ?_⟩
    · show Binds e₂ (Λ σ (cfState (Hax.forFold _ _ _ _)))
      rw [forFold_of_lt hlt]
      exact binds_of_sub hQ₂ (hinit σ hG.1)
    · dsimp only
      rw [denote'_forFold bi fuel (r₁ fuel (by omega)) (r₂ fuel (by omega)), forFold_of_lt hlt]
      exact denoteForLoop'_done bi fuel var body e₂ (by omega)

/-- **While loop whose body may break.** The condition keeps the invariant bindings; the
    loop corresponds to `Hax.whileFold` on every state from which it stops. -/
theorem corresB_whileFoldG [HaxEnc B] {Γ : S → BList} {G : S → Prop} {cond body : ImpExpr}
    {a₀ : S → A} {c : S → A → Bool} {g gb : S → A → A} {w : S → A → B}
    {Λ : S → A → BList} {Nc : S × A → BList} {Cb : S × A → Bool}
    {Wb Vb : S × A → Value} {Tb Nb : S × A → BList}
    (hinit : ∀ σ, G σ → BindsSub (Γ σ) (Λ σ (a₀ σ)))
    (hcond : CorresB bi (fun t : S × A => Λ t.1 t.2) (fun t => G t.1) cond
      (fun t => .bool (c t.1 t.2)) Nc)
    (hcondN : ∀ t : S × A, G t.1 → BindsSub (Nc t) (Λ t.1 t.2))
    (hbody : CorresG bi Nc (fun t => G t.1 ∧ c t.1 t.2 = true) body Cb Wb Vb Tb Nb)
    (hW : ∀ t : S × A, G t.1 ∧ c t.1 t.2 = true → Cb t = true → Wb t = enc (w t.1 t.2))
    (hV : ∀ t : S × A, G t.1 ∧ c t.1 t.2 = true → Cb t = false →
      (Vb t).isControlFlow = false)
    (hT : ∀ t : S × A, G t.1 ∧ c t.1 t.2 = true → Cb t = true →
      BindsSub (Tb t) (Λ t.1 (gb t.1 t.2)))
    (hN : ∀ t : S × A, G t.1 ∧ c t.1 t.2 = true → Cb t = false →
      BindsSub (Nb t) (Λ t.1 (g t.1 t.2)))
    (hterm : ∀ σ, G σ → Hax.WhileFoldStops (a₀ σ) (c σ)
      (fun a => stepCF (Cb (σ, a)) (w σ a) (gb σ a) (g σ a))) :
    CorresB bi Γ G (.whileFold cond body)
      (fun σ => cfVal (Hax.whileFold (a₀ σ) (c σ)
        (fun a => stepCF (Cb (σ, a)) (w σ a) (gb σ a) (g σ a))))
      (fun σ => Λ σ (cfState (Hax.whileFold (a₀ σ) (c σ)
        (fun a => stepCF (Cb (σ, a)) (w σ a) (gb σ a) (g σ a))))) := by
  have hb : WhileBody bi body G c
      (fun σ a => cfToExcept (stepCF (Cb (σ, a)) (w σ a) (gb σ a) (g σ a)))
      (fun env σ a => Binds env (Nc (σ, a))) (fun env σ a => Binds env (Λ σ a))
      (fun env σ p => Binds env (Λ σ p.2))
      (fun t => if Cb t = true then .controlFlow true (Wb t) else Vb t) := by
    refine corres_conseq hbody (fun _ _ h _ => h) (fun _ h => h) (fun _ _ => rfl)
      (fun env t hG hq => ?_)
    obtain ⟨σ, a⟩ := t
    cases hC : Cb (σ, a)
    · simp only [hC, Bool.false_eq_true, if_false, stepCF, cfToExcept] at hq ⊢
      exact binds_of_sub hq (hN _ hG hC)
    · simp only [hC, if_true, stepCF, cfToExcept] at hq ⊢
      exact binds_of_sub hq (hT _ hG hC)
  have hc' : WhileCond bi cond G c (fun env σ a => Binds env (Λ σ a))
      (fun env σ a => Binds env (Nc (σ, a))) := hcond
  have h := corres_whileFold_runtime (bi := bi) (P := fun env σ => Binds env (Γ σ))
    (W := fun _ (p : B × A) => enc p.1) (a₀ := a₀)
    (g := fun σ a => stepCF (Cb (σ, a)) (w σ a) (gb σ a) (g σ a))
    (fun env σ hb hG => binds_of_sub hb (hinit σ hG)) hc' hb (fun t hG hc => ?_) hterm
  · refine corres_conseq h (fun _ _ h _ => h) (fun _ h => h) (fun σ _ => ?_)
      (fun env σ hG hq => ?_)
    · exact loopVal_cfToExcept σ _
    · dsimp only at hq ⊢
      generalize Hax.whileFold _ _ _ = r at hq ⊢
      cases r with
      | Break p => exact hq
      | Continue a => exact binds_of_sub hq (hcondN (σ, a) hG)
  · obtain ⟨σ, a⟩ := t
    have hG' : G σ ∧ c σ a = true := ⟨hG, hc⟩
    cases hC : Cb (σ, a)
    · have := hV _ hG' hC
      simp only [stepCF, Bool.false_eq_true, if_false, cfToExcept, stepStop]
      generalize Vb (σ, a) = x at this ⊢
      cases x with
      | controlFlow b y => simp [Value.isControlFlow] at this
      | _ => rfl
    · simp only [stepCF, if_true, cfToExcept, stopPlain, stepStop]
      rw [hW _ hG' hC]

/-- **`Hax.foldRangeRev` is the reverse fold of the loop rule.** -/
theorem foldRangeRev_eq_foldRangeRevSpec (lo hi : Int) (a : A) (f : Int → A → A) :
    Hax.foldRangeRev lo hi a f = foldRangeRevSpec lo hi a f := by
  unfold Hax.foldRangeRev foldRangeRevSpec
  suffices H : ∀ n i a, Hax.foldRangeRev.go f n i a = foldFromRev f n i a from H _ _ _
  intro n
  induction n with
  | zero => intro i a; rfl
  | succ n ih => intro i a; exact ih (i - 1) (f i a)

theorem foldRangeRev_of_lt {lo hi : Int} (h : hi < lo) (a : A) (g : Int → A → A) :
    Hax.foldRangeRev lo hi a g = a := by
  rw [foldRangeRev_eq_foldRangeRevSpec]
  simp only [foldRangeRevSpec, show (hi - lo).toNat = 0 by omega, foldFromRev]

/-- **Reverse counted loop with a plain body.** The invariant binds `Λ σ a`, independent
    of the index; the loop corresponds to `Hax.foldRangeRev`, for all bounds. -/
theorem corresB_forFoldRevP {Γ N₁ N₂ : S → BList} {G : S → Prop} {var : String}
    {lo hi body : ImpExpr} {loF hiF : S → Int} {a₀ : S → A} {g : S → Int → A → A}
    {Λ : S → A → BList} {Vb : S × Int × A → Value} {Nb : S × Int × A → BList}
    (hlo : CorresB bi Γ G lo (fun σ => .int (loF σ)) N₁)
    (hhi : CorresB bi N₁ G hi (fun σ => .int (hiF σ)) N₂)
    (hinit : ∀ σ, G σ → BindsSub (N₂ σ) (Λ σ (a₀ σ)))
    (hfresh : ∀ σ a, bindLookup (Λ σ a) var = none)
    (hbody : CorresB bi (fun t : S × Int × A => (var, .int t.2.1) :: Λ t.1 t.2.2)
      (fun t => G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1) body Vb Nb)
    (hV : ∀ t : S × Int × A, G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1 →
      (Vb t).isControlFlow = false)
    (hstep : ∀ t : S × Int × A, G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1 →
      BindsSub (Nb t) (Λ t.1 (g t.1 t.2.1 t.2.2))) :
    CorresB bi Γ G (.forFoldRev var lo hi body) (fun _ => .unit)
      (fun σ => Λ σ (Hax.foldRangeRev (loF σ) (hiF σ) (a₀ σ) (g σ))) := by
  refine corres_guard_cases (fun σ => loF σ ≤ hiF σ) ?_ ?_
  · have h := corres_forFoldRev (bi := bi) (G := fun σ => G σ ∧ loF σ ≤ hiF σ)
      (Inv := fun env σ _ a => Binds env (Λ σ a)) (g := g) (a₀ := a₀) (Vb := Vb)
      (var := var) (body := body)
      (corres_conseq hlo (fun _ _ h _ => h) (fun _ h => h.1) (fun _ _ => rfl)
        (fun _ _ _ h => h))
      (corres_conseq hhi (fun _ _ h _ => h) (fun _ h => h.1) (fun _ _ => rfl)
        (fun _ _ _ h => h))
      (fun env σ hb hG => binds_of_sub hb (hinit σ hG.1)) (fun σ hG => hG.2)
      (corres_conseq hbody (fun env t h _ => binds_cons_of h.2 h.1)
        (fun _ hG => ⟨hG.1.1, hG.2⟩) (fun _ _ => rfl)
        (fun env t hG hb => binds_of_sub hb (hstep t ⟨hG.1.1, hG.2⟩)))
      (fun t hG hl hh => ?_)
      (fun env σ j a h => binds_extend_fresh h (hfresh σ a) _)
    · refine corres_conseq h (fun _ _ h _ => h) (fun _ h => h) (fun _ _ => rfl)
        (fun env σ _ hb => ?_)
      dsimp only at hb ⊢
      rw [foldRangeRev_eq_foldRangeRevSpec]
      exact hb
    · have := hV t ⟨hG.1, hl, hh⟩
      generalize Vb t = x at this ⊢
      cases x with
      | controlFlow b y => simp [Value.isControlFlow] at this
      | _ => rfl
  · intro env σ hP hG
    obtain ⟨f₁, e₁, hQ₁, r₁⟩ := hlo env σ hP hG.1
    obtain ⟨f₂, e₂, hQ₂, r₂⟩ := hhi e₁ σ hQ₁ hG.1
    have hlt : hiF σ < loF σ := by have := hG.2; omega
    refine ⟨max f₁ f₂, e₂, ?_, fun fuel hf => ?_⟩
    · show Binds e₂ (Λ σ (Hax.foldRangeRev (loF σ) (hiF σ) (a₀ σ) (g σ)))
      rw [foldRangeRev_of_lt hlt]
      exact binds_of_sub hQ₂ (hinit σ hG.1)
    · rw [denote'_forFoldRev bi fuel (r₁ fuel (by omega)) (r₂ fuel (by omega))]
      exact denoteForLoopRev'_done bi fuel var body e₂ (by omega)

theorem cfVal_isControlFlow [HaxEnc B] [HaxEnc.Plain B] (r : ControlFlow (B × A) A) :
    (cfVal r).isControlFlow = false := by
  cases r with
  | Break p => exact HaxEnc.Plain.not_cf p.1
  | Continue a => rfl

theorem whileFoldStops_of_rec {c : A → Bool} {f : A → ControlFlow B A} {n : Nat} {a : A}
    {r : Except B A} (h : WhileRecIn c (fun a => cfToExcept (f a)) n a r) :
    Hax.WhileFoldStops a c f :=
  ⟨n + 1, by rw [whileFoldFuel_of_rec h (n + 1) (by omega)]; rfl⟩

/-- **Termination of a while-fold from a measure** that decreases on every continuing
    trip. -/
theorem whileFoldStops_of_measure {c : A → Bool} {f : A → ControlFlow B A} (μ : A → Nat)
    (hdec : ∀ a a', c a = true → f a = .Continue a' → μ a' < μ a) (a : A) :
    Hax.WhileFoldStops a c f := by
  obtain ⟨n, r, h⟩ := whileTerminates_of_measure (c := c) (f := fun a => cfToExcept (f a)) μ
    (fun a a' hc hf => hdec a a' hc (by
      have := congrArg exceptToCF hf
      rw [exceptToCF_cfToExcept] at this
      exact this)) a
  exact whileFoldStops_of_rec h

end GenLoops

/-! ## Counted loops with early return -/

section GenReturnLoops

variable {S A R : Type} {bi : Builtins}

/-- One step of a counted loop with early return and no loop break: return `r` when `c`
    holds, continue with `a` otherwise. -/
def stepRet (c : Bool) (r : R) (a : A) : ControlFlow (ControlFlow R Unit) A :=
  if c = true then .Break (.Break r) else .Continue a

/-- Whether a loop with early return returned. -/
def retC : ControlFlow R (ControlFlow Unit A) → Bool
  | .Break _ => true
  | .Continue _ => false

/-- The returned value of a loop with early return, `d` when it did not return. -/
def retOut (d : R) : ControlFlow R (ControlFlow Unit A) → R
  | .Break r => r
  | .Continue _ => d

/-- The final accumulator of a loop with early return that ran to the end, `d`
    otherwise. -/
def retAcc (d : A) : ControlFlow R (ControlFlow Unit A) → A
  | .Continue (.Continue a) => a
  | _ => d

/-- The break relation of a loop without loop break: a return holds, a loop break
    does not. -/
def retBrk : Except R Unit → Prop
  | .ok _ => False
  | .error _ => True

/-- **Counted loop with early return.** A body exit is a return from the function with
    the value `w`; the loop corresponds to `Hax.forFoldReturn` with `stepRet`, for all
    bounds. Its exit condition is `retC`, its exit value the returned value and its
    exit bindings empty. -/
theorem corresG_forFoldReturnG [HaxEnc R] [HaxEnc.Plain R] {Γ N₁ N₂ : S → BList}
    {G : S → Prop} {var : String} {lo hi body : ImpExpr} {loF hiF : S → Int} {a₀ : S → A}
    {g : S → Int → A → A} {w : S → Int → A → R} {Λ : S → A → BList}
    {Cb : S × Int × A → Bool} {Wb Vb : S × Int × A → Value} {Tb Nb : S × Int × A → BList}
    (hlo : CorresB bi Γ G lo (fun σ => .int (loF σ)) N₁)
    (hhi : CorresB bi N₁ G hi (fun σ => .int (hiF σ)) N₂)
    (hinit : ∀ σ, G σ → BindsSub (N₂ σ) (Λ σ (a₀ σ)))
    (hfresh : ∀ σ a, bindLookup (Λ σ a) var = none)
    (hbody : CorresG bi (fun t : S × Int × A => (var, .int t.2.1) :: Λ t.1 t.2.2)
      (fun t => G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1) body Cb Wb Vb Tb Nb)
    (hW : ∀ t : S × Int × A, G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1 → Cb t = true →
      Wb t = enc (w t.1 t.2.1 t.2.2))
    (hV : ∀ t : S × Int × A, G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1 → Cb t = false →
      (Vb t).isControlFlow = false)
    (hN : ∀ t : S × Int × A, G t.1 ∧ loF t.1 ≤ t.2.1 ∧ t.2.1 < hiF t.1 → Cb t = false →
      BindsSub (Nb t) (Λ t.1 (g t.1 t.2.1 t.2.2))) :
    CorresG bi Γ G (.forFoldReturn var lo hi body)
      (fun σ => retC (Hax.forFoldReturn (loF σ) (hiF σ) (a₀ σ)
        (fun i a => stepRet (Cb (σ, i, a)) (w σ i a) (g σ i a))))
      (fun σ => enc (retOut (w σ (loF σ) (a₀ σ)) (Hax.forFoldReturn (loF σ) (hiF σ) (a₀ σ)
        (fun i a => stepRet (Cb (σ, i, a)) (w σ i a) (g σ i a)))))
      (fun _ => .unit) (fun _ => [])
      (fun σ => Λ σ (retAcc (a₀ σ) (Hax.forFoldReturn (loF σ) (hiF σ) (a₀ σ)
        (fun i a => stepRet (Cb (σ, i, a)) (w σ i a) (g σ i a))))) := by
  refine corres_guard_cases (fun σ => loF σ ≤ hiF σ) ?_ ?_
  · have hb : LoopBody bi var body (fun σ => G σ ∧ loF σ ≤ hiF σ) loF hiF
        (fun σ i a => stepToExcept (stepRet (Cb (σ, i, a)) (w σ i a) (g σ i a)))
        (fun env σ _ a => Binds env (Λ σ a)) (fun _ _ b => retBrk b)
        (fun t => if Cb t = true then .controlFlow true (Wb t) else Vb t) := by
      refine corres_conseq hbody (fun env t h _ => binds_cons_of h.2 h.1)
        (fun _ hG => ⟨hG.1.1, hG.2⟩) (fun _ _ => rfl) (fun env t hG hq => ?_)
      obtain ⟨σ, i, a⟩ := t
      cases hC : Cb (σ, i, a)
      · simp only [hC, Bool.false_eq_true, if_false, stepRet, stepToExcept] at hq ⊢
        exact binds_of_sub hq (hN _ ⟨hG.1.1, hG.2⟩ hC)
      · simp only [hC, if_true, stepRet, stepToExcept, retBrk]
    have h := corres_forFoldReturn (bi := bi) (P := fun env σ => Binds env (Γ σ))
      (G := fun σ => G σ ∧ loF σ ≤ hiF σ) (L := Unit) (X := fun _ r => enc r)
      (Wl := fun _ _ => .unit) (a₀ := a₀)
      (corres_conseq hlo (fun _ _ h _ => h) (fun _ h => h.1) (fun _ _ => rfl)
        (fun _ _ _ h => h))
      (corres_conseq hhi (fun _ _ h _ => h) (fun _ h => h.1) (fun _ _ => rfl)
        (fun _ _ _ h => h))
      (fun env σ hb hG => binds_of_sub hb (hinit σ hG.1)) (fun σ hG => hG.2) hb
      (fun t hG hl hh => ?_) (fun env σ i a h => binds_extend_fresh h (hfresh σ a) _)
    · refine corres_conseq h (fun _ _ h _ => h) (fun _ h => h) (fun σ _ => ?_)
        (fun env σ _ hq => ?_)
      · have key : ∀ (d : R) (r : ControlFlow R (ControlFlow Unit A)),
            excVal (retResult (fun _ (x : R) => enc x) (fun _ (_ : Unit) => Value.unit) σ
              (retToExcept r)) =
            if retC r = true then .controlFlow true (enc (retOut d r)) else .unit := by
          intro d r
          rcases r with x | (l | a) <;> rfl
        dsimp only
        rw [← retToExcept_forFoldReturn]
        exact key _ _
      · have key : ∀ (r : ControlFlow R (ControlFlow Unit A)),
            loopExit (fun env σ _ a => Binds env (Λ σ a)) (fun _ _ b => retBrk b) σ (hiF σ)
              (retToExcept r) env →
            Binds env (if retC r = true then [] else Λ σ (retAcc (a₀ σ) r)) := by
          intro r hq
          rcases r with x | (l | a)
          · intro y v hy; simp [retC] at hy
          · exact hq.elim
          · exact hq
        dsimp only at hq ⊢
        rw [← retToExcept_forFoldReturn] at hq
        exact key _ hq
    · obtain ⟨σ, i, a⟩ := t
      have hG' : G σ ∧ loF σ ≤ i ∧ i < hiF σ := ⟨hG.1, hl, hh⟩
      cases hC : Cb (σ, i, a)
      · have := hV _ hG' hC
        simp only [Bool.false_eq_true, if_false, stepRet, stepToExcept, stepStop]
        generalize Vb (σ, i, a) = x at this ⊢
        cases x with
        | controlFlow b y => simp [Value.isControlFlow] at this
        | _ => rfl
      · have := HaxEnc.Plain.not_cf (w σ i a)
        simp only [if_true, stepRet, stepToExcept, stepStop, retStop, hW _ hG' hC]
        generalize enc (w σ i a) = x at this ⊢
        cases x with
        | controlFlow b y => simp [Value.isControlFlow] at this
        | _ => rfl
  · intro env σ hP hG
    obtain ⟨f₁, e₁, hQ₁, r₁⟩ := hlo env σ hP hG.1
    obtain ⟨f₂, e₂, hQ₂, r₂⟩ := hhi e₁ σ hQ₁ hG.1
    have hlt : hiF σ < loF σ := by have := hG.2; omega
    have hr : Hax.forFoldReturn (loF σ) (hiF σ) (a₀ σ)
        (fun i a => stepRet (Cb (σ, i, a)) (w σ i a) (g σ i a)) =
          .Continue (.Continue (a₀ σ)) := by
      unfold Hax.forFoldReturn
      rw [show (hiF σ - loF σ).toNat = 0 by omega]
      rfl
    refine ⟨max f₁ f₂, e₂, ?_, fun fuel hf => ?_⟩
    · simp only [hr, retC, retAcc, Bool.false_eq_true, if_false]
      exact binds_of_sub hQ₂ (hinit σ hG.1)
    · simp only [hr, retC, Bool.false_eq_true, if_false]
      rw [denote'_forFoldReturn bi fuel (r₁ fuel (by omega)) (r₂ fuel (by omega))]
      exact denoteForLoop'Return_done bi fuel var body e₂ (by omega)

end GenReturnLoops

/-! ## `Option` match -/

section GenOptMatch

variable {S : Type} {bi : Builtins}

/-- **`Option` match with guarded exits in the arms.** The scrutinee variable holds
    `enc (O σ)`; the `Some` arm runs with its binder bound to the payload
    `(O σ).getD default`, the `None` arm from the entry bindings, and every component of
    the result is the conditional on `(O σ).isSome`. -/
theorem corresG_optMatch {α : Type} [HaxEnc α] [Inhabited α] {Γ Ts Ns Tn Nn : S → BList}
    {G : S → Prop} {o v : String} {e2 e1 : ImpExpr} {O : S → Option α} {Cs Cn : S → Bool}
    {Ws Vs Wn Vn : S → Value}
    (ho : ∀ σ, G σ → bindLookup (Γ σ) o = some (enc (O σ)))
    (hs : CorresG bi (fun σ => (v, enc ((O σ).getD default)) :: Γ σ)
      (fun σ => G σ ∧ (O σ).isSome = true) e2 Cs Ws Vs Ts Ns)
    (hn : CorresG bi Γ (fun σ => G σ ∧ (O σ).isSome = false) e1 Cn Wn Vn Tn Nn) :
    CorresG bi Γ G (.match_ (.var o) [(.somePat (.varPat v), e2), (.nonePat, e1)])
      (fun σ => if (O σ).isSome = true then Cs σ else Cn σ)
      (fun σ => if (O σ).isSome = true then Ws σ else Wn σ)
      (fun σ => if (O σ).isSome = true then Vs σ else Vn σ)
      (fun σ => if (O σ).isSome = true then Ts σ else Tn σ)
      (fun σ => if (O σ).isSome = true then Ns σ else Nn σ) := by
  refine corres_optMatch (O := fun σ => (O σ).map enc)
    (fun env σ hP hG => hP.lookup (ho σ hG)) ?_ ?_
  · rintro env σ ⟨env₀, x, hb, hx, rfl⟩ hG
    have hs' : (O σ).isSome = true := by simpa using hG.2
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs'
    have hxp : x = enc p := by
      rw [hp] at hx
      simp only [Option.map_some, Option.some.injEq] at hx
      exact hx.symm
    have hb' : Binds (env₀.extend v x) ((v, enc ((O σ).getD default)) :: Γ σ) := by
      rw [hxp, hp]
      exact binds_extend hb v _
    obtain ⟨f₀, e', hQ, r⟩ := hs _ σ hb' ⟨hG.1, hs'⟩
    refine ⟨f₀, e', ?_, fun fuel hf => ?_⟩
    · simp only [hs', if_true]; exact hQ
    · simp only [hs', if_true]; exact r fuel hf
  · intro env σ hb hG
    have hn' : (O σ).isSome = false := by
      have := hG.2
      cases h : O σ <;> simp_all
    obtain ⟨f₀, e', hQ, r⟩ := hn env σ hb ⟨hG.1, hn'⟩
    refine ⟨f₀, e', ?_, fun fuel hf => ?_⟩
    · simp only [hn', Bool.false_eq_true, if_false]; exact hQ
    · simp only [hn', Bool.false_eq_true, if_false]; exact r fuel hf

end GenOptMatch

/-! ## Conversions -/

section Glue

variable {S : Type} {bi : Builtins}

theorem bindsSub_nil_intro (Γ : BList) : BindsSub Γ [] := trivial

theorem bindsSub_cons_intro {Γ M : BList} {x : String} {v : Value}
    (h : bindLookup Γ x = some v) (hs : BindsSub Γ M) : BindsSub Γ ((x, v) :: M) := ⟨h, hs⟩

/-- Replace the value and the exit bindings of a derivation without exit. -/
theorem corresB_conseqVN {Γ N N' : S → BList} {G : S → Prop} {e : ImpExpr} {V V' : S → Value}
    (h : CorresB bi Γ G e V N) (hV : ∀ σ, G σ → V σ = V' σ)
    (hN : ∀ σ, G σ → BindsSub (N σ) (N' σ)) : CorresB bi Γ G e V' N' :=
  corres_conseq h (fun _ _ h _ => h) (fun _ h => h) hV
    (fun _ σ hG hb => binds_of_sub hb (hN σ hG))

/-- Sequence whose first expression may exit and whose second has no exit. -/
theorem corresG_seqL {Γ N₁ T₁ N₂ : S → BList} {G : S → Prop} {e1 e2 : ImpExpr}
    {C₁ : S → Bool} {W₁ V₁ V₂ : S → Value}
    (h1 : CorresG bi Γ G e1 C₁ W₁ V₁ T₁ N₁)
    (hp : ∀ σ, G σ → C₁ σ = false → (V₁ σ).isControlFlow = false)
    (h2 : CorresB bi N₁ (fun σ => G σ ∧ C₁ σ = false) e2 V₂ N₂) :
    CorresG bi Γ G (.seq e1 e2) C₁ W₁ V₂ T₁ N₂ := by
  have h := corresG_seq h1 hp (CorresG.ofPlain (fun _ => .unit) N₂ h2)
  have hC : (fun σ => C₁ σ || false) = C₁ := funext fun σ => Bool.or_false _
  rw [hC] at h
  refine corres_conseq h (fun _ _ h _ => h) (fun _ h => h) (fun σ _ => ?_) (fun env σ _ hb => ?_)
  · cases hc : C₁ σ <;> simp only [hc, if_true, Bool.false_eq_true, if_false]
  · cases hc : C₁ σ <;> simp only [hc, if_true, Bool.false_eq_true, if_false] at hb ⊢ <;> exact hb

/-- `let` whose bound expression may exit and whose body has no exit. -/
theorem corresG_letBindL {Γ N₁ T₁ N₂ : S → BList} {G : S → Prop} {x : String}
    {val body : ImpExpr} {C₁ : S → Bool} {W₁ V₁ V₂ : S → Value}
    (h1 : CorresG bi Γ G val C₁ W₁ V₁ T₁ N₁)
    (hp : ∀ σ, G σ → C₁ σ = false → (V₁ σ).isControlFlow = false)
    (h2 : CorresB bi (fun σ => (x, V₁ σ) :: N₁ σ) (fun σ => G σ ∧ C₁ σ = false) body V₂ N₂) :
    CorresG bi Γ G (.letBind x val body) C₁ W₁ V₂ T₁ N₂ := by
  have h := corresG_letBind h1 hp (CorresG.ofPlain (fun _ => .unit) N₂ h2)
  have hC : (fun σ => C₁ σ || false) = C₁ := funext fun σ => Bool.or_false _
  rw [hC] at h
  refine corres_conseq h (fun _ _ h _ => h) (fun _ h => h) (fun σ _ => ?_) (fun env σ _ hb => ?_)
  · cases hc : C₁ σ <;> simp only [hc, if_true, Bool.false_eq_true, if_false]
  · cases hc : C₁ σ <;> simp only [hc, if_true, Bool.false_eq_true, if_false] at hb ⊢ <;> exact hb

/-- The entry bindings of a function of the extraction. -/
theorem binds_entry {bi' : Builtins} {fn : ExtFn} {gv : BList}
    (h : fn.globalVals bi' = gv) (vs : List Value) :
    Binds (fn.entry bi' vs) (fn.params.zip vs ++ gv) := by
  rw [ExtFn.entry_eq h]
  exact binds_bindParams _

/-- A leaf of the struct and dependency table, read through the extraction table. -/
theorem extBase_leaf {T : Table} {fns : List ExtFn} {f : String} {l : Leaf}
    (hrt : runtimeTable.lookup f = none) (htag : parseTag f = none)
    (hl : T.lookup f = some l) (vs : List Value) :
    extBuiltins T fns f vs = l vs := by
  unfold extBuiltins
  rw [runtimeBuiltins_of_base hrt htag]
  exact Table.over_of_lookup hl vs

/-- Replace the exit and normal values under their conditions. -/
theorem corresG_castVW {Γ N T : S → BList} {G : S → Prop} {e : ImpExpr} {C : S → Bool}
    {W W' V V' : S → Value} (h : CorresG bi Γ G e C W V T N)
    (hW : ∀ σ, G σ → C σ = true → W σ = W' σ) (hV : ∀ σ, G σ → C σ = false → V σ = V' σ) :
    CorresG bi Γ G e C W' V' T N := by
  refine corres_conseq h (fun _ _ h _ => h) (fun _ h => h) (fun σ hG => ?_) (fun _ _ _ h => h)
  cases hc : C σ
  · simp only [Bool.false_eq_true, if_false]; exact hV σ hG hc
  · simp only [if_true]; rw [hW σ hG hc]

/-- Replace the normal exit bindings under the normal condition. -/
theorem corresG_subN {Γ N N' T : S → BList} {G : S → Prop} {e : ImpExpr} {C : S → Bool}
    {W V : S → Value} (h : CorresG bi Γ G e C W V T N)
    (hN : ∀ σ, G σ → C σ = false → BindsSub (N σ) (N' σ)) :
    CorresG bi Γ G e C W V T N' := by
  refine corres_conseq h (fun _ _ h _ => h) (fun _ h => h) (fun _ _ => rfl) (fun env σ hG hb => ?_)
  cases hc : C σ
  · simp only [hc, Bool.false_eq_true, if_false] at hb ⊢; exact binds_of_sub hb (hN σ hG hc)
  · simp only [hc, if_true] at hb ⊢; exact hb

/-- Replace the exit condition by a pointwise equal one. -/
theorem corresG_congrC {Γ N T : S → BList} {G : S → Prop} {e : ImpExpr} {C C' : S → Bool}
    {W V : S → Value} (h : CorresG bi Γ G e C W V T N) (hC : ∀ σ, C σ = C' σ) :
    CorresG bi Γ G e C' W V T N := by
  have : C = C' := funext hC
  subst this
  exact h

theorem ite_same {α : Type} (c : Bool) (a : α) : (if c = true then a else a) = a := by
  cases c <;> rfl

theorem ite_true_false (b : Bool) : (if b = true then true else false) = b := by cases b <;> rfl
theorem ite_false_true (b : Bool) : (if b = true then false else true) = !b := by cases b <;> rfl
theorem ite_true_left (b c : Bool) : (if b = true then true else c) = (b || c) := by cases b <;> rfl
theorem ite_false_right (b c : Bool) : (if b = true then c else false) = (b && c) := by
  cases b <;> rfl
theorem ite_false_left (b c : Bool) : (if b = true then false else c) = (!b && c) := by
  cases b <;> rfl
theorem ite_true_right (b c : Bool) : (if b = true then c else true) = (!b || c) := by
  cases b <;> rfl

/-- The branch taken when a conditional exit does not happen and the first branch
    always exits. -/
theorem ite_of_left_exit {α : Type} {b c : Bool} (a₁ a₂ : α)
    (h : (if b = true then true else c) = false) : (if b = true then a₁ else a₂) = a₂ := by
  cases b
  · rfl
  · simp at h

/-- The branch taken when a conditional exit does not happen and the second branch
    always exits. -/
theorem ite_of_right_exit {α : Type} {b c : Bool} (a₁ a₂ : α)
    (h : (if b = true then c else true) = false) : (if b = true then a₁ else a₂) = a₁ := by
  cases b
  · simp at h
  · rfl

/-- The branch taken when a conditional exit happens and the first branch never
    exits. -/
theorem ite_of_left_noexit {α : Type} {b c : Bool} (a₁ a₂ : α)
    (h : (if b = true then false else c) = true) : (if b = true then a₁ else a₂) = a₂ := by
  cases b
  · rfl
  · simp at h

/-- The branch taken when a conditional exit happens and the second branch never
    exits. -/
theorem ite_of_right_noexit {α : Type} {b c : Bool} (a₁ a₂ : α)
    (h : (if b = true then c else false) = true) : (if b = true then a₁ else a₂) = a₁ := by
  cases b
  · simp at h
  · rfl

/-- Replace the exit bindings under the exit condition. -/
theorem corresG_subT {Γ N T T' : S → BList} {G : S → Prop} {e : ImpExpr} {C : S → Bool}
    {W V : S → Value} (h : CorresG bi Γ G e C W V T N)
    (hT : ∀ σ, G σ → C σ = true → BindsSub (T σ) (T' σ)) :
    CorresG bi Γ G e C W V T' N := by
  refine corres_conseq h (fun _ _ h _ => h) (fun _ h => h) (fun _ _ => rfl) (fun env σ hG hb => ?_)
  cases hc : C σ
  · simp only [hc, Bool.false_eq_true, if_false] at hb ⊢; exact hb
  · simp only [hc, if_true] at hb ⊢; exact binds_of_sub hb (hT σ hG hc)

theorem map_global_nil (bi' : Builtins) :
    ([] : List String).map (fun g => (g, (bi' g []).getD .unit)) = [] := rfl

theorem map_global_cons {bi' : Builtins} {g : String} {gs : List String} {gv : BList}
    {v : Value} (h₁ : bi' g [] = some v)
    (h₂ : gs.map (fun g => (g, (bi' g []).getD .unit)) = gv) :
    (g :: gs).map (fun g => (g, (bi' g []).getD .unit)) = (g, v) :: gv := by
  simp only [List.map_cons, h₁, Option.getD_some]
  rw [h₂]

theorem globalVals_of_map {bi' : Builtins} {fn : ExtFn} {gv : BList}
    (h : fn.globals.map (fun g => (g, (bi' g []).getD .unit)) = gv) : fn.globalVals bi' = gv := h

end Glue

/-! ## Nested components -/

/-- The type `α` as one component of a tuple. Instance resolution does not unfold it, so
    a product `β × Boxed α` encodes as the pair `.tuple [enc b, enc a]` where `β × α`
    with a product `α` encodes as the flat tuple of all components. -/
def Boxed (α : Type) : Type := α

instance {α : Type} [HaxEnc α] : HaxEnc (Boxed α) := ⟨fun a => enc (α := α) a⟩

instance {α : Type} [HaxEnc α] [HaxEnc.Plain α] : HaxEnc.Plain (Boxed α) :=
  ⟨fun a => HaxEnc.Plain.not_cf (α := α) a⟩

end Hax.Ascent
