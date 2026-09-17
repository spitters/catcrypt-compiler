/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.Ascent.WhileFold
public import CatCrypt.Hax.Ascent.Exit

/-!
# Early exit in the `denote'` correspondence

The pipeline encodes an early `return` as a `controlFlow true w` value that `seq` and
`letBind` pass through, and a loop break inside a loop with early return as
`controlFlow true (controlFlow false w)` (`cfBreakContinue`). `cfExcept`
(`CatCrypt/Hax/Ascent/Exit.lean`) reads the first as the thrown value `w` of an
exception program.

## The exception level

`CorresX bi P G e R Q` is `Corres` whose value is the encoding `excVal (R σ)` of an
exception result `R σ : Except Value Value`: a thrown `w` is `controlFlow true w`, a
normal result `v` is `v`. `corresX_seq` and `corresX_letBind` are the exception monad's
bind: a thrown value skips the rest, a normal one runs it.

## Loops with early return

A step of a loop with early return is `f : S → Int → A → Except (Except R L) A`:
`.error (.error r)` returns `r` from the function, `.error (.ok l)` breaks the loop with
`l`, `.ok a` continues with `a`; this is the runtime's
`ControlFlow (ControlFlow R L) A` read through `stepToExcept`. The abstract folds are the
stopping folds of `CatCrypt/Hax/Ascent/Corres.lean` and
`CatCrypt/Hax/Ascent/WhileFold.lean` at the break type `Except R L`, and `retResult`
reads their result as the loop's exception result: normal completion is `.ok .unit`, a
loop break `.ok (Wl σ l)`, an early return the thrown `X σ r`.

## Functions

`FnCorresX bi e entry G f` states that the run of the body from `entry a` reads, through
`outcomeExceptCF`, as `encExc (f a)` from some fuel on; `fnCorresX_absProg` reads it as
the `AbsProg.except` refinement of `optGuard G f` by `haxEvalX bi e`.

## Main results

* `excVal`, `CorresX`, `corresX_of_corres`, `corresX_conseq`, `corresX_throw`,
  `corresX_seq`, `corresX_letBind`, `corresX_ifThenElse`
* `corres_cfBreakContinue`
* `fwdLoop_corres`, `corres_forFoldReturn`, `corres_forFoldRevReturn`,
  `corres_whileFoldReturn`
* `retToExcept_forFoldReturn`, `retToExcept_forFoldRevReturn`,
  `retToExcept_whileFoldReturn` — the runtime's loops with early return as the abstract
  folds
* `FnCorresX`, `fnCorresX_of_corresX`, `haxEvalX`, `fnCorresX_absProg`
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.Ascent

/-! ## The exception reading of a value -/

section Exc

/-- The value of an exception result: a thrown `w` is `controlFlow true w`, a normal
    result `v` is `v`. -/
def excVal : Except Value Value → Value
  | .error w => .controlFlow true w
  | .ok v => v

/-- A normal result is not a `controlFlow true` value. -/
def ExcPlain (r : Except Value Value) : Prop := ∀ w, r ≠ .ok (.controlFlow true w)

theorem cfExcept_excVal {r : Except Value Value} (h : ExcPlain r) : cfExcept (excVal r) = r := by
  cases r with
  | error w => rfl
  | ok v =>
    cases v with
    | controlFlow b w =>
      cases b
      · rfl
      · exact absurd rfl (h w)
    | _ => rfl

theorem excPlain_ok {v : Value} (hv : v.isControlFlow = false) : ExcPlain (.ok v) := by
  intro w h
  cases h
  simp [Value.isControlFlow] at hv

theorem excPlain_error (w : Value) : ExcPlain (.error w) := fun _ h => nomatch h

end Exc

/-! ## One-step equations -/

section Steps

variable (bi : Builtins) (fuel : Nat)

theorem denote'_seq_cf {e1 e2 : ImpExpr} {env s : Env} {b : Bool} {w : Value}
    (h : denote' bi fuel e1 env = (.val (.controlFlow b w), s)) :
    denote' bi fuel (.seq e1 e2) env = (.val (.controlFlow b w), s) := by
  simp only [denote', stateM_bind_apply, h]
  rfl

theorem denote'_letBind_cf {x : String} {val body : ImpExpr} {env s : Env} {b : Bool}
    {w : Value} (h : denote' bi fuel val env = (.val (.controlFlow b w), s)) :
    denote' bi fuel (.letBind x val body) env = (.val (.controlFlow b w), s) := by
  simp only [denote', stateM_bind_apply, h]
  rfl

theorem denote'_cfBreakContinue {e : ImpExpr} {env s : Env} {v : Value}
    (h : denote' bi fuel e env = (.val v, s)) (hv : v.isControlFlow = false) :
    denote' bi fuel (.cfBreakContinue e) env =
      (.val (.controlFlow true (.controlFlow false v)), s) := by
  simp only [denote', stateM_bind_apply, h]
  cases v <;> first | rfl | simp at hv

theorem denote'_forFoldReturn {var : String} {lo hi body : ImpExpr} {env s1 s2 : Env}
    {a b : Int} (hlo : denote' bi fuel lo env = (.val (.int a), s1))
    (hhi : denote' bi fuel hi s1 = (.val (.int b), s2)) :
    denote' bi fuel (.forFoldReturn var lo hi body) env =
      denoteForLoop'Return bi fuel var a b body s2 := by
  simp only [denote', stateM_bind_apply, hlo, hhi]

theorem denote'_forFoldRevReturn {var : String} {lo hi body : ImpExpr} {env s1 s2 : Env}
    {a b : Int} (hlo : denote' bi fuel lo env = (.val (.int a), s1))
    (hhi : denote' bi fuel hi s1 = (.val (.int b), s2)) :
    denote' bi fuel (.forFoldRevReturn var lo hi body) env =
      denoteForLoopRev'Return bi fuel var a b body s2 := by
  simp only [denote', stateM_bind_apply, hlo, hhi]

theorem denoteForLoop'Return_done (var : String) {a b : Int} (body : ImpExpr) (env : Env)
    (h : b ≤ a) : denoteForLoop'Return bi fuel var a b body env = (.val .unit, env) := by
  rw [denoteForLoop'Return]
  simp only [if_pos h]; rfl

theorem denoteForLoop'Return_step {fuel : Nat} (var : String) {a b : Int} {body : ImpExpr}
    {env s : Env} {v : Value} (hab : a < b) (hf : fuel ≠ 0)
    (h : denote' bi fuel body (env.extend var (.int a)) = (.val v, s)) :
    denoteForLoop'Return bi fuel var a b body env = match stopReturn v with
      | some w => (.val w, s)
      | none => denoteForLoop'Return bi (fuel - 1) var (a + 1) b body s := by
  rw [denoteForLoop'Return]
  simp only [if_neg (Int.not_le.mpr hab), if_neg hf, stateM_bind_apply, stateM_modify_apply, h]
  cases v with
  | controlFlow c w =>
    cases c
    · rfl
    · cases w with
      | controlFlow c' w' => cases c' <;> rfl
      | _ => rfl
  | _ => rfl

theorem denoteForLoopRev'Return_done (var : String) {a b : Int} (body : ImpExpr) (env : Env)
    (h : b ≤ a) : denoteForLoopRev'Return bi fuel var a b body env = (.val .unit, env) := by
  rw [denoteForLoopRev'Return]
  simp only [if_pos h]; rfl

theorem denoteForLoopRev'Return_step {fuel : Nat} (var : String) {a b : Int}
    {body : ImpExpr} {env s : Env} {v : Value} (hab : a < b) (hf : fuel ≠ 0)
    (h : denote' bi fuel body (env.extend var (.int (b - 1))) = (.val v, s)) :
    denoteForLoopRev'Return bi fuel var a b body env = match stopReturn v with
      | some w => (.val w, s)
      | none => denoteForLoopRev'Return bi (fuel - 1) var a (b - 1) body s := by
  rw [denoteForLoopRev'Return]
  simp only [if_neg (Int.not_le.mpr hab), if_neg hf, stateM_bind_apply, stateM_modify_apply, h]
  cases v with
  | controlFlow c w =>
    cases c
    · rfl
    · cases w with
      | controlFlow c' w' => cases c' <;> rfl
      | _ => rfl
  | _ => rfl

end Steps

/-! ## The exception-level judgment -/

section CorresX

variable {S : Type} {bi : Builtins}

/-- **The exception-level correspondence.** `Corres` whose value is the encoding
    `excVal (R σ)` of the exception result `R σ`. -/
def CorresX (bi : Builtins) (P : Env → S → Prop) (G : S → Prop) (e : ImpExpr)
    (R : S → Except Value Value) (Q : Env → S → Prop) : Prop :=
  Corres bi P G e (fun σ => excVal (R σ)) Q

/-- The exit relation of a composite whose first part may throw: `Q₁` when `R σ`
    throws, `Q₂` when it returns normally. -/
def excExit (Q₁ Q₂ : Env → S → Prop) (R : S → Except Value Value) (env : Env) (σ : S) :
    Prop :=
  match R σ with
  | .ok _ => Q₂ env σ
  | .error _ => Q₁ env σ

theorem corresX_of_corres {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} (h : Corres bi P G e V Q) : CorresX bi P G e (fun σ => .ok (V σ)) Q := h

theorem corres_of_corresX {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} (h : CorresX bi P G e (fun σ => .ok (V σ)) Q) : Corres bi P G e V Q := h

theorem corresX_conseq {P P' : Env → S → Prop} {G G' : S → Prop} {e : ImpExpr}
    {R R' : S → Except Value Value} {Q Q' : Env → S → Prop} (h : CorresX bi P G e R Q)
    (hP : ∀ env σ, P' env σ → G' σ → P env σ) (hG : ∀ σ, G' σ → G σ)
    (hR : ∀ σ, G' σ → R σ = R' σ) (hQ : ∀ env σ, G' σ → Q env σ → Q' env σ) :
    CorresX bi P' G' e R' Q' :=
  corres_conseq h hP hG (fun σ hG' => by rw [hR σ hG']) hQ

/-- **`return`.** An early return of a plain value throws it. -/
theorem corresX_throw {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr} {V : S → Value}
    (h : Corres bi P G e V Q) (hplain : ∀ σ, G σ → (V σ).isControlFlow = false) :
    CorresX bi P G (.cfBreak e) (fun σ => .error (V σ)) Q :=
  corres_cfBreak h hplain

/-- **Sequence at the exception level.** A thrown value of `e1` is the result of the
    sequence; a normal one, which is not a control-flow value, runs `e2`. -/
theorem corresX_seq {P Q₁ Q₂ : Env → S → Prop} {G : S → Prop} {e1 e2 : ImpExpr}
    {R₁ R₂ : S → Except Value Value} (h1 : CorresX bi P G e1 R₁ Q₁)
    (hplain : ∀ σ v, G σ → R₁ σ = .ok v → v.isControlFlow = false)
    (h2 : CorresX bi Q₁ (fun σ => G σ ∧ ∃ v, R₁ σ = .ok v) e2 R₂ Q₂) :
    CorresX bi P G (.seq e1 e2) (fun σ => (R₁ σ).bind fun _ => R₂ σ) (excExit Q₁ Q₂ R₁) := by
  intro env σ hP hG
  obtain ⟨f₁, e₁, hQ₁, r₁⟩ := h1 env σ hP hG
  dsimp only at r₁ ⊢
  cases hR : R₁ σ with
  | error w =>
    refine ⟨f₁, e₁, by simp only [excExit, hR]; exact hQ₁, fun fuel hf => ?_⟩
    have r := r₁ fuel hf
    simp only [hR, excVal] at r
    rw [denote'_seq_cf bi fuel r]
    rfl
  | ok v =>
    obtain ⟨f₂, e₂, hQ₂, r₂⟩ := h2 e₁ σ hQ₁ ⟨hG, v, hR⟩
    refine ⟨max f₁ f₂, e₂, by simp only [excExit, hR]; exact hQ₂, fun fuel hf => ?_⟩
    have r := r₁ fuel (by omega)
    simp only [hR, excVal] at r
    rw [denote'_seq bi fuel r (hplain σ v hG hR)]
    exact r₂ fuel (by omega)

/-- **`let` at the exception level.** A thrown value of the bound expression is the
    result; a normal value `v`, which is not a control-flow value, is bound at `x` and
    the body runs from `P₂`. -/
theorem corresX_letBind {P Q₁ P₂ Q₂ : Env → S → Prop} {G : S → Prop} {x : String}
    {val body : ImpExpr} {R₁ R₂ : S → Except Value Value} (hval : CorresX bi P G val R₁ Q₁)
    (hplain : ∀ σ v, G σ → R₁ σ = .ok v → v.isControlFlow = false)
    (hlink : ∀ env σ v, Q₁ env σ → G σ → R₁ σ = .ok v → P₂ (env.extend x v) σ)
    (hbody : CorresX bi P₂ (fun σ => G σ ∧ ∃ v, R₁ σ = .ok v) body R₂ Q₂) :
    CorresX bi P G (.letBind x val body) (fun σ => (R₁ σ).bind fun _ => R₂ σ)
      (excExit Q₁ Q₂ R₁) := by
  intro env σ hP hG
  obtain ⟨f₁, e₁, hQ₁, r₁⟩ := hval env σ hP hG
  dsimp only at r₁ ⊢
  cases hR : R₁ σ with
  | error w =>
    refine ⟨f₁, e₁, by simp only [excExit, hR]; exact hQ₁, fun fuel hf => ?_⟩
    have r := r₁ fuel hf
    simp only [hR, excVal] at r
    rw [denote'_letBind_cf bi fuel r]
    rfl
  | ok v =>
    obtain ⟨f₂, e₂, hQ₂, r₂⟩ := hbody _ σ (hlink e₁ σ v hQ₁ hG hR) ⟨hG, v, hR⟩
    refine ⟨max f₁ f₂, e₂, by simp only [excExit, hR]; exact hQ₂, fun fuel hf => ?_⟩
    have r := r₁ fuel (by omega)
    simp only [hR, excVal] at r
    rw [denote'_letBind bi fuel r (hplain σ v hG hR)]
    exact r₂ fuel (by omega)

/-- **Conditional at the exception level.** -/
theorem corresX_ifThenElse {P Q₁ Q : Env → S → Prop} {G : S → Prop} {c t e : ImpExpr}
    {C : S → Bool} {R : S → Except Value Value}
    (hc : Corres bi P G c (fun σ => .bool (C σ)) Q₁)
    (ht : CorresX bi Q₁ (fun σ => G σ ∧ C σ = true) t R Q)
    (he : CorresX bi Q₁ (fun σ => G σ ∧ C σ = false) e R Q) :
    CorresX bi P G (.ifThenElse c t e) R Q :=
  corres_ifThenElse hc ht he

/-- **Loop break inside a loop with early return.** The value is tagged
    `controlFlow true (controlFlow false ·)`. -/
theorem corres_cfBreakContinue {P Q : Env → S → Prop} {G : S → Prop} {e : ImpExpr}
    {V : S → Value} (h : Corres bi P G e V Q)
    (hplain : ∀ σ, G σ → (V σ).isControlFlow = false) :
    Corres bi P G (.cfBreakContinue e) (fun σ => .controlFlow true (.controlFlow false (V σ)))
      Q := by
  intro env σ hP hG
  obtain ⟨f₀, e₀, hQ, r⟩ := h env σ hP hG
  exact ⟨f₀, e₀, hQ, fun fuel hf => denote'_cfBreakContinue bi fuel (r fuel hf) (hplain σ hG)⟩

end CorresX

/-! ## Counted loops with early return -/

section ReturnLoops

variable {S A R L : Type} {bi : Builtins}

/-- The loop value of a stop of a loop with early return: a loop break `l` is `Wl σ l`,
    an early return `r` is `controlFlow true (X σ r)`. -/
def retStop (X : S → R → Value) (Wl : S → L → Value) (σ : S) : Except R L → Value
  | .ok l => Wl σ l
  | .error r => .controlFlow true (X σ r)

/-- The exception result of a loop with early return: normal completion is `.ok .unit`,
    a loop break `l` is `.ok (Wl σ l)`, an early return `r` throws `X σ r`. -/
def retResult (X : S → R → Value) (Wl : S → L → Value) (σ : S) :
    Except (Except R L) A → Except Value Value
  | .ok _ => .ok .unit
  | .error (.ok l) => .ok (Wl σ l)
  | .error (.error r) => .error (X σ r)

theorem excVal_retResult (X : S → R → Value) (Wl : S → L → Value) (σ : S)
    (r : Except (Except R L) A) : excVal (retResult X Wl σ r) = loopVal (retStop X Wl) σ r := by
  rcases r with (_ | _) | _ <;> rfl

/-- **The run of a forward loop helper.** For a helper `L fuel lo hi env` with the
    one-trip equations of a counted loop under the classifier `stop`, the run over the
    `n` indices from `i` to `hiF σ` returns `loopVal W σ (foldFromE (f σ) n i a)`. -/
theorem fwdLoop_corres {B : Type} {var : String} {body : ImpExpr}
    {Lh : Nat → Int → Int → Env → Outcome × Env} {stop : Value → Option Value}
    (hLd : ∀ fuel lo hi env, hi ≤ lo → Lh fuel lo hi env = (.val .unit, env))
    (hLs : ∀ fuel lo hi env s v, lo < hi → fuel ≠ 0 →
      denote' bi fuel body (env.extend var (.int lo)) = (.val v, s) →
      Lh fuel lo hi env = match stop v with
        | some w => (.val w, s)
        | none => Lh (fuel - 1) (lo + 1) hi s)
    {G : S → Prop} {loF hiF : S → Int} {f : S → Int → A → Except B A}
    {Inv : Env → S → Int → A → Prop} {Brk : Env → S → B → Prop} {Vb : S × Int × A → Value}
    {W : S → B → Value}
    (hbody : LoopBody bi var body G loF hiF f Inv Brk Vb)
    (hV : ∀ t : S × Int × A, G t.1 → loF t.1 ≤ t.2.1 → t.2.1 < hiF t.1 →
      stop (Vb t) = stepStop W t.1 (f t.1 t.2.1 t.2.2))
    (hext : ∀ env σ i a, Inv env σ i a → Inv (env.extend var (.int i)) σ i a) :
    ∀ (n : Nat) (σ : S) (i : Int) (a : A) (env : Env), G σ → loF σ ≤ i → i + n = hiF σ →
      Inv env σ i a →
      ∃ fuel₀ env', loopExit Inv Brk σ (hiF σ) (foldFromE (f σ) n i a) env' ∧
        ∀ fuel, fuel₀ ≤ fuel → Lh fuel i (hiF σ) env =
          (.val (loopVal W σ (foldFromE (f σ) n i a)), env') := by
  intro n
  induction n with
  | zero =>
    intro σ i a env _ _ hi hInv
    refine ⟨0, env, ?_, fun fuel _ => ?_⟩
    · simp only [foldFromE, loopExit]
      rw [← hi]; simpa using hInv
    · exact hLd fuel _ _ env (by omega)
  | succ n ih =>
    intro σ i a env hG hlo hi hInv
    have hlt : i < hiF σ := by omega
    have hP : Inv (env.extend var (.int i)) σ i a ∧
        (env.extend var (.int i)) var = some (.int i) :=
      ⟨hext env σ i a hInv, Env.extend_same _ _ _⟩
    obtain ⟨fb, e₁, hQ, rb⟩ := hbody (env.extend var (.int i)) (σ, i, a) hP ⟨hG, hlo, hlt⟩
    have hVt := hV (σ, i, a) hG hlo hlt
    simp only at hQ hVt rb
    cases hf : f σ i a with
    | error b =>
      simp only [hf, stepStop] at hQ hVt
      refine ⟨max fb 1, e₁, ?_, fun fuel hfu => ?_⟩
      · simp only [foldFromE, hf, loopExit]; exact hQ
      · simp only [foldFromE, hf, loopVal]
        rw [hLs fuel _ _ env e₁ _ hlt (by omega) (rb fuel (by omega)), hVt]
    | ok a' =>
      simp only [hf, stepStop] at hQ hVt
      obtain ⟨fr, e₂, hQ₂, rr⟩ := ih σ (i + 1) a' e₁ hG (by omega) (by omega) hQ
      refine ⟨max fb (fr + 1), e₂, ?_, fun fuel hfu => ?_⟩
      · simp only [foldFromE, hf]; exact hQ₂
      · simp only [foldFromE, hf]
        rw [hLs fuel _ _ env e₁ _ hlt (by omega) (rb fuel (by omega)), hVt]
        exact rr (fuel - 1) (by omega)

/-- **Counted loop with early return.** `forFoldReturn var lo hi body` over the bounds
    `loF σ ≤ hiF σ` has the exception result
    `retResult X Wl σ (foldRangeE (loF σ) (hiF σ) (a₀ σ) (f σ))`: `.ok .unit` and the
    invariant at `hiF σ` when every step continues, `.ok (Wl σ l)` when a step breaks the
    loop with `l`, and the thrown `X σ r` when a step returns `r`; the break relation
    `Brk` holds in the last two cases. A body value classified by `stopReturn` agrees with
    the step. -/
theorem corres_forFoldReturn {P Q₁ Q₂ : Env → S → Prop} {G : S → Prop} {var : String}
    {lo hi body : ImpExpr} {loF hiF : S → Int} {a₀ : S → A}
    {f : S → Int → A → Except (Except R L) A} {Inv : Env → S → Int → A → Prop}
    {Brk : Env → S → Except R L → Prop} {Vb : S × Int × A → Value}
    {X : S → R → Value} {Wl : S → L → Value}
    (hlo : Corres bi P G lo (fun σ => .int (loF σ)) Q₁)
    (hhi : Corres bi Q₁ G hi (fun σ => .int (hiF σ)) Q₂)
    (hinit : ∀ env σ, Q₂ env σ → G σ → Inv env σ (loF σ) (a₀ σ))
    (hle : ∀ σ, G σ → loF σ ≤ hiF σ)
    (hbody : LoopBody bi var body G loF hiF f Inv Brk Vb)
    (hV : ∀ t : S × Int × A, G t.1 → loF t.1 ≤ t.2.1 → t.2.1 < hiF t.1 →
      stopReturn (Vb t) = stepStop (retStop X Wl) t.1 (f t.1 t.2.1 t.2.2))
    (hext : ∀ env σ i a, Inv env σ i a → Inv (env.extend var (.int i)) σ i a) :
    CorresX bi P G (.forFoldReturn var lo hi body)
      (fun σ => retResult X Wl σ (foldRangeE (loF σ) (hiF σ) (a₀ σ) (f σ)))
      (fun env σ => loopExit Inv Brk σ (hiF σ) (foldRangeE (loF σ) (hiF σ) (a₀ σ) (f σ)) env) := by
  intro env σ hP hG
  obtain ⟨f₁, e₁, hQ₁, r₁⟩ := hlo env σ hP hG
  obtain ⟨f₂, e₂, hQ₂, r₂⟩ := hhi e₁ σ hQ₁ hG
  have hl := hle σ hG
  obtain ⟨f₃, e₃, hQ₃, r₃⟩ := fwdLoop_corres
    (Lh := fun fuel lo hi env => denoteForLoop'Return bi fuel var lo hi body env)
    (fun fuel lo hi env h => denoteForLoop'Return_done bi fuel var body env h)
    (fun fuel lo hi env s v hab hf h => denoteForLoop'Return_step bi var hab hf h)
    hbody hV hext ((hiF σ - loF σ).toNat) σ (loF σ) (a₀ σ) e₂ hG (Int.le_refl _) (by omega)
    (hinit e₂ σ hQ₂ hG)
  refine ⟨max f₁ (max f₂ f₃), e₃, hQ₃, fun fuel hf => ?_⟩
  dsimp only
  rw [excVal_retResult, denote'_forFoldReturn bi fuel (r₁ fuel (by omega)) (r₂ fuel (by omega))]
  exact r₃ fuel (by omega)

/-- **Reverse counted loop with early return.** `forFoldRevReturn var lo hi body` has the
    exception result `retResult X Wl σ (foldRangeRevE (loF σ) (hiF σ) (a₀ σ) (f σ))`. -/
theorem corres_forFoldRevReturn {P Q₁ Q₂ : Env → S → Prop} {G : S → Prop} {var : String}
    {lo hi body : ImpExpr} {loF hiF : S → Int} {a₀ : S → A}
    {f : S → Int → A → Except (Except R L) A} {Inv : Env → S → Int → A → Prop}
    {Brk : Env → S → Except R L → Prop} {Vb : S × Int × A → Value}
    {X : S → R → Value} {Wl : S → L → Value}
    (hlo : Corres bi P G lo (fun σ => .int (loF σ)) Q₁)
    (hhi : Corres bi Q₁ G hi (fun σ => .int (hiF σ)) Q₂)
    (hinit : ∀ env σ, Q₂ env σ → G σ → Inv env σ (hiF σ) (a₀ σ))
    (hle : ∀ σ, G σ → loF σ ≤ hiF σ)
    (hbody : LoopBodyRev bi var body G loF hiF f Inv Brk Vb)
    (hV : ∀ t : S × Int × A, G t.1 → loF t.1 ≤ t.2.1 → t.2.1 < hiF t.1 →
      stopReturn (Vb t) = stepStop (retStop X Wl) t.1 (f t.1 t.2.1 t.2.2))
    (hext : ∀ env σ j a, Inv env σ j a → Inv (env.extend var (.int (j - 1))) σ j a) :
    CorresX bi P G (.forFoldRevReturn var lo hi body)
      (fun σ => retResult X Wl σ (foldRangeRevE (loF σ) (hiF σ) (a₀ σ) (f σ)))
      (fun env σ => loopExit Inv Brk σ (loF σ)
        (foldRangeRevE (loF σ) (hiF σ) (a₀ σ) (f σ)) env) := by
  intro env σ hP hG
  obtain ⟨f₁, e₁, hQ₁, r₁⟩ := hlo env σ hP hG
  obtain ⟨f₂, e₂, hQ₂, r₂⟩ := hhi e₁ σ hQ₁ hG
  have hl := hle σ hG
  obtain ⟨f₃, e₃, hQ₃, r₃⟩ := revLoop_corres
    (L := fun fuel lo hi env => denoteForLoopRev'Return bi fuel var lo hi body env)
    (fun fuel lo hi env h => denoteForLoopRev'Return_done bi fuel var body env h)
    (fun fuel lo hi env s v hab hf h => denoteForLoopRev'Return_step bi var hab hf h)
    hbody hV hext ((hiF σ - loF σ).toNat) σ (hiF σ) (a₀ σ) e₂ hG (by omega) (Int.le_refl _)
    (hinit e₂ σ hQ₂ hG)
  refine ⟨max f₁ (max f₂ f₃), e₃, hQ₃, fun fuel hf => ?_⟩
  dsimp only
  rw [excVal_retResult,
    denote'_forFoldRevReturn bi fuel (r₁ fuel (by omega)) (r₂ fuel (by omega))]
  exact r₃ fuel (by omega)

/-- **While loop with early return.** `whileFoldReturn cond body` has the exception
    result `retResult X Wl σ (whileLoopE (c σ) (f σ) (a₀ σ))` on every abstract state
    satisfying the guard from which the loop terminates. -/
theorem corres_whileFoldReturn {P : Env → S → Prop} {G : S → Prop} {cond body : ImpExpr}
    {a₀ : S → A} {c : S → A → Bool} {f : S → A → Except (Except R L) A}
    {Inv InvC : Env → S → A → Prop} {Brk : Env → S → Except R L → Prop}
    {Vb : S × A → Value} {X : S → R → Value} {Wl : S → L → Value}
    (hinit : ∀ env σ, P env σ → G σ → Inv env σ (a₀ σ))
    (hcond : WhileCond bi cond G c Inv InvC)
    (hbody : WhileBody bi body G c f InvC Inv Brk Vb)
    (hV : ∀ t : S × A, G t.1 → c t.1 t.2 = true →
      stopReturn (Vb t) = stepStop (retStop X Wl) t.1 (f t.1 t.2))
    (hterm : ∀ σ, G σ → WhileTerminates (c σ) (f σ) (a₀ σ)) :
    CorresX bi P G (.whileFoldReturn cond body)
      (fun σ => retResult X Wl σ (whileLoopE (c σ) (f σ) (a₀ σ)))
      (fun env σ => whileExit InvC Brk σ (whileLoopE (c σ) (f σ) (a₀ σ)) env) := by
  intro env σ hP hG
  obtain ⟨n, r, hr⟩ := hterm σ hG
  dsimp only
  rw [whileLoopE_eq_of_rec hr, excVal_retResult]
  obtain ⟨f₀, e₀, hQ, hrun⟩ := whileLoop_total
    (L := fun fuel env => denoteWhile'Return bi fuel cond body env)
    (fun fuel env s hf hc => denoteWhile'Return_false bi hf hc)
    (fun fuel env s s' v hf hc hb => denoteWhile'Return_true bi hf hc hb)
    hcond hbody hV hG hr env (hinit env σ hP hG)
  exact ⟨f₀, e₀, hQ, fun fuel hf => by rw [denote'_whileFoldReturn]; exact hrun fuel hf⟩

/-- **A value run of `whileFoldReturn` proves termination.** -/
theorem corres_whileFoldReturn_terminates {P : Env → S → Prop} {G : S → Prop}
    {cond body : ImpExpr} {a₀ : S → A} {c : S → A → Bool}
    {f : S → A → Except (Except R L) A} {Inv InvC : Env → S → A → Prop}
    {Brk : Env → S → Except R L → Prop} {Vb : S × A → Value} {X : S → R → Value}
    {Wl : S → L → Value}
    (hinit : ∀ env σ, P env σ → G σ → Inv env σ (a₀ σ))
    (hcond : WhileCond bi cond G c Inv InvC)
    (hbody : WhileBody bi body G c f InvC Inv Brk Vb)
    (hV : ∀ t : S × A, G t.1 → c t.1 t.2 = true →
      stopReturn (Vb t) = stepStop (retStop X Wl) t.1 (f t.1 t.2))
    {env e' : Env} {σ : S} {fuel : Nat} {w : Value} (hP : P env σ) (hG : G σ)
    (hrun : denote' bi fuel (.whileFoldReturn cond body) env = (.val w, e')) :
    WhileTerminates (c σ) (f σ) (a₀ σ) := by
  rw [denote'_whileFoldReturn] at hrun
  obtain ⟨n, r, -, hr, -⟩ := whileLoop_sim
    (L := fun fuel env => denoteWhile'Return bi fuel cond body env)
    (fun fuel env s hf hc => denoteWhile'Return_false bi hf hc)
    (fun fuel env s s' v hf hc hb => denoteWhile'Return_true bi hf hc hb)
    (fun fuel env w e' h => denoteWhile'Return_inv bi h)
    hcond hbody hV hG fuel (a₀ σ) env e' w (hinit env σ hP hG) hrun
  exact ⟨n, r, hr⟩

end ReturnLoops

/-! ## The runtime's loops with early return -/

section RuntimeReturn

variable {A R L : Type}

/-- The `Except` reading of a step of a runtime loop with early return:
    `Break (Break r)` returns `r`, `Break (Continue l)` breaks the loop with `l`,
    `Continue a` continues with `a`. -/
def stepToExcept : ControlFlow (ControlFlow R L) A → Except (Except R L) A
  | .Break (.Break r) => .error (.error r)
  | .Break (.Continue l) => .error (.ok l)
  | .Continue a => .ok a

/-- The `Except` reading of the result of a runtime loop with early return:
    `Break r` is an early return, `Continue (Break l)` a loop break,
    `Continue (Continue a)` normal completion. -/
def retToExcept : ControlFlow R (ControlFlow L A) → Except (Except R L) A
  | .Break r => .error (.error r)
  | .Continue (.Break l) => .error (.ok l)
  | .Continue (.Continue a) => .ok a

/-- **The runtime's `forFoldReturn` is the stopping fold.** -/
theorem retToExcept_forFoldReturn (lo hi : Int) (a : A)
    (g : Int → A → ControlFlow (ControlFlow R L) A) :
    retToExcept (Hax.forFoldReturn lo hi a g) =
      foldRangeE lo hi a (fun i a => stepToExcept (g i a)) := by
  unfold Hax.forFoldReturn foldRangeE
  suffices H : ∀ n i a, retToExcept (Hax.forFoldReturn.go g n i a) =
      foldFromE (fun i a => stepToExcept (g i a)) n i a from H _ _ _
  intro n
  induction n with
  | zero => intro i a; rfl
  | succ n ih =>
    intro i a
    simp only [Hax.forFoldReturn.go, foldFromE]
    rcases g i a with (r | l) | a'
    · rfl
    · rfl
    · exact ih (i + 1) a'

/-- **The runtime's `forFoldRevReturn` is the stopping reverse fold.** -/
theorem retToExcept_forFoldRevReturn (lo hi : Int) (a : A)
    (g : Int → A → ControlFlow (ControlFlow R L) A) :
    retToExcept (Hax.forFoldRevReturn lo hi a g) =
      foldRangeRevE lo hi a (fun i a => stepToExcept (g i a)) := by
  unfold Hax.forFoldRevReturn foldRangeRevE
  suffices H : ∀ n i a, retToExcept (Hax.forFoldRevReturn.go g n i a) =
      foldFromRevE (fun i a => stepToExcept (g i a)) n i a from H _ _ _
  intro n
  induction n with
  | zero => intro i a; rfl
  | succ n ih =>
    intro i a
    simp only [Hax.forFoldRevReturn.go, foldFromRevE]
    rcases g i a with (r | l) | a'
    · rfl
    · rfl
    · exact ih (i - 1) a'

variable {cond : A → Bool} {g : A → ControlFlow (ControlFlow R L) A}

/-- The runtime result of an `Except` result of a loop with early return. -/
def exceptToRet : Except (Except R L) A → ControlFlow R (ControlFlow L A)
  | .error (.error r) => .Break r
  | .error (.ok l) => .Continue (.Break l)
  | .ok a => .Continue (.Continue a)

theorem retToExcept_exceptToRet (r : Except (Except R L) A) :
    retToExcept (exceptToRet r) = r := by
  rcases r with (_ | _) | _ <;> rfl

theorem whileFoldReturnFuel_of_rec {n : Nat} {a : A} {r : Except (Except R L) A}
    (h : WhileRecIn cond (fun a => stepToExcept (g a)) n a r) :
    ∀ m, n < m → Hax.whileFoldReturnFuel cond g m a = some (exceptToRet r) := by
  induction h with
  | done hc =>
    intro m hm
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp [Hax.whileFoldReturnFuel, hc, exceptToRet]
  | @brk a b hc hf =>
    intro m hm
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Hax.whileFoldReturnFuel, hc, if_true]
    rcases hg : g a with (r | l) | a'
    all_goals (rw [hg] at hf; cases hf; try rfl)
  | @step n a a' r hc hf _ ih =>
    intro m hm
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Hax.whileFoldReturnFuel, hc, if_true]
    rcases hg : g a with (r' | l) | a''
    · rw [hg] at hf; cases hf
    · rw [hg] at hf; cases hf
    · rw [hg] at hf; cases hf; exact ih m (by omega)

theorem rec_of_whileFoldReturnFuel :
    ∀ (m : Nat) (a : A) (r : ControlFlow R (ControlFlow L A)),
      Hax.whileFoldReturnFuel cond g m a = some r →
      ∃ n, WhileRecIn cond (fun a => stepToExcept (g a)) n a (retToExcept r) := by
  intro m
  induction m with
  | zero => intro a r h; simp [Hax.whileFoldReturnFuel] at h
  | succ m ih =>
    intro a r h
    simp only [Hax.whileFoldReturnFuel] at h
    cases hc : cond a with
    | false =>
      rw [hc] at h
      simp only [Bool.false_eq_true, if_false, Option.some.injEq] at h
      subst h
      exact ⟨0, .done hc⟩
    | true =>
      rw [hc, if_pos rfl] at h
      rcases hg : g a with (r' | l) | a'
      · rw [hg] at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨0, .brk hc (by rw [hg]; rfl)⟩
      · rw [hg] at h
        simp only [Option.some.injEq] at h
        subst h
        exact ⟨0, .brk hc (by rw [hg]; rfl)⟩
      · rw [hg] at h
        obtain ⟨n, hn⟩ := ih a' r h
        exact ⟨n + 1, .step hc (by rw [hg]; rfl) hn⟩

/-- **The runtime's `whileFoldReturn` is `whileLoopE`.** -/
theorem retToExcept_whileFoldReturn (a : A) :
    retToExcept (Hax.whileFoldReturn a cond g) =
      whileLoopE cond (fun a => stepToExcept (g a)) a := by
  by_cases ht : WhileTerminates cond (fun a => stepToExcept (g a)) a
  · obtain ⟨n, r, hr⟩ := ht
    rw [Hax.whileFoldReturn_eq_of_fuel (whileFoldReturnFuel_of_rec hr (n + 1) (by omega)),
      whileLoopE_eq_of_rec hr, retToExcept_exceptToRet]
  · have hs : ¬ Hax.WhileFoldReturnStops a cond g := by
      rintro ⟨m, hm⟩
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hm
      obtain ⟨n, hn⟩ := rec_of_whileFoldReturnFuel m a r hr
      exact ht ⟨n, _, hn⟩
    rw [Hax.whileFoldReturn_of_not_stops hs, whileLoopE_of_not_terminates ht]
    rfl

end RuntimeReturn

/-! ## Functions with early return -/

section Functions

variable {A R β : Type} {bi : Builtins}

/-- The exception result of a surface result, each side encoded. -/
def encExc [HaxEnc R] [HaxEnc β] : Except R β → Except Value Value
  | .error r => .error (enc r)
  | .ok b => .ok (enc b)

theorem excPlain_encExc [HaxEnc R] [HaxEnc β] [HaxEnc.Plain β] (r : Except R β) :
    ExcPlain (encExc r) := by
  cases r with
  | error r => exact excPlain_error _
  | ok b => exact excPlain_ok (HaxEnc.Plain.not_cf b)

/-- **The top-level form for a function with early return.** For every argument `a` with
    `G a`, the run of the body `e` from `entry a` reads, through `outcomeExceptCF`, as
    `encExc (f a)` from some fuel on. -/
def FnCorresX (bi : Builtins) [HaxEnc R] [HaxEnc β] (e : ImpExpr) (entry : A → Env)
    (G : A → Prop) (f : A → Except R β) : Prop :=
  ∀ a, G a → ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel →
    outcomeExceptCF (denote' bi fuel e (entry a)).1 = some (encExc (f a))

theorem fnCorresX_of_corresX [HaxEnc R] [HaxEnc β] [HaxEnc.Plain β] {e : ImpExpr}
    {entry : A → Env} {G : A → Prop} {f : A → Except R β} {Q : Env → A → Prop}
    (h : CorresX bi (fun env a => env = entry a) G e (fun a => encExc (f a)) Q) :
    FnCorresX bi e entry G f := by
  intro a hG
  obtain ⟨fuel₀, env', _, hrun⟩ := h (entry a) a rfl hG
  refine ⟨fuel₀, fun fuel hf => ?_⟩
  rw [hrun fuel hf]
  exact congrArg some (cfExcept_excVal (excPlain_encExc (f a)))

/-- The exception reading of the eventual value of the run of `e` from `env`. -/
noncomputable def haxEvalX (bi : Builtins) (e : ImpExpr) (env : Env) :
    Option (Except Value Value) :=
  (haxEval bi e env).map cfExcept

/-- **A function with early return as an exception program.** A `FnCorresX` is the
    `AbsProg.except` refinement of `optGuard G f` by `haxEvalX bi e`, with the entry
    relation `env = entry a` and the output relation `d = encExc r`. -/
theorem fnCorresX_absProg [HaxEnc R] [HaxEnc β] {e : ImpExpr} {entry : A → Env}
    {G : A → Prop} [DecidablePred G] {f : A → Except R β} (h : FnCorresX bi e entry G f) :
    (AbsProg.except (optGuard G f)).Refines (haxEvalX bi e) (fun env a => env = entry a)
      (fun d r => d = encExc r) := by
  intro env a r hentry hf
  subst hentry
  unfold optGuard at hf
  by_cases hG : G a
  · rw [if_pos hG, Option.some.injEq] at hf
    subst hf
    obtain ⟨fuel₀, hrun⟩ := h a hG
    have h₀ := hrun fuel₀ (Nat.le_refl _)
    rcases ho : (denote' bi fuel₀ e (entry a)).1 with v | v | v | _ | m
    all_goals rw [ho] at h₀
    all_goals try simp [outcomeExceptCF] at h₀
    have hev : haxEval bi e (entry a) = some v :=
      haxEval_eq (fuel₀ := fuel₀) fun fuel hf => by
        rw [denote'_val_mono bi ho hf, ho]
    exact ⟨cfExcept v, by simp [haxEvalX, hev], h₀⟩
  · rw [if_neg hG] at hf
    exact absurd hf (by simp)

end Functions

end Hax.Ascent
