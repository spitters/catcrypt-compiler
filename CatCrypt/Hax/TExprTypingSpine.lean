/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Phase.InlineLocalClosures
public import CatCrypt.Hax.TExprTypingCore

/-!
# Result types of the control-flow-aware semantics

`SpTy W S Γ E e τ` types an `ImpExpr` for the control-flow-aware evaluator `denote'` and the
spine reading `denoteSpine` that the typed front's correctness theorems run. The judgement is
parametric in a value interpretation `W : ImpType → Value → Prop`, which may represent a
type by values of another shape (the `u64` table represents words by `Value.int`), and in a
relational signature `S`, which gives a builtin several signatures (an array operation at
every length). The premises of the rules for literals, the unit value, tuples, projections
and loop counters are stated through `W`.

A control-flow value `Value.controlFlow b w` produced inside `e` passes through every
construct to the enclosing loop or to the top. The escape predicate `E` states which such
values may leave `e`: in a loop body, a loop break or continue (`foldEsc`, `foldRetEsc`); at
the top of a function body, an early return carrying a value of the result type (`retEsc`).

`TExprTyping.HasType` does not fit `denote'`: it types the node annotations (`AnnOK`), which
the extraction does not keep consistent, types a functional loop at the type of its body,
while `denote'` returns the unit value from a loop that completes, and interprets types by
`Value.HasType`, which represents `u64` by `Value.uint`.

## Main definitions

* `SpTy`, `SpTyList` — the typing judgement over literals, variables, `let`, calls, tuples,
  projections, conditionals, `()`, sequencing, type ascriptions, the functional loops
  `forFold`, `forFoldRev`, `whileFold`, their early-return forms `forFoldReturn`,
  `forFoldRevReturn`, `whileFoldReturn`, and the control-flow constructors `cfBreak`,
  `cfContinue`, `cfBreakContinue`
* `RespectW` — a builtin table returns values of the result type of every signature of `S`
* `EnvW`, `OutW`, `RunW` — typed environments, outcomes and runs
* `foldEsc`, `foldRetEsc`, `retEsc` — the escape predicates of loop bodies and function bodies
* `stripRet` — a value with its early-return tag removed

## Main results

* `SpTy.sound` — from an environment typed by `Γ`, under builtins respecting `S`, every run
  of `denote'` on an expression of type `τ` at every fuel returns a value of type `τ`, a
  control-flow value admitted by `E`, or an error, and its exit environment is typed by `Γ`
* `SpTy.denoteSpine_eq` — on a typed expression `denoteSpine` is `denote'`
* `SpTy.spine_result` — a typed function body of result type `T` run by `denoteSpine` to a
  value `v` returns a value of type `T` or an early return carrying one
* `SpTy.spine_stripRet` — the same statement through `stripRet`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.TExprTypingSpine

open _root_.Hax
open CatCrypt.Hax.TExprTyping (TyEnv TyEnv.extend TyEnv.Le)
open _root_.Hax.InlineLocalClosures (denoteSpine)

/-! ## Interpretations, signatures, escapes -/

/-- A value interpretation of types: `W τ v` states that `v` represents a value of type `τ`. -/
abbrev ValTy := ImpType → Value → Prop

/-- A relational builtin signature: `S f ts r` states that `f` takes arguments of the types
    `ts` to a result of type `r`. A builtin may carry several signatures. -/
abbrev RSig := String → List ImpType → ImpType → Prop

/-- The values `vs` have the types `ts` pointwise under `W`. -/
def ListW (W : ValTy) : List ImpType → List Value → Prop
  | [], [] => True
  | t :: ts, v :: vs => W t v ∧ ListW W ts vs
  | _, _ => False

/-- No value of any type under `W` is a control-flow value. -/
def NoCF (W : ValTy) : Prop := ∀ τ v, W τ v → v.isControlFlow = false

/-- The builtin table `bi` returns, on arguments of the parameter types of a signature of
    `S`, only values of its result type. -/
def RespectW (W : ValTy) (S : RSig) (bi : Builtins) : Prop :=
  ∀ f ts r, S f ts r → ∀ vs, ListW W ts vs → ∀ v, bi f vs = some v → W r v

/-- Every variable that `Γ` binds holds a value of its type in `env`. -/
def EnvW (W : ValTy) (Γ : TyEnv) (env : Env) : Prop :=
  ∀ x τ, Γ x = some τ → ∃ v, env x = some v ∧ W τ v

/-- An outcome of type `τ` with escapes `E`: a value of type `τ`, a control-flow value
    admitted by `E`, or an error. -/
def OutW (W : ValTy) (E : Value → Prop) : Outcome → ImpType → Prop
  | .val v, τ => W τ v ∨ (v.isControlFlow = true ∧ E v)
  | .err _, _ => True
  | _, _ => False

/-- A run of type `τ` under `Γ` with escapes `E`: its outcome has type `τ` with escapes `E`
    and its exit environment is typed by `Γ`. -/
def RunW (W : ValTy) (Γ : TyEnv) (E : Value → Prop) (τ : ImpType) (r : Outcome × Env) :
    Prop :=
  OutW W E r.1 τ ∧ EnvW W Γ r.2

/-- The escapes of the body of a loop `forFold`, `forFoldRev` or `whileFold` of type `τ`: a
    break carrying a value of type `τ`, or a continue. -/
def foldEsc (W : ValTy) (τ : ImpType) : Value → Prop
  | .controlFlow true v => W τ v
  | .controlFlow false _ => True
  | _ => False

/-- The escapes of the body of a loop `forFoldReturn`, `forFoldRevReturn` or
    `whileFoldReturn` of type `τ` inside an expression with escapes `E`: a loop break
    `Break (Continue v)` carrying a value of type `τ`, an early return `Break v` admitted by
    `E`, or a continue. -/
def foldRetEsc (W : ValTy) (τ : ImpType) (E : Value → Prop) : Value → Prop
  | .controlFlow true (.controlFlow false v) => W τ v
  | .controlFlow true v => E (.controlFlow true v)
  | .controlFlow false _ => True
  | _ => False

/-- The escapes of a function body of result type `T`: an early return `Break u` carrying a
    value of type `T`. -/
def retEsc (W : ValTy) (T : ImpType) : Value → Prop :=
  fun w => ∃ u, w = .controlFlow true u ∧ W T u

/-- A value with its early-return tag removed: `Break u` gives `u`, any other value itself. -/
def stripRet : Value → Value
  | .controlFlow true u => u
  | v => v

/-! ## The typing judgement -/

mutual
/-- `SpTy W S Γ E e τ`: under the interpretation `W`, the signature `S` and the type
    environment `Γ`, the expression `e` has type `τ`, and every control-flow value that
    leaves it is admitted by `E`. -/
inductive SpTy (W : ValTy) (S : RSig) : TyEnv → (Value → Prop) → ImpExpr → ImpType → Prop
  where
  | lit {Γ : TyEnv} {E : Value → Prop} {l : ImpLit} {τ : ImpType} :
      W τ (Value.ofLit l) → SpTy W S Γ E (.lit l) τ
  | var {Γ : TyEnv} {E : Value → Prop} {n : String} {τ : ImpType} :
      Γ n = some τ → SpTy W S Γ E (.var n) τ
  | letBind {Γ : TyEnv} {E : Value → Prop} {n : String} {v b : ImpExpr} {τ₁ τ : ImpType} :
      SpTy W S Γ E v τ₁ → TyEnv.Le Γ (Γ.extend n τ₁) → SpTy W S (Γ.extend n τ₁) E b τ →
      SpTy W S Γ E (.letBind n v b) τ
  | app {Γ : TyEnv} {E : Value → Prop} {f : String} {args : List ImpExpr}
      {ts : List ImpType} {r : ImpType} :
      S f ts r → SpTyList W S Γ E args ts → SpTy W S Γ E (.app f args) r
  | tuple {Γ : TyEnv} {E : Value → Prop} {es : List ImpExpr} {ts : List ImpType}
      {τ : ImpType} :
      SpTyList W S Γ E es ts → (∀ vs, ListW W ts vs → W τ (.tuple vs)) →
      SpTy W S Γ E (.tuple es) τ
  | proj {Γ : TyEnv} {E : Value → Prop} {e : ImpExpr} {i : Nat} {σ τ : ImpType} :
      SpTy W S Γ E e σ → (∀ v w, W σ v → v.projIdx i = some w → W τ w) →
      SpTy W S Γ E (.proj e i) τ
  | ifThenElse {Γ : TyEnv} {E : Value → Prop} {c t e : ImpExpr} {σ τ : ImpType} :
      SpTy W S Γ E c σ → SpTy W S Γ E t τ → SpTy W S Γ E e τ →
      SpTy W S Γ E (.ifThenElse c t e) τ
  | unitVal {Γ : TyEnv} {E : Value → Prop} {τ : ImpType} :
      W τ .unit → SpTy W S Γ E .unitVal τ
  | seq {Γ : TyEnv} {E : Value → Prop} {a b : ImpExpr} {σ τ : ImpType} :
      SpTy W S Γ E a σ → SpTy W S Γ E b τ → SpTy W S Γ E (.seq a b) τ
  | typeAscription {Γ : TyEnv} {E : Value → Prop} {e : ImpExpr} {s : String} {τ : ImpType} :
      SpTy W S Γ E e τ → SpTy W S Γ E (.typeAscription e s) τ
  | forFold {Γ : TyEnv} {E : Value → Prop} {v : String} {lo hi b : ImpExpr}
      {σ₁ σ₂ τi σb τ : ImpType} :
      SpTy W S Γ E lo σ₁ → SpTy W S Γ E hi σ₂ → (∀ k : Int, W τi (.int k)) →
      TyEnv.Le Γ (Γ.extend v τi) → SpTy W S (Γ.extend v τi) (foldEsc W τ) b σb →
      W τ .unit → SpTy W S Γ E (.forFold v lo hi b) τ
  | forFoldRev {Γ : TyEnv} {E : Value → Prop} {v : String} {lo hi b : ImpExpr}
      {σ₁ σ₂ τi σb τ : ImpType} :
      SpTy W S Γ E lo σ₁ → SpTy W S Γ E hi σ₂ → (∀ k : Int, W τi (.int k)) →
      TyEnv.Le Γ (Γ.extend v τi) → SpTy W S (Γ.extend v τi) (foldEsc W τ) b σb →
      W τ .unit → SpTy W S Γ E (.forFoldRev v lo hi b) τ
  | whileFold {Γ : TyEnv} {E : Value → Prop} {c b : ImpExpr} {σc σb τ : ImpType} :
      SpTy W S Γ E c σc → SpTy W S Γ (foldEsc W τ) b σb → W τ .unit →
      SpTy W S Γ E (.whileFold c b) τ
  | forFoldReturn {Γ : TyEnv} {E : Value → Prop} {v : String} {lo hi b : ImpExpr}
      {σ₁ σ₂ τi σb τ : ImpType} :
      SpTy W S Γ E lo σ₁ → SpTy W S Γ E hi σ₂ → (∀ k : Int, W τi (.int k)) →
      TyEnv.Le Γ (Γ.extend v τi) → SpTy W S (Γ.extend v τi) (foldRetEsc W τ E) b σb →
      W τ .unit → SpTy W S Γ E (.forFoldReturn v lo hi b) τ
  | forFoldRevReturn {Γ : TyEnv} {E : Value → Prop} {v : String} {lo hi b : ImpExpr}
      {σ₁ σ₂ τi σb τ : ImpType} :
      SpTy W S Γ E lo σ₁ → SpTy W S Γ E hi σ₂ → (∀ k : Int, W τi (.int k)) →
      TyEnv.Le Γ (Γ.extend v τi) → SpTy W S (Γ.extend v τi) (foldRetEsc W τ E) b σb →
      W τ .unit → SpTy W S Γ E (.forFoldRevReturn v lo hi b) τ
  | whileFoldReturn {Γ : TyEnv} {E : Value → Prop} {c b : ImpExpr} {σc σb τ : ImpType} :
      SpTy W S Γ E c σc → SpTy W S Γ (foldRetEsc W τ E) b σb → W τ .unit →
      SpTy W S Γ E (.whileFoldReturn c b) τ
  | cfBreak {Γ : TyEnv} {E : Value → Prop} {e : ImpExpr} {σ τ : ImpType} :
      SpTy W S Γ E e σ → (∀ v, W σ v → E (.controlFlow true v)) →
      SpTy W S Γ E (.cfBreak e) τ
  | cfContinue {Γ : TyEnv} {E : Value → Prop} {e : ImpExpr} {σ τ : ImpType} :
      SpTy W S Γ E e σ → (∀ v, W σ v → E (.controlFlow false v)) →
      SpTy W S Γ E (.cfContinue e) τ
  | cfBreakContinue {Γ : TyEnv} {E : Value → Prop} {e : ImpExpr} {σ τ : ImpType} :
      SpTy W S Γ E e σ → (∀ v, W σ v → E (.controlFlow true (.controlFlow false v))) →
      SpTy W S Γ E (.cfBreakContinue e) τ

/-- `SpTyList W S Γ E es ts`: the expressions `es` have the types `ts` pointwise. -/
inductive SpTyList (W : ValTy) (S : RSig) :
    TyEnv → (Value → Prop) → List ImpExpr → List ImpType → Prop where
  | nil {Γ : TyEnv} {E : Value → Prop} : SpTyList W S Γ E [] []
  | cons {Γ : TyEnv} {E : Value → Prop} {e : ImpExpr} {es : List ImpExpr} {τ : ImpType}
      {ts : List ImpType} :
      SpTy W S Γ E e τ → SpTyList W S Γ E es ts → SpTyList W S Γ E (e :: es) (τ :: ts)
end

/-! ## Typed environments -/

section Env

variable {W : ValTy}

theorem EnvW.mono {Γ Γ' : TyEnv} {env : Env} (hle : TyEnv.Le Γ Γ') (h : EnvW W Γ' env) :
    EnvW W Γ env :=
  fun x τ hx => h x τ (hle x τ hx)

theorem EnvW.extend {Γ : TyEnv} {env : Env} {n : String} {v : Value} {τ : ImpType}
    (h : EnvW W Γ env) (hv : W τ v) : EnvW W (Γ.extend n τ) (env.extend n v) := by
  intro x τ' hx
  unfold TyEnv.extend at hx
  unfold Env.extend
  split
  · rename_i hxn
    rw [if_pos hxn] at hx
    cases hx
    exact ⟨v, rfl, hv⟩
  · rename_i hxn
    rw [if_neg hxn] at hx
    exact h x τ' hx

/-- `Γ.extend n τ` extends `Γ` when `Γ` binds `n` at most at `τ`. -/
theorem TyEnv.le_extend {Γ : TyEnv} {n : String} {τ : ImpType}
    (h : ∀ τ', Γ n = some τ' → τ' = τ) : TyEnv.Le Γ (Γ.extend n τ) := by
  intro x τ' hx
  unfold TyEnv.extend
  split
  · rename_i hxn
    have hxn' : x = n := by simpa using hxn
    subst hxn'
    rw [h τ' hx]
  · exact hx

end Env

/-! ## The steps of `denote'` -/

section Steps

theorem stateM_bind_apply {σ α β : Type} (x : StateM σ α) (f : α → StateM σ β) (s : σ) :
    (x >>= f) s = f (x s).1 (x s).2 := rfl

theorem stateM_pure_apply {σ α : Type} (a : α) (s : σ) : (pure a : StateM σ α) s = (a, s) :=
  rfl

theorem stateM_modify_apply {σ : Type} (g : σ → σ) (s : σ) :
    (modify g : StateM σ PUnit) s = (⟨⟩, g s) := rfl

/-- The step after a child outcome in `denote'`: a control-flow value passes through, a
    value `w` continues with `k w`, any other outcome passes through. -/
def cfThen (k : Value → StateM Env Outcome) (o : Outcome) : StateM Env Outcome :=
  match o with
  | .val (.controlFlow b w) => pure (.val (.controlFlow b w))
  | .val w => k w
  | other => pure other

/-- The step of a counted loop after its upper bound's outcome: the loop `g` at the two
    integers when both bounds are integers or unsigned words, the outcome itself when it is
    a control-flow value or not a value, an error otherwise. -/
def boundsThen (g : Int → Int → StateM Env Outcome) (vlo : Value) (rhi : Outcome) :
    StateM Env Outcome :=
  match vlo, rhi with
  | .int lo_val, .val (.int hi_val) => g lo_val hi_val
  | .int lo_val, .val (.uint _ hi_val) => g lo_val hi_val
  | .uint _ lo_val, .val (.int hi_val) => g lo_val hi_val
  | .uint _ lo_val, .val (.uint _ hi_val) => g lo_val hi_val
  | _, .val (.controlFlow _ _) => pure rhi
  | _, .val _ => pure (.err "for loop bounds must be integers")
  | _, other => pure other

/-- The step of a loop `forFold`, `forFoldRev`, `whileFold` after its body's outcome. -/
def loopThen (cont : StateM Env Outcome) (o : Outcome) : StateM Env Outcome :=
  match o with
  | .val (.controlFlow true v) => pure (.val v)
  | .val (.controlFlow false _) => cont
  | .val _ => cont
  | other => pure other

/-- The step of a loop `forFoldReturn`, `forFoldRevReturn`, `whileFoldReturn` after its
    body's outcome. -/
def loopRetThen (cont : StateM Env Outcome) (o : Outcome) : StateM Env Outcome :=
  match o with
  | .val (.controlFlow true (.controlFlow false v)) => pure (.val v)
  | .val (.controlFlow true v) => pure (.val (.controlFlow true v))
  | .val (.controlFlow false _) => cont
  | .val _ => cont
  | other => pure other

/-- The step of a conditional or a loop condition after the condition's value, with the
    error message `msg` on a value that is not a Boolean. -/
def condThen (msg : String) (t e : StateM Env Outcome) (w : Value) : StateM Env Outcome :=
  match w with
  | .bool true => t
  | .bool false => e
  | _ => pure (.err msg)

/-- The step of an argument-list evaluation after an element's outcome: a value that is not a
    control-flow value continues with `k`, any other outcome gives no list. -/
def argsThen (k : Value → StateM Env (Option (List Value))) (o : Outcome) :
    StateM Env (Option (List Value)) :=
  match o with
  | .val (.controlFlow _ _) => pure none
  | .val v => k v
  | _ => pure none

variable (bi : Builtins) (fuel : Nat)

theorem denote'_letBind (n : String) (v b : ImpExpr) :
    denote' bi fuel (.letBind n v b) =
      denote' bi fuel v >>= cfThen (fun w => do modify (Env.extend · n w); denote' bi fuel b) := by
  rw [denote']; rfl

theorem denote'_seq (a b : ImpExpr) :
    denote' bi fuel (.seq a b) = denote' bi fuel a >>= cfThen (fun _ => denote' bi fuel b) := by
  rw [denote']; rfl

theorem denote'_proj (e : ImpExpr) (i : Nat) :
    denote' bi fuel (.proj e i) = denote' bi fuel e >>= cfThen (fun v =>
      match v.projIdx i with
      | some vi => pure (.val vi)
      | none => pure (.err s!"projection index {i} out of range")) := by
  rw [denote']; rfl

theorem denote'_cfBreak (e : ImpExpr) :
    denote' bi fuel (.cfBreak e) =
      denote' bi fuel e >>= cfThen (fun w => pure (.val (.controlFlow true w))) := by
  rw [denote']; rfl

theorem denote'_cfContinue (e : ImpExpr) :
    denote' bi fuel (.cfContinue e) =
      denote' bi fuel e >>= cfThen (fun w => pure (.val (.controlFlow false w))) := by
  rw [denote']; rfl

theorem denote'_cfBreakContinue (e : ImpExpr) :
    denote' bi fuel (.cfBreakContinue e) =
      denote' bi fuel e >>=
        cfThen (fun w => pure (.val (.controlFlow true (.controlFlow false w)))) := by
  rw [denote']; rfl

theorem denote'_ifThenElse (c t e : ImpExpr) :
    denote' bi fuel (.ifThenElse c t e) =
      denote' bi fuel c >>=
        cfThen (condThen "if condition not a bool" (denote' bi fuel t) (denote' bi fuel e)) := by
  rw [denote']
  congr 1
  funext o
  rcases o with v | _ | _ | _ | _
  · cases v with
    | bool b => cases b <;> rfl
    | _ => rfl
  all_goals rfl

theorem denote'_forFold (var : String) (lo hi body : ImpExpr) :
    denote' bi fuel (.forFold var lo hi body) =
      denote' bi fuel lo >>= cfThen (fun vlo => denote' bi fuel hi >>=
        boundsThen (fun a b => denoteForLoop' bi fuel var a b body) vlo) := by
  rw [denote']
  congr 1
  funext o
  rcases o with v | _ | _ | _ | _
  · cases v <;> rfl
  all_goals rfl

theorem denote'_forFoldRev (var : String) (lo hi body : ImpExpr) :
    denote' bi fuel (.forFoldRev var lo hi body) =
      denote' bi fuel lo >>= cfThen (fun vlo => denote' bi fuel hi >>=
        boundsThen (fun a b => denoteForLoopRev' bi fuel var a b body) vlo) := by
  rw [denote']
  congr 1
  funext o
  rcases o with v | _ | _ | _ | _
  · cases v <;> rfl
  all_goals rfl

theorem denote'_forFoldReturn (var : String) (lo hi body : ImpExpr) :
    denote' bi fuel (.forFoldReturn var lo hi body) =
      denote' bi fuel lo >>= cfThen (fun vlo => denote' bi fuel hi >>=
        boundsThen (fun a b => denoteForLoop'Return bi fuel var a b body) vlo) := by
  rw [denote']
  congr 1
  funext o
  rcases o with v | _ | _ | _ | _
  · cases v <;> rfl
  all_goals rfl

theorem denote'_forFoldRevReturn (var : String) (lo hi body : ImpExpr) :
    denote' bi fuel (.forFoldRevReturn var lo hi body) =
      denote' bi fuel lo >>= cfThen (fun vlo => denote' bi fuel hi >>=
        boundsThen (fun a b => denoteForLoopRev'Return bi fuel var a b body) vlo) := by
  rw [denote']
  congr 1
  funext o
  rcases o with v | _ | _ | _ | _
  · cases v <;> rfl
  all_goals rfl

theorem denoteForLoop'_eq (var : String) (lo hi : Int) (body : ImpExpr) :
    denoteForLoop' bi fuel var lo hi body =
      if lo ≥ hi then pure (.val .unit)
      else if fuel = 0 then pure (.err "out of fuel")
      else (modify (Env.extend · var (.int lo)) >>= fun _ => denote' bi fuel body >>=
        loopThen (denoteForLoop' bi (fuel - 1) var (lo + 1) hi body)) := by
  rw [denoteForLoop']; rfl

theorem denoteForLoopRev'_eq (var : String) (lo hi : Int) (body : ImpExpr) :
    denoteForLoopRev' bi fuel var lo hi body =
      if lo ≥ hi then pure (.val .unit)
      else if fuel = 0 then pure (.err "out of fuel")
      else (modify (Env.extend · var (.int (hi - 1))) >>= fun _ => denote' bi fuel body >>=
        loopThen (denoteForLoopRev' bi (fuel - 1) var lo (hi - 1) body)) := by
  rw [denoteForLoopRev']; rfl

theorem denoteForLoop'Return_eq (var : String) (lo hi : Int) (body : ImpExpr) :
    denoteForLoop'Return bi fuel var lo hi body =
      if lo ≥ hi then pure (.val .unit)
      else if fuel = 0 then pure (.err "out of fuel")
      else (modify (Env.extend · var (.int lo)) >>= fun _ => denote' bi fuel body >>=
        loopRetThen (denoteForLoop'Return bi (fuel - 1) var (lo + 1) hi body)) := by
  rw [denoteForLoop'Return]; rfl

theorem denoteForLoopRev'Return_eq (var : String) (lo hi : Int) (body : ImpExpr) :
    denoteForLoopRev'Return bi fuel var lo hi body =
      if lo ≥ hi then pure (.val .unit)
      else if fuel = 0 then pure (.err "out of fuel")
      else (modify (Env.extend · var (.int (hi - 1))) >>= fun _ => denote' bi fuel body >>=
        loopRetThen (denoteForLoopRev'Return bi (fuel - 1) var lo (hi - 1) body)) := by
  rw [denoteForLoopRev'Return]; rfl

theorem denoteWhile'_eq (cond body : ImpExpr) :
    denoteWhile' bi fuel cond body =
      if fuel = 0 then pure (.err "out of fuel")
      else denote' bi fuel cond >>= cfThen (condThen "while condition not a bool"
        (denote' bi fuel body >>= loopThen (denoteWhile' bi (fuel - 1) cond body))
        (pure (.val .unit))) := by
  rw [denoteWhile']
  by_cases h : fuel = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    congr 1
    funext o
    rcases o with v | _ | _ | _ | _
    · cases v with
      | bool b => cases b <;> rfl
      | _ => rfl
    all_goals rfl

theorem denoteWhile'Return_eq (cond body : ImpExpr) :
    denoteWhile'Return bi fuel cond body =
      if fuel = 0 then pure (.err "out of fuel")
      else denote' bi fuel cond >>= cfThen (condThen "while condition not a bool"
        (denote' bi fuel body >>= loopRetThen (denoteWhile'Return bi (fuel - 1) cond body))
        (pure (.val .unit))) := by
  rw [denoteWhile'Return]
  by_cases h : fuel = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    congr 1
    funext o
    rcases o with v | _ | _ | _ | _
    · cases v with
      | bool b => cases b <;> rfl
      | _ => rfl
    all_goals rfl

theorem denoteArgs'_cons (e : ImpExpr) (es : List ImpExpr) :
    denoteArgs' bi fuel (e :: es) = denote' bi fuel e >>= argsThen (fun v => do
      let rest ← denoteArgs' bi fuel es
      pure (rest.map (v :: ·))) := by
  rw [denoteArgs']; rfl

theorem cfThen_val {k : Value → StateM Env Outcome} {v : Value}
    (h : v.isControlFlow = false) : cfThen k (.val v) = k v := by
  cases v <;> first | rfl | simp [Value.isControlFlow] at h

theorem argsThen_val {k : Value → StateM Env (Option (List Value))} {v : Value}
    (h : v.isControlFlow = false) : argsThen k (.val v) = k v := by
  cases v <;> first | rfl | simp [Value.isControlFlow] at h

theorem loopThen_val {cont : StateM Env Outcome} {v : Value}
    (h : v.isControlFlow = false) : loopThen cont (.val v) = cont := by
  cases v <;> first | rfl | simp [Value.isControlFlow] at h

theorem loopRetThen_val {cont : StateM Env Outcome} {v : Value}
    (h : v.isControlFlow = false) : loopRetThen cont (.val v) = cont := by
  cases v <;> first | rfl | simp [Value.isControlFlow] at h

end Steps

/-! ## Typed runs of the steps -/

section Runs

variable {W : ValTy} {Γ : TyEnv} {E : Value → Prop} {τ : ImpType}

/-- A typed argument-list run: every list it returns has the types `ts`, and its exit
    environment is typed by `Γ`. -/
def ArgsW (W : ValTy) (Γ : TyEnv) (ts : List ImpType) (r : Option (List Value) × Env) :
    Prop :=
  (∀ vs, r.1 = some vs → ListW W ts vs) ∧ EnvW W Γ r.2

theorem OutW.val_cases (hW : NoCF W) {σ : ImpType} {v : Value} (h : OutW W E (.val v) σ) :
    (W σ v ∧ v.isControlFlow = false) ∨ ∃ b w, v = .controlFlow b w ∧ E (.controlFlow b w) := by
  rcases h with h | ⟨hc, he⟩
  · exact Or.inl ⟨h, hW _ _ h⟩
  · cases v <;> simp [Value.isControlFlow] at hc
    exact Or.inr ⟨_, _, rfl, he⟩

theorem cfThen_run (hW : NoCF W) {σ : ImpType} {k : Value → StateM Env Outcome} {o : Outcome}
    {s : Env} (ho : OutW W E o σ) (hs : EnvW W Γ s)
    (hk : ∀ v, W σ v → RunW W Γ E τ (k v s)) : RunW W Γ E τ (cfThen k o s) := by
  cases o with
  | val v =>
    rcases OutW.val_cases hW ho with ⟨hv, hc⟩ | ⟨b, w, rfl, he⟩
    · rw [cfThen_val hc]; exact hk v hv
    · exact ⟨Or.inr ⟨rfl, he⟩, hs⟩
  | err m => exact ⟨trivial, hs⟩
  | _ => exact ho.elim

theorem boundsThen_run (hW : NoCF W) {σ : ImpType} {g : Int → Int → StateM Env Outcome}
    {vlo : Value} {o : Outcome} {s : Env} (ho : OutW W E o σ) (hs : EnvW W Γ s)
    (hg : ∀ a b, RunW W Γ E τ (g a b s)) : RunW W Γ E τ (boundsThen g vlo o s) := by
  cases o with
  | val v =>
    rcases OutW.val_cases hW ho with ⟨-, hc⟩ | ⟨b, w, rfl, he⟩
    · cases vlo <;> cases v <;>
        first | exact hg _ _ | exact ⟨trivial, hs⟩ | simp [Value.isControlFlow] at hc
    · cases vlo <;> exact ⟨Or.inr ⟨rfl, he⟩, hs⟩
  | err m => cases vlo <;> exact ⟨trivial, hs⟩
  | _ => cases vlo <;> exact ho.elim

theorem loopThen_run (hW : NoCF W) {σb : ImpType} {cont : StateM Env Outcome} {o : Outcome}
    {s : Env} (ho : OutW W (foldEsc W τ) o σb) (hs : EnvW W Γ s)
    (hc : RunW W Γ E τ (cont s)) : RunW W Γ E τ (loopThen cont o s) := by
  cases o with
  | val v =>
    rcases OutW.val_cases hW ho with ⟨-, hnc⟩ | ⟨b, w, rfl, he⟩
    · rw [loopThen_val hnc]; exact hc
    · cases b
      · exact hc
      · exact ⟨Or.inl he, hs⟩
  | err m => exact ⟨trivial, hs⟩
  | _ => exact ho.elim

theorem loopRetThen_run (hW : NoCF W) {σb : ImpType} {cont : StateM Env Outcome}
    {o : Outcome} {s : Env} (ho : OutW W (foldRetEsc W τ E) o σb) (hs : EnvW W Γ s)
    (hc : RunW W Γ E τ (cont s)) : RunW W Γ E τ (loopRetThen cont o s) := by
  cases o with
  | val v =>
    rcases OutW.val_cases hW ho with ⟨-, hnc⟩ | ⟨b, w, rfl, he⟩
    · rw [loopRetThen_val hnc]; exact hc
    · cases b
      · exact hc
      · cases w with
        | controlFlow c u =>
          cases c
          · exact ⟨Or.inl he, hs⟩
          · exact ⟨Or.inr ⟨rfl, he⟩, hs⟩
        | _ => exact ⟨Or.inr ⟨rfl, he⟩, hs⟩
  | err m => exact ⟨trivial, hs⟩
  | _ => exact ho.elim

variable {bi : Builtins}

/-- The typed run of `e` at every fuel from every environment typed by `Γ`. -/
def Sound (W : ValTy) (bi : Builtins) (Γ : TyEnv) (E : Value → Prop) (τ : ImpType)
    (e : ImpExpr) : Prop :=
  ∀ fuel env, EnvW W Γ env → RunW W Γ E τ (denote' bi fuel e env)

theorem forLoop_run (hW : NoCF W) {τi σb : ImpType} {var : String} {body : ImpExpr}
    (hle : TyEnv.Le Γ (Γ.extend var τi)) (hint : ∀ k : Int, W τi (.int k)) (hunit : W τ .unit)
    (hb : Sound W bi (Γ.extend var τi) (foldEsc W τ) σb body) :
    ∀ fuel (lo hi : Int) env, EnvW W Γ env →
      RunW W Γ E τ (denoteForLoop' bi fuel var lo hi body env) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi env henv
    rw [denoteForLoop'_eq]
    by_cases h : lo ≥ hi
    · rw [if_pos h]; exact ⟨Or.inl hunit, henv⟩
    · rw [if_neg h, if_pos rfl]; exact ⟨trivial, henv⟩
  | succ f ih =>
    intro lo hi env henv
    rw [denoteForLoop'_eq]
    by_cases h : lo ≥ hi
    · rw [if_pos h]; exact ⟨Or.inl hunit, henv⟩
    · rw [if_neg h, if_neg (Nat.succ_ne_zero f)]
      simp only [stateM_bind_apply, stateM_modify_apply]
      obtain ⟨ho, hs⟩ := hb (f + 1) _ (henv.extend (n := var) (hint lo))
      exact loopThen_run hW ho (hs.mono hle) (ih (lo + 1) hi _ (hs.mono hle))

theorem forLoopRev_run (hW : NoCF W) {τi σb : ImpType} {var : String} {body : ImpExpr}
    (hle : TyEnv.Le Γ (Γ.extend var τi)) (hint : ∀ k : Int, W τi (.int k)) (hunit : W τ .unit)
    (hb : Sound W bi (Γ.extend var τi) (foldEsc W τ) σb body) :
    ∀ fuel (lo hi : Int) env, EnvW W Γ env →
      RunW W Γ E τ (denoteForLoopRev' bi fuel var lo hi body env) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi env henv
    rw [denoteForLoopRev'_eq]
    by_cases h : lo ≥ hi
    · rw [if_pos h]; exact ⟨Or.inl hunit, henv⟩
    · rw [if_neg h, if_pos rfl]; exact ⟨trivial, henv⟩
  | succ f ih =>
    intro lo hi env henv
    rw [denoteForLoopRev'_eq]
    by_cases h : lo ≥ hi
    · rw [if_pos h]; exact ⟨Or.inl hunit, henv⟩
    · rw [if_neg h, if_neg (Nat.succ_ne_zero f)]
      simp only [stateM_bind_apply, stateM_modify_apply]
      obtain ⟨ho, hs⟩ := hb (f + 1) _ (henv.extend (n := var) (hint (hi - 1)))
      exact loopThen_run hW ho (hs.mono hle) (ih lo (hi - 1) _ (hs.mono hle))

theorem forLoopReturn_run (hW : NoCF W) {τi σb : ImpType} {var : String} {body : ImpExpr}
    (hle : TyEnv.Le Γ (Γ.extend var τi)) (hint : ∀ k : Int, W τi (.int k)) (hunit : W τ .unit)
    (hb : Sound W bi (Γ.extend var τi) (foldRetEsc W τ E) σb body) :
    ∀ fuel (lo hi : Int) env, EnvW W Γ env →
      RunW W Γ E τ (denoteForLoop'Return bi fuel var lo hi body env) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi env henv
    rw [denoteForLoop'Return_eq]
    by_cases h : lo ≥ hi
    · rw [if_pos h]; exact ⟨Or.inl hunit, henv⟩
    · rw [if_neg h, if_pos rfl]; exact ⟨trivial, henv⟩
  | succ f ih =>
    intro lo hi env henv
    rw [denoteForLoop'Return_eq]
    by_cases h : lo ≥ hi
    · rw [if_pos h]; exact ⟨Or.inl hunit, henv⟩
    · rw [if_neg h, if_neg (Nat.succ_ne_zero f)]
      simp only [stateM_bind_apply, stateM_modify_apply]
      obtain ⟨ho, hs⟩ := hb (f + 1) _ (henv.extend (n := var) (hint lo))
      exact loopRetThen_run hW ho (hs.mono hle) (ih (lo + 1) hi _ (hs.mono hle))

theorem forLoopRevReturn_run (hW : NoCF W) {τi σb : ImpType} {var : String} {body : ImpExpr}
    (hle : TyEnv.Le Γ (Γ.extend var τi)) (hint : ∀ k : Int, W τi (.int k)) (hunit : W τ .unit)
    (hb : Sound W bi (Γ.extend var τi) (foldRetEsc W τ E) σb body) :
    ∀ fuel (lo hi : Int) env, EnvW W Γ env →
      RunW W Γ E τ (denoteForLoopRev'Return bi fuel var lo hi body env) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi env henv
    rw [denoteForLoopRev'Return_eq]
    by_cases h : lo ≥ hi
    · rw [if_pos h]; exact ⟨Or.inl hunit, henv⟩
    · rw [if_neg h, if_pos rfl]; exact ⟨trivial, henv⟩
  | succ f ih =>
    intro lo hi env henv
    rw [denoteForLoopRev'Return_eq]
    by_cases h : lo ≥ hi
    · rw [if_pos h]; exact ⟨Or.inl hunit, henv⟩
    · rw [if_neg h, if_neg (Nat.succ_ne_zero f)]
      simp only [stateM_bind_apply, stateM_modify_apply]
      obtain ⟨ho, hs⟩ := hb (f + 1) _ (henv.extend (n := var) (hint (hi - 1)))
      exact loopRetThen_run hW ho (hs.mono hle) (ih lo (hi - 1) _ (hs.mono hle))

theorem whileLoop_run (hW : NoCF W) {σc σb : ImpType} {cond body : ImpExpr}
    (hunit : W τ .unit) (hc : Sound W bi Γ E σc cond) (hb : Sound W bi Γ (foldEsc W τ) σb body) :
    ∀ fuel env, EnvW W Γ env → RunW W Γ E τ (denoteWhile' bi fuel cond body env) := by
  intro fuel
  induction fuel with
  | zero =>
    intro env henv
    rw [denoteWhile'_eq, if_pos rfl]
    exact ⟨trivial, henv⟩
  | succ f ih =>
    intro env henv
    rw [denoteWhile'_eq, if_neg (Nat.succ_ne_zero f), stateM_bind_apply]
    obtain ⟨ho, hs⟩ := hc (f + 1) env henv
    refine cfThen_run hW ho hs fun w _ => ?_
    cases w with
    | bool b =>
      cases b
      · exact ⟨Or.inl hunit, hs⟩
      · simp only [condThen, stateM_bind_apply]
        obtain ⟨ho', hs'⟩ := hb (f + 1) _ hs
        exact loopThen_run hW ho' hs' (ih _ hs')
    | _ => exact ⟨trivial, hs⟩

theorem whileLoopReturn_run (hW : NoCF W) {σc σb : ImpType} {cond body : ImpExpr}
    (hunit : W τ .unit) (hc : Sound W bi Γ E σc cond)
    (hb : Sound W bi Γ (foldRetEsc W τ E) σb body) :
    ∀ fuel env, EnvW W Γ env → RunW W Γ E τ (denoteWhile'Return bi fuel cond body env) := by
  intro fuel
  induction fuel with
  | zero =>
    intro env henv
    rw [denoteWhile'Return_eq, if_pos rfl]
    exact ⟨trivial, henv⟩
  | succ f ih =>
    intro env henv
    rw [denoteWhile'Return_eq, if_neg (Nat.succ_ne_zero f), stateM_bind_apply]
    obtain ⟨ho, hs⟩ := hc (f + 1) env henv
    refine cfThen_run hW ho hs fun w _ => ?_
    cases w with
    | bool b =>
      cases b
      · exact ⟨Or.inl hunit, hs⟩
      · simp only [condThen, stateM_bind_apply]
        obtain ⟨ho', hs'⟩ := hb (f + 1) _ hs
        exact loopRetThen_run hW ho' hs' (ih _ hs')
    | _ => exact ⟨trivial, hs⟩

end Runs

/-! ## Soundness -/

section Soundness

variable {W : ValTy} {S : RSig} {bi : Builtins}

mutual
/-- **Result-type soundness of `denote'`.**  From an environment typed by `Γ`, under builtins
    respecting `S`, every run of `denote'` on an expression of type `τ` with escapes `E`, at
    every fuel, returns a value of type `τ`, a control-flow value admitted by `E`, or an
    error, and its exit environment is typed by `Γ`. -/
theorem SpTy.sound (hW : NoCF W) (hbi : RespectW W S bi) : {Γ : TyEnv} → {E : Value → Prop} →
    {e : ImpExpr} → {τ : ImpType} → SpTy W S Γ E e τ → Sound W bi Γ E τ e
  | _, _, _, _, .lit h, fuel, env, henv => by
      rw [denote']; exact ⟨Or.inl h, henv⟩
  | _, _, _, _, @SpTy.var _ _ _ _ n _ hn, fuel, env, henv => by
      obtain ⟨v, hv, hvt⟩ := henv _ _ hn
      rw [denote']
      simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        StateT.pure, hv]
      exact ⟨Or.inl hvt, henv⟩
  | _, _, _, _, @SpTy.letBind _ _ _ _ n _ _ _ _ hv hle hb, fuel, env, henv => by
      have h1 := SpTy.sound hW hbi hv fuel env henv
      rw [denote'_letBind, stateM_bind_apply]
      refine cfThen_run hW h1.1 h1.2 fun w hw => ?_
      simp only [stateM_bind_apply, stateM_modify_apply]
      have h2 := SpTy.sound hW hbi hb fuel _ (h1.2.extend (n := n) hw)
      exact ⟨h2.1, h2.2.mono hle⟩
  | _, _, _, _, @SpTy.app _ _ _ _ f args ts r hS hargs, fuel, env, henv => by
      have h1 := SpTyList.sound hW hbi hargs fuel env henv
      rw [denote', denoteApp', stateM_bind_apply]
      generalize denoteArgs' bi fuel args env = ra at h1 ⊢
      obtain ⟨hvs, hs⟩ := h1
      rcases ra with ⟨_ | vals, s⟩
      · exact ⟨trivial, hs⟩
      · dsimp only
        rcases hb : bi f vals with _ | v
        · exact ⟨trivial, hs⟩
        · exact ⟨Or.inl (hbi f ts r hS vals (hvs vals rfl) v hb), hs⟩
  | _, _, _, _, @SpTy.tuple _ _ _ _ es ts _ hes htw, fuel, env, henv => by
      have h1 := SpTyList.sound hW hbi hes fuel env henv
      rw [denote', stateM_bind_apply]
      generalize denoteArgs' bi fuel es env = ra at h1 ⊢
      obtain ⟨hvs, hs⟩ := h1
      rcases ra with ⟨_ | vals, s⟩
      · exact ⟨trivial, hs⟩
      · exact ⟨Or.inl (htw vals (hvs vals rfl)), hs⟩
  | _, _, _, _, @SpTy.proj _ _ _ _ _ i _ _ he hp, fuel, env, henv => by
      have h1 := SpTy.sound hW hbi he fuel env henv
      rw [denote'_proj, stateM_bind_apply]
      refine cfThen_run hW h1.1 h1.2 fun v hv => ?_
      rcases hpi : v.projIdx i with _ | w
      · simp only; exact ⟨trivial, h1.2⟩
      · simp only; exact ⟨Or.inl (hp v w hv hpi), h1.2⟩
  | _, _, _, _, .ifThenElse hc ht he, fuel, env, henv => by
      have h1 := SpTy.sound hW hbi hc fuel env henv
      rw [denote'_ifThenElse, stateM_bind_apply]
      refine cfThen_run hW h1.1 h1.2 fun w _ => ?_
      cases w with
      | bool b =>
        cases b
        · exact SpTy.sound hW hbi he fuel _ h1.2
        · exact SpTy.sound hW hbi ht fuel _ h1.2
      | _ => exact ⟨trivial, h1.2⟩
  | _, _, _, _, .unitVal h, fuel, env, henv => by
      rw [denote']; exact ⟨Or.inl h, henv⟩
  | _, _, _, _, .seq ha hb, fuel, env, henv => by
      have h1 := SpTy.sound hW hbi ha fuel env henv
      rw [denote'_seq, stateM_bind_apply]
      exact cfThen_run hW h1.1 h1.2 fun _ _ => SpTy.sound hW hbi hb fuel _ h1.2
  | _, _, _, _, .typeAscription he, fuel, env, henv => by
      rw [denote']; exact SpTy.sound hW hbi he fuel env henv
  | _, _, _, _, .forFold hlo hhi hint hle hb hunit, fuel, env, henv => by
      have h1 := SpTy.sound hW hbi hlo fuel env henv
      rw [denote'_forFold, stateM_bind_apply]
      refine cfThen_run hW h1.1 h1.2 fun _ _ => ?_
      rw [stateM_bind_apply]
      have h2 := SpTy.sound hW hbi hhi fuel _ h1.2
      exact boundsThen_run hW h2.1 h2.2 fun a b =>
        forLoop_run hW hle hint hunit (SpTy.sound hW hbi hb) fuel a b _ h2.2
  | _, _, _, _, .forFoldRev hlo hhi hint hle hb hunit, fuel, env, henv => by
      have h1 := SpTy.sound hW hbi hlo fuel env henv
      rw [denote'_forFoldRev, stateM_bind_apply]
      refine cfThen_run hW h1.1 h1.2 fun _ _ => ?_
      rw [stateM_bind_apply]
      have h2 := SpTy.sound hW hbi hhi fuel _ h1.2
      exact boundsThen_run hW h2.1 h2.2 fun a b =>
        forLoopRev_run hW hle hint hunit (SpTy.sound hW hbi hb) fuel a b _ h2.2
  | _, _, _, _, .whileFold hc hb hunit, fuel, env, henv => by
      rw [denote']
      exact whileLoop_run hW hunit (SpTy.sound hW hbi hc) (SpTy.sound hW hbi hb) fuel env henv
  | _, _, _, _, .forFoldReturn hlo hhi hint hle hb hunit, fuel, env, henv => by
      have h1 := SpTy.sound hW hbi hlo fuel env henv
      rw [denote'_forFoldReturn, stateM_bind_apply]
      refine cfThen_run hW h1.1 h1.2 fun _ _ => ?_
      rw [stateM_bind_apply]
      have h2 := SpTy.sound hW hbi hhi fuel _ h1.2
      exact boundsThen_run hW h2.1 h2.2 fun a b =>
        forLoopReturn_run hW hle hint hunit (SpTy.sound hW hbi hb) fuel a b _ h2.2
  | _, _, _, _, .forFoldRevReturn hlo hhi hint hle hb hunit, fuel, env, henv => by
      have h1 := SpTy.sound hW hbi hlo fuel env henv
      rw [denote'_forFoldRevReturn, stateM_bind_apply]
      refine cfThen_run hW h1.1 h1.2 fun _ _ => ?_
      rw [stateM_bind_apply]
      have h2 := SpTy.sound hW hbi hhi fuel _ h1.2
      exact boundsThen_run hW h2.1 h2.2 fun a b =>
        forLoopRevReturn_run hW hle hint hunit (SpTy.sound hW hbi hb) fuel a b _ h2.2
  | _, _, _, _, .whileFoldReturn hc hb hunit, fuel, env, henv => by
      rw [denote']
      exact whileLoopReturn_run hW hunit (SpTy.sound hW hbi hc) (SpTy.sound hW hbi hb) fuel env
        henv
  | _, _, _, _, .cfBreak he hE, fuel, env, henv => by
      have h1 := SpTy.sound hW hbi he fuel env henv
      rw [denote'_cfBreak, stateM_bind_apply]
      exact cfThen_run hW h1.1 h1.2 fun v hv => ⟨Or.inr ⟨rfl, hE v hv⟩, h1.2⟩
  | _, _, _, _, .cfContinue he hE, fuel, env, henv => by
      have h1 := SpTy.sound hW hbi he fuel env henv
      rw [denote'_cfContinue, stateM_bind_apply]
      exact cfThen_run hW h1.1 h1.2 fun v hv => ⟨Or.inr ⟨rfl, hE v hv⟩, h1.2⟩
  | _, _, _, _, .cfBreakContinue he hE, fuel, env, henv => by
      have h1 := SpTy.sound hW hbi he fuel env henv
      rw [denote'_cfBreakContinue, stateM_bind_apply]
      exact cfThen_run hW h1.1 h1.2 fun v hv => ⟨Or.inr ⟨rfl, hE v hv⟩, h1.2⟩

/-- Result-type soundness of `denoteArgs'` on a typed argument list. -/
theorem SpTyList.sound (hW : NoCF W) (hbi : RespectW W S bi) : {Γ : TyEnv} →
    {E : Value → Prop} → {es : List ImpExpr} → {ts : List ImpType} → SpTyList W S Γ E es ts →
    ∀ fuel env, EnvW W Γ env → ArgsW W Γ ts (denoteArgs' bi fuel es env)
  | _, _, _, _, .nil, fuel, env, henv => by
      rw [denoteArgs']
      exact ⟨fun vs h => by cases h; trivial, henv⟩
  | _, _, _, _, .cons he hes, fuel, env, henv => by
      have h1 := SpTy.sound hW hbi he fuel env henv
      rw [denoteArgs'_cons, stateM_bind_apply]
      generalize denote' bi fuel _ env = r at h1 ⊢
      obtain ⟨ho, hs⟩ := h1
      rcases r with ⟨o, s⟩
      cases o with
      | val v =>
        rcases OutW.val_cases hW ho with ⟨hv, hc⟩ | ⟨b, w, rfl, -⟩
        · dsimp only
          rw [argsThen_val hc, stateM_bind_apply]
          have h2 := SpTyList.sound hW hbi hes fuel s hs
          generalize denoteArgs' bi fuel _ s = ra at h2 ⊢
          obtain ⟨hvs, hs2⟩ := h2
          rcases ra with ⟨_ | rs, s2⟩
          · exact ⟨fun vs h => (by cases h), hs2⟩
          · refine ⟨fun vs h => ?_, hs2⟩
            cases h
            exact ⟨hv, hvs rs rfl⟩
        · exact ⟨fun vs h => (by cases h), hs⟩
      | err m => exact ⟨fun vs h => (by cases h), hs⟩
      | _ => exact ho.elim
end

/-- On a typed expression the spine reading `denoteSpine` is `denote'`: a typed `let`
    binds no closure. -/
theorem SpTy.denoteSpine_eq : {Γ : TyEnv} → {E : Value → Prop} → {e : ImpExpr} →
    {τ : ImpType} → SpTy W S Γ E e τ → ∀ (bi : Builtins) (fuel : Nat),
      denoteSpine bi fuel e = denote' bi fuel e
  | _, _, _, _, @SpTy.letBind _ _ _ _ _ v _ _ _ hv _ hb, bi, fuel => by
      cases v with
      | lam ps body => cases hv
      | _ => rw [denote'_letBind, ← SpTy.denoteSpine_eq hb bi fuel]; rfl
  | _, _, _, _, .seq _ hb, bi, fuel => by
      rw [denote'_seq, ← SpTy.denoteSpine_eq hb bi fuel]; rfl
  | _, _, _, _, .lit _, _, _ => rfl
  | _, _, _, _, .var _, _, _ => rfl
  | _, _, _, _, .app _ _, _, _ => rfl
  | _, _, _, _, .tuple _ _, _, _ => rfl
  | _, _, _, _, .proj _ _, _, _ => rfl
  | _, _, _, _, .ifThenElse _ _ _, _, _ => rfl
  | _, _, _, _, .unitVal _, _, _ => rfl
  | _, _, _, _, .typeAscription _, _, _ => rfl
  | _, _, _, _, .forFold _ _ _ _ _ _, _, _ => rfl
  | _, _, _, _, .forFoldRev _ _ _ _ _ _, _, _ => rfl
  | _, _, _, _, .whileFold _ _ _, _, _ => rfl
  | _, _, _, _, .forFoldReturn _ _ _ _ _ _, _, _ => rfl
  | _, _, _, _, .forFoldRevReturn _ _ _ _ _ _, _, _ => rfl
  | _, _, _, _, .whileFoldReturn _ _ _, _, _ => rfl
  | _, _, _, _, .cfBreak _ _, _, _ => rfl
  | _, _, _, _, .cfContinue _ _, _, _ => rfl
  | _, _, _, _, .cfBreakContinue _ _, _, _ => rfl

/-- **Result type of a function body.**  A function body of result type `T`, typed with the
    early returns of `retEsc`, run by `denoteSpine` from an environment typed by `Γ` to a
    value `v`, returns a value of type `T` or an early return `Break u` carrying a value of
    type `T`; its exit environment is typed by `Γ`. -/
theorem SpTy.spine_result (hW : NoCF W) (hbi : RespectW W S bi) {Γ : TyEnv} {T : ImpType}
    {e : ImpExpr} (h : SpTy W S Γ (retEsc W T) e T) {fuel : Nat} {env env' : Env} {v : Value}
    (henv : EnvW W Γ env) (hrun : (denoteSpine bi fuel e).run env = (.val v, env')) :
    (W T v ∨ ∃ u, v = .controlFlow true u ∧ W T u) ∧ EnvW W Γ env' := by
  have h1 := SpTy.sound hW hbi h fuel env henv
  rw [← SpTy.denoteSpine_eq h bi fuel] at h1
  have hr : denoteSpine bi fuel e env = (.val v, env') := hrun
  rw [hr] at h1
  obtain ⟨ho, hs⟩ := h1
  refine ⟨?_, hs⟩
  rcases ho with ho | ⟨-, ho⟩
  · exact Or.inl ho
  · exact Or.inr ho

theorem stripRet_of_isControlFlow {v : Value} (h : v.isControlFlow = false) :
    stripRet v = v := by
  cases v <;> first | rfl | simp [Value.isControlFlow] at h

/-- A function body of result type `T` run by `denoteSpine` to a value `v` returns, after
    its early-return tag is removed, a value of type `T`. -/
theorem SpTy.spine_stripRet (hW : NoCF W) (hbi : RespectW W S bi) {Γ : TyEnv} {T : ImpType}
    {e : ImpExpr} (h : SpTy W S Γ (retEsc W T) e T) {fuel : Nat} {env env' : Env} {v : Value}
    (henv : EnvW W Γ env) (hrun : (denoteSpine bi fuel e).run env = (.val v, env')) :
    W T (stripRet v) := by
  rcases (SpTy.spine_result hW hbi h henv hrun).1 with hv | ⟨u, rfl, hu⟩
  · rw [stripRet_of_isControlFlow (hW _ _ hv)]; exact hv
  · exact hu

end Soundness

end CatCrypt.Hax.TExprTypingSpine
