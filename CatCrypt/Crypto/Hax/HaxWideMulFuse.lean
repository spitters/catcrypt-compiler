/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Phase.Monomorphise
public import HaxLean.TExpr
public import CatCrypt.Crypto.Hax.HaxToLowCTWordOps
public import HaxAscent.Ascent.TableCongr

/-!
# The high word of the widening multiply as one word call, in every position

Rust computes the high word of the `64 × 64 → 128` product of two `u64` values as
`((a as u128) * (b as u128) >> 64) as u64`, which hax extracts as the nested calls
`mulHiChain a b`:

```
cast#64 (Shr#128 (Mul (cast#128 a) (cast#128 b)) 64)
```

The typed front holds every scalar in one `64`-bit word, so it cannot hold the `128`-bit
intermediates of this chain. The pass `fuseMulHi` replaces each occurrence of the chain on
two variables, in any position of an expression, by the single word call `mulhi#64 a b`
(`mulHiCallName`), which the scalarisation of the typed exit front lowers to `SMulHiU`.
`fuseMulHiT` is the same pass on typed expressions; it keeps every type and erases to
`fuseMulHi` (`erase_fuseMulHiT`). `fuseMulHiIdiom` (`HaxToLowCTWordOps`) rewrites the
right-hand sides of the program spine only, and its value theorem holds per binding under
a range condition on the operands.

The chain and the word call read their arguments from the environment and change no
variable. Under a builtin table in which the four calls of the chain compute the value
of `mulhi#64` on every pair of values that are not control-flow values, refusing the same
pairs (`MulHiLaw`), the two expressions have the same run up to the text of an error
(`denote'_mulHi`), and so does every expression and its image under the pass
(`denote'_fuseMulHi`), with no condition on the values the program computes.

## Main definitions

* `mulHiOf` — the two variables of the chain `mulHiChain (.var a) (.var b)`.
* `fuseMulHi`, `fuseMulHiT` — the pass on untyped and on typed expressions.
* `mulHiChainVal`, `MulHiLaw` — the value of the chain under a table, and the law that
  it is the value of `mulhi#64`.
* `FlatRun` — a run that leaves the environment unchanged and ends in the value or
  error given by an optional value.
* `wideStepB`, `wideFreeB` — the `128`-bit steps of the chain, and the Boolean check that
  an expression calls none of them.

## Main results

* `mulHiOf_eq_some`, `mulHiOf_mulHiChain` — an expression is recognised exactly when it is
  the chain on two variables.
* `flatRun_var`, `flatRun_lit`, `flatRun_app` — the runs of variables, literals and calls
  on such runs.
* `denote'_mulHi` — under `MulHiLaw`, the word call runs as the chain.
* `denote'_fuseMulHi` — under `MulHiLaw`, every expression runs as its image under the
  pass, up to the text of an error.
* `erase_fuseMulHiT` — the typed pass erases to the untyped pass.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.WideMul

open _root_.Hax
open _root_.Hax.Monomorphise (ErrEq ErrEq.refl ErrEq.bind ErrEq.bindU ErrEq.pure_err
  ErrEq.bind_eq eraseErr run_bind forLoop'_errEq forLoopRev'_errEq forLoopOrig'_errEq
  forLoopRevOrig'_errEq forLoop'Return_errEq forLoopRev'Return_errEq whileOrig'_errEq
  while'_errEq while'Return_errEq)

/-! ## 1. The chain and the pass -/

/-- The two variables of an expression that is the chain `mulHiChain (.var a) (.var b)`, and
    `none` for every other expression. -/
def mulHiOf (e : ImpExpr) : Option (String × String) :=
  match e with
  | .app f [.app g [.app m [.app c₁ [.var a], .app c₂ [.var b]], .lit (.int k)]] =>
      if f = "cast#64" ∧ g = "Shr#128" ∧ m = "Mul" ∧ c₁ = "cast#128" ∧ c₂ = "cast#128" ∧ k = 64
      then some (a, b) else none
  | _ => none

theorem mulHiOf_eq_some {e : ImpExpr} {a b : String} (h : mulHiOf e = some (a, b)) :
    e = mulHiChain (.var a) (.var b) := by
  unfold mulHiOf at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
      cases h
      rfl
    · cases h
  · cases h

theorem mulHiOf_mulHiChain (a b : String) : mulHiOf (mulHiChain (.var a) (.var b)) = some (a, b) := by
  simp [mulHiOf, mulHiChain]

/-- **The pass.** Every occurrence of the chain `mulHiChain (.var a) (.var b)` becomes the
    word call `mulhi#64 a b`; every other node is kept. -/
def fuseMulHi : ImpExpr → ImpExpr
  | .lit v => .lit v
  | .var n => .var n
  | .unitVal => .unitVal
  | .continue_ => .continue_
  | .break_ none => .break_ none
  | .break_ (some e) => .break_ (some (fuseMulHi e))
  | .lam ps body => .lam ps (fuseMulHi body)
  | .app f args =>
      match mulHiOf (.app f args) with
      | some (a, b) => .app mulHiCallName [.var a, .var b]
      | none => .app f (mapExpr args)
  | .letBind n v body => .letBind n (fuseMulHi v) (fuseMulHi body)
  | .seq a b => .seq (fuseMulHi a) (fuseMulHi b)
  | .ifThenElse c t e => .ifThenElse (fuseMulHi c) (fuseMulHi t) (fuseMulHi e)
  | .tuple es => .tuple (mapExpr es)
  | .proj e i => .proj (fuseMulHi e) i
  | .match_ scrut arms => .match_ (fuseMulHi scrut) (mapArms arms)
  | .borrow e => .borrow (fuseMulHi e)
  | .deref e => .deref (fuseMulHi e)
  | .assign n rhs => .assign n (fuseMulHi rhs)
  | .forLoop v lo hi body => .forLoop v (fuseMulHi lo) (fuseMulHi hi) (fuseMulHi body)
  | .forLoopRev v lo hi body => .forLoopRev v (fuseMulHi lo) (fuseMulHi hi) (fuseMulHi body)
  | .whileLoop c body => .whileLoop (fuseMulHi c) (fuseMulHi body)
  | .earlyReturn e => .earlyReturn (fuseMulHi e)
  | .questionMark e => .questionMark (fuseMulHi e)
  | .forFold v lo hi body => .forFold v (fuseMulHi lo) (fuseMulHi hi) (fuseMulHi body)
  | .forFoldRev v lo hi body => .forFoldRev v (fuseMulHi lo) (fuseMulHi hi) (fuseMulHi body)
  | .whileFold c body => .whileFold (fuseMulHi c) (fuseMulHi body)
  | .forFoldReturn v lo hi body =>
      .forFoldReturn v (fuseMulHi lo) (fuseMulHi hi) (fuseMulHi body)
  | .forFoldRevReturn v lo hi body =>
      .forFoldRevReturn v (fuseMulHi lo) (fuseMulHi hi) (fuseMulHi body)
  | .whileFoldReturn c body => .whileFoldReturn (fuseMulHi c) (fuseMulHi body)
  | .cfBreak e => .cfBreak (fuseMulHi e)
  | .cfContinue e => .cfContinue (fuseMulHi e)
  | .cfBreakContinue e => .cfBreakContinue (fuseMulHi e)
  | .typeAscription e ty => .typeAscription (fuseMulHi e) ty
where
  /-- `fuseMulHi` on every expression of a list. -/
  mapExpr : List ImpExpr → List ImpExpr
    | [] => []
    | e :: es => fuseMulHi e :: mapExpr es
  /-- `fuseMulHi` on the body of every match arm. -/
  mapArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
    | [] => []
    | (p, e) :: rest => (p, fuseMulHi e) :: mapArms rest

@[simp] theorem fuseMulHi.mapExpr_eq (es : List ImpExpr) :
    fuseMulHi.mapExpr es = es.map fuseMulHi := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [fuseMulHi.mapExpr, ih]

@[simp] theorem fuseMulHi.mapArms_eq (arms : List (ImpPat × ImpExpr)) :
    fuseMulHi.mapArms arms = arms.map fun (p, e) => (p, fuseMulHi e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [fuseMulHi.mapArms, ih]

/-- The `128`-bit steps of the chain: `Mul`, `Shr#128` and `cast#128`. -/
def wideStepB (f : String) : Bool := f == "Mul" || f == "Shr#128" || f == "cast#128"

/-- **The check.** No call of `e`, closures included, is a `128`-bit step of the chain. On
    the output of `fuseMulHi` it holds when every such step of the input was part of a chain
    on two variables. -/
def wideFreeB (e : ImpExpr) : Bool := _root_.Hax.Ascent.callsOK (fun f => !wideStepB f) e

theorem fuseMulHi_app (f : String) (args : List ImpExpr) :
    fuseMulHi (.app f args) =
      match mulHiOf (.app f args) with
      | some (a, b) => .app mulHiCallName [.var a, .var b]
      | none => .app f (args.map fuseMulHi) := by
  rw [fuseMulHi, fuseMulHi.mapExpr_eq]

/-! ## 2. Runs that leave the environment unchanged -/

/-- The outcome an optional value stands for: the value, or an error. -/
def optOut : Option Value → Outcome
  | some v => .val v
  | none => .err ""

/-- A value that is not a control-flow value. -/
def nonCF (v : Value) : Option Value := if v.isControlFlow then none else some v

/-- The argument list `denoteArgs'` collects from the optional values of its arguments:
    `none` when one of them is `none` or a control-flow value. -/
def argsOpt : List (Option Value) → Option (List Value)
  | [] => some []
  | x :: xs => (x.bind nonCF).bind fun v => (argsOpt xs).map (v :: ·)

/-- The run of `e` from `ρ` leaves `ρ` unchanged and ends, up to the text of an error, in
    the outcome `optOut x`. -/
def FlatRun (bi : Builtins) (fuel : Nat) (e : ImpExpr) (ρ : Env) (x : Option Value) : Prop :=
  ∃ o, (denote' bi fuel e).run ρ = (o, ρ) ∧ eraseErr o = optOut x

/-- `FlatRun` for each expression of a list, with the optional values of a list. -/
def FlatRuns (bi : Builtins) (fuel : Nat) (ρ : Env) :
    List ImpExpr → List (Option Value) → Prop
  | [], [] => True
  | e :: es, x :: xs => FlatRun bi fuel e ρ x ∧ FlatRuns bi fuel ρ es xs
  | _, _ => False

theorem flatRun_var (bi : Builtins) (fuel : Nat) (x : String) (ρ : Env) :
    FlatRun bi fuel (.var x) ρ (ρ x) := by
  simp only [FlatRun, denote']
  rcases h : ρ x with _ | v
  · exact ⟨_, by simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, h]; rfl, rfl⟩
  · exact ⟨_, by simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, h]; rfl, rfl⟩

theorem flatRun_lit (bi : Builtins) (fuel : Nat) (l : ImpLit) (ρ : Env) :
    FlatRun bi fuel (.lit l) ρ (some (Value.ofLit l)) :=
  ⟨_, by simp only [denote']; rfl, rfl⟩

/-- The arguments of `FlatRuns` are collected into `argsOpt` of their values, with the
    environment unchanged. -/
theorem run_args (bi : Builtins) (fuel : Nat) (ρ : Env) :
    ∀ (es : List ImpExpr) (xs : List (Option Value)), FlatRuns bi fuel ρ es xs →
      (denoteArgs' bi fuel es).run ρ = (argsOpt xs, ρ)
  | [], [], _ => by rw [denoteArgs']; rfl
  | e :: es, x :: xs, ⟨⟨o, ho, he⟩, hr⟩ => by
    rw [denoteArgs']
    show ((denote' bi fuel e >>= _).run ρ) = _
    rw [run_bind, ho]
    have ih : denoteArgs' bi fuel es ρ = (argsOpt xs, ρ) := run_args bi fuel ρ es xs hr
    rcases x with _ | v
    · rcases o with w | _ | _ | _ | _ <;> simp [optOut, eraseErr] at he
      all_goals rfl
    · rcases o with w | _ | _ | _ | _ <;> simp [optOut, eraseErr] at he
      subst he
      cases w
      all_goals first
        | rfl
        | (show (Option.map _ (denoteArgs' bi fuel es ρ).1, (denoteArgs' bi fuel es ρ).2) = _
           rw [ih]; rfl)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem flatRun_app (bi : Builtins) (fuel : Nat) (ρ : Env) (f : String) (es : List ImpExpr)
    (xs : List (Option Value)) (h : FlatRuns bi fuel ρ es xs) :
    FlatRun bi fuel (.app f es) ρ ((argsOpt xs).bind (bi f)) := by
  simp only [FlatRun, denote']
  rw [denoteApp']
  show ∃ o, ((denoteArgs' bi fuel es >>= _).run ρ) = _ ∧ _
  rw [run_bind, run_args bi fuel ρ es xs h]
  rcases argsOpt xs with _ | vs
  · exact ⟨_, rfl, rfl⟩
  · simp only [Option.bind]
    rcases bi f vs with _ | r
    · exact ⟨_, rfl, rfl⟩
    · exact ⟨_, rfl, rfl⟩

theorem flatRun_app1 {bi : Builtins} {fuel : Nat} {ρ : Env} (f : String) {e : ImpExpr}
    {x : Option Value} (h : FlatRun bi fuel e ρ x) :
    FlatRun bi fuel (.app f [e]) ρ ((argsOpt [x]).bind (bi f)) :=
  flatRun_app bi fuel ρ f [e] [x] (by simp only [FlatRuns]; exact ⟨h, trivial⟩)

theorem flatRun_app2 {bi : Builtins} {fuel : Nat} {ρ : Env} (f : String) {e₁ e₂ : ImpExpr}
    {x₁ x₂ : Option Value} (h₁ : FlatRun bi fuel e₁ ρ x₁) (h₂ : FlatRun bi fuel e₂ ρ x₂) :
    FlatRun bi fuel (.app f [e₁, e₂]) ρ ((argsOpt [x₁, x₂]).bind (bi f)) :=
  flatRun_app bi fuel ρ f [e₁, e₂] [x₁, x₂] (by simp only [FlatRuns]; exact ⟨h₁, h₂, trivial⟩)

/-- Two expressions whose runs from every environment are `FlatRun` with the same
    optional value agree up to the text of an error. -/
theorem FlatRun.errEq {bi : Builtins} {fuel : Nat} {e₁ e₂ : ImpExpr}
    (h : ∀ ρ, ∃ x, FlatRun bi fuel e₁ ρ x ∧ FlatRun bi fuel e₂ ρ x) :
    ErrEq (denote' bi fuel e₁) (denote' bi fuel e₂) := by
  intro ρ
  obtain ⟨x, ⟨o₁, h₁, he₁⟩, ⟨o₂, h₂, he₂⟩⟩ := h ρ
  rw [h₁, h₂]
  exact ⟨rfl, he₁.trans he₂.symm⟩

/-! ## 3. The law and the chain -/

/-- The value of the chain under the table `bi` on the argument values `va`, `vb`: the four
    calls `cast#128`, `cast#128`, `Mul`, `Shr#128` (with `64`) and `cast#64`, each argument
    refused when it is a control-flow value. -/
def mulHiChainVal (bi : Builtins) (va vb : Value) : Option Value :=
  (argsOpt [(argsOpt [(argsOpt [bi "cast#128" [va], bi "cast#128" [vb]]).bind (bi "Mul"),
    some (.int 64)]).bind (bi "Shr#128")]).bind (bi "cast#64")

/-- **The law of the widening multiply.** On every pair of values that are not
    control-flow values, the chain computes under `bi` the value of `mulhi#64`, both
    refusing the same pairs. -/
def MulHiLaw (bi : Builtins) : Prop :=
  ∀ va vb : Value, va.isControlFlow = false → vb.isControlFlow = false →
    mulHiChainVal bi va vb = bi mulHiCallName [va, vb]

theorem mulHi_flat {bi : Builtins} (hL : MulHiLaw bi) (xa xb : Option Value) :
    (argsOpt [(argsOpt [(argsOpt [(argsOpt [xa]).bind (bi "cast#128"),
      (argsOpt [xb]).bind (bi "cast#128")]).bind (bi "Mul"),
      some (Value.ofLit (.int 64))]).bind (bi "Shr#128")]).bind (bi "cast#64") =
      (argsOpt [xa, xb]).bind (bi mulHiCallName) := by
  rcases xa with _ | va
  · rfl
  rcases xb with _ | vb
  · cases (nonCF va) <;> simp [argsOpt]
  cases hca : va.isControlFlow
  · cases hcb : vb.isControlFlow
    · have := hL va vb hca hcb
      simp only [mulHiChainVal] at this
      simpa [argsOpt, nonCF, hca, hcb, Value.ofLit] using this
    · simp [argsOpt, nonCF, hca, hcb]
  · simp [argsOpt, nonCF, hca]

/-- **The word call runs as the chain.** Under `MulHiLaw bi`, `mulhi#64 a b` and the chain
    `mulHiChain (.var a) (.var b)` agree up to the text of an error. -/
theorem denote'_mulHi {bi : Builtins} (hL : MulHiLaw bi) (a b : String) (fuel : Nat) :
    ErrEq (denote' bi fuel (.app mulHiCallName [.var a, .var b]))
      (denote' bi fuel (mulHiChain (.var a) (.var b))) := by
  apply FlatRun.errEq
  intro ρ
  have hva := flatRun_var bi fuel a ρ
  have hvb := flatRun_var bi fuel b ρ
  have h5 := flatRun_app1 "cast#64" (flatRun_app2 "Shr#128"
    (flatRun_app2 "Mul" (flatRun_app1 "cast#128" hva) (flatRun_app1 "cast#128" hvb))
    (flatRun_lit bi fuel (.int 64) ρ))
  rw [mulHi_flat hL] at h5
  exact ⟨_, flatRun_app2 mulHiCallName hva hvb, h5⟩

/-! ## 4. The pass preserves the run -/

section Pass

variable {bi : Builtins}

theorem denoteArgs'_fuseMulHi (args : List ImpExpr)
    (ih : ∀ a, a ∈ args → ∀ fuel, ErrEq (denote' bi fuel (fuseMulHi a)) (denote' bi fuel a))
    (fuel : Nat) :
    denoteArgs' bi fuel (args.map fuseMulHi) = denoteArgs' bi fuel args := by
  induction args with
  | nil => simp only [List.map_nil, denoteArgs']
  | cons a as iha =>
    simp only [List.map_cons, denoteArgs', iha (fun b hb => ih b (List.mem_cons_of_mem a hb))]
    exact ErrEq.bind_eq (ih a List.mem_cons_self fuel) (fun _ _ => rfl)

theorem denoteMatchArms'_fuseMulHi (arms : List (ImpPat × ImpExpr))
    (ih : ∀ pa, pa ∈ arms → ∀ fuel,
      ErrEq (denote' bi fuel (fuseMulHi pa.2)) (denote' bi fuel pa.2))
    (fuel : Nat) (v : Value) :
    ErrEq (denoteMatchArms' bi fuel v (arms.map fun (p, e) => (p, fuseMulHi e)))
      (denoteMatchArms' bi fuel v arms) := by
  induction arms with
  | nil => simp only [List.map_nil, denoteMatchArms']; exact ErrEq.refl _
  | cons pa rest iha =>
    obtain ⟨p, e⟩ := pa
    have he := ih (p, e) List.mem_cons_self fuel
    have hr := iha (fun b hb => ih b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, denoteMatchArms']
    refine ErrEq.bindU _ fun env => ?_
    split
    · exact ErrEq.bindU _ fun _ => he
    · exact hr

/-- **The pass preserves the run.** Under `MulHiLaw bi`, every expression and its image
    under `fuseMulHi` agree up to the text of an error, at every fuel. -/
theorem denote'_fuseMulHi (hL : MulHiLaw bi) (e : ImpExpr) : ∀ fuel,
    ErrEq (denote' bi fuel (fuseMulHi e)) (denote' bi fuel e) := by
  induction e using ImpExpr.ind with
  | app f args ih =>
    intro fuel
    rw [fuseMulHi_app]
    rcases hm : mulHiOf (.app f args) with _ | ⟨a, b⟩
    · simp only [denote']
      unfold denoteApp'
      rw [denoteArgs'_fuseMulHi args ih fuel]
      exact ErrEq.refl _
    · simp only
      rw [mulHiOf_eq_some hm]
      exact denote'_mulHi hL a b fuel
  | tuple es ih =>
    intro fuel
    simp only [fuseMulHi, fuseMulHi.mapExpr_eq, denote', denoteArgs'_fuseMulHi es ih fuel]
    exact ErrEq.refl _
  | match_ scrut arms ihs iha =>
    intro fuel
    have ha := denoteMatchArms'_fuseMulHi arms iha fuel
    simp only [fuseMulHi, fuseMulHi.mapArms_eq, denote']
    errEq_step
  | forLoop v lo hi body ihl ihh ihb =>
    intro fuel
    have := forLoopOrig'_errEq (v := v) ihb fuel
    simp only [fuseMulHi, denote']
    errEq_step
  | forLoopRev v lo hi body ihl ihh ihb =>
    intro fuel
    have := forLoopRevOrig'_errEq (v := v) ihb fuel
    simp only [fuseMulHi, denote']
    errEq_step
  | whileLoop c body ihc ihb =>
    intro fuel
    simp only [fuseMulHi, denote']
    exact whileOrig'_errEq ihc ihb fuel
  | forFold v lo hi body ihl ihh ihb =>
    intro fuel
    have := forLoop'_errEq (v := v) ihb fuel
    simp only [fuseMulHi, denote']
    errEq_step
  | forFoldRev v lo hi body ihl ihh ihb =>
    intro fuel
    have := forLoopRev'_errEq (v := v) ihb fuel
    simp only [fuseMulHi, denote']
    errEq_step
  | whileFold c body ihc ihb =>
    intro fuel
    simp only [fuseMulHi, denote']
    exact while'_errEq ihc ihb fuel
  | forFoldReturn v lo hi body ihl ihh ihb =>
    intro fuel
    have := forLoop'Return_errEq (v := v) ihb fuel
    simp only [fuseMulHi, denote']
    errEq_step
  | forFoldRevReturn v lo hi body ihl ihh ihb =>
    intro fuel
    have := forLoopRev'Return_errEq (v := v) ihb fuel
    simp only [fuseMulHi, denote']
    errEq_step
  | whileFoldReturn c body ihc ihb =>
    intro fuel
    simp only [fuseMulHi, denote']
    exact while'Return_errEq ihc ihb fuel
  | _ => intro fuel; simp only [fuseMulHi, denote']; errEq_step

end Pass

/-! ## 5. The pass on typed expressions -/

/-- **The typed pass.** Every call whose erasure is the chain `mulHiChain (.var a) (.var b)`
    becomes the word call `mulhi#64 a b` at the call's type, its two arguments variables of
    that type; every other node and every type is kept. -/
def fuseMulHiT : TExpr → TExpr
  | .mk (.lit v) ty => .mk (.lit v) ty
  | .mk (.var n) ty => .mk (.var n) ty
  | .mk (.letBind n v b) ty => .mk (.letBind n (fuseMulHiT v) (fuseMulHiT b)) ty
  | .mk (.lam ps b) ty => .mk (.lam ps (fuseMulHiT b)) ty
  | .mk (.app f args) ty =>
      match mulHiOf (.app f (args.map TExpr.erase)) with
      | some (a, b) => .mk (.app mulHiCallName [.mk (.var a) ty, .mk (.var b) ty]) ty
      | none => .mk (.app f (mapList args)) ty
  | .mk (.tuple es) ty => .mk (.tuple (mapList es)) ty
  | .mk (.proj e i) ty => .mk (.proj (fuseMulHiT e) i) ty
  | .mk (.ifThenElse c t e) ty =>
      .mk (.ifThenElse (fuseMulHiT c) (fuseMulHiT t) (fuseMulHiT e)) ty
  | .mk (.match_ s arms) ty => .mk (.match_ (fuseMulHiT s) (mapArms arms)) ty
  | .mk .unitVal ty => .mk .unitVal ty
  | .mk (.seq a b) ty => .mk (.seq (fuseMulHiT a) (fuseMulHiT b)) ty
  | .mk (.borrow e) ty => .mk (.borrow (fuseMulHiT e)) ty
  | .mk (.deref e) ty => .mk (.deref (fuseMulHiT e)) ty
  | .mk (.assign n r) ty => .mk (.assign n (fuseMulHiT r)) ty
  | .mk (.forLoop v lo hi b) ty =>
      .mk (.forLoop v (fuseMulHiT lo) (fuseMulHiT hi) (fuseMulHiT b)) ty
  | .mk (.forLoopRev v lo hi b) ty =>
      .mk (.forLoopRev v (fuseMulHiT lo) (fuseMulHiT hi) (fuseMulHiT b)) ty
  | .mk (.whileLoop c b) ty => .mk (.whileLoop (fuseMulHiT c) (fuseMulHiT b)) ty
  | .mk (.break_ none) ty => .mk (.break_ none) ty
  | .mk (.break_ (some e)) ty => .mk (.break_ (some (fuseMulHiT e))) ty
  | .mk .continue_ ty => .mk .continue_ ty
  | .mk (.earlyReturn e) ty => .mk (.earlyReturn (fuseMulHiT e)) ty
  | .mk (.questionMark e) ty => .mk (.questionMark (fuseMulHiT e)) ty
  | .mk (.forFold v lo hi b) ty =>
      .mk (.forFold v (fuseMulHiT lo) (fuseMulHiT hi) (fuseMulHiT b)) ty
  | .mk (.forFoldRev v lo hi b) ty =>
      .mk (.forFoldRev v (fuseMulHiT lo) (fuseMulHiT hi) (fuseMulHiT b)) ty
  | .mk (.whileFold c b) ty => .mk (.whileFold (fuseMulHiT c) (fuseMulHiT b)) ty
  | .mk (.forFoldReturn v lo hi b) ty =>
      .mk (.forFoldReturn v (fuseMulHiT lo) (fuseMulHiT hi) (fuseMulHiT b)) ty
  | .mk (.forFoldRevReturn v lo hi b) ty =>
      .mk (.forFoldRevReturn v (fuseMulHiT lo) (fuseMulHiT hi) (fuseMulHiT b)) ty
  | .mk (.whileFoldReturn c b) ty => .mk (.whileFoldReturn (fuseMulHiT c) (fuseMulHiT b)) ty
  | .mk (.cfBreak e) ty => .mk (.cfBreak (fuseMulHiT e)) ty
  | .mk (.cfContinue e) ty => .mk (.cfContinue (fuseMulHiT e)) ty
  | .mk (.cfBreakContinue e) ty => .mk (.cfBreakContinue (fuseMulHiT e)) ty
  | .mk (.ann e) ty => .mk (.ann (fuseMulHiT e)) ty
  | .mk (.namedProj n e) ty => .mk (.namedProj n (fuseMulHiT e)) ty
where
  /-- `fuseMulHiT` on every expression of a list. -/
  mapList : List TExpr → List TExpr
    | [] => []
    | e :: es => fuseMulHiT e :: mapList es
  /-- `fuseMulHiT` on every arm body. -/
  mapArms : List (ImpPat × TExpr) → List (ImpPat × TExpr)
    | [] => []
    | (p, e) :: rest => (p, fuseMulHiT e) :: mapArms rest

@[simp] theorem fuseMulHiT.mapList_eq (es : List TExpr) :
    fuseMulHiT.mapList es = es.map fuseMulHiT := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [fuseMulHiT.mapList, ih]

@[simp] theorem fuseMulHiT.mapArms_eq (arms : List (ImpPat × TExpr)) :
    fuseMulHiT.mapArms arms = arms.map fun (p, e) => (p, fuseMulHiT e) := by
  induction arms with
  | nil => rfl
  | cons pa arms ih => obtain ⟨p, e⟩ := pa; simp [fuseMulHiT.mapArms, ih]

/-- A projection call `.0` is not the chain. -/
theorem mulHiOf_proj0 (x : ImpExpr) : mulHiOf (.app ".0" [x]) = none := by
  unfold mulHiOf
  split
  · rename_i heq
    simp only [ImpExpr.app.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    simp
  · rfl

/-- **The typed pass erases to the untyped pass.** -/
theorem erase_fuseMulHiT (te : TExpr) : (fuseMulHiT te).erase = fuseMulHi te.erase := by
  induction te using TExpr.ind with
  | app ty f args ih =>
    simp only [TExpr.erase, TExpr.eraseList_eq, fuseMulHi_app]
    rw [fuseMulHiT]
    rcases hm : mulHiOf (.app f (args.map TExpr.erase)) with _ | ⟨a, b⟩
    · simp only [fuseMulHiT.mapList_eq, TExpr.erase, TExpr.eraseList_eq, List.map_map]
      congr 1
      apply List.map_congr_left
      intro x hx
      exact ih x hx
    · simp [TExpr.erase]
  | tuple ty es ih =>
    simp only [fuseMulHiT, TExpr.erase, TExpr.eraseList_eq, fuseMulHiT.mapList_eq, fuseMulHi,
      fuseMulHi.mapExpr_eq, List.map_map]
    congr 1
    apply List.map_congr_left
    intro x hx
    exact ih x hx
  | match_ ty s arms ihs iha =>
    simp only [fuseMulHiT, TExpr.erase, TExpr.eraseArms_eq, fuseMulHiT.mapArms_eq, fuseMulHi,
      fuseMulHi.mapArms_eq, List.map_map, ihs]
    congr 1
    apply List.map_congr_left
    rintro ⟨p, e⟩ hpe
    simp only [Function.comp, Prod.mk.injEq, true_and]
    exact iha (p, e) hpe
  | namedProj ty n e ih =>
    simp only [fuseMulHiT, TExpr.erase, fuseMulHi_app, mulHiOf_proj0, List.map_cons,
      List.map_nil, ih]
  | _ => simp_all [fuseMulHiT, TExpr.erase, fuseMulHi]

end CatCrypt.Crypto.Hax.WideMul
