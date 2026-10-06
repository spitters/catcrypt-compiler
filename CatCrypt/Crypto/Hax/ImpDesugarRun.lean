/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpDesugarIte
public import CatCrypt.Crypto.Hax.ImpDesugarRem
public import CatCrypt.Crypto.Hax.ImpDesugarTable

/-!
# Forward runs of the conditional and remainder desugarings

`ImpDesugarIte.desugarIte_denote` and `ImpDesugarRem.desugarRem_denote` relate two
successful runs. This module proves the run of the desugared form from the run of the
source.

A select evaluates both arms, so the arm the source does not run has to evaluate. The
condition is a typing of the speculatable expression at the two types `STy.word` (an integer
below `2^64`) and `STy.bit` (a Boolean), along a typing `Γ` of the variables that the
environment satisfies (`WordEnv`), at builtins whose renamed calls are defined on arguments
of the types of their signature (`TotalOn`). The check `iteOk` types every conditional the
pass replaces; it carries `Γ` through `letBind` and `seq` as `ImpDesugarRem.desugarRem`
carries its table of constants: a variable bound to a typed speculatable expression has its
type, and an expression that is not `pureForm` empties the typing.

The Barrett sequence is defined on operands below `2^64`. A builtin `Rem` that accepts a
wider operand runs where the sequence does not, so the forward lemma of the remainder pass
takes the hypothesis `RemWord`: `Rem` is defined on a first operand below `2^64` only.
`Hax.hax64Builtins` does not satisfy it.

## Main definitions

* `STy`, `STy.Holds` — the two types of speculatable expressions and their values.
* `SSig`, `TotalOn` — a signature of the renamed calls, and the builtins that are defined
  on arguments of the types of the signature.
* `WordEnv` — the environments that hold a value of its type at every typed variable.
* `specTy`, `specTys` — the type of a speculatable expression and of a list of arguments.
* `bindTy`, `seqTy`, `iteOk` — the typing after a `letBind` and after an expression in
  sequence, and the check of the conditional pass.
* `hax64WordSig` — the signature of the calls of `u64` code that are defined on all words.
* `entryTy` — the typing of the parameters of a function.
* `WordTotal`, `RemWord` — the hypotheses of the remainder pass on the builtins.

## Main results

* `specTy_runs` — the select form of a typed speculatable expression runs to a value of
  its type.
* `desugarIte_runs` — a source run to a value that is not a control-flow value is a run of
  the result of the conditional pass, to the same value and environment.
* `totalOn_hax64Builtins`, `totalOn_withSelect` — `TotalOn` at `Hax.hax64Builtins` and at a
  table with `select`.
* `wordEnv_entryTy` — an environment holding encodings at the parameters satisfies
  `WordEnv` at `entryTy`.
* `remForm_runs`, `remExpr_runs`, `desugarRem_runs` — the same for the remainder pass.
* `wordTotal_hax64Builtins`, `wordTotal_withSelect` — `WordTotal` at `Hax.hax64Builtins` and
  at a table with `select`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax.ImpDesugarRun

open _root_.Hax (ImpExpr ImpLit Value Env Outcome Builtins denote' denoteApp' denoteArgs')
open CatCrypt.Crypto.Hax.ImpDesugarIte
open CatCrypt.Crypto.Hax.ImpDesugarRem
open CatCrypt.Crypto.Hax.ImpToNF (withSelect withSelect_of_ne scalarBinOf scalarCmpOf
  scalarUnOf ScalarBin ScalarUn ScalarCmp hax64BinTable_sem hax64UnTable_sem hax64CmpTable_sem
  hax64BinTable_w hax64UnTable_w mem_of_find?_map orElse_none_eq EntryTyped enc)
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect (NfTy)

/-! ## 1. Runs of calls, bindings and sequences from the runs of their parts -/

/-- A list of arguments runs to values when its head runs to a value that is not a
    control-flow value and its tail runs to values from the environment the head leaves. -/
theorem denoteArgs'_cons_val {bi : Builtins} {fuel : Nat} {e : ImpExpr} {es : List ImpExpr}
    {env x y : Env} {u : Value} {vs : List Value}
    (h : denote' bi fuel e env = (.val u, x)) (hu : Plain u)
    (hr : denoteArgs' bi fuel es x = (some vs, y)) :
    denoteArgs' bi fuel (e :: es) env = (some (u :: vs), y) := by
  have key := denoteArgs'_cons_run bi fuel e es env
  rw [h] at key
  cases u
  case controlFlow k p => exact absurd rfl (hu k p)
  all_goals (simp only [hr] at key; exact key)

/-- A call runs to the value of the builtin on the values of its arguments. -/
theorem denote'_app_of {bi : Builtins} {fuel : Nat} {f : String} {args : List ImpExpr}
    {env e₁ : Env} {vals : List Value} {v : Value}
    (h : denoteArgs' bi fuel args env = (some vals, e₁)) (hb : bi f vals = some v) :
    denote' bi fuel (.app f args) env = (.val v, e₁) := by
  have key := denote'_app_run bi fuel f args env
  rw [h] at key
  simp only [hb] at key
  exact key

/-- A `letBind` runs as its body from the extended environment when its bound expression
    runs to a value that is not a control-flow value. -/
theorem denote'_letBind_of {bi : Builtins} {fuel : Nat} {n : String} {a b : ImpExpr}
    {env x : Env} {u : Value} {r : Outcome × Env}
    (h : denote' bi fuel a env = (.val u, x)) (hu : Plain u)
    (hb : denote' bi fuel b (Hax.Env.extend x n u) = r) :
    denote' bi fuel (.letBind n a b) env = r := by
  have key := Hax.denote'_letBind_run bi fuel n a b env
  rw [h] at key
  cases u
  case controlFlow k p => exact absurd rfl (hu k p)
  all_goals exact key.trans hb

/-- A `seq` runs as its second expression from the environment the first leaves when the
    first runs to a value that is not a control-flow value. -/
theorem denote'_seq_of {bi : Builtins} {fuel : Nat} {a b : ImpExpr}
    {env x : Env} {u : Value} {r : Outcome × Env}
    (h : denote' bi fuel a env = (.val u, x)) (hu : Plain u)
    (hb : denote' bi fuel b x = r) :
    denote' bi fuel (.seq a b) env = r := by
  have key := Hax.denote'_seq_run bi fuel a b env
  rw [h] at key
  cases u
  case controlFlow k p => exact absurd rfl (hu k p)
  all_goals exact key.trans hb

/-- An integer is not a control-flow value. -/
theorem plain_int (n : Int) : Plain (.int n) := fun _ _ h => by cases h

/-- A Boolean is not a control-flow value. -/
theorem plain_bool (k : Bool) : Plain (.bool k) := fun _ _ h => by cases h

/-- A call on two arguments that run to values in an environment they leave unchanged. -/
theorem app2_of {bi : Builtins} {fuel : Nat} {f : String} {a b : ImpExpr} {env : Env}
    {u₁ u₂ v : Value} (h1 : denote' bi fuel a env = (.val u₁, env)) (p1 : Plain u₁)
    (h2 : denote' bi fuel b env = (.val u₂, env)) (p2 : Plain u₂)
    (hb : bi f [u₁, u₂] = some v) :
    denote' bi fuel (.app f [a, b]) env = (.val v, env) :=
  denote'_app_of (denoteArgs'_cons_val h1 p1
    (denoteArgs'_cons_val h2 p2 (denoteArgs'_nil_run bi fuel env))) hb

/-! ## 2. Types of speculatable expressions -/

/-- The types of speculatable expressions: an integer below `2^64`, and a Boolean. -/
inductive STy where
  /-- An integer in `[0, 2^64)`. -/
  | word
  /-- A Boolean. -/
  | bit
  deriving DecidableEq, Repr

/-- The values of a type. -/
def STy.Holds : STy → Value → Prop
  | .word, v => ∃ a : Nat, a < 2 ^ 64 ∧ v = .int (a : Int)
  | .bit, v => ∃ k : Bool, v = .bool k

/-- A value of a type is not a control-flow value. -/
theorem STy.Holds.plain {τ : STy} {v : Value} (h : τ.Holds v) : Plain v := by
  intro k p hk
  subst hk
  cases τ with
  | word => obtain ⟨a, -, h⟩ := h; cases h
  | bit => obtain ⟨k', h⟩ := h; cases h

/-- A signature: the argument types and the result type of a call name. -/
abbrev SSig := String → Option (List STy × STy)

/-- **The renamed calls are total.** A name `g` the renaming `ρ` renames to, with the
    signature `sig g = (τs, τ)`, is defined on every list of values of the types `τs`, with
    a value of type `τ`. -/
def TotalOn (bi : Builtins) (ρ : String → Option String) (sig : SSig) : Prop :=
  ∀ f g, ρ f = some g → ∀ τs τ, sig g = some (τs, τ) → ∀ vals,
    List.Forall₂ STy.Holds τs vals → ∃ v, bi g vals = some v ∧ τ.Holds v

/-- The environment holds a value of its type at every variable `Γ` types. -/
def WordEnv (Γ : String → Option STy) (env : Env) : Prop :=
  ∀ x τ, Γ x = some τ → ∃ v, env x = some v ∧ τ.Holds v

/-- The type of a literal: an integer in `[0, 2^64)` is a word and a Boolean is a bit. -/
def litTy : ImpLit → Option STy
  | .int n => if 0 ≤ n ∧ n < 2 ^ 64 then some .word else none
  | .bool _ => some .bit
  | _ => none

/-- The value of a typed literal has its type. -/
theorem litTy_holds {l : ImpLit} {τ : STy} (h : litTy l = some τ) :
    τ.Holds (Value.ofLit l) := by
  cases l
  case int n =>
    simp only [litTy] at h
    split at h
    · rename_i hn
      cases h
      exact ⟨n.toNat, by omega, by rw [Int.toNat_of_nonneg hn.1]; rfl⟩
    · cases h
  case bool k =>
    simp only [litTy] at h
    cases h
    exact ⟨k, rfl⟩
  all_goals simp [litTy] at h

mutual
/-- The type of a speculatable expression along the renaming `ρ`, the signature `sig` and
    the typing `Γ` of the variables: a literal by `litTy`, a variable by `Γ`, a call of `f`
    with `ρ f = some g` by the signature of `g` at the types of its arguments, and a
    conditional with a Boolean condition and two arms of one type by that type. -/
def specTy (ρ : String → Option String) (sig : SSig) (Γ : String → Option STy) :
    ImpExpr → Option STy
  | .lit l => litTy l
  | .var x => Γ x
  | .app f args =>
      match ρ f, specTys ρ sig Γ args with
      | some g, some σs =>
          match sig g with
          | some (τs, τ) => if τs = σs then some τ else none
          | none => none
      | _, _ => none
  | .ifThenElse c a b =>
      match specTy ρ sig Γ c, specTy ρ sig Γ a, specTy ρ sig Γ b with
      | some .bit, some s, some t => if s = t then some s else none
      | _, _, _ => none
  | _ => none
/-- The types of a list of arguments. -/
def specTys (ρ : String → Option String) (sig : SSig) (Γ : String → Option STy) :
    List ImpExpr → Option (List STy)
  | [] => some []
  | e :: es =>
      match specTy ρ sig Γ e, specTys ρ sig Γ es with
      | some τ, some τs => some (τ :: τs)
      | _, _ => none
end

mutual
/-- **The select form of a typed speculatable expression runs.** In an environment that
    satisfies the typing, at builtins whose renamed calls are total, an expression of type
    `τ` has a select form, which runs to a value of type `τ` and leaves the environment
    unchanged. -/
theorem specTy_runs {bi : Builtins} {fuel : Nat} {ρ : String → Option String} {sig : SSig}
    {Γ : String → Option STy} {env : Env} (hsel : SelectSpec bi) (htot : TotalOn bi ρ sig)
    (hΓ : WordEnv Γ env) :
    ∀ (e : ImpExpr) (τ : STy), specTy ρ sig Γ e = some τ →
      ∃ e' v, specExpr ρ e = some e' ∧ denote' bi fuel e' env = (.val v, env) ∧ τ.Holds v
  | .lit l, τ, h => by
      unfold specTy at h
      exact ⟨.lit l, Value.ofLit l, by unfold specExpr; rfl, Hax.denote'_lit_run .., litTy_holds h⟩
  | .var x, τ, h => by
      unfold specTy at h
      obtain ⟨v, hx, hv⟩ := hΓ x τ h
      refine ⟨.var x, v, by unfold specExpr; rfl, ?_, hv⟩
      exact (Hax.denote'_var_run bi fuel x env).trans (by rw [hx])
  | .app f args, τ, h => by
      unfold specTy at h
      rcases hg : ρ f with _ | g <;> rcases ha : specTys ρ sig Γ args with _ | σs <;>
        rw [hg, ha] at h <;> try cases h
      dsimp only at h
      rcases hs : sig g with _ | ⟨τs, τ'⟩
      · rw [hs] at h; cases h
      · rw [hs] at h
        dsimp only at h
        split at h
        · rename_i heq
          cases h
          subst heq
          obtain ⟨as, vs, has, hrun, hty⟩ := specTys_runs hsel htot hΓ args _ ha
          obtain ⟨v, hb, hv⟩ := htot f g hg _ _ hs vs hty
          refine ⟨.app g as, v, ?_, denote'_app_of hrun hb, hv⟩
          unfold specExpr
          rw [hg, has]
        · cases h
  | .ifThenElse c a b, τ, h => by
      unfold specTy at h
      rcases hc : specTy ρ sig Γ c with _ | (_ | _) <;>
        rcases ha : specTy ρ sig Γ a with _ | ta <;>
        rcases hb : specTy ρ sig Γ b with _ | tb <;> rw [hc, ha, hb] at h <;>
        try cases h
      dsimp only at h
      split at h
      · rename_i heq
        cases h
        subst heq
        obtain ⟨c', vc, hc', hrc, k, rfl⟩ := specTy_runs hsel htot hΓ c _ hc
        obtain ⟨a', va, ha', hra, hva⟩ := specTy_runs hsel htot hΓ a _ ha
        obtain ⟨b', vb, hb', hrb, hvb⟩ := specTy_runs hsel htot hΓ b _ hb
        refine ⟨.app selectName [c', a', b'], if k then va else vb, ?_, ?_, ?_⟩
        · unfold specExpr
          rw [hc', ha', hb']
        · exact denote'_app_of (denoteArgs'_cons_val hrc (plain_bool k)
            (denoteArgs'_cons_val hra hva.plain (denoteArgs'_cons_val hrb hvb.plain
              (denoteArgs'_nil_run bi fuel env)))) (hsel k va vb)
        · cases k
          · exact hvb
          · exact hva
      · cases h
  | .letBind .., _, h | .lam .., _, h | .tuple .., _, h | .proj .., _, h
  | .match_ .., _, h | .unitVal, _, h | .seq .., _, h | .borrow .., _, h | .deref .., _, h
  | .assign .., _, h | .forLoop .., _, h | .forLoopRev .., _, h | .whileLoop .., _, h
  | .break_ .., _, h | .continue_, _, h | .earlyReturn .., _, h | .questionMark .., _, h
  | .forFold .., _, h | .forFoldRev .., _, h | .whileFold .., _, h
  | .forFoldReturn .., _, h | .forFoldRevReturn .., _, h | .whileFoldReturn .., _, h
  | .cfBreak .., _, h | .cfContinue .., _, h | .cfBreakContinue .., _, h
  | .typeAscription .., _, h => by simp [specTy] at h
/-- The list counterpart of `specTy_runs`. -/
theorem specTys_runs {bi : Builtins} {fuel : Nat} {ρ : String → Option String} {sig : SSig}
    {Γ : String → Option STy} {env : Env} (hsel : SelectSpec bi) (htot : TotalOn bi ρ sig)
    (hΓ : WordEnv Γ env) :
    ∀ (es : List ImpExpr) (σs : List STy), specTys ρ sig Γ es = some σs →
      ∃ es' vs, specArgs ρ es = some es' ∧ denoteArgs' bi fuel es' env = (some vs, env) ∧
        List.Forall₂ STy.Holds σs vs
  | [], σs, h => by
      unfold specTys at h
      cases h
      exact ⟨[], [], by unfold specArgs; rfl, denoteArgs'_nil_run bi fuel env, .nil⟩
  | e :: es, σs, h => by
      unfold specTys at h
      rcases he : specTy ρ sig Γ e with _ | τ <;> rcases hes : specTys ρ sig Γ es with _ | τs <;>
        rw [he, hes] at h <;> try (cases h; done)
      cases h
      obtain ⟨e', v, he', hr, hv⟩ := specTy_runs hsel htot hΓ e _ he
      obtain ⟨es', vs, hes', hrs, hvs⟩ := specTys_runs hsel htot hΓ es _ hes
      refine ⟨e' :: es', v :: vs, ?_, denoteArgs'_cons_val hr hv.plain hrs, .cons hv hvs⟩
      unfold specArgs
      rw [he', hes']
end

/-! ## 3. The conditional pass -/

/-- The typing after `let x = v`: `x` has the type of `v`, and every other entry is kept
    when `v` is `pureForm` and dropped otherwise. -/
def bindTy (ρ : String → Option String) (sig : SSig) (Γ : String → Option STy) (x : String)
    (v : ImpExpr) : String → Option STy :=
  fun y => if y = x then specTy ρ sig Γ v else if pureForm v then Γ y else none

/-- The typing after an expression in sequence: kept when the expression is `pureForm` and
    empty otherwise. -/
def seqTy (Γ : String → Option STy) (a : ImpExpr) : String → Option STy :=
  fun y => if pureForm a then Γ y else none

/-- **The check of the conditional pass.** Every conditional the pass replaces by its
    select form, reached through `letBind` and `seq`, is typed by `specTy` at the typing
    the bindings before it give. -/
def iteOk (ρ : String → Option String) (sig : SSig) : (String → Option STy) → ImpExpr → Bool
  | Γ, .letBind x v b => iteOk ρ sig Γ v && iteOk ρ sig (bindTy ρ sig Γ x v) b
  | Γ, .seq a b => iteOk ρ sig Γ a && iteOk ρ sig (seqTy Γ a) b
  | Γ, .ifThenElse c a b =>
      (specExpr ρ (.ifThenElse c a b)).isNone || (specTy ρ sig Γ (.ifThenElse c a b)).isSome
  | _, _ => true

/-- The typing after `let n = a` is satisfied by the environment the binding leaves. -/
theorem wordEnv_bindTy {bi : Builtins} {fuel : Nat} {ρ : String → Option String} {sig : SSig}
    (hsel : SelectSpec bi) (href : Refines bi ρ) (htot : TotalOn bi ρ sig)
    {Γ : String → Option STy} {n : String} {a : ImpExpr} {env x : Env} {u : Value}
    (hΓ : WordEnv Γ env) (h : denote' bi fuel a env = (.val u, x)) (hu : Plain u) :
    WordEnv (bindTy ρ sig Γ n a) (Hax.Env.extend x n u) := by
  intro y τ hy
  unfold bindTy at hy
  by_cases hyn : y = n
  · subst hyn
    rw [if_pos rfl] at hy
    obtain ⟨a', w, ha', hrun, hw⟩ := specTy_runs (fuel := fuel) hsel htot hΓ _ _ hy
    have huw : u = w := specExpr_denote hsel href _ _ _ _ _ _ _ ha' h hu hrun
    subst huw
    exact ⟨u, Hax.Env.extend_same _ _ _, hw⟩
  · rw [if_neg hyn] at hy
    split at hy
    · rename_i hp
      have ex : x = env := env_of_pureForm hp h
      subst ex
      rw [Hax.Env.extend_other _ _ _ _ hyn]
      exact hΓ y τ hy
    · cases hy

/-- The typing after an expression in sequence is satisfied by the environment it leaves. -/
theorem wordEnv_seqTy {bi : Builtins} {fuel : Nat} {Γ : String → Option STy} {a : ImpExpr}
    {env x : Env} {u : Value} (hΓ : WordEnv Γ env)
    (h : denote' bi fuel a env = (.val u, x)) : WordEnv (seqTy Γ a) x := by
  intro y τ hy
  unfold seqTy at hy
  split at hy
  · rename_i hp
    have ex : x = env := env_of_pureForm hp h
    subst ex
    exact hΓ y τ hy
  · cases hy

/-- **The conditional pass runs.** At builtins with `SelectSpec`, `Refines` and `TotalOn`,
    for a source that passes `iteOk` at a typing the environment satisfies, a run of the
    source at the fuel `fuel` to a value that is not a control-flow value is a run of the
    result of the pass at the same fuel, to the same value and the same environment. -/
theorem desugarIte_runs {bi : Builtins} {fuel : Nat} {ρ : String → Option String} {sig : SSig}
    (hsel : SelectSpec bi) (href : Refines bi ρ) (htot : TotalOn bi ρ sig) :
    ∀ (e : ImpExpr) (Γ : String → Option STy) (env e₁ : Env) (v : Value),
      iteOk ρ sig Γ e = true → WordEnv Γ env →
      denote' bi fuel e env = (.val v, e₁) → Plain v →
      denote' bi fuel (desugarIte ρ e) env = (.val v, e₁)
  | .letBind n a b, Γ, env, e₁, v, hok, hΓ, hs, hv => by
      simp only [iteOk, Bool.and_eq_true] at hok
      simp only [desugarIte]
      obtain ⟨u, x, h1, hu, h2⟩ := denote'_letBind_val hs hv
      have h1' := desugarIte_runs hsel href htot a Γ _ _ _ hok.1 hΓ h1 hu
      have h2' := desugarIte_runs hsel href htot b _ _ _ _ hok.2
        (wordEnv_bindTy hsel href htot hΓ h1 hu) h2 hv
      exact denote'_letBind_of h1' hu h2'
  | .seq a b, Γ, env, e₁, v, hok, hΓ, hs, hv => by
      simp only [iteOk, Bool.and_eq_true] at hok
      simp only [desugarIte]
      obtain ⟨u, x, h1, hu, h2⟩ := denote'_seq_val hs hv
      have h1' := desugarIte_runs hsel href htot a Γ _ _ _ hok.1 hΓ h1 hu
      have h2' := desugarIte_runs hsel href htot b _ _ _ _ hok.2 (wordEnv_seqTy hΓ h1) h2 hv
      exact denote'_seq_of h1' hu h2'
  | .ifThenElse c a b, Γ, env, e₁, v, hok, hΓ, hs, hv => by
      simp only [iteOk, Bool.or_eq_true] at hok
      simp only [desugarIte]
      rcases hsp : specExpr ρ (.ifThenElse c a b) with _ | e'
      · exact hs
      · have hty : (specTy ρ sig Γ (.ifThenElse c a b)).isSome = true := by
          rcases hok with h | h
          · rw [hsp] at h; cases h
          · exact h
        obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hty
        obtain ⟨e'', w, he'', hrun, -⟩ := specTy_runs (fuel := fuel) hsel htot hΓ _ _ hτ
        rw [hsp] at he''
        cases he''
        have hvw : v = w := specExpr_denote hsel href _ _ _ _ _ _ _ hsp hs hv hrun
        subst hvw
        have he : e₁ = env := env_of_pureForm (specExpr_forms ρ _ _ hsp).1 hs
        subst he
        exact hrun
  | .lit .., _, _, _, _, _, _, hs, _ | .var .., _, _, _, _, _, _, hs, _
  | .app .., _, _, _, _, _, _, hs, _
  | .lam .., _, _, _, _, _, _, hs, _
  | .tuple .., _, _, _, _, _, _, hs, _ | .proj .., _, _, _, _, _, _, hs, _
  | .match_ .., _, _, _, _, _, _, hs, _ | .unitVal, _, _, _, _, _, _, hs, _
  | .borrow .., _, _, _, _, _, _, hs, _
  | .deref .., _, _, _, _, _, _, hs, _ | .assign .., _, _, _, _, _, _, hs, _
  | .forLoop .., _, _, _, _, _, _, hs, _ | .forLoopRev .., _, _, _, _, _, _, hs, _
  | .whileLoop .., _, _, _, _, _, _, hs, _ | .break_ .., _, _, _, _, _, _, hs, _
  | .continue_, _, _, _, _, _, _, hs, _ | .earlyReturn .., _, _, _, _, _, _, hs, _
  | .questionMark .., _, _, _, _, _, _, hs, _ | .forFold .., _, _, _, _, _, _, hs, _
  | .forFoldRev .., _, _, _, _, _, _, hs, _ | .whileFold .., _, _, _, _, _, _, hs, _
  | .forFoldReturn .., _, _, _, _, _, _, hs, _
  | .forFoldRevReturn .., _, _, _, _, _, _, hs, _
  | .whileFoldReturn .., _, _, _, _, _, _, hs, _
  | .cfBreak .., _, _, _, _, _, _, hs, _ | .cfContinue .., _, _, _, _, _, _, hs, _
  | .cfBreakContinue .., _, _, _, _, _, _, hs, _
  | .typeAscription .., _, _, _, _, _, _, hs, _ => by
      simp only [desugarIte]
      exact hs

/-! ## 4. The signature of `u64` code -/

/-- **The signature of the calls of `u64` code that are defined on all words**: the
    wrapping sum, difference and product and the bitwise operations at a width take two
    words to a word, a comparison takes two words to a bit, and a complement, a wrapping
    negation and a truncation take a word to a word. -/
def hax64WordSig (g : String) : Option (List STy × STy) :=
  match scalarBinOf g with
  | some (op, _) =>
      if op ∈ [ScalarBin.add, .sub, .mul, .and, .or, .xor] then
        some ([.word, .word], .word)
      else none
  | none =>
      match scalarCmpOf g with
      | some _ => some ([.word, .word], .bit)
      | none =>
          match scalarUnOf g with
          | some _ => some ([.word], .word)
          | none => none

/-- A list of values of the types of two words is two integers below `2^64`. -/
theorem forall₂_word2 {vals : List Value}
    (h : List.Forall₂ STy.Holds [.word, .word] vals) :
    ∃ a b : Nat, a < 2 ^ 64 ∧ b < 2 ^ 64 ∧ vals = [.int (a : Int), .int (b : Int)] := by
  cases h with
  | cons h1 ht =>
    cases ht with
    | cons h2 hn =>
      cases hn
      obtain ⟨a, ha, rfl⟩ := h1
      obtain ⟨b, hb, rfl⟩ := h2
      exact ⟨a, b, ha, hb, rfl⟩

/-- A list of values of the type of one word is one integer below `2^64`. -/
theorem forall₂_word1 {vals : List Value} (h : List.Forall₂ STy.Holds [.word] vals) :
    ∃ a : Nat, a < 2 ^ 64 ∧ vals = [.int (a : Int)] := by
  cases h with
  | cons h1 hn =>
    cases hn
    obtain ⟨a, ha, rfl⟩ := h1
    exact ⟨a, ha, rfl⟩

/-- **`Hax.hax64Builtins` is defined on the signature `hax64WordSig`.** -/
theorem total_hax64Builtins {g : String} {τs : List STy} {τ : STy}
    (h : hax64WordSig g = some (τs, τ)) {vals : List Value}
    (hv : List.Forall₂ STy.Holds τs vals) :
    ∃ v, _root_.Hax.hax64Builtins g vals = some v ∧ τ.Holds v := by
  unfold hax64WordSig at h
  rcases hb : scalarBinOf g with _ | ⟨op, w⟩
  · rw [hb] at h
    dsimp only at h
    rcases hc : scalarCmpOf g with _ | cmp
    · rw [hc] at h
      dsimp only at h
      rcases hu : scalarUnOf g with _ | ⟨uop, w⟩
      · rw [hu] at h; cases h
      · rw [hu] at h
        cases h
        obtain ⟨a, ha, rfl⟩ := forall₂_word1 hv
        have hmem := mem_of_find?_map hu
        have hsem := hax64UnTable_sem _ hmem (a : Int)
        have hw : w ≤ 64 := hax64UnTable_w _ hmem
        have hP : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
        have ha' : (0 : Int) ≤ (a : Int) ∧ (a : Int) < 2 ^ 64 :=
          ⟨Int.natCast_nonneg a, by exact_mod_cast ha⟩
        dsimp only at hsem
        rw [hsem, orElse_none_eq]
        cases uop with
        | not =>
          simp only [ScalarUn.val, _root_.Hax.u64UnOp, if_pos ha']
          exact ⟨_, rfl, _, lt_of_le_of_lt (Nat.sub_le _ _)
            (lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos) hP), rfl⟩
        | neg =>
          simp only [ScalarUn.val, _root_.Hax.u64UnOp, if_pos ha']
          exact ⟨_, rfl, _, Nat.mod_lt _ (by decide), rfl⟩
        | cast =>
          simp only [ScalarUn.val, if_pos ha'.1]
          exact ⟨_, rfl, _, lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos w)) hP, rfl⟩
    · rw [hc] at h
      cases h
      obtain ⟨a, b, -, -, rfl⟩ := forall₂_word2 hv
      have hsem := hax64CmpTable_sem _ (mem_of_find?_map hc) (a : Int) (b : Int)
      exact ⟨_, hsem, _, rfl⟩
  · rw [hb] at h
    dsimp only at h
    split at h
    · rename_i hop
      cases h
      obtain ⟨a, b, ha, hb', rfl⟩ := forall₂_word2 hv
      have hmem := mem_of_find?_map hb
      have hsem := hax64BinTable_sem _ hmem (a : Int) (b : Int)
      have hw : w ≤ 64 := hax64BinTable_w _ hmem
      have hP : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
      have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
      dsimp only at hsem
      rw [hsem, _root_.Hax.u64BinOp_natCast ha hb', orElse_none_eq]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨_, rfl, _, lt_of_lt_of_le (Nat.mod_lt _ hpos) hP, rfl⟩
      · exact ⟨_, rfl, _, lt_of_lt_of_le (Nat.mod_lt _ hpos) hP, rfl⟩
      · exact ⟨_, rfl, _, lt_of_lt_of_le (Nat.mod_lt _ hpos) hP, rfl⟩
      · exact ⟨_, rfl, _, lt_of_le_of_lt Nat.and_le_left
          (lt_of_lt_of_le (Nat.mod_lt _ hpos) hP), rfl⟩
      · exact ⟨_, rfl, _, Nat.or_lt_two_pow (lt_of_lt_of_le (Nat.mod_lt _ hpos) hP)
          (lt_of_lt_of_le (Nat.mod_lt _ hpos) hP), rfl⟩
      · exact ⟨_, rfl, _, Nat.xor_lt_two_pow (lt_of_lt_of_le (Nat.mod_lt _ hpos) hP)
          (lt_of_lt_of_le (Nat.mod_lt _ hpos) hP), rfl⟩
    · cases h

/-- `Hax.hax64Builtins` satisfies `TotalOn` at `hax64WordSig`, for every renaming. -/
theorem totalOn_hax64Builtins (ρ : String → Option String) :
    TotalOn _root_.Hax.hax64Builtins ρ hax64WordSig :=
  fun _ _ _ _ _ hs _ hv => total_hax64Builtins hs hv

/-- `TotalOn` passes to the table with `select`, for a renaming that does not rename to
    `select`. -/
theorem totalOn_withSelect {bi : Builtins} {ρ : String → Option String} {sig : SSig}
    (h : TotalOn bi ρ sig) (hρ : ∀ f g, ρ f = some g → f ≠ "select" ∧ g ≠ "select") :
    TotalOn (withSelect bi) ρ sig := by
  intro f g hfg τs τ hs vals hv
  rw [withSelect_of_ne bi (hρ f g hfg).2]
  exact h f g hfg τs τ hs vals hv

/-- **`TotalOn` at the `u64` table with `select`**, for the renaming `hax64Spec` and the
    signature `hax64WordSig`. -/
theorem totalOn_hax64Spec :
    TotalOn (withSelect _root_.Hax.hax64Builtins) hax64Spec hax64WordSig :=
  totalOn_withSelect (totalOn_hax64Builtins _) ImpDesugarTable.hax64Spec_ne_select

/-! ## 5. The typing of the parameters -/

/-- The type of speculatable expressions of an `NfTy`: a `64`-bit word and a bit. -/
def styOf : NfTy → Option STy
  | .word w => if w = 64 then some .word else none
  | .bit => some .bit
  | _ => none

/-- The typing of the parameters `ps`: a parameter of a `64`-bit word type is a word and
    a parameter of the bit type is a bit. -/
def entryTy (ps : List (String × NfTy)) : String → Option STy :=
  fun x => (ps.find? (·.1 == x)).bind fun p => styOf p.2

/-- An environment holding, at each parameter, the encoding of a value of its type
    satisfies the typing `entryTy`. -/
theorem wordEnv_entryTy {env : Env} {ps : List (String × NfTy)} (h : EntryTyped env ps) :
    WordEnv (entryTy ps) env := by
  intro x τ hx
  unfold entryTy at hx
  rcases hf : ps.find? (·.1 == x) with _ | ⟨x', t⟩
  · rw [hf] at hx; cases hx
  · rw [hf] at hx
    have hx' : x' = x := by simpa using List.find?_some hf
    subst hx'
    obtain ⟨y, hy⟩ := h x' t (List.mem_of_find?_eq_some hf)
    refine ⟨_, hy, ?_⟩
    have hx2 : styOf t = some τ := hx
    cases t with
    | word w =>
      simp only [styOf] at hx2
      split at hx2
      · rename_i hw
        subst hw
        cases hx2
        exact ⟨y.toNat, y.isLt, rfl⟩
      · cases hx2
    | bit =>
      cases hx2
      exact ⟨y, rfl⟩
    | _ => simp [styOf] at hx2

/-! ## 6. The remainder pass -/

/-- **The word operations of the Barrett sequence are total**: on two integers below
    `2^64`, `mulhi#64`, `wrapping_mul#64` and `wrapping_sub#64` return an integer below
    `2^64`, and `Lt` returns a Boolean. -/
structure WordTotal (bi : Builtins) : Prop where
  mulhi : ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 →
    ∃ c : Nat, c < 2 ^ 64 ∧ bi "mulhi#64" [.int (a : Int), .int (b : Int)] = some (.int (c : Int))
  wmul : ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 →
    ∃ c : Nat, c < 2 ^ 64 ∧
      bi "wrapping_mul#64" [.int (a : Int), .int (b : Int)] = some (.int (c : Int))
  wsub : ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 →
    ∃ c : Nat, c < 2 ^ 64 ∧
      bi "wrapping_sub#64" [.int (a : Int), .int (b : Int)] = some (.int (c : Int))
  lt : ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 →
    ∃ k : Bool, bi "Lt" [.int (a : Int), .int (b : Int)] = some (.bool k)

/-- **`Rem` reads a word.** Where `Rem` is defined on two operands, the first is an integer
    below `2^64`. -/
def RemWord (bi : Builtins) : Prop :=
  ∀ u m v, bi "Rem" [u, m] = some v → ∃ a : Nat, a < 2 ^ 64 ∧ u = .int (a : Int)

/-- **The sequence runs.** On an operand that runs to an integer below `2^64` and leaves
    the environment unchanged, at a modulus `1 < p < 2^64`, `remForm p x` runs to a value
    and leaves the environment unchanged. -/
theorem remForm_runs {bi : Builtins} {fuel : Nat} (hsel : SelectSpec bi) (hT : WordTotal bi)
    {p a : Nat} {x : ImpExpr} {env : Env} (hp1 : 1 < p) (hp : p < 2 ^ 64) (ha : a < 2 ^ 64)
    (hx : denote' bi fuel x env = (.val (.int (a : Int)), env)) :
    ∃ w, denote' bi fuel (remForm p x) env = (.val w, env) := by
  have hμ : 2 ^ 64 / p < 2 ^ 64 := Nat.div_lt_self (by decide) hp1
  obtain ⟨c1, hc1, e1⟩ := hT.mulhi a (2 ^ 64 / p) ha hμ
  have r1 := app2_of hx (plain_int _) (lit_int_run bi fuel ((2 ^ 64 / p : Nat) : Int) env)
    (plain_int _) e1
  obtain ⟨c2, hc2, e2⟩ := hT.wmul c1 p hc1 hp
  have r2 := app2_of r1 (plain_int _) (lit_int_run bi fuel (p : Int) env) (plain_int _) e2
  obtain ⟨c3, hc3, e3⟩ := hT.wsub a c2 ha hc2
  have r3 : denote' bi fuel (barrettExpr p x) env = (.val (.int (c3 : Int)), env) :=
    app2_of hx (plain_int _) r2 (plain_int _) e3
  obtain ⟨k, e4⟩ := hT.lt c3 p hc3 hp
  have r4 := app2_of r3 (plain_int _) (lit_int_run bi fuel (p : Int) env) (plain_int _) e4
  obtain ⟨c5, -, e5⟩ := hT.wsub c3 p hc3 hp
  have r5 := app2_of r3 (plain_int _) (lit_int_run bi fuel (p : Int) env) (plain_int _) e5
  exact ⟨_, denote'_app_of (denoteArgs'_cons_val r4 (plain_bool k)
    (denoteArgs'_cons_val r3 (plain_int _) (denoteArgs'_cons_val r5 (plain_int _)
      (denoteArgs'_nil_run bi fuel env)))) (hsel k _ _)⟩

mutual
/-- **The rewriting runs.** At builtins with `SelectSpec`, `WordSpec`, `WordTotal` and
    `RemWord`, a run of a `pureForm` expression to a value, from an environment that holds
    the constants, is a run of its rewriting to the same value. -/
theorem remExpr_runs {bi : Builtins} {fuel : Nat} {κ : String → Option Nat}
    (hsel : SelectSpec bi) (hw : WordSpec bi) (hT : WordTotal bi) (hR : RemWord bi) :
    ∀ (e : ImpExpr) (env e₁ : Env) (v : Value), pureForm e = true → Known κ env →
      denote' bi fuel e env = (.val v, e₁) →
      denote' bi fuel (remExpr κ e) env = (.val v, e₁)
  | .app f args, env, e₁, v, hp, hk, hs => by
      have hpa : pureForms args = true := by simpa [pureForm] using hp
      obtain ⟨vals, hd, hb⟩ := denote'_app_val hs
      rcases hsite : remSite κ f args with _ | p
      · rw [remExpr_app, hsite]
        exact denote'_app_of (remArgs_runs hsel hw hT hR args env e₁ vals hpa hk hd) hb
      · obtain ⟨x, m, rfl, rfl, hm⟩ := remSite_some hsite
        simp only [pureForms, Bool.and_eq_true] at hpa
        obtain ⟨hmr, hp1, hp64, _⟩ := modulusOf_run hm bi fuel hk
        obtain ⟨u₁, x₁, r₁, h1, _, hr1, rfl⟩ := denoteArgs'_cons_some hd
        obtain ⟨u₂, x₂, r₂, h2, _, hr2, rfl⟩ := denoteArgs'_cons_some hr1
        have hnil := (denoteArgs'_nil_run bi fuel x₂).symm.trans hr2
        cases hnil
        have ex1 : x₁ = env := env_of_pureForm hpa.1 h1
        subst ex1
        rw [hmr] at h2
        cases h2
        obtain ⟨a, ha, rfl⟩ := hR _ _ _ hb
        have hx' := remExpr_runs hsel hw hT hR x _ _ _ hpa.1 hk h1
        obtain ⟨w, hform⟩ := remForm_runs hsel hT hp1 hp64 ha hx'
        have ht : denote' bi fuel (remExpr κ (.app "Rem" [x, m])) e₁ = (.val w, e₁) := by
          rw [remExpr_app, hsite]
          exact hform
        have hvw : v = w := remExpr_denote hsel hw _ _ _ _ _ _ hp hk hs ht
        subst hvw
        exact ht
  | .lit _, _, _, _, _, _, hs | .var _, _, _, _, _, _, hs
  | .ifThenElse .., _, _, _, _, _, hs => by
      simp only [remExpr]
      exact hs
  | .letBind .., _, _, _, h, _, _ | .lam .., _, _, _, h, _, _
  | .tuple .., _, _, _, h, _, _ | .proj .., _, _, _, h, _, _
  | .match_ .., _, _, _, h, _, _ | .unitVal, _, _, _, h, _, _
  | .seq .., _, _, _, h, _, _ | .borrow .., _, _, _, h, _, _
  | .deref .., _, _, _, h, _, _ | .assign .., _, _, _, h, _, _
  | .forLoop .., _, _, _, h, _, _ | .forLoopRev .., _, _, _, h, _, _
  | .whileLoop .., _, _, _, h, _, _ | .break_ .., _, _, _, h, _, _
  | .continue_, _, _, _, h, _, _ | .earlyReturn .., _, _, _, h, _, _
  | .questionMark .., _, _, _, h, _, _ | .forFold .., _, _, _, h, _, _
  | .forFoldRev .., _, _, _, h, _, _ | .whileFold .., _, _, _, h, _, _
  | .forFoldReturn .., _, _, _, h, _, _
  | .forFoldRevReturn .., _, _, _, h, _, _
  | .whileFoldReturn .., _, _, _, h, _, _
  | .cfBreak .., _, _, _, h, _, _ | .cfContinue .., _, _, _, h, _, _
  | .cfBreakContinue .., _, _, _, h, _, _
  | .typeAscription .., _, _, _, h, _, _ => by simp [pureForm] at h
/-- The list counterpart of `remExpr_runs`. -/
theorem remArgs_runs {bi : Builtins} {fuel : Nat} {κ : String → Option Nat}
    (hsel : SelectSpec bi) (hw : WordSpec bi) (hT : WordTotal bi) (hR : RemWord bi) :
    ∀ (es : List ImpExpr) (env e₁ : Env) (vs : List Value), pureForms es = true →
      Known κ env → denoteArgs' bi fuel es env = (some vs, e₁) →
      denoteArgs' bi fuel (remArgs κ es) env = (some vs, e₁)
  | [], env, e₁, vs, _, _, hs => by
      simp only [remArgs]
      exact hs
  | e :: es, env, e₁, vs, hp, hk, hs => by
      simp only [remArgs]
      simp only [pureForms, Bool.and_eq_true] at hp
      obtain ⟨u, x, vs0, hu1, hpu, hr, rfl⟩ := denoteArgs'_cons_some hs
      have ex : x = env := env_of_pureForm hp.1 hu1
      subst ex
      exact denoteArgs'_cons_val (remExpr_runs hsel hw hT hR e _ _ _ hp.1 hk hu1) hpu
        (remArgs_runs hsel hw hT hR es _ _ _ hp.2 hk hr)
end

/-- The pass at an expression that is neither a `letBind` nor a `seq` runs to the value of
    the source. -/
theorem desugarRem_leaf_runs {bi : Builtins} {fuel : Nat} {κ : String → Option Nat}
    (hsel : SelectSpec bi) (hw : WordSpec bi) (hT : WordTotal bi) (hR : RemWord bi)
    {e : ImpExpr} {env e₁ : Env} {v : Value} (hk : Known κ env)
    (hs : denote' bi fuel e env = (.val v, e₁)) :
    denote' bi fuel (if pureForm e then remExpr κ e else e) env = (.val v, e₁) := by
  by_cases hp : pureForm e = true
  · rw [if_pos hp]
    exact remExpr_runs hsel hw hT hR e _ _ _ hp hk hs
  · rw [if_neg hp]
    exact hs

/-- **The remainder pass runs.** At builtins with `SelectSpec`, `WordSpec`, `WordTotal`
    and `RemWord`, a run of the source at the fuel `fuel` to a value that is not a
    control-flow value, from an environment that holds the constants, is a run of the
    result of the pass at the same fuel, to the same value and the same environment. -/
theorem desugarRem_runs {bi : Builtins} {fuel : Nat} (hsel : SelectSpec bi)
    (hw : WordSpec bi) (hT : WordTotal bi) (hR : RemWord bi) :
    ∀ (e : ImpExpr) (κ : String → Option Nat) (env e₁ : Env) (v : Value),
      Known κ env → denote' bi fuel e env = (.val v, e₁) → Plain v →
      denote' bi fuel (desugarRem κ e) env = (.val v, e₁)
  | .letBind n a b, κ, env, e₁, v, hk, hs, hv => by
      simp only [desugarRem]
      obtain ⟨u, x, h1, hu, h2⟩ := denote'_letBind_val hs hv
      have h1' := desugarRem_runs hsel hw hT hR a κ _ _ _ hk h1 hu
      have h2' := desugarRem_runs hsel hw hT hR b _ _ _ _ (known_bindConst hk h1) h2 hv
      exact denote'_letBind_of h1' hu h2'
  | .seq a b, κ, env, e₁, v, hk, hs, hv => by
      simp only [desugarRem]
      obtain ⟨u, x, h1, hu, h2⟩ := denote'_seq_val hs hv
      have h1' := desugarRem_runs hsel hw hT hR a κ _ _ _ hk h1 hu
      have h2' := desugarRem_runs hsel hw hT hR b _ _ _ _ (known_seqConst hk h1) h2 hv
      exact denote'_seq_of h1' hu h2'
  | .lit .., _, _, _, _, hk, hs, _ | .var .., _, _, _, _, hk, hs, _
  | .app .., _, _, _, _, hk, hs, _
  | .ifThenElse .., _, _, _, _, hk, hs, _
  | .lam .., _, _, _, _, hk, hs, _
  | .tuple .., _, _, _, _, hk, hs, _
  | .proj .., _, _, _, _, hk, hs, _
  | .match_ .., _, _, _, _, hk, hs, _
  | .unitVal, _, _, _, _, hk, hs, _
  | .borrow .., _, _, _, _, hk, hs, _
  | .deref .., _, _, _, _, hk, hs, _
  | .assign .., _, _, _, _, hk, hs, _
  | .forLoop .., _, _, _, _, hk, hs, _
  | .forLoopRev .., _, _, _, _, hk, hs, _
  | .whileLoop .., _, _, _, _, hk, hs, _
  | .break_ .., _, _, _, _, hk, hs, _
  | .continue_, _, _, _, _, hk, hs, _
  | .earlyReturn .., _, _, _, _, hk, hs, _
  | .questionMark .., _, _, _, _, hk, hs, _
  | .forFold .., _, _, _, _, hk, hs, _
  | .forFoldRev .., _, _, _, _, hk, hs, _
  | .whileFold .., _, _, _, _, hk, hs, _
  | .forFoldReturn .., _, _, _, _, hk, hs, _
  | .forFoldRevReturn .., _, _, _, _, hk, hs, _
  | .whileFoldReturn .., _, _, _, _, hk, hs, _
  | .cfBreak .., _, _, _, _, hk, hs, _
  | .cfContinue .., _, _, _, _, hk, hs, _
  | .cfBreakContinue .., _, _, _, _, hk, hs, _
  | .typeAscription .., _, _, _, _, hk, hs, _ => by
      simp only [desugarRem]
      exact desugarRem_leaf_runs hsel hw hT hR hk hs

/-! ## 7. The word operations at the `u64` table -/

/-- **`Hax.hax64Builtins` satisfies `WordTotal`.** -/
theorem wordTotal_hax64Builtins : WordTotal _root_.Hax.hax64Builtins where
  mulhi a b ha hb := by
    refine ⟨a * b / 2 ^ 64, Nat.div_lt_of_lt_mul (Nat.mul_lt_mul'' ha hb), ?_⟩
    unfold _root_.Hax.hax64Builtins
    rw [_root_.Hax.hax64WordOps_mulhi, _root_.Hax.u64BinOp_natCast ha hb,
      Nat.shiftRight_eq_div_pow]
    rfl
  wmul a b ha hb := by
    refine ⟨a * b % 2 ^ 64, Nat.mod_lt _ (by decide), ?_⟩
    unfold _root_.Hax.hax64Builtins
    rw [_root_.Hax.hax64WordOps_wrapping_mul, _root_.Hax.u64BinOp_natCast ha hb]
    rfl
  wsub a b ha hb := by
    refine ⟨(a % 2 ^ 64 + 2 ^ 64 - b % 2 ^ 64) % 2 ^ 64, Nat.mod_lt _ (by decide), ?_⟩
    unfold _root_.Hax.hax64Builtins
    rw [_root_.Hax.hax64WordOps_wrapping_sub, _root_.Hax.u64BinOp_natCast ha hb]
    rfl
  lt a b _ _ := ⟨decide ((a : Int) < (b : Int)), rfl⟩

/-- `WordTotal` passes to the table with `select`. -/
theorem wordTotal_withSelect {bi : Builtins} (h : WordTotal bi) :
    WordTotal (withSelect bi) where
  mulhi a b ha hb := by
    rw [withSelect_of_ne bi (by decide)]
    exact h.mulhi a b ha hb
  wmul a b ha hb := by
    rw [withSelect_of_ne bi (by decide)]
    exact h.wmul a b ha hb
  wsub a b ha hb := by
    rw [withSelect_of_ne bi (by decide)]
    exact h.wsub a b ha hb
  lt a b ha hb := by
    rw [withSelect_of_ne bi (by decide)]
    exact h.lt a b ha hb

/-- `RemWord` passes to a table whose values are values of the table. -/
theorem remWord_mono {bi bi' : Builtins} (h : RemWord bi)
    (hsub : ∀ f vals v, bi' f vals = some v → bi f vals = some v) : RemWord bi' :=
  fun u m v hv => h u m v (hsub _ _ _ hv)

/-- `RemWord` passes to the table with `select`. -/
theorem remWord_withSelect {bi : Builtins} (h : RemWord bi) : RemWord (withSelect bi) :=
  fun u m v hv => h u m v (by rwa [withSelect_of_ne bi (by decide)] at hv)

end CatCrypt.Crypto.Hax.ImpDesugarRun
