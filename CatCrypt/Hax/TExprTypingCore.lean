/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.TExpr
public import HaxLean.AST
public import HaxLean.Semantics
public import CatCrypt.Hax.ClassBuiltins

/-!
# A typing judgement for typed hax expressions

`HasType sig Γ e τ` types a `TExpr` under a type environment `Γ` for its free variables
and a signature `sig` for the builtin functions it calls. A type parameter `.typeVar n` is
an opaque type constant: it is equal only to itself, and a value inhabits it only through
the interpretation `O` of the opaque types. A node annotation must be `.unknown` or the
derived type (`AnnOK`).

A `let`, a counted loop, a closure and a match arm may rebind a variable of `Γ` only at
the type `Γ` gives it (`TyEnv.Le Γ Γ'`). The reference semantics `denote` does not restore
the environment on leaving a binder, so a sibling expression evaluated later reads the
rebound value; the side condition keeps that value at the type the sibling is checked at.

## Main definitions

* `HasType`, `HasTypeList`, `HasTypeArms` — the typing judgement over literals, variables,
  `let`, closures, calls, tuples, projections, conditionals, matches on option, tuple,
  literal and variable patterns, `()`, sequencing, annotations and the functional loops
  `forFold`, `forFoldRev`, `whileFold`
* `check` — a decidable checker returning the derived type
* `Value.HasType` — value typing, parametric in the interpretation `O` of opaque types
* `BuiltinsRespect` — a builtin table returns values of the result type its signature gives

## Main results

* `check_sound` — `check sig Γ e = some τ` gives `HasType sig Γ e τ`
* `HasType.instTypes` — typing is stable under instantiation of type parameters
  (`TExpr.instTypes σ`), with the environment and signature instantiated by `σ`
* `HasType.sound` — type soundness of `denote` on every typed expression, at every fuel:
  from a well-typed environment, under builtins respecting `sig`, the run returns a value
  of the derived type or an error, and its exit environment is well typed. Closures and
  the functional loops denote an error under `denote`, so on them the statement holds
  through the error outcome.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.TExprTyping

open _root_.Hax
open CatCrypt.Hax.ClassBuiltins

/-! ## Environments and signatures -/

/-- A type environment: the type of each variable in scope. -/
abbrev TyEnv := String → Option ImpType

/-- A builtin signature: the parameter types and the result type of each builtin. -/
abbrev Sig := String → Option (List ImpType × ImpType)

/-- The type environment `Γ` with `n` bound to `τ`. -/
def TyEnv.extend (Γ : TyEnv) (n : String) (τ : ImpType) : TyEnv :=
  fun x => if x == n then some τ else Γ x

/-- The type environment `Γ` extended by the bindings `bs`, from left to right. -/
def TyEnv.extendList (Γ : TyEnv) : List (String × ImpType) → TyEnv
  | [] => Γ
  | (x, t) :: bs => TyEnv.extendList (Γ.extend x t) bs

/-- `Γ'` agrees with `Γ` on every variable `Γ` binds. -/
def TyEnv.Le (Γ Γ' : TyEnv) : Prop :=
  ∀ x τ, Γ x = some τ → Γ' x = some τ

/-- A node annotation agrees with a type when it is `.unknown` or the type itself. -/
def AnnOK (ann τ : ImpType) : Prop := ann = .unknown ∨ ann = τ

/-- The type of a literal. -/
def litTy : ImpLit → ImpType
  | .bool _ => .bool
  | .int _ => .int
  | .unit => .unit
  | .uintLit w _ => .uint w
  | .sintLit w _ => .sint w

/-! ## Pattern typing -/

mutual
/-- `PatHasType p τ bs`: the pattern `p` matches values of type `τ` and binds `bs`. -/
inductive PatHasType : ImpPat → ImpType → List (String × ImpType) → Prop where
  | wildcard (τ : ImpType) : PatHasType .wildcard τ []
  | var (n : String) (τ : ImpType) : PatHasType (.varPat n) τ [(n, τ)]
  | lit (l : ImpLit) : PatHasType (.litPat l) (litTy l) []
  | none (τ : ImpType) : PatHasType .nonePat (.option τ) []
  | some {p : ImpPat} {τ : ImpType} {bs : List (String × ImpType)} :
      PatHasType p τ bs → PatHasType (.somePat p) (.option τ) bs
  | tuple {ps : List ImpPat} {ts : List ImpType} {bs : List (String × ImpType)} :
      PatListHasType ps ts bs → PatHasType (.tuplePat ps) (.tuple ts) bs

/-- `PatListHasType ps ts bs`: the patterns `ps` match values of the types `ts` pointwise
    and bind `bs`. -/
inductive PatListHasType : List ImpPat → List ImpType → List (String × ImpType) → Prop where
  | nil : PatListHasType [] [] []
  | cons {p : ImpPat} {ps : List ImpPat} {t : ImpType} {ts : List ImpType}
      {bs bs' : List (String × ImpType)} :
      PatHasType p t bs → PatListHasType ps ts bs' →
      PatListHasType (p :: ps) (t :: ts) (bs ++ bs')
end

/-! ## The typing judgement -/

mutual
/-- `HasType sig Γ e τ`: under the signature `sig` and the type environment `Γ`, the typed
    expression `e` has type `τ`. -/
inductive HasType (sig : Sig) : TyEnv → TExpr → ImpType → Prop where
  | lit {Γ : TyEnv} {l : ImpLit} {ann : ImpType} :
      AnnOK ann (litTy l) → HasType sig Γ (.mk (.lit l) ann) (litTy l)
  | var {Γ : TyEnv} {n : String} {ann τ : ImpType} :
      Γ n = some τ → AnnOK ann τ → HasType sig Γ (.mk (.var n) ann) τ
  | letBind {Γ : TyEnv} {n : String} {v b : TExpr} {ann τ₁ τ : ImpType} :
      HasType sig Γ v τ₁ → TyEnv.Le Γ (Γ.extend n τ₁) → HasType sig (Γ.extend n τ₁) b τ →
      AnnOK ann τ → HasType sig Γ (.mk (.letBind n v b) ann) τ
  | lam {Γ : TyEnv} {ps : List String} {b : TExpr} {ann : ImpType} {ts : List ImpType}
      {r : ImpType} :
      ps.length = ts.length → TyEnv.Le Γ (Γ.extendList (ps.zip ts)) →
      HasType sig (Γ.extendList (ps.zip ts)) b r → AnnOK ann (.fn ts r) →
      HasType sig Γ (.mk (.lam ps b) ann) (.fn ts r)
  | app {Γ : TyEnv} {f : String} {args : List TExpr} {ann : ImpType} {ts : List ImpType}
      {r : ImpType} :
      sig f = some (ts, r) → HasTypeList sig Γ args ts → AnnOK ann r →
      HasType sig Γ (.mk (.app f args) ann) r
  | tuple {Γ : TyEnv} {es : List TExpr} {ann : ImpType} {ts : List ImpType} :
      HasTypeList sig Γ es ts → AnnOK ann (.tuple ts) →
      HasType sig Γ (.mk (.tuple es) ann) (.tuple ts)
  | projTuple {Γ : TyEnv} {e : TExpr} {i : Nat} {ann : ImpType} {ts : List ImpType}
      {τ : ImpType} :
      HasType sig Γ e (.tuple ts) → ts[i]? = some τ → AnnOK ann τ →
      HasType sig Γ (.mk (.proj e i) ann) τ
  | projArray {Γ : TyEnv} {e : TExpr} {i : Nat} {ann t : ImpType} {n : Nat} :
      HasType sig Γ e (.array t n) → i < n → AnnOK ann t →
      HasType sig Γ (.mk (.proj e i) ann) t
  | ifThenElse {Γ : TyEnv} {c t e : TExpr} {ann τ : ImpType} :
      HasType sig Γ c .bool → HasType sig Γ t τ → HasType sig Γ e τ → AnnOK ann τ →
      HasType sig Γ (.mk (.ifThenElse c t e) ann) τ
  | match_ {Γ : TyEnv} {s : TExpr} {arms : List (ImpPat × TExpr)} {ann σs τ : ImpType} :
      HasType sig Γ s σs → HasTypeArms sig Γ σs arms τ → AnnOK ann τ →
      HasType sig Γ (.mk (.match_ s arms) ann) τ
  | unitVal {Γ : TyEnv} {ann : ImpType} :
      AnnOK ann .unit → HasType sig Γ (.mk .unitVal ann) .unit
  | seq {Γ : TyEnv} {e₁ e₂ : TExpr} {ann τ₁ τ : ImpType} :
      HasType sig Γ e₁ τ₁ → HasType sig Γ e₂ τ → AnnOK ann τ →
      HasType sig Γ (.mk (.seq e₁ e₂) ann) τ
  | ann {Γ : TyEnv} {e : TExpr} {a τ : ImpType} :
      HasType sig Γ e τ → AnnOK a τ → HasType sig Γ (.mk (.ann e) a) τ
  | forFold {Γ : TyEnv} {v : String} {lo hi b : TExpr} {ann τi τ : ImpType} :
      τi.isIntLike = true → HasType sig Γ lo τi → HasType sig Γ hi τi →
      TyEnv.Le Γ (Γ.extend v τi) → HasType sig (Γ.extend v τi) b τ → AnnOK ann τ →
      HasType sig Γ (.mk (.forFold v lo hi b) ann) τ
  | forFoldRev {Γ : TyEnv} {v : String} {lo hi b : TExpr} {ann τi τ : ImpType} :
      τi.isIntLike = true → HasType sig Γ lo τi → HasType sig Γ hi τi →
      TyEnv.Le Γ (Γ.extend v τi) → HasType sig (Γ.extend v τi) b τ → AnnOK ann τ →
      HasType sig Γ (.mk (.forFoldRev v lo hi b) ann) τ
  | whileFold {Γ : TyEnv} {c b : TExpr} {ann τ : ImpType} :
      HasType sig Γ c .bool → HasType sig Γ b τ → AnnOK ann τ →
      HasType sig Γ (.mk (.whileFold c b) ann) τ

/-- `HasTypeList sig Γ es ts`: the expressions `es` have the types `ts` pointwise. -/
inductive HasTypeList (sig : Sig) : TyEnv → List TExpr → List ImpType → Prop where
  | nil {Γ : TyEnv} : HasTypeList sig Γ [] []
  | cons {Γ : TyEnv} {e : TExpr} {es : List TExpr} {τ : ImpType} {ts : List ImpType} :
      HasType sig Γ e τ → HasTypeList sig Γ es ts → HasTypeList sig Γ (e :: es) (τ :: ts)

/-- `HasTypeArms sig Γ σs arms τ`: each arm's pattern matches values of type `σs`, and its
    body has type `τ` under the pattern's bindings. -/
inductive HasTypeArms (sig : Sig) : TyEnv → ImpType → List (ImpPat × TExpr) → ImpType → Prop where
  | nil {Γ : TyEnv} {σs τ : ImpType} : HasTypeArms sig Γ σs [] τ
  | cons {Γ : TyEnv} {σs : ImpType} {p : ImpPat} {b : TExpr} {arms : List (ImpPat × TExpr)}
      {bs : List (String × ImpType)} {τ : ImpType} :
      PatHasType p σs bs → TyEnv.Le Γ (Γ.extendList bs) →
      HasType sig (Γ.extendList bs) b τ → HasTypeArms sig Γ σs arms τ →
      HasTypeArms sig Γ σs ((p, b) :: arms) τ
end

/-! ## Boolean equality of types -/

mutual
/-- `ImpType.beq` decides equality. -/
theorem eq_of_beq : (a b : ImpType) → ImpType.beq a b = true → a = b
  | a, b, h => by
    cases a <;> cases b <;>
      simp only [ImpType.beq, Bool.and_eq_true, beq_iff_eq,
        Bool.false_eq_true, ImpType.uint.injEq, ImpType.sint.injEq,
        ImpType.tuple.injEq, ImpType.option.injEq, ImpType.result.injEq,
        ImpType.controlFlow.injEq, ImpType.adt.injEq, ImpType.fn.injEq, ImpType.ref.injEq,
        ImpType.slice.injEq, ImpType.array.injEq, ImpType.typeVar.injEq] at h ⊢
    all_goals first
      | exact h
      | exact eq_of_beq _ _ h
      | exact eq_of_beqList _ _ h
      | exact ⟨eq_of_beq _ _ h.1, eq_of_beq _ _ h.2⟩
      | exact ⟨h.1, eq_of_beqList _ _ h.2⟩
      | exact ⟨eq_of_beqList _ _ h.1, eq_of_beq _ _ h.2⟩
      | exact ⟨eq_of_beq _ _ h.1, h.2⟩
      | (revert h; rename_i a b; cases a <;> cases b <;> decide)

/-- `ImpType.beq.beqList` decides equality of lists. -/
theorem eq_of_beqList : (a b : List ImpType) → ImpType.beq.beqList a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
      simp only [ImpType.beq.beqList, Bool.and_eq_true] at h
      rw [eq_of_beq x y h.1, eq_of_beqList xs ys h.2]
  | [], _ :: _, h => by simp [ImpType.beq.beqList] at h
  | _ :: _, [], h => by simp [ImpType.beq.beqList] at h
end

/-! ## Environment lemmas -/

theorem TyEnv.Le.refl (Γ : TyEnv) : TyEnv.Le Γ Γ := fun _ _ h => h

theorem TyEnv.Le.trans {Γ₁ Γ₂ Γ₃ : TyEnv} (h₁ : TyEnv.Le Γ₁ Γ₂) (h₂ : TyEnv.Le Γ₂ Γ₃) :
    TyEnv.Le Γ₁ Γ₃ := fun x τ h => h₂ x τ (h₁ x τ h)

theorem TyEnv.extendList_append (Γ : TyEnv) (bs bs' : List (String × ImpType)) :
    Γ.extendList (bs ++ bs') = (Γ.extendList bs).extendList bs' := by
  induction bs generalizing Γ with
  | nil => rfl
  | cons b bs ih => obtain ⟨x, t⟩ := b; exact ih _

/-! ## The checker -/

/-- `AnnOK` as a boolean. -/
def annB (ann τ : ImpType) : Bool := ImpType.beq ann .unknown || ImpType.beq ann τ

/-- The type `τ` when the annotation `ann` agrees with it. -/
def guardAnn (ann τ : ImpType) : Option ImpType := if annB ann τ then some τ else none

/-- Binding `n` at `τ` keeps every binding of `Γ`: `n` is unbound in `Γ` or bound at `τ`. -/
def fitsB (Γ : TyEnv) (n : String) (τ : ImpType) : Bool :=
  match Γ n with
  | none => true
  | some τ' => ImpType.beq τ' τ

/-- `fitsB Γ` for each binding of a list. -/
def fitsListB (Γ : TyEnv) (bs : List (String × ImpType)) : Bool :=
  bs.all fun b => fitsB Γ b.1 b.2

mutual
/-- The bindings of the pattern `p` at the scrutinee type `τ`, when `p` matches `τ`. -/
def checkPat : ImpPat → ImpType → Option (List (String × ImpType))
  | .wildcard, _ => some []
  | .varPat n, τ => some [(n, τ)]
  | .litPat l, τ => if ImpType.beq τ (litTy l) then some [] else none
  | .nonePat, .option _ => some []
  | .somePat p, .option τ => checkPat p τ
  | .tuplePat ps, .tuple ts => checkPatList ps ts
  | _, _ => none

/-- `checkPat` pointwise on a list of patterns and a list of types. -/
def checkPatList : List ImpPat → List ImpType → Option (List (String × ImpType))
  | [], [] => some []
  | p :: ps, t :: ts => do
      let bs ← checkPat p t
      let bs' ← checkPatList ps ts
      pure (bs ++ bs')
  | _, _ => none
end

mutual
/-- The type of `e` under `sig` and `Γ`, when `e` is typed by the rules of `HasType`. -/
def check (sig : Sig) (Γ : TyEnv) : TExpr → Option ImpType
  | .mk (.lit l) ann => guardAnn ann (litTy l)
  | .mk (.var n) ann => (Γ n).bind (guardAnn ann)
  | .mk (.letBind n v b) ann =>
      (check sig Γ v).bind fun τ₁ =>
        if fitsB Γ n τ₁ then (check sig (Γ.extend n τ₁) b).bind (guardAnn ann) else none
  | .mk (.lam ps b) ann =>
      match ann with
      | .fn ts r =>
          if ps.length == ts.length && fitsListB Γ (ps.zip ts) then
            (check sig (Γ.extendList (ps.zip ts)) b).bind fun r' =>
              if ImpType.beq r' r then some (.fn ts r) else none
          else none
      | _ => none
  | .mk (.app f args) ann =>
      (sig f).bind fun tr =>
        (checkList sig Γ args).bind fun ts' =>
          if ImpType.beq (.tuple ts') (.tuple tr.1) then guardAnn ann tr.2 else none
  | .mk (.tuple es) ann => (checkList sig Γ es).bind fun ts => guardAnn ann (.tuple ts)
  | .mk (.proj e i) ann =>
      (check sig Γ e).bind fun τe =>
        match τe with
        | .tuple ts => ts[i]?.bind (guardAnn ann)
        | .array t n => if i < n then guardAnn ann t else none
        | _ => none
  | .mk (.ifThenElse c t e) ann =>
      (check sig Γ c).bind fun τc => (check sig Γ t).bind fun τt =>
        (check sig Γ e).bind fun τe =>
          if ImpType.beq τc .bool && ImpType.beq τe τt then guardAnn ann τt else none
  | .mk (.match_ s arms) ann =>
      (check sig Γ s).bind fun σs => (checkArms sig Γ σs arms).bind (guardAnn ann)
  | .mk .unitVal ann => guardAnn ann .unit
  | .mk (.seq e₁ e₂) ann =>
      (check sig Γ e₁).bind fun _ => (check sig Γ e₂).bind (guardAnn ann)
  | .mk (.ann e) a => (check sig Γ e).bind (guardAnn a)
  | .mk (.forFold v lo hi b) ann =>
      (check sig Γ lo).bind fun τi => (check sig Γ hi).bind fun τh =>
        if τi.isIntLike && ImpType.beq τh τi && fitsB Γ v τi then
          (check sig (Γ.extend v τi) b).bind (guardAnn ann)
        else none
  | .mk (.forFoldRev v lo hi b) ann =>
      (check sig Γ lo).bind fun τi => (check sig Γ hi).bind fun τh =>
        if τi.isIntLike && ImpType.beq τh τi && fitsB Γ v τi then
          (check sig (Γ.extend v τi) b).bind (guardAnn ann)
        else none
  | .mk (.whileFold c b) ann =>
      (check sig Γ c).bind fun τc => (check sig Γ b).bind fun τ =>
        if ImpType.beq τc .bool then guardAnn ann τ else none
  | .mk (.borrow _) _ | .mk (.deref _) _ | .mk (.assign _ _) _
  | .mk (.forLoop _ _ _ _) _ | .mk (.forLoopRev _ _ _ _) _ | .mk (.whileLoop _ _) _
  | .mk (.break_ _) _ | .mk .continue_ _ | .mk (.earlyReturn _) _
  | .mk (.questionMark _) _ | .mk (.forFoldReturn _ _ _ _) _
  | .mk (.forFoldRevReturn _ _ _ _) _ | .mk (.whileFoldReturn _ _) _ | .mk (.cfBreak _) _
  | .mk (.cfContinue _) _ | .mk (.cfBreakContinue _) _ | .mk (.namedProj _ _) _ => none

/-- `check` pointwise on a list of expressions. -/
def checkList (sig : Sig) (Γ : TyEnv) : List TExpr → Option (List ImpType)
  | [] => some []
  | e :: es => (check sig Γ e).bind fun τ => (checkList sig Γ es).bind fun ts => some (τ :: ts)

/-- The common type of the bodies of the match arms at the scrutinee type `σs`; `none` on
    an empty list. -/
def checkArms (sig : Sig) (Γ : TyEnv) (σs : ImpType) :
    List (ImpPat × TExpr) → Option ImpType
  | [] => none
  | (p, b) :: rest =>
      (checkPat p σs).bind fun bs =>
        if fitsListB Γ bs then
          (check sig (Γ.extendList bs) b).bind fun τ =>
            match rest with
            | [] => some τ
            | _ :: _ => (checkArms sig Γ σs rest).bind fun τ' =>
                if ImpType.beq τ' τ then some τ else none
        else none
end

/-! ## Soundness of the checker -/

theorem annB_ok {ann τ : ImpType} (h : annB ann τ = true) : AnnOK ann τ := by
  simp only [annB, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (eq_of_beq _ _ h)
  · exact Or.inr (eq_of_beq _ _ h)

theorem guardAnn_some {ann τ τ' : ImpType} (h : guardAnn ann τ = some τ') :
    AnnOK ann τ ∧ τ' = τ := by
  unfold guardAnn at h
  split at h
  · cases h; exact ⟨annB_ok ‹_›, rfl⟩
  · cases h

theorem fitsB_le {Γ Δ : TyEnv} {n : String} {τ : ImpType} (hΔ : TyEnv.Le Γ Δ)
    (h : fitsB Γ n τ = true) : TyEnv.Le Γ (Δ.extend n τ) := by
  intro x τ' hx
  unfold TyEnv.extend
  by_cases hxn : x = n
  · subst hxn
    unfold fitsB at h
    rw [hx] at h
    simp only [beq_self_eq_true, if_true]
    rw [eq_of_beq _ _ h]
  · simp only [beq_iff_eq, hxn, if_false]
    exact hΔ x τ' hx

theorem fitsListB_le {Γ : TyEnv} {bs : List (String × ImpType)}
    (h : fitsListB Γ bs = true) : TyEnv.Le Γ (Γ.extendList bs) := by
  suffices ∀ Δ, TyEnv.Le Γ Δ → TyEnv.Le Γ (Δ.extendList bs) from this Γ (TyEnv.Le.refl Γ)
  induction bs with
  | nil => exact fun Δ hΔ => hΔ
  | cons b bs ih =>
    intro Δ hΔ
    simp only [fitsListB, List.all_cons, Bool.and_eq_true] at h
    exact ih h.2 _ (fitsB_le hΔ h.1)

mutual
theorem checkPat_sound : (p : ImpPat) → (τ : ImpType) → (bs : List (String × ImpType)) →
    checkPat p τ = some bs → PatHasType p τ bs
  | .wildcard, τ, bs, h => by cases h; exact .wildcard τ
  | .varPat n, τ, bs, h => by cases h; exact .var n τ
  | .litPat l, τ, bs, h => by
      simp only [checkPat] at h
      split at h
      · rename_i hb; cases h; rw [eq_of_beq _ _ hb]; exact .lit l
      · cases h
  | .nonePat, τ, bs, h => by
      cases τ <;> simp only [checkPat, reduceCtorEq] at h
      cases h; exact .none _
  | .somePat p, τ, bs, h => by
      cases τ <;> simp only [checkPat, reduceCtorEq] at h
      exact .some (checkPat_sound _ _ _ h)
  | .tuplePat ps, τ, bs, h => by
      cases τ <;> simp only [checkPat, reduceCtorEq] at h
      exact .tuple (checkPatList_sound _ _ _ h)
  | .okPat _, τ, bs, h => by cases τ <;> simp only [checkPat, reduceCtorEq] at h
  | .errPat _, τ, bs, h => by cases τ <;> simp only [checkPat, reduceCtorEq] at h
  | .ctorPat _ _, τ, bs, h => by cases τ <;> simp only [checkPat, reduceCtorEq] at h

theorem checkPatList_sound : (ps : List ImpPat) → (ts : List ImpType) →
    (bs : List (String × ImpType)) → checkPatList ps ts = some bs → PatListHasType ps ts bs
  | [], [], bs, h => by cases h; exact .nil
  | p :: ps, t :: ts, bs, h => by
      simp only [checkPatList, bind, Option.bind_eq_some_iff, pure] at h
      obtain ⟨b₁, h₁, b₂, h₂, h₃⟩ := h
      cases h₃
      exact .cons (checkPat_sound _ _ _ h₁) (checkPatList_sound _ _ _ h₂)
  | [], _ :: _, bs, h => by cases h
  | _ :: _, [], bs, h => by cases h
end

theorem beq_tuple_eq {ts ts' : List ImpType} (h : ImpType.beq (.tuple ts') (.tuple ts) = true) :
    ts' = ts := by
  have := eq_of_beq _ _ h
  injection this

mutual
/-- **Soundness of the checker.** -/
theorem check_sound (sig : Sig) : (Γ : TyEnv) → (e : TExpr) → (τ : ImpType) →
    check sig Γ e = some τ → HasType sig Γ e τ
  | Γ, .mk (.lit l) ann, τ, h => by
      simp only [check] at h
      obtain ⟨ha, rfl⟩ := guardAnn_some h
      exact .lit ha
  | Γ, .mk (.var n) ann, τ, h => by
      simp only [check, Option.bind_eq_some_iff] at h
      obtain ⟨τ', hn, hg⟩ := h
      obtain ⟨ha, rfl⟩ := guardAnn_some hg
      exact .var hn ha
  | Γ, .mk (.letBind n v b) ann, τ, h => by
      simp only [check, Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, hv, hb⟩ := h
      split at hb
      · rename_i hf
        simp only [Option.bind_eq_some_iff] at hb
        obtain ⟨τ', hb', hg⟩ := hb
        obtain ⟨ha, rfl⟩ := guardAnn_some hg
        exact .letBind (check_sound sig Γ v τ₁ hv) (fitsB_le (TyEnv.Le.refl Γ) hf)
          (check_sound sig _ b _ hb') ha
      · cases hb
  | Γ, .mk (.lam ps b) ann, τ, h => by
      simp only [check] at h
      split at h
      · rename_i ts r
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨r', hb, hr⟩ := h
          split at hr
          · rename_i hrr
            cases hr
            rw [eq_of_beq _ _ hrr] at hb
            exact .lam hc.1 (fitsListB_le hc.2) (check_sound sig _ b r hb) (Or.inr rfl)
          · cases hr
        · cases h
      · cases h
  | Γ, .mk (.app f args) ann, τ, h => by
      simp only [check, Option.bind_eq_some_iff] at h
      obtain ⟨⟨ts, r⟩, hf, ts', hl, hc⟩ := h
      split at hc
      · rename_i hb
        obtain ⟨ha, rfl⟩ := guardAnn_some hc
        rw [beq_tuple_eq hb] at hl
        exact .app hf (checkList_sound sig Γ args ts hl) ha
      · cases hc
  | Γ, .mk (.tuple es) ann, τ, h => by
      simp only [check, Option.bind_eq_some_iff] at h
      obtain ⟨ts, hl, hg⟩ := h
      obtain ⟨ha, rfl⟩ := guardAnn_some hg
      exact .tuple (checkList_sound sig Γ es ts hl) ha
  | Γ, .mk (.proj e i) ann, τ, h => by
      simp only [check, Option.bind_eq_some_iff] at h
      obtain ⟨τe, he, hm⟩ := h
      split at hm
      · rename_i ts
        simp only [Option.bind_eq_some_iff] at hm
        obtain ⟨τ', hi, hg⟩ := hm
        obtain ⟨ha, rfl⟩ := guardAnn_some hg
        exact .projTuple (check_sound sig Γ e _ he) hi ha
      · split at hm
        · rename_i hi
          obtain ⟨ha, rfl⟩ := guardAnn_some hm
          exact .projArray (check_sound sig Γ e _ he) hi ha
        · cases hm
      · cases hm
  | Γ, .mk (.ifThenElse c t e) ann, τ, h => by
      simp only [check, Option.bind_eq_some_iff] at h
      obtain ⟨τc, hc, τt, ht, τe, he, hg⟩ := h
      split at hg
      · rename_i hb
        simp only [Bool.and_eq_true] at hb
        obtain ⟨ha, rfl⟩ := guardAnn_some hg
        rw [eq_of_beq _ _ hb.1] at hc
        rw [eq_of_beq _ _ hb.2] at he
        exact .ifThenElse (check_sound sig Γ c _ hc) (check_sound sig Γ t _ ht)
          (check_sound sig Γ e _ he) ha
      · cases hg
  | Γ, .mk (.match_ s arms) ann, τ, h => by
      simp only [check, Option.bind_eq_some_iff] at h
      obtain ⟨σs, hs, τ', harms, hg⟩ := h
      obtain ⟨ha, rfl⟩ := guardAnn_some hg
      exact .match_ (check_sound sig Γ s σs hs) (checkArms_sound sig Γ σs arms _ harms) ha
  | Γ, .mk .unitVal ann, τ, h => by
      simp only [check] at h
      obtain ⟨ha, rfl⟩ := guardAnn_some h
      exact .unitVal ha
  | Γ, .mk (.seq e₁ e₂) ann, τ, h => by
      simp only [check, Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, hg⟩ := h
      obtain ⟨ha, rfl⟩ := guardAnn_some hg
      exact .seq (check_sound sig Γ e₁ τ₁ h₁) (check_sound sig Γ e₂ _ h₂) ha
  | Γ, .mk (.ann e) a, τ, h => by
      simp only [check, Option.bind_eq_some_iff] at h
      obtain ⟨τ', he, hg⟩ := h
      obtain ⟨ha, rfl⟩ := guardAnn_some hg
      exact .ann (check_sound sig Γ e _ he) ha
  | Γ, .mk (.forFold v lo hi b) ann, τ, h => by
      simp only [check, Option.bind_eq_some_iff] at h
      obtain ⟨τi, hlo, τh, hhi, hb⟩ := h
      split at hb
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        simp only [Option.bind_eq_some_iff] at hb
        obtain ⟨τ', hb', hg⟩ := hb
        obtain ⟨ha, rfl⟩ := guardAnn_some hg
        rw [eq_of_beq _ _ hc.1.2] at hhi
        exact .forFold hc.1.1 (check_sound sig Γ lo τi hlo) (check_sound sig Γ hi τi hhi)
          (fitsB_le (TyEnv.Le.refl Γ) hc.2) (check_sound sig _ b _ hb') ha
      · cases hb
  | Γ, .mk (.forFoldRev v lo hi b) ann, τ, h => by
      simp only [check, Option.bind_eq_some_iff] at h
      obtain ⟨τi, hlo, τh, hhi, hb⟩ := h
      split at hb
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        simp only [Option.bind_eq_some_iff] at hb
        obtain ⟨τ', hb', hg⟩ := hb
        obtain ⟨ha, rfl⟩ := guardAnn_some hg
        rw [eq_of_beq _ _ hc.1.2] at hhi
        exact .forFoldRev hc.1.1 (check_sound sig Γ lo τi hlo) (check_sound sig Γ hi τi hhi)
          (fitsB_le (TyEnv.Le.refl Γ) hc.2) (check_sound sig _ b _ hb') ha
      · cases hb
  | Γ, .mk (.whileFold c b) ann, τ, h => by
      simp only [check, Option.bind_eq_some_iff] at h
      obtain ⟨τc, hc, τ', hb, hg⟩ := h
      split at hg
      · rename_i hcb
        obtain ⟨ha, rfl⟩ := guardAnn_some hg
        rw [eq_of_beq _ _ hcb] at hc
        exact .whileFold (check_sound sig Γ c _ hc) (check_sound sig Γ b _ hb) ha
      · cases hg
  | _, .mk (.borrow _) _, _, h | _, .mk (.deref _) _, _, h | _, .mk (.assign _ _) _, _, h
  | _, .mk (.forLoop _ _ _ _) _, _, h | _, .mk (.forLoopRev _ _ _ _) _, _, h
  | _, .mk (.whileLoop _ _) _, _, h | _, .mk (.break_ _) _, _, h | _, .mk .continue_ _, _, h
  | _, .mk (.earlyReturn _) _, _, h | _, .mk (.questionMark _) _, _, h
  | _, .mk (.forFoldReturn _ _ _ _) _, _, h | _, .mk (.forFoldRevReturn _ _ _ _) _, _, h
  | _, .mk (.whileFoldReturn _ _) _, _, h | _, .mk (.cfBreak _) _, _, h
  | _, .mk (.cfContinue _) _, _, h | _, .mk (.cfBreakContinue _) _, _, h
  | _, .mk (.namedProj _ _) _, _, h => by simp [check] at h

/-- Soundness of `checkList`. -/
theorem checkList_sound (sig : Sig) : (Γ : TyEnv) → (es : List TExpr) → (ts : List ImpType) →
    checkList sig Γ es = some ts → HasTypeList sig Γ es ts
  | Γ, [], ts, h => by cases h; exact .nil
  | Γ, e :: es, ts, h => by
      simp only [checkList, Option.bind_eq_some_iff] at h
      obtain ⟨τ, he, ts', hes, hts⟩ := h
      cases hts
      exact .cons (check_sound sig Γ e τ he) (checkList_sound sig Γ es ts' hes)

/-- Soundness of `checkArms`. -/
theorem checkArms_sound (sig : Sig) : (Γ : TyEnv) → (σs : ImpType) →
    (arms : List (ImpPat × TExpr)) → (τ : ImpType) →
    checkArms sig Γ σs arms = some τ → HasTypeArms sig Γ σs arms τ
  | Γ, σs, [], τ, h => by cases h
  | Γ, σs, (p, b) :: rest, τ, h => by
      simp only [checkArms, Option.bind_eq_some_iff] at h
      obtain ⟨bs, hp, hr⟩ := h
      split at hr
      · rename_i hf
        simp only [Option.bind_eq_some_iff] at hr
        obtain ⟨τ₀, hb, hm⟩ := hr
        split at hm
        · cases hm
          exact .cons (checkPat_sound _ _ _ hp) (fitsListB_le hf)
            (check_sound sig _ b _ hb) .nil
        · simp only [Option.bind_eq_some_iff] at hm
          obtain ⟨τ', hrest, hif⟩ := hm
          split at hif
          · rename_i hbeq
            cases hif
            rw [eq_of_beq _ _ hbeq] at hrest
            exact .cons (checkPat_sound _ _ _ hp) (fitsListB_le hf)
              (check_sound sig _ b _ hb) (checkArms_sound sig Γ σs _ _ hrest)
          · cases hif
      · cases hr
end

/-! ## Value typing -/

/-- The types whose values `Value.HasType` leaves to the interpretation `O`: type
    parameters, named types, strings, functions and `.unknown`. -/
inductive IsOpaque : ImpType → Prop where
  | typeVar (n : String) : IsOpaque (.typeVar n)
  | adt (n : String) (as : List ImpType) : IsOpaque (.adt n as)
  | str : IsOpaque .str
  | fn (ps : List ImpType) (r : ImpType) : IsOpaque (.fn ps r)
  | unknown : IsOpaque .unknown

mutual
/-- `Value.HasType O v τ`: the value `v` has type `τ`, where a value of an opaque type `τ`
    is one satisfying `O τ`. An unsigned value lies below the modulus of its width; a
    reference type has the values of its target type. -/
inductive Value.HasType (O : ImpType → Value → Prop) : Value → ImpType → Prop where
  | bool (b : Bool) : Value.HasType O (.bool b) .bool
  | int (n : Int) : Value.HasType O (.int n) .int
  | uint {w : IntWidth} {n : Nat} : n < w.modulus → Value.HasType O (.uint w n) (.uint w)
  | sint (w : IntWidth) (n : Int) : Value.HasType O (.sint w n) (.sint w)
  | unit : Value.HasType O .unit .unit
  | tuple {vs : List Value} {ts : List ImpType} :
      Value.HasTypeList O vs ts → Value.HasType O (.tuple vs) (.tuple ts)
  | array {vs : List Value} {t : ImpType} {n : Nat} :
      Value.HasTypeAll O vs t → vs.length = n → Value.HasType O (.array vs) (.array t n)
  | slice {vs : List Value} {t : ImpType} :
      Value.HasTypeAll O vs t → Value.HasType O (.array vs) (.slice t)
  | none (t : ImpType) : Value.HasType O (.option none) (.option t)
  | some {v : Value} {t : ImpType} :
      Value.HasType O v t → Value.HasType O (.option (some v)) (.option t)
  | ok {v : Value} {a b : ImpType} :
      Value.HasType O v a → Value.HasType O (.result true v) (.result a b)
  | err {v : Value} {a b : ImpType} :
      Value.HasType O v b → Value.HasType O (.result false v) (.result a b)
  | brk {v : Value} {a b : ImpType} :
      Value.HasType O v a → Value.HasType O (.controlFlow true v) (.controlFlow a b)
  | cont {v : Value} {a b : ImpType} :
      Value.HasType O v b → Value.HasType O (.controlFlow false v) (.controlFlow a b)
  | ref {v : Value} {t : ImpType} {m : Bool} :
      Value.HasType O v t → Value.HasType O v (.ref t m)
  | ofOpaque {v : Value} {t : ImpType} : IsOpaque t → O t v → Value.HasType O v t

/-- `Value.HasTypeList O vs ts`: the values `vs` have the types `ts` pointwise. -/
inductive Value.HasTypeList (O : ImpType → Value → Prop) : List Value → List ImpType → Prop where
  | nil : Value.HasTypeList O [] []
  | cons {v : Value} {vs : List Value} {t : ImpType} {ts : List ImpType} :
      Value.HasType O v t → Value.HasTypeList O vs ts → Value.HasTypeList O (v :: vs) (t :: ts)

/-- `Value.HasTypeAll O vs t`: every value of `vs` has type `t`. -/
inductive Value.HasTypeAll (O : ImpType → Value → Prop) : List Value → ImpType → Prop where
  | nil (t : ImpType) : Value.HasTypeAll O [] t
  | cons {v : Value} {vs : List Value} {t : ImpType} :
      Value.HasType O v t → Value.HasTypeAll O vs t → Value.HasTypeAll O (v :: vs) t
end

variable {O : ImpType → Value → Prop}

theorem Value.HasTypeList.getElem? : {vs : List Value} → {ts : List ImpType} →
    Value.HasTypeList O vs ts → {i : Nat} → {τ : ImpType} → ts[i]? = some τ →
    ∃ v, vs[i]? = some v ∧ Value.HasType O v τ
  | _, _, .nil, _, _, hi => by simp at hi
  | _, _, .cons hv _, 0, _, hi => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi ⊢; subst hi
      exact ⟨_, rfl, hv⟩
  | _, _, .cons _ hvs, i + 1, _, hi => by
      simp only [List.getElem?_cons_succ] at hi ⊢; exact Value.HasTypeList.getElem? hvs hi

theorem Value.HasTypeAll.getElem? : {vs : List Value} → {t : ImpType} →
    Value.HasTypeAll O vs t → {i : Nat} → i < vs.length →
    ∃ v, vs[i]? = some v ∧ Value.HasType O v t
  | _, _, .nil _, _, hi => by simp at hi
  | _, _, .cons hv _, 0, _ => ⟨_, rfl, hv⟩
  | _, _, .cons _ hvs, i + 1, hi => by
      simp only [List.getElem?_cons_succ]
      exact Value.HasTypeAll.getElem? hvs (by simpa using hi)

theorem ofLit_hasType (l : ImpLit) : Value.HasType O (Value.ofLit l) (litTy l) := by
  cases l with
  | bool b => exact .bool b
  | int n => exact .int n
  | unit => exact .unit
  | uintLit w n => exact .uint (Nat.mod_lt _ (Nat.two_pow_pos _))
  | sintLit w n => exact .sint w n

/-! ## Typed environments and runs -/

/-- Every variable that `Γ` binds holds a value of its type in `env`. -/
def EnvHasType (O : ImpType → Value → Prop) (Γ : TyEnv) (env : Env) : Prop :=
  ∀ x τ, Γ x = some τ → ∃ v, env x = some v ∧ Value.HasType O v τ

/-- An outcome of type `τ`: a value of type `τ`, or an error. -/
def OutcomeHasType (O : ImpType → Value → Prop) : Outcome → ImpType → Prop
  | .val v, τ => Value.HasType O v τ
  | .err _, _ => True
  | _, _ => False

/-- A run of type `τ` under `Γ`: its outcome has type `τ` and its exit environment is typed
    by `Γ`. -/
def RunHasType (O : ImpType → Value → Prop) (Γ : TyEnv) (τ : ImpType)
    (r : Outcome × Env) : Prop :=
  OutcomeHasType O r.1 τ ∧ EnvHasType O Γ r.2

/-- A run of an argument list of types `ts` under `Γ`: the values it returns have the types
    `ts` and its exit environment is typed by `Γ`. -/
def ArgsRunHasType (O : ImpType → Value → Prop) (Γ : TyEnv) (ts : List ImpType)
    (r : Option (List Value) × Env) : Prop :=
  (∀ vs, r.1 = some vs → Value.HasTypeList O vs ts) ∧ EnvHasType O Γ r.2

/-- The builtin table `bi` returns, on arguments of the parameter types of a signature in
    `sig`, only values of its result type. -/
def BuiltinsRespect (O : ImpType → Value → Prop) (sig : Sig) (bi : Builtins) : Prop :=
  ∀ f ts r, sig f = some (ts, r) → ∀ vs, Value.HasTypeList O vs ts →
    ∀ v, bi f vs = some v → Value.HasType O v r

theorem EnvHasType.mono {Γ Γ' : TyEnv} {env : Env} (hle : TyEnv.Le Γ Γ')
    (h : EnvHasType O Γ' env) : EnvHasType O Γ env :=
  fun x τ hx => h x τ (hle x τ hx)

theorem EnvHasType.extend {Γ : TyEnv} {env : Env} {n : String} {v : Value} {τ : ImpType}
    (h : EnvHasType O Γ env) (hv : Value.HasType O v τ) :
    EnvHasType O (Γ.extend n τ) (env.extend n v) := by
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

theorem OutcomeHasType.of_not_val {o : Outcome} {τ τ' : ImpType}
    (h : OutcomeHasType O o τ) (hv : ∀ v, o ≠ .val v) : OutcomeHasType O o τ' := by
  cases o with
  | val v => exact absurd rfl (hv v)
  | err _ => trivial
  | _ => exact h.elim

mutual
/-- A successful match of a pattern of type `σ` against a value of type `σ` extends a typed
    environment to one typed by the pattern's bindings. -/
theorem matchPat_sound {Γ : TyEnv} : {p : ImpPat} → {σ : ImpType} →
    {bs : List (String × ImpType)} → PatHasType p σ bs → {v : Value} →
    Value.HasType O v σ → {env env' : Env} → matchPat p v env = some env' →
    EnvHasType O Γ env → EnvHasType O (Γ.extendList bs) env'
  | _, _, _, .wildcard _, v, _, env, env', hm, henv => by
      simp only [matchPat, Option.some.injEq] at hm; subst hm; exact henv
  | _, _, _, .var n _, v, hv, env, env', hm, henv => by
      simp only [matchPat, Option.some.injEq] at hm; subst hm
      exact henv.extend hv
  | _, _, _, .lit l, v, _, env, env', hm, henv => by
      simp only [matchPat] at hm
      split at hm
      · cases hm; exact henv
      · cases hm
  | _, _, _, .none _, v, hv, env, env', hm, henv => by
      cases hv with
      | none => simp only [matchPat, Option.some.injEq] at hm; subst hm; exact henv
      | some _ => simp [matchPat] at hm
      | ofOpaque ho _ => cases ho
  | _, _, _, .some hp, v, hv, env, env', hm, henv => by
      cases hv with
      | none => simp [matchPat] at hm
      | some hw => simp only [matchPat] at hm; exact matchPat_sound hp hw hm henv
      | ofOpaque ho _ => cases ho
  | _, _, _, .tuple hps, v, hv, env, env', hm, henv => by
      cases hv with
      | tuple hvs =>
        simp only [matchPat] at hm
        split at hm
        · cases hm
        · exact matchPatList_sound hps hvs hm henv
      | ofOpaque ho _ => cases ho

/-- `matchPat_sound` for a list of patterns. -/
theorem matchPatList_sound {Γ : TyEnv} : {ps : List ImpPat} → {ts : List ImpType} →
    {bs : List (String × ImpType)} → PatListHasType ps ts bs → {vs : List Value} →
    Value.HasTypeList O vs ts → {env env' : Env} → matchPat.matchPatList ps vs env = some env' →
    EnvHasType O Γ env → EnvHasType O (Γ.extendList bs) env'
  | _, _, _, .nil, _, .nil, env, env', hm, henv => by
      simp only [matchPat.matchPatList, Option.some.injEq] at hm; subst hm; exact henv
  | _, _, _, .cons hp hps, _, .cons hv hvs, env, env', hm, henv => by
      simp only [matchPat.matchPatList, bind, Option.bind_eq_some_iff] at hm
      obtain ⟨env₁, h₁, h₂⟩ := hm
      rw [TyEnv.extendList_append]
      exact matchPatList_sound hps hvs h₂ (matchPat_sound hp hv h₁ henv)
end

/-! ## Type soundness -/

variable {sig : Sig} {bi : Builtins} {fuel : Nat}

theorem RunHasType.of_err {Γ : TyEnv} {τ : ImpType} {msg : String} {env : Env}
    (henv : EnvHasType O Γ env) : RunHasType O Γ τ (.err msg, env) := ⟨trivial, henv⟩

mutual
/-- **Type soundness.** From an environment typed by `Γ`, under builtins respecting `sig`,
    the run of `denote` on the erasure of an expression of type `τ` returns a value of type
    `τ` or an error, and its exit environment is typed by `Γ`, at every fuel. -/
theorem HasType.sound (hbi : BuiltinsRespect O sig bi) : {Γ : TyEnv} → {e : TExpr} →
    {τ : ImpType} → HasType sig Γ e τ → (env : Env) → EnvHasType O Γ env →
    RunHasType O Γ τ (denote bi fuel e.erase env)
  | _, _, _, .lit _, env, henv => by
      simp only [TExpr.erase]; rw [denote]
      exact ⟨ofLit_hasType _, henv⟩
  | _, _, _, @HasType.var _ _ n _ _ hn _, env, henv => by
      simp only [TExpr.erase]; rw [denote]
      obtain ⟨v, hv, hvt⟩ := henv n _ hn
      simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        StateT.pure, hv]
      exact ⟨hvt, henv⟩
  | _, _, _, @HasType.letBind _ _ n v b _ _ _ hv hle hb _, env, henv => by
      simp only [TExpr.erase]; rw [denote]
      have ihv := HasType.sound hbi hv env henv
      simp only [bind, StateT.bind]
      rcases hr : denote bi fuel v.erase env with ⟨o, env₁⟩
      rw [hr] at ihv
      obtain ⟨ho, henv₁⟩ := ihv
      cases o with
      | val w =>
        simp only [modify, modifyGet, MonadStateOf.modifyGet]
        have ihb := HasType.sound hbi hb _ (henv₁.extend (n := n) ho)
        exact ⟨ihb.1, ihb.2.mono hle⟩
      | err _ => exact ⟨trivial, henv₁⟩
      | _ => exact ho.elim
  | _, _, _, .lam _ _ _ _, env, henv => by
      simp only [TExpr.erase]; rw [denote]; exact ⟨trivial, henv⟩
  | _, _, _, @HasType.app _ _ f args _ _ _ hf hargs _, env, henv => by
      simp only [TExpr.erase, TExpr.eraseList_eq]; rw [denote]
      have iha := HasTypeList.sound hbi hargs env henv
      simp only [bind, StateT.bind]
      rcases hr : denoteArgs bi fuel (args.map TExpr.erase) env with ⟨ro, env₁⟩
      rw [hr] at iha
      obtain ⟨hvs, henv₁⟩ := iha
      cases ro with
      | none => exact ⟨trivial, henv₁⟩
      | some vals =>
        dsimp only
        rcases hb : bi f vals with _ | w
        · exact ⟨trivial, henv₁⟩
        · exact ⟨hbi f _ _ hf vals (hvs vals rfl) w hb, henv₁⟩
  | _, _, _, @HasType.tuple _ _ es _ _ hes _, env, henv => by
      simp only [TExpr.erase, TExpr.eraseList_eq]; rw [denote]
      have iha := HasTypeList.sound hbi hes env henv
      simp only [bind, StateT.bind]
      rcases hr : denoteArgs bi fuel (es.map TExpr.erase) env with ⟨ro, env₁⟩
      rw [hr] at iha
      obtain ⟨hvs, henv₁⟩ := iha
      cases ro with
      | none => exact ⟨trivial, henv₁⟩
      | some vals => exact ⟨.tuple (hvs vals rfl), henv₁⟩
  | _, _, _, @HasType.projTuple _ _ e i _ _ _ he hi _, env, henv => by
      simp only [TExpr.erase]; rw [denote]
      have ihe := HasType.sound hbi he env henv
      simp only [bind, StateT.bind]
      rcases hr : denote bi fuel e.erase env with ⟨o, env₁⟩
      rw [hr] at ihe
      obtain ⟨ho, henv₁⟩ := ihe
      cases o with
      | val w =>
        cases ho with
        | tuple hvs =>
          obtain ⟨u, hu, hut⟩ := hvs.getElem? hi
          simp only [Value.projIdx, hu]
          exact ⟨hut, henv₁⟩
        | ofOpaque hop _ => cases hop
      | err _ => exact ⟨trivial, henv₁⟩
      | _ => exact ho.elim
  | _, _, _, @HasType.projArray _ _ e i _ _ _ he hi _, env, henv => by
      simp only [TExpr.erase]; rw [denote]
      have ihe := HasType.sound hbi he env henv
      simp only [bind, StateT.bind]
      rcases hr : denote bi fuel e.erase env with ⟨o, env₁⟩
      rw [hr] at ihe
      obtain ⟨ho, henv₁⟩ := ihe
      cases o with
      | val w =>
        cases ho with
        | array hvs hlen =>
          obtain ⟨u, hu, hut⟩ := hvs.getElem? (hlen ▸ hi)
          simp only [Value.projIdx, hu]
          exact ⟨hut, henv₁⟩
        | ofOpaque hop _ => cases hop
      | err _ => exact ⟨trivial, henv₁⟩
      | _ => exact ho.elim
  | _, _, _, @HasType.ifThenElse _ _ c t e _ _ hc ht he _, env, henv => by
      simp only [TExpr.erase]; rw [denote]
      have ihc := HasType.sound hbi hc env henv
      simp only [bind, StateT.bind]
      rcases hr : denote bi fuel c.erase env with ⟨o, env₁⟩
      rw [hr] at ihc
      obtain ⟨ho, henv₁⟩ := ihc
      cases o with
      | val w =>
        cases ho with
        | bool b =>
          cases b
          · exact HasType.sound hbi he env₁ henv₁
          · exact HasType.sound hbi ht env₁ henv₁
        | ofOpaque hop _ => cases hop
      | err _ => exact ⟨trivial, henv₁⟩
      | _ => exact ho.elim
  | _, _, _, @HasType.match_ _ _ s arms _ _ _ hs harms _, env, henv => by
      simp only [TExpr.erase, TExpr.eraseArms_eq]; rw [denote]
      have ihs := HasType.sound hbi hs env henv
      simp only [bind, StateT.bind]
      rcases hr : denote bi fuel s.erase env with ⟨o, env₁⟩
      rw [hr] at ihs
      obtain ⟨ho, henv₁⟩ := ihs
      cases o with
      | val w => exact HasTypeArms.sound hbi harms w ho env₁ henv₁
      | err _ => exact ⟨trivial, henv₁⟩
      | _ => exact ho.elim
  | _, _, _, .unitVal _, env, henv => by
      simp only [TExpr.erase]; rw [denote]; exact ⟨.unit, henv⟩
  | _, _, _, @HasType.seq _ _ e₁ e₂ _ _ _ h₁ h₂ _, env, henv => by
      simp only [TExpr.erase]; rw [denote]
      have ih₁ := HasType.sound hbi h₁ env henv
      simp only [bind, StateT.bind]
      rcases hr : denote bi fuel e₁.erase env with ⟨o, env₁⟩
      rw [hr] at ih₁
      obtain ⟨ho, henv₁⟩ := ih₁
      cases o with
      | val w => exact HasType.sound hbi h₂ env₁ henv₁
      | err _ => exact ⟨trivial, henv₁⟩
      | _ => exact ho.elim
  | _, _, _, .ann he _, env, henv => by
      simp only [TExpr.erase]; exact HasType.sound hbi he env henv
  | _, _, _, .forFold _ _ _ _ _ _, env, henv => by
      simp only [TExpr.erase]; rw [denote]; exact ⟨trivial, henv⟩
  | _, _, _, .forFoldRev _ _ _ _ _ _, env, henv => by
      simp only [TExpr.erase]; rw [denote]; exact ⟨trivial, henv⟩
  | _, _, _, .whileFold _ _ _, env, henv => by
      simp only [TExpr.erase]; rw [denote]; exact ⟨trivial, henv⟩

/-- Type soundness of `denoteArgs` on a typed argument list. -/
theorem HasTypeList.sound (hbi : BuiltinsRespect O sig bi) : {Γ : TyEnv} → {es : List TExpr} →
    {ts : List ImpType} → HasTypeList sig Γ es ts → (env : Env) → EnvHasType O Γ env →
    ArgsRunHasType O Γ ts (denoteArgs bi fuel (es.map TExpr.erase) env)
  | _, _, _, .nil, env, henv => by
      simp only [List.map_nil]; rw [denoteArgs]
      exact ⟨fun vs h => by cases h; exact .nil, henv⟩
  | _, _, _, @HasTypeList.cons _ _ e es _ _ he hes, env, henv => by
      simp only [List.map_cons]; rw [denoteArgs]
      have ihe := HasType.sound hbi he env henv
      simp only [bind, StateT.bind]
      rcases hr : denote bi fuel e.erase env with ⟨o, env₁⟩
      rw [hr] at ihe
      obtain ⟨ho, henv₁⟩ := ihe
      cases o with
      | val w =>
        have ihes := HasTypeList.sound hbi hes env₁ henv₁
        dsimp only
        rcases hr₂ : denoteArgs bi fuel (es.map TExpr.erase) env₁ with ⟨ro, env₂⟩
        rw [hr₂] at ihes
        obtain ⟨hvs, henv₂⟩ := ihes
        simp only [StateT.bind, hr₂, pure, StateT.pure]
        refine ⟨fun vs h => ?_, henv₂⟩
        cases ro with
        | none => exact absurd (show (none : Option (List Value)) = some vs from h) nofun
        | some rs =>
          cases (show some (w :: rs) = some vs from h)
          exact .cons ho (hvs rs rfl)
      | err _ => exact ⟨fun vs h => by simp [pure, StateT.pure] at h, henv₁⟩
      | earlyRet _ => exact ⟨fun vs h => by simp [pure, StateT.pure] at h, henv₁⟩
      | broke _ => exact ⟨fun vs h => by simp [pure, StateT.pure] at h, henv₁⟩
      | continued => exact ⟨fun vs h => by simp [pure, StateT.pure] at h, henv₁⟩

/-- Type soundness of `denoteMatchArms` on typed arms and a scrutinee value of their
    pattern type. -/
theorem HasTypeArms.sound (hbi : BuiltinsRespect O sig bi) : {Γ : TyEnv} → {σs : ImpType} →
    {arms : List (ImpPat × TExpr)} → {τ : ImpType} → HasTypeArms sig Γ σs arms τ →
    (v : Value) → Value.HasType O v σs → (env : Env) → EnvHasType O Γ env →
    RunHasType O Γ τ (denoteMatchArms bi fuel v (arms.map fun (p, e) => (p, e.erase)) env)
  | _, _, _, _, .nil, v, _, env, henv => by
      simp only [List.map_nil]; rw [denoteMatchArms]; exact ⟨trivial, henv⟩
  | _, _, _, _, @HasTypeArms.cons _ _ _ p b arms _ _ hp hle hb harms, v, hv, env, henv => by
      simp only [List.map_cons]; rw [denoteMatchArms]
      simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure]
      rcases hm : matchPat p v env with _ | env'
      · exact HasTypeArms.sound hbi harms v hv env henv
      · simp only [set]
        have ihb := HasType.sound hbi hb env' (matchPat_sound hp hv hm henv)
        exact ⟨ihb.1, ihb.2.mono hle⟩
end

/-! ## Instantiation of type parameters -/

/-- The type environment `Γ` with each type instantiated by `σ`. -/
def TyEnv.subst (σ : String → Option ImpType) (Γ : TyEnv) : TyEnv :=
  fun x => (Γ x).map (ImpType.substVars σ)

/-- The signature `sig` with each parameter and result type instantiated by `σ`. -/
def Sig.subst (σ : String → Option ImpType) (sig : Sig) : Sig :=
  fun f => (sig f).map fun tr => (tr.1.map (ImpType.substVars σ), ImpType.substVars σ tr.2)

section Subst

variable (σ : String → Option ImpType)

theorem substList_eq (ts : List ImpType) :
    ImpType.substVars.substList σ ts = ts.map (ImpType.substVars σ) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [ImpType.substVars.substList, ih, List.map_cons]

theorem substVars_tuple (ts : List ImpType) :
    ImpType.substVars σ (.tuple ts) = .tuple (ts.map (ImpType.substVars σ)) := by
  simp only [ImpType.substVars, substList_eq]

theorem substVars_fn (ts : List ImpType) (r : ImpType) :
    ImpType.substVars σ (.fn ts r) = .fn (ts.map (ImpType.substVars σ)) (ImpType.substVars σ r) := by
  simp only [ImpType.substVars, substList_eq]

theorem substVars_litTy (l : ImpLit) : ImpType.substVars σ (litTy l) = litTy l := by
  cases l <;> rfl

theorem substVars_of_isIntLike {τ : ImpType} (h : τ.isIntLike = true) :
    ImpType.substVars σ τ = τ := by
  cases τ <;> first | rfl | simp [ImpType.isIntLike] at h

theorem AnnOK.subst {ann τ : ImpType} (h : AnnOK ann τ) :
    AnnOK (ImpType.substVars σ ann) (ImpType.substVars σ τ) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem TyEnv.subst_extend (Γ : TyEnv) (n : String) (τ : ImpType) :
    (Γ.extend n τ).subst σ = (Γ.subst σ).extend n (ImpType.substVars σ τ) := by
  funext x
  simp only [TyEnv.subst, TyEnv.extend]
  split <;> rfl

theorem TyEnv.subst_extendList (Γ : TyEnv) (bs : List (String × ImpType)) :
    (Γ.extendList bs).subst σ =
      (Γ.subst σ).extendList (bs.map (Prod.map id (ImpType.substVars σ))) := by
  induction bs generalizing Γ with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨x, t⟩ := b
    simp only [TyEnv.extendList, List.map_cons, Prod.map, id]
    rw [ih, TyEnv.subst_extend]

theorem TyEnv.Le.subst {Γ Γ' : TyEnv} (h : TyEnv.Le Γ Γ') :
    TyEnv.Le (Γ.subst σ) (Γ'.subst σ) := by
  intro x τ hx
  simp only [TyEnv.subst, Option.map_eq_some_iff] at hx ⊢
  obtain ⟨τ₀, h₀, rfl⟩ := hx
  exact ⟨τ₀, h x τ₀ h₀, rfl⟩

mutual
theorem PatHasType.subst : {p : ImpPat} → {τ : ImpType} → {bs : List (String × ImpType)} →
    PatHasType p τ bs →
    PatHasType p (ImpType.substVars σ τ) (bs.map (Prod.map id (ImpType.substVars σ)))
  | _, _, _, .wildcard _ => .wildcard _
  | _, _, _, .var n _ => .var n _
  | _, _, _, .lit l => by rw [substVars_litTy]; exact .lit l
  | _, _, _, .none _ => .none _
  | _, _, _, .some hp => .some (PatHasType.subst hp)
  | _, _, _, .tuple hps => by rw [substVars_tuple]; exact .tuple (PatListHasType.subst hps)

theorem PatListHasType.subst : {ps : List ImpPat} → {ts : List ImpType} →
    {bs : List (String × ImpType)} → PatListHasType ps ts bs →
    PatListHasType ps (ts.map (ImpType.substVars σ)) (bs.map (Prod.map id (ImpType.substVars σ)))
  | _, _, _, .nil => .nil
  | _, _, _, .cons hp hps => by
      rw [List.map_append]
      exact .cons (PatHasType.subst hp) (PatListHasType.subst hps)
end

mutual
/-- **Typing is stable under instantiation of type parameters.** -/
theorem HasType.mapTy {sig : Sig} : {Γ : TyEnv} → {e : TExpr} → {τ : ImpType} →
    HasType sig Γ e τ →
    HasType (sig.subst σ) (Γ.subst σ) (TExpr.mapTy (ImpType.substVars σ) e)
      (ImpType.substVars σ τ)
  | _, _, _, .lit ha => by
      simp only [TExpr.mapTy, TExprKind.mapTy]
      have := ha.subst σ
      rw [substVars_litTy] at this ⊢
      exact .lit this
  | Γ, _, _, .var hn ha => by
      simp only [TExpr.mapTy, TExprKind.mapTy]
      exact .var (by simp [TyEnv.subst, hn]) (ha.subst σ)
  | Γ, _, _, .letBind hv hle hb ha => by
      simp only [TExpr.mapTy, TExprKind.mapTy]
      have hle' := hle.subst σ
      have hb' := HasType.mapTy hb
      rw [TyEnv.subst_extend] at hle' hb'
      exact .letBind (HasType.mapTy hv) hle' hb' (ha.subst σ)
  | Γ, _, _, .lam hlen hle hb ha => by
      simp only [TExpr.mapTy, TExprKind.mapTy]
      have hle' := hle.subst σ
      have hb' := HasType.mapTy hb
      have ha' := ha.subst σ
      rw [TyEnv.subst_extendList, ← List.zip_map_right] at hle' hb'
      rw [substVars_fn] at ha' ⊢
      exact .lam (by simpa using hlen) hle' hb' ha'
  | _, _, _, .app hf hargs ha => by
      simp only [TExpr.mapTy, TExprKind.mapTy]
      exact .app (by simp [Sig.subst, hf]) (HasTypeList.mapTy hargs) (ha.subst σ)
  | _, _, _, .tuple hes ha => by
      simp only [TExpr.mapTy, TExprKind.mapTy]
      have ha' := ha.subst σ
      rw [substVars_tuple] at ha' ⊢
      exact .tuple (HasTypeList.mapTy hes) ha'
  | _, _, _, .projTuple he hi ha => by
      simp only [TExpr.mapTy, TExprKind.mapTy]
      have he' := HasType.mapTy he
      rw [substVars_tuple] at he'
      exact .projTuple he' (by simp [List.getElem?_map, hi]) (ha.subst σ)
  | _, _, _, .projArray he hi ha => by
      simp only [TExpr.mapTy, TExprKind.mapTy]
      exact .projArray (HasType.mapTy he) hi (ha.subst σ)
  | _, _, _, .ifThenElse hc ht he ha => by
      simp only [TExpr.mapTy, TExprKind.mapTy]
      exact .ifThenElse (HasType.mapTy hc) (HasType.mapTy ht) (HasType.mapTy he) (ha.subst σ)
  | _, _, _, .match_ hs harms ha => by
      simp only [TExpr.mapTy, TExprKind.mapTy]
      exact .match_ (HasType.mapTy hs) (HasTypeArms.mapTy harms) (ha.subst σ)
  | _, _, _, .unitVal ha => by
      simp only [TExpr.mapTy, TExprKind.mapTy]
      exact .unitVal (ha.subst σ)
  | _, _, _, .seq h₁ h₂ ha => by
      simp only [TExpr.mapTy, TExprKind.mapTy]
      exact .seq (HasType.mapTy h₁) (HasType.mapTy h₂) (ha.subst σ)
  | _, _, _, .ann he ha => by
      simp only [TExpr.mapTy, TExprKind.mapTy]
      exact .ann (HasType.mapTy he) (ha.subst σ)
  | _, _, _, .forFold hi hlo hhi hle hb ha => by
      simp only [TExpr.mapTy, TExprKind.mapTy]
      have hle' := hle.subst σ
      have hb' := HasType.mapTy hb
      have hlo' := HasType.mapTy hlo
      have hhi' := HasType.mapTy hhi
      rw [TyEnv.subst_extend] at hle' hb'
      rw [substVars_of_isIntLike σ hi] at hle' hb' hlo' hhi'
      exact .forFold hi hlo' hhi' hle' hb' (ha.subst σ)
  | _, _, _, .forFoldRev hi hlo hhi hle hb ha => by
      simp only [TExpr.mapTy, TExprKind.mapTy]
      have hle' := hle.subst σ
      have hb' := HasType.mapTy hb
      have hlo' := HasType.mapTy hlo
      have hhi' := HasType.mapTy hhi
      rw [TyEnv.subst_extend] at hle' hb'
      rw [substVars_of_isIntLike σ hi] at hle' hb' hlo' hhi'
      exact .forFoldRev hi hlo' hhi' hle' hb' (ha.subst σ)
  | _, _, _, .whileFold hc hb ha => by
      simp only [TExpr.mapTy, TExprKind.mapTy]
      exact .whileFold (HasType.mapTy hc) (HasType.mapTy hb) (ha.subst σ)

/-- `HasType.mapTy` on an argument list. -/
theorem HasTypeList.mapTy {sig : Sig} : {Γ : TyEnv} → {es : List TExpr} →
    {ts : List ImpType} → HasTypeList sig Γ es ts →
    HasTypeList (sig.subst σ) (Γ.subst σ) (TExpr.mapTyList (ImpType.substVars σ) es)
      (ts.map (ImpType.substVars σ))
  | _, _, _, .nil => .nil
  | _, _, _, .cons he hes => .cons (HasType.mapTy he) (HasTypeList.mapTy hes)

/-- `HasType.mapTy` on match arms. -/
theorem HasTypeArms.mapTy {sig : Sig} : {Γ : TyEnv} → {σs : ImpType} →
    {arms : List (ImpPat × TExpr)} → {τ : ImpType} → HasTypeArms sig Γ σs arms τ →
    HasTypeArms (sig.subst σ) (Γ.subst σ) (ImpType.substVars σ σs)
      (TExpr.mapTyArms (ImpType.substVars σ) arms) (ImpType.substVars σ τ)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hp hle hb harms => by
      have hle' := hle.subst σ
      have hb' := HasType.mapTy hb
      rw [TyEnv.subst_extendList] at hle' hb'
      exact .cons (PatHasType.subst σ hp) hle' hb' (HasTypeArms.mapTy harms)
end

/-- Typing is stable under the instantiation `TExpr.instTypes σ` of the type parameters,
    with the environment and the signature instantiated by `σ`. -/
theorem HasType.instTypes {sig : Sig} {Γ : TyEnv} {e : TExpr} {τ : ImpType}
    (h : HasType sig Γ e τ) :
    HasType (sig.subst σ) (Γ.subst σ) (TExpr.instTypes σ e) (ImpType.substVars σ τ) :=
  h.mapTy σ

end Subst

end CatCrypt.Hax.TExprTyping
