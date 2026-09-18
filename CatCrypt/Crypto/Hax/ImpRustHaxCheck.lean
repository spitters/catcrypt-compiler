/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpRustPrint
public import CatCrypt.Crypto.Hax.LowCTToHaxSim

/-!
# Checking the hax frontend's reading of printed Rust

`ppImpRust ty e` (`CatCrypt.Crypto.Hax.ImpRustPrint`) prints a hax expression
`e` as Rust text.  The hax frontend (`cargo hax json`, then
`Hax.HaxAdapter.parseHaxExpr` followed by `reconstructForLoops` and
`normalizeAssignOps`, the passes `parseHaxItem` applies to a function body)
reads that text back as an expression `x` of a slightly different shape.
`normHaxRead` maps `x` to the printer's input shape, and the per-program check
`haxReadAgrees e x` compares the result with `e`.

The differences `normHaxRead` removes:

| printed `e` | frontend reading `x` | condition |
|---|---|---|
| `letBind a (array_update(a, i, s)) b` | `seq (assign a (array_update(a, i, s))) b` | the first argument of `array_update` is `var a` |
| `forFold v lo hi b` | `forLoop v lo hi b` | none |
| `app "scalar#Op" args` on the right of a binding or an assignment | `app "Op" args` | `(Op, scalar#Op)` in `haxOpPairs` |
| `app "scalar#Sub" args` | `app "saturating_sub" args` | as above |

The frontend suffixes the bit-sensitive operators with the operand width, so
`BitAnd` and `BitXor` on `u64` operands read as `BitAnd#64` and `BitXor#64`.
A call to a free function of the crate reads as its unqualified name.  A
comparison binding has the Rust type `bool` in the printed text; its reading is
the same `app` node.  rustc desugars `while c { b }` to a `loop` with an inner
conditional `break`, which the frontend's `Loop` arm reads as
`whileLoop (lit (bool true)) _`; `normHaxRead` does not map it, so a program
with a `while` loop fails the check.

## Semantics

The source semantics is hax-lean's `denote` of `forToLoop e`, the semantics
`lowCTToImp_simulates` is stated for.  `denote_normHaxRead` shows that
`normHaxRead` preserves it for every builtin table `bi` that interprets each
frontend operator name as its scalar call (`HaxOpsAgree bi`): the array-store
rule because `seq (assign a v) b` and `letBind a v b` both extend the
environment at `a` and continue with `b`, the loop rule because `forToLoop`
maps `forFold` and `forLoop` to the same loop, and the renaming by
`HaxOpsAgree`.

`haxReadAgrees e x` is `impEq (normHaxRead x) e`, with `impEq` a structural
equality on the printed fragment (`impEq_sound`).  `haxReadAgrees_sound` then
states that `x` runs as `e` does.  With `ppImpRust ty e = some t` the parser of
`ImpRustPrint` also reads `t` as `normHaxRead x` (`haxReadAgrees_parse`).

## Main definitions

* `haxOpPairs`, `haxOpName`, `HaxOpsAgree` — the operator names.
* `normHaxRead` — the normaliser.
* `impEq`, `haxReadAgrees` — the check.

## Main results

* `denote_normHaxRead`, `evalImp_normHaxRead` — the normaliser preserves the
  source semantics.
* `impEq_sound` — the equality is sound.
* `haxReadAgrees_sound`, `haxReadAgrees_parse` — soundness of the check.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpPat Value Env Outcome Builtins denote denoteArgs
  denoteForLoop denoteMatchArms denoteWhile denoteForLoop_congr denoteWhile_congr)

/-! ## §1  Operator names -/

/-- The operator names of the frontend's reading, each with the scalar call the
    printer prints as that operator. -/
def haxOpPairs : List (String × String) :=
  [("Add", "scalar#Add"), ("Mul", "scalar#Mul"), ("BitAnd#64", "scalar#BitAnd"),
   ("BitXor#64", "scalar#BitXor"), ("Lt", "scalar#Lt"), ("Gt", "scalar#Gt"),
   ("Le", "scalar#Le"), ("Ge", "scalar#Ge"), ("Eq", "scalar#Eq"), ("Ne", "scalar#Ne"),
   ("saturating_sub", "scalar#Sub")]

/-- The scalar call of a frontend operator name; every other name is kept. -/
def haxOpName (f : String) : String := (haxOpPairs.lookup f).getD f

/-- The builtin table interprets each frontend operator name as its scalar
    call. -/
def HaxOpsAgree (bi : Builtins) : Prop := ∀ p ∈ haxOpPairs, bi p.1 = bi p.2

theorem mem_of_lookup_eq_some (l : List (String × String)) (f g : String)
    (h : l.lookup f = some g) : (f, g) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : f = k
    · subst hk
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · have : (f == k) = false := by simpa using hk
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem HaxOpsAgree.name {bi : Builtins} (h : HaxOpsAgree bi) (f : String) :
    bi (haxOpName f) = bi f := by
  unfold haxOpName
  cases hl : haxOpPairs.lookup f with
  | none => rfl
  | some g => exact (h (f, g) (mem_of_lookup_eq_some _ f g hl)).symm

/-! ## §2  The normaliser -/

/-- The right-hand side of a binding or an assignment, with the operator name of
    a call replaced by its scalar call. -/
def normRhs : ImpExpr → ImpExpr
  | .app f args => .app (haxOpName f) args
  | e => e

/-- `v` is an `array_update` whose array argument is `var a`. -/
def isArrUpdateOf (a : String) : ImpExpr → Bool
  | .app f (.var b :: _) => decide (f = "array_update") && decide (b = a)
  | _ => false

mutual

/-- The printer's input shape of a frontend reading. -/
def normHaxRead : ImpExpr → ImpExpr
  | .letBind x v b => .letBind x (normRhs v) (normHaxRead b)
  | .seq (.assign x v) b =>
      if isArrUpdateOf x v then .letBind x v (normHaxRead b)
      else .seq (.assign x (normRhs v)) (normHaxRead b)
  | .seq a b => .seq (normHaxRead a) (normHaxRead b)
  | .assign x v => .assign x (normRhs v)
  | .ifThenElse c t e => .ifThenElse c (normHaxRead t) (normHaxRead e)
  | .whileLoop c b => .whileLoop c (normHaxRead b)
  | .forLoop x lo hi b => .forFold x lo hi (normHaxRead b)
  | .match_ s arms => .match_ s (normHaxArms arms)
  | e => e

/-- `normHaxRead` on every arm body. -/
def normHaxArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
  | [] => []
  | (p, b) :: r => (p, normHaxRead b) :: normHaxArms r

end

theorem normHaxRead_seq (a b : ImpExpr) (ha : ∀ x v, a ≠ .assign x v) :
    normHaxRead (.seq a b) = .seq (normHaxRead a) (normHaxRead b) := by
  cases a <;> first | rfl | exact absurd rfl (ha _ _)

/-! ## §3  The normaliser preserves the source semantics -/

/-- An outcome with the message of an error removed. -/
def eraseMsg : Outcome → Outcome
  | .err _ => .err ""
  | o => o

/-- Two computations agree up to error messages: from every environment they
    reach the same environment, and the same outcome except that the messages
    of two errors may differ. -/
def AgreeE (m m' : StateM Env Outcome) : Prop :=
  ∀ env, eraseMsg (m env).1 = eraseMsg (m' env).1 ∧ (m env).2 = (m' env).2

theorem AgreeE.refl (m : StateM Env Outcome) : AgreeE m m := fun _ => ⟨rfl, rfl⟩

theorem AgreeE.pure_err (s s' : String) :
    AgreeE (pure (.err s)) (pure (.err s')) := fun _ => ⟨rfl, rfl⟩

theorem eraseMsg_cases {o o' : Outcome} (h : eraseMsg o = eraseMsg o') :
    (∃ s s', o = .err s ∧ o' = .err s') ∨ o = o' := by
  cases o <;> cases o' <;> simp_all [eraseMsg]

theorem agreeE_bind_same {α : Type} (m : StateM Env α) (k k' : α → StateM Env Outcome)
    (hk : ∀ a, AgreeE (k a) (k' a)) : AgreeE (m >>= k) (m >>= k') :=
  fun env => hk (m env).1 (m env).2

theorem agreeE_bind {m m' : StateM Env Outcome} {k k' : Outcome → StateM Env Outcome}
    (hm : AgreeE m m') (hk : ∀ o, (∀ s, o ≠ .err s) → AgreeE (k o) (k' o))
    (herr : ∀ s s', AgreeE (k (.err s)) (k' (.err s'))) : AgreeE (m >>= k) (m' >>= k') := by
  intro env
  obtain ⟨h1, h2⟩ := hm env
  show eraseMsg (k (m env).1 (m env).2).1 = eraseMsg (k' (m' env).1 (m' env).2).1 ∧
    (k (m env).1 (m env).2).2 = (k' (m' env).1 (m' env).2).2
  rw [h2]
  by_cases he : ∃ s, (m env).1 = .err s
  · rcases eraseMsg_cases h1 with ⟨s, s', hs, hs'⟩ | ho
    · rw [hs, hs']; exact herr s s' _
    · obtain ⟨s, hs⟩ := he
      rw [← ho, hs]; exact herr s s _
  · rcases eraseMsg_cases h1 with ⟨s, _, hs, _⟩ | ho
    · exact absurd ⟨s, hs⟩ he
    · rw [← ho]; exact hk _ (fun s hs => he ⟨s, hs⟩) _

section Semantics

variable (bi : Builtins)

theorem denote_normRhs (h : HaxOpsAgree bi) (fuel : Nat) (v : ImpExpr) :
    AgreeE (denote bi fuel (forToLoop (normRhs v))) (denote bi fuel (forToLoop v)) := by
  cases v with
  | app f args =>
    simp only [normRhs, forToLoop]
    unfold denote
    rw [h.name f]
    refine agreeE_bind_same _ _ _ fun mv => ?_
    cases mv with
    | none => exact AgreeE.refl _
    | some vals =>
      dsimp only
      split
      · exact AgreeE.refl _
      · exact AgreeE.pure_err _ _
  | _ => exact AgreeE.refl _

/-- An assignment followed by `b` runs as the binding of the same name over
    `b`. -/
theorem denote_seq_assign (fuel : Nat) (x : String) (r b : ImpExpr) :
    denote bi fuel (.seq (.assign x r) b) = denote bi fuel (.letBind x r b) := by
  funext env
  simp only [denote, bind, StateT.bind, modify, modifyGet, MonadStateOf.modifyGet, pure]
  cases denote bi fuel r env with
  | mk o env' => cases o <;> rfl

/-- A binding whose value and body agree up to error messages. -/
theorem agreeE_letBind (fuel : Nat) (x : String) (v v' b b' : ImpExpr)
    (hv : AgreeE (denote bi fuel v') (denote bi fuel v))
    (hb : AgreeE (denote bi fuel b') (denote bi fuel b)) :
    AgreeE (denote bi fuel (.letBind x v' b')) (denote bi fuel (.letBind x v b)) := by
  unfold denote
  refine agreeE_bind hv (fun o _ => ?_) (fun _ _ => AgreeE.pure_err _ _)
  cases o with
  | val w => exact agreeE_bind_same _ _ _ fun _ => hb
  | _ => exact AgreeE.refl _

theorem denoteForLoop_agreeE (var : String) (body body' : ImpExpr)
    (hbody : ∀ fuel, AgreeE (denote bi fuel body') (denote bi fuel body)) :
    ∀ fuel lo hi, AgreeE (denoteForLoop bi fuel var lo hi body')
      (denoteForLoop bi fuel var lo hi body) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi
    unfold denoteForLoop
    split
    · exact AgreeE.refl _
    · exact AgreeE.refl _
  | succ n ih =>
    intro lo hi
    unfold denoteForLoop
    split
    · exact AgreeE.refl _
    · split
      · exact AgreeE.refl _
      · refine agreeE_bind_same _ _ _ fun _ => ?_
        refine agreeE_bind (hbody (n + 1)) (fun o _ => ?_) (fun _ _ => AgreeE.pure_err _ _)
        cases o with
        | val _ => exact ih _ _
        | continued => exact ih _ _
        | _ => exact AgreeE.refl _

theorem denoteWhile_agreeE (cond body body' : ImpExpr)
    (hbody : ∀ fuel, AgreeE (denote bi fuel body') (denote bi fuel body)) :
    ∀ fuel, AgreeE (denoteWhile bi fuel cond body') (denoteWhile bi fuel cond body) := by
  intro fuel
  induction fuel with
  | zero =>
    unfold denoteWhile
    exact AgreeE.refl _
  | succ n ih =>
    unfold denoteWhile
    split
    · exact AgreeE.refl _
    · refine agreeE_bind_same _ _ _ fun rc => ?_
      split
      · refine agreeE_bind (hbody (n + 1)) (fun o _ => ?_) (fun _ _ => AgreeE.pure_err _ _)
        cases o with
        | val _ => exact ih
        | continued => exact ih
        | _ => exact AgreeE.refl _
      all_goals exact AgreeE.refl _

theorem denoteMatchArms_normHaxArms (fuel : Nat) (v : Value)
    (arms : List (ImpPat × ImpExpr))
    (ih : ∀ pa ∈ arms, AgreeE (denote bi fuel (forToLoop (normHaxRead pa.2)))
      (denote bi fuel (forToLoop pa.2))) :
    AgreeE (denoteMatchArms bi fuel v (forToLoopArms (normHaxArms arms)))
      (denoteMatchArms bi fuel v (forToLoopArms arms)) := by
  induction arms with
  | nil => exact AgreeE.refl _
  | cons pa arms ihl =>
    obtain ⟨p, b⟩ := pa
    simp only [normHaxArms, forToLoopArms]
    unfold denoteMatchArms
    refine agreeE_bind_same _ _ _ fun env => ?_
    split
    · exact agreeE_bind_same _ _ _ fun _ => ih (p, b) List.mem_cons_self
    · exact ihl fun pa hpa => ih pa (List.mem_cons_of_mem _ hpa)

/-- **The normaliser preserves the source semantics**, up to error messages. -/
theorem denote_normHaxRead (h : HaxOpsAgree bi) (e : ImpExpr) :
    ∀ fuel, AgreeE (denote bi fuel (forToLoop (normHaxRead e)))
      (denote bi fuel (forToLoop e)) := by
  induction e using ImpExpr.ind with
  | letBind x v b _ ihb =>
    intro fuel
    simp only [normHaxRead, forToLoop]
    exact agreeE_letBind bi fuel x _ _ _ _ (denote_normRhs bi h fuel v) (ihb fuel)
  | seq a b iha ihb =>
    intro fuel
    by_cases ha : ∃ x v, a = .assign x v
    · obtain ⟨x, v, rfl⟩ := ha
      simp only [normHaxRead]
      split
      · simp only [forToLoop]
        rw [denote_seq_assign]
        exact agreeE_letBind bi fuel x _ _ _ _ (AgreeE.refl _) (ihb fuel)
      · simp only [forToLoop]
        rw [denote_seq_assign, denote_seq_assign]
        exact agreeE_letBind bi fuel x _ _ _ _ (denote_normRhs bi h fuel v) (ihb fuel)
    · rw [normHaxRead_seq a b (fun x v hx => ha ⟨x, v, hx⟩)]
      simp only [forToLoop]
      unfold denote
      refine agreeE_bind (iha fuel) (fun o _ => ?_) (fun _ _ => AgreeE.pure_err _ _)
      cases o with
      | val _ => exact ihb fuel
      | _ => exact AgreeE.refl _
  | assign x v _ =>
    intro fuel
    simp only [normHaxRead, forToLoop]
    unfold denote
    refine agreeE_bind (denote_normRhs bi h fuel v) (fun o _ => ?_)
      (fun _ _ => AgreeE.pure_err _ _)
    cases o with
    | val _ => exact AgreeE.refl _
    | _ => exact AgreeE.refl _
  | ifThenElse c t e _ iht ihe =>
    intro fuel
    simp only [normHaxRead, forToLoop]
    unfold denote
    refine agreeE_bind_same _ _ _ fun rc => ?_
    split
    · exact iht fuel
    · exact ihe fuel
    · exact AgreeE.refl _
    · exact AgreeE.refl _
  | whileLoop c b _ ihb =>
    intro fuel
    simp only [normHaxRead, forToLoop]
    unfold denote
    exact denoteWhile_agreeE bi _ _ _ ihb fuel
  | forLoop x lo hi b _ _ ihb =>
    intro fuel
    simp only [normHaxRead, forToLoop]
    unfold denote
    refine agreeE_bind_same _ _ _ fun rlo => ?_
    split
    · refine agreeE_bind_same _ _ _ fun rhi => ?_
      split
      · exact denoteForLoop_agreeE bi x _ _ ihb fuel _ _
      all_goals exact AgreeE.refl _
    · exact AgreeE.refl _
  | match_ s arms _ iha =>
    intro fuel
    simp only [normHaxRead, forToLoop]
    unfold denote
    refine agreeE_bind_same _ _ _ fun rs => ?_
    split
    · exact denoteMatchArms_normHaxArms bi fuel _ arms fun pa hpa => iha pa hpa fuel
    · exact AgreeE.refl _
  | _ => intro fuel; exact AgreeE.refl _

/-- A run that ends in a value, through a computation that agrees with another
    up to error messages, is a run of the other. -/
theorem evalImp_of_agreeE {fuel : Nat} {e e' : ImpExpr}
    (h : AgreeE (denote bi fuel e') (denote bi fuel e)) (env : Env) :
    evalImp bi fuel e' env = evalImp bi fuel e env := by
  obtain ⟨h1, h2⟩ := h env
  unfold evalImp
  simp only [StateT.run]
  generalize denote bi fuel e' env = p' at h1 h2 ⊢
  generalize denote bi fuel e env = p at h1 h2 ⊢
  obtain ⟨o', s'⟩ := p'
  obtain ⟨o, s⟩ := p
  simp only at h1 h2
  subst h2
  rcases eraseMsg_cases h1 with ⟨_, _, rfl, rfl⟩ | rfl <;> rfl

/-- `normHaxRead` preserves the successful runs `evalImp` of the source
    semantics. -/
theorem evalImp_normHaxRead (h : HaxOpsAgree bi) (e : ImpExpr) (fuel : Nat) (env : Env) :
    evalImp bi fuel (forToLoop (normHaxRead e)) env = evalImp bi fuel (forToLoop e) env :=
  evalImp_of_agreeE bi (denote_normHaxRead bi h e fuel) env

end Semantics

/-! ## §4  The check -/

/-- Equality of literals, on integer, Boolean and unit literals. -/
def litEq : ImpLit → ImpLit → Bool
  | .int a, .int b => decide (a = b)
  | .bool a, .bool b => decide (a = b)
  | .unit, .unit => true
  | _, _ => false

/-- Equality of lists of variable patterns. -/
def varPatsEq : List ImpPat → List ImpPat → Bool
  | [], [] => true
  | .varPat x :: ps, .varPat y :: qs => decide (x = y) && varPatsEq ps qs
  | _, _ => false

/-- Equality of patterns, on variable patterns and tuples of them. -/
def patEq : ImpPat → ImpPat → Bool
  | .varPat x, .varPat y => decide (x = y)
  | .tuplePat ps, .tuplePat qs => varPatsEq ps qs
  | _, _ => false

mutual

/-- Structural equality on the constructors of the printed fragment; `false`
    on every other constructor. -/
def impEq : ImpExpr → ImpExpr → Bool
  | .lit l, .lit m => litEq l m
  | .var x, .var y => decide (x = y)
  | .letBind x v b, .letBind y w c => decide (x = y) && impEq v w && impEq b c
  | .app f as, .app g bs => decide (f = g) && impEqList as bs
  | .proj a i, .proj b j => impEq a b && decide (i = j)
  | .ifThenElse c t e, .ifThenElse c' t' e' => impEq c c' && impEq t t' && impEq e e'
  | .match_ s as, .match_ s' bs => impEq s s' && impEqArms as bs
  | .unitVal, .unitVal => true
  | .seq a b, .seq c d => impEq a c && impEq b d
  | .assign x v, .assign y w => decide (x = y) && impEq v w
  | .whileLoop c b, .whileLoop c' b' => impEq c c' && impEq b b'
  | .forFold x lo hi b, .forFold y lo' hi' b' =>
      decide (x = y) && impEq lo lo' && impEq hi hi' && impEq b b'
  | _, _ => false

/-- `impEq` on lists. -/
def impEqList : List ImpExpr → List ImpExpr → Bool
  | [], [] => true
  | a :: as, b :: bs => impEq a b && impEqList as bs
  | _, _ => false

/-- `impEq` on match arms, with `patEq` on the patterns. -/
def impEqArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr) → Bool
  | [], [] => true
  | (p, a) :: as, (q, b) :: bs => patEq p q && impEq a b && impEqArms as bs
  | _, _ => false

end

theorem litEq_sound (l m : ImpLit) (h : litEq l m = true) : l = m := by
  cases l <;> cases m <;> simp_all [litEq]

theorem varPatsEq_sound : ∀ ps qs : List ImpPat, varPatsEq ps qs = true → ps = qs
  | [], [], _ => rfl
  | p :: ps, q :: qs, h => by
    cases p <;> cases q <;> simp only [varPatsEq, Bool.and_eq_true, decide_eq_true_eq,
      Bool.false_eq_true] at h
    obtain ⟨rfl, h⟩ := h
    rw [varPatsEq_sound ps qs h]
  | [], _ :: _, h => by simp [varPatsEq] at h
  | _ :: _, [], h => by simp [varPatsEq] at h

theorem patEq_sound (p q : ImpPat) (h : patEq p q = true) : p = q := by
  cases p <;> cases q <;> simp only [patEq, decide_eq_true_eq, Bool.false_eq_true] at h
  · rw [h]
  · rw [varPatsEq_sound _ _ h]

theorem impEqList_sound (as : List ImpExpr) (ih : ∀ a ∈ as, ∀ b, impEq a b = true → a = b) :
    ∀ bs, impEqList as bs = true → as = bs := by
  induction as with
  | nil => intro bs h; cases bs <;> simp_all [impEqList]
  | cons a as iha =>
    intro bs h
    cases bs with
    | nil => simp [impEqList] at h
    | cons b bs =>
      simp only [impEqList, Bool.and_eq_true] at h
      rw [ih a List.mem_cons_self b h.1,
        iha (fun a' ha' => ih a' (List.mem_cons_of_mem _ ha')) bs h.2]

theorem impEqArms_sound (as : List (ImpPat × ImpExpr))
    (ih : ∀ pa ∈ as, ∀ b, impEq pa.2 b = true → pa.2 = b) :
    ∀ bs, impEqArms as bs = true → as = bs := by
  induction as with
  | nil => intro bs h; cases bs <;> simp_all [impEqArms]
  | cons pa as iha =>
    intro bs h
    obtain ⟨p, a⟩ := pa
    cases bs with
    | nil => simp [impEqArms] at h
    | cons qb bs =>
      obtain ⟨q, b⟩ := qb
      simp only [impEqArms, Bool.and_eq_true] at h
      have hab : a = b := ih (p, a) List.mem_cons_self b h.1.2
      rw [patEq_sound p q h.1.1, hab,
        iha (fun pa' ha' => ih pa' (List.mem_cons_of_mem _ ha')) bs h.2]

/-- **The equality is sound.** -/
theorem impEq_sound (a : ImpExpr) : ∀ b, impEq a b = true → a = b := by
  induction a using ImpExpr.ind with
  | lit l =>
    intro b h; cases b <;> simp only [impEq, Bool.false_eq_true] at h
    rw [litEq_sound _ _ h]
  | var x =>
    intro b h; cases b <;> simp only [impEq, Bool.false_eq_true, decide_eq_true_eq] at h
    rw [h]
  | letBind x v body ihv ihb =>
    intro b h
    cases b <;> simp only [impEq, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, h1⟩, h2⟩ := h
    rw [ihv _ h1, ihb _ h2]
  | app f args ih =>
    intro b h
    cases b <;> simp only [impEq, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, h⟩ := h
    rw [impEqList_sound args ih _ h]
  | proj e i ih =>
    intro b h
    cases b <;> simp only [impEq, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h, rfl⟩ := h
    rw [ih _ h]
  | ifThenElse c t e ihc iht ihe =>
    intro b h
    cases b <;> simp only [impEq, Bool.false_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [ihc _ h1, iht _ h2, ihe _ h3]
  | match_ s arms ihs iha =>
    intro b h
    cases b <;> simp only [impEq, Bool.false_eq_true, Bool.and_eq_true] at h
    rw [ihs _ h.1, impEqArms_sound arms iha _ h.2]
  | unitVal => intro b h; cases b <;> simp only [impEq, Bool.false_eq_true] at h; rfl
  | seq a c iha ihc =>
    intro b h
    cases b <;> simp only [impEq, Bool.false_eq_true, Bool.and_eq_true] at h
    rw [iha _ h.1, ihc _ h.2]
  | assign x v ih =>
    intro b h
    cases b <;> simp only [impEq, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨rfl, h⟩ := h
    rw [ih _ h]
  | whileLoop c body ihc ihb =>
    intro b h
    cases b <;> simp only [impEq, Bool.false_eq_true, Bool.and_eq_true] at h
    rw [ihc _ h.1, ihb _ h.2]
  | forFold x lo hi body ihl ihh ihb =>
    intro b h
    cases b <;> simp only [impEq, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, h1⟩, h2⟩, h3⟩ := h
    rw [ihl _ h1, ihh _ h2, ihb _ h3]
  | _ => intro b h; cases b <;> simp [impEq] at h

/-- **The check.**  The frontend's reading `extracted` of the printed text of
    `printed`, normalised, equals `printed`. -/
def haxReadAgrees (printed extracted : ImpExpr) : Bool := impEq (normHaxRead extracted) printed

/-- **Soundness of the check.**  A frontend reading that passes the check runs,
    under the source semantics, as the printed expression does. -/
theorem haxReadAgrees_sound (bi : Builtins) (h : HaxOpsAgree bi) (e x : ImpExpr)
    (hc : haxReadAgrees e x = true) (fuel : Nat) (env : Env) :
    evalImp bi fuel (forToLoop x) env = evalImp bi fuel (forToLoop e) env := by
  rw [← impEq_sound _ _ hc, evalImp_normHaxRead bi h x fuel env]

/-- The parser of `ImpRustPrint` reads a printed text as the normalised
    frontend reading of the text, when the reading passes the check. -/
theorem haxReadAgrees_parse (ty : String → Option ImpRust.Tok) (e x : ImpExpr) (t : String)
    (hp : ppImpRust ty e = some t) (hc : haxReadAgrees e x = true) :
    parseImpRust t = some (normHaxRead x) := by
  rw [impEq_sound _ _ hc]
  exact parse_ppImpRust ty e t hp

/-! ## §5  A program for the round trip

`roundTripLowCT` binds `x` to the leaf call `fp_mul(a, b)`, replaces it four
times by `fp_mul(x, b)` in a counted loop, and binds the scalar `s` to `c + d`.
Its translation `roundTripImp` lies in the part of the front the simulation
`lowCTToImp_simulates_frontNF` covers (`roundTripImp_simScope`).  The emit
driver `bench/hax_roundtrip/emit_roundtrip.lean` prints it with `ppImpRustFn`
as the Rust function `roundtrip_prog` with the parameters `roundTripParams`
and the local types `roundTripTy`. -/

open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located SExpr TowerType)

/-- A slot of the field tower `TFp`. -/
def rtLoc (x : String) : Located := { locVar := x, locSrc := .TFp }

/-- The round-trip program. -/
def roundTripLowCT : LowCT :=
  .RLetZero "x" .TFp (.RSeq (.RCall "fp_mul" (rtLoc "x") [rtLoc "a", rtLoc "b"])
    (.RSeq (.RFor "i" 4 (.RCall "fp_mul" (rtLoc "x") [rtLoc "x", rtLoc "b"]))
      (.RLetU64Zero "s" (.RSeq (.RScalarSetExpr "s" (.SAdd (.SVar "c") (.SVar "d"))) .RSkip))))

/-- The hax translation of the round-trip program. -/
def roundTripImp : ImpExpr :=
  .letBind "x" (.app "fp_mul" [.var "a", .var "b"])
    (.seq (.forFold "i" (.lit (.int 0)) (.lit (.int 4))
        (.assign "x" (.app "fp_mul" [.var "x", .var "b"])))
      (.letBind "s" (.app "scalar#Add" [.var "c", .var "d"]) .unitVal))

theorem lowCTToImp_roundTripLowCT : lowCTToImp roundTripLowCT = some roundTripImp := rfl

/-- The Rust parameters of the printed function. -/
def roundTripParams : List (String × ImpRust.Tok) :=
  [("a", "[u64;6]"), ("b", "[u64;6]"), ("c", "u64"), ("d", "u64")]

/-- The Rust types of the locals of the printed function. -/
def roundTripTy (x : String) : Option ImpRust.Tok :=
  if x = "x" then some "[u64;6]" else if x = "s" then some "u64" else none

/-- The scalar names of the round-trip program. -/
def rtScalars : List String := ["i", "s", "c", "d"]

/-- The entry scope: the parameters `a`, `b` at `TFp`. -/
def rtEntryScope : TowerScope := [("a", .TFp), ("b", .TFp)]

/-- The exit scope: the entry scope and the local `x` at `TFp`. -/
def rtExitScope : TowerScope := [("x", .TFp), ("a", .TFp), ("b", .TFp)]

/-- The scope checker of the simulation accepts the round-trip program. -/
theorem roundTripImp_simScope :
    simScopeW towerOfCallName [] rtScalars [] [] rtEntryScope roundTripImp =
      some rtExitScope := by
  rw [simScopeW_eq_tow towerOfCallName (fun _ => .TFp) [] rtScalars [] [] roundTripImp ?_]
  · rfl
  · intro f hf
    simp only [roundTripImp, scopeCallNamesW, List.mem_cons, List.not_mem_nil, or_false,
      List.nil_append, List.cons_append] at hf
    rcases hf with rfl | rfl | rfl <;>
      simp [towerOfCallName_default_eq, towerOfCallName_default]

end CatCrypt.Crypto.Hax
