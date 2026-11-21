/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.ImpRustPrint
public import CatCrypt.Crypto.Hax.ImpEval

/-!
# Checking the hax frontend's reading of printed Rust

`ppImpRust ty e` (`CatCrypt.Crypto.Hax.ImpRustPrint`) prints a hax expression
`e` as Rust text.  The hax frontend (`cargo hax json`, then
`Hax.HaxAdapter.parseHaxTExpr` followed by `reconstructForLoopsTExpr`,
`normalizeAssignOpsTExpr` and `TExpr.erase`, the passes `parseHaxItemTExpr` applies to a
function body)
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
| `var x` as a call argument | `borrow (deref (var x))` | a reference parameter passed on |

A Rust block on the left of `;` scopes its bindings over the statements that
follow it, so a printed `seq (letBind x v b) c` reads back as
`letBind x v (seq b c)`.  `seqNF` associates the bindings and the sequencing of
a statement sequence to the right and drops a `unitVal` on the left of `;`; the
check compares the two sides in that form.

The frontend suffixes the bit-sensitive operators with the operand width, so
`BitAnd`, `BitXor`, `Shr` and `Shl` read as `BitAnd#64`, `BitXor#64`, `Shr#64` and
`Shl#64` on `u64` operands and as `BitAnd#size`, `BitXor#size`, `Shr#size` and
`Shl#size` on `usize` operands.
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

A reborrow is removed because hax-lean's `denote` reads `borrow` and `deref` as
the expression under them, so `borrow (deref e)` and `e` have the same
denotation.

## The returned local

`retOfUnit x e` replaces the tail `unitVal` of a statement sequence by the
variable `x`, the form `ppImpRustFnRet` prints inside a function with a return
type.  `denote_retOfUnit` states that it runs as `seq e (var x)`, so it leaves
the environment the body leaves and returns the value of `x` in it
(`evalImp_retOfUnit`).  `retTail x e` is `retOfUnit x (appendSeq e unitVal)`,
the returned form of a sequence whose tail is a loop or a call rather than
`unitVal`; `evalImp_retTail` states the same for it.  The frontend reads the
tail expression of a block as that variable, which `normHaxRead`, `seqNF` and
`impEq` carry unchanged.

`haxReadEq e x` is `impEq (seqNF (normHaxRead x)) (seqNF e)`, with `impEq` a
structural equality on the printed fragment (`impEq_sound`); `haxReadEq_sound`
states that `x` runs as `e` does.

## Renamed block locals

The typed reader renames the `let`-bound locals of a block used as a statement
apart with the suffix `_blkN`.  `impEqA σ a b` compares the two sides up to a
correspondence `σ` of the printed locals with the reading's locals, updated at
each binding along the evaluation order (`bindLocal`, `keepLocals`).
`haxReadAgrees e x` holds when `haxReadEq e x` does or `impEqA` relates the two
sides from the identity correspondence.  `haxReadAgrees_sound` states that the
two runs reach the same value, with final environments related by the
correspondence `haxReadLocals e x` (`RunRel`), which is the identity when
`haxReadEq e x` holds.

## Main definitions

* `haxOpPairs`, `haxOpName`, `HaxOpsAgree` — the operator names.
* `normArg`, `normRhs`, `normHaxRead` — the normaliser.
* `appendSeq`, `seqNF` — the sequence normal form.
* `retOfUnit`, `TailUnit`, `retTail` — the tail of a statement sequence.
* `impEq`, `haxReadEq` — the structural check.
* `LocalMap`, `bindLocal`, `keepLocals`, `bindLog`, `impEqA` — the comparison up to
  a renaming of locals.
* `haxReadAgrees`, `haxReadLocals`, `RunRel` — the check.

## Main results

* `denote_normHaxRead`, `evalImp_normHaxRead` — the normaliser preserves the
  source semantics.
* `denote_appendSeq`, `denote_seqNF`, `evalImp_seqNF` — the sequence normal
  form preserves the source semantics.
* `denote_retOfUnit`, `evalImp_retOfUnit`, `evalImp_retTail` — the returned
  form yields the value of the returned local.
* `impEq_sound` — the equality is sound.
* `impEqA_frame`, `denote_impEqA`, `evalImp_impEqA` — the comparison up to a
  renaming of locals is a simulation.
* `haxReadEq_sound`, `haxReadAgrees_sound`, `haxReadAgrees_run`,
  `haxReadAgrees_parse`, `haxReadAgrees_parseFnRet` — soundness of the checks.
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
  [("Add", "scalar#Add"), ("Mul", "scalar#Mul"), ("Add#64", "scalar#Add"),
   ("Add#size", "scalar#Add"), ("Mul#64", "scalar#Mul"), ("Mul#size", "scalar#Mul"),
   ("BitAnd#64", "scalar#BitAnd"),
   ("BitAnd#size", "scalar#BitAnd"), ("BitXor#64", "scalar#BitXor"),
   ("BitXor#size", "scalar#BitXor"), ("Shr#64", "scalar#Shr"), ("Shr#size", "scalar#Shr"),
   ("Shl#64", "scalar#Shl"), ("Shl#size", "scalar#Shl"), ("Lt", "scalar#Lt"), ("Gt", "scalar#Gt"),
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

/-- A call argument, with a reborrow `&*x` removed. -/
def normArg : ImpExpr → ImpExpr
  | .borrow (.deref e) => e
  | e => e

/-- `normArg` on every element of a list. -/
def normArgs : List ImpExpr → List ImpExpr
  | [] => []
  | a :: as => normArg a :: normArgs as

/-- The right-hand side of a binding or an assignment, with the operator name of
    a call replaced by its scalar call and the reborrows of its arguments
    removed. -/
def normRhs : ImpExpr → ImpExpr
  | .app f args => .app (haxOpName f) (normArgs args)
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

/-- The statement sequence with the tail `unitVal` replaced by the variable
    `x`. -/
def retOfUnit (x : String) : ImpExpr → ImpExpr
  | .letBind y v b => .letBind y v (retOfUnit x b)
  | .seq a b => .seq a (retOfUnit x b)
  | .unitVal => .var x
  | e => e

/-- The tail of a statement sequence is `unitVal`. -/
def TailUnit : ImpExpr → Bool
  | .letBind _ _ b => TailUnit b
  | .seq _ b => TailUnit b
  | .unitVal => true
  | _ => false

/-- The statement sequence `a ; c` with `a` associated to the right: a binding
    of `a` scopes over `c`, the sequencing of `a` is kept to the right, and a
    `unitVal` tail of `a` is dropped. -/
def appendSeq : ImpExpr → ImpExpr → ImpExpr
  | .letBind x v b, c => .letBind x v (appendSeq b c)
  | .seq a b, c => .seq a (appendSeq b c)
  | .unitVal, c => c
  | a, c => .seq a c

mutual

/-- A statement sequence with its bindings and its sequencing associated to the
    right: `(let x = v; b) ; c` becomes `let x = v; b ; c`, `(a ; b) ; c`
    becomes `a ; b ; c`, and `() ; c` becomes `c`, recursively inside bindings,
    conditionals, loop bodies and match arms. -/
def seqNF : ImpExpr → ImpExpr
  | .letBind x v b => .letBind x v (seqNF b)
  | .seq a b => appendSeq (seqNF a) (seqNF b)
  | .ifThenElse c t e => .ifThenElse c (seqNF t) (seqNF e)
  | .whileLoop c b => .whileLoop c (seqNF b)
  | .forLoop x lo hi b => .forLoop x lo hi (seqNF b)
  | .forFold x lo hi b => .forFold x lo hi (seqNF b)
  | .match_ s arms => .match_ s (seqNFArms arms)
  | e => e

/-- `seqNF` on every arm body. -/
def seqNFArms : List (ImpPat × ImpExpr) → List (ImpPat × ImpExpr)
  | [] => []
  | (p, b) :: r => (p, seqNF b) :: seqNFArms r

end

/-- The statement sequence `e` with the variable `x` as its tail expression:
    the body `ppImpRustFnRet` prints inside a function returning `x`. -/
def retTail (x : String) (e : ImpExpr) : ImpExpr := retOfUnit x (appendSeq e .unitVal)

/-- The tail of `e ; ()` is `unitVal`. -/
theorem tailUnit_appendSeq_unitVal (e : ImpExpr) : TailUnit (appendSeq e .unitVal) = true := by
  induction e using ImpExpr.ind with
  | letBind x v b _ ihb => simpa only [appendSeq, TailUnit] using ihb
  | seq a b _ ihb => simpa only [appendSeq, TailUnit] using ihb
  | _ => simp [appendSeq, TailUnit]

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

/-- A reborrow runs as the expression it borrows. -/
theorem denote_normArg (fuel : Nat) (a : ImpExpr) :
    denote bi fuel (forToLoop (normArg a)) = denote bi fuel (forToLoop a) := by
  unfold normArg
  split
  · simp [forToLoop, denote]
  · rfl

theorem denoteArgs_normArgs (fuel : Nat) (args : List ImpExpr) :
    denoteArgs bi fuel (forToLoopArgs (normArgs args)) =
      denoteArgs bi fuel (forToLoopArgs args) := by
  induction args with
  | nil => rfl
  | cons a as ih =>
    simp only [normArgs, forToLoopArgs]
    unfold denoteArgs
    rw [denote_normArg bi fuel a]
    funext env
    simp only [bind, StateT.bind]
    cases (denote bi fuel (forToLoop a) env).1 <;> simp [ih]

theorem denote_normRhs (h : HaxOpsAgree bi) (fuel : Nat) (v : ImpExpr) :
    AgreeE (denote bi fuel (forToLoop (normRhs v))) (denote bi fuel (forToLoop v)) := by
  cases v with
  | app f args =>
    simp only [normRhs, forToLoop]
    unfold denote
    rw [h.name f, denoteArgs_normArgs bi fuel args]
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
      all_goals first
        | exact denoteForLoop_agreeE bi x _ _ ihb fuel _ _
        | exact AgreeE.refl _
    all_goals first
      | exact AgreeE.refl _
      | (refine agreeE_bind_same _ _ _ fun rhi => ?_
         split
         all_goals first
           | exact denoteForLoop_agreeE bi x _ _ ihb fuel _ _
           | exact AgreeE.refl _)
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

/-! ### The returned local -/

theorem denote_letBind_congr (fuel : Nat) (y : String) (v b b' : ImpExpr)
    (h : denote bi fuel b = denote bi fuel b') :
    denote bi fuel (.letBind y v b) = denote bi fuel (.letBind y v b') := by
  simp only [denote]
  rw [h]

theorem denote_seq_congr_right (fuel : Nat) (a b b' : ImpExpr)
    (h : denote bi fuel b = denote bi fuel b') :
    denote bi fuel (.seq a b) = denote bi fuel (.seq a b') := by
  simp only [denote]
  rw [h]

theorem denote_seq_assoc (fuel : Nat) (a b c : ImpExpr) :
    denote bi fuel (.seq (.seq a b) c) = denote bi fuel (.seq a (.seq b c)) := by
  funext env
  simp only [denote, bind, StateT.bind, pure]
  cases denote bi fuel a env with
  | mk o env' => cases o <;> rfl

theorem denote_seq_letBind (fuel : Nat) (y : String) (v b c : ImpExpr) :
    denote bi fuel (.seq (.letBind y v b) c) = denote bi fuel (.letBind y v (.seq b c)) := by
  funext env
  simp only [denote, bind, StateT.bind, pure, modify, modifyGet, MonadStateOf.modifyGet]
  cases denote bi fuel v env with
  | mk o env' => cases o <;> rfl

theorem denote_seq_unitVal (fuel : Nat) (c : ImpExpr) :
    denote bi fuel (.seq .unitVal c) = denote bi fuel c := by
  funext env
  simp only [denote, bind, StateT.bind, pure, StateT.pure]

theorem denote_seq_apply (fuel : Nat) (a b : ImpExpr) (env : Env) :
    denote bi fuel (.seq a b) env =
      match denote bi fuel a env with
      | (.val _, s) => denote bi fuel b s
      | (o, s) => (o, s) := by
  simp only [denote, bind, StateT.bind, pure]
  cases denote bi fuel a env with
  | mk o s => cases o <;> rfl

theorem denote_var_apply (fuel : Nat) (x : String) (env : Env) :
    denote bi fuel (.var x) env =
      (match env x with
       | some w => .val w
       | none => .err s!"undefined variable: {x}", env) := by
  simp only [denote, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure]
  cases env x <;> rfl

/-- **The returned form runs as the sequence of the body and the returned
    variable.**  A statement sequence whose tail `unitVal` is replaced by `x`
    runs as the sequence that runs the body and then reads `x`, so it leaves the
    same environment and returns the value of `x` in it. -/
theorem denote_retOfUnit (x : String) (e : ImpExpr) (h : TailUnit e = true) (fuel : Nat) :
    denote bi fuel (forToLoop (retOfUnit x e)) =
      denote bi fuel (forToLoop (.seq e (.var x))) := by
  induction e using ImpExpr.ind with
  | letBind y v b ihv ihb =>
    simp only [TailUnit] at h
    simp only [retOfUnit, forToLoop]
    rw [denote_seq_letBind]
    exact denote_letBind_congr bi fuel y _ _ _ (ihb h)
  | seq a b iha ihb =>
    simp only [TailUnit] at h
    simp only [retOfUnit, forToLoop]
    rw [denote_seq_assoc]
    exact denote_seq_congr_right bi fuel _ _ _ (ihb h)
  | unitVal => simp only [retOfUnit, forToLoop, denote_seq_unitVal]
  | _ => simp [TailUnit] at h

/-- **The returned form yields the value of the returned local.**  A successful
    run of the returned form is a successful run of the body reaching the same
    environment, and its value is the value of `x` in that environment. -/
theorem evalImp_retOfUnit (x : String) (e : ImpExpr) (h : TailUnit e = true) (fuel : Nat)
    (env env' : Env) (v : Value)
    (hRun : evalImp bi fuel (forToLoop (retOfUnit x e)) env = some (v, env')) :
    (∃ u, evalImp bi fuel (forToLoop e) env = some (u, env')) ∧ env' x = some v := by
  simp only [evalImp, StateT.run, denote_retOfUnit bi x e h fuel, forToLoop,
    denote_seq_apply, denote_var_apply] at hRun
  simp only [evalImp, StateT.run]
  cases hb : denote bi fuel (forToLoop e) env with
  | mk o env1 =>
    rw [hb] at hRun
    cases o with
    | val u =>
      simp only at hRun
      cases hx : env1 x with
      | none => rw [hx] at hRun; simp at hRun
      | some w =>
        rw [hx] at hRun
        simp only [Option.some.injEq, Prod.mk.injEq] at hRun
        obtain ⟨rfl, rfl⟩ := hRun
        exact ⟨⟨u, rfl⟩, hx⟩
    | _ => simp at hRun

/-! ### The sequence normal form -/

theorem denote_bind_congr {α : Type} (m : StateM Env α) (k k' : α → StateM Env Outcome)
    (hk : ∀ a, k a = k' a) : (m >>= k) = (m >>= k') := by
  rw [funext hk]

theorem denote_seq_congr (fuel : Nat) (a a' b b' : ImpExpr)
    (ha : denote bi fuel a = denote bi fuel a') (hb : denote bi fuel b = denote bi fuel b') :
    denote bi fuel (.seq a b) = denote bi fuel (.seq a' b') := by
  simp only [denote]
  rw [ha, hb]

theorem denote_ifThenElse_congr (fuel : Nat) (c t t' e e' : ImpExpr)
    (ht : denote bi fuel t = denote bi fuel t') (he : denote bi fuel e = denote bi fuel e') :
    denote bi fuel (.ifThenElse c t e) = denote bi fuel (.ifThenElse c t' e') := by
  simp only [denote]
  rw [ht, he]

theorem denote_whileLoop_congr (fuel : Nat) (c b b' : ImpExpr)
    (hb : ∀ f, denote bi f b' = denote bi f b) :
    denote bi fuel (.whileLoop c b') = denote bi fuel (.whileLoop c b) := by
  simp only [denote]
  exact denoteWhile_congr bi fuel c c b b' (fun _ => rfl) hb

theorem denote_forLoop_congr (fuel : Nat) (x : String) (lo hi b b' : ImpExpr)
    (hb : ∀ f, denote bi f b' = denote bi f b) :
    denote bi fuel (.forLoop x lo hi b') = denote bi fuel (.forLoop x lo hi b) := by
  have h : ∀ (f : Nat) (l h' : Int),
      denoteForLoop bi f x l h' b' = denoteForLoop bi f x l h' b :=
    fun f l h' => denoteForLoop_congr bi f x l h' b b' hb
  simp only [denote, h]

/-- `a ; c` with `a` associated to the right runs as `a ; c`. -/
theorem denote_appendSeq (fuel : Nat) (c : ImpExpr) (a : ImpExpr) :
    denote bi fuel (forToLoop (appendSeq a c))
      = denote bi fuel (.seq (forToLoop a) (forToLoop c)) := by
  induction a using ImpExpr.ind with
  | letBind x v b _ ihb =>
    show denote bi fuel (.letBind x (forToLoop v) (forToLoop (appendSeq b c)))
      = denote bi fuel (.seq (.letBind x (forToLoop v) (forToLoop b)) (forToLoop c))
    rw [denote_seq_letBind]
    exact denote_letBind_congr bi fuel x _ _ _ ihb
  | seq a b _ ihb =>
    show denote bi fuel (.seq (forToLoop a) (forToLoop (appendSeq b c)))
      = denote bi fuel (.seq (.seq (forToLoop a) (forToLoop b)) (forToLoop c))
    rw [denote_seq_assoc]
    exact denote_seq_congr_right bi fuel _ _ _ ihb
  | unitVal => simp only [appendSeq, forToLoop, denote_seq_unitVal]
  | _ => simp only [appendSeq, forToLoop]

theorem denoteMatchArms_seqNFArms (fuel : Nat) (v : Value) (arms : List (ImpPat × ImpExpr))
    (ih : ∀ pa ∈ arms,
      denote bi fuel (forToLoop (seqNF pa.2)) = denote bi fuel (forToLoop pa.2)) :
    denoteMatchArms bi fuel v (forToLoopArms (seqNFArms arms))
      = denoteMatchArms bi fuel v (forToLoopArms arms) := by
  induction arms with
  | nil => rfl
  | cons pa arms ihl =>
    obtain ⟨p, b⟩ := pa
    simp only [seqNFArms, forToLoopArms]
    unfold denoteMatchArms
    refine denote_bind_congr _ _ _ fun env => ?_
    split
    · exact denote_bind_congr _ _ _ fun _ => ih (p, b) List.mem_cons_self
    · exact ihl fun pa hpa => ih pa (List.mem_cons_of_mem _ hpa)

/-- **The sequence normal form preserves the source semantics.** -/
theorem denote_seqNF (e : ImpExpr) : ∀ fuel,
    denote bi fuel (forToLoop (seqNF e)) = denote bi fuel (forToLoop e) := by
  induction e using ImpExpr.ind with
  | letBind x v b _ ihb =>
    intro fuel
    simp only [seqNF, forToLoop]
    exact denote_letBind_congr bi fuel x _ _ _ (ihb fuel)
  | seq a b iha ihb =>
    intro fuel
    simp only [seqNF, forToLoop]
    rw [denote_appendSeq bi fuel (seqNF b) (seqNF a)]
    exact denote_seq_congr bi fuel _ _ _ _ (iha fuel) (ihb fuel)
  | ifThenElse c t e _ iht ihe =>
    intro fuel
    simp only [seqNF, forToLoop]
    exact denote_ifThenElse_congr bi fuel _ _ _ _ _ (iht fuel) (ihe fuel)
  | whileLoop c b _ ihb =>
    intro fuel
    simp only [seqNF, forToLoop]
    exact denote_whileLoop_congr bi fuel _ _ _ ihb
  | forLoop x lo hi b _ _ ihb =>
    intro fuel
    simp only [seqNF, forToLoop]
    exact denote_forLoop_congr bi fuel x _ _ _ _ ihb
  | forFold x lo hi b _ _ ihb =>
    intro fuel
    simp only [seqNF, forToLoop]
    exact denote_forLoop_congr bi fuel x _ _ _ _ ihb
  | match_ s arms _ iha =>
    intro fuel
    simp only [seqNF, forToLoop]
    unfold denote
    refine denote_bind_congr _ _ _ fun rs => ?_
    split
    · exact denoteMatchArms_seqNFArms bi fuel _ arms fun pa hpa => iha pa hpa fuel
    · rfl
  | _ => intro fuel; rfl

/-- The sequence normal form preserves the successful runs `evalImp`. -/
theorem evalImp_seqNF (e : ImpExpr) (fuel : Nat) (env : Env) :
    evalImp bi fuel (forToLoop (seqNF e)) env = evalImp bi fuel (forToLoop e) env := by
  simp only [evalImp, StateT.run, denote_seqNF]

/-- A run of `e ; ()` is a run of `e` reaching the same environment. -/
theorem evalImp_seq_unitVal (e : ImpExpr) (fuel : Nat) (env env' : Env) (v : Value)
    (h : evalImp bi fuel (.seq e .unitVal) env = some (v, env')) :
    ∃ u, evalImp bi fuel e env = some (u, env') := by
  simp only [evalImp, StateT.run, denote_seq_apply] at h
  simp only [evalImp, StateT.run]
  cases hb : denote bi fuel e env with
  | mk o env1 =>
    rw [hb] at h
    cases o with
    | val u =>
      simp only [denote, pure, StateT.pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨u, rfl⟩
    | _ => simp at h

/-- **The returned form yields the value of the returned local.**  A successful
    run of `retTail x e` is a successful run of `e` reaching the same
    environment, and its value is the value of `x` in that environment. -/
theorem evalImp_retTail (x : String) (e : ImpExpr) (fuel : Nat) (env env' : Env) (v : Value)
    (hRun : evalImp bi fuel (forToLoop (retTail x e)) env = some (v, env')) :
    (∃ u, evalImp bi fuel (forToLoop e) env = some (u, env')) ∧ env' x = some v := by
  obtain ⟨⟨u, hu⟩, hx⟩ := evalImp_retOfUnit bi x (appendSeq e .unitVal)
    (tailUnit_appendSeq_unitVal e) fuel env env' v hRun
  refine ⟨?_, hx⟩
  rw [evalImp, denote_appendSeq bi fuel .unitVal e] at hu
  exact evalImp_seq_unitVal bi (forToLoop e) fuel env env' u hu

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
  | .tuple as, .tuple bs => impEqList as bs
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
  | tuple es ih =>
    intro b h
    cases b <;> simp only [impEq, Bool.false_eq_true] at h
    rw [impEqList_sound es ih _ h]
  | _ => intro b h; cases b <;> simp [impEq] at h

/-- The structural check.  The frontend's reading `extracted` of the printed text of
    `printed`, normalised, has the sequence normal form of `printed`. -/
def haxReadEq (printed extracted : ImpExpr) : Bool :=
  impEq (seqNF (normHaxRead extracted)) (seqNF printed)

/-- **Soundness of the structural check.**  A frontend reading that passes
    `haxReadEq` runs, under the source semantics, as the printed expression does. -/
theorem haxReadEq_sound (bi : Builtins) (h : HaxOpsAgree bi) (e x : ImpExpr)
    (hc : haxReadEq e x = true) (fuel : Nat) (env : Env) :
    evalImp bi fuel (forToLoop x) env = evalImp bi fuel (forToLoop e) env := by
  rw [← evalImp_normHaxRead bi h x fuel env, ← evalImp_seqNF bi (normHaxRead x) fuel env,
    impEq_sound _ _ hc, evalImp_seqNF bi e fuel env]

/-! ## §5  The comparison up to a renaming of locals

The typed reader renames the `let`-bound locals of a Rust block used as a statement
apart, with the suffix `_blk` and the position of the block (`renameBlockLocals` of
hax-lean's `HaxAdapter`), because the parse places the statements after the block in
the scope of the block's last binding.  The printed text binds `m1` where the reading
binds `m1_blk82`, and two blocks of one function may both bind `m1`.

`impEqA σ a b` compares a reading `a` with a printed expression `b` structurally, with
a correspondence `σ` of the printed locals with the reading's locals in place of
equality of names, and updates `σ` along the evaluation order: a binding of the
printed `m` against the reading's `y` makes `m` correspond to `y` (`bindLocal`).  A
conditional and a counted loop keep only the correspondences that their bindings do
not change (`keepLocals`).  `denote_impEqA` states that the two runs reach the same
value, with environments related by the final correspondence (`LocalRel`). -/

/-- A correspondence of the locals of the printed expression with the locals of the
    reading: `σ m = some y` when the printed local `m` holds the value of the
    reading's local `y`, and `σ m = none` when `m` is not tracked. -/
abbrev LocalMap := String → Option String

/-- The identity correspondence. -/
def idLocals : LocalMap := fun m => some m

/-- The correspondence after the printed local `m` and the reading's local `y` are
    bound to one value: `m` corresponds to `y`, and a printed local that
    corresponded to `y` is untracked. -/
def bindLocal (σ : LocalMap) (m y : String) : LocalMap := fun k =>
  if k = m then some y
  else
    match σ k with
    | some z => if z = y then none else some z
    | none => none

/-- No pair `(m', y')` of `log` binds the printed local `m` or the reading's local
    `z` except as the pair `(m, z)`. -/
def stableB (log : List (String × String)) (m z : String) : Bool :=
  log.all fun p => decide (p.1 = m) == decide (p.2 = z)

/-- `σ` with each printed local whose correspondence `log` may change untracked. -/
def keepLocals (σ : LocalMap) (log : List (String × String)) : LocalMap := fun k =>
  match σ k with
  | some z => if stableB log k z then some z else none
  | none => none

/-- The bounds of a counted loop whose bounds are integer literals. -/
def litBounds : ImpExpr → ImpExpr → Option (Int × Int)
  | .lit (.int l), .lit (.int h) => some (l, h)
  | _, _ => none

mutual

/-- The bindings `(printed local, reading's local)` that `impEqA` meets on a pair of
    expressions, in evaluation order. -/
def bindLog : ImpExpr → ImpExpr → List (String × String)
  | .letBind y v b, .letBind m w c => bindLog v w ++ (m, y) :: bindLog b c
  | .app _ as, .app _ bs => bindLogList as bs
  | .ifThenElse c t e, .ifThenElse c' t' e' =>
      bindLog c c' ++ (bindLog t t' ++ bindLog e e')
  | .seq a b, .seq c d => bindLog a c ++ bindLog b d
  | .assign y v, .assign m w => bindLog v w ++ [(m, y)]
  | .forFold y _ _ b, .forFold m _ _ c => (m, y) :: bindLog b c
  | _, _ => []

/-- `bindLog` on lists. -/
def bindLogList : List ImpExpr → List ImpExpr → List (String × String)
  | a :: as, b :: bs => bindLog a b ++ bindLogList as bs
  | _, _ => []

end

mutual

/-- Structural equality of a reading `a` with a printed expression `b` up to the
    correspondence of locals `σ`, on literals, variables, bindings, calls,
    conditionals, sequences, assignments and counted loops with literal bounds:
    the correspondence after `b`, or `none`. -/
def impEqA (σ : LocalMap) : ImpExpr → ImpExpr → Option LocalMap
  | .lit l, .lit l' => if litEq l l' then some σ else none
  | .var y, .var m => if σ m = some y then some σ else none
  | .letBind y v b, .letBind m w c =>
      (impEqA σ v w).bind fun σ1 => impEqA (bindLocal σ1 m y) b c
  | .app f as, .app g bs => if f = g then impEqAList σ as bs else none
  | .ifThenElse c t e, .ifThenElse c' t' e' =>
      (impEqA σ c c').bind fun σc =>
        (impEqA σc t t').bind fun _ => (impEqA σc e e').bind fun _ =>
          some (keepLocals σc (bindLog t t' ++ bindLog e e'))
  | .unitVal, .unitVal => some σ
  | .seq a b, .seq c d => (impEqA σ a c).bind fun σ1 => impEqA σ1 b d
  | .assign y v, .assign m w => (impEqA σ v w).map fun σ1 => bindLocal σ1 m y
  | .forFold y lo hi b, .forFold m lo' hi' c =>
      if (litBounds lo hi).isSome && decide (litBounds lo hi = litBounds lo' hi') then
        (impEqA (bindLocal (keepLocals σ ((m, y) :: bindLog b c)) m y) b c).map
          fun _ => keepLocals σ ((m, y) :: bindLog b c)
      else none
  | _, _ => none

/-- `impEqA` on lists, threading the correspondence. -/
def impEqAList (σ : LocalMap) : List ImpExpr → List ImpExpr → Option LocalMap
  | [], [] => some σ
  | a :: as, b :: bs => (impEqA σ a b).bind fun σ1 => impEqAList σ1 as bs
  | _, _ => none

end

theorem stableB_append (l₁ l₂ : List (String × String)) (m z : String) :
    stableB (l₁ ++ l₂) m z = (stableB l₁ m z && stableB l₂ m z) := by
  simp [stableB, List.all_append]

/-- The unfolding of `stableB` on a cons cell. -/
theorem stableB_cons (p : String × String) (l : List (String × String)) (m z : String) :
    stableB (p :: l) m z = ((decide (p.1 = m) == decide (p.2 = z)) && stableB l m z) := rfl

theorem bindLocal_stable (σ : LocalMap) (m y k z : String) (hk : σ k = some z)
    (hs : (decide (m = k) == decide (y = z)) = true) : bindLocal σ m y k = some z := by
  unfold bindLocal
  grind

theorem keepLocals_stable (σ : LocalMap) (log : List (String × String)) (k z : String)
    (hk : σ k = some z) (hs : stableB log k z = true) : keepLocals σ log k = some z := by
  simp [keepLocals, hk, hs]

theorem keepLocals_sub {σ : LocalMap} {log : List (String × String)} {k z : String}
    (h : keepLocals σ log k = some z) : σ k = some z ∧ stableB log k z = true := by
  unfold keepLocals at h
  grind

theorem litBounds_eq_some {lo hi : ImpExpr} {l h : Int} (hb : litBounds lo hi = some (l, h)) :
    lo = .lit (.int l) ∧ hi = .lit (.int h) := by
  unfold litBounds at hb
  split at hb <;> grind

/-- **The frame of the comparison.**  A printed local whose correspondence the
    bindings of the comparison do not change keeps it. -/
theorem impEqA_frame (a : ImpExpr) : ∀ (b : ImpExpr) (σ τ : LocalMap),
    impEqA σ a b = some τ → ∀ k z, σ k = some z → stableB (bindLog a b) k z = true →
      τ k = some z := by
  induction a using ImpExpr.ind with
  | lit l =>
    intro b σ τ h k z hk _
    cases b <;> simp only [impEqA, reduceCtorEq] at h
    split at h
    · cases h; exact hk
    · cases h
  | var y =>
    intro b σ τ h k z hk _
    cases b <;> simp only [impEqA, reduceCtorEq] at h
    split at h
    · cases h; exact hk
    · cases h
  | letBind y v body ihv ihb =>
    intro b σ τ h k z hk hs
    cases b <;> simp only [impEqA, reduceCtorEq, Option.bind_eq_some_iff] at h
    rename_i m w c
    obtain ⟨σ1, h1, h2⟩ := h
    simp only [bindLog, stableB_append, stableB_cons, Bool.and_eq_true] at hs
    exact ihb c _ τ h2 k z (bindLocal_stable σ1 m y k z (ihv w σ σ1 h1 k z hk hs.1) hs.2.1) hs.2.2
  | app f args ih =>
    intro b σ τ h k z hk hs
    cases b <;> simp only [impEqA, reduceCtorEq] at h
    rename_i g bs
    split at h
    · simp only [bindLog] at hs
      induction args generalizing bs σ with
      | nil =>
        cases bs <;> simp only [impEqAList, reduceCtorEq, Option.some.injEq] at h
        subst h; exact hk
      | cons a as iha =>
        cases bs <;> simp only [impEqAList, reduceCtorEq, Option.bind_eq_some_iff] at h
        rename_i b bs
        obtain ⟨σ1, h1, h2⟩ := h
        simp only [bindLogList, stableB_append, Bool.and_eq_true] at hs
        exact iha (fun a' ha' => ih a' (List.mem_cons_of_mem _ ha')) σ1
          (ih a List.mem_cons_self b σ σ1 h1 k z hk hs.1) bs hs.2 h2
    · cases h
  | ifThenElse c t e ihc _ _ =>
    intro b σ τ h k z hk hs
    cases b <;> simp only [impEqA, reduceCtorEq, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    rename_i c' t' e'
    obtain ⟨σc, hc, _, _, _, _, rfl⟩ := h
    simp only [bindLog, stableB_append, Bool.and_eq_true] at hs
    exact keepLocals_stable σc _ k z (ihc c' σ σc hc k z hk hs.1)
      (by simp only [stableB_append, Bool.and_eq_true]; exact hs.2)
  | unitVal =>
    intro b σ τ h k z hk _
    cases b <;> simp only [impEqA, reduceCtorEq, Option.some.injEq] at h
    subst h; exact hk
  | seq a1 a2 ih1 ih2 =>
    intro b σ τ h k z hk hs
    cases b <;> simp only [impEqA, reduceCtorEq, Option.bind_eq_some_iff] at h
    rename_i c d
    obtain ⟨σ1, h1, h2⟩ := h
    simp only [bindLog, stableB_append, Bool.and_eq_true] at hs
    exact ih2 d σ1 τ h2 k z (ih1 c σ σ1 h1 k z hk hs.1) hs.2
  | assign y v ih =>
    intro b σ τ h k z hk hs
    cases b <;> simp only [impEqA, reduceCtorEq, Option.map_eq_some_iff] at h
    rename_i m w
    obtain ⟨σ1, h1, rfl⟩ := h
    simp only [bindLog, stableB_append, stableB_cons, Bool.and_eq_true] at hs
    exact bindLocal_stable σ1 m y k z (ih w σ σ1 h1 k z hk hs.1) hs.2.1
  | forFold y lo hi body _ _ _ =>
    intro b σ τ h k z hk hs
    cases b <;> simp only [impEqA, reduceCtorEq] at h
    rename_i m lo' hi' c
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      simp only [bindLog] at hs
      exact keepLocals_stable σ _ k z hk hs
    · cases h
  | _ => intro b σ τ h; cases b <;> simp [impEqA] at h

/-- The printed local `k` holds, in the printed run's environment `ee`, the value
    the reading's environment `ex` holds at the reading's local `σ k`. -/
def LocalRel (σ : LocalMap) (ex ee : Env) : Prop := ∀ k z, σ k = some z → ee k = ex z

/-- Two runs end in the same value with environments related by `σ`, or both in an
    error. -/
def SimOut (σ : LocalMap) (p q : Outcome × Env) : Prop :=
  (∃ v, p.1 = .val v ∧ q.1 = .val v ∧ LocalRel σ p.2 q.2) ∨
    (∃ s s', p.1 = .err s ∧ q.1 = .err s')

/-- Two runs of argument lists end in the same values with environments related by
    `σ`, or both in no values. -/
def SimArgs (σ : LocalMap) (p q : Option (List Value) × Env) : Prop :=
  (∃ vs, p.1 = some vs ∧ q.1 = some vs ∧ LocalRel σ p.2 q.2) ∨ (p.1 = none ∧ q.1 = none)

/-- Two results of `evalImp` are both a value, with environments related by `σ`, or
    both no result. -/
def RunRel (σ : LocalMap) : Option (Value × Env) → Option (Value × Env) → Prop
  | none, none => True
  | some (v, ex), some (w, ee) => v = w ∧ LocalRel σ ex ee
  | _, _ => False

theorem localRel_idLocals (env : Env) : LocalRel idLocals env env := by
  intro k z h
  simp only [idLocals, Option.some.injEq] at h
  rw [h]

theorem localRel_idLocals_iff (ex ee : Env) : LocalRel idLocals ex ee ↔ ee = ex := by
  constructor
  · intro h; funext k; exact h k k rfl
  · rintro rfl; exact localRel_idLocals _

theorem runRel_idLocals (r : Option (Value × Env)) : RunRel idLocals r r := by
  rcases r with _ | ⟨v, env⟩
  · trivial
  · exact ⟨rfl, localRel_idLocals env⟩

theorem localRel_mono {σ σ' : LocalMap} {ex ee : Env} (h : LocalRel σ ex ee)
    (hs : ∀ k z, σ' k = some z → σ k = some z) : LocalRel σ' ex ee :=
  fun k z hk => h k z (hs k z hk)

theorem localRel_bind {σ : LocalMap} {ex ee : Env} (h : LocalRel σ ex ee) (m y : String)
    (v : Value) : LocalRel (bindLocal σ m y) (ex.extend y v) (ee.extend m v) := by
  intro k z hk
  unfold bindLocal at hk
  grind only [Env.extend_other, LocalRel.eq_def, Option.some_inj, Env.extend_same]

theorem simOut_mono {σ σ' : LocalMap} {p q : Outcome × Env} (h : SimOut σ p q)
    (hs : ∀ k z, σ' k = some z → σ k = some z) : SimOut σ' p q := by
  rcases h with ⟨v, h1, h2, hR⟩ | h
  · exact Or.inl ⟨v, h1, h2, localRel_mono hR hs⟩
  · exact Or.inr h

/-- The run `p` continued by `k` when it ends in a value. -/
def thenRun (p : Outcome × Env) (k : Value → Env → Outcome × Env) : Outcome × Env :=
  match p with
  | (.val v, e) => k v e
  | (o, e) => (o, e)

/-- The run `p` continued by `k` when it ends in a value, with no values otherwise. -/
def argsRun (p : Outcome × Env) (k : Value → Env → Option (List Value) × Env) :
    Option (List Value) × Env :=
  match p with
  | (.val v, e) => k v e
  | (_, e) => (none, e)

/-- The call of `f` on the values of an argument run. -/
def appRun (bi : Builtins) (f : String) (p : Option (List Value) × Env) : Outcome × Env :=
  match p with
  | (some vals, e) =>
    match bi f vals with
    | some v => (.val v, e)
    | none => (.err s!"unknown function or bad args: {f}", e)
  | (none, e) => (.err "non-value in function arguments", e)

theorem simOut_thenRun {σ τ : LocalMap} {p q : Outcome × Env}
    {k k' : Value → Env → Outcome × Env} (h : SimOut σ p q)
    (hk : ∀ v ex ee, LocalRel σ ex ee → SimOut τ (k v ex) (k' v ee)) :
    SimOut τ (thenRun p k) (thenRun q k') := by
  obtain ⟨o, e⟩ := p
  obtain ⟨o', e'⟩ := q
  rcases h with ⟨v, h1, h2, hR⟩ | ⟨s, s', h1, h2⟩
  · simp only at h1 h2 hR
    subst h1 h2
    exact hk v e e' hR
  · simp only at h1 h2
    subst h1 h2
    exact Or.inr ⟨s, s', rfl, rfl⟩

theorem simArgs_argsRun {σ τ : LocalMap} {p q : Outcome × Env}
    {k k' : Value → Env → Option (List Value) × Env} (h : SimOut σ p q)
    (hk : ∀ v ex ee, LocalRel σ ex ee → SimArgs τ (k v ex) (k' v ee)) :
    SimArgs τ (argsRun p k) (argsRun q k') := by
  obtain ⟨o, e⟩ := p
  obtain ⟨o', e'⟩ := q
  rcases h with ⟨v, h1, h2, hR⟩ | ⟨s, s', h1, h2⟩
  · simp only at h1 h2 hR
    subst h1 h2
    exact hk v e e' hR
  · simp only at h1 h2
    subst h1 h2
    exact Or.inr ⟨rfl, rfl⟩

theorem simArgs_cons {τ : LocalMap} {p q : Option (List Value) × Env} (v : Value)
    (h : SimArgs τ p q) : SimArgs τ (p.1.map (v :: ·), p.2) (q.1.map (v :: ·), q.2) := by
  rcases h with ⟨vs, h1, h2, hR⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨v :: vs, by simp [h1], by simp [h2], hR⟩
  · exact Or.inr ⟨by simp [h1], by simp [h2]⟩

theorem simOut_appRun (bi : Builtins) (f : String) {τ : LocalMap}
    {p q : Option (List Value) × Env} (h : SimArgs τ p q) :
    SimOut τ (appRun bi f p) (appRun bi f q) := by
  obtain ⟨o, e⟩ := p
  obtain ⟨o', e'⟩ := q
  rcases h with ⟨vs, h1, h2, hR⟩ | ⟨h1, h2⟩
  · simp only at h1 h2 hR
    subst h1 h2
    simp only [appRun]
    cases bi f vs
    · exact Or.inr ⟨_, _, rfl, rfl⟩
    · exact Or.inl ⟨_, rfl, rfl, hR⟩
  · simp only at h1 h2
    subst h1 h2
    exact Or.inr ⟨_, _, rfl, rfl⟩

section Simulation

variable (bi : Builtins)

theorem denoteArgs_nil_run (fuel : Nat) (env : Env) :
    (denoteArgs bi fuel []).run env = (some [], env) := by
  unfold denoteArgs
  rfl

theorem denoteArgs_cons_argsRun (fuel : Nat) (e : ImpExpr) (es : List ImpExpr) (env : Env) :
    (denoteArgs bi fuel (e :: es)).run env =
      argsRun ((denote bi fuel e).run env) fun v ea =>
        (((denoteArgs bi fuel es).run ea).1.map (v :: ·), ((denoteArgs bi fuel es).run ea).2) := by
  rw [denoteArgs_cons_run_eq]
  rcases (denote bi fuel e).run env with ⟨o, ea⟩
  cases o <;> rfl

theorem denote_app_appRun (fuel : Nat) (f : String) (args : List ImpExpr) (env : Env) :
    (denote bi fuel (.app f args)).run env = appRun bi f ((denoteArgs bi fuel args).run env) := by
  rw [denote_app_run_eq]
  rcases (denoteArgs bi fuel args).run env with ⟨mv, ea⟩
  cases mv <;> rfl

theorem denote_letBind_thenRun (fuel : Nat) (n : String) (v b : ImpExpr) (env : Env) :
    (denote bi fuel (.letBind n v b)).run env =
      thenRun ((denote bi fuel v).run env) fun w e => (denote bi fuel b).run (e.extend n w) := by
  rw [denote_letBind_run_eq]
  rcases (denote bi fuel v).run env with ⟨o, e⟩
  cases o <;> rfl

theorem denote_seq_thenRun (fuel : Nat) (a b : ImpExpr) (env : Env) :
    (denote bi fuel (.seq a b)).run env =
      thenRun ((denote bi fuel a).run env) fun _ e => (denote bi fuel b).run e := by
  rw [denote_seq_run_eq]
  rcases (denote bi fuel a).run env with ⟨o, e⟩
  cases o <;> rfl

theorem denote_assign_thenRun (fuel : Nat) (n : String) (v : ImpExpr) (env : Env) :
    (denote bi fuel (.assign n v)).run env =
      thenRun ((denote bi fuel v).run env) fun w e => (.val .unit, e.extend n w) := by
  rw [denote_assign_run_eq]
  rcases (denote bi fuel v).run env with ⟨o, e⟩
  cases o <;> rfl

theorem denote_ifThenElse_thenRun (fuel : Nat) (c t f : ImpExpr) (env : Env) :
    (denote bi fuel (.ifThenElse c t f)).run env =
      thenRun ((denote bi fuel c).run env) fun w e =>
        match w with
        | .bool true => (denote bi fuel t).run e
        | .bool false => (denote bi fuel f).run e
        | _ => (.err "if condition not a bool", e) := by
  rw [denote_ifThenElse_run_eq]
  rcases (denote bi fuel c).run env with ⟨o, e⟩
  cases o with
  | val w =>
    cases w with
    | bool bv => cases bv <;> rfl
    | _ => rfl
  | _ => rfl

/-- A counted loop whose bodies agree up to a correspondence that each trip keeps. -/
theorem denoteForLoop_impEqA (σ : LocalMap) (y m : String) (b c : ImpExpr)
    (hb : ∀ fuel ex ee, LocalRel (bindLocal σ m y) ex ee →
      SimOut σ ((denote bi fuel b).run ex) ((denote bi fuel c).run ee)) :
    ∀ fuel lo hi ex ee, LocalRel σ ex ee →
      SimOut σ ((denoteForLoop bi fuel y lo hi b).run ex)
        ((denoteForLoop bi fuel m lo hi c).run ee) := by
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi ex ee hR
    by_cases hl : hi ≤ lo
    · rw [denoteForLoop_ge_run (h := hl), denoteForLoop_ge_run (h := hl)]
      exact Or.inl ⟨_, rfl, rfl, hR⟩
    · rw [denoteForLoop_zero_run (h := by omega), denoteForLoop_zero_run (h := by omega)]
      exact Or.inr ⟨_, _, rfl, rfl⟩
  | succ n ih =>
    intro lo hi ex ee hR
    by_cases hl : hi ≤ lo
    · rw [denoteForLoop_ge_run (h := hl), denoteForLoop_ge_run (h := hl)]
      exact Or.inl ⟨_, rfl, rfl, hR⟩
    · rw [denoteForLoop_succ_run (h := by omega), denoteForLoop_succ_run (h := by omega)]
      have hS := hb (n + 1) _ _ (localRel_bind hR m y (.int lo))
      revert hS
      generalize (denote bi (n + 1) b).run (ex.extend y (.int lo)) = p
      generalize (denote bi (n + 1) c).run (ee.extend m (.int lo)) = q
      obtain ⟨o, e1⟩ := p
      obtain ⟨o', e2⟩ := q
      rintro (⟨v, h1, h2, hR1⟩ | ⟨s, s', h1, h2⟩)
      · simp only at h1 h2 hR1
        subst h1 h2
        exact ih (lo + 1) hi e1 e2 hR1
      · simp only at h1 h2
        subst h1 h2
        exact Or.inr ⟨_, _, rfl, rfl⟩

/-- **The comparison is a simulation.**  A reading and a printed expression that
    `impEqA` relates from `σ` to `τ` run, from environments related by `σ`, to the
    same value with environments related by `τ`, or both to an error. -/
theorem denote_impEqA (a : ImpExpr) : ∀ (b : ImpExpr) (σ τ : LocalMap),
    impEqA σ a b = some τ → ∀ fuel ex ee, LocalRel σ ex ee →
      SimOut τ ((denote bi fuel (forToLoop a)).run ex)
        ((denote bi fuel (forToLoop b)).run ee) := by
  induction a using ImpExpr.ind with
  | lit l =>
    intro b σ τ h fuel ex ee hR
    cases b <;> simp only [impEqA, reduceCtorEq] at h
    rename_i l'
    split at h
    · rename_i hl
      cases h
      rw [litEq_sound _ _ hl]
      simp only [forToLoop, denote_lit_eq]
      exact Or.inl ⟨_, rfl, rfl, hR⟩
    · cases h
  | var y =>
    intro b σ τ h fuel ex ee hR
    cases b <;> simp only [impEqA, reduceCtorEq] at h
    rename_i m
    split at h
    · rename_i hm
      cases h
      simp only [forToLoop, denote_var_run_eq]
      rw [hR m y hm]
      cases ex y
      · exact Or.inr ⟨_, _, rfl, rfl⟩
      · exact Or.inl ⟨_, rfl, rfl, hR⟩
    · cases h
  | letBind y v body ihv ihb =>
    intro b σ τ h fuel ex ee hR
    cases b <;> simp only [impEqA, reduceCtorEq, Option.bind_eq_some_iff] at h
    rename_i m w c
    obtain ⟨σ1, h1, h2⟩ := h
    simp only [forToLoop]
    rw [denote_letBind_thenRun, denote_letBind_thenRun]
    exact simOut_thenRun (ihv w σ σ1 h1 fuel ex ee hR) fun u ex1 ee1 hR1 =>
      ihb c _ τ h2 fuel _ _ (localRel_bind hR1 m y u)
  | app f args ih =>
    intro b σ τ h fuel ex ee hR
    cases b <;> simp only [impEqA, reduceCtorEq] at h
    rename_i g bs
    split at h
    · rename_i hfg
      subst hfg
      simp only [forToLoop]
      rw [denote_app_appRun, denote_app_appRun]
      refine simOut_appRun bi f ?_
      induction args generalizing bs σ ex ee with
      | nil =>
        cases bs <;> simp only [impEqAList, reduceCtorEq, Option.some.injEq] at h
        subst h
        simp only [forToLoopArgs, denoteArgs_nil_run]
        exact Or.inl ⟨[], rfl, rfl, hR⟩
      | cons a as iha =>
        cases bs <;> simp only [impEqAList, reduceCtorEq, Option.bind_eq_some_iff] at h
        rename_i b bs
        obtain ⟨σ1, h1, h2⟩ := h
        simp only [forToLoopArgs]
        rw [denoteArgs_cons_argsRun, denoteArgs_cons_argsRun]
        exact simArgs_argsRun (ih a List.mem_cons_self b σ σ1 h1 fuel ex ee hR)
          fun u ex1 ee1 hR1 => simArgs_cons u
            (iha (fun a' ha' => ih a' (List.mem_cons_of_mem _ ha')) σ1 ex1 ee1 hR1 bs h2)
    · cases h
  | ifThenElse c t e ihc iht ihe =>
    intro b σ τ h fuel ex ee hR
    cases b <;> simp only [impEqA, reduceCtorEq, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    rename_i c' t' e'
    obtain ⟨σc, hc, τ1, ht, τ2, he, rfl⟩ := h
    simp only [forToLoop]
    rw [denote_ifThenElse_thenRun, denote_ifThenElse_thenRun]
    refine simOut_thenRun (ihc c' σ σc hc fuel ex ee hR) fun u ex1 ee1 hR1 => ?_
    cases u with
    | bool bv =>
      cases bv
      · refine simOut_mono (ihe e' σc τ2 he fuel ex1 ee1 hR1) fun k z hk => ?_
        obtain ⟨hσ, hs⟩ := keepLocals_sub hk
        simp only [stableB_append, Bool.and_eq_true] at hs
        exact impEqA_frame _ _ _ _ he k z hσ hs.2
      · refine simOut_mono (iht t' σc τ1 ht fuel ex1 ee1 hR1) fun k z hk => ?_
        obtain ⟨hσ, hs⟩ := keepLocals_sub hk
        simp only [stableB_append, Bool.and_eq_true] at hs
        exact impEqA_frame _ _ _ _ ht k z hσ hs.1
    | _ => exact Or.inr ⟨_, _, rfl, rfl⟩
  | unitVal =>
    intro b σ τ h fuel ex ee hR
    cases b <;> simp only [impEqA, reduceCtorEq, Option.some.injEq] at h
    subst h
    simp only [forToLoop, denote_unitVal_eq]
    exact Or.inl ⟨_, rfl, rfl, hR⟩
  | seq a1 a2 ih1 ih2 =>
    intro b σ τ h fuel ex ee hR
    cases b <;> simp only [impEqA, reduceCtorEq, Option.bind_eq_some_iff] at h
    rename_i c d
    obtain ⟨σ1, h1, h2⟩ := h
    simp only [forToLoop]
    rw [denote_seq_thenRun, denote_seq_thenRun]
    exact simOut_thenRun (ih1 c σ σ1 h1 fuel ex ee hR) fun _ ex1 ee1 hR1 =>
      ih2 d σ1 τ h2 fuel ex1 ee1 hR1
  | assign y v ih =>
    intro b σ τ h fuel ex ee hR
    cases b <;> simp only [impEqA, reduceCtorEq, Option.map_eq_some_iff] at h
    rename_i m w
    obtain ⟨σ1, h1, rfl⟩ := h
    simp only [forToLoop]
    rw [denote_assign_thenRun, denote_assign_thenRun]
    exact simOut_thenRun (ih w σ σ1 h1 fuel ex ee hR) fun u ex1 ee1 hR1 =>
      Or.inl ⟨_, rfl, rfl, localRel_bind hR1 m y u⟩
  | forFold y lo hi body _ _ ihb =>
    intro b σ τ h fuel ex ee hR
    cases b <;> simp only [impEqA, reduceCtorEq] at h
    rename_i m lo' hi' c
    split at h
    · rename_i hb
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at hb
      obtain ⟨⟨⟨l, hh⟩, hlb⟩, heq⟩ := hb
      have hlb' := heq ▸ hlb
      obtain ⟨rfl, rfl⟩ := litBounds_eq_some hlb
      obtain ⟨rfl, rfl⟩ := litBounds_eq_some hlb'
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨τb, hbody, rfl⟩ := h
      simp only [forToLoop, denote_forLoop_lit_run]
      refine denoteForLoop_impEqA bi _ y m _ _ (fun fuel ex ee hR' =>
        simOut_mono (ihb c _ τb hbody fuel ex ee hR') fun k z hk => ?_) fuel l hh ex ee
        (localRel_mono hR fun k z hk => (keepLocals_sub hk).1)
      have hs := (keepLocals_sub hk).2
      simp only [stableB_cons, Bool.and_eq_true] at hs
      exact impEqA_frame _ _ _ _ hbody k z (bindLocal_stable _ m y k z hk hs.1) hs.2
    · cases h
  | _ => intro b σ τ h; cases b <;> simp [impEqA] at h

/-- `impEqA` relates the successful runs `evalImp`. -/
theorem evalImp_impEqA (a b : ImpExpr) (σ τ : LocalMap) (h : impEqA σ a b = some τ)
    (fuel : Nat) (ex ee : Env) (hR : LocalRel σ ex ee) :
    RunRel τ (evalImp bi fuel (forToLoop a) ex) (evalImp bi fuel (forToLoop b) ee) := by
  have hS := denote_impEqA bi a b σ τ h fuel ex ee hR
  unfold evalImp
  revert hS
  generalize (denote bi fuel (forToLoop a)).run ex = p
  generalize (denote bi fuel (forToLoop b)).run ee = q
  obtain ⟨o, e1⟩ := p
  obtain ⟨o', e2⟩ := q
  rintro (⟨v, h1, h2, hR1⟩ | ⟨s, s', h1, h2⟩)
  · simp only at h1 h2 hR1
    subst h1 h2
    exact ⟨rfl, hR1⟩
  · simp only at h1 h2
    subst h1 h2
    trivial

end Simulation

/-- **The check.**  The frontend's reading `extracted` of the printed text of
    `printed`, normalised, has the sequence normal form of `printed`, structurally
    (`haxReadEq`) or up to a renaming of locals (`impEqA`). -/
def haxReadAgrees (printed extracted : ImpExpr) : Bool :=
  haxReadEq printed extracted ||
    (impEqA idLocals (seqNF (normHaxRead extracted)) (seqNF printed)).isSome

/-- The correspondence of the printed locals with the reading's locals that the check
    establishes at the end of the run: the identity when `haxReadEq` holds. -/
def haxReadLocals (printed extracted : ImpExpr) : LocalMap :=
  if haxReadEq printed extracted then idLocals
  else (impEqA idLocals (seqNF (normHaxRead extracted)) (seqNF printed)).getD idLocals

/-- **Soundness of the check.**  A frontend reading that passes the check runs,
    under the source semantics and from the same environment, to the value the
    printed expression runs to, with the final environments related by
    `haxReadLocals`, or both fail. -/
theorem haxReadAgrees_sound (bi : Builtins) (h : HaxOpsAgree bi) (e x : ImpExpr)
    (hc : haxReadAgrees e x = true) (fuel : Nat) (env : Env) :
    RunRel (haxReadLocals e x) (evalImp bi fuel (forToLoop x) env)
      (evalImp bi fuel (forToLoop e) env) := by
  unfold haxReadLocals
  split
  · rename_i hq
    rw [haxReadEq_sound bi h e x hq fuel env]
    exact runRel_idLocals _
  · rename_i hq
    simp only [haxReadAgrees, hq, Bool.false_or, Option.isSome_iff_exists] at hc
    obtain ⟨τ, hτ⟩ := hc
    rw [hτ, Option.getD_some, ← evalImp_normHaxRead bi h x fuel env,
      ← evalImp_seqNF bi (normHaxRead x) fuel env, ← evalImp_seqNF bi e fuel env]
    exact evalImp_impEqA bi _ _ _ _ hτ fuel env env (localRel_idLocals env)

/-- A run of a reading that passes the check to a value is a run of the printed
    expression to that value, with the final environments related by
    `haxReadLocals`. -/
theorem haxReadAgrees_run (bi : Builtins) (h : HaxOpsAgree bi) (e x : ImpExpr)
    (hc : haxReadAgrees e x = true) (fuel : Nat) (env ex : Env) (v : Value)
    (hx : evalImp bi fuel (forToLoop x) env = some (v, ex)) :
    ∃ ee, evalImp bi fuel (forToLoop e) env = some (v, ee) ∧
      LocalRel (haxReadLocals e x) ex ee := by
  have hS := haxReadAgrees_sound bi h e x hc fuel env
  rw [hx] at hS
  revert hS
  rcases evalImp bi fuel (forToLoop e) env with _ | ⟨w, ee⟩
  · exact False.elim
  · rintro ⟨rfl, hR⟩
    exact ⟨ee, rfl, hR⟩

/-- The parser of `ImpRustPrint` reads a printed text back as the printed
    expression, and a frontend reading of that text that passes the check runs
    as it does. -/
theorem haxReadAgrees_parse (ty : String → Option ImpRust.Tok) (e x : ImpExpr) (t : String)
    (hp : ppImpRust ty e = some t) (hc : haxReadAgrees e x = true) :
    parseImpRust t = some e ∧
      ∀ bi, HaxOpsAgree bi → ∀ fuel env,
        RunRel (haxReadLocals e x) (evalImp bi fuel (forToLoop x) env)
          (evalImp bi fuel (forToLoop e) env) :=
  ⟨parse_ppImpRust ty e t hp, fun bi h fuel env => haxReadAgrees_sound bi h e x hc fuel env⟩

/-- The parser of `ImpRustPrint` reads a printed function with a return type
    back as its body, and a frontend reading of that body that passes the check
    runs as it does. -/
theorem haxReadAgrees_parseFnRet (name : String) (params : List (String × ImpRust.Tok))
    (retTy : ImpRust.Tok) (ty : String → Option ImpRust.Tok) (e x : ImpExpr) (t : String)
    (hp : ppImpRustFnRet name params retTy ty e = some t) (hc : haxReadAgrees e x = true) :
    parseImpRustFnRet t = some (name, params, retTy, e) ∧
      ∀ bi, HaxOpsAgree bi → ∀ fuel env,
        RunRel (haxReadLocals e x) (evalImp bi fuel (forToLoop x) env)
          (evalImp bi fuel (forToLoop e) env) :=
  ⟨parse_ppImpRustFnRet name params retTy ty e t hp,
    fun bi h fuel env => haxReadAgrees_sound bi h e x hc fuel env⟩

/-! ## §6  A program for the round trip

`roundTripImp` binds `x` to the leaf call `fp_mul(a, b)`, replaces it four
times by `fp_mul(x, b)` in a counted loop, and binds the scalar `s` to `c + d`.
The emit driver `bench/hax_roundtrip/emit_roundtrip.lean` prints it with
`ppImpRustFn` as the Rust function `roundtrip_prog` with the parameters
`roundTripParams` and the local types `roundTripTy`.  Its `LowCT` source and
the simulation are in `CatCrypt.Crypto.Hax.ImpRustHaxRoundTrip`. -/

/-- The round-trip program. -/
def roundTripImp : ImpExpr :=
  .letBind "x" (.app "fp_mul" [.var "a", .var "b"])
    (.seq (.forFold "i" (.lit (.int 0)) (.lit (.int 4))
        (.assign "x" (.app "fp_mul" [.var "x", .var "b"])))
      (.letBind "s" (.app "scalar#Add" [.var "c", .var "d"]) .unitVal))

/-- The Rust parameters of the printed function. -/
def roundTripParams : List (String × ImpRust.Tok) :=
  [("a", "[u64;6]"), ("b", "[u64;6]"), ("c", "u64"), ("d", "u64")]

/-- The Rust types of the locals of the printed function. -/
def roundTripTy (x : String) : Option ImpRust.Tok :=
  if x = "x" then some "[u64;6]" else if x = "s" then some "u64" else none

end CatCrypt.Crypto.Hax
