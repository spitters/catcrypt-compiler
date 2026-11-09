/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChain

/-!
# The call tree of the source semantics of `compileA`

The source semantics of the front `compileA` is the spine reading `denoteSpine` of a function
body at a builtin table (`haxRunsW`, `HaxModule.Runs`). This module reads the same semantics as a
finite interaction tree whose events are calls of a table: the reading `denoteSpineT` of a body
at a *tree table*, which answers a call by a tree, follows `denoteSpine` and `denote'` clause by
clause, and the adequacy theorem `runS_denoteSpineT` states that interpreting the tree under a
handler is `denoteSpine` at the table the handler induces. At the tree table of a module
(`moduleTreeTable`) the only events are the calls of its linked functions, with the name and
the argument values as the event and an optional value as the response (`none` when the callee
fails on the arguments, as a `Builtins` table answers); the calls of the functions of the
module are internal and run their own trees.

The tree is an ordinary inductive free monad without silent steps: the semantics is fuel
bounded, so every run is finite, and two trees are equivalent when they are equal. The proof of
adequacy for `denoteT` follows the functional induction principle `denote'.mutual_induct`.

## Main definitions

* `EventSig`, `CallTree`, `CallTree.bind`: an event signature and the free monad over it.
* `interp`, `interpSP`: interpretation of a tree under a pure handler, and under a handler in
  `SPComp`.
* `LinkCall`, `linkSig`: a call of a linked function, by name and argument values, answered by
  an optional value.
* `TreeTable`, `interpTable`: a table answering a call by a tree, and the builtin table a
  handler induces from it.
* `denoteT`, `denoteSpineT`: the readings `denote'` and `denoteSpine` at a tree table.
* `nfTree`: the call tree of the spine reading of an expression from an environment.
* `linkTreeTable`, `refBiT`, `moduleTreeTable`, `linkHandler`: the tree tables of a module,
  with a call of a linked function as an event, and the handler answering such a call by the
  meaning `sem` of the linked function.

## Main results

* `interp_bind`: interpretation is a monad morphism.
* `interpSP_pure`: under a handler of point masses, `interpSP` is the point mass at `interp`.
* `runS_denoteT`: interpreting the reading `denoteT` is `denote'` at the induced table.
* `runS_denoteSpineT`, `interp_nfTree`: interpreting the call tree is the spine reading
  `denoteSpine` at the induced table.
* `interp_nfTree_linkTable`: under `linkHandler m`, the call tree at the linked tree table of
  `m` interprets to `denoteSpine` at `m.linkTable`.
* `interp_nfTree_table`: under `linkHandler m`, the call tree at the tree table of `m`
  interprets to `denoteSpine` at `m.table`, the table of the source relation `HaxModule.Runs`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree

open _root_.Hax
open _root_.Hax.InlineLocalClosures
open CatCrypt.Core

/-! ## The free monad -/

/-- An event signature: a type of events and, for each event, the type of its responses. -/
structure EventSig where
  /-- The events. -/
  Event : Type
  /-- The responses to an event. -/
  Resp : Event → Type

/-- The finite interaction tree over the event signature `E`: `ret r` ends with the result `r`;
    `vis e c` performs the event `e` and continues with `c` at its response. -/
inductive CallTree (E : EventSig) (R : Type) where
  | ret : R → CallTree E R
  | vis : (e : E.Event) → (E.Resp e → CallTree E R) → CallTree E R

/-- Sequencing of trees: the continuation runs at the result of each leaf. -/
def CallTree.bind {E : EventSig} {α β : Type} :
    CallTree E α → (α → CallTree E β) → CallTree E β
  | .ret a, k => k a
  | .vis e c, k => .vis e (fun r => (c r).bind k)

/-- The free monad structure of `CallTree E`: `pure` is a leaf, `bind` is `CallTree.bind`. -/
instance {E : EventSig} : Monad (CallTree E) where
  pure := CallTree.ret
  bind := CallTree.bind

/-- Interpretation of a tree under a handler answering every event. -/
def interp {E : EventSig} {R : Type} (h : ∀ e : E.Event, E.Resp e) : CallTree E R → R
  | .ret r => r
  | .vis e c => interp h (c (h e))

/-- Interpretation of a tree in `SPComp` under a handler answering every event by a
    computation: a `vis` node binds the computation of the handler. -/
noncomputable def interpSP {E : EventSig} {R : Type} (h : ∀ e : E.Event, SPComp (E.Resp e)) :
    CallTree E R → SPComp R
  | .ret r => SPComp.pure r
  | .vis e k => (h e).bind (fun resp => interpSP h (k resp))

/-- Unfolding lemma of `interp` at a leaf. -/
@[simp] theorem interp_ret {E : EventSig} {R : Type} (h : ∀ e : E.Event, E.Resp e) (r : R) :
    interp h (CallTree.ret r) = r := rfl

/-- Unfolding lemma of `interp` at an event. -/
@[simp] theorem interp_vis {E : EventSig} {R : Type} (h : ∀ e : E.Event, E.Resp e)
    (e : E.Event) (c : E.Resp e → CallTree E R) :
    interp h (CallTree.vis e c) = interp h (c (h e)) := rfl

/-- Interpretation is a monad morphism: interpreting a sequence interprets the continuation at
    the interpreted result. -/
theorem interp_bind {E : EventSig} {α β : Type} (h : ∀ e : E.Event, E.Resp e)
    (t : CallTree E α) (k : α → CallTree E β) :
    interp h (t.bind k) = interp h (k (interp h t)) := by
  induction t with
  | ret a => rfl
  | vis e c ih => exact ih (h e)

/-- Unfolding lemma of `interpSP` at a leaf. -/
@[simp] theorem interpSP_ret {E : EventSig} {R : Type} (h : ∀ e : E.Event, SPComp (E.Resp e))
    (r : R) : interpSP h (CallTree.ret r) = SPComp.pure r := rfl

/-- Unfolding lemma of `interpSP` at an event. -/
@[simp] theorem interpSP_vis {E : EventSig} {R : Type} (h : ∀ e : E.Event, SPComp (E.Resp e))
    (e : E.Event) (k : E.Resp e → CallTree E R) :
    interpSP h (CallTree.vis e k) = (h e).bind (fun resp => interpSP h (k resp)) := rfl

/-! ## Linked calls as events -/

/-- A call of a linked function: its name and the argument values. -/
structure LinkCall where
  /-- The name of the callee. -/
  name : String
  /-- The argument values. -/
  args : List Value

/-- The event signature of linked calls: a call is answered by a value, or by `none` when the
    callee fails on the arguments. -/
def linkSig : EventSig where
  Event := LinkCall
  Resp := fun _ => Option Value

/-- A table answering a call by a tree over `E` of an optional value. -/
abbrev TreeTable (E : EventSig) : Type := String → List Value → CallTree E (Option Value)

/-- The builtin table a handler induces from a tree table. -/
def interpTable {E : EventSig} (h : ∀ e : E.Event, E.Resp e) (bt : TreeTable E) : Builtins :=
  fun g vals => interp h (bt g vals)

/-- The state monad over trees, in which the tree readings run. -/
abbrev TM (E : EventSig) : Type → Type := StateT Env (CallTree E)

/-- Interpretation of a stateful tree computation as a state computation. -/
def runS {E : EventSig} {α : Type} (h : ∀ e : E.Event, E.Resp e) (x : TM E α) : StateM Env α :=
  fun s => interp h (x s)

/-- Interpretation of stateful tree computations is a monad morphism. -/
theorem runS_bind {E : EventSig} {α β : Type} (h : ∀ e : E.Event, E.Resp e) (x : TM E α)
    (f : α → TM E β) : runS h (x >>= f) = runS h x >>= fun a => runS h (f a) := by
  funext s
  exact interp_bind h (x s) _

/-- A lifted tree interprets to the return of its interpretation. -/
theorem runS_lift {E : EventSig} {α : Type} (h : ∀ e : E.Event, E.Resp e) (t : CallTree E α) :
    runS h (StateT.lift t : TM E α) = pure (interp h t) := by
  funext s
  exact interp_bind h t _

/-! ## The reading `denote'` at a tree table -/

section Reading

variable {E : EventSig}

mutual

/-- The reading `denote'` at the tree table `bt`: clause by clause the reading of `denote'`,
    with a call answered by the tree of `bt`. -/
def denoteT (bt : TreeTable E) (fuel : Nat) : ImpExpr → TM E Outcome
  | .lit v => pure (.val (Value.ofLit v))
  | .var name => do
    let env ← get
    match env name with
    | some v => pure (.val v)
    | none => pure (.err s!"undefined variable: {name}")
  | .letBind name val body => do
    let rv ← denoteT bt fuel val
    match rv with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v => do modify (Env.extend · name v); denoteT bt fuel body
    | other => pure other
  | .lam _ _ =>
    pure (.err "closures are not evaluated by the reference semantics")
  | .app f args => denoteAppT bt fuel f args
  | .tuple elems => do
    let mvals ← denoteArgsT bt fuel elems
    match mvals with
    | some vals => pure (.val (.tuple vals))
    | none => pure (.err "non-value in tuple elements")
  | .proj e i => do
    let r ← denoteT bt fuel e
    match r with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v =>
      match v.projIdx i with
      | some vi => pure (.val vi)
      | none => pure (.err s!"projection index {i} out of range")
    | other => pure other
  | .ifThenElse c thn els => do
    let rc ← denoteT bt fuel c
    match rc with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val (.bool true) => denoteT bt fuel thn
    | .val (.bool false) => denoteT bt fuel els
    | .val _ => pure (.err "if condition not a bool")
    | other => pure other
  | .match_ scrut arms => do
    let rs ← denoteT bt fuel scrut
    match rs with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v => denoteMatchArmsT bt fuel v arms
    | other => pure other
  | .unitVal => pure (.val .unit)
  | .seq e1 e2 => do
    let r1 ← denoteT bt fuel e1
    match r1 with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val _ => denoteT bt fuel e2
    | other => pure other
  | .borrow e => denoteT bt fuel e
  | .deref e => denoteT bt fuel e
  | .assign name rhs => do
    let r ← denoteT bt fuel rhs
    match r with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v => do modify (Env.extend · name v); pure (.val .unit)
    | other => pure other
  | .forLoop var lo hi body => do
    let rlo ← denoteT bt fuel lo
    match rlo with
    | .val (.controlFlow _ _) => pure rlo
    | .val vlo => do
      let rhi ← denoteT bt fuel hi
      match vlo, rhi with
      | .int lo_val, .val (.int hi_val) =>
        denoteForLoopOrigT bt fuel var lo_val hi_val body
      | .int lo_val, .val (.uint _ hi_val) =>
        denoteForLoopOrigT bt fuel var lo_val hi_val body
      | .uint _ lo_val, .val (.int hi_val) =>
        denoteForLoopOrigT bt fuel var lo_val hi_val body
      | .uint _ lo_val, .val (.uint _ hi_val) =>
        denoteForLoopOrigT bt fuel var lo_val hi_val body
      | _, .val _ => pure (.err "for loop bounds must be integers")
      | _, other => pure other
    | other => pure other
  | .forLoopRev var lo hi body => do
    let rlo ← denoteT bt fuel lo
    match rlo with
    | .val (.controlFlow _ _) => pure rlo
    | .val vlo => do
      let rhi ← denoteT bt fuel hi
      match vlo, rhi with
      | .int lo_val, .val (.int hi_val) =>
        denoteForLoopRevOrigT bt fuel var lo_val hi_val body
      | .int lo_val, .val (.uint _ hi_val) =>
        denoteForLoopRevOrigT bt fuel var lo_val hi_val body
      | .uint _ lo_val, .val (.int hi_val) =>
        denoteForLoopRevOrigT bt fuel var lo_val hi_val body
      | .uint _ lo_val, .val (.uint _ hi_val) =>
        denoteForLoopRevOrigT bt fuel var lo_val hi_val body
      | _, .val _ => pure (.err "for loop bounds must be integers")
      | _, other => pure other
    | other => pure other
  | .whileLoop c body =>
    denoteWhileOrigT bt fuel c body
  | .break_ (some e) => do
    let r ← denoteT bt fuel e
    match r with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v => pure (.broke v)
    | other => pure other
  | .break_ none => pure (.broke .unit)
  | .continue_ => pure .continued
  | .earlyReturn e => do
    let r ← denoteT bt fuel e
    match r with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v => pure (.earlyRet v)
    | other => pure other
  | .questionMark e => do
    let r ← denoteT bt fuel e
    match r with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val (.result true v) => pure (.val v)
    | .val (.result false v) => pure (.earlyRet (.result false v))
    | .val _ => pure (.err "? operator on non-Result")
    | other => pure other
  | .forFold var lo hi body => do
    let rlo ← denoteT bt fuel lo
    match rlo with
    | .val (.controlFlow _ _) => pure rlo
    | .val vlo => do
      let rhi ← denoteT bt fuel hi
      match vlo, rhi with
      | .int lo_val, .val (.int hi_val) =>
        denoteForLoopT bt fuel var lo_val hi_val body
      | .int lo_val, .val (.uint _ hi_val) =>
        denoteForLoopT bt fuel var lo_val hi_val body
      | .uint _ lo_val, .val (.int hi_val) =>
        denoteForLoopT bt fuel var lo_val hi_val body
      | .uint _ lo_val, .val (.uint _ hi_val) =>
        denoteForLoopT bt fuel var lo_val hi_val body
      | _, .val (.controlFlow _ _) => pure rhi
      | _, .val _ => pure (.err "for loop bounds must be integers")
      | _, other => pure other
    | other => pure other
  | .forFoldRev var lo hi body => do
    let rlo ← denoteT bt fuel lo
    match rlo with
    | .val (.controlFlow _ _) => pure rlo
    | .val vlo => do
      let rhi ← denoteT bt fuel hi
      match vlo, rhi with
      | .int lo_val, .val (.int hi_val) =>
        denoteForLoopRevT bt fuel var lo_val hi_val body
      | .int lo_val, .val (.uint _ hi_val) =>
        denoteForLoopRevT bt fuel var lo_val hi_val body
      | .uint _ lo_val, .val (.int hi_val) =>
        denoteForLoopRevT bt fuel var lo_val hi_val body
      | .uint _ lo_val, .val (.uint _ hi_val) =>
        denoteForLoopRevT bt fuel var lo_val hi_val body
      | _, .val (.controlFlow _ _) => pure rhi
      | _, .val _ => pure (.err "for loop bounds must be integers")
      | _, other => pure other
    | other => pure other
  | .whileFold c body =>
    denoteWhileT bt fuel c body
  | .forFoldReturn var lo hi body => do
    let rlo ← denoteT bt fuel lo
    match rlo with
    | .val (.controlFlow _ _) => pure rlo
    | .val vlo => do
      let rhi ← denoteT bt fuel hi
      match vlo, rhi with
      | .int lo_val, .val (.int hi_val) =>
        denoteForLoopReturnT bt fuel var lo_val hi_val body
      | .int lo_val, .val (.uint _ hi_val) =>
        denoteForLoopReturnT bt fuel var lo_val hi_val body
      | .uint _ lo_val, .val (.int hi_val) =>
        denoteForLoopReturnT bt fuel var lo_val hi_val body
      | .uint _ lo_val, .val (.uint _ hi_val) =>
        denoteForLoopReturnT bt fuel var lo_val hi_val body
      | _, .val (.controlFlow _ _) => pure rhi
      | _, .val _ => pure (.err "for loop bounds must be integers")
      | _, other => pure other
    | other => pure other
  | .forFoldRevReturn var lo hi body => do
    let rlo ← denoteT bt fuel lo
    match rlo with
    | .val (.controlFlow _ _) => pure rlo
    | .val vlo => do
      let rhi ← denoteT bt fuel hi
      match vlo, rhi with
      | .int lo_val, .val (.int hi_val) =>
        denoteForLoopRevReturnT bt fuel var lo_val hi_val body
      | .int lo_val, .val (.uint _ hi_val) =>
        denoteForLoopRevReturnT bt fuel var lo_val hi_val body
      | .uint _ lo_val, .val (.int hi_val) =>
        denoteForLoopRevReturnT bt fuel var lo_val hi_val body
      | .uint _ lo_val, .val (.uint _ hi_val) =>
        denoteForLoopRevReturnT bt fuel var lo_val hi_val body
      | _, .val (.controlFlow _ _) => pure rhi
      | _, .val _ => pure (.err "for loop bounds must be integers")
      | _, other => pure other
    | other => pure other
  | .whileFoldReturn c body =>
    denoteWhileReturnT bt fuel c body
  | .cfBreak e => do
    let r ← denoteT bt fuel e
    match r with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v => pure (.val (.controlFlow true v))
    | other => pure other
  | .cfContinue e => do
    let r ← denoteT bt fuel e
    match r with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v => pure (.val (.controlFlow false v))
    | other => pure other
  | .cfBreakContinue e => do
    let r ← denoteT bt fuel e
    match r with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val v => pure (.val (.controlFlow true (.controlFlow false v)))
    | other => pure other
  | .typeAscription e _ => denoteT bt fuel e
  termination_by e => (fuel, sizeOf e)
  decreasing_by
    all_goals simp_wf
    all_goals (first | omega |
      (try (have := ImpExpr.sizeOf_pos lo);
       try (have := ImpExpr.sizeOf_pos hi);
       try (have := ImpExpr.sizeOf_pos body);
       try (have := string_sizeOf_pos f);
       omega))

/-- The reading of a call at a tree table: the arguments in order, then the tree of the
    table at the callee and the argument values. -/
def denoteAppT (bt : TreeTable E) (fuel : Nat) (f : String) (args : List ImpExpr) :
    TM E Outcome := do
  let mvals ← denoteArgsT bt fuel args
  match mvals with
  | some vals => do
    let r ← StateT.lift (bt f vals)
    match r with
    | some v => pure (.val v)
    | none => pure (.err s!"unknown function or bad args: {f}")
  | none => pure (.err "non-value in function arguments")
  termination_by (fuel, 1 + sizeOf args)

/-- The reading `denoteArgs'` of a list of arguments at a tree table. -/
def denoteArgsT (bt : TreeTable E) (fuel : Nat) :
    List ImpExpr → TM E (Option (List Value))
  | [] => pure (some [])
  | e :: es => do
    let r ← denoteT bt fuel e
    match r with
    | .val (.controlFlow _ _) => pure none
    | .val v => do
      let rest ← denoteArgsT bt fuel es
      pure (rest.map (v :: ·))
    | _ => pure none
  termination_by l => (fuel, sizeOf l)

/-- The reading `denoteMatchArms'` of match arms at a tree table. -/
def denoteMatchArmsT (bt : TreeTable E) (fuel : Nat)
    (v : Value) : List (ImpPat × ImpExpr) → TM E Outcome
  | [] => pure (.err "no matching pattern")
  | (pat, body) :: rest => do
    let env ← get
    match matchPat pat v env with
    | some env' => do set env'; denoteT bt fuel body
    | none => denoteMatchArmsT bt fuel v rest
  termination_by arms => (fuel, sizeOf arms)

/-- The reading `denoteForLoop'` at a tree table. -/
def denoteForLoopT (bt : TreeTable E) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) : TM E Outcome :=
  if lo ≥ hi then pure (.val .unit)
  else if fuel = 0 then pure (.err "out of fuel")
  else do
    modify (Env.extend · var (.int lo))
    let rb ← denoteT bt fuel body
    match rb with
    | .val (.controlFlow true v) => pure (.val v)
    | .val (.controlFlow false _) =>
      denoteForLoopT bt (fuel - 1) var (lo + 1) hi body
    | .val _ => denoteForLoopT bt (fuel - 1) var (lo + 1) hi body
    | other => pure other
  termination_by (fuel, sizeOf body + 1)

/-- The reading `denoteWhile'` at a tree table. -/
def denoteWhileT (bt : TreeTable E) (fuel : Nat)
    (cond body : ImpExpr) : TM E Outcome :=
  if fuel = 0 then pure (.err "out of fuel")
  else do
    let rc ← denoteT bt fuel cond
    match rc with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val (.bool true) => do
      let rb ← denoteT bt fuel body
      match rb with
      | .val (.controlFlow true v) => pure (.val v)
      | .val (.controlFlow false _) =>
        denoteWhileT bt (fuel - 1) cond body
      | .val _ => denoteWhileT bt (fuel - 1) cond body
      | other => pure other
    | .val (.bool false) => pure (.val .unit)
    | .val _ => pure (.err "while condition not a bool")
    | other => pure other
  termination_by (fuel, sizeOf cond + sizeOf body)
  decreasing_by
    all_goals (first | omega |
      (have := ImpExpr.sizeOf_pos cond;
       have := ImpExpr.sizeOf_pos body;
       omega))

/-- The reading `denoteForLoopOrig'` at a tree table. -/
def denoteForLoopOrigT (bt : TreeTable E) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) : TM E Outcome :=
  if lo ≥ hi then pure (.val .unit)
  else if fuel = 0 then pure (.err "out of fuel")
  else do
    modify (Env.extend · var (.int lo))
    let rb ← denoteT bt fuel body
    match rb with
    | .val _ | .continued =>
      denoteForLoopOrigT bt (fuel - 1) var (lo + 1) hi body
    | .broke v => pure (.val v)
    | other => pure other
  termination_by (fuel, sizeOf body + 1)

/-- The reading `denoteWhileOrig'` at a tree table. -/
def denoteWhileOrigT (bt : TreeTable E) (fuel : Nat)
    (cond body : ImpExpr) : TM E Outcome :=
  if fuel = 0 then pure (.err "out of fuel")
  else do
    let rc ← denoteT bt fuel cond
    match rc with
    | .val (.bool true) => do
      let rb ← denoteT bt fuel body
      match rb with
      | .val _ | .continued =>
        denoteWhileOrigT bt (fuel - 1) cond body
      | .broke v => pure (.val v)
      | other => pure other
    | .val (.bool false) => pure (.val .unit)
    | .val _ => pure (.err "while condition not a bool")
    | other => pure other
  termination_by (fuel, sizeOf cond + sizeOf body)
  decreasing_by
    all_goals (first | omega |
      (have := ImpExpr.sizeOf_pos cond;
       have := ImpExpr.sizeOf_pos body;
       omega))

/-- The reading `denoteForLoop'Return` at a tree table. -/
def denoteForLoopReturnT (bt : TreeTable E) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) : TM E Outcome :=
  if lo ≥ hi then pure (.val .unit)
  else if fuel = 0 then pure (.err "out of fuel")
  else do
    modify (Env.extend · var (.int lo))
    let rb ← denoteT bt fuel body
    match rb with
    | .val (.controlFlow true (.controlFlow false v)) => pure (.val v)
    | .val (.controlFlow true v) => pure (.val (.controlFlow true v))
    | .val (.controlFlow false _) =>
      denoteForLoopReturnT bt (fuel - 1) var (lo + 1) hi body
    | .val _ =>
      denoteForLoopReturnT bt (fuel - 1) var (lo + 1) hi body
    | other => pure other
  termination_by (fuel, sizeOf body + 1)

/-- The reading `denoteWhile'Return` at a tree table. -/
def denoteWhileReturnT (bt : TreeTable E) (fuel : Nat)
    (cond body : ImpExpr) : TM E Outcome :=
  if fuel = 0 then pure (.err "out of fuel")
  else do
    let rc ← denoteT bt fuel cond
    match rc with
    | .val (.controlFlow isBreak v) => pure (.val (.controlFlow isBreak v))
    | .val (.bool true) => do
      let rb ← denoteT bt fuel body
      match rb with
      | .val (.controlFlow true (.controlFlow false v)) => pure (.val v)
      | .val (.controlFlow true v) => pure (.val (.controlFlow true v))
      | .val (.controlFlow false _) =>
        denoteWhileReturnT bt (fuel - 1) cond body
      | .val _ =>
        denoteWhileReturnT bt (fuel - 1) cond body
      | other => pure other
    | .val (.bool false) => pure (.val .unit)
    | .val _ => pure (.err "while condition not a bool")
    | other => pure other
  termination_by (fuel, sizeOf cond + sizeOf body)
  decreasing_by
    all_goals (first | omega |
      (have := ImpExpr.sizeOf_pos cond;
       have := ImpExpr.sizeOf_pos body;
       omega))

/-- The reading `denoteForLoopRevOrig'` at a tree table. -/
def denoteForLoopRevOrigT (bt : TreeTable E) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) : TM E Outcome :=
  if lo ≥ hi then pure (.val .unit)
  else if fuel = 0 then pure (.err "out of fuel")
  else do
    modify (Env.extend · var (.int (hi - 1)))
    let rb ← denoteT bt fuel body
    match rb with
    | .val _ | .continued =>
      denoteForLoopRevOrigT bt (fuel - 1) var lo (hi - 1) body
    | .broke v => pure (.val v)
    | other => pure other
  termination_by (fuel, sizeOf body + 1)

/-- The reading `denoteForLoopRev'` at a tree table. -/
def denoteForLoopRevT (bt : TreeTable E) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) : TM E Outcome :=
  if lo ≥ hi then pure (.val .unit)
  else if fuel = 0 then pure (.err "out of fuel")
  else do
    modify (Env.extend · var (.int (hi - 1)))
    let rb ← denoteT bt fuel body
    match rb with
    | .val (.controlFlow true v) => pure (.val v)
    | .val (.controlFlow false _) =>
      denoteForLoopRevT bt (fuel - 1) var lo (hi - 1) body
    | .val _ => denoteForLoopRevT bt (fuel - 1) var lo (hi - 1) body
    | other => pure other
  termination_by (fuel, sizeOf body + 1)

/-- The reading `denoteForLoopRev'Return` at a tree table. -/
def denoteForLoopRevReturnT (bt : TreeTable E) (fuel : Nat)
    (var : String) (lo hi : Int) (body : ImpExpr) : TM E Outcome :=
  if lo ≥ hi then pure (.val .unit)
  else if fuel = 0 then pure (.err "out of fuel")
  else do
    modify (Env.extend · var (.int (hi - 1)))
    let rb ← denoteT bt fuel body
    match rb with
    | .val (.controlFlow true (.controlFlow false v)) => pure (.val v)
    | .val (.controlFlow true v) => pure (.val (.controlFlow true v))
    | .val (.controlFlow false _) =>
      denoteForLoopRevReturnT bt (fuel - 1) var lo (hi - 1) body
    | .val _ =>
      denoteForLoopRevReturnT bt (fuel - 1) var lo (hi - 1) body
    | other => pure other
  termination_by (fuel, sizeOf body + 1)

end

/-! ## Adequacy of the reading at a tree table -/

/-- A sequence interprets to a sequence when its parts do. -/
theorem runS_bind_congr {α β : Type} (h : ∀ e : E.Event, E.Resp e) {x : TM E α}
    {f : α → TM E β} {y : StateM Env α} {g : α → StateM Env β} (hx : runS h x = y)
    (hf : ∀ a, runS h (f a) = g a) : runS h (x >>= f) = y >>= g := by
  rw [runS_bind, hx]
  exact congrArg (y >>= ·) (funext hf)

/-- One step of the adequacy proof: a leaf, an induction hypothesis, a sequence, or a case
    split on a result. -/
local syntax "adeq_step" : tactic

macro_rules
  | `(tactic| adeq_step) => `(tactic| first
      | rfl
      | (simp only [*]; done)
      | (cases ‹Outcome.val _ = Outcome.val _›; adeq_step)
      | (refine runS_bind_congr _ ?_ ?_ <;> (try intro) <;> adeq_step)
      | (split <;> (try (rename_i hq; rw [hq])) <;> adeq_step)
      | (rw [runS_bind, runS_lift, pure_bind]; simp only [interpTable]; adeq_step)
      | (exfalso; grind))

/-- **Adequacy of the reading at a tree table**, for all thirteen readings at once:
    interpreting the reading at `bt` under `h` is the reading `denote'` (and its loop, argument
    and match helpers) at the table `interpTable h bt`. -/
theorem runS_denoteT_and (h : ∀ e : E.Event, E.Resp e) (bt : TreeTable E) :
    (∀ fuel e, runS h (denoteT bt fuel e) = denote' (interpTable h bt) fuel e) ∧
    (∀ fuel c b, runS h (denoteWhileReturnT bt fuel c b) =
      denoteWhile'Return (interpTable h bt) fuel c b) ∧
    (∀ fuel x lo hi b, runS h (denoteForLoopRevReturnT bt fuel x lo hi b) =
      denoteForLoopRev'Return (interpTable h bt) fuel x lo hi b) ∧
    (∀ fuel x lo hi b, runS h (denoteForLoopReturnT bt fuel x lo hi b) =
      denoteForLoop'Return (interpTable h bt) fuel x lo hi b) ∧
    (∀ fuel c b, runS h (denoteWhileT bt fuel c b) =
      denoteWhile' (interpTable h bt) fuel c b) ∧
    (∀ fuel x lo hi b, runS h (denoteForLoopRevT bt fuel x lo hi b) =
      denoteForLoopRev' (interpTable h bt) fuel x lo hi b) ∧
    (∀ fuel x lo hi b, runS h (denoteForLoopT bt fuel x lo hi b) =
      denoteForLoop' (interpTable h bt) fuel x lo hi b) ∧
    (∀ fuel c b, runS h (denoteWhileOrigT bt fuel c b) =
      denoteWhileOrig' (interpTable h bt) fuel c b) ∧
    (∀ fuel x lo hi b, runS h (denoteForLoopRevOrigT bt fuel x lo hi b) =
      denoteForLoopRevOrig' (interpTable h bt) fuel x lo hi b) ∧
    (∀ fuel x lo hi b, runS h (denoteForLoopOrigT bt fuel x lo hi b) =
      denoteForLoopOrig' (interpTable h bt) fuel x lo hi b) ∧
    (∀ fuel v arms, runS h (denoteMatchArmsT bt fuel v arms) =
      denoteMatchArms' (interpTable h bt) fuel v arms) ∧
    (∀ fuel args, runS h (denoteArgsT bt fuel args) =
      denoteArgs' (interpTable h bt) fuel args) ∧
    (∀ fuel f args, runS h (denoteAppT bt fuel f args) =
      denoteApp' (interpTable h bt) fuel f args) := by
  apply denote'.mutual_induct
  all_goals intros
  all_goals first
    | simp only [denoteT, denote']
    | rw [denoteWhileReturnT, denoteWhile'Return]
    | rw [denoteForLoopRevReturnT, denoteForLoopRev'Return]
    | rw [denoteForLoopReturnT, denoteForLoop'Return]
    | rw [denoteWhileT, denoteWhile']
    | rw [denoteForLoopRevT, denoteForLoopRev']
    | rw [denoteForLoopT, denoteForLoop']
    | rw [denoteWhileOrigT, denoteWhileOrig']
    | rw [denoteForLoopRevOrigT, denoteForLoopRevOrig']
    | rw [denoteForLoopOrigT, denoteForLoopOrig']
    | simp only [denoteMatchArmsT, denoteMatchArms']
    | simp only [denoteArgsT, denoteArgs']
    | rw [denoteAppT, denoteApp']
  case case7 =>
    refine runS_bind_congr _ (by assumption) ?_
    intro r
    split
    · rfl
    · rename_i v hv
      cases v
      all_goals first
        | exact (hv _ _ rfl).elim
        | (simp only []; split <;> (rename_i hq; rw [hq]; rfl))
    · adeq_step
  all_goals adeq_step

/-- **Adequacy of the reading at a tree table**: interpreting `denoteT` at `bt` under `h` is
    `denote'` at the table `interpTable h bt`. -/
theorem runS_denoteT (h : ∀ e : E.Event, E.Resp e) (bt : TreeTable E) (fuel : Nat)
    (e : ImpExpr) : runS h (denoteT bt fuel e) = denote' (interpTable h bt) fuel e :=
  (runS_denoteT_and h bt).1 fuel e

/-! ## The spine reading at a tree table -/

/-- The table `closureTable` at a tree table: the closure `f` runs the tree of the reading of
    its body from the environment of the binding extended by the arguments. -/
def closureTableT (bt : TreeTable E) (fuel₀ : Nat) (f : String) (ps : List String)
    (body : ImpExpr) (ρ : Env) : TreeTable E := fun g vals =>
  if g = f then
    if vals.length = ps.length then
      (denoteT bt fuel₀ body (bindAll ρ ps vals)).bind fun r =>
        .ret (match r.1 with
          | .val v => some v
          | _ => none)
    else .ret none
  else bt g vals

/-- The table a handler induces from the closure table at a tree table is the closure table at
    the induced table. -/
theorem interpTable_closureTableT (h : ∀ e : E.Event, E.Resp e) (bt : TreeTable E)
    (fuel₀ : Nat) (f : String) (ps : List String) (body : ImpExpr) (ρ : Env) :
    interpTable h (closureTableT bt fuel₀ f ps body ρ) =
      closureTable (interpTable h bt) fuel₀ f ps body ρ := by
  funext g vals
  have hrun := congrFun (runS_denoteT h bt fuel₀ body) (bindAll ρ ps vals)
  simp only [runS] at hrun
  simp only [interpTable, closureTableT, closureTable]
  split_ifs
  · rw [interp_bind, hrun]
    rfl
  · rfl
  · rfl

/-- The spine reading `denoteSpine` at a tree table: clause by clause the reading of
    `denoteSpine`, with `denoteT` in place of `denote'` and `closureTableT` in place of
    `closureTable`. -/
def denoteSpineT (bt : TreeTable E) (fuel : Nat) : ImpExpr → TM E Outcome
  | .letBind f (.lam ps body) cont =>
    if closureOk f ps body (inlineSpine cont) || blockOk f ps body (inlineSpine cont) then do
      let ρ ← get
      denoteSpineT (closureTableT bt fuel f ps body ρ) fuel cont
    else denoteT bt fuel (.letBind f (.lam ps body) cont)
  | .letBind x v cont => do
    let rv ← denoteT bt fuel v
    match rv with
    | .val (.controlFlow isBreak w) => pure (.val (.controlFlow isBreak w))
    | .val w => do modify (Env.extend · x w); denoteSpineT bt fuel cont
    | other => pure other
  | .seq a b => do
    let r ← denoteT bt fuel a
    match r with
    | .val (.controlFlow isBreak w) => pure (.val (.controlFlow isBreak w))
    | .val _ => denoteSpineT bt fuel b
    | other => pure other
  | e => denoteT bt fuel e

/-- **Adequacy of the spine reading at a tree table**: interpreting `denoteSpineT` at `bt`
    under `h` is `denoteSpine` at the table `interpTable h bt`. -/
theorem runS_denoteSpineT (h : ∀ e : E.Event, E.Resp e) (bt : TreeTable E) (fuel : Nat)
    (e : ImpExpr) : runS h (denoteSpineT bt fuel e) = denoteSpine (interpTable h bt) fuel e := by
  fun_induction denoteSpineT bt fuel e with
  | case1 bt f ps body cont hc ih =>
    simp only [denoteSpine, hc, ↓reduceIte]
    refine runS_bind_congr _ rfl fun ρ => ?_
    rw [ih ρ, interpTable_closureTableT]
  | case2 bt f ps body cont hc =>
    simp only [runS_denoteT, denoteSpine, hc, ↓reduceIte, Bool.false_eq_true]
  | case3 bt x v cont hv ih =>
    rw [denoteSpine]
    · refine runS_bind_congr _ (runS_denoteT h bt fuel v) fun r => ?_
      adeq_step
    · exact hv
  | case4 bt a b ih =>
    rw [denoteSpine]
    refine runS_bind_congr _ (runS_denoteT h bt fuel a) fun r => ?_
    adeq_step
  | case5 bt e h1 h2 h3 =>
    rw [runS_denoteT, denoteSpine]
    all_goals grind

/-- **The call tree** of the spine reading of `e` at the tree table `bt` and the fuel `fuel`,
    from the environment `env`: its events are the events of the trees of `bt`, and its leaves
    carry the outcome and the final environment. -/
def nfTree (bt : TreeTable E) (fuel : Nat) (e : ImpExpr) (env : Env) :
    CallTree E (Outcome × Env) :=
  denoteSpineT bt fuel e env

/-- **Adequacy of the call tree**: interpreting the call tree under `h` is the run of the spine
    reading `denoteSpine` at the table `interpTable h bt`. -/
theorem interp_nfTree (h : ∀ e : E.Event, E.Resp e) (bt : TreeTable E) (fuel : Nat)
    (e : ImpExpr) (env : Env) :
    interp h (nfTree bt fuel e env) = (denoteSpine (interpTable h bt) fuel e).run env :=
  congrFun (runS_denoteSpineT h bt fuel e) env

end Reading

/-- Interpreting a tree in `SPComp` under a handler that returns the answers of a pure handler
    is the point mass at the pure interpretation. -/
theorem interpSP_pure {E : EventSig} {R : Type} (h : ∀ e : E.Event, E.Resp e)
    (t : CallTree E R) : interpSP (fun e => SPComp.pure (h e)) t = SPComp.pure (interp h t) := by
  induction t with
  | ret r => rfl
  | vis e c ih => simp only [interpSP_vis, interp_vis, SPComp.pure_bind, ih]

/-! ## The call tree of a module -/

open CatCrypt.Crypto.Hax in
/-- The handler of the linked functions of the module `m`: a call is answered by the meaning
    `sem` of the first linked function with its name, on the argument values, and a call of
    another name by `none`. -/
def linkHandler (m : HaxModule) : ∀ e : linkSig.Event, linkSig.Resp e := fun e =>
  match m.linked.find? (·.name == e.name) with
  | some l => l.sem e.args
  | none => none

open CatCrypt.Crypto.Hax in
/-- The linked tree table of the module `m` over the table `bi`: a call of a linked function of
    `m` is an event, with the name and the argument values; every other call is answered by
    `bi` without an event. -/
def linkTreeTable (m : HaxModule) (bi : Builtins) : TreeTable linkSig := fun g vals =>
  match m.linked.find? (·.name == g) with
  | some _ => .vis (⟨g, vals⟩ : LinkCall) fun r => .ret r
  | none => .ret (bi g vals)

open CatCrypt.Crypto.Hax in
/-- Under the handler of the linked functions, the linked tree table induces the table
    `HaxModule.linkTable` of the linked functions. -/
theorem interpTable_linkTreeTable (m : HaxModule) (bi : Builtins) :
    interpTable (linkHandler m) (linkTreeTable m bi) = m.linkTable bi := by
  funext g vals
  simp only [interpTable, linkTreeTable, HaxModule.linkTable, linkBi]
  split <;> rename_i hq
  · change linkHandler m ⟨g, vals⟩ = _
    simp only [linkHandler, hq]
    rfl
  · rw [hq]
    rfl

open CatCrypt.Crypto.Hax in
/-- The table `refBi` of the functions `fs` at a tree table: a call of a function of `fs` runs
    the call tree of the spine reading of its extraction at the table of the next smaller depth,
    and is internal (no event of its own); every other call is a call of `bt`. -/
def refBiT {E : EventSig} (fs : List ModFn) (bt : TreeTable E) (fuel : Nat) :
    Nat → TreeTable E
  | 0, g, vals =>
      match fs.find? (·.name == g) with
      | some _ => .ret none
      | none => bt g vals
  | n + 1, g, vals =>
      match fs.find? (·.name == g) with
      | some f =>
          (nfTree (refBiT fs bt fuel n) fuel f.texpr.erase
              (ImpToNF.paramsEnv (f.params.map (·.1)) vals)).bind fun r =>
            .ret (match r.1 with
              | .val v => if (ImpToNF.dec f.res v).isSome then some v else none
              | _ => none)
      | none => bt g vals

open CatCrypt.Crypto.Hax in
/-- The table a handler induces from `refBiT` is `refBi` at the induced table. -/
theorem interpTable_refBiT {E : EventSig} (h : ∀ e : E.Event, E.Resp e) (fs : List ModFn)
    (bt : TreeTable E) (fuel : Nat) (n : Nat) :
    interpTable h (refBiT fs bt fuel n) = refBi fs (interpTable h bt) fuel n := by
  induction n with
  | zero =>
    funext g vals
    simp only [interpTable, refBiT, refBi]
    split <;> rename_i hq
    · rw [hq]
      rfl
    · rw [hq]
  | succ n ih =>
    funext g vals
    simp only [interpTable, refBiT, refBi]
    split <;> rename_i hq
    · rw [interp_bind, interp_nfTree, ih, hq]
      rfl
    · rw [hq]

open CatCrypt.Crypto.Hax in
/-- **The tree table of the module `m`** over the table `bi`, its functions run at the fuel
    `fuelC`: `refBiT` at its functions and its depth over the linked tree table. The events are
    the calls of the linked functions of `m`, from the entry or from a function of `m`. -/
def moduleTreeTable (m : HaxModule) (bi : Builtins) (fuelC : Nat) : TreeTable linkSig :=
  refBiT m.fns (linkTreeTable m bi) fuelC m.depth

open CatCrypt.Crypto.Hax in
/-- Under the handler of the linked functions, the tree table of a module induces the table
    `HaxModule.table` of the module. -/
theorem interpTable_moduleTreeTable (m : HaxModule) (bi : Builtins) (fuelC : Nat) :
    interpTable (linkHandler m) (moduleTreeTable m bi fuelC) = m.table bi fuelC := by
  rw [moduleTreeTable, interpTable_refBiT, interpTable_linkTreeTable]
  rfl

open CatCrypt.Crypto.Hax in
/-- **Adequacy at the linked table**: under the handler of the linked functions of `m`, the call
    tree of `e` at the linked tree table interprets to the run of `denoteSpine` at
    `m.linkTable bi`. -/
theorem interp_nfTree_linkTable (m : HaxModule) (bi : Builtins) (fuel : Nat) (e : ImpExpr)
    (env : Env) :
    interp (linkHandler m) (nfTree (linkTreeTable m bi) fuel e env) =
      (denoteSpine (m.linkTable bi) fuel e).run env := by
  rw [interp_nfTree, interpTable_linkTreeTable]

open CatCrypt.Crypto.Hax in
/-- **Adequacy at the table of the module**: under the handler of the linked functions of `m`,
    the call tree of `e` at the tree table of `m` interprets to the run of `denoteSpine` at
    `m.table bi fuelC`, the table of the source relation `HaxModule.Runs`. -/
theorem interp_nfTree_table (m : HaxModule) (bi : Builtins) (fuelC fuel : Nat) (e : ImpExpr)
    (env : Env) :
    interp (linkHandler m) (nfTree (moduleTreeTable m bi fuelC) fuel e env) =
      (denoteSpine (m.table bi fuelC) fuel e).run env := by
  rw [interp_nfTree, interpTable_moduleTreeTable]

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
