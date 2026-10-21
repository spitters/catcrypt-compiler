/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.CT.LowCTLeakage
public import CatCrypt.Crypto.Hax.HaxCallNames
public import HaxLean.SemanticsCF

/-!
# Source leakage of hax `ImpExpr` under `denote'`

The leakage of a run of `Hax.denote'` and constant time at the source, for a level
table over the variables of the environment.

## The leakage

`srcLeak M bi e fuel env` is the leakage of the run of `denote' bi fuel e` from `env`.
It is structured: a tree (`SrcLeak`) whose shape follows the evaluation, with the
events at its leaves (`SrcEv`):

* `branch b` — the outcome of the condition of an `ifThenElse` and of each guard test
  of a `whileFold`/`whileFoldReturn`;
* `exit` — a `cfBreak` that ends the enclosing loop or the function;
* `bound lo hi` — the bounds of a counted loop, read before its first trip;
* `op l` — a call of a two-operand scalar operation on variables (`scalarOpExpr`): the
  operand events `l` of its `SExpr` in the leakage model `M` of CTP-1 (`sexprLeak`),
  which are empty unless `M` classes an instruction of the operation variable time;
* `opaque env e` — a construct outside the modelled set: the whole environment;
* `declass v` — a call `declassify x` of the builtin `declassify` on a variable `x`: the
  value `v` of `x`.

The last event makes the model conservative: a program containing an unmodelled
construct is constant time only for runs from equal environments at that point.

Each evaluation step of `denote'` that decides control flow leaves one event, and the
leakage of a compound expression is the `cat` of the leakages of its parts in
evaluation order, with the leakage of a part that does not run omitted. The flat
leakage is `SrcLeak.flatten`; asking for equal trees (`SourceCT`) is at least as strong
as asking for equal flat traces.

## Constant time at the source

`PubEqEnv lt env₁ env₂`: the two environments agree on the variables `lt` marks
public. `SourceCT M bi lt e`: two runs of `e` at the same fuel from environments
agreeing on the public variables, both ending in a value, have equal leakage.

## Constant time modulo declassification

`SrcLeak.decls` is the sequence of declassified values of a leakage tree.
`SourceCTDOf bi L lt e`: for every sequence `d`, two runs of `e` from environments agreeing
on the public variables, both ending in a value, whose leakages `L` declassify `d`, have
equal leakage. `SourceCTD M bi lt e` is `SourceCTDOf` for `srcLeak M bi`; `SourceCT`
implies it (`SourceCT.sourceCTD`), and an expression without a `declassify` call at a
position `srcLeak` traverses (`DeclassFree`) declassifies no value
(`srcLeak_decls_of_declassFree`).

## Determinism of the traced `LowCT` semantics

`rustExecLeak_det`: two traced runs of a `LowCT` program from one state have the same
trace and the same final state. `sexprReadsOnly S e` states that `e` reads only the
scalar slots in `S` and no tower limb; `sexprLeak_congr` states that its leakage is then
determined by those slots.

## Main definitions

* `SrcEv`, `SrcLeak`, `SrcLeak.flatten`
* `boundInt`, `envScalarState`, `opLeak`, `tripCont`, `contLeak`
* `whileLeak`, `forLeak`, `forRevLeak`, `boundsLeak`, `srcLeak`
* `PubEqEnv`, `SourceCT`
* `SrcEv.declOf`, `SrcLeak.decls`, `SourceCTDOf`, `SourceCTD`, `DeclassFree`
* `sexprReadsOnly`

## Main results

* `SourceCT.sourceCTD`, `srcLeak_decls_of_declassFree`
* `rustExecLeak_det`
* `evalState_congr`, `sexprLeak_congr`
* `scalarOpExpr_readsOnly` — the `SExpr` of a scalar operation on the variables `a`
  and `b` reads only `a` and `b`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr Value Env Outcome Builtins denote')
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak LowCTLeakModel sexprLeak nodeLeak
  RustExecLeak)

/-! ## The leakage of a source run -/

/-- An event of the source leakage. -/
inductive SrcEv where
  /-- The outcome of a condition or a loop guard. -/
  | branch (b : Bool)
  /-- A `cfBreak` that ends the enclosing loop or the function. -/
  | exit
  /-- The bounds of a counted loop. -/
  | bound (lo hi : Int)
  /-- The operand events of a scalar operation in the CTP-1 leakage model. -/
  | op (l : List CTLeak)
  /-- A construct outside the modelled set, with the whole environment. -/
  | opaque (env : Env) (e : ImpExpr)
  /-- A call of the builtin `declassify`, with the value of its argument. -/
  | declass (v : Value)

/-- The value a source event declassifies: `v` for `declass v`, none otherwise. -/
def SrcEv.declOf : SrcEv → Option Value
  | .declass v => some v
  | _ => none

/-- The source leakage: a tree whose shape follows the evaluation. -/
inductive SrcLeak where
  | nil
  | ev (x : SrcEv)
  | cat (a b : SrcLeak)

/-- The events of a leakage tree, in evaluation order. -/
def SrcLeak.flatten : SrcLeak → List SrcEv
  | .nil => []
  | .ev x => [x]
  | .cat a b => a.flatten ++ b.flatten

/-- The declassified values of a leakage tree, in evaluation order. -/
def SrcLeak.decls : SrcLeak → List Value
  | .nil => []
  | .ev x => x.declOf.toList
  | .cat a b => a.decls ++ b.decls

/-- The integer a counted-loop bound denotes: an integer or an unsigned word. -/
def boundInt : Value → Option Int
  | .int n => some n
  | .uint _ n => some n
  | _ => none

/-- The scalar slots an environment determines: the decoding of each bound variable,
    `0` elsewhere, and no tower value. -/
def envScalarState (env : Env) : RustState :=
  { rsTower := fun _ => none, rsScalar := fun x => ((env x).bind valueToScalar).getD 0 }

/-- The leakage of a call `op a b` on two variables: the CTP-1 operand events of the
    scalar expression of `op`, or the whole environment when `op` is not a scalar
    operation. -/
def opLeak (M : LowCTLeakModel) (op a b : String) (env : Env) : SrcEv :=
  match scalarOpExpr op (.SVar a) (.SVar b) with
  | some se => .op (sexprLeak M (envScalarState env) se)
  | none => .opaque env (.app op [.var a, .var b])

/-- The leakage after a loop trip whose body ran to `o`: none when the body ended in
    a `controlFlow true` value or not in a value, and `k e2` for the environment `e2`
    after a trip that continues. -/
def tripCont (o : Outcome × Env) (k : Env → SrcLeak) : SrcLeak :=
  match o with
  | (.val (.controlFlow true _), _) => .nil
  | (.val _, e2) => k e2
  | _ => .nil

theorem tripCont_val {w : Value} (hw : w.isControlFlow = false) (e2 : Env)
    (k : Env → SrcLeak) : tripCont (.val w, e2) k = k e2 := by
  cases w <;> first | rfl | simp at hw

theorem tripCont_exit (w : Value) (e2 : Env) (k : Env → SrcLeak) :
    tripCont (.val (.controlFlow true w), e2) k = .nil := rfl

/-- The leakage of a `whileFold`/`whileFoldReturn` run at fuel `n + 1`, from the
    leakages `lc` of the guard and `lb` of the body: the guard's leakage and outcome,
    and at a `true` guard the body's leakage followed, unless the body ended in a
    `controlFlow true` value, by the leakage of the loop at fuel `n`. -/
def whileLeak (bi : Builtins) (c body : ImpExpr) (lc lb : Nat → Env → SrcLeak) :
    Nat → Env → SrcLeak
  | 0, _ => .nil
  | n + 1, env =>
    .cat (lc (n + 1) env)
      (match (denote' bi (n + 1) c).run env with
       | (.val (.bool true), e1) =>
         .cat (.ev (.branch true)) (.cat (lb (n + 1) e1)
           (tripCont ((denote' bi (n + 1) body).run e1) fun e2 =>
             whileLeak bi c body lc lb n e2))
       | (.val (.bool false), _) => .ev (.branch false)
       | _ => .nil)

/-- The leakage of the trips of a counted loop from `lo` up to `hi` at fuel `n + 1`:
    the body's leakage with the counter bound to `lo`, followed, unless the body
    ended in a `controlFlow true` value, by the trips from `lo + 1` at fuel `n`. -/
def forLeak (bi : Builtins) (i : String) (body : ImpExpr) (lb : Nat → Env → SrcLeak) :
    Nat → Int → Int → Env → SrcLeak
  | 0, _, _, _ => .nil
  | n + 1, lo, hi, env =>
    if lo ≥ hi then .nil else
      .cat (lb (n + 1) (env.extend i (.int lo)))
        (tripCont ((denote' bi (n + 1) body).run (env.extend i (.int lo))) fun e2 =>
          forLeak bi i body lb n (lo + 1) hi e2)

/-- `forLeak` for a loop counting down from `hi - 1` to `lo`. -/
def forRevLeak (bi : Builtins) (i : String) (body : ImpExpr) (lb : Nat → Env → SrcLeak) :
    Nat → Int → Int → Env → SrcLeak
  | 0, _, _, _ => .nil
  | n + 1, lo, hi, env =>
    if lo ≥ hi then .nil else
      .cat (lb (n + 1) (env.extend i (.int (hi - 1))))
        (tripCont ((denote' bi (n + 1) body).run (env.extend i (.int (hi - 1)))) fun e2 =>
          forRevLeak bi i body lb n lo (hi - 1) e2)

/-- The leakage of the bounds of a counted loop and of its trips: the leakage of
    the lower bound, then, when it is a value that is not a control-flow value, of the
    upper bound, then, when both denote integers, the `bound` event and the trips
    `trips lo hi` from the environment after the bounds. -/
def boundsLeak (bi : Builtins) (lo hi : ImpExpr) (llo lhi : Env → SrcLeak)
    (fuel : Nat) (trips : Int → Int → Env → SrcLeak) (env : Env) : SrcLeak :=
  .cat (llo env)
    (match (denote' bi fuel lo).run env with
     | (.val (.controlFlow _ _), _) => .nil
     | (.val vlo, e1) =>
       .cat (lhi e1)
         (match (denote' bi fuel hi).run e1 with
          | (.val vhi, e2) =>
            match boundInt vlo, boundInt vhi with
            | some l, some h => .cat (.ev (.bound l h)) (trips l h e2)
            | _, _ => .nil
          | _ => .nil)
     | _ => .nil)

/-- The leakage of a run that continues with `k` after the value `w` of a part: `k w`
    unless `w` is a control-flow value. -/
def contLeak (o : Outcome × Env) (k : Value → Env → SrcLeak) : SrcLeak :=
  match o with
  | (.val (.controlFlow _ _), _) => .nil
  | (.val w, e1) => k w e1
  | _ => .nil

/-- **The source leakage** of the run of `denote' bi fuel e` from `env` (see the module
    docstring). -/
def srcLeak (M : LowCTLeakModel) (bi : Builtins) : ImpExpr → Nat → Env → SrcLeak
  | .lit _, _, _ => .nil
  | .var _, _, _ => .nil
  | .unitVal, _, _ => .nil
  | .typeAscription e _, fuel, env => srcLeak M bi e fuel env
  | .letBind n v body, fuel, env =>
    .cat (srcLeak M bi v fuel env)
      (contLeak ((denote' bi fuel v).run env) fun w e1 => srcLeak M bi body fuel (e1.extend n w))
  | .app op [.var a, .var b], _, env => .ev (opLeak M op a b env)
  | .app "declassify" [.var x], _, env =>
    match env x with
    | some v => .ev (.declass v)
    | none => .nil
  | .seq a b, fuel, env =>
    .cat (srcLeak M bi a fuel env)
      (contLeak ((denote' bi fuel a).run env) fun _ e1 => srcLeak M bi b fuel e1)
  | .ifThenElse c t e, fuel, env =>
    .cat (srcLeak M bi c fuel env)
      (match (denote' bi fuel c).run env with
       | (.val (.bool true), e1) => .cat (.ev (.branch true)) (srcLeak M bi t fuel e1)
       | (.val (.bool false), e1) => .cat (.ev (.branch false)) (srcLeak M bi e fuel e1)
       | _ => .nil)
  | .cfBreak e, fuel, env =>
    .cat (srcLeak M bi e fuel env) (contLeak ((denote' bi fuel e).run env) fun _ _ => .ev .exit)
  | .whileFoldReturn c body, fuel, env =>
    whileLeak bi c body (srcLeak M bi c) (srcLeak M bi body) fuel env
  | .whileFold c body, fuel, env =>
    whileLeak bi c body (srcLeak M bi c) (srcLeak M bi body) fuel env
  | .forFoldReturn i lo hi body, fuel, env =>
    boundsLeak bi lo hi (srcLeak M bi lo fuel) (srcLeak M bi hi fuel) fuel
      (fun l h => forLeak bi i body (srcLeak M bi body) fuel l h) env
  | .forFold i lo hi body, fuel, env =>
    boundsLeak bi lo hi (srcLeak M bi lo fuel) (srcLeak M bi hi fuel) fuel
      (fun l h => forLeak bi i body (srcLeak M bi body) fuel l h) env
  | .forFoldRevReturn i lo hi body, fuel, env =>
    boundsLeak bi lo hi (srcLeak M bi lo fuel) (srcLeak M bi hi fuel) fuel
      (fun l h => forRevLeak bi i body (srcLeak M bi body) fuel l h) env
  | e, _, env => .ev (.opaque env e)

/-! ## Constant time at the source -/

/-- Two environments agree on the variables `lt` marks public. -/
def PubEqEnv (lt : LevelTable) (env₁ env₂ : Env) : Prop :=
  ∀ x, lt x = .Public → env₁ x = env₂ x

/-- **Source constant time** of `e` for the split `lt`: two runs of `e` at the same
    fuel from environments agreeing on the public variables, both ending in a value,
    have equal leakage. -/
def SourceCT (M : LowCTLeakModel) (bi : Builtins) (lt : LevelTable) (e : ImpExpr) : Prop :=
  ∀ (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome),
    PubEqEnv lt env₁ env₂ →
    (denote' bi fuel e).run env₁ = (o₁, env₁') → (∃ v, o₁ = .val v) →
    (denote' bi fuel e).run env₂ = (o₂, env₂') → (∃ v, o₂ = .val v) →
    srcLeak M bi e fuel env₁ = srcLeak M bi e fuel env₂

/-! ## Constant time modulo declassification -/

/-- **Source constant time modulo declassification** of `e` for the split `lt` and the
    source leakage `L`: for every sequence `d` of values, two runs of `e` at the same fuel
    from environments agreeing on the public variables, both ending in a value, whose
    leakages declassify the values `d` (`SrcLeak.decls`), have equal leakage. -/
def SourceCTDOf (bi : Builtins) (L : ImpExpr → Nat → Env → SrcLeak) (lt : LevelTable)
    (e : ImpExpr) : Prop :=
  ∀ (d : List Value) (fuel : Nat) (env₁ env₂ env₁' env₂' : Env) (o₁ o₂ : Outcome),
    PubEqEnv lt env₁ env₂ →
    (denote' bi fuel e).run env₁ = (o₁, env₁') → (∃ v, o₁ = .val v) →
    (denote' bi fuel e).run env₂ = (o₂, env₂') → (∃ v, o₂ = .val v) →
    (L e fuel env₁).decls = d → (L e fuel env₂).decls = d →
    L e fuel env₁ = L e fuel env₂

/-- **Source constant time modulo declassification** for the source leakage `srcLeak`. -/
abbrev SourceCTD (M : LowCTLeakModel) (bi : Builtins) (lt : LevelTable) (e : ImpExpr) : Prop :=
  SourceCTDOf bi (srcLeak M bi) lt e

/-- Source constant time implies source constant time modulo declassification. -/
theorem SourceCT.sourceCTD {M : LowCTLeakModel} {bi : Builtins} {lt : LevelTable}
    {e : ImpExpr} (h : SourceCT M bi lt e) : SourceCTD M bi lt e :=
  fun _ fuel _ _ _ _ _ _ hp r₁ v₁ r₂ v₂ _ _ => h fuel _ _ _ _ _ _ hp r₁ v₁ r₂ v₂

/-- `e` calls `declassify` at no position the source leakage `srcLeak` traverses. -/
def DeclassFree : ImpExpr → Prop
  | .typeAscription e _ => DeclassFree e
  | .letBind _ v body => DeclassFree v ∧ DeclassFree body
  | .app f _ => f ≠ "declassify"
  | .seq a b => DeclassFree a ∧ DeclassFree b
  | .ifThenElse c t e => DeclassFree c ∧ DeclassFree t ∧ DeclassFree e
  | .cfBreak e => DeclassFree e
  | .whileFoldReturn c body => DeclassFree c ∧ DeclassFree body
  | .whileFold c body => DeclassFree c ∧ DeclassFree body
  | .forFoldReturn _ lo hi body => DeclassFree lo ∧ DeclassFree hi ∧ DeclassFree body
  | .forFold _ lo hi body => DeclassFree lo ∧ DeclassFree hi ∧ DeclassFree body
  | .forFoldRevReturn _ lo hi body => DeclassFree lo ∧ DeclassFree hi ∧ DeclassFree body
  | _ => True

/-- A continuation that declassifies no value leaves `contLeak` declassifying none. -/
theorem contLeak_decls {o : Outcome × Env} {k : Value → Env → SrcLeak}
    (hk : ∀ w e1, (k w e1).decls = []) : (contLeak o k).decls = [] := by
  unfold contLeak; split <;> simp_all [SrcLeak.decls]

/-- A continuation that declassifies no value leaves `tripCont` declassifying none. -/
theorem tripCont_decls {o : Outcome × Env} {k : Env → SrcLeak}
    (hk : ∀ e2, (k e2).decls = []) : (tripCont o k).decls = [] := by
  unfold tripCont; split <;> simp_all [SrcLeak.decls]

/-- A guard and a body leakage that declassify no value leave `whileLeak` declassifying
    none. -/
theorem whileLeak_decls {bi : Builtins} {c body : ImpExpr} {lc lb : Nat → Env → SrcLeak}
    (hc : ∀ n env, (lc n env).decls = []) (hb : ∀ n env, (lb n env).decls = []) :
    ∀ n env, (whileLeak bi c body lc lb n env).decls = []
  | 0, _ => rfl
  | n + 1, env => by
    have ih := whileLeak_decls (bi := bi) (c := c) (body := body) hc hb n
    simp only [whileLeak, SrcLeak.decls, hc, List.nil_append]
    split <;> simp only [SrcLeak.decls, hb, SrcEv.declOf, Option.toList, List.nil_append,
      tripCont_decls ih]

/-- A body leakage that declassifies no value leaves `forLeak` declassifying none. -/
theorem forLeak_decls {bi : Builtins} {i : String} {body : ImpExpr}
    {lb : Nat → Env → SrcLeak} (hb : ∀ n env, (lb n env).decls = []) :
    ∀ n lo hi env, (forLeak bi i body lb n lo hi env).decls = []
  | 0, _, _, _ => rfl
  | n + 1, lo, hi, env => by
    have ih := forLeak_decls (bi := bi) (i := i) (body := body) hb n (lo + 1) hi
    simp only [forLeak]
    split
    · rfl
    · simp only [SrcLeak.decls, hb, List.nil_append, tripCont_decls ih]

/-- A body leakage that declassifies no value leaves `forRevLeak` declassifying none. -/
theorem forRevLeak_decls {bi : Builtins} {i : String} {body : ImpExpr}
    {lb : Nat → Env → SrcLeak} (hb : ∀ n env, (lb n env).decls = []) :
    ∀ n lo hi env, (forRevLeak bi i body lb n lo hi env).decls = []
  | 0, _, _, _ => rfl
  | n + 1, lo, hi, env => by
    have ih := forRevLeak_decls (bi := bi) (i := i) (body := body) hb n lo (hi - 1)
    simp only [forRevLeak]
    split
    · rfl
    · simp only [SrcLeak.decls, hb, List.nil_append, tripCont_decls ih]

/-- Bound and trip leakages that declassify no value leave `boundsLeak` declassifying
    none. -/
theorem boundsLeak_decls {bi : Builtins} {lo hi : ImpExpr} {llo lhi : Env → SrcLeak}
    {fuel : Nat} {trips : Int → Int → Env → SrcLeak} (hlo : ∀ env, (llo env).decls = [])
    (hhi : ∀ env, (lhi env).decls = []) (ht : ∀ l h env, (trips l h env).decls = [])
    (env : Env) : (boundsLeak bi lo hi llo lhi fuel trips env).decls = [] := by
  unfold boundsLeak
  simp only [SrcLeak.decls, hlo, List.nil_append]
  split
  · rfl
  · simp only [SrcLeak.decls, hhi, List.nil_append]
    split
    · split
      · simp only [SrcLeak.decls, SrcEv.declOf, Option.toList, ht, List.nil_append]
      · rfl
    · rfl
  · rfl

/-- `srcLeak_decls_of_declassFree` for the expressions of size below `k`. -/
theorem srcLeak_decls_of_lt (M : LowCTLeakModel) (bi : Builtins) :
    ∀ (k : Nat) (e : ImpExpr), sizeOf e < k → DeclassFree e →
      ∀ fuel env, (srcLeak M bi e fuel env).decls = []
  | 0, _, hk, _, _, _ => absurd hk (Nat.not_lt_zero _)
  | k + 1, e, hk, h, fuel, env => by
    have ih := srcLeak_decls_of_lt M bi k
    fun_induction srcLeak M bi e fuel env
    case case4 a _ _ _ _ =>
      exact ih a (by simp at hk; omega) h _ _
    case case5 v body _ _ _ _ =>
      simp only [SrcLeak.decls, ih v (by simp at hk; omega) h.1, List.nil_append]
      exact contLeak_decls fun _ _ => ih body (by simp at hk; omega) h.2 _ _
    case case6 =>
      simp only [SrcLeak.decls, opLeak]
      split <;> rfl
    case case7 => exact absurd rfl h
    case case9 a b _ _ _ _ =>
      simp only [SrcLeak.decls, ih a (by simp at hk; omega) h.1, List.nil_append]
      exact contLeak_decls fun _ _ => ih b (by simp at hk; omega) h.2 _ _
    case case10 c t f _ _ _ _ _ =>
      simp only [SrcLeak.decls, ih c (by simp at hk; omega) h.1, List.nil_append]
      split
      · simp only [SrcLeak.decls, SrcEv.declOf, Option.toList, List.nil_append,
          ih t (by simp at hk; omega) h.2.1]
      · simp only [SrcLeak.decls, SrcEv.declOf, Option.toList, List.nil_append,
          ih f (by simp at hk; omega) h.2.2]
      · rfl
    case case11 a _ _ _ =>
      simp only [SrcLeak.decls, ih a (by simp at hk; omega) h, List.nil_append]
      exact contLeak_decls fun _ _ => rfl
    case case12 c body _ _ =>
      exact whileLeak_decls (ih c (by simp at hk; omega) h.1)
        (ih body (by simp at hk; omega) h.2) _ _
    case case13 c body _ _ =>
      exact whileLeak_decls (ih c (by simp at hk; omega) h.1)
        (ih body (by simp at hk; omega) h.2) _ _
    case case14 lo hi body _ _ =>
      exact boundsLeak_decls (ih lo (by simp at hk; omega) h.1 _)
        (ih hi (by simp at hk; omega) h.2.1 _)
        (fun _ _ => forLeak_decls (ih body (by simp at hk; omega) h.2.2) _ _ _) _
    case case15 lo hi body _ _ =>
      exact boundsLeak_decls (ih lo (by simp at hk; omega) h.1 _)
        (ih hi (by simp at hk; omega) h.2.1 _)
        (fun _ _ => forLeak_decls (ih body (by simp at hk; omega) h.2.2) _ _ _) _
    case case16 lo hi body _ _ =>
      exact boundsLeak_decls (ih lo (by simp at hk; omega) h.1 _)
        (ih hi (by simp at hk; omega) h.2.1 _)
        (fun _ _ => forRevLeak_decls (ih body (by simp at hk; omega) h.2.2) _ _ _) _
    all_goals rfl

/-- The source leakage of an expression calling `declassify` at no position it traverses
    declassifies no value. -/
theorem srcLeak_decls_of_declassFree (M : LowCTLeakModel) (bi : Builtins) (e : ImpExpr)
    (h : DeclassFree e) (fuel : Nat) (env : Env) : (srcLeak M bi e fuel env).decls = [] :=
  srcLeak_decls_of_lt M bi (sizeOf e + 1) e (Nat.lt_succ_self _) h fuel env

/-! ## Scalar expressions reading a set of slots -/

/-- `e` reads only scalar slots in `S` and no tower limb. -/
def sexprReadsOnly (S : String → Prop) : SExpr → Prop
  | .SVar x => S x
  | .SLit _ => True
  | .SLimb _ _ => False
  | .SAdd a b => sexprReadsOnly S a ∧ sexprReadsOnly S b
  | .SSub a b => sexprReadsOnly S a ∧ sexprReadsOnly S b
  | .SMul a b => sexprReadsOnly S a ∧ sexprReadsOnly S b
  | .SShr a b => sexprReadsOnly S a ∧ sexprReadsOnly S b
  | .SShl a b => sexprReadsOnly S a ∧ sexprReadsOnly S b
  | .SAnd a b => sexprReadsOnly S a ∧ sexprReadsOnly S b
  | .SXor a b => sexprReadsOnly S a ∧ sexprReadsOnly S b
  | .SLt a b => sexprReadsOnly S a ∧ sexprReadsOnly S b
  | .SAsr a b => sexprReadsOnly S a ∧ sexprReadsOnly S b
  | .SMulS a b => sexprReadsOnly S a ∧ sexprReadsOnly S b
  | .SMulHiU a b => sexprReadsOnly S a ∧ sexprReadsOnly S b
  | .SMulHiS a b => sexprReadsOnly S a ∧ sexprReadsOnly S b

/-- An expression reading only the slots `S` has the same value in two states that
    agree on `S`. -/
theorem evalState_congr {S : String → Prop} {rs rs' : RustState}
    (hS : ∀ x, S x → rs.rsScalar x = rs'.rsScalar x) :
    ∀ e : SExpr, sexprReadsOnly S e → e.evalState rs = e.evalState rs'
  | .SVar x, h => hS x h
  | .SLit _, _ => rfl
  | .SLimb _ _, h => h.elim
  | .SAdd a b, h => by
    simp only [SExpr.evalState, evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SSub a b, h => by
    simp only [SExpr.evalState, evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SMul a b, h => by
    simp only [SExpr.evalState, evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SShr a b, h => by
    simp only [SExpr.evalState, evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SShl a b, h => by
    simp only [SExpr.evalState, evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SAnd a b, h => by
    simp only [SExpr.evalState, evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SXor a b, h => by
    simp only [SExpr.evalState, evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SLt a b, h => by
    simp only [SExpr.evalState, evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SAsr a b, h => by
    simp only [SExpr.evalState, evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SMulS a b, h => by
    simp only [SExpr.evalState, evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SMulHiU a b, h => by
    simp only [SExpr.evalState, evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SMulHiS a b, h => by
    simp only [SExpr.evalState, evalState_congr hS a h.1, evalState_congr hS b h.2]

/-- The leakage of an expression reading only the slots `S` is the same in two states
    that agree on `S`. -/
theorem sexprLeak_congr (M : LowCTLeakModel) {S : String → Prop} {rs rs' : RustState}
    (hS : ∀ x, S x → rs.rsScalar x = rs'.rsScalar x) :
    ∀ e : SExpr, sexprReadsOnly S e → sexprLeak M rs e = sexprLeak M rs' e
  | .SVar _, _ => rfl
  | .SLit _, _ => rfl
  | .SLimb _ _, h => h.elim
  | .SAdd a b, h => by
    simp only [sexprLeak, nodeLeak, sexprLeak_congr M hS a h.1, sexprLeak_congr M hS b h.2,
      evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SSub a b, h => by
    simp only [sexprLeak, nodeLeak, sexprLeak_congr M hS a h.1, sexprLeak_congr M hS b h.2,
      evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SMul a b, h => by
    simp only [sexprLeak, nodeLeak, sexprLeak_congr M hS a h.1, sexprLeak_congr M hS b h.2,
      evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SShr a b, h => by
    simp only [sexprLeak, nodeLeak, sexprLeak_congr M hS a h.1, sexprLeak_congr M hS b h.2,
      evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SShl a b, h => by
    simp only [sexprLeak, nodeLeak, sexprLeak_congr M hS a h.1, sexprLeak_congr M hS b h.2,
      evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SAnd a b, h => by
    simp only [sexprLeak, nodeLeak, sexprLeak_congr M hS a h.1, sexprLeak_congr M hS b h.2,
      evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SXor a b, h => by
    simp only [sexprLeak, nodeLeak, sexprLeak_congr M hS a h.1, sexprLeak_congr M hS b h.2,
      evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SLt a b, h => by
    simp only [sexprLeak, nodeLeak, sexprLeak_congr M hS a h.1, sexprLeak_congr M hS b h.2,
      evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SAsr a b, h => by
    simp only [sexprLeak, nodeLeak, sexprLeak_congr M hS a h.1, sexprLeak_congr M hS b h.2,
      evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SMulS a b, h => by
    simp only [sexprLeak, nodeLeak, sexprLeak_congr M hS a h.1, sexprLeak_congr M hS b h.2,
      evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SMulHiU a b, h => by
    simp only [sexprLeak, nodeLeak, sexprLeak_congr M hS a h.1, sexprLeak_congr M hS b h.2,
      evalState_congr hS a h.1, evalState_congr hS b h.2]
  | .SMulHiS a b, h => by
    simp only [sexprLeak, nodeLeak, sexprLeak_congr M hS a h.1, sexprLeak_congr M hS b h.2,
      evalState_congr hS a h.1, evalState_congr hS b h.2]

/-- The `SExpr` of a scalar operation on the variables `a` and `b` reads only `a` and
    `b`. -/
theorem scalarOpExpr_readsOnly {op a b : String} {se : SExpr}
    (h : scalarOpExpr op (.SVar a) (.SVar b) = some se) :
    sexprReadsOnly (fun x => x = a ∨ x = b) se := by
  unfold scalarOpExpr at h
  split at h
  all_goals first
    | (cases h; done)
    | (cases h; simp [sexprReadsOnly])

/-! ## Determinism of the traced `LowCT` semantics -/

/-- Two traced runs of a program from one state have the same trace and final state. -/
theorem rustExecLeak_det {N : Nat} {leafSpec : LeafSpec} {M : LowCTLeakModel} {c : LowCT}
    {rs r₁ : RustState} {t₁ : List CTLeak} (h₁ : RustExecLeak N leafSpec M c rs t₁ r₁) :
    ∀ {t₂ : List CTLeak} {r₂ : RustState}, RustExecLeak N leafSpec M c rs t₂ r₂ →
      t₁ = t₂ ∧ r₁ = r₂ := by
  induction h₁ with
  | skip => intro _ _ h; cases h; exact ⟨rfl, rfl⟩
  | seq c1 c2 rs r1 rs' t1 t2 _ _ ih1 ih2 =>
    intro _ _ h
    cases h with
    | seq _ _ _ r1' _ t1' t2' h1 h2 =>
      obtain ⟨rfl, rfl⟩ := ih1 h1
      obtain ⟨rfl, rfl⟩ := ih2 h2
      exact ⟨rfl, rfl⟩
  | letZero x t body rs rs' tr _ ih =>
    intro _ _ h; cases h with | letZero _ _ _ _ _ _ h => exact ih h
  | letU64Zero x body rs rs' tr _ ih =>
    intro _ _ h; cases h with | letU64Zero _ _ _ _ _ h => exact ih h
  | scalarSet => intro _ _ h; cases h; exact ⟨rfl, rfl⟩
  | ifTrue e ct cf rs rs' v tr hv hv0 _ ih =>
    intro _ _ h
    cases h with
    | ifTrue _ _ _ _ _ _ _ _ _ h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩
    | ifFalse _ _ _ _ _ _ h0 _ => exact absurd (hv ▸ h0) hv0
  | ifFalse e ct cf rs rs' tr h0 _ ih =>
    intro _ _ h
    cases h with
    | ifTrue _ _ _ _ _ _ _ hv hv0 _ => exact absurd (hv ▸ h0) hv0
    | ifFalse _ _ _ _ _ _ _ h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩
  | whileFalse e body rs h0 =>
    intro _ _ h
    cases h with
    | whileFalse => exact ⟨rfl, rfl⟩
    | whileTrue _ _ _ _ _ _ _ _ hv hv0 _ _ => exact absurd (hv ▸ h0) hv0
  | whileTrue e body rs r1 rs' v t1 t2 hv hv0 _ _ ih1 ih2 =>
    intro _ _ h
    cases h with
    | whileFalse _ _ _ h0 => exact absurd (hv ▸ h0) hv0
    | whileTrue _ _ _ r1' _ _ t1' t2' _ _ h1 h2 =>
      obtain ⟨rfl, rfl⟩ := ih1 h1
      obtain ⟨rfl, rfl⟩ := ih2 h2
      exact ⟨rfl, rfl⟩
  | forZero => intro _ _ h; cases h; exact ⟨rfl, rfl⟩
  | forSucc x n body rs r1 rs' t1 t2 _ _ ih1 ih2 =>
    intro _ _ h
    cases h with
    | forSucc _ _ _ _ r1' _ t1' t2' h1 h2 =>
      obtain ⟨rfl, rfl⟩ := ih1 h1
      obtain ⟨rfl, rfl⟩ := ih2 h2
      exact ⟨rfl, rfl⟩
  | forRuntime x bound body rs rs' tr _ ih =>
    intro _ _ h
    cases h with
    | forRuntime _ _ _ _ _ _ h => obtain ⟨rfl, rfl⟩ := ih h; exact ⟨rfl, rfl⟩
  | call f dest args rs oldDestV argList h1 h2 _ =>
    intro _ _ h
    cases h with
    | call _ _ _ _ oldDestV' _ h1' h2' _ =>
      rw [h1] at h1'; cases h1'; subst h2 h2'; exact ⟨rfl, rfl⟩
  | cloneCall cloneVar cloneTy oldDest innerF dest args rs rsClone rs' tr h1 _ ih =>
    intro _ _ h
    cases h with
    | cloneCall _ _ _ _ _ _ _ _ _ _ h1' h => subst h1 h1'; exact ih h
  | callSwap f dest1 dest2 args rs rs1 rs' t1 t2 _ _ ih1 ih2 =>
    intro _ _ h
    cases h with
    | callSwap _ _ _ _ _ rs1' _ t1' t2' h1 h2 =>
      obtain ⟨rfl, rfl⟩ := ih1 h1
      obtain ⟨rfl, rfl⟩ := ih2 h2
      exact ⟨rfl, rfl⟩
  | limbStore loc idx v rs oldDestV h1 =>
    intro _ _ h
    cases h with
    | limbStore _ _ _ _ _ h1' => rw [h1] at h1'; cases h1'; exact ⟨rfl, rfl⟩
  | limbStoreExpr loc idx e rs oldDestV h1 =>
    intro _ _ h
    cases h with
    | limbStoreExpr _ _ _ _ _ h1' => rw [h1] at h1'; cases h1'; exact ⟨rfl, rfl⟩
  | callN f dests args rs argList h1 _ _ =>
    intro _ _ h
    cases h with
    | callN _ _ _ _ _ h1' _ _ => subst h1 h1'; exact ⟨rfl, rfl⟩
  | selectFalse dst sel src0 src1 rs hd srcV h0 h1 =>
    intro _ _ h
    cases h with
    | selectFalse _ _ _ _ _ _ _ _ h1' => rw [h1] at h1'; cases h1'; exact ⟨rfl, rfl⟩
    | selectTrue _ _ _ _ _ _ _ _ hv hv0 _ => exact absurd (hv ▸ h0) hv0
  | selectTrue dst sel src0 src1 rs hd v srcV hv hv0 h1 =>
    intro _ _ h
    cases h with
    | selectFalse _ _ _ _ _ _ _ h0 _ => exact absurd (hv ▸ h0) hv0
    | selectTrue _ _ _ _ _ _ _ _ _ _ h1' => rw [h1] at h1'; cases h1'; exact ⟨rfl, rfl⟩
  | assert => intro _ _ h; cases h; exact ⟨rfl, rfl⟩
  | block body rs rs' tr _ ih =>
    intro _ _ h; cases h with | block _ _ _ _ h => exact ih h
  | tupleLoad dst src idx rs oldV srcV h1 h2 =>
    intro _ _ h
    cases h with
    | tupleLoad _ _ _ _ _ _ h1' h2' =>
      rw [h1] at h1'; cases h1'; rw [h2] at h2'; cases h2'; exact ⟨rfl, rfl⟩
  | arrStore arr idxVar src rs idx oldV srcV hi h1 h2 =>
    intro _ _ h
    cases h with
    | arrStore _ _ _ _ _ _ _ hi' h1' h2' =>
      subst hi hi'; rw [h1] at h1'; cases h1'; rw [h2] at h2'; cases h2'; exact ⟨rfl, rfl⟩
  | arrLoad dst src idxVar rs idx oldV srcV hi h1 h2 =>
    intro _ _ h
    cases h with
    | arrLoad _ _ _ _ _ _ _ hi' h1' h2' =>
      subst hi hi'; rw [h1] at h1'; cases h1'; rw [h2] at h2'; cases h2'; exact ⟨rfl, rfl⟩
  | arrStoreLit arr idx src rs oldV srcV h1 h2 =>
    intro _ _ h
    cases h with
    | arrStoreLit _ _ _ _ _ _ h1' h2' =>
      rw [h1] at h1'; cases h1'; rw [h2] at h2'; cases h2'; exact ⟨rfl, rfl⟩
  | arrLoadLit dst src idx rs oldV srcV h1 h2 =>
    intro _ _ h
    cases h with
    | arrLoadLit _ _ _ _ _ _ h1' h2' =>
      rw [h1] at h1'; cases h1'; rw [h2] at h2'; cases h2'; exact ⟨rfl, rfl⟩
  | scalarSetExpr => intro _ _ h; cases h; exact ⟨rfl, rfl⟩
  | callDstThreaded f dst args rs oldDestV argList h1 h2 _ =>
    intro _ _ h
    cases h with
    | callDstThreaded _ _ _ _ _ _ h1' h2' _ =>
      rw [h1] at h1'; cases h1'; subst h2 h2'; exact ⟨rfl, rfl⟩
  | copy dst src rs hd srcV h1 =>
    intro _ _ h
    cases h with
    | copy _ _ _ _ _ h1' => rw [h1] at h1'; cases h1'; exact ⟨rfl, rfl⟩

/-- A traced run ends in the state of every untraced run from the same state. -/
theorem rustExecLeak_state_eq {N : Nat} {leafSpec : LeafSpec} {M : LowCTLeakModel}
    {c : LowCT} {rs r r' : RustState} {t : List CTLeak}
    (h : RustExecLeak N leafSpec M c rs t r) (h' : RustExec N leafSpec c rs r') : r = r' := by
  obtain ⟨_, h''⟩ := CatCrypt.Crypto.SecureCompilation.CT.RustExec.exists_leak M h'
  exact (rustExecLeak_det h h'').2

/-- Two runs of a program from one state end in the same state. -/
theorem rustExec_det {N : Nat} {leafSpec : LeafSpec} {c : LowCT} {rs r₁ r₂ : RustState}
    (h₁ : RustExec N leafSpec c rs r₁) (h₂ : RustExec N leafSpec c rs r₂) : r₁ = r₂ := by
  obtain ⟨_, h₁'⟩ :=
    CatCrypt.Crypto.SecureCompilation.CT.RustExec.exists_leak LowCTLeakModel.owned h₁
  exact rustExecLeak_state_eq h₁' h₂

end CatCrypt.Crypto.Hax
