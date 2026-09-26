/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTExit
public import CatCrypt.Crypto.Hax.HaxToLowCTSimulates
public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ProgramFor
public import HaxLean.SemanticsCF

/-!
# Simulation of the exit-flag lowering over `Hax.denote'`

`haxToLowCTK` (`HaxToLowCTExit.lean`) lowers a function body with early returns
by an exit flag, a result slot and scalar operations.  This module proves that
the lowered `LowCT` simulates hax-lean's control-flow evaluator `Hax.denote'` on
the scalar fragment `exitSimOk`:

* scalar `letBind`s of a `u64` or bool literal, and of a scalar operation on two
  variables (`scalarOpExpr`);
* `seq`, `ifThenElse` on a variable, `whileFoldReturn` on a variable,
  `forFoldReturn` and `forFoldRevReturn` with bounds accepted by `forBounds`,
  `cfBreak` of a variable or a `u64` literal inside such a loop or, in a function
  body, at function level;
* outside tail position a variable or `unitVal`, in tail position a variable, a
  `u64` literal or `unitVal`;
* no name of the program is reserved (`exitReserved`, the prefix `"__exit_"`).

**Agreement.**  `envAgreesOff env rs` states that every binding of a
non-reserved name holds a scalar value (`ScalarVal`: a `u64` word below `2^64`,
a bool, or an integer in `[0, 2^64)`, the value a loop counter takes) whose
decoding is the `LowCT` scalar slot.  `envAgreesExit tl o env rs`
adds the exit component: an outcome `val (controlFlow true v)` has the exit flag
`1` and the returned word in `exitValName`; a value outcome that is not
control-flow-tagged has the flag `0`, and in tail position its decoding in the
result slot.  Every other outcome has no agreement.

**Scalar operations.**  `ScalarOpsSound bi` states that the builtin table
computes each operation of `scalarOpExpr` as `scalarOpNat` on scalar values.
hax-lean's `add`/`sub` wrap modulo `2^64` while LowCT's `SAdd`/`SSub` do not; the
table `noOverflow64 bi` refuses an `add` with `a + b ≥ 2^64` and a `sub` with
`b > a`, which is the no-overflow condition `inRangeState` imposes on the step
from `RustExec` to the emitted code.  A run of `denote'` over that table that
ends in a value performed no overflowing operation.
`scalarOpsSound_noOverflow64_width` discharges `ScalarOpsSound` for hax-lean's
width-aware comparison and arithmetic tables under that refusal.

**Loops.**  `exitLoop_sim` is the `whileFoldReturn` case, by induction on fuel
over the four outcomes of `denoteWhile'Return` at a `true` guard (exit, loop
break, continue or normal value) and the `false` guard.  The loop-break form
`controlFlow true (controlFlow false v)` does not arise, since a returned word
is a scalar value.  `exitForTrips_sim` and `exitForTripsRev_sim` are the
`forFoldReturn` and `forFoldRevReturn` cases, by induction on the trips left:
the lowered `RFor` runs `hi - lo` guarded trips, each binding the counter from
the trip counter of `RFor`, so a trip after an exit writes only the loop slot
(`exitedTrips`); the run of `RFor` is assembled from the trips by
`rustExec_rFor_of_tripsFrom`.

`haxToLowCTK_simulates` is the simulation of every fragment expression, in every
exit context `RunCtx` admits: a loop slot or the function context `exitFnSlot`.
`haxToLowCTFn_simulates_exit` is the function-level statement for a body in the
fragment with exits allowed at function level (`exitSimOk true true`): the
result slot holds the decoding of the returned or final value.

## Main results

* `haxToLowCTK_simulates`: the lowering of every `exitSimOk` expression simulates
  `Hax.denote'` under `ScalarOpsSound`
* `haxToLowCTFn_simulates_exit`, `haxToLowCTFn_simulates`: the result slot of the
  lowered function holds the decoding of the returned or final value, with and
  without exits at function level
* `exitLoop_sim`: the `whileFoldReturn` case, by induction on fuel
* `exitForTrips_sim`, `exitForTripsRev_sim`: the `forFoldReturn` and
  `forFoldRevReturn` cases, by induction on the trips left
* `scalarOpsSound_noOverflow64_width`: hax-lean's width-aware tables satisfy
  `ScalarOpsSound` under the no-overflow refusal
* `searchLoopShape_exitSimOk`: the search loop lies in the fragment
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit IntWidth Value Env Outcome Builtins denote')
open CatCrypt.Crypto.Jasmin.LowCT
  (LowCT SExpr RustState RustExec LeafSpec rsSetScalar)

/-! ## §1  Reserved names -/

/-- A name is reserved when it starts with `"__exit_"`. -/
def exitReserved (name : String) : Bool := "__exit_".toList.isPrefixOf name.toList

/-- A loop slot: a name starting with `"__exit_run"`. -/
def exitRunSlot (name : String) : Bool := "__exit_run".toList.isPrefixOf name.toList

/-- The exit context `fl` of the translator names a loop slot or the function
    context `exitFnSlot`. -/
def RunCtx (fl : Option String) : Prop :=
  ∀ r, fl = some r → exitRunSlot r = true ∨ r = exitFnSlot

/-! ## §2  Scalar values, agreement and the exit component -/

/-- A scalar value: a `u64` word below `2^64`, a bool, or an integer in
    `[0, 2^64)` (the counter of a `forFoldReturn`). -/
def ScalarVal : Value → Prop
  | .uint .w64 n => n < 2 ^ 64
  | .bool _ => True
  | .int n => 0 ≤ n ∧ n < 2 ^ 64
  | _ => False

/-- Agreement off the reserved names: every binding of a non-reserved name is a
    scalar value whose decoding is the `LowCT` scalar slot. -/
def envAgreesOff (env : Env) (rs : RustState) : Prop :=
  ∀ name v, exitReserved name = false → env name = some v →
    ScalarVal v ∧ valueToScalar v = some (rs.rsScalar name)

/-- Agreement with the exit component, for an expression in tail position `tl`. -/
def envAgreesExit (tl : Bool) : Outcome → Env → RustState → Prop
  | .val (.controlFlow true v), env, rs =>
      rs.rsScalar exitRetName = 1 ∧ valueToScalar v = some (rs.rsScalar exitValName) ∧
        envAgreesOff env rs
  | .val (.controlFlow false _), _, _ => False
  | .val v, env, rs =>
      rs.rsScalar exitRetName = 0 ∧ envAgreesOff env rs ∧
        (tl = true → valueToScalar v = some (rs.rsScalar exitResName))
  | _, _, _ => False

/-! ## §3  Scalar operations -/

theorem valueToScalar_bool (b : Bool) :
    valueToScalar (.bool b) = some (if b then 1 else 0) := by
  cases b <;> rfl

theorem valueToScalar_uint (w : IntWidth) (n : Nat) : valueToScalar (.uint w n) = some n := rfl

theorem valueToScalar_int (n : Nat) : valueToScalar (.int n) = some n := by
  simp [valueToScalar]

/-- hax-lean's unsigned operation `op` on scalars, as `LowCT` computes it. -/
def scalarOpNat (op : String) (a b : Nat) : Nat :=
  match op with
  | "lt"  => if a < b then 1 else 0
  | "gt"  => if b < a then 1 else 0
  | "le"  => 1 - (if b < a then 1 else 0)
  | "ge"  => 1 - (if a < b then 1 else 0)
  | "eq"  => 1 - (if a < b then 1 else 0) - (if b < a then 1 else 0)
  | "ne"  => (if a < b then 1 else 0) + (if b < a then 1 else 0)
  | "add" => a + b
  | "sub" => a - b
  | _     => 0

/-- The `SExpr` of a scalar operation evaluates to `scalarOpNat`. -/
theorem scalarOpExpr_eval (op x y : String) (se : SExpr) (σ : String → Nat)
    (h : scalarOpExpr op (.SVar x) (.SVar y) = some se) :
    se.eval σ = scalarOpNat op (σ x) (σ y) := by
  unfold scalarOpExpr at h
  split at h <;> (try cases h) <;> simp only [SExpr.eval, scalarOpNat]
  all_goals rfl

/-- The `SExpr` of a scalar operation on two variables reads no tower limb: the
    tower-aware evaluator gives it the value of `SExpr.eval`. -/
theorem scalarOpExpr_evalState (op x y : String) (se : SExpr) (rs : RustState)
    (h : scalarOpExpr op (.SVar x) (.SVar y) = some se) :
    se.evalState rs = se.eval rs.rsScalar := by
  unfold scalarOpExpr at h
  split at h <;> (try cases h) <;> rfl

/-- The builtin table computes every operation of `scalarOpExpr` on scalar
    values as a scalar value decoding to `scalarOpNat`. -/
def ScalarOpsSound (bi : Builtins) : Prop :=
  ∀ op va vb r na nb,
    (scalarOpExpr op (.SVar "a") (.SVar "b")).isSome = true →
    ScalarVal va → ScalarVal vb →
    valueToScalar va = some na → valueToScalar vb = some nb →
    bi op [va, vb] = some r →
    ScalarVal r ∧ valueToScalar r = some (scalarOpNat op na nb)

/-- The table `bi` with the overflowing `u64` operations refused: `add` of words
    with `a + b ≥ 2^64` and `sub` of words with `b > a`.  This is the no-overflow
    condition `inRangeState`. -/
def noOverflow64 (bi : Builtins) : Builtins := fun f args =>
  match f, args with
  | "add", [.uint _ a, .uint _ b] => if a + b < 2 ^ 64 then bi f args else none
  | "sub", [.uint _ a, .uint _ b] => if b ≤ a then bi f args else none
  | _, _ => bi f args

/-- hax-lean's width-aware unsigned comparison table before its arithmetic
    table. -/
def widthScalarOps : Builtins := fun f args =>
  _root_.Hax.widthCmpOps f args <|> _root_.Hax.widthArithOps f args

/-- On scalar values, hax-lean's width tables with overflow refused compute the
    scalar operations exactly. -/
theorem scalarOpsSound_noOverflow64_width : ScalarOpsSound (noOverflow64 widthScalarOps) := by
  intro op va vb r na nb hop hva hvb hna hnb hbi
  have hv : ∀ v : Value, ScalarVal v →
      (∃ n, v = .uint .w64 n ∧ n < 2 ^ 64) ∨ (∃ b, v = .bool b) ∨ ∃ n : Int, v = .int n := by
    intro v hv
    match v, hv with
    | .uint .w64 n, h => exact Or.inl ⟨n, rfl, h⟩
    | .bool b, _ => exact Or.inr (Or.inl ⟨b, rfl⟩)
    | .int n, _ => exact Or.inr (Or.inr ⟨n, rfl⟩)
  unfold scalarOpExpr at hop
  rcases hv va hva with ⟨a, rfl, ha⟩ | ⟨ba, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases hv vb hvb with ⟨b, rfl, hb⟩ | ⟨bb, rfl⟩ | ⟨b, rfl⟩
  · simp only [valueToScalar, Option.some.injEq] at hna hnb
    subst hna hnb
    split at hop
    all_goals simp [noOverflow64, widthScalarOps, Hax.widthCmpOps, Hax.widthArithOps,
      Hax.wrapUint, Hax.IntWidth.modulus, Hax.IntWidth.bits] at hbi hop
    all_goals obtain ⟨_, rfl⟩ := hbi
    all_goals simp only [ScalarVal, scalarOpNat, valueToScalar_bool, valueToScalar_uint,
      true_and, Option.some.injEq]
    all_goals first
      | (constructor <;> omega)
      | (split_ifs <;> simp_all <;> omega)
  all_goals simp [noOverflow64, widthScalarOps, Hax.widthCmpOps, Hax.widthArithOps] at hbi

/-! ## §4  One step of `denote'` on the fragment's constructors -/

section SourceSteps

variable (bi : Builtins) (fuel : Nat)

theorem denote'_var_run (x : String) (env : Env) :
    (denote' bi fuel (.var x)).run env =
      match env x with
      | some v => (.val v, env)
      | none => (.err s!"undefined variable: {x}", env) := by
  simp only [denote']
  cases h : env x <;>
    simp only [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, h]

theorem denote'_lit_run (l : ImpLit) (env : Env) :
    (denote' bi fuel (.lit l)).run env = (.val (Value.ofLit l), env) := by
  simp only [denote']; rfl

theorem denote'_unitVal_run (env : Env) :
    (denote' bi fuel .unitVal).run env = (.val .unit, env) := by
  simp only [denote']; rfl

theorem denote'_letBind_run (n : String) (val body : ImpExpr) (env : Env) :
    (denote' bi fuel (.letBind n val body)).run env =
      match (denote' bi fuel val).run env with
      | (.val (.controlFlow b v), e1) => (.val (.controlFlow b v), e1)
      | (.val v, e1) => (denote' bi fuel body).run (e1.extend n v)
      | (o, e1) => (o, e1) := by
  simp only [denote', StateT.run, bind, StateT.bind, pure, modify, modifyGet,
    MonadStateOf.modifyGet]
  rcases (denote' bi fuel val) env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> rfl

theorem denote'_seq_run (a b : ImpExpr) (env : Env) :
    (denote' bi fuel (.seq a b)).run env =
      match (denote' bi fuel a).run env with
      | (.val (.controlFlow k v), e1) => (.val (.controlFlow k v), e1)
      | (.val _, e1) => (denote' bi fuel b).run e1
      | (o, e1) => (o, e1) := by
  simp only [denote', StateT.run, bind, StateT.bind, pure]
  rcases (denote' bi fuel a) env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> rfl

theorem denote'_ifThenElse_run (c t e : ImpExpr) (env : Env) :
    (denote' bi fuel (.ifThenElse c t e)).run env =
      match (denote' bi fuel c).run env with
      | (.val (.controlFlow k v), e1) => (.val (.controlFlow k v), e1)
      | (.val (.bool true), e1) => (denote' bi fuel t).run e1
      | (.val (.bool false), e1) => (denote' bi fuel e).run e1
      | (.val _, e1) => (.err "if condition not a bool", e1)
      | (o, e1) => (o, e1) := by
  simp only [denote', StateT.run, bind, StateT.bind, pure]
  rcases (denote' bi fuel c) env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v with
  | bool b => cases b <;> rfl
  | _ => rfl

theorem denote'_cfBreak_run' (e : ImpExpr) (env : Env) :
    (denote' bi fuel (.cfBreak e)).run env =
      match (denote' bi fuel e).run env with
      | (.val (.controlFlow k v), e1) => (.val (.controlFlow k v), e1)
      | (.val v, e1) => (.val (.controlFlow true v), e1)
      | (o, e1) => (o, e1) := by
  simp only [denote', StateT.run, bind, StateT.bind, pure]
  rcases (denote' bi fuel e) env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> rfl

theorem denote'_app_run (f : String) (args : List ImpExpr) (env : Env) :
    (denote' bi fuel (.app f args)).run env =
      match (_root_.Hax.denoteArgs' bi fuel args).run env with
      | (some vals, e1) =>
          match bi f vals with
          | some v => (.val v, e1)
          | none => (.err s!"unknown function or bad args: {f}", e1)
      | (none, e1) => (.err "non-value in function arguments", e1) := by
  simp only [denote', _root_.Hax.denoteApp', StateT.run, bind, StateT.bind, pure]
  rcases (_root_.Hax.denoteArgs' bi fuel args) env with ⟨o, e1⟩
  rcases o with _ | vals
  · rfl
  · cases h : bi f vals <;> simp only [h] <;> rfl

theorem denoteArgs'_nil_run (env : Env) :
    (_root_.Hax.denoteArgs' bi fuel []).run env = (some [], env) := by
  simp only [_root_.Hax.denoteArgs']; rfl

theorem denoteArgs'_cons_run (e : ImpExpr) (es : List ImpExpr) (env : Env) :
    (_root_.Hax.denoteArgs' bi fuel (e :: es)).run env =
      match (denote' bi fuel e).run env with
      | (.val (.controlFlow _ _), e1) => (none, e1)
      | (.val v, e1) =>
          (((_root_.Hax.denoteArgs' bi fuel es).run e1).1.map (v :: ·),
            ((_root_.Hax.denoteArgs' bi fuel es).run e1).2)
      | (_, e1) => (none, e1) := by
  simp only [_root_.Hax.denoteArgs', StateT.run, bind, StateT.bind, pure]
  rcases (denote' bi fuel e) env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v <;> rfl

theorem denote'_whileFoldReturn_run (c body : ImpExpr) (env : Env) :
    (denote' bi fuel (.whileFoldReturn c body)).run env =
      (_root_.Hax.denoteWhile'Return bi fuel c body).run env := by
  simp only [denote']

theorem denoteWhile'Return_zero_run (c body : ImpExpr) (env : Env) :
    (_root_.Hax.denoteWhile'Return bi 0 c body).run env = (.err "out of fuel", env) := by
  rw [_root_.Hax.denoteWhile'Return]; rfl

theorem denoteWhile'Return_succ_run (n : Nat) (c body : ImpExpr) (env : Env) :
    (_root_.Hax.denoteWhile'Return bi (n + 1) c body).run env =
      match (denote' bi (n + 1) c).run env with
      | (.val (.controlFlow k v), e1) => (.val (.controlFlow k v), e1)
      | (.val (.bool true), e1) =>
          match (denote' bi (n + 1) body).run e1 with
          | (.val (.controlFlow true (.controlFlow false v)), e2) => (.val v, e2)
          | (.val (.controlFlow true v), e2) => (.val (.controlFlow true v), e2)
          | (.val (.controlFlow false _), e2) =>
              (_root_.Hax.denoteWhile'Return bi n c body).run e2
          | (.val _, e2) => (_root_.Hax.denoteWhile'Return bi n c body).run e2
          | (o, e2) => (o, e2)
      | (.val (.bool false), e1) => (.val .unit, e1)
      | (.val _, e1) => (.err "while condition not a bool", e1)
      | (o, e1) => (o, e1) := by
  rw [_root_.Hax.denoteWhile'Return]
  simp only [Nat.add_one_ne_zero, if_false, StateT.run, bind, StateT.bind, pure, Nat.add_sub_cancel]
  rcases (denote' bi (n + 1) c) env with ⟨o, e1⟩
  rcases o with v | _ | _ | _ | _ <;> try rfl
  cases v with
  | bool b =>
    cases b
    · rfl
    · simp only [StateT.bind]
      rcases (denote' bi (n + 1) body) e1 with ⟨o2, e2⟩
      rcases o2 with v2 | _ | _ | _ | _ <;> try rfl
      cases v2 with
      | controlFlow k w =>
        cases k
        · rfl
        · cases w with
          | controlFlow k2 w2 => cases k2 <;> rfl
          | _ => rfl
      | _ => rfl
  | _ => rfl

theorem denote'_letBind_run_val (n : String) (val body : ImpExpr) (env e1 : Env) (v : Value)
    (h : (denote' bi fuel val).run env = (.val v, e1)) (hv : v.isControlFlow = false) :
    (denote' bi fuel (.letBind n val body)).run env = (denote' bi fuel body).run (e1.extend n v) := by
  rw [denote'_letBind_run, h]; cases v <;> first | rfl | simp at hv

theorem denote'_letBind_run_nonval (n : String) (val body : ImpExpr) (env e1 : Env) (o : Outcome)
    (h : (denote' bi fuel val).run env = (o, e1)) (ho : ∀ v, o ≠ .val v) :
    (denote' bi fuel (.letBind n val body)).run env = (o, e1) := by
  rw [denote'_letBind_run, h]
  cases o with
  | val v => exact absurd rfl (ho v)
  | _ => rfl

theorem denote'_seq_run_val (a b : ImpExpr) (env e1 : Env) (v : Value)
    (h : (denote' bi fuel a).run env = (.val v, e1)) (hv : v.isControlFlow = false) :
    (denote' bi fuel (.seq a b)).run env = (denote' bi fuel b).run e1 := by
  rw [denote'_seq_run, h]; cases v <;> first | rfl | simp at hv

theorem denote'_seq_run_cf (a b : ImpExpr) (env e1 : Env) (k : Bool) (w : Value)
    (h : (denote' bi fuel a).run env = (.val (.controlFlow k w), e1)) :
    (denote' bi fuel (.seq a b)).run env = (.val (.controlFlow k w), e1) := by
  rw [denote'_seq_run, h]

theorem denote'_seq_run_nonval (a b : ImpExpr) (env e1 : Env) (o : Outcome)
    (h : (denote' bi fuel a).run env = (o, e1)) (ho : ∀ v, o ≠ .val v) :
    (denote' bi fuel (.seq a b)).run env = (o, e1) := by
  rw [denote'_seq_run, h]
  cases o with
  | val v => exact absurd rfl (ho v)
  | _ => rfl

theorem denote'_ifThenElse_var_run_bool (c : String) (t e : ImpExpr) (env : Env) (b : Bool)
    (h : env c = some (.bool b)) :
    (denote' bi fuel (.ifThenElse (.var c) t e)).run env =
      (denote' bi fuel (if b then t else e)).run env := by
  rw [denote'_ifThenElse_run, denote'_var_run, h]; cases b <;> rfl

theorem denote'_ifThenElse_var_run_uint (c : String) (t e : ImpExpr) (env : Env) (w : IntWidth)
    (k : Nat) (h : env c = some (.uint w k)) :
    (denote' bi fuel (.ifThenElse (.var c) t e)).run env = (.err "if condition not a bool", env) := by
  rw [denote'_ifThenElse_run, denote'_var_run, h]

theorem denote'_ifThenElse_var_run_int (c : String) (t e : ImpExpr) (env : Env)
    (k : Int) (h : env c = some (.int k)) :
    (denote' bi fuel (.ifThenElse (.var c) t e)).run env = (.err "if condition not a bool", env) := by
  rw [denote'_ifThenElse_run, denote'_var_run, h]

theorem denote'_ifThenElse_var_run_none (c : String) (t e : ImpExpr) (env : Env)
    (h : env c = none) :
    (denote' bi fuel (.ifThenElse (.var c) t e)).run env = (.err s!"undefined variable: {c}", env) := by
  rw [denote'_ifThenElse_run, denote'_var_run, h]

theorem denote'_app2_run (f a b : String) (env : Env) (va vb : Value)
    (ha : env a = some va) (hb : env b = some vb)
    (hva : va.isControlFlow = false) (hvb : vb.isControlFlow = false) :
    (denote' bi fuel (.app f [.var a, .var b])).run env =
      match bi f [va, vb] with
      | some r => (.val r, env)
      | none => (.err s!"unknown function or bad args: {f}", env) := by
  have hargs : (_root_.Hax.denoteArgs' bi fuel [.var a, .var b]).run env = (some [va, vb], env) := by
    rw [denoteArgs'_cons_run, denote'_var_run, ha]
    cases va <;> (try simp at hva) <;>
      (simp only
       rw [denoteArgs'_cons_run, denote'_var_run, hb]
       cases vb <;> (try simp at hvb) <;> (simp only [denoteArgs'_nil_run]; rfl))
  rw [denote'_app_run, hargs]

theorem denote'_app2_run_none_left (f a b : String) (env : Env) (ha : env a = none) :
    ∃ msg, (denote' bi fuel (.app f [.var a, .var b])).run env = (.err msg, env) := by
  rw [denote'_app_run, denoteArgs'_cons_run, denote'_var_run, ha]
  exact ⟨_, rfl⟩

theorem denote'_app2_run_none_right (f a b : String) (env : Env) (va : Value)
    (ha : env a = some va) (hva : va.isControlFlow = false) (hb : env b = none) :
    ∃ msg, (denote' bi fuel (.app f [.var a, .var b])).run env = (.err msg, env) := by
  rw [denote'_app_run, denoteArgs'_cons_run, denote'_var_run, ha]
  cases va <;> (try simp at hva) <;>
    (simp only
     rw [denoteArgs'_cons_run, denote'_var_run, hb]
     exact ⟨_, rfl⟩)

theorem denoteWhile'Return_succ_false (n : Nat) (c : String) (body : ImpExpr) (env : Env)
    (h : env c = some (.bool false)) :
    (_root_.Hax.denoteWhile'Return bi (n + 1) (.var c) body).run env = (.val .unit, env) := by
  rw [denoteWhile'Return_succ_run, denote'_var_run, h]

theorem denoteWhile'Return_succ_uint (n : Nat) (c : String) (body : ImpExpr) (env : Env)
    (w : IntWidth) (k : Nat) (h : env c = some (.uint w k)) :
    (_root_.Hax.denoteWhile'Return bi (n + 1) (.var c) body).run env =
      (.err "while condition not a bool", env) := by
  rw [denoteWhile'Return_succ_run, denote'_var_run, h]

theorem denoteWhile'Return_succ_int (n : Nat) (c : String) (body : ImpExpr) (env : Env)
    (k : Int) (h : env c = some (.int k)) :
    (_root_.Hax.denoteWhile'Return bi (n + 1) (.var c) body).run env =
      (.err "while condition not a bool", env) := by
  rw [denoteWhile'Return_succ_run, denote'_var_run, h]

theorem denoteWhile'Return_succ_none (n : Nat) (c : String) (body : ImpExpr) (env : Env)
    (h : env c = none) :
    ∃ msg, (_root_.Hax.denoteWhile'Return bi (n + 1) (.var c) body).run env = (.err msg, env) := by
  rw [denoteWhile'Return_succ_run, denote'_var_run, h]
  exact ⟨_, rfl⟩

theorem denoteWhile'Return_succ_exit (n : Nat) (c : String) (body : ImpExpr) (env e2 : Env)
    (w : Value) (h : env c = some (.bool true))
    (hb : (denote' bi (n + 1) body).run env = (.val (.controlFlow true w), e2))
    (hw : w.isControlFlow = false) :
    (_root_.Hax.denoteWhile'Return bi (n + 1) (.var c) body).run env =
      (.val (.controlFlow true w), e2) := by
  rw [denoteWhile'Return_succ_run, denote'_var_run, h]
  simp only
  rw [hb]
  cases w <;> first | rfl | simp at hw

theorem denoteWhile'Return_succ_iterate (n : Nat) (c : String) (body : ImpExpr) (env e2 : Env)
    (w : Value) (h : env c = some (.bool true))
    (hb : (denote' bi (n + 1) body).run env = (.val w, e2)) (hw : w.isControlFlow = false) :
    (_root_.Hax.denoteWhile'Return bi (n + 1) (.var c) body).run env =
      (_root_.Hax.denoteWhile'Return bi n (.var c) body).run e2 := by
  rw [denoteWhile'Return_succ_run, denote'_var_run, h]
  simp only
  rw [hb]
  cases w <;> first | rfl | simp at hw

theorem denoteWhile'Return_succ_nonval (n : Nat) (c : String) (body : ImpExpr) (env e2 : Env)
    (o : Outcome) (h : env c = some (.bool true))
    (hb : (denote' bi (n + 1) body).run env = (o, e2)) (ho : ∀ v, o ≠ .val v) :
    (_root_.Hax.denoteWhile'Return bi (n + 1) (.var c) body).run env = (o, e2) := by
  rw [denoteWhile'Return_succ_run, denote'_var_run, h]
  simp only
  rw [hb]
  cases o with
  | val v => exact absurd rfl (ho v)
  | _ => rfl

theorem denote'_forFoldReturn_lit_run (i : String) (lo hi : Int) (body : ImpExpr) (env : Env) :
    (denote' bi fuel (.forFoldReturn i (.lit (.int lo)) (.lit (.int hi)) body)).run env =
      (_root_.Hax.denoteForLoop'Return bi fuel i lo hi body).run env := by
  simp only [denote']; rfl

theorem denoteForLoop'Return_ge_run (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : hi ≤ lo) :
    (_root_.Hax.denoteForLoop'Return bi fuel i lo hi body).run env = (.val .unit, env) := by
  rw [_root_.Hax.denoteForLoop'Return, if_pos h]; rfl

theorem denoteForLoop'Return_zero_run (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : lo < hi) :
    (_root_.Hax.denoteForLoop'Return bi 0 i lo hi body).run env = (.err "out of fuel", env) := by
  rw [_root_.Hax.denoteForLoop'Return, if_neg (not_le.mpr h), if_pos rfl]; rfl

theorem denoteForLoop'Return_succ_run (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr)
    (env : Env) (h : lo < hi) :
    (_root_.Hax.denoteForLoop'Return bi (n + 1) i lo hi body).run env =
      match (denote' bi (n + 1) body).run (env.extend i (.int lo)) with
      | (.val (.controlFlow true (.controlFlow false v)), e2) => (.val v, e2)
      | (.val (.controlFlow true v), e2) => (.val (.controlFlow true v), e2)
      | (.val (.controlFlow false _), e2) =>
          (_root_.Hax.denoteForLoop'Return bi n i (lo + 1) hi body).run e2
      | (.val _, e2) => (_root_.Hax.denoteForLoop'Return bi n i (lo + 1) hi body).run e2
      | (o, e2) => (o, e2) := by
  rw [_root_.Hax.denoteForLoop'Return, if_neg (not_le.mpr h)]
  simp only [Nat.add_one_ne_zero, if_false, StateT.run, bind, StateT.bind, pure, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Nat.add_sub_cancel]
  rcases (denote' bi (n + 1) body) (env.extend i (.int lo)) with ⟨o2, e2⟩
  rcases o2 with v2 | _ | _ | _ | _ <;> try rfl
  cases v2 with
  | controlFlow k w =>
    cases k
    · rfl
    · cases w with
      | controlFlow k2 w2 => cases k2 <;> rfl
      | _ => rfl
  | _ => rfl

theorem denoteForLoop'Return_succ_exit (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr)
    (env e2 : Env) (w : Value) (h : lo < hi)
    (hb : (denote' bi (n + 1) body).run (env.extend i (.int lo)) = (.val (.controlFlow true w), e2))
    (hw : w.isControlFlow = false) :
    (_root_.Hax.denoteForLoop'Return bi (n + 1) i lo hi body).run env =
      (.val (.controlFlow true w), e2) := by
  rw [denoteForLoop'Return_succ_run bi n i lo hi body env h, hb]
  cases w <;> first | rfl | simp at hw

theorem denoteForLoop'Return_succ_iterate (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr)
    (env e2 : Env) (w : Value) (h : lo < hi)
    (hb : (denote' bi (n + 1) body).run (env.extend i (.int lo)) = (.val w, e2))
    (hw : w.isControlFlow = false) :
    (_root_.Hax.denoteForLoop'Return bi (n + 1) i lo hi body).run env =
      (_root_.Hax.denoteForLoop'Return bi n i (lo + 1) hi body).run e2 := by
  rw [denoteForLoop'Return_succ_run bi n i lo hi body env h, hb]
  cases w <;> first | rfl | simp at hw

theorem denoteForLoop'Return_succ_nonval (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr)
    (env e2 : Env) (o : Outcome) (h : lo < hi)
    (hb : (denote' bi (n + 1) body).run (env.extend i (.int lo)) = (o, e2))
    (ho : ∀ v, o ≠ .val v) :
    (_root_.Hax.denoteForLoop'Return bi (n + 1) i lo hi body).run env = (o, e2) := by
  rw [denoteForLoop'Return_succ_run bi n i lo hi body env h, hb]
  cases o with
  | val v => exact absurd rfl (ho v)
  | _ => rfl

theorem denote'_forFoldRevReturn_lit_run (i : String) (lo hi : Int) (body : ImpExpr) (env : Env) :
    (denote' bi fuel (.forFoldRevReturn i (.lit (.int lo)) (.lit (.int hi)) body)).run env =
      (_root_.Hax.denoteForLoopRev'Return bi fuel i lo hi body).run env := by
  simp only [denote']; rfl

theorem denoteForLoopRev'Return_ge_run (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : hi ≤ lo) :
    (_root_.Hax.denoteForLoopRev'Return bi fuel i lo hi body).run env = (.val .unit, env) := by
  rw [_root_.Hax.denoteForLoopRev'Return, if_pos h]; rfl

theorem denoteForLoopRev'Return_zero_run (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : lo < hi) :
    (_root_.Hax.denoteForLoopRev'Return bi 0 i lo hi body).run env = (.err "out of fuel", env) := by
  rw [_root_.Hax.denoteForLoopRev'Return, if_neg (not_le.mpr h), if_pos rfl]; rfl

theorem denoteForLoopRev'Return_succ_run (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr)
    (env : Env) (h : lo < hi) :
    (_root_.Hax.denoteForLoopRev'Return bi (n + 1) i lo hi body).run env =
      match (denote' bi (n + 1) body).run (env.extend i (.int (hi - 1))) with
      | (.val (.controlFlow true (.controlFlow false v)), e2) => (.val v, e2)
      | (.val (.controlFlow true v), e2) => (.val (.controlFlow true v), e2)
      | (.val (.controlFlow false _), e2) =>
          (_root_.Hax.denoteForLoopRev'Return bi n i lo (hi - 1) body).run e2
      | (.val _, e2) => (_root_.Hax.denoteForLoopRev'Return bi n i lo (hi - 1) body).run e2
      | (o, e2) => (o, e2) := by
  rw [_root_.Hax.denoteForLoopRev'Return, if_neg (not_le.mpr h)]
  simp only [Nat.add_one_ne_zero, if_false, StateT.run, bind, StateT.bind, pure, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Nat.add_sub_cancel]
  rcases (denote' bi (n + 1) body) (env.extend i (.int (hi - 1))) with ⟨o2, e2⟩
  rcases o2 with v2 | _ | _ | _ | _ <;> try rfl
  cases v2 with
  | controlFlow k w =>
    cases k
    · rfl
    · cases w with
      | controlFlow k2 w2 => cases k2 <;> rfl
      | _ => rfl
  | _ => rfl

theorem denoteForLoopRev'Return_succ_exit (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr)
    (env e2 : Env) (w : Value) (h : lo < hi)
    (hb : (denote' bi (n + 1) body).run (env.extend i (.int (hi - 1))) =
      (.val (.controlFlow true w), e2))
    (hw : w.isControlFlow = false) :
    (_root_.Hax.denoteForLoopRev'Return bi (n + 1) i lo hi body).run env =
      (.val (.controlFlow true w), e2) := by
  rw [denoteForLoopRev'Return_succ_run bi n i lo hi body env h, hb]
  cases w <;> first | rfl | simp at hw

theorem denoteForLoopRev'Return_succ_iterate (n : Nat) (i : String) (lo hi : Int)
    (body : ImpExpr) (env e2 : Env) (w : Value) (h : lo < hi)
    (hb : (denote' bi (n + 1) body).run (env.extend i (.int (hi - 1))) = (.val w, e2))
    (hw : w.isControlFlow = false) :
    (_root_.Hax.denoteForLoopRev'Return bi (n + 1) i lo hi body).run env =
      (_root_.Hax.denoteForLoopRev'Return bi n i lo (hi - 1) body).run e2 := by
  rw [denoteForLoopRev'Return_succ_run bi n i lo hi body env h, hb]
  cases w <;> first | rfl | simp at hw

theorem denoteForLoopRev'Return_succ_nonval (n : Nat) (i : String) (lo hi : Int)
    (body : ImpExpr) (env e2 : Env) (o : Outcome) (h : lo < hi)
    (hb : (denote' bi (n + 1) body).run (env.extend i (.int (hi - 1))) = (o, e2))
    (ho : ∀ v, o ≠ .val v) :
    (_root_.Hax.denoteForLoopRev'Return bi (n + 1) i lo hi body).run env = (o, e2) := by
  rw [denoteForLoopRev'Return_succ_run bi n i lo hi body env h, hb]
  cases o with
  | val v => exact absurd rfl (ho v)
  | _ => rfl

end SourceSteps

/-! ## §5  The fragment -/

/-- The fragment the simulation covers, at tail position `tl` and loop context
    `il`.  Every name it mentions is non-reserved. -/
def exitSimOk : Bool → Bool → ImpExpr → Bool
  | tl, il, .letBind n (.lit (.uintLit .w64 _)) body => !exitReserved n && exitSimOk tl il body
  | tl, il, .letBind n (.lit (.bool _)) body => !exitReserved n && exitSimOk tl il body
  | tl, il, .letBind n (.app op [.var a, .var b]) body =>
      (scalarOpExpr op (.SVar a) (.SVar b)).isSome && !exitReserved n && !exitReserved a &&
        !exitReserved b && exitSimOk tl il body
  | tl, il, .seq a b => exitSimOk false il a && exitSimOk tl il b
  | tl, il, .ifThenElse (.var v) t e => !exitReserved v && exitSimOk tl il t && exitSimOk tl il e
  | false, _, .whileFoldReturn (.var c) body => !exitReserved c && exitSimOk false true body
  | false, _, .forFoldReturn i lo hi body =>
      (forBounds lo hi).isSome && !exitReserved i && exitSimOk false true body
  | false, _, .forFoldRevReturn i lo hi body =>
      (forBounds lo hi).isSome && !exitReserved i && exitSimOk false true body
  | _, true, .cfBreak (.var x) => !exitReserved x
  | _, true, .cfBreak (.lit (.uintLit .w64 _)) => true
  | _, _, .var x => !exitReserved x
  | _, _, .unitVal => true
  | true, _, .lit (.uintLit .w64 _) => true
  | _, _, _ => false

/-! ## §5  The simulation statement -/

/-- The simulation of `e`: from agreeing states with the exit flag `0`, a run of
    `denote'` ending in a value is matched by a run of the lowered command ending
    in agreeing states; a command that cannot exit leaves the flag `0`. -/
def ExitSim (bi : Builtins) (N : Nat) (leafSpec : LeafSpec) (e : ImpExpr) : Prop :=
  ∀ (tl : Bool) (fl : Option String) (fuel : Nat) (env env' : Env) (o : Outcome)
    (rs : RustState) (c : LowCT) (x : Bool),
    exitSimOk tl fl.isSome e = true → RunCtx fl →
    haxToLowCTK true tl fl e = some (c, x) →
    (denote' bi fuel e).run env = (o, env') →
    (∃ v, o = .val v) →
    envAgreesOff env rs → rs.rsScalar exitRetName = 0 →
    ∃ rs', RustExec N leafSpec c rs rs' ∧ envAgreesExit tl o env' rs' ∧
      (x = false → rs'.rsScalar exitRetName = 0)

/-! ## §7  Reserved names, scalar slots and agreement -/

theorem exitReserved_ret : exitReserved exitRetName = true := by decide
theorem exitReserved_val : exitReserved exitValName = true := by decide
theorem exitReserved_res : exitReserved exitResName = true := by decide

theorem exitRetName_ne_val : exitRetName ≠ exitValName := by decide
theorem exitRetName_ne_res : exitRetName ≠ exitResName := by decide
theorem exitValName_ne_res : exitValName ≠ exitResName := by decide

theorem exitReserved_of_runSlot {r : String} (h : exitRunSlot r = true) :
    exitReserved r = true := by
  unfold exitRunSlot at h
  unfold exitReserved
  rw [List.isPrefixOf_iff_prefix] at h ⊢
  exact List.IsPrefix.trans (by decide) h

theorem runSlot_ne_ret {r : String} (h : exitRunSlot r = true) : r ≠ exitRetName := by
  rintro rfl; revert h; decide

theorem runSlot_ne_val {r : String} (h : exitRunSlot r = true) : r ≠ exitValName := by
  rintro rfl; revert h; decide

theorem runSlot_exitRunName {fl : Option String} (h : RunCtx fl) :
    exitRunSlot (exitRunName fl) = true := by
  cases fl with
  | none => decide
  | some r =>
    by_cases hf : r = exitFnSlot
    · subst hf; rw [exitRunName_fn]; decide
    have hr := (h r rfl).resolve_right hf
    unfold exitRunSlot at hr ⊢
    rw [List.isPrefixOf_iff_prefix] at hr ⊢
    simp only [exitRunName, if_neg hf, String.toList_append]
    exact List.IsPrefix.trans hr (List.prefix_append _ _)

theorem ne_of_reserved {n r : String} (hn : exitReserved n = false) (hr : exitReserved r = true) :
    n ≠ r := by
  rintro rfl; rw [hn] at hr; cases hr

@[simp] theorem rsScalar_rsSetScalar (rs : RustState) (x y : String) (v : Nat) :
    (rsSetScalar rs x v).rsScalar y = if y = x then v else rs.rsScalar y := by
  simp [rsSetScalar]

theorem rsSetScalar_rsSetScalar (rs : RustState) (x : String) (v w : Nat) :
    rsSetScalar (rsSetScalar rs x v) x w = rsSetScalar rs x w := by
  cases rs
  simp only [rsSetScalar, RustState.mk.injEq, true_and]
  funext y
  by_cases h : y = x <;> simp [h]

/-- Writing a reserved slot preserves agreement. -/
theorem envAgreesOff_set_reserved {env : Env} {rs : RustState} {x : String} (v : Nat)
    (hx : exitReserved x = true) (h : envAgreesOff env rs) :
    envAgreesOff env (rsSetScalar rs x v) := by
  intro name w hn hw
  rw [rsScalar_rsSetScalar, if_neg (ne_of_reserved hn hx)]
  exact h name w hn hw

/-- Binding a non-reserved name to a scalar value and writing its decoding into
    the slot of the same name preserves agreement. -/
theorem envAgreesOff_extend {env : Env} {rs : RustState} {n : String} {v : Value} {k : Nat}
    (hn : exitReserved n = false) (hv : ScalarVal v) (hk : valueToScalar v = some k)
    (h : envAgreesOff env rs) :
    envAgreesOff (env.extend n v) (rsSetScalar rs n k) := by
  intro name w hname hw
  rw [rsScalar_rsSetScalar]
  by_cases he : name = n
  · subst he
    simp only [_root_.Hax.Env.extend, beq_self_eq_true, if_true, Option.some.injEq] at hw
    subst hw
    exact ⟨hv, by simpa using hk⟩
  · simp only [_root_.Hax.Env.extend, beq_iff_eq, he, if_false] at hw
    rw [if_neg he]
    exact h name w hname hw

/-- The three shapes of a scalar value. -/
theorem ScalarVal.cases {v : Value} (h : ScalarVal v) :
    (∃ n, v = .uint .w64 n ∧ n < 2 ^ 64) ∨ (∃ b, v = .bool b) ∨
      ∃ n : Int, v = .int n ∧ 0 ≤ n ∧ n < 2 ^ 64 := by
  match v, h with
  | .uint .w64 n, h => exact Or.inl ⟨n, rfl, h⟩
  | .bool b, _ => exact Or.inr (Or.inl ⟨b, rfl⟩)
  | .int n, h => exact Or.inr (Or.inr ⟨n, rfl, h⟩)

theorem haxToLowCTK_letBind_eq (sc tl : Bool) (fl : Option String) (n : String)
    (val body : ImpExpr) :
    haxToLowCTK sc tl fl (.letBind n val body) =
      match letHeadK sc n val, haxToLowCTK sc tl fl body with
      | some k, some (bC, x) => some (k bC, x)
      | _, _ => none := by
  cases tl <;> cases fl <;> rfl

theorem haxToLowCTK_seq_eq (sc tl : Bool) (fl : Option String) (a b : ImpExpr) :
    haxToLowCTK sc tl fl (.seq a b) =
      match haxToLowCTK sc false fl a, haxToLowCTK sc tl fl b with
      | some (aC, xa), some (bC, xb) =>
          some (if xa then .RSeq aC (exitGuard bC) else .RSeq aC bC, xa || xb)
      | _, _ => none := by
  cases tl <;> cases fl <;> rfl

theorem haxToLowCTK_ifThenElse_eq (sc tl : Bool) (fl : Option String) (v : String)
    (t e : ImpExpr) :
    haxToLowCTK sc tl fl (.ifThenElse (.var v) t e) =
      match haxToLowCTK sc tl fl t, haxToLowCTK sc tl fl e with
      | some (tC, xt), some (eC, xe) => some (.RIfNz v tC eC, xt || xe)
      | _, _ => none := by
  cases tl <;> cases fl <;> rfl

theorem haxToLowCTK_whileFoldReturn_eq (sc : Bool) (fl : Option String) (c : String)
    (body : ImpExpr) :
    haxToLowCTK sc false fl (.whileFoldReturn (.var c) body) =
      match haxToLowCTK sc false (some (exitRunName fl)) body with
      | some (bC, _) => some (exitLoop (exitRunName fl) c bC, true)
      | none => none := by
  cases fl <;> rfl

theorem haxToLowCTK_forFoldReturn_eq (sc : Bool) (fl : Option String) (i : String)
    (lo hi body : ImpExpr) :
    haxToLowCTK sc false fl (.forFoldReturn i lo hi body) =
      match forBounds lo hi, haxToLowCTK sc false (some (exitRunName fl)) body with
      | some (l, h), some (bC, _) => some (exitForLoop (exitRunName fl) i l h bC, true)
      | _, _ => none := by
  cases fl <;> rfl

theorem haxToLowCTK_forFoldRevReturn_eq (sc : Bool) (fl : Option String) (i : String)
    (lo hi body : ImpExpr) :
    haxToLowCTK sc false fl (.forFoldRevReturn i lo hi body) =
      match forBounds lo hi, haxToLowCTK sc false (some (exitRunName fl)) body with
      | some (l, h), some (bC, _) => some (exitForLoopRev (exitRunName fl) i l h bC, true)
      | _, _ => none := by
  cases fl <;> rfl

/-- A scalar value is not tagged by control flow. -/
theorem ScalarVal.not_cf {v : Value} (h : ScalarVal v) : v.isControlFlow = false := by
  match v, h with
  | .uint .w64 _, _ => rfl
  | .bool _, _ => rfl
  | .int _, _ => rfl

/-- A value outcome that is not control-flow-tagged: its exit agreement is the
    normal component. -/
theorem envAgreesExit_val {tl : Bool} {v : Value} {env : Env} {rs : RustState}
    (hv : v.isControlFlow = false) :
    envAgreesExit tl (.val v) env rs ↔
      (rs.rsScalar exitRetName = 0 ∧ envAgreesOff env rs ∧
        (tl = true → valueToScalar v = some (rs.rsScalar exitResName))) := by
  cases v <;> first | exact Iff.rfl | simp at hv

/-- **The guarded continuation.** When the exit flag is `1`, the guarded
    statement `exitGuard b` leaves the state unchanged. -/
theorem exitGuard_exited (N : Nat) (leafSpec : LeafSpec) (b : LowCT) (rs : RustState)
    (h : rs.rsScalar exitRetName = 1) : RustExec N leafSpec (exitGuard b) rs rs :=
  RustExec.ifTrue _ _ _ _ _ 1 h (by decide) (RustExec.skip _)

/-- When the exit flag is `0`, the guarded statement runs. -/
theorem exitGuard_running (N : Nat) (leafSpec : LeafSpec) (b : LowCT) (rs rs' : RustState)
    (h : rs.rsScalar exitRetName = 0) (hb : RustExec N leafSpec b rs rs') :
    RustExec N leafSpec (exitGuard b) rs rs' :=
  RustExec.ifFalse _ _ _ _ _ h hb

/-- Writing the result slot preserves the exit flag and agreement. -/
theorem res_write (rs : RustState) (k : Nat) {env : Env} (h0 : rs.rsScalar exitRetName = 0)
    (hag : envAgreesOff env rs) :
    (rsSetScalar rs exitResName k).rsScalar exitRetName = 0 ∧
      envAgreesOff env (rsSetScalar rs exitResName k) ∧
      (rsSetScalar rs exitResName k).rsScalar exitResName = k := by
  refine ⟨?_, envAgreesOff_set_reserved k exitReserved_res hag, by simp⟩
  rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_res, h0]

/-! ## §8  The arms -/

section Arms

variable (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)

theorem exitSim_var (x : String) : ExitSim bi N leafSpec (.var x) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  have hx : exitReserved x = false := by
    cases tl <;> cases fl <;> simpa [exitSimOk] using hok
  rw [denote'_var_run] at hrun
  cases hv : env x with
  | none =>
    rw [hv] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨_, h⟩ := hval; cases h
  | some v =>
    rw [hv] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨hsv, hdec⟩ := hag x v hx hv
    cases tl with
    | false =>
      have hK' : haxToLowCTK true false fl (.var x) = some (.RSkip, false) := by
        cases fl <;> rfl
      rw [hK'] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      exact ⟨rs, RustExec.skip rs,
        (envAgreesExit_val hsv.not_cf).mpr ⟨hret, hag, fun h => by cases h⟩, fun _ => hret⟩
    | true =>
      have hK' : haxToLowCTK true true fl (.var x) =
          some (.RScalarSetExpr exitResName (.SVar x), false) := by
        cases fl <;> rfl
      rw [hK'] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      obtain ⟨h0, hag', hres⟩ := res_write rs (rs.rsScalar x) hret hag
      exact ⟨_, RustExec.scalarSetExpr _ _ rs,
        (envAgreesExit_val hsv.not_cf).mpr ⟨h0, hag', fun _ => by
          rw [hdec]; exact congrArg some hres.symm⟩,
        fun _ => h0⟩

theorem exitSim_unitVal : ExitSim bi N leafSpec .unitVal := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  rw [denote'_unitVal_run] at hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  cases tl with
  | false =>
    have hK' : haxToLowCTK true false fl .unitVal = some (.RSkip, false) := by cases fl <;> rfl
    rw [hK'] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    exact ⟨rs, RustExec.skip rs,
      (envAgreesExit_val rfl).mpr ⟨hret, hag, fun h => by cases h⟩, fun _ => hret⟩
  | true =>
    have hK' : haxToLowCTK true true fl .unitVal = some (.RScalarSet exitResName 0, false) := by
      cases fl <;> rfl
    rw [hK'] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    obtain ⟨h0, hag', hres⟩ := res_write rs 0 hret hag
    exact ⟨_, RustExec.scalarSet _ _ rs,
      (envAgreesExit_val rfl).mpr ⟨h0, hag', fun _ => by rw [hres]; rfl⟩, fun _ => h0⟩

theorem exitSim_lit (l : ImpLit) : ExitSim bi N leafSpec (.lit l) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  rw [denote'_lit_run] at hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  cases tl with
  | false => cases fl <;> simp [exitSimOk] at hok
  | true =>
    cases l with
    | uintLit w k =>
      cases w <;> try (cases fl <;> simp [exitSimOk] at hok; done)
      have hK' : haxToLowCTK true true fl (.lit (.uintLit .w64 k)) =
          some (.RScalarSet exitResName (k % IntWidth.w64.modulus), false) := by
        cases fl <;> rfl
      rw [hK'] at hK
      simp only [Option.some.injEq, Prod.mk.injEq] at hK
      obtain ⟨rfl, rfl⟩ := hK
      obtain ⟨h0, hag', hres⟩ := res_write rs (k % IntWidth.w64.modulus) hret hag
      exact ⟨_, RustExec.scalarSet _ _ rs,
        (envAgreesExit_val rfl).mpr ⟨h0, hag', fun _ => by rw [hres]; rfl⟩, fun _ => h0⟩
    | _ => cases fl <;> simp [exitSimOk] at hok

theorem exitSim_cfBreak (e : ImpExpr) : ExitSim bi N leafSpec (.cfBreak e) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  cases fl with
  | none => cases tl <;> simp [exitSimOk] at hok
  | some r =>
    rw [denote'_cfBreak_run'] at hrun
    -- the payload's word `k` and value `v`, with the payload store `s`
    obtain ⟨v, k, s, hpay, hsv, hk, hs, hsexec⟩ :
        ∃ v k s, (denote' bi fuel e).run env = (.val v, env) ∧ ScalarVal v ∧
          valueToScalar v = some k ∧ storeScalar exitValName e = some s ∧
          RustExec N leafSpec s rs (rsSetScalar rs exitValName k) := by
      cases e with
      | var x =>
        have hx : exitReserved x = false := by cases tl <;> simpa [exitSimOk] using hok
        rw [denote'_var_run] at hrun ⊢
        cases hv : env x with
        | none =>
          rw [hv] at hrun
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
          obtain ⟨_, h⟩ := hval; cases h
        | some v =>
          obtain ⟨hsv, hdec⟩ := hag x v hx hv
          exact ⟨v, rs.rsScalar x, _, rfl, hsv, hdec, rfl, RustExec.scalarSetExpr _ _ rs⟩
      | lit l =>
        cases l with
        | uintLit w k =>
          cases w <;> try (cases tl <;> simp [exitSimOk] at hok; done)
          refine ⟨.uint .w64 (k % IntWidth.w64.modulus), k % IntWidth.w64.modulus, _,
            denote'_lit_run bi fuel _ env, ?_, rfl, rfl, RustExec.scalarSet _ _ rs⟩
          exact Nat.mod_lt _ (by decide)
        | _ => cases tl <;> simp [exitSimOk] at hok
      | _ => cases tl <;> simp [exitSimOk] at hok
    rw [hpay] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (show (Outcome.val (.controlFlow true v), env) = (o, env') by
      rw [← hrun]; rcases hsv.cases with ⟨_, rfl, _⟩ | ⟨_, rfl⟩ | ⟨_, rfl, _⟩ <;> rfl)
    have hK' : haxToLowCTK true tl (some r) (.cfBreak e) =
        some (.RSeq s (.RScalarSet exitRetName 1), true) := by
      cases tl <;> simp [haxToLowCTK, exitStore, hs]
    rw [hK'] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    refine ⟨_, RustExec.seq _ _ _ _ _ hsexec (RustExec.scalarSet _ _ _), ?_, fun h => by cases h⟩
    refine ⟨by simp, ?_, ?_⟩
    · rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val.symm, rsScalar_rsSetScalar, if_pos rfl]
      exact hk
    · exact envAgreesOff_set_reserved 1 exitReserved_ret
        (envAgreesOff_set_reserved k exitReserved_val hag)

theorem exitSim_letBind_lit (n : String) (l : ImpLit) (body : ImpExpr)
    (ihb : ExitSim bi N leafSpec body) :
    ExitSim bi N leafSpec (.letBind n (.lit l) body) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  obtain ⟨v, k, hv, hsv, hk, hhead, hn, hokB⟩ :
      ∃ v k, Value.ofLit l = v ∧ ScalarVal v ∧ valueToScalar v = some k ∧
        letHeadK true n (.lit l) =
          some (fun bC => .RLetU64Zero n (.RSeq (.RScalarSet n k) bC)) ∧
        exitReserved n = false ∧ exitSimOk tl fl.isSome body = true := by
    cases l with
    | uintLit w k =>
      cases w <;> try (cases tl <;> cases fl <;> simp [exitSimOk] at hok; done)
      have hh : exitReserved n = false ∧ exitSimOk tl fl.isSome body = true := by
        cases tl <;> cases fl <;>
          simpa only [exitSimOk, Bool.and_eq_true, Bool.not_eq_true'] using hok
      exact ⟨_, k % IntWidth.w64.modulus, rfl, Nat.mod_lt _ (by decide), rfl, rfl, hh⟩
    | bool b =>
      have hh : exitReserved n = false ∧ exitSimOk tl fl.isSome body = true := by
        cases tl <;> cases fl <;>
          simpa only [exitSimOk, Bool.and_eq_true, Bool.not_eq_true'] using hok
      exact ⟨_, if b then 1 else 0, rfl, trivial, valueToScalar_bool b, rfl, hh⟩
    | _ => cases tl <;> cases fl <;> simp [exitSimOk] at hok
  rw [denote'_letBind_run_val bi fuel n _ body env env v (by rw [denote'_lit_run, hv])
    hsv.not_cf] at hrun
  rw [haxToLowCTK_letBind_eq, hhead] at hK
  rcases hB : haxToLowCTK true tl fl body with _ | ⟨bC, x⟩
  · rw [hB] at hK; cases hK
  rw [hB] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  have hret' : (rsSetScalar rs n k).rsScalar exitRetName = 0 := by
    rw [rsScalar_rsSetScalar, if_neg (ne_of_reserved hn exitReserved_ret).symm, hret]
  obtain ⟨rs', hexec, hagree, hx⟩ :=
    ihb tl fl fuel (env.extend n v) env' o (rsSetScalar rs n k) bC x hokB hfl hB hrun hval
      (envAgreesOff_extend hn hsv hk hag) hret'
  refine ⟨rs', RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSet _ _ _) ?_),
    hagree, hx⟩
  rw [rsSetScalar_rsSetScalar]; exact hexec

theorem scalarOpExpr_isSome_vars (op x y x' y' : String) :
    (scalarOpExpr op (.SVar x) (.SVar y)).isSome =
      (scalarOpExpr op (.SVar x') (.SVar y')).isSome := by
  unfold scalarOpExpr
  split <;> rfl

theorem exitSim_letBind_app (hs : ScalarOpsSound bi) (n op a b : String) (body : ImpExpr)
    (ihb : ExitSim bi N leafSpec body) :
    ExitSim bi N leafSpec (.letBind n (.app op [.var a, .var b]) body) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  have hok' : (scalarOpExpr op (.SVar a) (.SVar b)).isSome = true ∧ exitReserved n = false ∧
      exitReserved a = false ∧ exitReserved b = false ∧
      exitSimOk tl fl.isSome body = true := by
    cases tl <;> cases fl <;>
      (simp only [exitSimOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
       exact ⟨hok.1.1.1.1, hok.1.1.1.2, hok.1.1.2, hok.1.2, hok.2⟩)
  obtain ⟨hop, hn, ha', hb', hokB⟩ := hok'
  obtain ⟨se, hse⟩ := Option.isSome_iff_exists.mp hop
  have herr : ∀ msg e1, (denote' bi fuel (.app op [.var a, .var b])).run env = (.err msg, e1) →
      False := by
    intro msg e1 h
    rw [denote'_letBind_run_nonval bi fuel n _ body env e1 _ h (fun v hv => by cases hv)] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨_, h⟩ := hval; cases h
  cases hva : env a with
  | none =>
    obtain ⟨msg, h⟩ := denote'_app2_run_none_left bi fuel op a b env hva
    exact (herr msg env h).elim
  | some va =>
    obtain ⟨hsa, hda⟩ := hag a va ha' hva
    cases hvb : env b with
    | none =>
      obtain ⟨msg, h⟩ := denote'_app2_run_none_right bi fuel op a b env va hva hsa.not_cf hvb
      exact (herr msg env h).elim
    | some vb =>
      obtain ⟨hsb, hdb⟩ := hag b vb hb' hvb
      have happ := denote'_app2_run bi fuel op a b env va vb hva hvb hsa.not_cf hsb.not_cf
      cases hbi : bi op [va, vb] with
      | none => rw [hbi] at happ; exact (herr _ env happ).elim
      | some r =>
        rw [hbi] at happ
        have hop' := hop
        rw [scalarOpExpr_isSome_vars op a b "a" "b"] at hop'
        obtain ⟨hsr, hdr⟩ := hs op va vb r _ _ hop' hsa hsb hda hdb hbi
        rw [denote'_letBind_run_val bi fuel n _ body env env r happ hsr.not_cf] at hrun
        have hhead : letHeadK true n (.app op [.var a, .var b]) =
            some (fun bC => .RSeq (.RScalarSetExpr n se) bC) := by
          simp only [letHeadK, hse]
        rw [haxToLowCTK_letBind_eq, hhead] at hK
        rcases hB : haxToLowCTK true tl fl body with _ | ⟨bC, x⟩
        · rw [hB] at hK; cases hK
        rw [hB] at hK
        simp only [Option.some.injEq, Prod.mk.injEq] at hK
        obtain ⟨rfl, rfl⟩ := hK
        have hk : valueToScalar r = some (se.eval rs.rsScalar) := by
          rw [scalarOpExpr_eval op a b se _ hse]; exact hdr
        have hret' : (rsSetScalar rs n (se.eval rs.rsScalar)).rsScalar exitRetName = 0 := by
          rw [rsScalar_rsSetScalar, if_neg (ne_of_reserved hn exitReserved_ret).symm, hret]
        obtain ⟨rs', hexec, hagree, hx⟩ :=
          ihb tl fl fuel (env.extend n r) env' o (rsSetScalar rs n (se.eval rs.rsScalar)) bC x
            hokB hfl hB hrun hval (envAgreesOff_extend hn hsr hk hag) hret'
        have hset : RustExec N leafSpec (.RScalarSetExpr n se) rs
            (rsSetScalar rs n (se.eval rs.rsScalar)) := by
          rw [← scalarOpExpr_evalState op a b se rs hse]
          exact RustExec.scalarSetExpr _ _ _
        exact ⟨rs', RustExec.seq _ _ _ _ _ hset hexec, hagree, hx⟩

theorem exitSim_seq (a b : ImpExpr) (iha : ExitSim bi N leafSpec a)
    (ihb : ExitSim bi N leafSpec b) : ExitSim bi N leafSpec (.seq a b) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  have hok' : exitSimOk false fl.isSome a = true ∧ exitSimOk tl fl.isSome b = true := by
    cases tl <;> cases fl <;> simpa only [exitSimOk, Bool.and_eq_true] using hok
  rw [haxToLowCTK_seq_eq] at hK
  rcases hA : haxToLowCTK true false fl a with _ | ⟨aC, xa⟩
  · rw [hA] at hK; cases hK
  rcases hB : haxToLowCTK true tl fl b with _ | ⟨bC, xb'⟩
  · rw [hA, hB] at hK; cases hK
  rw [hA, hB] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  rcases hra : (denote' bi fuel a).run env with ⟨oa, e1⟩
  cases oa with
  | val va =>
    obtain ⟨rs1, hexA, hagA, hxA⟩ :=
      iha false fl fuel env e1 (.val va) rs aC xa hok'.1 hfl hA hra ⟨va, rfl⟩ hag hret
    cases hcf : va.isControlFlow with
    | false =>
      obtain ⟨h1, hag1, -⟩ := (envAgreesExit_val hcf).mp hagA
      rw [denote'_seq_run_val bi fuel a b env e1 va hra hcf] at hrun
      obtain ⟨rs', hexB, hagB, hxB⟩ :=
        ihb tl fl fuel e1 env' o rs1 bC xb' hok'.2 hfl hB hrun hval hag1 h1
      refine ⟨rs', ?_, hagB, fun h => hxB (by simp at h; exact h.2)⟩
      cases xa
      · exact RustExec.seq _ _ _ _ _ hexA hexB
      · exact RustExec.seq _ _ _ _ _ hexA (exitGuard_running _ _ _ _ _ h1 hexB)
    | true =>
      cases va with
      | controlFlow k w =>
        cases k with
        | false => exact (show False from hagA).elim
        | true =>
          obtain ⟨h1, hw, hag1⟩ := hagA
          rw [denote'_seq_run_cf bi fuel a b env e1 true w hra] at hrun
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
          cases xa with
          | false => have h0 := hxA rfl; rw [h1] at h0; cases h0
          | true =>
            exact ⟨rs1, RustExec.seq _ _ _ _ _ hexA (exitGuard_exited _ _ _ _ h1),
              ⟨h1, hw, hag1⟩, fun h => by simp at h⟩
      | _ => simp at hcf
  | _ =>
    rw [denote'_seq_run_nonval bi fuel a b env e1 _ hra (fun v h => by cases h)] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨_, h⟩ := hval; cases h

theorem exitSim_ifThenElse (v : String) (t e : ImpExpr) (iht : ExitSim bi N leafSpec t)
    (ihe : ExitSim bi N leafSpec e) : ExitSim bi N leafSpec (.ifThenElse (.var v) t e) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  have hok' : exitReserved v = false ∧ exitSimOk tl fl.isSome t = true ∧
      exitSimOk tl fl.isSome e = true := by
    cases tl <;> cases fl <;>
      (simp only [exitSimOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
       exact ⟨hok.1.1, hok.1.2, hok.2⟩)
  rw [haxToLowCTK_ifThenElse_eq] at hK
  rcases hT : haxToLowCTK true tl fl t with _ | ⟨tC, xt⟩
  · rw [hT] at hK; cases hK
  rcases hE : haxToLowCTK true tl fl e with _ | ⟨eC, xe⟩
  · rw [hT, hE] at hK; cases hK
  rw [hT, hE] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  cases hvv : env v with
  | none =>
    rw [denote'_ifThenElse_var_run_none bi fuel v t e env hvv] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨_, h⟩ := hval; cases h
  | some w =>
    obtain ⟨hsw, hdw⟩ := hag v w hok'.1 hvv
    rcases hsw.cases with ⟨k, rfl, _⟩ | ⟨bb, rfl⟩ | ⟨k, rfl, _⟩
    · rw [denote'_ifThenElse_var_run_uint bi fuel v t e env _ k hvv] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    swap
    · rw [denote'_ifThenElse_var_run_int bi fuel v t e env k hvv] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    · rw [denote'_ifThenElse_var_run_bool bi fuel v t e env bb hvv] at hrun
      rw [valueToScalar_bool, Option.some.injEq] at hdw
      cases bb with
      | true =>
        simp only [if_true] at hrun hdw
        obtain ⟨rs', hex, hag', hx⟩ := iht tl fl fuel env env' o rs tC xt hok'.2.1 hfl hT hrun
          hval hag hret
        exact ⟨rs', RustExec.ifTrue _ _ _ _ _ 1 hdw.symm (by decide) hex, hag',
          fun h => hx (by simp at h; exact h.1)⟩
      | false =>
        simp only [Bool.false_eq_true, if_false] at hrun hdw
        obtain ⟨rs', hex, hag', hx⟩ := ihe tl fl fuel env env' o rs eC xe hok'.2.2 hfl hE hrun
          hval hag hret
        exact ⟨rs', RustExec.ifFalse _ _ _ _ _ hdw.symm hex, hag',
          fun h => hx (by simp at h; exact h.2)⟩

/-- The statement after each trip of a lowered `whileFoldReturn`: the loop slot
    becomes `0` if the body exited and the guard otherwise. -/
def loopTail (run c : String) : LowCT :=
  .RIfNz exitRetName (.RScalarSet run 0) (.RScalarSetExpr run (.SVar c))

/-- **The loop case**, by induction on fuel.  From agreeing states with the exit
    flag `0` and the loop slot holding the guard, a run of `denoteWhile'Return`
    ending in a value is matched by the lowered `RWhileNz`: a `false` guard exits
    at once; at a `true` guard the body runs, and either exits (the flag is `1`,
    the loop slot becomes `0`, and the loop stops) or ends normally (the loop slot
    is refreshed from the guard and the loop continues at the smaller fuel). -/
theorem exitLoop_sim (run c : String) (body : ImpExpr) (bC : LowCT) (xb : Bool)
    (ihb : ExitSim bi N leafSpec body) (hslot : exitRunSlot run = true)
    (hc : exitReserved c = false) (hokB : exitSimOk false true body = true)
    (hKB : haxToLowCTK true false (some run) body = some (bC, xb)) :
    ∀ (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      (_root_.Hax.denoteWhile'Return bi fuel (.var c) body).run env = (o, env') →
      (∃ v, o = .val v) → envAgreesOff env rs → rs.rsScalar exitRetName = 0 →
      rs.rsScalar run = rs.rsScalar c →
      ∃ rs', RustExec N leafSpec (.RWhileNz run (.RSeq bC (loopTail run c))) rs rs' ∧
        envAgreesExit false o env' rs' := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hcr : c ≠ run := ne_of_reserved hc (exitReserved_of_runSlot hslot)
  have hresv := exitReserved_of_runSlot hslot
  intro fuel
  induction fuel with
  | zero =>
    intro env env' o rs h hval _ _ _
    rw [denoteWhile'Return_zero_run] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    obtain ⟨_, h⟩ := hval; cases h
  | succ n IH =>
    intro env env' o rs h hval hag hret hrc
    cases hvc : env c with
    | none =>
      obtain ⟨msg, h'⟩ := denoteWhile'Return_succ_none bi n c body env hvc
      rw [h'] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | some w =>
      obtain ⟨hsw, hdw⟩ := hag c w hc hvc
      rcases hsw.cases with ⟨k, rfl, _⟩ | ⟨bb, rfl⟩ | ⟨k, rfl, _⟩
      · rw [denoteWhile'Return_succ_uint bi n c body env _ k hvc] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h
      swap
      · rw [denoteWhile'Return_succ_int bi n c body env k hvc] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h
      · rw [valueToScalar_bool, Option.some.injEq] at hdw
        cases bb with
        | false =>
          simp only [Bool.false_eq_true, if_false] at hdw
          rw [denoteWhile'Return_succ_false bi n c body env hvc] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact ⟨rs, RustExec.whileFalse _ _ _ (by rw [hrc, ← hdw]),
            (envAgreesExit_val rfl).mpr ⟨hret, hag, fun h => by cases h⟩⟩
        | true =>
          simp only [if_true] at hdw
          have hrun1 : rs.rsScalar run = 1 := by rw [hrc, ← hdw]
          rcases hb : (denote' bi (n + 1) body).run env with ⟨ob, e2⟩
          cases ob with
          | val vb =>
            obtain ⟨rs1, hex1, hag1, -⟩ :=
              ihb false (some run) (n + 1) env e2 (.val vb) rs bC xb hokB hctx hKB hb
                ⟨vb, rfl⟩ hag hret
            cases hcf : vb.isControlFlow with
            | false =>
              obtain ⟨h1, hagE, -⟩ := (envAgreesExit_val hcf).mp hag1
              rw [denoteWhile'Return_succ_iterate bi n c body env e2 vb hvc hb hcf] at h
              have htail : RustExec N leafSpec (loopTail run c) rs1
                  (rsSetScalar rs1 run (rs1.rsScalar c)) :=
                RustExec.ifFalse _ _ _ _ _ h1 (RustExec.scalarSetExpr _ _ _)
              have hag2 : envAgreesOff e2 (rsSetScalar rs1 run (rs1.rsScalar c)) :=
                envAgreesOff_set_reserved _ hresv hagE
              have hret2 : (rsSetScalar rs1 run (rs1.rsScalar c)).rsScalar exitRetName = 0 := by
                rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, h1]
              have hrc2 : (rsSetScalar rs1 run (rs1.rsScalar c)).rsScalar run =
                  (rsSetScalar rs1 run (rs1.rsScalar c)).rsScalar c := by
                simp [rsScalar_rsSetScalar, hcr]
              obtain ⟨rs', hexL, hagL⟩ := IH e2 env' o _ h hval hag2 hret2 hrc2
              exact ⟨rs', RustExec.whileTrue _ _ _ _ _ 1 hrun1 (by decide)
                (RustExec.seq _ _ _ _ _ hex1 htail) hexL, hagL⟩
            | true =>
              cases vb with
              | controlFlow kk ww =>
                cases kk with
                | false => exact (show False from hag1).elim
                | true =>
                  obtain ⟨h1, hw, hagE⟩ := hag1
                  have hwcf : ww.isControlFlow = false := by
                    cases ww <;> first | rfl | simp [valueToScalar] at hw
                  rw [denoteWhile'Return_succ_exit bi n c body env e2 ww hvc hb hwcf] at h
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
                  refine ⟨rsSetScalar rs1 run 0,
                    RustExec.whileTrue _ _ _ _ _ 1 hrun1 (by decide)
                      (RustExec.seq _ _ _ _ _ hex1
                        (RustExec.ifTrue _ _ _ _ _ 1 h1 (by decide) (RustExec.scalarSet _ _ _)))
                      (RustExec.whileFalse _ _ _ (by simp)), ?_, ?_, ?_⟩
                  · rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, h1]
                  · rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_val hslot).symm]; exact hw
                  · exact envAgreesOff_set_reserved _ hresv hagE
              | _ => simp at hcf
          | _ =>
            rw [denoteWhile'Return_succ_nonval bi n c body env e2 _ hvc hb
              (fun v h => by cases h)] at h
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
            obtain ⟨_, h⟩ := hval; cases h

theorem exitSim_whileFoldReturn (c : String) (body : ImpExpr)
    (ihb : ExitSim bi N leafSpec body) :
    ExitSim bi N leafSpec (.whileFoldReturn (.var c) body) := by
  intro tl fl fuel env env' o rs cc xb hok hfl hK hrun hval hag hret
  cases tl with
  | true => cases fl <;> simp [exitSimOk] at hok
  | false =>
    have hok' : exitReserved c = false ∧ exitSimOk false true body = true := by
      cases fl <;> simpa only [exitSimOk, Bool.and_eq_true, Bool.not_eq_true'] using hok
    rw [haxToLowCTK_whileFoldReturn_eq] at hK
    rcases hB : haxToLowCTK true false (some (exitRunName fl)) body with _ | ⟨bC, x⟩
    · rw [hB] at hK; cases hK
    rw [hB] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    rw [denote'_whileFoldReturn_run] at hrun
    have hslot := runSlot_exitRunName hfl
    have hresv := exitReserved_of_runSlot hslot
    have hcr : c ≠ exitRunName fl := ne_of_reserved hok'.1 hresv
    have hcret : c ≠ exitRetName := ne_of_reserved hok'.1 exitReserved_ret
    have hcval : c ≠ exitValName := ne_of_reserved hok'.1 exitReserved_val
    let rs0 := rsSetScalar (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0)
      (exitRunName fl) 0
    let rs1 := rsSetScalar rs0 (exitRunName fl) (rs0.rsScalar c)
    have hag1 : envAgreesOff env rs1 :=
      envAgreesOff_set_reserved _ hresv (envAgreesOff_set_reserved _ hresv
        (envAgreesOff_set_reserved _ exitReserved_val
          (envAgreesOff_set_reserved _ exitReserved_ret hag)))
    have hret1 : rs1.rsScalar exitRetName = 0 := by
      simp [rs1, rs0, rsScalar_rsSetScalar, (runSlot_ne_ret hslot).symm, exitRetName_ne_val]
    have hrc1 : rs1.rsScalar (exitRunName fl) = rs1.rsScalar c := by
      simp [rs1, rsScalar_rsSetScalar, hcr]
    obtain ⟨rs', hexL, hagL⟩ :=
      exitLoop_sim bi N leafSpec (exitRunName fl) c body bC x ihb hslot hok'.1 hok'.2 hB
        fuel env env' o rs1 hrun hval hag1 hret1 hrc1
    exact ⟨rs', RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _
      (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) hexL))),
      hagL, fun h => by cases h⟩

/-- After an exit, the trips of a guarded body write only the loop slot: the
    exit agreement is preserved across any number of them. -/
theorem exitedTrips (run : String) (B : LowCT) (hslot : exitRunSlot run = true) :
    ∀ (d k : Nat) (rs : RustState) (w : Value) (env : Env),
      envAgreesExit false (.val (.controlFlow true w)) env rs →
      ∃ rs', TripsFrom N leafSpec run (exitGuard B) k d rs rs' ∧
        envAgreesExit false (.val (.controlFlow true w)) env rs' := by
  intro d
  induction d with
  | zero => intro k rs w env hag; exact ⟨rs, rfl, hag⟩
  | succ d IH =>
    intro k rs w env hag
    obtain ⟨h1, hw, hagO⟩ := hag
    have h1' : (rsSetScalar rs run k).rsScalar exitRetName = 1 := by
      rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm]; exact h1
    have hag' : envAgreesExit false (.val (.controlFlow true w)) env (rsSetScalar rs run k) :=
      ⟨h1', by rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_val hslot).symm]; exact hw,
        envAgreesOff_set_reserved _ (exitReserved_of_runSlot hslot) hagO⟩
    obtain ⟨rs', hT, hagL⟩ := IH (k + 1) (rsSetScalar rs run k) w env hag'
    exact ⟨rs', ⟨rsSetScalar rs run k, exitGuard_exited N leafSpec B _ h1', hT⟩, hagL⟩

/-- **The counted-loop case**, by induction on the trips left.  From agreeing
    states with the exit flag `0`, a run of `denoteForLoop'Return` from counter
    `lo + j` ending in a value is matched by `d` trips of the guarded trip body
    from trip counter `j`: each trip binds the counter, runs the body, and either
    exits (the remaining trips are skipped by the guard) or continues at the next
    counter value. -/
theorem exitForTrips_sim (run i : String) (lo hi : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSim bi N leafSpec body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOk false true body = true)
    (hKB : haxToLowCTK true false (some run) body = some (bC, xb)) :
    ∀ (d j fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      j + d = hi - lo →
      (_root_.Hax.denoteForLoop'Return bi fuel i ((lo + j : Nat) : Int) hi body).run env =
        (o, env') →
      (∃ v, o = .val v) → envAgreesOff env rs → rs.rsScalar exitRetName = 0 →
      ∃ rs', TripsFrom N leafSpec run (exitForTrip run i lo bC) j d rs rs' ∧
        envAgreesExit false o env' rs' := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hresv := exitReserved_of_runSlot hslot
  have hir : i ≠ run := ne_of_reserved hi_ hresv
  have hiret : i ≠ exitRetName := ne_of_reserved hi_ exitReserved_ret
  intro d
  induction d with
  | zero =>
    intro j fuel env env' o rs hj h hval hag hret
    rw [denoteForLoop'Return_ge_run bi fuel i _ _ body env (by omega)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rs, rfl, (envAgreesExit_val rfl).mpr ⟨hret, hag, fun h => by cases h⟩⟩
  | succ d IH =>
    intro j fuel env env' o rs hj h hval hag hret
    have hlt : ((lo + j : Nat) : Int) < hi := by omega
    cases fuel with
    | zero =>
      rw [denoteForLoop'Return_zero_run bi i _ _ body env hlt] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | succ n =>
      -- the state at the start of the body: the counter slot holds `lo + j`
      have hagT : envAgreesOff (env.extend i (.int ((lo + j : Nat) : Int)))
          (rsSetScalar (rsSetScalar rs run j) i (lo + j)) :=
        envAgreesOff_extend hi_ ⟨by omega, by omega⟩ (valueToScalar_int _)
          (envAgreesOff_set_reserved _ hresv hag)
      have hretT : (rsSetScalar (rsSetScalar rs run j) i (lo + j)).rsScalar exitRetName = 0 := by
        rw [rsScalar_rsSetScalar, if_neg hiret.symm, rsScalar_rsSetScalar,
          if_neg (runSlot_ne_ret hslot).symm, hret]
      have hpre : ∀ r, RustExec N leafSpec bC (rsSetScalar (rsSetScalar rs run j) i (lo + j)) r →
          RustExec N leafSpec (exitForTrip run i lo bC) (rsSetScalar rs run j) r := by
        intro r hr
        have hst : rsSetScalar (rsSetScalar (rsSetScalar rs run j) i 0) i
            ((SExpr.SAdd (.SVar run) (.SLit lo)).evalState
              (rsSetScalar (rsSetScalar rs run j) i 0)) =
            rsSetScalar (rsSetScalar rs run j) i (lo + j) := by
          rw [rsSetScalar_rsSetScalar]
          simp only [SExpr.evalState, rsScalar_rsSetScalar, if_neg hir.symm, if_true]
          rw [Nat.add_comm]
        refine exitGuard_running N leafSpec _ _ _
          (by rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hret])
          (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) ?_))
        rw [hst]; exact hr
      rcases hb : (denote' bi (n + 1) body).run (env.extend i (.int ((lo + j : Nat) : Int)))
        with ⟨ob, e2⟩
      cases ob with
      | val vb =>
        obtain ⟨rs1, hex1, hag1, -⟩ :=
          ihb false (some run) (n + 1) _ e2 (.val vb) _ bC xb hokB hctx hKB hb ⟨vb, rfl⟩ hagT hretT
        cases hcf : vb.isControlFlow with
        | false =>
          obtain ⟨h1, hagE, -⟩ := (envAgreesExit_val hcf).mp hag1
          rw [denoteForLoop'Return_succ_iterate bi n i _ hi body env e2 vb hlt hb hcf] at h
          have h' : (_root_.Hax.denoteForLoop'Return bi n i ((lo + (j + 1) : Nat) : Int) hi
              body).run e2 = (o, env') := by
            rw [show ((lo + (j + 1) : Nat) : Int) = ((lo + j : Nat) : Int) + 1 by push_cast; ring]
            exact h
          obtain ⟨rs', hT, hagL⟩ := IH (j + 1) n e2 env' o rs1 (by omega) h' hval hagE h1
          exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
        | true =>
          cases vb with
          | controlFlow kk ww =>
            cases kk with
            | false => exact (show False from hag1).elim
            | true =>
              obtain ⟨h1, hw, hagE⟩ := hag1
              have hwcf : ww.isControlFlow = false := by
                cases ww <;> first | rfl | simp [valueToScalar] at hw
              rw [denoteForLoop'Return_succ_exit bi n i _ hi body env e2 ww hlt hb hwcf] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
              obtain ⟨rs', hT, hagL⟩ :=
                exitedTrips N leafSpec run _ hslot d (j + 1) rs1 ww _ ⟨h1, hw, hagE⟩
              exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
          | _ => simp at hcf
      | _ =>
        rw [denoteForLoop'Return_succ_nonval bi n i _ hi body env e2 _ hlt hb
          (fun v h => by cases h)] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h

theorem exitSim_forFoldReturn (i : String) (lo hi body : ImpExpr)
    (ihb : ExitSim bi N leafSpec body) :
    ExitSim bi N leafSpec (.forFoldReturn i lo hi body) := by
  intro tl fl fuel env env' o rs cc xb hok hfl hK hrun hval hag hret
  cases tl with
  | true => cases fl <;> simp [exitSimOk] at hok
  | false =>
    have hok' : (forBounds lo hi).isSome = true ∧ exitReserved i = false ∧
        exitSimOk false true body = true := by
      cases fl <;> simpa only [exitSimOk, Bool.and_eq_true, Bool.not_eq_true', and_assoc] using hok
    rw [haxToLowCTK_forFoldReturn_eq] at hK
    rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
    · rw [hFB] at hok'; cases hok'.1
    obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
    rcases hB : haxToLowCTK true false (some (exitRunName fl)) body with _ | ⟨bC, x⟩
    · rw [hFB, hB] at hK; cases hK
    rw [hFB, hB] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    rw [denote'_forFoldReturn_lit_run] at hrun
    have hslot := runSlot_exitRunName hfl
    have hag0 : envAgreesOff env (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) :=
      envAgreesOff_set_reserved _ exitReserved_val (envAgreesOff_set_reserved _ exitReserved_ret hag)
    have hret0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar
        exitRetName = 0 := by
      rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]
    have hrun0 : (_root_.Hax.denoteForLoop'Return bi fuel i ((l + 0 : Nat) : Int) h body).run env =
        (o, env') := by
      rw [Nat.add_zero]; exact hrun
    obtain ⟨rs', hT, hagL⟩ :=
      exitForTrips_sim bi N leafSpec (exitRunName fl) i l h body bC x ihb hslot hok'.2.1 hh
        hok'.2.2 hB (h - l) 0 fuel env env' o _ (by omega) hrun0 hval hag0 hret0
    have hFor := rustExec_rFor_of_tripsFrom N leafSpec (exitRunName fl) _ (h - l) 0 _ _ rs'
      (RustExec.forZero _ _ _) hT
    rw [Nat.zero_add] at hFor
    exact ⟨rs', RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _ hFor), hagL,
      fun h => by cases h⟩

/-- **The reverse counted-loop case**: as `exitForTrips_sim`, with the counter
    running from `hi - 1` down and trip `j` binding it to `hi - 1 - j`. -/
theorem exitForTripsRev_sim (run i : String) (lo hi : Nat) (body : ImpExpr) (bC : LowCT)
    (xb : Bool) (ihb : ExitSim bi N leafSpec body) (hslot : exitRunSlot run = true)
    (hi_ : exitReserved i = false) (hhi : hi ≤ 2 ^ 64)
    (hokB : exitSimOk false true body = true)
    (hKB : haxToLowCTK true false (some run) body = some (bC, xb)) :
    ∀ (d j fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState),
      j + d = hi - lo →
      (_root_.Hax.denoteForLoopRev'Return bi fuel i lo ((hi - j : Nat) : Int) body).run env =
        (o, env') →
      (∃ v, o = .val v) → envAgreesOff env rs → rs.rsScalar exitRetName = 0 →
      ∃ rs', TripsFrom N leafSpec run (exitForTripRev run i hi bC) j d rs rs' ∧
        envAgreesExit false o env' rs' := by
  have hctx : RunCtx (some run) := fun r hr => by cases hr; exact Or.inl hslot
  have hresv := exitReserved_of_runSlot hslot
  have hir : i ≠ run := ne_of_reserved hi_ hresv
  have hiret : i ≠ exitRetName := ne_of_reserved hi_ exitReserved_ret
  intro d
  induction d with
  | zero =>
    intro j fuel env env' o rs hj h hval hag hret
    rw [denoteForLoopRev'Return_ge_run bi fuel i _ _ body env (by omega)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rs, rfl, (envAgreesExit_val rfl).mpr ⟨hret, hag, fun h => by cases h⟩⟩
  | succ d IH =>
    intro j fuel env env' o rs hj h hval hag hret
    have hlt : (lo : Int) < ((hi - j : Nat) : Int) := by omega
    have hc : ((hi - j : Nat) : Int) - 1 = ((hi - 1 - j : Nat) : Int) := by omega
    cases fuel with
    | zero =>
      rw [denoteForLoopRev'Return_zero_run bi i _ _ body env hlt] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨_, h⟩ := hval; cases h
    | succ n =>
      have hagT : envAgreesOff (env.extend i (.int (((hi - j : Nat) : Int) - 1)))
          (rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j)) :=
        envAgreesOff_extend hi_ ⟨by omega, by omega⟩ (by rw [hc, valueToScalar_int])
          (envAgreesOff_set_reserved _ hresv hag)
      have hretT : (rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j)).rsScalar exitRetName = 0 := by
        rw [rsScalar_rsSetScalar, if_neg hiret.symm, rsScalar_rsSetScalar,
          if_neg (runSlot_ne_ret hslot).symm, hret]
      have hpre : ∀ r, RustExec N leafSpec bC (rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j)) r →
          RustExec N leafSpec (exitForTripRev run i hi bC) (rsSetScalar rs run j) r := by
        intro r hr
        have hst : rsSetScalar (rsSetScalar (rsSetScalar rs run j) i 0) i
            ((SExpr.SSub (.SLit (hi - 1)) (.SVar run)).evalState
              (rsSetScalar (rsSetScalar rs run j) i 0)) =
            rsSetScalar (rsSetScalar rs run j) i (hi - 1 - j) := by
          rw [rsSetScalar_rsSetScalar]
          simp only [SExpr.evalState, rsScalar_rsSetScalar, if_neg hir.symm, if_true]
        refine exitGuard_running N leafSpec _ _ _
          (by rw [rsScalar_rsSetScalar, if_neg (runSlot_ne_ret hslot).symm, hret])
          (RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) ?_))
        rw [hst]; exact hr
      rcases hb : (denote' bi (n + 1) body).run (env.extend i (.int (((hi - j : Nat) : Int) - 1)))
        with ⟨ob, e2⟩
      cases ob with
      | val vb =>
        obtain ⟨rs1, hex1, hag1, -⟩ :=
          ihb false (some run) (n + 1) _ e2 (.val vb) _ bC xb hokB hctx hKB hb ⟨vb, rfl⟩ hagT hretT
        cases hcf : vb.isControlFlow with
        | false =>
          obtain ⟨h1, hagE, -⟩ := (envAgreesExit_val hcf).mp hag1
          rw [denoteForLoopRev'Return_succ_iterate bi n i lo _ body env e2 vb hlt hb hcf] at h
          have h' : (_root_.Hax.denoteForLoopRev'Return bi n i lo ((hi - (j + 1) : Nat) : Int)
              body).run e2 = (o, env') := by
            rw [show ((hi - (j + 1) : Nat) : Int) = ((hi - j : Nat) : Int) - 1 by omega]
            exact h
          obtain ⟨rs', hT, hagL⟩ := IH (j + 1) n e2 env' o rs1 (by omega) h' hval hagE h1
          exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
        | true =>
          cases vb with
          | controlFlow kk ww =>
            cases kk with
            | false => exact (show False from hag1).elim
            | true =>
              obtain ⟨h1, hw, hagE⟩ := hag1
              have hwcf : ww.isControlFlow = false := by
                cases ww <;> first | rfl | simp [valueToScalar] at hw
              rw [denoteForLoopRev'Return_succ_exit bi n i lo _ body env e2 ww hlt hb hwcf] at h
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
              obtain ⟨rs', hT, hagL⟩ :=
                exitedTrips N leafSpec run _ hslot d (j + 1) rs1 ww _ ⟨h1, hw, hagE⟩
              exact ⟨rs', ⟨rs1, hpre rs1 hex1, hT⟩, hagL⟩
          | _ => simp at hcf
      | _ =>
        rw [denoteForLoopRev'Return_succ_nonval bi n i lo _ body env e2 _ hlt hb
          (fun v h => by cases h)] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        obtain ⟨_, h⟩ := hval; cases h

theorem exitSim_forFoldRevReturn (i : String) (lo hi body : ImpExpr)
    (ihb : ExitSim bi N leafSpec body) :
    ExitSim bi N leafSpec (.forFoldRevReturn i lo hi body) := by
  intro tl fl fuel env env' o rs cc xb hok hfl hK hrun hval hag hret
  cases tl with
  | true => cases fl <;> simp [exitSimOk] at hok
  | false =>
    have hok' : (forBounds lo hi).isSome = true ∧ exitReserved i = false ∧
        exitSimOk false true body = true := by
      cases fl <;> simpa only [exitSimOk, Bool.and_eq_true, Bool.not_eq_true', and_assoc] using hok
    rw [haxToLowCTK_forFoldRevReturn_eq] at hK
    rcases hFB : forBounds lo hi with _ | ⟨l, h⟩
    · rw [hFB] at hok'; cases hok'.1
    obtain ⟨rfl, rfl, hh⟩ := forBounds_some hFB
    rcases hB : haxToLowCTK true false (some (exitRunName fl)) body with _ | ⟨bC, x⟩
    · rw [hFB, hB] at hK; cases hK
    rw [hFB, hB] at hK
    simp only [Option.some.injEq, Prod.mk.injEq] at hK
    obtain ⟨rfl, rfl⟩ := hK
    rw [denote'_forFoldRevReturn_lit_run] at hrun
    have hslot := runSlot_exitRunName hfl
    have hag0 : envAgreesOff env (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0) :=
      envAgreesOff_set_reserved _ exitReserved_val (envAgreesOff_set_reserved _ exitReserved_ret hag)
    have hret0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitValName 0).rsScalar
        exitRetName = 0 := by
      rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_val, rsScalar_rsSetScalar, if_pos rfl]
    have hrun0 : (_root_.Hax.denoteForLoopRev'Return bi fuel i l ((h - 0 : Nat) : Int) body).run
        env = (o, env') := by
      rw [Nat.sub_zero]; exact hrun
    obtain ⟨rs', hT, hagL⟩ :=
      exitForTripsRev_sim bi N leafSpec (exitRunName fl) i l h body bC x ihb hslot hok'.2.1 hh
        hok'.2.2 hB (h - l) 0 fuel env env' o _ (by omega) hrun0 hval hag0 hret0
    have hFor := rustExec_rFor_of_tripsFrom N leafSpec (exitRunName fl) _ (h - l) 0 _ _ rs'
      (RustExec.forZero _ _ _) hT
    rw [Nat.zero_add] at hFor
    exact ⟨rs', RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _ hFor), hagL,
      fun h => by cases h⟩

/-- An expression outside the fragment simulates vacuously. -/
theorem exitSim_of_not_ok (e : ImpExpr) (h : ∀ tl il, exitSimOk tl il e = false) :
    ExitSim bi N leafSpec e := by
  intro tl fl _ _ _ _ _ _ _ hok
  rw [h] at hok; cases hok

end Arms

/-! ## §9  The simulation theorems -/

/-- **Simulation of the exit-flag lowering.**  For a builtin table computing the
    scalar operations soundly, every expression of the fragment simulates:
    the lowered command matches every `denote'` run that ends in a value. -/
theorem haxToLowCTK_simulates (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (hs : ScalarOpsSound bi) (e : ImpExpr) : ExitSim bi N leafSpec e := by
  have nok : ∀ e : ImpExpr, (∀ tl il, exitSimOk tl il e = false) → ExitSim bi N leafSpec e :=
    exitSim_of_not_ok bi N leafSpec
  induction e using ImpExpr.ind with
  | lit l => exact exitSim_lit bi N leafSpec l
  | var x => exact exitSim_var bi N leafSpec x
  | unitVal => exact exitSim_unitVal bi N leafSpec
  | letBind n val body _ ihb =>
    cases val with
    | lit l => exact exitSim_letBind_lit bi N leafSpec n l body ihb
    | app op args =>
      rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, rest⟩⟩⟩
      · exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
      · exact nok _ (fun tl il => by cases tl <;> cases il <;> cases a1 <;> rfl)
      · cases a1 with
        | var a =>
          cases a2 with
          | var b => exact exitSim_letBind_app bi N leafSpec hs n op a b body ihb
          | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
        | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
      · exact nok _ (fun tl il => by
          cases tl <;> cases il <;> cases a1 <;> (try cases a2) <;> rfl)
    | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
  | seq a b iha ihb => exact exitSim_seq bi N leafSpec a b iha ihb
  | ifThenElse c t e _ iht ihe =>
    cases c with
    | var v => exact exitSim_ifThenElse bi N leafSpec v t e iht ihe
    | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
  | whileFoldReturn c body _ ihb =>
    cases c with
    | var v => exact exitSim_whileFoldReturn bi N leafSpec v body ihb
    | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)
  | forFoldReturn i lo hi body _ _ ihb => exact exitSim_forFoldReturn bi N leafSpec i lo hi body ihb
  | forFoldRevReturn i lo hi body _ _ ihb =>
    exact exitSim_forFoldRevReturn bi N leafSpec i lo hi body ihb
  | cfBreak e _ => exact exitSim_cfBreak bi N leafSpec e
  | _ => exact nok _ (fun tl il => by cases tl <;> cases il <;> rfl)

/-- The scalar a function returns: the payload of an early exit, or the final
    value. -/
def outcomeScalar : Outcome → Option Nat
  | .val (.controlFlow true v) => valueToScalar v
  | .val v => valueToScalar v
  | _ => none

theorem outcomeScalar_val {v : Value} (hv : v.isControlFlow = false) :
    outcomeScalar (.val v) = valueToScalar v := by
  cases v <;> first | rfl | simp at hv

/-- The fragment in a loop context contains the fragment outside every loop. -/
theorem exitSimOk_inLoop_of (tl il : Bool) (e : ImpExpr) (h : exitSimOk tl il e = true) :
    exitSimOk tl true e = true := by
  fun_induction exitSimOk tl il e <;> simp_all [exitSimOk]

/-- **Function-level simulation with function-level exits.**  For a function
    body of the fragment in tail position in an exit context (so a `cfBreak`
    may occur at function level, outside every loop), a builtin table computing
    the scalar operations soundly, and an entry state agreeing with the entry
    environment off the reserved names, a `denote'` run ending in a value is
    matched by the lowered function `haxToLowCTFn e`, whose result slot holds the
    decoding of the returned value (for an early exit) or of the final value. -/
theorem haxToLowCTFn_simulates_exit (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (hs : ScalarOpsSound bi) (e : ImpExpr) (c : LowCT)
    (hok : exitSimOk true true e = true) (hK : haxToLowCTFn e = some c)
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel e).run env = (o, env')) (hval : ∃ v, o = .val v)
    (hag : envAgreesOff env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ outcomeScalar o = some (rs'.rsScalar exitResName) := by
  unfold haxToLowCTFn at hK
  rcases hK0 : haxToLowCTK true true (some exitFnSlot) e with _ | ⟨c0, x⟩
  · rw [hK0] at hK; cases hK
  rw [hK0] at hK
  simp only [Option.map_some, Option.some.injEq] at hK
  subst hK
  have hag0 : envAgreesOff env (rsSetScalar (rsSetScalar rs exitRetName 0) exitResName 0) :=
    envAgreesOff_set_reserved _ exitReserved_res (envAgreesOff_set_reserved _ exitReserved_ret hag)
  have hret0 : (rsSetScalar (rsSetScalar rs exitRetName 0) exitResName 0).rsScalar exitRetName = 0 := by
    simp [rsScalar_rsSetScalar]
  obtain ⟨rs1, hex, hagE, -⟩ :=
    haxToLowCTK_simulates bi N leafSpec hs e true (some exitFnSlot) fuel env env' o _ c0 x hok
      (fun r h => Or.inr (Option.some.inj h).symm) hK0 hrun hval hag0 hret0
  obtain ⟨v, rfl⟩ := hval
  cases hcf : v.isControlFlow with
  | false =>
    obtain ⟨h1, -, htail⟩ := (envAgreesExit_val hcf).mp hagE
    refine ⟨rs1, RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _
      (RustExec.seq _ _ _ _ _ hex (RustExec.ifFalse _ _ _ _ _ h1 (RustExec.skip _)))), ?_⟩
    rw [outcomeScalar_val hcf]
    exact htail rfl
  | true =>
    cases v with
    | controlFlow k w =>
      cases k with
      | false => exact (show False from hagE).elim
      | true =>
        obtain ⟨h1, hw, -⟩ := hagE
        refine ⟨rsSetScalar rs1 exitResName (rs1.rsScalar exitValName),
          RustExec.letU64Zero _ _ _ _ (RustExec.letU64Zero _ _ _ _
            (RustExec.seq _ _ _ _ _ hex
              (RustExec.ifTrue _ _ _ _ _ 1 h1 (by decide) (RustExec.scalarSetExpr _ _ _)))), ?_⟩
        simp only [outcomeScalar, rsScalar_rsSetScalar, if_true]
        exact hw
    | _ => simp at hcf

/-- **Function-level simulation.**  `haxToLowCTFn_simulates_exit` for a function
    body of the fragment outside every loop context. -/
theorem haxToLowCTFn_simulates (bi : Builtins) (N : Nat) (leafSpec : LeafSpec)
    (hs : ScalarOpsSound bi) (e : ImpExpr) (c : LowCT)
    (hok : exitSimOk true false e = true) (hK : haxToLowCTFn e = some c)
    (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (hrun : (denote' bi fuel e).run env = (o, env')) (hval : ∃ v, o = .val v)
    (hag : envAgreesOff env rs) :
    ∃ rs', RustExec N leafSpec c rs rs' ∧ outcomeScalar o = some (rs'.rsScalar exitResName) :=
  haxToLowCTFn_simulates_exit bi N leafSpec hs e c (exitSimOk_inLoop_of true false e hok) hK
    fuel env env' o rs hrun hval hag

/-- The pipeline output of the search loop (`searchLoopShape`) lies in the
    fragment; a static check that the fragment's hypothesis is satisfiable on a
    loop with an early return, closed by `decide` in milliseconds. -/
theorem searchLoopShape_exitSimOk : exitSimOk true false searchLoopShape = true := by decide

end CatCrypt.Crypto.Hax
