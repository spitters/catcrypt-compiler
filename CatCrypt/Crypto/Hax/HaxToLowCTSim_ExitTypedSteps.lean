/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTSim_ExitTypedDefs
public import CatCrypt.Crypto.Hax.HaxCallNames

/-!
# The exit-flag lowering with one heap per name: agreement, steps and heads

The second of four parts of the typed exit-flag lowering; the overview is the docstring of
`HaxToLowCTSim_ExitTyped.lean`.  This part holds §7–§12: scalar values and agreement under
a placement (`ScalarValN`, `envAgreesT`, `envAgreesExitT`), the scalar operations and the
leaf conditions (`ExitLeaves`, `exitRange`, `leafCallScalar_exitRange`), the source steps
and the counted-loop bounds read at run time (`boundSE_sim`), the simulation statement
`ExitSimTy` and the translator's equations, the marshalling of call arguments into the
reserved tower slots (`callMarshal_sim`), and the simulation of the heads of a `letBind`
(`head_lit`, `head_var`, `headT_app`, `head_app`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit IntWidth Value Env Outcome Builtins denote')
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT Located SExpr RustState RustExec LeafSpec rsSetScalar)

/-! ## §7  Scalar values and agreement under a placement -/

open CatCrypt.Crypto.Jasmin.LowCT (rsSetTower locatedLookup locatedUpdate RustVal towerLimb
  rsTowerLimb)

theorem ScalarValN.not_cf {v : Value} (h : ScalarValN v) : v.isControlFlow = false := by
  cases v <;> first | rfl | exact h.elim

theorem ScalarValN.of_scalarVal {v : Value} (h : ScalarVal v) : ScalarValN v := by
  match v, h with
  | .uint .w64 _, h => exact h
  | .bool _, _ => trivial
  | .int _, h => exact h

/-- Agreement under the placement `A`: every binding of a non-reserved name placed in
    the scalar heap is a scalar value whose decoding is its scalar slot; every binding
    of a name placed in a tower at `t` is a value without a control-flow tag related by
    `br` to the tower slot of that name, which holds type `t`. -/
def envAgreesT (br : ValueTowerBridge) (A : ExitTowers) (env : Env) (rs : RustState) : Prop :=
  ∀ name v, exitReserved name = false → env name = some v →
    match A.lookup name with
    | none => ScalarValN v ∧ valueToScalar v = some (rs.rsScalar name)
    | some t => v.isControlFlow = false ∧ ∃ val, rs.rsTower name = some ⟨t, val⟩ ∧ br t v val

section Agreement

variable {br : ValueTowerBridge} {A : ExitTowers} {env : Env} {rs : RustState}

theorem envAgreesT_scalar (h : envAgreesT br A env rs) {x : String} {v : Value}
    (hx : exitReserved x = false) (hs : A.lookup x = none) (hv : env x = some v) :
    ScalarValN v ∧ valueToScalar v = some (rs.rsScalar x) := by
  have h' := h x v hx hv
  rw [hs] at h'
  exact h'

theorem envAgreesT_tower (h : envAgreesT br A env rs) {x : String} {v : Value} {t : TowerType}
    (hx : exitReserved x = false) (ht : A.lookup x = some t) (hv : env x = some v) :
    v.isControlFlow = false ∧ ∃ val, rs.rsTower x = some ⟨t, val⟩ ∧ br t v val := by
  have h' := h x v hx hv
  rw [ht] at h'
  exact h'

theorem envAgreesT_not_cf (h : envAgreesT br A env rs) {x : String} {v : Value}
    (hx : exitReserved x = false) (hv : env x = some v) : v.isControlFlow = false := by
  rcases hA : A.lookup x with _ | t
  · exact (envAgreesT_scalar h hx hA hv).1.not_cf
  · exact (envAgreesT_tower h hx hA hv).1

/-- Writing a reserved scalar slot preserves agreement. -/
theorem envAgreesT_set_reserved {x : String} (k : Nat) (hx : exitReserved x = true)
    (h : envAgreesT br A env rs) : envAgreesT br A env (rsSetScalar rs x k) := by
  intro name w hn hw
  have h' := h name w hn hw
  rcases hA : A.lookup name with _ | t <;> rw [hA] at h'
  · rw [rsScalar_rsSetScalar, if_neg (ne_of_reserved hn hx)]
    exact h'
  · exact h'

/-- Writing a reserved tower slot preserves agreement. -/
theorem envAgreesT_setTower_reserved {x : String} (s : Σ t, RustVal t)
    (hx : exitReserved x = true) (h : envAgreesT br A env rs) :
    envAgreesT br A env (rsSetTower rs x s) := by
  intro name w hn hw
  have h' := h name w hn hw
  rcases hA : A.lookup name with _ | t <;> rw [hA] at h'
  · exact h'
  · rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other rs x name s (ne_of_reserved hn hx).symm]
    exact h'

/-- Binding a non-reserved scalar name to a scalar value and writing its decoding into
    its scalar slot preserves agreement. -/
theorem envAgreesT_extend {n : String} {v : Value} {k : Nat} (hn : exitReserved n = false)
    (hs : A.lookup n = none) (hv : ScalarValN v) (hk : valueToScalar v = some k)
    (h : envAgreesT br A env rs) : envAgreesT br A (env.extend n v) (rsSetScalar rs n k) := by
  intro name w hname hw
  by_cases he : name = n
  · subst he
    simp only [_root_.Hax.Env.extend, beq_self_eq_true, if_true, Option.some.injEq] at hw
    subst hw
    rw [hs]
    exact ⟨hv, by simpa using hk⟩
  · simp only [_root_.Hax.Env.extend, beq_iff_eq, he, if_false] at hw
    have h' := h name w hname hw
    rcases hA : A.lookup name with _ | t <;> rw [hA] at h'
    · rw [rsScalar_rsSetScalar, if_neg he]
      exact h'
    · exact h'

/-- Binding a non-reserved tower name to a value related to a tower value, and writing
    that tower value into its slot, preserves agreement. -/
theorem envAgreesT_extend_tower {n : String} {v : Value} {t : TowerType} {val : RustVal t}
    (hn : exitReserved n = false) (ht : A.lookup n = some t) (hcf : v.isControlFlow = false)
    (hbr : br t v val) (h : envAgreesT br A env rs) :
    envAgreesT br A (env.extend n v) (rsSetTower rs n ⟨t, val⟩) := by
  intro name w hname hw
  by_cases he : name = n
  · subst he
    simp only [_root_.Hax.Env.extend, beq_self_eq_true, if_true, Option.some.injEq] at hw
    subst hw
    rw [ht]
    exact ⟨hcf, val, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same rs name _, hbr⟩
  · simp only [_root_.Hax.Env.extend, beq_iff_eq, he, if_false] at hw
    have h' := h name w hname hw
    rcases hA : A.lookup name with _ | u <;> rw [hA] at h'
    · exact h'
    · rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other rs n name _ (Ne.symm he)]
      exact h'

/-- Agreement off the reserved names is agreement under the empty placement. -/
theorem envAgreesT_nil_of_off (h : envAgreesOff env rs) : envAgreesT br [] env rs := by
  intro name v hn hv
  obtain ⟨hs, hd⟩ := h name v hn hv
  exact ⟨ScalarValN.of_scalarVal hs, hd⟩

end Agreement

/-- The agreement of a component `w` of a tuple result with its slot: a scalar word whose
    decoding is the scalar slot, or a value related by `br` to the tower slot at the type
    the slot holds. -/
def compAgreesT (br : ValueTowerBridge) (slot : String) (w : Value) (rs : RustState) : Prop :=
  (ScalarValN w ∧ valueToScalar w = some (rs.rsScalar slot)) ∨
    ∃ t val, rs.rsTower slot = some ⟨t, val⟩ ∧ br t w val

/-- The agreement of a payload `w` held under the placement `p` with the slot `slot`: a
    scalar word decoding to the scalar slot for `p = none`, and a value related by `br` to
    the tower slot at `t` for `p = some t`. -/
def payloadAgreesT (br : ValueTowerBridge) (p : Option TowerType) (slot : String) (w : Value)
    (rs : RustState) : Prop :=
  match p with
  | none => ScalarValN w ∧ valueToScalar w = some (rs.rsScalar slot)
  | some t => ∃ val, rs.rsTower slot = some ⟨t, val⟩ ∧ br t w val

/-- The result agreement for result placement `R`: the decoding of `v` in the scalar
    result slot, `v` related by `br` to the tower result slot, `v` a tuple whose
    component `i` agrees with the slot `exitResCompName i` (`compAgreesT`), or `v` an
    `Option` whose tag `0` or `1` is the scalar result slot and whose payload agrees with
    the slot `exitResCompName 0` (`payloadAgreesT`). -/
def resultAgreesT (br : ValueTowerBridge) (R : ExitRes) (v : Value) (rs : RustState) :
    Prop :=
  match R with
  | .scalar => valueToScalar v = some (rs.rsScalar exitResName)
  | .tower t => ∃ val, rs.rsTower exitResName = some ⟨t, val⟩ ∧ br t v val
  | .tuple => ∃ vs, v = .tuple vs ∧
      ∀ (i : Nat) (w : Value), vs[i]? = some w → compAgreesT br (exitResCompName i) w rs
  | .option p => (v = .option none ∧ rs.rsScalar exitResName = 0) ∨
      ∃ w, v = .option (some w) ∧ rs.rsScalar exitResName = 1 ∧
        payloadAgreesT br p (exitResCompName 0) w rs

/-- Agreement with the exit component under the placement `A` and result placement
    `R`, for an expression in tail position `tl`. -/
def envAgreesExitT (br : ValueTowerBridge) (A : ExitTowers) (R : ExitRes)
    (tl : Bool) : Outcome → Env → RustState → Prop
  | .val (.controlFlow true v), env, rs =>
      rs.rsScalar exitRetName = 1 ∧ valueToScalar v = some (rs.rsScalar exitValName) ∧
        envAgreesT br A env rs
  | .val (.controlFlow false _), _, _ => False
  | .val v, env, rs =>
      rs.rsScalar exitRetName = 0 ∧ envAgreesT br A env rs ∧
        (tl = true → resultAgreesT br R v rs)
  | _, _, _ => False

section ExitAgreement

variable {br : ValueTowerBridge} {A : ExitTowers} {R : ExitRes}

theorem envAgreesExitT_val {tl : Bool} {v : Value} {env : Env} {rs : RustState}
    (hv : v.isControlFlow = false) :
    envAgreesExitT br A R tl (.val v) env rs ↔
      (rs.rsScalar exitRetName = 0 ∧ envAgreesT br A env rs ∧
        (tl = true → resultAgreesT br R v rs)) := by
  cases v <;> first | exact Iff.rfl | simp at hv

theorem envAgreesExitT_reset {env : Env} {rs : RustState} {v : Value}
    (hag : envAgreesT br A env rs) (hv : v.isControlFlow = false) :
    envAgreesExitT br A R false (.val v) env (rsSetScalar rs exitRetName 0) :=
  (envAgreesExitT_val hv).mpr ⟨by simp [rsScalar_rsSetScalar],
    envAgreesT_set_reserved _ exitReserved_ret hag, fun h => by cases h⟩

/-- Writing the scalar result slot preserves the exit flag and agreement. -/
theorem res_writeT (rs : RustState) (k : Nat) {env : Env} (h0 : rs.rsScalar exitRetName = 0)
    (hag : envAgreesT br A env rs) :
    (rsSetScalar rs exitResName k).rsScalar exitRetName = 0 ∧
      envAgreesT br A env (rsSetScalar rs exitResName k) ∧
      (rsSetScalar rs exitResName k).rsScalar exitResName = k := by
  refine ⟨?_, envAgreesT_set_reserved k exitReserved_res hag, by simp⟩
  rw [rsScalar_rsSetScalar, if_neg exitRetName_ne_res, h0]

end ExitAgreement

/-- A state with the scalar heap of `rs` and the tower slots of `rs` at every name other
    than the marshalling slots agrees with every environment `rs` agrees with. -/
theorem envAgreesT_of_eqOn {br : ValueTowerBridge} {A : ExitTowers} {env : Env}
    {rs rs1 : RustState} (hS : rs1.rsScalar = rs.rsScalar)
    (hT : ∀ y, exitReserved y = false → rs1.rsTower y = rs.rsTower y)
    (h : envAgreesT br A env rs) : envAgreesT br A env rs1 := by
  intro name w hn hw
  have h' := h name w hn hw
  rcases hA : A.lookup name with _ | t <;> rw [hA] at h'
  · rw [hS]; exact h'
  · rw [hT name hn]; exact h'

/-! ## §8  Scalar operations and leaf conditions -/

/-- hax-lean's scalar operation `op` on scalars, as `LowCT` computes it: the value of
    `scalarOpExprT op` on the literals `a` and `b`, and `0` for an operation outside
    `scalarOpExprT`. -/
def scalarOpNatT (op : String) (a b : Nat) : Nat :=
  match scalarOpExprT op (.SLit a) (.SLit b) with
  | some se => se.eval fun _ => 0
  | none => 0

theorem widthOp_sexpr_congr (w : Nat) (o : WidthOp) {a b a' b' : SExpr} {rs : RustState}
    {σ : String → Nat} (ha : a.evalState rs = a'.eval σ) (hb : b.evalState rs = b'.eval σ) :
    (o.sexpr w a b).evalState rs = (o.sexpr w a' b').eval σ := by
  cases o <;> simp only [WidthOp.sexpr, widthMask, orExprN, widthAmt, SExpr.evalState,
    SExpr.eval, ha, hb]

/-- The value of a scalar operation depends only on the values of its operands. -/
theorem scalarOpExprT_congr (op : String) {a b a' b' : SExpr} {rs : RustState}
    {σ : String → Nat} (ha : a.evalState rs = a'.eval σ) (hb : b.evalState rs = b'.eval σ) :
    (scalarOpExprT op a b).map (·.evalState rs) = (scalarOpExprT op a' b').map (·.eval σ) := by
  unfold scalarOpExprT
  split
  all_goals try simp only [Option.map_some, SExpr.evalState, SExpr.eval, orExprN, ha, hb]
  rcases widthOpOf op with _ | ⟨w, o⟩
  · rfl
  · simp only [Option.map_some, widthOp_sexpr_congr w o ha hb]

/-- The `SExpr` of a scalar operation on two scalar slots evaluates to
    `scalarOpNatT`. -/
theorem scalarOpExprT_evalState (op x y : String) (se : SExpr) (rs : RustState)
    (h : scalarOpExprT op (.SVar x) (.SVar y) = some se) :
    se.evalState rs = scalarOpNatT op (rs.rsScalar x) (rs.rsScalar y) := by
  have hc := scalarOpExprT_congr op (a := .SVar x) (b := .SVar y)
    (a' := .SLit (rs.rsScalar x)) (b' := .SLit (rs.rsScalar y)) (rs := rs) (σ := fun _ => 0)
    rfl rfl
  rw [h] at hc
  unfold scalarOpNatT
  rcases h' : scalarOpExprT op (.SLit (rs.rsScalar x)) (.SLit (rs.rsScalar y)) with _ | se'
  · rw [h'] at hc; cases hc
  · rw [h'] at hc
    simpa using hc

theorem scalarOpExprT_isSome_vars (op x y x' y' : String) :
    (scalarOpExprT op (.SVar x) (.SVar y)).isSome =
      (scalarOpExprT op (.SVar x') (.SVar y')).isSome := by
  unfold scalarOpExprT
  split <;> try rfl
  rcases widthOpOf op with _ | ⟨w, o⟩ <;> rfl

/-- The builtin table computes every operation of `scalarOpExprT` on scalar values as a
    scalar value decoding to `scalarOpNatT`. -/
def ScalarOpsSoundT (bi : Builtins) : Prop :=
  ∀ op va vb r na nb,
    (scalarOpExprT op (.SVar "a") (.SVar "b")).isSome = true →
    ScalarValN va → ScalarValN vb →
    valueToScalar va = some na → valueToScalar vb = some nb →
    bi op [va, vb] = some r →
    ScalarValN r ∧ valueToScalar r = some (scalarOpNatT op na nb)

/-- The leaf condition of a call with a scalar result: when every argument value is
    related by `br` to the tower value the call reads, the builtin's result is a scalar
    value whose decoding is limb `0` of the leaf output. -/
def LeafCallScalar (bi : Builtins) (leafSpec : LeafSpec) (f : String) (dt : TowerType)
    (br : ValueTowerBridge) : Prop :=
  ∀ (args : List Located) (vals : List Value) (argList : List (Σ t : TowerType, RustVal t))
    (oldV : RustVal dt) (vRes : Value),
    bi f vals = some vRes →
    List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
    ScalarValN vRes ∧
      valueToScalar vRes = some (towerLimb (leafSpec.call f dt (args.map (·.locDst)) oldV argList) 0)

/-- The element load agrees with the builtin `index` on an array of words: for an array
    value related by `br` to a slot of a type `t` whose elements are words
    (`exitElemTower t = none`) and an index decoding to `k`, the builtin's result is a
    scalar value whose decoding is limb `0` of the element the leaf loads. -/
def IndexScalarAgrees (br : ValueTowerBridge) (bi : Builtins) (leafSpec : LeafSpec) : Prop :=
  ∀ (t : TowerType) (vArr vIdx vRes : Value) (arrV : RustVal t) (k : Nat),
    exitElemTower t = none →
    br t vArr arrV → valueToScalar vIdx = some k →
    bi "index" [vArr, vIdx] = some vRes →
    ScalarValN vRes ∧ valueToScalar vRes = some
      (towerLimb (leafSpec.arrLoad { locVar := exitCallName, locSrc := .TFp } default ⟨t, arrV⟩ k) 0)

/-- The element load agrees with the builtin `index` on an array of tower values: for an
    array value related by `br` to a slot of a type `t` whose elements have the tower type
    `t'` (`exitElemTower t = some t'`) and an index decoding to `k`, the builtin's result is
    related by `br` at `t'` to the element the leaf loads. -/
def IndexTowerAgrees (br : ValueTowerBridge) (bi : Builtins) (leafSpec : LeafSpec) : Prop :=
  ∀ (t t' : TowerType) (vArr vIdx vRes : Value) (arrV : RustVal t) (k : Nat),
    exitElemTower t = some t' →
    br t vArr arrV → valueToScalar vIdx = some k →
    bi "index" [vArr, vIdx] = some vRes →
    br t' vRes (leafSpec.arrLoad { locVar := exitCallName, locSrc := t' } default ⟨t, arrV⟩ k)

/-- The element store agrees with the builtin `array_update` on an array of words: for an
    array value related by `br` to a slot of a type `t` whose elements are words
    (`exitElemTower t = none`, so that `exitElem t = t.elemType`), an index decoding to
    `k`, and a scalar word decoding to `m`, the builtin's result is related at `t` to the
    store at element `k` of the word `m` marshalled into limb `0` of a fresh slot of type
    `exitElem t` named `z`. -/
def ArrUpdateWordAgrees (br : ValueTowerBridge) (bi : Builtins) (leafSpec : LeafSpec) : Prop :=
  ∀ (arr z : String) (t : TowerType) (vArr vIdx vSrc vRes : Value) (arrV : RustVal t)
    (k m : Nat),
    exitElemTower t = none → 8 ≤ (exitElem t).storageBytes →
    br t vArr arrV → valueToScalar vIdx = some k →
    ScalarValN vSrc → valueToScalar vSrc = some m →
    bi "array_update" [vArr, vIdx, vSrc] = some vRes →
    br t vRes (leafSpec.arrStore { locVar := arr, locSrc := t } arrV k
      ⟨exitElem t, leafSpec.limbStore ⟨z, exitElem t⟩ default 0 (BitVec.ofNat 64 m)⟩)

/-- The element store agrees with the builtin `array_update` on an array of tower values:
    for an array value related by `br` to a slot of a type `t` whose elements are tower
    values (`exitElemTower t ≠ none`, of type `exitElem t`), an index decoding to `k`, and a
    value related at `exitElem t` to `srcV`, the builtin's result is related at `t` to the
    store of `srcV` at element `k`. -/
def ArrUpdateTowerAgrees (br : ValueTowerBridge) (bi : Builtins) (leafSpec : LeafSpec) : Prop :=
  ∀ (arr : String) (t : TowerType) (vArr vIdx vSrc vRes : Value) (arrV : RustVal t)
    (srcV : RustVal (exitElem t)) (k : Nat),
    exitElemTower t ≠ none →
    br t vArr arrV → valueToScalar vIdx = some k →
    br (exitElem t) vSrc srcV →
    bi "array_update" [vArr, vIdx, vSrc] = some vRes →
    br t vRes (leafSpec.arrStore { locVar := arr, locSrc := t } arrV k ⟨exitElem t, srcV⟩)

/-- The marshalling of a scalar word into limb `0` of a fresh tower slot of at least `8`
    bytes is related by `br` to the word. -/
def ExitMarshal (br : ValueTowerBridge) (leafSpec : LeafSpec) : Prop :=
  ∀ (loc : Located) (v : Value) (k : Nat), 8 ≤ loc.locDst.storageBytes →
    ScalarValN v → valueToScalar v = some k →
    br loc.locDst v (leafSpec.limbStore loc default 0 (BitVec.ofNat 64 k))

/-- `LeafCallAgreesArgs` on the argument lists of `k` values: the leaf condition of a call
    whose result has a fixed number `k` of elements. -/
def LeafCallAgreesArgsLen (bi : Builtins) (leafSpec : LeafSpec) (f : String) (dt : TowerType)
    (br : ValueTowerBridge) (k : Nat) : Prop :=
  ∀ (args : List Located) (vals : List Value) (argList : List (Σ t : TowerType, RustVal t))
    (oldV : RustVal dt) (vRes : Value),
    vals.length = k → bi f vals = some vRes →
    List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
    br dt vRes (leafSpec.call f dt (args.map (·.locDst)) oldV argList)

theorem leafCallAgreesArgsLen_of {bi : Builtins} {leafSpec : LeafSpec} {f : String}
    {dt : TowerType} {br : ValueTowerBridge} (h : LeafCallAgreesArgs bi leafSpec f dt br)
    (k : Nat) : LeafCallAgreesArgsLen bi leafSpec f dt br k :=
  fun args vals argList oldV vRes _ hbi hF => h args vals argList oldV vRes hbi hF

/-- The leaf condition of `repeat(v, cnt)` at an array type `c` of `k` elements: when the
    count decodes to `k` and the value of `v` is related by `br` to the one slot the call
    reads, the builtin's result is related at `c` to the leaf output. -/
def LeafRepeatAgrees (bi : Builtins) (leafSpec : LeafSpec) (c : TowerType)
    (br : ValueTowerBridge) (k : Nat) : Prop :=
  ∀ (args : List Located) (vv vc vRes : Value) (argList : List (Σ t : TowerType, RustVal t))
    (oldV : RustVal c),
    valueToScalar vc = some k → bi "repeat" [vv, vc] = some vRes →
    List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) [vv] argList →
    br c vRes (leafSpec.call "repeat" c (args.map (·.locDst)) oldV argList)

/-- The relation of a payload `w` of an `Option` held at the payload type `t` to the leaf
    output `out`: a scalar word decoding to limb `0` for `t = TU64`, and `br t` otherwise. -/
def optPayloadRel (br : ValueTowerBridge) (t : TowerType) (w : Value) (out : RustVal t) :
    Prop :=
  if t = .TU64 then ScalarValN w ∧ valueToScalar w = some (towerLimb out 0) else br t w out

/-- The leaf condition of a call `f` returning an `Option` with payload type `t`, run as
    the two-output call `RCallN f [tag, payload]`: when the argument values are related by
    `br` to the slots the call reads, the builtin returns an `Option`, output `0` holds its
    tag `1` or `0` in limb `0`, and output `1` is related to a payload by `optPayloadRel`. -/
def LeafCallOption (bi : Builtins) (leafSpec : LeafSpec) (f : String) (t : TowerType)
    (br : ValueTowerBridge) : Prop :=
  ∀ (args : List Located) (vals : List Value) (argList : List (Σ t : TowerType, RustVal t))
    (oldT : RustVal .TU64) (oldP : RustVal t) (vRes : Value),
    bi f vals = some vRes →
    List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
    ∃ o, vRes = .option o ∧
      towerLimb (leafSpec.call (CatCrypt.Crypto.Jasmin.LowCT.callNLeafName f 0) .TU64
        (args.map (·.locDst)) oldT argList) 0 = (if o.isSome then 1 else 0) ∧
      ∀ w, o = some w → w.isControlFlow = false ∧
        optPayloadRel br t w (leafSpec.call (CatCrypt.Crypto.Jasmin.LowCT.callNLeafName f 1) t
          (args.map (·.locDst)) oldP argList)

/-- A builtin table that does not implement `f` satisfies `LeafCallOption`. -/
theorem leafCallOption_of_unmatched (bi : Builtins) (leafSpec : LeafSpec) (f : String)
    (t : TowerType) (br : ValueTowerBridge) (h : ∀ vals, bi f vals = none) :
    LeafCallOption bi leafSpec f t br := by
  intro _ vals _ _ _ _ hBi
  rw [h vals] at hBi
  cases hBi

/-- The builtins `None` and `Some` build `Option` values. -/
def OptCtors (bi : Builtins) : Prop :=
  (∀ vals r, bi "None" vals = some r → vals = [] ∧ r = .option none) ∧
    (∀ vals r, bi "Some" vals = some r → ∃ v, vals = [v] ∧ r = .option (some v))

/-- A builtin table that does not implement `repeat` satisfies `LeafRepeatAgrees`. -/
theorem leafRepeatAgrees_of_unmatched (bi : Builtins) (leafSpec : LeafSpec) (c : TowerType)
    (br : ValueTowerBridge) (k : Nat) (h : ∀ vals, bi "repeat" vals = none) :
    LeafRepeatAgrees bi leafSpec c br k := by
  intro _ vv vc _ _ _ _ hBi
  rw [h [vv, vc]] at hBi
  cases hBi

/-- A builtin table that does not implement `f` satisfies `LeafCallAgreesArgsLen`. -/
theorem leafCallAgreesArgsLen_of_unmatched (bi : Builtins) (leafSpec : LeafSpec) (f : String)
    (dt : TowerType) (br : ValueTowerBridge) (k : Nat) (h : ∀ vals, bi f vals = none) :
    LeafCallAgreesArgsLen bi leafSpec f dt br k := by
  intro _ vals _ _ _ _ hBi
  rw [h vals] at hBi
  cases hBi

/-- `LeafCallAgreesArgsLen` on argument slots of the type `e`: the leaf condition of a call
    whose result has `k` elements and whose argument slots all have the type `e`. -/
def LeafCallAgreesArgsAt (bi : Builtins) (leafSpec : LeafSpec) (f : String) (dt : TowerType)
    (br : ValueTowerBridge) (k : Nat) (e : TowerType) : Prop :=
  ∀ (args : List Located) (vals : List Value) (argList : List (Σ t : TowerType, RustVal t))
    (oldV : RustVal dt) (vRes : Value),
    vals.length = k → (∀ p ∈ argList, p.1 = e) → bi f vals = some vRes →
    List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
    br dt vRes (leafSpec.call f dt (args.map (·.locDst)) oldV argList)

theorem leafCallAgreesArgsAt_of_len {bi : Builtins} {leafSpec : LeafSpec} {f : String}
    {dt : TowerType} {br : ValueTowerBridge} {k : Nat}
    (h : LeafCallAgreesArgsLen bi leafSpec f dt br k) (e : TowerType) :
    LeafCallAgreesArgsAt bi leafSpec f dt br k e :=
  fun args vals argList oldV vRes hl _ hbi hF => h args vals argList oldV vRes hl hbi hF

/-- The leaf condition of `f` on argument slots of the types `ts`: argument `i` read from a
    slot of type `ts[i]`. -/
def LeafCallAgreesArgsTys (bi : Builtins) (leafSpec : LeafSpec) (f : String) (dt : TowerType)
    (br : ValueTowerBridge) (ts : List TowerType) : Prop :=
  ∀ (args : List Located) (vals : List Value) (argList : List (Σ t : TowerType, RustVal t))
    (oldV : RustVal dt) (vRes : Value),
    argList.map (·.1) = ts → bi f vals = some vRes →
    List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
    br dt vRes (leafSpec.call f dt (args.map (·.locDst)) oldV argList)

theorem leafCallAgreesArgsTys_of {bi : Builtins} {leafSpec : LeafSpec} {f : String}
    {dt : TowerType} {br : ValueTowerBridge} (h : LeafCallAgreesArgs bi leafSpec f dt br)
    (ts : List TowerType) : LeafCallAgreesArgsTys bi leafSpec f dt br ts :=
  fun args vals argList oldV vRes _ hbi hF => h args vals argList oldV vRes hbi hF

/-- `LeafCallScalar` on argument slots of the types `ts`. -/
def LeafCallScalarTys (bi : Builtins) (leafSpec : LeafSpec) (f : String) (dt : TowerType)
    (br : ValueTowerBridge) (ts : List TowerType) : Prop :=
  ∀ (args : List Located) (vals : List Value) (argList : List (Σ t : TowerType, RustVal t))
    (oldV : RustVal dt) (vRes : Value),
    argList.map (·.1) = ts → bi f vals = some vRes →
    List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
    ScalarValN vRes ∧
      valueToScalar vRes = some (towerLimb (leafSpec.call f dt (args.map (·.locDst)) oldV argList) 0)

/-- The leaf conditions of the typed simulation, for the declared call result types `D`
    (by default none): the scalar operations, the absence of control-flow results, the
    storage of a scalar into limb `0` of a fresh tower slot of at least `8` bytes, the
    calls with a tower result without a declared type at `towerOfCallName f`
    (`LeafCallAgreesArgs`, for every call other than the array operations `index`,
    `array_update`, `array_lit`, `repeat`) and with a
    scalar result (`LeafCallScalar`, for the scalar calls and for the leaves of
    `exitTowerScalarNames` whose names the front admits, `exitAdmits`), the element load and the element store on an array of words
    and on an array of tower values, the array literal of `k` values at each array type of
    `k` elements (`arrLitN`), the `repeat` with count `k` at each such type (`repeatN`),
    the calls other than the array operations with a declared
    result type `dr` at `dr` (`callD`) and, for a declared word result `TU64`, with a scalar
    result (`wordD`), the calls returning an `Option` with a declared payload type
    `t` of `DO` (`optD`), the linked callees of `DA` with argument slot types `ts` and
    result type `dr` on argument slots of the types `ts` (`callA`, and `wordA` for a word
    result), and the `Option` constructors `None` and `Some` (`optCtors`).  `callD`,
    `wordD`, `optD`, `callA` and `wordA` hold for the default `D`, `DO` and `DA`. -/
structure ExitLeaves (bi : Builtins) (leafSpec : LeafSpec) (br : ValueTowerBridge)
    (D : String → Option TowerType := fun _ => none)
    (DO : String → Option TowerType := fun _ => none)
    (DA : String → Option (List TowerType × TowerType) := fun _ => none) : Prop where
  ops : ScalarOpsSoundT bi
  plain : _root_.Hax.ContinueFlag.BuiltinsPlain bi
  marshal : ExitMarshal br leafSpec
  callT : ∀ f, exitScalarRes f = false → f ≠ "index" → f ≠ "array_update" →
    f ≠ "array_lit" → f ≠ "repeat" → DA f = none →
    LeafCallAgreesArgs bi leafSpec f (towerOfCallName f) br
  /-- The scalar calls with an admitted name (`exitAdmits`). -/
  callS : ∀ f, exitScalarCall f = true → exitAdmits f = true →
    LeafCallScalar bi leafSpec f (towerOfCallName f) br
  /-- The leaf calls of `exitTowerScalarNames` with an admitted name, whose arguments are
      related by `br` to tower values and whose result is a scalar word read from limb `0`
      of the leaf output, with no bridge on the result. -/
  callTS : ∀ f, exitTowerScalarCall f = true → exitAdmits f = true →
    LeafCallScalar bi leafSpec f (towerOfCallName f) br
  index : IndexScalarAgrees br bi leafSpec
  update : ArrUpdateWordAgrees br bi leafSpec
  indexT : IndexTowerAgrees br bi leafSpec
  updateT : ArrUpdateTowerAgrees br bi leafSpec
  /-- The array literal of `k` values held at an array type `c` of `k` elements whose
      element type holds a word, read from argument slots of the element type
      `exitElem c`. -/
  arrLitN : ∀ c k, exitArrLen c = some k → exitMarshalOk (exitElem c) = true →
    LeafCallAgreesArgsAt bi leafSpec "array_lit" c br k (exitElem c)
  /-- The `repeat` with count `k` held at an array type `c` of `k` elements whose element
      type holds a word. -/
  repeatN : ∀ c k, exitArrLen c = some k → exitMarshalOk (exitElem c) = true →
    LeafRepeatAgrees bi leafSpec c br k
  /-- A call outside `exitScalarRes` and the array operations with the declared result type
      `dr` agrees at `dr`. -/
  callD : ∀ f dr, D f = some dr → DO f = none → DA f = none → exitScalarRes f = false →
    f ≠ "index" → f ≠ "array_update" → f ≠ "array_lit" → f ≠ "repeat" →
    LeafCallAgreesArgs bi leafSpec f dr br := by
    intro f dr h; simp at h
  /-- A call outside `exitScalarRes` and the array operations with the declared word result
      `TU64` returns a scalar word whose decoding is limb `0` of the leaf output at `TU64`. -/
  wordD : ∀ f, D f = some .TU64 → DA f = none → exitScalarRes f = false → f ≠ "index" →
    f ≠ "array_update" → f ≠ "array_lit" → f ≠ "repeat" →
    LeafCallScalar bi leafSpec f .TU64 br := by
    intro f h; simp at h
  /-- A linked callee with argument slot types `ts` and result type `dr` agrees at `dr` on
      argument slots of the types `ts`. -/
  callA : ∀ f ts dr, DA f = some (ts, dr) → exitScalarRes f = false → f ≠ "index" →
    f ≠ "array_update" → f ≠ "array_lit" → f ≠ "repeat" →
    LeafCallAgreesArgsTys bi leafSpec f dr br ts := by
    intro f ts dr h; simp at h
  /-- A linked callee with argument slot types `ts` and the word result `TU64` returns, on
      argument slots of the types `ts`, a scalar word whose decoding is limb `0` of the leaf
      output. -/
  wordA : ∀ f ts, DA f = some (ts, .TU64) → exitScalarRes f = false → f ≠ "index" →
    f ≠ "array_update" → f ≠ "array_lit" → f ≠ "repeat" →
    LeafCallScalarTys bi leafSpec f .TU64 br ts := by
    intro f ts h; simp at h
  /-- A call outside `exitScalarRes` and the array operations with the declared `Option`
      payload type `t` satisfies `LeafCallOption` at `t`. -/
  optD : ∀ f t, DO f = some t → exitScalarRes f = false → f ≠ "index" →
    f ≠ "array_update" → f ≠ "array_lit" → f ≠ "repeat" →
    LeafCallOption bi leafSpec f t br := by
    intro f t h; simp at h
  /-- The builtins `None` and `Some` build `Option` values. -/
  optCtors : OptCtors bi

/-- The leaf conditions for the declared types `D`, `DO` and the linked callees `DA` give
    those for any `D'`, `DO'`, `DA'` declaring fewer, when no name `D'` declares is declared
    by `DO`, and every name without a linked callee in `DA'` has none in `DA`. -/
theorem ExitLeaves.mono {bi : Builtins} {leafSpec : LeafSpec} {br : ValueTowerBridge}
    {D D' DO DO' : String → Option TowerType}
    {DA DA' : String → Option (List TowerType × TowerType)}
    (hL : ExitLeaves bi leafSpec br D DO DA)
    (h : ∀ f dr, D' f = some dr → D f = some dr)
    (hO : ∀ f t, DO' f = some t → DO f = some t)
    (hdisj : ∀ f dr, D' f = some dr → DO f = none)
    (hA : ∀ f x, DA' f = some x → DA f = some x)
    (hA' : ∀ f, DA' f = none → DA f = none) : ExitLeaves bi leafSpec br D' DO' DA' where
  ops := hL.ops
  plain := hL.plain
  marshal := hL.marshal
  callT f hsc h1 h2 h3 h4 hda := hL.callT f hsc h1 h2 h3 h4 (hA' f hda)
  callS := hL.callS
  callTS := hL.callTS
  index := hL.index
  update := hL.update
  indexT := hL.indexT
  updateT := hL.updateT
  arrLitN := hL.arrLitN
  repeatN := hL.repeatN
  callD f dr hf _ hda := hL.callD f dr (h f dr hf) (hdisj f dr hf) (hA' f hda)
  wordD f hf hda := hL.wordD f (h f _ hf) (hA' f hda)
  optD f t hf := hL.optD f t (hO f t hf)
  callA f ts dr hf := hL.callA f ts dr (hA f _ hf)
  wordA f ts hf := hL.wordA f ts (hA f _ hf)
  optCtors := hL.optCtors

/-- The leaf conditions for the placement `exitTowers e`, which declares no call result
    type and records no linked callee. -/
theorem ExitLeaves.atExitTowers {bi : Builtins} {leafSpec : LeafSpec} {br : ValueTowerBridge}
    (hL : ExitLeaves bi leafSpec br) (e : ImpExpr) :
    ExitLeaves bi leafSpec br (exitCallTys (exitTowers e)) (exitOptTys (exitTowers e))
      (exitCalleeTys (exitTowers e)) :=
  hL.mono (fun f dr h => by rw [exitCallTys_exitTowers] at h; cases h)
    (fun f t h => by rw [exitOptTys_exitTowers] at h; cases h) (fun _ _ _ => rfl)
    (fun f x h => by rw [exitCalleeTys_exitTowers] at h; cases h) (fun _ _ => rfl)

/-- Every call of `exitScalarRes` with an admitted name satisfies `LeafCallScalar`. -/
theorem ExitLeaves.callSR {bi : Builtins} {leafSpec : LeafSpec} {br : ValueTowerBridge}
    {D DO : String → Option TowerType} {DA : String → Option (List TowerType × TowerType)}
    (hL : ExitLeaves bi leafSpec br D DO DA) {f : String} (hf : exitScalarRes f = true)
    (ha : exitAdmits f = true) :
    LeafCallScalar bi leafSpec f (towerOfCallName f) br := by
  unfold exitScalarRes at hf
  rcases Bool.or_eq_true_iff.mp hf with h | h
  · exact hL.callS f h ha
  · exact hL.callTS f h ha

/-- A builtin table that does not implement `f` satisfies the scalar leaf condition. -/
theorem leafCallScalar_of_unmatched (bi : Builtins) (leafSpec : LeafSpec) (f : String)
    (dt : TowerType) (br : ValueTowerBridge) (h : ∀ vals, bi f vals = none) :
    LeafCallScalar bi leafSpec f dt br := by
  intro _ vals _ _ _ hBi
  rw [h vals] at hBi
  cases hBi

/-- A call whose result the range-refusing table `exitRange` checks: a call of
    `exitScalarRes`.  An element load is not checked: its result is a word or a tower value
    according to the tower type of the array (`IndexScalarAgrees`, `IndexTowerAgrees`). -/
def exitScalarResult (f : String) : Bool := exitScalarRes f

/-- The table `bi` with every scalar result outside `ScalarValN` refused: a call of
    `exitScalarResult` whose result is not a scalar word returns `none`.  A run of `denote'`
    over this table that ends in a value is a run of `bi` whose scalar results are scalar
    words. -/
def exitRange (bi : Builtins) : Builtins := fun f vals =>
  match bi f vals with
  | some r => if exitScalarResult f && !scalarValNB r then none else some r
  | none => none

theorem exitRange_some {bi : Builtins} {f : String} {vals : List Value} {r : Value}
    (h : exitRange bi f vals = some r) :
    bi f vals = some r ∧ (exitScalarResult f = true → ScalarValN r) := by
  unfold exitRange at h
  rcases hb : bi f vals with _ | r'
  · rw [hb] at h; cases h
  · rw [hb] at h
    simp only at h
    split_ifs at h with hc
    cases h
    refine ⟨rfl, fun hs => ?_⟩
    simp only [hs, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
    exact (scalarValNB_iff r).mp (by simpa using hc)

theorem exitRange_of_not_scalar {bi : Builtins} {f : String} (hf : exitScalarResult f = false)
    (vals : List Value) : exitRange bi f vals = bi f vals := by
  unfold exitRange
  rcases bi f vals with _ | r
  · rfl
  · simp [hf]

theorem builtinsPlain_exitRange {bi : Builtins} (h : _root_.Hax.ContinueFlag.BuiltinsPlain bi) :
    _root_.Hax.ContinueFlag.BuiltinsPlain (exitRange bi) :=
  fun f args v hv => h f args v (exitRange_some hv).1

/-- A leaf of a call with a tower result agrees on the range-refusing table when it agrees
    on the table. -/
theorem leafCallAgreesArgs_exitRange {bi : Builtins} {leafSpec : LeafSpec} {f : String}
    {dt : TowerType} {br : ValueTowerBridge} (h : LeafCallAgreesArgs bi leafSpec f dt br) :
    LeafCallAgreesArgs (exitRange bi) leafSpec f dt br :=
  fun args vals argList oldV vRes hbi hF => h args vals argList oldV vRes (exitRange_some hbi).1 hF

/-- A leaf of a call with a scalar result agrees on the range-refusing table when, on
    every scalar-word result of the table, limb `0` of the leaf output is its decoding. -/
theorem leafCallScalar_exitRange {bi : Builtins} {leafSpec : LeafSpec} {f : String}
    {dt : TowerType} {br : ValueTowerBridge} (hf : exitScalarRes f = true)
    (h : ∀ (args : List Located) (vals : List Value)
      (argList : List (Σ t : TowerType, RustVal t)) (oldV : RustVal dt) (vRes : Value),
      bi f vals = some vRes →
      List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
      ScalarValN vRes →
      valueToScalar vRes = some (towerLimb (leafSpec.call f dt (args.map (·.locDst)) oldV argList) 0)) :
    LeafCallScalar (exitRange bi) leafSpec f dt br := by
  intro args vals argList oldV vRes hbi hF
  obtain ⟨hb, hs⟩ := exitRange_some hbi
  have hsv := hs (by simp [exitScalarResult, hf])
  exact ⟨hsv, h args vals argList oldV vRes hb hF hsv⟩

theorem exitRange_index {bi : Builtins} (vals : List Value) :
    exitRange bi "index" vals = bi "index" vals :=
  exitRange_of_not_scalar exitScalarRes_index vals

/-- The range-refusing table leaves `index` unchanged, so the element loads agree on it when
    they agree on the table. -/
theorem indexScalarAgrees_exitRange {br : ValueTowerBridge} {bi : Builtins}
    {leafSpec : LeafSpec} (h : IndexScalarAgrees br bi leafSpec) :
    IndexScalarAgrees br (exitRange bi) leafSpec := by
  intro t vArr vIdx vRes arrV k ht hbr hk hbi
  rw [exitRange_index] at hbi
  exact h t vArr vIdx vRes arrV k ht hbr hk hbi

theorem indexTowerAgrees_exitRange {br : ValueTowerBridge} {bi : Builtins}
    {leafSpec : LeafSpec} (h : IndexTowerAgrees br bi leafSpec) :
    IndexTowerAgrees br (exitRange bi) leafSpec := by
  intro t t' vArr vIdx vRes arrV k ht hbr hk hbi
  rw [exitRange_index] at hbi
  exact h t t' vArr vIdx vRes arrV k ht hbr hk hbi

/-! ## §9  Source steps -/

section SourceStepsT

variable (bi : Builtins) (fuel : Nat)

/-- A scalar value is a bool, or neither a bool nor tagged by control flow. -/
theorem ScalarValN.bool_or {w : Value} (h : ScalarValN w) :
    (∃ b, w = .bool b) ∨ ((∀ b, w ≠ .bool b) ∧ w.isControlFlow = false) := by
  rcases h.cases with ⟨_, _, rfl, _⟩ | ⟨b, rfl⟩ | ⟨_, rfl, _⟩ | rfl
  · exact Or.inr ⟨fun b h => (by cases h), rfl⟩
  · exact Or.inl ⟨b, rfl⟩
  · exact Or.inr ⟨fun b h => (by cases h), rfl⟩
  · exact Or.inr ⟨fun b h => (by cases h), rfl⟩

theorem denote'_ifThenElse_var_run_nonbool (c : String) (t e : ImpExpr) (env : Env) (w : Value)
    (h : env c = some w) (hb : ∀ b, w ≠ .bool b) (hw : w.isControlFlow = false) :
    (denote' bi fuel (.ifThenElse (.var c) t e)).run env = (.err "if condition not a bool", env) := by
  rw [denote'_ifThenElse_run, denote'_var_run, h]
  cases w <;> first | rfl | exact absurd rfl (hb _) | simp at hw

theorem denoteWhile'Return_succ_nonbool (n : Nat) (c : String) (body : ImpExpr) (env : Env)
    (w : Value) (h : env c = some w) (hb : ∀ b, w ≠ .bool b) (hw : w.isControlFlow = false) :
    (_root_.Hax.denoteWhile'Return bi (n + 1) (.var c) body).run env =
      (.err "while condition not a bool", env) := by
  rw [denoteWhile'Return_succ_run, denote'_var_run, h]
  cases w <;> first | rfl | exact absurd rfl (hb _) | simp at hw

theorem denoteWhile'_succ_nonbool (n : Nat) (c : String) (body : ImpExpr) (env : Env)
    (w : Value) (h : env c = some w) (hb : ∀ b, w ≠ .bool b) (hw : w.isControlFlow = false) :
    (_root_.Hax.denoteWhile' bi (n + 1) (.var c) body).run env =
      (.err "while condition not a bool", env) := by
  rw [denoteWhile'_succ_run, denote'_var_run, h]
  cases w <;> first | rfl | exact absurd rfl (hb _) | simp at hw

/-- `denote'_forFoldReturn_var_scalar` for a variable holding a value of `ScalarValN`. -/
theorem denote'_forFoldReturn_var_scalarN (i h : String) (lo : Int) (body : ImpExpr)
    (env env' : Env) (o : Outcome)
    (hrun : (denote' bi fuel (.forFoldReturn i (.lit (.int lo)) (.var h) body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) (hsv : ∀ v, env h = some v → ScalarValN v) :
    ∃ (v : Value) (H : Nat), env h = some v ∧ valueToScalar v = some H ∧ H < 2 ^ 64 ∧
      (_root_.Hax.denoteForLoop'Return bi fuel i lo H body).run env = (o, env') := by
  obtain ⟨u, rfl⟩ := hval
  rcases hh : env h with _ | w
  · simp only [denote'] at hrun
    simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, hh, Value.ofLit] at hrun
    cases (Prod.mk.inj hrun).1
  · have hs := hsv w hh
    cases w with
    | int n =>
      obtain ⟨h0, h1⟩ := hs
      refine ⟨_, n.toNat, rfl, ?_, by omega, ?_⟩
      · have hd := valueToScalar_int n.toNat
        rwa [Int.toNat_of_nonneg h0] at hd
      · rw [denote'_forFoldReturn_var_run bi fuel i h lo body env n hh] at hrun
        rwa [Int.toNat_of_nonneg h0]
    | uint wd n =>
      refine ⟨_, n, rfl, valueToScalar_uint wd n, hs, ?_⟩
      rw [_root_.Hax.denote'_forFoldReturn_lit_var_uint bi fuel i h lo body env wd n hh] at hrun
      exact hrun
    | bool b =>
      simp only [denote'] at hrun
      simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, StateT.pure, hh, Value.ofLit] at hrun
      cases (Prod.mk.inj hrun).1
    | unit =>
      simp only [denote'] at hrun
      simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, StateT.pure, hh, Value.ofLit] at hrun
      cases (Prod.mk.inj hrun).1
    | _ => exact (show False from hs).elim

/-- `denote'_forFold_var_scalar` for a variable holding a value of `ScalarValN`. -/
theorem denote'_forFold_var_scalarN (i h : String) (lo : Int) (body : ImpExpr)
    (env env' : Env) (o : Outcome)
    (hrun : (denote' bi fuel (.forFold i (.lit (.int lo)) (.var h) body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) (hsv : ∀ v, env h = some v → ScalarValN v) :
    ∃ (v : Value) (H : Nat), env h = some v ∧ valueToScalar v = some H ∧ H < 2 ^ 64 ∧
      (_root_.Hax.denoteForLoop' bi fuel i lo H body).run env = (o, env') := by
  obtain ⟨u, rfl⟩ := hval
  rcases hh : env h with _ | w
  · simp only [denote'] at hrun
    simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, hh, Value.ofLit] at hrun
    cases (Prod.mk.inj hrun).1
  · have hs := hsv w hh
    cases w with
    | int n =>
      obtain ⟨h0, h1⟩ := hs
      refine ⟨_, n.toNat, rfl, ?_, by omega, ?_⟩
      · have hd := valueToScalar_int n.toNat
        rwa [Int.toNat_of_nonneg h0] at hd
      · rw [denote'_forFold_var_run bi fuel i h lo body env n hh] at hrun
        rwa [Int.toNat_of_nonneg h0]
    | uint wd n =>
      refine ⟨_, n, rfl, valueToScalar_uint wd n, hs, ?_⟩
      rw [_root_.Hax.denote'_forFold_lit_var_uint bi fuel i h lo body env wd n hh] at hrun
      exact hrun
    | bool b =>
      simp only [denote'] at hrun
      simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, StateT.pure, hh, Value.ofLit] at hrun
      cases (Prod.mk.inj hrun).1
    | unit =>
      simp only [denote'] at hrun
      simp [StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, StateT.pure, hh, Value.ofLit] at hrun
      cases (Prod.mk.inj hrun).1
    | _ => exact (show False from hs).elim

/-- The arguments of a call on variables evaluate, when they evaluate to values, to the
    values of the variables, and leave the environment unchanged. -/
theorem denoteArgs'_vars_inv (args : List ImpExpr) (hargs : exitArgsOk args = true)
    (env e1 : Env) (o : Option (List Value))
    (h : (_root_.Hax.denoteArgs' bi fuel args).run env = (o, e1)) :
    e1 = env ∧ ∀ vals, o = some vals →
      List.Forall₂ (fun a v => ∃ x, a = ImpExpr.var x ∧ env x = some v) args vals := by
  induction args generalizing o e1 with
  | nil =>
    rw [denoteArgs'_nil_run] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rfl, fun vals hv => by cases hv; exact List.Forall₂.nil⟩
  | cons a as ih =>
    cases a with
    | var x =>
      simp only [exitArgsOk, Bool.and_eq_true] at hargs
      rw [denoteArgs'_cons_run, denote'_var_run] at h
      cases hx : env x with
      | none =>
        rw [hx] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        exact ⟨rfl, fun vals hv => by cases hv⟩
      | some v =>
        rw [hx] at h
        rcases hr : (_root_.Hax.denoteArgs' bi fuel as).run env with ⟨o', e1'⟩
        obtain ⟨he, hF⟩ := ih hargs.2 e1' o' hr
        cases v with
        | controlFlow k u =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact ⟨rfl, fun vals hv => by cases hv⟩
        | _ =>
          simp only [hr] at h
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          refine ⟨he, fun vals hv => ?_⟩
          rcases o' with _ | vs
          · cases hv
          · simp only [Option.map_some, Option.some.injEq] at hv
            subst hv
            exact List.Forall₂.cons ⟨x, rfl, hx⟩ (hF vs rfl)
    | _ => simp [exitArgsOk] at hargs

/-- A run of `let n = f(args); body` on variable arguments, over a builtin table
    returning no control-flow value, that ends in a value: the arguments evaluate to the
    values of the variables, the builtin returns `r`, and the body runs from the
    environment extended by `n ↦ r`. -/
theorem letBind_app_inv (hplain : _root_.Hax.ContinueFlag.BuiltinsPlain bi) (n f : String)
    (args : List ImpExpr) (body : ImpExpr) (hargs : exitArgsOk args = true)
    (env env' : Env) (o : Outcome)
    (hrun : (denote' bi fuel (.letBind n (.app f args) body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) :
    ∃ vals r, List.Forall₂ (fun a v => ∃ x, a = ImpExpr.var x ∧ env x = some v) args vals ∧
      bi f vals = some r ∧ (denote' bi fuel body).run (env.extend n r) = (o, env') := by
  rcases hA : (_root_.Hax.denoteArgs' bi fuel args).run env with ⟨oa, e1⟩
  obtain ⟨rfl, hF⟩ := denoteArgs'_vars_inv bi fuel args hargs env e1 oa hA
  have happ := denote'_app_run bi fuel f args e1
  rw [hA] at happ
  rcases oa with _ | vals
  · rw [denote'_letBind_run_nonval bi fuel n _ body e1 e1 _ happ (fun v h => by cases h)] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨_, h⟩ := hval; cases h
  · cases hbi : bi f vals with
    | none =>
      simp only [hbi] at happ
      rw [denote'_letBind_run_nonval bi fuel n _ body e1 e1 _ happ (fun v h => by cases h)] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    | some r =>
      simp only [hbi] at happ
      rw [denote'_letBind_run_val bi fuel n _ body e1 e1 r happ (hplain f vals r hbi)] at hrun
      exact ⟨vals, r, hF vals rfl, hbi, hrun⟩

/-- The arguments `[v, l]` of a call on a variable and a literal evaluate, when they
    evaluate to values, to the value of `v` and the value of `l`, and leave the environment
    unchanged. -/
theorem denoteArgs'_varLit_inv (v : String) (l : ImpLit) (env e1 : Env)
    (o : Option (List Value))
    (h : (_root_.Hax.denoteArgs' bi fuel [.var v, .lit l]).run env = (o, e1)) :
    e1 = env ∧ ∀ vals, o = some vals → ∃ vv, env v = some vv ∧ vals = [vv, Value.ofLit l] := by
  rw [denoteArgs'_cons_run, denote'_var_run] at h
  cases hx : env v with
  | none =>
    rw [hx] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact ⟨rfl, fun vals hv => by cases hv⟩
  | some vv =>
    rw [hx] at h
    have hl : (_root_.Hax.denoteArgs' bi fuel [.lit l]).run env = (some [Value.ofLit l], env) := by
      rw [denoteArgs'_cons_run]
      have h1 : (denote' bi fuel (.lit l)).run env = (.val (Value.ofLit l), env) := by
        simp only [denote']; rfl
      rw [h1]
      cases l <;> simp [denoteArgs'_nil_run, Value.ofLit]
    cases vv with
    | controlFlow k u =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨rfl, fun vals hv => by cases hv⟩
    | _ =>
      simp only [hl, Option.map_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨rfl, fun vals hv => ⟨_, rfl, (Option.some.inj hv).symm⟩⟩

private theorem stateM_bind_run' {σ α β : Type} (m : StateM σ α) (f : α → StateM σ β)
    (s : σ) : (m >>= f) s = (f (m s).1) (m s).2 := rfl

private theorem stateM_get_run' {σ : Type} (s : σ) : (get : StateM σ σ) s = (s, s) := rfl

/-- A `match` on an `Option` whose scrutinee evaluates to `Some w`: the `Some` arm runs with
    the payload bound. -/
theorem denote'_optMatch_some {s t e : ImpExpr} {p : String} {env env1 : Env} {w : Value}
    (hs : denote' bi fuel s env = (.val (.option (some w)), env1)) :
    denote' bi fuel (.match_ s [(.somePat (.varPat p), t), (.nonePat, e)]) env =
      denote' bi fuel t (env1.extend p w) := by
  simp only [denote', stateM_bind_run', hs, _root_.Hax.denoteMatchArms',
    stateM_get_run', _root_.Hax.matchPat]
  rfl

theorem denote'_optMatch_none {s t e : ImpExpr} {p : String} {env env1 : Env}
    (hs : denote' bi fuel s env = (.val (.option none), env1)) :
    denote' bi fuel (.match_ s [(.somePat (.varPat p), t), (.nonePat, e)]) env =
      denote' bi fuel e env1 := by
  simp only [denote', stateM_bind_run', hs, _root_.Hax.denoteMatchArms',
    stateM_get_run', _root_.Hax.matchPat]
  rfl

theorem denote'_optMatchR_some {s t e : ImpExpr} {p : String} {env env1 : Env} {w : Value}
    (hs : denote' bi fuel s env = (.val (.option (some w)), env1)) :
    denote' bi fuel (.match_ s [(.nonePat, e), (.somePat (.varPat p), t)]) env =
      denote' bi fuel t (env1.extend p w) := by
  simp only [denote', stateM_bind_run', hs, _root_.Hax.denoteMatchArms',
    stateM_get_run', _root_.Hax.matchPat]
  rfl

theorem denote'_optMatchR_none {s t e : ImpExpr} {p : String} {env env1 : Env}
    (hs : denote' bi fuel s env = (.val (.option none), env1)) :
    denote' bi fuel (.match_ s [(.nonePat, e), (.somePat (.varPat p), t)]) env =
      denote' bi fuel e env1 := by
  simp only [denote', stateM_bind_run', hs, _root_.Hax.denoteMatchArms',
    stateM_get_run', _root_.Hax.matchPat]
  rfl

/-- A `match` whose scrutinee does not evaluate to a value ends in that outcome. -/
theorem denote'_match_nonval {s : ImpExpr} {arms : List (_root_.Hax.ImpPat × ImpExpr)}
    {env env1 : Env} {o : Outcome} (hs : denote' bi fuel s env = (o, env1))
    (ho : ∀ v, o ≠ .val v) : denote' bi fuel (.match_ s arms) env = (o, env1) := by
  simp only [denote', stateM_bind_run', hs]
  rcases o with v | _ | _ | _ | _
  · exact absurd rfl (ho v)
  all_goals rfl

/-- A run of `let n = repeat(v, l); body` with a literal count, over a builtin table
    returning no control-flow value, that ends in a value: `v` holds `vv`, the builtin
    returns `r` on `vv` and the value of `l`, and the body runs from the environment
    extended by `n ↦ r`. -/
theorem letBind_repeat_inv (hplain : _root_.Hax.ContinueFlag.BuiltinsPlain bi) (n v : String)
    (l : ImpLit) (body : ImpExpr) (env env' : Env) (o : Outcome)
    (hrun : (denote' bi fuel (.letBind n (.app "repeat" [.var v, .lit l]) body)).run env =
      (o, env'))
    (hval : ∃ w, o = .val w) :
    ∃ vv r, env v = some vv ∧ bi "repeat" [vv, Value.ofLit l] = some r ∧
      (denote' bi fuel body).run (env.extend n r) = (o, env') := by
  rcases hA : (_root_.Hax.denoteArgs' bi fuel [.var v, .lit l]).run env with ⟨oa, e1⟩
  obtain ⟨rfl, hF⟩ := denoteArgs'_varLit_inv bi fuel v l env e1 oa hA
  have happ := denote'_app_run bi fuel "repeat" [.var v, .lit l] e1
  rw [hA] at happ
  rcases oa with _ | vals
  · rw [denote'_letBind_run_nonval bi fuel n _ body e1 e1 _ happ (fun v h => by cases h)] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    obtain ⟨_, h⟩ := hval; cases h
  · obtain ⟨vv, hvv, rfl⟩ := hF _ rfl
    cases hbi : bi "repeat" [vv, Value.ofLit l] with
    | none =>
      simp only [hbi] at happ
      rw [denote'_letBind_run_nonval bi fuel n _ body e1 e1 _ happ (fun v h => by cases h)] at hrun
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
      obtain ⟨_, h⟩ := hval; cases h
    | some r =>
      simp only [hbi] at happ
      rw [denote'_letBind_run_val bi fuel n _ body e1 e1 r happ (hplain _ _ r hbi)] at hrun
      exact ⟨vv, r, hvv, hbi, hrun⟩

theorem denote'_forFoldRev_lit_run (i : String) (lo hi : Int) (body : ImpExpr) (env : Env) :
    (denote' bi fuel (.forFoldRev i (.lit (.int lo)) (.lit (.int hi)) body)).run env =
      (_root_.Hax.denoteForLoopRev' bi fuel i lo hi body).run env := by
  simp only [denote']; rfl

theorem denoteForLoopRev'_ge_run (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : hi ≤ lo) :
    (_root_.Hax.denoteForLoopRev' bi fuel i lo hi body).run env = (.val .unit, env) := by
  rw [_root_.Hax.denoteForLoopRev', if_pos h]; rfl

theorem denoteForLoopRev'_zero_run (i : String) (lo hi : Int) (body : ImpExpr) (env : Env)
    (h : lo < hi) :
    (_root_.Hax.denoteForLoopRev' bi 0 i lo hi body).run env = (.err "out of fuel", env) := by
  rw [_root_.Hax.denoteForLoopRev', if_neg (not_le.mpr h), if_pos rfl]; rfl

theorem denoteForLoopRev'_succ_run (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr)
    (env : Env) (h : lo < hi) :
    (_root_.Hax.denoteForLoopRev' bi (n + 1) i lo hi body).run env =
      match (denote' bi (n + 1) body).run (env.extend i (.int (hi - 1))) with
      | (.val (.controlFlow true v), e2) => (.val v, e2)
      | (.val (.controlFlow false _), e2) =>
          (_root_.Hax.denoteForLoopRev' bi n i lo (hi - 1) body).run e2
      | (.val _, e2) => (_root_.Hax.denoteForLoopRev' bi n i lo (hi - 1) body).run e2
      | (o, e2) => (o, e2) := by
  rw [_root_.Hax.denoteForLoopRev', if_neg (not_le.mpr h)]
  simp only [Nat.add_one_ne_zero, if_false, StateT.run, bind, StateT.bind, pure, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Nat.add_sub_cancel]
  rcases (denote' bi (n + 1) body) (env.extend i (.int (hi - 1))) with ⟨o2, e2⟩
  rcases o2 with v2 | _ | _ | _ | _ <;> try rfl
  cases v2 with
  | controlFlow k w => cases k <;> rfl
  | _ => rfl

theorem denoteForLoopRev'_succ_break (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr)
    (env e2 : Env) (w : Value) (h : lo < hi)
    (hb : (denote' bi (n + 1) body).run (env.extend i (.int (hi - 1))) =
      (.val (.controlFlow true w), e2)) :
    (_root_.Hax.denoteForLoopRev' bi (n + 1) i lo hi body).run env = (.val w, e2) := by
  rw [denoteForLoopRev'_succ_run bi n i lo hi body env h, hb]

theorem denoteForLoopRev'_succ_iterate (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr)
    (env e2 : Env) (w : Value) (h : lo < hi)
    (hb : (denote' bi (n + 1) body).run (env.extend i (.int (hi - 1))) = (.val w, e2))
    (hw : w.isControlFlow = false) :
    (_root_.Hax.denoteForLoopRev' bi (n + 1) i lo hi body).run env =
      (_root_.Hax.denoteForLoopRev' bi n i lo (hi - 1) body).run e2 := by
  rw [denoteForLoopRev'_succ_run bi n i lo hi body env h, hb]
  cases w <;> first | rfl | simp at hw

theorem denoteForLoopRev'_succ_nonval (n : Nat) (i : String) (lo hi : Int) (body : ImpExpr)
    (env e2 : Env) (o : Outcome) (h : lo < hi)
    (hb : (denote' bi (n + 1) body).run (env.extend i (.int (hi - 1))) = (o, e2))
    (ho : ∀ v, o ≠ .val v) :
    (_root_.Hax.denoteForLoopRev' bi (n + 1) i lo hi body).run env = (o, e2) := by
  rw [denoteForLoopRev'_succ_run bi n i lo hi body env h, hb]
  cases o with
  | val v => exact absurd rfl (ho v)
  | _ => rfl

end SourceStepsT

/-! ### Counted-loop bounds read at run time -/

/-- The value of a literal of `exitLitOk` is a scalar word. -/
theorem exitLitOk_scalarValN {l : ImpLit} (hl : exitLitOk l = true) :
    ScalarValN (Value.ofLit l) := by
  cases l with
  | uintLit w m =>
    show m % w.modulus < 2 ^ 64
    cases w <;> simp only [IntWidth.modulus, IntWidth.bits] <;> first
      | omega | (simp only [exitLitOk] at hl; exact absurd hl (by decide))
  | int z =>
    simp only [exitLitOk, Bool.and_eq_true, decide_eq_true_eq] at hl
    exact hl
  | bool b => trivial
  | unit => trivial
  | _ => simp [exitLitOk] at hl

theorem scalarOpExprT_isSome_any (op : String) (a b a' b' : SExpr) :
    (scalarOpExprT op a b).isSome = (scalarOpExprT op a' b').isSome := by
  unfold scalarOpExprT
  split <;> try rfl
  rcases widthOpOf op with _ | ⟨w, o⟩ <;> rfl

/-- The value of a scalar operation on two scalar expressions is `scalarOpNatT` of their
    values. -/
theorem scalarOpExprT_evalState_any {op : String} {a b se : SExpr} {rs : RustState}
    (h : scalarOpExprT op a b = some se) :
    se.evalState rs = scalarOpNatT op (a.evalState rs) (b.evalState rs) := by
  have hc := scalarOpExprT_congr op (a := a) (b := b)
    (a' := .SLit (a.evalState rs)) (b' := .SLit (b.evalState rs)) (rs := rs) (σ := fun _ => 0)
    rfl rfl
  rw [h] at hc
  unfold scalarOpNatT
  rcases h' : scalarOpExprT op (.SLit (a.evalState rs)) (.SLit (b.evalState rs)) with _ | se'
  · rw [h'] at hc; cases hc
  · rw [h'] at hc
    simpa using hc

theorem denoteArgs'_cons_val {bi : Builtins} {fuel : Nat} {e : ImpExpr} {es : List ImpExpr}
    {env e1 : Env} {v : Value} (h : (denote' bi fuel e).run env = (.val v, e1))
    (hv : v.isControlFlow = false) :
    (_root_.Hax.denoteArgs' bi fuel (e :: es)).run env =
      (((_root_.Hax.denoteArgs' bi fuel es).run e1).1.map (v :: ·),
        ((_root_.Hax.denoteArgs' bi fuel es).run e1).2) := by
  rw [_root_.Hax.ContinueFlag.args_cons_run, h]
  cases v <;> first | rfl | simp at hv

theorem denoteArgs'_cons_nonval {bi : Builtins} {fuel : Nat} {e : ImpExpr} {es : List ImpExpr}
    {env e1 : Env} {o : Outcome} (h : (denote' bi fuel e).run env = (o, e1))
    (ho : ∀ v, o = .val v → v.isControlFlow = true) :
    (_root_.Hax.denoteArgs' bi fuel (e :: es)).run env = (none, e1) := by
  rw [_root_.Hax.ContinueFlag.args_cons_run, h]
  rcases o with v | _ | _ | _ | _
  · have := ho v rfl
    cases v <;> first | rfl | simp at this
  all_goals rfl

/-- **A bound of `boundSE` evaluates to its scalar expression.**  From an environment
    agreeing with `rs` under `A`, a run of `e` leaves the environment unchanged, and a value
    it returns is a scalar word decoding to the value of `boundSE A e` in `rs`, when the
    table computes the scalar operations (`ScalarOpsSoundT`). -/
theorem boundSE_sim {bi : Builtins} {br : ValueTowerBridge} (hS : ScalarOpsSoundT bi)
    {A : ExitTowers} {rs : RustState} {env : Env} (hag : envAgreesT br A env rs) (fuel : Nat)
    (e : ImpExpr) : ∀ {se : SExpr}, boundSE A e = some se → ∀ {o : Outcome} {env' : Env},
      (denote' bi fuel e).run env = (o, env') →
      env' = env ∧ ∀ v, o = .val v → ScalarValN v ∧ valueToScalar v = some (se.evalState rs) := by
  induction e using ImpExpr.ind
  case lit l =>
    intro se hse o env' hrun
    rw [_root_.Hax.ContinueFlag.lit_run] at hrun
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
    simp only [boundSE] at hse
    split at hse
    · rename_i hl
      obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp hse
      refine ⟨rfl, fun v hv => ?_⟩
      cases hv
      exact ⟨exitLitOk_scalarValN hl, by simpa [SExpr.evalState] using hk⟩
    · cases hse
  case var x =>
    intro se hse o env' hrun
    simp only [boundSE] at hse
    split at hse
    · rename_i hx
      simp only [Option.some.injEq] at hse
      subst hse
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hx
      rw [_root_.Hax.ContinueFlag.var_run] at hrun
      rcases hv : env x with _ | w
      · rw [hv] at hrun; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
        exact ⟨rfl, fun v h => by cases h⟩
      · rw [hv] at hrun; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
        refine ⟨rfl, fun v h => ?_⟩
        cases h
        have := envAgreesT_scalar hag hx.1 (by simpa [exitSc] using hx.2) hv
        simpa [SExpr.evalState] using this
    · cases hse
  case app op args ih =>
    intro se hse o env' hrun
    match args, ih, hse with
    | [a, b], ih, hse =>
      simp only [boundSE] at hse
      rcases hsa : boundSE A a with _ | sa
      · rw [hsa] at hse; cases hse
      rcases hsb : boundSE A b with _ | sb
      · rw [hsa, hsb] at hse; cases hse
      rw [hsa, hsb] at hse
      simp only at hse
      rw [_root_.Hax.ContinueFlag.app_run] at hrun
      rcases hra : (denote' bi fuel a).run env with ⟨oa, ea⟩
      obtain ⟨hea, hva⟩ := ih a (by simp) hsa hra
      subst hea
      rcases hrb : (denote' bi fuel b).run ea with ⟨ob, eb⟩
      obtain ⟨heb, hvb⟩ := ih b (by simp) hsb hrb
      subst heb
      by_cases hoa : ∃ va, oa = .val va
      · obtain ⟨va, rfl⟩ := hoa
        obtain ⟨hsva, hdva⟩ := hva va rfl
        rw [denoteArgs'_cons_val hra (ScalarValN.not_cf hsva)] at hrun
        by_cases hob : ∃ vb, ob = .val vb
        · obtain ⟨vb, rfl⟩ := hob
          obtain ⟨hsvb, hdvb⟩ := hvb vb rfl
          rw [denoteArgs'_cons_val hrb (ScalarValN.not_cf hsvb),
            _root_.Hax.ContinueFlag.args_nil_run] at hrun
          simp only [Option.map_some] at hrun
          rcases hr : bi op [va, vb] with _ | r
          · rw [hr] at hrun; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
            exact ⟨rfl, fun v h => by cases h⟩
          · rw [hr] at hrun; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
            refine ⟨rfl, fun v h => ?_⟩
            cases h
            have hsome : (scalarOpExprT op (.SVar "a") (.SVar "b")).isSome = true := by
              rw [scalarOpExprT_isSome_any op _ _ sa sb, hse]; rfl
            obtain ⟨h1, h2⟩ := hS op va vb r _ _ hsome hsva hsvb hdva hdvb hr
            exact ⟨h1, by rw [h2, scalarOpExprT_evalState_any hse]⟩
        · rw [denoteArgs'_cons_nonval (es := []) hrb (fun v h => absurd ⟨v, h⟩ hob)] at hrun
          simp only [Option.map_none] at hrun
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
          exact ⟨rfl, fun v h => by cases h⟩
      · rw [denoteArgs'_cons_nonval hra (fun v h => absurd ⟨v, h⟩ hoa)] at hrun
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
        exact ⟨rfl, fun v h => by cases h⟩
    | [], _, hse => simp [boundSE] at hse
    | [_], _, hse => simp [boundSE] at hse
    | _ :: _ :: _ :: _, _, hse => simp [boundSE] at hse
  all_goals (intro se hse; simp [boundSE] at hse)

theorem valueToScalar_uint_eq {w : IntWidth} {n k : Nat}
    (h : valueToScalar (.uint w n) = some k) : n = k := by
  simpa [valueToScalar] using h

theorem valueToScalar_int_eq {n : Int} {k : Nat} (h : valueToScalar (.int n) = some k) :
    n = (k : Int) := by
  simp only [valueToScalar] at h
  split at h
  · simp only [Option.some.injEq] at h; omega
  · cases h

theorem ScalarValN.lt_of_toScalar {v : Value} {k : Nat} (h : ScalarValN v)
    (hk : valueToScalar v = some k) : k < 2 ^ 64 := by
  rcases h.cases with ⟨w, n, rfl, hn⟩ | ⟨b, rfl⟩ | ⟨n, rfl, h0, hn⟩ | rfl
  · rw [valueToScalar_uint] at hk; cases hk; exact hn
  · cases b <;> simp [valueToScalar] at hk <;> omega
  · simp only [valueToScalar, if_pos h0, Option.some.injEq] at hk; omega
  · simp [valueToScalar] at hk; omega

/-- The lower bounds of `loBoundSE`: a literal, or a variable other than the counter that
    the body does not bind. -/
theorem loBoundSE_cases {A : ExitTowers} {i : String} {body lo : ImpExpr} {loE : SExpr}
    (h : loBoundSE A i body lo = some loE) :
    (∃ k, loE = .SLit k) ∨
      (∃ x, lo = .var x ∧ loE = .SVar x ∧ x ≠ i ∧
        _root_.Hax.InlineLocalClosures.frameOk (fun _ => true) (fun n => n != x)
          (fun _ => true) body = true) := by
  cases lo with
  | lit l =>
    simp only [loBoundSE, boundSE] at h
    split at h
    · obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.mp h
      exact Or.inl ⟨k, rfl⟩
    · cases h
  | var x =>
    simp only [loBoundSE] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      simp only [boundSE] at h
      split at h
      · simp only [Option.some.injEq] at h
        exact Or.inr ⟨x, rfl, h.symm, hc.1, hc.2⟩
      · cases h
    · cases h
  | _ => simp [loBoundSE] at h

/-- The bounds `boundSE` accepts: a literal, a variable, or a call on two arguments. -/
theorem boundSE_shape {A : ExitTowers} {e : ImpExpr} {se : SExpr} (h : boundSE A e = some se) :
    (∃ l, e = .lit l) ∨ (∃ x, e = .var x) ∨ (∃ f a b, e = .app f [a, b]) := by
  cases e with
  | lit l => exact Or.inl ⟨l, rfl⟩
  | var x => exact Or.inr (Or.inl ⟨x, rfl⟩)
  | app f args =>
    match args, h with
    | [a, b], _ => exact Or.inr (Or.inr ⟨f, a, b, rfl⟩)
    | [], h | [_], h | _ :: _ :: _ :: _, h => simp [boundSE] at h
  | _ => simp [boundSE] at h

theorem loBoundSE_boundSE {A : ExitTowers} {i : String} {body lo : ImpExpr} {loE : SExpr}
    (h : loBoundSE A i body lo = some loE) : boundSE A lo = some loE := by
  cases lo with
  | lit l => exact h
  | var x =>
    simp only [loBoundSE] at h
    split at h
    · exact h
    · cases h
  | _ => simp [loBoundSE] at h

/-- A `forFoldReturn` whose bounds evaluate, leaving the environment unchanged, to scalar
    words decoding to `L` and `H` runs as `denoteForLoop'Return` from `L` to `H`. -/
theorem denote'_forFoldReturn_scalar_bounds {bi : Builtins} {fuel : Nat} {i : String}
    {lo hi body : ImpExpr} {env env' : Env} {o : Outcome} {vlo vhi : Value} {L H : Nat}
    (hlo : (denote' bi fuel lo).run env = (.val vlo, env))
    (hhi : (denote' bi fuel hi).run env = (.val vhi, env))
    (hslo : ScalarValN vlo) (hshi : ScalarValN vhi)
    (hL : valueToScalar vlo = some L) (hH : valueToScalar vhi = some H)
    (hrun : (denote' bi fuel (.forFoldReturn i lo hi body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) :
    (_root_.Hax.denoteForLoop'Return bi fuel i L H body).run env = (o, env') := by
  obtain ⟨u, rfl⟩ := hval
  have hlo' : denote' bi fuel lo env = (.val vlo, env) := hlo
  have hhi' : denote' bi fuel hi env = (.val vhi, env) := hhi
  have hrun' : denote' bi fuel (.forFoldReturn i lo hi body) env = (.val u, env') := hrun
  rcases hslo.cases with ⟨w, n, rfl, _⟩ | ⟨b, rfl⟩ | ⟨n, rfl, h0, _⟩ | rfl <;>
  rcases hshi.cases with ⟨w', n', rfl, _⟩ | ⟨b', rfl⟩ | ⟨n', rfl, h0', _⟩ | rfl <;>
    simp only [denote', _root_.Hax.Ascent.stateM_bind_apply, hlo', hhi'] at hrun' <;>
    first
    | (have := congrArg Prod.fst hrun'; simp [pure, StateT.pure] at this; done)
    | (obtain rfl := valueToScalar_uint_eq hL; obtain rfl := valueToScalar_uint_eq hH; exact hrun')
    | (obtain rfl := valueToScalar_int_eq hL; obtain rfl := valueToScalar_uint_eq hH; exact hrun')
    | (obtain rfl := valueToScalar_uint_eq hL; obtain rfl := valueToScalar_int_eq hH; exact hrun')
    | (obtain rfl := valueToScalar_int_eq hL; obtain rfl := valueToScalar_int_eq hH; exact hrun')

/-- `denote'_forFoldReturn_scalar_bounds` for `forFold`. -/
theorem denote'_forFold_scalar_bounds {bi : Builtins} {fuel : Nat} {i : String}
    {lo hi body : ImpExpr} {env env' : Env} {o : Outcome} {vlo vhi : Value} {L H : Nat}
    (hlo : (denote' bi fuel lo).run env = (.val vlo, env))
    (hhi : (denote' bi fuel hi).run env = (.val vhi, env))
    (hslo : ScalarValN vlo) (hshi : ScalarValN vhi)
    (hL : valueToScalar vlo = some L) (hH : valueToScalar vhi = some H)
    (hrun : (denote' bi fuel (.forFold i lo hi body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) :
    (_root_.Hax.denoteForLoop' bi fuel i L H body).run env = (o, env') := by
  obtain ⟨u, rfl⟩ := hval
  have hlo' : denote' bi fuel lo env = (.val vlo, env) := hlo
  have hhi' : denote' bi fuel hi env = (.val vhi, env) := hhi
  have hrun' : denote' bi fuel (.forFold i lo hi body) env = (.val u, env') := hrun
  rcases hslo.cases with ⟨w, n, rfl, _⟩ | ⟨b, rfl⟩ | ⟨n, rfl, h0, _⟩ | rfl <;>
  rcases hshi.cases with ⟨w', n', rfl, _⟩ | ⟨b', rfl⟩ | ⟨n', rfl, h0', _⟩ | rfl <;>
    simp only [denote', _root_.Hax.Ascent.stateM_bind_apply, hlo', hhi'] at hrun' <;>
    first
    | (have := congrArg Prod.fst hrun'; simp [pure, StateT.pure] at this; done)
    | (obtain rfl := valueToScalar_uint_eq hL; obtain rfl := valueToScalar_uint_eq hH; exact hrun')
    | (obtain rfl := valueToScalar_int_eq hL; obtain rfl := valueToScalar_uint_eq hH; exact hrun')
    | (obtain rfl := valueToScalar_uint_eq hL; obtain rfl := valueToScalar_int_eq hH; exact hrun')
    | (obtain rfl := valueToScalar_int_eq hL; obtain rfl := valueToScalar_int_eq hH; exact hrun')

/-- A run of a `forFoldReturn` to a value whose bounds evaluate as `boundSE_sim` states,
    to scalar words decoding to `L` and `H`, runs as `denoteForLoop'Return` from `L` to
    `H`, with `H < 2 ^ 64`, and its bounds evaluate to values. -/
theorem denote'_forFoldReturn_pure_bounds {bi : Builtins} {fuel : Nat} {i : String}
    {lo hi body : ImpExpr} {env env' : Env} {o : Outcome} {L H : Nat}
    (hlo : ∀ {o e}, (denote' bi fuel lo).run env = (o, e) →
      e = env ∧ ∀ v, o = .val v → ScalarValN v ∧ valueToScalar v = some L)
    (hhi : ∀ {o e}, (denote' bi fuel hi).run env = (o, e) →
      e = env ∧ ∀ v, o = .val v → ScalarValN v ∧ valueToScalar v = some H)
    (hrun : (denote' bi fuel (.forFoldReturn i lo hi body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) :
    (_root_.Hax.denoteForLoop'Return bi fuel i L H body).run env = (o, env') ∧ H < 2 ^ 64 ∧
      ∃ vlo vhi, (denote' bi fuel lo).run env = (.val vlo, env) ∧
        (denote' bi fuel hi).run env = (.val vhi, env) := by
  obtain ⟨u, rfl⟩ := hval
  rcases hrl : (denote' bi fuel lo).run env with ⟨olo, elo⟩
  obtain ⟨rfl, hvl⟩ := hlo hrl
  rcases hrh : (denote' bi fuel hi).run elo with ⟨ohi, ehi⟩
  obtain ⟨rfl, hvh⟩ := hhi hrh
  have hlo' : denote' bi fuel lo ehi = (olo, ehi) := hrl
  have hhi' : denote' bi fuel hi ehi = (ohi, ehi) := hrh
  have hrun' : denote' bi fuel (.forFoldReturn i lo hi body) ehi = (.val u, env') := hrun
  cases olo with
  | val vlo =>
    obtain ⟨hsl, hdl⟩ := hvl vlo rfl
    cases ohi with
    | val vhi =>
      obtain ⟨hsh, hdh⟩ := hvh vhi rfl
      exact ⟨denote'_forFoldReturn_scalar_bounds hrl hrh hsl hsh hdl hdh hrun ⟨u, rfl⟩,
        hsh.lt_of_toScalar hdh, vlo, vhi, rfl, rfl⟩
    | _ =>
      rcases hsl.cases with ⟨w, n, rfl, _⟩ | ⟨b, rfl⟩ | ⟨n, rfl, _, _⟩ | rfl <;>
        simp only [denote', _root_.Hax.Ascent.stateM_bind_apply, hlo', hhi'] at hrun' <;>
        (have := congrArg Prod.fst hrun'; simp [pure, StateT.pure] at this)
  | _ =>
    simp only [denote', _root_.Hax.Ascent.stateM_bind_apply, hlo'] at hrun'
    have := congrArg Prod.fst hrun'; simp [pure, StateT.pure] at this

/-- `denote'_forFoldReturn_pure_bounds` for `forFold`. -/
theorem denote'_forFold_pure_bounds {bi : Builtins} {fuel : Nat} {i : String}
    {lo hi body : ImpExpr} {env env' : Env} {o : Outcome} {L H : Nat}
    (hlo : ∀ {o e}, (denote' bi fuel lo).run env = (o, e) →
      e = env ∧ ∀ v, o = .val v → ScalarValN v ∧ valueToScalar v = some L)
    (hhi : ∀ {o e}, (denote' bi fuel hi).run env = (o, e) →
      e = env ∧ ∀ v, o = .val v → ScalarValN v ∧ valueToScalar v = some H)
    (hrun : (denote' bi fuel (.forFold i lo hi body)).run env = (o, env'))
    (hval : ∃ v, o = .val v) :
    (_root_.Hax.denoteForLoop' bi fuel i L H body).run env = (o, env') ∧ H < 2 ^ 64 ∧
      ∃ vlo vhi, (denote' bi fuel lo).run env = (.val vlo, env) ∧
        (denote' bi fuel hi).run env = (.val vhi, env) := by
  obtain ⟨u, rfl⟩ := hval
  rcases hrl : (denote' bi fuel lo).run env with ⟨olo, elo⟩
  obtain ⟨rfl, hvl⟩ := hlo hrl
  rcases hrh : (denote' bi fuel hi).run elo with ⟨ohi, ehi⟩
  obtain ⟨rfl, hvh⟩ := hhi hrh
  have hlo' : denote' bi fuel lo ehi = (olo, ehi) := hrl
  have hhi' : denote' bi fuel hi ehi = (ohi, ehi) := hrh
  have hrun' : denote' bi fuel (.forFold i lo hi body) ehi = (.val u, env') := hrun
  cases olo with
  | val vlo =>
    obtain ⟨hsl, hdl⟩ := hvl vlo rfl
    cases ohi with
    | val vhi =>
      obtain ⟨hsh, hdh⟩ := hvh vhi rfl
      exact ⟨denote'_forFold_scalar_bounds hrl hrh hsl hsh hdl hdh hrun ⟨u, rfl⟩,
        hsh.lt_of_toScalar hdh, vlo, vhi, rfl, rfl⟩
    | _ =>
      rcases hsl.cases with ⟨w, n, rfl, _⟩ | ⟨b, rfl⟩ | ⟨n, rfl, _, _⟩ | rfl <;>
        simp only [denote', _root_.Hax.Ascent.stateM_bind_apply, hlo', hhi'] at hrun' <;>
        (have := congrArg Prod.fst hrun'; simp [pure, StateT.pure] at this)
  | _ =>
    simp only [denote', _root_.Hax.Ascent.stateM_bind_apply, hlo'] at hrun'
    have := congrArg Prod.fst hrun'; simp [pure, StateT.pure] at this

/-- A variable lower bound `x` of `loBoundSE` is not the counter, and a run of the body
    that ends in a value leaves it unchanged (`frameOk`). -/
theorem loBoundSE_frame {bi : Builtins} {A : ExitTowers} {i : String} {body lo : ImpExpr}
    {x : String} (hlo : loBoundSE A i body lo = some (.SVar x)) :
    x ≠ i ∧ ∀ (fuel : Nat) (e e2 : Env) (w : Value),
      (denote' bi fuel body).run e = (.val w, e2) → e2 x = e x := by
  rcases loBoundSE_cases hlo with ⟨k', hk⟩ | ⟨y, -, hy, hyi, hfr⟩
  · cases hk
  · have hyx : y = x := by cases hy; rfl
    subst hyx
    refine ⟨hyi, fun fuel e e2 w hb => ?_⟩
    have H := _root_.Hax.InlineLocalClosures.denote'_frame (bi₁ := bi) (bi₂ := bi)
      (R := fun e₁ e₂ => e₁ = e₂ ∧ e₂ y = e y) id _ _ _
      (fun e₁ e₂ z hR _ => by rw [hR.1]; rfl)
      (fun e₁ e₂ n w' hR hn => by
        refine ⟨by rw [hR.1], ?_⟩
        have hn' : n ≠ y := by simpa using hn
        simp only [_root_.Hax.Env.extend]
        rw [if_neg (by simpa using hn'.symm)]
        exact hR.2)
      (fun _ _ => rfl) body hfr fuel _ _ ⟨rfl, rfl⟩ _ e2 hb (fun ⟨m, hm⟩ => by cases hm)
    obtain ⟨s₁, -, hs⟩ := H
    exact hs.2

/-- The lower bound of `loBoundSE` keeps its entry value `env x` over a trip of the body
    that ends in a value. -/
theorem loBound_keep {bi : Builtins} {A : ExitTowers} {i : String} {body lo : ImpExpr}
    {loE : SExpr} (hlo : loBoundSE A i body lo = some loE) (env : Env) :
    ∀ (fuel : Nat) (e1 e2 : Env) (w : Value) (k : Int),
      (∀ x, loE = .SVar x → e1 x = env x) →
      (denote' bi fuel body).run (e1.extend i (.int k)) = (.val w, e2) →
      (∀ x, loE = .SVar x → e2 x = env x) := by
  intro fuel e1 e2 w k hK hb x hx
  subst hx
  obtain ⟨hxi, hfr⟩ := loBoundSE_frame (bi := bi) hlo
  rw [hfr fuel _ e2 w hb]
  simp only [_root_.Hax.Env.extend]
  rw [if_neg (by simpa using hxi)]
  exact hK x rfl

/-- A counted loop whose bounds evaluate, leaving the environment unchanged, to scalar
    words, and whose run ends in a value, has bounds that are neither bools nor the unit. -/
theorem forFoldReturn_bounds_words {bi : Builtins} {fuel : Nat} {i : String}
    {lo hi body : ImpExpr} {env env' : Env} {u vlo vhi : Value}
    (hlo : (denote' bi fuel lo).run env = (.val vlo, env))
    (hhi : (denote' bi fuel hi).run env = (.val vhi, env))
    (hslo : ScalarValN vlo) (hshi : ScalarValN vhi)
    (hrun : (denote' bi fuel (.forFoldReturn i lo hi body)).run env = (.val u, env')) :
    (∀ b, vlo ≠ .bool b) ∧ vlo ≠ .unit ∧ (∀ b, vhi ≠ .bool b) ∧ vhi ≠ .unit := by
  have hlo' : denote' bi fuel lo env = (.val vlo, env) := hlo
  have hhi' : denote' bi fuel hi env = (.val vhi, env) := hhi
  have hrun' : denote' bi fuel (.forFoldReturn i lo hi body) env = (.val u, env') := hrun
  rcases hslo.cases with ⟨w, n, rfl, _⟩ | ⟨b, rfl⟩ | ⟨n, rfl, h0, _⟩ | rfl <;>
  rcases hshi.cases with ⟨w', n', rfl, _⟩ | ⟨b', rfl⟩ | ⟨n', rfl, h0', _⟩ | rfl <;>
    simp only [denote', _root_.Hax.Ascent.stateM_bind_apply, hlo', hhi'] at hrun' <;>
    first
    | (have := congrArg Prod.fst hrun'; simp [pure, StateT.pure] at this; done)
    | simp

/-- `forFoldReturn_bounds_words` for `forFold`. -/
theorem forFold_bounds_words {bi : Builtins} {fuel : Nat} {i : String}
    {lo hi body : ImpExpr} {env env' : Env} {u vlo vhi : Value}
    (hlo : (denote' bi fuel lo).run env = (.val vlo, env))
    (hhi : (denote' bi fuel hi).run env = (.val vhi, env))
    (hslo : ScalarValN vlo) (hshi : ScalarValN vhi)
    (hrun : (denote' bi fuel (.forFold i lo hi body)).run env = (.val u, env')) :
    (∀ b, vlo ≠ .bool b) ∧ vlo ≠ .unit ∧ (∀ b, vhi ≠ .bool b) ∧ vhi ≠ .unit := by
  have hlo' : denote' bi fuel lo env = (.val vlo, env) := hlo
  have hhi' : denote' bi fuel hi env = (.val vhi, env) := hhi
  have hrun' : denote' bi fuel (.forFold i lo hi body) env = (.val u, env') := hrun
  rcases hslo.cases with ⟨w, n, rfl, _⟩ | ⟨b, rfl⟩ | ⟨n, rfl, h0, _⟩ | rfl <;>
  rcases hshi.cases with ⟨w', n', rfl, _⟩ | ⟨b', rfl⟩ | ⟨n', rfl, h0', _⟩ | rfl <;>
    simp only [denote', _root_.Hax.Ascent.stateM_bind_apply, hlo', hhi'] at hrun' <;>
    first
    | (have := congrArg Prod.fst hrun'; simp [pure, StateT.pure] at this; done)
    | simp

/-- The lower bound `loE` read at the start of a trip, from a state agreeing with an
    environment in which a variable lower bound keeps its entry value `vlo`, is the value
    `L` it decodes to at loop entry. -/
theorem loBound_read {br : ValueTowerBridge} {A : ExitTowers} {i : String}
    {body lo : ImpExpr} {loE : SExpr} (hlo : loBoundSE A i body lo = some loE) {run : String}
    (hslot : exitRunSlot run = true) {env : Env} {vlo : Value} {L : Nat}
    (hvlo : ∀ x, lo = .var x → env x = some vlo)
    (hL : valueToScalar vlo = some L) (hLit : ∀ k, loE = .SLit k → k = L) :
    ∀ (e1 : Env) (rs : RustState) (j : Nat), (∀ x, loE = .SVar x → e1 x = env x) →
      envAgreesT br A e1 rs → loE.evalState (rsSetScalar (rsSetScalar rs run j) i 0) = L := by
  intro e1 rs j hK hag
  rcases loBoundSE_cases hlo with ⟨k, rfl⟩ | ⟨x, rfl, rfl, hxi, -⟩
  · exact hLit k rfl
  · have hb := loBoundSE_boundSE hlo
    simp only [boundSE] at hb
    split at hb
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      have hxr : x ≠ run := ne_of_reserved hc.1 (exitReserved_of_runSlot hslot)
      have he1 : e1 x = some vlo := (hK x rfl).trans (hvlo x rfl)
      have hd := (envAgreesT_scalar hag hc.1 (by simpa [exitSc] using hc.2) he1).2
      rw [hL] at hd
      simp only [SExpr.evalState, rsScalar_rsSetScalar, if_neg hxi, if_neg hxr]
      exact (Option.some.inj hd).symm
    · cases hb

/-! ## §10  The simulation statement and the translator's equations -/

/-- The simulation of `e` under the placement `A` and result placement `R`: from states
    agreeing under `A` with the exit flag `0`, a run of `denote'` ending in a value is
    matched by a run of `haxToLowCTKT A` ending in states agreeing under `A`; a command
    that cannot exit leaves the flag `0`. -/
def ExitSimTy (bi : Builtins) (N : Nat) (leafSpec : LeafSpec) (br : ValueTowerBridge)
    (A : ExitTowers) (R : ExitRes) (e : ImpExpr) : Prop :=
  ∀ (tl : Bool) (fl : Option String) (fuel : Nat) (env env' : Env) (o : Outcome)
    (rs : RustState) (c : LowCT) (x : Bool),
    exitSimOkT A R tl fl.isSome e = true → RunCtx fl →
    haxToLowCTKT A tl fl e = some (c, x) →
    (denote' bi fuel e).run env = (o, env') →
    (∃ v, o = .val v) →
    envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
    ∃ rs', RustExec N leafSpec c rs rs' ∧ envAgreesExitT br A R tl o env' rs' ∧
      (x = false → rs'.rsScalar exitRetName = 0)

section Equations

variable (A : ExitTowers)

theorem haxToLowCTKT_letBind_eq (tl : Bool) (fl : Option String) (n : String)
    (val body : ImpExpr) :
    haxToLowCTKT A tl fl (.letBind n val body) =
      match letHeadT A n val, haxToLowCTKT A tl fl body with
      | some k, some (bC, x) => some (k bC, x)
      | _, _ => none := by
  cases tl <;> cases fl <;> rfl

theorem haxToLowCTKT_seq_eq (tl : Bool) (fl : Option String) (a b : ImpExpr) :
    haxToLowCTKT A tl fl (.seq a b) =
      match haxToLowCTKT A false fl a, haxToLowCTKT A tl fl b with
      | some (aC, xa), some (bC, xb) =>
          some (if xa then .RSeq aC (exitGuard bC) else .RSeq aC bC, xa || xb)
      | _, _ => none := by
  cases tl <;> cases fl <;> rfl

theorem haxToLowCTKT_ifThenElse_eq (tl : Bool) (fl : Option String) (v : String)
    (t e : ImpExpr) (hv : exitSc A v = true) :
    haxToLowCTKT A tl fl (.ifThenElse (.var v) t e) =
      match haxToLowCTKT A tl fl t, haxToLowCTKT A tl fl e with
      | some (tC, xt), some (eC, xe) => some (.RIfNz v tC eC, xt || xe)
      | _, _ => none := by
  cases tl <;> cases fl <;> exact if_pos hv

theorem haxToLowCTKT_typeAscription_eq (tl : Bool) (fl : Option String) (e : ImpExpr)
    (ty : String) : haxToLowCTKT A tl fl (.typeAscription e ty) = haxToLowCTKT A tl fl e := by
  cases tl <;> cases fl <;> rfl

theorem haxToLowCTKT_whileFoldReturn_eq (fl : Option String) (c : String) (body : ImpExpr)
    (hc : exitSc A c = true) :
    haxToLowCTKT A false fl (.whileFoldReturn (.var c) body) =
      match haxToLowCTKT A false (some (exitRunName fl)) body with
      | some (bC, _) => some (exitLoop (exitRunName fl) c bC, true)
      | none => none := by
  cases fl <;> exact if_pos hc

theorem haxToLowCTKT_forFoldReturn_eq (fl : Option String) (i : String) (lo hi body : ImpExpr)
    (hi' : (exitSc A i && exitScRt A lo hi) = true) :
    haxToLowCTKT A false fl (.forFoldReturn i lo hi body) =
      match forBounds lo hi, forBoundsRt lo hi,
          haxToLowCTKT A false (some (exitRunName fl)) body with
      | some (l, h), _, some (bC, _) => some (exitForLoop (exitRunName fl) i l h bC, true)
      | none, some (l, h), some (bC, _) =>
          some (exitForLoopRt (exitRunName fl) i l h bC, true)
      | none, none, some (bC, _) =>
          (forBoundsV A i body lo hi).map fun p =>
            (exitForLoopV (exitRunName fl) i p.1 p.2 bC, true)
      | _, _, _ => none := by
  cases fl <;> exact if_pos hi'

theorem haxToLowCTKT_forFoldRevReturn_eq (fl : Option String) (i : String)
    (lo hi body : ImpExpr) (hi' : exitSc A i = true) :
    haxToLowCTKT A false fl (.forFoldRevReturn i lo hi body) =
      match forBounds lo hi, haxToLowCTKT A false (some (exitRunName fl)) body with
      | some (l, h), some (bC, _) => some (exitForLoopRev (exitRunName fl) i l h bC, true)
      | _, _ => none := by
  cases fl <;> exact if_pos hi'

theorem haxToLowCTKT_forFold_some_eq (r i : String) (lo hi body : ImpExpr)
    (hi' : (exitSc A i && exitScRt A lo hi) = true) :
    haxToLowCTKT A false (some r) (.forFold i lo hi body) =
      match forBounds lo hi, forBoundsRt lo hi,
          haxToLowCTKT A false (some (exitRunName (some r))) body with
      | some (l, h), _, some (bC, _) =>
          some (breakLoop (exitForLoop (exitRunName (some r)) i l h bC), false)
      | none, some (l, h), some (bC, _) =>
          some (breakLoop (exitForLoopRt (exitRunName (some r)) i l h bC), false)
      | none, none, some (bC, _) =>
          (forBoundsV A i body lo hi).map fun p =>
            (breakLoop (exitForLoopV (exitRunName (some r)) i p.1 p.2 bC), false)
      | _, _, _ => none := if_pos hi'

theorem haxToLowCTKT_forFoldRev_some_eq (r i : String) (lo hi body : ImpExpr)
    (hi' : exitSc A i = true) :
    haxToLowCTKT A false (some r) (.forFoldRev i lo hi body) =
      match forBounds lo hi, haxToLowCTKT A false (some (exitRunName (some r))) body with
      | some (l, h), some (bC, _) =>
          some (breakLoop (exitForLoopRev (exitRunName (some r)) i l h bC), false)
      | _, _ => none := if_pos hi'

theorem haxToLowCTKT_whileFold_some_eq (r c : String) (body : ImpExpr)
    (hc : exitSc A c = true) :
    haxToLowCTKT A false (some r) (.whileFold (.var c) body) =
      match haxToLowCTKT A false (some (exitRunName (some r))) body with
      | some (bC, _) => some (breakLoop (exitLoop (exitRunName (some r)) c bC), false)
      | none => none := if_pos hc

theorem haxToLowCTKT_cfBreak_eq (tl : Bool) (r : String) (p : ImpExpr)
    (hp : exitScE A p = true) :
    haxToLowCTKT A tl (some r) (.cfBreak p) = (exitStore p).map fun s => (s, true) := by
  cases tl <;> exact if_pos hp

end Equations

/-! ## §11  The reserved tower slots and the marshalling of call arguments -/

theorem exitReserved_call : exitReserved exitCallName = true := by decide

theorem exitReserved_marshal (x : String) : exitReserved (exitMarshalName x) = true := by
  unfold exitReserved exitMarshalName
  rw [String.toList_append, List.isPrefixOf_iff_prefix]
  exact List.IsPrefix.trans (by decide) (List.prefix_append _ _)

theorem exitMarshalName_inj {x y : String} (h : exitMarshalName x = exitMarshalName y) :
    x = y := by
  unfold exitMarshalName at h
  have h' := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at h'
  exact String.ext (List.append_cancel_left h')

theorem exitCallName_ne_marshal (x : String) : exitCallName ≠ exitMarshalName x := by
  intro h
  have h' := congrArg (fun s => s.toList.take 8) h
  simp only [exitMarshalName, String.toList_append] at h'
  rw [List.take_append_of_le_length (by decide)] at h'
  revert h'; decide

theorem ne_marshal_of_nonreserved {y : String} (hy : exitReserved y = false) (x : String) :
    y ≠ exitMarshalName x := ne_of_reserved hy (exitReserved_marshal x)

theorem rsSetTower_rsSetTower (rs : RustState) (x : String) (v w : Σ t, RustVal t) :
    rsSetTower (rsSetTower rs x v) x w = rsSetTower rs x w := by
  cases rs
  simp only [rsSetTower, RustState.mk.injEq, and_true]
  funext y
  by_cases h : y = x <;> simp [h]

section Marshal

variable (N : Nat) (leafSpec : LeafSpec)

/-- The value `callMarshal` stores for the scalar `k` in the slot of `z`. -/
def marshalVal (dt : TowerType) (z : String) (k : Nat) : RustVal dt :=
  leafSpec.limbStore ⟨exitMarshalName z, dt⟩ default 0 (BitVec.ofNat 64 k)

/-- **The marshalling of call arguments.**  From a state `rs0` with the scalar heap of
    `rs` and the tower slots of `rs` at the non-reserved names, the context of
    `callMarshal` runs to a state `rs1` that keeps the scalar heap and every tower slot
    other than the marshalling slots, holds in each marshalling slot it wrote the value
    `marshalVal` of the scalar, and holds, for each argument, a tower value of the slot's
    type related by `br` to the argument's value in the slot it reads the argument from. -/
theorem callMarshal_sim {br : ValueTowerBridge} {A : ExitTowers} {env : Env} {rs : RustState}
    (hag : envAgreesT br A env rs) (hmar : ExitMarshal br leafSpec) (dt : TowerType) :
    ∀ (args : List ImpExpr) (ctx : LowCT → LowCT) (ls : List Located) (vals : List Value),
      callMarshal A dt args = some (ctx, ls) → exitArgsOk args = true →
      List.Forall₂ (fun a v => ∃ x, a = ImpExpr.var x ∧ env x = some v) args vals →
      ∀ rs0 : RustState, rs0.rsScalar = rs.rsScalar →
        (∀ y, exitReserved y = false → rs0.rsTower y = rs.rsTower y) →
        ∃ rs1, (∀ c rs', RustExec N leafSpec c rs1 rs' → RustExec N leafSpec (ctx c) rs0 rs') ∧
          rs1.rsScalar = rs.rsScalar ∧
          (∀ y, (∀ z, y ≠ exitMarshalName z) → rs1.rsTower y = rs0.rsTower y) ∧
          (∀ z, rs1.rsTower (exitMarshalName z) = rs0.rsTower (exitMarshalName z) ∨
            rs1.rsTower (exitMarshalName z) =
              some ⟨dt, marshalVal leafSpec dt z (rs.rsScalar z)⟩) ∧
          List.Forall₂ (fun v (a : Located) => ∃ val, rs1.rsTower a.locVar = some ⟨a.locDst, val⟩ ∧
            br a.locDst v val ∧
            ∀ z, a.locVar = exitMarshalName z → val = marshalVal leafSpec a.locDst z (rs.rsScalar z))
            vals ls := by
  intro args
  induction args with
  | nil =>
    intro ctx ls vals h _ hF rs0 hS _
    simp only [callMarshal, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases hF
    exact ⟨rs0, fun c rs' hc => hc, hS, fun _ _ => rfl, fun _ => Or.inl rfl, List.Forall₂.nil⟩
  | cons a as ih =>
    intro ctx ls vals h hok hF rs0 hS hT
    cases a with
    | var x =>
      simp only [exitArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hok
      obtain ⟨hxr, hok⟩ := hok
      rcases hF with _ | ⟨⟨x', hx', hxv⟩, hF⟩
      cases hx'
      rename_i v vs
      rcases hr : callMarshal A dt as with _ | ⟨ctx', ls'⟩
      · simp [callMarshal, hr] at h
      rcases hx : A.lookup x with _ | t
      · -- a scalar argument: store it into its marshalling slot
        simp only [callMarshal, hr, hx] at h
        split_ifs at h with hmo
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have h8 : 8 ≤ dt.storageBytes := by simpa [exitMarshalOk] using hmo
        obtain ⟨hsv, hdv⟩ := envAgreesT_scalar hag hxr hx hxv
        have hSB : (rsSetTower rs0 (exitMarshalName x)
            ⟨dt, marshalVal leafSpec dt x (rs.rsScalar x)⟩).rsScalar = rs.rsScalar := hS
        have hTB : ∀ y, exitReserved y = false → (rsSetTower rs0 (exitMarshalName x)
            ⟨dt, marshalVal leafSpec dt x (rs.rsScalar x)⟩).rsTower y = rs.rsTower y := by
          intro y hy
          rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _
            (ne_marshal_of_nonreserved hy x).symm]
          exact hT y hy
        obtain ⟨rs1, hex, hS1, hT1, hM1, hF1⟩ := ih ctx' ls' vs hr hok hF _ hSB hTB
        refine ⟨rs1, fun c rs' hc => ?_, hS1, ?_, ?_, ?_⟩
        · refine RustExec.letZero _ _ _ _ _ (RustExec.seq _ _ _ _ _
            (RustExec.limbStoreExpr _ _ _ _ default ?_) ?_)
          · exact locatedLookup_of_rsTower _ _ dt default
              (CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _)
          · have hev : (SExpr.SVar x).evalState
                (rsSetTower rs0 (exitMarshalName x) ⟨dt, default⟩) = rs.rsScalar x := by
              simp only [SExpr.evalState]
              exact congrFun hS x
            simp only [locatedUpdate, hev, rsSetTower_rsSetTower]
            exact hex c rs' hc
        · intro y hy
          rw [hT1 y hy, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _
            (fun h => hy x h.symm)]
        · intro z
          by_cases hz : z = x
          · subst hz
            right
            rcases hM1 z with h1 | h1
            · rw [h1, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same]
            · exact h1
          · have hmz : exitMarshalName x ≠ exitMarshalName z :=
              fun h => hz (exitMarshalName_inj h).symm
            rcases hM1 z with h1 | h1
            · left
              rw [h1, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _ hmz]
            · exact Or.inr h1
        · refine List.Forall₂.cons ⟨marshalVal leafSpec dt x (rs.rsScalar x), ?_, ?_, ?_⟩ hF1
          · rcases hM1 x with h1 | h1
            · rw [h1, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same]
            · exact h1
          · exact hmar ⟨exitMarshalName x, dt⟩ v _ h8 hsv hdv
          · intro z hz
            obtain rfl := exitMarshalName_inj hz
            rfl
      · -- a tower argument, read in place at its tower type
        simp only [callMarshal, hr, hx, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨-, val, hval, hbr⟩ := envAgreesT_tower hag hxr hx hxv
        obtain ⟨rs1, hex, hS1, hT1, hM1, hF1⟩ := ih ctx' ls' vs hr hok hF rs0 hS hT
        refine ⟨rs1, hex, hS1, hT1, hM1, List.Forall₂.cons ⟨val, ?_, hbr,
          fun z hz => absurd hz (ne_marshal_of_nonreserved hxr z)⟩ hF1⟩
        rw [hT1 x (ne_marshal_of_nonreserved hxr), hT x hxr]
        exact hval
    | _ => simp [callMarshal] at h

end Marshal

/-- The tower values `RCall` reads from slots holding related values are related
    elementwise. -/
theorem forall₂_filterMap_rsTower {br : ValueTowerBridge} {rs : RustState} :
    ∀ {vals : List Value} {ls : List Located},
      List.Forall₂ (fun v (a : Located) => ∃ val, rs.rsTower a.locVar = some ⟨a.locDst, val⟩ ∧
        br a.locDst v val) vals ls →
      List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals
        (ls.filterMap fun a => rs.rsTower a.locVar)
  | [], [], _ => by simp
  | v :: vs, a :: as, List.Forall₂.cons ⟨val, hv, hb⟩ h => by
    rw [List.filterMap_cons, hv]
    exact List.Forall₂.cons hb (forall₂_filterMap_rsTower h)

/-- Under `exitArgsAt A dt args`, every argument slot of `callMarshal A dt args` has the
    type `dt`. -/
theorem callMarshal_locDst (A : ExitTowers) (dt : TowerType) :
    ∀ (args : List ImpExpr) (ctx : LowCT → LowCT) (ls : List Located),
      callMarshal A dt args = some (ctx, ls) → exitArgsAt A dt args = true →
      ∀ a ∈ ls, a.locDst = dt := by
  intro args
  induction args with
  | nil =>
    intro ctx ls h _ a ha
    simp only [callMarshal, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    cases ha
  | cons e as ih =>
    intro ctx ls h hat
    cases e with
    | var x =>
      simp only [exitArgsAt, List.all_cons, Bool.and_eq_true] at hat
      rcases hr : callMarshal A dt as with _ | ⟨ctx', ls'⟩
      · simp [callMarshal, hr] at h
      have ih' := ih ctx' ls' hr hat.2
      rcases hx : A.lookup x with _ | t
      · simp only [callMarshal, hr, hx] at h
        split_ifs at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · rfl
        · exact ih' a ha
      · simp only [callMarshal, hr, hx, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have ht : t = dt := by simpa [hx] using hat.1
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ht
        · exact ih' a ha
    | _ => simp [callMarshal] at h

/-- The tower values `RCall` reads from slots each holding a value of its declared type
    have the declared types of the slots. -/
theorem filterMap_rsTower_types {rs : RustState} :
    ∀ {ls : List Located}, (∀ a ∈ ls, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      (ls.filterMap fun a => rs.rsTower a.locVar).map (·.1) = ls.map (·.locDst)
  | [], _ => rfl
  | a :: as, h => by
    obtain ⟨v, hv⟩ := h a (by simp)
    simp only [List.filterMap_cons, hv, List.map_cons,
      filterMap_rsTower_types (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem forall₂_rsTower_typed {br : ValueTowerBridge} {rs : RustState}
    {vals : List Value} {ls : List Located}
    (h : List.Forall₂ (fun v (a : Located) => ∃ val, rs.rsTower a.locVar = some ⟨a.locDst, val⟩ ∧
      br a.locDst v val) vals ls) :
    ∀ a ∈ ls, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩ := by
  induction h with
  | nil => intro a ha; cases ha
  | cons hh _ ih =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · obtain ⟨val, hv, -⟩ := hh
      exact ⟨val, hv⟩
    · exact ih a ha

/-! ## §12  The heads of a `letBind` -/

theorem exitSimOkT_letBind_body (A : ExitTowers) (R : ExitRes) (tl il : Bool)
    (n : String) (val body : ImpExpr) (h : exitSimOkT A R tl il (.letBind n val body) = true) :
    exitSimOkT A R tl il body = true := by
  cases val with
  | lit l => cases tl <;> cases il <;> simp_all [exitSimOkT]
  | var s => cases tl <;> cases il <;> simp_all [exitSimOkT]
  | app f args => cases tl <;> cases il <;> simp_all [exitSimOkT]
  | _ => cases tl <;> cases il <;> simp [exitSimOkT] at h

/-- A run of the head `k` of `let n = val` from agreeing states: the body of the binding
    runs from an environment `env1` agreeing with a state `rs1` with the exit flag `0`,
    and every run of a lowered body from `rs1` extends to a run of `k` applied to it. -/
def HeadSimT (bi : Builtins) (N : Nat) (leafSpec : LeafSpec) (br : ValueTowerBridge)
    (A : ExitTowers) (R : ExitRes) (n : String) (val body : ImpExpr) : Prop :=
  ∀ (tl il : Bool) (fuel : Nat) (env env' : Env) (o : Outcome) (rs : RustState)
    (k : LowCT → LowCT),
    exitSimOkT A R tl il (.letBind n val body) = true → letHeadT A n val = some k →
    (denote' bi fuel (.letBind n val body)).run env = (o, env') → (∃ v, o = .val v) →
    envAgreesT br A env rs → rs.rsScalar exitRetName = 0 →
    ∃ env1 rs1, (denote' bi fuel body).run env1 = (o, env') ∧ envAgreesT br A env1 rs1 ∧
      rs1.rsScalar exitRetName = 0 ∧
      ∀ bC rs', RustExec N leafSpec bC rs1 rs' → RustExec N leafSpec (k bC) rs rs'

section Heads

variable (bi : Builtins) (N : Nat) (leafSpec : LeafSpec) (br : ValueTowerBridge)
  (A : ExitTowers) (R : ExitRes)

/-- **The `letBind` arm** from a simulation of the head. -/
theorem exitSimTy_letBind_of_head (n : String) (val body : ImpExpr)
    (ihb : ExitSimTy bi N leafSpec br A R body)
    (hhead : HeadSimT bi N leafSpec br A R n val body) :
    ExitSimTy bi N leafSpec br A R (.letBind n val body) := by
  intro tl fl fuel env env' o rs c xb hok hfl hK hrun hval hag hret
  rw [haxToLowCTKT_letBind_eq] at hK
  rcases hk : letHeadT A n val with _ | k
  · rw [hk] at hK; cases hK
  rcases hB : haxToLowCTKT A tl fl body with _ | ⟨bC, x⟩
  · rw [hk, hB] at hK; cases hK
  rw [hk, hB] at hK
  simp only [Option.some.injEq, Prod.mk.injEq] at hK
  obtain ⟨rfl, rfl⟩ := hK
  obtain ⟨env1, rs1, hrun1, hag1, hret1, hexK⟩ :=
    hhead tl fl.isSome fuel env env' o rs k hok hk hrun hval hag hret
  obtain ⟨rs', hex, hagE, hx⟩ :=
    ihb tl fl fuel env1 env' o rs1 bC x (exitSimOkT_letBind_body A R _ _ n val body hok) hfl hB
      hrun1 hval hag1 hret1
  exact ⟨rs', hexK bC rs' hex, hagE, hx⟩

/-- The scalar binding `let n = kk` of a scalar name: a run of the body from the state
    whose slot `n` holds `kk` extends to a run of the lowered binding. -/
theorem exec_letU64_set (n : String) (kk : Nat) (bC : LowCT) (rs rs' : RustState)
    (h : RustExec N leafSpec bC (rsSetScalar rs n kk) rs') :
    RustExec N leafSpec (.RLetU64Zero n (.RSeq (.RScalarSet n kk) bC)) rs rs' :=
  RustExec.letU64Zero _ _ _ _ (RustExec.seq _ _ _ _ _ (RustExec.scalarSet _ _ _)
    (by rw [rsSetScalar_rsSetScalar]; exact h))

theorem ret_setScalar {rs : RustState} {n : String} {q : Nat} (hn : exitReserved n = false)
    (kk : Nat) (h : rs.rsScalar exitRetName = q) :
    (rsSetScalar rs n kk).rsScalar exitRetName = q := by
  rw [rsScalar_rsSetScalar, if_neg (ne_of_reserved hn exitReserved_ret).symm, h]

/-- The head of `let n = l`: on a scalar name, the scalar binding of `letHead`; on a name
    placed in a tower at `t`, the zero slot of type `t` with the literal's word in limb `0`,
    whose value the marshalling condition `hmar` relates to the literal. -/
theorem head_lit (hmar : ExitMarshal br leafSpec) (n : String) (l : ImpLit) (body : ImpExpr) :
    HeadSimT bi N leafSpec br A R n (.lit l) body := by
  intro tl il fuel env env' o rs k hok hk hrun hval hag hret
  have hh : exitLitOk l = true ∧ exitReserved n = false := by
    cases tl <;> cases il <;>
      (simp only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true'] at hok
       exact ⟨hok.1.1, hok.1.2⟩)
  obtain ⟨hl, hn⟩ := hh
  have hsv := exitLitOk_scalarValN hl
  rw [denote'_letBind_run_val bi fuel n _ body env env _ (denote'_lit_run bi fuel l env)
    hsv.not_cf] at hrun
  rcases hsc' : A.lookup n with _ | t
  · have hk' : letHead n (.lit l) = some k := by simpa [letHeadT, hsc'] using hk
    obtain ⟨kk, hkk, hdk⟩ : ∃ kk, k = (fun bC => .RLetU64Zero n (.RSeq (.RScalarSet n kk) bC)) ∧
        valueToScalar (Value.ofLit l) = some kk := by
      cases l with
      | uintLit w m =>
        simp only [letHead, Option.some.injEq] at hk'
        exact ⟨_, hk'.symm, rfl⟩
      | int z =>
        simp only [exitLitOk, Bool.and_eq_true, decide_eq_true_eq] at hl
        simp only [letHead, ge_iff_le, hl.1, if_true, Option.some.injEq] at hk'
        exact ⟨_, hk'.symm, by simp [valueToScalar, Value.ofLit, hl.1]⟩
      | bool b =>
        simp only [letHead, Option.some.injEq] at hk'
        exact ⟨_, hk'.symm, valueToScalar_bool b⟩
      | unit => simp [letHead] at hk'
      | _ => simp [exitLitOk] at hl
    subst hkk
    exact ⟨_, _, hrun, envAgreesT_extend hn hsc' hsv hdk hag, ret_setScalar hn _ hret,
      fun bC rs' h => exec_letU64_set N leafSpec n kk bC rs rs' h⟩
  · simp only [letHeadT, hsc'] at hk
    split_ifs at hk with hmo
    obtain ⟨kk, hdk, rfl⟩ := Option.map_eq_some_iff.mp hk
    have h8 : 8 ≤ t.storageBytes := by simpa [exitMarshalOk] using hmo
    refine ⟨_, rsSetTower rs n ⟨t, leafSpec.limbStore ⟨n, t⟩ default 0 (BitVec.ofNat 64 kk)⟩,
      hrun, envAgreesT_extend_tower hn hsc' hsv.not_cf (hmar ⟨n, t⟩ _ kk h8 hsv hdk) hag, hret,
      fun bC rs' h => ?_⟩
    refine RustExec.letZero _ _ _ _ _ (RustExec.seq _ _ _ _ _
      (RustExec.limbStoreExpr _ _ _ _ default ?_) ?_)
    · exact locatedLookup_of_rsTower _ _ t default
        (CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _)
    · simpa only [locatedUpdate, SExpr.evalState, rsSetTower_rsSetTower] using h

theorem head_var (n s : String) (body : ImpExpr) :
    HeadSimT bi N leafSpec br A R n (.var s) body := by
  intro tl il fuel env env' o rs k hok hk hrun hval hag hret
  have hh : exitReserved n = false ∧ exitReserved s = false ∧ A.lookup n = A.lookup s := by
    cases tl <;> cases il <;>
      (simp only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hok
       exact ⟨hok.1.1.1, hok.1.1.2, hok.1.2⟩)
  obtain ⟨hn, hs, hns⟩ := hh
  cases hw : env s with
  | none =>
    rw [denote'_letBind_run_nonval bi fuel n _ body env env _
      (by rw [denote'_var_run, hw]) (fun _ h => by cases h)] at hrun
    obtain ⟨v, hv⟩ := hval
    cases hrun
    cases hv
  | some w =>
    have hcf := envAgreesT_not_cf hag hs hw
    rw [denote'_letBind_run_val bi fuel n _ body env env w (by rw [denote'_var_run, hw])
      hcf] at hrun
    rcases hA : A.lookup s with _ | t
    · rw [hA] at hns
      simp only [letHeadT, hns, hA, letHead] at hk
      obtain ⟨hsv, hdv⟩ := envAgreesT_scalar hag hs hA hw
      by_cases hsn : n = s
      · subst hsn
        simp only [if_true, Option.some.injEq] at hk
        subst hk
        rw [Env.extend_self env n w hw] at hrun
        exact ⟨env, rs, hrun, hag, hret, fun bC rs' h => h⟩
      · simp only [hsn, if_false, Option.some.injEq] at hk
        subst hk
        exact ⟨_, _, hrun, envAgreesT_extend hn hns hsv hdv hag, ret_setScalar hn _ hret,
          fun bC rs' h => rustExec_letBind_copy N leafSpec n s bC rs rs' hsn h⟩
    · rw [hA] at hns
      simp only [letHeadT, hns, hA, if_true] at hk
      obtain ⟨-, val, hval', hbr⟩ := envAgreesT_tower hag hs hA hw
      by_cases hsn : n = s
      · subst hsn
        simp only [if_true, Option.some.injEq] at hk
        subst hk
        rw [Env.extend_self env n w hw] at hrun
        exact ⟨env, rs, hrun, hag, hret, fun bC rs' h => h⟩
      · simp only [hsn, if_false, Option.some.injEq] at hk
        subst hk
        refine ⟨_, rsSetTower rs n ⟨t, val⟩, hrun,
          envAgreesT_extend_tower hn hns hcf hbr hag, hret, fun bC rs' h => ?_⟩
        exact RustExec.seq _ _ _ _ _
          (RustExec.copy ⟨n, t⟩ ⟨s, t⟩ rs rfl val (locatedLookup_of_rsTower rs s t val hval')) h

/-! ### Inversion of the call heads -/

theorem scalarOpHeadT_some {n f : String} {args : List ImpExpr} {se : SExpr}
    (h : scalarOpHeadT A n f args = some se) :
    ∃ a b, args = [.var a, .var b] ∧ A.lookup n = none ∧ A.lookup a = none ∧
      A.lookup b = none ∧ scalarOpExprT f (.SVar a) (.SVar b) = some se := by
  unfold scalarOpHeadT at h
  split at h
  · rename_i a b
    split_ifs at h with hc
    exact ⟨a, b, rfl, hc.1, hc.2.1, hc.2.2, h⟩
  · cases h

theorem indexHeadT_some {n : String} {args : List ImpExpr} {k : LowCT → LowCT}
    (h : indexHeadT A n args = some k) :
    ∃ arr idx t, args = [.var arr, .var idx] ∧ A.lookup arr = some t ∧ A.lookup idx = none ∧
      ((exitElemTower t = none ∧ A.lookup n = none ∧ k = fun b => .RLetZero exitCallName .TFp
          (.RSeq (.RArrLoad ⟨exitCallName, .TFp⟩ ⟨arr, t⟩ idx)
            (.RSeq (.RScalarSetExpr n (.SLimb exitCallName 0)) b))) ∨
        ∃ t', exitElemTower t = some t' ∧ A.lookup n = some t' ∧
          k = fun b => .RLetZero exitCallName t'
            (.RSeq (.RArrLoad ⟨exitCallName, t'⟩ ⟨arr, t⟩ idx)
              (.RSeq (.RCopy ⟨n, t'⟩ ⟨exitCallName, t'⟩) b))) := by
  unfold indexHeadT at h
  split at h
  · rename_i arr idx
    rcases ht : A.lookup arr with _ | t <;> rw [ht] at h
    · cases h
    · simp only at h
      rcases he : exitElemTower t with _ | t' <;> simp only [he] at h
      · split_ifs at h with hi hn
        simp only [Option.some.injEq] at h
        exact ⟨arr, idx, t, rfl, ht, hi, Or.inl ⟨he, hn, h.symm⟩⟩
      · split_ifs at h with hi hn
        simp only [Option.some.injEq] at h
        exact ⟨arr, idx, t, rfl, ht, hi, Or.inr ⟨t', he, hn, h.symm⟩⟩
  · cases h

theorem updateHeadT_some {n : String} {args : List ImpExpr} {k : LowCT → LowCT}
    (h : updateHeadT A n args = some k) :
    ∃ arr idx src t ctx srcLoc, args = [.var arr, .var idx, .var src] ∧ n = arr ∧
      A.lookup arr = some t ∧ A.lookup idx = none ∧
      ((exitElemTower t).isNone = true → A.lookup src = none) ∧
      callMarshal A (exitElem t) [.var src] = some (ctx, [srcLoc]) ∧
      srcLoc.locSrc = exitElem t ∧
      k = fun b => .RSeq (ctx (.RArrStore ⟨arr, t⟩ idx srcLoc)) b := by
  unfold updateHeadT at h
  split at h
  · rename_i arr idx src
    rcases ht : A.lookup arr with _ | t <;> rw [ht] at h
    · cases h
    · simp only at h
      split_ifs at h with hc
      rcases hm : callMarshal A (exitElem t) [.var src] with _ | ⟨ctx, ls⟩ <;> rw [hm] at h
      · cases h
      · rcases ls with _ | ⟨srcLoc, _ | ⟨_, _⟩⟩ <;> simp only [reduceCtorEq] at h
        split_ifs at h with hsl
        simp only [Option.some.injEq] at h
        exact ⟨arr, idx, src, t, ctx, srcLoc, rfl, hc.1, ht, hc.2.1, hc.2.2, hm, hsl, h.symm⟩
  · cases h

theorem callHeadAt_some {n f : String} {dt dr : TowerType} {args : List ImpExpr}
    {k : LowCT → LowCT} (h : callHeadAt A n f dt dr args = some k) :
    ∃ ctx ls, callMarshal A dt args = some (ctx, ls) ∧
      ((A.lookup n = none ∧
          k = fun b => .RSeq (.RLetZero exitCallName dr
            (ctx (.RCall f ⟨exitCallName, dr⟩ ls)))
            (.RSeq (.RScalarSetExpr n (.SLimb exitCallName 0)) b)) ∨
        (A.lookup n = some dr ∧
          k = fun b => .RSeq (.RLetZero exitCallName dr
            (ctx (.RCall f ⟨exitCallName, dr⟩ ls)))
            (.RSeq (.RCopy ⟨n, dr⟩ ⟨exitCallName, dr⟩) b))) := by
  unfold callHeadAt at h
  rcases hm : callMarshal A dt args with _ | ⟨ctx, ls⟩ <;> rw [hm] at h
  · cases h
  · simp only at h
    refine ⟨ctx, ls, rfl, ?_⟩
    rcases hn : A.lookup n with _ | t <;> rw [hn] at h
    · simp only [Option.some.injEq] at h
      exact Or.inl ⟨rfl, h.symm⟩
    · simp only at h
      split_ifs at h with ht
      subst ht
      simp only [Option.some.injEq] at h
      exact Or.inr ⟨rfl, h.symm⟩

/-- The call heads: a call of `exitScalarRes` bound to a scalar name at
    `towerOfCallName f`; a call with the declared result type `dr` at `dr`, bound to a
    scalar name only for `dr = TU64`; a call without a declared result type bound to a name
    placed at `towerOfCallName f` at that type; a linked callee with argument slot types
    `ts` and result type `dr` at `dr`, whose argument slots have the types `ts`, bound to a
    scalar name only for `dr = TU64`. -/
theorem callHeadT_some {n f : String} {args : List ImpExpr} {k : LowCT → LowCT}
    (h : callHeadT A n f args = some k) :
    ∃ dt dr, callHeadAt A n f dt dr args = some k ∧
      ((exitScalarRes f = true ∧ A.lookup n = none ∧ dr = towerOfCallName f) ∨
        (exitScalarRes f = false ∧ exitCalleeTys A f = none ∧ exitCallTys A f = some dr ∧
          exitOptTys A f = none ∧ (A.lookup n = none → dr = .TU64)) ∨
        (exitScalarRes f = false ∧ exitCalleeTys A f = none ∧ exitCallTys A f = none ∧
          A.lookup n = some dr ∧ dr = towerOfCallName f) ∨
        (∃ ts, exitScalarRes f = false ∧ exitCalleeTys A f = some (ts, dr) ∧ dt = .TU64 ∧
          (callMarshal A .TU64 args).map (fun cl => cl.2.map (·.locDst)) = some ts ∧
          (A.lookup n = none → dr = .TU64))) := by
  unfold callHeadT at h
  by_cases hs : exitScalarRes f = true
  · rw [if_pos hs] at h
    split_ifs at h with hn
    exact ⟨_, _, h, Or.inl ⟨hs, hn.1, rfl⟩⟩
  · rw [if_neg hs] at h
    have hs' : exitScalarRes f = false := by simpa using hs
    rcases hc : exitCalleeTys A f with _ | ⟨ts, dr⟩ <;> rw [hc] at h
    · simp only at h
      rcases hd : exitCallTys A f with _ | dr <;> rw [hd] at h
      · simp only at h
        split_ifs at h with hn
        exact ⟨_, _, h, Or.inr (Or.inr (Or.inl ⟨hs', rfl, rfl, hn, rfl⟩))⟩
      · simp only at h
        split_ifs at h with hn
        refine ⟨_, _, h, Or.inr (Or.inl ⟨hs', rfl, rfl, ?_, fun h0 => ?_⟩)⟩
        · by_contra hne
          exact hn (Or.inl (Option.isSome_iff_ne_none.mpr hne))
        · by_contra hne
          exact hn (Or.inr ⟨h0, hne⟩)
    · simp only at h
      split_ifs at h with hn
      refine ⟨_, _, h, Or.inr (Or.inr (Or.inr ⟨ts, hs', rfl, rfl, ?_, fun h0 => ?_⟩))⟩
      · by_contra hne
        exact hn (Or.inr (Or.inr (Or.inr hne)))
      · by_contra hne
        exact hn (Or.inr (Or.inr (Or.inl ⟨h0, hne⟩)))

/-- A call head of `callHeadT` has an admitted name (`exitAdmits`). -/
theorem callHeadT_admits {n f : String} {args : List ImpExpr} {k : LowCT → LowCT}
    (h : callHeadT A n f args = some k) : exitAdmits f = true := by
  by_cases hs : exitScalarRes f = true
  · unfold callHeadT at h
    rw [if_pos hs] at h
    split_ifs at h with hn
    exact hn.2
  · exact exitAdmits_of_scalarRes_false (by simpa using hs)

/-- The call of `optHeadT` on the marshalling context `ctx` and the argument slots `ls`. -/
def optCallC (f : String) (t : TowerType) (ctx : LowCT → LowCT) (ls : List Located) : LowCT :=
  .RSeq (.RLetZero exitOptTagName .TU64 (.RLetZero exitOptPayName t
    (ctx (.RCallN f [⟨exitOptTagName, .TU64⟩, ⟨exitOptPayName, t⟩] ls))))
    (.RScalarSetExpr exitOptTagS (.SLimb exitOptTagName 0))

theorem optHeadT_some {f : String} {args : List ImpExpr} {p : String} {callC bindP : LowCT}
    (h : optHeadT A f args p = some (callC, bindP)) :
    ∃ t ctx ls, exitScalarRes f = false ∧ f ≠ "index" ∧ f ≠ "array_update" ∧
      f ≠ "array_lit" ∧ f ≠ "repeat" ∧ exitOptTys A f = some t ∧
      callMarshal A .TU64 args = some (ctx, ls) ∧ callC = optCallC f t ctx ls ∧
      ((A.lookup p = none ∧ t = .TU64 ∧
          bindP = .RScalarSetExpr p (.SLimb exitOptPayName 0)) ∨
        (A.lookup p = some t ∧ t ≠ .TU64 ∧ bindP = .RCopy ⟨p, t⟩ ⟨exitOptPayName, t⟩)) := by
  unfold optHeadT at h
  split_ifs at h with hf
  simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true] at hf
  obtain ⟨⟨⟨⟨hs, hi⟩, hu⟩, hl⟩, hr⟩ := hf
  rcases ht : exitOptTys A f with _ | t <;> rw [ht] at h
  · cases h
  simp only at h
  rcases hm : callMarshal A .TU64 args with _ | ⟨ctx, ls⟩ <;> rw [hm] at h
  · cases h
  simp only at h
  rcases hp : A.lookup p with _ | tp <;> rw [hp] at h
  · simp only at h
    split_ifs at h with htu
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨t, ctx, ls, hs, hi, hu, hl, hr, rfl, rfl, rfl, Or.inl ⟨rfl, htu, rfl⟩⟩
  · simp only at h
    split_ifs at h with htp
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, htu⟩ := htp
    exact ⟨tp, ctx, ls, hs, hi, hu, hl, hr, rfl, rfl, rfl, Or.inr ⟨rfl, htu, rfl⟩⟩

theorem repeatHeadT_some {n : String} {args : List ImpExpr} {k : LowCT → LowCT}
    (h : repeatHeadT A n args = some k) :
    ∃ v l c kN, args = [.var v, .lit l] ∧ A.lookup n = some c ∧
      valueToScalar (Value.ofLit l) = some kN ∧
      (exitArrLen c = some kN ∧ exitMarshalOk (exitElem c) = true) ∧
      callHeadAt A n "repeat" (exitElem c) c [.var v] = some k := by
  unfold repeatHeadT at h
  split at h
  · rename_i v l
    rcases hn : A.lookup n with _ | c <;> rcases hv : valueToScalar (Value.ofLit l) with _ | kN <;>
      simp only [hn, hv] at h
    all_goals first | cases h | skip
    split_ifs at h with hc
    exact ⟨v, l, c, kN, rfl, rfl, hv, hc, h⟩
  · cases h

theorem arrLitHeadN_some {n : String} {args : List ImpExpr} {k : LowCT → LowCT}
    (h : arrLitHeadN A n args = some k) :
    ∃ c, A.lookup n = some c ∧
      (exitArrLen c = some args.length ∧ exitMarshalOk (exitElem c) = true ∧
        exitArgsAt A (exitElem c) args = true) ∧
      callHeadAt A n "array_lit" (exitElem c) c args = some k := by
  unfold arrLitHeadN at h
  rcases hn : A.lookup n with _ | c <;> rw [hn] at h
  · cases h
  · simp only at h
    split_ifs at h with hl
    exact ⟨c, rfl, hl, h⟩


/-! ### Simulation of the call heads -/

variable {bi N leafSpec br A}

/-- The result of a head of `let n = f(args)`: from `rs`, a state agreeing with the
    environment extended by `n ↦ r`, with the exit flag `q` (by default `0`), through which
    every run of the lowered body extends to a run of the head. -/
def HeadResT (N : Nat) (leafSpec : LeafSpec) (br : ValueTowerBridge) (A : ExitTowers)
    (env : Env) (rs : RustState) (n : String) (r : Value) (k : LowCT → LowCT)
    (q : Nat := 0) : Prop :=
  ∃ rs1, envAgreesT br A (env.extend n r) rs1 ∧ rs1.rsScalar exitRetName = q ∧
    ∀ bC rs', RustExec N leafSpec bC rs1 rs' → RustExec N leafSpec (k bC) rs rs'

theorem forall₂_var2 {env : Env} {a b : String} {vals : List Value}
    (h : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v)
      [.var a, .var b] vals) : ∃ va vb, vals = [va, vb] ∧ env a = some va ∧ env b = some vb := by
  rcases h with _ | ⟨⟨x, hx, hxa⟩, h⟩
  rcases h with _ | ⟨⟨y, hy, hyb⟩, h⟩
  cases h
  cases hx; cases hy
  exact ⟨_, _, rfl, hxa, hyb⟩

theorem forall₂_var3 {env : Env} {a b c : String} {vals : List Value}
    (h : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v)
      [.var a, .var b, .var c] vals) :
    ∃ va vb vc, vals = [va, vb, vc] ∧ env a = some va ∧ env b = some vb ∧ env c = some vc := by
  rcases h with _ | ⟨⟨x, hx, hxa⟩, h⟩
  rcases h with _ | ⟨⟨y, hy, hyb⟩, h⟩
  rcases h with _ | ⟨⟨z, hz, hzc⟩, h⟩
  cases h
  cases hx; cases hy; cases hz
  exact ⟨_, _, _, rfl, hxa, hyb, hzc⟩

theorem headT_scalarOp {D DO : String → Option TowerType}
    {DA : String → Option (List TowerType × TowerType)} (hL : ExitLeaves bi leafSpec br D DO DA)
    {env : Env} {rs : RustState}
    {n f : String} {args : List ImpExpr} {se : SExpr} {vals : List Value} {r : Value}
    (hso : scalarOpHeadT A n f args = some se) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi f vals = some r) (hag : envAgreesT br A env rs)
    {q : Nat} (hret : rs.rsScalar exitRetName = q) :
    HeadResT N leafSpec br A env rs n r (fun b => .RSeq (.RScalarSetExpr n se) b) q := by
  obtain ⟨a, b, rfl, hnA, haA, hbA, hse⟩ := scalarOpHeadT_some A hso
  simp only [exitArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hargs
  obtain ⟨va, vb, rfl, hva, hvb⟩ := forall₂_var2 hF
  obtain ⟨hsa, hda⟩ := envAgreesT_scalar hag hargs.1 haA hva
  obtain ⟨hsb, hdb⟩ := envAgreesT_scalar hag hargs.2.1 hbA hvb
  have hop : (scalarOpExprT f (.SVar "a") (.SVar "b")).isSome = true := by
    rw [scalarOpExprT_isSome_vars f "a" "b" a b, hse]; rfl
  obtain ⟨hsr, hdr⟩ := hL.ops f va vb r _ _ hop hsa hsb hda hdb hbi
  rw [← scalarOpExprT_evalState f a b se rs hse] at hdr
  exact ⟨_, envAgreesT_extend hn hnA hsr hdr hag, ret_setScalar hn _ hret,
    fun bC rs' h => RustExec.seq _ _ _ _ _ (RustExec.scalarSetExpr _ _ _) h⟩

theorem rsTowerLimb_rsSetTower_same (rs : RustState) (x : String) (t : TowerType)
    (v : RustVal t) (i : Nat) : rsTowerLimb (rsSetTower rs x ⟨t, v⟩) x i = towerLimb v i := by
  simp [rsTowerLimb, CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same]

theorem headT_index {D DO : String → Option TowerType}
    {DA : String → Option (List TowerType × TowerType)} (hL : ExitLeaves bi leafSpec br D DO DA)
    {env : Env} {rs : RustState}
    {n : String} {args : List ImpExpr} {k : LowCT → LowCT} {vals : List Value} {r : Value}
    (hk : indexHeadT A n args = some k) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi "index" vals = some r) (hag : envAgreesT br A env rs)
    {q : Nat} (hret : rs.rsScalar exitRetName = q) :
    HeadResT N leafSpec br A env rs n r k q := by
  obtain ⟨arr, idx, t, rfl, htA, hiA, hcase⟩ := indexHeadT_some A hk
  simp only [exitArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hargs
  obtain ⟨vArr, vIdx, rfl, hva, hvi⟩ := forall₂_var2 hF
  obtain ⟨-, arrV, harr, hbr⟩ := envAgreesT_tower hag hargs.1 htA hva
  obtain ⟨-, hdi⟩ := envAgreesT_scalar hag hargs.2.1 hiA hvi
  have harrne : exitCallName ≠ arr := (ne_of_reserved hargs.1 exitReserved_call).symm
  rcases hcase with ⟨he, hnA, rfl⟩ | ⟨t', he, hnA, rfl⟩
  swap
  · -- an element of tower type `t'`: load it into the call slot and copy it into `n`
    have hbrR := hL.indexT t t' vArr vIdx r arrV _ he hbr hdi hbi
    let D : Located := ⟨exitCallName, t'⟩
    let lv := leafSpec.arrLoad D default ⟨t, arrV⟩ (rs.rsScalar idx)
    have hload : RustExec N leafSpec (.RArrLoad D ⟨arr, t⟩ idx)
        (rsSetTower rs exitCallName ⟨t', default⟩)
        (rsSetTower (rsSetTower rs exitCallName ⟨t', default⟩) exitCallName ⟨t', lv⟩) :=
      RustExec.arrLoad D ⟨arr, t⟩ idx _ _ default arrV rfl
        (locatedLookup_of_rsTower _ _ _ _ (CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _))
        (locatedLookup_of_rsTower _ _ _ _ (by
          rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _ harrne]; exact harr))
    have hagB : envAgreesT br A env
        (rsSetTower (rsSetTower rs exitCallName ⟨t', default⟩) exitCallName ⟨t', lv⟩) :=
      envAgreesT_setTower_reserved _ exitReserved_call
        (envAgreesT_setTower_reserved _ exitReserved_call hag)
    refine ⟨rsSetTower (rsSetTower (rsSetTower rs exitCallName ⟨t', default⟩) exitCallName
        ⟨t', lv⟩) n ⟨t', lv⟩, envAgreesT_extend_tower hn hnA (hL.plain _ _ _ hbi) hbrR hagB,
      hret, fun bC rs' h => ?_⟩
    exact RustExec.letZero _ _ _ _ _ (RustExec.seq _ _ _ _ _ hload
      (RustExec.seq _ _ _ _ _ (RustExec.copy ⟨n, t'⟩ ⟨exitCallName, t'⟩ _ rfl lv
        (locatedLookup_of_rsTower _ _ _ _
          (CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _))) h))
  obtain ⟨hsr, hdr⟩ := hL.index t vArr vIdx r arrV _ he hbr hdi hbi
  -- the states: the call slot zeroed, the element loaded, the limb copied
  let D : Located := ⟨exitCallName, .TFp⟩
  let lv := leafSpec.arrLoad D default ⟨t, arrV⟩ (rs.rsScalar idx)
  have hload : RustExec N leafSpec (.RArrLoad D ⟨arr, t⟩ idx)
      (rsSetTower rs exitCallName ⟨.TFp, default⟩)
      (rsSetTower (rsSetTower rs exitCallName ⟨.TFp, default⟩) exitCallName ⟨.TFp, lv⟩) :=
    RustExec.arrLoad D ⟨arr, t⟩ idx _ _ default arrV rfl
      (locatedLookup_of_rsTower _ _ _ _ (CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _))
      (locatedLookup_of_rsTower _ _ _ _ (by
        rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _ harrne]; exact harr))
  have hagB : envAgreesT br A env
      (rsSetTower (rsSetTower rs exitCallName ⟨.TFp, default⟩) exitCallName ⟨.TFp, lv⟩) :=
    envAgreesT_setTower_reserved _ exitReserved_call
      (envAgreesT_setTower_reserved _ exitReserved_call hag)
  have hev : (SExpr.SLimb exitCallName 0).evalState
      (rsSetTower (rsSetTower rs exitCallName ⟨.TFp, default⟩) exitCallName ⟨.TFp, lv⟩) =
      towerLimb lv 0 := by
    simp only [SExpr.evalState]
    exact rsTowerLimb_rsSetTower_same _ _ _ _ _
  refine ⟨rsSetScalar (rsSetTower (rsSetTower rs exitCallName ⟨.TFp, default⟩) exitCallName
      ⟨.TFp, lv⟩) n (towerLimb lv 0), envAgreesT_extend hn hnA hsr hdr hagB,
    ret_setScalar hn _ hret, fun bC rs' h => ?_⟩
  have hset := RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) n
    (.SLimb exitCallName 0)
    (rsSetTower (rsSetTower rs exitCallName ⟨.TFp, default⟩) exitCallName ⟨.TFp, lv⟩)
  rw [hev] at hset
  exact RustExec.letZero _ _ _ _ _ (RustExec.seq _ _ _ _ _ hload
    (RustExec.seq _ _ _ _ _ hset h))

theorem headT_update {D DO : String → Option TowerType}
    {DA : String → Option (List TowerType × TowerType)} (hL : ExitLeaves bi leafSpec br D DO DA)
    {env : Env} {rs : RustState}
    {n : String} {args : List ImpExpr} {k : LowCT → LowCT} {vals : List Value} {r : Value}
    (hk : updateHeadT A n args = some k) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi "array_update" vals = some r) (hag : envAgreesT br A env rs)
    {q : Nat} (hret : rs.rsScalar exitRetName = q) :
    HeadResT N leafSpec br A env rs n r k q := by
  obtain ⟨arr, idx, src, t, ctx, srcLoc, rfl, hna, htA, hiA, hsrcA, hm, hsl, rfl⟩ :=
    updateHeadT_some A hk
  subst hna
  have hargs' := hargs
  simp only [exitArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hargs'
  obtain ⟨vArr, vIdx, vSrc, rfl, hva, hvi, hvs⟩ := forall₂_var3 hF
  obtain ⟨-, arrV, harr, hbr⟩ := envAgreesT_tower hag hargs'.1 htA hva
  obtain ⟨-, hdi⟩ := envAgreesT_scalar hag hargs'.2.1 hiA hvi
  have hsrcOk : exitArgsOk [.var src] = true := by
    simp [exitArgsOk, hargs'.2.2.1]
  obtain ⟨rs1, hex, hS1, hT1, -, hF1⟩ :=
    callMarshal_sim N leafSpec hag hL.marshal (exitElem t) [.var src] ctx [srcLoc] [vSrc] hm
      hsrcOk (List.Forall₂.cons ⟨src, rfl, hvs⟩ List.Forall₂.nil) rs rfl (fun _ _ => rfl)
  rcases hF1 with _ | ⟨⟨sv, hsv, hbs, hmv⟩, -⟩
  obtain ⟨sName, sTy⟩ := srcLoc
  simp only at hsl
  subst hsl
  have hbrR : br t r (leafSpec.arrStore ⟨n, t⟩ arrV (rs.rsScalar idx) ⟨exitElem t, sv⟩) := by
    rcases he : exitElemTower t with _ | t'
    · -- an array of words: the source is a scalar marshalled into `exitMarshalName src`
      have hsA : A.lookup src = none := hsrcA (by simp [he])
      obtain ⟨hsvs, hdvs⟩ := envAgreesT_scalar hag hargs'.2.2.1 hsA hvs
      simp only [callMarshal, hsA] at hm
      split_ifs at hm with hmo
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, Located.mk.injEq,
        and_true] at hm
      obtain ⟨-, hsN⟩ := hm
      have h8 : 8 ≤ (exitElem t).storageBytes := by simpa [exitMarshalOk] using hmo
      rw [hmv src hsN.symm]
      exact hL.update n (exitMarshalName src) t vArr vIdx vSrc r arrV (rs.rsScalar idx)
        (rs.rsScalar src) he h8 hbr hdi hsvs hdvs hbi
    · exact hL.updateT n t vArr vIdx vSrc r arrV sv (rs.rsScalar idx) (by simp [he]) hbr hdi
        hbs hbi
  have harr1 : rs1.rsTower n = some ⟨t, arrV⟩ := by
    rw [hT1 n (ne_marshal_of_nonreserved hargs'.1)]; exact harr
  have hstore : RustExec N leafSpec (.RArrStore ⟨n, t⟩ idx ⟨sName, exitElem t⟩) rs1
      (rsSetTower rs1 n ⟨t, leafSpec.arrStore ⟨n, t⟩ arrV (rs.rsScalar idx)
        ⟨exitElem t, sv⟩⟩) :=
    RustExec.arrStore ⟨n, t⟩ idx ⟨sName, exitElem t⟩ rs1 _ arrV sv (congrFun hS1 idx)
      (locatedLookup_of_rsTower _ _ _ _ harr1) (locatedLookup_of_rsTower _ _ _ _ hsv)
  have hag1 : envAgreesT br A env rs1 :=
    envAgreesT_of_eqOn hS1 (fun y hy => hT1 y (ne_marshal_of_nonreserved hy)) hag
  refine ⟨_, envAgreesT_extend_tower hn htA (hL.plain _ _ _ hbi) hbrR hag1, ?_,
    fun bC rs' h => RustExec.seq _ _ _ _ _ (hex _ _ hstore) h⟩
  show rs1.rsScalar exitRetName = q
  rw [hS1]; exact hret

/-- The head of a call marshalling its scalar arguments at `dt` into a result slot of type
    `dr`, for a value `r` without a control-flow tag that the leaf output agrees with at the
    placement of the bound name, whenever the argument values are related to the slots the
    call reads. -/
theorem headT_callAtR {D DO : String → Option TowerType}
    {DA : String → Option (List TowerType × TowerType)} (hL : ExitLeaves bi leafSpec br D DO DA)
    {env : Env} {rs : RustState}
    {n f : String} {dt dr : TowerType} {args : List ImpExpr} {k : LowCT → LowCT}
    {vals : List Value} {r : Value} (hcf : r.isControlFlow = false)
    (hT : A.lookup n = some dr → ∀ (ls : List Located)
      (argList : List (Σ t : TowerType, RustVal t)) (oldV : RustVal dr),
      List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
      (exitArgsAt A dt args = true → ∀ p ∈ argList, p.1 = dt) →
      (∃ ctx, callMarshal A dt args = some (ctx, ls)) →
      argList.map (·.1) = ls.map (·.locDst) →
      br dr r (leafSpec.call f dr (ls.map (·.locDst)) oldV argList))
    (hS : A.lookup n = none → ∀ (ls : List Located)
      (argList : List (Σ t : TowerType, RustVal t)) (oldV : RustVal dr),
      List.Forall₂ (fun v (p : Σ t : TowerType, RustVal t) => br p.1 v p.2) vals argList →
      (∃ ctx, callMarshal A dt args = some (ctx, ls)) →
      argList.map (·.1) = ls.map (·.locDst) →
      ScalarValN r ∧
        valueToScalar r = some (towerLimb (leafSpec.call f dr (ls.map (·.locDst)) oldV argList) 0))
    (hk : callHeadAt A n f dt dr args = some k) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hag : envAgreesT br A env rs)
    {q : Nat} (hret : rs.rsScalar exitRetName = q) :
    HeadResT N leafSpec br A env rs n r k q := by
  obtain ⟨ctx, ls, hm, hcase⟩ := callHeadAt_some A hk
  have hloc := callMarshal_locDst A dt args ctx ls hm
  have hT0 : ∀ y, exitReserved y = false →
      (rsSetTower rs exitCallName ⟨dr, default⟩).rsTower y = rs.rsTower y := fun y hy =>
    CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _
      (ne_of_reserved hy exitReserved_call).symm
  obtain ⟨rs1, hex, hS1, hT1, -, hF1'⟩ :=
    callMarshal_sim N leafSpec hag hL.marshal dt args ctx ls vals hm hargs hF
      (rsSetTower rs exitCallName ⟨dr, default⟩) rfl hT0
  have hF1 : List.Forall₂ (fun v (a : Located) => ∃ val,
      rs1.rsTower a.locVar = some ⟨a.locDst, val⟩ ∧ br a.locDst v val) vals ls :=
    hF1'.imp fun _ _ h => by
      obtain ⟨val, h1, h2, -⟩ := h
      exact ⟨val, h1, h2⟩
  have hcall1 : rs1.rsTower exitCallName = some ⟨dr, default⟩ := by
    rw [hT1 exitCallName (fun z => exitCallName_ne_marshal z)]
    exact CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _
  let argList := ls.filterMap fun a => rs1.rsTower a.locVar
  let resV := leafSpec.call f dr (ls.map (·.locDst)) default argList
  have hcall : RustExec N leafSpec (.RCall f ⟨exitCallName, dr⟩ ls) rs1
      (rsSetTower rs1 exitCallName ⟨dr, resV⟩) :=
    RustExec.call f ⟨exitCallName, dr⟩ ls rs1 default argList
      (locatedLookup_of_rsTower _ _ _ _ hcall1) rfl (forall₂_rsTower_typed hF1)
  have hC : RustExec N leafSpec (.RLetZero exitCallName dr
      (ctx (.RCall f ⟨exitCallName, dr⟩ ls))) rs (rsSetTower rs1 exitCallName ⟨dr, resV⟩) :=
    RustExec.letZero _ _ _ _ _ (hex _ _ hcall)
  have hF2 := forall₂_filterMap_rsTower hF1
  have htys : argList.map (·.1) = ls.map (·.locDst) :=
    filterMap_rsTower_types (forall₂_rsTower_typed hF1)
  have hag2 : envAgreesT br A env (rsSetTower rs1 exitCallName ⟨dr, resV⟩) :=
    envAgreesT_setTower_reserved _ exitReserved_call
      (envAgreesT_of_eqOn hS1 (fun y hy => by
        rw [hT1 y (ne_marshal_of_nonreserved hy), hT0 y hy]) hag)
  have hret2 : (rsSetTower rs1 exitCallName ⟨dr, resV⟩).rsScalar exitRetName = q := by
    show rs1.rsScalar exitRetName = q
    rw [hS1]; exact hret
  rcases hcase with ⟨hnA, rfl⟩ | ⟨hnA, rfl⟩
  · obtain ⟨hsr, hdr⟩ := hS hnA ls argList default hF2 ⟨ctx, hm⟩ htys
    have hev : (SExpr.SLimb exitCallName 0).evalState
        (rsSetTower rs1 exitCallName ⟨dr, resV⟩) = towerLimb resV 0 := by
      simp only [SExpr.evalState]
      exact rsTowerLimb_rsSetTower_same _ _ _ _ _
    refine ⟨rsSetScalar (rsSetTower rs1 exitCallName ⟨dr, resV⟩) n (towerLimb resV 0),
      envAgreesT_extend hn hnA hsr hdr hag2, ret_setScalar hn _ hret2, fun bC rs' h => ?_⟩
    have hset := RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) n
      (.SLimb exitCallName 0) (rsSetTower rs1 exitCallName ⟨dr, resV⟩)
    rw [hev] at hset
    exact RustExec.seq _ _ _ _ _ hC (RustExec.seq _ _ _ _ _ hset h)
  · have hty : exitArgsAt A dt args = true → ∀ p ∈ argList, p.1 = dt := by
      intro hat p hp
      obtain ⟨a, ha, hap⟩ := List.mem_filterMap.mp hp
      obtain ⟨v, hv⟩ := forall₂_rsTower_typed hF1 a ha
      rw [hv, Option.some.injEq] at hap
      subst hap
      exact hloc hat a ha
    have hbrR := hT hnA ls argList default hF2 hty ⟨ctx, hm⟩ htys
    refine ⟨rsSetTower (rsSetTower rs1 exitCallName ⟨dr, resV⟩) n ⟨dr, resV⟩,
      envAgreesT_extend_tower hn hnA hcf hbrR hag2, hret2,
      fun bC rs' h => ?_⟩
    refine RustExec.seq _ _ _ _ _ hC (RustExec.seq _ _ _ _ _ ?_ h)
    exact RustExec.copy ⟨n, dr⟩ ⟨exitCallName, dr⟩ _ rfl resV
      (locatedLookup_of_rsTower _ _ _ _ (CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _))

/-- The head of a call marshalling its scalar arguments at `dt` into a result slot of type
    `dr`, under the leaf condition of `f` at `dr` for the placement of the bound name. -/
theorem headT_callAt {D DO : String → Option TowerType}
    {DA : String → Option (List TowerType × TowerType)} (hL : ExitLeaves bi leafSpec br D DO DA)
    {env : Env} {rs : RustState}
    {n f : String} {dt dr : TowerType} {args : List ImpExpr} {k : LowCT → LowCT}
    {vals : List Value} {r : Value}
    (hT : A.lookup n = some dr → LeafCallAgreesArgsLen bi leafSpec f dr br vals.length)
    (hS : A.lookup n = none → LeafCallScalar bi leafSpec f dr br)
    (hk : callHeadAt A n f dt dr args = some k) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi f vals = some r) (hag : envAgreesT br A env rs)
    {q : Nat} (hret : rs.rsScalar exitRetName = q) :
    HeadResT N leafSpec br A env rs n r k q :=
  headT_callAtR hL (hL.plain _ _ _ hbi)
    (fun h ls argList oldV hF2 _ _ _ => hT h ls vals argList oldV r rfl hbi hF2)
    (fun h ls argList oldV hF2 _ _ => hS h ls vals argList oldV r hbi hF2) hk hn hargs hF hag hret

/-- `headT_callAt` for arguments held in towers at `dt` (`exitArgsAt`), under the leaf
    condition of `f` on argument slots of the type `dt`. -/
theorem headT_callAtTyped {D DO : String → Option TowerType}
    {DA : String → Option (List TowerType × TowerType)}
    (hL : ExitLeaves bi leafSpec br D DO DA) {env : Env} {rs : RustState}
    {n f : String} {dt dr : TowerType} {args : List ImpExpr} {k : LowCT → LowCT}
    {vals : List Value} {r : Value} (hat : exitArgsAt A dt args = true)
    (hT : A.lookup n = some dr → LeafCallAgreesArgsAt bi leafSpec f dr br vals.length dt)
    (hS : A.lookup n = none → LeafCallScalar bi leafSpec f dr br)
    (hk : callHeadAt A n f dt dr args = some k) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi f vals = some r) (hag : envAgreesT br A env rs)
    {q : Nat} (hret : rs.rsScalar exitRetName = q) :
    HeadResT N leafSpec br A env rs n r k q :=
  headT_callAtR hL (hL.plain _ _ _ hbi)
    (fun h ls argList oldV hF2 hty _ _ => hT h ls vals argList oldV r rfl (hty hat) hbi hF2)
    (fun h ls argList oldV hF2 _ _ => hS h ls vals argList oldV r hbi hF2) hk hn hargs hF hag hret

/-- Every head of `appHeadT` satisfies `HeadResT` at the builtin's value. -/
theorem headT_app (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A)) {env : Env}
    {rs : RustState}
    {n f : String} {args : List ImpExpr} {k : LowCT → LowCT} {vals : List Value} {r : Value}
    (hk : appHeadT A n f args = some k) (hn : exitReserved n = false)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi f vals = some r) (hag : envAgreesT br A env rs)
    {q : Nat} (hret : rs.rsScalar exitRetName = q) :
    HeadResT N leafSpec br A env rs n r k q := by
  unfold appHeadT at hk
  rcases hso : scalarOpHeadT A n f args with _ | se
  · rw [hso] at hk
    simp only at hk
    split_ifs at hk with hfi hfu hfl hfr
    · subst hfi
      exact headT_index hL hk hn hargs hF hbi hag hret
    · subst hfu
      exact headT_update hL hk hn hargs hF hbi hag hret
    · subst hfl
      obtain ⟨c, hnA, ⟨hlen, hmo, hat⟩, hc⟩ := arrLitHeadN_some A hk
      rw [hF.length_eq] at hlen
      exact headT_callAtTyped hL hat (fun _ => hL.arrLitN c _ hlen hmo)
        (fun h => by rw [hnA] at h; cases h) hc hn hargs hF hbi hag hret
    · obtain ⟨v, l, -, -, rfl, -⟩ := repeatHeadT_some A hk
      simp [exitArgsOk] at hargs
    · obtain ⟨dt, dr, hc, hcase⟩ := callHeadT_some A hk
      rcases hcase with ⟨hsc, hnA, rfl⟩ | ⟨hsc, hce, hd, hdo, hnone⟩ | ⟨hsc, hce, -, hnA, rfl⟩ |
          ⟨ts, hsc, hca, rfl, hmts, hnone⟩
      · exact headT_callAt hL (fun h => by rw [hnA] at h; cases h)
          (fun _ => hL.callSR hsc (callHeadT_admits A hk)) hc hn hargs hF hbi hag hret
      · refine headT_callAt hL
          (fun _ => leafCallAgreesArgsLen_of (hL.callD f dr hd hdo hce hsc hfi hfu hfl hfr) _)
          (fun h0 => ?_) hc hn hargs hF hbi hag hret
        obtain rfl := hnone h0
        exact hL.wordD f hd hce hsc hfi hfu hfl hfr
      · exact headT_callAt hL
          (fun _ => leafCallAgreesArgsLen_of (hL.callT f hsc hfi hfu hfl hfr hce) _)
          (fun h => by rw [hnA] at h; cases h) hc hn hargs hF hbi hag hret
      · have hts : ∀ (ls : List Located) (argList : List (Σ t : TowerType, RustVal t)),
            (∃ ctx, callMarshal A .TU64 args = some (ctx, ls)) →
            argList.map (·.1) = ls.map (·.locDst) → argList.map (·.1) = ts := by
          intro ls argList ⟨ctx, hm⟩ hty
          rw [hm] at hmts
          simp only [Option.map_some, Option.some.injEq] at hmts
          rw [hty, hmts]
        refine headT_callAtR hL (hL.plain _ _ _ hbi)
          (fun _ ls argList oldV hF2 _ hm hty =>
            hL.callA f ts dr hca hsc hfi hfu hfl hfr ls vals argList oldV r
              (hts ls argList hm hty) hbi hF2)
          (fun h0 ls argList oldV hF2 hm hty => ?_) hc hn hargs hF hag hret
        obtain rfl := hnone h0
        exact hL.wordA f ts hca hsc hfi hfu hfl hfr ls vals argList oldV r
          (hts ls argList hm hty) hbi hF2
  · rw [hso] at hk
    simp only [Option.some.injEq] at hk
    subst hk
    exact headT_scalarOp hL hso hn hargs hF hbi hag hret

/-- The head of `let n = repeat(v, l)` with a literal count: `HeadResT` at the builtin's
    value on the value of `v` and the value of `l`. -/
theorem headT_repeat (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A)) {env : Env}
    {rs : RustState} {n v : String} {l : ImpLit} {k : LowCT → LowCT} {vv r : Value}
    (hk : repeatHeadT A n [.var v, .lit l] = some k) (hn : exitReserved n = false)
    (hvr : exitReserved v = false) (hv : env v = some vv)
    (hbi : bi "repeat" [vv, Value.ofLit l] = some r) (hag : envAgreesT br A env rs)
    {q : Nat} (hret : rs.rsScalar exitRetName = q) :
    HeadResT N leafSpec br A env rs n r k q := by
  obtain ⟨v', l', c, kN, hargs, hnA, hkN, ⟨hlen, hmo⟩, hc⟩ := repeatHeadT_some A hk
  simp only [List.cons.injEq, ImpExpr.var.injEq, ImpExpr.lit.injEq, and_true] at hargs
  obtain ⟨rfl, rfl⟩ := hargs
  refine headT_callAtR hL (hL.plain _ _ _ hbi)
    (fun _ ls argList oldV hF2 _ _ _ =>
      hL.repeatN c kN hlen hmo ls vv _ r argList oldV hkN hbi hF2)
    (fun h => by rw [hnA] at h; cases h) hc hn (by simp [exitArgsOk, hvr])
    (List.Forall₂.cons ⟨_, rfl, hv⟩ List.Forall₂.nil) hag hret

theorem exitReserved_optTag : exitReserved exitOptTagName = true := by decide
theorem exitReserved_optPay : exitReserved exitOptPayName = true := by decide
theorem exitReserved_optTagS : exitReserved exitOptTagS = true := by decide
theorem exitOptTagS_ne_ret : exitOptTagS ≠ exitRetName := by decide

theorem exitOptTagName_ne_marshal (x : String) : exitOptTagName ≠ exitMarshalName x := by
  intro h
  have h' := congrArg (fun s => s.toList.take 8) h
  simp only [exitMarshalName, String.toList_append] at h'
  rw [List.take_append_of_le_length (by decide)] at h'
  revert h'; decide

theorem exitOptPayName_ne_marshal (x : String) : exitOptPayName ≠ exitMarshalName x := by
  intro h
  have h' := congrArg (fun s => s.toList.take 8) h
  simp only [exitMarshalName, String.toList_append] at h'
  rw [List.take_append_of_le_length (by decide)] at h'
  revert h'; decide

/-- **The call of an `Option` match.** From a state agreeing with `env`, the call
    `optCallC f t ctx ls` of `optHeadT` on argument variables holding `vals` with
    `bi f vals = some vRes`, under `LeafCallOption` of `f` at `t`, runs to a state agreeing
    with `env`, with the exit flag kept, in which the builtin's result is an `Option` whose
    tag is the scalar slot `exitOptTagS` and whose payload agrees with the tower slot
    `exitOptPayName` by `optPayloadRel`. -/
theorem optCall_sim {D DO : String → Option TowerType}
    {DA : String → Option (List TowerType × TowerType)} (hL : ExitLeaves bi leafSpec br D DO DA)
    {env : Env} {rs : RustState} {f : String} {t : TowerType} {ctx : LowCT → LowCT}
    {ls : List Located} {args : List ImpExpr} {vals : List Value} {vRes : Value}
    (hm : callMarshal A .TU64 args = some (ctx, ls)) (hlc : LeafCallOption bi leafSpec f t br)
    (hargs : exitArgsOk args = true)
    (hF : List.Forall₂ (fun e v => ∃ x, e = ImpExpr.var x ∧ env x = some v) args vals)
    (hbi : bi f vals = some vRes) (hag : envAgreesT br A env rs) :
    ∃ o rs2, vRes = .option o ∧ RustExec N leafSpec (optCallC f t ctx ls) rs rs2 ∧
      envAgreesT br A env rs2 ∧ rs2.rsScalar exitRetName = rs.rsScalar exitRetName ∧
      rs2.rsScalar exitOptTagS = (if o.isSome then 1 else 0) ∧
      ∀ w, o = some w → w.isControlFlow = false ∧
        ∃ payOut, rs2.rsTower exitOptPayName = some ⟨t, payOut⟩ ∧ optPayloadRel br t w payOut := by
  let rs0 := rsSetTower (rsSetTower rs exitOptTagName ⟨.TU64, default⟩) exitOptPayName
    ⟨t, default⟩
  have hT0 : ∀ y, exitReserved y = false → rs0.rsTower y = rs.rsTower y := fun y hy => by
    simp only [rs0]
    rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _
        (ne_of_reserved hy exitReserved_optPay).symm,
      CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _
        (ne_of_reserved hy exitReserved_optTag).symm]
  obtain ⟨rs1, hex, hS1, hT1, -, hF1'⟩ :=
    callMarshal_sim N leafSpec hag hL.marshal .TU64 args ctx ls vals hm hargs hF rs0 rfl hT0
  have hF1 : List.Forall₂ (fun v (a : Located) => ∃ val,
      rs1.rsTower a.locVar = some ⟨a.locDst, val⟩ ∧ br a.locDst v val) vals ls :=
    hF1'.imp fun _ _ h => by
      obtain ⟨val, h1, h2, -⟩ := h
      exact ⟨val, h1, h2⟩
  have htag1 : rs1.rsTower exitOptTagName = some ⟨.TU64, default⟩ := by
    rw [hT1 _ (fun z => exitOptTagName_ne_marshal z)]
    simp only [rs0]
    rw [CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_other _ _ _ _ (by decide)]
    exact CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _
  have hpay1 : rs1.rsTower exitOptPayName = some ⟨t, default⟩ := by
    rw [hT1 _ (fun z => exitOptPayName_ne_marshal z)]
    exact CatCrypt.Crypto.Jasmin.LowCT.rsSetTower_same _ _ _
  let argList := ls.filterMap fun a => rs1.rsTower a.locVar
  let dests : List Located := [⟨exitOptTagName, .TU64⟩, ⟨exitOptPayName, t⟩]
  let rs2 := CatCrypt.Crypto.Jasmin.LowCT.callNUpdate leafSpec f (ls.map (·.locDst)) argList 0
    dests rs1
  have hcall : RustExec N leafSpec (.RCallN f dests ls) rs1 rs2 :=
    RustExec.callN f dests ls rs1 argList rfl (forall₂_rsTower_typed hF1) (by
      intro d hd
      simp only [dests, List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ⟨_, htag1⟩
      · exact ⟨_, hpay1⟩)
  have hnd : (dests.map (·.locVar)).Nodup := by simp [dests, exitOptTagName, exitOptPayName]
  let tagOut := leafSpec.call (CatCrypt.Crypto.Jasmin.LowCT.callNLeafName f 0) .TU64
    (ls.map (·.locDst)) ((CatCrypt.Crypto.Jasmin.LowCT.locatedLookup rs1
      ⟨exitOptTagName, .TU64⟩).getD default) argList
  let payOut := leafSpec.call (CatCrypt.Crypto.Jasmin.LowCT.callNLeafName f 1) t
    (ls.map (·.locDst)) ((CatCrypt.Crypto.Jasmin.LowCT.locatedLookup rs1
      ⟨exitOptPayName, t⟩).getD default) argList
  have htag2 : rs2.rsTower exitOptTagName = some ⟨.TU64, tagOut⟩ :=
    CatCrypt.Crypto.Jasmin.LowCT.rsTower_callNUpdate_nth leafSpec f _ argList dests 0 0 rs1
      ⟨exitOptTagName, .TU64⟩ hnd rfl
  have hpay2 : rs2.rsTower exitOptPayName = some ⟨t, payOut⟩ :=
    CatCrypt.Crypto.Jasmin.LowCT.rsTower_callNUpdate_nth leafSpec f _ argList dests 0 1 rs1
      ⟨exitOptPayName, t⟩ hnd rfl
  have hS2 : rs2.rsScalar = rs.rsScalar := by
    rw [CatCrypt.Crypto.Jasmin.LowCT.callNUpdate_rsScalar]; exact hS1
  have hT2 : ∀ y, exitReserved y = false → rs2.rsTower y = rs.rsTower y := fun y hy => by
    rw [CatCrypt.Crypto.Jasmin.LowCT.rsTower_callNUpdate_other _ _ _ _ _ _ _ _ (by
        simp only [dests, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false, not_or]
        exact ⟨ne_of_reserved hy exitReserved_optTag, ne_of_reserved hy exitReserved_optPay⟩),
      hT1 y (ne_marshal_of_nonreserved hy), hT0 y hy]
  have hag2 : envAgreesT br A env rs2 := envAgreesT_of_eqOn hS2 hT2 hag
  obtain ⟨o, rfl, htag, hpay⟩ := hlc ls vals argList _ _ vRes hbi (forall₂_filterMap_rsTower hF1)
  let rs3 := rsSetScalar rs2 exitOptTagS (towerLimb tagOut 0)
  have hev : (SExpr.SLimb exitOptTagName 0).evalState rs2 = towerLimb tagOut 0 := by
    simp only [SExpr.evalState, CatCrypt.Crypto.Jasmin.LowCT.rsTowerLimb, htag2]
  refine ⟨o, rs3, rfl, ?_, envAgreesT_set_reserved _ exitReserved_optTagS hag2, ?_, ?_,
    fun w hw => ⟨(hpay w hw).1, payOut, hpay2, (hpay w hw).2⟩⟩
  · have hset := RustExec.scalarSetExpr (N := N) (leafSpec := leafSpec) exitOptTagS
      (.SLimb exitOptTagName 0) rs2
    rw [hev] at hset
    exact RustExec.seq _ _ _ _ _ (RustExec.letZero _ _ _ _ _ (RustExec.letZero _ _ _ _ _
      (hex _ _ hcall))) hset
  · show (rsSetScalar rs2 exitOptTagS _).rsScalar exitRetName = _
    rw [rsScalar_rsSetScalar, if_neg exitOptTagS_ne_ret.symm, hS2]
  · show (rsSetScalar rs2 exitOptTagS _).rsScalar exitOptTagS = _
    rw [rsScalar_rsSetScalar, if_pos rfl]
    exact htag

theorem head_app (hL : ExitLeaves bi leafSpec br (exitCallTys A) (exitOptTys A) (exitCalleeTys A)) (n f : String)
    (args : List ImpExpr)
    (body : ImpExpr) : HeadSimT bi N leafSpec br A R n (.app f args) body := by
  intro tl il fuel env env' o rs k hok hk hrun hval hag hret
  have hh : exitReserved n = false ∧ exitArgsOkT f args = true := by
    cases tl <;> cases il <;>
      (simp only [exitSimOkT, Bool.and_eq_true, Bool.not_eq_true'] at hok
       exact ⟨hok.1.1.1, hok.1.1.2⟩)
  obtain ⟨hn, hargsT⟩ := hh
  have hk' : appHeadT A n f args = some k := hk
  by_cases hargs : exitArgsOk args = true
  · obtain ⟨vals, r, hF, hbi, hrun'⟩ :=
      letBind_app_inv bi fuel hL.plain n f args body hargs env env' o hrun hval
    obtain ⟨rs1, hag1, hret1, hex⟩ := headT_app hL hk' hn hargs hF hbi hag hret
    exact ⟨_, rs1, hrun', hag1, hret1, hex⟩
  · have hrep : f = "repeat" ∧ exitRepeatArgsOk args = true := by
      simpa [exitArgsOkT, hargs] using hargsT
    obtain ⟨rfl, hra⟩ := hrep
    match args, hra with
    | [.var v, .lit l], hra =>
      simp only [exitRepeatArgsOk, Bool.and_eq_true, Bool.not_eq_true'] at hra
      obtain ⟨vv, r, hv, hbi, hrun'⟩ :=
        letBind_repeat_inv bi fuel hL.plain n v l body env env' o hrun hval
      have hkr : repeatHeadT A n [.var v, .lit l] = some k := by
        simpa [appHeadT, scalarOpHeadT] using hk'
      obtain ⟨rs1, hag1, hret1, hex⟩ := headT_repeat hL hkr hn hra.1 hv hbi hag hret
      exact ⟨_, rs1, hrun', hag1, hret1, hex⟩

end Heads

end CatCrypt.Crypto.Hax
