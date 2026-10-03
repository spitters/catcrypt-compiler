/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
public import CatCrypt.Crypto.SecureCompilation.VIR.PassChain

/-!
# Bounds-driven operation selection over `Com jasminDialect`

Rewrites of a binding that hold for all operands within their intervals, run by one
`Com → Com` pass that carries, at each binding, the abstract environment of the range stage
(`ComPipeline.stageAbs`: an interval and a symbolic fact per variable) and the definition
table of the acyclic e-graph (`AegraphGeneric.Defs`: the operation and argument levels of
the node defining each level).

A rule (`BRule`) maps an expression, the abstract environment `A` and the definition table
`D` to an optional replacement, with soundness stated against the denotation under
`EnvOK A V` (every variable lies in its interval) and `DSound V D` (every recorded node
evaluates to the value at its level). The rules of `boundsRules` are

* `castElimRule`: the zero extension `castW w W y` of a truncation `y = castW W w a` is the
  copy of `a` when the interval of `a` lies below `2^w` (in particular when `W ≤ w`, the
  truncation of a zero extension back to its source width);
* `narrowOpRule`: the truncation `castW W w y` of a wide operation
  `y = a' ∘ b'` over `reg W` whose operands are zero extensions `a' = castW w W a`,
  `b' = castW w W b` is the narrow operation `a ∘ b` over `reg w`, for `∘` among `add`,
  `sub`, `mul`, `and`, `or`, `xor` and `w ≤ W` (a wide multiplication of zero-extended
  operands read at the narrow width is the narrow multiplication);
* `rangeStageRule`: the rewrites of the range stage `ComPipeline.rangeExpr`, among them a
  high multiply whose operand intervals bound it to `0` (a multiplication whose operands
  fit half the width), a carry-out `addCarryHi` that the intervals exclude (an add with no
  carry), a mask of an operand already in range, a multiply by `1` and a carry-chain add at
  carry-in `0`.

The pass `boundsCom` runs from an abstract environment of the inputs; `boundsOpt` runs from
the full lane range of every input and denotes its input at every valuation, and
`boundsOptFrom ivs` runs from input intervals `ivs` and denotes its input at every valuation
whose register inputs lie in `ivs`.

The rule `Rule` of `AegraphGeneric` reads only the definition table, and its soundness
quantifies over every valuation for which the table is sound; it has no argument for the
intervals of the variables and no hypothesis on the valuation from which an interval-dependent
side condition could be discharged. The rules here therefore run in their own pass.

## Main definitions

* `BRule`: a rewrite conditional on operand intervals and recorded definitions.
* `castElimRule`, `narrowOpRule`, `rangeStageRule`, `boundsRules`: the rules.
* `boundsCom`, `boundsOpt`, `boundsOptFrom`: the pass.
* `boundsStep`, `boundsCert`: the pass as a `PassChain` step and its certificate.

## Main results

* `setWidth_setWidth_of_lt`, `setWidth_apply_setWidth`: the `BitVec` identities of the cast
  rules.
* `castElimRule`, `narrowOpRule`, `rangeStageRule` carry their soundness (`BRule.sound`).
* `boundsCom_denote`: under an environment and a definition table that hold of `V`, the
  pass denotes its input at `V`.
* `boundsOpt_denote`: `boundsOpt c` denotes the same function as `c`.
* `boundsOptFrom_denote`: `boundsOptFrom ivs c` denotes `c` at every valuation whose register
  inputs lie in `ivs`.
* `boundsCert`: the certificate of the step at every semantics that reads a program through
  its denotation.
* `castElimOp_roundTrip`, `boundsCom_castRoundTrip`: the truncation of a zero extension back
  to its source width is replaced by a copy of the source, in every program of that shape.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.BoundsRules

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange
open CatCrypt.Crypto.Optimizer.Rewrite.AegraphGeneric
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph (binE)
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline (stageAbs stageAbs_sound rangeExpr
  rangeExpr_denote topEnv envOK_topEnv)

/-! ## 1. `BitVec` identities -/

/-- The zero extension of the truncation to `w` bits of a word below `2^w` is the word. -/
theorem setWidth_setWidth_of_lt {w W : Nat} (a : BitVec W) (h : a.toNat < 2 ^ w) :
    (a.setWidth w).setWidth W = a := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]

/-- The operations that commute with truncation: `add`, `sub`, `mul`, `and`, `or`, `xor`. -/
def narrowable : JasminBinOp → Bool
  | .add | .sub | .mul | .and | .or | .xor => true
  | _ => false

/-- The truncation to `w ≤ W` bits of an operation that commutes with truncation, applied to
    the zero extensions of two `w`-bit words, is the operation on the words. -/
theorem setWidth_apply_setWidth {w W : Nat} (h : w ≤ W) {bop : JasminBinOp}
    (hb : narrowable bop = true) (a b : BitVec w) :
    (bop.apply (a.setWidth W) (b.setWidth W)).setWidth w = bop.apply a b := by
  cases bop <;> simp only [narrowable, reduceCtorEq] at hb <;>
    simp only [JasminBinOp.apply]
  · simp [BitVec.setWidth_add _ _ h, BitVec.setWidth_setWidth_of_le _ h]
  · rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ h,
      BitVec.setWidth_neg_of_le h]
    simp [BitVec.setWidth_setWidth_of_le _ h]
  · rw [BitVec.setWidth_mul _ _ h, BitVec.setWidth_setWidth_of_le _ h,
      BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq, BitVec.setWidth_eq]
  · simp [BitVec.setWidth_setWidth_of_le _ h]
  · simp [BitVec.setWidth_setWidth_of_le _ h]
  · simp [BitVec.setWidth_setWidth_of_le _ h]

/-! ## 2. Reading the definition table -/

section Defs

variable {Γ : JCtxt} {V : Ctxt.Valuation Γ}

theorem gatherArgs_one {t1 : JasminTy} {l1 : Nat} {v1 : Ctxt.Var Γ t1}
    (h1 : varOfLvl? Γ t1 l1 = some v1) :
    gatherArgs V [t1] [l1] = some (.cons (v1.lookup V) .nil) := by
  simp [gatherArgs, varOfLvl?_lookup h1 V, castTo?]

theorem gatherArgs_two {t1 t2 : JasminTy} {l1 l2 : Nat} {v1 : Ctxt.Var Γ t1}
    {v2 : Ctxt.Var Γ t2} (h1 : varOfLvl? Γ t1 l1 = some v1)
    (h2 : varOfLvl? Γ t2 l2 = some v2) :
    gatherArgs V [t1, t2] [l1, l2] = some (.cons (v1.lookup V) (.cons (v2.lookup V) .nil)) := by
  simp [gatherArgs, varOfLvl?_lookup h1 V, varOfLvl?_lookup h2 V, castTo?]

/-- The node `castW w W` at the level of a variable `a` evaluates to the zero extension of
    the value of `a`. -/
theorem evalKey_castW {w W : Nat} {la : Nat} {a : Ctxt.Var Γ (.reg w)}
    (ha : varOfLvl? Γ (.reg w) la = some a) :
    evalKey V (.castW w W) [la] = some ⟨.reg W, (a.lookup V).setWidth W⟩ := by
  unfold evalKey
  erw [gatherArgs_one ha]
  rfl

/-- The node `regArith bop W` at the levels of `x` and `y` evaluates to `bop` on their
    values. -/
theorem evalKey_regArith {W : Nat} (bop : JasminBinOp) {lx ly : Nat}
    {x y : Ctxt.Var Γ (.reg W)} (hx : varOfLvl? Γ (.reg W) lx = some x)
    (hy : varOfLvl? Γ (.reg W) ly = some y) :
    evalKey V (.regArith bop W) [lx, ly] = some ⟨.reg W, bop.apply (x.lookup V) (y.lookup V)⟩ := by
  unfold evalKey
  erw [gatherArgs_two hx hy]
  rfl

/-- Under a definition table sound for `V`, the value at a recorded level is the value of
    its recorded node. -/
theorem dsound_at {D : Defs jasminDialect} (hD : DSound V D) {l : Nat} {op : JasminOp}
    {lv : List Nat} (hp : D[l]? = some (op, lv)) {s : JasminTy} {z z' : ⟦s⟧}
    (hl : getLvl V l = some ⟨s, z'⟩) (hz : evalKey V op lv = some ⟨s, z⟩) : z' = z := by
  obtain ⟨x, h1, h2⟩ := hD l _ hp
  rw [hz] at h1
  cases h1
  rw [hl] at h2
  simpa using h2

end Defs

/-! ## 3. Rules conditional on operand intervals -/

/-- **A bounds rule**: an optional replacement of an expression, read from the abstract
    environment `A` and the definition table `D`, which denotes the expression at every
    valuation for which `A` and `D` hold. -/
structure BRule where
  /-- The replacement of an expression, when the rule fires. -/
  apply : {Γ : JCtxt} → AEnv Γ → Defs jasminDialect → {t : JasminTy} →
    Expr jasminDialect Γ t → Option (Expr jasminDialect Γ t)
  /-- Soundness: under `EnvOK A V` and `DSound V D`, the replacement denotes the
      expression. -/
  sound : ∀ {Γ : JCtxt} (A : AEnv Γ) (D : Defs jasminDialect) (V : Ctxt.Valuation Γ),
    EnvOK A V → DSound V D → ∀ {t : JasminTy} (e e' : Expr jasminDialect Γ t),
    apply A D e = some e' → e'.denote V = e.denote V

section Rules

variable {Γ : JCtxt}

/-- The cast elimination on an operation: `castW w W y` with `y` recorded as `castW W w a`
    becomes the copy `a ||| a` when `W ≤ w` or the lane interval of `a` lies below `2^w`. -/
def castElimOp (A : AEnv Γ) (D : Defs jasminDialect) (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op)) :
    Option (Expr jasminDialect Γ (DialectSignature.ret (d := jasminDialect) op)) :=
  match op, args with
  | .castW w W, args =>
    let y : Ctxt.Var Γ (.reg w) := args.head
    match D[varLvl y]? with
    | some (.castW W' w', [la]) =>
      if W' = W ∧ w' = w then
        match varOfLvl? Γ (.reg W) la with
        | some a =>
          if W ≤ w ∨ (ivLane W (hget A a).1).2 < 2 ^ w then some (binE .or a a) else none
        | none => none
      else none
    | _ => none
  | _, _ => none

theorem castElimOp_sound {A : AEnv Γ} {D : Defs jasminDialect} {V : Ctxt.Valuation Γ}
    (hA : EnvOK A V) (hD : DSound V D) (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op))
    {e' : Expr jasminDialect Γ (DialectSignature.ret (d := jasminDialect) op)}
    (h : castElimOp A D op args = some e') :
    e'.denote V = DialectDenote.denote op (Expr.lookupArgs args V) := by
  cases op
  case castW w W =>
    match args with
    | .cons y .nil =>
    simp only [castElimOp, HVector.head] at h
    split at h
    · rename_i W' w' la hp
      split_ifs at h with hc
      obtain ⟨h1, h2⟩ := hc
      subst W' w'
      split at h
      · rename_i a ha
        split_ifs at h with hb
        cases h
        have hy : y.lookup V = (a.lookup V).setWidth w :=
          dsound_at hD hp (getLvl_var y V) (evalKey_castW ha)
        have hlt : (a.lookup V).toNat < 2 ^ w := by
          rcases hb with hb | hb
          · exact Nat.lt_of_lt_of_le (a.lookup V).isLt (Nat.pow_le_pow_right (by omega) hb)
          · have h2 := (Iv.mem_lane (hA.reg a).1).2
            have h3 : ((a.lookup V).toNat : Int) < ((2 ^ w : Nat) : Int) := by
              push_cast; exact lt_of_le_of_lt h2 hb
            exact_mod_cast h3
        show regVal V a ||| regVal V a = (y.lookup V).setWidth W
        rw [hy, BitVec.or_self]
        exact (setWidth_setWidth_of_lt _ hlt).symm
      · cases h
    · cases h
  all_goals simp [castElimOp] at h

/-- The narrowing on an operation: `castW W w y` with `w ≤ W`, `y` recorded as
    `regArith bop W x y'` and `x`, `y'` recorded as `castW w W a`, `castW w W b`, becomes
    `regArith bop w a b` for `bop` among `add`, `sub`, `mul`, `and`, `or`, `xor`. -/
def narrowOp (D : Defs jasminDialect) (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op)) :
    Option (Expr jasminDialect Γ (DialectSignature.ret (d := jasminDialect) op)) :=
  match op, args with
  | .castW W w, args =>
    let y : Ctxt.Var Γ (.reg W) := args.head
    if w ≤ W then
      match D[varLvl y]? with
      | some (.regArith bop W', [lx, ly]) =>
        if narrowable bop ∧ W' = W then
          match D[lx]?, D[ly]? with
          | some (.castW wa Wa, [la]), some (.castW wb Wb, [lb]) =>
            if wa = w ∧ Wa = W ∧ wb = w ∧ Wb = W then
              match varOfLvl? Γ (.reg W) lx, varOfLvl? Γ (.reg W) ly,
                varOfLvl? Γ (.reg w) la, varOfLvl? Γ (.reg w) lb with
              | some _, some _, some a, some b => some (binE bop a b)
              | _, _, _, _ => none
            else none
          | _, _ => none
        else none
      | _ => none
    else none
  | _, _ => none

theorem narrowOp_sound {D : Defs jasminDialect} {V : Ctxt.Valuation Γ}
    (hD : DSound V D) (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op))
    {e' : Expr jasminDialect Γ (DialectSignature.ret (d := jasminDialect) op)}
    (h : narrowOp D op args = some e') :
    e'.denote V = DialectDenote.denote op (Expr.lookupArgs args V) := by
  cases op
  case castW W w =>
    match args with
    | .cons y .nil =>
    simp only [narrowOp, HVector.head] at h
    split_ifs at h with hw
    split at h
    · rename_i bop W' lx ly hp
      split_ifs at h with hc
      obtain ⟨hb, h1⟩ := hc
      subst W'
      split at h
      · rename_i wa Wa la wb Wb lb hpx hpy
        split_ifs at h with hc2
        obtain ⟨h2, h3, h4, h5⟩ := hc2
        subst wa Wa wb Wb
        split at h
        · rename_i x y' a b hx hy' ha hb'
          cases h
          have hyv : y.lookup V = bop.apply (x.lookup V) (y'.lookup V) :=
            dsound_at hD hp (getLvl_var y V) (evalKey_regArith bop hx hy')
          have hxv : x.lookup V = (a.lookup V).setWidth W :=
            dsound_at hD hpx (varOfLvl?_lookup hx V) (evalKey_castW ha)
          have hyv' : y'.lookup V = (b.lookup V).setWidth W :=
            dsound_at hD hpy (varOfLvl?_lookup hy' V) (evalKey_castW hb')
          show bop.apply (a.lookup V) (b.lookup V) = (y.lookup V).setWidth w
          rw [hyv, hxv, hyv', setWidth_apply_setWidth hw hb]
        · cases h
      · cases h
    · cases h
  all_goals simp [narrowOp] at h

end Rules

/-- **Cast elimination**: the zero extension of a truncation, when the truncated word lies
    below the truncation width. -/
def castElimRule : BRule where
  apply A D _ e := (castElimOp A D e.op e.args).map fun e' => e.retTy_eq ▸ e'
  sound A D V hA hD _ e e' h := by
    rcases e with ⟨op, rfl, args⟩
    obtain ⟨e'', he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact castElimOp_sound hA hD op args he

/-- **Narrow operation selection**: the truncation of a wide operation on zero extensions. -/
def narrowOpRule : BRule where
  apply _ D _ e := (narrowOp D e.op e.args).map fun e' => e.retTy_eq ▸ e'
  sound A D V _ hD _ e e' h := by
    rcases e with ⟨op, rfl, args⟩
    obtain ⟨e'', he, rfl⟩ := Option.map_eq_some_iff.mp h
    exact narrowOp_sound hD op args he

/-- **Range rewrites**: `ComPipeline.rangeExpr`, the point rule and the rewrites of the range
    pass, as one rule. -/
def rangeStageRule : BRule where
  apply {Γ} A _ _ e := some (rangeExpr A Γ.length e)
  sound A _ V hA _ _ e e' h := by
    cases h
    exact rangeExpr_denote hA rfl e

/-- The bounds rules: cast elimination, narrow operation selection, then the range stage. -/
def boundsRules : List BRule := [castElimRule, narrowOpRule, rangeStageRule]

/-! ## 4. The pass -/

/-- The replacement of an expression by the first rule of `R` that fires, or the expression. -/
def applyRules (R : List BRule) {Γ : JCtxt} (A : AEnv Γ) (D : Defs jasminDialect)
    {t : JasminTy} (e : Expr jasminDialect Γ t) : Expr jasminDialect Γ t :=
  (R.findSome? fun r => r.apply A D e).getD e

theorem applyRules_denote (R : List BRule) {Γ : JCtxt} {A : AEnv Γ} {D : Defs jasminDialect}
    {V : Ctxt.Valuation Γ} (hA : EnvOK A V) (hD : DSound V D) {t : JasminTy}
    (e : Expr jasminDialect Γ t) : (applyRules R A D e).denote V = e.denote V := by
  unfold applyRules
  cases hf : R.findSome? (fun r => r.apply A D e) with
  | none => rfl
  | some e' =>
    obtain ⟨r, -, hr⟩ := List.exists_of_findSome?_eq_some hf
    exact r.sound A D V hA hD e e' hr

/-- **The bounds pass** from the abstract environment `A` and the definition table `D`: each
    binding is replaced by `applyRules R`, and the environment and the table are extended by
    the abstract value and the node of the input binding. -/
def boundsCom (R : List BRule) : {Γ : JCtxt} → {t : JasminTy} → AEnv Γ →
    Defs jasminDialect → Com jasminDialect Γ t → Com jasminDialect Γ t
  | _, _, _, _, .ret v => .ret v
  | Γ, _, A, D, .var e body =>
    .var (applyRules R A D e)
      (boundsCom R (HVector.cons (f := fun _ => AVal) (stageAbs A e) A)
        (D.insert Γ.length (e.op, argLvls e.args)) body)

/-- **Denotation of the bounds pass.** Under an abstract environment and a definition table
    that hold of `V`, the pass denotes its input at `V`. -/
theorem boundsCom_denote (R : List BRule) : ∀ {Γ : JCtxt} {t : JasminTy} (A : AEnv Γ)
    (D : Defs jasminDialect) (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ),
    EnvOK A V → DSound V D → (boundsCom R A D c).denote V = c.denote V
  | _, _, _, _, .ret _, _, _, _ => rfl
  | Γ, _, A, D, .var e body, V, hA, hD => by
    simp only [boundsCom, Com.denote]
    rw [applyRules_denote R hA hD e]
    refine boundsCom_denote R _ _ body _ (hA.cons (stageAbs_sound hA rfl e)) ?_
    exact dsound_insert (dsound_extend _ hD)
      (evalKey_extend_some V _ (evalKey_expr e V)) (getLvl_extend_top V _)

/-- **The bounds stage**: the bounds pass at `boundsRules` from the full lane range of every
    input and the empty definition table. -/
def boundsOpt {Γ : JCtxt} {t : JasminTy} (c : Com jasminDialect Γ t) : Com jasminDialect Γ t :=
  boundsCom boundsRules (topEnv Γ) ∅ c

/-- **Denotation of the bounds stage.** `boundsOpt c` denotes the same function as `c`. -/
theorem boundsOpt_denote {Γ : JCtxt} {t : JasminTy} (c : Com jasminDialect Γ t) :
    (boundsOpt c).denote = c.denote :=
  funext fun V => boundsCom_denote _ _ _ c V (envOK_topEnv V) (dsound_empty V)

/-- The abstract environment of input intervals holds of a valuation whose register inputs
    lie in them. -/
theorem envOK_ofIvs {Γ : JCtxt} (ivs : HVector (fun _ => Iv) Γ) (V : Ctxt.Valuation Γ)
    (hV : ∀ (w : Nat) (v : Ctxt.Var Γ (.reg w)), (hget ivs v).Mem w (v.lookup V)) :
    EnvOK (AEnv.ofIvs ivs) V := by
  intro u v
  rw [hget_ofIvs]
  cases u with
  | reg w => exact ⟨hV w v, SymOK.none _ _ _⟩
  | _ => trivial

/-- The bounds stage from the input intervals `ivs`. -/
def boundsOptFrom {Γ : JCtxt} {t : JasminTy} (ivs : HVector (fun _ => Iv) Γ)
    (c : Com jasminDialect Γ t) : Com jasminDialect Γ t :=
  boundsCom boundsRules (AEnv.ofIvs ivs) ∅ c

/-- **Denotation of the bounds stage from input intervals.** At a valuation whose register
    inputs lie in `ivs`, `boundsOptFrom ivs c` denotes the value of `c`. -/
theorem boundsOptFrom_denote {Γ : JCtxt} {t : JasminTy} (ivs : HVector (fun _ => Iv) Γ)
    (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ)
    (hV : ∀ (w : Nat) (v : Ctxt.Var Γ (.reg w)), (hget ivs v).Mem w (v.lookup V)) :
    (boundsOptFrom ivs c).denote V = c.denote V :=
  boundsCom_denote _ _ _ c V (envOK_ofIvs ivs V hV) (dsound_empty V)

/-! ## 5. The pass as a chain step -/

section Chain

open CatCrypt.Crypto.SecureCompilation.VIR.PassChain

/-- The bounds stage `boundsOpt` on `Com jasminDialect Γ t` as a chain step. -/
def boundsStep (Γ : JCtxt) (t : JasminTy) :
    Step (Com jasminDialect Γ t) (Com jasminDialect Γ t) :=
  ⟨"bounds", fun c => some (boundsOpt c)⟩

/-- **The certificate of the bounds step** at every semantics `S` of programs that reads a
    program only through its denotation: the output has the denotation of its input, from
    `boundsOpt_denote`. -/
def boundsCert {Γ : JCtxt} {t : JasminTy} (S : Sem (Com jasminDialect Γ t))
    (hS : ∀ c c' : Com jasminDialect Γ t, c'.denote = c.denote → S.den c' = S.den c) :
    StepCert (boundsStep Γ t).run S S :=
  StepCert.ofDenoteEq S fun c q hf => by
    cases hf
    exact hS c _ (boundsOpt_denote c)

end Chain

/-! ## 6. Redundant casts -/

/-- The cast elimination fires on the truncation `castW w W y` of a variable `y` recorded as
    the zero extension `castW W w a` of a narrower word, `W ≤ w`: the result is the copy of
    `a`. -/
theorem castElimOp_roundTrip {Γ : JCtxt} (A : AEnv Γ) {D : Defs jasminDialect} {w W : Nat}
    (y : Ctxt.Var Γ (.reg w)) {la : Nat} {a : Ctxt.Var Γ (.reg W)}
    (hy : D[varLvl y]? = some (.castW W w, [la])) (ha : varOfLvl? Γ (.reg W) la = some a)
    (hW : W ≤ w) : castElimOp A D (.castW w W) (.cons y .nil) = some (binE .or a a) := by
  simp [castElimOp, HVector.head, hy, ha, hW]

theorem varOfDepth?_varDepth : ∀ {Δ : JCtxt} {s : JasminTy} (v : Ctxt.Var Δ s),
    varOfDepth? Δ s (varDepth v) = some v
  | _ :: _, _, .here => by simp [varOfDepth?, varDepth]
  | _ :: _, _, .there v => by simp [varOfDepth?, varDepth, varOfDepth?_varDepth v]

/-- The variable at the level of a variable is that variable. -/
theorem varOfLvl?_varLvl {Δ : JCtxt} {s : JasminTy} (v : Ctxt.Var Δ s) :
    varOfLvl? Δ s (varLvl v) = some v := by
  have := varDepth_lt v
  unfold varOfLvl? varLvl
  rw [if_pos (by omega), show Δ.length - 1 - (Δ.length - 1 - varDepth v) = varDepth v by omega]
  exact varOfDepth?_varDepth v

/-- **A redundant cast removed.** In every program that zero-extends a variable `x` from
    `W` to `w ≥ W` bits and truncates the result back to `W` bits, the bounds pass replaces
    the truncation by the copy of `x`, from every abstract environment and definition
    table. -/
theorem boundsCom_castRoundTrip {Γ : JCtxt} {t : JasminTy} (A : AEnv Γ)
    (D : Defs jasminDialect) {w W : Nat} (hW : W ≤ w) (x : Ctxt.Var Γ (.reg W))
    (body : Com jasminDialect (.reg W :: .reg w :: Γ) t) :
    ∃ (e1 : Expr jasminDialect Γ (.reg w)) (body' : Com jasminDialect _ t),
      boundsCom boundsRules A D (.var ⟨.castW W w, rfl, .cons x .nil⟩ <|
          .var ⟨.castW w W, rfl, .cons .here .nil⟩ body) =
        .var e1 (.var (binE .or x.there x.there) body') := by
  simp only [boundsCom]
  have hy : (D.insert Γ.length (JasminOp.castW W w, argLvls (.cons x .nil)))[
      varLvl (Ctxt.Var.here : Ctxt.Var (JasminTy.reg w :: Γ) (JasminTy.reg w))]? =
      some (.castW W w, [varLvl (x.there : Ctxt.Var (JasminTy.reg w :: Γ) (JasminTy.reg W))]) := by
    have h1 : varLvl (Ctxt.Var.here : Ctxt.Var (JasminTy.reg w :: Γ) (JasminTy.reg w)) =
        Γ.length := by
      simp [varLvl, varDepth]
    have h2 : varLvl (x.there : Ctxt.Var (JasminTy.reg w :: Γ) (JasminTy.reg W)) =
        varLvl x := by
      have := varDepth_lt x
      simp only [varLvl, varDepth, List.length_cons]
      omega
    rw [h1, h2, Std.HashMap.getElem?_insert_self]
    rfl
  have hc := castElimOp_roundTrip (HVector.cons (f := fun _ => AVal)
      (stageAbs A ⟨.castW W w, rfl, .cons x .nil⟩) A) .here hy (varOfLvl?_varLvl _) hW
  have h2 : applyRules boundsRules (HVector.cons (f := fun _ => AVal)
      (stageAbs A ⟨.castW W w, rfl, .cons x .nil⟩) A)
      (D.insert Γ.length (JasminOp.castW W w, argLvls (.cons x .nil)))
      (⟨.castW w W, rfl, .cons .here .nil⟩ :
        Expr jasminDialect (JasminTy.reg w :: Γ) (JasminTy.reg W)) =
      binE .or x.there x.there := by
    simp only [applyRules, boundsRules, List.findSome?, castElimRule]
    rw [hc]
    rfl
  rw [h2]
  exact ⟨_, _, rfl⟩

end CatCrypt.Crypto.Optimizer.Rewrite.BoundsRules
