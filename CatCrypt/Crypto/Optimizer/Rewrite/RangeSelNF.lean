/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop
public import CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop
public meta import CatCrypt.Crypto.SecureCompilation.VIR.SelDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.SelDialect

/-!
# Range-conditioned selections of the unsigned minimum and the half-width multiply

The pass `rangeSel` takes a structured program of `jasminDialect` to a program of
`SelDialect.jasminSel`, the scalar dialect with the unsigned minimum `umin` and the
half-width multiply `mulu`. It runs the interval analysis of the range stage
(`ComPipeline.stageAbs`) with the checked loop annotation of `RangeNFLoop` (`CarriedAnn`,
`forInductive`, `whileInductive`, `carriedEnv`) and rewrites two idioms where the range
facts hold. Every other binding is embedded unchanged.

## The two selections

* The conditional add. For a binding `r = d + m` (operands in either order) whose operand
  `m` carries the fact `Sym.mask ℓ ic` of `d`, that is `m = (0 - (d >>> (w - 1))) &&& C` for
  a word `C` with `C.toNat` in `ic`, the rewrite fires when `0 < w`, `ic.2 < 2 ^ (w - 1)`,
  `-ic.1 ≤ id.1` and `id.2 < 2 ^ (w - 1)` for the interval `id` of `d` (the condition of
  `RangeDomain.ivCondAdd?`), and `ic` is one point `n`. In the direct form `d` is bound to
  `x - c` (a recorded subtraction) for a variable `c` whose lane interval is the point `n`,
  and the binding becomes `r = umin x d` (`RangeDomain.condAdd_sub_eq_umin`). Otherwise,
  when the context holds a variable `c` whose lane interval is the point `n`, the binding
  becomes `s = d + c; r = umin d s` (`RangeDomain.condAdd_eq_umin`).
* The half-width multiply. A binding `r = a * b` at width `w` whose operands have lane
  intervals with upper end below `2 ^ (w / 2)` becomes `r = mulu w a b`
  (`SelDialect.halfProd_eq_mul`).

## Form of the traversal

The second form of the conditional add inserts a binding, so the output context of a
continuation differs from its input context. The traversal `selGo` carries a map `VarMap Γ Δ`
from the variables of the input context `Γ` to variables of the output context `Δ`. The
analysis reads the input program only: the abstract environment and the recorded
subtractions refer to levels of the input context.

## Main definitions

* `VarMap`, `VarMap.OK`: a map of variables and the valuations it relates.
* `SubFact`, `SubOK`, `subPush`: recorded subtractions by level and their meaning.
* `condSel`, `halfFits`: the conditions of the two selections.
* `Emit`, `selBind`: the bindings one input binding becomes.
* `selGo`: the traversal.
* `rangeSel`: the pass, the traversal from the full lane range of every input.
* `selStep`, `selCert`: the chain step of the pass for an annotation computed from the
  program, with its certificate.
* `maskedMul`, `offsetCondAdd`: two programs on which the selections fire.

## Main results

* `condSel_sound`: a selected form of the conditional add has the value of the sum.
* `selBind_val`, `selBind_leak`: the bindings of `selBind` give the value of the input
  binding, and its events under a leakage model whose `regArith` operations are quiet.
* `selGo_denote`, `rangeSel_denote`: the output, read in `jasminSel`, denotes what the input
  denotes, at every fuel and for every annotation.
* `selGo_leakRun`, `rangeSel_leakRun`: under a leakage model whose `regArith` operations are
  quiet, the leakage run of the output is the leakage run of the input.
* `rangeSel_ctRel`: two runs of the input with equal events give two runs of the output with
  the same results and equal events.
* On `RangeNFLoop.lazyAddLoop` under `RangeNFLoop.lazyAddAnn` the pass binds one `umin`,
  keeps the number of bindings and lowers the number of `add` bindings from two to one; on
  `maskedMul` the multiply becomes `mulu 64`; on `offsetCondAdd` the second form inserts one
  binding (`#kat`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Rewrite.RangeSelNF

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.Optimizer.Rewrite.ComPipeline
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNF
open CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph (expr_ctLeak_regArith)
open CatCrypt.Crypto.SecureCompilation.VIR.SelDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectOpSum (castVar lookup_castVar)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel LeakKind Expr.ctLeak opLeak)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak

/-! ## 1. Maps of variables -/

/-- A map of the variables of a context of `jasminDialect` to variables of a context of
    `jasminSel`. -/
abbrev VarMap (Γ : JCtxt) (Δ : Ctxt jasminSel) : Type :=
  ∀ t : JasminTy, Ctxt.Var Γ t → Ctxt.Var Δ t

namespace VarMap

variable {Γ : JCtxt} {Δ : Ctxt jasminSel}

/-- The map of a context to itself. -/
def same (Γ : JCtxt) : VarMap Γ Γ := fun _ v => castVar v

/-- The map under one binding kept on both sides. -/
def lift (ρ : VarMap Γ Δ) (s : JasminTy) : VarMap (s :: Γ) (s :: Δ) := fun _ v =>
  match v with
  | .here => .here
  | .there v => .there (ρ _ v)

/-- The map into an output context with one more binding. -/
def skip (ρ : VarMap Γ Δ) (s : JasminTy) : VarMap Γ (s :: Δ) := fun t v => .there (ρ t v)

/-- The map under a prefix of bindings kept on both sides. -/
def liftApp (ρ : VarMap Γ Δ) : (cs : List JasminTy) → VarMap (cs ++ Γ) (cs ++ Δ)
  | [] => ρ
  | s :: cs => lift (liftApp ρ cs) s

/-- The image of an argument vector. -/
def args (ρ : VarMap Γ Δ) : {ts : List JasminTy} → HVector (fun t => Ctxt.Var Γ t) ts →
    HVector (fun t => Ctxt.Var Δ t) ts
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (ρ _ v) (args ρ vs)

/-- The image of each variable reads in `W` the value the variable has in `V`. -/
def OK (ρ : VarMap Γ Δ) (W : Ctxt.Valuation Δ) (V : Ctxt.Valuation Γ) : Prop :=
  ∀ (t : JasminTy) (v : Ctxt.Var Γ t), (ρ t v).lookup W = v.lookup V

variable {ρ : VarMap Γ Δ} {W : Ctxt.Valuation Δ} {V : Ctxt.Valuation Γ}

/-- The map of a context to itself relates a valuation to itself. -/
theorem OK.same (V : Ctxt.Valuation Γ) : OK (same Γ) V V := fun _ v => lookup_castVar v V

/-- A lifted map relates the extensions by one value. -/
theorem OK.lift (h : OK ρ W V) {s : JasminTy} (x : ⟦s⟧) :
    OK (lift ρ s) (W.extend x) (V.extend x) := fun t v => by
  cases v with
  | here => rfl
  | there v => exact h _ v

/-- A map into an output context with one more binding relates every extension of the
    output valuation. -/
theorem OK.skip (h : OK ρ W V) {s : JasminTy} (x : ⟦s⟧) : OK (skip ρ s) (W.extend x) V :=
  fun t v => h t v

/-- A map lifted under a prefix relates the extensions by one tuple. -/
theorem OK.liftApp (h : OK ρ W V) : ∀ (cs : List JasminTy)
    (X : Ctxt.Valuation (d := jasminDialect) cs),
    OK (liftApp ρ cs) (hvAppend (d := jasminSel) X W) (hvAppend (d := jasminDialect) X V)
  | [], .nil => h
  | _ :: cs, .cons x X => OK.lift (OK.liftApp h cs X) x

/-- The image of an argument vector reads in `W` the values of the vector in `V`. -/
theorem OK.args (h : OK ρ W V) : ∀ {ts : List JasminTy}
    (vs : HVector (fun t => Ctxt.Var Γ t) ts),
    Expr.lookupArgs (d := jasminSel) (args ρ vs) W = Expr.lookupArgs vs V
  | [], .nil => rfl
  | _ :: _, .cons v vs => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [h _ v, OK.args h vs]

end VarMap

/-! ## 2. Expressions of `jasminDialect` along a map of variables -/

section Embed

variable {Γ : JCtxt} {Δ : Ctxt jasminSel} {ρ : VarMap Γ Δ} {W : Ctxt.Valuation Δ}
  {V : Ctxt.Valuation Γ}

/-- An expression of `jasminDialect` as an expression of `jasminSel` over the output
    context: the operation tagged `.inl`, the arguments mapped. -/
def selEmbedExpr (ρ : VarMap Γ Δ) {t : JasminTy} (e : Expr jasminDialect Γ t) :
    Expr jasminSel Δ t where
  op := .inl e.op
  retTy_eq := e.retTy_eq
  args := VarMap.args ρ e.args

/-- An embedded expression has the value of the expression. -/
theorem selEmbedExpr_denote (h : VarMap.OK ρ W V) {t : JasminTy} (e : Expr jasminDialect Γ t) :
    (selEmbedExpr ρ e).denote W = e.denote V := by
  obtain ⟨op, rfl, args⟩ := e
  show DialectDenote.denote (d := jasminDialect) op
      (Expr.lookupArgs (d := jasminSel) (VarMap.args ρ args) W) = _
  rw [h.args args]
  rfl

/-- An embedded expression emits the events of the expression. -/
theorem selEmbedExpr_ctLeak (M : LeakModel jasminDialect) (h : VarMap.OK ρ W V) {t : JasminTy}
    (e : Expr jasminDialect Γ t) :
    Expr.ctLeak (jasminSelLeak M) (selEmbedExpr ρ e) W = Expr.ctLeak M e V := by
  show opLeak (jasminSelLeak M) (.inl e.op)
      (Expr.lookupArgs (d := jasminSel) (VarMap.args ρ e.args) W) = _
  rw [h.args e.args, jasminSel_opLeak_inl]
  rfl

/-- The sum of `a` and `b` in `jasminSel`. -/
def addE (w : Nat) (a b : Ctxt.Var Δ (JasminTy.reg w)) : Expr jasminSel Δ (JasminTy.reg w) :=
  ⟨.inl (.regArith .add w), rfl, .cons a (.cons b .nil)⟩

/-- The value of `addE`. -/
theorem addE_denote (w : Nat) (a b : Ctxt.Var Δ (JasminTy.reg w)) (W : Ctxt.Valuation Δ) :
    (addE w a b).denote W
      = (show BitVec w from a.lookup W) + (show BitVec w from b.lookup W) := by
  unfold Expr.denote; rfl

/-- A `regArith` operation emits no event under a model in which it is quiet. -/
theorem opLeak_regArith {L : LeakModel jasminDialect}
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (bop : JasminBinOp) (w : Nat)
    (vals : HVector (fun t => ⟦t⟧)
      (DialectSignature.sig (d := jasminDialect) (.regArith bop w))) :
    opLeak L (.regArith bop w) vals = [] := by
  unfold opLeak
  rw [hq]

/-- `addE` emits no event under a model whose `regArith` operations are quiet. -/
theorem addE_ctLeak {L : LeakModel jasminDialect}
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (w : Nat)
    (a b : Ctxt.Var Δ (JasminTy.reg w)) (W : Ctxt.Valuation Δ) :
    Expr.ctLeak (jasminSelLeak L) (addE w a b) W = [] := by
  unfold Expr.ctLeak
  exact (jasminSel_opLeak_inl L _ _).trans (opLeak_regArith hq _ _ _)

end Embed

/-! ## 3. Recorded subtractions -/

/-- A recorded subtraction: the `w`-bit word at level `y` is the word at level `x` minus the
    word at level `c`. -/
structure SubFact where
  /-- The width of the three words. -/
  w : Nat
  /-- The level of the difference. -/
  y : Nat
  /-- The level of the minuend. -/
  x : Nat
  /-- The level of the subtrahend. -/
  c : Nat

section Sub

variable {Γ : JCtxt}

/-- The recorded subtraction `f` holds under `V`, and its levels are levels of the
    context. -/
def SubFact.Holds (V : Ctxt.Valuation Γ) (f : SubFact) : Prop :=
  f.y < Γ.length ∧ f.x < Γ.length ∧ f.c < Γ.length ∧
    ∀ y x c : BitVec f.w, atLevel V f.w f.y = some y → atLevel V f.w f.x = some x →
      atLevel V f.w f.c = some c → y = x - c

/-- Every recorded subtraction of `D` holds under `V`. -/
def SubOK (D : List SubFact) (V : Ctxt.Valuation Γ) : Prop :=
  ∀ f ∈ D, f.Holds V

/-- A recorded subtraction that holds under `V` holds under every extension of `V`. -/
theorem SubFact.Holds.extend {V : Ctxt.Valuation Γ} {f : SubFact} (h : f.Holds V)
    {t : JasminTy} (z : ⟦t⟧) : f.Holds (V.extend z) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨Nat.lt_succ_of_lt h1, Nat.lt_succ_of_lt h2, Nat.lt_succ_of_lt h3,
    fun y x c hy hx hc => ?_⟩
  rw [atLevel_extend V z _ _ h1] at hy
  rw [atLevel_extend V z _ _ h2] at hx
  rw [atLevel_extend V z _ _ h3] at hc
  exact h4 y x c hy hx hc

/-- Recorded subtractions that hold under `V` hold under every extension of `V`. -/
theorem SubOK.extend {D : List SubFact} {V : Ctxt.Valuation Γ} (h : SubOK D V)
    {t : JasminTy} (z : ⟦t⟧) : SubOK D (V.extend z) :=
  fun f hf => (h f hf).extend z

/-- Recorded subtractions that hold under `V` hold under every extension of `V` by a
    prefix. -/
theorem SubOK.append {D : List SubFact} : ∀ (cs : List JasminTy) {Γ : JCtxt}
    (X : Ctxt.Valuation (d := jasminDialect) cs) {V : Ctxt.Valuation Γ}, SubOK D V →
    SubOK D (hvAppend X V : Ctxt.Valuation (d := jasminDialect) (cs ++ Γ))
  | [], _, .nil, _, h => h
  | _ :: cs, _, .cons x X, _, h => SubOK.extend (Γ := cs ++ _) (SubOK.append cs X h) x

/-- The word at the top level of an extension by a register value. -/
theorem atLevel_top (V : Ctxt.Valuation Γ) {w : Nat} (z : BitVec w) :
    atLevel (Γ := JasminTy.reg w :: Γ) (HVector.cons z V) w Γ.length = some z := by
  show (if Γ.length = Γ.length then regAs (.reg w) w z else atLevel V w Γ.length) = _
  rw [if_pos rfl, regAs_reg]

/-- The subtraction `a - b` bound on top of `V` holds as a recorded subtraction. -/
theorem subFact_bound (V : Ctxt.Valuation Γ) {w : Nat} (a b : Ctxt.Var Γ (.reg w)) :
    SubFact.Holds (Γ := JasminTy.reg w :: Γ) (HVector.cons (regVal V a - regVal V b) V)
      ⟨w, Γ.length, varLevel a, varLevel b⟩ := by
  refine ⟨Nat.lt_succ_self _, Nat.lt_succ_of_lt (varLevel_lt a),
    Nat.lt_succ_of_lt (varLevel_lt b), ?_⟩
  show ∀ y x c : BitVec w,
    atLevel (Γ := JasminTy.reg w :: Γ) (HVector.cons (regVal V a - regVal V b) V) w Γ.length
      = some y →
    atLevel (Γ := JasminTy.reg w :: Γ) (HVector.cons (regVal V a - regVal V b) V) w
      (varLevel a) = some x →
    atLevel (Γ := JasminTy.reg w :: Γ) (HVector.cons (regVal V a - regVal V b) V) w
      (varLevel b) = some c → y = x - c
  intro y x c hy hx hc
  rw [atLevel_top] at hy
  have hx' := (atLevel_extend V (t := JasminTy.reg w) (regVal V a - regVal V b) w _
    (varLevel_lt a)).symm.trans hx
  have hc' := (atLevel_extend V (t := JasminTy.reg w) (regVal V a - regVal V b) w _
    (varLevel_lt b)).symm.trans hc
  rw [atLevel_var a V] at hx'
  rw [atLevel_var b V] at hc'
  cases hy
  cases hx'
  cases hc'
  rfl

/-- The recorded subtractions `D` extended by the binding `e` in a context of length
    `len`: a subtraction `a - b` is recorded at the level `len` of its result. -/
def subPush (D : List SubFact) (len : Nat) {t : JasminTy} (e : Expr jasminDialect Γ t) :
    List SubFact :=
  match e.op, e.args with
  | .regArith .sub w, args =>
    let a : Ctxt.Var Γ (.reg w) := args.head
    let b : Ctxt.Var Γ (.reg w) := args.tail.head
    { w := w, y := len, x := levelIn len a, c := levelIn len b } :: D
  | _, _ => D

/-- Recorded subtractions that hold under `V`, extended by `subPush`, hold under the
    extension of `V` by the value of the binding. -/
theorem SubOK.push {D : List SubFact} {V : Ctxt.Valuation Γ} (h : SubOK D V) {len : Nat}
    (hlen : len = Γ.length) {t : JasminTy} (e : Expr jasminDialect Γ t) :
    SubOK (subPush D len e) (V.extend (e.denote V)) := by
  subst hlen
  rcases e with ⟨op, rfl, args⟩
  cases op
  case regArith bop w =>
    cases bop
    case sub =>
      match args with
      | .cons a (.cons b .nil) =>
        intro f hf
        simp only [subPush, HVector.head, HVector.tail, List.mem_cons] at hf
        rcases hf with rfl | hf
        · exact subFact_bound V a b
        · exact (h f hf).extend _
    all_goals exact fun f hf => (h f (by simpa only [subPush] using hf)).extend _
  all_goals exact fun f hf => (h f (by simpa only [subPush] using hf)).extend _

/-- The recorded subtraction of `D` whose difference is the `w`-bit word at level `ℓ`. -/
def subFind (D : List SubFact) (w ℓ : Nat) : Option SubFact :=
  D.find? fun f => f.w == w && f.y == ℓ

/-- A result of `subFind` is a member of the list at the width and the level asked. -/
theorem subFind_spec {D : List SubFact} {w ℓ : Nat} {f : SubFact}
    (h : subFind D w ℓ = some f) : f ∈ D ∧ f.w = w ∧ f.y = ℓ := by
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨List.mem_of_find?_eq_some h, hp.1, hp.2⟩

/-- The variable `varAt?` returns for a level holds the word at that level. -/
theorem atLevel_varAt {w : Nat} : ∀ {Γ : JCtxt} (V : Ctxt.Valuation Γ) {ℓ : Nat}
    {v : Ctxt.Var Γ (.reg w)}, varAt? w Γ ℓ = some v → atLevel V w ℓ = some (regVal V v)
  | [], _, _, _, h => by cases h
  | t :: Γ, .cons z V, ℓ, v, h => by
      unfold varAt? at h
      show (if ℓ = Γ.length then regAs t w z else atLevel V w ℓ) = _
      split at h
      · rename_i hl
        rw [if_pos hl]
        split at h
        · rename_i ht
          subst ht
          cases h
          exact regAs_reg w z
        · cases h
      · rename_i hl
        rw [if_neg hl]
        obtain ⟨v', hv', rfl⟩ := Option.map_eq_some_iff.mp h
        exact atLevel_varAt V hv'

end Sub

/-! ## 4. A variable that holds a constant -/

/-- A `w`-bit variable whose lane interval under `A` is the point `n`. -/
def constVar (w n : Nat) : {Γ : JCtxt} → AEnv Γ → Option (Ctxt.Var Γ (.reg w))
  | [], _ => none
  | t :: _, .cons a A =>
      if h : t = .reg w then
        if ivSingle? (ivLane w a.1) = some n then some (by subst h; exact .here)
        else (constVar w n A).map .there
      else (constVar w n A).map .there

/-- The lane interval of a result of `constVar` is the point `n`. -/
theorem constVar_spec {w n : Nat} : ∀ {Γ : JCtxt} (A : AEnv Γ) {c : Ctxt.Var Γ (.reg w)},
    constVar w n A = some c → ivSingle? (ivLane w (hget A c).1) = some n
  | [], _, _, h => by simp only [constVar, reduceCtorEq] at h
  | t :: Γ, .cons a A, c, h => by
      rw [constVar] at h
      split at h
      · rename_i ht
        subst ht
        split at h
        · rename_i hn
          cases h
          exact hn
        · obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp h
          exact constVar_spec A hc'
      · obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp h
        exact constVar_spec A hc'

/-! ## 5. The condition of the conditional add -/

section Cond

variable {Γ : JCtxt}

/-- A selected form of a conditional add at width `w`.

    * `direct x d`: the unsigned minimum of `x` and `d`.
    * `viaAdd d c`: the unsigned minimum of `d` and `d + c`. -/
inductive CondSel (Γ : JCtxt) (w : Nat) where
  | direct (x d : Ctxt.Var Γ (.reg w))
  | viaAdd (d c : Ctxt.Var Γ (.reg w))

/-- The value of a selected form under `V`. -/
def CondSel.val {w : Nat} (V : Ctxt.Valuation Γ) : CondSel Γ w → BitVec w
  | .direct x d => umin (regVal V x) (regVal V d)
  | .viaAdd d c => umin (regVal V d) (regVal V d + regVal V c)

/-- The minuend `x` of the `w`-bit word at level `ℓ`, when that word is a recorded
    subtraction `x - c` for a variable `c` whose lane interval is the point `n`. -/
def minuend? (A : AEnv Γ) (D : List SubFact) (w ℓ n : Nat) : Option (Ctxt.Var Γ (.reg w)) :=
  match subFind D w ℓ with
  | some f =>
    match varAt? w Γ f.x, varAt? w Γ f.c with
    | some x, some c => if ivSingle? (ivLane w (hget A c).1) = some n then some x else none
    | _, _ => none
  | none => none

/-- The selected form of `a + b` when the fact of `b` is the mask of `a` by a word whose
    interval is the point `n`, under the interval condition of `ivCondAdd?`: the direct form
    when `a` is a recorded subtraction of a variable that holds `n`, else the form through
    `a + c` for a variable `c` that holds `n`. -/
def condSel (A : AEnv Γ) (D : List SubFact) (len : Nat) {w : Nat}
    (a b : Ctxt.Var Γ (.reg w)) : Option (CondSel Γ w) :=
  match (hget A b).2 with
  | .mask ℓ ic =>
    if ℓ = levelIn len a ∧ 0 < w ∧ ic.2 < 2 ^ (w - 1) ∧ -ic.1 ≤ (hget A a).1.1 ∧
        (hget A a).1.2 < 2 ^ (w - 1) then
      match ivSingle? ic with
      | some n =>
        match minuend? A D w ℓ n with
        | some x => some (.direct x a)
        | none => (constVar w n A).map (.viaAdd a)
      | none => none
    else none
  | _ => none

/-- The selected form of `a + b` with the mask in either operand. -/
def condEither (A : AEnv Γ) (D : List SubFact) (len : Nat) {w : Nat}
    (a b : Ctxt.Var Γ (.reg w)) : Option (CondSel Γ w) :=
  match condSel A D len a b with
  | some r => some r
  | none => condSel A D len b a

variable {A : AEnv Γ} {D : List SubFact} {V : Ctxt.Valuation Γ}

/-- A result `x` of `minuend?` for the level `ℓ` and the point `n`: the word at level `ℓ` is
    the word of `x` minus every word whose `toNat` is `n`. -/
theorem minuend_sound (hA : EnvOK A V) (hD : SubOK D V) {w ℓ n : Nat}
    {x : Ctxt.Var Γ (.reg w)} (h : minuend? A D w ℓ n = some x) (d C : BitVec w)
    (hd : atLevel V w ℓ = some d) (hC : C.toNat = n) : d = regVal V x - C := by
  unfold minuend? at h
  split at h
  · rename_i f hf
    obtain ⟨hmem, hw, hy⟩ := subFind_spec hf
    split at h
    · rename_i x' c hx hc
      split at h
      · rename_i hn
        cases h
        obtain ⟨_, _, _, hsem⟩ := hD f hmem
        subst hw
        subst hy
        have hcv : regVal V c = C :=
          BitVec.eq_of_toNat_eq ((Iv.toNat_eq_of_single (hA.reg c).1 hn).trans hC.symm)
        rw [← hcv]
        exact hsem d _ _ hd (atLevel_varAt V hx) (atLevel_varAt V hc)
      · cases h
    · cases h
  · cases h

/-- **A selected form of the conditional add has the value of the sum.** -/
theorem condSel_sound (hA : EnvOK A V) (hD : SubOK D V) {len : Nat} (hlen : len = Γ.length)
    {w : Nat} {a b : Ctxt.Var Γ (.reg w)} {r : CondSel Γ w}
    (h : condSel A D len a b = some r) : r.val V = regVal V a + regVal V b := by
  subst hlen
  unfold condSel at h
  split at h
  · rename_i ℓ ic hs
    split at h
    · rename_i hc
      obtain ⟨hl, hw, hic, hlo, hhi⟩ := hc
      have hb := (hA.reg b).2
      rw [hs] at hb
      obtain ⟨C, hC1, hC2, hC⟩ := hb.holds a hl
      have hd := (hA.reg a).1
      have hCn : C.toNat < 2 ^ (w - 1) := by
        have : (C.toNat : Int) < 2 ^ (w - 1) := lt_of_le_of_lt hC2 hic
        exact_mod_cast this
      have hlo' : -(C.toNat : Int) ≤ (hget A a).1.1 := by omega
      have hsum : regVal V a + regVal V b = condAdd (regVal V a) C := by
        rw [hC]
        rfl
      split at h
      · rename_i n hn
        have hCeq : C.toNat = n := by
          unfold ivSingle? at hn
          split at hn
          · cases hn
            omega
          · cases hn
        split at h
        · rename_i x hx
          cases h
          have hdx := minuend_sound hA hD hx (regVal V a) C
            (by rw [hl]; exact atLevel_var a V) hCeq
          have hmem : (hget A a).1.Mem w (regVal V x - C) := by
            rw [← hdx]
            exact hd
          show umin (regVal V x) (regVal V a) = regVal V a + regVal V b
          rw [hsum, hdx]
          exact (condAdd_sub_eq_umin hw hmem hCn hlo' hhi).symm
        · obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
          have hcv : regVal V c = C :=
            BitVec.eq_of_toNat_eq
              ((Iv.toNat_eq_of_single (hA.reg c).1 (constVar_spec A hc)).trans hCeq.symm)
          show umin (regVal V a) (regVal V a + regVal V c) = regVal V a + regVal V b
          rw [hsum, hcv]
          exact (condAdd_eq_umin hw hd hCn hlo' hhi).symm
      · cases h
    · cases h
  · cases h

/-- A selected form of `condEither` has the value of the sum. -/
theorem condEither_sound (hA : EnvOK A V) (hD : SubOK D V) {len : Nat}
    (hlen : len = Γ.length) {w : Nat} {a b : Ctxt.Var Γ (.reg w)} {r : CondSel Γ w}
    (h : condEither A D len a b = some r) : r.val V = regVal V a + regVal V b := by
  unfold condEither at h
  split at h
  · rename_i r' hr
    cases h
    exact condSel_sound hA hD hlen hr
  · exact (condSel_sound hA hD hlen h).trans (BitVec.add_comm _ _)

/-! ## 6. The condition of the half-width multiply -/

/-- The lane interval of `i` at width `w` ends below `2 ^ (w / 2)`. -/
def halfFits (w : Nat) (i : Iv) : Bool := decide ((ivLane w i).2 < 2 ^ (w / 2))

/-- A member of an interval that `halfFits` accepts is below `2 ^ (w / 2)`. -/
theorem toNat_lt_of_halfFits {w : Nat} {i : Iv} {x : BitVec w} (h : i.Mem w x)
    (hf : halfFits w i = true) : x.toNat < 2 ^ (w / 2) := by
  have h2 := (Iv.mem_lane h).2
  simp only [halfFits, decide_eq_true_eq] at hf
  have : (x.toNat : Int) < 2 ^ (w / 2) := lt_of_le_of_lt h2 hf
  exact_mod_cast this

end Cond

/-! ## 7. The bindings one input binding becomes -/

/-- The bindings of the output for one binding of type `t` of the input, over the output
    context `Δ`: one expression, or an expression of type `s` followed by an expression
    that sees its result. -/
inductive Emit (Δ : Ctxt jasminSel) (t : JasminTy) : Type where
  | one (e : Expr jasminSel Δ t)
  | two (s : JasminTy) (e₁ : Expr jasminSel Δ s) (e₂ : Expr jasminSel (s :: Δ) t)

namespace Emit

variable {Γ : JCtxt} {Δ : Ctxt jasminSel} {t : JasminTy}

/-- The output context below the result of the bindings. -/
def ctx : Emit Δ t → Ctxt jasminSel
  | .one _ => Δ
  | .two s _ _ => s :: Δ

/-- The valuation of `ctx` after the bindings ran from `W`. -/
def env : (r : Emit Δ t) → Ctxt.Valuation Δ → Ctxt.Valuation r.ctx
  | .one _, W => W
  | .two _ e₁ _, W => W.extend (e₁.denote W)

/-- The result of the bindings from `W`. -/
def val : Emit Δ t → Ctxt.Valuation Δ → ⟦t⟧
  | .one e, W => e.denote W
  | .two _ e₁ e₂, W => e₂.denote (W.extend (e₁.denote W))

/-- The events of the bindings from `W`. -/
def leak (M : LeakModel jasminSel) : Emit Δ t → Ctxt.Valuation Δ → List CTLeak
  | .one e, W => Expr.ctLeak M e W
  | .two _ e₁ e₂, W => Expr.ctLeak M e₁ W ++ Expr.ctLeak M e₂ (W.extend (e₁.denote W))

/-- A map of variables into `Δ` as a map into `ctx`. -/
def wk : (r : Emit Δ t) → VarMap Γ Δ → VarMap Γ r.ctx
  | .one _, ρ => ρ
  | .two s _ _, ρ => VarMap.skip ρ s

/-- The bindings in front of a continuation that sees their result. -/
def plug {ts : List JasminTy} : (r : Emit Δ t) → NFProg jasminSel (t :: r.ctx) ts →
    NFProg jasminSel Δ ts
  | .one e, k => .var e k
  | .two _ e₁ e₂, k => .var e₁ (.var e₂ k)

/-- A map that relates `W` to `V` relates, as a map into `ctx`, the valuation after the
    bindings to `V`. -/
theorem wk_ok {ρ : VarMap Γ Δ} {W : Ctxt.Valuation Δ} {V : Ctxt.Valuation Γ}
    (h : VarMap.OK ρ W V) (r : Emit Δ t) : VarMap.OK (r.wk ρ) (r.env W) V := by
  cases r with
  | one e => exact h
  | two s e₁ e₂ => exact h.skip _

/-- The bindings in front of `k` denote `k` at the valuation after the bindings, extended
    by their result. -/
theorem plug_denote (fuel : Nat) {ts : List JasminTy} (r : Emit Δ t)
    (k : NFProg jasminSel (t :: r.ctx) ts) (W : Ctxt.Valuation Δ) :
    (r.plug k).denote fuel W = k.denote fuel ((r.env W).extend (r.val W)) := by
  cases r with
  | one e =>
    simp only [Emit.plug, Emit.env, Emit.val, NFProg.denote, Expr.denoteM_option_eq_some,
      Option.bind_eq_bind, Option.bind_some]
    rfl
  | two s e₁ e₂ =>
    simp only [Emit.plug, Emit.env, Emit.val, NFProg.denote, Expr.denoteM_option_eq_some,
      Option.bind_eq_bind, Option.bind_some]
    rfl

/-- The leakage run of the bindings in front of `k`: the run of `k` at the valuation after
    the bindings, behind their events. -/
theorem plug_leakRun (M : LeakModel jasminSel) (fuel : Nat) {ts : List JasminTy}
    (r : Emit Δ t) (k : NFProg jasminSel (t :: r.ctx) ts) (W : Ctxt.Valuation Δ) :
    NFProg.leakRun M fuel (r.plug k) W =
      (NFProg.leakRun M fuel k ((r.env W).extend (r.val W))).map fun q =>
        (q.1, r.leak M W ++ q.2) := by
  cases r with
  | one e => rfl
  | two s e₁ e₂ =>
    show ((NFProg.leakRun M fuel k _).map _).map _ = _
    rw [Option.map_map]
    congr 1
    funext q
    simp only [Function.comp, Emit.leak, List.append_assoc]

end Emit

section Bind

variable {Γ : JCtxt} {Δ : Ctxt jasminSel}

/-- The bindings of a selected form of the conditional add along a map of variables. -/
def CondSel.toEmit {w : Nat} (ρ : VarMap Γ Δ) : CondSel Γ w → Emit Δ (.reg w)
  | .direct x d => .one (uminE w (ρ _ x) (ρ _ d))
  | .viaAdd d c =>
      .two (.reg w) (addE w (ρ _ d) (ρ _ c)) (uminE w (.there (ρ _ d)) .here)

/-- The bindings of a selected form give its value. -/
theorem CondSel.toEmit_val {w : Nat} {ρ : VarMap Γ Δ} {W : Ctxt.Valuation Δ}
    {V : Ctxt.Valuation Γ} (hρ : VarMap.OK ρ W V) (r : CondSel Γ w) :
    (r.toEmit ρ).val W = r.val V := by
  cases r with
  | direct x d =>
    show (uminE w (ρ _ x) (ρ _ d)).denote W = _
    rw [uminE_denote, hρ _ x, hρ _ d]
    rfl
  | viaAdd d c =>
    show umin (show BitVec w from (ρ _ d).lookup W)
      ((show BitVec w from (ρ _ d).lookup W) + (show BitVec w from (ρ _ c).lookup W)) = _
    rw [hρ _ d, hρ _ c]
    rfl

/-- The bindings of a selected form emit no event under a model whose `regArith`
    operations are quiet. -/
theorem CondSel.toEmit_leak {L : LeakModel jasminDialect}
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {w : Nat} (ρ : VarMap Γ Δ)
    (r : CondSel Γ w) (W : Ctxt.Valuation Δ) :
    (r.toEmit ρ).leak (jasminSelLeak L) W = [] := by
  cases r with
  | direct x d => rfl
  | viaAdd d c =>
    show Expr.ctLeak (jasminSelLeak L) (addE w (ρ _ d) (ρ _ c)) W ++ [] = []
    rw [addE_ctLeak hq, List.append_nil]

/-- The selection for the operation `op` on `args`: the conditional add for an addition,
    the half-width multiply for a multiplication whose operands `halfFits` accepts. -/
def selOp (A : AEnv Γ) (D : List SubFact) (len : Nat) (ρ : VarMap Γ Δ) (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op)) :
    Option (Emit Δ (DialectSignature.ret (d := jasminDialect) op)) :=
  match op, args with
  | .regArith .add w, args =>
    let a : Ctxt.Var Γ (.reg w) := args.head
    let b : Ctxt.Var Γ (.reg w) := args.tail.head
    (condEither A D len a b).map (CondSel.toEmit ρ)
  | .regArith .mul w, args =>
    let a : Ctxt.Var Γ (.reg w) := args.head
    let b : Ctxt.Var Γ (.reg w) := args.tail.head
    if halfFits w (hget A a).1 && halfFits w (hget A b).1 then
      some (.one (muluE w (ρ _ a) (ρ _ b)))
    else none
  | _, _ => none

variable {A : AEnv Γ} {D : List SubFact} {len : Nat} {ρ : VarMap Γ Δ}
  {W : Ctxt.Valuation Δ} {V : Ctxt.Valuation Γ}

/-- A selection is made for a `regArith` operation only. -/
theorem selOp_op {op : JasminOp}
    {args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op)}
    {r : Emit Δ (DialectSignature.ret (d := jasminDialect) op)}
    (h : selOp A D len ρ op args = some r) : ∃ bop w, op = .regArith bop w := by
  cases op
  case regArith bop w => exact ⟨bop, w, rfl⟩
  all_goals simp [selOp] at h

/-- A selection gives the value of the operation. -/
theorem selOp_val (hA : EnvOK A V) (hD : SubOK D V) (hlen : len = Γ.length)
    (hρ : VarMap.OK ρ W V) {op : JasminOp}
    {args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op)}
    {r : Emit Δ (DialectSignature.ret (d := jasminDialect) op)}
    (h : selOp A D len ρ op args = some r) :
    r.val W = DialectDenote.denote (d := jasminDialect) op (Expr.lookupArgs args V) := by
  cases op
  case regArith bop w =>
    cases bop
    case add =>
      match args with
      | .cons a (.cons b .nil) =>
        simp only [selOp, HVector.head, HVector.tail] at h
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [CondSel.toEmit_val hρ]
        exact condEither_sound hA hD hlen hc
    case mul =>
      match args with
      | .cons a (.cons b .nil) =>
        simp only [selOp, HVector.head, HVector.tail] at h
        split at h
        · rename_i hf
          cases h
          simp only [Bool.and_eq_true] at hf
          show (muluE w (ρ _ a) (ρ _ b)).denote W = regVal V a * regVal V b
          rw [muluE_denote, hρ _ a, hρ _ b]
          exact halfProd_eq_mul _ _ (toNat_lt_of_halfFits (hA.reg a).1 hf.1)
            (toNat_lt_of_halfFits (hA.reg b).1 hf.2)
        · cases h
    all_goals simp [selOp] at h
  all_goals simp [selOp] at h

/-- A selection emits no event under a model whose `regArith` operations are quiet. -/
theorem selOp_leak {L : LeakModel jasminDialect}
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) {op : JasminOp}
    {args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op)}
    {r : Emit Δ (DialectSignature.ret (d := jasminDialect) op)}
    (h : selOp A D len ρ op args = some r) (W : Ctxt.Valuation Δ) :
    r.leak (jasminSelLeak L) W = [] := by
  cases op
  case regArith bop w =>
    cases bop
    case add =>
      match args with
      | .cons a (.cons b .nil) =>
        simp only [selOp, HVector.head, HVector.tail] at h
        obtain ⟨c, _, rfl⟩ := Option.map_eq_some_iff.mp h
        exact CondSel.toEmit_leak hq ρ c W
    case mul =>
      match args with
      | .cons a (.cons b .nil) =>
        simp only [selOp, HVector.head, HVector.tail] at h
        split at h
        · cases h
          rfl
        · cases h
    all_goals simp [selOp] at h
  all_goals simp [selOp] at h

/-- The bindings of the output for the binding `e` of the input: the selection of `selOp`
    when one is made, else `e` embedded. -/
def selBind (A : AEnv Γ) (D : List SubFact) (len : Nat) (ρ : VarMap Γ Δ) {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Emit Δ t :=
  match selOp A D len ρ e.op e.args with
  | some r => e.retTy_eq ▸ r
  | none => .one (selEmbedExpr ρ e)

/-- **The bindings of `selBind` give the value of the input binding.** -/
theorem selBind_val (hA : EnvOK A V) (hD : SubOK D V) (hlen : len = Γ.length)
    (hρ : VarMap.OK ρ W V) {t : JasminTy} (e : Expr jasminDialect Γ t) :
    (selBind A D len ρ e).val W = e.denote V := by
  rcases e with ⟨op, rfl, args⟩
  unfold selBind
  split
  · rename_i r hr
    exact selOp_val hA hD hlen hρ hr
  · exact selEmbedExpr_denote hρ (Expr.mk op rfl args)

/-- **The bindings of `selBind` emit the events of the input binding** under a model whose
    `regArith` operations are quiet. -/
theorem selBind_leak {L : LeakModel jasminDialect}
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (hρ : VarMap.OK ρ W V) {t : JasminTy}
    (e : Expr jasminDialect Γ t) :
    (selBind A D len ρ e).leak (jasminSelLeak L) W = Expr.ctLeak L e V := by
  rcases e with ⟨op, rfl, args⟩
  unfold selBind
  split
  · rename_i r hr
    obtain ⟨bop, w, rfl⟩ := selOp_op hr
    rw [expr_ctLeak_regArith L hq _ rfl V]
    exact selOp_leak hq hr W
  · exact selEmbedExpr_ctLeak L hρ _

end Bind

/-! ## 8. The traversal -/

/-- The traversal of a structured program from the abstract environment `A` and the
    recorded subtractions `D` of a context of length `len`, under the annotation `a` and
    along the map `ρ` of variables: each let-binding becomes the bindings of `selBind`;
    each region is kept, with the carried variables of a loop at the proposed intervals of
    `a` when the checker of `RangeNFLoop` accepts them and at the full lane range
    otherwise. -/
def selGo : {Γ : JCtxt} → {ts : List JasminTy} → {Δ : Ctxt jasminSel} → AEnv Γ →
    List SubFact → Nat → CarriedAnn → VarMap Γ Δ → NFProg jasminDialect Γ ts →
    NFProg jasminSel Δ ts
  | _, _, _, _, _, _, _, ρ, .ret vs => .ret (VarMap.args ρ vs)
  | _, _, _, A, D, len, a, ρ, .var e k =>
      (selBind A D len ρ e).plug
        (selGo (HVector.cons (f := fun _ => AVal) (stageAbs A e len) A) (subPush D len e)
          (len + 1) a (VarMap.lift ((selBind A D len ρ e).wk ρ) _) k)
  | _, _, _, A, D, len, a, ρ, .forLoop (cs := cs) count inits body k =>
      .forLoop (ρ _ count) (VarMap.args ρ inits)
        (selGo
          (carriedEnv (forInductive A len a inits body) cs a.ivs
            (topCons (HasWord64.word (d := jasminDialect)) A))
          D (cs.length + (len + 1)) a.inner
          (VarMap.liftApp (VarMap.lift ρ (HasWord64.word (d := jasminDialect))) cs) body)
        (selGo (carriedEnv (forInductive A len a inits body) cs a.ivs A) D
          (cs.length + len) a.rest (VarMap.liftApp ρ cs) k)
  | _, _, _, A, D, len, a, ρ, .ifThenElse (rs := rs) cond thn els k =>
      .ifThenElse (ρ _ cond) (selGo A D len a.inner ρ thn) (selGo A D len a.other ρ els)
        (selGo (topApp rs A) D (rs.length + len) a.rest (VarMap.liftApp ρ rs) k)
  | _, _, _, A, D, len, a, ρ, .whileLoop (cs := cs) inits body k =>
      .whileLoop (VarMap.args ρ inits)
        (selGo (carriedEnv (whileInductive A len a inits body) cs a.ivs A) D
          (cs.length + len) a.inner (VarMap.liftApp ρ cs) body)
        (selGo (carriedEnv (whileInductive A len a inits body) cs a.ivs A) D
          (cs.length + len) a.rest (VarMap.liftApp ρ cs) k)
  | _, _, _, A, D, len, a, ρ, .call (rs := rs) f args k =>
      .call f (VarMap.args ρ args)
        (selGo (topApp rs A) D (rs.length + len) a (VarMap.liftApp ρ rs) k)

/-! ## 9. Iterations of the two dialects under an invariant -/

/-- The exit-flag iteration of `jasminSel` is the iteration of `jasminDialect`. -/
theorem whileIter_sel {cs : List JasminTy}
    (step : Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) (HasBitType.bit (d := jasminDialect) :: cs))) :
    ∀ (n : Nat) (acc : Ctxt.Valuation (d := jasminDialect) cs),
      NFProg.whileIter (d := jasminSel) step n acc
        = NFProg.whileIter (d := jasminDialect) step n acc
  | 0, _ => rfl
  | n + 1, acc => by
      show (step acc >>= fun r => if HasBoolBit.toBool (d := jasminDialect) r.head
          then NFProg.whileIter (d := jasminSel) step n r.tail else some r.tail)
        = (step acc >>= fun r => if HasBoolBit.toBool (d := jasminDialect) r.head
          then NFProg.whileIter (d := jasminDialect) step n r.tail else some r.tail)
      simp only [whileIter_sel step n]

/-- Two binds are equal when their first computations are equal and their continuations
    agree on the result of the first. -/
theorem obind_congr {α β : Type} {o o' : Option α} {K K' : α → Option β} (e : o' = o)
    (hK : ∀ x, o = some x → K' x = K x) : o'.bind K' = o.bind K := by
  subst e
  rcases o' with _ | x
  · rfl
  · exact hK x rfl

/-- A counted run with events whose step keeps `P` ends in a state that satisfies `P`. -/
theorem forIterLeak_inv {cs : List JasminTy}
    (P : Ctxt.Valuation (d := jasminDialect) cs → Prop)
    (f : Nat → Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) cs × List CTLeak))
    (hf : ∀ i X r, P X → f i X = some r → P r.1) :
    ∀ (l : List Nat) (X : Ctxt.Valuation (d := jasminDialect) cs)
      (r : Ctxt.Valuation (d := jasminDialect) cs × List CTLeak), P X →
      forIterLeak (d := jasminDialect) f l X = some r → P r.1
  | [], X, r, h, e => by
      simp only [forIterLeak, Option.some.injEq] at e
      subst e
      exact h
  | i :: l, X, r, h, e => by
      simp only [forIterLeak, Option.bind_eq_some_iff, Option.map_eq_some_iff] at e
      obtain ⟨u, hu, q, hq, rfl⟩ := e
      exact forIterLeak_inv P f hf l u.1 q (hf i X u h hu) hq

/-- A counted run with events of `jasminSel` and one of `jasminDialect` whose steps agree on
    the states that satisfy `P`, from a state that satisfies `P`, are equal when the step
    keeps `P`. -/
theorem forIterLeak_congr_inv {cs : List JasminTy}
    (P : Ctxt.Valuation (d := jasminDialect) cs → Prop)
    (f g : Nat → Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect) cs × List CTLeak))
    (hg : ∀ i X, P X → g i X = f i X) (hf : ∀ i X r, P X → f i X = some r → P r.1) :
    ∀ (l : List Nat) (X : Ctxt.Valuation (d := jasminDialect) cs), P X →
      forIterLeak (d := jasminSel) g l X = forIterLeak (d := jasminDialect) f l X
  | [], _, _ => rfl
  | i :: l, X, h => by
      show ((g i X).bind fun r =>
          (forIterLeak (d := jasminSel) g l r.1).map fun q => (q.1, r.2 ++ q.2))
        = ((f i X).bind fun r =>
          (forIterLeak (d := jasminDialect) f l r.1).map fun q => (q.1, r.2 ++ q.2))
      exact obind_congr (hg i X h) fun u hu => by
        rw [forIterLeak_congr_inv P f g hg hf l u.1 (hf i X u h hu)]

/-- An exit-flag run with events whose step keeps `P` ends in a state that satisfies
    `P`. -/
theorem whileIterLeak_inv {cs : List JasminTy}
    (P : Ctxt.Valuation (d := jasminDialect) cs → Prop)
    (f : Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect)
        (HasBitType.bit (d := jasminDialect) :: cs) × List CTLeak))
    (hf : ∀ X r, P X → f X = some r → P r.1.tail) :
    ∀ (n : Nat) (X : Ctxt.Valuation (d := jasminDialect) cs)
      (r : Ctxt.Valuation (d := jasminDialect) cs × List CTLeak), P X →
      whileIterLeak (d := jasminDialect) f n X = some r → P r.1
  | 0, _, _, _, e => by simp [whileIterLeak] at e
  | n + 1, X, r, h, e => by
      simp only [whileIterLeak, Option.bind_eq_some_iff] at e
      obtain ⟨u, hu, e⟩ := e
      split at e
      · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp e
        exact whileIterLeak_inv P f hf n _ q (hf X u h hu) hq
      · cases e
        exact hf X u h hu

/-- An exit-flag run with events of `jasminSel` and one of `jasminDialect` whose steps agree
    on the states that satisfy `P`, from a state that satisfies `P`, are equal when the step
    keeps `P`. -/
theorem whileIterLeak_congr_inv {cs : List JasminTy}
    (P : Ctxt.Valuation (d := jasminDialect) cs → Prop)
    (f g : Ctxt.Valuation (d := jasminDialect) cs →
      Option (Ctxt.Valuation (d := jasminDialect)
        (HasBitType.bit (d := jasminDialect) :: cs) × List CTLeak))
    (hg : ∀ X, P X → g X = f X) (hf : ∀ X r, P X → f X = some r → P r.1.tail) :
    ∀ (n : Nat) (X : Ctxt.Valuation (d := jasminDialect) cs), P X →
      whileIterLeak (d := jasminSel) g n X = whileIterLeak (d := jasminDialect) f n X
  | 0, _, _ => rfl
  | n + 1, X, h => by
      show ((g X).bind fun r =>
          if HasBoolBit.toBool (d := jasminDialect) r.1.head then
            (whileIterLeak (d := jasminSel) g n r.1.tail).map
              fun q => (q.1, r.2 ++ .branch true :: q.2)
          else some (r.1.tail, r.2 ++ [.branch false]))
        = ((f X).bind fun r =>
          if HasBoolBit.toBool (d := jasminDialect) r.1.head then
            (whileIterLeak (d := jasminDialect) f n r.1.tail).map
              fun q => (q.1, r.2 ++ .branch true :: q.2)
          else some (r.1.tail, r.2 ++ [.branch false]))
      exact obind_congr (hg X h) fun u hu => by
        rw [whileIterLeak_congr_inv P f g hg hf n u.1.tail (hf X u h hu)]

/-! ## 10. The denotation -/

/-- **Denotation of the traversal.** Under an environment and recorded subtractions that
    hold of `V`, along a map that relates `W` to `V`, the output denotes at `W` what the
    input denotes at `V`, at every fuel and for every annotation. -/
theorem selGo_denote (fuel : Nat) : ∀ {Γ : JCtxt} {ts : List JasminTy}
    {Δ : Ctxt jasminSel} (A : AEnv Γ) (D : List SubFact) (len : Nat) (a : CarriedAnn)
    (ρ : VarMap Γ Δ) (p : NFProg jasminDialect Γ ts) (V : Ctxt.Valuation Γ)
    (W : Ctxt.Valuation Δ), len = Γ.length → EnvOK A V → SubOK D V → VarMap.OK ρ W V →
    (selGo A D len a ρ p).denote fuel W = p.denote fuel V
  | _, _, _, _, _, _, _, ρ, .ret vs, V, W, _, _, _, hρ => congrArg some (hρ.args vs)
  | _, _, _, A, D, len, a, ρ, .var e k, V, W, hlen, hA, hD, hρ => by
      simp only [selGo, Emit.plug_denote, NFProg.denote, Expr.denoteM_option_eq_some,
        Option.bind_eq_bind, Option.bind_some]
      rw [selBind_val hA hD hlen hρ e]
      exact selGo_denote fuel _ _ (len + 1) a _ k _ _ (by simp [hlen])
        (hA.cons (stageAbs_sound hA hlen e)) (hD.push hlen e)
        ((Emit.wk_ok hρ _).lift _)
  | _, _, _, A, D, len, a, ρ, .forLoop (cs := cs) count inits body k, V, W, hlen, hA, hD,
      hρ => by
      have hb : ∀ (acc : Ctxt.Valuation (d := jasminDialect) cs) (i : Nat),
          CarriedOK (forInductive A len a inits body) cs a.ivs acc →
          (selGo
              (carriedEnv (forInductive A len a inits body) cs a.ivs
                (topCons (HasWord64.word (d := jasminDialect)) A))
              D (cs.length + (len + 1)) a.inner
              (VarMap.liftApp (VarMap.lift ρ (HasWord64.word (d := jasminDialect))) cs)
              body).denote fuel
              (hvAppend (d := jasminSel) acc
                (.cons (HasWord64.ofNat (d := jasminDialect) i) W)) =
            body.denote fuel
              (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) :=
        fun acc i hP => selGo_denote fuel _ _ _ a.inner _ body _ _ (length_body cs _ hlen)
          (envOK_carriedEnv cs a.ivs acc hP (envOK_topCons hA _))
          (SubOK.append cs acc (hD.extend _)) ((hρ.lift _).liftApp cs acc)
      have hk : ∀ acc : Ctxt.Valuation (d := jasminDialect) cs,
          CarriedOK (forInductive A len a inits body) cs a.ivs acc →
          (selGo (carriedEnv (forInductive A len a inits body) cs a.ivs A) D
              (cs.length + len) a.rest (VarMap.liftApp ρ cs) k).denote fuel
              (hvAppend (d := jasminSel) acc W) =
            k.denote fuel (hvAppend acc V) :=
        fun acc hP => selGo_denote fuel _ _ _ a.rest _ k _ _ (length_app cs hlen)
          (envOK_carriedEnv cs a.ivs acc hP hA) (SubOK.append cs acc hD)
          (hρ.liftApp cs acc)
      have hs := forInductive_step fuel (a := a) (inits := inits) (body := body) hlen hA
      have hi := forInductive_init (len := len) (a := a) (inits := inits) (body := body) hA
      have hc : (ρ _ count).lookup W = count.lookup V := hρ _ count
      simp only [selGo, NFProg.denote]
      erw [hc, hρ.args inits]
      exact bind_congr_inv (foldlM_congr_inv _ _ _ hb hs _ _ hi)
        (fun acc hacc => hk acc (foldlM_inv _ _ hs _ _ _ hi hacc))
  | _, _, _, A, D, len, a, ρ, .ifThenElse (rs := rs) cond thn els k, V, W, hlen, hA, hD,
      hρ => by
      have hk : ∀ r : Ctxt.Valuation (d := jasminDialect) rs,
          (selGo (topApp rs A) D (rs.length + len) a.rest (VarMap.liftApp ρ rs) k).denote
              fuel (hvAppend (d := jasminSel) r W) =
            k.denote fuel (hvAppend r V) :=
        fun r => selGo_denote fuel _ _ _ a.rest _ k _ _ (length_app rs hlen)
          (envOK_topApp rs r hA) (SubOK.append rs r hD) (hρ.liftApp rs r)
      have hc : (ρ _ cond).lookup W = cond.lookup V := hρ _ cond
      simp only [selGo, NFProg.denote, hk,
        selGo_denote fuel A D len a.inner ρ thn V W hlen hA hD hρ,
        selGo_denote fuel A D len a.other ρ els V W hlen hA hD hρ]
      erw [hc]
      rfl
  | _, _, _, A, D, len, a, ρ, .whileLoop (cs := cs) inits body k, V, W, hlen, hA, hD,
      hρ => by
      have hb : ∀ acc : Ctxt.Valuation (d := jasminDialect) cs,
          CarriedOK (whileInductive A len a inits body) cs a.ivs acc →
          (selGo (carriedEnv (whileInductive A len a inits body) cs a.ivs A) D
              (cs.length + len) a.inner (VarMap.liftApp ρ cs) body).denote fuel
              (hvAppend (d := jasminSel) acc W) =
            body.denote fuel (hvAppend acc V) :=
        fun acc hP => selGo_denote fuel _ _ _ a.inner _ body _ _ (length_app cs hlen)
          (envOK_carriedEnv cs a.ivs acc hP hA) (SubOK.append cs acc hD)
          (hρ.liftApp cs acc)
      have hk : ∀ acc : Ctxt.Valuation (d := jasminDialect) cs,
          CarriedOK (whileInductive A len a inits body) cs a.ivs acc →
          (selGo (carriedEnv (whileInductive A len a inits body) cs a.ivs A) D
              (cs.length + len) a.rest (VarMap.liftApp ρ cs) k).denote fuel
              (hvAppend (d := jasminSel) acc W) =
            k.denote fuel (hvAppend acc V) :=
        fun acc hP => selGo_denote fuel _ _ _ a.rest _ k _ _ (length_app cs hlen)
          (envOK_carriedEnv cs a.ivs acc hP hA) (SubOK.append cs acc hD)
          (hρ.liftApp cs acc)
      have hs := whileInductive_step fuel (a := a) (inits := inits) (body := body) hlen hA
      have hi := whileInductive_init (len := len) (a := a) (inits := inits) (body := body) hA
      simp only [selGo, NFProg.denote]
      rw [hρ.args inits, whileIter_sel]
      exact bind_congr_inv (whileIter_congr_inv _ _ _ hb hs _ _ hi)
        (fun acc hacc => hk acc (whileIter_inv _ _ hs _ _ _ hi hacc))
  | _, _, _, A, D, len, a, ρ, .call (rs := rs) f args k, V, W, hlen, hA, hD, hρ => by
      have hk : ∀ r : Ctxt.Valuation (d := jasminDialect) rs,
          (selGo (topApp rs A) D (rs.length + len) a (VarMap.liftApp ρ rs) k).denote fuel
              (hvAppend (d := jasminSel) r W) =
            k.denote fuel (hvAppend r V) :=
        fun r => selGo_denote fuel _ _ _ a _ k _ _ (length_app rs hlen)
          (envOK_topApp rs r hA) (SubOK.append rs r hD) (hρ.liftApp rs r)
      simp only [selGo, NFProg.denote, hk]
      rw [hρ.args args]
      rfl

/-! ## 11. The leakage run -/

section Leak

variable {L : LeakModel jasminDialect}

/-- **Leakage run of the traversal.** Under a leakage model whose `regArith` operations are
    quiet, an environment and recorded subtractions that hold of `V`, and a map that relates
    `W` to `V`, the leakage run of the output at `W` is the leakage run of the input at
    `V`: the same results and the same events. -/
theorem selGo_leakRun (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (fuel : Nat) :
    ∀ {Γ : JCtxt} {ts : List JasminTy} {Δ : Ctxt jasminSel} (A : AEnv Γ)
      (D : List SubFact) (len : Nat) (a : CarriedAnn) (ρ : VarMap Γ Δ)
      (p : NFProg jasminDialect Γ ts) (V : Ctxt.Valuation Γ) (W : Ctxt.Valuation Δ),
      len = Γ.length → EnvOK A V → SubOK D V → VarMap.OK ρ W V →
      NFProg.leakRun (jasminSelLeak L) fuel (selGo A D len a ρ p) W =
        NFProg.leakRun L fuel p V
  | _, _, _, _, _, _, _, ρ, .ret vs, V, W, _, _, _, hρ =>
      congrArg (fun x => some (x, ([] : List CTLeak))) (hρ.args vs)
  | _, _, _, A, D, len, a, ρ, .var e k, V, W, hlen, hA, hD, hρ => by
      simp only [selGo, Emit.plug_leakRun, NFProg.leakRun]
      rw [selBind_val hA hD hlen hρ e, selBind_leak hq hρ e,
        selGo_leakRun hq fuel _ _ (len + 1) a _ k _ _ (by simp [hlen])
          (hA.cons (stageAbs_sound hA hlen e)) (hD.push hlen e)
          ((Emit.wk_ok hρ _).lift _)]
  | _, _, _, A, D, len, a, ρ, .forLoop (cs := cs) count inits body k, V, W, hlen, hA, hD,
      hρ => by
      have hb : ∀ (i : Nat) (acc : Ctxt.Valuation (d := jasminDialect) cs),
          CarriedOK (forInductive A len a inits body) cs a.ivs acc →
          NFProg.leakRun (jasminSelLeak L) fuel
              (selGo
                (carriedEnv (forInductive A len a inits body) cs a.ivs
                  (topCons (HasWord64.word (d := jasminDialect)) A))
                D (cs.length + (len + 1)) a.inner
                (VarMap.liftApp (VarMap.lift ρ (HasWord64.word (d := jasminDialect))) cs)
                body)
              (hvAppend (d := jasminSel) acc
                (.cons (HasWord64.ofNat (d := jasminDialect) i) W)) =
            NFProg.leakRun L fuel body
              (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) :=
        fun i acc hP => selGo_leakRun hq fuel _ _ _ a.inner _ body _ _
          (length_body cs _ hlen) (envOK_carriedEnv cs a.ivs acc hP (envOK_topCons hA _))
          (SubOK.append cs acc (hD.extend _)) ((hρ.lift _).liftApp cs acc)
      have hk : ∀ acc : Ctxt.Valuation (d := jasminDialect) cs,
          CarriedOK (forInductive A len a inits body) cs a.ivs acc →
          NFProg.leakRun (jasminSelLeak L) fuel
              (selGo (carriedEnv (forInductive A len a inits body) cs a.ivs A) D
                (cs.length + len) a.rest (VarMap.liftApp ρ cs) k)
              (hvAppend (d := jasminSel) acc W) =
            NFProg.leakRun L fuel k (hvAppend acc V) :=
        fun acc hP => selGo_leakRun hq fuel _ _ _ a.rest _ k _ _ (length_app cs hlen)
          (envOK_carriedEnv cs a.ivs acc hP hA) (SubOK.append cs acc hD)
          (hρ.liftApp cs acc)
      have hs : ∀ (i : Nat) (X : Ctxt.Valuation (d := jasminDialect) cs)
          (r : Ctxt.Valuation (d := jasminDialect) cs × List CTLeak),
          CarriedOK (forInductive A len a inits body) cs a.ivs X →
          NFProg.leakRun L fuel body
            (hvAppend X (.cons (HasWord64.ofNat (d := jasminDialect) i) V)) = some r →
          CarriedOK (forInductive A len a inits body) cs a.ivs r.1 :=
        fun i X r hX hr => forInductive_leakStep L fuel hlen hA i X r hX hr
      have hi := forInductive_init (len := len) (a := a) (inits := inits) (body := body) hA
      have hc : (ρ _ count).lookup W = count.lookup V := hρ _ count
      simp only [selGo, NFProg.leakRun]
      erw [hc, hρ.args inits]
      exact obind_congr (forIterLeak_congr_inv _ _ _ hb hs _ _ hi) fun r hr => by
        rw [hk r.1 (forIterLeak_inv _ _ hs _ _ _ hi hr)]
        rfl
  | _, _, _, A, D, len, a, ρ, .ifThenElse (rs := rs) cond thn els k, V, W, hlen, hA, hD,
      hρ => by
      have hk : ∀ r : Ctxt.Valuation (d := jasminDialect) rs,
          NFProg.leakRun (jasminSelLeak L) fuel
              (selGo (topApp rs A) D (rs.length + len) a.rest (VarMap.liftApp ρ rs) k)
              (hvAppend (d := jasminSel) r W) =
            NFProg.leakRun L fuel k (hvAppend r V) :=
        fun r => selGo_leakRun hq fuel _ _ _ a.rest _ k _ _ (length_app rs hlen)
          (envOK_topApp rs r hA) (SubOK.append rs r hD) (hρ.liftApp rs r)
      have hc : (ρ _ cond).lookup W = cond.lookup V := hρ _ cond
      simp only [selGo, NFProg.leakRun, hk,
        selGo_leakRun hq fuel A D len a.inner ρ thn V W hlen hA hD hρ,
        selGo_leakRun hq fuel A D len a.other ρ els V W hlen hA hD hρ]
      erw [hc]
      rfl
  | _, _, _, A, D, len, a, ρ, .whileLoop (cs := cs) inits body k, V, W, hlen, hA, hD,
      hρ => by
      have hb : ∀ acc : Ctxt.Valuation (d := jasminDialect) cs,
          CarriedOK (whileInductive A len a inits body) cs a.ivs acc →
          NFProg.leakRun (jasminSelLeak L) fuel
              (selGo (carriedEnv (whileInductive A len a inits body) cs a.ivs A) D
                (cs.length + len) a.inner (VarMap.liftApp ρ cs) body)
              (hvAppend (d := jasminSel) acc W) =
            NFProg.leakRun L fuel body (hvAppend acc V) :=
        fun acc hP => selGo_leakRun hq fuel _ _ _ a.inner _ body _ _ (length_app cs hlen)
          (envOK_carriedEnv cs a.ivs acc hP hA) (SubOK.append cs acc hD)
          (hρ.liftApp cs acc)
      have hk : ∀ acc : Ctxt.Valuation (d := jasminDialect) cs,
          CarriedOK (whileInductive A len a inits body) cs a.ivs acc →
          NFProg.leakRun (jasminSelLeak L) fuel
              (selGo (carriedEnv (whileInductive A len a inits body) cs a.ivs A) D
                (cs.length + len) a.rest (VarMap.liftApp ρ cs) k)
              (hvAppend (d := jasminSel) acc W) =
            NFProg.leakRun L fuel k (hvAppend acc V) :=
        fun acc hP => selGo_leakRun hq fuel _ _ _ a.rest _ k _ _ (length_app cs hlen)
          (envOK_carriedEnv cs a.ivs acc hP hA) (SubOK.append cs acc hD)
          (hρ.liftApp cs acc)
      have hs : ∀ (X : Ctxt.Valuation (d := jasminDialect) cs)
          (r : Ctxt.Valuation (d := jasminDialect)
            (HasBitType.bit (d := jasminDialect) :: cs) × List CTLeak),
          CarriedOK (whileInductive A len a inits body) cs a.ivs X →
          NFProg.leakRun L fuel body (hvAppend X V) = some r →
          CarriedOK (whileInductive A len a inits body) cs a.ivs r.1.tail :=
        fun X r hX hr => whileInductive_leakStep L fuel hlen hA X r hX hr
      have hi := whileInductive_init (len := len) (a := a) (inits := inits) (body := body) hA
      simp only [selGo, NFProg.leakRun]
      rw [hρ.args inits]
      exact obind_congr (whileIterLeak_congr_inv _ _ _ hb hs _ _ hi) fun r hr => by
        rw [hk r.1 (whileIterLeak_inv _ _ hs _ _ _ hi hr)]
  | _, _, _, _, _, _, _, _, .call .., _, _, _, _, _, _ => rfl

end Leak

/-! ## 12. The pass -/

/-- **The range-conditioned selections**: the traversal under the annotation `a` from the
    full lane range of every input, with no recorded subtraction, along the map of the
    context to itself. -/
def rangeSel {Γ : JCtxt} {ts : List JasminTy} (a : CarriedAnn)
    (p : NFProg jasminDialect Γ ts) : NFProg jasminSel Γ ts :=
  selGo (topEnv Γ) [] Γ.length a (VarMap.same Γ) p

/-- **Denotation of the pass.** `rangeSel a p`, read in `jasminSel`, denotes the function
    `p` denotes, at every fuel and for every annotation `a`. -/
theorem rangeSel_denote {Γ : JCtxt} {ts : List JasminTy} (a : CarriedAnn)
    (p : NFProg jasminDialect Γ ts) (fuel : Nat) (V : Ctxt.Valuation Γ) :
    (rangeSel a p).denote fuel V = p.denote fuel V :=
  selGo_denote fuel _ _ _ a _ p V V rfl (envOK_topEnv V) (fun _ h => nomatch h)
    (VarMap.OK.same V)

/-- **Leakage run of the pass.** Under a leakage model `L` whose `regArith` operations are
    quiet, `rangeSel a p` runs under `jasminSelLeak L` to the results and the events of the
    run of `p` under `L`. -/
theorem rangeSel_leakRun {L : LeakModel jasminDialect}
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (fuel : Nat) {Γ : JCtxt}
    {ts : List JasminTy} (a : CarriedAnn) (p : NFProg jasminDialect Γ ts)
    (V : Ctxt.Valuation Γ) :
    NFProg.leakRun (jasminSelLeak L) fuel (rangeSel a p) V = NFProg.leakRun L fuel p V :=
  selGo_leakRun hq fuel _ _ _ a _ p V V rfl (envOK_topEnv V) (fun _ h => nomatch h)
    (VarMap.OK.same V)

/-- **Leakage of the pass, two-run.** Under a leakage model whose `regArith` operations are
    quiet, two runs of `p` that succeed with equal events give two runs of `rangeSel a p`
    that succeed under `jasminSelLeak L`, with the same results and equal events. -/
theorem rangeSel_ctRel {L : LeakModel jasminDialect}
    (hq : ∀ bop w, L.kind (.regArith bop w) = .quiet) (fuel : Nat) {Γ : JCtxt}
    {ts : List JasminTy} (a : CarriedAnn) (p : NFProg jasminDialect Γ ts)
    (V₁ V₂ : Ctxt.Valuation Γ) (r₁ r₂ : Ctxt.Valuation (d := jasminDialect) ts × List CTLeak)
    (h₁ : NFProg.leakRun L fuel p V₁ = some r₁) (h₂ : NFProg.leakRun L fuel p V₂ = some r₂)
    (he : r₁.2 = r₂.2) :
    ∃ s₁ s₂, NFProg.leakRun (jasminSelLeak L) fuel (rangeSel a p) V₁ = some s₁ ∧
      NFProg.leakRun (jasminSelLeak L) fuel (rangeSel a p) V₂ = some s₂ ∧ s₁.1 = r₁.1 ∧
      s₂.1 = r₂.1 ∧ s₁.2 = s₂.2 :=
  ⟨r₁, r₂, (rangeSel_leakRun hq fuel a p V₁).trans h₁,
    (rangeSel_leakRun hq fuel a p V₂).trans h₂, rfl, rfl, he⟩

/-! ## 13. The chain step of the pass -/

open NFProgPasses (nfSem)

/-- The pass `rangeSel` as a chain step, at the annotation `syn p` computed from the input
    `p`. The function `syn` is not trusted: the pass checks each proposal. -/
def selStep (Γ : JCtxt) (ts : List JasminTy)
    (syn : NFProg jasminDialect Γ ts → CarriedAnn) :
    PassChain.Step (NFProg jasminDialect Γ ts) (NFProg jasminSel Γ ts) :=
  ⟨"range-sel", fun p => some (rangeSel (syn p) p)⟩

/-- The certificate of the pass: at the same valuation the output has the denotation of its
    input, from `rangeSel_denote`, for every `syn`. The two relations are the graphs of the
    identity. -/
def selCert (fuel : Nat) (Γ : JCtxt) (ts : List JasminTy)
    (syn : NFProg jasminDialect Γ ts → CarriedAnn) :
    PassChain.StepCert (selStep Γ ts syn).run (nfSem fuel jasminDialect Γ ts)
      (nfSem fuel jasminSel Γ ts) :=
  PassChain.StepCert.ofTransport _ _ (fun V => V) (fun o => o) fun p q V hf => by
    cases hf
    exact (rangeSel_denote (syn p) p fuel V).trans Option.map_id'.symm

/-! ## 14. Instances

`bindCount f p` counts the bindings of `p` whose operation satisfies `f`.

On `RangeNFLoop.lazyAddLoop` the conditional subtract of the loop body is `d = t - p`
followed by the mask of `d` with `p` and the sum `r = d + m`. Under
`RangeNFLoop.lazyAddAnn` the interval of `d` is `[5 - p, 4]`, the direct form applies and
`r` becomes `umin t d`.

`maskedMul` multiplies two inputs masked to 31 bits; both operands are below `2 ^ 32` and
the product becomes `mulu 64`.

`offsetCondAdd` masks an input to 31 bits, subtracts `5` and adds `7` conditionally. The
recorded subtraction has the subtrahend `5`, so the direct form does not apply; the
second form binds `d + 7` and the unsigned minimum. -/

/-- The number of bindings of a program of `jasminSel` whose operation satisfies `f`. -/
def bindCount (f : JasminOp ⊕ SelOp → Bool) : {Γ : Ctxt jasminSel} → {ts : List JasminTy} →
    NFProg jasminSel Γ ts → Nat
  | _, _, .ret _ => 0
  | _, _, .var e k => (if f e.op then 1 else 0) + bindCount f k
  | _, _, .forLoop _ _ body k => bindCount f body + bindCount f k
  | _, _, .ifThenElse _ thn els k => bindCount f thn + bindCount f els + bindCount f k
  | _, _, .whileLoop _ body k => bindCount f body + bindCount f k
  | _, _, .call _ _ k => bindCount f k

/-- The operation is an unsigned minimum. -/
def isUmin : JasminOp ⊕ SelOp → Bool
  | .inr (.umin _) => true
  | _ => false

/-- The operation is a half-width multiply at width `w`. -/
def isMulu (w : Nat) : JasminOp ⊕ SelOp → Bool
  | .inr (.mulu w') => w' == w
  | _ => false

/-- The operation is the `regArith` operation `bop`. -/
def isArith (bop : JasminBinOp) : JasminOp ⊕ SelOp → Bool
  | .inl (.regArith b _) => b == bop
  | _ => false

/-- The product of two 64-bit inputs masked to 31 bits. -/
def maskedMul : NFProg jasminDialect [JasminTy.reg 64, JasminTy.reg 64] [JasminTy.reg 64] :=
  .var ⟨JasminOp.regConst 64 2147483647, rfl, .nil⟩
  (.var ⟨JasminOp.regArith .and 64, rfl, .cons (.there .here) (.cons .here .nil)⟩
  (.var ⟨JasminOp.regArith .and 64, rfl,
    .cons (.there (.there (.there .here))) (.cons (.there .here) .nil)⟩
  (.var ⟨JasminOp.regArith .mul 64, rfl, .cons (.there .here) (.cons .here .nil)⟩
  (.ret (.cons .here .nil)))))

/-- A 64-bit input masked to 31 bits, minus `5`, plus `7` when the difference is
    negative, in mask form. -/
def offsetCondAdd : NFProg jasminDialect [JasminTy.reg 64] [JasminTy.reg 64] :=
  .var ⟨JasminOp.regConst 64 2147483647, rfl, .nil⟩
  (.var ⟨JasminOp.regArith .and 64, rfl, .cons (.there .here) (.cons .here .nil)⟩
  (.var ⟨JasminOp.regConst 64 5, rfl, .nil⟩
  (.var ⟨JasminOp.regConst 64 7, rfl, .nil⟩
  (.var ⟨JasminOp.regConst 64 63, rfl, .nil⟩
  (.var ⟨JasminOp.regConst 64 0, rfl, .nil⟩
  (.var ⟨JasminOp.regArith .sub 64, rfl,
    .cons (.there (.there (.there (.there .here))))
      (.cons (.there (.there (.there .here))) .nil)⟩
  (.var ⟨JasminOp.regArith .shr 64, rfl,
    .cons .here (.cons (.there (.there .here)) .nil)⟩
  (.var ⟨JasminOp.regArith .sub 64, rfl,
    .cons (.there (.there .here)) (.cons .here .nil)⟩
  (.var ⟨JasminOp.regArith .and 64, rfl,
    .cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil)⟩
  (.var ⟨JasminOp.regArith .add 64, rfl,
    .cons (.there (.there (.there .here))) (.cons .here .nil)⟩
  (.ret (.cons .here .nil))))))))))))

/- On `lazyAddLoop` under `lazyAddAnn` the pass binds one unsigned minimum. The budget
   covers the start of the evaluator at the first check of the file. -/
set_option kat.ms 3000 in
#kat bindCount isUmin (rangeSel lazyAddAnn lazyAddLoop) == 1

/- `lazyAddLoop` has two `add` bindings and fifteen bindings. -/
#kat bindCount (isArith .add) (ofScalar lazyAddLoop) == 2
#kat bindCount (fun _ => true) (ofScalar lazyAddLoop) == 15

/- The pass keeps one `add` binding and the number of bindings: the direct form inserts
   no binding. -/
#kat bindCount (isArith .add) (rangeSel lazyAddAnn lazyAddLoop) == 1
#kat bindCount (fun _ => true) (rangeSel lazyAddAnn lazyAddLoop) == 15

/- On `maskedMul` the multiply becomes one `mulu 64`. -/
#kat bindCount (isArith .mul) (ofScalar maskedMul) == 1
#kat bindCount (isArith .mul) (rangeSel .empty maskedMul) == 0
#kat bindCount (isMulu 64) (rangeSel .empty maskedMul) == 1

/- On `offsetCondAdd` the second form binds one unsigned minimum and one more binding. -/
#kat bindCount isUmin (rangeSel .empty offsetCondAdd) == 1
#kat bindCount (fun _ => true) (ofScalar offsetCondAdd) == 11
#kat bindCount (fun _ => true) (rangeSel .empty offsetCondAdd) == 12

end CatCrypt.Crypto.Optimizer.Rewrite.RangeSelNF
