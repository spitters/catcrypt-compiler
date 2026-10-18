/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.ComRange
public meta import CatCrypt.Crypto.Optimizer.ConstFold
public meta import CatCrypt.Crypto.Optimizer.CopyProp
public meta import CatCrypt.Crypto.Optimizer.UncomputePass
public meta import CatCrypt.Crypto.Optimizer.ComDCE
public import CatCrypt.Crypto.SecureCompilation.VIR.ComRange
public import CatCrypt.Crypto.Optimizer.ConstFold
public import CatCrypt.Crypto.Optimizer.CopyProp
public import CatCrypt.Crypto.Optimizer.UncomputePass
public import CatCrypt.Crypto.Optimizer.ComDCE
public import CatCryptCore.Tactics.KatGuard

/-!
# Range-driven folding over straight-line `Com jasminDialect`

`rangeFold ivs c` rewrites every binding of the straight-line program `c` with the
abstract values `ComRange.exprAbs` computes from the input intervals `ivs`, in one pass:

* a register binding whose interval is one point `n` becomes `regConst w n`;
* any other binding goes through `ConstFold.foldExpr`, whose known-constant environment
  holds the point of every variable with a one-point interval. The identities `x + 0`,
  `x ||| 0`, `x ^^^ 0` and `x * 1` become the copy `x ||| x`, the annihilators `x * 0`
  and `x &&& 0` become `0`, and an operation on two points becomes a constant.

On the conditional add `d + ((0 - (d >>> (w-1))) &&& C)` of a constant `C` (the
conditional subtract of `C` from `x` when `d = x - C`), the analysis settles the sign of
`d` whenever the interval of `d` lies on one side of `2^(w-1)`:

* `d` in `[0, 2^(w-1))`: the sign word, the mask and the masked constant are the point `0`,
  and the add is a copy of `d`;
* `d` in `[2^w - 2^(w-1), 2^w)`: the mask is the point `2^w - 1`, the masked constant is
  `C`, and the add is `d + C`.

`rangeFoldStage nOut ivs c` follows the fold with copy elimination
(`CopyProp.copyElimOut`) and dead-binding elimination (`ComDCE.dceLiveOut`), which remove
the copies and the bindings the fold leaves unread and keep the last `nOut` bindings, the
outputs an owned emitter stores. Each pass is one traversal of the program, so the stage is
linear in its size. `comRangeOpt` is the opt-in entry point: its argument `none` returns
the program unchanged (`comRangeOpt_none`).

## Main definitions

* `pointOf`, `pointExpr`: the constant and the constant expression of a one-point interval.
* `rangeFoldExpr`, `rangeFoldCom`, `rangeFold`: the fold.
* `rangeFoldStage`, `comRangeOpt`: the fold with the clean-up passes, and its opt-in form.
* `ivsUniform`, `inputsIn_uniform`: one interval for every input.

## Main results

* `rangeFoldCom_denote`: under an abstract environment and a constant environment that hold
  of the valuation, the fold preserves the denotation.
* `rangeFold_denote`, `rangeFoldStage_denote`, `comRangeOpt_denote`: when every register
  input lies in its interval, the rewritten program denotes the same value.
* `rangeFold_bindVals`, `rangeFoldStage_outputs`, `comRangeOpt_outputs`: under the same
  hypothesis, the fold preserves the value of every binding, and the stage the values of
  the last `nOut` bindings (`ComDCE.outputs`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.ComRangeFold

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.Optimizer.ConstFold (constE constE_denote foldExpr foldExpr_denote)

/-! ## 1. Points of intervals -/

/-- A member of an interval whose lane interval is the point `n` is `BitVec.ofNat w n`. -/
theorem eq_ofNat_of_point {w : Nat} {i : Iv} {z : BitVec w} {n : Nat} (h : i.Mem w z)
    (hn : ivSingle? (ivLane w i) = some n) : z = BitVec.ofNat w n := by
  have hz : z.toNat = n := Iv.toNat_eq_of_single h hn
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, ← hz, Nat.mod_eq_of_lt z.isLt]

/-- The constant the interval `i` gives a value of type `t`: its point, for `t = reg w`. -/
def pointOf : (t : JasminTy) → Iv → Option Nat
  | .reg w, i => ivSingle? (ivLane w i)
  | _, _ => none

/-- The constant expression the interval `i` gives a binding of type `t`. -/
def pointExpr {Γ : JCtxt} : (t : JasminTy) → Iv → Option (Expr jasminDialect Γ t)
  | .reg w, i => (ivSingle? (ivLane w i)).map (constE w)
  | _, _ => none

theorem pointExpr_denote {Γ : JCtxt} {V : Ctxt.Valuation Γ} {t : JasminTy} {a : AVal}
    {z : ⟦t⟧} {e' : Expr jasminDialect Γ t} (h : ValOK V t a z)
    (he : pointExpr t a.1 = some e') : e'.denote V = z := by
  cases t with
  | reg w =>
    simp only [pointExpr, Option.map_eq_some_iff] at he
    obtain ⟨n, hn, rfl⟩ := he
    rw [constE_denote]
    exact (eq_ofNat_of_point (show a.1.Mem w z ∧ SymOK V w z a.2 from h).1 hn).symm
  | _ => simp [pointExpr] at he

/-- Extending a constant environment with the point of a value's abstract value keeps it
    consistent. -/
theorem consistent_cons {Γ : JCtxt} {k : KEnv Γ} {V : Ctxt.Valuation Γ}
    (hk : KEnv.Consistent k V) {u : JasminTy} {a : AVal} {z : ⟦u⟧} (hz : ValOK V u a z) :
    KEnv.Consistent (KEnv.cons (t := u) (pointOf u a.1) k) (V.extend z) := by
  intro w v n hv
  cases v with
  | here => exact eq_ofNat_of_point (show a.1.Mem w z ∧ SymOK V w z a.2 from hz).1 hv
  | there v => exact hk v n hv

/-! ## 2. The fold -/

/-- The rewrite of one binding, in a context of length `len`: a register binding with a
    one-point interval becomes that constant, and any other binding goes through
    `foldExpr` under `k`. -/
def rangeFoldExpr {Γ : JCtxt} (A : AEnv Γ) (k : KEnv Γ) (len : Nat) {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Expr jasminDialect Γ t :=
  match pointExpr t (exprAbs A e len).1 with
  | some e' => e'
  | none => foldExpr e k

theorem rangeFoldExpr_denote {Γ : JCtxt} {A : AEnv Γ} {k : KEnv Γ} {V : Ctxt.Valuation Γ}
    (hA : EnvOK A V) (hk : KEnv.Consistent k V) {len : Nat} (hlen : len = Γ.length)
    {t : JasminTy} (e : Expr jasminDialect Γ t) :
    (rangeFoldExpr A k len e).denote V = e.denote V := by
  unfold rangeFoldExpr
  rw [exprAbs_len A e hlen]
  split
  · rename_i e' he
    exact pointExpr_denote (exprAbs_sound hA e) he
  · exact foldExpr_denote e k V hk

/-- The fold of a program from the abstract environment `A` and the constant environment
    `k` of its context, whose length is `len`. -/
def rangeFoldCom : {Γ : JCtxt} → {t : JasminTy} → AEnv Γ → KEnv Γ → Nat →
    Com jasminDialect Γ t → Com jasminDialect Γ t
  | _, _, _, _, _, .ret v => .ret v
  | _, _, A, k, len, .var (t := u) e body =>
    .var (rangeFoldExpr A k len e)
      (rangeFoldCom (HVector.cons (f := fun _ => AVal) (exprAbs A e len) A)
        (KEnv.cons (pointOf u (exprAbs A e len).1) k) (len + 1) body)

/-- The fold preserves the denotation under environments that hold of the valuation. -/
theorem rangeFoldCom_denote : ∀ {Γ : JCtxt} {t : JasminTy} (A : AEnv Γ) (k : KEnv Γ)
    (len : Nat) (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ), len = Γ.length →
    EnvOK A V → KEnv.Consistent k V → (rangeFoldCom A k len c).denote V = c.denote V
  | _, _, _, _, _, .ret _, _, _, _, _ => rfl
  | _, _, A, k, len, .var e body, V, hlen, hA, hk => by
    have he := exprAbs_sound hA e
    simp only [rangeFoldCom, Com.denote]
    rw [rangeFoldExpr_denote hA hk hlen e, exprAbs_len A e hlen]
    exact rangeFoldCom_denote _ _ (len + 1) body _ (by simp [hlen]) (hA.cons he)
      (consistent_cons hk he)

/-- Every register input lies in its interval of `ivs`. -/
def InputsIn {Γ : JCtxt} (ivs : HVector (fun _ => Iv) Γ) (V : Ctxt.Valuation Γ) : Prop :=
  ∀ (w : Nat) (v : Ctxt.Var Γ (.reg w)), (hget ivs v).Mem w (v.lookup V)

theorem envOK_ofIvs {Γ : JCtxt} {ivs : HVector (fun _ => Iv) Γ} {V : Ctxt.Valuation Γ}
    (h : InputsIn ivs V) : EnvOK (AEnv.ofIvs ivs) V := by
  intro u v
  rw [hget_ofIvs]
  cases u with
  | reg w => exact ⟨h w v, SymOK.none _ _ _⟩
  | _ => trivial

/-- The constant environment of the input points. -/
def kOfIvs : {Γ : JCtxt} → HVector (fun _ => Iv) Γ → KEnv Γ
  | [], .nil => .nil
  | t :: _, .cons i is => .cons (pointOf t i) (kOfIvs is)

theorem lookup_kOfIvs : ∀ {Γ : JCtxt} {t : JasminTy} (ivs : HVector (fun _ => Iv) Γ)
    (v : Ctxt.Var Γ t), KEnv.lookup v (kOfIvs ivs) = pointOf t (hget ivs v)
  | _ :: _, _, .cons _ _, .here => rfl
  | _ :: _, _, .cons _ is, .there v => lookup_kOfIvs is v

theorem kOfIvs_consistent {Γ : JCtxt} {ivs : HVector (fun _ => Iv) Γ}
    {V : Ctxt.Valuation Γ} (h : InputsIn ivs V) : KEnv.Consistent (kOfIvs ivs) V := by
  intro w v n hv
  rw [lookup_kOfIvs] at hv
  exact eq_ofNat_of_point (h w v) hv

/-- The range fold of `c` from the input intervals `ivs`. -/
def rangeFold {Γ : JCtxt} {t : JasminTy} (ivs : HVector (fun _ => Iv) Γ)
    (c : Com jasminDialect Γ t) : Com jasminDialect Γ t :=
  rangeFoldCom (AEnv.ofIvs ivs) (kOfIvs ivs) Γ.length c

/-- **Soundness of the range fold**: when every register input lies in its interval, the
    folded program denotes the same value. -/
theorem rangeFold_denote {Γ : JCtxt} {t : JasminTy} (ivs : HVector (fun _ => Iv) Γ)
    (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ) (h : InputsIn ivs V) :
    (rangeFold ivs c).denote V = c.denote V :=
  rangeFoldCom_denote _ _ _ c V rfl (envOK_ofIvs h) (kOfIvs_consistent h)

/-- The fold rewrites each binding into one binding of the same value: under environments
    that hold of the valuation, it preserves the value of every binding. -/
theorem rangeFoldCom_bindVals : ∀ {Γ : JCtxt} {t : JasminTy} (A : AEnv Γ) (k : KEnv Γ)
    (len : Nat) (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ), len = Γ.length →
    EnvOK A V → KEnv.Consistent k V →
    ComDCE.bindVals (rangeFoldCom A k len c) V = ComDCE.bindVals c V
  | _, _, _, _, _, .ret _, _, _, _, _ => rfl
  | _, _, A, k, len, .var e body, V, hlen, hA, hk => by
    have he := exprAbs_sound hA e
    simp only [rangeFoldCom, ComDCE.bindVals]
    rw [rangeFoldExpr_denote hA hk hlen e, exprAbs_len A e hlen,
      rangeFoldCom_bindVals _ _ (len + 1) body _ (by simp [hlen]) (hA.cons he)
        (consistent_cons hk he)]

/-- When every register input lies in its interval, the folded program has the binding
    values of the source. -/
theorem rangeFold_bindVals {Γ : JCtxt} {t : JasminTy} (ivs : HVector (fun _ => Iv) Γ)
    (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ) (h : InputsIn ivs V) :
    ComDCE.bindVals (rangeFold ivs c) V = ComDCE.bindVals c V :=
  rangeFoldCom_bindVals _ _ _ c V rfl (envOK_ofIvs h) (kOfIvs_consistent h)

/-- The interval `i` for every variable of a context. -/
def ivsUniform (i : Iv) : (Γ : JCtxt) → HVector (fun _ => Iv) Γ
  | [] => .nil
  | _ :: Γ => .cons i (ivsUniform i Γ)

theorem hget_ivsUniform (i : Iv) : ∀ {Γ : JCtxt} {t : JasminTy} (v : Ctxt.Var Γ t),
    hget (ivsUniform i Γ) v = i
  | _ :: _, _, .here => rfl
  | _ :: _, _, .there v => hget_ivsUniform i v

/-- Every register input lies in `i` when every register input is a member of `i`. -/
theorem inputsIn_uniform {Γ : JCtxt} {i : Iv} {V : Ctxt.Valuation Γ}
    (h : ∀ (w : Nat) (v : Ctxt.Var Γ (.reg w)), i.Mem w (v.lookup V)) :
    InputsIn (ivsUniform i Γ) V := by
  intro w v
  rw [hget_ivsUniform]
  exact h w v

/-! ## 3. The stage and its opt-in form -/

/-- The range fold followed by copy elimination and dead-binding elimination, keeping the
    last `nOut` bindings (the outputs an owned emitter stores). Each of the three passes is
    one traversal (`rangeFoldCom` tracks the length of its context,
    `CopyProp.copyElimOut` carries one renaming, `ComDCE.dceLiveOut` marks liveness in one
    backward scan), so the stage is linear in the size of the program. -/
def rangeFoldStage (nOut : Nat) {Γ : JCtxt} {t : JasminTy}
    (ivs : HVector (fun _ => Iv) Γ) (c : Com jasminDialect Γ t) : Com jasminDialect Γ t :=
  ComDCE.dceLiveOut nOut (CopyProp.copyElimOut nOut (rangeFold ivs c))

/-- **Soundness of the range-fold stage**: when every register input lies in its interval,
    the rewritten program denotes the same value. -/
theorem rangeFoldStage_denote (nOut : Nat) {Γ : JCtxt} {t : JasminTy}
    (ivs : HVector (fun _ => Iv) Γ) (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ)
    (h : InputsIn ivs V) : (rangeFoldStage nOut ivs c).denote V = c.denote V := by
  unfold rangeFoldStage
  rw [ComDCE.dceLiveOut_denote, CopyProp.copyElimOut_denote, rangeFold_denote ivs c V h]

/-- **The range-fold stage preserves the outputs**: when every register input lies in its
    interval, the last `nOut` bindings of the rewritten program hold the values of the last
    `nOut` bindings of the source. -/
theorem rangeFoldStage_outputs (nOut : Nat) {Γ : JCtxt} {t : JasminTy}
    (ivs : HVector (fun _ => Iv) Γ) (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ)
    (h : InputsIn ivs V) :
    ComDCE.outputs nOut (rangeFoldStage nOut ivs c) V = ComDCE.outputs nOut c V := by
  unfold rangeFoldStage
  rw [ComDCE.dceLiveOut_outputs, CopyProp.copyElimOut_outputs]
  unfold ComDCE.outputs
  rw [rangeFold_bindVals ivs c V h]

/-- The opt-in range-fold stage: `none` leaves the program unchanged, `some ivs` runs
    `rangeFoldStage nOut ivs`. -/
def comRangeOpt (nOut : Nat) {Γ : JCtxt} {t : JasminTy}
    (ivs? : Option (HVector (fun _ => Iv) Γ)) (c : Com jasminDialect Γ t) :
    Com jasminDialect Γ t :=
  match ivs? with
  | none => c
  | some ivs => rangeFoldStage nOut ivs c

theorem comRangeOpt_none (nOut : Nat) {Γ : JCtxt} {t : JasminTy}
    (c : Com jasminDialect Γ t) : comRangeOpt nOut none c = c := rfl

/-- **Soundness of the opt-in stage**: when the stage is on, with every register input in
    its interval, the rewritten program denotes the same value. -/
theorem comRangeOpt_denote (nOut : Nat) {Γ : JCtxt} {t : JasminTy}
    (ivs? : Option (HVector (fun _ => Iv) Γ)) (c : Com jasminDialect Γ t)
    (V : Ctxt.Valuation Γ) (h : ∀ ivs, ivs? = some ivs → InputsIn ivs V) :
    (comRangeOpt nOut ivs? c).denote V = c.denote V := by
  cases ivs? with
  | none => rfl
  | some ivs => exact rangeFoldStage_denote nOut ivs c V (h ivs rfl)

/-- **The opt-in stage preserves the outputs**: when the stage is on, with every register
    input in its interval, the last `nOut` binding values are unchanged. -/
theorem comRangeOpt_outputs (nOut : Nat) {Γ : JCtxt} {t : JasminTy}
    (ivs? : Option (HVector (fun _ => Iv) Γ)) (c : Com jasminDialect Γ t)
    (V : Ctxt.Valuation Γ) (h : ∀ ivs, ivs? = some ivs → InputsIn ivs V) :
    ComDCE.outputs nOut (comRangeOpt nOut ivs? c) V = ComDCE.outputs nOut c V := by
  cases ivs? with
  | none => rfl
  | some ivs => exact rangeFoldStage_outputs nOut ivs c V (h ivs rfl)

/-! ## 4. Static checks

`condSub64` is the conditional subtract of the BabyBear prime `p` from the input `x`
(level 0) at 64 bits: `d = x - p`, the sign word of `d`, its negation, the mask with `p`,
and the conditional add, returning the last binding. -/

/-- The conditional subtract of `p = 2013265921` as eight bindings. -/
def condSub64 : List Step :=
  [.const 2013265921, .const 63, .const 0,
   .bin .sub 0 1, .bin .shr 4 2, .bin .sub 3 5, .bin .and 6 1, .bin .add 4 7]

/- On `x` in `[p, 2p - 1]` the subtract always applies: the stage leaves the constant `p`
   and `x - p`. The first check of the file also pays for compiling the stage, so its budget
   is larger. -/
set_option kat.ms 1000 in
#kat (build 64 [.reg 64] condSub64).map (fun c =>
    UncomputePass.comLen (rangeFoldStage 0 (.cons (2013265921, 4026531841) .nil) c))
  == some 2

/- On the same interval with the last three bindings as outputs, the stage keeps them (the
   folded negation and mask, and the copy of `x - p` the add becomes) with `p` and `x - p`. -/
#kat (build 64 [.reg 64] condSub64).map (fun c =>
    UncomputePass.comLen (rangeFoldStage 3 (.cons (2013265921, 4026531841) .nil) c))
  == some 5

/- On `x` in `[0, p - 1]` the subtract never applies: the sign word, its negation and the
   masked constant fold, and the stage leaves `p`, `x - p`, `p` and their sum. -/
#kat (build 64 [.reg 64] condSub64).map (fun c =>
    UncomputePass.comLen (rangeFoldStage 0 (.cons (0, 2013265920) .nil) c))
  == some 4

/- On `x` in `[0, 2p - 1]` the analysis does not settle the sign and all eight bindings
   stay. -/
#kat (build 64 [.reg 64] condSub64).map (fun c =>
    UncomputePass.comLen (rangeFoldStage 0 (.cons (0, 4026531841) .nil) c))
  == some 8

end CatCrypt.Crypto.Optimizer.ComRangeFold
