/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminOutStageLeak
public import CatCrypt.Crypto.Optimizer.ComRangeFold

/-!
# The passes of the range-fold stage preserve a predicate on operations

`comAllOps P c` holds when every binding of the straight-line program `c` has an operation
satisfying `P`. For a predicate that holds of every `regArith` and every `regConst`
operation, each pass of `ComRangeFold.comRangeOpt` preserves it:

* the range fold replaces a binding by a `regConst` binding or by `ConstFold.foldExpr` of
  it, which is the binding itself, a `regArith` binding or a `regConst` binding;
* copy elimination deletes or renames bindings;
* dead-binding elimination deletes or re-indexes bindings.

At the parameters `Pj` with no variable-time operation (`Pj.opVT op = none` for every `op`),
`quietB Pj` is such a predicate, so a program of quiet operations stays one through the
stage (`comAllOps_comRangeOpt_quiet`).

## Main results

* `comAllOps_rangeFoldCom`, `comAllOps_copyElimOut`, `comAllOps_dceLiveOut`: each pass
  preserves `comAllOps P`.
* `comAllOps_comRangeOpt`: the opt-in stage preserves `comAllOps P`.
* `quietB_regArith`, `quietB_regConst`, `comAllOps_comRangeOpt_quiet`: the instance at
  `quietB Pj`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.ComPassQuiet

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminOutStage (comAllOps quietB)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jKind)
open CatCrypt.Crypto.Optimizer.ConstFold (constE foldBin foldExpr)
open CatCrypt.Crypto.Optimizer.ComRangeFold
open CatCrypt.Crypto.Optimizer.Rewrite.Egraph
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange
open CatCrypt.Crypto.SecureCompilation.RangeDomain (Iv)

variable (P : JasminOp → Bool)

/-! ## 1. The range fold -/

/-- `foldExpr` keeps an operation satisfying `P` when `P` holds of every `regArith` and
    `regConst` operation. -/
theorem foldExpr_op (hA : ∀ bop w, P (.regArith bop w) = true)
    (hC : ∀ w n, P (.regConst w n) = true) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (k : KEnv Γ) (he : P e.op = true) :
    P (foldExpr e k).op = true := by
  rcases e with ⟨op, hop, args⟩
  cases op
  case regArith bop w =>
    subst hop
    match args, (rfl : args = args) with
    | .cons a (.cons b .nil), _ =>
      simp only [foldExpr, HVector.head, HVector.tail]
      rcases hr : foldBin bop a b (KEnv.lookup a k) (KEnv.lookup b k) with _ | e'
      · exact hA bop w
      · have hform : (∃ bop', e'.op = .regArith bop' w) ∨ ∃ n, e' = constE w n := by
          unfold foldBin at hr
          split at hr <;> (try split at hr) <;>
            first
              | (cases hr; exact Or.inl ⟨_, rfl⟩)
              | (cases hr; exact Or.inr ⟨_, rfl⟩)
              | cases hr
        rcases hform with ⟨bop', hop'⟩ | ⟨n, rfl⟩
        · change P e'.op = true
          rw [hop']
          exact hA bop' w
        · exact hC w n
  all_goals exact he

/-- The rewrite of one binding by the range fold keeps an operation satisfying `P`. -/
theorem rangeFoldExpr_op (hA : ∀ bop w, P (.regArith bop w) = true)
    (hC : ∀ w n, P (.regConst w n) = true) {Γ : JCtxt} (A : AEnv Γ) (k : KEnv Γ)
    (len : Nat) {t : JasminTy} (e : Expr jasminDialect Γ t) (he : P e.op = true) :
    P (rangeFoldExpr A k len e).op = true := by
  unfold rangeFoldExpr
  split
  · rename_i e' hp
    cases t with
    | reg w =>
      simp only [pointExpr, Option.map_eq_some_iff] at hp
      obtain ⟨n, _, rfl⟩ := hp
      exact hC w n
    | _ => simp [pointExpr] at hp
  · exact foldExpr_op P hA hC e k he

/-- **The range fold preserves `comAllOps P`.** -/
theorem comAllOps_rangeFoldCom (hA : ∀ bop w, P (.regArith bop w) = true)
    (hC : ∀ w n, P (.regConst w n) = true) : ∀ {Γ : JCtxt} {t : JasminTy} (A : AEnv Γ)
    (k : KEnv Γ) (len : Nat) (c : Com jasminDialect Γ t),
    comAllOps P c = true → comAllOps P (rangeFoldCom A k len c) = true
  | _, _, _, _, _, .ret _, _ => rfl
  | _, _, A, k, len, .var e body, h => by
    simp only [comAllOps, Bool.and_eq_true] at h
    simp only [rangeFoldCom, comAllOps, Bool.and_eq_true]
    exact ⟨rangeFoldExpr_op P hA hC A k len e h.1,
      comAllOps_rangeFoldCom hA hC _ _ _ body h.2⟩

/-! ## 2. Copy elimination -/

/-- Copy elimination outside the last `k` bindings preserves `comAllOps P`: it deletes
    bindings and renames the others. -/
theorem comAllOps_copyElimOutGo (R : CopyProp.Generic.CopyRecog jasminDialect) (k : Nat) :
    ∀ {Γ Δ : Ctxt jasminDialect} {t : JasminTy} (rem : Nat) (ρ : Ctxt.Hom Γ Δ)
    (c : Com jasminDialect Γ t),
    comAllOps P c = true → comAllOps P (CopyProp.Generic.copyElimOutGo R k rem ρ c) = true
  | _, _, _, _, _, .ret _, _ => rfl
  | _, _, _, rem, ρ, .var e body, h => by
    simp only [comAllOps, Bool.and_eq_true] at h
    simp only [CopyProp.Generic.copyElimOutGo]
    split
    · exact comAllOps_copyElimOutGo R k (rem - 1) _ body h.2
    · simp only [comAllOps, Expr.op_rename, Bool.and_eq_true]
      exact ⟨h.1, comAllOps_copyElimOutGo R k (rem - 1) _ body h.2⟩

/-- **`copyElimOut` preserves `comAllOps P`.** -/
theorem comAllOps_copyElimOut (nOut : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (h : comAllOps P c = true) :
    comAllOps P (CopyProp.copyElimOut nOut c) = true :=
  comAllOps_copyElimOutGo P _ nOut _ _ c h

/-! ## 3. Dead-binding elimination -/

/-- The rebuild of dead-binding elimination preserves `comAllOps P`: it drops bindings and
    re-indexes the arguments of the others. -/
theorem comAllOps_dceGoWith (keep : Nat → Bool) :
    ∀ {Δ Γ : Ctxt jasminDialect} {t : JasminTy} (n : Nat) (θ : ComDCE.Thinning Δ Γ)
    (c : Com jasminDialect Γ t) (c' : Com jasminDialect Δ t),
    ComDCE.dceGoWith keep n θ c = some c' → comAllOps P c = true → comAllOps P c' = true
  | _, _, _, _, θ, .ret v, c', h, _ => by
    simp only [ComDCE.dceGoWith, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    rfl
  | _, _, _, n, θ, .var (t := u) e body, c', h, hc => by
    simp only [comAllOps, Bool.and_eq_true] at hc
    simp only [ComDCE.dceGoWith] at h
    split at h
    · split at h
      · rename_i e' b he hb
        simp only [Option.some.injEq] at h
        subst h
        simp only [ComDCE.Thinning.getExpr, Option.map_eq_some_iff] at he
        obtain ⟨_, _, rfl⟩ := he
        simp only [comAllOps, Bool.and_eq_true]
        exact ⟨hc.1, comAllOps_dceGoWith keep (n + 1) _ body b hb hc.2⟩
      · cases h
    · exact comAllOps_dceGoWith keep (n + 1) _ body c' h hc.2

/-- **`dceLiveOut` preserves `comAllOps P`.** -/
theorem comAllOps_dceLiveOut (nOut : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (h : comAllOps P c = true) :
    comAllOps P (ComDCE.dceLiveOut nOut c) = true := by
  unfold ComDCE.dceLiveOut
  dsimp only
  split
  · rename_i c' hc
    exact comAllOps_dceGoWith P _ _ _ c c' hc h
  · exact h

/-! ## 4. The stage -/

/-- **The range-fold stage preserves `comAllOps P`.** -/
theorem comAllOps_rangeFoldStage (hA : ∀ bop w, P (.regArith bop w) = true)
    (hC : ∀ w n, P (.regConst w n) = true) (nOut : Nat) {Γ : JCtxt} {t : JasminTy}
    (ivs : HVector (fun _ => Iv) Γ) (c : Com jasminDialect Γ t)
    (h : comAllOps P c = true) : comAllOps P (rangeFoldStage nOut ivs c) = true :=
  comAllOps_dceLiveOut P nOut _
    (comAllOps_copyElimOut P nOut _ (comAllOps_rangeFoldCom P hA hC _ _ _ c h))

/-- **The opt-in range-fold stage preserves `comAllOps P`.** -/
theorem comAllOps_comRangeOpt (hA : ∀ bop w, P (.regArith bop w) = true)
    (hC : ∀ w n, P (.regConst w n) = true) (nOut : Nat) {Γ : JCtxt} {t : JasminTy}
    (ivs? : Option (HVector (fun _ => Iv) Γ)) (c : Com jasminDialect Γ t)
    (h : comAllOps P c = true) : comAllOps P (comRangeOpt nOut ivs? c) = true := by
  cases ivs? with
  | none => exact h
  | some ivs => exact comAllOps_rangeFoldStage P hA hC nOut ivs c h

/-! ## 5. Quiet operations -/

/-- A `regArith` operation is quiet at parameters with no variable-time operation. -/
theorem quietB_regArith {Pj : JLeakParams} (hvt : ∀ op, Pj.opVT op = none)
    (bop : JasminBinOp) (w : Nat) : quietB Pj (.regArith bop w) = true := by
  simp only [quietB, jKind, hvt]

/-- A `regConst` operation is quiet at parameters with no variable-time operation. -/
theorem quietB_regConst {Pj : JLeakParams} (hvt : ∀ op, Pj.opVT op = none) (w n : Nat) :
    quietB Pj (.regConst w n) = true := by
  simp only [quietB, jKind, hvt]

/-- **The opt-in range-fold stage keeps a program of quiet operations one**, at parameters
    with no variable-time operation. -/
theorem comAllOps_comRangeOpt_quiet {Pj : JLeakParams} (hvt : ∀ op, Pj.opVT op = none)
    (nOut : Nat) {Γ : JCtxt} {t : JasminTy}
    (ivs? : Option (HVector (fun _ => Iv) Γ)) (c : Com jasminDialect Γ t)
    (h : comAllOps (quietB Pj) c = true) :
    comAllOps (quietB Pj) (comRangeOpt nOut ivs? c) = true :=
  comAllOps_comRangeOpt _ (quietB_regArith hvt) (quietB_regConst hvt) nOut ivs? c h

end CatCrypt.Crypto.Optimizer.ComPassQuiet
