/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd

@[expose] public section

set_option autoImplicit false

/-!
# Boolean checks of the stack-memory fragments

The export theorems of a straight-line body and of a runtime-count loop node take the
fragment conditions `ScalarMemN` (a register-returning chain), `ArrMemN` (an array-returning
chain of register heads and stores) and `ComExpOK` (every op in the fragment's op set, with an
immediate shift whose wire the decoder reads back) as hypotheses. This module decides each of
them by a structural recursion over the `Com`, so that a compiler can gate on them.

## Main results

* `opMemB`, `opMemB_sound` — the op set of the fragment with its side conditions.
* `scalarMemNB`, `scalarMemNB_sound` — a decision of `ScalarMemN`.
* `arrMemNB`, `arrMemNB_sound` — a decision of `ArrMemN`.
* `comExpOKB`, `comExpOKB_sound` — a decision of `ComExpOK`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (hasSuffix)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (ScalarMemN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop (OpPlain)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportShippedAnd
  (ComExpOK ImmShiftWireOK)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond
  (ArrMemN RegHeadMemN)

/-! ## 1. The op set -/

/-- The ops of the stack-memory fragment with the side conditions `ScalarMemN` asks: a
    constant at a positive width, an immediate shift by less than `2 ^ w`. -/
def opMemB : JasminOp → Bool
  | .regArith _ _ | .select _ | .mulhi _ | .addCarryLo _ | .addCarryHi _ | .castW _ _
  | .stackLoad _ _ | .stackStore _ _ | .cmp _ _ | .cmpImm _ _ _ => true
  | .regConst w _ => decide (0 < w)
  | .shrImm w m | .shlImm w m | .sarImm w m => decide (m < 2 ^ w)
  | _ => false

/-- A decision of `OpPlain`. -/
def opPlainB : JasminOp → Bool
  | .regArith _ _ | .regConst _ _ | .select _ | .shrImm _ _ | .shlImm _ _
  | .sarImm _ _ | .mulhi _ | .addCarryLo _ | .addCarryHi _ | .castW _ _
  | .stackLoad _ _ | .stackStore _ _ | .cmp _ _ | .cmpImm _ _ _ => true
  | _ => false

theorem opPlainB_sound {op : JasminOp} (h : opPlainB op = true) : OpPlain op := by
  cases op <;> simp_all [opPlainB, OpPlain]

/-- A decision of `ImmShiftWireOK`. -/
def immShiftWireOKB : JasminOp → Bool
  | .shrImm w n => w == 64 || !hasSuffix ("SHR" ++ ":" ++ toString n) ":64"
  | .shlImm w n => w == 64 || !hasSuffix ("SHL" ++ ":" ++ toString n) ":64"
  | .sarImm w n => w == 64 || !hasSuffix ("SAR" ++ ":" ++ toString n) ":64"
  | _ => true

theorem immShiftWireOKB_sound {op : JasminOp} (h : immShiftWireOKB op = true) :
    ImmShiftWireOK op := by
  cases op <;> simp_all [immShiftWireOKB, ImmShiftWireOK]

/-! ## 2. The fragments -/

/-- A decision of `ScalarMemN`: every binding's op is in `opMemB` and the return is a
    register. -/
def scalarMemNB : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Bool
  | _, .reg _, .ret _ => true
  | _, _, .ret _ => false
  | _, _, .var e body => opMemB e.op && scalarMemNB body

theorem scalarMemNB_sound : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → scalarMemNB c = true → ScalarMemN c
  | _, .reg _, .ret v, _ => ScalarMemN.ret v
  | _, .stackArr _ _, .ret _, h => by simp [scalarMemNB] at h
  | _, .inlineInt, .ret _, h => by simp [scalarMemNB] at h
  | _, .bool, .ret _, h => by simp [scalarMemNB] at h
  | _, _, .var ⟨op, heq, args⟩ body, h => by
      simp only [scalarMemNB, Bool.and_eq_true] at h
      obtain ⟨hop, hb⟩ := h
      have ih := scalarMemNB_sound body hb
      cases op <;> simp only [opMemB, Bool.false_eq_true, decide_eq_true_eq] at hop
      all_goals first
        | cases heq; exact ScalarMemN.var _ rfl args ih
        | cases heq; exact ScalarMemN.const _ hop rfl args ih
        | cases heq; exact ScalarMemN.sel rfl args ih
        | cases heq; exact ScalarMemN.shr hop rfl args ih
        | cases heq; exact ScalarMemN.shl hop rfl args ih
        | cases heq; exact ScalarMemN.sar hop rfl args ih
        | cases heq; exact ScalarMemN.mulhi rfl args ih
        | cases heq; exact ScalarMemN.addLo rfl args ih
        | cases heq; exact ScalarMemN.addHi rfl args ih
        | cases heq; exact ScalarMemN.cast rfl args ih
        | cases heq; exact ScalarMemN.load rfl args ih
        | cases heq; exact ScalarMemN.store rfl args ih
        | cases heq; exact ScalarMemN.cmp _ rfl args ih
        | cases heq; exact ScalarMemN.cmpImm _ rfl args ih

/-- A decision of `ArrMemN`: every binding's op is in `opMemB`; the return type is the
    array type of the index, so the return needs no check. -/
def arrMemNB : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body => opMemB e.op && arrMemNB body

/-- A register head whose op is in `opMemB` is in `RegHeadMemN`. -/
theorem regHeadMemN_of_opMemB {Γ : Ctxt jasminDialect} {w : Nat}
    (e : Expr jasminDialect Γ (JasminTy.reg w)) (h : opMemB e.op = true) : RegHeadMemN e := by
  unfold RegHeadMemN
  refine scalarMemNB_sound _ ?_
  simp [scalarMemNB, h]

theorem arrMemNB_sound {w n : Nat} : {Γ : Ctxt jasminDialect} →
    (c : Com jasminDialect Γ (JasminTy.stackArr w n)) → arrMemNB c = true → ArrMemN c
  | _, .ret v, _ => ArrMemN.ret v
  | _, .var ⟨op, heq, args⟩ body, h => by
      simp only [arrMemNB, Bool.and_eq_true] at h
      obtain ⟨hop, hb⟩ := h
      have ih := arrMemNB_sound body hb
      cases op <;> simp only [opMemB, Bool.false_eq_true] at hop
      case stackStore w' n' =>
        cases heq
        exact ArrMemN.store rfl args ih
      all_goals
        cases heq
        exact ArrMemN.reg (w' := _) _ (regHeadMemN_of_opMemB _ (by simp [opMemB, hop])) ih

/-- A decision of `ComExpOK`. -/
def comExpOKB : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Bool
  | _, _, .ret _ => true
  | _, _, .var e body => opPlainB e.op && immShiftWireOKB e.op && comExpOKB body

theorem comExpOKB_sound : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com jasminDialect Γ t) → comExpOKB c = true → ComExpOK c
  | _, _, .ret _, _ => trivial
  | _, _, .var e body, h => by
      simp only [comExpOKB, Bool.and_eq_true] at h
      exact ⟨opPlainB_sound h.1.1, immShiftWireOKB_sound h.1.2, comExpOKB_sound body h.2⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment
