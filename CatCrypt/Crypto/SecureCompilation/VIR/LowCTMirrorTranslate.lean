/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
public import CatCrypt.Crypto.Jasmin.LowCTToJasmin

/-!
# The `LowCT` lowering lands in the domain of the mirror translation

`LowCTToJasmin.toJasminCmd` lowers a `LowCT` program to a JasminAST command, and
`InstrRTranslateExt.translateCmdExt` translates JasminAST commands to the `psem.v`
mirror. On the fragment `callFreePlusCall` (call-free programs together with single
`RCall`, `RLimbStore` and `RCloneCall` leaves under `RSeq` and `RIfNz`), every
lowered command has a mirror translation.

## Main results

- `toJasminCmd_translateCmdExt_isSome`: for `callFreePlusCall c = true`,
  `translateCmdExt (toJasminCmd c)` is `some`.
- `translateCmdExt_append`: the translation of a concatenation is the
  concatenation of the translations.
- `unrollForJ_translateCmdExt_isSome`: the unrolled counted loop translates when
  its body does.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LowCTMirrorTranslate

open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslate
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateExt
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCT.RustExecWithCalls

/-- `List.mapM` over `Option` is `some` when every element maps to `some`. -/
theorem mapM_isSome_of_forall {α β : Type} (f : α → Option β) :
    ∀ (l : List α), (∀ a ∈ l, (f a).isSome = true) → (l.mapM f).isSome = true
  | [], _ => rfl
  | a :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a List.mem_cons_self)
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.mp
      (mapM_isSome_of_forall f l (fun x hx => h x (List.mem_cons_of_mem a hx)))
    simp [List.mapM_cons, hb, hbs]

/-- The translation of a concatenation is the concatenation of the translations. -/
theorem translateCmdExt_append :
    ∀ (a b : List AInstrR), translateCmdExt (a ++ b) =
      (match translateCmdExt a, translateCmdExt b with
       | some a', some b' => some (a' ++ b')
       | _, _ => none)
  | [], b => by cases h : translateCmdExt b <;> simp [translateCmdExt, h]
  | i :: a, b => by
    simp only [List.cons_append, translateCmdExt, translateCmdExt_append a b]
    cases translateInstrRExt i <;> cases translateCmdExt a <;> cases translateCmdExt b <;> rfl

/-- A concatenation translates when both parts do. -/
theorem translateCmdExt_append_isSome (a b : List AInstrR)
    (ha : (translateCmdExt a).isSome = true) (hb : (translateCmdExt b).isSome = true) :
    (translateCmdExt (a ++ b)).isSome = true := by
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp hb
  rw [translateCmdExt_append, ha', hb']
  rfl

/-- A command `i :: c` translates when `i` and `c` do. -/
theorem translateCmdExt_cons_isSome (i : AInstrR) (c : List AInstrR)
    (hi : (translateInstrRExt i).isSome = true) (hc : (translateCmdExt c).isSome = true) :
    (translateCmdExt (i :: c)).isSome = true := by
  obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.mp hi
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hc
  simp [translateCmdExt, hi', hc']

/-- The l-value of a tower location translates. -/
theorem translateLValExt_locToLVal_isSome (loc : Located) :
    (translateLValExt (locToLVal loc)).isSome = true := by
  simp [locToLVal, locToVar, towerToSType, translateLValExt, translateVarIExt, translateVarExt,
    translateSTypeExt]

/-- The read of a tower location translates. -/
theorem translatePExprExt_locToPExpr_isSome (loc : Located) :
    (translatePExprExt (locToPExpr loc)).isSome = true := by
  simp [locToPExpr, locToGVar, locToVar, towerToSType, translatePExprExt, translateGVarExt,
    translateVarIExt, translateVarExt, translateSTypeExt]

/-- A call over tower-location destinations and arguments translates. -/
theorem ccall_locs_translateInstrRExt_isSome (f : String) (dests args : List Located) :
    (translateInstrRExt (.Ccall .DoNotInline (dests.map locToLVal) { name := f }
      (args.map locToPExpr))).isSome = true := by
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp
    (mapM_isSome_of_forall translateLValExt (dests.map locToLVal) (fun a ha => by
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp ha
      exact translateLValExt_locToLVal_isSome d))
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp
    (mapM_isSome_of_forall translatePExprExt (args.map locToPExpr) (fun a ha => by
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp ha
      exact translatePExprExt_locToPExpr_isSome d))
  simp [translateInstrRExt, hl, he]

/-- The unrolled counted loop translates when its body does. -/
theorem unrollForJ_translateCmdExt_isSome (x : String) (bodyJ : List AInstrR)
    (hb : (translateCmdExt bodyJ).isSome = true) :
    ∀ n, (translateCmdExt (unrollForJ x bodyJ n)).isSome = true
  | 0 => rfl
  | n + 1 => by
    simp only [unrollForJ]
    refine translateCmdExt_append_isSome _ _ (unrollForJ_translateCmdExt_isSome x bodyJ hb n) ?_
    refine translateCmdExt_cons_isSome _ _ ?_ hb
    simp [translateInstrRExt, translateLValExt, translateVarIExt, translateVarExt,
      translateSTypeExt, translateSType, translateWSize, translatePExprExt, translateSOp1,
      translatePExpr]

/-- **Totality on the call fragment.** Every `LowCT` program in `callFreePlusCall`
    lowers to a JasminAST command that `translateCmdExt` translates to the mirror. -/
theorem toJasminCmd_translateCmdExt_isSome :
    ∀ (c : LowCT), callFreePlusCall c = true →
      (translateCmdExt (toJasminCmd c)).isSome = true := by
  intro c h
  induction c with
  | RSkip => rfl
  | RSeq c1 c2 ih1 ih2 =>
    simp only [callFreePlusCall, Bool.and_eq_true] at h
    simpa using translateCmdExt_append_isSome _ _ (ih1 h.1) (ih2 h.2)
  | RLetZero x t body ih =>
    simp only [callFreePlusCall, callFree] at h
    rw [toJasminCmd_RLetZero]
    refine translateCmdExt_cons_isSome _ _ ?_ (ih (callFreePlusCall_of_callFree _ h))
    simp [translateInstrRExt, translateLValExt, translateVarIExt, translateVarExt,
      translateSTypeExt, translatePExprExt]
  | RLetU64Zero x body ih =>
    simp only [callFreePlusCall, callFree] at h
    rw [toJasminCmd_RLetU64Zero]
    refine translateCmdExt_cons_isSome _ _ ?_ (ih (callFreePlusCall_of_callFree _ h))
    simp [translateInstrRExt, translateLValExt, translateVarIExt, translateVarExt,
      translateSTypeExt, translateSType, translateWSize, translatePExprExt, translatePExpr]
  | RScalarSet x v =>
    simp [translateCmdExt, translateInstrRExt, translateLValExt, translateVarIExt,
      translateVarExt, translateSTypeExt, translateSType, translateWSize, translatePExprExt,
      translateSOp1, translatePExpr]
  | RCall f dest args =>
    rw [toJasminCmd_RCall]
    exact translateCmdExt_cons_isSome _ _ (ccall_locs_translateInstrRExt_isSome f [dest] args) rfl
  | RCloneCall cv ct od f dest args =>
    rw [toJasminCmd_RCloneCall]
    refine translateCmdExt_cons_isSome _ _ ?_
      (translateCmdExt_cons_isSome _ _ (ccall_locs_translateInstrRExt_isSome f [dest] args) rfl)
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (translatePExprExt_locToPExpr_isSome od)
    simp [translateInstrRExt, translateLValExt, translateVarIExt, translateVarExt,
      translateSTypeExt, he]
  | RIfNz e ct cf ih1 ih2 =>
    simp only [callFreePlusCall, Bool.and_eq_true] at h
    rw [toJasminCmd_RIfNz]
    refine translateCmdExt_cons_isSome _ _ ?_ rfl
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (ih1 h.1)
    obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp (ih2 h.2)
    simp [translateInstrRExt, ht, hf, translatePExprExt, translateSOp2Ext, translateWSize,
      translateGVarExt, translateVarIExt, translateVarExt, translateSTypeExt, translateSType,
      translateSOp1, translatePExpr]
  | RWhileNz e body ih =>
    simp only [callFreePlusCall, callFree] at h
    rw [toJasminCmd_RWhileNz]
    refine translateCmdExt_cons_isSome _ _ ?_ rfl
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (ih (callFreePlusCall_of_callFree _ h))
    simp [translateInstrRExt, hb, translateCmdExt, translatePExprExt, translateSOp2Ext,
      translateWSize, translateGVarExt, translateVarIExt, translateVarExt, translateSTypeExt,
      translateSType, translatePExpr]
  | RFor x n body ih =>
    simp only [callFreePlusCall, callFree] at h
    rw [toJasminCmd_RFor]
    exact unrollForJ_translateCmdExt_isSome x _ (ih (callFreePlusCall_of_callFree _ h)) n
  | RLimbStore loc idx v =>
    rw [toJasminCmd_RLimbStore]
    refine translateCmdExt_cons_isSome _ _ ?_ rfl
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (translateLValExt_locToLVal_isSome loc)
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (translatePExprExt_locToPExpr_isSome loc)
    simp [translateInstrRExt, hl, he, translatePExprExt, translatePExpr]
  | RSelect dst sel src0 src1 =>
    rw [toJasminCmd_RSelect]
    refine translateCmdExt_cons_isSome _ _ ?_ rfl
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (translateLValExt_locToLVal_isSome dst)
    obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.mp (translatePExprExt_locToPExpr_isSome src0)
    obtain ⟨e1, he1⟩ := Option.isSome_iff_exists.mp (translatePExprExt_locToPExpr_isSome src1)
    simp [translateInstrRExt, hl, he0, he1, translatePExprExt, translateGVarExt,
      translateVarIExt, translateVarExt, translateSTypeExt, translateSType, translateWSize]
  | RAssert _ => rfl
  | RBlock body ih =>
    simp only [callFreePlusCall, callFree] at h
    rw [toJasminCmd_RBlock]
    exact ih (callFreePlusCall_of_callFree _ h)
  | RFnDef n p r body cont ih1 ih2 =>
    simp only [callFreePlusCall, callFree, Bool.and_eq_true] at h
    rw [toJasminCmd_RFnDef]
    exact translateCmdExt_append_isSome _ _ (ih1 (callFreePlusCall_of_callFree _ h.1))
      (ih2 (callFreePlusCall_of_callFree _ h.2))
  | RForRuntime => rfl
  | _ => simp [callFreePlusCall, callFree] at h

end CatCrypt.Crypto.SecureCompilation.VIR.LowCTMirrorTranslate
