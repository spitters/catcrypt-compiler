/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NormMulxOpt
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold

/-!
# The constant-index fold commutes with the width reading of `MULX`

`RegionPostFuseLift.normMulxBody` reads every two-output `MULX` of a body at its width `MULX:64`.
The fold stage `ConstIndexFold.foldIndexedBody` reads a mnemonic only at `LOADIDX`, `STOREIDX`,
`MOV:64`, `LOAD` and `STORE`, and reads an instruction otherwise through its gathered block
`lowerPrinted`, which is empty (`none`) for a `MULX` with two register destinations and one
source in either spelling. The frame parameters `bodyParams` read the mnemonics only through
the width class `bodyIsU64` and the `FRAME`/`FRAMEADD` directives; on a body of width class
`64` the width reading leaves them fixed. The fold therefore commutes with `normMulxBody` on a body
whose every `MULX` has that shape (`MulxShaped`), whose width class is `64`, and whose
dead-move elimination keeps the width class `64`.

## Main results

* `bodyParams_map_normI`: the width reading keeps the frame parameters of a `64`-bit body.
* `constIndexFoldBody_map_normI`: the fold commutes with the width reading.
* `dropDeadImmBody_map_normI`: the dead-move elimination commutes with the width reading.
* `foldIndexedBody_normMulxBody`: the fold stage commutes with `normMulxBody`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NormMulxFold

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (normMulx)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionPostFuseLift (normMulxBody)
open CatCrypt.Crypto.SecureCompilation.Haxc.NormMulxOpt (normI)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrGatherExtended (isLret)

/-! ## 1. The shape condition and the width reading of one instruction -/

/-- An instruction is `MULX`-shaped when it is no `MULX`, or a `MULX` with two register
    destinations and one source. -/
def mulxShapedI : LinstrR → Bool
  | .Lopn [.reg _, .reg _] "MULX" [_] => true
  | .Lopn _ o _ => o != "MULX"
  | _ => true

/-- Every `MULX` of the body has two register destinations and one source. -/
def MulxShaped (b : Lcmd) : Bool := b.all fun i => mulxShapedI i.li_i

/-- `withWidthTag 64 "MULX"` is the literal `MULX:64`. -/
theorem withWidthTag_mulx : withWidthTag 64 "MULX" = "MULX:64" := by
  decide +kernel

/-- The width reading fixes an instruction, or rewrites a `MULX` to `MULX:64`. -/
theorem normMulx_cases (r : LinstrR) :
    normMulx r = r ∨ ∃ ds ss, r = .Lopn ds "MULX" ss ∧ normMulx r = .Lopn ds "MULX:64" ss := by
  cases r with
  | Lopn ds o ss =>
    by_cases ho : o = "MULX"
    · subst ho
      exact Or.inr ⟨ds, ss, rfl, by simp [normMulx, withWidthTag_mulx]⟩
    · exact Or.inl (by simp [normMulx, ho])
  | _ => exact Or.inl rfl

/-- The width reading of one positioned instruction. -/
theorem normI_cases (j : Linstr) :
    normI j = j ∨ ∃ ii ds ss, j = ⟨ii, .Lopn ds "MULX" ss⟩
      ∧ normI j = ⟨ii, .Lopn ds "MULX:64" ss⟩ := by
  rcases j with ⟨ii, r⟩
  rcases normMulx_cases r with h | ⟨ds, ss, rfl, h⟩
  · exact Or.inl (by simp [normI, h])
  · exact Or.inr ⟨ii, ds, ss, rfl, by simp [normI, h]⟩

/-- A shaped `MULX` has two register destinations and one source. -/
theorem mulxShapedI_mulx {ds ss : List LOperand} (h : mulxShapedI (.Lopn ds "MULX" ss) = true) :
    ∃ d₁ d₂ s, ds = [.reg d₁, .reg d₂] ∧ ss = [s] := by
  unfold mulxShapedI at h
  split at h <;> grind

/-! ## 2. Folds over a body read through the width reading -/

/-- A left fold whose step does not see the width reading takes the same value on the width
    reading of a body. -/
theorem foldl_map_normI {α : Type} (g : α → Linstr → α) (hg : ∀ a j, g a (normI j) = g a j)
    (a : α) (b : Lcmd) : (b.map normI).foldl g a = b.foldl g a := by
  induction b generalizing a with
  | nil => rfl
  | cons j rest ih => simp only [List.map_cons, List.foldl_cons, hg, ih]

/-- A test that does not see the width reading holds of some instruction of the width reading
    of a body exactly when it holds of some instruction of the body. -/
theorem any_map_normI (g : Linstr → Bool) (hg : ∀ j, g (normI j) = g j) (b : Lcmd) :
    (b.map normI).any g = b.any g := by
  simp [List.any_map, Function.comp_def, hg]

/-- The `FRAME` directive of the width reading. -/
theorem frameDirective_map_normI (b : Lcmd) :
    frameDirective (b.map normI) = frameDirective b := by
  unfold frameDirective
  refine foldl_map_normI _ (fun a j => ?_) _ _
  rcases normI_cases j with h | ⟨ii, ds, ss, rfl, h⟩
  · rw [h]
  · rw [h]
    cases a <;> simp

/-- The `FRAMEADD` directives of the width reading. -/
theorem frameAddDirective_map_normI (b : Lcmd) :
    frameAddDirective (b.map normI) = frameAddDirective b := by
  unfold frameAddDirective
  refine foldl_map_normI _ (fun a j => ?_) _ _
  rcases normI_cases j with h | ⟨ii, ds, ss, rfl, h⟩
  · rw [h]
  · rw [h]
    simp

/-- The frame-array bytes of the width reading. -/
theorem faBytes_map_normI (b : Lcmd) : faBytes (b.map normI) = faBytes b := by
  unfold faBytes
  refine foldl_map_normI _ (fun a j => ?_) _ _
  rcases normI_cases j with h | ⟨ii, ds, ss, rfl, h⟩ <;> rw [h]

/-- The largest spill index of the width reading. -/
theorem maxSpillIdx_map_normI (b : Lcmd) : maxSpillIdx (b.map normI) = maxSpillIdx b := by
  unfold maxSpillIdx
  refine foldl_map_normI _ (fun a j => ?_) _ _
  rcases normI_cases j with h | ⟨ii, ds, ss, rfl, h⟩ <;> rw [h]

/-- The vector-spill bytes of the width reading. -/
theorem vecSpillBytes_map_normI (b : Lcmd) : vecSpillBytes (b.map normI) = vecSpillBytes b := by
  have : maxVecSpillIdx (b.map normI) = maxVecSpillIdx b := by
    unfold maxVecSpillIdx
    refine foldl_map_normI _ (fun a j => ?_) _ _
    rcases normI_cases j with h | ⟨ii, ds, ss, rfl, h⟩ <;> rw [h]
  simp only [vecSpillBytes, this]

/-- The call test of the width reading. -/
theorem bodyHasCall_map_normI (b : Lcmd) : bodyHasCall (b.map normI) = bodyHasCall b := by
  unfold bodyHasCall
  refine any_map_normI _ (fun j => ?_) _
  rcases normI_cases j with h | ⟨ii, ds, ss, rfl, h⟩ <;> rw [h]

/-- The qsave block size of the width reading. -/
theorem qsaveBytesFor_map_normI (b : Lcmd) : qsaveBytesFor (b.map normI) = qsaveBytesFor b := by
  simp only [qsaveBytesFor, bodyHasCall_map_normI]

/-- The callee-saved registers to save of the width reading. -/
theorem calleeSavedToSave_map_normI (b : Lcmd) :
    calleeSavedToSave (b.map normI) = calleeSavedToSave b := by
  have h1 : ∀ r, bodyWritesBareReg (b.map normI) r = bodyWritesBareReg b r := by
    intro r
    unfold bodyWritesBareReg
    refine any_map_normI _ (fun j => ?_) _
    rcases normI_cases j with h | ⟨ii, ds, ss, rfl, h⟩ <;> rw [h]
  have h2 : ∀ r, bodyParksQsave (b.map normI) r = bodyParksQsave b r := by
    intro r
    unfold bodyParksQsave
    refine any_map_normI _ (fun j => ?_) _
    rcases normI_cases j with h | ⟨ii, ds, ss, rfl, h⟩ <;> rw [h]
  simp only [calleeSavedToSave, h1, h2]

/-- The width reading keeps the width class `64`. -/
theorem bodyIsU64_map_normI {b : Lcmd} (hb : bodyIsU64 b = true) :
    bodyIsU64 (b.map normI) = true := by
  unfold bodyIsU64 at hb ⊢
  obtain ⟨j, hj, ht⟩ := List.any_eq_true.mp hb
  refine List.any_eq_true.mpr ⟨normI j, List.mem_map_of_mem hj, ?_⟩
  rcases normI_cases j with h | ⟨ii, ds, ss, rfl, h⟩
  · rw [h]; exact ht
  · rw [h]
    change hasSuffix "MULX:64" ":64" = true
    decide +kernel

/-- The frame size of the width reading of a body of width class `64`. -/
theorem frameSize_map_normI {b : Lcmd} (hb : bodyIsU64 b = true) :
    frameSize (b.map normI) = frameSize b := by
  simp only [frameSize, frameDirective_map_normI, frameAddDirective_map_normI, faBytes_map_normI,
    qsaveBytesFor_map_normI, bodyIsU64_map_normI hb, hb, maxSpillIdx_map_normI,
    vecSpillBytes_map_normI, bodyHasCall_map_normI, calleeSavedToSave_map_normI]

/-- **The width reading keeps the frame parameters of a body of width class `64`.** -/
theorem bodyParams_map_normI {b : Lcmd} (hb : bodyIsU64 b = true) :
    bodyParams (b.map normI) = bodyParams b := by
  simp only [bodyParams, frameSize_map_normI hb, bodyIsU64_map_normI hb, hb,
    qsaveBytesFor_map_normI]

/-- Equal frame parameters give equal width classes. -/
theorem bodyIsU64_of_bodyParams {x y : Lcmd} (h : bodyParams x = bodyParams y) :
    bodyIsU64 x = bodyIsU64 y := by
  simp only [bodyParams, Prod.mk.injEq] at h
  cases hx : bodyIsU64 x <;> cases hy : bodyIsU64 y <;> simp_all

/-! ## 3. The gather and the analysis on the width reading -/

/-- A two-output `MULX` does not gather. -/
theorem lowerPrinted_mulx (f w q : Nat) (d₁ d₂ : String) (s : LOperand) :
    lowerPrinted f w q (.Lopn [.reg d₁, .reg d₂] "MULX" [s]) = none := by
  cases s <;> rfl

/-- A two-output `MULX:64` does not gather. -/
theorem lowerPrinted_mulx64 (f w q : Nat) (d₁ d₂ : String) (s : LOperand) :
    lowerPrinted f w q (.Lopn [.reg d₁, .reg d₂] "MULX:64" [s]) = none := by
  cases s <;> rfl

/-- The gather of a shaped instruction does not see the width reading. -/
theorem lowerPrinted_normMulx (f w q : Nat) {r : LinstrR} (hs : mulxShapedI r = true) :
    lowerPrinted f w q (normMulx r) = lowerPrinted f w q r := by
  rcases normMulx_cases r with h | ⟨ds, ss, rfl, h⟩
  · rw [h]
  · obtain ⟨d₁, d₂, s, rfl, rfl⟩ := mulxShapedI_mulx hs
    rw [h, lowerPrinted_mulx, lowerPrinted_mulx64]

/-- The rewrite target of a `MULX` in either spelling is `none`. -/
theorem foldTarget?_mulx (env : KEnv) (ds ss : List LOperand) (o : String)
    (ho : o = "MULX" ∨ o = "MULX:64") : foldTarget? env (.Lopn ds o ss) = none := by
  unfold foldTarget?
  split <;> grind

/-- A rewrite target is fixed by the width reading. -/
theorem normMulx_of_foldTarget? {env : KEnv} {r j : LinstrR} (h : foldTarget? env r = some j) :
    normMulx j = j := by
  unfold foldTarget? at h
  split at h <;> grind [normMulx]

/-- The instruction is an `Lopn` whose mnemonic carries the width tag `:64`; the test
    `bodyIsU64` reads. -/
def u64T : LinstrR → Bool
  | .Lopn _ o _ => hasSuffix o ":64"
  | _ => false

/-- `bodyIsU64` is the test `u64T` at some instruction. -/
theorem bodyIsU64_eq_any (b : Lcmd) : bodyIsU64 b = b.any fun i => u64T i.li_i := by
  unfold bodyIsU64 u64T
  rfl

/-- A rewrite target keeps the width tag `:64` of its mnemonic. -/
theorem u64T_foldTarget? {env : KEnv} {r j : LinstrR} (h : foldTarget? env r = some j) :
    u64T j = u64T r := by
  unfold foldTarget? at h
  split at h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp only [u64T] <;>
    decide +kernel

/-- The rewrite of one instruction commutes with the width reading. -/
theorem foldInstr_normMulx (ex : List String) (env : KEnv) (r : LinstrR) :
    foldInstr ex env (normMulx r) = normMulx (foldInstr ex env r) := by
  rcases normMulx_cases r with h | ⟨ds, ss, rfl, h⟩
  · rw [h]
    unfold foldInstr
    split
    · exact h.symm
    · cases ht : foldTarget? env r with
      | none => exact h.symm
      | some j => exact (normMulx_of_foldTarget? ht).symm
  · rw [h]
    simp [foldInstr, foldTarget?_mulx env ds ss "MULX" (Or.inl rfl),
      foldTarget?_mulx env ds ss "MULX:64" (Or.inr rfl), h]

/-- A rewritten instruction keeps the `MULX` shape. -/
theorem mulxShapedI_foldInstr (ex : List String) (env : KEnv) {r : LinstrR}
    (hs : mulxShapedI r = true) : mulxShapedI (foldInstr ex env r) = true := by
  unfold foldInstr
  split
  · exact hs
  · cases ht : foldTarget? env r with
    | none => exact hs
    | some j =>
      unfold foldTarget? at ht
      split at ht <;> grind [mulxShapedI]

/-- The return test does not see the width reading. -/
theorem isLret_normI (j : Linstr) : isLret (normI j) = isLret j := by
  rcases normI_cases j with h | ⟨ii, ds, ss, rfl, h⟩ <;> simp only [h, isLret]

/-- The analysis step across a shaped instruction does not see the width reading. -/
theorem nextEnv_normI (p : Nat × Nat × Nat) (env : KEnv) {j : Linstr}
    (hs : mulxShapedI j.li_i = true) : nextEnv p env (normI j) = nextEnv p env j := by
  unfold nextEnv
  rw [isLret_normI]
  change (if isLret j = true then [] else
      match lowerPrinted p.1 p.2.1 p.2.2 (normMulx j.li_i) with
      | some js => (stepKs env js).killAll (narrowImmDsts (normMulx j.li_i))
      | none => match normMulx j.li_i with
        | .Lopn d _ _ => env.killAll (d.flatMap dstOpNames)
        | _ => []) = _
  rw [lowerPrinted_normMulx _ _ _ hs]
  rcases normMulx_cases j.li_i with h | ⟨ds, ss, h0, h⟩
  · rw [h]
    rfl
  · rw [h, h0]
    simp only [narrowImmDsts_of_not_narrow (o := "MULX:64") (by decide),
      narrowImmDsts_of_not_narrow (o := "MULX") (by decide)]
    rfl

/-! ## 4. The fold on the width reading -/

/-- The carry-in test of the fold does not see the width reading. -/
theorem carryNextB_map_normI (d : String) (rest : Lcmd) :
    carryNextB d (rest.map normI) = carryNextB d rest := by
  refine carryNextB_map d normI (fun j => ?_) rest
  have e : (normI j).li_i = normMulx j.li_i := rfl
  rw [e]
  rcases normMulx_cases j.li_i with h | ⟨ds, ss, h0, h⟩
  · rw [h]
  · rw [h, h0]
    exact carryStep_lopn_of_not_adcx d ds ss (by decide) (by decide)

/-- The carry-in reloads of the fold do not see the width reading. -/
theorem foldEnv_normI (env : KEnv) (j : Linstr) (rest : Lcmd) :
    foldEnv env (normI j).li_i (rest.map normI) = foldEnv env j.li_i rest := by
  have e : (normI j).li_i = normMulx j.li_i := rfl
  have hc : carryCopyB (normI j).li_i (rest.map normI) = carryCopyB j.li_i rest := by
    rw [e]
    rcases normMulx_cases j.li_i with h | ⟨ds, ss, h0, h⟩
    · rw [h]
      unfold carryCopyB
      split <;> simp [carryNextB_map_normI]
    · rw [h, h0]
      unfold carryCopyB
      split <;> split <;> grind
  simp only [foldEnv, hc]

/-- **The fold core commutes with the width reading** of a shaped body. -/
theorem foldCore_map_normI (p : Nat × Nat × Nat) (ex : List String) :
    ∀ (env : KEnv) (b : Lcmd), MulxShaped b = true →
      foldCore p ex env (b.map normI) = (foldCore p ex env b).map normI := by
  intro env b
  induction b generalizing env with
  | nil => intro _; rfl
  | cons j rest ih =>
    intro hs
    simp only [MulxShaped, List.all_cons, Bool.and_eq_true] at hs
    simp only [List.map_cons, foldCore, nextEnv_normI p env hs.1, ih _ hs.2]
    congr 1
    rw [foldEnv_normI]
    exact congrArg (Linstr.mk j.li_ii) (foldInstr_normMulx ex _ j.li_i)

/-- The fold core keeps the `MULX` shape. -/
theorem mulxShaped_foldCore (p : Nat × Nat × Nat) (ex : List String) :
    ∀ (env : KEnv) (b : Lcmd), MulxShaped b = true → MulxShaped (foldCore p ex env b) = true := by
  intro env b
  induction b generalizing env with
  | nil => intro _; rfl
  | cons j rest ih =>
    intro hs
    simp only [MulxShaped, List.all_cons, Bool.and_eq_true] at hs
    simp only [foldCore, MulxShaped, List.all_cons, Bool.and_eq_true]
    exact ⟨mulxShapedI_foldInstr ex _ hs.1, ih _ hs.2⟩

/-- The fold core keeps the width class. -/
theorem bodyIsU64_foldCore (p : Nat × Nat × Nat) (ex : List String) :
    ∀ (env : KEnv) (b : Lcmd), bodyIsU64 (foldCore p ex env b) = bodyIsU64 b := by
  intro env b
  induction b generalizing env with
  | nil => rfl
  | cons j rest ih =>
    have hj : u64T (foldInstr ex (foldEnv env j.li_i rest) j.li_i) = u64T j.li_i := by
      generalize foldEnv env j.li_i rest = E
      unfold foldInstr
      split
      · rfl
      · cases ht : foldTarget? E j.li_i with
        | none => rfl
        | some j' => exact u64T_foldTarget? ht
    have ih' := ih (nextEnv p env j)
    rw [bodyIsU64_eq_any, bodyIsU64_eq_any] at ih'
    rw [bodyIsU64_eq_any, bodyIsU64_eq_any]
    simp only [foldCore, List.any_cons, hj, ih']

/-- The arrays indexed at run time do not see the width reading of a shaped body. -/
theorem runtimeBases_map_normI (p : Nat × Nat × Nat) :
    ∀ (acc : List String) (env : KEnv) (b : Lcmd), MulxShaped b = true →
      runtimeBases p acc env (b.map normI) = runtimeBases p acc env b := by
  intro acc env b
  induction b generalizing acc env with
  | nil => intro _; rfl
  | cons j rest ih =>
    intro hs
    simp only [MulxShaped, List.all_cons, Bool.and_eq_true] at hs
    have h1 : (foldTarget? env (normI j).li_i).isSome = (foldTarget? env j.li_i).isSome := by
      change (foldTarget? env (normMulx j.li_i)).isSome = _
      rcases normMulx_cases j.li_i with h | ⟨ds, ss, h0, h⟩
      · rw [h]
      · rw [h, h0, foldTarget?_mulx env ds ss "MULX" (Or.inl rfl),
          foldTarget?_mulx env ds ss "MULX:64" (Or.inr rfl)]
    have h2 : idxBases (normI j).li_i = idxBases j.li_i := by
      change idxBases (normMulx j.li_i) = _
      rcases normMulx_cases j.li_i with h | ⟨ds, ss, h0, h⟩
      · rw [h]
      · rw [h, h0]
        rfl
    simp only [List.map_cons, runtimeBases, nextEnv_normI p env hs.1, h1, h2]
    exact ih _ _ hs.2

/-- The fold of a body keeps its frame parameters. -/
theorem bodyParams_constIndexFoldBody (b : Lcmd) :
    bodyParams (constIndexFoldBody b) = bodyParams b := by
  unfold constIndexFoldBody
  dsimp only
  split
  · assumption
  · rfl

/-- **The fold commutes with the width reading** of a shaped body of width class `64`. -/
theorem constIndexFoldBody_map_normI {b : Lcmd} (hs : MulxShaped b = true)
    (hb : bodyIsU64 b = true) :
    constIndexFoldBody (b.map normI) = (constIndexFoldBody b).map normI := by
  have hb' := bodyIsU64_foldCore (bodyParams b) (runtimeBases (bodyParams b) [] [] b) [] b
  unfold constIndexFoldBody
  simp only [bodyParams_map_normI hb, runtimeBases_map_normI _ _ _ _ hs,
    foldCore_map_normI _ _ _ _ hs, bodyParams_map_normI (hb'.trans hb)]
  by_cases hc : bodyParams (foldCore (bodyParams b) (runtimeBases (bodyParams b) [] [] b) [] b)
      = bodyParams b <;> simp [hc]

/-- The fold keeps the `MULX` shape. -/
theorem mulxShaped_constIndexFoldBody {b : Lcmd} (hs : MulxShaped b = true) :
    MulxShaped (constIndexFoldBody b) = true := by
  unfold constIndexFoldBody
  dsimp only
  split
  · exact mulxShaped_foldCore _ _ _ _ hs
  · exact hs

/-! ## 5. The dead-move elimination and the spelling on the width reading -/

/-- The dead-register scan does not see the width reading of a shaped body. -/
theorem deadAfter_map_normI (p : Nat × Nat × Nat) (r : String) :
    ∀ b : Lcmd, MulxShaped b = true → deadAfter p r (b.map normI) = deadAfter p r b := by
  intro b
  induction b with
  | nil => intro _; rfl
  | cons j rest ih =>
    intro hs
    simp only [MulxShaped, List.all_cons, Bool.and_eq_true] at hs
    simp only [List.map_cons, deadAfter, isLret_normI]
    rw [show (normI j).li_i = normMulx j.li_i from rfl, lowerPrinted_normMulx _ _ _ hs.1,
      ih hs.2]

/-- The dead immediate move of a shaped instruction does not see the width reading. -/
theorem deadImmReg?_normI (p : Nat × Nat × Nat) {j : Linstr} (hs : mulxShapedI j.li_i = true) :
    deadImmReg? p (normI j) = deadImmReg? p j := by
  unfold deadImmReg?
  change (match lowerPrinted p.1 p.2.1 p.2.2 (normMulx j.li_i) with
    | some [.mov r (.imm _)] =>
      if X86Backend.LprogBytes.isGpName r then some r else none
    | _ => none) = _
  rw [lowerPrinted_normMulx _ _ _ hs]
  rfl

/-- **The dead-move core commutes with the width reading** of a shaped body. -/
theorem dropDeadCore_map_normI (p : Nat × Nat × Nat) :
    ∀ b : Lcmd, MulxShaped b = true →
      dropDeadCore p (b.map normI) = (dropDeadCore p b).map normI := by
  intro b
  induction b with
  | nil => intro _; rfl
  | cons j rest ih =>
    intro hs
    have hs' := hs
    simp only [MulxShaped, List.all_cons, Bool.and_eq_true] at hs'
    simp only [List.map_cons, dropDeadCore, deadImmReg?_normI p hs'.1,
      deadAfter_map_normI p _ rest hs'.2, ih hs'.2]
    split
    · split <;> rfl
    · rfl

/-- **The dead-move elimination commutes with the width reading** of a shaped body of width
    class `64` whose dead-move core keeps the width class `64`. -/
theorem dropDeadImmBody_map_normI {b : Lcmd} (hs : MulxShaped b = true)
    (hb : bodyIsU64 b = true) (hd : bodyIsU64 (dropDeadCore (bodyParams b) b) = true) :
    dropDeadImmBody (b.map normI) = (dropDeadImmBody b).map normI := by
  unfold dropDeadImmBody
  simp only [bodyParams_map_normI hb, dropDeadCore_map_normI _ _ hs, bodyParams_map_normI hd]
  by_cases hc : bodyParams (dropDeadCore (bodyParams b) b) = bodyParams b <;> simp [hc]

/-- The spelling of one instruction commutes with the width reading. -/
theorem spellMemInstr_normMulx (r : LinstrR) :
    spellMemInstr (normMulx r) = normMulx (spellMemInstr r) := by
  rcases normMulx_cases r with h | ⟨ds, ss, rfl, h⟩
  · rw [h]
    unfold spellMemInstr
    split <;> grind [normMulx]
  · rw [h]
    unfold spellMemInstr
    split <;> grind [normMulx]

/-- The spelling commutes with the width reading. -/
theorem spellMemBody_map_normI (b : Lcmd) :
    spellMemBody (b.map normI) = (spellMemBody b).map normI := by
  simp only [spellMemBody, List.map_map]
  refine List.map_congr_left fun j _ => ?_
  simp [normI, spellMemInstr_normMulx]

/-! ## 6. The fold stage -/

/-- **The fold stage commutes with `normMulxBody`**, the reading of every `MULX` at its width
    `MULX:64`, on a body whose every `MULX` has two register destinations and one source, whose
    width class is `64`, and whose dead-move core after the fold keeps the width class `64`. -/
theorem foldIndexedBody_normMulxBody (b : Lcmd) (hs : MulxShaped b = true)
    (hb : bodyIsU64 b = true)
    (hd : bodyIsU64 (dropDeadCore (bodyParams b) (constIndexFoldBody b)) = true) :
    foldIndexedBody (normMulxBody b) = normMulxBody (foldIndexedBody b) := by
  have hp := bodyParams_constIndexFoldBody b
  have hb1 : bodyIsU64 (constIndexFoldBody b) = true := (bodyIsU64_of_bodyParams hp).trans hb
  change spellMemBody (dropDeadImmBody (constIndexFoldBody (b.map normI)))
    = (spellMemBody (dropDeadImmBody (constIndexFoldBody b))).map normI
  rw [constIndexFoldBody_map_normI hs hb,
    dropDeadImmBody_map_normI (mulxShaped_constIndexFoldBody hs) hb1 (by rw [hp]; exact hd),
    spellMemBody_map_normI]

end CatCrypt.Crypto.SecureCompilation.Haxc.NormMulxFold
