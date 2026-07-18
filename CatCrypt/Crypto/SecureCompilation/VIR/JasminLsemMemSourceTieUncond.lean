/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTie

set_option autoImplicit false

/-!
# Unconditional per-trip simulation + the array-carrier decode (B4 residuals i, iv)

`JasminLsemMemSourceTie` (B4) ties the memref export theorems to the source
denotation `JLoopBodyN.denote` / `ComL.denote`, but leaves the per-trip
simulation `hsim` as a hypothesis, discharged generically only at *encoded*
trip states. This module closes that residual and adds the array-carrier
decode:

1. **R1 — the unconditional per-trip discharge** (§2–§4): for the emitted
   `chain ++ writeback` body shape (`loopBodyFullMN` — the linearizer chain of
   the `ScalarMemN` update, the accumulator writeback into its argument
   register, the loop-index increment, the counter decrement), the per-trip
   simulation is **proved**, not hypothesised. The bricks are the strengthened
   straight-line simulation `lsemStraightMem_straightOps_full`
   (`JasminLsemMem` §15 — final store agreement + write frame) and the
   agreement-transport lemmas for the three writeback writes. The composed
   export theorems `loopMem_export_faithful_denote_uncond` / `_comL_uncond`
   carry only the schedule (`hprev`/`hlast`/`hbfin`/`htaken`/`hhalt`), the seed
   (`hseed`/`hn0`) and the counter-name hygiene (`hna`/`hnr`) hypotheses — no
   `hsim`.
2. **R4 — the array-carrier decode** (§5–§7): `decodeArrM` reads a named
   `larr` region off the halt state; `runBoundedLoopMemArr_decodes_denote` is
   the fold induction at an **array accumulator** (`accTy = .stackArr w n` —
   `JLoopBodyN` is already generic in `accTy`); `loopMemArr_export_faithful*`
   are the A1 export theorems concluded at the array cells (using the array
   half of `loopMem_runBounded`, previously discarded); and the **fill shape**
   `out[i] := a[i]` (`fillBodyM`, the in-place `LOADIDX`/`STOREIDX` pass the
   physical allocator produces) gets its per-trip simulation discharged
   unconditionally too — `fillLoop_export_faithful_denote` is `hsim`-free.
3. **Validation** (§8): the composed unconditional theorems are instantiated on
   concrete runs — the §7 doubling loop of the B4 file re-derived *through*
   `loopMem_export_faithful_denote_uncond` (no `hsim` side condition), and a
   4-cell fill loop at runtime count 3 through `fillLoop_export_faithful_denote`,
   its array cells decoding to the source fold.

**0 sorries; axioms = {propext, Classical.choice, Quot.sound} + the
pre-existing `aesSboxArrayW_size` `native_decide` inherited from the
`jasminDialect` denotation (+ `Lean.ofReduceBool` for the §8 concrete
witnesses).** The `lsem→bytes` encoder + Sail tables remain the declared
trusted base.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoopNestWhile
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChainBridge
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTie

/-! ## 1. Bricks: fold append, carrier congruence, raw writeback steps

Small execution/agreement facts about the *imported* machinery (nothing here
re-proves an interpreter result). -/

/-- Peel one succeeding step off the straight-line fold. -/
theorem lsemStraightMem_cons_some {i : LinstrRM} {is : List LinstrRM} {s s' : LstateM}
    (h : lsemStepMem i s = some s') :
    lsemStraightMem (i :: is) s = lsemStraightMem is s' := by
  rw [lsemStraightMem_cons, h]

/-- Register read through a `setReg`-then-bump at a different name. -/
theorem LstateM.getW_setReg_nextPc_other (s : LstateM) (r r' : String) {w : Nat}
    (v : BitVec w) (w' : Nat) (h : r' ≠ r) :
    ((s.setReg r v).nextPc).reg.getW r' w' = s.reg.getW r' w' := by
  rw [LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc]
  exact LstateN.getW_setReg_other _ _ _ _ _ h

/-- The straight-line fold splits over `++`. -/
theorem lsemStraightMem_append (xs ys : List LinstrRM) (s : LstateM) :
    lsemStraightMem (xs ++ ys) s = (lsemStraightMem xs s).bind (lsemStraightMem ys) := by
  induction xs generalizing s with
  | nil => simp
  | cons i is ih =>
      simp only [List.cons_append, lsemStraightMem_cons]
      cases lsemStepMem i s with
      | none => rfl
      | some s' => exact ih s'

/-- `getW` reads only `lvm`. -/
theorem LstateN.getW_congr_lvm {s1 s2 : LstateN} (h : s1.lvm = s2.lvm)
    (r : String) (w : Nat) : s1.getW r w = s2.getW r w := by
  unfold LstateN.getW
  rw [h]

/-- `getArr` reads only `larr`. -/
theorem LstateM.getArr_congr_larr {s1 s2 : LstateM} (h : s1.larr = s2.larr)
    (r : String) (w n : Nat) : s1.getArr r w n = s2.getArr r w n := by
  unfold LstateM.getArr
  rw [h]

/-- The array carrier ignores the pc. -/
theorem LstateM.larr_setLpc (s : LstateM) (pc : Nat) : (s.setLpc pc).larr = s.larr := rfl

/-- The agreement reads only the two carriers (`reg.lvm`, `larr`) — never the
    pc: it transports along carrier equality. -/
theorem StoreAgreesM.congr_carriers {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s s' : LstateM} {V : Ctxt.Valuation Γ}
    (hlvm : s'.reg.lvm = s.reg.lvm) (hlarr : s'.larr = s.larr)
    (h : StoreAgreesM nArgs curDepth s V) : StoreAgreesM nArgs curDepth s' V := by
  refine ⟨?_, ?_⟩
  · intro w' v
    rw [evalOperandN_resolveVar, LstateN.getW_congr_lvm hlvm, ← evalOperandN_resolveVar]
    exact h.reg v
  · intro w' n' v
    rw [LstateM.getArr_congr_larr hlarr]
    exact h.arr v

/-- Agreement survives a pc reset (the back-edge's `setLpc`). -/
theorem StoreAgreesM.setLpc {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : LstateM} {V : Ctxt.Valuation Γ} (h : StoreAgreesM nArgs curDepth s V)
    (pc : Nat) : StoreAgreesM nArgs curDepth (s.setLpc pc) V :=
  StoreAgreesM.congr_carriers (LstateM.reg_lvm_setLpc s pc) (LstateM.larr_setLpc s pc) h

/-- Agreement survives a pc bump. -/
theorem StoreAgreesM.nextPc {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : LstateM} {V : Ctxt.Valuation Γ} (h : StoreAgreesM nArgs curDepth s V) :
    StoreAgreesM nArgs curDepth s.nextPc V :=
  StoreAgreesM.congr_carriers rfl rfl h

/-- Width tags strip: `"ADD:64" → "ADD"`. -/
theorem stripWidthTag_ADD64 : stripWidthTag "ADD:64" = "ADD" := by decide +kernel

/-- Width tags strip: `"SUB:64" → "SUB"`. -/
theorem stripWidthTag_SUB64 : stripWidthTag "SUB:64" = "SUB" := by decide +kernel

/-- **Raw writeback step — `ADD dst ← a, #k`.** The typed step on the emitted
    `"ADD:64"` reg/imm wire, from a register read fact alone (no `Com` context):
    the data width is recovered from `a`'s store tag, the immediate is evaluated
    at it. -/
theorem lsemStepMem_add64Imm (dst a : String) (k : Nat) {w : Nat} (va : BitVec w)
    (st : LstateM) (ha : st.reg.getW a w = some va) :
    lsemStepMem (LinstrR.Lopn [.reg dst] "ADD:64" [.reg a, .imm k], MemTag.reg none) st
      = some ((st.setReg dst (va + BitVec.ofNat w k)).nextPc) := by
  have hstep : lsemStepCast (LinstrR.Lopn [.reg dst] "ADD:64" [.reg a, .imm k], none) st.reg
      = some ((st.reg.setReg dst (va + BitVec.ofNat w k)).nextPc) := by
    rw [lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ rfl rfl rfl,
      lsemStepSh_of_not_sar _ _ (by simp [sarStruct?, stripWidthTag_ADD64])]
    simp only [lsemStepN, readReg_of_getW ha, evalOperandN, stripWidthTag_ADD64, applyOpnN]
  rw [lsemStepMem_reg, hstep, Option.map_some]
  rfl

/-- **Raw writeback step — `SUB dst ← a, #k`.** -/
theorem lsemStepMem_sub64Imm (dst a : String) (k : Nat) {w : Nat} (va : BitVec w)
    (st : LstateM) (ha : st.reg.getW a w = some va) :
    lsemStepMem (LinstrR.Lopn [.reg dst] "SUB:64" [.reg a, .imm k], MemTag.reg none) st
      = some ((st.setReg dst (va - BitVec.ofNat w k)).nextPc) := by
  have hstep : lsemStepCast (LinstrR.Lopn [.reg dst] "SUB:64" [.reg a, .imm k], none) st.reg
      = some ((st.reg.setReg dst (va - BitVec.ofNat w k)).nextPc) := by
    rw [lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ rfl rfl rfl,
      lsemStepSh_of_not_sar _ _ (by simp [sarStruct?, stripWidthTag_SUB64])]
    simp only [lsemStepN, readReg_of_getW ha, evalOperandN, stripWidthTag_SUB64, applyOpnN]
  rw [lsemStepMem_reg, hstep, Option.map_some]
  rfl

/-- **Raw memory step — `LOADIDX dst ← base[idx]`** from read facts alone. -/
theorem lsemStepMem_loadIdx (dst base idx : String) (sc : Nat) {w n : Nat}
    (arr : Fin n → BitVec w) (vi : BitVec 64) (st : LstateM)
    (hb : st.getArr base w n = some arr) (hi : st.reg.getW idx 64 = some vi) :
    lsemStepMem (LinstrR.Lopn [.reg dst] "LOADIDX" [.arrIdx base idx sc],
        MemTag.load w n) st
      = some ((st.setReg dst (stackGet arr vi.toNat)).nextPc) := by
  simp only [lsemStepMem, loadStruct?, if_true, hb, hi]

/-- **Raw memory step — `STOREIDX dst ← base[idx] := val`** from read facts
    alone (the destination slot is a free name — in particular it may be `base`
    itself, the in-place pass the physical allocator produces). -/
theorem lsemStepMem_storeIdx (dst base idx val : String) (sc : Nat) {w n : Nat}
    (arr : Fin n → BitVec w) (vi : BitVec 64) (vv : BitVec w) (st : LstateM)
    (hb : st.getArr base w n = some arr) (hi : st.reg.getW idx 64 = some vi)
    (hv : st.reg.getW val w = some vv) :
    lsemStepMem (LinstrR.Lopn [.reg dst] "STOREIDX" [.arrIdx base idx sc, .reg val],
        MemTag.store w n) st
      = some ((st.setArr dst (stackSet arr vi.toNat vv)).nextPc) := by
  simp only [lsemStepMem, storeStruct?, if_true, hb, hi, hv]

/-! ## 2. The trip-context name geometry

The loop-body context is `accTy :: .reg 64 :: invTys` (`nA = |invTys| + 2`
binders, all arguments). The accumulator resolves to `argName (|invTys| + 1)`,
the loop index to `argName |invTys|`, each invariant to an `argName < |invTys|`.
Generic in `accTy` (scalar for R1, `stackArr` for R4). -/

variable {invTys : Ctxt jasminDialect}

/-- The accumulator's argument register. -/
def accRegMN (invTys : Ctxt jasminDialect) : String := argName (invTys.length + 1)

/-- The loop index's argument register. -/
def idxRegMN (invTys : Ctxt jasminDialect) : String := argName invTys.length

/-- The accumulator (`.here`) resolves to `accRegMN`. -/
theorem resolveVar_trip_acc {accTy : JasminTy} :
    resolveVar (invTys.length + 2) (invTys.length + 2) argName (fun _ => none)
      (.here : Ctxt.Var (accTy :: JasminTy.reg 64 :: invTys) accTy)
      = .reg (accRegMN invTys) := by
  simp only [resolveVar, varIndex]
  rw [show invTys.length + 2 - 1 - 0 = invTys.length + 1 from by omega,
    if_pos (by omega)]
  rfl

/-- The loop index (`.there .here`) resolves to `idxRegMN`. -/
theorem resolveVar_trip_idx {accTy : JasminTy} :
    resolveVar (invTys.length + 2) (invTys.length + 2) argName (fun _ => none)
      (.there .here : Ctxt.Var (accTy :: JasminTy.reg 64 :: invTys) (JasminTy.reg 64))
      = .reg (idxRegMN invTys) := by
  simp only [resolveVar, varIndex]
  rw [show invTys.length + 2 - 1 - (0 + 1) = invTys.length from by omega,
    if_pos (by omega)]
  rfl

/-- An invariant (`.there (.there v)`) resolves to an `argName` slot strictly
    below the index slot. -/
theorem resolveVar_trip_inv {accTy τ : JasminTy} (v : Ctxt.Var invTys τ) :
    ∃ j, j < invTys.length ∧
      resolveVar (invTys.length + 2) (invTys.length + 2) argName (fun _ => none)
        (.there (.there v) : Ctxt.Var (accTy :: JasminTy.reg 64 :: invTys) τ)
        = .reg (argName j) := by
  have hlt : varIndex v < invTys.length := JasminLsemSimulation.varIndex_lt v
  refine ⟨invTys.length - 1 - varIndex v, by omega, ?_⟩
  simp only [resolveVar, varIndex]
  rw [show invTys.length + 2 - 1 - (varIndex v + 1 + 1) = invTys.length - 1 - varIndex v
      from by omega,
    if_pos (by omega)]

/-! ### Readers off a trip agreement -/

/-- Read the scalar accumulator off a trip agreement. -/
theorem tripAgree_getW_acc {w : Nat} {s : LstateM} {invs : Ctxt.Valuation invTys}
    {vi : BitVec 64} {acc : BitVec w}
    (h : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s
      (.cons acc (.cons vi invs) :
        Ctxt.Valuation (JasminTy.reg w :: JasminTy.reg 64 :: invTys))) :
    s.reg.getW (accRegMN invTys) w = some acc := by
  have := h.reg (.here : Ctxt.Var (JasminTy.reg w :: JasminTy.reg 64 :: invTys) (.reg w))
  rwa [resolveVar_trip_acc, evalOperandN] at this

/-- Read the array accumulator off a trip agreement. -/
theorem tripAgree_getArr_acc {w n : Nat} {s : LstateM} {invs : Ctxt.Valuation invTys}
    {vi : BitVec 64} {arr : Fin n → BitVec w}
    (h : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s
      (.cons arr (.cons vi invs) :
        Ctxt.Valuation (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys))) :
    s.getArr (accRegMN invTys) w n = some arr := by
  have := h.arr (.here :
    Ctxt.Var (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (.stackArr w n))
  rwa [resolveVar_trip_acc] at this

/-- Read the loop index off a trip agreement (any `accTy`). -/
theorem tripAgree_getW_idx {accTy : JasminTy} {s : LstateM}
    {invs : Ctxt.Valuation invTys} {a : ⟦accTy⟧} {vi : BitVec 64}
    (h : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s
      (.cons a (.cons vi invs) :
        Ctxt.Valuation (accTy :: JasminTy.reg 64 :: invTys))) :
    s.reg.getW (idxRegMN invTys) 64 = some vi := by
  have := h.reg (.there .here :
    Ctxt.Var (accTy :: JasminTy.reg 64 :: invTys) (.reg 64))
  rwa [resolveVar_trip_idx, evalOperandN] at this

/-! ### Agreement transports across the writeback writes -/

/-- Writing an **untracked** register (a name that is no `argName` and no
    `regName` — e.g. the loop counter) preserves any agreement. -/
theorem StoreAgreesM.setReg_untracked {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : LstateM} {V : Ctxt.Valuation Γ} (r : String) {w : Nat} (v : BitVec w)
    (hra : ∀ j, r ≠ argName j) (hrr : ∀ k, r ≠ regName k)
    (h : StoreAgreesM nArgs curDepth s V) :
    StoreAgreesM nArgs curDepth (s.setReg r v) V := by
  refine ⟨?_, ?_⟩
  · intro w' u
    rw [evalOperandN_resolveVar] at *
    rw [LstateM.reg_setReg]
    have hname : operandName (resolveVar curDepth nArgs argName (fun _ => none) u) ≠ r := by
      simp only [resolveVar, operandName]
      by_cases hsa : curDepth - 1 - varIndex u < nArgs
      · simp only [hsa, if_true]
        exact fun he => hra _ he.symm
      · simp only [hsa, if_false]
        exact fun he => hrr _ he.symm
    rw [LstateN.getW_setReg_other _ _ _ _ _ hname]
    have := h.reg u
    rwa [evalOperandN_resolveVar] at this
  · intro w' n' u
    rw [LstateM.getArr_setReg]
    exact h.arr u

/-- Writing a fresh-block register `regName k`, `k ≥ curDepth` (e.g. a scratch
    slot), preserves any agreement at depth `curDepth = Γ.length`. -/
theorem StoreAgreesM.setReg_scratch {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : LstateM} {V : Ctxt.Valuation Γ} (hlen : Γ.length = curDepth)
    (k : Nat) (hk : curDepth ≤ k) {w : Nat} (v : BitVec w)
    (h : StoreAgreesM nArgs curDepth s V) :
    StoreAgreesM nArgs curDepth (s.setReg (regName k) v) V := by
  refine ⟨?_, ?_⟩
  · intro w' u
    have hv : varIndex u < curDepth := hlen ▸ JasminLsemSimulation.varIndex_lt u
    rw [evalOperandN_resolveVar, LstateM.reg_setReg,
      LstateN.getW_setReg_other _ _ _ _ _
        (resolveVar_operandName_ne_regName u hv k hk),
      ← evalOperandN_resolveVar]
    exact h.reg u
  · intro w' n' u
    rw [LstateM.getArr_setReg]
    exact h.arr u

/-- **Transport — accumulator register write.** Writing `accRegMN` re-points the
    accumulator: agreement at `[acc, vi, *invs]` becomes agreement at
    `[newAcc, vi, *invs]`. -/
theorem tripAgree_setReg_acc {w : Nat} {s : LstateM} {invs : Ctxt.Valuation invTys}
    {vi : BitVec 64} {acc : BitVec w}
    (h : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s
      (.cons acc (.cons vi invs) :
        Ctxt.Valuation (JasminTy.reg w :: JasminTy.reg 64 :: invTys)))
    (newAcc : BitVec w) :
    StoreAgreesM (invTys.length + 2) (invTys.length + 2)
      (s.setReg (accRegMN invTys) newAcc)
      (.cons newAcc (.cons vi invs) :
        Ctxt.Valuation (JasminTy.reg w :: JasminTy.reg 64 :: invTys)) := by
  refine ⟨?_, ?_⟩
  · intro w' v
    cases v with
    | here =>
        rw [resolveVar_trip_acc, evalOperandN, LstateM.reg_setReg,
          LstateN.getW_setReg_same]
        rfl
    | there v' =>
        cases v' with
        | here =>
            rw [resolveVar_trip_idx, evalOperandN, LstateM.reg_setReg,
              LstateN.getW_setReg_other _ _ _ _ _
                (show idxRegMN invTys ≠ accRegMN invTys from
                  JasminLsemSimulation.argName_ne (by omega))]
            have := h.reg (.there .here :
              Ctxt.Var (JasminTy.reg w :: JasminTy.reg 64 :: invTys) (.reg 64))
            rwa [resolveVar_trip_idx, evalOperandN] at this
        | there v'' =>
            obtain ⟨j, hj, hrv⟩ := resolveVar_trip_inv (accTy := JasminTy.reg w) v''
            rw [hrv, evalOperandN, LstateM.reg_setReg,
              LstateN.getW_setReg_other _ _ _ _ _
                (show argName j ≠ accRegMN invTys from
                  JasminLsemSimulation.argName_ne (by omega))]
            have := h.reg (.there (.there v''))
            rwa [hrv, evalOperandN] at this
  · intro w' n' v
    cases v with
    | there v' =>
        cases v' with
        | there v'' =>
            rw [LstateM.getArr_setReg]
            exact h.arr (.there (.there v''))

/-- **Transport — loop-index register write** (any `accTy`). Writing `idxRegMN`
    re-points the loop index. -/
theorem tripAgree_setReg_idx {accTy : JasminTy} {s : LstateM}
    {invs : Ctxt.Valuation invTys} {a : ⟦accTy⟧} {vi : BitVec 64}
    (h : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s
      (.cons a (.cons vi invs) : Ctxt.Valuation (accTy :: JasminTy.reg 64 :: invTys)))
    (newIdx : BitVec 64) :
    StoreAgreesM (invTys.length + 2) (invTys.length + 2)
      (s.setReg (idxRegMN invTys) newIdx)
      (.cons a (.cons newIdx invs) :
        Ctxt.Valuation (accTy :: JasminTy.reg 64 :: invTys)) := by
  refine ⟨?_, ?_⟩
  · intro w' v
    cases v with
    | here =>
        rw [resolveVar_trip_acc, evalOperandN, LstateM.reg_setReg,
          LstateN.getW_setReg_other _ _ _ _ _
            (show accRegMN invTys ≠ idxRegMN invTys from
              JasminLsemSimulation.argName_ne (by omega))]
        have := h.reg (.here :
          Ctxt.Var (JasminTy.reg w' :: JasminTy.reg 64 :: invTys) (.reg w'))
        rwa [resolveVar_trip_acc, evalOperandN] at this
    | there v' =>
        cases v' with
        | here =>
            rw [resolveVar_trip_idx, evalOperandN, LstateM.reg_setReg,
              LstateN.getW_setReg_same]
            rfl
        | there v'' =>
            obtain ⟨j, hj, hrv⟩ := resolveVar_trip_inv (accTy := accTy) v''
            rw [hrv, evalOperandN, LstateM.reg_setReg,
              LstateN.getW_setReg_other _ _ _ _ _
                (show argName j ≠ idxRegMN invTys from
                  JasminLsemSimulation.argName_ne (by omega))]
            have := h.reg (.there (.there v''))
            rwa [hrv, evalOperandN] at this
  · intro w' n' v
    cases v with
    | here =>
        rw [resolveVar_trip_acc]
        show (s.setReg (idxRegMN invTys) newIdx).getArr (accRegMN invTys) w' n' = _
        rw [LstateM.getArr_setReg]
        have := h.arr (.here :
          Ctxt.Var (JasminTy.stackArr w' n' :: JasminTy.reg 64 :: invTys)
            (.stackArr w' n'))
        rwa [resolveVar_trip_acc] at this
    | there v' =>
        cases v' with
        | there v'' =>
            rw [LstateM.getArr_setReg]
            exact h.arr (.there (.there v''))

/-- **Transport — accumulator array write** (`accTy = .stackArr w n`). Writing
    the accumulator slot's array re-points the array accumulator. -/
theorem tripAgree_setArr_acc {w n : Nat} {s : LstateM} {invs : Ctxt.Valuation invTys}
    {vi : BitVec 64} {arr : Fin n → BitVec w}
    (h : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s
      (.cons arr (.cons vi invs) :
        Ctxt.Valuation (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys)))
    (newArr : Fin n → BitVec w) :
    StoreAgreesM (invTys.length + 2) (invTys.length + 2)
      (s.setArr (accRegMN invTys) newArr)
      (.cons newArr (.cons vi invs) :
        Ctxt.Valuation (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys)) := by
  refine ⟨?_, ?_⟩
  · intro w' v
    cases v with
    | there v' =>
        cases v' with
        | here =>
            rw [resolveVar_trip_idx, evalOperandN, LstateM.reg_setArr]
            have := h.reg (.there .here :
              Ctxt.Var (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (.reg 64))
            rwa [resolveVar_trip_idx, evalOperandN] at this
        | there v'' =>
            obtain ⟨j, hj, hrv⟩ :=
              resolveVar_trip_inv (accTy := JasminTy.stackArr w n) v''
            rw [hrv, evalOperandN, LstateM.reg_setArr]
            have := h.reg (.there (.there v''))
            rwa [hrv, evalOperandN] at this
  · intro w' n' v
    cases v with
    | here =>
        rw [resolveVar_trip_acc]
        show (s.setArr (accRegMN invTys) newArr).getArr (accRegMN invTys) w n = _
        rw [LstateM.getArr_setArr_same]
        rfl
    | there v' =>
        cases v' with
        | there v'' =>
            obtain ⟨j, hj, hrv⟩ :=
              resolveVar_trip_inv (accTy := JasminTy.stackArr w n) v''
            rw [hrv]
            show (s.setArr (accRegMN invTys) newArr).getArr (argName j) w' n' = _
            rw [LstateM.getArr_setArr_other _ _ _ _ _ _
              (show argName j ≠ accRegMN invTys from
                JasminLsemSimulation.argName_ne (by omega))]
            have := h.arr (.there (.there v''))
            rwa [hrv] at this

/-! ## 3. R1 — the emitted `chain ++ writeback` body and its proved per-trip pass -/

/-- The canonical writeback of a scalar-accumulator loop pass: move the chain's
    result register into the accumulator argument (`ADD acc ← ret, #0` — the
    machine model's register move), advance the loop index, decrement the
    counter. -/
def loopWritebackMN {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w)) (nReg : String) : List LinstrRM :=
  [ (LinstrR.Lopn [.reg (accRegMN invTys)] "ADD:64"
      [.reg (loopBodyRetRegMN update), .imm 0], MemTag.reg none)
  , (LinstrR.Lopn [.reg (idxRegMN invTys)] "ADD:64"
      [.reg (idxRegMN invTys), .imm 1], MemTag.reg none)
  , (LinstrR.Lopn [.reg nReg] "SUB:64" [.reg nReg, .imm 1], MemTag.reg none) ]

/-- **The emitted loop body**: the linearizer chain of the `ScalarMemN` update
    followed by the canonical writeback — the `chain ++ writeback` shape the
    back-edge iterates. -/
def loopBodyFullMN {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w)) (nReg : String) : List LinstrRM :=
  loopBodyChainMN update ++ loopWritebackMN update nReg

/-- Every element of the full body is an `Lopn` (A1's side condition, by
    construction). -/
theorem loopBodyFullMN_isLopn {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w)) (nReg : String) :
    ∀ i ∈ loopBodyFullMN update nReg, IsLopn i := by
  intro i hi
  rw [loopBodyFullMN, List.mem_append] at hi
  rcases hi with hi | hi
  · exact straightOpsMem_isLopn update (invTys.length + 2) (invTys.length + 2) i hi
  · simp only [loopWritebackMN, List.mem_cons] at hi
    rcases hi with rfl | rfl | rfl | h
    · exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, rfl⟩
    · exact absurd h (List.not_mem_nil)

/-- **The proved per-trip pass (R1).** One pass of the emitted
    `chain ++ writeback` body, from ANY machine state agreeing with the trip-`t`
    valuation and holding a readable counter: it succeeds, lands in a state
    agreeing with the trip-`(t+1)` valuation at the stepped accumulator
    `JLoopBodyN.stepC`, and decrements the counter. The chain half is the
    strengthened straight-line simulation (`lsemStraightMem_straightOps_full` —
    final agreement + write frame); the writeback half is the three raw steps
    with the agreement transports. NO encoded-state hypothesis. -/
theorem loopBodyFullMN_trip {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (invs : Ctxt.Valuation invTys) (t : Nat) (acc : BitVec w) (bt : LstateM)
    (hagree : StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt
      (tripValMN invs t acc))
    (vn : BitVec 64) (hn : bt.reg.getW nReg 64 = some vn) :
    ∃ bt', lsemStraightMem (loopBodyFullMN update nReg) bt = some bt'
      ∧ StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt'
          (tripValMN invs (t + 1) (JLoopBodyN.stepC update invs t acc))
      ∧ bt'.reg.getW nReg 64 = some (vn - 1#64) := by
  -- the chain: strengthened straight-line simulation
  obtain ⟨stc, hrunC, hAgC, hFrC, hretC⟩ :=
    lsemStraightMem_straightOps_full hupd rfl rfl le_rfl hagree
  have hret : stc.reg.getW (loopBodyRetRegMN update) w
      = some (JLoopBodyN.stepC update invs t acc) := hretC
  have hnc : stc.reg.getW nReg 64 = some vn :=
    (hFrC.1 nReg 64 (fun k _ => hnr k)).trans hn
  -- split the fold at the writeback
  rw [loopBodyFullMN, lsemStraightMem_append]
  have hchain : lsemStraightMem (loopBodyChainMN update) bt = some stc := hrunC
  rw [hchain, Option.bind_some]
  -- step 1: accumulator writeback
  set stepv : BitVec w := JLoopBodyN.stepC update invs t acc with hstepv
  have h1 := lsemStepMem_add64Imm (accRegMN invTys) (loopBodyRetRegMN update) 0
    stepv stc hret
  rw [show stepv + BitVec.ofNat w 0 = stepv from by simp] at h1
  set s1 := (stc.setReg (accRegMN invTys) stepv).nextPc with hs1
  have hAg1 : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s1
      (.cons stepv (.cons (BitVec.ofNat 64 t) invs) :
        Ctxt.Valuation (JasminTy.reg w :: JasminTy.reg 64 :: invTys)) :=
    StoreAgreesM.nextPc (tripAgree_setReg_acc hAgC stepv)
  -- step 2: loop-index increment
  have hidx1 : s1.reg.getW (idxRegMN invTys) 64 = some (BitVec.ofNat 64 t) :=
    tripAgree_getW_idx hAg1
  have h2 := lsemStepMem_add64Imm (idxRegMN invTys) (idxRegMN invTys) 1
    (BitVec.ofNat 64 t) s1 hidx1
  rw [show BitVec.ofNat 64 t + BitVec.ofNat 64 1 = BitVec.ofNat 64 (t + 1) from by
    rw [BitVec.ofNat_add]] at h2
  set s2 := (s1.setReg (idxRegMN invTys) (BitVec.ofNat 64 (t + 1))).nextPc with hs2
  have hAg2 : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s2
      (.cons stepv (.cons (BitVec.ofNat 64 (t + 1)) invs) :
        Ctxt.Valuation (JasminTy.reg w :: JasminTy.reg 64 :: invTys)) :=
    StoreAgreesM.nextPc (tripAgree_setReg_idx hAg1 (BitVec.ofNat 64 (t + 1)))
  -- step 3: counter decrement
  have hn2 : s2.reg.getW nReg 64 = some vn := by
    rw [hs2, LstateM.getW_setReg_nextPc_other _ _ _ _ _
        (show nReg ≠ idxRegMN invTys from hna invTys.length),
      hs1, LstateM.getW_setReg_nextPc_other _ _ _ _ _
        (show nReg ≠ accRegMN invTys from hna (invTys.length + 1))]
    exact hnc
  have h3 := lsemStepMem_sub64Imm nReg nReg 1 vn s2 hn2
  set s3 := (s2.setReg nReg (vn - BitVec.ofNat 64 1)).nextPc with hs3
  refine ⟨s3, ?_, ?_, ?_⟩
  · -- run the three writeback steps
    show lsemStraightMem (loopWritebackMN update nReg) stc = some s3
    rw [loopWritebackMN, lsemStraightMem_cons_some h1, lsemStraightMem_cons_some h2,
      lsemStraightMem_cons_some h3, lsemStraightMem_nil]
  · exact StoreAgreesM.nextPc
      (StoreAgreesM.setReg_untracked nReg (vn - BitVec.ofNat 64 1) hna hnr hAg2)
  · show ((s2.setReg nReg (vn - BitVec.ofNat 64 1)).nextPc).reg.getW nReg 64 = _
    rw [LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc,
      LstateN.getW_setReg_same]

/-! ## 4. R1 — the trip invariant and the unconditional export theorems -/

/-- **The trip invariant.** Every `runBoundedLoopMem` trip state of the emitted
    `chain ++ writeback` loop agrees with its trip valuation at the source fold
    `JLoopBodyN.denote ⟨t, update⟩`, with a readable counter — proved by
    induction from the seed, one `loopBodyFullMN_trip` per back-edge. -/
theorem loopBodyFullMN_inv {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (invs : Ctxt.Valuation invTys) (s0 : LstateM) (acc0 : BitVec w)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s0
      (tripValMN invs 0 acc0))
    (hn0 : (s0.reg.getW nReg 64).isSome) :
    ∀ t (bt : LstateM),
      runBoundedLoopMem (loopBodyFullMN update nReg) t s0 = some bt →
      StoreAgreesM (invTys.length + 2) (invTys.length + 2) bt
          (tripValMN invs t (JLoopBodyN.denote ⟨t, update⟩ invs acc0))
        ∧ (bt.reg.getW nReg 64).isSome := by
  intro t
  induction t with
  | zero =>
      intro bt hbt
      rw [runBoundedLoopMem_zero] at hbt
      obtain rfl := Option.some.inj hbt
      exact ⟨hseed, hn0⟩
  | succ k ih =>
      intro bt hbt
      rw [runBoundedLoopMem_succ_right] at hbt
      cases hbk : runBoundedLoopMem (loopBodyFullMN update nReg) k s0 with
      | none => rw [hbk] at hbt; simp at hbt
      | some bk =>
          rw [hbk, Option.bind_some] at hbt
          obtain ⟨hAgk, hnk⟩ := ih bk hbk
          obtain ⟨vn, hvn⟩ := Option.isSome_iff_exists.mp hnk
          obtain ⟨bt', hbt', hAg', hn'⟩ := loopBodyFullMN_trip update hupd nReg hna hnr
            invs k (JLoopBodyN.denote ⟨k, update⟩ invs acc0) bk hAgk vn hvn
          rw [hbt', Option.map_some] at hbt
          obtain rfl := Option.some.inj hbt
          refine ⟨?_, ?_⟩
          · rw [JLoopBodyN.denote_succ]
            exact StoreAgreesM.setLpc hAg' 1
          · rw [show ((bt'.setLpc 1).reg).getW nReg 64 = bt'.reg.getW nReg 64 from
              LstateN.getW_congr_lvm (LstateM.reg_lvm_setLpc bt' 1) nReg 64, hn']
            rfl

/-- **A1 export faithfulness, source-tied, UNCONDITIONAL per-trip (R1).** As
    `loopMem_export_faithful_denote`, for the emitted `chain ++ writeback` body
    `loopBodyFullMN`: the remaining hypotheses are the counter **schedule**
    (`hprev`/`hlast`/`hbfin`/`htaken`/`hhalt`), the **seed**
    (`hseed`/`hn0` — the start state is any state agreeing with the trip-0
    valuation, e.g. the encoded arguments) and the counter-name hygiene
    (`hna`/`hnr`). The per-trip simulation `hsim` is DISCHARGED
    (`loopBodyFullMN_trip` through the trip invariant), and the all-`Lopn` side
    condition holds by construction. -/
theorem loopMem_export_faithful_denote_uncond {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update)
    (invs : Ctxt.Valuation invTys)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (acc0 : BitVec w)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s.base
      (tripValMN invs 0 acc0))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (m : Nat) (hm : 0 < m) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyFullMN update nReg) (m - 1) s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyFullMN update nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyFullMN update nReg) m s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi,
      runBoundedLoopMem (loopBodyFullMN update nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg (loopBodyFullMN update nReg)))
          (m * ((loopBodyFullMN update nReg).length + 1)) s = some t
        ∧ decodeM t.base (accRegMN invTys) w
            = some (JLoopBodyN.denote ⟨m, update⟩ invs acc0) := by
  have hinv := loopBodyFullMN_inv update hupd nReg hna hnr invs s.base acc0 hseed hn0
  refine loopMem_export_faithful_denote update invs fn top nReg
    (loopBodyFullMN update nReg) (loopBodyFullMN_isLopn update nReg) s hfn hpc m hm
    bprev blast bfin hprev hlast hbfin htaken hhalt (accRegMN invTys) acc0 ?_ ?_
  · -- the seed decode: read the accumulator arg off the seed agreement
    exact tripAgree_getW_acc hseed
  · -- the per-trip simulation, DISCHARGED through the invariant
    intro t ht bt acct hbt hdec
    obtain ⟨hAgt, hnt⟩ := hinv t bt hbt
    obtain ⟨vn, hvn⟩ := Option.isSome_iff_exists.mp hnt
    have hacct : decodeM bt (accRegMN invTys) w
        = some (JLoopBodyN.denote ⟨t, update⟩ invs acc0) := tripAgree_getW_acc hAgt
    rw [hdec] at hacct
    obtain rfl := Option.some.inj hacct
    obtain ⟨bt', hbt', hAg', _⟩ := loopBodyFullMN_trip update hupd nReg hna hnr
      invs t _ bt hAgt vn hvn
    exact ⟨bt', hbt', tripAgree_getW_acc hAg'⟩

/-- **A1 export faithfulness at `ComL.denote`, UNCONDITIONAL per-trip (R1).**
    The `loopMem_export_faithful_comL` upgrade: the machine run of the emitted
    `chain ++ writeback` counter loop decodes to the front node
    `ComL.forLoopNRt`'s denotation, with only schedule/seed/name-hygiene
    hypotheses. -/
theorem loopMem_export_faithful_comL_uncond {Γ : Ctxt jasminDialect} {w : Nat}
    (update : Com jasminDialect (JasminTy.reg w :: JasminTy.reg 64 :: invTys)
      (JasminTy.reg w))
    (hupd : ScalarMemN update)
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (initV : Ctxt.Var Γ (JasminTy.reg w))
    (invsV : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ)
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hseed : StoreAgreesM (invTys.length + 2) (invTys.length + 2) s.base
      (tripValMN (Expr.lookupArgs invsV V) 0 (initV.lookup V)))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (hm : 0 < (count.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (loopBodyFullMN update nReg) ((count.lookup V).toNat - 1)
      s.base = some bprev)
    (hlast : lsemStraightMem (loopBodyFullMN update nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (loopBodyFullMN update nReg) (count.lookup V).toNat
      s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (count.lookup V).toNat → ∀ bi,
      runBoundedLoopMem (loopBodyFullMN update nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg (loopBodyFullMN update nReg)))
          ((count.lookup V).toNat * ((loopBodyFullMN update nReg).length + 1)) s = some t
        ∧ decodeM t.base (accRegMN invTys) w
            = some ((ComL.forLoopNRt update count initV invsV (.ret .here)).denote V) := by
  rw [comL_forLoopNRt_ret_denote]
  exact loopMem_export_faithful_denote_uncond update hupd (Expr.lookupArgs invsV V)
    fn top nReg hna hnr s hfn hpc (initV.lookup V) hseed hn0 _ hm
    bprev blast bfin hprev hlast hbfin htaken hhalt

/-! ## 5. R4 — the array-carrier decode

The B4 export theorems observe only the register half (`decodeM = reg.getW`),
so an array-ACCUMULATOR loop (the fill phase `out[i] := a[i]`) had no
source-tie form. `decodeArrM` reads a named `larr` region; the fold induction
and the export wrappers below conclude at the array cells, at
`accTy = .stackArr w n` (`JLoopBodyN` is already `accTy`-generic). -/

/-- **The array-carrier decode**: read a named `larr` region off a (halt) state
    at an expected shape — the array analogue of `decodeM`. -/
def decodeArrM (st : LstateM) (obsName : String) (w n : Nat) :
    Option (Fin n → BitVec w) :=
  st.getArr obsName w n

/-- `decodeArrM` reads only the array carrier. -/
theorem decodeArrM_congr_larr (s1 s2 : LstateM) (h : s1.larr = s2.larr)
    (r : String) (w n : Nat) : decodeArrM s1 r w n = decodeArrM s2 r w n :=
  LstateM.getArr_congr_larr h r w n

/-- The back-edge's pc reset does not touch the array carrier. -/
theorem decodeArrM_setLpc (s : LstateM) (pc : Nat) (r : String) (w n : Nat) :
    decodeArrM (s.setLpc pc) r w n = decodeArrM s r w n := rfl

/-- The trip valuation of an **array-accumulator** loop body:
    `[arr, ofNat t, *invs]` over `.stackArr w n :: .reg 64 :: invTys`. -/
def tripValArrMN {w n : Nat} (invs : Ctxt.Valuation invTys) (t : Nat)
    (arr : Fin n → BitVec w) :
    Ctxt.Valuation (d := jasminDialect)
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) :=
  .cons arr (.cons (BitVec.ofNat 64 t) invs)

/-- **The array fold induction.** As `runBoundedLoopMem_decodes_denote`, at an
    array accumulator: if the start state's array cell decodes the seed and
    every trip computes one `JLoopBodyN.stepC` under the `decodeArrM`
    correspondence, the `m`-fold decodes at the array slot to the source loop's
    `m`-fold denotation — the array cells ARE the source's array output. -/
theorem runBoundedLoopMemArr_decodes_denote {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (invs : Ctxt.Valuation invTys) (body : List LinstrRM) (arrSlot : String)
    (s0 : LstateM) (arr0 : Fin n → BitVec w)
    (hinit : decodeArrM s0 arrSlot w n = some arr0) :
    ∀ m : Nat,
      (∀ t, t < m → ∀ (bt : LstateM) (arrt : Fin n → BitVec w),
        runBoundedLoopMem body t s0 = some bt →
        decodeArrM bt arrSlot w n = some arrt →
        ∃ bt', lsemStraightMem body bt = some bt'
          ∧ decodeArrM bt' arrSlot w n
              = some (JLoopBodyN.stepC update invs t arrt)) →
      ∀ bfin : LstateM, runBoundedLoopMem body m s0 = some bfin →
        decodeArrM bfin arrSlot w n
          = some (JLoopBodyN.denote ⟨m, update⟩ invs arr0) := by
  intro m
  induction m with
  | zero =>
      intro _ bfin hrun
      rw [runBoundedLoopMem_zero] at hrun
      obtain rfl := Option.some.inj hrun
      exact hinit
  | succ k ih =>
      intro hsim bfin hrun
      rw [runBoundedLoopMem_succ_right] at hrun
      cases hbk : runBoundedLoopMem body k s0 with
      | none => rw [hbk] at hrun; simp at hrun
      | some bk =>
          rw [hbk, Option.bind_some] at hrun
          have hdk := ih (fun t ht => hsim t (Nat.lt_succ_of_lt ht)) bk hbk
          obtain ⟨bt', hbt', hdec'⟩ := hsim k (Nat.lt_succ_self k) bk _ hbk hdk
          rw [hbt', Option.map_some] at hrun
          obtain rfl := Option.some.inj hrun
          rw [JLoopBodyN.denote_succ, decodeArrM_setLpc]
          exact hdec'

/-! ## 6. R4 — the A1 export theorems at the array cells -/

/-- **A1 export faithfulness — array observable.** As `loopMem_export_faithful`
    (`JasminLsemMemChainBridge`), but observing a named ARRAY region: the halt
    state's `decodeArrM` agrees with the fold's. Uses the array half of
    `loopMem_runBounded` (never re-proved), previously discarded by the
    register-only lift. -/
theorem loopMemArr_export_faithful (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (hlopn : ∀ i ∈ body, IsLopn i)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (m : Nat) (hm : 0 < m) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem body (m - 1) s.base = some bprev)
    (hlast : lsemStraightMem body bprev = some blast)
    (hbfin : runBoundedLoopMem body m s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi, runBoundedLoopMem body i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false)
    (arrSlot : String) (w n : Nat) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          (m * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot w n = decodeArrM bfin arrSlot w n := by
  obtain ⟨t, ht, _hreg, harr⟩ := loopMem_runBounded fn top nReg body hlopn s hfn hpc m hm
    bprev blast bfin hprev hlast hbfin htaken hhalt
  exact ⟨t, ht, decodeArrM_congr_larr t.base bfin harr arrSlot w n⟩

/-- **A1 export faithfulness at the array cells, tied to the source
    denotation.** Under the A1 schedule plus the array seed decode and the
    per-trip simulation, the emitted counter loop's machine run halts at a
    state whose ARRAY slot decodes to `JLoopBodyN.denote ⟨m, update⟩ invs arr0`
    — the source loop's array output. -/
theorem loopMemArr_export_faithful_denote {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (invs : Ctxt.Valuation invTys)
    (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (hlopn : ∀ i ∈ body, IsLopn i)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (m : Nat) (hm : 0 < m) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem body (m - 1) s.base = some bprev)
    (hlast : lsemStraightMem body bprev = some blast)
    (hbfin : runBoundedLoopMem body m s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi, runBoundedLoopMem body i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false)
    (arrSlot : String) (arr0 : Fin n → BitVec w)
    (hinit : decodeArrM s.base arrSlot w n = some arr0)
    (hsim : ∀ t, t < m → ∀ (bt : LstateM) (arrt : Fin n → BitVec w),
      runBoundedLoopMem body t s.base = some bt →
      decodeArrM bt arrSlot w n = some arrt →
      ∃ bt', lsemStraightMem body bt = some bt'
        ∧ decodeArrM bt' arrSlot w n = some (JLoopBodyN.stepC update invs t arrt)) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          (m * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot w n
            = some (JLoopBodyN.denote ⟨m, update⟩ invs arr0) := by
  obtain ⟨t, ht, hdec⟩ := loopMemArr_export_faithful fn top nReg body hlopn s hfn hpc
    m hm bprev blast bfin hprev hlast hbfin htaken hhalt arrSlot w n
  exact ⟨t, ht, hdec.trans (runBoundedLoopMemArr_decodes_denote update invs body
    arrSlot s.base arr0 hinit m hsim bfin hbfin)⟩

/-- The front node's denotation is the loop fold, at ANY accumulator type
    (the `accTy`-generic form of `comL_forLoopNRt_ret_denote` — in particular
    at a memref accumulator). -/
theorem comL_forLoopNRt_ret_denote_acc {Γ : Ctxt jasminDialect} {accTy : JasminTy}
    (update : Com jasminDialect (accTy :: JasminTy.reg 64 :: invTys) accTy)
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (init : Ctxt.Var Γ accTy)
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ) :
    (ComL.forLoopNRt update count init invs (.ret .here)).denote V
      = JLoopBodyN.denote ⟨(count.lookup V).toNat, update⟩
          (Expr.lookupArgs invs V) (init.lookup V) := rfl

/-- **A1 export faithfulness at the array cells, concluded at `ComL.denote`.**
    The machine run of the emitted counter loop decodes AT THE ARRAY SLOT to
    the front node `ComL.forLoopNRt`'s denotation, at a memref accumulator. -/
theorem loopMemArr_export_faithful_comL {Γ : Ctxt jasminDialect} {w n : Nat}
    (update : Com jasminDialect
      (JasminTy.stackArr w n :: JasminTy.reg 64 :: invTys) (JasminTy.stackArr w n))
    (count : Ctxt.Var Γ (JasminTy.reg 64))
    (initV : Ctxt.Var Γ (JasminTy.stackArr w n))
    (invsV : HVector (fun ty => Ctxt.Var Γ ty) invTys) (V : Ctxt.Valuation Γ)
    (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (hlopn : ∀ i ∈ body, IsLopn i)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (hm : 0 < (count.lookup V).toNat) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem body ((count.lookup V).toNat - 1) s.base = some bprev)
    (hlast : lsemStraightMem body bprev = some blast)
    (hbfin : runBoundedLoopMem body (count.lookup V).toNat s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < (count.lookup V).toNat → ∀ bi,
      runBoundedLoopMem body i s.base = some bi → condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false)
    (arrSlot : String)
    (hinit : decodeArrM s.base arrSlot w n = some (initV.lookup V))
    (hsim : ∀ t, t < (count.lookup V).toNat → ∀ (bt : LstateM)
      (arrt : Fin n → BitVec w),
      runBoundedLoopMem body t s.base = some bt →
      decodeArrM bt arrSlot w n = some arrt →
      ∃ bt', lsemStraightMem body bt = some bt'
        ∧ decodeArrM bt' arrSlot w n
            = some (JLoopBodyN.stepC update (Expr.lookupArgs invsV V) t arrt)) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((count.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeArrM t.base arrSlot w n
            = some ((ComL.forLoopNRt update count initV invsV (.ret .here)).denote V) := by
  rw [comL_forLoopNRt_ret_denote_acc]
  exact loopMemArr_export_faithful_denote update (Expr.lookupArgs invsV V) fn top nReg
    body hlopn s hfn hpc _ hm bprev blast bfin hprev hlast hbfin htaken hhalt arrSlot _
    hinit hsim

/-! ## 7. R4 — the fill shape `out[i] := a[i]`, per-trip DISCHARGED

The fill-phase body: load `a[i]` into a scratch slot, store it into `out[i]`
**in place** (the store's destination slot is the accumulator argument itself —
exactly the pass the physical allocator produces from the SSA chain), advance
the index, decrement the counter. Its per-trip simulation is proved from the
raw step lemmas + the agreement transports, so the composed export theorem
below is `hsim`-free. -/

/-- Register read through a `setArr`-then-bump (array writes don't touch the
    register file). -/
theorem LstateM.getW_setArr_nextPc (s : LstateM) (r : String) {w n : Nat}
    (arr : Fin n → BitVec w) (r' : String) (w' : Nat) :
    ((s.setArr r arr).nextPc).reg.getW r' w' = s.reg.getW r' w' := by
  rw [LstateM.reg_nextPc, LstateM.reg_setArr, LstateN.getW_nextPc]

/-- Register read through a `setReg`-then-bump at the same name. -/
theorem LstateM.getW_setReg_nextPc_same (s : LstateM) (r : String) {w : Nat}
    (v : BitVec w) : ((s.setReg r v).nextPc).reg.getW r w = some v := by
  rw [LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc,
    LstateN.getW_setReg_same]

/-- The fill-phase source body `out[i] := a[i]` over
    `[out : .stackArr w n, i : .reg 64, a : .stackArr w n]`: load `a[i]`, store
    it at `out[i]`, return the updated array. -/
def fillUpdate (w n : Nat) : Com jasminDialect
    [JasminTy.stackArr w n, JasminTy.reg 64, JasminTy.stackArr w n]
    (JasminTy.stackArr w n) :=
  .var (⟨JasminOp.stackLoad w n, rfl,
      .cons (.there (.there .here)) (.cons (.there .here) .nil)⟩ :
    Expr jasminDialect _ (.reg w))
    (.var (⟨JasminOp.stackStore w n, rfl,
        .cons (.there .here) (.cons (.there (.there .here)) (.cons .here .nil))⟩ :
      Expr jasminDialect _ (.stackArr w n))
      (.ret .here))

/-- One fill trip denotes `stackSet arr i (stackGet src i)`. -/
theorem fillUpdate_stepC {w n : Nat} (src : Fin n → BitVec w) (t : Nat)
    (arr : Fin n → BitVec w) :
    JLoopBodyN.stepC (fillUpdate w n)
        (.cons src .nil : Ctxt.Valuation (d := jasminDialect) [JasminTy.stackArr w n]) t arr
      = stackSet arr (BitVec.ofNat 64 t).toNat
          (stackGet src (BitVec.ofNat 64 t).toNat) := rfl

/-- **The emitted fill body** (in-place): `LOADIDX r3 ← a0[a1]`,
    `STOREIDX a2 ← a2[a1] := r3`, `ADD a1 ← a1, #1`, `SUB n ← n, #1`. The two
    memory wires are the real `opToLinstrR` images of the `fillUpdate` chain,
    with the store's destination slot physically allocated onto the accumulator
    argument `a2` (the SSA slot `r4` collapsed in place). -/
def fillBodyM (w n : Nat) (nReg : String) : List LinstrRM :=
  [ (LinstrR.Lopn [.reg (regName 3)] "LOADIDX"
      [.arrIdx (argName 0) (argName 1) (w / 8)], MemTag.load w n)
  , (LinstrR.Lopn [.reg (argName 2)] "STOREIDX"
      [.arrIdx (argName 2) (argName 1) (w / 8), .reg (regName 3)], MemTag.store w n)
  , (LinstrR.Lopn [.reg (argName 1)] "ADD:64" [.reg (argName 1), .imm 1],
      MemTag.reg none)
  , (LinstrR.Lopn [.reg nReg] "SUB:64" [.reg nReg, .imm 1], MemTag.reg none) ]

/-- Every fill-body element is an `Lopn`. -/
theorem fillBodyM_isLopn (w n : Nat) (nReg : String) :
    ∀ i ∈ fillBodyM w n nReg, IsLopn i := by
  intro i hi
  simp only [fillBodyM, List.mem_cons] at hi
  rcases hi with rfl | rfl | rfl | rfl | h
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact absurd h (List.not_mem_nil)

/-- **The proved per-trip fill pass (R4).** One pass of the emitted in-place
    fill body, from ANY state agreeing with the trip-`t` valuation and holding
    a readable counter: it succeeds, the accumulator array cell steps by
    `JLoopBodyN.stepC (fillUpdate w n)`, and the next-trip agreement holds. -/
theorem fillBodyM_trip {w n : Nat} (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (src : Fin n → BitVec w) (t : Nat) (arrt : Fin n → BitVec w) (bt : LstateM)
    (hagree : StoreAgreesM 3 3 bt
      (tripValArrMN (invTys := [JasminTy.stackArr w n]) (.cons src .nil) t arrt))
    (vn : BitVec 64) (hn : bt.reg.getW nReg 64 = some vn) :
    ∃ bt', lsemStraightMem (fillBodyM w n nReg) bt = some bt'
      ∧ StoreAgreesM 3 3 bt'
          (tripValArrMN (invTys := [JasminTy.stackArr w n]) (.cons src .nil) (t + 1)
            (JLoopBodyN.stepC (fillUpdate w n)
              (.cons src .nil : Ctxt.Valuation (d := jasminDialect) [JasminTy.stackArr w n]) t arrt))
      ∧ bt'.reg.getW nReg 64 = some (vn - 1#64) := by
  -- reads off the trip agreement
  have hsrc : bt.getArr (argName 0) w n = some src :=
    hagree.arr (.there (.there .here) :
      Ctxt.Var (d := jasminDialect)
        (JasminTy.stackArr w n :: JasminTy.reg 64 :: [JasminTy.stackArr w n])
        (JasminTy.stackArr w n))
  have hidx : bt.reg.getW (argName 1) 64 = some (BitVec.ofNat 64 t) :=
    tripAgree_getW_idx (invTys := [JasminTy.stackArr w n]) hagree
  -- step 1: the load into the scratch slot `r3`
  have h1 := lsemStepMem_loadIdx (regName 3) (argName 0) (argName 1) (w / 8)
    src (BitVec.ofNat 64 t) bt hsrc hidx
  set lv : BitVec w := stackGet src (BitVec.ofNat 64 t).toNat with hlv
  set s1 := (bt.setReg (regName 3) lv).nextPc with hs1
  have hAg1 : StoreAgreesM 3 3 s1
      (tripValArrMN (invTys := [JasminTy.stackArr w n]) (.cons src .nil) t arrt) :=
    StoreAgreesM.nextPc (StoreAgreesM.setReg_scratch rfl 3 (by simp) lv hagree)
  -- step 2: the in-place store into the accumulator slot `a2`
  have hacc1 : s1.getArr (argName 2) w n = some arrt :=
    tripAgree_getArr_acc (invTys := [JasminTy.stackArr w n]) hAg1
  have hidx1 : s1.reg.getW (argName 1) 64 = some (BitVec.ofNat 64 t) :=
    tripAgree_getW_idx (invTys := [JasminTy.stackArr w n]) hAg1
  have hval1 : s1.reg.getW (regName 3) w = some lv := by
    rw [hs1]
    exact LstateM.getW_setReg_nextPc_same bt (regName 3) lv
  have h2 := lsemStepMem_storeIdx (argName 2) (argName 2) (argName 1) (regName 3)
    (w / 8) arrt (BitVec.ofNat 64 t) lv s1 hacc1 hidx1 hval1
  set na : Fin n → BitVec w := stackSet arrt (BitVec.ofNat 64 t).toNat lv with hna2
  set s2 := (s1.setArr (argName 2) na).nextPc with hs2
  have hAg2 : StoreAgreesM 3 3 s2
      (tripValArrMN (invTys := [JasminTy.stackArr w n]) (.cons src .nil) t na) :=
    StoreAgreesM.nextPc (tripAgree_setArr_acc (invTys := [JasminTy.stackArr w n]) hAg1 na)
  -- step 3: the index increment
  have hidx2 : s2.reg.getW (argName 1) 64 = some (BitVec.ofNat 64 t) :=
    tripAgree_getW_idx (invTys := [JasminTy.stackArr w n]) hAg2
  have h3 := lsemStepMem_add64Imm (argName 1) (argName 1) 1 (BitVec.ofNat 64 t) s2 hidx2
  rw [show BitVec.ofNat 64 t + BitVec.ofNat 64 1 = BitVec.ofNat 64 (t + 1) from by
    rw [BitVec.ofNat_add]] at h3
  set s3 := (s2.setReg (argName 1) (BitVec.ofNat 64 (t + 1))).nextPc with hs3
  have hAg3 : StoreAgreesM 3 3 s3
      (tripValArrMN (invTys := [JasminTy.stackArr w n]) (.cons src .nil) (t + 1) na) :=
    StoreAgreesM.nextPc (tripAgree_setReg_idx (invTys := [JasminTy.stackArr w n])
      hAg2 (BitVec.ofNat 64 (t + 1)))
  -- step 4: the counter decrement
  have hn3 : s3.reg.getW nReg 64 = some vn := by
    rw [hs3, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (hna 1),
      hs2, LstateM.getW_setArr_nextPc,
      hs1, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (hnr 3)]
    exact hn
  have h4 := lsemStepMem_sub64Imm nReg nReg 1 vn s3 hn3
  set s4 := (s3.setReg nReg (vn - 1#64)).nextPc with hs4
  refine ⟨s4, ?_, ?_, ?_⟩
  · rw [fillBodyM, lsemStraightMem_cons_some h1, lsemStraightMem_cons_some h2,
      lsemStraightMem_cons_some h3, lsemStraightMem_cons_some h4, lsemStraightMem_nil]
  · rw [fillUpdate_stepC]
    exact StoreAgreesM.nextPc
      (StoreAgreesM.setReg_untracked nReg (vn - 1#64) hna hnr hAg3)
  · rw [hs4]
    exact LstateM.getW_setReg_nextPc_same s3 nReg (vn - 1#64)

/-- **The fill trip invariant** — every trip state agrees with the source fold
    of `fillUpdate` at its trip valuation, with a readable counter. -/
theorem fillBodyM_inv {w n : Nat} (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (src : Fin n → BitVec w) (s0 : LstateM) (arr0 : Fin n → BitVec w)
    (hseed : StoreAgreesM 3 3 s0
      (tripValArrMN (invTys := [JasminTy.stackArr w n]) (.cons src .nil) 0 arr0))
    (hn0 : (s0.reg.getW nReg 64).isSome) :
    ∀ t (bt : LstateM),
      runBoundedLoopMem (fillBodyM w n nReg) t s0 = some bt →
      StoreAgreesM 3 3 bt
          (tripValArrMN (invTys := [JasminTy.stackArr w n]) (.cons src .nil) t
            (JLoopBodyN.denote ⟨t, fillUpdate w n⟩
              (.cons src .nil : Ctxt.Valuation (d := jasminDialect) [JasminTy.stackArr w n]) arr0))
        ∧ (bt.reg.getW nReg 64).isSome := by
  intro t
  induction t with
  | zero =>
      intro bt hbt
      rw [runBoundedLoopMem_zero] at hbt
      obtain rfl := Option.some.inj hbt
      exact ⟨hseed, hn0⟩
  | succ k ih =>
      intro bt hbt
      rw [runBoundedLoopMem_succ_right] at hbt
      cases hbk : runBoundedLoopMem (fillBodyM w n nReg) k s0 with
      | none => rw [hbk] at hbt; simp at hbt
      | some bk =>
          rw [hbk, Option.bind_some] at hbt
          obtain ⟨hAgk, hnk⟩ := ih bk hbk
          obtain ⟨vn, hvn⟩ := Option.isSome_iff_exists.mp hnk
          obtain ⟨bt', hbt', hAg', hn'⟩ := fillBodyM_trip nReg hna hnr src k _ bk
            hAgk vn hvn
          rw [hbt', Option.map_some] at hbt
          obtain rfl := Option.some.inj hbt
          refine ⟨?_, ?_⟩
          · rw [JLoopBodyN.denote_succ]
            exact StoreAgreesM.setLpc hAg' 1
          · rw [show ((bt'.setLpc 1).reg).getW nReg 64 = bt'.reg.getW nReg 64 from
              LstateN.getW_congr_lvm (LstateM.reg_lvm_setLpc bt' 1) nReg 64, hn']
            rfl

/-- **The fill-loop export theorem, at the array cells, UNCONDITIONAL per-trip
    (R4).** The emitted in-place fill loop `out[i] := a[i]` (runtime trip count
    read off the counter register), run by the machine model from any seed
    state agreeing with the trip-0 valuation: the halt state's array slot
    `decodeArrM`s to the source fold `JLoopBodyN.denote ⟨m, fillUpdate w n⟩` —
    the array cells ARE the source denotation's array output. Only
    schedule/seed/name-hygiene hypotheses; `hsim` is discharged. -/
theorem fillLoop_export_faithful_denote {w n : Nat}
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (src arr0 : Fin n → BitVec w)
    (hseed : StoreAgreesM 3 3 s.base
      (tripValArrMN (invTys := [JasminTy.stackArr w n]) (.cons src .nil) 0 arr0))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (m : Nat) (hm : 0 < m) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (fillBodyM w n nReg) (m - 1) s.base = some bprev)
    (hlast : lsemStraightMem (fillBodyM w n nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (fillBodyM w n nReg) m s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi,
      runBoundedLoopMem (fillBodyM w n nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg (fillBodyM w n nReg)))
          (m * ((fillBodyM w n nReg).length + 1)) s = some t
        ∧ decodeArrM t.base (argName 2) w n
            = some (JLoopBodyN.denote ⟨m, fillUpdate w n⟩
                (.cons src .nil : Ctxt.Valuation (d := jasminDialect) [JasminTy.stackArr w n]) arr0) := by
  have hinv := fillBodyM_inv nReg hna hnr src s.base arr0 hseed hn0
  refine loopMemArr_export_faithful_denote (invTys := [JasminTy.stackArr w n])
    (fillUpdate w n) (.cons src .nil) fn top nReg (fillBodyM w n nReg)
    (fillBodyM_isLopn w n nReg) s hfn hpc m hm bprev blast bfin hprev hlast hbfin
    htaken hhalt (argName 2) arr0 ?_ ?_
  · exact tripAgree_getArr_acc (invTys := [JasminTy.stackArr w n]) hseed
  · intro t ht bt arrt hbt hdec
    obtain ⟨hAgt, hnt⟩ := hinv t bt hbt
    obtain ⟨vn, hvn⟩ := Option.isSome_iff_exists.mp hnt
    have harrt : decodeArrM bt (argName 2) w n
        = some (JLoopBodyN.denote ⟨t, fillUpdate w n⟩
            (.cons src .nil : Ctxt.Valuation (d := jasminDialect) [JasminTy.stackArr w n]) arr0) :=
      tripAgree_getArr_acc (invTys := [JasminTy.stackArr w n]) hAgt
    rw [hdec] at harrt
    obtain rfl := Option.some.inj harrt
    obtain ⟨bt', hbt', hAg', _⟩ := fillBodyM_trip nReg hna hnr src t _ bt hAgt vn hvn
    exact ⟨bt', hbt', tripAgree_getArr_acc (invTys := [JasminTy.stackArr w n]) hAg'⟩

/-! ## 8. Validation: the unconditional theorems instantiated on concrete runs

R1: the B4 §7 doubling loop re-derived THROUGH
`loopMem_export_faithful_denote_uncond` — no `hsim` side condition (the per-trip
pass is proved). The body is the CANONICAL `chain ++ writeback` (with the
loop-index increment the §7 hand-writeback omitted). R4: a 4-cell fill loop at
runtime count 3 through `fillLoop_export_faithful_denote` — the array cells
decode to the source fold. -/

/-- The counter register name `"n"` is no argument name (`"a…"`). -/
theorem counterN_ne_argName (j : Nat) : "n" ≠ argName j := by
  unfold argName
  intro h
  have hd := congrArg (fun s => s.toList.head?) h
  simp [String.toList_append] at hd

/-- The counter register name `"n"` is no SSA register name (`"r…"`). -/
theorem counterN_ne_regName (k : Nat) : "n" ≠ regName k := by
  unfold regName
  intro h
  have hd := congrArg (fun s => s.toList.head?) h
  simp [String.toList_append] at hd

/-! ### R1 validate: the doubling loop, hsim-free -/

/-- The canonical emitted body of the doubling loop: the linearizer chain of
    `wUpd` (`acc := acc + acc`) + the canonical writeback. -/
def wBodyU : List LinstrRM := loopBodyFullMN (invTys := []) wUpd "n"

/-- The doubling-loop program on counter `"n"`. -/
def wProgU : LprogM := singletonProgM "f" (loopLinstrRM 0 "n" wBodyU)

/-- The seed base state: the encoded trip-0 valuation (`acc = 5`), counter
    `n = 2`, pc at the loop top. -/
def wBaseU : LstateM :=
  (((encodeM (tripValMN (invTys := []) .nil 0 (5#64))).setReg "n" (2#64)).setLpc 1)

/-- The seed program state. -/
def wStartU : LstatePM := { base := wBaseU, lfn := "f" }

/-- The seed state agrees with the trip-0 valuation (the encoded arguments,
    with the untracked counter write and the pc move absorbed). -/
theorem wBaseU_seed :
    StoreAgreesM 2 2 wBaseU (tripValMN (invTys := []) .nil 0 (5#64)) :=
  StoreAgreesM.setLpc
    (StoreAgreesM.setReg_untracked "n" (2#64) counterN_ne_argName counterN_ne_regName
      (encodeM_StoreAgreesM (tripValMN (invTys := []) .nil 0 (5#64)))) 1

/-- Trip 1 of the doubling loop reaches a state. -/
theorem wPrev_isSome : (runBoundedLoopMem wBodyU 1 wBaseU).isSome := by native_decide

/-- The trip-1 state. -/
def wPrevU : LstateM := (runBoundedLoopMem wBodyU 1 wBaseU).get wPrev_isSome

theorem wPrevU_eq : runBoundedLoopMem wBodyU 1 wBaseU = some wPrevU :=
  (Option.some_get wPrev_isSome).symm

/-- The last body pass from the trip-1 state succeeds. -/
theorem wLast_isSome : (lsemStraightMem wBodyU wPrevU).isSome := by native_decide

/-- The post-last-pass state. -/
def wLastU : LstateM := (lsemStraightMem wBodyU wPrevU).get wLast_isSome

theorem wLastU_eq : lsemStraightMem wBodyU wPrevU = some wLastU :=
  (Option.some_get wLast_isSome).symm

/-- The 2-trip fold reaches a state. -/
theorem wFin_isSome : (runBoundedLoopMem wBodyU 2 wBaseU).isSome := by native_decide

/-- The 2-trip fold state. -/
def wFinU : LstateM := (runBoundedLoopMem wBodyU 2 wBaseU).get wFin_isSome

theorem wFinU_eq : runBoundedLoopMem wBodyU 2 wBaseU = some wFinU :=
  (Option.some_get wFin_isSome).symm

/-- **Validate (R1).** The doubling-loop conclusion derived THROUGH the
    unconditional export theorem: only the schedule (concrete run facts), the
    seed agreement and the counter-name hygiene are supplied — **no `hsim`
    side condition**. The machine run of the emitted `chain ++ writeback` loop
    decodes the accumulator argument to the source denotation
    `JLoopBodyN.denote ⟨2, wUpd⟩ .nil 5`. -/
theorem wLoop_export_uncond :
    ∃ t : LstatePM,
      lsemFuelMemL wProgU (2 * (wBodyU.length + 1)) wStartU = some t
        ∧ decodeM t.base (accRegMN []) 64
            = some (JLoopBodyN.denote ⟨2, wUpd⟩ .nil (5#64)) := by
  refine loopMem_export_faithful_denote_uncond (invTys := []) wUpd wUpd_scalarMemN
    .nil "f" 0 "n" counterN_ne_argName counterN_ne_regName wStartU rfl rfl (5#64)
    wBaseU_seed (by native_decide) 2 (by omega) wPrevU wLastU wFinU wPrevU_eq
    wLastU_eq wFinU_eq ?_ (by native_decide)
  intro i h1 h2 bi hbi
  have hi : i = 1 := by omega
  subst hi
  obtain rfl := Option.some.inj (wPrevU_eq.symm.trans hbi)
  native_decide

/-- **Validate (R1, value + non-vacuity crosscheck).** The same fuel/program
    actually runs to a halt whose accumulator decodes `20` (`5 → 10 → 20`) —
    the theorem's existential is inhabited by the real run. -/
example :
    (lsemFuelMemL wProgU (2 * (wBodyU.length + 1)) wStartU).map
        (fun t => decodeM t.base (accRegMN []) 64)
      = some (some (20#64)) := by native_decide

/-! ### R4 validate: a 4-cell fill loop at runtime count 3 -/

/-- The source array. -/
def fSrc : Fin 4 → BitVec 64 := ![101#64, 202#64, 303#64, 404#64]

/-- The output seed (survives where no trip writes — cell 3). -/
def fInit : Fin 4 → BitVec 64 := ![7#64, 7#64, 7#64, 7#64]

/-- The emitted fill body at `w = 64`, `n = 4`, counter `"n"`. -/
def fBodyV : List LinstrRM := fillBodyM 64 4 "n"

/-- The fill-loop program. -/
def fProgV : LprogM := singletonProgM "f" (loopLinstrRM 0 "n" fBodyV)

/-- The seed base: encoded `[out = fInit, i = 0, a = fSrc]`, counter `n = 3`,
    pc at the loop top. -/
def fBaseV : LstateM :=
  (((encodeM (tripValArrMN (invTys := [JasminTy.stackArr 64 4])
      (.cons fSrc .nil) 0 fInit)).setReg "n" (3#64)).setLpc 1)

/-- The seed program state. -/
def fStartV : LstatePM := { base := fBaseV, lfn := "f" }

/-- The fill seed agrees with the trip-0 valuation. -/
theorem fBaseV_seed :
    StoreAgreesM 3 3 fBaseV
      (tripValArrMN (invTys := [JasminTy.stackArr 64 4]) (.cons fSrc .nil) 0 fInit) :=
  StoreAgreesM.setLpc
    (StoreAgreesM.setReg_untracked "n" (3#64) counterN_ne_argName counterN_ne_regName
      (encodeM_StoreAgreesM (tripValArrMN (invTys := [JasminTy.stackArr 64 4])
        (.cons fSrc .nil) 0 fInit))) 1

theorem fT1_isSome : (runBoundedLoopMem fBodyV 1 fBaseV).isSome := by native_decide

/-- The trip-1 state. -/
def fT1 : LstateM := (runBoundedLoopMem fBodyV 1 fBaseV).get fT1_isSome

theorem fT1_eq : runBoundedLoopMem fBodyV 1 fBaseV = some fT1 :=
  (Option.some_get fT1_isSome).symm

theorem fT2_isSome : (runBoundedLoopMem fBodyV 2 fBaseV).isSome := by native_decide

/-- The trip-2 state. -/
def fT2 : LstateM := (runBoundedLoopMem fBodyV 2 fBaseV).get fT2_isSome

theorem fT2_eq : runBoundedLoopMem fBodyV 2 fBaseV = some fT2 :=
  (Option.some_get fT2_isSome).symm

theorem fLast_isSome : (lsemStraightMem fBodyV fT2).isSome := by native_decide

/-- The post-last-pass state. -/
def fLastV : LstateM := (lsemStraightMem fBodyV fT2).get fLast_isSome

theorem fLastV_eq : lsemStraightMem fBodyV fT2 = some fLastV :=
  (Option.some_get fLast_isSome).symm

theorem fFin_isSome : (runBoundedLoopMem fBodyV 3 fBaseV).isSome := by native_decide

/-- The 3-trip fold state. -/
def fFinV : LstateM := (runBoundedLoopMem fBodyV 3 fBaseV).get fFin_isSome

theorem fFinV_eq : runBoundedLoopMem fBodyV 3 fBaseV = some fFinV :=
  (Option.some_get fFin_isSome).symm

/-- **Validate (R4).** The fill loop `out[i] := a[i]` at runtime count 3 over 4
    cells, THROUGH the hsim-free export theorem: the machine run's halt state
    decodes AT THE ARRAY SLOT to the source fold
    `JLoopBodyN.denote ⟨3, fillUpdate 64 4⟩ [fSrc] fInit` — the array cells are
    the source denotation's array output. -/
theorem fillLoop_export_uncond :
    ∃ t : LstatePM,
      lsemFuelMemL fProgV (3 * (fBodyV.length + 1)) fStartV = some t
        ∧ decodeArrM t.base (argName 2) 64 4
            = some (JLoopBodyN.denote ⟨3, fillUpdate 64 4⟩
                (.cons fSrc .nil :
                  Ctxt.Valuation (d := jasminDialect) [JasminTy.stackArr 64 4]) fInit) := by
  refine fillLoop_export_faithful_denote "f" 0 "n" counterN_ne_argName
    counterN_ne_regName fStartV rfl rfl fSrc fInit fBaseV_seed (by native_decide)
    3 (by omega) fT2 fLastV fFinV fT2_eq fLastV_eq fFinV_eq ?_ (by native_decide)
  intro i h1 h2 bi hbi
  have hi : i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl
  · obtain rfl := Option.some.inj (fT1_eq.symm.trans hbi)
    native_decide
  · obtain rfl := Option.some.inj (fT2_eq.symm.trans hbi)
    native_decide

/-- **Validate (R4, cells crosscheck).** The source fold's cells are the
    expected fill (`[101, 202, 303, 7]` — three trips copy, cell 3 keeps the
    seed). -/
example :
    ((List.finRange 4).map (fun i =>
        (JLoopBodyN.denote ⟨3, fillUpdate 64 4⟩
          (.cons fSrc .nil :
            Ctxt.Valuation (d := jasminDialect) [JasminTy.stackArr 64 4]) fInit i).toNat))
      = [101, 202, 303, 7] := by native_decide

/-- The machine run's array cells equal the source fold's, read off the real
    `lsemFuelMemL` halt state (fuel/schedule non-vacuous). -/
example :
    (lsemFuelMemL fProgV (3 * (fBodyV.length + 1)) fStartV).map (fun t =>
        (decodeArrM t.base (argName 2) 64 4).map (fun f =>
          (List.finRange 4).map (fun i => (f i).toNat)))
      = some (some [101, 202, 303, 7]) := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
