/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond

@[expose] public section

set_option autoImplicit false

/-!
# The wide (aggregate) loop carrier: `scf.for iter_args : any fixed-width T`

`JasminLsemMemSourceTieUncond` closes the loop-export faithfulness at two
carriers: a **scalar** `reg w` accumulator (`loopMem_export_faithful_comL_uncond`,
per-trip discharged for any `ScalarMemN` update) and a **`stackArr w n` array**
accumulator (`loopMemArr_export_faithful_comL`, general array update, per-trip
`hsim` hypothesised — discharged unconditionally only for the copy shape
`fillUpdate`). This module adds the two remaining pieces for the
`iter_args : any fixed-width aggregate` (MLIR `scf.for`) capability:

1. **A carrier-agnostic export theorem** (§2): `decodeCarrier` reads the halt
   state at an arbitrary accumulator type `accTy` (`.reg w` → the register decode
   `decodeM`; `.stackArr w n` → the array decode `decodeArrM`), and
   `loopWide_export_faithful_comL` states the export faithfulness at that
   `accTy`, delegating to the scalar/array theorems by cases. This is the
   `iter_args : any T` statement; adding a carrier arm extends it.

2. **A COUPLED aggregate update, per-trip DISCHARGED** (§3–§5): the essential
   Montgomery-ladder capability a scalar carrier cannot express — a
   loop-carried `stackArr w 2` state `[x, z]` whose next value depends on
   *both* old cells (`x' = x + z`, `z' = x − z`, the differential-addition
   core). Its emitted in-place body (materialise the two static cell indices,
   double-buffer the two old cells into scratch, recompute, store both back,
   advance the index, decrement the counter) gets its per-trip simulation
   *proved*, so the composed export theorem `ladderLoop_export_faithful_denote`
   is `hsim`-free — a 4-coordinate ladder pairs two such blocks.

The reg/reg arithmetic and immediate-MOV raw steps (§1) extend the
`JasminLsemMemSourceTieUncond` reg/imm bricks to the two-source and nullary
opcode shapes the coupled update needs.

**0 sorries; axioms inherited from the imported `jasminDialect` denotation +
`Lean.ofReduceBool` for the §5 concrete witnesses.**
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieWide

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
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTie
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond

/-! ## 1. Two-source and nullary raw steps

The `JasminLsemMemSourceTieUncond` reg/imm bricks (`lsemStepMem_add64Imm`,
`lsemStepMem_sub64Imm`) handle a single register source plus an immediate. The
coupled update recomputes a cell from *two* register sources and materialises a
static cell index from an immediate, so we add the reg/reg and immediate-MOV
raw steps at the same delegation depth. -/

/-- Width tag strip: `"MOV:64" → "MOV"`. -/
theorem stripWidthTag_MOV64 : stripWidthTag "MOV:64" = "MOV" := by decide +kernel

/-- The width tag of `"MOV:64"` recovers width 64. -/
theorem widthFromTag_MOV64 : widthFromTag "MOV:64" = 64 := by decide +kernel

/-- **Raw step — immediate MOV `dst ← #k` at width 64.** Materialise a constant
    (e.g. a static array cell index) into a register. -/
theorem lsemStepMem_movImm (dst : String) (k : Nat) (st : LstateM) :
    lsemStepMem (LinstrR.Lopn [.reg dst] "MOV:64" [.imm k], MemTag.reg none) st
      = some ((st.setReg dst (BitVec.ofNat 64 k)).nextPc) := by
  have hstep : lsemStepCast (LinstrR.Lopn [.reg dst] "MOV:64" [.imm k], none) st.reg
      = some ((st.reg.setReg dst (BitVec.ofNat 64 k)).nextPc) := by
    rw [lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ rfl rfl rfl rfl rfl,
      lsemStepSh_of_not_sar _ _ (by simp [sarStruct?])]
    simp only [lsemStepN, stripWidthTag_MOV64, if_true]
    rw [widthFromTag_MOV64]
  rw [lsemStepMem_reg, hstep, Option.map_some]
  rfl

/-- **Raw step — reg/reg `ADD dst ← a, b` at width 64.** Both sources are
    registers; the data width is recovered from `a`'s store tag and `b` is read
    at it. -/
theorem lsemStepMem_add64Reg (dst a b : String) {w : Nat} (va vb : BitVec w)
    (st : LstateM) (ha : st.reg.getW a w = some va) (hb : st.reg.getW b w = some vb) :
    lsemStepMem (LinstrR.Lopn [.reg dst] "ADD:64" [.reg a, .reg b], MemTag.reg none) st
      = some ((st.setReg dst (va + vb)).nextPc) := by
  have hstep : lsemStepCast (LinstrR.Lopn [.reg dst] "ADD:64" [.reg a, .reg b], none) st.reg
      = some ((st.reg.setReg dst (va + vb)).nextPc) := by
    rw [lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ (by simp [mulhiStruct?, stripWidthTag_ADD64]) rfl rfl rfl rfl,
      lsemStepSh_of_not_sar _ _ (by simp [sarStruct?])]
    simp only [lsemStepN, readReg_of_getW ha, evalOperandN, hb, stripWidthTag_ADD64,
      applyOpnN]
  rw [lsemStepMem_reg, hstep, Option.map_some]
  rfl

/-- **Raw step — reg/reg `SUB dst ← a, b` at width 64.** -/
theorem lsemStepMem_sub64Reg (dst a b : String) {w : Nat} (va vb : BitVec w)
    (st : LstateM) (ha : st.reg.getW a w = some va) (hb : st.reg.getW b w = some vb) :
    lsemStepMem (LinstrR.Lopn [.reg dst] "SUB:64" [.reg a, .reg b], MemTag.reg none) st
      = some ((st.setReg dst (va - vb)).nextPc) := by
  have hstep : lsemStepCast (LinstrR.Lopn [.reg dst] "SUB:64" [.reg a, .reg b], none) st.reg
      = some ((st.reg.setReg dst (va - vb)).nextPc) := by
    rw [lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ (by simp [mulhiStruct?, stripWidthTag_SUB64]) rfl rfl rfl rfl,
      lsemStepSh_of_not_sar _ _ (by simp [sarStruct?])]
    simp only [lsemStepN, readReg_of_getW ha, evalOperandN, hb, stripWidthTag_SUB64,
      applyOpnN]
  rw [lsemStepMem_reg, hstep, Option.map_some]
  rfl

/-! ## 2. The carrier-agnostic export theorem (`iter_args : any fixed-width T`)

The scalar (`decodeM`) and array (`decodeArrM`) halt observations are the two
instances of one carrier-generic decode. `decodeCarrier accTy` reads the halt
state at an arbitrary accumulator type, `runBoundedLoopMemWide_decodes_denote`
is the fold induction parametric in any pc-invariant decode, and
`loopWide_export_faithful_denote` / `_comL` are the export theorems concluding at
`decodeCarrier` for an arbitrary `accTy`. Adding a carrier arm to `decodeCarrier`
(with its pc-invariance + halt-congruence facts) extends the theorem to that
carrier — the statement is `accTy`-polymorphic. -/

variable {invTys : Ctxt jasminDialect}

/-- Read the halt state at an **arbitrary** accumulator type: the register decode
    `decodeM` for `.reg w`, the array decode `decodeArrM` for `.stackArr w n`.
    The `iter_args : any fixed-width T` observation. -/
def decodeCarrier : (accTy : JasminTy) → LstateM → String → Option ⟦accTy⟧
  | .reg w, st, name => decodeM st name w
  | .stackArr w n, st, name => decodeArrM st name w n
  | _, _, _ => none

/-- `decodeCarrier` ignores the pc (the back-edge's `setLpc`). -/
theorem decodeCarrier_setLpc (accTy : JasminTy) (st : LstateM) (pc : Nat) (name : String) :
    decodeCarrier accTy (st.setLpc pc) name = decodeCarrier accTy st name := by
  cases accTy with
  | reg w => exact decodeM_setLpc st pc name w
  | stackArr w n => exact decodeArrM_setLpc st pc name w n
  | bool => rfl
  | inlineInt => rfl

/-- `decodeCarrier` transports across a register-store + array-carrier equality —
    the two halves `loopMem_runBounded` exposes at the interpreter halt state. -/
theorem decodeCarrier_congr (accTy : JasminTy) {s1 s2 : LstateM}
    (hreg : s1.reg.lvm = s2.reg.lvm) (harr : s1.larr = s2.larr) (name : String) :
    decodeCarrier accTy s1 name = decodeCarrier accTy s2 name := by
  cases accTy with
  | reg w => exact LstateN.getW_congr_lvm hreg name w
  | stackArr w n => exact LstateM.getArr_congr_larr harr name w n
  | bool => rfl
  | inlineInt => rfl

/-- **The carrier-generic fold induction.** As `runBoundedLoopMemArr_decodes_denote`,
    parametric in ANY pc-invariant `decode`: if the seed decodes `acc0` and every
    trip computes one `JLoopBodyN.stepC` under the `decode` correspondence, the
    `m`-fold decodes to the source loop's `m`-fold denotation. Instantiating
    `decode := decodeCarrier accTy · accSlot` covers every carrier at once. -/
theorem runBoundedLoopMemWide_decodes_denote {accTy : JasminTy}
    (update : Com jasminDialect (accTy :: JasminTy.reg 64 :: invTys) accTy)
    (invs : Ctxt.Valuation invTys) (body : List LinstrRM)
    (decode : LstateM → Option ⟦accTy⟧)
    (hdec_pc : ∀ (s : LstateM) (p : Nat), decode (s.setLpc p) = decode s)
    (s0 : LstateM) (acc0 : ⟦accTy⟧) (hinit : decode s0 = some acc0) :
    ∀ m : Nat,
      (∀ t, t < m → ∀ (bt : LstateM) (acct : ⟦accTy⟧),
        runBoundedLoopMem body t s0 = some bt → decode bt = some acct →
        ∃ bt', lsemStraightMem body bt = some bt' ∧
          decode bt' = some (JLoopBodyN.stepC update invs t acct)) →
      ∀ bfin : LstateM, runBoundedLoopMem body m s0 = some bfin →
        decode bfin = some (JLoopBodyN.denote ⟨m, update⟩ invs acc0) := by
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
          rw [JLoopBodyN.denote_succ, hdec_pc]
          exact hdec'

/-- **The carrier-agnostic export theorem, tied to the source denotation.** For
    an arbitrary accumulator type `accTy`, under the A1 counter schedule plus the
    carrier seed decode and the per-trip simulation (both at `decodeCarrier`), the
    emitted counter loop's machine run halts at a state whose carrier decodes to
    `JLoopBodyN.denote ⟨m, update⟩ invs acc0`. The `.reg w` and `.stackArr w n`
    export theorems of `JasminLsemMemSourceTie{,Uncond}` are its two carriers. -/
theorem loopWide_export_faithful_denote {accTy : JasminTy}
    (update : Com jasminDialect (accTy :: JasminTy.reg 64 :: invTys) accTy)
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
    (accSlot : String) (acc0 : ⟦accTy⟧)
    (hinit : decodeCarrier accTy s.base accSlot = some acc0)
    (hsim : ∀ t, t < m → ∀ (bt : LstateM) (acct : ⟦accTy⟧),
      runBoundedLoopMem body t s.base = some bt →
      decodeCarrier accTy bt accSlot = some acct →
      ∃ bt', lsemStraightMem body bt = some bt' ∧
        decodeCarrier accTy bt' accSlot = some (JLoopBodyN.stepC update invs t acct)) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          (m * (body.length + 1)) s = some t
        ∧ decodeCarrier accTy t.base accSlot
            = some (JLoopBodyN.denote ⟨m, update⟩ invs acc0) := by
  obtain ⟨t, ht, hreg, harr⟩ := loopMem_runBounded fn top nReg body hlopn s hfn hpc m hm
    bprev blast bfin hprev hlast hbfin htaken hhalt
  refine ⟨t, ht, ?_⟩
  rw [decodeCarrier_congr accTy hreg harr accSlot]
  exact runBoundedLoopMemWide_decodes_denote update invs body
    (fun st => decodeCarrier accTy st accSlot)
    (fun s p => decodeCarrier_setLpc accTy s p accSlot) s.base acc0 hinit m hsim bfin hbfin

/-- **The carrier-agnostic export theorem, concluded at `ComL.forLoopNRt`.** The
    machine run of the emitted counter loop decodes at the carrier to the front
    node's denotation, at an ARBITRARY accumulator type. -/
theorem loopWide_export_faithful_comL {Γ : Ctxt jasminDialect} {accTy : JasminTy}
    (update : Com jasminDialect (accTy :: JasminTy.reg 64 :: invTys) accTy)
    (count : Ctxt.Var Γ (JasminTy.reg 64)) (initV : Ctxt.Var Γ accTy)
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
    (accSlot : String)
    (hinit : decodeCarrier accTy s.base accSlot = some (initV.lookup V))
    (hsim : ∀ t, t < (count.lookup V).toNat → ∀ (bt : LstateM) (acct : ⟦accTy⟧),
      runBoundedLoopMem body t s.base = some bt →
      decodeCarrier accTy bt accSlot = some acct →
      ∃ bt', lsemStraightMem body bt = some bt' ∧
        decodeCarrier accTy bt' accSlot
          = some (JLoopBodyN.stepC update (Expr.lookupArgs invsV V) t acct)) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg body))
          ((count.lookup V).toNat * (body.length + 1)) s = some t
        ∧ decodeCarrier accTy t.base accSlot
            = some ((ComL.forLoopNRt update count initV invsV (.ret .here)).denote V) := by
  rw [comL_forLoopNRt_ret_denote_acc]
  exact loopWide_export_faithful_denote update (Expr.lookupArgs invsV V) fn top nReg
    body hlopn s hfn hpc _ hm bprev blast bfin hprev hlast hbfin htaken hhalt accSlot _
    hinit hsim

/-! ## 3. A COUPLED aggregate update: the Montgomery differential-addition core

The essential capability a scalar carrier cannot express: a loop-carried
`stackArr w 2` state `[x, z]` whose next value depends on *both* old cells,
`x' = x + z`, `z' = x − z` — the differential-addition step at the heart of a
Montgomery ladder (a 4-coordinate ladder state pairs two such blocks). The
source update reads both cells, recomputes both, and stores both; the emitted
body materialises the two static cell indices, double-buffers the old cells into
scratch registers (so the recompute sees the OLD `x, z` — the coupling would be
destroyed by an in-place single-cell pass), stores both back, then advances the
index and decrements the counter. -/

/-- The coupled source body over `[acc : .stackArr w 2, i : .reg 64]`: load the
    two cells at static indices `0, 1`, compute `x + z` and `x − z`, store both
    back. Returns the updated pair. -/
def ladderUpdate (w : Nat) : Com jasminDialect
    [JasminTy.stackArr w 2, JasminTy.reg 64] (JasminTy.stackArr w 2) :=
  .var (⟨JasminOp.regConst 64 0, rfl, .nil⟩ : Expr jasminDialect _ (.reg 64))
  (.var (⟨JasminOp.regConst 64 1, rfl, .nil⟩ : Expr jasminDialect _ (.reg 64))
  (.var (⟨JasminOp.stackLoad w 2, rfl,
      .cons (.there (.there .here)) (.cons (.there .here) .nil)⟩ :
    Expr jasminDialect _ (.reg w))
  (.var (⟨JasminOp.stackLoad w 2, rfl,
      .cons (.there (.there (.there .here))) (.cons (.there .here) .nil)⟩ :
    Expr jasminDialect _ (.reg w))
  (.var (⟨JasminOp.regArith .add w, rfl,
      .cons (.there .here) (.cons .here .nil)⟩ :
    Expr jasminDialect _ (.reg w))
  (.var (⟨JasminOp.regArith .sub w, rfl,
      .cons (.there (.there .here)) (.cons (.there .here) .nil)⟩ :
    Expr jasminDialect _ (.reg w))
  (.var (⟨JasminOp.stackStore w 2, rfl,
      .cons (.there (.there (.there (.there (.there (.there .here))))))
        (.cons (.there (.there (.there (.there (.there .here)))))
          (.cons (.there .here) .nil))⟩ :
    Expr jasminDialect _ (.stackArr w 2))
  (.var (⟨JasminOp.stackStore w 2, rfl,
      .cons .here
        (.cons (.there (.there (.there (.there (.there .here)))))
          (.cons (.there .here) .nil))⟩ :
    Expr jasminDialect _ (.stackArr w 2))
  (.ret .here))))))))

/-- One coupled trip denotes the differential-addition step on the pair. -/
theorem ladderUpdate_stepC {w : Nat} (t : Nat) (arr : Fin 2 → BitVec w) :
    JLoopBodyN.stepC (ladderUpdate w)
        (.nil : Ctxt.Valuation (d := jasminDialect) []) t arr
      = stackSet (stackSet arr (BitVec.ofNat 64 0).toNat
            (stackGet arr (BitVec.ofNat 64 0).toNat + stackGet arr (BitVec.ofNat 64 1).toNat))
          (BitVec.ofNat 64 1).toNat
          (stackGet arr (BitVec.ofNat 64 0).toNat - stackGet arr (BitVec.ofNat 64 1).toNat) :=
  rfl

/-- **The emitted coupled body** (`w`, counter `nReg`): materialise the static
    cell indices, double-buffer the two old cells into scratch, recompute the
    coupled pair, store both cells back in place, advance the index, decrement
    the counter. Scratch registers: `regName 2..9`; accumulator `argName 1`;
    loop index `argName 0`. -/
def ladderBodyM (w : Nat) (nReg : String) : List LinstrRM :=
  [ (LinstrR.Lopn [.reg (regName 2)] "MOV:64" [.imm 0], MemTag.reg none)
  , (LinstrR.Lopn [.reg (regName 4)] "LOADIDX"
      [.arrIdx (argName 1) (regName 2) (w / 8)], MemTag.load w 2)
  , (LinstrR.Lopn [.reg (regName 3)] "MOV:64" [.imm 1], MemTag.reg none)
  , (LinstrR.Lopn [.reg (regName 5)] "LOADIDX"
      [.arrIdx (argName 1) (regName 3) (w / 8)], MemTag.load w 2)
  , (LinstrR.Lopn [.reg (regName 6)] "ADD:64" [.reg (regName 4), .reg (regName 5)],
      MemTag.reg none)
  , (LinstrR.Lopn [.reg (regName 7)] "SUB:64" [.reg (regName 4), .reg (regName 5)],
      MemTag.reg none)
  , (LinstrR.Lopn [.reg (regName 8)] "MOV:64" [.imm 0], MemTag.reg none)
  , (LinstrR.Lopn [.reg (argName 1)] "STOREIDX"
      [.arrIdx (argName 1) (regName 8) (w / 8), .reg (regName 6)], MemTag.store w 2)
  , (LinstrR.Lopn [.reg (regName 9)] "MOV:64" [.imm 1], MemTag.reg none)
  , (LinstrR.Lopn [.reg (argName 1)] "STOREIDX"
      [.arrIdx (argName 1) (regName 9) (w / 8), .reg (regName 7)], MemTag.store w 2)
  , (LinstrR.Lopn [.reg (argName 0)] "ADD:64" [.reg (argName 0), .imm 1], MemTag.reg none)
  , (LinstrR.Lopn [.reg nReg] "SUB:64" [.reg nReg, .imm 1], MemTag.reg none) ]

/-- Every emitted coupled-body element is an `Lopn`. -/
theorem ladderBodyM_isLopn (w : Nat) (nReg : String) :
    ∀ i ∈ ladderBodyM w nReg, IsLopn i := by
  intro i hi
  simp only [ladderBodyM, List.mem_cons] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact ⟨_, _, _, rfl⟩
  · exact absurd h (List.not_mem_nil)

/-! ## 4. The coupled per-trip pass, DISCHARGED unconditionally -/

/-- **The proved per-trip coupled pass.** One pass of the emitted coupled body,
    from ANY state agreeing with the trip-`t` valuation and holding a readable
    counter: it succeeds, the accumulator pair steps by
    `JLoopBodyN.stepC (ladderUpdate w)`, and the counter decrements. NO encoded-
    state hypothesis. -/
theorem ladderBodyM_trip {w : Nat} (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (t : Nat) (arrt : Fin 2 → BitVec w) (bt : LstateM)
    (hagree : StoreAgreesM 2 2 bt
      (tripValArrMN (invTys := []) .nil t arrt))
    (vn : BitVec 64) (hn : bt.reg.getW nReg 64 = some vn) :
    ∃ bt', lsemStraightMem (ladderBodyM w nReg) bt = some bt'
      ∧ StoreAgreesM 2 2 bt'
          (tripValArrMN (invTys := []) .nil (t + 1)
            (JLoopBodyN.stepC (ladderUpdate w)
              (.nil : Ctxt.Valuation (d := jasminDialect) []) t arrt))
      ∧ bt'.reg.getW nReg 64 = some (vn - 1#64) := by
  -- abbreviations
  set lx : BitVec w := stackGet arrt (BitVec.ofNat 64 0).toNat with hlx
  set lz : BitVec w := stackGet arrt (BitVec.ofNat 64 1).toNat with hlz
  -- step 1: MOV i0 (regName 2) ← 0
  have h1 := lsemStepMem_movImm (regName 2) 0 bt
  set s1 := (bt.setReg (regName 2) (BitVec.ofNat 64 0)).nextPc with hs1
  have hAg1 : StoreAgreesM 2 2 s1 (tripValArrMN (invTys := []) .nil t arrt) :=
    StoreAgreesM.nextPc (StoreAgreesM.setReg_scratch (curDepth := 2) rfl 2 (by omega) (BitVec.ofNat 64 0) hagree)
  -- step 2: LOADIDX rx (regName 4) ← acc[i0]
  have hacc1 : s1.getArr (argName 1) w 2 = some arrt :=
    tripAgree_getArr_acc (invTys := []) hAg1
  have hi01 : s1.reg.getW (regName 2) 64 = some (BitVec.ofNat 64 0) := by
    rw [hs1]; exact LstateM.getW_setReg_nextPc_same bt (regName 2) (BitVec.ofNat 64 0)
  have h2 := lsemStepMem_loadIdx (regName 4) (argName 1) (regName 2) (w / 8)
    arrt (BitVec.ofNat 64 0) s1 hacc1 hi01
  set s2 := (s1.setReg (regName 4) lx).nextPc with hs2
  have hAg2 : StoreAgreesM 2 2 s2 (tripValArrMN (invTys := []) .nil t arrt) :=
    StoreAgreesM.nextPc (StoreAgreesM.setReg_scratch (curDepth := 2) rfl 4 (by omega) lx hAg1)
  -- step 3: MOV i1 (regName 3) ← 1
  have h3 := lsemStepMem_movImm (regName 3) 1 s2
  set s3 := (s2.setReg (regName 3) (BitVec.ofNat 64 1)).nextPc with hs3
  have hAg3 : StoreAgreesM 2 2 s3 (tripValArrMN (invTys := []) .nil t arrt) :=
    StoreAgreesM.nextPc (StoreAgreesM.setReg_scratch (curDepth := 2) rfl 3 (by omega) (BitVec.ofNat 64 1) hAg2)
  -- step 4: LOADIDX rz (regName 5) ← acc[i1]
  have hacc3 : s3.getArr (argName 1) w 2 = some arrt :=
    tripAgree_getArr_acc (invTys := []) hAg3
  have hi13 : s3.reg.getW (regName 3) 64 = some (BitVec.ofNat 64 1) := by
    rw [hs3]; exact LstateM.getW_setReg_nextPc_same s2 (regName 3) (BitVec.ofNat 64 1)
  have h4 := lsemStepMem_loadIdx (regName 5) (argName 1) (regName 3) (w / 8)
    arrt (BitVec.ofNat 64 1) s3 hacc3 hi13
  set s4 := (s3.setReg (regName 5) lz).nextPc with hs4
  have hAg4 : StoreAgreesM 2 2 s4 (tripValArrMN (invTys := []) .nil t arrt) :=
    StoreAgreesM.nextPc (StoreAgreesM.setReg_scratch (curDepth := 2) rfl 5 (by omega) lz hAg3)
  -- reads of the buffered cells off s4
  have hrx4 : s4.reg.getW (regName 4) w = some lx := by
    rw [hs4, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (regName_ne (by omega)),
      hs3, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (regName_ne (by omega)),
      hs2, LstateM.getW_setReg_nextPc_same]
  have hrz4 : s4.reg.getW (regName 5) w = some lz := by
    rw [hs4, LstateM.getW_setReg_nextPc_same]
  -- step 5: ADD rx2 (regName 6) ← rx, rz  (= lx + lz)
  have h5 := lsemStepMem_add64Reg (regName 6) (regName 4) (regName 5) lx lz s4 hrx4 hrz4
  set s5 := (s4.setReg (regName 6) (lx + lz)).nextPc with hs5
  have hAg5 : StoreAgreesM 2 2 s5 (tripValArrMN (invTys := []) .nil t arrt) :=
    StoreAgreesM.nextPc (StoreAgreesM.setReg_scratch (curDepth := 2) rfl 6 (by omega) (lx + lz) hAg4)
  have hrx5 : s5.reg.getW (regName 4) w = some lx := by
    rw [hs5, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (regName_ne (by omega)), hrx4]
  have hrz5 : s5.reg.getW (regName 5) w = some lz := by
    rw [hs5, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (regName_ne (by omega)), hrz4]
  -- step 6: SUB rz2 (regName 7) ← rx, rz  (= lx - lz)
  have h6 := lsemStepMem_sub64Reg (regName 7) (regName 4) (regName 5) lx lz s5 hrx5 hrz5
  set s6 := (s5.setReg (regName 7) (lx - lz)).nextPc with hs6
  have hAg6 : StoreAgreesM 2 2 s6 (tripValArrMN (invTys := []) .nil t arrt) :=
    StoreAgreesM.nextPc (StoreAgreesM.setReg_scratch (curDepth := 2) rfl 7 (by omega) (lx - lz) hAg5)
  -- step 7: MOV j0 (regName 8) ← 0
  have h7 := lsemStepMem_movImm (regName 8) 0 s6
  set s7 := (s6.setReg (regName 8) (BitVec.ofNat 64 0)).nextPc with hs7
  have hAg7 : StoreAgreesM 2 2 s7 (tripValArrMN (invTys := []) .nil t arrt) :=
    StoreAgreesM.nextPc (StoreAgreesM.setReg_scratch (curDepth := 2) rfl 8 (by omega) (BitVec.ofNat 64 0) hAg6)
  -- step 8: STOREIDX acc[j0] := rx2
  have hacc7 : s7.getArr (argName 1) w 2 = some arrt :=
    tripAgree_getArr_acc (invTys := []) hAg7
  have hj07 : s7.reg.getW (regName 8) 64 = some (BitVec.ofNat 64 0) := by
    rw [hs7]; exact LstateM.getW_setReg_nextPc_same s6 (regName 8) (BitVec.ofNat 64 0)
  have hrx27 : s7.reg.getW (regName 6) w = some (lx + lz) := by
    rw [hs7, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (regName_ne (by omega)),
      hs6, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (regName_ne (by omega)),
      hs5, LstateM.getW_setReg_nextPc_same]
  have h8 := lsemStepMem_storeIdx (argName 1) (argName 1) (regName 8) (regName 6)
    (w / 8) arrt (BitVec.ofNat 64 0) (lx + lz) s7 hacc7 hj07 hrx27
  set na1 : Fin 2 → BitVec w := stackSet arrt (BitVec.ofNat 64 0).toNat (lx + lz) with hna1
  set s8 := (s7.setArr (argName 1) na1).nextPc with hs8
  have hAg8 : StoreAgreesM 2 2 s8 (tripValArrMN (invTys := []) .nil t na1) :=
    StoreAgreesM.nextPc (tripAgree_setArr_acc (invTys := []) hAg7 na1)
  -- step 9: MOV j1 (regName 9) ← 1
  have h9 := lsemStepMem_movImm (regName 9) 1 s8
  set s9 := (s8.setReg (regName 9) (BitVec.ofNat 64 1)).nextPc with hs9
  have hAg9 : StoreAgreesM 2 2 s9 (tripValArrMN (invTys := []) .nil t na1) :=
    StoreAgreesM.nextPc (StoreAgreesM.setReg_scratch (curDepth := 2) rfl 9 (by omega) (BitVec.ofNat 64 1) hAg8)
  -- step 10: STOREIDX acc[j1] := rz2
  have hacc9 : s9.getArr (argName 1) w 2 = some na1 :=
    tripAgree_getArr_acc (invTys := []) hAg9
  have hj19 : s9.reg.getW (regName 9) 64 = some (BitVec.ofNat 64 1) := by
    rw [hs9]; exact LstateM.getW_setReg_nextPc_same s8 (regName 9) (BitVec.ofNat 64 1)
  have hrz29 : s9.reg.getW (regName 7) w = some (lx - lz) := by
    rw [hs9, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (regName_ne (by omega)),
      hs8, LstateM.getW_setArr_nextPc,
      hs7, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (regName_ne (by omega)),
      hs6, LstateM.getW_setReg_nextPc_same]
  have h10 := lsemStepMem_storeIdx (argName 1) (argName 1) (regName 9) (regName 7)
    (w / 8) na1 (BitVec.ofNat 64 1) (lx - lz) s9 hacc9 hj19 hrz29
  set na2 : Fin 2 → BitVec w := stackSet na1 (BitVec.ofNat 64 1).toNat (lx - lz) with hna2
  set s10 := (s9.setArr (argName 1) na2).nextPc with hs10
  have hAg10 : StoreAgreesM 2 2 s10 (tripValArrMN (invTys := []) .nil t na2) :=
    StoreAgreesM.nextPc (tripAgree_setArr_acc (invTys := []) hAg9 na2)
  -- step 11: ADD idx ← idx, #1
  have hidx10 : s10.reg.getW (argName 0) 64 = some (BitVec.ofNat 64 t) :=
    tripAgree_getW_idx (invTys := []) hAg10
  have h11 := lsemStepMem_add64Imm (argName 0) (argName 0) 1 (BitVec.ofNat 64 t) s10 hidx10
  rw [show BitVec.ofNat 64 t + BitVec.ofNat 64 1 = BitVec.ofNat 64 (t + 1) from by
    rw [BitVec.ofNat_add]] at h11
  set s11 := (s10.setReg (argName 0) (BitVec.ofNat 64 (t + 1))).nextPc with hs11
  have hAg11 : StoreAgreesM 2 2 s11 (tripValArrMN (invTys := []) .nil (t + 1) na2) :=
    StoreAgreesM.nextPc (tripAgree_setReg_idx (invTys := []) hAg10 (BitVec.ofNat 64 (t + 1)))
  -- step 12: SUB n ← n, #1
  have hn11 : s11.reg.getW nReg 64 = some vn := by
    rw [hs11, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (hna 0),
      hs10, LstateM.getW_setArr_nextPc,
      hs9, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (hnr 9),
      hs8, LstateM.getW_setArr_nextPc,
      hs7, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (hnr 8),
      hs6, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (hnr 7),
      hs5, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (hnr 6),
      hs4, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (hnr 5),
      hs3, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (hnr 3),
      hs2, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (hnr 4),
      hs1, LstateM.getW_setReg_nextPc_other _ _ _ _ _ (hnr 2)]
    exact hn
  have h12 := lsemStepMem_sub64Imm nReg nReg 1 vn s11 hn11
  set s12 := (s11.setReg nReg (vn - BitVec.ofNat 64 1)).nextPc with hs12
  refine ⟨s12, ?_, ?_, ?_⟩
  · rw [ladderBodyM, lsemStraightMem_cons_some h1, lsemStraightMem_cons_some h2,
      lsemStraightMem_cons_some h3, lsemStraightMem_cons_some h4,
      lsemStraightMem_cons_some h5, lsemStraightMem_cons_some h6,
      lsemStraightMem_cons_some h7, lsemStraightMem_cons_some h8,
      lsemStraightMem_cons_some h9, lsemStraightMem_cons_some h10,
      lsemStraightMem_cons_some h11, lsemStraightMem_cons_some h12,
      lsemStraightMem_nil]
  · rw [ladderUpdate_stepC]
    exact StoreAgreesM.nextPc
      (StoreAgreesM.setReg_untracked nReg (vn - BitVec.ofNat 64 1) hna hnr hAg11)
  · rw [hs12]
    exact LstateM.getW_setReg_nextPc_same s11 nReg (vn - BitVec.ofNat 64 1)

/-- **The coupled trip invariant** — every trip state agrees with the source
    fold of `ladderUpdate` at its trip valuation, with a readable counter. -/
theorem ladderBodyM_inv {w : Nat} (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s0 : LstateM) (arr0 : Fin 2 → BitVec w)
    (hseed : StoreAgreesM 2 2 s0 (tripValArrMN (invTys := []) .nil 0 arr0))
    (hn0 : (s0.reg.getW nReg 64).isSome) :
    ∀ t (bt : LstateM),
      runBoundedLoopMem (ladderBodyM w nReg) t s0 = some bt →
      StoreAgreesM 2 2 bt
          (tripValArrMN (invTys := []) .nil t
            (JLoopBodyN.denote ⟨t, ladderUpdate w⟩
              (.nil : Ctxt.Valuation (d := jasminDialect) []) arr0))
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
      cases hbk : runBoundedLoopMem (ladderBodyM w nReg) k s0 with
      | none => rw [hbk] at hbt; simp at hbt
      | some bk =>
          rw [hbk, Option.bind_some] at hbt
          obtain ⟨hAgk, hnk⟩ := ih bk hbk
          obtain ⟨vn, hvn⟩ := Option.isSome_iff_exists.mp hnk
          obtain ⟨bt', hbt', hAg', hn'⟩ := ladderBodyM_trip nReg hna hnr k _ bk hAgk vn hvn
          rw [hbt', Option.map_some] at hbt
          obtain rfl := Option.some.inj hbt
          refine ⟨?_, ?_⟩
          · rw [JLoopBodyN.denote_succ]
            exact StoreAgreesM.setLpc hAg' 1
          · rw [show ((bt'.setLpc 1).reg).getW nReg 64 = bt'.reg.getW nReg 64 from
              LstateN.getW_congr_lvm (LstateM.reg_lvm_setLpc bt' 1) nReg 64, hn']
            rfl

/-! ## 5. The coupled-loop export theorem, hsim-free, through the wide theorem -/

/-- **The coupled-loop export theorem, at the array cells, UNCONDITIONAL per-trip.**
    The emitted coupled ladder-step loop, run by the machine model from any seed
    agreeing with the trip-0 valuation, halts at a state whose accumulator pair
    `decodeCarrier`s to the source fold `JLoopBodyN.denote ⟨m, ladderUpdate w⟩`.
    Routed through the carrier-agnostic `loopWide_export_faithful_denote` at
    `accTy = .stackArr w 2`: only schedule/seed/name-hygiene hypotheses; the
    coupled per-trip simulation is discharged. -/
theorem ladderLoop_export_faithful_denote {w : Nat}
    (fn : String) (top : LLabel) (nReg : String)
    (hna : ∀ j, nReg ≠ argName j) (hnr : ∀ k, nReg ≠ regName k)
    (s : LstatePM) (hfn : s.lfn = fn) (hpc : s.base.lpc = 1)
    (arr0 : Fin 2 → BitVec w)
    (hseed : StoreAgreesM 2 2 s.base (tripValArrMN (invTys := []) .nil 0 arr0))
    (hn0 : (s.base.reg.getW nReg 64).isSome)
    (m : Nat) (hm : 0 < m) (bprev blast bfin : LstateM)
    (hprev : runBoundedLoopMem (ladderBodyM w nReg) (m - 1) s.base = some bprev)
    (hlast : lsemStraightMem (ladderBodyM w nReg) bprev = some blast)
    (hbfin : runBoundedLoopMem (ladderBodyM w nReg) m s.base = some bfin)
    (htaken : ∀ i, 0 < i → i < m → ∀ bi,
      runBoundedLoopMem (ladderBodyM w nReg) i s.base = some bi →
      condNZ bi (.reg nReg) = true)
    (hhalt : condNZ blast (.reg nReg) = false) :
    ∃ t : LstatePM,
      lsemFuelMemL (singletonProgM fn (loopLinstrRM top nReg (ladderBodyM w nReg)))
          (m * ((ladderBodyM w nReg).length + 1)) s = some t
        ∧ decodeCarrier (JasminTy.stackArr w 2) t.base (argName 1)
            = some (JLoopBodyN.denote ⟨m, ladderUpdate w⟩
                (.nil : Ctxt.Valuation (d := jasminDialect) []) arr0) := by
  have hinv := ladderBodyM_inv nReg hna hnr s.base arr0 hseed hn0
  refine loopWide_export_faithful_denote (invTys := []) (ladderUpdate w) .nil fn top nReg
    (ladderBodyM w nReg) (ladderBodyM_isLopn w nReg) s hfn hpc m hm bprev blast bfin
    hprev hlast hbfin htaken hhalt (argName 1) arr0 ?_ ?_
  · exact tripAgree_getArr_acc (invTys := []) hseed
  · intro t ht bt acct hbt hdec
    obtain ⟨hAgt, hnt⟩ := hinv t bt hbt
    obtain ⟨vn, hvn⟩ := Option.isSome_iff_exists.mp hnt
    have harrt : decodeCarrier (JasminTy.stackArr w 2) bt (argName 1)
        = some (JLoopBodyN.denote ⟨t, ladderUpdate w⟩
            (.nil : Ctxt.Valuation (d := jasminDialect) []) arr0) :=
      tripAgree_getArr_acc (invTys := []) hAgt
    rw [hdec] at harrt
    obtain rfl := Option.some.inj harrt
    obtain ⟨bt', hbt', hAg', _⟩ := ladderBodyM_trip nReg hna hnr t _ bt hAgt vn hvn
    exact ⟨bt', hbt', tripAgree_getArr_acc (invTys := []) hAg'⟩

/-! ## 6. Validation: the coupled loop at runtime count 3, hsim-free -/

/-- The initial pair `[9, 4]`. -/
def lInit : Fin 2 → BitVec 64 := ![9#64, 4#64]

/-- The emitted coupled body at `w = 64`, counter `"n"`. -/
def lBodyV : List LinstrRM := ladderBodyM 64 "n"

/-- The coupled-loop program. -/
def lProgV : LprogM := singletonProgM "f" (loopLinstrRM 0 "n" lBodyV)

/-- The seed base: encoded `[acc = lInit, i = 0]`, counter `n = 3`, pc at the
    loop top. -/
def lBaseV : LstateM :=
  (((encodeM (tripValArrMN (invTys := []) .nil 0 lInit)).setReg "n" (3#64)).setLpc 1)

/-- The seed program state. -/
def lStartV : LstatePM := { base := lBaseV, lfn := "f" }

/-- The coupled seed agrees with the trip-0 valuation. -/
theorem lBaseV_seed :
    StoreAgreesM 2 2 lBaseV (tripValArrMN (invTys := []) .nil 0 lInit) :=
  StoreAgreesM.setLpc
    (StoreAgreesM.setReg_untracked "n" (3#64) counterN_ne_argName counterN_ne_regName
      (encodeM_StoreAgreesM (tripValArrMN (invTys := []) .nil 0 lInit))) 1

theorem lT2_isSome : (runBoundedLoopMem lBodyV 2 lBaseV).isSome := by native_decide

/-- The trip-2 state. -/
def lT2 : LstateM := (runBoundedLoopMem lBodyV 2 lBaseV).get lT2_isSome

theorem lT2_eq : runBoundedLoopMem lBodyV 2 lBaseV = some lT2 :=
  (Option.some_get lT2_isSome).symm

theorem lT1_isSome : (runBoundedLoopMem lBodyV 1 lBaseV).isSome := by native_decide

/-- The trip-1 state. -/
def lT1 : LstateM := (runBoundedLoopMem lBodyV 1 lBaseV).get lT1_isSome

theorem lT1_eq : runBoundedLoopMem lBodyV 1 lBaseV = some lT1 :=
  (Option.some_get lT1_isSome).symm

theorem lLast_isSome : (lsemStraightMem lBodyV lT2).isSome := by native_decide

/-- The post-last-pass state. -/
def lLastV : LstateM := (lsemStraightMem lBodyV lT2).get lLast_isSome

theorem lLastV_eq : lsemStraightMem lBodyV lT2 = some lLastV :=
  (Option.some_get lLast_isSome).symm

theorem lFin_isSome : (runBoundedLoopMem lBodyV 3 lBaseV).isSome := by native_decide

/-- The 3-trip fold state. -/
def lFinV : LstateM := (runBoundedLoopMem lBodyV 3 lBaseV).get lFin_isSome

theorem lFinV_eq : runBoundedLoopMem lBodyV 3 lBaseV = some lFinV :=
  (Option.some_get lFin_isSome).symm

/-- **Validate.** The coupled differential-addition loop at runtime count 3,
    THROUGH the hsim-free carrier-agnostic export theorem: the machine run's
    halt state decodes AT THE `.stackArr 64 2` ACCUMULATOR to the source fold
    `JLoopBodyN.denote ⟨3, ladderUpdate 64⟩ [] lInit` — the coupled cells ARE
    the source denotation's pair output. -/
theorem ladderLoop_export_uncond :
    ∃ t : LstatePM,
      lsemFuelMemL lProgV (3 * (lBodyV.length + 1)) lStartV = some t
        ∧ decodeCarrier (JasminTy.stackArr 64 2) t.base (argName 1)
            = some (JLoopBodyN.denote ⟨3, ladderUpdate 64⟩
                (.nil : Ctxt.Valuation (d := jasminDialect) []) lInit) := by
  refine ladderLoop_export_faithful_denote "f" 0 "n" counterN_ne_argName
    counterN_ne_regName lStartV rfl rfl lInit lBaseV_seed (by native_decide)
    3 (by omega) lT2 lLastV lFinV lT2_eq lLastV_eq lFinV_eq ?_ (by native_decide)
  intro i h1 h2 bi hbi
  have hi : i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl
  · obtain rfl := Option.some.inj (lT1_eq.symm.trans hbi)
    native_decide
  · obtain rfl := Option.some.inj (lT2_eq.symm.trans hbi)
    native_decide

/-- **Validate (cells crosscheck).** The source fold's cells after 3 coupled
    steps of `x' = x+z, z' = x−z` from `[9, 4]`: `[9,4]→[13,5]→[18,8]→[26,10]`. -/
example :
    ((List.finRange 2).map (fun i =>
        (JLoopBodyN.denote ⟨3, ladderUpdate 64⟩
          (.nil : Ctxt.Valuation (d := jasminDialect) []) lInit i).toNat))
      = [26, 10] := by native_decide

/-- The machine run's accumulator cells equal the source fold's, read off the
    real `lsemFuelMemL` halt state (fuel/schedule non-vacuous). -/
example :
    (lsemFuelMemL lProgV (3 * (lBodyV.length + 1)) lStartV).map (fun t =>
        (decodeCarrier (JasminTy.stackArr 64 2) t.base (argName 1)).map (fun f =>
          (List.finRange 2).map (fun i => (f i).toNat)))
      = some (some [26, 10]) := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieWide
