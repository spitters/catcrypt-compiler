/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaCfg
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaCall
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaX86

/-!
# Segment tactics for the cut-point rule

The cut-point rule `IsaCfg.corresIsa_of_labels_floyd` asks, per cut point, for a run of at
most `B` steps to an exit or to a cut point. This module states that obligation as a
predicate on a position, `SegAt isa P B Q k m`: from the state `m` at counter `k`, at most
`B` steps of `P` reach a state satisfying `Q`. One lemma per kind of instruction reduces
`SegAt` at a counter to `SegAt` at the successor position with the bound decreased by one,
and the tactics apply the lemma of the instruction fetched at the counter.

The state after a step is a term over the state before it (`setBase`, `next`, `goto`), and
its registers and arrays are computed by `simp`. A step lemma of an instruction that reads
the state has the form `∃ x, p s x ∧ SegAt …`, in which `p s x` says that `x` is the value
read; `isa_pre` computes `x` from the hypotheses on the initial state.

## Tactics

* `isa_cutpoints Inv, μ, B, N at ls` applies `corresIsa_of_cuts` with the invariant family
  `Inv`, the measure `μ`, the step bound `B`, the bound `N` on the entry measure and the
  list `ls` of the labels that are cut points. It leaves the entry condition, the segment
  from the entry and one segment per label of `ls`, each a `SegAt` goal after the
  position and the invariant are introduced. `isa_cutpoints Inv, μ, B at ls` applies
  `corresIsaRun_of_cuts` to a `CorresIsaRun` goal, where the fuel is that of the initial
  state and no bound `N` is given.
* `isa_steps` runs the straight-line instructions at the counter, then one control
  instruction: a label or a jump ends the run, and a conditional jump on a register gives
  two goals, the taken branch at its label and the other branch run further by
  `isa_steps`. The condition of each branch is a hypothesis of its goal.
* `isa_exit` closes a segment at the end of the body and leaves the exit relation.
* `isa_cut l` closes a segment at the label `l` and leaves the invariant of `l` and the
  decrease of the measure.
* `isa_lopn` steps one straight-line instruction. It is extended by `macro_rules` with one
  rule per instruction shape, each `isa_lopnZero` to `isa_lopnThree` at the step lemma of the
  shape; `isa_opn_proof` proves such a step lemma for a register operation of `lsemStepN`.

The goals the tactics leave are closed by `simp` with the definitions of the relation and
the invariants and the hypotheses in context, followed by `bv_decide` or `bv_omega` on the
remaining word arithmetic. A measure that reads a register is stated through `wordNat`.

## Main results

* `SegAt`, `SegAt.done`, `SegAt.of_steps`, `SegAt.of_seg`: the segment predicate, its end
  and its composition with a run of one or of several steps.
* `SegAt.label`, `SegAt.goto`, `SegAt.cond`: the control instructions.
* `X86Steps`, `SegAt.lopnZero` to `SegAt.lopnThree`, `SegAt.condReg`: straight-line instructions
  and register conditions at `x86Isa` and `x86Isa.withCalls`.
* `shrI`, `addI`, `subI`, `negI`, `movI`, `storeI`, `loadI` with their steps
  `lsemStepMem_shrI` to `lsemStepMem_loadI`.
* `CutPost`, `corresIsa_of_cuts`, `lsemFuelMemF_of_cuts`, `corresIsaRun_of_cuts`: the
  cut-point rule over `SegAt` with a list of cut labels, at a fixed fuel, at the fuel of
  the initial state, and as `CorresIsaRun`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

namespace IsaCfg

open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCall
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (stackGet stackSet)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_step x86Isa_condEval)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (decC ccPol)

/-! ## States after a step -/

/-- The state `s` with its base replaced by `b`. -/
def setBase (s : LstateMF) (b : LstateM) : LstateMF := { s with prog := { s.prog with base := b } }

@[simp] theorem setBase_base (s : LstateMF) (b : LstateM) : (setBase s b).prog.base = b := rfl

@[simp] theorem setBase_lfn (s : LstateMF) (b : LstateM) :
    (setBase s b).prog.lfn = s.prog.lfn := rfl

@[simp] theorem next_base (s : LstateMF) : (next s).prog.base = s.prog.base.nextPc := rfl

@[simp] theorem next_lfn (s : LstateMF) : (next s).prog.lfn = s.prog.lfn := rfl

@[simp] theorem goto_lvm (s : LstateMF) (k : Nat) :
    (goto s k).prog.base.reg.lvm = s.prog.base.reg.lvm := rfl

@[simp] theorem goto_lpc (s : LstateMF) (k : Nat) : (goto s k).prog.base.lpc = k := rfl

@[simp] theorem goto_lfn (s : LstateMF) (k : Nat) : (goto s k).prog.lfn = s.prog.lfn := rfl

@[simp] theorem getArr_withALUFlags (i : LinstrRM) (s0 s1 : LstateM) (r : String) (w n : Nat) :
    (withALUFlags i s0 s1).getArr r w n = s1.getArr r w n := by
  unfold LstateM.getArr; rw [withALUFlags_larr]

@[simp] theorem singletonProgM_lfn (fn : String) (body : List LinstrRM) :
    (singletonProgM fn body).lfn = fn := rfl

/-- The word of a register value as a natural number. A measure stated through `wordNat`
    is computed by `simp` once the register value is. -/
def wordNat (p : Σ w, BitVec w) : Nat := p.2.toNat

@[simp] theorem wordNat_mk (w : Nat) (v : BitVec w) : wordNat ⟨w, v⟩ = v.toNat := rfl

/-- A register holding a value of width `w` reads at width `w`. -/
theorem getW_of_lvm (s : LstateN) (r : String) {w : Nat} (v : BitVec w)
    (h : s.lvm r = ⟨w, v⟩) : s.getW r w = some v := by
  unfold LstateN.getW
  rw [h]
  simp

/-- The read of a register depends on the value of that register only. -/
theorem getW_congr {s s' : LstateN} {r : String} (w : Nat) (h : s.lvm r = s'.lvm r) :
    s.getW r w = s'.getW r w := by
  unfold LstateN.getW
  rw [h]

/-! ## Steps of `x86Isa` -/

/-- The `x86Isa` step of an `Lopn` instruction `i` that is neither the flag compare nor a
    register copy, where `lsemStepMem` steps the base to `b`: the state with base `b` and
    the flags `i` writes. -/
theorem x86_step_mem (P : LprogM) {s : LstateMF} {i : LinstrRM} {b : LstateM} (hl : IsLopn i)
    (hc : cmpArgs? i = none) (hm : movRegArgs? i = none)
    (h : lsemStepMem i s.prog.base = some b) :
    x86Isa.step P i s = some (setBase s (withALUFlags i s.prog.base b)) := by
  rw [x86Isa_step, evalInstrPMemF_lopn P i s hl hc hm, stepMemF_of_lsemStepMem h]
  rfl

/-- **One straight-line step at `x86Isa`.** At counter `k` holding an `Lopn` instruction
    `i` that is neither the flag compare nor a register copy, a step `lsemStepMem` of `i`
    on the base to `b` is one step of the program to the state with base `b` and the flags
    `i` writes, at counter `k + 1`. -/
theorem x86_steps_mem {P : LprogM} {k : Nat} {s : LstateMF} {i : LinstrRM} {b : LstateM}
    (hat : atPc P k s) (hi : P.body[k]? = some i) (hl : IsLopn i)
    (hc : cmpArgs? i = none) (hm : movRegArgs? i = none)
    (h : lsemStepMem i s.prog.base = some b) :
    Steps x86Isa P 1 s (setBase s (withALUFlags i s.prog.base b)) ∧
      atPc P (k + 1) (setBase s (withALUFlags i s.prog.base b)) := by
  refine ⟨Steps.one ?_, hat.1, ?_⟩
  · rw [lsemStepPMemF_of_atPc x86Isa hat hi, x86Isa_step, evalInstrPMemF_lopn P i s hl hc hm,
      stepMemF_of_lsemStepMem h]
    rfl
  · rw [setBase_base, withALUFlags_lpc, lsemStepMem_lpc_succ i _ b h, hat.2]

/-- The step of an `Lopn` instruction that is neither the flag compare nor a register
    copy stays in the function and advances the counter by one. -/
theorem x86_step_lopn_pc (P : LprogM) (i : LinstrRM) (hl : IsLopn i)
    (hc : cmpArgs? i = none) (hm : movRegArgs? i = none) (u u' : LstateMF)
    (h : x86Isa.step P i u = some u') :
    u'.prog.lfn = u.prog.lfn ∧ u'.prog.base.lpc = u.prog.base.lpc + 1 := by
  rw [x86Isa_step, evalInstrPMemF_lopn P i u hl hc hm] at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨rfl, stepMemF_lpc_succ i _ b hb⟩

/-- A conditional on a register that is not a condition-code name tests the register for
    non-zero at width `64`. -/
theorem x86_condEval_reg (s : LstateMF) (r : String) (v : BitVec 64)
    (hr : ccPol (.reg r) = none) (h : s.prog.base.reg.lvm r = ⟨64, v⟩) :
    x86Isa.condEval s (.reg r) = decide (v ≠ 0#64) := by
  rw [x86Isa_condEval]
  unfold decC
  rw [hr]
  simp only [condNZ, evalOperandN, getW_of_lvm _ r v h]

/-! ## Instructions and their steps -/

/-- `d := a >>> k` at width `64`. -/
def shrI (d a : String) (k : Nat) : LinstrRM :=
  (.Lopn [.reg d] "SHR:64" [.reg a, .imm k], .reg none)

/-- `d := a + k` at width `64`. -/
def addI (d a : String) (k : Nat) : LinstrRM :=
  (.Lopn [.reg d] "ADD:64" [.reg a, .imm k], .reg none)

/-- `d := a - k` at width `64`. -/
def subI (d a : String) (k : Nat) : LinstrRM :=
  (.Lopn [.reg d] "SUB:64" [.reg a, .imm k], .reg none)

/-- `d := -a` at width `64`. -/
def negI (d a : String) : LinstrRM := (.Lopn [.reg d] "NEG:64" [.reg a], .reg none)

/-- `d := k` at width `64`. -/
def movI (d : String) (k : Nat) : LinstrRM := (.Lopn [.reg d] "MOV:64" [.imm k], .reg none)

/-- `d := base` with the word at index `idx` set to `val`, for an array of `n` words. -/
def storeI (n : Nat) (d base idx val : String) : LinstrRM :=
  (.Lopn [.reg d] "STOREIDX" [.arrIdx base idx 8, .reg val], .store 64 n)

/-- `d := base[idx]`, for an array of `n` words. -/
def loadI (n : Nat) (d base idx : String) : LinstrRM :=
  (.Lopn [.reg d] "LOADIDX" [.arrIdx base idx 8], .load 64 n)

theorem stripWidthTag_shr64 : stripWidthTag "SHR:64" = "SHR" := by decide

theorem stripWidthTag_add64 : stripWidthTag "ADD:64" = "ADD" := by decide

theorem stripWidthTag_sub64 : stripWidthTag "SUB:64" = "SUB" := by decide

theorem stripWidthTag_neg64 : stripWidthTag "NEG:64" = "NEG" := by decide

theorem stripWidthTag_mov64 : stripWidthTag "MOV:64" = "MOV" := by decide

/-- `isa_opn_proof I` proves a step equation `lsemStepMem (I …) s = some …` for an
    instruction `I` that is a register operation of `lsemStepN` at width `64` with the
    mnemonic `SHR`, `ADD`, `SUB`, `NEG` or `MOV`, from the hypotheses on the registers it
    reads. -/
macro "isa_opn_proof " i:ident : tactic => `(tactic|
  (rw [$i:ident, lsemStepMem_reg, JasminLsemCast.lsemStepCast_of_delegate _ _ (Or.inr rfl),
     JasminLsemMulCarry.lsemStepMC_of_delegate _ _ rfl rfl rfl rfl rfl,
     JasminLsemShift.lsemStepSh_of_not_sar _ _ rfl]
   simp [lsemStepN, readReg, evalOperandN, applyOpnN, stripWidthTag_shr64, stripWidthTag_add64,
     stripWidthTag_sub64, stripWidthTag_neg64, stripWidthTag_mov64, *]
   rfl))

theorem lsemStepMem_shrI (d a : String) (k : Nat) (s : LstateM) (va : BitVec 64)
    (h : s.reg.lvm a = ⟨64, va⟩) :
    lsemStepMem (shrI d a k) s =
      some (s.setReg d (va >>> shiftMask 64 (BitVec.ofNat 64 k).toNat)).nextPc := by
  isa_opn_proof shrI

theorem lsemStepMem_addI (d a : String) (k : Nat) (s : LstateM) (va : BitVec 64)
    (h : s.reg.lvm a = ⟨64, va⟩) :
    lsemStepMem (addI d a k) s = some (s.setReg d (va + BitVec.ofNat 64 k)).nextPc := by
  isa_opn_proof addI

theorem lsemStepMem_subI (d a : String) (k : Nat) (s : LstateM) (va : BitVec 64)
    (h : s.reg.lvm a = ⟨64, va⟩) :
    lsemStepMem (subI d a k) s = some (s.setReg d (va - BitVec.ofNat 64 k)).nextPc := by
  isa_opn_proof subI

theorem lsemStepMem_negI (d a : String) (s : LstateM) (va : BitVec 64)
    (h : s.reg.lvm a = ⟨64, va⟩) :
    lsemStepMem (negI d a) s = some (s.setReg d (0 - va)).nextPc := by
  isa_opn_proof negI

theorem lsemStepMem_movI (d : String) (k : Nat) (s : LstateM) :
    lsemStepMem (movI d k) s = some (s.setReg d (BitVec.ofNat 64 k)).nextPc := by
  isa_opn_proof movI

theorem lsemStepMem_storeI (n : Nat) (d base idx val : String) (s : LstateM)
    (arr : Fin n → BitVec 64) (vi vv : BitVec 64) (ha : s.getArr base 64 n = some arr)
    (hi : s.reg.lvm idx = ⟨64, vi⟩) (hv : s.reg.lvm val = ⟨64, vv⟩) :
    lsemStepMem (storeI n d base idx val) s =
      some (s.setArr d (stackSet arr vi.toNat vv)).nextPc := by
  simp [storeI, lsemStepMem, storeStruct?, ha, getW_of_lvm _ idx vi hi, getW_of_lvm _ val vv hv]

theorem lsemStepMem_loadI (n : Nat) (d base idx : String) (s : LstateM)
    (arr : Fin n → BitVec 64) (vi : BitVec 64) (ha : s.getArr base 64 n = some arr)
    (hi : s.reg.lvm idx = ⟨64, vi⟩) :
    lsemStepMem (loadI n d base idx) s = some (s.setReg d (stackGet arr vi.toNat)).nextPc := by
  simp [loadI, lsemStepMem, loadStruct?, ha, getW_of_lvm _ idx vi hi]

/-! ## The segment predicate -/

/-- **A segment from a position.** From the state `m` at counter `k` in the function of
    `P`, a run of at most `B` steps reaches a state satisfying `Q`. -/
def SegAt (isa : Isa) (P : LprogM) (B : Nat) (Q : LstateMF → Prop) (k : Nat) (m : LstateMF) :
    Prop :=
  atPc P k m → ∃ n m', n ≤ B ∧ Steps isa P n m m' ∧ Q m'

section Seg

variable {isa : Isa} {P : LprogM} {B : Nat} {Q : LstateMF → Prop} {k : Nat} {m : LstateMF}

/-- A segment ends at a state satisfying `Q`. -/
theorem SegAt.done (h : atPc P k m → Q m) : SegAt isa P B Q k m :=
  fun hat => ⟨0, m, Nat.zero_le _, Steps.refl isa P m, h hat⟩

/-- One step to the counter `k'`, then a segment from `k'`. -/
theorem SegAt.of_steps {k' : Nat} {m1 : LstateMF}
    (h1 : atPc P k m → Steps isa P 1 m m1 ∧ atPc P k' m1) (h : SegAt isa P B Q k' m1) :
    SegAt isa P (B + 1) Q k m := by
  intro hat
  obtain ⟨hs, hat1⟩ := h1 hat
  obtain ⟨n, m', hn, hs', hQ⟩ := h hat1
  exact ⟨1 + n, m', by omega, hs.trans hs', hQ⟩

/-- A run of at most `b` steps to the counter `k'` in a state satisfying `R`, then a
    segment from every such state. The run of a call site by `IsaCall.steps_call` has this
    form. -/
theorem SegAt.of_seg {k' b : Nat} {R : LstateMF → Prop}
    (h1 : atPc P k m → ∃ n m1, n ≤ b ∧ Steps isa P n m m1 ∧ atPc P k' m1 ∧ R m1)
    (h : ∀ m1, atPc P k' m1 → R m1 → SegAt isa P B Q k' m1) : SegAt isa P (B + b) Q k m := by
  intro hat
  obtain ⟨n1, m1, hn1, hs, hat1, hR⟩ := h1 hat
  obtain ⟨n, m', hn, hs', hQ⟩ := h m1 hat1 hR hat1
  exact ⟨n1 + n, m', by omega, hs.trans hs', hQ⟩

/-- A segment as the run the cut-point rule asks for. -/
theorem SegAt.run (h : SegAt isa P B Q k m) (hat : atPc P k m) :
    ∃ n m', n ≤ B ∧ Steps isa P n m m' ∧ Q m' :=
  h hat

/-- A label is one step to the next counter. -/
theorem SegAt.label {kind : LabelKind} {l : LLabel} {tag : MemTag}
    (hi : P.body[k]? = some (.Llabel kind l, tag)) (h : SegAt isa P B Q (k + 1) (next m)) :
    SegAt isa P (B + 1) Q k m :=
  SegAt.of_steps (fun hat => steps_label isa hat hi) h

/-- A goto within the function of `P` is one step to the counter after its label. -/
theorem SegAt.goto {q : Nat} {l : LLabel} {tag : MemTag}
    (hi : P.body[k]? = some (.Lgoto (P.lfn, l), tag)) (hl : findLabelMem l P.body = some q)
    (h : SegAt isa P B Q (q + 1) (IsaCfg.goto m (q + 1))) : SegAt isa P (B + 1) Q k m :=
  SegAt.of_steps (fun hat => ⟨(steps_goto isa hat hi hl).1, atPc_goto (q + 1) hat⟩) h

/-- A conditional jump is one step, to the counter after its label when the condition
    holds and to the next counter otherwise. -/
theorem SegAt.cond {q : Nat} {c : LOperand} {l : LLabel} {tag : MemTag}
    (hi : P.body[k]? = some (.Lcond c l, tag)) (hl : findLabelMem l P.body = some q)
    (ht : isa.condEval m c = true → SegAt isa P B Q (q + 1) (IsaCfg.goto m (q + 1)))
    (hf : isa.condEval m c = false → SegAt isa P B Q (k + 1) (next m)) :
    SegAt isa P (B + 1) Q k m := by
  cases hc : isa.condEval m c
  · exact SegAt.of_steps (fun hat => steps_cond_not_taken isa hat hi hc) (hf hc)
  · exact SegAt.of_steps
      (fun hat => ⟨(steps_cond_taken isa hat hi hc hl).1, atPc_goto (q + 1) hat⟩) (ht hc)

end Seg

/-! ## Segments at the x86 instruction set -/

/-- **An instruction set that steps as `x86Isa`** on straight-line instructions and on
    register conditions: an `Lopn` instruction that is neither the flag compare nor a
    register copy steps by `lsemStepMem` with the flags it writes, and a conditional on a
    register that is not a condition-code name tests the register for non-zero. -/
class X86Steps (isa : Isa) : Prop where
  /-- The step of a straight-line instruction. -/
  lopn : ∀ {P : LprogM} {k : Nat} {s : LstateMF} {i : LinstrRM} {b : LstateM},
    atPc P k s → P.body[k]? = some i → IsLopn i → cmpArgs? i = none → movRegArgs? i = none →
    lsemStepMem i s.prog.base = some b →
    Steps isa P 1 s (setBase s (withALUFlags i s.prog.base b)) ∧
      atPc P (k + 1) (setBase s (withALUFlags i s.prog.base b))
  /-- The value of a register condition. -/
  condReg : ∀ (s : LstateMF) (r : String) (v : BitVec 64), ccPol (.reg r) = none →
    s.prog.base.reg.lvm r = ⟨64, v⟩ → isa.condEval s (.reg r) = decide (v ≠ 0#64)

instance : X86Steps x86Isa := ⟨x86_steps_mem, x86_condEval_reg⟩

instance : X86Steps x86Isa.withCalls :=
  ⟨fun hat hi hl hc hm h =>
      ⟨steps_one_of_not_call x86Isa hat hi (isCall_of_isLopn hl) (x86_step_mem _ hl hc hm h),
        (x86_steps_mem hat hi hl hc hm h).2⟩,
    x86_condEval_reg⟩

section X86

variable {isa : Isa} [X86Steps isa] {P : LprogM} {B : Nat} {Q : LstateMF → Prop} {k : Nat}
  {m : LstateMF} {i : LinstrRM}

/-- A straight-line instruction whose step reads nothing. -/
theorem SegAt.lopnZero {f : LstateM → LstateM} (hstep : ∀ s, lsemStepMem i s = some (f s))
    (hi : P.body[k]? = some i) (hl : IsLopn i) (hc : cmpArgs? i = none)
    (hm : movRegArgs? i = none)
    (h : SegAt isa P B Q (k + 1) (setBase m (withALUFlags i m.prog.base (f m.prog.base)))) :
    SegAt isa P (B + 1) Q k m :=
  SegAt.of_steps (fun hat => X86Steps.lopn hat hi hl hc hm (hstep _)) h

/-- A straight-line instruction whose step reads one value `x`, described by `p`. -/
theorem SegAt.lopnOne {X : Type} {p : LstateM → X → Prop} {f : LstateM → X → LstateM}
    (hstep : ∀ s x, p s x → lsemStepMem i s = some (f s x))
    (hi : P.body[k]? = some i) (hl : IsLopn i) (hc : cmpArgs? i = none)
    (hm : movRegArgs? i = none)
    (h : ∃ x, p m.prog.base x ∧
      SegAt isa P B Q (k + 1) (setBase m (withALUFlags i m.prog.base (f m.prog.base x)))) :
    SegAt isa P (B + 1) Q k m := by
  obtain ⟨x, hp, h⟩ := h
  exact SegAt.of_steps (fun hat => X86Steps.lopn hat hi hl hc hm (hstep _ x hp)) h

/-- A straight-line instruction whose step reads two values. -/
theorem SegAt.lopnTwo {X Y : Type} {p : LstateM → X → Prop} {p' : LstateM → Y → Prop}
    {f : LstateM → X → Y → LstateM}
    (hstep : ∀ s x y, p s x → p' s y → lsemStepMem i s = some (f s x y))
    (hi : P.body[k]? = some i) (hl : IsLopn i) (hc : cmpArgs? i = none)
    (hm : movRegArgs? i = none)
    (h : ∃ x y, p m.prog.base x ∧ p' m.prog.base y ∧
      SegAt isa P B Q (k + 1) (setBase m (withALUFlags i m.prog.base (f m.prog.base x y)))) :
    SegAt isa P (B + 1) Q k m := by
  obtain ⟨x, y, hp, hp', h⟩ := h
  exact SegAt.of_steps (fun hat => X86Steps.lopn hat hi hl hc hm (hstep _ x y hp hp')) h

/-- A straight-line instruction whose step reads three values. -/
theorem SegAt.lopnThree {X Y Z : Type} {p : LstateM → X → Prop} {p' : LstateM → Y → Prop}
    {p'' : LstateM → Z → Prop} {f : LstateM → X → Y → Z → LstateM}
    (hstep : ∀ s x y z, p s x → p' s y → p'' s z → lsemStepMem i s = some (f s x y z))
    (hi : P.body[k]? = some i) (hl : IsLopn i) (hc : cmpArgs? i = none)
    (hm : movRegArgs? i = none)
    (h : ∃ x y z, p m.prog.base x ∧ p' m.prog.base y ∧ p'' m.prog.base z ∧
      SegAt isa P B Q (k + 1) (setBase m (withALUFlags i m.prog.base (f m.prog.base x y z)))) :
    SegAt isa P (B + 1) Q k m := by
  obtain ⟨x, y, z, hp, hp', hp'', h⟩ := h
  exact SegAt.of_steps
    (fun hat => X86Steps.lopn hat hi hl hc hm (hstep _ x y z hp hp' hp'')) h

/-- A conditional jump on a register holding the word `v`: the taken branch under
    `v ≠ 0` and the other branch under `v = 0`. -/
theorem SegAt.condReg {q : Nat} {r : String} {l : LLabel} {tag : MemTag}
    (hi : P.body[k]? = some (.Lcond (.reg r) l, tag)) (hr : ccPol (.reg r) = none)
    (hl : findLabelMem l P.body = some q)
    (h : ∃ v : BitVec 64, m.prog.base.reg.lvm r = ⟨64, v⟩ ∧
      (v ≠ 0#64 → SegAt isa P B Q (q + 1) (IsaCfg.goto m (q + 1))) ∧
      (v = 0#64 → SegAt isa P B Q (k + 1) (next m))) :
    SegAt isa P (B + 1) Q k m := by
  obtain ⟨v, hv, ht, hf⟩ := h
  have hc := X86Steps.condReg (isa := isa) m r v hr hv
  refine SegAt.cond hi hl (fun h => ht ?_) (fun h => hf ?_)
  · rw [hc] at h; simpa using h
  · rw [hc] at h; simpa using h

end X86

/-! ## The cut-point rule over segments -/

section Rule

variable {A : Type}

/-- **The end of a segment of the cut-point rule**, from the cut point `c` in the state
    `m`: the state `m'` is halted and related to `fa a`, or it is at a label of `ls` whose
    invariant holds at a measure below that of `c` at `m`. -/
def CutPost (P : LprogM) (SR : LstateMF → A → Prop) (fa : A → A)
    (Inv : Option LLabel → LstateMF → A → Prop) (μ : Option LLabel → LstateMF → A → Nat)
    (ls : List LLabel) (c : Option LLabel) (m : LstateMF) (a : A) (m' : LstateMF) : Prop :=
  (Halted P m' ∧ SR m' (fa a)) ∨
    ∃ l ∈ ls, atLabel P l m' ∧ Inv (some l) m' a ∧ μ (some l) m' a < μ c m a

variable {P : LprogM} {SR : LstateMF → A → Prop} {fa : A → A}
  {Inv : Option LLabel → LstateMF → A → Prop} {μ : Option LLabel → LstateMF → A → Nat}
  {ls : List LLabel} {c : Option LLabel} {m : LstateMF} {a : A} {m' : LstateMF} {k : Nat}

/-- A state at or past the end of the body that is related to `fa a` ends a segment. -/
theorem CutPost.exit (hat : atPc P k m') (hk : P.body.length ≤ k)
    (h : SR m' (fa a)) : CutPost P SR fa Inv μ ls c m a m' :=
  Or.inl ⟨halted_of_atPc hat hk, h⟩

/-- A state at the counter after the label `l` of `ls` that satisfies the invariant of
    `l` at a smaller measure ends a segment. -/
theorem CutPost.cut (l : LLabel) {q : Nat} (hl : l ∈ ls)
    (hq : findLabelMem l P.body = some q) (hat : atPc P (q + 1) m')
    (h : Inv (some l) m' a ∧ μ (some l) m' a < μ c m a) :
    CutPost P SR fa Inv μ ls c m a m' :=
  Or.inr ⟨l, hl, ⟨q, hq, hat⟩, h.1, h.2⟩

/-- The segment condition of `corresIsa_of_labels_floyd` from one segment per cut point,
    for the invariants restricted to the entry and the labels of `ls`. -/
theorem seg_of_cuts (isa : Isa) (P : LprogM) (SR : LstateMF → A → Prop) (fa : A → A)
    (Inv : Option LLabel → LstateMF → A → Prop) (μ : Option LLabel → LstateMF → A → Nat)
    (ls : List LLabel) (B : Nat)
    (h0 : ∀ m a, atPc P 0 m → Inv none m a →
      SegAt isa P B (CutPost P SR fa Inv μ ls none m a) 0 m)
    (hl : ∀ l ∈ ls, ∃ q, findLabelMem l P.body = some q ∧
      ∀ m a, atPc P (q + 1) m → Inv (some l) m a →
      SegAt isa P B (CutPost P SR fa Inv μ ls (some l) m a) (q + 1) m)
    (c : Option LLabel) (m : LstateMF) (a : A) (hat : atCut P c m)
    (hI : Inv c m a ∧ ∀ l, c = some l → l ∈ ls) :
    ∃ n m', n ≤ B ∧ Steps isa P n m m' ∧
      ((Halted P m' ∧ SR m' (fa a)) ∨ ∃ c', atCut P c' m' ∧
        (Inv c' m' a ∧ ∀ l, c' = some l → l ∈ ls) ∧ μ c' m' a < μ c m a) := by
  obtain ⟨hI, hc⟩ := hI
  have key : ∀ m', CutPost P SR fa Inv μ ls c m a m' →
      ((Halted P m' ∧ SR m' (fa a)) ∨ ∃ c', atCut P c' m' ∧
        (Inv c' m' a ∧ ∀ l, c' = some l → l ∈ ls) ∧ μ c' m' a < μ c m a) := by
    rintro m' (h | ⟨l, hl, hat', hI', hμ⟩)
    · exact Or.inl h
    · exact Or.inr ⟨some l, hat', ⟨hI', fun l' e => by cases e; exact hl⟩, hμ⟩
  cases c with
  | none =>
      obtain ⟨n, m', hn, hs, hQ⟩ := h0 m a hat hI hat
      exact ⟨n, m', hn, hs, key m' hQ⟩
  | some l =>
      obtain ⟨q, hq, h⟩ := hl l (hc l rfl)
      obtain ⟨q', hq', hat⟩ := hat
      obtain rfl : q' = q := Option.some.inj (hq'.symm.trans hq)
      obtain ⟨n, m', hn, hs, hQ⟩ := h m a hat hI hat
      exact ⟨n, m', hn, hs, key m' hQ⟩

/-- **`CorresIsa` from one segment per cut point.** `corresIsa_of_labels_floyd` with the
    cut points the entry and the labels of the list `ls`: the entry condition (`hentry`),
    the segment from the entry at counter `0` (`h0`), and for each label of `ls` its
    landing counter and the segment from it (`hl`). Each segment ends by `CutPost`. -/
theorem corresIsa_of_cuts (isa : Isa) (P : LprogM) (SR : LstateMF → A → Prop)
    (Pre : A → Prop) (fa : A → A) (Inv : Option LLabel → LstateMF → A → Prop)
    (μ : Option LLabel → LstateMF → A → Nat) (ls : List LLabel) (B N : Nat)
    (hentry : ∀ m a, SR m a → Pre a → atPc P 0 m ∧ Inv none m a ∧ μ none m a ≤ N)
    (h0 : ∀ m a, atPc P 0 m → Inv none m a →
      SegAt isa P B (CutPost P SR fa Inv μ ls none m a) 0 m)
    (hl : ∀ l ∈ ls, ∃ q, findLabelMem l P.body = some q ∧
      ∀ m a, atPc P (q + 1) m → Inv (some l) m a →
      SegAt isa P B (CutPost P SR fa Inv μ ls (some l) m a) (q + 1) m) :
    CorresIsa isa P SR Pre fa (B * (N + 1)) :=
  corresIsa_of_labels_floyd isa P SR Pre fa
    (fun c m a => Inv c m a ∧ ∀ l, c = some l → l ∈ ls) μ B N
    (fun m a hSR hPre =>
      ⟨(hentry m a hSR hPre).1, ⟨(hentry m a hSR hPre).2.1, fun _ e => nomatch e⟩,
        (hentry m a hSR hPre).2.2⟩)
    (seg_of_cuts isa P SR fa Inv μ ls B h0 hl)

/-- **The run from one segment per cut point, with the fuel of the initial state.**
    `lsemFuelMemF_of_labels_floyd` with the cut points the entry and the labels of `ls`. -/
theorem lsemFuelMemF_of_cuts (isa : Isa) (P : LprogM) (SR : LstateMF → A → Prop)
    (Pre : A → Prop) (fa : A → A) (Inv : Option LLabel → LstateMF → A → Prop)
    (μ : Option LLabel → LstateMF → A → Nat) (ls : List LLabel) (B : Nat)
    (hentry : ∀ m a, SR m a → Pre a → atPc P 0 m ∧ Inv none m a)
    (h0 : ∀ m a, atPc P 0 m → Inv none m a →
      SegAt isa P B (CutPost P SR fa Inv μ ls none m a) 0 m)
    (hl : ∀ l ∈ ls, ∃ q, findLabelMem l P.body = some q ∧
      ∀ m a, atPc P (q + 1) m → Inv (some l) m a →
      SegAt isa P B (CutPost P SR fa Inv μ ls (some l) m a) (q + 1) m)
    (m : LstateMF) (a : A) (hSR : SR m a) (hPre : Pre a) :
    ∃ t, isa.lsemFuelMemF P (B * (μ none m a + 1)) m = some t ∧ SR t (fa a) :=
  lsemFuelMemF_of_labels_floyd isa P SR Pre fa
    (fun c m a => Inv c m a ∧ ∀ l, c = some l → l ∈ ls) μ B
    (fun m a hSR hPre =>
      ⟨(hentry m a hSR hPre).1, (hentry m a hSR hPre).2, fun _ e => nomatch e⟩)
    (seg_of_cuts isa P SR fa Inv μ ls B h0 hl) m a hSR hPre

/-- **`CorresIsaRun` from one segment per cut point**: `lsemFuelMemF_of_cuts` with the fuel
    quantified. -/
theorem corresIsaRun_of_cuts (isa : Isa) (P : LprogM) (SR : LstateMF → A → Prop)
    (Pre : A → Prop) (fa : A → A) (Inv : Option LLabel → LstateMF → A → Prop)
    (μ : Option LLabel → LstateMF → A → Nat) (ls : List LLabel) (B : Nat)
    (hentry : ∀ m a, SR m a → Pre a → atPc P 0 m ∧ Inv none m a)
    (h0 : ∀ m a, atPc P 0 m → Inv none m a →
      SegAt isa P B (CutPost P SR fa Inv μ ls none m a) 0 m)
    (hl : ∀ l ∈ ls, ∃ q, findLabelMem l P.body = some q ∧
      ∀ m a, atPc P (q + 1) m → Inv (some l) m a →
      SegAt isa P B (CutPost P SR fa Inv μ ls (some l) m a) (q + 1) m) :
    CorresIsaRun isa P SR Pre fa := fun m a hSR hPre =>
  ⟨_, lsemFuelMemF_of_cuts isa P SR Pre fa Inv μ ls B hentry h0 hl m a hSR hPre⟩

end Rule

/-! ## Tactics -/

/-- `isa_pre` computes the values an instruction reads: it simplifies a goal
    `∃ x, p s x ∧ …`, in which `p s x` equates a register or an array of the state term `s`
    with `x`, using the hypotheses on the initial state. -/
macro "isa_pre" : tactic => `(tactic| simp [*])

/-- `isa_lopn` steps the straight-line instruction at the counter of a `SegAt` goal. Each
    instruction shape has one `macro_rules` rule, which applies `SegAt.lopnZero` to
    `SegAt.lopnThree` to the step lemma of the shape. -/
syntax "isa_lopn" : tactic

/-- `isa_lopnZero h` steps the instruction at the counter by the step lemma `h`, which reads
    no value of the state. -/
macro "isa_lopnZero " h:term : tactic =>
  `(tactic| refine SegAt.lopnZero $h rfl ⟨_, _, _, rfl⟩ rfl rfl ?_)

/-- `isa_lopnOne h` steps the instruction at the counter by the step lemma `h`, which reads
    one value of the state. -/
macro "isa_lopnOne " h:term : tactic =>
  `(tactic| (refine SegAt.lopnOne $h rfl ⟨_, _, _, rfl⟩ rfl rfl ?_; isa_pre))

/-- `isa_lopnTwo h` steps the instruction at the counter by the step lemma `h`, which reads
    two values of the state. -/
macro "isa_lopnTwo " h:term : tactic =>
  `(tactic| (refine SegAt.lopnTwo $h rfl ⟨_, _, _, rfl⟩ rfl rfl ?_; isa_pre))

/-- `isa_lopnThree h` steps the instruction at the counter by the step lemma `h`, which reads
    three values of the state. -/
macro "isa_lopnThree " h:term : tactic =>
  `(tactic| (refine SegAt.lopnThree $h rfl ⟨_, _, _, rfl⟩ rfl rfl ?_; isa_pre))

macro_rules
  | `(tactic| isa_lopn) => `(tactic| isa_lopnZero (lsemStepMem_movI _ _))
macro_rules
  | `(tactic| isa_lopn) => `(tactic| isa_lopnOne (lsemStepMem_shrI _ _ _))
macro_rules
  | `(tactic| isa_lopn) => `(tactic| isa_lopnOne (lsemStepMem_addI _ _ _))
macro_rules
  | `(tactic| isa_lopn) => `(tactic| isa_lopnOne (lsemStepMem_subI _ _ _))
macro_rules
  | `(tactic| isa_lopn) => `(tactic| isa_lopnOne (lsemStepMem_negI _ _))
macro_rules
  | `(tactic| isa_lopn) => `(tactic| isa_lopnTwo (lsemStepMem_loadI _ _ _ _))
macro_rules
  | `(tactic| isa_lopn) => `(tactic| isa_lopnThree (lsemStepMem_storeI _ _ _ _ _))

/-- `isa_steps` runs a `SegAt` goal forward: the straight-line instructions at the
    counter, then one label, one goto, or one conditional jump on a register. A conditional
    jump gives the goal of the taken branch, at its label, and the goal of the other
    branch, run further by `isa_steps`; the condition is a hypothesis of each. -/
syntax "isa_steps" : tactic

macro_rules | `(tactic| isa_steps) => `(tactic|
  (repeat isa_lopn
   first
   | refine SegAt.label rfl ?_
   | refine SegAt.goto rfl rfl ?_
   | (refine SegAt.condReg rfl rfl rfl ?_
      isa_pre
      refine ⟨fun _ => ?_, fun _ => ?_⟩
      on_goal 2 => isa_steps)
   | skip))

/-- `isa_exit` ends a `SegAt` goal of the cut-point rule at the end of the body. It leaves
    the exit relation `SR m' (fa a)`. -/
macro "isa_exit" : tactic => `(tactic|
  refine SegAt.done fun hat => CutPost.exit hat (by first | exact Nat.le_refl _ | decide) ?_)

/-- `isa_cut l` ends a `SegAt` goal of the cut-point rule at the counter after the label
    `l`. It leaves the invariant of `l` and the decrease of the measure. -/
macro "isa_cut " l:term : tactic => `(tactic|
  refine SegAt.done fun hat => CutPost.cut $l (by decide) rfl hat ⟨?_, ?_⟩)

/-- `isa_cutpoints Inv, μ, B, N at ls` applies `corresIsa_of_cuts`, and
    `isa_cutpoints Inv, μ, B at ls` applies `corresIsaRun_of_cuts`. The goals are the entry
    condition, the segment from the entry, and one segment per label of `ls`. -/
syntax "isa_cutpoints " term ", " term ", " term (", " term)? " at " term : tactic

macro_rules
  | `(tactic| isa_cutpoints $inv, $mu, $b, $n at $ls) => `(tactic|
      (refine corresIsa_of_cuts _ _ _ _ _ $inv $mu $ls $b $n ?_ ?_ ?_
       on_goal 3 =>
         repeat' first
           | exact fun _ h => absurd h List.not_mem_nil
           | refine List.forall_mem_cons.2 ⟨⟨_, rfl, ?_⟩, ?_⟩))
  | `(tactic| isa_cutpoints $inv, $mu, $b at $ls) => `(tactic|
      (refine corresIsaRun_of_cuts _ _ _ _ _ $inv $mu $ls $b ?_ ?_ ?_
       on_goal 3 =>
         repeat' first
           | exact fun _ h => absurd h List.not_mem_nil
           | refine List.forall_mem_cons.2 ⟨⟨_, rfl, ?_⟩, ?_⟩))

end IsaCfg

end CatCrypt.Crypto.SecureCompilation.Ascent
