/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

@[expose] public section

set_option autoImplicit false

/-!
# The step of an instruction-set subset over `LstateMF`

An instruction set other than x86 runs the `Lprog` instructions of its alphabet with the
reference semantics of the memref machine and refuses every other instruction. `subsetStep`
is that step: the control step `ctlStep` under the instruction set's branch condition on a
control instruction, an instruction-set arm `ext` (for example a compare that writes the
zero flag), and otherwise, on an instruction of the alphabet, the core step `coreStep`. The
core step is the register copy of `movRegArgs?` and the memref step `evalInstrPMemL` of
`JasminLsemMemLoop`; it writes none of the flags `zf`, `cf`, `of`.

The alphabet is a list of mnemonic bases (`mnemOk`): an `Lopn` is in it when the base of its
mnemonic (`stripWidthTag`) is in the list.

`RegRel regs s get` relates the register file of an `LstateMF` to the register file `get` of
a machine on the registers `regs`: each holds the 64-bit value `get r`. The register step
lemmas `coreStep_binop` and `coreStep_mov` are the two arms of the core step an
instruction-selection simulation needs, and `RegRel_setReg` is their effect on the relation.

## Main results

* `coreStep`, `mnemOk`, `subsetStep`, `subsetStep_ctl`: the step and its control obligation.
* `subsetStep_refuse`: an instruction outside the alphabet has no step.
* `coreStep_binop`, `coreStep_mov`: the register arithmetic and the register copy.
* `RegRel`, `RegRel_setReg`: the register relation and its update.
* `coreStep_loadIdx`, `coreStep_storeIdx`, `coreStep_binopImm`: the array load and store and
  the register-immediate arithmetic.
* `coreStep_loadC`, `coreStep_storeC`: the compile-time-offset load and store of the word
  memory `lmem`.
* `Frame`, `FrameM`, `FrameX`, `IdxBound`: the frames of a register step, of a memory step and
  of a step that writes the flags, and the index bound of an array access, shared by the
  instruction-selection simulations.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard

/-- **The core step**: the register copy of `movRegArgs?` (the destination takes the stored
    value of the source at its stored width), and otherwise the memref step
    `evalInstrPMemL`. The flags are unchanged. -/
def coreStep (P : LprogM) (i : LinstrRM) (s : LstateMF) : Option LstateMF :=
  match movRegArgs? i with
  | some (dst, src) =>
      match readReg s.prog.base.reg (.reg src) with
      | some ⟨_, v⟩ =>
          some { s with prog := { s.prog with base := (s.prog.base.setReg dst v).nextPc } }
      | none => none
  | none => (evalInstrPMemL P i s.prog).map (fun p => { s with prog := p })

/-- An instruction is in the alphabet `bases` when it is an `Lopn` whose mnemonic base is in
    the list. -/
def mnemOk (bases : List String) : LinstrR → Bool
  | .Lopn _ opn _ => bases.contains (stripWidthTag opn)
  | _ => false

/-- **The step of an instruction-set subset**: the control step under `cond` on a control
    instruction; on an instruction of the alphabet `bases`, the arm `ext` when it claims the
    instruction (`some r`) and the core step otherwise; no step on any other instruction. -/
def subsetStep (bases : List String) (cond : LstateMF → LOperand → Bool)
    (ext : LinstrRM → LstateMF → Option (Option LstateMF))
    (P : LprogM) (i : LinstrRM) (s : LstateMF) : Option LstateMF :=
  if isCtl i.fst then ctlStep cond P i s
  else if mnemOk bases i.fst then
    match ext i s with
    | some r => r
    | none => coreStep P i s
  else none

/-- The step of a subset on a control instruction is the shared control step. -/
theorem subsetStep_ctl (bases : List String) (cond : LstateMF → LOperand → Bool)
    (ext : LinstrRM → LstateMF → Option (Option LstateMF))
    (P : LprogM) (i : LinstrRM) (s : LstateMF) (h : isCtl i.fst = true) :
    subsetStep bases cond ext P i s = ctlStep cond P i s := by
  simp [subsetStep, h]

/-- **An `Lopn` outside the alphabet has no step.** -/
theorem subsetStep_refuse (bases : List String) (cond : LstateMF → LOperand → Bool)
    (ext : LinstrRM → LstateMF → Option (Option LstateMF))
    (P : LprogM) (dsts : List LOperand) (opn : String) (srcs : List LOperand) (tag : MemTag)
    (s : LstateMF) (h : bases.contains (stripWidthTag opn) = false) :
    subsetStep bases cond ext P (.Lopn dsts opn srcs, tag) s = none := by
  simp only [subsetStep, isCtl, mnemOk, h, Bool.false_eq_true, if_false]

/-- **The core step of a 64-bit register arithmetic instruction** `d := a ⊙ b` with a
    register first source: the destination takes the value of the operation. -/
theorem coreStep_binop (P : LprogM) (bop : JasminBinOp) (d a b : String) (s : LstateMF)
    (va vb : BitVec 64) (hva : s.prog.base.reg.getW a 64 = some va)
    (hvb : s.prog.base.reg.getW b 64 = some vb) :
    coreStep P (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .reg b], .reg none) s
      = some { s with prog := { s.prog with
          base := (s.prog.base.setReg d (bop.apply va vb)).nextPc } } := by
  have hstrip := stripWidthTag_withWidthTag_binOpName' 64 bop
  have hm : mulhiStruct? (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .reg b])
      = none := by
    simp only [mulhiStruct?, hstrip]; cases bop <;> rfl
  have hs : sarStruct? (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .reg b])
      = none := rfl
  have hstep : lsemStepMem
      (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .reg b], .reg none) s.prog.base
      = some ((s.prog.base.setReg d (bop.apply va vb)).nextPc) := by
    rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ hm rfl rfl rfl rfl, lsemStepSh_of_not_sar _ _ hs]
    simp only [lsemStepN, readReg_of_getW hva, evalOperandN, hvb, hstrip,
      applyOpnN_binOpName, Option.map_some]
    rfl
  unfold coreStep
  have hmov : movRegArgs?
      (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .reg b], MemTag.reg none)
      = none := rfl
  rw [hmov, evalInstrPMemL_lopn P _ s.prog ⟨_, _, _, rfl⟩, hstep]
  rfl

/-- **The core step of a 64-bit register copy** `d := a`: the destination takes the stored
    value of the source. -/
theorem coreStep_mov (P : LprogM) (d a : String) (tag : MemTag) (s : LstateMF)
    (v : BitVec 64) (hv : s.prog.base.reg.lvm a = ⟨64, v⟩) :
    coreStep P (.Lopn [.reg d] (withWidthTag 64 "MOV") [.reg a], tag) s
      = some { s with prog := { s.prog with base := (s.prog.base.setReg d v).nextPc } } := by
  have hmov : movRegArgs? (.Lopn [.reg d] (withWidthTag 64 "MOV") [.reg a], tag)
      = some (d, a) := by
    simp only [movRegArgs?]
    rw [if_pos (by decide +kernel)]
  unfold coreStep
  rw [hmov]
  simp only [readReg, hv]

/-- **The register relation**: on each register of `regs`, the register file of the
    `LstateMF` holds the 64-bit value `get r`. -/
def RegRel (regs : List String) (s : LstateMF) (get : String → BitVec 64) : Prop :=
  ∀ r ∈ regs, s.prog.base.reg.lvm r = ⟨64, get r⟩

/-- A related register reads at width 64. -/
theorem RegRel.getW {regs : List String} {s : LstateMF} {get : String → BitVec 64}
    (h : RegRel regs s get) {r : String} (hr : r ∈ regs) :
    s.prog.base.reg.getW r 64 = some (get r) :=
  getW_eq_some_iff.mpr (h r hr)

/-- **The register relation after a write**: writing `v` to `d` on the `LstateMF` and on the
    machine (`get'` reads `v` at `d` and `get` elsewhere) preserves the relation. -/
theorem RegRel_setReg {regs : List String} {s : LstateMF} {get get' : String → BitVec 64}
    (h : RegRel regs s get) (d : String) (v : BitVec 64)
    (hget : ∀ r ∈ regs, get' r = if r = d then v else get r) :
    RegRel regs { s with prog := { s.prog with base := (s.prog.base.setReg d v).nextPc } }
      get' := by
  intro r hr
  simp only [LstateM.reg_nextPc, LstateN.lvm_nextPc, LstateM.reg_setReg, LstateN.lvm_setReg,
    hget r hr]
  split
  · rfl
  · exact h r hr

/-! ## The memory arms of the core step -/

/-- An array cell of shape `(64, n)` reads back at that shape. -/
theorem getArr_of_larr {s : LstateM} {base : String} {n : Nat} {arr : Fin n → BitVec 64}
    (h : s.larr base = ⟨64, n, arr⟩) : s.getArr base 64 n = some arr := by
  unfold LstateM.getArr
  rw [h]
  simp

/-- **The core step of an array load** `d := base[idx]` at width 64: the destination takes
    the element `stackGet arr idx` of the array. -/
theorem coreStep_loadIdx (P : LprogM) (d base idx : String) (sc n : Nat) (s : LstateMF)
    (arr : Fin n → BitVec 64) (vi : BitVec 64) (harr : s.prog.base.larr base = ⟨64, n, arr⟩)
    (hvi : s.prog.base.reg.getW idx 64 = some vi) :
    coreStep P (.Lopn [.reg d] "LOADIDX" [.arrIdx base idx sc], .load 64 n) s
      = some { s with prog := { s.prog with
          base := (s.prog.base.setReg d (stackGet arr vi.toNat)).nextPc } } := by
  have hga : s.prog.base.getArr base 64 n = some arr := getArr_of_larr harr
  unfold coreStep
  have hmov : movRegArgs? (.Lopn [.reg d] "LOADIDX" [.arrIdx base idx sc], MemTag.load 64 n)
      = none := rfl
  rw [hmov, evalInstrPMemL_lopn P _ s.prog ⟨_, _, _, rfl⟩]
  simp only [lsemStepMem, loadStruct?, if_true, hga, hvi, Option.map_some]

/-- **The core step of an array store** `base[idx] := v` at width 64: the array takes the
    update `stackSet arr idx v`. -/
theorem coreStep_storeIdx (P : LprogM) (base idx v : String) (sc n : Nat) (s : LstateMF)
    (arr : Fin n → BitVec 64) (vi vv : BitVec 64) (harr : s.prog.base.larr base = ⟨64, n, arr⟩)
    (hvi : s.prog.base.reg.getW idx 64 = some vi) (hvv : s.prog.base.reg.getW v 64 = some vv) :
    coreStep P (.Lopn [.reg base] "STOREIDX" [.arrIdx base idx sc, .reg v], .store 64 n) s
      = some { s with prog := { s.prog with
          base := (s.prog.base.setArr base (stackSet arr vi.toNat vv)).nextPc } } := by
  have hga : s.prog.base.getArr base 64 n = some arr := getArr_of_larr harr
  unfold coreStep
  have hmov : movRegArgs? (.Lopn [.reg base] "STOREIDX" [.arrIdx base idx sc, .reg v],
      MemTag.store 64 n) = none := rfl
  rw [hmov, evalInstrPMemL_lopn P _ s.prog ⟨_, _, _, rfl⟩]
  simp only [lsemStepMem, storeStruct?, if_true, hga, hvi, hvv, Option.map_some]

/-- **The core step of a 64-bit register-immediate arithmetic instruction** `d := a ⊙ k`: the
    destination takes the value of the operation on the immediate `k` at width 64. -/
theorem coreStep_binopImm (P : LprogM) (bop : JasminBinOp) (d a : String) (k : Nat)
    (s : LstateMF) (va : BitVec 64) (hsar : binOpName bop ≠ "SAR")
    (hva : s.prog.base.reg.getW a 64 = some va) :
    coreStep P (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .imm k], .reg none) s
      = some { s with prog := { s.prog with
          base := (s.prog.base.setReg d (bop.apply va (BitVec.ofNat 64 k))).nextPc } } := by
  have hstrip := stripWidthTag_withWidthTag_binOpName' 64 bop
  have hm : mulhiStruct? (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .imm k])
      = none := by
    simp only [mulhiStruct?]
  have hs : sarStruct? (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .imm k])
      = none := by
    simp only [sarStruct?, hstrip, if_neg hsar]
  have hstep : lsemStepMem
      (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .imm k], .reg none) s.prog.base
      = some ((s.prog.base.setReg d (bop.apply va (BitVec.ofNat 64 k))).nextPc) := by
    rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ hm rfl rfl rfl rfl, lsemStepSh_of_not_sar _ _ hs]
    simp only [lsemStepN, readReg_of_getW hva, evalOperandN, hstrip,
      applyOpnN_binOpName, Option.map_some]
    rfl
  unfold coreStep
  have hmov : movRegArgs?
      (.Lopn [.reg d] (withWidthTag 64 (binOpName bop)) [.reg a, .imm k], MemTag.reg none)
      = none := rfl
  rw [hmov, evalInstrPMemL_lopn P _ s.prog ⟨_, _, _, rfl⟩, hstep]
  rfl

/-- **The core step of a compile-time-offset load** `d := lmem p off` (`MOVQ`, tag `.loadC`). -/
theorem coreStep_loadC (P : LprogM) (d p : String) (off : Nat) (s : LstateMF) :
    coreStep P (.Lopn [.reg d] "MOVQ" [.arr p off], .loadC) s
      = some { s with prog := { s.prog with
          base := (s.prog.base.setReg d (s.prog.base.lmem p (Int.ofNat off))).nextPc } } := by
  unfold coreStep
  have hmov : movRegArgs? (.Lopn [.reg d] "MOVQ" [.arr p off], MemTag.loadC) = none := rfl
  rw [hmov, evalInstrPMemL_lopn P _ s.prog ⟨_, _, _, rfl⟩]
  simp only [lsemStepMem, loadCStruct?, if_true, Option.map_some]

/-- **The core step of a compile-time-offset store** `lmem p off := v` (`MOVQ`, tag
    `.storeC`). -/
theorem coreStep_storeC (P : LprogM) (p v : String) (off : Nat) (s : LstateMF) (vv : BitVec 64)
    (hvv : s.prog.base.reg.getW v 64 = some vv) :
    coreStep P (.Lopn [.arr p off] "MOVQ" [.reg v], .storeC) s
      = some { s with prog := { s.prog with
          base := (s.prog.base.storeMemC p (Int.ofNat off) vv).nextPc } } := by
  unfold coreStep
  have hmov : movRegArgs? (.Lopn [.arr p off] "MOVQ" [.reg v], MemTag.storeC) = none := rfl
  rw [hmov, evalInstrPMemL_lopn P _ s.prog ⟨_, _, _, rfl⟩]
  simp only [lsemStepMem, storeCStruct?, if_true, hvv, Option.map_some]

/-- On an in-range index the update `stackSet` changes that cell only. -/
theorem stackSet_eq_of_lt {w n : Nat} (arr : Fin n → BitVec w) (k : Nat) (hk : k < n)
    (v : BitVec w) : stackSet arr k v = fun j => if j.val = k then v else arr j := by
  cases n with
  | zero => omega
  | succ m =>
      funext j
      simp only [stackSet, Fin.ext_iff, Nat.mod_eq_of_lt hk]

/-- A name on which `contains` is `false` is not in the list. -/
theorem not_mem_of_contains_false {l : List String} {a : String} (h : l.contains a = false) :
    a ∉ l := fun hm => by rw [List.contains_iff_mem.mpr hm] at h; cases h

/-! ## Frames and index bounds -/

/-- The frame of a register step: the zero flag, the function, the arrays, the word memory
    and the carry and overflow flags are unchanged and the counter advances by `n`. -/
def Frame (n : Nat) (s s' : LstateMF) : Prop :=
  s'.zf = s.zf ∧ s'.prog.lfn = s.prog.lfn ∧ s'.prog.base.larr = s.prog.base.larr
    ∧ s'.prog.base.lmem = s.prog.base.lmem ∧ s'.prog.base.cf = s.prog.base.cf
    ∧ s'.prog.base.of = s.prog.base.of ∧ s'.prog.base.reg.lpc = s.prog.base.reg.lpc + n

/-- The frame of a step of a memory fragment: the zero flag, the function, the word memory
    and the carry and overflow flags are unchanged and the counter advances by `n`. -/
def FrameM (n : Nat) (s s' : LstateMF) : Prop :=
  s'.zf = s.zf ∧ s'.prog.lfn = s.prog.lfn ∧ s'.prog.base.lmem = s.prog.base.lmem
    ∧ s'.prog.base.cf = s.prog.base.cf ∧ s'.prog.base.of = s.prog.base.of
    ∧ s'.prog.base.reg.lpc = s.prog.base.reg.lpc + n

/-- The frame of a step that may write the flags, the arrays and the word memory: the
    function and the overflow flag are unchanged and the counter advances by `n`. -/
def FrameX (n : Nat) (s s' : LstateMF) : Prop :=
  s'.prog.lfn = s.prog.lfn ∧ s'.prog.base.of = s.prog.base.of
    ∧ s'.prog.base.reg.lpc = s.prog.base.reg.lpc + n

/-- **The index bound** of an instruction under the register values `g`: the index of an
    array load or store is below the size of its array. -/
def IdxBound (sz : String → Nat) (i : LinstrRM) (g : String → BitVec 64) : Prop :=
  (∀ d base idx, loadStruct? i.1 = some (d, base, idx) → (g idx).toNat < sz base) ∧
  (∀ d base idx v, storeStruct? i.1 = some (d, base, idx, v) → (g idx).toNat < sz base)

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
