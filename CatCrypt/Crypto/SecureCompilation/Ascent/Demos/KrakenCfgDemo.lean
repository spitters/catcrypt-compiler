/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaCfg
public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaX86

/-!
# Three control-flow examples at the x86 instruction set

Three `Lprog` programs over `x86Isa`, each with a pure specification, proved by the
cut-point rule `IsaCfg.corresIsa_of_labels_floyd` of `Ascent.CorresIsaCfg`. They follow the
x64 examples `Cond`, `Alias` and `P3` of the Kraken verified-assembly framework.

* `condProg` computes the absolute value of the register `x`: the sign bit is shifted into
  `t`, a conditional jump on `t` selects the negation. Its cut points are the entry and the
  label of the negation block.
* `aliasProg` writes `u` to `a[i]` and `v` to `a[j]` and reads `a[i]` into `r`, for an array
  `a` of `n` words and in-range indices `i` and `j`. The read value is `v` when `i = j` and
  `u` otherwise. It is one straight-line segment, run by `IsaCfg.steps_of_runL_halted`.
* `loopProg` multiplies the register `n` by three with a loop of three blocks (head, body,
  exit) that adds `3` to `r` and decrements `n` until `n` is zero. Its cut points are the
  entry and the loop head, with the invariant `r = 3 * (n₀ - n)` and the measure `n`.

The machine flags restrict the conditions: the flag compare of the flag machine records
equality only, and a conditional jump on a register tests it for non-zero, so the examples
branch on a register.

The side relation of each example pins the program counter to a component of the abstract
state, since `CorresM` has one relation before and after the run. The theorems `cond_run`,
`alias_run` and `loop_run` restate each correspondence on a machine state.

## Main results

* `x86_steps_mem`, `x86_condEval_reg`: one step of a straight-line instruction and the
  value of a register condition at `x86Isa`.
* `cond_corresIsa`, `cond_run`: the absolute value.
* `alias_corresIsa`, `alias_run`: two stores through possibly equal indices.
* `loop_corresIsa`, `loop_run`: the multiplication loop.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.KrakenCfgDemo

open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
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

/-! ## Steps of `x86Isa` -/

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

/-- A register holding a value of width `w` reads at width `w`. -/
theorem getW_of_lvm (s : LstateN) (r : String) {w : Nat} (v : BitVec w)
    (h : s.lvm r = ⟨w, v⟩) : s.getW r w = some v := by
  unfold LstateN.getW
  rw [h]
  simp

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

/-! ## Instructions -/

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

theorem lsemStepMem_shrI (d a : String) (k : Nat) (s : LstateM) (va : BitVec 64)
    (h : s.reg.lvm a = ⟨64, va⟩) :
    lsemStepMem (shrI d a k) s =
      some (s.setReg d (va >>> (BitVec.ofNat 64 k).toNat)).nextPc := by
  rw [shrI, lsemStepMem_reg, JasminLsemCast.lsemStepCast_of_delegate _ _ (Or.inr rfl),
    JasminLsemMulCarry.lsemStepMC_of_delegate _ _ rfl rfl rfl rfl rfl,
    JasminLsemShift.lsemStepSh_of_not_sar _ _ rfl]
  simp [lsemStepN, readReg, h, evalOperandN,
    show stripWidthTag "SHR:64" = "SHR" from by decide, applyOpnN]
  rfl

theorem lsemStepMem_addI (d a : String) (k : Nat) (s : LstateM) (va : BitVec 64)
    (h : s.reg.lvm a = ⟨64, va⟩) :
    lsemStepMem (addI d a k) s = some (s.setReg d (va + BitVec.ofNat 64 k)).nextPc := by
  rw [addI, lsemStepMem_reg, JasminLsemCast.lsemStepCast_of_delegate _ _ (Or.inr rfl),
    JasminLsemMulCarry.lsemStepMC_of_delegate _ _ rfl rfl rfl rfl rfl,
    JasminLsemShift.lsemStepSh_of_not_sar _ _ rfl]
  simp [lsemStepN, readReg, h, evalOperandN,
    show stripWidthTag "ADD:64" = "ADD" from by decide, applyOpnN]
  rfl

theorem lsemStepMem_subI (d a : String) (k : Nat) (s : LstateM) (va : BitVec 64)
    (h : s.reg.lvm a = ⟨64, va⟩) :
    lsemStepMem (subI d a k) s = some (s.setReg d (va - BitVec.ofNat 64 k)).nextPc := by
  rw [subI, lsemStepMem_reg, JasminLsemCast.lsemStepCast_of_delegate _ _ (Or.inr rfl),
    JasminLsemMulCarry.lsemStepMC_of_delegate _ _ rfl rfl rfl rfl rfl,
    JasminLsemShift.lsemStepSh_of_not_sar _ _ rfl]
  simp [lsemStepN, readReg, h, evalOperandN,
    show stripWidthTag "SUB:64" = "SUB" from by decide, applyOpnN]
  rfl

theorem lsemStepMem_negI (d a : String) (s : LstateM) (va : BitVec 64)
    (h : s.reg.lvm a = ⟨64, va⟩) :
    lsemStepMem (negI d a) s = some (s.setReg d (0 - va)).nextPc := by
  rw [negI, lsemStepMem_reg, JasminLsemCast.lsemStepCast_of_delegate _ _ (Or.inr rfl),
    JasminLsemMulCarry.lsemStepMC_of_delegate _ _ rfl rfl rfl rfl rfl,
    JasminLsemShift.lsemStepSh_of_not_sar _ _ rfl]
  simp [lsemStepN, readReg, h,
    show stripWidthTag "NEG:64" = "NEG" from by decide, applyOpnN]
  rfl

theorem lsemStepMem_movI (d : String) (k : Nat) (s : LstateM) :
    lsemStepMem (movI d k) s = some (s.setReg d (BitVec.ofNat 64 k)).nextPc := by
  rw [movI, lsemStepMem_reg, JasminLsemCast.lsemStepCast_of_delegate _ _ (Or.inr rfl),
    JasminLsemMulCarry.lsemStepMC_of_delegate _ _ rfl rfl rfl rfl rfl,
    JasminLsemShift.lsemStepSh_of_not_sar _ _ rfl]
  simp [lsemStepN, show stripWidthTag "MOV:64" = "MOV" from by decide]
  rfl

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

/-! ## `Cond`: the absolute value by a conditional jump -/

/-- The absolute value of `x`: `t := x >>> 63`; when `t` is non-zero jump to label `1`,
    which negates `x`; otherwise jump to the end, label `2`. -/
def condProg (fn : String) : LprogM := singletonProgM fn
  [ shrI "t" "x" 63,
    (.Lcond (.reg "t") 1, .reg none),
    (.Lgoto (fn, 2), .reg none),
    (.Llabel .internal 1, .reg none),
    negI "x" "x",
    (.Llabel .internal 2, .reg none) ]

/-- The absolute value of a two's-complement word. -/
def absSpec (v : BitVec 64) : BitVec 64 := if v.msb then -v else v

/-- The state is in `fn` at the counter of the abstract pair and holds its word in `x`. -/
def condSR (fn : String) (t : LstateMF) (a : BitVec 64 × Nat) : Prop :=
  t.prog.lfn = fn ∧ t.prog.base.lpc = a.2 ∧ t.prog.base.reg.lvm "x" = ⟨64, a.1⟩

/-- The invariants of `condProg`: `x` holds the entry word, negative at label `1`. -/
def condInv : Option LLabel → LstateMF → BitVec 64 × Nat → Prop
  | none, m, a => m.prog.base.reg.lvm "x" = ⟨64, a.1⟩
  | some l, m, a => l = 1 ∧ m.prog.base.reg.lvm "x" = ⟨64, a.1⟩ ∧ a.1.msb = true

/-- **`Cond`.** From counter `0`, `condProg` halts at counter `6` with the absolute value
    of the entry word in `x`. -/
theorem cond_corresIsa (fn : String) :
    CorresIsa x86Isa (condProg fn) (condSR fn) (fun a => a.2 = 0)
      (fun a => (absSpec a.1, 6)) (3 * (1 + 1)) := by
  refine corresIsa_of_labels_floyd x86Isa (condProg fn) (condSR fn) _ _ condInv
    (fun c _ _ => if c = none then 1 else 0) 3 1 ?_ ?_
  · rintro m ⟨v, k⟩ ⟨hfn, hpc, hx⟩ hk
    exact ⟨⟨hfn, hpc.trans hk⟩, hx, Nat.le_refl _⟩
  · rintro (_ | l) m ⟨v, k⟩ hat hI
    · -- the entry block
      have hx : m.prog.base.reg.lvm "x" = ⟨64, v⟩ := hI
      obtain ⟨h1, at1⟩ := x86_steps_mem hat rfl ⟨_, _, _, rfl⟩ rfl rfl
        (lsemStepMem_shrI "t" "x" 63 m.prog.base v hx)
      generalize hm1 : setBase m _ = m1 at h1 at1
      have ht : m1.prog.base.reg.lvm "t" = ⟨64, v >>> 63⟩ := by subst hm1; simp
      have hx1 : m1.prog.base.reg.lvm "x" = ⟨64, v⟩ := by subst hm1; simp [hx]
      have hc := x86_condEval_reg m1 "t" _ rfl ht
      by_cases hneg : v >>> 63 = 0#64
      · obtain ⟨h2, at2⟩ := steps_cond_not_taken x86Isa at1 rfl (by rw [hc]; simp [hneg])
        obtain ⟨h3, -⟩ := steps_goto x86Isa (q := 5) at2 rfl rfl
        refine ⟨_, _, ?_, (h1.trans h2).trans h3,
          Or.inl ⟨halted_of_atPc (atPc_goto 6 at2) (Nat.le_refl _), at2.1, rfl, ?_⟩⟩
        · exact Nat.le_refl _
        · have : absSpec v = v := by unfold absSpec; bv_decide
          simp [hx1, this]
      · obtain ⟨h2, at2⟩ := steps_cond_taken x86Isa (q := 3) at1 rfl (by rw [hc]; simp [hneg])
          rfl
        refine ⟨_, _, ?_, h1.trans h2, Or.inr ⟨some 1, at2, ⟨rfl, ?_, ?_⟩, by simp⟩⟩
        · exact Nat.le_succ _
        · simp [hx1]
        · show v.msb = true
          bv_decide
    · -- the negation block
      obtain ⟨rfl, hx, hmsb⟩ := hI
      obtain ⟨q, hq, hat⟩ := hat
      obtain rfl : 3 = q := Option.some.inj hq
      obtain ⟨h1, at1⟩ := x86_steps_mem hat rfl ⟨_, _, _, rfl⟩ rfl rfl
        (lsemStepMem_negI "x" "x" m.prog.base v hx)
      generalize hm1 : setBase m _ = m1 at h1 at1
      have hx1 : m1.prog.base.reg.lvm "x" = ⟨64, 0 - v⟩ := by subst hm1; simp
      obtain ⟨h2, at2⟩ := steps_label x86Isa at1 rfl
      refine ⟨_, _, ?_, h1.trans h2,
        Or.inl ⟨halted_of_atPc at2 (Nat.le_refl _), at2.1, at2.2, ?_⟩⟩
      · exact Nat.le_succ _
      · have : absSpec v = 0 - v := by
          have hmsb' : v.msb = true := hmsb
          unfold absSpec; bv_decide
        simp [hx1, this]

/-- `cond_corresIsa` on a machine state: from counter `0` in `fn` with the word `v` in
    `x`, the run of `condProg fn` returns a state with the absolute value of `v` in `x`. -/
theorem cond_run (fn : String) (s : LstateMF) (v : BitVec 64) (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.lpc = 0) (hx : s.prog.base.reg.lvm "x" = ⟨64, v⟩) :
    ∃ t, x86Isa.lsemFuelMemF (condProg fn) 6 s = some t ∧
      t.prog.base.reg.lvm "x" = ⟨64, absSpec v⟩ := by
  obtain ⟨t, hrun, hSR⟩ := cond_corresIsa fn s (v, 0) ⟨hfn, hpc, hx⟩ rfl
  exact ⟨t, hrun, hSR.2.2⟩

/-! ## `Alias`: two stores through possibly equal indices -/

/-- `a[i] := u; a[j] := v; r := a[i]` on an array `a` of `n` words. -/
def aliasProg (fn : String) (n : Nat) : LprogM := singletonProgM fn
  [ storeI n "a" "a" "i" "u", storeI n "a" "a" "j" "v", loadI n "r" "a" "i" ]

/-- The abstract state of `aliasProg`: the array, the two indices, the two stored words,
    the word of `r` and the program counter. -/
structure AliasSt (n : Nat) where
  /-- The array `a`. -/
  arr : Fin n → BitVec 64
  /-- The index `i`. -/
  i : BitVec 64
  /-- The index `j`. -/
  j : BitVec 64
  /-- The word `u`. -/
  u : BitVec 64
  /-- The word `v`. -/
  v : BitVec 64
  /-- The word of `r`. -/
  r : BitVec 64
  /-- The program counter. -/
  pc : Nat

/-- The state is in `fn` at the counter of the abstract state and holds its array and its
    five words. -/
def aliasSR (fn : String) (n : Nat) (t : LstateMF) (a : AliasSt n) : Prop :=
  t.prog.lfn = fn ∧ t.prog.base.lpc = a.pc ∧ t.prog.base.getArr "a" 64 n = some a.arr ∧
    t.prog.base.reg.lvm "i" = ⟨64, a.i⟩ ∧ t.prog.base.reg.lvm "j" = ⟨64, a.j⟩ ∧
    t.prog.base.reg.lvm "u" = ⟨64, a.u⟩ ∧ t.prog.base.reg.lvm "v" = ⟨64, a.v⟩ ∧
    t.prog.base.reg.lvm "r" = ⟨64, a.r⟩

/-- The specification of `aliasProg`: both stores applied to the array, and in `r` the
    word `v` when the indices are equal and `u` otherwise. -/
def aliasSpec {n : Nat} (a : AliasSt n) : AliasSt n :=
  { a with arr := stackSet (stackSet a.arr a.i.toNat a.u) a.j.toNat a.v,
           r := if a.i = a.j then a.v else a.u, pc := 3 }

/-- The read after the two stores, by the case split on the aliasing of the indices. -/
theorem stackGet_alias {n : Nat} (arr : Fin n → BitVec 64) (i j u v : BitVec 64)
    (hi : i.toNat < n) (hj : j.toNat < n) :
    stackGet (stackSet (stackSet arr i.toNat u) j.toNat v) i.toNat = if i = j then v else u := by
  cases n with
  | zero => omega
  | succ m =>
      simp only [stackGet, stackSet, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
      by_cases h : i = j
      · subst h; simp
      · have hne : i.toNat ≠ j.toNat := fun hc => h (BitVec.eq_of_toNat_eq hc)
        simp [h, Fin.ext_iff, hne]

/-- **`Alias`.** From counter `0` with in-range indices, `aliasProg` halts at counter `3`
    with both stores applied and, in `r`, `v` when `i = j` and `u` otherwise. -/
theorem alias_corresIsa (fn : String) (n : Nat) :
    CorresIsa x86Isa (aliasProg fn n) (aliasSR fn n)
      (fun a => a.pc = 0 ∧ a.i.toNat < n ∧ a.j.toNat < n) aliasSpec (3 * (0 + 1)) := by
  refine corresIsa_of_labels_floyd x86Isa (aliasProg fn n) (aliasSR fn n) _ _
    (fun c m a => c = none ∧ aliasSR fn n m a ∧ a.i.toNat < n ∧ a.j.toNat < n)
    (fun _ _ _ => 0) 3 0 ?_ ?_
  · rintro m a hSR ⟨hk, hi, hj⟩
    exact ⟨⟨hSR.1, hSR.2.1.trans hk⟩, ⟨rfl, hSR, hi, hj⟩, Nat.le_refl _⟩
  · rintro c m a hat ⟨rfl, ⟨hfn, -, harr, hi, hj, hu, hv, -⟩, hin, hjn⟩
    -- the three instructions as a list run
    have e1 := lsemStepMem_storeI n "a" "a" "i" "u" m.prog.base a.arr a.i a.u harr hi hu
    have hstep : ∀ i ∈ [storeI n "a" "a" "i" "u", storeI n "a" "a" "j" "v", loadI n "r" "a" "i"],
        ∀ u u', x86Isa.step (aliasProg fn n) i u = some u' →
          u'.prog.lfn = u.prog.lfn ∧ u'.prog.base.lpc = u.prog.base.lpc + 1 := by
      intro i hi u u' h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;>
        exact x86_step_lopn_pc _ _ ⟨_, _, _, rfl⟩ rfl rfl u u' h
    have x1 := x86_step_mem (aliasProg fn n) ⟨_, _, _, rfl⟩ rfl rfl e1
    generalize hm1 : setBase m _ = m1 at x1
    have harr1 : m1.prog.base.getArr "a" 64 n = some (stackSet a.arr a.i.toNat a.u) := by
      subst hm1; simp
    have hlvm1 : m1.prog.base.reg.lvm = m.prog.base.reg.lvm := by subst hm1; simp
    have e2 := lsemStepMem_storeI n "a" "a" "j" "v" m1.prog.base _ a.j a.v harr1
      (by rw [hlvm1]; exact hj) (by rw [hlvm1]; exact hv)
    have x2 := x86_step_mem (aliasProg fn n) ⟨_, _, _, rfl⟩ rfl rfl e2
    generalize hm2 : setBase m1 _ = m2 at x2
    have harr2 : m2.prog.base.getArr "a" 64 n =
        some (stackSet (stackSet a.arr a.i.toNat a.u) a.j.toNat a.v) := by
      subst hm2; simp
    have hlvm2 : m2.prog.base.reg.lvm = m.prog.base.reg.lvm := by subst hm2; simp [hlvm1]
    have e3 := lsemStepMem_loadI n "r" "a" "i" m2.prog.base _ a.i harr2
      (by rw [hlvm2]; exact hi)
    have x3 := x86_step_mem (aliasProg fn n) ⟨_, _, _, rfl⟩ rfl rfl e3
    generalize hm3 : setBase m2 _ = m3 at x3
    have hrun : x86Isa.runL (aliasProg fn n)
        [storeI n "a" "a" "i" "u", storeI n "a" "a" "j" "v", loadI n "r" "a" "i"] m = some m3 := by
      simp only [Isa.runL, x1, x2, x3, Option.bind_some]
    obtain ⟨hsteps, hhalt⟩ := steps_of_runL_halted x86Isa (aliasProg fn n) _ [] m m3 rfl hat
      hstep hrun
    refine ⟨_, m3, Nat.le_refl _, hsteps, Or.inl ⟨hhalt, ?_⟩⟩
    have hfn3 : m3.prog.lfn = fn := by subst hm3 hm2 hm1; exact hfn
    have hpc3 : m3.prog.base.lpc = 3 := by
      have h1 := (hstep _ (by simp) m m1 x1).2
      have h2 := (hstep _ (by simp) m1 m2 x2).2
      have h3 := (hstep _ (by simp) m2 m3 x3).2
      rw [h3, h2, h1, hat.2]
    have hlvm3 : m3.prog.base.reg.lvm =
        fun r => if r = "r" then ⟨64, stackGet (stackSet (stackSet a.arr a.i.toNat a.u)
          a.j.toNat a.v) a.i.toNat⟩ else m.prog.base.reg.lvm r := by
      subst hm3; simp [hlvm2]
    have harr3 : m3.prog.base.getArr "a" 64 n =
        some (stackSet (stackSet a.arr a.i.toNat a.u) a.j.toNat a.v) := by
      subst hm3; simp [harr2]
    refine ⟨hfn3, hpc3, harr3, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hlvm3]
    · simpa [aliasSpec] using hi
    · simpa [aliasSpec] using hj
    · simpa [aliasSpec] using hu
    · simpa [aliasSpec] using hv
    · simp [aliasSpec, stackGet_alias a.arr a.i a.j a.u a.v hin hjn]

/-- `alias_corresIsa` on a machine state: from counter `0` in `fn` with the array `arr` in
    `a`, in-range indices `i` and `j` and the words `u` and `v`, the run of `aliasProg`
    returns a state with `v` in `r` when `i = j` and `u` otherwise. -/
theorem alias_run (fn : String) (n : Nat) (s : LstateMF) (arr : Fin n → BitVec 64)
    (i j u v r : BitVec 64) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 0)
    (harr : s.prog.base.getArr "a" 64 n = some arr)
    (hi : s.prog.base.reg.lvm "i" = ⟨64, i⟩) (hj : s.prog.base.reg.lvm "j" = ⟨64, j⟩)
    (hu : s.prog.base.reg.lvm "u" = ⟨64, u⟩) (hv : s.prog.base.reg.lvm "v" = ⟨64, v⟩)
    (hr : s.prog.base.reg.lvm "r" = ⟨64, r⟩) (hin : i.toNat < n) (hjn : j.toNat < n) :
    ∃ t, x86Isa.lsemFuelMemF (aliasProg fn n) 3 s = some t ∧
      t.prog.base.reg.lvm "r" = ⟨64, if i = j then v else u⟩ ∧
      t.prog.base.getArr "a" 64 n = some (stackSet (stackSet arr i.toNat u) j.toNat v) := by
  obtain ⟨t, hrun, hSR⟩ := alias_corresIsa fn n s ⟨arr, i, j, u, v, r, 0⟩
    ⟨hfn, hpc, harr, hi, hj, hu, hv, hr⟩ ⟨rfl, hin, hjn⟩
  exact ⟨t, hrun, hSR.2.2.2.2.2.2.2, hSR.2.2.1⟩

/-! ## `P3`: a loop of three blocks -/

/-- `r := 0`; at the head, label `1`, jump to the body, label `2`, when `n` is non-zero and
    to the exit, label `3`, otherwise; the body adds `3` to `r`, decrements `n` and jumps
    to the head. -/
def loopProg (fn : String) : LprogM := singletonProgM fn
  [ movI "r" 0,
    (.Llabel .internal 1, .reg none),
    (.Lcond (.reg "n") 2, .reg none),
    (.Lgoto (fn, 3), .reg none),
    (.Llabel .internal 2, .reg none),
    addI "r" "r" 3,
    subI "n" "n" 1,
    (.Lgoto (fn, 1), .reg none),
    (.Llabel .internal 3, .reg none) ]

/-- The state is in `fn` at the counter of the abstract triple and holds its words in `n`
    and `r`. -/
def loopSR (fn : String) (t : LstateMF) (a : BitVec 64 × BitVec 64 × Nat) : Prop :=
  t.prog.lfn = fn ∧ t.prog.base.lpc = a.2.2 ∧ t.prog.base.reg.lvm "n" = ⟨64, a.1⟩ ∧
    t.prog.base.reg.lvm "r" = ⟨64, a.2.1⟩

/-- The invariants of `loopProg`: at the entry `n` holds the entry word `n₀`; at the head
    `n` holds a word `k` and `r` holds `3 * (n₀ - k)`. -/
def loopInv : Option LLabel → LstateMF → BitVec 64 × BitVec 64 × Nat → Prop
  | none, m, a => m.prog.base.reg.lvm "n" = ⟨64, a.1⟩
  | some l, m, a => l = 1 ∧ ∃ k : BitVec 64, m.prog.base.reg.lvm "n" = ⟨64, k⟩ ∧
      m.prog.base.reg.lvm "r" = ⟨64, 3 * (a.1 - k)⟩

/-- The measure of `loopProg`: the word of `n` at the head, and `2 ^ 64` at the entry. -/
def loopMeasure : Option LLabel → LstateMF → BitVec 64 × BitVec 64 × Nat → Nat
  | none, _, _ => 2 ^ 64
  | some _, m, _ => (m.prog.base.reg.lvm "n").2.toNat

/-- **`P3`.** From counter `0`, `loopProg` halts at counter `9` with `n` zero and three
    times the entry word of `n` in `r`. -/
theorem loop_corresIsa (fn : String) :
    CorresIsa x86Isa (loopProg fn) (loopSR fn) (fun a => a.2.2 = 0)
      (fun a => (0, 3 * a.1, 9)) (4 * (2 ^ 64 + 1)) := by
  refine corresIsa_of_labels_floyd x86Isa (loopProg fn) (loopSR fn) _ _ loopInv loopMeasure
    4 (2 ^ 64) ?_ ?_
  · rintro m ⟨n0, r0, pc⟩ ⟨hfn, hpc, hn, -⟩ hk
    exact ⟨⟨hfn, hpc.trans hk⟩, hn, Nat.le_refl _⟩
  · rintro (_ | l) m ⟨n0, r0, pc⟩ hat hI
    · -- the entry block
      have hn : m.prog.base.reg.lvm "n" = ⟨64, n0⟩ := hI
      obtain ⟨h1, at1⟩ := x86_steps_mem hat rfl ⟨_, _, _, rfl⟩ rfl rfl
        (lsemStepMem_movI "r" 0 m.prog.base)
      generalize hm1 : setBase m _ = m1 at h1 at1
      have hn1 : m1.prog.base.reg.lvm "n" = ⟨64, n0⟩ := by subst hm1; simp [hn]
      have hr1 : m1.prog.base.reg.lvm "r" = ⟨64, 0#64⟩ := by subst hm1; simp
      obtain ⟨h2, at2⟩ := steps_label x86Isa at1 rfl
      refine ⟨_, _, ?_, h1.trans h2,
        Or.inr ⟨some 1, ⟨1, rfl, at2⟩, ⟨rfl, n0, by simp [hn1], by simp [hr1]⟩, ?_⟩⟩
      · exact Nat.le_add_left 2 2
      · show ((next m1).prog.base.reg.lvm "n").2.toNat < 2 ^ 64
        rw [show (next m1).prog.base.reg.lvm "n" = ⟨64, n0⟩ from hn1]
        exact n0.isLt
    · -- the head, then the exit or the body
      obtain ⟨rfl, k, hn, hr⟩ := hI
      obtain ⟨q, hq, hat⟩ := hat
      obtain rfl : 1 = q := Option.some.inj hq
      have hc := x86_condEval_reg m "n" k rfl hn
      by_cases hk : k = 0#64
      · obtain ⟨h1, at1⟩ := steps_cond_not_taken x86Isa hat rfl (by rw [hc]; simp [hk])
        obtain ⟨h2, -⟩ := steps_goto x86Isa (q := 8) at1 rfl rfl
        refine ⟨_, _, ?_, h1.trans h2,
          Or.inl ⟨halted_of_atPc (atPc_goto 9 at1) (Nat.le_refl _), at1.1, rfl, ?_, ?_⟩⟩
        · exact Nat.le_add_left 2 2
        · simp [hn, hk]
        · simp [hr, hk]
      · obtain ⟨h1, -⟩ := steps_cond_taken x86Isa (q := 4) hat rfl (by rw [hc]; simp [hk]) rfl
        have at1 : atPc (loopProg fn) 5 (goto m 5) := atPc_goto 5 hat
        obtain ⟨h2, at2⟩ := x86_steps_mem at1 rfl ⟨_, _, _, rfl⟩ rfl rfl
          (lsemStepMem_addI "r" "r" 3 (goto m 5).prog.base (3 * (n0 - k))
            (by rw [goto_lvm]; exact hr))
        generalize hm2 : setBase (goto m 5) _ = m2 at h2 at2
        have hn2 : m2.prog.base.reg.lvm "n" = ⟨64, k⟩ := by subst hm2; simp [hn]
        have hr2 : m2.prog.base.reg.lvm "r" = ⟨64, 3 * (n0 - k) + 3#64⟩ := by subst hm2; simp
        obtain ⟨h3, at3⟩ := x86_steps_mem at2 rfl ⟨_, _, _, rfl⟩ rfl rfl
          (lsemStepMem_subI "n" "n" 1 m2.prog.base k hn2)
        generalize hm3 : setBase m2 _ = m3 at h3 at3
        have hn3 : m3.prog.base.reg.lvm "n" = ⟨64, k - 1#64⟩ := by subst hm3; simp
        have hr3 : m3.prog.base.reg.lvm "r" = ⟨64, 3 * (n0 - k) + 3#64⟩ := by
          subst hm3; simp [hr2]
        obtain ⟨h4, at4⟩ := steps_goto x86Isa (q := 1) at3 rfl rfl
        refine ⟨_, _, ?_, ((h1.trans h2).trans h3).trans h4,
          Or.inr ⟨some 1, at4, ⟨rfl, k - 1#64, by rw [goto_lvm]; exact hn3, ?_⟩, ?_⟩⟩
        · exact Nat.le_refl _
        · rw [goto_lvm, hr3]
          have : 3 * (n0 - k) + 3#64 = 3 * (n0 - (k - 1#64)) := by bv_decide
          rw [this]
        · show ((goto m3 2).prog.base.reg.lvm "n").2.toNat < (m.prog.base.reg.lvm "n").2.toNat
          rw [goto_lvm, hn3, hn]
          show (k - 1#64).toNat < k.toNat
          bv_omega

/-- `loop_corresIsa` on a machine state: from counter `0` in `fn` with the word `n` in `n`,
    the run of `loopProg fn` returns a state with `3 * n` in `r` and zero in `n`. -/
theorem loop_run (fn : String) (s : LstateMF) (n r : BitVec 64) (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.lpc = 0) (hn : s.prog.base.reg.lvm "n" = ⟨64, n⟩)
    (hr : s.prog.base.reg.lvm "r" = ⟨64, r⟩) :
    ∃ t, x86Isa.lsemFuelMemF (loopProg fn) (4 * (2 ^ 64 + 1)) s = some t ∧
      t.prog.base.reg.lvm "r" = ⟨64, 3 * n⟩ ∧ t.prog.base.reg.lvm "n" = ⟨64, 0#64⟩ := by
  obtain ⟨t, hrun, hSR⟩ := loop_corresIsa fn s (n, r, 0) ⟨hfn, hpc, hn, hr⟩ rfl
  exact ⟨t, hrun, hSR.2.2.2, hSR.2.2.1⟩

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.KrakenCfgDemo
