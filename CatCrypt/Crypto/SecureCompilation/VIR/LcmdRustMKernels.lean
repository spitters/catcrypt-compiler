/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LcmdRustM

/-!
# Kernels of the linear memref language proved through the `RustM` reading

Three kernels of the linear instruction language `LinstrRM`, each proved by `vcgen` over
the body reading `LcmdRustM.bodyM` and transferred to the flag-extended interpreter
`JasminLsemMemFlagGuard.lsemFuelMemF`:

* a two-limb carry chain `ADD:64; ADC:64`;
* a counted loop that sums the first `n` limbs of a stack array, in the flag-guarded loop
  shape `flagLoopLinstrRM` (body, `CMP c,#0`, `Lcond NZ top`) that `forLoopLcmdNRt` emits;
* a fixed-size buffer written at two indices and read back.

## Main results

* `stepM_adc_spec`, `stepM_sub_spec`: the `@[spec]` triples of the add-with-carry `ADC:64`,
  which reads the carry flag, and of the 64-bit subtraction `SUB:64`.
* `flagLoop_of_pass_triple`: the loop rule. A loop invariant `Inv k` whose pass triple
  `⦃Inv k⦄ bodyM body ⦃Inv (k + 1)⦄` holds for `k < n`, and which reads the counter as
  `n - k`, gives a run of `lsemFuelMemF` over the flag-guarded loop of `n` passes to a state
  that agrees with a state satisfying `Inv n` on the registers and arrays.
* `add2_spec`, `add2_lsemFuelMemF`: the carry chain leaves `r0 + 2^64 r1 + 2^128 cf` equal
  to the sum of the two-limb operands.
* `sumBody_pass_spec`, `sumLoop_lsemFuelMemF`: the loop leaves the sum of the first `n`
  limbs of the array in `acc`.
* `bufRoundTrip_spec`, `bufRoundTrip_lsemFuelMemF`: the buffer holds both stores and the
  loads return the stored words.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.LcmdRustMKernels

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LcmdRustM
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (x86_ADD x86_ADC x86_SUB)
open Aeneas.Std (RustM Error)
open _root_.Std.WP Lean.Order

/-! ## 1. Specifications of the carry and the subtraction -/

/-- Unfolding lemma of `withFlags` at the carry flag. -/
@[simp] theorem withFlags_cf (t : LstateM) (c o : Bool) : (withFlags t c o).cf = c := rfl

/-- **The add-with-carry.** `ADC:64 dst ← a, b`: when `a` and `b` hold 64-bit words, the
    step writes the word of the machine's `x86_ADC` with carry-in `CF` to `dst`, its carry
    and overflow flags, and advances the pc. -/
@[spec]
theorem stepM_adc_spec (dst a b : String)
    (post : Unit → LstateM → Prop) {epost : Error → Prop} :
    Triple (stepM (.Lopn [.reg dst] "ADC:64" [.reg a, .reg b], .reg none))
      (fun s : LstateM => Lean.Order.meet ((s.reg.getW a 64).isSome ∧ (s.reg.getW b 64).isSome)
        (post () (withFlags
          (s.setReg dst (x86_ADC ((s.reg.getW a 64).getD 0) ((s.reg.getW b 64).getD 0)
            s.cf).word).nextPc
          ((x86_ADC ((s.reg.getW a 64).getD 0) ((s.reg.getW b 64).getD 0) s.cf).cf.getD false)
          ((x86_ADC ((s.reg.getW a 64).getD 0) ((s.reg.getW b 64).getD 0) s.cf).of.getD
            false))))
      post epost := by
  refine ⟨fun s h => ?_⟩
  obtain ⟨⟨h1, h2⟩, hp⟩ := (meet_prop_eq_and _ _).mp h
  obtain ⟨va, ha⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨vb, hb⟩ := Option.isSome_iff_exists.mp h2
  rw [ha, hb] at hp
  have hstrip : stripWidthTag "ADC:64" = "ADC" := by decide +kernel
  have hm : mulhiStruct? (.Lopn [.reg dst] "ADC:64" [.reg a, .reg b]) = none := by
    simp only [mulhiStruct?, hstrip]; rfl
  have hs : sarStruct? (.Lopn [.reg dst] "ADC:64" [.reg a, .reg b]) = none := by
    simp only [sarStruct?]
  have hnone : lsemStepMem (.Lopn [.reg dst] "ADC:64" [.reg a, .reg b], .reg none) s
      = none := by
    rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inr rfl),
      lsemStepMC_of_delegate _ _ hm rfl rfl rfl rfl, lsemStepSh_of_not_sar _ _ hs]
    simp only [lsemStepN, readReg_of_getW ha, evalOperandN, hb, hstrip]
    rfl
  have hcarry : carryArgs? (.Lopn [.reg dst] "ADC:64" [.reg a, .reg b], .reg none)
      = some (.adc, dst, .reg a, .reg b) := by
    simp [carryArgs?, withWidthTag]
  rw [StateT.wp_apply_eq, stepM_run]
  simp only [stepMemF, hnone, hcarry, carryStep, evalOperandN, ha, hb, Option.map_some]
  exact hp

/-- **The 64-bit subtraction.** `SUB:64 dst ← a, b`: when `a` and `b` hold 64-bit words,
    the step writes their difference to `dst`, the carry and overflow flags of the
    machine's `x86_SUB`, and advances the pc. -/
@[spec]
theorem stepM_sub_spec (dst a b : String) (cd : Option Nat)
    (post : Unit → LstateM → Prop) {epost : Error → Prop} :
    Triple (stepM (.Lopn [.reg dst] "SUB:64" [.reg a, .reg b], .reg cd))
      (fun s : LstateM => Lean.Order.meet ((s.reg.getW a 64).isSome ∧ (s.reg.getW b 64).isSome)
        (post () (withFlags
          (s.setReg dst ((s.reg.getW a 64).getD 0 - (s.reg.getW b 64).getD 0)).nextPc
          ((x86_SUB ((s.reg.getW a 64).getD 0) ((s.reg.getW b 64).getD 0)).cf.getD false)
          ((x86_SUB ((s.reg.getW a 64).getD 0) ((s.reg.getW b 64).getD 0)).of.getD false))))
      post epost := by
  refine ⟨fun s h => ?_⟩
  obtain ⟨⟨h1, h2⟩, hp⟩ := (meet_prop_eq_and _ _).mp h
  obtain ⟨va, ha⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨vb, hb⟩ := Option.isSome_iff_exists.mp h2
  rw [ha, hb] at hp
  have hstrip : stripWidthTag "SUB:64" = "SUB" := by decide +kernel
  have hlow : lsemStepMem (.Lopn [.reg dst] "SUB:64" [.reg a, .reg b], .reg cd) s
      = some ((s.setReg dst (va - vb)).nextPc) := by
    rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inl ⟨rfl, rfl⟩),
      lsemStepMC_of_delegate _ _ rfl rfl rfl rfl rfl,
      lsemStepSh_of_not_sar _ _ (by simp [sarStruct?])]
    simp only [lsemStepN, readReg_of_getW ha, evalOperandN, hb, hstrip, applyOpnN,
      Option.map_some]
    rfl
  have hflag : aluFlagOp? (.Lopn [.reg dst] "SUB:64" [.reg a, .reg b], .reg cd)
      = some (.sub, .reg a, .reg b) := by
    simp [aluFlagOp?, withWidthTag]
  rw [StateT.wp_apply_eq, stepM_run, stepMemF_of_lsemStepMem hlow]
  simp only [withALUFlags, hflag, evalOperandN, ha, hb, Option.map_some]
  exact hp

/-! ## 2. Carry equations of the machine's addition -/

/-- `ADD`: the sum word and the carry-out recombine to the sum of the operands. -/
theorem x86_ADD_toNat_carry (a b : BitVec 64) :
    (a + b).toNat + 2 ^ 64 * ((x86_ADD a b).cf.getD false).toNat = a.toNat + b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [x86_ADD, X86Backend.Jasmin.rflags_of_aluop, X86Backend.Jasmin.wunsigned,
    Option.getD_some, BitVec.toNat_add]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat
  · simp_all
    omega
  · simp_all

/-- `ADC`: the word and the carry-out recombine to the sum of the operands and the
    carry-in. -/
theorem x86_ADC_toNat_carry (a b : BitVec 64) (c : Bool) :
    (x86_ADC a b c).word.toNat + 2 ^ 64 * ((x86_ADC a b c).cf.getD false).toNat
      = a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [x86_ADC, X86Backend.Jasmin.rflags_of_aluop, X86Backend.Jasmin.add_carry,
    X86Backend.Jasmin.wunsigned, Option.getD_some, BitVec.toNat_ofNat]
  have hc : (if c = true then 1 else 0) = c.toNat := by cases c <;> rfl
  have hc1 := Bool.toNat_le c
  rw [hc]
  by_cases hS : a.toNat + b.toNat + c.toNat < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hS]
    simp
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hne : a.toNat + b.toNat + c.toNat - 2 ^ 64 ≠ a.toNat + b.toNat + c.toNat := by omega
    simp only [ne_eq, hne, not_false_eq_true, decide_true, Bool.toNat_true]
    omega

/-! ## 3. The carry chain -/

/-- The two-limb addition `ADD:64 r0 ← a0, b0; ADC:64 r1 ← a1, b1`. -/
def add2 : List LinstrRM :=
  [(.Lopn [.reg "r0"] "ADD:64" [.reg "a0", .reg "b0"], .reg none),
   (.Lopn [.reg "r1"] "ADC:64" [.reg "a1", .reg "b1"], .reg none)]

/-- **The carry chain, proved by `vcgen`.** The two result limbs and the carry-out
    recombine to the sum of the two-limb operands. -/
theorem add2_spec (a0 a1 b0 b1 : BitVec 64) :
    ⦃fun s => s.reg.getW "a0" 64 = some a0 ∧ s.reg.getW "a1" 64 = some a1 ∧
        s.reg.getW "b0" 64 = some b0 ∧ s.reg.getW "b1" 64 = some b1⦄
      bodyM add2
    ⦃fun _ s' => ∃ r0 r1 : BitVec 64, s'.reg.getW "r0" 64 = some r0 ∧
        s'.reg.getW "r1" 64 = some r1 ∧
        r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * s'.cf.toNat
          = (a0.toNat + 2 ^ 64 * a1.toNat) + (b0.toNat + 2 ^ 64 * b1.toNat)⦄ := by
  simp only [add2, bodyM]
  set_option experimental.vcgen true in vcgen
  all_goals
    rename_i h
    obtain ⟨h0, h1, h2, h3⟩ := h
    simp [withFlags, LstateN.getW_setReg_other, h0, h1, h2, h3]
  have e1 := x86_ADD_toNat_carry a0 b0
  have e2 := x86_ADC_toNat_carry a1 b1 ((x86_ADD a0 b0).cf.getD false)
  grind

/-! ## 4. The fixed-size buffer -/

/-- The buffer body: `buf[i] := u; buf[j] := v; x := buf[i]; y := buf[j]` over a stack
    array `buf` of four 64-bit words. -/
def bufRoundTrip : List LinstrRM :=
  [(.Lopn [.reg "buf"] "STOREIDX" [.arrIdx "buf" "i" 8, .reg "u"], .store 64 4),
   (.Lopn [.reg "buf"] "STOREIDX" [.arrIdx "buf" "j" 8, .reg "v"], .store 64 4),
   (.Lopn [.reg "x"] "LOADIDX" [.arrIdx "buf" "i" 8], .load 64 4),
   (.Lopn [.reg "y"] "LOADIDX" [.arrIdx "buf" "j" 8], .load 64 4)]

/-- **The buffer, proved by `vcgen`.** With both indices below the buffer size `4` and
    distinct, the buffer holds both stores and the loads return the stored words. -/
theorem bufRoundTrip_spec (arr : Fin 4 → BitVec 64) (i j u v : BitVec 64)
    (hi : i.toNat < 4) (hj : j.toNat < 4) (hij : i.toNat ≠ j.toNat) :
    ⦃fun s => s.getArr "buf" 64 4 = some arr ∧ s.reg.getW "i" 64 = some i ∧
        s.reg.getW "j" 64 = some j ∧ s.reg.getW "u" 64 = some u ∧
        s.reg.getW "v" 64 = some v⦄
      bodyM bufRoundTrip
    ⦃fun _ s' => s'.getArr "buf" 64 4 = some (stackSet (stackSet arr i.toNat u) j.toNat v) ∧
        s'.reg.getW "x" 64 = some u ∧ s'.reg.getW "y" 64 = some v⦄ := by
  simp only [bufRoundTrip, bodyM]
  set_option experimental.vcgen true in vcgen
  all_goals
    rename_i h
    obtain ⟨ha, hi', hj', hu, hv⟩ := h
    simp [LstateN.getW_setReg_other, ha, hi', hj', hu, hv, hi, hj]
  all_goals simp [stackGet, stackSet, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj, Fin.ext_iff, hij]

/-- The buffer body is a plain-`Lopn` body. -/
theorem bufRoundTrip_plain : PlainLopnBody bufRoundTrip := by
  intro i hmem
  simp only [bufRoundTrip, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> exact ⟨⟨_, _, _, rfl⟩, by decide, by decide⟩

/-- **The buffer transferred to the interpreter.** From a state at program counter `0`
    satisfying the precondition, `lsemFuelMemF` runs the one-function program of the buffer
    body in four steps to a state whose buffer holds both stores and whose `x` and `y`
    hold the stored words. -/
theorem bufRoundTrip_lsemFuelMemF (fn : String) (arr : Fin 4 → BitVec 64) (i j u v : BitVec 64)
    (hi : i.toNat < 4) (hj : j.toNat < 4) (hij : i.toNat ≠ j.toNat) (s : LstateM)
    (h0 : s.lpc = 0) (ha : s.getArr "buf" 64 4 = some arr) (hi' : s.reg.getW "i" 64 = some i)
    (hj' : s.reg.getW "j" 64 = some j) (hu : s.reg.getW "u" 64 = some u)
    (hv : s.reg.getW "v" 64 = some v) (zf : Bool) :
    ∃ s', lsemFuelMemF (singletonProgM fn bufRoundTrip) 4
        { prog := { base := s, lfn := fn }, zf := zf }
        = some { prog := { base := s', lfn := fn }, zf := zf } ∧
      s'.getArr "buf" 64 4 = some (stackSet (stackSet arr i.toNat u) j.toNat v) ∧
      s'.reg.getW "x" 64 = some u ∧ s'.reg.getW "y" 64 = some v :=
  lsemFuelMemF_of_bodyM_triple fn bufRoundTrip (bufRoundTrip_spec arr i j u v hi hj hij)
    bufRoundTrip_plain s h0 ⟨ha, hi', hj', hu, hv⟩ zf

/-- The carry-chain body is a plain-`Lopn` body. -/
theorem add2_plain : PlainLopnBody add2 := by
  intro i hmem
  simp only [add2, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl <;> exact ⟨⟨_, _, _, rfl⟩, by decide, by decide⟩

/-- **The carry chain transferred to the interpreter.** From a state at program counter
    `0` holding the two-limb operands, `lsemFuelMemF` runs the one-function program of the
    carry chain in two steps to a state whose result limbs and carry flag recombine to the
    sum of the operands. -/
theorem add2_lsemFuelMemF (fn : String) (a0 a1 b0 b1 : BitVec 64) (s : LstateM)
    (h0 : s.lpc = 0) (ha0 : s.reg.getW "a0" 64 = some a0) (ha1 : s.reg.getW "a1" 64 = some a1)
    (hb0 : s.reg.getW "b0" 64 = some b0) (hb1 : s.reg.getW "b1" 64 = some b1) (zf : Bool) :
    ∃ s', lsemFuelMemF (singletonProgM fn add2) 2
        { prog := { base := s, lfn := fn }, zf := zf }
        = some { prog := { base := s', lfn := fn }, zf := zf } ∧
      ∃ r0 r1 : BitVec 64, s'.reg.getW "r0" 64 = some r0 ∧ s'.reg.getW "r1" 64 = some r1 ∧
        r0.toNat + 2 ^ 64 * r1.toNat + 2 ^ 128 * s'.cf.toNat
          = (a0.toNat + 2 ^ 64 * a1.toNat) + (b0.toNat + 2 ^ 64 * b1.toNat) :=
  lsemFuelMemF_of_bodyM_triple fn add2 (add2_spec a0 a1 b0 b1) add2_plain s h0
    ⟨ha0, ha1, hb0, hb1⟩ zf

/-! ## 5. The loop rule over the flag-guarded loop -/

/-- A triple of the body reading with exception postcondition `⊥` is, at a state
    satisfying the precondition, a run of the flag body-fold to a state satisfying the
    postcondition. -/
theorem lsemStraightMemF_of_triple {body : List LinstrRM} {Pre : LstateM → Prop}
    {Q : Unit → LstateM → Prop} (h : Triple (bodyM body) Pre Q Lean.Order.bot) {s : LstateM}
    (hs : Pre s) : ∃ s', lsemStraightMemF body s = some s' ∧ Q () s' := by
  obtain ⟨u, s', hrun, hQ⟩ := run_of_triple h hs
  cases u
  exact ⟨s', (bodyM_ok_iff body s s').1 hrun, hQ⟩

/-- **The loop rule.** Let `Inv k` be a loop invariant of the flag-guarded loop
    `flagLoopLinstrRM top nReg body` with `n` passes: its pass triple
    `⦃Inv k⦄ bodyM body ⦃Inv (k + 1)⦄` holds for `k < n`, it survives the back-edge's
    reset of the pc, and it reads the counter `nReg` as `n - k`. From a state at the loop
    top satisfying `Inv 0`, `lsemFuelMemF` runs `n` passes and halts at a state that agrees
    on the registers and the arrays with a state satisfying `Inv n`. -/
theorem flagLoop_of_pass_triple (fn : String) (top : LLabel) (nReg : String)
    (body : List LinstrRM) (hbody : PlainLopnBody body) (n : Nat) (hn : 0 < n)
    (hn64 : n < 2 ^ 64) (Inv : Nat → LstateM → Prop)
    (hpass : ∀ k, k < n → ⦃ Inv k ⦄ bodyM body ⦃ fun _ => Inv (k + 1) ⦄)
    (hlpc : ∀ k s, Inv k s → Inv k (s.setLpc 1))
    (hctr : ∀ k s, k ≤ n → Inv k s → s.reg.getW nReg 64 = some (BitVec.ofNat 64 (n - k)))
    (b0 : LstateM) (hpc : b0.lpc = 1) (h0 : Inv 0 b0) (zf : Bool) :
    ∃ (t : LstateMF) (b : LstateM),
      lsemFuelMemF (singletonProgM fn (flagLoopLinstrRM top nReg body))
          (n * (body.length + 2)) { prog := { base := b0, lfn := fn }, zf := zf } = some t ∧
      Inv n b ∧ t.prog.base.reg.lvm = b.reg.lvm ∧ t.prog.base.larr = b.larr := by
  have hstep : ∀ k s, k < n → Inv k s →
      ∃ s', lsemStraightMemF body s = some s' ∧ Inv (k + 1) s' :=
    fun k _ hk hs => lsemStraightMemF_of_triple (hpass k hk) hs
  have hchain : ∀ k, k ≤ n → ∃ b, runBoundedLoopMemF body k b0 = some b ∧ Inv k b := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨b0, rfl, h0⟩
    | succ k ih =>
      intro hk
      obtain ⟨b, hb, hIb⟩ := ih (by omega)
      obtain ⟨s', hs', hIs'⟩ := hstep k b (by omega) hIb
      refine ⟨s'.setLpc 1, ?_, hlpc _ _ hIs'⟩
      rw [runBoundedLoopMemF_succ_right, hb, Option.bind_some, hs', Option.map_some]
  obtain ⟨bprev, hprev, hIprev⟩ := hchain (n - 1) (by omega)
  obtain ⟨blast, hlast, hIlast⟩ := hstep (n - 1) bprev (by omega) hIprev
  obtain ⟨bfin, hfin, hIfin⟩ := hchain n le_rfl
  have htaken : ∀ i, 0 < i → i < n → ∀ bi, runBoundedLoopMemF body i b0 = some bi →
      condNZ bi (.reg nReg) = true := by
    intro i _ hin bi hbi
    obtain ⟨b, hb, hIb⟩ := hchain i (by omega)
    rw [hb, Option.some.injEq] at hbi
    subst hbi
    have hr := hctr i b (by omega) hIb
    unfold condNZ
    rw [show evalOperandN b.reg 64 (.reg nReg) = some (BitVec.ofNat 64 (n - i)) from hr]
    grind
  have hzero : blast.reg.getW nReg 64 = some 0#64 := by
    rw [hctr (n - 1 + 1) blast (by omega) hIlast]
    grind
  obtain ⟨t, ht, hlvm, hlarr, _⟩ := flagLoop_runBounded fn top nReg body hbody b0 zf hpc n hn
    bprev blast bfin hprev hlast hfin (fun i hi hin bi hbi => htaken i hi hin bi hbi) hzero
  exact ⟨t, bfin, ht, hIfin, hlvm, hlarr⟩

/-! ## 6. The counted loop: the sum of `n` limbs -/

/-- The sum of the first `k` limbs of a stack array, modulo `2^64`. -/
def limbSum {N : Nat} (arr : Fin N → BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | k + 1 => limbSum arr k + stackGet arr k

/-- The loop body over a stack array `a` of `N` words:
    `x := a[i]; acc := acc + x; i := i + one; c := c - one`. -/
def sumBody (N : Nat) : List LinstrRM :=
  [(.Lopn [.reg "x"] "LOADIDX" [.arrIdx "a" "i" 8], .load 64 N),
   (.Lopn [.reg "acc"] "ADD:64" [.reg "acc", .reg "x"], .reg none),
   (.Lopn [.reg "i"] "ADD:64" [.reg "i", .reg "one"], .reg none),
   (.Lopn [.reg "c"] "SUB:64" [.reg "c", .reg "one"], .reg none)]

/-- The loop invariant after `k` of `n` passes: `a` holds `arr`, the index `i` is `k`, the
    counter `c` is `n - k`, `acc` is the sum of the first `k` limbs and `one` is `1`. -/
def SumInv (N n : Nat) (arr : Fin N → BitVec 64) (k : Nat) (s : LstateM) : Prop :=
  s.getArr "a" 64 N = some arr ∧ s.reg.getW "i" 64 = some (BitVec.ofNat 64 k) ∧
    s.reg.getW "c" 64 = some (BitVec.ofNat 64 (n - k)) ∧
    s.reg.getW "acc" 64 = some (limbSum arr k) ∧ s.reg.getW "one" 64 = some 1

/-- **The pass triple of the loop, proved by `vcgen`.** One pass of the body takes the
    invariant at `k < n` to the invariant at `k + 1`. -/
theorem sumBody_pass_spec (N n : Nat) (hN : N < 2 ^ 64) (hnN : n ≤ N)
    (arr : Fin N → BitVec 64) (k : Nat) (hk : k < n) :
    ⦃ SumInv N n arr k ⦄ bodyM (sumBody N) ⦃ fun _ => SumInv N n arr (k + 1) ⦄ := by
  have hmod : k % 18446744073709551616 = k := Nat.mod_eq_of_lt (by omega)
  have hkN : k < N := by omega
  have hi1 : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hc1 : BitVec.ofNat 64 (n - k) - 1#64 = BitVec.ofNat 64 (n - (k + 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  simp only [sumBody, bodyM]
  set_option experimental.vcgen true in vcgen
  all_goals
    rename_i h
    obtain ⟨ha, hi, hc, hacc, hone⟩ := h
    simp [SumInv, LstateN.getW_setReg_other, ha, hi, hc, hacc, hone, hmod, hkN, hi1, hc1,
      limbSum]

/-- The loop body is a plain-`Lopn` body. -/
theorem sumBody_plain (N : Nat) : PlainLopnBody (sumBody N) := by
  intro i hmem
  simp only [sumBody, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl <;> exact ⟨⟨_, _, _, rfl⟩, rfl, rfl⟩

/-- **The counted loop transferred to the interpreter.** From a state at the loop top
    (pc `1`, past the label) satisfying the invariant at `0`, `lsemFuelMemF` runs the
    flag-guarded loop of `n ≤ N` passes over the stack array `a` and halts at a state whose
    `acc` holds the sum of the first `n` limbs and whose array `a` is unchanged. -/
theorem sumLoop_lsemFuelMemF (fn : String) (top : LLabel) (N n : Nat) (hN : N < 2 ^ 64)
    (hn : 0 < n) (hnN : n ≤ N) (arr : Fin N → BitVec 64) (s : LstateM) (hpc : s.lpc = 1)
    (hs : SumInv N n arr 0 s) (zf : Bool) :
    ∃ t : LstateMF,
      lsemFuelMemF (singletonProgM fn (flagLoopLinstrRM top "c" (sumBody N)))
          (n * ((sumBody N).length + 2)) { prog := { base := s, lfn := fn }, zf := zf }
        = some t ∧
      t.prog.base.reg.getW "acc" 64 = some (limbSum arr n) ∧
      t.prog.base.getArr "a" 64 N = some arr := by
  obtain ⟨t, b, ht, hInv, hlvm, hlarr⟩ := flagLoop_of_pass_triple fn top "c" (sumBody N)
    (sumBody_plain N) n hn (by omega) (SumInv N n arr)
    (fun k hk => sumBody_pass_spec N n hN hnN arr k hk) (fun _ _ h => h)
    (fun _ _ _ h => h.2.2.1) s hpc hs zf
  have hacc : t.prog.base.reg.getW "acc" 64 = b.reg.getW "acc" 64 := by
    unfold LstateN.getW
    rw [hlvm]
  have harr : t.prog.base.getArr "a" 64 N = b.getArr "a" 64 N := by
    unfold LstateM.getArr
    rw [hlarr]
  exact ⟨t, ht, hacc.trans hInv.2.2.2.1, harr.trans hInv.1⟩

end CatCrypt.Crypto.SecureCompilation.VIR.LcmdRustMKernels
