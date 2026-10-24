/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.PackedStateEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextValidate

/-!
# The packed-state IR on the `%zmm` machine: lowering, simulation, checked text

`lowerInstr` maps each instruction of the packed-state IR (`PackedStateEmit.PInstr`) to
instructions of the machine model `ZmmTextModel`: IR register `r` is `%zmm r`, the
modulus `p` and `mu` sit in every dword of `%zmm24` and `%zmm25`, `%zmm26` to `%zmm31`
are scratch, and `%k1` holds the even-dword mask `0x5555`.

* `cst` is a 64-byte load from the data table;
* `add` and `sub` are `vpaddd`/`vpsubd`, the correction by `p` and `vpminud`;
* `mul` is the sequence `mulSeq`: `vpmuludq` of the even dwords and of the odd dwords
  moved down by `vmovshdup`, the low words times `mu`, those times `p`, the two
  differences of high words merged by a `vmovshdup` under `%k1`, and `vpminud` of `d`
  and `d + p` (`lane_mulVal`: dword `j` is `mmulW` of dword `j` of the operands);
* `perm` loads its index vector and applies `vpermd`;
* `blend` sets `%k2` and applies `vpblendmd`.

`lowerInstr_sim` states that the machine run of the lowered instructions keeps the IR
register file dword-wise (`MRel`) and the invariant on `%zmm24`, `%zmm25` and `%k1`
(`Inv`); `lowerProg_sim` composes it over a program between a prologue that loads the
constants and the state and an epilogue that stores register 0. Every instruction has
operands fixed by the program, so `ZmmTextLeakage.parse_constant_time` applies to the
parsed text: the permutation indices and blend masks are constants of the text.

`emitChecked` prints the lowered program as AT&T text, parses it back with
`ZmmTextValidate.parse`, and returns the text only when the parsed program is the
lowering and the parsed data table holds every constant vector at its label
(`roCheck`). `emitChecked_sound` states what a returned text computes on the machine
model.

## Main definitions

* `mulSeq`, `lowerInstr`, `lowerProg`: the lowering.
* `MRel`, `Inv`: the simulation relation and the machine invariant.
* `instrText`, `renderText`, `cLabel`: the text.
* `roCheck`, `emitChecked`: the checked emitter.

## Main results

* `lane_mulVal`: the Montgomery-product sequence computes `mmulW` on every dword.
* `lowerInstr_sim`, `lowerBody_sim`, `lowerProg_sim`: the machine simulates the IR.
* `roCheck_sound`, `emitChecked_sound`: soundness of the checked emitter.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.PackedStateRender

open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel
open CatCrypt.Crypto.SecureCompilation.VIR.PackedStateEmit
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp mulHiW)
open CatCrypt.Crypto.SecureCompilation.RangeDomain (umin)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextValidate (parse)

/-! ## 1. Dword lanes of the machine operations -/

/-- Dword `2i` of a `vpmuludq` product is the low word of the product of the even
    dwords. -/
theorem lane_muludq_even (x y : BitVec 512) (i : Nat) (hi : i < 8) :
    lane 32 (semLW 64 .muludq x y) (2 * i) = lane 32 x (2 * i) * lane 32 y (2 * i) := by
  rw [lane32_even, lane_semLW _ _ _ (by norm_num) (by omega)]
  simp only [LOp.apply]
  rw [← lane32_even, ← lane32_even, lo_mul_setWidth]

/-- Dword `2i+1` of a `vpmuludq` product is the high word of the product of the even
    dwords. -/
theorem lane_muludq_odd (x y : BitVec 512) (i : Nat) (hi : i < 8) :
    lane 32 (semLW 64 .muludq x y) (2 * i + 1) = mulHiW (lane 32 x (2 * i)) (lane 32 y (2 * i)) := by
  rw [lane32_odd, lane_semLW _ _ _ (by norm_num) (by omega)]
  simp only [LOp.apply]
  rw [← lane32_even, ← lane32_even, hi_mul_setWidth]

/-- Dword `j` of a dword operation. -/
theorem lane_lw32 (o : LOp) (x y : BitVec 512) {j : Nat} (hj : j < 16) :
    lane 32 (semLW 32 o x y) j = o.apply (lane 32 x j) (lane 32 y j) :=
  lane_semLW _ _ _ (by norm_num) (by omega)

/-- Dword `j` of `vmovshdup`. -/
theorem lane_shdup (x : BitVec 512) {j : Nat} (hj : j < 16) :
    lane 32 (semDup true x) j = lane 32 x (2 * (j / 2) + 1) := by
  rw [lane_semDup _ _ hj]; rfl

/-- The even-dword mask `0x5555`. -/
abbrev evenMask : BitVec 16 := 0x5555

theorem evenMask_even (i : Nat) (hi : i < 8) : evenMask.getLsbD (2 * i) = true := by
  revert i; decide

theorem evenMask_odd (i : Nat) (hi : i < 8) : evenMask.getLsbD (2 * i + 1) = false := by
  revert i; decide

/-- The value the Montgomery-product sequence leaves: `vpmuludq` of the even dwords and
    of the odd dwords (moved down by `vmovshdup`), the low words times `mu`, those times
    `p`, the two differences of high words merged by a masked `vmovshdup`, and the
    unsigned minimum of `d` and `d + p`. -/
def mulVal (P MU A B : BitVec 512) (k : BitVec 16) : BitVec 512 :=
  let PE := semLW 64 .muludq A B
  let PO := semLW 64 .muludq (semDup true A) (semDup true B)
  let QPE := semLW 64 .muludq (semLW 64 .muludq PE MU) P
  let QPO := semLW 64 .muludq (semLW 64 .muludq PO MU) P
  let D := semMerge k (semDup true (semLW 32 (.bin .sub) PE QPE))
    (semLW 32 (.bin .sub) PO QPO)
  semLW 32 .minu D (semLW 32 (.bin .add) D P)

/-- **The Montgomery-product sequence computes `mmulW` on every dword**, when every
    dword of `P` is `p` and every dword of `MU` is `mu`. -/
theorem lane_mulVal (P MU A B : BitVec 512) (p mu : BitVec 32)
    (hP : ∀ j < 16, lane 32 P j = p) (hMU : ∀ j < 16, lane 32 MU j = mu)
    {j : Nat} (hj : j < 16) :
    lane 32 (mulVal P MU A B evenMask) j = mmulW p mu (lane 32 A j) (lane 32 B j) := by
  unfold mulVal mmulW
  simp only
  rw [lane_lw32 _ _ _ hj, lane_lw32 _ _ _ hj, hP j hj, lane_semMerge _ _ _ hj]
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
  · have hi : i < 8 := by omega
    rw [evenMask_even i hi, ite_eq_left rfl, lane_shdup _ hj,
      show 2 * (2 * i / 2) + 1 = 2 * i + 1 by omega, lane_lw32 _ _ _ (by omega),
      lane_muludq_odd _ _ _ hi, lane_muludq_odd _ _ _ hi, lane_muludq_even _ _ _ hi,
      lane_muludq_even _ _ _ hi, hP _ (by omega), hMU _ (by omega)]
    rfl
  · have hi : i < 8 := by omega
    rw [evenMask_odd i hi, ite_eq_right (by simp), lane_lw32 _ _ _ hj,
      lane_muludq_odd _ _ _ hi, lane_muludq_odd _ _ _ hi, lane_muludq_even _ _ _ hi,
      lane_muludq_even _ _ _ hi, hP _ (by omega), hMU _ (by omega), lane_shdup _ (by omega),
      lane_shdup _ (by omega), show 2 * (2 * i / 2) + 1 = 2 * i + 1 by omega]
    rfl

/-! ## 2. The lowering -/

/-- The machine register of an IR register. -/
def mreg (r : PReg) : Fin 32 := ⟨r.val, by omega⟩

theorem mreg_ne (r : PReg) (k : Fin 32) (hk : 24 ≤ k.val) : mreg r ≠ k := by
  intro h; have := congrArg Fin.val h; simp [mreg] at this; omega

theorem mreg_lit (r : PReg) : mreg r ≠ 24 ∧ mreg r ≠ 25 ∧ mreg r ≠ 26 ∧ mreg r ≠ 27 ∧
    mreg r ≠ 28 ∧ mreg r ≠ 29 ∧ mreg r ≠ 30 ∧ mreg r ≠ 31 :=
  ⟨mreg_ne r _ (by decide), mreg_ne r _ (by decide), mreg_ne r _ (by decide),
    mreg_ne r _ (by decide), mreg_ne r _ (by decide), mreg_ne r _ (by decide),
    mreg_ne r _ (by decide), mreg_ne r _ (by decide)⟩

theorem lit_mreg (r : PReg) : (24 : Fin 32) ≠ mreg r ∧ (25 : Fin 32) ≠ mreg r ∧
    (26 : Fin 32) ≠ mreg r ∧ (27 : Fin 32) ≠ mreg r ∧ (28 : Fin 32) ≠ mreg r ∧
    (29 : Fin 32) ≠ mreg r ∧ (30 : Fin 32) ≠ mreg r ∧ (31 : Fin 32) ≠ mreg r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := mreg_lit r
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, h7.symm, h8.symm⟩

theorem mreg_inj {r s : PReg} (h : mreg r = mreg s) : r = s := by
  apply Fin.ext; have := congrArg Fin.val h; simpa [mreg] using this

/-- A machine state with scratch register values: the state after writing `v` to a
    register at or above 24 keeps every IR register. -/
theorem setZ_mreg (σ : MState) (k : Fin 32) (hk : 24 ≤ k.val) (v : BitVec 512) (r : PReg) :
    (σ.setZ k v).zmm (mreg r) = σ.zmm (mreg r) := by
  simp [MState.setZ, mreg_ne r k hk]

/-- The dword words of an index vector. -/
def idxWords (idx : Fin 16 → Fin 16) : Fin 16 → BitVec 32 :=
  fun j => BitVec.ofNat 32 (idx j).val

/-- The mask word of a lane mask: bit `j` is `m j`. -/
def maskWord (m : Fin 16 → Bool) : BitVec 32 :=
  BitVec.ofFnLE fun i : Fin 32 => if h : i.val < 16 then m ⟨i.val, h⟩ else false

/-- The vector with `p` in every dword. -/
def pVec (mp : MontParams) : Fin 16 → BitVec 32 := fun _ => BitVec.ofNat 32 mp.p

/-- The vector with `mu` in every dword. -/
def muVec (mp : MontParams) : Fin 16 → BitVec 32 := fun _ => BitVec.ofNat 32 mp.mu

/-- The Montgomery product of registers `a` and `b` into `d`, over the scratch registers
    26 to 31, with `p` in register 24, `mu` in register 25 and the even-dword mask in
    `%k1`. -/
def mulSeq (a b d : Fin 32) : List Instr :=
  [.dup true a 26 none, .dup true b 27 none,
   .op 64 .muludq (.reg b) a 28, .op 64 .muludq (.reg 27) 26 29,
   .op 64 .muludq (.reg 25) 28 30, .op 64 .muludq (.reg 25) 29 31,
   .op 64 .muludq (.reg 24) 30 30, .op 64 .muludq (.reg 24) 31 31,
   .op 32 (.bin .sub) (.reg 30) 28 28, .op 32 (.bin .sub) (.reg 31) 29 29,
   .dup true 28 29 (some 1),
   .op 32 (.bin .add) (.reg 24) 29 26, .op 32 .minu (.reg 26) 29 d]

/-- The machine instructions of one IR instruction; `L` names the data label of a
    constant vector. The sum and difference use the scratch registers 26 and 27, a
    permutation loads its index vector into register 26, a blend sets `%k2`. -/
def lowerInstr (L : (Fin 16 → BitVec 32) → String) : PInstr → List Instr
  | .cst d c => [.ldC (.full (L c)) (mreg d)]
  | .mov d a => [.mova (mreg a) (mreg d)]
  | .add d a b => [.op 32 (.bin .add) (.reg (mreg b)) (mreg a) 26,
      .op 32 (.bin .sub) (.reg 24) 26 27, .op 32 .minu (.reg 27) 26 (mreg d)]
  | .sub d a b => [.op 32 (.bin .sub) (.reg (mreg b)) (mreg a) 26,
      .op 32 (.bin .add) (.reg 24) 26 27, .op 32 .minu (.reg 27) 26 (mreg d)]
  | .mul d a b => mulSeq (mreg a) (mreg b) (mreg d)
  | .perm d a idx => [.ldC (.full (L (idxWords idx))) 26, .perm (mreg a) 26 (mreg d)]
  | .blend d a b m => [.movEax (maskWord m), .kmov 2, .blend 2 (mreg a) (mreg b) (mreg d)]

/-- The constant vectors an instruction reads from the data table. -/
def instrConsts : PInstr → List (Fin 16 → BitVec 32)
  | .cst _ c => [c]
  | .perm _ _ idx => [idxWords idx]
  | _ => []

/-- The data table holds the constant vector `c` at label `L c`. -/
def RoHas (ro : Std.HashMap String (Array (BitVec 64))) (L : (Fin 16 → BitVec 32) → String)
    (c : Fin 16 → BitVec 32) : Prop :=
  ∃ v, csrcVal .zmm ro (.full (L c)) = some v ∧ ∀ j : Fin 16, lane 32 v j = c j

/-! ## 3. Simulation of the IR by the machine -/

/-- Register `r` of the IR is dword-wise machine register `r`. -/
def MRel (W : Regs (BitVec 32)) (σ : MState) : Prop :=
  ∀ (r : PReg) (j : Fin 16), lane 32 (σ.zmm (mreg r)) j = W r j

/-- The machine invariant: `p` in every dword of register 24, `mu` in every dword of
    register 25, the even-dword mask in `%k1`. -/
structure Inv (mp : MontParams) (σ : MState) : Prop where
  p : ∀ j < 16, lane 32 (σ.zmm 24) j = BitVec.ofNat 32 mp.p
  mu : ∀ j < 16, lane 32 (σ.zmm 25) j = BitVec.ofNat 32 mp.mu
  k1 : σ.kr 1 = evenMask

theorem sim_add (mp : MontParams) (L : (Fin 16 → BitVec 32) → String)
    (ro : Std.HashMap String (Array (BitVec 64))) (inp : Nat → BitVec 512)
    (d a b : PReg) (W : Regs (BitVec 32)) (σ : MState) (hR : MRel W σ) (hI : Inv mp σ) :
    ∃ σ', run .zmm inp ro σ (lowerInstr L (.add d a b)) = some σ' ∧
      MRel ((PInstr.add d a b).step (wordAlg mp) W) σ' ∧ Inv mp σ' ∧ σ'.log = σ.log := by
  unfold MRel at hR
  refine ⟨_, rfl, ?_, ?_, rfl⟩
  · intro r j
    by_cases hr : r = d
    · subst hr
      simp [MState.setZ, wr, PInstr.step, PInstr.val, PInstr.dst, wordAlg, maddW, lane_lw32,
        LOp.apply, mreg_lit, lit_mreg, hR, hI.p _ j.isLt, JasminBinOp.apply]
    · have hne : mreg r ≠ mreg d := fun h => hr (mreg_inj h)
      simp [MState.setZ, PInstr.step, PInstr.dst, hne, mreg_lit, Function.update_of_ne hr, hR]
  · exact ⟨fun j hj => by simp [MState.setZ, lit_mreg, hI.p j hj],
      fun j hj => by simp [MState.setZ, lit_mreg, hI.mu j hj], hI.k1⟩

theorem maskWord_getLsbD (m : Fin 16 → Bool) (j : Fin 16) :
    (maskWord m).getLsbD j.val = m j := by
  have h32 : j.val < 32 := by omega
  simp [maskWord, BitVec.getLsbD_ofFnLE, h32]

theorem mulSeq_zmm (inp : Nat → BitVec 512) (ro : Std.HashMap String (Array (BitVec 64)))
    (σ : MState) (a b d : PReg) :
    ∃ σ', run .zmm inp ro σ (mulSeq (mreg a) (mreg b) (mreg d)) = some σ' ∧
      σ'.zmm (mreg d) = mulVal (σ.zmm 24) (σ.zmm 25) (σ.zmm (mreg a)) (σ.zmm (mreg b)) (σ.kr 1) ∧
      (∀ r : PReg, r ≠ d → σ'.zmm (mreg r) = σ.zmm (mreg r)) ∧
      σ'.zmm 24 = σ.zmm 24 ∧ σ'.zmm 25 = σ.zmm 25 ∧ σ'.kr = σ.kr ∧ σ'.log = σ.log := by
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp [MState.setZ, wr, mreg_lit, lit_mreg, mulVal]
  · intro r hr
    have hne : mreg r ≠ mreg d := fun h => hr (mreg_inj h)
    simp [MState.setZ, hne, mreg_lit]
  · simp [MState.setZ, lit_mreg]
  · simp [MState.setZ, lit_mreg]

/-- **One IR instruction is simulated by its machine instructions.** From a machine
    state holding the IR register file `W` dword-wise and the invariant, with the data
    table holding the instruction's constant vectors, the lowered instructions run and
    leave a state holding the IR register file after the instruction, the invariant, and
    the same stores. -/
theorem lowerInstr_sim (mp : MontParams) (L : (Fin 16 → BitVec 32) → String)
    (ro : Std.HashMap String (Array (BitVec 64))) (inp : Nat → BitVec 512) (i : PInstr)
    (hro : ∀ c ∈ instrConsts i, RoHas ro L c) (W : Regs (BitVec 32)) (σ : MState)
    (hR : MRel W σ) (hI : Inv mp σ) :
    ∃ σ', run .zmm inp ro σ (lowerInstr L i) = some σ' ∧
      MRel (i.step (wordAlg mp) W) σ' ∧ Inv mp σ' ∧ σ'.log = σ.log := by
  unfold MRel at hR
  have hInvZ : ∀ (d : PReg) (v : BitVec 512), Inv mp (σ.setZ (mreg d) v) := fun d v =>
    ⟨fun j hj => by simp [MState.setZ, lit_mreg, hI.p j hj],
      fun j hj => by simp [MState.setZ, lit_mreg, hI.mu j hj], hI.k1⟩
  cases i with
  | cst d c =>
    obtain ⟨v, hv, hl⟩ := hro c (by simp [instrConsts])
    refine ⟨σ.setZ (mreg d) (wr .zmm v), by simp [lowerInstr, run, step, hv], ?_, hInvZ d _,
      rfl⟩
    intro r j
    by_cases hr : r = d
    · subst hr
      simp [MState.setZ, wr, PInstr.step, PInstr.val, PInstr.dst, wordAlg, hl]
    · have hne : mreg r ≠ mreg d := fun h => hr (mreg_inj h)
      simp [MState.setZ, PInstr.step, PInstr.dst, hne, Function.update_of_ne hr, hR]
  | mov d a =>
    refine ⟨_, rfl, ?_, hInvZ d _, rfl⟩
    intro r j
    by_cases hr : r = d
    · subst hr
      simp [MState.setZ, wr, PInstr.step, PInstr.val, PInstr.dst, hR]
    · have hne : mreg r ≠ mreg d := fun h => hr (mreg_inj h)
      simp [MState.setZ, PInstr.step, PInstr.dst, hne, Function.update_of_ne hr, hR]
  | add d a b => exact sim_add mp L ro inp d a b W σ hR hI
  | sub d a b =>
    refine ⟨_, rfl, ?_, ?_, rfl⟩
    · intro r j
      by_cases hr : r = d
      · subst hr
        simp [MState.setZ, wr, PInstr.step, PInstr.val, PInstr.dst, wordAlg, msubW, lane_lw32,
          LOp.apply, mreg_lit, lit_mreg, hR, hI.p _ j.isLt, JasminBinOp.apply]
      · have hne : mreg r ≠ mreg d := fun h => hr (mreg_inj h)
        simp [MState.setZ, PInstr.step, PInstr.dst, hne, mreg_lit, Function.update_of_ne hr, hR]
    · exact ⟨fun j hj => by simp [MState.setZ, lit_mreg, hI.p j hj],
        fun j hj => by simp [MState.setZ, lit_mreg, hI.mu j hj], hI.k1⟩
  | mul d a b =>
    obtain ⟨σ', hrun, hd, hother, h24, h25, hkr, hlog⟩ := mulSeq_zmm inp ro σ a b d
    refine ⟨σ', hrun, ?_, ⟨fun j hj => by rw [h24]; exact hI.p j hj,
      fun j hj => by rw [h25]; exact hI.mu j hj, by rw [hkr]; exact hI.k1⟩, hlog⟩
    intro r j
    by_cases hr : r = d
    · subst hr
      rw [hd, hI.k1, lane_mulVal _ _ _ _ _ _ hI.p hI.mu j.isLt, hR a j, hR b j]
      simp [PInstr.step, PInstr.val, PInstr.dst, wordAlg]
    · rw [hother r hr, hR r j]
      simp [PInstr.step, PInstr.dst, Function.update_of_ne hr]
  | perm d a idx =>
    obtain ⟨v, hv, hl⟩ := hro (idxWords idx) (by simp [instrConsts])
    refine ⟨(σ.setZ 26 (wr .zmm v)).setZ (mreg d)
      (wr .zmm (semPerm 16 ((σ.setZ 26 (wr .zmm v)).zmm (mreg a)) (wr .zmm v))),
      by simp [lowerInstr, run, step, hv, Mode.act, MState.setZ], ?_, ?_, rfl⟩
    · intro r j
      by_cases hr : r = d
      · subst hr
        have hidx : (lane 32 v j).toNat % 16 = (idx j).val := by
          have h16 := (idx j).isLt
          rw [hl j]
          simp only [idxWords, BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (show (idx j).val < 2 ^ 32 by omega), Nat.mod_eq_of_lt h16]
        simp only [MState.setZ, ite_eq_left, wr]
        rw [lane_semPerm _ _ _ j.isLt, hidx]
        simp [mreg_lit, hR, PInstr.step, PInstr.val, PInstr.dst]
      · have hne : mreg r ≠ mreg d := fun h => hr (mreg_inj h)
        simp [MState.setZ, PInstr.step, PInstr.dst, hne, mreg_lit, Function.update_of_ne hr, hR]
    · exact ⟨fun j hj => by simp [MState.setZ, lit_mreg, hI.p j hj],
        fun j hj => by simp [MState.setZ, lit_mreg, hI.mu j hj], hI.k1⟩
  | blend d a b m =>
    refine ⟨_, rfl, ?_, ?_, rfl⟩
    · intro r j
      by_cases hr : r = d
      · subst hr
        simp only [MState.setZ, ite_eq_left, wr]
        rw [lane_semMerge _ _ _ j.isLt]
        simp [maskWord_getLsbD, hR, PInstr.step, PInstr.val, PInstr.dst]
      · have hne : mreg r ≠ mreg d := fun h => hr (mreg_inj h)
        simp [MState.setZ, PInstr.step, PInstr.dst, hne, Function.update_of_ne hr, hR]
    · exact ⟨fun j hj => by simp [MState.setZ, lit_mreg, hI.p j hj],
        fun j hj => by simp [MState.setZ, lit_mreg, hI.mu j hj], by simp [MState.setZ, hI.k1]⟩

theorem run_append (m : Mode) (inp : Nat → BitVec 512)
    (ro : Std.HashMap String (Array (BitVec 64))) :
    ∀ (p q : List Instr) (σ : MState),
      run m inp ro σ (p ++ q) = (run m inp ro σ p).bind fun σ' => run m inp ro σ' q
  | [], _, _ => rfl
  | i :: is, q, σ => by
    simp only [List.cons_append, run]
    cases step m inp ro σ i with
    | none => rfl
    | some σ1 => exact run_append m inp ro is q σ1

/-- The constant vectors a program reads from the data table. -/
def progConsts (prog : List PInstr) : List (Fin 16 → BitVec 32) := prog.flatMap instrConsts

/-- **A program is simulated by its lowering.** -/
theorem lowerBody_sim (mp : MontParams) (L : (Fin 16 → BitVec 32) → String)
    (ro : Std.HashMap String (Array (BitVec 64))) (inp : Nat → BitVec 512) :
    ∀ (prog : List PInstr) (W : Regs (BitVec 32)) (σ : MState),
      (∀ c ∈ progConsts prog, RoHas ro L c) → MRel W σ → Inv mp σ →
      ∃ σ', run .zmm inp ro σ (prog.flatMap (lowerInstr L)) = some σ' ∧
        MRel (exec (wordAlg mp) prog W) σ' ∧ Inv mp σ' ∧ σ'.log = σ.log
  | [], W, σ, _, hR, hI => ⟨σ, rfl, hR, hI, rfl⟩
  | i :: is, W, σ, hro, hR, hI => by
    obtain ⟨σ1, h1, hR1, hI1, hl1⟩ := lowerInstr_sim mp L ro inp i
      (fun c hc => hro c (by simp only [progConsts, List.flatMap_cons, List.mem_append]; exact .inl hc))
      W σ hR hI
    obtain ⟨σ2, h2, hR2, hI2, hl2⟩ := lowerBody_sim mp L ro inp is _ σ1
      (fun c hc => hro c (by simp only [progConsts, List.flatMap_cons, List.mem_append]; exact .inr hc))
      hR1 hI1
    refine ⟨σ2, ?_, hR2, hI2, hl2.trans hl1⟩
    rw [List.flatMap_cons, run_append, h1, Option.bind_some, h2]

/-- The prologue: `p` and `mu` into registers 24 and 25, the even-dword mask into
    `%k1`. -/
def prologue (mp : MontParams) (L : (Fin 16 → BitVec 32) → String) : List Instr :=
  [.ldC (.full (L (pVec mp))) 24, .ldC (.full (L (muVec mp))) 25,
   .movEax (BitVec.ofNat 32 0x5555), .kmov 1]

/-- The machine program of an IR program on the state in register 0: the prologue, the
    state loaded from input offset 0, the lowered body, the state stored at output
    offset 0. -/
def lowerProg (mp : MontParams) (L : (Fin 16 → BitVec 32) → String) (prog : List PInstr) :
    List Instr :=
  prologue mp L ++ [.ldIn 0 0] ++ prog.flatMap (lowerInstr L) ++ [.st 0 0]

/-- The state after the prologue and the load of the state. -/
def afterPrologue (σ : MState) (vp vm x : BitVec 512) : MState :=
  { zmm := fun r => if r = 0 then x else if r = 25 then vm else if r = 24 then vp else σ.zmm r,
    eax := BitVec.ofNat 32 0x5555,
    kr := fun k => if k = 1 then (BitVec.ofNat 32 0x5555).setWidth 16 else σ.kr k,
    log := σ.log, stk := σ.stk }

/-- **Soundness of the lowering.** When the data table holds `p`, `mu` and the program's
    constant vectors, the machine program runs from any state with no stores and stores
    at output offset 0 a value whose dwords are register 0 of the IR run from a register
    file whose register 0 holds the dwords of the input at offset 0. -/
theorem lowerProg_sim (mp : MontParams) (L : (Fin 16 → BitVec 32) → String)
    (ro : Std.HashMap String (Array (BitVec 64))) (inp : Nat → BitVec 512)
    (prog : List PInstr)
    (hro : ∀ c ∈ pVec mp :: muVec mp :: progConsts prog, RoHas ro L c) (σ : MState) :
    ∃ W : Regs (BitVec 32), (∀ j : Fin 16, W 0 j = lane 32 (inp 0) j) ∧
      ∃ σ', run .zmm inp ro σ (lowerProg mp L prog) = some σ' ∧
        ∃ y, σ'.outAt 0 = some y ∧ ∀ j : Fin 16, lane 32 y j = exec (wordAlg mp) prog W 0 j := by
  obtain ⟨vp, hvp, hlp⟩ := hro (pVec mp) (by simp)
  obtain ⟨vm, hvm, hlm⟩ := hro (muVec mp) (by simp)
  obtain ⟨σ0, hpro, hσ0⟩ : ∃ σ0, run .zmm inp ro σ (prologue mp L ++ [.ldIn 0 0]) = some σ0 ∧
      σ0 = afterPrologue σ vp vm (inp 0) :=
    ⟨_, by simp [prologue, run, step, hvp, hvm, afterPrologue, MState.setZ, wr], rfl⟩
  have hI0 : Inv mp σ0 := by
    subst hσ0
    exact ⟨fun j hj => by simp [afterPrologue]; exact hlp ⟨j, hj⟩,
      fun j hj => by simp [afterPrologue]; exact hlm ⟨j, hj⟩, rfl⟩
  refine ⟨fun r j => lane 32 (σ0.zmm (mreg r)) j, fun j => by subst hσ0; rfl, ?_⟩
  obtain ⟨σ1, h1, hR1, -, -⟩ := lowerBody_sim mp L ro inp prog _ σ0
    (fun c hc => hro c (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hc)))
    (fun r j => rfl) hI0
  refine ⟨{ σ1 with log := (0, wr .zmm (σ1.zmm 0)) :: σ1.log }, ?_, σ1.zmm 0, ?_,
    fun j => hR1 0 j⟩
  · rw [lowerProg, run_append, run_append, hpro, Option.bind_some, h1, Option.bind_some]
    rfl
  · simp [MState.outAt, wr]

/-! ## 4. The text and the checked emitter -/

/-- A word as eight hexadecimal digits. -/
def hex8 (w : BitVec 32) : String :=
  let s := Nat.toDigits 16 w.toNat
  String.ofList (List.replicate (8 - s.length) '0' ++ s)

/-- The data label of a constant vector: `.Lps_` followed by its dwords in hexadecimal. -/
def cLabel (c : Fin 16 → BitVec 32) : String :=
  ".Lps_" ++ String.join ((List.finRange 16).map fun j => hex8 (c j))

/-- A vector register name. -/
def zr (r : Fin 32) : String := "%zmm" ++ toString r.val

/-- The mnemonics of the lane-wise operations the lowering emits. -/
def lopText : Nat → LOp → Option String
  | 32, .bin .add => some "vpaddd"
  | 32, .bin .sub => some "vpsubd"
  | 32, .minu => some "vpminud"
  | 64, .muludq => some "vpmuludq"
  | _, _ => none

/-- The AT&T line of an instruction the lowering emits. -/
def instrText : Instr → Except String String
  | .ldIn off d => .ok s!"\tvmovdqu64 {off}(%rsi), {zr d}"
  | .ldC (.full l) d => .ok s!"\tvmovdqu64 {l}(%rip), {zr d}"
  | .st r off => .ok s!"\tvmovdqu64 {zr r}, {off}(%rdi)"
  | .op L o (.reg s2) s1 d =>
    match lopText L o with
    | some mn => .ok s!"\t{mn} {zr s2}, {zr s1}, {zr d}"
    | none => .error "packed render: a lane-wise operation without a mnemonic"
  | .dup true a d none => .ok s!"\tvmovshdup {zr a}, {zr d}"
  | .dup true a d (some k) => .ok s!"\tvmovshdup {zr a}, {zr d}\{%k{k.val}}"
  | .mova a d => .ok s!"\tvmovdqa64 {zr a}, {zr d}"
  | .movEax imm => .ok s!"\tmovl ${imm.toNat}, %eax"
  | .kmov k => .ok s!"\tkmovw %eax, %k{k.val}"
  | .perm s i d => .ok s!"\tvpermd {zr s}, {zr i}, {zr d}"
  | .blend k a b d => .ok s!"\tvpblendmd {zr a}, {zr b}, {zr d}\{%k{k.val}}"
  | _ => .error "packed render: an instruction outside the packed-state forms"

/-- The data lines of a constant vector at its label: 64-byte alignment, the label, eight
    quadwords (dword `2i` low). -/
def dataLines (c : Fin 16 → BitVec 32) : List String :=
  ["\t.p2align 6", cLabel c ++ ":"] ++ (List.finRange 8).map fun i =>
    "\t.quad " ++ toString ((c ⟨2 * i.val, by omega⟩).toNat
      + (c ⟨2 * i.val + 1, by omega⟩).toNat * 2 ^ 32)

/-- The constant vectors with distinct labels, first occurrence first. -/
def distinctConsts (cs : List (Fin 16 → BitVec 32)) : List (Fin 16 → BitVec 32) :=
  (cs.foldl (fun (acc : List String × List (Fin 16 → BitVec 32)) c =>
    if acc.1.contains (cLabel c) then acc else (cLabel c :: acc.1, c :: acc.2)) ([], [])).2.reverse

/-- The AT&T text of the function `sym`: the instructions, the epilogue, and the data
    table of the constant vectors `cs`. -/
def renderText (sym : String) (prog : List Instr) (cs : List (Fin 16 → BitVec 32)) :
    Except String String := do
  let body ← prog.mapM instrText
  let lines := ["\t.text", "\t.globl " ++ sym, "\t.type " ++ sym ++ ", @function", sym ++ ":"]
    ++ body ++ ["\tvzeroupper", "\tret", "\t.size " ++ sym ++ ", .-" ++ sym, "\t.section .rodata"]
    ++ (distinctConsts cs).flatMap dataLines
    ++ ["\t.section .note.GNU-stack,\"\",@progbits", ""]
  return "\n".intercalate lines

/-- Whether the data table holds every constant vector of `cs` at its label. -/
def roCheck (ro : Std.HashMap String (Array (BitVec 64))) (L : (Fin 16 → BitVec 32) → String)
    (cs : List (Fin 16 → BitVec 32)) : Bool :=
  cs.all fun c =>
    match csrcVal .zmm ro (.full (L c)) with
    | some v => (List.finRange 16).all fun j => lane 32 v j == c j
    | none => false

theorem roCheck_sound {ro : Std.HashMap String (Array (BitVec 64))}
    {L : (Fin 16 → BitVec 32) → String} {cs : List (Fin 16 → BitVec 32)}
    (h : roCheck ro L cs = true) : ∀ c ∈ cs, RoHas ro L c := by
  intro c hc
  have h1 := List.all_eq_true.mp h c hc
  cases e : csrcVal .zmm ro (.full (L c)) with
  | none => rw [e] at h1; cases h1
  | some v =>
    rw [e] at h1
    exact ⟨v, e, fun j => by
      have := List.all_eq_true.mp h1 j (List.mem_finRange j)
      simpa using this⟩

/-- **The checked packed-state emitter.** Renders the lowering of `prog` as the function
    `sym`, parses the text back, and returns it only when the parsed program is the
    lowering and the parsed data table holds `p`, `mu` and the program's constant
    vectors. -/
def emitChecked (mp : MontParams) (sym : String) (prog : List PInstr) :
    Except String String :=
  match renderText sym (lowerProg mp cLabel prog) (pVec mp :: muVec mp :: progConsts prog) with
  | .error e => .error e
  | .ok text =>
    match parse .zmm text with
    | .error e => .error ("packed render: the text does not parse: " ++ e)
    | .ok (mprog, ro) =>
      if mprog = lowerProg mp cLabel prog ∧
          roCheck ro cLabel (pVec mp :: muVec mp :: progConsts prog) = true then .ok text
      else .error "packed render: the parsed text is not the lowered program"

/-- **Soundness of the checked emitter.** A text `emitChecked` returns parses to a
    program that, from any machine state, stores at output offset 0 a value whose dwords
    are register 0 of the IR run of `prog` from a register file whose register 0 holds
    the dwords of the input at offset 0. -/
theorem emitChecked_sound {mp : MontParams} {sym : String} {prog : List PInstr}
    {text : String} (h : emitChecked mp sym prog = .ok text) :
    ∃ mprog ro, parse .zmm text = .ok (mprog, ro) ∧
      ∀ (inp : Nat → BitVec 512) (σ : MState),
        ∃ W : Regs (BitVec 32), (∀ j : Fin 16, W 0 j = lane 32 (inp 0) j) ∧
          ∃ σ', run .zmm inp ro σ mprog = some σ' ∧
            ∃ y, σ'.outAt 0 = some y ∧
              ∀ j : Fin 16, lane 32 y j = exec (wordAlg mp) prog W 0 j := by
  unfold emitChecked at h
  split at h
  · cases h
  · rename_i text' _
    split at h
    · cases h
    · rename_i mprog ro hp
      split at h
      · rename_i hc
        cases h
        obtain ⟨rfl, hro⟩ := hc
        exact ⟨_, ro, hp, fun inp σ =>
          lowerProg_sim mp cLabel ro inp prog (roCheck_sound hro) σ⟩
      · cases h

end CatCrypt.Crypto.SecureCompilation.VIR.PackedStateRender
