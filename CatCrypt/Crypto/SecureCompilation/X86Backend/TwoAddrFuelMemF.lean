/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVTwoAddr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi

@[expose] public section

set_option autoImplicit false

/-!
# Two-address legalisation on the flag machine

`TwoAddrLegalize.twoAddrBody` rewrites an untied instruction `opn d, [a, b]` by one of four
routes (`OwnedLprogTV.twoAddrRoute`): the flag route of `CMP` and `TEST`, the copy route
`mov d, a; opn d, [d, b]`, the commutative route `opn d, [d, a]`, and the scratch route through
`R15` saved in the frame slot `qsave.R15`. `TwoAddrLegalize.twoAddrBody_lsemStraight` states the
pass on straight-line bodies of the machine `lsemStraight`. This module states it on whole
bodies of the flag machine `lsemFuelMemF`, the machine of the region back end.

The pass expands one instruction at a time and keeps every label, conditional branch and goto
(`OwnedLprogTV.twoAddrBody_typedR`), so the theorem is an instance of the expansion lift
`JasminLsemExportLower.lsemFuelMemF_expand`. The state relation is `AgreeT ok`: the registers
agree off the save slot `qsave.R15` when the scratch route is enabled (`ok`), and everywhere
otherwise; the arrays, the word memory and the carry and overflow flags agree.

## Method

* An instruction that reads no name off which two states disagree steps alike from them
  (`fstepF_agreeT`, from the congruence `JasminLsemAddrCongr.fstepF_congr`).
* A two-source operation computes the same word whatever its destination
  (`fstepF_dst`, through `lsemStepN_dst`, `lsemStepSh_dst`, `lsemStepMC_dst`,
  `lsemStepCast_dst`).
* A commutative operation computes the same word and flags with its register sources
  exchanged (`fstepF_comm`).
* The copy route is `JasminLsemExportLower.fstepF_twoAddr`; the scratch route is the copy
  route at `R15`, after the save and the destination rename, followed by the copy into the
  destination and the restore (`runStraightF_scratch`).

## Main definitions

* `KeptT`, `AgreeT`: the names the pass keeps and the agreement of two bases on them.
* `legalRM`: the typed legalisation of one instruction.
* `twoAddrOKI`, `twoAddrOK`: the decidable side conditions of the theorem.

## Main results

* `instrOK_legalRM`: the per-instruction condition of the expansion lift.
* `twoAddrBody_lsemFuelMemF`: every halting run of a body that passes `twoAddrOK` is matched by
  a halting run of its legalisation with at most five times the fuel.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrFuelMemF

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (cellParts?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames fstepF_frame_dst)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (clsB clsB_spec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize
  (commBases movFor tieBase isRegOrImm twoAddrBody bodyAvoids instrAvoids opAvoids
   mentionsScratch scratchSave)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
  (commOpns typeBody TagFirstSrc TwoAddrRoute twoAddrRoute legalR twoAddrRouteWF
   twoAddrBody_typedR)

/-! ## 1. The destination of a two-source operation -/

/-- The register step of a two-source instruction writes, at any destination `D'`, the word it
    writes at `D`. -/
theorem lsemStepN_dst (opn : String) (a b : LOperand) (D D' : String) (s : LstateN) :
    lsemStepN (.Lopn [.reg D'] opn [a, b]) s =
      (lsemStepN (.Lopn [.reg D] opn [a, b]) s).map
        (fun t => (s.setReg D' (t.lvm D).2).nextPc) := by
  cases a <;> cases b <;> simp only [lsemStepN, immFirstN] <;> (repeat' split) <;>
    simp_all [LstateN.setReg, LstateN.nextPc, Option.map_map, Function.comp_def]

theorem lsemStepSh_dst (opn : String) (a b : LOperand) (D D' : String) (s : LstateN) :
    lsemStepSh (.Lopn [.reg D'] opn [a, b]) s =
      (lsemStepSh (.Lopn [.reg D] opn [a, b]) s).map
        (fun t => (s.setReg D' (t.lvm D).2).nextPc) := by
  cases a <;> cases b <;> simp only [lsemStepSh, sarStruct?] <;> (try split_ifs) <;>
    (try exact lsemStepN_dst opn _ _ D D' s)
  all_goals
    rename_i x n h
    cases hr : readReg s (.reg x) with
    | none => simp [hr]
    | some p => obtain ⟨w, v⟩ := p; simp [hr, LstateN.setReg, LstateN.nextPc]

theorem lsemStepMC_dst (opn : String) (a b : LOperand) (D D' : String) (s : LstateN) :
    lsemStepMC (.Lopn [.reg D'] opn [a, b]) s =
      (lsemStepMC (.Lopn [.reg D] opn [a, b]) s).map
        (fun t => (s.setReg D' (t.lvm D).2).nextPc) := by
  cases a <;> cases b <;>
    simp only [lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?,
      sbbhiStruct?] <;> (try split_ifs) <;>
    (try exact lsemStepSh_dst opn _ _ D D' s)
  all_goals
    rename_i x y h
    cases hr : readReg s (.reg x) with
    | none => simp [hr]
    | some p =>
        obtain ⟨w, v⟩ := p
        cases hg : s.getW y w <;> simp [hr, hg, LstateN.setReg, LstateN.nextPc]

theorem lsemStepCast_dst (opn : String) (a b : LOperand) (cd : Option Nat) (D D' : String)
    (s : LstateN) :
    lsemStepCast (.Lopn [.reg D'] opn [a, b], cd) s =
      (lsemStepCast (.Lopn [.reg D] opn [a, b], cd) s).map
        (fun t => (s.setReg D' (t.lvm D).2).nextPc) := by
  simp only [lsemStepCast, castStruct?, movImmStruct?]
  exact lsemStepMC_dst opn a b D D' s

/-- The state `t` with its register file replaced by the register file of `s` in which `D'`
    holds the cell of `t` at `D`, one program counter later. -/
def movDst (s : LstateM) (D D' : String) (t : LstateM) : LstateM :=
  { t with reg := (s.reg.setReg D' (t.reg.lvm D).2).nextPc }

theorem lvm_nextPc_setReg_self (s : LstateN) (r : String) {w : Nat} (v : BitVec w) :
    (s.setReg r v).nextPc.lvm r = ⟨w, v⟩ := by simp

theorem lvm_nextPc_setReg_sig (s : LstateN) (r : String) (x : Σ w, BitVec w) :
    (s.setReg r x.2).nextPc.lvm r = x := by simp

theorem lvm_nextPc_setReg_other (s : LstateN) {r q : String} {w : Nat} (v : BitVec w)
    (h : q ≠ r) : (s.setReg r v).nextPc.lvm q = s.lvm q := by simp [h]

theorem withALUFlags_setReg (i : LinstrRM) (s0 s1 : LstateM) (r : LstateN) :
    withALUFlags i s0 { s1 with reg := r } = { withALUFlags i s0 s1 with reg := r } := by
  unfold withALUFlags
  split
  · split <;> rfl
  · rfl

theorem withALUFlags_congr {i j : LinstrRM} (h : aluFlagOp? i = aluFlagOp? j) :
    withALUFlags i = withALUFlags j := by
  funext s0 s1
  unfold withALUFlags
  rw [h]

/-- **The destination of a two-source operation.** A register-tagged `opn D', [a, b]` other
    than the flag compare steps to the state `opn D, [a, b]` steps to, with the word written at
    `D` written at `D'` and every other register as before the step. -/
theorem fstepF_dst (opn : String) (a b : LOperand) (cd : Option Nat) (D D' : String)
    (hcmp : opn ≠ withWidthTag 64 "CMP") (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg D'] opn [a, b], .reg cd) s zf =
      (fstepF (.Lopn [.reg D] opn [a, b], .reg cd) s zf).map
        (fun p => (movDst s D D' p.1, p.2)) := by
  have hc : ∀ E, cmpArgs? (.Lopn [.reg E] opn [a, b], .reg cd) = none := fun E => by
    simp [cmpArgs?, hcmp]
  have hm : ∀ E, movRegArgs? (.Lopn [.reg E] opn [a, b], .reg cd) = none := fun E => by
    cases a <;> cases b <;> rfl
  simp only [fstepF, hc, hm, stepMemF, lsemStepMem_reg, lsemStepCast_dst opn a b cd D D']
  cases hr : lsemStepCast (.Lopn [.reg D] opn [a, b], cd) s.reg with
  | some r =>
      have ha : aluFlagOp? (.Lopn [.reg D'] opn [a, b], .reg cd)
          = aluFlagOp? (.Lopn [.reg D] opn [a, b], .reg cd) := rfl
      rw [Option.map_some, Option.map_some, Option.map_some, Option.map_some,
        withALUFlags_congr ha]
      show some (withALUFlags _ s { s with reg := _ }, zf) = some (movDst s D D' _, zf)
      rw [show ({ s with reg := (s.reg.setReg D' (r.lvm D).2).nextPc } : LstateM)
          = { ({ s with reg := r } : LstateM) with reg := (s.reg.setReg D' (r.lvm D).2).nextPc }
          from rfl, withALUFlags_setReg]
      simp only [movDst]
      rw [withALUFlags_reg]
  | none =>
      simp only [Option.map_none, carryArgs?, wideArgs?]
      split_ifs <;> simp only [carryStep, wideStep, Option.map_none] <;> (repeat' split) <;>
        simp only [Option.map_some, Option.map_none, movDst, LstateM.setReg, LstateM.nextPc] <;>
        (try rw [lvm_nextPc_setReg_self])

/-! ## 2. Exchanged sources of a commutative operation -/

theorem aluB5_comm {op : AluOp} (hop : op ≠ .sub) (a b : BitVec 64) :
    aluB5 op a b = aluB5 op b a := by
  cases op
  · simp [aluB5, Jasmin.x86_ADD, BitVec.add_comm, Nat.add_comm, Int.add_comm]
  · exact absurd rfl hop
  all_goals simp [aluB5, Jasmin.x86_AND, Jasmin.x86_OR, Jasmin.x86_XOR, BitVec.and_comm,
    BitVec.or_comm, BitVec.xor_comm]

theorem applyOpnN_comm {w : Nat} {m : String} (hm : commBases.contains m = true)
    (a b : BitVec w) : applyOpnN w m [a, b] = applyOpnN w m [b, a] := by
  simp only [commBases, List.contains_iff_mem, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    simp [applyOpnN, BitVec.add_comm, BitVec.mul_comm, BitVec.and_comm, BitVec.or_comm,
      BitVec.xor_comm]

theorem getW_of_lvm {s : LstateN} {r : String} {w : Nat} {v : BitVec w}
    (h : s.lvm r = ⟨w, v⟩) : s.getW r w = some v := by
  unfold LstateN.getW
  rw [h]
  simp

theorem getW_of_ne {s : LstateN} {r : String} {w : Nat} (h : (s.lvm r).1 ≠ w) :
    s.getW r w = none := by
  unfold LstateN.getW
  simp [h]

/-- The register step of a commutative operation with exchanged register sources. -/
theorem lsemStepN_comm {opn d y : String} (hm : commBases.contains (stripWidthTag opn) = true)
    (s : LstateN) :
    lsemStepN (.Lopn [.reg d] opn [.reg y, .reg d]) s
      = lsemStepN (.Lopn [.reg d] opn [.reg d, .reg y]) s := by
  cases hy : s.lvm y with
  | mk wy vy =>
  cases hd : s.lvm d with
  | mk wd vd =>
  by_cases hw : wy = wd
  · subst hw
    simp only [lsemStepN, readReg, evalOperandN, hy, hd, getW_of_lvm hy, getW_of_lvm hd,
      applyOpnN_comm hm vy vd]
    have hc : cmpOfName? (stripWidthTag opn) = none := by
      simp only [commBases, List.contains_iff_mem, List.mem_cons, List.mem_nil_iff,
        or_false] at hm
      rcases hm with h | h | h | h | h <;> rw [h] <;> rfl
    simp only [hc]
  · simp only [lsemStepN, readReg, evalOperandN, hy, hd,
      getW_of_ne (show (s.lvm d).1 ≠ wy by rw [hd]; exact Ne.symm hw),
      getW_of_ne (show (s.lvm y).1 ≠ wd by rw [hy]; exact hw)]

theorem withALUFlags_comm {opn d y : String} (hsub : opn ≠ withWidthTag 64 "SUB") (τ : MemTag)
    (s0 s1 : LstateM) :
    withALUFlags (.Lopn [.reg d] opn [.reg y, .reg d], τ) s0 s1
      = withALUFlags (.Lopn [.reg d] opn [.reg d, .reg y], τ) s0 s1 := by
  unfold withALUFlags aluFlagOp?
  dsimp only
  split_ifs <;>
    (cases hy : evalOperandN s0.reg 64 (.reg y) <;> cases hd : evalOperandN s0.reg 64 (.reg d) <;>
      simp only [hy, hd, aluB5_comm (by decide : AluOp.add ≠ .sub),
        aluB5_comm (by decide : AluOp.and ≠ .sub), aluB5_comm (by decide : AluOp.or ≠ .sub),
        aluB5_comm (by decide : AluOp.xor ≠ .sub)])

/-- **Exchanged sources of a commutative operation.** For a mnemonic of `commOpns`, or a base of
    `commBases` tagged at a width other than `64`, the register-tagged `opn d, [y, d]` and
    `opn d, [d, y]` step alike. -/
theorem fstepF_comm {opn d y : String}
    (hopn : opn ∈ commOpns ∨ ∃ w, w ≠ 64 ∧ ∃ b, b ∈ commBases ∧ opn = withWidthTag w b)
    (cd : Option Nat) (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg d] opn [.reg y, .reg d], .reg cd) s zf
      = fstepF (.Lopn [.reg d] opn [.reg d, .reg y], .reg cd) s zf := by
  have hF : commBases.contains (stripWidthTag opn) = true ∧ stripWidthTag opn ≠ "MULXHI" ∧
      opn ≠ withWidthTag 64 "CMP" ∧ opn ≠ withWidthTag 64 "ADC" ∧ opn ≠ withWidthTag 64 "SBB" ∧
      opn ≠ withWidthTag 64 "ADCX" ∧ opn ≠ withWidthTag 64 "ADOX" ∧
      opn ≠ withWidthTag 64 "MOV" ∧ opn ≠ withWidthTag 64 "SUB" := by
    rcases hopn with hopn | ⟨w, hw, b, hb, rfl⟩
    · simp only [commOpns, List.mem_cons, List.mem_nil_iff, or_false] at hopn
      rcases hopn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    · have hsf : tagSepFree b = true := by
        simp only [commBases, List.mem_cons, List.mem_nil_iff, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
      have hne : ∀ X : String, '^' ∉ (withWidthTag 64 X).toList → withWidthTag w b ≠ withWidthTag 64 X :=
        fun X hX => (OwnedLprogTV.withWidthTag_eq_iff_false hw b hX).mp
      rw [stripWidthTag_withWidthTag w hsf]
      refine ⟨by simpa using hb, ?_, hne _ (by decide +kernel), hne _ (by decide +kernel),
        hne _ (by decide +kernel), hne _ (by decide +kernel), hne _ (by decide +kernel),
        hne _ (by decide +kernel), hne _ (by decide +kernel)⟩
      simp only [commBases, List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨hm, hmx, hcmp, hadc, hsbb, hadcx, hadox, hmov, hsub⟩ := hF
  have hmem : ∀ a b : String, lsemStepMem (.Lopn [.reg d] opn [.reg a, .reg b], .reg cd) s
      = (lsemStepN (.Lopn [.reg d] opn [.reg a, .reg b]) s.reg).map
          (fun r => { s with reg := r }) := by
    intro a b
    rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inl ⟨rfl, by simp [movImmStruct?]⟩),
      lsemStepMC_of_delegate _ _ (by simp [mulhiStruct?, hmx]) rfl rfl rfl rfl,
      lsemStepSh_of_not_sar _ _ rfl]
  have hca : ∀ a b : String, carryArgs? (.Lopn [.reg d] opn [.reg a, .reg b], .reg cd) = none :=
    fun a b => by simp [carryArgs?, hadc, hsbb, hadcx, hadox]
  have hwa : ∀ a b : String, wideArgs? (.Lopn [.reg d] opn [.reg a, .reg b], .reg cd) = none :=
    fun a b => by simp [wideArgs?, hmov]
  have hc : ∀ a b : String, cmpArgs? (.Lopn [.reg d] opn [.reg a, .reg b], .reg cd) = none :=
    fun a b => by simp [cmpArgs?, hcmp]
  have hmv : ∀ a b : String, movRegArgs? (.Lopn [.reg d] opn [.reg a, .reg b], .reg cd) = none :=
    fun a b => rfl
  simp only [fstepF, hc, hmv, stepMemF, hmem, hca, hwa, lsemStepN_comm (y := y) (d := d) hm,
    withALUFlags_comm hsub]

/-- The two-source step of `lsemStepN` is stuck on a flag head `CMP` or `TEST`: neither has a
    value (`applyOpnN`) nor a comparison-bit (`cmpOfName?`) arm. -/
theorem lsemStepN_flag {opn : String} (hS : stripWidthTag opn = "CMP" ∨ stripWidthTag opn = "TEST")
    (d : String) (a b : LOperand) (s : LstateN) :
    lsemStepN (.Lopn [.reg d] opn [a, b]) s = none := by
  rcases hS with hS | hS <;> simp only [lsemStepN, hS, applyOpnN, cmpOfName?, immFirstN] <;>
    split <;> (try split) <;> simp_all <;> split <;> rfl

/-- **A `^w`-tagged flag head does not step on the flag machine.** For `CMP` or `TEST` and a
    width `w ≠ 64`, no arm of `fstepF` reads `withWidthTag w m`. -/
theorem fstepF_withWidthTag_flag {w : Nat} (hw : w ≠ 64) {m : String}
    (hm : m = "CMP" ∨ m = "TEST") (d : String) (a b : LOperand) (τ : MemTag) (s : LstateM)
    (zf : Bool) :
    fstepF (.Lopn [.reg d] (withWidthTag w m) [a, b], τ) s zf = none := by
  have hsf : tagSepFree m = true := by rcases hm with rfl | rfl <;> decide +kernel
  have h1 : stripWidthTag (withWidthTag w m) = m := stripWidthTag_withWidthTag w hsf
  have hne : ∀ s : String, '^' ∉ s.toList → (withWidthTag w m = s ↔ False) :=
    fun s hs => OwnedLprogTV.withWidthTag_eq_iff_false hw m hs
  have hw64 : ∀ X, withWidthTag 64 X = X ++ ":64" := fun X => by simp [withWidthTag]
  have hN : ∀ r, lsemStepN (.Lopn [.reg d] (withWidthTag w m) [a, b]) r = none :=
    lsemStepN_flag (by rw [h1]; exact hm) d a b
  have hmx : m ≠ "MULXHI" ∧ m ≠ "SAR" := by rcases hm with rfl | rfl <;> decide
  have hMC : ∀ r, lsemStepMC (.Lopn [.reg d] (withWidthTag w m) [a, b]) r = none := by
    intro r
    rw [lsemStepMC_of_delegate _ _ (by unfold mulhiStruct?; split <;> simp_all)
      (by cases a <;> cases b <;> rfl) (by cases a <;> cases b <;> rfl)
      (by cases a <;> cases b <;> rfl) (by cases a <;> cases b <;> rfl),
      lsemStepSh_of_not_sar _ _ (by unfold sarStruct?; split <;> simp_all)]
    exact hN r
  have hCast : ∀ cd r, lsemStepCast (.Lopn [.reg d] (withWidthTag w m) [a, b], cd) r = none := by
    intro cd r
    rw [lsemStepCast_of_delegate _ _ (Or.inl ⟨by cases a <;> rfl, by cases a <;> cases b <;> rfl⟩)]
    exact hMC r
  have hc : cmpArgs? (.Lopn [.reg d] (withWidthTag w m) [a, b], τ) = none := by
    simp [cmpArgs?, hw64, hne]
  have hmv : movRegArgs? (.Lopn [.reg d] (withWidthTag w m) [a, b], τ) = none := by
    cases a <;> cases b <;> rfl
  have hca : carryArgs? (.Lopn [.reg d] (withWidthTag w m) [a, b], τ) = none := by
    simp [carryArgs?, hw64, hne]
  have hwa : wideArgs? (.Lopn [.reg d] (withWidthTag w m) [a, b], τ) = none := by
    simp [wideArgs?, hw64, hne]
  have l1 : loadStruct? (.Lopn [.reg d] (withWidthTag w m) [a, b]) = none := by
    unfold loadStruct?; split <;> simp_all
  have l2 : storeStruct? (.Lopn [.reg d] (withWidthTag w m) [a, b]) = none := by
    unfold storeStruct?; split <;> simp_all
  have l3 : loadCStruct? (.Lopn [.reg d] (withWidthTag w m) [a, b]) = none := by
    unfold loadCStruct?; split <;> simp_all
  have l4 : storeCStruct? (.Lopn [.reg d] (withWidthTag w m) [a, b]) = none := by
    unfold storeCStruct?; split <;> simp_all
  have l5 : zeroStruct? (.Lopn [.reg d] (withWidthTag w m) [a, b]) = none := by
    unfold zeroStruct?; split <;> simp_all
  have l6 : storeImmStruct? (.Lopn [.reg d] (withWidthTag w m) [a, b]) = none := by
    unfold storeImmStruct?; split <;> simp_all
  have hS : stepMemF (.Lopn [.reg d] (withWidthTag w m) [a, b], τ) s = none := by
    cases τ <;> simp only [stepMemF, lsemStepMem, hCast, Option.map_none, hca, hwa, l1, l2, l3,
      l4, l5, l6]
  simp only [fstepF, hc, hmv, hS, Option.map_none]

/-- The flag operations `CMP` and `TEST` step alike at every destination. -/
theorem fstepF_flag_dst {opn : String}
    (hopn : opn = "CMP" ∨ opn = "CMP:64" ∨ opn = "TEST" ∨ opn = "TEST:64" ∨
      ∃ w, w ≠ 64 ∧ (opn = withWidthTag w "CMP" ∨ opn = withWidthTag w "TEST"))
    (d d' : String) (a b : LOperand) (τ : MemTag) (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg d'] opn [a, b], τ) s zf = fstepF (.Lopn [.reg d] opn [a, b], τ) s zf := by
  rcases hopn with h | h | h | h | ⟨w, hw, h | h⟩
  rotate_left 4
  · subst h
    rw [fstepF_withWidthTag_flag hw (Or.inl rfl), fstepF_withWidthTag_flag hw (Or.inl rfl)]
  · subst h
    rw [fstepF_withWidthTag_flag hw (Or.inr rfl), fstepF_withWidthTag_flag hw (Or.inr rfl)]
  all_goals (subst h; cases τ <;> cases a <;> cases b <;> rfl)

/-! ## 3. Agreement off the save slot -/

/-- The names the legalisation keeps: every name other than the save slot `qsave.R15` when the
    scratch route is enabled, and every name otherwise. -/
def KeptT (ok : Bool) (r : String) : Prop := ok = true → r ≠ scratchSave

/-- Two bases agree on the registers of `KeptT ok`, on the arrays, on the word memory and on
    the carry and overflow flags. -/
structure AgreeT (ok : Bool) (s s' : LstateM) : Prop where
  /-- The registers agree on the kept names. -/
  reg : ∀ r, KeptT ok r → s'.reg.lvm r = s.reg.lvm r
  /-- The arrays agree. -/
  arr : s'.larr = s.larr
  /-- The word memories agree. -/
  mem : s'.lmem = s.lmem
  /-- The carry flags agree. -/
  cf : s'.cf = s.cf
  /-- The overflow flags agree. -/
  of : s'.of = s.of

theorem AgreeT.refl (ok : Bool) (s : LstateM) : AgreeT ok s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem AgreeT.setLpc {ok : Bool} {a b : LstateM} (h : AgreeT ok a b) (p q : Nat) :
    AgreeT ok (a.setLpc p) (b.setLpc q) := ⟨h.reg, h.arr, h.mem, h.cf, h.of⟩

theorem AgreeT.of_eqPc {ok : Bool} {a b c : LstateM} (h : AgreeT ok a b) (he : EqPc b c) :
    AgreeT ok a c := by
  unfold EqPc at he
  rw [he]
  exact ⟨h.reg, h.arr, h.mem, h.cf, h.of⟩

/-- **A step from agreeing bases.** An instruction that reads only kept names steps from two
    agreeing bases to two agreeing bases, with the same zero flag. -/
theorem fstepF_agreeT {ok : Bool} {i : LinstrRM} (hr : ∀ r, readsI i.1 r → KeptT ok r)
    {s s' t : LstateM} {zf z : Bool} (hA : AgreeT ok s s') (h : fstepF i s zf = some (t, z)) :
    ∃ t', fstepF i s' zf = some (t', z) ∧ AgreeT ok t t' := by
  have hM : MAgree (readsI i.1) s (s'.setLpc s.lpc) :=
    ⟨⟨rfl, fun r hr' => (hA.reg r (hr r hr')).symm⟩, hA.arr.symm, hA.mem.symm, hA.cf.symm,
      hA.of.symm⟩
  have hc := fstepF_congr i hM zf
  rw [h, fstepF_setLpc] at hc
  cases h' : fstepF i s' zf with
  | none => rw [h'] at hc; cases hc
  | some q =>
      rw [h', Option.map_some] at hc
      obtain ⟨t', z'⟩ := q
      cases hc with
      | some hF =>
          obtain ⟨⟨⟨-, hN⟩, hlarr, hlmem, hcf, hof⟩, hz⟩ := hF
          simp only at hz
          subst hz
          refine ⟨t', rfl, ⟨fun r hr' => ?_, hlarr.symm, hlmem.symm, hcf.symm, hof.symm⟩⟩
          rcases hN r with he | ⟨he1, he2⟩
          · exact he.symm
          · have e2 : t'.reg.lvm r = s'.reg.lvm r := he2
            rw [e2, he1]
            exact hA.reg r hr'

/-! ## 4. The names an avoiding instruction reads -/

/-- The base of a cell name `mem.B.off` contains no dot. -/
theorem dot_not_mem_of_cellParts {n b : String} {o : Nat} (h : cellParts? n = some (b, o)) :
    '.' ∉ b.toList := by
  unfold cellParts? at h
  split_ifs at h
  split at h
  · rename_i base off hsp
    obtain ⟨-, rfl⟩ := Option.map_eq_some_iff.mp h |>.choose_spec |> fun h' =>
      (⟨h'.1, (Prod.mk.inj h'.2).1.symm⟩ : _ ∧ b = String.ofList base)
    rw [List.span_eq_takeWhile_dropWhile, Prod.mk.injEq] at hsp
    rw [String.toList_ofList, ← hsp.1]
    intro hm
    have := List.all_eq_true.mp (List.all_takeWhile (p := fun c => c != '.')
      (l := n.toList.drop 4)) '.' hm
    simp at this
  · cases h

/-- The base of a cell operand is not the save slot. -/
theorem cellBase_ne_scratchSave {o : LOperand} {b : String} (h : cellBase o = some b) :
    b ≠ scratchSave := by
  cases o with
  | reg n =>
      simp only [cellBase, Option.map_eq_some_iff] at h
      obtain ⟨⟨b', off⟩, hp, rfl⟩ := h
      intro he
      simp only at he
      have hd := dot_not_mem_of_cellParts hp
      rw [he] at hd
      exact hd (by decide)
  | _ => simp [cellBase] at h

/-- A name of an operand that avoids the scratch register does not mention it. -/
theorem srcNames_avoid {o : LOperand} (h : opAvoids o = true) :
    ∀ n ∈ srcNames o, mentionsScratch n = false := by
  intro n hn
  cases o <;> simp_all [srcNames, opAvoids]
  rcases hn with rfl | rfl <;> simp_all

theorem ne_scratchSave_of_mentions {n : String} (h : mentionsScratch n = false) :
    n ≠ scratchSave := by
  rintro rfl
  rw [TwoAddrLegalize.mentionsScratch_scratchSave] at h
  cases h

theorem ne_reloadScratch_of_mentions {n : String} (h : mentionsScratch n = false) :
    n ≠ reloadScratch := by
  rintro rfl
  rw [TwoAddrLegalize.mentionsScratch_reloadScratch] at h
  cases h

/-- An `Lopn` whose sources avoid the scratch register reads no save slot. -/
theorem readsI_ne_scratchSave {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : ∀ op ∈ ss, opAvoids op = true) :
    ∀ r, readsI (.Lopn ds o ss) r → r ≠ scratchSave := by
  intro r hr
  rcases hr with rfl | ⟨rfl, -⟩ | hm
  · decide
  · decide
  · rcases hm with hm | hm
    · obtain ⟨op, hop, hn⟩ := List.mem_flatMap.mp hm
      exact ne_scratchSave_of_mentions (srcNames_avoid (h op hop) r hn)
    · obtain ⟨op, -, hn⟩ := List.mem_filterMap.mp hm
      exact cellBase_ne_scratchSave hn

/-- **The names an avoiding instruction reads are kept.** -/
theorem readsI_kept {ok : Bool} {x : LinstrR} (hav : ok = true → instrAvoids x = true) :
    ∀ r, readsI x r → KeptT ok r := by
  intro r hr hok
  cases x with
  | Lopn ds o ss =>
      have ha := hav hok
      simp only [instrAvoids, Bool.and_eq_true, List.all_eq_true] at ha
      exact readsI_ne_scratchSave ha.2 r hr
  | _ =>
      rcases hr with rfl | ⟨rfl, -⟩ | hm
      · decide
      · decide
      · exact hm.elim

/-! ## 5. The scratch route -/

/-- **The scratch route.** Let `opn d, [s0, s1]` step from `s` to `t`, with `opn` not the flag
    compare and none of `d`, `s0` and the names of `s1` mentioning `R15`. From a base that
    agrees with `s` off `qsave.R15`, the save `mov qsave.R15, R15`, the copy `mov R15, s0`, the
    operation `opn R15, [R15, s1]`, the copy `mov d, R15` and the restore `mov R15, qsave.R15`
    run to a base that agrees with `t` off `qsave.R15`, with the same zero flag. -/
theorem runStraightF_scratch {opn m d s0 : String} {s1 : LOperand} {cd : Option Nat}
    (hm : stripWidthTag m = "MOV") (hcmp : opn ≠ withWidthTag 64 "CMP")
    (hd : mentionsScratch d = false) (hs0 : mentionsScratch s0 = false)
    (hs1 : opAvoids s1 = true) (τ1 τ2 τ4 τ5 : MemTag) {s s' t : LstateM} {zf z : Bool}
    (hA : AgreeT true s s')
    (h : fstepF (.Lopn [.reg d] opn [.reg s0, s1], .reg cd) s zf = some (t, z)) :
    ∃ t', runStraightF
        [(.Lopn [.reg scratchSave] "MOV:64" [.reg reloadScratch], τ1),
         (.Lopn [.reg reloadScratch] m [.reg s0], τ2),
         (.Lopn [.reg reloadScratch] opn [.reg reloadScratch, s1], .reg cd),
         (.Lopn [.reg d] m [.reg reloadScratch], τ4),
         (.Lopn [.reg reloadScratch] "MOV:64" [.reg scratchSave], τ5)] s' zf = some (t', z)
      ∧ AgreeT true t t' := by
  have hRQ : reloadScratch ≠ scratchSave := by decide
  have hdR := ne_reloadScratch_of_mentions hd
  have hdQ := ne_scratchSave_of_mentions hd
  have hs0R := ne_reloadScratch_of_mentions hs0
  have hs0Q := ne_scratchSave_of_mentions hs0
  have hs1R : s1 ≠ .reg reloadScratch := by
    rintro rfl
    simp [opAvoids, TwoAddrLegalize.mentionsScratch_reloadScratch] at hs1
  -- the operation at the destination `R15`, from `s`
  have h1 : fstepF (.Lopn [.reg reloadScratch] opn [.reg s0, s1], .reg cd) s zf
      = some (movDst s d reloadScratch t, z) := by
    rw [fstepF_dst opn _ _ cd d reloadScratch hcmp, h]
    rfl
  -- the save
  let u1 : LstateM := (s'.setReg scratchSave (s'.reg.lvm reloadScratch).2).nextPc
  have hsave : fstepF (.Lopn [.reg scratchSave] "MOV:64" [.reg reloadScratch], τ1) s' zf
      = some (u1, zf) := fstepF_movWire _ _ _ τ1 (by decide) s' zf
  have hAu : AgreeT true s u1 := by
    refine ⟨fun r hr => ?_, hA.arr, hA.mem, hA.cf, hA.of⟩
    have hrQ : r ≠ scratchSave := hr rfl
    simp only [u1, LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.lvm_nextPc,
      LstateN.lvm_setReg, hrQ, ite_false]
    exact hA.reg r hr
  -- the operation from the saved state
  have hreads : ∀ r, readsI (.Lopn [.reg reloadScratch] opn [.reg s0, s1]) r → KeptT true r :=
    fun r hr _ => readsI_ne_scratchSave (fun op hop => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hop
      rcases hop with rfl | rfl
      · simp [opAvoids, hs0]
      · exact hs1) r hr
  obtain ⟨t1, ht1, hA1⟩ := fstepF_agreeT hreads hAu h1
  -- the copy into `R15` and the operation on it
  obtain ⟨t2, ht2, hE2⟩ := fstepF_twoAddr reloadScratch s0 s1 opn m cd τ2 hm hcmp hs1R ht1
  -- the copy into `d` and the restore
  let t3 : LstateM := (t2.setReg d (t2.reg.lvm reloadScratch).2).nextPc
  let t4 : LstateM := (t3.setReg reloadScratch (t3.reg.lvm scratchSave).2).nextPc
  refine ⟨t4, ?_, ?_⟩
  · rw [runStraightF_cons, hsave, Option.bind_some]
    rw [show [((LinstrR.Lopn [.reg reloadScratch] m [.reg s0]), τ2),
          ((LinstrR.Lopn [.reg reloadScratch] opn [.reg reloadScratch, s1]), MemTag.reg cd),
          ((LinstrR.Lopn [.reg d] m [.reg reloadScratch]), τ4),
          ((LinstrR.Lopn [.reg reloadScratch] "MOV:64" [.reg scratchSave]), τ5)]
        = [(movWire reloadScratch s0 m, τ2), (binopWire reloadScratch reloadScratch s1 opn, .reg cd)]
          ++ [((LinstrR.Lopn [.reg d] m [.reg reloadScratch]), τ4),
            ((LinstrR.Lopn [.reg reloadScratch] "MOV:64" [.reg scratchSave]), τ5)] from rfl,
      JasminLsemAddrMem.runStraightF_append, ht2, Option.bind_some, runStraightF_cons]
    rw [show (LinstrR.Lopn [.reg d] m [.reg reloadScratch]) = movWire d reloadScratch m from rfl,
      fstepF_movWire d reloadScratch m τ4 hm, Option.bind_some, runStraightF_cons,
      show (LinstrR.Lopn [.reg reloadScratch] "MOV:64" [.reg scratchSave])
        = movWire reloadScratch scratchSave "MOV:64" from rfl,
      fstepF_movWire reloadScratch scratchSave "MOV:64" τ5 (by decide), Option.bind_some,
      runStraightF_nil]
  · -- the registers the source writes and the registers the steps write
    have hdst : ∀ r, r ≠ d → t.reg.lvm r = s.reg.lvm r := fun r hr =>
      (fstepF_frame_dst h (by simp [dstNames, JasminLsemExportRewrites.opNames, hr])).1
    have h1Q : t1.reg.lvm scratchSave = u1.reg.lvm scratchSave :=
      (fstepF_frame_dst ht1 (by simp [dstNames, JasminLsemExportRewrites.opNames, hRQ.symm])).1
    unfold EqPc at hE2
    have e2 : t2.reg.lvm = t1.reg.lvm := by rw [hE2]; rfl
    have e3 : t3.reg = (t2.reg.setReg d (t2.reg.lvm reloadScratch).2).nextPc := rfl
    have e4 : t4.reg = (t3.reg.setReg reloadScratch (t3.reg.lvm scratchSave).2).nextPc := rfl
    have hmv : ∀ r, r ≠ scratchSave →
        t1.reg.lvm r = (movDst s d reloadScratch t).reg.lvm r := fun r hr => hA1.reg r (fun _ => hr)
    refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · have hrQ : r ≠ scratchSave := hr rfl
      rw [e4]
      by_cases hrR : r = reloadScratch
      · subst hrR
        rw [lvm_nextPc_setReg_sig, e3, lvm_nextPc_setReg_other _ _ (Ne.symm hdQ), e2, h1Q]
        simp only [u1, LstateM.reg_nextPc, LstateM.reg_setReg]
        rw [lvm_nextPc_setReg_sig, hA.reg _ (fun _ => hRQ), hdst _ (Ne.symm hdR)]
      · rw [lvm_nextPc_setReg_other _ _ hrR, e3]
        by_cases hrd : r = d
        · subst hrd
          rw [lvm_nextPc_setReg_sig, e2, hmv _ hRQ]
          simp only [movDst]
          rw [lvm_nextPc_setReg_sig]
        · rw [lvm_nextPc_setReg_other _ _ hrd, e2, hmv _ hrQ]
          simp only [movDst]
          rw [lvm_nextPc_setReg_other _ _ hrR, hdst _ hrd]
    · show t2.larr = t.larr
      rw [hE2]
      exact hA1.arr
    · show t2.lmem = t.lmem
      rw [hE2]
      exact hA1.mem
    · show t2.cf = t.cf
      rw [hE2]
      exact hA1.cf
    · show t2.of = t.of
      rw [hE2]
      exact hA1.of

/-! ## 6. The routes -/

/-- The legalisation of one typed instruction, each emitted instruction typed with `tg`. -/
def legalRM (ok : Bool) (tg : LinstrR → MemTag) (p : LinstrRM) : List LinstrRM :=
  (legalR ok p.1).map fun x => (x, tg x)

/-- The tag is a register tag. -/
def isRegTag : MemTag → Bool
  | .reg _ => true
  | _ => false

/-- **The side conditions on one instruction**, typed with `tg`: the instruction is an `Lopn`,
    a label, a zero-flag conditional or a goto (`clsB`); its route is one the value checker
    accepts (`OwnedLprogTV.twoAddrRouteWF`: the copy, commutative and scratch routes from a
    register first source, the target of the flag, commutative and scratch routes typed as the
    source); and an instruction the pass rewrites carries a register tag. -/
def twoAddrOKI (tg : LinstrR → MemTag) (x : LinstrR) : Bool :=
  clsB (x, tg x) && twoAddrRouteWF [] tg x &&
    match twoAddrRoute x with
    | .keep => true
    | _ => isRegTag (tg x)

/-- **The side conditions of the theorem** on a body typed with `tg`: `twoAddrOKI` at every
    instruction. -/
def twoAddrOK (tg : LinstrR → MemTag) (body : Lcmd) : Bool :=
  body.all fun i => twoAddrOKI tg i.li_i

/-- A straight segment simulates one instruction from agreeing bases. -/
def SimT (ok : Bool) (i : LinstrRM) (js : List LinstrRM) : Prop :=
  ∀ (s s' t : LstateM) (zf zt : Bool), AgreeT ok s s' → fstepF i s zf = some (t, zt) →
    ∃ t', runStraightF js s' zf = some (t', zt) ∧ AgreeT ok t t'

theorem simT_self {ok : Bool} {i : LinstrRM} (hr : ∀ r, readsI i.1 r → KeptT ok r) :
    SimT ok i [i] := by
  intro s s' t zf zt hA h
  obtain ⟨t', h', hA'⟩ := fstepF_agreeT hr hA h
  exact ⟨t', by rw [runStraightF_cons, h']; rfl, hA'⟩

theorem simT_of_fstepF_eq {ok : Bool} {i j : LinstrRM} (hr : ∀ r, readsI i.1 r → KeptT ok r)
    (he : ∀ s zf, fstepF j s zf = fstepF i s zf) : SimT ok i [j] := by
  intro s s' t zf zt hA h
  obtain ⟨t', h', hA'⟩ := fstepF_agreeT hr hA h
  exact ⟨t', by rw [runStraightF_cons, he, h']; rfl, hA'⟩

theorem isRegTag_spec {τ : MemTag} (h : isRegTag τ = true) : ∃ cd, τ = .reg cd := by
  cases τ <;> simp_all [isRegTag]

theorem ne_reg_of_contains {d : String} {b : LOperand}
    (h : (LprogLeak.opNames b).contains d = false) : b ≠ .reg d := by
  rintro rfl
  simp [LprogLeak.opNames] at h

/-- **The simulation of one instruction by its legalisation.** -/
theorem simT_legal {tg : LinstrR → MemTag} (htg : TagFirstSrc tg) {ok : Bool} {x : LinstrR}
    (hwf : twoAddrRouteWF [] tg x = true)
    (htag : twoAddrRoute x ≠ .keep → isRegTag (tg x) = true)
    (hav : ok = true → instrAvoids x = true) : SimT ok (x, tg x) (legalRM ok tg (x, tg x)) := by
  have hself : SimT ok (x, tg x) [(x, tg x)] := simT_self (readsI_kept hav)
  have hrd := readsI_kept (ok := ok) hav
  unfold legalRM legalR
  split
  · rename_i d opn a b hx
    simp only at hx
    subst hx
    cases hr : twoAddrRoute (.Lopn [.reg d] opn [a, b]) with
    | keep => exact hself
    | flag =>
        obtain ⟨hb, m, hm⟩ := OwnedLprogTV.twoAddrRoute_flag hr
        cases a with
        | reg y =>
            simp only [twoAddrRouteWF, hr, beq_iff_eq] at hwf
            simp only [List.map_cons, List.map_nil, hwf]
            exact simT_of_fstepF_eq hrd (fun s zf =>
              fstepF_flag_dst (OwnedLprogTV.opn_flag hm hb) d y _ b _ s zf)
        | _ => exact hself
    | copy m =>
        obtain ⟨hm, hb, hc, -⟩ := OwnedLprogTV.twoAddrRoute_copy hr
        obtain ⟨cd, hcd⟩ := isRegTag_spec (htag (by rw [hr]; simp))
        cases a with
        | reg y =>
            simp only [List.map_cons, List.map_nil]
            rw [htg d opn (.reg d) (.reg y) b, hcd]
            intro s s' t zf zt hA h
            obtain ⟨t1, h1, hA1⟩ := fstepF_agreeT hrd hA h
            obtain ⟨t2, h2, hE⟩ := fstepF_twoAddr d y b opn m cd _
              (TwoAddrLegalize.stripWidthTag_movFor hm) (OwnedLprogTV.opn_ne_cmp64 hc)
              (ne_reg_of_contains hb) h1
            exact ⟨t2, h2, hA1.of_eqPc hE⟩
        | _ => simp [twoAddrRouteWF, hr] at hwf
    | comm =>
        obtain ⟨hc, rfl, m, hm⟩ := OwnedLprogTV.twoAddrRoute_comm hr
        obtain ⟨-, hyd, -⟩ := OwnedLprogTV.twoAddrRoute_untied hr (by simp)
        obtain ⟨cd, hcd⟩ := isRegTag_spec (htag (by rw [hr]; simp))
        cases a with
        | reg y =>
            simp only [twoAddrRouteWF, hr, beq_iff_eq] at hwf
            simp only [List.map_cons, List.map_nil, hwf]
            rw [hcd]
            exact simT_of_fstepF_eq hrd (fun s zf =>
              (fstepF_comm (OwnedLprogTV.opn_comm hm hc) cd s zf).symm)
        | _ => simp [twoAddrRouteWF, hr] at hwf
    | scratch m =>
        obtain ⟨hm, hc, -⟩ := OwnedLprogTV.twoAddrRoute_scratch hr
        obtain ⟨cd, hcd⟩ := isRegTag_spec (htag (by rw [hr]; simp))
        cases ok with
        | false => exact hself
        | true =>
            have ha := hav rfl
            simp only [instrAvoids, List.all_cons, List.all_nil, Bool.and_true,
              Bool.and_eq_true] at ha
            obtain ⟨had, haa, hab⟩ := ha
            have hd : mentionsScratch d = false := by simpa [opAvoids] using had
            cases a with
            | reg y =>
                have hy : mentionsScratch y = false := by simpa [opAvoids] using haa
                simp only [ite_true]
                split
                · rename_i hcb
                  simp only [Bool.and_eq_true, beq_iff_eq] at hcb
                  obtain ⟨hcb, rfl⟩ := hcb
                  simp only [twoAddrRouteWF, hr, hcb, Bool.true_and,
                    List.contains_nil, Bool.not_false, beq_iff_eq, ite_true] at hwf
                  simp only [List.map_cons, List.map_nil, hwf, hcd]
                  intro s s' t zf zt hA h
                  rw [fstepF_comm (OwnedLprogTV.opn_comm hm hcb)] at h
                  exact runStraightF_scratch (TwoAddrLegalize.stripWidthTag_movFor hm)
                    (OwnedLprogTV.opn_ne_cmp64 hc) hd hd (by simpa [opAvoids] using hy)
                    _ _ _ _ hA h
                · rename_i hcb
                  simp only [twoAddrRouteWF, hr, hcb, Bool.false_eq_true, ite_false,
                    Bool.true_and, List.contains_nil, Bool.not_false, beq_iff_eq] at hwf
                  simp only [List.map_cons, List.map_nil, hwf, hcd]
                  intro s s' t zf zt hA h
                  exact runStraightF_scratch (TwoAddrLegalize.stripWidthTag_movFor hm)
                    (OwnedLprogTV.opn_ne_cmp64 hc) hd hy hab _ _ _ _ hA h
            | _ => simp [twoAddrRouteWF, hr] at hwf
  · exact hself

/-! ## 7. Whole bodies -/

/-- Every instruction the legalisation of an `Lopn` emits is an `Lopn`. -/
theorem legalR_lopn (ok : Bool) {ds : List LOperand} {o : String} {ss : List LOperand} :
    ∀ y ∈ legalR ok (.Lopn ds o ss), ∃ ds' o' ss', y = .Lopn ds' o' ss' := by
  intro y hy
  unfold legalR at hy
  split at hy
  · repeat' split at hy
    all_goals
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, _, rfl⟩
  · simp only [List.mem_singleton] at hy
    exact ⟨_, _, _, hy⟩

/-- An instruction other than an `Lopn` is kept. -/
theorem legalR_of_not_lopn (ok : Bool) {x : LinstrR} (hx : ∀ ds o ss, x ≠ .Lopn ds o ss) :
    legalR ok x = [x] := by
  unfold legalR
  split
  · exact absurd rfl (hx _ _ _)
  · rfl

theorem legalR_length_le (ok : Bool) (x : LinstrR) : (legalR ok x).length ≤ 5 := by
  unfold legalR
  split
  · repeat' split
    all_goals simp
  · simp

/-- **The per-instruction condition of the expansion lift** for the legalisation, at the
    agreement off the save slot. -/
theorem instrOK_legalRM {tg : LinstrR → MemTag} (htg : TagFirstSrc tg) {ok : Bool}
    {x : LinstrR} (hx : twoAddrOKI tg x = true) (hav : ok = true → instrAvoids x = true) :
    InstrOK (AgreeT ok) (legalRM ok tg) (x, tg x) := by
  simp only [twoAddrOKI, Bool.and_eq_true] at hx
  obtain ⟨⟨hcls, hwf⟩, htag⟩ := hx
  have htag' : twoAddrRoute x ≠ .keep → isRegTag (tg x) = true := by
    intro hk
    revert htag
    cases hr : twoAddrRoute x with
    | keep => exact absurd hr hk
    | _ => exact id
  rcases clsB_spec hcls with hl | hc
  · obtain ⟨ds, o, ss, hxe⟩ := hl
    refine Or.inl ⟨⟨ds, o, ss, hxe⟩, fun j hj => ?_, simT_legal htg hwf htag' hav⟩
    simp only [legalRM, List.mem_map] at hj
    obtain ⟨y, hy, rfl⟩ := hj
    simp only at hxe
    subst hxe
    obtain ⟨ds', o', ss', rfl⟩ := legalR_lopn ok y hy
    exact ⟨ds', o', ss', rfl⟩
  · have hnl : ∀ ds o ss, x ≠ .Lopn ds o ss := by
      intro ds o ss he
      rcases hc with ⟨kd, l, h⟩ | ⟨c, l, h, -⟩ | ⟨tgt, h⟩ <;> simp only at h <;> rw [he] at h <;>
        cases h
    refine Or.inr ⟨?_, hc⟩
    simp only [legalRM, legalR_of_not_lopn ok hnl, List.map_cons, List.map_nil]

/-- **`twoAddrBody_lsemFuelMemF`: two-address legalisation preserves halting runs.** Let the
    typing `tg` give a two-source operation one tag whatever its first source
    (`OwnedLprogTV.TagFirstSrc`), and let the body pass `twoAddrOK tg`. Every halting run of the
    typed body from program counter `0` is matched by a halting run of the typed body of
    `twoAddrBody body` from the same state, with at most five times the fuel; the final states
    agree on every register other than the save slot `qsave.R15` (on every register when the
    body names the scratch register `R15`, `bodyAvoids body = false`), on the arrays, the word
    memory, the carry, overflow and zero flags and the function name, and the final program
    counter is the `pcMap` image. -/
theorem twoAddrBody_lsemFuelMemF {tg : LinstrR → MemTag} (htg : TagFirstSrc tg) {body : Lcmd}
    (h : twoAddrOK tg body = true) (fn : String) (s t : LstateMF)
    (hpc : s.prog.base.lpc = 0) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn (typeBody tg body)) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel * 5
      ∧ lsemFuelMemF (singletonProgM fn (typeBody tg (twoAddrBody body))) fuel' s = some t'
      ∧ AgreeT (bodyAvoids body) t.prog.base t'.prog.base ∧ t'.zf = t.zf
      ∧ t'.prog.lfn = t.prog.lfn
      ∧ t'.prog.base.lpc
          = pcMap (legalRM (bodyAvoids body) tg) (typeBody tg body) t.prog.base.lpc := by
  have hP : ExpProg (AgreeT (bodyAvoids body)) (legalRM (bodyAvoids body) tg)
      (singletonProgM fn (typeBody tg body))
      (singletonProgM fn (typeBody tg (twoAddrBody body))) := by
    refine ⟨rfl, twoAddrBody_typedR tg body, fun k i hk => ?_,
      fun _ _ p q hA => hA.setLpc p q⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hk)
    refine instrOK_legalRM htg (List.all_eq_true.mp h j hj) (fun hok => ?_)
    simp only [bodyAvoids, List.all_eq_true] at hok
    exact hok j hj
  have hlen : ∀ i ∈ (singletonProgM fn (typeBody tg body)).body,
      (legalRM (bodyAvoids body) tg i).length ≤ 5 := by
    intro i _
    simp only [legalRM, List.length_map]
    exact legalR_length_le _ _
  have hR : RelX (AgreeT (bodyAvoids body)) (legalRM (bodyAvoids body) tg)
      (singletonProgM fn (typeBody tg body)) s s := by
    refine ⟨rfl, rfl, ?_, AgreeT.refl _ _⟩
    rw [hpc]; rfl
  obtain ⟨fuel', t', hf, hrun', hRt⟩ := lsemFuelMemF_expand hP hlen fuel hR hrun
  exact ⟨fuel', t', hf, hrun', hRt.base, hRt.zf, hRt.lfn, hRt.pc⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrFuelMemF
