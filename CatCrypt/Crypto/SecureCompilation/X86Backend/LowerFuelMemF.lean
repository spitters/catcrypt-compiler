/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload
public import CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrFuelMemF
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowerCore

/-!
# The post-allocation lowering on the flag machine, per instruction family

After register allocation, `JasminLprogExport.physBodyWithStores` lowers each allocated
instruction to a short list of instructions over physical names and spill slots: the
two-address form of a binop (`lowerTwoAddr`), the legalised one-source instruction
(`legalizeOneSrc`), the select and the materialised comparison with spilled operands
(`cmovSpillSeq`, `setccSpill?`). This module states each of these lowerings as a simulation
of one instruction on the flag machine `lsemFuelMemF`, at the agreement
`CmpSpillReload.AgreeS` of two bases off the reload scratches `R15` and `R14`. Each such
simulation gives the per-instruction condition `JasminLsemExportLower.InstrOK` of the
expansion lift `JasminLsemExportLower.lsemFuelMemF_expand` (`instrOK_of_simS`).

Both the source instruction and its lowering are typed with one tag function `tg`, as
`OwnedLprogTV.typeBody tg` types a body.

## Main definitions

* `SimS`: a straight segment simulates one instruction from bases agreeing off the scratches.
* `RegTagOn`: the tag function gives every `Lopn` of a mnemonic a register tag.
* `sibPlainB`: an operand with no spilled SIB base or index.
* `lowerCoreOKB`: the cases of `LowerCore.lowerCore` the simulations below cover.

## Main results

* `fstepF_agreeS`: an `Lopn` that names no scratch and is no `MULX` steps from agreeing bases
  to agreeing bases.
* `instrOK_of_simS`: a simulation is the per-instruction condition of the expansion lift.
* `simS_append`, `simS_scratch`: sequencing of simulations, and a binop routed through `R15`.
* `simS_legalizeMov`, `simS_legalizeOneSrc`: the legalised copy and one-source instruction.
* `simS_legalizeBinop`, `simS_lowerTwoAddr`: the two-address lowering of a binop whose
  second source is no spill slot.
* `simS_lowerTwoAddrShiftImm`: the two-address shift by an immediate.
* `simS_cmovSpillSeq`, `simS_cmovSpillDst?`: the select with spilled operands.
* `simS_setccSpill?`: the materialised comparison with spilled operands.
* `fstepF_src2`, `simS_srcScratch`: a second source read by its cell, and through a scratch.
* `simS_legalizeBinopSpill`, `simS_lowerTwoAddrSpill`: the two-address lowering of a binop
  with a spilled second source and a register destination.
* `fstepF_dst1`, `simS_loadScratch`, `simS_legalizeMemLoad`: the destination of a one-source
  instruction, and the legalised load on a source with no spilled SIB base or index.
* `simS_lowerCore`: the lowering core on the instructions `lowerCoreOKB` admits.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LowerFuelMemF

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
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (renRM_id emptyP)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload

/-! ## 1. Simulation off the scratches -/

/-- A straight segment `js` simulates the instruction `i` off the scratches: from every pair
    of bases agreeing off `R15` and `R14`, a step of `i` from the first is matched by a run
    of `js` from the second to a base agreeing with the result, with the same zero flag. -/
def SimS (i : LinstrRM) (js : List LinstrRM) : Prop :=
  ∀ (s s' t : LstateM) (zf zt : Bool), AgreeS s s' → fstepF i s zf = some (t, zt) →
    ∃ t', runStraightF js s' zf = some (t', zt) ∧ AgreeS t t'

/-- Agreement off the scratches is kept by changes of the two program counters. -/
theorem AgreeS.setLpc {a b : LstateM} (h : AgreeS a b) (p q : Nat) :
    AgreeS (a.setLpc p) (b.setLpc q) := ⟨h.reg, h.arr, h.mem, h.cf, h.of⟩

/-- Agreement off the scratches is kept by a change of the right program counter. -/
theorem AgreeS.of_eqPc {a b c : LstateM} (h : AgreeS a b) (he : EqPc b c) : AgreeS a c := by
  unfold EqPc at he
  rw [he]
  exact ⟨h.reg, h.arr, h.mem, h.cf, h.of⟩

/-- **A simulation is the per-instruction condition of the expansion lift.** -/
theorem instrOK_of_simS {expand : LinstrRM → List LinstrRM} {i : LinstrRM} (hl : IsLopn i)
    (hj : ∀ j ∈ expand i, IsLopn j) (h : SimS i (expand i)) : InstrOK AgreeS expand i :=
  Or.inl ⟨hl, hj, h⟩

/-- The empty name is no scratch. -/
theorem keptS_empty : KeptS "" := ⟨by decide, by decide⟩

/-- A spill slot is no scratch. -/
theorem keptS_of_isSpill {n : String} (h : (LOperand.reg n).isSpill = true) : KeptS n := by
  refine ⟨?_, ?_⟩
  · rintro rfl; revert h; grind only [reloadScratch_not_spill]
  · rintro rfl; revert h; grind only [reloadScratch2_not_spill]

/-- The identity renaming on the names other than the scratches. -/
theorem renOn_id_keptS : RenOn id KeptS := ⟨fun _ _ _ _ h => h, keptS_empty, rfl⟩

/-- The empty program is its own identity renaming on the names other than the scratches. -/
theorem renProg_emptyS : RenProg id KeptS 0 emptyP emptyP :=
  ⟨rfl, fun _ => rfl, fun k _ => by simp [emptyP], fun k i _ h => by simp [emptyP] at h,
    fun k i _ h => by simp [emptyP] at h, fun l pc h => by simp⟩

/-- **A step from bases agreeing off the scratches.** An `Lopn` that names neither `R15` nor
    `R14` and is no `MULX` steps from agreeing bases to agreeing bases, with the same zero
    flag. -/
theorem fstepF_agreeS {i : LinstrRM} (hl : IsLopn i) (hn : ∀ n ∈ instrNames i.1, KeptS n)
    (hm : mulxFree i = true) {s s' t : LstateM} {zf zt : Bool} (hA : AgreeS s s')
    (h : fstepF i s zf = some (t, zt)) :
    ∃ t', fstepF i s' zf = some (t', zt) ∧ AgreeS t t' := by
  let S : LstateMF := { prog := { base := s, lfn := "" }, zf := zf }
  let S' : LstateMF := { prog := { base := s'.setLpc s.lpc, lfn := "" }, zf := zf }
  have hR : RelF id KeptS S S' :=
    ⟨⟨⟨rfl, fun r hr => hA.reg r hr⟩, fun r hr => hA.arr r hr, hA.mem⟩, rfl, rfl, hA.cf,
      hA.of⟩
  have hc : CondOK i := ⟨fun c l he => (by
    obtain ⟨d, o, s0, hd⟩ := hl; rw [hd] at he; cases he), hm⟩
  have he : evalInstrPMemF emptyP i S
      = some { prog := { base := t, lfn := "" }, zf := zt } := by
    rw [evalInstrPMemF_isLopn _ i S hl]
    change (fstepF i s zf).map _ = _
    rw [h]; rfl
  obtain ⟨T', hT', hRT, -⟩ := evalInstrPMemF_ren renOn_id_keptS renProg_emptyS i hn hc hR
    (Nat.zero_le _) he
  rw [renRM_id, evalInstrPMemF_isLopn _ i S' hl] at hT'
  obtain ⟨bz, hb, rfl⟩ := Option.map_eq_some_iff.mp hT'
  have hb' : fstepF i (s'.setLpc s.lpc) zf = some bz := hb
  rw [fstepF_setLpc] at hb'
  obtain ⟨⟨t'', z''⟩, h'', hbz⟩ := Option.map_eq_some_iff.mp hb'
  subst hbz
  obtain ⟨⟨⟨-, hreg⟩, harr, hmem⟩, -, hzf, hcf, hof⟩ := hRT
  refine ⟨t'', ?_, ⟨fun r hr => hreg r hr, fun r hr => harr r hr, hmem, hcf, hof⟩⟩
  rw [h'']
  simp only at hzf
  rw [hzf]

/-- An `Lopn` that names no scratch and is no `MULX` simulates itself. -/
theorem simS_self {i : LinstrRM} (hl : IsLopn i) (hn : ∀ n ∈ instrNames i.1, KeptS n)
    (hm : mulxFree i = true) : SimS i [i] := by
  intro s s' t zf zt hA h
  obtain ⟨t', h', hA'⟩ := fstepF_agreeS hl hn hm hA h
  exact ⟨t', by rw [runStraightF_cons, h']; rfl, hA'⟩

/-- The tag function `tg` gives every `Lopn` with mnemonic `opn` a register tag. -/
def RegTagOn (tg : LinstrR → MemTag) (opn : String) : Prop :=
  ∀ ds ss, ∃ cd, tg (.Lopn ds opn ss) = .reg cd

/-! ## 2. Two-address binops -/

/-- **The two-address binop off the scratches.** The pair `MOV d, s0 ; OP d, d, s1`
    simulates `OP d, s0, s1` off the scratches, when the binop names no scratch and is no
    `MULX`, `s1` is not the register `d` and `OP` is not the flag compare. -/
theorem simS_twoAddr (d s0 : String) (s1 : LOperand) (opn mov : String) (cd : Option Nat)
    (tagM : MemTag) (hmov : stripWidthTag mov = "MOV") (hcmp : opn ≠ withWidthTag 64 "CMP")
    (hd : s1 ≠ .reg d) (hn : ∀ n ∈ instrNames (binopWire d s0 s1 opn), KeptS n)
    (hm : mulxFree (binopWire d s0 s1 opn, .reg cd) = true) :
    SimS (binopWire d s0 s1 opn, .reg cd)
      [(movWire d s0 mov, tagM), (binopWire d d s1 opn, .reg cd)] := by
  intro s s' t zf zt hA h
  obtain ⟨t1, h1, hA1⟩ := fstepF_agreeS ⟨_, _, _, rfl⟩ hn hm hA h
  obtain ⟨t2, h2, hE⟩ := fstepF_twoAddr d s0 s1 opn mov cd tagM hmov hcmp hd h1
  exact ⟨t2, h2, AgreeS.of_eqPc hA1 hE⟩

/-- A two-address binop mnemonic is not the flag compare. -/
theorem ne_cmp_of_isTwoAddrBinop {opn : String} (hb : isTwoAddrBinop opn = true) :
    opn ≠ withWidthTag 64 "CMP" := by
  rintro rfl
  revert hb
  decide +kernel

/-- Agreement off the scratches is transitive. -/
theorem AgreeS.trans {a b c : LstateM} (h1 : AgreeS a b) (h2 : AgreeS b c) : AgreeS a c :=
  ⟨fun r hr => (h2.reg r hr).trans (h1.reg r hr), fun r hr => (h2.arr r hr).trans (h1.arr r hr),
    h2.mem.trans h1.mem, h2.cf.trans h1.cf, h2.of.trans h1.of⟩

/-- **Sequencing two simulations.** When every step of `i` is a step of `j` followed by a step
    of `k`, up to the program counter, and `sj`, `sk` simulate `j`, `k`, then `sj ++ sk`
    simulates `i`. -/
theorem simS_append {i j k : LinstrRM} {sj sk : List LinstrRM}
    (hsplit : ∀ (s t : LstateM) (zf zt : Bool), fstepF i s zf = some (t, zt) →
      ∃ u zu t2, fstepF j s zf = some (u, zu) ∧ fstepF k u zu = some (t2, zt) ∧ EqPc t t2)
    (hj : SimS j sj) (hk : SimS k sk) : SimS i (sj ++ sk) := by
  intro s s' t zf zt hA h
  obtain ⟨u, zu, t2, hu, ht2, hE⟩ := hsplit s t zf zt h
  obtain ⟨u', hu', hAu⟩ := hj s s' u zf zu hA hu
  obtain ⟨t3, ht3, hAt⟩ := hk u u' t2 zu zt hAu ht2
  refine ⟨t3, ?_, AgreeS.trans (AgreeS.of_eqPc (AgreeS.refl t) hE) hAt⟩
  rw [JasminLsemAddrMem.runStraightF_append, hu', Option.bind_some]
  exact ht3

/-- **The binop through the reload scratch.** The sequence
    `mov R15, s0 ; OP R15, R15, s1 ; mov d, R15` simulates `OP d, s0, s1` off the scratches,
    when the binop names no scratch and `OP` is not the flag compare. -/
theorem simS_scratch {opn m d s0 : String} {s1 : LOperand} {cd : Option Nat}
    (hm : stripWidthTag m = "MOV") (hcmp : opn ≠ withWidthTag 64 "CMP")
    (hn : ∀ n ∈ instrNames (.Lopn [.reg d] opn [.reg s0, s1]), KeptS n) (τ2 τ4 : MemTag) :
    SimS (.Lopn [.reg d] opn [.reg s0, s1], .reg cd)
      [(.Lopn [.reg reloadScratch] m [.reg s0], τ2),
       (.Lopn [.reg reloadScratch] opn [.reg reloadScratch, s1], .reg cd),
       (.Lopn [.reg d] m [.reg reloadScratch], τ4)] := by
  intro s s' t zf z hA h
  have hs1R : s1 ≠ .reg reloadScratch := by
    rintro rfl
    exact (hn reloadScratch (by simp [instrNames, opNames])).1 rfl
  obtain ⟨t1, ht1, hA1⟩ := fstepF_agreeS ⟨_, _, _, rfl⟩ hn
    (mulxFree_of_lopn1 ⟨_, _, _, rfl⟩) hA h
  have h1 : fstepF (.Lopn [.reg reloadScratch] opn [.reg s0, s1], .reg cd) s' zf
      = some (TwoAddrFuelMemF.movDst s' d reloadScratch t1, z) := by
    rw [TwoAddrFuelMemF.fstepF_dst opn _ _ cd d reloadScratch hcmp, ht1]; rfl
  obtain ⟨t2, ht2, hE2⟩ := fstepF_twoAddr reloadScratch s0 s1 opn m cd τ2 hm hcmp hs1R h1
  obtain ⟨p, rfl⟩ : ∃ p, t2 = (TwoAddrFuelMemF.movDst s' d reloadScratch t1).setLpc p :=
    ⟨_, hE2⟩
  have e3 := fstepF_movWire d reloadScratch m τ4 hm
    ((TwoAddrFuelMemF.movDst s' d reloadScratch t1).setLpc p) z
  have hdst : ∀ r, r ≠ d → t1.reg.lvm r = s'.reg.lvm r := fun r hr =>
    (JasminLsemStepFrame.fstepF_frame_dst ht1 (by simp [JasminLsemStepFrame.dstNames,
      opNames, hr])).1
  refine ⟨((((TwoAddrFuelMemF.movDst s' d reloadScratch t1).setLpc p).setReg d
      (((TwoAddrFuelMemF.movDst s' d reloadScratch t1).setLpc p).reg.lvm
        reloadScratch).2).nextPc), ?_, AgreeS.trans hA1 ?_⟩
  · rw [show [((LinstrR.Lopn [.reg reloadScratch] m [.reg s0]), τ2),
          ((LinstrR.Lopn [.reg reloadScratch] opn [.reg reloadScratch, s1]), MemTag.reg cd),
          ((LinstrR.Lopn [.reg d] m [.reg reloadScratch]), τ4)]
        = [(movWire reloadScratch s0 m, τ2),
            (binopWire reloadScratch reloadScratch s1 opn, .reg cd)]
          ++ [(movWire d reloadScratch m, τ4)] from rfl,
      JasminLsemAddrMem.runStraightF_append, ht2, Option.bind_some, runStraightF_cons, e3]
    rfl
  · refine ⟨fun r hr => ?_, fun r _ => ?_, ?_, ?_, ?_⟩
    · by_cases hrd : r = d
      · subst hrd
        simp [TwoAddrFuelMemF.movDst, LstateM.setLpc, LstateM.setReg, LstateM.nextPc]
      · have hrR : r ≠ reloadScratch := hr.1
        simp [TwoAddrFuelMemF.movDst, LstateM.setLpc, LstateM.setReg, LstateM.nextPc, hrd,
          hrR, hdst r hrd]
    · simp [TwoAddrFuelMemF.movDst, LstateM.setLpc, LstateM.setReg, LstateM.nextPc]
    · simp [TwoAddrFuelMemF.movDst, LstateM.setLpc, LstateM.setReg, LstateM.nextPc]
    · simp [TwoAddrFuelMemF.movDst, LstateM.setLpc, LstateM.setReg, LstateM.nextPc]
    · simp [TwoAddrFuelMemF.movDst, LstateM.setLpc, LstateM.setReg, LstateM.nextPc]

/-! ## 3. Register copies and one-source instructions -/

/-- **The legalised register copy.** `legalizeMov` simulates the copy `mov d, s` off the
    scratches, when the copy names no scratch and its mnemonic strips to `MOV` or is a
    `copyQ` mnemonic. -/
theorem simS_legalizeMov {tg : LinstrR → MemTag} {mov : String} {d s : LOperand}
    (hcp : stripWidthTag mov = "MOV" ∨ copyQ mov = true)
    (hn : ∀ n ∈ instrNames (.Lopn [d] mov [s]), KeptS n) :
    SimS (.Lopn [d] mov [s], tg (.Lopn [d] mov [s]))
      ((legalizeMov d s mov).map fun y => (y, tg y)) := by
  unfold legalizeMov
  split
  · rename_i hsp
    simp only [Bool.and_eq_true] at hsp
    obtain ⟨hds, hss⟩ := hsp
    cases d with
    | reg dn =>
        cases s with
        | reg sn =>
            simp only [List.map_cons, List.map_nil]
            intro a a' t zf zt hA h
            exact fstepF_copySpill dn sn mov _ _ _ hcp (keptS_of_isSpill hss) hA h
        | _ => simp [LOperand.isSpill] at hss
    | _ => simp [LOperand.isSpill] at hds
  · simpa only [List.map_cons, List.map_nil] using
      simS_self ⟨_, _, _, rfl⟩ hn (mulxFree_of_lopn1 ⟨_, _, _, rfl⟩)

/-- **The legalised one-source instruction.** Under a move selection that keeps the
    mnemonic, `legalizeOneSrc` simulates `opn d, s` off the scratches, when the instruction
    names no scratch, and a copy mnemonic strips to `MOV` or is a `copyQ` mnemonic. -/
theorem simS_legalizeOneSrc {tg : LinstrR → MemTag} {u64 : Bool} {opn : String}
    {d s : LOperand} (hmn : spillImmMovMnem u64 opn d s = opn)
    (hcp : (stripWidthTag opn == "MOV" || stripWidthTag opn == "MOVQ") = true →
      stripWidthTag opn = "MOV" ∨ copyQ opn = true)
    (hn : ∀ n ∈ instrNames (.Lopn [d] opn [s]), KeptS n) :
    SimS (.Lopn [d] opn [s], tg (.Lopn [d] opn [s]))
      ((legalizeOneSrc u64 opn d s).map fun y => (y, tg y)) := by
  unfold legalizeOneSrc
  rw [hmn]
  split
  · rename_i hc
    exact simS_legalizeMov (hcp hc) hn
  · simpa only [List.map_cons, List.map_nil] using
      simS_self ⟨_, _, _, rfl⟩ hn (mulxFree_of_lopn1 ⟨_, _, _, rfl⟩)

/-! ## 4. Two-address binops -/

/-- **The legalised two-address binop.** For a second source `s1` that is no spill slot,
    `legalizeBinop` simulates the register-tagged `OP d, d, s1` off the scratches, when the
    binop names no scratch and `OP` is not the flag compare. -/
theorem simS_legalizeBinop {tg : LinstrR → MemTag} {d : String} {s1 : LOperand}
    {opn mov : String} {cd : Option Nat}
    (htg : ∀ D X, tg (.Lopn [.reg D] opn [.reg X, s1]) = .reg cd)
    (hmov : stripWidthTag mov = "MOV") (hcmp : opn ≠ withWidthTag 64 "CMP")
    (hs1 : s1.isSpill = false)
    (hn : ∀ n ∈ instrNames (.Lopn [.reg d] opn [.reg d, s1]), KeptS n) :
    SimS (.Lopn [.reg d] opn [.reg d, s1], .reg cd)
      ((legalizeBinop (.reg d) s1 opn mov).map fun y => (y, tg y)) := by
  unfold legalizeBinop
  rw [hs1]
  cases hd : (LOperand.reg d).isSpill
  · simp only [List.map_cons, List.map_nil, htg]
    exact simS_self ⟨_, _, _, rfl⟩ hn (mulxFree_of_lopn1 ⟨_, _, _, rfl⟩)
  · simp only [List.map_cons, List.map_nil, htg]
    exact simS_scratch hmov hcmp hn _ _

/-- **The copy followed by the two-address binop.** When `sk` simulates the register-tagged
    `OP d, d, s1`, the legalised copy `mov d, s0` followed by `sk` simulates `OP d, s0, s1`
    off the scratches, when `d` and `s0` are no scratches, `s1` is not the register `d` and
    `OP` is not the flag compare. -/
theorem simS_movThen {tg : LinstrR → MemTag} {d s0 : String} {s1 : LOperand}
    {opn mov : String} {cd : Option Nat} {sk : List LinstrRM}
    (hmov : stripWidthTag mov = "MOV") (hcmp : opn ≠ withWidthTag 64 "CMP")
    (hd : s1 ≠ .reg d) (hkd : KeptS d) (hks0 : KeptS s0)
    (hk : SimS (.Lopn [.reg d] opn [.reg d, s1], .reg cd) sk) :
    SimS (.Lopn [.reg d] opn [.reg s0, s1], .reg cd)
      ((legalizeMov (.reg d) (.reg s0) mov).map (fun y => (y, tg y)) ++ sk) := by
  refine simS_append (j := (.Lopn [.reg d] mov [.reg s0], tg (.Lopn [.reg d] mov [.reg s0])))
    (k := (.Lopn [.reg d] opn [.reg d, s1], .reg cd)) ?_ (simS_legalizeMov (Or.inl hmov) ?_) hk
  · intro s t zf zt h
    obtain ⟨t2, h2, hE⟩ := fstepF_twoAddr d s0 s1 opn mov cd
      (tg (.Lopn [.reg d] mov [.reg s0])) hmov hcmp hd h
    rw [runStraightF_cons] at h2
    cases hu : fstepF (movWire d s0 mov, tg (.Lopn [.reg d] mov [.reg s0])) s zf with
    | none => rw [hu] at h2; cases h2
    | some uz =>
        rw [hu, Option.bind_some, runStraightF_cons] at h2
        cases hk : fstepF (binopWire d d s1 opn, .reg cd) uz.1 uz.2 with
        | none => rw [hk] at h2; cases h2
        | some q =>
            rw [hk, Option.bind_some, runStraightF_nil] at h2
            exact ⟨uz.1, uz.2, t2, hu, hk.trans h2, hE⟩
  · intro n hn1
    simp only [instrNames, opNames, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hn1
    rcases hn1 with rfl | rfl
    · exact hkd
    · exact hks0

/-- **The two-address lowering of a binop.** For a binop `OP d, s0, s1` of the two-address
    alphabet whose second source `s1` is no spill slot and needs no wide-immediate
    materialisation, `lowerTwoAddr` simulates it off the scratches, when the binop names no
    scratch, every binop `OP D, X, s1` carries the register tag of the source, and `s1` is not
    the register `d`. -/
theorem simS_lowerTwoAddr {tg : LinstrR → MemTag} {d s0 : String} {s1 : LOperand}
    {opn mov : String} {cd : Option Nat}
    (htg : ∀ D X, tg (.Lopn [.reg D] opn [.reg X, s1]) = .reg cd)
    (hb : isTwoAddrBinop opn = true) (hmov : stripWidthTag mov = "MOV")
    (hd : s1 ≠ .reg d) (hs1 : s1.isSpill = false)
    (himm : materializeWideImm s1 mov = ([], s1))
    (hn : ∀ n ∈ instrNames (.Lopn [.reg d] opn [.reg s0, s1]), KeptS n) :
    SimS (.Lopn [.reg d] opn [.reg s0, s1], tg (.Lopn [.reg d] opn [.reg s0, s1]))
      ((lowerTwoAddr (.reg d) (.reg s0) s1 opn mov).map fun y => (y, tg y)) := by
  have hcmp := ne_cmp_of_isTwoAddrBinop hb
  have hkd : KeptS d := hn d (by simp [instrNames, opNames])
  have hks0 : KeptS s0 := hn s0 (by simp [instrNames, opNames])
  have hn' : ∀ n ∈ instrNames (.Lopn [.reg d] opn [.reg d, s1]), KeptS n := by
    intro n hn1
    simp only [instrNames, opNames, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons] at hn1
    rcases hn1 with rfl | rfl | h1
    · exact hkd
    · exact hkd
    · exact hn n (by simp [instrNames, opNames, h1])
  rw [htg]
  unfold lowerTwoAddr
  rw [himm]
  by_cases hds : (LOperand.reg d) = .reg s0
  · obtain rfl : d = s0 := by injection hds
    simpa only [ite_true, List.nil_append] using
      simS_legalizeBinop (tg := tg) (mov := mov) htg hmov hcmp hs1 hn'
  · by_cases hsp : (LOperand.reg d).isSpill = true
    · simp only [hds, hsp, ite_false, ite_true, List.nil_append, scratchBinop, hs1,
        Bool.false_eq_true, List.cons_append, List.map_cons, List.map_nil, htg]
      exact simS_scratch hmov hcmp hn _ _
    · simp only [hds, hsp, Bool.false_eq_true, ite_false, List.nil_append, List.append_nil,
        List.map_append]
      exact simS_movThen hmov hcmp hd hkd hks0 (simS_legalizeBinop htg hmov hcmp hs1 hn')

/-- **The two-address shift by an immediate.** `lowerTwoAddrShiftImm` simulates the
    register-tagged `OP d, s0, #v` off the scratches, when the shift names no scratch, every
    shift `OP D, X, #v` carries the register tag of the source, and `OP` is not the flag
    compare. -/
theorem simS_lowerTwoAddrShiftImm {tg : LinstrR → MemTag} {d s0 : String} {v : Nat}
    {opn mov : String} {cd : Option Nat}
    (htg : ∀ D X, tg (.Lopn [.reg D] opn [.reg X, .imm v]) = .reg cd)
    (hmov : stripWidthTag mov = "MOV") (hcmp : opn ≠ withWidthTag 64 "CMP")
    (hn : ∀ n ∈ instrNames (.Lopn [.reg d] opn [.reg s0, .imm v]), KeptS n) :
    SimS (.Lopn [.reg d] opn [.reg s0, .imm v], tg (.Lopn [.reg d] opn [.reg s0, .imm v]))
      ((lowerTwoAddrShiftImm (.reg d) (.reg s0) v opn mov).map fun y => (y, tg y)) := by
  have hkd : KeptS d := hn d (by simp [instrNames, opNames])
  have hks0 : KeptS s0 := hn s0 (by simp [instrNames, opNames])
  have hn' : ∀ n ∈ instrNames (.Lopn [.reg d] opn [.reg d, .imm v]), KeptS n := by
    intro n hn1
    simp only [instrNames, opNames, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hn1
    rcases hn1 with rfl | rfl <;> exact hkd
  rw [htg]
  unfold lowerTwoAddrShiftImm
  cases hsp : (LOperand.reg d).isSpill
  · by_cases hds : (LOperand.reg d) = .reg s0
    · obtain rfl : d = s0 := by injection hds
      simp only [Bool.false_eq_true, ite_false, ite_true, List.map_cons, List.map_nil, htg]
      exact simS_self ⟨_, _, _, rfl⟩ hn (mulxFree_of_lopn1 ⟨_, _, _, rfl⟩)
    · simp only [Bool.false_eq_true, ite_false, hds, List.map_append, List.map_cons,
        List.map_nil, htg]
      exact simS_movThen hmov hcmp (by simp) hkd hks0
        (simS_self ⟨_, _, _, rfl⟩ hn' (mulxFree_of_lopn1 ⟨_, _, _, rfl⟩))
  · simp only [ite_true, List.map_cons, List.map_nil, htg]
    exact simS_scratch hmov hcmp hn _ _

/-! ## 4. Selects and comparisons with spilled operands -/

/-- **The select with spilled operands.** `cmovSpillSeq` simulates the register-tagged select
    `CMOV:64 D, [C, T, F]` off the scratches, when `C`, `T` and `F` are no scratches. -/
theorem simS_cmovSpillSeq {tg : LinstrR → MemTag} (htg : RegTagOn tg "CMOV:64")
    {D C T F : String} (hC : KeptS C) (hT : KeptS T) (hF : KeptS F) :
    SimS (.Lopn [.reg D] "CMOV:64" [.reg C, .reg T, .reg F],
        tg (.Lopn [.reg D] "CMOV:64" [.reg C, .reg T, .reg F]))
      ((cmovSpillSeq "CMOV:64" (.reg D) (.reg C) (.reg T) (.reg F)).map fun y => (y, tg y)) := by
  intro a a' t zf zt hA h
  obtain ⟨cd, hcd⟩ := htg [.reg D] [.reg C, .reg T, .reg F]
  rw [hcd] at h
  unfold cmovSpillSeq
  cases hc : (LOperand.reg C).isSpill <;> cases hd : (LOperand.reg D).isSpill
  · obtain ⟨rfl, w, v, rfl, h2⟩ := fstepF_cmov64_congr (D' := D) (cd' := cd)
      (hA.reg C hC) (hA.reg T hT) (hA.reg F hF) h
    simp only [Bool.false_eq_true, ite_false, List.nil_append, List.map_cons, List.map_nil,
      hcd]
    exact ⟨_, by rw [runStraightF_cons, h2]; rfl, hA.setReg D v⟩
  · obtain ⟨cd', hcd'⟩ := htg [.reg reloadScratch] [.reg C, .reg T, .reg F]
    simp only [Bool.false_eq_true, ite_false, ite_true, List.nil_append, List.map_cons,
      List.map_nil, hcd']
    exact fstepF_cmovDstSpill D C T F cd cd' _ hC hT hF hA h
  · obtain ⟨cd', hcd'⟩ := htg [.reg D] [.reg reloadScratch2, .reg T, .reg F]
    simp only [Bool.false_eq_true, ite_false, ite_true, List.cons_append, List.nil_append,
      List.map_cons, List.map_nil, hcd']
    exact fstepF_cmovCondSpill D C T F cd cd' _ hC hT hF hA h
  · obtain ⟨cd', hcd'⟩ := htg [.reg reloadScratch] [.reg reloadScratch2, .reg T, .reg F]
    simp only [ite_true, List.cons_append, List.nil_append, List.map_cons, List.map_nil, hcd']
    exact fstepF_cmovCondDstSpill D C T F cd cd' _ _ hC hT hF hA h

/-- **The scratch select.** Where `cmovSpillDst?` is defined on a select over register
    operands, its expansion simulates the select off the scratches, when the condition and
    the two values are no scratches. -/
theorem simS_cmovSpillDst? {tg : LinstrR → MemTag} (htg : RegTagOn tg "CMOV:64")
    {opn D C T F : String} {L : List LinstrR}
    (h : cmovSpillDst? [.reg D] opn [.reg C, .reg T, .reg F] = some L)
    (hC : KeptS C) (hT : KeptS T) (hF : KeptS F) :
    SimS (.Lopn [.reg D] opn [.reg C, .reg T, .reg F],
        tg (.Lopn [.reg D] opn [.reg C, .reg T, .reg F])) (L.map fun y => (y, tg y)) := by
  unfold cmovSpillDst? at h
  dsimp only at h
  split_ifs at h with hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨-, rfl⟩ := hc
  cases h
  exact simS_cmovSpillSeq htg hC hT hF


/-- **The materialised comparison with spilled operands.** Where `setccSpill?` is defined on
    a register-tagged comparison `SET<cc> D, [A, B]`, its expansion simulates the comparison
    off the scratches, when `A` and `B` are no scratches. -/
theorem simS_setccSpill? {tg : LinstrR → MemTag} {c : JasminDialect.JasminCmp} {wOp : Nat}
    (htg : RegTagOn tg (withWidthTag wOp (cmpName c))) {D A B : String} {L : List LinstrR}
    (h : setccSpill? [.reg D] (withWidthTag wOp (cmpName c)) [.reg A, .reg B] = some L)
    (hA' : KeptS A) (hB' : KeptS B) :
    SimS (.Lopn [.reg D] (withWidthTag wOp (cmpName c)) [.reg A, .reg B],
        tg (.Lopn [.reg D] (withWidthTag wOp (cmpName c)) [.reg A, .reg B]))
      (L.map fun y => (y, tg y)) := by
  unfold setccSpill? at h
  dsimp only at h
  split_ifs at h
  cases h
  intro a a' t zf zt hA hs
  obtain ⟨cd, hcd⟩ := htg [.reg D] [.reg A, .reg B]
  obtain ⟨cd', hcd'⟩ := htg [.reg reloadScratch] [.reg reloadScratch, .reg reloadScratch2]
  rw [hcd] at hs
  simp only [List.map_cons, List.map_nil, hcd']
  exact fstepF_setccSpill c wOp D A B _ cd cd' _ _ _ (stripWidthTag_setccMov _) hA' hB' hA hs

/-! ## 5. A second source read through a scratch -/

/-- The register step of a two-source instruction reads its second register source by its
    cell: under two names holding the same cell, the step is the same. -/
theorem lsemStepMC_src2 (st : LstateN) (d x R S opn : String) (h : st.lvm R = st.lvm S) :
    lsemStepMC (binopWire d x (.reg R) opn) st = lsemStepMC (binopWire d x (.reg S) opn) st := by
  have hg : ∀ w, st.getW R w = st.getW S w := fun w => by unfold LstateN.getW; rw [h]
  simp only [binopWire, lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?,
    sbbhiStruct?, lsemStepSh, sarStruct?, lsemStepN, evalOperandN, hg]
  by_cases hm : stripWidthTag opn = "MULXHI" <;> simp only [hm, ↓reduceIte, hg]

/-- **The second source by its cell.** A register-tagged two-source instruction other than
    the flag compare steps alike under two names of its second source that hold the same
    cell, at any two register tags. -/
theorem fstepF_src2 (d x R S opn : String) (cd cd' : Option Nat)
    (hcmp : opn ≠ withWidthTag 64 "CMP") (s : LstateM) (zf : Bool)
    (h : s.reg.lvm R = s.reg.lvm S) :
    fstepF (binopWire d x (.reg R) opn, .reg cd') s zf
      = fstepF (binopWire d x (.reg S) opn, .reg cd) s zf := by
  have he : ∀ w, evalOperandN s.reg w (.reg R) = evalOperandN s.reg w (.reg S) := fun w => by
    simp only [evalOperandN]; unfold LstateN.getW; rw [h]
  rw [fstepF_binopWire _ _ _ _ _ hcmp, fstepF_binopWire _ _ _ _ _ hcmp]
  unfold stepMemF
  rw [lsemStepMem_binopWire, lsemStepMem_binopWire, lsemStepMC_src2 _ _ _ _ _ _ h]
  cases lsemStepMC (binopWire d x (.reg S) opn) s.reg with
  | some r =>
      simp only [Option.map_some]
      unfold withALUFlags aluFlagOp?
      simp only [binopWire]
      split_ifs <;> simp only [he]
  | none =>
      simp only [Option.map_none]
      unfold carryArgs? carryStep wideArgs? wideStep
      simp only [binopWire]
      split_ifs <;> simp only [he]

/-- **A second source read through a scratch.** For a scratch `R`, the pair
    `MOV R, S ; OP d, x, R` simulates the register-tagged `OP d, x, S` off the scratches,
    when the binop names no scratch and `OP` is not the flag compare. -/
theorem simS_srcScratch {d x R S opn mov : String} {cd cd' : Option Nat} (τ : MemTag)
    (hR : ¬ KeptS R) (hmov : stripWidthTag mov = "MOV") (hcmp : opn ≠ withWidthTag 64 "CMP")
    (hn : ∀ n ∈ instrNames (binopWire d x (.reg S) opn), KeptS n) :
    SimS (binopWire d x (.reg S) opn, .reg cd)
      [(movWire R S mov, τ), (binopWire d x (.reg R) opn, .reg cd')] := by
  intro s s' t zf zt hA h
  have hS : KeptS S := hn S (by simp [instrNames, binopWire, opNames])
  have hRS : R ≠ S := fun e => hR (e ▸ hS)
  have hAu : AgreeS s (s'.setReg R (s'.reg.lvm S).2).nextPc := hA.setScratch hR _
  have hu : ((s'.setReg R (s'.reg.lvm S).2).nextPc).reg.lvm R
      = ((s'.setReg R (s'.reg.lvm S).2).nextPc).reg.lvm S :=
    (lvm_copy s' R S).trans (lvm_copy_other s' S hRS.symm).symm
  obtain ⟨t', ht', hAt⟩ := fstepF_agreeS ⟨_, _, _, rfl⟩ hn
    (mulxFree_of_lopn1 ⟨_, _, _, rfl⟩) hAu h
  refine ⟨t', ?_, hAt⟩
  rw [runStraightF_cons, fstepF_movWire R S mov τ hmov, Option.bind_some, runStraightF_cons,
    fstepF_src2 d x R S opn cd cd' hcmp _ zf hu, ht']
  rfl

/-- The step of the constant-index store `STOREIMM [d] [b, x, #k]` at the tag `.storeImm w n`
    reads the array of `b` at shape `(w, n)` and the cell of `x` at width `w`, writes the
    updated array to `d` and keeps the zero flag. -/
theorem fstepF_storeImmCell (d b x : String) (k w n : Nat) (u : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg d] "STOREIMM" [.reg b, .reg x, .imm k], .storeImm w n) u zf
      = (u.getArr b w n).bind fun arr => (u.reg.getW x w).map fun vv =>
          ((u.setArr d (JasminDialect.stackSet arr k vv)).nextPc, zf) := by
  simp only [fstepF, cmpArgs?, movRegArgs?]
  rw [stepMemF_of_quiet rfl rfl rfl]
  simp only [lsemStepMem, storeImmStruct?, ite_true]
  cases u.getArr b w n <;> cases u.reg.getW x w <;> rfl

/-- **A stored value read through a scratch.** For a value register `v` other than the
    scratches, when the store `STOREIMM [d] [b, v, #k]` at the tag `.storeImm w n` steps from
    a base `s`, the pair `MOV:64 R15, v ; STOREIMM [d] [b, R15, #k]` runs from every base
    that agrees with `s` off the scratches and holds the array of `s` at `b`, to a base that
    agrees with the result off the scratches, with the same zero flag. The base `b` may be the
    scratch `R14`. -/
theorem fstepF_storeImmScratch {d b v : String} (k w n : Nat) (τ : MemTag) (hv : KeptS v)
    {s s' t : LstateM} {zf zt : Bool} (hA : AgreeS s s') (hb : s'.larr b = s.larr b)
    (h : fstepF (.Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm k], .storeImm w n) s zf
      = some (t, zt)) :
    ∃ t', runStraightF [(.Lopn [.reg reloadScratch] "MOV:64" [.reg v], τ),
        (.Lopn [.reg d] "STOREIMM" [.reg b, .reg reloadScratch, .imm k], .storeImm w n)] s' zf
        = some (t', zt) ∧ AgreeS t t' := by
  let u := (s'.setReg reloadScratch (s'.reg.lvm v).2).nextPc
  have hga : u.getArr b w n = s.getArr b w n := by
    exact (fun (a c : LstateM) (h : a.larr b = c.larr b) =>
      (by unfold LstateM.getArr; rw [h] : a.getArr b w n = c.getArr b w n)) u s hb
  have hgv : u.reg.getW reloadScratch w = s.reg.getW v w := by
    unfold LstateN.getW
    rw [lvm_copy, hA.reg v hv]
  rw [fstepF_storeImmCell] at h
  cases ha : s.getArr b w n with
  | none => rw [ha] at h; cases h
  | some arr =>
    cases hvv : s.reg.getW v w with
    | none => rw [ha, hvv] at h; cases h
    | some vv =>
      rw [ha, hvv] at h
      simp only [Option.bind_some, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨(u.setArr d (JasminDialect.stackSet arr k vv)).nextPc, ?_, ?_⟩
      · rw [runStraightF_cons, show (LinstrR.Lopn [.reg reloadScratch] "MOV:64" [.reg v], τ)
            = (movWire reloadScratch v "MOV:64", τ) from rfl,
          fstepF_movWire reloadScratch v "MOV:64" τ stripWidthTag_mov64,
          Option.bind_some, runStraightF_cons, fstepF_storeImmCell, hga, hgv, ha, hvv]
        rfl
      · refine ⟨fun r hr => ?_, fun r hr => ?_, hA.mem, hA.cf, hA.of⟩
        · have hrS : r ≠ reloadScratch := hr.1
          simp [u, LstateM.setReg, LstateM.nextPc, hrS, hA.reg r hr]
        · by_cases hrd : r = d
          · simp [u, LstateM.setArr, LstateM.setReg, LstateM.nextPc, hrd]
          · simp [u, LstateM.setArr, LstateM.setReg, LstateM.nextPc, hrd, hA.arr r hr]

/-- **The spilled-value store through a scratch.** For a base `b` and a value register `v`
    other than the scratches, `MOV:64 R15, v ; STOREIMM [d] [b, R15, #k]` simulates
    `STOREIMM [d] [b, v, #k]` at the tag `.storeImm w n` off the scratches. -/
theorem simS_storeImmScratch {d b v : String} (k w n : Nat) (τ : MemTag) (hb : KeptS b)
    (hv : KeptS v) :
    SimS (.Lopn [.reg d] "STOREIMM" [.reg b, .reg v, .imm k], .storeImm w n)
      [(.Lopn [.reg reloadScratch] "MOV:64" [.reg v], τ),
        (.Lopn [.reg d] "STOREIMM" [.reg b, .reg reloadScratch, .imm k], .storeImm w n)] :=
  fun _ _ _ _ _ hA h => fstepF_storeImmScratch k w n τ hv hA (hA.arr b hb) h

/-- **The legalised binop with a spilled second source.** For a register `d` and a spill
    slot `S`, `legalizeBinop` simulates the register-tagged `OP d, d, S` off the scratches,
    when the binop names no scratch, every binop `OP D, X, R15` carries one register tag
    and `OP` is not the flag compare. -/
theorem simS_legalizeBinopSpill {tg : LinstrR → MemTag} {d S opn mov : String}
    {cd cd' : Option Nat}
    (htg : ∀ D X, tg (.Lopn [.reg D] opn [.reg X, .reg reloadScratch]) = .reg cd')
    (hmov : stripWidthTag mov = "MOV") (hcmp : opn ≠ withWidthTag 64 "CMP")
    (hd : (LOperand.reg d).isSpill = false) (hS : (LOperand.reg S).isSpill = true)
    (hn : ∀ n ∈ instrNames (.Lopn [.reg d] opn [.reg d, .reg S]), KeptS n) :
    SimS (.Lopn [.reg d] opn [.reg d, .reg S], .reg cd)
      ((legalizeBinop (.reg d) (.reg S) opn mov).map fun y => (y, tg y)) := by
  unfold legalizeBinop
  rw [hd, hS]
  simp only [List.map_cons, List.map_nil, htg]
  exact simS_srcScratch _ not_keptS_reloadScratch hmov hcmp hn

/-- **The two-address lowering of a binop with a spilled second source.** For a binop
    `OP d, s0, S` of the two-address alphabet with a register destination `d` and a spill
    slot `S`, `lowerTwoAddr` simulates it off the scratches, when the binop names no scratch,
    every binop `OP D, X, S` carries the register tag of the source and every binop
    `OP D, X, R15` one register tag. -/
theorem simS_lowerTwoAddrSpill {tg : LinstrR → MemTag} {d s0 S opn mov : String}
    {cd cd' : Option Nat}
    (htg : ∀ D X, tg (.Lopn [.reg D] opn [.reg X, .reg S]) = .reg cd)
    (htg' : ∀ D X, tg (.Lopn [.reg D] opn [.reg X, .reg reloadScratch]) = .reg cd')
    (hb : isTwoAddrBinop opn = true) (hmov : stripWidthTag mov = "MOV")
    (hd : (LOperand.reg d).isSpill = false) (hS : (LOperand.reg S).isSpill = true)
    (hn : ∀ n ∈ instrNames (.Lopn [.reg d] opn [.reg s0, .reg S]), KeptS n) :
    SimS (.Lopn [.reg d] opn [.reg s0, .reg S], tg (.Lopn [.reg d] opn [.reg s0, .reg S]))
      ((lowerTwoAddr (.reg d) (.reg s0) (.reg S) opn mov).map fun y => (y, tg y)) := by
  have hcmp := ne_cmp_of_isTwoAddrBinop hb
  have hkd : KeptS d := hn d (by simp [instrNames, opNames])
  have hks0 : KeptS s0 := hn s0 (by simp [instrNames, opNames])
  have hdS : LOperand.reg S ≠ .reg d := by
    intro e; rw [e, hd] at hS; cases hS
  have hn' : ∀ n ∈ instrNames (.Lopn [.reg d] opn [.reg d, .reg S]), KeptS n := by
    intro n hn1
    simp only [instrNames, opNames, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.cons_append, List.nil_append, List.mem_cons] at hn1
    rcases hn1 with rfl | rfl | rfl | h1
    · exact hkd
    · exact hkd
    · exact hn _ (by simp [instrNames, opNames])
    · simp at h1
  rw [htg]
  unfold lowerTwoAddr
  simp only [materializeWideImm]
  by_cases hds : (LOperand.reg d) = .reg s0
  · obtain rfl : d = s0 := by injection hds
    simpa only [ite_true, List.nil_append] using
      simS_legalizeBinopSpill (tg := tg) (mov := mov) htg' hmov hcmp hd hS hn'
  · simp only [hds, hd, Bool.false_eq_true, ite_false, List.nil_append, List.append_nil,
      List.map_append]
    exact simS_movThen hmov hcmp hdS hkd hks0
      (simS_legalizeBinopSpill htg' hmov hcmp hd hS hn')

/-! ## 6. One-source loads -/

/-- The register step of a one-source instruction writes, at any destination `D'`, the word
    it writes at `D`. -/
theorem lsemStepMC_dst1 (opn : String) (a : LOperand) (D D' : String) (s : LstateN) :
    lsemStepMC (.Lopn [.reg D'] opn [a]) s =
      (lsemStepMC (.Lopn [.reg D] opn [a]) s).map
        (fun t => (s.setReg D' (t.lvm D).2).nextPc) := by
  cases a <;> simp only [lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?,
    sbbhiStruct?, lsemStepSh, sarStruct?, lsemStepN] <;> (repeat' split) <;>
    simp_all [LstateN.setReg, LstateN.nextPc]

/-- The typed register step of a one-source instruction writes, at any destination `D'`, the
    word it writes at `D`. -/
theorem lsemStepCast_dst1 (opn : String) (a : LOperand) (cd : Option Nat) (D D' : String)
    (s : LstateN) :
    lsemStepCast (.Lopn [.reg D'] opn [a], cd) s =
      (lsemStepCast (.Lopn [.reg D] opn [a], cd) s).map
        (fun t => (s.setReg D' (t.lvm D).2).nextPc) := by
  have hMC := lsemStepMC_dst1 opn a D D' s
  cases a <;> cases cd <;> simp only [lsemStepCast, castStruct?, movImmStruct?, hMC]
  all_goals
    split_ifs <;> (repeat' split) <;>
      simp_all only [Option.map_some, Option.map_none, Option.some.injEq, Prod.mk.injEq,
        reduceCtorEq, BitVec.truncate_eq_setWidth, Sigma.mk.injEq] <;>
      (rw [TwoAddrFuelMemF.lvm_nextPc_setReg_self]; try (subst_vars; grind))

/-- The memory step of a one-source instruction other than the array zeroing writes, at any
    destination `D'`, the cell it writes at `D`. -/
theorem lsemStepMem_dst1 (opn : String) (a : LOperand) (τ : MemTag) (D D' : String)
    (hz : opn ≠ "ZEROARR") (s : LstateM) :
    lsemStepMem (.Lopn [.reg D'] opn [a], τ) s =
      (lsemStepMem (.Lopn [.reg D] opn [a], τ) s).map (TwoAddrFuelMemF.movDst s D D') := by
  have hC := lsemStepCast_dst1 opn a none D D' s.reg
  have hC' := fun cd => lsemStepCast_dst1 opn a cd D D' s.reg
  cases τ <;> simp only [lsemStepMem, loadStruct?, storeStruct?, loadCStruct?, storeCStruct?,
    zeroStruct?, storeImmStruct?, hz, ite_false]
  all_goals first
    | rfl
    | (simp only [hC', Option.map_map]; rfl)
    | (cases a <;> dsimp only <;> (try split_ifs) <;>
        first
          | (simp only [hC, Option.map_map]; rfl)
          | ((repeat' split) <;>
              (simp_all only [Int.ofNat_eq_natCast, Option.map_some, Option.map_none,
                Option.some.injEq, Prod.mk.injEq, reduceCtorEq, TwoAddrFuelMemF.movDst,
                LstateM.setReg, LstateM.nextPc]
               try rw [TwoAddrFuelMemF.lvm_nextPc_setReg_self])))

/-- **The destination of a one-source instruction.** A one-source instruction other than the
    array zeroing steps, at any destination `D'` and any tag, to the state it steps to at `D`,
    with the cell written at `D` written at `D'` and every other register as before the
    step. -/
theorem fstepF_dst1 (opn : String) (a : LOperand) (τ : MemTag) (D D' : String)
    (hz : opn ≠ "ZEROARR") (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg D'] opn [a], τ) s zf =
      (fstepF (.Lopn [.reg D] opn [a], τ) s zf).map
        (fun p => (TwoAddrFuelMemF.movDst s D D' p.1, p.2)) := by
  have hc : ∀ E, cmpArgs? (.Lopn [.reg E] opn [a], τ) = none := fun E => rfl
  have hs : ∀ E, stepMemF (.Lopn [.reg E] opn [a], τ) s
      = lsemStepMem (.Lopn [.reg E] opn [a], τ) s := fun E => by
    unfold stepMemF withALUFlags
    cases lsemStepMem (.Lopn [.reg E] opn [a], τ) s <;> rfl
  have hm := lsemStepMem_dst1 opn a τ D D' hz s
  unfold fstepF
  simp only [hc, hs, hm]
  cases a with
  | reg x =>
      simp only [movRegArgs?]
      split_ifs
      · clear hm hs hc
        dsimp only
        rcases h : readReg s.reg (.reg x) with _ | ⟨w, v⟩
        · rfl
        · simp only [TwoAddrFuelMemF.movDst, Option.map_some, LstateM.setReg, LstateM.nextPc]
          rw [TwoAddrFuelMemF.lvm_nextPc_setReg_self]
      · clear hm hs hc
        dsimp only
        rcases h : readReg s.reg (.reg x) with _ | ⟨w, v⟩
        · rfl
        · simp only [TwoAddrFuelMemF.movDst, Option.map_some, LstateM.setReg, LstateM.nextPc]
          rw [TwoAddrFuelMemF.lvm_nextPc_setReg_self]
      · cases lsemStepMem (.Lopn [.reg D] opn [.reg x], τ) s <;> rfl
  | _ =>
      simp only [movRegArgs?]
      cases lsemStepMem (.Lopn [.reg D] opn [_], τ) s <;> rfl

/-- **A load through the reload scratch.** The pair `opn R15, s ; mov d, R15` simulates the
    one-source `opn d, s` off the scratches, when the instruction names no scratch and is no
    array zeroing, and both loads carry one tag. -/
theorem simS_loadScratch {d opn m : String} {a : LOperand} {τ τ2 : MemTag}
    (hm : stripWidthTag m = "MOV") (hz : opn ≠ "ZEROARR")
    (hn : ∀ n ∈ instrNames (.Lopn [.reg d] opn [a]), KeptS n) :
    SimS (.Lopn [.reg d] opn [a], τ)
      [(.Lopn [.reg reloadScratch] opn [a], τ), (.Lopn [.reg d] m [.reg reloadScratch], τ2)] := by
  intro s s' t zf z hA h
  obtain ⟨t1, ht1, hA1⟩ := fstepF_agreeS ⟨_, _, _, rfl⟩ hn
    (mulxFree_of_lopn1 ⟨_, _, _, rfl⟩) hA h
  have h1 : fstepF (.Lopn [.reg reloadScratch] opn [a], τ) s' zf
      = some (TwoAddrFuelMemF.movDst s' d reloadScratch t1, z) := by
    rw [fstepF_dst1 opn a τ d reloadScratch hz, ht1]; rfl
  have e2 := fstepF_movWire d reloadScratch m τ2 hm
    (TwoAddrFuelMemF.movDst s' d reloadScratch t1) z
  have hdst : ∀ r, r ≠ d → t1.reg.lvm r = s'.reg.lvm r := fun r hr =>
    (JasminLsemStepFrame.fstepF_frame_dst ht1 (by simp [JasminLsemStepFrame.dstNames,
      opNames, hr])).1
  refine ⟨((TwoAddrFuelMemF.movDst s' d reloadScratch t1).setReg d
      ((TwoAddrFuelMemF.movDst s' d reloadScratch t1).reg.lvm reloadScratch).2).nextPc,
    ?_, AgreeS.trans hA1 ?_⟩
  · rw [runStraightF_cons, h1, Option.bind_some, runStraightF_cons]
    unfold movWire at e2
    rw [e2]
    rfl
  · refine ⟨fun r hr => ?_, fun r _ => ?_, ?_, ?_, ?_⟩
    · by_cases hrd : r = d
      · subst hrd
        simp [TwoAddrFuelMemF.movDst, LstateM.setReg, LstateM.nextPc]
      · have hrR : r ≠ reloadScratch := hr.1
        simp [TwoAddrFuelMemF.movDst, LstateM.setReg, LstateM.nextPc, hrd, hrR, hdst r hrd]
    · simp [TwoAddrFuelMemF.movDst, LstateM.setReg, LstateM.nextPc]
    · simp [TwoAddrFuelMemF.movDst, LstateM.setReg, LstateM.nextPc]
    · simp [TwoAddrFuelMemF.movDst, LstateM.setReg, LstateM.nextPc]
    · simp [TwoAddrFuelMemF.movDst, LstateM.setReg, LstateM.nextPc]

/-- An operand that `legalizeSibElem` keeps: no SIB element with a spilled base or index. -/
def sibPlainB : LOperand → Bool
  | .arrIdx b i _ => !sibNameSpill b && !sibNameSpill i
  | _ => true

/-- `legalizeSibElem` keeps an operand that `sibPlainB` admits, with no prelude. -/
theorem legalizeSibElem_of_plain {o : LOperand} (h : sibPlainB o = true) :
    legalizeSibElem o = ([], o) := by
  unfold legalizeSibElem
  split <;> simp_all [sibPlainB]

/-- A load mnemonic is no array zeroing. -/
theorem ne_zeroArr_of_isMemLoad {opn : String} (hl : isMemLoad opn = true) :
    opn ≠ "ZEROARR" := by
  rintro rfl
  revert hl
  decide +kernel

/-- **The legalised load.** On a source that `sibPlainB` admits, `legalizeMemLoad` simulates
    the load `opn d, s` off the scratches, when the load names no scratch and the loads
    `opn D, s` carry one tag at every register destination `D`. -/
theorem simS_legalizeMemLoad {tg : LinstrR → MemTag} {d a : LOperand} {opn mov : String}
    (hl : isMemLoad opn = true) (hsib : sibPlainB a = true) (hmov : stripWidthTag mov = "MOV")
    (htl : ∀ D D', tg (.Lopn [.reg D] opn [a]) = tg (.Lopn [.reg D'] opn [a]))
    (hn : ∀ n ∈ instrNames (.Lopn [d] opn [a]), KeptS n) :
    SimS (.Lopn [d] opn [a], tg (.Lopn [d] opn [a]))
      ((legalizeMemLoad d a opn mov).map fun y => (y, tg y)) := by
  unfold legalizeMemLoad
  simp only [legalizeSibElem_of_plain hsib, List.nil_append]
  cases hd : d.isSpill
  · simp only [Bool.false_eq_true, ite_false, List.map_cons, List.map_nil]
    exact simS_self ⟨_, _, _, rfl⟩ hn (mulxFree_of_lopn1 ⟨_, _, _, rfl⟩)
  · cases d with
    | reg dn =>
        simp only [ite_true, List.map_cons, List.map_nil]
        rw [htl reloadScratch dn]
        refine simS_loadScratch ?_ (ne_zeroArr_of_isMemLoad hl) hn
        cases a with
        | arrIdx _ _ sc =>
            dsimp only
            split_ifs
            · exact stripWidthTag_mov64
            · exact hmov
        | _ => exact hmov
    | _ => simp [LOperand.isSpill] at hd

/-! ## 7. The lowering core -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.LowerCore (lowerCore)

/-- An operand that `materializeWideImm` keeps: no immediate of `2 ^ 31` or more. -/
def immSmallB : LOperand → Bool
  | .imm v => decide (v < 2 ^ 31)
  | _ => true

/-- The cases of `lowerCore imm u64 w` that the per-family simulations of this module
    cover: a two-address binop `OP d, s0, s1` over register names, by the count `v` when `imm`
    is `some v` and `s1` is the immediate `v`, otherwise when `s1` is neither `d` nor a wide
    immediate and is a spill slot only under a register destination `d`; a non-store `Lopn`
    with one register destination and two sources that `setccSpill?` leaves unchanged; a
    select `CMOV:64` over register names; an `Lopn` with one destination and three or more
    sources that `cmovSpillDst?` leaves unchanged; a load whose source has no spilled SIB base
    or index (`sibPlainB`); a one-source instruction that is no native shift or rotate and no
    load, whose move selection keeps the mnemonic and whose copy mnemonic strips to `MOV` or is
    a `copyQ` mnemonic. `false` on stores, loads through a spilled SIB base or index, native
    shifts and rotates, binops with a wide second source, with a spilled second source under a
    spilled destination or with a count read from a register, materialised comparisons with
    spilled operands, instructions with several destinations, and every instruction other
    than `Lopn`. -/
def lowerCoreOKB (imm : Option Nat) (u64 : Bool) : LinstrR → Bool
  | .Lopn [.reg d] opn [.reg s0, s1] =>
      if isTwoAddrBinop opn then
        match imm with
        | some v => s1 == .imm v
        | none =>
            s1 != .reg d && immSmallB s1 && (!s1.isSpill || !(LOperand.reg d).isSpill)
      else !isMemStore opn && (setccSpill? [.reg d] opn [.reg s0, s1]).isNone
        && (andnSpill? [.reg d] opn [.reg s0, s1]).isNone
  | .Lopn [.reg _] opn [.reg _, .reg _, .reg _] =>
      !isTwoAddrBinop opn && opn == "CMOV:64"
  | .Lopn [d] opn (s0 :: s1 :: s2 :: ss) =>
      !isTwoAddrBinop opn && (cmovSpillDst? [d] opn (s0 :: s1 :: s2 :: ss)).isNone
  | .Lopn [d] opn [s] =>
      !isNativeShiftRotate opn &&
        if isMemLoad opn then sibPlainB s
        else spillImmMovMnem u64 opn d s == opn &&
          (!(stripWidthTag opn == "MOV" || stripWidthTag opn == "MOVQ") ||
            stripWidthTag opn == "MOV" || copyQ opn)
  | _ => false

/-- **The lowering core off the scratches.** On an instruction `w` that names no scratch and
    on which `lowerCoreOKB imm u64` holds, `lowerCore imm u64 w` simulates `w` off the
    scratches, when the tag function gives each two-address binop with a fixed second source
    one register tag, every `CMOV:64` a register tag, and each load with a fixed source one
    tag at every register destination. -/
theorem simS_lowerCore {tg : LinstrR → MemTag} {imm : Option Nat} {u64 : Bool} {w : LinstrR}
    (hok : lowerCoreOKB imm u64 w = true)
    (htg : ∀ opn s1, isTwoAddrBinop opn = true →
      ∃ cd, ∀ D X, tg (.Lopn [.reg D] opn [.reg X, s1]) = .reg cd)
    (hcm : RegTagOn tg "CMOV:64")
    (htl : ∀ opn s, isMemLoad opn = true →
      ∀ D D', tg (.Lopn [.reg D] opn [s]) = tg (.Lopn [.reg D'] opn [s]))
    (hn : ∀ n ∈ instrNames w, KeptS n) :
    SimS (w, tg w) ((lowerCore imm u64 w).map fun y => (y, tg y)) := by
  unfold lowerCoreOKB at hok
  split at hok
  · rename_i d opn s0 s1
    by_cases hb : isTwoAddrBinop opn = true
    · obtain ⟨cd, hcd⟩ := htg opn s1 hb
      simp only [hb, ↓reduceIte] at hok
      cases imm with
      | some v =>
        have hs : s1 = .imm v := by simpa using hok
        subst hs
        simp only [lowerCore, hb, ite_true]
        exact simS_lowerTwoAddrShiftImm hcd (stripWidthTag_setccMov opn)
          (ne_cmp_of_isTwoAddrBinop hb) hn
      | none =>
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true,
          Bool.not_eq_true'] at hok
        obtain ⟨⟨hd, hw⟩, hsp⟩ := hok
        have himm : materializeWideImm s1 (if hasSuffix opn ":64" then "MOV:64" else "MOV")
            = ([], s1) := by
          unfold materializeWideImm
          split <;> simp_all [immSmallB]
        simp only [lowerCore, hb, ite_true]
        cases hs : s1.isSpill
        · exact simS_lowerTwoAddr hcd hb (stripWidthTag_setccMov opn) hd hs himm hn
        · have hds : (LOperand.reg d).isSpill = false := by simpa [hs] using hsp
          cases s1 with
          | reg S =>
              obtain ⟨cd', hcd'⟩ := htg opn (.reg reloadScratch) hb
              exact simS_lowerTwoAddrSpill hcd hcd' hb (stripWidthTag_setccMov opn) hds hs hn
          | _ => simp [LOperand.isSpill] at hs
    · simp only [Bool.not_eq_true] at hb
      simp only [hb, Bool.false_eq_true, ite_false, Bool.and_eq_true, Bool.not_eq_true',
        Option.isNone_iff_eq_none] at hok
      obtain ⟨⟨hst, hset⟩, hand⟩ := hok
      have hl : lowerCore imm u64 (.Lopn [.reg d] opn [.reg s0, s1])
          = [.Lopn [.reg d] opn [.reg s0, s1]] := by
        simp only [lowerCore, hb, hst, Bool.false_eq_true, ite_false]
        exact legalizeSpillDst_of_none rfl hset hand
      rw [hl]
      exact simS_self ⟨_, _, _, rfl⟩ hn (mulxFree_of_lopn1 ⟨_, _, _, rfl⟩)
  · rename_i D opn C T F
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hok
    obtain ⟨hb, rfl⟩ := hok
    have hC : KeptS C := hn C (by simp [instrNames, opNames])
    have hT : KeptS T := hn T (by simp [instrNames, opNames])
    have hF : KeptS F := hn F (by simp [instrNames, opNames])
    simp only [lowerCore, hb, Bool.false_eq_true, ite_false]
    unfold legalizeSpillDst
    cases h : cmovSpillDst? [.reg D] "CMOV:64" [.reg C, .reg T, .reg F] with
    | some L => exact simS_cmovSpillDst? hcm h hC hT hF
    | none =>
      simpa [setccSpill?, andnSpill?] using
        simS_self (i := (.Lopn [.reg D] "CMOV:64" [.reg C, .reg T, .reg F],
          tg (.Lopn [.reg D] "CMOV:64" [.reg C, .reg T, .reg F]))) ⟨_, _, _, rfl⟩ hn
          (mulxFree_of_lopn1 ⟨_, _, _, rfl⟩)
  · rename_i d opn s0 s1 s2 ss _
    simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hok
    obtain ⟨hb, hc⟩ := hok
    have hl : lowerCore imm u64 (.Lopn [d] opn (s0 :: s1 :: s2 :: ss))
        = [.Lopn [d] opn (s0 :: s1 :: s2 :: ss)] := by
      simp only [lowerCore, hb, Bool.false_eq_true, ite_false]
      exact legalizeSpillDst_of_none hc (by cases s0 <;> cases s1 <;> rfl)
        (by cases s0 <;> cases s1 <;> rfl)
    rw [hl]
    exact simS_self ⟨_, _, _, rfl⟩ hn (mulxFree_of_lopn1 ⟨_, _, _, rfl⟩)
  · rename_i d opn s
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
    obtain ⟨hns, hok⟩ := hok
    by_cases hld : isMemLoad opn = true
    · simp only [hld, ite_true] at hok
      simp only [lowerCore, hns, hld, Bool.false_eq_true, ite_false, ite_true]
      exact simS_legalizeMemLoad hld hok (stripWidthTag_setccMov opn) (htl opn s hld) hn
    · simp only [Bool.not_eq_true] at hld
      simp only [hld, Bool.false_eq_true, ite_false, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨hmn, hcp⟩ := hok
      simp only [lowerCore, hns, hld, Bool.false_eq_true, ite_false]
      refine simS_legalizeOneSrc hmn (fun h => ?_) hn
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcp h ⊢
      grind
  · simp at hok

end CatCrypt.Crypto.SecureCompilation.X86Backend.LowerFuelMemF
