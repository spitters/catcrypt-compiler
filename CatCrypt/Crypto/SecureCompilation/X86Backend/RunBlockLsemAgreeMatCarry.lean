/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookRunBlock

/-!
# `runBlock` ↔ `lsemStraightMem` agreement for the immediate-carry gadget

`RunBlockLsemAgree.lean` §9 carries the flag/carry axis over the
**register-source** `adcx` / `adox` under the designated-slot correspondence
`JLstateCorrF`. This module covers the **immediate-source** forms
`.adcx dst (.imm n)` / `.adox dst (.imm n)`, of which the carry-materialise
gadget `SchoolbookRunBlock.materialiseCarry` is the instance that motivates
them: `[.adcx hi (.imm 0), .adox hi (.imm 0)]`, which folds the `CF` chain bit
then the `OF` chain bit into `hi` and leaves both flags cleared.

## Why a zero register rather than an immediate-carry recognizer

The structured lsem `ADCX` / `ADCXHI` recognizers (`adcxStruct?` /
`adcxhiStruct?`, `VIR/JasminLsemMulCarry.lean`) match three **register**
sources, so an immediate second operand has no structured wire. Two ways to
supply one:

* materialise the immediate in a fresh register and reuse the existing
  three-register wire, or
* widen `adcxStruct?` to accept an `LOperand` source.

This module takes the first. The second changes the recognizer's result type
(`String × String × String × String` would have to carry an operand), which
would rewrite the `ADCX` arm of `lsemStepMC` and every `adcxStruct? … = none`
fact the other bridge modules discharge by shape —
`RunBlockLsemAgree.lean:216`, `:505`, `RunBlockLsemAgreeNeg.lean:86`,
`RunBlockLsemAgreeCmov.lean:87`. The zero-register route adds one wire and
touches no shared declaration, and a 1→2 lowering is already the idiom (the
register-source `.adcx` lowers to `ADCXHI` then `ADCX`, §9).

The materialising register `z` is required to lie in the synthetic flag
namespace `flg`, the same device that keeps the designated `CF` / `OF` slots
apart from the real block registers: `JLstateCorrF.regAgree` is asserted only
off `flg`, so a write to `z` is invisible to the correspondence.

## The lowering

`.adcx dst (.imm n)` with materialising register `z` and fresh `CF` slot `fr`,
at current slots `(cfN, ofN)`, becomes three wires:

* `MOV z, n` — the literal at width 64;
* `ADCXHI fr ← dst, z, cfN` — the carry-out to the fresh slot;
* `ADCX dst ← dst, z, cfN` — the data to `dst`.

`.adox` is the same on the `OF` slot. Both migrate the designated namespace
(`(cfN, ofN)` to `(fr, ofN)`, resp. `(cfN, fr)`), so a block of them threads a
*chain* of slot names rather than a fixed pair: `matCarryWires` lowers a block
paired with its per-instruction fresh names, and `matCarrySlots` computes the
namespace the block ends in.

## Main results

* `InImmCarrySubset`: the covered opcode set — `.adcx` / `.adox` at an
  immediate source.
* `MatCarrySlotsOk`, `MatCarryStep`, `MatCarryFresh`: the name-disjointness side
  condition, per opcode and folded along a block.
* `matCarryWire` / `matCarryNext`: the three-wire lowering and the slot it
  migrates to; `matCarryWires` / `matCarrySlots`: their block folds.
* `adcxImm_case`, `adoxImm_case`: per-opcode totality and `JLstateCorrF`
  migration.
* `runBlock_lsem_agreeMat`: the block-induction lift over a straight-line block
  of immediate-carry opcodes.
* `runBlock_lsem_agreeMat_loop`: the counted-loop lift, for a block whose fresh
  names return the namespace to where it started.
* `materialiseCarry_lsem_agree`: the gadget itself, as a two-instruction block.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMatCarry

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.X86Backend.SchoolbookRunBlock
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. The covered subset and its side condition -/

/-- The immediate-carry subset: the two-address `adcx` / `adox` at an immediate
    source. The register-source forms are `RunBlockLsemAgree` §9's; every other
    opcode is out of scope here. -/
def InImmCarrySubset : JInstr 64 → Prop
  | .adcx _ (.imm _) => True
  | .adox _ (.imm _) => True
  | _                => False

/-- The name-disjointness side condition of one immediate-carry lowering:
    the accumulator `dst` is a real block register (off the flag namespace
    `flg`), the materialising register `z` and the fresh slot `fr` are synthetic
    flag names, and `z` / `fr` avoid each other and both designated slots. The
    conditions `z ≠ dst` and `fr ≠ dst` follow from the namespace membership. -/
def MatCarrySlotsOk (flg : String → Prop) (z fr dst cfN ofN : String) : Prop :=
  ¬ flg dst ∧ flg z ∧ flg fr ∧ z ≠ cfN ∧ z ≠ ofN ∧ z ≠ fr ∧ fr ≠ cfN ∧ fr ≠ ofN

/-- The side condition of one opcode at the designated slots it runs from;
    vacuous off the subset. -/
def MatCarryStep (flg : String → Prop) (z fr : String) :
    JInstr 64 → String × String → Prop
  | .adcx dst (.imm _), (cfN, ofN) => MatCarrySlotsOk flg z fr dst cfN ofN
  | .adox dst (.imm _), (cfN, ofN) => MatCarrySlotsOk flg z fr dst cfN ofN
  | _, _                           => True

/-! ## 2. The lowering -/

/-- The three-wire lowering of one immediate-carry opcode, given the
    materialising register `z`, the fresh slot `fr`, and the designated slots
    the opcode runs from: move the literal into `z`, write the carry-out to
    `fr`, write the data to `dst`. `.adcx` reads the `CF` slot, `.adox` the `OF`
    slot. Out-of-subset opcodes lower to the empty block (never claimed to
    agree). -/
def matCarryWire (z fr : String) : JInstr 64 → String × String → List LinstrRM
  | .adcx dst (.imm n), (cfN, _) =>
      [ (movImmLinstr 64 z n, MemTag.reg none),
        (LinstrR.Lopn [LOperand.reg fr] (withWidthTag 64 "ADCXHI")
          [LOperand.reg dst, LOperand.reg z, LOperand.reg cfN], MemTag.reg none),
        (LinstrR.Lopn [LOperand.reg dst] (withWidthTag 64 "ADCX")
          [LOperand.reg dst, LOperand.reg z, LOperand.reg cfN], MemTag.reg none) ]
  | .adox dst (.imm n), (_, ofN) =>
      [ (movImmLinstr 64 z n, MemTag.reg none),
        (LinstrR.Lopn [LOperand.reg fr] (withWidthTag 64 "ADCXHI")
          [LOperand.reg dst, LOperand.reg z, LOperand.reg ofN], MemTag.reg none),
        (LinstrR.Lopn [LOperand.reg dst] (withWidthTag 64 "ADCX")
          [LOperand.reg dst, LOperand.reg z, LOperand.reg ofN], MemTag.reg none) ]
  | _, _ => []

/-- The three wires of an immediate-source `.adcx`. -/
theorem matCarryWire_adcx (z fr dst cfN ofN : String) (n : Nat) :
    matCarryWire z fr (.adcx dst (.imm n)) (cfN, ofN) =
      [ (movImmLinstr 64 z n, MemTag.reg none),
        (LinstrR.Lopn [LOperand.reg fr] (withWidthTag 64 "ADCXHI")
          [LOperand.reg dst, LOperand.reg z, LOperand.reg cfN], MemTag.reg none),
        (LinstrR.Lopn [LOperand.reg dst] (withWidthTag 64 "ADCX")
          [LOperand.reg dst, LOperand.reg z, LOperand.reg cfN], MemTag.reg none) ] := rfl

/-- The three wires of an immediate-source `.adox`. -/
theorem matCarryWire_adox (z fr dst cfN ofN : String) (n : Nat) :
    matCarryWire z fr (.adox dst (.imm n)) (cfN, ofN) =
      [ (movImmLinstr 64 z n, MemTag.reg none),
        (LinstrR.Lopn [LOperand.reg fr] (withWidthTag 64 "ADCXHI")
          [LOperand.reg dst, LOperand.reg z, LOperand.reg ofN], MemTag.reg none),
        (LinstrR.Lopn [LOperand.reg dst] (withWidthTag 64 "ADCX")
          [LOperand.reg dst, LOperand.reg z, LOperand.reg ofN], MemTag.reg none) ] := rfl

/-- The designated slots after one immediate-carry opcode: `.adcx` replaces the
    `CF` slot by the fresh name, `.adox` the `OF` slot. -/
def matCarryNext (fr : String) : JInstr 64 → String × String → String × String
  | .adcx _ (.imm _), (_, ofN) => (fr, ofN)
  | .adox _ (.imm _), (cfN, _) => (cfN, fr)
  | _, ns                      => ns

/-- The lowering of a straight-line block, each opcode paired with the fresh
    slot it allocates, threading the designated namespace along the block. -/
def matCarryWires (z : String) :
    List (JInstr 64 × String) → String × String → List LinstrRM
  | [], _ => []
  | (i, fr) :: rest, ns =>
      matCarryWire z fr i ns ++ matCarryWires z rest (matCarryNext fr i ns)

/-- The designated namespace a block ends in. -/
def matCarrySlots : List (JInstr 64 × String) → String × String → String × String
  | [], ns => ns
  | (i, fr) :: rest, ns => matCarrySlots rest (matCarryNext fr i ns)

/-- The block lowering peels one opcode. -/
theorem matCarryWires_cons (z : String) (i : JInstr 64) (fr : String)
    (rest : List (JInstr 64 × String)) (ns : String × String) :
    matCarryWires z ((i, fr) :: rest) ns =
      matCarryWire z fr i ns ++ matCarryWires z rest (matCarryNext fr i ns) := rfl

/-- The end-of-block namespace peels one opcode. -/
theorem matCarrySlots_cons (i : JInstr 64) (fr : String)
    (rest : List (JInstr 64 × String)) (ns : String × String) :
    matCarrySlots ((i, fr) :: rest) ns = matCarrySlots rest (matCarryNext fr i ns) := rfl

/-- The side condition along a block: each opcode's name-disjointness holds at
    the designated slots it runs from. It constrains names only, so it is
    independent of the machine state. -/
def MatCarryFresh (flg : String → Prop) (z : String) :
    List (JInstr 64 × String) → String × String → Prop
  | [], _ => True
  | (i, fr) :: rest, ns =>
      MatCarryStep flg z fr i ns ∧ MatCarryFresh flg z rest (matCarryNext fr i ns)

/-! ## 3. Per-opcode agreement -/

/-- **Per-opcode agreement for `.adcx dst (.imm n)`.** The three-wire lowering
    does not fail, and its result satisfies `JLstateCorrF` with the `CF` slot
    migrated to `fr`: `dst` receives the carry-add word, `fr` the carry-out bit,
    and the `OF` slot is untouched. -/
theorem adcxImm_case (s : JState 64) (ls : LstateM) (flg : String → Prop) (cfN ofN : String)
    (hcorr : JLstateCorrF s ls flg cfN ofN) (dst z fr : String) (n : Nat)
    (hok : MatCarrySlotsOk flg z fr dst cfN ofN) :
    ∃ ls', lsemStraightMem (matCarryWire z fr (.adcx dst (.imm n)) (cfN, ofN)) ls = some ls' ∧
      JLstateCorrF (runBlock s [.adcx dst (.imm n)]) ls' flg fr ofN := by
  obtain ⟨hdst, hz, hfr, hzcf, hzof, hzfr, hfrcf, hfrof⟩ := hok
  have hdst_z : dst ≠ z := fun h => hdst (h ▸ hz)
  have hdst_fr : dst ≠ fr := fun h => hdst (h ▸ hfr)
  have hdst_of : dst ≠ ofN := fun h => hdst (h ▸ hcorr.ofFlg)
  -- Step 0: materialise the literal in the synthetic register `z`.
  set ls0 : LstateM :=
    { ls with reg := (ls.reg.setReg z (BitVec.ofNat 64 n)).nextPc } with hls0
  have hstep0 : lsemStepMem (movImmLinstr 64 z n, MemTag.reg none) ls = some ls0 :=
    lsemStepMem_movImm z n ls
  have hva0 : ls0.reg.getW dst 64 = some (s.regs dst) := by
    rw [hls0]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ hdst_z]; exact hcorr.regAgree dst hdst
  have hvz0 : ls0.reg.getW z 64 = some (BitVec.ofNat 64 n) := by
    rw [hls0]; simp only [LstateN.getW_nextPc, LstateN.getW_setReg_same]
  have hvc0 : ls0.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := by
    rw [hls0]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hzcf)]; exact hcorr.cfAgree
  -- Step 1: the carry-out to the fresh slot `fr`.
  set ls1 : LstateM :=
    { ls0 with reg := (ls0.reg.setReg fr
        (carryOutBit (s.regs dst) (BitVec.ofNat 64 n) (flagBit (s.flagB (·.cf))))).nextPc }
    with hls1
  have hstep1 : lsemStepMem
      (.Lopn [.reg fr] (withWidthTag 64 "ADCXHI")
        [.reg dst, .reg z, .reg cfN], MemTag.reg none) ls0 = some ls1 :=
    lsemStepMem_adcxhi3 fr dst z cfN ls0 _ _ _ hva0 hvz0 hvc0
  have hva1 : ls1.reg.getW dst 64 = some (s.regs dst) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ hdst_fr]; exact hva0
  have hvz1 : ls1.reg.getW z 64 = some (BitVec.ofNat 64 n) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ hzfr]; exact hvz0
  have hvc1 : ls1.reg.getW cfN 1 = some (flagBit (s.flagB (·.cf))) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hfrcf)]; exact hvc0
  -- Step 2: the data to `dst`.
  set ls2 : LstateM :=
    { ls1 with reg := (ls1.reg.setReg dst
        (addCarryWord (s.regs dst) (BitVec.ofNat 64 n) (flagBit (s.flagB (·.cf))))).nextPc }
    with hls2
  have hstep2 : lsemStepMem
      (.Lopn [.reg dst] (withWidthTag 64 "ADCX")
        [.reg dst, .reg z, .reg cfN], MemTag.reg none) ls1 = some ls2 :=
    lsemStepMem_adcx3 dst dst z cfN ls1 _ _ _ hva1 hvz1 hvc1
  refine ⟨ls2, ?_, ?_⟩
  · rw [matCarryWire_adcx]
    simp only [lsemStraightMem_cons, hstep0, hstep1, hstep2, lsemStraightMem_nil]
  · set co : Bool :=
      (waddcarry (s.regs dst) (BitVec.ofNat 64 n) (s.flagB (·.cf))).1 with hco
    set res : BitVec 64 :=
      (waddcarry (s.regs dst) (BitVec.ofNat 64 n) (s.flagB (·.cf))).2 with hres
    have hrun : runBlock s [.adcx dst (.imm n)] =
        { regs := fun r' => if r' = dst then res else s.regs r'
          flags := { s.flags with cf := some co }, mem := s.mem } := by
      simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, JOperand.eval, JState.get,
        hco, hres]
    rw [hrun]
    have hdata : addCarryWord (s.regs dst) (BitVec.ofNat 64 n) (flagBit (s.flagB (·.cf)))
        = res := by rw [hres]; exact adcx_data_eq _ _ _
    have hcarry : carryOutBit (s.regs dst) (BitVec.ofNat 64 n) (flagBit (s.flagB (·.cf)))
        = flagBit co := by rw [hco]; exact adcx_carry_eq _ _ _
    refine ⟨?_, ?_, ?_, ?_, hfr, hcorr.ofFlg, hfrof⟩
    · intro r hr
      have hr_fr : r ≠ fr := by rintro rfl; exact hr hfr
      have hr_z : r ≠ z := by rintro rfl; exact hr hz
      by_cases hrd : r = dst
      · subst hrd
        simp only [hls2, hls1, hls0, LstateN.getW_nextPc, LstateN.getW_setReg_same]
        rw [hdata]; simp
      · simp only [hls2, hls1, hls0, LstateN.getW_nextPc,
          LstateN.getW_setReg_other _ _ _ _ _ hrd,
          LstateN.getW_setReg_other _ _ _ _ _ hr_fr,
          LstateN.getW_setReg_other _ _ _ _ _ hr_z]
        rw [hcorr.regAgree r hr]; simp [hrd]
    · intro base off; exact hcorr.memAgree base off
    · simp only [hls2, hls1, hls0, LstateN.getW_nextPc,
        LstateN.getW_setReg_other _ _ _ _ _ hdst_fr.symm, LstateN.getW_setReg_same]
      rw [hcarry]; simp only [JState.flagB, Option.getD_some]
    · simp only [hls2, hls1, hls0, LstateN.getW_nextPc,
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hdst_of),
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hfrof),
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hzof)]
      exact hcorr.ofAgree

/-- **Per-opcode agreement for `.adox dst (.imm n)`.** Identical to
    `adcxImm_case` on the `OF` slot: `.adox` reads and writes `OF`, and its lsem
    image is the same structured `ADCX` / `ADCXHI` carry realizer threading the
    `OF` slot. -/
theorem adoxImm_case (s : JState 64) (ls : LstateM) (flg : String → Prop) (cfN ofN : String)
    (hcorr : JLstateCorrF s ls flg cfN ofN) (dst z fr : String) (n : Nat)
    (hok : MatCarrySlotsOk flg z fr dst cfN ofN) :
    ∃ ls', lsemStraightMem (matCarryWire z fr (.adox dst (.imm n)) (cfN, ofN)) ls = some ls' ∧
      JLstateCorrF (runBlock s [.adox dst (.imm n)]) ls' flg cfN fr := by
  obtain ⟨hdst, hz, hfr, hzcf, hzof, hzfr, hfrcf, hfrof⟩ := hok
  have hdst_z : dst ≠ z := fun h => hdst (h ▸ hz)
  have hdst_fr : dst ≠ fr := fun h => hdst (h ▸ hfr)
  have hdst_cf : dst ≠ cfN := fun h => hdst (h ▸ hcorr.cfFlg)
  set ls0 : LstateM :=
    { ls with reg := (ls.reg.setReg z (BitVec.ofNat 64 n)).nextPc } with hls0
  have hstep0 : lsemStepMem (movImmLinstr 64 z n, MemTag.reg none) ls = some ls0 :=
    lsemStepMem_movImm z n ls
  have hva0 : ls0.reg.getW dst 64 = some (s.regs dst) := by
    rw [hls0]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ hdst_z]; exact hcorr.regAgree dst hdst
  have hvz0 : ls0.reg.getW z 64 = some (BitVec.ofNat 64 n) := by
    rw [hls0]; simp only [LstateN.getW_nextPc, LstateN.getW_setReg_same]
  have hvo0 : ls0.reg.getW ofN 1 = some (flagBit (s.flagB (·.of))) := by
    rw [hls0]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hzof)]; exact hcorr.ofAgree
  set ls1 : LstateM :=
    { ls0 with reg := (ls0.reg.setReg fr
        (carryOutBit (s.regs dst) (BitVec.ofNat 64 n) (flagBit (s.flagB (·.of))))).nextPc }
    with hls1
  have hstep1 : lsemStepMem
      (.Lopn [.reg fr] (withWidthTag 64 "ADCXHI")
        [.reg dst, .reg z, .reg ofN], MemTag.reg none) ls0 = some ls1 :=
    lsemStepMem_adcxhi3 fr dst z ofN ls0 _ _ _ hva0 hvz0 hvo0
  have hva1 : ls1.reg.getW dst 64 = some (s.regs dst) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ hdst_fr]; exact hva0
  have hvz1 : ls1.reg.getW z 64 = some (BitVec.ofNat 64 n) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ hzfr]; exact hvz0
  have hvo1 : ls1.reg.getW ofN 1 = some (flagBit (s.flagB (·.of))) := by
    rw [hls1]; simp only [LstateN.getW_nextPc]
    rw [LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hfrof)]; exact hvo0
  set ls2 : LstateM :=
    { ls1 with reg := (ls1.reg.setReg dst
        (addCarryWord (s.regs dst) (BitVec.ofNat 64 n) (flagBit (s.flagB (·.of))))).nextPc }
    with hls2
  have hstep2 : lsemStepMem
      (.Lopn [.reg dst] (withWidthTag 64 "ADCX")
        [.reg dst, .reg z, .reg ofN], MemTag.reg none) ls1 = some ls2 :=
    lsemStepMem_adcx3 dst dst z ofN ls1 _ _ _ hva1 hvz1 hvo1
  refine ⟨ls2, ?_, ?_⟩
  · rw [matCarryWire_adox]
    simp only [lsemStraightMem_cons, hstep0, hstep1, hstep2, lsemStraightMem_nil]
  · set co : Bool :=
      (waddcarry (s.regs dst) (BitVec.ofNat 64 n) (s.flagB (·.of))).1 with hco
    set res : BitVec 64 :=
      (waddcarry (s.regs dst) (BitVec.ofNat 64 n) (s.flagB (·.of))).2 with hres
    have hrun : runBlock s [.adox dst (.imm n)] =
        { regs := fun r' => if r' = dst then res else s.regs r'
          flags := { s.flags with of := some co }, mem := s.mem } := by
      simp only [runBlock_cons, runBlock_nil, evalInstr, x86_ADCX, JOperand.eval, JState.get,
        hco, hres]
    rw [hrun]
    have hdata : addCarryWord (s.regs dst) (BitVec.ofNat 64 n) (flagBit (s.flagB (·.of)))
        = res := by rw [hres]; exact adcx_data_eq _ _ _
    have hcarry : carryOutBit (s.regs dst) (BitVec.ofNat 64 n) (flagBit (s.flagB (·.of)))
        = flagBit co := by rw [hco]; exact adcx_carry_eq _ _ _
    refine ⟨?_, ?_, ?_, ?_, hcorr.cfFlg, hfr, Ne.symm hfrcf⟩
    · intro r hr
      have hr_fr : r ≠ fr := by rintro rfl; exact hr hfr
      have hr_z : r ≠ z := by rintro rfl; exact hr hz
      by_cases hrd : r = dst
      · subst hrd
        simp only [hls2, hls1, hls0, LstateN.getW_nextPc, LstateN.getW_setReg_same]
        rw [hdata]; simp
      · simp only [hls2, hls1, hls0, LstateN.getW_nextPc,
          LstateN.getW_setReg_other _ _ _ _ _ hrd,
          LstateN.getW_setReg_other _ _ _ _ _ hr_fr,
          LstateN.getW_setReg_other _ _ _ _ _ hr_z]
        rw [hcorr.regAgree r hr]; simp [hrd]
    · intro base off; exact hcorr.memAgree base off
    · simp only [hls2, hls1, hls0, LstateN.getW_nextPc,
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hdst_cf),
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hfrcf),
        LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hzcf)]
      exact hcorr.cfAgree
    · simp only [hls2, hls1, hls0, LstateN.getW_nextPc,
        LstateN.getW_setReg_other _ _ _ _ _ hdst_fr.symm, LstateN.getW_setReg_same]
      rw [hcarry]; simp only [JState.flagB, Option.getD_some]

/-- **Per-instruction agreement on the immediate-carry subset.** Every opcode of
    `InImmCarrySubset` whose names satisfy `MatCarryStep` lowers through
    `matCarryWire` to a wire block that does not fail, and whose result satisfies
    `JLstateCorrF` at the migrated slots `matCarryNext`. -/
theorem matCarryWire_agrees (i : JInstr 64) (hi : InImmCarrySubset i)
    (flg : String → Prop) (z fr : String) (ns : String × String)
    (hok : MatCarryStep flg z fr i ns)
    (s : JState 64) (ls : LstateM) (hcorr : JLstateCorrF s ls flg ns.1 ns.2) :
    ∃ ls', lsemStraightMem (matCarryWire z fr i ns) ls = some ls' ∧
      JLstateCorrF (runBlock s [i]) ls' flg (matCarryNext fr i ns).1 (matCarryNext fr i ns).2 := by
  obtain ⟨cfN, ofN⟩ := ns
  cases i
  case adcx dst src =>
    cases src
    case imm n => exact adcxImm_case s ls flg cfN ofN hcorr dst z fr n hok
    case reg r => exact hi.elim
  case adox dst src =>
    cases src
    case imm n => exact adoxImm_case s ls flg cfN ofN hcorr dst z fr n hok
    case reg r => exact hi.elim
  all_goals exact hi.elim

/-! ## 4. Block-level lift -/

/-- **Block-level agreement on the immediate-carry subset.** A straight-line
    block of immediate-carry opcodes, each paired with the fresh slot it
    allocates and satisfying the name-disjointness fold `MatCarryFresh`, runs to
    completion under `lsemStraightMem` on `matCarryWires`, and its result
    corresponds — on the register, memory, and both carry axes — to the
    `runBlock` result, in the migrated namespace `matCarrySlots`. Straight-line
    induction on the block. -/
theorem runBlock_lsem_agreeMat (bs : List (JInstr 64 × String))
    (flg : String → Prop) (z : String) (ns : String × String)
    (hb : ∀ p ∈ bs, InImmCarrySubset p.1) (hok : MatCarryFresh flg z bs ns)
    (s : JState 64) (ls : LstateM) (h : JLstateCorrF s ls flg ns.1 ns.2) :
    ∃ ls', lsemStraightMem (matCarryWires z bs ns) ls = some ls' ∧
      JLstateCorrF (runBlock s (bs.map Prod.fst)) ls'
        flg (matCarrySlots bs ns).1 (matCarrySlots bs ns).2 := by
  induction bs generalizing s ls ns with
  | nil => exact ⟨ls, rfl, h⟩
  | cons p rest ih =>
    obtain ⟨i, fr⟩ := p
    obtain ⟨hoki, hokr⟩ := hok
    obtain ⟨ls1, hstep1, hcorr1⟩ :=
      matCarryWire_agrees i (hb _ (List.mem_cons_self ..)) flg z fr ns hoki s ls h
    obtain ⟨ls', hstep', hcorr'⟩ :=
      ih (matCarryNext fr i ns) (fun q hq => hb q (List.mem_cons_of_mem _ hq)) hokr
        (runBlock s [i]) ls1 hcorr1
    refine ⟨ls', ?_, ?_⟩
    · rw [matCarryWires_cons, lsemStraightMem_append, hstep1, Option.bind]
      exact hstep'
    · rw [matCarrySlots_cons]
      simpa only [List.map_cons, runBlock_cons, runBlock_nil] using hcorr'

/-! ## 5. Counted-loop lift -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
  CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll in
/-- **The counted-loop lift on the immediate-carry subset.** A block whose fresh
    names bring the designated namespace back to where it started
    (`matCarrySlots bs ns = ns`) satisfies the fixed-namespace per-trip contract
    of `runBlock_lsem_agreeF_loop`, so it lifts over a runtime trip count: the
    `n`-fold `runBoundedLoopMem` over the lowered body runs to completion and its
    result corresponds to the `JState`-side `n`-fold `runBoundedLoop`, still in
    the canonical namespace. The name-disjointness condition is state-free, so
    the same `MatCarryFresh` serves every trip. A single opcode cannot satisfy
    `hret` (its fresh slot must differ from the one it replaces), but an
    even-length chain on one carry axis can: the second allocation may reuse the
    original name. -/
theorem runBlock_lsem_agreeMat_loop (bs : List (JInstr 64 × String))
    (flg : String → Prop) (z : String) (ns : String × String)
    (hb : ∀ p ∈ bs, InImmCarrySubset p.1) (hok : MatCarryFresh flg z bs ns)
    (hret : matCarrySlots bs ns = ns)
    (n : Nat) (s : JState 64) (ls : LstateM) (h : JLstateCorrF s ls flg ns.1 ns.2) :
    ∃ ls', runBoundedLoopMem (matCarryWires z bs ns) n ls = some ls' ∧
      JLstateCorrF (runBoundedLoop s n (bs.map Prod.fst)) ls' flg ns.1 ns.2 := by
  refine runBlock_lsem_agreeF_loop (bs.map Prod.fst) (matCarryWires z bs ns)
    flg ns.1 ns.2 (fun s' ls' h' => ?_) n s ls h
  obtain ⟨ls'', hstep, hcorr⟩ := runBlock_lsem_agreeMat bs flg z ns hb hok s' ls' h'
  rw [hret] at hcorr
  exact ⟨ls'', hstep, hcorr⟩

/-! ## 6. The carry-materialise gadget -/

/-- **The gadget `materialiseCarry hi` agrees on both machine models.** Its two
    opcodes — `.adcx hi (.imm 0)` folding the `CF` chain bit, then
    `.adox hi (.imm 0)` folding the `OF` chain bit — lower to the six-wire block
    `matCarryWires`, which does not fail and whose result corresponds, on the
    register, memory, and both carry axes, to the `runBlock` result. The
    designated namespace migrates from `(cfN, ofN)` to the two fresh slots
    `(cfNew, ofNew)`, so the wire block is the lsem twin of the
    `SchoolbookRunBlock` gadget whose value side is `materialiseCarry_value`. -/
theorem materialiseCarry_lsem_agree (hi z cfNew ofNew : String)
    (flg : String → Prop) (cfN ofN : String)
    (hok1 : MatCarrySlotsOk flg z cfNew hi cfN ofN)
    (hok2 : MatCarrySlotsOk flg z ofNew hi cfNew ofN)
    (s : JState 64) (ls : LstateM) (h : JLstateCorrF s ls flg cfN ofN) :
    ∃ ls', lsemStraightMem
        (matCarryWires z
          [(JInstr.adcx hi (JOperand.imm 0), cfNew),
           (JInstr.adox hi (JOperand.imm 0), ofNew)] (cfN, ofN)) ls = some ls' ∧
      JLstateCorrF (runBlock s (materialiseCarry hi)) ls' flg cfNew ofNew := by
  obtain ⟨ls', hstep, hcorr⟩ :=
    runBlock_lsem_agreeMat
      [(JInstr.adcx hi (JOperand.imm 0), cfNew), (JInstr.adox hi (JOperand.imm 0), ofNew)]
      flg z (cfN, ofN) (by simp [InImmCarrySubset]) ⟨hok1, hok2, trivial⟩ s ls h
  exact ⟨ls', hstep, hcorr⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgreeMatCarry
