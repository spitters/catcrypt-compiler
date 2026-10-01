/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenSim
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenSim
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem

@[expose] public section

set_option autoImplicit false

/-!
# Decoded simulations of the carry family

`DecodedLsemStep` relates a flag-machine instruction to the machine instructions it decodes
to under `DecLsemCorr`, which does not relate the carry and overflow flags. This module adds
the flag agreement `CCorr`: `DecLsemCorr` together with, when the carry (overflow) flag is
live, the machine flag `CF` (`OF`) holding the flag machine's `LstateM.cf` (`LstateM.of`).

The classes are the carry family `ADC`, `SBB`, `ADCX`, `ADOX` against the machine's `adc`,
`sbb`, `adcx`, `adox` on the register of the destination, which read the carry-in from the
live flag, and the flag writers `ADD`, `SUB`, `XOR` against `add`, `sub`, `xor`, after which
both flags are live.

## Main results

* `fstepF_of_carryArgs`: the flag machine's step of a carry-family instruction is
  `carryStep`.
* `decSimC_adc`, `decSimC_sbb`: add and subtract with the live carry flag.
* `decSimC_adcx`, `decSimC_adox`: the two independent chains of the ADX extension.
* `decSimC_add`, `decSimC_sub`, `decSimC_xor`: the flag writers, both flags live after.
* `decSimC_add_adc`: an `ADD`, `ADC` carry chain decodes to `add`, `adc`.
* `decSimC_mov2`, `decSimC_mov2_elided`, `decSimC_mov2Imm`, `decSimC_mulx`: the flag-quiet
  lift instructions stepped by `wideStep`, the two-source `MOV:64` against `mov` (or nothing)
  and the register `MULX:64` against `mulx`, both flags kept; `wideCls`, `wideCls_sound`:
  their Boolean class.
* `stepOKC`, `decSim_of_stepOKC`: the Boolean check `DecodeGenSim.stepOK` extended by the
  carry family, the flag writers, the flag-preserving register copy and the flag-quiet
  lift instructions, tracking which of the two flags is live; an accepted instruction
  simulates its machine instructions.
* `bodyOKC`, `decSim_of_bodyOKC`: the check over a body.
* `coreStepC`, `mbodyOKC_sound`, `decSim_of_loopOKC`: the word-array memory check of
  `DecodeGenMem` extended by the carry family, the flag writers and the flag-quiet lift
  instructions (`wideStepM`); the loads, stores, moves
  and frame reloads keep the live flags (`MCorrC`: `MCorr` with the flag agreement).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeCarry

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
  (lsemStepMem_of_carryArgs lsemStepMem_flags lsemStepMem_of_wideArgs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenSim
  (GCorr InjOn survives_of_injOn stepOK decSim_of_stepOK isCmpB)

/-! ## 1. The correspondence with flag agreement -/

/-- `DecLsemCorr` with the machine carry flag holding `b.cf` when `cl` holds and the machine
    overflow flag holding `b.of` when `ol` holds. -/
def CCorr (π : String → String) (L : String → Prop) (Lay : Layout)
    (frame : String → Option (BitVec 64)) (K : String → Nat → Prop) (zl cl ol : Prop) :
    AState → LstateM → Bool → Prop :=
  fun sa b zf => DecLsemCorr π L Lay frame K zl sa b zf
    ∧ (cl → sa.flags.cf = some b.cf) ∧ (ol → sa.flags.of = some b.of)

variable {π : String → String} {L L' : String → Prop} {Lay : Layout}
  {frame : String → Option (BitVec 64)} {K : String → Nat → Prop} {zl cl ol : Prop}

/-- The correspondence does not read the flag machine's carry and overflow flags. -/
theorem DecLsemCorr.setFlags {sa : AState} {b : LstateM} {zf : Bool}
    (h : DecLsemCorr π L Lay frame K zl sa b zf) (c o : Bool) :
    DecLsemCorr π L Lay frame K zl sa { b with cf := c, of := o } zf where
  regs r hr := h.regs r hr
  zfEq := h.zfEq
  cells A j hk := h.cells A j hk
  slots := h.slots

/-! ## 2. The flag machine's carry-family step -/

/-- The instruction `m:64 d, a, c` on registers. -/
def carryI (m d a c : String) : LinstrRM :=
  (.Lopn [.reg d] (withWidthTag 64 m) [.reg a, .reg c], .reg none)

/-- The step of a carry-family instruction is the carry step on the base. -/
theorem fstepF_of_carryArgs {i : LinstrRM} {p : CarryOp × String × LOperand × LOperand}
    (hc : cmpArgs? i = none) (hm : movRegArgs? i = none) (hk : carryArgs? i = some p)
    (b : LstateM) (zf : Bool) :
    fstepF i b zf = (carryStep p.1 p.2.1 p.2.2.1 p.2.2.2 b).map (fun t => (t, zf)) := by
  unfold fstepF stepMemF
  rw [hc, hm]
  simp only [lsemStepMem_of_carryArgs hk, hk]

theorem cmpArgs?_carryI (m d a c : String) (h : withWidthTag 64 m ≠ withWidthTag 64 "CMP") :
    cmpArgs? (carryI m d a c) = none := by
  simp only [cmpArgs?, carryI, if_neg h]

theorem movRegArgs?_carryI (m d a c : String) : movRegArgs? (carryI m d a c) = none := rfl

theorem carryArgs?_adc (d a c : String) :
    carryArgs? (carryI "ADC" d a c) = some (.adc, d, .reg a, .reg c) := by
  simp only [carryArgs?, carryI, if_true]

theorem carryArgs?_sbb (d a c : String) :
    carryArgs? (carryI "SBB" d a c) = some (.sbb, d, .reg a, .reg c) := by
  simp only [carryArgs?, carryI, if_true,
    if_neg (show withWidthTag 64 "SBB" ≠ withWidthTag 64 "ADC" by decide +kernel)]

theorem carryArgs?_adcx (d a c : String) :
    carryArgs? (carryI "ADCX" d a c) = some (.adcx, d, .reg a, .reg c) := by
  simp only [carryArgs?, carryI, if_true,
    if_neg (show withWidthTag 64 "ADCX" ≠ withWidthTag 64 "ADC" by decide +kernel),
    if_neg (show withWidthTag 64 "ADCX" ≠ withWidthTag 64 "SBB" by decide +kernel)]

theorem carryArgs?_adox (d a c : String) :
    carryArgs? (carryI "ADOX" d a c) = some (.adox, d, .reg a, .reg c) := by
  simp only [carryArgs?, carryI, if_true,
    if_neg (show withWidthTag 64 "ADOX" ≠ withWidthTag 64 "ADC" by decide +kernel),
    if_neg (show withWidthTag 64 "ADOX" ≠ withWidthTag 64 "SBB" by decide +kernel),
    if_neg (show withWidthTag 64 "ADOX" ≠ withWidthTag 64 "ADCX" by decide +kernel)]

/-! ## 3. The carry family -/

/-- `ADC:64 d, a, c` against `adc %c, %d` with `d` and `a` in one register and the carry
    flag live; afterwards both flags are live. -/
theorem decSimC_adc (d a c : String) (ha : L a) (hc : L c) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (CCorr π L Lay frame K zl True ol) (CCorr π L' Lay frame K False True True)
      [carryI "ADC" d a c] [.adc (π d) (.reg (π c))] := by
  refine DecSim.single fun sa b zf h => ?_
  obtain ⟨hC, hcf, -⟩ := h
  have hva := hC.regs a ha
  have hvc := hC.regs c hc
  have hcin : sa.flags.cf.getD false = b.cf := by rw [hcf trivial]; rfl
  rw [fstepF_of_carryArgs (cmpArgs?_carryI _ _ _ _ (by decide +kernel))
    (movRegArgs?_carryI _ _ _ _) (carryArgs?_adc d a c)]
  simp only [carryStep, evalOperandN, hva, hvc, Option.map_some]
  refine ⟨_, zf, rfl, ?_, fun _ => ?_, fun _ => ?_⟩
  · refine DecLsemCorr.setFlags (hC.write d (x86_ADC (sa.regs (π a)) (sa.regs (π c)) b.cf).word
      (evalInstrA sa (.adc (π d) (.reg (π c)))) (fun r => ?_) rfl hL
      (fun hz : False => hz.elim)) _ _
    show (if r = π d then _ else _) = _
    simp only [JState.get, JOperand.eval, AState.view, JState.flagB, hcin, hda]
  · show (x86_ADC (sa.regs (π d)) (sa.regs (π c)) (sa.flags.cf.getD false)).cf = _
    rw [hcin, hda]
    rfl
  · show (x86_ADC (sa.regs (π d)) (sa.regs (π c)) (sa.flags.cf.getD false)).of = _
    rw [hcin, hda]
    rfl

/-- `SBB:64 d, a, c` against `sbb %c, %d` with `d` and `a` in one register and the carry
    flag live; afterwards both flags are live. -/
theorem decSimC_sbb (d a c : String) (ha : L a) (hc : L c) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (CCorr π L Lay frame K zl True ol) (CCorr π L' Lay frame K False True True)
      [carryI "SBB" d a c] [.sbb (π d) (.reg (π c))] := by
  refine DecSim.single fun sa b zf h => ?_
  obtain ⟨hC, hcf, -⟩ := h
  have hva := hC.regs a ha
  have hvc := hC.regs c hc
  have hcin : sa.flags.cf.getD false = b.cf := by rw [hcf trivial]; rfl
  rw [fstepF_of_carryArgs (cmpArgs?_carryI _ _ _ _ (by decide +kernel))
    (movRegArgs?_carryI _ _ _ _) (carryArgs?_sbb d a c)]
  simp only [carryStep, evalOperandN, hva, hvc, Option.map_some]
  refine ⟨_, zf, rfl, ?_, fun _ => ?_, fun _ => ?_⟩
  · refine DecLsemCorr.setFlags (hC.write d (x86_SBB (sa.regs (π a)) (sa.regs (π c)) b.cf).word
      (evalInstrA sa (.sbb (π d) (.reg (π c)))) (fun r => ?_) rfl hL
      (fun hz : False => hz.elim)) _ _
    show (if r = π d then _ else _) = _
    simp only [JState.get, JOperand.eval, AState.view, JState.flagB, hcin, hda]
  · show (x86_SBB (sa.regs (π d)) (sa.regs (π c)) (sa.flags.cf.getD false)).cf = _
    rw [hcin, hda]
    rfl
  · show (x86_SBB (sa.regs (π d)) (sa.regs (π c)) (sa.flags.cf.getD false)).of = _
    rw [hcin, hda]
    rfl

/-- `ADCX:64 d, a, c` against `adcx %c, %d` with `d` and `a` in one register and the carry
    flag live; the overflow flag keeps its agreement. -/
theorem decSimC_adcx (d a c : String) (ha : L a) (hc : L c) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (CCorr π L Lay frame K zl True ol) (CCorr π L' Lay frame K False True ol)
      [carryI "ADCX" d a c] [.adcx (π d) (.reg (π c))] := by
  refine DecSim.single fun sa b zf h => ?_
  obtain ⟨hC, hcf, hof⟩ := h
  have hva := hC.regs a ha
  have hvc := hC.regs c hc
  have hcin : sa.flags.cf.getD false = b.cf := by rw [hcf trivial]; rfl
  rw [fstepF_of_carryArgs (cmpArgs?_carryI _ _ _ _ (by decide +kernel))
    (movRegArgs?_carryI _ _ _ _) (carryArgs?_adcx d a c)]
  simp only [carryStep, evalOperandN, hva, hvc, Option.map_some]
  refine ⟨_, zf, rfl, ?_, fun _ => ?_, fun hol => ?_⟩
  · refine DecLsemCorr.setFlags (hC.write d (x86_ADCX (sa.regs (π a)) (sa.regs (π c)) b.cf).2
      (evalInstrA sa (.adcx (π d) (.reg (π c)))) (fun r => ?_) rfl hL
      (fun hz : False => hz.elim)) _ _
    show (if r = π d then _ else _) = _
    simp only [JState.get, JOperand.eval, AState.view, JState.flagB, hcin, hda]
    rfl
  · show (x86_ADCX (sa.regs (π d)) (sa.regs (π c)) (sa.flags.cf.getD false)).1 = _
    rw [hcin, hda]
    rfl
  · exact hof hol

/-- `ADOX:64 d, a, c` against `adox %c, %d` with `d` and `a` in one register and the
    overflow flag live; the carry flag keeps its agreement. -/
theorem decSimC_adox (d a c : String) (ha : L a) (hc : L c) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (CCorr π L Lay frame K zl cl True) (CCorr π L' Lay frame K False cl True)
      [carryI "ADOX" d a c] [.adox (π d) (.reg (π c))] := by
  refine DecSim.single fun sa b zf h => ?_
  obtain ⟨hC, hcf, hof⟩ := h
  have hva := hC.regs a ha
  have hvc := hC.regs c hc
  have hoin : sa.flags.of.getD false = b.of := by rw [hof trivial]; rfl
  rw [fstepF_of_carryArgs (cmpArgs?_carryI _ _ _ _ (by decide +kernel))
    (movRegArgs?_carryI _ _ _ _) (carryArgs?_adox d a c)]
  simp only [carryStep, evalOperandN, hva, hvc, Option.map_some]
  refine ⟨_, zf, rfl, ?_, fun hcl => ?_, fun _ => ?_⟩
  · refine DecLsemCorr.setFlags (hC.write d (x86_ADCX (sa.regs (π a)) (sa.regs (π c)) b.of).2
      (evalInstrA sa (.adox (π d) (.reg (π c)))) (fun r => ?_) rfl hL
      (fun hz : False => hz.elim)) _ _
    show (if r = π d then _ else _) = _
    simp only [JState.get, JOperand.eval, AState.view, JState.flagB, hoin, hda]
    rfl
  · exact hcf hcl
  · show (x86_ADCX (sa.regs (π d)) (sa.regs (π c)) (sa.flags.of.getD false)).1 = _
    rw [hoin, hda]
    rfl

/-! ## 4. The flag writers -/

theorem aluFlagOp?_addI (d a c : String) :
    aluFlagOp? (addI d a c) = some (.add, .reg a, .reg c) := by
  simp only [aluFlagOp?, addI, binRegI]
  rw [if_pos (by decide +kernel)]

theorem aluFlagOp?_subI (d a c : String) :
    aluFlagOp? (subI d a c) = some (.sub, .reg a, .reg c) := by
  simp only [aluFlagOp?, subI, binRegI]
  rw [if_neg (by decide +kernel), if_pos (by decide +kernel)]

theorem aluFlagOp?_xorI (d a c : String) :
    aluFlagOp? (xorI d a c) = some (.xor, .reg a, .reg c) := by
  simp only [aluFlagOp?, xorI, binRegI]
  rw [if_neg (by decide +kernel), if_neg (by decide +kernel), if_neg (by decide +kernel),
    if_neg (by decide +kernel), if_pos (by decide +kernel)]

/-- The flags `withALUFlags` writes for a recognised operation on two registers readable at
    width `64`. -/
theorem withALUFlags_reg2 {i : LinstrRM} {op : AluOp} {a c : String}
    (hi : aluFlagOp? i = some (op, .reg a, .reg c)) {s0 : LstateM} {va vc : BitVec 64}
    (ha : s0.reg.getW a 64 = some va) (hc : s0.reg.getW c 64 = some vc) (s1 : LstateM) :
    (withALUFlags i s0 s1).cf = (aluB5 op va vc).cf.getD false
      ∧ (withALUFlags i s0 s1).of = (aluB5 op va vc).of.getD false := by
  unfold withALUFlags
  rw [hi]
  simp [evalOperandN, ha, hc]

/-- A flag writer `opn:64 d, a, c` against the two-address machine operation `mk`, whose flag
    record is `aluB5 op`, with `d` and `a` in one register; afterwards both flags are live. -/
theorem decSimC_alu (opn base : String) (op : AluOp) (hstrip : stripWidthTag opn = base)
    (hcmp : opn ≠ withWidthTag 64 "CMP") (hmul : base ≠ "MULXHI")
    (hcarry : base ≠ "ADC" ∧ base ≠ "SBB" ∧ base ≠ "ADCX" ∧ base ≠ "ADOX")
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hf : ∀ x y, applyOpnN 64 base [x, y] = some (f x y))
    (hop : ∀ d a c : String, aluFlagOp? (binRegI opn d a c) = some (op, .reg a, .reg c))
    (mk : String → JOperand → JInstr 64)
    (hmk : ∀ (sa : AState) (D S r : String),
      (evalInstrA sa (mk D (.reg S))).regs r
        = if r = D then f (sa.regs D) (sa.regs S) else sa.regs r)
    (hmkm : ∀ (sa : AState) (D S : String), (evalInstrA sa (mk D (.reg S))).mem = sa.mem)
    (hmkf : ∀ (sa : AState) (D S : String),
      (evalInstrA sa (mk D (.reg S))).flags.cf = (aluB5 op (sa.regs D) (sa.regs S)).cf
        ∧ (evalInstrA sa (mk D (.reg S))).flags.of = (aluB5 op (sa.regs D) (sa.regs S)).of)
    (hsome : ∀ x y, (aluB5 op x y).cf = some ((aluB5 op x y).cf.getD false)
        ∧ (aluB5 op x y).of = some ((aluB5 op x y).of.getD false))
    (d a c : String) (ha : L a) (hc : L c) (hda : π d = π a) (hL : Survives π L L' d) :
    DecSim (CCorr π L Lay frame K zl cl ol) (CCorr π L' Lay frame K False True True)
      [binRegI opn d a c] [mk (π d) (.reg (π c))] := by
  refine DecSim.single fun sa b zf h => ?_
  obtain ⟨hC, -, -⟩ := h
  have hva := hC.regs a ha
  have hvc := hC.regs c hc
  rw [fstepF_binRegI opn base d a c hstrip hcmp hmul hcarry (ne_mov_of_applyOpnN hf) b zf _ hva,
    hvc, Option.bind_some, hf, Option.map_some]
  have hw := withALUFlags_reg2 (hop d a c) hva hvc
    ((b.setReg d (f (sa.regs (π a)) (sa.regs (π c)))).nextPc)
  refine ⟨_, zf, rfl, DecLsemCorr.withALUFlags (hC.write d (f (sa.regs (π a)) (sa.regs (π c)))
    (evalInstrA sa (mk (π d) (.reg (π c)))) (fun r => by rw [hmk, hda]) (hmkm _ _ _) hL
    (fun hz : False => hz.elim)) _ _, fun _ => ?_, fun _ => ?_⟩
  · rw [(hmkf sa (π d) (π c)).1, hw.1, hda]
    exact (hsome _ _).1
  · rw [(hmkf sa (π d) (π c)).2, hw.2, hda]
    exact (hsome _ _).2

/-- `ADD:64 d, a, c` against `add %c, %d` with `d` and `a` in one register. -/
theorem decSimC_add (d a c : String) (ha : L a) (hc : L c) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (CCorr π L Lay frame K zl cl ol) (CCorr π L' Lay frame K False True True)
      [addI d a c] [.add (π d) (.reg (π c))] :=
  decSimC_alu _ "ADD" .add JasminLsemMemSourceTieUncond.stripWidthTag_ADD64
    (by decide +kernel) (by decide) (by decide) (· + ·) (fun _ _ => rfl)
    aluFlagOp?_addI JInstr.add (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) d a c ha hc hda hL

/-- `SUB:64 d, a, c` against `sub %c, %d` with `d` and `a` in one register. -/
theorem decSimC_sub (d a c : String) (ha : L a) (hc : L c) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (CCorr π L Lay frame K zl cl ol) (CCorr π L' Lay frame K False True True)
      [subI d a c] [.sub (π d) (.reg (π c))] :=
  decSimC_alu _ "SUB" .sub JasminLsemMemSourceTieUncond.stripWidthTag_SUB64
    (by decide +kernel) (by decide) (by decide) (· - ·) (fun _ _ => rfl)
    aluFlagOp?_subI JInstr.sub (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) d a c ha hc hda hL

/-- `XOR:64 d, a, c` against `xor %c, %d` with `d` and `a` in one register; both flags are
    cleared. -/
theorem decSimC_xor (d a c : String) (ha : L a) (hc : L c) (hda : π d = π a)
    (hL : Survives π L L' d) :
    DecSim (CCorr π L Lay frame K zl cl ol) (CCorr π L' Lay frame K False True True)
      [xorI d a c] [.xor_ (π d) (.reg (π c))] :=
  decSimC_alu _ "XOR" .xor stripWidthTag_XOR64
    (by decide +kernel) (by decide) (by decide) (· ^^^ ·) (fun _ _ => rfl)
    aluFlagOp?_xorI JInstr.xor_ (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => ⟨rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl⟩) d a c ha hc hda hL

/-! ## 5. A carry chain -/

/-- **An `ADD`, `ADC` carry chain decodes to `add`, `adc`.** The `ADD` makes the carry flag
    live and the `ADC` reads it; the two classes compose. -/
theorem decSimC_add_adc {L'' : String → Prop} (d0 a0 c0 d1 a1 c1 : String)
    (ha0 : L a0) (hc0 : L c0) (hda0 : π d0 = π a0) (hL0 : Survives π L L' d0)
    (ha1 : L' a1) (hc1 : L' c1) (hda1 : π d1 = π a1) (hL1 : Survives π L' L'' d1) :
    DecSim (CCorr π L Lay frame K zl cl ol) (CCorr π L'' Lay frame K False True True)
      [addI d0 a0 c0, carryI "ADC" d1 a1 c1]
      [.add (π d0) (.reg (π c0)), .adc (π d1) (.reg (π c1))] :=
  (decSimC_add d0 a0 c0 ha0 hc0 hda0 hL0).append (decSimC_adc d1 a1 c1 ha1 hc1 hda1 hL1)

/-! ## 6. The register copy keeps the flags -/

/-- `MOV:64 d, s` against `mov %s, %d`: neither machine touches a flag. -/
theorem decSimC_movReg (d s : String) (hs : L s) (hL : Survives π L L' d) :
    DecSim (CCorr π L Lay frame K zl cl ol) (CCorr π L' Lay frame K False cl ol)
      [movRI d s] [.mov (π d) (.reg (π s))] :=
  DecSim.single fun _ b zf h =>
    ⟨_, zf, fstepF_movRI d s b zf _ (h.1.regs s hs),
      h.1.write d _ _ (fun _ => rfl) rfl hL (fun hz : False => hz.elim), h.2.1, h.2.2⟩

/-- `MOV:64 d, s` with `d` and `s` in one machine register, against nothing. -/
theorem decSimC_movReg_elided (d s : String) (hs : L s) (hds : π d = π s)
    (hL : Survives π L L' d) :
    DecSim (CCorr π L Lay frame K zl cl ol) (CCorr π L' Lay frame K False cl ol)
      [movRI d s] [] :=
  DecSim.lsemOnly fun sa b zf h =>
    ⟨_, zf, fstepF_movRI d s b zf _ (h.1.regs s hs),
      h.1.write d (sa.regs (π s)) sa (fun r => by split <;> simp_all) rfl hL (fun hz : False => hz.elim),
      h.2.1, h.2.2⟩

/-! ## 7. The flag-quiet lift instructions

The two-source copy `MOV:64 d, x, b` (printed `mov b, d`; the first source is not read) and
the widening multiply `MULX:64 lo, hi, c` (printed `mulx c, lo, hi`, with the implicit first
source `mulxSrc`), which the flag machine steps by `wideStep`. Neither machine writes a
flag, so the flag agreement is kept. -/

/-- The two-source copy `MOV:64 d, x, b`. -/
def mov2I (d : String) (x b : LOperand) : LinstrRM :=
  (.Lopn [.reg d] (withWidthTag 64 "MOV") [x, b], .reg none)

/-- The widening multiply `MULX:64 lo, hi, b`. -/
def mulxI (lo hi : String) (b : LOperand) : LinstrRM :=
  (.Lopn [.reg lo, .reg hi] (withWidthTag 64 "MULX") [b], .reg none)

/-- The step of a flag-quiet lift instruction is `wideStep` on the base. -/
theorem fstepF_of_wideArgs {i : LinstrRM} {w : WideOp} (hc : cmpArgs? i = none)
    (hm : movRegArgs? i = none) (hk : carryArgs? i = none) (hw : wideArgs? i = some w)
    (b : LstateM) (zf : Bool) :
    fstepF i b zf = (wideStep w b).map (fun t => (t, zf)) := by
  unfold fstepF stepMemF
  rw [hc, hm]
  simp only [lsemStepMem_of_wideArgs hw, hk, hw]

theorem fstepF_mov2I (d : String) (x b : LOperand) (s : LstateM) (zf : Bool) :
    fstepF (mov2I d x b) s zf = (wideStep (.mov d b) s).map (fun t => (t, zf)) :=
  fstepF_of_wideArgs
    (by simp only [cmpArgs?, mov2I]; rw [if_neg (by decide +kernel)])
    (by cases x <;> cases b <;> rfl)
    (by simp only [carryArgs?, mov2I]; rw [if_neg (by decide +kernel), if_neg (by decide +kernel),
      if_neg (by decide +kernel), if_neg (by decide +kernel)])
    (by simp only [wideArgs?, mov2I, if_true]) s zf

theorem fstepF_mulxI (lo hi : String) (b : LOperand) (s : LstateM) (zf : Bool) :
    fstepF (mulxI lo hi b) s zf = (wideStep (.mulx lo hi b) s).map (fun t => (t, zf)) :=
  fstepF_of_wideArgs rfl rfl rfl (by simp only [wideArgs?, mulxI, true_or, if_true]) s zf

/-- `MOV:64 d, x, s` against `mov %s, %d`. -/
theorem decSimC_mov2 (d : String) (x : LOperand) (s : String) (hs : L s)
    (hL : Survives π L L' d) :
    DecSim (CCorr π L Lay frame K zl cl ol) (CCorr π L' Lay frame K False cl ol)
      [mov2I d x (.reg s)] [.mov (π d) (.reg (π s))] :=
  DecSim.single fun _ b zf h =>
    ⟨_, zf, by rw [fstepF_mov2I]; simp only [wideStep, evalOperandN, h.1.regs s hs,
        Option.map_some]; rfl,
      h.1.write d _ _ (fun _ => rfl) rfl hL (fun hz : False => hz.elim), h.2.1, h.2.2⟩

/-- `MOV:64 d, x, s` with `d` and `s` in one machine register, against nothing. -/
theorem decSimC_mov2_elided (d : String) (x : LOperand) (s : String) (hs : L s)
    (hds : π d = π s) (hL : Survives π L L' d) :
    DecSim (CCorr π L Lay frame K zl cl ol) (CCorr π L' Lay frame K False cl ol)
      [mov2I d x (.reg s)] [] :=
  DecSim.lsemOnly fun sa b zf h =>
    ⟨_, zf, by rw [fstepF_mov2I]; simp only [wideStep, evalOperandN, h.1.regs s hs,
        Option.map_some],
      h.1.write d (sa.regs (π s)) sa (fun r => by split <;> simp_all) rfl hL (fun hz : False => hz.elim),
      h.2.1, h.2.2⟩

/-- `MOV:64 d, x, #n` against `mov $n, %d`. -/
theorem decSimC_mov2Imm (d : String) (x : LOperand) (n : Nat) (hL : Survives π L L' d) :
    DecSim (CCorr π L Lay frame K zl cl ol) (CCorr π L' Lay frame K False cl ol)
      [mov2I d x (.imm n)] [.mov (π d) (.imm n)] :=
  DecSim.single fun _ b zf h =>
    ⟨_, zf, by rw [fstepF_mov2I]; rfl,
      h.1.write d _ _ (fun _ => rfl) rfl hL (fun hz : False => hz.elim), h.2.1, h.2.2⟩

/-- A write of `vlo` to the name `lo` and then of `vhi` to the name `hi` on the flag machine,
    and to the distinct registers `π lo` and `π hi` on the machine, memory unchanged,
    preserves the correspondence on a surviving live set. -/
theorem DecLsemCorr.write2 {sa : AState} {b : LstateM} {zf : Bool}
    (h : DecLsemCorr π L Lay frame K zl sa b zf) (lo hi : String) (vlo vhi : BitVec 64)
    (sa' : AState)
    (hregs : ∀ r, sa'.regs r = if r = π hi then vhi else if r = π lo then vlo else sa.regs r)
    (hmem : sa'.mem = sa.mem) (hHL : π hi ≠ π lo)
    (hL : ∀ r, L' r → r = hi ∨ r = lo ∨ (L r ∧ π r ≠ π lo ∧ π r ≠ π hi)) :
    DecLsemCorr π L' Lay frame K False sa' (((b.setReg lo vlo).setReg hi vhi).nextPc) zf where
  regs r hr := by
    rw [LstateM.reg_nextPc, LstateN.getW_nextPc, LstateM.reg_setReg, LstateM.reg_setReg]
    rcases hL r hr with rfl | rfl | ⟨hrL, h1, h2⟩
    · rw [LstateN.getW_setReg_same, hregs, if_pos rfl]
    · have hne : r ≠ hi := fun e => hHL (by rw [e])
      rw [LstateN.getW_setReg_other _ _ _ _ _ hne, LstateN.getW_setReg_same, hregs,
        if_neg (Ne.symm hHL), if_pos rfl]
    · have hne1 : r ≠ hi := fun e => h2 (by rw [e])
      have hne2 : r ≠ lo := fun e => h1 (by rw [e])
      rw [LstateN.getW_setReg_other _ _ _ _ _ hne1, LstateN.getW_setReg_other _ _ _ _ _ hne2,
        h.regs r hrL, hregs, if_neg h2, if_neg h1]
  zfEq hz := hz.elim
  cells A j hk := by
    obtain ⟨hj, arr, ha, hr⟩ := h.cells A j hk
    exact ⟨hj, arr, by simpa using ha, by rw [hmem]; exact hr⟩
  slots A q hq := by rw [hmem]; exact h.slots A q hq

/-- `MULX:64 lo, hi, c` against `mulx %c, %lo, %hi` whose implicit source is the register of
    `mulxSrc`, with distinct destination registers. -/
theorem decSimC_mulx (lo hi c : String) (hR : L mulxSrc) (hc : L c) (hHL : π hi ≠ π lo)
    (hL : ∀ r, L' r → r = hi ∨ r = lo ∨ (L r ∧ π r ≠ π lo ∧ π r ≠ π hi)) :
    DecSim (CCorr π L Lay frame K zl cl ol) (CCorr π L' Lay frame K False cl ol)
      [mulxI lo hi (.reg c)] [.mulx (π hi) (π lo) (.reg (π mulxSrc)) (.reg (π c))] := by
  refine DecSim.single fun sa b zf h => ?_
  obtain ⟨hC, hcf, hof⟩ := h
  rw [fstepF_mulxI]
  simp only [wideStep, evalOperandN, hC.regs mulxSrc hR, hC.regs c hc, Option.map_some]
  exact ⟨_, zf, rfl, DecLsemCorr.write2 hC lo hi _ _ _ (fun _ => rfl) rfl hHL hL, hcf, hof⟩

/-- The names live after a write of the names `ws`: a written name, or a name live before
    whose register is the register of no written name. -/
def SurvivesL (π : String → String) (L L' : String → Prop) (ws : List String) : Prop :=
  ∀ r, L' r → r ∈ ws ∨ (L r ∧ ∀ w ∈ ws, π r ≠ π w)

theorem survivesL_of_injOn {N : List String} (hinj : InjOn π N) {ws : List String}
    (hws : ∀ w ∈ ws, w ∈ N) : SurvivesL π (· ∈ N) (· ∈ N) ws := fun r hr =>
  if h : r ∈ ws then Or.inl h
  else Or.inr ⟨hr, fun w hw he => h (by rw [hinj r hr w (hws w hw) he]; exact hw)⟩

/-- The flag-quiet lift classes against their machine instructions: the two-source copy of
    a register (`mov`, or nothing when `d` and `s` share a register) or of an immediate, and
    the register `MULX` with distinct destination registers. The result is the names read
    and the names written, or `none` for no class. -/
def wideCls (π : String → String) (i : LinstrRM) (js : List (JInstr 64)) :
    Option (List String × List String) :=
  match i with
  | (.Lopn [.reg d] opn [_, .reg s], .reg none) =>
      if opn == withWidthTag 64 "MOV"
          && (js == [.mov (π d) (.reg (π s))] || (π d == π s && js.isEmpty)) then
        some ([s], [d])
      else none
  | (.Lopn [.reg d] opn [_, .imm n], .reg none) =>
      if opn == withWidthTag 64 "MOV" && js == [.mov (π d) (.imm n)] then some ([], [d])
      else none
  | (.Lopn [.reg lo, .reg hi] opn [.reg c], .reg none) =>
      if opn == withWidthTag 64 "MULX" && π hi != π lo
          && js == [.mulx (π hi) (π lo) (.reg (π mulxSrc)) (.reg (π c))] then
        some ([mulxSrc, c], [lo, hi])
      else none
  | _ => none

theorem wideCls_sound {i : LinstrRM} {js : List (JInstr 64)} {srcs ws : List String}
    (h : wideCls π i js = some (srcs, ws)) (hs : ∀ r ∈ srcs, L r) (hL : SurvivesL π L L' ws) :
    DecSim (CCorr π L Lay frame K zl cl ol) (CCorr π L' Lay frame K False cl ol) [i] js := by
  unfold wideCls at h
  split at h
  · rename_i d opn x s
    split_ifs at h with hc
    cases h
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.isEmpty_iff] at hc
    obtain ⟨rfl, hj⟩ := hc
    have hS : Survives π L L' d := fun r hr =>
      (hL r hr).imp List.mem_singleton.mp fun h' => ⟨h'.1, h'.2 d (List.mem_singleton_self d)⟩
    rcases hj with rfl | ⟨hds, rfl⟩
    · exact decSimC_mov2 d x s (hs s (List.mem_singleton_self s)) hS
    · exact decSimC_mov2_elided d x s (hs s (List.mem_singleton_self s)) hds hS
  · rename_i d opn x n
    split_ifs at h with hc
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact decSimC_mov2Imm d x n fun r hr =>
      (hL r hr).imp List.mem_singleton.mp fun h' => ⟨h'.1, h'.2 d (List.mem_singleton_self d)⟩
  · rename_i lo hi opn c
    split_ifs at h with hc
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨rfl, hHL⟩, rfl⟩ := hc
    refine decSimC_mulx lo hi c (hs _ (by simp)) (hs c (by simp)) hHL fun r hr => ?_
    rcases hL r hr with hw | ⟨hrL, hne⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨hrL, hne lo (by simp), hne hi (by simp)⟩)
  · cases h

/-! ## 8. The check with flag liveness -/

/-- A register instruction of `DecodeGenSim.stepOK` simulates its machine instructions
    with no flag live afterwards. -/
theorem decSimC_of_stepOK {N : List String} (hinj : InjOn π N) {i : LinstrRM}
    {js : List (JInstr 64)} (h : stepOK π N i js = true) :
    DecSim (CCorr π (· ∈ N) Lay frame K zl cl ol)
      (CCorr π (· ∈ N) Lay frame K False False False) [i] js :=
  (decSim_of_stepOK (Lay := Lay) (frame := frame) (K := K) (zl := zl) hinj h).weaken
    (fun _ _ _ h => h.1) (fun _ _ _ h => ⟨h.dropZf, fun hf => hf.elim, fun hf => hf.elim⟩)

/-- The carry family and the flag writers `opn:64 d, a, c` with `d` and `a` in one register,
    with the flags live before (`fl`); the flags live afterwards, or `none` for no class. -/
def carryOp (π : String → String) (fl : Bool × Bool) (d opn a c : String)
    (js : List (JInstr 64)) : Option (Bool × Bool) :=
  if π d == π a then
    match js with
    | [.adc D (.reg C)] =>
        if opn == withWidthTag 64 "ADC" && D == π d && C == π c && fl.1 then some (true, true)
        else none
    | [.sbb D (.reg C)] =>
        if opn == withWidthTag 64 "SBB" && D == π d && C == π c && fl.1 then some (true, true)
        else none
    | [.adcx D (.reg C)] =>
        if opn == withWidthTag 64 "ADCX" && D == π d && C == π c && fl.1 then some (true, fl.2)
        else none
    | [.adox D (.reg C)] =>
        if opn == withWidthTag 64 "ADOX" && D == π d && C == π c && fl.2 then some (fl.1, true)
        else none
    | [.add D (.reg C)] =>
        if opn == "ADD:64" && D == π d && C == π c then some (true, true) else none
    | [.sub D (.reg C)] =>
        if opn == "SUB:64" && D == π d && C == π c then some (true, true) else none
    | [.xor_ D (.reg C)] =>
        if opn == "XOR:64" && D == π d && C == π c then some (true, true) else none
    | _ => none
  else none

theorem carryOp_sound {fl fl' : Bool × Bool} {d opn a c : String} {js : List (JInstr 64)}
    (h : carryOp π fl d opn a c js = some fl') (ha : L a) (hc : L c) (hS : Survives π L L' d) :
    DecSim (CCorr π L Lay frame K zl (fl.1 = true) (fl.2 = true))
      (CCorr π L' Lay frame K False (fl'.1 = true) (fl'.2 = true))
      [(.Lopn [.reg d] opn [.reg a, .reg c], .reg none)] js := by
  unfold carryOp at h
  split_ifs at h with hda
  simp only [beq_iff_eq] at hda
  split at h
  · split_ifs at h with hc'
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    cases h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hf⟩ := hc'
    exact (decSimC_adc (ol := fl.2 = true) d a c ha hc hda hS).weaken
      (fun _ _ _ h => ⟨h.1, fun _ => h.2.1 hf, h.2.2⟩)
      (fun _ _ _ h => ⟨h.1, fun _ => h.2.1 trivial, fun _ => h.2.2 trivial⟩)
  · split_ifs at h with hc'
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    cases h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hf⟩ := hc'
    exact (decSimC_sbb (ol := fl.2 = true) d a c ha hc hda hS).weaken
      (fun _ _ _ h => ⟨h.1, fun _ => h.2.1 hf, h.2.2⟩)
      (fun _ _ _ h => ⟨h.1, fun _ => h.2.1 trivial, fun _ => h.2.2 trivial⟩)
  · split_ifs at h with hc'
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    cases h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hf⟩ := hc'
    exact (decSimC_adcx (ol := fl.2 = true) d a c ha hc hda hS).weaken
      (fun _ _ _ h => ⟨h.1, fun _ => h.2.1 hf, h.2.2⟩)
      (fun _ _ _ h => ⟨h.1, fun _ => h.2.1 trivial, h.2.2⟩)
  · split_ifs at h with hc'
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    cases h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hf⟩ := hc'
    exact (decSimC_adox (cl := fl.1 = true) d a c ha hc hda hS).weaken
      (fun _ _ _ h => ⟨h.1, h.2.1, fun _ => h.2.2 hf⟩)
      (fun _ _ _ h => ⟨h.1, h.2.1, fun _ => h.2.2 trivial⟩)
  · split_ifs at h with hc'
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    cases h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc'
    exact (decSimC_add (cl := fl.1 = true) (ol := fl.2 = true) d a c ha hc hda hS).weaken
      (fun _ _ _ h => h)
      (fun _ _ _ h => ⟨h.1, fun _ => h.2.1 trivial, fun _ => h.2.2 trivial⟩)
  · split_ifs at h with hc'
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    cases h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc'
    exact (decSimC_sub (cl := fl.1 = true) (ol := fl.2 = true) d a c ha hc hda hS).weaken
      (fun _ _ _ h => h)
      (fun _ _ _ h => ⟨h.1, fun _ => h.2.1 trivial, fun _ => h.2.2 trivial⟩)
  · split_ifs at h with hc'
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    cases h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc'
    exact (decSimC_xor (cl := fl.1 = true) (ol := fl.2 = true) d a c ha hc hda hS).weaken
      (fun _ _ _ h => h)
      (fun _ _ _ h => ⟨h.1, fun _ => h.2.1 trivial, fun _ => h.2.2 trivial⟩)
  · cases h

/-- The carry family and the flag writers on registers of `N`, with the flags live before
    (`fl`); the flags live afterwards, or `none` for no class. -/
def carryClass (π : String → String) (N : List String) (fl : Bool × Bool)
    (d opn a c : String) (js : List (JInstr 64)) : Option (Bool × Bool) :=
  if N.contains d && N.contains a && N.contains c then carryOp π fl d opn a c js else none

theorem carryClass_sound {N : List String} (hinj : InjOn π N) {fl fl' : Bool × Bool}
    {d opn a c : String} {js : List (JInstr 64)} (h : carryClass π N fl d opn a c js = some fl') :
    DecSim (CCorr π (· ∈ N) Lay frame K zl (fl.1 = true) (fl.2 = true))
      (CCorr π (· ∈ N) Lay frame K False (fl'.1 = true) (fl'.2 = true))
      [(.Lopn [.reg d] opn [.reg a, .reg c], .reg none)] js := by
  unfold carryClass at h
  split_ifs at h with hN
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hN
  obtain ⟨⟨hd, ha⟩, hc⟩ := hN
  exact carryOp_sound h ha hc (survives_of_injOn hinj hd)

/-- The check with flag liveness without the flag-quiet lift classes: a carry-family
    instruction or a flag writer (`carryClass`), a register copy that keeps the flags, or any
    instruction of `DecodeGenSim.stepOK` with no flag live afterwards. -/
def stepOKCBase (π : String → String) (N : List String) (fl : Bool × Bool) (i : LinstrRM)
    (js : List (JInstr 64)) : Option (Bool × Bool) :=
  match i with
  | (.Lopn [.reg d] opn [.reg a, .reg c], .reg none) =>
      match carryClass π N fl d opn a c js with
      | some fl' => some fl'
      | none => if stepOK π N i js then some (false, false) else none
  | (.Lopn [.reg d] opn [.reg a], .reg none) =>
      if N.contains d && N.contains a && opn == withWidthTag 64 "MOV" then
        if js == [.mov (π d) (.reg (π a))] then some fl
        else if π d == π a && js.isEmpty then some fl
        else if stepOK π N i js then some (false, false) else none
      else if stepOK π N i js then some (false, false) else none
  | _ => if stepOK π N i js then some (false, false) else none

theorem decSim_of_stepOKCBase {N : List String} (hinj : InjOn π N) {fl fl' : Bool × Bool}
    {i : LinstrRM} {js : List (JInstr 64)} (h : stepOKCBase π N fl i js = some fl') :
    DecSim (CCorr π (· ∈ N) Lay frame K zl (fl.1 = true) (fl.2 = true))
      (CCorr π (· ∈ N) Lay frame K False (fl'.1 = true) (fl'.2 = true)) [i] js := by
  have hfb : stepOK π N i js = true → fl' = (false, false) →
      DecSim (CCorr π (· ∈ N) Lay frame K zl (fl.1 = true) (fl.2 = true))
        (CCorr π (· ∈ N) Lay frame K False (fl'.1 = true) (fl'.2 = true)) [i] js := by
    intro hs hfl
    subst hfl
    exact (decSimC_of_stepOK hinj hs).weaken (fun _ _ _ h => h)
      (fun _ _ _ h => ⟨h.1, fun hf => by simp at hf, fun hf => by simp at hf⟩)
  unfold stepOKCBase at h
  split at h
  · rename_i d opn a c
    split at h
    · rename_i fl'' hcc
      cases h
      exact carryClass_sound hinj hcc
    · split_ifs at h with hs
      cases h
      exact hfb hs rfl
  · rename_i d opn a
    split_ifs at h with h1 h2 h3 h4 h5
    · cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at h1
      obtain ⟨⟨hd, ha⟩, rfl⟩ := h1
      simp only [beq_iff_eq] at h2
      subst h2
      exact decSimC_movReg d a ha (survives_of_injOn hinj hd)
    · cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at h1
      obtain ⟨⟨hd, ha⟩, rfl⟩ := h1
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h3
      obtain ⟨hda, rfl⟩ := h3
      exact decSimC_movReg_elided d a ha hda (survives_of_injOn hinj hd)
    · cases h
      exact hfb h4 rfl
    · cases h
      exact hfb h5 rfl
  · split_ifs at h with hs
    cases h
    exact hfb hs rfl

/-- **The check with flag liveness.** An instruction against its machine instructions,
    from the flags live before (`fl`): a flag-quiet lift instruction (`wideCls`) on names of
    `N`, which keeps the live flags, or an instruction of `stepOKCBase`. The result is the
    flags live afterwards. -/
def stepOKC (π : String → String) (N : List String) (fl : Bool × Bool) (i : LinstrRM)
    (js : List (JInstr 64)) : Option (Bool × Bool) :=
  match wideCls π i js with
  | some (srcs, ws) =>
      if srcs.all N.contains && ws.all N.contains then some fl else stepOKCBase π N fl i js
  | none => stepOKCBase π N fl i js

theorem decSim_of_stepOKC {N : List String} (hinj : InjOn π N) {fl fl' : Bool × Bool}
    {i : LinstrRM} {js : List (JInstr 64)} (h : stepOKC π N fl i js = some fl') :
    DecSim (CCorr π (· ∈ N) Lay frame K zl (fl.1 = true) (fl.2 = true))
      (CCorr π (· ∈ N) Lay frame K False (fl'.1 = true) (fl'.2 = true)) [i] js := by
  unfold stepOKC at h
  split at h
  · rename_i srcs ws hw
    split_ifs at h with hN
    · cases h
      simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hN
      exact wideCls_sound hw hN.1 (survivesL_of_injOn hinj hN.2)
    · exact decSim_of_stepOKCBase hinj h
  · exact decSim_of_stepOKCBase hinj h

/-- A body accepted instruction by instruction, threading the live flags. -/
def bodyOKC (π : String → String) (N : List String) :
    Bool × Bool → List LinstrRM → List (List (JInstr 64)) → Bool
  | _, [], [] => true
  | fl, i :: is, js :: jss =>
      match stepOKC π N fl i js with
      | some fl' => bodyOKC π N fl' is jss
      | none => false
  | _, _, _ => false

/-- **A body simulates its machine instructions**, a carry chain included. -/
theorem decSim_of_bodyOKC {N : List String} (hinj : InjOn π N) :
    ∀ (is : List LinstrRM) (jss : List (List (JInstr 64))) (fl : Bool × Bool) (zl : Prop),
      bodyOKC π N fl is jss = true →
      DecSim (CCorr π (· ∈ N) Lay frame K zl (fl.1 = true) (fl.2 = true))
        (CCorr π (· ∈ N) Lay frame K False False False) is jss.flatten := by
  intro is
  induction is with
  | nil =>
    intro jss fl zl h
    cases jss with
    | nil =>
        exact (DecSim.nil _).weaken (fun _ _ _ h => h)
          (fun _ _ _ h => ⟨h.1.dropZf, fun hf => hf.elim, fun hf => hf.elim⟩)
    | cons _ _ => simp [bodyOKC] at h
  | cons i is ih =>
    intro jss fl zl h
    cases jss with
    | nil => simp [bodyOKC] at h
    | cons js jss =>
      simp only [bodyOKC] at h
      split at h
      · rename_i fl' hs
        rw [List.flatten_cons]
        exact (decSim_of_stepOKC hinj hs).append (ih jss fl' False h)
      · cases h

/-! ## 9. The check on carry chains

An `ADD`, register copy, `ADC` chain is accepted from no live flag; an `ADC` with no live
carry flag, and an `ADC` after a copy through `imul`, are rejected. -/

/- `add`, `mov`, `adc`: the copy keeps the carry flag live. -/
set_option kat.ms 1000 in
#kat bodyOKC id ["a", "b", "c", "d", "e"] (false, false)
  [addI "a" "a" "b", movRI "e" "a", carryI "ADC" "c" "c" "d"]
  [[.add "a" (.reg "b")], [.mov "e" (.reg "a")], [.adc "c" (.reg "d")]]

/- `adc` with no live carry flag. -/
#kat !bodyOKC id ["c", "d"] (false, false) [carryI "ADC" "c" "c" "d"] [[.adc "c" (.reg "d")]]

/- `imul` does not keep the carry flag live. -/
#kat !bodyOKC id ["a", "b", "c", "d"] (false, false)
  [addI "a" "a" "b", binRegI "MUL:64" "a" "a" "b", carryI "ADC" "c" "c" "d"]
  [[.add "a" (.reg "b")], [.imul "a" (.reg "b")], [.adc "c" (.reg "d")]]

/-! ## 10. Word-array memory with flag liveness -/

section Mem

open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecSimTactic

/-- The flag agreement of `CCorr`: the machine carry (overflow) flag holds `b.cf` (`b.of`)
    when `cl` (`ol`) holds. -/
def FlagAg (cl ol : Prop) (sa : AState) (b : LstateM) : Prop :=
  (cl → sa.flags.cf = some b.cf) ∧ (ol → sa.flags.of = some b.of)

/-- `MCorr` with the flag agreement at the live flags `fl`. -/
abbrev MCorrC (E : MemEnv) (base : String → BitVec 64) (rsp : BitVec 64) (s : St) (zl : Prop)
    (fl : Bool × Bool) : AState → LstateM → Bool → Prop :=
  fun sa b zf => MCorr E base rsp s zl sa b zf ∧ FlagAg (fl.1 = true) (fl.2 = true) sa b

/-- A segment simulation carries the flag agreement when neither machine writes a flag. -/
theorem decSim_keepFlags {I J : AState → LstateM → Bool → Prop} {ls : List LinstrRM}
    {js : List (JInstr 64)} (h : DecSim I J ls js)
    (hl : ∀ b zf b' zf', runStraightF ls b zf = some (b', zf') → b'.cf = b.cf ∧ b'.of = b.of)
    (hj : ∀ sa, (aMachine.runBlock sa js).flags = sa.flags) (cl ol : Prop) :
    DecSim (fun sa b zf => I sa b zf ∧ FlagAg cl ol sa b)
      (fun sa b zf => J sa b zf ∧ FlagAg cl ol sa b) ls js := by
  intro sa b zf ⟨hi, hc, ho⟩
  obtain ⟨b', z', hr, hJ⟩ := h sa b zf hi
  obtain ⟨e1, e2⟩ := hl b zf b' z' hr
  refine ⟨b', z', hr, hJ, fun c => ?_, fun o => ?_⟩
  · rw [hj sa, e1]; exact hc c
  · rw [hj sa, e2]; exact ho o

/-- An instruction that is neither a flag writer nor of the carry family keeps the flag
    machine's carry and overflow flags. -/
theorem fstepF_flags_quiet {i : LinstrRM} (ha : aluFlagOp? i = none) (hk : carryArgs? i = none)
    {b b' : LstateM} {zf zf' : Bool} (h : fstepF i b zf = some (b', zf')) :
    b'.cf = b.cf ∧ b'.of = b.of := by
  unfold fstepF at h
  split at h
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h
  · split at h
    · split at h
      · cases h; exact ⟨rfl, rfl⟩
      · cases h
    · obtain ⟨b1, hb1, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      unfold stepMemF at hb1
      split at hb1
      · rename_i b2 hb2
        cases hb1
        rw [withALUFlags_of_none ha]
        exact lsemStepMem_flags hb2
      · simp only [hk] at hb1
        split at hb1
        · exact wideStep_flags _ _ _ hb1
        · cases hb1

/-- The machine instructions that write no flag: moves, the frame load, and the indexed load
    and store. -/
def keepsFlags : JInstr 64 → Bool
  | .mov _ _ => true
  | .loadMem _ _ _ => true
  | .loadMemIdx _ _ _ _ => true
  | .storeMemIdx _ _ _ _ => true
  | _ => false

theorem evalInstrA_flags_of_keeps {j : JInstr 64} (h : keepsFlags j = true) (sa : AState) :
    (evalInstrA sa j).flags = sa.flags := by
  cases j <;> first | rfl | exact absurd h (by simp [keepsFlags])

theorem runBlock_flags_of_keeps :
    ∀ (js : List (JInstr 64)) (sa : AState), js.all keepsFlags = true →
      (aMachine.runBlock sa js).flags = sa.flags
  | [], _, _ => rfl
  | j :: js, sa, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    show (aMachine.runBlock (aMachine.exec sa j) js).flags = _
    rw [runBlock_flags_of_keeps js _ h.2, aMachine_exec, evalInstrA_flags_of_keeps h.1]

theorem keepsFlags_of_machStep {E : MemEnv} {s s' : St} {j : JInstr 64}
    (h : machStep E s j = some s') : keepsFlags j = true := by
  unfold machStep at h
  split at h
  · rfl
  · rfl
  · exact absurd h (by simp)

theorem keepsFlags_of_machRun {E : MemEnv} :
    ∀ (js : List (JInstr 64)) (s s' : St), machRun E s js = some s' → js.all keepsFlags = true
  | [], _, _, _ => rfl
  | j :: js, s, s', h => by
    obtain ⟨s1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨keepsFlags_of_machStep h1, keepsFlags_of_machRun js s1 s' h2⟩

/-- An instruction and its machine instructions write no flag. -/
def quietB (i : LinstrRM) (js : List (JInstr 64)) : Bool :=
  (aluFlagOp? i).isNone && (carryArgs? i).isNone && js.all keepsFlags

variable {E : MemEnv} {base : String → BitVec 64} {rsp : BitVec 64}

/-- The carry family and the flag writers on live registers, the machine instructions
    writing no stack register. -/
def carryStepM (E : MemEnv) (s : St) (fl : Bool × Bool) (i : LinstrRM) (js : List (JInstr 64)) :
    Option (St × (Bool × Bool)) :=
  match i with
  | (.Lopn [.reg d] opn [.reg a, .reg c], .reg none) =>
      if decide (E.sp ∉ js.flatMap dsts) && decide (a ∈ s.1) && decide (c ∈ s.1) then
        (carryOp E.pi fl d opn a c js).map fun fl' =>
          ((liveW E.pi s.1 d (E.pi d), s.2.kill (js.flatMap dsts)), fl')
      else none
  | _ => none

theorem carryStepM_sound {s s' : St} {fl fl' : Bool × Bool} {i : LinstrRM}
    {js : List (JInstr 64)} (h : carryStepM E s fl i js = some (s', fl')) {zl : Prop} :
    DecSim (MCorrC E base rsp s zl fl) (MCorrC E base rsp s' False fl') [i] js := by
  unfold carryStepM at h
  split at h
  · rename_i d opn a c
    split_ifs at h with hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hsp, ha⟩, hc⟩ := hc
    obtain ⟨fl'', hop, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    have hd := DecSim.frame (MachOK E base rsp s)
      (MachOK E base rsp (s.1, s.2.kill (js.flatMap dsts)))
      (carryOp_sound (Lay := regLay E.rs base) (frame := regFrame E.rs rsp) (K := regK E.rs)
        (zl := zl) (L := (· ∈ s.1)) (L' := liveAfter E.pi (· ∈ s.1) d (E.pi d)) hop ha hc
        (fun _ hr => hr))
      (fun sa hm => machOK_block hsp hm)
    exact hd.weaken (fun _ _ _ h => ⟨⟨h.1.1, h.2.1, h.2.2⟩, h.1.2⟩)
      (fun _ _ _ h => ⟨⟨corr_liveW h.1.1, h.2⟩, h.1.2.1, h.1.2.2⟩)
  · exact absurd h (by simp)

/-- The live list after a write of the names `ws`: the written names, and the names of
    `Ls` whose register is the register of no written name. -/
def liveWs (π : String → String) (Ls ws : List String) : List String :=
  ws ++ Ls.filter (fun r => ws.all (fun w => π r != π w))

theorem mem_liveWs {π : String → String} {Ls ws : List String} {r : String} :
    r ∈ liveWs π Ls ws ↔ r ∈ ws ∨ (r ∈ Ls ∧ ∀ w ∈ ws, π r ≠ π w) := by
  simp [liveWs]

/-- The flag-quiet lift classes (`wideCls`) on live registers, the machine instructions
    writing no stack register; the live flags are kept. -/
def wideStepM (E : MemEnv) (s : St) (fl : Bool × Bool) (i : LinstrRM) (js : List (JInstr 64)) :
    Option (St × (Bool × Bool)) :=
  match wideCls E.pi i js with
  | some (srcs, ws) =>
      if decide (E.sp ∉ js.flatMap dsts) && srcs.all (fun r => decide (r ∈ s.1)) then
        some ((liveWs E.pi s.1 ws, s.2.kill (js.flatMap dsts)), fl)
      else none
  | none => none

theorem wideStepM_sound {s s' : St} {fl fl' : Bool × Bool} {i : LinstrRM}
    {js : List (JInstr 64)} (h : wideStepM E s fl i js = some (s', fl')) {zl : Prop} :
    DecSim (MCorrC E base rsp s zl fl) (MCorrC E base rsp s' False fl') [i] js := by
  unfold wideStepM at h
  split at h
  · rename_i srcs ws hw
    split_ifs at h with hc
    cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
    obtain ⟨hsp, hs⟩ := hc
    have hd := DecSim.frame (MachOK E base rsp s)
      (MachOK E base rsp (s.1, s.2.kill (js.flatMap dsts)))
      (wideCls_sound (Lay := regLay E.rs base) (frame := regFrame E.rs rsp) (K := regK E.rs)
        (zl := zl) (cl := fl.1 = true) (ol := fl.2 = true) (L := (· ∈ s.1))
        (L' := (· ∈ liveWs E.pi s.1 ws)) hw hs (fun _ hr => mem_liveWs.mp hr))
      (fun sa hm => machOK_block hsp hm)
    exact hd.weaken (fun _ _ _ h => ⟨⟨h.1.1, h.2.1, h.2.2⟩, h.1.2⟩)
      (fun _ _ _ h => ⟨⟨h.1.1, h.2⟩, h.1.2.1, h.1.2.2⟩)
  · exact absurd h (by simp)

/-- **The class check with flag liveness on one instruction.** A carry-family instruction or
    a flag writer on live registers (`carryStepM`); a flag-quiet lift instruction on live
    registers (`wideStepM`), which keeps the live flags; otherwise a class of `coreStep`,
    which keeps the live flags when neither machine writes a flag and leaves none live
    otherwise. -/
def coreStepC (E : MemEnv) (s : St) (fl : Bool × Bool) (i : LinstrRM) (js : List (JInstr 64)) :
    Option (St × (Bool × Bool)) :=
  match carryStepM E s fl i js with
  | some r => some r
  | none =>
      match wideStepM E s fl i js with
      | some r => some r
      | none => (coreStep E s i js).map fun s' => (s', if quietB i js then fl else (false, false))

theorem coreStepC_sound (hsep : MemSep E.rs base rsp) {s s' : St} {fl fl' : Bool × Bool}
    {i : LinstrRM} {js : List (JInstr 64)} (h : coreStepC E s fl i js = some (s', fl'))
    {zl : Prop} :
    DecSim (MCorrC E base rsp s zl fl) (MCorrC E base rsp s' False fl') [i] js := by
  unfold coreStepC at h
  split at h
  · rename_i r hr
    cases h
    exact carryStepM_sound hr
  split at h
  · rename_i r hr
    cases h
    exact wideStepM_sound hr
  · obtain ⟨s'', hc, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    have hd := coreStep_sound hsep hc (zl := zl)
    split
    · rename_i hq
      simp only [quietB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hq
      obtain ⟨⟨ha, hk⟩, hj⟩ := hq
      exact decSim_keepFlags hd (fun b zf b' zf' hr => fstepF_flags_quiet ha hk
        (by rwa [runStraightF_singleton] at hr)) (fun sa => runBlock_flags_of_keeps js sa hj) _ _
    · exact hd.weaken (fun _ _ _ h => h.1)
        (fun _ _ _ h => ⟨h, fun hf => by simp at hf, fun hf => by simp at hf⟩)

/-- The machine-only classes keep the flag agreement. -/
theorem machStepC_sound {s s' : St} {j : JInstr 64} (h : machStep E s j = some s') {zl : Prop}
    (fl : Bool × Bool) :
    DecSim (MCorrC E base rsp s zl fl) (MCorrC E base rsp s' zl fl) [] [j] :=
  decSim_keepFlags (machStep_sound h) (fun _ _ _ _ hr => by cases hr; exact ⟨rfl, rfl⟩)
    (fun sa => runBlock_flags_of_keeps [j] sa (by simp [keepsFlags_of_machStep h])) _ _

theorem machRunC_sound {js : List (JInstr 64)} {s s' : St} (h : machRun E s js = some s')
    {zl : Prop} (fl : Bool × Bool) :
    DecSim (MCorrC E base rsp s zl fl) (MCorrC E base rsp s' zl fl) [] js :=
  decSim_keepFlags (machRun_sound js s s' zl h)
    (fun _ _ _ _ hr => by cases hr; exact ⟨rfl, rfl⟩) (fun sa => runBlock_flags_of_keeps js sa (keepsFlags_of_machRun js s s' h)) _ _

/-- One flag-machine instruction against a group of machine instructions, with flag
    liveness: a prefix of machine-only instructions, then the instructions of one class. -/
def grpStepC (E : MemEnv) (i : LinstrRM) :
    St → Bool × Bool → List (JInstr 64) → Option (St × (Bool × Bool))
  | s, fl, [] => coreStepC E s fl i []
  | s, fl, j :: js =>
      match coreStepC E s fl i (j :: js) with
      | some r => some r
      | none => (machStep E s j).bind fun s1 => grpStepC E i s1 fl js

theorem grpStepC_sound (hsep : MemSep E.rs base rsp) (i : LinstrRM) :
    ∀ (js : List (JInstr 64)) (s s' : St) (fl fl' : Bool × Bool) (zl : Prop),
      grpStepC E i s fl js = some (s', fl') →
      DecSim (MCorrC E base rsp s zl fl) (MCorrC E base rsp s' False fl') [i] js := by
  intro js
  induction js with
  | nil => intro s s' fl fl' zl h; exact coreStepC_sound hsep h
  | cons j js ih =>
    intro s s' fl fl' zl h
    simp only [grpStepC] at h
    split at h
    · rename_i r hc
      cases h
      exact coreStepC_sound hsep hc
    · obtain ⟨s1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      exact DecSim.mach_cons (machStepC_sound h1 fl) (ih s1 s' fl fl' zl h2)

/-- **The check on a body with flag liveness.** `mbodyOK` with the live flags threaded
    through the groups; returns the final state and live flags. -/
def mbodyOKC (E : MemEnv) (fin : St → Bool) :
    St → Bool × Bool → List LinstrRM → List (JInstr 64) → Option (St × (Bool × Bool))
  | s, fl, [], js =>
      match machRun E s js with
      | some s' => if fin s' then some (s', fl) else none
      | none => none
  | s, fl, i :: is, js => (List.range (js.length + 1)).findSome? fun k =>
      (grpStepC E i s fl (js.take k)).bind fun r => mbodyOKC E fin r.1 r.2 is (js.drop k)

/-- **An accepted body simulates its machine instructions** with the flag agreement at the
    returned live flags, and its final state satisfies `fin`. -/
theorem mbodyOKC_sound (hsep : MemSep E.rs base rsp) (fin : St → Bool) :
    ∀ (is : List LinstrRM) (s s' : St) (fl fl' : Bool × Bool) (js : List (JInstr 64))
      (zl : Prop), mbodyOKC E fin s fl is js = some (s', fl') →
      fin s' = true
        ∧ DecSim (MCorrC E base rsp s zl fl) (MCorrC E base rsp s' False fl') is js := by
  intro is
  induction is with
  | nil =>
    intro s s' fl fl' js zl h
    simp only [mbodyOKC] at h
    split at h
    · rename_i s'' hm
      split at h
      · rename_i hf
        cases h
        exact ⟨hf, (machRunC_sound hm fl).weaken (fun _ _ _ h => h)
          (fun _ _ _ h => ⟨⟨h.1.1.mono (fun _ hr => hr) (fun hf => hf.elim) (fun _ _ h => h),
            h.1.2⟩, h.2⟩)⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  | cons i is ih =>
    intro s s' fl fl' js zl h
    simp only [mbodyOKC] at h
    obtain ⟨k, -, hk⟩ := List.exists_of_findSome?_eq_some h
    obtain ⟨r, h1, h2⟩ := Option.bind_eq_some_iff.mp hk
    obtain ⟨hf, h2'⟩ := ih r.1 s' r.2 fl' (js.drop k) False h2
    have := (grpStepC_sound hsep i (js.take k) s r.1 fl r.2 zl h1).append h2'
    rw [List.take_append_drop] at this
    exact ⟨hf, this⟩

/-- The live flags `fl0` of a loop head are live in `fl`. -/
def flagsFin (fl0 fl : Bool × Bool) : Bool := (!fl0.1 || fl.1) && (!fl0.2 || fl.2)

/-- **The check on a loop body with flag liveness.** The body is accepted from the live list
    `L0`, the abstract state `a0` and the live flags `fl0`, with a final live list containing
    `L0` and final live flags containing `fl0`. -/
def loopOKC (E : MemEnv) (L0 : List String) (a0 : Abs) (fl0 : Bool × Bool)
    (is : List LinstrRM) (js : List (JInstr 64)) : Bool :=
  match mbodyOKC E (liveFin L0) (L0, a0) fl0 is js with
  | some (_, fl) => flagsFin fl0 fl
  | none => false

/-- **An accepted loop body simulates its machine instructions** with the flag agreement,
    from the live list `L0`, the facts `a0` and the live flags `fl0` back to `L0` with no
    machine facts and the live flags `fl0`. -/
theorem decSim_of_loopOKC (hsep : MemSep E.rs base rsp) {L0 : List String} {a0 : Abs}
    {fl0 : Bool × Bool} {is : List LinstrRM} {js : List (JInstr 64)}
    (h : loopOKC E L0 a0 fl0 is js = true) (zl : Prop) :
    DecSim (MCorrC E base rsp (L0, a0) zl fl0) (MCorrC E base rsp (L0, Abs.empty) False fl0)
      is js := by
  unfold loopOKC at h
  split at h
  · rename_i s' fl hs
    obtain ⟨hf, hd⟩ := mbodyOKC_sound hsep (liveFin L0) is _ s' fl0 fl js zl hs
    have hL : ∀ r ∈ L0, r ∈ s'.1 := by simpa [liveFin] using hf
    simp only [flagsFin, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, h2⟩ := h
    exact hd.weaken (fun _ _ _ h => h)
      (fun sa _ _ h => ⟨⟨h.1.1.mono (fun r hr => hL r hr) id (fun _ _ h => h),
        h.1.2.1, Abs.holds_empty base E.nb sa⟩,
        fun hc => h.2.1 (h1.resolve_left (by simp [hc])),
        fun ho => h.2.2 (h2.resolve_left (by simp [ho]))⟩)
  · exact absurd h (by simp)

/- An `ADD`, register copy, `ADC` chain in one machine block, with no region. -/
set_option kat.ms 1000 in
#kat (mbodyOKC ⟨id, "%rsp", [], 8⟩ (fun _ => true) (["a", "b", "c", "d", "e"], Abs.empty)
  (false, false) [addI "a" "a" "b", movRI "e" "a", carryI "ADC" "c" "c" "d"]
  [.add "a" (.reg "b"), .mov "e" (.reg "a"), .adc "c" (.reg "d")]).isSome

/- `imul` does not keep the carry flag live. -/
#kat (mbodyOKC ⟨id, "%rsp", [], 8⟩ (fun _ => true) (["a", "b", "c", "d"], Abs.empty)
  (false, false) [addI "a" "a" "b", binRegI "MUL:64" "a" "a" "b", carryI "ADC" "c" "c" "d"]
  [.add "a" (.reg "b"), .imul "a" (.reg "b"), .adc "c" (.reg "d")]).isNone

end Mem

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeCarry
