/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites

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
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (lsemStepMem_of_carryArgs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep

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
  rw [fstepF_binRegI opn base d a c hstrip hcmp hmul hcarry b zf _ hva, hvc, Option.bind_some,
    hf, Option.map_some]
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

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeCarry
