/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak

@[expose] public section

set_option autoImplicit false

/-!
# The leakage of the carry add with a slot carry-in and of the select with a slot false value

The carry add `ADCX:64 D, A, S, C` whose carry-in `C` is a frame slot is printed
(`DecodePrintedAddrW.SArm.adcxc`) as the save of a scratch register in the red-zone word, the
reload of the frame word of `C` into the scratch, `bt $0` of the scratch and the add: for a
register destination, the restore of the scratch, the copy of `A` into `D` and `adcx`; for a
slot destination, the add in the scratch, the store into the slot of `D` and the restore.

Under the regime `doitm` the decoded instructions emit no `vt` event. Their memory events are
the frame addresses of the slot operands that the address machine accesses (`instrLeakA`), in
the order the machine instructions access them, with the red-zone word `redW rsp` accessed by
the save and the restore. Every address is a frame address below the stack register, so the
events are a function of the stack register, the frame and the operand names.

The select `CMOV:64 D, [C, A, B]` whose false value `B` is a frame slot
(`DecodePrintedAddrW.vfPieces`) is printed as the load of the frame word of `B` into `D`,
`test C, C` and `cmovne` from a register or from the frame word of a slot `A`; its events are
the frame addresses of `B` and of a slot `A`.

## Main results

* `blockLeakA_append`: the leakage of a block splits along an append.
* `instrLeakA_adcxc`: the events of the add on the address machine: the frame addresses of the
  slot carry-in, the slot word sources and the slot destination.
* `SArm.leak_adcxc`: the events of the decoded instructions: the red-zone word, the carry-in,
  then the word sources and the destination with the second red-zone access, in machine order.
* `instrLeakA_cmovSlotF`, `leak_cmovSlotF`: the events of the select with a slot false value on
  the address machine (true value, then false value) and of its decoded instructions (false
  value, then true value).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrWLeak

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT (blockLeakA opLeak resolveEv)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime (instrLeak)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrLeakPhys
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak DoitRegime X86Mnem)

/-- **The leakage of a block splits along an append**, the second part from the state the
    first part ends in. -/
theorem blockLeakA_append (r : DoitRegime) :
    ∀ (sa : AState) (xs ys : List (JInstr 64)),
      blockLeakA r sa (xs ++ ys) = blockLeakA r sa xs ++ blockLeakA r (aMachine.runBlock sa xs) ys
  | _, [], _ => rfl
  | sa, i :: is, ys => by
    simp only [List.cons_append, blockLeakA, List.append_assoc]
    rw [blockLeakA_append r (evalInstrA sa i) is ys]
    rfl

/-- The events of a name's frame address: one event for a frame slot, none otherwise. -/
def fEv (P : Params) (rsp : BitVec 64) (x : String) : List CTLeak :=
  (frameP P rsp x).toList.map evA

/-- The frame events of a slot at its offset. -/
theorem fEv_slot {P : Params} {rsp : BitVec 64} {x : String} (hk : kOk P x = true)
    (hs : isSpillOrQsave x = true) :
    fEv P rsp x = [evA (rsp + BitVec.ofInt 64 (slotOff P x))] := by
  rcases kOk_cases hk with hg | ⟨off, hoff, -, -⟩
  · simp [(gpFacts hg).notSlot] at hs
  · simp [fEv, frameP, hoff, slotOff]

/-- A general-purpose name has no frame events. -/
theorem fEv_gp {P : Params} {rsp : BitVec 64} {x : String} (hg : gpOk x = true) :
    fEv P rsp x = [] := by
  simp [fEv, frameP_gp hg]

/-- The frame events of a well-placed operand: none for a general-purpose name. -/
theorem fEv_of_not_slot {P : Params} {rsp : BitVec 64} {x : String} (hk : kOk P x = true)
    (hs : isSpillOrQsave x = false) : fEv P rsp x = [] := by
  rcases kOk_cases hk with hg | ⟨off, hoff, -, -⟩
  · exact fEv_gp hg
  · simp [(slot_facts hoff).1] at hs

/-- The events of a `%rsp`-relative load or store at `off` are its address. -/
theorem opLeak_loadRsp (sa : AState) (d : String) (off : Int) :
    opLeak .doitm sa (.loadMem d "%rsp" off) = [evA (sa.regs "%rsp" + BitVec.ofInt 64 off)] := by
  simp [opLeak, instrLeak, resolveEv, JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing, evA]

theorem opLeak_storeRsp (sa : AState) (x : String) (off : Int) :
    opLeak .doitm sa (.storeMem "%rsp" off (.reg x))
      = [evA (sa.regs "%rsp" + BitVec.ofInt 64 off)] := by
  simp [opLeak, instrLeak, resolveEv, JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing, evA]

/-- The test of a slot carry-in accesses the red-zone word and the frame word of `C`. -/
theorem leak_cPre (P : Params) (rsp : BitVec 64) (C : String) (acc : Nat) (sa : AState)
    (hsp : sa.regs "%rsp" = rsp) :
    blockLeakA .doitm sa ((cPre P C acc).map Prod.snd)
      = [evA (redW rsp), evA (rsp + BitVec.ofInt 64 (slotOff P C))] := by
  obtain ⟨r1, -⟩ := evalInstrA_storeMem_eq sa "%rsp" (SailX86Decoder.regName acc) cmovRedZone
  simp only [cPre, List.map_cons, List.map_nil, blockLeakA, opLeak_storeRsp, opLeak_loadRsp, r1,
    hsp, List.append_nil, List.cons_append, List.nil_append]
  simp [opLeak, instrLeak, JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing, redW]

/-- The copy of a well-placed operand `A` into the accumulator accesses the frame word of a
    slot `A`. -/
theorem leak_sMv (P : Params) (rsp : BitVec 64) (D A : String) (acc : Nat) (sa : AState)
    (hsp : sa.regs "%rsp" = rsp) (hA : kOk P A = true) :
    blockLeakA .doitm sa ((sMv P D A acc).map Prod.snd) = fEv P rsp A := by
  unfold sMv
  split
  · rename_i hs
    simp [blockLeakA, opLeak_loadRsp, hsp, fEv_slot hA hs]
  · rename_i hs
    rw [fEv_of_not_slot hA (by simpa using hs)]
    split
    · rfl
    · simp [blockLeakA, opLeak, instrLeak, JInstr.mnem, DoitRegime.leaksOperands,
        X86Mnem.timing]

/-- The add of a well-placed operand `S` into the accumulator accesses the frame word of a
    slot `S`. -/
theorem leak_sAd (P : Params) (rsp : BitVec 64) (S : String) (acc : Nat) (sa : AState)
    (hsp : sa.regs "%rsp" = rsp) (hS : kOk P S = true) :
    blockLeakA .doitm sa ((sAd P S acc).map Prod.snd) = fEv P rsp S := by
  unfold sAd
  split
  · rename_i hs
    simp [blockLeakA, opLeak, instrLeak, resolveEv, JInstr.mnem, DoitRegime.leaksOperands,
      X86Mnem.timing, hsp, fEv_slot hS hs, evA]
  · rename_i hs
    rw [fEv_of_not_slot hS (by simpa using hs)]
    simp [blockLeakA, opLeak, instrLeak, JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing]

/-- **The events of the add with a slot carry-in on the address machine**: the frame addresses
    of the carry-in, the slot word sources and the slot destination. -/
theorem instrLeakA_adcxc (P : Params) (rsp : BitVec 64) (D A S C : String)
    (h : (SArm.adcxc D A S C).ok P = true) (s : LstateA) :
    instrLeakA (frameP P rsp) ((SArm.adcxc D A S C).instr, .reg none) s
      = fEv P rsp C ++ fEv P rsp A ++ fEv P rsp S ++ fEv P rsp D := by
  obtain ⟨hCs, hC, -, -, -, -⟩ := adcxc_facts h
  have hfC := kOk_frame hC hCs rsp
  obtain ⟨aC, haC⟩ := Option.isSome_iff_exists.mp hfC
  simp [instrLeakA, SArm.instr, slotMov?, slotCmp?, cellA?, slotCarry?, haC, fEv]

/-- **The events of the decoded instructions of the add with a slot carry-in.** Under `doitm`,
    from a machine state whose stack register holds `rsp`: the save in the red-zone word, the
    reload of the carry-in word, then, for a slot destination, the slot word sources, the store
    into the destination and the restore from the red-zone word, and, for a register
    destination, the restore followed by the slot word sources. -/
theorem SArm.leak_adcxc (P : Params) (rsp : BitVec 64) (D A S C : String)
    (h : (SArm.adcxc D A S C).ok P = true) (sa : AState) (hsp : sa.regs "%rsp" = rsp) :
    blockLeakA .doitm sa ((SArm.adcxc D A S C).js P)
      = evA (redW rsp) :: fEv P rsp C
        ++ (if isSpillOrQsave D then
              fEv P rsp A ++ fEv P rsp S ++ fEv P rsp D ++ [evA (redW rsp)]
            else evA (redW rsp) :: (fEv P rsp A ++ fEv P rsp S)) := by
  obtain ⟨hCs, hC, hD, hA, hS, -⟩ := adcxc_facts h
  obtain ⟨hRg, -, -, -⟩ := scratchS_spec A S C
  set acc := gpNumU (scratchS A S C) with hacc
  set R := SailX86Decoder.regName acc with hR
  have hRsp : R ≠ "%rsp" := (gpFacts hRg).physNe
  have hdC := kOk_sep hC hCs rsp
  obtain ⟨r3, -, -⟩ := run_cPre P rsp C acc sa hsp hdC
  have hsp3 : (aMachine.runBlock sa ((cPre P C acc).map Prod.snd)).regs "%rsp" = rsp := by
    rw [r3, ite_eq_right (Ne.symm hRsp), hsp]
  rw [fEv_slot hC hCs]
  by_cases hDs : isSpillOrQsave D = true
  · have hjs : (SArm.adcxc D A S C).js P
        = (cPre P C acc).map Prod.snd ++ ((sMv P D A acc).map Prod.snd
            ++ ((sAd P S acc).map Prod.snd
            ++ [.storeMem "%rsp" (slotOff P D) (.reg R), .loadMem R "%rsp" cmovRedZone])) := by
      simp [SArm.js, SArm.pieces, hDs, List.map_append, cRst, hR, hacc]
    set sa3 := aMachine.runBlock sa ((cPre P C acc).map Prod.snd)
    have hlay : isSpillOrQsave A = true ∨ ¬ (A = D ∧ acc = gpNumU D) := by
      by_cases hAs : isSpillOrQsave A = true
      · exact Or.inl hAs
      · right; rintro ⟨rfl, -⟩; exact hAs hDs
    obtain ⟨r4, -, -⟩ := run_sMv P rsp D A acc sa3 hsp3 hlay
    set sa4 := aMachine.runBlock sa3 ((sMv P D A acc).map Prod.snd)
    have hsp4 : sa4.regs "%rsp" = rsp := by rw [r4, ite_eq_right (Ne.symm hRsp), hsp3]
    obtain ⟨r5, -, -⟩ := run_sAd P rsp S acc sa4 hsp4
    set sa5 := aMachine.runBlock sa4 ((sAd P S acc).map Prod.snd)
    have hsp5 : sa5.regs "%rsp" = rsp := by rw [r5, ite_eq_right (Ne.symm hRsp), hsp4]
    obtain ⟨r6, -⟩ := evalInstrA_storeMem_eq sa5 "%rsp" R (slotOff P D)
    rw [hjs, blockLeakA_append, blockLeakA_append, blockLeakA_append, leak_cPre P rsp C acc sa hsp,
      leak_sMv P rsp D A acc sa3 hsp3 hA, leak_sAd P rsp S acc sa4 hsp4 hS, ite_eq_left hDs,
      fEv_slot hD hDs]
    change _ ++ (_ ++ (_ ++ blockLeakA .doitm sa5 _)) = _
    simp only [blockLeakA, opLeak_storeRsp, opLeak_loadRsp, r6, hsp5]
    simp [redW]
  · have hjs : (SArm.adcxc D A S C).js P
        = (cPre P C acc).map Prod.snd ++ ([.loadMem R "%rsp" cmovRedZone]
            ++ ((sMv P D A (gpNumU D)).map Prod.snd ++ (sAd P S (gpNumU D)).map Prod.snd)) := by
      simp [SArm.js, SArm.pieces, hDs, List.map_append, cRst, hR, hacc]
    have hDg : gpOk D = true := by
      rcases kOk_cases hD with hg | ⟨off, hoff, -, -⟩
      · exact hg
      · exact absurd (slot_facts hoff).1 hDs
    obtain ⟨r4, -, -⟩ := run_cTest P rsp C acc sa hsp hRsp hdC
    set sa4 := aMachine.runBlock sa ((cPre P C acc).map Prod.snd ++ [(cRst acc).2]) with hsa4
    have hsp4 : sa4.regs "%rsp" = rsp := by rw [r4, hsp]
    have hsa4' : aMachine.runBlock (aMachine.runBlock sa ((cPre P C acc).map Prod.snd))
        [.loadMem R "%rsp" cmovRedZone] = sa4 := by
      rw [hsa4, RInstrSemantics.Machine.runBlock_append]; rfl
    have hpD : SailX86Decoder.regName (gpNumU D) = phys D := rfl
    set sa5 := aMachine.runBlock sa4 ((sMv P D A (gpNumU D)).map Prod.snd) with hsa5
    have hsp5 : sa5.regs "%rsp" = rsp := by
      by_cases hlay : isSpillOrQsave A = true ∨ ¬ (A = D ∧ gpNumU D = gpNumU D)
      · obtain ⟨hr, -, -⟩ := run_sMv P rsp D A (gpNumU D) sa4 hsp4 hlay
        rw [hr, hpD, ite_eq_right (fun e => (gpFacts hDg).physNe e.symm), hsp4]
      · simp only [not_or, Bool.not_eq_true, not_not] at hlay
        obtain ⟨hAs, rfl, -⟩ := hlay
        have he : sMv P A A (gpNumU A) = [] := by simp [sMv, hAs]
        rw [hsa5, he]
        exact hsp4
    rw [hjs, blockLeakA_append, blockLeakA_append, blockLeakA_append, hsa4',
      leak_cPre P rsp C acc sa hsp, leak_sMv P rsp D A (gpNumU D) sa4 hsp4 hA,
      ← hsa5, leak_sAd P rsp S (gpNumU D) sa5 hsp5 hS, ite_eq_right hDs]
    simp only [blockLeakA, opLeak_loadRsp, hsp3]
    simp [redW]

/-- **The events of the select with a slot false value on the address machine**: the frame
    addresses of a slot true value and of the false value. -/
theorem instrLeakA_cmovSlotF (P : Params) (rsp : BitVec 64) (D C A B : String)
    (h : vfOk P D C A B = true) (s : LstateA) :
    instrLeakA (frameP P rsp) (.Lopn [.reg D] "CMOV:64" [.reg C, .reg A, .reg B], .reg none) s
      = fEv P rsp A ++ fEv P rsp B := by
  simp only [vfOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hD, -⟩, hBs⟩, hBk⟩, -⟩, -⟩, -⟩, -⟩ := h
  obtain ⟨aB, haB⟩ := Option.isSome_iff_exists.mp (kOk_frame hBk hBs rsp)
  simp [instrLeakA, slotMov?, slotCmp?, cellA?, slotCarry?, slotImm?, slotCmov?, haB, fEv,
    frameP_gp hD]

/-- **The events of the decoded instructions of the select with a slot false value.** Under
    `doitm`, from a machine state whose stack register holds `rsp`: the load of the frame word of
    the false value, then the frame word of a slot true value. -/
theorem leak_cmovSlotF (P : Params) (rsp : BitVec 64) (D C A B : String)
    (h : vfOk P D C A B = true) (sa : AState) (hsp : sa.regs "%rsp" = rsp) :
    blockLeakA .doitm sa ((vfPieces P D C A B).map Prod.snd) = fEv P rsp B ++ fEv P rsp A := by
  simp only [vfOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hD, -⟩, hBs⟩, hBk⟩, hAk⟩, -⟩, -⟩, -⟩ := h
  have hRsp : phys D ≠ "%rsp" := (gpFacts hD).physNe
  obtain ⟨r1, -⟩ := evalInstrA_loadMem_eq sa (phys D) "%rsp" (slotOff P B)
  set sa1 := evalInstrA sa (.loadMem (phys D) "%rsp" (slotOff P B))
  have hsp1 : sa1.regs "%rsp" = rsp := by rw [r1, ite_eq_right (Ne.symm hRsp), hsp]
  have hsp2 : (evalInstrA sa1 (.test (phys C) (.reg (phys C)))).regs "%rsp" = rsp := by
    simpa [evalInstrA, evalInstr, AState.view, JState.writeB5] using hsp1
  rw [fEv_slot hBk hBs]
  cases hAs : isSpillOrQsave A with
  | true =>
    rw [fEv_slot hAk hAs]
    simp only [vfPieces, vfCm, hAs, ite_true, List.map_cons, List.map_nil, blockLeakA,
      opLeak_loadRsp, hsp]
    simp [opLeak, instrLeak, resolveEv, JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing,
      evA, hsp2, sa1]
  | false =>
    rw [fEv_of_not_slot hAk hAs]
    simp only [vfPieces, vfCm, hAs, Bool.false_eq_true, ite_false, List.map_cons, List.map_nil,
      blockLeakA, opLeak_loadRsp, hsp]
    simp [opLeak, instrLeak, JInstr.mnem, DoitRegime.leaksOperands, X86Mnem.timing]

/-- **A width-carrying cast between general-purpose names emits no event on the address
    machine.** -/
theorem instrLeakA_castW (P : Params) (rsp : BitVec 64) (o D A : String) (m w : Nat)
    (hk : castMovBits o = some m) (_hD : gpOk D = true) (_hA : gpOk A = true) (s : LstateA) :
    instrLeakA (frameP P rsp) (.Lopn [.reg D] o [.reg A], .reg (some w)) s = [] := by
  rcases castMovBits_cases hk with ⟨-, rfl | rfl | rfl | rfl | rfl⟩ | ⟨-, rfl | rfl | rfl⟩ <;>
    simp (config := { decide := true }) [instrLeakA, slotMov?, slotCmp?, cellA?, slotCarry?,
      slotImm?, slotCmov?]

/-- **The decoded instructions of a width-carrying cast emit no event** under `doitm`: the
    zero-extending register move accesses no memory and is no operand-leaking mnemonic. -/
theorem leak_castW (m : Nat) (D A : String) (sa : AState) :
    blockLeakA .doitm sa ((castPieces m D A).map Prod.snd) = [] := by
  simp [castPieces, blockLeakA, opLeak, instrLeak, JInstr.mnem, DoitRegime.leaksOperands,
    X86Mnem.timing]

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrWLeak
