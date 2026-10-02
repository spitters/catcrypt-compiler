/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr

@[expose] public section

set_option autoImplicit false

/-!
# The address-machine correspondence with one-bit carry registers

`DecodePrintedAddr.ACorr` relates every general-purpose name of the address machine to its
machine register at width `64`. The carry chain of the address machine keeps a carry in a
name at width `1` (`ADCXHI` writes `carryOutBit`, `ADCX` reads its carry-in at width `1`),
while the machine keeps it in a 64-bit register as `0` or `1`. `ACorrW` relates such a name
to the zero-extension of its bit.

An arm of `DecodePrintedAddr` reads no one-bit name (`WideAt`). Its step from a state related
by `ACorrW` is the step from the state with every one-bit general-purpose name widened
(`widenS`), which `ACorr` relates, up to the congruence `JasminLsemAddrCongr.fstepA_congr`
in the names the instruction reads (`AArm.simW`).

The carry arms (`CArm`) are the add `ADCX:64 D, A, S, C`, printed `bt $0, C; adcx S, D` after
the copy of `A` into `D`, and its carry-out binding `ADCXHI:64 O, A, S, C`, printed `setc O`;
the binding reads the carry flag the add leaves, which the run threads to it (`CarryAt`). The
cell arms (`MArm`) are the whole-word load and store of a cell `mem.B.off`, printed
`mov off(%B)`. The class `printedAddrWB` adds both to the bodies of `DecodePrintedCFG`.

## Main definitions

* `widenS` — the address state with each one-bit general-purpose name zero-extended to `64`.
* `ACorrW` — the correspondence with one-bit names.
* `WideAt` — no general-purpose name an instruction reads is a one-bit name.
* `CArm`, `MArm` — the carry and cell arms.
* `printedAddrWB`, `SafeW` — the covered bodies and the run safety they are simulated under.

## Main results

* `ACorr.toW`, `ACorrW.widen`: `ACorr` is the case of `ACorrW` without one-bit names, and an
  `ACorrW` state widens to an `ACorr` state.
* `AArm.simW`: an arm of `DecodePrintedAddr` steps from `ACorrW` to `ACorrW`.
* `CArm.bytes`, `sim_adcx`, `sim_adcxhi`, `MArm.bytes`, `sim_ldm`, `sim_stm`: the bytes and
  the simulations of the carry and cell arms.
* `run_simW`, `printedAddr_simW`: the decoded bytes of a body in `printedAddrWB` simulate its
  run on the address machine.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr

/-! ## 1. The correspondence -/

/-- The cell of name `r` widened: a one-bit value of a general-purpose name zero-extended to
    width `64`, any other cell unchanged. -/
def widenCell (r : String) (c : Σ w, BitVec w) : Σ w, BitVec w :=
  if (gpOk r && c.1 == 1) = true then ⟨64, c.2.setWidth 64⟩ else c

/-- The address state with every one-bit general-purpose name zero-extended to width `64`. -/
def widenS (s : LstateA) : LstateA :=
  { s with reg := { s.reg with lvm := fun r => widenCell r (s.reg.lvm r) } }

/-- **The correspondence with one-bit names.** Each general-purpose name holds the value of
    its machine register at width `64`, or a bit whose zero-extension the machine register
    holds; the stack register holds `rsp`; the memories agree outside the red-zone word. -/
structure ACorrW (rsp : BitVec 64) (sa : AState) (s : LstateA) : Prop where
  /-- A general-purpose name holds its machine register, or a bit it zero-extends. -/
  regs : ∀ r, gpOk r = true → s.reg.getW r 64 = some (sa.regs (phys r))
    ∨ ∃ b : BitVec 1, s.reg.lvm r = ⟨1, b⟩ ∧ sa.regs (phys r) = b.setWidth 64
  /-- The stack register holds `rsp`. -/
  sp : sa.regs "%rsp" = rsp
  /-- The memories agree outside the red-zone word. -/
  mem : ∀ x, ¬ InRange8 (redW rsp) x → s.mem x = sa.mem x

theorem ACorr.toW {rsp : BitVec 64} {sa : AState} {s : LstateA} (h : ACorr rsp sa s) :
    ACorrW rsp sa s :=
  ⟨fun r hr => Or.inl (h.regs r hr), h.sp, h.mem⟩

theorem lvm_of_getW {s : LstateN} {r : String} {v : BitVec 64} (h : s.getW r 64 = some v) :
    s.lvm r = ⟨64, v⟩ :=
  getW_eq_some_iff.1 h

theorem ACorrW.widen {rsp : BitVec 64} {sa : AState} {s : LstateA} (h : ACorrW rsp sa s) :
    ACorr rsp sa (widenS s) where
  regs r hr := by
    rcases h.regs r hr with hg | ⟨b, hb, hm⟩
    · have hl := lvm_of_getW hg
      rw [getW_eq_some_iff]
      simp [widenS, widenCell, hl]
    · rw [getW_eq_some_iff]
      show widenCell r (s.reg.lvm r) = _
      rw [hb]
      simp [widenCell, hr, hm]
  sp := h.sp
  mem := h.mem

/-- No general-purpose name the instruction reads holds a one-bit value. -/
def WideAt (s : LstateA) (i : LinstrR) : Prop :=
  ∀ r, readsI i r → gpOk r = true → (s.reg.lvm r).1 ≠ 1

theorem aagree_widen {s : LstateA} {i : LinstrR} (hw : WideAt s i) :
    AAgree (readsI i) s (widenS s) := by
  refine ⟨⟨rfl, fun r hr => ?_⟩, rfl, rfl, rfl⟩
  show s.reg.lvm r = widenCell r (s.reg.lvm r)
  by_cases hg : gpOk r = true
  · have h1 := hw r hr hg
    simp [widenCell, h1]
  · simp [widenCell, hg]

/-! ## 2. The arms of `DecodePrintedAddr` -/

/-- A read name keeps its 64-bit value under widening. -/
theorem getW_widen {s : LstateA} {i : LinstrR} (hw : WideAt s i) {r : String}
    (hr : readsI i r) (w : Nat) : (widenS s).reg.getW r w = s.reg.getW r w :=
  ((getW_congr (aagree_widen hw).1 hr w)).symm

/-- **An arm of `DecodePrintedAddr` on the correspondence with one-bit names.** From
    `ACorrW`, an arm that reads no one-bit name and whose indexed load is safe steps, if the
    address machine steps, to a state that `ACorrW` relates to the machine run of the arm's
    decoded instructions; after a compare the machine zero flag is the flag of the address
    machine. -/
theorem AArm.simW (P : Params) (rsp : BitVec 64) (a : AArm) (h : a.ok P = true)
    (sa : AState) (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s) (hw : WideAt s a.li.fst)
    (hsafe : a.LoadSafe rsp s) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) a.li s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa (a.js P)) s'
      ∧ (cmpArmB a = true → (aMachine.runBlock sa (a.js P)).flags.zf.getD false = zf') := by
  have hsafe' : a.LoadSafe rsp (widenS s) := by
    cases a with
    | ldx D B I =>
      intro p vi hp hvi
      have hB : readsI (AArm.ldx D B I).li.fst B := by
        show readsI (.Lopn [.reg D] "LOADIDX" [.arrIdx B I 8]) B
        exact base_reads (List.mem_singleton_self _)
      have hI : readsI (AArm.ldx D B I).li.fst I := by
        show readsI (.Lopn [.reg D] "LOADIDX" [.arrIdx B I 8]) I
        exact idx_reads (List.mem_singleton_self _)
      rw [getW_widen hw hB] at hp
      rw [getW_widen hw hI] at hvi
      exact hsafe p vi hp hvi
    | _ => trivial
  obtain ⟨t', zt, h1, h2, h3⟩ := AArm.sim P rsp a h sa (widenS s) zf hc.widen hsafe'
  have hcg := fstepA_congr (frameP P rsp) a.li (aagree_widen hw) zf
  rw [hst, h1] at hcg
  cases hcg with
  | some hs =>
    obtain ⟨hn, hmem, -, -, hz⟩ := hs
    simp only at hn hmem hz
    subst hz
    refine ⟨⟨fun r hr => ?_, h2.sp, fun x hx => by rw [hmem]; exact h2.mem x hx⟩, h3⟩
    rcases hn.2 r with he | ⟨he1, he2⟩
    · left
      unfold LstateN.getW
      rw [he]
      exact h2.regs r hr
    · have hreg := h2.regs r hr
      rw [getW_eq_some_iff] at hreg
      rw [he2] at hreg
      change widenCell r (s.reg.lvm r) = _ at hreg
      rcases hcell : s.reg.lvm r with ⟨wr, vr⟩
      rw [hcell] at hreg he1
      by_cases h1w : wr = 1
      · subst h1w
        right
        refine ⟨vr, he1, ?_⟩
        simp [widenCell, hr] at hreg
        exact hreg.symm
      · left
        rw [getW_eq_some_iff, he1]
        simpa [widenCell, h1w] using hreg

/-! ## 3. The bytes of the carry chain -/

/-- `ADCX:64 D, A, S, C` between general-purpose names: the copy of `A` into `D` unless they
    coincide, `bt $0, C`, and `adcx S, D`. -/
theorem encodeLopn_adcx3 (F W : Nat) (D A S C : String) (qB : Nat) (hD : gpOk D = true)
    (hA : gpOk A = true) (hS : gpOk S = true) (hC : gpOk C = true) :
    encodeLopn F W (.Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C]) qB
      = (if A = D then [] else encAluRRw 1 0x89 (gpNumU D) (gpNumU A))
        ++ encBtImm 1 (gpNumU C) 0 ++ ScalarEncoder.encAdxCarry 0x66 (gpNumU D) (gpNumU S) := by
  have fD := gpFacts hD
  have fA := gpFacts hA
  have fS := gpFacts hS
  have fC := gpFacts hC
  have hst : stripWidthTag "ADCX:64" = "ADCX" := by decide +kernel
  have hpx : adxPrefix "ADCX" = some 0x66 := rfl
  by_cases hAD : A = D
  · subst hAD
    simp (config := { decide := true }) [encodeLopn, fA.notSlot, fA.notMem, fS.notSlot,
      fS.notMem, fC.notSlot, fC.notMem, LprogBytes.rexW, hst, hpx]
  · simp (config := { decide := true }) [encodeLopn, fD.notSlot, fD.notMem, fA.notSlot,
      fA.notMem, fS.notSlot, fS.notMem, fC.notSlot, fC.notMem, hAD, LprogBytes.rexW, hst, hpx]

/-- `ADCXHI:64 O, A, S, C`: the carry flag materialised into `O` by `setc` and `movzbq`. -/
theorem encodeLopn_adcxhi3 (F W : Nat) (O A S C : String) (qB : Nat) (hO : gpOk O = true) :
    encodeLopn F W (.Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]) qB
      = encSetccMovzx 0x92 (gpNumU O) :=
  LprogBytes.encodeLopn_adcxhi F W O [.reg A, .reg S, .reg C] (gpFacts hO).isGp

open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder hiding regName
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape

/-- `bt $0, %c`. -/
theorem pieceDec_bt (c : Nat) (hc : c < 16) :
    PieceDec (encBtImm 1 c 0, .bt (SailX86Decoder.regName c) (.imm 0)) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have e := roundtrip_bt canonAlloc (SailX86Decoder.regName c) 0 rest (by decide)
  have he : encBtImm 1 c 0 = ScalarEncoder.encBtImm8 c 0 := by
    simp [encBtImm, ScalarEncoder.encBtImm8, rexOpt_w1]
  simpa [ScalarEncoder.encodeJInstr, renameJ, nameOf, operandOf, regOf_canon c hc,
    gpNum_regName c hc, he] using e

/-- `adcx %s, %d`. -/
theorem pieceDec_adcx (d s : Nat) (hd : d < 16) (hs : s < 16) :
    PieceDec (ScalarEncoder.encAdxCarry 0x66 d s,
      .adcx (SailX86Decoder.regName d) (.reg (SailX86Decoder.regName s))) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have e := roundtrip_adcx canonAlloc (SailX86Decoder.regName d) (SailX86Decoder.regName s)
    rest
  simpa [ScalarEncoder.encodeJInstr, renameJ, nameOf, operandOf, regOf_canon d hd,
    regOf_canon s hs, gpNum_regName d hd, gpNum_regName s hs] using e

/-- `setc %o` and `movzbq`. -/
theorem pieceDec_setc (o : Nat) (ho : o < 16) :
    PieceDec (encSetccMovzx 0x92 o, .setc (SailX86Decoder.regName o)) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have he : encSetccMovzx 0x92 o = ScalarEncoder.encSetcMovzx o := by
    interval_cases o <;> rfl
  rw [he]
  exact decodeJ1_encSetcMovzx o ho rest

/-! ## 4. The address-machine steps of the carry chain -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry

/-- The address machine steps `ADCX:64 D, A, S, C` on registers by writing `addCarryWord` of
    the 64-bit values of `A`, `S` and the one-bit value of `C` to `D`. -/
theorem fstepA_adcx3 (frame : String → Option (BitVec 64)) (D A S C : String) (s : LstateA)
    (zf : Bool) (hfD : frame D = none) (hfA : frame A = none) (hfS : frame S = none)
    {va vb : BitVec 64} (hA : s.reg.getW A 64 = some va) (hS : s.reg.getW S 64 = some vb) :
    fstepA frame (.Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C], .reg none) s zf
      = (s.reg.getW C 1).map fun vc =>
          ({ s with reg := (s.reg.setReg D (VIR.JasminDialect.addCarryWord va vb vc)).nextPc },
            zf) := by
  cases hc : s.reg.getW C 1 <;>
    simp (config := { decide := true }) [fstepA, slotMov?, slotCmp?, regStepA, fstepF,
      cmpArgs?, movRegArgs?, stepMemF, lsemStepMem, lsemStepCast, castStruct?, movImmStruct?,
      lsemStepMC, mulhiStruct?, adcxStruct?, readReg_of_getW hA, hS, hc, withALUFlags,
      aluFlagOp?, carryArgs?, wideArgs?, cellA?, slotCarry?, hfD, hfA, hfS]

/-- The address machine steps `ADCXHI:64 O, A, S, C` on registers by writing the one-bit
    `carryOutBit` of the 64-bit values of `A`, `S` and the one-bit value of `C` to `O`. -/
theorem fstepA_adcxhi (frame : String → Option (BitVec 64)) (O A S C : String) (s : LstateA)
    (zf : Bool) (hfO : frame O = none) (hfA : frame A = none) (hfS : frame S = none)
    {va vb : BitVec 64} (hA : s.reg.getW A 64 = some va) (hS : s.reg.getW S 64 = some vb) :
    fstepA frame (.Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C], .reg none) s zf
      = (s.reg.getW C 1).map fun vc =>
          ({ s with reg := (s.reg.setReg O (VIR.JasminDialect.carryOutBit va vb vc)).nextPc },
            zf) := by
  cases hc : s.reg.getW C 1 <;>
    simp (config := { decide := true }) [fstepA, slotMov?, slotCmp?, regStepA, fstepF,
      cmpArgs?, movRegArgs?, stepMemF, lsemStepMem, lsemStepCast, castStruct?, movImmStruct?,
      lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, readReg_of_getW hA, hS, hc,
      withALUFlags, aluFlagOp?, carryArgs?, wideArgs?, cellA?, slotCarry?, hfO, hfA, hfS]

/-! ## 5. The machine steps of the carry chain -/

/-- `bt $0, %c` writes bit `0` of `c` to the carry flag and nothing else. -/
theorem evalInstrA_bt0 (sa : AState) (c : String) :
    (evalInstrA sa (.bt c (.imm 0))).regs = sa.regs
      ∧ (evalInstrA sa (.bt c (.imm 0))).mem = sa.mem
      ∧ (evalInstrA sa (.bt c (.imm 0))).flags.cf = some ((sa.regs c).getLsbD 0) := by
  refine ⟨rfl, evalInstrA_mem_of_noWriteB sa _ rfl, ?_⟩
  simp [evalInstrA, evalInstr, x86_BT, wbit, AState.view, JOperand.eval]

/-- `adcx %s, %d` writes the word of `x86_ADCX` to `d` and its carry to the carry flag. -/
theorem evalInstrA_adcx (sa : AState) (d s : String) :
    (evalInstrA sa (.adcx d (.reg s))).regs = (fun r => if r = d then
        (x86_ADCX (sa.regs d) (sa.regs s) (sa.flags.cf.getD false)).2 else sa.regs r)
      ∧ (evalInstrA sa (.adcx d (.reg s))).mem = sa.mem
      ∧ (evalInstrA sa (.adcx d (.reg s))).flags.cf
        = (x86_ADCX (sa.regs d) (sa.regs s) (sa.flags.cf.getD false)).1 := by
  refine ⟨?_, evalInstrA_mem_of_noWriteB sa _ rfl, ?_⟩ <;>
    simp [evalInstrA, evalInstr, AState.view, JOperand.eval, JState.flagB]

/-- `setc %o` writes `1` or `0` to `o` by the carry flag, and keeps the flags. -/
theorem evalInstrA_setc (sa : AState) (o : String) :
    (evalInstrA sa (.setc o)).regs = (fun r => if r = o then
        (if sa.flags.cf.getD false then 1 else 0) else sa.regs r)
      ∧ (evalInstrA sa (.setc o)).mem = sa.mem
      ∧ (evalInstrA sa (.setc o)).flags = sa.flags := by
  refine ⟨rfl, evalInstrA_mem_of_noWriteB sa _ rfl, rfl⟩

/-- The word of `addCarryWord` is the word of `waddcarry` at the carry-in bit. -/
theorem addCarryWord_eq (va vb : BitVec 64) (vc : BitVec 1) :
    VIR.JasminDialect.addCarryWord va vb vc = (waddcarry va vb (vc.getLsbD 0)).2 := by
  rcases (by decide : ∀ v : BitVec 1, v = 0 ∨ v = 1) vc with rfl | rfl <;>
    simp [VIR.JasminDialect.addCarryWord, waddcarry, BitVec.ofNat_add]

/-- The bit of `carryOutBit` is the carry of `waddcarry` at the carry-in bit. -/
theorem carryOutBit_eq (va vb : BitVec 64) (vc : BitVec 1) :
    VIR.JasminDialect.carryOutBit va vb vc
      = if (waddcarry va vb (vc.getLsbD 0)).1 then 1 else 0 := by
  rcases (by decide : ∀ v : BitVec 1, v = 0 ∨ v = 1) vc with rfl | rfl <;>
    simp [VIR.JasminDialect.carryOutBit, waddcarry, ge_iff_le]

/-! ## 6. The carry arms -/

/-- A carry instruction of a physical body. -/
inductive CArm where
  /-- `ADCX:64 D, A, S, C`: `D := A + S + C` with the one-bit carry-in `C`. -/
  | adcx (D A S C : String)
  /-- `ADCXHI:64 O, A, S, C`: `O :=` the one-bit carry-out of `A + S + C`. -/
  | adcxhi (O A S C : String)

/-- The instruction of a carry arm. -/
def CArm.instr : CArm → LinstrR
  | .adcx D A S C => .Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C]
  | .adcxhi O A S C => .Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]

/-- The byte pieces of a carry arm. -/
def CArm.pieces : CArm → List (List (BitVec 8) × JInstr 64)
  | .adcx D A S C =>
      (if A = D then [] else [(encAluRRw 1 0x89 (gpNumU D) (gpNumU A),
          .mov (phys D) (.reg (phys A)))])
        ++ [(encBtImm 1 (gpNumU C) 0, .bt (phys C) (.imm 0)),
          (ScalarEncoder.encAdxCarry 0x66 (gpNumU D) (gpNumU S), .adcx (phys D) (.reg (phys S)))]
  | .adcxhi O _ _ _ => [(encSetccMovzx 0x92 (gpNumU O), .setc (phys O))]

/-- The machine instructions of a carry arm. -/
def CArm.js (c : CArm) : List (JInstr 64) := c.pieces.map Prod.snd

/-- **The conditions of a carry arm**: general-purpose operands, a carry-in other than the
    two word sources, and, when the copy of `A` into `D` is laid down, a destination other
    than `S` and `C`, which the copy would overwrite before they are read. -/
def CArm.ok : CArm → Bool
  | .adcx D A S C => gpOk D && gpOk A && gpOk S && gpOk C && A != C && S != C
      && (A == D || (D != S && D != C))
  | .adcxhi O A S C => gpOk O && gpOk A && gpOk S && gpOk C && A != C && S != C

/-- **The bytes of a carry arm.** -/
theorem CArm.bytes (P : Params) (c : CArm) (h : c.ok = true) :
    encodeLopn P.frame P.spillW c.instr P.qsaveB = c.pieces.flatMap Prod.fst
      ∧ ∀ q ∈ c.pieces, PieceDec q := by
  cases c with
  | adcx D A S C =>
    simp only [CArm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hD, hA⟩, hS⟩, hC⟩, -⟩, -⟩, -⟩ := h
    refine ⟨?_, ?_⟩
    · rw [CArm.instr, encodeLopn_adcx3 _ _ _ _ _ _ _ hD hA hS hC]
      by_cases hAD : A = D <;> simp [CArm.pieces, hAD]
    · intro q hq
      simp only [CArm.pieces, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        at hq
      rcases hq with hq | rfl | rfl
      · by_cases hAD : A = D
        · simp [hAD] at hq
        · simp only [hAD, if_false, List.mem_singleton] at hq
          subst hq
          exact fun rest => decodeLinstr_movRR _ _ rest (gpNumU_lt_16 D) (gpNumU_lt_16 A)
      · exact pieceDec_bt _ (gpNumU_lt_16 C)
      · exact pieceDec_adcx _ _ (gpNumU_lt_16 D) (gpNumU_lt_16 S)
  | adcxhi O A S C =>
    simp only [CArm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hO, -⟩, -⟩, -⟩, -⟩, -⟩ := h
    refine ⟨by simp [CArm.instr, CArm.pieces, encodeLopn_adcxhi3 _ _ _ _ _ _ _ hO], ?_⟩
    intro q hq
    simp only [CArm.pieces, List.mem_singleton] at hq
    subst hq
    exact pieceDec_setc _ (gpNumU_lt_16 O)

/-- The computed shape of a carry arm's instruction decodes to its machine instructions. -/
theorem CArm.shape_ops {P : Params} {c : CArm} (h : c.ok = true) {sh : DShape}
    (hs : shapeOf P c.instr = some sh) : sh.ops' = c.js := by
  obtain ⟨hb, hp⟩ := c.bytes P h
  cases c <;> exact shapeOf_lopn_ops _ hb hp hs

/-- A write of `v` to the machine register of `D`, against a write to `D` that `ACorrW`
    relates to `v`, preserves `ACorrW` when the memories still agree outside the red-zone
    word. -/
theorem ACorrW.write {rsp : BitVec 64} {sa sa' : AState} {s s' : LstateA}
    (h : ACorrW rsp sa s) {D : String} (hD : gpOk D = true) (v : BitVec 64)
    (hregs : ∀ r, sa'.regs r = if r = phys D then v else sa.regs r)
    (hmem : ∀ x, ¬ InRange8 (redW rsp) x → s'.mem x = sa'.mem x)
    (hlvm : ∀ r, r ≠ D → s'.reg.lvm r = s.reg.lvm r)
    (hcell : s'.reg.getW D 64 = some v ∨ ∃ b : BitVec 1, s'.reg.lvm D = ⟨1, b⟩ ∧ v = b.setWidth 64) :
    ACorrW rsp sa' s' where
  regs r hr := by
    by_cases hrD : r = D
    · subst hrD
      rw [hregs, if_pos rfl]
      exact hcell
    · rw [hregs, if_neg (fun e => hrD (phys_inj hr hD e))]
      have hl := hlvm r hrD
      have hg : s'.reg.getW r 64 = s.reg.getW r 64 := by unfold LstateN.getW; rw [hl]
      rw [hg, hl]
      exact h.regs r hr
  sp := by rw [hregs, if_neg (fun e => (gpFacts hD).physNe e.symm)]; exact h.sp
  mem := hmem

/-- The carry flag of the machine holds the carry-out of `A + S + C` on the words of the
    address state at the frame `frame`. -/
def CarryAt (frame : String → Option (BitVec 64)) (sa : AState) (s : LstateA)
    (A S C : String) : Prop :=
  ∃ co, sa.flags.cf = some co ∧ ∀ va vb vc, wordA frame s A = some va →
    wordA frame s S = some vb → s.reg.getW C 1 = some vc → (waddcarry va vb (vc.getLsbD 0)).1 = co

/-- A 64-bit general-purpose name under `ACorrW` reads its machine register. -/
theorem ACorrW.wide {rsp : BitVec 64} {sa : AState} {s : LstateA} (h : ACorrW rsp sa s)
    {r : String} (hr : gpOk r = true) (hw : (s.reg.lvm r).1 ≠ 1) :
    s.reg.getW r 64 = some (sa.regs (phys r)) := by
  rcases h.regs r hr with hg | ⟨b, hb, -⟩
  · exact hg
  · exact absurd (by rw [hb]) hw

/-- A name read at width `1` under `ACorrW` holds a bit its machine register zero-extends. -/
theorem ACorrW.bit {rsp : BitVec 64} {sa : AState} {s : LstateA} (h : ACorrW rsp sa s)
    {r : String} (hr : gpOk r = true) {vc : BitVec 1} (hc : s.reg.getW r 1 = some vc) :
    sa.regs (phys r) = vc.setWidth 64 := by
  have hl := getW_eq_some_iff.1 hc
  rcases h.regs r hr with hg | ⟨b, hb, hm⟩
  · have := getW_eq_some_iff.1 hg
    rw [hl] at this
    simp at this
  · rw [hl] at hb
    obtain rfl := eq_of_heq (Sigma.mk.inj hb).2
    exact hm

/-- **The carry-chain add.** From `ACorrW`, with `A` and `S` at width `64`, the address-machine
    step of `ADCX:64 D, A, S, C` is matched by `bt $0, C; adcx S, D` (after the copy of `A`
    into `D`): the registers end related by `ACorrW`, the zero flag is kept, and, when `D` is
    none of `A`, `S`, `C`, the machine carry flag holds the carry-out of the add on the
    values of the result state. -/
theorem sim_adcx (P : Params) (rsp : BitVec 64) (D A S C : String)
    (h : (CArm.adcx D A S C).ok = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s) (hwA : (s.reg.lvm A).1 ≠ 1) (hwS : (s.reg.lvm S).1 ≠ 1)
    (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((CArm.adcx D A S C).instr, .reg none) s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa (CArm.adcx D A S C).js) s' ∧ zf' = zf
      ∧ (D ≠ A → D ≠ S → D ≠ C →
          CarryAt (frameP P rsp) (aMachine.runBlock sa (CArm.adcx D A S C).js) s' A S C) := by
  simp only [CArm.ok, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hD, hA⟩, hS⟩, hC⟩, -⟩, -⟩, hal⟩ := h
  set va := sa.regs (phys A) with hva
  set vb := sa.regs (phys S) with hvb
  have hgA := hc.wide hA hwA
  have hgS := hc.wide hS hwS
  rw [CArm.instr, fstepA_adcx3 _ D A S C s zf (frameP_gp hD) (frameP_gp hA) (frameP_gp hS)
    hgA hgS] at hst
  cases hgc : s.reg.getW C 1 with
  | none => rw [hgc] at hst; cases hst
  | some vc =>
  rw [hgc] at hst
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  have hmC := hc.bit hC hgc
  set bit := vc.getLsbD 0 with hbit
  -- the machine run, up to the copy of `A` into `D`
  obtain ⟨sa1, hrun, h1D, h1S, h1C, h1r, h1f, h1m⟩ : ∃ sa1 : AState,
      aMachine.runBlock sa (CArm.adcx D A S C).js
        = evalInstrA (evalInstrA sa1 (.bt (phys C) (.imm 0))) (.adcx (phys D) (.reg (phys S)))
      ∧ sa1.regs (phys D) = va ∧ sa1.regs (phys S) = vb ∧ sa1.regs (phys C) = vc.setWidth 64
      ∧ (∀ r, r ≠ phys D → sa1.regs r = sa.regs r) ∧ sa1.flags = sa.flags
      ∧ sa1.mem = sa.mem := by
    by_cases hAD : A = D
    · subst hAD
      exact ⟨sa, by simp [CArm.js, CArm.pieces]; rfl, rfl, rfl, hmC, fun _ _ => rfl, rfl, rfl⟩
    · obtain ⟨hDS, hDC⟩ := hal.resolve_left hAD
      have r1 : ∀ r, (evalInstrA sa (.mov (phys D) (.reg (phys A)))).regs r
          = if r = phys D then sa.regs (phys A) else sa.regs r := fun r => rfl
      refine ⟨evalInstrA sa (.mov (phys D) (.reg (phys A))), ?_, ?_, ?_, ?_, ?_, rfl,
        evalInstrA_mem_of_noWriteB sa _ rfl⟩
      · simp [CArm.js, CArm.pieces, hAD]; rfl
      · rw [r1, if_pos rfl]
      · rw [r1, if_neg (fun e => hDS (phys_inj hS hD e).symm)]
      · rw [r1, if_neg (fun e => hDC (phys_inj hC hD e).symm)]; exact hmC
      · intro r hr; rw [r1, if_neg hr]
  obtain ⟨r2, m2, c2⟩ := evalInstrA_bt0 sa1 (phys C)
  obtain ⟨r3, m3, c3⟩ := evalInstrA_adcx (evalInstrA sa1 (.bt (phys C) (.imm 0))) (phys D) (phys S)
  have hcf2 : (evalInstrA sa1 (.bt (phys C) (.imm 0))).flags.cf.getD false = bit := by
    rw [c2, h1C]
    simp [hbit]
  set co := (waddcarry va vb bit).1 with hco
  have hword : (x86_ADCX va vb bit).2 = VIR.JasminDialect.addCarryWord va vb vc := by
    rw [addCarryWord_eq]; rfl
  rw [hrun]
  refine ⟨hc.write hD (VIR.JasminDialect.addCarryWord va vb vc) (fun r => ?_) (fun x hx => ?_)
    (fun r hr => ?_) ?_, rfl, fun hDA hDS hDC => ⟨co, ?_, fun va' vb' vc' ha hb hcc => ?_⟩⟩
  · simp only [r3, r2, hcf2, h1D, h1S, hword]
    split
    · rfl
    · rename_i hne; exact h1r r hne
  · rw [m3, m2, h1m]; exact hc.mem x hx
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr]
  · left
    exact getW_setReg_nextPcN s.reg D D _ |>.trans (if_pos rfl)
  · rw [c3, r2, hcf2, h1D, h1S]; rfl
  · simp only [wordA, frameP_gp hA, frameP_gp hS] at ha hb
    have eA : (s.reg.setReg D (VIR.JasminDialect.addCarryWord va vb vc)).nextPc.getW A 64
        = some va := by rw [getW_setReg_nextPcN, if_neg (Ne.symm hDA)]; exact hgA
    have eS : (s.reg.setReg D (VIR.JasminDialect.addCarryWord va vb vc)).nextPc.getW S 64
        = some vb := by rw [getW_setReg_nextPcN, if_neg (Ne.symm hDS)]; exact hgS
    have eC : (s.reg.setReg D (VIR.JasminDialect.addCarryWord va vb vc)).nextPc.getW C 1
        = some vc := by
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hDC)]; exact hgc
    have := ha.symm.trans eA
    have := hb.symm.trans eS
    have := hcc.symm.trans eC
    simp_all

/-- **The carry-out binding.** From `ACorrW`, with `A` and `S` at width `64` and the machine
    carry flag holding the carry-out of `A + S + C`, the address-machine step of
    `ADCXHI:64 O, A, S, C`, which writes the one-bit carry-out to `O`, is matched by
    `setc O`: the registers end related by `ACorrW`, and the zero flag and the machine flags
    are kept. -/
theorem sim_adcxhi (P : Params) (rsp : BitVec 64) (O A S C : String)
    (h : (CArm.adcxhi O A S C).ok = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s) (hwA : (s.reg.lvm A).1 ≠ 1) (hwS : (s.reg.lvm S).1 ≠ 1)
    (hcy : CarryAt (frameP P rsp) sa s A S C) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((CArm.adcxhi O A S C).instr, .reg none) s zf
      = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa (CArm.adcxhi O A S C).js) s' ∧ zf' = zf
      ∧ (aMachine.runBlock sa (CArm.adcxhi O A S C).js).flags = sa.flags := by
  simp only [CArm.ok, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hO, hA⟩, hS⟩, hC⟩, -⟩, -⟩ := h
  have hgA := hc.wide hA hwA
  have hgS := hc.wide hS hwS
  rw [CArm.instr, fstepA_adcxhi _ O A S C s zf (frameP_gp hO) (frameP_gp hA) (frameP_gp hS)
    hgA hgS] at hst
  cases hgc : s.reg.getW C 1 with
  | none => rw [hgc] at hst; cases hst
  | some vc =>
  rw [hgc] at hst
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  obtain ⟨co, hcf, hco⟩ := hcy
  have hco' := hco _ _ _ (by simp only [wordA, frameP_gp hA]; exact hgA)
    (by simp only [wordA, frameP_gp hS]; exact hgS) hgc
  obtain ⟨r1, m1, f1⟩ := evalInstrA_setc sa (phys O)
  have hrun : aMachine.runBlock sa (CArm.adcxhi O A S C).js = evalInstrA sa (.setc (phys O)) := rfl
  rw [hrun]
  refine ⟨hc.write hO (if co then 1 else 0) (fun r => ?_) (fun x hx => ?_) (fun r hr => ?_) ?_,
    rfl, f1⟩
  · rw [r1, hcf]; rfl
  · rw [m1]; exact hc.mem x hx
  · show (s.reg.setReg O _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr]
  · right
    refine ⟨VIR.JasminDialect.carryOutBit (sa.regs (phys A)) (sa.regs (phys S)) vc, ?_, ?_⟩
    · show (if O = O then _ else _) = _
      rw [if_pos rfl]
    · rw [carryOutBit_eq, hco']
      cases co <;> decide

/-! ## 7. The cell arms -/

/-- The encoder's parse of a `mem.<B>.<off>` name is the address machine's, with the base
    read as a register number. -/
theorem parseMemName_cellParts (n : String) :
    parseMemName n = (cellParts? n).map fun p => (gpNumU p.1, Int.ofNat p.2) := by
  unfold parseMemName cellParts?
  split
  · generalize List.span (fun x => x != '.') (List.drop 4 n.toList) = p
    rcases p with ⟨base, _ | ⟨c, off⟩⟩
    · rfl
    · by_cases hc : c = '.'
      · subst hc
        simp only
        cases natOfDigits? off <;> rfl
      · simp [hc]
  · rfl

/-- A whole-word access of a cell `[B + off]` of a physical body. -/
inductive MArm where
  /-- `LOAD:64 D, n` with `n` the cell `[B + off]`. -/
  | ldm (D n B : String) (off : Nat)
  /-- `STORE:64 n, S` with `n` the cell `[B + off]`. -/
  | stm (n B : String) (off : Nat) (S : String)

/-- The instruction of a cell arm. -/
def MArm.instr : MArm → LinstrR
  | .ldm D n _ _ => .Lopn [.reg D] "LOAD:64" [.reg n]
  | .stm n _ _ S => .Lopn [.reg n] "STORE:64" [.reg S]

/-- The byte pieces of a cell arm: `mov off(%B), %D` and `mov %S, off(%B)`. -/
def MArm.pieces : MArm → List (List (BitVec 8) × JInstr 64)
  | .ldm D _ B off => [(encMemMovw 1 0x8b (gpNumU D) (gpNumU B) (Int.ofNat off),
      .loadMem (phys D) (phys B) (Int.ofNat off))]
  | .stm _ B off S => [(encMemMovw 1 0x89 (gpNumU S) (gpNumU B) (Int.ofNat off),
      .storeMem (phys B) (Int.ofNat off) (.reg (phys S)))]

/-- The machine instructions of a cell arm. -/
def MArm.js (m : MArm) : List (JInstr 64) := m.pieces.map Prod.snd

/-- **The conditions of a cell arm**: the cell name parses to the base and offset of the arm,
    general-purpose register and base, and an offset with a signed 32-bit displacement. -/
def MArm.ok : MArm → Bool
  | .ldm D n B off => cellParts? n == some (B, off) && gpOk D && gpOk B
      && dispOk32 (Int.ofNat off)
  | .stm n B off S => cellParts? n == some (B, off) && gpOk S && gpOk B
      && dispOk32 (Int.ofNat off)

/-- The cell arm of an instruction. -/
def classifyM : LinstrR → Option MArm
  | .Lopn [.reg d] o [.reg n] =>
      if o = "LOAD:64" then (cellParts? n).map fun p => .ldm d n p.1 p.2
      else if o = "STORE:64" then (cellParts? d).map fun p => .stm d p.1 p.2 n
      else none
  | _ => none

theorem classifyM_instr {i : LinstrR} {m : MArm} (h : classifyM i = some m) : m.instr = i := by
  unfold classifyM at h
  split at h
  · split_ifs at h with h1 h2
    · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h; subst h1; rfl
    · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h; subst h2; rfl
  · cases h

/-- `mov off(%b), %d` with a signed 32-bit displacement. -/
theorem pieceDec_loadMem (d b : Nat) (off : Int) (hd : d < 16) (hb : b < 16)
    (h : dispOk32 off = true) :
    PieceDec (encMemMovw 1 0x8b d b off,
      .loadMem (SailX86Decoder.regName d) (SailX86Decoder.regName b) off) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have e := roundtrip_loadMem32 canonAlloc (SailX86Decoder.regName d)
    (SailX86Decoder.regName b) off rest h
  simpa [ScalarEncoder.encodeJInstr, renameJ, nameOf, regOf_canon d hd, regOf_canon b hb,
    gpNum_regName d hd, gpNum_regName b hb, LprogJInstrBytesAgree.encMemMovw_one] using e

/-- `mov %s, off(%b)` with a signed 32-bit displacement. -/
theorem pieceDec_storeMem (s b : Nat) (off : Int) (hs : s < 16) (hb : b < 16)
    (h : dispOk32 off = true) :
    PieceDec (encMemMovw 1 0x89 s b off,
      .storeMem (SailX86Decoder.regName b) off (.reg (SailX86Decoder.regName s))) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have e := roundtrip_storeMem32 canonAlloc (SailX86Decoder.regName b)
    (SailX86Decoder.regName s) off rest h
  simpa [ScalarEncoder.encodeJInstr, renameJ, nameOf, operandOf, regOf_canon s hs,
    regOf_canon b hb, gpNum_regName s hs, gpNum_regName b hb,
    LprogJInstrBytesAgree.encMemMovw_one] using e

/-- A cell name is no frame-slot name. -/
theorem notSlot_of_cell {n : String} {p : String × Nat} (h : cellParts? n = some p) :
    isSpillOrQsave n = false ∧ ∀ F W qB, spillQsaveOff F W n qB = none := by
  unfold cellParts? at h
  split at h
  · rename_i hp
    unfold hasPrefix at hp
    rw [List.isPrefixOf_iff_prefix] at hp
    obtain ⟨t, ht⟩ := hp
    have hk : hasPrefix n "k." = false := by
      unfold hasPrefix; rw [← ht]; simp [List.isPrefixOf]
    have hq : hasPrefix n "qsave." = false := by
      unfold hasPrefix; rw [← ht]; simp [List.isPrefixOf]
    exact ⟨by simp [isSpillOrQsave, hk, hq], fun F W qB => by simp [spillQsaveOff, hk, hq]⟩
  · cases h

/-- `LOAD:64 D, n` with `n` the cell `[B + off]` and `D` general-purpose. -/
theorem encodeLopn_ldm (F W : Nat) (D n B : String) (off : Nat) (qB : Nat)
    (hn : cellParts? n = some (B, off)) (hD : gpOk D = true) :
    encodeLopn F W (.Lopn [.reg D] "LOAD:64" [.reg n]) qB
      = encMemMovw 1 0x8b (gpNumU D) (gpNumU B) (Int.ofNat off) := by
  have fD := gpFacts hD
  obtain ⟨hs, hoff⟩ := notSlot_of_cell hn
  have hpm : parseMemName n = some (gpNumU B, Int.ofNat off) := by
    rw [parseMemName_cellParts, hn]; rfl
  simp (config := { decide := true }) [encodeLopn, encTwoAddr, fD.off, fD.notSlot, fD.notMem,
    hs, hoff, hpm, tagShiftExt, aluOpcode, stripWidthTag, LprogBytes.rexW, memSrcOp, adxPrefix]

/-- `STORE:64 n, S` with `n` the cell `[B + off]` and `S` general-purpose. -/
theorem encodeLopn_stm (F W : Nat) (n B : String) (off : Nat) (S : String) (qB : Nat)
    (hn : cellParts? n = some (B, off)) (hS : gpOk S = true) :
    encodeLopn F W (.Lopn [.reg n] "STORE:64" [.reg S]) qB
      = encMemMovw 1 0x89 (gpNumU S) (gpNumU B) (Int.ofNat off) := by
  have fS := gpFacts hS
  obtain ⟨hs, hoff⟩ := notSlot_of_cell hn
  have hpm : parseMemName n = some (gpNumU B, Int.ofNat off) := by
    rw [parseMemName_cellParts, hn]; rfl
  simp (config := { decide := true }) [encodeLopn, encTwoAddr, fS.off, fS.notSlot, fS.notMem,
    hs, hoff, hpm, tagShiftExt, aluOpcode, stripWidthTag, LprogBytes.rexW, memDstOp, adxPrefix]

/-- **The bytes of a cell arm.** -/
theorem MArm.bytes (P : Params) (m : MArm) (h : m.ok = true) :
    encodeLopn P.frame P.spillW m.instr P.qsaveB = m.pieces.flatMap Prod.fst
      ∧ ∀ q ∈ m.pieces, PieceDec q := by
  cases m with
  | ldm D n B off =>
    simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hn, hD⟩, hB⟩, hd⟩ := h
    refine ⟨by simp [MArm.instr, MArm.pieces, encodeLopn_ldm _ _ _ _ _ _ _ hn hD], ?_⟩
    intro q hq
    simp only [MArm.pieces, List.mem_singleton] at hq
    subst hq
    exact pieceDec_loadMem _ _ _ (gpNumU_lt_16 D) (gpNumU_lt_16 B) hd
  | stm n B off S =>
    simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hn, hS⟩, hB⟩, hd⟩ := h
    refine ⟨by simp [MArm.instr, MArm.pieces, encodeLopn_stm _ _ _ _ _ _ _ hn hS], ?_⟩
    intro q hq
    simp only [MArm.pieces, List.mem_singleton] at hq
    subst hq
    exact pieceDec_storeMem _ _ _ (gpNumU_lt_16 S) (gpNumU_lt_16 B) hd

/-- The computed shape of a cell arm's instruction decodes to its machine instruction. -/
theorem MArm.shape_ops {P : Params} {m : MArm} (h : m.ok = true) {sh : DShape}
    (hs : shapeOf P m.instr = some sh) : sh.ops' = m.js := by
  obtain ⟨hb, hp⟩ := m.bytes P h
  cases m <;> exact shapeOf_lopn_ops _ hb hp hs

/-- **The cell load.** From `ACorrW`, with the base `B` at width `64` and the eight bytes at
    the cell address disjoint from the red-zone word, the address-machine step of
    `LOAD:64 D, n` is matched by `mov off(%B), %D`. -/
theorem sim_ldm (P : Params) (rsp : BitVec 64) (D n B : String) (off : Nat)
    (h : (MArm.ldm D n B off).ok = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s) (hwB : (s.reg.lvm B).1 ≠ 1)
    (hsafe : ∀ p, s.reg.getW B 64 = some p → Disjoint8 (redW rsp) (p + BitVec.ofNat 64 off))
    (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((MArm.ldm D n B off).instr, .reg none) s zf
      = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa (MArm.ldm D n B off).js) s' ∧ zf' = zf := by
  simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hn, hD⟩, hB⟩, -⟩ := h
  have hgB := hc.wide hB hwB
  rw [MArm.instr, fstepA_ldm _ hn hgB] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  set a := sa.regs (phys B) + BitVec.ofNat 64 off with ha
  have hrd : read64 s.mem a = read64 sa.mem a := read64_eq_of_agree hc.mem (hsafe _ hgB)
  obtain ⟨hregs, hmem⟩ := evalInstrA_loadMem_eq sa (phys D) (phys B) (Int.ofNat off)
  have hofs : BitVec.ofInt 64 (Int.ofNat off) = BitVec.ofNat 64 off := BitVec.ofInt_natCast _ _
  have hrun : aMachine.runBlock sa (MArm.ldm D n B off).js
      = evalInstrA sa (.loadMem (phys D) (phys B) (Int.ofNat off)) := rfl
  rw [hrun]
  refine ⟨hc.write hD (read64 s.mem a) (fun r => by rw [hregs, hofs, hrd]) (fun x hx => ?_)
    (fun r hr => ?_) (Or.inl ?_), rfl⟩
  · rw [hmem]; exact hc.mem x hx
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr]
  · exact getW_setReg_nextPcN s.reg D D _ |>.trans (if_pos rfl)

/-- **The cell store.** From `ACorrW`, with the base `B` and the source `S` at width `64`,
    the address-machine step of `STORE:64 n, S` is matched by `mov %S, off(%B)`. -/
theorem sim_stm (P : Params) (rsp : BitVec 64) (n B : String) (off : Nat) (S : String)
    (h : (MArm.stm n B off S).ok = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s) (hwB : (s.reg.lvm B).1 ≠ 1) (hwS : (s.reg.lvm S).1 ≠ 1)
    (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((MArm.stm n B off S).instr, .reg none) s zf
      = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa (MArm.stm n B off S).js) s' ∧ zf' = zf := by
  simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hn, hS⟩, hB⟩, -⟩ := h
  have hgB := hc.wide hB hwB
  have hgS := hc.wide hS hwS
  rw [MArm.instr, fstepA_stm _ hn hgB hgS] at hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
  obtain ⟨hregs, hmem⟩ := evalInstrA_storeMem_eq sa (phys B) (phys S) (Int.ofNat off)
  have hofs : BitVec.ofInt 64 (Int.ofNat off) = BitVec.ofNat 64 off := BitVec.ofInt_natCast _ _
  have hrun : aMachine.runBlock sa (MArm.stm n B off S).js
      = evalInstrA sa (.storeMem (phys B) (Int.ofNat off) (.reg (phys S))) := rfl
  rw [hrun]
  refine ⟨⟨fun r hr => ?_, by rw [hregs]; exact hc.sp, fun x hx => ?_⟩, rfl⟩
  · rw [hregs]
    have hg : s.reg.nextPc.getW r 64 = s.reg.getW r 64 := LstateN.getW_nextPc _ _ _
    show s.reg.nextPc.getW r 64 = _ ∨ ∃ b : BitVec 1, s.reg.nextPc.lvm r = ⟨1, b⟩ ∧ _
    rw [hg]
    exact hc.regs r hr
  · show write64 s.mem _ _ x = _
    rw [hmem, hofs]
    exact agree_write64 hc.mem _ _ x hx

/-! ## 8. The carry arms with frame-slot operands -/

/-- A slot name is no cell name and no general-purpose name. -/
theorem slot_facts {x : String} {F W qB : Nat} {off : Int}
    (h : spillQsaveOff F W x qB = some off) :
    isSpillOrQsave x = true ∧ parseMemName x = none ∧ gpOk x = false := by
  unfold spillQsaveOff at h
  have hpre : hasPrefix x "k." = true ∨ hasPrefix x "qsave." = true := by
    split at h
    · exact Or.inl ‹_›
    · split at h
      · exact Or.inr ‹_›
      · cases h
  refine ⟨by simp [isSpillOrQsave, hpre], ?_, ?_⟩
  · unfold parseMemName
    rcases hpre with hp | hp <;>
    · unfold hasPrefix at hp ⊢
      rw [List.isPrefixOf_iff_prefix] at hp
      obtain ⟨t, ht⟩ := hp
      rw [← ht]
      simp [List.isPrefixOf]
  · cases hg : gpOk x
    · rfl
    · have hm := mem_gpList hg
      simp only [gpList, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> simp [hasPrefix] at hpre

/-- The four scratch candidates of a spilled-destination add are not all among three names. -/
theorem scratch_exists (A S C : String) :
    (["RAX", "RBX", "RCX", "RDX"].filter fun r => !([A, S, C].contains r)) ≠ [] := by
  intro h
  rw [List.filter_eq_nil_iff] at h
  have h1 := h "RAX" (by simp)
  have h2 := h "RBX" (by simp)
  have h3 := h "RCX" (by simp)
  have h4 := h "RDX" (by simp)
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.not_eq_true',
    Bool.not_eq_false, Bool.or_eq_true, beq_iff_eq] at h1 h2 h3 h4
  rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
    rcases h3 with h3 | h3 | h3 <;> rcases h4 with h4 | h4 | h4 <;>
    (subst_vars; simp_all (config := { decide := true }))

/-- The scratch register of a spilled-destination add: the first of `RAX`, `RBX`, `RCX`,
    `RDX` none of `A`, `S`, `C` names, as the encoder and the printer pick it. -/
def scratchS (A S C : String) : String :=
  match ["RAX", "RBX", "RCX", "RDX"].filter fun r => !([A, S, C].contains r) with
  | r :: _ => r
  | [] => "RDX"

/-- An operand of a carry arm: a general-purpose name, or a frame slot whose offset has a
    signed 32-bit displacement and whose eight bytes are disjoint from the red-zone word. -/
def kOk (P : Params) (x : String) : Bool :=
  gpOk x || (isSpillOrQsave x && match spillQsaveOff P.frame P.spillW x P.qsaveB with
    | some off => dispOk32 off && sepB cmovRedZone off
    | none => false)

/-- A carry instruction with a frame-slot operand. -/
inductive SArm where
  /-- `ADCX:64 D, A, S, C` with a frame slot among `D`, `A`, `S`. -/
  | adcx (D A S C : String)
  /-- `ADCXHI:64 O, A, S, C` with a frame slot among `A`, `S`. -/
  | adcxhi (O A S C : String)

/-- The instruction of a slot carry arm. -/
def SArm.instr : SArm → LinstrR
  | .adcx D A S C => .Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C]
  | .adcxhi O A S C => .Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]

/-- The copy of `A` into the accumulator `acc` of the add into `D`: a reload from the slot
    of `A`, nothing when `A` is the accumulator `D`, a register copy otherwise. -/
def sMv (P : Params) (D A : String) (acc : Nat) : List (List (BitVec 8) × JInstr 64) :=
  if isSpillOrQsave A then
    [(encRspMem 1 0x8b acc (slotOff P A),
      .loadMem (SailX86Decoder.regName acc) "%rsp" (slotOff P A))]
  else if A = D ∧ acc = gpNumU D then []
  else [(encAluRRw 1 0x89 acc (gpNumU A), .mov (SailX86Decoder.regName acc) (.reg (phys A)))]

/-- The add of `S` into the accumulator `acc`: `adcx` from the slot of `S` or from `S`. -/
def sAd (P : Params) (S : String) (acc : Nat) : List (List (BitVec 8) × JInstr 64) :=
  if isSpillOrQsave S then
    [(encAdxRspMem 0x66 acc (slotOff P S),
      .adcxMem (SailX86Decoder.regName acc) "%rsp" (slotOff P S))]
  else [(ScalarEncoder.encAdxCarry 0x66 acc (gpNumU S),
      .adcx (SailX86Decoder.regName acc) (.reg (phys S)))]

/-- The byte pieces of a slot carry arm. -/
def SArm.pieces (P : Params) : SArm → List (List (BitVec 8) × JInstr 64)
  | .adcx D A S C =>
      let bt := (encBtImm 1 (gpNumU C) 0, JInstr.bt (phys C) (.imm 0))
      if isSpillOrQsave D then
        let acc := gpNumU (scratchS A S C)
        bt :: (encRspMem 1 0x89 acc cmovRedZone,
            .storeMem "%rsp" cmovRedZone (.reg (SailX86Decoder.regName acc)))
          :: (sMv P D A acc ++ sAd P S acc
            ++ [(encRspMem 1 0x89 acc (slotOff P D),
                  .storeMem "%rsp" (slotOff P D) (.reg (SailX86Decoder.regName acc))),
                (encRspMem 1 0x8b acc cmovRedZone,
                  .loadMem (SailX86Decoder.regName acc) "%rsp" cmovRedZone)])
      else sMv P D A (gpNumU D) ++ bt :: sAd P S (gpNumU D)
  | .adcxhi O _ _ _ => [(encSetccMovzx 0x92 (gpNumU O), .setc (phys O))]

/-- The machine instructions of a slot carry arm. -/
def SArm.js (P : Params) (c : SArm) : List (JInstr 64) := (c.pieces P).map Prod.snd

/-- **The conditions of a slot carry arm**: general-purpose or well-placed slot operands with a
    slot among them, a general-purpose carry-in other than the word sources, a general-purpose
    carry-out destination, and, for a register destination with the copy of `A` laid down, a
    destination other than `S` and `C`. -/
def SArm.ok (P : Params) : SArm → Bool
  | .adcx D A S C => gpOk C && A != C && S != C && kOk P D && kOk P A && kOk P S
      && (isSpillOrQsave D || isSpillOrQsave A || isSpillOrQsave S)
      && (isSpillOrQsave D || (A == D && gpOk A) || (D != S && D != C))
  | .adcxhi O A S C => gpOk O && gpOk C && A != C && S != C && kOk P A && kOk P S
      && (isSpillOrQsave A || isSpillOrQsave S)

theorem kOk_cases {P : Params} {x : String} (h : kOk P x = true) :
    gpOk x = true ∨ ∃ off, spillQsaveOff P.frame P.spillW x P.qsaveB = some off
      ∧ dispOk32 off = true ∧ sepB cmovRedZone off = true := by
  unfold kOk at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨-, h⟩
  · exact Or.inl h
  · right
    split at h
    · rename_i off hoff
      simp only [Bool.and_eq_true] at h
      exact ⟨off, hoff, h.1, h.2⟩
    · cases h

/-- The facts of an operand the encoder reads: a general-purpose name, or a slot at its
    offset. -/
theorem opnd_facts {P : Params} {x : String} (h : kOk P x = true) :
    parseMemName x = none ∧ (isSpillOrQsave x = false ∨ ∃ off,
      spillQsaveOff P.frame P.spillW x P.qsaveB = some off ∧ isSpillOrQsave x = true
        ∧ slotOff P x = off) := by
  rcases kOk_cases h with hg | ⟨off, hoff, -, -⟩
  · exact ⟨(gpFacts hg).notMem, Or.inl (gpFacts hg).notSlot⟩
  · obtain ⟨h1, h2, -⟩ := slot_facts hoff
    exact ⟨h2, Or.inr ⟨off, hoff, h1, by simp [slotOff, hoff]⟩⟩

/-- The encoder's choice of the scratch register is `scratchS`. -/
theorem scratch_filter (A S C : String) :
    ["RAX", "RBX", "RCX", "RDX"].filter (fun r => !([A, S, C].contains r))
      = scratchS A S C :: (["RAX", "RBX", "RCX", "RDX"].filter
          (fun r => !([A, S, C].contains r))).tail := by
  unfold scratchS
  have hne := scratch_exists A S C
  revert hne
  cases ["RAX", "RBX", "RCX", "RDX"].filter (fun r => !([A, S, C].contains r)) with
  | nil => intro h; exact absurd rfl h
  | cons r rs => intro _; rfl

/-- **The bytes of a slot carry add.** -/
theorem encodeLopn_sadcx (P : Params) (D A S C : String) (h : (SArm.adcx D A S C).ok P = true) :
    encodeLopn P.frame P.spillW (SArm.adcx D A S C).instr P.qsaveB
      = ((SArm.adcx D A S C).pieces P).flatMap Prod.fst := by
  simp only [SArm.ok, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hC, hAC⟩, hSC⟩, hD⟩, hA⟩, hS⟩, -⟩, hal⟩ := h
  have fC := gpFacts hC
  obtain ⟨hDm, hDk⟩ := opnd_facts hD
  obtain ⟨hAm, hAk⟩ := opnd_facts hA
  obtain ⟨hSm, hSk⟩ := opnd_facts hS
  have hst : stripWidthTag "ADCX:64" = "ADCX" := by decide +kernel
  have hpx : adxPrefix "ADCX" = some 0x66 := rfl
  have hw : LprogBytes.rexW (LprogAsmPrinter.mnemWidth "ADCX:64") = 1 := by decide +kernel
  have hfC := fC.notSlot
  have hmC := fC.notMem
  have hsc := scratch_filter A S C
  rcases hDk with hDs | ⟨oD, hoD, hDs, hsD⟩ <;> rcases hAk with hAs | ⟨oA, hoA, hAs, hsA⟩ <;>
    rcases hSk with hSs | ⟨oS, hoS, hSs, hsS⟩ <;>
    simp (config := { decide := true }) [encodeLopn, SArm.instr, SArm.pieces, sMv, sAd, *]
  all_goals first
    | (by_cases hAD : A = D <;> simp [hAD] <;> done)
    | (split
       · rename_i heq
         exact absurd heq (by simpa using scratch_exists A S C)
       · rename_i r tl heq
         have hr : scratchS A S C = r := by simp [scratchS, heq]
         rw [hr]
         by_cases hAD : A = D
         · subst hAD; simp_all [cmovRedZone]
         · simp [hAD, cmovRedZone])

/-- `adcx off(%rsp), %d` with a signed 32-bit displacement. -/
theorem pieceDec_adcxRsp (d : Nat) (off : Int) (hd : d < 16) (h : dispOk32 off = true) :
    PieceDec (encAdxRspMem 0x66 d off,
      .adcxMem (SailX86Decoder.regName d) "%rsp" off) := by
  intro rest
  apply decodeLinstr_of_decodeJ1
  have e := roundtrip_adcxMem32 canonAlloc (SailX86Decoder.regName d) "%rsp" off rest h
  have hrsp : AsmPrinter.regOf canonAlloc "%rsp" = "%rsp" := by decide
  have hg4 : ScalarEncoder.gpNum "%rsp" = 4 := by decide
  have heq : encAdxRspMem 0x66 d off
      = ScalarEncoder.encodeJInstr canonAlloc (.adcxMem (SailX86Decoder.regName d) "%rsp" off) := by
    simp only [ScalarEncoder.encodeJInstr, regOf_canon d hd, gpNum_regName d hd, hrsp, hg4,
      encAdxRspMem, ScalarEncoder.memTail]
    split_ifs <;> simp_all (config := { decide := true })
  rw [heq]
  have h4 : SailX86Decoder.regName 4 = "%rsp" := rfl
  simpa [renameJ, nameOf, regOf_canon d hd, hrsp, gpNum_regName d hd, hg4, h4] using e

/-- **The bytes of a slot carry arm.** -/
theorem SArm.bytes (P : Params) (c : SArm) (h : c.ok P = true) :
    encodeLopn P.frame P.spillW c.instr P.qsaveB = (c.pieces P).flatMap Prod.fst
      ∧ ∀ q ∈ c.pieces P, PieceDec q := by
  cases c with
  | adcx D A S C =>
    refine ⟨encodeLopn_sadcx P D A S C h, ?_⟩
    simp only [SArm.ok, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
      beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hC, -⟩, -⟩, hD⟩, hA⟩, hS⟩, -⟩, -⟩ := h
    have hmv : ∀ acc, acc < 16 → ∀ q ∈ sMv P D A acc, PieceDec q := by
      intro acc hacc q hq
      simp only [sMv] at hq
      split at hq
      · simp only [List.mem_singleton] at hq
        subst hq
        rcases kOk_cases hA with hg | ⟨off, hoff, hd, -⟩
        · simp_all [(gpFacts hg).notSlot]
        · intro rest
          rw [show slotOff P A = off by simp [slotOff, hoff]]
          exact decodeLinstr_rspLoad acc off rest hacc hd
      · split at hq
        · cases hq
        · simp only [List.mem_singleton] at hq
          subst hq
          exact fun rest => decodeLinstr_movRR _ _ rest hacc (gpNumU_lt_16 A)
    have had : ∀ acc, acc < 16 → ∀ q ∈ sAd P S acc, PieceDec q := by
      intro acc hacc q hq
      simp only [sAd] at hq
      split at hq
      · simp only [List.mem_singleton] at hq
        subst hq
        rcases kOk_cases hS with hg | ⟨off, hoff, hd, -⟩
        · simp_all [(gpFacts hg).notSlot]
        · rw [show slotOff P S = off by simp [slotOff, hoff]]
          exact pieceDec_adcxRsp acc off hacc hd
      · simp only [List.mem_singleton] at hq
        subst hq
        exact pieceDec_adcx _ _ hacc (gpNumU_lt_16 S)
    intro q hq
    simp only [SArm.pieces] at hq
    split at hq
    · rename_i hDs
      have hacc := gpNumU_lt_16 (scratchS A S C)
      have hdD : dispOk32 (slotOff P D) = true := by
        rcases kOk_cases hD with hg | ⟨off, hoff, hd, -⟩
        · simp_all [(gpFacts hg).notSlot]
        · simpa [slotOff, hoff] using hd
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | ((hq | hq) | rfl | rfl)
      · exact pieceDec_bt _ (gpNumU_lt_16 C)
      · exact fun rest => decodeLinstr_rspStore _ cmovRedZone rest hacc (by decide)
      · exact hmv _ hacc q hq
      · exact had _ hacc q hq
      · exact fun rest => decodeLinstr_rspStore _ _ rest hacc hdD
      · exact fun rest => decodeLinstr_rspLoad _ cmovRedZone rest hacc (by decide)
    · simp only [List.mem_append, List.mem_cons] at hq
      rcases hq with hq | rfl | hq
      · exact hmv _ (gpNumU_lt_16 D) q hq
      · exact pieceDec_bt _ (gpNumU_lt_16 C)
      · exact had _ (gpNumU_lt_16 D) q hq
  | adcxhi O A S C =>
    simp only [SArm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hO, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
    refine ⟨by simp [SArm.instr, SArm.pieces, encodeLopn_adcxhi3 _ _ _ _ _ _ _ hO], ?_⟩
    intro q hq
    simp only [SArm.pieces, List.mem_singleton] at hq
    subst hq
    exact pieceDec_setc _ (gpNumU_lt_16 O)

/-- The computed shape of a slot carry arm's instruction decodes to its machine
    instructions. -/
theorem SArm.shape_ops {P : Params} {c : SArm} (h : c.ok P = true) {sh : DShape}
    (hs : shapeOf P c.instr = some sh) : sh.ops' = c.js P := by
  obtain ⟨hb, hp⟩ := c.bytes P h
  cases c <;> exact shapeOf_lopn_ops _ hb hp hs

/-- The machine word of an operand: the word at its frame address for a slot, its register
    otherwise. -/
def valM (P : Params) (rsp : BitVec 64) (sa : AState) (x : String) : BitVec 64 :=
  if isSpillOrQsave x then read64 sa.mem (rsp + BitVec.ofInt 64 (slotOff P x))
  else sa.regs (phys x)

theorem sepB_disj {off : Int} (h : sepB cmovRedZone off = true) (rsp : BitVec 64) :
    Disjoint8 (redW rsp) (rsp + BitVec.ofInt 64 off) := by
  simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact disjoint8_add_ofInt rsp cmovRedZone off h.1 h.2

/-- An operand of a slot carry arm reads, on the address machine, its machine word. -/
theorem wordA_valM {P : Params} {rsp : BitVec 64} {sa : AState} {s : LstateA}
    (hc : ACorrW rsp sa s) {x : String} (hk : kOk P x = true)
    (hw : gpOk x = true → (s.reg.lvm x).1 ≠ 1) :
    wordA (frameP P rsp) s x = some (valM P rsp sa x) := by
  rcases kOk_cases hk with hg | ⟨off, hoff, -, hsep⟩
  · simp [wordA, frameP_gp hg, valM, (gpFacts hg).notSlot, hc.wide hg (hw hg)]
  · obtain ⟨hs, -, -⟩ := slot_facts hoff
    simp only [wordA, frameP, hoff, Option.map_some, valM, hs, if_true,
      show slotOff P x = off by simp [slotOff, hoff]]
    rw [read64_eq_of_agree hc.mem (sepB_disj hsep rsp)]

/-- `adcx off(%b), %d` writes the word of `x86_ADCX` to `d` and its carry to the carry flag. -/
theorem evalInstrA_adcxMem (sa : AState) (d b : String) (off : Int) :
    (evalInstrA sa (.adcxMem d b off)).regs = (fun r => if r = d then
        (x86_ADCX (sa.regs d) (read64 sa.mem (sa.regs b + BitVec.ofInt 64 off))
          (sa.flags.cf.getD false)).2 else sa.regs r)
      ∧ (evalInstrA sa (.adcxMem d b off)).mem = sa.mem
      ∧ (evalInstrA sa (.adcxMem d b off)).flags.cf
        = (x86_ADCX (sa.regs d) (read64 sa.mem (sa.regs b + BitVec.ofInt 64 off))
            (sa.flags.cf.getD false)).1 := by
  refine ⟨?_, evalInstrA_mem_of_noWriteB sa _ rfl, ?_⟩ <;>
    simp [evalInstrA, evalInstr, AState.view, JState.flagB, JState.load]

/-- The copy of `A` into the accumulator `acc`, when it is laid down, writes the machine word
    of `A` to `acc` and keeps the memory and the flags. -/
theorem run_sMv (P : Params) (rsp : BitVec 64) (D A : String) (acc : Nat) (sa : AState)
    (hsp : sa.regs "%rsp" = rsp)
    (hlay : isSpillOrQsave A = true ∨ ¬ (A = D ∧ acc = gpNumU D)) :
    (∀ r, (aMachine.runBlock sa ((sMv P D A acc).map Prod.snd)).regs r
        = if r = SailX86Decoder.regName acc then valM P rsp sa A else sa.regs r)
      ∧ (aMachine.runBlock sa ((sMv P D A acc).map Prod.snd)).mem = sa.mem
      ∧ (aMachine.runBlock sa ((sMv P D A acc).map Prod.snd)).flags = sa.flags := by
  unfold sMv
  split
  · rename_i hs
    obtain ⟨hregs, hmem⟩ := evalInstrA_loadMem_eq sa (SailX86Decoder.regName acc) "%rsp"
      (slotOff P A)
    refine ⟨fun r => ?_, hmem, rfl⟩
    show (evalInstrA sa _).regs r = _
    rw [hregs, hsp]
    simp [valM, hs]
  · rename_i hs
    have hlay' := hlay.resolve_left (by simp [hs])
    rw [if_neg hlay']
    refine ⟨fun r => ?_, evalInstrA_mem_of_noWriteB sa _ rfl, rfl⟩
    show (evalInstrA sa _).regs r = _
    simp [valM, hs]
    rfl

/-- The add of `S` into the accumulator `acc` writes the word of `x86_ADCX` of the
    accumulator, the machine word of `S` and the carry flag to `acc`, and its carry to the
    carry flag. -/
theorem run_sAd (P : Params) (rsp : BitVec 64) (S : String) (acc : Nat) (sa : AState)
    (hsp : sa.regs "%rsp" = rsp) :
    (∀ r, (aMachine.runBlock sa ((sAd P S acc).map Prod.snd)).regs r
        = if r = SailX86Decoder.regName acc then
            (x86_ADCX (sa.regs (SailX86Decoder.regName acc)) (valM P rsp sa S)
              (sa.flags.cf.getD false)).2 else sa.regs r)
      ∧ (aMachine.runBlock sa ((sAd P S acc).map Prod.snd)).mem = sa.mem
      ∧ (aMachine.runBlock sa ((sAd P S acc).map Prod.snd)).flags.cf
        = (x86_ADCX (sa.regs (SailX86Decoder.regName acc)) (valM P rsp sa S)
            (sa.flags.cf.getD false)).1 := by
  unfold sAd
  split
  · rename_i hs
    obtain ⟨hr, hm, hf⟩ := evalInstrA_adcxMem sa (SailX86Decoder.regName acc) "%rsp" (slotOff P S)
    refine ⟨fun r => ?_, hm, ?_⟩
    · show (evalInstrA sa _).regs r = _
      rw [hr, hsp]
      simp [valM, hs]
    · show (evalInstrA sa _).flags.cf = _
      rw [hf, hsp]
      simp [valM, hs]
  · rename_i hs
    obtain ⟨hr, hm, hf⟩ := evalInstrA_adcx sa (SailX86Decoder.regName acc) (phys S)
    refine ⟨fun r => ?_, hm, ?_⟩
    · show (evalInstrA sa _).regs r = _
      rw [hr]
      simp [valM, hs]
    · show (evalInstrA sa _).flags.cf = _
      rw [hf]
      simp [valM, hs]

/-- A slot operand has a frame address. -/
theorem kOk_frame {P : Params} {x : String} (hk : kOk P x = true)
    (hs : isSpillOrQsave x = true) (rsp : BitVec 64) : (frameP P rsp x).isSome = true := by
  rcases kOk_cases hk with hg | ⟨off, hoff, -, -⟩
  · simp [(gpFacts hg).notSlot] at hs
  · simp [frameP, hoff]

/-- Some operand of a slot carry arm is a slot, which the address machine sees. -/
theorem slot_seen {P : Params} {D A S : String} (hD : kOk P D = true) (hA : kOk P A = true)
    (hS : kOk P S = true)
    (h : isSpillOrQsave D = true ∨ isSpillOrQsave A = true ∨ isSpillOrQsave S = true)
    (rsp : BitVec 64) :
    ((frameP P rsp D).isSome || (frameP P rsp A).isSome || (frameP P rsp S).isSome) = true := by
  rcases h with h | h | h <;> simp [kOk_frame _ h rsp, *]

/-- A word the address machine reads off a name other than `D` survives a write to `D` that
    keeps the memory. -/
theorem wordA_setReg {frame : String → Option (BitVec 64)} {s : LstateA} {D x : String}
    (hx : x ≠ D) {w : Nat} (v : BitVec w) :
    wordA frame { s with reg := (s.reg.setReg D v).nextPc } x = wordA frame s x := by
  unfold wordA
  split
  · rfl
  · show (s.reg.setReg D v).nextPc.getW x 64 = _
    rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ hx]

/-- **The slot carry add into a register.** From `ACorrW`, the address-machine step of
    `ADCX:64 D, A, S, C` with `D` a register and a slot among `A`, `S` is matched by the
    reload or copy of `A` into `D`, `bt $0, C` and `adcx` from the slot or register `S`. -/
theorem sim_sadcx_reg (P : Params) (rsp : BitVec 64) (D A S C : String)
    (h : (SArm.adcx D A S C).ok P = true) (hDg : gpOk D = true) (sa : AState) (s : LstateA)
    (zf : Bool) (hc : ACorrW rsp sa s) (hwA : gpOk A = true → (s.reg.lvm A).1 ≠ 1)
    (hwS : gpOk S = true → (s.reg.lvm S).1 ≠ 1) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((SArm.adcx D A S C).instr, .reg none) s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((SArm.adcx D A S C).js P)) s' ∧ zf' = zf
      ∧ (D ≠ A → D ≠ S → D ≠ C →
          CarryAt (frameP P rsp) (aMachine.runBlock sa ((SArm.adcx D A S C).js P)) s' A S C) := by
  simp only [SArm.ok, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hC, hAC⟩, hSC⟩, hD⟩, hA⟩, hS⟩, hsl0⟩, hal⟩ := h
  have hDs : isSpillOrQsave D = false := (gpFacts hDg).notSlot
  have hfD : frameP P rsp D = none := frameP_gp hDg
  set va := valM P rsp sa A with hva
  set vb := valM P rsp sa S with hvb
  have hA' := wordA_valM hc hA hwA
  have hS' := wordA_valM hc hS hwS
  rw [SArm.instr, fstepA_adcxSlot _ D A S C s zf (slot_seen hD hA hS (by simp_all) rsp) hA' hS']
    at hst
  cases hgc : s.reg.getW C 1 with
  | none => rw [hgc] at hst; cases hst
  | some vc =>
  rw [hgc] at hst
  simp only [Option.map_some, hfD, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  have hmC := hc.bit hC hgc
  set bit := vc.getLsbD 0 with hbit
  have hCD : C ≠ D := by
    intro e; subst e
    rcases hal with (hal | ⟨rfl, -⟩) | ⟨-, hal⟩
    · simp [hDs] at hal
    · exact hAC rfl
    · exact hal rfl
  have hsp := hc.sp
  -- the machine run: the copy of `A`, `bt`, the add
  have hjs : (SArm.adcx D A S C).js P
      = (sMv P D A (gpNumU D)).map Prod.snd ++ (.bt (phys C) (.imm 0)
        :: (sAd P S (gpNumU D)).map Prod.snd) := by
    simp [SArm.js, SArm.pieces, hDs, List.map_append]
  have hpD : SailX86Decoder.regName (gpNumU D) = phys D := rfl
  set sa1 := aMachine.runBlock sa ((sMv P D A (gpNumU D)).map Prod.snd) with hsa1
  obtain ⟨r1D, r1o, m1, f1⟩ : sa1.regs (phys D) = va ∧ (∀ r, r ≠ phys D → sa1.regs r = sa.regs r)
      ∧ sa1.mem = sa.mem ∧ sa1.flags = sa.flags := by
    by_cases hlay : isSpillOrQsave A = true ∨ ¬ (A = D ∧ gpNumU D = gpNumU D)
    · obtain ⟨hr, hm, hf⟩ := run_sMv P rsp D A (gpNumU D) sa hsp hlay
      refine ⟨by rw [hr, hpD, if_pos rfl], fun r hr' => by rw [hr, hpD, if_neg hr'], hm, hf⟩
    · simp only [not_or, Bool.not_eq_true, not_not] at hlay
      obtain ⟨hAs, rfl, -⟩ := hlay
      have he : sMv P A A (gpNumU A) = [] := by simp [sMv, hAs]
      rw [hsa1, he]
      exact ⟨by simp [hva, valM, hAs], fun _ _ => rfl, rfl, rfl⟩
  set sa2 := evalInstrA sa1 (.bt (phys C) (.imm 0)) with hsa2
  obtain ⟨r2, m2, c2⟩ : sa2.regs = sa1.regs ∧ sa2.mem = sa1.mem
      ∧ sa2.flags.cf = some ((sa1.regs (phys C)).getLsbD 0) := evalInstrA_bt0 sa1 (phys C)
  have hC1 : sa1.regs (phys C) = vc.setWidth 64 := by
    rw [r1o _ (fun e => hCD (phys_inj hC hDg e)), hmC]
  have hcf2 : sa2.flags.cf.getD false = bit := by
    rw [c2, hC1]; simp [hbit]
  have hsp2 : sa2.regs "%rsp" = rsp := by
    rw [r2, r1o _ (fun e => (gpFacts hDg).physNe e.symm), hsp]
  have hvb2 : valM P rsp sa2 S = vb := by
    by_cases hSs : isSpillOrQsave S = true
    · simp [valM, hSs, m2, m1, hvb]
    · have hSg : gpOk S = true := by
        rcases kOk_cases hS with hg | ⟨off, hoff, -, -⟩
        · exact hg
        · exact absurd (slot_facts hoff).1 hSs
      simp only [valM, hSs, Bool.false_eq_true, if_false, hvb, r2]
      by_cases hSD : S = D
      · subst hSD
        rcases hal with (hal | ⟨rfl, -⟩) | ⟨hal, -⟩
        · simp [hDs] at hal
        · rw [r1D]; simp [hva, valM, (gpFacts hDg).notSlot]
        · exact absurd rfl hal
      · rw [r1o _ (fun e => hSD (phys_inj hSg hDg e))]
  obtain ⟨r3, m3, c3⟩ := run_sAd P rsp S (gpNumU D) sa2 hsp2
  rw [hpD, r2, r1D, hvb2, hcf2] at r3 c3
  have hword : (x86_ADCX va vb bit).2 = VIR.JasminDialect.addCarryWord va vb vc := by
    rw [addCarryWord_eq]; rfl
  rw [hjs, RInstrSemantics.Machine.runBlock_append, RInstrSemantics.Machine.runBlock_cons]
  change ACorrW rsp (aMachine.runBlock sa2 _) _ ∧ _
  refine ⟨hc.write hDg (VIR.JasminDialect.addCarryWord va vb vc) (fun r => ?_) (fun x hx => ?_)
    (fun r hr => ?_) ?_, rfl, fun hDA hDS hDC => ⟨(waddcarry va vb bit).1, ?_,
      fun va' vb' vc' ha hb hcc => ?_⟩⟩
  · rw [r3, ← hword]
    split
    · rfl
    · rename_i hne; exact r1o _ hne
  · rw [m3, m2, m1]; exact hc.mem x hx
  · show (s.reg.setReg D _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr]
  · left
    exact getW_setReg_nextPcN s.reg D D _ |>.trans (if_pos rfl)
  · exact c3
  · rw [wordA_setReg (Ne.symm hDA)] at ha
    rw [wordA_setReg (Ne.symm hDS)] at hb
    have eC : (s.reg.setReg D (VIR.JasminDialect.addCarryWord va vb vc)).nextPc.getW C 1
        = some vc := by
      rw [LstateN.getW_nextPc, LstateN.getW_setReg_other _ _ _ _ _ (Ne.symm hDC)]; exact hgc
    have e1 := ha.symm.trans hA'
    have e2 := hb.symm.trans hS'
    have e3 := hcc.symm.trans eC
    simp_all

/-- The scratch register is one of `RAX`, `RBX`, `RCX`, `RDX` and none of `A`, `S`, `C`. -/
theorem scratchS_spec (A S C : String) :
    gpOk (scratchS A S C) = true ∧ scratchS A S C ≠ A ∧ scratchS A S C ≠ S
      ∧ scratchS A S C ≠ C := by
  have hmem : scratchS A S C ∈ ["RAX", "RBX", "RCX", "RDX"].filter
      (fun r => !([A, S, C].contains r)) := by
    rw [scratch_filter A S C]; exact List.mem_cons_self
  rw [List.mem_filter] at hmem
  obtain ⟨h1, h2⟩ := hmem
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.not_eq_true',
    Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h2
  refine ⟨?_, fun e => h2.1 e, fun e => h2.2.1 e, fun e => h2.2.2 e⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
  rcases h1 with h | h | h | h <;> rw [h] <;> decide

/-- A word the address machine reads off a name whose frame address is disjoint from `ad`
    survives a store at `ad`. -/
theorem wordA_write {frame : String → Option (BitVec 64)} {s : LstateA} {ad : BitVec 64}
    {x : String} (hx : ∀ ax, frame x = some ax → Disjoint8 ad ax) (v : BitVec 64) :
    wordA frame { s with reg := s.reg.nextPc, mem := write64 s.mem ad v } x = wordA frame s x := by
  unfold wordA
  split
  · rename_i ax hax
    simp only [Option.some.injEq]
    exact read64_write64_of_disjoint _ _ _ _ (hx ax hax)
  · exact LstateN.getW_nextPc _ _ _

/-- `mov %x, off(%b)` keeps the registers and the flags. -/
theorem evalInstrA_storeMem_flags (sa : AState) (b x : String) (off : Int) :
    (evalInstrA sa (.storeMem b off (.reg x))).flags = sa.flags := rfl

/-- `mov off(%b), %d` keeps the flags. -/
theorem evalInstrA_loadMem_flags (sa : AState) (d b : String) (off : Int) :
    (evalInstrA sa (.loadMem d b off)).flags = sa.flags := rfl

/-- **The slot carry add into a slot.** From `ACorrW`, the address-machine step of
    `ADCX:64 D, A, S, C` with `D` a frame slot is matched by `bt $0, C`, the save of the
    scratch in the red-zone word, the reload or copy of `A` into the scratch, `adcx` from the
    slot or register `S`, the store into the slot of `D` and the restore of the scratch. -/
theorem sim_sadcx_slot (P : Params) (rsp : BitVec 64) (D A S C : String)
    (h : (SArm.adcx D A S C).ok P = true) (hDs : isSpillOrQsave D = true) (sa : AState)
    (s : LstateA) (zf : Bool) (hc : ACorrW rsp sa s) (hwA : gpOk A = true → (s.reg.lvm A).1 ≠ 1)
    (hwS : gpOk S = true → (s.reg.lvm S).1 ≠ 1) (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((SArm.adcx D A S C).instr, .reg none) s zf = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((SArm.adcx D A S C).js P)) s' ∧ zf' = zf
      ∧ (D ≠ A → D ≠ S → D ≠ C →
          (isSpillOrQsave A = true → sepB (slotOff P D) (slotOff P A) = true) →
          (isSpillOrQsave S = true → sepB (slotOff P D) (slotOff P S) = true) →
          CarryAt (frameP P rsp) (aMachine.runBlock sa ((SArm.adcx D A S C).js P)) s' A S C) := by
  simp only [SArm.ok, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hC, hAC⟩, hSC⟩, hD⟩, hA⟩, hS⟩, -⟩, -⟩ := h
  obtain ⟨offD, hoD, -, hsepD⟩ : ∃ off, spillQsaveOff P.frame P.spillW D P.qsaveB = some off
      ∧ dispOk32 off = true ∧ sepB cmovRedZone off = true := by
    rcases kOk_cases hD with hg | h
    · simp [(gpFacts hg).notSlot] at hDs
    · exact h
  have hsD : slotOff P D = offD := by simp [slotOff, hoD]
  set aD := rsp + BitVec.ofInt 64 offD with haD
  have hfD : frameP P rsp D = some aD := by simp [frameP, hoD, haD]
  set va := valM P rsp sa A with hva
  set vb := valM P rsp sa S with hvb
  have hA' := wordA_valM hc hA hwA
  have hS' := wordA_valM hc hS hwS
  rw [SArm.instr, fstepA_adcxSlot _ D A S C s zf (by simp [hfD]) hA' hS'] at hst
  cases hgc : s.reg.getW C 1 with
  | none => rw [hgc] at hst; cases hst
  | some vc =>
  rw [hgc] at hst
  simp only [Option.map_some, hfD, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  have hmC := hc.bit hC hgc
  set bit := vc.getLsbD 0 with hbit
  have hsp := hc.sp
  obtain ⟨hRg, hRA, hRS, hRC⟩ := scratchS_spec A S C
  set R := SailX86Decoder.regName (gpNumU (scratchS A S C)) with hR
  have hRp : R = phys (scratchS A S C) := rfl
  have hRne : ∀ x, gpOk x = true → x ≠ scratchS A S C → phys x ≠ R := fun x hx hne e =>
    hne (phys_inj hx hRg (e.trans hRp))
  have hRsp : R ≠ "%rsp" := by rw [hRp]; exact (gpFacts hRg).physNe
  have hsepRA : isSpillOrQsave A = true → Disjoint8 (redW rsp)
      (rsp + BitVec.ofInt 64 (slotOff P A)) := fun hs => by
    rcases kOk_cases hA with hg | ⟨off, hoff, -, hsep⟩
    · simp [(gpFacts hg).notSlot] at hs
    · rw [show slotOff P A = off by simp [slotOff, hoff]]; exact sepB_disj hsep rsp
  have hsepRS : isSpillOrQsave S = true → Disjoint8 (redW rsp)
      (rsp + BitVec.ofInt 64 (slotOff P S)) := fun hs => by
    rcases kOk_cases hS with hg | ⟨off, hoff, -, hsep⟩
    · simp [(gpFacts hg).notSlot] at hs
    · rw [show slotOff P S = off by simp [slotOff, hoff]]; exact sepB_disj hsep rsp
  -- the run
  have hjs : (SArm.adcx D A S C).js P
      = .bt (phys C) (.imm 0) :: .storeMem "%rsp" cmovRedZone (.reg R)
        :: ((sMv P D A (gpNumU (scratchS A S C))).map Prod.snd
          ++ (sAd P S (gpNumU (scratchS A S C))).map Prod.snd
          ++ [.storeMem "%rsp" (slotOff P D) (.reg R), .loadMem R "%rsp" cmovRedZone]) := by
    simp [SArm.js, SArm.pieces, hDs, List.map_append, hR]
  set sa1 := evalInstrA sa (.bt (phys C) (.imm 0)) with hsa1
  obtain ⟨r1, m1, c1⟩ : sa1.regs = sa.regs ∧ sa1.mem = sa.mem
      ∧ sa1.flags.cf = some ((sa.regs (phys C)).getLsbD 0) := evalInstrA_bt0 sa (phys C)
  set sa2 := evalInstrA sa1 (.storeMem "%rsp" cmovRedZone (.reg R)) with hsa2
  obtain ⟨r2, m2⟩ := evalInstrA_storeMem_eq sa1 "%rsp" R cmovRedZone
  rw [← hsa2] at r2 m2
  have f2 : sa2.flags = sa1.flags := evalInstrA_storeMem_flags _ _ _ _
  rw [r1, m1, hsp] at m2
  set old := sa.regs R with hold
  have hsp2 : sa2.regs "%rsp" = rsp := by rw [r2, r1, hsp]
  set sa3 := aMachine.runBlock sa2 ((sMv P D A (gpNumU (scratchS A S C))).map Prod.snd)
    with hsa3
  have hlay : isSpillOrQsave A = true ∨ ¬ (A = D ∧ gpNumU (scratchS A S C) = gpNumU D) := by
    by_cases hAs : isSpillOrQsave A = true
    · exact Or.inl hAs
    · right; rintro ⟨rfl, -⟩; exact hAs hDs
  obtain ⟨r3, m3, f3⟩ := run_sMv P rsp D A (gpNumU (scratchS A S C)) sa2 hsp2 hlay
  rw [← hsa3] at r3 m3 f3
  have hva3 : valM P rsp sa2 A = va := by
    by_cases hAs : isSpillOrQsave A = true
    · simp only [valM, hAs, if_true, hva, m2]
      exact read64_write64_of_disjoint _ _ _ _ (hsepRA hAs)
    · have hAg : gpOk A = true := by
        rcases kOk_cases hA with hg | ⟨off, hoff, -, -⟩
        · exact hg
        · exact absurd (slot_facts hoff).1 hAs
      simp only [valM, hAs, Bool.false_eq_true, if_false, hva, r2, r1]
  set sa4 := aMachine.runBlock sa3 ((sAd P S (gpNumU (scratchS A S C))).map Prod.snd) with hsa4
  have hsp3 : sa3.regs "%rsp" = rsp := by rw [r3, if_neg (Ne.symm hRsp), hsp2]
  obtain ⟨r4, m4, c4⟩ := run_sAd P rsp S (gpNumU (scratchS A S C)) sa3 hsp3
  rw [← hsa4] at r4 m4 c4
  have hvb3 : valM P rsp sa3 S = vb := by
    by_cases hSs : isSpillOrQsave S = true
    · simp only [valM, hSs, if_true, hvb, m3, m2]
      exact read64_write64_of_disjoint _ _ _ _ (hsepRS hSs)
    · have hSg : gpOk S = true := by
        rcases kOk_cases hS with hg | ⟨off, hoff, -, -⟩
        · exact hg
        · exact absurd (slot_facts hoff).1 hSs
      simp only [valM, hSs, Bool.false_eq_true, if_false, hvb]
      rw [r3, if_neg (hRne S hSg (Ne.symm hRS)), r2, r1]
  have hcf3 : sa3.flags.cf.getD false = bit := by
    rw [f3, f2, c1, hmC]; simp [hbit]
  rw [show sa3.regs R = va by rw [r3, if_pos rfl, hva3], hvb3, hcf3] at r4 c4
  set res := (x86_ADCX va vb bit).2 with hres
  set sa5 := evalInstrA sa4 (.storeMem "%rsp" (slotOff P D) (.reg R)) with hsa5
  obtain ⟨r5, m5⟩ := evalInstrA_storeMem_eq sa4 "%rsp" R (slotOff P D)
  rw [← hsa5] at r5 m5
  have hsp4 : sa4.regs "%rsp" = rsp := by rw [r4, if_neg (Ne.symm hRsp), hsp3]
  rw [hsp4, hsD, r4, if_pos rfl] at m5
  set sa6 := evalInstrA sa5 (.loadMem R "%rsp" cmovRedZone) with hsa6
  obtain ⟨r6, m6⟩ := evalInstrA_loadMem_eq sa5 R "%rsp" cmovRedZone
  rw [← hsa6] at r6 m6
  have hsp5 : sa5.regs "%rsp" = rsp := by rw [r5, hsp4]
  have hDisD : Disjoint8 aD (redW rsp) := by
    have := sepB_disj hsepD rsp
    exact ⟨this.2, this.1⟩
  have hrest : read64 sa5.mem (sa5.regs "%rsp" + BitVec.ofInt 64 cmovRedZone) = old := by
    rw [hsp5, m5, m4, m3, m2]
    show read64 (write64 (write64 sa.mem (redW rsp) old) aD res) (redW rsp) = old
    rw [read64_write64_of_disjoint _ _ _ _ hDisD, read64_write64_same]
  have hrun : aMachine.runBlock sa ((SArm.adcx D A S C).js P) = sa6 := by
    rw [hjs, RInstrSemantics.Machine.runBlock_cons, RInstrSemantics.Machine.runBlock_cons,
      RInstrSemantics.Machine.runBlock_append, RInstrSemantics.Machine.runBlock_append]
    rfl
  have hword : res = VIR.JasminDialect.addCarryWord va vb vc := by
    rw [hres, addCarryWord_eq]; rfl
  rw [hrun]
  have hregs6 : sa6.regs = sa.regs := by
    funext r
    rw [r6, hrest, r5, r4]
    by_cases hr : r = R
    · subst hr; rw [if_pos rfl]
    · rw [if_neg hr, if_neg hr, r3, if_neg hr, r2, r1]
  have hmem6 : sa6.mem = write64 (write64 sa.mem (redW rsp) old) aD res := by
    rw [m6, m5, m4, m3, m2]; rfl
  refine ⟨⟨fun r hr => ?_, by rw [hregs6]; exact hsp, fun x hx => ?_⟩, rfl,
    fun hDA hDS hDC hsA hsS => ⟨(waddcarry va vb bit).1, ?_, fun va' vb' vc' ha hb hcc => ?_⟩⟩
  · rw [hregs6]
    show s.reg.nextPc.getW r 64 = _ ∨ ∃ b : BitVec 1, s.reg.nextPc.lvm r = ⟨1, b⟩ ∧ _
    rw [LstateN.getW_nextPc]
    exact hc.regs r hr
  · show write64 s.mem aD _ x = _
    rw [hmem6, ← hword]
    refine agree_write64 (fun y hy => ?_) _ _ x hx
    rw [write64_of_not_inRange _ _ _ _ hy]
    exact hc.mem y hy
  · show sa6.flags.cf = _
    rw [evalInstrA_loadMem_flags, evalInstrA_storeMem_flags, c4]
    rfl
  · have hdisA : ∀ ax, frameP P rsp A = some ax → Disjoint8 aD ax := by
      intro ax hax
      simp only [frameP, Option.map_eq_some_iff] at hax
      obtain ⟨off, hoff, rfl⟩ := hax
      have hAs := (slot_facts hoff).1
      have hsep := hsA hAs
      rw [hsD, show slotOff P A = off by simp [slotOff, hoff]] at hsep
      simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at hsep
      exact disjoint8_add_ofInt rsp offD off hsep.1 hsep.2
    have hdisS : ∀ ax, frameP P rsp S = some ax → Disjoint8 aD ax := by
      intro ax hax
      simp only [frameP, Option.map_eq_some_iff] at hax
      obtain ⟨off, hoff, rfl⟩ := hax
      have hSs := (slot_facts hoff).1
      have hsep := hsS hSs
      rw [hsD, show slotOff P S = off by simp [slotOff, hoff]] at hsep
      simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at hsep
      exact disjoint8_add_ofInt rsp offD off hsep.1 hsep.2
    rw [wordA_write hdisA] at ha
    rw [wordA_write hdisS] at hb
    have eC : s.reg.nextPc.getW C 1 = some vc := by rw [LstateN.getW_nextPc]; exact hgc
    have e1 := ha.symm.trans hA'
    have e2 := hb.symm.trans hS'
    have e3 := hcc.symm.trans eC
    simp_all

/-- **The slot carry-out binding.** From `ACorrW`, with the machine carry flag holding the
    carry-out of `A + S + C` on the address-machine words, the step of `ADCXHI:64 O, A, S, C`
    with a slot among `A`, `S` is matched by `setc O`: the registers end related by `ACorrW`,
    and the zero flag and the machine flags are kept. -/
theorem sim_sadcxhi (P : Params) (rsp : BitVec 64) (O A S C : String)
    (h : (SArm.adcxhi O A S C).ok P = true) (sa : AState) (s : LstateA) (zf : Bool)
    (hc : ACorrW rsp sa s) (hwA : gpOk A = true → (s.reg.lvm A).1 ≠ 1)
    (hwS : gpOk S = true → (s.reg.lvm S).1 ≠ 1) (hcy : CarryAt (frameP P rsp) sa s A S C)
    (s' : LstateA) (zf' : Bool)
    (hst : fstepA (frameP P rsp) ((SArm.adcxhi O A S C).instr, .reg none) s zf
      = some (s', zf')) :
    ACorrW rsp (aMachine.runBlock sa ((SArm.adcxhi O A S C).js P)) s' ∧ zf' = zf
      ∧ (aMachine.runBlock sa ((SArm.adcxhi O A S C).js P)).flags = sa.flags := by
  simp only [SArm.ok, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hO, hC⟩, -⟩, -⟩, hA⟩, hS⟩, hsl0⟩ := h
  have hA' := wordA_valM hc hA hwA
  have hS' := wordA_valM hc hS hwS
  have hsl : ((frameP P rsp O).isSome || (frameP P rsp A).isSome
      || (frameP P rsp S).isSome) = true := by
    rcases hsl0 with h | h
    · simp [kOk_frame hA h rsp]
    · simp [kOk_frame hS h rsp]
  rw [SArm.instr, fstepA_adcxhiSlot _ O A S C s zf hsl hA' hS'] at hst
  cases hgc : s.reg.getW C 1 with
  | none => rw [hgc] at hst; cases hst
  | some vc =>
  rw [hgc] at hst
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hst
  obtain ⟨rfl, rfl⟩ := hst
  obtain ⟨co, hcf, hco⟩ := hcy
  have hco' := hco _ _ _ hA' hS' hgc
  obtain ⟨r1, m1, f1⟩ := evalInstrA_setc sa (phys O)
  have hrun : aMachine.runBlock sa ((SArm.adcxhi O A S C).js P)
      = evalInstrA sa (.setc (phys O)) := rfl
  rw [hrun]
  refine ⟨hc.write hO (if co then 1 else 0) (fun r => ?_) (fun x hx => ?_) (fun r hr => ?_) ?_,
    rfl, f1⟩
  · rw [r1, hcf]; rfl
  · rw [m1]; exact hc.mem x hx
  · show (s.reg.setReg O _).nextPc.lvm r = _
    simp [LstateN.nextPc, LstateN.setReg, hr]
  · right
    refine ⟨VIR.JasminDialect.carryOutBit (valM P rsp sa A) (valM P rsp sa S) vc, ?_, ?_⟩
    · show (if O = O then _ else _) = _
      rw [if_pos rfl]
    · rw [carryOutBit_eq, hco']
      cases co <;> decide

/-! ## 9. The covered bodies with carry chains -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep (aMachine_step_op)

/-- The carry arm of an instruction: `ADCX:64` and `ADCXHI:64` on three register sources. -/
def classifyC : LinstrR → Option CArm
  | .Lopn [.reg d] m [.reg a, .reg s, .reg c] =>
      if m = "ADCX:64" then some (.adcx d a s c)
      else if m = "ADCXHI:64" then some (.adcxhi d a s c) else none
  | _ => none

theorem classifyC_instr {i : LinstrR} {c : CArm} (h : classifyC i = some c) : c.instr = i := by
  unfold classifyC at h
  split at h
  · split_ifs at h with h1 h2
    · obtain rfl := Option.some.inj h; subst h1; rfl
    · obtain rfl := Option.some.inj h; subst h2; rfl
  · cases h

/-- The one-bit carry-in names an instruction reads: the carry-in of `ADCX:64` and
    `ADCXHI:64`, none for any other instruction. -/
def carryIns : LinstrR → List String
  | .Lopn [.reg _] m [.reg _, .reg _, .reg c] =>
      if m = "ADCX:64" ∨ m = "ADCXHI:64" then [c] else []
  | _ => []

theorem carryIns_of_classifyC {i : LinstrR} (h : classifyC i = none) : carryIns i = [] := by
  unfold carryIns
  split
  · simp only [classifyC] at h
    split_ifs at h with h1 h2
    simp [h1, h2]
  · rfl

/-- An instruction other than the closing return of a printed body with carry chains: an
    `Lopn` read into a carry arm or an arm of `DecodePrintedAddr` whose conditions hold, a
    label, or a conditional branch on the zero flag to a label the body defines. -/
def instrOKWB (body : Lcmd) (P : Params) : LinstrR → Bool
  | .Lopn ds o ss =>
      match classifyC (.Lopn ds o ss) with
      | some c => c.ok
      | none =>
          match classifyM (.Lopn ds o ss) with
          | some m => m.ok
          | none =>
              match classifyA (.Lopn ds o ss) with
              | some a => a.ok P
              | none => false
  | .Llabel _ _ => true
  | .Lcond (.reg cc) l => (condPol cc).isSome && (labelAt body l).isSome
  | _ => false

/-- A carry-out binding `ADCXHI:64 O, A, S, C` at position `k` directly follows the add
    `ADCX:64 D, A, S, C` on the same sources, whose destination is none of them. -/
def carryPrevB (body : Lcmd) (k : Nat) : Bool :=
  match body[k]? with
  | some ⟨_, .Lopn [.reg _] o [.reg a, .reg s, .reg c]⟩ =>
      if o = "ADCXHI:64" then
        k != 0 && (match body[k - 1]? with
          | some ⟨_, .Lopn [.reg d] o' [.reg a', .reg s', .reg c']⟩ =>
              o' == "ADCX:64" && a == a' && s == s' && c == c' && d != a && d != s && d != c
          | _ => false)
      else true
  | _ => true

/-- **The covered printed bodies with carry chains**: decodable, ending in the return, every
    other instruction a carry arm or in the fragment of `DecodePrintedCFG`, every conditional
    branch directly after a compare, and every carry-out binding directly after its add. -/
def printedAddrWB (body : Lcmd) : Bool :=
  decodableLcmd body && body.getLast?.any (fun r => isRetB r.li_i)
    && body.dropLast.all (fun i => instrOKWB body (Params.ofBody body) i.li_i)
    && (List.range body.length).all (condPrevB body)
    && (List.range body.length).all (carryPrevB body)

/-- At the program counter of `s`, no general-purpose name the instruction reads, other than
    a carry-in, holds a one-bit value. -/
def WideSafeAt (body : Lcmd) (s : LstateA) : Prop :=
  ∀ ii ds o ss, body[s.reg.lpc]? = some ⟨ii, .Lopn ds o ss⟩ →
    ∀ r, readsI (.Lopn ds o ss) r → gpOk r = true → r ∉ carryIns (.Lopn ds o ss) →
      (s.reg.lvm r).1 ≠ 1

/-- At the program counter of `s`, a cell load reads eight bytes disjoint from the red-zone
    word at `rsp`. -/
def CellSafeAt (rsp : BitVec 64) (body : Lcmd) (s : LstateA) : Prop :=
  ∀ ii D n B off p, body[s.reg.lpc]? = some ⟨ii, .Lopn [.reg D] "LOAD:64" [.reg n]⟩ →
    cellParts? n = some (B, off) → s.reg.getW B 64 = some p →
    Disjoint8 (redW rsp) (p + BitVec.ofNat 64 off)

/-- The run safety of a body with carry chains and cells: safe indexed loads, no one-bit
    name read besides a carry-in, and safe cell loads. -/
def SafeW (rsp : BitVec 64) (body : Lcmd) (s : LstateA) : Prop :=
  LoadSafeAt rsp body s ∧ WideSafeAt body s ∧ CellSafeAt rsp body s

/-- At position `k` a carry-out binding finds the carry-out of its add in the machine carry
    flag. -/
def CarryReq (frame : String → Option (BitVec 64)) (body : Lcmd) (k : Nat) (sa : AState)
    (s : LstateA) : Prop :=
  ∀ ii O A S C, body[k]? = some ⟨ii, .Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]⟩ →
    CarryAt frame sa s A S C

/-- The facts of a body in the class `printedAddrWB` that the simulation reads. -/
structure BodyFactsW (body : Lcmd) (shs : List DShape) : Prop where
  /-- The shapes of the body. -/
  shapes : shapesOf (Params.ofBody body) body = some shs
  /-- The body is not empty. -/
  pos : 0 < body.length
  /-- The last instruction is the return. -/
  last : (body[body.length - 1]'(by omega)).li_i = .Lret
  /-- Every other instruction is covered. -/
  instr : ∀ k (hk : k + 1 < body.length),
    instrOKWB body (Params.ofBody body) (body[k]'(by omega)).li_i = true
  /-- Every conditional branch follows a compare. -/
  cond : ∀ k, k < body.length → condPrevB body k = true
  /-- Every carry-out binding follows its add. -/
  carry : ∀ k, k < body.length → carryPrevB body k = true

theorem acorrW_setLpc {rsp : BitVec 64} {sa : AState} {s : LstateA} (h : ACorrW rsp sa s)
    (p : Nat) : ACorrW rsp sa (s.setLpc p) :=
  ⟨h.regs, h.sp, h.mem⟩

theorem haltedA_eq_falseW {body : Lcmd} {shs : List DShape} (hF : BodyFactsW body shs)
    {s : LstateA} {k : Nat} (hpc : s.reg.lpc = k) (hk : k + 1 < body.length) :
    haltedA body s = false := by
  have hok := hF.instr k hk
  unfold haltedA
  rw [hpc, List.getElem?_eq_getElem (by omega)]
  revert hok
  rcases body[k] with ⟨ii, li⟩
  cases li <;> simp [instrOKWB]

/-- The instruction after one that is no add is no carry-out binding. -/
theorem no_carryReq {body : Lcmd} {shs : List DShape} (hF : BodyFactsW body shs) {k : Nat}
    (hk : k + 1 < body.length) (h : ∀ ii d a s c, body[k]? ≠
      some ⟨ii, .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c]⟩)
    (frame : String → Option (BitVec 64)) (sa : AState) (s : LstateA) :
    CarryReq frame body (k + 1) sa s := by
  intro ii O A S C hb
  have hc := hF.carry (k + 1) hk
  unfold carryPrevB at hc
  rw [hb] at hc
  simp only [if_true, Nat.add_sub_cancel] at hc
  split at hc
  · next ii' d o' a' s' c' heq =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨-, ⟨⟨⟨⟨⟨⟨ho, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩⟩ := hc
    subst ho
    exact absurd heq (h ii' d a' s' c')
  · simp at hc

/-- A carry-out binding is required at a label. -/
theorem carryReq_label {body : Lcmd} {k : Nat} {ii : Nat} {kd : LabelKind} {l : LLabel}
    (hb : body[k]? = some ⟨ii, .Llabel kd l⟩) (frame : String → Option (BitVec 64))
    (sa : AState) (s : LstateA) : CarryReq frame body k sa s := by
  intro ii' O A S C h
  rw [hb] at h
  simp at h

/-- The readsI of `normA i` are those of `i`. -/
theorem readsI_normA (i : LinstrR) (r : String) : readsI (normA i) r ↔ readsI i r := by
  cases i <;> simp [normA, readsI]

/-- An instruction on three register sources is no compare arm. -/
theorem classifyA_three_not_cmp (d m : String) (a s c : String) :
    (classifyA (.Lopn [.reg d] m [.reg a, .reg s, .reg c])).any cmpArmB = false := by
  simp [classifyA, cmpArmB, Option.any_map]

/-- The decoded instructions of an `Lopn` at position `k` run from its decoded index to the
    decoded index of `k + 1`. -/
theorem reaches_block {body : Lcmd} {shs : List DShape} (a b : JInstr 64) {k : Nat}
    (hks : k < shs.length) {ds : List LOperand} {o : String} {ss : List LOperand}
    (hshk : shapeOf (Params.ofBody body) (.Lopn ds o ss) = some shs[k]) {js : List (JInstr 64)}
    (hops : shs[k].ops' = js) {sa : AState} {e : Nat} {sa' : AState}
    (hR : Reaches aMachine (.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))
      (posOf shs (k + 1)) (aMachine.runBlock sa js) e sa') :
    Reaches aMachine (.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))
      (posOf shs k) sa e sa' := by
  obtain ⟨A, B, hsplit, hA⟩ := prog_split body shs a b k hks
  obtain ⟨hblk, hn⟩ := blkOf_lopn (body := body) (shs := shs) hshk
  have hprog : (RInstr.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))
      = A ++ js.map RInstr.op ++ B := by
    rw [hsplit, hblk, hops]
  have h0 := reaches_ops aMachine A js B sa
  rw [← hprog, hA] at h0
  have hpos : posOf shs (k + 1) = posOf shs k + js.length := by
    rw [posOf_succ shs k hks, hn, hops]
  rw [hpos] at hR
  exact h0.trans hR

/-- The instruction at position `k` of a body. -/
theorem body_get {body : Lcmd} {k : Nat} (hk : k < body.length) :
    body[k]? = some (body[k]'hk) := List.getElem?_eq_getElem hk

/-- **The run on both machines, with carry chains.** From states related by `ACorrW` at
    instruction `k` of a body in `printedAddrWB`, with the machine zero flag equal to the
    flag at a conditional branch and the machine carry flag holding the carry-out at a
    carry-out binding, every terminating run of the address machine whose indexed loads
    avoid the red-zone word and whose instructions read no one-bit name besides a carry-in
    is matched by a path of the machine on the decoded program from the index of `k` to the
    index of the closing return, ending in states related by `ACorrW`. -/
theorem run_simW {body : Lcmd} {shs : List DShape} (hF : BodyFactsW body shs) (rsp : BitVec 64)
    (a b : JInstr 64) :
    ∀ (fuel k : Nat) (sa : AState) (s : LstateA) (zf : Bool) (t : LstateA × Bool),
      s.reg.lpc = k → (hk : k < body.length) → ACorrW rsp sa s →
      (isCondB (body[k]'hk).li_i = true → sa.flags.zf.getD false = zf) →
      CarryReq (frameP (Params.ofBody body) rsp) body k sa s →
      runA (frameP (Params.ofBody body) rsp) body fuel s zf = some t →
      RunSafe (frameP (Params.ofBody body) rsp) body
        (SafeW rsp body) fuel s zf →
      ∃ sa', Reaches aMachine (.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))
          (posOf shs k) sa (posOf shs (body.length - 1)) sa' ∧ ACorrW rsp sa' t.1 := by
  set P := Params.ofBody body with hP
  set frame := frameP P rsp
  set prog : List RInstr := .op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret])
  obtain ⟨hl, hsh⟩ := shapesOf_spec P body shs hF.shapes
  -- the halt at the return
  have hhalt : ∀ (fuel : Nat) (sa : AState) (s : LstateA) (zf : Bool) (t : LstateA × Bool),
      s.reg.lpc = body.length - 1 → ACorrW rsp sa s →
      runA frame body fuel s zf = some t →
      ∃ sa', Reaches aMachine prog (posOf shs (body.length - 1)) sa
          (posOf shs (body.length - 1)) sa' ∧ ACorrW rsp sa' t.1 := by
    intro fuel sa s zf t hpc hc hrun
    have hh : haltedA body s = true := by
      unfold haltedA
      rw [hpc, List.getElem?_eq_getElem (by have := hF.pos; omega)]
      have := hF.last
      revert this
      rcases body[body.length - 1]'(by have := hF.pos; omega) with ⟨ii, li⟩
      intro h
      simp only at h
      subst h
      rfl
    rw [runA_halt _ _ _ _ _ hh] at hrun
    obtain rfl := Option.some.inj hrun
    exact ⟨sa, .refl _ _, hc⟩
  intro fuel
  induction fuel with
  | zero =>
    intro k sa s zf t hpc hk hc _ _ hrun _
    by_cases hkn : k + 1 < body.length
    · simp [runA, haltedA_eq_falseW hF hpc hkn] at hrun
    · have hk' : k = body.length - 1 := by omega
      subst hk'
      exact hhalt 0 sa s zf t hpc hc hrun
  | succ f ih =>
    intro k sa s zf t hpc hk hc hz hcy hrun hsafe
    by_cases hkn : k + 1 < body.length
    swap
    · have hk' : k = body.length - 1 := by omega
      subst hk'
      exact hhalt (f + 1) sa s zf t hpc hc hrun
    rw [runA_step _ _ _ _ _ (haltedA_eq_falseW hF hpc hkn)] at hrun
    have hok := hF.instr k hkn
    have hget : body[s.reg.lpc]? = some (body[k]'hk) := by
      rw [hpc]; exact List.getElem?_eq_getElem hk
    have hks : k < shs.length := by omega
    have hshk := hsh k hk hks
    -- the step of the address machine
    cases hst : stepA frame body s zf with
    | none => rw [hst] at hrun; cases hrun
    | some p =>
    obtain ⟨s', zf'⟩ := p
    rw [hst, Option.bind_some] at hrun
    have hsafe' := hsafe.2 s' zf' hst
    -- an instruction other than an add leaves no carry-out binding next
    have hnoadd : (∀ ii d a s c, body[k]? ≠
        some ⟨ii, .Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c]⟩) →
        ∀ sa s, CarryReq frame body (k + 1) sa s :=
      fun h sa s => no_carryReq hF hkn h frame sa s
    -- a conditional branch next follows a compare arm
    have hcondNext : isCondB (body[k + 1]'hkn).li_i = true →
        ((classifyA (body[k]'hk).li_i).any cmpArmB) = true := by
      intro hcnd
      have hc2 := hF.cond (k + 1) hkn
      unfold condPrevB at hc2
      rw [List.getElem?_eq_getElem hkn] at hc2
      revert hc2 hcnd
      rcases body[k + 1] with ⟨ii', li'⟩
      cases li' <;> simp [isCondB, List.getElem?_eq_getElem hk]
    rcases hbk : body[k]'hk with ⟨ii, li⟩
    rw [hbk] at hok hget hshk hz hcondNext
    simp only at hok hshk hz hcondNext
    have hbk? : body[k]? = some ⟨ii, li⟩ := by rw [body_get hk, hbk]
    cases li with
    | Lopn ds o ss =>
      have hstepEq : stepA frame body s zf
          = fstepA frame (normA (.Lopn ds o ss), tagA (.Lopn ds o ss)) s zf := by
        simp only [stepA, hget]
      rw [hstepEq] at hst
      have hws := hsafe.1.2.1 ii ds o ss (by rw [hget])
      simp only [instrOKWB] at hok
      split at hok
      · -- a carry arm
        rename_i c hcl
        have hia := classifyC_instr hcl
        cases c with
        | adcx D A S C =>
          simp only [CArm.instr] at hia
          simp only [← hia] at hst hws hshk hbk? hcondNext
          have hli : (normA (.Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C]),
              tagA (.Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C]))
              = ((CArm.adcx D A S C).instr, MemTag.reg none) := by
            simp (config := { decide := true }) [normA, tagA, CArm.instr]
          rw [hli] at hst
          have hok' := hok
          simp only [CArm.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok'
          obtain ⟨⟨⟨⟨⟨⟨-, hA⟩, hS⟩, -⟩, hAC⟩, hSC⟩, -⟩ := hok'
          have hwA : (s.reg.lvm A).1 ≠ 1 := hws A (reg_reads (by simp)) hA
            (by simp [carryIns, hAC])
          have hwS : (s.reg.lvm S).1 ≠ 1 := hws S (reg_reads (by simp)) hS
            (by simp [carryIns, hSC])
          obtain ⟨hc', hzz, hcyo⟩ := sim_adcx P rsp D A S C hok sa s zf hc hwA hwS s' zf' hst
          subst zf'
          have hpc' : s'.reg.lpc = k + 1 := by
            rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
          have hz' : isCondB (body[k + 1]'hkn).li_i = true →
              (aMachine.runBlock sa (CArm.adcx D A S C).js).flags.zf.getD false = zf := by
            intro hcnd
            have := hcondNext hcnd
            rw [classifyA_three_not_cmp] at this
            cases this
          have hcy' : CarryReq frame body (k + 1) (aMachine.runBlock sa (CArm.adcx D A S C).js)
              s' := by
            intro ii' O A' S' C' hb
            have hc2 := hF.carry (k + 1) hkn
            unfold carryPrevB at hc2
            rw [hb] at hc2
            simp only [if_true, Nat.add_sub_cancel, hbk?] at hc2
            simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
              Nat.add_one_ne_zero, not_false_eq_true, true_and] at hc2
            obtain ⟨⟨⟨⟨⟨⟨-, rfl⟩, rfl⟩, rfl⟩, hDA⟩, hDS⟩, hDC⟩ := hc2
            exact hcyo hDA hDS hDC
          obtain ⟨sa', hR, hC⟩ := ih (k + 1) _ s' zf t hpc' hkn hc' hz' hcy' hrun hsafe'
          refine ⟨sa', ?_, hC⟩
          have hops := CArm.shape_ops hok (by rw [show (CArm.adcx D A S C).instr
            = .Lopn [.reg D] "ADCX:64" [.reg A, .reg S, .reg C] from rfl]; exact hshk)
          exact reaches_block a b hks hshk hops hR
        | adcxhi O A S C =>
          simp only [CArm.instr] at hia
          simp only [← hia] at hst hws hshk hbk? hcondNext
          have hli : (normA (.Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]),
              tagA (.Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C]))
              = ((CArm.adcxhi O A S C).instr, MemTag.reg none) := by
            simp (config := { decide := true }) [normA, tagA, CArm.instr]
          rw [hli] at hst
          have hok' := hok
          simp only [CArm.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at hok'
          obtain ⟨⟨⟨⟨⟨-, hA⟩, hS⟩, -⟩, hAC⟩, hSC⟩ := hok'
          have hwA : (s.reg.lvm A).1 ≠ 1 := hws A (reg_reads (by simp)) hA
            (by simp [carryIns, hAC])
          have hwS : (s.reg.lvm S).1 ≠ 1 := hws S (reg_reads (by simp)) hS
            (by simp [carryIns, hSC])
          have hcyk := hcy ii O A S C hbk?
          obtain ⟨hc', hzz, hfl⟩ :=
            sim_adcxhi P rsp O A S C hok sa s zf hc hwA hwS hcyk s' zf' hst
          subst zf'
          have hpc' : s'.reg.lpc = k + 1 := by
            rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
          have hz' : isCondB (body[k + 1]'hkn).li_i = true →
              (aMachine.runBlock sa (CArm.adcxhi O A S C).js).flags.zf.getD false = zf := by
            intro hcnd
            have := hcondNext hcnd
            rw [classifyA_three_not_cmp] at this
            cases this
          have hcy' := hnoadd (fun ii' d a' s'' c' h => by
            rw [hbk?] at h
            simp at h) (aMachine.runBlock sa (CArm.adcxhi O A S C).js) s'
          obtain ⟨sa', hR, hC⟩ := ih (k + 1) _ s' zf t hpc' hkn hc' hz' hcy' hrun hsafe'
          refine ⟨sa', ?_, hC⟩
          have hops := CArm.shape_ops hok (by rw [show (CArm.adcxhi O A S C).instr
            = .Lopn [.reg O] "ADCXHI:64" [.reg A, .reg S, .reg C] from rfl]; exact hshk)
          exact reaches_block a b hks hshk hops hR
      · rename_i hclC
        have hnotadd : ∀ ii' d a' s'' c', body[k]? ≠
            some ⟨ii', .Lopn [.reg d] "ADCX:64" [.reg a', .reg s'', .reg c']⟩ := by
          intro ii' d a' s'' c' h
          rw [hbk?] at h
          simp only [Option.some.injEq, Linstr.mk.injEq] at h
          obtain ⟨-, h2⟩ := h
          rw [h2] at hclC
          simp [classifyC] at hclC
        split at hok
        · -- a cell arm
          rename_i m hclM
          have hia := classifyM_instr hclM
          have hli : (normA (.Lopn ds o ss), tagA (.Lopn ds o ss)) = (m.instr, MemTag.reg none) := by
            rw [← hia]
            cases m <;> simp (config := { decide := true }) [normA, tagA, MArm.instr]
          rw [hli] at hst
          have hz' : ∀ sa' : AState, isCondB (body[k + 1]'hkn).li_i = true →
              sa'.flags.zf.getD false = zf' := by
            intro sa' hcnd
            have hcm := hcondNext hcnd
            rw [← hia] at hcm
            cases m <;> simp [MArm.instr, classifyA, cmpArmB, Option.any_map, isMovM] at hcm
          have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
          cases m with
          | ldm D n B off =>
            have hok' := hok
            simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at hok'
            obtain ⟨⟨⟨hn, -⟩, hB⟩, -⟩ := hok'
            simp only [MArm.instr] at hia
            have hwB : (s.reg.lvm B).1 ≠ 1 := hws B (by rw [← hia]; exact cell_reads (by simp) hn)
              hB (by rw [carryIns_of_classifyC hclC]; simp)
            have hsafeM : ∀ p, s.reg.getW B 64 = some p →
                Disjoint8 (redW rsp) (p + BitVec.ofNat 64 off) := fun p hp =>
              hsafe.1.2.2 ii D n B off p (by rw [hget, ← hia]) hn hp
            obtain ⟨hc', -⟩ := sim_ldm P rsp D n B off hok sa s zf hc hwB hsafeM s' zf' hst
            obtain ⟨sa', hR, hC⟩ := ih (k + 1) _ s' zf' t hpc' hkn hc' (hz' _)
              (hnoadd hnotadd _ _) hrun hsafe'
            refine ⟨sa', ?_, hC⟩
            have hops := MArm.shape_ops hok (by simp only [MArm.instr]; rw [hia]; exact hshk)
            exact reaches_block a b hks hshk hops hR
          | stm n B off S =>
            have hok' := hok
            simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at hok'
            obtain ⟨⟨⟨hn, hS⟩, hB⟩, -⟩ := hok'
            simp only [MArm.instr] at hia
            have hwB : (s.reg.lvm B).1 ≠ 1 := hws B (by rw [← hia]; exact cell_reads (by simp) hn)
              hB (by rw [carryIns_of_classifyC hclC]; simp)
            have hwS : (s.reg.lvm S).1 ≠ 1 := hws S (by rw [← hia]; exact reg_reads (by simp))
              hS (by rw [carryIns_of_classifyC hclC]; simp)
            obtain ⟨hc', -⟩ := sim_stm P rsp n B off S hok sa s zf hc hwB hwS s' zf' hst
            obtain ⟨sa', hR, hC⟩ := ih (k + 1) _ s' zf' t hpc' hkn hc' (hz' _)
              (hnoadd hnotadd _ _) hrun hsafe'
            refine ⟨sa', ?_, hC⟩
            have hops := MArm.shape_ops hok (by simp only [MArm.instr]; rw [hia]; exact hshk)
            exact reaches_block a b hks hshk hops hR
        · -- an arm of `DecodePrintedAddr`
          split at hok
          · rename_i ar hcl
            have hia := classifyA_instr hcl
            have hli := AArm.li_eq hok
            rw [← hia, hli] at hst
            have hsafeA : ar.LoadSafe rsp s := by
              cases ar with
              | ldx D B' I =>
                intro p vi hp hvi
                exact hsafe.1.1 ii D B' I (by rw [hget, ← hia]; rfl) p vi hp hvi
              | _ => trivial
            have hw : WideAt s ar.li.fst := by
              intro r hr hg
              have hfst : ar.li.fst = normA ar.instr := by rw [← hli]
              rw [hfst, readsI_normA, hia] at hr
              exact hws r hr hg (by rw [carryIns_of_classifyC hclC]; simp)
            obtain ⟨hc', hzf'⟩ := AArm.simW P rsp ar hok sa s zf hc hw hsafeA s' zf' hst
            have hpc' : s'.reg.lpc = k + 1 := by rw [fstepA_lpc _ _ _ _ _ _ hst, hpc]
            have hz' : isCondB (body[k + 1]'hkn).li_i = true →
                (aMachine.runBlock sa (ar.js P)).flags.zf.getD false = zf' := by
              intro hcnd
              have hcm := hcondNext hcnd
              rw [hcl] at hcm
              exact hzf' (by simpa using hcm)
            obtain ⟨sa', hR, hC⟩ := ih (k + 1) _ s' zf' t hpc' hkn hc' hz'
              (hnoadd hnotadd _ _) hrun hsafe'
            refine ⟨sa', ?_, hC⟩
            have hops : shs[k].ops' = ar.js P := AArm.shape_ops hok (by rw [hia]; exact hshk)
            exact reaches_block a b hks hshk hops hR
          · cases hok
    | Llabel kd l =>
      have hstep : stepA frame body s zf = some (s.setLpc (k + 1), zf) := by
        unfold stepA
        rw [hget]
        simp only [hpc]
      rw [hstep] at hst
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
      have hz' : isCondB (body[k + 1]'hkn).li_i = true → sa.flags.zf.getD false = zf := by
        intro hcnd
        have := hcondNext hcnd
        simp [classifyA, cmpArmB, Option.any_map] at this
      have hcy' := hnoadd (fun ii' d a' s'' c' h => by rw [hbk?] at h; simp at h) sa
        (s.setLpc (k + 1))
      obtain ⟨sa', hR, hC⟩ := ih (k + 1) sa (s.setLpc (k + 1)) zf t rfl hkn (acorrW_setLpc hc _)
        hz' hcy' hrun hsafe'
      refine ⟨sa', ?_, hC⟩
      rw [posOf_succ shs k hks] at hR
      have hsk : shs[k] = .one .skip := by
        simp [shapeOf] at hshk; exact hshk.symm
      rw [hsk] at hR
      simpa [nOf] using hR
    | Lcond c l =>
      cases c with
      | reg cc =>
        simp only [instrOKWB, Bool.and_eq_true, Option.isSome_iff_exists] at hok
        obtain ⟨⟨pol, hpol⟩, ⟨p, hp⟩⟩ := hok
        obtain ⟨hpl, hlabp, -⟩ := labelAt_spec hp
        have hsk : shs[k] = .one (.jcc (ccNibble cc) l) := by
          simp [shapeOf] at hshk; exact hshk.symm
        obtain ⟨A, B, hsplit, hA⟩ := prog_split body shs a b k hks
        have hj : prog[posOf shs k]? = some (.jcc (ccNibble cc) (posOf shs p)) := by
          show (RInstr.op a :: (shs.flatMap (blkOf body shs) ++ [.op b, .ret]))[posOf shs k]? = _
          rw [hsplit, hsk, ← hA, List.append_assoc, List.getElem?_append_right (by omega)]
          simp [blkOf, hp]
        have hzf : sa.flags.zf.getD false = zf := hz rfl
        have hms := step_jcc_pol prog (posOf shs k) (posOf shs p) sa cc pol hpol hj
        rw [hzf] at hms
        by_cases hzp : zf = pol
        · have hstep : stepA frame body s zf = some (s.setLpc p, zf) := by
            unfold stepA
            rw [hget]
            simp [hpol, hzp, hp]
          rw [hstep] at hst
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
          have hz' : isCondB (body[p]'hpl).li_i = true → sa.flags.zf.getD false = zf := by
            intro hcnd
            revert hlabp hcnd
            rcases body[p] with ⟨ii', li'⟩
            cases li' <;> simp [isCondB, isLabelB]
          have hcy' : CarryReq frame body p sa (s.setLpc p) := by
            intro ii' O A' S' C' hb
            rw [List.getElem?_eq_getElem hpl] at hb
            rw [Option.some.inj hb] at hlabp
            simp [isLabelB] at hlabp
          obtain ⟨sa', hR, hC⟩ := ih p sa (s.setLpc p) zf t rfl hpl (acorrW_setLpc hc _) hz'
            hcy' hrun hsafe'
          rw [if_pos hzp] at hms
          exact ⟨sa', .next hms hR, hC⟩
        · have hstep : stepA frame body s zf = some (s.setLpc (k + 1), zf) := by
            unfold stepA
            rw [hget]
            simp [hpol, hzp, hpc]
          rw [hstep] at hst
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hst)
          have hz' : isCondB (body[k + 1]'hkn).li_i = true → sa.flags.zf.getD false = zf := by
            intro hcnd
            have := hcondNext hcnd
            simp [classifyA, cmpArmB, Option.any_map] at this
          have hcy' := hnoadd (fun ii' d a' s'' c' h => by rw [hbk?] at h; simp at h) sa
            (s.setLpc (k + 1))
          obtain ⟨sa', hR, hC⟩ := ih (k + 1) sa (s.setLpc (k + 1)) zf t rfl hkn
            (acorrW_setLpc hc _) hz' hcy' hrun hsafe'
          rw [if_neg hzp] at hms
          rw [posOf_succ shs k hks, hsk] at hR
          exact ⟨sa', .next hms (by simpa [nOf] using hR), hC⟩
      | _ => simp [instrOKWB] at hok
    | _ => simp [instrOKWB] at hok

/-! ## 8. A covered body with carry chains against its decoded bytes -/

/-- The facts of a body in the class `printedAddrWB`. -/
theorem bodyFactsW_of {body : Lcmd} (h : printedAddrWB body = true) :
    ∃ shs, BodyFactsW body shs := by
  simp only [printedAddrWB, Bool.and_eq_true, Option.any_eq_true, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨hdec, r, hlast, hret⟩, hins⟩, hcond⟩, hcar⟩ := h
  have hdec' := hdec
  simp only [decodableLcmd, Bool.and_eq_true] at hdec'
  obtain ⟨shs, hs⟩ := Option.isSome_iff_exists.mp hdec'.1.1.1.1.1
  have hpos : 0 < body.length := by
    cases body with
    | nil => simp at hlast
    | cons _ _ => simp
  refine ⟨shs, ⟨hs, hpos, ?_, fun k hk => ?_, fun k hk => hcond k hk, fun k hk => hcar k hk⟩⟩
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
    obtain rfl := Option.some.inj hlast
    revert hret
    unfold isRetB
    split <;> simp_all
  · have hm : (body[k]'(by omega)) ∈ body.dropLast := by
      rw [List.mem_iff_getElem]
      exact ⟨k, by simp; omega, by simp⟩
    exact hins _ hm

/-- The branch targets of a covered body resolve to the decoded index of their label. -/
theorem targetsOK_ofW {body : Lcmd} {shs : List DShape} (hF : BodyFactsW body shs) :
    TargetsOK body shs (fundefItemsL body shs) := by
  obtain ⟨hl, hsh⟩ := shapesOf_spec _ body shs hF.shapes
  intro sh hm l ht
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
  have hshk := hsh k (by omega) hk
  by_cases hkn : k + 1 < body.length
  · have hok := hF.instr k hkn
    revert hshk hok
    rcases body[k] with ⟨ii, li⟩
    cases li with
    | Lcond c l' =>
      cases c with
      | reg cc =>
        simp only [shapeOf, Option.some.injEq, instrOKWB, Bool.and_eq_true,
          Option.isSome_iff_exists]
        intro hsk hok
        rw [← hsk] at ht
        simp only [shTarget, Shape.target, Option.some.injEq] at ht
        subst ht
        obtain ⟨-, p, hp⟩ := hok
        obtain ⟨off, ho⟩ := labelPos_fundef hF.shapes hp
        exact ⟨off, by rw [hp]; exact ho⟩
      | _ => simp [instrOKWB]
    | Lopn ds o ss =>
      intro hsk _
      rcases shapeOfBytes_ok (bs := encodeLopn _ _ (.Lopn ds o ss) _) hsk with
        ⟨q, he, -, -⟩ | ⟨pcs, he, -, -⟩ <;> rw [he] at ht <;> simp [shTarget, Shape.target] at ht
    | Llabel kd l' =>
      intro hsk _
      simp only [shapeOf, Option.some.injEq] at hsk
      rw [← hsk] at ht
      simp [shTarget, Shape.target] at ht
    | _ => simp [instrOKWB]
  · have hk' : k = body.length - 1 := by omega
    subst hk'
    have hlast := hF.last
    revert hshk hlast
    rcases body[body.length - 1]'(by omega) with ⟨ii, li⟩
    intro hshk hlast
    simp only at hlast hshk
    subst hlast
    simp only [shapeOf, Option.some.injEq] at hshk
    rw [← hshk] at ht
    simp [shTarget, Shape.target] at ht

/-- **The decoded bytes of a covered printed body with carry chains simulate its run on the
    address machine.** For every body in the class `printedAddrWB`, from a machine state `sa`
    and an address state `s` at program counter `0` that `ACorrW` relates at the entry stack
    register with equal memories, every terminating run of the address machine on the body,
    with frame words at their addresses below the entry stack register, whose indexed loads
    read outside the red-zone word and whose instructions read no one-bit name besides a
    carry-in, is matched by a halting run of the machine on the decoded function bytes. At the
    end the stack register is restored, every general-purpose name holds the value of its
    machine register or a bit the machine register zero-extends, and the memories agree outside
    the red-zone word. -/
theorem printedAddr_simW (body : Lcmd) (h : printedAddrWB body = true) (sa : AState)
    (s : LstateA) (zf : Bool) (hpc : s.reg.lpc = 0)
    (hent : ∀ R, gpOk R = true → s.reg.getW R 64 = some (sa.regs (phys R))
      ∨ ∃ b : BitVec 1, s.reg.lvm R = ⟨1, b⟩ ∧ sa.regs (phys R) = b.setWidth 64)
    (hmem : s.mem = sa.mem) (fuel : Nat) (t : LstateA × Bool)
    (hrun : runA (frameP (Params.ofBody body) (frameRsp body sa)) body fuel s zf = some t)
    (hsafe : RunSafe (frameP (Params.ofBody body) (frameRsp body sa)) body
      (SafeW (frameRsp body sa) body) fuel s zf) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ Halts aMachine prog 0 sa sa' ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ (∀ R, gpOk R = true → t.1.reg.getW R 64 = some (sa'.regs (phys R))
          ∨ ∃ b : BitVec 1, t.1.reg.lvm R = ⟨1, b⟩ ∧ sa'.regs (phys R) = b.setWidth 64)
      ∧ (∀ x, ¬ InRange8 (redW (frameRsp body sa)) x → t.1.mem x = sa'.mem x) := by
  obtain ⟨shs, hF⟩ := bodyFactsW_of h
  have hdec : decodableLcmd body = true := by
    simp only [printedAddrWB, Bool.and_eq_true] at h
    exact h.1.1.1.1
  obtain ⟨hl, hsh⟩ := shapesOf_spec _ body shs hF.shapes
  set P := Params.ofBody body
  set F := P.frame
  set rsp := frameRsp body sa with hrsp
  set prog : List RInstr := .op (leaFrame (-(Int.ofNat F)))
    :: (shs.flatMap (blkOf body shs) ++ [.op (leaFrame (Int.ofNat F)), .ret]) with hprog
  have hdecode : decodeLprog (encodeLfundefBytes body) = some prog := by
    rw [decodeLprog_encodeLfundefBytes hdec, fundefLayout, fundefItems,
      show shapesD P body = shs by
        rw [shapesD, show shapesOf P body = some shs from hF.shapes]; rfl]
    exact expectedFrom_fundef body shs hl.symm (targetsOK_ofW hF)
  -- the prologue
  obtain ⟨hl1, hm1⟩ := evalInstrA_leaFrame sa (-(Int.ofNat F))
  set sa1 := evalInstrA sa (leaFrame (-(Int.ofNat F)))
  have hc0 : ACorrW rsp sa1 s :=
    { regs := fun R hR => by
        rw [hl1, if_neg (fun e => (gpFacts hR).physNe e)]
        exact hent R hR
      sp := by rw [hl1, if_pos rfl, hrsp]; rfl
      mem := fun x _ => by rw [hmem, hm1] }
  have hz0 : isCondB (body[0]'hF.pos).li_i = true → sa1.flags.zf.getD false = zf := by
    intro hcnd
    have hc := hF.cond 0 hF.pos
    revert hc hcnd
    unfold condPrevB
    rw [List.getElem?_eq_getElem hF.pos]
    rcases body[0]'hF.pos with ⟨ii, li⟩
    cases li <;> simp [isCondB]
  have hcy0 : CarryReq (frameP P rsp) body 0 sa1 s := by
    intro ii O A S C hb
    have hc := hF.carry 0 hF.pos
    unfold carryPrevB at hc
    rw [hb] at hc
    simp at hc
  obtain ⟨sa2, hR, hc2⟩ :=
    run_simW hF rsp _ _ fuel 0 sa1 s zf t hpc hF.pos hc0 hz0 hcy0 hrun hsafe
  -- the epilogue
  have hskip : shs[shs.length - 1]'(by have := hF.pos; omega) = .one .skip := by
    have hsk := hsh (body.length - 1) (by have := hF.pos; omega) (by have := hF.pos; omega)
    have hlast := hF.last
    revert hsk hlast
    rcases body[body.length - 1]'(by have := hF.pos; omega) with ⟨ii, li⟩
    intro hsk hlast
    simp only at hlast hsk
    subst hlast
    simp only [shapeOf, Option.some.injEq] at hsk
    simp only [hl] at hsk ⊢
    exact hsk.symm
  obtain ⟨he1, he2⟩ := prog_end body shs (leaFrame (-(Int.ofNat F))) (leaFrame (Int.ofNat F))
    (by have := hF.pos; omega) hskip
  rw [hl] at he1 he2
  obtain ⟨hl2, hm2⟩ := evalInstrA_leaFrame sa2 (Int.ofNat F)
  refine ⟨prog, evalInstrA sa2 (leaFrame (Int.ofNat F)), hdecode,
    ⟨posOf shs (body.length - 1) + 1, ?_, he2⟩, ?_, fun R hR => ?_, fun x hx => ?_⟩
  · have h01 : Reaches aMachine prog 0 sa 1 sa1 := .single (aMachine_step_op prog 0 sa _ rfl)
    have hpos0 : posOf shs 0 = 1 := by simp [posOf]
    rw [hpos0] at hR
    exact (h01.trans hR).trans (.single (aMachine_step_op prog _ sa2 _ he1))
  · rw [hl2, if_pos rfl, hc2.sp, hrsp, frameRsp]
    simp [F, P, BitVec.ofInt_neg, BitVec.ofInt_natCast]
  · rw [hl2, if_neg (fun e => (gpFacts hR).physNe e)]
    exact hc2.regs R hR
  · rw [hm2]
    exact hc2.mem x hx

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
