/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LowerLegal
public import CatCrypt.Crypto.SecureCompilation.X86Backend.GateOfLegal

@[expose] public section

set_option autoImplicit false

/-!
# The image gate on legal forms

The image simulation with carry chains gates a printed body by `imgGateBW frame slotArr body`
(`ImageAddrSimW`): every instruction before the last passes `instrGateBW`, the gate `gateAtW`
at the one-bit width analysis `oneBitAt`, the last instruction is the return, and every
array-pointer reload follows a save (`reloadSavedB`). The image of the body is defined on the
class `physImgB slotArr body` (`JasminLsemAddrImage`). This module compares the gate with the
legal forms `LegalForm` of the x86 encoder.

`ImgForm` lists the sub-forms of the legal forms that `gateAtW` accepts, one constructor per
accepted shape. Each constructor carries the hypotheses of the matching constructor of
`GateOfLegal.GateForm`, so every sub-form is a legal form, together with the conditions the
gate reads off the frame map, the array map and the width analysis: general-purpose names
without a frame word, frame slots with one, read names outside the analysis, and the base of
an indexed access holding an array pointer (`accArr`). The theorems `refusedImg_*` give, for
families of legal forms outside `ImgForm`, a legal instruction the gate refuses, evaluated in
its one-instruction body.

## Main definitions

* `ImgForm frame slotArr body k W` — the legal forms the gate accepts at instruction `k` of
  `body` at the width analysis `W`.
* `ImgRefused i` — `i` is a legal form in its one-instruction body that `instrGateBW` refuses.
* `SaveOf j` — `j` saves a general-purpose register into its slot `qsave.R`.

## Main results

* `gate_*`: the gate `gateAtW` on each accepted shape.
* `gateForm_of_imgForm`, `gateAtW_of_imgForm`, `instrGateBW_of_legalForm`: every sub-form of
  `ImgForm` is a sub-form of `GateForm`, hence a legal form, and passes the gate.
* `refusedImg_*`: the legal forms the gate refuses, one witness per family.
* `reloadSavedB_of_savePrefix`, `imgGateBW_of_legal`: a body of sub-forms of `ImgForm` that
  ends with the return and opens with the saves of its array slots passes `imgGateBW`.
* `physImgB_of_savePrefix`: a body that opens with saves of general-purpose registers, writes
  no array slot after them and resolves every indexed access is in the class `physImgB`.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImgGateOfLegal

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (condPol labelAt bitMovB normA)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov? slotCmp? cellA? slotCarry?
  cellParts?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr (srcNames cellBase readsRdx)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk isRetB gpFacts)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (carryIns kOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSimW
open CatCrypt.Crypto.SecureCompilation.X86Backend.GateOfLegal
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (castStruct? movImmStruct?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry (mulhiStruct? adcxStruct?
  adcxhiStruct? sbbStruct? sbbhiStruct?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift (sarStruct?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

/-! ## 1. Evaluation of the symbolic step on register names -/

/-- An instruction whose mnemonic is not `MOV` is no untagged immediate move. -/
theorem movImmStruct?_ne {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : o ≠ "MOV") : movImmStruct? (.Lopn ds o ss) = none := by
  unfold movImmStruct?
  split
  · rename_i heq; cases heq; exact absurd rfl h
  · rfl

/-- The sources of an operation whose first source is its destination are not exchanged. -/
theorem commSwap_self (o d b : String) : commSwap o d d b = false := by
  simp [commSwap]

/-- The register description of a two-source operation over two registers with a mnemonic of
    `binOk`. -/
theorem symN_binRR (dst opn ra rb : String) (R : String → STerm)
    (hb : binOk (stripWidthTag opn) = true) :
    symN (.Lopn [.reg dst] opn [.reg ra, .reg rb]) R =
      if commSwap opn dst ra rb then
        .set dst (.bin (stripWidthTag opn) (R rb) (R ra)) [.eqW (R rb) (R ra)]
      else .set dst (.bin (stripWidthTag opn) (R ra) (R rb)) [.eqW (R ra) (R rb)] := by
  dsimp only [symN]
  rw [if_pos hb]

theorem strip_ADD : stripWidthTag "ADD:64" = "ADD" := by decide +kernel
theorem strip_SUB : stripWidthTag "SUB:64" = "SUB" := by decide +kernel
theorem strip_AND : stripWidthTag "AND:64" = "AND" := by decide +kernel
theorem strip_OR : stripWidthTag "OR:64" = "OR" := by decide +kernel
theorem strip_XOR : stripWidthTag "XOR:64" = "XOR" := by decide +kernel
theorem strip_MUL : stripWidthTag "MUL:64" = "MUL" := by decide +kernel
theorem binOk_ADD : binOk "ADD" = true := by decide +kernel
theorem binOk_SUB : binOk "SUB" = true := by decide +kernel
theorem binOk_AND : binOk "AND" = true := by decide +kernel
theorem binOk_OR : binOk "OR" = true := by decide +kernel
theorem binOk_XOR : binOk "XOR" = true := by decide +kernel
theorem binOk_MUL : binOk "MUL" = true := by decide +kernel
theorem strip_MOV64 : stripWidthTag "MOV:64" = "MOV" := by decide +kernel
theorem strip_MOVQ : stripWidthTag "MOVQ" = "MOVQ" := by decide +kernel
theorem strip_CMOV : stripWidthTag "CMOV:64" = "CMOV" := by decide +kernel
theorem strip_CMP : stripWidthTag "CMP:64" = "CMP" := by decide +kernel
theorem strip_SETE : stripWidthTag "SETE:64" = "SETE" := by decide +kernel
theorem strip_SETNE : stripWidthTag "SETNE:64" = "SETNE" := by decide +kernel
theorem strip_SHL : stripWidthTag "SHL:64" = "SHL" := by decide +kernel
theorem strip_SHR : stripWidthTag "SHR:64" = "SHR" := by decide +kernel
theorem binOk_SHL : binOk "SHL" = true := by decide +kernel
theorem binOk_SHR : binOk "SHR" = true := by decide +kernel
theorem binOk_SETE : binOk "SETE" = false := by decide +kernel
theorem binOk_SETNE : binOk "SETNE" = false := by decide +kernel
theorem copyQ_MOVQ : copyQ "MOVQ" = true := by decide +kernel
theorem cmp_SETE : (VIR.JasminLsemWidthN.cmpOfName? "SETE").isSome = true := by decide +kernel
theorem cmp_SETNE : (VIR.JasminLsemWidthN.cmpOfName? "SETNE").isSome = true := by decide +kernel
theorem width_64 (m : String) (h : hasSuffix m ":64" = true) :
    VIR.JasminLsemWidthN.widthFromTag m = 64 := by
  simp [VIR.JasminLsemWidthN.widthFromTag, h]

/-- The register description of a materialised comparison over two registers. -/
theorem symN_setccRR (dst opn ra rb : String) (R : String → STerm)
    (hb : binOk (stripWidthTag opn) = false)
    (hc : (VIR.JasminLsemWidthN.cmpOfName? (stripWidthTag opn)).isSome = true) :
    symN (.Lopn [.reg dst] opn [.reg ra, .reg rb]) R =
      .set dst (.setcc ((VIR.JasminLsemWidthN.cmpOfName? (stripWidthTag opn)).getD .eq) (R ra)
        (R rb)) [.eqW (R ra) (R rb)] := by
  dsimp only [symN]
  rw [if_neg (by simp [hb]), if_pos hc]

/-- The register description of a select over registers. -/
theorem symN_cmov (dst opn c a b : String) (R : String → STerm)
    (h : stripWidthTag opn = "CMOV") :
    symN (.Lopn [.reg dst] opn [.reg c, .reg a, .reg b]) R =
      .set dst (.sel (R a) (R b) (R c)) [.wid (R c) 1, .eqW (R a) (R b)] := by
  dsimp only [symN]
  rw [if_pos h]

/-- The register description of a move of an immediate into a register. -/
theorem symN_movImm (dst opn : String) (n : Nat) (R : String → STerm)
    (h : stripWidthTag opn = "MOV") :
    symN (.Lopn [.reg dst] opn [.imm n]) R =
      .set dst (.immW (VIR.JasminLsemWidthN.widthFromTag opn) n) [] := by
  dsimp only [symN]
  rw [if_pos h]

/-- The register description of a two-source operation against an immediate that fits its
    width, other than a shift by `0`. -/
theorem symN_binRI (dst opn ra : String) (n : Nat) (R : String → STerm)
    (hb : binOk (stripWidthTag opn) = true)
    (h0 : ¬((stripWidthTag opn = "SHL" ∨ stripWidthTag opn = "SHR") ∧ n = 0))
    (hn : n < 2 ^ VIR.JasminLsemWidthN.widthFromTag opn) :
    symN (.Lopn [.reg dst] opn [.reg ra, .imm n]) R =
      .set dst (.bin (stripWidthTag opn) (R ra)
        (.immW (VIR.JasminLsemWidthN.widthFromTag opn) n)) [] := by
  dsimp only [symN]
  rw [if_pos hb, if_neg h0, if_pos hn]

/-- The register description of a shift by `0`. -/
theorem symN_shift0 (dst opn ra : String) (R : String → STerm)
    (hb : binOk (stripWidthTag opn) = true)
    (h0 : stripWidthTag opn = "SHL" ∨ stripWidthTag opn = "SHR") :
    symN (.Lopn [.reg dst] opn [.reg ra, .imm 0]) R = .set dst (R ra) [] := by
  dsimp only [symN]
  rw [if_pos hb, if_pos ⟨h0, rfl⟩]

/-- The sources of an operation of a non-commutative base are not exchanged. -/
theorem commSwap_of_not_comm (o d a b : String)
    (h : TwoAddrLegalize.commBases.contains (stripWidthTag o) = false) :
    commSwap o d a b = false := by
  simp only [commSwap, h, Bool.false_and]

theorem comm_SHL : TwoAddrLegalize.commBases.contains "SHL" = false := by decide +kernel
theorem comm_SHR : TwoAddrLegalize.commBases.contains "SHR" = false := by decide +kernel

/-- A frame-slot name is no cell name. -/
theorem hasPrefix_mem_of_slot {q : String} (h : LprogBytes.isSpillOrQsave q = true) :
    hasPrefix q "mem." = false := by
  simp only [LprogBytes.isSpillOrQsave, Bool.or_eq_true, hasPrefix] at h ⊢
  have e1 : ("mem." : String).toList = ['m', 'e', 'm', '.'] := by decide +kernel
  have e2 : ("k." : String).toList = ['k', '.'] := by decide +kernel
  have e3 : ("qsave." : String).toList = ['q', 's', 'a', 'v', 'e', '.'] := by decide +kernel
  rw [e1]
  rw [e2, e3] at h
  cases hq : q.toList with
  | nil => rfl
  | cons c t =>
    rw [hq] at h
    rcases h with h | h <;> simp only [List.isPrefixOf, Bool.and_eq_true, beq_iff_eq] at h <;>
      simp [List.isPrefixOf, ← h.1]

/-- A frame-slot name is no cell name. -/
theorem cellParts?_of_slot {q : String} (h : LprogBytes.isSpillOrQsave q = true) :
    cellParts? q = none := by
  simp [cellParts?, hasPrefix_mem_of_slot h]

/-- The simplification set that evaluates the register gate `regGateBW` on an instruction of a
    concrete mnemonic over register names. -/
macro "img_sym" : tactic => `(tactic|
  simp only [regGateBW, regOkB, normA, symStep, cmpArgs?, movRegArgs?, flagCondCC?, carryArgs?,
    wideArgs?, withWidthTag, ↓reduceIte, String.reduceAppend, String.reduceEq, symMem, liftR,
    symCast, castStruct?, movImmStruct?_ne, ne_eq, not_false_eq_true, or_self, or_false, symMC,
    mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?, sbbhiStruct?, symSh, sarStruct?,
    strip_ADD, strip_SUB, strip_AND, strip_OR, strip_XOR, strip_MUL, binOk_ADD, binOk_SUB,
    binOk_AND, binOk_OR, binOk_XOR, binOk_MUL, strip_MOV64, strip_MOVQ, strip_CMOV, strip_CMP,
    strip_SETE, strip_SETNE, strip_SHL, strip_SHR, binOk_SHL, binOk_SHR, binOk_SETE,
    binOk_SETNE, copyQ_MOVQ, cmp_SETE, cmp_SETNE, symN_setccRR, symN_cmov, symN_movImm,
    symN_binRR, commSwap_self, comm_SHL, comm_SHR, commSwap_of_not_comm, aluFl, aluFlT,
    aluFlagOp?, symOp64, aluSwap, cellA?, slotCarry?, slotCmp?, slotMov?, Bool.false_and,
    Bool.false_eq_true, Option.isNone_none, Option.all_none, Bool.true_and, Bool.and_true])

example (frame : String → Option (BitVec 64)) (W : List String) (m d s : String)
    (hm : m ∈ ["ADD:64", "SUB:64", "AND:64", "OR:64", "XOR:64", "MUL:64"]) (hd : gpOk d = true)
    (hfd : frame d = none) (hfs : frame s = none) (hdW : d ∉ W) :
    regGateBW frame W (normA (.Lopn [.reg d] m [.reg d, .reg s])) = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> img_sym <;>
  simp [descArrFree, descReads, SSt.setR, SSt.regs, SSt.start, RegFile.get_set, termArrFree,
    guardArrFree, flagArrFree, STerm.vars, SG.vars, SFlag.vars, wid64WB, STerm.wbase,
    STerm.wknown, hfd, hfs, hd, hdW]

/-- A general-purpose name is no cell name. -/
theorem cellParts?_of_gpOk {r : String} (h : gpOk r = true) : cellParts? r = none := by
  have hm := DecodePrinted.mem_gpList h
  simp only [DecodePrinted.gpList, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide +kernel

theorem readOkB_of_forall {frame : String → Option (BitVec 64)} {W : List String} {x : LinstrR}
    (h : ∀ r ∈ readNames x, r ∉ W) : readOkB (gateReadSet frame W x) x = true := by
  unfold readOkB
  rw [List.all_eq_true]
  intro r hr
  have hsub : ∀ r, r ∈ gateReadSet frame W x → r ∈ W := by
    intro r hr'
    unfold gateReadSet at hr'
    split at hr' <;> first | exact (List.mem_filter.1 hr').1 | exact hr'
  have : r ∉ gateReadSet frame W x := fun hm => h r hr (hsub r hm)
  simp [this]

theorem gateAtW_reg {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {x : LinstrR} (hr : ∀ r ∈ readNames x, r ∉ W) (hc : carryI? x = none)
    (hi : icase frame x = .reg) (hm : movImmStruct? x = none) (hb : bitStore? body k x = none)
    (hg : regGateBW frame W (normA x) = true) (hcm : cmovCondOkB W x = true) :
    gateAtW frame slotArr body k W x = true := by
  simp [gateAtW, readOkB_of_forall hr, hc, hi, hm, hb, hg, hcm]

/-- The simplification set that evaluates the kind `icase` of an instruction of a concrete
    mnemonic. -/
macro "img_icase" : tactic => `(tactic|
  simp only [icase, VIR.JasminLsemAddrRun.castTagW, String.reduceEq, ↓reduceIte, or_self,
    slotMov?, slotCmp?, ne_eq, not_true_eq_false, or_false, false_or])

/-- The simplification set that closes the conditions of `regGateBW` after `img_sym`. -/
macro "img_fin" : tactic => `(tactic|
  simp [descArrFree, descReads, SSt.setR, SSt.regs, SSt.start, RegFile.get_set, termArrFree,
    guardArrFree, flagArrFree, STerm.vars, SG.vars, SFlag.vars, wid64WB, STerm.wbase,
    STerm.wknown, *])

/-- The simplification set that evaluates the names `readNames` an instruction reads. -/
macro "img_reads" : tactic => `(tactic|
  simp [readOkB, carryIns, readNames, readsRdx, VIR.JasminLsemAddrCongr.rdxOp, srcNames,
    cellBase, withWidthTag, *])

/-! ## 2. The gate on the accepted forms -/

/-- **A label passes the gate.** -/
theorem gate_label (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) (k : Nat) (W : List String) (kd : LabelKind) (l : LLabel) :
    gateAtW frame slotArr body k W (.Llabel kd l) = true := by
  simp [gateAtW, carryI?, icase, readOkB, readNames]

/-- **A branch on a condition code with a polarity passes the gate** when every name of the
    analysis `W` lies in the analysis one past the target label. -/
theorem gate_cond {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {cc : String} {l : LLabel} {p : Nat} (hpol : (condPol cc).isSome = true)
    (hp : labelAt body l = some p) (hW : ∀ r ∈ W, r ∈ oneBitAt frame body (p + 1)) :
    gateAtW frame slotArr body k W (.Lcond (.reg cc) l) = true := by
  simp only [gateAtW, carryI?, icase, readOkB, readNames, List.all_nil, Bool.true_or,
    Bool.true_and, hpol, hp, Option.any_some]
  simp only [Bool.or_eq_true, List.isEmpty_iff, List.all_eq_true, List.contains_iff_mem]
  exact Or.inr hW

/-- **An indexed load at stride `8` passes the gate** when its base holds the pointer of an
    array (`accArr`), its names hold no frame word, and the base and index lie outside the
    analysis. -/
theorem gate_loadIdx {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {d b x : String} (hd : gpOk d = true) (hacc : (accArr slotArr body k b).isSome = true)
    (hfd : frame d = none) (hfb : frame b = none) (hfx : frame x = none) (hbW : b ∉ W)
    (hxW : x ∉ W) :
    gateAtW frame slotArr body k W (.Lopn [.reg d] "LOADIDX" [.arrIdx b x 8]) = true := by
  have hr := readOkB_of_forall (frame := frame)
    (x := .Lopn [.reg d] "LOADIDX" [.arrIdx b x 8]) (W := W) (by
      have := cellParts?_of_gpOk hd
      img_reads)
  simp [gateAtW, carryI?, icase, hr, hacc, hd, hfd, hfb, hfx]

/-- **An indexed store at stride `8` passes the gate** when its base holds the pointer of an
    array, its names hold no frame word, the array name is no cell name, and the base, index
    and value lie outside the analysis. -/
theorem gate_storeIdx {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {a b x v : String} (ha : cellParts? a = none) (hv : gpOk v = true)
    (hacc : (accArr slotArr body k b).isSome = true) (hfb : frame b = none)
    (hfx : frame x = none) (hfv : frame v = none) (hbW : b ∉ W) (hxW : x ∉ W) (hvW : v ∉ W) :
    gateAtW frame slotArr body k W (.Lopn [.reg a] "STOREIDX" [.arrIdx b x 8, .reg v])
      = true := by
  have hr := readOkB_of_forall (frame := frame)
    (x := .Lopn [.reg a] "STOREIDX" [.arrIdx b x 8, .reg v]) (W := W) (by
      have := cellParts?_of_gpOk hv
      img_reads)
  simp [gateAtW, carryI?, icase, hr, hacc, hfb, hfx, hfv]

/-- **A two-address operation over general-purpose names passes the gate** when its names hold
    no frame word and lie outside the analysis. -/
theorem gate_alu {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {m d s : String} (hm : m ∈ ["ADD:64", "SUB:64", "AND:64", "OR:64", "XOR:64", "MUL:64"])
    (hd : gpOk d = true) (hs : gpOk s = true) (hfd : frame d = none) (hfs : frame s = none)
    (hdW : d ∉ W) (hsW : s ∉ W) :
    gateAtW frame slotArr body k W (.Lopn [.reg d] m [.reg d, .reg s]) = true := by
  have := cellParts?_of_gpOk hd
  have := cellParts?_of_gpOk hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · apply gateAtW_reg
    · img_reads
    · rfl
    · img_icase
    · exact movImmStruct?_ne (by decide)
    · rfl
    · img_sym; img_fin
    · rfl

/-- **The compare of two general-purpose names passes the gate** when its names hold no frame
    word and lie outside the analysis. -/
theorem gate_cmp {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {d s : String} (hd : gpOk d = true) (hs : gpOk s = true) (hfd : frame d = none)
    (hfs : frame s = none) (hdW : d ∉ W) (hsW : s ∉ W) :
    gateAtW frame slotArr body k W (.Lopn [.reg d] "CMP:64" [.reg d, .reg s]) = true := by
  have := cellParts?_of_gpOk hd
  have := cellParts?_of_gpOk hs
  apply gateAtW_reg
  · img_reads
  · rfl
  · img_icase
    simp [hfs]
  · exact movImmStruct?_ne (by decide)
  · rfl
  · img_sym; img_fin
  · rfl

/-- **A 64-bit move between general-purpose names passes the gate** when its names hold no
    frame word and the source lies outside the analysis. -/
theorem gate_movRR {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {m d s : String} (hm : m ∈ ["MOV:64", "MOVQ"]) (hd : gpOk d = true) (hs : gpOk s = true)
    (hfd : frame d = none) (hfs : frame s = none) (hsW : s ∉ W) :
    gateAtW frame slotArr body k W (.Lopn [.reg d] m [.reg s]) = true := by
  have := cellParts?_of_gpOk hd
  have := cellParts?_of_gpOk hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;>
  · apply gateAtW_reg
    · img_reads
    · rfl
    · img_icase
      simp [hfd, hfs]
    · exact movImmStruct?_ne (by decide)
    · rfl
    · img_sym; img_fin
    · rfl

/-- **A load of a frame slot into a general-purpose name passes the gate** when a slot of the
    analysis is no destination of an untagged immediate move of the body. -/
theorem gate_movLoad {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {m d q : String} (hm : m ∈ ["MOV:64", "MOVQ"]) (hd : gpOk d = true)
    (hq : LprogBytes.isSpillOrQsave q = true) (hfd : frame d = none)
    (hfq : (frame q).isSome = true) (hqW : q ∈ W → q ∉ movlNames body) :
    gateAtW frame slotArr body k W (.Lopn [.reg d] m [.reg q]) = true := by
  have := cellParts?_of_gpOk hd
  have := cellParts?_of_slot hq
  have hqg := not_gpOk_of_slot hq
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hfq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  have hi : icase frame (.Lopn [.reg d] m [.reg q]) = .sload d q := by
    rcases hm with rfl | rfl <;> (img_icase; simp [hfd, ha])
  simp only [gateAtW, carryI?, hi, gateReadSet]
  rcases hm with rfl | rfl <;>
  · by_cases hW : q ∈ W
    · have := hqW hW
      img_reads
    · img_reads

/-- **A store of a general-purpose name into a frame slot passes the gate** when a stored name
    of the analysis is no destination of a narrow cast of the body. -/
theorem gate_movStore {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {m q s : String} (hm : m ∈ ["MOV:64", "MOVQ"]) (hs : gpOk s = true)
    (hq : LprogBytes.isSpillOrQsave q = true) (hfq : (frame q).isSome = true)
    (hfs : frame s = none) (hsW : s ∈ W → s ∉ castDsts body) :
    gateAtW frame slotArr body k W (.Lopn [.reg q] m [.reg s]) = true := by
  have := cellParts?_of_gpOk hs
  have := cellParts?_of_slot hq
  have := hasPrefix_mem_of_slot hq
  have hqg := not_gpOk_of_slot hq
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hfq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  have hi : icase frame (.Lopn [.reg q] m [.reg s]) = .sstore q s := by
    rcases hm with rfl | rfl <;> (img_icase; simp [hfs, ha])
  simp only [gateAtW, carryI?, hi, gateReadSet]
  rcases hm with rfl | rfl <;>
  · by_cases hW : s ∈ W
    · have := hsW hW
      img_reads
    · img_reads

/-- **A 64-bit move of an immediate into a general-purpose name passes the gate** when the
    name holds no frame word. -/
theorem gate_movImm64 {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {d : String} {v : Nat} (hd : gpOk d = true) (hfd : frame d = none) :
    gateAtW frame slotArr body k W (.Lopn [.reg d] "MOV:64" [.imm v]) = true := by
  have := cellParts?_of_gpOk hd
  have hgn : gpNameB d = true := hd
  apply gateAtW_reg
  · img_reads
  · rfl
  · img_icase
  · exact movImmStruct?_ne (by decide)
  · simp [bitStore?, hgn]
  · img_sym
    simp only [width_64 "MOV:64" (by decide +kernel)]
    img_fin
  · rfl

/-- **A 64-bit move of an immediate into a frame slot holding no array pointer passes the
    gate.** -/
theorem gate_movImmSlot {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {q : String} {v : Nat} (hq : LprogBytes.isSpillOrQsave q = true)
    (hfq : (frame q).isSome = true) (hsl : slotArr q = none) :
    gateAtW frame slotArr body k W (.Lopn [.reg q] "MOV:64" [.imm v]) = true := by
  have := cellParts?_of_slot hq
  have hi : icase frame (.Lopn [.reg q] "MOV:64" [.imm v]) = .reg := by img_icase
  have hr := readOkB_of_forall (frame := frame) (x := .Lopn [.reg q] "MOV:64" [.imm v])
    (W := W) (by img_reads)
  have hs : sImmB frame slotArr (.Lopn [.reg q] "MOV:64" [.imm v]) = true := by
    simp [sImmB, hfq, hsl]
  simp only [gateAtW, carryI?, hi, hr, movImmStruct?_ne (show "MOV:64" ≠ "MOV" by decide),
    hs, Bool.true_or, Bool.true_and]
  split <;> rfl

/-- **An untagged move of a carry constant into a general-purpose name passes the gate**: a
    move `MOV d, #n` that `bitMovB` accepts, into a name without a frame word. -/
theorem gate_movImmBit {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {d : String} {n : Nat} (hd : gpOk d = true) (hfd : frame d = none)
    (hbit : bitMovB body k (.Lopn [.reg d] "MOV" [.imm n]) = true) :
    gateAtW frame slotArr body k W (.Lopn [.reg d] "MOV" [.imm n]) = true := by
  have := cellParts?_of_gpOk hd
  have hi : icase frame (.Lopn [.reg d] "MOV" [.imm n]) = .reg := by img_icase
  have hr := readOkB_of_forall (frame := frame) (x := .Lopn [.reg d] "MOV" [.imm n])
    (W := W) (by img_reads)
  simp [gateAtW, carryI?, hi, hr, movImmStruct?, hbit, hd, hfd]

/-- A name of `kOk` is no cell name. -/
theorem cellParts?_of_kOk {P : Params} {x : String} (h : kOk P x = true) : cellParts? x = none := by
  cases hs : LprogBytes.isSpillOrQsave x
  · exact cellParts?_of_gpOk (gpOk_of_kOk h hs)
  · exact cellParts?_of_slot hs

/-- **The carry-chain add over general-purpose names passes the gate** when its word sources
    lie outside the analysis; the carry-in may lie in it. -/
theorem gate_adcx {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {d a s c : String} (hd : gpOk d = true) (ha : gpOk a = true) (hs : gpOk s = true)
    (hc : gpOk c = true) (hac : a ≠ c) (hsc : s ≠ c) (haW : a ∉ W) (hsW : s ∉ W) :
    gateAtW frame slotArr body k W (.Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c])
      = true := by
  have := cellParts?_of_gpOk hd
  have := cellParts?_of_gpOk ha
  have := cellParts?_of_gpOk hs
  have := cellParts?_of_gpOk hc
  have hi : icase frame (.Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c]) = .reg := by
    img_icase
  simp only [gateAtW, carryI?, ↓reduceIte, gateReadSet, hi]
  simp [carryOkB, hd, ha, hs, hc, hac, hsc]
  img_reads

/-- **The carry-out binding of a carry-chain add passes the gate** when its destination is a
    general-purpose name, each source is a general-purpose name or a name with a frame word,
    the carry-in is none of the word sources, and the word sources lie outside the
    analysis. -/
theorem gate_adcxhi {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {P : Params} {o a s c : String} (ho : gpOk o = true) (ha : kOk P a = true)
    (hs : kOk P s = true) (hc : kOk P c = true)
    (hfa : gpOk a = true ∨ (frame a).isSome = true) (hfs : gpOk s = true ∨ (frame s).isSome = true)
    (hfc : gpOk c = true ∨ (frame c).isSome = true) (hac : a ≠ c) (hsc : s ≠ c)
    (haW : a ∉ W) (hsW : s ∉ W) :
    gateAtW frame slotArr body k W (.Lopn [.reg o] "ADCXHI:64" [.reg a, .reg s, .reg c])
      = true := by
  have := cellParts?_of_gpOk ho
  have := cellParts?_of_kOk ha
  have := cellParts?_of_kOk hs
  have := cellParts?_of_kOk hc
  have hi : icase frame (.Lopn [.reg o] "ADCXHI:64" [.reg a, .reg s, .reg c]) = .reg := by
    img_icase
  simp only [gateAtW, carryI?, String.reduceEq, ↓reduceIte, gateReadSet, hi]
  have hco : carryOkB frame slotArr o a s c = true := by
    simp only [carryOkB, ho, Bool.true_or, Bool.and_true, Bool.and_eq_true, Bool.or_eq_true,
      bne_iff_ne, ne_eq]
    exact ⟨⟨⟨⟨hfc, hfa⟩, hfs⟩, hac⟩, hsc⟩
  rw [hco, Bool.and_true]
  img_reads

/-- **The select over general-purpose names passes the gate** when its condition is none of
    the other operands, its names hold no frame word, and its two values lie outside the
    analysis; the condition may lie in it. -/
theorem gate_select {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {d c a b : String} (hd : gpOk d = true) (hc : gpOk c = true) (ha : gpOk a = true)
    (hb : gpOk b = true) (hac : a ≠ c) (hbc : b ≠ c) (hfd : frame d = none)
    (hfc : frame c = none) (hfa : frame a = none) (hfb : frame b = none) (haW : a ∉ W)
    (hbW : b ∉ W) :
    gateAtW frame slotArr body k W (.Lopn [.reg d] "CMOV:64" [.reg c, .reg a, .reg b])
      = true := by
  have := cellParts?_of_gpOk hd
  have := cellParts?_of_gpOk hc
  have := cellParts?_of_gpOk ha
  have := cellParts?_of_gpOk hb
  have hi : icase frame (.Lopn [.reg d] "CMOV:64" [.reg c, .reg a, .reg b]) = .reg := by
    img_icase
  have hr : readOkB (gateReadSet frame W (.Lopn [.reg d] "CMOV:64" [.reg c, .reg a, .reg b]))
      (.Lopn [.reg d] "CMOV:64" [.reg c, .reg a, .reg b]) = true := by
    simp only [gateReadSet, hi]
    img_reads
  have hsc : sCmovB frame slotArr (.Lopn [.reg d] "CMOV:64" [.reg c, .reg a, .reg b])
      = false := by simp [sCmovB, hfd, hfa, hfb]
  have hcm : cmovCondOkB W (.Lopn [.reg d] "CMOV:64" [.reg c, .reg a, .reg b]) = true := by
    simp [cmovCondOkB, hd, hc, ha, hb, hac, hbc]
  have hg : regGateBW frame W (normA (.Lopn [.reg d] "CMOV:64" [.reg c, .reg a, .reg b]))
      = true := by
    img_sym; img_fin
  simp [gateAtW, carryI?, hi, hr, movImmStruct?_ne (show "CMOV:64" ≠ "MOV" by decide),
    bitStore?, sImmB, hsc, hg, hcm]

/-- **A materialised comparison of two general-purpose names passes the gate** when its names
    hold no frame word and its sources lie outside the analysis. -/
theorem gate_setcc {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {m d a b : String} (hm : m ∈ ["SETE:64", "SETNE:64"]) (hd : gpOk d = true)
    (ha : gpOk a = true) (hb : gpOk b = true) (hfd : frame d = none) (hfa : frame a = none)
    (hfb : frame b = none) (haW : a ∉ W) (hbW : b ∉ W) :
    gateAtW frame slotArr body k W (.Lopn [.reg d] m [.reg a, .reg b]) = true := by
  have := cellParts?_of_gpOk hd
  have := cellParts?_of_gpOk ha
  have := cellParts?_of_gpOk hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;>
  · apply gateAtW_reg
    · img_reads
    · rfl
    · img_icase
    · exact movImmStruct?_ne (by decide)
    · rfl
    · img_sym; img_fin
    · rfl

/-- **A three-register left or logical right shift passes the gate** when its names hold no
    frame word and its sources lie outside the analysis. -/
theorem gate_shiftReg {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {m d a b : String} (hm : m ∈ ["SHL:64", "SHR:64"]) (hd : gpOk d = true)
    (ha : gpOk a = true) (hb : gpOk b = true) (hfd : frame d = none) (hfa : frame a = none)
    (hfb : frame b = none) (haW : a ∉ W) (hbW : b ∉ W) :
    gateAtW frame slotArr body k W (.Lopn [.reg d] m [.reg a, .reg b]) = true := by
  have := cellParts?_of_gpOk hd
  have := cellParts?_of_gpOk ha
  have := cellParts?_of_gpOk hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl <;>
  · apply gateAtW_reg
    · img_reads
    · rfl
    · img_icase
    · exact movImmStruct?_ne (by decide)
    · rfl
    · img_sym; img_fin
    · rfl

/-- **A two-address operation against an immediate below `2^64` passes the gate** when its
    destination holds no frame word and lies outside the analysis. -/
theorem gate_aluImm {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {m d : String} {v : Nat} (hm : m ∈ ["ADD:64", "SUB:64", "AND:64", "OR:64", "XOR:64"])
    (hd : gpOk d = true) (hfd : frame d = none) (hdW : d ∉ W) (hv : v < 2 ^ 64) :
    gateAtW frame slotArr body k W (.Lopn [.reg d] m [.reg d, .imm v]) = true := by
  have := cellParts?_of_gpOk hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  have h1 : binOk (stripWidthTag m) = true := by
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have h2 : ¬(stripWidthTag m = "SHL" ∨ stripWidthTag m = "SHR") := by
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have h3 : hasSuffix m ":64" = true := by
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have hsym := fun R => symN_binRI d m d v R h1 (fun h => h2 h.1) (by rw [width_64 m h3]; exact hv)
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
  · apply gateAtW_reg
    · img_reads
    · rfl
    · img_icase
    · exact movImmStruct?_ne (by decide)
    · rfl
    · img_sym
      simp only [hsym]
      img_fin
    · rfl

/-- **The 64-bit compare of a general-purpose name against an immediate passes the gate**
    when the name holds no frame word and lies outside the analysis. -/
theorem gate_cmpImm {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {d : String} {v : Nat} (hd : gpOk d = true) (hfd : frame d = none) (hdW : d ∉ W) :
    gateAtW frame slotArr body k W (.Lopn [.reg d] "CMP:64" [.reg d, .imm v]) = true := by
  have := cellParts?_of_gpOk hd
  apply gateAtW_reg
  · img_reads
  · rfl
  · img_icase
  · exact movImmStruct?_ne (by decide)
  · rfl
  · img_sym; img_fin
  · rfl

/-- **A two-address left or logical right shift by an immediate below `64` passes the gate**
    when its destination holds no frame word and lies outside the analysis. -/
theorem gate_shiftImm {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {m d : String} {n : Nat} (hm : m ∈ ["SHL:64", "SHR:64"]) (hd : gpOk d = true)
    (hfd : frame d = none) (hdW : d ∉ W) (hn : n < 64) :
    gateAtW frame slotArr body k W (.Lopn [.reg d] m [.reg d, .imm n]) = true := by
  have := cellParts?_of_gpOk hd
  have hn' : n < 2 ^ 64 := lt_trans hn (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  have h1 : binOk (stripWidthTag m) = true := by rcases hm with rfl | rfl <;> decide +kernel
  have h2 : stripWidthTag m = "SHL" ∨ stripWidthTag m = "SHR" := by
    rcases hm with rfl | rfl <;> decide +kernel
  have h3 : hasSuffix m ":64" = true := by rcases hm with rfl | rfl <;> decide +kernel
  rcases Nat.eq_zero_or_pos n with rfl | h0
  · have hsym := fun R => symN_shift0 d m d R h1 h2
    rcases hm with rfl | rfl <;>
    · apply gateAtW_reg
      · img_reads
      · rfl
      · img_icase
      · exact movImmStruct?_ne (by decide)
      · rfl
      · img_sym
        simp only [hsym]
        img_fin
      · rfl
  · have hsym := fun R => symN_binRI d m d n R h1 (fun h => by omega)
      (by rw [width_64 m h3]; exact hn')
    rcases hm with rfl | rfl <;>
    · apply gateAtW_reg
      · img_reads
      · rfl
      · img_icase
      · exact movImmStruct?_ne (by decide)
      · rfl
      · img_sym
        simp only [hsym]
        img_fin
      · rfl

/-! ## 3. The accepted sub-family of the legal forms -/

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (LegalForm)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
open CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeComplete
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (dispOk32)

/-- **The sub-forms of the legal forms that the gate `gateAtW` accepts** at instruction `k` of
    `body`, at the frame map `frame`, the array map `slotArr` and the width analysis `W`. Each
    constructor carries the hypotheses of the matching constructor of `GateForm body` and the
    conditions of the image: the names without a frame word, the frame slots with one, the
    names read outside `W`, the base of an indexed access holding an array pointer. -/
inductive ImgForm (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (body : Lcmd) (k : Nat) (W : List String) : LinstrR → Prop
  /-- A 64-bit register move between general-purpose names. -/
  | movRR (m d s : String) : m ∈ ["MOV:64", "MOVQ"] → gpOk d = true → gpOk s = true →
      frame d = none → frame s = none → s ∉ W →
      ImgForm frame slotArr body k W (.Lopn [.reg d] m [.reg s])
  /-- A 64-bit store of a general-purpose name into a frame slot. -/
  | movStore (m q s : String) : m ∈ ["MOV:64", "MOVQ"] → isSpillOrQsave q = true →
      (spillQsaveOff (Params.ofBody body).frame (Params.ofBody body).spillW q
        (Params.ofBody body).qsaveB).isSome = true →
      dispOk32 (slotOff (Params.ofBody body) q) = true → gpOk s = true →
      (frame q).isSome = true → frame s = none → (s ∈ W → s ∉ castDsts body) →
      ImgForm frame slotArr body k W (.Lopn [.reg q] m [.reg s])
  /-- A 64-bit load of a frame slot into a general-purpose name. -/
  | movLoad (m d q : String) : m ∈ ["MOV:64", "MOVQ"] → gpOk d = true →
      isSpillOrQsave q = true → kOk (Params.ofBody body) q = true →
      frame d = none → (frame q).isSome = true → (q ∈ W → q ∉ movlNames body) →
      ImgForm frame slotArr body k W (.Lopn [.reg d] m [.reg q])
  /-- An untagged move of a carry constant below `2^31` into a general-purpose name. -/
  | movImmBit (d : String) (n : Nat) : gpOk d = true → n < 2 ^ 31 → frame d = none →
      bitMovB body k (.Lopn [.reg d] "MOV" [.imm n]) = true →
      ImgForm frame slotArr body k W (.Lopn [.reg d] "MOV" [.imm n])
  /-- A 64-bit immediate move into a general-purpose name. -/
  | movImm64 (d : String) (v : Nat) : gpOk d = true → v < 2 ^ 64 → frame d = none →
      ImgForm frame slotArr body k W (.Lopn [.reg d] "MOV:64" [.imm v])
  /-- A 64-bit immediate move into a frame slot holding no array pointer. -/
  | movImmSlot (q : String) (v : Nat) : isSpillOrQsave q = true →
      (spillQsaveOff (Params.ofBody body).frame (Params.ofBody body).spillW q
        (Params.ofBody body).qsaveB).isSome = true →
      dispOk32 (slotOff (Params.ofBody body) q) = true → v < 2 ^ 64 →
      (ScalarEncoder.fitsImm32S v = true ∨
        sepB cmovRedZone (slotOff (Params.ofBody body) q) = true) →
      (frame q).isSome = true → slotArr q = none →
      ImgForm frame slotArr body k W (.Lopn [.reg q] "MOV:64" [.imm v])
  /-- The 64-bit select over general-purpose names. -/
  | select (d c a b : String) : gpOk d = true → gpOk c = true → gpOk a = true →
      gpOk b = true → d ≠ c → a ≠ c → b ≠ c → frame d = none → frame c = none →
      frame a = none → frame b = none → a ∉ W → b ∉ W →
      ImgForm frame slotArr body k W (.Lopn [.reg d] "CMOV:64" [.reg c, .reg a, .reg b])
  /-- A 64-bit materialised comparison over general-purpose names. -/
  | setcc (m d a b : String) : m ∈ ["SETE:64", "SETNE:64"] → gpOk d = true → gpOk a = true →
      gpOk b = true → frame d = none → frame a = none → frame b = none → a ∉ W → b ∉ W →
      ImgForm frame slotArr body k W (.Lopn [.reg d] m [.reg a, .reg b])
  /-- A 64-bit two-address operation over general-purpose names. -/
  | alu (m d s : String) :
      m ∈ ["ADD:64", "SUB:64", "AND:64", "OR:64", "XOR:64", "MUL:64", "CMP:64"] →
      gpOk d = true → gpOk s = true → frame d = none → frame s = none → d ∉ W → s ∉ W →
      ImgForm frame slotArr body k W (.Lopn [.reg d] m [.reg d, .reg s])
  /-- A 64-bit two-address operation against an immediate that sign-extends from 32 bits. -/
  | aluImm (m d : String) (v : Nat) : m ∈ ["ADD:64", "SUB:64", "AND:64", "OR:64", "XOR:64"] →
      gpOk d = true → v < 2 ^ 64 → ScalarEncoder.fitsImm32S v = true → frame d = none →
      d ∉ W → ImgForm frame slotArr body k W (.Lopn [.reg d] m [.reg d, .imm v])
  /-- The 64-bit compare against an immediate that sign-extends from 8 bits. -/
  | cmpImm (d : String) (v : Nat) : gpOk d = true → fitsImm8S 1 v = true → frame d = none →
      d ∉ W → ImgForm frame slotArr body k W (.Lopn [.reg d] "CMP:64" [.reg d, .imm v])
  /-- A 64-bit two-address shift by an immediate below `64`, nonzero for `SHR:64`. -/
  | shiftImm (m d : String) (n : Nat) : m ∈ ["SHL:64", "SHR:64"] → gpOk d = true → n < 64 →
      (0 < n ∨ m = "SHL:64") → frame d = none → d ∉ W →
      ImgForm frame slotArr body k W (.Lopn [.reg d] m [.reg d, .imm n])
  /-- A 64-bit three-register left or logical right shift. -/
  | shiftReg (m d a b : String) : m ∈ ["SHL:64", "SHR:64"] → gpOk d = true → gpOk a = true →
      gpOk b = true → frame d = none → frame a = none → frame b = none → a ∉ W → b ∉ W →
      ImgForm frame slotArr body k W (.Lopn [.reg d] m [.reg a, .reg b])
  /-- The indexed load at stride `8` through a base holding an array pointer. -/
  | loadIdx (d b x : String) : gpOk d = true → gpOk b = true → gpOk x = true →
      gpNumU b % 8 ≠ 5 → (accArr slotArr body k b).isSome = true → frame d = none →
      frame b = none → frame x = none → b ∉ W → x ∉ W →
      ImgForm frame slotArr body k W (.Lopn [.reg d] "LOADIDX" [.arrIdx b x 8])
  /-- The indexed store at stride `8` through a base holding an array pointer. -/
  | storeIdx (a b x v : String) : gpOk b = true → gpOk x = true → gpOk v = true →
      gpNumU b % 8 ≠ 5 → cellParts? a = none → (accArr slotArr body k b).isSome = true →
      frame b = none → frame x = none → frame v = none → b ∉ W → x ∉ W → v ∉ W →
      ImgForm frame slotArr body k W (.Lopn [.reg a] "STOREIDX" [.arrIdx b x 8, .reg v])
  /-- The 64-bit carry-chain add over general-purpose names. -/
  | adcx (d a s c : String) : gpOk d = true → gpOk a = true → gpOk s = true → gpOk c = true →
      a ≠ c → s ≠ c → (a = d ∨ (d ≠ s ∧ d ≠ c)) → a ∉ W → s ∉ W →
      ImgForm frame slotArr body k W (.Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c])
  /-- The carry-out binding of a 64-bit add. -/
  | adcxhi (o a s c : String) : gpOk o = true → kOk (Params.ofBody body) a = true →
      kOk (Params.ofBody body) s = true → kOk (Params.ofBody body) c = true → a ≠ c → s ≠ c →
      (gpOk a = true ∨ (frame a).isSome = true) → (gpOk s = true ∨ (frame s).isSome = true) →
      (gpOk c = true ∨ (frame c).isSome = true) → a ∉ W → s ∉ W →
      ImgForm frame slotArr body k W (.Lopn [.reg o] "ADCXHI:64" [.reg a, .reg s, .reg c])
  /-- A label. -/
  | label (kd : LabelKind) (l : LLabel) : ImgForm frame slotArr body k W (.Llabel kd l)
  /-- A branch on a condition code with a polarity to a label of the body, one past which the
      width analysis contains every name of `W`. -/
  | cond (cc : String) (l : LLabel) (p : Nat) : (condPol cc).isSome = true →
      labelAt body l = some p → (∀ r ∈ W, r ∈ oneBitAt frame body (p + 1)) →
      ImgForm frame slotArr body k W (.Lcond (.reg cc) l)

/-- Every sub-form of `ImgForm` is a sub-form of `GateForm`. -/
theorem gateForm_of_imgForm {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {i : LinstrR} (h : ImgForm frame slotArr body k W i) : GateForm body i := by
  cases h with
  | movRR m d s hm hd hs => exact .movRR m d s hm hd hs
  | movStore m q s hm hq h1 h2 hs => exact .movStore m q s hm hq h1 h2 hs
  | movLoad m d q hm hd hq hk => exact .movLoad m d q hm hd hq hk
  | movImmBit d n hd hn => exact .movImm32 d n hd hn
  | movImm64 d v hd hv => exact .movImm64 d v hd hv
  | movImmSlot q v hq h1 h2 hv hor => exact .movImmSlot q v hq h1 h2 hv hor
  | select d c a b hd hc ha hb h1 h2 h3 => exact .select d c a b hd hc ha hb h1 h2 h3
  | setcc m d a b hm hd ha hb => exact .setcc m d a b hm hd ha hb
  | alu m d s hm hd hs => exact .alu m d s hm hd hs
  | aluImm m d v hm hd hv hf => exact .aluImm m d v hm hd hv hf
  | cmpImm d v hd hv => exact .cmpImm d v hd hv
  | shiftImm m d n hm hd hn h0 => exact .shiftImm m d n hm hd hn h0
  | shiftReg m d a b hm hd ha hb => exact .shiftReg m d a b hm hd ha hb
  | loadIdx d b x hd hb hx h5 => exact .loadIdx d b x hd hb hx h5
  | storeIdx a b x v hb hx hv h5 => exact .storeIdx a b x v hb hx hv h5
  | adcx d a s c hd ha hs hc h1 h2 h3 => exact .adcx d a s c hd ha hs hc h1 h2 h3
  | adcxhi o a s c ho ha hs hc h1 h2 => exact .adcxhi o a s c ho ha hs hc h1 h2
  | label kd l => exact .label kd l
  | cond cc l p hpol hp => exact .cond cc l hpol (by simp [hp])

/-- **`gateAtW` accepts every sub-form of `ImgForm`.** -/
theorem gateAtW_of_imgForm {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {W : List String}
    {i : LinstrR} (h : ImgForm frame slotArr body k W i) :
    gateAtW frame slotArr body k W i = true := by
  cases h with
  | movRR m d s hm hd hs hfd hfs hsW => exact gate_movRR hm hd hs hfd hfs hsW
  | movStore m q s hm hq _ _ hs hfq hfs hsW => exact gate_movStore hm hs hq hfq hfs hsW
  | movLoad m d q hm hd hq _ hfd hfq hqW => exact gate_movLoad hm hd hq hfd hfq hqW
  | movImmBit d n hd _ hfd hbit => exact gate_movImmBit hd hfd hbit
  | movImm64 d v hd _ hfd => exact gate_movImm64 hd hfd
  | movImmSlot q v hq _ _ _ _ hfq hsl => exact gate_movImmSlot hq hfq hsl
  | select d c a b hd hc ha hb _ hac hbc hfd hfc hfa hfb haW hbW =>
    exact gate_select hd hc ha hb hac hbc hfd hfc hfa hfb haW hbW
  | setcc m d a b hm hd ha hb hfd hfa hfb haW hbW =>
    exact gate_setcc hm hd ha hb hfd hfa hfb haW hbW
  | alu m d s hm hd hs hfd hfs hdW hsW =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | rfl
    all_goals first
      | exact gate_cmp hd hs hfd hfs hdW hsW
      | exact gate_alu (by subst h; simp) hd hs hfd hfs hdW hsW
  | aluImm m d v hm hd hv _ hfd hdW => exact gate_aluImm hm hd hfd hdW hv
  | cmpImm d v hd _ hfd hdW => exact gate_cmpImm hd hfd hdW
  | shiftImm m d n hm hd hn _ hfd hdW => exact gate_shiftImm hm hd hfd hdW hn
  | shiftReg m d a b hm hd ha hb hfd hfa hfb haW hbW =>
    exact gate_shiftReg hm hd ha hb hfd hfa hfb haW hbW
  | loadIdx d b x hd _ _ _ hacc hfd hfb hfx hbW hxW =>
    exact gate_loadIdx hd hacc hfd hfb hfx hbW hxW
  | storeIdx a b x v _ _ hv _ ha hacc hfb hfx hfv hbW hxW hvW =>
    exact gate_storeIdx ha hv hacc hfb hfx hfv hbW hxW hvW
  | adcx d a s c hd ha hs hc hac hsc _ haW hsW => exact gate_adcx hd ha hs hc hac hsc haW hsW
  | adcxhi o a s c ho ha hs hc hac hsc hfa hfs hfc haW hsW =>
    exact gate_adcxhi ho ha hs hc hfa hfs hfc hac hsc haW hsW
  | label kd l => exact gate_label frame slotArr body k W kd l
  | cond cc l p hpol hp hW => exact gate_cond hpol hp hW

/-- **The image gate accepts the legal forms of `ImgForm`**: every sub-form of `ImgForm` at the
    width analysis `oneBitAt frame body k` is a legal form of the x86 encoder in the context of
    `body`, and `instrGateBW` accepts it at position `k`. -/
theorem instrGateBW_of_legalForm {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat} {i : LinstrR}
    (h : ImgForm frame slotArr body k (oneBitAt frame body k) i) :
    LegalForm X86Isa.x86Isa x86Enc (x86Enc.ctx body) i
      ∧ instrGateBW frame slotArr body k i = true :=
  ⟨legalForm_of_gateForm (gateForm_of_imgForm h), gateAtW_of_imgForm h⟩

/-! ## 4. The legal forms the gate refuses -/

/-- The instruction `i` is a legal form in its one-instruction body `wb i`, which `instrGateBW`
    refuses at position `0` at the frame map and the array map without entries. -/
def ImgRefused (i : LinstrR) : Prop :=
  x86LegalB (x86Enc.ctx (wb i)) i = true
    ∧ instrGateBW (fun _ => none) (fun _ => none) (wb i) 0 i = false

/-- A whole-word load of a cell `mem.B.off` is a legal form the gate refuses (`regOkB` requires
    `cellA? = none`). Missing simulation case: the carry-chain simulation reads a cell only
    after the cell rewriting `cellBody` that the region back end applies before the gate. -/
theorem refusedImg_loadCell : ImgRefused (.Lopn [.reg "RAX"] "LOAD:64" [.reg "mem.RBX.8"]) := by
  unfold ImgRefused; constructor <;> rfl

/-- A whole-word store into a cell is a legal form the gate refuses. Missing simulation case,
    as for `refusedImg_loadCell`. -/
theorem refusedImg_storeCell :
    ImgRefused (.Lopn [.reg "mem.RBX.8"] "STORE:64" [.reg "RAX"]) := by
  unfold ImgRefused; constructor <;> rfl

/-- An untagged immediate move that is no carry constant (`bitMovB` requires a value below `2`
    whose next use is a carry-in) is a legal form the gate refuses. Missing simulation case: the
    simulation reads an untagged immediate move only as a one-bit carry constant. -/
theorem refusedImg_movImm32 : ImgRefused (.Lopn [.reg "RAX"] "MOV" [.imm 5]) := by
  unfold ImgRefused; constructor <;> rfl

/-- An unconditional jump is a legal form the gate refuses. Missing simulation case: the gate
    has no arm for `Lgoto`, and the carry-chain step lemmas have no case for it. -/
theorem refusedImg_goto : ImgRefused (.Lgoto ("", 1)) := by
  unfold ImgRefused; constructor <;> rfl

/-- A call is a legal form the gate refuses. Missing simulation case of the carry-chain
    simulation, which has no call arm. -/
theorem refusedImg_call : ImgRefused (.Lcall none ("f", 1)) := by
  unfold ImgRefused; constructor <;> rfl

/-- An indexed load at stride `4` is a legal form the gate refuses. Missing simulation case:
    the image `imgInstr` resolves indexed accesses at stride `8` only. -/
theorem refusedImg_loadIdx4 :
    ImgRefused (.Lopn [.reg "RAX"] "LOADIDX" [.arrIdx "RBX" "RCX" 4]) := by
  unfold ImgRefused; constructor <;> rfl

/-- An alignment directive is a legal form the gate refuses. Missing simulation case: the gate
    has no arm for `Lalign`. -/
theorem refusedImg_align : ImgRefused LinstrR.Lalign := by
  unfold ImgRefused; constructor <;> rfl

/-- A branch on a condition code without a zero-flag polarity (`condPol`) is a legal form the
    gate refuses. Missing simulation case: the simulation reads branches on the zero flag
    only. -/
theorem refusedImg_condCarry : ImgRefused (.Lcond (.reg "C") 1) := by
  unfold ImgRefused; constructor <;> rfl

/-- The overflow-chain carry-out `ADOXHI:64` is a legal form the gate refuses. Missing
    simulation case: the carry-chain simulation covers `ADCX:64` and `ADCXHI:64` only
    (`carryI?`). -/
theorem refusedImg_adoxhi :
    ImgRefused (.Lopn [.reg "RAX"] "ADOXHI:64" [.reg "RAX", .reg "RCX", .reg "RDX"]) := by
  unfold ImgRefused; constructor <;> rfl

/-- The width-tagged indexed load `LOADIDX:64` is a legal form the gate refuses. Missing
    simulation case: the image `imgInstr` and the gate read the untagged `LOADIDX` only. -/
theorem refusedImg_loadIdx64 :
    ImgRefused (.Lopn [.reg "RAX"] "LOADIDX:64" [.arrIdx "RBX" "RCX" 8]) := by
  unfold ImgRefused; constructor <;> decide +kernel

/-! ## 5. The gate of a body -/

/-- **A body that opens with the saves of its array slots reloads every array pointer after a
    save**: if every instruction of the prefix `pre` is a save `MOVQ qsave.R, R` whose source
    holds no array pointer, and every array slot is saved in `pre` or is an entry-held slot
    (`heldReg?`), then `reloadSavedB` holds of `pre ++ rest`. -/
theorem reloadSavedB_of_savePrefix {slotArr : String → Option (String × Nat)} {pre rest : Lcmd}
    (hpre : ∀ j ∈ pre, isSaveB j.li_i = true ∧
      ∀ d q, slotMov? j.li_i = some (d, q) → slotArr q = none)
    (hcover : ∀ q, (slotArr q).isSome = true → (heldReg? q).isSome = true ∨
      ∃ j ∈ pre, (slotMov? j.li_i).map Prod.fst = some q) :
    reloadSavedB slotArr (pre ++ rest) = true := by
  unfold reloadSavedB
  rw [List.all_eq_true]
  intro k _
  cases hb : (pre ++ rest)[k]? with
  | none => rfl
  | some i =>
    simp only
    cases hm : slotMov? i.li_i with
    | none => rfl
    | some p =>
      obtain ⟨d, q⟩ := p
      simp only
      by_cases hlt : k < pre.length
      · rw [List.getElem?_append_left hlt] at hb
        have hq := (hpre i (List.mem_of_getElem? hb)).2 d q hm
        simp [hq]
      · cases hs : slotArr q with
        | none => simp
        | some a =>
          rcases hcover q (by simp [hs]) with hh | ⟨j, hj, hjq⟩
          · simp [hh]
          · obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hj
            have hsave := (hpre _ hj).1
            simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range]
            right
            refine ⟨n, by omega, ?_⟩
            rw [List.getElem?_append_left hn, List.getElem?_eq_getElem hn]
            simp [hsave, hjq]

/-- **`imgGateBW` holds of a body of legal forms with a save prefix**: let `body = pre ++ rest`
    end with a return, every instruction before the last be a sub-form of `ImgForm` at its
    width analysis, and the prefix `pre` save the array slots as in
    `reloadSavedB_of_savePrefix`. Then `imgGateBW frame slotArr body` holds, and every
    instruction before the last is a legal form of the x86 encoder in the context of
    `body`. -/
theorem imgGateBW_of_legal {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {pre rest : Lcmd}
    (hform : ∀ k i, k + 1 < (pre ++ rest).length → (pre ++ rest)[k]? = some i →
      ImgForm frame slotArr (pre ++ rest) k (oneBitAt frame (pre ++ rest) k) i.li_i)
    (hret : ∃ ii, (pre ++ rest).getLast? = some ⟨ii, .Lret⟩)
    (hpre : ∀ j ∈ pre, isSaveB j.li_i = true ∧
      ∀ d q, slotMov? j.li_i = some (d, q) → slotArr q = none)
    (hcover : ∀ q, (slotArr q).isSome = true → (heldReg? q).isSome = true ∨
      ∃ j ∈ pre, (slotMov? j.li_i).map Prod.fst = some q) :
    imgGateBW frame slotArr (pre ++ rest) = true
      ∧ ∀ k i, k + 1 < (pre ++ rest).length → (pre ++ rest)[k]? = some i →
        LegalForm X86Isa.x86Isa x86Enc (x86Enc.ctx (pre ++ rest)) i.li_i := by
  refine ⟨?_, fun k i hk hi => (instrGateBW_of_legalForm (hform k i hk hi)).1⟩
  obtain ⟨ii, hl⟩ := hret
  simp only [imgGateBW, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨fun k hk => ?_, by simp [hl, isRetB]⟩, reloadSavedB_of_savePrefix hpre hcover⟩
  cases hi : (pre ++ rest)[k]? with
  | none => rfl
  | some i =>
    simpa using (instrGateBW_of_legalForm (hform k i (by omega) hi)).2

/-! ## 6. The class of the image of a body -/

/-- The slot `qsave.R` of a register is a frame-slot name. -/
theorem isSpillOrQsave_slotOfReg (R : String) : isSpillOrQsave (slotOfReg R) = true := by
  have e : ("qsave." : String).toList = ['q', 's', 'a', 'v', 'e', '.'] := by decide +kernel
  simp [isSpillOrQsave, slotOfReg, hasPrefix, String.toList_append, e]

/-- The save `m qsave.R, R` of a general-purpose register `R`, `m` one of `MOVQ` and `MOV:64`. -/
def SaveOf (j : Linstr) : Prop :=
  ∃ R m, gpOk R = true ∧ m ∈ ["MOVQ", "MOV:64"] ∧ j.li_i = .Lopn [.reg (slotOfReg R)] m [.reg R]

theorem slotMov?_of_saveOf {j : Linstr} (h : SaveOf j) :
    ∃ R, gpOk R = true ∧ slotMov? j.li_i = some (slotOfReg R, R) := by
  obtain ⟨R, m, hR, hm, hj⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  refine ⟨R, hR, ?_⟩
  rw [hj]
  rcases hm with rfl | rfl <;> simp [slotMov?]

/-- **The class `physImgB` of a body with a save prefix**: let every instruction of the prefix
    `pre` be the save of a general-purpose register (`SaveOf`), let no instruction of `rest`
    write an array slot, and let every indexed access of `rest` resolve to an array
    (`accOkB`). Then `physImgB slotArr (pre ++ rest)` holds. -/
theorem physImgB_of_savePrefix {slotArr : String → Option (String × Nat)} {pre rest : Lcmd}
    (hpre : ∀ j ∈ pre, SaveOf j)
    (hrest : ∀ j ∈ rest, ∀ ds o ss, j.li_i = .Lopn ds o ss → ∀ x ∈ ds,
      (∀ q, x = .reg q → slotArr q = none) ∧ (∀ q n, x = .arr q n → slotArr q = none)
        ∧ (∀ q i sc, x = .arrIdx q i sc → slotArr q = none))
    (hacc : ∀ k i, pre.length ≤ k → (pre ++ rest)[k]? = some i →
      accOkB slotArr (pre ++ rest) k i.li_i = true) :
    physImgB slotArr (pre ++ rest) = true := by
  unfold physImgB
  rw [List.all_eq_true]
  intro k _
  cases hb : (pre ++ rest)[k]? with
  | none => rfl
  | some i =>
    simp only [Bool.and_eq_true]
    by_cases hlt : k < pre.length
    · rw [List.getElem?_append_left hlt] at hb
      have hi := List.mem_of_getElem? hb
      obtain ⟨R, m, hR, hm, hj⟩ := hpre i hi
      have hent : entryRegB (pre ++ rest) k R = true := by
        unfold entryRegB
        rw [List.take_append_of_le_length (by omega), List.all_eq_true]
        intro j hj'
        obtain ⟨R', hR', hs⟩ := slotMov?_of_saveOf (hpre j (List.mem_of_mem_take hj'))
        have hne : slotOfReg R' ≠ R := by
          intro e
          have := not_gpOk_of_slot (isSpillOrQsave_slotOfReg R')
          rw [e, hR] at this
          cases this
        simp [hs, hne]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rw [hj]
      rcases hm with rfl | rfl <;> simp [accOkB, slotWriteB, slotMov?, hent]
    · refine ⟨hacc k i (by omega) hb, ?_⟩
      rw [List.getElem?_append_right (by omega)] at hb
      have hi := List.mem_of_getElem? hb
      unfold slotWriteB
      split
      · rename_i ds o ss heq
        rw [List.all_eq_true]
        intro x hx
        obtain ⟨h1, h2, h3⟩ := hrest i hi ds o ss heq x hx
        cases x with
        | reg q => simp [h1 q rfl]
        | arr q n => simp [h2 q n rfl]
        | arrIdx q j sc => simp [h3 q j sc rfl]
        | imm _ => rfl
      · rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImgGateOfLegal
