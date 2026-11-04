/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGenStraight
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrMnemDispatch

@[expose] public section

set_option autoImplicit false

/-!
# The decoded bytes of a printed body simulate its flag-machine run

The printed body of the owned back end names physical registers (`RAX`, …, `R15`) and frame
words (`qsave.X`, `k.N`). Its function bytes `encodeLfundefBytes` decode
(`DecodeLayout.decodeLprog_encodeLfundefBytes`) to the program of the computed shapes of its
instructions. This module proves, by induction over the body and one lemma per encoder arm,
that the decoded program simulates the flag machine `lsemFuelMemF` run on the body, under the
identity correspondence of the printer: a physical name `R` reads the machine register
`phys R`, and a written frame word reads the word at its frame address.

## The arms

`classify` reads an instruction into one of the covered arms `Arm`; `Arm.ok` is the Boolean
condition of an arm, and `Arm.pieces` its bytes with their decoded instructions. The arms are
the register moves `MOV:64` and `MOVQ`, the immediate move of a sign-extended `imm32`, the
store and the load of a frame word, the two-address `ADD`, `SUB`, `AND`, `OR`, `XOR` with a
register or a sign-extended `imm8` source, the count-in-mnemonic shifts `SHR:k:64` and
`SHL:k:64` by a nonzero count, the count-`0` shift `SHL:0:64`, a register copy, and the load-effective-address `LEA:64` over the
SIB form `[B + X · sc]`.

## Main results

* `pieces_unique`, `shapeOf_lopn_ops`: the decoded instructions of an `Lopn` are determined
  by any decomposition of its bytes into decodable pieces.
* `phys_inj`: the machine register map is injective on the general-purpose names.
* `Arm.bytes`: the encoder lays down the pieces of an arm whose conditions hold.
* `Arm.sim`: the flag-machine step of such an arm is simulated by its decoded instructions,
  from the correspondence `PCorr` to `PCorr`.
* `lineOK_sim`: a segment accepted by `lineOK` is simulated by the decoded instructions of
  its computed shapes, by induction over the segment.
* `printed_line_sim`, `printedLine_sim`: for every straight-line body in the class
  `printedLineB`, every halting flag-machine run from the identity correspondence is
  matched by a halting run of `aMachine` on the decoded function bytes, ending in the
  identity correspondence with the stack register restored.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout
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
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedLsemStep

/-! ## 1. The decoded instructions of one instruction's bytes -/

/-- A piece that decodes in front of every continuation is not empty. -/
theorem pieceDec_ne_nil {q : List (BitVec 8) × JInstr 64} (h : PieceDec q) : q.1 ≠ [] := by
  intro he
  have h0 := h []
  rw [he] at h0
  simp [decodeLinstr] at h0

/-- **Pieces are unique.** Two lists of pieces, each decoding in front of every
    continuation, with one concatenation, carry the same instructions. -/
theorem pieces_unique :
    ∀ (p₁ p₂ : List (List (BitVec 8) × JInstr 64)), (∀ q ∈ p₁, PieceDec q) →
      (∀ q ∈ p₂, PieceDec q) → p₁.flatMap Prod.fst = p₂.flatMap Prod.fst →
      p₁.map Prod.snd = p₂.map Prod.snd := by
  intro p₁
  induction p₁ with
  | nil =>
    intro p₂ _ h₂ he
    cases p₂ with
    | nil => rfl
    | cons q r =>
      exfalso
      simp only [List.flatMap_nil, List.flatMap_cons] at he
      exact pieceDec_ne_nil (h₂ q List.mem_cons_self) (List.append_eq_nil_iff.mp he.symm).1
  | cons q r ih =>
    intro p₂ h₁ h₂ he
    cases p₂ with
    | nil =>
      exfalso
      simp only [List.flatMap_nil, List.flatMap_cons] at he
      exact pieceDec_ne_nil (h₁ q List.mem_cons_self) (List.append_eq_nil_iff.mp he).1
    | cons q' r' =>
      simp only [List.flatMap_cons] at he
      obtain ⟨-, hx, hr⟩ :=
        decodeLinstr_prefix_free (h₁ q List.mem_cons_self) (h₂ q' List.mem_cons_self) he
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨DInstr.op.inj hx, ih r' (fun x hx => h₁ x (List.mem_cons_of_mem _ hx))
        (fun x hx => h₂ x (List.mem_cons_of_mem _ hx)) hr⟩

/-- **The computed shape of an `Lopn` is its pieces.** When the bytes of an `Lopn` are the
    concatenation of pieces that each decode in front of every continuation, every shape
    `shapeOf` computes for it decodes to the instructions of those pieces. -/
theorem shapeOf_lopn_ops {P : Params} {ds : List LOperand} {o : String} {ss : List LOperand}
    {sh : DShape} (pcs : List (List (BitVec 8) × JInstr 64))
    (hb : encodeLopn P.frame P.spillW (.Lopn ds o ss) P.qsaveB = pcs.flatMap Prod.fst)
    (hp : ∀ q ∈ pcs, PieceDec q) (h : shapeOf P (.Lopn ds o ss) = some sh) :
    sh.ops' = pcs.map Prod.snd := by
  rcases shapeOfBytes_ok (bs := encodeLopn P.frame P.spillW (.Lopn ds o ss) P.qsaveB) h with
    ⟨q, rfl, hbq, hq⟩ | ⟨pcs', rfl, hb', hq'⟩
  · have := pieces_unique [q] pcs (by simpa using hq) hp (by simpa [hb] using hbq.symm)
    simpa [DShape.ops'] using this
  · exact pieces_unique pcs' pcs hq' hp (by rw [hb', hb])

/-! ## 2. Physical register names -/

/-- The general-purpose names of a printed body other than the stack register `RSP`. -/
def gpList : List String :=
  ["RAX", "RCX", "RDX", "RBX", "RBP", "RSI", "RDI", "R8", "R9", "R10", "R11", "R12", "R13",
    "R14", "R15"]

/-- A general-purpose name of a printed body other than the stack register. -/
def gpOk (r : String) : Bool := gpList.contains r

/-- The machine register of a physical name: the canonical `%rN` name of its register
    number. -/
def phys (r : String) : String := SailX86Decoder.regName (gpNumU r)

/-- The physical name of a register number, a left inverse of `gpNumU` on `gpList`. -/
def numU (n : Nat) : String := (gpList.find? (fun r => gpNumU r == n)).getD ""

theorem mem_gpList {r : String} (h : gpOk r = true) : r ∈ gpList := by
  simpa [gpOk] using h

theorem numU_gpNumU {r : String} (h : gpOk r = true) : numU (gpNumU r) = r := by
  have hm := mem_gpList h
  simp only [gpList, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

theorem gpNum_phys {r : String} (h : gpOk r = true) : ScalarEncoder.gpNum (phys r) = gpNumU r := by
  have hm := mem_gpList h
  simp only [gpList, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> decide

/-- `phys` is injective on the general-purpose names. -/
theorem phys_inj {r d : String} (hr : gpOk r = true) (hd : gpOk d = true)
    (h : phys r = phys d) : r = d := by
  rw [← numU_gpNumU hr, ← numU_gpNumU hd, ← gpNum_phys hr, ← gpNum_phys hd, h]

/-- Facts of a general-purpose name: its register number, its register name, and that it is
    no spill, save or memory name. -/
structure GpFacts (r : String) : Prop where
  isGp : isGpName r = true
  notSlot : isSpillOrQsave r = false
  notMem : parseMemName r = none
  ne4 : gpNumU r ≠ 4
  physNe : phys r ≠ "%rsp"
  off : ∀ F W qB, spillQsaveOff F W r qB = none

theorem gpFacts {r : String} (h : gpOk r = true) : GpFacts r := by
  have hm := mem_gpList h
  simp only [gpList, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, fun _ _ _ => rfl⟩

/-! ## 3. The bytes of the covered arms -/

/-- The two-address `encTwoAddr` form between two general-purpose names is the register
    form, for an opcode other than the `LOAD` opcode `0x8B`. -/
theorem encTwoAddr_rr (F W w op : Nat) (D S : String) (qB : Nat) (hD : gpOk D = true)
    (hS : gpOk S = true) (hop : op ≠ 0x8b) :
    encTwoAddr F W w op (.reg D) (.reg S) qB = encAluRRw w op (gpNumU D) (gpNumU S) := by
  have fD := gpFacts hD
  have fS := gpFacts hS
  simp [encTwoAddr, fD.off, fS.off, fD.notMem, fS.notMem, fD.isGp, fS.isGp, memDstOp, hop]

/-- The operation `op` (`ADD`, a move or `LOAD`) of a general-purpose name into a frame
    word: for a move, the store `0x89`. -/
theorem encTwoAddr_store (F W w op : Nat) (q S : String) (qB : Nat) (off : Int)
    (hq : spillQsaveOff F W q qB = some off) (hS : gpOk S = true)
    (hop : op = 0x01 ∨ op = 0x89 ∨ op = 0x8b) :
    encTwoAddr F W w op (.reg q) (.reg S) qB = encRspMem w (memDstOp op) (gpNumU S) off := by
  have fS := gpFacts hS
  simp only [encTwoAddr, hq, fS.off, fS.isGp, ite_true, ite_eq_left hop]

/-- The operation `op` (`ADD`, a move or `LOAD`) of a frame word into a general-purpose
    name: for a move, the load `0x8b`. -/
theorem encTwoAddr_load (F W w op : Nat) (D q : String) (qB : Nat) (off : Int)
    (hq : spillQsaveOff F W q qB = some off) (hD : gpOk D = true)
    (hop : op = 0x01 ∨ op = 0x89 ∨ op = 0x8b) :
    encTwoAddr F W w op (.reg D) (.reg q) qB = encRspMem w (memSrcOp op) (gpNumU D) off := by
  have fD := gpFacts hD
  simp only [encTwoAddr, hq, fD.off, fD.isGp, ite_true, ite_eq_left hop]

/-- The register moves of a printed body: `MOV:64` and the whole-word `MOVQ`. -/
def isMovM (m : String) : Bool := m == "MOV:64" || m == "MOVQ"

/-- A register move dispatches to the two-address move form at `REX.W = 1`. -/
theorem encodeLopn_movM (F W : Nat) (m D S : String) (qB : Nat) (hm : isMovM m = true) :
    encodeLopn F W (.Lopn [.reg D] m [.reg S]) qB
      = encTwoAddr F W 1 0x89 (.reg D) (.reg S) qB := by
  simp only [isMovM, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with rfl | rfl
  · exact LprogJInstrMnemDispatch.encodeLopn_mov F W D S qB
  · exact LprogJInstrMnemDispatch.dispatch_alu_one F W 0x89 "MOVQ" "MOVQ" D S qB
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The immediate move `MOV:64 D, #v` of a value in the sign-extended `imm32` range. -/
theorem encodeLopn_movImm (F W : Nat) (D : String) (v qB : Nat) (hD : gpOk D = true)
    (hv : ScalarEncoder.fitsImm32S v = true) :
    encodeLopn F W (.Lopn [.reg D] "MOV:64" [.imm v]) qB = encMovImmw 1 (gpNumU D) v := by
  have fD := gpFacts hD
  simp only [ScalarEncoder.fitsImm32S] at hv
  simp only [encodeLopn,
    show (isCarryOutBinding "MOV:64" || isMulHiBinding "MOV:64") = false from by decide +kernel,
    show stripWidthTag "MOV:64" = "MOV" from by decide +kernel,
    show mnemWidth "MOV:64" = 64 from by decide +kernel,
    show ("MOV" == "MULX") = false from by decide +kernel,
    show ("MOV" == "MULXMEM") = false from by decide +kernel,
    show adxPrefix "MOV" = none from by decide +kernel,
    LprogBytes.rexW, Bool.false_eq_true, ite_false, ite_true, fD.notSlot, Bool.false_and]
  simp [encImmOp, fD.notSlot, hv]

/-- The two-address arithmetic and logic mnemonics of the covered fragment, with the opcode of
    their register form and their machine instruction. -/
def aluArm : String → Option (Nat × (String → JOperand → JInstr 64))
  | "ADD:64" => some (0x01, .add)
  | "SUB:64" => some (0x29, .sub)
  | "AND:64" => some (0x21, .and_)
  | "OR:64" => some (0x09, .or_)
  | "XOR:64" => some (0x31, .xor_)
  | _ => none

/-- A two-address arithmetic or logic instruction dispatches to the two-address register
    form of its opcode, which is in the decoder's table with its machine instruction. -/
theorem encodeLopn_alu (F W : Nat) (m D A S : String) (qB : Nat) {op : Nat}
    {mk : String → JOperand → JInstr 64} (h : aluArm m = some (op, mk)) :
    encodeLopn F W (.Lopn [.reg D] m [.reg A, .reg S]) qB
        = encTwoAddr F W 1 op (.reg D) (.reg S) qB
      ∧ aluTableOp op = true ∧ aluMnemonic op = some mk := by
  unfold aluArm at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;>
    exact ⟨LprogJInstrMnemDispatch.dispatch_alu_two F W _ _ _ D A S qB
      (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      by decide, rfl⟩

/-- A count-in-mnemonic shift between general-purpose names: the copy of the source when it
    is not the destination, then the shift of the destination in place. -/
theorem encodeLopn_shift (F W : Nat) (m D S : String) (qB ext : Nat)
    (hbind : (isCarryOutBinding m || isMulHiBinding m) = false)
    (hmulx : (stripWidthTag m == "MULX") = false)
    (hmulxmem : (stripWidthTag m == "MULXMEM") = false)
    (hadx : adxPrefix (stripWidthTag m) = none)
    (hext : tagShiftExt (stripWidthTag m) = some ext)
    (hD : gpOk D = true) (hS : gpOk S = true) (hn : tagShiftCount (stripWidthTag m) ≠ 0) :
    encodeLopn F W (.Lopn [.reg D] m [.reg S]) qB
      = (if D = S then [] else encAluRRw (LprogBytes.rexW (mnemWidth m)) 0x89 (gpNumU D) (gpNumU S))
        ++ encTagShift (LprogBytes.rexW (mnemWidth m)) ext (gpNumU D) (stripWidthTag m) := by
  have fD := gpFacts hD
  have fS := gpFacts hS
  simp only [encodeLopn, hbind, hmulx, hmulxmem, hadx, hext, fD.isGp, fS.isGp,
    Bool.false_eq_true, ite_false, Bool.and_self, ite_true, ite_eq_right hn, beq_iff_eq]

/-- The immediate form of an arithmetic or logic mnemonic of `aluArm`: its encoding as the
    sign-extended `imm8` group-1 form under the opcode extension `dig`, the decoder's reading
    of that form, the flag-machine step, and the machine semantics, all through one word
    function `f`. -/
theorem aluArm_imm {m : String} {op : Nat} {mk : String → JOperand → JInstr 64}
    (h : aluArm m = some (op, mk)) :
    ∃ (dig : Nat) (f : BitVec 64 → BitVec 64 → BitVec 64),
      (∀ (F W : Nat) (D : String) (v qB : Nat), gpOk D = true → fitsImm8S 1 v = true →
        encodeLopn F W (.Lopn [.reg D] m [.reg D, .imm v]) qB = encAluImm8 1 dig (gpNumU D) v)
      ∧ dig < 8 ∧ aluImm8Mnemonic dig = some mk ∧ aluImmDigit (stripWidthTag m) = some dig
      ∧ (∀ (st : LstateM) (D : String) (va : BitVec 64) (k : Nat),
          st.reg.getW D 64 = some va →
          lsemStepMem (.Lopn [.reg D] m [.reg D, .imm k], .reg none) st
            = some ((st.setReg D (f va (BitVec.ofNat 64 k))).nextPc))
      ∧ (∀ (sa : AState) (D r : String) (k : Nat), (evalInstrA sa (mk D (.imm k))).regs r
          = if r = D then f (sa.regs D) (BitVec.ofNat 64 k) else sa.regs r)
      ∧ (∀ (sa : AState) (D : String) (k : Nat),
          (evalInstrA sa (mk D (.imm k))).mem = sa.mem) := by
  unfold aluArm at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h
  all_goals first
    | refine ⟨0, (· + ·), ?_, by decide, rfl, by decide +kernel, ?_, fun _ _ _ _ => rfl,
        fun _ _ _ => rfl⟩
    | refine ⟨5, (· - ·), ?_, by decide, rfl, by decide +kernel, ?_, fun _ _ _ _ => rfl,
        fun _ _ _ => rfl⟩
    | refine ⟨4, (· &&& ·), ?_, by decide, rfl, by decide +kernel, ?_, fun _ _ _ _ => rfl,
        fun _ _ _ => rfl⟩
    | refine ⟨1, (· ||| ·), ?_, by decide, rfl, by decide +kernel, ?_, fun _ _ _ _ => rfl,
        fun _ _ _ => rfl⟩
    | refine ⟨6, (· ^^^ ·), ?_, by decide, rfl, by decide +kernel, ?_, fun _ _ _ _ => rfl,
        fun _ _ _ => rfl⟩
  all_goals first
    | (intro F W D v qB hD hv
       have fD := gpFacts hD
       simp only [encodeLopn, isCarryOutBinding, isMulHiBinding, stripWidthTag, mnemWidth,
         adxPrefix, hasSuffix, LprogBytes.rexW]
       simp (config := { decide := true }) [encImmOp, fD.notSlot, hv, shiftImmExt,
         aluImmDigit])
    | (intro st D va k hg
       rw [lsemStepMem_reg, JasminLsemCast.lsemStepCast_of_delegate _ _ (Or.inr rfl),
         JasminLsemMulCarry.lsemStepMC_of_delegate _ _ rfl rfl rfl rfl rfl,
         JasminLsemShift.lsemStepSh_of_not_sar _ _
           (by simp (config := { decide := true }) [JasminLsemShift.sarStruct?])]
       simp (config := { decide := true }) only [lsemStepN, readReg_of_getW hg,
         evalOperandN, stripWidthTag, applyOpnN]
       rfl)

/-- The `imm32` form of an arithmetic or logic mnemonic of `aluArm`: for an immediate outside
    the sign-extended `imm8` range that sign-extends from 32 bits, the encoder lays down the
    group-1 form `81 /dig id` under the opcode extension `dig`, which the decoder reads as the
    machine instruction `mk`. -/
theorem aluArm_imm32 {m : String} {op : Nat} {mk : String → JOperand → JInstr 64}
    (h : aluArm m = some (op, mk)) :
    ∃ dig : Nat, aluImmDigit (stripWidthTag m) = some dig ∧ dig < 8
      ∧ aluImmMnemonic dig = some mk
      ∧ ∀ (F W : Nat) (D : String) (v qB : Nat), gpOk D = true → fitsImm8S 1 v = false →
        ScalarEncoder.fitsImm32S v = true →
        encodeLopn F W (.Lopn [.reg D] m [.reg D, .imm v]) qB = encAluImmw 1 dig (gpNumU D) v := by
  unfold aluArm at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h
  all_goals first
    | refine ⟨0, by decide +kernel, by decide, rfl, ?_⟩
    | refine ⟨5, by decide +kernel, by decide, rfl, ?_⟩
    | refine ⟨4, by decide +kernel, by decide, rfl, ?_⟩
    | refine ⟨1, by decide +kernel, by decide, rfl, ?_⟩
    | refine ⟨6, by decide +kernel, by decide, rfl, ?_⟩
  all_goals
    intro F W D v qB hD h8 h32
    have fD := gpFacts hD
    have hi : imm32Fits 1 v = true := by
      simpa [imm32Fits, ScalarEncoder.fitsImm32S] using h32
    simp only [encodeLopn, isCarryOutBinding, isMulHiBinding, stripWidthTag, mnemWidth,
      adxPrefix, hasSuffix, LprogBytes.rexW]
    simp (config := { decide := true }) [encImmOp, fD.notSlot, h8, hi, shiftImmExt,
      aluImmDigit]

/-- The shift mnemonics of the immediate-count arm: `SHL:64` and `SHR:64`. -/
def isShI (m : String) : Bool := m == "SHL:64" || m == "SHR:64"

/-- The group-2 opcode extension of an immediate-count shift: `4` for `SHL:64`, `5` for
    `SHR:64`. -/
def shIExt (m : String) : Nat := if m = "SHL:64" then 4 else 5

/-- The machine shift of an immediate-count shift: `shl` for `SHL:64`, `shr` for `SHR:64`. -/
def shIMk (m : String) : String → JOperand → JInstr 64 :=
  if m = "SHL:64" then JInstr.shl else JInstr.shr

/-- The bytes of the immediate-count shift by `k` of the register numbered `n`: the
    shift-by-one form `D1 /ext` for `k = 1`, the shift-by-`imm8` form `C1 /ext ib`
    otherwise. -/
def shIBytes (m : String) (n k : Nat) : List (BitVec 8) :=
  if k = 1 then encShift1 1 (shIExt m) n else encShiftImmw 1 (shIExt m) n k

/-- An immediate-count shift `SHL:64`/`SHR:64` of a general-purpose name in place
    dispatches to `shIBytes`. -/
theorem encodeLopn_shI (F W : Nat) (m D : String) (k qB : Nat) (hm : isShI m = true)
    (hD : gpOk D = true) :
    encodeLopn F W (.Lopn [.reg D] m [.reg D, .imm k]) qB = shIBytes m (gpNumU D) k := by
  have fD := gpFacts hD
  simp only [isShI, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with rfl | rfl <;>
  · simp only [encodeLopn, isCarryOutBinding, isMulHiBinding, stripWidthTag, mnemWidth,
      adxPrefix, hasSuffix, LprogBytes.rexW]
    simp (config := { decide := true }) [encImmOp, fD.notSlot, shiftImmExt, shIBytes, shIExt]

/-- The immediate-count shift of a general-purpose name by `0 < k < 64` decodes to the
    machine shift of its register. -/
theorem pieceDec_shI (m D : String) (k : Nat) (hm : isShI m = true) (hk : k < 64) :
    PieceDec (shIBytes m (gpNumU D) k, shIMk m (phys D) (.imm k)) := by
  intro rest
  simp only [isShI, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with rfl | rfl
  · by_cases h1 : k = 1
    · subst h1
      simpa [phys, shIBytes, shIExt, shIMk] using
        decodeLinstr_shift1 4 (gpNumU D) rest (Or.inl rfl) (gpNumU_lt_16 D)
    · simpa [phys, shIBytes, shIExt, shIMk, h1] using
        decodeLinstr_shiftImm8 4 (gpNumU D) k rest (Or.inl rfl) (gpNumU_lt_16 D) (by omega)
  · by_cases h1 : k = 1
    · subst h1
      simpa [phys, shIBytes, shIExt, shIMk] using
        decodeLinstr_shift1 5 (gpNumU D) rest (Or.inr (Or.inl rfl)) (gpNumU_lt_16 D)
    · simpa [phys, shIBytes, shIExt, shIMk, h1] using
        decodeLinstr_shiftImm8 5 (gpNumU D) k rest (Or.inr (Or.inl rfl)) (gpNumU_lt_16 D)
          (by omega)

/-- A count-`0` count-in-mnemonic shift between general-purpose names: no bytes when `D` is
    `S`, the register copy otherwise. -/
theorem encodeLopn_shift0 (F W : Nat) (m D S : String) (qB ext : Nat)
    (hbind : (isCarryOutBinding m || isMulHiBinding m) = false)
    (hmulx : (stripWidthTag m == "MULX") = false)
    (hmulxmem : (stripWidthTag m == "MULXMEM") = false)
    (hadx : adxPrefix (stripWidthTag m) = none)
    (hext : tagShiftExt (stripWidthTag m) = some ext)
    (hD : gpOk D = true) (hS : gpOk S = true) (hn : tagShiftCount (stripWidthTag m) = 0) :
    encodeLopn F W (.Lopn [.reg D] m [.reg S]) qB
      = if D = S then [] else
          encAluRRw (LprogBytes.rexW (mnemWidth m)) 0x89 (gpNumU D) (gpNumU S) := by
  have fD := gpFacts hD
  have fS := gpFacts hS
  simp only [encodeLopn, hbind, hmulx, hmulxmem, hadx, hext, fD.isGp, fS.isGp,
    Bool.false_eq_true, ite_false, Bool.and_self, ite_true, hn, beq_iff_eq]

/-- The load-effective-address `LEA:64 D, [B + X · sc]` between general-purpose names, with
    an index other than `RSP` and a stride the SIB byte encodes, dispatches to the SIB form
    `REX.W 8D /r`. -/
theorem encodeLopn_leaIdx (F W : Nat) (D B X : String) (sc qB : Nat) (hD : gpOk D = true)
    (hB : gpOk B = true) (hX : gpOk X = true) (h4 : gpNumU X ≠ 4)
    (hs : ScalarEncoder.scaleOk sc = true) :
    encodeLopn F W (.Lopn [.reg D] "LEA:64" [.arrIdx B X sc]) qB
      = encMemMovSibw 1 0x8d (gpNumU D) (gpNumU B) (gpNumU X) sc := by
  have fD := gpFacts hD
  have fB := gpFacts hB
  have fX := gpFacts hX
  simp only [ScalarEncoder.scaleOk] at hs
  simp only [encodeLopn,
    show (isCarryOutBinding "LEA:64" || isMulHiBinding "LEA:64") = false from by decide +kernel,
    show stripWidthTag "LEA:64" = "LEA" from by decide +kernel,
    show mnemWidth "LEA:64" = 64 from by decide +kernel,
    show ("LEA" == "MULX") = false from by decide +kernel,
    show ("LEA" == "MULXMEM") = false from by decide +kernel,
    show adxPrefix "LEA" = none from by decide +kernel,
    show tagShiftExt "LEA" = none from by decide +kernel,
    show aluOpcode "LEA" = none from by decide +kernel,
    show twoByteOpcode "LEA" = none from by decide +kernel,
    show ("LEA" == "LEA") = true from by decide +kernel,
    LprogBytes.rexW, fD.isGp, fB.isGp, fX.isGp, Bool.false_eq_true, ite_false, ite_true]
  simp [h4, hs]

/-! ## 4. The decoded pieces of the covered arms -/

/-- `SHR $k, %d` (`REX.W C1 /5 ib`) on a general-purpose name decodes to the shift of its
    machine register. -/
theorem pieceDec_shrImm (D : String) (k : Nat) (hD : gpOk D = true) (hk : k < 256) :
    PieceDec (encShiftImmw 1 5 (gpNumU D) k, .shr (phys D) (.imm k)) := by
  intro rest
  rw [LprogJInstrBytesAgree.encShiftImmw_one]
  apply decodeLinstr_of_decodeJ1
  have h := roundtrip_shr [(phys D, phys D)] (phys D) k rest hk
  have e : ScalarEncoder.gpNum (SailX86Decoder.regName (gpNumU D)) = gpNumU D := gpNum_phys hD
  simpa [ScalarEncoder.encodeJInstr, renameJ, nameOf, operandOf, AsmPrinter.regOf, e, phys]
    using h

/-- The register copy between two general-purpose names. -/
theorem pieceDec_movRR (D S : String) :
    PieceDec (encAluRRw 1 0x89 (gpNumU D) (gpNumU S), .mov (phys D) (.reg (phys S))) :=
  fun rest => decodeLinstr_movRR _ _ rest (gpNumU_lt_16 D) (gpNumU_lt_16 S)

/-- The shift of a general-purpose name by a count `0 < k < 64`. -/
theorem pieceDec_tagShr (D : String) (k : Nat) (hD : gpOk D = true) (hk0 : k ≠ 0)
    (hk : k < 64) (base : String) (hc : tagShiftCount base = k) :
    PieceDec (encTagShift 1 5 (gpNumU D) base, .shr (phys D) (.imm k)) := by
  unfold encTagShift
  rw [hc]
  by_cases h1 : k = 1
  · subst h1
    intro rest
    have h := decodeLinstr_shift1 5 (gpNumU D) rest (Or.inr (Or.inl rfl)) (gpNumU_lt_16 D)
    simpa [phys] using h
  · simp only [h1, ite_false]
    exact pieceDec_shrImm D k hD (by omega)

/-- A count-in-mnemonic shift is a left shift: its group-2 opcode extension is `4`. -/
def tagShl (m : String) : Bool := tagShiftExt (stripWidthTag m) == some 4

/-- A count-in-mnemonic shift is a right rotate: its group-2 opcode extension is `1`. -/
def tagRor (m : String) : Bool := tagShiftExt (stripWidthTag m) == some 1

/-- The group-2 opcode extension of a count-in-mnemonic shift: `4` for a left shift, `1` for a
    right rotate, `5` otherwise. -/
def tagShExt (m : String) : Nat := if tagShl m then 4 else if tagRor m then 1 else 5

/-- The mnemonic stem of a count-in-mnemonic shift: `SHL` for a left shift, `ROR` for a right
    rotate, `SHR` otherwise. -/
def tagShName (m : String) : String :=
  if tagShl m then "SHL" else if tagRor m then "ROR" else "SHR"

/-- The machine shift of a count-in-mnemonic shift: `shl` for a left shift, `ror` for a right
    rotate, `shr` otherwise. -/
def tagShMk (m : String) : String → JOperand → JInstr 64 :=
  if tagShl m then JInstr.shl else if tagRor m then JInstr.ror else JInstr.shr

/-- The count-in-mnemonic shift of a general-purpose name by a count `0 < k < 64` decodes to
    the machine shift of its register, in the direction of the mnemonic. -/
theorem pieceDec_tagShift (m D : String) (k : Nat) (hD : gpOk D = true) (hk0 : k ≠ 0)
    (hk : k < 64) (base : String) (hc : tagShiftCount base = k) :
    PieceDec (encTagShift 1 (tagShExt m) (gpNumU D) base, tagShMk m (phys D) (.imm k)) := by
  by_cases hs : tagShl m = true
  · simp only [tagShExt, tagShMk, hs, ite_true]
    unfold encTagShift
    rw [hc]
    intro rest
    by_cases h1 : k = 1
    · subst h1
      simpa [phys] using
        decodeLinstr_shift1 4 (gpNumU D) rest (Or.inl rfl) (gpNumU_lt_16 D)
    · simpa [phys, h1] using
        decodeLinstr_shiftImm8 4 (gpNumU D) k rest (Or.inl rfl) (gpNumU_lt_16 D) (by omega)
  · by_cases hr : tagRor m = true
    · simp only [tagShExt, tagShMk, hs, hr, Bool.false_eq_true, ite_false, ite_true]
      unfold encTagShift
      rw [hc]
      intro rest
      by_cases h1 : k = 1
      · subst h1
        simpa [phys] using decodeLinstr_ror1 (gpNumU D) rest (gpNumU_lt_16 D)
      · simpa [phys, h1] using
          decodeLinstr_rorImm8 (gpNumU D) k rest (gpNumU_lt_16 D) (by omega)
    · simp only [tagShExt, tagShMk, hs, hr, Bool.false_eq_true, ite_false]
      exact pieceDec_tagShr D k hD hk0 hk base hc

/-! ## 5. The covered arms -/

/-- A covered instruction of a printed body. -/
inductive Arm where
  /-- A register move `m D, S` between general-purpose names. -/
  | movRR (m D S : String)
  /-- The immediate move `MOV:64 D, #v`. -/
  | movRI (D : String) (v : Nat)
  /-- The store `m q, S` of a general-purpose name to the frame word named `q`. -/
  | store (m q S : String)
  /-- The load `m D, q` of the frame word named `q`. -/
  | load (m D q : String)
  /-- The two-address operation `m D, D, S`. -/
  | alu (m D S : String)
  /-- The two-address operation `m D, D, #v` with a sign-extended `imm8` or `imm32`
      immediate. -/
  | aluI (m D : String) (v : Nat)
  /-- The count-in-mnemonic shift `m D, S` by a nonzero count, `m` the mnemonic `SHR:k:64` or
      `SHL:k:64`. -/
  | shr (m D S : String)
  /-- The count-`0` shift `m D, S` with `m` the mnemonic `SHL:0:64`, a copy. -/
  | shl0 (m D S : String)
  /-- The two-address shift `m D, D, #k` by an immediate count, `m` the mnemonic `SHL:64` or
      `SHR:64`. -/
  | shI (m D : String) (k : Nat)
  /-- The load-effective-address `LEA:64 D, [B + X · sc]` over the SIB form. -/
  | lea (D B X : String) (sc : Nat)

/-- The instruction of an arm. -/
def Arm.instr : Arm → LinstrR
  | .movRR m D S => .Lopn [.reg D] m [.reg S]
  | .movRI D v => .Lopn [.reg D] "MOV:64" [.imm v]
  | .store m q S => .Lopn [.reg q] m [.reg S]
  | .load m D q => .Lopn [.reg D] m [.reg q]
  | .alu m D S => .Lopn [.reg D] m [.reg D, .reg S]
  | .aluI m D v => .Lopn [.reg D] m [.reg D, .imm v]
  | .shr m D S => .Lopn [.reg D] m [.reg S]
  | .shl0 m D S => .Lopn [.reg D] m [.reg S]
  | .shI m D k => .Lopn [.reg D] m [.reg D, .imm k]
  | .lea D B X sc => .Lopn [.reg D] "LEA:64" [.arrIdx B X sc]

/-- The arm of an instruction, read off its operand shape and mnemonic; `none` outside the
    covered shapes. -/
def classify : LinstrR → Option Arm
  | .Lopn [.reg d] m [.reg s] =>
      if isMovM m then
        if gpOk d && gpOk s then some (.movRR m d s)
        else if gpOk s then some (.store m d s)
        else some (.load m d s)
      else if m == withWidthTag 64 ("SHL" ++ ":" ++ toString 0) then some (.shl0 m d s)
      else some (.shr m d s)
  | .Lopn [.reg d] m [.imm v] => if m == "MOV:64" then some (.movRI d v) else none
  | .Lopn [.reg d] m [.reg a, .reg s] => if d == a then some (.alu m d s) else none
  | .Lopn [.reg d] m [.reg a, .imm v] =>
      if d == a then (if isShI m then some (.shI m d v) else some (.aluI m d v)) else none
  | .Lopn [.reg d] m [.arrIdx b x sc] => if m == "LEA:64" then some (.lea d b x sc) else none
  | _ => none

theorem classify_instr {i : LinstrR} {a : Arm} (h : classify i = some a) : a.instr = i := by
  unfold classify at h
  split at h
  · split_ifs at h <;> (obtain rfl := Option.some.inj h; rfl)
  · split_ifs at h with hm
    obtain rfl := Option.some.inj h
    simp only [beq_iff_eq] at hm
    subst hm
    rfl
  · split_ifs at h with hm
    obtain rfl := Option.some.inj h
    simp only [beq_iff_eq] at hm
    subst hm
    rfl
  · split_ifs at h with hm <;> obtain rfl := Option.some.inj h <;>
      simp only [beq_iff_eq] at hm <;> subst hm <;> rfl
  · split_ifs at h with hm
    obtain rfl := Option.some.inj h
    simp only [beq_iff_eq] at hm
    subst hm
    rfl
  · exact absurd h (by simp)

/-- The frame offset of the frame-word name `q` under the body parameters `P`. -/
def slotOff (P : Params) (q : String) : Int :=
  (spillQsaveOff P.frame P.spillW q P.qsaveB).getD 0

/-- The shift count of a count-in-mnemonic shift. -/
def shrK (m : String) : Nat := tagShiftCount (stripWidthTag m)

/-- Two frame offsets whose eight-byte words are disjoint. -/
def sepB (o o' : Int) : Bool :=
  decide (8 ≤ (o - o').natAbs) && decide ((o - o').natAbs ≤ 2 ^ 64 - 8)

/-- The byte pieces of an arm: the bytes and the decoded instruction of each machine
    instruction the encoder lays down for it. -/
def Arm.pieces (P : Params) : Arm → List (List (BitVec 8) × JInstr 64)
  | .movRR _ D S => [(encAluRRw 1 0x89 (gpNumU D) (gpNumU S), .mov (phys D) (.reg (phys S)))]
  | .movRI D v => [(encMovImmw 1 (gpNumU D) v, .mov (phys D) (.imm v))]
  | .store _ q S =>
      [(encRspMem 1 0x89 (gpNumU S) (slotOff P q), .storeMem "%rsp" (slotOff P q) (.reg (phys S)))]
  | .load _ D q =>
      [(encRspMem 1 0x8b (gpNumU D) (slotOff P q), .loadMem (phys D) "%rsp" (slotOff P q))]
  | .alu m D S =>
      match aluArm m with
      | some (op, mk) => [(encAluRRw 1 op (gpNumU D) (gpNumU S), mk (phys D) (.reg (phys S)))]
      | none => []
  | .aluI m D v =>
      match aluArm m with
      | some (_, mk) =>
          [(if fitsImm8S 1 v then encAluImm8 1 ((aluImmDigit (stripWidthTag m)).getD 0) (gpNumU D) v
            else encAluImmw 1 ((aluImmDigit (stripWidthTag m)).getD 0) (gpNumU D) v,
            mk (phys D) (.imm v))]
      | none => []
  | .shr m D S =>
      (if D = S then [] else
        [(encAluRRw 1 0x89 (gpNumU D) (gpNumU S), .mov (phys D) (.reg (phys S)))])
        ++ [(encTagShift 1 (tagShExt m) (gpNumU D) (stripWidthTag m),
              tagShMk m (phys D) (.imm (shrK m)))]
  | .shl0 _ D S =>
      if D = S then [] else
        [(encAluRRw 1 0x89 (gpNumU D) (gpNumU S), .mov (phys D) (.reg (phys S)))]
  | .shI m D k => [(shIBytes m (gpNumU D) k, shIMk m (phys D) (.imm k))]
  | .lea D B X sc =>
      [(encMemMovSibw 1 0x8d (gpNumU D) (gpNumU B) (gpNumU X) sc,
        .lea (phys D) (phys B) (phys X) sc 0)]

/-- The machine instructions of an arm. -/
def Arm.js (P : Params) (a : Arm) : List (JInstr 64) := (a.pieces P).map Prod.snd

/-- **The conditions of an arm** under the body parameters `P`, with the frame words `Q`
    written before it: general-purpose operands; an immediate in the sign-extended `imm32`
    range; a frame word with an offset in `rel32` range, not a general-purpose name, whose
    word is disjoint from every other written frame word (store) or written before (load);
    an arithmetic or logic mnemonic of `aluArm`; a shift by a count `0 < k < 64` spelled
    `SHR:k:64` or `SHL:k:64`; an immediate-count shift `SHR:64` by `0 < k < 64` or `SHL:64`
    by `k < 64`, the count `0` being a copy. -/
def Arm.ok (P : Params) (Q : List (String × Int)) : Arm → Bool
  | .movRR m D S => isMovM m && gpOk D && gpOk S
  | .movRI D v => gpOk D && decide (v < 2 ^ 64) && ScalarEncoder.fitsImm32S v
  | .store m q S =>
      isMovM m && gpOk S && !gpOk q
        && (spillQsaveOff P.frame P.spillW q P.qsaveB).isSome && dispOk32 (slotOff P q)
        && Q.all (fun p => p.1 == q || sepB p.2 (slotOff P q))
  | .load m D q =>
      isMovM m && gpOk D && (spillQsaveOff P.frame P.spillW q P.qsaveB).isSome
        && dispOk32 (slotOff P q) && Q.any (fun p => p.1 == q && p.2 == slotOff P q)
  | .alu m D S => (aluArm m).isSome && gpOk D && gpOk S
  | .aluI m D v =>
      (aluArm m).isSome && gpOk D
        && (fitsImm8S 1 v || (decide (v < 2 ^ 64) && ScalarEncoder.fitsImm32S v))
  | .shr m D S =>
      gpOk D && gpOk S && !(isCarryOutBinding m || isMulHiBinding m)
        && !(stripWidthTag m == "MULX") && !(stripWidthTag m == "MULXMEM")
        && (adxPrefix (stripWidthTag m)).isNone
        && tagShiftExt (stripWidthTag m) == some (tagShExt m)
        && LprogBytes.rexW (mnemWidth m) == 1 && decide (0 < shrK m) && decide (shrK m < 64)
        && m == withWidthTag 64 (tagShName m ++ ":" ++ toString (shrK m))
  | .shl0 m D S =>
      gpOk D && gpOk S && !(isCarryOutBinding m || isMulHiBinding m)
        && !(stripWidthTag m == "MULX") && !(stripWidthTag m == "MULXMEM")
        && (adxPrefix (stripWidthTag m)).isNone && tagShiftExt (stripWidthTag m) == some 4
        && LprogBytes.rexW (mnemWidth m) == 1 && tagShiftCount (stripWidthTag m) == 0
        && m == withWidthTag 64 ("SHL" ++ ":" ++ toString 0)
  | .shI m D k => isShI m && gpOk D && (decide (0 < k) || m == "SHL:64") && decide (k < 64)
  | .lea D B X sc => gpOk D && gpOk B && gpOk X && gpNumU X != 4 && ScalarEncoder.scaleOk sc

/-- The frame words written after an arm. -/
def Arm.post (P : Params) (Q : List (String × Int)) : Arm → List (String × Int)
  | .store _ q _ => (q, slotOff P q) :: Q.filter (fun p => p.1 != q)
  | _ => Q

/-- **The bytes of an arm.** For an arm whose conditions hold, the encoder lays down the
    concatenation of its pieces, and each piece decodes in front of every continuation. -/
theorem Arm.bytes (P : Params) (Q : List (String × Int)) (a : Arm) (h : a.ok P Q = true) :
    encodeLopn P.frame P.spillW a.instr P.qsaveB = (a.pieces P).flatMap Prod.fst
      ∧ ∀ q ∈ a.pieces P, PieceDec q := by
  cases a with
  | movRR m D S =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨hm, hD⟩, hS⟩ := h
    refine ⟨?_, ?_⟩
    · simp [Arm.instr, Arm.pieces, encodeLopn_movM _ _ _ _ _ _ hm,
        encTwoAddr_rr _ _ _ 0x89 _ _ _ hD hS (by decide)]
    · simpa [Arm.pieces] using pieceDec_movRR D S
  | movRI D v =>
    simp only [Arm.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hD, hv⟩, hf⟩ := h
    refine ⟨?_, ?_⟩
    · simp [Arm.instr, Arm.pieces, encodeLopn_movImm _ _ _ _ _ hD hf]
    · simp only [Arm.pieces, List.mem_singleton]
      rintro q rfl rest
      exact decodeLinstr_movImm _ _ rest (gpNumU_lt_16 D) hv hf
  | store m q S =>
    simp only [Arm.ok, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨hm, hS⟩, -⟩, hsome⟩, hd⟩, -⟩ := h
    obtain ⟨off, hoff⟩ := Option.isSome_iff_exists.mp hsome
    have hso : slotOff P q = off := by simp [slotOff, hoff]
    refine ⟨?_, ?_⟩
    · simp [Arm.instr, Arm.pieces, encodeLopn_movM _ _ _ _ _ _ hm,
        encTwoAddr_store _ _ _ 0x89 _ _ _ _ hoff hS (by decide), hso, memDstOp]
    · simp only [Arm.pieces, List.mem_singleton]
      rintro p rfl rest
      exact decodeLinstr_rspStore _ _ rest (gpNumU_lt_16 S) hd
  | load m D q =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hm, hD⟩, hsome⟩, hd⟩, -⟩ := h
    obtain ⟨off, hoff⟩ := Option.isSome_iff_exists.mp hsome
    have hso : slotOff P q = off := by simp [slotOff, hoff]
    refine ⟨?_, ?_⟩
    · simp [Arm.instr, Arm.pieces, encodeLopn_movM _ _ _ _ _ _ hm,
        encTwoAddr_load _ _ _ 0x89 _ _ _ _ hoff hD (by decide), hso, memSrcOp]
    · simp only [Arm.pieces, List.mem_singleton]
      rintro p rfl rest
      exact decodeLinstr_rspLoad _ _ rest (gpNumU_lt_16 D) hd
  | alu m D S =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨hm, hD⟩, hS⟩ := h
    obtain ⟨⟨op, mk⟩, hop⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨he, htab, hmk⟩ := encodeLopn_alu P.frame P.spillW m D D S P.qsaveB hop
    refine ⟨?_, ?_⟩
    · have h8b : op ≠ 0x8b := by
        simp only [aluTableOp, decide_eq_true_eq] at htab
        exact htab.2.2.2.1
      simp [Arm.instr, Arm.pieces, hop, he, encTwoAddr_rr _ _ _ op _ _ _ hD hS h8b]
    · simp only [Arm.pieces, hop, List.mem_singleton]
      rintro p rfl rest
      exact decodeLinstr_aluRR op mk _ _ rest (gpNumU_lt_16 D) (gpNumU_lt_16 S) htab hmk
  | aluI m D v =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨hm, hD⟩, hv⟩ := h
    obtain ⟨⟨op, mk⟩, hop⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨dig, f, henc, hdig, hmk, hdg, -, -, -⟩ := aluArm_imm hop
    by_cases h8 : fitsImm8S 1 v = true
    · refine ⟨?_, ?_⟩
      · simp [Arm.instr, Arm.pieces, hop, hdg, h8, henc P.frame P.spillW D v P.qsaveB hD h8]
      · simp only [Arm.pieces, hop, hdg, h8, ite_true, Option.getD_some, List.mem_singleton]
        rintro p rfl rest
        exact decodeLinstr_aluImm8 dig mk _ _ rest hdig (gpNumU_lt_16 D) h8 hmk
    · have h8f : fitsImm8S 1 v = false := Bool.eq_false_iff.mpr h8
      simp only [h8f, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨hlt, h32⟩ := hv
      obtain ⟨dig', hdg', hdig', hmk', henc'⟩ := aluArm_imm32 hop
      rw [hdg] at hdg'
      obtain rfl := Option.some.inj hdg'
      refine ⟨?_, ?_⟩
      · simp [Arm.instr, Arm.pieces, hop, hdg, h8f, henc' P.frame P.spillW D v P.qsaveB hD h8f h32]
      · simp only [Arm.pieces, hop, hdg, h8f, Bool.false_eq_true, ite_false, Option.getD_some,
          List.mem_singleton]
        rintro p rfl rest
        exact decodeLinstr_aluImm32 dig mk _ _ rest hdig (gpNumU_lt_16 D) hlt h32 hmk'
  | shI m D k =>
    simp only [Arm.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hm, hD⟩, -⟩, hk⟩ := h
    refine ⟨?_, ?_⟩
    · simp [Arm.instr, Arm.pieces, encodeLopn_shI P.frame P.spillW m D k P.qsaveB hm hD]
    · simp only [Arm.pieces, List.mem_singleton]
      rintro p rfl
      exact pieceDec_shI m D k hm hk
  | lea D B X sc =>
    simp only [Arm.ok, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨⟨⟨hD, hB⟩, hX⟩, h4⟩, hs⟩ := h
    refine ⟨?_, ?_⟩
    · simp [Arm.instr, Arm.pieces, encodeLopn_leaIdx _ _ _ _ _ _ _ hD hB hX h4 hs]
    · simp only [Arm.pieces, List.mem_singleton]
      rintro p rfl rest
      exact decodeLinstr_leaIdx _ _ _ sc rest (gpNumU_lt_16 D) (gpNumU_lt_16 B)
        (gpNumU_lt_16 X) h4 hs
  | shl0 m D S =>
    simp only [Arm.ok, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
      Option.isNone_iff_eq_none, Bool.or_eq_false_iff] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hS⟩, hbind⟩, hmulx⟩, hmulxmem⟩, hadx⟩, hext⟩, hw⟩, hn⟩, -⟩ := h
    refine ⟨?_, ?_⟩
    · rw [Arm.instr, encodeLopn_shift0 P.frame P.spillW m D S P.qsaveB 4
        (by simp [hbind]) (by simp [hmulx]) (by simp [hmulxmem]) hadx hext hD hS hn, hw]
      by_cases hDS : D = S <;> simp [Arm.pieces, hDS]
    · intro p hp
      simp only [Arm.pieces] at hp
      split at hp
      · simp at hp
      · simp only [List.mem_singleton] at hp
        subst hp
        exact pieceDec_movRR D S
  | shr m D S =>
    simp only [Arm.ok, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, Option.isNone_iff_eq_none,
      decide_eq_true_eq, Bool.or_eq_false_iff] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hS⟩, hbind⟩, hmulx⟩, hmulxmem⟩, hadx⟩, hext⟩, hw⟩, hk0⟩, hk⟩, -⟩ :=
      h
    refine ⟨?_, ?_⟩
    · rw [Arm.instr, encodeLopn_shift P.frame P.spillW m D S P.qsaveB (tagShExt m)
        (by simp [hbind]) (by simp [hmulx]) (by simp [hmulxmem]) hadx hext hD hS
        (by unfold shrK at hk0; omega), hw]
      by_cases hDS : D = S <;> simp [Arm.pieces, hDS]
    · intro p hp
      simp only [Arm.pieces, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · split at hp
        · simp at hp
        · simp only [List.mem_singleton] at hp
          subst hp
          exact pieceDec_movRR D S
      · exact pieceDec_tagShift m D (shrK m) hD (by omega) hk _ rfl

/-! ## 6. The correspondence of a printed body -/

/-- **The identity correspondence of a printed body.** Each general-purpose name reads at
    width `64` the value of its machine register; the stack register holds `rsp`; each
    written frame word `(q, off)` of `Q` reads at width `64` the word at `rsp + off`; and no
    frame-word name is a general-purpose name. -/
structure PCorr (Q : List (String × Int)) (rsp : BitVec 64) (sa : AState) (b : LstateM)
    (_zf : Bool) : Prop where
  /-- A general-purpose name holds the value of its machine register. -/
  regs : ∀ r, gpOk r = true → b.reg.getW r 64 = some (sa.regs (phys r))
  /-- The stack register holds `rsp`. -/
  sp : sa.regs "%rsp" = rsp
  /-- A written frame word holds the word at its frame address. -/
  slots : ∀ p ∈ Q, b.reg.getW p.1 64 = some (read64 sa.mem (rsp + BitVec.ofInt 64 p.2))
  /-- No frame-word name is a general-purpose name. -/
  names : ∀ p ∈ Q, gpOk p.1 = false

theorem getW_setReg_nextPc (b : LstateM) (D r : String) (v : BitVec 64) :
    ((b.setReg D v).nextPc).reg.getW r 64 = if r = D then some v else b.reg.getW r 64 := by
  rw [LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc]
  split
  · rename_i h; subst h; exact LstateN.getW_setReg_same _ _ _
  · rename_i h; exact LstateN.getW_setReg_other _ _ _ _ _ h

/-- A write of `v` to the general-purpose name `D` on the flag machine and to its machine
    register, memory unchanged, preserves the correspondence. -/
theorem PCorr.write {Q : List (String × Int)} {rsp : BitVec 64} {sa sa' : AState}
    {b b' : LstateM} {zf zf' : Bool} (h : PCorr Q rsp sa b zf) {D : String}
    (hD : gpOk D = true) (v : BitVec 64)
    (hregs : ∀ r, sa'.regs r = if r = phys D then v else sa.regs r) (hmem : sa'.mem = sa.mem)
    (hb : ∀ r, r ≠ D → b'.reg.getW r 64 = b.reg.getW r 64)
    (hbD : b'.reg.getW D 64 = some v) : PCorr Q rsp sa' b' zf' where
  regs r hr := by
    by_cases hrD : r = D
    · subst hrD; rw [hbD, hregs, ite_eq_left rfl]
    · rw [hb r hrD, h.regs r hr, hregs, ite_eq_right (fun e => hrD (phys_inj hr hD e))]
  sp := by rw [hregs, ite_eq_right (fun e => (gpFacts hD).physNe e.symm)]; exact h.sp
  slots p hp := by
    have hne : p.1 ≠ D := fun e => by have := h.names p hp; rw [e, hD] at this; cases this
    rw [hb _ hne, hmem]; exact h.slots p hp
  names := h.names

/-- The flag-machine step of a register move between names. -/
theorem fstepF_movM (m d s : String) (hm : isMovM m = true) (b : LstateM) (zf : Bool)
    (v : BitVec 64) (hv : b.reg.getW s 64 = some v) :
    fstepF (.Lopn [.reg d] m [.reg s], .reg none) b zf = some ((b.setReg d v).nextPc, zf) := by
  simp only [isMovM, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with rfl | rfl
  · exact fstepF_movRI d s b zf v hv
  · simp [fstepF, cmpArgs?, movRegArgs?, readReg_of_getW hv,
      show stripWidthTag "MOVQ" = "MOVQ" from by decide +kernel]

/-- The flag-machine step of the load-effective-address `LEA:64 d, [b + x · sc]`: the
    address `b + sc · x` written to `d`, the zero flag unchanged. -/
theorem fstepF_lea (d b x : String) (sc : Nat) (s : LstateM) (zf : Bool) {p vi : BitVec 64}
    (hb : s.reg.getW b 64 = some p) (hx : s.reg.getW x 64 = some vi) :
    fstepF (.Lopn [.reg d] "LEA:64" [.arrIdx b x sc], .reg none) s zf
      = some ((s.setReg d (p + BitVec.ofNat 64 (sc * vi.toNat))).nextPc, zf) := by
  have hl : lsemStepMem (.Lopn [.reg d] "LEA:64" [.arrIdx b x sc], .reg none) s
      = some ((s.setReg d (p + BitVec.ofNat 64 (sc * vi.toNat))).nextPc) := by
    rw [lsemStepMem_reg, JasminLsemCast.lsemStepCast_of_delegate _ _ (Or.inr rfl),
      JasminLsemMulCarry.lsemStepMC_of_delegate _ _ rfl rfl rfl rfl rfl,
      JasminLsemShift.lsemStepSh_of_not_sar _ _
        (by simp (config := { decide := true }) [JasminLsemShift.sarStruct?])]
    simp only [lsemStepN, show stripWidthTag "LEA:64" = "LEA" from by decide +kernel, ite_true,
      hb, hx, Option.map_some]
    rfl
  simp [fstepF, cmpArgs?, movRegArgs?, stepMemF_of_lsemStepMem hl, withALUFlags, aluFlagOp?]

/-- The flag-machine and machine semantics of an arithmetic or logic mnemonic of
    `aluArm`. -/
theorem aluArm_sem {m : String} {op : Nat} {mk : String → JOperand → JInstr 64}
    (h : aluArm m = some (op, mk)) :
    ∃ (base : String) (f : BitVec 64 → BitVec 64 → BitVec 64), stripWidthTag m = base
      ∧ m ≠ withWidthTag 64 "CMP" ∧ base ≠ "MULXHI"
      ∧ (base ≠ "ADC" ∧ base ≠ "SBB" ∧ base ≠ "ADCX" ∧ base ≠ "ADOX")
      ∧ (∀ x y, applyOpnN 64 base [x, y] = some (f x y))
      ∧ (∀ (sa : AState) (D S r : String), (evalInstrA sa (mk D (.reg S))).regs r
          = if r = D then f (sa.regs D) (sa.regs S) else sa.regs r)
      ∧ (∀ (sa : AState) (D S : String), (evalInstrA sa (mk D (.reg S))).mem = sa.mem) := by
  unfold aluArm at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h
  · exact ⟨"ADD", (· + ·), by decide +kernel, by decide +kernel, by decide, by decide,
      fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  · exact ⟨"SUB", (· - ·), by decide +kernel, by decide +kernel, by decide, by decide,
      fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  · exact ⟨"AND", (· &&& ·), by decide +kernel, by decide +kernel, by decide, by decide,
      fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  · exact ⟨"OR", (· ||| ·), by decide +kernel, by decide +kernel, by decide, by decide,
      fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  · exact ⟨"XOR", (· ^^^ ·), by decide +kernel, by decide +kernel, by decide, by decide,
      fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem evalInstrA_storeMem_eq (sa : AState) (B X : String) (off : Int) :
    (evalInstrA sa (.storeMem B off (.reg X))).regs = sa.regs
      ∧ (evalInstrA sa (.storeMem B off (.reg X))).mem
        = write64 sa.mem (sa.regs B + BitVec.ofInt 64 off) (sa.regs X) := by
  refine ⟨?_, ?_⟩ <;>
    simp [evalInstrA, evalInstr, JState.store, AState.view, writeAddr, writeVal, JOperand.eval]

theorem evalInstrA_loadMem_eq (sa : AState) (S B : String) (off : Int) :
    (∀ r, (evalInstrA sa (.loadMem S B off)).regs r
      = if r = S then read64 sa.mem (sa.regs B + BitVec.ofInt 64 off) else sa.regs r)
      ∧ (evalInstrA sa (.loadMem S B off)).mem = sa.mem := by
  refine ⟨fun r => ?_, ?_⟩
  · by_cases hr : r = S <;> simp [evalInstrA, evalInstr, JState.setReg, AState.view, hr, x86_MOV]
  · simp [evalInstrA, evalInstr, JState.setReg, AState.view, writeAddr]

theorem evalInstrA_lea_eq (sa : AState) (D B X : String) (sc : Nat) :
    (∀ r, (evalInstrA sa (.lea D B X sc 0)).regs r
      = if r = D then sa.regs B + BitVec.ofNat 64 (sc * (sa.regs X).toNat) else sa.regs r)
      ∧ (evalInstrA sa (.lea D B X sc 0)).mem = sa.mem := by
  have hm : ∀ v : BitVec 64, v * BitVec.ofNat 64 sc = BitVec.ofNat 64 (sc * v.toNat) := by
    intro v
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, Nat.mul_mod, Nat.mul_comm]
  refine ⟨fun r => ?_, ?_⟩
  · by_cases hr : r = D <;>
      simp [evalInstrA, evalInstr, JState.setReg, JState.get, AState.view, hr, x86_LEA, hm]
  · simp [evalInstrA, evalInstr, JState.setReg, AState.view, writeAddr]

/-! ## 7. The simulation of one arm -/

/-- **One arm.** From the correspondence with the written frame words `Q`, the flag-machine
    step of an arm whose conditions hold succeeds, and its result corresponds, with the frame
    words `a.post P Q`, to the machine run of the decoded instructions of the arm. -/
theorem Arm.sim (P : Params) (Q : List (String × Int)) (rsp : BitVec 64) (a : Arm)
    (h : a.ok P Q = true) :
    DecSim (PCorr Q rsp) (PCorr (a.post P Q) rsp) [(a.instr, .reg none)] (a.js P) := by
  cases a with
  | movRR m D S =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨hm, hD⟩, hS⟩ := h
    show DecSim _ _ [_] [.mov (phys D) (.reg (phys S))]
    exact DecSim.single fun sa b zf hc =>
      ⟨_, zf, fstepF_movM m D S hm b zf _ (hc.regs S hS),
        hc.write hD (sa.regs (phys S)) (fun _ => rfl) rfl
          (fun r hr => by rw [getW_setReg_nextPc, ite_eq_right hr])
          (by rw [getW_setReg_nextPc, ite_eq_left rfl])⟩
  | movRI D v =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨hD, -⟩, -⟩ := h
    show DecSim _ _ [_] [.mov (phys D) (.imm v)]
    exact DecSim.single fun sa b zf hc =>
      ⟨_, zf, fstepF_movII D v b zf,
        hc.write hD (BitVec.ofNat 64 v) (fun _ => rfl) rfl
          (fun r hr => by rw [getW_setReg_nextPc, ite_eq_right hr])
          (by rw [getW_setReg_nextPc, ite_eq_left rfl])⟩
  | store m q S =>
    simp only [Arm.ok, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
      Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨hm, hS⟩, hq⟩, -⟩, -⟩, hsep⟩ := h
    show DecSim _ _ [_] [.storeMem "%rsp" (slotOff P q) (.reg (phys S))]
    refine DecSim.single fun sa b zf hc =>
      ⟨_, zf, fstepF_movM m q S hm b zf _ (hc.regs S hS), ?_⟩
    obtain ⟨hregs, hmem⟩ := evalInstrA_storeMem_eq sa "%rsp" (phys S) (slotOff P q)
    rw [hc.sp] at hmem
    refine ⟨fun r hr => ?_, by rw [hregs]; exact hc.sp, fun p hp => ?_, fun p hp => ?_⟩
    · have hrq : r ≠ q := fun e => by rw [e, hq] at hr; cases hr
      rw [getW_setReg_nextPc, ite_eq_right hrq, hregs]
      exact hc.regs r hr
    · simp only [Arm.post, List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq] at hp
      rcases hp with rfl | ⟨hpQ, hpq⟩
      · rw [getW_setReg_nextPc, ite_eq_left rfl, hmem, read64_write64_same]
      · rw [getW_setReg_nextPc, ite_eq_right hpq, hmem, hc.slots p hpQ,
          read64_write64_of_disjoint]
        rcases hsep p hpQ with he | hs
        · exact absurd he hpq
        · simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at hs
          exact (disjoint8_add_ofInt rsp p.2 (slotOff P q) hs.1 hs.2).symm
    · simp only [Arm.post, List.mem_cons, List.mem_filter] at hp
      rcases hp with rfl | ⟨hpQ, -⟩
      · exact hq
      · exact hc.names p hpQ
  | load m D q =>
    simp only [Arm.ok, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hm, hD⟩, -⟩, -⟩, ⟨p, hpQ, hp1, hp2⟩⟩ := h
    show DecSim _ _ [_] [.loadMem (phys D) "%rsp" (slotOff P q)]
    have hv := fun (sa : AState) (b : LstateM) (zf : Bool) (hc : PCorr Q rsp sa b zf) => by
      have := hc.slots p hpQ
      rw [hp1, hp2] at this
      exact this
    refine DecSim.single fun sa b zf hc =>
      ⟨_, zf, fstepF_movM m D q hm b zf _ (hv sa b zf hc), ?_⟩
    obtain ⟨hregs, hmem⟩ := evalInstrA_loadMem_eq sa (phys D) "%rsp" (slotOff P q)
    exact hc.write hD _ (fun r => by rw [hregs, hc.sp]) hmem
      (fun r hr => by rw [getW_setReg_nextPc, ite_eq_right hr])
      (by rw [getW_setReg_nextPc, ite_eq_left rfl])
  | alu m D S =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨hm, hD⟩, hS⟩ := h
    obtain ⟨⟨op, mk⟩, hop⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨base, f, hstrip, hcmp, hmul, hcarry, hf, hmk, hmkm⟩ := aluArm_sem hop
    have hjs : Arm.js P (.alu m D S) = [mk (phys D) (.reg (phys S))] := by
      simp [Arm.js, Arm.pieces, hop]
    rw [hjs]
    show DecSim _ _ [binRegI m D D S] _
    refine DecSim.single fun sa b zf hc =>
      ⟨withALUFlags (binRegI m D D S) b
        ((b.setReg D (f (sa.regs (phys D)) (sa.regs (phys S)))).nextPc),
      zf, ?_, hc.write hD (f (sa.regs (phys D)) (sa.regs (phys S))) (hmk sa _ _) (hmkm sa _ _)
        (fun r hr => by rw [withALUFlags_reg, getW_setReg_nextPc, ite_eq_right hr])
        (by rw [withALUFlags_reg, getW_setReg_nextPc, ite_eq_left rfl])⟩
    rw [fstepF_binRegI m base D D S hstrip hcmp hmul hcarry (ne_mov_of_applyOpnN hf) b zf _
      (hc.regs D hD) (cmpOfName?_of_applyOpnN (hf 0 0)), hc.regs S hS, Option.bind_some, hf,
      Option.map_some]
  | aluI m D v =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨hm, hD⟩, -⟩ := h
    obtain ⟨⟨op, mk⟩, hop⟩ := Option.isSome_iff_exists.mp hm
    obtain ⟨dig, f, -, -, -, -, hstep, hmk, hmkm⟩ := aluArm_imm hop
    obtain ⟨-, -, -, hcmp, -, -, -, -, -⟩ := aluArm_sem hop
    have hjs : Arm.js P (.aluI m D v) = [mk (phys D) (.imm v)] := by
      simp [Arm.js, Arm.pieces, hop]
    rw [hjs]
    refine DecSim.single fun sa b zf hc =>
      ⟨withALUFlags ((Arm.aluI m D v).instr, .reg none) b
        ((b.setReg D (f (sa.regs (phys D)) (BitVec.ofNat 64 v))).nextPc), zf, ?_,
      hc.write hD _ (fun r => hmk sa (phys D) r v) (hmkm sa _ _)
        (fun r hr => by rw [withALUFlags_reg, getW_setReg_nextPc, ite_eq_right hr])
        (by rw [withALUFlags_reg, getW_setReg_nextPc, ite_eq_left rfl])⟩
    have hl := hstep b D _ v (hc.regs D hD)
    simp [fstepF, cmpArgs?, movRegArgs?, Arm.instr, hcmp, stepMemF_of_lsemStepMem hl]
  | shI m D k =>
    simp only [Arm.ok, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hm, hD⟩, hk0⟩, hk⟩ := h
    have hjs : Arm.js P (.shI m D k) = [shIMk m (phys D) (.imm k)] := by
      simp [Arm.js, Arm.pieces]
    rw [hjs]
    simp only [isShI, Bool.or_eq_true, beq_iff_eq] at hm
    rcases hm with rfl | rfl
    · have hi : ((Arm.shI "SHL:64" D k).instr, MemTag.reg none)
          = DecodeGenSim.shiftImmS "SHL" D D k := by
        simp [Arm.instr, DecodeGenSim.shiftImmS, withWidthTag]
      rw [hi]
      have hw : ∀ v : BitVec 64, (x86_SHL v (BitVec.ofNat 64 k)).word = v <<< k := by
        intro v
        rcases Nat.eq_zero_or_pos k with rfl | hkp
        · simp [x86_SHL, shiftCount, rflags_None]
        · exact DecodeGenSim.x86_SHL_word_imm v k (by omega) hk
      exact DecSim.single fun sa b zf hc =>
        ⟨_, zf, (DecodeGenSim.fstepF_shiftImmS (Or.inr rfl) D D k b zf).trans
          (DecodeGenSim.fstepF_shlImmI D D k hk b zf _ (hc.regs D hD)),
          hc.write hD _ (fun r => by
              show (if r = phys D then (x86_SHL (sa.regs (phys D)) (BitVec.ofNat 64 k)).word
                else sa.regs r) = _
              rw [hw]) rfl
            (fun r hr => by rw [getW_setReg_nextPc, ite_eq_right hr])
            (by rw [getW_setReg_nextPc, ite_eq_left rfl])⟩
    · have hi : ((Arm.shI "SHR:64" D k).instr, MemTag.reg none)
          = DecodeGenSim.shiftImmS "SHR" D D k := by
        simp [Arm.instr, DecodeGenSim.shiftImmS, withWidthTag]
      rw [hi]
      have hk0 : 0 < k := by simpa using hk0
      exact DecSim.single fun sa b zf hc =>
        ⟨_, zf, (DecodeGenSim.fstepF_shiftImmS (Or.inl rfl) D D k b zf).trans
          (fstepF_shrImmI D D k hk b zf _ (hc.regs D hD)),
          hc.write hD _ (fun r => by
              show (if r = phys D then (x86_SHR (sa.regs (phys D)) (BitVec.ofNat 64 k)).word
                else sa.regs r) = _
              rw [x86_SHR_word_imm _ k (by omega) hk]) rfl
            (fun r hr => by rw [getW_setReg_nextPc, ite_eq_right hr])
            (by rw [getW_setReg_nextPc, ite_eq_left rfl])⟩
  | lea D B X sc =>
    simp only [Arm.ok, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hD, hB⟩, hX⟩, -⟩, -⟩ := h
    show DecSim _ _ [_] [.lea (phys D) (phys B) (phys X) sc 0]
    refine DecSim.single fun sa b zf hc =>
      ⟨_, zf, fstepF_lea D B X sc b zf (hc.regs B hB) (hc.regs X hX), ?_⟩
    obtain ⟨hregs, hmem⟩ := evalInstrA_lea_eq sa (phys D) (phys B) (phys X) sc
    exact hc.write hD _ hregs hmem
      (fun r hr => by rw [getW_setReg_nextPc, ite_eq_right hr])
      (by rw [getW_setReg_nextPc, ite_eq_left rfl])
  | shl0 m D S =>
    simp only [Arm.ok, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hS⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hm⟩ := h
    have hi : ((Arm.shl0 m D S).instr, MemTag.reg none) = immShiftI "SHL" D S 0 := by
      rw [Arm.instr, immShiftI, ← hm]
    rw [hi]
    by_cases hDS : D = S
    · subst hDS
      have hjs : Arm.js P (.shl0 m D D) = [] := by simp [Arm.js, Arm.pieces]
      rw [hjs]
      exact DecSim.lsemOnly fun sa b zf hc =>
        ⟨_, zf, fstepF_shl0I D D b zf _ (hc.regs D hD),
          hc.write hD (sa.regs (phys D)) (fun r => by split <;> simp_all) rfl
            (fun r hr => by rw [getW_setReg_nextPc, ite_eq_right hr])
            (by rw [getW_setReg_nextPc, ite_eq_left rfl])⟩
    · have hjs : Arm.js P (.shl0 m D S) = [.mov (phys D) (.reg (phys S))] := by
        simp [Arm.js, Arm.pieces, hDS]
      rw [hjs]
      exact DecSim.single fun sa b zf hc =>
        ⟨_, zf, fstepF_shl0I D S b zf _ (hc.regs S hS),
          hc.write hD (sa.regs (phys S)) (fun _ => rfl) rfl
            (fun r hr => by rw [getW_setReg_nextPc, ite_eq_right hr])
            (by rw [getW_setReg_nextPc, ite_eq_left rfl])⟩
  | shr m D S =>
    simp only [Arm.ok, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hD, hS⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hk0⟩, hk⟩, hm⟩ :=
      h
    have hjs : Arm.js P (.shr m D S) = (if D = S then [] else [.mov (phys D) (.reg (phys S))])
        ++ [tagShMk m (phys D) (.imm (shrK m))] := by
      by_cases hDS : D = S <;> simp [Arm.js, Arm.pieces, hDS]
    rw [hjs]
    by_cases hs : tagShl m = true
    · simp only [tagShName, tagShMk, hs, ite_true] at hm ⊢
      generalize shrK m = k at hk0 hk hm ⊢
      have hi : ((Arm.shr m D S).instr, MemTag.reg none) = immShiftI "SHL" D S k := by
        rw [Arm.instr, immShiftI, ← hm]
      rw [hi]
      intro sa b zf hc
      have hst := DecodeGenSim.fstepF_shlImmI D S k hk b zf _ (hc.regs S hS)
      refine ⟨_, zf, (by rw [runStraightF_singleton]; exact hst), ?_⟩
      have hw : ∀ v : BitVec 64, (x86_SHL v (BitVec.ofNat 64 k)).word = v <<< k :=
        fun v => DecodeGenSim.x86_SHL_word_imm v k (by omega) hk
      by_cases hDS : D = S
      · subst hDS
        rw [ite_eq_left rfl, List.nil_append]
        show PCorr Q rsp (evalInstrA sa (.shl (phys D) (.imm k))) _ zf
        exact hc.write hD _ (fun r => by
            show (if r = phys D then (x86_SHL (sa.regs (phys D)) (BitVec.ofNat 64 k)).word
              else sa.regs r) = _
            rw [hw]) rfl
          (fun r hr => by rw [getW_setReg_nextPc, ite_eq_right hr])
          (by rw [getW_setReg_nextPc, ite_eq_left rfl])
      · rw [ite_eq_right hDS, List.singleton_append]
        show PCorr Q rsp (evalInstrA (evalInstrA sa (.mov (phys D) (.reg (phys S))))
          (.shl (phys D) (.imm k))) _ zf
        exact hc.write hD _ (fun r => by
            show (if r = phys D then (x86_SHL (if phys D = phys D then sa.regs (phys S)
              else sa.regs (phys D)) (BitVec.ofNat 64 k)).word
              else (if r = phys D then sa.regs (phys S) else sa.regs r)) = _
            rw [hw, ite_eq_left rfl]
            split <;> rfl) rfl
          (fun r hr => by rw [getW_setReg_nextPc, ite_eq_right hr])
          (by rw [getW_setReg_nextPc, ite_eq_left rfl])
    by_cases hr : tagRor m = true
    · simp only [tagShName, tagShMk, hs, hr, Bool.false_eq_true, ite_false, ite_true] at hm ⊢
      generalize shrK m = k at hk0 hk hm ⊢
      have hi : ((Arm.shr m D S).instr, MemTag.reg none) = immShiftI "ROR" D S k := by
        rw [Arm.instr, immShiftI, ← hm]
      rw [hi]
      intro sa b zf hc
      have hst := fstepF_rorImmI D S k b zf _ (hc.regs S hS)
      refine ⟨_, zf, (by rw [runStraightF_singleton]; exact hst), ?_⟩
      have hw : ∀ v : BitVec 64, (x86_ROR v (BitVec.ofNat 64 k)).word = v.rotateRight k :=
        fun v => x86_ROR_word_imm v k (by omega) hk
      by_cases hDS : D = S
      · subst hDS
        rw [ite_eq_left rfl, List.nil_append]
        show PCorr Q rsp (evalInstrA sa (.ror (phys D) (.imm k))) _ zf
        exact hc.write hD _ (fun r => by
            show (if r = phys D then (x86_ROR (sa.regs (phys D)) (BitVec.ofNat 64 k)).word
              else sa.regs r) = _
            rw [hw]) rfl
          (fun r hr => by rw [getW_setReg_nextPc, ite_eq_right hr])
          (by rw [getW_setReg_nextPc, ite_eq_left rfl])
      · rw [ite_eq_right hDS, List.singleton_append]
        show PCorr Q rsp (evalInstrA (evalInstrA sa (.mov (phys D) (.reg (phys S))))
          (.ror (phys D) (.imm k))) _ zf
        exact hc.write hD _ (fun r => by
            show (if r = phys D then (x86_ROR (if phys D = phys D then sa.regs (phys S)
              else sa.regs (phys D)) (BitVec.ofNat 64 k)).word
              else (if r = phys D then sa.regs (phys S) else sa.regs r)) = _
            rw [hw, ite_eq_left rfl]
            split <;> rfl) rfl
          (fun r hr => by rw [getW_setReg_nextPc, ite_eq_right hr])
          (by rw [getW_setReg_nextPc, ite_eq_left rfl])
    · simp only [tagShName, tagShMk, hs, hr, Bool.false_eq_true, ite_false] at hm ⊢
      generalize shrK m = k at hk0 hk hm ⊢
      have hi : ((Arm.shr m D S).instr, MemTag.reg none) = immShiftI "SHR" D S k := by
        rw [Arm.instr, immShiftI, ← hm]
      rw [hi]
      intro sa b zf hc
      have hst := fstepF_shrImmI D S k hk b zf _ (hc.regs S hS)
      refine ⟨_, zf, (by rw [runStraightF_singleton]; exact hst), ?_⟩
      have hw : ∀ v : BitVec 64, (x86_SHR v (BitVec.ofNat 64 k)).word = v >>> k :=
        fun v => x86_SHR_word_imm v k (by omega) hk
      by_cases hDS : D = S
      · subst hDS
        rw [ite_eq_left rfl, List.nil_append]
        show PCorr Q rsp (evalInstrA sa (.shr (phys D) (.imm k))) _ zf
        exact hc.write hD _ (fun r => by
            show (if r = phys D then (x86_SHR (sa.regs (phys D)) (BitVec.ofNat 64 k)).word
              else sa.regs r) = _
            rw [hw]) rfl
          (fun r hr => by rw [getW_setReg_nextPc, ite_eq_right hr])
          (by rw [getW_setReg_nextPc, ite_eq_left rfl])
      · rw [ite_eq_right hDS, List.singleton_append]
        show PCorr Q rsp (evalInstrA (evalInstrA sa (.mov (phys D) (.reg (phys S))))
          (.shr (phys D) (.imm k))) _ zf
        exact hc.write hD _ (fun r => by
            show (if r = phys D then (x86_SHR (if phys D = phys D then sa.regs (phys S)
              else sa.regs (phys D)) (BitVec.ofNat 64 k)).word
              else (if r = phys D then sa.regs (phys S) else sa.regs r)) = _
            rw [hw, ite_eq_left rfl]
            split <;> rfl) rfl
          (fun r hr => by rw [getW_setReg_nextPc, ite_eq_right hr])
          (by rw [getW_setReg_nextPc, ite_eq_left rfl])

/-! ## 8. A straight-line segment -/

/-- The flag-machine instructions of a printed body, at the register tag. -/
def printedOps (body : Lcmd) : List LinstrRM := body.map fun l => (l.li_i, .reg none)

/-- **The check of a straight-line segment** from the written frame words `Q`: every
    instruction is read into an arm whose conditions hold. Returns the written frame words at
    the end of the segment. -/
def lineOK (P : Params) : List (String × Int) → Lcmd → Option (List (String × Int))
  | Q, [] => some Q
  | Q, l :: rest =>
      match classify l.li_i with
      | some a => if a.ok P Q then lineOK P (a.post P Q) rest else none
      | none => none

theorem Arm.instr_lopn (a : Arm) : ∃ ds o ss, a.instr = .Lopn ds o ss := by
  cases a <;> exact ⟨_, _, _, rfl⟩

/-- The shape of an arm's instruction decodes to the arm's machine instructions. -/
theorem Arm.shape_ops {P : Params} {Q : List (String × Int)} {a : Arm} (h : a.ok P Q = true)
    {sh : DShape} (hs : shapeOf P a.instr = some sh) : sh.ops' = a.js P := by
  obtain ⟨hb, hp⟩ := a.bytes P Q h
  obtain ⟨ds, o, ss, he⟩ := a.instr_lopn
  rw [he] at hb hs
  exact shapeOf_lopn_ops _ hb hp hs

/-- **A checked segment.** For a segment accepted by `lineOK` from `Q` to `Q'` with computed
    shapes `shs`, the flag machine's straight fold of the segment is simulated by the decoded
    instructions of its shapes, from `PCorr Q` to `PCorr Q'`. -/
theorem lineOK_sim (P : Params) (rsp : BitVec 64) :
    ∀ (seg : Lcmd) (Q Q' : List (String × Int)) (shs : List DShape),
      lineOK P Q seg = some Q' → shapesOf P seg = some shs →
      DecSim (PCorr Q rsp) (PCorr Q' rsp) (printedOps seg) (shs.flatMap DShape.ops') := by
  intro seg
  induction seg with
  | nil =>
    intro Q Q' shs h hs
    simp only [lineOK, Option.some.injEq] at h
    simp only [shapesOf, Option.some.injEq] at hs
    subst h hs
    exact DecSim.nil _
  | cons l rest ih =>
    intro Q Q' shs h hs
    simp only [lineOK] at h
    split at h
    · rename_i a ha
      split at h
      · rename_i hok
        simp only [shapesOf] at hs
        split at hs
        · rename_i sh shs' h1 h2
          simp only [Option.some.injEq] at hs
          subst hs
          have hi := classify_instr ha
          rw [← hi] at h1
          have hops := Arm.shape_ops hok h1
          have hl : (l.li_i, MemTag.reg none) = (a.instr, MemTag.reg none) := by rw [hi]
          show DecSim _ _ ((l.li_i, MemTag.reg none) :: printedOps rest)
            (sh.ops' ++ shs'.flatMap DShape.ops')
          rw [hl, hops]
          exact (Arm.sim P Q rsp a hok).append (ih _ _ _ h h2)
        · exact absurd hs (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- Every instruction of a checked segment is an `Lopn`. -/
theorem lineOK_lopn (P : Params) :
    ∀ (seg : Lcmd) (Q Q' : List (String × Int)), lineOK P Q seg = some Q' →
      ∀ i ∈ printedOps seg, IsLopn i := by
  intro seg
  induction seg with
  | nil => intro _ _ _ i hi; simp [printedOps] at hi
  | cons l rest ih =>
    intro Q Q' h i hi
    simp only [lineOK] at h
    split at h
    · rename_i a ha
      split at h
      · simp only [printedOps, List.map_cons, List.mem_cons] at hi
        rcases hi with rfl | hi
        · obtain ⟨ds, o, ss, he⟩ := a.instr_lopn
          exact ⟨ds, o, ss, by rw [← classify_instr ha, he]⟩
        · exact ih _ _ h i hi
      · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- The computed shapes of a segment of `Lopn`s are straight-line shapes. -/
theorem straightB_of_lopns {P : Params} :
    ∀ {seg : Lcmd} {shs : List DShape}, (∀ i ∈ printedOps seg, IsLopn i) →
      shapesOf P seg = some shs → ∀ sh ∈ shs, straightB sh = true := by
  intro seg
  induction seg with
  | nil =>
    intro shs _ hs sh hsh
    simp only [shapesOf, Option.some.injEq] at hs
    subst hs
    simp at hsh
  | cons l rest ih =>
    intro shs hL hs sh hsh
    simp only [shapesOf] at hs
    split at hs
    · rename_i sh1 shs' h1 h2
      simp only [Option.some.injEq] at hs
      subst hs
      rcases List.mem_cons.mp hsh with rfl | hsh
      · obtain ⟨ds, o, ss, he⟩ := hL (l.li_i, .reg none) (by simp [printedOps])
        simp only at he
        rw [he] at h1
        rcases shapeOfBytes_ok (bs := encodeLopn P.frame P.spillW (.Lopn ds o ss) P.qsaveB) h1
          with ⟨q, rfl, -, -⟩ | ⟨pcs, rfl, -, -⟩ <;> rfl
      · exact ih (fun i hi => hL i (by simp [printedOps] at hi ⊢; exact Or.inr hi)) h2 sh hsh
    · exact absurd hs (by simp)

/-- A checked segment with computed shapes is a straight-line segment. -/
theorem straightOK_of_lineOK {P : Params} :
    ∀ {seg : Lcmd} {Q Q' : List (String × Int)} {shs : List DShape},
      lineOK P Q seg = some Q' → shapesOf P seg = some shs → straightOK P seg = true := by
  intro seg Q Q' shs h hs
  have hL := lineOK_lopn P seg Q Q' h
  unfold straightOK
  rw [hs]
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun sh hsh => straightB_of_lopns hL hs sh hsh, fun l hl => ?_⟩
  · obtain ⟨ds, o, ss, he⟩ := hL (l.li_i, .reg none) (List.mem_map_of_mem hl)
    simp only at he
    simp [he, labelOf]

/-! ## 9. A straight-line printed body -/

/-- The computed shapes of a segment followed by the return. -/
theorem shapesOf_append_ret (P : Params) (r : Linstr) (hr : r.li_i = .Lret) :
    ∀ seg : Lcmd, shapesOf P (seg ++ [r]) = (shapesOf P seg).map (· ++ [.one .skip]) := by
  intro seg
  induction seg with
  | nil => simp [shapesOf, hr, shapeOf]
  | cons l rest ih =>
    simp only [List.cons_append, shapesOf, ih]
    cases shapeOf P l.li_i <;> cases shapesOf P rest <;> rfl

theorem evalInstrA_leaFrame (sa : AState) (d : Int) :
    (∀ r, (evalInstrA sa (leaFrame d)).regs r
      = if r = "%rsp" then sa.regs "%rsp" + BitVec.ofInt 64 d else sa.regs r)
      ∧ (evalInstrA sa (leaFrame d)).mem = sa.mem := by
  refine ⟨fun r => ?_, ?_⟩
  · by_cases hr : r = "%rsp" <;>
      simp [leaFrame, evalInstrA, evalInstr, JState.setReg, AState.view, hr, x86_LEA]
  · simp [leaFrame, evalInstrA, evalInstr, JState.setReg, AState.view, writeAddr]

/-- **The straight-line printed body against its decoded bytes.** Let `body` be a straight-line
    printed body: a segment `P1` accepted by `lineOK` followed by the return, in the class
    `decodableLcmd`. From a machine state `sa` and a flag-machine state `b` at program counter
    `0` in which every general-purpose name `R` holds the value of the machine register
    `phys R`, every halting run of the flag machine on `P1` is matched by a halting run of the
    machine on the decoded function bytes. At the end the stack register is restored and every
    general-purpose name holds the value of its machine register. -/
theorem printed_line_sim (body P1 : Lcmd) (r : Linstr) (hbody : body = P1 ++ [r])
    (hr : r.li_i = .Lret) (hdec : decodableLcmd body = true) {Q : List (String × Int)}
    (hchk : lineOK (Params.ofBody body) [] P1 = some Q) (fn : String) (sa : AState)
    (b : LstateM) (zf : Bool) (hpc : b.lpc = 0)
    (hent : ∀ R, gpOk R = true → b.reg.getW R 64 = some (sa.regs (phys R))) (k : Nat)
    (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn (printedOps P1)) k
      { prog := { base := b, lfn := fn }, zf := zf } = some t) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ Halts aMachine prog 0 sa sa' ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ R, gpOk R = true → t.prog.base.reg.getW R 64 = some (sa'.regs (phys R)) := by
  set P := Params.ofBody body with hP
  simp only [decodableLcmd, Bool.and_eq_true, List.isEmpty_iff, bne_iff_ne, ne_eq] at hdec
  obtain ⟨⟨⟨⟨⟨hsh, hsaves⟩, hF0⟩, hF⟩, hF'⟩, hbr⟩ := hdec
  have hsb : shapesOf P body = (shapesOf P P1).map (· ++ [.one .skip]) := by
    rw [hbody]; exact shapesOf_append_ret P r hr P1
  obtain ⟨shs1, hs1⟩ : ∃ shs1, shapesOf P P1 = some shs1 := by
    rw [hsb] at hsh
    cases h : shapesOf P P1 with
    | none => rw [h] at hsh; exact absurd hsh (by simp)
    | some s => exact ⟨s, rfl⟩
  have hD1 : shapesD P P1 = shs1 := by simp [shapesD, hs1]
  have hDb : shapesD P body = shs1 ++ [.one .skip] := by simp [shapesD, hsb, hs1]
  have hstr := straightOK_of_lineOK hchk hs1
  have hbr' : branchOK (fundefItemsL body (shapesD P P1 ++ [.one .skip])) 0
      (fundefItemsL body (shapesD P P1 ++ [.one .skip])) = true := by
    rw [hD1, ← hDb]; exact hbr
  have hlay := DecodeGenStraight.decodeLprog_line_gen body P1 r hbody hstr hr hsaves
    (Int.ofNat_ne_zero.mpr hF0) hF hF' hbr'
  rw [← hP] at hlay
  set F := P.frame
  set js := opsD P P1 with hjs
  have hjs' : js = shs1.flatMap DShape.ops' := by rw [hjs, opsD, hD1]
  -- the prologue
  obtain ⟨hl1, hm1⟩ := evalInstrA_leaFrame sa (-(Int.ofNat F))
  set sa1 := evalInstrA sa (leaFrame (-(Int.ofNat F)))
  set rsp1 := sa.regs "%rsp" + BitVec.ofInt 64 (-(Int.ofNat F))
  have hc0 : PCorr [] rsp1 sa1 b zf :=
    { regs := fun R hR => by
        rw [hent R hR, hl1, ite_eq_right (fun e => (gpFacts hR).physNe e)]
      sp := by rw [hl1, ite_eq_left rfl]
      slots := fun p hp => absurd hp (by simp)
      names := fun p hp => absurd hp (by simp) }
  obtain ⟨b1, z1, hr1, hc1⟩ := lineOK_sim P rsp1 P1 [] Q shs1 hchk hs1 sa1 b zf hc0
  have hrun1 := DecodeGenStraight.lsemFuelMemF_line fn (printedOps P1)
    (lineOK_lopn P P1 [] Q hchk) b b1 zf z1 hpc hr1
  obtain rfl := DecodedLsemLoop.lsemFuelMemF_det _ k _ _ t _ hrun hrun1
  -- the epilogue
  set sa2 := aMachine.runBlock sa1 (shs1.flatMap DShape.ops')
  obtain ⟨hl2, -⟩ := evalInstrA_leaFrame sa2 (Int.ofNat F)
  have hrb : aMachine.runBlock sa (leaFrame (-(Int.ofNat F)) :: js ++ [leaFrame (Int.ofNat F)])
      = evalInstrA sa2 (leaFrame (Int.ofNat F)) := by
    rw [List.cons_append, hjs']
    show aMachine.runBlock sa1 _ = _
    rw [Machine.runBlock_append]
    rfl
  refine ⟨_, aMachine.runBlock sa (leaFrame (-(Int.ofNat F)) :: js ++ [leaFrame (Int.ofNat F)]),
    hlay, halts_of_reaches
      (pc' := (leaFrame (-(Int.ofNat F)) :: js ++ [leaFrame (Int.ofNat F)]).length) ?_ ?_,
    ?_, ?_⟩
  · have h := reaches_ops aMachine [] (leaFrame (-(Int.ofNat F)) :: js ++ [leaFrame (Int.ofNat F)])
      [.ret] sa
    simpa [DecodeGenStraight.lineLayout] using h
  · simp [DecodeGenStraight.lineLayout]
  · rw [hrb, hl2, ite_eq_left rfl, hc1.sp]
    simp [rsp1, F, BitVec.ofInt_neg, BitVec.ofInt_natCast]
  · intro R hR
    rw [hrb, hl2, ite_eq_right (fun e => (gpFacts hR).physNe e)]
    exact hc1.regs R hR

/-- An instruction that is the return. -/
def isRetB : LinstrR → Bool
  | .Lret => true
  | _ => false

/-- **The straight-line printed bodies of the covered fragment**: decodable, ending in the
    return, with every other instruction read into an arm whose conditions hold. -/
def printedLineB (body : Lcmd) : Bool :=
  decodableLcmd body && body.getLast?.any (fun r => isRetB r.li_i)
    && (lineOK (Params.ofBody body) [] body.dropLast).isSome

/-- **The decoded bytes of a straight-line printed body simulate its flag-machine run.** For
    every body in the class `printedLineB`, from a machine state `sa` and a flag-machine state
    `b` at program counter `0` in which every general-purpose name `R` holds the value of the
    machine register `phys R`, every halting run of the flag machine on the body without its
    return is matched by a halting run of the machine on the decoded function bytes, after
    which the stack register is restored and every general-purpose name holds the value of
    its machine register. -/
theorem printedLine_sim (body : Lcmd) (h : printedLineB body = true) (fn : String)
    (sa : AState) (b : LstateM) (zf : Bool) (hpc : b.lpc = 0)
    (hent : ∀ R, gpOk R = true → b.reg.getW R 64 = some (sa.regs (phys R))) (k : Nat)
    (t : LstateMF)
    (hrun : lsemFuelMemF (singletonProgM fn (printedOps body.dropLast)) k
      { prog := { base := b, lfn := fn }, zf := zf } = some t) :
    ∃ prog sa', decodeLprog (encodeLfundefBytes body) = some prog
      ∧ Halts aMachine prog 0 sa sa' ∧ sa'.regs "%rsp" = sa.regs "%rsp"
      ∧ ∀ R, gpOk R = true → t.prog.base.reg.getW R 64 = some (sa'.regs (phys R)) := by
  simp only [printedLineB, Bool.and_eq_true, Option.any_eq_true] at h
  obtain ⟨⟨hdec, r, hlast, hret⟩, hok⟩ := h
  obtain ⟨Q, hQ⟩ := Option.isSome_iff_exists.mp hok
  have hr : r.li_i = .Lret := by
    revert hret; unfold isRetB; split <;> simp_all
  have hbody : body = body.dropLast ++ [r] := (List.dropLast_append_getLast? r hlast).symm
  exact printed_line_sim body body.dropLast r hbody hr hdec hQ fn sa b zf hpc hent k t hrun

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
