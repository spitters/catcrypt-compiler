/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCoveredPasses

/-!
# The legal forms of the lowering against the covered instructions

`LowerLegal.lower_legal` proves that every instruction the lowering emits has a legal form
`LegalForm` of the x86 encoder; `PrintedCompleteLegal.Covered` is the class of instructions the
printed-class gate `instrOKWB` accepts. This module compares the two classes: every legal form
in the context of a body is covered in that body or lies in one of the families of
`LegalGap`, each named by the shape and the condition that the gate does not read.

The general-purpose names of the gate (`gpOk`) are the encoder registers (`isGpName`) other
than the stack register `RSP`. The allocation pool and the two reload scratch registers of the
x86 back end are general-purpose names of the gate, so a register the allocation resolves is
never `RSP`.

## Main definitions

* `UsesRsp ds ss`: an operand among `ds` and `ss` names the stack register.
* `CellName n`, `CellOk n`: `n` is a memory cell the encoder addresses, and a cell
  `mem.B.off` with a general-purpose base `B` and a `rel32` offset.
* `LegalGap body i`: the families of legal forms outside `Covered body`.

## Main results

* `gpOk_iff_isGpName`: the gate's general-purpose names are the encoder registers other than
  `RSP`.
* `gpOk_of_mem_allocPool`, `gpOk_reloadScratch`, `gpOk_reloadScratch2`: the allocation pool
  and the reload scratch registers are general-purpose names of the gate.
* `covered_or_gap_of_legalForm`: a legal form in the context of a body is covered in it or
  lies in a family of `LegalGap`.
* `covered_or_gap_lower`: every instruction of one position of `physPositionEmit` is covered
  in a body or lies in a family of `LegalGap`, under the hypotheses of `lower_legal` at the
  parameters of that body.
* `legalGap_of_unfusedMulHi`: an unfused high-word binding lies in the family `mulHi`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCoveredLower

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (cellParts?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (condPol labelAt)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (LegalForm isMovMnem)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (faOff)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (kOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeComplete
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder (dispOk32)
open CatCrypt.Crypto.SecureCompilation.X86Backend.GateOfLegal (GateForm castMnems tagMnem)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCompleteLegal (Covered UnfusedMulHi)

/-! ## 1. The stack register -/

/-- **The gate's general-purpose names are the encoder registers other than `RSP`.** -/
theorem gpOk_iff_isGpName (r : String) : gpOk r = true ↔ isGpName r = true ∧ r ≠ "RSP" := by
  unfold gpOk gpList isGpName
  split <;> simp_all

/-- An encoder register other than `RSP` is a general-purpose name of the gate. -/
theorem gpOk_of_isGpName {r : String} (h : isGpName r = true) (hr : r ≠ "RSP") :
    gpOk r = true :=
  (gpOk_iff_isGpName r).2 ⟨h, hr⟩

/-- The allocation pool of the x86 back end consists of general-purpose names of the gate. -/
theorem gpOk_of_mem_allocPool {r : String} (h : r ∈ X86Isa.x86Isa.allocPool) : gpOk r = true := by
  rw [X86Isa.x86Isa_allocPool] at h
  revert r
  decide

/-- The primary reload scratch register is a general-purpose name of the gate. -/
theorem gpOk_reloadScratch : gpOk reloadScratch = true := by decide

/-- The secondary reload scratch register is a general-purpose name of the gate. -/
theorem gpOk_reloadScratch2 : gpOk reloadScratch2 = true := by decide

/-! ## 2. The families outside the covered instructions -/

/-- **An operand names the stack register**: a register operand `RSP` among the destinations
    `ds` and the sources `ss`, or a register-indexed source with base or index `RSP`. -/
def UsesRsp (ds ss : List LOperand) : Prop :=
  LOperand.reg "RSP" ∈ ds ++ ss ∨
    ∃ (x : String) (sc : Nat), LOperand.arrIdx "RSP" x sc ∈ ss ∨ LOperand.arrIdx x "RSP" sc ∈ ss

/-- **A memory cell the encoder addresses**: a name `mem.<base>.<off>` with a tabulated
    base. -/
def CellName (n : String) : Prop := (parseMemNameGp n).isSome = true

/-- **A cell the gate reads**: a name `mem.B.off` with a general-purpose base `B` and a
    `rel32` offset `off`. -/
def CellOk (n : String) : Prop :=
  ∃ (b : String) (off : Nat), cellParts? n = some (b, off) ∧ gpOk b = true ∧
    dispOk32 (Int.ofNat off) = true

/-- The two-address operations over registers the gate reads. -/
def aluMnems : List String :=
  ["ADD:64", "SUB:64", "AND:64", "OR:64", "XOR:64", "MUL:64", "CMP:64"]

/-- **The two-address operations against an immediate the gate reads**: a group-1 operation
    at the 64-bit tag against a 64-bit immediate that sign-extends from 32 bits, the compare
    against an immediate that sign-extends from 8 bits, a left or logical right shift by a
    count below `64` (nonzero for the right shift), and an arithmetic right shift by
    `1 … 63`. -/
def AluImmOk (opn : String) (v : Nat) : Prop :=
  (opn ∈ ["ADD:64", "SUB:64", "AND:64", "OR:64", "XOR:64"] ∧ v < 2 ^ 64 ∧
      ScalarEncoder.fitsImm32S v = true) ∨
    (opn = "CMP:64" ∧ fitsImm8S 1 v = true) ∨
    (opn ∈ ["SHL:64", "SHR:64"] ∧ v < 64 ∧ (0 < v ∨ opn = "SHL:64")) ∨
    (opn = "SAR:64" ∧ 0 < v ∧ v < 64)

/-- **The one-source operations the gate reads**: a width cast of `castMnems`, the count-`0`
    shift `SHL:0:64`, and a count-in-mnemonic left or logical right shift `b:k:64` by
    `1 … 63`. -/
def UnaryOk (opn : String) : Prop :=
  opn ∈ castMnems ∨ opn = "SHL:0:64" ∨
    ∃ (b : String) (k : Nat), b ∈ ["SHL", "SHR"] ∧ 0 < k ∧ k < 64 ∧ opn = tagMnem b k

/-- **The families of legal forms outside the covered instructions** of the body `body`. Each
    constructor names a shape of `LegalForm` at the x86 encoder and the condition under which
    no arm of `GateOfLegal.GateForm`, no printed shape and no stack-array shape reads it. -/
inductive LegalGap (body : Lcmd) : LinstrR → Prop
  /-- An operation that names the stack register `RSP`, which the gate's general-purpose
      names exclude. -/
  | rsp (ds : List LOperand) (opn : String) (ss : List LOperand) : UsesRsp ds ss →
      LegalGap body (.Lopn ds opn ss)
  /-- The untagged register move `MOV D, S`, between registers, frame slots or cells. -/
  | movUntagged (d s : String) : LegalGap body (.Lopn [.reg d] "MOV" [.reg s])
  /-- The move `MOVQ` into or out of a memory cell; the gate reads cell moves at `MOV:64`. -/
  | movqCell (d s : String) : CellName d ∨ CellName s →
      LegalGap body (.Lopn [.reg d] "MOVQ" [.reg s])
  /-- An operation on a memory cell without a general-purpose base or a `rel32` offset. -/
  | cellOff (ds : List LOperand) (opn : String) (ss : List LOperand) (n : String) :
      LOperand.reg n ∈ ds ++ ss → CellName n → ¬ CellOk n → LegalGap body (.Lopn ds opn ss)
  /-- A move into a frame slot whose offset is outside the `rel32` range. -/
  | slotStoreFar (m q s : String) : isSpillOrQsave q = true →
      dispOk32 (slotOff (Params.ofBody body) q) = false →
      LegalGap body (.Lopn [.reg q] m [.reg s])
  /-- A move out of a frame slot that fails `kOk`: an offset outside the `rel32` range or a
      word that overlaps the red-zone word. -/
  | slotLoadRedZone (m d q : String) : isSpillOrQsave q = true →
      kOk (Params.ofBody body) q = false → LegalGap body (.Lopn [.reg d] m [.reg q])
  /-- The immediate move `MOVQ D, #v`; the gate reads immediate moves at `MOV` and
      `MOV:64`. -/
  | movqImm (d : String) (v : Nat) : LegalGap body (.Lopn [.reg d] "MOVQ" [.imm v])
  /-- An immediate move of a value beyond its field: at least `2^31` under the untagged `MOV`
      or at least `2^64`. -/
  | movImmWide (mn d : String) (v : Nat) : (mn = "MOV" ∧ 2 ^ 31 ≤ v) ∨ 2 ^ 64 ≤ v →
      LegalGap body (.Lopn [.reg d] mn [.imm v])
  /-- An immediate move into a frame slot at a mnemonic other than `MOV:64`, at an offset
      outside the `rel32` range, or of a value that does not sign-extend from 32 bits into a
      word that overlaps the red-zone word. -/
  | slotImm (mn q : String) (v : Nat) : isSpillOrQsave q = true →
      (mn ≠ "MOV:64" ∨ dispOk32 (slotOff (Params.ofBody body) q) = false ∨
        (ScalarEncoder.fitsImm32S v = false ∧
          sepB cmovRedZone (slotOff (Params.ofBody body) q) = false)) →
      LegalGap body (.Lopn [.reg q] mn [.imm v])
  /-- A select at a mnemonic other than `CMOV:64`. -/
  | selectMnem (d opn c a b : String) : opn ≠ "CMOV:64" →
      LegalGap body (.Lopn [.reg d] opn [.reg c, .reg a, .reg b])
  /-- A select whose condition register is the destination or a data operand. -/
  | selectAlias (d c a b : String) : d = c ∨ a = c ∨ b = c →
      LegalGap body (.Lopn [.reg d] "CMOV:64" [.reg c, .reg a, .reg b])
  /-- A materialised comparison at the untagged `SETE` or `SETNE`. -/
  | setccMnem (d opn a : String) (s : LOperand) : opn ∉ ["SETE:64", "SETNE:64"] →
      LegalGap body (.Lopn [.reg d] opn [.reg a, s])
  /-- A materialised comparison against an immediate of at least `2^31`. -/
  | setccImmWide (d opn a : String) (v : Nat) : 2 ^ 31 ≤ v →
      LegalGap body (.Lopn [.reg d] opn [.reg a, .imm v])
  /-- A two-address operation over registers at a mnemonic outside `aluMnems`: an untagged
      or narrow `ADD`, `SUB`, `AND`, `OR`, `XOR`, `MUL` or `CMP`. -/
  | aluMnem (d opn s : String) : x86Alu opn = true → opn ∉ aluMnems →
      LegalGap body (.Lopn [.reg d] opn [.reg d, .reg s])
  /-- A two-address operation against an immediate outside `AluImmOk`: an untagged or narrow
      mnemonic, a multiplication by an immediate, a compare against an immediate beyond
      8 bits, or a shift count of at least `64`. -/
  | aluImm (d opn : String) (v : Nat) : x86AluImm opn v = true → ¬ AluImmOk opn v →
      LegalGap body (.Lopn [.reg d] opn [.reg d, .imm v])
  /-- A three-register shift other than `SHL:64` and `SHR:64`: the arithmetic `SAR:64`. -/
  | shiftRegMnem (d opn a s : String) : x86ShiftReg opn = true →
      opn ∉ ["SHL:64", "SHR:64"] → LegalGap body (.Lopn [.reg d] opn [.reg a, .reg s])
  /-- The and-not `ANDN:64`, which the gate does not read. -/
  | andn (d opn a s : String) : x86Andn opn = true →
      LegalGap body (.Lopn [.reg d] opn [.reg a, .reg s])
  /-- A one-source operation outside `UnaryOk`: the negation, an arithmetic right shift or a
      shift by `64` or more in the mnemonic, or a cast outside `castMnems`. -/
  | unaryMnem (d opn s : String) : x86Unary opn = true → ¬ UnaryOk opn →
      LegalGap body (.Lopn [.reg d] opn [.reg s])
  /-- A load or store other than `LOAD:64` from a cell the gate reads into a general-purpose
      name, and `STORE:64` of a general-purpose name into such a cell. -/
  | memMov (d mn s : String) : x86MemMov mn = true →
      ¬ ((mn = "LOAD:64" ∧ gpOk d = true ∧ CellOk s) ∨
        (mn = "STORE:64" ∧ CellOk d ∧ gpOk s = true)) →
      LegalGap body (.Lopn [.reg d] mn [.reg s])
  /-- A register-indexed load or address computation other than `LEA:64` and `LOADIDX` at
      stride `8`. -/
  | sibLoad (d opn b x : String) (sc : Nat) : ¬ (opn = "LEA:64" ∨ (opn = "LOADIDX" ∧ sc = 8)) →
      LegalGap body (.Lopn [.reg d] opn [.arrIdx b x sc])
  /-- A register-indexed store other than `STOREIDX` at stride `8` into a named array. -/
  | sibStore (a : LOperand) (opn b x v : String) (sc : Nat) :
      ¬ (opn = "STOREIDX" ∧ sc = 8 ∧ ∃ A, a = .reg A) →
      LegalGap body (.Lopn [a] opn [.arrIdx b x sc, .reg v])
  /-- A constant-index stack-array store whose destination is no general-purpose name. -/
  | storeImmDst (a : LOperand) (b v : String) (k : Nat) : (¬ ∃ D, a = .reg D ∧ gpOk D = true) →
      LegalGap body (.Lopn [a] "STOREIMM" [.reg b, .reg v, .imm k])
  /-- The stack-array zeroing into a destination register; the gate reads the zeroing from a
      base register. -/
  | zeroArrDst (d : String) (n w : Nat) : LegalGap body (.Lopn [.reg d] "ZEROARR" [.imm n, .imm w])
  /-- A frame-array address whose base offset is outside the `rel32` range. -/
  | leaFaFar (d q : String) : dispOk32 (faOff q) = false →
      LegalGap body (.Lopn [.reg d] "LEA:64" [.reg q])
  /-- A carry-chain addition at a mnemonic other than `ADCX:64`. -/
  | carryMnem (d opn a s c : String) : x86Carry3 opn = true → opn ≠ "ADCX:64" →
      LegalGap body (.Lopn [.reg d] opn [.reg a, .reg s, .reg c])
  /-- A carry-chain addition or carry-out binding whose carry-in is a word source. -/
  | carryInWord (d opn a s c : String) : a = c ∨ s = c →
      LegalGap body (.Lopn [.reg d] opn [.reg a, .reg s, .reg c])
  /-- A carry-chain addition whose destination is a later source and not the first. -/
  | carryDst (d a s c : String) : a ≠ d → d = s ∨ d = c →
      LegalGap body (.Lopn [.reg d] "ADCX:64" [.reg a, .reg s, .reg c])
  /-- A flag materialisation other than `ADCXHI:64`: `ADOXHI`, `SETC`, or an untagged or
      narrow carry-out binding. -/
  | flagMnem (d opn : String) (ss : List LOperand) : x86FlagOut opn ss = true →
      opn ≠ "ADCXHI:64" → LegalGap body (.Lopn [.reg d] opn ss)
  /-- A carry-out binding whose sources are not three registers. -/
  | flagArity (d : String) (ss : List LOperand) : (¬ ∃ a s c, ss = [.reg a, .reg s, .reg c]) →
      LegalGap body (.Lopn [.reg d] "ADCXHI:64" ss)
  /-- A carry-out binding with a source that fails `kOk`: a frame slot outside the `rel32`
      range or overlapping the red-zone word, or a name that is neither a general-purpose
      name nor a frame slot. -/
  | flagSlotSrc (d a s c : String) :
      kOk (Params.ofBody body) a = false ∨ kOk (Params.ofBody body) s = false ∨
        kOk (Params.ofBody body) c = false →
      LegalGap body (.Lopn [.reg d] "ADCXHI:64" [.reg a, .reg s, .reg c])
  /-- A widening multiplication at a mnemonic other than `MULX`. -/
  | mulxMnem (l h opn s : String) : x86WideMul opn = true → opn ≠ "MULX" →
      LegalGap body (.Lopn [.reg l, .reg h] opn [.reg s])
  /-- A high-word binding `MULXHI` at any tag (`UnfusedMulHi` at the 64-bit tag). -/
  | mulHi (ds : List LOperand) (opn : String) (ss : List LOperand) :
      isMulHiBinding opn = true → LegalGap body (.Lopn ds opn ss)
  /-- A frame directive or the keep marker. -/
  | directive (ds : List LOperand) (opn : String) (ss : List LOperand) :
      opn ∈ ["FRAME", "FRAMEADD", "KEEP"] → LegalGap body (.Lopn ds opn ss)
  /-- An identity count-in-mnemonic shift of a register onto itself other than `SHL:0:64`. -/
  | identityShift (d opn : String) : isIdentityTagShift opn = true → opn ≠ "SHL:0:64" →
      LegalGap body (.Lopn [.reg d] opn [.reg d])
  /-- A jump, a call, a return or an alignment directive. -/
  | transfer (i : LinstrR) :
      (∃ t, i = .Lgoto t) ∨ (∃ ra t, i = .Lcall ra t) ∨ i = .Lret ∨ i = .Lalign →
      LegalGap body i
  /-- A conditional branch on a condition other than the zero flag, or to a label the body
      does not define. -/
  | condOut (cc : String) (l : LLabel) :
      (condPol cc).isSome = false ∨ (labelAt body l).isSome = false →
      LegalGap body (.Lcond (.reg cc) l)

/-- An unfused high-word binding lies in the family `mulHi`. -/
theorem legalGap_of_unfusedMulHi {body : Lcmd} {i : LinstrR} (h : UnfusedMulHi i) :
    LegalGap body i := by
  obtain ⟨ds, ss, rfl⟩ := h
  exact .mulHi ds _ ss (by decide)

/-! ## 3. The register moves -/

/-- A frame slot with a frame offset is a memory name of the encoder. -/
theorem encMemName_of_slot {F W Q : Nat} {n : String} (h : (spillQsaveOff F W n Q).isSome = true) :
    encMemName n = true := by
  obtain ⟨off, ho⟩ := Option.isSome_iff_exists.1 h
  simp [encMemName, isSpillOrQsave_of_spillQsaveOff ho]

/-- A memory cell the encoder addresses is a memory name of the encoder. -/
theorem encMemName_of_cell {n : String} (h : CellName n) : encMemName n = true := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 h
  simp [encMemName, parseMemName_of_parseMemNameGp hp]

/-- A name with a frame offset is a frame-slot name. -/
theorem isSpillOrQsave_of_slot {F W Q : Nat} {n : String}
    (h : (spillQsaveOff F W n Q).isSome = true) : isSpillOrQsave n = true := by
  obtain ⟨off, ho⟩ := Option.isSome_iff_exists.1 h
  exact isSpillOrQsave_of_spillQsaveOff ho

/-- A register move of `LegalForm` in the context of `body` is covered or in a gap family. -/
theorem covered_or_gap_mov {body : Lcmd} {mn d s : String} (hm : isMovMnem mn = true)
    (hd : OpResolves (Params.ofBody body).frame (Params.ofBody body).spillW
      (Params.ofBody body).qsaveB d)
    (hs : OpResolves (Params.ofBody body).frame (Params.ofBody body).spillW
      (Params.ofBody body).qsaveB s)
    (hds : (encMemName d && encMemName s) = false) :
    Covered body (.Lopn [.reg d] mn [.reg s]) ∨ LegalGap body (.Lopn [.reg d] mn [.reg s]) := by
  by_cases hR : UsesRsp [.reg d] [.reg s]
  · exact Or.inr (.rsp _ _ _ hR)
  have hdR : d ≠ "RSP" := by rintro rfl; exact hR (Or.inl (by simp))
  have hsR : s ≠ "RSP" := by rintro rfl; exact hR (Or.inl (by simp))
  by_cases hMOV : mn = "MOV"
  · subst hMOV; exact Or.inr (.movUntagged d s)
  have hm' : mn ∈ ["MOV:64", "MOVQ"] := by
    simp only [isMovMnem, Bool.or_eq_true, beq_iff_eq] at hm
    grind
  rcases hd with hdg | hdq | hdc <;> rcases hs with hsg | hsq | hsc
  · exact Or.inl (Or.inl (.movRR mn d s hm' (gpOk_of_isGpName hdg hdR)
      (gpOk_of_isGpName hsg hsR)))
  · by_cases hk : kOk (Params.ofBody body) s = true
    · exact Or.inl (Or.inl (.movLoad mn d s hm' (gpOk_of_isGpName hdg hdR)
        (isSpillOrQsave_of_slot hsq) hk))
    · exact Or.inr (.slotLoadRedZone mn d s (isSpillOrQsave_of_slot hsq) (by simpa using hk))
  · by_cases hq : mn = "MOVQ"
    · subst hq; exact Or.inr (.movqCell d s (Or.inr hsc))
    have h64 : mn = "MOV:64" := by simp only [List.mem_cons, List.not_mem_nil] at hm'; grind
    subst h64
    by_cases hc : CellOk s
    · obtain ⟨b, off, h1, h2, h3⟩ := hc
      exact Or.inl (Or.inl (.loadMov d s b off h1 (gpOk_of_isGpName hdg hdR) h2 h3))
    · exact Or.inr (.cellOff _ _ _ s (by simp) hsc hc)
  · by_cases hk : dispOk32 (slotOff (Params.ofBody body) d) = true
    · exact Or.inl (Or.inl (.movStore mn d s hm' (isSpillOrQsave_of_slot hdq) hdq hk
        (gpOk_of_isGpName hsg hsR)))
    · exact Or.inr (.slotStoreFar mn d s (isSpillOrQsave_of_slot hdq) (by simpa using hk))
  · simp [encMemName_of_slot hdq, encMemName_of_slot hsq] at hds
  · simp [encMemName_of_slot hdq, encMemName_of_cell hsc] at hds
  · by_cases hq : mn = "MOVQ"
    · subst hq; exact Or.inr (.movqCell d s (Or.inl hdc))
    have h64 : mn = "MOV:64" := by simp only [List.mem_cons, List.not_mem_nil] at hm'; grind
    subst h64
    by_cases hc : CellOk d
    · obtain ⟨b, off, h1, h2, h3⟩ := hc
      exact Or.inl (Or.inl (.storeMov d b off s h1 (gpOk_of_isGpName hsg hsR) h2 h3))
    · exact Or.inr (.cellOff _ _ _ d (by simp) hdc hc)
  · simp [encMemName_of_cell hdc, encMemName_of_slot hsq] at hds
  · simp [encMemName_of_cell hdc, encMemName_of_cell hsc] at hds

/-! ## 4. The immediate moves -/

/-- An immediate move into an encoder register is covered or in a gap family. -/
theorem covered_or_gap_movImmReg {body : Lcmd} {mn d : String} {v : Nat}
    (hm : isMovMnem mn = true) (hd : isGpName d = true) :
    Covered body (.Lopn [.reg d] mn [.imm v]) ∨ LegalGap body (.Lopn [.reg d] mn [.imm v]) := by
  by_cases hR : d = "RSP"
  · exact Or.inr (.rsp _ _ _ (Or.inl (by simp [hR])))
  have hg := gpOk_of_isGpName hd hR
  obtain rfl | rfl | rfl : mn = "MOV" ∨ mn = "MOV:64" ∨ mn = "MOVQ" := by
    simp only [isMovMnem, Bool.or_eq_true, beq_iff_eq] at hm
    grind
  · by_cases hv : v < 2 ^ 31
    · exact Or.inl (Or.inl (.movImm32 d v hg hv))
    · exact Or.inr (.movImmWide _ d v (Or.inl ⟨rfl, by omega⟩))
  · by_cases hv : v < 2 ^ 64
    · exact Or.inl (Or.inl (.movImm64 d v hg hv))
    · exact Or.inr (.movImmWide _ d v (Or.inr (by omega)))
  · exact Or.inr (.movqImm d v)

/-- An immediate move into a frame slot with a frame offset is covered or in a gap family. -/
theorem covered_or_gap_movImmSlot {body : Lcmd} {mn q : String} {v : Nat}
    (hs : (spillQsaveOff (Params.ofBody body).frame (Params.ofBody body).spillW q
      (Params.ofBody body).qsaveB).isSome = true) :
    Covered body (.Lopn [.reg q] mn [.imm v]) ∨ LegalGap body (.Lopn [.reg q] mn [.imm v]) := by
  have hq := isSpillOrQsave_of_slot hs
  by_cases hv : 2 ^ 64 ≤ v
  · exact Or.inr (.movImmWide _ _ _ (Or.inr hv))
  by_cases h64 : mn = "MOV:64"
  · subst h64
    by_cases hdsp : dispOk32 (slotOff (Params.ofBody body) q) = true
    · by_cases hf : ScalarEncoder.fitsImm32S v = true ∨
          sepB cmovRedZone (slotOff (Params.ofBody body) q) = true
      · exact Or.inl (Or.inl (.movImmSlot q v hq hs hdsp (by omega) hf))
      · exact Or.inr (.slotImm _ q v hq (Or.inr (Or.inr
          (by unfold ScalarEncoder.fitsImm32S at hf ⊢; simp_all))))
    · exact Or.inr (.slotImm _ q v hq (Or.inr (Or.inl (by simpa using hdsp))))
  · exact Or.inr (.slotImm _ q v hq (Or.inl h64))

/-! ## 5. The register operations -/

/-- A select over encoder registers is covered or in a gap family. -/
theorem covered_or_gap_select {body : Lcmd} {opn d c a b : String} (hd : isGpName d = true)
    (hc : isGpName c = true) (ha : isGpName a = true) (hb : isGpName b = true) :
    Covered body (.Lopn [.reg d] opn [.reg c, .reg a, .reg b]) ∨
      LegalGap body (.Lopn [.reg d] opn [.reg c, .reg a, .reg b]) := by
  by_cases hR : UsesRsp [.reg d] [.reg c, .reg a, .reg b]
  · exact Or.inr (.rsp _ _ _ hR)
  have hdR : d ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have hcR : c ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have haR : a ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have hbR : b ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  by_cases ho : opn = "CMOV:64"
  · subst ho
    by_cases hal : d = c ∨ a = c ∨ b = c
    · exact Or.inr (.selectAlias d c a b hal)
    · exact Or.inl (Or.inl (.select d c a b (gpOk_of_isGpName hd hdR) (gpOk_of_isGpName hc hcR)
        (gpOk_of_isGpName ha haR) (gpOk_of_isGpName hb hbR) (by grind) (by grind) (by grind)))
  · exact Or.inr (.selectMnem d opn c a b ho)

/-- A materialised comparison over encoder registers is covered or in a gap family. -/
theorem covered_or_gap_setcc {body : Lcmd} {opn d a s : String} (hd : isGpName d = true)
    (ha : isGpName a = true) (hs : isGpName s = true) :
    Covered body (.Lopn [.reg d] opn [.reg a, .reg s]) ∨
      LegalGap body (.Lopn [.reg d] opn [.reg a, .reg s]) := by
  by_cases hR : UsesRsp [.reg d] [.reg a, .reg s]
  · exact Or.inr (.rsp _ _ _ hR)
  have hdR : d ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have haR : a ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have hsR : s ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  by_cases hm : opn ∈ ["SETE:64", "SETNE:64"]
  · exact Or.inl (Or.inl (.setcc opn d a s hm (gpOk_of_isGpName hd hdR)
      (gpOk_of_isGpName ha haR) (gpOk_of_isGpName hs hsR)))
  · exact Or.inr (.setccMnem d opn a _ hm)

/-- A materialised comparison against an immediate is covered or in a gap family. -/
theorem covered_or_gap_setccImm {body : Lcmd} {opn d a : String} {v : Nat}
    (hd : isGpName d = true) (ha : isGpName a = true) :
    Covered body (.Lopn [.reg d] opn [.reg a, .imm v]) ∨
      LegalGap body (.Lopn [.reg d] opn [.reg a, .imm v]) := by
  by_cases hR : UsesRsp [.reg d] [.reg a, .imm v]
  · exact Or.inr (.rsp _ _ _ hR)
  have hdR : d ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have haR : a ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  by_cases hm : opn ∈ ["SETE:64", "SETNE:64"]
  · by_cases hv : v < 2 ^ 31
    · exact Or.inl (Or.inl (.setccImm opn d a v hm (gpOk_of_isGpName hd hdR)
        (gpOk_of_isGpName ha haR) hv))
    · exact Or.inr (.setccImmWide d opn a v (by omega))
  · exact Or.inr (.setccMnem d opn a _ hm)

/-- A two-address operation over encoder registers is covered or in a gap family. -/
theorem covered_or_gap_alu {body : Lcmd} {opn d s : String} (ho : x86Alu opn = true)
    (hd : isGpName d = true) (hs : isGpName s = true) :
    Covered body (.Lopn [.reg d] opn [.reg d, .reg s]) ∨
      LegalGap body (.Lopn [.reg d] opn [.reg d, .reg s]) := by
  by_cases hR : UsesRsp [.reg d] [.reg d, .reg s]
  · exact Or.inr (.rsp _ _ _ hR)
  have hdR : d ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have hsR : s ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  by_cases hm : opn ∈ aluMnems
  · exact Or.inl (Or.inl (.alu opn d s hm (gpOk_of_isGpName hd hdR) (gpOk_of_isGpName hs hsR)))
  · exact Or.inr (.aluMnem d opn s ho hm)

/-- A two-address operation against an immediate is covered or in a gap family. -/
theorem covered_or_gap_aluImm {body : Lcmd} {opn d : String} {v : Nat}
    (ho : x86AluImm opn v = true) (hd : isGpName d = true) :
    Covered body (.Lopn [.reg d] opn [.reg d, .imm v]) ∨
      LegalGap body (.Lopn [.reg d] opn [.reg d, .imm v]) := by
  by_cases hR : d = "RSP"
  · exact Or.inr (.rsp _ _ _ (Or.inl (by simp [hR])))
  have hg := gpOk_of_isGpName hd hR
  by_cases hk : AluImmOk opn v
  · rcases hk with ⟨hm, hv, hf⟩ | ⟨rfl, hf⟩ | ⟨hm, hv, h0⟩ | ⟨rfl, h0, hv⟩
    · exact Or.inl (Or.inl (.aluImm opn d v hm hg hv hf))
    · exact Or.inl (Or.inl (.cmpImm d v hg hf))
    · exact Or.inl (Or.inl (.shiftImm opn d v hm hg hv h0))
    · exact Or.inl (Or.inl (.sarImm d v hg h0 hv))
  · exact Or.inr (.aluImm d opn v ho hk)

/-- A three-register shift is covered or in a gap family. -/
theorem covered_or_gap_shiftReg {body : Lcmd} {opn d a s : String}
    (ho : x86ShiftReg opn = true) (hd : isGpName d = true) (ha : isGpName a = true)
    (hs : isGpName s = true) :
    Covered body (.Lopn [.reg d] opn [.reg a, .reg s]) ∨
      LegalGap body (.Lopn [.reg d] opn [.reg a, .reg s]) := by
  by_cases hR : UsesRsp [.reg d] [.reg a, .reg s]
  · exact Or.inr (.rsp _ _ _ hR)
  have hdR : d ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have haR : a ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have hsR : s ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  by_cases hm : opn ∈ ["SHL:64", "SHR:64"]
  · exact Or.inl (Or.inl (.shiftReg opn d a s hm (gpOk_of_isGpName hd hdR)
      (gpOk_of_isGpName ha haR) (gpOk_of_isGpName hs hsR)))
  · exact Or.inr (.shiftRegMnem d opn a s ho hm)

/-- A one-source operation over encoder registers is covered or in a gap family. -/
theorem covered_or_gap_unary {body : Lcmd} {opn d s : String} (ho : x86Unary opn = true)
    (hd : isGpName d = true) (hs : isGpName s = true) :
    Covered body (.Lopn [.reg d] opn [.reg s]) ∨ LegalGap body (.Lopn [.reg d] opn [.reg s]) := by
  by_cases hR : UsesRsp [.reg d] [.reg s]
  · exact Or.inr (.rsp _ _ _ hR)
  have hdR : d ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have hsR : s ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have gd := gpOk_of_isGpName hd hdR
  have gs := gpOk_of_isGpName hs hsR
  by_cases hk : UnaryOk opn
  · rcases hk with hc | rfl | ⟨b, k, hb, h0, h64, rfl⟩
    · exact Or.inl (Or.inl (.cast opn d s hc gd gs))
    · exact Or.inl (Or.inl (.shl0 d s gd gs))
    · exact Or.inl (Or.inl (.tagShift b k d s hb h0 h64 gd gs))
  · exact Or.inr (.unaryMnem d opn s ho hk)

/-- A load or store between resolving names is covered or in a gap family. -/
theorem covered_or_gap_memMov {body : Lcmd} {mn d s : String} (hm : x86MemMov mn = true) :
    Covered body (.Lopn [.reg d] mn [.reg s]) ∨ LegalGap body (.Lopn [.reg d] mn [.reg s]) := by
  by_cases hk : (mn = "LOAD:64" ∧ gpOk d = true ∧ CellOk s) ∨
      (mn = "STORE:64" ∧ CellOk d ∧ gpOk s = true)
  · rcases hk with ⟨rfl, gd, b, off, h1, h2, h3⟩ | ⟨rfl, ⟨b, off, h1, h2, h3⟩, gs⟩
    · exact Or.inl (Or.inl (.load d s b off h1 gd h2 h3))
    · exact Or.inl (Or.inl (.store d b off s h1 gs h2 h3))
  · exact Or.inr (.memMov d mn s hm hk)

/-- A register-indexed load or address computation is covered or in a gap family. -/
theorem covered_or_gap_sibLoad {body : Lcmd} {opn d b x : String} {sc : Nat}
    (ho : x86SibLoad opn x sc = true) (hd : isGpName d = true) (hb : isGpName b = true)
    (hx : isGpName x = true) :
    Covered body (.Lopn [.reg d] opn [.arrIdx b x sc]) ∨
      LegalGap body (.Lopn [.reg d] opn [.arrIdx b x sc]) := by
  by_cases hR : UsesRsp [.reg d] [.arrIdx b x sc]
  · exact Or.inr (.rsp _ _ _ hR)
  have hdR : d ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have hbR : b ≠ "RSP" := by rintro rfl; exact hR (Or.inr ⟨x, sc, Or.inl (by simp)⟩)
  have hxR : x ≠ "RSP" := by rintro rfl; exact hR (Or.inr ⟨b, sc, Or.inr (by simp)⟩)
  have gd := gpOk_of_isGpName hd hdR
  have gb := gpOk_of_isGpName hb hbR
  have gx := gpOk_of_isGpName hx hxR
  by_cases hl : opn = "LEA:64"
  · subst hl
    have hsc : sc ∈ [1, 2, 4, 8] := by
      simp only [x86SibLoad, x86SibScale, Bool.and_eq_true] at ho
      simpa using ho.1.1
    exact Or.inl (Or.inl (.leaIdx d b x sc gd gb gx hsc))
  by_cases hi : opn = "LOADIDX" ∧ sc = 8
  · obtain ⟨rfl, rfl⟩ := hi
    exact Or.inl (Or.inl (.loadIdx d b x gd gb gx))
  · exact Or.inr (.sibLoad d opn b x sc (by grind))

/-- A register-indexed store is covered or in a gap family. -/
theorem covered_or_gap_sibStore {body : Lcmd} {a : LOperand} {opn b x v : String} {sc : Nat}
    (hb : isGpName b = true) (hx : isGpName x = true) (hv : isGpName v = true) :
    Covered body (.Lopn [a] opn [.arrIdx b x sc, .reg v]) ∨
      LegalGap body (.Lopn [a] opn [.arrIdx b x sc, .reg v]) := by
  by_cases hR : UsesRsp [a] [.arrIdx b x sc, .reg v]
  · exact Or.inr (.rsp _ _ _ hR)
  have hbR : b ≠ "RSP" := by rintro rfl; exact hR (Or.inr ⟨x, sc, Or.inl (by simp)⟩)
  have hxR : x ≠ "RSP" := by rintro rfl; exact hR (Or.inr ⟨b, sc, Or.inr (by simp)⟩)
  have hvR : v ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  by_cases hk : opn = "STOREIDX" ∧ sc = 8 ∧ ∃ A, a = .reg A
  · obtain ⟨rfl, rfl, A, rfl⟩ := hk
    exact Or.inl (Or.inl (.storeIdx A b x v (gpOk_of_isGpName hb hbR) (gpOk_of_isGpName hx hxR)
      (gpOk_of_isGpName hv hvR)))
  · exact Or.inr (.sibStore a opn b x v sc hk)

/-- A constant-index stack-array store is covered or in a gap family. -/
theorem covered_or_gap_storeImm {body : Lcmd} {a : LOperand} {b v : String} {k : Nat}
    (hk : x86StoreImm k = true) (hb : isGpName b = true) (hv : isGpName v = true) :
    Covered body (.Lopn [a] "STOREIMM" [.reg b, .reg v, .imm k]) ∨
      LegalGap body (.Lopn [a] "STOREIMM" [.reg b, .reg v, .imm k]) := by
  by_cases hR : UsesRsp [a] [.reg b, .reg v, .imm k]
  · exact Or.inr (.rsp _ _ _ hR)
  have hbR : b ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have hvR : v ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  by_cases hD : ∃ D, a = .reg D ∧ gpOk D = true
  · obtain ⟨D, rfl, gD⟩ := hD
    exact Or.inl (Or.inl (.storeImm D b v k gD (gpOk_of_isGpName hb hbR)
      (gpOk_of_isGpName hv hvR) hk))
  · exact Or.inr (.storeImmDst a b v k hD)

/-- A stack-array zeroing from a base register is covered or names the stack register. -/
theorem covered_or_gap_zeroArrSrc {body : Lcmd} {b : String} {n w : Nat}
    (hz : x86ZeroArr n w = true) (hb : isGpName b = true) :
    Covered body (.Lopn [] "ZEROARR" [.reg b, .imm n, .imm w]) ∨
      LegalGap body (.Lopn [] "ZEROARR" [.reg b, .imm n, .imm w]) := by
  by_cases hR : b = "RSP"
  · exact Or.inr (.rsp _ _ _ (Or.inl (by simp [hR])))
  simp only [x86ZeroArr, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hz
  obtain ⟨⟨rfl, hn⟩, hk⟩ := hz
  exact Or.inl (Or.inl (.zeroArr b n (gpOk_of_isGpName hb hR) hn hk))

/-- A frame-array address load is covered or in a gap family. -/
theorem covered_or_gap_leaFa {body : Lcmd} {opn d q : String} (ho : x86LeaFa opn q = true)
    (hd : isGpName d = true) :
    Covered body (.Lopn [.reg d] opn [.reg q]) ∨ LegalGap body (.Lopn [.reg d] opn [.reg q]) := by
  by_cases hR : d = "RSP"
  · exact Or.inr (.rsp _ _ _ (Or.inl (by simp [hR])))
  simp only [x86LeaFa, Bool.and_eq_true, beq_iff_eq] at ho
  obtain ⟨rfl, hq⟩ := ho
  by_cases hdsp : dispOk32 (faOff q) = true
  · exact Or.inl (Or.inl (.leaFa d q (gpOk_of_isGpName hd hR) hq hdsp))
  · exact Or.inr (.leaFaFar d q (by simpa using hdsp))

/-- A three-source carry-chain addition is covered or in a gap family. -/
theorem covered_or_gap_carry3 {body : Lcmd} {opn d a s c : String} (ho : x86Carry3 opn = true)
    (hd : isGpName d = true) (ha : isGpName a = true) (hs : isGpName s = true)
    (hc : isGpName c = true) :
    Covered body (.Lopn [.reg d] opn [.reg a, .reg s, .reg c]) ∨
      LegalGap body (.Lopn [.reg d] opn [.reg a, .reg s, .reg c]) := by
  by_cases hR : UsesRsp [.reg d] [.reg a, .reg s, .reg c]
  · exact Or.inr (.rsp _ _ _ hR)
  have hdR : d ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have haR : a ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have hsR : s ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have hcR : c ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  by_cases hm : opn = "ADCX:64"
  · subst hm
    by_cases hw : a = c ∨ s = c
    · exact Or.inr (.carryInWord d _ a s c hw)
    by_cases hdst : a = d ∨ (d ≠ s ∧ d ≠ c)
    · exact Or.inl (Or.inl (.adcx d a s c (gpOk_of_isGpName hd hdR) (gpOk_of_isGpName ha haR)
        (gpOk_of_isGpName hs hsR) (gpOk_of_isGpName hc hcR) (by grind) (by grind) hdst))
    · exact Or.inr (.carryDst d a s c (by grind) (by grind))
  · exact Or.inr (.carryMnem d opn a s c ho hm)

/-- A flag materialisation into an encoder register is covered or in a gap family. -/
theorem covered_or_gap_flagOut {body : Lcmd} {opn d : String} {ss : List LOperand}
    (ho : x86FlagOut opn ss = true) (hd : isGpName d = true) :
    Covered body (.Lopn [.reg d] opn ss) ∨ LegalGap body (.Lopn [.reg d] opn ss) := by
  by_cases hR : d = "RSP"
  · exact Or.inr (.rsp _ _ _ (Or.inl (by simp [hR])))
  by_cases hm : opn = "ADCXHI:64"
  · subst hm
    by_cases har : ∃ a s c, ss = [.reg a, .reg s, .reg c]
    · obtain ⟨a, s, c, rfl⟩ := har
      by_cases hw : a = c ∨ s = c
      · exact Or.inr (.carryInWord d _ a s c hw)
      by_cases hk : kOk (Params.ofBody body) a = true ∧ kOk (Params.ofBody body) s = true ∧
          kOk (Params.ofBody body) c = true
      · exact Or.inl (Or.inl (.adcxhi d a s c (gpOk_of_isGpName hd hR) hk.1 hk.2.1 hk.2.2
          (by grind) (by grind)))
      · exact Or.inr (.flagSlotSrc d a s c (by grind))
    · exact Or.inr (.flagArity d ss har)
  · exact Or.inr (.flagMnem d opn ss ho hm)

/-- A widening multiplication into encoder registers is covered or in a gap family. -/
theorem covered_or_gap_wideMul {body : Lcmd} {opn l h s : String} (ho : x86WideMul opn = true)
    (hl : isGpName l = true) (hh : isGpName h = true) (hs : isGpName s = true) :
    Covered body (.Lopn [.reg l, .reg h] opn [.reg s]) ∨
      LegalGap body (.Lopn [.reg l, .reg h] opn [.reg s]) := by
  by_cases hR : UsesRsp [.reg l, .reg h] [.reg s]
  · exact Or.inr (.rsp _ _ _ hR)
  have hlR : l ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have hhR : h ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  have hsR : s ≠ "RSP" := by rintro rfl; exact hR (by simp [UsesRsp])
  by_cases hm : opn = "MULX"
  · subst hm
    exact Or.inl (Or.inl (.mulx l h s (gpOk_of_isGpName hl hlR) (gpOk_of_isGpName hh hhR)
      (gpOk_of_isGpName hs hsR)))
  · exact Or.inr (.mulxMnem l h opn s ho hm)

/-- An instruction the encoder accepts whatever its operands is covered or in a gap family. -/
theorem covered_or_gap_fixed {body : Lcmd} {i : LinstrR} (h : x86Fixed i = true) :
    Covered body i ∨ LegalGap body i := by
  cases i with
  | Lopn ds opn ss =>
    by_cases hmh : isMulHiBinding opn = true
    · exact Or.inr (.mulHi ds opn ss hmh)
    by_cases hdir : opn ∈ ["FRAME", "FRAMEADD", "KEEP"]
    · exact Or.inr (.directive ds opn ss hdir)
    have hid : ∃ d, ds = [.reg d] ∧ ss = [.reg d] ∧ isGpName d = true ∧
        isIdentityTagShift opn = true := by
      simp only [x86Fixed, carriesNoBytes] at h
      split at h <;> grind
    obtain ⟨d, rfl, rfl, hd, hi⟩ := hid
    by_cases hR : d = "RSP"
    · exact Or.inr (.rsp _ _ _ (Or.inl (by simp [hR])))
    by_cases h0 : opn = "SHL:0:64"
    · subst h0
      exact Or.inl (Or.inl (.shl0 d d (gpOk_of_isGpName hd hR) (gpOk_of_isGpName hd hR)))
    · exact Or.inr (.identityShift d opn hi h0)
  | Lcond cnd l =>
    cases cnd with
    | reg cc =>
      by_cases hc : (condPol cc).isSome = true ∧ (labelAt body l).isSome = true
      · exact Or.inl (Or.inl (.cond cc l hc.1 hc.2))
      · exact Or.inr (.condOut cc l (by grind))
    | _ => simp [x86Fixed, carriesNoBytes] at h
  | Llabel k l => exact Or.inl (Or.inl (.label k l))
  | Lgoto t => exact Or.inr (.transfer _ (Or.inl ⟨t, rfl⟩))
  | Lcall ra t => exact Or.inr (.transfer _ (Or.inr (Or.inl ⟨ra, t, rfl⟩)))
  | Lret => exact Or.inr (.transfer _ (Or.inr (Or.inr (Or.inl rfl))))
  | Lalign => exact Or.inr (.transfer _ (Or.inr (Or.inr (Or.inr rfl))))
  | _ => simp [x86Fixed, carriesNoBytes] at h

/-! ## 6. The legal forms and the lowering -/

/-- **A legal form in the context of a body is covered in it or lies in a gap family.** The
    context is the frame size, the spill width and the save block of `Params.ofBody body`,
    which are those of `x86Enc.ctx body`. -/
theorem covered_or_gap_of_legalForm {body : Lcmd} {i : LinstrR}
    (h : LowerLegal.LF (Params.ofBody body).frame (Params.ofBody body).spillW
      (Params.ofBody body).qsaveB i) :
    Covered body i ∨ LegalGap body i := by
  cases h with
  | mov mn d s hm hd hs hds => exact covered_or_gap_mov hm hd hs hds
  | select m opn dn cn tn fn _ _ h1 h2 h3 h4 => exact covered_or_gap_select h1 h2 h3 h4
  | setcc opn dn an sn _ h1 h2 h3 => exact covered_or_gap_setcc h1 h2 h3
  | setccImm opn dn an v _ h1 h2 => exact covered_or_gap_setccImm h1 h2
  | movImmReg mn dn v hm h1 => exact covered_or_gap_movImmReg hm h1
  | movImmSlot mn dn v _ hs _ => exact covered_or_gap_movImmSlot hs
  | alu opn dn sn ho h1 h2 => exact covered_or_gap_alu ho h1 h2
  | aluImm opn dn v ho h1 => exact covered_or_gap_aluImm ho h1
  | shiftReg opn dn an sn ho h1 h2 h3 => exact covered_or_gap_shiftReg ho h1 h2 h3
  | andn opn dn an sn ho _ _ _ => exact Or.inr (.andn dn opn an sn ho)
  | unary opn dn sn ho h1 h2 => exact covered_or_gap_unary ho h1 h2
  | memMov mn d s hm _ _ _ => exact covered_or_gap_memMov hm
  | sibLoad opn dn bn xn sc ho h1 h2 h3 => exact covered_or_gap_sibLoad ho h1 h2 h3
  | sibStore a opn bn xn vn sc _ h1 h2 h3 => exact covered_or_gap_sibStore h1 h2 h3
  | storeImm a bn vn k hk h1 h2 => exact covered_or_gap_storeImm hk h1 h2
  | zeroArr dn n w _ _ => exact Or.inr (.zeroArrDst dn n w)
  | zeroArrSrc bn n w hz h1 => exact covered_or_gap_zeroArrSrc hz h1
  | leaFa opn dn q ho h1 => exact covered_or_gap_leaFa ho h1
  | carry3 opn dn an sn kn ho h1 h2 h3 h4 => exact covered_or_gap_carry3 ho h1 h2 h3 h4
  | flagOut opn dn srcs ho h1 => exact covered_or_gap_flagOut ho h1
  | wideMul opn ln hn sn ho h1 h2 h3 => exact covered_or_gap_wideMul ho h1 h2 h3
  | fixed i hi => exact covered_or_gap_fixed hi

open LowerLegal (PosOk lower_legal) in
/-- **The lowering emits covered instructions or instructions of a gap family**: under the
    hypotheses of `LowerLegal.lower_legal` at the frame size, spill width and save block of a
    body `out`, every instruction of one position of `physPositionEmit` is covered in `out` or
    lies in a family of `LegalGap out`. -/
theorem covered_or_gap_lower (out : Lcmd) (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String) (outStoreMap : OutStoreMap)
    (storeBase : String) (abiW : Nat) (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (reservedVec : List Nat)
    (i : Linstr) (virtIdx : Nat) (rm : LOperand → LOperand)
    (hrm : rm =
      let tbl := straightCallComposeTable body (physTableOut body outStoreMap reservedVec)
      if bodyHasCall body then remapOperandCalleeSave body tbl else remapOperand body tbl)
    (habi : abiW ≠ 8 ∧ abiW ≠ 16 ∧ abiW ≠ 256)
    (hargs : ∀ s, AllocOp (Params.ofBody out).frame (Params.ofBody out).spillW
      (Params.ofBody out).qsaveB (.reg (physNameForBody body
        (straightCallComposeTable body (physTableOut body outStoreMap reservedVec))
        (argName s))))
    (hsave : ∀ base, OpResolves (Params.ofBody out).frame (Params.ofBody out).spillW
      (Params.ofBody out).qsaveB (abiLoadSave base))
    (hrdi : OpResolves (Params.ofBody out).frame (Params.ofBody out).spillW
      (Params.ofBody out).qsaveB abiSaveRdiName)
    (hmbr : ∀ b q, memrefBaseReload b = some q → OpResolves (Params.ofBody out).frame
      (Params.ofBody out).spillW (Params.ofBody out).qsaveB q)
    (hloadBase : isGpName loadBase = true) (hstoreBase : isGpName storeBase = true)
    (hcall : ∀ p ∈ callArgBaseReload, isGpName p.1 = true ∧ OpResolves (Params.ofBody out).frame
      (Params.ofBody out).spillW (Params.ofBody out).qsaveB p.2)
    (hout : ∀ d tl opn srcs, i.li_i = .Lopn (d :: tl) opn srcs →
      outStoreOffs outStoreMap d ≠ [] → AllocOp (Params.ofBody out).frame
        (Params.ofBody out).spillW (Params.ofBody out).qsaveB (rm d))
    (hpos : PosOk (Params.ofBody out).frame (Params.ofBody out).spillW
      (Params.ofBody out).qsaveB rm shiftImm i.li_i) :
    ∀ r ∈ physPositionEmit shiftImm body inLoadMap loadBase outStoreMap storeBase abiW
      memrefBaseReload callArgBaseReload reservedVec (i, virtIdx),
      Covered out r.li_i ∨ LegalGap out r.li_i := fun r hr =>
  covered_or_gap_of_legalForm (lower_legal shiftImm body inLoadMap loadBase outStoreMap
    storeBase abiW memrefBaseReload callArgBaseReload reservedVec i virtIdx rm hrm habi hargs
    hsave hrdi hmbr hloadBase hstoreBase hcall hout hpos r hr)

end CatCrypt.Crypto.SecureCompilation.X86Backend.PrintedCoveredLower
