/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsaStackFrame
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG

@[expose] public section

set_option autoImplicit false

/-!
# The image of a covered printed body names no stack pointer

The procedure specification of a body placed after a label and followed by a return
(`IsaCall`, over `spFreeBodyB`) asks two Boolean conditions of the body: no instruction is a
call or a return, and no instruction names the stack pointer `RSP`. This module derives both
for the image `virtImg slotArr body` of a covered printed body, from the class of covered
printed bodies `printedAddrB`, the image class `physImgB` and a condition on the array names
of the slot map.

The class `printedAddrB` admits, before the closing return, labels, branches on the
condition codes `Z` and `NZ`, and `Lopn`s read into an arm of `classifyA` whose conditions
hold; each arm requires every operand name to be a general-purpose name accepted by `gpOk`,
which excludes `RSP`, or a frame-slot name `k.N` or `qsave.R`, with one exception: the
destination of an indexed store, which names the array and is no machine operand. The class
of the image `physImgB` makes every indexed store resolve to an array, so the image replaces
that destination by the name of the array. The array names of the slot map of a layout are
argument names `a<j>`, renamed for a loop by the renaming `synthRen` computes, every target
of which is a name that an instruction of the image reads.

The class `printedAddrWB` of printed bodies with carry chains admits, besides the arms of
`classifyA`, casts, immediate moves, carry arms and selects on general-purpose names and
frame-slot names, materialised comparisons and register-count shifts on general-purpose
names, and cell accesses whose base is a general-purpose name. A cell name
`mem.<A>.<off>` is read with the characters of `A` before its first dot as its base, so the
cell name of `A` is a cell name of the base `RSP` only if `A` begins with `RSP`. The
predicate `rspFreeNameB`, a name that does not begin with `RSP` and is no cell name of the
base `RSP`, therefore holds of general-purpose names, frame-slot names, condition codes,
argument names and cell names of a general-purpose base, and of the cell name of every name
of which it holds.

## Main results

* `stackNameB`, `stackFreeB`: a name that is `RSP` or a cell name of the base `RSP`, and an
  instruction none of whose operand names is one.
* `rspFreeNameB`, `rspFreeB`, `RspFreeUpToStore`: a name that does not begin with `RSP` and
  is no cell name of the base `RSP`; an instruction all of whose operand names are such
  names; and that condition up to the destination of an indexed store.
* `rspFreeNameB_memName`: the cell name of a name that passes `rspFreeNameB` passes it.
* `rspFree_of_armOk`, `rspFree_of_instrOKWB`: an instruction of the covered fragment, and of
  the covered fragment with carry chains, passes `RspFreeUpToStore`.
* `stackFreeB_of_instrOKB`: an instruction of the covered fragment names no stack name, or
  is an indexed store whose base, index and value do not.
* `virtImg_stackFree`, `virtImg_spFreeBodyB`, `virtImg_noCall`: the image of a covered
  printed body in the image class, at a slot map whose array names are no stack names, names
  `RSP` in no instruction and contains no call and no return.
* `synthRen_target_mem`: every target of the synthesised renaming is a name that an
  instruction of the image reads.
* `stackNameB_slotArrOf`, `stackNameB_slotRen_synthRen`: no array name of the slot map of a
  layout, and of that slot map renamed by the synthesised renaming, is a stack name.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieUncond (decodeArrM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRenameLoop (renOf)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage (virtImg imgInstr accArr
  physImgB accOkB bitStore? bitStore?_spec virtImg_getElem? cellIdxStore? cellIdxStore?_spec
  arrImmImg arrImmImg_lopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (normA condPol)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr (srcNames cellBase)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (cellParts? slotMov?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (isCall)
open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCall
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertLoop
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf resolveVar_top)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrRoute
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (straightArrB chainAlias
  straightRegB straightRouteB straightRouteOutB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim (physImgB_at accArr_spec
  imgInstr_stx)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted (gpOk gpList mem_gpList Arm
  classify classify_instr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (AArm classifyA
  classifyA_instr cellParts?_gp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW (notSlot_of_cell
  instrOKWB printedAddrWB classifyK classifyK_spec castOk imm32Ok classifyS classifyS_instr
  SArm classifyC classifyC_instr CArm classifyM classifyM_instr MArm classifyI classifyI_instr
  iOk classifyL classifyL_instr lOk classifyV classifyV_instr vOk vtOk vfOk kOk classifyE
  classifyE_instr eOk eInstr classifyX classifyX_instr xOk xInstr classifyEI classifyEI_instr
  eiOk eiInstr classifyR classifyR_instr rOk rInstr)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (printedAddrB instrOKB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (isSpillOrQsave spillQsaveOff)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (movImmStruct? movImmStruct?_spec)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCells (cellBody cellMove
  cellBody_getElem? cellBody_length cellA_ld cellA_st hasPrefix_memName hasPrefix_of_cellParts)

/-! ## 1. Stack names -/

/-- The name `r` is the stack pointer `RSP` or a cell name `mem.RSP.<off>`. -/
def stackNameB (r : String) : Bool := opSpB "RSP" (.reg r)

/-- The names of the operands of an instruction: the names of the destination and source
    operands of an `Lopn` and of the operand of a conditional jump. -/
def operandNames : LinstrR → List String
  | .Lopn ds _ ss => (ds ++ ss).flatMap srcNames
  | .Lcond c _ => srcNames c
  | _ => []

/-- No operand name of the instruction is a stack name. -/
def stackFreeB (i : LinstrR) : Bool := (operandNames i).all fun r => !stackNameB r

/-- A name that is no stack name is not `RSP`. -/
theorem ne_rsp_of_stackNameB {r : String} (h : stackNameB r = false) : r ≠ "RSP" := by
  rintro rfl
  simp [stackNameB, opSpB] at h

/-- An instruction none of whose operand names is a stack name passes the check `spFreeB`
    of the stack pointer. -/
theorem spFreeB_of_stackFreeB {i : LinstrR} (h : stackFreeB i = true) :
    spFreeB "RSP" i = true := by
  have hn : ∀ r ∈ operandNames i, stackNameB r = false := by
    simpa [stackFreeB] using h
  have hop : ∀ x : LOperand, (∀ r ∈ srcNames x, stackNameB r = false) →
      opSpB "RSP" x = false := by
    intro x hx
    cases x with
    | reg r => exact hx r (by simp [srcNames])
    | imm _ => rfl
    | arr b _ => simpa [opSpB] using ne_rsp_of_stackNameB (hx b (by simp [srcNames]))
    | arrIdx b j _ =>
        simpa [opSpB] using And.intro (ne_rsp_of_stackNameB (hx b (by simp [srcNames])))
          (ne_rsp_of_stackNameB (hx j (by simp [srcNames])))
  cases i with
  | Lopn ds o ss =>
      simp only [spFreeB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        List.any_eq_false]
      refine ⟨by decide, fun x hx => by
        simpa using hop x fun r hr => hn r (List.mem_flatMap.mpr ⟨x, hx, hr⟩)⟩
  | Lcond c l =>
      simp only [spFreeB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
      exact ⟨by decide, hop c fun r hr => hn r hr⟩
  | _ => rfl

/-- A general-purpose name is no stack name. -/
theorem stackNameB_gp {r : String} (h : gpOk r = true) : stackNameB r = false := by
  have hc := cellParts?_gp h
  have hm := mem_gpList h
  have hne : r ≠ "RSP" := by
    rintro rfl
    simp [gpList] at hm
  simp [stackNameB, opSpB, cellBase, hc, hne]

/-- A frame-slot name `k.N` or `qsave.R` is no stack name. -/
theorem stackNameB_slot {r : String} (h : isSpillOrQsave r = true) : stackNameB r = false := by
  have hc : cellParts? r = none := by
    cases hp : cellParts? r with
    | none => rfl
    | some p => rw [(notSlot_of_cell hp).1] at h; cases h
  have hne : r ≠ "RSP" := by
    rintro rfl
    revert h
    decide
  simp [stackNameB, opSpB, cellBase, hc, hne]

/-- A name with a frame offset is no stack name. -/
theorem stackNameB_frame {F W : Nat} {r : String} {qB : Nat}
    (h : (spillQsaveOff F W r qB).isSome = true) : stackNameB r = false := by
  refine stackNameB_slot ?_
  unfold spillQsaveOff at h
  unfold isSpillOrQsave
  split_ifs at h with h1 h2
  · simp [h1]
  · simp [h2]
  · cases h

/-- An argument name `a<j>` is no stack name. -/
theorem stackNameB_argName (j : Nat) : stackNameB (argName j) = false := by
  have hh := JasminLsemExportTransfer.head?_argName j
  have hc : cellParts? (argName j) = none := by
    cases hp : cellParts? (argName j) with
    | none => rfl
    | some p =>
        have hm := X86Backend.ImageAddrCells.hasPrefix_of_cellParts hp
        unfold hasPrefix at hm
        rw [List.isPrefixOf_iff_prefix] at hm
        obtain ⟨t, ht⟩ := hm
        rw [← ht] at hh
        simp at hh
  have hne : argName j ≠ "RSP" := by
    intro he
    rw [he] at hh
    simp at hh
  simp [stackNameB, opSpB, cellBase, hc, hne]

/-- The operand names of the widening multiply read at its width are those of the
    instruction. -/
theorem operandNames_normA (x : LinstrR) : operandNames (normA x) = operandNames x := by
  cases x <;> rfl

/-! ## 2. Names that do not begin with the stack pointer -/

/-- The name `r` does not begin with `RSP` and is no cell name of the base `RSP`. The cell
    name `memName A off` of a name `A` that passes is a name that passes. -/
def rspFreeNameB (r : String) : Bool :=
  !hasPrefix r "RSP" && !(cellBase (.reg r) == some "RSP")

/-- Every operand name of the instruction passes `rspFreeNameB`. -/
def rspFreeB (i : LinstrR) : Bool := (operandNames i).all rspFreeNameB

/-- The instruction `x` passes `rspFreeB`, or is an indexed store whose base, index and
    value pass `rspFreeNameB`; the destination of an indexed store names the array and is
    not constrained. -/
def RspFreeUpToStore (x : LinstrR) : Prop :=
  rspFreeB x = true ∨ ∃ d b i v, x = .Lopn [.reg d] "STOREIDX" [.arrIdx b i 8, .reg v]
    ∧ rspFreeNameB b = true ∧ rspFreeNameB i = true ∧ rspFreeNameB v = true

/-- A name that passes `rspFreeNameB` is no stack name. -/
theorem stackNameB_of_rspFreeNameB {r : String} (h : rspFreeNameB r = true) :
    stackNameB r = false := by
  simp only [rspFreeNameB, Bool.and_eq_true, Bool.not_eq_true'] at h
  have hne : r ≠ "RSP" := by
    rintro rfl
    exact absurd h.1 (by decide)
  simp [stackNameB, opSpB, hne, h.2]

/-- An instruction that passes `rspFreeB` names no stack name. -/
theorem stackFreeB_of_rspFreeB {i : LinstrR} (h : rspFreeB i = true) : stackFreeB i = true := by
  simp only [rspFreeB, stackFreeB, List.all_eq_true] at h ⊢
  intro r hr
  simp [stackNameB_of_rspFreeNameB (h r hr)]

/-- A name with the prefix `p` has the first character of `p`. -/
theorem head?_of_hasPrefix {r p : String} {c : Char} (h : hasPrefix r p = true)
    (hc : p.toList.head? = some c) : r.toList.head? = some c := by
  unfold hasPrefix at h
  rw [List.isPrefixOf_iff_prefix] at h
  obtain ⟨t, ht⟩ := h
  rw [← ht]
  cases hp : p.toList with
  | nil => rw [hp] at hc; cases hc
  | cons a u => rw [hp] at hc; simpa using hc

/-- A name whose first character is not `R` does not begin with `RSP`. -/
theorem hasPrefix_rsp_of_head {r : String} {c : Char} (hh : r.toList.head? = some c)
    (hc : c ≠ 'R') : hasPrefix r "RSP" = false := by
  cases h : hasPrefix r "RSP" with
  | false => rfl
  | true =>
      have := head?_of_hasPrefix (c := 'R') h (by simp)
      rw [hh] at this
      exact absurd (Option.some.inj this) hc

/-- A name whose first character is not `m` is no cell name. -/
theorem cellParts?_of_head {r : String} {c : Char} (hh : r.toList.head? = some c)
    (hc : c ≠ 'm') : cellParts? r = none := by
  cases h : cellParts? r with
  | none => rfl
  | some p =>
      have := head?_of_hasPrefix (c := 'm') (hasPrefix_of_cellParts h) (by simp)
      rw [hh] at this
      exact absurd (Option.some.inj this) hc

/-- A name whose first character is neither `R` nor `m` passes `rspFreeNameB`. -/
theorem rspFreeNameB_of_head {r : String} {c : Char} (hh : r.toList.head? = some c)
    (hR : c ≠ 'R') (hm : c ≠ 'm') : rspFreeNameB r = true := by
  simp [rspFreeNameB, cellBase, hasPrefix_rsp_of_head hh hR, cellParts?_of_head hh hm]

/-- A general-purpose name passes `rspFreeNameB`. -/
theorem rspFreeNameB_gp {r : String} (h : gpOk r = true) : rspFreeNameB r = true := by
  have hc := cellParts?_gp h
  have hm := mem_gpList h
  have hp : hasPrefix r "RSP" = false := by
    simp only [gpList, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> decide
  simp [rspFreeNameB, cellBase, hc, hp]

/-- A frame-slot name `k.N` or `qsave.R` passes `rspFreeNameB`. -/
theorem rspFreeNameB_slot {r : String} (h : isSpillOrQsave r = true) :
    rspFreeNameB r = true := by
  unfold isSpillOrQsave at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact rspFreeNameB_of_head (head?_of_hasPrefix (c := 'k') h (by simp)) (by decide)
      (by decide)
  · exact rspFreeNameB_of_head (head?_of_hasPrefix (c := 'q') h (by simp)) (by decide)
      (by decide)

/-- A name with a frame offset passes `rspFreeNameB`. -/
theorem rspFreeNameB_frame {F W : Nat} {r : String} {qB : Nat}
    (h : (spillQsaveOff F W r qB).isSome = true) : rspFreeNameB r = true := by
  refine rspFreeNameB_slot ?_
  unfold spillQsaveOff at h
  unfold isSpillOrQsave
  split_ifs at h with h1 h2
  · simp [h1]
  · simp [h2]
  · cases h

/-- An operand of a carry arm, a general-purpose name or a frame slot, passes
    `rspFreeNameB`. -/
theorem rspFreeNameB_kOk {P : X86Backend.LprogBytesDecode.Params} {x : String}
    (h : kOk P x = true) : rspFreeNameB x = true := by
  unfold kOk at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨h, -⟩
  · exact rspFreeNameB_gp h
  · exact rspFreeNameB_slot h

/-- An argument name `a<j>` passes `rspFreeNameB`. -/
theorem rspFreeNameB_argName (j : Nat) : rspFreeNameB (argName j) = true :=
  rspFreeNameB_of_head (JasminLsemExportTransfer.head?_argName j) (by decide) (by decide)

/-- A cell name of a general-purpose base passes `rspFreeNameB`. -/
theorem rspFreeNameB_cell {n B : String} {off : Nat} (h : cellParts? n = some (B, off))
    (hB : gpOk B = true) : rspFreeNameB n = true := by
  have hp := hasPrefix_rsp_of_head (head?_of_hasPrefix (c := 'm') (hasPrefix_of_cellParts h)
    (by simp)) (by decide)
  have hne : B ≠ "RSP" := by
    rintro rfl
    have hm := mem_gpList hB
    simp [gpList] at hm
  simp [rspFreeNameB, cellBase, h, hp, hne]

/-- The characters of a cell name before its first dot are not `RSP` when the characters
    `a` of the base do not begin with `RSP`. -/
theorem takeWhile_ne_rsp {a rest : List Char}
    (ha : List.isPrefixOf ['R', 'S', 'P'] a = false) :
    (a ++ '.' :: rest).takeWhile (· != '.') ≠ ['R', 'S', 'P'] := by
  intro h
  have hpre : ['R', 'S', 'P'] <+: a ++ '.' :: rest := by
    rw [← h]
    exact List.takeWhile_prefix _
  obtain ⟨u, hu⟩ := hpre
  rcases a with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at hu
  · simp at hu
  · simp at hu
  · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hu
    obtain ⟨rfl, rfl, rfl, -⟩ := hu
    simp [List.isPrefixOf] at ha

/-- **The cell name of a name that passes `rspFreeNameB` passes `rspFreeNameB`**: the name
    `memName A off` begins with `mem.`, and its base, the characters of `A` before the first
    dot, is `RSP` only if `A` begins with `RSP`. -/
theorem rspFreeNameB_memName {A : String} (hA : rspFreeNameB A = true) (off : Nat) :
    rspFreeNameB (memName A off) = true := by
  simp only [rspFreeNameB, Bool.and_eq_true, Bool.not_eq_true'] at hA
  have hp := hasPrefix_rsp_of_head (head?_of_hasPrefix (c := 'm') (hasPrefix_memName A off)
    (by simp)) (by decide)
  have hb : cellBase (.reg (memName A off)) ≠ some "RSP" := by
    intro hb
    simp only [cellBase, cellParts?, hasPrefix_memName, ite_true] at hb
    have hd : (memName A off).toList.drop 4 = A.toList ++ '.' :: (toString off).toList := by
      simp [memName]
    rw [hd, List.span_eq_takeWhile_dropWhile] at hb
    have ha : List.isPrefixOf ['R', 'S', 'P'] A.toList = false := hA.1
    have ht := takeWhile_ne_rsp (rest := (toString off).toList) ha
    split at hb
    · rename_i base off' he
      simp only [Prod.mk.injEq] at he
      rw [Option.map_map] at hb
      obtain ⟨o, -, ho⟩ := Option.map_eq_some_iff.mp hb
      have hbase : base = ['R', 'S', 'P'] := by
        have := congrArg String.toList ho
        simpa using this
      exact ht (he.1.trans hbase)
    · cases hb
  simp [rspFreeNameB, hp, hb]

/-! ## 3. The covered fragment -/

/-- A condition code with a polarity is no stack name. -/
theorem stackNameB_condPol {cc : String} (h : (condPol cc).isSome = true) :
    stackNameB cc = false := by
  unfold condPol at h
  split at h
  · decide
  · decide
  · cases h

/-- A condition code with a polarity passes `rspFreeNameB`. -/
theorem rspFreeNameB_condPol {cc : String} (h : (condPol cc).isSome = true) :
    rspFreeNameB cc = true := by
  unfold condPol at h
  split at h
  · decide
  · decide
  · cases h

/-- **An instruction read into an arm of `classifyA` whose conditions hold passes
    `RspFreeUpToStore`**: every operand name is a general-purpose name or a frame-slot name,
    except the destination of an indexed store. -/
theorem rspFree_of_armOk {P : X86Backend.LprogBytesDecode.Params} {x : LinstrR} {a : AArm}
    (hc : classifyA x = some a) (h : a.ok P = true) : RspFreeUpToStore x := by
  unfold RspFreeUpToStore
  rw [← classifyA_instr hc]
  cases a with
  | reg a =>
      simp only [AArm.ok, Bool.and_eq_true] at h
      obtain ⟨⟨hr, hok⟩, -⟩ := h
      left
      cases a with
      | movRR m D S =>
          simp only [Arm.ok, Bool.and_eq_true] at hok
          simp [rspFreeB, operandNames, srcNames, AArm.instr, Arm.instr,
            rspFreeNameB_gp hok.1.2, rspFreeNameB_gp hok.2]
      | movRI D v =>
          simp only [Arm.ok, Bool.and_eq_true] at hok
          simp [rspFreeB, operandNames, srcNames, AArm.instr, Arm.instr,
            rspFreeNameB_gp hok.1.1]
      | store m q S => exact absurd hr (by simp [X86Backend.DecodePrintedAddr.regArmB])
      | load m D q => exact absurd hr (by simp [X86Backend.DecodePrintedAddr.regArmB])
      | alu m D S =>
          simp only [Arm.ok, Bool.and_eq_true] at hok
          simp [rspFreeB, operandNames, srcNames, AArm.instr, Arm.instr,
            rspFreeNameB_gp hok.1.2, rspFreeNameB_gp hok.2]
      | aluI m D v =>
          simp only [Arm.ok, Bool.and_eq_true] at hok
          simp [rspFreeB, operandNames, srcNames, AArm.instr, Arm.instr,
            rspFreeNameB_gp hok.1.2]
      | shr m D S =>
          simp only [Arm.ok, Bool.and_eq_true] at hok
          have hg := hok.1.1.1.1.1.1.1.1.1
          simp [rspFreeB, operandNames, srcNames, AArm.instr, Arm.instr,
            rspFreeNameB_gp hg.1, rspFreeNameB_gp hg.2]
      | shl0 m D S =>
          simp only [Arm.ok, Bool.and_eq_true] at hok
          have hg := hok.1.1.1.1.1.1.1.1
          simp [rspFreeB, operandNames, srcNames, AArm.instr, Arm.instr,
            rspFreeNameB_gp hg.1, rspFreeNameB_gp hg.2]
      | shI m D k =>
          simp only [Arm.ok, Bool.and_eq_true] at hok
          simp [rspFreeB, operandNames, srcNames, AArm.instr, Arm.instr,
            rspFreeNameB_gp hok.1.1.2]
      | lea D B X sc =>
          simp only [Arm.ok, Bool.and_eq_true] at hok
          simp [rspFreeB, operandNames, srcNames, AArm.instr, Arm.instr,
            rspFreeNameB_gp hok.1.1.1.1, rspFreeNameB_gp hok.1.1.1.2,
            rspFreeNameB_gp hok.1.1.2]
  | st m q S =>
      simp only [AArm.ok, Bool.and_eq_true] at h
      left
      simp [rspFreeB, operandNames, srcNames, AArm.instr, rspFreeNameB_gp h.1.1.1.1,
        rspFreeNameB_frame h.1.1.2]
  | ld m D q =>
      simp only [AArm.ok, Bool.and_eq_true] at h
      left
      simp [rspFreeB, operandNames, srcNames, AArm.instr,
        rspFreeNameB_gp h.1.1.1.1.1, rspFreeNameB_frame h.1.1.1.2]
  | cmpR c r =>
      simp only [AArm.ok, Bool.and_eq_true] at h
      left
      simp [rspFreeB, operandNames, srcNames, AArm.instr, rspFreeNameB_gp h.1,
        rspFreeNameB_gp h.2]
  | cmpI c k =>
      simp only [AArm.ok, Bool.and_eq_true] at h
      left
      simp [rspFreeB, operandNames, srcNames, AArm.instr, rspFreeNameB_gp h.1]
  | cmpM c q =>
      simp only [AArm.ok, Bool.and_eq_true] at h
      left
      simp [rspFreeB, operandNames, srcNames, AArm.instr,
        rspFreeNameB_gp h.1.1.1.1.1, rspFreeNameB_slot h.1.1.1.2]
  | ldx D B I =>
      simp only [AArm.ok, Bool.and_eq_true] at h
      left
      simp [rspFreeB, operandNames, srcNames, AArm.instr,
        rspFreeNameB_gp h.1.1.1, rspFreeNameB_gp h.1.1.2, rspFreeNameB_gp h.1.2]
  | stx d B I V =>
      simp only [AArm.ok, Bool.and_eq_true] at h
      exact Or.inr ⟨d, B, I, V, rfl, rspFreeNameB_gp h.1.1.1,
        rspFreeNameB_gp h.1.1.2, rspFreeNameB_gp h.1.2⟩
  | mul D S =>
      simp only [AArm.ok, Bool.and_eq_true] at h
      left
      simp [rspFreeB, operandNames, srcNames, AArm.instr, rspFreeNameB_gp h.1,
        rspFreeNameB_gp h.2]
  | mulxS H S =>
      simp only [AArm.ok, Bool.and_eq_true] at h
      left
      simp [rspFreeB, operandNames, srcNames, AArm.instr, rspFreeNameB_gp h.1,
        rspFreeNameB_gp h.2]
  | mulx L H S =>
      simp only [AArm.ok, Bool.and_eq_true] at h
      left
      simp [rspFreeB, operandNames, srcNames, AArm.instr, rspFreeNameB_gp h.1.1.1,
        rspFreeNameB_gp h.1.1.2, rspFreeNameB_gp h.1.2]
  | zero B n =>
      simp only [AArm.ok, Bool.and_eq_true] at h
      left
      simp [rspFreeB, operandNames, srcNames, AArm.instr, rspFreeNameB_gp h.1.1]
  | simm d B V k =>
      simp only [AArm.ok, Bool.and_eq_true] at h
      left
      simp [rspFreeB, operandNames, srcNames, AArm.instr, rspFreeNameB_gp h.1.1.1,
        rspFreeNameB_gp h.1.1.2, rspFreeNameB_gp h.2]

/-- **An instruction of the covered fragment with carry chains passes `RspFreeUpToStore`**:
    every operand name is a general-purpose name, a frame-slot name, a condition code or a
    cell name of a general-purpose base, except the destination of an indexed store. -/
theorem rspFree_of_instrOKWB {body : Lcmd} {P : X86Backend.LprogBytesDecode.Params}
    {x : LinstrR} (h : instrOKWB body P x = true) : RspFreeUpToStore x := by
  cases x with
  | Lopn ds o ss =>
      simp only [instrOKWB] at h
      split at h
      · rename_i d a m w hk
        obtain ⟨o', he, -, -⟩ := classifyK_spec hk
        simp only [castOk, Bool.and_eq_true] at h
        rw [he]
        left
        simp [rspFreeB, operandNames, srcNames, rspFreeNameB_gp h.1, rspFreeNameB_gp h.2]
      split at h
      · rename_i d n hm
        simp only [imm32Ok, Bool.and_eq_true] at h
        obtain ⟨_, he⟩ := movImmStruct?_spec hm
        rw [he]
        left
        simp [rspFreeB, operandNames, srcNames, rspFreeNameB_gp h.1]
      split at h
      · rename_i c hs
        rw [← classifyS_instr hs]
        left
        cases c <;> simp only [SArm.ok, Bool.and_eq_true] at h <;>
          simp [rspFreeB, operandNames, srcNames, SArm.instr]
        · exact ⟨rspFreeNameB_kOk h.1.1.1.1.2, rspFreeNameB_kOk h.1.1.1.2,
            rspFreeNameB_kOk h.1.1.2, rspFreeNameB_gp h.1.1.1.1.1.1.1⟩
        · exact ⟨rspFreeNameB_gp h.1.1.1.1.1.1, rspFreeNameB_kOk h.1.1.2,
            rspFreeNameB_kOk h.1.2, rspFreeNameB_kOk h.1.1.1.1.1.2⟩
        · exact ⟨rspFreeNameB_kOk h.1.1.1.2, rspFreeNameB_kOk h.1.1.2,
            rspFreeNameB_kOk h.1.2, rspFreeNameB_kOk h.1.1.1.1.2⟩
      split at h
      · rename_i c hs
        rw [← classifyC_instr hs]
        left
        cases c <;> simp only [CArm.ok, Bool.and_eq_true] at h <;>
          simp [rspFreeB, operandNames, srcNames, CArm.instr]
        · exact ⟨rspFreeNameB_gp h.1.1.1.1.1.1, rspFreeNameB_gp h.1.1.1.1.1.2,
            rspFreeNameB_gp h.1.1.1.1.2, rspFreeNameB_gp h.1.1.1.2⟩
        · exact ⟨rspFreeNameB_gp h.1.1.1.1.1, rspFreeNameB_gp h.1.1.1.1.2,
            rspFreeNameB_gp h.1.1.1.2, rspFreeNameB_gp h.1.1.2⟩
      split at h
      · rename_i c hs
        rw [← classifyM_instr hs]
        left
        cases c <;> simp only [MArm.ok, Bool.and_eq_true, beq_iff_eq] at h <;>
          simp [rspFreeB, operandNames, srcNames, MArm.instr]
        · exact ⟨rspFreeNameB_gp h.1.1.2, rspFreeNameB_cell h.1.1.1 h.1.2⟩
        · exact ⟨rspFreeNameB_cell h.1.1.1 h.1.2, rspFreeNameB_gp h.1.1.2⟩
        · exact ⟨rspFreeNameB_cell h.1.1.1 h.1.2, rspFreeNameB_gp h.1.1.2⟩
        · exact ⟨rspFreeNameB_gp h.1.1.2, rspFreeNameB_cell h.1.1.1 h.1.2⟩
      split at h
      · rename_i q v hs
        rw [classifyI_instr hs]
        simp only [iOk, Bool.and_eq_true] at h
        left
        simp [rspFreeB, operandNames, srcNames, rspFreeNameB_slot h.1.1.1.1]
      split at h
      · rename_i d v hs
        rw [(classifyL_instr hs).1]
        simp only [lOk, Bool.and_eq_true] at h
        left
        simp [rspFreeB, operandNames, srcNames, rspFreeNameB_gp h.1.1]
      split at h
      · rename_i d c a b hs
        rw [classifyV_instr hs]
        left
        simp only [Bool.or_eq_true] at h
        rcases h with h | h | h
        · simp only [vOk, Bool.and_eq_true] at h
          simp [rspFreeB, operandNames, srcNames, rspFreeNameB_gp h.1.1.1.1.1.1,
            rspFreeNameB_gp h.1.1.1.1.1.2, rspFreeNameB_gp h.1.1.1.1.2,
            rspFreeNameB_gp h.1.1.1.2]
        · simp only [vtOk, Bool.and_eq_true] at h
          simp [rspFreeB, operandNames, srcNames, rspFreeNameB_gp h.1.1.1.1.1.1,
            rspFreeNameB_gp h.1.1.1.1.1.2, rspFreeNameB_gp h.1.1.1.1.2,
            rspFreeNameB_kOk h.1.1.2]
        · simp only [vfOk, Bool.and_eq_true] at h
          simp [rspFreeB, operandNames, srcNames, rspFreeNameB_gp h.1.1.1.1.1.1.1,
            rspFreeNameB_gp h.1.1.1.1.1.1.2, rspFreeNameB_kOk h.1.1.1.1.2,
            rspFreeNameB_kOk h.1.1.1.2]
      split at h
      · rename_i n d a b hs
        rw [classifyE_instr hs]
        simp only [eOk, Bool.and_eq_true] at h
        left
        simp [eInstr, rspFreeB, operandNames, srcNames, rspFreeNameB_gp h.1.1,
          rspFreeNameB_gp h.1.2, rspFreeNameB_gp h.2]
      split at h
      · rename_i l d a b hs
        rw [classifyX_instr hs]
        simp only [xOk, Bool.and_eq_true] at h
        left
        simp [xInstr, rspFreeB, operandNames, srcNames, rspFreeNameB_gp h.1.1,
          rspFreeNameB_gp h.1.2, rspFreeNameB_gp h.2]
      split at h
      · rename_i n d a v hs
        rw [classifyEI_instr hs]
        simp only [eiOk, Bool.and_eq_true] at h
        left
        simp [eiInstr, rspFreeB, operandNames, srcNames, rspFreeNameB_gp h.1.1,
          rspFreeNameB_gp h.1.2]
      split at h
      · rename_i d k hs
        rw [classifyR_instr hs]
        simp only [rOk, Bool.and_eq_true] at h
        left
        simp [rInstr, rspFreeB, operandNames, srcNames, rspFreeNameB_gp h.1.1]
      split at h
      · rename_i a hc
        exact rspFree_of_armOk hc h
      · cases h
  | Llabel _ _ => exact Or.inl rfl
  | Lcond c l =>
      cases c with
      | reg cc =>
          simp only [instrOKWB, Bool.and_eq_true] at h
          left
          simp [rspFreeB, operandNames, srcNames, rspFreeNameB_condPol h.1]
      | _ => simp [instrOKWB] at h
  | _ => simp [instrOKWB] at h

/-- **An instruction of the covered fragment names no stack name**, or is an indexed store
    whose base, index and value are no stack names; the destination of an indexed store
    names the array and is not constrained. -/
theorem stackFreeB_of_instrOKB {body : Lcmd} {P : X86Backend.LprogBytesDecode.Params}
    {x : LinstrR} (h : instrOKB body P x = true) :
    stackFreeB x = true ∨ ∃ d b i v, x = .Lopn [.reg d] "STOREIDX" [.arrIdx b i 8, .reg v]
      ∧ stackNameB b = false ∧ stackNameB i = false ∧ stackNameB v = false := by
  cases x with
  | Lopn ds o ss =>
      simp only [instrOKB] at h
      cases hc : classifyA (.Lopn ds o ss) with
      | none => rw [hc] at h; cases h
      | some a =>
          rw [hc] at h
          simp only at h
          rcases rspFree_of_armOk hc h with hf | ⟨d, b, i, v, hx, hb, hi, hv⟩
          · exact Or.inl (stackFreeB_of_rspFreeB hf)
          · exact Or.inr ⟨d, b, i, v, hx, stackNameB_of_rspFreeNameB hb,
              stackNameB_of_rspFreeNameB hi, stackNameB_of_rspFreeNameB hv⟩
  | Llabel _ _ => exact Or.inl rfl
  | Lcond c l =>
      cases c with
      | reg cc =>
          simp only [instrOKB, Bool.and_eq_true] at h
          left
          simp [stackFreeB, operandNames, srcNames, stackNameB_condPol h.1]
      | _ => simp [instrOKB] at h
  | _ => simp [instrOKB] at h

/-! ## 4. The image of a covered body -/

/-- **The shapes of the image of an instruction**: the instruction with the widening
    multiply read at its width; an indexed load or an indexed store on the array of a
    resolved access; the one-bit move of a stored carry constant; the indexed store of an
    indexed store through a cell (`cellIdxStore?`); or the name-keyed zeroing or
    constant-index store of an array zeroing or a constant-index store (`arrImmImg`). -/
theorem imgInstr_cases (slotArr : String → Option (String × Nat)) (body : Lcmd) (k : Nat)
    (x : LinstrR) :
    (imgInstr slotArr body k x).fst = normA x
    ∨ (∃ d o b idx A n, X86Backend.LprogAsmPrinter.untagCaret o = "LOADIDX"
        ∧ x = .Lopn [.reg d] o [.arrIdx b idx 8]
        ∧ accArr slotArr body k b = some (A, n)
        ∧ (imgInstr slotArr body k x).fst = .Lopn [.reg d] "LOADIDX" [.arrIdx A idx 8])
    ∨ (∃ d o b idx v A n, X86Backend.LprogAsmPrinter.untagCaret o = "STOREIDX"
        ∧ x = .Lopn [.reg d] o [.arrIdx b idx 8, .reg v]
        ∧ accArr slotArr body k b = some (A, n)
        ∧ (imgInstr slotArr body k x).fst
          = .Lopn [.reg A] "STOREIDX" [.arrIdx A idx 8, .reg v])
    ∨ (∃ d n, x = .Lopn [.reg d] "MOV:64" [.imm n]
        ∧ (imgInstr slotArr body k x).fst = .Lopn [.reg d] "MOV" [.imm n])
    ∨ (∃ A n q v, cellIdxStore? slotArr body k x = some (A, n, q, v)
        ∧ (imgInstr slotArr body k x).fst
          = .Lopn [.reg A] "STOREIDX" [.arrIdx A q 8, .reg v])
    ∨ ∃ r, arrImmImg slotArr body k x = some r ∧ (imgInstr slotArr body k x).fst = r.1 := by
  unfold imgInstr
  split
  · split_ifs with ho
    · split
      · rename_i A n hA
        exact Or.inr (Or.inl ⟨_, _, _, _, A, n, ho, rfl, hA, rfl⟩)
      · exact Or.inl rfl
    · exact Or.inl rfl
  · split_ifs with ho
    · split
      · rename_i A n hA
        exact Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, A, n, ho, rfl, hA, rfl⟩))
      · exact Or.inl rfl
    · exact Or.inl rfl
  · split
    · rename_i d n hb
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨d, n, (bitStore?_spec hb).1, rfl⟩)))
    · split
      · rename_i A n q v hc
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨A, n, q, v, hc, rfl⟩))))
      · split
        · rename_i r hr
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨r, hr, rfl⟩))))
        · exact Or.inl rfl

/-- An instruction of the covered fragment is no indexed store through a cell: the fragment
    stores to a frame slot only, and a cell name is no frame slot. -/
theorem cellIdxStore?_of_instrOKB {slotArr : String → Option (String × Nat)} {body body' : Lcmd}
    {P : X86Backend.LprogBytesDecode.Params} {k : Nat} {x : LinstrR}
    (hok : instrOKB body' P x = true) : cellIdxStore? slotArr body k x = none := by
  cases hs : cellIdxStore? slotArr body k x with
  | none => rfl
  | some p =>
      exfalso
      obtain ⟨A, n, q, v⟩ := p
      obtain ⟨c, D, -, -, -, -, -, -, -, rfl, hc, -⟩ := cellIdxStore?_spec hs
      have hgc : gpOk c = false := by
        cases hg : gpOk c with
        | false => rfl
        | true => rw [cellParts?_gp hg] at hc; cases hc
      have hsl := (notSlot_of_cell hc).2
      simp [instrOKB, classifyA, hgc, AArm.ok, hsl, X86Backend.DecodePrinted.isMovM] at hok

/-- The array of a resolved access is an array of the slot map. -/
theorem stackNameB_accArr {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {b A : String} {n : Nat}
    (hsl : ∀ q A n, slotArr q = some (A, n) → stackNameB A = false)
    (h : accArr slotArr body k b = some (A, n)) : stackNameB A = false := by
  obtain ⟨q, -, hq, -⟩ := accArr_spec h
  exact hsl q A n hq

/-- **The image of an instruction of the covered fragment names no stack name**, when every
    indexed access of the instruction resolves to an array (`accOkB`) and no array name of
    the slot map is a stack name. -/
theorem stackFreeB_imgInstr {slotArr : String → Option (String × Nat)} {body : Lcmd}
    {P : X86Backend.LprogBytesDecode.Params} {k : Nat} {x : LinstrR}
    (hok : instrOKB body P x = true) (hacc : accOkB slotArr body k x = true)
    (hsl : ∀ q A n, slotArr q = some (A, n) → stackNameB A = false) :
    stackFreeB (imgInstr slotArr body k x).fst = true := by
  rcases stackFreeB_of_instrOKB hok with hf | ⟨d, b, i, v, rfl, hb, hi, hv⟩
  · rcases imgInstr_cases slotArr body k x with h | ⟨d, o, b, idx, A, n, -, rfl, hA, h⟩ |
      ⟨d, o, b, idx, v, A, n, -, rfl, hA, h⟩ | ⟨d, n, rfl, h⟩ | ⟨A, n, q, v, hc, -⟩ |
      ⟨ri, hri, h⟩
    · rw [h]
      simp only [stackFreeB, operandNames_normA] at hf ⊢
      exact hf
    · rw [h]
      have hA' := stackNameB_accArr hsl hA
      simp [stackFreeB, operandNames, srcNames] at hf ⊢
      simp [hf, hA']
    · rw [h]
      have hA' := stackNameB_accArr hsl hA
      simp [stackFreeB, operandNames, srcNames] at hf ⊢
      simp [hf, hA']
    · rw [h]
      simpa [stackFreeB, operandNames, srcNames] using hf
    · rw [cellIdxStore?_of_instrOKB hok] at hc
      cases hc
    · rw [h]
      unfold arrImmImg at hri
      split at hri
      · split_ifs at hri
        split at hri
        · rename_i A n hA
          cases hri
          simp [stackFreeB, operandNames, srcNames, stackNameB_accArr hsl hA]
        · cases hri
      · split_ifs at hri
        split at hri
        · rename_i A n hA
          cases hri
          simp [stackFreeB, operandNames, srcNames] at hf ⊢
          simp [hf, stackNameB_accArr hsl hA]
        · cases hri
      · cases hri
  · simp only [accOkB, Bool.true_and] at hacc
    obtain ⟨⟨A, n⟩, hA⟩ := Option.isSome_iff_exists.mp hacc
    rw [imgInstr_stx slotArr body k hA]
    simp [stackFreeB, operandNames, srcNames, stackNameB_accArr hsl hA, hi, hv]

/-- An instruction of the image of a body is the image of an instruction of the body before
    its last, at its position. -/
theorem mem_virtImg {slotArr : String → Option (String × Nat)} {body : Lcmd} {i : LinstrRM}
    (hi : i ∈ virtImg slotArr body) :
    ∃ k j, body[k]? = some j ∧ j ∈ body.dropLast ∧ i = imgInstr slotArr body k j.li_i := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
  rw [virtImg_getElem?] at hk
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hk
  refine ⟨k, j, ?_, List.mem_of_getElem? hj, rfl⟩
  rw [List.dropLast_eq_take, List.getElem?_take] at hj
  split_ifs at hj
  exact hj

/-- Every instruction of a covered printed body before its last is in the covered
    fragment. -/
theorem instrOKB_of_printedAddrB {body : Lcmd} (hp : printedAddrB body = true) {j : Linstr}
    (hj : j ∈ body.dropLast) :
    instrOKB body (X86Backend.LprogBytesDecode.Params.ofBody body) j.li_i = true := by
  simp only [printedAddrB, Bool.and_eq_true, List.all_eq_true] at hp
  exact hp.1.2 j hj

/-- **The image of a covered printed body names no stack name**: for a body in the class
    `printedAddrB` and the image class `physImgB`, at a slot map none of whose array names
    is a stack name, no operand name of an instruction of the image is `RSP` or a cell name
    of the base `RSP`. -/
theorem virtImg_stackFree {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hp : printedAddrB body = true) (hphys : physImgB slotArr body = true)
    (hsl : ∀ q A n, slotArr q = some (A, n) → stackNameB A = false) :
    ∀ i ∈ virtImg slotArr body, stackFreeB i.fst = true := by
  intro i hi
  obtain ⟨k, j, hk, hj, rfl⟩ := mem_virtImg hi
  exact stackFreeB_imgInstr (instrOKB_of_printedAddrB hp hj) (physImgB_at hphys hk).1 hsl

/-- **The image of a covered printed body does not name the stack pointer**: under the
    hypotheses of `virtImg_stackFree`, the image passes the check `spFreeBodyB` of `RSP`. -/
theorem virtImg_spFreeBodyB {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hp : printedAddrB body = true) (hphys : physImgB slotArr body = true)
    (hsl : ∀ q A n, slotArr q = some (A, n) → stackNameB A = false) :
    spFreeBodyB "RSP" (virtImg slotArr body) = true :=
  List.all_eq_true.mpr fun i hi =>
    spFreeB_of_stackFreeB (virtImg_stackFree hp hphys hsl i hi)

/-- **The image of a covered printed body contains no call and no return**, at every slot
    map. -/
theorem virtImg_noCall (slotArr : String → Option (String × Nat)) {body : Lcmd}
    (hp : printedAddrB body = true) :
    ((virtImg slotArr body).all fun i => !isCall i.fst) = true := by
  refine List.all_eq_true.mpr fun i hi => ?_
  obtain ⟨k, j, -, hj, rfl⟩ := mem_virtImg hi
  have hok := instrOKB_of_printedAddrB hp hj
  rcases imgInstr_cases slotArr body k j.li_i with h | ⟨_, _, _, _, _, _, -, -, -, h⟩ |
    ⟨_, _, _, _, _, _, _, -, -, -, h⟩ | ⟨_, _, -, h⟩ | ⟨_, _, _, _, -, h⟩ | ⟨_, hri, h⟩
  · rw [h]
    cases hx : j.li_i <;> rw [hx] at hok <;> simp [instrOKB] at hok <;> rfl
  · rw [h]; rfl
  · rw [h]; rfl
  · rw [h]; rfl
  · rw [h]; rfl
  · obtain ⟨ds, o, ss, he⟩ := arrImmImg_lopn hri
    rw [h, he]
    rfl

/-! ## 5. The names an instruction of the image reads -/

/-- A name an instruction reads (`rdWr`) is an operand name. -/
theorem rdWr_sub {x : LinstrR} {r : String} (h : r ∈ (rdWr x).1) : r ∈ operandNames x := by
  cases x with
  | Lopn ds o ss =>
      simp only [rdWr, List.mem_append] at h
      simp only [operandNames, List.flatMap_append, List.mem_append]
      rcases h with h | h
      · obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp h
        refine Or.inr (List.mem_flatMap.mpr ⟨p, hp, ?_⟩)
        cases p <;> simp_all [opNames, srcNames]
      · obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp h
        refine Or.inl (List.mem_flatMap.mpr ⟨p, hp, ?_⟩)
        cases p <;> simp_all [srcNames]
  | _ => simp [rdWr] at h

/-- A name an instruction of the covered fragment reads is no stack name. -/
theorem stackNameB_of_read {body : Lcmd} {P : X86Backend.LprogBytesDecode.Params}
    {x : LinstrR} (hok : instrOKB body P x = true) {r : String} (hr : r ∈ (rdWr x).1) :
    stackNameB r = false := by
  rcases stackFreeB_of_instrOKB hok with hf | ⟨d, b, i, v, rfl, hb, hi, hv⟩
  · have hn : ∀ r ∈ operandNames x, stackNameB r = false := by simpa [stackFreeB] using hf
    exact hn r (rdWr_sub hr)
  · simp [rdWr, opNames] at hr
    rcases hr with rfl | rfl | rfl <;> assumption

/-- The source of a move between names (`slotMov?`) is a name the move reads. -/
theorem read_of_slotMov {i : LinstrR} {d s : String} (h : slotMov? i = some (d, s)) :
    s ∈ (rdWr i).1 := by
  unfold slotMov? at h
  split at h
  · split_ifs at h
    cases h
    simp [rdWr, opNames]
  · cases h

/-- A name the image of an instruction reads is a name the instruction reads, an array
    name of the slot map, or, for an indexed store through a cell (`cellIdxStore?`), the
    frame slot of its index, which an instruction of the body before it reads. -/
theorem read_imgInstr {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {x : LinstrR} {r : String} (hr : r ∈ (rdWr (imgInstr slotArr body k x).fst).1) :
    r ∈ (rdWr x).1 ∨ (∃ q n, slotArr q = some (r, n))
      ∨ ∃ A n v j i', cellIdxStore? slotArr body k x = some (A, n, r, v) ∧ j < k
        ∧ body[j]? = some i' ∧ r ∈ (rdWr i'.li_i).1 := by
  rcases imgInstr_cases slotArr body k x with h | ⟨d, o, b, idx, A, n, -, rfl, hA, h⟩ |
    ⟨d, o, b, idx, v, A, n, -, rfl, hA, h⟩ | ⟨d, n, rfl, h⟩ | ⟨A, n, q, v, hc, h⟩ |
    ⟨ri, hri, h⟩
  rotate_left 4
  · obtain ⟨c, D, B, X, d1, s, l, r', m, hx, -, h3, -, -, -, hr', hm, -, -, -, -, -, -, -,
      hacc⟩ := cellIdxStore?_spec hc
    rw [h] at hr
    simp only [rdWr, opNames, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl
    · obtain ⟨q', -, hq', -⟩ := accArr_spec hacc
      exact Or.inr (Or.inl ⟨q', n, hq'⟩)
    · exact Or.inr (Or.inr ⟨A, n, v, k - 3, r', hc, by omega, hr', read_of_slotMov hm⟩)
    · left
      rw [hx]
      simp [rdWr, opNames]
  · rw [h] at hr
    unfold arrImmImg at hri
    split at hri
    · split_ifs at hri
      split at hri
      · cases hri
        simp [rdWr, opNames] at hr
      · cases hri
    · split_ifs at hri
      split at hri
      · rename_i A n hA
        cases hri
        obtain ⟨q, -, hq, -⟩ := accArr_spec hA
        simp [rdWr, opNames] at hr ⊢
        rcases hr with rfl | rfl
        · exact Or.inr (Or.inl ⟨q, n, hq⟩)
        · simp
      · cases hri
    · cases hri
  · rw [h] at hr
    left
    cases x <;> exact hr
  · rw [h] at hr
    obtain ⟨q, -, hq, -⟩ := accArr_spec hA
    simp [rdWr, opNames] at hr ⊢
    rcases hr with rfl | rfl
    · exact Or.inr (Or.inl ⟨q, n, hq⟩)
    · simp
  · rw [h] at hr
    obtain ⟨q, -, hq, -⟩ := accArr_spec hA
    simp [rdWr, opNames] at hr ⊢
    rcases hr with rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨q, n, hq⟩)
    · simp
    · simp
  · rw [h] at hr
    simp [rdWr, opNames] at hr

/-- **A name an instruction of the image of a covered printed body reads is no stack
    name**, at a slot map none of whose array names is a stack name. -/
theorem stackNameB_of_read_virtImg {slotArr : String → Option (String × Nat)} {body : Lcmd}
    (hp : printedAddrB body = true)
    (hsl : ∀ q A n, slotArr q = some (A, n) → stackNameB A = false) {i : LinstrRM}
    (hi : i ∈ virtImg slotArr body) {r : String} (hr : r ∈ (rdWr i.fst).1) :
    stackNameB r = false := by
  obtain ⟨k, j, -, hj, rfl⟩ := mem_virtImg hi
  rcases read_imgInstr hr with h | ⟨q, n, hq⟩ | ⟨_, _, _, _, _, hc, -⟩
  · exact stackNameB_of_read (instrOKB_of_printedAddrB hp hj) h
  · exact hsl q r n hq
  · rw [cellIdxStore?_of_instrOKB (instrOKB_of_printedAddrB hp hj)] at hc
    cases hc

/-- A name a list of instructions reads before writing it is read by one of them. -/
theorem exposed_sub {is : List LinstrR} {y : String} (h : y ∈ exposed is) :
    ∃ i ∈ is, y ∈ (rdWr i).1 := by
  have key : ∀ (is : List LinstrR) (acc : List String × List String),
      y ∈ (is.foldl (fun (acc : List String × List String) i =>
        let rw := rdWr i
        (acc.1 ++ (rw.1.filter fun x => !acc.2.contains x && !acc.1.contains x).eraseDups,
          acc.2 ++ rw.2)) acc).1 → y ∈ acc.1 ∨ ∃ i ∈ is, y ∈ (rdWr i).1 := by
    intro is
    induction is with
    | nil => intro acc h; exact Or.inl h
    | cons i t ih =>
        intro acc h
        rw [List.foldl_cons] at h
        rcases ih _ h with h' | ⟨j, hj, hy⟩
        · simp only [List.mem_append] at h'
          rcases h' with h' | h'
          · exact Or.inl h'
          · exact Or.inr ⟨i, List.mem_cons_self, (List.mem_filter.mp
              (List.mem_eraseDups.mp h')).1⟩
        · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, hy⟩
  rcases key is ([], []) h with h' | h'
  · cases h'
  · exact h'

/-- A fold that appends to its accumulator pairs whose second components are found in `ys`
    yields pairs of the accumulator or pairs whose second component is in `ys`. -/
theorem foldl_find_snd {α : Type} (ys : List String)
    (P : List (α × String) → α → String → Bool) (xs : List α) :
    ∀ (acc : List (α × String)), ∀ p ∈ xs.foldl (fun acc x =>
        match ys.find? (P acc x) with
        | some y => acc ++ [(x, y)]
        | none => acc) acc, p ∈ acc ∨ p.2 ∈ ys := by
  induction xs with
  | nil => intro acc p hp; exact Or.inl hp
  | cons x t ih =>
      intro acc p hp
      rw [List.foldl_cons] at hp
      rcases ih _ p hp with h | h
      · cases hf : ys.find? (P acc x) with
        | none => rw [hf] at h; exact Or.inl h
        | some y =>
            rw [hf] at h
            simp only [List.mem_append, List.mem_singleton] at h
            rcases h with h | rfl
            · exact Or.inl h
            · exact Or.inr (List.mem_of_find?_eq_some hf)
      · exact Or.inr h

/-- **Every target of the synthesised renaming is a name that an instruction of the image
    reads.** -/
theorem synthRen_target_mem {src img : List LinstrRM} {k0 : Nat} {p : String × String}
    (hp : p ∈ synthRen src img k0) : ∃ i ∈ img, p.2 ∈ (rdWr i.fst).1 := by
  unfold synthRen at hp
  split at hp
  · dsimp only at hp
    split at hp
    · split at hp
      · rcases foldl_find_snd _ _ _ _ p hp with h | h
        · cases h
        · simp only [List.mem_append, List.mem_filter] at h
          have fin : ∀ n s,
              p.2 ∈ exposed (List.map Prod.fst (List.take n (List.drop s img))) →
                ∃ i ∈ img, p.2 ∈ (rdWr i.fst).1 := by
            intro n s hy
            obtain ⟨i, hi, hr⟩ := exposed_sub hy
            obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
            exact ⟨j, List.mem_of_mem_drop (List.mem_of_mem_take hj), hr⟩
          rcases h with (h | h) | h <;> exact fin _ _ h.1.1
      · simp at hp
    · simp at hp
  · simp at hp

/-! ## 6. The slot maps -/

/-- No array name of the slot map of a layout is a stack name: it is an argument name. -/
theorem stackNameB_slotArrOf {σ : AbiLayout} {nm : String → String} {q A : String} {n : Nat}
    (h : slotArrOf σ nm q = some (A, n)) : stackNameB A = false := by
  obtain ⟨j, a, -, -, rfl, -⟩ := slotArrOf_some h
  exact stackNameB_argName j

/-- A renaming none of whose targets is a stack name sends a name that is no stack name to
    a name that is no stack name. -/
theorem stackNameB_renOf {ps : List (String × String)}
    (hps : ∀ p ∈ ps, stackNameB p.2 = false) {r : String} (hr : stackNameB r = false) :
    stackNameB (renOf ps r) = false := by
  rcases renOf_cases ps r with h | ⟨p, hp, -, h⟩
  · rw [h]; exact hr
  · rw [h]; exact hps p hp

/-- **No array name of the renamed slot map of a loop is a stack name**: for a covered
    printed body, the slot map of a layout renamed by the renaming synthesised against the
    image of the body has no stack name among its array names. -/
theorem stackNameB_slotRen_synthRen {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {src : List LinstrRM} {k0 : Nat} (hp : printedAddrB body = true) {q A : String} {n : Nat}
    (h : slotRen (slotArrOf σ nm)
      (renOf (synthRen src (virtImg (slotArrOf σ nm) body) k0)) q = some (A, n)) :
    stackNameB A = false := by
  obtain ⟨A0, h0, rfl⟩ := slotRen_some h
  refine stackNameB_renOf (fun p hp' => ?_) (stackNameB_slotArrOf h0)
  obtain ⟨i, hi, hr⟩ := synthRen_target_mem hp'
  exact stackNameB_of_read_virtImg hp (fun _ _ _ => stackNameB_slotArrOf) hi hr

end CatCrypt.Crypto.SecureCompilation.Haxc
