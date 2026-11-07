/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs
public import CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel

@[expose] public section

set_option autoImplicit false

/-!
# The vector instructions of the `Lprog` instruction-set record

A vector instruction of the `Lprog` level is an `Lopn` with one register destination and a
mnemonic with the characters `V512:` first. `vecArgs?` reads such an instruction as a
`VecOp`: a lane-wise operation, an immediate shift or rotate, a dword duplication, a move,
a dword permutation, a masked blend, a three-input bitwise function, or a load or a store
of eight consecutive 64-bit elements of an array. The numeric parameters of an operation
(lane width, shift count, truth table) are immediate operands; the shape of the array of a
load or a store is the memory tag of the instruction. `vecStep` runs a `VecOp` on the base
state `LstateM`: registers are read at width 512 (a mask at width 16) from the width-tagged
register file, the value is that of the semantic functions of `ZmmTextModel`, the program
counter advances by one, and no flag is written.

`Isa.withVec I` is the record `I` whose step on an instruction `vecArgs?` reads is
`vecStep`. An instruction set that has no step on those instructions (`Isa.RefusesVec`)
has every step of its own in `I.withVec` (`Isa.withVec_stepLe`).

The x86 flag machine `evalInstrPMemF` has no step on an `Lopn` whose mnemonic starts with a
character that no mnemonic of the machine starts with (`FreshMnem`, `evalInstrPMemF_fresh`);
`V` is such a character, so `x86Isa` refuses the vector instructions
(`x86Isa_refusesVec`).

## Main definitions

* `usedHeads`, `FreshMnem`: the first characters of the mnemonics of the flag machine, and
  the mnemonics that start with none of them.
* `VecOp`, `lopOfName?`, `vecOfBase?`, `vecArgs?`, `vecStep`: the vector instructions, their
  recogniser and their step.
* `Isa.withVec`, `Isa.RefusesVec`: the instruction set with the vector step, and the
  refusal of the vector instructions.

## Main results

* `FreshMnem.ne`, `FreshMnem.strip`, `lsemStepMem_fresh`, `evalInstrPMemF_fresh`: the flag
  machine has no step on an `Lopn` with a mnemonic of `FreshMnem`.
* `vecArgs?_wire`, `vecArgs?_of_isCtl`: an instruction `vecArgs?` reads is an `Lopn` with a
  mnemonic of `FreshMnem`, and no control instruction.
* `vecStep_lpc`, `vecStep_flags`: a vector step advances the program counter by one and
  keeps the carry and overflow flags.
* `Isa.withVec_step_vec`, `Isa.withVec_step_of_none`, `Isa.withVec_stepLe`,
  `Isa.withVec_step_vec_pc_flags`: the step of `I.withVec`.
* `x86Isa_refusesVec`: `x86Isa.RefusesVec`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.VecIsa

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast (lsemStepCast castStruct?
  movImmStruct?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry (lsemStepMC mulhiStruct?
  adcxStruct? adcxhiStruct? sbbStruct? sbbhiStruct?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift (lsemStepSh sarStruct?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminImmShiftMnem (immShiftMnem?)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs (splitChars_head)
open CatCrypt.Crypto.SecureCompilation.VIR.ZmmTextModel (LOp lane ofLanes semLW semShImm semDup
  semMerge semPerm semRol semTern)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)

/-! ## 1. Mnemonics the flag machine does not read -/

/-- The first characters of the mnemonics the x86 flag machine reads, and the separators
    `:` and `^` of a mnemonic. -/
def usedHeads : List Char :=
  ['A', 'C', 'L', 'M', 'N', 'O', 'R', 'S', 'T', 'X', 'Z', ':', '^']

/-- A mnemonic whose first character is outside `usedHeads`. -/
def FreshMnem (opn : String) : Prop :=
  ∃ c t, opn.toList = c :: t ∧ c ∉ usedHeads

/-- A mnemonic of `FreshMnem` differs from every mnemonic that is empty or starts with a
    character of `usedHeads`. -/
theorem FreshMnem.ne {opn : String} (h : FreshMnem opn) (lit : String)
    (hl : lit.toList.head?.all (fun c => decide (c ∈ usedHeads)) = true) : ¬ opn = lit := by
  obtain ⟨c, t, ht, hc⟩ := h
  rintro rfl
  rw [ht] at hl
  simp only [List.head?_cons, Option.all_some, decide_eq_true_eq] at hl
  exact hc hl

/-- **The mnemonic without its width tag.** A mnemonic of `FreshMnem` with the width tag
    `:64` removed is a mnemonic of `FreshMnem`. -/
theorem FreshMnem.strip {opn : String} (h : FreshMnem opn) : FreshMnem (stripWidthTag opn) := by
  obtain ⟨c, t, ht, hc⟩ := h
  have hca : (c != '^') = true := by
    simp only [bne_iff_ne, ne_eq]
    rintro rfl
    exact hc (by decide)
  unfold stripWidthTag
  split
  · refine ⟨c, t.takeWhile (fun x => x != '^'), ?_, hc⟩
    rw [String.toList_ofList, ht, List.takeWhile_cons_of_pos (p := fun x => x != '^') hca]
  split
  · next hs =>
    unfold hasSuffix at hs
    obtain ⟨L, hL⟩ := List.isSuffixOf_iff_suffix.mp hs
    rw [show (":64" : String).toList = [':', '6', '4'] from by decide, ht] at hL
    cases L with
    | nil =>
      obtain ⟨rfl, -⟩ := List.cons.inj hL
      exact absurd (by decide) hc
    | cons a L' =>
      obtain ⟨rfl, hL'⟩ := List.cons.inj hL
      refine ⟨a, L', ?_, hc⟩
      have hd : ∀ X : List Char, (X ++ [':', '6', '4']).dropLast.dropLast.dropLast = X := by
        intro X
        simp
      rw [String.toList_ofList, ht, ← hL']
      exact hd (a :: L')
  · exact ⟨c, t, ht, hc⟩

/-- The operation table `applyOpnN` has no entry at a mnemonic of `FreshMnem`. -/
theorem applyOpnN_none_of_fresh {w : Nat} {m : String} (h : FreshMnem m)
    (l : List (BitVec w)) : applyOpnN w m l = none := by
  unfold applyOpnN
  split <;> first | rfl | exact absurd rfl (h.ne _ (by decide))

/-- A mnemonic of `FreshMnem` is no count-tagged immediate shift. -/
theorem immShiftMnem?_fresh {opn : String} (h : FreshMnem opn) : immShiftMnem? opn = none := by
  obtain ⟨c, r, hr, hc⟩ := h.strip
  obtain ⟨g, gs, hg⟩ := splitChars_head c (fun e => hc (e ▸ by decide)) r
  unfold immShiftMnem?
  simp only [hr, hg]
  split
  · next mn ds heq =>
    obtain ⟨rfl, -⟩ := List.cons.inj heq
    have hf : FreshMnem (String.ofList (c :: g)) := ⟨c, g, String.toList_ofList, hc⟩
    have hne : ∀ lit : String, lit.toList.head?.all (fun c => decide (c ∈ usedHeads)) = true →
        (String.ofList (c :: g) == lit) = false := fun lit hl =>
      beq_eq_false_iff_ne.mpr (hf.ne lit hl)
    simp only [hne "SHL" (by decide), hne "SHR" (by decide), hne "SAR" (by decide),
      hne "ROR" (by decide), Bool.or_self, Bool.false_eq_true, ite_false]
  · rfl

variable {dst opn : String} {srcs : List LOperand}

/-- The width-aware step has no step on an `Lopn` with a mnemonic of `FreshMnem`. -/
theorem lsemStepN_fresh (h : FreshMnem opn) (s : LstateN) :
    lsemStepN (.Lopn [.reg dst] opn srcs) s = none := by
  have hap : ∀ (w : Nat) (l : List (BitVec w)), applyOpnN w (stripWidthTag opn) l = none :=
    fun w l => applyOpnN_none_of_fresh h.strip l
  have h1 := h.strip.ne "CMOV" (by decide)
  have h2 := h.strip.ne "MOV" (by decide)
  have h3 := h.strip.ne "NEG" (by decide)
  have h4 := h.strip.ne "LEA" (by decide)
  have h5 : cmpOfName? (stripWidthTag opn) = none :=
    cmpOfName?_eq_none (h.strip.ne _ (by decide)) (h.strip.ne _ (by decide))
      (h.strip.ne _ (by decide)) (h.strip.ne _ (by decide)) (h.strip.ne _ (by decide))
      (h.strip.ne _ (by decide))
  have h6 : ¬ (opn = "MOV:8" ∨ opn = "MOV:16") := fun h' =>
    h'.elim (h.ne _ (by decide)) (h.ne _ (by decide))
  unfold lsemStepN
  split <;> first
    | rfl
    | (rename_i heq
       cases heq
       try simp only [h1, h2, h3, h4, h5, h6, hap, immFirstN, immShiftMnem?_fresh h, ite_false,
         Option.map_none]
       repeat' (first | rfl | split))

/-- The shift-aware and the multiply-and-carry steps have no step on an `Lopn` with a
    mnemonic of `FreshMnem`. -/
theorem lsemStepMC_fresh (h : FreshMnem opn) (s : LstateN) :
    lsemStepMC (.Lopn [.reg dst] opn srcs) s = none := by
  have e1 : mulhiStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold mulhiStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.strip.ne _ (by decide)))
  have e2 : adcxStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold adcxStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.strip.ne _ (by decide)))
  have e3 : adcxhiStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold adcxhiStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.strip.ne _ (by decide)))
  have e4 : sbbStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold sbbStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.strip.ne _ (by decide)))
  have e5 : sbbhiStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold sbbhiStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.strip.ne _ (by decide)))
  have e6 : sarStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold sarStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.strip.ne _ (by decide)))
  simp only [lsemStepMC, lsemStepSh, e1, e2, e3, e4, e5, e6, lsemStepN_fresh h]

/-- The cast-aware step has no step on an `Lopn` with a mnemonic of `FreshMnem`, at every
    descriptor. -/
theorem lsemStepCast_fresh (h : FreshMnem opn) (cd : Option Nat) (s : LstateN) :
    lsemStepCast (.Lopn [.reg dst] opn srcs, cd) s = none := by
  have e1 : castStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold castStruct?
    split
    · next heq =>
      cases heq
      refine ite_eq_right ?_
      simp only [h.ne "ZEROEXT" (by decide), h.ne "TRUNC" (by decide),
        h.ne "CASTW_32_32" (by decide), h.ne "CASTW_32_64" (by decide),
        h.ne "CASTW_64_32" (by decide), h.ne "CASTW_64_64" (by decide),
        h.ne "CASTW_64_16" (by decide), h.ne "CASTW_16_64" (by decide),
        h.ne "CASTW_16_16" (by decide), h.ne "CASTW_16_32" (by decide),
        h.ne "CASTW_32_16" (by decide), or_self, not_false_eq_true]
    · rfl
  have e2 : movImmStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold movImmStruct?
    split
    · next heq =>
      cases heq
      exact ite_eq_right (fun hc => h.strip.ne "MOV" (by decide)
        (JasminLsemCast.stripWidthTag_of_isMovImm hc))
    · rfl
  simp only [lsemStepCast, e1, e2, lsemStepMC_fresh h]

/-- **The memory step has no step on an `Lopn` with a mnemonic of `FreshMnem`**, at every
    memory tag. -/
theorem lsemStepMem_fresh (h : FreshMnem opn) (tag : MemTag) (s : LstateM) :
    lsemStepMem (.Lopn [.reg dst] opn srcs, tag) s = none := by
  have e1 : loadStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold loadStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.ne _ (by decide)))
  have e2 : storeStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold storeStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.ne _ (by decide)))
  have e3 : loadCStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold loadCStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.ne _ (by decide)))
  have e4 : storeCStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold storeCStruct?
    split <;> first | rfl | (rename_i heq; cases heq)
  have e5 : zeroStruct? (.Lopn [.reg dst] opn srcs) = none := by
    simp only [zeroStruct?, ite_eq_right (h.ne "ZEROARR" (by decide))]
  have e6 : storeImmStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold storeImmStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.ne _ (by decide)))
  cases tag <;>
    simp only [lsemStepMem, e1, e2, e3, e4, e5, e6, lsemStepCast_fresh h, Option.map_none]

/-- **The flag machine has no step on an `Lopn` with a mnemonic of `FreshMnem`**, at every
    memory tag, in every program and from every state. -/
theorem evalInstrPMemF_fresh (h : FreshMnem opn) (P : LprogM) (tag : MemTag) (s : LstateMF) :
    evalInstrPMemF P (.Lopn [.reg dst] opn srcs, tag) s = none := by
  have hI : IsLopn (LinstrR.Lopn [.reg dst] opn srcs, tag) := ⟨_, _, _, rfl⟩
  have e1 : cmpArgs? (LinstrR.Lopn [.reg dst] opn srcs, tag) = none := by
    unfold cmpArgs?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.ne _ (by decide +kernel)))
  have e2 : movRegArgs? (LinstrR.Lopn [.reg dst] opn srcs, tag) = none := by
    unfold movRegArgs?
    split
    · next heq =>
      cases heq
      have hq : copyQ opn = false := by
        simp only [copyQ, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        exact ⟨⟨h.ne _ (by decide), h.ne _ (by decide)⟩, h.ne _ (by decide)⟩
      rw [ite_eq_right (h.strip.ne "MOV" (by decide)), hq]
      rfl
    · rfl
  have e3 : carryArgs? (LinstrR.Lopn [.reg dst] opn srcs, tag) = none := by
    unfold carryArgs?
    split
    · next heq =>
      cases heq
      simp only [h.ne (withWidthTag 64 "ADC") (by decide +kernel),
        h.ne (withWidthTag 64 "SBB") (by decide +kernel),
        h.ne (withWidthTag 64 "ADCX") (by decide +kernel),
        h.ne (withWidthTag 64 "ADOX") (by decide +kernel), ite_false]
    · rfl
  have e4 : wideArgs? (LinstrR.Lopn [.reg dst] opn srcs, tag) = none := by
    unfold wideArgs?
    split
    · next heq =>
      cases heq
      exact ite_eq_right (h.ne _ (by decide +kernel))
    · next heq =>
      cases heq
    · rfl
  unfold evalInstrPMemF
  simp only [e1, e2, e3, e4, flagCondCC?, evalInstrPMemL_lopn _ _ _ hI,
    lsemStepMem_fresh h, Option.map_none]

/-! ## 2. The vector instructions -/

/-- A vector instruction of the `Lprog` level on named registers of 512 bits. -/
inductive VecOp where
  /-- `dst := a ∘ b` lane-wise at width `L`. -/
  | op (L : Nat) (o : LOp) (dst a b : String)
  /-- `dst := a` with every lane of width `L` shifted by `imm`, left or right. -/
  | shi (L : Nat) (left : Bool) (imm : Nat) (dst a : String)
  /-- `dst := a` with every lane of width `L` rotated left by `imm`. -/
  | rol (L imm : Nat) (dst a : String)
  /-- `dst := a` with each dword pair holding its odd (`odd`) or its even dword. -/
  | dup (odd : Bool) (dst a : String)
  /-- `dst := a`. -/
  | mova (dst a : String)
  /-- Dword `j` of `dst` is dword `idx[j]` of `src`. -/
  | perm (dst src idx : String)
  /-- Dword `j` of `dst` is dword `j` of `a` where bit `j` of the mask `k` is set, else of
      `b`. -/
  | blend (dst k a b : String)
  /-- `dst` is the bitwise function with truth table `imm` of `a`, `b` and `c`. -/
  | tern (imm : BitVec 8) (dst a b c : String)
  /-- `dst` holds the eight elements of the array `base` of length `n` from index `idx`. -/
  | load (n : Nat) (dst base idx : String)
  /-- `dst` is the array `base` of length `n` with the eight lanes of `val` from index
      `idx`. -/
  | store (n : Nat) (dst base idx val : String)

/-- The lane-wise operation of a base mnemonic. -/
def lopOfName? : String → Option LOp
  | "ADD" => some (.bin .add)
  | "SUB" => some (.bin .sub)
  | "MUL" => some (.bin .mul)
  | "AND" => some (.bin .and)
  | "OR" => some (.bin .or)
  | "XOR" => some (.bin .xor)
  | "SHL" => some (.bin .shl)
  | "SHR" => some (.bin .shr)
  | "ANDN" => some (.bin .andn)
  | "MINU" => some .minu
  | "MULUDQ" => some .muludq
  | _ => none

/-- The vector instruction of a base mnemonic (the mnemonic after `V512:`), a destination,
    operands and a memory tag. -/
def vecOfBase? (base dst : String) (srcs : List LOperand) (tag : MemTag) : Option VecOp :=
  match base with
  | "MOVA" =>
      match srcs with
      | [.reg a] => some (.mova dst a)
      | _ => none
  | "SHDUP" =>
      match srcs with
      | [.reg a] => some (.dup true dst a)
      | _ => none
  | "SLDUP" =>
      match srcs with
      | [.reg a] => some (.dup false dst a)
      | _ => none
  | "SLL" =>
      match srcs with
      | [.reg a, .imm L, .imm k] => some (.shi L true k dst a)
      | _ => none
  | "SRL" =>
      match srcs with
      | [.reg a, .imm L, .imm k] => some (.shi L false k dst a)
      | _ => none
  | "ROL" =>
      match srcs with
      | [.reg a, .imm L, .imm k] => some (.rol L k dst a)
      | _ => none
  | "PERMD" =>
      match srcs with
      | [.reg src, .reg idx] => some (.perm dst src idx)
      | _ => none
  | "BLENDMD" =>
      match srcs with
      | [.reg k, .reg a, .reg b] => some (.blend dst k a b)
      | _ => none
  | "TERNLOG" =>
      match srcs with
      | [.reg a, .reg b, .reg c, .imm t] => some (.tern (BitVec.ofNat 8 t) dst a b c)
      | _ => none
  | "LOADIDX" =>
      match srcs, tag with
      | [.arrIdx b idx _], .load 64 n => some (.load n dst b idx)
      | _, _ => none
  | "STOREIDX" =>
      match srcs, tag with
      | [.arrIdx b idx _, .reg val], .store 64 n => some (.store n dst b idx val)
      | _, _ => none
  | m =>
      match srcs with
      | [.reg a, .reg b, .imm L] => (lopOfName? m).map fun o => .op L o dst a b
      | _ => none

/-- **The recogniser of the vector instructions**: an `Lopn` with one register destination
    and a mnemonic with the characters `V512:` first, read by `vecOfBase?`. -/
def vecArgs? (i : LinstrRM) : Option VecOp :=
  match i.fst with
  | .Lopn [.reg dst] opn srcs =>
      if "V512:".toList.isPrefixOf opn.toList then
        vecOfBase? (String.ofList (opn.toList.drop "V512:".toList.length)) dst srcs i.snd
      else none
  | _ => none

/-- An instruction `vecArgs?` reads is an `Lopn` with one register destination and a
    mnemonic of `FreshMnem`. -/
theorem vecArgs?_wire {i : LinstrRM} (h : vecArgs? i ≠ none) :
    ∃ dst opn srcs, i.fst = .Lopn [.reg dst] opn srcs ∧ FreshMnem opn := by
  unfold vecArgs? at h
  split at h
  · next dst opn srcs heq =>
    split at h
    · next hp =>
      obtain ⟨t, ht⟩ := List.isPrefixOf_iff_prefix.mp hp
      refine ⟨dst, opn, srcs, heq, 'V', '5' :: '1' :: '2' :: ':' :: t, ?_, by decide⟩
      rw [← ht]
      rfl
    · exact absurd rfl h
  · exact absurd rfl h

/-- A control instruction is no vector instruction. -/
theorem vecArgs?_of_isCtl {i : LinstrRM} (h : isCtl i.fst = true) : vecArgs? i = none := by
  obtain ⟨x, tag⟩ := i
  cases x <;> simp_all [isCtl, vecArgs?]

/-- The eight elements of an array from index `i`, as lanes of 64 bits; an element outside
    the array reads zero. -/
def loadLanes {n : Nat} (arr : Fin n → BitVec 64) (i : Nat) : BitVec 512 :=
  ofLanes 64 (fun k => if h : i + k < n then arr ⟨i + k, h⟩ else 0)

/-- The array with the eight lanes of `x` written from index `i`; a lane outside the array
    is dropped. -/
def storeLanes {n : Nat} (arr : Fin n → BitVec 64) (i : Nat) (x : BitVec 512) :
    Fin n → BitVec 64 :=
  fun j => if i ≤ j.val ∧ j.val < i + 8 then lane 64 x (j.val - i) else arr j

/-- **The step of a vector instruction** on the base state: the sources are read at width
    512 (the mask of a blend at width 16, an index at width 64), the destination register
    is written with the value of the semantic functions of `ZmmTextModel` (a store writes
    the destination array), and the program counter advances. A source of another width
    has no step. -/
def vecStep (q : VecOp) (s : LstateM) : Option LstateM :=
  match q with
  | .op L o dst a b =>
      match s.reg.getW a 512, s.reg.getW b 512 with
      | some x, some y => some ((s.setReg dst (semLW L o x y)).nextPc)
      | _, _ => none
  | .shi L l imm dst a =>
      match s.reg.getW a 512 with
      | some x => some ((s.setReg dst (semShImm L l imm x)).nextPc)
      | none => none
  | .rol L imm dst a =>
      match s.reg.getW a 512 with
      | some x => some ((s.setReg dst (semRol L imm x)).nextPc)
      | none => none
  | .dup odd dst a =>
      match s.reg.getW a 512 with
      | some x => some ((s.setReg dst (semDup odd x)).nextPc)
      | none => none
  | .mova dst a =>
      match s.reg.getW a 512 with
      | some x => some ((s.setReg dst x).nextPc)
      | none => none
  | .perm dst src idx =>
      match s.reg.getW src 512, s.reg.getW idx 512 with
      | some x, some y => some ((s.setReg dst (semPerm 16 x y)).nextPc)
      | _, _ => none
  | .blend dst k a b =>
      match s.reg.getW k 16, s.reg.getW a 512, s.reg.getW b 512 with
      | some m, some x, some y => some ((s.setReg dst (semMerge m x y)).nextPc)
      | _, _, _ => none
  | .tern imm dst a b c =>
      match s.reg.getW a 512, s.reg.getW b 512, s.reg.getW c 512 with
      | some x, some y, some z => some ((s.setReg dst (semTern imm x y z)).nextPc)
      | _, _, _ => none
  | .load n dst base idx =>
      match s.getArr base 64 n, s.reg.getW idx 64 with
      | some arr, some vi => some ((s.setReg dst (loadLanes arr vi.toNat)).nextPc)
      | _, _ => none
  | .store n dst base idx val =>
      match s.getArr base 64 n, s.reg.getW idx 64, s.reg.getW val 512 with
      | some arr, some vi, some x => some ((s.setArr dst (storeLanes arr vi.toNat x)).nextPc)
      | _, _, _ => none

/-- Every vector step advances the program counter by one. -/
theorem vecStep_lpc (q : VecOp) (s s' : LstateM) (h : vecStep q s = some s') :
    s'.reg.lpc = s.reg.lpc + 1 := by
  unfold vecStep at h
  cases q <;> dsimp only at h <;> split at h <;>
    first
      | (obtain rfl := Option.some.inj h; rfl)
      | exact absurd h (by simp)

/-- A vector step keeps the carry and overflow flags. -/
theorem vecStep_flags (q : VecOp) (s s' : LstateM) (h : vecStep q s = some s') :
    s'.cf = s.cf ∧ s'.of = s.of := by
  unfold vecStep at h
  cases q <;> dsimp only at h <;> split at h <;>
    first
      | (obtain rfl := Option.some.inj h; exact ⟨rfl, rfl⟩)
      | exact absurd h (by simp)

end CatCrypt.Crypto.SecureCompilation.VIR.VecIsa

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.VecIsa

namespace Isa

variable (I : Isa)

/-- **The instruction set with the vector step.** The record `I` with its step replaced, on
    an instruction `vecArgs?` reads, by `vecStep` on the base state; the step of every other
    instruction, the data and the branch condition are those of `I`. -/
def withVec : Isa :=
  { I with
    step := fun P i s =>
      match vecArgs? i with
      | some q => (vecStep q s.prog.base).map fun b => { s with prog := { s.prog with base := b } }
      | none => I.step P i s
    step_ctl := fun P i s h => by
      simp only [vecArgs?_of_isCtl h]
      exact I.step_ctl P i s h }

@[simp] theorem withVec_toIsaData : I.withVec.toIsaData = I.toIsaData := rfl

@[simp] theorem withVec_condEval : I.withVec.condEval = I.condEval := rfl

/-- The step of a vector instruction is `vecStep` on the base state. -/
theorem withVec_step_vec (P : LprogM) (i : LinstrRM) (s : LstateMF) {q : VecOp}
    (h : vecArgs? i = some q) :
    I.withVec.step P i s =
      (vecStep q s.prog.base).map fun b => { s with prog := { s.prog with base := b } } := by
  simp only [withVec, h]

/-- The step of an instruction that is no vector instruction is the step of `I`. -/
theorem withVec_step_of_none (P : LprogM) (i : LinstrRM) (s : LstateMF)
    (h : vecArgs? i = none) : I.withVec.step P i s = I.step P i s := by
  simp only [withVec, h]

/-- **A vector step advances the program counter by one and writes no flag**: the zero
    flag, the carry flag and the overflow flag are unchanged, and so is the function
    name. -/
theorem withVec_step_vec_pc_flags (P : LprogM) (i : LinstrRM) (s s' : LstateMF) {q : VecOp}
    (hq : vecArgs? i = some q) (h : I.withVec.step P i s = some s') :
    s'.prog.base.reg.lpc = s.prog.base.reg.lpc + 1 ∧ s'.zf = s.zf ∧
      s'.prog.base.cf = s.prog.base.cf ∧ s'.prog.base.of = s.prog.base.of ∧
      s'.prog.lfn = s.prog.lfn := by
  rw [I.withVec_step_vec P i s hq, Option.map_eq_some_iff] at h
  obtain ⟨b, hb, rfl⟩ := h
  exact ⟨vecStep_lpc q _ b hb, rfl, (vecStep_flags q _ b hb).1, (vecStep_flags q _ b hb).2, rfl⟩

/-- `I` has no step on an instruction `vecArgs?` reads. -/
def RefusesVec : Prop :=
  ∀ (P : LprogM) (i : LinstrRM) (s : LstateMF), vecArgs? i ≠ none → I.step P i s = none

/-- Every step of an instruction set that refuses the vector instructions is a step of the
    instruction set with the vector step. -/
theorem withVec_stepLe (h : I.RefusesVec) : I.StepLe I.withVec := by
  intro P i s s' hs
  cases hq : vecArgs? i with
  | none => rw [I.withVec_step_of_none P i s hq]; exact hs
  | some q => rw [h P i s (by rw [hq]; exact Option.some_ne_none q)] at hs; cases hs

end Isa

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

namespace CatCrypt.Crypto.SecureCompilation.VIR.VecIsa

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)

/-- **The x86 instruction set refuses the vector instructions.** -/
theorem x86Isa_refusesVec : x86Isa.RefusesVec := by
  intro P i s h
  obtain ⟨w, tag⟩ := i
  obtain ⟨dst, opn, srcs, rfl, hm⟩ := vecArgs?_wire h
  exact evalInstrPMemF_fresh hm P tag s

end CatCrypt.Crypto.SecureCompilation.VIR.VecIsa
