/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

@[expose] public section

set_option autoImplicit false

/-!
# The x86 flag machine refuses the shadow instructions of calls

A call of a separately provided procedure `f` is the shadow instruction
`LprogIsa.callShadow dst f srcs`, an `Lopn` with one register destination and the mnemonic
`"CALL:" ++ f`. `LprogIsa.shadowCall?` recognises every `Lopn` with one register destination
whose mnemonic has the characters `CALL:` first. This module proves that the x86 flag
machine `evalInstrPMemF` has no step on such an instruction, at every memory tag and from
every state: the mnemonic, and the mnemonic with its width tag `:64` removed, have the
characters `CA` first, so no recogniser of the flag machine and no arm of the straight-line
step reads them.

## Main results

* `stripWidthTag_callMnem`: the mnemonic of a shadow instruction with its width tag removed
  has the characters `CA` first.
* `lsemStepN_callMnem`, `lsemStepMem_callMnem`: the straight-line steps have no step on a
  shadow instruction.
* `evalInstrPMemF_shadowCall`: the flag machine has no step on an instruction recognised by
  `shadowCall?`.
* `x86Isa_refusesProcs`: `x86Isa.RefusesProcs T` for every procedure table `T`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs

open CatCrypt.Crypto.SecureCompilation.VIR
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
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)

/-! ## 1. The mnemonic -/

/-- A mnemonic whose characters start with `CALL:`. -/
def CallMnem (opn : String) : Prop :=
  ∃ t, opn.toList = 'C' :: 'A' :: 'L' :: 'L' :: ':' :: t

/-- An instruction recognised by `shadowCall?` is an `Lopn` with one register destination
    and a mnemonic of `CallMnem`. -/
theorem shadowCall?_wire {i : LinstrR} (h : shadowCall? i ≠ none) :
    ∃ dst opn srcs, i = .Lopn [.reg dst] opn srcs ∧ CallMnem opn := by
  unfold shadowCall? at h
  split at h
  · next dst opn srcs =>
    split at h
    · next hp =>
      obtain ⟨t, ht⟩ := List.isPrefixOf_iff_prefix.mp hp
      refine ⟨dst, opn, srcs, rfl, t, ?_⟩
      rw [← ht]
      rfl
    · exact absurd rfl h
  · exact absurd rfl h

/-- A mnemonic of `CallMnem` differs from every mnemonic whose first three characters are
    not `CAL`. -/
theorem CallMnem.ne {opn : String} (h : CallMnem opn) (lit : String)
    (hl : (lit.toList.take 3 == ['C', 'A', 'L']) = false) : ¬ opn = lit := by
  obtain ⟨t, ht⟩ := h
  rintro rfl
  rw [ht] at hl
  simp at hl

/-- **The mnemonic without its width tag.** A mnemonic of `CallMnem` with the width tag
    `:64` removed has the characters `CA` first. -/
theorem stripWidthTag_callMnem {opn : String} (h : CallMnem opn) :
    ∃ r, (stripWidthTag opn).toList = 'C' :: 'A' :: r := by
  obtain ⟨t, ht⟩ := h
  unfold stripWidthTag
  split
  · rw [String.toList_ofList, ht]
    exact ⟨_, rfl⟩
  · split
    · rw [String.toList_ofList, ht]
      exact ⟨_, rfl⟩
    · rw [ht]
      exact ⟨_, rfl⟩

/-- A mnemonic of `CallMnem` with its width tag removed differs from every mnemonic whose
    first two characters are not `CA`. -/
theorem CallMnem.strip_ne {opn : String} (h : CallMnem opn) (lit : String)
    (hl : (lit.toList.take 2 == ['C', 'A']) = false) : ¬ stripWidthTag opn = lit := by
  obtain ⟨r, hr⟩ := stripWidthTag_callMnem h
  intro he
  rw [← he, hr] at hl
  simp at hl

/-- The operation table `applyOpnN` has no entry at a mnemonic whose first two characters
    are `CA`. -/
theorem applyOpnN_none_of_ca {w : Nat} {m : String} {r : List Char}
    (h : m.toList = 'C' :: 'A' :: r) (l : List (BitVec w)) : applyOpnN w m l = none := by
  unfold applyOpnN
  have h' : m.toList.head? = some 'C' := by rw [h]; rfl
  clear h
  split <;> first | rfl | exact absurd h' (by decide)

/-- The first group of a character list that starts with a character other than the
    separator starts with that character. -/
theorem splitChars_head (c : Char) (hc : c ≠ ':') (l : List Char) :
    ∃ g gs, splitChars ':' (c :: l) = (c :: g) :: gs := by
  simp only [splitChars, ite_eq_right hc]
  split
  · exact ⟨[], [], rfl⟩
  · exact ⟨_, _, rfl⟩

/-- A mnemonic of `CallMnem` is no count-tagged immediate shift. -/
theorem immShiftMnem?_callMnem {opn : String} (h : CallMnem opn) : immShiftMnem? opn = none := by
  have hcore : ∃ r, (stripWidthTag opn).toList = 'C' :: r := by
    obtain ⟨r, hr⟩ := stripWidthTag_callMnem h
    exact ⟨_, hr⟩
  obtain ⟨r, hr⟩ := hcore
  obtain ⟨g, gs, hg⟩ := splitChars_head 'C' (by decide) r
  unfold immShiftMnem?
  simp only [hr, hg]
  split
  · next mn ds heq =>
    obtain ⟨rfl, -⟩ := List.cons.inj heq
    have hne : ∀ lit : String, lit.toList.head? ≠ some 'C' →
        (String.ofList ('C' :: g) == lit) = false := by
      intro lit hl
      rw [beq_eq_false_iff_ne]
      rintro rfl
      rw [String.toList_ofList] at hl
      exact hl rfl
    simp only [hne "SHL" (by decide), hne "SHR" (by decide), hne "SAR" (by decide),
      Bool.or_self, Bool.false_eq_true, ite_false]
  · rfl

/-! ## 2. The straight-line steps -/

variable {dst opn : String} {srcs : List LOperand}

/-- The width-aware step has no step on a shadow instruction. -/
theorem lsemStepN_callMnem (h : CallMnem opn) (s : LstateN) :
    lsemStepN (.Lopn [.reg dst] opn srcs) s = none := by
  obtain ⟨r, hr⟩ := stripWidthTag_callMnem h
  have hap : ∀ (w : Nat) (l : List (BitVec w)), applyOpnN w (stripWidthTag opn) l = none :=
    fun w l => applyOpnN_none_of_ca hr l
  have h1 := h.strip_ne "CMOV" (by decide)
  have h2 := h.strip_ne "MOV" (by decide)
  have h3 := h.strip_ne "NEG" (by decide)
  have h4 := h.strip_ne "LEA" (by decide)
  have h5 : cmpOfName? (stripWidthTag opn) = none :=
    cmpOfName?_eq_none (h.strip_ne _ (by decide)) (h.strip_ne _ (by decide))
      (h.strip_ne _ (by decide)) (h.strip_ne _ (by decide)) (h.strip_ne _ (by decide))
      (h.strip_ne _ (by decide))
  unfold lsemStepN
  split <;> first
    | rfl
    | (rename_i heq
       cases heq <;>
         (try simp only [h1, h2, h3, h4, h5, hap, immFirstN, immShiftMnem?_callMnem h, ite_false,
           Option.map_none]) <;>
         repeat' (first | rfl | split))

/-- The shift-aware and the multiply-and-carry steps have no step on a shadow instruction. -/
theorem lsemStepMC_callMnem (h : CallMnem opn) (s : LstateN) :
    lsemStepMC (.Lopn [.reg dst] opn srcs) s = none := by
  have e1 : mulhiStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold mulhiStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.strip_ne _ (by decide)))
  have e2 : adcxStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold adcxStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.strip_ne _ (by decide)))
  have e3 : adcxhiStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold adcxhiStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.strip_ne _ (by decide)))
  have e4 : sbbStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold sbbStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.strip_ne _ (by decide)))
  have e5 : sbbhiStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold sbbhiStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.strip_ne _ (by decide)))
  have e6 : sarStruct? (.Lopn [.reg dst] opn srcs) = none := by
    unfold sarStruct?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (h.strip_ne _ (by decide)))
  simp only [lsemStepMC, lsemStepSh, e1, e2, e3, e4, e5, e6, lsemStepN_callMnem h]

/-- The cast-aware step has no step on a shadow instruction, at every descriptor. -/
theorem lsemStepCast_callMnem (h : CallMnem opn) (cd : Option Nat) (s : LstateN) :
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
      exact ite_eq_right (fun hc => h.strip_ne "MOV" (by decide)
        (JasminLsemCast.stripWidthTag_of_isMovImm hc))
    · rfl
  simp only [lsemStepCast, e1, e2, lsemStepMC_callMnem h]

/-- **The memory step has no step on a shadow instruction**, at every memory tag. -/
theorem lsemStepMem_callMnem (h : CallMnem opn) (tag : MemTag) (s : LstateM) :
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
    simp only [lsemStepMem, e1, e2, e3, e4, e5, e6, lsemStepCast_callMnem h, Option.map_none]

/-! ## 3. The flag machine -/

/-- **The flag machine has no step on a shadow instruction.** An instruction recognised by
    `shadowCall?`, at every memory tag, in every program and from every state, has no step
    of `evalInstrPMemF`. -/
theorem evalInstrPMemF_shadowCall (P : LprogM) (i : LinstrRM) (s : LstateMF)
    (h : shadowCall? i.fst ≠ none) : evalInstrPMemF P i s = none := by
  obtain ⟨w, tag⟩ := i
  obtain ⟨dst, opn, srcs, rfl, hm⟩ := shadowCall?_wire h
  have hI : IsLopn (LinstrR.Lopn [.reg dst] opn srcs, tag) := ⟨_, _, _, rfl⟩
  have e1 : cmpArgs? (LinstrR.Lopn [.reg dst] opn srcs, tag) = none := by
    unfold cmpArgs?
    split <;> first | rfl | (rename_i heq; cases heq; exact ite_eq_right (hm.ne _ (by decide +kernel)))
  have e2 : movRegArgs? (LinstrR.Lopn [.reg dst] opn srcs, tag) = none := by
    unfold movRegArgs?
    split
    · next heq =>
      cases heq
      obtain ⟨t, ht⟩ := hm
      rw [ite_eq_right (CallMnem.strip_ne ⟨t, ht⟩ "MOV" (by decide)),
        copyQ_eq_false_of_toList ht (by decide)]
      rfl
    · rfl
  have e3 : carryArgs? (LinstrR.Lopn [.reg dst] opn srcs, tag) = none := by
    unfold carryArgs?
    split
    · next heq =>
      cases heq
      simp only [hm.ne (withWidthTag 64 "ADC") (by decide +kernel),
        hm.ne (withWidthTag 64 "SBB") (by decide +kernel),
        hm.ne (withWidthTag 64 "ADCX") (by decide +kernel),
        hm.ne (withWidthTag 64 "ADOX") (by decide +kernel), ite_false]
    · rfl
  have e4 : wideArgs? (LinstrR.Lopn [.reg dst] opn srcs, tag) = none := by
    unfold wideArgs?
    split
    · next heq =>
      cases heq
      exact ite_eq_right (hm.ne _ (by decide +kernel))
    · next heq =>
      cases heq
    · rfl
  unfold evalInstrPMemF
  simp only [e1, e2, e3, e4, flagCondCC?, evalInstrPMemL_lopn _ _ _ hI,
    lsemStepMem_callMnem hm, Option.map_none]

/-- **The x86 instruction set refuses the shadow instructions of every procedure table.** -/
theorem x86Isa_refusesProcs (T : ProcTable) : x86Isa.RefusesProcs T := by
  intro P i s h
  refine evalInstrPMemF_shadowCall P i s fun hn => h ?_
  simp only [procCall?, hn, Option.bind_none]

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs
