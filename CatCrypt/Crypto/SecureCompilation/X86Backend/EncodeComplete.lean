/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.String.TakeDrop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogJInstrMnemDispatch
public import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherFullBody

@[expose] public section

set_option autoImplicit false

/-!
# Encoder completeness on the spill legalisations

The checked encoder `LprogBytes.encodeLcmdChecked` accepts a body exactly when every
instruction satisfies `encodableLinstrR`. This module proves that predicate on the
instructions the spill legalisations of the physical-ABI allocation
(`physBodyWithStores`) emit, and its preservation by the load forwarding `loadCSE`.

## Operands

The allocation renames every operand of a one-source move, a select and a
materialised comparison to a general-purpose register or a spill slot `k.N`
(`AllocOp`). A slot name resolves to a frame offset when `spillQsaveOff` parses it
(`SlotResolves`). The encoder addresses a name as memory when it is a frame slot or
a `mem.*` cell (`encMemName`).

## Main results

* `encTwoAddr_ne_nil`: the two-address form has bytes when both names resolve and at
  most one is a memory name; `slotResolves_of_encTwoAddr`: a form with bytes has
  resolving names.
* `encodableLinstrR_mov_iff`, `encodableLinstrR_mov`: a register move `MOV`, `MOV:64`
  or `MOVQ` is encodable exactly when its two-address form has bytes, so under the
  same conditions.
* `legalizeMov_encodable`, `legalizeOneSrc_encodable`: every instruction of a
  legalised register copy over allocated operands is encodable.
* `cmovSpillSeq_encodable`: every instruction of the scratch select is encodable when
  the selected values are registers.
* `setccSpill?_encodable`: every instruction of the scratch comparison is encodable
  for the comparisons `SETE` and `SETNE`.
* `legalizeSpillDst_encodable`: the combination, with the encodability of the
  unlegalised instruction as the hypothesis of the fall-through arm.
* `loadCSE_encodable`: `loadCSE` maps a body of encodable instructions to a body of
  encodable instructions, at the same frame size, spill width and save block.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeComplete

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-! ## Non-empty byte forms -/

theorem encAluRRw_ne_nil (w op d s : Nat) : encAluRRw w op d s ≠ [] := by
  simp [encAluRRw]

theorem enc0FRRw_ne_nil (w op d s : Nat) : enc0FRRw w op d s ≠ [] := by
  simp [enc0FRRw]

theorem encMemMovw_ne_nil (w op r base : Nat) (off : Int) : encMemMovw w op r base off ≠ [] := by
  simp [encMemMovw]

theorem encRspMem_ne_nil (w op r : Nat) (off : Int) : encRspMem w op r off ≠ [] := by
  unfold encRspMem
  split_ifs <;> simp

theorem encCmovSelect_ne_nil (w dn cn tn fn : Nat) : encCmovSelect w dn cn tn fn ≠ [] := by
  unfold encCmovSelect
  split_ifs <;> simp [encAluRRw]

theorem encSetccCmp_ne_nil (w op d a b : Nat) : encSetccCmp w op d a b ≠ [] := by
  simp [encSetccCmp, encAluRRw]

/-! ## Operand classes -/

/-- A frame-slot name (`k.N`, `qsave.X`) parses to a frame offset. -/
def SlotResolves (F W Q : Nat) (n : String) : Prop :=
  isSpillOrQsave n = true → (spillQsaveOff F W n Q).isSome = true

/-- A name the encoder addresses as memory: a frame slot or a `mem.*` cell. -/
def encMemName (n : String) : Bool := isSpillOrQsave n || (parseMemName n).isSome

/-- An operand of the allocated body: a general-purpose register, or a spill slot
    `k.N` whose frame offset resolves. -/
def AllocOp (F W Q : Nat) (o : LOperand) : Prop :=
  ∃ n, o = .reg n ∧
    (isGpName n = true ∨ (hasPrefix n "k." = true ∧ (spillQsaveOff F W n Q).isSome = true))

theorem isSpillOrQsave_of_spillQsaveOff {F W Q : Nat} {n : String} {off : Int}
    (h : spillQsaveOff F W n Q = some off) : isSpillOrQsave n = true := by
  unfold spillQsaveOff at h
  unfold isSpillOrQsave
  by_cases hk : hasPrefix n "k." = true
  · simp [hk]
  · by_cases hq : hasPrefix n "qsave." = true
    · simp [hq]
    · simp [hk, hq] at h

theorem spillQsaveOff_of_not {F W Q : Nat} {n : String} (h : isSpillOrQsave n = false) :
    spillQsaveOff F W n Q = none := by
  cases ho : spillQsaveOff F W n Q with
  | none => rfl
  | some off => rw [isSpillOrQsave_of_spillQsaveOff ho] at h; cases h

theorem hasPrefix_mem_of_parseMemName {n : String} {p : Nat × Int}
    (h : parseMemName n = some p) : hasPrefix n "mem." = true := by
  unfold parseMemName at h
  by_cases hm : hasPrefix n "mem." = true
  · exact hm
  · simp [hm] at h

theorem slotResolves_of_isGpName {F W Q : Nat} {n : String} (h : isGpName n = true) :
    SlotResolves F W Q n := fun hq => by
  rw [(notSlotMem_of_isGpName h).1] at hq; cases hq

theorem encMemName_of_isGpName {n : String} (h : isGpName n = true) : encMemName n = false := by
  have := notSlotMem_of_isGpName h
  simp [encMemName, this.1, this.2]

theorem isGpName_of_hasPrefix_k {n : String} (hk : hasPrefix n "k." = true) :
    isGpName n = false := by
  unfold isGpName
  split <;> first | rfl | (exfalso; revert hk; decide)

theorem isSpill_reg (n : String) : (LOperand.reg n).isSpill = hasPrefix n "k." := by
  simp [LOperand.isSpill, PhysAbiShape.isPrefixOf_eq_list, hasPrefix]

theorem isSpillOrQsave_of_k {n : String} (hk : hasPrefix n "k." = true) :
    isSpillOrQsave n = true := by
  simp [isSpillOrQsave, hk]

/-- An allocated name resolves. -/
theorem AllocOp.slotResolves {F W Q : Nat} {n : String} (h : AllocOp F W Q (.reg n)) :
    SlotResolves F W Q n := by
  obtain ⟨m, hm, hc⟩ := h
  simp only [LOperand.reg.injEq] at hm
  subst hm
  rcases hc with hg | ⟨_, hs⟩
  · exact slotResolves_of_isGpName hg
  · exact fun _ => hs

/-- An allocated name is a memory name exactly when it is a spill slot. -/
theorem AllocOp.encMemName_eq {F W Q : Nat} {n : String} (h : AllocOp F W Q (.reg n)) :
    encMemName n = (LOperand.reg n).isSpill := by
  obtain ⟨m, hm, hc⟩ := h
  simp only [LOperand.reg.injEq] at hm
  subst hm
  rw [isSpill_reg]
  rcases hc with hg | ⟨hk, _⟩
  · rw [encMemName_of_isGpName hg]
    cases hk : hasPrefix n "k."
    · rfl
    · rw [isGpName_of_hasPrefix_k hk] at hg; cases hg
  · simp [encMemName, isSpillOrQsave_of_k hk, hk]

theorem isGpName_R15 : isGpName reloadScratch = true := by decide +kernel
theorem isGpName_R14 : isGpName reloadScratch2 = true := by decide +kernel

theorem allocOp_gp {F W Q : Nat} {n : String} (h : isGpName n = true) :
    AllocOp F W Q (.reg n) := ⟨n, rfl, Or.inl h⟩

/-! ## The two-address form -/

/-- **The two-address form has bytes** when both names resolve and at most one is a
    memory name. -/
theorem encTwoAddr_ne_nil {F W Q w op : Nat} {d s : String}
    (hd : SlotResolves F W Q d) (hs : SlotResolves F W Q s)
    (hm : (encMemName d && encMemName s) = false) :
    encTwoAddr F W w op (.reg d) (.reg s) Q ≠ [] := by
  unfold encTwoAddr
  cases hod : spillQsaveOff F W d Q with
  | some od =>
    have hqd := isSpillOrQsave_of_spillQsaveOff hod
    have hqs : isSpillOrQsave s = false := by
      cases hqs : isSpillOrQsave s
      · rfl
      · simp [encMemName, hqd, hqs] at hm
    simp [hod, spillQsaveOff_of_not hqs (F := F) (W := W) (Q := Q), hqs, encRspMem_ne_nil]
  | none =>
    have hqd : isSpillOrQsave d = false := by
      cases h : isSpillOrQsave d
      · rfl
      · have := hd h; rw [hod] at this; cases this
    cases hos : spillQsaveOff F W s Q with
    | some os =>
      simp [hod, hos, hqd, encRspMem_ne_nil]
    | none =>
      have hqs : isSpillOrQsave s = false := by
        cases h : isSpillOrQsave s
        · rfl
        · have := hs h; rw [hos] at this; cases this
      simp only [hod, hos, hqd, hqs, Bool.or_self, Bool.false_eq_true, if_false]
      cases hpd : parseMemName d <;> cases hps : parseMemName s
      · simp [encAluRRw_ne_nil]
      · simp [encMemMovw_ne_nil]
      · simp [encMemMovw_ne_nil]
      · simp [encMemName, hpd, hps] at hm

/-- **A two-address form with bytes has resolving names.** -/
theorem slotResolves_of_encTwoAddr {F W Q w op : Nat} {d s : String}
    (h : encTwoAddr F W w op (.reg d) (.reg s) Q ≠ []) :
    SlotResolves F W Q d ∧ SlotResolves F W Q s := by
  refine ⟨fun hq => ?_, fun hq => ?_⟩
  · cases hod : spillQsaveOff F W d Q
    · exfalso
      apply h
      unfold encTwoAddr
      cases hos : spillQsaveOff F W s Q <;> simp [hod, hos, hq]
    · rfl
  · cases hos : spillQsaveOff F W s Q
    · exfalso
      apply h
      unfold encTwoAddr
      cases hod : spillQsaveOff F W d Q <;> simp [hod, hos, hq]
    · rfl

/-! ## Register moves -/

/-- The register-move mnemonics of the exporter and its legalisations. -/
def isMovMnem (mn : String) : Bool := mn == "MOV" || mn == "MOV:64" || mn == "MOVQ"

/-- The one-source dispatch of a two-address mnemonic at the width of its tag. -/
theorem dispatch_alu_one_w
    (frame spillW op : Nat) (mnem base : String) (dn sn : String) (qsaveB : Nat)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = false)
    (hadx : adxPrefix base = none) (halu : aluOpcode base = some op)
    (htag : tagShiftExt base = none) :
    encodeLopn frame spillW (.Lopn [.reg dn] mnem [.reg sn]) qsaveB
      = encTwoAddr frame spillW (rexW (mnemWidth mnem)) op (.reg dn) (.reg sn) qsaveB := by
  simp only [encodeLopn, hbind, hstrip, hmulx, hmulxmem, hadx, halu, htag,
    Bool.false_eq_true, if_false]

/-- A register move dispatches to the two-address move form. -/
theorem encodeLopn_movAny {F W Q : Nat} {mn : String} (d s : String) (hm : isMovMnem mn = true) :
    encodeLopn F W (.Lopn [.reg d] mn [.reg s]) Q
      = encTwoAddr F W (rexW (mnemWidth mn)) 0x89 (.reg d) (.reg s) Q := by
  simp only [isMovMnem, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with (rfl | rfl) | rfl
  · exact dispatch_alu_one_w F W 0x89 "MOV" "MOV" d s Q (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact dispatch_alu_one_w F W 0x89 "MOV:64" "MOV" d s Q (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · exact dispatch_alu_one_w F W 0x89 "MOVQ" "MOVQ" d s Q (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

theorem carriesNoBytes_mov {mn : String} (d s : String) (hm : isMovMnem mn = true) :
    carriesNoBytes (.Lopn [.reg d] mn [.reg s]) = false := by
  simp only [isMovMnem, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with (rfl | rfl) | rfl <;>
    simp [carriesNoBytes, show isMulHiBinding "MOV" = false from by decide +kernel,
      show isMulHiBinding "MOV:64" = false from by decide +kernel,
      show isMulHiBinding "MOVQ" = false from by decide +kernel,
      show isIdentityTagShift "MOV" = false from by decide +kernel,
      show isIdentityTagShift "MOV:64" = false from by decide +kernel,
      show isIdentityTagShift "MOVQ" = false from by decide +kernel]

/-- A register move is encodable exactly when its two-address form has bytes. -/
theorem encodableLinstrR_mov_iff {F W Q : Nat} {mn d s : String} (hm : isMovMnem mn = true) :
    encodableLinstrR F W (.Lopn [.reg d] mn [.reg s]) Q = true ↔
      encTwoAddr F W (rexW (mnemWidth mn)) 0x89 (.reg d) (.reg s) Q ≠ [] := by
  simp [encodableLinstrR, encodeLinstrR, encodeLopn_movAny d s hm, carriesNoBytes_mov d s hm]

/-- **A register move is encodable** when both names resolve and at most one is a
    memory name. -/
theorem encodableLinstrR_mov {F W Q : Nat} {mn d s : String} (hm : isMovMnem mn = true)
    (hd : SlotResolves F W Q d) (hs : SlotResolves F W Q s)
    (hds : (encMemName d && encMemName s) = false) :
    encodableLinstrR F W (.Lopn [.reg d] mn [.reg s]) Q = true :=
  (encodableLinstrR_mov_iff hm).2 (encTwoAddr_ne_nil hd hs hds)

/-- An encodable register move has resolving names. -/
theorem slotResolves_of_encodableLinstrR_mov {F W Q : Nat} {mn d s : String}
    (hm : isMovMnem mn = true) (h : encodableLinstrR F W (.Lopn [.reg d] mn [.reg s]) Q = true) :
    SlotResolves F W Q d ∧ SlotResolves F W Q s :=
  slotResolves_of_encTwoAddr ((encodableLinstrR_mov_iff hm).1 h)

/-- A move between an allocated operand and a general-purpose register is encodable,
    in either direction. -/
theorem encodableLinstrR_mov_gp_left {F W Q : Nat} {mn r n : String} (hm : isMovMnem mn = true)
    (hr : isGpName r = true) (hn : AllocOp F W Q (.reg n)) :
    encodableLinstrR F W (.Lopn [.reg r] mn [.reg n]) Q = true :=
  encodableLinstrR_mov hm (slotResolves_of_isGpName hr) hn.slotResolves
    (by simp [encMemName_of_isGpName hr])

theorem encodableLinstrR_mov_gp_right {F W Q : Nat} {mn r n : String} (hm : isMovMnem mn = true)
    (hr : isGpName r = true) (hn : AllocOp F W Q (.reg n)) :
    encodableLinstrR F W (.Lopn [.reg n] mn [.reg r]) Q = true :=
  encodableLinstrR_mov hm hn.slotResolves (slotResolves_of_isGpName hr)
    (by simp [encMemName_of_isGpName hr])

/-! ## The legalised register copy -/

/-- **Every instruction of a legalised register copy over allocated operands is
    encodable.** -/
theorem legalizeMov_encodable {F W Q : Nat} {d s : LOperand} {mov : String}
    (hm : isMovMnem mov = true) (hd : AllocOp F W Q d) (hs : AllocOp F W Q s) :
    ∀ i ∈ legalizeMov d s mov, encodableLinstrR F W i Q = true := by
  obtain ⟨dn, rfl, hd'⟩ := hd
  obtain ⟨sn, rfl, hs'⟩ := hs
  have hd : AllocOp F W Q (.reg dn) := ⟨dn, rfl, hd'⟩
  have hs : AllocOp F W Q (.reg sn) := ⟨sn, rfl, hs'⟩
  intro i hi
  unfold legalizeMov at hi
  split_ifs at hi with hb
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact encodableLinstrR_mov_gp_left hm isGpName_R15 hs
    · exact encodableLinstrR_mov_gp_right hm isGpName_R15 hd
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi
    refine encodableLinstrR_mov hm hd.slotResolves hs.slotResolves ?_
    rw [hd.encMemName_eq, hs.encMemName_eq]
    simpa using hb

theorem stripWidthTag_of_isMovMnem {mn : String} (hm : isMovMnem mn = true) :
    (stripWidthTag mn == "MOV" || stripWidthTag mn == "MOVQ") = true := by
  simp only [isMovMnem, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with (rfl | rfl) | rfl <;> decide +kernel

/-- **Every instruction of the one-source arm of the allocation on a register move
    over allocated operands is encodable.** -/
theorem legalizeOneSrc_encodable {F W Q : Nat} {u64 : Bool} {opn : String} {d s : LOperand}
    (hm : isMovMnem opn = true) (hd : AllocOp F W Q d) (hs : AllocOp F W Q s) :
    ∀ i ∈ legalizeOneSrc u64 opn d s, encodableLinstrR F W i Q = true := by
  have hsm : spillImmMovMnem u64 opn d s = opn := by
    obtain ⟨sn, rfl, -⟩ := hs
    rfl
  unfold legalizeOneSrc
  rw [if_pos (stripWidthTag_of_isMovMnem hm), hsm]
  exact legalizeMov_encodable hm hd hs

/-! ## The scratch select -/

theorem carriesNoBytes_cmov64 (dn cn tn fn : String) :
    carriesNoBytes (.Lopn [.reg dn] "CMOV:64" [.reg cn, .reg tn, .reg fn]) = false := by
  simp [carriesNoBytes, show isMulHiBinding "CMOV:64" = false from by decide +kernel,
    show ("CMOV:64" == "KEEP") = false from by decide +kernel]

/-- A select over four general-purpose registers is encodable. -/
theorem encodableLinstrR_cmov64_gp {F W Q : Nat} {dn cn tn fn : String}
    (hd : isGpName dn = true) (hc : isGpName cn = true) (ht : isGpName tn = true)
    (hf : isGpName fn = true) :
    encodableLinstrR F W (.Lopn [.reg dn] "CMOV:64" [.reg cn, .reg tn, .reg fn]) Q = true := by
  have he := GatherFullBody.encodeLopn_cmov64_emits F W dn cn tn fn Q (by simp [hd, hc, ht, hf])
  simp [encodableLinstrR, encodeLinstrR, he, carriesNoBytes_cmov64,
    encCmovSelect_ne_nil]

theorem isGpName_of_allocOp_not_spill {F W Q : Nat} {n : String} (h : AllocOp F W Q (.reg n))
    (hs : (LOperand.reg n).isSpill = false) : isGpName n = true := by
  obtain ⟨m, hm, hc⟩ := h
  simp only [LOperand.reg.injEq] at hm
  subst hm
  rcases hc with hg | ⟨hk, _⟩
  · exact hg
  · rw [isSpill_reg, hk] at hs; cases hs

/-- **Every instruction of the scratch select is encodable** when the destination and
    the condition are allocated and the selected values are general-purpose
    registers. -/
theorem cmovSpillSeq_encodable {F W Q : Nat} {d c : LOperand} {tn fn : String}
    (hd : AllocOp F W Q d) (hc : AllocOp F W Q c) (ht : isGpName tn = true)
    (hf : isGpName fn = true) :
    ∀ i ∈ cmovSpillSeq "CMOV:64" d c (.reg tn) (.reg fn), encodableLinstrR F W i Q = true := by
  have hm64 : isMovMnem "MOV:64" = true := by decide +kernel
  obtain ⟨dn, rfl, hd'⟩ := hd
  obtain ⟨cn, rfl, hc'⟩ := hc
  have hd : AllocOp F W Q (.reg dn) := ⟨dn, rfl, hd'⟩
  have hc : AllocOp F W Q (.reg cn) := ⟨cn, rfl, hc'⟩
  intro i hi
  unfold cmovSpillSeq at hi
  cases hcs : (LOperand.reg cn).isSpill <;> cases hds : (LOperand.reg dn).isSpill <;>
    simp only [hcs, hds, if_true, if_false, Bool.false_eq_true, List.nil_append,
      List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  · subst hi
    exact encodableLinstrR_cmov64_gp (isGpName_of_allocOp_not_spill hd hds)
      (isGpName_of_allocOp_not_spill hc hcs) ht hf
  · rcases hi with rfl | rfl
    · exact encodableLinstrR_cmov64_gp isGpName_R15 (isGpName_of_allocOp_not_spill hc hcs) ht hf
    · exact encodableLinstrR_mov_gp_right hm64 isGpName_R15 hd
  · rcases hi with rfl | rfl
    · exact encodableLinstrR_mov_gp_left hm64 isGpName_R14 hc
    · exact encodableLinstrR_cmov64_gp (isGpName_of_allocOp_not_spill hd hds) isGpName_R14 ht hf
  · rcases hi with rfl | rfl | rfl
    · exact encodableLinstrR_mov_gp_left hm64 isGpName_R14 hc
    · exact encodableLinstrR_cmov64_gp isGpName_R15 isGpName_R14 ht hf
    · exact encodableLinstrR_mov_gp_right hm64 isGpName_R15 hd

/-! ## The scratch comparison -/

/-- The materialised comparisons the encoder builds: `SETE` and `SETNE`, untagged or
    at the `:64` tag. -/
def isSetccEncMnem (opn : String) : Bool :=
  opn == "SETE" || opn == "SETNE" || opn == "SETE:64" || opn == "SETNE:64"

/-- The materialised-comparison dispatch: a mnemonic whose base is in none of the
    tables before the comparison arm reaches `encSetccCmp`. -/
theorem dispatch_setcc (frame spillW op : Nat) (mnem base : String) (dn an sn : String)
    (qsaveB : Nat)
    (hbind : (isCarryOutBinding mnem || isMulHiBinding mnem) = false)
    (hstrip : stripWidthTag mnem = base)
    (hmulx : (base == "MULX") = false) (hmulxmem : (base == "MULXMEM") = false)
    (hadx : adxPrefix base = none) (htag : tagShiftExt base = none)
    (halu : aluOpcode base = none) (h0f : twoByteOpcode base = none)
    (hst : (base == "STOREIDX") = false) (hcmp : (base == "CMP") = false)
    (hsh : (base == "SHL" || base == "SHR" || base == "SAR") = false)
    (hcc : setccCmpOp base = some op)
    (hgp : (isGpName dn && isGpName an && isGpName sn) = true) :
    encodeLopn frame spillW (.Lopn [.reg dn] mnem [.reg an, .reg sn]) qsaveB
      = encSetccCmp (rexW (mnemWidth mnem)) op (gpNumU dn) (gpNumU an) (gpNumU sn) := by
  simp only [Bool.or_eq_false_iff] at hsh
  obtain ⟨⟨hshl, hshr⟩, hsar⟩ := hsh
  simp only [encodeLopn, hbind, hstrip, hmulx, hmulxmem, hadx, htag, halu, h0f, hst, hcmp,
    hshl, hshr, hsar, hcc, hgp, Bool.or_false, Bool.false_eq_true, if_false, if_true]

theorem encodeLopn_setcc_ne_nil {F W Q : Nat} {opn dn an sn : String}
    (ho : isSetccEncMnem opn = true)
    (hd : isGpName dn = true) (ha : isGpName an = true) (hs : isGpName sn = true) :
    encodeLopn F W (.Lopn [.reg dn] opn [.reg an, .reg sn]) Q ≠ [] := by
  have hgp : (isGpName dn && isGpName an && isGpName sn) = true := by simp [hd, ha, hs]
  simp only [isSetccEncMnem, Bool.or_eq_true, beq_iff_eq] at ho
  rcases ho with ((rfl | rfl) | rfl) | rfl
  · rw [dispatch_setcc F W 0x94 "SETE" "SETE" dn an sn Q (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hgp]
    exact encSetccCmp_ne_nil _ _ _ _ _
  · rw [dispatch_setcc F W 0x95 "SETNE" "SETNE" dn an sn Q (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hgp]
    exact encSetccCmp_ne_nil _ _ _ _ _
  · rw [dispatch_setcc F W 0x94 "SETE:64" "SETE" dn an sn Q (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hgp]
    exact encSetccCmp_ne_nil _ _ _ _ _
  · rw [dispatch_setcc F W 0x95 "SETNE:64" "SETNE" dn an sn Q (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) hgp]
    exact encSetccCmp_ne_nil _ _ _ _ _

/-- A materialised comparison `SETE`/`SETNE` over three general-purpose registers is
    encodable. -/
theorem encodableLinstrR_setcc_gp {F W Q : Nat} {opn dn an sn : String}
    (ho : isSetccEncMnem opn = true)
    (hd : isGpName dn = true) (ha : isGpName an = true) (hs : isGpName sn = true) :
    encodableLinstrR F W (.Lopn [.reg dn] opn [.reg an, .reg sn]) Q = true := by
  have he := encodeLopn_setcc_ne_nil (F := F) (W := W) (Q := Q) ho hd ha hs
  simp [encodableLinstrR, encodeLinstrR, he]

theorem isMovMnem_setccMov (opn : String) : isMovMnem (setccMov opn) = true := by
  unfold setccMov
  split <;> decide +kernel

/-- **Every instruction of the scratch comparison is encodable** for the comparisons
    `SETE` and `SETNE` over allocated operands. -/
theorem setccSpill?_encodable {F W Q : Nat} {dsts : List LOperand} {opn : String}
    {srcs : List LOperand} {l : List LinstrR} (h : setccSpill? dsts opn srcs = some l)
    (ho : isSetccEncMnem opn = true) (hd : ∀ o ∈ dsts, AllocOp F W Q o)
    (hs : ∀ o ∈ srcs, AllocOp F W Q o) :
    ∀ i ∈ l, encodableLinstrR F W i Q = true := by
  unfold setccSpill? at h
  split at h
  · rename_i d a b
    split_ifs at h
    cases h
    have hdd := hd d (by simp)
    have ha := hs (.reg a) (by simp)
    have hb := hs (.reg b) (by simp)
    obtain ⟨dn, rfl, -⟩ := hdd
    have hm := isMovMnem_setccMov opn
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact encodableLinstrR_mov_gp_left hm isGpName_R15 ha
    · exact encodableLinstrR_mov_gp_left hm isGpName_R14 hb
    · exact encodableLinstrR_setcc_gp ho isGpName_R15 isGpName_R15 isGpName_R14
    · exact encodableLinstrR_mov_gp_right hm isGpName_R15 (hd _ (by simp))
  · cases h

/-! ## The spill legalisation of a general instruction -/

/-- **Every instruction of `legalizeSpillDst` is encodable**, for allocated operands:
    the scratch select when its selected values are registers, the scratch comparison
    when it is `SETE` or `SETNE`, and the single instruction when it is itself
    encodable. -/
theorem legalizeSpillDst_encodable {F W Q : Nat} {dsts : List LOperand} {opn : String}
    {srcs : List LOperand}
    (hd : ∀ o ∈ dsts, AllocOp F W Q o) (hs : ∀ o ∈ srcs, AllocOp F W Q o)
    (hsel : ∀ c t f, srcs = [c, t, f] → opn = "CMOV:64" →
      ∃ tn fn, t = .reg tn ∧ f = .reg fn ∧ isGpName tn = true ∧ isGpName fn = true)
    (hcmp : isSetccMnem opn = true → isSetccEncMnem opn = true)
    (hone : cmovSpillDst? dsts opn srcs = none → setccSpill? dsts opn srcs = none →
      encodableLinstrR F W (.Lopn dsts opn srcs) Q = true) :
    ∀ i ∈ legalizeSpillDst dsts opn srcs, encodableLinstrR F W i Q = true := by
  unfold legalizeSpillDst
  cases hc : cmovSpillDst? dsts opn srcs with
  | some l =>
    simp only
    unfold cmovSpillDst? at hc
    split at hc
    · rename_i d c t f
      split_ifs at hc with hb
      cases hc
      have hop : opn = "CMOV:64" := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        exact hb.2
      obtain ⟨tn, fn, rfl, rfl, ht, hf⟩ := hsel c t f rfl hop
      subst hop
      exact cmovSpillSeq_encodable (hd d (by simp)) (hs c (by simp)) ht hf
    · cases hc
  | none =>
    cases hs' : setccSpill? dsts opn srcs with
    | some l =>
      simp only
      have hset : isSetccMnem opn = true := by
        unfold setccSpill? at hs'
        split at hs'
        · split_ifs at hs' with hb
          · exact (Bool.and_eq_true _ _ ▸ hb).2
        · cases hs'
      exact setccSpill?_encodable hs' (hcmp hset) hd hs
    | none =>
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro i rfl
      exact hone hc hs'

/-! ## Load forwarding -/

section LoadCSE

open CatCrypt.Crypto.Optimizer.LoadCSE

/-- A memory name of the encoder is a memory name of the load forwarding. -/
theorem isMemName_of_encMemName {n : String} (h : encMemName n = true) : isMemName n = true := by
  simp only [encMemName, Bool.or_eq_true, Option.isSome_iff_exists] at h
  simp only [isMemName, Bool.or_eq_true, PhysAbiShape.isPrefixOf_eq_list]
  rcases h with hq | ⟨p, hp⟩
  · simp only [isSpillOrQsave, hasPrefix, Bool.or_eq_true] at hq
    rcases hq with hk | hq
    · exact Or.inl (Or.inl hk)
    · exact Or.inl (Or.inr hq)
  · exact Or.inr (hasPrefix_mem_of_parseMemName hp)

theorem isMovMnem_of_isMov64Mnem {mn : String} (h : isMov64Mnem mn = true) :
    isMovMnem mn = true := by
  simp only [isMov64Mnem, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> decide +kernel

/-- The load environment holds only names that resolve. -/
def EnvResolves (F W Q : Nat) (h : LoadEnv) : Prop := ∀ p ∈ h, SlotResolves F W Q p.2

/-- **One forwarding step keeps an encodable instruction encodable** and the
    environment resolving. -/
theorem stepLoad_encodable {F W Q : Nat} (h : LoadEnv) (i : Linstr) (hh : EnvResolves F W Q h)
    (hi : encodableLinstrR F W i.li_i Q = true) :
    encodableLinstrR F W (stepLoad h i).1.li_i Q = true ∧
      EnvResolves F W Q (stepLoad h i).2 := by
  cases hr : asWideReload i.li_i with
  | none =>
    refine ⟨by simp only [stepLoad, hr]; exact hi, ?_⟩
    simp only [stepLoad, hr]
    intro p hp
    exact hh p ((mem_foldl_killReg _ _ p (mem_foldl_killSlot _ _ p hp).1).1)
  | some dsm =>
    obtain ⟨d, s, mn⟩ := dsm
    obtain ⟨hli, hm⟩ := asWideReload_eq hr
    have hmv := isMovMnem_of_isMov64Mnem hm
    rw [hli] at hi
    obtain ⟨hd, -⟩ := slotResolves_of_encodableLinstrR_mov hmv hi
    have henv : EnvResolves F W Q (((h.killReg d).killSlot d).set s d) := by
      intro p hp
      rcases CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad.mem_set hp with
        ⟨hp', _⟩ | rfl
      · exact hh p (mem_killReg (mem_killSlot hp').1).1
      · exact hd
    cases hf : h.find s with
    | none =>
      simp only [stepLoad, hr, hf]
      exact ⟨by rw [hli]; exact hi, henv⟩
    | some r =>
      have hrr : SlotResolves F W Q r :=
        hh (s, r) (CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad.mem_of_find hf)
      by_cases hrd : r = d
      · simp only [stepLoad, hr, hf, hrd, if_true]
        exact ⟨by rw [hli]; exact hi, by simpa [hrd] using henv⟩
      · by_cases hmm : isMemName d = true ∧ isMemName r = true
        · simp only [stepLoad, hr, hf, hrd, if_false, if_pos hmm]
          exact ⟨by rw [hli]; exact hi, henv⟩
        · simp only [stepLoad, hr, hf, hrd, if_false, if_neg hmm]
          refine ⟨encodableLinstrR_mov hmv hd hrr ?_, henv⟩
          cases hed : encMemName d <;> cases her : encMemName r
          all_goals first
            | rfl
            | exact absurd ⟨isMemName_of_encMemName hed, isMemName_of_encMemName her⟩ hmm

/-- **`loadCSE` preserves encodability**: at a fixed frame size, spill width and save
    block, a body of encodable instructions is forwarded to a body of encodable
    instructions. -/
theorem loadCSE_encodable {F W Q : Nat} (body : List Linstr)
    (hb : ∀ i ∈ body, encodableLinstrR F W i.li_i Q = true) :
    ∀ i ∈ loadCSE body, encodableLinstrR F W i.li_i Q = true := by
  rw [loadCSE_eq]
  suffices ∀ (h : LoadEnv) (b : List Linstr), EnvResolves F W Q h →
      (∀ i ∈ b, encodableLinstrR F W i.li_i Q = true) →
      ∀ i ∈ loadCSEAux h b, encodableLinstrR F W i.li_i Q = true from
    this [] body (fun _ hp => by simp at hp) hb
  intro h b
  induction b generalizing h with
  | nil => intro _ _ i hi; simp at hi
  | cons j js ih =>
    intro hh hjs i hi
    rw [loadCSEAux_cons, List.mem_cons] at hi
    have hstep := stepLoad_encodable h j hh (hjs j List.mem_cons_self)
    rcases hi with rfl | hi
    · exact hstep.1
    · exact ih _ hstep.2 (fun k hk => hjs k (List.mem_cons_of_mem j hk)) i hi

end LoadCSE

end CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeComplete
