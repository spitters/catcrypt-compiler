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
public import CatCrypt.Crypto.SecureCompilation.VIR.IsaEncodeComplete

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
(`AllocOp`). A name resolves when it is a general-purpose register, a frame slot whose
offset `spillQsaveOff` parses, or a `mem.*` cell whose base is a general-purpose
register (`OpResolves`). The encoder addresses
a name as memory when it is a frame slot or a `mem.*` cell (`encMemName`).

## Main definitions

* `x86Enc`: the x86 instance of the instruction-level encoder `IsaEncoder`.

## Main results

* `x86Enc_complete`: the x86 encoder satisfies the completeness law `EncoderComplete` for
  the x86 back end; the results on the legalisations and on `loadCSE` below are its
  instances through the generic theorems of `IsaEncodeComplete`.
* `encTwoAddr_ne_nil_iff`: the two-address form has bytes exactly when one name is a
  general-purpose register and the other resolves; `encTwoAddr_ne_nil`: so when both
  names resolve and at most one is a memory name; `opResolves_of_encTwoAddr`: a form
  with bytes has resolving names.
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
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (isMovMnem IsaEncoder AllocOpI
  EncoderComplete)

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

/-- A name the two-address form resolves: a general-purpose register, a frame slot
    (`k.N`, `qsave.X`) whose frame offset parses, or a `mem.*` cell whose base is a
    general-purpose register. -/
def OpResolves (F W Q : Nat) (n : String) : Prop :=
  isGpName n = true ∨ (spillQsaveOff F W n Q).isSome = true ∨ (parseMemNameGp n).isSome = true

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

theorem opResolves_of_isGpName {F W Q : Nat} {n : String} (h : isGpName n = true) :
    OpResolves F W Q n := Or.inl h

theorem isGpName_of_spillQsaveOff {F W Q : Nat} {n : String} {off : Int}
    (h : spillQsaveOff F W n Q = some off) : isGpName n = false := by
  cases hg : isGpName n
  · rfl
  · have hq := (notSlotMem_of_isGpName hg).1
    rw [isSpillOrQsave_of_spillQsaveOff h] at hq; cases hq

theorem isGpName_of_parseMemName {n : String} {p : Nat × Int} (h : parseMemName n = some p) :
    isGpName n = false := by
  cases hg : isGpName n
  · rfl
  · rw [(notSlotMem_of_isGpName hg).2] at h; cases h

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
theorem AllocOp.opResolves {F W Q : Nat} {n : String} (h : AllocOp F W Q (.reg n)) :
    OpResolves F W Q n := by
  obtain ⟨m, hm, hc⟩ := h
  simp only [LOperand.reg.injEq] at hm
  subst hm
  rcases hc with hg | ⟨_, hs⟩
  · exact Or.inl hg
  · exact Or.inr (Or.inl hs)

/-- A resolving name the encoder does not address as memory is a general-purpose
    register. -/
theorem isGpName_of_opResolves {F W Q : Nat} {n : String} (h : OpResolves F W Q n)
    (hm : encMemName n = false) : isGpName n = true := by
  rcases h with hg | hs | hp
  · exact hg
  · obtain ⟨off, ho⟩ := Option.isSome_iff_exists.1 hs
    simp [encMemName, isSpillOrQsave_of_spillQsaveOff ho] at hm
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hp
    simp [encMemName, parseMemName_of_parseMemNameGp hp] at hm

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

/-- **The two-address form has bytes exactly on the resolvable operand pairs**: one
    name is a general-purpose register and the other resolves (a register, a frame
    slot whose offset parses, or a `mem.*` cell with a general-purpose base). -/
theorem encTwoAddr_ne_nil_iff {F W Q w op : Nat} {d s : String} :
    encTwoAddr F W w op (.reg d) (.reg s) Q ≠ [] ↔
      (isGpName d = true ∧ OpResolves F W Q s) ∨ (OpResolves F W Q d ∧ isGpName s = true) := by
  unfold encTwoAddr OpResolves
  cases hod : spillQsaveOff F W d Q with
  | some od =>
    have hgd := isGpName_of_spillQsaveOff hod
    cases hos : spillQsaveOff F W s Q with
    | some os =>
      simp [hod, hos, hgd, isGpName_of_spillQsaveOff hos]
    | none =>
      cases hgs : isGpName s <;> simp [hod, hos, hgd, hgs, encRspMem_ne_nil]
  | none =>
    cases hos : spillQsaveOff F W s Q with
    | some os =>
      have hgs := isGpName_of_spillQsaveOff hos
      cases hgd : isGpName d <;> simp [hod, hos, hgd, hgs, encRspMem_ne_nil]
    | none =>
      cases hpd : parseMemNameGp d with
      | some pd =>
        obtain ⟨bd, od⟩ := pd
        have hgd := isGpName_of_parseMemName (parseMemName_of_parseMemNameGp hpd)
        cases hps : parseMemNameGp s with
        | some ps =>
          obtain ⟨bs, os⟩ := ps
          simp [hod, hos, hpd, hps, hgd,
            isGpName_of_parseMemName (parseMemName_of_parseMemNameGp hps)]
        | none =>
          cases hgs : isGpName s <;> simp [hod, hos, hpd, hps, hgd, hgs, encMemMovw_ne_nil]
      | none =>
        cases hps : parseMemNameGp s with
        | some ps =>
          obtain ⟨bs, os⟩ := ps
          have hgs := isGpName_of_parseMemName (parseMemName_of_parseMemNameGp hps)
          cases hgd : isGpName d <;> simp [hod, hos, hpd, hps, hgd, hgs, encMemMovw_ne_nil]
        | none =>
          cases hgd : isGpName d <;> cases hgs : isGpName s <;>
            simp [hod, hos, hpd, hps, hgd, hgs, encAluRRw_ne_nil]

/-- **The two-address form has bytes** when both names resolve and at most one is a
    memory name. -/
theorem encTwoAddr_ne_nil {F W Q w op : Nat} {d s : String}
    (hd : OpResolves F W Q d) (hs : OpResolves F W Q s)
    (hm : (encMemName d && encMemName s) = false) :
    encTwoAddr F W w op (.reg d) (.reg s) Q ≠ [] := by
  refine encTwoAddr_ne_nil_iff.2 ?_
  cases hmd : encMemName d
  · exact Or.inl ⟨isGpName_of_opResolves hd hmd, hs⟩
  · rw [hmd, Bool.true_and] at hm
    exact Or.inr ⟨hd, isGpName_of_opResolves hs hm⟩

/-- **A two-address form with bytes has resolving names.** -/
theorem opResolves_of_encTwoAddr {F W Q w op : Nat} {d s : String}
    (h : encTwoAddr F W w op (.reg d) (.reg s) Q ≠ []) :
    OpResolves F W Q d ∧ OpResolves F W Q s := by
  rcases encTwoAddr_ne_nil_iff.1 h with ⟨hd, hs⟩ | ⟨hd, hs⟩
  · exact ⟨Or.inl hd, hs⟩
  · exact ⟨hd, Or.inl hs⟩

/-! ## Register moves -/

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
    (hd : OpResolves F W Q d) (hs : OpResolves F W Q s)
    (hds : (encMemName d && encMemName s) = false) :
    encodableLinstrR F W (.Lopn [.reg d] mn [.reg s]) Q = true :=
  (encodableLinstrR_mov_iff hm).2 (encTwoAddr_ne_nil hd hs hds)

/-- An encodable register move has resolving names. -/
theorem opResolves_of_encodableLinstrR_mov {F W Q : Nat} {mn d s : String}
    (hm : isMovMnem mn = true) (h : encodableLinstrR F W (.Lopn [.reg d] mn [.reg s]) Q = true) :
    OpResolves F W Q d ∧ OpResolves F W Q s :=
  opResolves_of_encTwoAddr ((encodableLinstrR_mov_iff hm).1 h)

/-- A move between an allocated operand and a general-purpose register is encodable,
    in either direction. -/
theorem encodableLinstrR_mov_gp_left {F W Q : Nat} {mn r n : String} (hm : isMovMnem mn = true)
    (hr : isGpName r = true) (hn : AllocOp F W Q (.reg n)) :
    encodableLinstrR F W (.Lopn [.reg r] mn [.reg n]) Q = true :=
  encodableLinstrR_mov hm (opResolves_of_isGpName hr) hn.opResolves
    (by simp [encMemName_of_isGpName hr])

theorem encodableLinstrR_mov_gp_right {F W Q : Nat} {mn r n : String} (hm : isMovMnem mn = true)
    (hr : isGpName r = true) (hn : AllocOp F W Q (.reg n)) :
    encodableLinstrR F W (.Lopn [.reg n] mn [.reg r]) Q = true :=
  encodableLinstrR_mov hm hn.opResolves (opResolves_of_isGpName hr)
    (by simp [encMemName_of_isGpName hr])

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

/-- The load environment holds only names that resolve. -/
def EnvResolves (F W Q : Nat) (h : LoadEnv) : Prop := ∀ p ∈ h, OpResolves F W Q p.2

end LoadCSE

/-! ## The x86 encoder -/

/-- **The x86 encoder**: the context of a body is its frame size, spill width and save
    block; an instruction is encodable in a context when `encodableLinstrR` holds there;
    the encoder registers are the general-purpose registers; a name resolves when
    `OpResolves` holds; a spill slot has a frame offset when `spillQsaveOff` parses; the
    memory names are `encMemName`; the materialised comparisons are `isSetccEncMnem`. -/
def x86Enc : IsaEncoder where
  Ctx := Nat × Nat × Nat
  ctx body := (frameSize body, if bodyIsU64 body then 64 else 32, qsaveBytesFor body)
  instr c i := encodableLinstrR c.1 c.2.1 i c.2.2
  reg := isGpName
  resolves c n := OpResolves c.1 c.2.1 c.2.2 n
  slot c n := (spillQsaveOff c.1 c.2.1 n c.2.2).isSome = true
  memName := encMemName
  setcc := isSetccEncMnem

/-- An operand is allocated at a frame size, spill width and save block exactly when it is
    an allocated operand of the x86 encoder in that context. -/
theorem allocOp_iff_allocOpI {F W Q : Nat} {o : LOperand} :
    AllocOp F W Q o ↔ AllocOpI x86Enc (F, W, Q) o := by
  simp only [AllocOp, AllocOpI, x86Enc, isSpill_reg]

/-- **The x86 encoder is complete for the x86 back end.** -/
theorem x86Enc_complete : EncoderComplete VIR.LprogIsa.x86Backend x86Enc where
  encodable_eq _ := rfl
  pool_reg := by decide +kernel
  reload_reg := by decide +kernel
  reloadSnd_reg := by decide +kernel
  reg_resolves _ _ h := Or.inl h
  slot_resolves _ _ h := Or.inr (Or.inl h)
  reg_not_spill n h := by
    rw [isSpill_reg]
    cases hk : hasPrefix n "k."
    · rfl
    · change isGpName n = true at h
      rw [isGpName_of_hasPrefix_k hk] at h; cases h
  reg_not_mem _ h := encMemName_of_isGpName h
  spill_mem n h := by
    rw [isSpill_reg] at h
    simp [x86Enc, encMemName, isSpillOrQsave_of_k h]
  mem_loadCSE _ h := isMemName_of_encMemName h
  mov_iff c mn d s hm := by
    refine (encodableLinstrR_mov_iff hm).trans ⟨fun h => ?_, fun ⟨hd, hs, hds⟩ =>
      encTwoAddr_ne_nil hd hs hds⟩
    obtain ⟨hd, hs⟩ := opResolves_of_encTwoAddr h
    refine ⟨hd, hs, ?_⟩
    rcases encTwoAddr_ne_nil_iff.1 h with ⟨hg, -⟩ | ⟨-, hg⟩
    · show (encMemName d && encMemName s) = false
      simp [encMemName_of_isGpName hg]
    · show (encMemName d && encMemName s) = false
      simp [encMemName_of_isGpName hg]
  select_reg m hm c dn cn tn fn hd hc ht hf := by
    have hm' : m = "CMOV" := (Option.some.inj hm).symm
    subst hm'
    exact encodableLinstrR_cmov64_gp hd hc ht hf
  setcc_reg c opn dn an sn ho hd ha hs := encodableLinstrR_setcc_gp ho hd ha hs

/-- The select mnemonic of the x86 instruction set is `CMOV`. -/
theorem x86Isa_selectMnemonic : X86Isa.x86Isa.selectMnemonic = some "CMOV" := rfl

/-! ## The legalised register copy -/

/-- **Every instruction of a legalised register copy over allocated operands is
    encodable.** -/
theorem legalizeMov_encodable {F W Q : Nat} {d s : LOperand} {mov : String}
    (hm : isMovMnem mov = true) (hd : AllocOp F W Q d) (hs : AllocOp F W Q s) :
    ∀ i ∈ legalizeMov d s mov, encodableLinstrR F W i Q = true :=
  x86Enc_complete.legalizeMovI_encodable (c := (F, W, Q)) hm (allocOp_iff_allocOpI.1 hd)
    (allocOp_iff_allocOpI.1 hs)

/-- **Every instruction of the one-source arm of the allocation on a register move
    over allocated operands is encodable.** -/
theorem legalizeOneSrc_encodable {F W Q : Nat} {u64 : Bool} {opn : String} {d s : LOperand}
    (hm : isMovMnem opn = true) (hd : AllocOp F W Q d) (hs : AllocOp F W Q s) :
    ∀ i ∈ legalizeOneSrc u64 opn d s, encodableLinstrR F W i Q = true :=
  x86Enc_complete.legalizeOneSrcI_encodable (c := (F, W, Q)) hm (allocOp_iff_allocOpI.1 hd)
    (allocOp_iff_allocOpI.1 hs)

/-! ## The scratch select -/

/-- **Every instruction of the scratch select is encodable** when the destination and
    the condition are allocated and the selected values are general-purpose
    registers. -/
theorem cmovSpillSeq_encodable {F W Q : Nat} {d c : LOperand} {tn fn : String}
    (hd : AllocOp F W Q d) (hc : AllocOp F W Q c) (ht : isGpName tn = true)
    (hf : isGpName fn = true) :
    ∀ i ∈ cmovSpillSeq "CMOV:64" d c (.reg tn) (.reg fn), encodableLinstrR F W i Q = true :=
  x86Enc_complete.cmovSpillSeqI_encodable (c := (F, W, Q)) x86Isa_selectMnemonic
    (allocOp_iff_allocOpI.1 hd)
    (allocOp_iff_allocOpI.1 hc) ht hf

/-! ## The scratch comparison -/

/-- **Every instruction of the scratch comparison is encodable** for the comparisons
    `SETE` and `SETNE` over allocated operands. -/
theorem setccSpill?_encodable {F W Q : Nat} {dsts : List LOperand} {opn : String}
    {srcs : List LOperand} {l : List LinstrR} (h : setccSpill? dsts opn srcs = some l)
    (ho : isSetccEncMnem opn = true) (hd : ∀ o ∈ dsts, AllocOp F W Q o)
    (hs : ∀ o ∈ srcs, AllocOp F W Q o) :
    ∀ i ∈ l, encodableLinstrR F W i Q = true :=
  x86Enc_complete.setccSpillI?_encodable (c := (F, W, Q)) h ho
    (fun o ho => allocOp_iff_allocOpI.1 (hd o ho)) (fun o ho => allocOp_iff_allocOpI.1 (hs o ho))

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
    ∀ i ∈ legalizeSpillDst dsts opn srcs, encodableLinstrR F W i Q = true :=
  x86Enc_complete.legalizeSpillDstI_encodable (c := (F, W, Q)) x86Isa_selectMnemonic
    (fun o ho => allocOp_iff_allocOpI.1 (hd o ho)) (fun o ho => allocOp_iff_allocOpI.1 (hs o ho))
    hsel hcmp hone

/-! ## Load forwarding -/

section LoadCSE

open CatCrypt.Crypto.Optimizer.LoadCSE

/-- **One forwarding step keeps an encodable instruction encodable** and the
    environment resolving. -/
theorem stepLoad_encodable {F W Q : Nat} (h : LoadEnv) (i : Linstr) (hh : EnvResolves F W Q h)
    (hi : encodableLinstrR F W i.li_i Q = true) :
    encodableLinstrR F W (stepLoad h i).1.li_i Q = true ∧
      EnvResolves F W Q (stepLoad h i).2 :=
  x86Enc_complete.stepLoad_encodableI (c := (F, W, Q)) h i hh hi

/-- **`loadCSE` preserves encodability**: at a fixed frame size, spill width and save
    block, a body of encodable instructions is forwarded to a body of encodable
    instructions. -/
theorem loadCSE_encodable {F W Q : Nat} (body : List Linstr)
    (hb : ∀ i ∈ body, encodableLinstrR F W i.li_i Q = true) :
    ∀ i ∈ loadCSE body, encodableLinstrR F W i.li_i Q = true :=
  x86Enc_complete.loadCSE_encodableI (c := (F, W, Q)) body hb

end LoadCSE

end CatCrypt.Crypto.SecureCompilation.X86Backend.EncodeComplete
