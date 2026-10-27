/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportPhysAbi
public import CatCrypt.Crypto.SecureCompilation.X86Backend.WellFormedX86
public import CatCrypt.Crypto.SecureCompilation.VIR.AllocOut

/-!
# Resolved operands of the expansion arms of `physPositionEmit`

`physPositionEmit` expands one virtual instruction of a register-allocated body through
the legalisers and lowerers of the export (`lowerTwoAddr`, `lowerTwoAddrShiftImm`,
`lowerNativeShiftRotate`, `legalizeMemLoad`, `legalizeMemStoreK`, `legalizeSpillDst`,
`legalizeOneSrc`, the memref base reload `reloadMemrefBase`, and the remapped
pass-through). This module proves that each arm emits only operations whose operands are
resolved over x86 (`OpsResolved`, the x86 instance of the `resolved` field of
`AllocOutInstr`).

Every arm lemma is stated over the remapped operands it receives, so it holds for any
operand map: the lemmas never unfold `physNameForBody`, `remapOperand` or
`remapOperandCalleeSave`. A register operand is required to be resolved
(`opResolved`); the address of a memory load or store is required to be `AddrOk`, a
resolved operand or a register-indexed address whose base and index are physical
registers or spill slots (`sibElemArgsOk`), since `legalizeSibElem` reloads a spilled base
or index into a scratch register.

## Main definitions

* `OpsResolved x`: every operand of the operation `x` is `opResolved`.
* `AddrOk o`: the operand `o` is resolved, or a register-indexed address with SIB-ok base
  and index and a legal scale.

## Main statements

* `legalizeMov_resolved`, `legalizeBinop_resolved`, `materializeWideImm_resolved`,
  `lowerTwoAddr_resolved`, `lowerTwoAddrShiftImm_resolved`,
  `lowerNativeShiftRotate_resolved`, `legalizeSibElem_resolved`,
  `reloadMemrefBase_resolved`, `legalizeMemLoad_resolved`, `legalizeMemStore_resolved`,
  `constIdxStore?_resolved`, `legalizeMemStoreK_resolved`, `legalizeOneSrc_resolved`,
  `legalizeSpillDst_resolved`: the legalisers and lowerers emit resolved operations on
  resolved operands.
* `opsResolved_iff_allocOut_x86`: `OpsResolved` is the `resolved` field of
  `AllocOutInstr x86Data`.
* `physPositionEmit_resolved`, `physPositionEmit_allocOut_resolved`: every operation one
  position of `physPositionEmit` emits has operands resolved over `x86Data`, given resolved
  values of the operand map and of the ABI names.
* `physNameForBody_resolved_of_fit`, `physNameForBody_sibArgOk_of_fit`: below the bound
  `vectorBase`, `physNameForBody` names a physical register or a spill slot.
* `physBodyWithStores_allocOut_resolved`, `physBodyWithStores_allocOut_resolved_abi`: the
  whole stored body.
* `comToLfundefPhysAbiFromVirt_allocOut_resolved`, `lfundefPhysAbiOfVirt_allocOut_resolved`:
  every instruction of the two ABI exports at the x86 register file (prologue, argument
  saves and materialisation, stored body, return move, callee-saved restore) has operands
  resolved over `x86Data`, given the naming hypotheses on the allocated body
  (`fromVirtAllocBody`, `ofVirtAllocBody`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysPositionEmitWF

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.AllocForm (lopnOperands)
open CatCrypt.Crypto.SecureCompilation.X86Backend.WellFormedX86

/-! ## 1. Resolved operations and SIB-ok addresses -/

/-- Every operand of the operation `x` is resolved over x86 (`opResolved`); vacuous on
    every instruction other than an operation. -/
def OpsResolved (x : LinstrR) : Prop := ∀ o ∈ lopnOperands x, opResolved o = true

/-- An address operand that the export can legalise into a resolved one: a register-indexed
    address whose base and index are physical registers or spill slots and whose scale is
    legal (`sibElemArgsOk`), or any other resolved operand. -/
def AddrOk : LOperand → Prop
  | .arrIdx b i s => sibElemArgsOk b i s
  | o => opResolved o = true

/-- An operation is resolved iff its destinations and its sources are. -/
@[simp] theorem opsResolved_Lopn (ds : List LOperand) (opn : String) (ss : List LOperand) :
    OpsResolved (.Lopn ds opn ss) ↔
      (∀ o ∈ ds, opResolved o = true) ∧ ∀ o ∈ ss, opResolved o = true := by
  simp only [OpsResolved, lopnOperands, List.mem_append]
  exact ⟨fun h => ⟨fun o ho => h o (Or.inl ho), fun o ho => h o (Or.inr ho)⟩,
    fun h o ho => ho.elim (h.1 o) (h.2 o)⟩

/-- The primary reload scratch `R15` is resolved. -/
@[simp] theorem opResolved_reloadScratch : opResolved (.reg reloadScratch) = true :=
  reloadScratch_ok.1

/-- The secondary reload scratch `R14` is resolved. -/
@[simp] theorem opResolved_reloadScratch2 : opResolved (.reg reloadScratch2) = true :=
  reloadScratch2_ok.1

/-- An immediate is resolved. -/
@[simp] theorem opResolved_imm (v : Nat) : opResolved (.imm v) = true := rfl

/-- A resolved operand is `AddrOk`. -/
theorem addrOk_of_resolved {o : LOperand} (h : opResolved o = true) : AddrOk o := by
  cases o with
  | arrIdx b i s =>
    simp only [opResolved, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨Or.inl h.1.1, Or.inl h.1.2, h.2⟩
  | _ => exact h

/-- **The x86 instance of `AllocOutInstr.resolved`.** `OpsResolved x` is the statement that
    every operand of `x` is `opResolvedI x86Data`. -/
theorem opsResolved_iff_allocOut_x86 (x : LinstrR) :
    OpsResolved x ↔
      ∀ o ∈ lopnOperands x, opResolvedI TwoAddrLegalize.x86Data o = true := by
  rw [opResolvedI_x86]
  rfl

/-! ## 2. The register legalisers and lowerers -/

/-- `legalizeMov` emits resolved operations on resolved operands. -/
theorem legalizeMov_resolved (d s : LOperand) (mov : String)
    (hd : opResolved d = true) (hs : opResolved s = true) :
    ∀ x ∈ legalizeMov d s mov, OpsResolved x := by
  unfold legalizeMov
  split <;> simp [hd, hs]

/-- `legalizeBinop` emits resolved operations on resolved operands. -/
theorem legalizeBinop_resolved (d s : LOperand) (opn mov : String)
    (hd : opResolved d = true) (hs : opResolved s = true) :
    ∀ x ∈ legalizeBinop d s opn mov, OpsResolved x := by
  unfold legalizeBinop
  split <;> simp [hd, hs]

/-- The wide-immediate prelude of `materializeWideImm` is resolved, and so is the source it
    returns. -/
theorem materializeWideImm_resolved (s : LOperand) (mov : String)
    (hs : opResolved s = true) :
    (∀ x ∈ (materializeWideImm s mov).1, OpsResolved x) ∧
      opResolved (materializeWideImm s mov).2 = true := by
  unfold materializeWideImm
  split
  · split <;> simp [hs]
  · simp [hs]

/-- `lowerTwoAddr` emits resolved operations on resolved operands. -/
theorem lowerTwoAddr_resolved (d s0 s1 : LOperand) (opn mov : String)
    (hd : opResolved d = true) (hs0 : opResolved s0 = true) (hs1 : opResolved s1 = true) :
    ∀ x ∈ lowerTwoAddr d s0 s1 opn mov, OpsResolved x := by
  obtain ⟨hpre, hs1'⟩ := materializeWideImm_resolved s1 mov hs1
  unfold lowerTwoAddr
  intro x hx
  rcases hmw : materializeWideImm s1 mov with ⟨pre, s1v⟩
  rw [hmw] at hx hpre hs1'
  simp only at hx hpre hs1'
  split at hx <;> simp only [List.mem_append] at hx
  · exact hx.elim (hpre x) (legalizeBinop_resolved d _ opn mov hd hs1' x)
  · exact hx.elim (fun h => h.elim (legalizeMov_resolved d s0 mov hd hs0 x) (hpre x))
      (legalizeBinop_resolved d _ opn mov hd hs1' x)

/-- `lowerTwoAddrShiftImm` emits resolved operations on resolved operands. -/
theorem lowerTwoAddrShiftImm_resolved (d s0 : LOperand) (v : Nat) (opn mov : String)
    (hd : opResolved d = true) (hs0 : opResolved s0 = true) :
    ∀ x ∈ lowerTwoAddrShiftImm d s0 v opn mov, OpsResolved x := by
  unfold lowerTwoAddrShiftImm
  intro x hx
  split at hx
  · simp at hx; rcases hx with rfl | rfl | rfl <;> simp [hd, hs0]
  · split at hx
    · simp at hx; subst hx; simp [hd]
    · simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact legalizeMov_resolved d s0 mov hd hs0 x hx
      · simp [hd]

/-- `lowerNativeShiftRotate` emits resolved operations on resolved operands. -/
theorem lowerNativeShiftRotate_resolved (d s : LOperand) (opn mov : String)
    (hd : opResolved d = true) (hs : opResolved s = true) :
    ∀ x ∈ lowerNativeShiftRotate d s opn mov, OpsResolved x := by
  unfold lowerNativeShiftRotate
  split <;> simp [hd, hs]

/-- `legalizeOneSrc` emits resolved operations on resolved operands. -/
theorem legalizeOneSrc_resolved (u64 : Bool) (opn : String) (d s : LOperand)
    (hd : opResolved d = true) (hs : opResolved s = true) :
    ∀ x ∈ legalizeOneSrc u64 opn d s, OpsResolved x := by
  unfold legalizeOneSrc
  split
  · exact legalizeMov_resolved d s _ hd hs
  · simp [hd, hs]

/-- `legalizeSpillDst` emits resolved operations on resolved operands. -/
theorem legalizeSpillDst_resolved (dsts : List LOperand) (opn : String) (srcs : List LOperand)
    (hd : ∀ o ∈ dsts, opResolved o = true) (hs : ∀ o ∈ srcs, opResolved o = true) :
    ∀ x ∈ legalizeSpillDst dsts opn srcs, OpsResolved x := by
  unfold legalizeSpillDst
  split
  · next l h =>
    unfold cmovSpillDst? at h
    split at h
    · split at h
      · cases h
        unfold cmovSpillSeq
        split_ifs <;> simp_all
      · cases h
    · cases h
  · split
    · next l h =>
      unfold setccSpill? at h
      split at h
      · split at h
        · cases h
          simp_all
        · cases h
      · cases h
    · simp_all

/-! ## 3. The address legalisers -/

/-- A well-formed operation has resolved operands. -/
theorem opsResolved_of_wf {x : LinstrR} (h : wfLinstr x = true) : OpsResolved x := by
  intro o ho
  cases x with
  | Lopn ds opn ss => exact (wfLinstr_sound _ h).2 o ho
  | _ => simp [lopnOperands] at ho

/-- After `legalizeSibElem`, an `AddrOk` operand is resolved, and the reload prelude is
    resolved. -/
theorem legalizeSibElem_resolved (o : LOperand) (h : AddrOk o) :
    (∀ x ∈ (legalizeSibElem o).1, OpsResolved x) ∧ opResolved (legalizeSibElem o).2 = true := by
  cases o with
  | arrIdx b i s =>
    exact ⟨fun x hx => opsResolved_of_wf (legalizeSibElem_prelude_wf b i s h.1 h.2.1 x hx),
      legalizeSibElem_fixed_resolved b i s h⟩
  | _ => exact ⟨by simp [legalizeSibElem], h⟩

/-- The memref base reload of `reloadMemrefBase` is resolved when every save slot it reads is
    resolved, and it keeps an address `AddrOk`. -/
theorem reloadMemrefBase_resolved (memrefBaseReload : String → Option String) (o : LOperand)
    (hq : ∀ b q, memrefBaseReload b = some q → opResolved (.reg q) = true) (h : AddrOk o) :
    (∀ x ∈ (reloadMemrefBase memrefBaseReload o).1, OpsResolved x) ∧
      AddrOk (reloadMemrefBase memrefBaseReload o).2 := by
  cases o with
  | arrIdx b i s =>
    cases hb : memrefBaseReload b with
    | none =>
      simp only [reloadMemrefBase, hb]
      exact ⟨by simp, h⟩
    | some q =>
      simp only [reloadMemrefBase, hb]
      exact ⟨by rcases ptrLoad_cases q with hp | hp <;> simp [hq b q hb, hp],
        Or.inl (by decide), h.2.1, h.2.2⟩
  | _ => exact ⟨by simp [reloadMemrefBase], h⟩

/-- `legalizeMemLoad` emits resolved operations on a resolved destination and an `AddrOk`
    source. -/
theorem legalizeMemLoad_resolved (d s : LOperand) (opn mov : String)
    (hd : opResolved d = true) (hs : AddrOk s) :
    ∀ x ∈ legalizeMemLoad d s opn mov, OpsResolved x := by
  obtain ⟨hpre, hs'⟩ := legalizeSibElem_resolved s hs
  unfold legalizeMemLoad
  rcases hl : legalizeSibElem s with ⟨pre, s'⟩
  rw [hl] at hpre hs'
  simp only at hpre hs' ⊢
  rw [List.forall_mem_append]
  refine ⟨hpre, ?_⟩
  split <;> simp [hd, hs']

/-- `legalizeMemStore` emits resolved operations on a resolved array result and value and an
    `AddrOk` address. -/
theorem legalizeMemStore_resolved (dArr addr val : LOperand) (opn mov : String)
    (hda : opResolved dArr = true) (haddr : AddrOk addr) (hval : opResolved val = true) :
    ∀ x ∈ legalizeMemStore dArr addr val opn mov, OpsResolved x := by
  obtain ⟨hpre, ha'⟩ := legalizeSibElem_resolved addr haddr
  unfold legalizeMemStore
  rcases hl : legalizeSibElem addr with ⟨pre, a'⟩
  rw [hl] at hpre ha'
  simp only at hpre ha' ⊢
  repeat' split
  all_goals
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx | hx <;>
      first
      | exact hpre x hx
      | (subst hx; simp [hval, ha', scratch2Mem_resolved])
      | simp [hda, hval, ha']

/-- A character list free of `.`, followed by `.`, splits at that `.`. -/
theorem span_ne_dot (L l : List Char) (h : '.' ∉ L) :
    (L ++ '.' :: l).span (fun x => decide (x ≠ '.')) = (L, '.' :: l) := by
  rw [List.span_eq_takeWhile_dropWhile]
  induction L with
  | nil => simp
  | cons c L ih =>
    simp only [List.mem_cons, not_or] at h
    have hc : decide (c ≠ '.') = true := by simpa using Ne.symm h.1
    simp only [List.cons_append, List.takeWhile_cons, List.dropWhile_cons, hc, ite_true]
    have := ih h.2
    simp only [Prod.mk.injEq] at this
    rw [this.1, this.2]

/-- The base+offset name `mem.<b>.<off>` over a physical register `b` is resolved. -/
theorem memName_resolved_of_phys {b : String} (hb : b ∈ x86PhysRegNames) (off : Nat) :
    opResolved (.reg (memName b off)) = true := by
  have hdot : '.' ∉ b.toList := by
    simp only [x86PhysRegNames, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide
  have hl : (memName b off).toList =
      ['m', 'e', 'm', '.'] ++ (b.toList ++ '.' :: (toString off).toList) := by
    simp [memName, String.toList_append]
  have hp : hasPrefix (memName b off) "mem." = true := by
    simp [hasPrefix, hl]
  have hm : memNameResolved (memName b off) = true := by
    unfold memNameResolved
    rw [hp, Bool.true_and, hl]
    simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]
    rw [span_ne_dot _ _ hdot]
    simp only [natOfDigitsSep?_toString, Option.isSome_some, Bool.and_true,
      decide_eq_true_eq]
    exact List.mem_map_of_mem hb
  simp [opResolved, regNameResolved, hm]

/-- The displacement store of `constIdxStore?` emits resolved operations on a resolved value
    and an `AddrOk` address. -/
theorem constIdxStore?_resolved (k : Option Nat) (addr val : LOperand) (l : List LinstrR)
    (haddr : AddrOk addr) (hval : opResolved val = true)
    (h : constIdxStore? k addr val = some l) :
    ∀ x ∈ l, OpsResolved x := by
  cases addr with
  | arrIdx b i s =>
    obtain ⟨hb, -, -⟩ := haddr
    unfold constIdxStore? at h
    dsimp only at h
    by_cases hbs : sibNameSpill b = true
    · have hm := memName_resolved_of_phys (by decide : reloadScratch2 ∈ x86PhysRegNames)
      have hr : opResolved (.reg b) = true := by
        simp [opResolved, regNameResolved, sibArgOk_spill_resolved hb hbs]
      simp only [hbs, ite_true] at h
      split_ifs at h
      split at h
      · split_ifs at h
        cases h
        simp [hval, hm, hr]
      · cases h
    · rw [Bool.not_eq_true] at hbs
      have hm := memName_resolved_of_phys (sibArgOk_nonspill_phys hb hbs)
      simp only [hbs, Bool.false_eq_true, ite_false] at h
      split_ifs at h
      split at h
      · split_ifs at h
        cases h
        simp [hval, hm]
      · cases h
  | _ => simp [constIdxStore?] at h

/-- `legalizeMemStoreK` emits resolved operations on a resolved array result and value and an
    `AddrOk` address. -/
theorem legalizeMemStoreK_resolved (k : Option Nat) (dArr addr val : LOperand)
    (opn mov : String) (hda : opResolved dArr = true) (haddr : AddrOk addr)
    (hval : opResolved val = true) :
    ∀ x ∈ legalizeMemStoreK k dArr addr val opn mov, OpsResolved x := by
  unfold legalizeMemStoreK
  split
  · next l h => exact constIdxStore?_resolved k addr val l haddr hval h
  · exact legalizeMemStore_resolved dArr addr val opn mov hda haddr hval

/-! ## 4. One position of `physPositionEmit` -/

/-- **Register-indexed operands only at addresses.** Of an operation of the virtual body, no
    destination is a register-indexed address, and a register-indexed source is the address of
    a memory load `[d] opn [a]` (`isMemLoad`, not a native shift) or the address of a memory
    store `[d] opn [a, v]` (`isMemStore`, not a two-address binop) whose value `v` is not
    register-indexed. These are the positions `physPositionEmit` legalises through
    `legalizeSibElem`. -/
def SibAtAddr : LinstrR → Prop
  | .Lopn dsts opn srcs =>
      (∀ o ∈ dsts, ∀ b y s, o ≠ .arrIdx b y s) ∧
      ∀ b y s, .arrIdx b y s ∈ srcs →
        (srcs = [.arrIdx b y s] ∧ dsts.length = 1 ∧ isMemLoad opn = true ∧
          isNativeShiftRotate opn = false) ∨
        (∃ v, srcs = [.arrIdx b y s, v] ∧ dsts.length = 1 ∧ isMemStore opn = true ∧
          isTwoAddrBinop opn = false ∧ ∀ b' y' s', v ≠ .arrIdx b' y' s')
  | _ => True

/-- The save slot an input load reads its base pointer from is resolved. -/
theorem abiLoadSave_resolved (base : String) : opResolved (.reg (abiLoadSave base)) = true := by
  unfold abiLoadSave abiSaveOf
  split_ifs <;> decide

/-- **One position of `physPositionEmit` emits resolved operations.** Let `rm` be the operand
    map of `physPositionEmit`. Suppose the virtual instruction carries register-indexed
    operands only at addresses (`SibAtAddr`), `rm` resolves each of its other operands
    (`hdir`) and maps each register-indexed operand to an `AddrOk` address (`haddr`), and
    the save slots of the memref base reload (`hmbr`), the names of the argument loads
    (`hargs`), the input and output memory names (`hloadBase`, `hstoreBase`) and the
    post-call reloads (`hcall`) are resolved. Then every operation of the position (inline
    loads, expansion, post-call reloads, inline store) has resolved operands. The hypotheses
    on `rm` and on `physNameForBody` are stated on their values, so the theorem does not
    depend on the definitions of the resolvers. -/
theorem physPositionEmit_resolved (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String) (outStoreMap : OutStoreMap)
    (storeBase : String) (abiW : Nat) (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (reservedVec : List Nat)
    (i : Linstr) (virtIdx : Nat) (rm : LOperand → LOperand)
    (hrm : rm =
      let tbl := straightCallComposeTable body (physTableOut body outStoreMap reservedVec)
      if bodyHasCall body then remapOperandCalleeSave body tbl else remapOperand body tbl)
    (hsib : SibAtAddr i.li_i)
    (hdir : ∀ o ∈ lopnOperands i.li_i, (∀ b y s, o ≠ .arrIdx b y s) →
      opResolved (rm o) = true)
    (haddr : ∀ b y s, .arrIdx b y s ∈ lopnOperands i.li_i → AddrOk (rm (.arrIdx b y s)))
    (hmbr : ∀ b q, memrefBaseReload b = some q → opResolved (.reg q) = true)
    (hargs : ∀ s, opResolved (.reg (physNameForBody body
      (straightCallComposeTable body (physTableOut body outStoreMap reservedVec))
      (argName s))) = true)
    (hloadBase : ∀ off, opResolved (.reg (memName loadBase off)) = true)
    (hstoreBase : ∀ off, opResolved (.reg (memName storeBase off)) = true)
    (hcall : ∀ p ∈ callArgBaseReload,
      opResolved (.reg p.1) = true ∧ opResolved (.reg p.2) = true) :
    ∀ r ∈ physPositionEmit shiftImm body inLoadMap loadBase outStoreMap storeBase abiW
      memrefBaseReload callArgBaseReload reservedVec (i, virtIdx), OpsResolved r.li_i := by
  intro r hr
  obtain ⟨ii, x⟩ := i
  simp only at hsib hdir haddr
  unfold physPositionEmit at hr
  simp only [List.mem_append, ← hrm] at hr
  have hdst : ∀ ds opn ss, x = .Lopn ds opn ss → ∀ o ∈ ds, opResolved (rm o) = true := by
    intro ds opn ss hx o ho
    subst hx
    exact hdir o (List.mem_append_left _ ho) (hsib.1 o ho)
  rcases hr with ((hr | hr) | hr) | hr
  · -- the inline argument loads
    rw [List.mem_flatMap] at hr
    obtain ⟨⟨s, base, off⟩, -, hr⟩ := hr
    split at hr <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      rcases hr with rfl | rfl | rfl <;>
      simp [hargs, abiLoadSave_resolved, hloadBase]
  · -- the expansion
    have hwrap : ∀ (L : List LinstrR) (r : Linstr),
        r ∈ L.map (fun r => ({ li_ii := ii, li_i := r } : Linstr)) → r.li_i ∈ L := by
      intro L r h
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
      exact ha
    split at hr
    · next d tail opn s0 s1 tail1 =>
      have hd := hdst _ _ _ rfl d List.mem_cons_self
      have hsrc : ∀ o ∈ s0 :: s1 :: tail1, (∀ b y s, o ≠ .arrIdx b y s) →
          opResolved (rm o) = true :=
        fun o ho h => hdir o (List.mem_append_right _ ho) h
      split at hr
      · next hbin =>
        have hns : ∀ o ∈ s0 :: s1 :: tail1, ∀ b y s, o ≠ .arrIdx b y s := by
          intro o ho b y s ho'
          subst ho'
          rcases hsib.2 b y s ho with ⟨h1, -⟩ | ⟨v, -, -, -, h2, -⟩
          · simp at h1
          · simp [hbin] at h2
        have h0 := hsrc s0 (by simp) (hns s0 (by simp))
        have h1 := hsrc s1 (by simp) (hns s1 (by simp))
        split at hr
        · exact lowerTwoAddrShiftImm_resolved _ _ _ _ _ hd h0 _ (hwrap _ _ hr)
        · exact lowerTwoAddr_resolved _ _ _ _ _ hd h0 h1 _ (hwrap _ _ hr)
      · next hbin =>
        split at hr
        · next _ d' opn' addr val heq =>
          simp only [LinstrR.Lopn.injEq, List.cons.injEq] at heq
          obtain ⟨⟨h1, rfl⟩, h2, h3, h4, rfl⟩ := heq
          subst h1 h2 h3 h4
          have h1 : opResolved (rm s1) = true := by
            refine hsrc s1 (by simp) ?_
            intro b y s h
            subst h
            rcases hsib.2 b y s (by simp) with ⟨hl, -⟩ | ⟨v, hl, -, -, -, hv⟩
            · simp at hl
            · simp only [List.cons.injEq, and_true] at hl
              exact hv b y s hl.2.symm
          split at hr
          · next hst =>
            have hA : AddrOk (rm s0) := by
              cases s0 with
              | arrIdx b y s => exact haddr b y s (by simp [lopnOperands])
              | _ => exact addrOk_of_resolved (hsrc _ (by simp) (by intro _ _ _ h; cases h))
            obtain ⟨hpre, hA'⟩ := reloadMemrefBase_resolved memrefBaseReload (rm s0) hmbr hA
            rw [List.mem_append] at hr
            rcases hr with hr | hr
            · exact hpre _ (hwrap _ _ hr)
            · exact legalizeMemStoreK_resolved _ _ _ _ _ _ hd hA' h1 _ (hwrap _ _ hr)
          · next hst =>
            have h0 : opResolved (rm s0) = true := by
              refine hsrc s0 (by simp) ?_
              intro b y s h
              subst h
              rcases hsib.2 b y s (by simp) with ⟨hl, -⟩ | ⟨v, -, -, hm, -⟩
              · simp at hl
              · exact hst hm
            exact legalizeSpillDst_resolved _ _ _ (by simp [hd]) (by simp [h0, h1]) _
              (hwrap _ _ hr)
        · next _ dsts opn' srcs hne heq =>
          simp only [LinstrR.Lopn.injEq] at heq
          obtain ⟨rfl, rfl, rfl⟩ := heq
          have hns : ∀ o ∈ s0 :: s1 :: tail1, ∀ b y s, o ≠ .arrIdx b y s := by
            intro o ho b y s h
            subst h
            rcases hsib.2 b y s ho with ⟨hl, -⟩ | ⟨v, hl, hlen, -⟩
            · simp at hl
            · simp only [List.length_cons, Nat.add_eq_right, List.length_eq_zero_iff] at hlen
              subst hlen
              exact hne d _ v rfl hl
          refine legalizeSpillDst_resolved _ _ _ ?_ ?_ _ (hwrap _ _ hr)
          · intro o ho
            obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
            exact hdst _ _ _ rfl o' ho'
          · intro o ho
            obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
            exact hsrc o' ho' (hns o' ho')
        · next _ _ hne =>
          exact (hne _ _ _ rfl).elim
    · next _ d opn s =>
      have hd := hdst _ _ _ rfl d (by simp)
      have hsrc : (∀ b y s', s ≠ .arrIdx b y s') → opResolved (rm s) = true :=
        fun h => hdir s (by simp [lopnOperands]) h
      split at hr
      · next hnat =>
        have hs := hsrc (by
          intro b y s' h
          subst h
          rcases hsib.2 b y s' (by simp) with ⟨-, -, -, hn⟩ | ⟨v, hl, -⟩
          · simp [hnat] at hn
          · simp at hl)
        exact lowerNativeShiftRotate_resolved _ _ _ _ hd hs _ (hwrap _ _ hr)
      · split at hr
        · have hA : AddrOk (rm s) := by
            cases s with
            | arrIdx b y s' => exact haddr b y s' (by simp [lopnOperands])
            | _ => exact addrOk_of_resolved (hsrc (by intro _ _ _ h; cases h))
          obtain ⟨hpre, hA'⟩ := reloadMemrefBase_resolved memrefBaseReload (rm s) hmbr hA
          rw [List.mem_append] at hr
          rcases hr with hr | hr
          · exact hpre _ (hwrap _ _ hr)
          · exact legalizeMemLoad_resolved _ _ _ _ hd hA' _ (hwrap _ _ hr)
        · next hld =>
          have hs := hsrc (by
            intro b y s' h
            subst h
            rcases hsib.2 b y s' (by simp) with ⟨-, -, hl, -⟩ | ⟨v, hl, -⟩
            · exact hld hl
            · simp at hl)
          exact legalizeOneSrc_resolved _ _ _ _ hd hs _ (hwrap _ _ hr)
    · next _ dsts opn srcs h1 h2 =>
      have hns : ∀ o ∈ srcs, ∀ b y s, o ≠ .arrIdx b y s := by
        intro o ho b y s h
        subst h
        rcases hsib.2 b y s ho with ⟨hl, hlen, -⟩ | ⟨v, hl, hlen, -⟩
        · obtain ⟨d0, rfl⟩ := List.length_eq_one_iff.mp hlen
          exact h2 d0 _ rfl hl
        · obtain ⟨d0, rfl⟩ := List.length_eq_one_iff.mp hlen
          exact h1 d0 [] _ v [] rfl hl
      simp only [List.mem_singleton] at hr
      subst hr
      rw [opsResolved_Lopn]
      constructor
      · intro o ho
        obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        exact hdst _ _ _ rfl o' ho'
      · intro o ho
        obtain ⟨o', ho', rfl⟩ := List.mem_map.mp ho
        exact hdir o' (List.mem_append_right _ ho') (hns o' ho')
    · next _ _ _ hne =>
      simp only [List.mem_singleton] at hr
      subst hr
      intro o ho
      cases x with
      | Lopn ds opn ss => exact (hne ds opn ss rfl).elim
      | _ => simp [lopnOperands] at ho
  · -- the pointer reloads after a call
    split at hr
    · rw [List.mem_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      simp [hcall p hp]
    · simp at hr
  · -- the inline output store
    split at hr
    · next d tail opn srcs =>
      have hd := hdst _ _ _ rfl d List.mem_cons_self
      have hrdi : opResolved (.reg abiSaveRdiName) = true := by decide
      repeat' split at hr
      all_goals
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      all_goals
        rcases hr with rfl | rfl | rfl <;> simp [hd, hrdi, hstoreBase]
    · simp at hr

/-- **One position of `physPositionEmit` in `AllocOut` form at x86.** Under the hypotheses of
    `physPositionEmit_resolved`, every operand of every emitted operation is resolved over
    `x86Data`, the `resolved` field of `AllocOutInstr x86Data`. -/
theorem physPositionEmit_allocOut_resolved (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String) (outStoreMap : OutStoreMap)
    (storeBase : String) (abiW : Nat) (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (reservedVec : List Nat)
    (i : Linstr) (virtIdx : Nat) (rm : LOperand → LOperand)
    (hrm : rm =
      let tbl := straightCallComposeTable body (physTableOut body outStoreMap reservedVec)
      if bodyHasCall body then remapOperandCalleeSave body tbl else remapOperand body tbl)
    (hsib : SibAtAddr i.li_i)
    (hdir : ∀ o ∈ lopnOperands i.li_i, (∀ b y s, o ≠ .arrIdx b y s) →
      opResolved (rm o) = true)
    (haddr : ∀ b y s, .arrIdx b y s ∈ lopnOperands i.li_i → AddrOk (rm (.arrIdx b y s)))
    (hmbr : ∀ b q, memrefBaseReload b = some q → opResolved (.reg q) = true)
    (hargs : ∀ s, opResolved (.reg (physNameForBody body
      (straightCallComposeTable body (physTableOut body outStoreMap reservedVec))
      (argName s))) = true)
    (hloadBase : ∀ off, opResolved (.reg (memName loadBase off)) = true)
    (hstoreBase : ∀ off, opResolved (.reg (memName storeBase off)) = true)
    (hcall : ∀ p ∈ callArgBaseReload,
      opResolved (.reg p.1) = true ∧ opResolved (.reg p.2) = true) :
    ∀ r ∈ physPositionEmit shiftImm body inLoadMap loadBase outStoreMap storeBase abiW
      memrefBaseReload callArgBaseReload reservedVec (i, virtIdx),
      ∀ o ∈ lopnOperands r.li_i, opResolvedI TwoAddrLegalize.x86Data o = true := fun r hr =>
  (opsResolved_iff_allocOut_x86 _).mp
    (physPositionEmit_resolved shiftImm body inLoadMap loadBase outStoreMap storeBase abiW
      memrefBaseReload callArgBaseReload reservedVec i virtIdx rm hrm hsib hdir haddr hmbr
      hargs hloadBase hstoreBase hcall r hr)

/-! ## 5. The naming hypothesis under the fit bound -/

/-- The callee-saved-first permutation keeps an index below `vectorBase`. -/
theorem calleeFirstPhys_lt_vectorBase {p : Nat} (hp : p < vectorBase) :
    calleeFirstPhys p < vectorBase := by
  have hord : ∀ q < numGPRegs, calleeSavedFirstOrder.getD q q < vectorBase := by decide
  unfold calleeFirstPhys
  split
  · next h => exact hord p h
  · exact hp

/-- **`physNameForBody` names a physical register or a spill slot under the fit bound.** For
    a name whose allocation index is below `vectorBase` (`hfit`), and whose pass-through
    renderings (a frame-slot name, or a hardware register name in a body with a call) are
    physical registers or spill slots, `physNameForBody` returns a physical register or a
    spill slot (`sibArgOk`). -/
theorem physNameForBody_sibArgOk_of_fit (body : Lcmd) (tbl : Array Nat) (n : String)
    (hframe : isFrameSlotName n = true → sibArgOk n)
    (hhw : isHwRegName n = true → sibArgOk n)
    (hfit : physMapTabled tbl (nameSlot body n) < vectorBase) :
    sibArgOk (physNameForBody body tbl n) := by
  unfold physNameForBody
  split
  · next h => exact hframe h
  · split
    · split
      · next h => exact hhw h
      · split
        · exact physRegName_sibArgOk _ hfit
        · exact physRegName_sibArgOk _ (calleeFirstPhys_lt_vectorBase hfit)
    · exact physRegName_sibArgOk _ hfit

/-- A physical register or a spill slot is a resolved register name. -/
theorem opResolved_of_sibArgOk {n : String} (h : sibArgOk n) : opResolved (.reg n) = true := by
  rcases h with h | h <;> simp [opResolved, regNameResolved, h]

/-- **The naming hypothesis of `physPositionEmit_resolved` under the fit bound**: the name
    `physNameForBody` gives `n` is resolved when the allocation index of `n` is below
    `vectorBase` and its pass-through renderings are physical registers or spill slots. -/
theorem physNameForBody_resolved_of_fit (body : Lcmd) (tbl : Array Nat) (n : String)
    (hframe : isFrameSlotName n = true → sibArgOk n)
    (hhw : isHwRegName n = true → sibArgOk n)
    (hfit : physMapTabled tbl (nameSlot body n) < vectorBase) :
    opResolved (.reg (physNameForBody body tbl n)) = true :=
  opResolved_of_sibArgOk (physNameForBody_sibArgOk_of_fit body tbl n hframe hhw hfit)

/-! ## 6. The memory bases, the save slots and the post-call reloads -/

/-- The base+offset names over the reload scratch `R14`, the input and output memory base
    of the ABI exports, are resolved. -/
theorem memName_reloadScratch2_resolved (off : Nat) :
    opResolved (.reg (memName reloadScratch2 off)) = true :=
  memName_resolved_of_phys (by decide) off

/-- A save slot of `abiSaveOf` is resolved. -/
theorem abiSaveOf_resolved {reg q : String} (h : abiSaveOf reg = some q) :
    opResolved (.reg q) = true := by
  unfold abiSaveOf at h
  split_ifs at h <;> cases h <;> decide

/-- A save slot of `abiSaveOfExt` is resolved. -/
theorem abiSaveOfExt_resolved {reg q : String} (h : abiSaveOfExt reg = some q) :
    opResolved (.reg q) = true := by
  unfold abiSaveOfExt at h
  split at h
  · next s hs => cases h; exact abiSaveOf_resolved hs
  · split_ifs at h <;> cases h <;> decide

/-- A frame slot of `abiSlotOfExt` is resolved: the save slot of an argument register, or
    the slot `qsave.RSP+off` of an argument passed in a stack word. -/
theorem abiSlotOfExt_resolved {reg q : String} (h : abiSlotOfExt reg = some q) :
    opResolved (.reg q) = true := by
  unfold abiSlotOfExt at h
  split at h
  · next s hs => cases h; exact abiSaveOfExt_resolved hs
  · obtain ⟨off, hoff, rfl⟩ := Option.map_eq_some_iff.mp h
    have hq : qsaveNameResolved ("qsave." ++ reg) = true := by
      simp [qsaveNameResolved, JasminLprogExport.hasPrefix, String.toList_append, hoff]
    simp [opResolved, regNameResolved, hq]

/-- An allocatable caller-saved general-purpose register is resolved. -/
theorem opResolved_of_isCallerSavedAllocGPR {n : String} (h : isCallerSavedAllocGPR n = true) :
    opResolved (.reg n) = true := by
  simp only [isCallerSavedAllocGPR, callerSavedAllocGPRs, List.contains_iff_mem,
    List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- **A lookup map over a pair list reads resolved slots.** If every pair of `pairs` carries a
    resolved second component, the map `b ↦ snd (find (fst = b) pairs)`, the shape of the
    `memrefBaseReload` maps of the ABI exports, satisfies the hypothesis `hmbr` of
    `physPositionEmit_resolved`. -/
theorem findSnd_resolved (pairs : List (String × String))
    (h : ∀ p ∈ pairs, opResolved (.reg p.2) = true) :
    ∀ b q, (pairs.find? (fun p => p.1 == b)).map Prod.snd = some q →
      opResolved (.reg q) = true := by
  intro b q hq
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hq
  exact h p (List.mem_of_find?_eq_some hp)

/-- **The `memrefBaseReload` map of `lfundefPhysAbiOfVirt` reads resolved slots.** For any
    naming `P` of the arguments, the map keyed on `P argNm` with value the save slot
    `abiSaveOfExt abiReg` satisfies `hmbr`. -/
theorem memrefBaseReload_saveExt_resolved (argAbi : List (String × String))
    (P : String → String) :
    ∀ b q, ((argAbi.filterMap (fun (argNm, abiReg) =>
        match abiSaveOfExt abiReg with
        | some saveName => some (P argNm, saveName)
        | none => none)).find? (fun p => p.1 == b)).map Prod.snd = some q →
      opResolved (.reg q) = true := by
  refine findSnd_resolved _ ?_
  intro p hp
  obtain ⟨⟨argNm, abiReg⟩, -, hf⟩ := List.mem_filterMap.mp hp
  simp only at hf
  split at hf
  · next s hs => cases hf; exact abiSaveOfExt_resolved hs
  · cases hf

/-- **The `memrefBaseReload` map of `comToLfundefPhysAbiFromVirt` reads resolved slots.** For
    any naming `P` of the argument positions, the map keyed on `P j` with value the frame slot
    `abiSlotOfExt abiReg` of an argument not covered by `inLoadMap` (a save slot or the
    caller's stack word) satisfies `hmbr`. -/
theorem memrefBaseReload_slotExt_resolved (abiArgs : List String) (inLoadMap : InLoadMap)
    (P : Nat → String) :
    ∀ b q, ((abiArgs.zipIdx.filterMap (fun (abiReg, j) =>
        match inLoadMap j with
        | some _ => none
        | none =>
            match abiSlotOfExt abiReg with
            | some saveName => some (P j, saveName)
            | none => none)).find? (fun p => p.1 == b)).map Prod.snd = some q →
      opResolved (.reg q) = true := by
  refine findSnd_resolved _ ?_
  intro p hp
  obtain ⟨⟨abiReg, j⟩, -, hf⟩ := List.mem_filterMap.mp hp
  simp only at hf
  split at hf
  · cases hf
  · split at hf
    · next s hs =>
      cases hf
      exact abiSlotOfExt_resolved hs
    · cases hf

/-- **The `callArgBaseReload` list of `lfundefPhysAbiOfVirt` is resolved.** For any naming `P`
    of the argument positions, each pair keeps a caller-saved register `P j` with the save slot
    `abiSaveOfExt abiReg`; both are resolved, the hypothesis `hcall` of
    `physPositionEmit_resolved`. -/
theorem callArgBaseReload_resolved (abiArgs : List String) (P : Nat → String) :
    ∀ p ∈ abiArgs.zipIdx.filterMap (fun (abiReg, j) =>
        match abiSaveOfExt abiReg with
        | some saveName => if isCallerSavedAllocGPR (P j) then some (P j, saveName) else none
        | none => none),
      opResolved (.reg p.1) = true ∧ opResolved (.reg p.2) = true := by
  intro p hp
  obtain ⟨⟨abiReg, j⟩, -, hf⟩ := List.mem_filterMap.mp hp
  simp only at hf
  split at hf
  · next s hs =>
    split_ifs at hf with hc
    cases hf
    exact ⟨opResolved_of_isCallerSavedAllocGPR hc, abiSaveOfExt_resolved hs⟩
  · cases hf

/-! ## 7. The whole body -/

/-- **Every operation of `physBodyWithStores` is resolved over x86.** Suppose every virtual
    instruction of `body` carries register-indexed operands only at addresses (`SibAtAddr`),
    the operand map `rm` resolves its other operands (`hdir`) and maps its register-indexed
    operands to `AddrOk` addresses (`haddr`), and the save slots, argument names, memory bases
    and post-call reloads are resolved (`hmbr`, `hargs`, `hloadBase`, `hstoreBase`, `hcall`).
    Then every instruction of `physBodyWithStores` satisfies the `resolved` field of
    `AllocOutInstr x86Data`. -/
theorem physBodyWithStores_allocOut_resolved (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String) (outStoreMap : OutStoreMap)
    (storeBase : String) (abiW : Nat) (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (reservedVec : List Nat)
    (rm : LOperand → LOperand)
    (hrm : rm =
      let tbl := straightCallComposeTable body (physTableOut body outStoreMap reservedVec)
      if bodyHasCall body then remapOperandCalleeSave body tbl else remapOperand body tbl)
    (hsib : ∀ i ∈ body, SibAtAddr i.li_i)
    (hdir : ∀ i ∈ body, ∀ o ∈ lopnOperands i.li_i, (∀ b y s, o ≠ .arrIdx b y s) →
      opResolved (rm o) = true)
    (haddr : ∀ i ∈ body, ∀ b y s, .arrIdx b y s ∈ lopnOperands i.li_i →
      AddrOk (rm (.arrIdx b y s)))
    (hmbr : ∀ b q, memrefBaseReload b = some q → opResolved (.reg q) = true)
    (hargs : ∀ s, opResolved (.reg (physNameForBody body
      (straightCallComposeTable body (physTableOut body outStoreMap reservedVec))
      (argName s))) = true)
    (hloadBase : ∀ off, opResolved (.reg (memName loadBase off)) = true)
    (hstoreBase : ∀ off, opResolved (.reg (memName storeBase off)) = true)
    (hcall : ∀ p ∈ callArgBaseReload,
      opResolved (.reg p.1) = true ∧ opResolved (.reg p.2) = true) :
    ∀ r ∈ physBodyWithStores shiftImm body inLoadMap loadBase outStoreMap storeBase abiW
      memrefBaseReload callArgBaseReload reservedVec,
      ∀ o ∈ lopnOperands r.li_i, opResolvedI TwoAddrLegalize.x86Data o = true := by
  intro r hr
  rw [physBodyWithStores_eq_flatMap, List.mem_flatMap] at hr
  obtain ⟨⟨i, k⟩, hik, hr⟩ := hr
  have hi : i ∈ body := List.fst_mem_of_mem_zipIdx hik
  exact physPositionEmit_allocOut_resolved shiftImm body inLoadMap loadBase outStoreMap
    storeBase abiW memrefBaseReload callArgBaseReload reservedVec i k rm hrm (hsib i hi)
    (hdir i hi) (haddr i hi) hmbr hargs hloadBase hstoreBase hcall r hr

/-- **`physBodyWithStores` at the ABI exports' bases is resolved over x86.** With the reload
    scratch `R14` as input and output memory base, a `memrefBaseReload` map that reads resolved
    slots (`memrefBaseReload_saveExt_resolved`, `memrefBaseReload_slotExt_resolved`) and a
    resolved `callArgBaseReload` list (`callArgBaseReload_resolved`), every instruction of
    `physBodyWithStores` satisfies the `resolved` field of `AllocOutInstr x86Data` under the
    body-shape hypothesis `SibAtAddr` and the naming hypotheses `hdir`, `haddr`, `hargs`. -/
theorem physBodyWithStores_allocOut_resolved_abi (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap) (abiW : Nat)
    (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (reservedVec : List Nat)
    (rm : LOperand → LOperand)
    (hrm : rm =
      let tbl := straightCallComposeTable body (physTableOut body outStoreMap reservedVec)
      if bodyHasCall body then remapOperandCalleeSave body tbl else remapOperand body tbl)
    (hsib : ∀ i ∈ body, SibAtAddr i.li_i)
    (hdir : ∀ i ∈ body, ∀ o ∈ lopnOperands i.li_i, (∀ b y s, o ≠ .arrIdx b y s) →
      opResolved (rm o) = true)
    (haddr : ∀ i ∈ body, ∀ b y s, .arrIdx b y s ∈ lopnOperands i.li_i →
      AddrOk (rm (.arrIdx b y s)))
    (hmbr : ∀ b q, memrefBaseReload b = some q → opResolved (.reg q) = true)
    (hargs : ∀ s, opResolved (.reg (physNameForBody body
      (straightCallComposeTable body (physTableOut body outStoreMap reservedVec))
      (argName s))) = true)
    (hcall : ∀ p ∈ callArgBaseReload,
      opResolved (.reg p.1) = true ∧ opResolved (.reg p.2) = true) :
    ∀ r ∈ physBodyWithStores shiftImm body inLoadMap reloadScratch2 outStoreMap reloadScratch2
      abiW memrefBaseReload callArgBaseReload reservedVec,
      ∀ o ∈ lopnOperands r.li_i, opResolvedI TwoAddrLegalize.x86Data o = true :=
  physBodyWithStores_allocOut_resolved shiftImm body inLoadMap reloadScratch2 outStoreMap
    reloadScratch2 abiW memrefBaseReload callArgBaseReload reservedVec rm hrm hsib hdir haddr
    hmbr hargs memName_reloadScratch2_resolved memName_reloadScratch2_resolved hcall

/-- **The constant-shape base reload keeps operations resolved**: when every operation of
    `l` and every save slot of `mbr` is resolved, so is every operation of
    `reloadArrImmBody mbr l`. -/
theorem reloadArrImmBody_resolved {mbr : String → Option String} {l : Lcmd}
    (hmbr : ∀ b q, mbr b = some q → opResolved (.reg q) = true)
    (hl : ∀ r ∈ l, OpsResolved r.li_i) :
    ∀ r ∈ reloadArrImmBody mbr l, OpsResolved r.li_i := by
  intro r hr
  rcases mem_reloadArrImmBody hr with h | ⟨i, hi, l', hre, -, hx⟩
  · exact hl r h
  · have hiR := hl i hi
    obtain ⟨b, q, hq, ⟨n, w, -, rfl⟩ | ⟨d, v, k, hiEq, rfl⟩⟩ := reloadArrImm_eq_some hre
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx <;> rw [hx] <;> rcases ptrLoad_cases q with hp | hp <;>
        simp [hmbr b q hq, hp]
    · rw [hiEq] at hiR
      simp only [opsResolved_Lopn, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hiR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx <;> rw [hx] <;> rcases ptrLoad_cases q with hp | hp <;>
        simp [hmbr b q hq, hiR, hp]

/-! ## 8. The whole function -/

/-- A well-formed instruction has resolved operands. -/
theorem opsResolved_of_wfLinstr {x : LinstrR} (h : wfLinstr x = true) : OpsResolved x := by
  obtain ⟨-, hres⟩ := wfLinstr_sound x h
  intro o ho
  unfold lopnOperands at ho
  split at ho
  · exact hres o ho
  · simp at ho

/-- An argument register with a save slot of `abiSaveOfExt` is resolved. -/
theorem reg_resolved_of_abiSaveOfExt {reg q : String} (h : abiSaveOfExt reg = some q) :
    opResolved (.reg reg) = true := by
  unfold abiSaveOfExt abiSaveOf at h
  split at h
  · next s hs =>
    split_ifs at hs with h1 h2
    · rw [beq_iff_eq] at h1; subst h1; decide
    · rw [beq_iff_eq] at h2; subst h2; decide
  · split_ifs at h with h1 h2 h3 h4 <;> simp only [beq_iff_eq] at * <;> subst_vars <;> decide

/-- The prologue saves of a list of argument registers to their save slots are resolved. -/
theorem extraInputSaves_resolved (regs : List String) :
    ∀ r ∈ regs.filterMap (fun abiReg =>
      match abiSaveOfExt abiReg with
      | some saveName => some (⟨0, .Lopn [.reg saveName] "MOVQ" [.reg abiReg]⟩ : Linstr)
      | none => none), OpsResolved r.li_i := by
  intro r hr
  obtain ⟨abiReg, -, hf⟩ := List.mem_filterMap.mp hr
  split at hf
  · next s hs =>
    cases hf
    intro o ho
    simp only [lopnOperands, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact abiSaveOfExt_resolved hs
    · exact reg_resolved_of_abiSaveOfExt hs
  · cases hf

/-- **The argument materialisation is resolved.** Every instruction of
    `buildArgPtrMaterialize` has resolved operands when the names of the arguments are
    resolved (`hphys`) and every argument register read directly, one without a frame slot,
    is resolved (`habi`). -/
theorem buildArgPtrMaterialize_resolved (virt : Lfundef) (tbl : Array Nat)
    (abiArgs : List String) (inLoadMap : InLoadMap)
    (hphys : ∀ j, opResolved (.reg (physNameForBody virt.lfd_body tbl (argName j))) = true)
    (habi : ∀ r ∈ abiArgs, abiSlotOfExt r = none → opResolved (.reg r) = true) :
    ∀ r ∈ buildArgPtrMaterialize virt tbl abiArgs inLoadMap, OpsResolved r.li_i := by
  intro r hr
  unfold buildArgPtrMaterialize at hr
  obtain ⟨⟨abiReg, j⟩, hmem, hr⟩ := List.mem_flatMap.mp hr
  have hreg := List.fst_mem_of_mem_zipIdx hmem
  have hR : opResolved (.reg reloadScratch) = true := by decide
  have hP := hphys j
  simp only at hr
  split at hr
  · simp at hr
  · split_ifs at hr <;>
      rcases hs : abiSlotOfExt abiReg with _ | s <;>
      simp only [hs, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
      (try rcases hr with rfl | rfl) <;>
      intro o ho <;>
      simp only [lopnOperands, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at ho <;>
      rcases ho with rfl | rfl <;>
      first
        | with_reducible assumption
        | with_reducible exact habi abiReg hreg hs
        | with_reducible exact abiSlotOfExt_resolved hs

/-- `insertEpilogue` keeps resolvedness: the body without its last instruction, the
    epilogue and the final return. -/
theorem insertEpilogue_resolved (body epi : Lcmd)
    (hb : ∀ r ∈ body, OpsResolved r.li_i) (he : ∀ r ∈ epi, OpsResolved r.li_i) :
    ∀ r ∈ insertEpilogue body epi, OpsResolved r.li_i := by
  intro r hr
  unfold insertEpilogue at hr
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (h | h) | rfl
  · exact hb r (List.dropLast_subset _ h)
  · exact he r h
  · intro o ho; simp [lopnOperands] at ho

/-- The body the allocation of `comToLfundefPhysAbiFromVirt` runs on: the virtual body with
    its call shadows expanded, renamed onto the residence slots when `residence` is given,
    with the argument-liveness pin in front for three or more arguments or `forceLivePin`,
    its memref threads canonicalised, and the result-liveness pin `resLivePin` behind. -/
def fromVirtAllocBody (virt0 : Lfundef) (residence : Option (Array Nat))
    (forceLivePin retToRax : Bool) (outStoreMap : OutStoreMap) : Lcmd :=
  let virt0 := { virt0 with lfd_body := expandCallShadows virt0.lfd_body }
  let virtR :=
    match residence with
    | none => virt0
    | some slots =>
        { virt0 with
          lfd_body := residenceRenameBody virt0.lfd_arg.length (residenceArraySlotOf slots)
                        (materializeShiftCountImms virt0.lfd_body) }
  let nArgs := virtR.lfd_arg.length
  (if nArgs ≥ 3 || forceLivePin then
      [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
            ((List.range nArgs).map (fun j => (.reg (argName j) : LOperand)))⟩]
    else []) ++ canonicalizeMemrefThread virtR.lfd_body
      ++ resLivePin retToRax outStoreMap virt0.lfd_res

/-- Without residence slots the allocated body is the pinned, canonicalised body with its call
    shadows expanded. -/
theorem fromVirtAllocBody_none (virt0 : Lfundef) (forceLivePin retToRax : Bool)
    (outStoreMap : OutStoreMap) :
    fromVirtAllocBody virt0 none forceLivePin retToRax outStoreMap =
      (if virt0.lfd_arg.length ≥ 3 || forceLivePin then
          [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
                ((List.range virt0.lfd_arg.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread (expandCallShadows virt0.lfd_body)
        ++ resLivePin retToRax outStoreMap virt0.lfd_res := rfl

/-- With residence slots the allocated body is renamed onto the slots before it is pinned and
    canonicalised. -/
theorem fromVirtAllocBody_some (virt0 : Lfundef) (slots : Array Nat)
    (forceLivePin retToRax : Bool) (outStoreMap : OutStoreMap) :
    fromVirtAllocBody virt0 (some slots) forceLivePin retToRax outStoreMap =
      (if virt0.lfd_arg.length ≥ 3 || forceLivePin then
          [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
                ((List.range virt0.lfd_arg.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
        else []) ++ canonicalizeMemrefThread
          (residenceRenameBody virt0.lfd_arg.length (residenceArraySlotOf slots)
            (materializeShiftCountImms (expandCallShadows virt0.lfd_body)))
        ++ resLivePin retToRax outStoreMap virt0.lfd_res := rfl

/-- The return move of `comToLfundefPhysAbiFromVirt` is resolved when the name of the
    returned value is. -/
theorem retMat_resolved (B : Lcmd) (tbl : Array Nat) (res : Option String) (c : Bool)
    (hret : ∀ rn ∈ res, opResolved (.reg (physNameForBody B tbl rn)) = true) :
    ∀ r ∈ (if c = true then
        match res with
        | some rn =>
            if nameSlot B rn < (bodyNames B).length then
              if (physNameForBody B tbl rn == sysvRetReg) = true then []
              else [(⟨0, .Lopn [.reg sysvRetReg] "MOVQ" [.reg (physNameForBody B tbl rn)]⟩ :
                Linstr)]
            else []
        | none => []
      else []), OpsResolved r.li_i := by
  intro r hr
  cases res with
  | none => simp at hr
  | some rn =>
    split at hr
    · simp only at hr
      split_ifs at hr <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      intro o ho
      simp only [lopnOperands, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl
      · decide
      · exact hret rn rfl
    · simp at hr

/-- **Every operation of `comToLfundefPhysAbiFromVirt` is resolved over x86.** On the x86
    register file and without a forwarder body, let `B` be the allocated body
    (`fromVirtAllocBody`) and `tbl` its allocation table. Under the naming hypotheses of
    `physBodyWithStores_allocOut_resolved_abi` on `B` (`hsib`, `hdir`, `haddr`, `hargs`), a
    resolved name for the returned value (`hret`) and resolved argument registers read
    directly (`habi`), every instruction of the function body satisfies the `resolved` field
    of `AllocOutInstr x86Data`. The prologue, the saves of further arguments, the argument
    materialisation, the inline loads and stores with their memref base reloads (from a save
    slot or the caller's stack word), the return move and the callee-saved restore are each
    resolved. -/
theorem comToLfundefPhysAbiFromVirt_allocOut_resolved (virt0 : Lfundef)
    (shiftImm : ShiftImmOracle) (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap)
    (abiArgs : List String) (abiTyin : List Nat) (residence : Option (Array Nat))
    (abiW : Nat) (forceLivePin reserveVecScratch retToRax : Bool)
    (rm : LOperand → LOperand)
    (hrm : rm =
      let B := fromVirtAllocBody virt0 residence forceLivePin retToRax outStoreMap
      let tbl := straightCallComposeTable B (physTableOut B outStoreMap
        (if reserveVecScratch then [numVecRegs - 1] else []))
      if bodyHasCall B then remapOperandCalleeSave B tbl else remapOperand B tbl)
    (hsib : ∀ i ∈ fromVirtAllocBody virt0 residence forceLivePin retToRax outStoreMap,
      SibAtAddr i.li_i)
    (hdir : ∀ i ∈ fromVirtAllocBody virt0 residence forceLivePin retToRax outStoreMap,
      ∀ o ∈ lopnOperands i.li_i, (∀ b y s, o ≠ .arrIdx b y s) → opResolved (rm o) = true)
    (haddr : ∀ i ∈ fromVirtAllocBody virt0 residence forceLivePin retToRax outStoreMap,
      ∀ b y s, .arrIdx b y s ∈ lopnOperands i.li_i → AddrOk (rm (.arrIdx b y s)))
    (hargs : ∀ s,
      let B := fromVirtAllocBody virt0 residence forceLivePin retToRax outStoreMap
      opResolved (.reg (physNameForBody B (straightCallComposeTable B (physTableOut B
        outStoreMap (if reserveVecScratch then [numVecRegs - 1] else []))) (argName s))) = true)
    (hret : ∀ rn ∈ virt0.lfd_res.head?,
      let B := fromVirtAllocBody virt0 residence forceLivePin retToRax outStoreMap
      opResolved (.reg (physNameForBody B (straightCallComposeTable B (physTableOut B
        outStoreMap (if reserveVecScratch then [numVecRegs - 1] else []))) rn)) = true)
    (habi : ∀ r ∈ abiArgs, abiSlotOfExt r = none → opResolved (.reg r) = true) :
    ∀ r ∈ (comToLfundefPhysAbiFromVirt virt0 shiftImm inLoadMap outStoreMap abiArgs abiTyin
        residence abiW forceLivePin none reserveVecScratch retToRax).lfd_body,
      ∀ o ∈ lopnOperands r.li_i, opResolvedI TwoAddrLegalize.x86Data o = true := by
  intro r hr
  refine (opsResolved_iff_allocOut_x86 _).mp ?_
  cases residence <;>
  · simp only [comToLfundefPhysAbiFromVirt, comToLfundefPhysAbiFromVirtCert, Option.getD_none, List.mem_append,
      ← fromVirtAllocBody_none, ← fromVirtAllocBody_some] at hr
    rcases hr with ((hp | hx) | ha) | hb
    · exact opsResolved_of_wfLinstr (buildPrologue_wf _ _ _ r hp)
    · exact extraInputSaves_resolved _ r hx
    · refine buildArgPtrMaterialize_resolved _ _ abiArgs inLoadMap ?_ habi r ha
      exact hargs
    · refine insertEpilogue_resolved _ _ ?_ ?_ r hb
      · intro r' hr'
        have hmem := (List.mem_filter.mp hr').1
        refine (opsResolved_iff_allocOut_x86 _).mpr
          (physBodyWithStores_allocOut_resolved_abi _
            (fromVirtAllocBody virt0 _ forceLivePin retToRax outStoreMap) inLoadMap outStoreMap abiW _ [] (if reserveVecScratch then [numVecRegs - 1] else [])
            rm hrm hsib hdir haddr ?_ hargs (by simp) r' hmem)
        refine findSnd_resolved _ ?_
        intro p hp
        obtain ⟨⟨abiReg, j⟩, -, hf⟩ := List.mem_filterMap.mp hp
        simp only at hf
        split at hf
        · cases hf
        · split at hf
          · next s hs => cases hf; exact abiSlotOfExt_resolved hs
          · cases hf
      · intro r' hr'
        rcases List.mem_append.mp hr' with hm | hm
        · exact retMat_resolved _ _ _ _ hret r' hm
        · exact opsResolved_of_wfLinstr (calleeSaveRestoreEpilogue_wf r' hm)

/-- The body the allocation of `lfundefPhysAbiOfVirt` runs on: the virtual body with the
    accumulator registers aliased onto the output argument, its memref threads canonicalised,
    and the argument-liveness pin in front for four or more arguments. -/
def ofVirtAllocBody (virt0 : Lfundef) (outArg' : String) (accRegs abiArgs : List String) :
    Lcmd :=
  (if abiArgs.length ≥ 4 then
      [⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
            ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩]
    else []) ++
    canonicalizeMemrefThread (accRegs.foldl (fun b r => aliasRegBody r outArg' b) virt0.lfd_body)

/-- **Every operation of `lfundefPhysAbiOfVirt` is resolved over x86.** On the x86 register
    file, let `B` be the allocated body (`ofVirtAllocBody`). Under the naming hypotheses of
    `physBodyWithStores_allocOut_resolved_abi` on `B` (`hsib`, `hdir`, `haddr`, `hargs`, over
    the composed allocation table), resolved argument names in the plain allocation table that
    the argument materialisation reads (`hphys`) and resolved argument registers read directly
    (`habi`), every instruction of the function body satisfies the `resolved` field of
    `AllocOutInstr x86Data`. -/
theorem lfundefPhysAbiOfVirt_allocOut_resolved (virt0 : Lfundef) (outArg' : String)
    (inArgs' accRegs : List String) (shiftImm : ShiftImmOracle) (abiArgs : List String)
    (abiTyin : List Nat) (posBind : Bool) (rm : LOperand → LOperand)
    (hrm : rm =
      let B := ofVirtAllocBody virt0 outArg' accRegs abiArgs
      let tbl := straightCallComposeTable B (physTableOut B [] [])
      if bodyHasCall B then remapOperandCalleeSave B tbl else remapOperand B tbl)
    (hsib : ∀ i ∈ ofVirtAllocBody virt0 outArg' accRegs abiArgs, SibAtAddr i.li_i)
    (hdir : ∀ i ∈ ofVirtAllocBody virt0 outArg' accRegs abiArgs,
      ∀ o ∈ lopnOperands i.li_i, (∀ b y s, o ≠ .arrIdx b y s) → opResolved (rm o) = true)
    (haddr : ∀ i ∈ ofVirtAllocBody virt0 outArg' accRegs abiArgs, ∀ b y s,
      .arrIdx b y s ∈ lopnOperands i.li_i → AddrOk (rm (.arrIdx b y s)))
    (hargs : ∀ s,
      let B := ofVirtAllocBody virt0 outArg' accRegs abiArgs
      opResolved (.reg (physNameForBody B (straightCallComposeTable B (physTableOut B [] []))
        (argName s))) = true)
    (hphys : ∀ s,
      let B := ofVirtAllocBody virt0 outArg' accRegs abiArgs
      opResolved (.reg (physNameForBody B (physTableOut B []) (argName s))) = true)
    (habi : ∀ r ∈ abiArgs, abiSlotOfExt r = none → opResolved (.reg r) = true) :
    ∀ r ∈ (lfundefPhysAbiOfVirt virt0 outArg' inArgs' accRegs shiftImm abiArgs abiTyin
        (posBind := posBind)).lfd_body,
      ∀ o ∈ lopnOperands r.li_i, opResolvedI TwoAddrLegalize.x86Data o = true := by
  intro r hr
  refine (opsResolved_iff_allocOut_x86 _).mp ?_
  have hB : ∀ (abiArgs : List String),
      (if abiArgs.length ≥ 4 then
        [(⟨0, .Lopn [.reg "%livepin"] "LIVEPIN"
              ((List.range abiArgs.length).map (fun j => (.reg (argName j) : LOperand)))⟩ :
          Linstr)]
      else []) ++
      canonicalizeMemrefThread (accRegs.foldl (fun b r => aliasRegBody r outArg' b)
        virt0.lfd_body) = ofVirtAllocBody virt0 outArg' accRegs abiArgs := fun _ => rfl
  simp only [lfundefPhysAbiOfVirt, lfundefPhysAbiOfVirtCert, List.mem_append, hB] at hr
  rcases hr with ((hp | hx) | ha) | hb
  · exact opsResolved_of_wfLinstr (buildPrologue_wf _ _ _ r hp)
  · exact extraInputSaves_resolved _ r hx
  · refine buildArgPtrMaterialize_resolved _ _ abiArgs _ ?_ habi r ha
    exact hphys
  · refine insertEpilogue_resolved _ _ ?_ ?_ r hb
    · have hmbr : ∀ b q, Option.map Prod.snd
          (List.find? (fun p => p.1 == b)
            (List.filterMap
              (fun x =>
                match abiSaveOfExt x.2 with
                | some saveName =>
                  some
                    (physNameForBody (ofVirtAllocBody virt0 outArg' accRegs abiArgs)
                        (physTableOut (ofVirtAllocBody virt0 outArg' accRegs abiArgs) []) x.1,
                      saveName)
                | none => none)
              (argBasePairs posBind outArg' inArgs' abiArgs))) = some q →
          opResolved (.reg q) = true := by
        refine findSnd_resolved _ ?_
        intro p hp
        obtain ⟨⟨argNm, abiReg⟩, -, hf⟩ := List.mem_filterMap.mp hp
        simp only at hf
        split at hf
        · next s hs => cases hf; exact abiSaveOfExt_resolved hs
        · cases hf
      refine reloadArrImmBody_resolved hmbr ?_
      intro r' hr'
      have hmem := (List.mem_filter.mp hr').1
      refine (opsResolved_iff_allocOut_x86 _).mpr
        (physBodyWithStores_allocOut_resolved_abi _ (ofVirtAllocBody virt0 outArg' accRegs abiArgs)
          _ [] 0 _ _ [] rm hrm hsib hdir haddr hmbr hargs ?_ r' hmem)
      · intro p hp
        obtain ⟨⟨abiReg, j⟩, -, hf⟩ := List.mem_filterMap.mp hp
        simp only at hf
        split at hf
        · next s hs =>
          split_ifs at hf with hc
          cases hf
          exact ⟨opResolved_of_isCallerSavedAllocGPR hc, abiSaveOfExt_resolved hs⟩
        · cases hf
    · exact fun r' hm => opsResolved_of_wfLinstr (calleeSaveRestoreEpilogue_wf r' hm)

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysPositionEmitWF
