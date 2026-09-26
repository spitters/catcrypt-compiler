/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.String.TakeDrop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulMulCarrySel
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminImmShiftMnem

/-!
# Whole-function register-allocation faithfulness with immediate shifts and rotates

`ToLprogFaithfulMulCarrySel.toLprogPhysAbi_faithful_uniformMCS` covers a `Com`
whose bindings are binary `regArith`, `regConst`, `mulhi`, `addCarryLo`,
`addCarryHi` and `select`. This module covers a `Com` whose bindings are those
together with the immediate shifts `shlImm`, `shrImm`, `sarImm` and the rotate
`rorImm`.

`opToLinstrR` emits `shlImm w n` as the one-source head
`Lopn [.reg dst] (withWidthTag w ("SHL:" ++ toString n)) [.reg src]`: the count
is carried in the mnemonic, the single source is the shifted register. `shrImm`,
`sarImm` and `rorImm` are emitted the same way with the bases `SHR:`, `SAR:` and
`ROR:`. Under `physBody` such a head takes the one-source arm: the mnemonic is a
native shift or rotate (`isNativeShiftRotate`), so the instruction is lowered by
`lowerNativeShiftRotate`, which emits it unchanged with renamed operands when
neither renamed operand is a spill slot, and otherwise threads the value through
the reload scratch `R15`. This module covers the first case; the binding kind
carries the non-spill condition `hnsp`.

`JasminLsem.lsemStep` runs the emitted instruction through
`applyOpn (stripWidthTag opn) [src]`, whose count-tagged arm decodes the count
with `parseImmShiftMnem`, a parser over `String.splitOn`. `String.splitOn` is a
well-founded recursion over byte positions with no characterisation lemma, and
it does not reduce in the kernel on a closed string, so the value that arm
returns on the exported mnemonic is not derivable here. The binding kind
`UnaryImmBinding` therefore carries that value as its field `hop`, in the form
`applyOpn opn [a] = some (vval a)` at every word `a`, as `BinopBinding` and
`BinopMovBinding` carry theirs. `applyOpn_unary_of_parse` derives `hop` from a
`parseImmShiftMnem` equation, so a proof of the parser's value on the exported
mnemonic closes the gap for the whole fragment at once.

## Main results

* `stripWidthTag_countTag`: the width tag strips off the exported shift mnemonic
  exactly, for every count other than `64`.
* `isNativeShiftRotate_countTag`: the exported shift mnemonic is a native shift
  or rotate.
* `physBodyElem_unaryImm`: `physBody` expands a non-spill native shift head to
  the single renamed instruction.
* `remapBlockMaintains1`: a one-source single-instruction binding re-establishes
  `StoreRel` against `s ↦ s.setReg nDst (vval (s.lvm nSrc))`.
* `UnaryImmBinding`: the binding kind of an immediate shift or rotate head.
* `applyOpn_unary_of_parse`: the `lsem` value of a one-source instruction whose
  mnemonic `parseImmShiftMnem` decodes.
* `UniformRegArithShift`: the `Com` fragment of `UniformRegArithMCS` together with
  `shlImm`, `shrImm`, `sarImm` and `rorImm` bindings at a count other than `64`.
* `CoverDataShift.uniformRegArithShift`: cover data exists only for that
  fragment; `CoverDataMCS.toShift` embeds the previous fragment's cover data.
* `physBody_lsem_result_uniformShift`: the physical body run of such a `Com`
  reads the composed virtual store at the physical result register.
* `toLprogPhysAbi_faithful_uniformShift`: the whole emitted function body
  `prologue ++ argMatSeq pairs ++ physBody ++ Lret :: rest`, run under `lsemRun`,
  leaves the composed virtual store's result in the physical result register.
* `toLprogPhysAbi_faithful_uniformShift_twoPtr`: the same at the canonical
  `[RDI, RSI]` materialization pairs.
* `toLprogPhysAbi_faithful_uniformShift_epilogue`: the same with the callee-save
  restore epilogue before the `Lret`.

## Scope

A count of `64` is excluded because `SHL:64` ends in the width tag `:64` that
`stripWidthTag` removes, so the exported mnemonic of a shift by `64` reaches
`applyOpn` without its count. A spill operand on the shift head takes the
three-instruction `R15` lowering, which is not covered. The hypotheses on the
emitted body are those of `toLprogPhysAbi_faithful_uniformMCS`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulShift

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminImmShiftMnem
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulSpill
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWriteSide
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBody
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulFlatMap
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulCover
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulNary
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulWholeFn
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulProlog
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulAssembled
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulConst
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulBinopMov
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulMulCarrySel

/-! ## 1. The exported shift mnemonic

The exported mnemonic of an immediate shift or rotate is
`withWidthTag w (m ++ ":" ++ toString n)` with `m` one of the four bases. -/

/-- The four count-tagged mnemonic bases `opToLinstrR` emits for the immediate
    shifts and the rotate. -/
def ShiftBase (m : String) : Prop := m = "SHL" ∨ m = "SHR" ∨ m = "SAR" ∨ m = "ROR"

/-- A shift base carries no separator. -/
theorem ShiftBase.no_colon {m : String} (hm : ShiftBase m) : ∀ c ∈ m.toList, c ≠ ':' := by
  rcases hm with rfl | rfl | rfl | rfl <;> decide

/-- A decimal rendering whose character list is `['6', '4']` renders `64`. -/
theorem toString_eq_64 {n : Nat} (h : (toString n).toList = ['6', '4']) : n = 64 := by
  have h1 := natOfDigits?_toString n
  rw [h] at h1
  have h2 : natOfDigits? ['6', '4'] = some 64 := by decide
  rw [h2] at h1
  exact (Option.some.inj h1).symm

/-- A count-tagged mnemonic ends in `:64` only when its count is `64`. -/
theorem hasSuffix_countTag_eq_false (m : String) {n : Nat} (hn : n ≠ 64) :
    hasSuffix (m ++ ":" ++ toString n) ":64" = false := by
  apply Bool.eq_false_iff.mpr
  intro hsuf
  unfold hasSuffix at hsuf
  rw [List.isSuffixOf_iff_suffix, toList_mnem,
    show (":64" : String).toList = [':', '6', '4'] from by decide] at hsuf
  obtain ⟨t, ht⟩ := hsuf
  have hrev := congrArg List.reverse ht
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.append_assoc] at hrev
  have hnc := toString_no_colon n
  apply hn
  apply toString_eq_64
  have hnil : (toString n).toList ≠ [] := by
    intro h
    have h1 := natOfDigits?_toString n
    rw [h] at h1
    cases h1
  rcases hds : (toString n).toList.reverse with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
  · exact absurd (List.reverse_eq_nil_iff.mp hds) hnil
  · rw [hds] at hrev
    simp at hrev
  · rw [hds] at hrev
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrev
    obtain ⟨rfl, rfl, _⟩ := hrev
    have := congrArg List.reverse hds
    simpa using this
  · rw [hds] at hrev
    simp only [List.cons_append, List.cons.injEq] at hrev
    obtain ⟨_, _, hc, _⟩ := hrev
    exfalso
    apply hnc c _ hc.symm
    have : c ∈ (toString n).toList.reverse := by rw [hds]; simp
    exact List.mem_reverse.mp this

/-- The width tag strips off the exported shift mnemonic exactly, at every width
    and every count other than `64`. -/
theorem stripWidthTag_countTag {m : String} (hm : ShiftBase m) (w : Nat) {n : Nat}
    (hn : n ≠ 64) :
    stripWidthTag (withWidthTag w (m ++ ":" ++ toString n)) = m ++ ":" ++ toString n := by
  unfold withWidthTag
  split
  · exact stripWidthTag_append64 _
  · unfold stripWidthTag
    rw [hasSuffix_countTag_eq_false m hn]
    rfl

/-- A string starts with any of its own prefixes. -/
theorem hasPrefix_append_self (p t : String) : hasPrefix (p ++ t) p = true := by
  unfold hasPrefix
  rw [List.isPrefixOf_iff_prefix, String.toList_append]
  exact List.prefix_append _ _

/-- The exported shift mnemonic is a native shift or rotate. -/
theorem isNativeShiftRotate_countTag {m : String} (hm : ShiftBase m) (w : Nat) {n : Nat}
    (hn : n ≠ 64) :
    isNativeShiftRotate (withWidthTag w (m ++ ":" ++ toString n)) = true := by
  simp only [isNativeShiftRotate, stripWidthTag_countTag hm w hn,
    string_isPrefixOf_eq_hasPrefix, List.any_cons, List.any_nil, Bool.or_false]
  rcases hm with rfl | rfl | rfl | rfl <;>
    simp only [show ("SHL" : String) ++ ":" = "SHL:" from rfl,
      show ("SHR" : String) ++ ":" = "SHR:" from rfl,
      show ("SAR" : String) ++ ":" = "SAR:" from rfl,
      show ("ROR" : String) ++ ":" = "ROR:" from rfl,
      hasPrefix_append_self, Bool.or_true, Bool.true_or]

/-! ## 2. The one-source step and its maintenance -/

/-- A one-source single-instruction step: when the modeled opcode applies to the
    evaluated register source, the instruction writes that value at the
    destination and advances the pc. -/
theorem lsemStep_src1 {w : Nat} (nD nA opn : String) (s : Lstate w) (v : BitVec w)
    (hv : applyOpn (stripWidthTag opn) [s.lvm nA] = some v) :
    lsemStep (.Lopn [.reg nD] opn [.reg nA]) s = some ((s.setReg nD v).nextPc) := by
  simp only [lsemStep, List.map_cons, List.map_nil, evalOperand, hv]

/-- **Maintenance of a one-source single-instruction binding.** The renamed
    instruction `opn ρ nDst, ρ nSrc` re-establishes `StoreRel` against
    `s ↦ s.setReg nDst (vval (s.lvm nSrc))`, given the modeled-opcode premise
    `hop` at every word and the destination injectivity `hinj`. -/
theorem remapBlockMaintains1 {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (Lin Lout : List String)
    (nDst nSrc opn : String) (vval : BitVec w → BitVec w)
    (hSrcIn : nSrc ∈ Lin)
    (hinj : ∀ m ∈ Lout, physRename body tbl m = physRename body tbl nDst → m = nDst)
    (hcarry : ∀ m ∈ Lout, m ≠ nDst → m ∈ Lin)
    (hop : ∀ a : BitVec w, applyOpn (stripWidthTag opn) [a] = some (vval a)) :
    BlockMaintains body tbl Lin Lout
      [.Lopn [.reg (physRename body tbl nDst)] opn [.reg (physRename body tbl nSrc)]]
      (fun s => s.setReg nDst (vval (s.lvm nSrc))) := by
  intro s s' hrel
  have hop' : applyOpn (stripWidthTag opn) [s'.lvm (physRename body tbl nSrc)]
      = some (vval (s.lvm nSrc)) := by
    rw [hrel nSrc hSrcIn]; exact hop _
  refine ⟨(s'.setReg (physRename body tbl nDst) (vval (s.lvm nSrc))).nextPc, ?_, ?_⟩
  · rw [lsemStraight_cons,
      lsemStep_src1 (physRename body tbl nDst) (physRename body tbl nSrc) opn s' _ hop']
    rfl
  · intro m hmL
    by_cases hm : physRename body tbl m = physRename body tbl nDst
    · have hmd : m = nDst := hinj m hmL hm
      subst hmd
      simp
    · have hmne : m ≠ nDst := fun he => hm (by rw [he])
      simp only [Lstate.lvm_nextPc, Lstate.lvm_setReg, if_neg hm, if_neg hmne]
      exact hrel m (hcarry m hmL hmne)

/-! ## 3. The binding kind -/

/-- An immediate shift or rotate binding along the renaming
    `physRename body tbl`: the logical destination `nDst` receives `vval` of the
    value at `nSrc`, where `vval` is the `lsem` value of the count-tagged
    mnemonic `opn` (`hop`); neither renamed operand is a spill slot (`hnsp`), and
    no other logical name is renamed onto the physical register of `nDst`. -/
structure UnaryImmBinding (w : Nat) (body : Lcmd) (tbl : Array Nat) where
  /-- The logical destination name. -/
  nDst : String
  /-- The logical source name. -/
  nSrc : String
  /-- The count-tagged mnemonic, width tag included. -/
  opn : String
  /-- The value written at the destination, as a function of the source word. -/
  vval : BitVec w → BitVec w
  /-- The logical names live before the binding. -/
  Lin : List String
  /-- The logical names live after the binding. -/
  Lout : List String
  /-- The binding reads its source. -/
  hSrcIn : nSrc ∈ Lin
  /-- No other name live after the binding shares the destination's physical
      register. -/
  hinj : ∀ m ∈ Lout, physRename body tbl m = physRename body tbl nDst → m = nDst
  /-- Every name live after the binding other than its destination was already
      live before it. -/
  hcarry : ∀ m ∈ Lout, m ≠ nDst → m ∈ Lin
  /-- Neither renamed operand is a spill slot. -/
  hnsp : ((LOperand.reg (physRename body tbl nDst)).isSpill
      || (LOperand.reg (physRename body tbl nSrc)).isSpill) = false
  /-- The `lsem` value of the mnemonic at every source word. -/
  hop : ∀ a : BitVec w, applyOpn (stripWidthTag opn) [a] = some (vval a)

/-- The physical block of an immediate shift or rotate binding:
    `opn ρ nDst, ρ nSrc`. -/
def UnaryImmBinding.block {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : UnaryImmBinding w body tbl) : List LinstrR :=
  [.Lopn [.reg (physRename body tbl b.nDst)] b.opn [.reg (physRename body tbl b.nSrc)]]

/-- The virtual transformer of an immediate shift or rotate binding: write
    `vval` of the source value at `nDst`. -/
def UnaryImmBinding.vstep {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : UnaryImmBinding w body tbl) : Lstate w → Lstate w :=
  fun s => s.setReg b.nDst (b.vval (s.lvm b.nSrc))

/-- An immediate shift or rotate binding's block re-establishes `StoreRel`
    against its virtual transformer. -/
theorem UnaryImmBinding.maintains {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : UnaryImmBinding w body tbl) :
    BlockMaintains body tbl b.Lin b.Lout b.block b.vstep :=
  remapBlockMaintains1 body tbl b.Lin b.Lout b.nDst b.nSrc b.opn b.vval
    b.hSrcIn b.hinj b.hcarry b.hop

/-! ## 4. The `physBody` expansion of a native shift head -/

/-- `physBody` expands a one-source native shift or rotate head whose renamed
    operands are not spill slots to the single renamed instruction. -/
theorem physBodyElem_unaryImm (body : Lcmd) (tbl : Array Nat) (ii : Nat)
    (nDst nSrc opn : String)
    (hnat : isNativeShiftRotate opn = true)
    (hnsp : ((LOperand.reg (physRename body tbl nDst)).isSpill
      || (LOperand.reg (physRename body tbl nSrc)).isSpill) = false) :
    (physBodyElem body tbl ⟨ii, .Lopn [.reg nDst] opn [.reg nSrc]⟩).map (·.li_i)
      = [.Lopn [.reg (physRename body tbl nDst)] opn [.reg (physRename body tbl nSrc)]] := by
  simp only [physBodyElem, hnat, if_true, remapOperand_reg, lowerNativeShiftRotate, hnsp,
    Bool.false_eq_true, if_false, List.map_cons, List.map_nil]

/-! ## 5. The `lsem` value of a decoded mnemonic -/

/-- The value `applyOpn` gives a one-source instruction whose mnemonic is none of
    the named one-source opcodes and which `parseImmShiftMnem` decodes: the
    decoded direction applied at the decoded count. -/
theorem applyOpn_unary_of_parse {w : Nat} (opn : String) (att : String) (k wd : Nat)
    (hne : opn ∉ ["MOV", "MOVQ", "MOV:8", "MOV:16", "LOADIDX", "STOREIDX"])
    (hp : parseImmShiftMnem opn = some (att, k, wd)) (a : BitVec w) :
    applyOpn opn [a]
      = some (if att = "shl" then a <<< k
          else if att = "sar" then BitVec.sshiftRight a k
          else if att = "rol" then a.rotateLeft k
          else if att = "ror" then a.rotateRight k
          else a >>> k) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hne
  unfold applyOpn
  split <;> simp_all

/-- The character lists of the four shift bases. -/
theorem ShiftBase.toList {m : String} (hm : ShiftBase m) :
    m.toList = ['S', 'H', 'L'] ∨ m.toList = ['S', 'H', 'R'] ∨ m.toList = ['S', 'A', 'R']
      ∨ m.toList = ['R', 'O', 'R'] := by
  rcases hm with rfl | rfl | rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inl (by decide))
  · exact Or.inr (Or.inr (Or.inl (by decide)))
  · exact Or.inr (Or.inr (Or.inr (by decide)))

/-- The first two characters of an exported shift mnemonic are those of its
    base, which no named one-source opcode shares. -/
theorem countTag_ne_unary {m : String} (hm : ShiftBase m) (n : Nat) :
    (m ++ ":" ++ toString n) ∉ ["MOV", "MOVQ", "MOV:8", "MOV:16", "LOADIDX", "STOREIDX"] := by
  intro hmem
  have key : ∀ u ∈ ["MOV", "MOVQ", "MOV:8", "MOV:16", "LOADIDX", "STOREIDX"],
      (m ++ ":" ++ toString n).toList.take 2 ≠ u.toList.take 2 := by
    have hpre : (m ++ ":" ++ toString n).toList.take 2 = m.toList.take 2 := by
      rw [toList_mnem]
      rcases hm.toList with h | h | h | h <;> rw [h] <;> rfl
    rw [hpre]
    rcases hm.toList with h | h | h | h <;> rw [h] <;> decide
  exact key _ hmem rfl

/-- The `lsem` value of an exported immediate shift or rotate whose mnemonic
    `parseImmShiftMnem` decodes. -/
theorem applyOpn_countTag_of_parse {w : Nat} {m : String} (hm : ShiftBase m) (wOp : Nat)
    {n : Nat} (hn : n ≠ 64) (att : String) (k wd : Nat)
    (hp : parseImmShiftMnem (m ++ ":" ++ toString n) = some (att, k, wd)) (a : BitVec w) :
    applyOpn (stripWidthTag (withWidthTag wOp (m ++ ":" ++ toString n))) [a]
      = some (if att = "shl" then a <<< k
          else if att = "sar" then BitVec.sshiftRight a k
          else if att = "rol" then a.rotateLeft k
          else if att = "ror" then a.rotateRight k
          else a >>> k) := by
  rw [stripWidthTag_countTag hm wOp hn]
  exact applyOpn_unary_of_parse _ att k wd (countTag_ne_unary hm n) hp a

/-! ## 6. The sum of binding kinds -/

/-- A binding of the previous fragment or an immediate shift or rotate binding. -/
inductive ShiftBinding (w : Nat) (body : Lcmd) (tbl : Array Nat) where
  | mcs (b : MulCarryBinding w body tbl)
  | unaryImm (u : UnaryImmBinding w body tbl)

/-- The physical block of a binding. -/
def ShiftBinding.block {w : Nat} {body : Lcmd} {tbl : Array Nat} :
    ShiftBinding w body tbl → List LinstrR
  | .mcs b => b.block
  | .unaryImm u => u.block

/-- The virtual transformer of a binding. -/
def ShiftBinding.vstep {w : Nat} {body : Lcmd} {tbl : Array Nat} :
    ShiftBinding w body tbl → Lstate w → Lstate w
  | .mcs b => b.vstep
  | .unaryImm u => u.vstep

/-- The logical names live before a binding. -/
def ShiftBinding.Lin {w : Nat} {body : Lcmd} {tbl : Array Nat} :
    ShiftBinding w body tbl → List String
  | .mcs b => b.Lin
  | .unaryImm u => u.Lin

/-- The logical names live after a binding. -/
def ShiftBinding.Lout {w : Nat} {body : Lcmd} {tbl : Array Nat} :
    ShiftBinding w body tbl → List String
  | .mcs b => b.Lout
  | .unaryImm u => u.Lout

/-- Every binding's block is a `BlockMaintains` witness across its live sets. -/
theorem ShiftBinding.maintains {w : Nat} {body : Lcmd} {tbl : Array Nat}
    (b : ShiftBinding w body tbl) :
    BlockMaintains body tbl b.Lin b.Lout b.block b.vstep := by
  cases b with
  | mcs b => exact b.maintains
  | unaryImm u => exact u.maintains

/-- A cover of a source body by a binding list: the `physBody` expansion of the
    `i`-th instruction, projected to `LinstrR`, is the `i`-th binding's block. -/
inductive BodyCoverShift {w : Nat} (body : Lcmd) (tbl : Array Nat) :
    Lcmd → List (ShiftBinding w body tbl) → Prop where
  | nil : BodyCoverShift body tbl [] []
  | cons {i : Linstr} {b : ShiftBinding w body tbl} {is : Lcmd}
      {bs : List (ShiftBinding w body tbl)} :
      (physBodyElem body tbl i).map (·.li_i) = b.block → BodyCoverShift body tbl is bs →
      BodyCoverShift body tbl (i :: is) (b :: bs)

/-- The `physBody` expansion of a covered sub-body is the flattened block list. -/
theorem physBody_flatMap_blocksShift {w : Nat} (body : Lcmd) (sub : Lcmd)
    (bs : List (ShiftBinding w body (bodyPhysTable body)))
    (hcover : BodyCoverShift body (bodyPhysTable body) sub bs) :
    sub.flatMap (fun i => (physBodyElem body (bodyPhysTable body) i).map (·.li_i))
      = (bs.map (·.block)).flatten := by
  induction hcover with
  | nil => rfl
  | cons hib _ ih => rw [List.flatMap_cons, List.map_cons, List.flatten_cons, ih, hib]

/-- The literal `physBody` of a covered body, projected to `LinstrR`, is the
    flattened block list. -/
theorem physBody_map_li_iShift {w : Nat} (body : Lcmd)
    (bs : List (ShiftBinding w body (bodyPhysTable body)))
    (hcover : BodyCoverShift body (bodyPhysTable body) body bs) :
    (physBody (fun _ => none) body).map (·.li_i) = (bs.map (·.block)).flatten := by
  rw [physBody_eq_flatMap, List.map_flatMap]
  exact physBody_flatMap_blocksShift body body bs hcover

/-- Running the flattened block list of a binding list from a `StoreRel`-related
    start reads the composed virtual store at every renamed register. -/
theorem shiftBody_lsem_result {w : Nat} (body : Lcmd) (tbl : Array Nat)
    (bs : List (ShiftBinding w body tbl)) (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w)
    (hrel : StoreRel body tbl L s s') (nRes : String) (hnRes : nRes ∈ N) :
    ∃ s'', lsemStraight ((bs.map (·.block)).flatten) s' = some s''
      ∧ s''.lvm (physRename body tbl nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  have hmaint : BlocksMaintain body tbl L N (bs.map (fun b => (b.block, b.vstep))) :=
    blocksMaintain_of_chained body tbl bs N (·.Lin) (·.Lout) (·.block) (·.vstep)
      L (fun b _ => b.maintains) hch
  have hkey := physBlocks_storeRel_result body tbl L N
    (bs.map (fun b => (b.block, b.vstep))) hmaint s s' hrel nRes hnRes
  have hreidx : ((bs.map (fun b => (b.block, b.vstep))).map Prod.fst) = bs.map (·.block) := by
    rw [List.map_map]; rfl
  rw [hreidx] at hkey
  exact hkey

/-- Physical faithfulness of the literal `physBody` on a covered body. -/
theorem physBody_lsem_resultShift {w : Nat} (body : Lcmd)
    (bs : List (ShiftBinding w body (bodyPhysTable body)))
    (hcover : BodyCoverShift body (bodyPhysTable body) body bs)
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w) (hrel : StoreRel body (bodyPhysTable body) L s s')
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ s'', lsemStraight ((physBody (fun _ => none) body).map (·.li_i)) s' = some s''
      ∧ s''.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  rw [physBody_map_li_iShift body bs hcover]
  exact shiftBody_lsem_result body (bodyPhysTable body) bs L N hch s s' hrel nRes hnRes

/-! ## 7. The `Com` fragment and its threaded cover data -/

/-- A `Com` all of whose bindings are those of `UniformRegArithMCS` or immediate
    shifts `shlImm` / `shrImm` / `sarImm` or rotates `rorImm` at a count other
    than `64`, terminating at `.ret`. -/
inductive UniformRegArithShift : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → Prop where
  | ret {Γ t} (v : Ctxt.Var Γ t) : UniformRegArithShift (.ret v)
  | var {Γ s} {w : Nat} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
      (a0 a1 : Ctxt.Var Γ (JasminTy.reg w)) (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hw : w ≠ 64) (hns : NonShift bop) (hbody : UniformRegArithShift body) :
      UniformRegArithShift
        (.var ⟨JasminOp.regArith bop w, heq, .cons a0 (.cons a1 .nil)⟩ body)
  | var64 {Γ s} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop 64) = .reg 64)
      (a0 a1 : Ctxt.Var Γ (JasminTy.reg 64))
      (body : Com jasminDialect (JasminTy.reg 64 :: Γ) s)
      (hns : NonShift bop) (hbody : UniformRegArithShift body) :
      UniformRegArithShift
        (.var ⟨JasminOp.regArith bop 64, heq, .cons a0 (.cons a1 .nil)⟩ body)
  | const {Γ s} {w n : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
      (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hbody : UniformRegArithShift body) :
      UniformRegArithShift (.var ⟨JasminOp.regConst w n, heq, .nil⟩ body)
  | mulhi {Γ s} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
      (a0 a1 : Ctxt.Var Γ (JasminTy.reg w)) (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hbody : UniformRegArithShift body) :
      UniformRegArithShift (.var ⟨JasminOp.mulhi w, heq, .cons a0 (.cons a1 .nil)⟩ body)
  | addCarryLo {Γ s} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
      (a0 a1 : Ctxt.Var Γ (JasminTy.reg w)) (a2 : Ctxt.Var Γ (JasminTy.reg 1))
      (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hbody : UniformRegArithShift body) :
      UniformRegArithShift
        (.var ⟨JasminOp.addCarryLo w, heq, .cons a0 (.cons a1 (.cons a2 .nil))⟩ body)
  | addCarryHi {Γ s} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
      (a0 a1 : Ctxt.Var Γ (JasminTy.reg w)) (a2 : Ctxt.Var Γ (JasminTy.reg 1))
      (body : Com jasminDialect (JasminTy.reg 1 :: Γ) s)
      (hbody : UniformRegArithShift body) :
      UniformRegArithShift
        (.var ⟨JasminOp.addCarryHi w, heq, .cons a0 (.cons a1 (.cons a2 .nil))⟩ body)
  | select {Γ s} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
      (c : Ctxt.Var Γ (JasminTy.reg 1)) (a0 a1 : Ctxt.Var Γ (JasminTy.reg w))
      (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hbody : UniformRegArithShift body) :
      UniformRegArithShift
        (.var ⟨JasminOp.select w, heq, .cons c (.cons a0 (.cons a1 .nil))⟩ body)
  | shlImm {Γ s} {w n : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
      (a0 : Ctxt.Var Γ (JasminTy.reg w)) (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hn : n ≠ 64) (hbody : UniformRegArithShift body) :
      UniformRegArithShift (.var ⟨JasminOp.shlImm w n, heq, .cons a0 .nil⟩ body)
  | shrImm {Γ s} {w n : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
      (a0 : Ctxt.Var Γ (JasminTy.reg w)) (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hn : n ≠ 64) (hbody : UniformRegArithShift body) :
      UniformRegArithShift (.var ⟨JasminOp.shrImm w n, heq, .cons a0 .nil⟩ body)
  | sarImm {Γ s} {w n : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
      (a0 : Ctxt.Var Γ (JasminTy.reg w)) (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hn : n ≠ 64) (hbody : UniformRegArithShift body) :
      UniformRegArithShift (.var ⟨JasminOp.sarImm w n, heq, .cons a0 .nil⟩ body)
  | rorImm {Γ s} {w n : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.rorImm w n) = .reg w)
      (a0 : Ctxt.Var Γ (JasminTy.reg w)) (body : Com jasminDialect (JasminTy.reg w :: Γ) s)
      (hn : n ≠ 64) (hbody : UniformRegArithShift body) :
      UniformRegArithShift (.var ⟨JasminOp.rorImm w n, heq, .cons a0 .nil⟩ body)

/-- The previous fragment is contained in the shift fragment. -/
theorem UniformRegArithMCS.toShift {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (h : UniformRegArithMCS com) :
    UniformRegArithShift com := by
  induction h with
  | ret v => exact .ret v
  | var bop heq a0 a1 body hw hns _ ih => exact .var bop heq a0 a1 body hw hns ih
  | var64 bop heq a0 a1 body hns _ ih => exact .var64 bop heq a0 a1 body hns ih
  | const heq body _ ih => exact .const heq body ih
  | mulhi heq a0 a1 body _ ih => exact .mulhi heq a0 a1 body ih
  | addCarryLo heq a0 a1 a2 body _ ih => exact .addCarryLo heq a0 a1 a2 body ih
  | addCarryHi heq a0 a1 a2 body _ ih => exact .addCarryHi heq a0 a1 a2 body ih
  | select heq c a0 a1 body _ ih => exact .select heq c a0 a1 body ih

/-- Cover data threaded along a shift-fragment `Com` over a fixed whole
    `body`/`tbl`. The arms of the previous fragment carry the data of
    `CoverDataMCS`; the four shift arms carry a `UnaryImmBinding` whose
    destination is `regName d`, whose source is the resolved operand name, whose
    mnemonic is the exported count-tagged mnemonic and whose value is the
    dialect's shift or rotate at the count. -/
inductive CoverDataShift {w : Nat} (body : Lcmd) (tbl : Array Nat) (nArgs : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) →
    List (ShiftBinding w body tbl) → Prop where
  | ret {Γ t} (v : Ctxt.Var Γ t) (d : Nat) : CoverDataShift body tbl nArgs (.ret v) d []
  | var {Γ s} {bop : JasminBinOp}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w}
      {a0 a1 : Ctxt.Var Γ (JasminTy.reg w)} {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (hw : w ≠ 64) (hns : bop ≠ .shl ∧ bop ≠ .shr ∧ bop ≠ .andn)
      (b : BinopBinding w body tbl) (bs : List (ShiftBinding w body tbl))
      (hdst : b.nDst = regName d)
      (hopn : b.opn = withWidthTag w (binOpName bop))
      (hsrc : b.nSrc = resolveVarName d nArgs a1)
      (hcol : physRename body tbl (resolveVarName d nArgs a0)
          = physRename body tbl (regName d))
      (htail : CoverDataShift body tbl nArgs bdy (d + 1) bs) :
      CoverDataShift body tbl nArgs
        (.var ⟨JasminOp.regArith bop w, heq, .cons a0 (.cons a1 .nil)⟩ bdy) d
        (.mcs (.arith (.binop b)) :: bs)
  | var64 {Γ s} {bop : JasminBinOp}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop 64) = .reg 64}
      {a0 a1 : Ctxt.Var Γ (JasminTy.reg 64)}
      {bdy : Com jasminDialect (JasminTy.reg 64 :: Γ) s}
      (d : Nat) (hns : NonShift bop)
      (b : ToLprogFaithfulBinopWide.BinopWideBinding w body tbl)
      (bs : List (ShiftBinding w body tbl))
      (hdst : b.nDst = regName d)
      (hbop : b.bop = bop)
      (hsrc : b.nSrc = resolveVarName d nArgs a1)
      (hcol : physRename body tbl (resolveVarName d nArgs a0)
          = physRename body tbl (regName d))
      (htail : CoverDataShift body tbl nArgs bdy (d + 1) bs) :
      CoverDataShift body tbl nArgs
        (.var ⟨JasminOp.regArith bop 64, heq, .cons a0 (.cons a1 .nil)⟩ bdy) d
        (.mcs (.binopWide b) :: bs)
  | varMov {Γ s} {bop : JasminBinOp}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w}
      {a0 a1 : Ctxt.Var Γ (JasminTy.reg w)} {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (hw : w ≠ 64) (hns : NonShift bop)
      (b : ToLprogFaithfulBinopMov.BinopMovBinding w body tbl)
      (bs : List (ShiftBinding w body tbl))
      (hdst : b.nDst = regName d)
      (hopn : b.opn = withWidthTag w (binOpName bop))
      (hS0 : b.nS0 = resolveVarName d nArgs a0)
      (hsrc : b.nSrc = resolveVarName d nArgs a1)
      (htail : CoverDataShift body tbl nArgs bdy (d + 1) bs) :
      CoverDataShift body tbl nArgs
        (.var ⟨JasminOp.regArith bop w, heq, .cons a0 (.cons a1 .nil)⟩ bdy) d
        (.mcs (.binopMov b) :: bs)
  | var64Mov {Γ s} {bop : JasminBinOp}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop 64) = .reg 64}
      {a0 a1 : Ctxt.Var Γ (JasminTy.reg 64)}
      {bdy : Com jasminDialect (JasminTy.reg 64 :: Γ) s}
      (d : Nat) (hns : NonShift bop)
      (b : ToLprogFaithfulBinopMov.BinopMovWideBinding w body tbl)
      (bs : List (ShiftBinding w body tbl))
      (hdst : b.nDst = regName d)
      (hbop : b.bop = bop)
      (hS0 : b.nS0 = resolveVarName d nArgs a0)
      (hsrc : b.nSrc = resolveVarName d nArgs a1)
      (htail : CoverDataShift body tbl nArgs bdy (d + 1) bs) :
      CoverDataShift body tbl nArgs
        (.var ⟨JasminOp.regArith bop 64, heq, .cons a0 (.cons a1 .nil)⟩ bdy) d
        (.mcs (.binopMovWide b) :: bs)
  | const {Γ s} {n : Nat}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w}
      {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (c : ConstBinding w body tbl) (bs : List (ShiftBinding w body tbl))
      (hdst : c.nDst = regName d) (hn : c.n = n)
      (htail : CoverDataShift body tbl nArgs bdy (d + 1) bs) :
      CoverDataShift body tbl nArgs
        (.var ⟨JasminOp.regConst w n, heq, .nil⟩ bdy) d (.mcs (.arith (.const c)) :: bs)
  | mulhi {Γ s}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w}
      {a0 a1 : Ctxt.Var Γ (JasminTy.reg w)} {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (m : MulHiBinding w body tbl) (bs : List (ShiftBinding w body tbl))
      (hdst : m.nDst = regName d)
      (hA : m.nA = resolveVarName d nArgs a0)
      (hB : m.nB = resolveVarName d nArgs a1)
      (htail : CoverDataShift body tbl nArgs bdy (d + 1) bs) :
      CoverDataShift body tbl nArgs
        (.var ⟨JasminOp.mulhi w, heq, .cons a0 (.cons a1 .nil)⟩ bdy) d (.mcs (.mulhi m) :: bs)
  | addCarryLo {Γ s}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w}
      {a0 a1 : Ctxt.Var Γ (JasminTy.reg w)} {a2 : Ctxt.Var Γ (JasminTy.reg 1)}
      {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (c : AddCarryLoBinding w body tbl) (bs : List (ShiftBinding w body tbl))
      (hdst : c.nDst = regName d)
      (hA : c.nA = resolveVarName d nArgs a0)
      (hB : c.nB = resolveVarName d nArgs a1)
      (hC : c.nC = resolveVarName d nArgs a2)
      (htail : CoverDataShift body tbl nArgs bdy (d + 1) bs) :
      CoverDataShift body tbl nArgs
        (.var ⟨JasminOp.addCarryLo w, heq, .cons a0 (.cons a1 (.cons a2 .nil))⟩ bdy) d
        (.mcs (.addCarryLo c) :: bs)
  | addCarryHi {Γ s}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1}
      {a0 a1 : Ctxt.Var Γ (JasminTy.reg w)} {a2 : Ctxt.Var Γ (JasminTy.reg 1)}
      {bdy : Com jasminDialect (JasminTy.reg 1 :: Γ) s}
      (d : Nat) (c : AddCarryHiBinding w body tbl) (bs : List (ShiftBinding w body tbl))
      (hdst : c.nDst = regName d)
      (hA : c.nA = resolveVarName d nArgs a0)
      (hB : c.nB = resolveVarName d nArgs a1)
      (hC : c.nC = resolveVarName d nArgs a2)
      (htail : CoverDataShift body tbl nArgs bdy (d + 1) bs) :
      CoverDataShift body tbl nArgs
        (.var ⟨JasminOp.addCarryHi w, heq, .cons a0 (.cons a1 (.cons a2 .nil))⟩ bdy) d
        (.mcs (.addCarryHi c) :: bs)
  | select {Γ s}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w}
      {a0 : Ctxt.Var Γ (JasminTy.reg 1)} {a1 a2 : Ctxt.Var Γ (JasminTy.reg w)}
      {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (c : SelectBinding w body tbl) (bs : List (ShiftBinding w body tbl))
      (hdst : c.nDst = regName d)
      (hCond : c.nCond = resolveVarName d nArgs a0)
      (hA : c.nA = resolveVarName d nArgs a1)
      (hB : c.nB = resolveVarName d nArgs a2)
      (htail : CoverDataShift body tbl nArgs bdy (d + 1) bs) :
      CoverDataShift body tbl nArgs
        (.var ⟨JasminOp.select w, heq, .cons a0 (.cons a1 (.cons a2 .nil))⟩ bdy) d
        (.mcs (.select c) :: bs)
  | shlImm {Γ s} {n : Nat}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w}
      {a0 : Ctxt.Var Γ (JasminTy.reg w)} {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (hn : n ≠ 64) (u : UnaryImmBinding w body tbl)
      (bs : List (ShiftBinding w body tbl))
      (hdst : u.nDst = regName d)
      (hsrc : u.nSrc = resolveVarName d nArgs a0)
      (hopn : u.opn = withWidthTag w ("SHL:" ++ toString n))
      (hval : u.vval = fun a : BitVec w => a <<< n)
      (htail : CoverDataShift body tbl nArgs bdy (d + 1) bs) :
      CoverDataShift body tbl nArgs
        (.var ⟨JasminOp.shlImm w n, heq, .cons a0 .nil⟩ bdy) d (.unaryImm u :: bs)
  | shrImm {Γ s} {n : Nat}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w}
      {a0 : Ctxt.Var Γ (JasminTy.reg w)} {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (hn : n ≠ 64) (u : UnaryImmBinding w body tbl)
      (bs : List (ShiftBinding w body tbl))
      (hdst : u.nDst = regName d)
      (hsrc : u.nSrc = resolveVarName d nArgs a0)
      (hopn : u.opn = withWidthTag w ("SHR:" ++ toString n))
      (hval : u.vval = fun a : BitVec w => a >>> n)
      (htail : CoverDataShift body tbl nArgs bdy (d + 1) bs) :
      CoverDataShift body tbl nArgs
        (.var ⟨JasminOp.shrImm w n, heq, .cons a0 .nil⟩ bdy) d (.unaryImm u :: bs)
  | sarImm {Γ s} {n : Nat}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w}
      {a0 : Ctxt.Var Γ (JasminTy.reg w)} {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (hn : n ≠ 64) (u : UnaryImmBinding w body tbl)
      (bs : List (ShiftBinding w body tbl))
      (hdst : u.nDst = regName d)
      (hsrc : u.nSrc = resolveVarName d nArgs a0)
      (hopn : u.opn = withWidthTag w ("SAR:" ++ toString n))
      (hval : u.vval = fun a : BitVec w => BitVec.sshiftRight a n)
      (htail : CoverDataShift body tbl nArgs bdy (d + 1) bs) :
      CoverDataShift body tbl nArgs
        (.var ⟨JasminOp.sarImm w n, heq, .cons a0 .nil⟩ bdy) d (.unaryImm u :: bs)
  | rorImm {Γ s} {n : Nat}
      {heq : DialectSignature.ret (d := jasminDialect) (JasminOp.rorImm w n) = .reg w}
      {a0 : Ctxt.Var Γ (JasminTy.reg w)} {bdy : Com jasminDialect (JasminTy.reg w :: Γ) s}
      (d : Nat) (hn : n ≠ 64) (u : UnaryImmBinding w body tbl)
      (bs : List (ShiftBinding w body tbl))
      (hdst : u.nDst = regName d)
      (hsrc : u.nSrc = resolveVarName d nArgs a0)
      (hopn : u.opn = withWidthTag w ("ROR:" ++ toString n))
      (hval : u.vval = fun a : BitVec w => a.rotateRight n)
      (htail : CoverDataShift body tbl nArgs bdy (d + 1) bs) :
      CoverDataShift body tbl nArgs
        (.var ⟨JasminOp.rorImm w n, heq, .cons a0 .nil⟩ bdy) d (.unaryImm u :: bs)

/-- Cover data exists only for a shift-fragment `Com`. -/
theorem CoverDataShift.uniformRegArithShift {w : Nat} {body : Lcmd} {tbl : Array Nat}
    {nArgs : Nat} {Γ : Ctxt jasminDialect} {t : JasminTy} {com : Com jasminDialect Γ t}
    {d : Nat} {bs : List (ShiftBinding w body tbl)}
    (h : CoverDataShift body tbl nArgs com d bs) : UniformRegArithShift com := by
  induction h with
  | ret v d => exact .ret v
  | var d hw hns b bs _ _ _ _ _ ih => exact .var _ _ _ _ _ hw hns ih
  | var64 d hns b bs _ _ _ _ _ ih => exact .var64 _ _ _ _ _ hns ih
  | varMov d hw hns b bs _ _ _ _ _ ih => exact .var _ _ _ _ _ hw hns ih
  | var64Mov d hns b bs _ _ _ _ _ ih => exact .var64 _ _ _ _ _ hns ih
  | const d c bs _ _ _ ih => exact .const _ _ ih
  | mulhi d m bs _ _ _ _ ih => exact .mulhi _ _ _ _ ih
  | addCarryLo d c bs _ _ _ _ _ ih => exact .addCarryLo _ _ _ _ _ ih
  | addCarryHi d c bs _ _ _ _ _ ih => exact .addCarryHi _ _ _ _ _ ih
  | select d c bs _ _ _ _ _ ih => exact .select _ _ _ _ _ ih
  | shlImm d hn u bs _ _ _ _ _ ih => exact .shlImm _ _ _ hn ih
  | shrImm d hn u bs _ _ _ _ _ ih => exact .shrImm _ _ _ hn ih
  | sarImm d hn u bs _ _ _ _ _ ih => exact .sarImm _ _ _ hn ih
  | rorImm d hn u bs _ _ _ _ _ ih => exact .rorImm _ _ _ hn ih

/-- Cover data of the previous fragment is cover data of the shift fragment, with
    every binding tagged `mcs`. -/
theorem CoverDataMCS.toShift {w : Nat} {body : Lcmd} {tbl : Array Nat} {nArgs : Nat}
    {Γ : Ctxt jasminDialect} {t : JasminTy} {com : Com jasminDialect Γ t} {d : Nat}
    {bs : List (MulCarryBinding w body tbl)}
    (h : CoverDataMCS body tbl nArgs com d bs) :
    CoverDataShift body tbl nArgs com d (bs.map .mcs) := by
  induction h with
  | ret v d => exact .ret v d
  | var d hw hns b bs hdst hopn hsrc hcol _ ih => exact .var d hw hns b _ hdst hopn hsrc hcol ih
  | var64 d hns b bs hdst hbop hsrc hcol _ ih => exact .var64 d hns b _ hdst hbop hsrc hcol ih
  | varMov d hw hns b bs hdst hopn hS0 hsrc _ ih => exact .varMov d hw hns b _ hdst hopn hS0 hsrc ih
  | var64Mov d hns b bs hdst hbop hS0 hsrc _ ih => exact .var64Mov d hns b _ hdst hbop hS0 hsrc ih
  | const d c bs hdst hn _ ih => exact .const d c _ hdst hn ih
  | mulhi d m bs hdst hA hB _ ih => exact .mulhi d m _ hdst hA hB ih
  | addCarryLo d c bs hdst hA hB hC _ ih => exact .addCarryLo d c _ hdst hA hB hC ih
  | addCarryHi d c bs hdst hA hB hC _ ih => exact .addCarryHi d c _ hdst hA hB hC ih
  | select d c bs hdst hCond hA hB _ ih => exact .select d c _ hdst hCond hA hB ih

/-! ## 8. The head shapes -/

/-- The `bindingHeads` head of a `shlImm w n` binding at depth `curDepth` is
    `SHL:n[:64] regName curDepth, a0`. -/
theorem bindingHeads_shlImm_eq {Γ : Ctxt jasminDialect} {s : JasminTy}
    (nArgs w n : Nat)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
    (a0 : Ctxt.Var Γ (JasminTy.reg w))
    (body : Com jasminDialect (JasminTy.reg w :: Γ) s) (curDepth : Nat) :
    bindingHeads nArgs argName (fun _ => none)
      (.var ⟨JasminOp.shlImm w n, heq, .cons a0 .nil⟩ body) curDepth
      = (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w ("SHL:" ++ toString n))
          [.reg (resolveVarName curDepth nArgs a0)]⟩ : Linstr)
        :: bindingHeads nArgs argName (fun _ => none) body (curDepth + 1) := by
  show (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w ("SHL:" ++ toString n))
      [resolveVar curDepth nArgs argName (fun _ => none) a0]⟩ : Linstr) :: _ = _
  rw [resolveVar_eq_reg]

/-- The `bindingHeads` head of a `shrImm w n` binding at depth `curDepth` is
    `SHR:n[:64] regName curDepth, a0`. -/
theorem bindingHeads_shrImm_eq {Γ : Ctxt jasminDialect} {s : JasminTy}
    (nArgs w n : Nat)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
    (a0 : Ctxt.Var Γ (JasminTy.reg w))
    (body : Com jasminDialect (JasminTy.reg w :: Γ) s) (curDepth : Nat) :
    bindingHeads nArgs argName (fun _ => none)
      (.var ⟨JasminOp.shrImm w n, heq, .cons a0 .nil⟩ body) curDepth
      = (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w ("SHR:" ++ toString n))
          [.reg (resolveVarName curDepth nArgs a0)]⟩ : Linstr)
        :: bindingHeads nArgs argName (fun _ => none) body (curDepth + 1) := by
  show (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w ("SHR:" ++ toString n))
      [resolveVar curDepth nArgs argName (fun _ => none) a0]⟩ : Linstr) :: _ = _
  rw [resolveVar_eq_reg]

/-- The `bindingHeads` head of a `sarImm w n` binding at depth `curDepth` is
    `SAR:n[:64] regName curDepth, a0`. -/
theorem bindingHeads_sarImm_eq {Γ : Ctxt jasminDialect} {s : JasminTy}
    (nArgs w n : Nat)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
    (a0 : Ctxt.Var Γ (JasminTy.reg w))
    (body : Com jasminDialect (JasminTy.reg w :: Γ) s) (curDepth : Nat) :
    bindingHeads nArgs argName (fun _ => none)
      (.var ⟨JasminOp.sarImm w n, heq, .cons a0 .nil⟩ body) curDepth
      = (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w ("SAR:" ++ toString n))
          [.reg (resolveVarName curDepth nArgs a0)]⟩ : Linstr)
        :: bindingHeads nArgs argName (fun _ => none) body (curDepth + 1) := by
  show (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w ("SAR:" ++ toString n))
      [resolveVar curDepth nArgs argName (fun _ => none) a0]⟩ : Linstr) :: _ = _
  rw [resolveVar_eq_reg]

/-- The `bindingHeads` head of a `rorImm w n` binding at depth `curDepth` is
    `ROR:n[:64] regName curDepth, a0`. -/
theorem bindingHeads_rorImm_eq {Γ : Ctxt jasminDialect} {s : JasminTy}
    (nArgs w n : Nat)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.rorImm w n) = .reg w)
    (a0 : Ctxt.Var Γ (JasminTy.reg w))
    (body : Com jasminDialect (JasminTy.reg w :: Γ) s) (curDepth : Nat) :
    bindingHeads nArgs argName (fun _ => none)
      (.var ⟨JasminOp.rorImm w n, heq, .cons a0 .nil⟩ body) curDepth
      = (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w ("ROR:" ++ toString n))
          [.reg (resolveVarName curDepth nArgs a0)]⟩ : Linstr)
        :: bindingHeads nArgs argName (fun _ => none) body (curDepth + 1) := by
  show (⟨0, .Lopn [.reg (regName curDepth)] (withWidthTag w ("ROR:" ++ toString n))
      [resolveVar curDepth nArgs argName (fun _ => none) a0]⟩ : Linstr) :: _ = _
  rw [resolveVar_eq_reg]

/-- The cover layer of a shift or rotate head whose binding names the head's
    destination, source and mnemonic. -/
theorem unaryImmHead_cover {w : Nat} (body : Lcmd) (tbl : Array Nat) (nArgs d : Nat)
    {m : String} (hm : ShiftBase m) (wOp n : Nat) (hn : n ≠ 64)
    {Γ : Ctxt jasminDialect} {τ : JasminTy} (a0 : Ctxt.Var Γ τ)
    (u : UnaryImmBinding w body tbl)
    (hdst : u.nDst = regName d)
    (hsrc : u.nSrc = resolveVarName d nArgs a0)
    (hopn : u.opn = withWidthTag wOp (m ++ ":" ++ toString n)) :
    (physBodyElem body tbl ⟨0, .Lopn [.reg (regName d)] (withWidthTag wOp (m ++ ":" ++ toString n))
        [.reg (resolveVarName d nArgs a0)]⟩).map (·.li_i)
      = (ShiftBinding.unaryImm u).block := by
  rw [ShiftBinding.block, UnaryImmBinding.block, ← hdst, ← hsrc, ← hopn]
  exact physBodyElem_unaryImm body tbl 0 u.nDst u.nSrc u.opn
    (by rw [hopn]; exact isNativeShiftRotate_countTag hm wOp hn) u.hnsp

/-- The threaded cover data yields a cover of the head list `bindingHeads … com d`. -/
theorem coverDataShift_bodyCover {w : Nat} (body : Lcmd) (tbl : Array Nat) (nArgs : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (d : Nat) (bs : List (ShiftBinding w body tbl))
    (hcd : CoverDataShift body tbl nArgs com d bs) :
    BodyCoverShift body tbl (bindingHeads nArgs argName (fun _ => none) com d) bs := by
  induction hcd with
  | ret v d => exact .nil
  | var d hw hns b bs hdst hopn hsrc hcol _ ih =>
      rw [bindingHeads_var_eq]
      exact .cons (physBodyElem_of_realizes body tbl _ b
        (regArithHead_realizes body tbl nArgs d _ w hw hns _ _ b hdst hopn hsrc hcol)) ih
  | var64 d hns b bs hdst hbop hsrc hcol _ ih =>
      rw [bindingHeads_var_eq]
      exact .cons (ToLprogFaithfulBinopWide.regArithHead64_cover body tbl nArgs d _ hns _ _ b
        hdst hbop hsrc hcol) ih
  | varMov d hw hns b bs hdst hopn hS0 hsrc _ ih =>
      rw [bindingHeads_var_eq]
      exact .cons (ToLprogFaithfulBinopMov.regArithHeadMov_cover body tbl nArgs d _ w hw hns _ _ b
        hdst hopn hS0 hsrc) ih
  | var64Mov d hns b bs hdst hbop hS0 hsrc _ ih =>
      rw [bindingHeads_var_eq]
      exact .cons (ToLprogFaithfulBinopMov.regArithHeadMov64_cover body tbl nArgs d _ hns _ _ b
        hdst hbop hS0 hsrc) ih
  | const d c bs hdst hn _ ih =>
      rw [bindingHeads_const_eq]
      refine .cons ?_ ih
      rw [physBodyElem_regConst, ShiftBinding.block, MulCarryBinding.block,
        ArithConstBinding.block, ConstBinding.block, hdst, hn]
  | mulhi d m bs hdst hA hB _ ih =>
      rw [bindingHeads_mulhi_eq]
      refine .cons ?_ ih
      rw [physBodyElem_mulhi, ShiftBinding.block, MulCarryBinding.block, MulHiBinding.block,
        hdst, hA, hB]
  | addCarryLo d c bs hdst hA hB hC _ ih =>
      rw [bindingHeads_addCarryLo_eq]
      refine .cons ?_ ih
      rw [physBodyElem_src3 body tbl 0 _ _ _ _ _ (not_isBinop_ADCX _),
        ShiftBinding.block, MulCarryBinding.block, AddCarryLoBinding.block, hdst, hA, hB, hC]
  | addCarryHi d c bs hdst hA hB hC _ ih =>
      rw [bindingHeads_addCarryHi_eq]
      refine .cons ?_ ih
      rw [physBodyElem_src3 body tbl 0 _ _ _ _ _ (not_isBinop_ADCXHI _),
        ShiftBinding.block, MulCarryBinding.block, AddCarryHiBinding.block, hdst, hA, hB, hC]
  | select d c bs hdst hCond hA hB _ ih =>
      rw [bindingHeads_select_eq]
      refine .cons ?_ ih
      rw [physBodyElem_src3 body tbl 0 _ _ _ _ _ (not_isBinop_CMOV _),
        ShiftBinding.block, MulCarryBinding.block, SelectBinding.block, hdst, hCond, hA, hB]
  | shlImm d hn u bs hdst hsrc hopn _ _ ih =>
      rw [bindingHeads_shlImm_eq]
      exact .cons (unaryImmHead_cover body tbl nArgs d (Or.inl rfl) w _ hn _ u hdst hsrc hopn) ih
  | shrImm d hn u bs hdst hsrc hopn _ _ ih =>
      rw [bindingHeads_shrImm_eq]
      exact .cons (unaryImmHead_cover body tbl nArgs d (Or.inr (Or.inl rfl)) w _ hn _ u
        hdst hsrc hopn) ih
  | sarImm d hn u bs hdst hsrc hopn _ _ ih =>
      rw [bindingHeads_sarImm_eq]
      exact .cons (unaryImmHead_cover body tbl nArgs d (Or.inr (Or.inr (Or.inl rfl))) w _ hn _ u
        hdst hsrc hopn) ih
  | rorImm d hn u bs hdst hsrc hopn _ _ ih =>
      rw [bindingHeads_rorImm_eq]
      exact .cons (unaryImmHead_cover body tbl nArgs d (Or.inr (Or.inr (Or.inr rfl))) w _ hn _ u
        hdst hsrc hopn) ih

/-- **Physical body faithfulness, shift fragment.** For a body that is the head
    list `bindingHeads … com d` of a `Com` with threaded `CoverDataShift`, running
    the literal `physBody (fun _ => none) body` from a `StoreRel`-related start
    reads the composed virtual store at the physical result register. -/
theorem physBody_lsem_result_uniformShift {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (ShiftBinding w body (bodyPhysTable body)))
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverDataShift body (bodyPhysTable body) nArgs com d bs)
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (s s' : Lstate w)
    (hrel : StoreRel body (bodyPhysTable body) L s s')
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ s'', lsemStraight ((physBody (fun _ => none) body).map (·.li_i)) s' = some s''
      ∧ s''.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  have hcov0 := coverDataShift_bodyCover body (bodyPhysTable body) nArgs com d bs hcd
  have hcov : BodyCoverShift body (bodyPhysTable body) body bs := hbody ▸ hcov0
  exact physBody_lsem_resultShift body bs hcov L N hch s s' hrel nRes hnRes

/-! ## 9. The assembled whole-function theorems -/

/-- The straight-line core: `prologue ++ argMatSeq pairs ++ physBody` runs under
    `lsemStraight` from the entry state to a state whose physical result register
    reads the composed virtual store, and the list is `Lret`-free. -/
theorem prologue_argMat_body_lsemStraightShift {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (ShiftBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverDataShift body (bodyPhysTable body) nArgs com d bs)
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (sEntry s : Lstate w)
    (hdisjFrame : PrologueFrameDisjoint body (bodyPhysTable body) L)
    (hoff : StoreRelOff body (bodyPhysTable body) L (pairs.map Prod.fst) s sEntry)
    (habi : ArgMatAbi body (bodyPhysTable body) L pairs s (prologueState sEntry))
    (nRes : String) (hnRes : nRes ∈ N) :
    .Lret ∉ ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
        ++ (physBody (fun _ => none) body).map (·.li_i))
    ∧ ∃ sEnd,
      lsemStraight
        ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
          ++ (physBody (fun _ => none) body).map (·.li_i)) sEntry
        = some sEnd
      ∧ sEnd.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  have hoffP :=
    buildPrologue_preserves_StoreRelOff body (bodyPhysTable body) L _ s sEntry
      hdisjFrame hoff
  obtain ⟨sMat, hrunMat, _⟩ := argMatSeq_reads pairs hfresh hdist (prologueState sEntry)
  have hrelMat : StoreRel body (bodyPhysTable body) L s sMat :=
    argMatSeq_establishes_StoreRel body (bodyPhysTable body) L pairs hfresh hdist s _ sMat
      hoffP habi hrunMat
  obtain ⟨sB, hrunBody, hread⟩ :=
    physBody_lsem_result_uniformShift body nArgs d com bs hbody hcd L N hch s sMat
      hrelMat nRes hnRes
  refine ⟨?_, sB, ?_, hread⟩
  · intro hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · rcases List.mem_append.mp hmem with hmem | hmem
      · exact Lret_not_mem_of_lsemStraight_some _ _ _
          (buildPrologue_lsem virt tbl0 inLoadMap sEntry) hmem
      · exact Lret_not_mem_of_lsemStraight_some _ _ _ hrunMat hmem
    · exact Lret_not_mem_of_lsemStraight_some _ _ _ hrunBody hmem
  · rw [lsemStraight_append, lsemStraight_append, buildPrologue_lsem, Option.bind_some,
      hrunMat, Option.bind_some, hrunBody]

/-- **Whole-function register-allocation faithfulness, shift fragment.** For a
    `Com` of the `UniformRegArithMCS` bindings together with `shlImm`, `shrImm`,
    `sarImm` and `rorImm` bindings whose head list is `body`, with the threaded
    `CoverDataShift`, running `buildPrologue ++ argMatSeq pairs ++ physBody ++
    Lret :: rest` under `lsemRun` from an entry state related to the virtual store
    off the materialization destinations (`hoff`), whose renaming avoids the
    prologue cells (`hdisjFrame`) and whose materialization sources carry the
    argument values (`habi`), reaches a state whose physical result register reads
    the composed virtual store. -/
theorem toLprogPhysAbi_faithful_uniformShift {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (ShiftBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (rest : List LinstrR) (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverDataShift body (bodyPhysTable body) nArgs com d bs)
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (sEntry s : Lstate w)
    (hdisjFrame : PrologueFrameDisjoint body (bodyPhysTable body) L)
    (hoff : StoreRelOff body (bodyPhysTable body) L (pairs.map Prod.fst) s sEntry)
    (habi : ArgMatAbi body (bodyPhysTable body) L pairs s (prologueState sEntry))
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ sEnd,
      lsemRun
        ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
          ++ (physBody (fun _ => none) body).map (·.li_i) ++ .Lret :: rest) sEntry
        = some sEnd
      ∧ sEnd.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  obtain ⟨hnoLret, sEnd, hrun, hread⟩ :=
    prologue_argMat_body_lsemStraightShift body nArgs d com bs virt tbl0 inLoadMap pairs
      hfresh hdist hbody hcd L N hch sEntry s hdisjFrame hoff habi nRes hnRes
  rw [lsemRun_body_ret _ _ _ hnoLret]
  exact ⟨sEnd, hrun, hread⟩

/-- **Whole-function faithfulness at the two-pointer ABI, shift fragment.** The
    instance of `toLprogPhysAbi_faithful_uniformShift` at `twoPtrPairs`: `RDI`
    holds the virtual value of every name renamed onto `argName 0`'s register,
    and `RSI` that of every name renamed onto `argName 1`'s register. -/
theorem toLprogPhysAbi_faithful_uniformShift_twoPtr {w : Nat} (body : Lcmd) (nArgs d : Nat)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (ShiftBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (rest : List LinstrR)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverDataShift body (bodyPhysTable body) nArgs com d bs)
    (hmemref : MemrefPtrsDistinct body (bodyPhysTable body))
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (sEntry s : Lstate w)
    (hdisjFrame : PrologueFrameDisjoint body (bodyPhysTable body) L)
    (hm0 : argName 0 ∈ L) (hm1 : argName 1 ∈ L)
    (hoff : StoreRelOff body (bodyPhysTable body) L
      [physRename body (bodyPhysTable body) (argName 0),
       physRename body (bodyPhysTable body) (argName 1)] s sEntry)
    (hRdi : ∀ m ∈ L, physRename body (bodyPhysTable body) m
      = physRename body (bodyPhysTable body) (argName 0) → sEntry.lvm "RDI" = s.lvm m)
    (hRsi : ∀ m ∈ L, physRename body (bodyPhysTable body) m
      = physRename body (bodyPhysTable body) (argName 1) → sEntry.lvm "RSI" = s.lvm m)
    (nRes : String) (hnRes : nRes ∈ N) :
    ∃ sEnd,
      lsemRun
        ((buildPrologue virt tbl0 inLoadMap).map (·.li_i)
          ++ argMatSeq (twoPtrPairs body (bodyPhysTable body))
          ++ (physBody (fun _ => none) body).map (·.li_i) ++ .Lret :: rest) sEntry
        = some sEnd
      ∧ sEnd.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  refine toLprogPhysAbi_faithful_uniformShift body nArgs d com bs virt tbl0 inLoadMap rest _
    (twoPtrPairs_sourcesFresh _ _ L hdisjFrame hm0 hm1)
    (twoPtrPairs_destsDistinct _ _ hmemref)
    hbody hcd L N hch sEntry s hdisjFrame hoff ?_ nRes hnRes
  intro p hp m hmL hpm
  simp only [twoPtrPairs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · dsimp only
    rw [prologueState_lvm_abiSaveRdi]
    exact hRdi m hmL hpm
  · dsimp only
    rw [prologueState_lvm_abiSaveRsi]
    exact hRsi m hmL hpm

/-- **Whole-function faithfulness with the callee-save restore epilogue, shift
    fragment.** The function body `buildPrologue ++ argMatSeq pairs ++ physBody ++
    calleeSaveRestoreEpilogue ++ Lret :: rest` run under `lsemRun`; the physical
    result register is read after the restore, so it is not one of the six
    callee-saved registers (`hResFree`). -/
theorem toLprogPhysAbi_faithful_uniformShift_epilogue {w : Nat} (body : Lcmd)
    (nArgs d : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
    (bs : List (ShiftBinding w body (bodyPhysTable body)))
    (virt : Lfundef) (tbl0 : Array Nat) (inLoadMap : InLoadMap)
    (rest : List LinstrR) (pairs : List (String × String))
    (hfresh : SourcesFresh pairs) (hdist : DestsDistinct pairs)
    (hbody : body = bindingHeads nArgs argName (fun _ => none) com d)
    (hcd : CoverDataShift body (bodyPhysTable body) nArgs com d bs)
    (L N : List String)
    (hch : Chained (bs.map (fun b => (b.Lin, b.Lout))) L N)
    (sEntry s : Lstate w)
    (hdisjFrame : PrologueFrameDisjoint body (bodyPhysTable body) L)
    (hoff : StoreRelOff body (bodyPhysTable body) L (pairs.map Prod.fst) s sEntry)
    (habi : ArgMatAbi body (bodyPhysTable body) L pairs s (prologueState sEntry))
    (nRes : String) (hnRes : nRes ∈ N)
    (hResFree : physRename body (bodyPhysTable body) nRes ∉ epilogueWritten) :
    ∃ sEnd,
      lsemRun
        ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
          ++ (physBody (fun _ => none) body).map (·.li_i)
          ++ calleeSaveRestoreEpilogue.map (·.li_i) ++ .Lret :: rest) sEntry
        = some sEnd
      ∧ sEnd.lvm (physRename body (bodyPhysTable body) nRes)
          = (composeVSteps (bs.map (fun b => (b.block, b.vstep))) s).lvm nRes := by
  obtain ⟨hnoLret, sB, hrun, hread⟩ :=
    prologue_argMat_body_lsemStraightShift body nArgs d com bs virt tbl0 inLoadMap pairs
      hfresh hdist hbody hcd L N hch sEntry s hdisjFrame hoff habi nRes hnRes
  have hnoLretEpi : .Lret ∉ calleeSaveRestoreEpilogue.map (·.li_i) :=
    Lret_not_mem_of_lsemStraight_some _ _ _ (calleeSaveRestoreEpilogue_lsem sB)
  have hnoLret' : .Lret ∉
      ((buildPrologue virt tbl0 inLoadMap).map (·.li_i) ++ argMatSeq pairs
        ++ (physBody (fun _ => none) body).map (·.li_i)
        ++ calleeSaveRestoreEpilogue.map (·.li_i)) := by
    intro hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hnoLret hmem
    · exact hnoLretEpi hmem
  rw [lsemRun_body_ret _ _ _ hnoLret', lsemStraight_append, hrun, Option.bind_some,
    calleeSaveRestoreEpilogue_lsem]
  exact ⟨epilogueState sB, rfl,
    by rw [calleeSaveRestoreEpilogue_frame sB _ hResFree]; exact hread⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulShift
