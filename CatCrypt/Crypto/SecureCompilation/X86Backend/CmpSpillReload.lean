/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.Proofs
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi

@[expose] public section

set_option autoImplicit false

/-!
# Reload of a spilled first operand of a compare

The loop exporter prints the guards of a counted loop as `CMP ctr, 0` and its invariant touch
as `CMP ctr, r`, and the spill step of the allocator (`legalizeSpillDst`) keeps a compare
whose counter is in a spill slot as one instruction. The checked encoder
`LprogBytes.encodeLfundefBytesChecked` has no form for a compare whose first operand is a
spill slot. The pass `cmpReload` of this module rewrites such a compare into a copy of the
slot to the reload scratch `reloadScratch` followed by the compare on the scratch, which
sets the same flags; the second operand, an immediate, a register or a spill slot, is kept.

On the flag machine `lsemFuelMemF` the pass is an instruction expansion in the sense of
`JasminLsemExportLower.lsemFuelMemF_expand`. The semantic theorem `cmpReload_lsemFuelMemF`
covers a body in which no instruction names the scratch (`cmpReloadOK`); the final states
agree outside the scratch (`JasminLsemFuseMulHi.Agree`). A body in which another
instruction uses the scratch is outside the theorem.

## Main definitions

* `spillCmp?`: the mnemonic, the slot and the second operand of a compare whose first
  operand is a spill slot.
* `cmpReloadI`, `cmpReload`: the rewrite of an instruction and of a body.
* `cmpReloadRM`: the rewrite of a typed instruction, the expansion of the simulation.
* `cmpReloadOK`: the decidable side conditions of the semantic theorem.
* `KeptS`, `AgreeS`: the names other than the scratches `R15` and `R14`, and the agreement
  of two bases on them.

## Main results

* `cmpReload_of_forall`: the pass is the identity on a body without such a compare.
* `spillCmp?_of_mem_cmpReload`, `cmpReload_idem`: the result has no such compare, and the
  pass is idempotent.
* `typeBody_cmpReload`: the typed body of the result is the expansion of the typed body.
* `fstepF_cmpReload`: the copy and the compare on the scratch reach the state of the
  compare on the slot, outside the scratch, with the same zero flag.
* `cmpReload_lsemFuelMemF`: a halting run of a body that passes `cmpReloadOK` is matched
  by a halting run of the rewritten body with at most twice the fuel.
* `fstepF_copySpill`, `fstepF_cmovCondSpill`, `fstepF_cmovDstSpill`,
  `fstepF_cmovCondDstSpill`, `fstepF_setccSpill`: the spill expansions of the allocation
  path (`legalizeOneSrc`, `cmovSpillSeq`, `setccSpill?`) reach the state of the source
  instruction outside `R15` and `R14`, with the same zero flag.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (x86Abi)

/-- **A compare whose first operand is a spill slot**: for `Lopn [d] opn [d, s]` with
    mnemonic base `CMP`, `d` a spill slot and `s` other than the reload scratch, the
    mnemonic, the slot name and the second operand; `none` for every other instruction. -/
def spillCmp? (w : LinstrR) (abi : IsaAbi := x86Abi) : Option (String × String × LOperand) :=
  match w with
  | .Lopn [.reg d] opn [.reg a, s] =>
      if stripWidthTag opn == "CMP" && d == a && (LOperand.reg d).isSpill
          && s != .reg abi.reload then some (opn, d, s)
      else none
  | _ => none

/-- The copy mnemonic at the width of the compare `opn`. -/
def movOf (opn : String) : String := if hasSuffix opn ":64" then "MOV:64" else "MOV"

/-- **The rewrite of an instruction**: a compare on a spilled first operand becomes the copy
    of the slot to the reload scratch and the compare on the scratch; every other
    instruction is kept. -/
def cmpReloadI (i : Linstr) (abi : IsaAbi := x86Abi) : Lcmd :=
  match spillCmp? i.li_i abi with
  | some (opn, d, s) =>
      [⟨i.li_ii, .Lopn [.reg abi.reload] (movOf opn) [.reg d]⟩,
       ⟨i.li_ii, .Lopn [.reg abi.reload] opn [.reg abi.reload, s]⟩]
  | none => [i]

/-- **The reload of spilled compare operands** on a body. -/
def cmpReload (body : Lcmd) (abi : IsaAbi := x86Abi) : Lcmd :=
  body.flatMap fun i => cmpReloadI i abi

theorem cmpReload_nil : cmpReload [] = [] := rfl

theorem cmpReload_append (a b : Lcmd) : cmpReload (a ++ b) = cmpReload a ++ cmpReload b :=
  List.flatMap_append

/-- An instruction that is no compare on a spilled first operand is kept. -/
theorem cmpReloadI_of_none {i : Linstr} (h : spillCmp? i.li_i = none) : cmpReloadI i = [i] := by
  simp [cmpReloadI, h]

/-- **The pass is the identity on a body without a compare on a spilled first operand.** -/
theorem cmpReload_of_forall {body : Lcmd} (h : ∀ i ∈ body, spillCmp? i.li_i = none) :
    cmpReload body = body := by
  induction body with
  | nil => rfl
  | cons i rest ih =>
      have hi := cmpReloadI_of_none (h i List.mem_cons_self)
      have hr := ih fun j hj => h j (List.mem_cons_of_mem _ hj)
      simp only [cmpReload] at hr ⊢
      rw [List.flatMap_cons, hi, hr]
      rfl

/-- A copy at the mnemonic `movOf opn` is no compare on a spilled first operand. -/
theorem spillCmp?_mov (opn : String) (d s : LOperand) :
    spillCmp? (.Lopn [d] (movOf opn) [s]) = none := by
  simp [spillCmp?]

/-- A compare on the reload scratch is no compare on a spilled first operand. -/
theorem spillCmp?_scratch (opn : String) (s : LOperand) :
    spillCmp? (.Lopn [.reg reloadScratch] opn [.reg reloadScratch, s]) = none := by
  simp [spillCmp?, reloadScratch_not_spill]

/-- No instruction of a rewritten instruction is a compare on a spilled first operand. -/
theorem spillCmp?_of_mem_cmpReloadI {i j : Linstr} (hj : j ∈ cmpReloadI i) :
    spillCmp? j.li_i = none := by
  unfold cmpReloadI at hj
  split at hj
  · rename_i opn d s _
    rcases List.mem_cons.mp hj with rfl | hj
    · exact spillCmp?_mov opn _ _
    · rcases List.mem_singleton.mp hj with rfl
      exact spillCmp?_scratch opn s
  · rename_i hn
    rcases List.mem_singleton.mp hj with rfl
    exact hn

/-- **The result of the pass has no compare on a spilled first operand.** -/
theorem spillCmp?_of_mem_cmpReload {body : Lcmd} {j : Linstr} (hj : j ∈ cmpReload body) :
    spillCmp? j.li_i = none := by
  obtain ⟨i, -, hji⟩ := List.mem_flatMap.mp hj
  exact spillCmp?_of_mem_cmpReloadI hji

/-- The pass is idempotent. -/
theorem cmpReload_idem (body : Lcmd) : cmpReload (cmpReload body) = cmpReload body :=
  cmpReload_of_forall fun _ hj => spillCmp?_of_mem_cmpReload hj

/-! ## The pass on the flag machine -/

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi (Agree KeptN fstepF_agree clsB
  clsB_spec)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames mulxFree)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV (typeBody)

/-- The rewrite of a typed instruction: `cmpReloadI` on its wire, typed with `tag`. -/
def cmpReloadRM (tag : LinstrR → MemTag) (i : LinstrRM) (abi : IsaAbi := x86Abi) :
    List LinstrRM :=
  typeBody tag (cmpReloadI ⟨0, i.1⟩ abi)

theorem typeBody_cmpReloadI (tag : LinstrR → MemTag) (i : Linstr) :
    typeBody tag (cmpReloadI i) = cmpReloadRM tag (i.li_i, tag i.li_i) := by
  unfold cmpReloadRM cmpReloadI
  simp only
  split <;> rfl

/-- **The pass is an instruction expansion**: the typed body of `cmpReload body` is the
    typed body of `body` expanded by `cmpReloadRM`. -/
theorem typeBody_cmpReload (tag : LinstrR → MemTag) (body : Lcmd) :
    typeBody tag (cmpReload body) = (typeBody tag body).flatMap (cmpReloadRM tag) := by
  induction body with
  | nil => rfl
  | cons i rest ih =>
      have h : typeBody tag (cmpReload (i :: rest))
          = typeBody tag (cmpReloadI i) ++ typeBody tag (cmpReload rest) := by
        simp [cmpReload, typeBody]
      rw [h, ih, typeBody_cmpReloadI]
      rfl

/-- The wire of a compare on a spilled first operand. -/
theorem spillCmp?_eq_some {w : LinstrR} {opn d : String} {s : LOperand}
    (h : spillCmp? w = some (opn, d, s)) :
    w = .Lopn [.reg d] opn [.reg d, s] ∧ stripWidthTag opn = "CMP" := by
  unfold spillCmp? at h
  split at h
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨⟨⟨h1, rfl⟩, -⟩, -⟩ := hc
      exact ⟨rfl, h1⟩
    · cases h
  · cases h

/-- The copy mnemonic of the flag compare strips to `"MOV"`. -/
theorem movOf_cmp64 : stripWidthTag (movOf (withWidthTag 64 "CMP")) = "MOV" := by decide

/-- **The rewritten flag compare.** When the flag compare `CMP d, s` steps from a base, the
    pair `MOV R15, d ; CMP R15, s` runs from every base that agrees with it outside `R15`
    to a base that agrees with the result outside `R15`, with the same zero flag, provided
    neither `d` nor `s` names `R15`. The compare writes the zero flag only. -/
theorem fstepF_cmpReload (d : String) (s : LOperand) (tg t1 t2 : MemTag)
    (hd : KeptN d) (hs : ∀ n ∈ opNames s, KeptN n) {a a' t : LstateM} {zf zt : Bool}
    (hA : Agree a a')
    (h : fstepF (.Lopn [.reg d] (withWidthTag 64 "CMP") [.reg d, s], tg) a zf = some (t, zt)) :
    ∃ t', runStraightF
        [(.Lopn [.reg reloadScratch] (movOf (withWidthTag 64 "CMP")) [.reg d], t1),
         (.Lopn [.reg reloadScratch] (withWidthTag 64 "CMP") [.reg reloadScratch, s], t2)] a' zf
        = some (t', zt) ∧ Agree t t' := by
  have hc : ∀ (x : String) (tg : MemTag),
      cmpArgs? (.Lopn [.reg x] (withWidthTag 64 "CMP") [.reg x, s], tg) = some (.reg x, s) := by
    intro x tg; simp [cmpArgs?]
  have hmv := fstepF_movWire reloadScratch d _ t1 movOf_cmp64 a' zf
  unfold movWire at hmv
  have e1 : evalOperandN ((a'.setReg reloadScratch (a'.reg.lvm d).2).nextPc).reg 64
      (.reg reloadScratch) = evalOperandN a.reg 64 (.reg d) := by
    have hd' : ((a'.reg.setReg reloadScratch (a'.reg.lvm d).2).nextPc).lvm reloadScratch
        = a.reg.lvm d := by
      rw [← hA.reg d hd]; simp [LstateN.nextPc, LstateN.lvm_setReg]
    simp only [evalOperandN, LstateM.reg_nextPc, LstateM.reg_setReg]
    unfold LstateN.getW
    rw [hd']
  have e2 : evalOperandN ((a'.setReg reloadScratch (a'.reg.lvm d).2).nextPc).reg 64 s
      = evalOperandN a.reg 64 s := by
    cases s with
    | reg b =>
        have hb : b ≠ reloadScratch := hs b (by simp [opNames])
        simp only [evalOperandN, LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc,
          LstateN.getW_setReg_other _ _ _ _ _ hb]
        unfold LstateN.getW
        rw [hA.reg b hb]
    | _ => rfl
  unfold fstepF at h
  rw [hc] at h
  simp only at h
  rw [runStraightF_cons, hmv, Option.bind_some, runStraightF_cons]
  unfold fstepF
  rw [hc]
  simp only [e1, e2]
  cases ha : evalOperandN a.reg 64 (.reg d) with
  | none => rw [ha] at h; simp at h
  | some va =>
      cases hb : evalOperandN a.reg 64 s with
      | none => rw [ha, hb] at h; simp at h
      | some vb =>
          rw [ha, hb] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨_, rfl, ⟨fun r hr => ?_, fun r hr => hA.arr r hr, hA.mem, hA.cf, hA.of⟩⟩
          have hr' : r ≠ reloadScratch := hr
          simp [LstateM.setReg, LstateM.nextPc, LstateN.nextPc, LstateN.lvm_setReg, hr',
            hA.reg r hr]

/-- The side conditions of the pass on one wire typed with `tag`: the instruction is an
    `Lopn`, a label, a zero-flag conditional or a goto; it does not name the reload
    scratch; it is not a `MULX`; and a compare on a spilled first operand carries the
    mnemonic of the flag compare. -/
def cmpReloadOKI (tag : LinstrR → MemTag) (w : LinstrR) (abi : IsaAbi := x86Abi) : Bool :=
  let r := abi.reload
  clsB (w, tag w) && (instrNames w).all (fun n => n != r) && mulxFree (w, tag w)
    && (match spillCmp? w abi with
        | some (opn, _, _) => opn == withWidthTag 64 "CMP"
        | none => true)

/-- **The side conditions of the pass** on a body typed with `tag`: `cmpReloadOKI` at
    every instruction. -/
def cmpReloadOK (tag : LinstrR → MemTag) (body : Lcmd) (abi : IsaAbi := x86Abi) : Bool :=
  body.all fun i => cmpReloadOKI tag i.li_i abi

/-- **The per-instruction condition of the pass**, at the agreement outside `R15`. -/
theorem instrOK_cmpReload {tag : LinstrR → MemTag} {w : LinstrR}
    (h : cmpReloadOKI tag w = true) : InstrOK Agree (cmpReloadRM tag) (w, tag w) := by
  simp only [cmpReloadOKI, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨hcls, hn⟩, hm⟩, hw⟩ := h
  have hkept : ∀ n ∈ instrNames w, KeptN n := hn
  cases hsp : spillCmp? w with
  | none =>
      have hself : cmpReloadRM tag (w, tag w) = [(w, tag w)] := by
        simp [cmpReloadRM, cmpReloadI, hsp, typeBody]
      rcases clsB_spec hcls with hl | hc
      · refine Or.inl ⟨hl, fun j hj => ?_, fun s s' t zf zt hA hst => ?_⟩
        · replace hj : j ∈ cmpReloadRM tag (w, tag w) := hj
          rw [hself] at hj
          obtain rfl : j = (w, tag w) := by simpa using hj
          exact hl
        · show ∃ t', runStraightF (cmpReloadRM tag (w, tag w)) s' zf = some (t', zt) ∧ Agree t t'
          rw [hself]
          obtain ⟨t', h', hA'⟩ := fstepF_agree hl hkept hm hA hst
          exact ⟨t', by rw [runStraightF_cons, h']; rfl, hA'⟩
      · exact Or.inr ⟨hself, hc⟩
  | some p =>
      obtain ⟨opn, d, s⟩ := p
      rw [hsp] at hw
      obtain rfl : opn = withWidthTag 64 "CMP" := by simpa using hw
      obtain ⟨rfl, -⟩ := spillCmp?_eq_some hsp
      have hexp : cmpReloadRM tag
          (.Lopn [.reg d] (withWidthTag 64 "CMP") [.reg d, s],
            tag (.Lopn [.reg d] (withWidthTag 64 "CMP") [.reg d, s]))
          = [(.Lopn [.reg reloadScratch] (movOf (withWidthTag 64 "CMP")) [.reg d],
               tag (.Lopn [.reg reloadScratch] (movOf (withWidthTag 64 "CMP")) [.reg d])),
             (.Lopn [.reg reloadScratch] (withWidthTag 64 "CMP") [.reg reloadScratch, s],
               tag (.Lopn [.reg reloadScratch] (withWidthTag 64 "CMP")
                 [.reg reloadScratch, s]))] := by
        have hr : x86Abi.reload = reloadScratch := rfl
        simp [cmpReloadRM, cmpReloadI, hsp, typeBody, hr]
      refine Or.inl ⟨⟨_, _, _, rfl⟩, fun j hj => ?_, fun a a' t zf zt hA hst => ?_⟩
      · simp only [hexp, List.mem_cons, List.mem_nil_iff, or_false] at hj
        rcases hj with rfl | rfl <;> exact ⟨_, _, _, rfl⟩
      · simp only [hexp]
        exact fstepF_cmpReload d s _ _ _ (hkept d (by simp [instrNames, opNames]))
          (fun n hn' => hkept n (by simp only [instrNames, List.cons_append, List.nil_append,
            List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append]
                                    exact Or.inr (Or.inr hn'))) hA hst

/-- **`cmpReload_lsemFuelMemF`: the reload of spilled compare operands preserves halting
    runs.** For a body that passes `cmpReloadOK tag`, every halting run of the typed body
    from program counter `0` is matched by a halting run of the typed body of
    `cmpReload body` from the same state, with at most twice the fuel; the final states
    agree on every register and array other than `R15`, on the word memory, the carry,
    overflow and zero flags and the function name, and the final program counter is the
    `pcMap` image. -/
theorem cmpReload_lsemFuelMemF {tag : LinstrR → MemTag} {body : Lcmd}
    (h : cmpReloadOK tag body = true) (fn : String) (s t : LstateMF)
    (hpc : s.prog.base.lpc = 0) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn (typeBody tag body)) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel * 2
      ∧ lsemFuelMemF (singletonProgM fn (typeBody tag (cmpReload body))) fuel' s = some t'
      ∧ Agree t.prog.base t'.prog.base ∧ t'.zf = t.zf ∧ t'.prog.lfn = t.prog.lfn
      ∧ t'.prog.base.lpc = pcMap (cmpReloadRM tag) (typeBody tag body) t.prog.base.lpc := by
  have hP : ExpProg Agree (cmpReloadRM tag) (singletonProgM fn (typeBody tag body))
      (singletonProgM fn (typeBody tag (cmpReload body))) := by
    refine ⟨rfl, typeBody_cmpReload tag body, fun k i hk => ?_, fun _ _ p q hA => hA.setLpc p q⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hk)
    exact instrOK_cmpReload (List.all_eq_true.mp h j hj)
  have hlen : ∀ i ∈ (singletonProgM fn (typeBody tag body)).body,
      (cmpReloadRM tag i).length ≤ 2 := by
    intro i _
    unfold cmpReloadRM cmpReloadI typeBody
    simp only
    split <;> simp
  have hR : RelX Agree (cmpReloadRM tag) (singletonProgM fn (typeBody tag body)) s s := by
    refine ⟨rfl, rfl, ?_, Agree.refl _⟩
    rw [hpc]; rfl
  obtain ⟨fuel', t', hf, hrun', hRt⟩ := lsemFuelMemF_expand hP hlen fuel hR hrun
  exact ⟨fuel', t', hf, hrun', hRt.base, hRt.zf, hRt.lfn, hRt.pc⟩

/-! ## The spill expansions of the allocator on the flag machine

The allocation path `physBodyWithStores` routes a copy between two spill slots
(`legalizeOneSrc`), a select whose condition or destination is a spill slot
(`cmovSpillSeq`) and a materialised comparison with a spilled operand (`setccSpill?`)
through the reload scratches `R15` and `R14`. Each expansion run from a base that agrees
with the source base outside the two scratches reaches a base that agrees with the
source instruction's result outside the two scratches, with the same zero flag. -/

/-- The names the spill expansions may change beyond the source: the reload scratches
    `R15` (`reloadScratch`) and `R14` (`reloadScratch2`). -/
def KeptS (r : String) : Prop := r ≠ reloadScratch ∧ r ≠ reloadScratch2

/-- Two bases agree on every register and array name other than `R15` and `R14`, on the
    word memory and on the carry and overflow flags. -/
structure AgreeS (s s' : LstateM) : Prop where
  /-- The registers agree outside the scratches. -/
  reg : ∀ r, KeptS r → s'.reg.lvm r = s.reg.lvm r
  /-- The arrays agree outside the scratches. -/
  arr : ∀ r, KeptS r → s'.larr r = s.larr r
  /-- The word memories agree. -/
  mem : s'.lmem = s.lmem
  /-- The carry flags agree. -/
  cf : s'.cf = s.cf
  /-- The overflow flags agree. -/
  of : s'.of = s.of

theorem AgreeS.refl (s : LstateM) : AgreeS s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

/-- Two agreeing bases that write the same value to the same register and advance agree. -/
theorem AgreeS.setReg {a a' : LstateM} (h : AgreeS a a') (D : String) {w : Nat}
    (v : BitVec w) : AgreeS (a.setReg D v).nextPc (a'.setReg D v).nextPc := by
  refine ⟨fun r hr => ?_, fun r hr => h.arr r hr, h.mem, h.cf, h.of⟩
  by_cases hrD : r = D
  · subst hrD; simp [LstateM.setReg, LstateM.nextPc]
  · simp [LstateM.setReg, LstateM.nextPc, hrD, h.reg r hr]

/-- A write to a scratch on the right keeps the agreement. -/
theorem AgreeS.setScratch {a a' : LstateM} (h : AgreeS a a') {S : String} (hS : ¬ KeptS S)
    {w : Nat} (v : BitVec w) : AgreeS a (a'.setReg S v).nextPc := by
  refine ⟨fun r hr => ?_, fun r hr => h.arr r hr, h.mem, h.cf, h.of⟩
  have hrS : r ≠ S := fun e => hS (e ▸ hr)
  simp [LstateM.setReg, LstateM.nextPc, hrS, h.reg r hr]

/-- A register copy `mov d, s` (a mnemonic stripping to `MOV`, or a `copyQ` mnemonic)
    writes the cell of `s` to `d` and keeps the zero flag. -/
theorem fstepF_copyWire (d s mov : String) (tg : MemTag)
    (hm : stripWidthTag mov = "MOV" ∨ copyQ mov = true) (a : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg d] mov [.reg s], tg) a zf
      = some ((a.setReg d (a.reg.lvm s).2).nextPc, zf) := by
  refine JasminLsemFuseMulHi.fstepF_copy rfl ?_ a zf
  rcases hm with hm | hm
  · simp [movRegArgs?, hm]
  · by_cases h' : stripWidthTag mov = "MOV"
    · simp [movRegArgs?, h']
    · simp only [movRegArgs?]
      rw [ite_eq_right h', ite_eq_left hm]

/-- The cell a register copy writes is the cell of its source. -/
theorem lvm_copy (a : LstateM) (d s : String) :
    ((a.setReg d (a.reg.lvm s).2).nextPc).reg.lvm d = a.reg.lvm s := by
  simp [LstateM.setReg, LstateM.nextPc]

/-- A register copy leaves every other cell. -/
theorem lvm_copy_other (a : LstateM) {d r : String} (s : String) (h : r ≠ d) :
    ((a.setReg d (a.reg.lvm s).2).nextPc).reg.lvm r = a.reg.lvm r := by
  simp [LstateM.setReg, LstateM.nextPc, h]

/-- **The copy between spill slots.** When the copy `mov d, s` steps from a base, the pair
    `mov R15, s ; mov d, R15` runs from every base that agrees with it outside the
    scratches to a base that agrees with the result outside the scratches, with the same
    zero flag, provided `s` is no scratch. -/
theorem fstepF_copySpill (d s mov : String) (tg t1 t2 : MemTag)
    (hm : stripWidthTag mov = "MOV" ∨ copyQ mov = true) (hs : KeptS s)
    {a a' t : LstateM} {zf zt : Bool} (hA : AgreeS a a')
    (h : fstepF (.Lopn [.reg d] mov [.reg s], tg) a zf = some (t, zt)) :
    ∃ t', runStraightF [(.Lopn [.reg reloadScratch] mov [.reg s], t1),
        (.Lopn [.reg d] mov [.reg reloadScratch], t2)] a' zf = some (t', zt)
      ∧ AgreeS t t' := by
  rw [fstepF_copyWire _ _ _ _ hm] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨_, by
    rw [runStraightF_cons, fstepF_copyWire _ _ _ _ hm, Option.bind_some, runStraightF_cons,
      fstepF_copyWire _ _ _ _ hm]; rfl, ?_⟩
  have hR : ((a'.setReg reloadScratch (a'.reg.lvm s).2).nextPc).reg.lvm reloadScratch
      = a.reg.lvm s := by rw [lvm_copy, hA.reg s hs]
  rw [hR]
  exact (hA.setScratch (fun hk => hk.1 rfl) _).setReg d _

/-- The flag machine steps the register-tagged select `CMOV:64 D, [C, T, F]` by the
    width-aware step `lsemStepN` on the register file, keeping the zero flag. -/
theorem fstepF_cmov64_eq (D C T F : String) (cd : Option Nat) (m : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg D] "CMOV:64" [.reg C, .reg T, .reg F], .reg cd) m zf
      = (lsemStepN (.Lopn [.reg D] "CMOV:64" [.reg C, .reg T, .reg F]) m.reg).map
          (fun r => ({ m with reg := r }, zf)) := by
  have hw : (.Lopn [.reg D] "CMOV:64" [.reg C, .reg T, .reg F] : LinstrR)
      = opToLinstrR (JasminDialect.JasminOp.select 64) D [.reg C, .reg T, .reg F] := by
    rw [opToLinstrR]; rfl
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    JasminLsemMulCarry.struct?_select (w := 64) D [.reg C, .reg T, .reg F]
  have h6 := JasminLsemShift.sarStruct?_select (w := 64) D [.reg C, .reg T, .reg F]
  rw [← hw] at h1 h2 h3 h4 h5 h6
  unfold fstepF
  have hc : cmpArgs? (.Lopn [.reg D] "CMOV:64" [.reg C, .reg T, .reg F], .reg cd) = none := rfl
  have hm : movRegArgs? (.Lopn [.reg D] "CMOV:64" [.reg C, .reg T, .reg F], .reg cd) = none :=
    rfl
  simp only [hc, hm]
  rw [stepMemF_of_quiet rfl rfl rfl, lsemStepMem_reg,
    JasminLsemCast.lsemStepCast_of_delegate _ _ (Or.inl ⟨rfl, rfl⟩),
    JasminLsemMulCarry.lsemStepMC_of_delegate _ _ h1 h2 h3 h4 h5,
    JasminLsemShift.lsemStepSh_of_not_sar _ _ h6]
  cases lsemStepN (.Lopn [.reg D] "CMOV:64" [.reg C, .reg T, .reg F]) m.reg <;> rfl

/-- **The select on substituted cells.** When the select `CMOV:64 D, [C, T, F]` steps from
    a base `a`, the select `CMOV:64 D', [C', T', F']` steps from every base `b` whose cells
    at `C'`, `T'`, `F'` are the cells of `a` at `C`, `T`, `F`, writing the same value. -/
theorem fstepF_cmov64_congr {D D' C C' T T' F F' : String} {cd cd' : Option Nat}
    {a b t : LstateM} {zf zt : Bool}
    (hC : b.reg.lvm C' = a.reg.lvm C) (hT : b.reg.lvm T' = a.reg.lvm T)
    (hF : b.reg.lvm F' = a.reg.lvm F)
    (h : fstepF (.Lopn [.reg D] "CMOV:64" [.reg C, .reg T, .reg F], .reg cd) a zf
      = some (t, zt)) :
    zt = zf ∧ ∃ (w : Nat) (v : BitVec w), t = (a.setReg D v).nextPc
      ∧ fstepF (.Lopn [.reg D'] "CMOV:64" [.reg C', .reg T', .reg F'], .reg cd') b zf
          = some ((b.setReg D' v).nextPc, zf) := by
  rw [fstepF_cmov64_eq] at h
  rw [fstepF_cmov64_eq]
  have hs : stripWidthTag "CMOV:64" = "CMOV" := by decide +kernel
  have gC : b.reg.getW C' 1 = a.reg.getW C 1 := by unfold LstateN.getW; rw [hC]
  have gF : ∀ w, b.reg.getW F' w = a.reg.getW F w := fun w => by
    unfold LstateN.getW; rw [hF]
  simp only [lsemStepN, hs, ite_true, operandName, readReg, evalOperandN] at h ⊢
  rw [gC, hT]
  simp only [gF]
  generalize a.reg.lvm T = cT at h ⊢
  obtain ⟨wT, vT⟩ := cT
  cases hc : a.reg.getW C 1 with
  | none => simp [hc] at h
  | some vc =>
      cases hf : a.reg.getW F wT with
      | none => simp [hc, hf] at h
      | some vf =>
          simp only [hc, hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨rfl, _, JasminDialect.selectW vc vT vf, rfl, ?_⟩
          simp only [hf, Option.map_some]
          rfl

theorem reloadScratch_ne_reloadScratch2 : reloadScratch ≠ reloadScratch2 := by decide

theorem not_keptS_reloadScratch : ¬ KeptS reloadScratch := fun h => h.1 rfl

theorem not_keptS_reloadScratch2 : ¬ KeptS reloadScratch2 := fun h => h.2 rfl

theorem stripWidthTag_mov64 : stripWidthTag "MOV:64" = "MOV" := by decide +kernel

/-- The cell a step writes to a register is the written value. -/
theorem lvm_setReg_self (a : LstateM) (D : String) {w : Nat} (v : BitVec w) :
    ((a.setReg D v).nextPc).reg.lvm D = ⟨w, v⟩ := by
  simp [LstateM.setReg, LstateM.nextPc]

/-- **The select on a reloaded condition.** When the select `CMOV:64 D, [C, T, F]` steps
    from a base, the pair `MOV:64 R14, C ; CMOV:64 D, [R14, T, F]` runs from every base that
    agrees with it outside the scratches to a base that agrees with the result outside the
    scratches, with the same zero flag, provided `C`, `T` and `F` are no scratches. -/
theorem fstepF_cmovCondSpill (D C T F : String) (cd cd' : Option Nat) (t1 : MemTag)
    (hC : KeptS C) (hT : KeptS T) (hF : KeptS F) {a a' t : LstateM} {zf zt : Bool}
    (hA : AgreeS a a')
    (h : fstepF (.Lopn [.reg D] "CMOV:64" [.reg C, .reg T, .reg F], .reg cd) a zf
      = some (t, zt)) :
    ∃ t', runStraightF [(.Lopn [.reg reloadScratch2] "MOV:64" [.reg C], t1),
        (.Lopn [.reg D] "CMOV:64" [.reg reloadScratch2, .reg T, .reg F], .reg cd')] a' zf
        = some (t', zt) ∧ AgreeS t t' := by
  have e1 := fstepF_copyWire reloadScratch2 C "MOV:64" t1 (Or.inl stripWidthTag_mov64) a' zf
  have hX := hA.setScratch not_keptS_reloadScratch2 (a'.reg.lvm C).2
  obtain ⟨rfl, w, v, rfl, h2⟩ := fstepF_cmov64_congr (D' := D) (cd' := cd')
    (by rw [lvm_copy, hA.reg C hC]) (hX.reg T hT) (hX.reg F hF) h
  exact ⟨_, by rw [runStraightF_cons, e1, Option.bind_some, runStraightF_cons, h2]; rfl,
    hX.setReg D v⟩

/-- **The select into a spilled destination.** When the select `CMOV:64 D, [C, T, F]` steps
    from a base, the pair `CMOV:64 R15, [C, T, F] ; MOV:64 D, R15` runs from every base that
    agrees with it outside the scratches to a base that agrees with the result outside the
    scratches, with the same zero flag, provided `C`, `T` and `F` are no scratches. -/
theorem fstepF_cmovDstSpill (D C T F : String) (cd cd' : Option Nat) (t2 : MemTag)
    (hC : KeptS C) (hT : KeptS T) (hF : KeptS F) {a a' t : LstateM} {zf zt : Bool}
    (hA : AgreeS a a')
    (h : fstepF (.Lopn [.reg D] "CMOV:64" [.reg C, .reg T, .reg F], .reg cd) a zf
      = some (t, zt)) :
    ∃ t', runStraightF
        [(.Lopn [.reg reloadScratch] "CMOV:64" [.reg C, .reg T, .reg F], .reg cd'),
         (.Lopn [.reg D] "MOV:64" [.reg reloadScratch], t2)] a' zf
        = some (t', zt) ∧ AgreeS t t' := by
  obtain ⟨rfl, w, v, rfl, h2⟩ := fstepF_cmov64_congr (D' := reloadScratch) (cd' := cd')
    (hA.reg C hC) (hA.reg T hT) (hA.reg F hF) h
  have e2 := fstepF_copyWire D reloadScratch "MOV:64" t2 (Or.inl stripWidthTag_mov64)
    (a'.setReg reloadScratch v).nextPc zt
  rw [lvm_setReg_self] at e2
  exact ⟨_, by rw [runStraightF_cons, h2, Option.bind_some, runStraightF_cons, e2]; rfl,
    (hA.setScratch not_keptS_reloadScratch v).setReg D v⟩

/-- **The select on a reloaded condition into a spilled destination.** When the select
    `CMOV:64 D, [C, T, F]` steps from a base, the sequence
    `MOV:64 R14, C ; CMOV:64 R15, [R14, T, F] ; MOV:64 D, R15` runs from every base that
    agrees with it outside the scratches to a base that agrees with the result outside the
    scratches, with the same zero flag, provided `C`, `T` and `F` are no scratches. -/
theorem fstepF_cmovCondDstSpill (D C T F : String) (cd cd' : Option Nat) (t1 t3 : MemTag)
    (hC : KeptS C) (hT : KeptS T) (hF : KeptS F) {a a' t : LstateM} {zf zt : Bool}
    (hA : AgreeS a a')
    (h : fstepF (.Lopn [.reg D] "CMOV:64" [.reg C, .reg T, .reg F], .reg cd) a zf
      = some (t, zt)) :
    ∃ t', runStraightF [(.Lopn [.reg reloadScratch2] "MOV:64" [.reg C], t1),
        (.Lopn [.reg reloadScratch] "CMOV:64" [.reg reloadScratch2, .reg T, .reg F], .reg cd'),
        (.Lopn [.reg D] "MOV:64" [.reg reloadScratch], t3)] a' zf
        = some (t', zt) ∧ AgreeS t t' := by
  have e1 := fstepF_copyWire reloadScratch2 C "MOV:64" t1 (Or.inl stripWidthTag_mov64) a' zf
  have hX := hA.setScratch not_keptS_reloadScratch2 (a'.reg.lvm C).2
  obtain ⟨rfl, w, v, rfl, h2⟩ := fstepF_cmov64_congr (D' := reloadScratch) (cd' := cd')
    (by rw [lvm_copy, hA.reg C hC]) (hX.reg T hT) (hX.reg F hF) h
  have e3 := fstepF_copyWire D reloadScratch "MOV:64" t3 (Or.inl stripWidthTag_mov64)
    (((a'.setReg reloadScratch2 (a'.reg.lvm C).2).nextPc).setReg reloadScratch v).nextPc zt
  rw [lvm_setReg_self] at e3
  exact ⟨_, by
      rw [runStraightF_cons, e1, Option.bind_some, runStraightF_cons, h2, Option.bind_some,
        runStraightF_cons, e3]; rfl,
    (hX.setScratch not_keptS_reloadScratch v).setReg D v⟩

/-- The flag machine steps the register-tagged materialised comparison
    `SET<cc> D, [A, B]` by the width-aware step `lsemStepN` on the register file, keeping
    the zero flag. -/
theorem fstepF_setcc_eq (c : JasminDialect.JasminCmp) (wOp : Nat) (D A B : String)
    (cd : Option Nat) (m : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg D] (withWidthTag wOp (cmpName c)) [.reg A, .reg B], .reg cd) m zf
      = (lsemStepN (.Lopn [.reg D] (withWidthTag wOp (cmpName c)) [.reg A, .reg B]) m.reg).map
          (fun r => ({ m with reg := r }, zf)) := by
  have hs := JasminLsem.stripWidthTag_withWidthTag_cmpName wOp c
  have hne : ∀ m : String, stripWidthTag (withWidthTag 64 m) = m → cmpName c ≠ m →
      withWidthTag wOp (cmpName c) ≠ withWidthTag 64 m :=
    fun m h1 h2 he => h2 (hs.symm.trans (he ▸ h1))
  have hc : cmpArgs? (.Lopn [.reg D] (withWidthTag wOp (cmpName c)) [.reg A, .reg B], .reg cd)
      = none := by
    simp only [cmpArgs?]
    rw [ite_eq_right (hne "CMP" (by decide +kernel) (by cases c <;> decide))]
  have hm : movRegArgs?
      (.Lopn [.reg D] (withWidthTag wOp (cmpName c)) [.reg A, .reg B], .reg cd) = none := rfl
  have hk : carryArgs?
      (.Lopn [.reg D] (withWidthTag wOp (cmpName c)) [.reg A, .reg B], .reg cd) = none := by
    simp only [carryArgs?,
      ite_eq_right (hne "ADC" (by decide +kernel) (by cases c <;> decide)),
      ite_eq_right (hne "SBB" (by decide +kernel) (by cases c <;> decide)),
      ite_eq_right (hne "ADCX" (by decide +kernel) (by cases c <;> decide)),
      ite_eq_right (hne "ADOX" (by decide +kernel) (by cases c <;> decide))]
  have hw : wideArgs?
      (.Lopn [.reg D] (withWidthTag wOp (cmpName c)) [.reg A, .reg B], .reg cd) = none := by
    simp only [wideArgs?, ite_eq_right (hne "MOV" (by decide +kernel) (by cases c <;> decide))]
  unfold fstepF
  simp only [hc, hm]
  rw [stepMemF_of_quiet (aluFlagOp?_cmp c wOp D _ _ _) hk hw, lsemStepMem_reg,
    JasminLsemCast.lsemStepCast_of_delegate _ _
      (Or.inl ⟨rfl, by simp [JasminLsemCast.movImmStruct?]⟩),
    JasminLsemMulCarry.lsemStepMC_of_delegate _ _
      (by simp only [JasminLsemMulCarry.mulhiStruct?, hs]; cases c <;> rfl) rfl rfl rfl rfl,
    JasminLsemShift.lsemStepSh_of_not_sar _ _
      (by simp only [JasminLsemShift.sarStruct?])]
  cases lsemStepN (.Lopn [.reg D] (withWidthTag wOp (cmpName c)) [.reg A, .reg B]) m.reg <;> rfl

/-- **The comparison on substituted cells.** When the comparison `SET<cc> D, [A, B]` steps
    from a base `a`, the comparison `SET<cc> D', [A', B']` steps from every base `b` whose
    cells at `A'`, `B'` are the cells of `a` at `A`, `B`, writing the same value. -/
theorem fstepF_setcc_congr {c : JasminDialect.JasminCmp} {wOp : Nat} {D D' A A' B B' : String}
    {cd cd' : Option Nat} {a b t : LstateM} {zf zt : Bool}
    (hA : b.reg.lvm A' = a.reg.lvm A) (hB : b.reg.lvm B' = a.reg.lvm B)
    (h : fstepF (.Lopn [.reg D] (withWidthTag wOp (cmpName c)) [.reg A, .reg B], .reg cd) a zf
      = some (t, zt)) :
    zt = zf ∧ ∃ (w : Nat) (v : BitVec w), t = (a.setReg D v).nextPc
      ∧ fstepF (.Lopn [.reg D'] (withWidthTag wOp (cmpName c)) [.reg A', .reg B'], .reg cd')
          b zf = some ((b.setReg D' v).nextPc, zf) := by
  rw [fstepF_setcc_eq] at h
  rw [fstepF_setcc_eq]
  have gB : ∀ w, b.reg.getW B' w = a.reg.getW B w := fun w => by
    unfold LstateN.getW; rw [hB]
  have rA : readReg b.reg (.reg A') = some (a.reg.lvm A) := by simp only [readReg, hA]
  have rA' : readReg a.reg (.reg A) = some (a.reg.lvm A) := rfl
  simp only [lsemStepN] at h ⊢
  rw [rA] at ⊢
  rw [rA'] at h
  generalize a.reg.lvm A = cA at h ⊢
  obtain ⟨wA, vA⟩ := cA
  simp only [evalOperandN, gB] at h ⊢
  cases hb : a.reg.getW B wA with
  | none => simp [hb] at h
  | some vb =>
      simp only [hb] at h ⊢
      cases happ : applyOpnN wA (stripWidthTag (withWidthTag wOp (cmpName c))) [vA, vb] with
      | some v =>
          simp only [happ, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rfl, _, v, rfl, rfl, trivial⟩
      | none =>
          simp only [happ] at h ⊢
          cases hcmp : cmpOfName? (stripWidthTag (withWidthTag wOp (cmpName c))) with
          | none => simp [hcmp] at h
          | some k =>
              simp only [hcmp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h ⊢
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨rfl, _, JasminDialect.cmpBit k vA vb, rfl, rfl, trivial⟩

/-- **The comparison on the scratches.** When the comparison `SET<cc> D, [A, B]` steps from
    a base, the sequence `mov R15, A ; mov R14, B ; SET<cc> R15, [R15, R14] ; mov D, R15`
    (a move mnemonic stripping to `MOV`) runs from every base that agrees with it outside
    the scratches to a base that agrees with the result outside the scratches, with the
    same zero flag, provided `A` and `B` are no scratches. -/
theorem fstepF_setccSpill (c : JasminDialect.JasminCmp) (wOp : Nat) (D A B mov : String)
    (cd cd' : Option Nat) (t1 t2 t4 : MemTag) (hmov : stripWidthTag mov = "MOV")
    (hA' : KeptS A) (hB' : KeptS B) {a a' t : LstateM} {zf zt : Bool} (hA : AgreeS a a')
    (h : fstepF (.Lopn [.reg D] (withWidthTag wOp (cmpName c)) [.reg A, .reg B], .reg cd) a zf
      = some (t, zt)) :
    ∃ t', runStraightF [(.Lopn [.reg reloadScratch] mov [.reg A], t1),
        (.Lopn [.reg reloadScratch2] mov [.reg B], t2),
        (.Lopn [.reg reloadScratch] (withWidthTag wOp (cmpName c))
          [.reg reloadScratch, .reg reloadScratch2], .reg cd'),
        (.Lopn [.reg D] mov [.reg reloadScratch], t4)] a' zf
        = some (t', zt) ∧ AgreeS t t' := by
  have e1 := fstepF_copyWire reloadScratch A mov t1 (Or.inl hmov) a' zf
  have hX1 := hA.setScratch not_keptS_reloadScratch (a'.reg.lvm A).2
  generalize hX1d : (a'.setReg reloadScratch (a'.reg.lvm A).2).nextPc = X1 at e1 hX1
  have e2 := fstepF_copyWire reloadScratch2 B mov t2 (Or.inl hmov) X1 zf
  have hX2 := hX1.setScratch not_keptS_reloadScratch2 (X1.reg.lvm B).2
  have h15 : ((X1.setReg reloadScratch2 (X1.reg.lvm B).2).nextPc).reg.lvm reloadScratch
      = a.reg.lvm A := by
    rw [lvm_copy_other _ _ reloadScratch_ne_reloadScratch2, ← hX1d, lvm_copy, hA.reg A hA']
  have h14 : ((X1.setReg reloadScratch2 (X1.reg.lvm B).2).nextPc).reg.lvm reloadScratch2
      = a.reg.lvm B := by
    rw [lvm_copy, hX1.reg B hB']
  obtain ⟨rfl, w, v, rfl, h3⟩ := fstepF_setcc_congr (D' := reloadScratch) (cd' := cd')
    h15 h14 h
  have e4 := fstepF_copyWire D reloadScratch mov t4 (Or.inl hmov)
    (((X1.setReg reloadScratch2 (X1.reg.lvm B).2).nextPc).setReg reloadScratch v).nextPc zt
  rw [lvm_setReg_self] at e4
  exact ⟨_, by
      rw [runStraightF_cons, e1, Option.bind_some, runStraightF_cons, e2, Option.bind_some,
        runStraightF_cons, h3, Option.bind_some, runStraightF_cons, e4]; rfl,
    (hX2.setScratch not_keptS_reloadScratch v).setReg D v⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload
