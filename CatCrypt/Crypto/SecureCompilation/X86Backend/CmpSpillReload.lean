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

## Main results

* `cmpReload_of_forall`: the pass is the identity on a body without such a compare.
* `spillCmp?_of_mem_cmpReload`, `cmpReload_idem`: the result has no such compare, and the
  pass is idempotent.
* `typeBody_cmpReload`: the typed body of the result is the expansion of the typed body.
* `fstepF_cmpReload`: the copy and the compare on the scratch reach the state of the
  compare on the slot, outside the scratch, with the same zero flag.
* `cmpReload_lsemFuelMemF`: a halting run of a body that passes `cmpReloadOK` is matched
  by a halting run of the rewritten body with at most twice the fuel.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-- **A compare whose first operand is a spill slot**: for `Lopn [d] opn [d, s]` with
    mnemonic base `CMP`, `d` a spill slot and `s` other than the reload scratch, the
    mnemonic, the slot name and the second operand; `none` for every other instruction. -/
def spillCmp? : LinstrR → Option (String × String × LOperand)
  | .Lopn [.reg d] opn [.reg a, s] =>
      if stripWidthTag opn == "CMP" && d == a && (LOperand.reg d).isSpill
          && s != .reg reloadScratch then some (opn, d, s)
      else none
  | _ => none

/-- The copy mnemonic at the width of the compare `opn`. -/
def movOf (opn : String) : String := if hasSuffix opn ":64" then "MOV:64" else "MOV"

/-- **The rewrite of an instruction**: a compare on a spilled first operand becomes the copy
    of the slot to the reload scratch and the compare on the scratch; every other
    instruction is kept. -/
def cmpReloadI (i : Linstr) : Lcmd :=
  match spillCmp? i.li_i with
  | some (opn, d, s) =>
      [⟨i.li_ii, .Lopn [.reg reloadScratch] (movOf opn) [.reg d]⟩,
       ⟨i.li_ii, .Lopn [.reg reloadScratch] opn [.reg reloadScratch, s]⟩]
  | none => [i]

/-- **The reload of spilled compare operands** on a body. -/
def cmpReload (body : Lcmd) : Lcmd := body.flatMap cmpReloadI

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
def cmpReloadRM (tag : LinstrR → MemTag) (i : LinstrRM) : List LinstrRM :=
  typeBody tag (cmpReloadI ⟨0, i.1⟩)

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
def cmpReloadOKI (tag : LinstrR → MemTag) (w : LinstrR) : Bool :=
  clsB (w, tag w) && (instrNames w).all (fun n => n != reloadScratch) && mulxFree (w, tag w)
    && (match spillCmp? w with
        | some (opn, _, _) => opn == withWidthTag 64 "CMP"
        | none => true)

/-- **The side conditions of the pass** on a body typed with `tag`: `cmpReloadOKI` at
    every instruction. -/
def cmpReloadOK (tag : LinstrR → MemTag) (body : Lcmd) : Bool :=
  body.all fun i => cmpReloadOKI tag i.li_i

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
        · rw [hself] at hj
          obtain rfl : j = (w, tag w) := by simpa using hj
          exact hl
        · rw [hself]
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
        simp [cmpReloadRM, cmpReloadI, hsp, typeBody]
      refine Or.inl ⟨⟨_, _, _, rfl⟩, fun j hj => ?_, fun a a' t zf zt hA hst => ?_⟩
      · rw [hexp] at hj
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
        rcases hj with rfl | rfl <;> exact ⟨_, _, _, rfl⟩
      · rw [hexp]
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

end CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload
