/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresIsa
public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
public import CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmIsa

/-!
# The `runBlock` correspondence `CorresJ` at the x86 instruction set

`CorresJ SR P fa c` is a forward simulation over the total fold `runBlock` of a block
`c : List (JInstr 64)`. This module transports it to `CorresIsa x86Isa` for the `Lprog`
program `singletonProgM fn (c.flatMap jToRMs)`, the lowering of `c` of `RunBlockLsemAgree`,
when every instruction of `c` is in the subset `InSubsetM` (register arithmetic, the
compile-time-offset loads and stores, `mulx`).

The `Lprog` side relation `liftSR fn SR` holds at a flag-extended state `t` and an abstract
pair `(a, k)` when `t` is in the function `fn` at program counter `k` and some `JState`
related to `a` by `SR` agrees with the base of `t` on the registers and the memory
(`RunBlockLsemAgree.JLstateCorr`). The flags of the two machines are not related: on
`InSubsetM` the registers and the memory of `runBlock` do not depend on the flags. The
program counter is part of the abstract state because `CorresM` uses one relation before
and after the run, which start at counter `0` and end at the length of the body.

The transport is stated once for an arbitrary instruction set, over a run of the program
that agrees with `runBlock` (`corresIsa_of_lsemFuelMemF`), and at `x86Isa` over the extended
straight fold `runStraightF` of the flag machine (`corresIsa_x86_of_runStraightF`). For
`InSubsetM` the fold agreement composes `runBlock_lsem_agreeM` (`runBlock` against
`lsemStraightMem`) and `runStraightF_of_lsemStraightMem` (`lsemStraightMem` against the flag
machine's straight fold, equal up to the carry and overflow flags); the run of the fold is
the segment run `lsemFuelMemF_segF` with `x86Isa_lsemFuelMemF` (the generic run at `x86Isa`
is the flag machine's run).

The same lowered program runs on the AArch64 instance `armIsa` when the block is in
`InFieldArithSubset` (no `mulx`, whose high half `MULXHI` is outside the AArch64 alphabet):
there the step of each lowered instruction is `lsemStepMem` on the base, so the run is
`lsemStraightMem` (`armIsa_runL_map_jToRM`), and `Isa.lsemFuelMemF_of_runL` of `LprogIsa`
turns it into the run of the program.

## Main results

* `liftSR`: the `Lprog` side relation of a `JState` relation.
* `plainLopnBody_flatMap_jToRMs`: the lowering of an `InSubsetM` block is a plain `Lopn`
  body.
* `x86Isa_lsemFuelMemF_straight`: a plain `Lopn` body runs from counter `0` with fuel its
  length to the state of its straight fold.
* `corresIsa_of_lsemFuelMemF`: `CorresJ` gives `CorresIsa isa`, for any instruction set
  `isa`, for a program whose run from counter `0` agrees with `runBlock`.
* `corresIsa_x86_of_runStraightF`: `CorresJ` gives `CorresIsa x86Isa` for a body of `Lopn`s
  whose extended straight fold agrees with `runBlock`.
* `corresIsa_x86_of_corresJ`: `CorresJ` over an `InSubsetM` block gives `CorresIsa x86Isa`
  for its lowering.
* `corresIsa_x86_add2`: the two-instruction example `x += 1; x += 2`.
* `armIsa_step_jToRM`, `armIsa_runL_map_jToRM`, `corresIsa_arm_of_corresJ`,
  `corresIsa_arm_add2`: the same transport and the same example at `armIsa`.

@ascent-fixture theorems: corresIsa_x86_add2, corresIsa_arm_add2
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RunBlockLsemAgree
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (LinstrRM LstateM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (findInstrMem singletonProgM
  IsLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF PlainLopnBody
  cmpArgs? movRegArgs?)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (runStraightF
  runStraightF_lpc runStraightF_of_lsemStraightMem lsemFuelMemF_segF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_lsemFuelMemF)

/-- **The `Lprog` side relation of a `JState` relation**: the state is in the function `fn`
    at the program counter of the abstract pair, and some `JState` related by `SR` to the
    abstract state agrees with its base on the registers and the memory. -/
def liftSR {AState : Type} (fn : String) (SR : JState 64 → AState → Prop)
    (t : LstateMF) (a : AState × Nat) : Prop :=
  t.prog.lfn = fn ∧ t.prog.base.lpc = a.2 ∧ ∃ s, SR s a.1 ∧ JLstateCorr s t.prog.base

/-- The register and memory agreement does not read the carry and overflow flags. -/
theorem JLstateCorr_withFlags {s : JState 64} {b : LstateM} (h : JLstateCorr s b)
    (c o : Bool) : JLstateCorr s { b with cf := c, of := o } :=
  ⟨h.regAgree, h.memAgree⟩

/-- The lowering of an instruction of `InSubsetM` consists of `Lopn`s that are neither the
    flag compare nor a register copy. -/
theorem plainLopnBody_jToRMs (i : JInstr 64) (hi : InSubsetM i) :
    PlainLopnBody (jToRMs i) := by
  cases i
  case mov d s =>
    cases s <;> simp_all [InSubsetM, InFieldArithSubset, jToRMs, jToRM, PlainLopnBody,
      IsLopn, cmpArgs?, movRegArgs?]
  case storeMem b o s =>
    cases s <;> simp_all [InSubsetM, InFieldArithSubset, jToRMs, jToRM, PlainLopnBody, IsLopn,
      cmpArgs?, movRegArgs?]
  case mulx h l a b =>
    cases a <;> cases b <;> simp_all [InSubsetM, InFieldArithSubset, jToRMs, PlainLopnBody,
      IsLopn, cmpArgs?, movRegArgs?, withWidthTag]
  all_goals simp_all [InSubsetM, InFieldArithSubset, jToRMs, jToRM, PlainLopnBody, IsLopn,
    cmpArgs?, movRegArgs?, withWidthTag]

/-- The lowering of a block of `InSubsetM` instructions is a plain `Lopn` body. -/
theorem plainLopnBody_flatMap_jToRMs (c : List (JInstr 64)) (hc : ∀ i ∈ c, InSubsetM i) :
    PlainLopnBody (c.flatMap jToRMs) := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hx
  exact plainLopnBody_jToRMs i (hc i hi) x hxi

/-- **A plain `Lopn` body from counter `0`**: the `x86Isa` run of the singleton program with
    fuel the body length ends in the state the straight fold `runStraightF` reaches. -/
theorem x86Isa_lsemFuelMemF_straight (fn : String) (seg : List LinstrRM)
    (hl : ∀ i ∈ seg, IsLopn i) (b0 b : LstateM) (zf z : Bool) (hpc : b0.lpc = 0)
    (hrun : runStraightF seg b0 zf = some (b, z)) :
    x86Isa.lsemFuelMemF (singletonProgM fn seg) seg.length
        { prog := { base := b0, lfn := fn }, zf := zf }
      = some { prog := { base := b, lfn := fn }, zf := z } := by
  rw [x86Isa_lsemFuelMemF]
  have hseg := lsemFuelMemF_segF (singletonProgM fn seg) fn rfl seg b0 zf 0 hl
    (fun k _ => by rw [hpc, Nat.zero_add]; rfl)
  rw [Nat.add_zero] at hseg
  rw [hseg, hrun, Option.bind_some]
  have hlpc : b.lpc = seg.length := by
    rw [runStraightF_lpc seg b0 zf b z hrun, hpc, Nat.zero_add]
  unfold VIR.JasminLsemMemFlagGuard.lsemFuelMemF
  simp only [findInstrMem, singletonProgM, ite_true]
  rw [hlpc, List.getElem?_eq_none (le_refl _)]

/-- **`CorresJ` over a run of an instruction set.** Let the run of `prog` at the instruction
    set `isa` with fuel `n`, from every state of the function `fn` at counter `0` whose base
    agrees with a `JState` `s` on the registers and the memory, end in the function `fn` at
    counter `len` in a base agreeing with `runBlock s c`. Then a `runBlock` correspondence
    `CorresJ SR P fa c` gives the `CorresIsa isa` correspondence of `prog` with fuel `n`,
    under the lifted relation `liftSR fn SR`, from counter `0` to counter `len`. -/
theorem corresIsa_of_lsemFuelMemF {AState : Type} (isa : VIR.LprogIsa.Isa)
    (SR : JState 64 → AState → Prop) (P : AState → Prop) (fa : AState → AState)
    (c : List (JInstr 64)) (fn : String) (prog : VIR.JasminLsemMemLoop.LprogM) (n len : Nat)
    (hrun : ∀ (s : JState 64) (b0 : LstateM) (zf : Bool), JLstateCorr s b0 → b0.lpc = 0 →
      ∃ b z, isa.lsemFuelMemF prog n { prog := { base := b0, lfn := fn }, zf := zf }
          = some { prog := { base := b, lfn := fn }, zf := z } ∧
        b.lpc = len ∧ JLstateCorr (runBlock s c) b)
    (h : CorresJ SR P fa c) :
    CorresIsa isa prog (liftSR fn SR) (fun a => P a.1 ∧ a.2 = 0) (fun a => (fa a.1, len)) n := by
  rintro ⟨⟨b0, lfn⟩, zf⟩ ⟨a, k⟩ ⟨hfn, hpc, s, hSR, hcorr⟩ ⟨hP, hk⟩
  simp only at hfn hpc hcorr hP hk
  subst hfn hk
  obtain ⟨b, z, hF, hlpc, hcorr'⟩ := hrun s b0 zf hcorr hpc
  exact ⟨_, hF, rfl, hlpc, runBlock s c, h s a hSR hP, hcorr'⟩

/-- **`CorresJ` at the x86 instruction set, over the extended straight fold.** Let `seg` be a
    body of `Lopn`s whose fold `runStraightF`, from every state agreeing with a `JState` `s`
    on the registers and the memory, reaches a state agreeing with `runBlock s c`. Then a
    `runBlock` correspondence `CorresJ SR P fa c` gives the `CorresIsa x86Isa`
    correspondence of `singletonProgM fn seg` with fuel its length, under the lifted
    relation `liftSR fn SR`, from counter `0` to the end of the body. -/
theorem corresIsa_x86_of_runStraightF {AState : Type} (SR : JState 64 → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : List (JInstr 64)) (fn : String)
    (seg : List LinstrRM) (hl : ∀ i ∈ seg, IsLopn i)
    (hagree : ∀ (s : JState 64) (b0 : LstateM) (zf : Bool), JLstateCorr s b0 →
      ∃ b z, runStraightF seg b0 zf = some (b, z) ∧ JLstateCorr (runBlock s c) b)
    (h : CorresJ SR P fa c) :
    CorresIsa x86Isa (singletonProgM fn seg) (liftSR fn SR)
      (fun a => P a.1 ∧ a.2 = 0) (fun a => (fa a.1, seg.length)) seg.length :=
  corresIsa_of_lsemFuelMemF x86Isa SR P fa c fn (singletonProgM fn seg) seg.length seg.length
    (fun s b0 zf hcorr hpc => by
      obtain ⟨b, z, hF, hcorr'⟩ := hagree s b0 zf hcorr
      refine ⟨b, z, x86Isa_lsemFuelMemF_straight fn seg hl b0 b zf z hpc hF, ?_, hcorr'⟩
      rw [runStraightF_lpc seg b0 zf b z hF, hpc, Nat.zero_add])
    h

/-- **`CorresJ` at the x86 instruction set.** For a block `c` of `InSubsetM` instructions, a
    `runBlock` correspondence `CorresJ SR P fa c` gives the `CorresIsa x86Isa` correspondence
    of the lowered program `singletonProgM fn (c.flatMap jToRMs)` with fuel its length,
    under the lifted relation `liftSR fn SR`, from counter `0` to the end of the body. -/
theorem corresIsa_x86_of_corresJ {AState : Type} (SR : JState 64 → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : List (JInstr 64)) (fn : String)
    (hc : ∀ i ∈ c, InSubsetM i) (h : CorresJ SR P fa c) :
    CorresIsa x86Isa (singletonProgM fn (c.flatMap jToRMs)) (liftSR fn SR)
      (fun a => P a.1 ∧ a.2 = 0) (fun a => (fa a.1, (c.flatMap jToRMs).length))
      (c.flatMap jToRMs).length :=
  corresIsa_x86_of_runStraightF SR P fa c fn (c.flatMap jToRMs)
    (fun i hi => (plainLopnBody_flatMap_jToRMs c hc i hi).1)
    (fun s b0 zf hcorr => by
      obtain ⟨ls', hrun, hcorr'⟩ := runBlock_lsem_agreeM c hc s b0 hcorr
      obtain ⟨cf, of, hF⟩ := runStraightF_of_lsemStraightMem _
        (plainLopnBody_flatMap_jToRMs c hc) b0 ls' zf hrun
      exact ⟨_, zf, hF, JLstateCorr_withFlags hcorr' cf of⟩)
    h

/-! ## Example: two additions -/

/-- The block `x += 1; x += 2`. -/
def add2Block : List (JInstr 64) := [.add "x" (.imm 1), .add "x" (.imm 2)]

/-- The block `x += 1; x += 2` adds `3` to the register `x` under `runBlock`. -/
theorem corresJ_add2 :
    CorresJ (fun (st : JState 64) (v : BitVec 64) => st.regs "x" = v) (fun _ => True)
      (fun v => v + 3) add2Block := by
  intro st a h _
  simp only [add2Block, runBlock_cons, runBlock_nil, evalInstr, JState.writeB5W, x86_ADD,
    rflags_of_aluop, JState.get, JOperand.eval, h, ite_true, BitVec.add_assoc]
  rfl

/-- **The two-instruction example at x86**: the lowered program of `x += 1; x += 2` adds `3`
    to the register `x` in two steps of the `x86Isa` run. -/
theorem corresIsa_x86_add2 (fn : String) :
    CorresIsa x86Isa (singletonProgM fn (add2Block.flatMap jToRMs))
      (liftSR fn (fun (st : JState 64) (v : BitVec 64) => st.regs "x" = v))
      (fun a => True ∧ a.2 = 0) (fun a => (a.1 + 3, 2)) 2 :=
  corresIsa_x86_of_corresJ _ _ _ add2Block fn
    (by simp [add2Block, InSubsetM, InFieldArithSubset]) corresJ_add2

/-! ## The same lowering at the AArch64 instance

On the lowering of an `InFieldArithSubset` instruction the `armIsa` step is the straight-line
step `lsemStepMem` on the base, with the flags unchanged. -/

open CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmIsa (armIsa armIsa_step_core armBases
  armCmp)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (coreStep mnemOk isCtl)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem (lsemStepMem lsemStraightMem)

/-- An `InFieldArithSubset` instruction lowers to the single instruction `jToRM i`. -/
theorem jToRMs_of_inFieldArithSubset (i : JInstr 64) (hi : InFieldArithSubset i) :
    jToRMs i = [jToRM i] := by
  cases i <;> simp_all [InFieldArithSubset, jToRMs]

/-- On a block of `InFieldArithSubset` instructions the lowering is `List.map jToRM`. -/
theorem flatMap_jToRMs_of_inFieldArithSubset (c : List (JInstr 64))
    (hc : ∀ i ∈ c, InFieldArithSubset i) : c.flatMap jToRMs = c.map jToRM := by
  induction c with
  | nil => rfl
  | cons i c ih =>
      rw [List.flatMap_cons, List.map_cons,
        jToRMs_of_inFieldArithSubset i (hc i (List.mem_cons_self ..)),
        ih (fun j hj => hc j (List.mem_cons_of_mem i hj))]
      rfl

/-- The `armIsa` step of the lowering of an `InFieldArithSubset` instruction is
    `lsemStepMem` on the base. -/
theorem armIsa_step_jToRM (P : VIR.JasminLsemMemLoop.LprogM) (i : JInstr 64)
    (hi : InFieldArithSubset i) (s : LstateMF) :
    armIsa.step P (jToRM i) s =
      (lsemStepMem (jToRM i) s.prog.base).map
        (fun b => { s with prog := { s.prog with base := b } }) := by
  have hplain := plainLopnBody_jToRMs i (by cases i <;> simp_all [InSubsetM, InFieldArithSubset])
    (jToRM i) (by rw [jToRMs_of_inFieldArithSubset i hi]; exact List.mem_singleton_self _)
  obtain ⟨hl, hc, hm⟩ := hplain
  have hok : mnemOk armBases (jToRM i).fst = true := by
    cases i
    case mov d s => cases s <;> simp_all [InFieldArithSubset, jToRM, mnemOk]; decide
    case storeMem b o s => cases s <;> simp_all [InFieldArithSubset, jToRM, mnemOk]; decide
    all_goals simp_all [InFieldArithSubset, jToRM, mnemOk] <;> decide
  have hctl : isCtl (jToRM i).fst = false := by
    obtain ⟨d, o, src, hd⟩ := hl
    rw [hd]; rfl
  have hcmp : armCmp (jToRM i) s = none := by
    unfold armCmp; rw [hc]
  rw [armIsa_step_core P _ s hok hctl hcmp]
  unfold coreStep
  rw [hm, VIR.JasminLsemMemLoop.evalInstrPMemL_lopn P _ s.prog hl, Option.map_map]
  rfl

/-- The `armIsa` run of the lowering of an `InFieldArithSubset` block is its straight-line
    run `lsemStraightMem` on the base. -/
theorem armIsa_runL_map_jToRM (P : VIR.JasminLsemMemLoop.LprogM) (c : List (JInstr 64))
    (hc : ∀ i ∈ c, InFieldArithSubset i) (b0 : LstateM) (fn : String) (zf : Bool) :
    armIsa.runL P (c.map jToRM) { prog := { base := b0, lfn := fn }, zf := zf } =
      (lsemStraightMem (c.map jToRM) b0).map
        (fun b => { prog := { base := b, lfn := fn }, zf := zf }) := by
  induction c generalizing b0 with
  | nil => rfl
  | cons i c ih =>
      simp only [List.map_cons, VIR.LprogIsa.Isa.runL, VIR.JasminLsemMem.lsemStraightMem_cons,
        armIsa_step_jToRM P i (hc i (List.mem_cons_self ..))]
      cases lsemStepMem (jToRM i) b0 with
      | none => rfl
      | some b1 =>
          simp only [Option.map_some, Option.bind_some]
          exact ih (fun j hj => hc j (List.mem_cons_of_mem i hj)) b1

/-- **`CorresJ` at the AArch64 instruction set.** For a block `c` of `InFieldArithSubset`
    instructions, a `runBlock` correspondence `CorresJ SR P fa c` gives the `CorresIsa armIsa`
    correspondence of the same lowered program as `corresIsa_x86_of_corresJ`, with fuel its
    length, under the lifted relation `liftSR fn SR`. -/
theorem corresIsa_arm_of_corresJ {AState : Type} (SR : JState 64 → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : List (JInstr 64)) (fn : String)
    (hc : ∀ i ∈ c, InFieldArithSubset i) (h : CorresJ SR P fa c) :
    CorresIsa armIsa (singletonProgM fn (c.flatMap jToRMs)) (liftSR fn SR)
      (fun a => P a.1 ∧ a.2 = 0) (fun a => (fa a.1, (c.flatMap jToRMs).length))
      (c.flatMap jToRMs).length := by
  rw [flatMap_jToRMs_of_inFieldArithSubset c hc]
  refine corresIsa_of_lsemFuelMemF armIsa SR P fa c fn _ _ _ (fun s b0 zf hcorr hpc => ?_) h
  obtain ⟨ls', hrun, hcorr'⟩ := runBlock_lsem_agree c hc s b0 hcorr
  have hrunL := armIsa_runL_map_jToRM (singletonProgM fn (c.map jToRM)) c hc b0 fn zf
  rw [hrun, Option.map_some] at hrunL
  refine ⟨ls', zf, armIsa.lsemFuelMemF_of_runL _ (c.map jToRM) [] _ _ rfl rfl hpc ?_ hrunL, ?_,
    hcorr'⟩
  · intro j hj u u' hu
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    rw [armIsa_step_jToRM _ i (hc i hi)] at hu
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hu
    exact ⟨rfl, VIR.JasminLsemMemLoop.lsemStepMem_lpc_succ _ _ _ hb⟩
  · rw [VIR.JasminLsemMemLoop.lsemStraightMem_lpc _ b0 ls' hrun, hpc, Nat.zero_add]

/-- **The two-instruction example at AArch64**: the program of `corresIsa_x86_add2` adds `3`
    to the register `x` in two steps of the `armIsa` run. -/
theorem corresIsa_arm_add2 (fn : String) :
    CorresIsa armIsa (singletonProgM fn (add2Block.flatMap jToRMs))
      (liftSR fn (fun (st : JState 64) (v : BitVec 64) => st.regs "x" = v))
      (fun a => True ∧ a.2 = 0) (fun a => (a.1 + 3, 2)) 2 :=
  corresIsa_arm_of_corresJ _ _ _ add2Block fn
    (by simp [add2Block, InFieldArithSubset]) corresJ_add2

end CatCrypt.Crypto.SecureCompilation.Ascent
