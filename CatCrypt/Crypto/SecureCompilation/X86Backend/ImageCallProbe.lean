/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink

@[expose] public section

set_option autoImplicit false

/-!
# The image relation across a call to a specified procedure

`ImageAddrSim.ImgRel` relates a state of the name-keyed machine on the image of a printed
body to a state of the address machine `LstateA`, and `DecodePrintedAddr.ACorr` relates that
state to a state of the byte machine `aMachine`. This module states the specification of a
callee on the byte machine (`CalleeSpec`), a summary step of a call on the two name-keyed
levels (`callSummary`, `callA`), and proves that the two relations hold again after the
call.

## The summary step

A call sets the result name to the callee's function of the argument words, sets every
general-purpose name the callee does not keep and the three flags to the values of an
oracle `CallOut`, and advances the program counter. `callSummary` is the step on the image
and `callA` the step on `LstateA`; `CallStep` is the relation over all oracles.

## The relation after a call

With the oracle read off the byte machine after the return (`outOf`), `ImgRel` and `ACorr`
hold after the call (`imgRel_call`, `acorr_call`, `call_reestablishes`). The flags need no
exemption: `ACorr` does not relate flags, so `callA` takes the flags of the oracle of the
image. For an arbitrary oracle the image state agrees with a related state off the names
`exempt c`; `ImgRelX X` is `ImgRel` up to the values of the names in `X`. A register
instruction whose symbolic description reads no name of `X` (`readsClearB`) removes the
names it writes from `X` (`relX_reg_checked`), a frame-word load removes its destination
(`relX_sload`), and `ImgRelX []` is `ImgRel` (`imgRelX_nil`).

## Main results

* `CalleeSig`, `CalleeSpec`: the specification of a callee on the byte machine.
* `callSpec_return`: the byte machine across `callOps`, the callee and `retOps`.
* `haltsC_call_spec`: a call to a relocated copy of a specified block continues after it.
* `imgRel_call`: `ImgRel` across the summary step, for a memory that keeps the frame words
  and the array words.
* `acorr_call`: `ACorr` across the summary step with the oracle `outOf`.
* `call_reestablishes`: from `ImgRel`, `ACorr` and `CalleeSpec`, with the frame words and the
  array words outside the callee's footprint and the return word (`FootClear`), the callee
  halts and both relations hold after the return; for every oracle the relaxed relation
  holds.
* `relX_reg`, `relX_reg_checked`, `relX_sload`, `imgRelX_nil`: the relaxed relation along
  the instructions after the call.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun (normA)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr callOps retOps)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg haltsC_call_relocated)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (leaFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrinted
  (gpOk gpList mem_gpList gpFacts phys evalInstrA_leaFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddr (ACorr redW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG (LoadSafeAt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrSim
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)

/-! ## 1. The specification of a callee -/

/-- The interface of a callee: the names of its argument registers and of its result
    register, the general-purpose names it keeps, its function on the argument words, its
    precondition on the entry state and its footprint, the set of addresses it may write,
    as a function of the entry state. -/
structure CalleeSig where
  /-- The names of the argument registers, in order. -/
  args : List String
  /-- The name of the result register. -/
  res : String
  /-- The general-purpose names whose registers the callee keeps. -/
  keep : List String
  /-- The function on the argument words. -/
  sem : List (BitVec 64) → BitVec 64
  /-- The precondition on the state at the callee's entry. -/
  pre : AState → Prop
  /-- The addresses the callee may write, from the state at its entry. -/
  foot : AState → BitVec 64 → Prop

/-- **The specification of a callee on the byte machine.** From every entry state that
    satisfies the precondition, the block `q` halts from index `0`; at its return the result
    register holds the function of the argument registers at entry, the stack register and
    the kept registers hold their entry values, and every byte outside the footprint holds
    its entry value. -/
def CalleeSpec (q : List RInstr) (c : CalleeSig) : Prop :=
  ∀ s : AState, c.pre s → ∃ s' : AState, HaltsC aMachine q 0 s s'
    ∧ s'.regs (phys c.res) = c.sem (c.args.map fun a => s.regs (phys a))
    ∧ s'.regs "%rsp" = s.regs "%rsp"
    ∧ (∀ r ∈ c.keep, s'.regs (phys r) = s.regs (phys r))
    ∧ ∀ x, ¬ c.foot s x → s'.mem x = s.mem x

/-! ## 2. The byte machine across a call -/

/-- The address of the return word of a call from `s`: eight below the stack register. -/
def retWord (s : AState) : BitVec 64 := s.regs "%rsp" + BitVec.ofInt 64 (-8)

/-- The state at the callee's entry: after the call lowers the stack register and stores
    the return index. -/
def entryOf (ret : Nat) (s : AState) : AState := (callOps ret).foldl aMachine.exec s

theorem entryOf_eq (ret : Nat) (s : AState) :
    entryOf ret s
      = evalInstrA (evalInstrA s (leaFrame (-8))) (.storeMem "%rsp" 0 (.imm ret)) := rfl

/-- The registers at the callee's entry: the stack register is the address of the return
    word, the others are kept. -/
theorem entryOf_regs (ret : Nat) (s : AState) (r : String) :
    (entryOf ret s).regs r = if r = "%rsp" then retWord s else s.regs r := by
  have h := (evalInstrA_leaFrame s (-8)).1 r
  have e : (evalInstrA (evalInstrA s (leaFrame (-8))) (.storeMem "%rsp" 0 (.imm ret))).regs r
      = (evalInstrA s (leaFrame (-8))).regs r := by
    simp [evalInstrA, evalInstr, JState.store, AState.view]
  rw [entryOf_eq, e, h]
  rfl

/-- The memory at the callee's entry differs from the memory before the call only in the
    return word. -/
theorem entryOf_mem (ret : Nat) (s : AState) (x : BitVec 64) (hx : ¬ InRange8 (retWord s) x) :
    (entryOf ret s).mem x = s.mem x := by
  have h1 := (evalInstrA_leaFrame s (-8)).1 "%rsp"
  have h2 := (evalInstrA_leaFrame s (-8)).2
  rw [if_pos rfl] at h1
  have e : s.regs "%rsp" + BitVec.ofInt 64 (-8) + BitVec.ofInt 64 0 = retWord s := by
    simp [retWord]
  rw [entryOf_eq]
  show write64 (evalInstrA s (leaFrame (-8))).mem
    ((evalInstrA s (leaFrame (-8))).regs "%rsp" + BitVec.ofInt 64 0) _ x = _
  rw [h1, h2, e, write64_of_not_inRange _ _ _ _ hx]

theorem retOps_eq (s : AState) : retOps.foldl aMachine.exec s = evalInstrA s (leaFrame 8) := rfl

/-- **The byte machine across a call to a specified callee.** From a state whose entry state
    satisfies the precondition, the callee halts; after the return the stack register holds
    its value before the call, the result register holds the function of the argument
    registers before the call, the kept registers are kept, and every byte outside the
    footprint and the return word is kept. -/
theorem callSpec_return {q : List RInstr} {c : CalleeSig} (h : CalleeSpec q c)
    (hargs : ∀ a ∈ c.args, gpOk a = true) (hres : gpOk c.res = true)
    (hkeep : ∀ r ∈ c.keep, gpOk r = true) (ret : Nat) (s : AState)
    (hpre : c.pre (entryOf ret s)) :
    ∃ sc, HaltsC aMachine q 0 (entryOf ret s) sc
      ∧ (retOps.foldl aMachine.exec sc).regs "%rsp" = s.regs "%rsp"
      ∧ (retOps.foldl aMachine.exec sc).regs (phys c.res)
          = c.sem (c.args.map fun a => s.regs (phys a))
      ∧ (∀ r ∈ c.keep, (retOps.foldl aMachine.exec sc).regs (phys r) = s.regs (phys r))
      ∧ ∀ x, ¬ c.foot (entryOf ret s) x → ¬ InRange8 (retWord s) x →
          (retOps.foldl aMachine.exec sc).mem x = s.mem x := by
  obtain ⟨sc, hrun, hr, hsp, hk, hm⟩ := h (entryOf ret s) hpre
  have hne : ∀ r, gpOk r = true → phys r ≠ "%rsp" := fun r hr => (gpFacts hr).physNe
  obtain ⟨hl, hlm⟩ := evalInstrA_leaFrame sc 8
  refine ⟨sc, hrun, ?_, ?_, fun r hr' => ?_, fun x hx hx' => ?_⟩
  · rw [retOps_eq, hl, if_pos rfl, hsp, entryOf_regs, if_pos rfl, retWord, BitVec.add_assoc]
    simp
  · rw [retOps_eq, hl, if_neg (hne _ hres), hr]
    congr 1
    refine List.map_congr_left fun a ha => ?_
    rw [entryOf_regs, if_neg (hne a (hargs a ha))]
  · rw [retOps_eq, hl, if_neg (hne r (hkeep r hr')), hk r hr', entryOf_regs,
      if_neg (hne r (hkeep r hr'))]
  · rw [retOps_eq, hlm, hm x hx, entryOf_mem ret s x hx']

/-- **A call to a relocated copy of a specified block.** In
    `pre ++ shiftProg pre.length q ++ post`, let index `pc` hold a `call` to the copy of a
    block `q` without `call` that satisfies `CalleeSpec`. From a state whose entry state
    satisfies the precondition there is a state `s'`, with the stack register, the result
    register, the kept registers and the memory as in `callSpec_return`, such that every run
    of the linked program from `pc + 1` and `s'` extends to a run from `pc` and `s`. -/
theorem haltsC_call_spec {q : List RInstr} {c : CalleeSig} (h : CalleeSpec q c)
    (hq : ∀ tg, RInstr.call tg ∉ q) (hargs : ∀ a ∈ c.args, gpOk a = true)
    (hres : gpOk c.res = true) (hkeep : ∀ r ∈ c.keep, gpOk r = true)
    (pre post : List RInstr) {pc : Nat}
    (hcall : (pre ++ shiftProg pre.length q ++ post)[pc]? = some (.call pre.length))
    (s : AState) (hpre : c.pre (entryOf (pc + 1) s)) :
    ∃ s' : AState, s'.regs "%rsp" = s.regs "%rsp"
      ∧ s'.regs (phys c.res) = c.sem (c.args.map fun a => s.regs (phys a))
      ∧ (∀ r ∈ c.keep, s'.regs (phys r) = s.regs (phys r))
      ∧ (∀ x, ¬ c.foot (entryOf (pc + 1) s) x → ¬ InRange8 (retWord s) x → s'.mem x = s.mem x)
      ∧ ∀ s'', HaltsC aMachine (pre ++ shiftProg pre.length q ++ post) (pc + 1) s' s'' →
          HaltsC aMachine (pre ++ shiftProg pre.length q ++ post) pc s s'' := by
  obtain ⟨sc, hrun, h1, h2, h3, h4⟩ := callSpec_return h hargs hres hkeep (pc + 1) s hpre
  exact ⟨_, h1, h2, h3, h4, fun s'' hr =>
    haltsC_call_relocated aMachine pre q post hq hcall hrun hr⟩

/-! ## 3. The summary step of a call -/

/-- The values a call leaves unspecified: a word for each name and the three flags. -/
structure CallOut where
  /-- The word of a name the callee does not keep. -/
  reg : String → BitVec 64
  /-- The zero flag. -/
  zf : Bool
  /-- The carry flag. -/
  cf : Bool
  /-- The overflow flag. -/
  of : Bool

/-- The name `r` is a general-purpose name the callee does not keep. -/
def clobB (c : CalleeSig) (r : String) : Bool := gpOk r && !c.keep.contains r

/-- The word of an argument name: its value at width `64`, and `0` at another width. -/
def argWord (R : LstateN) (a : String) : BitVec 64 := (R.getW a 64).getD 0

theorem argWord_congr {R R' : LstateN} {a : String} (h : R.lvm a = R'.lvm a) :
    argWord R a = argWord R' a := by
  unfold argWord
  rw [getW_congr h]

/-- The register file after a call: the result name holds the function of the argument
    words, a name the callee does not keep holds the oracle's word, every other name is
    kept, and the program counter advances. -/
def callRegs (c : CalleeSig) (ω : CallOut) (R : LstateN) : LstateN where
  lvm := fun r =>
    if r = c.res then ⟨64, c.sem (c.args.map (argWord R))⟩
    else if clobB c r then ⟨64, ω.reg r⟩ else R.lvm r
  lpc := R.lpc + 1

/-- **The summary step of a call on the image**, a function of the oracle `ω`: the register
    file of `callRegs`, the three flags of `ω`, the arrays kept. -/
def callSummary (c : CalleeSig) (ω : CallOut) (s : LstateMF) : LstateMF :=
  { prog := { s.prog with
      base := { s.prog.base with reg := callRegs c ω s.prog.base.reg, cf := ω.cf, of := ω.of } }
    zf := ω.zf }

/-- The summary step of a call as a relation: `callSummary` for some oracle. -/
def CallStep (c : CalleeSig) (s t : LstateMF) : Prop := ∃ ω, t = callSummary c ω s

/-- **The summary step of a call on the address machine** `LstateA`: the register file of
    `callRegs`, the memory `m`, the carry and overflow flags of `ω`. -/
def callA (c : CalleeSig) (ω : CallOut) (m : AMem) (sa : LstateA) : LstateA :=
  { reg := callRegs c ω sa.reg, mem := m, cf := ω.cf, of := ω.of }

/-! ## 4. The image relation across the summary step -/

/-- Two memories that agree on the eight bytes from `a` hold one word at `a`. -/
theorem read64_congr_range {m m' : AMem} {a : BitVec 64}
    (h : ∀ x, InRange8 a x → m' x = m x) : read64 m' a = read64 m a := by
  have hk : ∀ k, k < 8 → m' (a + BitVec.ofNat 64 k) = m (a + BitVec.ofNat 64 k) :=
    fun k hk => h _ (by unfold InRange8; rw [toNat_add_sub_self a k hk]; exact hk)
  have h0 : m' a = m a := h a (by simp [InRange8])
  simp only [read64, h0, hk 1 (by decide), hk 2 (by decide), hk 3 (by decide),
    hk 4 (by decide), hk 5 (by decide), hk 6 (by decide), hk 7 (by decide)]

/-- After a call instruction no register is a reload of a frame word. -/
theorem reloadOf_call {slotArr : String → Option (String × Nat)} {body : Lcmd} {k : Nat}
    {bi : Linstr} (hb : body[k]? = some bi) {ra : Option String} {tgt : String × LLabel}
    (hbi : bi.li_i = .Lcall ra tgt) (b : String) : reloadOf slotArr body (k + 1) b = none := by
  simp [reloadOf, hb, hbi, slotMov?]

/-- **The image relation across the summary step of a call**, for one oracle on both
    levels. Let the instruction at the program counter be a call, the argument names and
    the result name general-purpose names, and every save of an array pointer after the
    call save a register the call keeps (`hsv`). If the memory `m` after the call holds the
    bytes of every frame word and of every array word of the memory before it, the relation
    holds between `callSummary c ω s` and `callA c ω m sa`. -/
theorem imgRel_call {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (c : CalleeSig) (ω : CallOut)
    {s : LstateMF} {sa : LstateA} {zf : Bool} (hrel : ImgRel frame slotArr base body s sa zf)
    {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi) {ra : Option String}
    {tgt : String × LLabel} (hbi : bi.li_i = .Lcall ra tgt)
    (hargs : ∀ a ∈ c.args, gpOk a = true) (hres : gpOk c.res = true)
    (hsv : ∀ k R A n, SaveAt body k R → slotArr (slotOfReg R) = some (A, n) →
      sa.reg.lpc < k → R ≠ c.res ∧ clobB c R = false)
    {m : AMem} (hfr : ∀ q a, frame q = some a → ∀ x, InRange8 a x → m x = sa.mem x)
    (hce : ∀ q A n j, slotArr q = some (A, n) → j < n →
      ∀ x, InRange8 (cellAt (base A) j) x → m x = sa.mem x) :
    ImgRel frame slotArr base body (callSummary c ω s) (callA c ω m sa) ω.zf := by
  have hmap : c.args.map (argWord s.prog.base.reg) = c.args.map (argWord sa.reg) :=
    List.map_congr_left fun a ha => argWord_congr (hrel.regs a (hsep.gp a (hargs a ha)))
  have hlvm : ∀ r, gpOk r = false →
      (callRegs c ω s.prog.base.reg).lvm r = s.prog.base.reg.lvm r := by
    intro r hr
    have h1 : r ≠ c.res := fun e => by rw [e, hres] at hr; cases hr
    simp [callRegs, h1, clobB, hr]
  refine ⟨congrArg (· + 1) hrel.pc, fun r hr => ?_, fun q a ha => ?_, rfl, rfl, rfl,
    fun r hr => ?_, fun q A n hq => ?_, fun k R A n a hS hA ha => ⟨fun hk => ?_, fun hk => ?_⟩,
    fun b q a A n hr => ?_, fun R A n a hR hA ha => by
      show read64 m a = base A
      rw [read64_congr_range (hfr _ a ha)]
      exact hrel.held R A n a hR hA ha⟩
  · show (callRegs c ω s.prog.base.reg).lvm r = (callRegs c ω sa.reg).lvm r
    simp only [callRegs, hmap, hrel.regs r hr]
  · have hq : gpOk q = false := by
      cases hg : gpOk q
      · rfl
      · rw [hsep.gp q hg] at ha; cases ha
    show (callRegs c ω s.prog.base.reg).lvm q = ⟨64, read64 m a⟩
    rw [hlvm q hq, hrel.slots q a ha, read64_congr_range (hfr q a ha)]
  · show ((callRegs c ω sa.reg).lvm r).1 = 64
    simp only [callRegs]
    split_ifs
    · rfl
    · rfl
    · exact hrel.wid r hr
  · obtain ⟨arr, h1, h2⟩ := hrel.cells q A n hq
    exact ⟨arr, h1, fun j hj => by
      show read64 m _ = _
      rw [read64_congr_range (hce q A n j hq hj)]; exact h2 j hj⟩
  · have hk' : k < sa.reg.lpc := by
      have hk0 : k < sa.reg.lpc + 1 := hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk0 with h | rfl
      · exact h
      · obtain ⟨i, hi, hm⟩ := hS
        rw [hb] at hi
        cases hi
        rw [hbi] at hm
        cases hm
    show read64 m a = base A
    rw [read64_congr_range (hfr _ a ha)]
    exact (hrel.saved k R A n a hS hA ha).1 hk'
  · have hk0 : sa.reg.lpc + 1 ≤ k := hk
    obtain ⟨hne, hcl⟩ := hsv k R A n hS hA (by omega)
    have e : (callRegs c ω sa.reg).lvm R = sa.reg.lvm R := by
      simp [callRegs, hne, hcl]
    show (callRegs c ω sa.reg).getW R 64 = some (base A)
    rw [getW_congr e]
    exact (hrel.saved k R A n a hS hA ha).2 (by omega)
  · have e : reloadOf slotArr body (sa.reg.lpc + 1) b = some q := hr
    rw [reloadOf_call hb hbi] at e
    cases e

/-- An indexed-load condition at a call instruction holds: the instruction is no load. -/
theorem loadSafeAt_call {rsp : BitVec 64} {body : Lcmd} {sa : LstateA} {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {ra : Option String} {tgt : String × LLabel}
    (hbi : bi.li_i = .Lcall ra tgt) : LoadSafeAt rsp body sa := by
  intro ii D B I h
  rw [hb] at h
  cases h
  cases hbi

/-! ## 5. The byte correspondence across the call -/

/-- The oracle read off the byte machine: the word of a name is the value of its machine
    register in `sA`; the flags are those of `ω`. -/
def outOf (sA : AState) (ω : CallOut) : CallOut := { ω with reg := fun r => sA.regs (phys r) }

/-- The memory of the address machine after a call: the bytes of the red-zone word of the
    memory `old` before it, the other bytes of the byte machine's memory `new`. -/
def memAfter (rsp : BitVec 64) (old new : AMem) : AMem :=
  fun x => if InRange8 (redW rsp) x then old x else new x

/-- **The byte correspondence across the summary step.** If after the return the stack
    register and the kept registers hold their values before the call and the result
    register holds the function of the argument registers, `ACorr` holds between the byte
    state after the return and `callA` with the oracle `outOf` and the memory `memAfter`. -/
theorem acorr_call {rsp : BitVec 64} {sA sA' : AState} {sa : LstateA} (c : CalleeSig)
    (ω : CallOut) (hc : ACorr rsp sA sa) (hargs : ∀ a ∈ c.args, gpOk a = true)
    (hsp : sA'.regs "%rsp" = sA.regs "%rsp")
    (hr : sA'.regs (phys c.res) = c.sem (c.args.map fun a => sA.regs (phys a)))
    (hk : ∀ r ∈ c.keep, sA'.regs (phys r) = sA.regs (phys r)) :
    ACorr rsp sA' (callA c (outOf sA' ω) (memAfter rsp sa.mem sA'.mem) sa) := by
  refine ⟨fun r hg => ?_, hsp.trans hc.sp, fun x hx => ?_⟩
  · show (callRegs c (outOf sA' ω) sa.reg).getW r 64 = some (sA'.regs (phys r))
    rw [getW_eq_some_iff]
    simp only [callRegs]
    split_ifs with h1 h2
    · subst h1
      rw [hr]
      congr 2
      refine List.map_congr_left fun a ha => ?_
      simp [argWord, hc.regs a (hargs a ha)]
    · rfl
    · have hm : r ∈ c.keep := by simpa [clobB, hg] using h2
      rw [hk r hm]
      exact getW_eq_some_iff.mp (hc.regs r hg)
  · show memAfter rsp sa.mem sA'.mem x = sA'.mem x
    simp [memAfter, hx]

/-- The frame words and the array words lie outside the set `T` of addresses. -/
def FootClear (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (T : BitVec 64 → Prop) : Prop :=
  (∀ q a, frame q = some a → ∀ x, InRange8 a x → ¬ T x)
    ∧ ∀ q A n j, slotArr q = some (A, n) → j < n →
        ∀ x, InRange8 (cellAt (base A) j) x → ¬ T x

/-! ## 6. The relaxed relation -/

/-- Two image states agree off the names of `X`: on the other names, the program counter,
    the arrays and the three flags. -/
structure AgreeOff (X : List String) (s s' : LstateMF) : Prop where
  regs : ∀ r, r ∉ X → s.prog.base.reg.lvm r = s'.prog.base.reg.lvm r
  pc : s.prog.base.reg.lpc = s'.prog.base.reg.lpc
  arr : s.prog.base.larr = s'.prog.base.larr
  zf : s.zf = s'.zf
  cf : s.prog.base.cf = s'.prog.base.cf
  of : s.prog.base.of = s'.prog.base.of

/-- **The relaxed relation**: `ImgRel` up to the values of the names in `X`. The image
    state agrees off `X` with a state related to the address state. -/
def ImgRelX (frame : String → Option (BitVec 64)) (slotArr : String → Option (String × Nat))
    (base : String → BitVec 64) (body : Lcmd) (X : List String) (s : LstateMF) (sa : LstateA)
    (zf : Bool) : Prop :=
  ∃ s', AgreeOff X s s' ∧ ImgRel frame slotArr base body s' sa zf

/-- `ImgRel` reads an image state through the components of `AgreeOff []`. -/
theorem imgRel_of_agree {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {s s' : LstateMF} {sa : LstateA} {zf : Bool} (h : AgreeOff [] s s')
    (hrel : ImgRel frame slotArr base body s' sa zf) : ImgRel frame slotArr base body s sa zf where
  pc := hrel.pc.trans h.pc.symm
  regs r hr := (h.regs r (by simp)).trans (hrel.regs r hr)
  slots q a ha := (h.regs q (by simp)).trans (hrel.slots q a ha)
  zf := h.zf.trans hrel.zf
  cf := hrel.cf.trans h.cf.symm
  of := hrel.of.trans h.of.symm
  wid := hrel.wid
  cells q A n hq := by
    obtain ⟨arr, h1, h2⟩ := hrel.cells q A n hq
    exact ⟨arr, by rw [getArr_congr h.arr]; exact h1, h2⟩
  saved := hrel.saved
  reload := hrel.reload
  held := hrel.held

/-- **The relaxed relation with no exempted name is the relation.** -/
theorem imgRelX_nil {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {body : Lcmd}
    {s : LstateMF} {sa : LstateA} {zf : Bool} :
    ImgRelX frame slotArr base body [] s sa zf ↔ ImgRel frame slotArr base body s sa zf :=
  ⟨fun ⟨_, h, hrel⟩ => imgRel_of_agree h hrel,
    fun hrel => ⟨s, ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩, hrel⟩⟩

/-- The names exempted after a call: the general-purpose names the callee does not keep,
    other than the result name. -/
def exempt (c : CalleeSig) : List String :=
  gpList.filter fun r => !c.keep.contains r && r != c.res

/-- Two summary steps of one call agree off the exempted names when their oracles have the
    same flags. -/
theorem agreeOff_callSummary (c : CalleeSig) (ω ω' : CallOut) (s : LstateMF)
    (hz : ω.zf = ω'.zf) (hcf : ω.cf = ω'.cf) (hof : ω.of = ω'.of) :
    AgreeOff (exempt c) (callSummary c ω s) (callSummary c ω' s) := by
  refine ⟨fun r hr => ?_, rfl, rfl, hz, hcf, hof⟩
  show (callRegs c ω s.prog.base.reg).lvm r = (callRegs c ω' s.prog.base.reg).lvm r
  simp only [callRegs]
  split_ifs with h1 h2
  · rfl
  · exfalso
    apply hr
    simp only [clobB, Bool.and_eq_true, Bool.not_eq_true'] at h2
    simp only [exempt, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne]
    exact ⟨mem_gpList h2.1, h2.2, h1⟩
  · rfl

/-! ## 7. A call re-establishes the relations -/

/-- **A call to a specified callee re-establishes the relations.** Let the image state `s`,
    the address state `sa` and the byte state `sA` be related by `ImgRel` and `ACorr`, the
    instruction at the program counter be a call to a callee with `CalleeSpec`, and the
    frame words and the array words lie outside the callee's footprint and the return word
    (`FootClear`). Then the callee halts from its entry state, and for every oracle `ω`,
    after the return: `ACorr` holds for the address state `callA` with the oracle `outOf`;
    `ImgRel` holds for the summary step with that oracle; and the relaxed relation at the
    names `exempt c` holds for the summary step with `ω`. -/
theorem call_reestablishes {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) {q : List RInstr} {c : CalleeSig}
    (hspec : CalleeSpec q c) (hargs : ∀ a ∈ c.args, gpOk a = true) (hres : gpOk c.res = true)
    (hkeep : ∀ r ∈ c.keep, gpOk r = true) {s : LstateMF} {sa : LstateA} {zf : Bool}
    (hrel : ImgRel frame slotArr base body s sa zf) {sA : AState} (hc : ACorr rsp sA sa)
    {bi : Linstr} (hb : body[sa.reg.lpc]? = some bi) {ra : Option String}
    {tgt : String × LLabel} (hbi : bi.li_i = .Lcall ra tgt)
    (hsv : ∀ k R A n, SaveAt body k R → slotArr (slotOfReg R) = some (A, n) →
      sa.reg.lpc < k → R ≠ c.res ∧ clobB c R = false)
    (ret : Nat) (hpre : c.pre (entryOf ret sA))
    (hfoot : FootClear frame slotArr base
      fun x => c.foot (entryOf ret sA) x ∨ InRange8 (retWord sA) x) :
    ∃ sc, HaltsC aMachine q 0 (entryOf ret sA) sc ∧ ∀ ω : CallOut,
      ACorr rsp (retOps.foldl aMachine.exec sc)
          (callA c (outOf (retOps.foldl aMachine.exec sc) ω)
            (memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem) sa)
        ∧ ImgRel frame slotArr base body
            (callSummary c (outOf (retOps.foldl aMachine.exec sc) ω) s)
            (callA c (outOf (retOps.foldl aMachine.exec sc) ω)
              (memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem) sa) ω.zf
        ∧ ImgRelX frame slotArr base body (exempt c) (callSummary c ω s)
            (callA c (outOf (retOps.foldl aMachine.exec sc) ω)
              (memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem) sa) ω.zf := by
  obtain ⟨sc, hrun, hsp, hr, hk, hm⟩ := callSpec_return hspec hargs hres hkeep ret sA hpre
  refine ⟨sc, hrun, fun ω => ?_⟩
  have hmem : ∀ x, ¬ (c.foot (entryOf ret sA) x ∨ InRange8 (retWord sA) x) →
      memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem x = sa.mem x := by
    intro x hx
    unfold memAfter
    split_ifs with hred
    · rfl
    · rw [hm x (fun h => hx (Or.inl h)) (fun h => hx (Or.inr h))]
      exact (hc.mem x hred).symm
  have hI : ImgRel frame slotArr base body
      (callSummary c (outOf (retOps.foldl aMachine.exec sc) ω) s)
      (callA c (outOf (retOps.foldl aMachine.exec sc) ω)
        (memAfter rsp sa.mem (retOps.foldl aMachine.exec sc).mem) sa) ω.zf :=
    imgRel_call hsep c (outOf _ ω) hrel hb hbi hargs hres hsv
      (fun q a ha x hx => hmem x (hfoot.1 q a ha x hx))
      (fun q A n j hq hj x hx => hmem x (hfoot.2 q A n j hq hj x hx))
  exact ⟨acorr_call c ω hc hargs hsp hr hk, hI,
    _, agreeOff_callSummary c ω (outOf _ ω) s rfl rfl rfl, hI⟩

/-! ## 8. The relaxed relation along the instructions after the call -/

/-- **A register instruction on the relaxed relation.** A register instruction that passes
    the gate, whose symbolic description reads no array and no name of `X`, is matched by a
    step of the address machine, and the relaxed relation holds after it at the names of `X`
    the instruction does not write. -/
theorem relX_reg {frame : String → Option (BitVec 64)} {slotArr : String → Option (String × Nat)}
    {base : String → BitVec 64} {rsp : BitVec 64} {body : Lcmd}
    (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateB frame slotArr body = true) (P : LprogM) {X : List String}
    {s t : LstateMF} {sa : LstateA} {zf : Bool}
    (hX : ImgRelX frame slotArr base body X s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) (hc : icase frame bi.li_i = .reg)
    (hg : regGateB frame (normA bi.li_i) = true) {ss : SSt} {gs : List SG}
    (hS : symStep (normA bi.li_i, .reg none) SSt.start = .ok ss gs)
    (hA : descArrFree ss gs = true) (hR : ∀ r ∈ descReads ss gs, r ∉ X)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelX frame slotArr base body (X.filter fun r => !ss.wr.contains r) t sa' t.zf := by
  obtain ⟨s', hag, hrel⟩ := hX
  obtain ⟨t', ht', hwr, hkeep', hkeep, hzf, hcf, hof, hlarr', hlarr, hlpc', hlpc, -⟩ :=
    step_congr P P (normA bi.li_i, .reg none) hS hA s s' t
      (fun r hr => (hag.regs r (hR r hr)).symm) hag.zf.symm hag.cf.symm hag.of.symm hs
  obtain ⟨sa', hst, hr'⟩ := rel_reg hsep hphys (.of_imgGateB hgate) P hrel hb hc hg ht'
  rw [hzf] at hst hr'
  refine ⟨sa', hst, t', ⟨fun r hr => ?_, ?_, ?_, hzf.symm, hcf.symm, hof.symm⟩, hr'⟩
  · by_cases hw : r ∈ ss.wr
    · exact (hwr r hw).symm
    · have hx : r ∉ X := fun hx => hr (by simp [hx, hw])
      rw [hkeep r hw, hkeep' r hw]
      exact hag.regs r hx
  · rw [hlpc, hlpc', hag.pc]
  · rw [hlarr, hlarr', hag.arr]

/-- **The check of an instruction after a call**: the symbolic description of the register
    instruction `x` reads no array and no name of `X`. -/
def readsClearB (X : List String) (x : LinstrR) : Bool :=
  match symStep (x, .reg none) SSt.start with
  | .ok ss gs => descArrFree ss gs && (descReads ss gs).all fun r => !X.contains r
  | _ => false

/-- The exempted names after the register instruction `x`: those of `X` it does not write. -/
def exemptNext (X : List String) (x : LinstrR) : List String :=
  match symStep (x, .reg none) SSt.start with
  | .ok ss _ => X.filter fun r => !ss.wr.contains r
  | _ => X

/-- **A checked register instruction on the relaxed relation.** A register instruction that
    passes the gate and `readsClearB X` is matched by a step of the address machine, and the
    relaxed relation holds after it at `exemptNext X`. -/
theorem relX_reg_checked {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (hgate : imgGateB frame slotArr body = true) (P : LprogM) {X : List String}
    {s t : LstateMF} {sa : LstateA} {zf : Bool}
    (hX : ImgRelX frame slotArr base body X s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) (hc : icase frame bi.li_i = .reg)
    (hg : regGateB frame (normA bi.li_i) = true)
    (hck : readsClearB X (normA bi.li_i) = true)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelX frame slotArr base body (exemptNext X (normA bi.li_i)) t sa' t.zf := by
  unfold readsClearB at hck
  unfold exemptNext
  cases hS : symStep (normA bi.li_i, .reg none) SSt.start with
  | fail => rw [hS] at hck; cases hck
  | unk => rw [hS] at hck; cases hck
  | ok ss gs =>
    rw [hS] at hck
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hck
    exact relX_reg hsep hphys hgate P hX hb hc hg hS hck.1
      (fun r hr hx => by simpa [hx] using hck.2 r hr) hs

/-- **A frame-word load on the relaxed relation.** A load of a frame word into the
    general-purpose name `d` is matched by a step of the address machine, and the relaxed
    relation holds after it at the names of `X` other than `d`. -/
theorem relX_sload {frame : String → Option (BitVec 64)}
    {slotArr : String → Option (String × Nat)} {base : String → BitVec 64} {rsp : BitVec 64}
    {body : Lcmd} (hsep : ImgSep frame slotArr base rsp) (hphys : physImgB slotArr body = true)
    (P : LprogM) {X : List String} {s t : LstateMF} {sa : LstateA} {zf : Bool}
    (hX : ImgRelX frame slotArr base body X s sa zf) {bi : Linstr}
    (hb : body[sa.reg.lpc]? = some bi) {d q : String} (hc : icase frame bi.li_i = .sload d q)
    (hgd : gpOk d = true) (hq : q ∉ X)
    (hs : evalInstrPMemF P (normA bi.li_i, .reg none) s = some t) :
    ∃ sa', fstepA frame (normA bi.li_i, .reg none) sa zf = some (sa', t.zf)
      ∧ ImgRelX frame slotArr base body (X.filter fun r => r != d) t sa' t.zf := by
  obtain ⟨s', hag, hrel⟩ := hX
  have hm := (icase_sload hc).1
  have hn := normA_of_slotMov hm
  have ht' := eval_slotMov P hm (.reg none) s'
  rw [← hn] at ht'
  obtain ⟨sa', hst, hr'⟩ := rel_sload hsep hphys P hrel hb hc hgd ht'
  rw [hn, eval_slotMov P hm] at hs
  cases hs
  refine ⟨sa', ?_, { s' with prog := { s'.prog with
      base := (s'.prog.base.setReg d (s'.prog.base.reg.lvm q).2).nextPc } },
    ⟨fun r hr => ?_, ?_, hag.arr, hag.zf, hag.cf, hag.of⟩, ?_⟩
  · rw [hst]
    exact congrArg (fun z => some (sa', z)) hag.zf.symm
  · have hqe := hag.regs q hq
    show (if r = d then (⟨_, (s.prog.base.reg.lvm q).2⟩ : Σ w, BitVec w)
        else s.prog.base.reg.lvm r)
      = (if r = d then ⟨_, (s'.prog.base.reg.lvm q).2⟩ else s'.prog.base.reg.lvm r)
    by_cases hd : r = d
    · rw [if_pos hd, if_pos hd]
      exact hqe
    · have hx : r ∉ X := fun hx => hr (by simp [hx, hd])
      rw [if_neg hd, if_neg hd]
      exact hag.regs r hx
  · exact congrArg (· + 1) hag.pc
  · show ImgRel frame slotArr base body _ sa' s.zf
    rw [hag.zf]
    exact hr'

end CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe
