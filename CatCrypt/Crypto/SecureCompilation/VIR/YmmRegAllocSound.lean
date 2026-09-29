/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.YmmSelect
public import Std.Data.HashMap

/-!
# Soundness of YMM register allocation and materialization

`YmmRegAlloc.ymmMaterialize` places a program over virtual vector names into
physical registers from a list of decisions: a resident name becomes its
register, a spilled name is reloaded into a scratch register before the
instruction that reads it and stored back after the instruction that writes it.
This module proves the materialized program correct for every decision list
that passes an executable check, whatever produced the decisions.

## The check

`ymmAllocValid decisions scratch out p` computes the live sets of `p` backwards
from the live-out set `out` (`ymmLiveIn`) and checks, at every instruction:

* every name the instruction mentions has a decision;
* the instruction touches at most `scratch.length` distinct spilled names;
* its memory operand, if any, is not a frame cell (base `ymmFrameBase`);
* the location (register or frame cell) of the name it writes differs from the
  location of every other name live after it.

Globally, the scratch registers are distinct and no decision places a name in
a scratch register. Two names may share a register or a frame cell when their
live ranges are disjoint; the interference condition is exactly what makes that
sharing sound, so the check covers linear-scan register reuse and the
frame-cell reuse of `compactSlots` alike.

## The simulation

`AllocRel decisions L sv sp` relates a virtual state `sv` and a physical state
`sp`: they agree on every memory cell off the frame, and every name of `L` has
its virtual value at its location in `sp`. `ymmMaterializeInstr_step` carries
the relation across one instruction, from the live set before it to the live
set after it, and `ymmMaterialize_rel` across the program.

## Main definitions

* `ymmLiveIn`: the names live on entry to a program, given its live-out set.
* `instrAllocOk`, `ymmAllocValid`, `ymmAllocValidClosed`: the check.
* `AllocRel`: the relation between virtual and physical states.

## Main results

* `ymmMaterializeInstr_step`: one materialized instruction preserves `AllocRel`.
* `ymmMaterialize_sound`: a checked allocation's materialized program, started
  in a related state, ends in a state related on the live-out set.
* `ymmMaterialize_sound_closed`: for a program with no live-in and no live-out
  registers, the materialized program ends with the virtual program's memory
  off the frame.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAllocSound

open CatCrypt.Crypto.SecureCompilation.VIR.YmmAsmPrint
open CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.YmmSelect
open CatCrypt.Crypto.SecureCompilation.VIR.YmmDialect
open CatCrypt.Crypto.Optimizer.GenericRegAlloc

/-! ## Liveness and the check -/

/-- The names live before `i` when `L` is live after it. -/
def liveStep (i : YmmInstr) (L : List String) : List String :=
  ymmReadNames i ++ L.filter (fun n => !(ymmWrittenNames i).contains n)

/-- The names live on entry to a program whose live-out set is `out`. -/
def ymmLiveIn (out : List String) : List YmmInstr → List String
  | [] => out
  | i :: rest => liveStep i (ymmLiveIn out rest)

/-- The memory operand of an instruction, if any, is not a frame cell. -/
def memOffFrame : YmmInstr → Bool
  | .yload _ m => m.base != ymmFrameBase
  | .ystore m _ => m.base != ymmFrameBase
  | _ => true

/-- The check at one instruction `i` with `L` live after it. -/
def instrAllocOk (d : List (String × Slot)) (scratch : List String) (i : YmmInstr)
    (L : List String) : Bool :=
  (ymmNamesOf i).all (fun n => (d.lookup n).isSome)
    && decide ((spilledNamesOf d i).length ≤ scratch.length)
    && memOffFrame i
    && (ymmWrittenNames i).all (fun w => L.all (fun n => n == w || d.lookup n != d.lookup w))

/-- No decision places a name in a scratch register. -/
def residentsOffScratch (d : List (String × Slot)) (scratch : List String) : Bool :=
  d.all (fun e => match e.2 with
    | .resident r => !scratch.contains r
    | .spilled _ => true)

/-- The per-instruction check over a program together with its live-in set,
    computed in one backward pass. -/
def allocCheckGo (d : List (String × Slot)) (scratch out : List String) :
    List YmmInstr → Bool × List String
  | [] => (true, out)
  | i :: rest =>
    let r := allocCheckGo d scratch out rest
    (instrAllocOk d scratch i r.2 && r.1, liveStep i r.2)

theorem allocCheckGo_snd (d : List (String × Slot)) (scratch out : List String)
    (p : List YmmInstr) : (allocCheckGo d scratch out p).2 = ymmLiveIn out p := by
  induction p with
  | nil => rfl
  | cons i rest ih => simp [allocCheckGo, ymmLiveIn, ih]

/-! ## The compiled check

`allocCheckGo` looks every name up in the decision list, so one instruction
costs the size of its live set times the length of `d`. `allocCheckGoFast`
computes the same pair with the decisions in a hash map built once, folding
the program from the right. `allocCheckGo_eq_fast` states the equality and is
registered with `@[csimp]`, so compiled code runs the hash-map version while the
proofs keep the list version. `ymmAllocValid` and `ymmAllocValidClosed` are
defined after the registration, so their compiled bodies call the hash-map
version. -/

/-- The decisions as a hash map. The first entry for a name wins, as in
    `List.lookup`. -/
def decisionMap (d : List (String × Slot)) : Std.HashMap String Slot :=
  d.foldr (fun e m => m.insert e.1 e.2) ∅

theorem decisionMap_getElem? (d : List (String × Slot)) (n : String) :
    (decisionMap d)[n]? = d.lookup n := by
  induction d with
  | nil => simp [decisionMap]
  | cons e t ih =>
    obtain ⟨a, b⟩ := e
    simp only [decisionMap, List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getElem?_insert, ih, List.lookup_cons]
    by_cases h : a = n
    · subst h; simp
    · have h1 : (a == n) = false := by simp [h]
      have h2 : (n == a) = false := by simp [Ne.symm h]
      simp [h1, h2]

/-- Whether a looked-up decision is a spill. -/
def isSpilledSlot : Option Slot → Bool
  | some (.spilled _) => true
  | _ => false

/-- `spilledNamesOf` with the decisions given as a lookup function. -/
def spilledNamesBy (look : String → Option Slot) (i : YmmInstr) : List String :=
  ((ymmReadNames i) ++ (ymmWrittenNames i)).eraseDups.filter
    (fun n => isSpilledSlot (look n))

theorem spilledNamesBy_lookup (d : List (String × Slot)) (i : YmmInstr) :
    spilledNamesBy (fun n => d.lookup n) i = spilledNamesOf d i := by
  unfold spilledNamesBy spilledNamesOf
  congr 1
  funext n
  unfold spillSlotOf
  dsimp only
  rcases d.lookup n with _ | (_ | _) <;> rfl

/-- `instrAllocOk` with the decisions given as a lookup function and the
    number of scratch registers. -/
def instrAllocOkBy (look : String → Option Slot) (nScratch : Nat) (i : YmmInstr)
    (L : List String) : Bool :=
  (ymmNamesOf i).all (fun n => (look n).isSome)
    && decide ((spilledNamesBy look i).length ≤ nScratch)
    && memOffFrame i
    && (ymmWrittenNames i).all (fun w => L.all (fun n => n == w || look n != look w))

theorem instrAllocOkBy_lookup (d : List (String × Slot)) (scratch : List String)
    (i : YmmInstr) (L : List String) :
    instrAllocOkBy (fun n => d.lookup n) scratch.length i L
      = instrAllocOk d scratch i L := by
  simp only [instrAllocOkBy, instrAllocOk, spilledNamesBy_lookup]

/-- The check at instruction `i`: from the Boolean result and the live set
    after `i`, the Boolean result and the live set before it. -/
def allocCheckStepBy (look : String → Option Slot) (nScratch : Nat) (i : YmmInstr)
    (r : Bool × List String) : Bool × List String :=
  (instrAllocOkBy look nScratch i r.2 && r.1, liveStep i r.2)

/-- `allocCheckGo` with the decisions given as a lookup function, as a right
    fold over the program. -/
def allocCheckGoBy (look : String → Option Slot) (nScratch : Nat) (out : List String)
    (p : List YmmInstr) : Bool × List String :=
  p.foldr (allocCheckStepBy look nScratch) (true, out)

theorem allocCheckGoBy_lookup (d : List (String × Slot)) (scratch out : List String)
    (p : List YmmInstr) :
    allocCheckGoBy (fun n => d.lookup n) scratch.length out p
      = allocCheckGo d scratch out p := by
  induction p with
  | nil => rfl
  | cons i rest ih =>
    simp only [allocCheckGoBy, List.foldr_cons] at ih ⊢
    rw [ih]
    simp only [allocCheckStepBy, allocCheckGo, instrAllocOkBy_lookup]

/-- `allocCheckGo` over the hash map of the decisions. -/
def allocCheckGoFast (d : List (String × Slot)) (scratch out : List String)
    (p : List YmmInstr) : Bool × List String :=
  let m := decisionMap d
  allocCheckGoBy (fun n => m[n]?) scratch.length out p

/-- The hash-map check computes the list check. -/
@[csimp] theorem allocCheckGo_eq_fast : @allocCheckGo = @allocCheckGoFast := by
  funext d scratch out p
  have hm : (fun n => (decisionMap d)[n]?) = (fun n => d.lookup n) :=
    funext (decisionMap_getElem? d)
  simp only [allocCheckGoFast, hm, allocCheckGoBy_lookup]

/-! ## The check over a program -/

/-- The allocation check: distinct scratch registers, residents off them, and
    `instrAllocOk` at every instruction. -/
def ymmAllocValid (d : List (String × Slot)) (scratch out : List String)
    (p : List YmmInstr) : Bool :=
  decide scratch.Nodup && residentsOffScratch d scratch && (allocCheckGo d scratch out p).1

/-- `ymmAllocValid` with no live-out registers, and no live-in registers. -/
def ymmAllocValidClosed (d : List (String × Slot)) (scratch : List String)
    (p : List YmmInstr) : Bool :=
  let r := allocCheckGo d scratch [] p
  decide scratch.Nodup && residentsOffScratch d scratch && r.1 && r.2.isEmpty

/-! ## The relation -/

/-- The value `v` is at location `s` of the physical state `sp`. -/
def SlotHolds (sp : YmmState) (v : BitVec 256) : Slot → Prop
  | .resident r => sp.regs r = v
  | .spilled off => sp.mem ⟨ymmFrameBase, off⟩ = v

/-- The physical state `sp` agrees with the virtual state `sv` on memory off
    the frame, and holds the value of every name of `L` at its location. -/
def AllocRel (d : List (String × Slot)) (L : List String) (sv sp : YmmState) : Prop :=
  (∀ m : YmmMem, m.base ≠ ymmFrameBase → sp.mem m = sv.mem m) ∧
    ∀ n ∈ L, ∀ s, d.lookup n = some s → SlotHolds sp (sv.regs n) s

/-! ## The materialized instruction, unfolded -/

/-- The scratch register `ymmMaterializeInstr` gives a spilled name. -/
def scrOf (d : List (String × Slot)) (scratch : List String) (i : YmmInstr) (n : String) :
    Option String :=
  ((spilledNamesOf d i).findIdx? (· == n)).bind (fun k => scratch[k]?)

/-- The physical register `ymmMaterializeInstr` renames a name to. -/
def physOf (d : List (String × Slot)) (scratch : List String) (i : YmmInstr) (n : String) :
    String :=
  match residentReg d n with
  | some r => r
  | none => (scrOf d scratch i n).getD n

/-- The reloads `ymmMaterializeInstr` issues before an instruction. -/
def reloadsOf (d : List (String × Slot)) (scratch : List String) (i : YmmInstr) :
    List YmmInstr :=
  (ymmReadNames i).eraseDups.filterMap (fun n =>
    (spillSlotOf d n).bind (fun off =>
      (scrOf d scratch i n).map (fun s => YmmInstr.yload s ⟨ymmFrameBase, off⟩)))

/-- The stores `ymmMaterializeInstr` issues after an instruction. -/
def storesOf (d : List (String × Slot)) (scratch : List String) (i : YmmInstr) :
    List YmmInstr :=
  (ymmWrittenNames i).eraseDups.filterMap (fun n =>
    (spillSlotOf d n).bind (fun off =>
      (scrOf d scratch i n).map (fun s => YmmInstr.ystore ⟨ymmFrameBase, off⟩ s)))

theorem ymmMaterializeInstr_eq (d : List (String × Slot)) (scratch : List String)
    (i : YmmInstr) :
    ymmMaterializeInstr d scratch i
      = reloadsOf d scratch i ++ renameYmm (physOf d scratch i) i :: storesOf d scratch i :=
  rfl

/-! ## Lookups and scratch assignment -/

theorem lookup_mem {d : List (String × Slot)} {n : String} {s : Slot}
    (h : d.lookup n = some s) : (n, s) ∈ d := by
  obtain ⟨l₁, l₂, rfl, _⟩ := List.lookup_eq_some_iff.mp h
  simp

theorem resident_not_scratch {d : List (String × Slot)} {scratch : List String}
    (hres : residentsOffScratch d scratch = true) {n r : String}
    (h : d.lookup n = some (.resident r)) : r ∉ scratch := by
  have := List.all_eq_true.mp hres _ (lookup_mem h)
  simpa using this

theorem spillSlotOf_eq {d : List (String × Slot)} {n : String} {off : Int}
    (h : d.lookup n = some (.spilled off)) : spillSlotOf d n = some off := by
  simp [spillSlotOf, h]

theorem residentReg_eq {d : List (String × Slot)} {n r : String}
    (h : d.lookup n = some (.resident r)) : residentReg d n = some r := by
  simp [residentReg, h]

theorem residentReg_spilled {d : List (String × Slot)} {n : String} {off : Int}
    (h : d.lookup n = some (.spilled off)) : residentReg d n = none := by
  simp [residentReg, h]

theorem spillSlotOf_some {d : List (String × Slot)} {n : String} {off : Int}
    (h : spillSlotOf d n = some off) : d.lookup n = some (.spilled off) := by
  unfold spillSlotOf at h
  split at h <;> simp_all

theorem scrOf_mem {d : List (String × Slot)} {scratch : List String} {i : YmmInstr}
    {n s : String} (h : scrOf d scratch i n = some s) : s ∈ scratch := by
  unfold scrOf at h
  obtain ⟨k, _, hk⟩ := Option.bind_eq_some_iff.mp h
  exact List.mem_of_getElem? hk

theorem scrOf_inj {d : List (String × Slot)} {scratch : List String} {i : YmmInstr}
    (hnd : scratch.Nodup) {n n' s : String}
    (h : scrOf d scratch i n = some s) (h' : scrOf d scratch i n' = some s) : n = n' := by
  unfold scrOf at h h'
  obtain ⟨k, hk, hs⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨k', hk', hs'⟩ := Option.bind_eq_some_iff.mp h'
  have hlt : k < scratch.length := (List.getElem?_eq_some_iff.mp hs).1
  have hkk : k = k' := (List.getElem?_inj hlt hnd).mp (hs.trans hs'.symm)
  subst hkk
  obtain ⟨hlt₁, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hk
  obtain ⟨_, hp', _⟩ := List.findIdx?_eq_some_iff_getElem.mp hk'
  simp only [beq_iff_eq] at hp hp'
  exact hp.symm.trans hp'

theorem scrOf_some {d : List (String × Slot)} {scratch : List String} {i : YmmInstr}
    (hlen : (spilledNamesOf d i).length ≤ scratch.length) {n : String}
    (hn : n ∈ ymmNamesOf i) (hsp : (spillSlotOf d n).isSome) :
    ∃ s, scrOf d scratch i n = some s := by
  have hmem : n ∈ spilledNamesOf d i := by
    simp only [spilledNamesOf, List.mem_filter, List.mem_eraseDups]
    exact ⟨hn, hsp⟩
  have hsome : ((spilledNamesOf d i).findIdx? (· == n)).isSome := by
    rw [List.findIdx?_isSome, List.any_eq_true]
    exact ⟨n, hmem, by simp⟩
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨hlt, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hk
  have hlt' : k < scratch.length := lt_of_lt_of_le hlt hlen
  refine ⟨scratch[k], ?_⟩
  simp [scrOf, hk, hlt']

/-! ## Runs of loads, of stores, and of one renamed instruction -/

theorem run_loads (ls : List YmmInstr) (hl : ∀ x ∈ ls, ∃ r m, x = .yload r m)
    (sp : YmmState) :
    (ymmRun ls sp).mem = sp.mem ∧
      (∀ r, (∀ m, YmmInstr.yload r m ∉ ls) → (ymmRun ls sp).regs r = sp.regs r) ∧
      ∀ r m, YmmInstr.yload r m ∈ ls → (∀ m', YmmInstr.yload r m' ∈ ls → m' = m) →
        (ymmRun ls sp).regs r = sp.mem m := by
  induction ls generalizing sp with
  | nil => simp
  | cons x ls ih =>
    obtain ⟨r₀, m₀, rfl⟩ := hl x (by simp)
    have ih' := ih (fun y hy => hl y (by simp [hy])) (ymmStep (.yload r₀ m₀) sp)
    have hmem : (ymmStep (.yload r₀ m₀) sp).mem = sp.mem := rfl
    refine ⟨by rw [ymmRun_cons, ih'.1, hmem], ?_, ?_⟩
    · intro r hr
      rw [ymmRun_cons, ih'.2.1 r (fun m hm => hr m (by simp [hm]))]
      have : r ≠ r₀ := fun h => hr m₀ (by simp [h])
      simp [ymmStep, YmmState.setReg, this]
    · intro r m hin huniq
      rw [ymmRun_cons]
      by_cases hls : ∃ m', YmmInstr.yload r m' ∈ ls
      · obtain ⟨m', hm'⟩ := hls
        have hmm : m' = m := huniq m' (by simp [hm'])
        subst hmm
        rw [ih'.2.2 r m' hm' (fun m'' h => huniq m'' (by simp [h])), hmem]
      · push Not at hls
        rw [ih'.2.1 r hls]
        have hx : YmmInstr.yload r m = .yload r₀ m₀ := by
          rcases List.mem_cons.mp hin with h | h
          · exact h
          · exact absurd h (hls m)
        injection hx with h1 h2
        subst h1; subst h2
        simp [ymmStep, YmmState.setReg]

theorem aluVal_map (op : YmmOp) (regs : String → BitVec 256) (f : String → String)
    (srcs : List String) :
    aluVal op regs (srcs.map f) = aluVal op (fun a => regs (f a)) srcs := by
  rcases srcs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp [aluVal]

theorem ymmWrittenNames_cases (i : YmmInstr) :
    ymmWrittenNames i = [] ∨ ∃ w, ymmWrittenNames i = [w] := by
  cases i <;> simp [ymmWrittenNames]

/-- An instruction leaves every register it does not write unchanged. -/
theorem ymmStep_regs_of_not_written (i : YmmInstr) (sv : YmmState) (n : String)
    (hn : n ∉ ymmWrittenNames i) : (ymmStep i sv).regs n = sv.regs n := by
  cases i <;> simp_all [ymmStep, ymmWrittenNames, YmmState.setReg, YmmState.setMem]

/-- One instruction renamed by `f`, run from a physical state that holds every
    operand's virtual value at its renamed register and agrees with the virtual
    memory off the frame: it writes the virtual result to the renamed
    destination, leaves every other register and every frame cell unchanged,
    and agrees with the virtual memory off the frame afterwards. -/
theorem rename_step (f : String → String) (i : YmmInstr) (sv sp : YmmState)
    (hread : ∀ n ∈ ymmReadNames i, sp.regs (f n) = sv.regs n)
    (hmem : ∀ m : YmmMem, m.base ≠ ymmFrameBase → sp.mem m = sv.mem m)
    (hoff : memOffFrame i = true) :
    (∀ w ∈ ymmWrittenNames i, (ymmStep (renameYmm f i) sp).regs (f w) = (ymmStep i sv).regs w) ∧
    (∀ r, (∀ w ∈ ymmWrittenNames i, r ≠ f w) →
      (ymmStep (renameYmm f i) sp).regs r = sp.regs r) ∧
    (∀ m : YmmMem, m.base ≠ ymmFrameBase →
      (ymmStep (renameYmm f i) sp).mem m = (ymmStep i sv).mem m) ∧
    (∀ m : YmmMem, m.base = ymmFrameBase → (ymmStep (renameYmm f i) sp).mem m = sp.mem m) := by
  cases i with
  | alu op dst srcs =>
    simp only [ymmReadNames] at hread
    have hv : aluVal op sp.regs (srcs.map f) = aluVal op sv.regs srcs := by
      rw [aluVal_map]; exact aluVal_congr op srcs hread
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp_all [renameYmm, ymmStep, ymmWrittenNames, YmmState.setReg]
  | ymov dst src =>
    simp only [ymmReadNames] at hread
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp_all [renameYmm, ymmStep, ymmWrittenNames, YmmState.setReg]
  | yload dst m₀ =>
    have hb : m₀.base ≠ ymmFrameBase := by simpa [memOffFrame] using hoff
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp_all [renameYmm, ymmStep, ymmWrittenNames, YmmState.setReg]
  | ystore m₀ src =>
    simp only [ymmReadNames] at hread
    have hb : m₀.base ≠ ymmFrameBase := by simpa [memOffFrame] using hoff
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [ymmWrittenNames]
    · intro r _; rfl
    · intro m hm
      simp only [renameYmm, ymmStep, YmmState.setMem]
      split_ifs <;> simp_all
    · intro m hm
      simp only [renameYmm, ymmStep, YmmState.setMem]
      rw [if_neg]
      rintro ⟨h1, _⟩
      exact hb (h1 ▸ hm)
  | ternlog imm dst b c =>
    simp only [ymmReadNames, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hread
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp_all [renameYmm, ymmStep, ymmWrittenNames, YmmState.setReg]

/-! ## One instruction -/

/-- **One materialized instruction preserves the relation.** If the check holds
    at `i` with `L` live after it, a physical state related to the virtual one
    on the names live before `i` is taken by `ymmMaterializeInstr` to a state
    related to `ymmStep i` of the virtual one on `L`. -/
theorem ymmMaterializeInstr_step (d : List (String × Slot)) (scratch : List String)
    (i : YmmInstr) (L : List String) (sv sp : YmmState)
    (hnd : scratch.Nodup) (hres : residentsOffScratch d scratch = true)
    (hok : instrAllocOk d scratch i L = true)
    (hrel : AllocRel d (liveStep i L) sv sp) :
    AllocRel d L (ymmStep i sv) (ymmRun (ymmMaterializeInstr d scratch i) sp) := by
  simp only [instrAllocOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Option.isSome_iff_exists] at hok
  obtain ⟨⟨⟨hloc, hlen⟩, hoff⟩, hint⟩ := hok
  have hint' : ∀ w ∈ ymmWrittenNames i, ∀ n ∈ L, n ≠ w → d.lookup n ≠ d.lookup w := by
    intro w hw n hn hne
    have := hint w hw n hn
    simpa [hne] using this
  rw [ymmMaterializeInstr_eq, ymmRun_append, ymmRun_cons]
  -- the reloads
  have hrl : ∀ x ∈ reloadsOf d scratch i, ∃ s off n, n ∈ ymmReadNames i ∧
      spillSlotOf d n = some off ∧ scrOf d scratch i n = some s ∧
      x = .yload s ⟨ymmFrameBase, off⟩ := by
    intro x hx
    simp only [reloadsOf, List.mem_filterMap, Option.bind_eq_some_iff,
      Option.map_eq_some_iff, List.mem_eraseDups] at hx
    obtain ⟨n, hn, off, hoff', s, hs, rfl⟩ := hx
    exact ⟨s, off, n, hn, hoff', hs, rfl⟩
  obtain ⟨h1mem, h1keep, h1load⟩ := run_loads (reloadsOf d scratch i)
    (fun x hx => by obtain ⟨s, off, _, _, _, _, rfl⟩ := hrl x hx; exact ⟨_, _, rfl⟩) sp
  set sp1 := ymmRun (reloadsOf d scratch i) sp with hsp1
  have h1keep' : ∀ r, r ∉ scratch → sp1.regs r = sp.regs r := by
    intro r hr
    apply h1keep
    intro m hm
    obtain ⟨s, off, n, _, _, hs, hx⟩ := hrl _ hm
    injection hx with h _
    exact hr (h ▸ scrOf_mem hs)
  have hnames_r : ∀ n ∈ ymmReadNames i, n ∈ ymmNamesOf i := fun n hn => by
    simp [ymmNamesOf, hn]
  have hnames_w : ∀ n ∈ ymmWrittenNames i, n ∈ ymmNamesOf i := fun n hn => by
    simp [ymmNamesOf, hn]
  have hread : ∀ n ∈ ymmReadNames i, sp1.regs (physOf d scratch i n) = sv.regs n := by
    intro n hn
    obtain ⟨sl, hsl⟩ := hloc n (hnames_r n hn)
    have hold := hrel.2 n (by simp [liveStep, hn]) sl hsl
    cases sl with
    | resident r =>
      simp only [physOf, residentReg_eq hsl]
      rw [h1keep' r (resident_not_scratch hres hsl)]
      exact hold
    | spilled off =>
      obtain ⟨s, hs⟩ := scrOf_some hlen (hnames_r n hn) (by simp [spillSlotOf_eq hsl])
      simp only [physOf, residentReg_spilled hsl, hs, Option.getD_some]
      rw [h1load s ⟨ymmFrameBase, off⟩ ?_ ?_]
      · exact hold
      · simp only [reloadsOf, List.mem_filterMap, Option.bind_eq_some_iff,
          Option.map_eq_some_iff, List.mem_eraseDups]
        exact ⟨n, hn, off, spillSlotOf_eq hsl, s, hs, rfl⟩
      · intro m' hm'
        obtain ⟨s', off', n', _, hoff', hs', hx⟩ := hrl _ hm'
        injection hx with h1 h2
        subst h1
        have hnn : n = n' := scrOf_inj hnd hs hs'
        subst hnn
        rw [spillSlotOf_eq hsl] at hoff'
        injection hoff' with h
        rw [h2, h]
  have hmem1 : ∀ m : YmmMem, m.base ≠ ymmFrameBase → sp1.mem m = sv.mem m := by
    intro m hm; rw [h1mem]; exact hrel.1 m hm
  obtain ⟨h2w, h2keep, h2mem, h2frame⟩ :=
    rename_step (physOf d scratch i) i sv sp1 hread hmem1 hoff
  set sp2 := ymmStep (renameYmm (physOf d scratch i) i) sp1 with hsp2
  -- the physical register of a name with a location
  have hphys_res : ∀ n r, d.lookup n = some (.resident r) → physOf d scratch i n = r := by
    intro n r h; simp [physOf, residentReg_eq h]
  have hphys_sp : ∀ n off s, d.lookup n = some (.spilled off) →
      scrOf d scratch i n = some s → physOf d scratch i n = s := by
    intro n off s h hs; simp [physOf, residentReg_spilled h, hs]
  rcases ymmWrittenNames_cases i with hw | ⟨w, hw⟩
  · -- no register written: no stores
    have hst : storesOf d scratch i = [] := by simp [storesOf, hw]
    rw [hst, ymmRun_nil]
    refine ⟨h2mem, ?_⟩
    intro n hn sl hsl
    have hlive : n ∈ liveStep i L := by simp [liveStep, hw, hn]
    have hold := hrel.2 n hlive sl hsl
    rw [ymmStep_regs_of_not_written i sv n (by simp [hw])]
    cases sl with
    | resident r =>
      show sp2.regs r = _
      rw [h2keep r (by simp [hw]), h1keep' r (resident_not_scratch hres hsl)]
      exact hold
    | spilled off =>
      show sp2.mem _ = _
      rw [h2frame _ rfl, h1mem]
      exact hold
  · -- one register `w` written
    obtain ⟨slw, hslw⟩ := hloc w (hnames_w w (by simp [hw]))
    have hwmem : w ∈ ymmWrittenNames i := by simp [hw]
    cases slw with
    | resident rw =>
      have hst : storesOf d scratch i = [] := by
        simp [storesOf, hw, spillSlotOf, hslw]
      rw [hst, ymmRun_nil]
      refine ⟨h2mem, ?_⟩
      intro n hn sl hsl
      by_cases hnw : n = w
      · subst hnw
        rw [hslw] at hsl
        injection hsl with hsl; subst hsl
        show sp2.regs rw = _
        rw [← hphys_res n rw hslw]
        exact h2w n hwmem
      · have hlive : n ∈ liveStep i L := by simp [liveStep, hw, hn, hnw]
        have hold := hrel.2 n hlive sl hsl
        rw [ymmStep_regs_of_not_written i sv n (by simp [hw, hnw])]
        have hne := hint' w hwmem n hn hnw
        cases sl with
        | resident r =>
          show sp2.regs r = _
          rw [h2keep r ?_, h1keep' r (resident_not_scratch hres hsl)]
          · exact hold
          · intro w' hw'
            have : w' = w := by simpa [hw] using hw'
            subst this
            rw [hphys_res w' rw hslw]
            intro hrr; subst hrr
            exact hne (hsl.trans hslw.symm)
        | spilled off =>
          show sp2.mem _ = _
          rw [h2frame _ rfl, h1mem]
          exact hold
    | spilled offw =>
      obtain ⟨s, hs⟩ := scrOf_some hlen (hnames_w w hwmem) (by simp [spillSlotOf_eq hslw])
      have hst : storesOf d scratch i = [.ystore ⟨ymmFrameBase, offw⟩ s] := by
        simp only [storesOf, hw]
        show List.filterMap _ [w] = _
        simp [spillSlotOf_eq hslw, hs]
      rw [hst, ymmRun_cons, ymmRun_nil]
      have hpw : physOf d scratch i w = s := hphys_sp w offw s hslw hs
      refine ⟨?_, ?_⟩
      · intro m hm
        simp only [ymmStep, YmmState.setMem]
        rw [if_neg (fun h => hm h.1)]
        exact h2mem m hm
      · intro n hn sl hsl
        by_cases hnw : n = w
        · subst hnw
          rw [hslw] at hsl
          injection hsl with hsl; subst hsl
          show (sp2.setMem _ _).mem _ = _
          simp only [YmmState.setMem, and_self, if_true]
          rw [← hpw]
          exact h2w n hwmem
        · have hlive : n ∈ liveStep i L := by simp [liveStep, hw, hn, hnw]
          have hold := hrel.2 n hlive sl hsl
          rw [ymmStep_regs_of_not_written i sv n (by simp [hw, hnw])]
          have hne := hint' w hwmem n hn hnw
          cases sl with
          | resident r =>
            show (sp2.setMem _ _).regs r = _
            simp only [YmmState.setMem]
            rw [h2keep r ?_, h1keep' r (resident_not_scratch hres hsl)]
            · exact hold
            · intro w' hw'
              have : w' = w := by simpa [hw] using hw'
              subst this
              rw [hpw]
              intro hrs; subst hrs
              exact resident_not_scratch hres hsl (scrOf_mem hs)
          | spilled off =>
            show (sp2.setMem _ _).mem _ = _
            simp only [YmmState.setMem]
            rw [if_neg, h2frame _ rfl, h1mem]
            · exact hold
            · rintro ⟨_, hd⟩
              exact hne (by rw [hsl, hslw, hd])

/-! ## The program -/

/-- **The simulation over a program.** A checked allocation's materialized
    program, run from a state related to the virtual one on the live-in set,
    ends in a state related to the virtual final state on the live-out set. -/
theorem ymmMaterialize_rel (d : List (String × Slot)) (scratch out : List String)
    (hnd : scratch.Nodup) (hres : residentsOffScratch d scratch = true) :
    ∀ (p : List YmmInstr) (sv sp : YmmState), (allocCheckGo d scratch out p).1 = true →
      AllocRel d (ymmLiveIn out p) sv sp →
      AllocRel d out (ymmRun p sv) (ymmRun (ymmMaterialize d scratch p) sp) := by
  intro p
  induction p with
  | nil => intro sv sp _ h; exact h
  | cons i rest ih =>
    intro sv sp hchk hrel
    simp only [allocCheckGo, Bool.and_eq_true, allocCheckGo_snd] at hchk
    rw [ymmMaterialize, List.flatMap_cons, ymmRun_append, ymmRun_cons]
    exact ih _ _ hchk.2 (ymmMaterializeInstr_step d scratch i _ sv sp hnd hres hchk.1 hrel)

/-- **Soundness of materialization.** For any program `p` and any decisions and
    scratch registers passing `ymmAllocValid`, running `ymmMaterialize` from a
    physical state related to the virtual state on the live-in names ends in a
    state related to the virtual final state on the live-out names `out`: equal
    memory off the frame, and each live-out name's value at its location. -/
theorem ymmMaterialize_sound (d : List (String × Slot)) (scratch out : List String)
    (p : List YmmInstr) (h : ymmAllocValid d scratch out p = true) (sv sp : YmmState)
    (hrel : AllocRel d (ymmLiveIn out p) sv sp) :
    AllocRel d out (ymmRun p sv) (ymmRun (ymmMaterialize d scratch p) sp) := by
  simp only [ymmAllocValid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ymmMaterialize_rel d scratch out h.1.1 h.1.2 p sv sp h.2 hrel

/-- **Soundness of materialization for a closed program.** For decisions and
    scratch registers passing `ymmAllocValidClosed`, the materialized program
    and the virtual program, started in states that agree on memory off the
    frame, end in states that agree on memory off the frame. -/
theorem ymmMaterialize_sound_closed (d : List (String × Slot)) (scratch : List String)
    (p : List YmmInstr) (h : ymmAllocValidClosed d scratch p = true) (sv sp : YmmState)
    (hmem : ∀ m : YmmMem, m.base ≠ ymmFrameBase → sp.mem m = sv.mem m) :
    ∀ m : YmmMem, m.base ≠ ymmFrameBase →
      (ymmRun (ymmMaterialize d scratch p) sp).mem m = (ymmRun p sv).mem m := by
  simp only [ymmAllocValidClosed, Bool.and_eq_true, decide_eq_true_eq,
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨hnd, hres⟩, hchk⟩, hnil⟩ := h
  rw [allocCheckGo_snd] at hnil
  refine (ymmMaterialize_rel d scratch [] hnd hres p sv sp hchk ⟨hmem, ?_⟩).1
  intro n hn
  rw [hnil] at hn
  cases hn

end CatCrypt.Crypto.SecureCompilation.VIR.YmmRegAllocSound
