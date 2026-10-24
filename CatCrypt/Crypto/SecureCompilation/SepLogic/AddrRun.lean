/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.SepLogic.AddrState
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun

/-!
# Write footprint and read locality of a run of the address machine

A step of the address machine on a body (`JasminLsemAddrRun.stepA`) is `fstepA` at an `Lopn`
and a move of the program counter at a label or a conditional branch. `stepWrites frame c s`
is the write footprint of the step at the program counter of `s`: `writesA` of the
instruction at an `Lopn`, the program counter otherwise. `stepReads frame c s` is its read
footprint: `readsA` at an `Lopn`, the program counter and the zero flag otherwise.

`runWrites frame c n s zf` and `runReads frame c n s zf` are the unions of these footprints
over the steps that the run `runA frame c n s zf` executes, each at the state the run holds
at that step; the read footprint always holds the program counter, which decides whether the
run halts.

## Main definitions

* `Addr.LocRel`: two results that agree on a write set and agree with their starts outside
  it.
* `Addr.stepWrites`, `Addr.stepReads`, `Addr.runWrites`, `Addr.runReads`.

## Main results

* `Addr.stepA_local`, `Addr.stepA_writesIn`: read locality and write footprint of a step.
* `Addr.runA_local`, `Addr.runA_writesIn`, `Addr.runA_frame`: read locality and write
  footprint of a run, and the frame rule for a run.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.SepLogic.Addr

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrCongr (ORel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (write64)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (LstateN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemStepFrame (dstNames)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (opNames)
open Footprinted SAssert

/-- The results `p`, `q` of two runs from `s₀`, `t₀` agree on `W`, and each agrees with its
    start outside `W`. -/
def LocRel (W : Set Loc) (s₀ t₀ p q : LstateA × Bool) : Prop :=
  AgreeOn W p q ∧ AgreeOn Wᶜ s₀ p ∧ AgreeOn Wᶜ t₀ q

theorem LocRel.empty (s₀ t₀ : LstateA × Bool) : LocRel ∅ s₀ t₀ s₀ t₀ :=
  ⟨fun _ h => absurd h (Set.notMem_empty _), agreeOn_refl _ _, agreeOn_refl _ _⟩

/-- Sequencing: results related on `W` followed by results related on `V` are related on
    `W ∪ V`. -/
theorem LocRel.seq {W V : Set Loc} {s₀ t₀ p q a b : LstateA × Bool} (h₁ : LocRel W s₀ t₀ p q)
    (h₂ : LocRel V p q a b) : LocRel (W ∪ V) s₀ t₀ a b := by
  obtain ⟨h11, h12, h13⟩ := h₁
  obtain ⟨h21, h22, h23⟩ := h₂
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · by_cases hv : l ∈ V
    · exact h21 l hv
    · rcases hl with hw | hv'
      · exact (h22 l hv).symm.trans ((h11 l hw).trans (h23 l hv))
      · exact absurd hv' hv
  · exact (h12 l fun h => hl (Or.inl h)).trans (h22 l fun h => hl (Or.inr h))
  · exact (h13 l fun h => hl (Or.inl h)).trans (h23 l fun h => hl (Or.inr h))

/-! ## One step on a body -/

/-- The write footprint of the step of the body `c` at the program counter of `s`. -/
def stepWrites (frame : String → Option (BitVec 64)) (c : Lcmd) (s : LstateA) : Set Loc :=
  match c[s.reg.lpc]? with
  | some ⟨_, .Lopn ds o ss⟩ =>
      writesA frame (normA (.Lopn ds o ss), tagAt c s.reg.lpc (.Lopn ds o ss)) s
  | _ => {.pc}

/-- The read footprint of the step of the body `c` at the program counter of `s`. -/
def stepReads (frame : String → Option (BitVec 64)) (c : Lcmd) (s : LstateA) : Set Loc :=
  match c[s.reg.lpc]? with
  | some ⟨_, .Lopn ds o ss⟩ =>
      readsA frame (normA (.Lopn ds o ss), tagAt c s.reg.lpc (.Lopn ds o ss)) s
  | _ => {l | l = .pc ∨ l = .flag .zf}

theorem pc_mem_stepReads (frame : String → Option (BitVec 64)) (c : Lcmd) (s : LstateA) :
    Loc.pc ∈ stepReads frame c s := by
  unfold stepReads
  split
  · exact trivial
  · exact Or.inl rfl

/-- Setting the program counter writes only the program counter. -/
theorem locRel_setLpc (s t : LstateA) (zf : Bool) (n : Nat) :
    LocRel {.pc} (s, zf) (t, zf) (s.setLpc n, zf) (t.setLpc n, zf) := by
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · rw [Set.mem_singleton_iff] at hl
    subst hl
    rfl
  all_goals
    cases l with
    | pc => exact absurd rfl hl
    | _ => rfl

/-- **Read locality of a step.** Two states that agree on the read footprint of the step at
    `s` both step or both fail; the results agree on the write footprint and each agrees with
    its start outside it. -/
theorem stepA_local (frame : String → Option (BitVec 64)) (c : Lcmd) {s t : LstateA}
    {zf zt : Bool} (h : AgreeOn (stepReads frame c s) (s, zf) (t, zt)) :
    ORel (LocRel (stepWrites frame c s) (s, zf) (t, zt)) (stepA frame c s zf)
      (stepA frame c t zt) := by
  have hpc : s.reg.lpc = t.reg.lpc := h _ (pc_mem_stepReads frame c s)
  unfold stepA stepWrites
  unfold stepReads at h
  rw [← hpc]
  cases hc : c[s.reg.lpc]? with
  | none => exact ORel.none
  | some x =>
    rw [hc] at h
    obtain ⟨ii, x⟩ := x
    cases x with
    | Lopn ds o ss => exact fstepA_local frame _ h
    | Llabel k l =>
      have hz : zf = zt := h (.flag .zf) (Or.inr rfl)
      subst hz
      exact ORel.some (locRel_setLpc s t zf _)
    | Lcond cond l =>
      have hz : zf = zt := h (.flag .zf) (Or.inr rfl)
      subst hz
      cases cond with
      | reg cc =>
        simp only
        cases condPol cc with
        | none => exact ORel.none
        | some pol =>
          simp only
          split
          · cases labelAt c l with
            | none => exact ORel.none
            | some p => exact ORel.some (locRel_setLpc s t zf _)
          · exact ORel.some (locRel_setLpc s t zf _)
      | _ => exact ORel.none
    | _ => exact ORel.none

/-- **The write footprint of a step.** -/
theorem stepA_writesIn (frame : String → Option (BitVec 64)) (c : Lcmd) {s : LstateA}
    {zf : Bool} {p : LstateA × Bool} (h : stepA frame c s zf = some p) :
    AgreeOn (stepWrites frame c s)ᶜ (s, zf) p := by
  have hl := stepA_local frame c (agreeOn_refl (stepReads frame c s) (s, zf))
  rw [h] at hl
  cases hl with
  | some hr => exact hr.2.1

/-! ## Runs -/

/-- The union of the write footprints of the steps the run of `c` from `s` executes within
    `n` steps. -/
def runWrites (frame : String → Option (BitVec 64)) (c : Lcmd) :
    Nat → LstateA → Bool → Set Loc
  | 0, _, _ => ∅
  | n + 1, s, zf =>
      if haltedA c s then ∅
      else stepWrites frame c s ∪
        match stepA frame c s zf with
        | some p => runWrites frame c n p.1 p.2
        | none => ∅

/-- The program counter and the union of the read footprints of the steps the run of `c`
    from `s` executes within `n` steps. -/
def runReads (frame : String → Option (BitVec 64)) (c : Lcmd) :
    Nat → LstateA → Bool → Set Loc
  | 0, _, _ => {.pc}
  | n + 1, s, zf =>
      if haltedA c s then {.pc}
      else stepReads frame c s ∪
        match stepA frame c s zf with
        | some p => runReads frame c n p.1 p.2
        | none => ∅

theorem pc_mem_runReads (frame : String → Option (BitVec 64)) (c : Lcmd) :
    ∀ (n : Nat) (s : LstateA) (zf : Bool), Loc.pc ∈ runReads frame c n s zf
  | 0, _, _ => rfl
  | n + 1, s, zf => by
    unfold runReads
    split
    · rfl
    · exact Or.inl (pc_mem_stepReads frame c s)

theorem haltedA_congr {c : Lcmd} {s t : LstateA} (h : s.reg.lpc = t.reg.lpc) :
    haltedA c t = haltedA c s := by
  unfold haltedA
  rw [h]

/-- **Read locality of a run.** Two states that agree on the read footprint of the run of
    `c` from `s` both halt within `n` steps or neither does; the final states agree on the
    write footprint of the run and each agrees with its start outside it. -/
theorem runA_local (frame : String → Option (BitVec 64)) (c : Lcmd) :
    ∀ (n : Nat) (s t : LstateA) (zf zt : Bool),
      AgreeOn (runReads frame c n s zf) (s, zf) (t, zt) →
      ORel (LocRel (runWrites frame c n s zf) (s, zf) (t, zt)) (runA frame c n s zf)
        (runA frame c n t zt) := by
  intro n
  induction n with
  | zero =>
    intro s t zf zt h
    have hh := haltedA_congr (c := c) (h _ (pc_mem_runReads frame c 0 s zf))
    unfold runA
    rw [hh]
    split
    · exact ORel.some ⟨fun _ hl => absurd hl (Set.notMem_empty _),
        agreeOn_refl _ _, agreeOn_refl _ _⟩
    · exact ORel.none
  | succ n ih =>
    intro s t zf zt h
    have hh := haltedA_congr (c := c) (h _ (pc_mem_runReads frame c (n + 1) s zf))
    cases hs : haltedA c s with
    | true =>
      rw [runA_halt frame c _ s zf hs, runA_halt frame c _ t zt (hh.trans hs)]
      unfold runWrites
      rw [if_pos hs]
      exact ORel.some ⟨fun _ hl => absurd hl (Set.notMem_empty _),
        agreeOn_refl _ _, agreeOn_refl _ _⟩
    | false =>
      rw [runA_step frame c _ s zf hs, runA_step frame c _ t zt (hh.trans hs)]
      unfold runWrites
      unfold runReads at h
      rw [if_neg (by simp [hs])] at h ⊢
      have hS := stepA_local frame c (agreeOn_anti Set.subset_union_left h)
      revert h hS
      cases stepA frame c s zf <;> cases stepA frame c t zt <;> intro h hS
      · exact ORel.none
      · cases hS
      · cases hS
      rename_i p q
      cases hS with
      | some hpq =>
      have hR : AgreeOn (runReads frame c n p.1 p.2) p q := by
        intro l hl
        by_cases hw : l ∈ stepWrites frame c s
        · exact hpq.1 l hw
        · exact (hpq.2.1 l hw).symm.trans ((h l (Or.inr hl)).trans (hpq.2.2 l hw))
      exact (ih p.1 q.1 p.2 q.2 hR).mono fun a b hab => hpq.seq hab

/-- **The write footprint of a run.** A run that halts within `n` steps ends in a state that
    agrees with its start outside `runWrites`. -/
theorem runA_writesIn (frame : String → Option (BitVec 64)) (c : Lcmd) {n : Nat} {s : LstateA}
    {zf : Bool} {p : LstateA × Bool} (h : runA frame c n s zf = some p) :
    AgreeOn (runWrites frame c n s zf)ᶜ (s, zf) p := by
  have hl := runA_local frame c n s s zf zf (agreeOn_refl _ _)
  rw [h] at hl
  cases hl with
  | some hr => exact hr.2.1

/-- **The frame rule for a run.** A run that halts preserves every assertion whose footprint
    avoids the run's write footprint. -/
theorem runA_frame (frame : String → Option (BitVec 64)) (c : Lcmd) {n : Nat} {s : LstateA}
    {zf : Bool} {p : LstateA × Bool} (h : runA frame c n s zf = some p)
    (R : SAssert (LstateA × Bool) Loc) (hd : Disjoint R.fp (runWrites frame c n s zf))
    (hR : R.holds (s, zf)) : R.holds p :=
  R.supp _ _ (agreeOn_anti (fun _ hl hw => Set.disjoint_left.1 hd hl hw)
    (runA_writesIn frame c h)) hR

/-! ## A cell store followed by a register move -/

/-- The body `MOV:64 mem.B.0, V; MOV:64 D, S`: a store of `V` into the cell at `B`, then a
    move of `S` into `D`. -/
def storeMoveBody : Lcmd :=
  [⟨0, .Lopn [.reg "mem.B.0"] "MOV:64" [.reg "V"]⟩, ⟨1, .Lopn [.reg "D"] "MOV:64" [.reg "S"]⟩]

/-- The first step of `storeMoveBody` stores the value of `V` at the address in `B`. -/
theorem stepA_storeMoveBody_zero {s : LstateA} (zf : Bool) (hpc : s.reg.lpc = 0)
    {p v : BitVec 64} (hB : s.reg.getW "B" 64 = some p) (hV : s.reg.getW "V" 64 = some v) :
    stepA (fun _ => none) storeMoveBody s zf
      = some (⟨s.reg.nextPc, write64 s.mem (p + BitVec.ofNat 64 0) v, s.cf, s.of⟩, zf) := by
  have hn : cellParts? "mem.B.0" = some ("B", 0) := by decide
  unfold stepA
  rw [hpc]
  simp only [storeMoveBody, List.getElem?_cons_zero]
  rw [tagAt_of_ne (by simp [JasminLsemCast.movImmStruct?]),
    tagA_lopn (by decide) (by decide)]
  simp only [normA, castTagW]
  simp (config := { decide := true }) only [if_false]
  exact fstepA_movStm _ hn hB hV zf

/-- The second step of `storeMoveBody` moves the value of `S` into `D`. -/
theorem stepA_storeMoveBody_one {s : LstateA} (zf : Bool) (hpc : s.reg.lpc = 1) :
    stepA (fun _ => none) storeMoveBody s zf
      = some (⟨(s.reg.setReg "D" (s.reg.lvm "S").2).nextPc, s.mem, s.cf, s.of⟩, zf) := by
  have hD : cellParts? "D" = none := by decide
  have hS : cellParts? "S" = none := by decide
  have hu : X86Backend.LprogAsmPrinter.untagCaret "MOV:64" = "MOV:64" :=
    X86Backend.LprogAsmPrinter.untagCaret_of_caret_free (by decide)
  unfold stepA
  rw [hpc]
  simp only [storeMoveBody, List.getElem?_cons_succ, List.getElem?_cons_zero]
  rw [tagAt_of_ne (by simp [JasminLsemCast.movImmStruct?]),
    tagA_lopn (by decide) (by decide)]
  simp (config := { decide := true }) [normA, hu, fstepA, slotMov?_mov64 hD hS,
    regStepA, JasminLsemMemFlagNestJoin.fstepF, JasminLsemMemFlagGuard.cmpArgs?,
    JasminLsemMemFlagGuard.movRegArgs?, JasminLsemWidthN.readReg, LstateM.setReg,
    LstateM.nextPc]

/-- The write footprint of two steps of `storeMoveBody` from the first instruction: the cell
    name and `D`, the program counter, the flags, and the eight bytes at the address in `B`. -/
theorem runWrites_storeMoveBody {s : LstateA} (zf : Bool) (hpc : s.reg.lpc = 0)
    {p v : BitVec 64} (hB : s.reg.getW "B" 64 = some p) (hV : s.reg.getW "V" 64 = some v) :
    runWrites (fun _ => none) storeMoveBody 2 s zf = (fun l => match l with
      | .reg r => r = "mem.B.0" ∨ r = "D"
      | .pc => True
      | .flag _ => True
      | .mem x => x ∈ (⟨p + BitVec.ofNat 64 0, 8⟩ : Rng 64) : Set Loc) := by
  have hn : cellParts? "mem.B.0" = some ("B", 0) := by decide
  have hD : cellParts? "D" = none := by decide
  have hS : cellParts? "S" = none := by decide
  have hu : X86Backend.LprogAsmPrinter.untagCaret "MOV:64" = "MOV:64" :=
    X86Backend.LprogAsmPrinter.untagCaret_of_caret_free (by decide)
  have hstep := stepA_storeMoveBody_zero zf hpc hB hV
  have hstep2 := stepA_storeMoveBody_one (s := ⟨s.reg.nextPc,
    write64 s.mem (p + BitVec.ofNat 64 0) v, s.cf, s.of⟩) zf
    (by simp [JasminLsemWidthN.LstateN.nextPc, hpc])
  rw [runWrites, if_neg (by simp [haltedA, hpc, storeMoveBody]), hstep]
  simp only
  rw [runWrites, if_neg (by simp [haltedA, hpc, storeMoveBody]), hstep2]
  have w1 : stepWrites (fun _ => none) storeMoveBody s
      = writesA (fun _ => none) (.Lopn [.reg "mem.B.0"] "MOV:64" [.reg "V"], .reg none) s := by
    unfold stepWrites
    rw [hpc]
    simp only [storeMoveBody, List.getElem?_cons_zero]
    rw [tagAt_of_ne (by simp [JasminLsemCast.movImmStruct?]),
      tagA_lopn (by decide) (by decide)]
    simp (config := { decide := true }) [normA, hu, castTagW]
  have w2 : ∀ t : LstateA, t.reg.lpc = 1 → stepWrites (fun _ => none) storeMoveBody t
      = writesA (fun _ => none) (.Lopn [.reg "D"] "MOV:64" [.reg "S"], .reg none) t := by
    intro t ht
    unfold stepWrites
    rw [ht]
    simp only [storeMoveBody, List.getElem?_cons_succ, List.getElem?_cons_zero]
    rw [tagAt_of_ne (by simp [JasminLsemCast.movImmStruct?]),
      tagA_lopn (by decide) (by decide)]
    simp (config := { decide := true }) [normA, hu, castTagW]
  have s1 : storeA? (fun _ => none) (.Lopn [.reg "mem.B.0"] "MOV:64" [.reg "V"], .reg none)
      s.reg = some (p + BitVec.ofNat 64 0) := by
    simp [storeA?, slotMov?, slotCmp?, cellA?, hn, hB, hu]
  have s2 : ∀ r : LstateN,
      storeA? (fun _ => none) (.Lopn [.reg "D"] "MOV:64" [.reg "S"], .reg none) r = none := by
    intro r
    simp [storeA?, slotMov?_mov64 hD hS]
  have r1 : storeR? (fun _ => none) (.Lopn [.reg "mem.B.0"] "MOV:64" [.reg "V"], .reg none)
      s.reg = some ⟨p + BitVec.ofNat 64 0, 8⟩ := by
    simp [storeR?, s1]
  have r2 : ∀ r : LstateN,
      storeR? (fun _ => none) (.Lopn [.reg "D"] "MOV:64" [.reg "S"], .reg none) r = none := by
    intro r
    simp [storeR?, s2]
  rw [w1, w2 _ (by simp [JasminLsemWidthN.LstateN.nextPc, hpc])]
  simp only [runWrites, Set.union_empty]
  ext l
  cases l with
  | reg r =>
    show (r ∈ dstNames (.Lopn [.reg "mem.B.0"] "MOV:64" [.reg "V"]) ∨
      r ∈ dstNames (.Lopn [.reg "D"] "MOV:64" [.reg "S"])) ↔ (r = "mem.B.0" ∨ r = "D")
    simp [dstNames, opNames]
  | pc => exact ⟨fun _ => trivial, fun _ => Or.inl trivial⟩
  | flag f => exact ⟨fun _ => trivial, fun _ => Or.inl trivial⟩
  | mem x =>
    show ((∃ R, storeR? (fun _ => none) (.Lopn [.reg "mem.B.0"] "MOV:64" [.reg "V"], .reg none)
        s.reg = some R ∧ x ∈ R) ∨
      (∃ R, storeR? (fun _ => none) (.Lopn [.reg "D"] "MOV:64" [.reg "S"], .reg none)
        s.reg.nextPc = some R ∧ x ∈ R)) ↔ x ∈ (⟨p + BitVec.ofNat 64 0, 8⟩ : Rng 64)
    rw [r1, r2]
    simp

/-- **Non-vacuity of the frame rule for a run.** Two steps of `storeMoveBody` from the first
    instruction halt, and an array of words disjoint from the stored word holds after them. -/
theorem runA_storeMoveBody_frame {s : LstateA} (zf : Bool) (hpc : s.reg.lpc = 0)
    {p v : BitVec 64} (hB : s.reg.getW "B" 64 = some p) (hV : s.reg.getW "V" 64 = some v)
    {a : BitVec 64} {xs : List (BitVec (8 * 8))}
    (hd : Disjoint (arrAt 8 a xs).fp (⟨p + BitVec.ofNat 64 0, 8⟩ : Rng 64).toSet)
    (hR : (arrPts 8 a xs).holds (s, zf)) :
    ∃ q, runA (fun _ => none) storeMoveBody 2 s zf = some q ∧ (arrPts 8 a xs).holds q := by
  have hstep := stepA_storeMoveBody_zero zf hpc hB hV
  have hstep2 := stepA_storeMoveBody_one (s := ⟨s.reg.nextPc,
    write64 s.mem (p + BitVec.ofNat 64 0) v, s.cf, s.of⟩) zf
    (by simp [JasminLsemWidthN.LstateN.nextPc, hpc])
  have hrun : runA (fun _ => none) storeMoveBody 2 s zf = some (⟨(s.reg.nextPc.setReg "D"
      (s.reg.nextPc.lvm "S").2).nextPc, write64 s.mem (p + BitVec.ofNat 64 0) v, s.cf, s.of⟩,
      zf) := by
    rw [runA_step _ _ _ _ _ (by simp [haltedA, hpc, storeMoveBody]), hstep, Option.bind_some,
      runA_step _ _ _ _ _ (by simp [haltedA, hpc, storeMoveBody, LstateN.nextPc]), hstep2,
      Option.bind_some, runA_halt _ _ _ _ _ (by simp [haltedA, hpc, storeMoveBody,
        LstateN.nextPc, LstateN.setReg])]
  refine ⟨_, hrun, runA_frame _ _ hrun _ ?_ hR⟩
  refine Set.disjoint_left.2 fun l hl hw => ?_
  rw [runWrites_storeMoveBody zf hpc hB hV] at hw
  obtain ⟨x, hx, rfl⟩ := hl
  exact Set.disjoint_left.1 hd hx hw

end CatCrypt.Crypto.SecureCompilation.SepLogic.Addr
