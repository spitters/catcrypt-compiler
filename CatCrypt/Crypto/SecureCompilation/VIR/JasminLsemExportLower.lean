/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin

@[expose] public section

set_option autoImplicit false

/-!
# Instruction expansion on the flag machine

The physical export rewrites a body instruction by instruction after register
allocation: a three-address binop `OP d, s0, s1` becomes `MOV d, s0 ; OP d, d, s1`
(`lowerTwoAddr`), and the synthetic `LIVEPIN` is dropped. Both are expansions
`expand : LinstrRM → List LinstrRM` applied with `List.flatMap`, so program
counters and label positions move. This module proves that such an expansion
preserves halting runs of the flag machine `lsemFuelMemF` over `LstateM`.

## Contents

* **§1 the program-counter map.** `pcMap expand body k` is the length of the
  expansion of the first `k` instructions. `getElem?_flatMap_pcMap` locates the
  expansion of instruction `k` in the expanded body, and
  `findLabelMem_flatMap` sends a label position through `pcMap`.
* **§2 the simulation.** `InstrOK Q expand i` is the per-instruction condition:
  an `Lopn` whose expansion is a straight segment that reaches a `Q`-related
  state (the empty segment included), or a label, a zero-flag conditional or a
  goto that expands to itself. `lsemFuelMemF_expand` matches every halting run
  of `P` by a halting run of `P.body.flatMap expand`, with final states related
  by `RelX` and fuel at most `fuel * m` for a bound `m` on expansion lengths.
* **§3 states equal up to the program counter.** `EqPc` is the relation of the
  two-address lowering, which uses no scratch register. `fstepF_setLpc` states
  that a straight step does not read the program counter, and `instrOK_self`
  derives `InstrOK` for an instruction that expands to itself.
* **§4 two-address lowering.** `fstepF_movWire` steps the inserted copy
  `MOV d, s0`, which leaves the zero flag unchanged. `lsemStepMC_twoAddr` and
  `fstepF_twoAddr` run `MOV d, s0 ; OP d, d, s1` to the state of `OP d, s0, s1`
  up to the program counter, when `s1` is not the register `d` and `OP` is not
  the flag compare. `lowerRM` is the lowering of a body, `LowerOK` its side
  conditions, and `lsemFuelMemF_lowerRM` the instance of `lsemFuelMemF_expand`
  at `EqPc` with fuel bound `fuel * 2`.

## Scope

The lowering `lowerRM` is stated on `LinstrRM` bodies with a binop test and a
copy mnemonic as parameters; its identification with the output of
`physBodyRmap` on a spill-free body is outside this module, as is the removal of
the synthetic `LIVEPIN`. Array accesses stay keyed by array name: the reload of
an array base into `R14` that `physBodyWithStores` places before
`LOADIDX`/`STOREIDX` is not an expansion on this machine. The legalisation of
stack-slot operands through `R15`/`R14` needs a relation that ignores the two
scratch registers; `lsemFuelMemF_expand` takes any such `Q`.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin

/-! ## 1. The program-counter map -/

section PcMap

variable {α : Type} (expand : α → List α)

/-- The position in `body.flatMap expand` at which the expansion of instruction
    `k` of `body` begins: the length of the expansion of the first `k`
    instructions. -/
def pcMap (body : List α) (k : Nat) : Nat :=
  ((body.take k).flatMap expand).length

@[simp] theorem pcMap_zero (body : List α) : pcMap expand body 0 = 0 := by
  simp [pcMap]

theorem pcMap_succ {body : List α} {k : Nat} {i : α} (h : body[k]? = some i) :
    pcMap expand body (k + 1) = pcMap expand body k + (expand i).length := by
  unfold pcMap
  rw [List.take_add_one, h]
  simp

theorem pcMap_of_length_le {body : List α} {k : Nat} (h : body.length ≤ k) :
    pcMap expand body k = (body.flatMap expand).length := by
  unfold pcMap
  rw [List.take_of_length_le h]

/-- The expansion of instruction `k` sits at `pcMap k` in the expanded body. -/
theorem getElem?_flatMap_pcMap {body : List α} {k : Nat} {i : α} (h : body[k]? = some i)
    {j : Nat} (hj : j < (expand i).length) :
    (body.flatMap expand)[pcMap expand body k + j]? = (expand i)[j]? := by
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp h).1
  have hsplit : body = body.take k ++ i :: body.drop (k + 1) := by
    have hi : body[k] = i := (List.getElem?_eq_some_iff.mp h).2
    rw [← hi, List.cons_getElem_drop_succ, List.take_append_drop]
  have hfm : body.flatMap expand
      = (body.take k).flatMap expand ++ (expand i ++ (body.drop (k + 1)).flatMap expand) := by
    conv_lhs => rw [hsplit]
    rw [List.flatMap_append, List.flatMap_cons]
  rw [hfm]
  unfold pcMap
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left hj]

/-- Past the end of `body` the mapped position is past the end of the expanded
    body. -/
theorem getElem?_flatMap_pcMap_none {body : List α} {k : Nat} (h : body[k]? = none) :
    (body.flatMap expand)[pcMap expand body k]? = none := by
  have hk : body.length ≤ k := List.getElem?_eq_none_iff.mp h
  rw [pcMap_of_length_le expand hk]
  exact List.getElem?_eq_none_iff.mpr (Nat.le_refl _)

/-- The first position satisfying `p` moves through `pcMap`, when an element
    satisfying `p` expands to itself and the expansion of any other element holds
    no element satisfying `p`. -/
theorem findIdx?_flatMap (p : α → Bool) :
    ∀ (body : List α),
      (∀ i ∈ body, (p i = true → expand i = [i])
        ∧ (p i = false → ∀ j ∈ expand i, p j = false)) →
      (body.flatMap expand).findIdx? p = (body.findIdx? p).map (pcMap expand body) := by
  intro body
  induction body with
  | nil => intro _; rfl
  | cons i is ih =>
      intro h
      have his := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
      obtain ⟨h1, h2⟩ := h i (by simp)
      cases hp : p i with
      | true =>
          rw [List.flatMap_cons, h1 hp]
          simp [List.findIdx?_cons, hp]
      | false =>
          have hnone : (expand i).findIdx? p = none := by
            rw [List.findIdx?_eq_none_iff]
            intro j hj
            simpa using h2 hp j hj
          rw [List.flatMap_cons, List.findIdx?_append, hnone, his]
          simp only [List.findIdx?_cons, hp, Option.none_or, Option.map_map]
          cases is.findIdx? p with
          | none => rfl
          | some k =>
              simp [pcMap, Nat.add_comm]

end PcMap

/-! ## 2. The simulation -/

section Sim

variable (Q : LstateM → LstateM → Prop) (expand : LinstrRM → List LinstrRM)

/-- The condition on one instruction of the source program. Either it is an
    `Lopn` whose expansion is a list of `Lopn`s (possibly empty) that, run as a
    straight segment from a `Q`-related state, reaches a `Q`-related state with
    the same zero flag; or it is a label, a zero-flag conditional or a goto, and
    expands to itself. -/
def InstrOK (i : LinstrRM) : Prop :=
  (IsLopn i ∧ (∀ j ∈ expand i, IsLopn j) ∧
    ∀ (s s' t : LstateM) (zf zt : Bool), Q s s' → fstepF i s zf = some (t, zt) →
      ∃ t', runStraightF (expand i) s' zf = some (t', zt) ∧ Q t t')
  ∨ (expand i = [i] ∧
      ((∃ kd l, i.1 = LinstrR.Llabel kd l)
        ∨ (∃ c l, i.1 = LinstrR.Lcond c l ∧ flagCondCC? i ≠ none)
        ∨ (∃ tgt, i.1 = LinstrR.Lgoto tgt)))

/-- The two programs of an expansion simulation: the same function name, the
    target body is the expanded source body, every source instruction satisfies
    `InstrOK`, and `Q` does not constrain the program counters. -/
structure ExpProg (P P' : LprogM) : Prop where
  /-- The function names agree. -/
  lfn : P'.lfn = P.lfn
  /-- The target body is the expansion of the source body. -/
  body : P'.body = P.body.flatMap expand
  /-- Every source instruction satisfies the per-instruction condition. -/
  inst : ∀ (k : Nat) (i : LinstrRM), P.body[k]? = some i → InstrOK Q expand i
  /-- `Q` is stable under writes of the two program counters. -/
  pc : ∀ a b p q, Q a b → Q (a.setLpc p) (b.setLpc q)

/-- The state relation of the simulation: function name and zero flag agree, the
    target program counter is the image of the source one under `pcMap`, and the
    bases are related by `Q`. -/
structure RelX (P : LprogM) (s s' : LstateMF) : Prop where
  /-- The function names agree. -/
  lfn : s'.prog.lfn = s.prog.lfn
  /-- The zero flags agree. -/
  zf : s'.zf = s.zf
  /-- The target program counter is the mapped source program counter. -/
  pc : s'.prog.base.lpc = pcMap expand P.body s.prog.base.lpc
  /-- The bases are related. -/
  base : Q s.prog.base s'.prog.base

variable {Q expand}

theorem isLabel_of_isLopn {i : LinstrRM} (h : IsLopn i) (l : LLabel) :
    JasminLsemLabeled.isLabel l i.1 = false := by
  obtain ⟨d, o, s, hd⟩ := h
  rw [hd]; rfl

/-- A label position of the source body moves through `pcMap`. -/
theorem findLabelMem_flatMap {P P' : LprogM} (hP : ExpProg Q expand P P') (l : LLabel) :
    findLabelMem l P'.body = (findLabelMem l P.body).map (pcMap expand P.body) := by
  unfold findLabelMem JasminLsemLabeled.findLabel
  rw [hP.body, List.findIdx?_map, List.findIdx?_map]
  refine findIdx?_flatMap expand _ P.body (fun i hi => ?_)
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hi
  rcases hP.inst k i hk with ⟨hl, hex, _⟩ | ⟨hself, _⟩
  · refine ⟨fun hp => ?_, fun _ j hj => isLabel_of_isLopn (hex j hj) l⟩
    have := isLabel_of_isLopn hl l
    simp only [Function.comp] at hp
    rw [this] at hp
    exact absurd hp (by simp)
  · refine ⟨fun _ => hself, fun hp j hj => ?_⟩
    rw [hself] at hj
    obtain rfl : j = i := by simpa using hj
    exact hp

/-- A label of the source body expands to one instruction, so the position after
    it moves through `pcMap` to the position after its image. -/
theorem pcMap_succ_of_findLabelMem {P P' : LprogM} (hP : ExpProg Q expand P P') {l : LLabel}
    {pc : Nat} (hl : findLabelMem l P.body = some pc) :
    pcMap expand P.body (pc + 1) = pcMap expand P.body pc + 1 := by
  obtain ⟨w, hw, hlab⟩ := JasminLsemLabeled.findLabel_sound l _ pc hl
  rw [List.getElem?_map] at hw
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hw
  rw [pcMap_succ expand hi]
  rcases hP.inst pc i hi with ⟨hlopn, _⟩ | ⟨hself, _⟩
  · rw [isLabel_of_isLopn hlopn l] at hlab
    exact absurd hlab (by simp)
  · rw [hself]; rfl

/-- A jump of the source program is matched by the same jump of the target. -/
theorem evalJumpMem_expand {P P' : LprogM} (hP : ExpProg Q expand P P') (l : LLabel)
    {p p' q : LstatePM} (hQ : Q p.base p'.base) (hfn : p'.lfn = p.lfn)
    (h : evalJumpMem P l p = some q) :
    ∃ q', evalJumpMem P' l p' = some q' ∧ Q q.base q'.base ∧ q'.lfn = q.lfn
      ∧ q'.base.lpc = pcMap expand P.body q.base.lpc := by
  unfold evalJumpMem at h ⊢
  rw [findLabelMem_flatMap hP l]
  cases hl : findLabelMem l P.body with
  | none => simp [hl] at h
  | some pc =>
      simp only [hl, Option.map_some] at h ⊢
      cases h
      exact ⟨_, rfl, hP.pc _ _ _ _ hQ, hfn, (pcMap_succ_of_findLabelMem hP hl).symm⟩

/-- **One source step.** A successful step of the source program at instruction
    `i` is matched by `(expand i).length` steps of the target program from a
    related state, into a related state. -/
theorem evalInstrPMemF_expand {P P' : LprogM} (hP : ExpProg Q expand P P')
    {s s' u : LstateMF} {i : LinstrRM} (hR : RelX Q expand P s s')
    (hfn : s.prog.lfn = P.lfn) (hget : P.body[s.prog.base.lpc]? = some i)
    (he : evalInstrPMemF P i s = some u) :
    ∃ u', (∀ f, lsemFuelMemF P' ((expand i).length + f) s' = lsemFuelMemF P' f u')
      ∧ RelX Q expand P u u' := by
  have hfn' : s'.prog.lfn = P'.lfn := hR.lfn.trans (hfn.trans hP.lfn.symm)
  have hpos : ∀ k, k < (expand i).length →
      P'.body[s'.prog.base.lpc + k]? = (expand i)[k]? := by
    intro k hk
    rw [hR.pc, hP.body]
    exact getElem?_flatMap_pcMap expand hget hk
  rcases hP.inst _ i hget with ⟨hlopn, hex, hstep⟩ | ⟨hself, hctl⟩
  · rw [evalInstrPMemF_isLopn P i s hlopn] at he
    obtain ⟨bz, hb, rfl⟩ := Option.map_eq_some_iff.mp he
    obtain ⟨b, z⟩ := bz
    obtain ⟨b', hb', hQb⟩ := hstep _ _ _ _ _ hR.base hb
    refine ⟨{ prog := { base := b', lfn := s'.prog.lfn }, zf := z }, fun f => ?_, ?_⟩
    · have hseg := lsemFuelMemF_segF P' s'.prog.lfn hfn' (expand i) s'.prog.base s'.zf f
        hex hpos
      rw [← hR.zf] at hb'
      rw [hb'] at hseg
      exact hseg
    · refine ⟨hR.lfn, rfl, ?_, hQb⟩
      have h1 := runStraightF_lpc _ _ _ _ _ hb'
      have h2 := fstepF_lpc_succ _ _ _ _ _ hb
      show b'.lpc = pcMap expand P.body b.lpc
      rw [h1, h2, pcMap_succ expand hget, hR.pc]
  · have hfetch : findInstrMem P' s'.prog = some i := by
      unfold findInstrMem
      rw [if_pos hfn']
      have := hpos 0 (by rw [hself]; simp)
      simpa [hself] using this
    have hone : ∀ {u' : LstateMF}, evalInstrPMemF P' i s' = some u' →
        ∀ f, lsemFuelMemF P' ((expand i).length + f) s' = lsemFuelMemF P' f u' := by
      intro u' hu' f
      rw [hself, List.length_singleton, Nat.add_comm]
      exact lsemFuelMemF_step P' f i s' u' hfetch hu'
    have hnext : pcMap expand P.body (s.prog.base.lpc + 1) = s'.prog.base.lpc + 1 := by
      rw [pcMap_succ expand hget, hself, hR.pc]; rfl
    obtain ⟨wire, tag⟩ := i
    rcases hctl with ⟨kd, l, hw⟩ | ⟨c, l, hw, hcc⟩ | ⟨tgt, hw⟩
    · obtain rfl : wire = LinstrR.Llabel kd l := hw
      rw [evalInstrPMemF_label] at he
      cases he
      exact ⟨_, hone (evalInstrPMemF_label P' kd l tag s'),
        ⟨hR.lfn, hR.zf, hnext.symm, hP.pc _ _ _ _ hR.base⟩⟩
    · obtain rfl : wire = LinstrR.Lcond c l := hw
      have h1 : cmpArgs? (LinstrR.Lcond c l, tag) = none := rfl
      have h2 : movRegArgs? (LinstrR.Lcond c l, tag) = none := rfl
      cases h3 : flagCondCC? (LinstrR.Lcond c l, tag) with
      | none => exact absurd h3 hcc
      | some pl =>
          obtain ⟨pol, lbl⟩ := pl
          unfold evalInstrPMemF at he
          simp only [h1, h2, h3] at he
          split at he
          · rename_i hz
            obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp he
            obtain ⟨q', hq', hQq, hfq, hpq⟩ := evalJumpMem_expand hP lbl hR.base hR.lfn hq
            refine ⟨{ s' with prog := q' }, hone ?_, ⟨hfq, hR.zf, hpq, hQq⟩⟩
            unfold evalInstrPMemF
            simp only [h1, h2, h3]
            rw [if_pos (hR.zf.trans hz), hq']; rfl
          · rename_i hz
            cases he
            refine ⟨{ s' with prog := { s'.prog with base := s'.prog.base.nextPc } },
              hone ?_, ⟨hR.lfn, hR.zf, hnext.symm, hP.pc _ _ _ _ hR.base⟩⟩
            unfold evalInstrPMemF
            simp only [h1, h2, h3]
            rw [if_neg (fun h => hz (hR.zf.symm.trans h))]
    · obtain rfl : wire = LinstrR.Lgoto tgt := hw
      obtain ⟨fn, l⟩ := tgt
      have hev : ∀ (R : LprogM) (x : LstateMF),
          evalInstrPMemF R (LinstrR.Lgoto (fn, l), tag) x
            = (if fn = R.lfn then evalJumpMem R l x.prog else none).map
                (fun p => { x with prog := p }) := fun R x => by
        rw [evalInstrPMemF_delegate R _ x rfl rfl rfl rfl rfl]; rfl
      rw [hev] at he
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp he
      split at hq
      · rename_i hf
        obtain ⟨q', hq', hQq, hfq, hpq⟩ := evalJumpMem_expand hP l hR.base hR.lfn hq
        refine ⟨{ s' with prog := q' }, hone ?_, ⟨hfq, hR.zf, hpq, hQq⟩⟩
        rw [hev, hP.lfn, if_pos hf, hq']; rfl
      · exact absurd hq (by simp)

/-- **The flag machine under an instruction expansion.** Every halting run of
    `P` is matched, from a related state, by a halting run of the expanded
    program into a related state. The target run takes `(expand i).length` steps
    for each source step at instruction `i`, so its fuel is at most `fuel * m` for
    a bound `m` on the expansion lengths. -/
theorem lsemFuelMemF_expand {P P' : LprogM} (hP : ExpProg Q expand P P') {m : Nat}
    (hm : ∀ i ∈ P.body, (expand i).length ≤ m) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, RelX Q expand P s s' →
      lsemFuelMemF P fuel s = some t →
      ∃ fuel' t', fuel' ≤ fuel * m ∧ lsemFuelMemF P' fuel' s' = some t'
        ∧ RelX Q expand P t t' := by
  have hhalt : ∀ {s s' : LstateMF}, RelX Q expand P s s' →
      findInstrMem P s.prog = none → findInstrMem P' s'.prog = none := by
    intro s s' hR hf
    unfold findInstrMem at hf ⊢
    rw [hR.lfn, hP.lfn]
    split
    · rename_i hfn
      rw [if_pos hfn] at hf
      rw [hR.pc, hP.body]
      exact getElem?_flatMap_pcMap_none expand hf
    · rfl
  intro fuel
  induction fuel with
  | zero =>
      intro s s' t hR h
      unfold lsemFuelMemF at h
      cases hf : findInstrMem P s.prog with
      | none =>
          simp only [hf] at h
          cases h
          exact ⟨0, s', by simp, lsemFuelMemF_halt P' 0 s' (hhalt hR hf), hR⟩
      | some i => simp [hf] at h
  | succ n ih =>
      intro s s' t hR h
      unfold lsemFuelMemF at h
      cases hf : findInstrMem P s.prog with
      | none =>
          simp only [hf] at h
          cases h
          exact ⟨0, s', by simp, lsemFuelMemF_halt P' 0 s' (hhalt hR hf), hR⟩
      | some i =>
          simp only [hf] at h
          have hfg : s.prog.lfn = P.lfn ∧ P.body[s.prog.base.lpc]? = some i := by
            unfold findInstrMem at hf
            split at hf
            · exact ⟨by assumption, hf⟩
            · simp at hf
          cases he : evalInstrPMemF P i s with
          | none => simp [he] at h
          | some u =>
              simp only [he] at h
              obtain ⟨u', hrun, hRu⟩ := evalInstrPMemF_expand hP hR hfg.1 hfg.2 he
              obtain ⟨f', t', hf', hrun', hRt⟩ := ih hRu h
              have hlen := hm i (List.mem_of_getElem? hfg.2)
              refine ⟨(expand i).length + f', t', ?_, by rw [hrun]; exact hrun', hRt⟩
              rw [Nat.succ_mul]
              omega

end Sim

/-! ## 3. States equal up to the program counter -/

/-- The register state with its program counter replaced. -/
def setLpcN (s : LstateN) (p : Nat) : LstateN := { s with lpc := p }

theorem lsemStepN_setLpc (i : LinstrR) (s : LstateN) (p : Nat) :
    lsemStepN i (setLpcN s p) = (lsemStepN i s).map (fun t => setLpcN t (p + 1)) := by
  have hr : ∀ o, readReg (setLpcN s p) o = readReg s o := fun o => by cases o <;> rfl
  have he : ∀ w o, evalOperandN (setLpcN s p) w o = evalOperandN s w o :=
    fun w o => by cases o <;> rfl
  have hg : ∀ r w, (setLpcN s p).getW r w = s.getW r w := fun _ _ => rfl
  unfold lsemStepN
  split <;> (try simp only [hr, he, hg]) <;> (repeat' split) <;> rfl

theorem lsemStepSh_setLpc (i : LinstrR) (s : LstateN) (p : Nat) :
    lsemStepSh i (setLpcN s p) = (lsemStepSh i s).map (fun t => setLpcN t (p + 1)) := by
  have hr : ∀ o, readReg (setLpcN s p) o = readReg s o := fun o => by cases o <;> rfl
  unfold lsemStepSh
  split <;> (try simp only [hr]) <;> (repeat' split) <;>
    first | rfl | exact lsemStepN_setLpc _ _ _

theorem lsemStepMC_setLpc (i : LinstrR) (s : LstateN) (p : Nat) :
    lsemStepMC i (setLpcN s p) = (lsemStepMC i s).map (fun t => setLpcN t (p + 1)) := by
  have hr : ∀ o, readReg (setLpcN s p) o = readReg s o := fun o => by cases o <;> rfl
  have hg : ∀ r w, (setLpcN s p).getW r w = s.getW r w := fun _ _ => rfl
  unfold lsemStepMC
  simp only [hr, hg]
  (repeat' split) <;> first | rfl | exact lsemStepSh_setLpc _ _ _

theorem lsemStepCast_setLpc (i : LinstrRT) (s : LstateN) (p : Nat) :
    lsemStepCast i (setLpcN s p) = (lsemStepCast i s).map (fun t => setLpcN t (p + 1)) := by
  have hr : ∀ o, readReg (setLpcN s p) o = readReg s o := fun o => by cases o <;> rfl
  unfold lsemStepCast
  split <;> (try simp only [hr]) <;> (repeat' split) <;>
    first | rfl | exact lsemStepMC_setLpc _ _ _

/-- **A memory step does not read the program counter.** -/
theorem lsemStepMem_setLpc (i : LinstrRM) (s : LstateM) (p : Nat) :
    lsemStepMem i (s.setLpc p) = (lsemStepMem i s).map (fun t => t.setLpc (p + 1)) := by
  have hreg : (s.setLpc p).reg = setLpcN s.reg p := rfl
  have ha : ∀ r w n, (s.setLpc p).getArr r w n = s.getArr r w n := fun _ _ _ => rfl
  have hg : ∀ r w, (setLpcN s.reg p).getW r w = s.reg.getW r w := fun _ _ => rfl
  have hm : (s.setLpc p).lmem = s.lmem := rfl
  unfold lsemStepMem
  simp only [hreg, ha, hg, hm]
  (repeat' split) <;>
    first
      | rfl
      | (rw [lsemStepCast_setLpc, Option.map_map, Option.map_map]; rfl)

/-- **The flag machine's straight-line step does not read the program counter.** -/
theorem stepMemF_setLpc (i : LinstrRM) (s : LstateM) (p : Nat) :
    stepMemF i (s.setLpc p) = (stepMemF i s).map (fun t => t.setLpc (p + 1)) := by
  have he : ∀ w o, evalOperandN (s.setLpc p).reg w o = evalOperandN s.reg w o :=
    fun w o => by cases o <;> rfl
  unfold stepMemF
  rw [lsemStepMem_setLpc]
  cases lsemStepMem i s with
  | some b =>
      simp only [Option.map_some]
      unfold withALUFlags
      simp only [he]
      split
      · split <;> rfl
      · rfl
  | none =>
      simp only [Option.map_none]
      split
      · unfold carryStep
        simp only [he]
        split
        · split <;> rfl
        · rfl
      · rfl

/-- **A straight step does not read the program counter.** -/
theorem fstepF_setLpc (i : LinstrRM) (s : LstateM) (zf : Bool) (p : Nat) :
    fstepF i (s.setLpc p) zf
      = (fstepF i s zf).map (fun bz => (bz.1.setLpc (p + 1), bz.2)) := by
  have hreg : (s.setLpc p).reg = setLpcN s.reg p := rfl
  have hr : ∀ o, readReg (setLpcN s.reg p) o = readReg s.reg o :=
    fun o => by cases o <;> rfl
  have he : ∀ w o, evalOperandN (setLpcN s.reg p) w o = evalOperandN s.reg w o :=
    fun w o => by cases o <;> rfl
  unfold fstepF
  simp only [hreg, hr, he]
  (repeat' split) <;>
    first
      | rfl
      | (rw [stepMemF_setLpc, Option.map_map, Option.map_map]; rfl)

/-- Two bases that differ in the program counter only. -/
def EqPc (a b : LstateM) : Prop := b = a.setLpc b.lpc

theorem EqPc.refl_setLpc (a : LstateM) (p : Nat) : EqPc a (a.setLpc p) := rfl

theorem EqPc.setLpc {a b : LstateM} (h : EqPc a b) (p q : Nat) :
    EqPc (a.setLpc p) (b.setLpc q) := by
  unfold EqPc at h ⊢
  rw [h]; rfl

/-- A straight segment that runs from a state runs from every state equal to it
    up to the program counter, with the same flag and an equal final state. -/
theorem runStraightF_eqPc :
    ∀ (seg : List LinstrRM) {s s' t : LstateM} {zf zt : Bool}, EqPc s s' →
      runStraightF seg s zf = some (t, zt) →
      ∃ t', runStraightF seg s' zf = some (t', zt) ∧ EqPc t t' := by
  intro seg
  induction seg with
  | nil =>
      intro s s' t zf zt hE h
      simp only [runStraightF_nil, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨s', rfl, hE⟩
  | cons i is ih =>
      intro s s' t zf zt hE h
      rw [runStraightF_cons] at h ⊢
      cases hs : fstepF i s zf with
      | none => rw [hs] at h; exact absurd h (by simp)
      | some bz =>
          rw [hs, Option.bind_some] at h
          unfold EqPc at hE
          rw [hE, fstepF_setLpc, hs, Option.map_some, Option.bind_some]
          exact ih (EqPc.refl_setLpc bz.1 _) h

/-- An `Lopn` that expands to itself satisfies the per-instruction condition at
    `EqPc`. -/
theorem instrOK_self {expand : LinstrRM → List LinstrRM} {i : LinstrRM}
    (hl : IsLopn i) (hself : expand i = [i]) : InstrOK EqPc expand i := by
  refine Or.inl ⟨hl, fun j hj => ?_, fun s s' t zf zt hE h => ?_⟩
  · rw [hself] at hj
    obtain rfl : j = i := by simpa using hj
    exact hl
  · rw [hself]
    refine runStraightF_eqPc [i] hE ?_
    rw [runStraightF_cons, h]; rfl

/-! ## 4. Two-address lowering -/

/-- The three-address wire `OP d, x, s1`. -/
def binopWire (d x : String) (s1 : LOperand) (opn : String) : LinstrR :=
  .Lopn [.reg d] opn [.reg x, s1]

/-- A second write to `d`, one fall-through later, overwrites the first. -/
theorem setReg_nextPc_setReg (st : LstateN) (d : String) {w w' : Nat} (v : BitVec w)
    (r : BitVec w') :
    (((st.setReg d v).nextPc).setReg d r).nextPc = setLpcN ((st.setReg d r).nextPc) (st.lpc + 2) := by
  simp only [LstateN.setReg, LstateN.nextPc, setLpcN]
  congr 1
  funext r'
  split <;> rfl

/-- **The register step of the lowered binop.** After `d` receives the cell of
    `s0`, the step of `OP d, d, s1` is the step of `OP d, s0, s1` one program
    counter later, when `s1` is not the register `d`. -/
theorem lsemStepMC_twoAddr (st : LstateN) (d s0 : String) (s1 : LOperand) (opn : String)
    {w : Nat} (v : BitVec w) (hc : st.lvm s0 = ⟨w, v⟩) (hd : s1 ≠ .reg d) :
    lsemStepMC (binopWire d d s1 opn) ((st.setReg d v).nextPc)
      = (lsemStepMC (binopWire d s0 s1 opn) st).map (fun t => setLpcN t (st.lpc + 2)) := by
  have hr1 : readReg st (.reg s0) = some ⟨w, v⟩ := by simp only [readReg, hc]
  have hr2 : readReg ((st.setReg d v).nextPc) (.reg d) = some ⟨w, v⟩ := by
    simp only [readReg, LstateN.lvm_nextPc, LstateN.lvm_setReg, if_true]
  cases s1 with
  | reg b =>
      have hb : b ≠ d := fun h => hd (by rw [h])
      have hgw : ∀ (w' : Nat), ((st.setReg d v).nextPc).getW b w' = st.getW b w' :=
        fun w' => by rw [LstateN.getW_nextPc, LstateN.getW_setReg_other st d b v w' hb]
      simp only [binopWire, lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?,
        sbbhiStruct?, lsemStepSh, sarStruct?, lsemStepN, hr1, hr2, evalOperandN, hgw]
      by_cases hm : stripWidthTag opn = "MULXHI"
      · simp only [hm, ↓reduceIte, hr1, hr2, hgw]
        split
        · simp only [Option.map_some, setReg_nextPc_setReg]
        · rfl
      · simp only [hm, ↓reduceIte]
        split
        · split
          · simp only [Option.map_some, setReg_nextPc_setReg]
          · rfl
        · rfl
  | imm n =>
      simp only [binopWire, lsemStepMC, mulhiStruct?, adcxStruct?, adcxhiStruct?, sbbStruct?,
        sbbhiStruct?, lsemStepSh, sarStruct?, lsemStepN, hr1, hr2, evalOperandN]
      by_cases hm : stripWidthTag opn = "SAR"
      · simp only [hm, ↓reduceIte, hr1, hr2, Option.map_some, setReg_nextPc_setReg]
      · simp only [hm, ↓reduceIte]
        split
        · simp only [Option.map_some, setReg_nextPc_setReg]
        · rfl
  | arr _ _ => rfl
  | arrIdx _ _ _ => rfl

/-- The inserted copy `MOV d, s0`, under any mnemonic that strips to `"MOV"`. -/
def movWire (d s0 mov : String) : LinstrR := .Lopn [.reg d] mov [.reg s0]

/-- **The inserted copy.** `MOV d, s0` writes the cell of `s0` to `d` and leaves
    the zero flag unchanged. -/
theorem fstepF_movWire (d s0 mov : String) (tag : MemTag) (hmov : stripWidthTag mov = "MOV")
    (s : LstateM) (zf : Bool) :
    fstepF (movWire d s0 mov, tag) s zf
      = some ((s.setReg d (s.reg.lvm s0).2).nextPc, zf) := by
  have h1 : cmpArgs? (movWire d s0 mov, tag) = none := rfl
  have h2 : movRegArgs? (movWire d s0 mov, tag) = some (d, s0) := by
    simp only [movRegArgs?, movWire, hmov, if_true]
  unfold fstepF
  simp only [h1, h2]
  rfl

/-- The memory step of a register-tagged binop is the register step `lsemStepMC`. -/
theorem lsemStepMem_binopWire (d x : String) (s1 : LOperand) (opn : String)
    (cd : Option Nat) (s : LstateM) :
    lsemStepMem (binopWire d x s1 opn, .reg cd) s
      = (lsemStepMC (binopWire d x s1 opn) s.reg).map (fun r => { s with reg := r }) := by
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _ (Or.inl rfl)]

/-- The straight step of a register-tagged binop that is not the flag compare is
    the flag machine's step `stepMemF`, with the zero flag unchanged. -/
theorem fstepF_binopWire (d x : String) (s1 : LOperand) (opn : String) (cd : Option Nat)
    (hcmp : opn ≠ withWidthTag 64 "CMP") (s : LstateM) (zf : Bool) :
    fstepF (binopWire d x s1 opn, .reg cd) s zf
      = (stepMemF (binopWire d x s1 opn, .reg cd) s).map (fun b => (b, zf)) := by
  have h1 : cmpArgs? (binopWire d x s1 opn, MemTag.reg cd) = none := by
    simp only [cmpArgs?, binopWire, hcmp, if_false]
  have h2 : movRegArgs? (binopWire d x s1 opn, MemTag.reg cd) = none := rfl
  unfold fstepF
  simp only [h1, h2]

/-- **The flag machine's step of the two-address binop.** After the copy
    `MOV d, s0`, the binop `OP d, d, s1` steps as `OP d, s0, s1` from the state before
    the copy, up to the program counter, provided `s1` is not the register `d`. -/
theorem stepMemF_twoAddr (d s0 : String) (s1 : LOperand) (opn : String) (cd : Option Nat)
    (s : LstateM) {w : Nat} (v : BitVec w) (hc : s.reg.lvm s0 = ⟨w, v⟩) (hd : s1 ≠ .reg d) :
    stepMemF (binopWire d d s1 opn, .reg cd) ((s.setReg d v).nextPc)
      = (stepMemF (binopWire d s0 s1 opn, .reg cd) s).map
          (fun t => t.setLpc (s.reg.lpc + 2)) := by
  have hlow := lsemStepMC_twoAddr s.reg d s0 s1 opn v hc hd
  have e1 : ∀ u, evalOperandN ((s.setReg d v).nextPc).reg u (.reg d)
      = evalOperandN s.reg u (.reg s0) := by
    intro u
    have hd' : ((s.reg.setReg d v).nextPc).lvm d = s.reg.lvm s0 := by
      rw [hc]; simp [LstateN.nextPc, LstateN.lvm_setReg]
    simp only [evalOperandN, LstateM.reg_nextPc, LstateM.reg_setReg]
    unfold LstateN.getW
    rw [hd']
  have e2 : ∀ u, evalOperandN ((s.setReg d v).nextPc).reg u s1 = evalOperandN s.reg u s1 := by
    intro u
    cases s1 with
    | reg b =>
        have hb : b ≠ d := fun h => hd (by rw [h])
        simp only [evalOperandN, LstateM.reg_nextPc, LstateM.reg_setReg, LstateN.getW_nextPc,
          LstateN.getW_setReg_other _ _ _ _ _ hb]
    | _ => rfl
  unfold stepMemF
  rw [lsemStepMem_binopWire, lsemStepMem_binopWire]
  rw [show ((s.setReg d v).nextPc).reg = (s.reg.setReg d v).nextPc from rfl, hlow]
  have hset : ∀ x : BitVec 64, (((s.setReg d v).nextPc).setReg d x).nextPc
      = ((s.setReg d x).nextPc).setLpc (s.reg.lpc + 2) := by
    intro x
    simp only [LstateM.setLpc, LstateM.nextPc, LstateM.setReg, LstateN.nextPc,
      LstateN.setReg]
    congr 2
    funext r'
    by_cases h : r' = d <;> simp [h]
  cases lsemStepMC (binopWire d s0 s1 opn) s.reg with
  | some r =>
      simp only [Option.map_some]
      unfold withALUFlags aluFlagOp?
      simp only [binopWire]
      split_ifs <;> simp only [e1, e2] <;>
        (cases evalOperandN s.reg 64 (.reg s0) <;> cases evalOperandN s.reg 64 s1 <;> rfl)
  | none =>
      simp only [Option.map_none]
      unfold carryArgs? carryStep
      simp only [binopWire]
      split_ifs <;> simp only [e1, e2] <;>
        (cases evalOperandN s.reg 64 (.reg s0) <;> cases evalOperandN s.reg 64 s1 <;>
          simp only [Option.map_some, Option.map_none, hset] <;> rfl)

/-- **Two-address lowering of one binop.** When `OP d, s0, s1` steps, the pair
    `MOV d, s0 ; OP d, d, s1` runs from the same state to a state equal up to the
    program counter, with the same zero flag, provided `s1` is not the register
    `d` and `OP` is not the flag compare. -/
theorem fstepF_twoAddr (d s0 : String) (s1 : LOperand) (opn mov : String) (cd : Option Nat)
    (tagM : MemTag) (hmov : stripWidthTag mov = "MOV")
    (hcmp : opn ≠ withWidthTag 64 "CMP") (hd : s1 ≠ .reg d)
    {s t : LstateM} {zf zt : Bool}
    (h : fstepF (binopWire d s0 s1 opn, .reg cd) s zf = some (t, zt)) :
    ∃ t', runStraightF [(movWire d s0 mov, tagM), (binopWire d d s1 opn, .reg cd)] s zf
        = some (t', zt) ∧ EqPc t t' := by
  rw [fstepF_binopWire d s0 s1 opn cd hcmp] at h
  obtain ⟨t0, ht, hrt⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrt
  have hc : s.reg.lvm s0 = ⟨(s.reg.lvm s0).1, (s.reg.lvm s0).2⟩ := rfl
  have hs := stepMemF_twoAddr d s0 s1 opn cd s (s.reg.lvm s0).2 hc hd
  rw [ht, Option.map_some] at hs
  refine ⟨t0.setLpc (s.reg.lpc + 2), ?_, rfl⟩
  rw [runStraightF_cons, fstepF_movWire d s0 mov tagM hmov, Option.bind_some,
    runStraightF_cons, fstepF_binopWire d d s1 opn cd hcmp, hs]
  rfl

theorem EqPc.trans {a b c : LstateM} (h1 : EqPc a b) (h2 : EqPc b c) : EqPc a c := by
  unfold EqPc at h1 h2 ⊢
  rw [h2, h1]; rfl

theorem EqPc.symm {a b : LstateM} (h : EqPc a b) : EqPc b a := by
  unfold EqPc at h ⊢
  rw [h]; rfl

/-- The two-address lowering of a body on the flag machine, parametric in the
    binop test `isB` and the width-matched copy mnemonic `movFor`: a
    register-tagged `OP d, s0, s1` with `isB OP` and `d ≠ s0` becomes
    `MOV d, s0 ; OP d, d, s1`, and every other instruction is kept. -/
def lowerRM (isB : String → Bool) (movFor : String → String) (i : LinstrRM) : List LinstrRM :=
  match i with
  | (.Lopn [.reg d] opn [.reg s0, s1], .reg cd) =>
      if isB opn = true ∧ d ≠ s0 then
        [(movWire d s0 (movFor opn), .reg none), (binopWire d d s1 opn, .reg cd)]
      else [i]
  | _ => [i]

theorem lowerRM_cases (isB : String → Bool) (movFor : String → String) (i : LinstrRM) :
    lowerRM isB movFor i = [i] ∨
      ∃ d opn s0 s1 cd, i = (binopWire d s0 s1 opn, MemTag.reg cd) ∧ isB opn = true ∧ d ≠ s0
        ∧ lowerRM isB movFor i
            = [(movWire d s0 (movFor opn), .reg none), (binopWire d d s1 opn, .reg cd)] := by
  unfold lowerRM
  split
  · rename_i d opn s0 s1 cd
    by_cases hc : isB opn = true ∧ d ≠ s0
    · exact Or.inr ⟨d, opn, s0, s1, cd, rfl, hc.1, hc.2, by rw [if_pos hc]⟩
    · exact Or.inl (by rw [if_neg hc])
  · exact Or.inl rfl

theorem lowerRM_length_le (isB : String → Bool) (movFor : String → String) (i : LinstrRM) :
    (lowerRM isB movFor i).length ≤ 2 := by
  rcases lowerRM_cases isB movFor i with h | ⟨_, _, _, _, _, _, _, _, h⟩ <;> rw [h] <;> simp

/-- The side conditions of the two-address lowering of a program: the copy
    mnemonic strips to `"MOV"`, a lowered mnemonic is not the flag compare, the
    second source of a lowered binop is not its destination register, and every
    instruction is an `Lopn`, a label, a zero-flag conditional or a goto. -/
structure LowerOK (isB : String → Bool) (movFor : String → String) (P : LprogM) : Prop where
  /-- The copy mnemonic of a lowered binop strips to `"MOV"`. -/
  mov : ∀ opn, isB opn = true → stripWidthTag (movFor opn) = "MOV"
  /-- A lowered mnemonic is not the flag compare. -/
  cmp : ∀ opn, isB opn = true → opn ≠ withWidthTag 64 "CMP"
  /-- The second source of a lowered binop is not its destination register. -/
  src : ∀ (k : Nat) d opn s0 s1 cd,
    P.body[k]? = some (binopWire d s0 s1 opn, MemTag.reg cd) → isB opn = true → d ≠ s0 →
      s1 ≠ .reg d
  /-- The instruction classes of the program. -/
  ctl : ∀ (k : Nat) (i : LinstrRM), P.body[k]? = some i →
    IsLopn i ∨ (∃ kd l, i.1 = LinstrR.Llabel kd l)
      ∨ (∃ c l, i.1 = LinstrR.Lcond c l ∧ flagCondCC? i ≠ none)
      ∨ (∃ tgt, i.1 = LinstrR.Lgoto tgt)

/-- **The per-instruction condition of the two-address lowering.** -/
theorem instrOK_lowerRM {isB : String → Bool} {movFor : String → String} {P : LprogM}
    (hP : LowerOK isB movFor P) {k : Nat} {i : LinstrRM} (hk : P.body[k]? = some i) :
    InstrOK EqPc (lowerRM isB movFor) i := by
  rcases lowerRM_cases isB movFor i with hself | ⟨d, opn, s0, s1, cd, rfl, hb, hne, hlow⟩
  · rcases hP.ctl k i hk with hl | hctl
    · exact instrOK_self hl hself
    · exact Or.inr ⟨hself, hctl⟩
  · refine Or.inl ⟨⟨_, _, _, rfl⟩, fun j hj => ?_, fun s s' t zf zt hE h => ?_⟩
    · rw [hlow] at hj
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl
      · exact ⟨_, _, _, rfl⟩
      · exact ⟨_, _, _, rfl⟩
    · rw [hlow]
      obtain ⟨t1, hrun, hE1⟩ := fstepF_twoAddr d s0 s1 opn (movFor opn) cd (.reg none)
        (hP.mov opn hb) (hP.cmp opn hb) (hP.src k d opn s0 s1 cd hk hb hne) h
      obtain ⟨t2, hrun2, hE2⟩ := runStraightF_eqPc _ hE hrun
      exact ⟨t2, hrun2, hE1.trans hE2⟩

/-- **Two-address lowering preserves halting runs.** Every halting run of `P` is
    matched by a halting run of the lowered program with at most twice the fuel;
    the final states agree in function name, zero flag, registers, arrays and
    memory, and the final program counter is the `pcMap` image. -/
theorem lsemFuelMemF_lowerRM {isB : String → Bool} {movFor : String → String} {P : LprogM}
    (hP : LowerOK isB movFor P) (fuel : Nat) {s s' t : LstateMF}
    (hR : RelX EqPc (lowerRM isB movFor) P s s') (h : lsemFuelMemF P fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel * 2
      ∧ lsemFuelMemF ⟨P.lfn, P.body.flatMap (lowerRM isB movFor)⟩ fuel' s' = some t'
      ∧ RelX EqPc (lowerRM isB movFor) P t t' :=
  lsemFuelMemF_expand (P := P)
    (P' := ⟨P.lfn, P.body.flatMap (lowerRM isB movFor)⟩)
    ⟨rfl, rfl, fun _ _ hk => instrOK_lowerRM hP hk, fun _ _ p q hE => hE.setLpc p q⟩
    (fun i _ => lowerRM_length_le isB movFor i) fuel hR h


end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
