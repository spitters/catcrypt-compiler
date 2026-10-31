/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower

/-!
# Instruction expansion under a position-indexed relation

`JasminLsemExportLower.lsemFuelMemF_expand` matches every halting run of a program `P` on the
flag machine `lsemFuelMemF` by a halting run of `P.body.flatMap expand`, under a relation `Q`
on base states that does not depend on the position. This module states the same simulation for
a family of relations `R k` indexed by the source position `k`: the relation at a state is the
member of the family at its source program counter.

The per-instruction condition `InstrOKQ R expand P k i` at source position `k` asks that a
straight instruction step from `R k` be matched by its expansion reaching `R (k + 1)`, and that a
control instruction expand to itself and transport `R k` to `R k'` under program-counter writes
for each successor position `k'`: `k + 1` for a label and a fall-through, and the position after
the target label for a jump (`NextQ`, `JumpQ`).

## Main results

* `ExpProgQ.shape`: the shape part of an indexed expansion is an `ExpProg` at the empty relation,
  so the label lemmas of `JasminLsemExportLower` apply.
* `evalInstrPMemF_expandQ`: one source step is matched by `(expand i).length` target steps.
* `lsemFuelMemF_expandQ`: every halting run of `P` is matched by a halting run of the expanded
  program with fuel at most `fuel * m`, the final states related by `RelXQ`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.LsemExpandQ

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower

section Sim

variable (R : Nat → LstateM → LstateM → Prop) (expand : LinstrRM → List LinstrRM)

/-- The family `R` passes from position `k` to position `k'` under writes of the two program
    counters. -/
def NextQ (k k' : Nat) : Prop :=
  ∀ a b p q, R k a b → R k' (a.setLpc p) (b.setLpc q)

/-- A jump from position `k` to label `l` of `P` passes `R k` to the family member at the
    position after the label. -/
def JumpQ (P : LprogM) (k : Nat) (l : LLabel) : Prop :=
  ∀ pc, findLabelMem l P.body = some pc → NextQ R k (pc + 1)

/-- The condition on the instruction `i` at position `k` of the source program `P`. Either it
    is an `Lopn` whose expansion is a list of `Lopn`s that, run as a straight segment from an
    `R k`-related state, reaches an `R (k + 1)`-related state with the same zero flag; or it
    expands to itself and is a label passing `R k` to `R (k + 1)`, a zero-flag conditional
    passing `R k` to `R (k + 1)` and to the member after its target label, or a goto passing
    `R k` to the member after its target label. -/
def InstrOKQ (P : LprogM) (k : Nat) (i : LinstrRM) : Prop :=
  (IsLopn i ∧ (∀ j ∈ expand i, IsLopn j) ∧
    ∀ (s s' t : LstateM) (zf zt : Bool), R k s s' → fstepF i s zf = some (t, zt) →
      ∃ t', runStraightF (expand i) s' zf = some (t', zt) ∧ R (k + 1) t t')
  ∨ (expand i = [i] ∧
      ((∃ kd l, i.1 = LinstrR.Llabel kd l ∧ NextQ R k (k + 1))
        ∨ (∃ c l pl, i.1 = LinstrR.Lcond c l ∧ flagCondCC? i = some pl
            ∧ NextQ R k (k + 1) ∧ JumpQ R P k pl.2)
        ∨ (∃ fn l, i.1 = LinstrR.Lgoto (fn, l) ∧ JumpQ R P k l)))

/-- The two programs of an indexed expansion simulation: the same function name, the target
    body is the expanded source body, and every source instruction satisfies `InstrOKQ` at its
    position. -/
structure ExpProgQ (P P' : LprogM) : Prop where
  /-- The function names agree. -/
  lfn : P'.lfn = P.lfn
  /-- The target body is the expansion of the source body. -/
  body : P'.body = P.body.flatMap expand
  /-- Every source instruction satisfies the per-instruction condition at its position. -/
  inst : ∀ (k : Nat) (i : LinstrRM), P.body[k]? = some i → InstrOKQ R expand P k i

/-- The state relation of the indexed simulation: function name and zero flag agree, the target
    program counter is the image of the source one under `pcMap`, and the bases are related by
    the member of `R` at the source program counter. -/
structure RelXQ (P : LprogM) (s s' : LstateMF) : Prop where
  /-- The function names agree. -/
  lfn : s'.prog.lfn = s.prog.lfn
  /-- The zero flags agree. -/
  zf : s'.zf = s.zf
  /-- The target program counter is the mapped source program counter. -/
  pc : s'.prog.base.lpc = pcMap expand P.body s.prog.base.lpc
  /-- The bases are related at the source program counter. -/
  base : R s.prog.base.lpc s.prog.base s'.prog.base

variable {R expand}

/-- The shape of an indexed expansion is an expansion at the empty relation. -/
theorem ExpProgQ.shape {P P' : LprogM} (hP : ExpProgQ R expand P P') :
    ExpProg (fun _ _ => False) expand P P' where
  lfn := hP.lfn
  body := hP.body
  inst := by
    intro k i hi
    rcases hP.inst k i hi with ⟨hl, hex, _⟩ | ⟨hself, hc⟩
    · exact Or.inl ⟨hl, hex, fun _ _ _ _ _ h => h.elim⟩
    · refine Or.inr ⟨hself, ?_⟩
      rcases hc with ⟨kd, l, h, _⟩ | ⟨c, l, pl, h, hcc, _, _⟩ | ⟨fn, l, h, _⟩
      · exact Or.inl ⟨kd, l, h⟩
      · exact Or.inr (Or.inl ⟨c, l, h, by rw [hcc]; simp⟩)
      · exact Or.inr (Or.inr ⟨(fn, l), h⟩)
  pc := fun _ _ _ _ h => h.elim

/-- A jump of the source program is matched by the same jump of the target, into states
    related at the position after the label. -/
theorem evalJumpMem_expandQ {P P' : LprogM} (hP : ExpProgQ R expand P P') (l : LLabel)
    {k : Nat} (hJ : JumpQ R P k l) {p p' q : LstatePM} (hQ : R k p.base p'.base)
    (hfn : p'.lfn = p.lfn) (h : evalJumpMem P l p = some q) :
    ∃ q', evalJumpMem P' l p' = some q' ∧ R q.base.lpc q.base q'.base ∧ q'.lfn = q.lfn
      ∧ q'.base.lpc = pcMap expand P.body q.base.lpc := by
  unfold evalJumpMem at h ⊢
  rw [findLabelMem_flatMap hP.shape l]
  cases hl : findLabelMem l P.body with
  | none => simp [hl] at h
  | some pc =>
      simp only [hl, Option.map_some] at h ⊢
      cases h
      exact ⟨_, rfl, hJ pc hl _ _ _ _ hQ, hfn, (pcMap_succ_of_findLabelMem hP.shape hl).symm⟩

/-- **One source step.** A successful step of the source program at instruction `i` is matched
    by `(expand i).length` steps of the target program from a related state, into a state
    related at the successor position. -/
theorem evalInstrPMemF_expandQ {P P' : LprogM} (hP : ExpProgQ R expand P P')
    {s s' u : LstateMF} {i : LinstrRM} (hR : RelXQ R expand P s s')
    (hfn : s.prog.lfn = P.lfn) (hget : P.body[s.prog.base.lpc]? = some i)
    (he : evalInstrPMemF P i s = some u) :
    ∃ u', (∀ f, lsemFuelMemF P' ((expand i).length + f) s' = lsemFuelMemF P' f u')
      ∧ RelXQ R expand P u u' := by
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
    · have h1 := runStraightF_lpc _ _ _ _ _ hb'
      have h2 := fstepF_lpc_succ _ _ _ _ _ hb
      refine ⟨hR.lfn, rfl, ?_, ?_⟩
      · change b'.lpc = pcMap expand P.body b.lpc
        rw [h1, h2, pcMap_succ expand hget, hR.pc]
      · change R b.lpc b b'
        rw [h2]
        exact hQb
  · have hfetch : findInstrMem P' s'.prog = some i := by
      unfold findInstrMem
      rw [ite_eq_left hfn']
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
    rcases hctl with ⟨kd, l, hw, hN⟩ | ⟨c, l, pl, hw, hcc, hN, hJ⟩ | ⟨fn, l, hw, hJ⟩
    · obtain rfl : wire = LinstrR.Llabel kd l := hw
      rw [evalInstrPMemF_label] at he
      cases he
      exact ⟨_, hone (evalInstrPMemF_label P' kd l tag s'),
        ⟨hR.lfn, hR.zf, hnext.symm, hN _ _ _ _ hR.base⟩⟩
    · obtain rfl : wire = LinstrR.Lcond c l := hw
      have h1 : cmpArgs? (LinstrR.Lcond c l, tag) = none := rfl
      have h2 : movRegArgs? (LinstrR.Lcond c l, tag) = none := rfl
      obtain ⟨pol, lbl⟩ := pl
      unfold evalInstrPMemF at he
      simp only [h1, h2, hcc] at he
      split at he
      · rename_i hz
        obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp he
        obtain ⟨q', hq', hQq, hfq, hpq⟩ := evalJumpMem_expandQ hP lbl hJ hR.base hR.lfn hq
        refine ⟨{ s' with prog := q' }, hone ?_, ⟨hfq, hR.zf, hpq, hQq⟩⟩
        unfold evalInstrPMemF
        simp only [h1, h2, hcc]
        rw [ite_eq_left (hR.zf.trans hz), hq']; rfl
      · rename_i hz
        cases he
        refine ⟨{ s' with prog := { s'.prog with base := s'.prog.base.nextPc } },
          hone ?_, ⟨hR.lfn, hR.zf, hnext.symm, hN _ _ _ _ hR.base⟩⟩
        unfold evalInstrPMemF
        simp only [h1, h2, hcc]
        rw [ite_eq_right (fun h => hz (hR.zf.symm.trans h))]
    · obtain rfl : wire = LinstrR.Lgoto (fn, l) := hw
      have hev : ∀ (Rp : LprogM) (x : LstateMF),
          evalInstrPMemF Rp (LinstrR.Lgoto (fn, l), tag) x
            = (if fn = Rp.lfn then evalJumpMem Rp l x.prog else none).map
                (fun p => { x with prog := p }) := fun Rp x => by
        rw [evalInstrPMemF_delegate Rp _ x rfl rfl rfl rfl rfl rfl]; rfl
      rw [hev] at he
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp he
      split at hq
      · rename_i hf
        obtain ⟨q', hq', hQq, hfq, hpq⟩ := evalJumpMem_expandQ hP l hJ hR.base hR.lfn hq
        refine ⟨{ s' with prog := q' }, hone ?_, ⟨hfq, hR.zf, hpq, hQq⟩⟩
        rw [hev, hP.lfn, ite_eq_left hf, hq']; rfl
      · exact absurd hq (by simp)

/-- **The flag machine under an indexed instruction expansion.** Every halting run of `P` is
    matched, from a related state, by a halting run of the expanded program into a related
    state. The target run takes `(expand i).length` steps for each source step at instruction
    `i`, so its fuel is at most `fuel * m` for a bound `m` on the expansion lengths. -/
theorem lsemFuelMemF_expandQ {P P' : LprogM} (hP : ExpProgQ R expand P P') {m : Nat}
    (hm : ∀ i ∈ P.body, (expand i).length ≤ m) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, RelXQ R expand P s s' →
      lsemFuelMemF P fuel s = some t →
      ∃ fuel' t', fuel' ≤ fuel * m ∧ lsemFuelMemF P' fuel' s' = some t'
        ∧ RelXQ R expand P t t' := by
  have hhalt : ∀ {s s' : LstateMF}, RelXQ R expand P s s' →
      findInstrMem P s.prog = none → findInstrMem P' s'.prog = none := by
    intro s s' hR hf
    unfold findInstrMem at hf ⊢
    rw [hR.lfn, hP.lfn]
    split
    · rename_i hfn
      rw [ite_eq_left hfn] at hf
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
              obtain ⟨u', hrun, hRu⟩ := evalInstrPMemF_expandQ hP hR hfg.1 hfg.2 he
              obtain ⟨f', t', hf', hrun', hRt⟩ := ih hRu h
              have hlen := hm i (List.mem_of_getElem? hfg.2)
              refine ⟨(expand i).length + f', t', ?_, by rw [hrun]; exact hrun', hRt⟩
              rw [Nat.succ_mul]
              omega

end Sim

end CatCrypt.Crypto.SecureCompilation.Haxc.LsemExpandQ
