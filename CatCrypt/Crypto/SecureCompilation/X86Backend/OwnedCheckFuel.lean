/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked

@[expose] public section

set_option autoImplicit false

/-!
# Soundness of the register allocation checker at an explicit fuel

`OwnedLprogTVChecked.ownedCheckMC_sound` matches a halting checked run of a body `B` at fuel
`fuel` by a halting checked run of the rewritten body `B'` at some fuel. Its simulation
`SimAtC` goes by induction on the measure `fuel * (nb + 1) + (nb - k)`, for `nb` the number of
blocks of `B` and `k` the current block, and each step of that induction runs one block of
`B'`. The steps of the rewritten run in one step of the induction, by the terminator of the
block:

* fall through: the instructions of the block from its entry;
* jump, and branch (taken or not): those instructions and the terminator;
* the end of the body: none.

Each is at most `B'.length + 1`, and the induction takes at most the measure plus one steps,
so the rewritten run halts within `checkFuel B B' fuel
= (B'.length + 1) * (fuel * (nb + 1) + nb + 1)`. This module carries that bound through the
simulation (`SimAtCF`, `sim_stepCF`), states the soundness theorems with it, in the form "the
rewritten body halts in one state at every fuel from `checkFuel B B' fuel` on" for the
checked run, and derives the statements of `OwnedLprogTVChecked` from them.

## Main definitions

* `blockCount`: the number of blocks of the control-flow graph of a body.
* `checkFuel`: the fuel of the rewritten body.
* `SimAtCF`: the simulation `SimAtC` with the fuel of the rewritten run bounded by
  `(B'.length + 1) * N`.

## Main results

* `lsemFuelMemFk_add`: a halting checked run returns the same state at every larger fuel.
* `sim_stepCF`, `simAtCF_all`: the simulation with the fuel bound.
* `ownedCheckWithC_sound_at_fuel`: soundness for given live sets, the fuel of the rewritten
  run at most `checkFuel B B' fuel`.
* `ownedCheckMC_sound_at_fuel`, `ownedCheckMC_sound_fuel`: the rewritten body halts in one
  state at every fuel from `checkFuel B B' fuel` on, over an instruction set and at x86.
* `ownedCheckWithC_sound_at_of_fuel`, `ownedCheckMC_sound_at_of_fuel`,
  `ownedCheckMC_sound_of_fuel`: the statements of `ownedCheckWithC_sound_at`,
  `ownedCheckMC_sound_at` and `ownedCheckMC_sound`, from the forms at an explicit fuel.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedCheckFuel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
  (x86Isa x86Isa_lsemFuelMemF x86Isa_runL x86Isa_lsemFuelMemFk x86Isa_RunIdxOk)

/-! ## 1. The fuel of the rewritten body -/

/-- The number of blocks of the control-flow graph of a body, `0` when the body has none. -/
def blockCount (B : List LinstrRM) : Nat :=
  match cfgOf (B.map Prod.fst) with
  | some G => G.blocks.size
  | none => 0

/-- The fuel of the rewritten body `B'` for a run of `B` at fuel `fuel`. -/
def checkFuel (B B' : List LinstrRM) (fuel : Nat) : Nat :=
  (B'.length + 1) * (fuel * (blockCount B + 1) + blockCount B + 1)

theorem blockCount_eq {B : List LinstrRM} {G : CFG} (hG : cfgOf (B.map Prod.fst) = some G) :
    blockCount B = G.blocks.size := by
  unfold blockCount
  rw [hG]

/-- One step of the simulation adds at most `L + 1` to the fuel of the rewritten run. -/
theorem step_bound {L N m f : Nat} (hm : m ≤ L) (hf : f ≤ (L + 1) * N) :
    m + (f + 1) ≤ (L + 1) * (N + 1) := by
  rw [Nat.mul_add_one]
  omega

/-- A halting checked run returns the same state at every larger fuel. -/
theorem lsemFuelMemFk_add (I : Isa) (ck : Bool) (P : LprogM) :
    ∀ (n k : Nat) (s t : LstateMF), I.lsemFuelMemFk ck P n s = some t →
      I.lsemFuelMemFk ck P (n + k) s = some t := by
  intro n
  induction n with
  | zero =>
      intro k s t h
      simp only [Isa.lsemFuelMemFk] at h
      split at h
      · next hf => cases h; rw [Nat.zero_add]; exact I.lsemFuelMemFk_halt ck P k s hf
      · cases h
  | succ n ih =>
      intro k s t h
      rw [Nat.add_right_comm]
      simp only [Isa.lsemFuelMemFk] at h ⊢
      cases hf : findInstrMem P s.prog with
      | none => simp only [hf] at h ⊢; exact h
      | some i =>
          simp only [hf] at h ⊢
          cases hs : I.evalInstrPMemFk ck P i s with
          | none => simp only [hs, reduceCtorEq] at h
          | some s' => simp only [hs] at h ⊢; exact ih k s' t h

/-! ## 2. The simulation with the fuel bound -/

/-- The simulation `SimAtC` with the fuel of the rewritten run bounded: a halting source run
    in bounds from a block entry, of measure below `N`, is matched by a halting run in bounds
    of the rewritten body of at most `(B'.length + 1) * N` steps. -/
def SimAtCF (I : Isa) (outs : List String) (L : Nat → List String × Bool)
    (B B' : List LinstrRM) (G G' : CFG) (fn : String) (N : Nat) : Prop :=
  ∀ (fuel k : Nat) (s s' t : LstateMF),
    fuel * (G.blocks.size + 1) + (G.blocks.size - k) < N → k < G.blocks.size →
    Pair B B' (G.blk k) (G'.blk k) s.prog.base.reg.lpc s'.prog.base.reg.lpc →
    Rel (L k) s s' → s.prog.lfn = fn →
    I.lsemFuelMemF (singletonProgM fn B) fuel s = some t →
    I.RunIdxOk (singletonProgM fn B) fuel s →
    ∃ f' t', f' ≤ (B'.length + 1) * N ∧
      I.lsemFuelMemF (singletonProgM fn B') f' s' = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') f' s'

theorem fall_contCF {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    {outs : List String} {L : Nat → List String × Bool} {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : Checked outs L B B' G G' sym dec) {N k : Nat}
    (ih : SimAtCF I outs L B B' G G' fn N) (hk : k < G.blocks.size) {nx : Option Nat}
    (hn : G.next k = nx) (hn' : G'.next k = nx) {w w' t : LstateMF} {f0 : Nat}
    (hw : w.prog.base.reg.lpc = (G.blk k).stop) (hw' : w'.prog.base.reg.lpc = (G'.blk k).stop)
    (hfn : w.prog.lfn = fn) (hfn' : w'.prog.lfn = fn)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) f0 w = some t)
    (hok : I.RunIdxOk (singletonProgM fn B) f0 w)
    (hmeas : f0 * (G.blocks.size + 1) + (G.blocks.size - (k + 1)) < N)
    (hrel : ∀ j, nx = some j → Rel (L j) w w') (hobs : nx = none → Obs outs w w') :
    ∃ f' t', f' ≤ (B'.length + 1) * N ∧
      I.lsemFuelMemF (singletonProgM fn B') f' w' = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') f' w' := by
  have hk' : k < G'.blocks.size := hc.size ▸ hk
  cases nx with
  | none =>
      have e1 := (stop_next hc.hG hk).1 hn
      have e2 := (stop_next hc.hG' hk').1 hn'
      rw [halt_at_end_at I hfn (hw.trans e1)] at hrun
      cases hrun
      exact ⟨0, w', Nat.zero_le _, halt_at_end_at I hfn' (hw'.trans e2) 0, hobs rfl, trivial⟩
  | some j =>
      obtain ⟨hj, hjlt, e1⟩ := (stop_next hc.hG hk).2 j hn
      obtain ⟨-, -, e2⟩ := (stop_next hc.hG' hk').2 j hn'
      subst hj
      exact ih f0 (k + 1) w w' t hmeas hjlt (Or.inl ⟨hw.trans e1, hw'.trans e2⟩) (hrel _ rfl)
        hfn hrun hok

theorem jump_contCF {I : Isa} {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} {N tg : Nat} (ih : SimAtCF I outs L B B' G G' fn N)
    (htg : tg < G.blocks.size) {l l' : LLabel}
    (hl : findLabel l (B.map Prod.fst) = some (G.blk tg).start)
    (hl' : findLabel l' (B'.map Prod.fst) = some (G'.blk tg).start) {w w' t : LstateMF}
    {f1 : Nat} (hw : w.prog.base.reg.lpc = (G.blk tg).start + 1)
    (hw' : w'.prog.base.reg.lpc = (G'.blk tg).start + 1) (hfn : w.prog.lfn = fn)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) f1 w = some t)
    (hok : I.RunIdxOk (singletonProgM fn B) f1 w)
    (hmeas : f1 * (G.blocks.size + 1) + (G.blocks.size - tg) < N) (hrel : Rel (L tg) w w') :
    ∃ f' t', f' ≤ (B'.length + 1) * N ∧
      I.lsemFuelMemF (singletonProgM fn B') f' w' = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') f' w' :=
  ih f1 tg w w' t hmeas htg (Or.inr ⟨hw, label_at hl, hw', label_at hl'⟩) hrel hfn hrun hok

/-- **One step of the simulation with the fuel bound.** The step of `sim_stepC`: the
    rewritten run of the block costs at most `B'.length + 1` steps, by the terminator of the
    block (fall through, jump, branch taken, branch not taken). -/
theorem sim_stepCF {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hL : SymLaws I sym dec)
    {outs : List String} {L : Nat → List String × Bool} {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : Checked outs L B B' G G' sym dec)
    (hob : ∀ k < G.blocks.size, oblOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym = true)
    {N : Nat} (ih : SimAtCF I outs L B B' G G' fn N) :
    SimAtCF I outs L B B' G G' fn (N + 1) := by
  intro fuel k s s' t hN hk hpair hrel hfn hrun hokS
  obtain ⟨hTk, hok⟩ := hc.blk k hk
  have hk' : k < G'.blocks.size := hc.size ▸ hk
  have F := blockFacts hc.hG hk
  have F' := blockFacts hc.hG' hk'
  obtain ⟨hE, hE'⟩ := hpair.entry
  obtain ⟨hs1, hle⟩ := entry_le hc.hG hk hE
  obtain ⟨hs1', hle'⟩ := entry_le hc.hG' hk' hE'
  have hfn' : s'.prog.lfn = fn := hrel.1.trans hfn
  -- the source runs the block body
  have hplain := body_plain hc.hG hk hs1
  obtain ⟨u, f, hf, hu, hru⟩ :=
    fuel_runL_at hL.plain _ _ s t fuel hfn (drop_split B hle) hplain hrun
  have hokS' := hf ▸ hokS
  obtain ⟨hlS, hokU⟩ :=
    runIdxOk_runL_at hL.plain _ _ s u f hfn (drop_split B hle) hplain hu hokS'
  obtain ⟨hul, hup⟩ := runL_frame_at hL.plain _ s u hplain hu
  have hbstop : bstopOf (G.blk k).term (G.blk k) ≤ B.length := by
    unfold bstopOf; split <;> have := F.le <;> simp at this <;> omega
  have hbstop' : bstopOf (G'.blk k).term (G'.blk k) ≤ B'.length := by
    unfold bstopOf; split <;> have := F'.le <;> simp at this <;> omega
  simp only [List.length_take, List.length_drop] at hup hf
  have hupc : u.prog.base.reg.lpc = bstopOf (G.blk k).term (G.blk k) := by
    rw [hup]; omega
  have hul' : u.prog.lfn = fn := hul.trans hfn
  -- the last instruction of the source block
  have hlt : (G.blk k).stop - 1 < B.length := by have := F.le; have := F.lt; simp at *; omega
  obtain ⟨z, hz⟩ : ∃ z, B[(G.blk k).stop - 1]? = some z :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  have hterm := F.term
  rw [List.getElem?_map, hz, Option.map_some] at hterm
  have hlt' : (G'.blk k).stop - 1 < B'.length := by
    have := F'.le; have := F'.lt; simp at *; omega
  obtain ⟨z', hz'⟩ : ∃ z', B'[(G'.blk k).stop - 1]? = some z' :=
    ⟨_, List.getElem?_eq_getElem hlt'⟩
  have hterm' := F'.term
  rw [List.getElem?_map, hz', Option.map_some, hTk] at hterm'
  -- a block ending in `Lret` is never left by a halting run
  by_cases hret : (G.blk k).term = .ret
  · rcases termOk_spec hterm with ⟨_, hT, _⟩ | ⟨_, _, _, hT, _⟩ | ⟨_, _, _, _, hT, _⟩ | ⟨_, hzr⟩
    all_goals try (rw [hret] at hT; cases hT)
    have hupc2 : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by
      rw [hupc]; simp [bstopOf, hret]
    obtain ⟨_, _, _, he, _⟩ :=
      run_inv_at hru (by rw [findInstrMem_single hul', hupc2, hz])
    obtain ⟨zi, zt⟩ := z
    simp only at hzr
    subst hzr
    rw [hL.ret] at he
    cases he
  -- the symbolic runs of the two block bodies
  have hD := symRun_sound_at hL.step_sound (singletonProgM fn B)
    ((B.drop s.prog.base.reg.lpc).take
    (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)) SSt.start _ _ _ _ _ s
    (holds_start s)
  rw [symRun_entry_at hL.label hE hle] at hD
  rcases blockOk_spec hok hret with hfail | ⟨ss, gs, ss', gs', hS, hS', hgs, hta, hex⟩
  · rw [hfail] at hD
    simp only [SOut.DescN] at hD
    rw [hD] at hu
    cases hu
  rw [hS] at hD
  obtain ⟨hAll, hH, hFr⟩ := hD.1 u hu
  have hV : ∀ r ∈ (L k).1, s'.prog.base.reg.lvm r = s.prog.base.reg.lvm r := hrel.2.2.2.1
  have hH0' : Holds s'.prog.base.reg.lvm s.prog.base.larr s'.prog.base.cf s'.prog.base.of s'.zf
      SSt.start s' :=
    ⟨fun _ => rfl, fun q => by rw [hrel.2.1]; rfl, rfl, by simp [SSt.start, STerm.ev],
      by simp [SSt.start, STerm.ev]⟩
  rw [hTk] at hle'
  have hD' := symRun_sound_at hL.step_sound (singletonProgM fn B')
    ((B'.drop s'.prog.base.reg.lpc).take
    (bstopOf (G.blk k).term (G'.blk k) - s'.prog.base.reg.lpc)) SSt.start _ _ _ _ _ s' hH0'
  rw [symRun_entry_at hL.label hE' hle', hS'] at hD'
  have hAllN := allG_normG.mpr hAll
  have hAll' : AllG s'.prog.base.reg.lvm s.prog.base.larr s'.prog.base.cf s'.prog.base.of gs' :=
    allG_normG.mp fun g hg =>
      (SG.holds_congr _ g (fun r hr => (hV r ((hgs g hg).2.1 r hr)).symm)
        (fun e => by
          obtain ⟨-, hc, ho⟩ := hrel.2.2.2.2 ((hgs g hg).2.2 e)
          exact ⟨hc.symm, ho.symm⟩)).mp
      (hAllN g (hgs g hg).1)
  obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp (hD'.2 hAll')
  obtain ⟨-, hH', hFr'⟩ := hD'.1 u' hu'
  have hplain' := body_plain hc.hG' hk' hs1'
  rw [hTk] at hplain' hbstop'
  -- the index obligations: the source block is in bounds, so the rewritten block is
  have hOS := (symObl_sound_at hL.step_sound (singletonProgM fn B) _ SSt.start _ _ _ _ _ s u
    (holds_start s)
    ⟨ss, gs, by rw [symRun_entry_at hL.label hE hle]; exact hS⟩ hu).mp hlS
  rw [symObl_entry_at hL.label hE hle] at hOS
  have hO := oblOk_spec (hob k hk) hret hS
  have hlI : RunLOk (singletonProgM fn B') ((B'.drop s'.prog.base.reg.lpc).take
      (bstopOf (G.blk k).term (G'.blk k) - s'.prog.base.reg.lpc)) s' I := by
    refine (symObl_sound_at hL.step_sound (singletonProgM fn B') _ SSt.start _ _ _ _ _ s' u'
      hH0' ⟨ss', gs', by rw [symRun_entry_at hL.label hE' hle']; exact hS'⟩ hu').mpr
      fun o ho => ?_
    rw [symObl_entry_at hL.label hE' hle'] at ho
    obtain ⟨hoS, hvars, hfl⟩ := hO o ho
    have hev := STerm.ev_congr s.prog.base.larr o.1
      (V := s'.prog.base.reg.lvm) (V' := s.prog.base.reg.lvm)
      (C := s'.prog.base.cf) (O := s'.prog.base.of)
      (C' := s.prog.base.cf) (O' := s.prog.base.of)
      (fun r hr => hV r (hvars r hr))
      (fun e => by
        obtain ⟨-, hc, ho⟩ := hrel.2.2.2.2 (hfl e)
        exact ⟨hc, ho⟩)
    have h1 := hOS o hoS
    unfold SObl.holds at h1 ⊢
    rw [hev]
    exact h1
  have hrun' := runL_fuel_at hL.plain _ _ s' u' hfn' (drop_split B' hle') hplain' hu'
  have hokJ : ∀ f0, I.RunIdxOk (singletonProgM fn B') f0 u' →
      I.RunIdxOk (singletonProgM fn B') (((B'.drop s'.prog.base.reg.lpc).take
        (bstopOf (G.blk k).term (G'.blk k) - s'.prog.base.reg.lpc)).length + f0) s' :=
    fun f0 h0 =>
      runIdxOk_of_runL_at hL.plain _ _ s' u' f0 hfn' (drop_split B' hle') hplain' hu' hlI h0
  simp only [List.length_take, List.length_drop] at hrun' hokJ
  have hupc' : u'.prog.base.reg.lpc = bstopOf (G.blk k).term (G'.blk k) := by
    rw [hFr'.2.1]; simp only [List.length_take, List.length_drop]; omega
  have hul'' : u'.prog.lfn = fn := hFr'.1.trans hfn'
  obtain ⟨hsucc, hhalt⟩ := exit_rel hH hH' hV (fun hz => hrel.2.2.2.2 hz)
    (symRun_good_at hL.good _ SSt.good_start hS) (symRun_good_at hL.good _ SSt.good_start hS')
    (by rw [hul'', hul']) (by rw [hFr'.2.2, hrel.2.2.1, hFr.2.2]) hex
  have hfle : f ≤ fuel := by omega
  obtain ⟨m', hm', hmok, hmle⟩ : ∃ m',
      (∀ f0, I.lsemFuelMemF (singletonProgM fn B') (m' + f0) s' =
        I.lsemFuelMemF (singletonProgM fn B') f0 u') ∧
      (∀ f0, I.RunIdxOk (singletonProgM fn B') f0 u' →
        I.RunIdxOk (singletonProgM fn B') (m' + f0) s') ∧ m' ≤ B'.length :=
    ⟨_, hrun', hokJ, by omega⟩
  clear hrun' hokJ
  obtain ⟨zi, zt⟩ := z
  obtain ⟨zi', zt'⟩ := z'
  rw [hz, hz'] at hta
  simp only at hterm hterm'
  rcases termOk_spec hterm with ⟨nx, hT, _, hnx⟩ | ⟨tg, x, l, hT, hzi, htg, hl⟩ |
      ⟨tg, nx, c, l, hT, hzi, htg, hl, hnx⟩ | ⟨hT, _⟩
  · -- fall through
    obtain ⟨nx', hT', _, hnx'⟩ | ⟨_, _, _, hT', _⟩ | ⟨_, _, _, _, hT', _⟩ | ⟨hT', _⟩ :=
      termOk_spec hterm'
    all_goals rw [hT] at hT'
    all_goals try cases hT'
    have hw : u.prog.base.reg.lpc = (G.blk k).stop := by rw [hupc, hT]; rfl
    have hw' : u'.prog.base.reg.lpc = (G'.blk k).stop := by rw [hupc', hT]; rfl
    obtain ⟨f'', t', hfb, hr, hobs, hrok⟩ := fall_contCF hc ih hk hnx.symm hnx'.symm hw hw' hul'
      hul'' hru hokU (measure_le hN hfle hk)
      (fun j hj => hsucc j (by simp [hT, Term.succs, hj]))
      (fun hn => hhalt (by simp [hT, hn, Term.halts]))
    exact ⟨m' + f'', t',
      Nat.le_trans (Nat.add_le_add_left (Nat.le_succ f'') m') (step_bound hmle hfb),
      by rw [hm']; exact hr, hobs, hmok _ hrok⟩
  · -- jump
    obtain ⟨_, hT', _⟩ | ⟨tg', x', l', hT', hzi', htg', hl'⟩ | ⟨_, _, _, _, hT', _⟩ |
        ⟨hT', _⟩ := termOk_spec hterm'
    all_goals rw [hT] at hT'
    all_goals try cases hT'
    subst hzi hzi'
    have hxx : x = x' := by simpa [termAgree, hT] using hta
    subst hxx
    have hw : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by rw [hupc, hT]; rfl
    have hw' : u'.prog.base.reg.lpc = (G'.blk k).stop - 1 := by rw [hupc', hT]; rfl
    have hfetch : findInstrMem (singletonProgM fn B) u.prog = some (.Lgoto (x, l), zt) := by
      rw [findInstrMem_single hul', hw, hz]
    obtain ⟨f1, u1, hf1, he, hr1⟩ := run_inv_at hru hfetch
    have hok1 := runIdxOk_next_at hfetch he (hf1 ▸ hokU)
    rw [I.step_goto] at he
    by_cases hx : x = (singletonProgM fn B).lfn
    · rw [if_pos hx, evalJumpMem_single hl] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      have he' : I.step (singletonProgM fn B') (.Lgoto (x, l'), zt') u' =
          some { u' with prog := { u'.prog with
            base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } } := by
        rw [I.step_goto, if_pos (by simpa [singletonProgM, hul'', hul'] using hx),
          evalJumpMem_single hl']
        rfl
      have hfetch' : findInstrMem (singletonProgM fn B') u'.prog =
          some (.Lgoto (x, l'), zt') := by
        rw [findInstrMem_single hul'', hw', hz']
      obtain ⟨f'', t', hfb, hr, hobs, hrok⟩ := jump_contCF
        (w' := { u' with prog := { u'.prog with
          base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } }) ih htg hl hl' rfl rfl
        (by exact hul') hr1 hok1
        (measure_lt hN (show f1 + 1 ≤ fuel by omega)) (hsucc tg (by simp [hT, Term.succs]))
      refine ⟨m' + (f'' + 1), t', step_bound hmle hfb, ?_, hobs,
        hmok _ (runIdxOk_step_at hfetch' (idxOkB_goto _ _ _ _) he' hrok)⟩
      rw [hm', I.lsemFuelMemF_step _ _ _ _ _ hfetch' he']
      exact hr
    · rw [if_neg hx] at he
      cases he
  · -- branch
    obtain ⟨_, hT', _⟩ | ⟨_, _, _, hT', _⟩ | ⟨tg', nx', c', l', hT', hzi', htg', hl', hnx'⟩ |
        ⟨hT', _⟩ := termOk_spec hterm'
    all_goals rw [hT] at hT'
    all_goals try cases hT'
    subst hzi hzi'
    simp only [termAgree, hT, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
      Bool.not_eq_true'] at hta
    obtain ⟨⟨hdeq, hdv⟩, hdz⟩ := hta
    have hdec : I.condEval u' c' = I.condEval u c := by
      rw [hL.dec_sound hH' c', hL.dec_sound hH c, ← hdeq]
      exact SDec.ev_congr _ _ (fun r hr => hV r (vIn_spec hdv r hr))
        (fun hz => hrel.2.2.2.2 (by
          rcases hdz with h | h
          · rw [hz] at h; cases h
          · exact h))
    have hw : u.prog.base.reg.lpc = (G.blk k).stop - 1 := by rw [hupc, hT]; rfl
    have hw' : u'.prog.base.reg.lpc = (G'.blk k).stop - 1 := by rw [hupc', hT]; rfl
    have hfetch : findInstrMem (singletonProgM fn B) u.prog = some (.Lcond c l, zt) := by
      rw [findInstrMem_single hul', hw, hz]
    have hfetch' : findInstrMem (singletonProgM fn B') u'.prog = some (.Lcond c' l', zt') := by
      rw [findInstrMem_single hul'', hw', hz']
    obtain ⟨f1, u1, hf1, he, hr1⟩ := run_inv_at hru hfetch
    have hok1 := runIdxOk_next_at hfetch he (hf1 ▸ hokU)
    rw [I.step_cond] at he
    have hstop : 0 < (G.blk k).stop := by have := F.lt; omega
    have hstop' : 0 < (G'.blk k).stop := by have := F'.lt; omega
    by_cases hd : I.condEval u c = true
    · rw [if_pos hd, evalJumpMem_single hl] at he
      simp only [Option.map_some, Option.some.injEq] at he
      subst he
      have he' : I.step (singletonProgM fn B') (.Lcond c' l', zt') u' =
          some { u' with prog := { u'.prog with
            base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } } := by
        rw [I.step_cond, if_pos (hdec.trans hd), evalJumpMem_single hl']
        rfl
      obtain ⟨f'', t', hfb, hr, hobs, hrok⟩ := jump_contCF
        (w' := { u' with prog := { u'.prog with
          base := u'.prog.base.setLpc ((G'.blk tg).start + 1) } }) ih htg hl hl' rfl rfl
        (by exact hul') hr1 hok1
        (measure_lt hN (show f1 + 1 ≤ fuel by omega)) (hsucc tg (by simp [hT, Term.succs]))
      refine ⟨m' + (f'' + 1), t', step_bound hmle hfb, ?_, hobs,
        hmok _ (runIdxOk_step_at hfetch' (idxOkB_cond _ _ _ _) he' hrok)⟩
      rw [hm', I.lsemFuelMemF_step _ _ _ _ _ hfetch' he']
      exact hr
    · rw [if_neg hd] at he
      simp only [Option.some.injEq] at he
      have he' : I.step (singletonProgM fn B') (.Lcond c' l', zt') u' =
          some { u' with prog := { u'.prog with base := u'.prog.base.nextPc } } := by
        rw [I.step_cond, if_neg (by rw [hdec]; exact hd)]
      obtain ⟨f'', t', hfb, hr, hobs, hrok⟩ := fall_contCF (w := u1)
        (w' := { u' with prog := { u'.prog with base := u'.prog.base.nextPc } })
        hc ih hk hnx.symm hnx'.symm
        (by rw [← he]; show u.prog.base.reg.lpc + 1 = _; omega)
        (by show u'.prog.base.reg.lpc + 1 = _; omega)
        (by rw [← he]; exact hul') hul'' hr1 hok1
        (measure_le hN (show f1 ≤ fuel by omega) hk)
        (fun j hj => by rw [← he]; exact hsucc j (by simp [hT, Term.succs, hj]))
        (fun hn => by rw [← he]; exact hhalt (by simp [hT, hn, Term.halts]))
      refine ⟨m' + (f'' + 1), t', step_bound hmle hfb, ?_, hobs,
        hmok _ (runIdxOk_step_at hfetch' (idxOkB_cond _ _ _ _) he' hrok)⟩
      rw [hm', I.lsemFuelMemF_step _ _ _ _ _ hfetch' he']
      exact hr
  · exact absurd hT hret

theorem simAtCF_all {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hL : SymLaws I sym dec) {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : Checked outs L B B' G G' sym dec)
    (hob : ∀ k < G.blocks.size,
      oblOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym = true) :
    ∀ N, SimAtCF I outs L B B' G G' fn N
  | 0 => fun _ _ _ _ _ hN => absurd hN (Nat.not_lt_zero _)
  | N + 1 => sim_stepCF hL hc hob (simAtCF_all hL hc hob N)

/-! ## 3. Soundness at an explicit fuel -/

/-- **Soundness for given live sets, with the fuel bound.** Under the hypotheses of
    `ownedCheckWithC_sound_at`, the matching run of `B'` has fuel at most
    `checkFuel B B' fuel`. -/
theorem ownedCheckWithC_sound_at_fuel {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec)
    {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM} (h : ownedCheckWith outs L B B' sym dec = true)
    (hob : oblCheckWith L B B' sym = true) (fn : String)
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t)
    (hok : I.RunIdxOk (singletonProgM fn B) fuel s) :
    ∃ fuel' t', fuel' ≤ checkFuel B B' fuel ∧
      I.lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') fuel' s := by
  unfold ownedCheckWith at h
  unfold oblCheckWith at hob
  split at h
  · rename_i G G' hG hG'
    rw [hG, hG'] at hob
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, beq_iff_eq,
      List.all_eq_true, List.mem_range] at h hob
    obtain ⟨⟨⟨hne, hne'⟩, hsz⟩, hblk⟩ := h
    have hc : Checked outs L B B' G G' sym dec :=
      ⟨hG, hG', hsz.symm, fun k hk => ⟨(hblk k hk).1.symm, (hblk k hk).2⟩⟩
    have hwl : B.map Prod.fst ≠ [] := by simpa using hne
    have hwl' : B'.map Prod.fst ≠ [] := by simpa using hne'
    obtain ⟨h0, hs0⟩ := cfgOf_start_zero hG hwl
    obtain ⟨-, hs0'⟩ := cfgOf_start_zero hG' hwl'
    have hsim := simAtCF_all hL hc hob
      (fuel * (G.blocks.size + 1) + (G.blocks.size - 0) + 1) fuel 0 s s t
      (Nat.lt_succ_self _) h0
      (Or.inl ⟨hpc.trans hs0.symm, hpc.trans hs0'.symm⟩)
      ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩ hfn hrun hok
    unfold checkFuel
    rw [blockCount_eq hG]
    rw [Nat.sub_zero] at hsim
    exact hsim
  · cases h

/-- **Soundness of the checker at an explicit fuel, over an instruction set.** Under the
    hypotheses of `ownedCheckMC_sound_at`, the checked run of the singleton program over `B'`
    halts in one state at every fuel from `checkFuel B B' fuel` on, and that state agrees
    with the end state of the run of `B` on the registers `outs`, the arrays and the word
    memory. -/
theorem ownedCheckMC_sound_at_fuel {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec) (hS : SymSubst sym dec)
    {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMC outs B B' sym dec = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : I.lsemFuelMemFk true (singletonProgM fn B) fuel s = some t) :
    ∃ t', (∀ k, checkFuel B B' fuel ≤ k →
        I.lsemFuelMemFk true (singletonProgM fn B') k s = some t') ∧ Obs outs t t' := by
  obtain ⟨L, hL', hO⟩ := ownedCheckMC_with_at hS h
  obtain ⟨f', t', hf, hr, hobs, hok⟩ := ownedCheckWithC_sound_at_fuel hL hL' hO fn s t hfn hpc
    fuel (I.lsemFuelMemF_of_checked _ fuel s t hrun) (I.runIdxOk_of_checked _ fuel s t hrun)
  refine ⟨t', fun k hk => ?_, hobs⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (hf.trans hk)
  exact lsemFuelMemFk_add I true _ f' d s t' (I.lsemFuelMemFk_of_runIdxOk true _ f' s t' hr hok)

/-- **Soundness of the checker at an explicit fuel.** Under the hypotheses of
    `ownedCheckMC_sound`, the checked run (`lsemFuelMemFk true`) of the singleton program over
    `B'` halts in one state at every fuel from `checkFuel B B' fuel` on, and that state
    agrees with the end state of the run of `B` on the registers `outs`, the arrays and the
    word memory. -/
theorem ownedCheckMC_sound_fuel {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMC outs B B' = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : lsemFuelMemFk true (singletonProgM fn B) fuel s = some t) :
    ∃ t', (∀ k, checkFuel B B' fuel ≤ k →
        lsemFuelMemFk true (singletonProgM fn B') k s = some t') ∧ Obs outs t t' := by
  rw [← x86Isa_lsemFuelMemFk] at hrun
  simpa only [x86Isa_lsemFuelMemFk] using
    ownedCheckMC_sound_at_fuel symLaws_x86 symSubst_x86 h fn s t hfn hpc fuel hrun

/-! ## 4. The statements with an existential fuel -/

/-- The statement of `ownedCheckWithC_sound_at`, from `ownedCheckWithC_sound_at_fuel`. -/
theorem ownedCheckWithC_sound_at_of_fuel {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec)
    {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM} (h : ownedCheckWith outs L B B' sym dec = true)
    (hob : oblCheckWith L B B' sym = true) (fn : String)
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn B) fuel s = some t)
    (hok : I.RunIdxOk (singletonProgM fn B) fuel s) :
    ∃ fuel' t', I.lsemFuelMemF (singletonProgM fn B') fuel' s = some t' ∧ Obs outs t t' ∧
      I.RunIdxOk (singletonProgM fn B') fuel' s := by
  obtain ⟨f', t', -, hrest⟩ := ownedCheckWithC_sound_at_fuel hL h hob fn s t hfn hpc fuel hrun
    hok
  exact ⟨f', t', hrest⟩

/-- The statement of `ownedCheckMC_sound_at`, from `ownedCheckMC_sound_at_fuel` at the fuel
    `checkFuel B B' fuel`. -/
theorem ownedCheckMC_sound_at_of_fuel {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec) (hS : SymSubst sym dec)
    {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMC outs B B' sym dec = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : I.lsemFuelMemFk true (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', I.lsemFuelMemFk true (singletonProgM fn B') fuel' s = some t' ∧
      Obs outs t t' := by
  obtain ⟨t', hk, hobs⟩ := ownedCheckMC_sound_at_fuel hL hS h fn s t hfn hpc fuel hrun
  exact ⟨_, t', hk _ (Nat.le_refl _), hobs⟩

/-- The statement of `ownedCheckMC_sound`, from `ownedCheckMC_sound_fuel` at the fuel
    `checkFuel B B' fuel`. -/
theorem ownedCheckMC_sound_of_fuel {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckMC outs B B' = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : lsemFuelMemFk true (singletonProgM fn B) fuel s = some t) :
    ∃ fuel' t', lsemFuelMemFk true (singletonProgM fn B') fuel' s = some t' ∧
      Obs outs t t' := by
  obtain ⟨t', hk, hobs⟩ := ownedCheckMC_sound_fuel h fn s t hfn hpc fuel hrun
  exact ⟨_, t', hk _ (Nat.le_refl _), hobs⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedCheckFuel
