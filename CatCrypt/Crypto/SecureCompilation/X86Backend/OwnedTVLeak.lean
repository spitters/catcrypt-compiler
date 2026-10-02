/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak

@[expose] public section

set_option autoImplicit false

/-!
# The register allocation checker on traced runs

The traced flag machine `lsemFuelMemFLeak` emits, at each step, the address events of the
array operands of an `Lopn` (`opLeakF`: the array name with the element offset) and the
branch event of a conditional (`instrLeakF`). The events of a block body are a function of
the symbolic run of the body (`symLeak`): an array operand `b[x * sc]` emits the address
event of `b` at `sc` times the value of the symbolic word of `x`, a compile-time element
`b[i]` the event of `b` at `i`. Register moves, frame-word moves and labels emit nothing.

`leakCheckWith` asks, at every block pair the checker `ownedCheckM` compares, that the
symbolic events of the rewritten block are those of the source block, over registers (and
flags) live at the block. Array names are not renamed by the checker (the two runs share
their arrays), and the branch events agree because the checker already compares the
symbolic branch conditions. Under `ownedCheckWith` and `leakCheckWith`, two halting traced
runs of the source and of the rewritten body from one state have one trace. `ownedCheckML`
is `ownedCheckMC` with `leakCheckWith` at its live sets.

## Main definitions

* `SEv`, `opSLeak`, `instrSLeak`, `symLeak`: symbolic events and their collection.
* `leakL`: the events of a straight-line stretch.
* `leakOk`, `leakCheckWith`, `ownedCheckML`: the checks.
* `TVPub`: public-equal entry states of the source that have halting checked runs.

## Main results

* `instrLeakF_holds`, `leakL_sound`: the events of a stretch from its symbolic run.
* `fuel_runLLeak`, `run_invL`: traced runs through a stretch and through one step.
* `ownedCheckWithL_trace`, `ownedCheckML_trace`: one trace for the source and the rewritten
  body.
* `ownedCheckML_sound_leak`: a halting checked traced run of the source is matched by a
  halting checked run of the rewritten body with the same trace.
* `memFCT_of_ownedCheckML`: constant time of the source gives constant time of the
  rewritten body.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedTVLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemChecked
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (findLabel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTimeRel)

/-! ## 1. Symbolic events -/

/-- A symbolic leakage event: the address event of an array operand at a register index
    (`addr b sc t`: the element offset `sc` times the value of `t` in the array `b`) or at a
    compile-time element offset (`addrK b i`). -/
inductive SEv where
  | addr (b : String) (sc : Nat) (t : STerm)
  | addrK (b : String) (i : Nat)
  deriving DecidableEq

/-- The event a symbolic event denotes, for the start registers `V`, arrays `A` and carry
    and overflow flags `C`, `O`. -/
def SEv.ev (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool) : SEv → CTLeak
  | .addr b sc t => .addr b (Int.ofNat (sc * (t.ev V A C O).2.toNat))
  | .addrK b i => .addr b (Int.ofNat i)

/-- The start registers a symbolic event reads. -/
def SEv.vars : SEv → List String
  | .addr _ _ t => t.vars
  | .addrK _ _ => []

/-- The symbolic event reads a start flag. -/
def SEv.readsF : SEv → Bool
  | .addr _ _ t => t.readsF
  | .addrK _ _ => false

theorem SEv.ev_congr {V V' : String → Σ w, BitVec w} (A : String → ArrCell)
    {C O C' O' : Bool} (e : SEv) (h : ∀ r ∈ e.vars, V r = V' r)
    (hf : e.readsF = true → C = C' ∧ O = O') : e.ev V A C O = e.ev V' A C' O' := by
  cases e with
  | addr b sc t => simp only [SEv.ev]; rw [STerm.ev_congr A t h hf]
  | addrK b i => rfl

/-- The symbolic events of an operand from the symbolic state `ss`. -/
def opSLeak (ss : SSt) : LOperand → List SEv
  | .arr b i => [.addrK b i]
  | .arrIdx b x sc => [.addr b sc (ss.regs x)]
  | _ => []

/-- The symbolic events of an instruction from the symbolic state `ss`: those of the
    operands of an `Lopn` other than a load-effective-address `LEA`, which accesses no
    memory. -/
def instrSLeak (i : LinstrRM) (ss : SSt) : List SEv :=
  match i.1 with
  | .Lopn ds o xs => if stripWidthTag o = "LEA" then [] else (ds ++ xs).flatMap (opSLeak ss)
  | _ => []

/-- The symbolic events of a list of instructions, collected along its symbolic run. -/
def symLeak : List LinstrRM → SSt → List SEv
  | [], _ => []
  | i :: is, ss =>
      instrSLeak i ss ++
        match symStep i ss with
        | .ok ss1 _ => symLeak is ss1
        | _ => []

theorem symLeak_label {i : LinstrRM} (h : isLbl i = true) (is : List LinstrRM) (ss : SSt) :
    symLeak (i :: is) ss = symLeak is ss := by
  obtain ⟨x, tag⟩ := i
  have hx : instrSLeak (x, tag) ss = [] := by
    cases x <;> simp_all [isLbl, instrSLeak]
  simp only [symLeak, hx, symStep_label h, List.nil_append]

theorem symLeak_entry {B : List LinstrRM} {b : Block} {T : Term} {p : Nat}
    (hp : EntryAt B b p) (hle : p ≤ bstopOf T b) :
    symLeak ((B.drop p).take (bstopOf T b - p)) SSt.start =
      symLeak (bodyAt B b T) SSt.start := by
  rcases hp with rfl | ⟨rfl, x, hx, hl⟩
  · rfl
  · unfold bodyAt
    rw [take_cons B (by omega) hx, symLeak_label hl]

/-! ## 2. The events of a stretch -/

/-- The events of the flag-machine steps of a list of instructions, in order. -/
def leakL (P : LprogM) : List LinstrRM → LstateMF → List CTLeak
  | [], _ => []
  | i :: is, s =>
      instrLeakF i s ++
        match evalInstrPMemF P i s with
        | some s1 => leakL P is s1
        | none => []

/-- **The events of a non-terminator from its symbolic description.** -/
theorem instrLeakF_holds {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O Z : Bool}
    {ss : SSt} {s : LstateMF} (hs : Holds V A C O Z ss s) (i : LinstrRM)
    (hi : isTermR i.1 = false) : instrLeakF i s = (instrSLeak i ss).map (SEv.ev V A C O) := by
  obtain ⟨x, tag⟩ := i
  cases x with
  | Lopn ds o xs =>
      simp only [instrLeakF, flagCondCC?, instrLeakB, instrSLeak]
      split_ifs
      · rfl
      simp only [List.map_flatMap]
      refine congrArg (fun g => List.flatMap g (ds ++ xs)) (funext fun op => ?_)
      cases op with
      | arrIdx b x sc =>
          simp only [opLeakF, opSLeak, SEv.ev, idxVal, List.map_cons, List.map_nil]
          rw [hs.1 x]
      | arr b i => simp [opLeakF, opSLeak, SEv.ev]
      | reg r => simp [opLeakF, opSLeak]
      | imm n => simp [opLeakF, opSLeak]
  | Lcond c l => simp [isTermR] at hi
  | Lgoto _ => simp [isTermR] at hi
  | Lret => simp [isTermR] at hi
  | _ => rfl

/-- **The events of a stretch are the symbolic events of its symbolic run**, for a run of a
    stretch of non-terminators from a state the start of a successful symbolic run
    describes. -/
theorem leakL_sound (P : LprogM) :
    ∀ (is : List LinstrRM) (ss : SSt) (V : String → Σ w, BitVec w) (A : String → ArrCell)
      (C O Z : Bool) (s u : LstateMF), Holds V A C O Z ss s →
      (∀ x ∈ is, isTermR x.1 = false) →
      (∃ ss' gs, symRun is ss = .ok ss' gs) → runL P is s = some u →
      leakL P is s = (symLeak is ss).map (SEv.ev V A C O)
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => by simp [leakL, symLeak]
  | i :: is, ss, V, A, C, O, Z, s, u, hs, hx, ⟨ss', gs, hr⟩, hu => by
      have hstep := symStep_sound P i ss V A C O Z s hs
      simp only [runL] at hu
      obtain ⟨s1, e1, e2⟩ := Option.bind_eq_some_iff.mp hu
      simp only [symRun] at hr
      cases h1 : symStep i ss with
      | ok ss1 g1 =>
          rw [h1] at hstep
          simp only [h1] at hr
          cases h2 : symRun is ss1 with
          | ok ss2 g2 =>
              have hH1 := (hstep.1 s1 e1).2.1
              have ih := leakL_sound P is ss1 V A C O Z s1 u hH1
                (fun y hy => hx y (by simp [hy])) ⟨_, _, h2⟩ e2
              simp only [leakL, symLeak, h1, e1, List.map_append, ih,
                instrLeakF_holds hs i (hx i (by simp))]
          | fail => simp [h2] at hr
          | unk => simp [h2] at hr
      | fail => simp [h1] at hr
      | unk => simp [h1] at hr

/-! ## 3. Traced runs through a stretch and a step -/

section Run

variable {fn : String} {B : List LinstrRM}

/-- A halting traced run from the start of a stretch `xs` of non-terminators of the body
    runs `xs`, emitting `leakL`, and then the rest. -/
theorem fuel_runLLeak :
    ∀ (xs rest : List LinstrRM) (s t : LstateMF) (fuel : Nat) (ℓ : List CTLeak),
      s.prog.lfn = fn → B.drop s.prog.base.reg.lpc = xs ++ rest →
      (∀ x ∈ xs, isTermR x.1 = false) →
      lsemFuelMemFLeak (singletonProgM fn B) fuel s = some (t, ℓ) →
      ∃ u f ℓ₂, fuel = xs.length + f ∧ runL (singletonProgM fn B) xs s = some u ∧
        lsemFuelMemFLeak (singletonProgM fn B) f u = some (t, ℓ₂) ∧
        ℓ = leakL (singletonProgM fn B) xs s ++ ℓ₂
  | [], _, s, t, fuel, ℓ, _, _, _, h => ⟨s, fuel, ℓ, by simp, rfl, h, by simp [leakL]⟩
  | x :: xs, rest, s, t, fuel, ℓ, hfn, hB, hx, h => by
      have hget : B[s.prog.base.reg.lpc]? = some x := by
        rw [← List.head?_drop, hB]; rfl
      have hfetch : findInstrMem (singletonProgM fn B) s.prog = some x := by
        rw [findInstrMem_single hfn, hget]
      cases fuel with
      | zero => simp [lsemFuelMemFLeak, hfetch] at h
      | succ f =>
          cases he : evalInstrPMemF (singletonProgM fn B) x s with
          | none => simp [lsemFuelMemFLeak, hfetch, he] at h
          | some s1 =>
              rw [lsemFuelMemFLeak_step _ f x s s1 hfetch he] at h
              obtain ⟨⟨t1, ℓ1⟩, hr, hre⟩ := Option.map_eq_some_iff.mp h
              simp only [Prod.mk.injEq] at hre
              obtain ⟨rfl, rfl⟩ := hre
              obtain ⟨h1, h2⟩ := step_plain (hx x (by simp)) he
              have hB1 : B.drop s1.prog.base.reg.lpc = xs ++ rest := by
                rw [h2, ← List.drop_drop, hB]; rfl
              obtain ⟨u, f', ℓ₂, hf, hu, hrun, hl⟩ := fuel_runLLeak xs rest s1 t1 f ℓ1
                (h1.trans hfn) hB1 (fun y hy => hx y (by simp [hy])) hr
              refine ⟨u, f', ℓ₂, by simp [hf]; omega, by simp [runL, he, hu], hrun, ?_⟩
              simp [leakL, he, hl]

end Run

/-- One fetched step of a halting traced run. -/
theorem run_invL {P : LprogM} {f : Nat} {s t : LstateMF} {ℓ : List CTLeak} {i : LinstrRM}
    (h : lsemFuelMemFLeak P f s = some (t, ℓ)) (hi : findInstrMem P s.prog = some i) :
    ∃ f1 s1 ℓ1, f = f1 + 1 ∧ evalInstrPMemF P i s = some s1 ∧
      lsemFuelMemFLeak P f1 s1 = some (t, ℓ1) ∧ ℓ = instrLeakF i s ++ ℓ1 := by
  cases f with
  | zero => simp [lsemFuelMemFLeak, hi] at h
  | succ f1 =>
      cases he : evalInstrPMemF P i s with
      | none => simp [lsemFuelMemFLeak, hi, he] at h
      | some s1 =>
          rw [lsemFuelMemFLeak_step _ f1 i s s1 hi he] at h
          obtain ⟨⟨t1, ℓ1⟩, hr, hre⟩ := Option.map_eq_some_iff.mp h
          simp only [Prod.mk.injEq] at hre
          obtain ⟨rfl, rfl⟩ := hre
          exact ⟨f1, s1, ℓ1, rfl, rfl, hr, rfl⟩

theorem haltL {fn : String} {B : List LinstrRM} {w : LstateMF} (hfn : w.prog.lfn = fn)
    (hw : w.prog.base.reg.lpc = B.length) (f : Nat) :
    lsemFuelMemFLeak (singletonProgM fn B) f w = some (w, []) := by
  apply lsemFuelMemFLeak_halt
  rw [findInstrMem_single hfn, hw]
  simp

/-- A jump emits no event. -/
theorem instrLeakF_goto (x : String) (l : LLabel) (tag : MemTag) (s : LstateMF) :
    instrLeakF (.Lgoto (x, l), tag) s = [] := rfl

/-- A conditional emits the branch it takes. -/
theorem instrLeakF_cond (c : LOperand) (l : LLabel) (tag : MemTag) (s : LstateMF) :
    instrLeakF (.Lcond c l, tag) s = [.branch (decC s c)] := by
  unfold instrLeakF decC
  rw [OwnedLprogTV.flagCondCC?_cond]
  cases ccPol c with
  | some pol => rfl
  | none => simp only [Option.map_none, instrLeakB]; rw [← condNZ_reg]

/-! ## 4. The checks -/

/-- The symbolic events of the rewritten block are those of the source block, over registers
    and flags live at the block, unless the block ends in `Lret` or the source block always
    fails. -/
def leakOk (L : Nat → List String × Bool) (k : Nat) (T : Term) (B B' : List LinstrRM)
    (b b' : Block) : Bool :=
  match T with
  | .ret => true
  | _ =>
      match symRun (bodyAt B b T) SSt.start with
      | .ok _ _ =>
          symLeak (bodyAt B' b' T) SSt.start == symLeak (bodyAt B b T) SSt.start &&
            (symLeak (bodyAt B b T) SSt.start).all fun e => okIn (L k) e.vars e.readsF
      | _ => true

/-- `leakOk` at every block pair of the two graphs. -/
def leakCheckWith (L : Nat → List String × Bool) (B B' : List LinstrRM) : Bool :=
  match cfgOf (B.map Prod.fst), cfgOf (B'.map Prod.fst) with
  | some G, some G' =>
      (List.range G.blocks.size).all fun k =>
        leakOk L k (G.blk k).term B B' (G.blk k) (G'.blk k)
  | _, _ => false

/-- **The checker on traced runs**: `ownedCheckMC` and `leakCheckWith` at the live sets
    `ownedCheckM` computes. -/
def ownedCheckML (outs : List String) (B B' : List LinstrRM) : Bool :=
  match cfgOf (B.map Prod.fst), cfgOf (B'.map Prod.fst) with
  | some G, some G' =>
      let R := runsOf B B' G G'
      let L := liveIter outs B G R (4 * G.blocks.size + 64)
        (Array.replicate G.blocks.size ([], false))
      ownedCheckWithR outs (fun k => L.getD k ([], false)) B B' G G' R
        && oblCheckWith (fun k => L.getD k ([], false)) B B'
        && leakCheckWith (fun k => L.getD k ([], false)) B B'
  | _, _ => false

/-- `ownedCheckML` accepts only pairs `ownedCheckMC` accepts. -/
theorem ownedCheckMC_of_ownedCheckML {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckML outs B B' = true) : ownedCheckMC outs B B' = true := by
  unfold ownedCheckML at h
  unfold ownedCheckMC
  cases hG : cfgOf (B.map Prod.fst) with
  | none => simp [hG] at h
  | some G =>
      cases hG' : cfgOf (B'.map Prod.fst) with
      | none => simp [hG, hG'] at h
      | some G' =>
          rw [hG, hG'] at h
          simp only [Bool.and_eq_true] at h ⊢
          exact h.1

theorem ownedCheckML_with {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckML outs B B' = true) :
    ∃ L, ownedCheckWith outs L B B' = true ∧ leakCheckWith L B B' = true := by
  unfold ownedCheckML at h
  cases hG : cfgOf (B.map Prod.fst) with
  | none => simp [hG] at h
  | some G =>
      cases hG' : cfgOf (B'.map Prod.fst) with
      | none => simp [hG, hG'] at h
      | some G' =>
          rw [hG, hG'] at h
          simp only [Bool.and_eq_true] at h
          exact ⟨_, ownedCheckWithR_spec hG hG' h.1.1, h.2⟩

theorem leakOk_spec {L : Nat → List String × Bool} {k : Nat} {T : Term} {B B' : List LinstrRM}
    {b b' : Block} (h : leakOk L k T B B' b b' = true) (hT : T ≠ .ret) {ss : SSt}
    {gs : List SG} (hs : symRun (bodyAt B b T) SSt.start = .ok ss gs) :
    symLeak (bodyAt B' b' T) SSt.start = symLeak (bodyAt B b T) SSt.start ∧
      ∀ e ∈ symLeak (bodyAt B b T) SSt.start,
        (∀ v ∈ e.vars, v ∈ (L k).1) ∧ (e.readsF = true → (L k).2 = true) := by
  have h2 : (match symRun (bodyAt B b T) SSt.start with
      | .ok _ _ =>
          symLeak (bodyAt B' b' T) SSt.start == symLeak (bodyAt B b T) SSt.start &&
            (symLeak (bodyAt B b T) SSt.start).all fun e => okIn (L k) e.vars e.readsF
      | _ => true) = true := by
    cases T with
    | ret => exact absurd rfl hT
    | _ => exact h
  rw [hs] at h2
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h2
  exact ⟨h2.1, fun e he => okIn_spec (h2.2 e he)⟩

/-! ## 5. One trace -/

/-- The trace agreement up to the measure `N`: a halting traced source run and a halting
    traced run of the rewritten body from related states at a block entry have one
    trace. -/
def SimAtL (L : Nat → List String × Bool) (B B' : List LinstrRM) (G G' : CFG) (fn : String)
    (N : Nat) : Prop :=
  ∀ (fuel k : Nat) (s s' t t' : LstateMF) (f' : Nat) (ℓ ℓ' : List CTLeak),
    fuel * (G.blocks.size + 1) + (G.blocks.size - k) < N → k < G.blocks.size →
    Pair B B' (G.blk k) (G'.blk k) s.prog.base.reg.lpc s'.prog.base.reg.lpc →
    Rel (L k) s s' → s.prog.lfn = fn →
    lsemFuelMemFLeak (singletonProgM fn B) fuel s = some (t, ℓ) →
    lsemFuelMemFLeak (singletonProgM fn B') f' s' = some (t', ℓ') → ℓ' = ℓ

theorem fall_contL {outs : List String} {L : Nat → List String × Bool} {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : Checked outs L B B' G G') {N k : Nat}
    (ih : SimAtL L B B' G G' fn N) (hk : k < G.blocks.size) {nx : Option Nat}
    (hn : G.next k = nx) (hn' : G'.next k = nx) {w w' t t' : LstateMF} {f0 f1 : Nat}
    {ℓ ℓ' : List CTLeak}
    (hw : w.prog.base.reg.lpc = (G.blk k).stop) (hw' : w'.prog.base.reg.lpc = (G'.blk k).stop)
    (hfn : w.prog.lfn = fn) (hfn' : w'.prog.lfn = fn)
    (hrun : lsemFuelMemFLeak (singletonProgM fn B) f0 w = some (t, ℓ))
    (hrun' : lsemFuelMemFLeak (singletonProgM fn B') f1 w' = some (t', ℓ'))
    (hmeas : f0 * (G.blocks.size + 1) + (G.blocks.size - (k + 1)) < N)
    (hrel : ∀ j, nx = some j → Rel (L j) w w') : ℓ' = ℓ := by
  have hk' : k < G'.blocks.size := hc.size ▸ hk
  cases nx with
  | none =>
      have e1 := (stop_next hc.hG hk).1 hn
      have e2 := (stop_next hc.hG' hk').1 hn'
      rw [haltL hfn (hw.trans e1)] at hrun
      rw [haltL hfn' (hw'.trans e2)] at hrun'
      simp only [Option.some.injEq, Prod.mk.injEq] at hrun hrun'
      rw [← hrun.2, ← hrun'.2]
  | some j =>
      obtain ⟨hj, hjlt, e1⟩ := (stop_next hc.hG hk).2 j hn
      obtain ⟨-, -, e2⟩ := (stop_next hc.hG' hk').2 j hn'
      subst hj
      exact ih f0 (k + 1) w w' t t' f1 ℓ ℓ' hmeas hjlt (Or.inl ⟨hw.trans e1, hw'.trans e2⟩)
        (hrel _ rfl) hfn hrun hrun'

theorem sim_stepL {outs : List String} {L : Nat → List String × Bool} {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : Checked outs L B B' G G')
    (hlk : ∀ k < G.blocks.size, leakOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) = true)
    {N : Nat} (ih : SimAtL L B B' G G' fn N) : SimAtL L B B' G G' fn (N + 1) := by
  intro fuel k s s' t t' f' ℓ ℓ' hN hk hpair hrel hfn hrun hrun'
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
  obtain ⟨u, f, ℓ₂, hf, hu, hru, hℓ⟩ :=
    fuel_runLLeak _ _ s t fuel ℓ hfn (drop_split B hle) hplain hrun
  obtain ⟨hul, hup⟩ := runL_frame _ s u hplain hu
  simp only [List.length_take, List.length_drop] at hup hf
  have hupc : u.prog.base.reg.lpc = bstopOf (G.blk k).term (G.blk k) := by
    have hbstop : bstopOf (G.blk k).term (G.blk k) ≤ B.length := by
      unfold bstopOf; split <;> have := F.le <;> simp at this <;> omega
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
    obtain ⟨_, _, _, _, he, _⟩ :=
      run_invL hru (by rw [findInstrMem_single hul', hupc2, hz])
    obtain ⟨zi, zt⟩ := z
    simp only at hzr
    subst hzr
    rw [evalInstrPMemF_ret] at he
    cases he
  -- the symbolic runs of the two block bodies
  have hD := symRun_sound (singletonProgM fn B) ((B.drop s.prog.base.reg.lpc).take
    (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)) SSt.start _ _ _ _ _ s
    (holds_start s)
  rw [symRun_entry hE hle] at hD
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
  have hD' := symRun_sound (singletonProgM fn B') ((B'.drop s'.prog.base.reg.lpc).take
    (bstopOf (G.blk k).term (G'.blk k) - s'.prog.base.reg.lpc)) SSt.start _ _ _ _ _ s' hH0'
  rw [symRun_entry hE' hle', hS'] at hD'
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
  rw [hTk] at hplain'
  -- the rewritten body runs its block body
  obtain ⟨u'', f'', ℓ₂', hf', hu'', hru', hℓ'⟩ :=
    fuel_runLLeak _ _ s' t' f' ℓ' hfn' (drop_split B' hle') hplain' hrun'
  rw [hu'] at hu''
  cases hu''
  -- the events of the two block bodies
  have hLS := leakL_sound (singletonProgM fn B) _ SSt.start _ _ _ _ _ s u (holds_start s)
    hplain ⟨ss, gs, by rw [symRun_entry hE hle]; exact hS⟩ hu
  rw [symLeak_entry hE hle] at hLS
  have hLI := leakL_sound (singletonProgM fn B') _ SSt.start _ _ _ _ _ s' u' hH0'
    hplain' ⟨ss', gs', by rw [symRun_entry hE' hle']; exact hS'⟩ hu'
  rw [symLeak_entry hE' hle'] at hLI
  obtain ⟨hleq, hlv⟩ := leakOk_spec (hlk k hk) hret hS
  have hstretch : leakL (singletonProgM fn B') ((B'.drop s'.prog.base.reg.lpc).take
      (bstopOf (G.blk k).term (G'.blk k) - s'.prog.base.reg.lpc)) s' =
      leakL (singletonProgM fn B) ((B.drop s.prog.base.reg.lpc).take
        (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)) s := by
    rw [hLI, hLS, hleq]
    refine List.map_congr_left fun e he => ?_
    obtain ⟨hvars, hfl⟩ := hlv e he
    exact SEv.ev_congr _ e (fun r hr => hV r (hvars r hr)) (fun h => by
      obtain ⟨-, hc, ho⟩ := hrel.2.2.2.2 (hfl h)
      exact ⟨hc, ho⟩)
  rw [hℓ, hℓ', hstretch]
  congr 1
  have hupc' : u'.prog.base.reg.lpc = bstopOf (G.blk k).term (G'.blk k) := by
    have hbstop' : bstopOf (G.blk k).term (G'.blk k) ≤ B'.length := by
      rw [← hTk]; unfold bstopOf; split <;> have := F'.le <;> simp at this <;> omega
    rw [hFr'.2.1]; simp only [List.length_take, List.length_drop]; omega
  have hul'' : u'.prog.lfn = fn := hFr'.1.trans hfn'
  obtain ⟨hsucc, -⟩ := exit_rel hH hH' hV (fun hz => hrel.2.2.2.2 hz)
    (symRun_good _ SSt.good_start hS) (symRun_good _ SSt.good_start hS')
    (by rw [hul'', hul']) (by rw [hFr'.2.2, hrel.2.2.1, hFr.2.2]) hex
  have hfle : f ≤ fuel := by omega
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
    exact fall_contL hc ih hk hnx.symm hnx'.symm hw hw' hul' hul'' hru hru'
      (measure_le hN hfle hk) (fun j hj => hsucc j (by simp [hT, Term.succs, hj]))
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
    have hfetch' : findInstrMem (singletonProgM fn B') u'.prog =
        some (.Lgoto (x, l'), zt') := by
      rw [findInstrMem_single hul'', hw', hz']
    obtain ⟨f1, u1, ℓ1, hf1, he, hr1, hℓ1⟩ := run_invL hru hfetch
    obtain ⟨f1', u1', ℓ1', -, he', hr1', hℓ1'⟩ := run_invL hru' hfetch'
    rw [hℓ1, hℓ1', instrLeakF_goto, instrLeakF_goto]
    rw [evalInstrPMemF_goto] at he he'
    by_cases hx : x = (singletonProgM fn B).lfn
    · rw [if_pos hx, evalJumpMem_single hl] at he
      rw [if_pos (by simpa [singletonProgM, hul'', hul'] using hx),
        evalJumpMem_single hl'] at he'
      simp only [Option.map_some, Option.some.injEq] at he he'
      subst he he'
      exact ih f1 tg
        { prog := { base := u.prog.base.setLpc ((G.blk tg).start + 1), lfn := u.prog.lfn },
          zf := u.zf }
        { prog := { base := u'.prog.base.setLpc ((G'.blk tg).start + 1), lfn := u'.prog.lfn },
          zf := u'.zf } t t' f1' ℓ1 ℓ1' (measure_lt hN (show f1 + 1 ≤ fuel by omega)) htg
        (Or.inr ⟨rfl, label_at hl, rfl, label_at hl'⟩) (hsucc tg (by simp [hT, Term.succs]))
        hul' hr1 hr1'
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
    have hdec : decC u' c' = decC u c := by
      rw [decC_eq hH' c', decC_eq hH c, ← hdeq]
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
    obtain ⟨f1, u1, ℓ1, hf1, he, hr1, hℓ1⟩ := run_invL hru hfetch
    obtain ⟨f1', u1', ℓ1', -, he', hr1', hℓ1'⟩ := run_invL hru' hfetch'
    rw [hℓ1, hℓ1', instrLeakF_cond, instrLeakF_cond, hdec]
    congr 1
    rw [evalInstrPMemF_cond] at he he'
    have hstop : 0 < (G.blk k).stop := by have := F.lt; omega
    have hstop' : 0 < (G'.blk k).stop := by have := F'.lt; omega
    by_cases hd : decC u c = true
    · rw [if_pos hd, evalJumpMem_single hl] at he
      rw [if_pos (hdec.trans hd), evalJumpMem_single hl'] at he'
      simp only [Option.map_some, Option.some.injEq] at he he'
      subst he he'
      exact ih f1 tg
        { prog := { base := u.prog.base.setLpc ((G.blk tg).start + 1), lfn := u.prog.lfn },
          zf := u.zf }
        { prog := { base := u'.prog.base.setLpc ((G'.blk tg).start + 1), lfn := u'.prog.lfn },
          zf := u'.zf } t t' f1' ℓ1 ℓ1' (measure_lt hN (show f1 + 1 ≤ fuel by omega)) htg
        (Or.inr ⟨rfl, label_at hl, rfl, label_at hl'⟩) (hsucc tg (by simp [hT, Term.succs]))
        hul' hr1 hr1'
    · rw [if_neg hd] at he
      rw [if_neg (by rw [hdec]; exact hd)] at he'
      simp only [Option.some.injEq] at he he'
      subst he he'
      refine fall_contL (w := { u with prog := { u.prog with base := u.prog.base.nextPc } })
        (w' := { u' with prog := { u'.prog with base := u'.prog.base.nextPc } })
        hc ih hk hnx.symm hnx'.symm ?_ ?_ hul' hul'' hr1 hr1'
        (measure_le hN (show f1 ≤ fuel by omega) hk)
        (fun j hj => hsucc j (by simp [hT, Term.succs, hj]))
      · show u.prog.base.reg.lpc + 1 = _; omega
      · show u'.prog.base.reg.lpc + 1 = _; omega
  · exact absurd hT hret

theorem simAtL_all {outs : List String} {L : Nat → List String × Bool} {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : Checked outs L B B' G G')
    (hlk : ∀ k < G.blocks.size, leakOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) = true) :
    ∀ N, SimAtL L B B' G G' fn N
  | 0 => fun _ _ _ _ _ _ _ _ _ hN => absurd hN (Nat.not_lt_zero _)
  | N + 1 => sim_stepL hc hlk (simAtL_all hc hlk N)

/-! ## 6. Soundness on traced runs -/

/-- **One trace for given live sets.** If `ownedCheckWith outs L B B'` and
    `leakCheckWith L B B'` accept, a halting traced run of `B` and a halting traced run of
    `B'`, both from one state at pc `0`, have one trace. -/
theorem ownedCheckWithL_trace {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM} (h : ownedCheckWith outs L B B' = true)
    (hlk : leakCheckWith L B B' = true) (fn : String) (s : LstateMF) (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.reg.lpc = 0) {fuel f' : Nat} {t t' : LstateMF} {ℓ ℓ' : List CTLeak}
    (hrun : lsemFuelMemFLeak (singletonProgM fn B) fuel s = some (t, ℓ))
    (hrun' : lsemFuelMemFLeak (singletonProgM fn B') f' s = some (t', ℓ')) : ℓ' = ℓ := by
  unfold ownedCheckWith at h
  unfold leakCheckWith at hlk
  split at h
  · rename_i G G' hG hG'
    rw [hG, hG'] at hlk
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, beq_iff_eq,
      List.all_eq_true, List.mem_range] at h hlk
    obtain ⟨⟨⟨hne, hne'⟩, hsz⟩, hblk⟩ := h
    have hc : Checked outs L B B' G G' :=
      ⟨hG, hG', hsz.symm, fun k hk => ⟨(hblk k hk).1.symm, (hblk k hk).2⟩⟩
    have hwl : B.map Prod.fst ≠ [] := by simpa using hne
    have hwl' : B'.map Prod.fst ≠ [] := by simpa using hne'
    obtain ⟨h0, hs0⟩ := cfgOf_start_zero hG hwl
    obtain ⟨-, hs0'⟩ := cfgOf_start_zero hG' hwl'
    exact simAtL_all hc hlk _ fuel 0 s s t t' f' ℓ ℓ' (Nat.lt_succ_self _) h0
      (Or.inl ⟨hpc.trans hs0.symm, hpc.trans hs0'.symm⟩)
      ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩ hfn hrun hrun'
  · cases h

/-- **One trace under `ownedCheckML`.** If `ownedCheckML outs B B'` accepts, a halting traced
    run of `B` and a halting traced run of `B'`, both from one state at pc `0` of that
    function, have one trace. -/
theorem ownedCheckML_trace {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckML outs B B' = true) (fn : String) (s : LstateMF) (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.reg.lpc = 0) {fuel f' : Nat} {t t' : LstateMF} {ℓ ℓ' : List CTLeak}
    (hrun : lsemFuelMemFLeak (singletonProgM fn B) fuel s = some (t, ℓ))
    (hrun' : lsemFuelMemFLeak (singletonProgM fn B') f' s = some (t', ℓ')) : ℓ' = ℓ := by
  obtain ⟨L, hL, hlk⟩ := ownedCheckML_with h
  exact ownedCheckWithL_trace hL hlk fn s hfn hpc hrun hrun'

/-- **Soundness of the checker on traced runs.** If `ownedCheckML outs B B'` accepts, a
    halting checked run of `B` from a state at pc `0` of that function, with trace `ℓ` on the
    traced flag machine, is matched by a halting checked run of `B'` from the same state, the
    end states agreeing on `outs`, on the arrays and on the word memory, whose traced run has
    the trace `ℓ`. -/
theorem ownedCheckML_sound_leak {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckML outs B B' = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : lsemFuelMemFk true (singletonProgM fn B) fuel s = some t) {ℓ : List CTLeak}
    (hl : FRun (singletonProgM fn B) s ℓ) :
    ∃ fuel' t', lsemFuelMemFk true (singletonProgM fn B') fuel' s = some t' ∧
      Obs outs t t' ∧ FRun (singletonProgM fn B') s ℓ := by
  obtain ⟨f', t', hr', hobs⟩ :=
    ownedCheckMC_sound (ownedCheckMC_of_ownedCheckML h) fn s t hfn hpc fuel hrun
  refine ⟨f', t', hr', hobs, ?_⟩
  have hu := lsemFuelMemF_of_checked _ f' s t' hr'
  rw [← lsemFuelMemFLeak_fst] at hu
  obtain ⟨⟨t2, ℓ'⟩, h2, -⟩ := Option.map_eq_some_iff.mp hu
  obtain ⟨g, t1, h1⟩ := hl
  rw [← ownedCheckML_trace h fn s hfn hpc h1 h2]
  exact ⟨f', t2, h2⟩

/-! ## 7. Constant time -/

/-- Public-equal entry states of `B` at pc `0` of `fn` with halting checked runs of `B`. -/
def TVPub (fn : String) (B : List LinstrRM) (pubEq : LstateMF → LstateMF → Prop)
    (s₁ s₂ : LstateMF) : Prop :=
  pubEq s₁ s₂ ∧ s₁.prog.lfn = fn ∧ s₂.prog.lfn = fn ∧ s₁.prog.base.reg.lpc = 0
    ∧ s₂.prog.base.reg.lpc = 0
    ∧ (∃ f t, lsemFuelMemFk true (singletonProgM fn B) f s₁ = some t)
    ∧ (∃ f t, lsemFuelMemFk true (singletonProgM fn B) f s₂ = some t)

/-- **Constant time through the checker.** If `ownedCheckML outs B B'` accepts and `B` is
    constant time on the flag machine for `pubEq`, then `B'` is constant time on the flag
    machine between public-equal entry states of `B` at pc `0` from which `B` has halting
    checked runs (`TVPub`). -/
theorem memFCT_of_ownedCheckML {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckML outs B B' = true) (fn : String) {pubEq : LstateMF → LstateMF → Prop}
    (hct : MemFCT (singletonProgM fn B) pubEq) :
    MemFCT (singletonProgM fn B') (TVPub fn B pubEq) := by
  rintro s₁ s₂ ℓ₁ ℓ₂ ⟨hp, hfn₁, hfn₂, hpc₁, hpc₂, ⟨f₁, t₁, hk₁⟩, ⟨f₂, t₂, hk₂⟩⟩
    ⟨g₁, r₁, hr₁⟩ ⟨g₂, r₂, hr₂⟩
  have hsrc : ∀ (s : LstateMF) (f : Nat) (t : LstateMF),
      lsemFuelMemFk true (singletonProgM fn B) f s = some t →
      ∃ ℓ, FRun (singletonProgM fn B) s ℓ := by
    intro s f t hk
    have hu := lsemFuelMemF_of_checked _ f s t hk
    rw [← lsemFuelMemFLeak_fst] at hu
    obtain ⟨⟨t', ℓ⟩, h', -⟩ := Option.map_eq_some_iff.mp hu
    exact ⟨ℓ, f, t', h'⟩
  obtain ⟨v₁, hv₁⟩ := hsrc s₁ f₁ t₁ hk₁
  obtain ⟨v₂, hv₂⟩ := hsrc s₂ f₂ t₂ hk₂
  obtain ⟨g₁', t₁', hv₁'⟩ := hv₁
  obtain ⟨g₂', t₂', hv₂'⟩ := hv₂
  rw [ownedCheckML_trace h fn s₁ hfn₁ hpc₁ hv₁' hr₁,
    ownedCheckML_trace h fn s₂ hfn₂ hpc₂ hv₂' hr₂]
  exact hct s₁ s₂ v₁ v₂ hp ⟨g₁', t₁', hv₁'⟩ ⟨g₂', t₂', hv₂'⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedTVLeak
