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
`b[i]` the event of `b` at `i`, and a constant-index store `STOREIMM d, [b, v, #k]` the event
of `b` at `8 * k` (`storeImmSEv`). Register moves, frame-word moves and labels emit nothing.

`leakCheckWith` asks, at every block pair the checker `ownedCheckM` compares, that the
symbolic events of the rewritten block are those of the source block up to the normal form
`SEv.norm` (an event at a register index whose word is an immediate is the event at the
compile-time offset), over registers (and flags) live at the block. Array names are not renamed by the checker (the two runs share
their arrays), and the branch events agree because the checker already compares the
symbolic branch conditions. Under `ownedCheckWith` and `leakCheckWith`, two halting traced
runs of the source and of the rewritten body from one state have one trace. `ownedCheckML`
is `ownedCheckMC` with `leakCheckWith` at its live sets and its must-constant facts: the
events of each block are collected from the symbolic run that starts from the facts of the
block.

The traced run of an instruction set `I : LprogIsa.Isa` is `Isa.lsemFuelMemFLeak`: the
recursion of `lsemFuelMemFLeak` with the step of `I`, a conditional emitting the branch
`I.condEval` decides (`Isa.instrLeakF`). The checks take the symbolic step and the symbolic
branch condition as trailing arguments that default to the x86 ones. The theorems with the
suffix `_at` are stated for an instruction set whose step the symbolic step describes
(`OwnedLprogTV.SymLaws`); the theorems about `lsemFuelMemFLeak` are their instances at
`X86Isa.x86Isa`, at which the generic traced run is `lsemFuelMemFLeak`
(`x86Isa_lsemFuelMemFLeak`).

## Main definitions

* `Isa.instrLeakF`, `Isa.lsemFuelMemFLeak`, `Isa.FRun`, `Isa.MemFCT`: the events, the traced
  run and constant time of an instruction set.
* `SEv`, `opSLeak`, `storeImmSEv`, `instrSLeak`, `symLeak`: symbolic events and their
  collection; `SEv.norm`, their normal form.
* `leakL`: the events of a straight-line stretch.
* `leakOk`, `leakCheckWith`, `ownedCheckML`: the checks.
* `TVPubAt`, `TVPub`: public-equal entry states of the source that have halting checked
  runs.

## Main results

* `x86Isa_instrLeakF`, `x86Isa_lsemFuelMemFLeak`, `x86Isa_FRun`: the generic traced run at
  `x86Isa` is the traced flag machine.
* `instrLeakF_holds_at`, `leakL_sound_at`: the events of a stretch from its symbolic run.
* `fuel_runLLeak_at`, `run_invL_at`: traced runs through a stretch and through one step.
* `ownedCheckML_checked_at`: the checker on traced runs gives `CheckedC` and the event check.
* `checkedC_trace_at`, `ownedCheckWithL_trace_at`, `ownedCheckML_trace_at`,
  `ownedCheckML_sound_leak_at`, `memFCT_of_ownedCheckML_at`: one trace, soundness on traced
  runs and constant time over an instruction set.
* `ownedCheckWithL_trace`, `ownedCheckML_trace`: one trace for the source and the rewritten
  body.
* `ownedCheckML_sound_leak`: a halting checked traced run of the source is matched by a
  halting checked run of the rewritten body with the same trace.
* `memFCT_of_ownedCheckML`: constant time of the source gives constant time of the
  rewritten body.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.Isa

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTimeRel)

/-- The events of an instruction on the instruction set `I`: the branch event of the
    decision `I.condEval` takes at a conditional, otherwise the address events
    `instrLeakB` of the operands. -/
def instrLeakF (I : Isa) (i : LinstrRM) (s : LstateMF) : List CTLeak :=
  match i.fst with
  | .Lcond c _ => [.branch (I.condEval s c)]
  | _ => instrLeakB s.prog.base.reg i

/-- **The run of an instruction set with its leakage trace**: the recursion of
    `Isa.lsemFuelMemF`, each step prepending the events `Isa.instrLeakF` of the fetched
    instruction at the state it runs from. -/
def lsemFuelMemFLeak (I : Isa) (P : LprogM) : Nat → LstateMF → Option (LstateMF × List CTLeak)
  | 0, s => match findInstrMem P s.prog with
            | none => some (s, [])
            | some _ => none
  | fuel + 1, s =>
      match findInstrMem P s.prog with
      | none => some (s, [])
      | some i =>
          match I.step P i s with
          | some s' =>
              (lsemFuelMemFLeak I P fuel s').map fun r => (r.1, I.instrLeakF i s ++ r.2)
          | none => none

/-- The state component of the traced run is `Isa.lsemFuelMemF`. -/
theorem lsemFuelMemFLeak_fst (I : Isa) (P : LprogM) :
    ∀ (fuel : Nat) (s : LstateMF),
      (I.lsemFuelMemFLeak P fuel s).map Prod.fst = I.lsemFuelMemF P fuel s := by
  intro fuel
  induction fuel with
  | zero =>
      intro s
      simp only [lsemFuelMemFLeak, lsemFuelMemF]
      cases findInstrMem P s.prog <;> rfl
  | succ n ih =>
      intro s
      simp only [lsemFuelMemFLeak, lsemFuelMemF]
      cases findInstrMem P s.prog with
      | none => rfl
      | some i =>
          simp only []
          cases I.step P i s with
          | none => rfl
          | some s' =>
              simp only []
              rw [← ih s', Option.map_map]
              rfl

/-- A halted state emits nothing. -/
theorem lsemFuelMemFLeak_halt (I : Isa) (P : LprogM) (fuel : Nat) (s : LstateMF)
    (h : findInstrMem P s.prog = none) : I.lsemFuelMemFLeak P fuel s = some (s, []) := by
  cases fuel <;> simp [lsemFuelMemFLeak, h]

/-- One fetched-and-evaluated step of the traced run. -/
theorem lsemFuelMemFLeak_step (I : Isa) (P : LprogM) (fuel : Nat) (i : LinstrRM)
    (s s' : LstateMF)
    (hfetch : findInstrMem P s.prog = some i) (heval : I.step P i s = some s') :
    I.lsemFuelMemFLeak P (fuel + 1) s
      = (I.lsemFuelMemFLeak P fuel s').map fun r => (r.1, I.instrLeakF i s ++ r.2) := by
  rw [lsemFuelMemFLeak, hfetch]
  simp only [heval]

/-- A terminating run of `P` on the instruction set `I` from `s` with trace `ℓ`. -/
def FRun (I : Isa) (P : LprogM) (s : LstateMF) (ℓ : List CTLeak) : Prop :=
  ∃ fuel t, I.lsemFuelMemFLeak P fuel s = some (t, ℓ)

/-- **Constant time on an instruction set**: two terminating runs of `P` from states related
    by `pubEq` have equal traces. -/
def MemFCT (I : Isa) (P : LprogM) (pubEq : LstateMF → LstateMF → Prop) : Prop :=
  ConstantTimeRel pubEq (I.FRun P)

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.Isa

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
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa
  (x86Isa x86Isa_lsemFuelMemF x86Isa_runL x86Isa_lsemFuelMemFk)

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

/-- The symbolic event of a constant-index store `STOREIMM d, [b, v, #k]` at the tag
    `.storeImm w n`: the array `b` at the compile-time byte offset `8 * k` (`storeImmEv`). -/
def storeImmSEv (i : LinstrRM) : List SEv :=
  match i.2 with
  | .storeImm _ _ =>
      match storeImmStruct? i.1 with
      | some (_, b, _, k) => [.addrK b (8 * k)]
      | none => []
  | _ => []

/-- The symbolic event of a constant-index store denotes its event. -/
theorem storeImmSEv_ev (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (i : LinstrRM) : (storeImmSEv i).map (SEv.ev V A C O) = storeImmEv i := by
  unfold storeImmSEv storeImmEv
  rcases hi : i.2 <;> simp only [hi] <;> try rfl
  rcases hs : storeImmStruct? i.1 with _ | ⟨_, b, _, k⟩ <;> simp [hs, SEv.ev]

/-- The symbolic events of an instruction from the symbolic state `ss`: those of the
    operands of an `Lopn` other than a load-effective-address `LEA`, which accesses no
    memory, followed by the event `storeImmSEv` of a constant-index store. -/
def instrSLeak (i : LinstrRM) (ss : SSt) : List SEv :=
  match i.1 with
  | .Lopn ds o xs =>
      if stripWidthTag o = "LEA" then [] else (ds ++ xs).flatMap (opSLeak ss) ++ storeImmSEv i
  | _ => []

/-- The normal form of a symbolic event: an address event at a register index whose word is
    the immediate `n` at width `w` is the compile-time address event at offset
    `sc * (n % 2 ^ w)`; every other event is unchanged. -/
def SEv.norm : SEv → SEv
  | .addr b sc (.immW w n) => .addrK b (sc * (n % 2 ^ w))
  | e => e

/-- The normal form denotes the event the symbolic event denotes. -/
theorem SEv.ev_norm (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
    (e : SEv) : e.norm.ev V A C O = e.ev V A C O := by
  unfold SEv.norm
  split
  · simp [SEv.ev, STerm.ev, BitVec.toNat_ofNat]
  · rfl

/-- The symbolic events of a list of instructions, collected along its symbolic run under
    the symbolic step `sym`. -/
def symLeak : List LinstrRM → SSt → optParam (LinstrRM → SSt → SOut) symStep → List SEv
  | [], _, _ => []
  | i :: is, ss, sym =>
      instrSLeak i ss ++
        match sym i ss with
        | .ok ss1 _ => symLeak is ss1 sym
        | _ => []

theorem symLeak_label_at {sym : LinstrRM → SSt → SOut}
    (hlab : ∀ {i : LinstrRM}, isLbl i = true → ∀ ss : SSt, sym i ss = .ok ss [])
    {i : LinstrRM} (h : isLbl i = true) (is : List LinstrRM) (ss : SSt) :
    symLeak (i :: is) ss sym = symLeak is ss sym := by
  obtain ⟨x, tag⟩ := i
  have hx : instrSLeak (x, tag) ss = [] := by
    cases x <;> simp_all [isLbl, instrSLeak]
  simp only [symLeak, hx, hlab h, List.nil_append]

theorem symLeak_label {i : LinstrRM} (h : isLbl i = true) (is : List LinstrRM) (ss : SSt) :
    symLeak (i :: is) ss = symLeak is ss :=
  symLeak_label_at (fun h ss => symStep_label h ss) h is ss

theorem symLeak_entry_at {sym : LinstrRM → SSt → SOut}
    (hlab : ∀ {i : LinstrRM}, isLbl i = true → ∀ ss : SSt, sym i ss = .ok ss [])
    {B : List LinstrRM} {b : Block} {T : Term} {p : Nat} {ss : SSt}
    (hp : EntryAt B b p) (hle : p ≤ bstopOf T b) :
    symLeak ((B.drop p).take (bstopOf T b - p)) ss sym = symLeak (bodyAt B b T) ss sym := by
  rcases hp with rfl | ⟨rfl, x, hx, hl⟩
  · rfl
  · unfold bodyAt
    rw [take_cons B (by omega) hx, symLeak_label_at hlab hl]

theorem symLeak_entry {B : List LinstrRM} {b : Block} {T : Term} {p : Nat}
    (hp : EntryAt B b p) (hle : p ≤ bstopOf T b) :
    symLeak ((B.drop p).take (bstopOf T b - p)) SSt.start =
      symLeak (bodyAt B b T) SSt.start :=
  symLeak_entry_at (fun h ss => symStep_label h ss) hp hle

/-! ## 2. The traced run at x86, and the events of a stretch -/

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

/-- The events of an instruction at `x86Isa` are those of the flag machine. -/
theorem x86Isa_instrLeakF (i : LinstrRM) (s : LstateMF) :
    x86Isa.instrLeakF i s = instrLeakF i s := by
  obtain ⟨x, tag⟩ := i
  cases x with
  | Lcond c l => rw [instrLeakF_cond]; rfl
  | _ => rfl

/-- The generic traced run at `x86Isa` is `lsemFuelMemFLeak`. -/
theorem x86Isa_lsemFuelMemFLeak (P : LprogM) :
    ∀ (fuel : Nat) (s : LstateMF),
      x86Isa.lsemFuelMemFLeak P fuel s = lsemFuelMemFLeak P fuel s
  | 0, s => by
      cases hf : findInstrMem P s.prog with
      | none => rw [Isa.lsemFuelMemFLeak_halt _ _ _ _ hf, lsemFuelMemFLeak_halt _ _ _ hf]
      | some i => simp only [Isa.lsemFuelMemFLeak, lsemFuelMemFLeak, hf]
  | fuel + 1, s => by
      cases hf : findInstrMem P s.prog with
      | none => rw [Isa.lsemFuelMemFLeak_halt _ _ _ _ hf, lsemFuelMemFLeak_halt _ _ _ hf]
      | some i =>
          cases he : evalInstrPMemF P i s with
          | none =>
              have he' : x86Isa.step P i s = none := he
              simp only [Isa.lsemFuelMemFLeak, lsemFuelMemFLeak, hf, he, he']
          | some s' =>
              rw [Isa.lsemFuelMemFLeak_step x86Isa P fuel i s s' hf he,
                lsemFuelMemFLeak_step P fuel i s s' hf he, x86Isa_lsemFuelMemFLeak P fuel s',
                x86Isa_instrLeakF]

/-- The terminating traced runs at `x86Isa` are those of the flag machine. -/
theorem x86Isa_FRun (P : LprogM) (s : LstateMF) (ℓ : List CTLeak) :
    x86Isa.FRun P s ℓ ↔ FRun P s ℓ := by
  simp only [Isa.FRun, FRun, x86Isa_lsemFuelMemFLeak]

/-- The events of the steps of a list of instructions on the instruction set `I`, in
    order. -/
def leakL (I : Isa) (P : LprogM) : List LinstrRM → LstateMF → List CTLeak
  | [], _ => []
  | i :: is, s =>
      I.instrLeakF i s ++
        match I.step P i s with
        | some s1 => leakL I P is s1
        | none => []

/-- **The events of a non-terminator from its symbolic description.** -/
theorem instrLeakF_holds_at (I : Isa) {V : String → Σ w, BitVec w} {A : String → ArrCell}
    {C O Z : Bool}
    {ss : SSt} {s : LstateMF} (hs : Holds V A C O Z ss s) (i : LinstrRM)
    (hi : isTermR i.1 = false) :
    I.instrLeakF i s = (instrSLeak i ss).map (SEv.ev V A C O) := by
  obtain ⟨x, tag⟩ := i
  cases x with
  | Lopn ds o xs =>
      simp only [Isa.instrLeakF, instrLeakB, instrSLeak]
      split_ifs
      · rfl
      simp only [List.map_append, List.map_flatMap]
      rw [storeImmSEv_ev]
      congr 1
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
    stretch of non-terminators of the instruction set `I` from a state the start of a
    successful symbolic run describes. -/
theorem leakL_sound_at {I : Isa} {sym : LinstrRM → SSt → SOut}
    (hsym : ∀ (P : LprogM) (i : LinstrRM) (ss : SSt), StepSound (I.step P i) ss (sym i ss))
    (P : LprogM) :
    ∀ (is : List LinstrRM) (ss : SSt) (V : String → Σ w, BitVec w) (A : String → ArrCell)
      (C O Z : Bool) (s u : LstateMF), Holds V A C O Z ss s →
      (∀ x ∈ is, isTermR x.1 = false) →
      (∃ ss' gs, symRun is ss sym = .ok ss' gs) → I.runL P is s = some u →
      leakL I P is s = (symLeak is ss sym).map (SEv.ev V A C O)
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => by simp [leakL, symLeak]
  | i :: is, ss, V, A, C, O, Z, s, u, hs, hx, ⟨ss', gs, hr⟩, hu => by
      have hstep := hsym P i ss V A C O Z s hs
      simp only [Isa.runL] at hu
      obtain ⟨s1, e1, e2⟩ := Option.bind_eq_some_iff.mp hu
      simp only [symRun] at hr
      cases h1 : sym i ss with
      | ok ss1 g1 =>
          rw [h1] at hstep
          simp only [h1] at hr
          cases h2 : symRun is ss1 sym with
          | ok ss2 g2 =>
              have hH1 := (hstep.1 s1 e1).2.1
              have ih := leakL_sound_at hsym P is ss1 V A C O Z s1 u hH1
                (fun y hy => hx y (by simp [hy])) ⟨_, _, h2⟩ e2
              simp only [leakL, symLeak, h1, e1, List.map_append, ih,
                instrLeakF_holds_at I hs i (hx i (by simp))]
          | fail => simp [h2] at hr
          | unk => simp [h2] at hr
      | fail => simp [h1] at hr
      | unk => simp [h1] at hr

/-! ## 3. Traced runs through a stretch and a step -/

section Run

variable {fn : String} {B : List LinstrRM}

/-- A halting traced run of the instruction set `I` from the start of a stretch `xs` of
    non-terminators of the body runs `xs`, emitting `leakL`, and then the rest. -/
theorem fuel_runLLeak_at {I : Isa} (hpl : StepPlain I) :
    ∀ (xs rest : List LinstrRM) (s t : LstateMF) (fuel : Nat) (ℓ : List CTLeak),
      s.prog.lfn = fn → B.drop s.prog.base.reg.lpc = xs ++ rest →
      (∀ x ∈ xs, isTermR x.1 = false) →
      I.lsemFuelMemFLeak (singletonProgM fn B) fuel s = some (t, ℓ) →
      ∃ u f ℓ₂, fuel = xs.length + f ∧ I.runL (singletonProgM fn B) xs s = some u ∧
        I.lsemFuelMemFLeak (singletonProgM fn B) f u = some (t, ℓ₂) ∧
        ℓ = leakL I (singletonProgM fn B) xs s ++ ℓ₂
  | [], _, s, t, fuel, ℓ, _, _, _, h => ⟨s, fuel, ℓ, by simp, rfl, h, by simp [leakL]⟩
  | x :: xs, rest, s, t, fuel, ℓ, hfn, hB, hx, h => by
      have hget : B[s.prog.base.reg.lpc]? = some x := by
        rw [← List.head?_drop, hB]; rfl
      have hfetch : findInstrMem (singletonProgM fn B) s.prog = some x := by
        rw [findInstrMem_single hfn, hget]
      cases fuel with
      | zero => simp [Isa.lsemFuelMemFLeak, hfetch] at h
      | succ f =>
          cases he : I.step (singletonProgM fn B) x s with
          | none => simp [Isa.lsemFuelMemFLeak, hfetch, he] at h
          | some s1 =>
              rw [I.lsemFuelMemFLeak_step _ f x s s1 hfetch he] at h
              obtain ⟨⟨t1, ℓ1⟩, hr, hre⟩ := Option.map_eq_some_iff.mp h
              simp only [Prod.mk.injEq] at hre
              obtain ⟨rfl, rfl⟩ := hre
              obtain ⟨h1, h2⟩ := hpl _ (hx x (by simp)) he
              have hB1 : B.drop s1.prog.base.reg.lpc = xs ++ rest := by
                rw [h2, ← List.drop_drop, hB]; rfl
              obtain ⟨u, f', ℓ₂, hf, hu, hrun, hl⟩ := fuel_runLLeak_at hpl xs rest s1 t1 f ℓ1
                (h1.trans hfn) hB1 (fun y hy => hx y (by simp [hy])) hr
              refine ⟨u, f', ℓ₂, by simp [hf]; omega, by simp [Isa.runL, he, hu], hrun, ?_⟩
              simp [leakL, he, hl]

end Run

/-- One fetched step of a halting traced run of the instruction set `I`. -/
theorem run_invL_at {I : Isa} {P : LprogM} {f : Nat} {s t : LstateMF} {ℓ : List CTLeak}
    {i : LinstrRM}
    (h : I.lsemFuelMemFLeak P f s = some (t, ℓ)) (hi : findInstrMem P s.prog = some i) :
    ∃ f1 s1 ℓ1, f = f1 + 1 ∧ I.step P i s = some s1 ∧
      I.lsemFuelMemFLeak P f1 s1 = some (t, ℓ1) ∧ ℓ = I.instrLeakF i s ++ ℓ1 := by
  cases f with
  | zero => simp [Isa.lsemFuelMemFLeak, hi] at h
  | succ f1 =>
      cases he : I.step P i s with
      | none => simp [Isa.lsemFuelMemFLeak, hi, he] at h
      | some s1 =>
          rw [I.lsemFuelMemFLeak_step _ f1 i s s1 hi he] at h
          obtain ⟨⟨t1, ℓ1⟩, hr, hre⟩ := Option.map_eq_some_iff.mp h
          simp only [Prod.mk.injEq] at hre
          obtain ⟨rfl, rfl⟩ := hre
          exact ⟨f1, s1, ℓ1, rfl, rfl, hr, rfl⟩

/-- A state of the instruction set `I` at the end of the body is halted and emits
    nothing. -/
theorem haltL_at (I : Isa) {fn : String} {B : List LinstrRM} {w : LstateMF}
    (hfn : w.prog.lfn = fn)
    (hw : w.prog.base.reg.lpc = B.length) (f : Nat) :
    I.lsemFuelMemFLeak (singletonProgM fn B) f w = some (w, []) := by
  apply I.lsemFuelMemFLeak_halt
  rw [findInstrMem_single hfn, hw]
  simp

/-! ## 4. The checks -/

/-- The symbolic events of the rewritten block are those of the source block up to the
    normal form `SEv.norm`, over registers and flags live at the block, unless the block ends
    in `Lret` or the source block always fails. The source block runs from its facts `A k`,
    the rewritten block from its facts `A' k`; both default to no fact. -/
def leakOk (L : Nat → List String × Bool) (k : Nat) (T : Term) (B B' : List LinstrRM)
    (b b' : Block) (sym : LinstrRM → SSt → SOut := symStep)
    (A A' : Nat → List CFact := fun _ => []) : Bool :=
  match T with
  | .ret => true
  | _ =>
      match symRun (bodyAt B b T) (startC (A k)) sym with
      | .ok _ _ =>
          (symLeak (bodyAt B' b' T) (startC (A' k)) sym).map SEv.norm ==
              (symLeak (bodyAt B b T) (startC (A k)) sym).map SEv.norm &&
            (symLeak (bodyAt B b T) (startC (A k)) sym).all fun e =>
              okIn (L k) e.vars e.readsF
      | _ => true

/-- `leakOk` at every block pair of the two graphs, with the facts `A` and `A'`. -/
def leakCheckWith (L : Nat → List String × Bool) (B B' : List LinstrRM)
    (sym : LinstrRM → SSt → SOut := symStep) (A A' : Nat → List CFact := fun _ => []) :
    Bool :=
  match cfgOf (B.map Prod.fst), cfgOf (B'.map Prod.fst) with
  | some G, some G' =>
      (List.range G.blocks.size).all fun k =>
        leakOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym A A'
  | _, _ => false

theorem leakCheckWith_spec {L : Nat → List String × Bool} {B B' : List LinstrRM}
    {sym : LinstrRM → SSt → SOut} {A A' : Nat → List CFact} {G G' : CFG}
    (hG : cfgOf (B.map Prod.fst) = some G) (hG' : cfgOf (B'.map Prod.fst) = some G')
    (h : leakCheckWith L B B' sym A A' = true) :
    ∀ k < G.blocks.size,
      leakOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym A A' = true := by
  unfold leakCheckWith at h
  rw [hG, hG'] at h
  simpa only [List.all_eq_true, List.mem_range] using h

/-- **The checker on traced runs**: the comparison of `ownedCheckMC` and `leakCheckWith` at
    its live sets and facts, with every block of `B` run symbolically between its calls
    (`blocksRunCB`), so that the traces of every block are compared. The check compares
    traces, so it needs no observed name: the leak check of the region gate observes none
    (`regionLeakB`). The symbolic step `sym` and the symbolic branch condition `dec` default
    to the x86 ones, `symStep` and `symDec`. -/
def ownedCheckML (outs : List String) (B B' : List LinstrRM)
    (sym : LinstrRM → SSt → SOut := symStep) (dec : SSt → LOperand → SDec := symDec) : Bool :=
  match cfgOf (B.map Prod.fst), cfgOf (B'.map Prod.fst) with
  | some G, some G' =>
      let A := annotAt (constAnnotArr B G sym)
      let A' := annotAt (constAnnotArr B' G' sym)
      let R := runsOfC A A' B B' G G' sym
      let L := liveIter outs B G R (4 * G.blocks.size + 64)
        (Array.replicate G.blocks.size ([], false)) dec
      ownedCheckWithR outs (fun k => L.getD k ([], false)) B B' G G' R dec
        && oblCheckWith (fun k => L.getD k ([], false)) B B' sym A A'
        && factCheck A B G sym && factCheck A' B' G' sym
        && blocksRunCB B sym
        && leakCheckWith (fun k => L.getD k ([], false)) B B' sym A A'
  | _, _ => false

/-- `ownedCheckML` accepts only pairs `ownedCheckMC` accepts, when the check has an output to
    compare. -/
theorem ownedCheckMC_of_ownedCheckML {outs : List String} {B B' : List LinstrRM}
    {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (h : ownedCheckML outs B B' sym dec = true) (ho : hasOutsB outs B = true) :
    ownedCheckMC outs B B' sym dec = true := by
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
          exact ⟨⟨h.1.1, ho⟩, h.1.2⟩

/-- A pair `ownedCheckML` accepts satisfies `CheckedC` and the index obligations for some
    live sets and facts, when `sym` and `dec` commute with substitution. -/
theorem ownedCheckML_checkedObl_at {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hS : SymSubst sym dec) {outs : List String}
    {B B' : List LinstrRM} (h : ownedCheckML outs B B' sym dec = true) :
    ∃ L A A' G G', CheckedC outs L A A' B B' G G' sym dec ∧
      ∀ k < G.blocks.size,
        oblOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym A A' = true := by
  unfold ownedCheckML at h
  cases hG : cfgOf (B.map Prod.fst) with
  | none => simp [hG] at h
  | some G =>
      cases hG' : cfgOf (B'.map Prod.fst) with
      | none => simp [hG, hG'] at h
      | some G' =>
          rw [hG, hG'] at h
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, -⟩ := h
          exact ⟨_, _, _, G, G', checkedC_of_withR hS hG hG' h1 h3 h4,
            oblCheckWith_spec hG hG' h2⟩

/-- A pair `ownedCheckML` accepts under `sym` and `dec` satisfies `CheckedC` and the event
    check for some live sets and facts, when `sym` and `dec` commute with substitution. -/
theorem ownedCheckML_checked_at {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hS : SymSubst sym dec) {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckML outs B B' sym dec = true) :
    ∃ L A A' G G', CheckedC outs L A A' B B' G G' sym dec ∧
      ∀ k < G.blocks.size,
        leakOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym A A' = true := by
  unfold ownedCheckML at h
  cases hG : cfgOf (B.map Prod.fst) with
  | none => simp [hG] at h
  | some G =>
      cases hG' : cfgOf (B'.map Prod.fst) with
      | none => simp [hG, hG'] at h
      | some G' =>
          rw [hG, hG'] at h
          simp only [Bool.and_eq_true] at h
          obtain ⟨⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, -⟩, h5⟩ := h
          exact ⟨_, _, _, G, G', checkedC_of_withR hS hG hG' h1 h3 h4,
            leakCheckWith_spec hG hG' h5⟩

theorem leakOk_spec {L : Nat → List String × Bool} {k : Nat} {T : Term} {B B' : List LinstrRM}
    {b b' : Block} {sym : LinstrRM → SSt → SOut} {A A' : Nat → List CFact}
    (h : leakOk L k T B B' b b' sym A A' = true) (hT : T ≠ .ret) {ss : SSt}
    {gs : List SG} (hs : symRun (bodyAt B b T) (startC (A k)) sym = .ok ss gs) :
    (symLeak (bodyAt B' b' T) (startC (A' k)) sym).map SEv.norm =
        (symLeak (bodyAt B b T) (startC (A k)) sym).map SEv.norm ∧
      ∀ e ∈ symLeak (bodyAt B b T) (startC (A k)) sym,
        (∀ v ∈ e.vars, v ∈ (L k).1) ∧ (e.readsF = true → (L k).2 = true) := by
  have h2 : (match symRun (bodyAt B b T) (startC (A k)) sym with
      | .ok _ _ =>
          (symLeak (bodyAt B' b' T) (startC (A' k)) sym).map SEv.norm ==
              (symLeak (bodyAt B b T) (startC (A k)) sym).map SEv.norm &&
            (symLeak (bodyAt B b T) (startC (A k)) sym).all fun e =>
              okIn (L k) e.vars e.readsF
      | _ => true) = true := by
    cases T with
    | ret => exact absurd rfl hT
    | _ => exact h
  rw [hs] at h2
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h2
  exact ⟨h2.1, fun e he => okIn_spec (h2.2 e he)⟩

/-! ## 5. One trace -/

/-- The trace agreement on the instruction set `I` up to the measure `N`: a halting traced
    source run and a halting traced run of the rewritten body from related states at a block
    entry, the source state satisfying the facts `A` of the block and the rewritten state the
    facts `A'`, have one trace. -/
def SimAtL (I : Isa) (L : Nat → List String × Bool) (A A' : Nat → List CFact)
    (B B' : List LinstrRM) (G G' : CFG) (fn : String) (N : Nat) : Prop :=
  ∀ (fuel k : Nat) (s s' t t' : LstateMF) (f' : Nat) (ℓ ℓ' : List CTLeak),
    fuel * (G.blocks.size + 1) + (G.blocks.size - k) < N → k < G.blocks.size →
    Pair B B' (G.blk k) (G'.blk k) s.prog.base.reg.lpc s'.prog.base.reg.lpc →
    Rel (L k) s s' → FactsAt (A k) s ∧ FactsAt (A' k) s' → s.prog.lfn = fn →
    I.lsemFuelMemFLeak (singletonProgM fn B) fuel s = some (t, ℓ) →
    I.lsemFuelMemFLeak (singletonProgM fn B') f' s' = some (t', ℓ') → ℓ' = ℓ

theorem fall_contL {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    {outs : List String} {L : Nat → List String × Bool} {A A' : Nat → List CFact}
    {B B' : List LinstrRM} {G G' : CFG} {fn : String}
    (hc : CheckedC outs L A A' B B' G G' sym dec) {N k : Nat}
    (ih : SimAtL I L A A' B B' G G' fn N) (hk : k < G.blocks.size) {nx : Option Nat}
    (hn : G.next k = nx) (hn' : G'.next k = nx) {w w' t t' : LstateMF} {f0 f1 : Nat}
    {ℓ ℓ' : List CTLeak}
    (hw : w.prog.base.reg.lpc = (G.blk k).stop) (hw' : w'.prog.base.reg.lpc = (G'.blk k).stop)
    (hfn : w.prog.lfn = fn) (hfn' : w'.prog.lfn = fn)
    (hrun : I.lsemFuelMemFLeak (singletonProgM fn B) f0 w = some (t, ℓ))
    (hrun' : I.lsemFuelMemFLeak (singletonProgM fn B') f1 w' = some (t', ℓ'))
    (hmeas : f0 * (G.blocks.size + 1) + (G.blocks.size - (k + 1)) < N)
    (hrel : ∀ j, nx = some j → Rel (L j) w w')
    (hfa : ∀ j, nx = some j → FactsAt (A j) w ∧ FactsAt (A' j) w') : ℓ' = ℓ := by
  have hk' : k < G'.blocks.size := hc.size ▸ hk
  cases nx with
  | none =>
      have e1 := (stop_next hc.hG hk).1 hn
      have e2 := (stop_next hc.hG' hk').1 hn'
      rw [haltL_at I hfn (hw.trans e1)] at hrun
      rw [haltL_at I hfn' (hw'.trans e2)] at hrun'
      simp only [Option.some.injEq, Prod.mk.injEq] at hrun hrun'
      rw [← hrun.2, ← hrun'.2]
  | some j =>
      obtain ⟨hj, hjlt, e1⟩ := (stop_next hc.hG hk).2 j hn
      obtain ⟨-, -, e2⟩ := (stop_next hc.hG' hk').2 j hn'
      subst hj
      exact ih f0 (k + 1) w w' t t' f1 ℓ ℓ' hmeas hjlt (Or.inl ⟨hw.trans e1, hw'.trans e2⟩)
        (hrel _ rfl) (hfa _ rfl) hfn hrun hrun'

theorem sim_stepL {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hL : SymLaws I sym dec)
    {outs : List String} {L : Nat → List String × Bool} {A A' : Nat → List CFact}
    {B B' : List LinstrRM} {G G' : CFG} {fn : String}
    (hc : CheckedC outs L A A' B B' G G' sym dec)
    (hlk : ∀ k < G.blocks.size,
      leakOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym A A' = true)
    {N : Nat} (ih : SimAtL I L A A' B B' G G' fn N) :
    SimAtL I L A A' B B' G G' fn (N + 1) := by
  intro fuel k s s' t t' f' ℓ ℓ' hN hk hpair hrel ⟨hfa, hfa'⟩ hfn hrun hrun'
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
    fuel_runLLeak_at hL.plain _ _ s t fuel ℓ hfn (drop_split B hle) hplain hrun
  obtain ⟨hul, hup⟩ := runL_frame_at hL.plain _ s u hplain hu
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
      run_invL_at hru (by rw [findInstrMem_single hul', hupc2, hz])
    obtain ⟨zi, zt⟩ := z
    simp only at hzr
    subst hzr
    rw [hL.ret] at he
    cases he
  -- the symbolic runs of the two block bodies
  have hD := symRun_sound_at hL.step_sound (singletonProgM fn B)
    ((B.drop s.prog.base.reg.lpc).take
    (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)) (startC (A k)) _ _ _ _ _ s
    (holds_startC hfa fun _ => rfl)
  rw [symRun_entryS_at hL.label hE hle] at hD
  rcases blockOkS_spec hok hret with hfail | ⟨ss, gs, ss', gs', hS, hS', hgs, hta, hex⟩
  · rw [hfail] at hD
    simp only [SOut.DescN] at hD
    rw [hD] at hu
    cases hu
  rw [hS] at hD
  obtain ⟨hAll, hH, hFr⟩ := hD.1 u hu
  have hV : ∀ r ∈ (L k).1, s'.prog.base.reg.lvm r = s.prog.base.reg.lvm r := hrel.2.2.2.1
  have hH0' : Holds s'.prog.base.reg.lvm s.prog.base.larr s'.prog.base.cf s'.prog.base.of s'.zf
      (startC (A' k)) s' :=
    holds_startC hfa' fun q => by rw [hrel.2.1]
  rw [hTk] at hle'
  have hD' := symRun_sound_at hL.step_sound (singletonProgM fn B')
    ((B'.drop s'.prog.base.reg.lpc).take
    (bstopOf (G.blk k).term (G'.blk k) - s'.prog.base.reg.lpc)) (startC (A' k))
    _ _ _ _ _ s' hH0'
  rw [symRun_entryS_at hL.label hE' hle', hS'] at hD'
  have hAll' : AllG s'.prog.base.reg.lvm s.prog.base.larr s'.prog.base.cf s'.prog.base.of gs' :=
    allG_normG.mp fun g hg =>
      (SG.holds_congr _ g (fun r hr => (hV r ((hgs g hg).2.1 r hr)).symm)
        (fun e => by
          obtain ⟨-, hc, ho⟩ := hrel.2.2.2.2 ((hgs g hg).2.2 e)
          exact ⟨hc.symm, ho.symm⟩)).mp
      ((hgs g hg).1 _ _ _ _ hAll)
  obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp (hD'.2 hAll')
  obtain ⟨-, hH', hFr'⟩ := hD'.1 u' hu'
  have hplain' := body_plain hc.hG' hk' hs1'
  rw [hTk] at hplain'
  -- the rewritten body runs its block body
  obtain ⟨u'', f'', ℓ₂', hf', hu'', hru', hℓ'⟩ :=
    fuel_runLLeak_at hL.plain _ _ s' t' f' ℓ' hfn' (drop_split B' hle') hplain' hrun'
  rw [hu'] at hu''
  cases hu''
  -- the events of the two block bodies
  have hLS := leakL_sound_at hL.step_sound (singletonProgM fn B) _ (startC (A k)) _ _ _ _ _ s u
    (holds_startC hfa fun _ => rfl)
    hplain ⟨ss, gs, by rw [symRun_entryS_at hL.label hE hle]; exact hS⟩ hu
  rw [symLeak_entry_at hL.label hE hle] at hLS
  have hLI := leakL_sound_at hL.step_sound (singletonProgM fn B') _
    (startC (A' k)) _ _ _ _ _ s' u' hH0'
    hplain' ⟨ss', gs', by rw [symRun_entryS_at hL.label hE' hle']; exact hS'⟩ hu'
  rw [symLeak_entry_at hL.label hE' hle'] at hLI
  obtain ⟨hleq, hlv⟩ := leakOk_spec (hlk k hk) hret hS
  have hstretch : leakL I (singletonProgM fn B') ((B'.drop s'.prog.base.reg.lpc).take
      (bstopOf (G.blk k).term (G'.blk k) - s'.prog.base.reg.lpc)) s' =
      leakL I (singletonProgM fn B) ((B.drop s.prog.base.reg.lpc).take
        (bstopOf (G.blk k).term (G.blk k) - s.prog.base.reg.lpc)) s := by
    have hnorm : ∀ (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O : Bool)
        (l : List SEv), l.map (SEv.ev V A C O) = (l.map SEv.norm).map (SEv.ev V A C O) :=
      fun V A C O l => by simp [Function.comp_def, SEv.ev_norm]
    rw [hLI, hLS,
      hnorm _ _ _ _ (symLeak (bodyAt B' (G'.blk k) (G.blk k).term) (startC (A' k)) sym), hleq,
      ← hnorm]
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
    (symRun_good_at hL.good _ (startC_good _) hS) (symRun_good_at hL.good _ (startC_good _) hS')
    (by rw [hul'', hul']) (by rw [hFr'.2.2, hrel.2.2.1, hFr.2.2]) hAll
    (allG_normG.mp fun g hg => (hgs g hg).1 _ _ _ _ hAll) hex
  have hfk' := factCheck_blk hc.facts' hk'
  rw [hTk] at hfk'
  have hfs : ∀ j ∈ (G.blk k).term.succs, FactsAt (A j) u ∧ FactsAt (A' j) u' := fun j hj =>
    ⟨factsAt_of_holds hH (factsOk_spec (factCheck_blk hc.facts hk) hS j hj),
      factsAt_of_holds hH' (factsOk_spec hfk' hS' j hj)⟩
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
      (fun j hj => hfs j (by simp [hT, Term.succs, hj]))
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
    obtain ⟨f1, u1, ℓ1, hf1, he, hr1, hℓ1⟩ := run_invL_at hru hfetch
    obtain ⟨f1', u1', ℓ1', -, he', hr1', hℓ1'⟩ := run_invL_at hru' hfetch'
    rw [hℓ1, hℓ1']
    show ([] : List CTLeak) ++ ℓ1' = [] ++ ℓ1
    rw [I.step_goto] at he he'
    by_cases hx : x = (singletonProgM fn B).lfn
    · rw [ite_eq_left hx, evalJumpMem_single hl] at he
      rw [ite_eq_left (by simpa [singletonProgM, hul'', hul'] using hx),
        evalJumpMem_single hl'] at he'
      simp only [Option.map_some, Option.some.injEq] at he he'
      subst he he'
      exact ih f1 tg
        { prog := { base := u.prog.base.setLpc ((G.blk tg).start + 1), lfn := u.prog.lfn },
          zf := u.zf }
        { prog := { base := u'.prog.base.setLpc ((G'.blk tg).start + 1), lfn := u'.prog.lfn },
          zf := u'.zf } t t' f1' ℓ1 ℓ1' (measure_lt hN (show f1 + 1 ≤ fuel by omega)) htg
        (Or.inr ⟨rfl, label_at hl, rfl, label_at hl'⟩) (hsucc tg (by simp [hT, Term.succs]))
        (hfs tg (by simp [hT, Term.succs])) hul' hr1 hr1'
    · rw [ite_eq_right hx] at he
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
    obtain ⟨f1, u1, ℓ1, hf1, he, hr1, hℓ1⟩ := run_invL_at hru hfetch
    obtain ⟨f1', u1', ℓ1', -, he', hr1', hℓ1'⟩ := run_invL_at hru' hfetch'
    rw [hℓ1, hℓ1']
    show [CTLeak.branch (I.condEval u' c')] ++ ℓ1' = [CTLeak.branch (I.condEval u c)] ++ ℓ1
    rw [hdec]
    congr 1
    rw [I.step_cond] at he he'
    have hstop : 0 < (G.blk k).stop := by have := F.lt; omega
    have hstop' : 0 < (G'.blk k).stop := by have := F'.lt; omega
    by_cases hd : I.condEval u c = true
    · rw [ite_eq_left hd, evalJumpMem_single hl] at he
      rw [ite_eq_left (hdec.trans hd), evalJumpMem_single hl'] at he'
      simp only [Option.map_some, Option.some.injEq] at he he'
      subst he he'
      exact ih f1 tg
        { prog := { base := u.prog.base.setLpc ((G.blk tg).start + 1), lfn := u.prog.lfn },
          zf := u.zf }
        { prog := { base := u'.prog.base.setLpc ((G'.blk tg).start + 1), lfn := u'.prog.lfn },
          zf := u'.zf } t t' f1' ℓ1 ℓ1' (measure_lt hN (show f1 + 1 ≤ fuel by omega)) htg
        (Or.inr ⟨rfl, label_at hl, rfl, label_at hl'⟩) (hsucc tg (by simp [hT, Term.succs]))
        (hfs tg (by simp [hT, Term.succs])) hul' hr1 hr1'
    · rw [ite_eq_right hd] at he
      rw [ite_eq_right (by rw [hdec]; exact hd)] at he'
      simp only [Option.some.injEq] at he he'
      subst he he'
      refine fall_contL (w := { u with prog := { u.prog with base := u.prog.base.nextPc } })
        (w' := { u' with prog := { u'.prog with base := u'.prog.base.nextPc } })
        hc ih hk hnx.symm hnx'.symm ?_ ?_ hul' hul'' hr1 hr1'
        (measure_le hN (show f1 ≤ fuel by omega) hk)
        (fun j hj => hsucc j (by simp [hT, Term.succs, hj]))
        (fun j hj => hfs j (by simp [hT, Term.succs, hj]))
      · show u.prog.base.reg.lpc + 1 = _; omega
      · show u'.prog.base.reg.lpc + 1 = _; omega
  · exact absurd hT hret

theorem simAtL_all {I : Isa} {sym : LinstrRM → SSt → SOut} {dec : SSt → LOperand → SDec}
    (hL : SymLaws I sym dec) {outs : List String} {L : Nat → List String × Bool}
    {A A' : Nat → List CFact} {B B' : List LinstrRM}
    {G G' : CFG} {fn : String} (hc : CheckedC outs L A A' B B' G G' sym dec)
    (hlk : ∀ k < G.blocks.size,
      leakOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym A A' = true) :
    ∀ N, SimAtL I L A A' B B' G G' fn N
  | 0 => fun _ _ _ _ _ _ _ _ _ hN => absurd hN (Nat.not_lt_zero _)
  | N + 1 => sim_stepL hL hc hlk (simAtL_all hL hc hlk N)

/-! ## 6. Soundness on traced runs -/

/-- **One trace for given live sets and facts, over an instruction set.** If the symbolic
    step `sym` and branch condition `dec` satisfy `SymLaws I sym dec`, the two bodies satisfy
    `CheckedC` for the live sets `L` and the facts `A` and `A'`, and every block pair passes
    `leakOk`, a halting traced run of `B` and a halting traced run of `B'` on `I`, both from
    one state at pc `0`, have one trace. -/
theorem checkedC_trace_at {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec)
    {outs : List String} {L : Nat → List String × Bool} {A A' : Nat → List CFact}
    {B B' : List LinstrRM} {G G' : CFG} (hc : CheckedC outs L A A' B B' G G' sym dec)
    (hlk : ∀ k < G.blocks.size,
      leakOk L k (G.blk k).term B B' (G.blk k) (G'.blk k) sym A A' = true) (fn : String)
    (s : LstateMF) (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.reg.lpc = 0) {fuel f' : Nat} {t t' : LstateMF} {ℓ ℓ' : List CTLeak}
    (hrun : I.lsemFuelMemFLeak (singletonProgM fn B) fuel s = some (t, ℓ))
    (hrun' : I.lsemFuelMemFLeak (singletonProgM fn B') f' s = some (t', ℓ')) : ℓ' = ℓ := by
  obtain ⟨h0, hs0⟩ := cfgOf_start_zero hc.hG hc.ne
  obtain ⟨-, hs0'⟩ := cfgOf_start_zero hc.hG' hc.ne'
  exact simAtL_all hL hc hlk _ fuel 0 s s t t' f' ℓ ℓ' (Nat.lt_succ_self _) h0
    (Or.inl ⟨hpc.trans hs0.symm, hpc.trans hs0'.symm⟩)
    ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩
    ⟨(by rw [factCheck_entry hc.facts]; intro f hf; cases hf),
      (by rw [factCheck_entry hc.facts']; intro f hf; cases hf)⟩ hfn hrun hrun'

/-- **One trace for given live sets, over an instruction set.** If the symbolic step `sym`
    and branch condition `dec` satisfy `SymLaws I sym dec`, and
    `ownedCheckWith outs L B B' sym dec` and `leakCheckWith L B B' sym` accept, a halting
    traced run of `B` and a halting traced run of `B'` on `I`, both from one state at pc `0`,
    have one trace. -/
theorem ownedCheckWithL_trace_at {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec)
    {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM} (h : ownedCheckWith outs L B B' sym dec = true)
    (hlk : leakCheckWith L B B' sym = true) (fn : String) (s : LstateMF)
    (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.reg.lpc = 0) {fuel f' : Nat} {t t' : LstateMF} {ℓ ℓ' : List CTLeak}
    (hrun : I.lsemFuelMemFLeak (singletonProgM fn B) fuel s = some (t, ℓ))
    (hrun' : I.lsemFuelMemFLeak (singletonProgM fn B') f' s = some (t', ℓ')) : ℓ' = ℓ := by
  obtain ⟨G, G', hc⟩ := checkedC_of_with h
  exact checkedC_trace_at hL hc (leakCheckWith_spec hc.hG hc.hG' hlk) fn s hfn hpc hrun hrun'

/-- **One trace for given live sets.** If `ownedCheckWith outs L B B'` and
    `leakCheckWith L B B'` accept, a halting traced run of `B` and a halting traced run of
    `B'`, both from one state at pc `0`, have one trace. -/
theorem ownedCheckWithL_trace {outs : List String} {L : Nat → List String × Bool}
    {B B' : List LinstrRM} (h : ownedCheckWith outs L B B' = true)
    (hlk : leakCheckWith L B B' = true) (fn : String) (s : LstateMF) (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.reg.lpc = 0) {fuel f' : Nat} {t t' : LstateMF} {ℓ ℓ' : List CTLeak}
    (hrun : lsemFuelMemFLeak (singletonProgM fn B) fuel s = some (t, ℓ))
    (hrun' : lsemFuelMemFLeak (singletonProgM fn B') f' s = some (t', ℓ')) : ℓ' = ℓ := by
  rw [← x86Isa_lsemFuelMemFLeak] at hrun hrun'
  exact ownedCheckWithL_trace_at symLaws_x86 h hlk fn s hfn hpc hrun hrun'

/-- **One trace under `ownedCheckML`, over an instruction set.** -/
theorem ownedCheckML_trace_at {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec) (hS : SymSubst sym dec)
    {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckML outs B B' sym dec = true) (fn : String) (s : LstateMF)
    (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.reg.lpc = 0) {fuel f' : Nat} {t t' : LstateMF} {ℓ ℓ' : List CTLeak}
    (hrun : I.lsemFuelMemFLeak (singletonProgM fn B) fuel s = some (t, ℓ))
    (hrun' : I.lsemFuelMemFLeak (singletonProgM fn B') f' s = some (t', ℓ')) : ℓ' = ℓ := by
  obtain ⟨L, A, A', G, G', hc, hlk⟩ := ownedCheckML_checked_at hS h
  exact checkedC_trace_at hL hc hlk fn s hfn hpc hrun hrun'

/-- **One trace under `ownedCheckML`.** If `ownedCheckML outs B B'` accepts, a halting traced
    run of `B` and a halting traced run of `B'`, both from one state at pc `0` of that
    function, have one trace. -/
theorem ownedCheckML_trace {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckML outs B B' = true) (fn : String) (s : LstateMF) (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.reg.lpc = 0) {fuel f' : Nat} {t t' : LstateMF} {ℓ ℓ' : List CTLeak}
    (hrun : lsemFuelMemFLeak (singletonProgM fn B) fuel s = some (t, ℓ))
    (hrun' : lsemFuelMemFLeak (singletonProgM fn B') f' s = some (t', ℓ')) : ℓ' = ℓ := by
  rw [← x86Isa_lsemFuelMemFLeak] at hrun hrun'
  exact ownedCheckML_trace_at symLaws_x86 symSubst_x86 h fn s hfn hpc hrun hrun'

/-- **Soundness of the checker on traced runs, over an instruction set.** If the symbolic
    step `sym` and branch condition `dec` satisfy `SymLaws I sym dec` and `SymSubst sym dec`,
    and `ownedCheckML outs B B' sym dec` accepts, a halting checked run of `B` on `I` from a
    state at pc `0` of that function, with trace `ℓ`, is matched by a halting checked run of
    `B'` from the same state, the end states agreeing on `outs`, on the arrays and on the
    word memory, whose traced run has the trace `ℓ`. -/
theorem ownedCheckML_sound_leak_at {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec) (hS : SymSubst sym dec)
    {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckML outs B B' sym dec = true) (fn : String) (s t : LstateMF)
    (hfn : s.prog.lfn = fn) (hpc : s.prog.base.reg.lpc = 0) (fuel : Nat)
    (hrun : I.lsemFuelMemFk true (singletonProgM fn B) fuel s = some t) {ℓ : List CTLeak}
    (hl : I.FRun (singletonProgM fn B) s ℓ) :
    ∃ fuel' t', I.lsemFuelMemFk true (singletonProgM fn B') fuel' s = some t' ∧
      Obs outs t t' ∧ I.FRun (singletonProgM fn B') s ℓ := by
  obtain ⟨L, A, A', G, G', hc, hob⟩ := ownedCheckML_checkedObl_at hS h
  obtain ⟨f', t', -, hr, hobs, hok⟩ := OwnedCheckFuel.checkedC_sound_at_fuel hL hc hob fn s t
    hfn hpc fuel (I.lsemFuelMemF_of_checked _ fuel s t hrun) (I.runIdxOk_of_checked _ fuel s t hrun)
  have hr' := I.lsemFuelMemFk_of_runIdxOk true _ f' s t' hr hok
  refine ⟨f', t', hr', hobs, ?_⟩
  have hu := I.lsemFuelMemF_of_checked _ f' s t' hr'
  rw [← I.lsemFuelMemFLeak_fst] at hu
  obtain ⟨⟨t2, ℓ'⟩, h2, -⟩ := Option.map_eq_some_iff.mp hu
  obtain ⟨g, t1, h1⟩ := hl
  rw [← ownedCheckML_trace_at hL hS h fn s hfn hpc h1 h2]
  exact ⟨f', t2, h2⟩

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
  rw [← x86Isa_lsemFuelMemFk] at hrun
  rw [← x86Isa_FRun] at hl
  simpa only [x86Isa_lsemFuelMemFk, x86Isa_FRun] using
    ownedCheckML_sound_leak_at symLaws_x86 symSubst_x86 h fn s t hfn hpc fuel hrun hl

/-! ## 7. Constant time -/

/-- Public-equal entry states of `B` at pc `0` of `fn` with halting checked runs of `B` on
    the instruction set `I`. -/
def TVPubAt (I : Isa) (fn : String) (B : List LinstrRM) (pubEq : LstateMF → LstateMF → Prop)
    (s₁ s₂ : LstateMF) : Prop :=
  pubEq s₁ s₂ ∧ s₁.prog.lfn = fn ∧ s₂.prog.lfn = fn ∧ s₁.prog.base.reg.lpc = 0
    ∧ s₂.prog.base.reg.lpc = 0
    ∧ (∃ f t, I.lsemFuelMemFk true (singletonProgM fn B) f s₁ = some t)
    ∧ (∃ f t, I.lsemFuelMemFk true (singletonProgM fn B) f s₂ = some t)

/-- Public-equal entry states of `B` at pc `0` of `fn` with halting checked runs of `B`. -/
def TVPub (fn : String) (B : List LinstrRM) (pubEq : LstateMF → LstateMF → Prop)
    (s₁ s₂ : LstateMF) : Prop :=
  pubEq s₁ s₂ ∧ s₁.prog.lfn = fn ∧ s₂.prog.lfn = fn ∧ s₁.prog.base.reg.lpc = 0
    ∧ s₂.prog.base.reg.lpc = 0
    ∧ (∃ f t, lsemFuelMemFk true (singletonProgM fn B) f s₁ = some t)
    ∧ (∃ f t, lsemFuelMemFk true (singletonProgM fn B) f s₂ = some t)

/-- **Constant time through the checker, over an instruction set.** If the symbolic step
    `sym` and branch condition `dec` satisfy `SymLaws I sym dec` and `SymSubst sym dec`,
    `ownedCheckML outs B B' sym dec` accepts and `B` is constant time on `I` for `pubEq`, then
    `B'` is constant time on `I` between public-equal entry states of `B` at pc `0` from
    which `B` has halting checked runs (`TVPubAt`). -/
theorem memFCT_of_ownedCheckML_at {I : Isa} {sym : LinstrRM → SSt → SOut}
    {dec : SSt → LOperand → SDec} (hL : SymLaws I sym dec) (hS : SymSubst sym dec)
    {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckML outs B B' sym dec = true) (fn : String)
    {pubEq : LstateMF → LstateMF → Prop}
    (hct : I.MemFCT (singletonProgM fn B) pubEq) :
    I.MemFCT (singletonProgM fn B') (TVPubAt I fn B pubEq) := by
  rintro s₁ s₂ ℓ₁ ℓ₂ ⟨hp, hfn₁, hfn₂, hpc₁, hpc₂, ⟨f₁, t₁, hk₁⟩, ⟨f₂, t₂, hk₂⟩⟩
    ⟨g₁, r₁, hr₁⟩ ⟨g₂, r₂, hr₂⟩
  have hsrc : ∀ (s : LstateMF) (f : Nat) (t : LstateMF),
      I.lsemFuelMemFk true (singletonProgM fn B) f s = some t →
      ∃ ℓ, I.FRun (singletonProgM fn B) s ℓ := by
    intro s f t hk
    have hu := I.lsemFuelMemF_of_checked _ f s t hk
    rw [← I.lsemFuelMemFLeak_fst] at hu
    obtain ⟨⟨t', ℓ⟩, h', -⟩ := Option.map_eq_some_iff.mp hu
    exact ⟨ℓ, f, t', h'⟩
  obtain ⟨v₁, hv₁⟩ := hsrc s₁ f₁ t₁ hk₁
  obtain ⟨v₂, hv₂⟩ := hsrc s₂ f₂ t₂ hk₂
  obtain ⟨g₁', t₁', hv₁'⟩ := hv₁
  obtain ⟨g₂', t₂', hv₂'⟩ := hv₂
  rw [ownedCheckML_trace_at hL hS h fn s₁ hfn₁ hpc₁ hv₁' hr₁,
    ownedCheckML_trace_at hL hS h fn s₂ hfn₂ hpc₂ hv₂' hr₂]
  exact hct s₁ s₂ v₁ v₂ hp ⟨g₁', t₁', hv₁'⟩ ⟨g₂', t₂', hv₂'⟩

/-- **Constant time through the checker.** If `ownedCheckML outs B B'` accepts and `B` is
    constant time on the flag machine for `pubEq`, then `B'` is constant time on the flag
    machine between public-equal entry states of `B` at pc `0` from which `B` has halting
    checked runs (`TVPub`). -/
theorem memFCT_of_ownedCheckML {outs : List String} {B B' : List LinstrRM}
    (h : ownedCheckML outs B B' = true) (fn : String) {pubEq : LstateMF → LstateMF → Prop}
    (hct : MemFCT (singletonProgM fn B) pubEq) :
    MemFCT (singletonProgM fn B') (TVPub fn B pubEq) := by
  have hct' : x86Isa.MemFCT (singletonProgM fn B) pubEq := fun s₁ s₂ ℓ₁ ℓ₂ hp h₁ h₂ =>
    hct s₁ s₂ ℓ₁ ℓ₂ hp ((x86Isa_FRun _ _ _).mp h₁) ((x86Isa_FRun _ _ _).mp h₂)
  have hat := memFCT_of_ownedCheckML_at symLaws_x86 symSubst_x86 h fn hct'
  intro s₁ s₂ ℓ₁ ℓ₂ hp h₁ h₂
  refine hat s₁ s₂ ℓ₁ ℓ₂ ?_ ((x86Isa_FRun _ _ _).mpr h₁) ((x86Isa_FRun _ _ _).mpr h₂)
  simpa only [TVPubAt, TVPub, x86Isa_lsemFuelMemFk] using hp

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedTVLeak
