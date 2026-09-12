/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTReturn

/-!
# Indirect-branch misprediction over a modelled indirect-call structure

`SpeculativeCTMachine` is the store-bypass (Spectre-v4) layer over
`List (JInstr w)`, `SpeculativeCTControlFlow` the branch-misprediction
(Spectre-v1 / PHT) layer over `MachineConstantTime.OwnedCF`, and
`SpeculativeCTReturn` the return-misprediction (Spectre-RSB) layer over `CallCF`.
This module is the indirect-branch (Spectre-v2 / BTB) layer over `ICallCF`.

## The modelling assumption, and how it differs from the other three variants

`JasminModel.JInstr` has no indirect jump, `Jasmin.LowCT` has no indirect-jump
node, and `LprogBytes.encodeLinstrR` encodes `LinstrR.Ligoto` to the empty byte
list (`encodeLinstrR_Ligoto_nil` below). So no source, no IR node and no emitted
byte of the owned pipeline carries an indirect branch, and there is nothing in
the pipeline for an indirect-branch speculation site to attach to.

`ICallCF` is therefore a **modelled** syntax: a block structure carrying an
explicit indirect-call node with a target register and a callee table supplied to
the semantics. Every theorem below is a statement about that syntax. No theorem
maps a `Com`, an `Lcmd`, a `LowCT` command or a `List (JInstr w)` to an
`ICallCF.icall`, and none can, because no such node exists downstream.

This is a weaker connection to the emitted artifact than the other three
variants have. `SpeculativeCTControlFlow.toLprogPhysAbi_gather_cfSpec_state_independent`
and `SpeculativeCTReturn.toLprogPhysAbi_gather_callSpec_state_independent` land
on the block the deployed export gathers; the analogue here,
`toLprogPhysAbi_gather_icallSpec_state_independent`, lands on the same gathered
block and holds because that block is `ICallFree` — it says the deployed leaf has
no indirect-branch site, not that the model has been connected to it.

`SpeculativeCT.specObs` models the same site at `.RCall` by reading the predicted
callee pointer as word `0` of the call's destination slot. `ICallCF` does not
inherit that particular assumption: the indirect-call node carries its own target
register and the callee table is a parameter of the semantics, so the predicted
callee is an entry of that table rather than a word read out of the state at the
architectural site. What both share is that the node itself is postulated.

## The model

`ICallCF w` is `OwnedCF w` leaves, sequential composition, and a node
`icall tgt cont`: an indirect call through the target register `tgt`, continuing
with `cont`. `BTBTable w` is the callee table — the indirect-branch target set of
the program — supplied to the semantics, as `RSB` is in `SpeculativeCTReturn`.
The architecturally taken callee is the table entry the runtime value of `tgt`
indexes (`icallTarget`); an out-of-range value takes no callee.

`icallExec` is the architectural leakage semantics: the indirect transfer emits
`MachineConstantTime.MLeak.branch`, then the taken callee's trace, then the
continuation. `icallSpecExec window P table s cc` adds the BTB: when the window is
open and the predictor `P` names a table index other than the architectural one,
that entry's architectural trace, truncated to `window` and closed by
`SpeculativeCTControlFlow.SLeak.rollback`, is emitted before the taken callee
runs.

The transient contribution is the *mispredicted* table entry's trace. The
architectural clause at the same site emits `MLeak.branch` and the *taken*
entry's trace. `icallDemo_transient_not_architectural` exhibits a state at which
the transient clause emits an event the architectural trace does not contain.

## The results

`icallSpecExec_arch_mem` is predictor-free: on the index-free fragment every
memory event of the speculative trace — architectural or transient — names an
address drawn from the program text of the block or of a table entry.
`icallIndexed_escapes_program_text` exhibits a table entry outside that fragment
whose speculative trace names an address outside the program text.

`owned_sct_indirect` is the leakage-equality result: an `ICallControlled` block
over a `CFControlled` callee table, under a `BTBPubDriven` predictor, has the same
speculative trace from any two states agreeing on the public registers.
Both hypotheses are used: `secretDrivenBTBPredictor_leaks` separates two
public-equivalent states with a predictor reading a secret register, and
`secretTargetICall_leaks` separates them with a secret target register at the
predictor that never mispredicts.

`icallSpecExec_of_icallFree` is the scoping result: a block with no indirect-call
node has no BTB site, so its speculative trace is its architectural trace for
every predictor, window and table.

## Scope

Modelled: indirect-branch target misprediction at an indirect-call node, with a
callee table and a bounded transient window.

Not modelled: store-to-load forwarding (`SpeculativeCTMachine`), branch
misprediction (`SpeculativeCTControlFlow`), return misprediction
(`SpeculativeCTReturn`), an indirect call inside a callee table entry — table
entries are `OwnedCF w`, so callees carry no further indirect-call node — nested
mis-speculation inside a transient window, a predicted target outside the callee
table, cache-line granularity, and port contention.

## References

* Kocher, Horn, Fogh, Genkin, Gruss, Haas, Hamburg, Lipp, Mangard, Prescher,
  Schwarz, Yarom, "Spectre Attacks: Exploiting Speculative Execution",
  S&P 2019 (variant 2, branch target injection).
* Cauligi, Disselkoen, von Gleissenthall, Tullsen, Stefan, Rezk, Barthe,
  "Constant-Time Foundations for the New Spectre Era", PLDI 2020.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTIndirect

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTControlFlow
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTReturn

/-! ## 1. The block structure with indirect-call sites -/

/-- A structured block with indirect-call sites.

    * `leaf cf` — an owned control-flow block (`MachineConstantTime.OwnedCF`).
      It carries no indirect-call site, since `JInstr` has no indirect-jump
      constructor.
    * `seq a b` — sequential composition.
    * `icall tgt cont` — an indirect call through the target register `tgt`,
      continuing with `cont`. The callee is the entry of the callee table that the
      runtime value of `tgt` indexes; the transfer is the speculation site. -/
inductive ICallCF (w : Nat) where
  /-- An owned control-flow block, with no indirect-call site. -/
  | leaf (cf : OwnedCF w)
  /-- Sequential composition of two blocks. -/
  | seq (a b : ICallCF w)
  /-- An indirect call through target register `tgt`, continuing with `cont`. -/
  | icall (tgt : String) (cont : ICallCF w)

/-- The callee table: the indirect-branch target set of the program, indexed by
    the runtime value of a target register. Its entries are owned control-flow
    blocks. -/
abbrev BTBTable (w : Nat) := List (OwnedCF w)

/-! ## 2. The architectural semantics -/

/-- The callee an indirect call takes: the table entry the runtime value of the
    target register indexes, or none when that value is out of range. -/
def icallTarget {w : Nat} (table : BTBTable w) (s : JState w) (tgt : String) :
    Option (OwnedCF w) :=
  table[(s.get tgt).toNat]?

/-- The callee an indirect call takes is an entry of the callee table. -/
theorem icallTarget_mem {w : Nat} {table : BTBTable w} {s : JState w} {tgt : String}
    {c : OwnedCF w} (h : icallTarget table s tgt = some c) : c ∈ table :=
  List.mem_of_getElem? h

/-- The architectural leakage the taken callee contributes. -/
def icallTakenLeak {w : Nat} (table : BTBTable w) (s : JState w) (tgt : String) :
    List MLeak :=
  match icallTarget table s tgt with
  | none => []
  | some c => (cfExec s c).1

/-- The state the taken callee leaves behind. -/
def icallTakenState {w : Nat} (table : BTBTable w) (s : JState w) (tgt : String) :
    JState w :=
  match icallTarget table s tgt with
  | none => s
  | some c => (cfExec s c).2

/-- An event of the taken callee's trace is an event of some table entry's
    architectural trace. -/
theorem mem_of_mem_icallTakenLeak {w : Nat} {table : BTBTable w} {s : JState w}
    {tgt : String} {e : MLeak} (h : e ∈ icallTakenLeak table s tgt) :
    ∃ c, c ∈ table ∧ e ∈ (cfExec s c).1 := by
  unfold icallTakenLeak at h
  split at h
  · exact absurd h (by simp)
  · rename_i c hc
    exact ⟨c, icallTarget_mem hc, h⟩

/-- `icallExec table s cc = (leak, s')`: the architectural machine leakage trace
    of the block `cc` from state `s` over the callee table `table`, together with
    the post-state. An indirect call emits the transfer decision, then the taken
    callee, then the continuation; leaves delegate to
    `MachineConstantTime.cfExec`. -/
def icallExec {w : Nat} (table : BTBTable w) (s : JState w) :
    ICallCF w → List MLeak × JState w
  | .leaf cf => cfExec s cf
  | .seq a b =>
      ((icallExec table s a).1 ++ (icallExec table (icallExec table s a).2 b).1,
       (icallExec table (icallExec table s a).2 b).2)
  | .icall tgt cont =>
      (MLeak.branch :: (icallTakenLeak table s tgt
          ++ (icallExec table (icallTakenState table s tgt) cont).1),
       (icallExec table (icallTakenState table s tgt) cont).2)

/-! ## 3. The branch-target predictor and the transient window -/

/-- A branch-target predictor: at an indirect call, given the whole machine state
    and the target register of the site, which table index does it name as the
    callee? `none` predicts the architecturally taken entry. An arbitrary function
    of the state, so a predictor may read secret registers. -/
abbrev BTBPredictor (w : Nat) := JState w → String → Option Nat

/-- The predictor that always names the architecturally taken callee. -/
def neverMispredictIndirect {w : Nat} : BTBPredictor w := fun _ _ => none

/-- The block an indirect call runs transiently: the table entry the predictor
    names, when the speculation window is open and that entry is neither the
    architecturally taken one nor out of range. -/
def mispredictICallTarget {w : Nat} (window : Nat) (P : BTBPredictor w)
    (table : BTBTable w) (s : JState w) (tgt : String) : Option (OwnedCF w) :=
  if 0 < window then
    match P s tgt with
    | none => none
    | some i => if i = (s.get tgt).toNat then none else table[i]?
  else none

@[simp] theorem mispredictICallTarget_of_window_zero {w : Nat} (P : BTBPredictor w)
    (table : BTBTable w) (s : JState w) (tgt : String) :
    mispredictICallTarget 0 P table s tgt = none := by
  simp [mispredictICallTarget]

@[simp] theorem mispredictICallTarget_neverMispredictIndirect {w : Nat} (window : Nat)
    (table : BTBTable w) (s : JState w) (tgt : String) :
    mispredictICallTarget window neverMispredictIndirect table s tgt = none := by
  simp [mispredictICallTarget, neverMispredictIndirect]

/-- A mispredicted callee is an entry of the callee table. -/
theorem mispredictICallTarget_mem {w : Nat} {window : Nat} {P : BTBPredictor w}
    {table : BTBTable w} {s : JState w} {tgt : String} {c : OwnedCF w}
    (h : mispredictICallTarget window P table s tgt = some c) : c ∈ table := by
  unfold mispredictICallTarget at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · exact List.mem_of_getElem? h
  · exact absurd h (by simp)

/-- The leakage a mispredicted indirect call contributes: the named table entry's
    architectural trace truncated to the speculation window, closed by a rollback
    marker; nothing when the prediction is correct. -/
def icallTransient {w : Nat} (window : Nat) (P : BTBPredictor w)
    (table : BTBTable w) (s : JState w) (tgt : String) : List SLeak :=
  match mispredictICallTarget window P table s tgt with
  | none => []
  | some c => (archTrace (cfExec s c).1).take window ++ [SLeak.rollback]

@[simp] theorem icallTransient_of_none {w : Nat} {window : Nat} {P : BTBPredictor w}
    {table : BTBTable w} {s : JState w} {tgt : String}
    (h : mispredictICallTarget window P table s tgt = none) :
    icallTransient window P table s tgt = [] := by
  simp [icallTransient, h]

/-- An event of a mispredicted indirect call's contribution is the rollback marker
    or an event of some table entry's architectural trace. -/
theorem mem_of_mem_icallTransient {w : Nat} {window : Nat} {P : BTBPredictor w}
    {table : BTBTable w} {s : JState w} {tgt : String} {x : SLeak}
    (h : x ∈ icallTransient window P table s tgt) :
    x = SLeak.rollback ∨ ∃ c, c ∈ table ∧ x ∈ archTrace (cfExec s c).1 := by
  unfold icallTransient at h
  split at h
  · exact absurd h (by simp)
  · rename_i c hc
    rcases List.mem_append.mp h with h' | h'
    · exact Or.inr ⟨c, mispredictICallTarget_mem hc, List.mem_of_mem_take h'⟩
    · exact Or.inl (List.mem_singleton.mp h')

/-! ## 4. The speculative semantics -/

/-- `icallSpecExec window P table s cc = (leak, s')`: the speculative leakage trace
    of the block `cc` from state `s` under branch-target predictor `P`, speculation
    window `window` and callee table `table`, together with the architectural
    post-state.

    A leaf contributes its architectural trace: it carries no indirect-call site.
    An indirect call emits the transfer decision, then the contribution of a
    mispredicted callee, then the architecturally taken callee, then the
    continuation from the taken callee's post-state. -/
def icallSpecExec {w : Nat} (window : Nat) (P : BTBPredictor w) (table : BTBTable w)
    (s : JState w) : ICallCF w → List SLeak × JState w
  | .leaf cf => (archTrace (cfExec s cf).1, (cfExec s cf).2)
  | .seq a b =>
      ((icallSpecExec window P table s a).1
          ++ (icallSpecExec window P table (icallSpecExec window P table s a).2 b).1,
       (icallSpecExec window P table (icallSpecExec window P table s a).2 b).2)
  | .icall tgt cont =>
      (SLeak.arch MLeak.branch
          :: (icallTransient window P table s tgt
              ++ archTrace (icallTakenLeak table s tgt)
              ++ (icallSpecExec window P table (icallTakenState table s tgt) cont).1),
       (icallSpecExec window P table (icallTakenState table s tgt) cont).2)

/-! ## 5. The architectural projection -/

/-- **The architectural projection.** A predictor that names no wrong callee
    reproduces the architectural leakage trace and post-state of `icallExec`. -/
theorem icallSpecExec_of_no_mispredict {w : Nat} (window : Nat) (P : BTBPredictor w)
    (table : BTBTable w)
    (hno : ∀ (s : JState w) (tgt : String),
      mispredictICallTarget window P table s tgt = none) (cc : ICallCF w) :
    ∀ s : JState w,
      icallSpecExec window P table s cc
        = (archTrace (icallExec table s cc).1, (icallExec table s cc).2) := by
  induction cc with
  | leaf cf => intro s; simp [icallSpecExec, icallExec]
  | seq a b iha ihb =>
    intro s
    simp only [icallSpecExec, icallExec, iha s, ihb (icallExec table s a).2,
      archTrace_append]
  | icall tgt cont ihcont =>
    intro s
    simp only [icallSpecExec, icallExec, ihcont (icallTakenState table s tgt),
      icallTransient_of_none (hno _ _), archTrace_append, archTrace_cons,
      List.nil_append]

/-- With the speculation window closed the speculative trace is the architectural
    trace, for every predictor. -/
theorem icallSpecExec_of_window_zero {w : Nat} (P : BTBPredictor w)
    (table : BTBTable w) (cc : ICallCF w) (s : JState w) :
    icallSpecExec 0 P table s cc
      = (archTrace (icallExec table s cc).1, (icallExec table s cc).2) :=
  icallSpecExec_of_no_mispredict 0 P table
    (fun _ _ => mispredictICallTarget_of_window_zero P table _ _) cc s

/-- Under the always-correct predictor the speculative trace is the architectural
    trace, for every window. -/
theorem icallSpecExec_neverMispredictIndirect {w : Nat} (window : Nat)
    (table : BTBTable w) (cc : ICallCF w) (s : JState w) :
    icallSpecExec window neverMispredictIndirect table s cc
      = (archTrace (icallExec table s cc).1, (icallExec table s cc).2) :=
  icallSpecExec_of_no_mispredict window neverMispredictIndirect table
    (fun _ _ => mispredictICallTarget_neverMispredictIndirect window table _ _) cc s

/-! ## 6. Indirect-call-free blocks have no branch-target site -/

/-- The block contains no indirect-call node. -/
def ICallFree {w : Nat} : ICallCF w → Prop
  | .leaf _ => True
  | .seq a b => ICallFree a ∧ ICallFree b
  | .icall _ _ => False

/-- **An indirect-call-free block has no branch-target speculation site.** Its
    speculative trace is its architectural trace, for every branch-target
    predictor, every speculation window and every callee table. -/
theorem icallSpecExec_of_icallFree {w : Nat} (window : Nat) (P : BTBPredictor w)
    (table : BTBTable w) (cc : ICallCF w) (h : ICallFree cc) :
    ∀ s : JState w,
      icallSpecExec window P table s cc
        = (archTrace (icallExec table s cc).1, (icallExec table s cc).2) := by
  induction cc with
  | leaf cf => intro s; simp [icallSpecExec, icallExec]
  | seq a b iha ihb =>
    intro s
    simp only [icallSpecExec, icallExec, iha h.1 s, ihb h.2 (icallExec table s a).2,
      archTrace_append]
  | icall tgt cont _ => exact absurd h (by simp [ICallFree])

/-! ## 7. The index-free fragment and its compile-time address set -/

/-- Every straight-line leaf of every owned block of `cc` addresses memory through
    a base register and a compile-time-constant displacement. -/
def ICallAllDirect {w : Nat} : ICallCF w → Prop
  | .leaf cf => CFAllDirect cf
  | .seq a b => ICallAllDirect a ∧ ICallAllDirect b
  | .icall _ cont => ICallAllDirect cont

/-- The address events the program text of a block contains, together with the
    transfer decision of each indirect call. -/
def icallAddrs {w : Nat} : ICallCF w → List MLeak
  | .leaf cf => cfAddrs cf
  | .seq a b => icallAddrs a ++ icallAddrs b
  | .icall _ cont => MLeak.branch :: icallAddrs cont

/-- **A speculative memory event names a program-text address.** On the index-free
    fragment every memory access the speculative trace records — architectural or
    transient — occurs in `A`, given that `A` covers the compile-time address set
    of the block and of every callee-table entry. No predictor, window, table or
    state produces an address outside `A`. -/
theorem icallSpecExec_arch_mem {w : Nat} (window : Nat) (P : BTBPredictor w)
    (A : List MLeak) (table : BTBTable w) (cc : ICallCF w) (hd : ICallAllDirect cc)
    (htd : ∀ c ∈ table, CFAllDirect c) (hA : ∀ e ∈ icallAddrs cc, e ∈ A)
    (hAt : ∀ c ∈ table, ∀ e ∈ cfAddrs c, e ∈ A) :
    ∀ (s : JState w) (e : MLeak),
      SLeak.arch e ∈ (icallSpecExec window P table s cc).1 → e ∈ A := by
  induction cc with
  | leaf cf =>
    intro s e he
    rw [icallSpecExec] at he
    exact hA e (cfExec_mem_cfAddrs cf hd s e (mem_of_arch_mem_archTrace he))
  | seq a b iha ihb =>
    intro s e he
    rw [icallSpecExec] at he
    rcases List.mem_append.mp he with h | h
    · exact iha hd.1 (fun e' he' => hA e' (List.mem_append_left _ he')) s e h
    · exact ihb hd.2 (fun e' he' => hA e' (List.mem_append_right _ he')) _ e h
  | icall tgt cont ihcont =>
    intro s e he
    have hcontA : ∀ e' ∈ icallAddrs cont, e' ∈ A :=
      fun e' he' => hA e' (List.mem_cons_of_mem _ he')
    rw [icallSpecExec] at he
    rcases List.mem_cons.mp he with h | h
    · cases h; exact hA _ (List.mem_cons_self ..)
    · rcases List.mem_append.mp h with h' | h'
      · rcases List.mem_append.mp h' with h'' | h''
        · rcases mem_of_mem_icallTransient h'' with hr | ⟨c, hc, hx⟩
          · exact absurd hr (by simp)
          · exact hAt c hc e
              (cfExec_mem_cfAddrs c (htd c hc) s e (mem_of_arch_mem_archTrace hx))
        · obtain ⟨c, hc, hx⟩ := mem_of_mem_icallTakenLeak (mem_of_arch_mem_archTrace h'')
          exact hAt c hc e (cfExec_mem_cfAddrs c (htd c hc) s e hx)
      · exact ihcont hd hcontA _ e h'

/-! ## 8. Leakage equality under a public-driven predictor

Whether a transient window opens, and which table entry it runs, are both
observations. Leakage equality across two states therefore needs the predictor to
name the same entry on both, which is the hypothesis `BTBPubDriven`, and needs
the architectural transfer to take the same entry on both, which is the public
target register `ICallControlled` demands at an indirect call. -/

/-- The block is CT-controlled: every owned leaf is
    `MachineConstantTime.CFControlled` and every indirect call's target register is
    public. -/
def ICallControlled (pub : PubPred) {w : Nat} : ICallCF w → Prop
  | .leaf cf => CFControlled pub cf
  | .seq a b => ICallControlled pub a ∧ ICallControlled pub b
  | .icall tgt cont => pub tgt = true ∧ ICallControlled pub cont

/-- A branch-target predictor is public-driven when it names the same table index
    on any two states that agree on the public registers. -/
def BTBPubDriven (pub : PubPred) {w : Nat} (P : BTBPredictor w) : Prop :=
  ∀ s₁ s₂ : JState w, agreePub pub s₁ s₂ → ∀ tgt : String, P s₁ tgt = P s₂ tgt

/-- The always-correct predictor is public-driven. -/
theorem btbPubDriven_neverMispredictIndirect (pub : PubPred) {w : Nat} :
    BTBPubDriven pub (neverMispredictIndirect (w := w)) := fun _ _ _ _ => rfl

/-- The architecturally taken callee is the same on states agreeing on the public
    registers, when the target register is public. -/
theorem icallTarget_pub_determined (pub : PubPred) {w : Nat} (table : BTBTable w)
    {s₁ s₂ : JState w} (hag : agreePub pub s₁ s₂) (tgt : String)
    (hpub : pub tgt = true) :
    icallTarget table s₁ tgt = icallTarget table s₂ tgt := by
  simp only [icallTarget, hag tgt hpub]

/-- The taken callee's trace is the same on states agreeing on the public
    registers, and its post-states still agree, when the target register is public
    and every table entry is CT-controlled. -/
theorem icallTaken_pub_determined (pub : PubPred) {w : Nat} (table : BTBTable w)
    (htab : ∀ c ∈ table, CFControlled pub c) {s₁ s₂ : JState w}
    (hag : agreePub pub s₁ s₂) (tgt : String) (hpub : pub tgt = true) :
    icallTakenLeak table s₁ tgt = icallTakenLeak table s₂ tgt
      ∧ agreePub pub (icallTakenState table s₁ tgt) (icallTakenState table s₂ tgt) := by
  have ht : icallTarget table s₁ tgt = icallTarget table s₂ tgt :=
    icallTarget_pub_determined pub table hag tgt hpub
  cases hc : icallTarget table s₁ tgt with
  | none =>
    have hc2 : icallTarget table s₂ tgt = none := by rw [← ht]; exact hc
    refine ⟨?_, ?_⟩
    · simp only [icallTakenLeak, hc, hc2]
    · simpa only [icallTakenState, hc, hc2] using hag
  | some c =>
    have hc2 : icallTarget table s₂ tgt = some c := by rw [← ht]; exact hc
    obtain ⟨hl, ha⟩ := cfExec_pub_determined pub c (htab c (icallTarget_mem hc)) s₁ s₂ hag
    simp only [icallTakenLeak, icallTakenState, hc, hc2]
    exact ⟨hl, ha⟩

/-- A public-driven predictor names the same table entry on states agreeing on the
    public registers, when the target register is public. -/
theorem mispredictICallTarget_pub_determined (pub : PubPred) {w : Nat} (window : Nat)
    {P : BTBPredictor w} (hP : BTBPubDriven pub P) (table : BTBTable w)
    {s₁ s₂ : JState w} (hag : agreePub pub s₁ s₂) (tgt : String)
    (hpub : pub tgt = true) :
    mispredictICallTarget window P table s₁ tgt
      = mispredictICallTarget window P table s₂ tgt := by
  simp only [mispredictICallTarget, hP s₁ s₂ hag tgt, hag tgt hpub]

/-- A mispredicted indirect call's contribution is the same on two states agreeing
    on the public registers, when the predictor is public-driven, the target
    register is public and every table entry is CT-controlled. -/
theorem icallTransient_pub_determined (pub : PubPred) {w : Nat} (window : Nat)
    {P : BTBPredictor w} (hP : BTBPubDriven pub P) (table : BTBTable w)
    (htab : ∀ c ∈ table, CFControlled pub c) {s₁ s₂ : JState w}
    (hag : agreePub pub s₁ s₂) (tgt : String) (hpub : pub tgt = true) :
    icallTransient window P table s₁ tgt = icallTransient window P table s₂ tgt := by
  have hm : mispredictICallTarget window P table s₁ tgt
      = mispredictICallTarget window P table s₂ tgt :=
    mispredictICallTarget_pub_determined pub window hP table hag tgt hpub
  cases hc : mispredictICallTarget window P table s₁ tgt with
  | none =>
    have hc2 : mispredictICallTarget window P table s₂ tgt = none := by rw [← hm]; exact hc
    rw [icallTransient_of_none hc, icallTransient_of_none hc2]
  | some c =>
    have hc2 : mispredictICallTarget window P table s₂ tgt = some c := by rw [← hm]; exact hc
    have hl : (cfExec s₁ c).1 = (cfExec s₂ c).1 :=
      (cfExec_pub_determined pub c (htab c (mispredictICallTarget_mem hc)) s₁ s₂ hag).1
    simp only [icallTransient, hc, hc2, hl]

/-- **Indirect-branch-misprediction leakage equality.** An `ICallControlled` block
    over a CT-controlled callee table produces, under a public-driven branch-target
    predictor, the same speculative leakage trace from any two states agreeing on
    the public registers, and preserves that agreement on the post-states, for
    every speculation window. -/
theorem icallSpecExec_pub_determined (pub : PubPred) {w : Nat} (window : Nat)
    {P : BTBPredictor w} (hP : BTBPubDriven pub P) (table : BTBTable w)
    (htab : ∀ c ∈ table, CFControlled pub c) (cc : ICallCF w)
    (hcc : ICallControlled pub cc) :
    ∀ s₁ s₂ : JState w, agreePub pub s₁ s₂ →
      (icallSpecExec window P table s₁ cc).1 = (icallSpecExec window P table s₂ cc).1
        ∧ agreePub pub (icallSpecExec window P table s₁ cc).2
            (icallSpecExec window P table s₂ cc).2 := by
  induction cc with
  | leaf cf =>
    intro s₁ s₂ hag
    obtain ⟨hl, ha⟩ := cfExec_pub_determined pub cf hcc s₁ s₂ hag
    rw [icallSpecExec, icallSpecExec]
    exact ⟨by rw [hl], ha⟩
  | seq a b iha ihb =>
    intro s₁ s₂ hag
    obtain ⟨hla, haa⟩ := iha hcc.1 s₁ s₂ hag
    obtain ⟨hlb, hab⟩ := ihb hcc.2 _ _ haa
    exact ⟨by rw [icallSpecExec, icallSpecExec, hla, hlb],
           by rw [icallSpecExec, icallSpecExec]; exact hab⟩
  | icall tgt cont ihcont =>
    intro s₁ s₂ hag
    obtain ⟨hpub, hcont⟩ := hcc
    obtain ⟨hlt, hat⟩ := icallTaken_pub_determined pub table htab hag tgt hpub
    obtain ⟨hlc, hac⟩ := ihcont hcont _ _ hat
    refine ⟨?_, by rw [icallSpecExec, icallSpecExec]; exact hac⟩
    rw [icallSpecExec, icallSpecExec, hlt, hlc,
      icallTransient_pub_determined pub window hP table htab hag tgt hpub]

/-- **The indirect-branch form of `owned_ct_control_flow`.** Over blocks built from
    owned control-flow leaves by sequencing and indirect calls, an `ICallControlled`
    block over a CT-controlled callee table leaks the same speculative trace under a
    public-driven branch-target predictor from any two states agreeing on the public
    registers, for every speculation window. -/
theorem owned_sct_indirect (pub : PubPred) {w : Nat} (window : Nat)
    {P : BTBPredictor w} (hP : BTBPubDriven pub P) (table : BTBTable w)
    (htab : ∀ c ∈ table, CFControlled pub c) (cc : ICallCF w)
    (hcc : ICallControlled pub cc) (s₁ s₂ : JState w) (hag : agreePub pub s₁ s₂) :
    (icallSpecExec window P table s₁ cc).1 = (icallSpecExec window P table s₂ cc).1 :=
  (icallSpecExec_pub_determined pub window hP table htab cc hcc s₁ s₂ hag).1

/-! ## 9. The worked indirect call, and what its architectural clause exposes

`btbDemoTable` has two entries: entry `0` touches no memory, entry `1` stores
through the public pointer `op`. `icallDemo` calls indirectly through the public
target register `g`, which is `0` in both `SpeculativeCTControlFlow.zeroState` and
`SpeculativeCTControlFlow.secretState`, so entry `0` is the architecturally taken
callee in both. -/

/-- The callee table: entry `0` touches no memory, entry `1` stores through the
    public pointer `op`. -/
def btbDemoTable : BTBTable 64 :=
  [ .straight [], .straight [ .storeMem "op" 0 (.reg "t") ] ]

/-- Every entry of `btbDemoTable` addresses memory through a base register and a
    compile-time displacement. -/
theorem btbDemoTable_allDirect : ∀ c ∈ btbDemoTable, CFAllDirect c := by
  intro c hc
  simp only [btbDemoTable, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · intro i hi; simp at hi
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact trivial

/-- Every entry of `btbDemoTable` is CT-controlled w.r.t.
    `MachineConstantTime.cfPub`. -/
theorem btbDemoTable_controlled : ∀ c ∈ btbDemoTable, CFControlled cfPub c := by
  intro c hc
  simp only [btbDemoTable, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · intro i hi; simp at hi
  · intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact ⟨by simp [idxReg], by simp [dstRegs]⟩

/-- An indirect call through the public target register `g`. -/
def icallDemo : ICallCF 64 := .icall "g" (.leaf (.straight []))

/-- `icallDemo` addresses memory through base registers and compile-time
    displacements. -/
theorem icallDemo_allDirect : ICallAllDirect icallDemo := by
  intro i hi; simp at hi

/-- `icallDemo` is CT-controlled w.r.t. `MachineConstantTime.cfPub`: its target
    register `g` is public. -/
theorem icallDemo_controlled : ICallControlled cfPub icallDemo := by
  refine ⟨by decide, ?_⟩
  intro i hi; simp at hi

/-- The architectural trace of `icallDemo` from `secretState`: the transfer
    decision, and nothing else — the taken callee is the empty table entry `0`. -/
theorem icallDemo_arch_trace :
    (icallExec btbDemoTable secretState icallDemo).1 = [MLeak.branch] := by
  simp [icallDemo, btbDemoTable, icallExec, icallTakenLeak, icallTakenState,
    icallTarget, cfExec, secretState, JState.get]

/-! ## 10. A secret-driven branch-target predictor separates public-equivalent
states

`BTBPubDriven` cannot be dropped: which table entry the transient window runs is
an observation, so a predictor reading the secret register `sec` gives two
public-equivalent states different speculative traces on a block that is both
`ICallControlled` and `ICallAllDirect`. -/

/-- A predictor that names table entry `1` exactly when the secret register `sec`
    is nonzero. -/
def secretBTBPredictor : BTBPredictor 64 :=
  fun s _ => if s.get "sec" = 0 then none else some 1

/-- `secretBTBPredictor` is not public-driven w.r.t.
    `MachineConstantTime.cfPub`. -/
theorem not_btbPubDriven_secretBTBPredictor :
    ¬ BTBPubDriven cfPub secretBTBPredictor := by
  intro h
  have := h zeroState secretState zeroState_agreePub_secretState "g"
  simp [secretBTBPredictor, zeroState, secretState, JState.get] at this

/-- The speculative trace from a state whose secret register is zero: the
    predictor names the architecturally taken callee, so only the transfer
    decision is observed. -/
theorem icallDemo_trace_zeroState :
    (icallSpecExec 1 secretBTBPredictor btbDemoTable zeroState icallDemo).1
      = [SLeak.arch MLeak.branch] := by
  simp [icallDemo, btbDemoTable, icallSpecExec, icallTransient,
    mispredictICallTarget, secretBTBPredictor, icallTakenLeak, icallTakenState,
    icallTarget, cfExec, zeroState, JState.get, archTrace]

/-- The speculative trace from a state whose secret register is nonzero: the
    predictor names table entry `1`, whose store is observed transiently before
    the rollback marker. -/
theorem icallDemo_trace_secretState :
    (icallSpecExec 1 secretBTBPredictor btbDemoTable secretState icallDemo).1
      = [SLeak.arch MLeak.branch, SLeak.arch (MLeak.mem "op" 0), SLeak.rollback] := by
  simp [icallDemo, btbDemoTable, icallSpecExec, icallTransient,
    mispredictICallTarget, secretBTBPredictor, icallTakenLeak, icallTakenState,
    icallTarget, cfExec, instrLeak, secretState, JState.get, archTrace]

/-- **A secret-driven branch-target predictor is not covered.** On a block that is
    both `ICallControlled` and `ICallAllDirect`, over a CT-controlled callee table,
    a predictor reading a secret register names a wrong table entry from one of two
    public-equivalent states and the architecturally taken one from the other, so
    the speculative traces differ. `BTBPubDriven` in `icallSpecExec_pub_determined`
    is therefore not removable. -/
theorem secretDrivenBTBPredictor_leaks :
    (icallSpecExec 1 secretBTBPredictor btbDemoTable zeroState icallDemo).1
      ≠ (icallSpecExec 1 secretBTBPredictor btbDemoTable secretState icallDemo).1 := by
  rw [icallDemo_trace_zeroState, icallDemo_trace_secretState]
  decide

/-- **The transient clause emits an event the architectural clause does not.**
    At `secretState` the mispredicted callee's store appears in the speculative
    trace and does not appear in the architectural trace of the same block from the
    same state. -/
theorem icallDemo_transient_not_architectural :
    SLeak.arch (MLeak.mem "op" 0)
        ∈ (icallSpecExec 1 secretBTBPredictor btbDemoTable secretState icallDemo).1
      ∧ SLeak.arch (MLeak.mem "op" 0)
        ∉ archTrace (icallExec btbDemoTable secretState icallDemo).1 := by
  constructor
  · rw [icallDemo_trace_secretState]; decide
  · rw [icallDemo_arch_trace]; decide

/-! ## 11. A secret target register separates public-equivalent states

The public target register `ICallControlled` demands at an indirect call cannot be
dropped either: with a secret target register the *architectural* transfer already
takes different table entries from two public-equivalent states, at the predictor
that never mispredicts. -/

/-- An indirect call through the secret target register `sec`. -/
def icallSecretTgt : ICallCF 64 := .icall "sec" (.leaf (.straight []))

/-- `icallSecretTgt` is not CT-controlled w.r.t. `MachineConstantTime.cfPub`: its
    target register `sec` is secret. -/
theorem not_icallControlled_icallSecretTgt :
    ¬ ICallControlled cfPub icallSecretTgt := by
  intro h
  have : cfPub "sec" = true := h.1
  simp [cfPub] at this

/-- The trace of `icallSecretTgt` from `zeroState`: entry `0` is taken. -/
theorem icallSecretTgt_trace_zeroState :
    (icallSpecExec 1 neverMispredictIndirect btbDemoTable zeroState icallSecretTgt).1
      = [SLeak.arch MLeak.branch] := by
  simp [icallSecretTgt, btbDemoTable, icallSpecExec, icallTakenLeak, icallTakenState,
    icallTarget, cfExec, zeroState, JState.get, archTrace]

/-- The trace of `icallSecretTgt` from `secretState`: entry `1` is taken, and its
    store is observed. -/
theorem icallSecretTgt_trace_secretState :
    (icallSpecExec 1 neverMispredictIndirect btbDemoTable secretState icallSecretTgt).1
      = [SLeak.arch MLeak.branch, SLeak.arch (MLeak.mem "op" 0)] := by
  simp [icallSecretTgt, btbDemoTable, icallSpecExec, icallTakenLeak, icallTakenState,
    icallTarget, cfExec, instrLeak, secretState, JState.get, archTrace]

/-- **A secret target register is not covered.** With the predictor that never
    mispredicts and a CT-controlled callee table, an indirect call through a secret
    target register takes different callees from two public-equivalent states, so
    the traces differ. The public-target-register clause of `ICallControlled` is
    therefore not removable. -/
theorem secretTargetICall_leaks :
    (icallSpecExec 1 neverMispredictIndirect btbDemoTable zeroState icallSecretTgt).1
      ≠ (icallSpecExec 1 neverMispredictIndirect btbDemoTable secretState
          icallSecretTgt).1 := by
  rw [icallSecretTgt_trace_zeroState, icallSecretTgt_trace_secretState]
  decide

/-! ## 12. A public-driven predictor that does mispredict

The hypotheses of `owned_sct_indirect` are satisfiable with a nonempty transient
window: `pubBTBPredictor` reads only the public register `g`, is public-driven,
and names a wrong table entry at `g = 0`. -/

/-- A predictor that names table entry `1` exactly when the public register `g` is
    zero. -/
def pubBTBPredictor : BTBPredictor 64 :=
  fun s _ => if s.get "g" = 0 then some 1 else none

/-- `pubBTBPredictor` is public-driven w.r.t. `MachineConstantTime.cfPub`. -/
theorem btbPubDriven_pubBTBPredictor : BTBPubDriven cfPub pubBTBPredictor := by
  intro s₁ s₂ hag tgt
  have hg : s₁.get "g" = s₂.get "g" := hag "g" (by decide)
  simp only [pubBTBPredictor, hg]

/-- The trace `pubBTBPredictor` produces on `icallDemo` from `zeroState`: the
    transfer decision, then the mispredicted entry `1`'s store and the rollback
    marker. -/
theorem icallDemo_pub_trace_zeroState :
    (icallSpecExec 1 pubBTBPredictor btbDemoTable zeroState icallDemo).1
      = [SLeak.arch MLeak.branch, SLeak.arch (MLeak.mem "op" 0), SLeak.rollback] := by
  simp [icallDemo, btbDemoTable, icallSpecExec, icallTransient,
    mispredictICallTarget, pubBTBPredictor, icallTakenLeak, icallTakenState,
    icallTarget, cfExec, instrLeak, zeroState, JState.get, archTrace]

/-- **The hypotheses of `owned_sct_indirect` are satisfiable with the transient
    window open.** `pubBTBPredictor` is public-driven and mispredicts at both
    states, and `icallDemo_pub_trace_zeroState` pins the common trace: it carries
    the mispredicted entry's store and the rollback marker, so the conclusion is
    not the drained-window equality of
    `icallSpecExec_neverMispredictIndirect`. -/
theorem icallDemo_pub_sct :
    (icallSpecExec 1 pubBTBPredictor btbDemoTable zeroState icallDemo).1
      = (icallSpecExec 1 pubBTBPredictor btbDemoTable secretState icallDemo).1 :=
  owned_sct_indirect cfPub 1 btbPubDriven_pubBTBPredictor btbDemoTable
    btbDemoTable_controlled icallDemo icallDemo_controlled zeroState secretState
    zeroState_agreePub_secretState

/-- **`icallSpecExec_arch_mem` applied to the worked indirect call.** Over
    `btbDemoTable`, every memory event the speculative trace of `icallDemo`
    records — architectural or transient — is the transfer decision or the store at
    `op + 0`, for every branch-target predictor, every window and every state. -/
theorem icallDemo_arch_mem (window : Nat) (P : BTBPredictor 64) (s : JState 64)
    (e : MLeak) (he : SLeak.arch e ∈ (icallSpecExec window P btbDemoTable s icallDemo).1) :
    e ∈ [MLeak.branch, MLeak.mem "op" 0] := by
  refine icallSpecExec_arch_mem window P [MLeak.branch, MLeak.mem "op" 0] btbDemoTable
    icallDemo icallDemo_allDirect btbDemoTable_allDirect ?_ ?_ s e he
  · intro e' he'
    simp only [icallDemo, icallAddrs, cfAddrs, List.flatMap_nil, List.mem_singleton] at he'
    simp [he']
  · intro c hc e' he'
    simp only [btbDemoTable, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · simp [cfAddrs] at he'
    · simp only [cfAddrs, List.flatMap_cons, List.flatMap_nil, instrAddrs,
        List.append_nil, List.mem_singleton] at he'
      simp [he']

/-! ## 13. A callee table outside the index-free fragment

`icallSpecExec_arch_mem` needs `CFAllDirect` of every callee-table entry. A table
entry using register-indexed addressing computes an address from a register value,
and the speculative trace then names an address the program text does not
contain. -/

/-- A callee table whose only entry is the register-indexed scatter
    `MachineConstantTime.indexedScatterLeaf`. -/
def btbIndexedTable : BTBTable 64 := [ .straight indexedScatterLeaf ]

/-- The entry of `btbIndexedTable` is outside the index-free fragment. -/
theorem btbIndexedTable_not_allDirect :
    ¬ (∀ c ∈ btbIndexedTable, CFAllDirect c) := by
  intro h
  exact indexedScatterLeaf_not_direct
    (h (.straight indexedScatterLeaf) (by simp [btbIndexedTable]))

/-- The register file holding `1` in the index register `idx`. -/
def idxState : JState 64 := { regs := fun r => if r = "idx" then 1 else 0 }

/-- **The address-set containment fails outside the index-free fragment.** Over
    `btbIndexedTable` the speculative trace of `icallDemo` from `idxState` names
    the address `op + 8`, which occurs neither in the block's compile-time address
    set nor in any table entry's. So the `CFAllDirect` hypothesis of
    `icallSpecExec_arch_mem` is not removable. -/
theorem icallIndexed_escapes_program_text :
    SLeak.arch (MLeak.mem "op" 8)
        ∈ (icallSpecExec 1 neverMispredictIndirect btbIndexedTable idxState icallDemo).1
      ∧ MLeak.mem "op" 8 ∉ icallAddrs icallDemo
      ∧ ∀ c ∈ btbIndexedTable, MLeak.mem "op" 8 ∉ cfAddrs c := by
  refine ⟨?_, ?_, ?_⟩
  · simp [icallDemo, btbIndexedTable, indexedScatterLeaf, icallSpecExec,
      icallTakenLeak, icallTakenState, icallTarget, cfExec, instrLeak, idxState,
      JState.get, archTrace]
  · simp [icallDemo, icallAddrs, cfAddrs]
  · intro c hc
    simp only [btbIndexedTable, List.mem_singleton] at hc
    subst hc
    simp [cfAddrs, indexedScatterLeaf, instrAddrs]

/-- The trace of the register-indexed leaf from `SpeculativeCTControlFlow.zeroState`:
    the scatter's effective address is `op + 0`. -/
theorem indexedLeaf_trace_zeroState :
    (icallSpecExec 1 neverMispredictIndirect btbDemoTable zeroState
        (.leaf (.straight indexedScatterLeaf))).1 = [SLeak.arch (MLeak.mem "op" 0)] := by
  simp [icallSpecExec, cfExec, indexedScatterLeaf, instrLeak, archTrace, zeroState,
    JState.get]

/-- The trace of the register-indexed leaf from `idxState`: the scatter's effective
    address is `op + 8`. -/
theorem indexedLeaf_trace_idxState :
    (icallSpecExec 1 neverMispredictIndirect btbDemoTable idxState
        (.leaf (.straight indexedScatterLeaf))).1 = [SLeak.arch (MLeak.mem "op" 8)] := by
  simp [icallSpecExec, cfExec, indexedScatterLeaf, instrLeak, archTrace, idxState,
    JState.get]

/-- **A register-indexed leaf is not covered.** Two states differing on the index
    register give the leaf different speculative traces, so the index-free
    hypothesis of `icallSpecExec_straight_isDirect` — and of the deployed-export
    result below — is not removable. -/
theorem indexedLeaf_icallSpec_leaks :
    (icallSpecExec 1 neverMispredictIndirect btbDemoTable zeroState
        (.leaf (.straight indexedScatterLeaf))).1
      ≠ (icallSpecExec 1 neverMispredictIndirect btbDemoTable idxState
          (.leaf (.straight indexedScatterLeaf))).1 := by
  rw [indexedLeaf_trace_zeroState, indexedLeaf_trace_idxState]
  decide

/-! ## 14. The emitted artifact has no indirect-branch site

`LprogBytes.encodeLinstrR` encodes `LinstrR.Ligoto` to the empty byte list, and
`SpeculativeCTPreservation.isControlTransfer` rejects it from the gather, so the
block the deployed export emits carries no indirect branch. The results below
scope the model to that block: it is an `ICallCF.leaf`, hence `ICallFree`, hence
its speculative trace is fixed by the program text. -/

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (gatherJBlock6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation (lcmdDirect)

/-- **The indirect jump encodes to no bytes.** `LprogBytes.encodeLinstrR` has no
    arm for `LinstrR.Ligoto`, so the owned backend emits nothing for an indirect
    jump and the emitted artifact carries no indirect-branch site. -/
theorem encodeLinstrR_Ligoto_nil (frame spillW : Nat) (dispOf : LLabel → Int)
    (o : LOperand) :
    LprogBytes.encodeLinstrR frame spillW dispOf (.Ligoto o) = [] := rfl

/-- The gathered block, read as an `ICallCF`, is indirect-call-free. -/
theorem gathered_icallFree (g : List (JInstr 64)) :
    ICallFree (ICallCF.leaf (OwnedCF.straight g)) := trivial

/-- A straight-line leaf in the index-free fragment has a speculative trace fixed
    by the program text, for every branch-target predictor, window and callee
    table. -/
theorem icallSpecExec_straight_isDirect {w : Nat} (window : Nat) (P : BTBPredictor w)
    {body : List (JInstr w)} (h : ∀ i ∈ body, IsDirect i) (table : BTBTable w)
    (s₁ s₂ : JState w) :
    (icallSpecExec window P table s₁ (.leaf (.straight body))).1
      = (icallSpecExec window P table s₂ (.leaf (.straight body))).1 := by
  rw [icallSpecExec, icallSpecExec, cfExec, cfExec,
    blockLeak_state_independent body h s₁ s₂]

/-- The `allDirect` form of `icallSpecExec_straight_isDirect`. -/
theorem icallSpecExec_straight_allDirect (window : Nat) (P : BTBPredictor 64)
    {body : List (JInstr 64)} (h : allDirect body = true) (table : BTBTable 64)
    (s₁ s₂ : JState 64) :
    (icallSpecExec window P table s₁ (.leaf (.straight body))).1
      = (icallSpecExec window P table s₂ (.leaf (.straight body))).1 :=
  icallSpecExec_straight_isDirect window P
    (ConstantTimeCoverage.allDirect_mem_isDirect body h) table s₁ s₂

/-- **The deployed export's gathered block under indirect-branch misprediction.**
    When the virtual body a `Com` lowers to uses no register-indexed operand, the
    block the deployed allocator emits has the same speculative leakage trace from
    any two machine states, for every branch-target predictor, every speculation
    window and every callee table.

    Covered: the leaf the export gathers, which carries no indirect call and so no
    branch-target site. Not covered: any body carrying an indirect branch — no such
    body gathers, `LinstrR.Ligoto` encodes to no bytes, and no lowering from any
    emitted form to an `ICallCF.icall` is established here; and a kernel using
    register-indexed addressing, which fails the `lcmdDirect` hypothesis. -/
theorem toLprogPhysAbi_gather_icallSpec_state_independent {Γ : Ctxt jasminDialect}
    {t : JasminTy} (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle) (immSlotMap : ImmSlotMap) (inLoadMap : InLoadMap)
    (outStoreMap : OutStoreMap) (abiArgs : List String) (abiTyin : List Nat)
    (residence : Option (Array Nat)) (abiW : Nat) (forceLivePin : Bool)
    (hd : lcmdDirect (comToLfundef com immSlotMap).lfd_body = true)
    {f : String × Lfundef} {g : List (JInstr 64)}
    (hf : f ∈ (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap outStoreMap
      abiArgs abiTyin residence abiW forceLivePin).lp_funcs)
    (hg : gatherJBlock6 f.2.lfd_body = some g)
    (window : Nat) (P : BTBPredictor 64) (table : BTBTable 64) (s₁ s₂ : JState 64) :
    (icallSpecExec window P table s₁ (.leaf (.straight g))).1
      = (icallSpecExec window P table s₂ (.leaf (.straight g))).1 :=
  icallSpecExec_straight_allDirect window P
    (AllocCTPreservation.toLprogPhysAbi_gather_allDirect com fname shiftImm immSlotMap
      inLoadMap outStoreMap abiArgs abiTyin residence abiW forceLivePin hd hf hg)
    table s₁ s₂

/-- An owned block read as an `ICallCF` leaf is index-free exactly when the owned
    block is. -/
theorem icallAllDirect_leaf {w : Nat} (cf : OwnedCF w) :
    ICallAllDirect (ICallCF.leaf cf) ↔ CFAllDirect cf := Iff.rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTIndirect
