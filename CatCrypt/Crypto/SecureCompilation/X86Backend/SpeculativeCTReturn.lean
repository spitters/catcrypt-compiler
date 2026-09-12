/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTControlFlow

/-!
# Return-target misprediction over the emitted call/return structure

`JasminModel.JInstr` has no call and no return constructor, so a gathered
`List (JInstr w)` block, and the structured block `MachineConstantTime.OwnedCF`
layered over it, cannot express a call. The call and the return reach bytes one
level up: `LprogBytes.encodeLinstrR` encodes `LinstrR.Lcall` as a `call rel32`,
and an exported function body ends in `LinstrR.Lret`, which the function framing
renders as the `ret` byte. A `call`/`ret` pair drives the hardware
return-stack buffer, so the return-target speculation site lives at the
`Lcmd`/`Lprog` level, above the block the machine leakage models work on.

`CallCF` is the block structure at that level: owned control-flow leaves, sequential
composition, and a call node carrying its callee and its continuation. `RSB` is the
return-stack buffer of pending continuations, `RSBPredictor` supplies a return
target at each return, and `callSpecExec` is the leakage semantics in which a
mispredicted return runs a wrong continuation for a bounded window before rolling
back.

`SpeculativeCTMachine` is the store-bypass (Spectre-v4) layer over
`List (JInstr w)`, and `SpeculativeCTControlFlow` the branch-misprediction
(Spectre-v1) layer over `OwnedCF`. This module is the return-misprediction
(Spectre-RSB) layer over `CallCF`, and follows the same idiom: a predictor that
reads the whole machine state, a speculation window, projection lemmas back to the
architectural trace, a predictor-free containment result, and a leakage-equality
result under a public-driven predictor.

## The model

`callExec` is the architectural leakage semantics: a call runs its callee and then
its continuation. `callSpecExec window P s rsb cc` adds the return site. At the
return of a call node, the correct target is the continuation the call pushed —
index `0` of the return-stack buffer. When the window is open and the predictor
names a different entry of the buffer, that entry's architectural trace, truncated
to `window` and closed by `SLeak.rollback`, is emitted before the correct
continuation runs. The buffer is the program's own pending return targets, so a
mispredicted return runs code the program contains, which is the return-stack
buffer underflow shape of Spectre-RSB.

## The three results

`callSpecExec_arch_mem` is predictor-free: on the index-free fragment
(`CallAllDirect`), every memory event of the speculative trace — architectural or
transient — names an address drawn from the program text of the block or of a
pending return target. No predictor, window, buffer or state produces an address
outside that set.

`owned_sct_return` is the leakage-equality result: a `CallControlled` block under an
`RSBPubDriven` predictor, with every pending return target `CallControlled`, has the
same speculative trace from any two states agreeing on the public registers.
`secretDrivenRetPredictor_leaks` shows `RSBPubDriven` cannot be dropped: whether a
transient window opens is itself an observation, so a predictor reading a secret
register separates two public-equivalent states on a block that is both
`CallControlled` and `CallAllDirect`.

`callSpecExec_of_callFree` is the scoping result for the deployed leaf: a block with
no call node has no return site, so its speculative trace is its architectural trace
for every predictor, window and buffer. The body the export gathers carries no
`Lcall` (`SpeculativeCTPreservation.gatherJBlock6_no_control_transfer`), so it is
such a block, and `toLprogPhysAbi_gather_callSpec_state_independent` composes the
scoping result with `AllocCTPreservation.toLprogPhysAbi_gather_allDirect`.

## Scope

Modelled: return-target misprediction at the return of a call node, with a
return-stack buffer of pending continuations and a bounded transient window.

Not modelled: store-to-load forwarding (`SpeculativeCTMachine`), branch
misprediction (`SpeculativeCTControlFlow`), indirect-jump misprediction
(`LinstrR.Ligoto` encodes to no bytes in `LprogBytes.encodeLinstrR`), nested
mis-speculation inside a transient window — the transient path contributes its
architectural trace — a return target outside the pending buffer, cache-line
granularity, port contention, and the caller-saved clobber a real `call` performs.

`CallCF` is a model of the emitted call structure, not the output of a lowering: no
theorem maps an `Lcmd` carrying `Lcall` to a `CallCF`.

## References

* Maisuradze, Rossow, "ret2spec: Speculative Execution Using Return Stack Buffers",
  CCS 2018.
* Koruyeh, Khasawneh, Song, Abu-Ghazaleh, "Spectre Returns! Speculation Attacks
  using the Return Stack Buffer", WOOT 2018.
* Cauligi, Disselkoen, von Gleissenthall, Tullsen, Stefan, Rezk, Barthe,
  "Constant-Time Foundations for the New Spectre Era", PLDI 2020.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTReturn

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTControlFlow

/-! ## 1. The call/return block structure -/

/-- A structured block with call sites.

    * `leaf cf` — an owned control-flow block (`MachineConstantTime.OwnedCF`):
      straight-line machine leaves, sequencing, counted loops and public-guard
      conditionals. It carries no call site, since `JInstr` has no call
      constructor.
    * `seq a b` — sequential composition.
    * `call callee cont` — a call to `callee` followed by the continuation `cont`.
      The call pushes `cont` as the return target; the return of `callee` is the
      speculation site. -/
inductive CallCF (w : Nat) where
  /-- An owned control-flow block, with no call site. -/
  | leaf (cf : OwnedCF w)
  /-- Sequential composition of two blocks. -/
  | seq (a b : CallCF w)
  /-- A call to `callee` whose return continues with `cont`. -/
  | call (callee cont : CallCF w)

/-- The return-stack buffer: the pending return targets, innermost first. Index `0`
    is the target the innermost pending call pushed, which is the architecturally
    correct target of the next return. -/
abbrev RSB (w : Nat) := List (CallCF w)

/-! ## 2. The architectural semantics -/

/-- `callExec s cc = (leak, s')`: the architectural machine leakage trace of the
    block `cc` from state `s`, together with the post-state. A call runs its callee
    and then its continuation; leaves delegate to `MachineConstantTime.cfExec`. -/
def callExec {w : Nat} (s : JState w) : CallCF w → List MLeak × JState w
  | .leaf cf => cfExec s cf
  | .seq a b =>
      ((callExec s a).1 ++ (callExec (callExec s a).2 b).1,
       (callExec (callExec s a).2 b).2)
  | .call callee cont =>
      ((callExec s callee).1 ++ (callExec (callExec s callee).2 cont).1,
       (callExec (callExec s callee).2 cont).2)

/-! ## 3. The return-target predictor and the transient window -/

/-- A return-target predictor: at a return, given the whole machine state and the
    return-stack buffer, which buffer entry does it name as the return target?
    `none` predicts the correct target. An arbitrary function of the state, so a
    predictor may read secret registers. -/
abbrev RSBPredictor (w : Nat) := JState w → RSB w → Option Nat

/-- The predictor that always names the correct return target. -/
def neverMispredictRet {w : Nat} : RSBPredictor w := fun _ _ => none

/-- The block a return runs transiently: the buffer entry the predictor names, when
    the speculation window is open and that entry is neither the correct target
    (index `0`) nor out of range. -/
def mispredictTarget {w : Nat} (window : Nat) (P : RSBPredictor w) (s : JState w)
    (rsb : RSB w) : Option (CallCF w) :=
  if 0 < window then
    match P s rsb with
    | none => none
    | some i => if i = 0 then none else rsb[i]?
  else none

@[simp] theorem mispredictTarget_of_window_zero {w : Nat} (P : RSBPredictor w)
    (s : JState w) (rsb : RSB w) : mispredictTarget 0 P s rsb = none := by
  simp [mispredictTarget]

@[simp] theorem mispredictTarget_neverMispredictRet {w : Nat} (window : Nat)
    (s : JState w) (rsb : RSB w) :
    mispredictTarget window neverMispredictRet s rsb = none := by
  simp [mispredictTarget, neverMispredictRet]

/-- A mispredicted return target is a pending return target of the buffer. -/
theorem mispredictTarget_mem {w : Nat} {window : Nat} {P : RSBPredictor w}
    {s : JState w} {rsb : RSB w} {c : CallCF w}
    (h : mispredictTarget window P s rsb = some c) : c ∈ rsb := by
  unfold mispredictTarget at h
  split at h
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · exact List.mem_of_getElem? h
  · exact absurd h (by simp)

/-- The leakage a mispredicted return contributes: the named buffer entry's
    architectural trace truncated to the speculation window, closed by a rollback
    marker; nothing when the prediction is correct. -/
def retTransient {w : Nat} (window : Nat) (P : RSBPredictor w) (s : JState w)
    (rsb : RSB w) : List SLeak :=
  match mispredictTarget window P s rsb with
  | none => []
  | some c => (archTrace (callExec s c).1).take window ++ [SLeak.rollback]

@[simp] theorem retTransient_of_none {w : Nat} {window : Nat} {P : RSBPredictor w}
    {s : JState w} {rsb : RSB w} (h : mispredictTarget window P s rsb = none) :
    retTransient window P s rsb = [] := by
  simp [retTransient, h]

/-- An event of a mispredicted return's contribution is the rollback marker or an
    event of some pending return target's architectural trace. -/
theorem mem_of_mem_retTransient {w : Nat} {window : Nat} {P : RSBPredictor w}
    {s : JState w} {rsb : RSB w} {x : SLeak}
    (h : x ∈ retTransient window P s rsb) :
    x = SLeak.rollback ∨ ∃ c, c ∈ rsb ∧ x ∈ archTrace (callExec s c).1 := by
  unfold retTransient at h
  split at h
  · exact absurd h (by simp)
  · rename_i c hc
    rcases List.mem_append.mp h with h' | h'
    · exact Or.inr ⟨c, mispredictTarget_mem hc, List.mem_of_mem_take h'⟩
    · exact Or.inl (List.mem_singleton.mp h')

/-! ## 4. The speculative semantics -/

/-- `callSpecExec window P s rsb cc = (leak, s')`: the speculative leakage trace of
    the block `cc` from state `s` under return-target predictor `P`, speculation
    window `window` and pending return targets `rsb`, together with the
    architectural post-state.

    A leaf contributes its architectural trace: it carries no return site. A call
    node runs its callee with its continuation pushed onto the buffer, then — at the
    return — the contribution of a mispredicted target, then the continuation from
    the unchanged state, which is the rollback. -/
def callSpecExec {w : Nat} (window : Nat) (P : RSBPredictor w) (s : JState w)
    (rsb : RSB w) (cc : CallCF w) : List SLeak × JState w :=
  match cc with
  | .leaf cf => (archTrace (cfExec s cf).1, (cfExec s cf).2)
  | .seq a b =>
      ((callSpecExec window P s rsb a).1
          ++ (callSpecExec window P (callSpecExec window P s rsb a).2 rsb b).1,
       (callSpecExec window P (callSpecExec window P s rsb a).2 rsb b).2)
  | .call callee cont =>
      ((callSpecExec window P s (cont :: rsb) callee).1
          ++ retTransient window P (callSpecExec window P s (cont :: rsb) callee).2
              (cont :: rsb)
          ++ (callSpecExec window P
                (callSpecExec window P s (cont :: rsb) callee).2 rsb cont).1,
       (callSpecExec window P
          (callSpecExec window P s (cont :: rsb) callee).2 rsb cont).2)

/-! ## 5. The architectural projection

With no mispredicted return the speculative trace is the architectural trace of
`callExec`, and the post-states coincide. This holds when the window is closed and
under the always-correct predictor. -/

/-- **The architectural projection.** A predictor that names no wrong return target
    reproduces the architectural leakage trace and post-state of `callExec`. -/
theorem callSpecExec_of_no_mispredict {w : Nat} (window : Nat) (P : RSBPredictor w)
    (hno : ∀ (s : JState w) (rsb : RSB w), mispredictTarget window P s rsb = none)
    (cc : CallCF w) :
    ∀ (s : JState w) (rsb : RSB w),
      callSpecExec window P s rsb cc = (archTrace (callExec s cc).1, (callExec s cc).2) := by
  induction cc with
  | leaf cf => intro s rsb; simp [callSpecExec, callExec]
  | seq a b iha ihb =>
    intro s rsb
    simp only [callSpecExec, callExec, iha s rsb, ihb (callExec s a).2 rsb, archTrace_append]
  | call callee cont ihcallee ihcont =>
    intro s rsb
    simp only [callSpecExec, callExec, ihcallee s (cont :: rsb),
      ihcont (callExec s callee).2 rsb, retTransient_of_none (hno _ _),
      archTrace_append, List.append_nil]

/-- With the speculation window closed the speculative trace is the architectural
    trace, for every predictor. -/
theorem callSpecExec_of_window_zero {w : Nat} (P : RSBPredictor w) (cc : CallCF w)
    (s : JState w) (rsb : RSB w) :
    callSpecExec 0 P s rsb cc = (archTrace (callExec s cc).1, (callExec s cc).2) :=
  callSpecExec_of_no_mispredict 0 P (fun _ _ => mispredictTarget_of_window_zero P _ _) cc s rsb

/-- Under the always-correct predictor the speculative trace is the architectural
    trace, for every window. -/
theorem callSpecExec_neverMispredictRet {w : Nat} (window : Nat) (cc : CallCF w)
    (s : JState w) (rsb : RSB w) :
    callSpecExec window neverMispredictRet s rsb cc
      = (archTrace (callExec s cc).1, (callExec s cc).2) :=
  callSpecExec_of_no_mispredict window neverMispredictRet
    (fun _ _ => mispredictTarget_neverMispredictRet window _ _) cc s rsb

/-! ## 6. Call-free blocks have no return site

The block the deployed export gathers is a straight-line `List (JInstr 64)`, hence a
`CallCF.leaf`, and `JInstr` has no call constructor. A block with no call node has no
return site, so no predictor, window or buffer changes its trace. -/

/-- The block contains no call node. -/
def CallFree {w : Nat} : CallCF w → Prop
  | .leaf _ => True
  | .seq a b => CallFree a ∧ CallFree b
  | .call _ _ => False

/-- **A call-free block has no return-speculation site.** Its speculative trace is
    its architectural trace, for every return-target predictor, every speculation
    window and every return-stack buffer. -/
theorem callSpecExec_of_callFree {w : Nat} (window : Nat) (P : RSBPredictor w)
    (cc : CallCF w) (h : CallFree cc) :
    ∀ (s : JState w) (rsb : RSB w),
      callSpecExec window P s rsb cc = (archTrace (callExec s cc).1, (callExec s cc).2) := by
  induction cc with
  | leaf cf => intro s rsb; simp [callSpecExec, callExec]
  | seq a b iha ihb =>
    intro s rsb
    simp only [callSpecExec, callExec, iha h.1 s rsb, ihb h.2 (callExec s a).2 rsb,
      archTrace_append]
  | call callee cont _ _ => exact absurd h (by simp [CallFree])

/-! ## 7. The index-free fragment and its compile-time address set -/

/-- Every straight-line leaf of every owned block of `cc` addresses memory through a
    base register and a compile-time-constant displacement. -/
def CallAllDirect {w : Nat} : CallCF w → Prop
  | .leaf cf => CFAllDirect cf
  | .seq a b => CallAllDirect a ∧ CallAllDirect b
  | .call callee cont => CallAllDirect callee ∧ CallAllDirect cont

/-- The address events the program text of a block contains, together with the
    branch decision of each conditional. -/
def callAddrs {w : Nat} : CallCF w → List MLeak
  | .leaf cf => cfAddrs cf
  | .seq a b => callAddrs a ++ callAddrs b
  | .call callee cont => callAddrs callee ++ callAddrs cont

/-- On the index-free fragment an architectural event of an owned block is an event
    of its compile-time address set. -/
theorem cfExec_mem_cfAddrs {w : Nat} (cf : OwnedCF w) (hd : CFAllDirect cf)
    (s : JState w) (e : MLeak) (he : e ∈ (cfExec s cf).1) : e ∈ cfAddrs cf := by
  refine cfSpecExec_arch_mem_cfAddrs 0 neverMispredict cf hd s e ?_
  rw [cfSpecExec_of_window_zero]
  exact List.mem_map_of_mem he

/-- On the index-free fragment an architectural event of a block is an event of its
    compile-time address set. -/
theorem callExec_mem_callAddrs {w : Nat} (cc : CallCF w) (hd : CallAllDirect cc) :
    ∀ (s : JState w) (e : MLeak), e ∈ (callExec s cc).1 → e ∈ callAddrs cc := by
  induction cc with
  | leaf cf => intro s e he; exact cfExec_mem_cfAddrs cf hd s e he
  | seq a b iha ihb =>
    intro s e he
    rw [callExec] at he
    rcases List.mem_append.mp he with h | h
    · exact List.mem_append_left _ (iha hd.1 s e h)
    · exact List.mem_append_right _ (ihb hd.2 _ e h)
  | call callee cont ihcallee ihcont =>
    intro s e he
    rw [callExec] at he
    rcases List.mem_append.mp he with h | h
    · exact List.mem_append_left _ (ihcallee hd.1 s e h)
    · exact List.mem_append_right _ (ihcont hd.2 _ e h)

/-! ## 8. A mispredicted return emits only program-text addresses

The predictor decides which pending return target runs, not what any instruction's
address depends on. On the index-free fragment every memory operand is a base
register plus a compile-time displacement, and a mispredicted return runs a pending
return target of the program, so every memory event of the speculative trace names
an address the block or one of its pending return targets contains. This holds for
every predictor, every window, every buffer and every state. -/

/-- **A speculative memory event names a program-text address.** On the index-free
    fragment every memory access the speculative trace records — architectural or
    transient — occurs in `A`, given that `A` covers the compile-time address set of
    the block and of every pending return target. No predictor, window, buffer or
    state produces an address outside `A`. -/
theorem callSpecExec_arch_mem {w : Nat} (window : Nat) (P : RSBPredictor w)
    (A : List MLeak) (cc : CallCF w) (hd : CallAllDirect cc)
    (hA : ∀ e ∈ callAddrs cc, e ∈ A) :
    ∀ (s : JState w) (rsb : RSB w),
      (∀ c ∈ rsb, CallAllDirect c) → (∀ c ∈ rsb, ∀ e ∈ callAddrs c, e ∈ A) →
      ∀ e : MLeak, SLeak.arch e ∈ (callSpecExec window P s rsb cc).1 → e ∈ A := by
  induction cc with
  | leaf cf =>
    intro s rsb _ _ e he
    rw [callSpecExec] at he
    exact hA e (cfExec_mem_cfAddrs cf hd s e (mem_of_arch_mem_archTrace he))
  | seq a b iha ihb =>
    intro s rsb hrd hra e he
    rw [callSpecExec] at he
    rcases List.mem_append.mp he with h | h
    · exact iha hd.1 (fun e' he' => hA e' (List.mem_append_left _ he')) s rsb hrd hra e h
    · exact ihb hd.2 (fun e' he' => hA e' (List.mem_append_right _ he')) _ rsb hrd hra e h
  | call callee cont ihcallee ihcont =>
    intro s rsb hrd hra e he
    have hcontA : ∀ e' ∈ callAddrs cont, e' ∈ A :=
      fun e' he' => hA e' (List.mem_append_right _ he')
    have hrd' : ∀ c ∈ cont :: rsb, CallAllDirect c := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hd.2
      · exact hrd c hc'
    have hra' : ∀ c ∈ cont :: rsb, ∀ e' ∈ callAddrs c, e' ∈ A := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hcontA
      · exact hra c hc'
    rw [callSpecExec] at he
    rcases List.mem_append.mp he with h | h
    · rcases List.mem_append.mp h with h' | h'
      · exact ihcallee hd.1 (fun e' he' => hA e' (List.mem_append_left _ he')) s
          (cont :: rsb) hrd' hra' e h'
      · rcases mem_of_mem_retTransient h' with hr | ⟨c, hc, hx⟩
        · exact absurd hr (by simp)
        · exact hra' c hc e
            (callExec_mem_callAddrs c (hrd' c hc) _ e (mem_of_arch_mem_archTrace hx))
    · exact ihcont hd.2 hcontA _ rsb hrd hra e h

/-! ## 9. Leakage equality under a public-driven predictor

Whether a transient window opens is itself an observation: it decides whether the
mis-speculated events and the rollback marker appear. Leakage equality across two
states therefore needs the predictor to make the same decision on both, which is the
hypothesis `RSBPubDriven`. It is the one hypothesis
`MachineConstantTime.owned_ct_control_flow` does not carry. -/

/-- The block is CT-controlled: every owned leaf is `MachineConstantTime.CFControlled`
    (straight-line leaves CT-addressed, conditional guards public). -/
def CallControlled (pub : PubPred) {w : Nat} : CallCF w → Prop
  | .leaf cf => CFControlled pub cf
  | .seq a b => CallControlled pub a ∧ CallControlled pub b
  | .call callee cont => CallControlled pub callee ∧ CallControlled pub cont

/-- A return-target predictor is public-driven when it names the same buffer entry on
    any two states that agree on the public registers. -/
def RSBPubDriven (pub : PubPred) {w : Nat} (P : RSBPredictor w) : Prop :=
  ∀ s₁ s₂ : JState w, agreePub pub s₁ s₂ → ∀ rsb : RSB w, P s₁ rsb = P s₂ rsb

/-- The always-correct predictor is public-driven. -/
theorem rsbPubDriven_neverMispredictRet (pub : PubPred) {w : Nat} :
    RSBPubDriven pub (neverMispredictRet (w := w)) := fun _ _ _ _ => rfl

/-- A public-driven predictor names the same return target on states agreeing on the
    public registers. -/
theorem mispredictTarget_pub_determined (pub : PubPred) {w : Nat} (window : Nat)
    {P : RSBPredictor w} (hP : RSBPubDriven pub P) {s₁ s₂ : JState w}
    (hag : agreePub pub s₁ s₂) (rsb : RSB w) :
    mispredictTarget window P s₁ rsb = mispredictTarget window P s₂ rsb := by
  simp only [mispredictTarget, hP s₁ s₂ hag rsb]

/-- **Architectural leakage equality for a block with calls.** A `CallControlled`
    block produces the same architectural trace from any two states agreeing on the
    public registers, and preserves that agreement on the post-states. -/
theorem callExec_pub_determined (pub : PubPred) {w : Nat} (cc : CallCF w)
    (hcc : CallControlled pub cc) :
    ∀ s₁ s₂ : JState w, agreePub pub s₁ s₂ →
      (callExec s₁ cc).1 = (callExec s₂ cc).1
        ∧ agreePub pub (callExec s₁ cc).2 (callExec s₂ cc).2 := by
  induction cc with
  | leaf cf => intro s₁ s₂ hag; exact cfExec_pub_determined pub cf hcc s₁ s₂ hag
  | seq a b iha ihb =>
    intro s₁ s₂ hag
    obtain ⟨hla, haa⟩ := iha hcc.1 s₁ s₂ hag
    obtain ⟨hlb, hab⟩ := ihb hcc.2 _ _ haa
    exact ⟨by rw [callExec, callExec, hla, hlb], by rw [callExec, callExec]; exact hab⟩
  | call callee cont ihcallee ihcont =>
    intro s₁ s₂ hag
    obtain ⟨hla, haa⟩ := ihcallee hcc.1 s₁ s₂ hag
    obtain ⟨hlb, hab⟩ := ihcont hcc.2 _ _ haa
    exact ⟨by rw [callExec, callExec, hla, hlb], by rw [callExec, callExec]; exact hab⟩

/-- A mispredicted return's contribution is the same on two states agreeing on the
    public registers, when the predictor is public-driven and every pending return
    target is CT-controlled. -/
theorem retTransient_pub_determined (pub : PubPred) {w : Nat} (window : Nat)
    {P : RSBPredictor w} (hP : RSBPubDriven pub P) {s₁ s₂ : JState w}
    (hag : agreePub pub s₁ s₂) (rsb : RSB w)
    (hrsb : ∀ c ∈ rsb, CallControlled pub c) :
    retTransient window P s₁ rsb = retTransient window P s₂ rsb := by
  have hm : mispredictTarget window P s₁ rsb = mispredictTarget window P s₂ rsb :=
    mispredictTarget_pub_determined pub window hP hag rsb
  cases hc : mispredictTarget window P s₁ rsb with
  | none =>
    have hc2 : mispredictTarget window P s₂ rsb = none := by rw [← hm]; exact hc
    rw [retTransient_of_none hc, retTransient_of_none hc2]
  | some c =>
    have hc2 : mispredictTarget window P s₂ rsb = some c := by rw [← hm]; exact hc
    have hl : (callExec s₁ c).1 = (callExec s₂ c).1 :=
      (callExec_pub_determined pub c (hrsb c (mispredictTarget_mem hc)) s₁ s₂ hag).1
    simp only [retTransient, hc, hc2, hl]

/-- **Return-misprediction leakage equality.** A `CallControlled` block, whose pending
    return targets are all `CallControlled`, produces under a public-driven
    return-target predictor the same speculative leakage trace from any two states
    agreeing on the public registers, and preserves that agreement on the
    post-states, for every speculation window.

    The architectural events close as in `MachineConstantTime.cfExec_pub_determined`.
    The transient events close because a public-driven predictor names the same
    pending return target on both runs, and that target's architectural trace is
    itself public-determined. -/
theorem callSpecExec_pub_determined (pub : PubPred) {w : Nat} (window : Nat)
    {P : RSBPredictor w} (hP : RSBPubDriven pub P) (cc : CallCF w)
    (hcc : CallControlled pub cc) :
    ∀ (s₁ s₂ : JState w) (rsb : RSB w), agreePub pub s₁ s₂ →
      (∀ c ∈ rsb, CallControlled pub c) →
      (callSpecExec window P s₁ rsb cc).1 = (callSpecExec window P s₂ rsb cc).1
        ∧ agreePub pub (callSpecExec window P s₁ rsb cc).2
            (callSpecExec window P s₂ rsb cc).2 := by
  induction cc with
  | leaf cf =>
    intro s₁ s₂ rsb hag _
    obtain ⟨hl, ha⟩ := cfExec_pub_determined pub cf hcc s₁ s₂ hag
    rw [callSpecExec, callSpecExec]
    exact ⟨by rw [hl], ha⟩
  | seq a b iha ihb =>
    intro s₁ s₂ rsb hag hrsb
    obtain ⟨hla, haa⟩ := iha hcc.1 s₁ s₂ rsb hag hrsb
    obtain ⟨hlb, hab⟩ := ihb hcc.2 _ _ rsb haa hrsb
    exact ⟨by rw [callSpecExec, callSpecExec, hla, hlb],
           by rw [callSpecExec, callSpecExec]; exact hab⟩
  | call callee cont ihcallee ihcont =>
    intro s₁ s₂ rsb hag hrsb
    have hrsb' : ∀ c ∈ cont :: rsb, CallControlled pub c := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hcc.2
      · exact hrsb c hc'
    obtain ⟨hla, haa⟩ := ihcallee hcc.1 s₁ s₂ (cont :: rsb) hag hrsb'
    obtain ⟨hlb, hab⟩ := ihcont hcc.2 _ _ rsb haa hrsb
    refine ⟨?_, by rw [callSpecExec, callSpecExec]; exact hab⟩
    rw [callSpecExec, callSpecExec, hla, hlb,
      retTransient_pub_determined pub window hP haa (cont :: rsb) hrsb']

/-- **The return-misprediction form of `owned_ct_control_flow`.** Over blocks built
    from counted-loop and public-guard-conditional owned leaves by sequencing and
    calls, a `CallControlled` block with `CallControlled` pending return targets leaks
    the same speculative trace under a public-driven return-target predictor from any
    two states agreeing on the public registers, for every speculation window. -/
theorem owned_sct_return (pub : PubPred) {w : Nat} (window : Nat)
    {P : RSBPredictor w} (hP : RSBPubDriven pub P) (cc : CallCF w)
    (hcc : CallControlled pub cc) (rsb : RSB w)
    (hrsb : ∀ c ∈ rsb, CallControlled pub c) (s₁ s₂ : JState w)
    (hag : agreePub pub s₁ s₂) :
    (callSpecExec window P s₁ rsb cc).1 = (callSpecExec window P s₂ rsb cc).1 :=
  (callSpecExec_pub_determined pub window hP cc hcc s₁ s₂ rsb hag hrsb).1

/-! ## 10. A secret-driven return predictor separates public-equivalent states

The transient window is an observation, so `RSBPubDriven` cannot be dropped. The
block below is a nested call, so at the inner return the buffer holds two pending
targets and index `1` is a wrong but present target. The block is both
`CallControlled` and `CallAllDirect`, and a predictor reading the secret register
`sec` gives two public-equivalent states different speculative traces. -/

/-- A predictor that names the second pending return target exactly when the secret
    register `sec` is nonzero. -/
def secretRetPredictor : RSBPredictor 64 :=
  fun s _ => if s.get "sec" = 0 then none else some 1

/-- The inner callee: a leaf that touches no memory. -/
def retDemoCallee : OwnedCF 64 := .straight []

/-- The inner call's continuation: a leaf that touches no memory. -/
def retDemoCont1 : OwnedCF 64 := .straight []

/-- The outer call's continuation: a store through the public pointer `op`. -/
def retDemoCont0 : OwnedCF 64 := .straight [ .storeMem "op" 0 (.reg "t") ]

/-- A nested call: the inner return's buffer holds the inner continuation at index
    `0` and the outer continuation at index `1`. -/
def retDemo : CallCF 64 :=
  .call (.call (.leaf retDemoCallee) (.leaf retDemoCont1)) (.leaf retDemoCont0)

/-- Every leaf of `retDemo` addresses memory through a base register and a
    compile-time displacement. -/
theorem retDemo_allDirect : CallAllDirect retDemo := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi; simp [retDemoCallee] at hi
  · intro i hi; simp [retDemoCont1] at hi
  · intro i hi
    simp only [retDemoCont0, List.mem_singleton] at hi
    subst hi
    exact trivial

/-- Every leaf of `retDemo` is CT-controlled w.r.t. `MachineConstantTime.cfPub`: the
    address base `op` is public and the leaves write no public register. -/
theorem retDemo_callControlled : CallControlled cfPub retDemo := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i hi; simp [retDemoCallee] at hi
  · intro i hi; simp [retDemoCont1] at hi
  · intro i hi
    simp only [retDemoCont0, List.mem_singleton] at hi
    subst hi
    exact ⟨by simp [idxReg], by simp [dstRegs]⟩

/-- The speculative trace from a state whose secret register is zero: the predictor
    names the correct return target at both returns, so only the architectural store
    is observed. -/
theorem retDemo_trace_zeroState :
    (callSpecExec 1 secretRetPredictor zeroState [] retDemo).1
      = [SLeak.arch (MLeak.mem "op" 0)] := by
  simp [retDemo, retDemoCallee, retDemoCont1, retDemoCont0, callSpecExec,
    retTransient, mispredictTarget, secretRetPredictor, callExec, cfExec, instrLeak,
    zeroState, JState.get, archTrace]

/-- The speculative trace from a state whose secret register is nonzero: at the inner
    return the predictor names the outer continuation, whose store is observed
    transiently before the rollback marker. -/
theorem retDemo_trace_secretState :
    (callSpecExec 1 secretRetPredictor secretState [] retDemo).1
      = [SLeak.arch (MLeak.mem "op" 0), SLeak.rollback, SLeak.arch (MLeak.mem "op" 0)] := by
  simp [retDemo, retDemoCallee, retDemoCont1, retDemoCont0, callSpecExec,
    retTransient, mispredictTarget, secretRetPredictor, callExec, cfExec, instrLeak,
    secretState, JState.get, archTrace]

/-- **A secret-driven return predictor is not covered.** On a block that is both
    `CallControlled` and `CallAllDirect`, a predictor reading a secret register names
    a wrong pending return target from one of two public-equivalent states and the
    correct one from the other, so the speculative traces differ. `RSBPubDriven` in
    `callSpecExec_pub_determined` is therefore not removable, and it is the hypothesis
    the architectural result `MachineConstantTime.owned_ct_control_flow` does not
    carry. -/
theorem secretDrivenRetPredictor_leaks :
    (callSpecExec 1 secretRetPredictor zeroState [] retDemo).1
      ≠ (callSpecExec 1 secretRetPredictor secretState [] retDemo).1 := by
  rw [retDemo_trace_zeroState, retDemo_trace_secretState]
  decide

/-! ## 11. The deployed export

`SpeculativeCTPreservation.gatherJBlock6_no_control_transfer` rejects every
control-transfer instruction, the call among them, so the body the deployed export
gathers carries no `Lcall` and the gathered block is a `CallCF.leaf` with no return
site. Its speculative trace is therefore state-independent outright, for every
return-target predictor, every window and every buffer. The `CallCF` layer above it
is the model of the emitted call structure; nothing here maps an `Lcmd` carrying
`Lcall` to a `CallCF`. -/

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (gatherJBlock6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation (lcmdDirect)

/-- The gathered block, read as a `CallCF`, is call-free. -/
theorem gathered_callFree (g : List (JInstr 64)) :
    CallFree (CallCF.leaf (OwnedCF.straight g)) := trivial

/-- A straight-line leaf in the index-free fragment has a speculative trace fixed by
    the program text, for every return-target predictor, window and buffer. -/
theorem callSpecExec_straight_isDirect {w : Nat} (window : Nat) (P : RSBPredictor w)
    {body : List (JInstr w)} (h : ∀ i ∈ body, IsDirect i) (rsb : RSB w)
    (s₁ s₂ : JState w) :
    (callSpecExec window P s₁ rsb (.leaf (.straight body))).1
      = (callSpecExec window P s₂ rsb (.leaf (.straight body))).1 := by
  rw [callSpecExec, callSpecExec, cfExec, cfExec,
    blockLeak_state_independent body h s₁ s₂]

/-- The `allDirect` form of `callSpecExec_straight_isDirect`. -/
theorem callSpecExec_straight_allDirect (window : Nat) (P : RSBPredictor 64)
    {body : List (JInstr 64)} (h : allDirect body = true) (rsb : RSB 64)
    (s₁ s₂ : JState 64) :
    (callSpecExec window P s₁ rsb (.leaf (.straight body))).1
      = (callSpecExec window P s₂ rsb (.leaf (.straight body))).1 :=
  callSpecExec_straight_isDirect window P
    (ConstantTimeCoverage.allDirect_mem_isDirect body h) rsb s₁ s₂

/-- **The deployed export's gathered block under return misprediction.** When the
    virtual body a `Com` lowers to uses no register-indexed operand, the block the
    deployed allocator emits has the same speculative leakage trace from any two
    machine states, for every return-target predictor, every speculation window and
    every return-stack buffer.

    Covered: the leaf the export gathers, which carries no call and so no return
    site. Not covered: a body whose `Lcmd` carries an `Lcall` — that body does not
    gather, and no lowering from such an `Lcmd` to a `CallCF` is established here;
    and a kernel using register-indexed addressing, which fails the `lcmdDirect`
    hypothesis. -/
theorem toLprogPhysAbi_gather_callSpec_state_independent {Γ : Ctxt jasminDialect}
    {t : JasminTy} (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle) (immSlotMap : ImmSlotMap) (inLoadMap : InLoadMap)
    (outStoreMap : OutStoreMap) (abiArgs : List String) (abiTyin : List Nat)
    (residence : Option (Array Nat)) (abiW : Nat) (forceLivePin : Bool)
    (hd : lcmdDirect (comToLfundef com immSlotMap).lfd_body = true)
    {f : String × Lfundef} {g : List (JInstr 64)}
    (hf : f ∈ (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap outStoreMap
      abiArgs abiTyin residence abiW forceLivePin).lp_funcs)
    (hg : gatherJBlock6 f.2.lfd_body = some g)
    (window : Nat) (P : RSBPredictor 64) (rsb : RSB 64) (s₁ s₂ : JState 64) :
    (callSpecExec window P s₁ rsb (.leaf (.straight g))).1
      = (callSpecExec window P s₂ rsb (.leaf (.straight g))).1 :=
  callSpecExec_straight_allDirect window P
    (AllocCTPreservation.toLprogPhysAbi_gather_allDirect com fname shiftImm immSlotMap
      inLoadMap outStoreMap abiArgs abiTyin residence abiW forceLivePin hd hf hg) rsb s₁ s₂

/-- An owned block read as a `CallCF` leaf is index-free exactly when the owned block
    is. Composed with
    `SpeculativeCTControlFlow.toLprogPhysAbi_gather_cfAllDirect` this supplies the
    `CallAllDirect` hypothesis of `callSpecExec_arch_mem` for the gathered block of
    the deployed export. -/
theorem callAllDirect_leaf {w : Nat} (cf : OwnedCF w) :
    CallAllDirect (CallCF.leaf cf) ↔ CFAllDirect cf := Iff.rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTReturn
