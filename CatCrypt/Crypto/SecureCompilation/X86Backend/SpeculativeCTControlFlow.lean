/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation

/-!
# Branch-misprediction leakage over the structured owned control-flow block

`MachineConstantTime.cfExec` is the architectural leakage semantics of the
structured owned block `OwnedCF`: straight-line `List (JInstr w)` leaves, sequential
composition, a counted loop with a compile-time trip count, and a conditional on a
register guard. This module adds a **branch predictor** to that semantics: at a
conditional the predictor may steer execution down the arm the guard does not
select, a bounded number of that arm's leakage events are emitted, and a rollback
marker closes the transient window; at a loop exit the predictor may steer one
further transient iteration of the body.

`SpeculativeCTMachine` is the store-bypass (Spectre-v4) counterpart at the
straight-line `List (JInstr w)` level. This module is the branch-misprediction
(Spectre-v1 / PHT) counterpart at the `OwnedCF` level, and follows the same idiom: a
predictor that reads the whole machine state, a speculation window, and projection
lemmas back to the architectural trace.

## The model

`CFPredictor w` is an arbitrary function of the whole machine state and the syntactic
node, so a predictor may read secret registers. `cfSpecExec window P s cf` is the
speculative leakage trace and post-state. Its observation alphabet `SLeak` is
`MachineConstantTime.MLeak` extended with a `rollback` marker, so the architectural
events are carried unchanged and only the transient boundary is new. The transient
contribution at a site is the mispredicted continuation's own speculative trace
truncated to `window`, followed by `rollback`; the architecturally-taken
continuation then runs from the unchanged state, which is the rollback.

## The two results

`cfSpecExec_arch_mem_cfAddrs` is predictor-free: on the index-free fragment
(`CFAllDirect` — every instruction of every leaf is `MachineConstantTime.IsDirect`)
every memory event of the speculative trace names an address that occurs in
`cfAddrs cf`, the list of `(base, displacement)` pairs read off the program text.
A mispredicted path therefore cannot compute an address the program does not
already contain, for every predictor, every window and every state.

`cfSpecExec_pub_determined` is the leakage-equality result: a `CFControlled` block
under a `PubDriven` predictor has the same speculative trace from any two states
agreeing on the public registers. `PubDriven` is the hypothesis the architectural
result `MachineConstantTime.owned_ct_control_flow` does not carry, and
`secretDrivenPredictor_leaks` shows it cannot be dropped: a predictor that reads a
secret register separates two public-equivalent states on a block that is both
`CFControlled` and `CFAllDirect`, because whether a transient window opens is itself
an observation.

## Scope

The results hold on the index-free fragment, where a memory operand is a base
register plus a compile-time displacement. Kernels routed through `memrefGetDyn` or
`stackLoad` — the SDitH and UOV array kernels among them — use register-indexed
addressing and lie outside it; `cfSpecExec_arch_mem_cfAddrs` says nothing about
them, and for them a transient path can compute an address from a register value.

`OwnedCF` is a model of the emitted control-flow shapes, not the output of a
lowering: no theorem maps an `Lcmd` carrying `Lcond`/`Lgoto` to an `OwnedCF`. The
composition `toLprogPhysAbi_gather_cfSpec_state_independent` lands on the
straight-line block the deployed export gathers, which is a `OwnedCF.straight` leaf
and so contains no branch site.

Not modelled: store-to-load forwarding (`SpeculativeCTMachine` covers it), indirect
branch and return misprediction, cache-line granularity, port contention, and
transient instructions fetched from outside the block.

## References

* Cauligi, Disselkoen, von Gleissenthall, Tullsen, Stefan, Rezk, Barthe,
  "Constant-Time Foundations for the New Spectre Era", PLDI 2020.
* Vassena, Disselkoen, von Gleissenthall, Cauligi, Kıcı, Jhala, Tullsen, Stefan,
  "Automatically Eliminating Speculative Leaks with Blade", POPL 2021.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTControlFlow

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime

/-! ## 1. The speculative observation alphabet -/

/-- A speculative leakage event: an architectural machine event, or the marker that
    closes a mis-speculated window. -/
inductive SLeak where
  /-- An architectural machine leakage event. -/
  | arch (e : MLeak)
  /-- The end of a mis-speculated window. -/
  | rollback
  deriving DecidableEq, Repr

/-- The architectural trace read as a speculative trace. -/
def archTrace (l : List MLeak) : List SLeak := l.map SLeak.arch

@[simp] theorem archTrace_nil : archTrace [] = [] := rfl

@[simp] theorem archTrace_cons (e : MLeak) (l : List MLeak) :
    archTrace (e :: l) = SLeak.arch e :: archTrace l := rfl

@[simp] theorem archTrace_append (a b : List MLeak) :
    archTrace (a ++ b) = archTrace a ++ archTrace b := List.map_append ..

theorem mem_of_arch_mem_archTrace {e : MLeak} {l : List MLeak}
    (h : SLeak.arch e ∈ archTrace l) : e ∈ l := by
  rw [archTrace, List.mem_map] at h
  obtain ⟨e', he', heq⟩ := h
  cases heq
  exact he'

/-! ## 2. The branch predictor and the transient window -/

/-- A branch predictor: at a speculation site, given the whole machine state and the
    syntactic node, does the prediction miss? An arbitrary function of the state, so
    a predictor may read secret registers. -/
abbrev CFPredictor (w : Nat) := JState w → OwnedCF w → Bool

/-- The predictor that never misses. -/
def neverMispredict {w : Nat} : CFPredictor w := fun _ _ => false

/-- Does a transient window open at this site: the speculation window admits one and
    the predictor misses. -/
def mispredicts {w : Nat} (window : Nat) (P : CFPredictor w) (s : JState w)
    (cf : OwnedCF w) : Bool := 0 < window && P s cf

@[simp] theorem mispredicts_of_window_zero {w : Nat} (P : CFPredictor w)
    (s : JState w) (cf : OwnedCF w) : mispredicts 0 P s cf = false := by
  simp [mispredicts]

@[simp] theorem mispredicts_neverMispredict {w : Nat} (window : Nat) (s : JState w)
    (cf : OwnedCF w) : mispredicts window neverMispredict s cf = false := by
  simp [mispredicts, neverMispredict]

/-- The leakage a transient window contributes: the mis-speculated continuation's
    trace truncated to the window, closed by a rollback marker; nothing when no
    window opens. -/
def transient (window : Nat) (fire : Bool) (t : List SLeak) : List SLeak :=
  if fire then t.take window ++ [SLeak.rollback] else []

@[simp] theorem transient_false (window : Nat) (t : List SLeak) :
    transient window false t = [] := rfl

theorem mem_of_mem_transient {window : Nat} {fire : Bool} {t : List SLeak}
    {x : SLeak} (h : x ∈ transient window fire t) : x ∈ t ∨ x = SLeak.rollback := by
  unfold transient at h
  cases fire with
  | false => simp at h
  | true =>
    rcases List.mem_append.mp h with h' | h'
    · exact Or.inl (List.mem_of_mem_take h')
    · exact Or.inr (List.mem_singleton.mp h')

/-! ## 3. The speculative semantics -/

mutual

/-- `cfSpecExec window P s cf = (leak, s')`: the speculative leakage trace of the
    structured block `cf` from state `s` under predictor `P` and speculation window
    `window`, together with the architectural post-state.

    A straight-line leaf has no speculation site and contributes its architectural
    trace. A conditional emits the branch decision, then — when a window opens — the
    trace of the arm the guard does not select, truncated to `window` and closed by a
    rollback marker, and then the selected arm from the unchanged state. A counted
    loop runs its iterations and may, on the exit prediction, contribute one further
    transient iteration of the body from the loop's post-state. -/
def cfSpecExec {w : Nat} (window : Nat) (P : CFPredictor w) (s : JState w)
    (cf : OwnedCF w) : List SLeak × JState w :=
  match cf with
  | .straight body => (archTrace (blockLeak s body), runBlock s body)
  | .seq a b =>
      ((cfSpecExec window P s a).1
          ++ (cfSpecExec window P (cfSpecExec window P s a).2 b).1,
       (cfSpecExec window P (cfSpecExec window P s a).2 b).2)
  | .loop n body =>
      ((cfSpecLoop window P n body s).1
          ++ transient window (mispredicts window P (cfSpecLoop window P n body s).2
                (.loop n body))
              (cfSpecExec window P (cfSpecLoop window P n body s).2 body).1,
       (cfSpecLoop window P n body s).2)
  | .ifPub guard thenB elseB =>
      if s.get guard = 0 then
        (SLeak.arch MLeak.branch
            :: (transient window (mispredicts window P s (.ifPub guard thenB elseB))
                  (cfSpecExec window P s thenB).1
                ++ (cfSpecExec window P s elseB).1),
         (cfSpecExec window P s elseB).2)
      else
        (SLeak.arch MLeak.branch
            :: (transient window (mispredicts window P s (.ifPub guard thenB elseB))
                  (cfSpecExec window P s elseB).1
                ++ (cfSpecExec window P s thenB).1),
         (cfSpecExec window P s thenB).2)
  termination_by 2 * sizeOf cf
  decreasing_by all_goals (simp_wf <;> omega)

/-- `cfSpecLoop window P n body s`: the speculative trace of `n` iterations of
    `body`, concatenated, with the state threaded through each iteration. The trip
    count is the program's literal, so the number of iterations is fixed by the
    program text. -/
def cfSpecLoop {w : Nat} (window : Nat) (P : CFPredictor w) (n : Nat)
    (body : OwnedCF w) (s : JState w) : List SLeak × JState w :=
  match n with
  | 0 => ([], s)
  | n + 1 =>
      ((cfSpecExec window P s body).1
          ++ (cfSpecLoop window P n body (cfSpecExec window P s body).2).1,
       (cfSpecLoop window P n body (cfSpecExec window P s body).2).2)
  termination_by 2 * sizeOf body + 2 * n + 1
  decreasing_by all_goals (simp_wf <;> omega)

end

/-! ## 4. The architectural projection

With no transient window the speculative trace is the architectural trace of
`MachineConstantTime.cfExec`, and the post-states coincide. This holds when the
window is closed and under the never-miss predictor. -/

/-- The loop half of the projection, for a body whose projection is known. -/
theorem cfSpecLoop_of_no_mispredict {w : Nat} (window : Nat) (P : CFPredictor w)
    (body : OwnedCF w)
    (ih : ∀ s : JState w,
      cfSpecExec window P s body = (archTrace (cfExec s body).1, (cfExec s body).2)) :
    ∀ (n : Nat) (s : JState w),
      cfSpecLoop window P n body s = (archTrace (cfLoop n body s).1, (cfLoop n body s).2) := by
  intro n
  induction n with
  | zero => intro s; simp [cfSpecLoop, cfLoop]
  | succ m ihm =>
    intro s
    simp only [cfSpecLoop, cfLoop, ih s, ihm (cfExec s body).2, archTrace_append]

/-- **The architectural projection.** A predictor that opens no transient window
    reproduces the architectural leakage trace and post-state of `cfExec`. -/
theorem cfSpecExec_of_no_mispredict {w : Nat} (window : Nat) (P : CFPredictor w)
    (hno : ∀ (s : JState w) (cf : OwnedCF w), mispredicts window P s cf = false)
    (cf : OwnedCF w) :
    ∀ s : JState w,
      cfSpecExec window P s cf = (archTrace (cfExec s cf).1, (cfExec s cf).2) := by
  induction cf with
  | straight body => intro s; simp [cfSpecExec, cfExec]
  | seq a b iha ihb =>
    intro s
    simp only [cfSpecExec, cfExec, iha s, ihb (cfExec s a).2, archTrace_append]
  | loop n body ihbody =>
    intro s
    simp only [cfSpecExec, cfExec, hno, transient_false, List.append_nil,
      cfSpecLoop_of_no_mispredict window P body ihbody n s]
  | ifPub guard thenB elseB iht ihe =>
    intro s
    by_cases hz : s.get guard = 0
    · simp only [cfSpecExec, cfExec, if_pos hz, hno, transient_false, List.nil_append,
        iht s, ihe s, archTrace_cons]
    · simp only [cfSpecExec, cfExec, if_neg hz, hno, transient_false, List.nil_append,
        iht s, ihe s, archTrace_cons]

/-- With the speculation window closed the speculative trace is the architectural
    trace, for every predictor. -/
theorem cfSpecExec_of_window_zero {w : Nat} (P : CFPredictor w) (cf : OwnedCF w)
    (s : JState w) :
    cfSpecExec 0 P s cf = (archTrace (cfExec s cf).1, (cfExec s cf).2) :=
  cfSpecExec_of_no_mispredict 0 P (fun _ _ => mispredicts_of_window_zero P _ _) cf s

/-- Under the never-miss predictor the speculative trace is the architectural
    trace, for every window. -/
theorem cfSpecExec_neverMispredict {w : Nat} (window : Nat) (cf : OwnedCF w)
    (s : JState w) :
    cfSpecExec window neverMispredict s cf
      = (archTrace (cfExec s cf).1, (cfExec s cf).2) :=
  cfSpecExec_of_no_mispredict window neverMispredict
    (fun _ _ => mispredicts_neverMispredict window _ _) cf s

/-! ## 5. The index-free fragment and its compile-time address set -/

/-- Every instruction of every straight-line leaf of `cf` addresses memory through a
    base register and a compile-time-constant displacement. -/
def CFAllDirect {w : Nat} : OwnedCF w → Prop
  | .straight body => ∀ i ∈ body, IsDirect i
  | .seq a b => CFAllDirect a ∧ CFAllDirect b
  | .loop _ body => CFAllDirect body
  | .ifPub _ thenB elseB => CFAllDirect thenB ∧ CFAllDirect elseB

/-- The leakage event an instruction emits when its addressing is direct: the
    memory accesses at its base register and compile-time displacement, or none;
    `addToMem` reads and writes its cell, two accesses. -/
def instrAddrs {w : Nat} : JInstr w → List MLeak
  | .loadMem _ base off => [.mem base off]
  | .storeMem base off _ => [.mem base off]
  | .mulxMem _ _ _ base off => [.mem base off]
  | .addMem _ base off | .adcxMem _ base off | .adoxMem _ base off
  | .imulMem _ base off | .imulriMem _ base off _ | .cmpMem _ base off => [.mem base off]
  | .cmovccMem _ _ base off => [.mem base off]
  | .addToMem base off _ => [.mem base off, .mem base off]
  | _ => []

/-- A direct instruction's leak is its compile-time address event. -/
theorem instrLeak_eq_instrAddrs {w : Nat} (s : JState w) (i : JInstr w)
    (h : IsDirect i) : instrLeak s i = instrAddrs i := by
  cases i <;> first | rfl | (simp [IsDirect] at h)

/-- On the index-free fragment the architectural leakage trace of a straight-line
    leaf is the list of address events read off the program text. -/
theorem blockLeak_eq_flatMap_instrAddrs {w : Nat} (body : List (JInstr w))
    (h : ∀ i ∈ body, IsDirect i) (s : JState w) :
    blockLeak s body = body.flatMap instrAddrs := by
  induction body generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [blockLeak_cons, List.flatMap_cons,
      instrLeak_eq_instrAddrs s i (h i (List.mem_cons_self ..)),
      ih (fun j hj => h j (List.mem_cons_of_mem i hj)) (evalInstr s i)]

/-- The address events the program text of a structured block contains, together
    with the branch decision of each conditional. -/
def cfAddrs {w : Nat} : OwnedCF w → List MLeak
  | .straight body => body.flatMap instrAddrs
  | .seq a b => cfAddrs a ++ cfAddrs b
  | .loop _ body => cfAddrs body
  | .ifPub _ thenB elseB => MLeak.branch :: (cfAddrs thenB ++ cfAddrs elseB)

/-! ## 6. A mispredicted path emits only program-text addresses

The predictor decides which instructions run, not what any instruction's address
depends on. On the index-free fragment every memory operand is a base register plus
a compile-time displacement, and the instructions available to a transient path are
those of the program, so every memory event of the speculative trace names an
address already present in `cfAddrs`. This holds for every predictor, every window
and every state. -/

/-- The loop half of the containment. -/
theorem cfSpecLoop_arch_mem_cfAddrs {w : Nat} (window : Nat) (P : CFPredictor w)
    (body : OwnedCF w)
    (ih : ∀ (s : JState w) (e : MLeak),
      SLeak.arch e ∈ (cfSpecExec window P s body).1 → e ∈ cfAddrs body) :
    ∀ (n : Nat) (s : JState w) (e : MLeak),
      SLeak.arch e ∈ (cfSpecLoop window P n body s).1 → e ∈ cfAddrs body := by
  intro n
  induction n with
  | zero => intro s e he; simp [cfSpecLoop] at he
  | succ m ihm =>
    intro s e he
    rw [cfSpecLoop] at he
    rcases List.mem_append.mp he with h | h
    · exact ih s e h
    · exact ihm _ e h

/-- **A speculative memory event names a program-text address.** On the index-free
    fragment every memory access the speculative trace records — architectural or
    transient — is an access at a base register and compile-time displacement that
    occurs in the program. No predictor, window or state produces an address outside
    `cfAddrs cf`. -/
theorem cfSpecExec_arch_mem_cfAddrs {w : Nat} (window : Nat) (P : CFPredictor w)
    (cf : OwnedCF w) (hd : CFAllDirect cf) :
    ∀ (s : JState w) (e : MLeak),
      SLeak.arch e ∈ (cfSpecExec window P s cf).1 → e ∈ cfAddrs cf := by
  induction cf with
  | straight body =>
    intro s e he
    rw [cfSpecExec] at he
    have := mem_of_arch_mem_archTrace he
    rwa [blockLeak_eq_flatMap_instrAddrs body hd s] at this
  | seq a b iha ihb =>
    intro s e he
    rw [cfSpecExec] at he
    rcases List.mem_append.mp he with h | h
    · exact List.mem_append_left _ (iha hd.1 s e h)
    · exact List.mem_append_right _ (ihb hd.2 _ e h)
  | loop n body ihbody =>
    intro s e he
    rw [cfSpecExec] at he
    rcases List.mem_append.mp he with h | h
    · exact cfSpecLoop_arch_mem_cfAddrs window P body (fun s' e' => ihbody hd s' e') n s e h
    · rcases mem_of_mem_transient h with h' | h'
      · exact ihbody hd _ e h'
      · exact absurd h' (by simp)
  | ifPub guard thenB elseB iht ihe =>
    intro s e he
    by_cases hz : s.get guard = 0
    · rw [cfSpecExec, if_pos hz] at he
      rcases List.mem_cons.mp he with h | h
      · cases h; exact List.mem_cons_self ..
      · rcases List.mem_append.mp h with h' | h'
        · rcases mem_of_mem_transient h' with h'' | h''
          · exact List.mem_cons_of_mem _ (List.mem_append_left _ (iht hd.1 s e h''))
          · exact absurd h'' (by simp)
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihe hd.2 s e h'))
    · rw [cfSpecExec, if_neg hz] at he
      rcases List.mem_cons.mp he with h | h
      · cases h; exact List.mem_cons_self ..
      · rcases List.mem_append.mp h with h' | h'
        · rcases mem_of_mem_transient h' with h'' | h''
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihe hd.2 s e h''))
          · exact absurd h'' (by simp)
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ (iht hd.1 s e h'))

/-- The memory form of the containment: a speculative access at `base + off` is an
    access the program text contains. -/
theorem cfSpecExec_mem_addr_in_program {w : Nat} (window : Nat) (P : CFPredictor w)
    (cf : OwnedCF w) (hd : CFAllDirect cf) (s : JState w) (base : String) (off : Int)
    (h : SLeak.arch (MLeak.mem base off) ∈ (cfSpecExec window P s cf).1) :
    MLeak.mem base off ∈ cfAddrs cf :=
  cfSpecExec_arch_mem_cfAddrs window P cf hd s _ h

/-! ## 7. Leakage equality under a public-driven predictor

Whether a transient window opens is itself an observation: it decides whether the
mis-speculated events and the rollback marker appear. Leakage equality across two
states therefore needs the predictor to make the same decision on both, which is the
hypothesis `PubDriven`. It is the one hypothesis
`MachineConstantTime.owned_ct_control_flow` does not carry. -/

/-- A predictor is public-driven when it makes the same decision on any two states
    that agree on the public registers. -/
def PubDriven (pub : PubPred) {w : Nat} (P : CFPredictor w) : Prop :=
  ∀ s₁ s₂ : JState w, agreePub pub s₁ s₂ → ∀ cf : OwnedCF w, P s₁ cf = P s₂ cf

/-- The never-miss predictor is public-driven. -/
theorem pubDriven_neverMispredict (pub : PubPred) {w : Nat} :
    PubDriven pub (neverMispredict (w := w)) := fun _ _ _ _ => rfl

/-- A public-driven predictor takes the same transient decision on states agreeing
    on the public registers. -/
theorem mispredicts_pub_determined (pub : PubPred) {w : Nat} (window : Nat)
    {P : CFPredictor w} (hP : PubDriven pub P) {s₁ s₂ : JState w}
    (hag : agreePub pub s₁ s₂) (cf : OwnedCF w) :
    mispredicts window P s₁ cf = mispredicts window P s₂ cf := by
  simp only [mispredicts, hP s₁ s₂ hag cf]

/-- The loop half of the leakage-equality result. -/
theorem cfSpecLoop_pub_determined (pub : PubPred) {w : Nat} (window : Nat)
    (P : CFPredictor w) (body : OwnedCF w)
    (ih : ∀ s₁ s₂ : JState w, agreePub pub s₁ s₂ →
      (cfSpecExec window P s₁ body).1 = (cfSpecExec window P s₂ body).1
        ∧ agreePub pub (cfSpecExec window P s₁ body).2 (cfSpecExec window P s₂ body).2) :
    ∀ (n : Nat) (s₁ s₂ : JState w), agreePub pub s₁ s₂ →
      (cfSpecLoop window P n body s₁).1 = (cfSpecLoop window P n body s₂).1
        ∧ agreePub pub (cfSpecLoop window P n body s₁).2 (cfSpecLoop window P n body s₂).2 := by
  intro n
  induction n with
  | zero => intro s₁ s₂ hag; exact ⟨by simp [cfSpecLoop], by simpa [cfSpecLoop] using hag⟩
  | succ m ihm =>
    intro s₁ s₂ hag
    obtain ⟨hl, ha⟩ := ih s₁ s₂ hag
    obtain ⟨hl', ha'⟩ := ihm (cfSpecExec window P s₁ body).2 (cfSpecExec window P s₂ body).2 ha
    exact ⟨by rw [cfSpecLoop, cfSpecLoop, hl, hl'], by rw [cfSpecLoop, cfSpecLoop]; exact ha'⟩

/-- **Branch-misprediction leakage equality over the structured owned block.** A
    `CFControlled` block under a public-driven predictor produces the same
    speculative leakage trace from any two states agreeing on the public registers,
    and preserves that agreement on the post-states, for every speculation window.

    The architectural events close exactly as in
    `MachineConstantTime.cfExec_pub_determined`: a public guard makes both runs take
    the same arm, and a counted loop runs the same number of iterations. The
    transient events close because a public-driven predictor opens a window on both
    runs or on neither, and the mis-speculated arm's trace is itself covered by the
    induction hypothesis at the same pair of states. -/
theorem cfSpecExec_pub_determined (pub : PubPred) {w : Nat} (window : Nat)
    {P : CFPredictor w} (hP : PubDriven pub P) (cf : OwnedCF w)
    (hcf : CFControlled pub cf) :
    ∀ s₁ s₂ : JState w, agreePub pub s₁ s₂ →
      (cfSpecExec window P s₁ cf).1 = (cfSpecExec window P s₂ cf).1
        ∧ agreePub pub (cfSpecExec window P s₁ cf).2 (cfSpecExec window P s₂ cf).2 := by
  induction cf with
  | straight body =>
    intro s₁ s₂ hag
    rw [cfSpecExec, cfSpecExec]
    exact ⟨by rw [blockLeak_pub_determined pub body hcf s₁ s₂ hag],
           runBlock_agreePub_preserved pub body hcf s₁ s₂ hag⟩
  | seq a b iha ihb =>
    intro s₁ s₂ hag
    obtain ⟨hla, haa⟩ := iha hcf.1 s₁ s₂ hag
    obtain ⟨hlb, hab⟩ := ihb hcf.2 _ _ haa
    exact ⟨by rw [cfSpecExec, cfSpecExec, hla, hlb], by rw [cfSpecExec, cfSpecExec]; exact hab⟩
  | loop n body ihbody =>
    intro s₁ s₂ hag
    have hcb : CFControlled pub body := hcf
    obtain ⟨hl, ha⟩ := cfSpecLoop_pub_determined pub window P body (ihbody hcb) n s₁ s₂ hag
    obtain ⟨hlt, -⟩ := ihbody hcb _ _ ha
    refine ⟨?_, by rw [cfSpecExec, cfSpecExec]; exact ha⟩
    rw [cfSpecExec, cfSpecExec, hl, hlt,
      mispredicts_pub_determined pub window hP ha (.loop n body)]
  | ifPub guard thenB elseB iht ihe =>
    intro s₁ s₂ hag
    obtain ⟨hg, hct, hce⟩ := hcf
    have hgeq : s₁.get guard = s₂.get guard := hag guard hg
    obtain ⟨hlt, hat⟩ := iht hct s₁ s₂ hag
    obtain ⟨hle, hae⟩ := ihe hce s₁ s₂ hag
    have hm := mispredicts_pub_determined pub window hP hag (.ifPub guard thenB elseB)
    by_cases hz : s₁.get guard = 0
    · have hz2 : s₂.get guard = 0 := by rw [← hgeq]; exact hz
      refine ⟨?_, ?_⟩
      · rw [cfSpecExec, cfSpecExec, if_pos hz, if_pos hz2, hlt, hle, hm]
      · rw [cfSpecExec, cfSpecExec, if_pos hz, if_pos hz2]; exact hae
    · have hz2 : ¬ s₂.get guard = 0 := by rw [← hgeq]; exact hz
      refine ⟨?_, ?_⟩
      · rw [cfSpecExec, cfSpecExec, if_neg hz, if_neg hz2, hlt, hle, hm]
      · rw [cfSpecExec, cfSpecExec, if_neg hz, if_neg hz2]; exact hat

/-- **The speculative form of `owned_ct_control_flow`.** Over the counted-loop and
    public-guard-conditional fragment, a `CFControlled` block under a public-driven
    predictor leaks the same speculative trace from any two states agreeing on the
    public registers, for every speculation window. -/
theorem owned_sct_control_flow (pub : PubPred) {w : Nat} (window : Nat)
    {P : CFPredictor w} (hP : PubDriven pub P) (cf : OwnedCF w)
    (hcf : CFControlled pub cf) (s₁ s₂ : JState w) (hag : agreePub pub s₁ s₂) :
    (cfSpecExec window P s₁ cf).1 = (cfSpecExec window P s₂ cf).1 :=
  (cfSpecExec_pub_determined pub window hP cf hcf s₁ s₂ hag).1

/-! ## 8. A secret-driven predictor separates public-equivalent states

The transient window is an observation, so `PubDriven` cannot be dropped. The block
below is both `CFControlled` and `CFAllDirect`, and a predictor reading the secret
register `sec` gives two public-equivalent states different speculative traces: one
opens a window down the untaken arm and the other does not. -/

/-- A predictor that misses exactly when the secret register `sec` is nonzero. -/
def secretPredictor : CFPredictor 64 := fun s _ => s.get "sec" != 0

/-- Both arms of `MachineConstantTime.cfIfDemo` address memory through a base
    register and a compile-time displacement. -/
theorem cfIfDemo_allDirect : CFAllDirect cfIfDemo := by
  constructor
  · intro i hi
    simp only [List.mem_singleton] at hi; subst hi; exact trivial
  · intro i hi
    simp only [List.mem_singleton] at hi; subst hi; exact trivial

/-- The zero register file. -/
def zeroState : JState 64 := { regs := fun _ => 0 }

/-- The register file holding `1` in the secret register `sec`. -/
def secretState : JState 64 := { regs := fun r => if r = "sec" then 1 else 0 }

/-- The two states agree on the public registers of `MachineConstantTime.cfPub`. -/
theorem zeroState_agreePub_secretState : agreePub cfPub zeroState secretState := by
  intro r hr
  simp only [cfPub, Bool.or_eq_true, decide_eq_true_eq] at hr
  rcases hr with (rfl | rfl) | rfl <;> rfl

/-- **A secret-driven predictor is not covered.** On a block that is both
    `CFControlled` and `CFAllDirect`, a predictor reading a secret register opens a
    transient window from one of two public-equivalent states and not from the other,
    so the speculative traces differ. `PubDriven` in `cfSpecExec_pub_determined` is
    therefore not removable, and it is the hypothesis the architectural result
    `MachineConstantTime.owned_ct_control_flow` does not carry. -/
theorem secretDrivenPredictor_leaks :
    (cfSpecExec 1 secretPredictor zeroState cfIfDemo).1
      ≠ (cfSpecExec 1 secretPredictor secretState cfIfDemo).1 := by
  simp only [cfIfDemo, cfSpecExec, mispredicts, secretPredictor, transient,
    zeroState, secretState, JState.get, archTrace, blockLeak_cons, blockLeak_nil,
    instrLeak]
  decide

/-! ## 9. The deployed export

`gatherJBlock6` rejects every control-transfer instruction
(`SpeculativeCTPreservation.gatherJBlock6_no_control_transfer`), so the block the
deployed export gathers is a straight-line `OwnedCF.straight` leaf with no
speculation site. Its speculative trace is therefore state-independent outright, for
every predictor and every window — no public/secret split and no `PubDriven` side
condition. The `OwnedCF` layer above it is the model of the emitted control-flow
shapes; nothing here maps an `Lcmd` carrying `Lcond`/`Lgoto` to an `OwnedCF`. -/

/-- A straight-line leaf has no speculation site: its speculative trace is its
    architectural trace, for every predictor and every window. -/
theorem cfSpecExec_straight {w : Nat} (window : Nat) (P : CFPredictor w)
    (s : JState w) (body : List (JInstr w)) :
    (cfSpecExec window P s (.straight body)).1 = archTrace (blockLeak s body) := by
  rw [cfSpecExec]

/-- A straight-line leaf in the index-free fragment has a speculative trace fixed by
    the program text. -/
theorem cfSpecExec_straight_isDirect {w : Nat} (window : Nat) (P : CFPredictor w)
    {body : List (JInstr w)} (h : ∀ i ∈ body, IsDirect i) (s₁ s₂ : JState w) :
    (cfSpecExec window P s₁ (.straight body)).1
      = (cfSpecExec window P s₂ (.straight body)).1 := by
  rw [cfSpecExec_straight, cfSpecExec_straight,
    blockLeak_state_independent body h s₁ s₂]

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherImmForms (gatherJBlock6)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage (allDirect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCTPreservation (lcmdDirect)

/-- The `allDirect` form of `cfSpecExec_straight_isDirect`. -/
theorem cfSpecExec_straight_allDirect {w : Nat} (window : Nat) (P : CFPredictor w)
    {body : List (JInstr w)} (h : allDirect body = true) (s₁ s₂ : JState w) :
    (cfSpecExec window P s₁ (.straight body)).1
      = (cfSpecExec window P s₂ (.straight body)).1 :=
  cfSpecExec_straight_isDirect window P
    (ConstantTimeCoverage.allDirect_mem_isDirect body h) s₁ s₂

/-- **The deployed export's gathered block under branch misprediction.** When the
    virtual body a `Com` lowers to uses no register-indexed operand, the block the
    deployed allocator emits is a straight-line leaf whose speculative leakage trace
    is the same from any two machine states, for every branch predictor and every
    speculation window.

    Covered: the leaf the export gathers, which carries no control-transfer
    instruction and so no speculation site. Not covered: a body whose `Lcmd` carries
    `Lcond`/`Lgoto` — that body does not gather, and no lowering from such an `Lcmd`
    to an `OwnedCF` is established here; and a kernel using register-indexed
    addressing, which fails the `lcmdDirect` hypothesis. -/
theorem toLprogPhysAbi_gather_cfSpec_state_independent {Γ : Ctxt jasminDialect}
    {t : JasminTy} (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle) (immSlotMap : ImmSlotMap) (inLoadMap : InLoadMap)
    (outStoreMap : OutStoreMap) (abiArgs : List String) (abiTyin : List Nat)
    (residence : Option (Array Nat)) (abiW : Nat) (forceLivePin : Bool)
    (hd : lcmdDirect (comToLfundef com immSlotMap).lfd_body = true)
    {f : String × Lfundef} {g : List (JInstr 64)}
    (hf : f ∈ (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap outStoreMap
      abiArgs abiTyin residence abiW forceLivePin).lp_funcs)
    (hg : gatherJBlock6 f.2.lfd_body = some g)
    (window : Nat) (P : CFPredictor 64) (s₁ s₂ : JState 64) :
    (cfSpecExec window P s₁ (.straight g)).1
      = (cfSpecExec window P s₂ (.straight g)).1 :=
  cfSpecExec_straight_allDirect window P
    (AllocCTPreservation.toLprogPhysAbi_gather_allDirect com fname shiftImm immSlotMap
      inLoadMap outStoreMap abiArgs abiTyin residence abiW forceLivePin hd hf hg) s₁ s₂

/-- **The deployed export's gathered block inside a structured control-flow
    context.** A `CFControlled` block whose straight-line leaves are index-free has,
    under a public-driven predictor, the same speculative leakage trace from any two
    states agreeing on the public registers. The gathered block of the deployed
    export supplies such a leaf: `CFAllDirect (.straight g)` holds of it. -/
theorem toLprogPhysAbi_gather_cfAllDirect {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (shiftImm : ShiftImmOracle)
    (immSlotMap : ImmSlotMap) (inLoadMap : InLoadMap) (outStoreMap : OutStoreMap)
    (abiArgs : List String) (abiTyin : List Nat) (residence : Option (Array Nat))
    (abiW : Nat) (forceLivePin : Bool)
    (hd : lcmdDirect (comToLfundef com immSlotMap).lfd_body = true)
    {f : String × Lfundef} {g : List (JInstr 64)}
    (hf : f ∈ (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap outStoreMap
      abiArgs abiTyin residence abiW forceLivePin).lp_funcs)
    (hg : gatherJBlock6 f.2.lfd_body = some g) :
    CFAllDirect (OwnedCF.straight g) :=
  ConstantTimeCoverage.allDirect_mem_isDirect g
    (AllocCTPreservation.toLprogPhysAbi_gather_allDirect com fname shiftImm immSlotMap
      inLoadMap outStoreMap abiArgs abiTyin residence abiW forceLivePin hd hf hg)

end CatCrypt.Crypto.SecureCompilation.X86Backend.SpeculativeCTControlFlow
