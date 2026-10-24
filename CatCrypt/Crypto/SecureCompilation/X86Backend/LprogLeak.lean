/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled

/-!
# Leakage of `Lprog` along the executed trace

A leakage model for the labelled semantics of `JasminLsemLabeled` (`findInstr`,
`evalInstrP`) and the constant-time notion it induces.

A leakage model `LeakFn w ε` assigns to each instruction and state a list of
events of type `ε`, subject to four conditions:

* the number of events of an instruction does not depend on the state;
* equal events of a `Lcond` fix whether its condition operand is non-zero;
* states that agree on memory and on the names the instruction reads
  (`readNames`) give equal events;
* a single-destination `Lopn` whose sources are registers and immediates emits
  nothing.

`LprogLeakCT.ctLeak` is the instance in the event vocabulary `CT.CTLeak`
(branch outcomes and `lmem` addresses).

## Main results

* `lprogLeak L P n s`: the events of the first `n` steps of `P` from `s`,
  stopping at a halted state or a failed step.
* `EntryCT L P pub`: two entry states (same function, program counter `0`)
  related by `pub` have equal leakage for every number of steps.
* `lprogLeak_split`: two states at the same instruction with equal leakage for
  every fuel emit the same events there, both step or both fail, reach the same
  function and program counter, and continue with equal leakage. The event count
  of a step is fixed by the instruction, so a flattened trace splits into its
  steps in the same way on both sides.
* `lprogLeak_silent`: a straight-line run of event-free `Lopn` instructions
  shifts the leakage by the run's length.
* `lsemStep_agreeOn`: a step from two states that agree on memory, on the names
  the instruction reads and on a set of names ends in two states that agree on
  memory and on that set.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeak

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc (regOrImm)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
  (applyOpn_isSome_congr_length)

/-! ## 1. Read names and leakage models -/

/-- The `lvm` names an operand reads: a register, or the index of an indexed
    access. -/
def opNames : LOperand → List String
  | .reg n => [n]
  | .arrIdx _ x _ => [x]
  | _ => []

/-- The `lvm` names an instruction reads, destinations' index registers
    included. -/
def readNames : LinstrR → List String
  | .Lopn ds _ ss => (ds ++ ss).flatMap opNames
  | .Lcond c _ => opNames c
  | _ => []

/-- A leakage model over `Lstate w` with events of type `ε`. -/
structure LeakFn (w : Nat) (ε : Type) where
  /-- The events of an instruction from a state. -/
  ev : Lstate w → LinstrR → List ε
  /-- The number of events does not depend on the state. -/
  length_eq : ∀ (s t : Lstate w) (i : LinstrR), (ev s i).length = (ev t i).length
  /-- The events of a conditional branch fix its outcome. -/
  cond : ∀ (s t : Lstate w) (c : LOperand) (l : LLabel),
    ev s (.Lcond c l) = ev t (.Lcond c l) →
      ((evalOperand s c ≠ 0) ↔ (evalOperand t c ≠ 0))
  /-- The events depend on memory and on the names read. -/
  congr : ∀ (s t : Lstate w) (i : LinstrR), s.lmem = t.lmem →
    (∀ x ∈ readNames i, s.lvm x = t.lvm x) → ev s i = ev t i
  /-- A register-and-immediate `Lopn` emits nothing. -/
  frag : ∀ (s : Lstate w) (d opn : String) (ss : List LOperand),
    ss.all regOrImm = true → ev s (.Lopn [.reg d] opn ss) = []

variable {w : Nat} {ε : Type}

/-- The events of the first `n` steps of `P` from `s`. A halted state
    (`findInstr` is `none`) emits nothing; a failed step emits the events of the
    fetched instruction and stops. -/
def lprogLeak (L : LeakFn w ε) (P : Lprog) : Nat → LstateP w → List ε
  | 0, _ => []
  | n + 1, s =>
      match findInstr P s with
      | none => []
      | some i =>
          L.ev s.base i ++
            match evalInstrP P i s with
            | some s' => lprogLeak L P n s'
            | none => []

/-- Constant time from function entry: two states at program counter `0` of the
    same function, related by `pub`, have equal leakage for every fuel. -/
def EntryCT (L : LeakFn w ε) (P : Lprog) (pub : LstateP w → LstateP w → Prop) : Prop :=
  ∀ s₁ s₂ : LstateP w, pub s₁ s₂ → s₁.lfn = s₂.lfn → s₁.base.lpc = 0 →
    s₂.base.lpc = 0 → ∀ n, lprogLeak L P n s₁ = lprogLeak L P n s₂

@[simp] theorem lprogLeak_zero (L : LeakFn w ε) (P : Lprog) (s : LstateP w) :
    lprogLeak L P 0 s = [] := rfl

theorem lprogLeak_succ_of_findInstr (L : LeakFn w ε) (P : Lprog) (n : Nat)
    {s : LstateP w} {i : LinstrR} (h : findInstr P s = some i) :
    lprogLeak L P (n + 1) s =
      L.ev s.base i ++
        match evalInstrP P i s with
        | some s' => lprogLeak L P n s'
        | none => [] := by
  simp only [lprogLeak, h]

theorem lprogLeak_of_findInstr_none (L : LeakFn w ε) (P : Lprog) (n : Nat)
    {s : LstateP w} (h : findInstr P s = none) : lprogLeak L P n s = [] := by
  cases n with
  | zero => rfl
  | succ n => simp only [lprogLeak, h]

/-! ## 2. Steps from two states at one instruction -/

/-- Whether an instruction steps does not depend on the state. -/
theorem lsemStep_isSome_congr (i : LinstrR) (s t : Lstate w) :
    (lsemStep i s).isSome = (lsemStep i t).isSome := by
  have hap : ∀ (opn : String) (l₁ l₂ : List (BitVec w)) (f g : BitVec w → Lstate w),
      l₁.length = l₂.length →
      (match applyOpn opn l₁ with | some v => some (f v) | none => none).isSome =
        (match applyOpn opn l₂ with | some v => some (g v) | none => none).isSome := by
    intro opn l₁ l₂ f g hl
    have := applyOpn_isSome_congr_length opn l₁ l₂ hl
    cases h₁ : applyOpn opn l₁ <;> cases h₂ : applyOpn opn l₂ <;> simp_all
  cases i with
  | Lopn ds opn ss =>
      match ds, ss with
      | [.reg d], .arrIdx b x sc :: rest =>
          simp only [lsemStep]
          split_ifs
          · rfl
          · cases rest with
            | nil => rfl
            | cons v tl => cases tl <;> rfl
          · exact hap _ _ _ _ _ (by simp)
      | [.reg d], [] => exact hap _ _ _ _ _ (by simp)
      | [.reg d], .reg _ :: rest => exact hap _ _ _ _ _ (by simp)
      | [.reg d], .imm _ :: rest => exact hap _ _ _ _ _ (by simp)
      | [.reg d], .arr _ _ :: rest => exact hap _ _ _ _ _ (by simp)
      | [], _ => rfl
      | [.imm _], _ => rfl
      | [.arr _ _], _ => rfl
      | [.arrIdx _ _ _], _ => rfl
      | _ :: _ :: _, _ => simp [lsemStep]
  | _ => rfl

/-- Two states of one function at one instruction, with equal events there, both
    step or both fail, and a step reaches the same function, and the same program
    counter when the two started at the same one. -/
theorem evalInstrP_lockstep (L : LeakFn w ε) (P : Lprog) (i : LinstrR)
    (s₁ s₂ : LstateP w) (hfn : s₁.lfn = s₂.lfn) (hleak : L.ev s₁.base i = L.ev s₂.base i) :
    (evalInstrP P i s₁).isSome = (evalInstrP P i s₂).isSome ∧
      ∀ a b, evalInstrP P i s₁ = some a → evalInstrP P i s₂ = some b →
        a.lfn = b.lfn ∧ (s₁.base.lpc = s₂.base.lpc → a.base.lpc = b.base.lpc) := by
  have hjump : ∀ (d : String × LLabel),
      (evalJump P d s₁).isSome = (evalJump P d s₂).isSome ∧
        ∀ a b, evalJump P d s₁ = some a → evalJump P d s₂ = some b →
          a.lfn = b.lfn ∧ (s₁.base.lpc = s₂.base.lpc → a.base.lpc = b.base.lpc) := by
    intro d
    obtain ⟨fn, l⟩ := d
    simp only [evalJump]
    cases getFundef P fn with
    | none => simp
    | some fd =>
        dsimp only
        cases findLabel l (fd.lfd_body.map Linstr.li_i) with
        | none => simp
        | some pc =>
            refine ⟨rfl, ?_⟩
            intro a b ha hb
            simp only [Option.some.injEq] at ha hb
            subst ha hb
            exact ⟨rfl, fun _ => rfl⟩
  have hstraight : ∀ j : LinstrR, IsStraightLine j = true →
      (evalInstrP P j s₁).isSome = (evalInstrP P j s₂).isSome ∧
        ∀ a b, evalInstrP P j s₁ = some a → evalInstrP P j s₂ = some b →
          a.lfn = b.lfn ∧ (s₁.base.lpc = s₂.base.lpc → a.base.lpc = b.base.lpc) := by
    intro j hj
    rw [evalInstrP_straightLine P j s₁ hj, evalInstrP_straightLine P j s₂ hj]
    refine ⟨by simp only [Option.isSome_map]; exact lsemStep_isSome_congr j _ _, ?_⟩
    intro a b ha hb
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.1 ha
    obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 hb
    refine ⟨hfn, fun hpc => ?_⟩
    simp only [lsemStep_lpc_succ j _ _ hj ha', lsemStep_lpc_succ j _ _ hj hb', hpc]
  cases i with
  | Lgoto d => exact hjump d
  | Lcond c l =>
      have hc := L.cond _ _ c l hleak
      simp only [evalInstrP]
      by_cases h₁ : evalOperand s₁.base c ≠ 0
      · have h₂ := hc.1 h₁
        simp only [h₁, h₂, ite_true, ne_eq, not_false_eq_true]
        rw [hfn]
        exact hjump (s₂.lfn, l)
      · have h₂ : ¬ evalOperand s₂.base c ≠ 0 := fun h => h₁ (hc.2 h)
        simp only [h₁, h₂, ite_false]
        refine ⟨rfl, ?_⟩
        intro a b ha hb
        simp only [Option.some.injEq] at ha hb
        subst ha hb
        exact ⟨hfn, fun hpc => by simp [hpc]⟩
  | Lopn ds opn ss => exact hstraight _ rfl
  | Llabel k l => exact hstraight _ rfl
  | Lalign => exact hstraight _ rfl
  | Ligoto _ => simp [evalInstrP]
  | Lcall _ _ => simp [evalInstrP]
  | Lret => simp [evalInstrP]
  | LstoreLabel _ _ => simp [evalInstrP]
  | Lsyscall _ => simp [evalInstrP]

/-- **Splitting equal leakage at one step.** Two states of one function at one
    instruction, with equal leakage for every fuel, emit the same events at the
    instruction, both step or both fail, and after a step reach the same function
    and program counter (when they started at the same one) with equal leakage for
    every fuel. -/
theorem lprogLeak_split (L : LeakFn w ε) (P : Lprog) {s₁ s₂ : LstateP w} {i : LinstrR}
    (heq : ∀ n, lprogLeak L P n s₁ = lprogLeak L P n s₂) (hfn : s₁.lfn = s₂.lfn)
    (h₁ : findInstr P s₁ = some i) (h₂ : findInstr P s₂ = some i) :
    L.ev s₁.base i = L.ev s₂.base i ∧
      (evalInstrP P i s₁).isSome = (evalInstrP P i s₂).isSome ∧
      ∀ a b, evalInstrP P i s₁ = some a → evalInstrP P i s₂ = some b →
        a.lfn = b.lfn ∧ (s₁.base.lpc = s₂.base.lpc → a.base.lpc = b.base.lpc) ∧
          ∀ n, lprogLeak L P n a = lprogLeak L P n b := by
  have e : ∀ (s : LstateP w),
      (match evalInstrP P i s with
        | some s' => lprogLeak L P 0 s'
        | none => []) = [] := by
    intro s; cases evalInstrP P i s <;> rfl
  have h1 := heq 1
  rw [lprogLeak_succ_of_findInstr L P 0 h₁, lprogLeak_succ_of_findInstr L P 0 h₂,
    e s₁, e s₂, List.append_nil, List.append_nil] at h1
  obtain ⟨hsome, hpos⟩ := evalInstrP_lockstep L P i s₁ s₂ hfn h1
  refine ⟨h1, hsome, fun a b ha hb => ⟨(hpos a b ha hb).1, (hpos a b ha hb).2, ?_⟩⟩
  intro n
  have h := heq (n + 1)
  rw [lprogLeak_succ_of_findInstr L P n h₁, lprogLeak_succ_of_findInstr L P n h₂, ha, hb,
    h1] at h
  exact List.append_cancel_left h

/-! ## 3. A silent straight-line run -/

theorem lsemStraight_lpc :
    ∀ (is : List LinstrR) (s b : Lstate w), (∀ i ∈ is, IsStraightLine i = true) →
      lsemStraight is s = some b → b.lpc = s.lpc + is.length := by
  intro is
  induction is with
  | nil => intro s b _ h; simp only [lsemStraight_nil, Option.some.injEq] at h; subst h; rfl
  | cons i is ih =>
      intro s b hsl h
      simp only [lsemStraight_cons] at h
      cases hs : lsemStep i s with
      | none => rw [hs] at h; cases h
      | some s' =>
          rw [hs] at h
          rw [ih s' b (fun j hj => hsl j (List.mem_cons_of_mem _ hj)) h,
            lsemStep_lpc_succ i s s' (hsl i (List.mem_cons_self ..)) hs, List.length_cons]
          omega

/-- **A silent run shifts the leakage by its length.** When the instructions at
    `pre, pre+1, …` of the body are the straight-line, event-free instructions
    `runR`, and they run from `s` to `b`, the leakage from `s` with fuel `n` is the
    leakage from the state after the run with fuel `n - runR.length`. -/
theorem lprogLeak_silent (L : LeakFn w ε) (P : Lprog) (fn : String) (bodyR : List LinstrR)
    (Hfetch : ∀ u : LstateP w, u.lfn = fn → findInstr P u = bodyR[u.base.lpc]?) :
    ∀ (runR : List LinstrR),
      (∀ i ∈ runR, IsStraightLine i = true ∧ ∀ t : Lstate w, L.ev t i = []) →
      ∀ (pre : Nat), (∀ (k : Nat) (hk : k < runR.length), bodyR[pre + k]? = some runR[k]) →
      ∀ (s : LstateP w), s.lfn = fn → s.base.lpc = pre →
      ∀ (b : Lstate w), lsemStraight runR s.base = some b →
      ∀ n, lprogLeak L P n s = lprogLeak L P (n - runR.length) ⟨b, fn⟩ := by
  intro runR
  induction runR with
  | nil =>
      intro _ pre _ s hfn _ b hb n
      simp only [lsemStraight_nil, Option.some.injEq] at hb
      subst hb
      obtain ⟨sb, sfn⟩ := s
      simp only at hfn
      subst hfn
      rfl
  | cons i is ih =>
      intro hsil pre hat s hfn hpc b hb n
      have hi := hsil i (List.mem_cons_self ..)
      have hfetch : findInstr P s = some i := by
        rw [Hfetch s hfn, hpc]
        exact hat 0 (by simp)
      simp only [lsemStraight_cons] at hb
      cases hs : lsemStep i s.base with
      | none => rw [hs] at hb; cases hb
      | some b₁ =>
          rw [hs] at hb
          have hstep : evalInstrP P i s = some ⟨b₁, fn⟩ := by
            rw [evalInstrP_straightLine P i s hi.1, hs]
            simp [hfn]
          cases n with
          | zero => simp
          | succ n =>
              rw [lprogLeak_succ_of_findInstr L P n hfetch, hstep, hi.2 s.base, List.nil_append]
              dsimp only
              have hat' : ∀ (k : Nat) (hk : k < is.length),
                  bodyR[(pre + 1) + k]? = some is[k] := by
                intro k hk
                have := hat (k + 1) (by simp; omega)
                rw [show pre + 1 + k = pre + (k + 1) by omega]
                simpa using this
              have hpc₁ : b₁.lpc = pre + 1 := by rw [lsemStep_lpc_succ i _ _ hi.1 hs, hpc]
              rw [ih (fun j hj => hsil j (List.mem_cons_of_mem _ hj)) (pre + 1) hat'
                ⟨b₁, fn⟩ rfl hpc₁ b hb n]
              congr 1
              simp only [List.length_cons]
              omega

/-! ## 4. A step from two states that agree on a set of names -/

theorem evalOperand_agreeOn {s t : Lstate w} (hm : s.lmem = t.lmem) (o : LOperand)
    (hv : ∀ x ∈ opNames o, s.lvm x = t.lvm x) : evalOperand s o = evalOperand t o := by
  cases o with
  | reg r => exact hv r (by simp [opNames])
  | imm _ => rfl
  | arr b i => simp [evalOperand, hm]
  | arrIdx b x sc => simp [evalOperand, hm, hv x (by simp [opNames])]

/-- **A step preserves agreement on a set of names.** From two states that agree
    on memory, on the names `i` reads and on the names satisfying `A`, the step of
    `i` succeeds on both or on neither, and the results agree on memory and on the
    names satisfying `A`. -/
theorem lsemStep_agreeOn (A : String → Prop) (i : LinstrR) {s t : Lstate w}
    (hm : s.lmem = t.lmem) (hr : ∀ x ∈ readNames i, s.lvm x = t.lvm x)
    (hA : ∀ x, A x → s.lvm x = t.lvm x) :
    (lsemStep i s).isSome = (lsemStep i t).isSome ∧
      ∀ s' t', lsemStep i s = some s' → lsemStep i t = some t' →
        s'.lmem = t'.lmem ∧ ∀ x, A x → s'.lvm x = t'.lvm x := by
  refine ⟨lsemStep_isSome_congr i s t, ?_⟩
  have hsrc : ∀ (ds ss : List LOperand) (opn : String), i = .Lopn ds opn ss →
      ∀ o ∈ ss, evalOperand s o = evalOperand t o := by
    intro ds ss opn hi o ho
    subst hi
    refine evalOperand_agreeOn hm o (fun x hx => hr x ?_)
    simp only [readNames, List.mem_flatMap, List.mem_append]
    exact ⟨o, Or.inr ho, hx⟩
  have hset : ∀ (d : String) (v : BitVec w),
      ((s.setReg d v).nextPc).lmem = ((t.setReg d v).nextPc).lmem ∧
        ∀ x, A x → ((s.setReg d v).nextPc).lvm x = ((t.setReg d v).nextPc).lvm x := by
    intro d v
    refine ⟨hm, fun x hx => ?_⟩
    simp only [Lstate.nextPc, Lstate.lvm_setReg]
    split
    · rfl
    · exact hA x hx
  intro s' t' hs ht
  cases i with
  | Lopn ds opn ss =>
      have hev := hsrc ds ss opn rfl
      have hmap : ss.map (evalOperand s) = ss.map (evalOperand t) :=
        List.map_congr_left hev
      match ds, ss, hev, hmap, hr with
      | [.reg d], .arrIdx b x sc :: rest, hev, hmap, hr =>
          have hx : s.lvm x = t.lvm x := hr x (by simp [readNames, opNames])
          simp only [lsemStep] at hs ht
          rw [hx] at hs
          split_ifs at hs ht with h1 h2
          · simp only [Option.some.injEq] at hs ht
            subst hs ht
            rw [hm]
            exact hset d _
          · cases rest with
            | nil => cases hs
            | cons v tl =>
                cases tl with
                | cons _ _ => cases hs
                | nil =>
                    simp only [Option.some.injEq] at hs ht
                    subst hs ht
                    have hv := hev v (by simp)
                    refine ⟨?_, fun y hy => hA y hy⟩
                    simp only [Lstate.nextPc, hm, hv]
          · rw [hmap] at hs
            cases happ : applyOpn (stripWidthTag opn)
                ((LOperand.arrIdx b x sc :: rest).map (evalOperand t)) with
            | none => rw [happ] at hs; cases hs
            | some v =>
                rw [happ] at hs ht
                simp only [Option.some.injEq] at hs ht
                subst hs ht
                exact hset d v
      | [.reg d], [], _, hmap, _ =>
          simp only [lsemStep, List.map_nil] at hs ht
          cases happ : applyOpn (w := w) (stripWidthTag opn) [] with
          | none => rw [happ] at hs; cases hs
          | some v =>
              rw [happ] at hs ht
              simp only [Option.some.injEq] at hs ht
              subst hs ht
              exact hset d v
      | [.reg d], .reg r :: rest, _, hmap, _ =>
          simp only [lsemStep] at hs ht
          rw [hmap] at hs
          cases happ : applyOpn (stripWidthTag opn) ((LOperand.reg r :: rest).map (evalOperand t)) with
          | none => rw [happ] at hs; cases hs
          | some v =>
              rw [happ] at hs ht
              simp only [Option.some.injEq] at hs ht
              subst hs ht
              exact hset d v
      | [.reg d], .imm k :: rest, _, hmap, _ =>
          simp only [lsemStep] at hs ht
          rw [hmap] at hs
          cases happ : applyOpn (stripWidthTag opn) ((LOperand.imm k :: rest).map (evalOperand t)) with
          | none => rw [happ] at hs; cases hs
          | some v =>
              rw [happ] at hs ht
              simp only [Option.some.injEq] at hs ht
              subst hs ht
              exact hset d v
      | [.reg d], .arr b k :: rest, _, hmap, _ =>
          simp only [lsemStep] at hs ht
          rw [hmap] at hs
          cases happ : applyOpn (stripWidthTag opn) ((LOperand.arr b k :: rest).map (evalOperand t)) with
          | none => rw [happ] at hs; cases hs
          | some v =>
              rw [happ] at hs ht
              simp only [Option.some.injEq] at hs ht
              subst hs ht
              exact hset d v
      | [], _, _, _, _ => simp [lsemStep] at hs
      | [.imm _], _, _, _, _ => simp [lsemStep] at hs
      | [.arr _ _], _, _, _, _ => simp [lsemStep] at hs
      | [.arrIdx _ _ _], _, _, _, _ => simp [lsemStep] at hs
      | _ :: _ :: _, _, _, _, _ => simp [lsemStep] at hs
  | Llabel _ _ =>
      simp only [lsemStep, Option.some.injEq] at hs ht
      subst hs ht
      exact ⟨hm, hA⟩
  | Lalign =>
      simp only [lsemStep, Option.some.injEq] at hs ht
      subst hs ht
      exact ⟨hm, hA⟩
  | _ => simp [lsemStep] at hs

end CatCrypt.Crypto.SecureCompilation.X86Backend.LprogLeak
