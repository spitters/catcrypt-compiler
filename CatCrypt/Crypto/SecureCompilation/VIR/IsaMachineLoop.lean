/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.IsaMachineBlock
public import CatCrypt.Crypto.SecureCompilation.MachineMem64

@[expose] public section

set_option autoImplicit false

/-!
# Counted loops of a decoded program over `IsaMachine`

`IsaMachine.ReachesIn M prog n pc s t pc' s'` is a path of exactly `n` steps of `mstep` from
index `pc` and state `s` to index `pc'` and state `s'`, with the leakage trace `t`: the step
count is the fuel of the path, and the trace is the concatenation of `stepLeak` along it.
Forgetting the count and the trace gives `IsaMachine.Reaches`; a path followed by a halting
run with leakage is a halting run with leakage.

A loop node of a decoded program has a guard segment from the index `g`, a body segment from
the index `top` to the index `foot`, and a conditional back branch at `foot` to `top`. The
guard reaches `top` when the trip count is not zero and an exit index otherwise. For a trip
count `k`, a guard of `ng` steps and a body of `nb` steps, the node runs in
`ng + k * (nb + 1)` steps and ends in the state of `k` iterations of the body transformer on
the state after the guard (`reachesIn_loopNode`). The trip count is carried by an invariant
`Inv j s`, `j` the number of iterations that remain, which fixes the outcome of the back
branch.

`LimbInv` is the memory invariant of a loop that writes `f (A k) (B k)` to the cell `k` of an
output array from the cells `k` of two input arrays; `LimbInv.step` is one iteration.

## Main definitions

* `IsaMachine.stepLeak`, `IsaMachine.ReachesIn`: the leakage of one step, and the paths with
  step count and trace.
* `IsaMachine.loopLeak`: the trace of `k` iterations of a loop.
* `MachineMem64.LimbInv`: the memory invariant of a limb-wise loop.

## Main results

* `IsaMachine.ReachesIn.reaches`, `IsaMachine.ReachesIn.trans`, `IsaMachine.ReachesIn.runL`:
  the path without count and trace, composition, and a path before a halting run.
* `IsaMachine.reachesIn_ops`, `IsaMachine.reachesIn_branch`: a straight-line segment and a
  branch as paths.
* `IsaMachine.reachesIn_loop`: the body and the back branch, for a trip count `k + 1`.
* `IsaMachine.reachesIn_loopNode`: the guarded loop, the zero-trip case included.
* `IsaMachine.StepAgree`, `IsaMachine.RunL.trace_eq_of_stepAgree`,
  `IsaMachine.constantTimeRel_of_stepAgree`: two runs with leakage from states related at an
  index have equal traces when every step from related states has equal leakage and leads to
  related states; the halting runs from index 0 are then `ConstantTimeRel` for the relation
  at index 0.
* `MachineMem64.decide_ofNat64_ne_zero`: the zero test of a count as a 64-bit word.
* `MachineMem64.LimbInv.step`: one iteration of a limb-wise loop.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Next)
open CatCrypt.Crypto.SecureCompilation.CT

namespace IsaMachine

/-- The leakage of the step of `prog` at `pc` in the state `s`: an operation emits `opLeak`,
    a block `blockLeak`, a branch the `branch` event of its outcome. -/
def stepLeak (M : IsaMachine) (prog : List M.Instr) (pc : Nat) (s : M.MState) : List CTLeak :=
  match M.act prog pc s with
  | some (.op i) => M.opLeak s i
  | some (.block ops) => M.blockLeak s ops
  | some (.branch b _) => [.branch b]
  | _ => []

/-- **A path with step count and trace**: `n` steps of `mstep` from index `pc` and state `s`
    to index `pc'` and state `s'`, with the leakage trace `t`. -/
inductive ReachesIn (M : IsaMachine) (prog : List M.Instr) :
    Nat → Nat → M.MState → List CTLeak → Nat → M.MState → Prop
  | refl (pc : Nat) (s : M.MState) : ReachesIn M prog 0 pc s [] pc s
  | next {n pc : Nat} {s : M.MState} {pc' : Nat} {s' : M.MState} {t : List CTLeak} {pc'' : Nat}
      {s'' : M.MState} (h : M.mstep prog pc s = some (.go pc' s'))
      (hr : ReachesIn M prog n pc' s' t pc'' s'') :
      ReachesIn M prog (n + 1) pc s (M.stepLeak prog pc s ++ t) pc'' s''

variable {M : IsaMachine}

/-- A path with step count and trace is a path. -/
theorem ReachesIn.reaches {prog : List M.Instr} {n pc : Nat} {s : M.MState} {t : List CTLeak}
    {pc' : Nat} {s' : M.MState} (h : M.ReachesIn prog n pc s t pc' s') :
    M.Reaches prog pc s pc' s' := by
  induction h with
  | refl => exact .refl _ _
  | next hs _ ih => exact .next hs ih

/-- **Composition of paths**: the step counts add and the traces concatenate. -/
theorem ReachesIn.trans {prog : List M.Instr} {n m pc : Nat} {s : M.MState} {t u : List CTLeak}
    {pc' : Nat} {s' : M.MState} {pc'' : Nat} {s'' : M.MState}
    (h : M.ReachesIn prog n pc s t pc' s') (h' : M.ReachesIn prog m pc' s' u pc'' s'') :
    M.ReachesIn prog (n + m) pc s (t ++ u) pc'' s'' := by
  induction h with
  | refl => simpa using h'
  | @next n pc s pc₁ s₁ t pc₂ s₂ hs _ ih =>
    have := ReachesIn.next hs (ih h')
    rwa [show n + m + 1 = n + 1 + m by omega, ← List.append_assoc] at this

/-- A path under equal step count, trace, end index and end state. -/
theorem ReachesIn.congr {prog : List M.Instr} {n n' pc : Nat} {s : M.MState}
    {t t' : List CTLeak} {pc' pc'' : Nat} {s' s'' : M.MState}
    (h : M.ReachesIn prog n pc s t pc' s') (hn : n = n') (ht : t = t') (hpc : pc' = pc'')
    (hs : s' = s'') : M.ReachesIn prog n' pc s t' pc'' s'' := by
  subst hn ht hpc hs
  exact h

/-- **A path before a halting run with leakage** is a halting run with leakage, the trace of
    the path first. -/
theorem ReachesIn.runL {prog : List M.Instr} {n pc : Nat} {s : M.MState} {t u : List CTLeak}
    {pc' : Nat} {s' s'' : M.MState} (h : M.ReachesIn prog n pc s t pc' s')
    (h' : M.RunL (fun _ _ => True) prog pc' s' u s'') :
    M.RunL (fun _ _ => True) prog pc s (t ++ u) s'' := by
  induction h with
  | refl => simpa using h'
  | @next n pc s pc₁ s₁ t pc₂ s₂ hs _ ih =>
    have hr := ih h'
    rw [List.append_assoc]
    unfold mstep at hs
    unfold stepLeak
    split at hs
    · exact absurd hs (by simp)
    · rename_i i hi
      simp only [Option.some.injEq, Next.go.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      rw [hi]
      exact .op hi trivial hr
    · rename_i ops hi
      simp only [Option.some.injEq, Next.go.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      rw [hi]
      exact .block hi (M.blockOk_true _ _) hr
    · rename_i b tgt hi
      simp only [Option.some.injEq, Next.go.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      rw [hi]
      exact .branch hi hr
    · simp at hs
    · simp at hs

/-- **A straight-line segment as a path**: `ops.length` steps with the leakage of the block,
    to the index after the segment and the state of the block fold. -/
theorem reachesIn_ops {prog : List M.Instr} :
    ∀ (ops : List M.Op) (pc : Nat) (s : M.MState), M.OpsAt prog pc ops →
      M.ReachesIn prog ops.length pc s (M.blockLeak s ops) (pc + ops.length) (M.runBlock s ops)
  | [], pc, s, _ => .refl pc s
  | i :: is, pc, s, h => by
      have hstep : M.mstep prog pc s = some (.go (pc + 1) (M.exec s i)) := by
        simp only [mstep, h.head s]
      have hleak : M.stepLeak prog pc s = M.opLeak s i := by
        simp only [stepLeak, h.head s]
      have ih := reachesIn_ops is (pc + 1) (M.exec s i) h.tail
      rw [show pc + 1 + is.length = pc + (i :: is).length by simp; omega] at ih
      have := ReachesIn.next hstep ih
      rwa [hleak] at this

/-- **A branch as a path**: one step with the `branch` event of the outcome, to the target
    when taken and to the next index otherwise. -/
theorem reachesIn_branch {prog : List M.Instr} {pc : Nat} {s : M.MState} {b : Bool} {tgt : Nat}
    (h : M.act prog pc s = some (.branch b tgt)) :
    M.ReachesIn prog 1 pc s [.branch b] (if b then tgt else pc + 1) s := by
  have hstep : M.mstep prog pc s = some (.go (if b then tgt else pc + 1) s) := by
    simp only [mstep, h]
  have := ReachesIn.next hstep (.refl _ _)
  simpa [stepLeak, h] using this

/-- **The trace of `k` iterations of a loop** with the body transformer `F` and the body trace
    `T`: the trace of the body, then the `branch` event of the back branch, taken when an
    iteration remains. -/
def loopLeak {S : Type} (F : S → S) (T : S → List CTLeak) : Nat → S → List CTLeak
  | 0, _ => []
  | k + 1, s => T s ++ .branch (decide (k ≠ 0)) :: loopLeak F T k (F s)

/-- Loops whose body traces agree along two runs related by `R` have equal traces. -/
theorem loopLeak_congr {S : Type} {F : S → S} {T : S → List CTLeak} {R : S → S → Prop}
    (hT : ∀ s₁ s₂, R s₁ s₂ → T s₁ = T s₂) (hF : ∀ s₁ s₂, R s₁ s₂ → R (F s₁) (F s₂)) :
    ∀ (k : Nat) (s₁ s₂ : S), R s₁ s₂ → loopLeak F T k s₁ = loopLeak F T k s₂
  | 0, _, _, _ => rfl
  | k + 1, s₁, s₂, h => by
      simp only [loopLeak, hT s₁ s₂ h, loopLeak_congr hT hF k _ _ (hF s₁ s₂ h)]

/-- **The run of a counted loop from its head.** The body is a path of `nb` steps from `top`
    to `foot` with the transformer `F` and the trace `T`; the action at `foot` is a branch to
    `top`, taken when an iteration remains; `Inv j s` states that `j` iterations remain in
    `s`. From a state with `k + 1` iterations, the machine reaches the index after the branch
    in `(k + 1) * (nb + 1)` steps, in the state of `k + 1` iterations of `F`, with the trace
    `loopLeak`, and no iteration remains. -/
theorem reachesIn_loop {prog : List M.Instr} {top foot nb : Nat} {F : M.MState → M.MState}
    {T : M.MState → List CTLeak} {Inv : Nat → M.MState → Prop}
    (hbody : ∀ j s, Inv (j + 1) s → M.ReachesIn prog nb top s (T s) foot (F s))
    (hfoot : ∀ j s, Inv (j + 1) s →
      M.act prog foot (F s) = some (.branch (decide (j ≠ 0)) top))
    (hinv : ∀ j s, Inv (j + 1) s → Inv j (F s)) :
    ∀ (k : Nat) (s : M.MState), Inv (k + 1) s →
      M.ReachesIn prog ((k + 1) * (nb + 1)) top s (loopLeak F T (k + 1) s) (foot + 1)
        (F^[k + 1] s) ∧ Inv 0 (F^[k + 1] s)
  | 0, s, h => by
      have hb := (hbody 0 s h).trans (reachesIn_branch (hfoot 0 s h))
      refine ⟨hb.congr (by omega) (by simp [loopLeak]) (by simp) rfl, hinv 0 s h⟩
  | k + 1, s, h => by
      have hb := (hbody (k + 1) s h).trans (reachesIn_branch (hfoot (k + 1) s h))
      obtain ⟨ih, hi⟩ := reachesIn_loop hbody hfoot hinv k (F s) (hinv (k + 1) s h)
      refine ⟨(hb.trans ih).congr ?_ ?_ rfl ?_, ?_⟩
      · rw [Nat.succ_mul (k + 1)]; omega
      · simp [loopLeak]
      · rw [Function.iterate_succ_apply (f := F) (n := k + 1)]
      · rwa [Function.iterate_succ_apply (f := F) (n := k + 1)]

/-- **The run of a loop node.** The guard is a path of `ng` steps from `g` with the
    transformer `G` and the trace `Tg`, to `top` when the trip count `k` is not zero and to
    `exit₀` when it is zero; the body and the back branch are as in `reachesIn_loop`. From a
    state with trip count `k` (`Pre k s`), the machine reaches the exit, `exit₀` at `k = 0`
    and `foot + 1` otherwise, in `ng + k * (nb + 1)` steps, in the state of `k` iterations
    of `F` on the state after the guard, with the trace of the guard followed by `loopLeak`;
    no iteration remains. -/
theorem reachesIn_loopNode {prog : List M.Instr} {g top foot exit₀ ng nb : Nat}
    {G F : M.MState → M.MState} {Tg T : M.MState → List CTLeak}
    {Pre Inv : Nat → M.MState → Prop}
    (hguard : ∀ k s, Pre k s →
      M.ReachesIn prog ng g s (Tg s) (if k = 0 then exit₀ else top) (G s))
    (hpre : ∀ k s, Pre k s → Inv k (G s))
    (hbody : ∀ j s, Inv (j + 1) s → M.ReachesIn prog nb top s (T s) foot (F s))
    (hfoot : ∀ j s, Inv (j + 1) s →
      M.act prog foot (F s) = some (.branch (decide (j ≠ 0)) top))
    (hinv : ∀ j s, Inv (j + 1) s → Inv j (F s)) (k : Nat) (s : M.MState) (h : Pre k s) :
    M.ReachesIn prog (ng + k * (nb + 1)) g s (Tg s ++ loopLeak F T k (G s))
        (if k = 0 then exit₀ else foot + 1) (F^[k] (G s)) ∧ Inv 0 (F^[k] (G s)) := by
  have hg := hguard k s h
  cases k with
  | zero => exact ⟨hg.congr (by omega) (by simp [loopLeak]) (by simp) rfl, hpre 0 s h⟩
  | succ k =>
    obtain ⟨hl, hi⟩ := reachesIn_loop hbody hfoot hinv k (G s) (hpre (k + 1) s h)
    rw [if_neg (Nat.succ_ne_zero k)] at hg
    exact ⟨(hg.trans hl).congr rfl rfl (by simp) rfl, hi⟩

/-! ## Constant time from the leakage of one step -/

/-- **Agreement of one step** of `prog` at `pc` from the states `s₁` and `s₂`, for a relation
    `R` on the states at an index and a relation `Q` on the states at a `ret`. The two actions
    are of the same kind. Two operations or blocks are equal, have equal leakage and lead to
    states related by `R` at the next index. Two branches have the same outcome and target,
    and `R` holds at the index the branch goes to. Two calls have the same target, `callOps`
    has equal leakage and leads to states related by `R` at the target, and from callee
    states related by `Q` the block `retOps` has equal leakage and leads to states related by
    `R` at the next index. At two `ret` actions `Q` holds. A state with no action has no run,
    and the agreement holds. -/
def StepAgree (M : IsaMachine) (prog : List M.Instr) (R : Nat → M.MState → M.MState → Prop)
    (Q : M.MState → M.MState → Prop) (pc : Nat) (s₁ s₂ : M.MState) : Prop :=
  match M.act prog pc s₁, M.act prog pc s₂ with
  | none, _ => True
  | _, none => True
  | some (.op i), some (.op j) =>
      i = j ∧ M.opLeak s₁ i = M.opLeak s₂ i ∧ R (pc + 1) (M.exec s₁ i) (M.exec s₂ i)
  | some (.block a), some (.block b) =>
      a = b ∧ M.blockLeak s₁ a = M.blockLeak s₂ a ∧
        R (pc + 1) (M.runBlock s₁ a) (M.runBlock s₂ a)
  | some (.branch b t), some (.branch b' t') =>
      b = b' ∧ t = t' ∧ R (if b then t else pc + 1) s₁ s₂
  | some (.call t), some (.call t') =>
      t = t' ∧ M.blockLeak s₁ (M.callOps (pc + 1)) = M.blockLeak s₂ (M.callOps (pc + 1)) ∧
        R t (M.runBlock s₁ (M.callOps (pc + 1))) (M.runBlock s₂ (M.callOps (pc + 1))) ∧
        ∀ c₁ c₂, Q c₁ c₂ → M.blockLeak c₁ M.retOps = M.blockLeak c₂ M.retOps ∧
          R (pc + 1) (M.runBlock c₁ M.retOps) (M.runBlock c₂ M.retOps)
  | some .ret, some .ret => Q s₁ s₂
  | _, _ => False

/-- **Two runs with leakage from related states have equal traces.** When every step from
    states related by `R` satisfies `StepAgree`, two halting runs of `prog` from the same
    index and from states related by `R` there have equal leakage traces, and their final
    states are related by `Q`. -/
theorem RunL.trace_eq_of_stepAgree {ok ok' : M.MState → M.Op → Prop} {prog : List M.Instr}
    {R : Nat → M.MState → M.MState → Prop} {Q : M.MState → M.MState → Prop}
    (hstep : ∀ pc s₁ s₂, R pc s₁ s₂ → M.StepAgree prog R Q pc s₁ s₂)
    {pc : Nat} {s₁ s₂ : M.MState} {t₁ t₂ : List CTLeak} {s₁' s₂' : M.MState}
    (h₁ : M.RunL ok prog pc s₁ t₁ s₁') (h₂ : M.RunL ok' prog pc s₂ t₂ s₂')
    (hR : R pc s₁ s₂) : t₁ = t₂ ∧ Q s₁' s₂' := by
  induction h₁ generalizing s₂ t₂ s₂' with
  | ret h =>
    have hs := hstep _ _ _ hR
    cases h₂ with
    | ret h' =>
      simp only [StepAgree, h, h'] at hs
      exact ⟨rfl, hs⟩
    | _ => simp_all [StepAgree]
  | op h _ _ ih =>
    have hs := hstep _ _ _ hR
    cases h₂ with
    | op h' _ hr' =>
      simp only [StepAgree, h, h'] at hs
      obtain ⟨rfl, hl, hR'⟩ := hs
      obtain ⟨rfl, hq⟩ := ih hr' hR'
      exact ⟨by rw [hl], hq⟩
    | _ => simp_all [StepAgree]
  | block h _ _ ih =>
    have hs := hstep _ _ _ hR
    cases h₂ with
    | block h' _ hr' =>
      simp only [StepAgree, h, h'] at hs
      obtain ⟨rfl, hl, hR'⟩ := hs
      obtain ⟨rfl, hq⟩ := ih hr' hR'
      exact ⟨by rw [hl], hq⟩
    | _ => simp_all [StepAgree]
  | branch h _ ih =>
    have hs := hstep _ _ _ hR
    cases h₂ with
    | branch h' hr' =>
      simp only [StepAgree, h, h'] at hs
      obtain ⟨rfl, rfl, hR'⟩ := hs
      obtain ⟨rfl, hq⟩ := ih hr' hR'
      exact ⟨rfl, hq⟩
    | _ => simp_all [StepAgree]
  | call h _ _ _ _ ihc ihr =>
    have hs := hstep _ _ _ hR
    cases h₂ with
    | call h' _ hc' _ hr' =>
      simp only [StepAgree, h, h'] at hs
      obtain ⟨rfl, hl, hRc, hret⟩ := hs
      obtain ⟨rfl, hqc⟩ := ihc hc' hRc
      obtain ⟨hlr, hRr⟩ := hret _ _ hqc
      obtain ⟨rfl, hq⟩ := ihr hr' hRr
      exact ⟨by rw [hl, hlr], hq⟩
    | _ => simp_all [StepAgree]

/-- **Constant time of a decoded program from the leakage of its steps.** When every step
    from states related by `R` satisfies `StepAgree`, the halting runs of `prog` from index 0
    are `ConstantTimeRel` for the relation `R 0` on entry states. The hypothesis is a
    condition on single steps; the side conditions `ok` of the runs are arbitrary. -/
theorem constantTimeRel_of_stepAgree {ok : M.MState → M.Op → Prop} {prog : List M.Instr}
    {R : Nat → M.MState → M.MState → Prop} {Q : M.MState → M.MState → Prop}
    (hstep : ∀ pc s₁ s₂, R pc s₁ s₂ → M.StepAgree prog R Q pc s₁ s₂) :
    ConstantTimeRel (R 0) (fun s t => ∃ s', M.RunL ok prog 0 s t s') := by
  rintro s₁ s₂ t₁ t₂ hR ⟨_, h₁⟩ ⟨_, h₂⟩
  exact (h₁.trace_eq_of_stepAgree hstep h₂ hR).1

/-- Every step from equal states satisfies `StepAgree` for equality. -/
theorem stepAgree_eq (prog : List M.Instr) (pc : Nat) (s : M.MState) :
    M.StepAgree prog (fun _ => Eq) Eq pc s s := by
  unfold StepAgree
  cases M.act prog pc s with
  | none => trivial
  | some a => cases a <;> simp

end IsaMachine

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

namespace CatCrypt.Crypto.SecureCompilation.MachineMem64

/-- A count below `2⁶⁴` is zero exactly when its 64-bit word is. -/
theorem decide_ofNat64_ne_zero {j : Nat} (h : j < 2 ^ 64) :
    decide (BitVec.ofNat 64 j ≠ 0) = decide (j ≠ 0) := by
  have e : BitVec.ofNat 64 j = 0 ↔ j = 0 := by
    constructor
    · intro e
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
      exact this
    · rintro rfl; rfl
  exact decide_eq_decide.mpr (not_congr e)

/-- **The memory invariant of a limb-wise loop** after `i` iterations: the input arrays `A`
    at `pa` and `B` at `pb` of `n` doublewords are in place, and the cells below `i` of the
    output at `po` hold `f (A k) (B k)`. -/
def LimbInv (f : BitVec 64 → BitVec 64 → BitVec 64) (n : Nat) (pa pb po : BitVec 64)
    (A B : Fin n → BitVec 64) (i : Nat) (m : Mem64) : Prop :=
  ArrAt m pa n A ∧ ArrAt m pb n B ∧
    ∀ k : Fin n, k.val < i → read64 m (po + BitVec.ofNat 64 (8 * k.val)) = f (A k) (B k)

/-- **One iteration of a limb-wise loop**: the write of `f` of the two input cells `i` to the
    output cell `i`, the output cells separated from the input cells, takes the invariant at
    `i` to the invariant at `i + 1`. -/
theorem LimbInv.step {f : BitVec 64 → BitVec 64 → BitVec 64} {n : Nat} {pa pb po : BitVec 64}
    {A B : Fin n → BitVec 64} {i : Nat} {m : Mem64} (h : LimbInv f n pa pb po A B i m)
    (hi : i < n) (hn : 8 * n ≤ 2 ^ 64)
    (hsa : ∀ j k : Fin n,
      MemSep (po + BitVec.ofNat 64 (8 * j.val)) (pa + BitVec.ofNat 64 (8 * k.val)))
    (hsb : ∀ j k : Fin n,
      MemSep (po + BitVec.ofNat 64 (8 * j.val)) (pb + BitVec.ofNat 64 (8 * k.val))) :
    LimbInv f n pa pb po A B (i + 1)
      (write64 m (po + BitVec.ofNat 64 (8 * i))
        (f (read64 m (pa + BitVec.ofNat 64 (8 * i))) (read64 m (pb + BitVec.ofNat 64 (8 * i)))))
      := by
  obtain ⟨ha, hb, ho⟩ := h
  refine ⟨ArrAt_write_sep ha _ _ (hsa ⟨i, hi⟩), ArrAt_write_sep hb _ _ (hsb ⟨i, hi⟩), ?_⟩
  intro k hk
  by_cases hki : k.val = i
  · rw [hki, read64_write64_same]
    have e : k = ⟨i, hi⟩ := Fin.ext hki
    rw [e, ← ha ⟨i, hi⟩, ← hb ⟨i, hi⟩]
  · rw [read64_write64_sep m _ (memSep_cells po k.val i n k.isLt hi hn hki)]
    exact ho k (by omega)

end CatCrypt.Crypto.SecureCompilation.MachineMem64
