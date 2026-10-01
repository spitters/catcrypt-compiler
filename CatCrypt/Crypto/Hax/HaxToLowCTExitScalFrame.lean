/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.LowCTExec

/-!
# The exit frame of a body without an early return

The typed exit front wraps a function body `K` in the frame

```
RLetU64Zero r (RLetU64Zero s (RSeq K (RIfNz r t RSkip)))
```

with the return flag `r`, the result slot `s` and the early-return tail `t`, which copies the
early-return value into `s`. When `K` leaves `r` unwritten (`scalarKeepsB r K`), the flag is
zero at the test and the tail never runs; `exitScalFrameNorm` drops the test, so that the
program reads no name the tail reads. A run of the frame gives a run of the normalised
program to the same state (`exitScalFrameNorm_run`).

The A-normal form of the front binds a literal operand to a word,
`RLetU64Zero t (RSeq (RScalarSet t k) rest)`. When `rest` leaves `t` unwritten, `litProp`
writes the literal `k` in place of `t` in the scalar expressions of `rest` (`substLitC`), so
that, for example, a shift by a literal count is a shift by an immediate. A run of a program
is a run of its propagated form to the same state (`litProp_run`).

A word binder whose word the program never reads is dead, with its writes (`deadElim`, outside
the result words `isResName`); a word binder whose body reads no word before writing it is a
dead initialisation (`dropInit`). The back end removes such code, and the straight-line check
compares the flag machine with the machine instruction by instruction, so the front removes it
first. A run of the program gives a run of the result to a state that agrees with it on the
tower slots and the result words (`ResAgree`). `exitScalPrep` is the frame normalisation, the
propagation, the dead-word elimination and the dead-initialisation removal.

## Main results

* `scalarKeepsB`, `rustExec_scalarKeeps` — the scalar frame of a run: a command that writes no
  scalar `s` leaves it unchanged.
* `exitScalFrameNorm`, `exitScalFrameNorm_run` — the frame without its flag test, and its
  runs.
* `substLitE`, `evalState_substLitE`, `substLitC`, `substLitC_run` — a literal in place of a
  word that holds it.
* `rFor_map` — a map on trip bodies keeping their runs keeps the runs of a counted loop.
* `litLet`, `litProp`, `litProp_run` — the propagation of the literal bindings, in loops and
  under tower binders and branches as well.
* `noReadE`, `noReadC`, `writesX`, `AgreeOff`, `sim_off1`, `killK`, `killK_sim` — runs from
  states agreeing off words the program never reads.
* `isResName`, `ResAgree`, `deadElim`, `deadElim_run`, `dropInit`, `dropInit_run` — the dead
  words and dead initialisations.
* `exitScalPrep`, `exitScalPrep_run` — the normalisation the word scalarisation reads.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Crypto.Jasmin.LowCT

variable {N : Nat} {L : LeafSpec}

/-- The command leaves the scalar `s` unwritten: no scalar write, word binder or loop index
    names `s`, and no command outside those listed. -/
def scalarKeepsB (s : String) : LowCT → Bool
  | .RSkip => true
  | .RSeq a b => scalarKeepsB s a && scalarKeepsB s b
  | .RLetU64Zero x b => x != s && scalarKeepsB s b
  | .RLetZero _ _ b => scalarKeepsB s b
  | .RScalarSet x _ => x != s
  | .RScalarSetExpr x _ => x != s
  | .RIfNz _ a b => scalarKeepsB s a && scalarKeepsB s b
  | .RArrLoad _ _ _ => true
  | .RArrStore _ _ _ => true
  | .RLimbStoreExpr _ _ _ => true
  | .RCopy _ _ => true
  | .RFor x _ b => x != s && scalarKeepsB s b
  | .RForRuntime x _ b => x != s && scalarKeepsB s b
  | .RCall _ _ _ => true
  | _ => false

/-- **Scalar frame.** A run of a command that `scalarKeepsB s` accepts leaves the scalar `s`
    unchanged. -/
theorem rustExec_scalarKeeps {s : String} {c : LowCT} {rs rs' : RustState}
    (h : RustExec N L c rs rs') (hk : scalarKeepsB s c = true) :
    rs'.rsScalar s = rs.rsScalar s := by
  induction h with
  | skip => rfl
  | seq _ _ _ _ _ _ _ ih1 ih2 =>
      simp only [scalarKeepsB, Bool.and_eq_true] at hk
      rw [ih2 hk.2, ih1 hk.1]
  | letZero _ _ _ _ _ _ ih =>
      exact ih hk
  | letU64Zero x _ _ _ _ ih =>
      simp only [scalarKeepsB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
      rw [ih hk.2]
      simp [rsSetScalar, Ne.symm hk.1]
  | scalarSet x _ _ =>
      simp only [scalarKeepsB, bne_iff_ne, ne_eq] at hk
      simp [rsSetScalar, Ne.symm hk]
  | ifTrue _ _ _ _ _ _ _ _ _ ih =>
      simp only [scalarKeepsB, Bool.and_eq_true] at hk
      exact ih hk.1
  | ifFalse _ _ _ _ _ _ _ ih =>
      simp only [scalarKeepsB, Bool.and_eq_true] at hk
      exact ih hk.2
  | forZero => rfl
  | forSucc x _ _ _ _ _ _ _ ih1 ih2 =>
      simp only [scalarKeepsB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
      rw [ih2 hk.2, ← ih1 (by simp [scalarKeepsB, hk.1, hk.2])]
      simp [rsSetScalar, Ne.symm hk.1]
  | forRuntime _ _ _ _ _ _ ih =>
      simp only [scalarKeepsB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
      exact ih (by simp [scalarKeepsB, hk.1, hk.2])
  | scalarSetExpr x _ _ =>
      simp only [scalarKeepsB, bne_iff_ne, ne_eq] at hk
      simp [rsSetScalar, Ne.symm hk]
  | limbStoreExpr => rfl
  | arrStore => rfl
  | arrLoad => rfl
  | copy => rfl
  | call => rfl
  | _ => simp [scalarKeepsB] at hk

/-- **The exit frame of a body without an early return, normalised.** On a frame
    `RLetU64Zero r (RLetU64Zero s (RSeq K (RIfNz r t RSkip)))` whose body `K` leaves the flag
    `r` unwritten, the frame without the flag test, `RLetU64Zero r (RLetU64Zero s K)`; every
    other command unchanged. -/
def exitScalFrameNorm : LowCT → LowCT
  | .RLetU64Zero r (.RLetU64Zero s (.RSeq K (.RIfNz r' t .RSkip))) =>
      if r' = r ∧ scalarKeepsB r K = true then .RLetU64Zero r (.RLetU64Zero s K)
      else .RLetU64Zero r (.RLetU64Zero s (.RSeq K (.RIfNz r' t .RSkip)))
  | c => c

/-- **The normalised frame keeps its runs.** A run of `c` is a run of `exitScalFrameNorm c`
    between the same states. -/
theorem exitScalFrameNorm_run {c : LowCT} {rs rs' : RustState} (h : RustExec N L c rs rs') :
    RustExec N L (exitScalFrameNorm c) rs rs' := by
  unfold exitScalFrameNorm
  split
  · rename_i r s K r' t
    split
    · rename_i hc
      obtain ⟨rfl, hk⟩ := hc
      cases h with
      | letU64Zero _ _ _ _ h =>
      cases h with
      | letU64Zero _ _ _ _ h =>
      cases h with
      | seq _ _ _ rK _ hK hF =>
      have h0 : rK.rsScalar r' = 0 := by
        rw [rustExec_scalarKeeps hK hk]
        by_cases hs : s = r' <;> simp [rsSetScalar, hs]
      cases hF with
      | ifTrue _ _ _ _ _ v hv hv0 _ => exact absurd (hv ▸ h0) hv0
      | ifFalse _ _ _ _ _ _ hF =>
          cases hF
          exact .letU64Zero _ _ _ _ (.letU64Zero _ _ _ _ hK)
    · exact h
  · exact h

/-! ## Literal propagation -/

/-- The expression with the literal `k` in place of every read of the word `t`. -/
def substLitE (t : String) (k : Nat) : SExpr → SExpr
  | .SVar x => if x = t then .SLit k else .SVar x
  | .SAdd a b => .SAdd (substLitE t k a) (substLitE t k b)
  | .SSub a b => .SSub (substLitE t k a) (substLitE t k b)
  | .SMul a b => .SMul (substLitE t k a) (substLitE t k b)
  | .SShr a b => .SShr (substLitE t k a) (substLitE t k b)
  | .SShl a b => .SShl (substLitE t k a) (substLitE t k b)
  | .SAnd a b => .SAnd (substLitE t k a) (substLitE t k b)
  | .SXor a b => .SXor (substLitE t k a) (substLitE t k b)
  | .SLt a b => .SLt (substLitE t k a) (substLitE t k b)
  | .SAsr a b => .SAsr (substLitE t k a) (substLitE t k b)
  | .SMulS a b => .SMulS (substLitE t k a) (substLitE t k b)
  | .SMulHiU a b => .SMulHiU (substLitE t k a) (substLitE t k b)
  | .SMulHiS a b => .SMulHiS (substLitE t k a) (substLitE t k b)
  | e => e

/-- At a state whose word `t` holds `k`, the substituted expression has the value of the
    expression. -/
theorem evalState_substLitE {t : String} {k : Nat} {rs : RustState} (h : rs.rsScalar t = k) :
    ∀ e : SExpr, (substLitE t k e).evalState rs = e.evalState rs := by
  intro e
  induction e with
  | SVar x =>
      simp only [substLitE]
      split
      · rename_i hx; subst hx; exact h.symm
      · rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SShr a b iha ihb
  | SShl a b iha ihb | SAnd a b iha ihb | SXor a b iha ihb | SLt a b iha ihb
  | SAsr a b iha ihb | SMulS a b iha ihb | SMulHiU a b iha ihb | SMulHiS a b iha ihb =>
      simp only [substLitE, SExpr.evalState, iha, ihb]
  | _ => rfl

/-- The command with the literal `k` in place of the word `t` in the scalar expressions of its
    sequences, word and tower binders, branches, counted and runtime-count loops (the bound of
    a runtime-count loop included), scalar writes and limb stores; every other command
    unchanged. -/
def substLitC (t : String) (k : Nat) : LowCT → LowCT
  | .RSeq a b => .RSeq (substLitC t k a) (substLitC t k b)
  | .RLetU64Zero x b => .RLetU64Zero x (substLitC t k b)
  | .RLetZero x ty b => .RLetZero x ty (substLitC t k b)
  | .RIfNz g a b => .RIfNz g (substLitC t k a) (substLitC t k b)
  | .RFor x n b => .RFor x n (substLitC t k b)
  | .RForRuntime x bd b => .RForRuntime x (substLitE t k bd) (substLitC t k b)
  | .RScalarSetExpr x e => .RScalarSetExpr x (substLitE t k e)
  | .RLimbStoreExpr l i e => .RLimbStoreExpr l i (substLitE t k e)
  | c => c

/-- A map on trip bodies that keeps their runs keeps the runs of a counted loop. -/
theorem rFor_map {x : String} {b b' : LowCT} {P : RustState → Prop}
    (hP : ∀ (n : Nat) {rs r : RustState}, RustExec N L (.RFor x n b) rs r → P rs →
      P (rsSetScalar r x n))
    (hb : ∀ {rs rs' : RustState}, RustExec N L b rs rs' → P rs → RustExec N L b' rs rs') :
    ∀ (n : Nat) {rs rs' : RustState}, RustExec N L (.RFor x n b) rs rs' → P rs →
      RustExec N L (.RFor x n b') rs rs'
  | 0, _, _, h, _ => by cases h; exact .forZero _ _ _
  | n + 1, _, _, h, hp => by
      cases h with
      | forSucc _ _ _ _ r1 _ h1 h2 =>
          exact .forSucc _ _ _ _ _ _ (rFor_map hP hb n h1 hp) (hb h2 (hP n h1 hp))

/-- **A literal in place of the word that holds it.** A run of a command that leaves `t`
    unwritten, from a state whose word `t` holds `k`, is a run of `substLitC t k` between the
    same states. -/
theorem substLitC_run {t : String} {k : Nat} :
    ∀ (c : LowCT) {rs rs' : RustState}, RustExec N L c rs rs' → rs.rsScalar t = k →
      scalarKeepsB t c = true → RustExec N L (substLitC t k c) rs rs' := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro rs rs' h ht hk
      simp only [scalarKeepsB, Bool.and_eq_true] at hk
      cases h with
      | seq _ _ _ r1 _ h1 h2 =>
          exact .seq _ _ _ _ _ (iha h1 ht hk.1)
            (ihb h2 (by rw [rustExec_scalarKeeps h1 hk.1, ht]) hk.2)
  | RLetU64Zero x b ih =>
      intro rs rs' h ht hk
      simp only [scalarKeepsB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
      cases h with
      | letU64Zero _ _ _ _ hb =>
          exact .letU64Zero _ _ _ _ (ih hb (by simp [rsSetScalar, Ne.symm hk.1, ht]) hk.2)
  | RScalarSetExpr x e =>
      intro rs rs' h ht _
      cases h with
      | scalarSetExpr =>
          show RustExec N L (.RScalarSetExpr x (substLitE t k e)) rs _
          rw [← evalState_substLitE ht e]
          exact .scalarSetExpr _ _ _
  | RLetZero x ty b ih =>
      intro rs rs' h ht hk
      cases h with
      | letZero _ _ _ _ _ hb => exact .letZero _ _ _ _ _ (ih hb ht hk)
  | RIfNz g a b iha ihb =>
      intro rs rs' h ht hk
      simp only [scalarKeepsB, Bool.and_eq_true] at hk
      cases h with
      | ifTrue _ _ _ _ _ v hv hv0 h => exact .ifTrue _ _ _ _ _ v hv hv0 (iha h ht hk.1)
      | ifFalse _ _ _ _ _ hv h => exact .ifFalse _ _ _ _ _ hv (ihb h ht hk.2)
  | RFor x n b ih =>
      intro rs rs' h ht hk
      simp only [scalarKeepsB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
      refine rFor_map (P := fun r => r.rsScalar t = k) (fun m r r' hr hp => ?_)
        (fun h hp => ih h hp hk.2) n h ht
      rw [show (rsSetScalar r' x m).rsScalar t = r'.rsScalar t by simp [rsSetScalar, Ne.symm hk.1],
        rustExec_scalarKeeps hr (by simp [scalarKeepsB, hk.1, hk.2]), hp]
  | RForRuntime x bd b ih =>
      intro rs rs' h ht hk
      simp only [scalarKeepsB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
      cases h with
      | forRuntime _ _ _ _ _ h =>
          refine .forRuntime _ _ _ _ _ ?_
          rw [evalState_substLitE ht bd]
          refine rFor_map (P := fun r => r.rsScalar t = k) (fun m r r' hr hp => ?_)
            (fun h hp => ih h hp hk.2) _ h ht
          rw [show (rsSetScalar r' x m).rsScalar t = r'.rsScalar t by
              simp [rsSetScalar, Ne.symm hk.1],
            rustExec_scalarKeeps hr (by simp [scalarKeepsB, hk.1, hk.2]), hp]
  | RLimbStoreExpr l i e =>
      intro rs rs' h ht _
      cases h with
      | limbStoreExpr _ _ _ _ old hl =>
          show RustExec N L (.RLimbStoreExpr l i (substLitE t k e)) rs _
          rw [← evalState_substLitE ht e]
          exact .limbStoreExpr _ _ _ _ _ hl
  | _ => intro rs rs' h _ _; exact h

/-- The word binder `RLetU64Zero x b` with the literal of `b`'s leading write `x := k`
    propagated into the rest of `b`, when the rest leaves `x` unwritten; otherwise the binder
    unchanged. -/
def litLet (x : String) (b : LowCT) : LowCT :=
  match b with
  | .RSeq (.RScalarSet t k) rest =>
      if t = x ∧ scalarKeepsB x rest = true then
        .RLetU64Zero x (.RSeq (.RScalarSet x k) (substLitC x k rest))
      else .RLetU64Zero x b
  | _ => .RLetU64Zero x b

theorem litLet_run {x : String} {b : LowCT} {rs rs' : RustState}
    (h : RustExec N L (.RLetU64Zero x b) rs rs') : RustExec N L (litLet x b) rs rs' := by
  unfold litLet
  split
  · rename_i t k rest
    split
    · rename_i hc
      obtain ⟨rfl, hk⟩ := hc
      cases h with
      | letU64Zero _ _ _ _ h =>
      cases h with
      | seq _ _ _ r1 _ h1 h2 =>
      cases h1
      exact .letU64Zero _ _ _ _ (.seq _ _ _ _ _ (.scalarSet _ _ _)
        (substLitC_run rest h2 (by simp [rsSetScalar]) hk))
    · exact h
  · exact h

/-- **Literal propagation** at the word binders (`litLet`) of sequences, word and tower binders,
    branches, counted and runtime-count loops. -/
def litProp : LowCT → LowCT
  | .RSeq a b => .RSeq (litProp a) (litProp b)
  | .RLetU64Zero x b => litLet x (litProp b)
  | .RLetZero x ty b => .RLetZero x ty (litProp b)
  | .RIfNz g a b => .RIfNz g (litProp a) (litProp b)
  | .RFor x n b => .RFor x n (litProp b)
  | .RForRuntime x bd b => .RForRuntime x bd (litProp b)
  | c => c

/-- **The propagated program keeps its runs.** -/
theorem litProp_run : ∀ (c : LowCT) {rs rs' : RustState}, RustExec N L c rs rs' →
    RustExec N L (litProp c) rs rs' := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro rs rs' h
      cases h with
      | seq _ _ _ r1 _ h1 h2 => exact .seq _ _ _ _ _ (iha h1) (ihb h2)
  | RLetU64Zero x b ih =>
      intro rs rs' h
      cases h with
      | letU64Zero _ _ _ _ hb => exact litLet_run (.letU64Zero _ _ _ _ (ih hb))
  | RLetZero x ty b ih =>
      intro rs rs' h
      cases h with
      | letZero _ _ _ _ _ hb => exact .letZero _ _ _ _ _ (ih hb)
  | RIfNz g a b iha ihb =>
      intro rs rs' h
      cases h with
      | ifTrue _ _ _ _ _ v hv hv0 h => exact .ifTrue _ _ _ _ _ v hv hv0 (iha h)
      | ifFalse _ _ _ _ _ hv h => exact .ifFalse _ _ _ _ _ hv (ihb h)
  | RFor x n b ih =>
      intro rs rs' h
      exact rFor_map (P := fun _ => True) (fun _ _ _ _ _ => trivial) (fun h _ => ih h) n h trivial
  | RForRuntime x bd b ih =>
      intro rs rs' h
      cases h with
      | forRuntime _ _ _ _ _ h =>
          exact .forRuntime _ _ _ _ _
            (rFor_map (P := fun _ => True) (fun _ _ _ _ _ => trivial) (fun h _ => ih h) _ h trivial)
  | _ => intro rs rs' h; exact h

/-! ## Dead words -/

/-- The expression reads no word of `K`. -/
def noReadE (K : List String) : SExpr → Bool
  | .SVar y => !K.contains y
  | .SAdd a b | .SSub a b | .SMul a b | .SShr a b | .SShl a b | .SAnd a b | .SXor a b
  | .SLt a b | .SAsr a b | .SMulS a b | .SMulHiU a b | .SMulHiS a b => noReadE K a && noReadE K b
  | _ => true

/-- Two states agree off the words `K`: equal tower slots, equal words outside `K`. -/
def AgreeOff (K : List String) (r1 r2 : RustState) : Prop :=
  r1.rsTower = r2.rsTower ∧ ∀ y, y ∉ K → r1.rsScalar y = r2.rsScalar y

theorem evalState_congr_agreeOff {K : List String} {rs1 rs2 : RustState} (h : AgreeOff K rs1 rs2) :
    ∀ e : SExpr, noReadE K e = true → e.evalState rs1 = e.evalState rs2 := by
  intro e
  induction e with
  | SVar y =>
      intro hy
      simp only [noReadE, Bool.not_eq_true'] at hy
      exact h.2 y (fun hm => by rw [List.contains_iff_mem.mpr hm] at hy; cases hy)
  | SLit n => intro _; rfl
  | SLimb v i => intro _; simp only [SExpr.evalState, rsTowerLimb, h.1]
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SShr a b iha ihb
  | SShl a b iha ihb | SAnd a b iha ihb | SXor a b iha ihb | SLt a b iha ihb
  | SAsr a b iha ihb | SMulS a b iha ihb | SMulHiU a b iha ihb | SMulHiS a b iha ihb =>
      intro hab
      simp only [noReadE, Bool.and_eq_true] at hab
      simp only [SExpr.evalState, iha hab.1, ihb hab.2]

/-- The command is built from skips, sequences, word binders and scalar writes, and reads no
    word of `K`. -/
def noReadC (K : List String) : LowCT → Bool
  | .RSkip => true
  | .RSeq a b => noReadC K a && noReadC K b
  | .RLetU64Zero _ b => noReadC K b
  | .RScalarSet _ _ => true
  | .RScalarSetExpr _ e => noReadE K e
  | _ => false

/-- The command writes the word `x` on its spine, outside a binder of `x`. -/
def writesX (x : String) : LowCT → Bool
  | .RSeq a b => writesX x a || writesX x b
  | .RLetU64Zero y b => y != x && writesX x b
  | .RScalarSet y _ => y == x
  | .RScalarSetExpr y _ => y == x
  | _ => false

theorem agreeOff_set {K : List String} {r1 r2 : RustState} (h : AgreeOff K r1 r2) (y : String)
    (v : Nat) : AgreeOff K (rsSetScalar r1 y v) (rsSetScalar r2 y v) :=
  ⟨h.1, fun z hz => by simp only [rsSetScalar]; split <;> [rfl; exact h.2 z hz]⟩

theorem agreeOff_set_mem {K : List String} {r1 r2 : RustState} (h : AgreeOff K r1 r2)
    {y : String} (hy : y ∈ K) (v : Nat) : AgreeOff K (rsSetScalar r1 y v) r2 :=
  ⟨h.1, fun z hz => by
    simp only [rsSetScalar]
    split
    · rename_i he; rw [beq_iff_eq] at he; subst he; exact absurd hy hz
    · exact h.2 z hz⟩

theorem agreeOff_refl (K : List String) (r : RustState) : AgreeOff K r r := ⟨rfl, fun _ _ => rfl⟩

theorem eq_of_agreeOff_set {x : String} {r1 r2 : RustState} (h : AgreeOff [x] r1 r2) (v : Nat) :
    rsSetScalar r1 x v = rsSetScalar r2 x v := by
  obtain ⟨t1, s1⟩ := r1
  obtain ⟨t2, s2⟩ := r2
  obtain ⟨ht, hs⟩ := h
  simp only at ht
  subst ht
  simp only [rsSetScalar, RustState.mk.injEq, true_and]
  funext z
  split
  · rfl
  · rename_i hz
    exact hs z (by simpa using hz)

/-- **A command that reads no `x`** runs from two states agreeing off `x` to states agreeing
    off `x`, equal when it writes `x` on its spine. -/
theorem sim_off1 {x : String} : ∀ (c : LowCT), noReadC [x] c = true →
    ∀ {rs1 r1 rs2 : RustState}, RustExec N L c rs1 r1 → AgreeOff [x] rs1 rs2 →
      ∃ r2, RustExec N L c rs2 r2 ∧ AgreeOff [x] r1 r2 ∧ (writesX x c = true → r1 = r2) := by
  intro c
  induction c with
  | RSkip =>
      intro _ rs1 r1 rs2 h hag
      cases h
      exact ⟨rs2, .skip _, hag, by simp [writesX]⟩
  | RSeq a b iha ihb =>
      intro hn rs1 r1 rs2 h hag
      simp only [noReadC, Bool.and_eq_true] at hn
      cases h with
      | seq _ _ _ m1 _ h1 h2 =>
        obtain ⟨m2, h1', hag1, hw1⟩ := iha hn.1 h1 hag
        by_cases hwa : writesX x a = true
        · obtain rfl := hw1 hwa
          exact ⟨r1, .seq _ _ _ _ _ h1' h2, agreeOff_refl _ _, fun _ => rfl⟩
        · obtain ⟨r2, h2', hag2, hw2⟩ := ihb hn.2 h2 hag1
          refine ⟨r2, .seq _ _ _ _ _ h1' h2', hag2, fun hw => hw2 ?_⟩
          simpa [writesX, hwa] using hw
  | RLetU64Zero y b ih =>
      intro hn rs1 r1 rs2 h hag
      simp only [noReadC] at hn
      cases h with
      | letU64Zero _ _ _ _ hb =>
        by_cases hy : y = x
        · subst hy
          rw [eq_of_agreeOff_set hag 0] at hb
          exact ⟨r1, .letU64Zero _ _ _ _ hb, agreeOff_refl _ _, fun _ => rfl⟩
        · obtain ⟨r2, hb', hag2, hw2⟩ := ih hn hb (agreeOff_set hag y 0)
          refine ⟨r2, .letU64Zero _ _ _ _ hb', hag2, fun hw => hw2 ?_⟩
          simpa [writesX, hy] using hw
  | RScalarSet y n =>
      intro _ rs1 r1 rs2 h hag
      cases h
      by_cases hy : y = x
      · subst hy
        exact ⟨_, .scalarSet _ _ _, by rw [eq_of_agreeOff_set hag n]; exact agreeOff_refl _ _,
          fun _ => eq_of_agreeOff_set hag n⟩
      · exact ⟨_, .scalarSet _ _ _, agreeOff_set hag y n, by simp [writesX, hy]⟩
  | RScalarSetExpr y e =>
      intro hn rs1 r1 rs2 h hag
      simp only [noReadC] at hn
      cases h
      rw [evalState_congr_agreeOff hag e hn]
      by_cases hy : y = x
      · subst hy
        exact ⟨_, .scalarSetExpr _ _ _, by rw [eq_of_agreeOff_set hag]; exact agreeOff_refl _ _,
          fun _ => eq_of_agreeOff_set hag _⟩
      · exact ⟨_, .scalarSetExpr _ _ _, agreeOff_set hag y _, by simp [writesX, hy]⟩
  | _ => intro hn; simp [noReadC] at hn

/-- The command reads no word of `K`: no expression, branch guard or element index names a word
    of `K`, over sequences, word and tower binders, branches, counted and runtime-count loops,
    scalar writes, limb stores, element loads and stores, calls and copies. -/
def readsNoneB (K : List String) : LowCT → Bool
  | .RSkip => true
  | .RSeq a b => readsNoneB K a && readsNoneB K b
  | .RLetU64Zero _ b => readsNoneB K b
  | .RLetZero _ _ b => readsNoneB K b
  | .RScalarSet _ _ => true
  | .RScalarSetExpr _ e => noReadE K e
  | .RLimbStoreExpr _ _ e => noReadE K e
  | .RIfNz g a b => !K.contains g && readsNoneB K a && readsNoneB K b
  | .RFor _ _ b => readsNoneB K b
  | .RForRuntime _ bd b => noReadE K bd && readsNoneB K b
  | .RArrLoad _ _ i => !K.contains i
  | .RArrStore _ i _ => !K.contains i
  | .RCall _ _ _ => true
  | .RCopy _ _ => true
  | _ => false

theorem locatedLookup_congr {r1 r2 : RustState} (h : r1.rsTower = r2.rsTower) (l : Located) :
    locatedLookup r1 l = locatedLookup r2 l := by
  simp only [locatedLookup, h]

theorem agreeOff_setTower {K : List String} {r1 r2 : RustState} (h : AgreeOff K r1 r2)
    (y : String) (v : Σ t : TowerType, RustVal t) :
    AgreeOff K (rsSetTower r1 y v) (rsSetTower r2 y v) :=
  ⟨by simp only [rsSetTower, h.1], h.2⟩

/-- **A command that reads no word of `K` runs alike from states agreeing off `K`**: every run
    from the first state is matched by a run from the second, to states agreeing off `K`. -/
theorem readsNone_sim {K : List String} {c : LowCT} {rs1 r1 : RustState}
    (h : RustExec N L c rs1 r1) (hk : readsNoneB K c = true) :
    ∀ {rs2 : RustState}, AgreeOff K rs1 rs2 → ∃ r2, RustExec N L c rs2 r2 ∧ AgreeOff K r1 r2 := by
  induction h with
  | skip => intro rs2 hag; exact ⟨rs2, .skip _, hag⟩
  | seq _ _ _ _ _ _ _ ih1 ih2 =>
      intro rs2 hag
      simp only [readsNoneB, Bool.and_eq_true] at hk
      obtain ⟨m, hm, hag1⟩ := ih1 hk.1 hag
      obtain ⟨r2, hr2, hag2⟩ := ih2 hk.2 hag1
      exact ⟨r2, .seq _ _ _ _ _ hm hr2, hag2⟩
  | letZero x t _ _ _ _ ih =>
      intro rs2 hag
      obtain ⟨r2, hr2, hag2⟩ := ih hk (agreeOff_setTower hag x _)
      exact ⟨r2, .letZero _ _ _ _ _ hr2, hag2⟩
  | letU64Zero x _ _ _ _ ih =>
      intro rs2 hag
      obtain ⟨r2, hr2, hag2⟩ := ih hk (agreeOff_set hag x 0)
      exact ⟨r2, .letU64Zero _ _ _ _ hr2, hag2⟩
  | scalarSet x v _ =>
      intro rs2 hag
      exact ⟨_, .scalarSet _ _ _, agreeOff_set hag x v⟩
  | ifTrue g _ _ _ _ v hv hv0 _ ih =>
      intro rs2 hag
      simp only [readsNoneB, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not] at hk
      obtain ⟨r2, hr2, hag2⟩ := ih hk.1.2 hag
      exact ⟨r2, .ifTrue _ _ _ _ _ v (by rw [← hag.2 g hk.1.1]; exact hv) hv0 hr2, hag2⟩
  | ifFalse g _ _ _ _ hv _ ih =>
      intro rs2 hag
      simp only [readsNoneB, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not] at hk
      obtain ⟨r2, hr2, hag2⟩ := ih hk.2 hag
      exact ⟨r2, .ifFalse _ _ _ _ _ (by rw [← hag.2 g hk.1.1]; exact hv) hr2, hag2⟩
  | forZero => intro rs2 hag; exact ⟨rs2, .forZero _ _ _, hag⟩
  | forSucc x n _ _ _ _ _ _ ih1 ih2 =>
      intro rs2 hag
      obtain ⟨m, hm, hag1⟩ := ih1 hk hag
      obtain ⟨r2, hr2, hag2⟩ := ih2 hk (agreeOff_set hag1 x n)
      exact ⟨r2, .forSucc _ _ _ _ _ _ hm hr2, hag2⟩
  | forRuntime x bd _ _ _ _ ih =>
      intro rs2 hag
      simp only [readsNoneB, Bool.and_eq_true] at hk
      obtain ⟨r2, hr2, hag2⟩ := ih hk.2 hag
      refine ⟨r2, .forRuntime _ _ _ _ _ ?_, hag2⟩
      rw [← evalState_congr_agreeOff hag bd hk.1]
      exact hr2
  | call f d args _ old argList hlk hargs hty =>
      intro rs2 hag
      refine ⟨_, .call f d args rs2 old argList (by rw [← locatedLookup_congr hag.1]; exact hlk)
        (by rw [← hag.1]; exact hargs) (by rw [← hag.1]; exact hty), ?_⟩
      exact agreeOff_setTower hag _ _
  | limbStoreExpr l i e _ old hl =>
      intro rs2 hag
      refine ⟨_, .limbStoreExpr l i e rs2 old (by rw [← locatedLookup_congr hag.1]; exact hl), ?_⟩
      rw [← evalState_congr_agreeOff hag e hk]
      exact agreeOff_setTower hag _ _
  | arrStore arr i src _ idx old srcV hi ho hsrc =>
      intro rs2 hag
      simp only [readsNoneB, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not] at hk
      refine ⟨_, .arrStore arr i src rs2 idx old srcV (by rw [← hag.2 i hk]; exact hi)
        (by rw [← locatedLookup_congr hag.1]; exact ho)
        (by rw [← locatedLookup_congr hag.1]; exact hsrc), agreeOff_setTower hag _ _⟩
  | arrLoad d src i _ idx old srcV hi ho hsrc =>
      intro rs2 hag
      simp only [readsNoneB, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not] at hk
      refine ⟨_, .arrLoad d src i rs2 idx old srcV (by rw [← hag.2 i hk]; exact hi)
        (by rw [← locatedLookup_congr hag.1]; exact ho)
        (by rw [← locatedLookup_congr hag.1]; exact hsrc), agreeOff_setTower hag _ _⟩
  | scalarSetExpr x e _ =>
      intro rs2 hag
      refine ⟨_, .scalarSetExpr _ _ _, ?_⟩
      rw [evalState_congr_agreeOff hag e hk]
      exact agreeOff_set hag x _
  | copy d src _ hty srcV hl =>
      intro rs2 hag
      exact ⟨_, .copy d src rs2 hty srcV (by rw [← locatedLookup_congr hag.1]; exact hl),
        agreeOff_setTower hag _ _⟩
  | _ => simp [readsNoneB] at hk

/-- The command with the binders and the scalar writes of the words of `K` removed. -/
def killK (K : List String) : LowCT → LowCT
  | .RSeq a b => .RSeq (killK K a) (killK K b)
  | .RLetU64Zero y b => if K.contains y then killK K b else .RLetU64Zero y (killK K b)
  | .RScalarSet y n => if K.contains y then .RSkip else .RScalarSet y n
  | .RScalarSetExpr y e => if K.contains y then .RSkip else .RScalarSetExpr y e
  | c => c

/-- **Removing the words of `K` that the command never reads** keeps its runs up to the words of
    `K`. -/
theorem killK_sim {K : List String} : ∀ (c : LowCT), noReadC K c = true →
    ∀ {rs1 r1 rs2 : RustState}, RustExec N L c rs1 r1 → AgreeOff K rs1 rs2 →
      ∃ r2, RustExec N L (killK K c) rs2 r2 ∧ AgreeOff K r1 r2 := by
  intro c
  induction c with
  | RSkip =>
      intro _ rs1 r1 rs2 h hag
      cases h
      exact ⟨rs2, .skip _, hag⟩
  | RSeq a b iha ihb =>
      intro hn rs1 r1 rs2 h hag
      simp only [noReadC, Bool.and_eq_true] at hn
      cases h with
      | seq _ _ _ m1 _ h1 h2 =>
        obtain ⟨m2, h1', hag1⟩ := iha hn.1 h1 hag
        obtain ⟨r2, h2', hag2⟩ := ihb hn.2 h2 hag1
        exact ⟨r2, .seq _ _ _ _ _ h1' h2', hag2⟩
  | RLetU64Zero y b ih =>
      intro hn rs1 r1 rs2 h hag
      simp only [noReadC] at hn
      cases h with
      | letU64Zero _ _ _ _ hb =>
        by_cases hy : K.contains y = true
        · simp only [killK, hy, if_true]
          exact ih hn hb (agreeOff_set_mem hag (List.contains_iff_mem.mp hy) 0)
        · simp only [killK, hy, Bool.false_eq_true, if_false]
          obtain ⟨r2, hb', hag2⟩ := ih hn hb (agreeOff_set hag y 0)
          exact ⟨r2, .letU64Zero _ _ _ _ hb', hag2⟩
  | RScalarSet y n =>
      intro _ rs1 r1 rs2 h hag
      cases h
      by_cases hy : K.contains y = true
      · simp only [killK, hy, if_true]
        exact ⟨rs2, .skip _, agreeOff_set_mem hag (List.contains_iff_mem.mp hy) n⟩
      · simp only [killK, hy, Bool.false_eq_true, if_false]
        exact ⟨_, .scalarSet _ _ _, agreeOff_set hag y n⟩
  | RScalarSetExpr y e =>
      intro hn rs1 r1 rs2 h hag
      simp only [noReadC] at hn
      cases h
      by_cases hy : K.contains y = true
      · simp only [killK, hy, if_true]
        exact ⟨rs2, .skip _, agreeOff_set_mem hag (List.contains_iff_mem.mp hy) _⟩
      · simp only [killK, hy, Bool.false_eq_true, if_false]
        rw [evalState_congr_agreeOff hag e hn]
        exact ⟨_, .scalarSetExpr _ _ _, agreeOff_set hag y _⟩
  | _ => intro hn; simp [noReadC] at hn

/-- The word binders on the spine of sequences and word binders. -/
def binders : LowCT → List String
  | .RSeq a b => binders a ++ binders b
  | .RLetU64Zero y b => y :: binders b
  | _ => []

/-- The result words of the exit front: the scalar result slot `__exit_res` and the component
    slots `__exit_rc…`. -/
def isResName (y : String) : Bool :=
  y == "__exit_res" || y.toList.take 9 == "__exit_rc".toList

/-- Two states agree on the tower slots and the result words. -/
def ResAgree (r1 r2 : RustState) : Prop :=
  r1.rsTower = r2.rsTower ∧ ∀ y, isResName y = true → r1.rsScalar y = r2.rsScalar y

/-- The binders of the spine other than the result words. -/
def deadNames (c : LowCT) : List String := (binders c).filter fun y => !isResName y

/-- **Dead-word elimination.** When the command reads none of its bound words other than the
    result words, those binders and their writes removed (`killK`); otherwise the command. -/
def deadElim (c : LowCT) : LowCT :=
  if noReadC (deadNames c) c then killK (deadNames c) c else c

theorem deadElim_run {c : LowCT} {rs r : RustState} (h : RustExec N L c rs r) :
    ∃ r', RustExec N L (deadElim c) rs r' ∧ ResAgree r r' := by
  unfold deadElim
  split
  · rename_i hn
    obtain ⟨r', h', hag⟩ := killK_sim c hn h (agreeOff_refl _ rs)
    refine ⟨r', h', hag.1, fun y hy => hag.2 y (fun hm => ?_)⟩
    simp only [deadNames, List.mem_filter, hy, Bool.not_true, Bool.false_eq_true,
      and_false] at hm
  · exact ⟨r, h, rfl, fun _ _ => rfl⟩

/-- **Dead initialisation.** A word binder `RLetU64Zero x b` whose body reads no `x` and writes
    `x` on its spine without the binder; along the spine. -/
def dropInit : LowCT → LowCT
  | .RSeq a b => .RSeq (dropInit a) (dropInit b)
  | .RLetU64Zero x b =>
      if noReadC [x] b && writesX x b then dropInit b else .RLetU64Zero x (dropInit b)
  | c => c

theorem dropInit_run : ∀ (c : LowCT) {rs r : RustState}, RustExec N L c rs r →
    RustExec N L (dropInit c) rs r := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro rs r h
      cases h with
      | seq _ _ _ m _ h1 h2 => exact .seq _ _ _ _ _ (iha h1) (ihb h2)
  | RLetU64Zero x b ih =>
      intro rs r h
      cases h with
      | letU64Zero _ _ _ _ hb =>
        simp only [dropInit]
        split
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          have hag : AgreeOff [x] (rsSetScalar rs x 0) rs :=
            agreeOff_set_mem (agreeOff_refl [x] rs) (List.mem_singleton_self x) 0
          obtain ⟨r2, hb', -, hw⟩ := sim_off1 b hc.1 hb hag
          rw [hw hc.2]
          exact ih hb'
        · exact .letU64Zero _ _ _ _ (ih hb)
  | _ => intro rs r h; exact h

/-- The normalisation the word scalarisation reads: the exit frame without its flag test
    (`exitScalFrameNorm`), literal propagation (`litProp`), dead-word elimination
    (`deadElim`) and dead initialisation (`dropInit`). -/
def exitScalPrep (c : LowCT) : LowCT := dropInit (deadElim (litProp (exitScalFrameNorm c)))

/-- **The normalised program keeps its runs** up to the dead words: a run of `c` gives a run of
    `exitScalPrep c` from the same state to a state that agrees with it on the tower slots and
    the result words. -/
theorem exitScalPrep_run {c : LowCT} {rs rs' : RustState} (h : RustExec N L c rs rs') :
    ∃ rs'', RustExec N L (exitScalPrep c) rs rs'' ∧ ResAgree rs' rs'' := by
  obtain ⟨r', h', hra⟩ := deadElim_run (litProp_run _ (exitScalFrameNorm_run h))
  exact ⟨r', dropInit_run _ h', hra⟩

end CatCrypt.Crypto.Hax
