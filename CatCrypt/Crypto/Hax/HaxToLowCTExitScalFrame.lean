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
* `litLet`, `litProp`, `litProp_run` — the propagation of the literal bindings of a spine.
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
    sequences, word binders and scalar writes; every other command unchanged. -/
def substLitC (t : String) (k : Nat) : LowCT → LowCT
  | .RSeq a b => .RSeq (substLitC t k a) (substLitC t k b)
  | .RLetU64Zero x b => .RLetU64Zero x (substLitC t k b)
  | .RScalarSetExpr x e => .RScalarSetExpr x (substLitE t k e)
  | c => c

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

/-- **Literal propagation** along the spine of sequences and word binders (`litLet`). -/
def litProp : LowCT → LowCT
  | .RSeq a b => .RSeq (litProp a) (litProp b)
  | .RLetU64Zero x b => litLet x (litProp b)
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
