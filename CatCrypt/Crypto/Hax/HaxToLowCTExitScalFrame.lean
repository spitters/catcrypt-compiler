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
is a run of its propagated form to the same state (`litProp_run`). `exitScalPrep` is the frame
normalisation followed by the propagation.

## Main results

* `scalarKeepsB`, `rustExec_scalarKeeps` — the scalar frame of a run: a command that writes no
  scalar `s` leaves it unchanged.
* `exitScalFrameNorm`, `exitScalFrameNorm_run` — the frame without its flag test, and its
  runs.
* `substLitE`, `evalState_substLitE`, `substLitC`, `substLitC_run` — a literal in place of a
  word that holds it.
* `litLet`, `litProp`, `litProp_run` — the propagation of the literal bindings of a spine.
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

/-- The normalisation the word scalarisation reads: the exit frame without its flag test
    (`exitScalFrameNorm`), then literal propagation (`litProp`). -/
def exitScalPrep (c : LowCT) : LowCT := litProp (exitScalFrameNorm c)

/-- **The normalised program keeps its runs.** -/
theorem exitScalPrep_run {c : LowCT} {rs rs' : RustState} (h : RustExec N L c rs rs') :
    RustExec N L (exitScalPrep c) rs rs' :=
  litProp_run _ (exitScalFrameNorm_run h)

end CatCrypt.Crypto.Hax
