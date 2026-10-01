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

## Main results

* `scalarKeepsB`, `rustExec_scalarKeeps` — the scalar frame of a run: a command that writes no
  scalar `s` leaves it unchanged.
* `exitScalFrameNorm`, `exitScalFrameNorm_run` — the frame without its flag test, and its
  runs.
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

end CatCrypt.Crypto.Hax
