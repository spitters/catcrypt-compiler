/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote

/-!
# The per-brick obligation in invariant-preserving form

`Secp256k1PointOpFrontDenote.BrickStep` quantifies over every `SEnvScalar` with
no entry condition, and is refutable: the bricks are carry-free only while each
half-limb is below `2 ^ 32`, and `feVal` is a plain `Σ 2 ^ (32 * k) * toNat` that
does not constrain them. Its docstring carries the counterexample.

Chaining bricks is what forces the repair to be non-local. `brickFold_scheduleEval`
feeds one brick's output environment to the next, so a per-brick statement is only
usable if each brick both *assumes* an entry condition and *re-establishes* it.

`BrickStepInv` is that statement, parametric in the entry predicate, and
`brickFold_scheduleEval_inv` / `jacDblSchedule_waist_value_inv` are the fold and
the schedule value tie over it. The predicate is a parameter rather than a fixed
definition so that the per-op value obligations — `Secp256k1FeMulBrickFrame`'s
`MulEntry` / `MulBrickValue` for the multiply, and the corresponding add and
subtract obligations — can be instantiated at whichever invariant they establish.

## Main results

* `BrickStepInv`: one brick at schedule names moves the readout by one
  `stepFOpG` **and** carries the entry predicate to its output environment.
* `brickFold_scheduleEval_inv`: the fold over a schedule, threading the predicate
  through every brick.
* `jacDblSchedule_waist_value_inv`, `jacAddSchedule_waist_value_inv`: the two
  point-operation schedules' waist values, on the entry predicate rather than on
  a false hypothesis.
* `brickFold_inv`, `jacDblSchedule_scope_inv`, `jacAddSchedule_scope_inv`: the
  entry predicate itself at the schedule's output environment, which a consumer
  of that environment needs alongside the value tie.
* `brickStepInv_of_brickStep`: any `BrickStep` gives `BrickStepInv` at the
  trivial predicate, so the earlier form is subsumed rather than contradicted.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpBrickInv

open CatCrypt.Crypto.Jasmin.LowCT (LowCT)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpCompositional
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote

/-- **The per-brick obligation, invariant-preserving.** On an environment
    satisfying `Inv`, one emitted brick whose three field-element names are
    schedule names moves every schedule field element's readout by exactly one
    `stepFOpG`, and its output environment again satisfies `Inv`. The second
    conjunct is what lets the fold chain bricks; the `FOpSchedOkB` hypothesis is
    the one `brickFold_scheduleEval_inv` already carries for the whole schedule,
    and it separates the operands from the brick's own temporaries. -/
def BrickStepInv (Inv : SEnvScalar → Prop) : Prop :=
  ∀ (i : Nat) (op : FOp) (env env' : SEnvScalar),
    FOpSchedOkB op = true →
    Inv env →
    semScalar (seqAll (emitFOp i op)) env = some env' →
    (∀ fe : String, schedNameB fe = true →
        feVal env' fe = stepFOpG fm fa fs (feVal env) op fe)
      ∧ Inv env'

/-- The unconditional form gives the invariant-preserving form at the trivial
    predicate: `BrickStep` is the `Inv := fun _ => True` instance. -/
theorem brickStepInv_of_brickStep (hB : BrickStep) :
    BrickStepInv (fun _ => True) := by
  intro i op env env' _ _ hsem
  exact ⟨hB i op env env' hsem, trivial⟩

/-- **The entry predicate survives the whole schedule.** `BrickStepInv`
    re-establishes `Inv` at every brick, so the fold carries it to the output
    environment. This is the conjunct a consumer of the schedule's output needs
    — the epilogue's store block reads the half-limb slots and so wants the
    scope, not only the value tie. -/
theorem brickFold_inv {Inv : SEnvScalar → Prop} (hB : BrickStepInv Inv) :
    ∀ (ops : List FOp) (ls : List (List LowCT)),
      List.Forall₂ (fun op l => ∃ i, l = emitFOp i op) ops ls →
      (∀ op ∈ ops, FOpSchedOkB op = true) →
      ∀ (env env' : SEnvScalar),
        Inv env →
        semScalar (seqAll ls.flatten) env = some env' →
        Inv env' := by
  intro ops
  induction ops with
  | nil =>
      intro ls hf _ env env' hInv hsem
      cases hf
      simp only [List.flatten_nil] at hsem
      obtain rfl : env' = env := (Option.some.inj hsem).symm
      exact hInv
  | cons op ops ih =>
      intro ls hf hops env env' hInv hsem
      cases hf with
      | cons hl hrest =>
          rename_i l ls'
          obtain ⟨i, rfl⟩ := hl
          rw [List.flatten_cons, semScalar_seqAll_append] at hsem
          cases he : semScalar (seqAll (emitFOp i op)) env with
          | none => rw [he] at hsem; simp at hsem
          | some e1 =>
              rw [he] at hsem
              simp only [Option.bind_some] at hsem
              obtain ⟨-, hInv1⟩ := hB i op env e1 (hops op (.head _)) hInv he
              exact ih ls' hrest (fun o ho => hops o (.tail _ ho)) e1 env' hInv1 hsem

/-- **The brick fold, over an entry predicate.** Mirrors
    `brickFold_scheduleEval`, threading `Inv` through each brick: the head brick
    consumes it and re-establishes it for the tail. -/
theorem brickFold_scheduleEval_inv {Inv : SEnvScalar → Prop}
    (hB : BrickStepInv Inv) :
    ∀ (ops : List FOp) (ls : List (List LowCT)),
      List.Forall₂ (fun op l => ∃ i, l = emitFOp i op) ops ls →
      (∀ op ∈ ops, FOpSchedOkB op = true) →
      ∀ (env env' : SEnvScalar),
        Inv env →
        semScalar (seqAll ls.flatten) env = some env' →
        ∀ fe, schedNameB fe = true →
          feVal env' fe = scheduleEvalG fm fa fs ops (feVal env) fe := by
  intro ops
  induction ops with
  | nil =>
      intro ls hf _ env env' _ hsem fe _
      cases hf
      simp only [List.flatten_nil] at hsem
      obtain rfl : env' = env := (Option.some.inj hsem).symm
      rfl
  | cons op ops ih =>
      intro ls hf hops env env' hInv hsem fe hfe
      cases hf with
      | cons hl hrest =>
          rename_i l ls'
          obtain ⟨i, rfl⟩ := hl
          rw [List.flatten_cons, semScalar_seqAll_append] at hsem
          cases he : semScalar (seqAll (emitFOp i op)) env with
          | none => rw [he] at hsem; simp at hsem
          | some e1 =>
              rw [he] at hsem
              simp only [Option.bind_some] at hsem
              obtain ⟨hstep, hInv1⟩ := hB i op env e1 (hops op (.head _)) hInv he
              have hIH :=
                ih ls' hrest (fun o ho => hops o (.tail _ ho)) e1 env' hInv1 hsem fe hfe
              rw [hIH]
              exact scheduleEvalG_congr fm fa fs ops (feVal e1)
                (stepFOpG fm fa fs (feVal env) op)
                (fun o ho => hops o (.tail _ ho)) hstep fe hfe

/-- **The doubling schedule's waist value, on an entry predicate.** The statement
    `jacDblSchedule_waist_value` makes, with its false hypothesis replaced by
    `BrickStepInv` at a predicate the entry environment satisfies. -/
theorem jacDblSchedule_waist_value_inv {Inv : SEnvScalar → Prop}
    (hB : BrickStepInv Inv)
    (env env' : SEnvScalar) (X Y Z : Nat)
    (hInv : Inv env)
    (h0 : ∀ fe, schedNameB fe = true → feVal env fe = dblEnv0 X Y Z fe)
    (hSem : semScalar (seqAll (runSchedule jacDblSchedule)) env = some env') :
    (feVal env' "Xp", feVal env' "Yp", feVal env' "Zp") = jacDblSpec X Y Z := by
  have hok : ∀ op ∈ jacDblSchedule, FOpSchedOkB op = true := by decide
  have hfa := forall2_mapIdx jacDblSchedule (fun i op => emitFOp i op) (fun i op => ⟨i, rfl⟩)
  have key := brickFold_scheduleEval_inv hB jacDblSchedule _ hfa hok env env' hInv hSem
  have hcong : ∀ fe, schedNameB fe = true →
      scheduleEvalG fm fa fs jacDblSchedule (feVal env) fe
        = scheduleEval jacDblSchedule (dblEnv0 X Y Z) fe :=
    scheduleEvalG_congr fm fa fs jacDblSchedule (feVal env) (dblEnv0 X Y Z) hok h0
  have hXp : schedNameB "Xp" = true := by decide
  have hYp : schedNameB "Yp" = true := by decide
  have hZp : schedNameB "Zp" = true := by decide
  rw [key "Xp" hXp, key "Yp" hYp, key "Zp" hZp,
    hcong "Xp" hXp, hcong "Yp" hYp, hcong "Zp" hZp]
  exact jacDblSchedule_realizes_spec X Y Z

/-- **The addition schedule's waist value, on an entry predicate.** The
    `jacAddSchedule` counterpart of `jacDblSchedule_waist_value_inv`. -/
theorem jacAddSchedule_waist_value_inv {Inv : SEnvScalar → Prop}
    (hB : BrickStepInv Inv)
    (env env' : SEnvScalar) (X1 Y1 Z1 X2 Y2 Z2 : Nat)
    (hInv : Inv env)
    (h0 : ∀ fe, schedNameB fe = true → feVal env fe = addEnv0 X1 Y1 Z1 X2 Y2 Z2 fe)
    (hSem : semScalar (seqAll (runSchedule jacAddSchedule)) env = some env') :
    (feVal env' "Xp", feVal env' "Yp", feVal env' "Zp") = jacAddSpec X1 Y1 Z1 X2 Y2 Z2 := by
  have hok : ∀ op ∈ jacAddSchedule, FOpSchedOkB op = true := by decide
  have hfa := forall2_mapIdx jacAddSchedule (fun i op => emitFOp i op) (fun i op => ⟨i, rfl⟩)
  have key := brickFold_scheduleEval_inv hB jacAddSchedule _ hfa hok env env' hInv hSem
  have hcong : ∀ fe, schedNameB fe = true →
      scheduleEvalG fm fa fs jacAddSchedule (feVal env) fe
        = scheduleEval jacAddSchedule (addEnv0 X1 Y1 Z1 X2 Y2 Z2) fe :=
    scheduleEvalG_congr fm fa fs jacAddSchedule (feVal env)
      (addEnv0 X1 Y1 Z1 X2 Y2 Z2) hok h0
  have hXp : schedNameB "Xp" = true := by decide
  have hYp : schedNameB "Yp" = true := by decide
  have hZp : schedNameB "Zp" = true := by decide
  rw [key "Xp" hXp, key "Yp" hYp, key "Zp" hZp,
    hcong "Xp" hXp, hcong "Yp" hYp, hcong "Zp" hZp]
  exact jacAddSchedule_realizes_spec X1 Y1 Z1 X2 Y2 Z2

/-- **The entry predicate survives the doubling schedule.** The `brickFold_inv`
    instance at `jacDblSchedule`. -/
theorem jacDblSchedule_scope_inv {Inv : SEnvScalar → Prop} (hB : BrickStepInv Inv)
    (env env' : SEnvScalar) (hInv : Inv env)
    (hSem : semScalar (seqAll (runSchedule jacDblSchedule)) env = some env') :
    Inv env' := by
  have hok : ∀ op ∈ jacDblSchedule, FOpSchedOkB op = true := by decide
  have hfa := forall2_mapIdx jacDblSchedule (fun i op => emitFOp i op) (fun i op => ⟨i, rfl⟩)
  exact brickFold_inv hB jacDblSchedule _ hfa hok env env' hInv hSem

/-- **The entry predicate survives the addition schedule.** -/
theorem jacAddSchedule_scope_inv {Inv : SEnvScalar → Prop} (hB : BrickStepInv Inv)
    (env env' : SEnvScalar) (hInv : Inv env)
    (hSem : semScalar (seqAll (runSchedule jacAddSchedule)) env = some env') :
    Inv env' := by
  have hok : ∀ op ∈ jacAddSchedule, FOpSchedOkB op = true := by decide
  have hfa := forall2_mapIdx jacAddSchedule (fun i op => emitFOp i op) (fun i op => ⟨i, rfl⟩)
  exact brickFold_inv hB jacAddSchedule _ hfa hok env env' hInv hSem

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpBrickInv
