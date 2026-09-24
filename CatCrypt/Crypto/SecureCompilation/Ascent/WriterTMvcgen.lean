/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockMvcgen


@[expose] public section
set_option autoImplicit false

/-!
# A writer / accumulating-log effect for `mvcgen`

`Std.Do`'s weakest-precondition metatheory ships `@[spec]`/`wp` lemmas for the four
standard transformers — `StateT`, `ReaderT`, `ExceptT`, `OptionT` — so `mvcgen`
walks computations built from them. It has **no** `WriterT`. This module gives
`mvcgen` a **writer effect** — an accumulating log — which is exactly the shape
leakage takes when it is *internalized*: the coPara interface channel, whose
`⊕`-growth accumulates observations, read as a monotone log the VC generator walks.

## Writer-as-state, no new `PostShape`

This module takes the writer-as-state route. A writer over a log monoid is a **write-only
state**: `tell` only ever *appends*, never reads. So

    WriterT W m  ≅  StateT W m      with   tell w = modify (· ++ w),

and the writer's weakest precondition is the **native `StateT` WP** — `PostShape`
`.arg W ps`, the same shape `mvcgen`'s `modify`/`bind`/`forM` `@[spec]` lemmas
already fire on. We take the simplest concrete log monoid, `W := List I` (a stream
of leakage events `I`), and `tell (i : I) = modify (· ++ [i])`. No new `PostShape`,
no new `wp` lemma: the accumulating log is a `StateM` and `mvcgen` walks it out of
the box.

The general **graded**-`PostShape` route — a writer whose WP tracks the emitted
monoid element as its own barrel rather than folding it into a state — is not
treated here; it is what one needs when the log must *not* be encoded as
state (e.g. a commutative or resource-graded accumulation).

## What is proved

* `tell_spec` — the `@[spec]` triple for `tell`: its precondition is the native
  `modify` weakest precondition (the post at the `++[i]`-appended log). `mvcgen`'s
  built-in `modify` handling discharges it; no custom `wp` lemma.
* `writerM_triple_iff` — the "log = write-only state" bridge: the `Std.Do` triple
  over a `WriterM` program whose postcondition mentions the **final accumulated
  log** is exactly the run-level statement `∀ log, P log → Q (prog.run log)`.
* `demo_log` / `demo_log_prefix` — a concrete program that does two `tell`s, with a
  triple pinning the final log to `[a, b]`, closed by **`mvcgen`**. This is the
  witness that leakage-as-accumulating-log is `mvcgen`-walkable.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Std.Do

/-! ## 1. The writer, encoded as a write-only state

`WriterM I` is the writer over the free-monoid log `List I` of leakage events `I`.
`tell` appends one event; because it only appends, the log is a *write-only* state
and `WriterM I = StateM (List I)`. -/

/-- **The writer monad** over an accumulating log of `I`-events, encoded as a
    write-only state `StateM (List I)`. -/
abbrev WriterM (I : Type) (α : Type) : Type := StateM (List I) α

/-- **`tell`** emits one leakage event, appending it to the accumulating log. This
    is the write-only-state encoding of the writer's `tell`: `modify (· ++ [i])`. -/
def tell {I : Type} (i : I) : WriterM I Unit :=
  modify (fun log => log ++ [i])

/-- The `PostShape` of `WriterM I = StateT (List I) Id`: a single log argument over
    the pure (no-throw) base — the **native `StateT` shape**, `.arg (List I) .pure`.
    The writer-as-state encoding introduces no new `PostShape`. -/
abbrev psW (I : Type) : PostShape := .arg (List I) .pure

/-! ## 2. The writer's WP is the native `StateT` WP -/

/-- **The `tell` `@[spec]` triple.** The Hoare triple for one `tell i`: its
    precondition is the native `modify` weakest precondition — the post evaluated
    at the `++[i]`-appended log. `mvcgen`'s built-in `modify`/`StateT` handling
    discharges it directly; `tell` needs no custom `wp` lemma. This is what makes
    `tell` `mvcgen`-walkable. -/
@[spec]
theorem tell_spec {I : Type} (i : I) (Q : PostCond Unit (psW I)) :
    Triple (tell i) (fun log => Q.1 () (log ++ [i])) Q := by
  unfold tell Triple
  mvcgen

/-! ## 3. The bridge: the `Std.Do` triple IS a statement about the final log

For the pure `WriterM = StateM (List I)`, the weakest precondition of a program at
a post that mentions the **final accumulated log** is exactly the post evaluated at
`prog.run`. So the `Std.Do` Hoare triple and the run-level statement coincide. -/

/-- **The write-only-state bridge.** The `Std.Do` weakest-precondition triple over a
    `WriterM` program — with a postcondition mentioning the final accumulated log —
    is equivalent to the run-level statement `∀ log, P log → Q (prog.run log)`.
    Forward evaluates the WP at a concrete initial log via the `StateM` adequacy
    lemma `StateM.of_wp_run_eq`; reverse is reflexivity of the `StateM` WP (the
    weakest precondition of a `StateM` program at a run-level post *is* the post at
    `prog.run`). This makes precise that the log is a write-only state. -/
theorem writerM_triple_iff {I α : Type} (P : List I → Prop)
    (Q : α → List I → Prop) (prog : WriterM I α) :
    (⦃fun log => ⌜P log⌝⦄ prog ⦃⇓ a log => ⌜Q a log⌝⦄) ↔
      (∀ log, P log → Q (prog.run log).1 (prog.run log).2) := by
  constructor
  · -- forward: evaluate the WP at the concrete initial log via adequacy.
    intro h log hP
    exact StateM.of_wp_run_eq (x := prog.run log) rfl (fun p => Q p.1 p.2)
      (fun _ => h log hP)
  · -- reverse: reflexivity of the `StateM` WP — `wp⟦prog⟧ post log` is definitionally
    -- `post.1 (prog.run log).1 (prog.run log).2`.
    intro h
    refine Triple.iff.mpr ?_
    simp only [SPred.entails_1]
    intro log hP
    exact h log hP

/-! ## 4. Demonstration: `mvcgen` walks an accumulating writer

A concrete `WriterM I` program that emits two events, and a triple pinning the
final log. `mvcgen [tell_spec]` walks the two `tell`s, threading the accumulating
log through the native `StateT` WP; the residual VC is the arithmetic of the log
fold. This is the witness that leakage-as-accumulating-log is `mvcgen`-walkable. -/

/-- A two-event writer program: emit `a`, then `b`. -/
def demoProg {I : Type} (a b : I) : WriterM I Unit := do
  tell a
  tell b

/-- **`mvcgen` walks the accumulating writer.** Starting from the empty log, the
    two-`tell` program `demoProg a b` ends with log `[a, b]`. `mvcgen [tell_spec]`
    fires the writer step spec twice, accumulating `[] ++ [a] ++ [b]`; the residual
    is closed by `simp`. This is the concrete proof that an accumulating leakage log
    is `mvcgen`-walkable. -/
theorem demo_log {I : Type} (a b : I) :
    ⦃fun log => ⌜log = []⌝⦄ demoProg a b ⦃⇓ _ log => ⌜log = [a, b]⌝⦄ := by
  unfold demoProg
  mvcgen [tell_spec]
  simp_all

/-- **`mvcgen` on the writer, started from an arbitrary log.** From any starting log
    `w`, `demoProg a b` ends with `w ++ [a, b]` — the writer *accumulates*
    onto whatever the incoming log was, rather than overwriting it. Same `mvcgen`
    walk; the residual is the append fold `(w ++ [a]) ++ [b] = w ++ [a, b]`. -/
theorem demo_log_accumulates {I : Type} (a b : I) (w : List I) :
    ⦃fun log => ⌜log = w⌝⦄ demoProg a b ⦃⇓ _ log => ⌜log = w ++ [a, b]⌝⦄ := by
  unfold demoProg
  mvcgen [tell_spec]
  simp_all

end CatCrypt.Crypto.SecureCompilation.Ascent
