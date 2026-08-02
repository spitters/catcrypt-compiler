/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockCorres

/-!
# `CorresJ` as a Hoare triple — joining ascend to the Hoare-logic style

The ascent's `CorresJ` (a forward simulation over `runBlock`) and the project's
Hoare-logic track (`Jasmin/BignumHoare.lean`'s `BignumTriple`) are two views of the
same machine-level reasoning. This module makes the join explicit: it defines the
`runBlock` analogue of `BignumTriple` and proves `CorresJ` **is** a family of such
Hoare triples.

`BignumHoare.BignumTriple P body Q := ∀ s s', P s → bignumStep body s s' → Q s'` is a
partial-correctness Hoare triple over the relational `bignumStep`. `runBlock` is
total, so its triple drops the `s'`-existential:

    RunBlockTriple P body Q := ∀ st, P st → Q (runBlock st body)

The Hoare algebra (consequence, sequencing, conjunction) is the same as
`BignumTriple`'s, re-proved over `runBlock`. `corresJ_iff_triple` closes the join:
`CorresJ SR P fa c` holds iff, for every abstract state `a` satisfying `P`, the
triple `{SR · a} c {SR · (fa a)}` holds — the forward simulation is exactly a
`fa`-indexed family of `runBlock` Hoare triples. So ascend's correspondence and the
Hoare-logic formalism are interchangeable at the machine level; a `CorresJ` leaf can
be read as a Hoare triple and composed with the triple rules, and vice versa.

A full join to `BignumHoare` itself (over `bignumStep`/`BignumState`, a distinct
machine) additionally needs the `runBlock ↔ bignumStep` semantics bridge — the same
`runBlock ↔ lsem` territory as `RunBlockLsemAgree`. This module supplies the
formalism-level half.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- **The `runBlock` Hoare triple.** From a `JState` satisfying the precondition `P`,
    running `body` under the total `runBlock` lands in a state satisfying `Q`. The
    `runBlock` analogue of `BignumHoare.BignumTriple` — total, so no `s'`-existential. -/
def RunBlockTriple (P : JState 64 → Prop) (body : List (JInstr 64))
    (Q : JState 64 → Prop) : Prop :=
  ∀ st, P st → Q (runBlock st body)

/-! ## The Hoare algebra (mirrors `BignumTriple`'s rules) -/

/-- Consequence: strengthen the precondition, weaken the postcondition. -/
theorem RunBlockTriple.consequence {P P' Q Q' : JState 64 → Prop}
    {body : List (JInstr 64)} (hpre : ∀ st, P' st → P st) (hpost : ∀ st, Q st → Q' st)
    (h : RunBlockTriple P body Q) : RunBlockTriple P' body Q' :=
  fun st hP' => hpost _ (h st (hpre st hP'))

/-- Sequencing: compose triples over concatenated blocks. -/
theorem RunBlockTriple.seq {P R Q : JState 64 → Prop} {b₁ b₂ : List (JInstr 64)}
    (h₁ : RunBlockTriple P b₁ R) (h₂ : RunBlockTriple R b₂ Q) :
    RunBlockTriple P (b₁ ++ b₂) Q := by
  intro st hP
  rw [runBlock_append]
  exact h₂ _ (h₁ st hP)

/-- Conjunction: a block satisfying two postconditions satisfies their conjunction. -/
theorem RunBlockTriple.conj {P₁ P₂ Q₁ Q₂ : JState 64 → Prop} {body : List (JInstr 64)}
    (h₁ : RunBlockTriple P₁ body Q₁) (h₂ : RunBlockTriple P₂ body Q₂) :
    RunBlockTriple (fun st => P₁ st ∧ P₂ st) body (fun st => Q₁ st ∧ Q₂ st) :=
  fun st hP => ⟨h₁ st hP.1, h₂ st hP.2⟩

/-! ## The join: `CorresJ` is a family of Hoare triples -/

/-- **`CorresJ` → Hoare triple.** A `CorresJ` correspondence yields, for each abstract
    state `a` satisfying `P`, the `runBlock` Hoare triple `{SR · a} c {SR · (fa a)}`. -/
theorem corresJ_toTriple {AState : Type} (SR : JState 64 → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : List (JInstr 64))
    (h : CorresJ SR P fa c) (a : AState) (ha : P a) :
    RunBlockTriple (fun st => SR st a) c (fun st => SR st (fa a)) :=
  fun st hst => h st a hst ha

/-- **Hoare triple → `CorresJ`.** If, for every `a` satisfying `P`, the triple
    `{SR · a} c {SR · (fa a)}` holds, then `CorresJ SR P fa c` holds. -/
theorem corresJ_ofTriple {AState : Type} (SR : JState 64 → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : List (JInstr 64))
    (h : ∀ a, P a → RunBlockTriple (fun st => SR st a) c (fun st => SR st (fa a))) :
    CorresJ SR P fa c :=
  fun st a hst ha => h a ha st hst

/-- **The join.** `CorresJ SR P fa c` holds iff it is the `fa`-indexed family of
    `runBlock` Hoare triples `{SR · a} c {SR · (fa a)}` (for `a` satisfying `P`). The
    ascent's forward simulation and the Hoare-logic formalism are the same statement. -/
theorem corresJ_iff_triple {AState : Type} (SR : JState 64 → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : List (JInstr 64)) :
    CorresJ SR P fa c
      ↔ ∀ a, P a → RunBlockTriple (fun st => SR st a) c (fun st => SR st (fa a)) :=
  ⟨fun h a ha => corresJ_toTriple SR P fa c h a ha, corresJ_ofTriple SR P fa c⟩

/-- The carry leaf `corresJ_sbb`, read as a `runBlock` Hoare triple: from `SRcarry`
    at `a`, the single `sbb` instruction lands in `SRcarry` at `sbbStep dst src a`.
    A concrete witness that an ascent leaf is a Hoare triple. -/
theorem sbb_as_triple (dst src : String) (a : ACarry) :
    RunBlockTriple (fun st => SRcarry st a) [.sbb dst (.reg src)]
      (fun st => SRcarry st (sbbStep dst src a)) :=
  corresJ_toTriple SRcarry (fun _ => True) (sbbStep dst src) _
    (corresJ_sbb dst src) a trivial

end CatCrypt.Crypto.SecureCompilation.Ascent
