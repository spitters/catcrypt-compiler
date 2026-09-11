/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.CorresHoare
public import Mathlib.Data.Finset.Basic

/-!
# A first-order affine separation logic over `JState`, with a derived frame rule

This module builds the **separation logic for ascend**: an affine, points-to +
frame separation logic over the machine state `JState 64`, whose heap is the
register file (`JState.get`). It is first-order and *not* step-indexed — there is
no later modality, no guarded recursion, no bunched implication. The single
non-trivial content is the **frame rule**, derived from the ascent's existing
footprint lemmas (the "an op writes only its `dst`" seeds such as
`runBlock_lowerArith_id_other` and the `sbb`/store frames).

## The pieces

* **Footprint-scoped assertions.** `DependsOn L P` says the assertion `P` reads
  only the registers in the finite footprint `L`: it cannot distinguish two
  states that agree on `L`. Points-to `ptsTo r v` (written `r ↦ v`) is the atom,
  with footprint `{r}`.

* **Separating conjunction.** `sepConj P Q` is plain conjunction; the *separation*
  is carried by the footprints, not intrinsically by `∗`. `DependsOn.sepConj`
  shows footprints compose by **union** (`DependsOn (L₁ ∪ L₂) (P ∗ Q)`), which is
  the affine-heap reading of `∗`. The frame rule takes the footprints and a
  `Disjoint` hypothesis explicitly rather than making `∗` domain-tracking.

* **The frame rule.** `writesOnly L body` says `runBlock body` leaves every
  register outside `L` unchanged — this is exactly the shape of the ascent's
  `*_get_other` footprint seeds, and we discharge it for a concrete leaf from the
  machine semantics. Given a triple `{P} body {Q}`, a write-footprint `writesOnly
  Lw body`, a frame `DependsOn Lr R` disjoint from `Lw`, the framed triple
  `{P ∧ R} body {Q ∧ R}` holds: `writesOnly` + `DependsOn` preserve `R` across
  `runBlock`.

* **A framed leaf.** `sbb_framed_triple` frames the genuine carry leaf
  `sbb_as_triple` (from `CorresHoare`) with a points-to `r₀ ↦ v` on a disjoint
  register, showing local reasoning holds for a real machine block.

## Relationship to iris-lean

This is deliberately self-contained and does **not** connect to iris-lean's
bunched-implication (`BI`) structure. Embedding this affine SL into iris-lean's
`BI` (to reuse MoSeL's `∗`/`-∗`/`□` proof mode and its algebra) needs a
`JState ↔ Nat`-heap encoding — the register file as an Iris resource algebra /
heap camera — which is the further step; it is not attempted here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## Footprint-scoped assertions -/

/-- **The register footprint of an assertion.** `DependsOn L P` holds when `P`
    looks only at the registers named in the finite set `L`: any two states that
    agree on every register in `L` are indistinguishable to `P`. The footprint
    `L` is the read-set of the assertion — the separation-logic domain that a
    disjoint write may not touch. -/
def DependsOn (L : Finset String) (P : JState 64 → Prop) : Prop :=
  ∀ s s', (∀ r ∈ L, s.get r = s'.get r) → (P s ↔ P s')

/-- Enlarging the footprint is sound: an assertion that reads only `L` also reads
    only any `L' ⊇ L`. -/
theorem DependsOn.mono {L L' : Finset String} {P : JState 64 → Prop}
    (h : DependsOn L P) (hsub : L ⊆ L') : DependsOn L' P :=
  fun s s' hagree => h s s' (fun r hr => hagree r (hsub hr))

/-! ## Points-to and separating conjunction -/

/-- **Points-to.** `ptsTo r v` (`r ↦ v`) asserts register `r` holds `v`. Its
    footprint is the singleton `{r}`. -/
def ptsTo (r : String) (v : BitVec 64) : JState 64 → Prop := fun st => st.get r = v

@[inherit_doc] scoped notation:60 r " ↦ " v => ptsTo r v

/-- The points-to atom reads only its own register: `DependsOn {r} (r ↦ v)`. -/
theorem ptsTo_dependsOn (r : String) (v : BitVec 64) : DependsOn {r} (ptsTo r v) := by
  intro s s' h
  have hr : s.get r = s'.get r := h r (Finset.mem_singleton_self r)
  simp only [ptsTo, hr]

/-- **Separating conjunction**, as plain conjunction. Separation is tracked by the
    footprints (see `DependsOn.sepConj`), not intrinsically by `∗`. -/
def sepConj (P Q : JState 64 → Prop) : JState 64 → Prop := fun st => P st ∧ Q st

@[inherit_doc] scoped infixr:35 " ∗ " => sepConj

/-- **Footprints compose by union.** If `P` reads only `L₁` and `Q` reads only
    `L₂`, then `P ∗ Q` reads only `L₁ ∪ L₂`. This is the affine-heap reading of
    the separating conjunction: the combined assertion's read-set is the union of
    the conjuncts' read-sets. -/
theorem DependsOn.sepConj {L₁ L₂ : Finset String} {P Q : JState 64 → Prop}
    (hP : DependsOn L₁ P) (hQ : DependsOn L₂ Q) :
    DependsOn (L₁ ∪ L₂) (sepConj P Q) := by
  intro s s' h
  have h1 : ∀ r ∈ L₁, s.get r = s'.get r := fun r hr => h r (Finset.mem_union_left _ hr)
  have h2 : ∀ r ∈ L₂, s.get r = s'.get r := fun r hr => h r (Finset.mem_union_right _ hr)
  exact and_congr (hP s s' h1) (hQ s s' h2)

/-! ## The write footprint of a block -/

/-- **The write footprint of a block.** `writesOnly L body` holds when running
    `body` under `runBlock` leaves every register *outside* `L` unchanged: `L`
    over-approximates the set of registers the block may modify. This is exactly
    the shape of the ascent's `*_get_other` footprint seeds
    (`runBlock_lowerArith_id_other`, `lowerArith2_get_other`, `lowerMulHi_get_other`,
    …): each says a lowered op writes only its destination register. -/
def writesOnly (L : Finset String) (body : List (JInstr 64)) : Prop :=
  ∀ st r, r ∉ L → (runBlock st body).get r = st.get r

/-- A single `sbb dst src` writes only `dst` among the registers (it also writes
    `CF`, but the register-file heap is unaffected elsewhere). The `writesOnly`
    packaging of the register-frame half of `corresJ_sbb`. -/
theorem writesOnly_sbb (dst src : String) :
    writesOnly {dst} [.sbb dst (.reg src)] := by
  intro st r hr
  have hrne : r ≠ dst := by simpa only [Finset.mem_singleton] using hr
  simp only [runBlock_cons, runBlock_nil, evalInstr, JState.get, JState.writeB5W]
  rw [if_neg hrne]

/-! ## The frame rule -/

/-- **The frame rule.** From a triple `{P} body {Q}`, a write-footprint
    `writesOnly Lw body`, a frame assertion `R` reading only `Lr`, and disjoint
    footprints `Disjoint Lw Lr`, the framed triple `{P ∧ R} body {Q ∧ R}` holds.

    Local reasoning: because `body` writes only inside `Lw` and `R` reads only
    inside the disjoint `Lr`, `R` is untouched by `runBlock body`, so it survives
    verbatim alongside the original postcondition. This is derived purely from the
    footprint seeds — no re-analysis of the block's semantics. -/
theorem RunBlockTriple.frame {P Q R : JState 64 → Prop} {body : List (JInstr 64)}
    {Lw Lr : Finset String}
    (htriple : RunBlockTriple P body Q) (hwrites : writesOnly Lw body)
    (hR : DependsOn Lr R) (hdisj : Disjoint Lw Lr) :
    RunBlockTriple (fun st => P st ∧ R st) body (fun st => Q st ∧ R st) := by
  intro st hPR
  refine ⟨htriple st hPR.1, ?_⟩
  have hagree : ∀ r ∈ Lr, st.get r = (runBlock st body).get r := by
    intro r hr
    have hrw : r ∉ Lw := Finset.disjoint_right.mp hdisj hr
    exact (hwrites st r hrw).symm
  exact (hR st (runBlock st body) hagree).mp hPR.2

/-! ## A framed leaf — local reasoning holds on a real machine block -/

/-- **A framed carry leaf.** Framing the genuine subtract-with-borrow triple
    `sbb_as_triple` with a points-to `r₀ ↦ v` on a register `r₀ ≠ dst`. The
    resulting triple `{SRcarry · a ∧ r₀ ↦ v} sbb dst src {SRcarry · (sbbStep …) ∧ r₀ ↦ v}`
    shows the points-to on the disjoint register `r₀` is preserved across the
    machine step — local reasoning about `sbb` does not disturb the frame. -/
theorem sbb_framed_triple (dst src r₀ : String) (v : BitVec 64) (a : ACarry)
    (hne : r₀ ≠ dst) :
    RunBlockTriple
      (fun st => SRcarry st a ∧ ptsTo r₀ v st)
      [.sbb dst (.reg src)]
      (fun st => SRcarry st (sbbStep dst src a) ∧ ptsTo r₀ v st) :=
  (sbb_as_triple dst src a).frame (writesOnly_sbb dst src)
    (ptsTo_dependsOn r₀ v) (Finset.disjoint_singleton.mpr hne.symm)

end CatCrypt.Crypto.SecureCompilation.Ascent
