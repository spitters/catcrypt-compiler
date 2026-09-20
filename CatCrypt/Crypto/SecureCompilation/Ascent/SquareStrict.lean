/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.RunBlockMvcgen

/-!
# The machine-side correspondence squares

`Hax/Ascent/Square.lean` gives the square algebra of the source-level `Corres`: a
strict vertical category, and a horizontal composition whose associativity and right
unit hold only up to a semantic identification, because `.seq (.seq e₁ e₂) e₃` and
`.seq e₁ (.seq e₂ e₃)` are distinct `ImpExpr` values and `corres_seq`'s composite
reports the second leg's value function.

This module gives the same algebra for the machine-side squares, where a horizontal
arrow is a `List (JInstr 64)`, horizontal composition is `++`, and the square is
`RunBlockTriple P body Q` — a state-monad triple with no value component.

## Vertical direction

`VMapJ` bundles the two hypotheses of `RunBlockTriple.consequence` into one arrow
between the boundary data `(P, Q)` and `(P', Q')`. `VMapJ.id` and `VMapJ.comp` make
these a category (`vmapJ_id_comp`, `vmapJ_comp_id`, `vmapJ_comp_assoc`), and
`vsquareJ_act` is the action on a square, with its two functor laws
(`vsquareJ_act_id`, `vsquareJ_act_comp`). `VMapJ` and `RunBlockTriple` are `Prop`s,
so every one of these equations is settled by proof irrelevance; componentwise the
composite is plain function composition, which is unital and associative on the nose.

## Horizontal direction

`RunBlockTriple.hcomp` is `RunBlockTriple.seq` under the square-algebra name, and
`RunBlockTriple.hid` is the empty block. The three laws are stated over the programs
as well as the proofs:

* Associativity. `(l₁ ++ l₂) ++ l₃` and `l₁ ++ (l₂ ++ l₃)` are equal terms
  (`List.append_assoc`), so the two triple statements are the *same* proposition, and
  the two composite proofs agree once transported along that equality
  (`hcomp_assoc`). The equality of programs is propositional, not definitional, for
  variable lists; for concrete instruction literals both bracketings reduce to the
  same list and the transport disappears (`sbb_three_assoc`).
* Left unit. `[] ++ l` reduces to `l`, so `hid_hcomp` is an equality of proofs of one
  and the same statement, with no transport.
* Right unit. `l ++ []` equals `l` by `List.append_nil`, which is propositional for a
  variable list, so `hcomp_hid` carries a transport; for a concrete list it reduces
  and the transport disappears (`sbb_hid_right`).

So both hax-side weaknesses are absent here: the unit is two-sided, and associativity
is an identity of programs rather than a semantic identification.

## Interchange

`vmapJ_hcomp_interchange` mirrors `vmap_hcomp_interchange`: weakening the two ends of
a horizontal composite at the shared middle predicate is the same proof as composing
two separately weakened triples. Both sides prove `RunBlockTriple P' (l₁ ++ l₂) R'` —
the same program on the nose — so the law is `rfl`.

## The `CorresJ` reading

`corresJ_hcomp` is the composition law for `CorresJ` itself, obtained from
`corresJ_iff_triple` and `RunBlockTriple.hcomp`: two correspondences sharing a middle
abstract state compose over `l₁ ++ l₂` with abstract step `fa₂ ∘ fa₁`, provided the
first re-establishes the second's precondition. `corresJ_hid` is the empty block at
the identity step, and `corresJ_hcomp_assoc` records that both the program side and
the abstract side reassociate.

## The specification-monad reading

`runBlockM_append` identifies horizontal composition with bind in `StateM (JState 64)`.
Under it the three list laws are images of the monad laws: `bind_assoc` gives
`runBlockM ((l₁ ++ l₂) ++ l₃) = runBlockM (l₁ ++ (l₂ ++ l₃))`, `pure_bind` the left
unit and `bind_pure` the right unit, each without appealing to the corresponding
`List` lemma. `runBlockM_triple_iff` then carries each equation to the `Std.Do`
triples. The transport runs in one direction only: `runBlockM` is not injective, so a
monad-level equality of two block runs does not return a `List`-level equality of the
blocks, and the statements of §2 are the stronger ones.

## Main definitions

* `VMapJ`, `VMapJ.id`, `VMapJ.comp` — the vertical category of boundary weakenings
* `vsquareJ_act`, `vsquareJ_act_id`, `vsquareJ_act_comp` — its action on a square
* `RunBlockTriple.hcomp`, `RunBlockTriple.hid` — horizontal composition and identity
* `RunBlockTriple.hcomp_assoc`, `hid_hcomp`, `hcomp_hid` — the three horizontal laws
* `vmapJ_hcomp_interchange` — the interchange law
* `corresJ_hcomp`, `corresJ_hid`, `corresJ_hcomp_assoc` — the laws read on `CorresJ`
* `runBlockM_append`, `runBlockM_assoc_of_monad`, `runBlockM_nil_append_of_monad`,
  `runBlockM_append_nil_of_monad` — the specification-monad images
* `sbb_three_assoc`, `sbb_hid_left`, `sbb_hid_right` — the carry-leaf witnesses
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Std.Do
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. The vertical category of boundary weakenings -/

/-- A vertical arrow of the machine-side correspondence double category: the two
    hypotheses `RunBlockTriple.consequence` needs to turn a square with boundary
    `(P, Q)` into one with boundary `(P', Q')`. -/
structure VMapJ (P P' Q Q' : JState 64 → Prop) : Prop where
  /-- The precondition weakens. -/
  hP : ∀ st, P' st → P st
  /-- The postcondition strengthens. -/
  hQ : ∀ st, Q st → Q' st

/-- The vertical identity: both fields at their trivial witness. -/
theorem VMapJ.id (P Q : JState 64 → Prop) : VMapJ P P Q Q where
  hP := fun _ h => h
  hQ := fun _ h => h

/-- Vertical composition: chase both arrows through the shared middle boundary. -/
theorem VMapJ.comp {P P' P'' Q Q' Q'' : JState 64 → Prop}
    (m : VMapJ P P' Q Q') (m' : VMapJ P' P'' Q' Q'') : VMapJ P P'' Q Q'' where
  hP := fun st h => m.hP st (m'.hP st h)
  hQ := fun st h => m'.hQ st (m.hQ st h)

/-- Left unit for vertical composition. -/
theorem vmapJ_id_comp {P P' Q Q' : JState 64 → Prop} (m : VMapJ P P' Q Q') :
    (VMapJ.id P Q).comp m = m := rfl

/-- Right unit for vertical composition. -/
theorem vmapJ_comp_id {P P' Q Q' : JState 64 → Prop} (m : VMapJ P P' Q Q') :
    m.comp (VMapJ.id P' Q') = m := rfl

/-- Associativity of vertical composition. -/
theorem vmapJ_comp_assoc {P₀ P₁ P₂ P₃ Q₀ Q₁ Q₂ Q₃ : JState 64 → Prop}
    (m₁ : VMapJ P₀ P₁ Q₀ Q₁) (m₂ : VMapJ P₁ P₂ Q₁ Q₂) (m₃ : VMapJ P₂ P₃ Q₂ Q₃) :
    (m₁.comp m₂).comp m₃ = m₁.comp (m₂.comp m₃) := rfl

/-- **The action of a vertical arrow on a square.** `RunBlockTriple.consequence`
    under the `VMapJ` packaging. -/
theorem vsquareJ_act {P P' Q Q' : JState 64 → Prop} {body : List (JInstr 64)}
    (h : RunBlockTriple P body Q) (m : VMapJ P P' Q Q') : RunBlockTriple P' body Q' :=
  RunBlockTriple.consequence m.hP m.hQ h

/-- **Unit law of the action.** Acting by the vertical identity changes nothing; both
    sides prove `RunBlockTriple P body Q`, a `Prop`, so the equation is settled by
    proof irrelevance. -/
theorem vsquareJ_act_id {P Q : JState 64 → Prop} {body : List (JInstr 64)}
    (h : RunBlockTriple P body Q) : vsquareJ_act h (VMapJ.id P Q) = h := rfl

/-- **Functoriality of the action.** Acting by a vertical composite is acting by the
    two arrows in turn — an identity between two proofs of
    `RunBlockTriple P'' body Q''`. -/
theorem vsquareJ_act_comp {P P' P'' Q Q' Q'' : JState 64 → Prop}
    {body : List (JInstr 64)} (h : RunBlockTriple P body Q) (m : VMapJ P P' Q Q')
    (m' : VMapJ P' P'' Q' Q'') :
    vsquareJ_act h (m.comp m') = vsquareJ_act (vsquareJ_act h m) m' := rfl

/-! ## 2. The horizontal category of blocks

A horizontal arrow from `P` to `Q` is a block `l` with a proof `RunBlockTriple P l Q`;
composition concatenates the blocks and the identity is the empty block. Each law is
stated over both components: an equality of the programs, and — since
`RunBlockTriple` is a `Prop`, so proof irrelevance identifies any two proofs of one
statement — an equality of the composite proofs, transported along the program
equality where that equality is not definitional. -/

/-- **Horizontal composition.** `RunBlockTriple.seq` under the square-algebra name:
    triples over `l₁` and `l₂` sharing the middle predicate `Q` compose over
    `l₁ ++ l₂`. -/
theorem RunBlockTriple.hcomp {P Q R : JState 64 → Prop} {l₁ l₂ : List (JInstr 64)}
    (h₁ : RunBlockTriple P l₁ Q) (h₂ : RunBlockTriple Q l₂ R) :
    RunBlockTriple P (l₁ ++ l₂) R :=
  RunBlockTriple.seq h₁ h₂

/-- **The horizontal identity.** The empty block leaves the state alone, so it
    transports any predicate to itself. -/
theorem RunBlockTriple.hid (P : JState 64 → Prop) : RunBlockTriple P [] P :=
  fun _ h => h

/-- The two bracketings of a three-block composite are the same program. -/
theorem hcomp_prog_assoc (l₁ l₂ l₃ : List (JInstr 64)) :
    (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃) :=
  List.append_assoc l₁ l₂ l₃

/-- **Associativity of horizontal composition.** The two bracketings build proofs of
    statements that `hcomp_prog_assoc` identifies, and transporting the left
    bracketing along that equality gives the right one. -/
theorem RunBlockTriple.hcomp_assoc {P Q R S : JState 64 → Prop}
    {l₁ l₂ l₃ : List (JInstr 64)} (h₁ : RunBlockTriple P l₁ Q)
    (h₂ : RunBlockTriple Q l₂ R) (h₃ : RunBlockTriple R l₃ S) :
    hcomp_prog_assoc l₁ l₂ l₃ ▸ ((h₁.hcomp h₂).hcomp h₃) = h₁.hcomp (h₂.hcomp h₃) :=
  rfl

/-- **Left unit.** `[] ++ l` reduces to `l`, so composing with the identity on the
    left is an equality of proofs of one statement, with no transport. -/
theorem RunBlockTriple.hid_hcomp {P Q : JState 64 → Prop} {l : List (JInstr 64)}
    (h : RunBlockTriple P l Q) : (RunBlockTriple.hid P).hcomp h = h :=
  rfl

/-- **Right unit.** `l ++ []` equals `l` by `List.append_nil`; transporting the
    composite along that equality gives back the original proof. -/
theorem RunBlockTriple.hcomp_hid {P Q : JState 64 → Prop} {l : List (JInstr 64)}
    (h : RunBlockTriple P l Q) :
    List.append_nil l ▸ (h.hcomp (RunBlockTriple.hid Q)) = h :=
  rfl

/-! ## 3. Interchange -/

/-- **The interchange law.** Weakening `h₁` by `mIn` and `h₂` by `mOut` and then
    composing horizontally is the same proof as composing horizontally and then
    weakening by the arrow built from `mIn.hP` and `mOut.hQ`. Both sides prove
    `RunBlockTriple P' (l₁ ++ l₂) R'` — the same program, so no associator enters and
    the law is `rfl`. -/
theorem vmapJ_hcomp_interchange {P P' Q Q' R R' : JState 64 → Prop}
    {l₁ l₂ : List (JInstr 64)} (h₁ : RunBlockTriple P l₁ Q) (h₂ : RunBlockTriple Q l₂ R)
    (mIn : VMapJ P P' Q Q') (mOut : VMapJ Q Q' R R') :
    (vsquareJ_act h₁ mIn).hcomp (vsquareJ_act h₂ mOut)
      = vsquareJ_act (h₁.hcomp h₂) { hP := mIn.hP, hQ := mOut.hQ } :=
  rfl

/-! ## 4. The laws read on `CorresJ`

`corresJ_iff_triple` presents `CorresJ SR P fa c` as the `fa`-indexed family of
triples `{SR · a} c {SR · (fa a)}`. Horizontal composition of that family is the
composition law an ascent reader uses directly. -/

/-- **Composition of correspondences.** Two `CorresJ` correspondences over the same
    state relation, whose first re-establishes the second's precondition on the
    abstract state it produces, compose over the concatenated block `l₁ ++ l₂` with
    abstract step `fa₂ ∘ fa₁`. Obtained from `RunBlockTriple.hcomp` through
    `corresJ_iff_triple`. -/
theorem corresJ_hcomp {AState : Type} (SR : JState 64 → AState → Prop)
    {P Q : AState → Prop} {fa₁ fa₂ : AState → AState} {l₁ l₂ : List (JInstr 64)}
    (h₁ : CorresJ SR P fa₁ l₁) (h₂ : CorresJ SR Q fa₂ l₂)
    (hmid : ∀ a, P a → Q (fa₁ a)) :
    CorresJ SR P (fa₂ ∘ fa₁) (l₁ ++ l₂) :=
  (corresJ_iff_triple SR P (fa₂ ∘ fa₁) (l₁ ++ l₂)).mpr fun a ha =>
    RunBlockTriple.hcomp
      ((corresJ_iff_triple SR P fa₁ l₁).mp h₁ a ha)
      ((corresJ_iff_triple SR Q fa₂ l₂).mp h₂ (fa₁ a) (hmid a ha))

/-- **The identity correspondence.** The empty block refines the identity abstract
    step, under any precondition. -/
theorem corresJ_hid {AState : Type} (SR : JState 64 → AState → Prop)
    (P : AState → Prop) : CorresJ SR P id [] :=
  (corresJ_iff_triple SR P id []).mpr fun a _ => RunBlockTriple.hid (fun st => SR st a)

/-- **Associativity for correspondences.** Both the program side and the abstract side
    reassociate: the concatenations agree by `List.append_assoc` and the abstract steps
    by associativity of function composition, so the two bracketings of a three-leg
    chain state the same proposition. -/
theorem corresJ_hcomp_assoc {AState : Type} (SR : JState 64 → AState → Prop)
    (P : AState → Prop) (fa₁ fa₂ fa₃ : AState → AState) (l₁ l₂ l₃ : List (JInstr 64)) :
    CorresJ SR P ((fa₃ ∘ fa₂) ∘ fa₁) ((l₁ ++ l₂) ++ l₃)
      = CorresJ SR P (fa₃ ∘ (fa₂ ∘ fa₁)) (l₁ ++ (l₂ ++ l₃)) := by
  rw [hcomp_prog_assoc]
  rfl

/-! ## 5. The specification-monad reading

`runBlockM` runs a block in `StateM (JState 64)`, and `runBlockM_triple_iff` equates
the `Std.Do` triple over it with `RunBlockTriple`. Under `runBlockM_append`,
horizontal composition is bind, and the three laws of §2 are the images of the monad
laws. -/

/-- **Horizontal composition is bind.** The monadic run of a concatenation is the run
    of the first block followed by the run of the second. -/
theorem runBlockM_append (l₁ l₂ : List (JInstr 64)) :
    runBlockM (l₁ ++ l₂) = runBlockM l₁ >>= fun _ => runBlockM l₂ := by
  induction l₁ with
  | nil => simp [runBlockM]
  | cons i is ih =>
    simp only [List.cons_append, runBlockM_cons, ih, bind_assoc]

/-- Associativity of block concatenation as the image of `bind_assoc`, derived from
    `runBlockM_append` without `List.append_assoc`. -/
theorem runBlockM_assoc_of_monad (l₁ l₂ l₃ : List (JInstr 64)) :
    runBlockM ((l₁ ++ l₂) ++ l₃) = runBlockM (l₁ ++ (l₂ ++ l₃)) := by
  simp only [runBlockM_append, bind_assoc]

/-- The left unit as the image of `pure_bind`. -/
theorem runBlockM_nil_append_of_monad (l : List (JInstr 64)) :
    runBlockM ([] ++ l) = runBlockM l := by
  simp only [runBlockM_append, runBlockM_nil, pure_bind]

/-- The right unit as the image of `bind_pure`. -/
theorem runBlockM_append_nil_of_monad (l : List (JInstr 64)) :
    runBlockM (l ++ []) = runBlockM l := by
  simp only [runBlockM_append, runBlockM_nil, bind_pure_unit]

/-- **Horizontal composition on the `Std.Do` triples.** Two triples over `runBlockM`
    sharing the middle predicate compose over the concatenated block. The proof goes
    through `runBlockM_triple_iff` and `RunBlockTriple.hcomp`. -/
theorem runBlockM_triple_hcomp {P Q R : JState 64 → Prop} {l₁ l₂ : List (JInstr 64)}
    (h₁ : ⦃fun s => ⌜P s⌝⦄ runBlockM l₁ ⦃⇓ _ s => ⌜Q s⌝⦄)
    (h₂ : ⦃fun s => ⌜Q s⌝⦄ runBlockM l₂ ⦃⇓ _ s => ⌜R s⌝⦄) :
    ⦃fun s => ⌜P s⌝⦄ runBlockM (l₁ ++ l₂) ⦃⇓ _ s => ⌜R s⌝⦄ :=
  (runBlockM_triple_iff P R (l₁ ++ l₂)).mpr
    (RunBlockTriple.hcomp ((runBlockM_triple_iff P Q l₁).mp h₁)
      ((runBlockM_triple_iff Q R l₂).mp h₂))

/-! ## 6. Witnesses on the carry leaves

`sbb_as_triple` reads the subtract-with-borrow leaf `corresJ_sbb` as a
`RunBlockTriple`. Three such leaves compose in either bracketing, and each side of a
single leaf absorbs the identity: the blocks are instruction literals, so every
concatenation reduces and each law is `rfl` with no transport. -/

/-- Three subtract-with-borrow leaves compose to the same proof under either
    bracketing. -/
theorem sbb_three_assoc (d0 s0 d1 s1 d2 s2 : String) (a : ACarry) :
    ((sbb_as_triple d0 s0 a).hcomp
          (sbb_as_triple d1 s1 (sbbStep d0 s0 a))).hcomp
        (sbb_as_triple d2 s2 (sbbStep d1 s1 (sbbStep d0 s0 a)))
      = (sbb_as_triple d0 s0 a).hcomp
          ((sbb_as_triple d1 s1 (sbbStep d0 s0 a)).hcomp
            (sbb_as_triple d2 s2 (sbbStep d1 s1 (sbbStep d0 s0 a)))) :=
  rfl

/-- The identity block on the left of a subtract-with-borrow leaf. -/
theorem sbb_hid_left (dst src : String) (a : ACarry) :
    (RunBlockTriple.hid (fun st => SRcarry st a)).hcomp (sbb_as_triple dst src a)
      = sbb_as_triple dst src a :=
  rfl

/-- The identity block on the right of a subtract-with-borrow leaf. -/
theorem sbb_hid_right (dst src : String) (a : ACarry) :
    (sbb_as_triple dst src a).hcomp
        (RunBlockTriple.hid (fun st => SRcarry st (sbbStep dst src a)))
      = sbb_as_triple dst src a :=
  rfl

end CatCrypt.Crypto.SecureCompilation.Ascent
