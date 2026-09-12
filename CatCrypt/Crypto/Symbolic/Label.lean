/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

module

/-!
# Corruption Label Lattice

Port of DY*'s label system. Labels track the corruption level of
cryptographic material.

## Main definitions

* `Label` — corruption labels forming a lattice
* `Label.bot` — bottom: never corrupt (unless explicitly compromised)
* `Label.top` — top: always known to the attacker
* `principalLabel` — label requiring corruption of a specific principal
* `canFlow` — label ordering (information flow)

## Design

DY* uses labels to track which principals must be corrupted for a value to be
known to the attacker. The label lattice is:
- `bot` (⊥): requires corrupting ALL principals (= secret)
- `top` (⊤): requires corrupting NO principals (= public)
- `principal p`: requires corrupting principal `p`
- `meet l₁ l₂`: requires corrupting someone from BOTH l₁ AND l₂
- `join l₁ l₂`: requires corrupting someone from l₁ OR l₂

## References

* DY*-extrinsic: `DY.Core.Label.Type`, `DY.Core.Label.Lattice`
-/

@[expose] public section

namespace CatCrypt.Crypto.Symbolic

/-- Corruption labels.

A label records which principals must be compromised for the labeled value
to be known to the attacker. Uses the free lattice over principal names. -/
inductive Label where
  /-- Bottom (secret): value is protected unless explicitly compromised -/
  | bot : Label
  /-- Top (public): value is always available to the attacker -/
  | top : Label
  /-- Value is protected by principal `p`'s honesty -/
  | principal : (p : String) → Label
  /-- Meet: value is protected if EITHER component label protects it -/
  | meet : Label → Label → Label
  /-- Join: value is protected only if BOTH component labels protect it -/
  | join : Label → Label → Label
  deriving DecidableEq, Repr, Inhabited

/-- Shorthand for principal labels -/
def principalLabel (p : String) : Label := .principal p

/-! ## Corruption Semantics

A corruption set `C : String → Prop` lists all compromised principals.
A label is "corrupt" under `C` if the corruption set is sufficient. -/

/-- Whether a label is corrupt given a set of corrupted principals -/
def Label.isCorrupt (C : String → Prop) : Label → Prop
  | .bot => False
  | .top => True
  | .principal p => C p
  | .meet l₁ l₂ => l₁.isCorrupt C ∧ l₂.isCorrupt C
  | .join l₁ l₂ => l₁.isCorrupt C ∨ l₂.isCorrupt C

/-- Corruption is monotone: more corrupted principals → more labels are corrupt -/
theorem Label.isCorrupt_mono {C₁ C₂ : String → Prop} (h : ∀ s, C₁ s → C₂ s) (l : Label) :
    l.isCorrupt C₁ → l.isCorrupt C₂ := by
  induction l with
  | bot => exact id
  | top => exact id
  | principal p => exact h p
  | meet _ _ ih₁ ih₂ => exact fun ⟨h₁, h₂⟩ => ⟨ih₁ h₁, ih₂ h₂⟩
  | join _ _ ih₁ ih₂ =>
    exact fun h' => h'.elim (fun h₁ => .inl (ih₁ h₁)) (fun h₂ => .inr (ih₂ h₂))

/-! ## Label Ordering (Information Flow)

`canFlow l₁ l₂` means: for all corruption sets C, if l₁ is corrupt then l₂
is corrupt. This is the information flow ordering. -/

/-- Information flow ordering: `canFlow l₁ l₂` iff l₁ being corrupt implies
l₂ is corrupt, for ALL possible corruption sets. -/
def canFlow (l₁ l₂ : Label) : Prop :=
  ∀ C : String → Prop, l₁.isCorrupt C → l₂.isCorrupt C

theorem canFlow_refl (l : Label) : canFlow l l := fun _ h => h

theorem canFlow_trans {l₁ l₂ l₃ : Label} :
    canFlow l₁ l₂ → canFlow l₂ l₃ → canFlow l₁ l₃ :=
  fun h₁₂ h₂₃ C h => h₂₃ C (h₁₂ C h)

theorem canFlow_bot (l : Label) : canFlow Label.bot l :=
  fun _ h => absurd h id

theorem canFlow_top (l : Label) : canFlow l Label.top :=
  fun _ _ => trivial

theorem canFlow_meet_left (l₁ l₂ : Label) : canFlow (Label.meet l₁ l₂) l₁ :=
  fun _ h => h.1

theorem canFlow_meet_right (l₁ l₂ : Label) : canFlow (Label.meet l₁ l₂) l₂ :=
  fun _ h => h.2

theorem canFlow_join_left (l₁ l₂ : Label) : canFlow l₁ (Label.join l₁ l₂) :=
  fun _ h => .inl h

theorem canFlow_join_right (l₁ l₂ : Label) : canFlow l₂ (Label.join l₁ l₂) :=
  fun _ h => .inr h

theorem canFlow_meet_intro {l l₁ l₂ : Label} :
    canFlow l l₁ → canFlow l l₂ → canFlow l (Label.meet l₁ l₂) :=
  fun h₁ h₂ C h => ⟨h₁ C h, h₂ C h⟩

theorem canFlow_join_elim {l₁ l₂ l : Label} :
    canFlow l₁ l → canFlow l₂ l → canFlow (Label.join l₁ l₂) l :=
  fun h₁ h₂ C h => h.elim (h₁ C) (h₂ C)

/-! ## Publishability

A term is "publishable" if its label flows to `top` — i.e., it's always
corrupt. In practice this means the label IS `top`. -/

/-- A label is publishable if it flows to top (= attacker always knows it) -/
def Label.isPublishable (l : Label) : Prop := canFlow l Label.top

theorem Label.top_isPublishable : Label.isPublishable Label.top := by
  intro C _; exact trivial

/-! ## Derived Label Operations -/

/-- Label for a DH shared secret: meet of both participants' labels -/
def dhLabel (p₁ p₂ : String) : Label :=
  Label.meet (principalLabel p₁) (principalLabel p₂)

/-- Label for a group key: meet of all participants' labels -/
def groupLabel (ps : List String) : Label :=
  ps.foldl (fun acc p => Label.meet acc (principalLabel p)) Label.top

end CatCrypt.Crypto.Symbolic
