/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.Secrecy
public import CatCrypt.Crypto.Hax.HaxCallNames
public import CatCrypt.Crypto.SecureCompilation.SourceSecrecyTransfer.Defs

/-!
# The level table of a function from its hax secrecy record

hax-lean's `FnSecrecy` gives each parameter of a function a `BindingSecrecy`. The
front names the slot of a parameter `x` by the variable `x` (`haxToLowCT`), and struct
flattening (`flatE`) names the slot of field `f` of a struct variable `x` by
`structCompName x f`. `levelsOf` is the level table these names induce:

* a `secret` parameter `x` marks the slot `x` secret;
* a `fields fs` parameter `x` marks the slot `structCompName x f` secret for each
  `f ∈ fs`, and the slot `x`, which holds the whole struct where the struct is not
  flattened;
* every other slot is public.

The table is `SourceSecrecy.toLevelTable` of the record's secret slots with no
declassified binding.

## Main definitions

* `bindingSlots`, `secretSlots` — the slots a record marks secret
* `levelsOf` — the level table of a record
* `levelsOfFn` — the level table of a function of a crate's record list

## Main results

* `levelsOf_eq_secret_iff` — `levelsOf s` marks a slot secret exactly when it is a
  secret parameter, a field of a parameter with a secret field listed in its record,
  or the root slot of such a parameter
* `levelsOf_eq_public_iff`
* `levelsOfFn_of_not_listed` — a function the list does not name has the all-public
  table
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CT

open _root_.Hax (FnSecrecy BindingSecrecy)
open CatCrypt.Crypto.Jasmin.LowCT (LevelTable SecretLevel)
open CatCrypt.Crypto.SecureCompilation.SourceSecrecyTransfer (SourceSecrecy)
open CatCrypt.Crypto.Hax (structCompName)

/-- The slots a binding `x` of secrecy `b` marks secret: none for `pub`, `x` for
    `secret`, and `x` with the component slot `structCompName x f` of each listed
    field `f` for `fields`. -/
def bindingSlots (x : String) : BindingSecrecy → List String
  | .pub => []
  | .secret => [x]
  | .fields fs => x :: fs.map (structCompName x)

/-- The slots the record `s` marks secret, parameter by parameter. -/
def secretSlots (s : FnSecrecy) : List String :=
  s.params.flatMap fun p => bindingSlots p.1 p.2

/-- The record `s` as a `SourceSecrecy`: its secret slots, nothing declassified. -/
def toSourceSecrecy (s : FnSecrecy) : SourceSecrecy :=
  { secret := secretSlots s, declassified := [] }

/-- The level table of the record `s`: `Secret` at its secret slots, `Public`
    elsewhere. -/
def levelsOf (s : FnSecrecy) : LevelTable := (toSourceSecrecy s).toLevelTable

/-- The level table of the function `fn` from the records `tbl` of its crate. -/
def levelsOfFn (tbl : List FnSecrecy) (fn : String) : LevelTable :=
  levelsOf (FnSecrecy.lookup tbl fn)

theorem mem_bindingSlots_iff (x v : String) (b : BindingSecrecy) :
    v ∈ bindingSlots x b ↔
      (b = .secret ∧ v = x) ∨
        ∃ fs, b = .fields fs ∧ (v = x ∨ ∃ f ∈ fs, v = structCompName x f) := by
  cases b with
  | pub => simp [bindingSlots]
  | secret => simp [bindingSlots]
  | fields fs => simp [bindingSlots, eq_comm]

theorem levelsOf_eq_secret_iff' (s : FnSecrecy) (v : String) :
    levelsOf s v = .Secret ↔ v ∈ secretSlots s := by
  simp only [levelsOf, toSourceSecrecy, SourceSecrecy.toLevelTable]
  by_cases h : v ∈ secretSlots s <;> simp [h]

/-- **The table marks exactly the declared secrets.** A slot is secret in
    `levelsOf s` exactly when it is a parameter `x` declared `secret`, or, for a
    parameter `x` declared `fields fs`, the slot `x` or the component slot
    `structCompName x f` of a field `f ∈ fs`. -/
theorem levelsOf_eq_secret_iff (s : FnSecrecy) (v : String) :
    levelsOf s v = .Secret ↔
      (∃ x, (x, BindingSecrecy.secret) ∈ s.params ∧ v = x) ∨
        ∃ x fs, (x, BindingSecrecy.fields fs) ∈ s.params ∧
          (v = x ∨ ∃ f ∈ fs, v = structCompName x f) := by
  rw [levelsOf_eq_secret_iff']
  simp only [secretSlots, List.mem_flatMap, mem_bindingSlots_iff]
  constructor
  · rintro ⟨⟨x, b⟩, hp, (⟨rfl, rfl⟩ | ⟨fs, rfl, h⟩)⟩
    · exact .inl ⟨_, hp, rfl⟩
    · exact .inr ⟨_, fs, hp, h⟩
  · rintro (⟨x, hp, rfl⟩ | ⟨x, fs, hp, h⟩)
    · exact ⟨_, hp, .inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, hp, .inr ⟨fs, rfl, h⟩⟩

/-- Every slot that is not a declared secret is public in `levelsOf s`. -/
theorem levelsOf_eq_public_iff (s : FnSecrecy) (v : String) :
    levelsOf s v = .Public ↔ v ∉ secretSlots s := by
  rw [← levelsOf_eq_secret_iff']
  cases levelsOf s v <;> simp

/-- A function the record list does not name has the all-public table. -/
theorem levelsOfFn_of_not_listed (tbl : List FnSecrecy) (fn : String)
    (h : tbl.find? (·.fn == fn) = none) (v : String) :
    levelsOfFn tbl fn v = .Public := by
  rw [levelsOfFn, levelsOf_eq_public_iff]
  simp [FnSecrecy.lookup, h, secretSlots]

end CatCrypt.Crypto.SecureCompilation.CT
