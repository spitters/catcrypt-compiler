/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hash.SHAKE

/-!
# Domain separation by a prefix: an abstract model

An abstract model of domain separation by a prefix. A customization is a pair (N, S)
of byte strings, and an encoding is a parameter: any injective function from
customizations to byte strings that maps the empty pair to the empty string.
`cshake_eval` applies `shake_xof` to the message when the customization is empty and
to the encoded customization followed by the message otherwise.

## Main definitions

* `CSHAKECustomization` -- the pair (N, S)
* `CSHAKEEncoding` -- an injective prefix function
* `CSHAKEInstance` -- a level, a customization, an encoding and a SHAKE instance
* `cshake_eval` -- `shake_xof` of the prefixed message
* `cshake128`, `cshake256` -- `cshake_eval` packaged as an `XOFDef`, by level

## Main results

* `cshake_eval_empty`, `cshake_eval_nonempty` -- the two cases of `cshake_eval`
* `cshake_different_inputs` -- distinct non-empty customizations give distinct
  prefixed messages
* `cshake_differs_from_shake` -- for a non-empty customization and message, the
  prefixed message differs from the message
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Hash.Keccak
open CatCrypt.Crypto.Hash.SHAKE
open scoped ENNReal

namespace CatCrypt.Crypto.Hash.CSHAKE

/-! ## Customization Parameters -/

/-- A customization: the pair (N, S) of byte strings that selects the prefix. -/
structure CSHAKECustomization where
  /-- Function name string N. -/
  functionName : List (BitVec 8)
  /-- Customization string S. -/
  customization : List (BitVec 8)
deriving DecidableEq

/-- The empty customization: both N and S are empty. -/
def emptyCustomization : CSHAKECustomization where
  functionName := []
  customization := []

/-- Check whether a customization is the empty one. -/
def CSHAKECustomization.isEmpty (c : CSHAKECustomization) : Bool :=
  c.functionName.isEmpty && c.customization.isEmpty

/-- The empty customization is indeed empty. -/
theorem emptyCustomization_isEmpty : emptyCustomization.isEmpty = true := rfl

/-! ## Encoding (Abstract Interface) -/

/-- An abstract prefix function: any injective function from customizations to byte
    strings that maps the empty customization to the empty string. -/
structure CSHAKEEncoding where
  /-- The prefix of a customization. -/
  encode : CSHAKECustomization → List (BitVec 8)
  /-- Different customizations have different prefixes. -/
  injective : Function.Injective encode
  /-- Empty customization encodes to the empty list. -/
  encode_empty : encode emptyCustomization = []

/-! ## Instances -/

/-- The level of the model: which SHAKE parameter set it uses. -/
inductive CSHAKELevel where
  /-- The level with the SHAKE-128 parameters. -/
  | cshake128 : CSHAKELevel
  /-- The level with the SHAKE-256 parameters. -/
  | cshake256 : CSHAKELevel
deriving DecidableEq

/-- The SHAKE parameters of a level. -/
def CSHAKELevel.toSHAKEParams : CSHAKELevel → SHAKEParams
  | .cshake128 => shake128_params
  | .cshake256 => shake256_params

/-- An instance of the prefix model over a SHAKE instance. -/
structure CSHAKEInstance where
  /-- The level (128 or 256). -/
  level : CSHAKELevel
  /-- Customization parameters (N, S). -/
  custom : CSHAKECustomization
  /-- The encoding scheme. -/
  encoding : CSHAKEEncoding
  /-- The underlying SHAKE instance. -/
  shakeInst : SHAKEInstance
  /-- Parameters match the level. -/
  params_match : shakeInst.params = level.toSHAKEParams

/-- Evaluation of the prefix model: `shake_xof` of the message for the empty
    customization, and of the encoded customization followed by the message otherwise. -/
def cshake_eval (inst : CSHAKEInstance) (msg : List (BitVec 8))
    (outputBytes : ℕ) : List (BitVec 8) :=
  if inst.custom = emptyCustomization then
    shake_xof inst.shakeInst msg outputBytes
  else
    let pfx := inst.encoding.encode inst.custom
    shake_xof inst.shakeInst (pfx ++ msg) outputBytes

/-- At the empty customization `cshake_eval` is `shake_xof`. -/
theorem cshake_eval_empty (inst : CSHAKEInstance)
    (h : inst.custom = emptyCustomization)
    (msg : List (BitVec 8)) (n : ℕ) :
    cshake_eval inst msg n = shake_xof inst.shakeInst msg n := by
  simp [cshake_eval, h]

/-- At a non-empty customization `cshake_eval` is `shake_xof` of the prefixed message. -/
theorem cshake_eval_nonempty (inst : CSHAKEInstance)
    (h : inst.custom ≠ emptyCustomization)
    (msg : List (BitVec 8)) (n : ℕ) :
    cshake_eval inst msg n =
    shake_xof inst.shakeInst (inst.encoding.encode inst.custom ++ msg) n := by
  unfold cshake_eval; simp [h]

/-! ## XOF Wrappers -/

/-- The prefix model at level 128 as an `XOFDef`. -/
def cshake128 (inst : CSHAKEInstance) (_ : inst.level = .cshake128) :
    XOFDef where
  name := "SHAKE128 prefix model"
  security := 128
  eval := cshake_eval inst

/-- The prefix model at level 256 as an `XOFDef`. -/
def cshake256 (inst : CSHAKEInstance) (_ : inst.level = .cshake256) :
    XOFDef where
  name := "SHAKE256 prefix model"
  security := 256
  eval := cshake_eval inst

/-! ## Distinctness of the prefixed messages -/

/-- Distinct non-empty customizations give distinct prefixed messages, for the same
    message. The statement is about the argument of `shake_xof`. -/
theorem cshake_different_inputs (enc : CSHAKEEncoding)
    (c₁ c₂ : CSHAKECustomization)
    (_h₁ : c₁ ≠ emptyCustomization) (_h₂ : c₂ ≠ emptyCustomization)
    (hne : c₁ ≠ c₂) (msg : List (BitVec 8)) :
    enc.encode c₁ ++ msg ≠ enc.encode c₂ ++ msg := by
  intro heq
  apply hne
  apply enc.injective
  exact List.append_cancel_right heq

/-- For a non-empty customization and a non-empty message, the prefixed message
    differs from the message. The statement is about the argument of `shake_xof`. -/
theorem cshake_differs_from_shake (enc : CSHAKEEncoding)
    (c : CSHAKECustomization) (hne : c ≠ emptyCustomization)
    (msg : List (BitVec 8)) (_hm : msg ≠ []) :
    enc.encode c ++ msg ≠ msg := by
  intro heq
  have hlen : (enc.encode c).length + msg.length = msg.length := by
    rw [← List.length_append]; rw [heq]
  have hzero : (enc.encode c).length = 0 := by omega
  have hempty : enc.encode c = [] := List.eq_nil_of_length_eq_zero hzero
  have : c = emptyCustomization := enc.injective (by rw [hempty, enc.encode_empty])
  exact hne this

end CatCrypt.Crypto.Hash.CSHAKE
