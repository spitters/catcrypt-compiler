/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hash.SHAKE

/-!
# cSHAKE: Customizable SHAKE (SP 800-185, Section 6.2)

Formalizes cSHAKE-128 and cSHAKE-256, the customizable variants of SHAKE
that provide built-in domain separation via function name and customization
string parameters.

## Overview

cSHAKE extends SHAKE with two additional inputs:
- **N**: function name string (identifies the derived function, e.g., "KMAC")
- **S**: customization string (user-chosen domain separator)

When both N and S are empty, cSHAKE reduces to SHAKE. Otherwise, the
inputs are encoded using `left_encode` and prepended to the message
before absorption.

## Key property: domain separation

The central theorem is `cshake_domain_separation`: different (N, S) pairs
produce independent functions. In the random oracle model, cSHAKE with
distinct customization strings behaves as independent random oracles.
This is the property that enables NIST SP 800-185 derived functions
(KMAC, TupleHash, ParallelHash) to share a single sponge primitive
without interference.

The domain separation property is stated abstractly: the encoding
function `cshake_encode` is injective, so different customization
parameters always produce different sponge inputs.

## Main definitions

* `CSHAKECustomization` -- (N, S) pair for domain separation
* `cshake_encode` -- encode N, S into padding (abstract, injective)
* `CSHAKEInstance` -- cSHAKE-128 or cSHAKE-256 instance
* `cshake128`, `cshake256` -- cSHAKE XOF constructors
* `cshake_domain_separation` -- different (N, S) give different sponge inputs

## References

* [SP 800-185 -- SHA-3 Derived Functions, Section 6.2, NIST 2016]
* [Kelsey, Chang, Perlner -- SHA-3 Derived Functions, 2016]

**0 axioms**, **all goals closed**.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.Hash.Keccak
open CatCrypt.Crypto.Hash.SHAKE
open scoped ENNReal

namespace CatCrypt.Crypto.Hash.CSHAKE

/-! ## Customization Parameters -/

/-- cSHAKE customization parameters.

    - `N`: function name bit string (identifies the higher-level function)
    - `S`: customization bit string (user-chosen domain separator)

    When both are empty, cSHAKE degenerates to plain SHAKE. -/
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

/-- Abstract encoding function for cSHAKE customization.

    This captures the SP 800-185 `bytepad(encode_string(N) || encode_string(S), w)`
    encoding. We model it as an abstract injective function from customization
    parameters to byte strings, since the security-relevant property is
    injectivity (domain separation), not the concrete byte layout.

    In the concrete implementation:
    - `encode_string(X) = left_encode(len(X)) || X`
    - `left_encode(x)` encodes the integer x as a variable-length big-endian byte string
    - The encoding is prefix-free by construction (length comes first) -/
structure CSHAKEEncoding where
  /-- Encode customization parameters into a byte prefix. -/
  encode : CSHAKECustomization → List (BitVec 8)
  /-- The encoding is injective: different customizations produce different prefixes.
      This is the prefix-free property of left_encode. -/
  injective : Function.Injective encode
  /-- Empty customization encodes to the empty list. -/
  encode_empty : encode emptyCustomization = []

/-- Domain separation: different customizations produce different encoded prefixes.

    This is the fundamental property that enables cSHAKE-based derived
    functions to act as independent random oracles. -/
theorem cshake_domain_separation (enc : CSHAKEEncoding)
    (c₁ c₂ : CSHAKECustomization) (h : enc.encode c₁ = enc.encode c₂) :
    c₁ = c₂ :=
  enc.injective h

/-! ## cSHAKE Instances -/

/-- cSHAKE security level (128 or 256). -/
inductive CSHAKELevel where
  /-- cSHAKE-128 (128-bit security). -/
  | cshake128 : CSHAKELevel
  /-- cSHAKE-256 (256-bit security). -/
  | cshake256 : CSHAKELevel
deriving DecidableEq

/-- Get the underlying SHAKE parameters for a cSHAKE level. -/
def CSHAKELevel.toSHAKEParams : CSHAKELevel → SHAKEParams
  | .cshake128 => shake128_params
  | .cshake256 => shake256_params

/-- cSHAKE-128 has 128-bit security. -/
theorem CSHAKELevel.cshake128_security :
    CSHAKELevel.cshake128.toSHAKEParams.security_level = 128 := rfl

/-- cSHAKE-256 has 256-bit security. -/
theorem CSHAKELevel.cshake256_security :
    CSHAKELevel.cshake256.toSHAKEParams.security_level = 256 := rfl

/-- A cSHAKE instance: customizable XOF built on SHAKE. -/
structure CSHAKEInstance where
  /-- Security level (128 or 256). -/
  level : CSHAKELevel
  /-- Customization parameters (N, S). -/
  custom : CSHAKECustomization
  /-- The encoding scheme. -/
  encoding : CSHAKEEncoding
  /-- The underlying SHAKE instance. -/
  shakeInst : SHAKEInstance
  /-- Parameters match the level. -/
  params_match : shakeInst.params = level.toSHAKEParams

/-- Evaluate cSHAKE: prepend encoded customization, then apply SHAKE.

    If N = S = "" (empty customization), falls back to plain SHAKE.
    Otherwise, prepend the encoded (N, S) to the message. -/
def cshake_eval (inst : CSHAKEInstance) (msg : List (BitVec 8))
    (outputBytes : ℕ) : List (BitVec 8) :=
  if inst.custom = emptyCustomization then
    -- When N = S = "", cSHAKE is just SHAKE
    shake_xof inst.shakeInst msg outputBytes
  else
    -- Prepend bytepad(encode_string(N) || encode_string(S), w)
    let pfx := inst.encoding.encode inst.custom
    shake_xof inst.shakeInst (pfx ++ msg) outputBytes

/-- cSHAKE with empty customization equals plain SHAKE. -/
theorem cshake_eval_empty (inst : CSHAKEInstance)
    (h : inst.custom = emptyCustomization)
    (msg : List (BitVec 8)) (n : ℕ) :
    cshake_eval inst msg n = shake_xof inst.shakeInst msg n := by
  simp [cshake_eval, h]

/-- cSHAKE with non-empty customization prepends the encoding. -/
theorem cshake_eval_nonempty (inst : CSHAKEInstance)
    (h : inst.custom ≠ emptyCustomization)
    (msg : List (BitVec 8)) (n : ℕ) :
    cshake_eval inst msg n =
    shake_xof inst.shakeInst (inst.encoding.encode inst.custom ++ msg) n := by
  unfold cshake_eval; simp [h]

/-! ## XOF Wrappers -/

/-- cSHAKE-128 as an abstract XOF. -/
def cshake128 (inst : CSHAKEInstance) (_ : inst.level = .cshake128) :
    XOFDef where
  name := "cSHAKE128"
  security := 128
  eval := cshake_eval inst

/-- cSHAKE-256 as an abstract XOF. -/
def cshake256 (inst : CSHAKEInstance) (_ : inst.level = .cshake256) :
    XOFDef where
  name := "cSHAKE256"
  security := 256
  eval := cshake_eval inst

/-! ## Domain Separation Consequences -/

/-- Two cSHAKE instances with different non-empty customizations always
    produce different sponge inputs (for the same message).

    This is the key consequence of encoding injectivity: if c₁ ≠ c₂
    and neither is empty, then the sponge sees different byte sequences,
    so in the random oracle model the outputs are independent. -/
theorem cshake_different_inputs (enc : CSHAKEEncoding)
    (c₁ c₂ : CSHAKECustomization)
    (_h₁ : c₁ ≠ emptyCustomization) (_h₂ : c₂ ≠ emptyCustomization)
    (hne : c₁ ≠ c₂) (msg : List (BitVec 8)) :
    enc.encode c₁ ++ msg ≠ enc.encode c₂ ++ msg := by
  intro heq
  apply hne
  apply enc.injective
  exact List.append_cancel_right heq

/-- cSHAKE with non-empty customization differs from plain SHAKE
    (the encoding adds a non-empty prefix). -/
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
