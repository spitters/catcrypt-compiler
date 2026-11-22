/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hash.CSHAKE

/-!
# Keyed prefix hash over the customized SHAKE model

An abstract keyed hash: `cshake_eval`, at an instance whose function name is the
byte string "KMAC", applied to the key bytes followed by the message bytes.

## Main definitions

* `KMACParams` -- a level (128 or 256), an output length and a key length
* `KMACScheme` -- parameters with a `CSHAKEInstance` of the same level and
  function name "KMAC"
* `kmac_compute` -- `cshake_eval` of `key ++ msg`

The theorems evaluate the fields and projections of the two parameter sets.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Crypto.Hash.CSHAKE

namespace CatCrypt.Crypto.Hash.KMAC

/-! ## Parameters -/

/-- Parameters of the keyed prefix hash.

    - `security_level`: 128 or 256, selects the level of the customized SHAKE model
    - `output_length`: requested output length in bytes
    - `key_length`: key length in bytes -/
structure KMACParams where
  /-- The level, 128 or 256. -/
  security_level : ℕ
  /-- Output length in bytes. -/
  output_length : ℕ
  /-- Key length in bytes. -/
  key_length : ℕ
  /-- The level is 128 or 256. -/
  valid_security : security_level = 128 ∨ security_level = 256

/-- Parameters at level 128, with a 32-byte output and a 16-byte key. -/
def kmac128_params : KMACParams where
  security_level := 128
  output_length := 32
  key_length := 16
  valid_security := Or.inl rfl

/-- Parameters at level 256, with a 64-byte output and a 32-byte key. -/
def kmac256_params : KMACParams where
  security_level := 256
  output_length := 64
  key_length := 32
  valid_security := Or.inr rfl

/-- The level of the customized SHAKE model for a parameter set. -/
def KMACParams.toCLevel (p : KMACParams) : CSHAKELevel :=
  if p.security_level = 128 then .cshake128 else .cshake256

/-- The capacity in bits for a parameter set. -/
def KMACParams.capacity (p : KMACParams) : ℕ :=
  if p.security_level = 128 then 256 else 512

/-- `kmac128_params` selects the level `cshake128`. -/
theorem kmac128_level : kmac128_params.toCLevel = .cshake128 := rfl

/-- `kmac256_params` selects the level `cshake256`. -/
theorem kmac256_level : kmac256_params.toCLevel = .cshake256 := by
  simp [KMACParams.toCLevel, kmac256_params]

/-! ## Keyed prefix hash -/

/-- The data of a keyed prefix hash: parameters and an instance of the customized
    SHAKE model at their level, with function name "KMAC". -/
structure KMACScheme where
  /-- The parameters. -/
  params : KMACParams
  /-- The instance of the customized SHAKE model. -/
  cshakeInst : CSHAKEInstance
  /-- The level of the instance is the level of the parameters. -/
  level_match : cshakeInst.level = params.toCLevel
  /-- The customization uses function name "KMAC". -/
  kmac_name : cshakeInst.custom.functionName = "KMAC".toList.map (BitVec.ofNat 8 ·.toNat)

/-- The keyed prefix hash: `cshake_eval` of the key bytes followed by the message
    bytes, at the output length of the parameters. -/
def kmac_compute (S : KMACScheme) (key : List (BitVec 8))
    (msg : List (BitVec 8)) : List (BitVec 8) :=
  cshake_eval S.cshakeInst (key ++ msg) S.params.output_length

/-! ## Values of the parameter sets -/

/-- `kmac128_params` has capacity 256. -/
theorem kmac128_capacity : kmac128_params.capacity = 256 := rfl

/-- `kmac256_params` has capacity 512. -/
theorem kmac256_capacity : kmac256_params.capacity = 512 := by
  simp [KMACParams.capacity, kmac256_params]

/-- `kmac128_params` has a 16-byte key. -/
theorem kmac128_key_length : kmac128_params.key_length = 16 := rfl

/-- `kmac256_params` has a 32-byte key. -/
theorem kmac256_key_length : kmac256_params.key_length = 32 := rfl

end CatCrypt.Crypto.Hash.KMAC
