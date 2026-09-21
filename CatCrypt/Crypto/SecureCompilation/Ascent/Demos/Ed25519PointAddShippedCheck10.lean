/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedCheck09

/-!
# The tenth part check of the shipped point addition

The flag-aware symbolic executor of `Ed25519PointAddShippedParts` carries the entry
locations and flags of the last canonical part of
`Imported.Ed25519PointAddShipped.ed25519PointAddShippedBlock` to its exit ones, under the
slot values of the generated program `paG`. Importing this module brings the ten part
checks into scope, since each imports the one before it.

`Ed25519PointAddShippedCheck01` states why each part check has a module of its own.

## Main results

* `pa_part10`: the part check of the slots from 2251.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

theorem pa_part10 :
    partCheck2 2251 paSl10 paMap9 (some (aoWE (.v 2250))) none paOut none none
      (canonFromD shippedBank (paState 9) ed25519PointAddShippedPart10) = true := by
  decide +kernel

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof
