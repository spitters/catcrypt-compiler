/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedParts

/-!
# The first part check of the shipped point addition

The flag-aware symbolic executor of `Ed25519PointAddShippedParts` carries the entry
locations and flags of the first canonical part of
`Imported.Ed25519PointAddShipped.ed25519PointAddShippedBlock` to its exit ones, under the
slot values of the generated program `paG`.

Each of the ten part checks is a `decide +kernel` over a symbolic run of about 230
instructions. One of them alone reaches 2.8 GB of kernel memory, and five in one module
reach 5 GB, because the allocator does not return what a finished reduction frees. One
check per module bounds that by one `lean` process, and the ten are chained by import so
that they run one at a time rather than concurrently.

## Main results

* `pa_part1`: the part check of the slots from 57.
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

theorem pa_part1 :
    partCheck2 57 paSl1 paIn none none paMap1 (some (aoWE (.v 238))) none
      (canonFromD shippedBank {} ed25519PointAddShippedPart01) = true := by
  decide +kernel

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof
