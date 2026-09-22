/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedParts

/-!
# The first five part checks of the shipped point addition

Each theorem states that the flag-aware symbolic executor of
`Ed25519PointAddShippedParts` carries the entry locations and flags of one canonical part
of `Imported.Ed25519PointAddShipped.ed25519PointAddShippedBlock` to its exit ones, under
the slot values of the generated program `paG`. The checks are `pa_part1` … `pa_part5`, each by
`decide +kernel`.
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

theorem pa_part2 :
    partCheck2 239 paSl2 paMap1 (some (aoWE (.v 238))) none paMap2 none none
      (canonFromD shippedBank (paState 1) ed25519PointAddShippedPart02) = true := by
  decide +kernel

theorem pa_part3 :
    partCheck2 499 paSl3 paMap2 none none paMap3 (some (.v 761)) none
      (canonFromD shippedBank (paState 2) ed25519PointAddShippedPart03) = true := by
  decide +kernel

theorem pa_part4 :
    partCheck2 762 paSl4 paMap3 (some (.v 761)) none paMap4 (some (.v 1019))
      none (canonFromD shippedBank (paState 3) ed25519PointAddShippedPart04) = true := by
  decide +kernel

theorem pa_part5 :
    partCheck2 1020 paSl5 paMap4 (some (.v 1019)) none paMap5
      (some (.v 1269)) none
      (canonFromD shippedBank (paState 4) ed25519PointAddShippedPart05) = true := by
  decide +kernel


end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof
