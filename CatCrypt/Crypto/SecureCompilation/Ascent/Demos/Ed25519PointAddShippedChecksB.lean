/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedChecksA

/-!
# The last five part checks of the shipped point addition

Each theorem states that the flag-aware symbolic executor of
`Ed25519PointAddShippedParts` carries the entry locations and flags of one canonical part
of `Imported.Ed25519PointAddShipped.ed25519PointAddShippedBlock` to its exit ones, under
the slot values of the generated program `paG`. The checks are `pa_part6` … `pa_part10`, each by
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

theorem pa_part6 :
    partCheck2 1270 paSl6 paMap5 (some (.v 1269)) none paMap6
      (some (aoWE (.v 1494))) none
      (canonFromD shippedBank (paState 5) ed25519PointAddShippedPart06) = true := by
  decide +kernel

theorem pa_part7 :
    partCheck2 1495 paSl7 paMap6 (some (aoWE (.v 1494))) none paMap7
      (some (.v 1747)) none
      (canonFromD shippedBank (paState 6) ed25519PointAddShippedPart07) = true := by
  decide +kernel

theorem pa_part8 :
    partCheck2 1748 paSl8 paMap7 (some (.v 1747)) none paMap8 none none
      (canonFromD shippedBank (paState 7) ed25519PointAddShippedPart08) = true := by
  decide +kernel

theorem pa_part9 :
    partCheck2 1996 paSl9 paMap8 none none paMap9 (some (aoWE (.v 2250)))
      none (canonFromD shippedBank (paState 8) ed25519PointAddShippedPart09) = true := by
  decide +kernel

theorem pa_part10 :
    partCheck2 2251 paSl10 paMap9 (some (aoWE (.v 2250))) none paOut none none
      (canonFromD shippedBank (paState 9) ed25519PointAddShippedPart10) = true := by
  decide +kernel




end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof
