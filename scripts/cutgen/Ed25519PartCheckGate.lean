/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedParts
import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdModel

/-!
# The ed25519 part-check statements, evaluated

The correctness of the shipped `ed25519_point_add`, `ed25519_sc_reduce` and
`ed25519_sc_muladd` rests on twenty-seven part checks, each a `partCheck … = true` closed by
`decide +kernel`. The kernel checks cost gigabytes and do not build on a development box,
so a statement can fail against a re-imported block without any build reporting it.

This tool evaluates the same twenty-seven statements with the compiled evaluator, in
seconds, and exits non-zero when any is `false`. It adds no trust — the kernel proofs are
the artefact — and reports that a statement the proofs rest on has stopped holding. It
imports the executor, the models and the part maps, and none of the modules that hold the
checks.

    lake env lean scripts/cutgen/Ed25519PartCheckGate.lean
-/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScReduceShipped
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScMuladdShipped
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdShippedProof

/-- Each part check by its theorem name, beside the value of its statement. -/
def checks : List (String × Bool) :=
  [("pa_part1", partCheck2 57 paSl1 paIn none none paMap1 (some (aoWE (.v 238))) none
      (canonFromD shippedBank {} ed25519PointAddShippedPart01)),
   ("pa_part2", partCheck2 239 paSl2 paMap1 (some (aoWE (.v 238))) none paMap2 none none
      (canonFromD shippedBank (paState 1) ed25519PointAddShippedPart02)),
   ("pa_part3", partCheck2 499 paSl3 paMap2 none none paMap3 (some (.v 761)) none
      (canonFromD shippedBank (paState 2) ed25519PointAddShippedPart03)),
   ("pa_part4", partCheck2 762 paSl4 paMap3 (some (.v 761)) none paMap4 (some (.v 1019)) none
      (canonFromD shippedBank (paState 3) ed25519PointAddShippedPart04)),
   ("pa_part5", partCheck2 1020 paSl5 paMap4 (some (.v 1019)) none paMap5 (some (.v 1269))
      none (canonFromD shippedBank (paState 4) ed25519PointAddShippedPart05)),
   ("pa_part6", partCheck2 1270 paSl6 paMap5 (some (.v 1269)) none paMap6
      (some (aoWE (.v 1494))) none (canonFromD shippedBank (paState 5) ed25519PointAddShippedPart06)),
   ("pa_part7", partCheck2 1495 paSl7 paMap6 (some (aoWE (.v 1494))) none paMap7
      (some (.v 1747)) none (canonFromD shippedBank (paState 6) ed25519PointAddShippedPart07)),
   ("pa_part8", partCheck2 1748 paSl8 paMap7 (some (.v 1747)) none paMap8 none none
      (canonFromD shippedBank (paState 7) ed25519PointAddShippedPart08)),
   ("pa_part9", partCheck2 1996 paSl9 paMap8 none none paMap9 (some (aoWE (.v 2250))) none
      (canonFromD shippedBank (paState 8) ed25519PointAddShippedPart09)),
   ("pa_part10", partCheck2 2251 paSl10 paMap9 (some (aoWE (.v 2250))) none paOut none none
      (canonFromD shippedBank (paState 9) ed25519PointAddShippedPart10)),
   ("scr_part1", partCheck 16 (xSlice 16 64) scrIn scrMap1
      (canonFromD shippedBank {} ed25519ScReduceShippedPart01)),
   ("scr_part2", partCheck 64 (xSlice 64 116) scrMap1 scrMap2
      (canonFromD shippedBank (scrState 1) ed25519ScReduceShippedPart02)),
   ("scr_part3", partCheck 116 (xSlice 116 169) scrMap2 scrMap3
      (canonFromD shippedBank (scrState 2) ed25519ScReduceShippedPart03)),
   ("scr_part4", partCheck 169 (xSlice 169 219) scrMap3 scrMap4
      (canonFromD shippedBank (scrState 3) ed25519ScReduceShippedPart04)),
   ("scr_part5", partCheck 219 (xSlice 219 269) scrMap4 scrMap5
      (canonFromD shippedBank (scrState 4) ed25519ScReduceShippedPart05)),
   ("scr_part6", partCheck 269 (xSlice 269 320) scrMap5 scrMap6
      (canonFromD shippedBank (scrState 5) ed25519ScReduceShippedPart06)),
   ("scr_part7", partCheck 320 (xSlice 320 354) scrMap6 scrOut
      (canonFromD shippedBank (scrState 6) ed25519ScReduceShippedPart07)),
   ("scr_part8", partCheck 354 (xSlice 354 354) scrOut scrOut
      (canonFromD shippedBank (scrState 7) ed25519ScReduceShippedPart08)),
   ("scm_part1", partCheck 16 (mSlice 16 69) scmIn scmMap1
      (canonFromD shippedBank {} ed25519ScMuladdShippedPart01)),
   ("scm_part2", partCheck 69 (mSlice 69 114) scmMap1 scmMap2
      (canonFromD shippedBank (scmState 1) ed25519ScMuladdShippedPart02)),
   ("scm_part3", partCheck 114 (mSlice 114 165) scmMap2 scmMap3
      (canonFromD shippedBank (scmState 2) ed25519ScMuladdShippedPart03)),
   ("scm_part4", partCheck 165 (mSlice 165 219) scmMap3 scmMap4
      (canonFromD shippedBank (scmState 3) ed25519ScMuladdShippedPart04)),
   ("scm_part5", partCheck 219 (mSlice 219 269) scmMap4 scmMap5
      (canonFromD shippedBank (scmState 4) ed25519ScMuladdShippedPart05)),
   ("scm_part6", partCheck 269 (mSlice 269 319) scmMap5 scmMap6
      (canonFromD shippedBank (scmState 5) ed25519ScMuladdShippedPart06)),
   ("scm_part7", partCheck 319 (mSlice 319 369) scmMap6 scmMap7
      (canonFromD shippedBank (scmState 6) ed25519ScMuladdShippedPart07)),
   ("scm_part8", partCheck 369 (mSlice 369 416) scmMap7 scmMap8
      (canonFromD shippedBank (scmState 7) ed25519ScMuladdShippedPart08)),
   ("scm_part9", partCheck 416 (mSlice 416 434) scmMap8 scmOut
      (canonFromD shippedBank (scmState 8) ed25519ScMuladdShippedPart09))]

/-- Print every statement's value, and fail when any is `false`. The failure is an
    exception, so elaboration fails and `lake env lean` exits non-zero; a returned exit
    code would be discarded by `#eval`. -/
def gate : IO Unit := do
  let mut bad := 0
  for (n, b) in checks do
    IO.println s!"{if b then "ok   " else "FALSE"} {n}"
    if !b then bad := bad + 1
  IO.println s!"part-check gate: {checks.length - bad} of {checks.length} statements hold"
  if bad ≠ 0 then
    throw <| IO.userError s!"part-check gate: {bad} statement(s) do not hold"

#eval gate
