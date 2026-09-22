/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519SymExec

/-!
# The `ed25519_sc_reduce` part checks, evaluated

Each part check of `Ed25519ScReduceShippedProof` is `partCheck … = true`, closed by
`decide +kernel`. This tool evaluates the same statements with the compiled evaluator,
so a statement that fails against the imported block shows as `false` in seconds,
without the gigabytes the kernel check costs.

    lake env lean scripts/cutgen/Ed25519ScReduceEval.lean
-/

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScReduceShipped
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

#eval IO.println s!"scr_part1: {partCheck 16 (xSlice 16 64) scrIn scrMap1 (canonFromD shippedBank {} ed25519ScReduceShippedPart01)}"
#eval IO.println s!"scr_part2: {partCheck 64 (xSlice 64 116) scrMap1 scrMap2 (canonFromD shippedBank (scrState 1) ed25519ScReduceShippedPart02)}"
#eval IO.println s!"scr_part3: {partCheck 116 (xSlice 116 169) scrMap2 scrMap3 (canonFromD shippedBank (scrState 2) ed25519ScReduceShippedPart03)}"
#eval IO.println s!"scr_part4: {partCheck 169 (xSlice 169 219) scrMap3 scrMap4 (canonFromD shippedBank (scrState 3) ed25519ScReduceShippedPart04)}"
#eval IO.println s!"scr_part5: {partCheck 219 (xSlice 219 269) scrMap4 scrMap5 (canonFromD shippedBank (scrState 4) ed25519ScReduceShippedPart05)}"
#eval IO.println s!"scr_part6: {partCheck 269 (xSlice 269 320) scrMap5 scrMap6 (canonFromD shippedBank (scrState 5) ed25519ScReduceShippedPart06)}"
#eval IO.println s!"scr_part7: {partCheck 320 (xSlice 320 354) scrMap6 scrOut (canonFromD shippedBank (scrState 6) ed25519ScReduceShippedPart07)}"
#eval IO.println s!"scr_part8: {partCheck 354 (xSlice 354 354) scrOut scrOut (canonFromD shippedBank (scrState 7) ed25519ScReduceShippedPart08)}"
