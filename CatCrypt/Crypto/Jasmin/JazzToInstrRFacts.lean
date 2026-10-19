/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JazzToInstrR
public meta import CatCrypt.Crypto.Jasmin.JazzToInstrR

/-!
# The output types of the asm operations of the op table

`opnNoneTys op n` types the discarded outputs `_` of a call of the asm operation `op` with
`n` outputs (`JazzToInstrR.asmOutTys`). This module evaluates it at the 64-bit operations
the lowering `nfToJasmin` emits. The table reads the operation name through
`String.splitOn` and `String.toNat?`, which do not reduce under `decide`; the values are
computed by `native_decide`, in a module that imports no part of the emit front.

## Main results

* `opnNoneTys_ADD_64`, `opnNoneTys_ADC_64`, `opnNoneTys_NEG_64`: five flags and a word.
* `opnNoneTys_CMP_64`: five flags.
* `opnNoneTys_MULX_64`: no entry; the outputs of `MULX_lo_hi_64` are typed `u64`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.JazzToInstrR

/-- The `_` outputs of `ADD_64`: five flags and a word. -/
theorem opnNoneTys_ADD_64 :
    opnNoneTys "ADD_64" 6 = List.replicate 5 .sbool ++ [.sword .U64] := by native_decide

/-- The `_` outputs of `ADC_64`: five flags and a word. -/
theorem opnNoneTys_ADC_64 :
    opnNoneTys "ADC_64" 6 = List.replicate 5 .sbool ++ [.sword .U64] := by native_decide

/-- The `_` outputs of `NEG_64`: five flags and a word. -/
theorem opnNoneTys_NEG_64 :
    opnNoneTys "NEG_64" 6 = List.replicate 5 .sbool ++ [.sword .U64] := by native_decide

/-- The `_` outputs of `CMP_64`: five flags. -/
theorem opnNoneTys_CMP_64 : opnNoneTys "CMP_64" 5 = List.replicate 5 .sbool := by
  native_decide

/-- `MULX_lo_hi_64` has no entry in the output table; its `_` outputs are typed `u64`. -/
theorem opnNoneTys_MULX_64 : opnNoneTys "MULX_lo_hi_64" 2 = [] := by native_decide

end CatCrypt.Crypto.Jasmin.JazzToInstrR
