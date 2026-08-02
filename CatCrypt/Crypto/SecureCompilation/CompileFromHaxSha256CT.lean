/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxSchedule
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxCompress
import CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction

/-!
# The compiled SHA-256 schedule and compression are constant-time by construction

The functional results (`fullSchedule_compiles`, `fullCompress_isSome` /
`compress1_value`) say the compiled `Com jasminDialect` computes the right value.
This file adds the **security** axis on the same artifacts: the compiled message
schedule and compression loop are in the **index-free fragment**
(`JasminCTByConstruction.ComJasminCTByConstruction`) — they bind no `stackLoad` /
`stackStore`, so there is no data-dependent control or addressing surface, hence no
secret can create a timing/address channel. The input reads resolve to the register
file (`inp` atoms), not data-indexed memory, so the whole program is constant-time
by construction.

Together with the functional theorems this is the two-axis end-to-end statement —
*the source compiles to a `Com` that is both value-correct and constant-time* — for
the real SHA-256 message schedule and compression round loop. (The machine-block CT
guarantee then follows once the `Com jasminDialect → machine` lowering's
CT-preservation — the register-allocator workstream — discharges
`SecureCompileChain.LoweringCTPreserving`.)
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha256CT

open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.JasminCTByConstruction
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxSchedule
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxCompress

set_option maxRecDepth 100000

/-- **The compiled full SHA-256 message schedule is constant-time by construction.**
    The `Com jasminDialect` produced for `schedProgram 64` (all 48 σ-recurrence
    writes) is in the index-free fragment — no `stackLoad`/`stackStore`, no
    data-dependent control surface — so `ComJasminCTByConstruction` holds. -/
theorem fullSchedule_compiled_is_CT :
    ComJasminCTByConstruction
      ((compileFromHax (w := 32) (nIn := 16) ["w"]
        (ImpExprToThir.schedProgram 64)).get fullSchedule_isSome) :=
  CompileFromHaxScope.compileFromHax_get_ct fullSchedule_isSome

/-- **The compiled full SHA-256 compression loop is constant-time by construction.**
    The `Com jasminDialect` produced for `compProgram 64` (all 64 rounds) is in the
    index-free fragment, so `ComJasminCTByConstruction` holds — the Σ/Ch/Maj round
    body and the array reads are pure register dataflow, no addressing surface. -/
theorem fullCompress_compiled_is_CT :
    ComJasminCTByConstruction
      ((compileFromHax (w := 32) (nIn := 72) ["in"] (compProgram 64)).get
        fullCompress_isSome) :=
  CompileFromHaxScope.compileFromHax_get_ct fullCompress_isSome

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSha256CT
