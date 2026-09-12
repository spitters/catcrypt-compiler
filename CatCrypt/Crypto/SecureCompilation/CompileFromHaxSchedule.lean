/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.CompileFromHax
public import CatCrypt.Crypto.SecureCompilation.CompileFromHax

/-!
# The SHA-256 message schedule compiles end to end (value-correct)

§9 of `ImpExprToThir` proves the **general-N** message-schedule preservation
`schedProgram_denoteScalar`: the unrolled σ-recurrence

```text
  W[i] = σ₁(W[i-2]) + W[i-7] + σ₀(W[i-15]) + W[i-16]      (i = 16 .. N-1)
```

denotes (under the source semantics `denoteScalar`) to the array-state
fold `schedFold`. That is the front-IR half. This file supplies the missing
**`compileFromHax`-level** tie: routing `schedProgram_denoteScalar` through the C3
meta-theorem `compileFromHax_meets_spec` gives that the *compiled* `Com
jasminDialect` denotes to `schedFold` — value-correct against FIPS 180-4.

* `schedProgram_compiles_value` — **general N** (`16 < N`), conditional on the
  program compiling: whenever `compileFromHax (schedProgram N) = some c`, the
  compiled `c` denotes to `schedFold (inpGet I) (N-16) (N-1)` (the `W[N-1]` the
  schedule returns).
* `fullSchedule_isSome` / `fullSchedule_compiles` — the **full** SHA-256 message
  schedule (`N = 64`, all 48 writes `W[16..63]`) compiles and is value-correct,
  unconditionally (compilation success discharged by `native_decide`). The whole
  message-schedule function, from a high-level (hax-shaped) source, end to end.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxSchedule

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.CompileFromHax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-! ## §1  General-N value-correctness (conditional on compilation) -/

/-- **The σ-message-schedule is value-correct (general N).** For any `16 < N`,
    whenever the §9 schedule program `schedProgram N` compiles
    (`compileFromHax … = some c`), the compiled `Com jasminDialect` `c` denotes to
    exactly the FIPS 180-4 array-state value `schedFold (inpGet I) (N-16) (N-1)` —
    the returned word `W[N-1]`. Routes §9's `schedProgram_denoteScalar` through the
    C3 meta-theorem `compileFromHax_meets_spec`. -/
theorem schedProgram_compiles_value {N : Nat} (hlt : 16 < N) (I : Fin 16 → BitVec 32)
    {c : Com jasminDialect (frontCtxt 32 16 []) (rW 32)}
    (hc : compileFromHax (w := 32) (nIn := 16) ["w"] (schedProgram N) = some c) :
    c.denote (inputValuation 32 16 I) = schedFold (inpGet I) (N - 16) (N - 1) :=
  compileFromHax_meets_spec (w := 32) (nIn := 16) ["w"] I (schedProgram N) _ hc
    (schedProgram_denoteScalar I N hlt)

/-! ## §2  The full SHA-256 message schedule (N = 64, all 48 writes) -/

/-- The full SHA-256 message schedule (`N = 64`: writes `W[16..63]`) compiles
    through the unchanged `compileFromHax`. -/
theorem fullSchedule_isSome :
    (compileFromHax (w := 32) (nIn := 16) ["w"] (schedProgram 64)).isSome := by
  native_decide

/-- **The full SHA-256 message schedule compiles, value-correct.** There is a
    compiled `Com jasminDialect` `c` such that `schedProgram 64` (all 48 σ-recurrence
    writes `W[16..63]`, from the 16 input message words) compiles to `c`, and for
    every input `I`, `c` denotes to exactly the FIPS 180-4 schedule value at the
    final word `W[63] = schedFold (inpGet I) 48 63`. The whole message-schedule
    function, from a high-level source, end to end. -/
theorem fullSchedule_compiles :
    ∃ c : Com jasminDialect (frontCtxt 32 16 []) (rW 32),
      compileFromHax (w := 32) (nIn := 16) ["w"] (schedProgram 64) = some c ∧
      ∀ I : Fin 16 → BitVec 32,
        c.denote (inputValuation 32 16 I) = schedFold (inpGet I) 48 63 := by
  refine ⟨_, (Option.some_get fullSchedule_isSome).symm, fun I => ?_⟩
  have h := schedProgram_compiles_value (N := 64) (by norm_num) I
    (Option.some_get fullSchedule_isSome).symm
  simpa using h

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxSchedule
