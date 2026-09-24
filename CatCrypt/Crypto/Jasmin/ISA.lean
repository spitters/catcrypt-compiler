/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JasminTranslate

/-!
# ISA Abstraction for Jasmin Compiler Targets

The class `JasminISA` parametrizes the Jasmin backend over an instruction set
architecture: a type of assembly programs, a compiler, an assembly semantics,
and the correctness of the compiler against `translateProg`. The front-end
pipeline (constant folding, nop elimination) is ISA-independent.

## Main definitions

* `JasminISA` — class of ISA targets with assembly type, compiler, semantics
  and compiler correctness

Client code (e.g. `AESEndToEnd.lean`) is parametric over `[JasminISA]`. An
instance for AArch64 can take its semantics from LNSym, one for RISC-V from the
Sail model's Lean backend.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin

set_option autoImplicit false

/-- An instruction set architecture for the Jasmin compiler backend.
    Each ISA provides a type for compiled assembly programs, a compiler
    function, an assembly semantics, and the correctness of the compiler
    against the Jasmin source-level translation. -/
class JasminISA where
  /-- Type of compiled assembly programs for this ISA. -/
  AsmProg : Type
  /-- Jasmin compiler targeting this ISA. -/
  compile : JasminProg → Option AsmProg
  /-- Abstract semantics of an assembly program (returns a computation
      given an entry point and arguments). -/
  asmSemantics : AsmProg → FunName → List TypedValue → Option (CatCrypt.Deep.RawCode (List TypedValue))
  /-- Compiler correctness: if compilation succeeds, the assembly semantics
      agree with the Jasmin source-level translation for all entry points
      and arguments. -/
  compilerCorrect : ∀ (p : JasminProg) (xp : AsmProg) (entry : FunName)
    (args : List TypedValue) (fuel : Nat),
    compile p = some xp →
    ∀ code, translateProg p entry args fuel = some code →
    asmSemantics xp entry args = some code

end CatCrypt.Crypto.Jasmin
