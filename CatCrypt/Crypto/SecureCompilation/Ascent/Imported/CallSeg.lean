/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel

/-!
# Imported functions with calls

`JInstr` has no call instruction. An x86-64 function imported by
`bench/s2n_import/import_owned.sh` that contains `call SYM` is represented as a list
of `CallSeg` values: each is a run of `JInstr 64` instructions followed by the symbol
of the `call` that ends the run, or by nothing. The function is the concatenation of
the runs, with each recorded call executed after its run. A run whose `callee` is
`none` is followed directly by the next run; the importer divides long runs this way.

The semantics of a call is not part of `JasminModel`. A proof over an imported
function supplies, for each callee, a specification of its effect on registers and
memory, and composes it with `runBlock` over the runs.

## Main definitions

* `CallSeg`: a run of instructions and the call that ends it.
* `CallSeg.instrs`: the instructions of a list of runs, in order.
* `CallSeg.callees`: the called symbols of a list of runs, in order.

## Main results

* `CallSeg.instrs_append`, `CallSeg.callees_append`: both commute with `++`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Imported

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- A run of instructions of an imported function, followed by the `call` of
    `callee` when `callee = some sym`. -/
structure CallSeg where
  /-- The instructions of the run, in order. -/
  body : List (JInstr 64)
  /-- The symbol of the `call` after the run, if any. -/
  callee : Option String
  deriving Repr

/-- The instructions of a list of runs, in order, with the calls removed. -/
def CallSeg.instrs (fs : List CallSeg) : List (JInstr 64) :=
  fs.flatMap CallSeg.body

/-- The called symbols of a list of runs, in order. -/
def CallSeg.callees (fs : List CallSeg) : List String :=
  fs.filterMap CallSeg.callee

/-- The instructions of a concatenation are the concatenated instructions. -/
theorem CallSeg.instrs_append (a b : List CallSeg) :
    CallSeg.instrs (a ++ b) = CallSeg.instrs a ++ CallSeg.instrs b :=
  List.flatMap_append

/-- The calls of a concatenation are the concatenated calls. -/
theorem CallSeg.callees_append (a b : List CallSeg) :
    CallSeg.callees (a ++ b) = CallSeg.callees a ++ CallSeg.callees b :=
  List.filterMap_append

end CatCrypt.Crypto.SecureCompilation.Ascent.Imported
