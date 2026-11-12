/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.ReifyArrays
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Iterators
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestIterAdapters

/-!
# `reifyAeneas%` on loops over iterator adapters

The three functions of `AeneasFront.Demo.TestIterAdapters`, each a loop over an iterator
adapter, read as NF programs by `reifyAeneas%`: the adapter state is built by binds whose value
the reader computes, and the loop is the counted `forLoop` of `Reify.indexedForLoop` at the
instances `enumRangeIter`, `enumArrayIter` and `zipArrayIter` of `AeneasFront.Iterators`. Each
comes with the statement that a value of the function is, embedded, the denotation of its
program in the compiler's semantics `PDenP hax64WExit` from some fuel on (`Reify.toDenote`).

## Main results

* `enumRangeSum_denote`, `enumArraySum_denote`, `zipArraySum_denote`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo

open Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.AeneasFront
open CatCrypt.Crypto.Hax (hax64WExit)
open CatCrypt.Crypto.Hax.ImpToNF (PDenP)

/-- `iter_adapters.enum_range_sum` read as an NF program. -/
def enumRangeSum := reifyAeneas% iter_adapters.enum_range_sum

/-- A value of `enum_range_sum` is the denotation of its NF program. -/
theorem enumRangeSum_denote (a : Aeneas.Std.Array U32 4#usize) (acc z : U32)
    (h : iter_adapters.enum_range_sum a acc = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel enumRangeSum.prog (vCons a (vCons acc vNil)) =
        some (.cons (embW z) .nil) :=
  Reify.toDenote (enumRangeSum.sound a acc) h

/-- `iter_adapters.enum_array_sum` read as an NF program. -/
def enumArraySum := reifyAeneas% iter_adapters.enum_array_sum

/-- A value of `enum_array_sum` is the denotation of its NF program. -/
theorem enumArraySum_denote (a b : Aeneas.Std.Array U32 4#usize) (acc z : U32)
    (h : iter_adapters.enum_array_sum a b acc = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel enumArraySum.prog (vCons a (vCons b (vCons acc vNil))) =
        some (.cons (embW z) .nil) :=
  Reify.toDenote (enumArraySum.sound a b acc) h

/-- `iter_adapters.zip_array_sum` read as an NF program. -/
def zipArraySum := reifyAeneas% iter_adapters.zip_array_sum

/-- A value of `zip_array_sum` is the denotation of its NF program. -/
theorem zipArraySum_denote (a b : Aeneas.Std.Array U32 4#usize) (acc z : U32)
    (h : iter_adapters.zip_array_sum a b acc = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel zipArraySum.prog (vCons a (vCons b (vCons acc vNil))) =
        some (.cons (embW z) .nil) :=
  Reify.toDenote (zipArraySum.sound a b acc) h

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo
