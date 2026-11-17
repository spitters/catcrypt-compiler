/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.ReifySlices
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.HaxArrays

/-!
# `reifyAeneas%` on slices and arrays of arrays of the hax Lean backend

Six functions of the output of the hax 0.4.2 Lean backend on the Aeneas test crate `arrays`
(`HaxArrays`, copied unchanged) read as NF programs by `reifyAeneas%`, each with the statement
that a value of the function is, embedded, the denotation of its program in the compiler's
semantics `PDenP hax64WExit` from some fuel on (`Reify.toDenote`).

* the indexing of an array of arrays: `arrays.index_index_array`, read by `reifyE_aaIndex` and
  `reifyE_index`;
* the update of slices of `u32` words at variable indices: `arrays.array_update1`,
  `arrays.array_update2`, `arrays.array_update3`, read by `reifyE_supdate`;
* the indexing and update of a slice at a literal index: `arrays.index_slice_u32_0`,
  `arrays.incr_slice`, read by `reifyE_sindex` and `reifyE_supdate` with the literal bound first.

## Main results

* `indexIndexArray_denote`, `arrayUpdate1_denote`, `arrayUpdate2_denote`,
  `arrayUpdate3_denote`, `indexSliceU32_0_denote`, `incrSlice_denote`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.Hax

open Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.AeneasFront
open CatCrypt.Crypto.Hax (hax64WExit)
open CatCrypt.Crypto.Hax.ImpToNF (PDenP)

/-- `arrays.index_index_array` read as an NF program. -/
def indexIndexArray := reifyAeneas% arrays.index_index_array

/-- A value of `arrays.index_index_array` is the denotation of its NF program. -/
theorem indexIndexArray_denote (s : Aeneas.Std.Array (Aeneas.Std.Array U32 32#usize) 32#usize)
    (i j : Usize) (z : U32) (h : arrays.index_index_array s i j = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel indexIndexArray.prog (vCons s (vCons i (vCons j vNil))) =
        some (.cons (embW z) .nil) :=
  Reify.toDenote (indexIndexArray.sound s i j) h

/-- `arrays.array_update1` read as an NF program. -/
def arrayUpdate1 := reifyAeneas% arrays.array_update1

/-- A value of `arrays.array_update1` is the denotation of its NF program. -/
theorem arrayUpdate1_denote (a : Slice U32) (i : Usize) (x : U32) (z : Slice U32)
    (h : arrays.array_update1 a i x = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel arrayUpdate1.prog (vCons a (vCons i (vCons x vNil))) =
        some (.cons (embS z) .nil) :=
  Reify.toDenote (arrayUpdate1.sound a i x) h

/-- `arrays.array_update2` read as an NF program. -/
def arrayUpdate2 := reifyAeneas% arrays.array_update2

/-- A value of `arrays.array_update2` is the denotation of its NF program. -/
theorem arrayUpdate2_denote (a : Slice U32) (i : Usize) (x : U32) (z : Slice U32)
    (h : arrays.array_update2 a i x = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel arrayUpdate2.prog (vCons a (vCons i (vCons x vNil))) =
        some (.cons (embS z) .nil) :=
  Reify.toDenote (arrayUpdate2.sound a i x) h

/-- `arrays.array_update3` read as an NF program. -/
def arrayUpdate3 := reifyAeneas% arrays.array_update3

/-- A value of `arrays.array_update3` is the denotation of its NF program. -/
theorem arrayUpdate3_denote (a : Slice U32) (i : Usize) (x : U32) (z : Slice U32)
    (h : arrays.array_update3 a i x = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel arrayUpdate3.prog (vCons a (vCons i (vCons x vNil))) =
        some (.cons (embS z) .nil) :=
  Reify.toDenote (arrayUpdate3.sound a i x) h

/-- `arrays.index_slice_u32_0` read as an NF program. -/
def indexSliceU32_0 := reifyAeneas% arrays.index_slice_u32_0

/-- A value of `arrays.index_slice_u32_0` is the denotation of its NF program. -/
theorem indexSliceU32_0_denote (x : Slice U32) (z : U32)
    (h : arrays.index_slice_u32_0 x = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel indexSliceU32_0.prog (vCons x vNil) = some (.cons (embW z) .nil) :=
  Reify.toDenote (indexSliceU32_0.sound x) h

/-- `arrays.incr_slice` read as an NF program. -/
def incrSlice := reifyAeneas% arrays.incr_slice

/-- A value of `arrays.incr_slice` is the denotation of its NF program. -/
theorem incrSlice_denote (x z : Slice U32) (h : arrays.incr_slice x = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel incrSlice.prog (vCons x vNil) = some (.cons (embS z) .nil) :=
  Reify.toDenote (incrSlice.sound x) h

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.Hax
