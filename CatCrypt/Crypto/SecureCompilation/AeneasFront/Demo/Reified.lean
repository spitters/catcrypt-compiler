/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.ReifyArrays
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestScalars
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestArrays
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestLoops
public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo.TestIterators

/-!
# `reifyAeneas%` on Aeneas test outputs

Six functions of the Aeneas test outputs (`TestScalars`, `TestArrays`, `TestLoops`,
`TestIterators`, copied unchanged from Aeneas commit `b08bf81`) read as NF programs by
`reifyAeneas%`, each with the statement that a value of the Aeneas function is, embedded, the denotation of its program in
the compiler's semantics `PDenP hax64WExit` from some fuel on (`Reify.toDenote`, the reifier's
proof by construction composed with `nfToRustM_sim`).

* straight-line scalar code: `scalars.add_and` (two lifted `&&&`, a checked `+`) and
  `scalars.u32_use_wrapping_add` (`core.num.U32.wrapping_add`);
* arrays: `arrays.index_array_u32` (`Array.index_usize`) and `arrays.incr_array` (an index, a
  checked `+` and an update at literal operands);
* a loop: `loops.iter_loop`, the Aeneas `loop` over `loops.iter_loop.body` (a branch on `<`,
  a checked `+` of a literal, `cont` and `done`), read as an exit-flag `whileLoop`;
* a range loop: `iterators.copy_arrays`, the Aeneas `loop` over the range `0..256` stepped by
  `IteratorRange.next`, whose step reads `src[i]` and writes it to `dst[i]`, read as a counted
  `forLoop` (`Reify.rangeForLoop`, through `loop_range` and `foldRangeAux`).

## Main results

* `addAnd_denote`, `useWrappingAdd_denote`, `indexArrayU32_denote`, `incrArray_denote`,
  `iterLoop_denote`, `copyArrays_denote`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo

open Aeneas.Std
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.AeneasFront
open CatCrypt.Crypto.Hax (hax64WExit)
open CatCrypt.Crypto.Hax.ImpToNF (PDenP)

/-- `scalars.add_and` read as an NF program. -/
def addAnd := reifyAeneas% scalars.add_and

/-- A value of `scalars.add_and` is the denotation of its NF program in the compiler's
    semantics. -/
theorem addAnd_denote (a b z : U32) (h : scalars.add_and a b = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel → PDenP hax64WExit fuel addAnd.prog (vCons a (vCons b vNil)) =
      some (.cons (embW z) .nil) :=
  Reify.toDenote (addAnd.sound a b) h

/-- `scalars.u32_use_wrapping_add` read as an NF program. -/
def useWrappingAdd := reifyAeneas% scalars.u32_use_wrapping_add

/-- A value of `scalars.u32_use_wrapping_add` is the denotation of its NF program. -/
theorem useWrappingAdd_denote (x y z : U32) (h : scalars.u32_use_wrapping_add x y = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel useWrappingAdd.prog (vCons x (vCons y vNil)) =
        some (.cons (embW z) .nil) :=
  Reify.toDenote (useWrappingAdd.sound x y) h

/-- `arrays.index_array_u32` read as an NF program. -/
def indexArrayU32 := reifyAeneas% arrays.index_array_u32

/-- A value of `arrays.index_array_u32` is the denotation of its NF program. -/
theorem indexArrayU32_denote (s : Aeneas.Std.Array U32 32#usize) (i : Usize) (z : U32)
    (h : arrays.index_array_u32 s i = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel indexArrayU32.prog (vCons s (vCons i vNil)) =
        some (.cons (embW z) .nil) :=
  Reify.toDenote (indexArrayU32.sound s i) h

/-- `arrays.incr_array` read as an NF program. -/
def incrArray := reifyAeneas% arrays.incr_array

/-- A value of `arrays.incr_array` is the denotation of its NF program. -/
theorem incrArray_denote (x y : Aeneas.Std.Array U32 2#usize)
    (h : arrays.incr_array x = .ok y) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel incrArray.prog (vCons x vNil) = some (.cons (embA y) .nil) :=
  Reify.toDenote (incrArray.sound x) h

/-- `loops.iter_loop`, an Aeneas `loop` over the body `loops.iter_loop.body`, read as an NF
    program with an exit-flag loop. -/
def iterLoop := reifyAeneas% loops.iter_loop

/-- A value of `loops.iter_loop` is the denotation of its NF program. -/
theorem iterLoop_denote (max i z : U32) (h : loops.iter_loop max i = .ok z) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel iterLoop.prog (vCons max (vCons i vNil)) =
        some (.cons (embW z) .nil) :=
  Reify.toDenote (iterLoop.sound max i) h

/-- `iterators.copy_arrays`, an Aeneas `loop` over the range `0..256`, read as an NF program
    with a counted loop. -/
def copyArrays := reifyAeneas% iterators.copy_arrays

/-- A value of `iterators.copy_arrays` is the denotation of its NF program. -/
theorem copyArrays_denote (src dst y : Aeneas.Std.Array U8 256#usize)
    (h : iterators.copy_arrays src dst = .ok y) :
    ∃ N, ∀ fuel, N ≤ fuel →
      PDenP hax64WExit fuel copyArrays.prog (vCons src (vCons dst vNil)) =
        some (.cons (embA y) .nil) :=
  Reify.toDenote (copyArrays.sound src dst) h

end CatCrypt.Crypto.SecureCompilation.AeneasFront.Demo
