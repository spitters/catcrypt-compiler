/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-!
# Wide / multi-pointer leaf ABI — the 4-pointer (modulus-as-pointer) witness

Keystone #2 (wide / array ABI) of `COMPILER_ROADMAP.md`. The backend scoping found
that the leaf calling convention is ALREADY general over up to six SysV
integer/pointer arguments via `AsmPrinter.intArgRegs` + `argMarshalMoves` — the
proven Montgomery kernels (`Curve4MontMulProvenEmit` &c.) already use a
**3-pointer** ABI `f(z, x, y)`. The smallest landable increment for #2 is the
**4-pointer** shape that passes the modulus as its own `reg ptr u64[N]` argument
instead of baking it as immediates: `montmul(z, x, y, p)`.

This file WITNESSES that shape with a proof — that the existing marshaller already
places the 4th pointer in its SysV home `%rcx` and emits exactly the one MULX-funnel
move — additive, reusing only proven infra. It does NOT touch `buildPrologue` /
`compileComToElf` (the larger owned-path N-pointer rework, which edits shared
restructure core and is coordinated separately).
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.WideAbiFourPtr

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-- A 4-pointer Montgomery-with-explicit-modulus leaf signature: result `z`, the two
    operands `x`/`y`, and the modulus `p` as its own pointer argument. -/
def montmul4Args : List AbiArg :=
  [⟨"z", .intPtr⟩, ⟨"x", .intPtr⟩, ⟨"y", .intPtr⟩, ⟨"p", .intPtr⟩]

/-- The Montgomery allocation: `z→%rdi`, `x→%rsi` are home; `y` is moved off the
    MULX funnel register `%rdx` to a free GPR `%r10`; the new 4th pointer `p` lands
    in its home `%rcx`. -/
def montmul4Alloc : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("y", "%r10"), ("p", "%rcx")]

/-- The 4th integer/pointer argument arrives in `%rcx` (its SysV home). -/
theorem fourth_ptr_home : intArgHome 3 = some "%rcx" := rfl

/-- **The 4-pointer ABI marshals correctly with the existing infra.** The only move
    emitted is freeing the MULX funnel `%rdx` into `%r10` for operand `y`; the result
    `z` (`%rdi`), operand `x` (`%rsi`) and the modulus `p` (`%rcx`) are all already
    home, so the modulus pointer needs no extra plumbing — the leaf ABI carries a
    4th pointer with zero new machinery. -/
theorem montmul4_marshal :
    argMarshalMoves montmul4Alloc montmul4Args = ["\tmovq %rdx, %r10"] := by
  rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.WideAbiFourPtr
