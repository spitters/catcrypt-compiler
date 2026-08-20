/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-!
# Wide / multi-pointer leaf ABI — the 4- and 5-pointer (modulus-as-pointer) witnesses

Item #2 (wide / array ABI) of `COMPILER_ROADMAP.md`. The leaf calling convention
is general over up to six SysV integer/pointer arguments via
`AsmPrinter.intArgRegs` + `argMarshalMoves` — the proven Montgomery kernels
(`Curve4MontMulProvenEmit` &c.) already use a
**3-pointer** ABI `f(z, x, y)`. The next shape passes the modulus as its own
`reg ptr u64[N]` argument instead of baking it as immediates: the **4-pointer**
`montmul(z, x, y, p)`; the one after passes the reduction constant
`w = -p⁻¹ mod 2⁶⁴` as a fifth pointer, the **5-pointer** `montmul(z, x, y, p, w)`.

Each shape is witnessed here with a proof that the existing marshaller places the
new pointer in its SysV home register (`%rcx` for the 4th, `%r8` for the 5th) and
emits exactly the one MULX-funnel move `movq %rdx, %r10` — additive, reusing only
proven infra. It does NOT touch `buildPrologue` / `compileComToElf` (the larger
owned-path N-pointer rework, which edits shared restructure core and is coordinated
separately).

## Main results

* `fourth_ptr_home` / `fifth_ptr_home` — the 4th and 5th integer/pointer arguments
  arrive in their SysV homes `%rcx` (index 3) and `%r8` (index 4).
* `montmul4_marshal` / `montmul5_marshal` — under the Montgomery allocation the
  marshaller emits exactly `["\tmovq %rdx, %r10"]` for both shapes: the extra
  pointer arguments (`p`, `w`) are already home and need no plumbing, so the only
  move is freeing the MULX funnel `%rdx` for operand `y`.
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

/-- A 5-pointer Montgomery leaf signature: result `z`, the two operands `x`/`y`,
    the modulus `p`, and the reduction constant `w = -p⁻¹ mod 2⁶⁴` passed as its
    own pointer argument. -/
def montmul5Args : List AbiArg :=
  [⟨"z", .intPtr⟩, ⟨"x", .intPtr⟩, ⟨"y", .intPtr⟩, ⟨"p", .intPtr⟩, ⟨"w", .intPtr⟩]

/-- The Montgomery allocation for the 5-pointer shape: `z→%rdi`, `x→%rsi` are home;
    `y` is moved off the MULX funnel register `%rdx` to a free GPR `%r10`; the
    modulus `p` lands in its home `%rcx`; the new 5th pointer `w` lands in its home
    `%r8`. -/
def montmul5Alloc : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("y", "%r10"), ("p", "%rcx"), ("w", "%r8")]

/-- The 5th integer/pointer argument arrives in `%r8` (its SysV home). -/
theorem fifth_ptr_home : intArgHome 4 = some "%r8" := rfl

/-- **The 5-pointer ABI marshals correctly with the existing infra.** As in the
    4-pointer case the only move emitted is freeing the MULX funnel `%rdx` into
    `%r10` for operand `y`; the result `z` (`%rdi`), operand `x` (`%rsi`), the
    modulus `p` (`%rcx`) and the reduction constant `w` (`%r8`) are all already
    home, so the fifth pointer needs no extra plumbing — the leaf ABI carries a
    5th pointer with zero new machinery. -/
theorem montmul5_marshal :
    argMarshalMoves montmul5Alloc montmul5Args = ["\tmovq %rdx, %r10"] := by
  rfl

end CatCrypt.Crypto.SecureCompilation.X86Backend.WideAbiFourPtr
