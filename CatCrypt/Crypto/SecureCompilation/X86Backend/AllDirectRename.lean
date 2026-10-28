/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
public import CatCrypt.Crypto.Optimizer.RandomizedRegAlloc

/-!
# Register renaming preserves direct addressing

A register renaming rewrites register names and never opcodes, and `IsDirect` is an opcode
property, so a renaming preserves `IsDirect` of an instruction (`allDirect_renameInstr`) and
`allDirect` of a block (`allDirect_renameBlock`). An aliasing-free allocation therefore
cannot turn a direct-addressed block into a secret-indexed one.

The two theorems live in the namespace
`CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarCompileCorrect`, whose compiler-correctness
theorem for the scalar fragment uses them.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarCompileCorrect

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc (renameBlock)

open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc in
/-- A renaming preserves `IsDirect`: it rewrites register *names*, never opcodes,
    and `IsDirect` excludes exactly the two register-indexed opcodes
    (`loadMemIdx`/`storeMemIdx`), whose constructor `renameInstr` preserves. -/
theorem allDirect_renameInstr (ρ : String → String) (i : JInstr 64) :
    IsDirect (renameInstr ρ i) ↔ IsDirect i := by
  cases i <;> simp [renameInstr, IsDirect]

open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc in
/-- A renaming preserves `allDirect` of a whole block. -/
theorem allDirect_renameBlock (ρ : String → String) (block : List (JInstr 64)) :
    allDirect (renameBlock ρ block) = allDirect block := by
  unfold allDirect renameBlock
  induction block with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons, List.all_cons, ih]
    rw [decide_eq_decide.mpr (allDirect_renameInstr ρ i)]

end CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarCompileCorrect
