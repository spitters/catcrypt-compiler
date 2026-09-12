/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Transfer.Base.Related
public import CatCrypt.Crypto.SecureCompilation.X86Backend.Preservation
public import CatCrypt.Crypto.Bridges.Transfer.CompilerRegistry

/-!
# The rest of the x86 backend's binops, wired into the `Related` registry

This extends `CompilerRegistry.lean` (which wired `ADD`/`MUL`/`XOR`) to the
remaining modeled two-address ALU opcodes: `SUB`, `AND`, `OR`, `SHL`, `SHR`.
The construction is identical — each emitted x86 op becomes the pure binary
function it realizes (run one `step`, read the destination), its preservation
lemma (`X86Backend.Preservation.⟨op⟩_preserves`) is restated in pure binary
form, and that pure form is registered as a `RelatedBinOp` witness in the same
`Trocq.Related` registry. The `Related`-resolution engine then composes these
per-instruction preservations into whole-expression value-preservations with no
manual proof — the same engine that composes a security transfer.

## Why `SHL`/`SHR` use named abstract ops

`Related`-resolution keys on syntactic heads. The shift's abstract op is
`a <<< b.toNat`, which is *not* of the form `?op a b` for a head-constant `?op`
(the head is `HShiftLeft.hShiftLeft`, but the second operand is `b.toNat`, not
`b`). A bare lambda `fun a b => a <<< b.toNat` likewise has no constant head for
the `composeBinOp` higher-order pattern to match. So `SHL`/`SHR` are registered
against the named functions `abstractShl`/`abstractShr` (constant heads), and
expressions are written with those heads. `SUB`/`AND`/`OR` need no such wrapper:
`·-·`, `·&&&·`, `·|||·` already present head-constant binary operations.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

variable {w : Nat}

/-! ## Named abstract shift ops (head-constant, for resolution)

The shift's natural abstract form `a <<< b.toNat` has no head-constant binary
operator for `Related`-resolution to key on; these named wrappers supply one. -/

/-- Abstract logical left shift by `b.toNat` — head-constant form of `· <<< ·.toNat`. -/
def abstractShl (a b : BitVec w) : BitVec w := a <<< b.toNat
/-- Abstract logical right shift by `b.toNat` — head-constant form of `· >>> ·.toNat`. -/
def abstractShr (a b : BitVec w) : BitVec w := a >>> b.toNat

/-! ## Per-instruction preservation in pure binary-function form -/

/-- The pure binary function the emitted x86 `SUB` realizes. -/
def x86Sub (a b : BitVec w) : BitVec w := (step (st2 a b) (.sub "x" (.reg "y"))).get "x"
/-- The pure binary function the emitted x86 `AND` realizes. -/
def x86And (a b : BitVec w) : BitVec w := (step (st2 a b) (.and_ "x" (.reg "y"))).get "x"
/-- The pure binary function the emitted x86 `OR` realizes. -/
def x86Or  (a b : BitVec w) : BitVec w := (step (st2 a b) (.or_ "x" (.reg "y"))).get "x"
/-- The pure binary function the emitted x86 `SHL` realizes. -/
def x86Shl (a b : BitVec w) : BitVec w := (step (st2 a b) (.shl "x" (.reg "y"))).get "x"
/-- The pure binary function the emitted x86 `SHR` realizes. -/
def x86Shr (a b : BitVec w) : BitVec w := (step (st2 a b) (.shr "x" (.reg "y"))).get "x"

/-- Compiler preservation (pure form): emitted x86 `SUB` computes `-`. -/
theorem x86Sub_eq (a b : BitVec w) : x86Sub a b = a - b := by
  unfold x86Sub st2; rw [sub_preserves]; rfl
/-- Compiler preservation (pure form): emitted x86 `AND` computes `&&&`. -/
theorem x86And_eq (a b : BitVec w) : x86And a b = a &&& b := by
  unfold x86And st2; rw [and_preserves]; rfl
/-- Compiler preservation (pure form): emitted x86 `OR` computes `|||`. -/
theorem x86Or_eq (a b : BitVec w) : x86Or a b = a ||| b := by
  unfold x86Or st2; rw [or_preserves]; rfl
/-- Compiler preservation (pure form): emitted x86 `SHL` computes `abstractShl`. -/
theorem x86Shl_eq (a b : BitVec w) : x86Shl a b = abstractShl a b := by
  unfold x86Shl abstractShl st2; rw [shl_preserves]; rfl
/-- Compiler preservation (pure form): emitted x86 `SHR` computes `abstractShr`. -/
theorem x86Shr_eq (a b : BitVec w) : x86Shr a b = abstractShr a b := by
  unfold x86Shr abstractShr st2; rw [shr_preserves]; rfl

/-! ## Wiring into the `Related` registry -/

/-- The compiler's `SUB` preservation as a registry entry. -/
instance relatedX86Sub : RelatedBinOp (id : BitVec w → BitVec w) (· - ·) x86Sub :=
  ⟨fun a b => (x86Sub_eq a b).symm⟩
/-- The compiler's `AND` preservation as a registry entry. -/
instance relatedX86And : RelatedBinOp (id : BitVec w → BitVec w) (· &&& ·) x86And :=
  ⟨fun a b => (x86And_eq a b).symm⟩
/-- The compiler's `OR` preservation as a registry entry. -/
instance relatedX86Or : RelatedBinOp (id : BitVec w → BitVec w) (· ||| ·) x86Or :=
  ⟨fun a b => (x86Or_eq a b).symm⟩
/-- The compiler's `SHL` preservation as a registry entry. -/
instance relatedX86Shl : RelatedBinOp (id : BitVec w → BitVec w) abstractShl x86Shl :=
  ⟨fun a b => (x86Shl_eq a b).symm⟩
/-- The compiler's `SHR` preservation as a registry entry. -/
instance relatedX86Shr : RelatedBinOp (id : BitVec w → BitVec w) abstractShr x86Shr :=
  ⟨fun a b => (x86Shr_eq a b).symm⟩

/-! ## Single-op resolution

Each registered op resolves on its own — the leaf-plus-one-commuting-square base
case. -/

/-- Resolution composes a single registered `SUB`. -/
example (a b : BitVec 64) : a - b = x86Sub a b :=
  (inferInstance : Related (id : BitVec 64 → BitVec 64) (a - b) _).rel
/-- Resolution composes a single registered `AND`. -/
example (a b : BitVec 64) : a &&& b = x86And a b :=
  (inferInstance : Related (id : BitVec 64 → BitVec 64) (a &&& b) _).rel
/-- Resolution composes a single registered `OR`. -/
example (a b : BitVec 64) : a ||| b = x86Or a b :=
  (inferInstance : Related (id : BitVec 64 → BitVec 64) (a ||| b) _).rel
/-- Resolution composes a single registered `SHL`. -/
example (a b : BitVec 64) : abstractShl a b = x86Shl a b :=
  (inferInstance : Related (id : BitVec 64 → BitVec 64) (abstractShl a b) _).rel
/-- Resolution composes a single registered `SHR`. -/
example (a b : BitVec 64) : abstractShr a b = x86Shr a b :=
  (inferInstance : Related (id : BitVec 64 → BitVec 64) (abstractShr a b) _).rel

/-! ## The engine composes the compiler steps automatically

`Related`-resolution composes the registered per-instruction preservations into a
whole-expression value-preservation — no manual proof, the same way it composes a
security transfer. -/

/-- Composition demo mixing `SUB`, `AND`, and `SHL`: the composite word
    expression equals the composition of the emitted x86 ops it compiles to,
    derived purely by `Related` instance resolution over the wired
    compiler-preservation registry. -/
example (a b c d : BitVec 64) :
    (a - b) &&& (abstractShl c d) = x86And (x86Sub a b) (x86Shl c d) :=
  (inferInstance : Related (id : BitVec 64 → BitVec 64) ((a - b) &&& (abstractShl c d)) _).rel

/-- A larger composite mixing `OR`, `SUB`, `SHR`, and `AND` across four nested
    emitted ops — still closed by a single instance-resolution call. -/
example (a b c d e : BitVec 64) :
    ((a ||| b) - (abstractShr c d)) &&& e
      = x86And (x86Sub (x86Or a b) (x86Shr c d)) e :=
  (inferInstance : Related (id : BitVec 64 → BitVec 64)
    (((a ||| b) - (abstractShr c d)) &&& e) _).rel

end Transfer
