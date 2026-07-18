/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Transfer.Base.Related
import CatCrypt.Crypto.SecureCompilation.X86Backend.Preservation

/-!
# The compiler's preservation lemmas, wired into the `Related` registry

Concrete realization of the relational-compilation ↔ Trocq connection
(`relational-compilation-trocq-connection.md`): the in-Lean x86 backend's
per-instruction **preservation lemmas** (`X86Backend.Preservation.*`) become
`RelatedBinOp` instances in the **same** `Trocq.Related` registry that hosts the
security-bridge realizations. Then the **same** `Related`-resolution engine that
composes a security transfer composes the **compiler's** per-instruction
value-preservation into a whole-expression value-preservation — confirming
compilation and proof-transfer are one construction at two relations (here, the
relation is "the emitted x86 op computes the abstract word op").

Each `x86⟨op⟩` is the pure binary function the emitted x86 instruction realizes
(run one `step`, read the destination), and `x86⟨op⟩_eq` is its preservation —
the `Preservation.⟨op⟩_preserves` lemma in pure form. Registering it as
`RelatedBinOp id (abstract op) (x86⟨op⟩)` puts the compiler step into the
registry; resolution does the rest, never inventing a preservation it wasn't given.
-/

set_option autoImplicit false

namespace Transfer

open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

variable {w : Nat}

/-- A two-register initial state binding `"x" ↦ a`, `"y" ↦ b`. -/
private def st2 (a b : BitVec w) : State w :=
  { regs := fun r => if r = "x" then a else if r = "y" then b else 0 }

/-! ## Per-instruction preservation in pure binary-function form -/

/-- The pure binary function the emitted x86 `ADD` realizes. -/
def x86Add (a b : BitVec w) : BitVec w := (step (st2 a b) (.add "x" (.reg "y"))).get "x"
/-- The pure binary function the emitted x86 `MUL` (low word) realizes. -/
def x86Mul (a b : BitVec w) : BitVec w := (step (st2 a b) (.mul "x" (.reg "y"))).get "x"
/-- The pure binary function the emitted x86 `XOR` realizes. -/
def x86Xor (a b : BitVec w) : BitVec w := (step (st2 a b) (.xor_ "x" (.reg "y"))).get "x"

/-- Compiler preservation (pure form): emitted x86 `ADD` computes `+`. -/
theorem x86Add_eq (a b : BitVec w) : x86Add a b = a + b := by
  unfold x86Add st2; rw [add_preserves]; rfl
/-- Compiler preservation (pure form): emitted x86 `MUL` computes `*`. -/
theorem x86Mul_eq (a b : BitVec w) : x86Mul a b = a * b := by
  unfold x86Mul st2; rw [mul_preserves]; rfl
/-- Compiler preservation (pure form): emitted x86 `XOR` computes `^^^`. -/
theorem x86Xor_eq (a b : BitVec w) : x86Xor a b = a ^^^ b := by
  unfold x86Xor st2; rw [xor_preserves]; rfl

/-! ## Wiring into the `Related` registry -/

/-- The compiler's `ADD` preservation as a registry entry. -/
instance relatedX86Add : RelatedBinOp (id : BitVec w → BitVec w) (· + ·) x86Add :=
  ⟨fun a b => (x86Add_eq a b).symm⟩
/-- The compiler's `MUL` preservation as a registry entry. -/
instance relatedX86Mul : RelatedBinOp (id : BitVec w → BitVec w) (· * ·) x86Mul :=
  ⟨fun a b => (x86Mul_eq a b).symm⟩
/-- The compiler's `XOR` preservation as a registry entry. -/
instance relatedX86Xor : RelatedBinOp (id : BitVec w → BitVec w) (· ^^^ ·) x86Xor :=
  ⟨fun a b => (x86Xor_eq a b).symm⟩

/-! ## The engine composes the compiler steps automatically

`Related`-resolution composes the registered per-instruction preservations into a
whole-expression value-preservation — no manual proof, the same way it composes a
security transfer. -/

/-- A composite word expression equals the composition of the emitted x86 ops it
    compiles to — derived purely by `Related` instance resolution over the wired
    compiler-preservation registry. -/
example (a b c : BitVec 64) : a * b + c = x86Add (x86Mul a b) c :=
  (inferInstance : Related (id : BitVec 64 → BitVec 64) (a * b + c) _).rel

/-- Another, mixing three emitted ops. -/
example (a b c d : BitVec 64) :
    (a + b) ^^^ (c * d) = x86Xor (x86Add a b) (x86Mul c d) :=
  (inferInstance : Related (id : BitVec 64 → BitVec 64) ((a + b) ^^^ (c * d)) _).rel

end Transfer
