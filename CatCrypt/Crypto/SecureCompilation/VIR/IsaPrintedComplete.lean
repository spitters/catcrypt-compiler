/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.LegalizeIsa

@[expose] public section

set_option autoImplicit false

/-!
# Completeness of a printed-class gate of an instruction set

The assembly simulation of an instruction set accepts a printed body through an instruction
gate `ok body c i` in a context `c` of the body. This module states, over a register file
`I : IsaAbi`, which instruction shapes such a gate must accept: the materialised comparison
`SETE:64 R, [A, B]` / `SETNE:64 R, [A, B]` and the count-`0` shift `SHL:64 R, R, #0`, each
over registers of the register file other than the stack pointer. A body each of whose
instructions before the last has one of these shapes or passes the gate passes the
instruction conjunct of the gate.

## Main definitions

* `IsaAbi.IsGp`: a register of the register file other than the stack pointer.
* `PrintedShape`: the materialised comparison and the count-`0` shift over such registers.
* `PrintedComplete`: the gate accepts both shapes in every body and every context.

## Main results

* `PrintedComplete.ok_of_shape`: the gate accepts every instruction of a printed shape.
* `PrintedComplete.all_of_shapes`: a body each of whose instructions before the last has a
  printed shape or passes the gate passes the gate on all of them.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

namespace IsaAbi

variable (abi : IsaAbi)

/-- **A general-purpose register** of the register file: a register (`IsReg`) other than the
    stack pointer. -/
def IsGp (n : String) : Prop := abi.IsReg n ∧ n ≠ abi.sp

instance (n : String) : Decidable (abi.IsGp n) := by
  unfold IsGp
  infer_instance

end IsaAbi

/-- **The printed shapes** over the register file `I`: the materialised comparison
    `SETE:64 R, [A, B]` (`n = false`) or `SETNE:64 R, [A, B]` (`n = true`) and the count-`0`
    shift `SHL:64 R, R, #0`, each over general-purpose registers of `I`. -/
def PrintedShape (I : IsaAbi) (i : LinstrR) : Prop :=
  (∃ (n : Bool) (R A B : String), I.IsGp R ∧ I.IsGp A ∧ I.IsGp B ∧
      i = .Lopn [.reg R] (if n then "SETNE:64" else "SETE:64") [.reg A, .reg B])
    ∨ ∃ R : String, I.IsGp R ∧ i = .Lopn [.reg R] "SHL:64" [.reg R, .imm 0]

/-- **Completeness of a printed-class gate** `ok` with contexts `Ctx` over the register file
    `I`: in every body and every context, `ok` accepts the materialised comparison
    `SETE:64 R, [A, B]` / `SETNE:64 R, [A, B]` and the count-`0` shift `SHL:64 R, R, #0`
    over general-purpose registers of `I`. -/
structure PrintedComplete (I : IsaAbi) (Ctx : Type) (ok : Lcmd → Ctx → LinstrR → Bool) :
    Prop where
  /-- The materialised comparison over general-purpose registers passes the gate. -/
  setcc : ∀ (body : Lcmd) (c : Ctx) (n : Bool) (R A B : String), I.IsGp R → I.IsGp A →
    I.IsGp B → ok body c (.Lopn [.reg R] (if n then "SETNE:64" else "SETE:64") [.reg A, .reg B])
      = true
  /-- The count-`0` shift of a general-purpose register in place passes the gate. -/
  shl0 : ∀ (body : Lcmd) (c : Ctx) (R : String), I.IsGp R →
    ok body c (.Lopn [.reg R] "SHL:64" [.reg R, .imm 0]) = true

namespace PrintedComplete

variable {I : IsaAbi} {Ctx : Type} {ok : Lcmd → Ctx → LinstrR → Bool}

/-- A complete gate accepts every instruction of a printed shape. -/
theorem ok_of_shape (h : PrintedComplete I Ctx ok) (body : Lcmd) (c : Ctx) {i : LinstrR}
    (hi : PrintedShape I i) : ok body c i = true := by
  rcases hi with ⟨n, R, A, B, hR, hA, hB, rfl⟩ | ⟨R, hR, rfl⟩
  · exact h.setcc body c n R A B hR hA hB
  · exact h.shl0 body c R hR

/-- **The instruction conjunct from the shapes**: under a complete gate, a body each of whose
    instructions before the last has a printed shape or passes the gate in the context
    `ctx body` passes the gate on all of them. -/
theorem all_of_shapes (h : PrintedComplete I Ctx ok) (ctx : Lcmd → Ctx) {body : Lcmd}
    (hb : ∀ i ∈ body.dropLast, PrintedShape I i.li_i ∨ ok body (ctx body) i.li_i = true) :
    body.dropLast.all (fun i => ok body (ctx body) i.li_i) = true := by
  rw [List.all_eq_true]
  intro i hi
  rcases hb i hi with hs | hok
  · exact h.ok_of_shape body (ctx body) hs
  · exact hok

end PrintedComplete

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
