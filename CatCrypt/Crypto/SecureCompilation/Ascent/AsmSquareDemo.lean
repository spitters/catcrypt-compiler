/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.SquareStrict

/-!
# Demo: the correspondence square over an x86 block

A two-limb subtract-with-borrow chain, `r0 -= s0` then `r1 -= s1 - CF`, carried
through the square algebra of `SquareStrict.lean`. The same five steps appear in
`RustMSquareDemo.lean` over `RustM`, in the same order, so the two sides can be
read side by side.

1. A leg: `sbb_as_triple` is the square of one `sbb` instruction.
2. Horizontal composition: `RunBlockTriple.hcomp` concatenates the two legs, and
   the composite is stated over the two-instruction literal, which the
   concatenation reduces to.
3. The horizontal identity: the empty block absorbs on the left by `rfl` and on
   the right along `List.append_nil`.
4. The vertical direction: a `VMapJ` strengthens the entry relation to a chain
   that starts without a borrow and weakens the exit relation to the registers,
   and `vsquareJ_act` applies it.
5. A state in the entry relation, so the demo constrains something.

## Main results

* `sbb2_square` — the two-limb chain refines the composed `sbbStep` fold.
* `sbb2_hid_left`, `sbb2_hid_right` — the empty block on either side of the
  chain gives back the same proof.
* `sbb2_regs_only` — the chain read at the weakened boundary.
* `sbb2_entry_inhabited` — a machine state and an abstract state in the entry
  relation of `sbb2_regs_only`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos

open CatCrypt.Crypto.SecureCompilation.Ascent
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-- The abstract effect of the chain: the borrow out of limb 0 is the borrow limb 1
    reads. -/
def sbb2 (a : ACarry) : ACarry := sbbStep "r1" "s1" (sbbStep "r0" "s0" a)

/-! ## 1. The two legs -/

/-- Limb 0, from `SRcarry` at `a`. -/
theorem sbb2_leg0 (a : ACarry) :
    RunBlockTriple (fun st => SRcarry st a) [.sbb "r0" (.reg "s0")]
      (fun st => SRcarry st (sbbStep "r0" "s0" a)) :=
  sbb_as_triple "r0" "s0" a

/-- Limb 1, from the exit relation of limb 0. -/
theorem sbb2_leg1 (a : ACarry) :
    RunBlockTriple (fun st => SRcarry st (sbbStep "r0" "s0" a)) [.sbb "r1" (.reg "s1")]
      (fun st => SRcarry st (sbb2 a)) :=
  sbb_as_triple "r1" "s1" (sbbStep "r0" "s0" a)

/-! ## 2. Horizontal composition -/

/-- **The composite.** The two legs concatenate, and `[i₀] ++ [i₁]` reduces to the
    two-instruction literal, so the composite is stated over the block itself with no
    transport. -/
theorem sbb2_square (a : ACarry) :
    RunBlockTriple (fun st => SRcarry st a)
      [.sbb "r0" (.reg "s0"), .sbb "r1" (.reg "s1")]
      (fun st => SRcarry st (sbb2 a)) :=
  (sbb2_leg0 a).hcomp (sbb2_leg1 a)

/-! ## 3. The horizontal identity -/

/-- The empty block on the left gives back the same proof. -/
theorem sbb2_hid_left (a : ACarry) :
    (RunBlockTriple.hid (fun st => SRcarry st a)).hcomp (sbb2_square a) = sbb2_square a :=
  rfl

/-- The empty block on the right gives back the same proof, transported along
    `l ++ [] = l`. -/
theorem sbb2_hid_right (a : ACarry) :
    List.append_nil [JInstr.sbb "r0" (.reg "s0"), JInstr.sbb "r1" (.reg "s1")]
        ▸ ((sbb2_square a).hcomp (RunBlockTriple.hid (fun st => SRcarry st (sbb2 a))))
      = sbb2_square a :=
  rfl

/-! ## 4. The vertical direction -/

/-- A vertical arrow: the chain starts without a borrow in, and the exit relation is
    read on the registers alone. -/
theorem noBorrowIn (a : ACarry) :
    VMapJ (fun st => SRcarry st a) (fun st => SRcarry st a ∧ a.cf = false)
      (fun st => SRcarry st (sbb2 a)) (fun st => ∀ r, st.regs r = (sbb2 a).regs r) where
  hP := fun _ h => h.1
  hQ := fun _ h => h.1

/-- **The chain at the weakened boundary**, by the action of `noBorrowIn`. -/
theorem sbb2_regs_only (a : ACarry) :
    RunBlockTriple (fun st => SRcarry st a ∧ a.cf = false)
      [.sbb "r0" (.reg "s0"), .sbb "r1" (.reg "s1")]
      (fun st => ∀ r, st.regs r = (sbb2 a).regs r) :=
  vsquareJ_act (sbb2_square a) (noBorrowIn a)

/-! ## 5. The entry relation is inhabited -/

/-- A machine state and an abstract state in the entry relation of `sbb2_regs_only`:
    all registers zero, the carry flag clear. -/
theorem sbb2_entry_inhabited :
    ∃ st a, SRcarry st a ∧ a.cf = false :=
  ⟨{ regs := fun _ => 0, flags := { cf := some false, of := none } },
    { regs := fun _ => 0, cf := false }, ⟨fun _ => rfl, rfl⟩, rfl⟩

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos
