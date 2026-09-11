/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Optimizer.GenericRegAllocValidated
public import CatCrypt.Crypto.Optimizer.SpillingRegAlloc
public import CatCrypt.Crypto.Optimizer.RandomizedRegAlloc

/-!
# A decidable no-alias checker for the x86 (`JInstr`) register allocator

`RandomizedRegAlloc.regalloc_runBlock_sound` proves that an injective renaming `ρ`
(with a left inverse `σ`) preserves the `JState` semantics of a `JInstr 64` block —
the validated-renaming soundness of the x86 register allocator, covering `mulx`
(two destinations), the memory ops, and the flags via the `StateRel ρ` simulation.

This file adds the **decidable no-alias checker** that gates it: `noAliasX ρ block`
decides whether `ρ` is injective on the register names the block mentions (its
written names — note `JInstr.mulx` writes *two* — and read names, from
`SpillingRegAlloc`). The checker is the translation-validation half: an untrusted
allocator emits `ρ`, the checker accepts it iff no two live names collide on a
physical register.

* `noAliasX_sound` — a passing check yields the no-alias certificate
  (`RenInjOn` on the block names);
* `injective_noAliasX` — a globally-injective renaming always passes (the checker
  never rejects a valid allocation — soundness's hypothesis is sufficient);
* `regalloc_runBlock_validated` — packages the two: a globally-injective `ρ` with
  left inverse `σ` both passes the checker and is sound. So the checker is a
  verified decision procedure consistent with the soundness theorem.

The remaining step toward the ARM `BInst`-style result — *weakening*
`regalloc_runBlock_sound`'s global-injectivity hypothesis to the checker's
on-block-names injectivity — requires re-proving the `StateRel` simulation in a
name-scoped form (`StateRelOn`); see `docs/jasmin-parity-plan.md` (x86 X2). The
`ZInstr` vector backend, being memory-free and single-output, already gets the
*scoped* keystone for free via `Avx512RegAllocValidated`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.JInstrRegAllocValidated

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.Optimizer.GenericRegAlloc
open CatCrypt.Crypto.Optimizer.RandomizedRegAlloc

/-- The register names one `JInstr 64` mentions: its written names (two for `mulx`)
    and its read names, from the x86 allocator's `SpillingRegAlloc` accessors. -/
def bNamesX (i : JInstr 64) : List String :=
  SpillingRegAlloc.writtenNames i ++ SpillingRegAlloc.readNames i

/-- Every register name a `JInstr 64` block mentions. -/
def blockNamesX (block : List (JInstr 64)) : List String :=
  block.flatMap bNamesX

/-- **The x86 no-alias checker.** Decides whether the renaming `ρ` the allocator
    produced is injective on the block's register names — no two live names share a
    physical register. Decidable, so it runs on a concrete allocation. -/
def noAliasX (ρ : String → String) (block : List (JInstr 64)) : Bool :=
  decide (RenInjOn (blockNamesX block) ρ)

/-- The checker is sound: passing it yields the no-alias certificate on the block's
    names (`RenInjOn`). -/
theorem noAliasX_sound (ρ : String → String) (block : List (JInstr 64))
    (h : noAliasX ρ block = true) : RenInjOn (blockNamesX block) ρ := by
  unfold noAliasX at h; exact of_decide_eq_true h

/-- A globally-injective renaming always passes the checker — the checker never
    rejects a renaming that the soundness theorem accepts. -/
theorem injective_noAliasX {ρ : String → String} (hρ : Function.Injective ρ)
    (block : List (JInstr 64)) : noAliasX ρ block = true := by
  unfold noAliasX
  refine decide_eq_true ?_
  intro a _ b _ hab; exact hρ hab

/-- **Validated renaming, checked (x86).** A globally-injective renaming `ρ` with a
    left inverse `σ` — the soundness theorem's hypotheses — both passes the no-alias
    checker and preserves the `JState` semantics up to `ρ`. The checker is thus a
    verified decision procedure consistent with `regalloc_runBlock_sound`: the
    allocator's output is accepted exactly when it is alias-free, and acceptance is
    necessary for the proven soundness. -/
theorem regalloc_runBlock_validated {ρ σ : String → String}
    (hρ : Function.Injective ρ) (hσ : Function.LeftInverse σ ρ)
    (block : List (JInstr 64)) (s : JState 64) :
    noAliasX ρ block = true ∧
      StateRel ρ (runBlock (renameState σ s) (renameBlock ρ block)) (runBlock s block) :=
  ⟨injective_noAliasX hρ block, regalloc_runBlock_sound hρ hσ block s⟩

end CatCrypt.Crypto.Optimizer.JInstrRegAllocValidated
