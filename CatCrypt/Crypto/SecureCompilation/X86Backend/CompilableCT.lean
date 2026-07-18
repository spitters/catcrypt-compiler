/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-!
# Phase 0 — the compilable constant-time subset contract

This module names the **subset contract** shared by the compiler front (reject
out-of-subset input) and the backend (assume it). For a *secure* compiler over
the terminating hax subset we take the constant-time discipline as the policy:

> control flow, loop bounds, and memory indices are **public** — no secret value
> reaches a branch condition, a loop bound, or a memory address.

The three layers of the security story and where each lives:

* **Policy** — the CT discipline above. `CompilableCT` is its machine-level
  statement.
* **Enforcement** — the secret-type information-flow lattice
  (`Optimizer/SecretType.lean`'s `SecretLevel`, propagated by the
  `SecretType*` passes). It statically rejects a program whose secret labels
  flow into a branch/bound/index. (Phase 2 threads those labels end-to-end and
  discharges `CompilableCT` from a `public`-labelled control surface; the hook is
  recorded in §3.)
* **Guarantee** — `MachineConstantTime.blockLeak`: the leakage trace (control
  flow + memory addresses) of a `CompilableCT` leaf is a function of the program
  text alone, independent of every register value. This is the security target,
  discharged here by `CompilableCT.constant_time`.

At the machine level the CT policy is exactly **direct addressing**: every
instruction avoids the register-indexed `loadMemIdx`/`storeMemIdx` (the only
JInstr forms whose leak inspects a runtime — possibly secret — value), and the
straight-line subset has no conditional branch at all. That is precisely
`ConstantTimeCoverage.allDirect`, so `CompilableCT` is its `Prop` form, and the
guarantee is the already-proven `allDirect_constant_time`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CompilableCT

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-! ## 1. The contract -/

/-- **The compilable constant-time subset (machine level).** A straight-line leaf
    `block` is CT-compilable when every instruction uses direct (base +
    compile-time-constant) addressing — i.e. no `loadMemIdx`/`storeMemIdx` with a
    runtime register index, and (in the straight-line subset) no conditional
    branch. This is the policy the secret-type IF lattice enforces at the source/IR
    level and that `MachineConstantTime` discharges as a leakage guarantee. -/
def CompilableCT {w : Nat} (block : List (JInstr w)) : Prop :=
  allDirect block = true

/-- The contract is decidable — `allDirect` is a `Bool`, so the front can check
    (and reject) any candidate block by `decide`/`native_decide`. -/
instance {w : Nat} (block : List (JInstr w)) : Decidable (CompilableCT block) :=
  inferInstanceAs (Decidable (allDirect block = true))

/-- **The front-side checker.** `true` iff `block` is in the CT-compilable subset.
    The CLI runs this on the `cargo hax into lean`-extracted block and rejects
    (or marks unverified) anything that fails. -/
def compilableCT? {w : Nat} (block : List (JInstr w)) : Bool := allDirect block

@[simp] theorem compilableCT?_eq_true_iff {w : Nat} (block : List (JInstr w)) :
    compilableCT? block = true ↔ CompilableCT block := Iff.rfl

/-! ## 2. The guarantee — CT-compilable ⇒ constant-time -/

/-- **The security guarantee.** A `CompilableCT` leaf produces the **same**
    machine leakage trace from any two initial states `s₁ s₂`: its observable
    control-flow + memory-address sequence is a function of the program text
    alone, so it leaks nothing about register values (in particular secret
    inputs). This is `ConstantTimeCoverage.allDirect_constant_time` under the
    contract name — the end-to-end target the front+backend deliver. -/
theorem CompilableCT.constant_time {w : Nat} {block : List (JInstr w)}
    (h : CompilableCT block) (s₁ s₂ : JState w) :
    blockLeak s₁ block = blockLeak s₂ block :=
  allDirect_constant_time block h s₁ s₂

/-- The control-flow channel of a `CompilableCT` leaf is empty from any state —
    no conditional branch is taken (the branch half of constant-time). -/
theorem CompilableCT.no_branch {w : Nat} {block : List (JInstr w)}
    (_h : CompilableCT block) (s : JState w) :
    (blockLeak s block).filter MLeak.isBranch = [] :=
  allDirect_no_branch block s

/-! ## 3. Front rejection (Except form) + the Phase-2 IF-lattice hook

`checkCompilableCT` is the front's gate: it returns the block unchanged when it
is in the CT subset, or an error message naming the violation otherwise. The CLI
(`catcrypt-emit`) calls this between `cargo hax into lean` and the backend emit.

The Phase-2 hook: a richer contract will seed each operand with a `SecretLevel`
(from the hax/hacspec secret types) and require the *labels* of branch/bound/index
operands to be `public`. `CompilableCT` is the machine-level shadow of that
policy; threading the labels through the `SecretType*` passes and discharging this
predicate from a `public`-control-surface is Phase 2. -/

/-- The front gate: pass the block through iff it is CT-compilable, else report
    the violation. -/
def checkCompilableCT {w : Nat} (block : List (JInstr w)) :
    Except String (List (JInstr w)) :=
  if compilableCT? block then .ok block
  else .error "catcrypt: block is not in the constant-time subset \
    (a register-indexed memory access or a data-dependent branch reaches a \
    secret-derivable value); restrict to direct addressing / public control flow"

@[simp] theorem checkCompilableCT_ok {w : Nat} {block : List (JInstr w)}
    (h : CompilableCT block) : checkCompilableCT block = .ok block := by
  simp [checkCompilableCT, compilableCT?_eq_true_iff, h]

end CatCrypt.Crypto.SecureCompilation.X86Backend.CompilableCT
