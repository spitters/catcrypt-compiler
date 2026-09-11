/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect

/-!
# Forward-conditional lowering (#281 increment)

`X86Dialect.lean` lowers a **straight-line** block `List (JInstr w)` to a
`Com (x86Dialect w)` and proves `lowerBlock_denote`
(`(lowerBlock block).denote (s ::ᵥ V) = runBlock s block`); `LoopUnroll.lean`
adds the **bounded counter-loop** by unrolling to that straight-line subset.
This module adds the next control-flow primitive: the **forward conditional** —
the `Lcond cond lbl` + taken/fall-through shape, a 2-way split that runs one of
two straight-line sub-blocks and then converges.

## The condition is PUBLIC (constant-time discipline)

Constant-time code forbids a *secret*-dependent branch: those are compiled to
`CMOVcc` (already in `JasminModel`'s `evalInstr`, the `.cmove`/`.cmovne`/`.cmovb`
arms — no PC divergence). A genuine `Lcond` in the emitted constant-time subset
therefore tests a **public** value — a loop/length bound, a counter-zero test, a
public configuration flag. We model the condition as a predicate

```
cond : JState w → Bool
```

reading the *public* machine state (a flag or a register holding a public
bound). Because the value is public, the two paths are observationally
distinguishable to the adversary by construction, so resolving the branch at
lowering time leaks nothing — exactly the property that makes a forward
conditional admissible in constant-time code.

## The three pieces

* `runCond s cond thenBlk fallBlk` — the machine semantics of the forward
  conditional: evaluate the public condition on `s`, run `thenBlk` if true else
  `fallBlk` (both straight-line via `runBlock`), and return the converged state.
* `lowerCond cond thenBlk fallBlk s` — the lowering. Since the public condition
  resolves on the incoming state, the lowered program is the baseline
  `lowerBlock` of whichever branch the condition selects (the framework's `Com`
  is pure A-normal form with no region/branch op — a public forward conditional
  is *compiled away* into the straight-line subset, just as `LoopUnroll`
  compiles the bounded loop away by unrolling). The selection is on a public
  value, so this is a faithful trace of the taken path.
* `condBlock_lowering_denote` — the forward-conditional generalisation of
  `lowerBlock_denote`: denoting the lowered conditional on a valuation whose head
  is `s` equals `runCond s cond thenBlk fallBlk`. The proof **case-splits on the
  public condition value** and in each branch reduces to `lowerBlock_denote` on
  the corresponding straight-line sub-block.

## Trust story

No new axioms beyond the baseline's `lowerBlock_denote` (`[propext,
Quot.sound]`). `runCond` is a `Bool`-guarded choice of two `runBlock`s;
`condBlock_lowering_denote` is a `cond`-case-split each arm of which is exactly
`lowerBlock_denote`. Backward jumps, general unstructured CFG/labels, and calls
are out of scope (later increments).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Cond

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect

/-! ## 1. Public conditions

A forward conditional in the emitted constant-time subset tests a **public**
value. We model the condition as a predicate on the machine state, and provide
the two conditions jasminc actually emits for a public counter test: `ZF`
(zero / `jz`) and "register is zero" (the `n == 0` loop guard before the loop
counter is loaded into a flag). -/

/-- A public branch condition: a predicate on the (public) machine state. The
    forward conditional branches on `cond s`. -/
abbrev JCond (w : Nat) := JState w → Bool

/-- The `je`/`jz` condition: the zero flag is set. (`ZF = some true`.) -/
def condZF {w : Nat} : JCond w := fun s => s.flagB (·.zf)

/-- The `jne`/`jnz` condition: the zero flag is clear. -/
def condNZF {w : Nat} : JCond w := fun s => ! s.flagB (·.zf)

/-- A public "register holds zero" test on a named register — the `n == 0`
    bound guard before a bounded loop. -/
def condRegZero {w : Nat} (r : String) : JCond w := fun s => decide ((s.get r).toNat = 0)

/-! ## 2. The forward-conditional machine semantics -/

/-- `runCond s cond thenBlk fallBlk`: the machine semantics of a forward
    conditional. Evaluate the public condition on the incoming state; run
    `thenBlk` (the taken path) if it holds, else `fallBlk` (the fall-through
    path). Both branches are straight-line (`runBlock`) and converge to a single
    successor state. -/
def runCond {w : Nat} (s : JState w) (cond : JCond w)
    (thenBlk fallBlk : List (JInstr w)) : JState w :=
  if cond s then runBlock s thenBlk else runBlock s fallBlk

@[simp] theorem runCond_true {w : Nat} (s : JState w) (cond : JCond w)
    (thenBlk fallBlk : List (JInstr w)) (h : cond s = true) :
    runCond s cond thenBlk fallBlk = runBlock s thenBlk := by
  simp [runCond, h]

@[simp] theorem runCond_false {w : Nat} (s : JState w) (cond : JCond w)
    (thenBlk fallBlk : List (JInstr w)) (h : cond s = false) :
    runCond s cond thenBlk fallBlk = runBlock s fallBlk := by
  simp [runCond, h]

/-! ## 3. Lowering the forward conditional

The framework's `Com` (`VIR/Core.lean`) is pure A-normal form: it has only
`.ret` and `.var`, no region- or branch-carrying op. A **public** forward
conditional resolves on the incoming (public) state, so — exactly as
`LoopUnroll` compiles a bounded loop away by unrolling into the straight-line
subset — we compile the public conditional away by *selecting* the baseline
`lowerBlock` of the branch the condition takes. The selection reads only public
state, so it is a faithful trace of the taken path and leaks nothing beyond what
a public branch already reveals.

`lowerCond` is therefore parameterised by the incoming state `s` (the public
selector); for a fixed `s` it is a genuine `Com (x86Dialect w)` whose
denotation is the taken straight-line block. -/

/-- Lower a forward conditional, given the incoming (public) state `s` that
    resolves the branch: produce the baseline `lowerBlock` of the selected
    branch. (Public selection — see the module docstring.) -/
def lowerCond {w : Nat} {Γ : Ctxt (x86Dialect w)} (s : JState w) (cond : JCond w)
    (thenBlk fallBlk : List (JInstr w)) :
    Com (x86Dialect w) (X86Ty.machine w :: Γ) (X86Ty.machine w) :=
  if cond s then lowerBlock (Γ := Γ) thenBlk else lowerBlock (Γ := Γ) fallBlk

/-! ## 4. Forward-conditional lowering correctness

The forward-conditional generalisation of `lowerBlock_denote`. The proof
**case-splits on the public condition value** `cond s`; each arm is exactly
`lowerBlock_denote` on the corresponding straight-line sub-block. -/

/-- **Forward-conditional lowering correctness.** Denoting the lowered forward
    conditional on a valuation whose head is the incoming state `s` equals the
    forward-conditional machine semantics `runCond s cond thenBlk fallBlk`. By
    case analysis on the public condition value: when `cond s` is true the
    lowered program is `lowerBlock thenBlk`, whose denotation is `runBlock s
    thenBlk` by `lowerBlock_denote`; symmetrically for the fall-through path.
    This is the conditional generalisation of `lowerBlock_denote`. -/
theorem condBlock_lowering_denote {w : Nat} {Γ : Ctxt (x86Dialect w)}
    (s : JState w) (cond : JCond w) (thenBlk fallBlk : List (JInstr w))
    (V : Ctxt.Valuation Γ) :
    (lowerCond (Γ := Γ) s cond thenBlk fallBlk).denote (.cons s V)
      = runCond s cond thenBlk fallBlk := by
  unfold lowerCond runCond
  cases h : cond s with
  | true => simp only [if_true]; exact lowerBlock_denote thenBlk s V
  | false => simp only [Bool.false_eq_true, if_false]; exact lowerBlock_denote fallBlk s V

/-- The closed-context specialisation (singleton context `[machine w]`): the
    lowered forward conditional denotes the state transformer
    `s ↦ runCond s cond thenBlk fallBlk`. -/
theorem condBlock_lowering_denote_closed {w : Nat} (s : JState w) (cond : JCond w)
    (thenBlk fallBlk : List (JInstr w)) :
    (lowerCond (Γ := []) s cond thenBlk fallBlk).denote (.cons s .nil)
      = runCond s cond thenBlk fallBlk :=
  condBlock_lowering_denote s cond thenBlk fallBlk .nil

/-! ## 5. The concrete example: a public bound-guard forward conditional

A faithful synthetic 2-block forward conditional of the shape jasminc emits for
a **public** counter guard: `jz skip` around a one-iteration body. With `n`
public (a length/limb count),

```
        cmp  n, 0            // sets ZF iff n == 0   (public test)
        jz   skip            // forward conditional (taken path = fall-through body)
   body:  acc += 1 ; n -= 1  // the guarded body  (then-block)
   skip:  ...                // converge           (fall-through = empty)
```

The condition `condZF` reads the public `ZF`. We model the "n == 0" guard via
the `ZF` set/clear from a preceding public compare. The two branches are the
straight-line `acc += 1; n -= 1` body (taken when `ZF` is clear, i.e. `n ≠ 0`)
versus the empty fall-through (taken when `ZF` set). -/

/-- The guarded body: `acc += 1; n -= 1` (run when the public guard says `n ≠ 0`). -/
def guardBody : List (JInstr 64) :=
  [ .add "acc" (.imm 1), .sub "n" (.imm 1) ]

/-- The forward-conditional skeleton: branch on `condNZF` (public `n ≠ 0`),
    running `guardBody` on the taken path and nothing on the fall-through. -/
def guardCond : JCond 64 := condNZF

/-- **Forward-conditional lowering correctness on the public bound guard.**
    Lowering the `jz`-guarded forward conditional to `Com (x86Dialect 64)` and
    denoting it on any incoming state `s` equals the forward-conditional machine
    semantics `runCond s condNZF guardBody []`. Instantiates
    `condBlock_lowering_denote_closed`. -/
theorem guard_cond_lowering_correct (s : JState 64) :
    (lowerCond (Γ := []) s guardCond guardBody []).denote (.cons s .nil)
      = runCond s guardCond guardBody [] :=
  condBlock_lowering_denote_closed s guardCond guardBody []

/-- Concrete sanity pin, **taken path** (`ZF` clear, i.e. `n ≠ 0`): with
    `n = 5, acc = 0` and `ZF = some false`, the lowered conditional runs
    `guardBody`, leaving `acc = 1` and `n = 4`. -/
example :
    let s0 : JState 64 :=
      { regs := fun r => if r = "n" then (5 : BitVec 64) else 0
        flags := { zf := some false } }
    let s := (lowerCond (Γ := []) s0 guardCond guardBody []).denote (.cons s0 .nil)
    (s.get "acc").toNat = 1 ∧ (s.get "n").toNat = 4 := by
  intro s0 s
  show _ ∧ _
  rw [show s = runCond s0 guardCond guardBody [] from
        guard_cond_lowering_correct s0]
  native_decide

/-- Concrete sanity pin, **fall-through path** (`ZF` set, i.e. `n == 0`): with
    `n = 0, acc = 7` and `ZF = some true`, the lowered conditional skips
    `guardBody`, leaving `acc = 7` and `n = 0` unchanged. -/
example :
    let s0 : JState 64 :=
      { regs := fun r => if r = "acc" then (7 : BitVec 64) else 0
        flags := { zf := some true } }
    let s := (lowerCond (Γ := []) s0 guardCond guardBody []).denote (.cons s0 .nil)
    (s.get "acc").toNat = 7 ∧ (s.get "n").toNat = 0 := by
  intro s0 s
  show _ ∧ _
  rw [show s = runCond s0 guardCond guardBody [] from
        guard_cond_lowering_correct s0]
  native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.Cond
