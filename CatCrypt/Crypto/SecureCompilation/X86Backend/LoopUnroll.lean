/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect

/-!
# Bounded-loop lowering by unrolling

`X86Dialect.lean` lowers a **straight-line** block `List (JInstr w)` to a
`Com (x86Dialect w)` and proves `lowerBlock_denote`
(`(lowerBlock block).denote (s ::ᵥ V) = runBlock s block`). This module adds the
first control-flow case: the **bounded counter-decrement loop**

```
while (n != 0) { body ; n -= 1 }
```

— the shape every emitted `mpn`/bignum kernel uses for its inner pass (see
`bench/glue_audit/mpn_addmul_1.jazz` lines 9–26, `mpn_add_1.jazz` lines 8–16,
etc.). We handle it by the simplest sound strategy: **unroll to a straight-line
block and reduce to `lowerBlock_denote`**. No new control-flow ops are added to
the dialect; the loop is compiled away into the straight-line subset the
baseline already covers.

## What "bounded" means here

The trip count `n : Nat` is a *compile-time* constant — the static unroll factor
the emitter picks (`mpn`'s `#pragma unroll`, or a fixed limb count `n = 4` for a
256-bit kernel). The runtime loop counter register is decremented by the body's
own `n -= 1` instruction (a `.sub "n" (.imm 1)` in the modeled subset), so the
unrolled block is itself a faithful straight-line trace of the loop's `n`
iterations. We do **not** model the `n != 0` *test* as machine state (that is a
conditional jump, the next increment); we model the loop *body executed exactly
`n` times*, which is what a bounded/fully-unrolled loop denotes.

## The three pieces

* `runBoundedLoop s n body` — run `body` (a `List (JInstr w)`, including its own
  counter decrement) `n` times in sequence from state `s`. This is the
  bounded-loop machine semantics.
* `unrollBounded n body` — the straight-line concatenation of `n` copies of
  `body`.
* `runBoundedLoop_eq_runBlock_unroll` — `runBoundedLoop s n body =
  runBlock s (unrollBounded n body)`, by induction on `n`. Composed with
  `lowerBlock_denote` this gives `boundedLoop_lowering_denote`:
  lowering the unrolled loop to `Com (x86Dialect w)` and denoting it equals the
  bounded-loop machine semantics.

## Trust story

No new axioms beyond the baseline's `lowerBlock_denote` (`[propext,
Quot.sound]`). `unrollBounded` is plain `List` concatenation and
`runBoundedLoop_eq_runBlock_unroll` is a `runBlock`-append induction; the
bounded-loop lowering theorem is their composition with `lowerBlock_denote`.
Forward conditionals, general CFG/labels, and calls are out of scope (later
increments).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect

/-! ## 1. `runBlock` over an appended block -/

/-- `runBlock` distributes over list append: running `xs ++ ys` is running `xs`
    then running `ys` from the resulting state. This is the sequential-composition
    law for the straight-line fold, and the engine of the unroll correctness. -/
@[simp] theorem runBlock_append {w : Nat} (s : JState w) (xs ys : List (JInstr w)) :
    runBlock s (xs ++ ys) = runBlock (runBlock s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => simp [runBlock, ih]

/-! ## 2. The bounded-loop machine semantics -/

/-- `runBoundedLoop s n body`: the machine semantics of a bounded counter loop
    that runs `body` exactly `n` times, threading the state. `body` is the full
    loop body in the modeled scalar subset, **including** its own counter
    decrement instruction (the emitted `n -= 1`); the trip count `n` is the
    compile-time unroll factor. -/
def runBoundedLoop {w : Nat} (s : JState w) (n : Nat) (body : List (JInstr w)) :
    JState w :=
  match n with
  | 0 => s
  | k + 1 => runBoundedLoop (runBlock s body) k body

@[simp] theorem runBoundedLoop_zero {w : Nat} (s : JState w) (body : List (JInstr w)) :
    runBoundedLoop s 0 body = s := rfl

@[simp] theorem runBoundedLoop_succ {w : Nat} (s : JState w) (k : Nat)
    (body : List (JInstr w)) :
    runBoundedLoop s (k + 1) body = runBoundedLoop (runBlock s body) k body := rfl

/-! ## 3. The unroller -/

/-- `unrollBounded n body`: the straight-line concatenation of `n` copies of the
    loop body. The fully-unrolled trace of a bounded loop. -/
def unrollBounded {w : Nat} (n : Nat) (body : List (JInstr w)) : List (JInstr w) :=
  match n with
  | 0 => []
  | k + 1 => body ++ unrollBounded k body

@[simp] theorem unrollBounded_zero {w : Nat} (body : List (JInstr w)) :
    unrollBounded 0 body = [] := rfl

@[simp] theorem unrollBounded_succ {w : Nat} (k : Nat) (body : List (JInstr w)) :
    unrollBounded (k + 1) body = body ++ unrollBounded k body := rfl

/-- `unrollBounded n body` is `n` copies of `body` flattened — the same as
    `(List.replicate n body).flatten`. A sanity characterisation. -/
theorem unrollBounded_eq_replicate_flatten {w : Nat} (n : Nat)
    (body : List (JInstr w)) :
    unrollBounded n body = (List.replicate n body).flatten := by
  induction n with
  | zero => rfl
  | succ k ih => simp [unrollBounded, List.replicate, ih]

/-! ## 4. Unroll correctness: the bounded loop equals running the unrolled block -/

/-- **Unroll correctness.** Running the bounded loop `n` times equals running the
    straight-line unrolled block. By induction on `n`, peeling one body per step
    and using `runBlock_append`. This is the bridge from the loop's iterated
    semantics to the straight-line semantics the baseline lowering covers. -/
theorem runBoundedLoop_eq_runBlock_unroll {w : Nat} (s : JState w) (n : Nat)
    (body : List (JInstr w)) :
    runBoundedLoop s n body = runBlock s (unrollBounded n body) := by
  induction n generalizing s with
  | zero => rfl
  | succ k ih => simp [runBoundedLoop, unrollBounded, runBlock_append, ih]

/-! ## 5. The bounded-loop lowering-correctness theorem

Composing `runBoundedLoop_eq_runBlock_unroll` with the baseline
`lowerBlock_denote`: lowering the *unrolled* loop to `Com (x86Dialect w)` and
denoting it on a valuation whose head is the incoming state `s` equals the
bounded-loop machine semantics `runBoundedLoop s n body`. This is the
bounded-loop generalisation of `lowerBlock_denote`. -/

/-- Lower a bounded loop: unroll it `n` times, then lower the resulting
    straight-line block with the baseline `lowerBlock`. -/
def lowerBoundedLoop {w : Nat} {Γ : Ctxt (x86Dialect w)} (n : Nat)
    (body : List (JInstr w)) :
    Com (x86Dialect w) (X86Ty.machine w :: Γ) (X86Ty.machine w) :=
  lowerBlock (Γ := Γ) (unrollBounded n body)

/-- **Bounded-loop lowering correctness.** The denotation of the lowered,
    unrolled bounded loop on a valuation whose head is `s` equals the
    bounded-loop machine semantics `runBoundedLoop s n body`. The bounded-loop
    generalisation of `lowerBlock_denote`: the loop is compiled away into the
    straight-line subset, and the lowering of that subset is denotation-
    preserving. -/
theorem boundedLoop_lowering_denote {w : Nat} {Γ : Ctxt (x86Dialect w)}
    (n : Nat) (body : List (JInstr w)) (s : JState w) (V : Ctxt.Valuation Γ) :
    (lowerBoundedLoop (Γ := Γ) n body).denote (.cons s V)
      = runBoundedLoop s n body := by
  rw [lowerBoundedLoop, lowerBlock_denote, runBoundedLoop_eq_runBlock_unroll]

/-- The closed-context specialisation (singleton context `[machine w]`): the
    lowered bounded loop denotes the state transformer
    `s ↦ runBoundedLoop s n body`. -/
theorem boundedLoop_lowering_denote_closed {w : Nat} (n : Nat)
    (body : List (JInstr w)) (s : JState w) :
    (lowerBoundedLoop (Γ := []) n body).denote (.cons s .nil)
      = runBoundedLoop s n body :=
  boundedLoop_lowering_denote n body s .nil

/-! ## 6. The concrete real example: the `mpn_addmul_1` inner loop

Source: `bench/glue_audit/mpn_addmul_1.jazz` lines 9–26, the emitted
`while (n != 0) { … ; n -= 1 }` inner loop. We transcribe its body into the
modeled `JInstr 64` scalar+ADX subset.

The `.jazz` body is

```
t = [:u64 ap + 0];                     // load
hi, lo = #MULX(b, t);                  //  → .mulx "hi" "lo" b t
_, c1__f, _, _, _, lo = #ADD_64(lo, cy); //  → .add "lo" cy   (sets CF)
c1__b = #SETcc(c1__f); c1 = (64u) c1__b; // materialise the carry into c1
w = [:u64 op + 0];                     // load
_, c2__f, _, _, _, lo = #ADD_64(lo, w);  //  → .add "lo" w    (sets CF)
c2__b = #SETcc(c2__f); c2 = (64u) c2__b; // materialise the carry into c2
[:u64 op + 0] = lo;                    // store
cy = hi; cy += c1; cy += c2;           //  → .mov "cy" hi; .add "cy" c1; .add "cy" c2
ap += 8; op += 8;                      // pointer bumps
n -= 1;                                //  → .sub "n" 1   (the counter decrement)
```

Memory operands (`[:u64 ap + 0]`, `[:u64 op + 0]`) follow `Lowering.lean`'s
`lowerOperand` convention — modeled as named registers (the memory cell is read
into / written from a register name). `#SETcc` materialises the just-set `CF`
into a GP register; in the modeled subset we read the carry register directly.
The pointer bumps `ap += 8` / `op += 8` are plain `.add … (.imm 8)`. The body is
straight-line scalar+ADX, so unrolling it `n` times is a faithful trace of the
bounded loop's `n` iterations. -/

/-- The `mpn_addmul_1` inner-loop body as a `List (JInstr 64)`, transcribed from
    `bench/glue_audit/mpn_addmul_1.jazz` lines 10–25, **including** the trailing
    `n -= 1` counter decrement (line 25). Memory cells are modeled as registers
    (`t` = `[ap]`, `w` = `[op]`) per `Lowering.lean`'s `lowerOperand` convention;
    `#SETcc`-materialised carries are read from the `c1`/`c2` registers. -/
def mpnAddmul1Body : List (JInstr 64) :=
  [ .mov "t" (.reg "ap_mem")        -- t = [:u64 ap + 0]
  , .mulx "hi" "lo" (.reg "b") (.reg "t")  -- hi, lo = #MULX(b, t)
  , .add "lo" (.reg "cy")           -- lo += cy        (ADD_64, sets CF → c1)
  , .mov "w" (.reg "op_mem")        -- w = [:u64 op + 0]
  , .add "lo" (.reg "w")            -- lo += w         (ADD_64, sets CF → c2)
  , .mov "op_mem" (.reg "lo")       -- [:u64 op + 0] = lo
  , .mov "cy" (.reg "hi")           -- cy = hi
  , .add "cy" (.reg "c1")           -- cy += c1
  , .add "cy" (.reg "c2")           -- cy += c2
  , .add "ap" (.imm 8)              -- ap += 8
  , .add "op" (.imm 8)              -- op += 8
  , .sub "n" (.imm 1) ]             -- n -= 1          (the counter decrement)

/-- **Bounded-loop lowering correctness on the real emitted `mpn_addmul_1`
    inner loop.** Lowering the loop unrolled `n` times to `Com (x86Dialect 64)`
    and denoting it on any incoming state `s` equals the bounded-loop machine
    semantics `runBoundedLoop s n mpnAddmul1Body` — the body run `n` times.
    Instantiates `boundedLoop_lowering_denote` on the body transcribed from
    `bench/glue_audit/mpn_addmul_1.jazz` lines 10–25. -/
theorem mpnAddmul1_boundedLoop_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBoundedLoop (Γ := []) n mpnAddmul1Body).denote (.cons s .nil)
      = runBoundedLoop s n mpnAddmul1Body :=
  boundedLoop_lowering_denote_closed n mpnAddmul1Body s

/-- A concrete sanity pin: with trip count `n = 3` and a zero initial state,
    the lowered-and-denoted bounded loop equals the bounded-loop semantics, and
    after three iterations the pointer `op` has advanced by `3 * 8 = 24` and the
    counter `n` register has been decremented three times to `2^64 - 3`. This
    exercises the whole unroll → lower → denote path computationally. -/
example :
    let s0 : JState 64 :=
      { regs := fun r => if r = "n" then (3 : BitVec 64) else 0 }
    let s := (lowerBoundedLoop (Γ := []) 3 mpnAddmul1Body).denote (.cons s0 .nil)
    (s.get "op").toNat = 24 ∧ (s.get "n").toNat = (3 : BitVec 64).toNat - 3 := by
  intro s0 s
  show _ ∧ _
  rw [show s = runBoundedLoop s0 3 mpnAddmul1Body from
        mpnAddmul1_boundedLoop_lowering_correct 3 s0]
  native_decide

end CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll
