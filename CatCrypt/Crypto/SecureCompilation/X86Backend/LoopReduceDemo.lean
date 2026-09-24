/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JForProgIndexed
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgIndexed
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LoopCarriedDemo
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoopCarriedDemo

/-!
# Array-reduction loop emit — `v := v + a[i]` over a memref

`CounterLoopDemo` / `LoopCarriedDemo` lower a **counter-reading** loop body
`(acc, ctr) ↦ acc ⊕ ctr` (resp. `acc + ctr`) through the verified x86
counter-loop emit (`cforIdxToLprogAbiBodyZeroAcc`, body context `[accTy, .reg 64]`)
and tie its denotation to a reference (`xorUpTo` / `sumUpTo`). There the
loop-carried value is fed by the **loop counter** (`ctr = n - i`), not by a value
loaded from a caller-supplied **array**. That counter-reading body context has no
pointer/array slot — it is exactly `[accTy, .reg 64]` (acc, counter).

This module treats the **array reduction** `v := v + a[i]` for
`i = 0 .. n-1`, where the per-iteration summand `a[i]` is **loaded from a base
array** each iteration, not read off the counter. The body therefore needs an
array/pointer slot in its context. We use the three-slot body context
`JForProgIndexed.tabCtxt (.reg 64) nRC = [.reg 64, .reg 64, .stackArr 64 nRC]`
(`acc`, loop-index register `idx`, the array `a`), whose abstract `execCom`
denotation tie is `JForProgIndexed.loopRunT_eq_denoteT` and is what
the x86 emit must realise.

## What this module proves

1. **The array-reduction body** `arrSumBody nRC : Com jasminDialect
   (tabCtxt (.reg 64) nRC) (.reg 64)` — a `stackLoad a idx` (the memref load
   `a[idx]`) followed by a `regArith .add` (`acc + a[idx]`). It is `StraightLine`
   (both binders are non-`stackStore` ops), so it meets the hypothesis of `loopRunT_eq_denoteT`.
   One-step denotation `arrSumBody.denote [acc, ofNat i, a] = acc + stackGet a i`
   is `rfl`.

2. **The reduction loop** `arrSumLoop a n : JForProgTab (.reg 64) nRC` and its
   index-dependent denotation `denoteT init = foldl (fun acc i => acc + a[i])
   (range n) init` — the running array sum `init + Σ_{i<n} a[i]`.

3. **An independent reference** `arrSumUpTo a n` (a plain `Nat`-recursive
   `BitVec 64` fold `Σ_{j<n} a[j]`, no dialect / `Com` / register allocator) and
   the **value-tie** `arrSumLoop_denoteT_eq_ref`:
   `(arrSumLoop a n).denoteT 0 = arrSumUpTo a n` for **all** `n ≤ nRC`. The loop
   folds the summands `a[0], a[1], …, a[n-1]` in ascending index order; the
   reference recurses on `n` (so associates the other way). Reconciled by the same
   AC-fold re-indexing argument `LoopCarriedDemo` uses
   (`range_succ_eq_map`/`foldl_map`/`ac_rfl`) — no heavy kernel `native_decide`.

4. **The abstract emit tie** `arrSumLoop_loopRun_eq_ref`: routing through the
   array-loop theorem `JForProgIndexed.loopRunT_eq_denoteT`, the
   abstract emitted loop run `loopRunT leafSem (arrSumLoop a n) 0` (the `execCom`
   evaluator threading the named accumulator, the index register and the array
   buffer through `n` iterations) equals the reference `arrSumUpTo a n`, under the
   single opaque-leaf hypothesis `LeafAgrees` that theorem carries.

## Scope (the x86-register-pin splice is outside this module)

The tie in §4 is over `execCom` (the abstract dialect evaluator), via
`loopRunT_eq_denoteT` — the array-loop control-flow theorem in
`JForProgIndexed`. It is **not** carried to the x86 `Lprog` byte emit.
`cforIdxToLprogAbiBodyZeroAcc` (the verified x86 counter-loop emit `LoopCarriedDemo`
uses) only accepts a **two-slot** body `Com jasminDialect [accTy, .reg 64] accTy`
(`acc`, counter): it pins the body's second-arg register to the loop counter `nReg`
and has **no third register/pointer operand** for an array base, and no
per-iteration `MOV resReg, [base + idx*8]` memory-load splice. Adding a
`[accTy, .reg 64, ptr]` body context to the x86 ABI splice — a base-pointer arg
register plus a scaled-indexed load `mem[base + idx*8]` inside the loop body, RA'd
and register-pinned alongside the counter — is an x86-backend extension, not
reachable by reuse alone; `LoopReduceX86Demo` treats it. This module pins the
array-reduction **value semantics** and the **abstract array-loop control-flow
tie**.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LoopReduceDemo

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminTy jasminDialect stackGet)
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgIndexed
  (tabCtxt JForProgTab JForProgTab.denoteT JForProgTab.stepT loopRunT
   loopRunT_eq_denoteT)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect (StraightLine)

/-! ## 1. The array-reduction body `(acc, idx, a) ↦ acc + a[idx]`

The body lives over the three-slot context `tabCtxt (.reg 64) nRC =
[.reg 64, .reg 64, .stackArr 64 nRC]` (`acc`, `idx`, `a`). It loads `a[idx]` by a
`stackLoad` (the memref load), then folds it into `acc` by a `regArith .add`. -/

/-- The array-reduction loop body: a leading liveness binder `regArith .add` of
    `acc` and `idx` (result discarded — see below), then `stackLoad a idx` (load
    `a[idx]` from the `stackArr` base), then `regArith .add` of `acc` and the
    loaded value.

    Context evolution (context grows at the head, every prior slot shifts `.there`):
    * input `[acc, idx, a] = [.reg 64, .reg 64, .stackArr 64 nRC]`;
    * the leading `regArith .add` over `acc = .here` and `idx = .there .here`
      pushes a (shadowed) result at the new `.here`; `acc`/`idx`/`a` shift to
      `.there .here` / `.there (.there .here)` / `.there (.there (.there .here))`;
    * `stackLoad` (args `a = .there³ .here`, `idx = .there² .here`) pushes the
      loaded `a[idx]` at the new `.here`; `acc` is now `.there (.there .here)`;
    * `regArith .add` over `acc = .there (.there .here)` and the loaded value
      `.here` produces `acc + a[idx]`, returned with `.ret .here`.

    The leading binder is a **register-liveness device for the x86 emit**, not a
    semantic step: it is shadowed by the later bindings and never reaches `.ret`,
    so the denotation is exactly `acc + a[idx]` (`arrSumBody_denote`, by `rfl`).
    Its purpose is to make the `acc`-arg's live range start at the body's first
    instruction so the linear-scan register allocator keeps `acc`, `idx` and the
    array base in three *distinct* registers across the loop back-edge — see the
    aliasing note in `cforIdxToLprogAbiBodyArr` / `LoopReduceX86Demo`. -/
def arrSumBody (nRC : Nat) : Com jasminDialect (tabCtxt (.reg 64) nRC) (.reg 64) :=
  -- Leading **liveness binder** (`acc + idx`, result discarded): it reads `acc`
  -- (head `.here`) and `idx` (`.there .here`) *before* the load, so the
  -- accumulator's live range starts at the body's first instruction rather than
  -- only at the closing `regArith .add`. Without it the `acc`-arg and the array
  -- base/`idx`-arg uses are disjoint, and the x86 linear scan
  -- (`comToLfundefPhys`) reclaims and **aliases** them onto one register, so the
  -- per-iteration arg-register pins in `cforIdxToLprogAbiBodyArr` clobber the
  -- accumulator. Forcing the three loop-carried roles (`acc`, `idx`, array base)
  -- to be simultaneously live makes the linear scan keep them in *distinct*
  -- registers across the back-edge — the same overlap guarantee the §5b
  -- rejection-sampler body (`acc ^= ctr`, which reads both in one binding)
  -- enjoys for free. The binding is shadowed (never read by `.ret`), so the
  -- denotation is unchanged: the final value is `acc + a[idx]`.
  .var (.mk (.regArith .add 64) rfl
        (.cons .here (.cons (.there .here) .nil)))
    (.var (.mk (.stackLoad 64 nRC) rfl
          (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) .nil)))
      (.var (.mk (.regArith .add 64) rfl
            (.cons (.there (.there .here)) (.cons .here .nil)))
        (.ret .here)))

/-- One-step denotation: `arrSumBody` on `[acc, ofNat i, a]` is
    `acc + stackGet a i` (`= acc + a[i mod nRC]`). The `stackLoad` reads
    `stackGet a (BitVec.ofNat 64 i).toNat`; for in-range `i` the index is `i`. -/
@[simp] theorem arrSumBody_denote (nRC : Nat) (acc : BitVec 64) (i : Nat)
    (a : Fin nRC → BitVec 64) :
    (arrSumBody nRC).denote
        (.cons acc (.cons (BitVec.ofNat 64 i) (.cons a .nil)))
      = acc + stackGet a (BitVec.ofNat 64 i).toNat := rfl

/-- `arrSumBody` is `StraightLine`: all three binders are non-`stackStore` ops
    (the leading liveness `regArith .add`, the `stackLoad`, then the folding
    `regArith .add`). This meets the array-loop theorem's hypothesis
    (`JForProgIndexed.loopRunT_eq_denoteT` needs `StraightLine p.body`). -/
theorem arrSumBody_straightLine (nRC : Nat) : StraightLine (arrSumBody nRC) := by
  refine ⟨?_, ?_, ?_, trivial⟩ <;> intro w n h <;> exact nomatch h

/-! ## 2. The array-reduction loop and its index-dependent denotation

`arrSumLoop a n` is the `JForProgTab` whose constant table is the array `a`, whose
trip count is `n`, and whose body is `arrSumBody`. Its index-dependent denotation
folds `acc := acc + a[i]` over `i = 0 .. n-1`. -/

/-- The array-reduction loop: `for i = 0 to n { acc := acc + a[i] }`, with the
    array `a` as the loop-invariant `JForProgTab` table read at the threaded loop
    index `idx`. -/
def arrSumLoop {nRC : Nat} (a : Fin nRC → BitVec 64) (n : Nat) :
    JForProgTab (.reg 64) nRC :=
  { n := n, table := a, body := arrSumBody nRC }

/-- The loop's index-dependent step at iteration `i`: `acc ↦ acc + a[i]` (via the
    `stackLoad a idx` body). `arrSumLoop_stepT` unfolds `stepT` to `arrSumBody`'s
    one-step denotation. -/
@[simp] theorem arrSumLoop_stepT {nRC : Nat} (a : Fin nRC → BitVec 64) (n : Nat)
    (i : Nat) (acc : BitVec 64) :
    (arrSumLoop a n).stepT i acc = acc + stackGet a (BitVec.ofNat 64 i).toNat :=
  rfl

/-- The loop's full index-dependent denotation is the explicit `List.range n`
    sum-fold `acc := acc + a[i]`, summing the array entries in ascending index
    order. -/
theorem arrSumLoop_denoteT {nRC : Nat} (a : Fin nRC → BitVec 64) (n : Nat)
    (init : BitVec 64) :
    (arrSumLoop a n).denoteT init
      = (List.range n).foldl
          (fun acc i => acc + stackGet a (BitVec.ofNat 64 i).toNat) init := rfl

/-! ## 3. The independent reference `Σ_{j<n} a[j]` and the value-tie -/

/-- Independent reference fold: `Σ_{j<n} a[j]` as a plain `Nat`-recursive
    `BitVec 64` fold — no dialect, no `Com`, no register allocator. Recurses on
    `n`, adding `a[n-1]` last (so it associates the opposite way from the loop's
    ascending fold; reconciled below by associativity-commutativity). -/
def arrSumUpTo {nRC : Nat} (a : Fin nRC → BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | k + 1 => arrSumUpTo a k + stackGet a (BitVec.ofNat 64 k).toNat

/-- The sum-fold over `List.range n` (summand `stackGet a i`) equals
    `init + arrSumUpTo a n`: the loop sum-accumulates the array entries in
    ascending order, the reference recurses on `n`; the values agree because `+`
    is associative-commutative. Proved by peeling the **last** loop iteration
    (`range_succ`), so the residual fold over `range k` is exactly the IH.
    Generalised over `init` so the induction goes through. -/
theorem rangeArrSumFold_eq {nRC : Nat} (a : Fin nRC → BitVec 64) (n : Nat)
    (init : BitVec 64) :
    (List.range n).foldl
        (fun acc i => acc + stackGet a (BitVec.ofNat 64 i).toNat) init
      = init + arrSumUpTo a n := by
  induction n generalizing init with
  | zero => simp [arrSumUpTo]
  | succ k ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, arrSumUpTo]
      ac_rfl

/-! The reference's `stackGet a i` reduces to `a[i]` on in-range `i`, and the
loop's `stackGet a (ofNat 64 i).toNat` reduces to `stackGet a i` when
`i < 2^64`. The value-tie below keeps the closed `stackGet` form (total, no side
condition); a callers'-facing `a[i]` form follows by `stackGet_id` /
`BitVec.toNat_ofNat` under `i < nRC ≤ 2^64`. -/

/-- **The value-tie (all trip counts).** The emitted array-reduction loop's
    index-dependent denotation from `acc = 0` equals the independent reference
    `Σ_{j<n} stackGet a j` for every `n`. Structural — no kernel `native_decide`. -/
theorem arrSumLoop_denoteT_eq_ref {nRC : Nat} (a : Fin nRC → BitVec 64) (n : Nat) :
    (arrSumLoop a n).denoteT (0 : BitVec 64) = arrSumUpTo a n := by
  rw [arrSumLoop_denoteT, rangeArrSumFold_eq]; simp

/-- On an in-range index, the loop's `stackGet a (ofNat 64 i).toNat` reads exactly
    the array entry `a i` (the `ofNat 64`/`toNat` round-trip is the identity when
    `i < nRC ≤ 2^64`, then `stackGet_id`). -/
theorem stackGet_ofNat_in_range {nRC : Nat} (a : Fin nRC → BitVec 64) (i : Nat)
    (hi : i < nRC) (hn : nRC ≤ 2 ^ 64) :
    stackGet a (BitVec.ofNat 64 i).toNat = a ⟨i, hi⟩ := by
  rw [BitVec.toNat_ofNat]
  have : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
  rw [this]
  exact JasminDialect.stackGet_id a ⟨i, hi⟩

/-- **The reader-facing `a[i]` form of the reference.** For a trip count
    `n ≤ nRC ≤ 2^64`, the reference `arrSumUpTo a` over `0 .. n` reads the in-range
    array entries directly: each step adds `a ⟨k, _⟩` (via the in-range `stackGet`
    reduction `stackGet_ofNat_in_range`), so the certified sum is the natural array
    sum `Σ_{j<n} a[j]` over the `Fin nRC` entries. Stated as the
    last-step recursion (the per-term form callers fold into a `Fin`-indexed sum). -/
theorem arrSumUpTo_succ_in_range {nRC : Nat} (a : Fin nRC → BitVec 64) (k : Nat)
    (hk : k < nRC) (hn : nRC ≤ 2 ^ 64) :
    arrSumUpTo a (k + 1) = arrSumUpTo a k + a ⟨k, hk⟩ := by
  rw [arrSumUpTo, stackGet_ofNat_in_range a k hk hn]


/-! ## 4. The abstract emit tie (via the array-loop control-flow theorem)

`JForProgIndexed.loopRunT_eq_denoteT` ties the abstract emitted loop run
`loopRunT leafSem p init` (the `execCom` evaluator threading the named
accumulator, the index register and the array buffer through `n` iterations) to
`p.denoteT init`, under the opaque-leaf edge `LeafAgrees`. Composing it with §3's
value-tie gives the emitted array-reduction loop's run = the reference array sum.

This tie is over `execCom` (the abstract dialect evaluator) — NOT over the x86
`Lprog` byte emit. The x86 memref-load register-pin splice is outside this module
(see the module docstring). -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect (LeafSem LeafAgrees)

/-- **The abstract emit tie.** Routed through the array-loop control-flow theorem
    `JForProgIndexed.loopRunT_eq_denoteT` (with `StraightLine` discharged by
    `arrSumBody_straightLine` and the opaque-leaf edge `LeafAgrees` carried), the
    abstract emitted array-reduction loop run from `acc = 0` equals the
    independent reference `Σ_{j<n} stackGet a j`.

    This is the array-indexed (memref-load) analogue of `LoopCarriedDemo`'s
    counter-reading additive tie, lifted to the three-slot `[acc, idx, a]` body
    context whose `stackLoad a idx` is the per-iteration memref load. The tie is
    over the abstract `execCom` evaluator; the x86 register-pin splice for the
    memory load is the explicit residual. -/
theorem arrSumLoop_loopRun_eq_ref {nRC : Nat} {leafSem : LeafSem}
    (hLeaf : LeafAgrees leafSem) (a : Fin nRC → BitVec 64) (n : Nat) :
    loopRunT leafSem (arrSumLoop a n) (0 : BitVec 64) = arrSumUpTo a n := by
  rw [loopRunT_eq_denoteT hLeaf (arrSumLoop a n) (arrSumBody_straightLine nRC),
      arrSumLoop_denoteT_eq_ref]

end CatCrypt.Crypto.SecureCompilation.X86Backend.LoopReduceDemo
