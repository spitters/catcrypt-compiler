/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.CounterLoopDemo
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CounterLoopDemo

/-!
# Loop-carried-value emit — additive accumulator (task #538, wall #2)

`CounterLoopDemo.lean` lowers the smallest **counter-reading** loop body
`(acc, ctr) ↦ acc XOR ctr` through `cforIdxToLprogAbiBodyZeroAcc` (one body copy
+ the `SUB ; CMP ; jne .L0` back-edge) and ties its denotation to the reference
`XOR_{k=1..n} k` for **all** trip counts (`CounterLoopDemo.cforIdxDenote_xor_eq_ref`).
That demonstrates the loop *control-flow* path with an idempotent-algebra (XOR)
loop-carried value.

This module advances to a **non-idempotent, order-insensitive additive**
loop-carried value through the *same* verified x86 emit path. The body is

```
   (acc, ctr) ↦ acc + ctr            -- Com jasminDialect [reg 64, reg 64] (reg 64)
```

so `cforIdxDenote n sumCtrBody 0` folds `acc := acc + ctr` over the live counter
`ctr = n, n-1, …, 1`, i.e. it computes the running sum `Σ_{k=1..n} k`. We:

1. give an **independent reference** `sumUpTo n` (the plain `Nat`-recursive
   `BitVec 64` fold `Σ_{k=1..n} k`, no dialect / `Com` / register allocator) and
   prove `cforIdxDenote n sumCtrBody 0 = sumUpTo n` for **all** `n` by structural
   induction on the loop's `List.range`-fold (the loop folds `n, …, 1`, the
   reference `1, …, n`; `+` is associative-commutative so the values agree) — no
   heavy kernel `native_decide`;
2. reuse `cforIdxToLprogAbiBodyZeroAcc` (the *same* verified looped emit
   `CounterLoopDemo` uses) to lower `sumCtrBody` to a callable parameterless
   `void → u64` owned `.s`, computing the same fold from `acc = 0`.

## Why this is a genuine increment over the XOR demo

The XOR demo's algebra is idempotent and self-inverse; the only thing it
exercises is the counter-reading *plumbing*. The additive accumulator is a
distinct fold algebra: the loop-carried value strictly *grows* each iteration
(`acc` depends on every prior `ctr`), and the closed form is the Gauss sum
`n(n+1)/2 mod 2^64`. The reference/loop reconciliation is the same AC-fold
re-indexing argument, but the value carried is now a true running reduction —
the shape every "fold `f` over `0..n` into one register" inner pass uses
(checksum/length-prefixed accumulation, the additive case of a `Σ`-reduction).

## What this is NOT (the honest residual, see report)

The loop-carried value here is fed by the **loop counter** (`ctr = n-i`), not by
a value loaded from a caller-supplied **array** `mem[i]`. A genuine
`v := v + mem[base + i]` array-sum needs the body to carry an array/pointer slot
(the `[acc, idx, table]` shape of `JForProgIndexed.JForProgTab`, whose abstract
`execCom` denotation tie is `JForProgIndexed.loopRunT_eq_denoteT`) wired into the
x86 `cforIdxToLprogAbiBody` register-pin splice — that wiring is the named
residual, not claimed here. This module pins the additive loop-carried value
through the counter-reading path; the array-indexed memref body is the next wall.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LoopCarriedDemo

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminTy jasminDialect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLfundef)

/-! ## 1. The additive counter-reading body `(acc, ctr) ↦ acc + ctr` -/

/-- The additive counter-reading loop body: a single `regArith .add` over the two
    context vars `(acc, ctr) : [reg 64, reg 64]`. `acc` is `.here`, `ctr` is
    `.there .here`. Identical shape to `CounterLoopDemo.xorCtrBody` with the op
    `.xor` replaced by `.add` (the only change — same lowering path). Result is
    returned with `.ret .here`. -/
def sumCtrBody : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  .var (.mk (.regArith .add 64) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- One-step denotation: `sumCtrBody` on `(acc, ctr)` is `acc + ctr`. -/
@[simp] theorem sumCtrBody_denote (acc ctr : BitVec 64) :
    sumCtrBody.denote (.cons acc (.cons ctr .nil)) = acc + ctr := rfl

/-! ## 2. The independent reference `Σ_{k=1..n} k` -/

/-- Independent reference fold: `Σ_{k=1..n} k` as a plain `Nat`-recursive
    `BitVec 64` fold — no dialect, no `Com`, no register allocator. `sumUpTo`
    folds in `1, 2, …, n` (`+` is commutative, so the loop's `n, …, 1` order
    yields the same value — discharged below). -/
def sumUpTo : Nat → BitVec 64
  | 0 => 0
  | k + 1 => sumUpTo k + BitVec.ofNat 64 (k + 1)

/-! ## 3. Denotation == reference (the structural proof, no heavy kernel) -/

/-- Rewrite `cforIdxDenote n sumCtrBody init` to the explicit `List.range n`
    sum-fold with the live counter `n - i` at iteration `i`. `cforIdxDenote`'s
    body call `sumCtrBody.denote (cons acc (cons (ofNat (n-i)) nil))` is
    definitionally `acc + ofNat (n-i)` (`sumCtrBody_denote`). -/
theorem cforIdxDenote_sum (n : Nat) (init : BitVec 64) :
    cforIdxDenote n sumCtrBody init
      = (List.range n).foldl
          (fun acc i => acc + BitVec.ofNat 64 (n - i)) init := by
  unfold cforIdxDenote; rfl

/-- The sum-fold over `List.range n` with summand `n - i` equals
    `init + sumUpTo n`: the loop sum-accumulates the multiset `{1, …, n}` in
    order `n, …, 1`, the reference in order `1, …, n`; the values agree. Proved by
    peeling the **first** loop iteration (`i = 0`, counter `n`): the residual fold
    over `range k` with counter `(k+1) - (j+1) = k - j` is exactly the IH at
    `n = k`. Generalised over `init` so the induction goes through. -/
theorem rangeSumFold_eq (n : Nat) (init : BitVec 64) :
    (List.range n).foldl (fun acc i => acc + BitVec.ofNat 64 (n - i)) init
      = init + sumUpTo n := by
  induction n generalizing init with
  | zero => simp [sumUpTo]
  | succ k ih =>
      rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
      have hreidx : (fun (acc : BitVec 64) (j : Nat) =>
          acc + BitVec.ofNat 64 (k + 1 - Nat.succ j))
          = (fun acc j => acc + BitVec.ofNat 64 (k - j)) := by
        funext acc j
        have : k + 1 - Nat.succ j = k - j := by omega
        rw [this]
      rw [hreidx, ih (init + BitVec.ofNat 64 (k + 1 - 0))]
      simp only [Nat.sub_zero, sumUpTo]
      ac_rfl

/-- **The end-to-end functional KAT (all trip counts).** The emitted
    counter-reading additive loop's denotation equals the independent reference
    `Σ_{k=1..n} k` for every `n`. Structural — no kernel `native_decide`. -/
theorem cforIdxDenote_sum_eq_ref (n : Nat) :
    cforIdxDenote n sumCtrBody (0 : BitVec 64) = sumUpTo n := by
  rw [cforIdxDenote_sum, rangeSumFold_eq]; simp

/-- Specialisation at the demo trip count `n = 100`: the emitted additive loop's
    denotation equals `sumUpTo 100` (`Σ_{k=1..100} k`). The concrete byte
    (`Σ_{1..100} = 5050 = 0x13BA`, the Gauss closed form `n(n+1)/2`) is pinned at
    run time by the bench driver's C reference and the byte-KAT, not by a heavy
    in-Lean kernel reduction. -/
theorem cforIdxDenote_sum100 :
    cforIdxDenote 100 sumCtrBody (0 : BitVec 64) = sumUpTo 100 :=
  cforIdxDenote_sum_eq_ref 100

/-! ## 4. The owned-emit `Lcmd` and rendered `.s` (driver-facing) -/

/-- The additive counter-reading loop lowered to a callable parameterless
    `void → u64` owned function body: `sumCtrBody` wrapped by
    `cforIdxToLprogAbiBodyZeroAcc` at width 64, top label `0`, counter register
    `R8`, trip count `100`. The accumulator is zero-initialised in the prologue
    (`XOR accReg,accReg`), matching a C prototype `uint64_t f(void)` that starts
    from `acc = 0`. Reuses the *same* verified looped emit `CounterLoopDemo` uses;
    only the body op differs. -/
def sumCtrAbiLcmd : VIR.JasminLprogExport.Lcmd :=
  cforIdxToLprogAbiBodyZeroAcc 64 0 "R8" 100 sumCtrBody

/-- The rendered AT&T `.s` text for the additive loop, function name
    `loop_carried_sum`. The driver writes this to `bench/loop_carried/gen/`. -/
def renderSumCtrLoopS : String := renderLfundef "loop_carried_sum" sumCtrAbiLcmd

/-- The emitted body is non-empty (the lowering produced instructions): it ends
    with the `MOV RAX, resReg` return splice, so it is a `(_ :: _) ++ [_]`. -/
theorem sumCtrAbiLcmd_nonempty : sumCtrAbiLcmd ≠ [] := by
  simp only [sumCtrAbiLcmd, cforIdxToLprogAbiBodyZeroAcc]
  exact List.append_ne_nil_of_right_ne_nil _ (by simp)

end CatCrypt.Crypto.SecureCompilation.X86Backend.LoopCarriedDemo
