/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow

/-!
# Counter-reading loop emit — end-to-end demo (task #538, STEP 5)

`LprogControlFlow.lean` authored the **counter-reading** loop lowering
(`cforIdxToLprogAbiBody` / `cforIdxToLprogAbiBodyZeroAcc` / `cforIdxDenote`): a
two-input body `Com jasminDialect [accTy, .reg 64] accTy` over `(acc, ctr)`
whose `ctr`-arg register is pinned to the live loop counter, emitting the
back-edge `… ; SUB nReg,#1 ; CMP nReg,#0 ; jne .L0`. That lowering's end-to-end
use was never demonstrated. This module is that demonstration.

We take the smallest counter-reading body —

```
   (acc, ctr) ↦ acc XOR ctr            -- Com jasminDialect [reg 64, reg 64] (reg 64)
```

— with trip count `n = 128`, so `cforIdxDenote 128 body 0` folds
`acc := acc XOR ctr` over `ctr = 128, 127, …, 1`, i.e. it computes
`XOR_{k=1..128} k`. We:

1. give an **independent reference** `xorUpTo n` (the plain `Nat`-recursive
   fold `XOR_{k=1..n} k`, no dialect, no `Com`, no register allocator) and prove
   `cforIdxDenote n xorCtrBody 0 = xorUpTo n` for **all** `n` by structural
   induction (the loop folds the counter `n, …, 1`; the reference folds
   `1, …, n`; XOR is associative-commutative so the values agree) — no heavy
   kernel `native_decide`;
2. expose `xorCtrAbiLcmd` / `renderXorCtrLoopS` so the bench driver
   (`bench/counter_loop/counter_loop_owned_emit.lean`) lowers the body via
   `cforIdxToLprogAbiBodyZeroAcc` + `renderLfundef` to a real `.s` the
   orchestrator byte-KATs against a C reference computing the same fold.

This is the prerequisite for compiling the BLOCKED `*_sign_rwhile_kernel`
rejection-loop family: a sign-rejection loop is a counter-reading loop whose
body, instead of `acc XOR ctr`, runs the (richer) candidate-derive + accept
test. The lowering path proven here is identical; only the body `Com` grows.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CounterLoopDemo

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminTy jasminDialect)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLfundef)

/-! ## 1. The counter-reading body `(acc, ctr) ↦ acc XOR ctr` -/

/-- The smallest counter-reading loop body: a single `regArith .xor` over the
    two context vars `(acc, ctr) : [reg 64, reg 64]`. `acc` is `.here` (1st ctx
    elem), `ctr` is `.there .here` (2nd). Mirrors `JasminDialect.smokeProg`'s
    two-input shape (`add` over `[reg 32, reg 32]`), specialised to `xor` at
    width 64. Result is returned with `.ret .here`. -/
def xorCtrBody : Com jasminDialect [.reg 64, .reg 64] (.reg 64) :=
  .var (.mk (.regArith .xor 64) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- One-step denotation: `xorCtrBody` on `(acc, ctr)` is `acc XOR ctr`. -/
@[simp] theorem xorCtrBody_denote (acc ctr : BitVec 64) :
    xorCtrBody.denote (.cons acc (.cons ctr .nil)) = acc ^^^ ctr := rfl

/-! ## 2. The independent reference `XOR_{k=1..n} k` -/

/-- Independent reference fold: `XOR_{k=1..n} k` as a plain `Nat`-recursive
    `BitVec 64` fold — no dialect, no `Com`, no register allocator. `xorUpTo`
    folds in `1, 2, …, n` (XOR is commutative, so the loop's `n, …, 1` order
    yields the same value — discharged below). -/
def xorUpTo : Nat → BitVec 64
  | 0 => 0
  | k + 1 => xorUpTo k ^^^ BitVec.ofNat 64 (k + 1)

/-! ## 3. Denotation == reference (the structural proof, no heavy kernel) -/

/-- Rewrite `cforIdxDenote n xorCtrBody init` to the explicit `List.range n`
    XOR-fold with the live counter `n - i` at iteration `i`. `cforIdxDenote`'s
    body call `xorCtrBody.denote (cons acc (cons (ofNat (n-i)) nil))` is
    definitionally `acc ^^^ ofNat (n-i)` (`xorCtrBody_denote`), so the two fold
    functions are equal. -/
theorem cforIdxDenote_xor (n : Nat) (init : BitVec 64) :
    cforIdxDenote n xorCtrBody init
      = (List.range n).foldl
          (fun acc i => acc ^^^ BitVec.ofNat 64 (n - i)) init := by
  unfold cforIdxDenote; rfl

/-- The XOR-fold over `List.range n` with summand `n - i` equals
    `init ^^^ xorUpTo n`: the loop XOR-accumulates the multiset `{1, …, n}` in
    order `n, …, 1`, the reference in order `1, …, n`; the values agree. Proved
    by peeling the **first** loop iteration (`i = 0`, counter `n`): the residual
    fold over `range k` with counter `(k+1) - (j+1) = k - j` is exactly the IH at
    `n = k`. Generalised over `init` so the induction goes through. -/
theorem rangeXorFold_eq (n : Nat) (init : BitVec 64) :
    (List.range n).foldl (fun acc i => acc ^^^ BitVec.ofNat 64 (n - i)) init
      = init ^^^ xorUpTo n := by
  induction n generalizing init with
  | zero => simp [xorUpTo]
  | succ k ih =>
      rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
      have hreidx : (fun (acc : BitVec 64) (j : Nat) =>
          acc ^^^ BitVec.ofNat 64 (k + 1 - Nat.succ j))
          = (fun acc j => acc ^^^ BitVec.ofNat 64 (k - j)) := by
        funext acc j
        have : k + 1 - Nat.succ j = k - j := by omega
        rw [this]
      rw [hreidx, ih (init ^^^ BitVec.ofNat 64 (k + 1 - 0))]
      simp only [Nat.sub_zero, xorUpTo]
      ac_rfl

/-- **The end-to-end functional KAT (all trip counts).** The emitted
    counter-reading loop's denotation equals the independent reference
    `XOR_{k=1..n} k` for every `n`. Structural — no kernel `native_decide`. -/
theorem cforIdxDenote_xor_eq_ref (n : Nat) :
    cforIdxDenote n xorCtrBody (0 : BitVec 64) = xorUpTo n := by
  rw [cforIdxDenote_xor, rangeXorFold_eq]; simp

/-- Specialisation at the demo trip count `n = 128`: the emitted counter-reading
    loop's denotation equals the reference `xorUpTo 128` (`XOR_{k=1..128} k`).
    The concrete byte (`128 = 0x80`, by the closed form `XOR_{1..n} = n` for
    `n ≡ 0 (mod 4)`) is pinned at run time by the bench driver's C reference and
    the byte-KAT, not by a heavy in-Lean kernel reduction. -/
theorem cforIdxDenote_xor128 :
    cforIdxDenote 128 xorCtrBody (0 : BitVec 64) = xorUpTo 128 :=
  cforIdxDenote_xor_eq_ref 128

/-! ## 4. The owned-emit `Lcmd` and rendered `.s` (driver-facing) -/

/-- The counter-reading loop lowered to a callable parameterless `void → u64`
    owned function body: `xorCtrBody` wrapped by `cforIdxToLprogAbiBodyZeroAcc`
    at width 64, top label `0`, counter register `R8`, trip count `128`. The
    accumulator is zero-initialised in the prologue (`XOR accReg,accReg`),
    matching a C prototype `uint64_t f(void)` that starts from `acc = 0`. -/
def xorCtrAbiLcmd : VIR.JasminLprogExport.Lcmd :=
  cforIdxToLprogAbiBodyZeroAcc 64 0 "R8" 128 xorCtrBody

/-- The rendered AT&T `.s` text for the counter-reading loop, function name
    `counter_loop_xor`. The driver writes this to `bench/counter_loop/gen/`. -/
def renderXorCtrLoopS : String := renderLfundef "counter_loop_xor" xorCtrAbiLcmd

/-- The emitted body is non-empty (the lowering produced instructions): it ends
    with the `MOV RAX, resReg` return splice, so it is a `(_ :: _) ++ [_]`. -/
theorem xorCtrAbiLcmd_nonempty : xorCtrAbiLcmd ≠ [] := by
  simp only [xorCtrAbiLcmd, cforIdxToLprogAbiBodyZeroAcc]
  exact List.append_ne_nil_of_right_ne_nil _ (by simp)

end CatCrypt.Crypto.SecureCompilation.X86Backend.CounterLoopDemo
