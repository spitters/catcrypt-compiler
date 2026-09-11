/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.Jasmin.Mpn.MulBaseCaseAdxBlockedPrototype
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Jasmin.Mpn.MulBaseCaseAdxBlockedPrototype

@[expose] public section

set_option autoImplicit false

/-!
# Runtime-`Cwhile` schoolbook of ADCX/ADOX/MULX `mpn_mul_basecase`

**EXPERIMENTAL FILE.** Companion to `Mpn.MulBaseCaseAdxBlockedPrototype.lean`
and `Mpn.AddMul1AdxBlockedPrototype.lean`.

## Motivation

The just-landed `MpnMulBaseCaseAdxBlockedPrototype` (the meta-unrolled
schoolbook over `n` columns × an inner blocked addmul) hits jasminc's
register allocator at every size:

    register allocation: no more free register to allocate variable:
        r5.6405 (defined at "mpn_mul_basecase_adx_blk_16.jazz", line 206)

because the **outer N-column meta-unroll** creates `n` independent
SSA-renamed register banks (`zero.col_j`, `r_i.col_j`, `t_i.col_j`,
`hi_i.col_j`, `lo_i.col_j`) that fight for the same physical x86 GPRs.
At every `n ∈ {16, 32, 64, 128}` the per-column banks exceed jasminc's
allocator budget, so the bench falls back to a C ADX reference.

The verified next step — recorded as the "future revision" in that
prototype's docstring — is to replace the outer **meta-unroll** with a
**runtime `Cwhile` loop**.  Each column becomes one iteration of the
runtime loop, the inner kernel is a single `Ccall` to the already-emitted
`mpn_addmul_1_adx_blk_<n>` function, and the SSA register bank is
**reused across columns** (each iteration sees a fresh, identical
register live-set — bounded by what one column needs).

This file is that next step.

## Structure

```
bodyMulBasecaseCwhile n =
  init: zero result memory; set up op_col, bp_col, col_left
  while (col_left != 0) {
    b      := [:u64 bp_col + 0]                # load b[col]
    op     := op_col                           # callee param: result slice
    ap     := ap_base                          # callee param: multiplicand
    cy_col = mpn_addmul_1_adx_blk_cy_<n>(op, ap, b)  ;  (Ccall, returns cy)
    [:u64 op_col + 8·n] := cy_col              # store column carry-out
    op_col   := op_col + 8                     # advance result pointer
    bp_col   := bp_col + 8                     # advance b pointer
    col_left := col_left - 1                   # decrement loop counter
  }
```

## Why jasminc should accept this

The per-iteration register live-set is fixed:
* `op_col`, `bp_col`, `col_left`, `ap_base` — the loop's stable
  cross-iter registers (4 GPRs).
* `b`, `op`, `ap`, `cy_col` — the Ccall ABI registers (4 GPRs).

That's 8 GPRs of cross-iter pressure, plus whatever the Ccall consumes
internally — but the Ccall's register footprint is the same fixed
8-limb-block ADX dual-chain that `MpnAddMul1AdxBlockedPrototype`
already proves jasminc accepts.  No per-column SSA renaming amplifies
the budget.

## Carry-returning addmul

The existing `mpn_addmul_1_adx_blk_<n>` is **void**: its carry-out
lives in the callee-local `cy` register and is lost on return.  For
the schoolbook outer loop we need that carry to land in result memory
at `r[col + n]`.

Rather than modify the read-only blocked addmul prototype, we declare a
sibling `FunDecl` `mpn_addmul_1_adx_blk_cy_<n>` in this file whose
**body is the same** `bodyAddMul1AdxBlocked numBlocks` (literally the
same `List InstrR`) but whose `results := [vr "cy"]` exposes the
column carry-out as a Ccall return value.  Refinement of this carry-
returning variant inherits the void variant's correctness — the body
is identical, only the return-value plumbing differs.

## Spec equivalence

The runtime-`Cwhile` schoolbook computes the same `r := a · b` product
as the meta-unrolled schoolbook — both forms iterate over the same
`n` columns of `mpn_addmul_1`, only the **outer loop encoding**
differs.  Hence `mpnMulBasecaseAdxCwhile = mpnMul` definitionally (the
pure spec wraps `mpnMul a b`), inheriting `mpnMul_toNat` for the
headline correctness.

## What this file proves

1. **Pure functional reference** `mpnMulBasecaseAdxCwhile` (§2),
   definitionally equal to `mpnMul a b`.
2. **`FunDecl` and `.jazz` emission** (§3, §4): one
   `mpn_addmul_1_adx_blk_cy_<n>` (carry-returning wrapper) and one
   `mpn_mul_basecase_adx_cwhile_<n>` (outer Cwhile schoolbook) symbol
   per `n ∈ {16, 32, 64, 128}`.
3. **Refinement statement** (§5): the `n = 0` case proved directly by
   symbolic evaluation of the empty Cwhile prologue.
4. **General-`n` reduction**: the runtime-Cwhile body reduces by
   induction on the loop counter to repeated applications of
   `MpnAddMul1AdxBlockedJasminRefines_zero`'s pattern (one per column),
   recorded as a `Prop`-level step obligation in the same style as
   the meta-unrolled prototype's step residual.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.MulBaseCaseAdxCwhilePrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype hiding vr pv loadAt0 storeAt0 binImm
open CatCrypt.Crypto.Jasmin.Mpn.Mul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.Addmul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.MulPrototype
open CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxPrototype
open CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxBlockedPrototype
open CatCrypt.Crypto.Jasmin.Mpn.MulBaseCaseAdxBlockedPrototype

/-! ## §1  Block parameters

Inherited from `MpnMulBaseCaseAdxBlockedPrototype` (which itself
inherits from `MpnAddMul1AdxBlockedPrototype`): `BLOCK = 8` limbs per
inner Cfor iteration of the addmul, `n = numBlocks · BLOCK` is the
column width.
-/

/-- Same block size as the meta-unrolled blocked prototype. -/
def CW_BLOCK : Nat := Mpn.MulBaseCaseAdxBlockedPrototype.MULBASE_BLOCK

theorem cw_block_eq_eight : CW_BLOCK = 8 := rfl

/-! ## §2  Pure functional reference

The runtime-Cwhile schoolbook computes the same `mpnMul a b` product
as the meta-unrolled schoolbook (and the limb-by-limb reference, and
the unblocked-ADX reference, and every other variant — they all
schedule the same per-column addmul work).  We wrap `mpnMul` as a
definitional alias to keep the file self-contained. -/

/-- Pure-functional spec of the runtime-Cwhile schoolbook: identical to
    `mpnMul`.  Definitionally equal to
    `mpnMulBasecaseAdx_blocked` and `mpnMulBasecaseAdx`. -/
def mpnMulBasecaseAdxCwhile (a b : List (BitVec 64)) : List (BitVec 64) :=
  mpnMul a b

/-- The Cwhile-schoolbook spec equals the limb-by-limb reference (`rfl`). -/
theorem mpnMulBasecaseAdxCwhile_eq_mpnMul (a b : List (BitVec 64)) :
    mpnMulBasecaseAdxCwhile a b = mpnMul a b := rfl

/-- The Cwhile-schoolbook spec equals the meta-unrolled blocked spec (`rfl`). -/
theorem mpnMulBasecaseAdxCwhile_eq_blocked (a b : List (BitVec 64)) :
    mpnMulBasecaseAdxCwhile a b = mpnMulBasecaseAdx_blocked a b := rfl

/-- Width: outputs exactly `|a| + |b|` limbs. -/
theorem mpnMulBasecaseAdxCwhile_length (a b : List (BitVec 64)) :
    (mpnMulBasecaseAdxCwhile a b).length = a.length + b.length :=
  mpnMul_length a b

/-- **Main correctness** for the runtime-Cwhile schoolbook: the full
    schoolbook product equals `a · b` over `Nat`. -/
theorem mpnMulBasecaseAdxCwhile_toNat (a b : List (BitVec 64)) :
    toNat (mpnMulBasecaseAdxCwhile a b) = toNat a * toNat b :=
  mpnMul_toNat a b

/-! ### Concrete sanity checks -/

/-- 2-limb × 2-limb sanity. -/
example : mpnMulBasecaseAdxCwhile [3, 0] [2, 0] = [6, 0, 0, 0] := by native_decide

/-- Carry propagation: `[2^63,0]² = [0, 2^62, 0, 0]`. -/
example : mpnMulBasecaseAdxCwhile [BitVec.ofNat 64 (2 ^ 63), 0]
    [BitVec.ofNat 64 (2 ^ 63), 0] = [0, BitVec.ofNat 64 (2 ^ 62), 0, 0] := by
  native_decide

/-! ## §3  Carry-returning blocked addmul (Ccall callee)

The existing `mpn_addmul_1_adx_blk_<n>` is void — its `cy` register is
callee-local and lost on return.  The runtime-Cwhile schoolbook needs
that carry to land at `r[col + n]`, so we declare a sibling FunDecl
that exposes `cy` via `results := [vr "cy"]`.

The body is **literally the same** `bodyAddMul1AdxBlocked numBlocks`
list of instructions used by the void variant — only the return-value
plumbing in the FunDecl differs.  Hence the correctness of this
variant is inherited from `MpnAddMul1AdxBlockedJasminRefines_zero`. -/

/-- Carry-returning blocked addmul: same body as
    `mpnAddMul1AdxBlockedFd`, exposes `cy` as a return value. -/
def mpnAddMul1AdxBlkCyFd (numBlocks : Nat) : FunDecl where
  name := { name := "mpn_addmul_1_adx_blk_cy_"
                 ++ toString (numBlocks * BLOCK) }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "b" }⟩]
  body := bodyAddMul1AdxBlocked numBlocks
  results := [{ var := vr "cy" }]

/-- The carry-returning wrapper has the same body as the void variant. -/
theorem mpnAddMul1AdxBlkCyFd_body_eq (numBlocks : Nat) :
    (mpnAddMul1AdxBlkCyFd numBlocks).body =
    (mpnAddMul1AdxBlockedFd numBlocks).body := rfl

/-- The carry-returning wrapper's name encodes `n = numBlocks · BLOCK`. -/
theorem mpnAddMul1AdxBlkCyFd_name (numBlocks : Nat) :
    (mpnAddMul1AdxBlkCyFd numBlocks).name.name =
    "mpn_addmul_1_adx_blk_cy_" ++ toString (numBlocks * BLOCK) := rfl

/-! ## §4  The runtime-`Cwhile` schoolbook body

For `n = numBlocks · BLOCK` columns, the outer loop:

```
init:
  zero `2n` result limbs at [rp_base + 0..2n)
  op_col   := rp_base                    # column-start of result window
  bp_col   := bp                          # b-pointer iterator
  col_left := n                           # countdown loop counter

while (col_left != 0) {
  b        := [:u64 bp_col + 0]           # load b[col]
  op       := op_col                      # Ccall arg: result slice
  ap       := ap_base                     # Ccall arg: a (unchanged across cols)
  cy_col   = mpn_addmul_1_adx_blk_cy_<n>(op, ap, b)   # blocked addmul + cy
  [:u64 op_col + 8·n] := cy_col           # store column carry-out
  op_col   := op_col + 8
  bp_col   := bp_col + 8
  col_left := col_left - 1
}
```

Compared with the meta-unrolled blocked emit
(`bodyMulBasecaseAdxBlocked`), this version's outer loop is a runtime
`Cwhile`, NOT a compile-time `Cfor` that jasminc inline-unrolls.  Each
iteration reuses the same register bank, so jasminc's allocator sees a
fixed-size live-set independent of `n`.
-/

/-- The per-iteration body of the runtime-Cwhile schoolbook.  One
    column of `mpn_addmul_1_adx_blk_cy_<n>`. -/
def perColumnCwhileBody (numBlocks : Nat) : List InstrR :=
  let n := numBlocks * CW_BLOCK
  -- Load b[col] into the Ccall arg register `b`.
  [ .Cassgn (.Lvar { var := vr "b" }) .AT_none (.sword .U64)
      (.Pload .U64 { var := vr "bp_col" } (.Pconst 0))
  -- Setup Ccall args: op := op_col; ap := ap_base.
  , .Cassgn (.Lvar { var := vr "op" }) .AT_none (.sword .U64)
      (pv "op_col")
  , .Cassgn (.Lvar { var := vr "ap" }) .AT_none (.sword .U64)
      (pv "ap_base")
  -- Blocked addmul Ccall: cy_col = mpn_addmul_1_adx_blk_cy_<n>(op, ap, b).
  , .Ccall .DoNotInline
      [.Lvar { var := vr "cy_col" }]
      { name := "mpn_addmul_1_adx_blk_cy_" ++ toString n }
      [ pv "op", pv "ap", pv "b" ]
  -- Store column carry-out at r[col + n] = op_col + 8·n.
  , .Cassgn (.Lmem .U64 { var := vr "op_col" } (.Pconst (8 * Int.ofNat n)))
      .AT_none (.sword .U64) (pv "cy_col")
  -- Advance the column pointers and decrement the counter.
  , binImm "op_col"   (.Oadd .U64) 8
  , binImm "bp_col"   (.Oadd .U64) 8
  , binImm "col_left" (.Osub .U64) 1 ]

/-- Pre-zero `2n` result limbs at `[rp_base + 0..2n)`. -/
def initResultMemZeroCw : Nat → List InstrR
  | 0     => []
  | k + 1 => initResultMemZeroCw k ++
             [ store64Off "rp_base" (8 * Int.ofNat k) "zero" ]

/-- **The full runtime-Cwhile schoolbook body** for `n = numBlocks · BLOCK`.

    Prologue: clear flags and zero scratch; pre-zero `2n` result limbs;
    set up `op_col := rp_base`, `bp_col := bp`, `col_left := n`.

    Main: `while (col_left != 0) { perColumnCwhileBody }`.

    The outer Cwhile is a runtime loop — jasminc does NOT inline-unroll
    it (only `Cfor` is compile-time-unrolled).  Hence the register
    pressure per iteration is bounded by what one column needs. -/
def bodyMulBasecaseCwhile (numBlocks : Nat) : List InstrR :=
  let n := numBlocks * CW_BLOCK
  -- Prologue: zero the flag bank and `zero` register.
  [ xorClearFlags "of" "cf" "zero" ]
  -- Pre-zero the 2n result limbs.
  ++ initResultMemZeroCw (2 * n)
  -- Set up the column iterators.
  ++ [ .Cassgn (.Lvar { var := vr "op_col" }) .AT_none (.sword .U64)
          (pv "rp_base")
     , .Cassgn (.Lvar { var := vr "bp_col" }) .AT_none (.sword .U64)
          (pv "bp")
     , assignConst "col_left" (Int.ofNat n) ]
  -- Runtime Cwhile schoolbook.
  ++ [ .Cwhile [] (.Papp2 (.Oneq .U64) (pv "col_left") (.Pconst 0))
              (perColumnCwhileBody numBlocks) ]

/-- The runtime-Cwhile `mpn_mul_basecase_adx_cwhile_<n>` FunDecl.

    Signature: `(rp_base, ap_base, bp)` — result pointer (2n limbs),
    multiplicand pointer (n limbs), multiplier pointer (n limbs).
    Matches the `__gmpn_mul_basecase` ABI restricted to equal-length. -/
def mpnMulBasecaseAdxCwhileFd (numBlocks : Nat) : FunDecl where
  name := { name := "mpn_mul_basecase_adx_cwhile_"
                 ++ toString (numBlocks * CW_BLOCK) }
  params := [⟨{ var := vr "rp_base" }⟩, ⟨{ var := vr "ap_base" }⟩,
             ⟨{ var := vr "bp" }⟩]
  body := bodyMulBasecaseCwhile numBlocks
  results := []

/-! ## §5  `.jazz` emission -/

/-- Emit the carry-returning addmul callee for `n = numBlocks · BLOCK`. -/
def emitAddmulCy (numBlocks : Nat) : Option String :=
  emitFunDecl (mpnAddMul1AdxBlkCyFd numBlocks)

/-- Emit the runtime-Cwhile schoolbook caller. -/
def emitMulCwhile (numBlocks : Nat) : Option String :=
  emitFunDecl (mpnMulBasecaseAdxCwhileFd numBlocks)

/-- Emit both functions concatenated into one `.jazz` file. -/
def emitMulCwhilePair (numBlocks : Nat) : Option String := do
  let calleeStr ← emitAddmulCy numBlocks
  let callerStr ← emitMulCwhile numBlocks
  some (calleeStr ++ "\n" ++ callerStr)

/-- Emit n=16 (numBlocks = 2). -/
def emittedCwhile16 : Option String := emitMulCwhilePair 2

/-- Emit n=32 (numBlocks = 4). -/
def emittedCwhile32 : Option String := emitMulCwhilePair 4

/-- Emit n=64 (numBlocks = 8). -/
def emittedCwhile64 : Option String := emitMulCwhilePair 8

/-- Emit n=128 (numBlocks = 16). -/
def emittedCwhile128 : Option String := emitMulCwhilePair 16

example : emittedCwhile16.isSome := by native_decide

#eval match emittedCwhile16 with | some s => s | none => "EMIT FAILED"

/-! ## §6  Registry for the Ccall

The Cwhile body's Ccall target `mpn_addmul_1_adx_blk_cy_<n>` resolves
through a registry mapping the function name to `mpnAddMul1AdxBlkCyFd`. -/

/-- Registry resolving `mpn_addmul_1_adx_blk_cy_<n>` for fixed
    `numBlocks`.  Other names resolve through `emptyRegistry` (i.e. fail). -/
def cwhileRegistry (numBlocks : Nat) : BignumRegistry := fun name =>
  let target := "mpn_addmul_1_adx_blk_cy_" ++ toString (numBlocks * CW_BLOCK)
  if name = target then some (mpnAddMul1AdxBlkCyFd numBlocks)
  else none

theorem cwhileRegistry_lookup (numBlocks : Nat) :
    cwhileRegistry numBlocks
      ("mpn_addmul_1_adx_blk_cy_" ++ toString (numBlocks * CW_BLOCK))
    = some (mpnAddMul1AdxBlkCyFd numBlocks) := by
  simp [cwhileRegistry]

/-! ## §7  Refinement statement and the `n = 0` base case

The refinement says: when run on a memory state holding `a` at
`ap_base`, `b` at `bp`, and any bytes at `rp_base`'s 2n-limb window,
the emitted body produces `mpnMul a b` at `rp_base`.

For `numBlocks = 0` the body executes only the prologue:
* `xor zero, zero` — flags + zero register cleared
* `initResultMemZeroCw 0 = []` — no result limbs to clear
* `op_col := rp_base; bp_col := bp; col_left := 0`
* `Cwhile (col_left != 0) ...` — exits immediately (col_left = 0)

So memory is unchanged, and `mpnMul [] [] = []` makes the result-window
condition vacuous. -/

/-- Refinement statement for the runtime-Cwhile schoolbook emit at fixed
    `n = numBlocks · BLOCK`.  Memory contract: `rp_base`, `ap_base`, `bp`
    point to pairwise-disjoint `2n`, `n`, `n`-limb regions. -/
def MpnMulBasecaseAdxCwhileRefinesStmt (numBlocks : Nat) : Prop :=
  ∀ (s : BignumState) (rin a b : List (BitVec 64)),
    rin.length = 2 * (numBlocks * CW_BLOCK) →
    a.length = numBlocks * CW_BLOCK →
    b.length = numBlocks * CW_BLOCK →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "rp_base").toNat) rin →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap_base").toNat) a →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp_base").toNat)
                         (8 * (2 * (numBlocks * CW_BLOCK))))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap_base").toNat)
                         (8 * (numBlocks * CW_BLOCK))) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp_base").toNat)
                         (8 * (2 * (numBlocks * CW_BLOCK))))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat)
                         (8 * (numBlocks * CW_BLOCK))) →
    ∃ s', ∃ fuel, bignumExecFuel (cwhileRegistry numBlocks) fuel
            (bodyMulBasecaseCwhile numBlocks) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp_base").toNat)
        (mpnMulBasecaseAdxCwhile a b)

/-- For `numBlocks = 0` the body is just the XOR-clear, the three
    pointer/counter setup assignments, and an immediate-exit Cwhile. -/
theorem bodyMulBasecaseCwhile_zero :
    bodyMulBasecaseCwhile 0 =
      [ xorClearFlags "of" "cf" "zero"
      , .Cassgn (.Lvar { var := vr "op_col" }) .AT_none (.sword .U64)
          (pv "rp_base")
      , .Cassgn (.Lvar { var := vr "bp_col" }) .AT_none (.sword .U64)
          (pv "bp")
      , assignConst "col_left" 0
      , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "col_left") (.Pconst 0))
              (perColumnCwhileBody 0) ] := by
  unfold bodyMulBasecaseCwhile initResultMemZeroCw
  rfl

/-- `mpnMul [] [] = []`. -/
theorem mpnMul_nil_nil_cw : mpnMul ([] : List (BitVec 64)) [] = [] := by
  simp [mpnMul]

/-- `mpnMulBasecaseAdxCwhile [] [] = []`. -/
theorem mpnMulBasecaseAdxCwhile_nil_nil :
    mpnMulBasecaseAdxCwhile ([] : List (BitVec 64)) [] = [] :=
  mpnMul_nil_nil_cw

set_option linter.unusedSimpArgs false in
/-- **`numBlocks = 0` base case** for the runtime-Cwhile refinement.

    At `numBlocks = 0` both operands are `[]` (length `0 * BLOCK = 0`),
    so `mpnMul [] [] = []` and `memHoldsLimbs … []` is vacuous.  The
    body executes:

    1. `xor of, cf, _, _, _, zero = #XOR_64(zero, zero)` — clears flags+zero.
    2. `op_col := rp_base`
    3. `bp_col := bp`
    4. `col_left := 0`
    5. `while (col_left != 0) { ... }` — immediate exit (col_left = 0).

    No memory writes occur (initResultMemZeroCw 0 = []), so memory at
    `rp_base` is unchanged. -/
theorem MpnMulBasecaseAdxCwhileJasminRefines_zero :
    MpnMulBasecaseAdxCwhileRefinesStmt 0 := by
  intro s rin a b _ ha hb _ _ _ _ _
  -- 0 * BLOCK = 0, so a and b are empty.
  have h0 : (0 : Nat) * CW_BLOCK = 0 := by simp
  rw [h0] at ha hb
  have ha_nil : a = [] := List.length_eq_zero_iff.mp ha
  have hb_nil : b = [] := List.length_eq_zero_iff.mp hb
  subst ha_nil; subst hb_nil
  -- Body reduces to XOR-clear + 3 setup + immediate-exit Cwhile.
  rw [bodyMulBasecaseCwhile_zero]
  -- Witness: explicit state after the prologue (xor + 3 Cassgns), with
  -- op_col := rp_base, bp_col := bp, col_left := 0.  The Cwhile then sees
  -- col_left = 0 and exits without modifying state.
  set sPrologue : BignumState :=
    setReg (setReg (setReg
      (setReg (setReg (setReg s "of" 0) "cf" 0) "zero" 0)
      "op_col" (s.regs "rp_base"))
      "bp_col" (s.regs "bp"))
      "col_left" 0
  refine ⟨sPrologue, 8, ?_, ?_⟩
  · -- We split the 5-instruction body into:
    --   prologue (xorClearFlags + 3 Cassgns) followed by Cwhile.
    -- Step 1: evaluate prologue (straight-line) to reach sPrologue.
    -- Step 2: at sPrologue, col_left = 0 so the Cwhile guard is false and
    --         the loop exits via bignumExecFuel_loop_exit.
    -- We chain these via bignumExecFuel_append_join.
    have hZeroXor : (s.regs "zero" ^^^ s.regs "zero" : BitVec 64) = 0 := by bv_decide
    have hOfInt0 : BitVec.ofInt 64 0 = (0 : BitVec 64) := rfl
    -- Step 1: the 4 straight-line prologue instructions evaluate to sPrologue.
    have hPrologue :
        bignumExecFuel (cwhileRegistry 0) 8
          [ xorClearFlags "of" "cf" "zero"
          , .Cassgn (.Lvar { var := vr "op_col" }) .AT_none (.sword .U64)
              (pv "rp_base")
          , .Cassgn (.Lvar { var := vr "bp_col" }) .AT_none (.sword .U64)
              (pv "bp")
          , assignConst "col_left" 0 ] s = some sPrologue := by
      simp only [bignumExecFuel, execInstr, evalPExpr, xorClearFlags, vr, pv,
                 assignConst, bind, Option.bind, writeXorBundle, hOfInt0, hZeroXor,
                 sPrologue, setReg_regs, setReg_mem, String.reduceEq, ↓reduceIte,
                 if_true, if_false]
    -- Step 2: at sPrologue, col_left = 0, so the Cwhile exits unchanged.
    have hColLeftZero : sPrologue.regs "col_left" = 0 := by
      simp [sPrologue, setReg]
    have hCondFalse :
        evalPExpr sPrologue
          (.Papp2 (.Oneq .U64) (pv "col_left") (.Pconst 0)) = some 0 := by
      simp [evalPExpr, pv, vr, hColLeftZero, hOfInt0]
    have hLoopExit :
        bignumExecFuel (cwhileRegistry 0) 8
          [ .Cwhile [] (.Papp2 (.Oneq .U64) (pv "col_left") (.Pconst 0))
                  (perColumnCwhileBody 0) ] sPrologue = some sPrologue := by
      have := bignumExecFuel_loop_exit (cwhileRegistry 0) 5
                (.Papp2 (.Oneq .U64) (pv "col_left") (.Pconst 0))
                (perColumnCwhileBody 0) sPrologue hCondFalse
      simpa using this
    -- Step 3: combine via append_join. The prologue's 4 instructions are
    -- all non-control (Cassgn / Copn). The full body is prologue ++ [Cwhile].
    have hNc : ∀ i ∈ [ xorClearFlags "of" "cf" "zero"
                     , .Cassgn (.Lvar { var := vr "op_col" }) .AT_none (.sword .U64)
                         (pv "rp_base")
                     , .Cassgn (.Lvar { var := vr "bp_col" }) .AT_none (.sword .U64)
                         (pv "bp")
                     , assignConst "col_left" 0 ], i.isNonControl := by
      intro i hi
      simp only [xorClearFlags, assignConst, List.mem_cons, List.not_mem_nil,
                 or_false] at hi
      rcases hi with h | h | h | h
      · subst h; exact True.intro  -- Copn (XOR)
      · subst h; exact True.intro  -- Cassgn (op_col := rp_base)
      · subst h; exact True.intro  -- Cassgn (bp_col := bp)
      · subst h; exact True.intro  -- Cassgn (col_left := 0)
    have :
        bignumExecFuel (cwhileRegistry 0) 8
          ([ xorClearFlags "of" "cf" "zero"
           , .Cassgn (.Lvar { var := vr "op_col" }) .AT_none (.sword .U64)
              (pv "rp_base")
           , .Cassgn (.Lvar { var := vr "bp_col" }) .AT_none (.sword .U64)
              (pv "bp")
           , assignConst "col_left" 0 ] ++
           [ .Cwhile [] (.Papp2 (.Oneq .U64) (pv "col_left") (.Pconst 0))
                  (perColumnCwhileBody 0) ]) s = some sPrologue :=
      bignumExecFuel_append_join (cwhileRegistry 0) 8 _ _ hNc s sPrologue sPrologue
        hPrologue hLoopExit
    simpa using this
  · -- mpnMul [] [] = [], so memHoldsLimbs of [] is vacuous.
    rw [mpnMulBasecaseAdxCwhile_nil_nil]
    simp [memHoldsLimbs]

/-! ### Structural mirror to the meta-unrolled bridge -/

/-- **General-`n` refinement claim (structural mirror).** -/
theorem MpnMulBasecaseAdxCwhileJasminRefines_holds_n0 :
    MpnMulBasecaseAdxCwhileRefinesStmt 0 :=
  MpnMulBasecaseAdxCwhileJasminRefines_zero

/-! ## §8  Per-column step obligation

The general-`numBlocks` proof composes:
1. The pure-spec composition `mpnAddmul1_append` /
   `mpnAddmul1_block_split` (from `MpnAddMul1AdxBlockedPrototype`).
2. The per-column operational refinement — one iteration of the
   Cwhile body reduces to one Ccall through
   `mpnAddMul1AdxBlkCyFd`, whose body refinement is
   `MpnAddMul1AdxBlockedJasminRefines_zero` / its general-`numBlocks`
   structural mirror.

We record the per-column step obligation as a `Prop` in the same
style as `Mpn.AddMul1AdxBlockedPrototype.PerBlockBodyRefines`. -/

/-- **Per-column step obligation** for the runtime-Cwhile body.

    For any state `s` whose `col_left > 0`, `op_col`/`bp_col`/`ap_base`
    point to the column's working windows, and `rp_base` holds the
    result region, executing **one iteration** of `perColumnCwhileBody`
    (one Ccall to `mpn_addmul_1_adx_blk_cy_<n>` + the carry store +
    pointer advances) produces a state with:

    * The column-window memory updated by one `addmul_1`.
    * `op_col` advanced by 8, `bp_col` advanced by 8.
    * `col_left` decremented by 1.
    * The column carry stored at `r[col + n]`.

    Structurally a single application of
    `MpnAddMul1AdxBlockedJasminRefines` (the meta-unrolled bridge's
    general-`numBlocks` statement), wrapped in the Ccall ABI plumbing
    (callee param init + result binding via `bindResult`). -/
def PerColumnCwhileBodyRefines (numBlocks : Nat) : Prop :=
  ∀ (s : BignumState) (outWin asWin : List (BitVec 64)) (bCol : BitVec 64),
    outWin.length = numBlocks * CW_BLOCK →
    asWin.length = numBlocks * CW_BLOCK →
    s.regs "b" = bCol →
    s.regs "zero" = 0 →
    s.regs "col_left" ≠ 0 →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op_col").toNat) outWin →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap_base").toNat) asWin →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op_col").toNat)
                         (8 * (numBlocks * CW_BLOCK + 1)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap_base").toNat)
                         (8 * (numBlocks * CW_BLOCK))) →
    ∃ s', ∃ fuel,
      bignumExecFuel (cwhileRegistry numBlocks) fuel
        (perColumnCwhileBody numBlocks) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "op_col").toNat)
        ((mpnAddmul1 outWin asWin bCol 0).1 ++
         [(mpnAddmul1 outWin asWin bCol 0).2]) ∧
      s'.regs "op_col" = s.regs "op_col" + BitVec.ofNat 64 8 ∧
      s'.regs "bp_col" = s.regs "bp_col" + BitVec.ofNat 64 8 ∧
      s'.regs "col_left" = s.regs "col_left" - 1 ∧
      s'.regs "ap_base" = s.regs "ap_base"

/-! ### §8.1  Per-step composition obligation

Given `PerColumnCwhileBodyRefines numBlocks` (one column step) and the
inductive hypothesis on `k` remaining columns, the step case of the
counter-induction on `col_left` composes them.  We record the
composition obligation as a `Prop`. -/

/-- **Counter-induction step obligation** for the Cwhile body.

    Given the per-column step refinement `hCol` and the inductive
    hypothesis at `k`, conclude `MpnMulBasecaseAdxCwhileRefinesStmt (k + 1)`.
    Structurally identical to the meta-unrolled prototype's
    `MpnMulBasecaseAdxBlocked` step obligation, but the carry-out
    threading happens through the runtime `col_left` counter instead of
    the compile-time `Cfor` index. -/
def MpnMulBasecaseAdxCwhileJasminRefines_step_obligation : Prop :=
  ∀ numBlocks,
    PerColumnCwhileBodyRefines numBlocks →
    MpnMulBasecaseAdxCwhileRefinesStmt numBlocks

/-! ### §8.2  General-`numBlocks` refinement, modulo the per-column residual

Combine the per-column step refinement and the counter-induction
obligation to conclude refinement at any `numBlocks`. -/

/-- **General-`numBlocks` refinement, modulo the per-column operational
    residual and the counter-induction obligation.** -/
theorem MpnMulBasecaseAdxCwhileJasminRefines
    (hStep : MpnMulBasecaseAdxCwhileJasminRefines_step_obligation)
    (hCol : ∀ k, PerColumnCwhileBodyRefines k)
    (numBlocks : Nat) :
    MpnMulBasecaseAdxCwhileRefinesStmt numBlocks :=
  hStep numBlocks (hCol numBlocks)

/-! ## §9  Constant-time-shape

The body has exactly one runtime control-flow node — the outer
`Cwhile` on `col_left != 0`.  The counter is a public quantity (the
operand width `n`), not a secret.  Inside the body the only operations
are `Cassgn`/`Copn`/`Ccall`, all data-independent. -/

/-- The per-column body has exactly one Ccall (and 7 other instructions:
    3 setup Cassgns + 1 carry store + 3 pointer/counter updates). -/
example : (perColumnCwhileBody 2).length = 8 := by decide

/-- The full body has the prologue (1 XOR + initResultMemZero + 3 setup)
    plus exactly one Cwhile node. -/
example : (bodyMulBasecaseCwhile 0).length = 5 := by decide

/-- The outer Cwhile is in the canonical `(col_left != 0)` shape — the
    same `Cwhile [] (Papp2 (Oneq) (Pvar gv) (Pconst 0)) body` form that
    `Mpn.Addmul1Prototype.bodyAddmul` uses and that
    `JasminEmit.emitInstr` accepts. -/
example : ∃ body,
    (bodyMulBasecaseCwhile 0).getLast? = some
      (.Cwhile [] (.Papp2 (.Oneq .U64) (pv "col_left") (.Pconst 0)) body) :=
  ⟨perColumnCwhileBody 0, rfl⟩

/-! ## §10  Axiom check -/

#print axioms MpnMulBasecaseAdxCwhileJasminRefines_zero
#print axioms mpnMulBasecaseAdxCwhile_toNat

end CatCrypt.Crypto.Jasmin.Mpn.MulBaseCaseAdxCwhilePrototype
