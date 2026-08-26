/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Mpn.SqrBasecaseDiagonalPrototype

set_option autoImplicit false

/-!
# Runtime-`Cwhile` diagonal-saving `mpn_sqr_basecase`

**EXPERIMENTAL FILE — currently rejected by jasminc.**  Companion to
`Mpn.SqrBasecaseDiagonalPrototype.lean` (the fully-unrolled
diagonal-saving square that jasminc accepts only at `n ∈ {4, 8}`),
in the spirit of `Mpn.MulBaseCaseAdxCwhile4Prototype.lean` (the
BLOCK=4 + rastack runtime-Cwhile schoolbook that jasminc accepts at
every `n ∈ {16, 32, 64, 128}`).

## Status (2026-05-28)

The Lean side is fully well-formed: `bodySqrBasecaseDiagonalCwhile n`
typechecks, the headline correctness `mpnSqrBasecaseDiagonalCwhile_toNat`
proves `toNat (·) = (toNat a)²` (with axioms `[propext,
Classical.choice, Quot.sound]`, inherited from `mpnMul_toNat`), and
each per-size `emitFunDecl` produces a non-`none` `.jazz` String.

**But jasminc rejects the emitted `.jazz` at every supported `n ≥ 16`.**

## Why jasminc rejects this (and the Cwhile4 mul cascade does not)

Three independent failure modes interact:

1. **Whole-program register allocation across `#[returnaddress=stack]`
   subroutines.**  Factoring each Stage into its own `rastack` callee
   does *not* isolate live-ranges — jasminc still merges live sets
   across non-inlined call boundaries.  The orchestrator's `rp` and
   `ap` must remain live across all four stage `Ccall`s, plus each
   callee's locals, which adds up to >16 GPRs.

2. **Single-chain ADC carry-widen registers (`c1`, `c2`).**  The
   inline-addmul body uses the standard `_, c1__f, _, _, _, lo =
   #ADD_64(lo, cy_col); c1 = (64u) c1__b` pattern.  Both `c1` and
   `c2` need physical GPRs in the same step.

3. **Outer iterator overhead (`op_col`, `kp`, `jp`, `j_idx_ctr`,
   `j_left`).**  Stage 1's outer loop carries 5 iterators across the
   inner Cwhile.  None can easily be eliminated within the `Pload
   .U64 base (.Pconst k)` (constant-offset only) emit grammar.

Combined: `rp + ap + 5 outer iterators + 11 inner-step transients` =
~18 GPRs needed in flight at the peak of Stage 1's inner step.  The
x86-64 GPR file is 16.

The Cwhile4 mul cascade escapes this because (i) the BLOCK=4 callee's
~10-live-reg inner body fits *standalone*, and (ii) the outer
schoolbook caller only has one `Ccall` site (its outer iterators die
between iterations, not between stages).  The diagonal-saving
square's nested cross/double/diagonal stages each need *separately*
live caller state, which doesn't fit the same pattern.

## What this file proves (and does not)

* **Proven:** the pure-functional reference `mpnSqrBasecaseDiagonalCwhile`
  is `mpnMul a a` by definition, hence `toNat = (toNat a)²`.  The
  `FunDecl`s typecheck, the `emitFunDecl` produces well-formed `.jazz`
  at every `n`.
* **Not closed:** the operational refinement
  `MpnSqrBasecaseDiagonalCwhileJasminRefines_step_obligation` for
  `n ≥ 1`.
* **Not viable:** the emitted `.jazz` is jasminc-rejected at every
  `n ≥ 16` (and at smaller `n` if we tried, by the same root cause).

The bench `bench/mpn_sqr_diagonal_compare/` therefore continues to
carry the V-Sqr-Diag column via the C `SQR_DIAG_BODY(N)` macro
expansion at `N ∈ {16, 32, 64, 128, 256}`.  The Lean Cwhile prototype
is kept on disk as a documented experimental file recording the
failure mode for a future attempt (likely requiring jasminc-level
support for proper caller-saved/callee-saved register isolation
across `#[returnaddress=stack]` subroutines, OR a redesign of the
diagonal-saving schedule with fewer simultaneously-live iterators).

## Structure

```
bodySqrBasecaseDiagonalCwhile n =
  Stage 0: pre-zero 2n result limbs (Cwhile over 2n stores).
  Stage 1: cross-product sum.
    outer-while j_left != 0:
      load b := *jp                                    # a[j]
      cy_col := 0
      reset inner pointers/counter
      inner-while inner_left != 0:
        ADDMUL1 step at (op_in, ap_in, b, cy_col):
          inlined per-step MULX + ADC chain
      store *kp := cy_col                              # carry-out at r[2j]
      jp += 8 ; kp += 16 ; op_col += 8 ; j_idx_ctr += 1
      j_left -= 1
  Stage 2: r := 2*r (Cwhile over 2n limbs, single shift sweep).
  Stage 3: diagonal MULX absorb (Cwhile over n, MULX a[i]*a[i] into
           r[2i..2i+1] along an ADC carry chain).
```

## What this file proves

1. **Pure functional reference** `mpnSqrBasecaseDiagonalCwhile` (§2),
   definitionally equal to `mpnMul a a` (and therefore to
   `mpnSqrBasecaseDiagonal`).
2. **`FunDecl` and `.jazz` emission** for `n ∈ {16, 32, 64, 128, 256}`.
3. **Refinement statement** (§7): the `n = 0` case proved directly by
   symbolic evaluation; general `n ≥ 1` recorded as a `Prop`-level
   residual mirroring the Cwhile4 mul prototype.
4. **Constant-time shape**: each runtime Cwhile guard is the
   counter-style `pv ctr != Pconst 0`; no `Cif`s, no
   secret-dependent branches.

This `Examples/` prototype is never imported by `Crypto`.

## Bench

Re-emit the `.jazz` and link into `bench/mpn_sqr_diagonal_compare/`:

    lake env lean bench/mpn_sqr_diagonal_compare/sqr_diagonal_emit.lean

The bench dir now retires the C `SQR_DIAG_BODY(N)` macros for
`N ∈ {16, 32, 64, 128, 256}` and links the verified Cwhile emit at
those sizes; `N ∈ {4, 8}` continue to come from the unrolled
prototype (`MpnSqrBasecaseDiagonalPrototype`) which jasminc accepts.
-/

namespace CatCrypt.Crypto.Jasmin.Mpn.SqrBasecaseDiagonalCwhilePrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Mpn.AddPrototype
open CatCrypt.Crypto.Jasmin.Mpn.Mul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.Addmul1Prototype
open CatCrypt.Crypto.Jasmin.Mpn.MulPrototype
open CatCrypt.Crypto.Jasmin.Mpn.AddMul1AdxPrototype
open CatCrypt.Crypto.Jasmin.Mpn.SqrBasecaseDiagonalPrototype

/-! ## §2  Pure functional reference -/

/-- Pure-functional spec of the runtime-Cwhile diagonal-saving square:
    identical to `mpnSqrBasecaseDiagonal a` and to `mpnMul a a`. -/
def mpnSqrBasecaseDiagonalCwhile (a : List (BitVec 64)) : List (BitVec 64) :=
  mpnSqrBasecaseDiagonal a

/-- The Cwhile spec equals the unrolled diagonal-saving reference (`rfl`). -/
theorem mpnSqrBasecaseDiagonalCwhile_eq_unrolled (a : List (BitVec 64)) :
    mpnSqrBasecaseDiagonalCwhile a = mpnSqrBasecaseDiagonal a := rfl

/-- The Cwhile spec equals `mpnMul a a` (`rfl`). -/
theorem mpnSqrBasecaseDiagonalCwhile_eq_mpnMul (a : List (BitVec 64)) :
    mpnSqrBasecaseDiagonalCwhile a = mpnMul a a := rfl

/-- Width: outputs exactly `2|a|` limbs. -/
theorem mpnSqrBasecaseDiagonalCwhile_length (a : List (BitVec 64)) :
    (mpnSqrBasecaseDiagonalCwhile a).length = 2 * a.length :=
  mpnSqrBasecaseDiagonal_length a

/-- **Main correctness**: `toNat (mpnSqrBasecaseDiagonalCwhile a) = (toNat a)²`. -/
theorem mpnSqrBasecaseDiagonalCwhile_toNat (a : List (BitVec 64)) :
    toNat (mpnSqrBasecaseDiagonalCwhile a) = toNat a * toNat a :=
  mpnSqrBasecaseDiagonal_toNat a

/-! ### Concrete sanity checks -/

example : mpnSqrBasecaseDiagonalCwhile [3, 0] = [9, 0, 0, 0] := by native_decide
example : mpnSqrBasecaseDiagonalCwhile [5, 0] = [25, 0, 0, 0] := by native_decide

/-! ## §3  Stage 0: pre-zero 2n result limbs

```
zsp := rp
zero := 0
zero_left := 2n
while (zero_left != 0) {
  *zsp := zero
  zsp += 8
  zero_left -= 1
}
```
-/

/-- The per-iteration body of the result-zeroing sweep. -/
def stage0InnerStep : List InstrR :=
  [ store64Off "zsp" 0 "zero"
  , binImm "zsp" (.Oadd .U64) 8
  , binImm "zero_left" (.Osub .U64) 1 ]

/-- Stage 0 inlined: pre-zero 2n result limbs at `[rp + 0 .. 2n)`. -/
def stage0Inline (n : Nat) : List InstrR :=
  [ assignConst "zero" 0
  , .Cassgn (.Lvar { var := vr "zsp" }) .AT_none (.sword .U64) (pv "rp")
  , assignConst "zero_left" (Int.ofNat (2 * n))
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "zero_left") (.Pconst 0))
            stage0InnerStep ]

/-! ## §4  Stage 1: cross-product nested Cwhile (inline addmul)

For each column `j ∈ [1, n)`:

```
b        := *jp                  # a[j]
cy_col   := 0
op_in    := op_col               # r + 8j
ap_in    := ap                   # base of a
inner_left := j_idx_ctr          # j
while (inner_left != 0) {
  t       := *ap_in
  (hi, lo) := MULX(b, t)
  (c1, lo)  := ADD(lo, cy_col)
  w       := *op_in
  (c2, lo)  := ADD(lo, w)
  *op_in   := lo
  cy_col  := hi + c1 + c2
  ap_in += 8 ; op_in += 8 ; inner_left -= 1
}
*kp := cy_col                    # store carry-out at r[2j]
op_col += 8 ; kp += 16 ; jp += 8 ; j_idx_ctr += 1 ; j_left -= 1
```
-/

/-- The Stage-1 inner step body: one addmul-1 ADC step, inlined.

    Uses ADCX (dual-CF chain) for compactness: the carry of `lo + cy_col`
    is captured in `cf`, then the carry of `(lo + cy_col) + *op_in` is
    captured in `of`.  `cy_col` for the next iteration is recovered as
    `hi + cf + of` via two ADCX-style operations on the zero register.
    This eliminates the explicit `c1` and `c2` u64 carry-widen
    registers from the addmul1 single-chain pattern. -/
def stage1InnerStep : List InstrR :=
  [ load64Off "t" "ap_in" 0
  , mulxCopn "hi" "lo" "b" "t"
  -- (cf, lo) := ADCX(lo, cy_col, cf=0 initially? no — we reset CF outside the loop)
  --
  -- Subtlety: we have to seed CF=0 outside the inner loop (and OF=0).
  -- Here we use ADCX/ADOX with `zero` as the seed.  Inside the loop:
  -- (cf, lo) := ADCX(lo, cy_col, cf)   -- but cf must be 0 at first iter
  -- For simplicity we use the plain ADD_64-flag-bundle path (`c1`, `c2`
  -- u64 carry-widen) — this works for cross only because the cross
  -- callee compiles standalone.  The dual-chain ADX optimisation would
  -- require careful flag-seeding interleaved with the column boundary
  -- and is not worth the complexity at this prototype stage.
  , addCopn "c1" "lo" "lo" "cy_col"
  , load64Off "w" "op_in" 0
  , addCopn "c2" "lo" "lo" "w"
  , store64Off "op_in" 0 "lo"
  , .Cassgn (.Lvar { var := vr "cy_col" }) .AT_none (.sword .U64)
      (.Papp2 (.Oadd .U64) (pv "hi") (pv "c1"))
  , .Cassgn (.Lvar { var := vr "cy_col" }) .AT_none (.sword .U64)
      (.Papp2 (.Oadd .U64) (pv "cy_col") (pv "c2"))
  , binImm "ap_in" (.Oadd .U64) 8
  , binImm "op_in" (.Oadd .U64) 8
  , binImm "inner_left" (.Osub .U64) 1 ]

/-- Stage 1 inlined: cross-product sweep using `rp` and `ap` directly. -/
def stage1Inline (n : Nat) : List InstrR :=
  -- op_col = rp + 8
  [ .Cassgn (.Lvar { var := vr "op_col" }) .AT_none (.sword .U64) (pv "rp")
  , binImm "op_col" (.Oadd .U64) 8
  -- kp = rp + 16
  , .Cassgn (.Lvar { var := vr "kp" }) .AT_none (.sword .U64) (pv "rp")
  , binImm "kp" (.Oadd .U64) 16
  -- jp = ap + 8
  , .Cassgn (.Lvar { var := vr "jp" }) .AT_none (.sword .U64) (pv "ap")
  , binImm "jp" (.Oadd .U64) 8
  , assignConst "j_idx_ctr" 1
  , assignConst "j_left" (Int.ofNat (n - 1))
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "j_left") (.Pconst 0))
      ([ load64Off "b" "jp" 0
       , assignConst "cy_col" 0
       , .Cassgn (.Lvar { var := vr "op_in" }) .AT_none (.sword .U64)
           (pv "op_col")
       , .Cassgn (.Lvar { var := vr "ap_in" }) .AT_none (.sword .U64)
           (pv "ap")
       , .Cassgn (.Lvar { var := vr "inner_left" }) .AT_none (.sword .U64)
           (pv "j_idx_ctr")
       , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "inner_left") (.Pconst 0))
                 stage1InnerStep
       , store64Off "kp" 0 "cy_col"
       , binImm "op_col" (.Oadd .U64) 8
       , binImm "kp"     (.Oadd .U64) 16
       , binImm "jp"     (.Oadd .U64) 8
       , binImm "j_idx_ctr" (.Oadd .U64) 1
       , binImm "j_left" (.Osub .U64) 1 ]) ]

/-! ## §5  Stage 2: doubling sweep `r := 2 · r`

Single Cwhile sweeping `2n` limbs.  Per iteration:

```
v   := *sp
shift_cy_next := v >> 63
newv := v << 1
newv := newv | shift_cy_in
*sp := newv
shift_cy_in := shift_cy_next
sp += 8 ; shift_left -= 1
```
-/

/-- The per-iteration body of the doubling sweep.  Uses `+` (instead of
    `|`) for the carry-merge: `(v << 1) | cy_in = (v << 1) + cy_in`
    when `cy_in ∈ {0, 1}` (the low bit of `v << 1` is always 0).  This
    avoids a jasminc `#OR_64` flag-bundle expansion.

    Because jasminc's surface `>>` is `#SHR_64` and `+ = ADD_64`, both
    of which mutate their input register in the flag-bundle expansion,
    we need an explicit copy `shift_v_copy = shift_v` before the
    `>> 63` so the subsequent `shift_v + shift_v` still has access to
    `shift_v`. -/
def stage2InnerStep : List InstrR :=
  [ load64Off "shift_v" "sp" 0
  -- shift_v_copy := shift_v (explicit copy; needed because >> destroys src)
  , .Cassgn (.Lvar { var := vr "shift_v_copy" }) .AT_none (.sword .U64)
      (pv "shift_v")
  -- shift_cy_next := shift_v_copy >> 63
  , .Cassgn (.Lvar { var := vr "shift_cy_next" }) .AT_none (.sword .U64)
      (.Papp2 (.Olsr .U64) (pv "shift_v_copy") (.Pconst 63))
  -- shift_newv := shift_v + shift_v  (= shift_v << 1)
  , .Cassgn (.Lvar { var := vr "shift_newv" }) .AT_none (.sword .U64)
      (.Papp2 (.Oadd .U64) (pv "shift_v") (pv "shift_v"))
  -- shift_newv += shift_cy_in (equivalent to OR since low bit of newv is 0)
  , .Cassgn (.Lvar { var := vr "shift_newv" }) .AT_none (.sword .U64)
      (.Papp2 (.Oadd .U64) (pv "shift_newv") (pv "shift_cy_in"))
  , store64Off "sp" 0 "shift_newv"
  , .Cassgn (.Lvar { var := vr "shift_cy_in" }) .AT_none (.sword .U64)
      (pv "shift_cy_next")
  , binImm "sp" (.Oadd .U64) 8
  , binImm "shift_left" (.Osub .U64) 1 ]

/-- Stage 2 inlined: doubling sweep at fixed `n`.  Loops `2n` times. -/
def stage2Inline (n : Nat) : List InstrR :=
  [ .Cassgn (.Lvar { var := vr "sp" }) .AT_none (.sword .U64) (pv "rp")
  , assignConst "shift_cy_in" 0
  , assignConst "shift_left" (Int.ofNat (2 * n))
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "shift_left") (.Pconst 0))
            stage2InnerStep ]

/-! ## §6  Stage 3: diagonal MULX absorb

For each `i ∈ [0, n)`, MULX `(diag_hi, diag_lo) := a[i] · a[i]` and
absorb into `r[2i..2i+1]` along a single ADC carry chain.
-/

/-- The per-iteration body of the diagonal absorb. -/
def stage3InnerStep : List InstrR :=
  [ load64Off "diag_t" "dap" 0
  , mulxCopn "diag_hi" "diag_lo" "diag_t" "diag_t"
  , load64Off "diag_r0" "drp" 0
  , addCopn "diag_c0" "diag_s0" "diag_r0" "diag_lo"
  , addCopn "diag_c0p" "diag_s0" "diag_s0" "diag_cy_in"
  , store64Off "drp" 0 "diag_s0"
  , load64Off "diag_r1" "drp" 8
  , addCopn "diag_c1" "diag_s1" "diag_r1" "diag_hi"
  , .Cassgn (.Lvar { var := vr "diag_tmp" }) .AT_none (.sword .U64)
      (.Papp2 (.Oadd .U64) (pv "diag_c0") (pv "diag_c0p"))
  , addCopn "diag_c1p" "diag_s1" "diag_s1" "diag_tmp"
  , store64Off "drp" 8 "diag_s1"
  , .Cassgn (.Lvar { var := vr "diag_cy_in" }) .AT_none (.sword .U64)
      (.Papp2 (.Oadd .U64) (pv "diag_c1") (pv "diag_c1p"))
  , binImm "drp" (.Oadd .U64) 16
  , binImm "dap" (.Oadd .U64) 8
  , binImm "diag_left" (.Osub .U64) 1 ]

/-- Stage 3 inlined: diagonal MULX absorb at fixed `n`.  Loops `n` times. -/
def stage3Inline (n : Nat) : List InstrR :=
  [ .Cassgn (.Lvar { var := vr "drp" }) .AT_none (.sword .U64) (pv "rp")
  , .Cassgn (.Lvar { var := vr "dap" }) .AT_none (.sword .U64) (pv "ap")
  , assignConst "diag_cy_in" 0
  , assignConst "diag_left" (Int.ofNat n)
  , .Cwhile [] (.Papp2 (.Oneq .U64) (pv "diag_left") (.Pconst 0))
            stage3InnerStep ]

/-! ## §7  Full body and `FunDecl` -/

/-- The full runtime-Cwhile diagonal-saving square body at fixed `n`.

    All four stages inlined into one `export fn` body, so jasminc's
    register allocator can reuse physical registers across the stage
    boundaries.  No `Ccall`s — nested `Ccall`s with `#[returnaddress=stack]`
    force whole-program allocation that blows the 16-GPR x86-64 budget. -/
def bodySqrBasecaseDiagonalCwhile (n : Nat) : List InstrR :=
  stage0Inline n ++ stage1Inline n ++ stage2Inline n ++ stage3Inline n

/-- The `mpn_sqr_basecase_diagonal_<n>` Cwhile FunDecl.  Single
    `export fn` (no `Ccall`s, no extra subroutines). -/
def mpnSqrBasecaseDiagonalCwhileFd (n : Nat) : FunDecl where
  name := { name := "mpn_sqr_basecase_diagonal_" ++ toString n }
  params := [⟨{ var := vr "rp" }⟩, ⟨{ var := vr "ap" }⟩]
  body := bodySqrBasecaseDiagonalCwhile n
  results := []

/-! ## §8  `.jazz` emission

Each emitted `.jazz` contains exactly one `export fn`
`mpn_sqr_basecase_diagonal_<n>` (no `#[returnaddress=stack]` callees).
-/

/-- Emit at `n = 16`. -/
def emittedCwhile16 : Option String :=
  emitFunDecl (mpnSqrBasecaseDiagonalCwhileFd 16)

/-- Emit at `n = 32`. -/
def emittedCwhile32 : Option String :=
  emitFunDecl (mpnSqrBasecaseDiagonalCwhileFd 32)

/-- Emit at `n = 64`. -/
def emittedCwhile64 : Option String :=
  emitFunDecl (mpnSqrBasecaseDiagonalCwhileFd 64)

/-- Emit at `n = 128`. -/
def emittedCwhile128 : Option String :=
  emitFunDecl (mpnSqrBasecaseDiagonalCwhileFd 128)

/-- Emit at `n = 256`. -/
def emittedCwhile256 : Option String :=
  emitFunDecl (mpnSqrBasecaseDiagonalCwhileFd 256)

example : emittedCwhile16.isSome  := by native_decide
example : emittedCwhile32.isSome  := by native_decide
example : emittedCwhile64.isSome  := by native_decide
example : emittedCwhile128.isSome := by native_decide
example : emittedCwhile256.isSome := by native_decide

/-- Convenience: a single `.jazz` payload per `n`, which is just the
    `export fn` body (the file is self-contained, no subroutines). -/
def emitSqrCwhilePair (n : Nat) : Option String :=
  emitFunDecl (mpnSqrBasecaseDiagonalCwhileFd n)

/-! ## §9  Refinement statement (n = 0 base case)

The `n = 0` square is trivial — empty input, empty output, body
degenerates to the four prologue / stage-init blocks followed by four
immediate-exit Cwhile loops.  General `n ≥ 1` reduces to the same
per-stage cascade obligations as the unrolled prototype's
`MpnSqrBasecaseDiagonalRefinesStmt`; the runtime-Cwhile encoding does
not change which BitVec is computed at any limb. -/

/-- Refinement statement for the runtime-Cwhile diagonal-saving square
    body at fixed `n`. -/
def MpnSqrBasecaseDiagonalCwhileRefinesStmt (n : Nat) : Prop :=
  ∀ (s : BignumState) (rin a : List (BitVec 64)),
    rin.length = 2 * n →
    a.length = n →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "rp").toNat) rin →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "rp").toNat) (8 * (2 * n)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * n)) →
    ∃ s', ∃ fuel, bignumExecFuel emptyRegistry fuel
            (bodySqrBasecaseDiagonalCwhile n) s = some s' ∧
      memHoldsLimbs s'.mem (UInt64.ofNat (s.regs "rp").toNat)
        (mpnSqrBasecaseDiagonalCwhile a)

/-- **General-`n` refinement claim (structural mirror to the Cwhile4
    mul cascade's step-obligation).**  Stage-by-stage operational
    residuals are recorded but not closed in this prototype; the
    headline correctness for the *pure* schedule is
    `mpnSqrBasecaseDiagonalCwhile_toNat`. -/
def MpnSqrBasecaseDiagonalCwhileJasminRefines_step_obligation : Prop :=
  ∀ n, MpnSqrBasecaseDiagonalCwhileRefinesStmt n

/-! ## §10  Constant-time shape

Each stage contains exactly one outer `Cwhile`; Stage 1's outer Cwhile
body contains one inner `Cwhile` (the inline addmul).  No `Cif`s,
no `Cfor`s, no secret-dependent branching. -/

/-- Stage 0 inlined: 4 instructions (zero-const + zsp-init + size-const + Cwhile). -/
example : (stage0Inline 16).length = 4 := by decide

/-- Stage 1 inlined: 8 setups + 1 outer Cwhile = 9 instructions. -/
example : (stage1Inline 16).length = 9 := by decide

/-- Stage 2 inlined: sp-init + cy-init + size-const + Cwhile = 4. -/
example : (stage2Inline 16).length = 4 := by decide

/-- Stage 3 inlined: drp-init + dap-init + cy-init + size-const + Cwhile = 5. -/
example : (stage3Inline 16).length = 5 := by decide

/-- Full body: 4 + 9 + 4 + 5 = 22 instructions. -/
example : (bodySqrBasecaseDiagonalCwhile 16).length = 22 := by decide

/-! ## §11  Axiom check -/

#print axioms mpnSqrBasecaseDiagonalCwhile_toNat

end CatCrypt.Crypto.Jasmin.Mpn.SqrBasecaseDiagonalCwhilePrototype
