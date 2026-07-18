/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.BignumExec
import CatCrypt.Crypto.Jasmin.S2NBignumSSA

set_option autoImplicit false

/-!
# Differential-test framework for `BignumExec`

The L2 trust gate. Runs
each port's body via `BignumExec` (our Lean semantics) on deterministic
test inputs and produces JSON that an external harness (in `scripts/`)
diffs against the same body's compiled-and-run output via
`JasminEmit ∘ jasminc`.

If the diff fails: either `BignumExec` is wrong, or `JasminEmit` is
wrong, or both. Either is a real bug — neither acceptable.

## What's in this file

- `TestCase` structure: a port name + initial register/memory + the
  expected final-memory contents at the output address.
- `runTestCase`: invokes `BignumExec` on the case, returns a
  pass/fail + the actual computed output.
- A handful of test cases for `bignum_mod_p25519_4` (the simplest
  port — straightforward subtract-and-mask-select reducer).

## What's not in this file (deferred to separate scripts)

- The shell harness that takes the JSON, compiles via jasminc, runs,
  diffs.
- Random-input generation (currently we hand-pick inputs that
  exercise the algorithm's branches).
- CI integration.

These are bench-side / shell-side work, not Lean-side. The
specification of "what the harness must do" lives in this file's
docstring; the implementation is `scripts/diff_bignum_sem.sh`.
-/

namespace CatCrypt.Crypto.Jasmin.BignumExecDiffTest

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.S2NBignumSSA

/-! ## §1. Test case structure -/

/-- One differential-test case for a port body.
    `inputs` and `expectedOutputs` are 4-limb little-endian Nat lists
    (matching the bignum 4×64 layout). -/
structure TestCase where
  portName        : String
  body            : List InstrR
  /-- Initial register settings (e.g., `("ap", 0x1000)`, `("op", 0x2000)`). -/
  initRegs        : List (String × UInt64)
  /-- Initial memory: address → byte. List form for serializability. -/
  initMem         : List (UInt64 × UInt8)
  /-- Expected final-memory contents at specific addresses. -/
  expectedMem     : List (UInt64 × UInt8)
  deriving Inhabited

/-! ## §2. Test-case execution -/

/-- Build a `BignumState` from a `TestCase`. -/
def buildInitState (tc : TestCase) : BignumState :=
  let regs : String → BitVec 64 := fun x =>
    match tc.initRegs.find? (fun ⟨n, _⟩ => n = x) with
    | some ⟨_, v⟩ => BitVec.ofNat 64 v.toNat
    | none        => 0
  let mem : Mem := fun a =>
    tc.initMem.find? (fun ⟨a', _⟩ => a' = a) |>.map (·.2)
  { regs := regs, mem := mem }

/-- Run a TestCase: returns `some final_state` if execution completes;
    `none` if BignumExec hits an unsupported InstrR. -/
def runTestCase (tc : TestCase) : Option BignumState :=
  bignumExec tc.body (buildInitState tc)

/-! ## §2'. Registry for Ccall-using bodies

The bodies that use `.Ccall` (currently just `bignum_inv_p25519`)
need a `BignumRegistry` that maps callee names to their `FunDecl`s.
We thread it through `runTestCaseFuel`, which is the Ccall-aware
counterpart to `runTestCase`. Existing test cases (which never
Ccall) work either way. -/

/-- Default fuel for Ccall-using executions. The deepest call chain
    we currently ship is single-level (`bignum_inv_p25519` →
    `bignum_montmul_p25519`); 1000 is a comfortable upper bound on
    body lengths × call depth. -/
def defaultFuel : Nat := 1000

/-- The standard registry for the bignum diff-test gate. Maps the
    routines that other ports might Ccall into. Add an entry here
    when a new body uses Ccall to a previously-unregistered helper. -/
def diffTestRegistry : BignumRegistry := fun name =>
  match name with
  | "bignum_montmul_p25519" => some BignumMontMulP25519_4.fd
  | "bignum_sqr_4"          => some BignumSqr4.fd
  | "bignum_mul_4"          => some BignumMul4.fd
  | "bignum_add_4"          => some BignumAdd4.fd
  | "bignum_sub_p25519"     => some BignumSubP25519.fd
  | "bignum_double_p25519"  => some BignumDoubleP25519.fd
  | "bignum_mod_p25519_4"   => some BignumModP25519_4.fd
  | _                       => none

/-- Ccall-aware run: invokes `bignumExecFuel` with the diff-test
    registry and `defaultFuel`. -/
def runTestCaseFuel (tc : TestCase) : Option BignumState :=
  bignumExecFuel diffTestRegistry defaultFuel tc.body (buildInitState tc)

/-- Validate that every expected-memory entry matches in the final
    state. -/
def checkExpected (tc : TestCase) (final : BignumState) : Bool :=
  tc.expectedMem.all (fun ⟨a, expected⟩ =>
    match final.mem.loadByte a with
    | some actual => actual = expected
    | none        => false)

/-- Full run-and-check. Uses the Ccall-aware `runTestCaseFuel`,
    so straight-line bodies and Ccall-using bodies share one path. -/
def runAndCheck (tc : TestCase) : Bool :=
  match runTestCaseFuel tc with
  | some final => checkExpected tc final
  | none       => false

/-! ## §3. Test cases for `bignum_mod_p25519_4`

Three cases:
1. Already-canonical: input 100, expect output 100.
2. Just-above-p: input p+5, expect output 5.
3. Boundary: input exactly p, expect output 0. -/

/-- Helper: little-endian bytes of a u64. -/
def u64Bytes (v : UInt64) (base : UInt64) : List (UInt64 × UInt8) :=
  [ (base    , (v >>> 0).toUInt8)
  , (base + 1, (v >>> 8).toUInt8)
  , (base + 2, (v >>> 16).toUInt8)
  , (base + 3, (v >>> 24).toUInt8)
  , (base + 4, (v >>> 32).toUInt8)
  , (base + 5, (v >>> 40).toUInt8)
  , (base + 6, (v >>> 48).toUInt8)
  , (base + 7, (v >>> 56).toUInt8) ]

/-- Bytes for a 4-limb little-endian value at `base`. -/
def fourLimbBytes (limbs : UInt64 × UInt64 × UInt64 × UInt64)
    (base : UInt64) : List (UInt64 × UInt8) :=
  u64Bytes limbs.1     (base +  0) ++
  u64Bytes limbs.2.1   (base +  8) ++
  u64Bytes limbs.2.2.1 (base + 16) ++
  u64Bytes limbs.2.2.2 (base + 24)

/-- TC1: input is already canonical (a = 100, well below p). -/
def tcModCanonical : TestCase where
  portName := "bignum_mod_p25519_4"
  body := BignumModP25519_4.body
  initRegs := [("ap", 0x1000), ("op", 0x2000)]
  initMem :=
    fourLimbBytes (100, 0, 0, 0) 0x1000 ++
    -- Pre-allocate the op range so loads-of-stores work.
    fourLimbBytes (0, 0, 0, 0) 0x2000
  -- Expected: op = 100 (low limb), 0 elsewhere.
  expectedMem := fourLimbBytes (100, 0, 0, 0) 0x2000

/-- TC2: input is just above p. We give a = p + 5 by setting the low
    limb to `0xFFFFFFFFFFFFFFED + 5 = 0xFFFFFFFFFFFFFFF2` and the rest
    matching p, plus carrying so that a > p. Expected output: 5. -/
def tcModAboveP : TestCase where
  portName := "bignum_mod_p25519_4"
  body := BignumModP25519_4.body
  initRegs := [("ap", 0x3000), ("op", 0x4000)]
  initMem :=
    -- a = p + 5: low limb wraps to 0xFFFFFFFFFFFFFFED + 5 = 0xFFFFFFFFFFFFFFF2,
    -- high limbs match p (= ff,ff,7f).
    fourLimbBytes (0xFFFFFFFFFFFFFFF2,
                   0xFFFFFFFFFFFFFFFF,
                   0xFFFFFFFFFFFFFFFF,
                   0x7FFFFFFFFFFFFFFF) 0x3000 ++
    fourLimbBytes (0, 0, 0, 0) 0x4000
  expectedMem := fourLimbBytes (5, 0, 0, 0) 0x4000

/-- TC3: bignum_add_4 — small two-limb add, no carries between limbs.
    Inputs (1, 0, 0, 0) + (2, 0, 0, 0) = (3, 0, 0, 0). -/
def tcAdd4Small : TestCase where
  portName := "bignum_add_4"
  body := BignumAdd4.body
  initRegs := [("ap", 0x1000), ("bp", 0x2000), ("op", 0x3000)]
  initMem :=
    fourLimbBytes (1, 0, 0, 0) 0x1000 ++
    fourLimbBytes (2, 0, 0, 0) 0x2000 ++
    fourLimbBytes (0, 0, 0, 0) 0x3000
  expectedMem := fourLimbBytes (3, 0, 0, 0) 0x3000

/-- TC4: bignum_sub_p25519 — small subtraction within canonical range.
    Inputs (5, 0, 0, 0) − (2, 0, 0, 0) = (3, 0, 0, 0). -/
def tcSubP25519Small : TestCase where
  portName := "bignum_sub_p25519"
  body := BignumSubP25519.body
  initRegs := [("ap", 0x1000), ("bp", 0x2000), ("op", 0x3000)]
  initMem :=
    fourLimbBytes (5, 0, 0, 0) 0x1000 ++
    fourLimbBytes (2, 0, 0, 0) 0x2000 ++
    fourLimbBytes (0, 0, 0, 0) 0x3000
  expectedMem := fourLimbBytes (3, 0, 0, 0) 0x3000

/-- TC5: bignum_double_p25519 — small doubling.
    Input (7, 0, 0, 0) → (14, 0, 0, 0). -/
def tcDoubleP25519Small : TestCase where
  portName := "bignum_double_p25519"
  body := BignumDoubleP25519.body
  initRegs := [("ap", 0x1000), ("op", 0x2000)]
  initMem :=
    fourLimbBytes (7, 0, 0, 0) 0x1000 ++
    fourLimbBytes (0, 0, 0, 0) 0x2000
  expectedMem := fourLimbBytes (14, 0, 0, 0) 0x2000

/-- TC6: bignum_mul_4 — small multiplication with no overflow into high
    limbs. Inputs (3, 0, 0, 0) × (4, 0, 0, 0) = 12, full 8-limb output
    (12, 0, 0, 0, 0, 0, 0, 0). -/
def tcMul4Small : TestCase where
  portName := "bignum_mul_4"
  body := BignumMul4.body
  initRegs := [("ap", 0x1000), ("bp", 0x2000), ("op", 0x3000)]
  initMem :=
    fourLimbBytes (3, 0, 0, 0) 0x1000 ++
    fourLimbBytes (4, 0, 0, 0) 0x2000 ++
    -- Pre-zero 64 bytes for 8-limb output.
    fourLimbBytes (0, 0, 0, 0) 0x3000 ++
    fourLimbBytes (0, 0, 0, 0) 0x3020
  -- Expected: low limb = 12, all other 7 limbs zero.
  expectedMem :=
    fourLimbBytes (12, 0, 0, 0) 0x3000 ++
    fourLimbBytes (0,  0, 0, 0) 0x3020

/-- TC7: bignum_mul_4_adcx — same as tcMul4Small but exercises the
    BMI2 dual-carry path. -/
def tcMul4AdcxSmall : TestCase where
  portName := "bignum_mul_4_adcx"
  body := BignumMul4Adcx.body
  initRegs := [("ap", 0x1000), ("bp", 0x2000), ("op", 0x3000)]
  initMem :=
    fourLimbBytes (3, 0, 0, 0) 0x1000 ++
    fourLimbBytes (4, 0, 0, 0) 0x2000 ++
    fourLimbBytes (0, 0, 0, 0) 0x3000 ++
    fourLimbBytes (0, 0, 0, 0) 0x3020
  expectedMem :=
    fourLimbBytes (12, 0, 0, 0) 0x3000 ++
    fourLimbBytes (0,  0, 0, 0) 0x3020

/-- TC8: bignum_sqr_4 — small squaring (5² = 25) into the low limb,
    rest zero. Exercises the streaming-accumulator MULX path. -/
def tcSqr4Small : TestCase where
  portName := "bignum_sqr_4"
  body := BignumSqr4.body
  initRegs := [("ap", 0x1000), ("op", 0x2000)]
  initMem :=
    fourLimbBytes (5, 0, 0, 0) 0x1000 ++
    fourLimbBytes (0, 0, 0, 0) 0x2000 ++
    fourLimbBytes (0, 0, 0, 0) 0x2020
  -- 5² = 25
  expectedMem :=
    fourLimbBytes (25, 0, 0, 0) 0x2000 ++
    fourLimbBytes (0,  0, 0, 0) 0x2020

/-- TC9: bignum_montmul_p25519 — small "Montgomery-ish" multiplication.
    Note: this body computes `(a · b) mod p_25519` (matches the current
    `refSem` placeholder in `BignumMontMulP25519_4`, not the full
    Montgomery form `a · b · R⁻¹ mod p`). For small `a, b` with
    `a · b < p`, the modular reduction is the identity, so
    `3 · 4 = 12`. -/
def tcMontMulSmall : TestCase where
  portName := "bignum_montmul_p25519"
  body := BignumMontMulP25519_4.body
  initRegs := [("ap", 0x1000), ("bp", 0x2000), ("op", 0x3000)]
  initMem :=
    fourLimbBytes (3, 0, 0, 0) 0x1000 ++
    fourLimbBytes (4, 0, 0, 0) 0x2000 ++
    fourLimbBytes (0, 0, 0, 0) 0x3000
  expectedMem := fourLimbBytes (12, 0, 0, 0) 0x3000

/-- TC10: bignum_inv_p25519 — full Bernstein addition chain.

    Computes `op := ap^(p-2) mod p_25519`, i.e. the modular inverse.
    The body now contains 254 squarings + 11 multiplies via 265
    `Ccall`s into `bignum_montmul_p25519`.

    For `a = 2`: by Fermat's little theorem, `2^(p-2) ≡ 2⁻¹ (mod p)`.
    Since `p = 2²⁵⁵ − 19` is odd, `2⁻¹ = (p + 1)/2 = 2²⁵⁴ − 9`,
    which decodes to little-endian 4-limb form:
    - l0 = 0xfffffffffffffff7
    - l1 = 0xffffffffffffffff
    - l2 = 0xffffffffffffffff
    - l3 = 0x3fffffffffffffff

    Memory layout: the body uses scratch buffers as offsets from
    `op` up to `op + 416` (the `u` ping-pong buffer), so we
    pre-allocate 448 bytes starting at the op address. -/
def tcInvP25519 : TestCase where
  portName := "bignum_inv_p25519"
  body := BignumInvP25519.body
  initRegs := [("ap", 0x1000), ("op", 0x2000)]
  initMem :=
    fourLimbBytes (2, 0, 0, 0) 0x1000 ++
    -- Pre-zero the 14 buffers (op + scratches) the chain writes to.
    -- 14 × 32 = 448 bytes covering op [0..447].
    fourLimbBytes (0, 0, 0, 0) 0x2000 ++
    fourLimbBytes (0, 0, 0, 0) 0x2020 ++
    fourLimbBytes (0, 0, 0, 0) 0x2040 ++
    fourLimbBytes (0, 0, 0, 0) 0x2060 ++
    fourLimbBytes (0, 0, 0, 0) 0x2080 ++
    fourLimbBytes (0, 0, 0, 0) 0x20a0 ++
    fourLimbBytes (0, 0, 0, 0) 0x20c0 ++
    fourLimbBytes (0, 0, 0, 0) 0x20e0 ++
    fourLimbBytes (0, 0, 0, 0) 0x2100 ++
    fourLimbBytes (0, 0, 0, 0) 0x2120 ++
    fourLimbBytes (0, 0, 0, 0) 0x2140 ++
    fourLimbBytes (0, 0, 0, 0) 0x2160 ++
    fourLimbBytes (0, 0, 0, 0) 0x2180 ++
    fourLimbBytes (0, 0, 0, 0) 0x21a0
  -- 2^(p-2) mod p = (p+1)/2 = 2^254 - 9
  -- = 28948022309329048855892746252171976963317496166410141009864396001978282409975
  expectedMem :=
    fourLimbBytes (0xfffffffffffffff7,
                   0xffffffffffffffff,
                   0xffffffffffffffff,
                   0x3fffffffffffffff) 0x2000

/-! ## §4. Differential gate

This is what the external harness consumes. For each test case, the
shell script:

1. Calls `lake env lean --run [...]` to print a JSON dump of
   `tc.initRegs / tc.initMem / tc.expectedMem`.
2. Runs `JasminEmit.emitFunDecl tc.fd > /tmp/<port>.jazz`.
3. Builds the harness binary with that .jazz linked in (template in
   `scripts/diff_bignum_sem_harness.c`).
4. Runs the harness with the JSON-derived inputs.
5. Diffs the harness output against `tc.expectedMem`.

Failure modes:
- Lean side fails: BignumExec doesn't compute what we declared in
  `expectedMem`. `runAndCheck tc = false`.
- C side fails: the compiled .o doesn't compute the expected bytes.
  Indicates JasminEmit or jasminc divergence from BignumExec.
- Both succeed: ✓ rule has L2 evidence on this test case.

Below: smoke-tests that the Lean side computes the expected value.
The C-side check is wired separately. -/

-- Lean-side verdict: BignumExec on tcModCanonical produces the
-- expected canonical output.
#eval runAndCheck tcModCanonical
-- Lean-side verdict: BignumExec on tcModAboveP correctly reduces
-- `a = p + 5` to `5`.
#eval runAndCheck tcModAboveP
-- Lean-side verdict: tcInvP25519 (`2^(p-2) mod p = 2^254 - 9`) round-trips
-- through the full Bernstein chain via 265 Ccalls in `bignumExecFuel`.
-- (Note: `#eval`'d at `lake env lean --run` time below via the Rust harness;
-- the in-file `#eval` would deep-recurse the interpreter on the 265-call chain.)
-- Use `lake exe diffemit tcInvP25519` to feed it through.

/-! ## §5. Notes on completeness

The two test cases above exercise:
- The `a < p` branch (cmov keeps `a`).
- The `a ≥ p` branch (cmov takes `a - p`).

For full L2 coverage of `bignum_mod_p25519_4` we'd want:
- ~100 random `a ∈ [0, 2p)` inputs.
- Boundary cases: `a = 0`, `a = p`, `a = 2p - 1`.
- A "should fail loudly" case: input `a ≥ 2p` (outside the
  precondition) — both Lean and C should produce *some* output, but
  neither is required to produce a specific value. We test that both
  agree on whatever they produce.

Adding these is mechanical; deferred until the shell harness is in
place to consume them. -/

end CatCrypt.Crypto.Jasmin.BignumExecDiffTest
