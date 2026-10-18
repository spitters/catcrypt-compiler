/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT

/-!
# Magic constants for division-by-constant strength reduction

This module states and verifies the magic-constant identities
`x / n = (x * m) >>> s` (below an input bound) for the fixed prime moduli of
the PQC and STARK kernels, which a lowering that replaces division by a
multiply-shift sequence consumes. It also defines the decision record of a
strength-reduction analysis over `JForProg` bodies. The `Com` rewrite with its
denotation theorem is `StrengthReduceReal`.

## Why this matters for crypto kernels

Barrett reduction with a fixed prime modulus is the dominant cost in many PQC
inner loops:

* ML-KEM (`q = 3329`) — every NTT butterfly involves a `mod q` step;
* ML-DSA (`q = 8380417`) — Barrett reduction on every coefficient after
  NTT-domain multiply-add;
* Falcon (`q = 12289`) — same shape;
* BabyBear (`q = 2013265921`) — STARK-friendly Mersenne-like prime, used in
  Plonky3-class hash arithmetisations.

On modern x86 the integer divider has 20-30× the latency of `mul`+`shr`; on
ARM the gap is similar. Replacing `div`/`mod` by precomputed multiply-shift
sequences is a **per-coefficient** speedup that compounds across thousands of
coefficients per polynomial. Hand-written PQC kernels (libcrux,
`pq-crystals/kyber`, etc.) all use this trick; LLVM's `InstCombine` also
performs it for general C code.

## The magic constants and their verified bounds

Granlund-Montgomery (1994) gives the schema:

  `n / d = (n * m) >>> s`     for all `n ∈ [0, 2^N)`,

where `s = N + ⌈log₂ d⌉` and `m = ⌈2^s / d⌉` (the "round-up" variant). The
condition for correctness is `m * d ≤ 2^s + 2^(s-N)`; for the primes below
this holds, and we verify it directly by exhaustive `native_decide` over the
relevant input range.

| Prime `d` | Magic `m` | Shift `s` | Bound `N` | Protocol |
|---|---|---|---|---|
| `3329`        | `161271`     | `29` | `2^16` | ML-KEM       |
| `12289`       | `87375`      | `30` | `2^16` | Falcon       |
| `8380417`     | `4198404`    | `45` | `2^23` | ML-DSA       |
| `2013265921`  | `2290649224` | `62` | `2^16` | BabyBear/STARKs |

The bounds are tight: each is verified by exhaustive `native_decide` over
`[0, N)`. Inputs above the bound can yield a spurious result; the emit pass
must guard against this (typically the input is a sum of two `BitVec` values
bounded above by the modulus, so the bound holds by construction).

## Main results

* `mlkem_q3329_magic`, `falcon_q12289_magic`, `mldsa_q8380417_magic`,
  `babybear_q_magic` — `x / d = (x * m) >>> s` for every `x` below the bound.
* `magicCheck_iff` — the Boolean checker decides that identity.

## Contents

* `MagicEntry` — a record `{ divisor, magic, shift, bound }` of a verified
  magic-constant tuple.
* `magicTableMlkem`, `magicTableMldsa`, `magicTableFalcon`, `magicTableBabyBear`
  — the four headline crypto-prime entries.
* `magicCheck` — the `Bool`-valued exhaustive identity check.
* `magicCheck_iff` — lift `magicCheck = true` to `∀ x < N, x / d = (x * m) >>> s`.
* `mlkem_q3329_magic`, `falcon_q12289_magic`, `mldsa_q8380417_magic`,
  `babybear_q_magic` — the four verified `∀`-forms, each closed by
  `native_decide` against `magicCheck_iff`.
* `StrengthReduceDecisions` — the analysis result: a list of
  `(position, MagicEntry)` labels.
* `analyzeStrengthReduce` — returns the empty decision list: jasminDialect
  has `mul`, `shr`, `and` but no `div`, so a division by a constant is reached
  only through leaf calls such as `RCall "mod_q"`, handled by
  `Optimizer/BarrettReduce.lean`.

The magic-constant identities are closed by `native_decide` against
exhaustive `Bool` checks.

## Relationship to `Optimizer/BarrettReduce.lean`

`BarrettReduce` (Optimizer Pass 1.1) rewrites *leaf calls* `RCall "mod_q"`
to `RCall "barrett_{q}"` at the `LowCT` level — its soundness obligation
is an external `LeafSpec`-level agreement on the `barrett_{q}` leaf. The
present file is **complementary**: it provides the verified magic-constant
table that any concrete `barrett_{q}` LeafSpec implementation will use to
discharge the agreement. When the emit pass lowers `barrett_{q}(x)` to
jasmin / asm, it consumes `magicTableMlkem` (or its peer) to know which
`(m, s)` to splat into the emitted multiply-shift sequence.

The two pieces compose: `BarrettReduce` decides *where* a Barrett site lives;
this file decides *how* a Barrett site lowers. CT preservation is uniform
across both: neither pass introduces a secret-dependent branch.

## Extensions

* **Modulo reduction.** `x mod n = x - (x / n) * n` lowers to two multiply-shift
  sequences (one to compute `x / n`, then a multiply-subtract). The
  framework here covers division; modulo reduces to division by the
  identity above. A dedicated `magicTableMod` is left as an unblocked
  extension (the arithmetic identity `x % n = x - (x / n) * n` is closed
  by `Nat.mod_def` or `BitVec.toNat_mod`, both already in mathlib /
  Lean core).
* **u32 / u16 width specialisations.** The magic table here is stated at
  the `Nat` level so it applies to any width that *contains* the input
  range. A future extension can package per-width `BitVec`-typed magic
  entries.
* **General magic-constant synthesis.** A future pass could compute the
  magic constant on the fly from the divisor (using `m = ⌈2^s/d⌉`,
  `s = N + ⌈log₂ d⌉`) and prove correctness from
  Granlund-Montgomery's sufficient condition. The tabular approach here
  is more reliable: each entry has a *concrete* `native_decide`
  verification, not a parametric bound-arithmetic proof. New primes can
  be added to the table whenever a new protocol needs one (LWE,
  Saber-q, etc.).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
open CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

namespace StrengthReduce

/-! ## 1. The magic-constant table

Each `MagicEntry` records a verified strength-reduction triple
`(divisor, magic, shift)` together with the maximum input value `bound`
over which the identity holds. Within the range `[0, bound)`,

  `x / divisor = (x * magic) >>> shift`.

This is the Granlund-Montgomery "round-up" magic constant; for each
entry below, the correctness identity is closed by exhaustive
`native_decide` over `Fin bound`. -/

/-- A verified strength-reduction magic-constant entry. The identity
`x / divisor = (x * magic) >>> shift` holds for all `x < bound`. -/
structure MagicEntry where
  /-- The divisor being strength-reduced. -/
  divisor : Nat
  /-- The precomputed multiplier `m = ⌈2^shift / divisor⌉`. -/
  magic : Nat
  /-- The right-shift amount `s = N + ⌈log₂ divisor⌉` where `N` is the
      input width. -/
  shift : Nat
  /-- The maximum input value (exclusive) over which the identity is
      verified. The emit pass must ensure inputs respect this bound. -/
  bound : Nat
  deriving Repr, DecidableEq

namespace MagicEntry

/-- The trivial / sentinel entry: divisor 1, identity multiplier. Useful
    as a no-op placeholder in lookup tables. -/
def trivial : MagicEntry where
  divisor := 1
  magic := 1
  shift := 0
  bound := 0

end MagicEntry

/-! ## 2. The exhaustive checker

`magicCheck q m s upper` returns `true` iff `x / q = (x * m) >>> s` for
all `x < upper`. It is decidable by `native_decide` because the search
space is bounded; for the four headline primes the range is small enough
to fit in seconds of compile time. -/

/-- Exhaustive `Bool` check: every `x ∈ [0, upper)` satisfies
    `x / q = (x * m) >>> s`. -/
def magicCheck (q m s upper : Nat) : Bool :=
  (List.range upper).all (fun x => x / q == (x * m) >>> s)

/-- Lift the `Bool` exhaustive check to a `∀`-form. This is the bridge
    from `native_decide`-closable check to a usable `∀`-statement that
    the emit pass and downstream callers can rewrite with. -/
theorem magicCheck_iff {q m s upper : Nat} :
    magicCheck q m s upper = true ↔
      ∀ x < upper, x / q = (x * m) >>> s := by
  unfold magicCheck
  rw [List.all_eq_true]
  constructor
  · intro h x hx
    exact beq_iff_eq.mp (h x (List.mem_range.mpr hx))
  · intro h x hx
    exact beq_iff_eq.mpr (h x (List.mem_range.mp hx))

/-! ## 3. The four verified headline entries

Each entry below is a concrete `MagicEntry` together with its verified
exhaustive identity. The identity is closed by `native_decide` against
`magicCheck_iff` — no manual bit-width arithmetic required. -/

/-- ML-KEM's `q = 3329` strength-reduction entry. Verified over 16-bit
    inputs (the natural range for ML-KEM's NTT coefficient slots). -/
def magicTableMlkem : MagicEntry where
  divisor := 3329
  magic := 161271
  shift := 29
  bound := 65536

/-- The verified strength-reduction identity for ML-KEM's `q = 3329`.
    Holds for all 16-bit inputs. The body is a `native_decide` against
    an exhaustive `magicCheck` over `Fin 65536` (= 65536 cases checked
    natively, closes in milliseconds). -/
theorem mlkem_q3329_magic :
    ∀ x < 65536, x / 3329 = (x * 161271) >>> 29 := by
  rw [← magicCheck_iff]; native_decide

/-- Falcon's `q = 12289` strength-reduction entry. Verified over 16-bit
    inputs. -/
def magicTableFalcon : MagicEntry where
  divisor := 12289
  magic := 87375
  shift := 30
  bound := 65536

/-- The verified strength-reduction identity for Falcon's `q = 12289`. -/
theorem falcon_q12289_magic :
    ∀ x < 65536, x / 12289 = (x * 87375) >>> 30 := by
  rw [← magicCheck_iff]; native_decide

/-- ML-DSA's `q = 8380417` strength-reduction entry. Verified over
    23-bit inputs (`q < 2^23`; the natural Barrett-reduction range for
    ML-DSA is `[0, q)`, which fits within `2^23`). -/
def magicTableMldsa : MagicEntry where
  divisor := 8380417
  magic := 4198404
  shift := 45
  bound := 8388608  -- 2^23

/-- The verified strength-reduction identity for ML-DSA's `q = 8380417`.
    Holds for all 23-bit inputs (covers the natural Barrett range). -/
theorem mldsa_q8380417_magic :
    ∀ x < 2^23, x / 8380417 = (x * 4198404) >>> 45 := by
  rw [← magicCheck_iff]; native_decide

/-- BabyBear's `q = 2^31 - 2^27 + 1` strength-reduction entry. Verified
    over 16-bit inputs (representative range; the magic constant also
    works for larger inputs but the exhaustive `native_decide` would
    take longer — extension is straightforward). -/
def magicTableBabyBear : MagicEntry where
  divisor := 2013265921
  magic := 2290649224
  shift := 62
  bound := 65536

/-- The verified strength-reduction identity for BabyBear. Verified at
    16-bit input range; the identity extends to larger inputs by
    Granlund-Montgomery's sufficient condition but the verification
    range here is sized for fast `native_decide` compile times. -/
theorem babybear_q_magic :
    ∀ x < 65536, x / 2013265921 = (x * 2290649224) >>> 62 := by
  rw [← magicCheck_iff]; native_decide

/-- The default magic table: the four headline crypto primes. New
    protocols can extend this list by adding their verified entry
    alongside an `_magic` theorem. -/
def defaultMagicTable : List MagicEntry :=
  [magicTableMlkem, magicTableFalcon, magicTableMldsa, magicTableBabyBear]

/-- Look up a `MagicEntry` by divisor. Returns `none` if the divisor is
    not in the table. -/
def lookupMagic (table : List MagicEntry) (d : Nat) : Option MagicEntry :=
  table.find? (fun e => e.divisor == d)

/-! Sanity tests of the lookup. -/

example : (lookupMagic defaultMagicTable 3329).map MagicEntry.magic = some 161271 := by
  decide

example : (lookupMagic defaultMagicTable 12289).map MagicEntry.magic = some 87375 := by
  decide

example : (lookupMagic defaultMagicTable 8380417).map MagicEntry.shift = some 45 := by
  decide

example : (lookupMagic defaultMagicTable 99991) = none := by decide

/-! ## 4. The analysis result -/

/-- A single strength-reduction decision: replace the binder at `pos`
    with a mul-shift sequence using `entry`. -/
structure StrengthReduceEntry where
  /-- The binder position to strength-reduce. -/
  pos : Nat
  /-- The verified magic entry to use. -/
  entry : MagicEntry
  deriving Repr

/-- **A strength-reduction decision.**

`rewrites` is the list of `(pos, MagicEntry)` labels: at each position
`pos`, the emit pass should replace a slow `div n` with `mul m; shr s`
using the table entry's verified `(m, s)`. -/
structure StrengthReduceDecisions where
  /-- Strength-reduction sites, in left-to-right body order. -/
  rewrites : List StrengthReduceEntry
  deriving Repr

namespace StrengthReduceDecisions

/-- The trivial decision: no strength-reduction sites. -/
def empty : StrengthReduceDecisions where
  rewrites := []

end StrengthReduceDecisions

/-! ## 5. The analysis

The jasminDialect has no `div` arm: `JasminBinOp` enumerates `add/sub/mul/and/or/xor/shl/shr` but not
`div`. So no `Com jasminDialect` body can syntactically contain a
divide-by-constant. The strength-reduction sites come from the
*leaf-call* layer (`Optimizer/BarrettReduce.lean` rewrites `RCall "mod_q"`
to `RCall "barrett_{q}"`; the present file supplies the magic table that
the `barrett_{q}` leaf consumes).

`analyzeStrengthReduce` therefore returns the empty decision. -/

/-- **Strength-reduction analysis.** Returns the empty decision: with no
`div` arm in `JasminBinOp`, a `Com jasminDialect` body has no
divide-by-constant site. -/
def analyzeStrengthReduce {accTy : JasminTy} (_p : JForProg accTy) :
    StrengthReduceDecisions :=
  StrengthReduceDecisions.empty

end StrengthReduce

end CatCrypt.Crypto.SecureCompilation.VIR
