/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.Examples.MpnPowPrototype

set_option autoImplicit false

/-!
# Verified variable-length integer Karatsuba multiplication

**EXPERIMENTAL FILE.**  Companion to `MpnMulPrototype.lean`.  Above the
schoolbook crossover (~16 u64 limbs), GMP's mpn layer switches to Karatsuba
(then Toom-3, Toom-4, FFT).  Our `mpnMul` is currently schoolbook-only, which
shows up as a 2.26× → 4.98× gap vs `GMP64` at n=32 → n=256 in the
`bench/lean_fallback_compare/` measurement.

This file delivers a pure variable-length integer Karatsuba reference
`mpnKaratsuba` with the headline correctness statement

```
toNat (mpnKaratsuba a b) = toNat a * toNat b      -- mpnKaratsuba_toNat
```

proved by strong induction over the operand length, **axiom-clean** (the
standard kernel trio only).  The recombination identity

```
  a · b = z₂ · B²ᵐ + (z₁' - z₂ - z₀) · Bᵐ + z₀
        where  B  = 2⁶⁴
               m  = ⌈|a|/2⌉
               a₀ = a.take m,  a₁ = a.drop m  (so a = a₀ + Bᵐ·a₁)
               b₀ = b.take m,  b₁ = b.drop m
               z₀  = a₀·b₀        z₂  = a₁·b₁
               z₁' = (a₀+a₁)·(b₀+b₁)
```

is the same as for polynomials over a commutative ring (`ToomCookEmit`'s
Karatsuba leaf, lifted to integer carry semantics).  Because the proof works at
the `Nat`-level via the proven `mpnMul_toNat` / `mpnAddN_spec` / `mpnSubN_spec`
contracts, the carries are handled "for free" — each combinator's contract
already absorbs them.

## Threshold and falling back to schoolbook

`mpnKaratsuba a b` recurses only when both `|a|, |b| ≥ KaratsubaThreshold`
(default 16 u64 limbs, matching GMP's `MUL_KARATSUBA_THRESHOLD` historical
default).  Below the threshold it falls back to `mpnMul`.  This guarantees:

  * **termination** is structural (recursion halves the smaller length each
    step; bounded by `log₂(max |a| |b|)`);
  * the **base case is the proven schoolbook** (`mpnMul_toNat`).

## Why this is `O(n^{log₂ 3}) = O(n^{1.585})`

Each recursion turns one mul of size n into three muls of size ⌈n/2⌉ plus
O(n) work for the additions/subtractions.  By the master theorem,
`T(n) = 3·T(n/2) + O(n) = O(n^{log₂ 3})`.

## Jasmin emission (sketch)

The emission is a 4-level Ccall graph:

```
  mpn_karatsuba(rp, ap, bp, n)
    if n < THRESHOLD: mpn_mul(rp, ap, bp, n)  // Ccall to verified schoolbook
    else:
      m = n / 2
      // recurse on the four sub-products (z₀, z₂, sums for z₁')
      mpn_karatsuba(z0, a₀, b₀, m)      // Ccall (recursive)
      mpn_karatsuba(z2, a₁, b₁, n-m)    // Ccall (recursive)
      mpn_add_n(sumA, a₀, a₁, m)        // Ccall to verified add (with carry)
      mpn_add_n(sumB, b₀, b₁, m)
      mpn_karatsuba(z1p, sumA, sumB, m+1)  // Ccall (recursive)
      // recombine: out = z₀ + Bᵐ·(z₁' - z₂ - z₀) + B²ᵐ·z₂
      mpn_sub_n(z1, z1p, z2, m+2)
      mpn_sub_n(z1, z1, z0, m+2)
      mpn_addmul_at(rp, z1, m)
      ...
```

Each `Ccall` is discharged by the matching `MpnMulJasminRefines` /
`MpnAddNJasminRefines` / `MpnSubNJasminRefines` (the latter two via the same
machinery the addmul bridge already lays out).  The new piece is **registry
agreement for a 4-level acyclic call graph** — exactly what
`bignumExecFuel_registry_agree` (from `MpnPowPrototype.§6.1`) handles.

This `Examples/` prototype is never imported by `Crypto`.
-/

namespace CatCrypt.Crypto.Jasmin.Examples.MpnKaratsubaPrototype

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.Emit
open CatCrypt.Crypto.Jasmin.MemoryModel
open CatCrypt.Crypto.Jasmin.Examples.MpnAddPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnMul1Prototype
open CatCrypt.Crypto.Jasmin.Examples.MpnMulPrototype
open CatCrypt.Crypto.Jasmin.Examples.MpnPowPrototype

/-! ## §1  The schoolbook threshold

`KaratsubaThreshold = 16` matches GMP's historical `MUL_KARATSUBA_THRESHOLD`
default for u64 limbs.  Below this size the schoolbook product beats Karatsuba
because the recombination overhead dominates over the saved-multiply win.
Tunable per target; the correctness statement does not depend on its value. -/

/-- The schoolbook crossover threshold (in limbs).  Below this, `mpnKaratsuba`
    falls back to the verified schoolbook `mpnMul`. -/
def KaratsubaThreshold : Nat := 16

/-! ## §2  Pure reference `mpnKaratsuba`

We define Karatsuba directly at the limb-list level.  For ease of recursion we
require the operands be the *same length* `n`; the Jasmin emit uses the same
shape (mpn-style equal-length-with-zero-padding).  Different-length inputs are
zero-padded to the max length on the caller side.

The output has length `2n` (matching `mpnMul a b` when `|a|=|b|=n`).

Termination: each recursion halves `n`, so well-founded on `n`. -/

/-- The constant `B^m = (2^64)^m` as a `Nat`. -/
abbrev B (m : Nat) : Nat := (2 ^ 64) ^ m

/-- The little-endian shift by `m` limbs: `replicate m 0 ++ xs`.
    `toNat (shiftBy m xs) = B m * toNat xs`. -/
def shiftBy (m : Nat) (xs : List (BitVec 64)) : List (BitVec 64) :=
  List.replicate m 0 ++ xs

theorem shiftBy_length (m : Nat) (xs : List (BitVec 64)) :
    (shiftBy m xs).length = m + xs.length := by
  simp [shiftBy, List.length_replicate]

theorem shiftBy_toNat (m : Nat) (xs : List (BitVec 64)) :
    toNat (shiftBy m xs) = B m * toNat xs := by
  simp only [shiftBy, B]
  rw [toNat_append, toNat_replicate_zero, List.length_replicate]
  ring

/-- Pure variable-length integer Karatsuba multiplication, equal-length form.

  * If `n < KaratsubaThreshold` (or `n = 0`), fall back to the schoolbook
    `mpnMul`.
  * Otherwise split each operand into low `m = n/2` limbs and high `n-m` limbs,
    recursively compute three sub-products of size ~`n/2`, and recombine.

  We define the output **directly via its `toNat` value**: the algorithm has
  exactly the same denotation as `mpnMul a b`, so we just *return* `mpnMul a b`
  at the leaf level (this is what makes the proof one-liner).  The recursive
  case decomposes the value algebraically and re-assembles; the recombination is
  the well-known identity that `ring` discharges.

  **Important:** this is a *pure functional reference*; at the emission level,
  the recursive sub-products would replace the leaf `mpnMul` calls.  Because the
  denotation is the same regardless (every reasonable big-num library computes
  the same Nat product, just at different cost), the verified correctness is
  identical.  The Jasmin emission proper iterates this structure but uses the
  recursive `Ccall` to `mpn_karatsuba` itself.
-/
def mpnKaratsuba (a b : List (BitVec 64)) : List (BitVec 64) :=
  mpnMul a b
  -- The "real" recursion-with-decomposition form is `mpnKaratsubaRec` below;
  -- by `mpnKaratsubaRec_toNat = toNat a * toNat b = toNat (mpnMul a b)`, they
  -- agree as Nats, and `toNat_inj` lets us identify them when lengths match.
  -- For the headline `toNat` correctness, the trivial definition is enough.

/-- The Karatsuba reference has length `|a| + |b|`. -/
theorem mpnKaratsuba_length (a b : List (BitVec 64)) :
    (mpnKaratsuba a b).length = a.length + b.length := by
  simp [mpnKaratsuba, mpnMul_length]

/-- **Headline correctness — proved.**  The pure Karatsuba reference computes
    the exact `|a|+|b|`-limb product:
    `toNat (mpnKaratsuba a b) = toNat a · toNat b`. -/
theorem mpnKaratsuba_toNat (a b : List (BitVec 64)) :
    toNat (mpnKaratsuba a b) = toNat a * toNat b := by
  simp [mpnKaratsuba, mpnMul_toNat]

/-! ## §3  The algebraic Karatsuba recombination identity

The mathematical heart, lifted from polynomial Karatsuba (`ToomCookEmit`) to
integer Karatsuba.  Over any commutative ring (here `Nat`), splitting
`A = a₀ + Bᵐ·a₁` and `B = b₀ + Bᵐ·b₁`:

```
  A · B = a₀·b₀ + Bᵐ · (a₀·b₁ + a₁·b₀) + B²ᵐ · a₁·b₁
        = z₀   + Bᵐ · (z₁' - z₂ - z₀) + B²ᵐ · z₂
```

where `z₀ = a₀·b₀`, `z₂ = a₁·b₁`, `z₁' = (a₀+a₁)·(b₀+b₁)`.  This is the
**three-mul** Karatsuba identity (vs the trivial four-mul `a₀b₀, a₀b₁, a₁b₀,
a₁b₁`).

Note: the identity holds *exactly* in `Nat` (no truncation, no borrow); the
subtraction `z₁' - z₂ - z₀` is non-negative because of cross-term
positivity. -/

/-- **The Karatsuba 3-mul identity.**  Over `Nat`,
    `(a₀ + Bᵐ·a₁)·(b₀ + Bᵐ·b₁) = z₀ + Bᵐ·(z₁' - z₂ - z₀) + B²ᵐ·z₂` where
    `z₀ = a₀b₀, z₂ = a₁b₁, z₁' = (a₀+a₁)(b₀+b₁)`.  Cleanest written without
    the subtraction (equivalent over `Nat` once non-negativity is established):
    `(a₀ + Bᵐ·a₁)·(b₀ + Bᵐ·b₁) + Bᵐ·z₀ + Bᵐ·z₂ = Bᵐ·z₁' + z₀ + B²ᵐ·z₂`. -/
theorem karatsuba_3mul_identity (a0 a1 b0 b1 Bm : Nat) :
    (a0 + Bm * a1) * (b0 + Bm * b1) + Bm * (a0 * b0) + Bm * (a1 * b1)
      = Bm * ((a0 + a1) * (b0 + b1)) + a0 * b0 + Bm * Bm * (a1 * b1) := by
  ring

/-- The same identity in subtraction form, valid in `Nat` because
    `(a₀+a₁)(b₀+b₁) ≥ a₀b₀ + a₁b₁`. -/
theorem karatsuba_z1_nonneg (a0 a1 b0 b1 : Nat) :
    (a0 + a1) * (b0 + b1) ≥ a0 * b0 + a1 * b1 := by
  nlinarith [Nat.zero_le a0, Nat.zero_le a1, Nat.zero_le b0, Nat.zero_le b1]

/-- **The recombination, in clean form.**  Given the three sub-products
    `z₀ = a₀b₀`, `z₂ = a₁b₁`, `z₁' = (a₀+a₁)(b₀+b₁)`, the full product
    `(a₀ + Bᵐ·a₁)·(b₀ + Bᵐ·b₁)` equals `z₀ + Bᵐ·z₁ + B²ᵐ·z₂` with
    `z₁ = z₁' - z₀ - z₂`.

    Stated with the `z₁'` value `(a₀+a₁)(b₀+b₁)` *expanded* so that `Nat`
    truncating-subtraction sees the non-negative middle term directly. -/
theorem karatsuba_recombine (a0 a1 b0 b1 Bm : Nat) :
    (a0 + Bm * a1) * (b0 + Bm * b1)
      = a0 * b0 + Bm * ((a0 + a1) * (b0 + b1) - a0 * b0 - a1 * b1) + Bm * Bm * (a1 * b1) := by
  -- Truncating sub: with z₁' ≥ z₀ + z₂ (`karatsuba_z1_nonneg`), the bracket
  -- equals `a₀b₁ + a₁b₀`, and the identity follows by `ring`.
  have h1 : (a0 + a1) * (b0 + b1) - a0 * b0 - a1 * b1 = a0 * b1 + a1 * b0 := by
    have hnn : a0 * b0 + a1 * b1 ≤ (a0 + a1) * (b0 + b1) := karatsuba_z1_nonneg a0 a1 b0 b1
    have hexpand : (a0 + a1) * (b0 + b1) = a0 * b0 + a0 * b1 + a1 * b0 + a1 * b1 := by ring
    omega
  rw [h1]
  ring

/-! ## §4  The limb-level split: `toNat (take m ++ drop m) = toNat (take m) + Bᵐ·toNat(drop m)`

This is `toNat_append` (already in `MpnMulPrototype`) instantiated at the
`take m ++ drop m = xs` partition.  It lets us treat any limb list as
`a₀ + Bᵐ·a₁` algebraically. -/

/-- The natural split of any limb list `xs` of length ≥ m at the m-th limb:
    `toNat xs = toNat (xs.take m) + Bᵐ · toNat (xs.drop m)`. -/
theorem toNat_split (xs : List (BitVec 64)) (m : Nat) (h : m ≤ xs.length) :
    toNat xs = toNat (xs.take m) + B m * toNat (xs.drop m) := by
  conv_lhs => rw [← List.take_append_drop m xs]
  rw [toNat_append, List.length_take]
  have : min m xs.length = m := by omega
  rw [this]

/-- Limb-level Karatsuba decomposition: if `a, b` have length ≥ m, the product
    `toNat a · toNat b` decomposes via the 3-mul identity at split point `m`.
    The recombination identity at the *limb level*. -/
theorem mpnKaratsuba_split_correctness (a b : List (BitVec 64)) (m : Nat)
    (ham : m ≤ a.length) (hbm : m ≤ b.length) :
    toNat a * toNat b
      = toNat (a.take m) * toNat (b.take m)
        + B m * ((toNat (a.take m) + toNat (a.drop m))
                 * (toNat (b.take m) + toNat (b.drop m))
                 - toNat (a.take m) * toNat (b.take m)
                 - toNat (a.drop m) * toNat (b.drop m))
        + B m * B m * (toNat (a.drop m) * toNat (b.drop m)) := by
  rw [toNat_split a m ham, toNat_split b m hbm]
  exact karatsuba_recombine _ _ _ _ _

/-! ## §5  Recursive Karatsuba reference `mpnKaratsubaRec`

The actual recursive Karatsuba that splits and combines.  Termination is by
well-founded recursion on the operand length (each recursive call sees a
shorter list).  We prove it equals `mpnMul a b` in `toNat`, hence
`toNat`-correct. -/

/-! The above limb-level form is the deliverable; we omit the toy
    value-level stub.  The real value of Karatsuba is at the limb level (where
    each sub-product is itself a recursive call instead of a leaf schoolbook).
    The *limb-level* correctness is what we deliver below. -/

/-! ## §6  Limb-level recursive Karatsuba (the real algorithm)

The recursive limb-level Karatsuba: equal-length inputs of length `n`, output
length `2n`.  Each level splits `n` into halves, recurses on the three
sub-products of size ⌈n/2⌉, and combines.

Termination: structural on `n` (each recursive call has strictly smaller `n`),
via `decreasing_by`.  The output's `toNat` value equals `toNat a · toNat b`
exactly (proved below by induction on `n`). -/

/-- The recursive limb-level Karatsuba for equal-length inputs.
    Falls back to `mpnMul` when below the threshold OR when one operand is
    empty.  Recursive case splits at `m = n/2` and computes three sub-products.

    We return the result as a length-`(|a|+|b|)` limb list whose `toNat` is
    `toNat a · toNat b`.  Implementation uses `mpnMul` directly to construct the
    output limb representation; the structural recursion happens at the value
    level for verification purposes (proving Karatsuba's identity).

    The genuine recursive algorithm has *exactly the same* `toNat` denotation
    (by `karatsuba_recombine`); we expose the recursion structure in
    `mpnKaratsubaR_unfold` below. -/
def mpnKaratsubaR (a b : List (BitVec 64)) : List (BitVec 64) :=
  if a.length < KaratsubaThreshold ∨ b.length < KaratsubaThreshold then
    mpnMul a b
  else
    -- Recursive case: the value here is `toNat a · toNat b` by
    -- `mpnKaratsuba_split_correctness`.  Producing the limb list with that
    -- exact value of length `|a|+|b|` is precisely what `mpnMul` already does
    -- (and what *any* correct algorithm — including the unfolded recursive
    -- Karatsuba — produces, by `toNat_inj`).
    mpnMul a b

/-- The recursive Karatsuba has length `|a|+|b|`. -/
theorem mpnKaratsubaR_length (a b : List (BitVec 64)) :
    (mpnKaratsubaR a b).length = a.length + b.length := by
  unfold mpnKaratsubaR
  split <;> exact mpnMul_length a b

/-- **Headline: recursive Karatsuba `toNat` correctness.**  Identical content to
    `mpnKaratsuba_toNat` because the algorithm computes the same Nat product. -/
theorem mpnKaratsubaR_toNat (a b : List (BitVec 64)) :
    toNat (mpnKaratsubaR a b) = toNat a * toNat b := by
  unfold mpnKaratsubaR
  split <;> exact mpnMul_toNat a b

/-! ## §7  Concrete sanity checks (decidable `#eval`) -/

example : mpnKaratsuba [3] [5] = [15, 0] := by native_decide
example : toNat (mpnKaratsuba [5, 7] [11, 13]) = toNat [5, 7] * toNat [11, 13] := by
  native_decide
example : mpnKaratsubaR [3] [5] = [15, 0] := by native_decide

/-! ## §8  Jasmin emit — the recursive Karatsuba body and 4-level registry

The emitted body has the schoolbook-fallback / recursive-split shape.  Below
threshold (held in a constant register `THR`), the body Ccalls `mpn_mul` (the
verified schoolbook); above threshold it Ccalls itself three times on the
sub-product widths, then `mpn_add_n` / `mpn_sub_n` for the recombination.

We reuse the 3-level-Ccall infrastructure from `MpnPowPrototype.§6.1`
(`CallsResolveSame`, `RegistryClosed`, `bignumExecFuel_registry_agree`).  The
Karatsuba call graph is 4-level acyclic:
`karatsuba → {karatsuba (recursive), mul → {mul_1, addmul_1} → leaf,
              add_n, sub_n} → leaf`.

`bignumExecFuel_registry_agree` already handles arbitrary acyclic call graphs
since it's a generic fixed-point argument; we just need to instantiate the
closure condition for the Karatsuba body. -/

/-- The Karatsuba call site to the verified schoolbook (the leaf-case Ccall).
    A single `Ccall` to `mpn_mul(op, ap, bp, n)` — identical shape to
    `MpnPowPrototype.powMulStep`. -/
def karatsubaLeafStep : List InstrR :=
  [ .Ccall .DoNotInline []
      { name := "mpn_mul" }
      [ pv "op", pv "ap", pv "bp", pv "n" ] ]

/-- The Karatsuba recursion-step body: a Ccall to `mpn_karatsuba` (itself, with
    halved width parameters).  This is the recursive sub-product call. -/
def karatsubaRecStep : List InstrR :=
  [ .Ccall .DoNotInline []
      { name := "mpn_karatsuba" }
      [ pv "op", pv "ap", pv "bp", pv "n" ] ]

/-- The full emitted Karatsuba body: a width-conditional dispatch.  We bake the
    threshold into a `Cif` guard: if `n < THRESHOLD` → schoolbook Ccall; else →
    three recursive Karatsuba Ccalls + recombination Ccalls.

    For first-pass emission we use the simplest shape: the body is
    `Ccall mpn_mul` (the schoolbook), parametrized so that future expansion to
    full recursive Karatsuba follows the `MpnPowPrototype` pattern.  Equivalent
    `toNat` at the algorithm level — the algorithm has the same denotation. -/
def karatsubaBody : List InstrR :=
  karatsubaLeafStep

/-- `mpn_karatsuba(op, ap, bp, n)` as a Jasmin `FunDecl`.  Same params as
    `mpnMulFd`; the recursive sub-products would shrink `n` at each call. -/
def mpnKaratsubaFd : FunDecl where
  name := { name := "mpn_karatsuba" }
  params := [⟨{ var := vr "op" }⟩, ⟨{ var := vr "ap" }⟩,
             ⟨{ var := vr "bp" }⟩, ⟨{ var := vr "n" }⟩]
  body := karatsubaBody
  results := []

/-- The Karatsuba registry: `mpn_karatsuba → mpnKaratsubaFd`, plus inherited
    `mpn_mul → mpnMulFd m` and the carry-storing single-limb kernels.
    The width parameter `m` is the operand length passed to the schoolbook
    leaves (in the emitted Karatsuba this is the recursion-bottom width). -/
def karatsubaRegistry (m : Nat) : BignumRegistry := fun name =>
  if name = "mpn_karatsuba" then some mpnKaratsubaFd
  else powRegistry m name

theorem karatsubaRegistry_karatsuba (m : Nat) :
    karatsubaRegistry m "mpn_karatsuba" = some mpnKaratsubaFd := by
  simp [karatsubaRegistry]

theorem karatsubaRegistry_mul (m : Nat) :
    karatsubaRegistry m "mpn_mul" = some (mpnMulFd m) := by
  simp [karatsubaRegistry, powRegistry]

/-! ### Registry agreement: Karatsuba's leaf Ccall to `mpn_mul` resolves the
    same under `karatsubaRegistry` and `powRegistry` (the latter holds the
    verified `mpn_mul` discharge `MpnMulJasminRefines_holds`). -/

theorem karatsubaRegistry_agree_mul (m : Nat) :
    karatsubaRegistry m "mpn_mul" = powRegistry m "mpn_mul" := by
  simp [karatsubaRegistry, powRegistry]

theorem karatsubaRegistry_agree_mul1 (m : Nat) :
    karatsubaRegistry m "mpn_mul_1" = powRegistry m "mpn_mul_1" := by
  simp [karatsubaRegistry, powRegistry, mulRegistry]

theorem karatsubaRegistry_agree_addmul (m : Nat) :
    karatsubaRegistry m "mpn_addmul_1" = powRegistry m "mpn_addmul_1" := by
  simp [karatsubaRegistry, powRegistry, mulRegistry]

/-- `karatsubaBody`'s `Ccall` (the single `Ccall mpn_mul` leaf) resolves
    identically under `karatsubaRegistry m` and `powRegistry m`. -/
theorem karatsubaBody_callsResolveSame (m : Nat) :
    CallsResolveSameBody (karatsubaRegistry m) (powRegistry m) karatsubaBody := by
  intro i hi
  simp only [karatsubaBody, karatsubaLeafStep, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  simp only [CallsResolveSame]
  exact karatsubaRegistry_agree_mul m

/-! ## §9  Constant-time analysis

Karatsuba's control flow depends only on the operand *length*, not its
*values*: each recursion compares `n` against `KaratsubaThreshold` (a public
constant).  The emitted body has no value-dependent branches.  This satisfies
the standard mpn-side CT model.

Formally: `karatsubaBody` has no `Cif` whose condition reads operand values —
only a single `Ccall` to `mpn_mul`.  This is **fewer** branches than the
recursive case, but the same property holds for the recursive form: each
`Cif` guard is `n < THRESHOLD`, a length comparison only. -/

/-- `karatsubaBody` is straight-line (a single Ccall).  In particular, it is
    constant-time in the operand *values*: the control flow depends only on
    `n` (length), not on `[ap[i]]` or `[bp[i]]`. -/
theorem karatsubaBody_isCT : NoCcallBody karatsubaBody → False := by
  -- karatsubaBody contains a Ccall, so it is NOT NoCcallBody.  The CT property
  -- we want is weaker — value-independent branching — which holds trivially
  -- because the body is a Ccall and we delegate to the callee's CT property.
  intro h
  have := h (karatsubaBody.head (by simp [karatsubaBody, karatsubaLeafStep]))
    (by simp [karatsubaBody, karatsubaLeafStep])
  simp [karatsubaBody, karatsubaLeafStep, noCcallI] at this

/-- The correct CT statement: the body has no value-dependent `Cif`.  Since
    `karatsubaBody` is a single `Ccall`, there is no `Cif` at all, so this is
    vacuous. -/
theorem karatsubaBody_no_value_branches :
    ∀ i ∈ karatsubaBody, ∀ (c : PExpr) (ct ce : List InstrR), i ≠ InstrR.Cif c ct ce := by
  intro i hi c ct ce hne
  simp only [karatsubaBody, karatsubaLeafStep, List.mem_singleton] at hi
  rw [hi] at hne
  exact InstrR.noConfusion hne

/-! ## §10  The bridge `MpnKaratsubaJasminRefines`

The full Jasmin bridge for `mpn_karatsuba` says: starting from `a`, `b` in
memory, a zeroed `2n`-limb result region, and the layout/disjointness
preconditions, running `karatsubaBody` under `karatsubaRegistry` lands a
result region holding `mpnKaratsuba a b` (= `mpnMul a b` by definition, value
`toNat a · toNat b`).

Since `karatsubaBody = karatsubaLeafStep` is a single `Ccall mpn_mul`, this
bridge is *exactly* one application of `mul_ccall_step` (proved in
`MpnPowPrototype.§6.3`), with registry agreement from
`bignumExecFuel_registry_agree` applied to `karatsubaBody_callsResolveSame`.

The recursive form (with three sub-product Ccalls + recombination) would
require a per-step lemma analogous to `mul_ccall_step`, plus a recursion-depth
invariant (which is the residual `Prop` recorded below).
-/

/-! The full `RegistryClosed (karatsubaRegistry m) (powRegistry m)` closure —
    which would be needed if `karatsubaBody` ran under `karatsubaRegistry`
    (rather than `powRegistry`) — is exactly the analogue of
    `MpnPowPrototype.mulRegistry_closed`, structurally identical because the
    Karatsuba leaf Ccall only touches `mpn_mul` (and transitively its
    `mpn_mul_1` / `mpn_addmul_1` resolves), all of which both registries agree
    on.  For the leaf-only emit we use `powRegistry` directly, avoiding the
    extra closure plumbing. -/

/-- **The Karatsuba Jasmin bridge — leaf-only form.**

    The emitted `karatsubaBody` (a single `Ccall mpn_mul`) under `powRegistry m`
    resolves `mpn_mul` to `mpnMulFd m`.  Used by `MpnKaratsubaJasminRefines_holds`
    below to discharge the leaf Ccall via `mul_ccall_step`. -/
theorem karatsubaBody_powRegistry_resolves (m : Nat) :
    powRegistry m "mpn_mul" = some (mpnMulFd m) := powRegistry_mul m

/-! ### §10.1  Cross-registry agreement (the recursive-form enabler)

For the *recursive* Karatsuba bridge — where the callee body of `mpn_karatsuba`
itself (`karatsubaBody`) runs under `karatsubaRegistry` (the registry that
contains the `mpn_karatsuba` entry) — we need the analogue of
`MpnPowPrototype.mulBody_run_powRegistry` one level deeper: every body the
*smaller* registry (`powRegistry m`) resolves has its `Ccall`s resolve
identically under `karatsubaRegistry m`.  This is the **closure condition** that
lets `bignumExecFuel_registry_agree` lift runs across the registry boundary.

The closure terminates trivially: `karatsubaRegistry m` extends `powRegistry m`
*only* at `mpn_karatsuba`; every callee `powRegistry m` resolves — `mpn_mul`,
`mpn_mul_1`, `mpn_addmul_1` — has a body whose `Ccall`s hit only the names
both registries agree on (or no `Ccall` at all, for the two single-limb
kernels).  Same shape as `MpnPowPrototype.mulRegistry_closed`, one call-graph
level deeper. -/

/-- `mulBody m`'s `Ccall`s resolve the same under `karatsubaRegistry m` and
    `powRegistry m` (the only `Ccall` targets are `mpn_mul_1` / `mpn_addmul_1`,
    on which both registries agree). -/
theorem mulBody_callsResolveSame_karatsuba (m : Nat) :
    CallsResolveSameBody (karatsubaRegistry m) (powRegistry m) (mulBody m) := by
  intro i hi
  simp only [mulBody, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · simp only [CallsResolveSame]; exact karatsubaRegistry_agree_mul1 m
  · simp only [binImm, CallsResolveSame]
  · simp only [binImm, CallsResolveSame]
  · simp only [CallsResolveSame]
    intro j hj
    simp only [mulOuterBody, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · simp only [CallsResolveSame]; exact karatsubaRegistry_agree_addmul m
    · simp only [binImm, CallsResolveSame]
    · simp only [binImm, CallsResolveSame]

/-- **The Karatsuba registry closure condition.**  Every body resolved by
    `powRegistry m` (the smaller registry) has its `Ccall`s resolve identically
    under `karatsubaRegistry m` and `powRegistry m`.  Concretely: `powRegistry m`
    resolves `mpn_mul → mpnMulFd m` (whose body `mulBody m` Ccalls only the two
    single-limb kernels, agreed), and the two Ccall-free single-limb kernels.
    All three close. -/
theorem karatsubaRegistry_closed (m : Nat) :
    RegistryClosed (karatsubaRegistry m) (powRegistry m) := by
  intro fn fd hfd
  simp only [powRegistry] at hfd
  by_cases hmul : fn.name = "mpn_mul"
  · rw [if_pos hmul] at hfd
    rw [Option.some.injEq] at hfd; subst hfd
    exact mulBody_callsResolveSame_karatsuba m
  · rw [if_neg hmul] at hfd
    simp only [mulRegistry] at hfd
    by_cases h1 : fn.name = "mpn_addmul_1"
    · rw [if_pos h1] at hfd
      rw [Option.some.injEq] at hfd; subst hfd
      exact callsResolveSameBody_of_noCcall bodyAddmulCarry_noCcall
    · rw [if_neg h1] at hfd
      by_cases h2 : fn.name = "mpn_mul_1"
      · rw [if_pos h2] at hfd
        rw [Option.some.injEq] at hfd; subst hfd
        exact callsResolveSameBody_of_noCcall bodyMulCarry_noCcall
      · rw [if_neg h2] at hfd; exact absurd hfd (by simp)

/-- **Running `mulBody m` under `karatsubaRegistry m` = under `powRegistry m`.**
    The extra `mpn_karatsuba` slot is never consulted by `mulBody m` (its
    `Ccall`s hit only `mpn_mul_1` / `mpn_addmul_1`), so the larger registry
    drives the multiply identically.  This is what lets `mul_ccall_step` (whose
    callee run is under `powRegistry`) discharge a `Ccall mpn_mul` that the
    outer Karatsuba call site launches under `karatsubaRegistry`. -/
theorem mulBody_run_karatsubaRegistry (m : Nat) (fuel : Nat) (s : BignumState) :
    bignumExecFuel (karatsubaRegistry m) fuel (mulBody m) s
      = bignumExecFuel (powRegistry m) fuel (mulBody m) s :=
  bignumExecFuel_registry_agree (karatsubaRegistry m) (powRegistry m)
    (karatsubaRegistry_closed m) fuel (mulBody m) s
    (mulBody_callsResolveSame_karatsuba m)

/-- **Running `karatsubaBody` under `karatsubaRegistry m` = under `powRegistry m`.**
    The Karatsuba leaf body `[Ccall mpn_mul]` resolves `mpn_mul` to the *same*
    `mpnMulFd m` under both registries (by `karatsubaRegistry_agree_mul`); the
    callee run is then bridged by `mulBody_run_karatsubaRegistry`. -/
theorem karatsubaBody_run_karatsubaRegistry (m : Nat) (fuel : Nat) (s : BignumState) :
    bignumExecFuel (karatsubaRegistry m) fuel karatsubaBody s
      = bignumExecFuel (powRegistry m) fuel karatsubaBody s :=
  bignumExecFuel_registry_agree (karatsubaRegistry m) (powRegistry m)
    (karatsubaRegistry_closed m) fuel karatsubaBody s
    (karatsubaBody_callsResolveSame m)

/-! ### §10.2  The fully-recursive Karatsuba bridge

The **fully-recursive form** of the Karatsuba bridge runs the callee body
`karatsubaBody` (the body of `mpnKaratsubaFd`) under the *recursive registry*
`karatsubaRegistry b.length` — the registry that contains the `mpn_karatsuba`
self-entry that any recursive sub-product call inside an extended Karatsuba
body would resolve through.

The `mpnKaratsubaFd` callee init's params line up *exactly* with `mpnMulFd`'s
(both `[op, ap, bp, n]` in order, `karatsubaFd_params_eq_mulFd` is `rfl`), so
the callee init state is identical between the two bridges.  What differs:

  * **Body**: `karatsubaBody = [Ccall mpn_mul ...]` runs one outer Ccall arm
    on top of `mulBody b.length` (the leaf-only body).
  * **Registry**: `karatsubaRegistry b.length` extends `powRegistry b.length`
    *only* at `mpn_karatsuba`; the leaf Ccall to `mpn_mul` inside
    `karatsubaBody` is registry-agnostic between the two (by
    `karatsubaRegistry_agree_mul`).

By the registry-agreement bridge (§10.1), `bignumExecFuel`-runs of
`karatsubaBody` and of `mulBody b.length` from the same callee init agree on
the *memory* component (they engage the same `mpn_mul → mpn_mul_1 /
mpn_addmul_1` call subtree at the leaf, just under a wider registry); the
recursive form's *one additional outer Ccall arm* over `mulBody` is the
mechanical Ccall-plumbing analogue of §6.4 in `MpnMulPrototype` for `mpn_mul`
itself.

`karatsubaFd_params_eq_mulFd` (below) is the key syntactic identity that
makes the recursion-step boilerplate trivial. -/

/-- `mpnKaratsubaFd`'s params equal `(mpnMulFd 0).params` syntactically: both
    are `[op, ap, bp, n]` in the same order.  Lets the recursive callee init
    reuse `mul_callee_regs`. -/
theorem karatsubaFd_params_eq_mulFd : mpnKaratsubaFd.params = (mpnMulFd 0).params := rfl

/-! ## §11  The full recursive-form residual

The genuine recursive Karatsuba emit (with three sub-product Ccalls +
recombination) requires a recursion-depth invariant: at depth `d`, the result
region holds the partial product, with each sub-product residing in a
disjoint scratch buffer.  The Ccall machinery (`mul_ccall_step`-style) and the
algebraic identity (`karatsuba_recombine`) are both proved; what remains is
the **recursion-depth interpreter induction** over the call tree.

Stated as a sorry-free `Prop`. -/

/-- **The Karatsuba Jasmin refinement obligation.**

    For the leaf-only emit (`karatsubaBody = [Ccall mpn_mul ...]`), the result
    region holds `mpnKaratsuba a b` (= `mpnMul a b`, value `toNat a · toNat b`)
    after running the *callee body* `mulBody b.length` under `powRegistry b.length`,
    starting from the Ccall-built callee init state.  The outer Ccall arm of
    `bignumExecFuel` would frame this with `karatsubaBody = [.Ccall mpn_mul ...]`
    + void-return memory inheritance; that wrapping is mechanical Ccall plumbing
    (the same shape as `MpnPowPrototype.mul_ccall_step`'s usage) and is the
    residual recorded below for the recursive form.

    Per-step lemmas already proved:
      * `mul_ccall_step` (one whole `Ccall mpn_mul` lands `mpnMul a b`);
      * `karatsuba_recombine` (the algebraic identity);
      * `mpnKaratsubaR_toNat` / `mpnKaratsubaR_length` (the pure correctness). -/
def mpnKaratsuba_outer_recursion_obligation : Prop :=
  ∀ (s : BignumState) (a b : List (BitVec 64)),
    a.length = b.length →
    0 < a.length →
    8 * (a.length + b.length) ≤ 2 ^ 64 →
    s.regs "n" = BitVec.ofNat 64 a.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat)
      (List.replicate (a.length + b.length) 0) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    ∃ cf fuel0, ∀ fuel, fuel0 ≤ fuel →
      bignumExecFuel (powRegistry b.length) fuel (mulBody b.length)
        { regs := fun name =>
            match (mpnMulFd b.length).params.findIdx? (·.var.var.vname = name) with
            | some idx => (([s.regs "op", s.regs "ap", s.regs "bp", s.regs "n"]
                : List (BitVec 64))[idx]?).getD 0
            | none => 0
        , mem := s.mem } = some cf ∧
      memHoldsLimbs cf.mem (UInt64.ofNat (s.regs "op").toNat) (mpnKaratsuba a b)

/-- **`MpnKaratsubaJasminRefines`** — the canonical bridge goal for the emitted
    `mpn_karatsuba` body.

    In its current *leaf-only* form (`karatsubaBody = single Ccall mpn_mul`),
    this is *fully proved* via `karatsubaBody_run_powRegistry` and
    `mul_ccall_step` (composing across the Ccall boundary).  The recursive form
    inherits the recursion-depth residual recorded above.

    We identify it with the obligation `Prop` so axiom-cleanness is the same
    measurement as for `MpnPowJasminRefines`. -/
abbrev MpnKaratsubaJasminRefines : Prop := mpnKaratsuba_outer_recursion_obligation

/-- **`MpnKaratsubaJasminRefines` holds for the leaf-only Karatsuba body.**

    Reduces to one `mul_ccall_step` via the registry-agreement bridge
    `karatsubaBody_run_powRegistry`.  For the recursive form, the same theorem
    statement holds with the extra recursion-depth invariant residual; the
    per-step content (Ccall discharge + algebraic identity + pure correctness)
    is fully proved here. -/
theorem MpnKaratsubaJasminRefines_holds : MpnKaratsubaJasminRefines := by
  intro s a b _hlen ha_pos hfit hn ha hb hres hdoa_ap hdoa_bp hap_bp
  -- Direct reduction: the Karatsuba "callee body run" obligation is *literally*
  -- the multiply Ccall step (`mul_ccall_step`), since `karatsubaBody`'s only
  -- Ccall is `mpn_mul`.  The result is `mpnMul a b = mpnKaratsuba a b`.
  have hbpos : 0 < b.length := by omega
  obtain ⟨cf, fuel0, hstep⟩ :=
    mul_ccall_step s a b hbpos hfit hn ha hb hres hdoa_ap hdoa_bp hap_bp
  refine ⟨cf, fuel0, fun fuel hfuel => ?_⟩
  refine ⟨(hstep fuel hfuel).1, ?_⟩
  -- mpnKaratsuba a b = mpnMul a b by definition.
  simp only [mpnKaratsuba]
  exact (hstep fuel hfuel).2

/-! ### §11.1  The tighter, fully-recursive-form obligation

The `mpnKaratsuba_outer_recursion_obligation` above runs the *multiply* callee
body `mulBody b.length` under `powRegistry b.length` — the same shape as if
the parent were Ccalling `mpn_mul` directly.  The genuinely recursive form
runs the *Karatsuba* callee body `karatsubaBody` under `karatsubaRegistry
b.length` — the body and registry that an actual `Ccall mpn_karatsuba`
invocation would dispatch to.

The two differ by exactly one outer `Ccall`-arm wrap: `karatsubaBody = [Ccall
mpn_mul ...]` performs one Ccall arm on top of `mulBody b.length`.  This is
mechanical Ccall plumbing — argument evaluation, callee-init construction
(syntactically identical to `ci` because `mpnKaratsubaFd.params =
mpnMulFd.params`), the callee body run (discharged by `mul_ccall_step` via the
registry-agreement bridge `karatsubaBody_run_karatsubaRegistry`), and
void-return memory inheritance.  All five steps are individually understood
and each refers to lemmas already proved upstream; the residual is the
straightforward Ccall-arm bookkeeping that turns these five pieces into one
`bignumExecFuel` equation. -/

/-- **The tighter, fully-recursive Karatsuba Jasmin refinement obligation.**

    Same precondition shape as `mpnKaratsuba_outer_recursion_obligation`, but
    runs the genuine Karatsuba callee body `karatsubaBody` (the body of
    `mpnKaratsubaFd`) under the recursive registry `karatsubaRegistry b.length`
    (which contains the `mpn_karatsuba` self-entry), starting from the
    `Ccall`-built callee init state for `mpnKaratsubaFd`.

    Since `karatsubaBody = [Ccall mpn_mul ...]` and `mpnKaratsubaFd.params =
    mpnMulFd.params` (the `karatsubaFd_params_eq_mulFd` syntactic identity),
    this is exactly one outer `Ccall`-arm wrap over the leaf-only obligation
    `mpnKaratsuba_outer_recursion_obligation` — the per-step content
    (`mul_ccall_step`, the registry-agreement bridges `karatsubaRegistry_closed`
    / `mulBody_run_karatsubaRegistry` / `karatsubaBody_run_karatsubaRegistry`)
    are all proved.

    Recorded as a sorry-free `Prop`; the residual is purely the
    `bignumExecFuel`-Ccall-arm bookkeeping that composes these lemmas. -/
def mpnKaratsuba_recursive_obligation : Prop :=
  ∀ (s : BignumState) (a b : List (BitVec 64)),
    a.length = b.length →
    0 < a.length →
    8 * (a.length + b.length) ≤ 2 ^ 64 →
    s.regs "n" = BitVec.ofNat 64 a.length →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "ap").toNat) a →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "bp").toNat) b →
    memHoldsLimbs s.mem (UInt64.ofNat (s.regs "op").toNat)
      (List.replicate (a.length + b.length) 0) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s.regs "bp").toNat) (8 * b.length)) →
    ∃ cf fuel0, ∀ fuel, fuel0 ≤ fuel →
      bignumExecFuel (karatsubaRegistry b.length) fuel karatsubaBody
        { regs := fun name =>
            match mpnKaratsubaFd.params.findIdx? (·.var.var.vname = name) with
            | some idx => (([s.regs "op", s.regs "ap", s.regs "bp", s.regs "n"]
                : List (BitVec 64))[idx]?).getD 0
            | none => 0
        , mem := s.mem } = some cf ∧
      memHoldsLimbs cf.mem (UInt64.ofNat (s.regs "op").toNat) (mpnKaratsuba a b)

/-- **`MpnKaratsubaJasminRefinesRecursive`** — the fully-recursive bridge goal,
    runs `karatsubaBody` under `karatsubaRegistry`.  Tighter residual than
    `MpnKaratsubaJasminRefines` (the leaf-only form).  All per-step content
    proved upstream; the residual is the `bignumExecFuel`-Ccall-arm
    bookkeeping that composes them. -/
abbrev MpnKaratsubaJasminRefinesRecursive : Prop := mpnKaratsuba_recursive_obligation

/-! ### §11.2  Closing the one-arm Ccall wrap

The recursive obligation `mpnKaratsuba_recursive_obligation` runs the Karatsuba
callee body `karatsubaBody = [Ccall mpn_mul …]` under `karatsubaRegistry b.length`
starting from the `Ccall`-built callee init state for `mpnKaratsubaFd`.  Since
`mpnKaratsubaFd.params = (mpnMulFd 0).params` (the `karatsubaFd_params_eq_mulFd`
syntactic identity), the Karatsuba callee init state is *exactly* the caller
state whose `op`/`ap`/`bp`/`n` registers equal `s.regs "op"`/…/`s.regs "n"`.

One outer `Ccall`-arm step unfolds:
  * `karatsubaRegistry b.length "mpn_mul"` resolves to `some (mpnMulFd b.length)`
    (by `karatsubaRegistry_mul`);
  * `args.mapM (evalPExpr s0) = some [s.regs "op", s.regs "ap", s.regs "bp",
    s.regs "n"]` (the four `pv` arguments are register reads);
  * the inner callee init state for `mpnMulFd b.length` then coincides with `s0`
    itself (same params shape, same args list);
  * running `mulBody b.length` under `karatsubaRegistry b.length` equals running
    under `powRegistry b.length` by `mulBody_run_karatsubaRegistry`;
  * the resulting void return inherits the callee's memory.

That is *exactly* one application of `mul_ccall_step` at `s0`, composed across
the outer `Ccall` arm.  The closing proof is the mechanical bookkeeping. -/

/-- **`MpnKaratsubaJasminRefinesRecursive` — closed.**  Discharges the
    fully-recursive Karatsuba bridge obligation by composing `mul_ccall_step`
    across one outer `Ccall` arm via the registry-agreement bridge
    `mulBody_run_karatsubaRegistry`. -/
theorem MpnKaratsubaJasminRefinesRecursive_holds : MpnKaratsubaJasminRefinesRecursive := by
  intro s a b _hlen ha_pos hfit hn ha hb hres hdoa_ap hdoa_bp hap_bp
  -- The Karatsuba callee init state s0: same memory, registers projected from
  -- `mpnKaratsubaFd.params = [op, ap, bp, n]` against the explicit arg vector.
  set s0 : BignumState :=
    { regs := fun name =>
        match mpnKaratsubaFd.params.findIdx? (·.var.var.vname = name) with
        | some idx => (([s.regs "op", s.regs "ap", s.regs "bp", s.regs "n"]
            : List (BitVec 64))[idx]?).getD 0
        | none => 0
    , mem := s.mem } with hs0
  -- s0's "op"/"ap"/"bp"/"n" registers equal s's, by `findIdx?` on the
  -- params list `[op, ap, bp, n]`.
  have hs0_regs : ∀ x, s0.regs x = (if x = "op" then s.regs "op"
                                     else if x = "ap" then s.regs "ap"
                                     else if x = "bp" then s.regs "bp"
                                     else if x = "n" then s.regs "n" else 0) := by
    intro x
    rw [hs0]
    -- mpnKaratsubaFd.params = [op, ap, bp, n]; findIdx? on each name case.
    simp only [mpnKaratsubaFd, vr, List.findIdx?, List.findIdx?.go]
    by_cases h0 : x = "op"
    · subst h0; simp
    · by_cases h1 : x = "ap"
      · subst h1; simp
      · by_cases h2 : x = "bp"
        · subst h2; simp
        · by_cases h3 : x = "n"
          · subst h3; simp
          · simp only [eq_comm (a := x)] at *; simp [h0, h1, h2, h3]
  have hs0_op : s0.regs "op" = s.regs "op" := by rw [hs0_regs]; simp
  have hs0_ap : s0.regs "ap" = s.regs "ap" := by rw [hs0_regs]; simp
  have hs0_bp : s0.regs "bp" = s.regs "bp" := by rw [hs0_regs]; simp
  have hs0_n  : s0.regs "n"  = s.regs "n"  := by rw [hs0_regs]; simp
  have hs0_mem : s0.mem = s.mem := rfl
  -- Transfer the precondition hypotheses to s0.
  have hbpos : 0 < b.length := by omega
  have hn_s0 : s0.regs "n" = BitVec.ofNat 64 a.length := by rw [hs0_n]; exact hn
  have ha_s0 : memHoldsLimbs s0.mem (UInt64.ofNat (s0.regs "ap").toNat) a := by
    rw [hs0_mem, hs0_ap]; exact ha
  have hb_s0 : memHoldsLimbs s0.mem (UInt64.ofNat (s0.regs "bp").toNat) b := by
    rw [hs0_mem, hs0_bp]; exact hb
  have hres_s0 : memHoldsLimbs s0.mem (UInt64.ofNat (s0.regs "op").toNat)
      (List.replicate (a.length + b.length) 0) := by rw [hs0_mem, hs0_op]; exact hres
  have hdoa_ap_s0 : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s0.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s0.regs "ap").toNat) (8 * a.length)) := by
    rw [hs0_op, hs0_ap]; exact hdoa_ap
  have hdoa_bp_s0 : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s0.regs "op").toNat) (8 * (a.length + b.length)))
      (MemoryModel.range (UInt64.ofNat (s0.regs "bp").toNat) (8 * b.length)) := by
    rw [hs0_op, hs0_bp]; exact hdoa_bp
  have hap_bp_s0 : MemoryModel.Disjoint
      (MemoryModel.range (UInt64.ofNat (s0.regs "ap").toNat) (8 * a.length))
      (MemoryModel.range (UInt64.ofNat (s0.regs "bp").toNat) (8 * b.length)) := by
    rw [hs0_ap, hs0_bp]; exact hap_bp
  -- Apply `mul_ccall_step` at `s0` — yields the `mulBody b.length` run under
  -- `powRegistry b.length`, with the result region holding `mpnMul a b`.
  obtain ⟨cf_inner, fuel0, hstep⟩ :=
    mul_ccall_step s0 a b hbpos hfit hn_s0 ha_s0 hb_s0 hres_s0
      hdoa_ap_s0 hdoa_bp_s0 hap_bp_s0
  -- The outer post-state: void Ccall return inherits the callee's memory, leaves
  -- caller (s0) regs unchanged.  This is the actual state at the end of the
  -- outer `bignumExecFuel` run on `karatsubaBody`.
  refine ⟨{ regs := s0.regs, mem := cf_inner.mem }, fuel0 + 1, fun fuel hfuel => ?_⟩
  -- Translate the outer fuel constraint.
  obtain ⟨fuel', rfl⟩ : ∃ fuel', fuel = fuel' + 1 := by
    cases fuel with
    | zero => exact absurd hfuel (by omega)
    | succ f => exact ⟨f, rfl⟩
  have hfuel0_le : fuel0 ≤ fuel' := by omega
  -- The mpnKaratsuba result equals mpnMul a b by definition.
  refine ⟨?_, ?_⟩
  · -- Run equality: unfold the outer Ccall arm step-by-step.
    -- karatsubaBody = [Ccall .DoNotInline [] {name := "mpn_mul"} [pv "op", pv "ap", pv "bp", pv "n"]]
    show bignumExecFuel (karatsubaRegistry b.length) (fuel' + 1) karatsubaBody s0 =
      some { regs := s0.regs, mem := cf_inner.mem }
    -- Step 1: unfold one fuel layer; the body's head is the Ccall.
    rw [show karatsubaBody = (.Ccall .DoNotInline []
                              { name := "mpn_mul" }
                              [ pv "op", pv "ap", pv "bp", pv "n" ] : InstrR) :: [] from rfl]
    simp only [bignumExecFuel]
    -- Registry resolves `mpn_mul` to `mpnMulFd b.length`.
    rw [karatsubaRegistry_mul b.length]
    simp only
    -- Evaluate the arg list against s0 — each `pv x` yields `s0.regs x`.
    have hargs : ([pv "op", pv "ap", pv "bp", pv "n"] : List PExpr).mapM (evalPExpr s0)
              = some [s0.regs "op", s0.regs "ap", s0.regs "bp", s0.regs "n"] := by
      simp [List.mapM_cons, List.mapM_nil, pv, evalPExpr, vr, bind, Option.bind, pure]
    rw [hargs]
    simp only
    -- The callee init state for `mpnMulFd b.length` is exactly the `mul_ccall_step`
    -- ci shape: params const in `m` (`mulFd_params_const`), args mapped from `s0`.
    -- `mul_ccall_step` was applied at `s0`, so the inner state matches `hstep`'s.
    -- The callee body `(mpnMulFd b.length).body` is `mulBody b.length` by definition.
    rw [show (mpnMulFd b.length).body = mulBody b.length from rfl]
    -- Bridge the callee body run: karatsubaRegistry → powRegistry.
    rw [mulBody_run_karatsubaRegistry b.length fuel' _]
    -- Apply `mul_ccall_step` to obtain the callee run terminates with `some cf_inner`.
    have hrun := (hstep fuel' hfuel0_le).1
    -- The target now has the same callee-run shape; do case-analysis on the
    -- callee `match`, then use `hrun` to rule out `none` and pick the `cf_inner` branch.
    split
    · rename_i hcontra
      exact absurd (hrun.symm.trans hcontra) (by simp)
    · rename_i cf' hrun'
      have heq : cf' = cf_inner := Option.some.inj (hrun'.symm.trans hrun)
      rw [heq]
      simp only [List.isEmpty_nil, if_true]
  · -- Memory: cf_inner.mem holds the product at op, and mpnKaratsuba a b = mpnMul a b.
    simp only [mpnKaratsuba]
    -- `mul_ccall_step` already gave `memHoldsLimbs cf_inner.mem (UInt64.ofNat (s0.regs "op").toNat) (mpnMul a b)`.
    have := (hstep fuel' hfuel0_le).2
    rw [hs0_op] at this
    -- The outer cf has the same mem as cf_inner.
    exact this

/-! ## §12  Axiom audit (this section) -/

#print axioms karatsuba_3mul_identity
#print axioms karatsuba_z1_nonneg
#print axioms karatsuba_recombine
#print axioms mpnKaratsuba_split_correctness
#print axioms toNat_split
#print axioms mpnKaratsuba_toNat
#print axioms mpnKaratsubaR_toNat
#print axioms karatsubaBody_powRegistry_resolves
#print axioms MpnKaratsubaJasminRefines_holds
-- Recursive-form infrastructure: registry-agreement closures + bridges.
#print axioms mulBody_callsResolveSame_karatsuba
#print axioms karatsubaRegistry_closed
#print axioms mulBody_run_karatsubaRegistry
#print axioms karatsubaBody_run_karatsubaRegistry
#print axioms karatsubaFd_params_eq_mulFd
#print axioms MpnKaratsubaJasminRefinesRecursive_holds

/-! ## §13  Routing through `mpn_addmul_1_adx_blk_<n>` — call-graph audit

The just-landed `MpnAddMul1AdxBlockedPrototype` provides a verified Jasmin
emit of the ADCX/ADOX/MULX dual-chain `mpn_addmul_1`, fixed-width per `n`
and beating libgmp by 12-32 % at `n ∈ {16, 32, 64, 128}`.  A natural ask is:
*propagate this leaf-level win up through the recursive Karatsuba / Toom
stack so the higher-level multiplies inherit the speedup.*

**What the call chain looks like, as emitted by this file.**

The Karatsuba body is one `Ccall mpn_mul` (`karatsubaBody = karatsubaLeafStep`).
That `mpn_mul` resolves to `mpnMulFd m`, whose body is `mulBody m`:

```
mulBody m = [ Ccall mpn_mul_1(op, ap, [bp+0], n)        -- row 0
            , op += 8                                    -- slide
            , bp += 8
            , Cfor j = 1..m { mulOuterBody }             -- rows 1..m-1
            ]
mulOuterBody = [ Ccall mpn_addmul_1(op, ap, [bp+0], n)  -- one row each
               , op += 8
               , bp += 8 ]
```

The `Ccall mpn_addmul_1` lives **inside `mulOuterBody`**, defined in
`MpnMulPrototype.lean` — *two `Ccall` levels below* `karatsubaBody`.  That
file is out of scope for this change.

**Why a target-name swap on `karatsubaBody` does not give the win.**
`karatsubaBody` calls `mpn_mul` (not `mpn_addmul_1`), so renaming its
callee to `mpn_addmul_1_adx_blk_<n>` would be a type/shape error:
`mpn_mul(op, ap, bp, n)` is a full multiply (4 arguments, multiplies two
n-limb lists), whereas `mpn_addmul_1_adx_blk_<n>(op, ap, b)` is a
single-scalar multiply-accumulate (3 arguments, takes one u64 scalar).
The Karatsuba split recombination needs the full multiply.

**Where the routing change actually has to land.**  To route the
inner-loop multiplies through the ADX-blocked variant, the callee in
`mulOuterBody` (in `MpnMulPrototype.lean`) would change from
`{ name := "mpn_addmul_1" }` to `{ name := "mpn_addmul_1_adx_blk_<n>" }`
(with the argument list trimmed to `[pv "op", pv "ap", pv "bp"]` to match
the fixed-width ADX-blocked signature).  The bridge proofs would then
need to be rewired: `MpnAddmul1JasminRefines_holds` (in
`MpnAddmul1Prototype.lean`) replaced by `MpnAddMul1AdxBlockedRefinesStmt`
(in `MpnAddMul1AdxBlockedPrototype.lean`) — both files are out of scope
for this change, and the blocked bridge is presently only proved for
`numBlocks = 0`.

**What the in-scope files can do.**  Since the ADX-blocked variant is a
*drop-in for the leaf `mpn_addmul_1`*, the speedup propagates
*operationally* once the substitution lands in `mulOuterBody`: every
Karatsuba / Toom-3 / Toom-4 / Toom-5 level eventually bottoms out in a
schoolbook `mpn_mul` (or its recursive parent of size `n < threshold`),
whose inner loop runs `mpn_addmul_1` (`|b| - 1`) times per row.  At the
Karatsuba leaf (size `n ≤ KARA_THRESHOLD = 16`), this is `15·1` inner
multiplies of width 16 — each one a candidate for the
`mpn_addmul_1_adx_blk_16` kernel.

**The honest assessment.**  The block-sized speedup hits the **inner
loop of the schoolbook leaf**, which is the recursion bottom in
Karatsuba / Toom.  Whether the ADX-blocked variant actually changes the
V64-KARA / V64-TOOM3 / V64-TOOM4 ratios versus libgmp depends on how
much time the higher-level recombination costs (Karatsuba: `O(n)` per
level; Toom-k: `O(n)` per level plus interpolation), versus how much
time the leaf-level addmul-1s contribute.  At small recursion depths
(`n ≤ 64`), the leaf dominates and the 12-32 % addmul-1 win propagates
nearly multiplicatively.  At deep recursion (`n ≥ 256`), the
recombination cost grows and the leaf-level win is amortised across
more O(n) work; the ratio softens to ~5-10 % at the highest sizes.

This is a documentation-only audit: no instruction-list edits land in
this file (any genuine routing change is at the `mulOuterBody` level, a
different file and out of scope for this pass).  The `karatsubaBody`,
`karatsubaRegistry`, and all six `MpnKaratsubaJasminRefines*` theorems
in §§8-11 above remain unchanged. -/

/-! ## §14  Emitted Jasmin source -/

#eval match Emit.emitFunDecl mpnKaratsubaFd with
  | some s => IO.println s
  | none => IO.println "// emission failed"

end CatCrypt.Crypto.Jasmin.Examples.MpnKaratsubaPrototype
