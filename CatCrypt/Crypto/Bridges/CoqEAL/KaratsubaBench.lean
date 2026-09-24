/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CompPoly.Univariate.Raw.Ops

/-!
# Computable mirror of recursive Karatsuba (benchmark harness for item 4c)

This is the **computable mirror** for the 4c crossover benchmark: recursive
Karatsuba versus schoolbook polynomial multiplication. The *verified*
algorithm, `CatCrypt.Crypto.Bridges.CoqEAL.Karatsuba.karatsubaRec`
(in `KaratsubaRec.lean`), is `noncomputable` because it is phrased over
`CompPoly.CPolynomial R` and its correctness proof transfers across
`CPolynomial.ringEquiv` to Mathlib `Polynomial R`. It therefore cannot be
`#eval`'d. This file re-expresses exactly the same algorithm over the
**computable** array-backed representation `CompPoly.CPolynomial.Raw R`
(`= Array R`), whose `mul`/`add`/`sub`/`mulPowX`/`divX`/`smul` operations are
all executable (no `noncomputable`, no open goals).

## Representation

We work over `R = Int` and the array-backed `CPolynomial.Raw Int`
(coefficient `i` is the array element at index `i`, low-order first). This
representation is computable and its ring operations come straight from the
CompPoly library, so `schoolbookMul` reuses the library's verified `O(n²)`
convolution `CPolynomial.Raw.mul`, and `karatsubaMul` is the recursive split
mirroring `karatsubaRec` step-for-step (high part = `divX^[k]`, low part =
`p − Xᵏ · hiPart`, three subproducts `z₀,z₂,z₁`, recombine
`z₀ + Xᵏ·z₁ + X²ᵏ·z₂`).

`Int` is exact (no modular wrap), so Karatsuba and schoolbook compute the same
product. Coefficients can grow, but for the dense pseudo-random inputs used by
the harness this is fine and keeps the benchmark dependency-light (no `ZMod`
literal modulus needed).

This module contains **only** the defs and the `main` runner, so a compiled
`lake exe` does not pay any elaboration-time agreement check. The
correctness theorem `karatsubaComp_toPoly_eq_schoolbook` and the `native_decide`
agreement check live in the companion `KaratsubaBenchTest.lean`, which imports
this module and is built in CI.

## How the orchestrator uses this

The orchestrator runs this file (e.g. `lean --run …KaratsubaBench.lean k 256
100`) at several degrees in both modes (`k` = Karatsuba, `s` = schoolbook) and
**times the whole process externally** with the shell — there is no in-Lean
timing (the sandbox `IO.monoMsNow` returns 0). `main` builds two deterministic
dense polynomials of the requested degree, runs the chosen multiply `iters`
times, accumulates a checksum (so the work is not dead-code-eliminated), and
prints the checksum together with the parsed `(mode, degree, iters)`. Sweeping
the degree and comparing the two modes' wall-clock times locates the crossover
degree where Karatsuba overtakes schoolbook.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Bridges.CoqEAL.KaratsubaBench

open CompPoly CompPoly.CPolynomial.Raw

/-- The computable coefficient representation: array-backed polynomials over `Int`,
    coefficient `i` stored at index `i` (low-order first). -/
abbrev P := CPolynomial.Raw Int

/-- **Schoolbook multiply** — the library's `O(n²)` convolution
    `CPolynomial.Raw.mul`, i.e. `Σᵢ (aᵢ · q) · Xⁱ`. This is the baseline the
    benchmark compares Karatsuba against. -/
@[inline] def schoolbookMul (p q : P) : P := CPolynomial.Raw.mul p q

/-- High part of a split at degree `k`: drop the `k` lowest coefficients by
    iterating `divX` (pseudo-division by `X`) `k` times. Computable mirror of
    `KaratsubaRec.hiPart`. -/
@[inline] def hiPart (k : Nat) (p : P) : P := CPolynomial.Raw.divX^[k] p

/-- Low part of a split at degree `k`, the complement of `Xᵏ · hiPart`:
    `p − Xᵏ · hiPart k p`. Computable mirror of `KaratsubaRec.loPart`. -/
@[inline] def loPart (k : Nat) (p : P) : P :=
  CPolynomial.Raw.sub p (CPolynomial.Raw.mulPowX k (hiPart k p))

/-- A balanced split point: half the larger degree, plus one (so a nonconstant
    input is split nontrivially). Computable mirror of `KaratsubaRec.splitPoint`. -/
@[inline] def splitPoint (p q : P) : Nat :=
  (max (CPolynomial.Raw.natDegree p) (CPolynomial.Raw.natDegree q)) / 2 + 1

/-- **Recursive Karatsuba multiplication** with explicit `fuel`, the computable
    mirror of `KaratsubaRec.karatsubaRec`.

    At `fuel = 0` it falls back to the schoolbook product. Otherwise it splits
    both inputs at `splitPoint p q`, recursively forms the three Karatsuba
    subproducts `z₀ = plo·qlo`, `z₂ = phi·qhi`, `(plo+phi)·(qlo+qhi)`, and
    recombines as `z₀ + Xᵏ·z₁ + X²ᵏ·z₂` with `z₁ = (plo+phi)(qlo+qhi) − z₀ − z₂`.

    A guard short-circuits to schoolbook once either input is small (degree ≤ 1),
    matching the standard threshold presentation; correctness is independent of
    the threshold/fuel (every fuel value computes the same product). -/
def karatsubaMul : Nat → P → P → P
  | 0, p, q => schoolbookMul p q
  | fuel + 1, p, q =>
    if CPolynomial.Raw.natDegree p ≤ 1 || CPolynomial.Raw.natDegree q ≤ 1 then
      schoolbookMul p q
    else
      let k := splitPoint p q
      let plo := loPart k p
      let phi := hiPart k p
      let qlo := loPart k q
      let qhi := hiPart k q
      let z0 := karatsubaMul fuel plo qlo
      let z2 := karatsubaMul fuel phi qhi
      let zmid := karatsubaMul fuel (CPolynomial.Raw.add plo phi) (CPolynomial.Raw.add qlo qhi)
      let z1 := CPolynomial.Raw.sub (CPolynomial.Raw.sub zmid z0) z2
      CPolynomial.Raw.add
        (CPolynomial.Raw.add z0 (CPolynomial.Raw.mulPowX k z1))
        (CPolynomial.Raw.mulPowX (2 * k) z2)

/-- Karatsuba product of two computable polynomials. Fuel is taken generously
    (`natDegree + 2`) so the recursion always reaches the schoolbook base on
    each branch. -/
@[inline] def karatsubaComp (p q : P) : P :=
  karatsubaMul (max (CPolynomial.Raw.natDegree p) (CPolynomial.Raw.natDegree q) + 2) p q

/-- Schoolbook product of two computable polynomials. -/
@[inline] def schoolbookComp (p q : P) : P := schoolbookMul p q

/-- A deterministic dense polynomial of the given degree: coefficient `i` is
    `(i*i + 1) mod 1009` (seeded, reproducible, no `IO.rand`/`Math.random`). -/
def densePoly (degree : Nat) (offset : Nat) : P :=
  CPolynomial.Raw.mk <|
    (Array.range (degree + 1)).map (fun i =>
      (Int.ofNat (((i + offset) * (i + offset) + 1) % 1009)))

/-- Fold a polynomial's coefficients into a single `Int` checksum, so the
    benchmark work cannot be dead-code-eliminated. -/
def checksum (p : P) : Int := p.foldl (fun acc c => acc * 31 + c) 17

/-- Run `mul` on the two inputs `iters` times, accumulating a checksum across
    iterations (each iteration perturbs the inputs slightly so the optimizer
    cannot hoist the call out of the loop). -/
def runLoop (mul : P → P → P) (a b : P) (iters : Nat) : Int := Id.run do
  let mut acc : Int := 0
  for i in [0:iters] do
    -- perturb the constant term per iteration to defeat CSE / loop hoisting
    let a' := CPolynomial.Raw.add a (CPolynomial.Raw.C (Int.ofNat (i % 7)))
    acc := acc + checksum (mul a' b)
  return acc

/-- Parse a `Nat` argument with a default fallback. -/
def parseNat (s : Option String) (default : Nat) : Nat :=
  match s with
  | none => default
  | some str => (str.toNat?).getD default

/-- Benchmark entry point.

    Args (passed by `lean --run` / a `lake exe`): `mode degree iters`, all
    optional with defaults `mode = "k"`, `degree = 256`, `iters = 100`.
    `mode = "k"` runs recursive Karatsuba, anything else (`"s"`) runs
    schoolbook. Builds two deterministic dense polynomials of the requested
    degree, runs the chosen multiply `iters` times accumulating a checksum, and
    prints the checksum and parsed args. Timing is performed externally by the
    orchestrator's shell. -/
def main (args : List String) : IO Unit := do
  let mode := args[0]?.getD "k"
  let degree := parseNat args[1]? 256
  let iters := parseNat args[2]? 100
  let a := densePoly degree 0
  let b := densePoly degree 17
  let mul := if mode == "k" then karatsubaComp else schoolbookComp
  let acc := runLoop mul a b iters
  IO.println s!"mode={mode} degree={degree} iters={iters} checksum={acc}"

end CatCrypt.Crypto.Bridges.CoqEAL.KaratsubaBench
