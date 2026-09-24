/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import Transfer
public import ReprTransfer
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

/-!
# Deciding `ZMod p` polynomial identities by reflection to an integer computation

**Exploratory prototype.** Motivation: `HashToCurveBLS12381.isogenyPolyIdentity`
is a degree-≈63 polynomial identity over `FpBLS = ZMod p` (381-bit `p`) with
fixed RFC-9380 coefficients, true only *mod p*. `ring` over `ZMod p` OOMs and
`native_decide` on `ZMod p` `npow` OOMs, because both perform the coefficient
arithmetic *inside* `ZMod p` (repeated modular reduction / `Fin p` npow).

The Rocq proof reduces it to an **integer** polynomial identity mod `p` verified
by reflective `poly_*_Z` computation: evaluate over `ℤ`, reduce mod `p` **once**
per coefficient. This file reconstructs that route in Lean, in the shape
ParamTransfer's data-refinement layer (`ReprTransfer`, `Examples/HexDecide.lean`)
prescribes.

## What ParamTransfer provides, and where it stops

* `ReprTransfer.BinOpRealization op bop` + `eq_transfer_backward` (the CoqEAL
  data-refinement level: domain maps + an equality-reflecting codomain
  embedding + a commuting square) decides a **single closed** `ZMod` equation
  `op a b = op a' b'` by `decide` on the integer residues. This is exactly the
  `HexDecide.residueMulReal` pattern, reconstructed as `residueMulReal` below.
* But `isogenyPolyIdentity` is a `∀ x`-quantified **polynomial** identity, not a
  closed equation. `BinOpRealization` transfers *one* application of *one*
  binop; it does not compose through a whole `+`/`*`/`^` expression tree, nor
  quantify over the point `x`.

The missing piece is the *compositional* homomorphism: push evaluation through
the whole ring-expression tree via generic (representation-agnostic) lemmas,
landing on a single per-coefficient integer residue check. That is the reflective
evaluator below — the `Polynomial ℤ ⇝ List ℤ` data refinement (CoqEAL `seqpoly`)
specialised to Horner form, which is precisely `HexSeqPoly`'s subject.

## The reflective core

`evalC : List ℤ → R → R` is Horner evaluation of an **integer**-coefficient list
at a point of an arbitrary commutative ring `R` (coefficients cast in via
`Int.cast`). The homomorphism lemmas `evalC_cAdd / cScale / cMul / cPow` are
proved **once, generically** over `R` — no coefficient arithmetic, no blow-up.
Over `ZMod m`, `evalC_congr_of_dvd` is the data-refinement decision step: two
Horner polynomials agree at every point iff their coefficient difference is
divisible by `m` — a `decide`/`native_decide` check on **`ℤ`** (GMP bignum), with
the modular reduction happening once per coefficient.
-/

namespace CatCrypt.Crypto.Pairing.ZModPolyReflect

open ReprTransfer

/-! ## The integer-coefficient Horner evaluator (data refinement of `Polynomial ℤ`) -/

variable {R : Type*} [CommRing R]

/-- Horner evaluation of an integer-coefficient list (low→high) at `x : R`,
    coefficients cast in through `Int.cast`. This is the computable `List ℤ`
    representation (CoqEAL `seqpoly`) of a polynomial, read out over `R`. -/
def evalC : List ℤ → R → R
  | [], _ => 0
  | c :: cs, x => (c : R) + x * evalC cs x

/-- Coefficient-wise addition. -/
def cAdd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: cAdd p q

/-- Scalar multiplication of a coefficient list. -/
def cScale (a : ℤ) : List ℤ → List ℤ
  | [] => []
  | b :: q => (a * b) :: cScale a q

/-- Coefficient-wise (convolution) product. -/
def cMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p, q => cAdd (cScale a q) (0 :: cMul p q)

/-- Coefficient-wise subtraction. -/
def cSub (p q : List ℤ) : List ℤ := cAdd p (cScale (-1) q)

/-- Coefficient-list power. -/
def cPow (p : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n + 1 => cMul p (cPow p n)

@[simp] theorem evalC_nil (x : R) : evalC ([] : List ℤ) x = 0 := rfl

@[simp] theorem evalC_cons (c : ℤ) (cs : List ℤ) (x : R) :
    evalC (c :: cs) x = (c : R) + x * evalC cs x := rfl

/-! ### Homomorphism lemmas — proved once, generically over `R` -/

theorem evalC_cAdd (p q : List ℤ) (x : R) :
    evalC (cAdd p q) x = evalC p x + evalC q x := by
  induction p generalizing q with
  | nil => simp [cAdd]
  | cons a p ih =>
    cases q with
    | nil => simp [cAdd]
    | cons b q => simp only [cAdd, evalC_cons, ih]; push_cast; ring

theorem evalC_cScale (a : ℤ) (q : List ℤ) (x : R) :
    evalC (cScale a q) x = (a : R) * evalC q x := by
  induction q with
  | nil => simp [cScale]
  | cons b q ih => simp only [cScale, evalC_cons, ih]; push_cast; ring

theorem evalC_cMul (p q : List ℤ) (x : R) :
    evalC (cMul p q) x = evalC p x * evalC q x := by
  induction p generalizing q with
  | nil => simp [cMul]
  | cons a p ih =>
    simp only [cMul, evalC_cAdd, evalC_cScale, evalC_cons, ih]; ring

theorem evalC_cSub (p q : List ℤ) (x : R) :
    evalC (cSub p q) x = evalC p x - evalC q x := by
  simp only [cSub, evalC_cAdd, evalC_cScale]; push_cast; ring

theorem evalC_cPow (p : List ℤ) (n : ℕ) (x : R) :
    evalC (cPow p n) x = (evalC p x) ^ n := by
  induction n with
  | zero => simp [cPow, evalC]
  | succ n ih => simp only [cPow, evalC_cMul, ih, pow_succ]; ring

/-! ### The data-refinement decision step over `ZMod m`

Two Horner polynomials agree at *every* point of `ZMod m` as soon as their
coefficient lists are congruent mod `m`. The hypothesis `(m : ℤ) ∣ c` for every
coefficient `c` of the difference `cSub p q` is a **decidable integer** predicate
(`decide` / `native_decide`, GMP bignum), so the modular reduction is performed
once per coefficient rather than throughout a `ZMod p` `ring` normalisation. -/

/-- A coefficient list all of whose entries reduce to `0` in `ZMod m` evaluates
    to `0` at every point. -/
theorem evalC_eq_zero_of_all {m : ℕ} (ds : List ℤ)
    (h : ∀ c ∈ ds, ((c : ZMod m) = 0)) (x : ZMod m) : evalC ds x = 0 := by
  induction ds with
  | nil => simp
  | cons c cs ih =>
    simp only [evalC_cons]
    rw [h c (by simp), ih (fun c hc => h c (by simp [hc]))]
    ring

/-- **The reflective decision principle.** If every coefficient of the difference
    `cSub p q` is divisible by `m` — a decidable check on `ℤ` — then the two
    Horner polynomials are equal at every point of `ZMod m`. This is the
    `ReprTransfer.BinOpRealization.eq_transfer_backward` step (`decide` on the
    concrete integer representation ⟹ abstract `ZMod` equation), lifted from a
    single binop to a whole polynomial expression. -/
theorem evalC_congr_of_dvd {m : ℕ} (p q : List ℤ)
    (h : ∀ c ∈ cSub p q, (m : ℤ) ∣ c) (x : ZMod m) :
    evalC p x = evalC q x := by
  have hz : evalC (cSub p q) x = 0 := by
    apply evalC_eq_zero_of_all
    intro c hc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd c m).mpr (h c hc)
  rw [evalC_cSub] at hz
  exact sub_eq_zero.mp hz

/-! ## Toy 1 — target-faithful, degree 2, modulus 101

`(x+3)·(x+7) = x²+10x+21` over `ZMod 101`, with the factors presented as Horner
coefficient lists exactly as `hornerEval isoYnum x'` is in the target. Closed by
kernel `decide` on the integer coefficient check — **no `ring`/`native_decide`
over `ZMod`**. The only rewriting is the homomorphism lemma `evalC_cMul`. -/
example (x : ZMod 101) :
    evalC [(3 : ℤ), 1] x * evalC [(7 : ℤ), 1] x = evalC [(21 : ℤ), 10, 1] x := by
  rw [← evalC_cMul]
  apply evalC_congr_of_dvd
  decide

/-! ## Toy 2 — degree ~13, 10-digit modulus (scaling probe for `decide`)

Two distinct reflections of the same degree-13 polynomial (cube of a
degree-3 factor times a degree-4 factor, in both orders), 10-digit coefficients,
10-digit modulus. Kernel `decide` on the integer residues stays fast. -/
example (x : ZMod 9999999967) :
    (evalC [(3141592653 : ℤ), 2718281828, 1618033988, 1414213562] x) ^ 3
        * evalC [(1732050807 : ℤ), 2236067977, 2645751311, 3316624790, 1000000007] x
      = evalC [(1732050807 : ℤ), 2236067977, 2645751311, 3316624790, 1000000007] x
        * (evalC [(3141592653 : ℤ), 2718281828, 1618033988, 1414213562] x) ^ 3 := by
  rw [← evalC_cPow, ← evalC_cMul, ← evalC_cMul]
  apply evalC_congr_of_dvd
  decide

/-! ## Near-target scale — degree ~75, 381-bit BLS12-381 prime (`native_decide`)

Product of a squared degree-15 factor and a cubed degree-15 factor (degree 75,
*exceeding* the target's degree ~63), with ~115-decimal-digit (381-bit-class)
coefficients, reduced modulo the actual 381-bit BLS12-381 base-field prime. The
integer coefficient check is discharged by `native_decide` (compiled GMP
arithmetic). Kernel `decide` also succeeds up to degree ~44 but becomes the
bottleneck beyond that; `native_decide` clears the full target with headroom. -/

/-- The BLS12-381 base-field prime `p` (381 bits). -/
def blsPrime : ℕ :=
  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787

/-- 115-decimal-digit base used to synthesise 381-bit-class coefficients. -/
def bigBase : ℤ := 10 ^ 115 + 271828182845904523536

/-- A degree-15 integer-coefficient list with 381-bit-class entries. -/
def pStress : List ℤ := (List.range 16).map (fun i => bigBase * (i + 3) + 1000003)

/-- A second degree-15 integer-coefficient list with 381-bit-class entries. -/
def qStress : List ℤ := (List.range 16).map (fun i => bigBase * (i + 5) + 9999991)

example (x : ZMod blsPrime) :
    (evalC pStress x) ^ 2 * (evalC qStress x) ^ 3
      = (evalC qStress x) ^ 3 * (evalC pStress x) ^ 2 := by
  rw [← evalC_cPow, ← evalC_cPow, ← evalC_cMul, ← evalC_cMul]
  apply evalC_congr_of_dvd
  native_decide

/-! ## Direct ParamTransfer API — the closed-equation level (`ReprTransfer`)

For completeness, the *closed* (non-parametric) case is handled directly by
ParamTransfer's `ReprTransfer.BinOpRealization`, exactly as
`Transfer/Examples/HexDecide.lean` does: multiplication in `ZMod m` is realised
by integer multiply-then-reduce along the residue embedding `ZMod m ↪ ℤ`, and
`eq_transfer_backward` discharges an abstract `ZMod` product equation by `decide`
on the integer residues. This is the single-binop base case that the
compositional `evalC` layer above generalises to whole polynomials. -/

/-- The residue embedding `ZMod m ↪ ℤ` (canonical representative, injective). -/
def residueEmb (m : ℕ) [NeZero m] : ReprEmbedding (ZMod m) ℤ where
  enc := fun a => (a.val : ℤ)
  enc_inj := by
    intro a b h; simp only at h
    exact ZMod.val_injective m (by exact_mod_cast h)

/-- `ZMod m` multiplication realised by integer multiply-then-reduce. -/
def residueMulReal (m : ℕ) [NeZero m] :
    BinOpRealization (fun a b : ZMod m => a * b) (fun x y : ℤ => (x * y) % (m : ℤ)) where
  encA := fun a => (a.val : ℤ)
  encB := fun b => (b.val : ℤ)
  cod := residueEmb m
  commutes := fun a b => by
    show ((a * b).val : ℤ) = ((a.val : ℤ) * (b.val : ℤ)) % (m : ℤ)
    rw [ZMod.val_mul]; push_cast; ring

/-- A closed `ZMod 5` product equation discharged purely by `decide` on the
    integer residues, via ParamTransfer's `eq_transfer_backward`. -/
example : (2 * 3 : ZMod 5) = (1 * 1 : ZMod 5) :=
  (residueMulReal 5).eq_transfer_backward (by decide)

/-! ## Axiom audit -/

section AxiomAudit

/-- info: 'CatCrypt.Crypto.Pairing.ZModPolyReflect.evalC_congr_of_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evalC_congr_of_dvd

end AxiomAudit

end CatCrypt.Crypto.Pairing.ZModPolyReflect
