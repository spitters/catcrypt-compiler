/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSemantic
import CatCrypt.Crypto.SecureCompilation.VIR.Negacyclic

/-!
# Poly VIR dialect (#482-4 — the L4′ polynomial-ring layer, over Field/ModArith)

The **L4′** level of the PrimeIR-style layered crypto-IR stack, the
polynomial-ring sibling of the EllipticCurve(L4) layer.  It sits above the `Field`/`ModArith` dialects:

    **Poly(L4′)** → Field(L3) → ModArith(L2) → {Vector | LowCT} → {jasmin | x86}

Today every NTT-using protocol re-derives its transform separately — ML-KEM,
ML-DSA, Plonky3, FAEST each carry their own butterfly schedule and their own
"the NTT computes the negacyclic convolution" argument.  This dialect gives the
**abstract polynomial-ring layer** one verified home, mirroring the way
`ModArithDialect` gives the residue-ring layer one home, `FieldDialect` gives
the field-tower layer one home, and `EllipticCurveDialect` gives the curve-group
layer one home.

## The ring and its denotation

The dialect's ring is `R = F[X]/(Xⁿ ± 1)` over `F = ZMod q`.  We model a ring
element in **coefficient form** as a `CompPoly.CPolynomial (ZMod q)` — the
algebraic polynomial — and in **NTT (evaluation) form** as an
`Array (ZMod q)` (the evaluation vector over the NTT domain).  The polynomial-
ring ops therefore denote into the *real* CompPoly NTT pipeline
(`LatticeNTTSound`'s `realNtt`/`realInvntt`/`realBasemul`/`realNttMul`), and the
once-per-dialect tie is CompPoly's negacyclic convolution theorem
(`realNttMul_negacyclic_coeff`, #32/#35): the `nttMul` op denotes, after the
`%ₘ (Xⁿ+1)` fold, to the explicit negacyclic convolution.

## Types (`PolyTy`)

* `polyC q n` — coefficient form over `Z_q[X]/(Xⁿ+1)`, `⟦·⟧ = CPolynomial (ZMod q)`.
  This is the denotation target of `intt`/`polyAdd`/… (the source representation).
* `polyN q n` — NTT (evaluation) form, `⟦·⟧ = Array (ZMod q)` (the evaluation
  vector the pointwise ops consume).

The `polyC`-vs-`polyN` split is the dialect's contribution: the algebraic ops
that need the abstract polynomial (`intt`, the negacyclic `nttMul`) live at
`polyC`; the *evaluation-domain* ops (`ntt`, pointwise `basemul`) cross between
`polyC` and `polyN`.  The lowering (`PolyLowering.lean`) connects them down to
ModArith butterfly schedules.

## Ops (`PolyOp`)

* `ntt`        — forward NTT `polyC → polyN` (CompPoly `forwardImpl`);
* `intt`       — inverse NTT `polyN → polyC` (CompPoly `inverseImpl` + truncate);
* `basemul`    — NTT-domain pointwise product `polyN → polyN → polyN`;
* `polyAdd`    — coefficient-form add `polyC → polyC → polyC`;
* `polySub`    — coefficient-form sub `polyC → polyC → polyC`;
* `polySMul`   — scalar-multiply a coefficient polynomial by `c : ZMod q`;
* `nttMul`     — the **negacyclic convolution** `polyC → polyC → polyC`, denoting
                 to the abstract ring product via the NTT round-trip
                 (`realNttMul = invntt ∘ basemul ∘ (ntt × ntt)`).

Each op **denotes to the abstract polynomial-ring operation** — `intt` is the
identity on the polynomial value (NTT form is the same polynomial), `nttMul`/
`basemul` denote via `realNttMul` (CompPoly's `fastMulImpl`), so the butterfly
schedule is an *optimization realisation* of the abstract spec, attached at
lowering (`PolyLowering.lean`), exactly as the chord-tangent/Karatsuba/CIOS
schedules are at `EllipticCurve`/`Field`/`ModArith`.

## Per-modulus NTT domain

The ops carry their modulus `q` in their payload, so the dialect-level
denotation needs an NTT `Domain` *per modulus*; the `NttDomains` class
(reused verbatim from `LatticeNTTSemantic`) supplies one.  For ML-KEM-768 the
intended instance picks the 512-point domain (`logN = 9`), which satisfies
`2·256 ≤ 512`.

## Pure-only + constant-time

Like the other algebraic dialects, every Poly-op denotation is a total pure
function (no memory/sampling effect).  Every op is data-oblivious — the NTT
butterfly schedule and the pointwise product are fixed, index-independent
schedules (the whole point of a constant-time NTT is that the twiddle access
pattern is data-independent) — so `ctSafe` is `true` for all ops.  This is the
L4′ instance of the VIR `ctSafe` story (`CTPredicate.lean`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.LatticeNTTSemantic (NttDomains enc encRaw enc_fits
  realNttMul_negacyclic_coeff enc_toPoly_degree_lt)
open CompPoly.CPolynomial.NTT (Domain)
open CompPoly.CPolynomial.NTT.Inverse (inverseImpl)
open CatCrypt.Crypto.SecureCompilation.VIR.Negacyclic (negaPoly)
open CompPoly (CPolynomial)
open Polynomial

/-! ## 1. Types -/

/-- The Poly dialect's value-type alphabet.  `polyC` and `polyN` are *distinct*
    constructors (coefficient form vs NTT/evaluation form), both parameterised by
    the modulus `q` and the ring degree `n`. -/
inductive PolyTy where
  /-- Coefficient form over `Z_q[X]/(Xⁿ+1)`, `⟦·⟧ = CPolynomial (ZMod q)`. -/
  | polyC (q n : Nat)
  /-- NTT (evaluation) form, `⟦·⟧ = Array (ZMod q)`. -/
  | polyN (q n : Nat)
  deriving DecidableEq

/-- Total denotation of `PolyTy`: coefficient form into the CompPoly
    polynomial `CPolynomial (ZMod q)`, NTT form into the evaluation vector
    `Array (ZMod q)`. -/
@[reducible] instance : TyDenote PolyTy where
  denote
    | .polyC q _ => CPolynomial (ZMod q)
    | .polyN q _ => Array (ZMod q)

/-! ## 2. Concrete leaf functions (the abstract poly-ring operations)

The algebraic leaves are the CompPoly NTT operations
(`realNtt`/`realInvntt`/`realBasemul`/`realNttMul` from `LatticeNTTSound`), so
the denotation is the abstract polynomial-ring math, NOT the toy `id` of
`latticeDialect`.  The add/sub/scalar leaves are `CPolynomial`'s native ring
operations. -/

variable {q n : Nat}

/-- Forward NTT leaf: CompPoly's `forwardImpl`, an actual transform (not `id`).
    Needs `Field (ZMod q)` (from `Fact (Nat.Prime q)`) for the CompPoly domain. -/
@[reducible] def nttF [Fact (Nat.Prime q)] (D : Domain (ZMod q)) (p : CPolynomial (ZMod q)) :
    Array (ZMod q) :=
  realNtt D p

/-- Inverse NTT leaf: CompPoly's `inverseImpl` (+ canonicalising trim), taking an
    evaluation array back to the coefficient polynomial. -/
@[reducible] def inttF [Fact (Nat.Prime q)] (D : Domain (ZMod q)) (a : Array (ZMod q)) :
    CPolynomial (ZMod q) :=
  ⟨(inverseImpl D a).trim, CompPoly.CPolynomial.Raw.Trim.isCanonical_trim _⟩

/-- NTT-domain pointwise base multiply leaf: CompPoly's `pointwiseMul`. -/
@[reducible] def basemulF [Fact (Nat.Prime q)] (D : Domain (ZMod q)) (a b : Array (ZMod q)) :
    Array (ZMod q) :=
  realBasemul D a b

/-- Coefficient-form polynomial add: `CPolynomial`'s native `+`. -/
@[reducible] def polyAddF (p r : CPolynomial (ZMod q)) : CPolynomial (ZMod q) := p + r

/-- Coefficient-form polynomial sub: `CPolynomial`'s native `-`. -/
@[reducible] def polySubF (p r : CPolynomial (ZMod q)) : CPolynomial (ZMod q) := p - r

/-- Scalar-multiply a coefficient polynomial by `c : ZMod q`: `(C c) * p`. -/
@[reducible] def polySMulF (c : ZMod q) (p : CPolynomial (ZMod q)) : CPolynomial (ZMod q) :=
  (CompPoly.CPolynomial.C c) * p

/-- The negacyclic NTT multiply leaf: the composite
    `invntt (basemul (ntt p) (ntt q))`, definitionally CompPoly's `fastMulImpl`
    (`realNttMul`).  Under `Domain.fits` this is the *cyclic* full product; the
    `%ₘ (Xⁿ+1)` fold (the dialect's negacyclic tie) turns it into the ring
    product of `Z_q[X]/(Xⁿ+1)`. -/
@[reducible] def nttMulF [Fact (Nat.Prime q)] (D : Domain (ZMod q)) (p r : CPolynomial (ZMod q)) :
    CPolynomial (ZMod q) :=
  realNttMul D p r

/-! ## 3. Op tags -/

/-- Operation tags for the Poly dialect.  The algebraic ops live over the
    polynomial-ring types `polyC`/`polyN`; each denotes to the abstract
    polynomial-ring operation (NTT round-trip, negacyclic convolution). -/
inductive PolyOp where
  /-- Forward NTT `polyC q n → polyN q n`. -/
  | ntt (q n : Nat)
  /-- Inverse NTT `polyN q n → polyC q n`. -/
  | intt (q n : Nat)
  /-- NTT-domain pointwise base multiply `polyN q n → polyN q n → polyN q n`. -/
  | basemul (q n : Nat)
  /-- Coefficient-form add `polyC q n → polyC q n → polyC q n`. -/
  | polyAdd (q n : Nat)
  /-- Coefficient-form sub `polyC q n → polyC q n → polyC q n`. -/
  | polySub (q n : Nat)
  /-- Scalar-multiply `polyC q n → polyC q n`, carrying the scalar `c : ZMod q`. -/
  | polySMul (q n : Nat) (c : ZMod q)
  /-- Negacyclic NTT multiply `polyC q n → polyC q n → polyC q n` (the headline
      op; denotes via `realNttMul` to the abstract ring product). -/
  | nttMul (q n : Nat)
  deriving DecidableEq

/-! ## 4. The dialect -/

/-- The Poly dialect: `Op` is `PolyOp`, `Ty` is `PolyTy`. -/
@[reducible] def polyDialect : Dialect :=
  { Op := PolyOp, Ty := PolyTy }

/-! ## 5. Op signatures (arg types + return type) -/

instance : DialectSignature polyDialect where
  sig op := match op with
    | .ntt q n => [.polyC q n]
    | .intt q n => [.polyN q n]
    | .basemul q n => [.polyN q n, .polyN q n]
    | .polyAdd q n => [.polyC q n, .polyC q n]
    | .polySub q n => [.polyC q n, .polyC q n]
    | .polySMul q n _ => [.polyC q n]
    | .nttMul q n => [.polyC q n, .polyC q n]
  ret op := match op with
    | .ntt q n => .polyN q n
    | .intt q n => .polyC q n
    | .basemul q n => .polyN q n
    | .polyAdd q n => .polyC q n
    | .polySub q n => .polyC q n
    | .polySMul q n _ => .polyC q n
    | .nttMul q n => .polyC q n

/-! ## 6. Op denotation (into the abstract polynomial ring)

The ops carry their modulus `q`; the denotation needs an NTT `Domain` per
modulus (the `NttDomains` class).  As in `realLatticeDenote`, the modulus guard
`Nat.Prime q` keeps the denotation total (the `else 0`/`else #[]` branch is
never exercised by the headline programs, which fix a prime `q`). -/

noncomputable instance polyDenote [ND : NttDomains] : DialectDenote polyDialect where
  denote op := match op with
    | .ntt q _ => fun args =>
        if h : Nat.Prime q then
          haveI : Fact (Nat.Prime q) := ⟨h⟩
          nttF (ND.dom q) args.head
        else (#[] : Array (ZMod q))
    | .intt q _ => fun args =>
        if h : Nat.Prime q then
          haveI : Fact (Nat.Prime q) := ⟨h⟩
          inttF (ND.dom q) args.head
        else (0 : CPolynomial (ZMod q))
    | .basemul q _ => fun args =>
        if h : Nat.Prime q then
          haveI : Fact (Nat.Prime q) := ⟨h⟩
          basemulF (ND.dom q) args.head args.tail.head
        else (#[] : Array (ZMod q))
    | .polyAdd _ _ => fun args => polyAddF args.head args.tail.head
    | .polySub _ _ => fun args => polySubF args.head args.tail.head
    | .polySMul _ _ c => fun args => polySMulF c args.head
    | .nttMul q _ => fun args =>
        if h : Nat.Prime q then
          haveI : Fact (Nat.Prime q) := ⟨h⟩
          nttMulF (ND.dom q) args.head args.tail.head
        else (0 : CPolynomial (ZMod q))

/-! ## 7. Constant-time predicate (L4′ instance of `CTPredicate.lean`)

Every Poly op is data-oblivious: the NTT butterfly schedule, the pointwise
product, and the coefficient add/sub/scalar are fixed, index-independent
schedules (no `ite` on data, no data-dependent memory index — a constant-time
NTT's twiddle access is data-independent by construction).  So `ctSafe` is
`true` for all ops. -/

/-- Per-op CT predicate: every Poly op is constant-time. -/
def PolyOp.ctSafe : PolyOp → Bool
  | _ => true

@[simp] theorem PolyOp.ctSafe_all (op : PolyOp) : op.ctSafe = true := rfl

/-- Per-expression CT predicate. -/
def ctSafeExpr {Γ : Ctxt polyDialect} {t : PolyTy}
    (e : Expr polyDialect Γ t) : Bool :=
  e.op.ctSafe

@[simp] theorem ctSafeExpr_true {Γ : Ctxt polyDialect} {t : PolyTy}
    (e : Expr polyDialect Γ t) : ctSafeExpr e = true := rfl

/-- Per-program CT predicate: a `Com` is CT-safe iff every let-bound expression
    is.  Since all Poly ops are CT, this is identically `true`. -/
def ctSafeCom {Γ : Ctxt polyDialect} {t : PolyTy} :
    Com polyDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExpr e && ctSafeCom body

/-- **CT by construction.** Every Poly program is constant-time.  This is the
    L4′-level realisation of the VIR CT-safety guarantee: the NTT layer
    introduces no data-dependent control flow or memory index, so CT-safety is
    free — it does not have to be re-checked per protocol. -/
theorem ctSafeCom_all {Γ : Ctxt polyDialect} {t : PolyTy}
    (c : Com polyDialect Γ t) : ctSafeCom c = true := by
  induction c with
  | ret _ => rfl
  | var e _ ih => simp [ctSafeCom, ctSafeExpr_true, ih]

/-! ## 8. Algebraic denotation facts (the once-per-dialect ties)

The add/sub/scalar facts hold **definitionally** (the leaves are `CPolynomial`'s
native ring ops).  The `nttMul` negacyclic fact is the deep tie: it reuses
CompPoly's `realNttMul_negacyclic_coeff` (#32/#35), so the dialect's `nttMul`
op — after the `%ₘ (Xⁿ+1)` fold — denotes to the negacyclic
convolution, stated **once** at the dialect. -/

variable [ND : NttDomains]

/-- `polyAdd` denotes to `CPolynomial` addition. -/
theorem polyAdd_denote (p r : CPolynomial (ZMod q)) :
    polyDenote.denote (.polyAdd q n) (.cons p (.cons r .nil)) = p + r := rfl

/-- `polySub` denotes to `CPolynomial` subtraction. -/
theorem polySub_denote (p r : CPolynomial (ZMod q)) :
    polyDenote.denote (.polySub q n) (.cons p (.cons r .nil)) = p - r := rfl

/-- `polySMul c` denotes to scalar-by-`c` multiplication. -/
theorem polySMul_denote (c : ZMod q) (p : CPolynomial (ZMod q)) :
    polyDenote.denote (.polySMul q n c) (.cons p .nil) = (CompPoly.CPolynomial.C c) * p := rfl

/-- `nttMul` denotes to `realNttMul` (CompPoly's `fastMulImpl`) for a prime
    modulus — the abstract NTT-based ring product, with the deep transform
    content carried inside `realNttMul`. -/
theorem nttMul_denote [Fact (Nat.Prime q)] (p r : CPolynomial (ZMod q)) :
    polyDenote.denote (.nttMul q n) (.cons p (.cons r .nil)) = realNttMul (ND.dom q) p r := by
  show (if h : Nat.Prime q then
          (haveI : Fact (Nat.Prime q) := ⟨h⟩; nttMulF (ND.dom q) p r)
        else (0 : CPolynomial (ZMod q))) = realNttMul (ND.dom q) p r
  rw [dif_pos (Fact.out : Nat.Prime q)]

/-- **The once-per-dialect negacyclic tie (#32/#35).** With the CompPoly
    NTT operations plugged into the dialect denotation, the negacyclic reduction
    `%ₘ (Xⁿ+1)` of the `nttMul` op's denotation, on the encoded inputs
    `enc a`, `enc b`, has its `k`-th coefficient (`k < n`) equal to the explicit
    negacyclic convolution

      `(Σ_{i+j=k} (enc a)ᵢ (enc b)ⱼ) − (Σ_{i+j=k+n} (enc a)ᵢ (enc b)ⱼ)`.

    This lifts `realNttMul_negacyclic_coeff` (the op-level CompPoly tie) onto the
    Poly **dialect** denotation: the dialect's `nttMul` op denotes, under the real
    ops, to the negacyclic product of `Z_q[X]/(Xⁿ+1)`.  It is the single
    structural tie connecting the abstract NTT op to the convolution spec; every
    NTT-using protocol inherits it without re-proving the transform. -/
theorem nttMul_negacyclic_coeff [Fact (Nat.Prime q)]
    (hD : 2 * n ≤ (ND.dom q).n) (hn : 0 < n)
    (a b : Fin n → BitVec 16) {k : Nat} (hk : k < n) :
    ((polyDenote.denote (.nttMul q n)
          (.cons (enc q n a) (.cons (enc q n b) .nil))).toPoly %ₘ negaPoly n).coeff k
      = (∑ ij ∈ Finset.antidiagonal k,
            (enc q n a).toPoly.coeff ij.1 * (enc q n b).toPoly.coeff ij.2)
        - (∑ ij ∈ Finset.antidiagonal (k + n),
            (enc q n a).toPoly.coeff ij.1 * (enc q n b).toPoly.coeff ij.2) := by
  rw [nttMul_denote (q := q) (n := n) (enc q n a) (enc q n b)]
  exact realNttMul_negacyclic_coeff (ND.dom q) hD hn a b hk

end CatCrypt.Crypto.SecureCompilation.VIR.PolyDialect
