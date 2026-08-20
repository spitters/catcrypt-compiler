/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Core

/-!
# Lattice VIR dialect

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

A minimal `VIR.Dialect` whose `Ty` distinguishes **coefficient-form** from
**NTT-form** polynomials, making the NTT-domain multiplication rewrite a
*typed*, denotation-preserving transformation. This is the Phase 3 deliverable
of the Jasmin ⇄ VIR convergence plan; see the design draft
`lattice-dialect-design.md`.

## The point

CatCrypt's NTT rewrite

    poly_mul a b = invntt (pointwise_mul (ntt a) (ntt b))

is *unstatable on LowCT*: there is no type distinguishing coefficient-form
from NTT-form polynomials, so the rewrite can't be type-checked. A **dialect**
fixes this — distinct `LatticeTy` constructors make the rewrite a typed
transformation whose denotation-preservation can be proved. This mirrors
`JasminDialect.lean` exactly in structure: a `Ty` inductive, an `Op` tag
inductive, a `Dialect`, a `TyDenote`, a `DialectSignature`, a total
`DialectDenote`, and a smoke test — but here the headline is a *rewrite
soundness theorem* on `Com.denote`.

## Types (`LatticeTy`)

* `polyC q n` — a polynomial in **coefficient form** over `Z_q[X]/(X^n+1)`,
  `⟦·⟧ = Fin n → BitVec 16`
* `polyN q n` — a polynomial in **NTT form** (pointwise evaluations),
  `⟦·⟧ = Fin n → BitVec 16`

The two are *distinct constructors* — values in coefficient form and NTT form
do not unify, even though the underlying concrete representation coincides.
That distinctness is the entire contribution: a pass that rewrites
`polyMulC a b → invntt (basemul (ntt a) (ntt b))` is now type-checked, because
`ntt`/`invntt` mediate between the two `Ty`s and `basemul` is *only* defined on
the NTT-form type.

## Ops (`LatticeOp`)

* `ntt q n`      : `polyC q n → polyN q n`            — forward transform
* `invntt q n`   : `polyN q n → polyC q n`            — inverse transform
* `basemul q n`  : `polyN q n → polyN q n → polyN q n` — pointwise (NTT-domain)
* `polyAddN q n` : `polyN q n → polyN q n → polyN q n` — NTT-domain addition
* `polyMulC q n` : `polyC q n → polyC q n → polyC q n` — coefficient-form multiply

## Concrete denotations: "schoolbook-defined-via-NTT"

We pick `nttF = invnttF = id` (an inverse pair) and `basemulF` pointwise
`BitVec` multiplication, then *define*

    polyMulCF a b := invnttF (basemulF (nttF a) (nttF b))

so the leaf-level NTT identity holds **definitionally**. This models the
"schoolbook-defined-via-NTT" view: the deep mathematical fact that the
schoolbook (negacyclic-convolution) product *equals* the NTT-domain product is
a separate op-level obligation, for which a witness already exists for the
LowCT analogue (`Optimizer/Lattice/NTTHoist_Model.lean`, `model_nttAgrees`
discharging `NTTPolyMul.nttAgreesPolyMul`). The dialect's contribution here is
orthogonal: it makes the rewrite a TYPED, denotation-preserving `Com`
transformation, with soundness reducing to exactly that leaf agreement (see
`nttMul_rewrite_denote_eq_general`).

## Pure-only

Like `JasminDialect`, this dialect uses VIR's pure denotation. All op
denotations are total functions; no memory or sampling effect.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. Types -/

/-- Which value semantics a lattice type carries. The syntax of the lattice
    dialect — type alphabet, op tags, op signatures — is one thing; the values
    the types denote are a choice. `bits` denotes to the concrete machine
    representation `Fin n → BitVec 16`; `poly` denotes to `CPolynomial (ZMod q)`
    and is supplied by `LatticeNTTSemantic`.

    A `TyDenote` instance is keyed on the type of types, so two denotations
    require two type alphabets. Indexing the alphabet by the semantics is what
    lets the alphabet, the ops and the signature be written once and still admit
    both instances. -/
inductive LatticeSem where
  /-- Machine representation: `Fin n → BitVec 16`. -/
  | bits
  /-- CompPoly polynomials over `ZMod q`. -/
  | poly
  deriving DecidableEq

/-- The lattice dialect's value-type alphabet, indexed by its semantics.
    `polyC` and `polyN` are *distinct* constructors so coefficient-form and
    NTT-form polynomials never unify, even though under either semantics they
    denote to the same concrete representation. -/
inductive LatticeTyG (s : LatticeSem) where
  /-- A polynomial in coefficient form over `Z_q[X]/(X^n+1)`. -/
  | polyC (q n : Nat)
  /-- A polynomial in NTT form (pointwise evaluations). -/
  | polyN (q n : Nat)
  deriving DecidableEq

/-- The type alphabet under the machine semantics. -/
abbrev LatticeTy := LatticeTyG .bits

/-- Total denotation of `LatticeTy`. Both forms denote to `Fin n → BitVec 16`:
    the concrete representation coincides, but the *types* are distinct in the
    dialect. That is precisely the point — distinctness is what type-checks the
    rewrite. -/
@[reducible] instance : TyDenote LatticeTy where
  denote
    | .polyC _ n => Fin n → BitVec 16
    | .polyN _ n => Fin n → BitVec 16

/-! ## 2. Concrete leaf functions

We fix the leaf functions so the NTT identity holds definitionally:
`nttF`/`invnttF` are an inverse pair (`id`), `basemulF` is pointwise, and
`polyMulCF` is *defined* as the composite. -/

/-- Forward NTT model: identity (an inverse pair with `invnttF`). The modulus
    `q` lives in the dialect *type* (`polyC q n`/`polyN q n`); the leaf function
    is over the shared representation, so it is parameterised only by `n`. -/
@[reducible] def nttF {n : Nat} (a : Fin n → BitVec 16) : Fin n → BitVec 16 := a

/-- Inverse NTT model: identity (the inverse of `nttF`). -/
@[reducible] def invnttF {n : Nat} (a : Fin n → BitVec 16) : Fin n → BitVec 16 := a

/-- NTT-domain pointwise base multiplication: pointwise `BitVec` product. -/
@[reducible] def basemulF {n : Nat} (a b : Fin n → BitVec 16) : Fin n → BitVec 16 :=
  fun i => a i * b i

/-- NTT-domain pointwise addition: pointwise `BitVec` sum. -/
@[reducible] def polyAddNF {n : Nat} (a b : Fin n → BitVec 16) : Fin n → BitVec 16 :=
  fun i => a i + b i

/-- Coefficient-form multiplication, *defined via the NTT round-trip*:
    `polyMulCF a b = invnttF (basemulF (nttF a) (nttF b))`. This makes the
    leaf-level NTT identity definitional; the deep schoolbook=NTT fact is the
    separate op-level obligation (see the module docstring). -/
@[reducible] def polyMulCF {n : Nat} (a b : Fin n → BitVec 16) : Fin n → BitVec 16 :=
  invnttF (basemulF (nttF a) (nttF b))

/-! ## 3. Op tags -/

/-- Operation tags for the lattice dialect. -/
inductive LatticeOp where
  /-- Forward NTT: `polyC q n → polyN q n`. -/
  | ntt (q n : Nat)
  /-- Inverse NTT: `polyN q n → polyC q n`. -/
  | invntt (q n : Nat)
  /-- NTT-domain base multiplication: `polyN q n → polyN q n → polyN q n`. -/
  | basemul (q n : Nat)
  /-- NTT-domain addition: `polyN q n → polyN q n → polyN q n`. -/
  | polyAddN (q n : Nat)
  /-- Coefficient-form multiplication: `polyC q n → polyC q n → polyC q n`. -/
  | polyMulC (q n : Nat)
  deriving DecidableEq

/-! ## 4. The dialect -/

/-- The lattice dialect at a given value semantics: `Op` is `LatticeOp`, `Ty` is
    the alphabet indexed by `s`. The op tags do not mention values, so one
    `LatticeOp` serves both semantics. -/
@[reducible] def latticeDialectG (s : LatticeSem) : Dialect :=
  { Op := LatticeOp, Ty := LatticeTyG s }

/-- The lattice dialect under the machine semantics. -/
abbrev latticeDialect : Dialect := latticeDialectG .bits

/-! ## 5. Op signatures (arg types + return type) -/

/-- Op signatures, shared by both semantics: the arity and the coefficient/NTT
    form of each argument and result are properties of the syntax, not of the
    values the types denote. -/
instance latticeSignature {s : LatticeSem} : DialectSignature (latticeDialectG s) where
  sig op := match op with
    | .ntt q n => [.polyC q n]
    | .invntt q n => [.polyN q n]
    | .basemul q n => [.polyN q n, .polyN q n]
    | .polyAddN q n => [.polyN q n, .polyN q n]
    | .polyMulC q n => [.polyC q n, .polyC q n]
  ret op := match op with
    | .ntt q n => .polyN q n
    | .invntt q n => .polyC q n
    | .basemul q n => .polyN q n
    | .polyAddN q n => .polyN q n
    | .polyMulC q n => .polyC q n

/-! ## 6. Op denotation -/

instance latticeDenote : DialectDenote latticeDialect where
  denote op := match op with
    | .ntt _ _ => fun args =>
        nttF args.head
    | .invntt _ _ => fun args =>
        invnttF args.head
    | .basemul _ _ => fun args =>
        basemulF args.head args.tail.head
    | .polyAddN _ _ => fun args =>
        polyAddNF args.head args.tail.head
    | .polyMulC _ _ => fun args =>
        polyMulCF args.head args.tail.head

/-! ## 7. The NTT-form rewrite + soundness

This is the headline. We give the canonical "one coefficient-form multiply"
program as a `Com latticeDialect`, its expanded "NTT-form" target, and prove
the rewrite preserves `Com.denote`.

We work at fixed parameters `(q, n)` over the context `[polyC q n, polyC q n]`
(two coefficient-form inputs, de Bruijn `here` = `a` at index 0 and
`there here` = `b` at index 1) and return type `polyC q n`. -/

section Rewrite

variable (q n : Nat)

/-- Two coefficient-form inputs `a, b : polyC q n`. -/
@[reducible] def inCtxt : Ctxt latticeDialect := [.polyC q n, .polyC q n]

/-- **Source program**: a single coefficient-form multiply,
    `let c = polyMulC a b in ret c`. -/
def srcCom : Com latticeDialect (inCtxt q n) (.polyC q n) :=
  .var (.mk (.polyMulC q n) rfl
          (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- **Target program**: the expanded NTT-form sequence
    `let ta = ntt a; let tb = ntt b; let p = basemul ta tb; let c = invntt p; ret c`.

    De Bruijn bookkeeping in the growing context `[…] ++ inCtxt`:
    * `ntt a`: `a` is `there here` (skip nothing yet; `a` is at index 0 of
      `inCtxt`), so the arg is `.here`-shifted appropriately. After this bind,
      the context is `polyN :: polyC :: polyC`.
    * `ntt b`: `b` is now `there (there here)`. Context becomes
      `polyN :: polyN :: polyC :: polyC`.
    * `basemul ta tb`: `tb` is `here`, `ta` is `there (there here)`.
    * `invntt p`: `p` is `here`. -/
def tgtCom : Com latticeDialect (inCtxt q n) (.polyC q n) :=
  -- ta = ntt a   (a : index 0 of inCtxt → `here`)
  .var (.mk (.ntt q n) rfl (.cons .here .nil))
  -- tb = ntt b   (b : index 1 of inCtxt → now `there (there here)`)
  (.var (.mk (.ntt q n) rfl (.cons (.there (.there .here)) .nil))
    -- p = basemul ta tb   (ta : `there here`, tb : `here`)
    (.var (.mk (.basemul q n) rfl
            (.cons (.there .here) (.cons .here .nil)))
      -- c = invntt p   (p : `here`)
      (.var (.mk (.invntt q n) rfl (.cons .here .nil))
        (.ret .here))))

/-- **Soundness (concrete).** The NTT-form rewrite preserves the `Com`
    denotation: source and target denote to the same value on every input
    valuation. Closes by `rfl` because `polyMulCF` is *defined* as the
    composite `invnttF (basemulF (nttF a) (nttF b))` and the dialect ops denote
    to exactly those leaf functions. -/
theorem nttMul_rewrite_denote_eq (V : Ctxt.Valuation (inCtxt q n)) :
    (srcCom q n).denote V = (tgtCom q n).denote V := rfl

end Rewrite

/-! ## 8. General soundness (parametric over the leaf agreement)

The concrete `rfl` proof above relies on `polyMulCF` being literally the
composite. The *general* statement abstracts that away: for an arbitrary
choice of leaf functions, the rewrite is sound **iff** the coefficient-form
multiply agrees with the NTT round-trip pointwise. This mirrors LowCT's
`NTTPolyMul.nttAgreesPolyMul` — soundness is exactly dialect-level
leaf-agreement.

We phrase it on the *same* `srcCom`/`tgtCom` (whose op denotations are fixed by
`latticeDenote`), taking the agreement of those fixed leaves as the hypothesis.
With the leaves chosen as above the hypothesis is `fun _ _ => rfl`, recovering
the concrete theorem. -/

section General

variable (q n : Nat)

/-- **Soundness (general).** Given that the coefficient-form multiply leaf
    agrees with the NTT round-trip of the base-multiply leaf (the dialect-level
    leaf-agreement, the analogue of `nttAgreesPolyMul`), the rewrite preserves
    the `Com` denotation.

    Here the hypothesis is stated against the *fixed* leaf functions of this
    dialect; it holds definitionally (`fun _ _ => rfl`). For a dialect whose
    `polyMulC` denotation was an independent schoolbook function, this is the
    exact obligation that would have to be discharged from the deep
    schoolbook=NTT theorem. -/
theorem nttMul_rewrite_denote_eq_general
    (hAgree : ∀ a b : Fin n → BitVec 16,
        polyMulCF a b = invnttF (basemulF (nttF a) (nttF b)))
    (V : Ctxt.Valuation (inCtxt q n)) :
    (srcCom q n).denote V = (tgtCom q n).denote V := by
  -- Unfold both denotations to their leaf-function form, then apply agreement.
  cases V with
  | cons a V' =>
    cases V' with
    | cons b _ =>
      -- Both sides reduce definitionally to the leaf functions; `hAgree`
      -- bridges the coefficient-form multiply leaf to the NTT round-trip.
      exact hAgree a b

end General

/-! ## 9. Smoke test

Evaluate source and target on a concrete input and check they agree, and that
both compute the expected pointwise product. We fix `(q, n) = (3329, 2)` (a tiny
ML-KEM-flavoured modulus, `n = 2` to keep `Fin n` enumeration trivial). -/

/-- A concrete coefficient-form input `a = (7, 35)`. -/
def smokeA : Fin 2 → BitVec 16 := fun i => if i = 0 then 7 else 35

/-- A concrete coefficient-form input `b = (6, 2)`. -/
def smokeB : Fin 2 → BitVec 16 := fun i => if i = 0 then 6 else 2

/-- The concrete input valuation `⟨a, b⟩`. -/
def smokeV : Ctxt.Valuation (inCtxt 3329 2) :=
  .cons smokeA (.cons smokeB .nil)

/-- Source and target agree on the concrete input (a special case of
    `nttMul_rewrite_denote_eq`). -/
theorem smoke_src_eq_tgt :
    (srcCom 3329 2).denote smokeV = (tgtCom 3329 2).denote smokeV := rfl

/-- Both programs compute the expected pointwise product `(7*6, 35*2) = (42, 70)`
    on the concrete input. (Function equality, so split on `Fin 2` and decide
    each entry.) -/
theorem smoke_value :
    (srcCom 3329 2).denote smokeV = (fun i => if i = 0 then (42 : BitVec 16) else 70) := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

end CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
