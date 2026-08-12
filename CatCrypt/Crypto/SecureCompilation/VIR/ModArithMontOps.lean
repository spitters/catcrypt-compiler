/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Core
import CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric
import Mathlib.Data.ZMod.Basic

/-!
# ModArith Montgomery domain-conversion ops — `to_mont` / `from_mont` / `mont_square`

A minimal `VIR.Dialect` whose ops are the Montgomery **domain-conversion** maps
`toMont`, `fromMont`, and the fused `montSquare`.  It is the CatCrypt counterpart
of fractalyze/prime-ir's **ModArith** dialect ops `mod_arith.to_mont`,
`mod_arith.from_mont`, and `mod_arith.mont_square` (`ModArithOps.td`).

## Why this dialect exists (the gap it closes)

CatCrypt already *computes* in the Montgomery domain — `montMul N R N'` /
`redc N R N'` (`Optimizer/Rewrite/MontgomeryRedcGeneric.lean`), with the proven
defining property `redc T · R ≡ T (mod N)` — but it does **not** expose the
domain-conversion maps `to_mont` / `from_mont` / `mont_square` as standalone
ops: they are implicit in the `montMul`/`redc` domain, and the Montgomery square
is just `montMul a a`.  This dialect **factors those three maps as first-class
ops**, matching the three prime-ir ModArith conversion ops one-for-one, with
denotations tied to the existing `montMul`/`redc` and the round-trip /
inverse-domain agreement lemmas proved on top of the **already-proved**
Montgomery reduction core (which is reused, not re-proved).

## The ops (`ModArithMontOp`), parametric in `(N R N' : ℤ)`

`N` is the modulus, `R` the Montgomery radix, `N'` the Montgomery constant
(`N · N' ≡ -1 (mod R)`).  Following `MontgomeryRedcGeneric`, residues are carried
as integers and the field meaning is read off `Int.ModEq … [ZMOD N]` (equivalently
the `ZMod N` cast).

* `toMont N R N'` — enter the Montgomery domain: `x ↦ x · R`.  (`mod_arith.to_mont`)
* `fromMont N R N'` — leave it: `x ↦ redc N R N' x` (`= x · R⁻¹ (mod N)`).
  (`mod_arith.from_mont`)
* `montSquare N R N'` — fused Montgomery square: `x ↦ montMul N R N' x x`.
  (`mod_arith.mont_square`)

## Type (`ModArithMontTy`)

* `residue N R N'` — a stored residue at modulus `N`, radix `R`, constant `N'`;
  `⟦·⟧ = ℤ`, matching the `ℤ` carrier of the `MontgomeryRedcGeneric` core (where
  the `Int.ModEq` algebra is cleanest).

## Concrete leaf functions

* `toMontF R x = x * R`
* `fromMontF N R N' x = redc N R N' x`
* `montSquareF N R N' x = montMul N R N' x x`  (the fused square is `montMul x x`
  by definition — `montSquareF_eq_montMul` is `rfl`).

## Agreement / correctness lemmas (reuse, don't re-prove, the REDC core)

The single piece of number theory is the proved lemma
`MontgomeryRedcGeneric.redc_mul_R_modEq : redc T · R ≡ T (mod N)`; every lemma
here is assembled from it (plus, for `fromMont_toMont`, the radix-inverse witness
`hRinv : R · Rinv ≡ 1 (mod N)` — the standard `gcd(R, N) = 1` precondition in
already-inverted form, carried explicitly so no inverse-existence is re-derived):

* `toMont_fromMont` : `toMont (fromMont x) ≡ x (mod N)` — *is* `redc_mul_R_modEq`.
* `fromMont_toMont` : `fromMont (toMont x) ≡ x (mod N)` — the key round-trip; cancel
  the radix using `hRinv`.
* `*_zmod` casts of both round-trips into `ZMod N` (the field-level inverse-domain
  statement).
* `montSquareF_mul_R` : `montSquare x · R ≡ x · x (mod N)` — the Montgomery-form
  correctness of the fused square, `redc_mul_R_modEq` at `x·x`.

## Honest classification

This is a **HIGH-tier, prime-ir-corresponding / agreement** dialect, NOT an
emit-wired one.  It has **no lowering out** (no `→ Com jasminDialect`, no backend
edge): like `tensorExtDialect` and the `mlirArith*` family, it is
correspondence-only: it substantiates the "prime-ir ModArith
domain-conversion aligned" claim and factors the previously-implicit Montgomery
conversions into three reusable ops with denotations tied to the existing
`montMul`/`redc` plus verified round-trip / inverse-domain laws.  It does **not**
add a new lowering or emit path — the bytes-reaching Montgomery arithmetic still
flows through the existing emit kernels (`MontgomeryMulEmitValue`,
`ConcreteMontMulRealizer`, `TransferMontRedcButterfly`, the owned `runZBlock`
REDC blocks — the `Com → jasmin → ELF` spine).  Do not
overclaim an emit this file does not build.

## Pure-only + constant-time

Each op is a fixed, data-independent arithmetic map (the Montgomery schedule is
multiply/shift, index-only, never data-dependent on a secret-chosen branch), so
its denotation is a total pure function and it is constant-time by construction
(`ctSafe = true`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ModArithMontOps

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric
  (montMul redc redc_mul_R_modEq)

/-! ## 1. Concrete leaf functions (the three Montgomery domain-conversion maps)

Each is defined directly in terms of the existing `MontgomeryRedcGeneric` core, so
their meaning is the Montgomery conversion. -/

/-- **Enter the Montgomery domain** (`mod_arith.to_mont`): `x ↦ x · R`. -/
@[reducible] def toMontF (R x : ℤ) : ℤ := x * R

/-- **Leave the Montgomery domain** (`mod_arith.from_mont`):
    `x ↦ redc N R N' x` (`= x · R⁻¹ (mod N)`).  This is exactly the proved
    `MontgomeryRedcGeneric.redc`. -/
@[reducible] def fromMontF (N R N' x : ℤ) : ℤ := redc N R N' x

/-- **Fused Montgomery square** (`mod_arith.mont_square`):
    `x ↦ montMul N R N' x x`, the existing `MontgomeryRedcGeneric.montMul` at a
    repeated operand. -/
@[reducible] def montSquareF (N R N' x : ℤ) : ℤ := montMul N R N' x x

/-- The fused square is `montMul x x` by definition — the standalone op is the
    diagonal of Montgomery multiplication, not a separate algorithm. -/
theorem montSquareF_eq_montMul (N R N' x : ℤ) :
    montSquareF N R N' x = montMul N R N' x x := rfl

/-- **Binary Montgomery multiply** (`mod_arith.mont_mul`):
    `(a, b) ↦ montMul N R N' a b` (`= a · b · R⁻¹ (mod N)`), the two-operand
    form of the existing `MontgomeryRedcGeneric.montMul`.  `montSquareF` is its
    diagonal (`montMulF N R N' x x = montSquareF N R N' x`). -/
@[reducible] def montMulF (N R N' a b : ℤ) : ℤ := montMul N R N' a b

/-- `montSquareF` is the diagonal of `montMulF` — repeated-operand binary
    Montgomery multiply. -/
theorem montSquareF_eq_montMulF (N R N' x : ℤ) :
    montSquareF N R N' x = montMulF N R N' x x := rfl

/-! ## 2. Type -/

/-- The ModArith-Montgomery dialect's value-type alphabet: a stored residue at
    modulus `N`, Montgomery radix `R`, and constant `N'`.  The `(N, R, N')`
    parameters are the dialect-level analogue of prime-ir's
    `!mod_arith.int<modulus : storage_type>` together with the Montgomery
    parameters the conversion ops carry. -/
inductive ModArithMontTy where
  /-- A residue at modulus `N`, radix `R`, Montgomery constant `N'`. -/
  | residue (N R N' : ℤ)
  deriving DecidableEq

/-- Total denotation of `ModArithMontTy`: a stored residue is an integer,
    matching the `ℤ` carrier of the `MontgomeryRedcGeneric` core; the field
    meaning is read via `Int.ModEq … [ZMOD N]` / the `ZMod N` cast. -/
@[reducible] instance : TyDenote ModArithMontTy where
  denote
    | .residue _ _ _ => ℤ

/-! ## 3. Op tags -/

/-- Operation tags for the ModArith-Montgomery dialect — the three Montgomery
    domain-conversion ops, mirroring prime-ir's `mod_arith.to_mont`,
    `mod_arith.from_mont`, `mod_arith.mont_square`. -/
inductive ModArithMontOp where
  /-- Enter the Montgomery domain (prime-ir `mod_arith.to_mont`). -/
  | toMont (N R N' : ℤ)
  /-- Leave the Montgomery domain (prime-ir `mod_arith.from_mont`). -/
  | fromMont (N R N' : ℤ)
  /-- Fused Montgomery square (prime-ir `mod_arith.mont_square`). -/
  | montSquare (N R N' : ℤ)
  /-- Binary Montgomery multiply (prime-ir `mod_arith.mont_mul`): two distinct
      residue operands. `montSquare` is its diagonal. -/
  | montMul (N R N' : ℤ)
  deriving DecidableEq

/-! ## 4. The dialect -/

/-- The ModArith-Montgomery dialect: `Op` is `ModArithMontOp`, `Ty` is
    `ModArithMontTy`. -/
@[reducible] def modArithMontDialect : Dialect :=
  { Op := ModArithMontOp, Ty := ModArithMontTy }

/-! ## 5. Op signature (arg types + return type)

The three domain-conversion ops are unary residue → residue at the same
`(N, R, N')`; the binary `montMul` takes two residues at that `(N, R, N')`. -/

instance : DialectSignature modArithMontDialect where
  sig op := match op with
    | .toMont N R N' => [.residue N R N']
    | .fromMont N R N' => [.residue N R N']
    | .montSquare N R N' => [.residue N R N']
    | .montMul N R N' => [.residue N R N', .residue N R N']
  ret op := match op with
    | .toMont N R N' => .residue N R N'
    | .fromMont N R N' => .residue N R N'
    | .montSquare N R N' => .residue N R N'
    | .montMul N R N' => .residue N R N'

/-! ## 6. Op denotation (into the Montgomery maps) -/

instance modArithMontDenote : DialectDenote modArithMontDialect where
  denote op := match op with
    | .toMont _ R _ => fun args => toMontF R args.head
    | .fromMont N R N' => fun args => fromMontF N R N' args.head
    | .montSquare N R N' => fun args => montSquareF N R N' args.head
    | .montMul N R N' => fun args => montMulF N R N' args.head args.tail.head

/-! ## 7. Per-op denotation agreement facts (tie each op to the existing core) -/

/-- **`toMont` denotation.** `toMont N R N'` denotes to `x ↦ x · R` — enter the
    Montgomery domain. -/
theorem toMont_denote (N R N' x : ℤ) :
    modArithMontDenote.denote (.toMont N R N') (.cons x .nil) = x * R := rfl

/-- **`fromMont` denotation.** `fromMont N R N'` denotes to the proved
    `MontgomeryRedcGeneric.redc N R N'` — leave the Montgomery domain. -/
theorem fromMont_denote (N R N' x : ℤ) :
    modArithMontDenote.denote (.fromMont N R N') (.cons x .nil) = redc N R N' x := rfl

/-- **`montSquare` denotation.** `montSquare N R N'` denotes to
    `montMul N R N' x x` — the fused square is the diagonal of the existing
    `MontgomeryRedcGeneric.montMul`. -/
theorem montSquare_denote (N R N' x : ℤ) :
    modArithMontDenote.denote (.montSquare N R N') (.cons x .nil)
      = montMul N R N' x x := rfl

/-- **`montMul` denotation.** The binary `montMul N R N'` denotes to
    `montMul N R N' a b` — Montgomery multiply on two distinct operands, the
    existing `MontgomeryRedcGeneric.montMul`.  `montSquare` is the diagonal
    (`b = a`). -/
theorem montMul_denote (N R N' a b : ℤ) :
    modArithMontDenote.denote (.montMul N R N') (.cons a (.cons b .nil))
      = montMul N R N' a b := rfl

/-! ## 8. Round-trip and inverse-domain agreement lemmas

The single piece of number theory is the proved lemma
`MontgomeryRedcGeneric.redc_mul_R_modEq`; every lemma here is assembled from it
(no Montgomery reduction is re-proved). -/

/-- **Inverse domain map A — `toMont ∘ fromMont`.**  `toMont (fromMont x) ≡ x
    (mod N)`.  This is *exactly* the proved Montgomery property
    `redc x · R ≡ x (mod N)` (`redc_mul_R_modEq`): re-entering the domain after
    leaving it restores `x`. -/
theorem toMont_fromMont (N R N' x : ℤ) (hN' : N * N' ≡ -1 [ZMOD R]) :
    toMontF R (fromMontF N R N' x) ≡ x [ZMOD N] := by
  unfold toMontF fromMontF
  exact redc_mul_R_modEq N R N' x hN'

/-- **Inverse domain map B — `fromMont ∘ toMont` (the key round-trip).**
    `fromMont (toMont x) ≡ x (mod N)`.  Leaving the domain after entering it
    restores `x`.  Built from `redc_mul_R_modEq` at `x·R` (giving
    `fromMont (toMont x) · R ≡ x · R`) and then cancelling the radix using the
    inverse witness `hRinv : R · Rinv ≡ 1 (mod N)`. -/
theorem fromMont_toMont (N R N' Rinv x : ℤ) (hN' : N * N' ≡ -1 [ZMOD R])
    (hRinv : R * Rinv ≡ 1 [ZMOD N]) :
    fromMontF N R N' (toMontF R x) ≡ x [ZMOD N] := by
  have h1 : fromMontF N R N' (toMontF R x) * R ≡ (x * R) [ZMOD N] := by
    unfold fromMontF toMontF
    exact redc_mul_R_modEq N R N' (x * R) hN'
  calc fromMontF N R N' (toMontF R x)
      = fromMontF N R N' (toMontF R x) * 1 := by ring
    _ ≡ fromMontF N R N' (toMontF R x) * (R * Rinv) [ZMOD N] := hRinv.symm.mul_left _
    _ = (fromMontF N R N' (toMontF R x) * R) * Rinv := by ring
    _ ≡ (x * R) * Rinv [ZMOD N] := h1.mul_right Rinv
    _ = x * (R * Rinv) := by ring
    _ ≡ x * 1 [ZMOD N] := hRinv.mul_left _
    _ = x := by ring

/-- **`toMont ∘ fromMont` over `ZMod N`.**  The field-level statement of
    `toMont_fromMont`: the two maps compose to the identity on `ZMod N`. -/
theorem toMont_fromMont_zmod (N : ℕ) (R N' x : ℤ) (hN' : (N : ℤ) * N' ≡ -1 [ZMOD R]) :
    ((toMontF R (fromMontF (N : ℤ) R N' x) : ℤ) : ZMod N) = ((x : ℤ) : ZMod N) :=
  (ZMod.intCast_eq_intCast_iff _ _ _).mpr (toMont_fromMont (N : ℤ) R N' x hN')

/-- **`fromMont ∘ toMont` over `ZMod N`.**  The field-level statement of the key
    round-trip `fromMont_toMont`: the two maps compose to the identity on
    `ZMod N`. -/
theorem fromMont_toMont_zmod (N : ℕ) (R N' Rinv x : ℤ) (hN' : (N : ℤ) * N' ≡ -1 [ZMOD R])
    (hRinv : R * Rinv ≡ 1 [ZMOD (N : ℤ)]) :
    ((fromMontF (N : ℤ) R N' (toMontF R x) : ℤ) : ZMod N) = ((x : ℤ) : ZMod N) :=
  (ZMod.intCast_eq_intCast_iff _ _ _).mpr (fromMont_toMont (N : ℤ) R N' Rinv x hN' hRinv)

/-- **Fused-square correctness.**  `montSquare x · R ≡ x · x (mod N)`, i.e.
    `montSquare x ≡ x² · R⁻¹ (mod N)` — the Montgomery-form output of the fused
    square.  Assembled from `redc_mul_R_modEq` at `x·x` (since `montSquare x =
    montMul x x = redc (x·x)`), reusing the proved core. -/
theorem montSquareF_mul_R (N R N' x : ℤ) (hN' : N * N' ≡ -1 [ZMOD R]) :
    montSquareF N R N' x * R ≡ x * x [ZMOD N] := by
  unfold montSquareF montMul
  exact redc_mul_R_modEq N R N' (x * x) hN'

/-! ## 9. Constant-time predicate (the dialect's CT instance)

Each conversion is a fixed multiply/shift arithmetic map — no `ite` on data, no
data-dependent memory index — so `ctSafe` is `true` for every op. -/

/-- Per-op CT predicate: every Montgomery domain-conversion op is constant-time. -/
def ModArithMontOp.ctSafe : ModArithMontOp → Bool
  | _ => true

@[simp] theorem ModArithMontOp.ctSafe_all (op : ModArithMontOp) :
    op.ctSafe = true := rfl

/-- Per-expression CT predicate. -/
def ctSafeExpr {Γ : Ctxt modArithMontDialect} {t : ModArithMontTy}
    (e : Expr modArithMontDialect Γ t) : Bool :=
  e.op.ctSafe

@[simp] theorem ctSafeExpr_true {Γ : Ctxt modArithMontDialect} {t : ModArithMontTy}
    (e : Expr modArithMontDialect Γ t) : ctSafeExpr e = true := rfl

/-- Per-program CT predicate: a `Com` is CT-safe iff every let-bound expression
    is.  Since every op is CT, this is identically `true`. -/
def ctSafeCom {Γ : Ctxt modArithMontDialect} {t : ModArithMontTy} :
    Com modArithMontDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExpr e && ctSafeCom body

/-- **CT by construction.**  Every ModArith-Montgomery program is constant-time:
    the domain conversions introduce no data-dependent control flow or memory
    index. -/
theorem ctSafeCom_all {Γ : Ctxt modArithMontDialect} {t : ModArithMontTy}
    (c : Com modArithMontDialect Γ t) : ctSafeCom c = true := by
  induction c with
  | ret _ => rfl
  | var e _ ih => simp [ctSafeCom, ctSafeExpr_true, ih]

end CatCrypt.Crypto.SecureCompilation.VIR.ModArithMontOps
