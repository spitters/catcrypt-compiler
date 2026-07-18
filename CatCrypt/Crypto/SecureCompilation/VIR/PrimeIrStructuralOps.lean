/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

/-!
# Prime-ir structural / reinterpret ops — `poly.to_tensor` / `poly.from_tensor`
  and `field.bitcast` / `mod_arith.bitcast`

A minimal **correspondence** `VIR.Dialect` whose ops are the prime-ir
*structural / reinterpret* ops that move data between equivalent representations
without doing arithmetic:

* `poly.to_tensor` / `poly.from_tensor` — the coefficient-vector ↔ polynomial
  maps (a polynomial in coefficient form *is* its coefficient tensor);
* `field.bitcast` / `mod_arith.bitcast` — the reinterpret-bits map between a
  field / mod-arith residue and its fixed-width `BitVec` storage.

It is the CatCrypt counterpart of prime-ir's `poly.to_tensor` /
`poly.from_tensor` (§3 of `PRIME_IR_GAP_ANALYSIS.md`) and `field.bitcast` /
`mod_arith.bitcast` (§1 / §2).

## Why this dialect exists (the gaps it closes)

Per `PRIME_IR_GAP_ANALYSIS.md` (repo root), these reinterpret maps were already
*used* — but only **implicitly**, never factored as standalone ops:

* `poly.to_tensor` (§3, line 89) — "`polyC`↔coeff-tensor via `from_tensor`
  leaf; implicit" — **PARTIAL**.
* `poly.from_tensor` (§3, line 90) — "implicit coeff construction" — **PARTIAL**.
* `field.bitcast` (§1, line 25) — "via leaf decode; no dedicated op" — **PARTIAL**.
* `mod_arith.bitcast` (§2, line 56) — "leaf decode" — **PARTIAL**.

This file **factors all four as first-class ops** with concrete denotations and
the round-trip lemmas a reinterpret op must satisfy — WITHOUT modifying the
`FieldDialect` / `ModArithDialect` / `PolyDialect` `Op` sets (additive only).

## The representations

* **Poly ↔ tensor.** prime-ir's `poly.to_tensor : PolyType → RankedTensor` and
  `poly.from_tensor : RankedTensor → PolyType` move between a degree-`< n`
  polynomial and its rank-1 length-`n` coefficient tensor.  We model **both
  sides in coefficient form** as the coefficient vector `Fin n → ZMod q`: a
  polynomial of degree `< n` over `Z_q` *is* its `n`-coefficient vector, and the
  tensor *is* that same vector viewed as a rank-1 array.  The two maps are
  therefore the identity on the coefficient vector — the reinterpret carries no
  arithmetic content — and the round-trips
  `polyFromTensor (polyToTensor p) = p`, `polyToTensor (polyFromTensor t) = t`
  hold by `rfl`.  (This is the honest "the poly IS its coeff tensor" model: it
  factors the *reinterpret*, not any NTT/transform content, which lives in
  `PolyDialect`'s `ntt`/`nttMul` ops.)

* **Field / mod-arith ↔ bits.** prime-ir's `field.bitcast` / `mod_arith.bitcast`
  reinterpret a residue's bits as a fixed-width integer storage and back.  We
  model the storage as `BitVec w` and the residue as `ZMod p`:

  * encode `ZMod p → BitVec w` is `a ↦ BitVec.ofNat w a.val` (the canonical
    little-endian residue bits);
  * decode `BitVec w → ZMod p` is `b ↦ (b.toNat : ZMod p)`.

  The round-trip `decode (encode a) = a` holds when the storage is wide enough
  to hold the modulus (`p ≤ 2^w`, no truncation); the reverse
  `encode (decode b) = b` holds when `b` already stores a canonical residue
  (`b.toNat < p`).  Both are the genuine no-truncation conditions a bit-reinterpret
  needs; we state them as explicit hypotheses rather than baking in a width.

## Honest classification (read `VIR/DIALECTS.md`)

This is a **HIGH-tier, prime-ir-corresponding / agreement** dialect, NOT an
emit-wired one.  Like `mlirArithDialect`, `tensorExtDialect`, `cmpDialect`, and
the `FieldDerivedOps` derived-arithmetic dialect in DIALECTS.md's
"correspondence-only" table, it has **no lowering out** (no `→ Com
jasminDialect`, no backend edge).  It substantiates the "prime-ir
`poly.to_tensor` / `poly.from_tensor` / `field.bitcast` / `mod_arith.bitcast`
aligned" claim by giving those reinterpret maps a first-class op with a verified
denotation and round-trip.  It does **not** add a lowering or emit path.  Do not
overclaim an emit this file does not build.

## What this file does NOT close (still-PARTIAL, named honestly)

* `elliptic_curve.pairing_check` (§4, line 123) — we have the Miller-loop / Fp12
  pieces (`RelationalFrontBls377MillerLoop.lean`, `…Fp12*.lean`) but a *fused*
  single `pairing_check` op that packages them is **deliberately skipped here**.
  Packaging it faithfully requires routing through those relational-front pieces
  (not a clean carrier-level identity like the maps above), so it would not be
  the additive, denotation-by-leaf shape this file keeps.  It remains a genuine
  **PARTIAL**; this file does not claim to close it.
* `elliptic_curve.bitcast` (§4, line 125) — the EC-point bit reinterpret — is
  also left as PARTIAL: an EC point is a multi-coordinate aggregate, so its
  bitcast is a tuple-of-residues reinterpret, not the single-residue map factored
  here.

## Pure-only + constant-time

Every op here is a **data-oblivious** reinterpret: `to_tensor`/`from_tensor`
relabel the same vector, and the field/mod bitcast is a fixed-width bit copy
(`BitVec.ofNat` / `toNat`) with no branch on the operand value and no
data-dependent index.  So `ctSafe` is `true` for every op — exactly the
`FieldDerivedOps`/`PolyDialect` data-oblivious story (and unlike the
equality-test ops of `cmpDialect`, these never branch on a secret value).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.PrimeIrStructuralOps

open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. The leaf functions (the denotation targets)

Each is a total reinterpret function.  The poly/tensor leaves are the identity
on the coefficient vector `Fin n → ZMod q`; the bitcast leaves are the canonical
encode/decode between `ZMod p` and `BitVec w`. -/

/-- `poly.to_tensor` leaf: reinterpret a degree-`< n` coefficient-form polynomial
    (modeled as its coefficient vector `Fin n → ZMod q`) as its rank-1 length-`n`
    coefficient tensor.  Since both sides are the coefficient vector, this is the
    identity — the reinterpret carries no arithmetic. -/
@[reducible] def polyToTensorF (q n : Nat) (p : Fin n → ZMod q) : Fin n → ZMod q := p

/-- `poly.from_tensor` leaf: reinterpret a rank-1 length-`n` coefficient tensor
    as the coefficient-form polynomial whose coefficients it lists.  The inverse
    of `polyToTensorF`; again the identity on the coefficient vector. -/
@[reducible] def polyFromTensorF (q n : Nat) (t : Fin n → ZMod q) : Fin n → ZMod q := t

/-- `field.bitcast` / `mod_arith.bitcast` **encode** leaf: reinterpret a residue
    `a : ZMod p` as its canonical fixed-width `BitVec w` storage, the
    little-endian bits of `a.val`. -/
@[reducible] def residueEncodeF (p w : Nat) (a : ZMod p) : BitVec w :=
  BitVec.ofNat w a.val

/-- `field.bitcast` / `mod_arith.bitcast` **decode** leaf: reinterpret a
    fixed-width `BitVec w` storage `b` as the residue `b.toNat : ZMod p`.  The
    inverse of `residueEncodeF` under the no-truncation / canonical-storage
    conditions. -/
@[reducible] def residueDecodeF (p w : Nat) (b : BitVec w) : ZMod p :=
  (b.toNat : ZMod p)

/-! ## 2. Round-trip / agreement lemmas (reinterpret correctness)

The once-per-op correctness ties.  Poly↔tensor round-trips are `rfl` (identity
on the coefficient vector).  The bitcast round-trips carry the genuine
no-truncation hypotheses: `decode ∘ encode = id` needs the storage wide enough
for the modulus (`p ≤ 2^w`); `encode ∘ decode = id` needs the stored value to be
a canonical residue (`b.toNat < p`). -/

/-- **Poly↔tensor round-trip.** `from_tensor (to_tensor p) = p` — the
    coefficient vector survives the reinterpret untouched. -/
theorem polyFromTensor_polyToTensor {q n : Nat} (p : Fin n → ZMod q) :
    polyFromTensorF q n (polyToTensorF q n p) = p := rfl

/-- **Poly↔tensor round-trip (other side).** `to_tensor (from_tensor t) = t`. -/
theorem polyToTensor_polyFromTensor {q n : Nat} (t : Fin n → ZMod q) :
    polyToTensorF q n (polyFromTensorF q n t) = t := rfl

/-- `to_tensor` and `from_tensor` are mutually inverse reinterprets (both the
    identity on the coefficient vector). -/
theorem polyToTensor_eq_polyFromTensor {q n : Nat} (v : Fin n → ZMod q) :
    polyToTensorF q n v = polyFromTensorF q n v := rfl

/-- **Bitcast round-trip (decode ∘ encode).** Reinterpreting a residue as bits
    and back recovers the residue, provided the storage is wide enough to hold
    the modulus (`p ≤ 2^w`), so the canonical value `a.val < p ≤ 2^w` is not
    truncated. -/
theorem residueDecode_residueEncode {p w : Nat} [NeZero p] (a : ZMod p)
    (hp : p ≤ 2 ^ w) :
    residueDecodeF p w (residueEncodeF p w a) = a := by
  have hlt : a.val < 2 ^ w := lt_of_lt_of_le (ZMod.val_lt a) hp
  simp only [residueDecodeF, residueEncodeF, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlt, ZMod.natCast_val, ZMod.cast_id]

/-- **Bitcast round-trip (encode ∘ decode).** Reinterpreting a `BitVec` storage
    as a residue and back recovers the storage, provided the storage already
    holds a canonical residue (`b.toNat < p`). -/
theorem residueEncode_residueDecode {p w : Nat} [NeZero p] (b : BitVec w)
    (hb : b.toNat < p) :
    residueEncodeF p w (residueDecodeF p w b) = b := by
  simp only [residueEncodeF, residueDecodeF, ZMod.val_natCast,
    Nat.mod_eq_of_lt hb, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## 3. Type (`StructTy`)

The reinterpret operands.  Poly and tensor share the coefficient-vector carrier
(distinguished as constructors so the *ops* carry the prime-ir source/dest
distinction); the residue and bit-storage carriers are `ZMod p` and `BitVec w`. -/

/-- The structural-ops dialect's value-type alphabet. -/
inductive StructTy where
  /-- Coefficient-form polynomial over `Z_q[X]`, degree `< n`, `⟦·⟧ = Fin n → ZMod q`
      (the coefficient vector). -/
  | poly (q n : Nat)
  /-- Rank-1 length-`n` coefficient tensor over `Z_q`, `⟦·⟧ = Fin n → ZMod q`. -/
  | tensor (q n : Nat)
  /-- A residue in `F_p` / `Z_p` (the `FieldDialect` / `ModArithDialect` carrier),
      `⟦·⟧ = ZMod p`. -/
  | residue (p : Nat)
  /-- Fixed-width `BitVec w` storage, `⟦·⟧ = BitVec w`. -/
  | bits (w : Nat)
  deriving DecidableEq

/-- Total denotation of `StructTy`.  Poly and tensor both denote to the
    coefficient vector `Fin n → ZMod q` (a poly in coefficient form *is* its
    coefficient tensor); residue to `ZMod p`; bits to `BitVec w`. -/
@[reducible] instance : TyDenote StructTy where
  denote
    | .poly q n => Fin n → ZMod q
    | .tensor q n => Fin n → ZMod q
    | .residue p => ZMod p
    | .bits w => BitVec w

/-! ## 4. Op tags (`StructOp`)

The reinterpret ops.  The two bitcast directions carry the modulus `p` and the
storage width `w`. -/

/-- Operation tags for the structural-ops dialect — prime-ir's reinterpret ops. -/
inductive StructOp where
  /-- `poly.to_tensor` over `poly q n → tensor q n`. -/
  | polyToTensor (q n : Nat)
  /-- `poly.from_tensor` over `tensor q n → poly q n`. -/
  | polyFromTensor (q n : Nat)
  /-- `field.bitcast` / `mod_arith.bitcast` **encode** `residue p → bits w`. -/
  | residueEncode (p w : Nat)
  /-- `field.bitcast` / `mod_arith.bitcast` **decode** `bits w → residue p`. -/
  | residueDecode (p w : Nat)
  deriving DecidableEq

/-! ## 5. The dialect -/

/-- The structural-ops dialect: `Op` is `StructOp`, `Ty` is `StructTy`. -/
@[reducible] def structDialect : Dialect :=
  { Op := StructOp, Ty := StructTy }

/-! ## 6. Op signatures (arg types + return type) -/

instance : DialectSignature structDialect where
  sig op := match op with
    | .polyToTensor q n => [.poly q n]
    | .polyFromTensor q n => [.tensor q n]
    | .residueEncode p _ => [.residue p]
    | .residueDecode _ w => [.bits w]
  ret op := match op with
    | .polyToTensor q n => .tensor q n
    | .polyFromTensor q n => .poly q n
    | .residueEncode _ w => .bits w
    | .residueDecode p _ => .residue p

/-! ## 7. Op denotation (into the genuine reinterpret leaves) -/

instance structDenote : DialectDenote structDialect where
  denote op := match op with
    | .polyToTensor q n => fun args => polyToTensorF q n args.head
    | .polyFromTensor q n => fun args => polyFromTensorF q n args.head
    | .residueEncode p w => fun args => residueEncodeF p w args.head
    | .residueDecode p w => fun args => residueDecodeF p w args.head

/-! ## 8. Per-op denotation / round-trip facts (the once-per-op ties)

The per-op denotations hold definitionally (the op denotations are the leaf
functions); combined with §2's round-trips, each reinterpret pair is shown
inverse. -/

/-- `poly.to_tensor` denotes to the identity on the coefficient vector. -/
theorem polyToTensor_denote {q n : Nat} (p : Fin n → ZMod q) :
    structDenote.denote (.polyToTensor q n) (.cons p .nil) = p := rfl

/-- `poly.from_tensor` denotes to the identity on the coefficient vector. -/
theorem polyFromTensor_denote {q n : Nat} (t : Fin n → ZMod q) :
    structDenote.denote (.polyFromTensor q n) (.cons t .nil) = t := rfl

/-- **Round-trip at the denotation level.** `⟦from_tensor⟧ (⟦to_tensor⟧ p) = p`. -/
theorem polyFromTensor_denote_polyToTensor_denote {q n : Nat} (p : Fin n → ZMod q) :
    structDenote.denote (.polyFromTensor q n)
        (.cons (structDenote.denote (.polyToTensor q n) (.cons p .nil)) .nil) = p := rfl

/-- `residueEncode` denotes to `BitVec.ofNat w a.val`. -/
theorem residueEncode_denote {p w : Nat} (a : ZMod p) :
    structDenote.denote (.residueEncode p w) (.cons a .nil) = BitVec.ofNat w a.val := rfl

/-- `residueDecode` denotes to `(b.toNat : ZMod p)`. -/
theorem residueDecode_denote {p w : Nat} (b : BitVec w) :
    structDenote.denote (.residueDecode p w) (.cons b .nil) = (b.toNat : ZMod p) := rfl

/-- **Bitcast round-trip at the denotation level (decode ∘ encode).** Under
    `p ≤ 2^w`, `⟦decode⟧ (⟦encode⟧ a) = a`. -/
theorem residueDecode_denote_residueEncode_denote {p w : Nat} [NeZero p]
    (a : ZMod p) (hp : p ≤ 2 ^ w) :
    structDenote.denote (.residueDecode p w)
        (.cons (structDenote.denote (.residueEncode p w) (.cons a .nil)) .nil) = a :=
  residueDecode_residueEncode a hp

/-- **Bitcast round-trip at the denotation level (encode ∘ decode).** Under
    `b.toNat < p`, `⟦encode⟧ (⟦decode⟧ b) = b`. -/
theorem residueEncode_denote_residueDecode_denote {p w : Nat} [NeZero p]
    (b : BitVec w) (hb : b.toNat < p) :
    structDenote.denote (.residueEncode p w)
        (.cons (structDenote.denote (.residueDecode p w) (.cons b .nil)) .nil) = b :=
  residueEncode_residueDecode b hb

/-! ## 9. Constant-time predicate (the dialect's CT instance)

Every op is a data-oblivious reinterpret: `to_tensor`/`from_tensor` relabel the
same vector, and the bitcast is a fixed-width bit copy.  No `ite` on data, no
data-dependent index, so `ctSafe` is `true` for every op — exactly the
`FieldDerivedOps`/`PolyDialect` story (and unlike `cmpDialect`'s equality
tests, these never branch on a secret value). -/

/-- Per-op CT predicate: every reinterpret op is constant-time. -/
def StructOp.ctSafe : StructOp → Bool
  | _ => true

@[simp] theorem StructOp.ctSafe_all (op : StructOp) : op.ctSafe = true := rfl

/-- Per-expression CT predicate. -/
def ctSafeExpr {Γ : Ctxt structDialect} {t : StructTy}
    (e : Expr structDialect Γ t) : Bool :=
  e.op.ctSafe

@[simp] theorem ctSafeExpr_true {Γ : Ctxt structDialect} {t : StructTy}
    (e : Expr structDialect Γ t) : ctSafeExpr e = true := rfl

/-- Per-program CT predicate: a `Com` is CT-safe iff every let-bound expression
    is.  Since every op is CT, this is identically `true`. -/
def ctSafeCom {Γ : Ctxt structDialect} {t : StructTy} :
    Com structDialect Γ t → Bool
  | .ret _ => true
  | .var e body => ctSafeExpr e && ctSafeCom body

/-- **CT by construction.**  Every structural-ops program is constant-time: a
    reinterpret introduces no data-dependent control flow or memory index. -/
theorem ctSafeCom_all {Γ : Ctxt structDialect} {t : StructTy}
    (c : Com structDialect Γ t) : ctSafeCom c = true := by
  induction c with
  | ret _ => rfl
  | var e _ ih => simp [ctSafeCom, ctSafeExpr_true, ih]

/-- Propositional form, decidable. -/
def ctSafePropCom {Γ : Ctxt structDialect} {t : StructTy}
    (c : Com structDialect Γ t) : Prop :=
  ctSafeCom c = true

instance {Γ : Ctxt structDialect} {t : StructTy}
    (c : Com structDialect Γ t) : Decidable (ctSafePropCom c) := by
  unfold ctSafePropCom; infer_instance

/-! ## 10. Smoke tests

Two one-op `Com structDialect` programs exercising each reinterpret. -/

/-- One-op smoke program: `poly.to_tensor` over `[poly 7 4]`. -/
def smokeTensorProg : Com structDialect [.poly 7 4] (.tensor 7 4) :=
  .var (.mk (.polyToTensor 7 4) rfl (.cons .here .nil))
    (.ret .here)

/-- The `to_tensor` smoke program is the identity on the coefficient vector. -/
example (t : Fin 4 → ZMod 7) : smokeTensorProg.denote (.cons t .nil) = t := rfl

/-- One-op smoke program: `field.bitcast` encode over `[residue 7]`, width 8. -/
def smokeEncodeProg : Com structDialect [.residue 7] (.bits 8) :=
  .var (.mk (.residueEncode 7 8) rfl (.cons .here .nil))
    (.ret .here)

/-- The bitcast-encode smoke program: residue `3 : ZMod 7` encodes to the
    8-bit storage `BitVec.ofNat 8 3`. -/
example : smokeEncodeProg.denote (.cons (3 : ZMod 7) .nil) = BitVec.ofNat 8 3 := by
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.PrimeIrStructuralOps
