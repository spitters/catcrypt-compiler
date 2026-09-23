/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Core.Code
public import CatCrypt.Crypto.SDist
public import CatCrypt.Crypto.CryptoWord

/-!
# CryptoSSA: the typed substrate for cryptographic compilation

The intrinsically-typed De Bruijn substrate shared by the MLIR-aligned crypto
SSA dialect (`catCryptDialect`) and the extraction/runtime layers built on it.

The design mirrors lean-mlir's `Dialect { Op, Ty, m }` and `Com` structure
(opencompl): types are `CryptoTy`, contexts are De Bruijn lists, variables are
intrinsically-typed `CVar`, and valuations are heterogeneous `HVec`.

## Substrate

```
CryptoTy   ─── types (bit, unit, pair, sum, sword n, memref n)
Ctx        ─── typing contexts (De Bruijn, like lean-mlir's `Ctxt`)
CVar       ─── intrinsically-typed De Bruijn variables
HVec       ─── heterogeneous valuation (typed environment)
CHVector   ─── heterogeneous vector indexed by a `List CryptoTy`
```

The crypto SSA IR proper is `catCryptDialect` (a `VIR.Dialect` over the `Com`
framework, in `VIR/CatCryptDialect.lean`), whose `SPComp` interpretation
`Com.denoteSP` and observational-distance pseudometric `comSdist`
(`Dialects/CryptoDialectSecurity.lean`) live on top of this substrate. New
crypto SSA is expressed over `catCryptDialect` (`Com catCryptDialect`) and
lowered via `DialectToJasminCom.cryptoDialectToJasminCom`.

## References

* lean-mlir (opencompl): `Dialect`, `Com`, `PeepholeRewrite`
* Barthe et al., "Secure Compilation of Side-Channel Countermeasures", POPL 2025
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.CryptoSSA

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

set_option autoImplicit true -- SSA IR: many context/type variables

/-! ## Section 1: Type System -/

/-- Types in the CryptoSSA IR.

    Mirrors lean-mlir's `Ty` parameter for a `Dialect`. -/
inductive CryptoTy where
  /-- Single bit (Bool). Used for OTP message/key/ciphertext. -/
  | bit
  /-- Unit type. -/
  | unit
  /-- Product type. -/
  | pair (a b : CryptoTy)
  /-- Sum (coproduct) type. Used for UC output channels (out ⊕ leak). -/
  | sum (a b : CryptoTy)
  /-- Machine word (BitVec n). Bridges to Jasmin's `sword ws` via `WSize.bits`. -/
  | sword (n : Nat)
  /-- Fixed-size memref (array) of `sword 64` limbs. Used for tower/limb
      storage: a BLS12-381 Fp element is `memref 6` (6 × 64-bit limbs).
      Mirrors MLIR's `memref<n×i64>`. -/
  | memref (n : Nat)
  /-- Fixed-size memref (array) of `n` cells, each a `w`-bit word. Mirrors
      MLIR's `memref<n×iw>`. The `w = 64` cell width is `memref n`. -/
  | memrefW (w n : Nat)
  deriving DecidableEq, Repr

/-- Denotation of CryptoSSA types into Lean types.
    `@[reducible]` so type class resolution can see through it (needed for BitVec ops). -/
@[reducible] def CryptoTy.denote : CryptoTy → Type
  | .bit => Bool
  | .unit => Unit
  | .pair a b => a.denote × b.denote
  | .sum a b => a.denote ⊕ b.denote
  | .sword n => BitVec n
  | .memref n => Fin n → BitVec 64
  | .memrefW w n => Fin n → BitVec w

instance : Nonempty CryptoTy.bit.denote := ⟨false⟩
instance : Nonempty CryptoTy.unit.denote := ⟨()⟩
instance {a b : CryptoTy} [Nonempty a.denote] [Nonempty b.denote] :
    Nonempty (CryptoTy.pair a b).denote :=
  ⟨(Classical.arbitrary _, Classical.arbitrary _)⟩
instance {a : CryptoTy} [Nonempty a.denote] {b : CryptoTy} :
    Nonempty (CryptoTy.sum a b).denote := ⟨.inl (Classical.arbitrary _)⟩
instance {n : Nat} : Nonempty (CryptoTy.sword n).denote := ⟨0⟩
instance {n : Nat} : Nonempty (CryptoTy.memref n).denote := ⟨fun _ => 0⟩
instance {w n : Nat} : Nonempty (CryptoTy.memrefW w n).denote := ⟨fun _ => 0⟩

/-- Recursive default witness for `CryptoTy.denote`. -/
def CryptoTy.default : (t : CryptoTy) → t.denote
  | .bit => false
  | .unit => ()
  | .pair a b => (default a, default b)
  | .sum a _ => Sum.inl (default a)
  | .sword _ => 0
  | .memref _ => fun _ => 0
  | .memrefW _ _ => fun _ => 0

instance {t : CryptoTy} : Nonempty t.denote := ⟨CryptoTy.default t⟩

/-! ## Section 2: Typing Contexts and Variables -/

/-- Typing context: a list of CryptoSSA types (De Bruijn, like lean-mlir's `Ctxt`). -/
abbrev Ctx := List CryptoTy

/-- Intrinsically-typed De Bruijn variable reference.

    `CVar Γ t` witnesses that type `t` appears at a specific position in `Γ`. -/
inductive CVar : Ctx → CryptoTy → Type where
  /-- The most recently bound variable. -/
  | here {Γ : Ctx} {t : CryptoTy} : CVar (t :: Γ) t
  /-- A variable bound earlier (shift by one). -/
  | there {Γ : Ctx} {s t : CryptoTy} : CVar Γ t → CVar (s :: Γ) t

/-- Boolean equality on CVar (De Bruijn index comparison). -/
def CVar.beq : CVar Γ t → CVar Γ t → Bool
  | .here, .here => true
  | .here, .there _ => false
  | .there _, .here => false
  | .there a, .there b => CVar.beq a b

theorem CVar.beq_eq_true_iff (a b : CVar Γ t) : a.beq b = true ↔ a = b := by
  induction a with
  | here => cases b <;> simp [beq]
  | there _ ih => cases b with
    | here => simp [beq]
    | there b => simp [beq, ih b]

instance : BEq (CVar Γ t) := ⟨CVar.beq⟩

instance : DecidableEq (CVar Γ t) :=
  fun a b => decidable_of_iff _ (CVar.beq_eq_true_iff a b)

/-! ## Section 3: Heterogeneous Valuation -/

/-- Heterogeneous vector of typed values, one per context entry.

    `HVec Γ` assigns a value of type `t.denote` to each entry `t` in `Γ`. -/
inductive HVec : Ctx → Type where
  /-- Empty valuation for empty context. -/
  | nil : HVec []
  /-- Extend valuation with a new value. -/
  | cons {Γ : Ctx} {t : CryptoTy} : t.denote → HVec Γ → HVec (t :: Γ)

/-- Look up the value of a variable in a valuation. -/
def CVar.lookup : CVar Γ t → HVec Γ → t.denote
  | .here, .cons v _ => v
  | .there x, .cons _ vs => x.lookup vs

/-- Extend a valuation with a new value at the head. -/
def HVec.extend (V : HVec Γ) (val : t.denote) : HVec (t :: Γ) :=
  .cons val V

/-! ## Section 3b: Heterogeneous Vector (typed)

Generic heterogeneous vector indexed by a `List CryptoTy`, with a per-element
type function `f`. Structurally identical to `VIR.HVector` so the translation
to VIR `Expr` is a trivial map (no list-vs-HVector shape mismatch).

Introduced 2026-05-14 as part of the `extCall` HVector refactor. -/

/-- A heterogeneous list of items indexed by `List CryptoTy`, with a per-tag
    type function. -/
inductive CHVector (f : CryptoTy → Type) : List CryptoTy → Type where
  | nil : CHVector f []
  | cons {t : CryptoTy} {ts : List CryptoTy} :
      f t → CHVector f ts → CHVector f (t :: ts)

namespace CHVector

/-- Map a CHVector pointwise. -/
def map {f g : CryptoTy → Type} (h : ∀ {t}, f t → g t) :
    {ts : List CryptoTy} → CHVector f ts → CHVector g ts
  | [], .nil => .nil
  | _ :: _, .cons x xs => .cons (h x) (map h xs)

end CHVector

/-- Convert a runtime-typed `List (Σ t, f t)` into a typed pair
    `(argTys, CHVector f argTys)`. The `argTys` is the projected first
    components in order. Used for migrating call sites that previously
    accumulated `List (Σ t : CryptoTy, CVar Γ t)`. -/
def listSigmaToCHVector {f : CryptoTy → Type} :
    (xs : List (Σ t : CryptoTy, f t)) →
    Σ argTys : List CryptoTy, CHVector f argTys
  | [] => ⟨[], .nil⟩
  | ⟨t, v⟩ :: rest =>
    match listSigmaToCHVector rest with
    | ⟨ts, hv⟩ => ⟨t :: ts, .cons v hv⟩

/-! ## Section 4: XOR Bijection (Key for OTP) -/

/-- XOR with a fixed Bool is a bijection.
    This is the core argument for OTP security. -/
def xorBij (m : Bool) : Bool ≃ Bool where
  toFun k := xor k m
  invFun c := xor c m
  left_inv k := by cases k <;> cases m <;> rfl
  right_inv c := by cases c <;> cases m <;> rfl

/-- Sampling a bit and XORing with a constant has the same distribution
    as sampling directly. This lifts the bijection to SPComp. -/
theorem sample_xor_eq_sample (m : Bool) :
    SPComp.bind (SPComp.sample Bool) (fun k => SPComp.pure (Bool.xor k m)) =
    SPComp.bind (SPComp.sample Bool) (fun c => SPComp.pure c) := by
  have : (fun k => SPComp.pure (Bool.xor k m)) = (fun k => (SPComp.pure ∘ (xorBij m)) k) := rfl
  rw [this, show SPComp.pure ∘ (xorBij m) = fun k => SPComp.pure (id ((xorBij m) k)) from rfl]
  rw [SPComp.sample_bind_pure_equiv (xorBij m) id]
  simp [id]

/-- More general version: sampling and XOR-then-f equals sampling and f. -/
theorem sample_xor_bind_eq (m : Bool) (k : Bool → SPComp γ) :
    SPComp.bind (SPComp.sample Bool) (fun b => k (Bool.xor b m)) =
    SPComp.bind (SPComp.sample Bool) k :=
  SPComp.sample_bind_equiv (xorBij m) k

end CatCrypt.Crypto.SecureCompilation.CryptoSSA
