/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-!
# The constant-time leakage of `catCryptDialect`

The instance of `ComLevelCheck.LeakModel` for `catCryptDialect`:

* the dynamic-index memref accesses (`memrefGetDyn`, `memrefSetDyn`,
  `memrefGetDyn128`, `memrefWGetDyn`, `memrefWSetDyn`) leak their index argument
  (position `1`) as a memory offset;
* the opaque array leaves `extCall "arrLoadDyn"` / `extCall "arrStoreDyn"`, which
  the front emits for an array access outside the memref word ABI, leak their last
  argument, the index;
* a leaf call the model marks (`leafVT`) leaks its argument values;
* an operation the model maps to a variable-time instruction (`opVT`) leaks its
  argument values as that instruction's operands;
* every other operation is quiet: the static-index memref accesses address a
  constant offset, and `ite` is a select of values.

A value reads as a natural number by its bits (`sword`, `bit`) and as `0`
otherwise (`valNat`).

`catCT`, `catLevelCheck` and `catLevelCheck_sound` are the constant-time
predicate, the level checker and its soundness at this model.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.CT (X86Mnem)

/-- The parameters of the dialect leakage: the leaf calls classed variable time
    and the operations lowered to a variable-time instruction. -/
structure CatLeakParams where
  leafVT : String → Bool := fun _ => false
  opVT : CatCryptOp → Option X86Mnem := fun _ => none

/-- The parameters of the owned x86 route: no variable-time leaf and no operation
    lowered to a variable-time instruction. -/
def CatLeakParams.owned : CatLeakParams := {}

/-- The event class of an operation. -/
def catKind (P : CatLeakParams) (op : CatCryptOp) : LeakKind :=
  match op with
  | .memrefGetDyn _ | .memrefSetDyn _ | .memrefGetDyn128 _
  | .memrefWGetDyn _ _ | .memrefWSetDyn _ _ => .addrAt 1
  | .extCall name argTys _ =>
      if P.leafVT name then .vtCall name
      else if name = "arrLoadDyn" ∨ name = "arrStoreDyn" then .addrAt (argTys.length - 1)
      else .quiet
  | op =>
      match P.opVT op with
      | some m => .vt m
      | none => .quiet

/-- The natural-number reading of a dialect value. -/
def catValNat : (t : CryptoTy) → ⟦t⟧ → Nat
  | .sword _, w => w.toNat
  | .bit, b => b.toNat
  | _, _ => 0

/-- The leakage model of `catCryptDialect` at the parameters `P`. -/
def catLeakModel (P : CatLeakParams) : LeakModel catCryptDialect where
  kind := catKind P
  valNat := catValNat

/-- Constant time of a `catCryptDialect` program for the entry labels `L`. -/
abbrev catCT (P : CatLeakParams) {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (L : Labels Γ) (c : Com catCryptDialect Γ t) : Prop :=
  ComCT (catLeakModel P) L c

/-- The level checker at the dialect leakage. -/
abbrev catLevelCheck (P : CatLeakParams) {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : Com catCryptDialect Γ t) (L : Labels Γ) : Bool :=
  Com.levelCheck (catLeakModel P) c L

/-- A program the checker accepts is constant time for its entry labels. -/
theorem catLevelCheck_sound (P : CatLeakParams) {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (c : Com catCryptDialect Γ t) (L : Labels Γ) (h : catLevelCheck P c L = true) :
    catCT P L c :=
  levelCheck_sound _ c L h

end CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectCTLeak
