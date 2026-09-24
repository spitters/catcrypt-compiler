/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom

/-!
# Value/type transports for the Jasmin lowering

The transports relating a CryptoSSA value to its `mapTy`-image type, used by the
dialect-native correctness file (`DialectToJasminComCorrect`).

## The per-value transport `ctTransTy`

`mapTy` does not in general make `⟦t⟧(CryptoSSA)` and `⟦mapTy t⟧(jasmin)`
*the same* Lean type — `⟦.bit⟧ = Bool` but `⟦mapTy .bit⟧ = ⟦.reg 1⟧ = BitVec 1`,
`⟦.unit⟧ = Unit` but `⟦.reg 0⟧ = BitVec 0`. We therefore make the transport
explicit as `ctTransTy : ⟦t⟧ → ⟦mapTy t⟧`, casing on `t`:

| `t`        | `⟦t⟧`             | `⟦mapTy t⟧`        | transport            |
|------------|-------------------|--------------------|----------------------|
| `sword w`  | `BitVec w`        | `BitVec w`         | identity             |
| `memref n` | `Fin n → BitVec64`| `Fin n → BitVec64` | identity             |
| `bit`      | `Bool`            | `BitVec 1`         | `BitVec.ofBool`      |
| `unit`     | `Unit`            | `BitVec 0`         | `default`            |
| `pair`/`sum`| `…`              | `BitVec 0`         | `default` (placeholder) |

On the `sword`/`memref` constructors `ctTransTy` *computes* to the identity.

These declarations live in the `CryptoToJasminComCorrect` namespace, which the
consumers open as `open … CryptoToJasminComCorrect (ctTransTy …)`;
`DialectToJasminComCorrect.lean` sources them from here.
-/

@[expose] public section

set_option autoImplicit true -- SSA IR front: many context/type variables

namespace CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Core

/-! ## The per-value transport `ctTransTy` -/

/-- Transport a CryptoSSA value to its `mapTy`-image type. Identity on the
    register/array forms (`sword`, `memref`), where source and target denote to
    the same Lean type; canonical/placeholder elsewhere. -/
def ctTransTy : {t : CryptoTy} → CryptoTy.denote t → ⟦mapTy t⟧
  | .sword _, v => v
  | .memref _, v => v
  | .memrefW _ _, v => v
  | .bit, v => BitVec.ofBool v
  | .unit, _ => JasminTy.default (.reg 0)
  | .pair _ _, _ => JasminTy.default (.reg 0)
  | .sum _ _, _ => JasminTy.default (.reg 0)

/-- On a concrete machine-word type, `ctTransTy` is the identity. -/
theorem ctTransTy_sword {w : Nat} (v : BitVec w) :
    ctTransTy (t := .sword w) v = v := rfl

/-- On a concrete memref type, `ctTransTy` is the identity. -/
theorem ctTransTy_memref {n : Nat} (v : Fin n → BitVec 64) :
    ctTransTy (t := .memref n) v = v := rfl

/-- On a width-carrying memref type, `ctTransTy` is the identity. -/
theorem ctTransTy_memrefW {w n : Nat} (v : Fin n → BitVec w) :
    ctTransTy (t := .memrefW w n) v = v := rfl

/-! ## Type-level default alignment -/

/-- **Type-level default alignment.** The `ctTransTy`-transport of the CryptoSSA
    canonical default equals the jasmin canonical default at the mapped type.
    Holds definitionally for each `CryptoTy`. -/
theorem ctTransTy_default {t : CryptoTy} :
    ctTransTy (CryptoTy.default t) = JasminTy.default (mapTy t) := by
  cases t <;> rfl

/-! ## `jasminExtSem` is the stub default on `mapTy`-produced shapes -/

/-- `jasminExtSem` on a `.reg w` return type is `JasminTy.default` for every
    leaf name and argument-type list: the only non-default `jasminExtSem`
    branches return a `.stackArr 16` type, so a `.reg w` return type falls
    through to the catch-all. -/
theorem jasminExtSem_reg (name : String) (w : Nat) (aT : List JasminTy)
    (a : HVector (fun t => ⟦t⟧) aT) :
    jasminExtSem name aT (.reg w) a = JasminTy.default (.reg w) := by
  cases aT <;> simp only [jasminExtSem]

/-- `jasminExtSem` on a `.stackArr 64 n` return type is `JasminTy.default`:
    the non-default branches all return a `.stackArr 16` type (width 16, not
    64), so a 64-bit array return type falls through to the catch-all. -/
theorem jasminExtSem_stackArr64 (name : String) (n : Nat) (aT : List JasminTy)
    (a : HVector (fun t => ⟦t⟧) aT) :
    jasminExtSem name aT (.stackArr 64 n) a = JasminTy.default (.stackArr 64 n) := by
  cases aT <;> simp only [jasminExtSem]

end CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect
