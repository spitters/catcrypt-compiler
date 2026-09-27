/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Core
public import CatCrypt.Crypto.SecureCompilation.VIR.CoreM
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.QuantumDialect
public import CatCrypt.Crypto.Jasmin.LowCTTypes

/-!
# Region-extended VIR programs

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

VIR's `Com` (see `Core.lean`) is straight-line: it has only `ret` and `var`.
That suffices for `select`-style conditionals (where both arms are values,
not nested sub-programs), but it can't model

1. a crypto-SSA conditional as *real* nested branches (`catCryptDialect`'s
   `.ite` op is a non-region select over two values), or
2. the quantum island's `QSProg.ifBit` (its QSSA-to-VIR lowering, outside this
   package, defers it because there is no region construct).

This module defines an additive region wrapper `ComR` that extends `Com` with a
single nested-branch constructor `ifBit cond lvl thenBr elseBr`. The
`lvl : SecretLevel` is a *caller-asserted* tag — the CT predicate uses it
to decide whether the branch is constant-time-safe.

## Design choices

* **Additive wrapper, not modification.** `Com` is unchanged; `ComR` is a
  separate inductive with `var`, `ret`, and `ifBit`. Every existing
  theorem about `Com` remains valid.

* **Bit type parameterised via `HasBitType d`.** Different dialects (here,
  `CatCryptDialect` and `quantumDialect`) have different bit types. A
  one-method typeclass `HasBitType` exposes the chosen bit type. Instances
  for both dialects are provided.

* **`SecretLevel` on the conditional**, not the bit variable. The tag is
  caller-asserted: the constructor expects the caller to know whether
  the scrutinee's value flow is public or secret. This keeps the
  bit-type clean and avoids re-encoding flow on every dialect's type
  alphabet (variable-level flow is tracked in `LowCT.lean`, a separate
  concern).

* **Translation `Com → ComR`** is total (structural). The reverse
  `ComR → Option Com` is partial (returns `none` on any `ifBit` node).

* **CT bridge** is in `CTPredicate.lean` (this module's sibling). We
  re-export the `ctSafeComR` predicate as a `Bool`-returning function
  so it composes with the existing `ctSafeCom`.

## Scope

* `ComR` is not wired into `CryptoToVIR.lean`.
* `QSProg.ifBit` is not translated into `ComR`.
* This is not an information-flow type system. The `SecretLevel` tag is
  caller-asserted; propagating it through ops is outside this module.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR

universe u v

open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (CatCryptOp catCryptDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.QuantumDialect (QOp QTy quantumDialect)
open CatCrypt.Crypto.Jasmin.LowCT (SecretLevel)

/-! ## 1. `HasBitType`: which dialect type denotes `Bool`?

Different dialects spell the "classical bit" differently. `CatCryptDialect`
uses `CryptoTy.bit`; `quantumDialect` uses `QTy.bit`. We expose a one-method
typeclass so the region constructor can reference whichever is appropriate. -/

/-- A dialect that has a designated "classical bit" type. The bit type
    should denote (via `TyDenote`) to `Bool`, though this file doesn't
    statically enforce that — the constructor only needs a representative
    `d.Ty`. -/
class HasBitType (d : Dialect) where
  /-- The dialect's chosen classical-bit type. -/
  bit : d.Ty

/-- `CatCryptDialect`'s bit type is `CryptoTy.bit`. -/
instance : HasBitType catCryptDialect where
  bit := CryptoTy.bit

/-- `quantumDialect`'s bit type is `QTy.bit`. -/
instance : HasBitType quantumDialect where
  bit := QTy.bit

/-! ## 2. `ComR`: region-extended programs

Three constructors:

* `ret v` — return a variable (same as `Com.ret`).
* `var e body` — let-binding (same as `Com.var`).
* `ifBit cond lvl thenBr elseBr` — branch on `cond : Var Γ bit`, with
  `lvl : SecretLevel` the caller-asserted secrecy level of `cond`'s value
  flow. Both branches return the same type and live in the same context
  as the conditional. -/

inductive ComR (d : Dialect) [DialectSignature d] [HasBitType d] :
    Ctxt d → d.Ty → Type _ where
  /-- Return a variable. -/
  | ret {Γ t} (v : Ctxt.Var Γ t) : ComR d Γ t
  /-- Let-bind an expression and continue. -/
  | var {Γ t s} (e : Expr d Γ t) (body : ComR d (t :: Γ) s) : ComR d Γ s
  /-- Branch on a classical bit, with each arm a nested `ComR`. The
      `SecretLevel` tag is caller-asserted information about whether the
      scrutinee value flow is public or secret. -/
  | ifBit {Γ t} (cond : Ctxt.Var Γ (HasBitType.bit (d := d)))
      (lvl : SecretLevel)
      (thenBr : ComR d Γ t) (elseBr : ComR d Γ t) : ComR d Γ t

/-! ## 3. Pure denotation prerequisite: bit type denotes to `Bool`

`HasBitType` tracks only the dialect type. To actually case-split on the
conditional value, we need that type to denote to `Bool`. This is the
`HasBoolBit` extension. -/

/-- A `HasBitType` instance whose bit type denotes to `Bool`. Used by
    `ComR.denote` to case-split on the conditional's value. -/
class HasBoolBit (d : Dialect) [TyDenote d.Ty] extends HasBitType d where
  /-- Convert the bit type's denotation to a `Bool`. -/
  toBool : ⟦HasBitType.bit (d := d)⟧ → Bool

/-- `CatCryptDialect`'s bit denotes to `Bool` already. -/
instance : HasBoolBit catCryptDialect where
  toBool := id

/-- `quantumDialect`'s bit denotes to `Bool` already. -/
instance : HasBoolBit quantumDialect where
  toBool := id

namespace ComR

/-! ## 4. Translation from `Com` to `ComR` (total)

Every straight-line `Com` lifts to a region-free `ComR`. This is a
structural recursion: `.ret → .ret`, `.var → .var` with the body lifted. -/

/-- Lift a `Com` into `ComR`. The result contains no `ifBit` nodes. -/
def ofCom {d : Dialect} [DialectSignature d] [HasBitType d] :
    {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → _root_.CatCrypt.Crypto.SecureCompilation.VIR.ComR d Γ t
  | _, _, .ret v => .ret v
  | _, _, .var e body => .var e (ofCom body)

/-! ## 5. Reverse translation `ComR → Option Com` (partial)

Returns `none` if the program contains any `ifBit` node, otherwise
strips the (region-free) skeleton back to a `Com`. -/

/-- Project a `ComR` back to a `Com`, failing if any `ifBit` is present. -/
def toCom? {d : Dialect} [DialectSignature d] [HasBitType d] :
    {Γ : Ctxt d} → {t : d.Ty} →
      _root_.CatCrypt.Crypto.SecureCompilation.VIR.ComR d Γ t →
      Option (Com d Γ t)
  | _, _, .ret v => some (.ret v)
  | _, _, .var e body => (toCom? body).map (Com.var e)
  | _, _, .ifBit _ _ _ _ => none

/-! ## 6. Round-trip: `toCom?` reverses `ofCom` on region-free programs -/

@[simp] theorem toCom?_ofCom {d : Dialect} [DialectSignature d] [HasBitType d] :
    ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t),
      (ofCom c).toCom? = some c
  | _, _, .ret _ => rfl
  | _, _, .var e body => by
      show (toCom? (ofCom body)).map (Com.var e) = some (Com.var e body)
      rw [toCom?_ofCom body]
      rfl

/-! ## 7. Pure denotation

When the program is region-free, denotation matches `Com.denote`. -/

/-- Pure denotation of a `ComR`. Branches on the conditional via
    `HasBoolBit.toBool`. -/
def denote {d : Dialect} [TyDenote d.Ty] [DialectSignature d]
    [DialectDenote d] [HasBoolBit d] :
    {Γ : Ctxt d} → {t : d.Ty} →
      _root_.CatCrypt.Crypto.SecureCompilation.VIR.ComR d Γ t →
      Ctxt.Valuation Γ → ⟦t⟧
  | _, _, .ret v, V => v.lookup V
  | _, _, .var e body, V => denote body (V.extend (e.denote V))
  | _, _, .ifBit cond _ thenBr elseBr, V =>
      if HasBoolBit.toBool (d := d) (cond.lookup V) then
        denote thenBr V
      else
        denote elseBr V

/-! ## 8. Monadic denotation

The monadic version threads the effect monad `M` through nested `ComR`s. -/

/-- Monadic denotation of a `ComR`. -/
def denoteM {d : Dialect} {M : Type → Type} [Monad M] [TyDenote d.Ty]
    [DialectSignature d] [DialectDenoteM d M] [HasBoolBit d] :
    {Γ : Ctxt d} → {t : d.Ty} →
      _root_.CatCrypt.Crypto.SecureCompilation.VIR.ComR d Γ t →
      Ctxt.Valuation Γ → M ⟦t⟧
  | _, _, .ret v, V => pure (v.lookup V)
  | _, _, .var e body, V =>
      e.denoteM V >>= fun val => denoteM body (V.extend val)
  | _, _, .ifBit cond _ thenBr elseBr, V =>
      if HasBoolBit.toBool (d := d) (cond.lookup V) then
        denoteM thenBr V
      else
        denoteM elseBr V

/-! ## 9. Compatibility with `Com.denote`

For region-free programs (those produced by `ofCom`), `ComR.denote`
agrees with `Com.denote`. -/

@[simp] theorem denote_ofCom {d : Dialect} [TyDenote d.Ty]
    [DialectSignature d] [DialectDenote d] [HasBoolBit d] :
    ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (V : Ctxt.Valuation Γ),
      (ofCom c).denote V = c.denote V
  | _, _, .ret _, _ => rfl
  | _, _, .var e body, V =>
      denote_ofCom body (V.extend (e.denote V))

end ComR

end CatCrypt.Crypto.SecureCompilation.VIR
