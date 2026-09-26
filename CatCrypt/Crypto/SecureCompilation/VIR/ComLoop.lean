/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Core
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-!
# A runtime-trip loop layer over any dialect

`ComLoop d` is the `scf.for`-with-`iter_args` layer over the straight-line
programs `Com d` of a dialect `d`: straight-line blocks, let-bindings, and a
counted loop `forRt` whose trip count is a variable read at run time, carrying one
loop-carried value through a straight-line body. The loop result is bound for the
continuation.

The trip counter has the dialect's word type `HasWord64.word`; `HasWord64` also
reads a counter value as a `Nat` and embeds a trip index into the word type. The
loop body runs over the context `acc :: word :: invTys`: the accumulator, the trip
index, and the invariants. `ComLoop.denote` folds the body over
`List.range (count).toNat`, the denotation of `ComL.forLoopNRt` in
`VIR/JasminLprogExport/ExportLoops.lean`.

`ComR` (`VIR/Regions.lean`) is the sibling layer carrying a two-armed branch;
`HasWord64` follows its `HasBitType`/`HasBoolBit` pattern.

## Main definitions

* `HasWord64` — the dialect's trip-counter type and its `Nat` readings.
* `ComLoop` — straight-line blocks, let-bindings and runtime-trip loops.
* `ComLoop.forRtFold` — the trip-count fold of a loop body.
* `ComLoop.denote` — the denotation.

## Main results

* `ComLoop.denote_block`, `ComLoop.denote_var`, `ComLoop.denote_forRt` — the
  equations of `denote`.
* `ComLoop.forRtFold_zero`, `ComLoop.forRtFold_succ` — the fold at zero trips and
  at one more trip.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR

open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (catCryptDialect)

/-! ## 1. The trip-counter type -/

/-- A dialect with a designated 64-bit word type `word`, used as the trip counter
    of a runtime-trip loop, with the reading `toNat` of a counter value and the
    embedding `ofNat` of a trip index. -/
class HasWord64 (d : Dialect.{0, 0}) [TyDenote d.Ty] where
  /-- The dialect's 64-bit word type. -/
  word : d.Ty
  /-- The trip count a counter value denotes. -/
  toNat : ⟦word⟧ → Nat
  /-- The counter value of a trip index. -/
  ofNat : Nat → ⟦word⟧

/-- The trip counter of `catCryptDialect` is `CryptoTy.sword 64`. -/
instance : HasWord64 catCryptDialect where
  word := CryptoTy.sword 64
  toNat := BitVec.toNat
  ofNat := BitVec.ofNat 64

/-! ## 2. `ComLoop` -/

/-- Programs of a dialect `d` with runtime-trip loops.

    * `block c` — a straight-line program `c`.
    * `var e k` — let-bind `e` and continue with `k`.
    * `forRt count init invs body k` — run `body` `count` times from the seed
      `init`, then continue with `k`, the final accumulator bound at `.here`.
      `body` is straight-line over `acc :: word :: invTys` (accumulator, trip index,
      invariants), and `invs` are the in-scope variables the invariants read. -/
inductive ComLoop (d : Dialect.{0, 0}) [DialectSignature d] [TyDenote d.Ty] [HasWord64 d] :
    Ctxt d → d.Ty → Type _ where
  /-- A straight-line program. -/
  | block {Γ t} (c : Com d Γ t) : ComLoop d Γ t
  /-- Let-bind an expression and continue with its result in scope. -/
  | var {Γ t s} (e : Expr d Γ t) (k : ComLoop d (t :: Γ) s) : ComLoop d Γ s
  /-- A runtime-trip loop carrying one value, with the final value bound for `k`. -/
  | forRt {Γ acc s} {invTys : Ctxt d} (count : Ctxt.Var Γ (HasWord64.word (d := d)))
      (init : Ctxt.Var Γ acc) (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
      (body : Com d (acc :: HasWord64.word (d := d) :: invTys) acc)
      (k : ComLoop d (acc :: Γ) s) : ComLoop d Γ s

namespace ComLoop

variable {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [DialectDenote d]
  [HasWord64 d]

/-- The `n`-trip fold of a loop body from the accumulator `a`: trip `t` runs `body`
    on the accumulator, the index `HasWord64.ofNat t`, and the invariant values
    `invs`. -/
def forRtFold {acc : d.Ty} {invTys : Ctxt d}
    (body : Com d (acc :: HasWord64.word (d := d) :: invTys) acc)
    (invs : Ctxt.Valuation invTys) (n : Nat) (a : ⟦acc⟧) : ⟦acc⟧ :=
  (List.range n).foldl
    (fun x t => body.denote (.cons x (.cons (HasWord64.ofNat (d := d) t) invs))) a

/-- Denotation of a `ComLoop`: a block by `Com.denote`, a loop by `forRtFold` at the
    trip count `HasWord64.toNat` reads from `count`. -/
def denote : {Γ : Ctxt d} → {t : d.Ty} → ComLoop d Γ t → Ctxt.Valuation Γ → ⟦t⟧
  | _, _, .block c, V => c.denote V
  | _, _, .var e k, V => k.denote (V.extend (e.denote V))
  | _, _, .forRt count init invs body k, V =>
      k.denote (V.extend
        (forRtFold body (Expr.lookupArgs invs V) (HasWord64.toNat (d := d) (count.lookup V))
          (init.lookup V)))

/-- A block denotes its straight-line program. -/
theorem denote_block {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (V : Ctxt.Valuation Γ) :
    (ComLoop.block c).denote V = c.denote V := rfl

/-- A let-binding denotes its continuation at the extended valuation. -/
theorem denote_var {Γ : Ctxt d} {t s : d.Ty} (e : Expr d Γ t) (k : ComLoop d (t :: Γ) s)
    (V : Ctxt.Valuation Γ) :
    (ComLoop.var e k).denote V = k.denote (V.extend (e.denote V)) := rfl

/-- A loop denotes its continuation at the valuation extended with the trip fold. -/
theorem denote_forRt {Γ : Ctxt d} {acc s : d.Ty} {invTys : Ctxt d}
    (count : Ctxt.Var Γ (HasWord64.word (d := d))) (init : Ctxt.Var Γ acc)
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (body : Com d (acc :: HasWord64.word (d := d) :: invTys) acc)
    (k : ComLoop d (acc :: Γ) s) (V : Ctxt.Valuation Γ) :
    (ComLoop.forRt count init invs body k).denote V =
      k.denote (V.extend
        (forRtFold body (Expr.lookupArgs invs V) (HasWord64.toNat (d := d) (count.lookup V))
          (init.lookup V))) := rfl

/-- Zero trips leave the accumulator unchanged. -/
theorem forRtFold_zero {acc : d.Ty} {invTys : Ctxt d}
    (body : Com d (acc :: HasWord64.word (d := d) :: invTys) acc)
    (invs : Ctxt.Valuation invTys) (a : ⟦acc⟧) :
    forRtFold body invs 0 a = a := rfl

/-- Trip `n` runs the body on the accumulator after the first `n` trips. -/
theorem forRtFold_succ {acc : d.Ty} {invTys : Ctxt d}
    (body : Com d (acc :: HasWord64.word (d := d) :: invTys) acc)
    (invs : Ctxt.Valuation invTys) (n : Nat) (a : ⟦acc⟧) :
    forRtFold body invs (n + 1) a =
      body.denote (.cons (forRtFold body invs n a) (.cons (HasWord64.ofNat (d := d) n) invs)) := by
  simp only [forRtFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

end ComLoop

end CatCrypt.Crypto.SecureCompilation.VIR
