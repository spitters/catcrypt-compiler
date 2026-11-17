/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.Reify

/-!
# `reifyAeneas%`: pure bitwise operations and shifts by an amount of another width

The Aeneas Lean backend of hax 0.4.2 prints a pure bitwise operation of unsigned words as a
value `ok (x &&& y)`, `ok (x ||| y)`, `ok (x ^^^ y)`, and a shift as the checked operation
`x >>> s`, `x <<< s` of `RustM`, whose amount `s` is a word of any unsigned width (a `usize`
for a Rust shift by `usize`). This module gives the `ReifyE` instances of these forms, which
`reifyAeneas%` finds by instance resolution:

* `ok (x op y)` for the three bitwise operations at a width of the table: the instances
  `reifyE_band`, `reifyE_bor`, `reifyE_bxor` of `AeneasFront.Reify` at `RustM.ok`, since
  `lift` is `RustM.ok`;
* `x >>> s` and `x <<< s` with `x` at a width of the table and `s` at any width of at most
  `64` bits: the call `Shr#t` or `Shl#t` of the table at the two words. A value of the Aeneas
  shift has an amount below the width of `x`, so the table reads the amount at the width of `x`
  with the same value (`aeCall2_shift`);
* a literal shift amount, bound first by `Reify.bindLit` and `Reify.okLit` (`LitOf`).

## Main results

* `aeCall2_shift`: the reading of the table's shift call at an amount of another width
* `reifyE_shr`, `reifyE_shl`: the shifts
* `reifyE_band_ok`, `reifyE_bor_ok`, `reifyE_bxor_ok`: the bitwise values
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open Aeneas.Std
open CatCrypt.Hax.RustSemantics
open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open Ctxt (Var Valuation)

/-! ## Bitwise values -/

/-- The bitwise and `ok (x &&& y)` of the backend output: `reifyE_band`. -/
instance reifyE_band_ok {ty : UScalarTy} [TableTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [Lookup V (embW x) va] [Lookup V (embW y) vb] :
    ReifyE (RustM.ok (x &&& y)) V (callE2 (opName .band ++ uTag ty) (.word 64) va vb) :=
  reifyE_band x y V

/-- The bitwise or `ok (x ||| y)` of the backend output: `reifyE_bor`. -/
instance reifyE_bor_ok {ty : UScalarTy} [TableTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [Lookup V (embW x) va] [Lookup V (embW y) vb] :
    ReifyE (RustM.ok (x ||| y)) V (callE2 (opName .bor ++ uTag ty) (.word 64) va vb) :=
  reifyE_bor x y V

/-- The bitwise xor `ok (x ^^^ y)` of the backend output: `reifyE_bxor`. -/
instance reifyE_bxor_ok {ty : UScalarTy} [TableTy ty] [Le64 ty] {Γ : Ctxt nfDialect}
    (x y : UScalar ty) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [Lookup V (embW x) va] [Lookup V (embW y) vb] :
    ReifyE (RustM.ok (x ^^^ y)) V (callE2 (opName .bxor ++ uTag ty) (.word 64) va vb) :=
  reifyE_bxor x y V

/-! ## Shifts -/

/-- A word whose value is below `2 ^ w` for the width `w` of `ty` is read at `ty` with its
    value. -/
theorem readW_wordV_of_lt {ty tys : UScalarTy} (s : UScalar tys) (hs : s.val < 2 ^ ty.numBits) :
    readW ty (wordV s) = .ok ⟨BitVec.ofNat _ s.val⟩ := by
  change litA ty (s.val : Int) = _
  exact litA_ofNat hs

/-- The word of `ty` read from an amount below `2 ^ w` has the value of the amount. -/
theorem val_ofNat_amount {ty tys : UScalarTy} (s : UScalar tys) (hs : s.val < 2 ^ ty.numBits) :
    (⟨BitVec.ofNat _ s.val⟩ : UScalar ty).val = s.val := by
  simp only [UScalar.val, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hs

/-- **The table's shift call at an amount of another width.** At a width of the table, the
    reading of `Shr#t` or `Shl#t` at a word and an amount below `2 ^ w` is the Aeneas shift by the
    amount read at the width of the word. -/
theorem aeCall2_shift {ty tys : UScalarTy} [h : TableTy ty] {o : WordOp}
    (ho : o = .shr ∨ o = .shl) (x : UScalar ty) (s : UScalar tys)
    (hs : s.val < 2 ^ ty.numBits) :
    aeCall2 (opName o ++ uTag ty) (wordV x) (wordV s) =
      (o.aen x ⟨BitVec.ofNat _ s.val⟩ >>= fun z => .ok (wordV z)) := by
  have hn : wordOpAt? (opName o ++ uTag ty) = some (ty, o) := by
    rcases ho with rfl | rfl <;> cases ty <;> decide +kernel
  have hw : wordAt ty o = true := by simp [wordAt, h.table]
  unfold aeCall2
  rw [hn]
  simp only [hw, ite_true, readW_wordV, readW_wordV_of_lt s hs, bind_tc_ok]

/-- A value of the Aeneas right shift has an amount below the width. -/
theorem shr_amount_lt {ty tys : UScalarTy} {x z : UScalar ty} {s : UScalar tys}
    (hz : x >>> s = .ok z) : s.val < ty.numBits := by
  change UScalar.shiftRight x s.val = _ at hz
  unfold UScalar.shiftRight at hz
  split at hz
  · assumption
  · cases hz

/-- A value of the Aeneas left shift has an amount below the width. -/
theorem shl_amount_lt {ty tys : UScalarTy} {x z : UScalar ty} {s : UScalar tys}
    (hz : x <<< s = .ok z) : s.val < ty.numBits := by
  change UScalar.shiftLeft x s.val = _ at hz
  unfold UScalar.shiftLeft at hz
  split at hz
  · assumption
  · cases hz

/-- **A right shift** `x >>> s` of a word of a width of the table by an amount of any width of
    at most `64` bits: the call `Shr#t` of the table. -/
instance reifyE_shr {ty tys : UScalarTy} [TableTy ty] [Le64 ty] [Le64 tys] {Γ : Ctxt nfDialect}
    (x : UScalar ty) (s : UScalar tys) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW x) va] [hs : Lookup V (embW s) vb] :
    ReifyE (x >>> s) V (callE2 (opName .shr ++ uTag ty) (.word 64) va vb) where
  sound z hz := by
    have hlt : s.val < 2 ^ ty.numBits :=
      lt_of_lt_of_le (shr_amount_lt hz) (Nat.lt_two_pow_self).le
    have he : WordOp.aen .shr x ⟨BitVec.ofNat _ s.val⟩ = x >>> s := by
      change UScalar.shiftRight x _ = UScalar.shiftRight x s.val
      rw [val_ofNat_amount s hlt]
    refine aeExpr_callE2 _ _ va vb V x s hx.eq hs.eq ?_ (dec_wordV z)
    rw [aeCall2_shift (.inl rfl) x s hlt, he, hz]
    rfl

/-- **A left shift** `x <<< s` of a word of a width of the table by an amount of any width of
    at most `64` bits: the call `Shl#t` of the table. -/
instance reifyE_shl {ty tys : UScalarTy} [TableTy ty] [Le64 ty] [Le64 tys] {Γ : Ctxt nfDialect}
    (x : UScalar ty) (s : UScalar tys) (V : Valuation Γ) {va vb : Var Γ (.word 64)}
    [hx : Lookup V (embW x) va] [hs : Lookup V (embW s) vb] :
    ReifyE (x <<< s) V (callE2 (opName .shl ++ uTag ty) (.word 64) va vb) where
  sound z hz := by
    have hlt : s.val < 2 ^ ty.numBits :=
      lt_of_lt_of_le (shl_amount_lt hz) (Nat.lt_two_pow_self).le
    have he : WordOp.aen .shl x ⟨BitVec.ofNat _ s.val⟩ = x <<< s := by
      change UScalar.shiftLeft x _ = UScalar.shiftLeft x s.val
      rw [val_ofNat_amount s hlt]
    refine aeExpr_callE2 _ _ va vb V x s hx.eq hs.eq ?_ (dec_wordV z)
    rw [aeCall2_shift (.inr rfl) x s hlt, he, hz]
    rfl

instance {ty tys : UScalarTy} (x : UScalar ty) (c : UScalar tys) : LitOf (x >>> c) tys c := ⟨⟩
instance {ty tys : UScalarTy} (x : UScalar ty) (c : UScalar tys) : LitOf (x <<< c) tys c := ⟨⟩

end CatCrypt.Crypto.SecureCompilation.AeneasFront
