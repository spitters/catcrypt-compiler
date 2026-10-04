/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProg
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# Structured programs over the Jasmin dialect

The instances that `NFProg` requires of a dialect, for `jasminDialect`:

* `HasWord64 jasminDialect`: the trip counter is the 64-bit register `JasminTy.reg 64`,
  denoting `BitVec 64`, read by `BitVec.toNat` and written by `BitVec.ofNat 64`.
* `HasBoolBit jasminDialect`: the branch bit is the 1-bit register `JasminTy.reg 1`,
  the result type of the comparison ops and the condition of `selectW`; it reads as
  `true` exactly at `1#1`, the reading `selectW` uses.

`DialectDenoteM jasminDialect Option` is `instDialectDenoteMOptionOfPure` over
`jasminDenote`, so `NFProg jasminDialect` has the denotation `NFProg.denote`.

## Main definitions

* `addConstLoop`: a counted loop that adds a constant to a carried word on each trip.

## Main results

* `foldlM_range_add`: a step that adds `c` to a one-word tuple, folded over
  `List.range m`, adds `m * c`.
* `addConstLoop_denote`: the denotation of `addConstLoop c` at every trip count, start
  value and fuel.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-- The trip counter of `jasminDialect` is the 64-bit register `reg 64`. -/
instance : HasWord64 jasminDialect where
  word := JasminTy.reg 64
  toNat := BitVec.toNat
  ofNat := BitVec.ofNat 64

/-- `jasminDialect` denotes calls in the empty environment. -/
instance : CallDenote jasminDialect := ⟨.empty⟩

/-- The branch bit of `jasminDialect` is the 1-bit register `reg 1`, read as `true`
    exactly at `1#1`. -/
instance : HasBoolBit jasminDialect where
  bit := JasminTy.reg 1
  toBool := fun (b : BitVec 1) => decide (b = 1#1)

/-- The counted loop that adds the constant `c` to a carried word once per trip. The
    context is `[n, x]`: the trip count `n` and the start value `x`, both `reg 64`.
    The body binds `c` with `regConst` and adds it to the carried word with
    `regArith .add`. -/
def addConstLoop (c : Nat) :
    NFProg jasminDialect [JasminTy.reg 64, JasminTy.reg 64] [JasminTy.reg 64] :=
  let body : NFProg jasminDialect
      [JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64]
      [JasminTy.reg 64] :=
    .var ⟨JasminOp.regConst 64 c, rfl, .nil⟩
      (.var ⟨JasminOp.regArith .add 64, rfl, .cons (.there .here) (.cons .here .nil)⟩
        (.ret (.cons .here .nil)))
  let k : NFProg jasminDialect [JasminTy.reg 64, JasminTy.reg 64, JasminTy.reg 64]
      [JasminTy.reg 64] := .ret (.cons .here .nil)
  NFProg.forLoop (d := jasminDialect) (cs := [JasminTy.reg 64])
    (Γ := [JasminTy.reg 64, JasminTy.reg 64])
    .here (.cons (.there .here) .nil) body k

/-- Folding over `m` indices a step `f` that adds `c` to a carried one-word tuple adds
    `m` copies of `c`. -/
theorem foldlM_range_add (c : BitVec 64)
    (f : Ctxt.Valuation (d := jasminDialect) [JasminTy.reg 64] → Nat →
      Option (Ctxt.Valuation (d := jasminDialect) [JasminTy.reg 64]))
    (hf : ∀ (x : BitVec 64) (i : Nat), f (.cons x .nil) i = some (.cons (x + c) .nil)) :
    (m : Nat) → (x : BitVec 64) →
    (List.range m).foldlM f (.cons x .nil) = some (.cons (x + BitVec.ofNat 64 m * c) .nil)
  | 0, x => by simp
  | m + 1, x => by
      rw [List.range_succ, List.foldlM_append, foldlM_range_add c f hf m x]
      simp only [Option.bind_eq_bind, Option.bind_some, List.foldlM_cons, List.foldlM_nil, hf]
      show some _ = some _
      rw [BitVec.ofNat_add, BitVec.add_mul, BitVec.add_assoc]
      simp

/-- `addConstLoop c` at the trip count `n` and the start value `x` returns
    `x + n * c` in `BitVec 64`, at every fuel. -/
theorem addConstLoop_denote (c : Nat) (n x : BitVec 64) (fuel : Nat) :
    (addConstLoop c).denote fuel (.cons n (.cons x .nil)) =
      some (.cons (x + n * BitVec.ofNat 64 c) .nil) := by
  rw [addConstLoop, NFProg.denote_forLoop]
  erw [foldlM_range_add (BitVec.ofNat 64 c) _ (fun x i => rfl)]
  show some (HVector.cons (f := fun t => ⟦t⟧) (t := JasminTy.reg 64)
    (x + BitVec.ofNat 64 n.toNat * BitVec.ofNat 64 c) .nil) = _
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

end CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin
