/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithChain
public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.SingleWord
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFMapLeak
public import HaxLean.Semantics

/-!
# Limb templates of the `mod_arith` operations

A limb template `ModArithLimbTemplate p r` implements the `mod_arith` operations that the
lowering `FieldToModArithChain.fieldToModArithJ` emits for the methods of the prime-field
interface at the modulus `p` and the representation `r`, on `jasminDialect`. A residue of
`ZMod p` is carried by one value of the carrier type `ty` (a register, or an array of
limbs) through the encoding `enc`. The template gives, for each method `m`, the straight-line
body `body m` over the carriers of its arguments; its value is the encoding of the
`mod_arith` value `methodVal p r m` of the arguments, and its events are the same at every
two valuations at leakage parameters with no variable-time operation. It gives as well the
blocks `ofWords w n` and `toWords w n` of the word casts `fromWordsM p w n` and
`toWordsM p w n` of `jasMod`, with their values and fixed events.

The method index matches the tagged heads of the prime-field interface: squaring and
doubling have bodies of one argument, as the template blocks of these heads do.

`ofSingleWord F` is the template of a single-word representation
`FieldWord.SingleWordField p` with the canonical encoding at a modulus at most `2 ^ 64`:
the carrier is a 64-bit register, the bodies are the blocks of `F`, and the word casts at
one 64-bit word are the load and the store at index `0`.

## Main definitions

* `ModArithLimbTemplate.limbSig`, `ModArithLimbTemplate.limbVals`: the signature and the
  argument values of a method on carriers.
* `ModArithLimbTemplate.methodVal`: the `mod_arith` value of a method at a representation.
* `ModArithLimbTemplate.LeakFixed`: a straight-line program emits the same events at every
  two valuations.
* `ModArithLimbTemplate`: the class of limb templates.
* `ModArithLimbTemplate.singleBody`, `ModArithLimbTemplate.loadBlk`,
  `ModArithLimbTemplate.storeBlk`, `ModArithLimbTemplate.ofSingleWord`: the template of a
  single-word representation.

## Main results

* `ModArithLimbTemplate.methodVal_canon`: at `canon`, the value of a method is the
  operation of `ZMod p`.
* `ModArithLimbTemplate.leakFixed_rename`: renaming keeps fixed events.
* `ModArithLimbTemplate.loadBlk_denote`, `ModArithLimbTemplate.storeBlk_denote`: the word
  casts at one word.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Algebraic

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldChainDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldToModArithChain (radixParams)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (SingleWordField canonEnc w64)
open Ctxt (Var Valuation)
open _root_.Hax.FieldTag (FieldMethod)

namespace ModArithLimbTemplate

/-! ## 1. Methods on carriers -/

/-- The signature of a method on carriers of type `τ`: two carriers for a method with two
    arguments, one for a method with one. -/
def limbSig (τ : JasminTy) : FieldMethod → List JasminTy
  | .add | .sub | .mul => [τ, τ]
  | .neg | .square | .double => [τ]

/-- The argument values of a method on carriers: `a` then `b` for a method with two
    arguments, `a` for a method with one. The first argument is the newest variable. -/
def limbVals {τ : JasminTy} : (m : FieldMethod) → ⟦τ⟧ → ⟦τ⟧ →
    Valuation (d := jasminDialect) (limbSig τ m)
  | .add, a, b | .sub, a, b | .mul, a, b => .cons a (.cons b .nil)
  | .neg, a, _ | .square, a, _ | .double, a, _ => .cons a .nil

/-- **The `mod_arith` value of a method** at the representation `r` on stored residues, as
    `fieldToModArithJ` lowers it: addition, subtraction and negation are `modAdd`, `modSub`
    and `modNeg`, doubling is `modAdd` of the argument with itself; multiplication and
    squaring are `modMul` at `canon` and `montMul` with the radix inverse of
    `radixParams k` at `mont k`. -/
def methodVal (p : Nat) : FieldRepr → FieldMethod → ZMod p → ZMod p → ZMod p
  | _, .add, x, y => modAddF x y
  | _, .sub, x, y => modSubF x y
  | _, .neg, x, _ => modNegF x
  | _, .double, x, _ => modAddF x x
  | .canon, .mul, x, y => modMulF x y
  | .canon, .square, x, _ => modMulF x x
  | .mont k, .mul, x, y => montMulF ((radixParams k).rInv p) x y
  | .mont k, .square, x, _ => montMulF ((radixParams k).rInv p) x x

/-- At `canon` the value of a method is the operation of `ZMod p`. -/
theorem methodVal_canon {p : Nat} (m : FieldMethod) (x y : ZMod p) :
    methodVal p .canon m x y =
      match m with
      | .add => x + y
      | .sub => x - y
      | .mul => x * y
      | .neg => -x
      | .square => x * x
      | .double => x + x := by
  cases m <;> rfl

/-! ## 2. Fixed events -/

/-- A straight-line program of `jasminDialect` emits the same events at every two
    valuations under the leakage model `M`. -/
def LeakFixed (M : LeakModel jasminDialect) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) : Prop :=
  ∀ V₁ V₂ : Valuation Γ, ComLevelCheck.Com.ctLeak M c V₁ = ComLevelCheck.Com.ctLeak M c V₂

/-- A renamed program with fixed events has fixed events. -/
theorem leakFixed_rename (M : LeakModel jasminDialect) {Γ Γ' : Ctxt jasminDialect}
    {t : JasminTy} (h : Ctxt.Hom Γ Γ') {c : Com jasminDialect Γ t} (hc : LeakFixed M c) :
    LeakFixed M (Com.rename h c) := by
  intro V₁ V₂
  rw [NFProg.Com.ctLeak_rename_pullV, NFProg.Com.ctLeak_rename_pullV]
  exact hc _ _

end ModArithLimbTemplate

open ModArithLimbTemplate in
/-- **A limb template of the `mod_arith` operations** at the modulus `p` and the
    representation `r`: the limb count, the carrier type `ty` of a residue with its
    encoding `enc`, the body of each method with its value against `methodVal p r` and its
    fixed events, and the blocks of the word casts with their values and fixed events. The
    events are fixed at the leakage parameters of `jasminDialect` with no variable-time
    operation. -/
class ModArithLimbTemplate (p : Nat) (r : FieldRepr) : Type where
  /-- The number of limbs of a residue. -/
  limbs : Nat
  /-- The carrier type of a residue. -/
  ty : JasminTy
  /-- The carrier of a stored residue. -/
  enc : ZMod p → ⟦ty⟧
  /-- The body of a method on the carriers of its arguments. -/
  body : (m : FieldMethod) → Com jasminDialect (limbSig ty m) ty
  body_denote : ∀ (m : FieldMethod) (x y : ZMod p),
    (body m).denote (limbVals m (enc x) (enc y)) = enc (methodVal p r m x y)
  body_fixed : ∀ Pj : JLeakParams, (∀ op, Pj.opVT op = none) →
    ∀ m, LeakFixed (jLeakModel Pj) (body m)
  /-- The block of the cast `fromWordsM p w n`, when the template has one. -/
  ofWords : (w n : Nat) → Option (Com jasminDialect [.stackArr w n] ty)
  ofWords_denote : ∀ (w n : Nat) (c : Com jasminDialect [.stackArr w n] ty),
    ofWords w n = some c → ∀ (A : Fin n → BitVec w) (y : ZMod p),
      fromWordsMF p w n A = some y → c.denote (.cons A .nil) = enc y
  ofWords_fixed : ∀ Pj : JLeakParams, (∀ op, Pj.opVT op = none) →
    ∀ (w n : Nat) (c : Com jasminDialect [.stackArr w n] ty), ofWords w n = some c →
      LeakFixed (jLeakModel Pj) c
  /-- The block of the cast `toWordsM p w n`, when the template has one. -/
  toWords : (w n : Nat) → Option (Com jasminDialect [ty] (.stackArr w n))
  toWords_denote : ∀ (w n : Nat) (c : Com jasminDialect [ty] (.stackArr w n)),
    toWords w n = some c → ∀ y : ZMod p, c.denote (.cons (enc y) .nil) = toWordsMF p w n y
  toWords_fixed : ∀ Pj : JLeakParams, (∀ op, Pj.opVT op = none) →
    ∀ (w n : Nat) (c : Com jasminDialect [ty] (.stackArr w n)), toWords w n = some c →
      LeakFixed (jLeakModel Pj) c

namespace ModArithLimbTemplate

/-! ## 3. The template of a single-word representation -/

/-- The body of a method in a single-word representation `F`: the block of `F` for the
    operation of the method on the parameters; squaring is the multiplication block and
    doubling the addition block on the one parameter. -/
def singleBody {p : Nat} (F : SingleWordField p) :
    (m : FieldMethod) → Com jasminDialect (limbSig w64 m) w64
  | .add => F.addBlk .here (.there .here)
  | .sub => F.subBlk .here (.there .here)
  | .mul => F.mulBlk .here (.there .here)
  | .neg => F.negBlk .here
  | .square => F.mulBlk .here .here
  | .double => F.addBlk .here .here

/-- The body of a method in a single-word representation returns the encoding of the value
    at `canon`. -/
theorem singleBody_denote {p : Nat} (F : SingleWordField p) (m : FieldMethod) (x y : ZMod p) :
    (singleBody F m).denote (limbVals m (F.enc x) (F.enc y)) =
      F.enc (methodVal p .canon m x y) := by
  cases m
  · exact F.addBlk_denote _ _ _ x y rfl rfl
  · exact F.subBlk_denote _ _ _ x y rfl rfl
  · exact F.mulBlk_denote _ _ _ x y rfl rfl
  · exact F.negBlk_denote _ _ x rfl
  · exact F.mulBlk_denote _ _ _ x x rfl rfl
  · exact F.addBlk_denote _ _ _ x x rfl rfl

/-- The load of the word at index `0` of an array of one word. -/
def loadBlk : Com jasminDialect [.stackArr 64 1] w64 :=
  .var ⟨.regConst 64 0, rfl, .nil⟩ <|
    .var ⟨.stackLoad 64 1, rfl, .cons (.there .here) (.cons .here .nil)⟩ (.ret .here)

/-- The store of a word at index `0` of a fresh array of one word. -/
def storeBlk : Com jasminDialect [w64] (.stackArr 64 1) :=
  .var ⟨.stackZero 64 1, rfl, .nil⟩ <|
    .var ⟨.stackStoreImm 64 1 0, rfl, .cons .here (.cons (.there .here) .nil)⟩ (.ret .here)

/-- The load of the array of one word that `fromWordsM` reads as `y` is the canonical word
    of `y`. -/
theorem loadBlk_denote {p : Nat} [NeZero p] (hp : p ≤ 2 ^ 64) (A : Fin 1 → BitVec 64)
    (y : ZMod p) (h : fromWordsMF p 64 1 A = some y) :
    loadBlk.denote (.cons A .nil) = canonEnc p y := by
  have h' : (A 0).toNat < p ∧ ((A 0).toNat : ZMod p) = y := by
    simpa [fromWordsMF, wordsVal] using h
  obtain ⟨hlt, rfl⟩ := h'
  show stackGet A (BitVec.ofNat 64 0).toNat = _
  apply FieldWord.eq_canonEnc_of_toNat hp
  simp [stackGet, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

/-- The store of the canonical word of `y` is the one-word cast `toWordsM` of `y`. -/
theorem storeBlk_denote {p : Nat} (y : ZMod p) :
    storeBlk.denote (.cons (canonEnc p y) .nil) = toWordsMF p 64 1 y := by
  show stackSet (JasminTy.default (.stackArr 64 1)) (0 : Nat) (canonEnc p y) = _
  funext i
  fin_cases i
  simp [stackSet, toWordsMF, wordsOf]
  rfl

/-- The load at index `0` has fixed events. -/
theorem loadBlk_fixed (Pj : JLeakParams) : LeakFixed (jLeakModel Pj) loadBlk := by
  intro V₁ V₂
  rfl

/-- The store at index `0` has fixed events at leakage parameters with no variable-time
    operation. -/
theorem storeBlk_fixed (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none) :
    LeakFixed (jLeakModel Pj) storeBlk := by
  intro V₁ V₂
  simp only [storeBlk, ComLevelCheck.Com.ctLeak, ComLevelCheck.Expr.ctLeak,
    ComLevelCheck.opLeak, jLeakModel, Dialects.JasminComLLeak.jKind, hV]

/-- The block of the cast `fromWordsM p w n` in a single-word representation: the load at
    one 64-bit word. -/
def singleOfWords : (w n : Nat) → Option (Com jasminDialect [.stackArr w n] w64)
  | 64, 1 => some loadBlk
  | _, _ => none

/-- The block of the cast `toWordsM p w n` in a single-word representation: the store at
    one 64-bit word. -/
def singleToWords : (w n : Nat) → Option (Com jasminDialect [w64] (.stackArr w n))
  | 64, 1 => some storeBlk
  | _, _ => none

/-- **The template of a single-word representation** `F` with the canonical encoding at a
    modulus `0 < p ≤ 2 ^ 64`, given the fixed events of its bodies: one limb in a 64-bit
    register, the blocks of `F`, and the load and the store at one 64-bit word. -/
@[instance_reducible] def ofSingleWord {p : Nat} [NeZero p] (F : SingleWordField p)
    (hp : p ≤ 2 ^ 64) (hF : F.enc = canonEnc p)
    (hfix : ∀ Pj : JLeakParams, (∀ op, Pj.opVT op = none) →
      ∀ m, LeakFixed (jLeakModel Pj) (singleBody F m)) :
    ModArithLimbTemplate p .canon where
  limbs := 1
  ty := w64
  enc := F.enc
  body := singleBody F
  body_denote := singleBody_denote F
  body_fixed := hfix
  ofWords := singleOfWords
  ofWords_denote w n c hc A y hy := by
    unfold singleOfWords at hc
    split at hc
    · cases hc
      rw [hF]
      exact loadBlk_denote hp A y hy
    · cases hc
  ofWords_fixed Pj _ w n c hc := by
    unfold singleOfWords at hc
    split at hc
    · cases hc
      exact loadBlk_fixed Pj
    · cases hc
  toWords := singleToWords
  toWords_denote w n c hc y := by
    unfold singleToWords at hc
    split at hc
    · cases hc
      rw [hF]
      exact storeBlk_denote y
    · cases hc
  toWords_fixed Pj hV w n c hc := by
    unfold singleToWords at hc
    split at hc
    · cases hc
      exact storeBlk_fixed Pj hV
    · cases hc

end ModArithLimbTemplate

end CatCrypt.Crypto.SecureCompilation.Algebraic
