/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.LeanFront
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute
public meta import CatCrypt.Hax.ReifyField
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.LeanFront
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute
public meta import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1

/-!
# Curve-field arithmetic through the Lean front

The product, the square, the sum and the difference of the prime fields of P-256, secp256k1,
P-384, BN254 and BLS12-381, each a Lean function over `ZMod p`, read by `reifyField%` and
compiled by `compileA`. The operations are written once, generic in the modulus (`fieldMul`,
`fieldSqr`, `fieldAdd`, `fieldSub`), and each function of a prime applies one of them at that
prime; `reifyField% f unfolding op` reads it as one call of the tagged head `m#p<p>` of the
prime-ir method `m` (`mul` for the product and the square, the square as the product of the
operand with itself). The literal is lifted to a typed expression with the operands as arrays of
`fieldLimbs p` words (`ImpExpr.toTExpr`).

The layout is `FieldRoute.fieldAbi`: the output buffer at `%rdi`, the operands `y` at `%rsi`
and `x` at `%rdx` (the operand `x` at `%rsi` for the square), each of `fieldLimbs p` words, and
the result the words at the entry `%rdi`. The chain of `compileA` lowers the tagged call by the
wide template of its modulus (`FieldWideInline.wideTemplateOf`): the Solinas template at
secp256k1, the canonical Montgomery template at the other primes. Operands and result are
canonical representatives, little-endian limbs (`FieldTag.limbsOf`).

For each function that `compileA` accepts, `<f>_compiles` states the acceptance (by
`native_decide`) and `<f>_bytes` that the decoded bytes halt with the limbs of the value of the
function on the limbs of its operands (`leanFront_correct_field2`, `leanFront_correct_field1`,
with the literal ascended by `fnCorres_fieldOp2`, `fnCorres_fieldOp1`). The functions that
`compileA` refuses have their literal and no theorem; the refusal is that of the check
`ownedCheckMC` of the back half (the guard check `guardsT`: a width guard of a one-bit
immediate in the image of the allocated body that no guard of the reference block matches).

## Main definitions

* `fieldMul`, `fieldSqr`, `fieldAdd`, `fieldSub` — the operations, generic in the modulus.
* `p256`, `secp256k1`, `p384`, `bn254`, `bls12381` — the moduli.
* `<prime><Op>`, `<prime><Op>Imp`, `<prime><Op>TE` — the function of an operation at a prime,
  its literal and its typed literal.
* `ctx2`, `ctx1` — the types of the operands.

## Main results

* `<prime><Op>_compiles` — `compileA` accepts the typed literal under `fieldAbi`.
* `<prime><Op>_bytes` — the decoded bytes compute the function on canonical limbs.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.LeanFrontFields

open CatCrypt.Crypto.SecureCompilation.Haxc
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute (fieldAbi)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open _root_.Hax (ImpExpr ImpType TExpr)
open _root_.Hax.FieldTag (limbsOf)
open _root_.Hax.Ascent (enc)
open CatCrypt.Crypto.Hax (hax64WExit)

/-! ## The operations -/

/-- The product of two elements of `ZMod p`. -/
def fieldMul {p : ℕ} (x y : ZMod p) : ZMod p := x * y

/-- The square of an element of `ZMod p`, as the product with itself. -/
def fieldSqr {p : ℕ} (x : ZMod p) : ZMod p := x * x

/-- The sum of two elements of `ZMod p`. -/
def fieldAdd {p : ℕ} (x y : ZMod p) : ZMod p := x + y

/-- The difference of two elements of `ZMod p`. -/
def fieldSub {p : ℕ} (x y : ZMod p) : ZMod p := x - y

/-! ## The moduli -/

/-- The P-256 base prime. -/
abbrev p256 : ℕ :=
  0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

/-- The secp256k1 base prime. -/
abbrev secp256k1 : ℕ :=
  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f

/-- The P-384 base prime. -/
abbrev p384 : ℕ :=
  0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff

/-- The BN254 base prime. -/
abbrev bn254 : ℕ :=
  0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

/-- The BLS12-381 base prime. -/
abbrev bls12381 : ℕ :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-! ## The types of the operands -/

/-- The operands `x` and `y`, arrays of `n` words. -/
def ctx2 (n : Nat) : List (String × ImpType) :=
  [("x", .array (.uint .w64) n), ("y", .array (.uint .w64) n)]

/-- The operand `x`, an array of `n` words. -/
def ctx1 (n : Nat) : List (String × ImpType) := [("x", .array (.uint .w64) n)]

/-- The typed expression of a literal whose lift fails: the unit literal. -/
def unitTE : TExpr := ⟨.lit .unit, .unit⟩

/-! ## The P-256 base prime -/

/-- The product at the P-256 base prime. -/
def p256Mul (x y : ZMod p256) : ZMod p256 := fieldMul x y

/-- The literal of `p256Mul`. -/
def p256MulImp : ImpExpr := reifyField% p256Mul unfolding fieldMul

/-- The typed literal of `p256Mul`. -/
def p256MulTE : TExpr := (p256MulImp.toTExpr (ctx2 4)).getD unitTE

/-- The square at the P-256 base prime. -/
def p256Sqr (x : ZMod p256) : ZMod p256 := fieldSqr x

/-- The literal of `p256Sqr`. -/
def p256SqrImp : ImpExpr := reifyField% p256Sqr unfolding fieldSqr

/-- The typed literal of `p256Sqr`. -/
def p256SqrTE : TExpr := (p256SqrImp.toTExpr (ctx1 4)).getD unitTE

/-- The sum at the P-256 base prime. -/
def p256Add (x y : ZMod p256) : ZMod p256 := fieldAdd x y

/-- The literal of `p256Add`. -/
def p256AddImp : ImpExpr := reifyField% p256Add unfolding fieldAdd

/-- The typed literal of `p256Add`. -/
def p256AddTE : TExpr := (p256AddImp.toTExpr (ctx2 4)).getD unitTE

theorem p256AddTE_spec : p256AddImp.toTExpr (ctx2 4) = some p256AddTE := rfl

set_option linter.style.native false in
/-- `compileA` accepts the typed literal of `p256Add` under `fieldAbi 2 4`. -/
theorem p256Add_compiles :
    (compileA p256AddTE (fieldAbi 2 4) "p256_add").isSome = true := by
  native_decide

/-- **The bytes of `p256Add`.** From every entry state satisfying the regions of `fieldAbi 2 4`
    whose operand regions at `%rdx` and `%rsi` hold the limbs of `x` and `y`, the bytes that
    `compileA` emits decode to a program that halts with the limbs of `p256Add x y` in the 4
    words at the entry `%rdi`. -/
theorem p256Add_bytes {P : Lprog} {bytes : List (BitVec 8)}
    (hc : compileA p256AddTE (fieldAbi 2 4) "p256_add" = some (P, bytes)) (sa : AState)
    (hsep : (fieldAbi 2 4).Regions sa) (x y : ZMod p256)
    (hx : wordsAt sa.mem (sa.regs "%rdx") 4 = limbsOf 4 x.val)
    (hy : wordsAt sa.mem (sa.regs "%rsi") 4 = limbsOf 4 y.val) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ wordsAt sa'.mem (sa.regs "%rdi") 4 = limbsOf 4 (p256Add x y).val := by
  have he : p256AddTE.erase = p256AddImp :=
    _root_.Hax.ImpExpr.erase_toTExpr p256AddTE_spec
  have hl : _root_.Hax.FieldTag.fieldLimbs p256 = 4 := by decide
  have h := leanFront_correct_field2 (p := p256) (by norm_num) p256AddTE (fieldAbi 2 4)
    "p256_add" P bytes hc (by rw [he]; rfl) "%rsi" "%rdx" (by rw [hl]; rfl) rfl
    (by rw [hl]; rfl) p256Add
    (by
      rw [he]
      exact fnCorres_fieldOp2 _ "t" p256Add
        (fun a b => hax64WExit_zmod_add_wide (by decide +kernel) (by norm_num) a b))
    (by decide) sa hsep x y (by rw [hl]; exact hx) (by rw [hl]; exact hy)
  rw [hl] at h
  exact h

/-- The difference at the P-256 base prime. -/
def p256Sub (x y : ZMod p256) : ZMod p256 := fieldSub x y

/-- The literal of `p256Sub`. -/
def p256SubImp : ImpExpr := reifyField% p256Sub unfolding fieldSub

/-- The typed literal of `p256Sub`. -/
def p256SubTE : TExpr := (p256SubImp.toTExpr (ctx2 4)).getD unitTE

theorem p256SubTE_spec : p256SubImp.toTExpr (ctx2 4) = some p256SubTE := rfl

set_option linter.style.native false in
/-- `compileA` accepts the typed literal of `p256Sub` under `fieldAbi 2 4`. -/
theorem p256Sub_compiles :
    (compileA p256SubTE (fieldAbi 2 4) "p256_sub").isSome = true := by
  native_decide

/-- **The bytes of `p256Sub`.** From every entry state satisfying the regions of `fieldAbi 2 4`
    whose operand regions at `%rdx` and `%rsi` hold the limbs of `x` and `y`, the bytes that
    `compileA` emits decode to a program that halts with the limbs of `p256Sub x y` in the 4
    words at the entry `%rdi`. -/
theorem p256Sub_bytes {P : Lprog} {bytes : List (BitVec 8)}
    (hc : compileA p256SubTE (fieldAbi 2 4) "p256_sub" = some (P, bytes)) (sa : AState)
    (hsep : (fieldAbi 2 4).Regions sa) (x y : ZMod p256)
    (hx : wordsAt sa.mem (sa.regs "%rdx") 4 = limbsOf 4 x.val)
    (hy : wordsAt sa.mem (sa.regs "%rsi") 4 = limbsOf 4 y.val) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ wordsAt sa'.mem (sa.regs "%rdi") 4 = limbsOf 4 (p256Sub x y).val := by
  have he : p256SubTE.erase = p256SubImp :=
    _root_.Hax.ImpExpr.erase_toTExpr p256SubTE_spec
  have hl : _root_.Hax.FieldTag.fieldLimbs p256 = 4 := by decide
  have h := leanFront_correct_field2 (p := p256) (by norm_num) p256SubTE (fieldAbi 2 4)
    "p256_sub" P bytes hc (by rw [he]; rfl) "%rsi" "%rdx" (by rw [hl]; rfl) rfl
    (by rw [hl]; rfl) p256Sub
    (by
      rw [he]
      exact fnCorres_fieldOp2 _ "t" p256Sub
        (fun a b => hax64WExit_zmod_sub_wide (by decide +kernel) (by norm_num) a b))
    (by decide) sa hsep x y (by rw [hl]; exact hx) (by rw [hl]; exact hy)
  rw [hl] at h
  exact h

/-! ## The secp256k1 base prime -/

/-- The product at the secp256k1 base prime. -/
def secp256k1Mul (x y : ZMod secp256k1) : ZMod secp256k1 := fieldMul x y

/-- The literal of `secp256k1Mul`. -/
def secp256k1MulImp : ImpExpr := reifyField% secp256k1Mul unfolding fieldMul

/-- The typed literal of `secp256k1Mul`. -/
def secp256k1MulTE : TExpr := (secp256k1MulImp.toTExpr (ctx2 4)).getD unitTE

theorem secp256k1MulTE_spec : secp256k1MulImp.toTExpr (ctx2 4) = some secp256k1MulTE := rfl

set_option linter.style.native false in
/-- `compileA` accepts the typed literal of `secp256k1Mul` under `fieldAbi 2 4`. -/
theorem secp256k1Mul_compiles :
    (compileA secp256k1MulTE (fieldAbi 2 4) "secp256k1_mul").isSome = true := by
  native_decide

/-- **The bytes of `secp256k1Mul`.** From every entry state satisfying the regions of `fieldAbi 2 4`
    whose operand regions at `%rdx` and `%rsi` hold the limbs of `x` and `y`, the bytes that
    `compileA` emits decode to a program that halts with the limbs of `secp256k1Mul x y` in the 4
    words at the entry `%rdi`. -/
theorem secp256k1Mul_bytes {P : Lprog} {bytes : List (BitVec 8)}
    (hc : compileA secp256k1MulTE (fieldAbi 2 4) "secp256k1_mul" = some (P, bytes)) (sa : AState)
    (hsep : (fieldAbi 2 4).Regions sa) (x y : ZMod secp256k1)
    (hx : wordsAt sa.mem (sa.regs "%rdx") 4 = limbsOf 4 x.val)
    (hy : wordsAt sa.mem (sa.regs "%rsi") 4 = limbsOf 4 y.val) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ wordsAt sa'.mem (sa.regs "%rdi") 4 = limbsOf 4 (secp256k1Mul x y).val := by
  have he : secp256k1MulTE.erase = secp256k1MulImp :=
    _root_.Hax.ImpExpr.erase_toTExpr secp256k1MulTE_spec
  have hl : _root_.Hax.FieldTag.fieldLimbs secp256k1 = 4 := by decide
  have h := leanFront_correct_field2 (p := secp256k1) (by norm_num) secp256k1MulTE (fieldAbi 2 4)
    "secp256k1_mul" P bytes hc (by rw [he]; rfl) "%rsi" "%rdx" (by rw [hl]; rfl) rfl
    (by rw [hl]; rfl) secp256k1Mul
    (by
      rw [he]
      exact fnCorres_fieldOp2 _ "t" secp256k1Mul
        (fun a b => hax64WExit_zmod_mul_wide (by decide +kernel) (by norm_num) a b))
    (by decide) sa hsep x y (by rw [hl]; exact hx) (by rw [hl]; exact hy)
  rw [hl] at h
  exact h

/-- The square at the secp256k1 base prime. -/
def secp256k1Sqr (x : ZMod secp256k1) : ZMod secp256k1 := fieldSqr x

/-- The literal of `secp256k1Sqr`. -/
def secp256k1SqrImp : ImpExpr := reifyField% secp256k1Sqr unfolding fieldSqr

/-- The typed literal of `secp256k1Sqr`. -/
def secp256k1SqrTE : TExpr := (secp256k1SqrImp.toTExpr (ctx1 4)).getD unitTE

theorem secp256k1SqrTE_spec : secp256k1SqrImp.toTExpr (ctx1 4) = some secp256k1SqrTE := rfl

set_option linter.style.native false in
/-- `compileA` accepts the typed literal of `secp256k1Sqr` under `fieldAbi 1 4`. -/
theorem secp256k1Sqr_compiles :
    (compileA secp256k1SqrTE (fieldAbi 1 4) "secp256k1_sqr").isSome = true := by
  native_decide

/-- **The bytes of `secp256k1Sqr`.** From every entry state satisfying the regions of `fieldAbi 1 4`
    whose operand region at `%rsi` holds the limbs of `x`, the bytes that `compileA` emits
    decode to a program that halts with the limbs of `secp256k1Sqr x` in the 4 words at the entry
    `%rdi`. -/
theorem secp256k1Sqr_bytes {P : Lprog} {bytes : List (BitVec 8)}
    (hc : compileA secp256k1SqrTE (fieldAbi 1 4) "secp256k1_sqr" = some (P, bytes)) (sa : AState)
    (hsep : (fieldAbi 1 4).Regions sa) (x : ZMod secp256k1)
    (hx : wordsAt sa.mem (sa.regs "%rsi") 4 = limbsOf 4 x.val) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ wordsAt sa'.mem (sa.regs "%rdi") 4 = limbsOf 4 (secp256k1Sqr x).val := by
  have he : secp256k1SqrTE.erase = secp256k1SqrImp :=
    _root_.Hax.ImpExpr.erase_toTExpr secp256k1SqrTE_spec
  have hl : _root_.Hax.FieldTag.fieldLimbs secp256k1 = 4 := by decide
  have h := leanFront_correct_field1 (p := secp256k1) (by norm_num) secp256k1SqrTE (fieldAbi 1 4)
    "secp256k1_sqr" P bytes hc (by rw [he]; rfl) "%rsi" (by rw [hl]; rfl) rfl
    (by rw [hl]; rfl) secp256k1Sqr
    (by
      rw [he]
      exact fnCorres_fieldOp1 _ "t" (· * ·)
        (fun a b => hax64WExit_zmod_mul_wide (by decide +kernel) (by norm_num) a b))
    (by decide) sa hsep x (by rw [hl]; exact hx)
  rw [hl] at h
  exact h

/-- The sum at the secp256k1 base prime. -/
def secp256k1Add (x y : ZMod secp256k1) : ZMod secp256k1 := fieldAdd x y

/-- The literal of `secp256k1Add`. -/
def secp256k1AddImp : ImpExpr := reifyField% secp256k1Add unfolding fieldAdd

/-- The typed literal of `secp256k1Add`. -/
def secp256k1AddTE : TExpr := (secp256k1AddImp.toTExpr (ctx2 4)).getD unitTE

theorem secp256k1AddTE_spec : secp256k1AddImp.toTExpr (ctx2 4) = some secp256k1AddTE := rfl

set_option linter.style.native false in
/-- `compileA` accepts the typed literal of `secp256k1Add` under `fieldAbi 2 4`. -/
theorem secp256k1Add_compiles :
    (compileA secp256k1AddTE (fieldAbi 2 4) "secp256k1_add").isSome = true := by
  native_decide

/-- **The bytes of `secp256k1Add`.** From every entry state satisfying the regions of `fieldAbi 2 4`
    whose operand regions at `%rdx` and `%rsi` hold the limbs of `x` and `y`, the bytes that
    `compileA` emits decode to a program that halts with the limbs of `secp256k1Add x y` in the 4
    words at the entry `%rdi`. -/
theorem secp256k1Add_bytes {P : Lprog} {bytes : List (BitVec 8)}
    (hc : compileA secp256k1AddTE (fieldAbi 2 4) "secp256k1_add" = some (P, bytes)) (sa : AState)
    (hsep : (fieldAbi 2 4).Regions sa) (x y : ZMod secp256k1)
    (hx : wordsAt sa.mem (sa.regs "%rdx") 4 = limbsOf 4 x.val)
    (hy : wordsAt sa.mem (sa.regs "%rsi") 4 = limbsOf 4 y.val) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ wordsAt sa'.mem (sa.regs "%rdi") 4 = limbsOf 4 (secp256k1Add x y).val := by
  have he : secp256k1AddTE.erase = secp256k1AddImp :=
    _root_.Hax.ImpExpr.erase_toTExpr secp256k1AddTE_spec
  have hl : _root_.Hax.FieldTag.fieldLimbs secp256k1 = 4 := by decide
  have h := leanFront_correct_field2 (p := secp256k1) (by norm_num) secp256k1AddTE (fieldAbi 2 4)
    "secp256k1_add" P bytes hc (by rw [he]; rfl) "%rsi" "%rdx" (by rw [hl]; rfl) rfl
    (by rw [hl]; rfl) secp256k1Add
    (by
      rw [he]
      exact fnCorres_fieldOp2 _ "t" secp256k1Add
        (fun a b => hax64WExit_zmod_add_wide (by decide +kernel) (by norm_num) a b))
    (by decide) sa hsep x y (by rw [hl]; exact hx) (by rw [hl]; exact hy)
  rw [hl] at h
  exact h

/-- The difference at the secp256k1 base prime. -/
def secp256k1Sub (x y : ZMod secp256k1) : ZMod secp256k1 := fieldSub x y

/-- The literal of `secp256k1Sub`. -/
def secp256k1SubImp : ImpExpr := reifyField% secp256k1Sub unfolding fieldSub

/-- The typed literal of `secp256k1Sub`. -/
def secp256k1SubTE : TExpr := (secp256k1SubImp.toTExpr (ctx2 4)).getD unitTE

theorem secp256k1SubTE_spec : secp256k1SubImp.toTExpr (ctx2 4) = some secp256k1SubTE := rfl

set_option linter.style.native false in
/-- `compileA` accepts the typed literal of `secp256k1Sub` under `fieldAbi 2 4`. -/
theorem secp256k1Sub_compiles :
    (compileA secp256k1SubTE (fieldAbi 2 4) "secp256k1_sub").isSome = true := by
  native_decide

/-- **The bytes of `secp256k1Sub`.** From every entry state satisfying the regions of `fieldAbi 2 4`
    whose operand regions at `%rdx` and `%rsi` hold the limbs of `x` and `y`, the bytes that
    `compileA` emits decode to a program that halts with the limbs of `secp256k1Sub x y` in the 4
    words at the entry `%rdi`. -/
theorem secp256k1Sub_bytes {P : Lprog} {bytes : List (BitVec 8)}
    (hc : compileA secp256k1SubTE (fieldAbi 2 4) "secp256k1_sub" = some (P, bytes)) (sa : AState)
    (hsep : (fieldAbi 2 4).Regions sa) (x y : ZMod secp256k1)
    (hx : wordsAt sa.mem (sa.regs "%rdx") 4 = limbsOf 4 x.val)
    (hy : wordsAt sa.mem (sa.regs "%rsi") 4 = limbsOf 4 y.val) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ wordsAt sa'.mem (sa.regs "%rdi") 4 = limbsOf 4 (secp256k1Sub x y).val := by
  have he : secp256k1SubTE.erase = secp256k1SubImp :=
    _root_.Hax.ImpExpr.erase_toTExpr secp256k1SubTE_spec
  have hl : _root_.Hax.FieldTag.fieldLimbs secp256k1 = 4 := by decide
  have h := leanFront_correct_field2 (p := secp256k1) (by norm_num) secp256k1SubTE (fieldAbi 2 4)
    "secp256k1_sub" P bytes hc (by rw [he]; rfl) "%rsi" "%rdx" (by rw [hl]; rfl) rfl
    (by rw [hl]; rfl) secp256k1Sub
    (by
      rw [he]
      exact fnCorres_fieldOp2 _ "t" secp256k1Sub
        (fun a b => hax64WExit_zmod_sub_wide (by decide +kernel) (by norm_num) a b))
    (by decide) sa hsep x y (by rw [hl]; exact hx) (by rw [hl]; exact hy)
  rw [hl] at h
  exact h

/-! ## The P-384 base prime -/

/-- The product at the P-384 base prime. -/
def p384Mul (x y : ZMod p384) : ZMod p384 := fieldMul x y

/-- The literal of `p384Mul`. -/
def p384MulImp : ImpExpr := reifyField% p384Mul unfolding fieldMul

/-- The typed literal of `p384Mul`. -/
def p384MulTE : TExpr := (p384MulImp.toTExpr (ctx2 6)).getD unitTE

/-- The square at the P-384 base prime. -/
def p384Sqr (x : ZMod p384) : ZMod p384 := fieldSqr x

/-- The literal of `p384Sqr`. -/
def p384SqrImp : ImpExpr := reifyField% p384Sqr unfolding fieldSqr

/-- The typed literal of `p384Sqr`. -/
def p384SqrTE : TExpr := (p384SqrImp.toTExpr (ctx1 6)).getD unitTE

/-- The sum at the P-384 base prime. -/
def p384Add (x y : ZMod p384) : ZMod p384 := fieldAdd x y

/-- The literal of `p384Add`. -/
def p384AddImp : ImpExpr := reifyField% p384Add unfolding fieldAdd

/-- The typed literal of `p384Add`. -/
def p384AddTE : TExpr := (p384AddImp.toTExpr (ctx2 6)).getD unitTE

theorem p384AddTE_spec : p384AddImp.toTExpr (ctx2 6) = some p384AddTE := rfl

set_option linter.style.native false in
/-- `compileA` accepts the typed literal of `p384Add` under `fieldAbi 2 6`. -/
theorem p384Add_compiles :
    (compileA p384AddTE (fieldAbi 2 6) "p384_add").isSome = true := by
  native_decide

/-- **The bytes of `p384Add`.** From every entry state satisfying the regions of `fieldAbi 2 6`
    whose operand regions at `%rdx` and `%rsi` hold the limbs of `x` and `y`, the bytes that
    `compileA` emits decode to a program that halts with the limbs of `p384Add x y` in the 6
    words at the entry `%rdi`. -/
theorem p384Add_bytes {P : Lprog} {bytes : List (BitVec 8)}
    (hc : compileA p384AddTE (fieldAbi 2 6) "p384_add" = some (P, bytes)) (sa : AState)
    (hsep : (fieldAbi 2 6).Regions sa) (x y : ZMod p384)
    (hx : wordsAt sa.mem (sa.regs "%rdx") 6 = limbsOf 6 x.val)
    (hy : wordsAt sa.mem (sa.regs "%rsi") 6 = limbsOf 6 y.val) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ wordsAt sa'.mem (sa.regs "%rdi") 6 = limbsOf 6 (p384Add x y).val := by
  have he : p384AddTE.erase = p384AddImp :=
    _root_.Hax.ImpExpr.erase_toTExpr p384AddTE_spec
  have hl : _root_.Hax.FieldTag.fieldLimbs p384 = 6 := by decide
  have h := leanFront_correct_field2 (p := p384) (by norm_num) p384AddTE (fieldAbi 2 6)
    "p384_add" P bytes hc (by rw [he]; rfl) "%rsi" "%rdx" (by rw [hl]; rfl) rfl
    (by rw [hl]; rfl) p384Add
    (by
      rw [he]
      exact fnCorres_fieldOp2 _ "t" p384Add
        (fun a b => hax64WExit_zmod_add_wide (by decide +kernel) (by norm_num) a b))
    (by decide) sa hsep x y (by rw [hl]; exact hx) (by rw [hl]; exact hy)
  rw [hl] at h
  exact h

/-- The difference at the P-384 base prime. -/
def p384Sub (x y : ZMod p384) : ZMod p384 := fieldSub x y

/-- The literal of `p384Sub`. -/
def p384SubImp : ImpExpr := reifyField% p384Sub unfolding fieldSub

/-- The typed literal of `p384Sub`. -/
def p384SubTE : TExpr := (p384SubImp.toTExpr (ctx2 6)).getD unitTE

theorem p384SubTE_spec : p384SubImp.toTExpr (ctx2 6) = some p384SubTE := rfl

set_option linter.style.native false in
/-- `compileA` accepts the typed literal of `p384Sub` under `fieldAbi 2 6`. -/
theorem p384Sub_compiles :
    (compileA p384SubTE (fieldAbi 2 6) "p384_sub").isSome = true := by
  native_decide

/-- **The bytes of `p384Sub`.** From every entry state satisfying the regions of `fieldAbi 2 6`
    whose operand regions at `%rdx` and `%rsi` hold the limbs of `x` and `y`, the bytes that
    `compileA` emits decode to a program that halts with the limbs of `p384Sub x y` in the 6
    words at the entry `%rdi`. -/
theorem p384Sub_bytes {P : Lprog} {bytes : List (BitVec 8)}
    (hc : compileA p384SubTE (fieldAbi 2 6) "p384_sub" = some (P, bytes)) (sa : AState)
    (hsep : (fieldAbi 2 6).Regions sa) (x y : ZMod p384)
    (hx : wordsAt sa.mem (sa.regs "%rdx") 6 = limbsOf 6 x.val)
    (hy : wordsAt sa.mem (sa.regs "%rsi") 6 = limbsOf 6 y.val) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ wordsAt sa'.mem (sa.regs "%rdi") 6 = limbsOf 6 (p384Sub x y).val := by
  have he : p384SubTE.erase = p384SubImp :=
    _root_.Hax.ImpExpr.erase_toTExpr p384SubTE_spec
  have hl : _root_.Hax.FieldTag.fieldLimbs p384 = 6 := by decide
  have h := leanFront_correct_field2 (p := p384) (by norm_num) p384SubTE (fieldAbi 2 6)
    "p384_sub" P bytes hc (by rw [he]; rfl) "%rsi" "%rdx" (by rw [hl]; rfl) rfl
    (by rw [hl]; rfl) p384Sub
    (by
      rw [he]
      exact fnCorres_fieldOp2 _ "t" p384Sub
        (fun a b => hax64WExit_zmod_sub_wide (by decide +kernel) (by norm_num) a b))
    (by decide) sa hsep x y (by rw [hl]; exact hx) (by rw [hl]; exact hy)
  rw [hl] at h
  exact h

/-! ## The BN254 base prime -/

/-- The product at the BN254 base prime. -/
def bn254Mul (x y : ZMod bn254) : ZMod bn254 := fieldMul x y

/-- The literal of `bn254Mul`. -/
def bn254MulImp : ImpExpr := reifyField% bn254Mul unfolding fieldMul

/-- The typed literal of `bn254Mul`. -/
def bn254MulTE : TExpr := (bn254MulImp.toTExpr (ctx2 4)).getD unitTE

/-- The square at the BN254 base prime. -/
def bn254Sqr (x : ZMod bn254) : ZMod bn254 := fieldSqr x

/-- The literal of `bn254Sqr`. -/
def bn254SqrImp : ImpExpr := reifyField% bn254Sqr unfolding fieldSqr

/-- The typed literal of `bn254Sqr`. -/
def bn254SqrTE : TExpr := (bn254SqrImp.toTExpr (ctx1 4)).getD unitTE

/-- The sum at the BN254 base prime. -/
def bn254Add (x y : ZMod bn254) : ZMod bn254 := fieldAdd x y

/-- The literal of `bn254Add`. -/
def bn254AddImp : ImpExpr := reifyField% bn254Add unfolding fieldAdd

/-- The typed literal of `bn254Add`. -/
def bn254AddTE : TExpr := (bn254AddImp.toTExpr (ctx2 4)).getD unitTE

theorem bn254AddTE_spec : bn254AddImp.toTExpr (ctx2 4) = some bn254AddTE := rfl

set_option linter.style.native false in
/-- `compileA` accepts the typed literal of `bn254Add` under `fieldAbi 2 4`. -/
theorem bn254Add_compiles :
    (compileA bn254AddTE (fieldAbi 2 4) "bn254_add").isSome = true := by
  native_decide

/-- **The bytes of `bn254Add`.** From every entry state satisfying the regions of `fieldAbi 2 4`
    whose operand regions at `%rdx` and `%rsi` hold the limbs of `x` and `y`, the bytes that
    `compileA` emits decode to a program that halts with the limbs of `bn254Add x y` in the 4
    words at the entry `%rdi`. -/
theorem bn254Add_bytes {P : Lprog} {bytes : List (BitVec 8)}
    (hc : compileA bn254AddTE (fieldAbi 2 4) "bn254_add" = some (P, bytes)) (sa : AState)
    (hsep : (fieldAbi 2 4).Regions sa) (x y : ZMod bn254)
    (hx : wordsAt sa.mem (sa.regs "%rdx") 4 = limbsOf 4 x.val)
    (hy : wordsAt sa.mem (sa.regs "%rsi") 4 = limbsOf 4 y.val) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ wordsAt sa'.mem (sa.regs "%rdi") 4 = limbsOf 4 (bn254Add x y).val := by
  have he : bn254AddTE.erase = bn254AddImp :=
    _root_.Hax.ImpExpr.erase_toTExpr bn254AddTE_spec
  have hl : _root_.Hax.FieldTag.fieldLimbs bn254 = 4 := by decide
  have h := leanFront_correct_field2 (p := bn254) (by norm_num) bn254AddTE (fieldAbi 2 4)
    "bn254_add" P bytes hc (by rw [he]; rfl) "%rsi" "%rdx" (by rw [hl]; rfl) rfl
    (by rw [hl]; rfl) bn254Add
    (by
      rw [he]
      exact fnCorres_fieldOp2 _ "t" bn254Add
        (fun a b => hax64WExit_zmod_add_wide (by decide +kernel) (by norm_num) a b))
    (by decide) sa hsep x y (by rw [hl]; exact hx) (by rw [hl]; exact hy)
  rw [hl] at h
  exact h

/-- The difference at the BN254 base prime. -/
def bn254Sub (x y : ZMod bn254) : ZMod bn254 := fieldSub x y

/-- The literal of `bn254Sub`. -/
def bn254SubImp : ImpExpr := reifyField% bn254Sub unfolding fieldSub

/-- The typed literal of `bn254Sub`. -/
def bn254SubTE : TExpr := (bn254SubImp.toTExpr (ctx2 4)).getD unitTE

theorem bn254SubTE_spec : bn254SubImp.toTExpr (ctx2 4) = some bn254SubTE := rfl

set_option linter.style.native false in
/-- `compileA` accepts the typed literal of `bn254Sub` under `fieldAbi 2 4`. -/
theorem bn254Sub_compiles :
    (compileA bn254SubTE (fieldAbi 2 4) "bn254_sub").isSome = true := by
  native_decide

/-- **The bytes of `bn254Sub`.** From every entry state satisfying the regions of `fieldAbi 2 4`
    whose operand regions at `%rdx` and `%rsi` hold the limbs of `x` and `y`, the bytes that
    `compileA` emits decode to a program that halts with the limbs of `bn254Sub x y` in the 4
    words at the entry `%rdi`. -/
theorem bn254Sub_bytes {P : Lprog} {bytes : List (BitVec 8)}
    (hc : compileA bn254SubTE (fieldAbi 2 4) "bn254_sub" = some (P, bytes)) (sa : AState)
    (hsep : (fieldAbi 2 4).Regions sa) (x y : ZMod bn254)
    (hx : wordsAt sa.mem (sa.regs "%rdx") 4 = limbsOf 4 x.val)
    (hy : wordsAt sa.mem (sa.regs "%rsi") 4 = limbsOf 4 y.val) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ wordsAt sa'.mem (sa.regs "%rdi") 4 = limbsOf 4 (bn254Sub x y).val := by
  have he : bn254SubTE.erase = bn254SubImp :=
    _root_.Hax.ImpExpr.erase_toTExpr bn254SubTE_spec
  have hl : _root_.Hax.FieldTag.fieldLimbs bn254 = 4 := by decide
  have h := leanFront_correct_field2 (p := bn254) (by norm_num) bn254SubTE (fieldAbi 2 4)
    "bn254_sub" P bytes hc (by rw [he]; rfl) "%rsi" "%rdx" (by rw [hl]; rfl) rfl
    (by rw [hl]; rfl) bn254Sub
    (by
      rw [he]
      exact fnCorres_fieldOp2 _ "t" bn254Sub
        (fun a b => hax64WExit_zmod_sub_wide (by decide +kernel) (by norm_num) a b))
    (by decide) sa hsep x y (by rw [hl]; exact hx) (by rw [hl]; exact hy)
  rw [hl] at h
  exact h

/-! ## The BLS12-381 base prime -/

/-- The product at the BLS12-381 base prime. -/
def bls12381Mul (x y : ZMod bls12381) : ZMod bls12381 := fieldMul x y

/-- The literal of `bls12381Mul`. -/
def bls12381MulImp : ImpExpr := reifyField% bls12381Mul unfolding fieldMul

/-- The typed literal of `bls12381Mul`. -/
def bls12381MulTE : TExpr := (bls12381MulImp.toTExpr (ctx2 6)).getD unitTE

/-- The square at the BLS12-381 base prime. -/
def bls12381Sqr (x : ZMod bls12381) : ZMod bls12381 := fieldSqr x

/-- The literal of `bls12381Sqr`. -/
def bls12381SqrImp : ImpExpr := reifyField% bls12381Sqr unfolding fieldSqr

/-- The typed literal of `bls12381Sqr`. -/
def bls12381SqrTE : TExpr := (bls12381SqrImp.toTExpr (ctx1 6)).getD unitTE

/-- The sum at the BLS12-381 base prime. -/
def bls12381Add (x y : ZMod bls12381) : ZMod bls12381 := fieldAdd x y

/-- The literal of `bls12381Add`. -/
def bls12381AddImp : ImpExpr := reifyField% bls12381Add unfolding fieldAdd

/-- The typed literal of `bls12381Add`. -/
def bls12381AddTE : TExpr := (bls12381AddImp.toTExpr (ctx2 6)).getD unitTE

/-- The difference at the BLS12-381 base prime. -/
def bls12381Sub (x y : ZMod bls12381) : ZMod bls12381 := fieldSub x y

/-- The literal of `bls12381Sub`. -/
def bls12381SubImp : ImpExpr := reifyField% bls12381Sub unfolding fieldSub

/-- The typed literal of `bls12381Sub`. -/
def bls12381SubTE : TExpr := (bls12381SubImp.toTExpr (ctx2 6)).getD unitTE

theorem bls12381SubTE_spec : bls12381SubImp.toTExpr (ctx2 6) = some bls12381SubTE := rfl

set_option linter.style.native false in
/-- `compileA` accepts the typed literal of `bls12381Sub` under `fieldAbi 2 6`. -/
theorem bls12381Sub_compiles :
    (compileA bls12381SubTE (fieldAbi 2 6) "bls12381_sub").isSome = true := by
  native_decide

/-- **The bytes of `bls12381Sub`.** From every entry state satisfying the regions of `fieldAbi 2 6`
    whose operand regions at `%rdx` and `%rsi` hold the limbs of `x` and `y`, the bytes that
    `compileA` emits decode to a program that halts with the limbs of `bls12381Sub x y` in the 6
    words at the entry `%rdi`. -/
theorem bls12381Sub_bytes {P : Lprog} {bytes : List (BitVec 8)}
    (hc : compileA bls12381SubTE (fieldAbi 2 6) "bls12381_sub" = some (P, bytes)) (sa : AState)
    (hsep : (fieldAbi 2 6).Regions sa) (x y : ZMod bls12381)
    (hx : wordsAt sa.mem (sa.regs "%rdx") 6 = limbsOf 6 x.val)
    (hy : wordsAt sa.mem (sa.regs "%rsi") 6 = limbsOf 6 y.val) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ wordsAt sa'.mem (sa.regs "%rdi") 6 = limbsOf 6 (bls12381Sub x y).val := by
  have he : bls12381SubTE.erase = bls12381SubImp :=
    _root_.Hax.ImpExpr.erase_toTExpr bls12381SubTE_spec
  have hl : _root_.Hax.FieldTag.fieldLimbs bls12381 = 6 := by decide
  have h := leanFront_correct_field2 (p := bls12381) (by norm_num) bls12381SubTE (fieldAbi 2 6)
    "bls12381_sub" P bytes hc (by rw [he]; rfl) "%rsi" "%rdx" (by rw [hl]; rfl) rfl
    (by rw [hl]; rfl) bls12381Sub
    (by
      rw [he]
      exact fnCorres_fieldOp2 _ "t" bls12381Sub
        (fun a b => hax64WExit_zmod_sub_wide (by decide +kernel) (by norm_num) a b))
    (by decide) sa hsep x y (by rw [hl]; exact hx) (by rw [hl]; exact hy)
  rw [hl] at h
  exact h

end CatCrypt.Crypto.SecureCompilation.Haxc.LeanFrontFields
