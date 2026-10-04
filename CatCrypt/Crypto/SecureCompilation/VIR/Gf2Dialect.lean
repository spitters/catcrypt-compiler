/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.DialectCategoryTemplate
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgMap
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin

/-!
# The GF(2) polynomial dialect and its template lowering to `jasminDialect`

`gf2Dialect` is the dialect of binary polynomials stored in bit vectors. Its types are
`poly w` (a polynomial of degree below `w`, denoting `BitVec w`), `word` and `bit` (the
trip counter and the branch bit of `NFProg`) and `blocks n` (an array of `n` 128-bit
message blocks). Its operations are the carry-less multiply of two 64-bit halves
(`clmul`), XOR, the whole-register byte shifts, the product in GF(2^128) at the GCM
modulus `X^128 + X^7 + X^2 + X + 1` (`mulReduced`), bit reversal, constants and the load
of a message block.

Each type of `gf2Dialect` denotes the Lean type of its image under the type map
`Gf2Ty.toJ` into `jasminDialect`, so the value transport of the lowering is the identity.
`gf2ToJasmin` is the template lowering `BlockLoweringData.ofTemplate gf2Frame gf2Template`:
`clmul` becomes one `vsimd (.clmul imm)`, `xor 128` one `vsimd (.bitwise .xor)`, the byte
shifts `vpslldq`/`vpsrldq`, `mulReduced` the Karatsuba product followed by the two folds
of the high half by the constant `0x87`, and `bitReverse` a `vsimd (.affineqb 0)` by the
bit-reversal matrix followed by a `vsimd .vpshufb` by the byte-reversal index.

The denotation of `mulReduced` is `mulRed a b = bf128MulSpec a b 0x87#128`, stated over
the verbatim copies `clmul128W`, `<<<`, `>>>` and `^^^` of the `jasminDialect` waist. Its
polynomial meaning, multiplication in `AdjoinRoot gcmPoly` under the least significant bit
first reading of a bit vector, is a theorem about the same expression.

`ghashNF n` is the GHASH loop as a counted loop of `NFProg gf2Dialect` over the block
count, carrying the accumulator `s` and computing `s := mulReduced (s ⊕ blk) h`, with the
message blocks read from an input of type `blocks n`.

## Main definitions

* `bf128MulSpec`, `mulRed`, `ghashFold`: the reduced product and the GHASH fold.
* `Gf2Ty`, `Gf2Op`, `gf2Dialect`: the dialect.
* `gf2Frame`, `gf2Template`, `gf2ToJasmin`: the template lowering to `jasminDialect`.
* `ghashNF`: the GHASH loop; `ghashJ`: its lowering by `NFProg.map gf2ToJasmin`.

## Main results

* `mulReducedBlock_denote`, `bitReverseBlock_denote`, `gf2Template_denote`: the block
  squares of the template.
* `gf2ToJasmin_blockOpTransports`: the block leaf of `gf2ToJasmin` at every expression.
* `spliceNatural_gf2ToJasmin`: `gf2ToJasmin` commutes with the block splice.
* `gf2ToJasmin_denote`: every `gf2Dialect` program and its lowering denote the same value.
* `ghashNF_denote`, `ghashNF_denote_ofFn`: the GHASH loop computes `ghashFold`.
* `vpshufb_affineqb_reverse`: `PSHUFB` after `GF2P8AFFINEQB` by the two constants reverses
  the bits of a 128-bit register.
* `map?_ghashNF`, `ghashJ_denote`: the partial lowering of the GHASH loop succeeds, and the
  lowered loop computes `ghashFold`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Gf2Dialect

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open Ctxt (Var Valuation)
open FieldDialectBlockDescent (BlockLoweringData pullV TransTy MapVal VarTransports
  BlockOpTransports MapValExtends blockFundamental)
open DialectCategory (LoweringFrame argsHom)
open MultiBlockLowering (hvAppend)

/-! ## 1. The GF(2^128) specifications -/

/-- The low half of the 256-bit carry-less product of `a` and `b` by Karatsuba:
    `t0 ⊕ ((t0 ⊕ t1 ⊕ t2) ≪ 64)` with `t0 = clmul(a, b, 0x00)`, `t2 = clmul(a, b, 0x11)`
    and `t1 = clmul(a ⊕ (a ≫ 64), b ⊕ (b ≫ 64), 0x00)`. -/
def gfClmulLoSpec (a b : BitVec 128) : BitVec 128 :=
  let t0 := clmul128W a b 0x00
  let t2 := clmul128W a b 0x11
  let alo := a ^^^ (a >>> (8 * 8))
  let blo := b ^^^ (b >>> (8 * 8))
  let t1 := clmul128W alo blo 0x00
  let t1b := (t1 ^^^ t0) ^^^ t2
  t0 ^^^ (t1b <<< (8 * 8))

/-- The high half of the 256-bit carry-less product of `a` and `b` by Karatsuba:
    `t2 ⊕ ((t0 ⊕ t1 ⊕ t2) ≫ 64)`. -/
def gfClmulHiSpec (a b : BitVec 128) : BitVec 128 :=
  let t0 := clmul128W a b 0x00
  let t2 := clmul128W a b 0x11
  let alo := a ^^^ (a >>> (8 * 8))
  let blo := b ^^^ (b >>> (8 * 8))
  let t1 := clmul128W alo blo 0x00
  let t1b := (t1 ^^^ t0) ^^^ t2
  t2 ^^^ (t1b >>> (8 * 8))

/-- The product of `a` and `b` reduced by the low word `r` of the modulus: the Karatsuba
    halves `(lo, hi)`, then two folds of the high part into `lo` by carry-less products
    with `r`. At `r = 0x87` it is the product in GF(2^128) modulo
    `X^128 + X^7 + X^2 + X + 1`. -/
def bf128MulSpec (a b r : BitVec 128) : BitVec 128 :=
  let lo := gfClmulLoSpec a b
  let hi := gfClmulHiSpec a b
  let t := clmul128W hi r 0x00
  let carry := clmul128W hi r 0x01
  let cshift := carry <<< (8 * 8)
  let t1 := t ^^^ cshift
  let cspill := carry >>> (8 * 8)
  let lo1 := lo ^^^ t1
  let t2 := clmul128W cspill r 0x00
  lo1 ^^^ t2

/-- The product in GF(2^128) at the GCM modulus, least significant bit first. -/
def mulRed (a b : BitVec 128) : BitVec 128 := bf128MulSpec a b 0x87#128

/-- The GHASH fold in the least significant bit first reading: `y ← (y ⊕ x) · h` per
    block. -/
def ghashFold (h y : BitVec 128) (xs : List (BitVec 128)) : BitVec 128 :=
  xs.foldl (fun acc x => mulRed (acc ^^^ x) h) y

/-- The `imm8` selector of `VPCLMULQDQ` that picks the high half of the first operand
    when `hiA` and the high half of the second when `hiB`. -/
def clmulImm (hiA hiB : Bool) : Nat :=
  (if hiA then 0x01 else 0x00) + (if hiB then 0x10 else 0x00)

/-- The carry-less multiply at `clmulImm hiA hiB` multiplies the selected halves. -/
theorem clmul128W_clmulImm (a b : BitVec 128) (hiA hiB : Bool) :
    clmul128W a b (clmulImm hiA hiB) = clmul64W (clmulHalfW a hiA) (clmulHalfW b hiB) := by
  cases hiA <;> cases hiB <;> rfl

/-- The matrix operand of `GF2P8AFFINEQB` that reverses the bits of every byte: byte `i`
    of each quadword is `2^i`. -/
def bitRevMatrix : Nat := 0x80402010080402018040201008040201

/-- The index operand of `PSHUFB` that reverses the byte order: byte `i` is `15 - i`. -/
def byteRevIndex : Nat := 0x000102030405060708090A0B0C0D0E0F

/-! ## 2. The dialect -/

/-- The type alphabet of `gf2Dialect`. -/
inductive Gf2Ty where
  /-- A binary polynomial of degree below `w`, stored in `w` bits. -/
  | poly (w : Nat)
  /-- A 64-bit word, the trip counter. -/
  | word
  /-- A one-bit flag, the branch bit. -/
  | bit
  /-- An array of `n` 128-bit message blocks. -/
  | blocks (n : Nat)
  deriving DecidableEq, Repr

/-- The image of a `gf2Dialect` type in `jasminDialect`: a polynomial of `w` bits is a
    `w`-bit register, a word a 64-bit register, a bit a one-bit register and a block array
    a stack array of 128-bit words. -/
@[reducible] def Gf2Ty.toJ : Gf2Ty → JasminTy
  | .poly w => .reg w
  | .word => .reg 64
  | .bit => .reg 1
  | .blocks n => .stackArr 128 n

/-- A `gf2Dialect` type denotes the Lean type of its `jasminDialect` image: `poly w`
    denotes `BitVec w`, `word` `BitVec 64`, `bit` `BitVec 1` and `blocks n`
    `Fin n → BitVec 128`. -/
@[reducible] instance : TyDenote Gf2Ty where
  denote t := TyDenote.denote t.toJ

/-- The operations of `gf2Dialect`. -/
inductive Gf2Op where
  /-- The carry-less product of the selected 64-bit halves of two 128-bit operands. -/
  | clmul (hiA hiB : Bool)
  /-- The sum (XOR) of two `w`-bit polynomials. -/
  | xor (w : Nat)
  /-- Multiplication by `X^(8k)` truncated to 128 bits (a left shift by `k` bytes). -/
  | shlBytes (k : Nat)
  /-- Division by `X^(8k)` (a right shift by `k` bytes). -/
  | shrBytes (k : Nat)
  /-- The product in GF(2^128) at the GCM modulus. -/
  | mulReduced
  /-- The reversal of the 128 bits. -/
  | bitReverse
  /-- The `w`-bit constant `c mod 2^w`. -/
  | const (w c : Nat)
  /-- The block of an array of `n` blocks at a word index (taken modulo `n`). -/
  | load128 (n : Nat)
  deriving DecidableEq, Repr

/-- The GF(2) polynomial dialect: `Op` is `Gf2Op`, `Ty` is `Gf2Ty`. -/
@[reducible] def gf2Dialect : Dialect := { Op := Gf2Op, Ty := Gf2Ty }

instance : DialectSignature gf2Dialect where
  sig op := match op with
    | .clmul _ _ => [.poly 128, .poly 128]
    | .xor w => [.poly w, .poly w]
    | .shlBytes _ => [.poly 128]
    | .shrBytes _ => [.poly 128]
    | .mulReduced => [.poly 128, .poly 128]
    | .bitReverse => [.poly 128]
    | .const _ _ => []
    | .load128 n => [.blocks n, .word]
  ret op := match op with
    | .clmul _ _ => .poly 128
    | .xor w => .poly w
    | .shlBytes _ => .poly 128
    | .shrBytes _ => .poly 128
    | .mulReduced => .poly 128
    | .bitReverse => .poly 128
    | .const w _ => .poly w
    | .load128 _ => .poly 128

instance gf2Denote : DialectDenote gf2Dialect where
  denote op := match op with
    | .clmul hiA hiB => fun args =>
        clmul128W args.head args.tail.head (clmulImm hiA hiB)
    | .xor w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        a ^^^ b
    | .shlBytes k => fun args =>
        let a : BitVec 128 := args.head
        a <<< (k * 8)
    | .shrBytes k => fun args =>
        let a : BitVec 128 := args.head
        a >>> (k * 8)
    | .mulReduced => fun args => mulRed args.head args.tail.head
    | .bitReverse => fun args =>
        let a : BitVec 128 := args.head
        a.reverse
    | .const w c => fun _ => show BitVec w from BitVec.ofNat w c
    | .load128 n => fun args =>
        show BitVec 128 from stackGet (n := n) args.head (args.tail.head : BitVec 64).toNat

/-- The trip counter of `gf2Dialect` is `word`, read by `BitVec.toNat`. -/
instance : HasWord64 gf2Dialect where
  word := Gf2Ty.word
  toNat := BitVec.toNat
  ofNat := BitVec.ofNat 64

/-- `gf2Dialect` denotes calls in the empty environment. -/
instance : CallDenote gf2Dialect := ⟨.empty⟩

/-- The branch bit of `gf2Dialect` is `bit`, read as `true` exactly at `1#1`. -/
instance : HasBoolBit gf2Dialect where
  bit := Gf2Ty.bit
  toBool := fun (b : BitVec 1) => decide (b = 1#1)

/-! ## 3. The frame -/

/-- The image of a variable in the mapped context. -/
def mapVar : {Γ : Ctxt gf2Dialect} → {t : Gf2Ty} → Var Γ t →
    Var (d := jasminDialect) (Γ.map Gf2Ty.toJ) t.toJ
  | _ :: _, _, .here => .here
  | _ :: _, _, .there v => .there (mapVar v)

/-- A valuation of a context as a valuation of the mapped context: the same values. -/
def mapVal : {Γ : Ctxt gf2Dialect} → Valuation Γ →
    Valuation (d := jasminDialect) (Γ.map Gf2Ty.toJ)
  | [], .nil => .nil
  | _ :: _, .cons x V => .cons x (mapVal V)

/-- Looking up a mapped variable in a mapped valuation is looking up the variable. -/
theorem lookup_mapVar : {Γ : Ctxt gf2Dialect} → {t : Gf2Ty} → (v : Var Γ t) →
    (V : Valuation Γ) → (mapVar v).lookup (mapVal V) = v.lookup V
  | _ :: _, _, .here, .cons _ _ => rfl
  | _ :: _, _, .there v, .cons _ V => lookup_mapVar v V

/-- A value of a `gf2Dialect` type as a value of its `jasminDialect` image: the same
    value. -/
def tr {t : Gf2Ty} (x : ⟦t⟧) : ⟦t.toJ⟧ := x

/-- The frame of `gf2ToJasmin`: the type map `Gf2Ty.toJ`, applied pointwise to
    contexts. -/
@[reducible] def gf2Frame : LoweringFrame gf2Dialect jasminDialect where
  mapTy := Gf2Ty.toJ
  mapCtx := List.map Gf2Ty.toJ
  mapCtx_nil := rfl
  mapCtx_cons := fun _ _ => rfl
  mapVar := mapVar
  mapVar_here := fun _ _ => rfl
  mapVar_there := fun _ _ _ _ => rfl

/-! ## 4. The blocks -/

/-- The 128-bit register type. -/
abbrev r128 : JasminTy := .reg 128

/-- The `VPCLMULQDQ` expression with selector `imm` at two variables. -/
def eClmul {Γ : Ctxt jasminDialect} (imm : Nat) (va vb : Var Γ r128) :
    Expr jasminDialect Γ r128 :=
  ⟨.vsimd (.clmul imm), rfl, .cons va (.cons vb .nil)⟩

/-- The `VPXOR` expression at two variables. -/
def eXor {Γ : Ctxt jasminDialect} (va vb : Var Γ r128) : Expr jasminDialect Γ r128 :=
  ⟨.vsimd (.bitwise .xor), rfl, .cons va (.cons vb .nil)⟩

/-- The `VPSRLDQ` expression by `k` bytes at a variable. -/
def eSrl {Γ : Ctxt jasminDialect} (k : Nat) (va : Var Γ r128) : Expr jasminDialect Γ r128 :=
  ⟨.vpsrldq k, rfl, .cons va .nil⟩

/-- The `VPSLLDQ` expression by `k` bytes at a variable. -/
def eSll {Γ : Ctxt jasminDialect} (k : Nat) (va : Var Γ r128) : Expr jasminDialect Γ r128 :=
  ⟨.vpslldq k, rfl, .cons va .nil⟩

/-- The constant expression `c mod 2^w`. -/
def eConst {Γ : Ctxt jasminDialect} (w c : Nat) : Expr jasminDialect Γ (.reg w) :=
  ⟨.regConst w c, rfl, .nil⟩

/-- The block of `clmul`: one `VPCLMULQDQ` with the selector `imm`. -/
def clmulBlock (imm : Nat) : Com jasminDialect [r128, r128] r128 :=
  .var ⟨.vsimd (.clmul imm), rfl, .cons .here (.cons (.there .here) .nil)⟩ (.ret .here)

/-- The block of `xor w`: one `VPXOR` at 128 bits, one scalar `xor` otherwise. -/
def xorBlock : (w : Nat) → Com jasminDialect [.reg w, .reg w] (.reg w)
  | 128 => .var ⟨.vsimd (.bitwise .xor), rfl, .cons .here (.cons (.there .here) .nil)⟩
      (.ret .here)
  | w => .var ⟨.regArith .xor w, rfl, .cons .here (.cons (.there .here) .nil)⟩ (.ret .here)

/-- The block of `shlBytes k`: one `VPSLLDQ`. -/
def shlBlock (k : Nat) : Com jasminDialect [r128] r128 :=
  .var ⟨.vpslldq k, rfl, .cons .here .nil⟩ (.ret .here)

/-- The block of `shrBytes k`: one `VPSRLDQ`. -/
def shrBlock (k : Nat) : Com jasminDialect [r128] r128 :=
  .var ⟨.vpsrldq k, rfl, .cons .here .nil⟩ (.ret .here)

/-- The block of `const w c`: one constant materialisation. -/
def constBlock (w c : Nat) : Com jasminDialect [] (.reg w) :=
  .var ⟨.regConst w c, rfl, .nil⟩ (.ret .here)

/-- The block of `load128 n`: one stack-array load. -/
def loadBlock (n : Nat) : Com jasminDialect [.stackArr 128 n, .reg 64] r128 :=
  .var ⟨.stackLoad 128 n, rfl, .cons .here (.cons (.there .here) .nil)⟩ (.ret .here)

/-- The block of `mulReduced` over `[a, b]`: the Karatsuba product (three `VPCLMULQDQ`,
    the halves `lo` and `hi` sharing the first nine bindings), the constant `0x87`, and
    the two folds of `hi` into `lo`. -/
def mulReducedBlock : Com jasminDialect [r128, r128] r128 :=
  -- [a, b]
  .var (eClmul 0x00 .here (.there .here))
  -- [t0, a, b]
  (.var (eClmul 0x11 (.there .here) (.there (.there .here)))
  -- [t2, t0, a, b]
  (.var (eSrl 8 (.there (.there .here)))
  -- [ahi, t2, t0, a, b]
  (.var (eXor (.there (.there (.there .here))) .here)
  -- [alo, ahi, t2, t0, a, b]
  (.var (eSrl 8 (.there (.there (.there (.there (.there .here))))))
  -- [bhi, alo, ahi, t2, t0, a, b]
  (.var (eXor (.there (.there (.there (.there (.there (.there .here)))))) .here)
  -- [blo, bhi, alo, ahi, t2, t0, a, b]
  (.var (eClmul 0x00 (.there (.there .here)) .here)
  -- [t1, blo, bhi, alo, ahi, t2, t0, a, b]
  (.var (eXor .here (.there (.there (.there (.there (.there (.there .here)))))))
  -- [t1a, t1, blo, bhi, alo, ahi, t2, t0, a, b]
  (.var (eXor .here (.there (.there (.there (.there (.there (.there .here)))))))
  -- [t1b, t1a, t1, blo, bhi, alo, ahi, t2, t0, a, b]
  (.var (eSll 8 .here)
  -- [midL, t1b, t1a, t1, blo, bhi, alo, ahi, t2, t0, a, b]
  (.var (eXor (.there (.there (.there (.there (.there (.there (.there (.there (.there
    .here))))))))) .here)
  -- [lo, midL, t1b, t1a, t1, blo, bhi, alo, ahi, t2, t0, a, b]
  (.var (eSrl 8 (.there (.there .here)))
  -- [midH, lo, midL, t1b, t1a, t1, blo, bhi, alo, ahi, t2, t0, a, b]
  (.var (eXor (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there
    .here)))))))))) .here)
  -- [hi, midH, lo, ...]
  (.var (eConst 128 0x87)
  -- [r, hi, midH, lo, ...]
  (.var (eClmul 0x00 (.there .here) .here)
  -- [t, r, hi, midH, lo, ...]
  (.var (eClmul 0x01 (.there (.there .here)) (.there .here))
  -- [carry, t, r, hi, midH, lo, ...]
  (.var (eSll 8 .here)
  -- [cshift, carry, t, r, hi, midH, lo, ...]
  (.var (eXor (.there (.there .here)) .here)
  -- [t1', cshift, carry, t, r, hi, midH, lo, ...]
  (.var (eSrl 8 (.there (.there .here)))
  -- [cspill, t1', cshift, carry, t, r, hi, midH, lo, ...]
  (.var (eXor (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))
    (.there .here))
  -- [lo1, cspill, t1', cshift, carry, t, r, ...]
  (.var (eClmul 0x00 (.there .here) (.there (.there (.there (.there (.there (.there .here)))))))
  -- [t2', lo1, ...]
  (.var (eXor (.there .here) .here)
  (.ret .here))))))))))))))))))))))

/-- The block of `bitReverse` over `[a]`: `GF2P8AFFINEQB` by `bitRevMatrix` reverses the
    bits of every byte, then `PSHUFB` by `byteRevIndex` reverses the byte order. -/
def bitReverseBlock : Com jasminDialect [r128] r128 :=
  .var ⟨.regConst 128 bitRevMatrix, rfl, .nil⟩
  (.var ⟨.vsimd (.affineqb 0#8), rfl, .cons (.there .here) (.cons .here .nil)⟩
  (.var ⟨.regConst 128 byteRevIndex, rfl, .nil⟩
  (.var ⟨.vsimd .vpshufb, rfl, .cons (.there .here) (.cons .here .nil)⟩
  (.ret .here))))

/-- The op template of `gf2ToJasmin`. -/
def gf2Template : gf2Frame.Template
  | .clmul hiA hiB => clmulBlock (clmulImm hiA hiB)
  | .xor w => xorBlock w
  | .shlBytes k => shlBlock k
  | .shrBytes k => shrBlock k
  | .mulReduced => mulReducedBlock
  | .bitReverse => bitReverseBlock
  | .const w c => constBlock w c
  | .load128 n => loadBlock n

/-- **The lowering of `gf2Dialect` to `jasminDialect`**, the template lowering of
    `gf2Template`. -/
def gf2ToJasmin : BlockLoweringData gf2Dialect jasminDialect :=
  BlockLoweringData.ofTemplate gf2Frame gf2Template

/-- `gf2ToJasmin` commutes with the block splice. -/
theorem spliceNatural_gf2ToJasmin : DialectCategory.SpliceNatural gf2ToJasmin :=
  DialectCategory.spliceNatural_ofTemplate _ _

/-! ## 5. The block squares -/

/-- The `xor` block denotes XOR. -/
theorem xorBlock_denote (w : Nat) (a b : BitVec w) :
    (xorBlock w).denote (.cons a (.cons b .nil)) = a ^^^ b := by
  unfold xorBlock
  split <;> rfl

/-- A `VPCLMULQDQ` binding denotes `clmul128W` of its operands. -/
theorem denote_var_clmul {Γ : Ctxt jasminDialect} {s : JasminTy} (imm : Nat)
    (va vb : Var Γ r128) (body : Com jasminDialect (r128 :: Γ) s) (V : Valuation Γ) :
    (Com.var (eClmul imm va vb) body).denote V =
      body.denote (V.extend (clmul128W (va.lookup V) (vb.lookup V) imm)) :=
  rfl

/-- A `VPXOR` binding denotes the XOR of its operands. -/
theorem denote_var_xor {Γ : Ctxt jasminDialect} {s : JasminTy}
    (va vb : Var Γ r128) (body : Com jasminDialect (r128 :: Γ) s) (V : Valuation Γ) :
    (Com.var (eXor va vb) body).denote V =
      body.denote (V.extend ((show BitVec 128 from va.lookup V) ^^^
        (show BitVec 128 from vb.lookup V))) :=
  rfl

/-- A `VPSRLDQ` binding denotes a right shift by whole bytes. -/
theorem denote_var_srl {Γ : Ctxt jasminDialect} {s : JasminTy} (k : Nat)
    (va : Var Γ r128) (body : Com jasminDialect (r128 :: Γ) s) (V : Valuation Γ) :
    (Com.var (eSrl k va) body).denote V =
      body.denote (V.extend ((show BitVec 128 from va.lookup V) >>> (k * 8))) :=
  rfl

/-- A `VPSLLDQ` binding denotes a left shift by whole bytes. -/
theorem denote_var_sll {Γ : Ctxt jasminDialect} {s : JasminTy} (k : Nat)
    (va : Var Γ r128) (body : Com jasminDialect (r128 :: Γ) s) (V : Valuation Γ) :
    (Com.var (eSll k va) body).denote V =
      body.denote (V.extend ((show BitVec 128 from va.lookup V) <<< (k * 8))) :=
  rfl

/-- A constant binding denotes the constant. -/
theorem denote_var_const {Γ : Ctxt jasminDialect} {s : JasminTy} (w c : Nat)
    (body : Com jasminDialect (.reg w :: Γ) s) (V : Valuation Γ) :
    (Com.var (eConst w c) body).denote V =
      body.denote (V.extend (show BitVec w from BitVec.ofNat w c)) :=
  rfl

/-- A return denotes the looked-up variable. -/
theorem denote_ret {Γ : Ctxt jasminDialect} {s : JasminTy} (v : Var Γ s) (V : Valuation Γ) :
    (Com.ret v : Com jasminDialect Γ s).denote V = v.lookup V :=
  rfl

/-- Looking up the head of a cons valuation. -/
theorem lookup_here_cons {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} (x : ⟦t⟧)
    (V : Valuation Γ) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (V.extend x) = x :=
  rfl

/-- Looking up a weakened variable in a cons valuation. -/
theorem lookup_there_cons {Γ : Ctxt jasminDialect} {t t' : jasminDialect.Ty} (x : ⟦t'⟧)
    (V : Valuation Γ) (v : Var Γ t) :
    (Ctxt.Var.there (s := t') v).lookup (V.extend x) = v.lookup V :=
  rfl

/-- The `mulReduced` block denotes `mulRed`. -/
theorem mulReducedBlock_denote (a b : BitVec 128) :
    mulReducedBlock.denote (.cons a (.cons b .nil)) = mulRed a b := by
  simp only [mulReducedBlock, denote_var_clmul, denote_var_xor, denote_var_srl,
    denote_var_sll, denote_var_const, denote_ret, lookup_here_cons, lookup_there_cons]
  rfl

/-- `PSHUFB` by `byteRevIndex` reverses the byte order. -/
theorem vpshufbW_byteRevIndex (x : BitVec 128) :
    vpshufbW x (BitVec.ofNat 128 byteRevIndex) = vPackBytesW (fun i => vByteOfW x i.rev) := by
  unfold vpshufbW
  congr 1
  funext i
  fin_cases i <;> rfl

/-- `GF2P8AFFINEQB` by `bitRevMatrix` with constant `0` reverses the bits of every byte. -/
theorem gf2p8affineqbW_bitRevMatrix (x : BitVec 128) :
    gf2p8affineqbW x (BitVec.ofNat 128 bitRevMatrix) 0#8 =
      vPackBytesW (fun k => (vByteOfW x k).reverse) := by
  unfold gf2p8affineqbW
  congr 1
  funext k
  generalize vByteOfW x k = y
  have hrows : ∀ i : Fin 8,
      vByteOfW (BitVec.ofNat 128 bitRevMatrix) ⟨k.val / 8 * 8 + i.val, by omega⟩ =
        1#8 <<< i.val := by
    intro i
    fin_cases k <;> fin_cases i <;> rfl
  simp only [hrows]
  simp only [gfAffineByteW, byteParityW, Fin.foldl_succ, Fin.foldl_zero, Fin.val_succ,
    Fin.val_zero]
  bv_decide

/-- Reversing the bytes of the byte-wise bit reversal reverses the bits. -/
theorem vPackBytesW_rev_reverse (a : BitVec 128) :
    vPackBytesW (fun i => vByteOfW (vPackBytesW (fun k => (vByteOfW a k).reverse)) i.rev) =
      a.reverse := by
  simp only [vPackBytesW, vByteOfW, Fin.foldl_succ, Fin.foldl_zero, Fin.val_succ,
    Fin.val_zero, Fin.rev]
  bv_decide

/-- `PSHUFB` by `byteRevIndex` after `GF2P8AFFINEQB` by `bitRevMatrix` reverses the bits
    of a 128-bit register. -/
theorem vpshufb_affineqb_reverse (a : BitVec 128) :
    vpshufbW (gf2p8affineqbW a (BitVec.ofNat 128 bitRevMatrix) 0#8)
      (BitVec.ofNat 128 byteRevIndex) = a.reverse := by
  rw [gf2p8affineqbW_bitRevMatrix, vpshufbW_byteRevIndex, vPackBytesW_rev_reverse]

/-- The `bitReverse` block denotes bit reversal. -/
theorem bitReverseBlock_denote (a : BitVec 128) :
    bitReverseBlock.denote (.cons a .nil) = a.reverse :=
  vpshufb_affineqb_reverse a

/-- **The block squares of the template**: on every operation, the template denotes the
    operation's denotation. -/
theorem gf2Template_denote : (op : Gf2Op) →
    (W : Valuation (d := gf2Dialect) (DialectSignature.sig op)) →
    (gf2Template op).denote (mapVal W) = tr (DialectDenote.denote (d := gf2Dialect) op W)
  | .clmul _ _, .cons _ (.cons _ .nil) => rfl
  | .xor w, .cons a (.cons b .nil) => xorBlock_denote w a b
  | .shlBytes _, .cons _ .nil => rfl
  | .shrBytes _, .cons _ .nil => rfl
  | .mulReduced, .cons a (.cons b .nil) => mulReducedBlock_denote a b
  | .bitReverse, .cons a .nil => bitReverseBlock_denote a
  | .const _ _, .nil => rfl
  | .load128 _, .cons _ (.cons _ .nil) => rfl

/-! ## 6. The fundamental property -/

/-- The value transport of `gf2ToJasmin`: the identity. -/
def transId : TransTy gf2ToJasmin := fun x => tr x

/-- The valuation transport of `gf2ToJasmin`: `mapVal`. -/
def mapValJ : MapVal gf2ToJasmin := fun V => mapVal V

/-- Pulling the mapped valuation back along the frame's image of an argument vector gives
    the mapped looked-up arguments. -/
theorem pullV_mapHom_argsHom {Γ : Ctxt gf2Dialect} : {ts : List Gf2Ty} →
    (args : HVector (fun t => Var Γ t) ts) → (V : Valuation Γ) →
    pullV (gf2Frame.mapHom (argsHom args)) (mapVal V) = mapVal (Expr.lookupArgs args V)
  | [], .nil, _ => rfl
  | _ :: _, .cons a as, V => by
      show HVector.cons _ _ = HVector.cons _ _
      congr 1
      · exact lookup_mapVar a V
      · exact pullV_mapHom_argsHom as V

/-- The variable leaf of `gf2ToJasmin`. -/
theorem gf2ToJasmin_varTransports : VarTransports gf2ToJasmin transId mapValJ :=
  fun v V => lookup_mapVar v V

/-- The binding-threading leaf of `gf2ToJasmin`. -/
theorem gf2ToJasmin_mapValExtends : MapValExtends gf2ToJasmin transId mapValJ :=
  fun _ _ => rfl

/-- **The block leaf of `gf2ToJasmin`**: the block of every expression denotes, on the
    mapped valuation, the expression's value. -/
theorem gf2ToJasmin_blockOpTransports : BlockOpTransports gf2ToJasmin transId mapValJ := by
  intro Γ t e V
  obtain ⟨op, rfl, args⟩ := e
  show (Com.rename (gf2Frame.mapHom (argsHom args)) (gf2Template op)).denote (mapVal V) =
    tr (DialectDenote.denote (d := gf2Dialect) op (Expr.lookupArgs args V))
  rw [FieldDialectBlockDescent.Com.denote_rename, pullV_mapHom_argsHom]
  exact gf2Template_denote op _

/-- **The fundamental property of `gf2ToJasmin`**: every `gf2Dialect` program and its
    lowering denote the same value. -/
theorem gf2ToJasmin_denote {Γ : Ctxt gf2Dialect} {t : Gf2Ty} (c : Com gf2Dialect Γ t)
    (V : Valuation Γ) : (gf2ToJasmin.blockLowerCom c).denote (mapVal V) = c.denote V :=
  blockFundamental gf2ToJasmin transId mapValJ gf2ToJasmin_varTransports
    gf2ToJasmin_blockOpTransports gf2ToJasmin_mapValExtends c V

/-! ## 7. The GHASH loop -/

/-- The input context of the GHASH loop: the hash key `h`, the block count, the initial
    accumulator `y₀` and the message blocks. -/
abbrev ghashCtx (n : Nat) : Ctxt gf2Dialect := [.poly 128, .word, .poly 128, .blocks n]

/-- **The GHASH loop** over `n` message blocks: a counted loop over the block count
    carrying the accumulator `s`, with body `s := mulReduced (s ⊕ blk) h`, where `blk` is
    the message block at the trip index. -/
def ghashNF (n : Nat) : NFProg gf2Dialect (ghashCtx n) [.poly 128] :=
  -- body context: [s, i, h, count, y₀, msg]
  let body : NFProg gf2Dialect
      [.poly 128, .word, .poly 128, .word, .poly 128, .blocks n] [.poly 128] :=
    .var ⟨Gf2Op.load128 n, rfl,
        .cons (.there (.there (.there (.there (.there .here))))) (.cons (.there .here) .nil)⟩
      -- [blk, s, i, h, count, y₀, msg]
      (.var ⟨Gf2Op.xor 128, rfl, .cons (.there .here) (.cons .here .nil)⟩
        -- [x, blk, s, i, h, count, y₀, msg]
        (.var ⟨Gf2Op.mulReduced, rfl,
            .cons .here (.cons (.there (.there (.there (.there .here)))) .nil)⟩
          (.ret (.cons .here .nil))))
  NFProg.forLoop (d := gf2Dialect) (cs := [.poly 128]) (.there .here)
    (.cons (.there (.there .here)) .nil) body (.ret (.cons .here .nil))

/-- The block of an array at an index below its length is its entry. -/
theorem stackGet_of_lt {n : Nat} (msg : Fin n → BitVec 128) {i : Nat} (hi : i < n) :
    stackGet msg i = msg ⟨i, hi⟩ := by
  match n, msg, hi with
  | m + 1, msg, hi =>
      show msg ⟨i % (m + 1), _⟩ = _
      congr 1
      exact Fin.ext (Nat.mod_eq_of_lt hi)

/-- **The GHASH loop computes the GHASH fold** of the blocks at the indices below the
    count, at every fuel. -/
theorem ghashNF_denote (n : Nat) (h : BitVec 128) (cnt : BitVec 64) (y : BitVec 128)
    (msg : Fin n → BitVec 128) (fuel : Nat) :
    (ghashNF n).denote fuel (.cons h (.cons cnt (.cons y (.cons msg .nil)))) =
      some (.cons (ghashFold h y ((List.range cnt.toNat).map (stackGet msg))) .nil) := by
  rw [ghashNF, NFProg.denote_forLoop]
  erw [NFProg.foldlM_single (d := gf2Dialect) _
    (fun (acc : BitVec 128) (i : Nat) => mulRed (acc ^^^ stackGet msg (BitVec.ofNat 64 i).toNat) h)
    (fun _ _ => rfl)]
  show some (HVector.cons (f := fun t : Gf2Ty => ⟦t⟧) (t := .poly 128)
    (List.foldl (fun (acc : BitVec 128) (i : Nat) =>
      mulRed (acc ^^^ stackGet msg (BitVec.ofNat 64 i).toNat) h) y (List.range cnt.toNat))
    .nil) = _
  have hf : List.foldl (fun (acc : BitVec 128) (i : Nat) =>
        mulRed (acc ^^^ stackGet msg (BitVec.ofNat 64 i).toNat) h) y (List.range cnt.toNat) =
      List.foldl (fun (acc : BitVec 128) (i : Nat) => mulRed (acc ^^^ stackGet msg i) h) y
        (List.range cnt.toNat) := by
    refine List.foldl_ext _ _ _ (fun acc i hi => ?_)
    rw [List.mem_range] at hi
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans hi cnt.isLt)]
  rw [hf, ghashFold, List.foldl_map]

/-- At the block count `n`, the GHASH loop computes the GHASH fold of all the blocks. -/
theorem ghashNF_denote_ofFn (n : Nat) (hn : n < 2 ^ 64) (h y : BitVec 128)
    (msg : Fin n → BitVec 128) (fuel : Nat) :
    (ghashNF n).denote fuel (.cons h (.cons (BitVec.ofNat 64 n) (.cons y (.cons msg .nil)))) =
      some (.cons (ghashFold h y (List.ofFn msg)) .nil) := by
  rw [ghashNF_denote]
  congr 3
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  refine List.ext_getElem (by simp) (fun i h₁ h₂ => ?_)
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  exact stackGet_of_lt msg _

/-- The trip counter and the branch bit of `gf2Dialect` map to those of `jasminDialect`. -/
theorem gf2RegionTypes : NFProg.RegionTypes gf2ToJasmin := ⟨rfl, rfl⟩

/-- The identity transport preserves the trip count, the trip index and the branch
    decision. -/
theorem gf2RegionTransports : NFProg.RegionTransports gf2ToJasmin gf2RegionTypes transId :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- The GHASH loop has no `call`. -/
theorem ghashNF_callFree (n : Nat) : (ghashNF n).callFree = true := rfl

/-- **The lowered GHASH loop**: `ghashNF n` lowered by `NFProg.map gf2ToJasmin`, the value
    of `NFProg.map? gf2ToJasmin.toPartial`. -/
def ghashJ (n : Nat) : NFProg jasminDialect ((ghashCtx n).map Gf2Ty.toJ) [r128] :=
  NFProg.map gf2ToJasmin gf2RegionTypes (ghashNF n) (fun v => v)

/-- The lowered GHASH loop is the value of the partial lowering `NFProg.map?`. -/
theorem map?_ghashNF (n : Nat) :
    NFProg.map? gf2ToJasmin.toPartial gf2RegionTypes (ghashNF n) (fun v => v) =
      some (ghashJ n) :=
  NFProg.map?_toPartial _ _ _ _

/-- **The lowered GHASH loop computes the GHASH fold**, at every fuel. -/
theorem ghashJ_denote (n : Nat) (h : BitVec 128) (cnt : BitVec 64) (y : BitVec 128)
    (msg : Fin n → BitVec 128) (fuel : Nat) :
    (ghashJ n).denote fuel (.cons h (.cons cnt (.cons y (.cons msg .nil)))) =
      some (.cons (ghashFold h y ((List.range cnt.toNat).map (stackGet msg))) .nil) := by
  have key := NFProg.map_denote_of_blockOpTransports gf2ToJasmin transId mapValJ
    gf2RegionTypes gf2ToJasmin_varTransports gf2ToJasmin_blockOpTransports
    gf2ToJasmin_mapValExtends gf2RegionTransports fuel (ghashNF n) (ghashNF_callFree n)
    (.cons h (.cons cnt (.cons y (.cons msg .nil))))
  rw [ghashNF_denote] at key
  exact key

end CatCrypt.Crypto.SecureCompilation.VIR.Gf2Dialect
