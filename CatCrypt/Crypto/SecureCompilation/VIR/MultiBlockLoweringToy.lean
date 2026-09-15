/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering

/-!
# Multi-value block lowering: double-word addition over two 64-bit registers

A source dialect `dwDialect` has one type, the 128-bit double word, and one op,
addition modulo `2^128`. A target dialect `wordDialect` has one type, the 64-bit
register, and two ops: addition modulo `2^64` and the carry-out of an addition.

The lowering `dwLowering` represents a double word by two registers, low word
first (`dwEnc`), and lowers one addition to a four-binding block: the low sum,
the carry of the low words, the sum of the high words, and the high sum with the
carry added. A three-addition source program lowers to a twelve-binding target
program, and its correctness follows from the block square by
`MultiBlockLoweringData.multiFundamental_on`.

## Main definitions

* `wordDialect`, `dwDialect`: the target and source dialects.
* `dwLowering`: the multi-value lowering, `dwEnc`: its encoding.
* `prog`: the source program `a + b + a + b`.

## Main results

* `setWidth_add_lo`, `setWidth_add_hi`: the low and high words of a 128-bit sum.
* `dwAdd_block`, `dw_blockSquare`: the block square of `dwLowering`.
* `dwLowering_fundamental`: every source program lowers correctly.
* `prog_lowered`: the lowered `prog` maps the registers of `a` and `b` to the
  registers of `a + b + a + b`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLoweringToy

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering

/-! ## 1. The target dialect: 64-bit registers -/

/-- The ops of `wordDialect`: addition modulo `2^64` and the carry-out of an
    addition. -/
inductive WOp where
  | add
  | carry

/-- The dialect of 64-bit registers. -/
def wordDialect : Dialect where
  Op := WOp
  Ty := Unit

instance : TyDenote wordDialect.Ty where
  denote _ := BitVec 64

instance : DialectSignature wordDialect where
  sig _ := [(), ()]
  ret _ := ()

/-- The carry-out of the addition of two 64-bit words, as a 64-bit word. -/
def carryOut (a b : BitVec 64) : BitVec 64 :=
  BitVec.ofNat 64 ((a.toNat + b.toNat) / 2 ^ 64)

/-- The denotation of the ops of `wordDialect` on their two arguments. -/
def wDenote : WOp → BitVec 64 → BitVec 64 → BitVec 64
  | .add, a, b => a + b
  | .carry, a, b => carryOut a b

instance : DialectDenote wordDialect where
  denote op args := wDenote op args.head args.tail.head

/-- The addition expression of `wordDialect`. -/
def wAdd {Γ : Ctxt wordDialect} (x y : Var Γ ()) : Expr wordDialect Γ () :=
  ⟨WOp.add, rfl, .cons x (.cons y .nil)⟩

/-- The carry expression of `wordDialect`. -/
def wCarry {Γ : Ctxt wordDialect} (x y : Var Γ ()) : Expr wordDialect Γ () :=
  ⟨WOp.carry, rfl, .cons x (.cons y .nil)⟩

/-! ## 2. The source dialect: 128-bit double words -/

/-- The op of `dwDialect`: addition modulo `2^128`. -/
inductive DOp where
  | add

/-- The dialect of 128-bit double words. -/
def dwDialect : Dialect where
  Op := DOp
  Ty := Unit

instance : TyDenote dwDialect.Ty where
  denote _ := BitVec 128

instance : DialectSignature dwDialect where
  sig _ := [(), ()]
  ret _ := ()

/-- The denotation of the op of `dwDialect` on its two arguments. -/
def dDenote : DOp → BitVec 128 → BitVec 128 → BitVec 128
  | .add, a, b => a + b

instance : DialectDenote dwDialect where
  denote op args := dDenote op args.head args.tail.head

/-- The two-variable context of `dwDialect`. -/
abbrev Ctx2 : Ctxt dwDialect := [(), ()]

/-- The valuation of `Ctx2` with entries `a` and `b`. -/
def val2 (a b : BitVec 128) : Valuation Ctx2 := .cons a (.cons b .nil)

/-- The addition expression of `dwDialect`. -/
def dAdd {Γ : Ctxt dwDialect} (x y : Var Γ ()) : Expr dwDialect Γ () :=
  ⟨DOp.add, rfl, .cons x (.cons y .nil)⟩

/-! ## 3. The lowering -/

/-- **The double-word lowering.** A double word is two registers, low word first.
    Over the argument registers `[a₀, a₁, b₀, b₁]`, addition binds
    `lo = a₀ + b₀`, `c = carry a₀ b₀`, `h = a₁ + b₁`, `hi = h + c` and returns
    `[lo, hi]`. -/
def dwLowering : MultiBlockLoweringData dwDialect wordDialect where
  mapTys _ := [(), ()]
  lowerOp
    | .add =>
        .var (wAdd .here (.there (.there .here)))
          (.var (wCarry (.there .here) (.there (.there (.there .here))))
            (.var (wAdd (.there (.there (.there .here)))
                (.there (.there (.there (.there (.there .here))))))
              (.var (wAdd .here (.there .here))
                (.ret (.cons (.there (.there (.there .here))) (.cons .here .nil))))))

/-- The encoding of a double word: its low and high 64-bit words. -/
def dwEnc : dwLowering.Enc := fun {_} x =>
  .cons (BitVec.setWidth (w := 128) 64 x)
    (.cons (BitVec.setWidth 64 (BitVec.ushiftRight (n := 128) x 64)) .nil)

/-- The low word of a 128-bit sum is the sum of the low words. -/
theorem setWidth_add_lo (x y : BitVec 128) :
    (x + y).setWidth 64 = x.setWidth 64 + y.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega

/-- The high word of a 128-bit sum is the sum of the high words and the carry of
    the low words. -/
theorem setWidth_add_hi (x y : BitVec 128) :
    ((x + y) >>> 64).setWidth 64
      = (x >>> 64).setWidth 64 + (y >>> 64).setWidth 64
        + carryOut (x.setWidth 64) (y.setWidth 64) := by
  apply BitVec.eq_of_toNat_eq
  simp only [carryOut, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have hx := x.isLt
  have hy := y.isLt
  omega

/-- The coverage predicate that holds of every expression. -/
def allGood : ∀ {Γ : Ctxt dwDialect} {t : dwDialect.Ty}, Expr dwDialect Γ t → Prop :=
  fun _ => True

/-- The addition block maps the registers of `x` and `y` to the registers of
    `x + y`. -/
theorem dwAdd_block (x y : BitVec 128) :
    (dwLowering.lowerOp DOp.add).denote (flatVal dwEnc (val2 x y))
      = dwEnc (t := ()) (x + y) := by
  show (HVector.cons (x.setWidth 64 + y.setWidth 64)
      (HVector.cons ((x >>> 64).setWidth 64 + (y >>> 64).setWidth 64
        + carryOut (x.setWidth 64) (y.setWidth 64)) .nil) : Valuation (d := wordDialect) [(), ()])
    = (HVector.cons ((x + y).setWidth 64) (HVector.cons (((x + y) >>> 64).setWidth 64) .nil) :
        Valuation (d := wordDialect) [(), ()])
  rw [setWidth_add_lo, setWidth_add_hi]

/-- **The block square of `dwLowering`.** -/
theorem dw_blockSquare : dwLowering.BlockSquare dwEnc allGood := by
  intro Γ t e _ vals
  rcases e with ⟨⟨⟩, h, args⟩
  match vals with
  | .cons x (.cons y .nil) => exact dwAdd_block x y

/-- **Correctness of the double-word lowering on every program.** -/
theorem dwLowering_fundamental {Γ : Ctxt dwDialect} {t : dwDialect.Ty}
    (c : Com dwDialect Γ t) (V : Valuation Γ) :
    (dwLowering.lowerMulti c).denote (flatVal dwEnc V) = dwEnc (c.denote V) :=
  dwLowering.multiFundamental_on dwEnc allGood dw_blockSquare c
    (coveredCom_of_forall allGood (fun _ => trivial) c) V

/-! ## 4. A three-op program -/

/-- The source program `let s = a + b; let t = s + a; let u = t + b; ret u`. -/
def prog : Com dwDialect Ctx2 () :=
  .var (dAdd .here (.there .here))
    (.var (dAdd .here (.there .here))
      (.var (dAdd .here (.there (.there (.there .here))))
        (.ret .here)))

/-- `prog` denotes `a + b + a + b`. -/
theorem prog_denote (a b : BitVec 128) :
    (prog.denote (val2 a b) : BitVec 128) = a + b + a + b :=
  rfl

/-- **The lowered `prog`** maps the registers of `a` and `b` to the registers of
    `a + b + a + b`. -/
theorem prog_lowered (a b : BitVec 128) :
    (dwLowering.lowerMulti prog).denote (flatVal dwEnc (val2 a b))
      = dwEnc (t := ()) (a + b + a + b) :=
  (dwLowering_fundamental prog (val2 a b)).trans
    (congrArg (fun z : BitVec 128 => dwEnc (t := ()) z) (prog_denote a b))

end CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLoweringToy
