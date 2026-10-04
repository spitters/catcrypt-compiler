/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.Gf2Dialect

/-!
# The aggregated GHASH step over `gf2Dialect`

The product in GF(2^128) at the GCM modulus splits into the unreduced 256-bit carry-less
product `mulWide a b`, a pair `(lo, hi)` of 128-bit halves computed by Karatsuba, and the
reduction `reduce256 (lo, hi)` by two folds of `hi` into `lo` through carry-less products
with the constant `0x87`: `reduce256 (mulWide a b) = mulRed a b`. Both maps are built from
`clmul128W`, `^^^` and whole-byte shifts, each linear over GF(2), so `reduce256` is linear
over XOR of pairs. Linearity lets four products share one reduction:

`agg4 h₁ h₂ h₃ h₄ s x₀ x₁ x₂ x₃ = reduce256 (mulWide (s ⊕ x₀) h₄ ⊕ mulWide x₁ h₃ ⊕ mulWide x₂ h₂ ⊕ mulWide x₃ h₁)`

is four GHASH steps at the key powers `hⱼ = h^j`. The identity uses the associativity of
`mulRed`, a polynomial fact stated here as the hypothesis `GF2Laws`; distributivity of
`mulRed` over XOR is proved here from bit-level linearity.

`ghashAggNF n` is the aggregated GHASH loop as a counted loop of `NFProg gf2Dialect` over
groups of four blocks. The four keys `h₁ … h₄` are inputs; the Karatsuba middle operands
`hⱼ ⊕ (hⱼ ≫ 64)` and the constant `0x87` are computed once before the loop. The message is
four block arrays `q₀ … q₃`, group `i` being `q₀[i], q₁[i], q₂[i], q₃[i]`. The loop body sums
the three Karatsuba partial products of the four multiplications and reduces once.

## Main definitions

* `xor256`, `mulWide`, `reduce256`, `kcomb`: the pair XOR, the unreduced product, the
  reduction and the Karatsuba combination.
* `mulWideNF`, `reduce256Block`: the unreduced product and the reduction as programs of
  `gf2Dialect`.
* `GF2Laws`, `agg4`: the associativity hypothesis and the aggregated step.
* `ghashAggNF`, `ghashAggJ`: the aggregated GHASH loop and its lowering by
  `NFProg.map gf2ToJasmin`.

## Main results

* `clmul64W_xor_left`, `clmul128W_xor_left`: the carry-less product is linear in its first
  operand.
* `reduce256_mulWide`, `reduce256_xor`, `mulWide_xor_left`, `xor_mulRed`: the reduction of
  the unreduced product is `mulRed`, and the reduction and `mulRed` are linear.
* `mulWideNF_denote`, `reduce256Block_denote`: the two programs compute `mulWide` and
  `reduce256`.
* `agg4_eq`: under `GF2Laws`, `agg4` at the powers of `h` is `ghashFold h s [x₀, x₁, x₂, x₃]`.
* `ghashAggNF_denote`, `ghashAggNF_denote_ghashFold`: the aggregated loop folds `agg4` over the
  groups, and under `GF2Laws` at the powers of `h` computes `ghashFold` over the blocks in
  group order.
* `map?_ghashAggNF`, `ghashAggJ_denote`, `ghashAggJ_denote_ghashFold`: the partial lowering
  succeeds and the lowered loop computes the same values.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Gf2Aggregate

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Gf2Dialect
open Ctxt (Var Valuation)

/-! ## 1. Linearity of the carry-less product -/

/-- A `Fin.foldl` whose step on a XOR splits into two steps splits into two folds. -/
theorem fin_foldl_xor {w : Nat} : {n : Nat} → (f g k : BitVec w → Fin n → BitVec w) →
    (∀ x y i, k (x ^^^ y) i = f x i ^^^ g y i) → (x y : BitVec w) →
    Fin.foldl n k (x ^^^ y) = Fin.foldl n f x ^^^ Fin.foldl n g y
  | 0, _, _, _, _, _, _ => by simp only [Fin.foldl_zero]
  | n + 1, f, g, k, hk, x, y => by
      rw [Fin.foldl_succ, Fin.foldl_succ, Fin.foldl_succ, hk]
      exact fin_foldl_xor _ _ _ (fun x y i => hk x y i.succ) _ _

/-- The mask of one step of the carry-less product is linear in the selected bit. -/
theorem mask_xor (u v : BitVec 64) :
    0#128 - ((u ^^^ v) &&& 1).setWidth 128 =
      (0#128 - (u &&& 1).setWidth 128) ^^^ (0#128 - (v &&& 1).setWidth 128) := by
  bv_decide

/-- One step of the carry-less product is linear in the multiplier and the accumulator. -/
theorem clmul64StepW_xor (a a' : BitVec 64) (b acc acc' : BitVec 128) (i : Nat) :
    clmul64StepW (a ^^^ a') b (acc ^^^ acc') i =
      clmul64StepW a b acc i ^^^ clmul64StepW a' b acc' i := by
  simp only [clmul64StepW, BitVec.ushiftRight_xor_distrib, mask_xor]
  generalize b <<< i = c
  generalize a >>> i = u
  generalize a' >>> i = v
  bv_decide

/-- The carry-less product of two 64-bit halves is linear in its first operand. -/
theorem clmul64W_xor_left (a a' b : BitVec 64) :
    clmul64W (a ^^^ a') b = clmul64W a b ^^^ clmul64W a' b := by
  have key := fin_foldl_xor (n := 64) (fun acc i => clmul64StepW a (b.setWidth 128) acc i.val)
    (fun acc i => clmul64StepW a' (b.setWidth 128) acc i.val)
    (fun acc i => clmul64StepW (a ^^^ a') (b.setWidth 128) acc i.val)
    (fun x y i => clmul64StepW_xor a a' _ x y i.val) 0 0
  rw [BitVec.xor_self] at key
  exact key

/-- The selected 64-bit half of a XOR is the XOR of the selected halves. -/
theorem clmulHalfW_xor (x y : BitVec 128) (hi : Bool) :
    clmulHalfW (x ^^^ y) hi = clmulHalfW x hi ^^^ clmulHalfW y hi := by
  cases hi <;> simp only [clmulHalfW, Bool.false_eq_true, ↓reduceIte] <;> bv_decide

/-- `VPCLMULQDQ` is linear in its first operand. -/
theorem clmul128W_xor_left (x y b : BitVec 128) (imm : Nat) :
    clmul128W (x ^^^ y) b imm = clmul128W x b imm ^^^ clmul128W y b imm := by
  simp only [clmul128W, clmulHalfW_xor, clmul64W_xor_left]

/-! ## 2. The unreduced product and the reduction -/

/-- The XOR of two 256-bit values held as `(lo, hi)` pairs. -/
def xor256 (x y : BitVec 128 × BitVec 128) : BitVec 128 × BitVec 128 :=
  (x.1 ^^^ y.1, x.2 ^^^ y.2)

/-- The unreduced 256-bit carry-less product of `a` and `b` as the pair of its Karatsuba
    halves `(lo, hi)`. -/
def mulWide (a b : BitVec 128) : BitVec 128 × BitVec 128 :=
  (gfClmulLoSpec a b, gfClmulHiSpec a b)

/-- The reduction of a 256-bit value `(lo, hi)` modulo `X^128 + X^7 + X^2 + X + 1`: two
    folds of the high half into the low half by carry-less products with `0x87`. -/
def reduce256 (x : BitVec 128 × BitVec 128) : BitVec 128 :=
  let r := 0x87#128
  let t := clmul128W x.2 r 0x00
  let carry := clmul128W x.2 r 0x01
  let cshift := carry <<< (8 * 8)
  let t1 := t ^^^ cshift
  let cspill := carry >>> (8 * 8)
  let lo1 := x.1 ^^^ t1
  let t2 := clmul128W cspill r 0x00
  lo1 ^^^ t2

/-- The reduction of the unreduced product is the reduced product. -/
theorem reduce256_mulWide (a b : BitVec 128) : reduce256 (mulWide a b) = mulRed a b := rfl

/-- **The reduction is linear** over the XOR of 256-bit values. -/
theorem reduce256_xor (x y : BitVec 128 × BitVec 128) :
    reduce256 (xor256 x y) = reduce256 x ^^^ reduce256 y := by
  simp only [reduce256, xor256, clmul128W_xor_left, BitVec.shiftLeft_xor_distrib,
    BitVec.ushiftRight_xor_distrib]
  bv_decide

/-- The Karatsuba combination of the partial products `t0 = a₀b₀`, `t1 = (a₀+a₁)(b₀+b₁)`
    and `t2 = a₁b₁` into the halves `(lo, hi)` of the 256-bit product. -/
def kcomb (t0 t1 t2 : BitVec 128) : BitVec 128 × BitVec 128 :=
  let u := (t1 ^^^ t0) ^^^ t2
  (t0 ^^^ (u <<< (8 * 8)), t2 ^^^ (u >>> (8 * 8)))

/-- The unreduced product is the Karatsuba combination of its three partial products. -/
theorem mulWide_eq_kcomb (a b : BitVec 128) :
    mulWide a b = kcomb (clmul128W a b 0x00)
      (clmul128W (a ^^^ (a >>> (8 * 8))) (b ^^^ (b >>> (8 * 8))) 0x00)
      (clmul128W a b 0x11) := rfl

/-- The Karatsuba combination is linear. -/
theorem kcomb_xor (t0 t1 t2 t0' t1' t2' : BitVec 128) :
    xor256 (kcomb t0 t1 t2) (kcomb t0' t1' t2') = kcomb (t0 ^^^ t0') (t1 ^^^ t1') (t2 ^^^ t2') := by
  simp only [kcomb, xor256, Prod.mk.injEq]
  constructor <;> bv_decide

/-- The unreduced product is linear in its first operand. -/
theorem mulWide_xor_left (a a' b : BitVec 128) :
    mulWide (a ^^^ a') b = xor256 (mulWide a b) (mulWide a' b) := by
  have hmid : (a ^^^ a') ^^^ ((a ^^^ a') >>> (8 * 8)) =
      (a ^^^ (a >>> (8 * 8))) ^^^ (a' ^^^ (a' >>> (8 * 8))) := by bv_decide
  rw [mulWide_eq_kcomb, mulWide_eq_kcomb, mulWide_eq_kcomb, kcomb_xor, hmid]
  simp only [clmul128W_xor_left]

/-- The reduced product distributes over XOR on the left. -/
theorem xor_mulRed (a a' b : BitVec 128) :
    mulRed (a ^^^ a') b = mulRed a b ^^^ mulRed a' b := by
  rw [← reduce256_mulWide, mulWide_xor_left, reduce256_xor, reduce256_mulWide,
    reduce256_mulWide]

/-! ## 3. The two blocks -/

/-- The polynomial type of 128 bits. -/
abbrev p128 : Gf2Ty := .poly 128

/-- `v% n` is the de Bruijn variable `n` bindings from the top of the context. -/
local syntax "v%" num : term

macro_rules
  | `(v% $n) => do
      let mut t ← `(Ctxt.Var.here)
      for _ in [0:n.getNat] do
        t ← `(Ctxt.Var.there $t)
      pure t

section Exprs

variable {Γ : Ctxt gf2Dialect}

/-- The `clmul hiA hiB` binding at two variables. -/
def gClmul (hiA hiB : Bool) (a b : Var Γ p128) : Expr gf2Dialect Γ p128 :=
  ⟨Gf2Op.clmul hiA hiB, rfl, .cons a (.cons b .nil)⟩

/-- The `xor 128` binding at two variables. -/
def gXor (a b : Var Γ p128) : Expr gf2Dialect Γ p128 :=
  ⟨Gf2Op.xor 128, rfl, .cons a (.cons b .nil)⟩

/-- The `shrBytes k` binding at a variable. -/
def gShr (k : Nat) (a : Var Γ p128) : Expr gf2Dialect Γ p128 :=
  ⟨Gf2Op.shrBytes k, rfl, .cons a .nil⟩

/-- The `shlBytes k` binding at a variable. -/
def gShl (k : Nat) (a : Var Γ p128) : Expr gf2Dialect Γ p128 :=
  ⟨Gf2Op.shlBytes k, rfl, .cons a .nil⟩

/-- The `const 128 c` binding. -/
def gConst (c : Nat) : Expr gf2Dialect Γ p128 :=
  ⟨Gf2Op.const 128 c, rfl, .nil⟩

/-- The `load128 n` binding of the block of an array at a word index. -/
def gLoad {n : Nat} (q : Var Γ (.blocks n)) (i : Var Γ .word) : Expr gf2Dialect Γ p128 :=
  ⟨Gf2Op.load128 n, rfl, .cons q (.cons i .nil)⟩

/-- The `clmul` binding denotes `clmul128W` at the selector `clmulImm hiA hiB`. -/
theorem gClmul_denote (hiA hiB : Bool) (a b : Var Γ p128) (V : Valuation Γ) :
    (gClmul hiA hiB a b).denote V =
      clmul128W (a.lookup V) (b.lookup V) (clmulImm hiA hiB) := rfl

/-- The `xor` binding denotes XOR. -/
theorem gXor_denote (a b : Var Γ p128) (V : Valuation Γ) :
    (gXor a b).denote V =
      (show BitVec 128 from a.lookup V) ^^^ (show BitVec 128 from b.lookup V) := rfl

/-- The `shrBytes` binding denotes a right shift by whole bytes. -/
theorem gShr_denote (k : Nat) (a : Var Γ p128) (V : Valuation Γ) :
    (gShr k a).denote V = (show BitVec 128 from a.lookup V) >>> (k * 8) := rfl

/-- The `shlBytes` binding denotes a left shift by whole bytes. -/
theorem gShl_denote (k : Nat) (a : Var Γ p128) (V : Valuation Γ) :
    (gShl k a).denote V = (show BitVec 128 from a.lookup V) <<< (k * 8) := rfl

/-- The `const` binding denotes the constant. -/
theorem gConst_denote (c : Nat) (V : Valuation Γ) :
    (gConst c : Expr gf2Dialect Γ p128).denote V = (BitVec.ofNat 128 c : BitVec 128) := rfl

/-- The `load128` binding denotes the block at the index. -/
theorem gLoad_denote {n : Nat} (q : Var Γ (.blocks n)) (i : Var Γ .word) (V : Valuation Γ) :
    (gLoad q i).denote V =
      stackGet (n := n) (q.lookup V) (show BitVec 64 from i.lookup V).toNat := rfl

/-- A binding of a straight-line program denotes its body at the extended valuation. -/
theorem com_denote_var {t s : Gf2Ty} (e : Expr gf2Dialect Γ t)
    (body : Com gf2Dialect (t :: Γ) s) (V : Valuation Γ) :
    (Com.var e body).denote V = body.denote (V.extend (e.denote V)) := rfl

/-- A binding of an `NFProg` denotes its continuation at the extended valuation. -/
theorem nf_denote_var {t : Gf2Ty} {ts : List Gf2Ty} (e : Expr gf2Dialect Γ t)
    (k : NFProg gf2Dialect (t :: Γ) ts) (fuel : Nat) (V : Valuation Γ) :
    (NFProg.var e k).denote fuel V = k.denote fuel (V.extend (e.denote V)) := by
  rw [NFProg.denote_var, Expr.denoteM_option_eq_some]
  rfl

end Exprs

/-- Looking up the head of an extended valuation. -/
theorem lookup_here_extend {Γ : Ctxt gf2Dialect} {t : Gf2Ty} (x : ⟦t⟧) (V : Valuation Γ) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (V.extend x) = x := rfl

/-- Looking up a weakened variable in an extended valuation. -/
theorem lookup_there_extend {Γ : Ctxt gf2Dialect} {t t' : Gf2Ty} (x : ⟦t'⟧)
    (V : Valuation Γ) (v : Var Γ t) :
    (Ctxt.Var.there (s := t') v).lookup (V.extend x) = v.lookup V := rfl

/-- The unreduced product over `[a, b]` as a program with the two results `[lo, hi]`: the
    three carry-less partial products and the Karatsuba combination. -/
def mulWideNF : NFProg gf2Dialect [p128, p128] [p128, p128] :=
  -- [a, b]
  .var (gClmul false false (v% 0) (v% 1))
  -- [t0, a, b]
  (.var (gClmul true true (v% 1) (v% 2))
  -- [t2, t0, a, b]
  (.var (gShr 8 (v% 2))
  (.var (gXor (v% 3) (v% 0))
  -- [alo, ahi, t2, t0, a, b]
  (.var (gShr 8 (v% 5))
  (.var (gXor (v% 6) (v% 0))
  -- [blo, bhi, alo, ahi, t2, t0, a, b]
  (.var (gClmul false false (v% 2) (v% 0))
  -- [t1, blo, bhi, alo, ahi, t2, t0, a, b]
  (.var (gXor (v% 0) (v% 6))
  (.var (gXor (v% 0) (v% 6))
  -- [u, t1a, t1, blo, bhi, alo, ahi, t2, t0, a, b]
  (.var (gShl 8 (v% 0))
  (.var (gXor (v% 9) (v% 0))
  -- [lo, midL, u, …]
  (.var (gShr 8 (v% 2))
  (.var (gXor (v% 10) (v% 0))
  -- [hi, midH, lo, …]
  (.ret (.cons (v% 2) (.cons (v% 0) .nil)))))))))))))))

/-- The reduction over `[lo, hi]`: the constant `0x87` and the two folds of `hi` into
    `lo`. -/
def reduce256Block : Com gf2Dialect [p128, p128] p128 :=
  -- [lo, hi]
  .var (gConst 0x87)
  -- [r, lo, hi]
  (.var (gClmul false false (v% 2) (v% 0))
  -- [t, r, lo, hi]
  (.var (gClmul true false (v% 3) (v% 1))
  -- [carry, t, r, lo, hi]
  (.var (gShl 8 (v% 0))
  (.var (gXor (v% 2) (v% 0))
  -- [t1, cshift, carry, t, r, lo, hi]
  (.var (gShr 8 (v% 2))
  (.var (gXor (v% 6) (v% 1))
  -- [lo1, cspill, t1, cshift, carry, t, r, lo, hi]
  (.var (gClmul false false (v% 1) (v% 6))
  (.var (gXor (v% 1) (v% 0))
  (.ret (v% 0))))))))))

/-- The unreduced-product program computes `mulWide`, at every fuel. -/
theorem mulWideNF_denote (a b : BitVec 128) (fuel : Nat) :
    mulWideNF.denote fuel (.cons a (.cons b .nil)) =
      some (.cons (mulWide a b).1 (.cons (mulWide a b).2 .nil)) := by
  simp only [mulWideNF, nf_denote_var, gClmul_denote, gXor_denote, gShr_denote, gShl_denote,
    lookup_here_extend, lookup_there_extend, NFProg.denote_ret]
  rfl

/-- The reduction block computes `reduce256`. -/
theorem reduce256Block_denote (lo hi : BitVec 128) :
    reduce256Block.denote (.cons lo (.cons hi .nil)) = reduce256 (lo, hi) := by
  simp only [reduce256Block, com_denote_var, gClmul_denote, gXor_denote, gShr_denote,
    gShl_denote, gConst_denote, lookup_here_extend, lookup_there_extend, Com.denote]
  rfl

/-! ## 4. The aggregated step -/

/-- The associativity of the reduced product, a theorem about the polynomial reading of
    `mulRed` taken as a hypothesis. -/
structure GF2Laws : Prop where
  /-- `mulRed` is associative. -/
  mulRed_assoc : ∀ a b c : BitVec 128, mulRed (mulRed a b) c = mulRed a (mulRed b c)

/-- **The aggregated GHASH step** over four blocks at the keys `h₁ … h₄`: the four
    unreduced products summed and reduced once. -/
def agg4 (h1 h2 h3 h4 s x0 x1 x2 x3 : BitVec 128) : BitVec 128 :=
  reduce256 (xor256 (xor256 (xor256 (mulWide (s ^^^ x0) h4) (mulWide x1 h3))
    (mulWide x2 h2)) (mulWide x3 h1))

/-- **The aggregated step at the powers of `h` is four GHASH steps.** -/
theorem agg4_eq (L : GF2Laws) (h s x0 x1 x2 x3 : BitVec 128) :
    agg4 h (mulRed h h) (mulRed (mulRed h h) h) (mulRed (mulRed (mulRed h h) h) h)
      s x0 x1 x2 x3 = ghashFold h s [x0, x1, x2, x3] := by
  simp only [agg4, reduce256_xor, reduce256_mulWide, ghashFold, List.foldl_cons,
    List.foldl_nil, xor_mulRed, L.mulRed_assoc]

/-- The value of the loop body of `ghashAggNF`: the three Karatsuba partial products of
    the four multiplications summed, combined and reduced once. -/
def aggStep (h1 h2 h3 h4 s b0 b1 b2 b3 : BitVec 128) : BitVec 128 :=
  let x0 := s ^^^ b0
  reduce256 (kcomb
    (((clmul128W x0 h4 0x00 ^^^ clmul128W b1 h3 0x00) ^^^ clmul128W b2 h2 0x00) ^^^
      clmul128W b3 h1 0x00)
    (((clmul128W (x0 ^^^ (x0 >>> (8 * 8))) (h4 ^^^ (h4 >>> (8 * 8))) 0x00 ^^^
        clmul128W (b1 ^^^ (b1 >>> (8 * 8))) (h3 ^^^ (h3 >>> (8 * 8))) 0x00) ^^^
        clmul128W (b2 ^^^ (b2 >>> (8 * 8))) (h2 ^^^ (h2 >>> (8 * 8))) 0x00) ^^^
      clmul128W (b3 ^^^ (b3 >>> (8 * 8))) (h1 ^^^ (h1 >>> (8 * 8))) 0x00)
    (((clmul128W x0 h4 0x11 ^^^ clmul128W b1 h3 0x11) ^^^ clmul128W b2 h2 0x11) ^^^
      clmul128W b3 h1 0x11))

/-- The loop body value is the aggregated step. -/
theorem aggStep_eq_agg4 (h1 h2 h3 h4 s b0 b1 b2 b3 : BitVec 128) :
    aggStep h1 h2 h3 h4 s b0 b1 b2 b3 = agg4 h1 h2 h3 h4 s b0 b1 b2 b3 := by
  simp only [aggStep, agg4, mulWide_eq_kcomb, kcomb_xor]

/-! ## 5. The aggregated GHASH loop -/

/-- The input context of the aggregated loop: the keys `h₁ … h₄`, the group count, the
    initial accumulator `y₀` and the four block arrays `q₀ … q₃`. -/
abbrev ghashAggCtx (n : Nat) : Ctxt gf2Dialect :=
  [p128, p128, p128, p128, .word, p128, .blocks n, .blocks n, .blocks n, .blocks n]

/-- The context after the bindings before the loop: `k₄, e₄, k₃, e₃, k₂, e₂, k₁, e₁`
    (`eⱼ = hⱼ ≫ 64`, `kⱼ = hⱼ ⊕ eⱼ`), the constant `r = 0x87`, then `ghashAggCtx n`. -/
abbrev aggPreCtx (n : Nat) : Ctxt gf2Dialect :=
  [p128, p128, p128, p128, p128, p128, p128, p128, p128, p128, p128, p128, p128, .word, p128,
    .blocks n, .blocks n, .blocks n, .blocks n]

/-- The loop body of the aggregated loop over the context `[s, i] ++ aggPreCtx n`: the four
    blocks of group `i`, the three partial products of each of the four multiplications,
    their sums, the Karatsuba combination and one reduction. -/
def aggBodyNF (n : Nat) : NFProg gf2Dialect (p128 :: .word :: aggPreCtx n) [p128] :=
  -- [s 0, i 1, k4 2, e4 3, k3 4, e3 5, k2 6, e2 7, k1 8, e1 9, r 10, h1 11, h2 12, h3 13,
  --  h4 14, cnt 15, y0 16, q0 17, q1 18, q2 19, q3 20]
  .var (gLoad (v% 17) (v% 1))
  (.var (gLoad (v% 19) (v% 2))
  (.var (gLoad (v% 21) (v% 3))
  (.var (gLoad (v% 23) (v% 4))
  -- [b3, b2, b1, b0, s, …]
  (.var (gXor (v% 4) (v% 3))
  -- x0 = s ⊕ b0 (binding 4); the product x0 · h4
  (.var (gClmul false false (v% 0) (v% 19))
  (.var (gClmul true true (v% 1) (v% 20))
  (.var (gShr 8 (v% 2))
  (.var (gXor (v% 3) (v% 0))
  (.var (gClmul false false (v% 0) (v% 11))
  -- the product b1 · h3 (bindings 10–14)
  (.var (gClmul false false (v% 8) (v% 23))
  (.var (gClmul true true (v% 9) (v% 24))
  (.var (gShr 8 (v% 10))
  (.var (gXor (v% 11) (v% 0))
  (.var (gClmul false false (v% 0) (v% 18))
  -- the product b2 · h2 (bindings 15–19)
  (.var (gClmul false false (v% 12) (v% 27))
  (.var (gClmul true true (v% 13) (v% 28))
  (.var (gShr 8 (v% 14))
  (.var (gXor (v% 15) (v% 0))
  (.var (gClmul false false (v% 0) (v% 25))
  -- the product b3 · h1 (bindings 20–24)
  (.var (gClmul false false (v% 16) (v% 31))
  (.var (gClmul true true (v% 17) (v% 32))
  (.var (gShr 8 (v% 18))
  (.var (gXor (v% 19) (v% 0))
  (.var (gClmul false false (v% 0) (v% 32))
  -- T0 (bindings 25–27), T2 (28–30), T1 (31–33)
  (.var (gXor (v% 19) (v% 14))
  (.var (gXor (v% 0) (v% 10))
  (.var (gXor (v% 0) (v% 6))
  (.var (gXor (v% 21) (v% 16))
  (.var (gXor (v% 0) (v% 12))
  (.var (gXor (v% 0) (v% 8))
  (.var (gXor (v% 21) (v% 16))
  (.var (gXor (v% 0) (v% 12))
  (.var (gXor (v% 0) (v% 8))
  -- the Karatsuba combination (bindings 34–39): u, lo, hi
  (.var (gXor (v% 0) (v% 6))
  (.var (gXor (v% 0) (v% 4))
  (.var (gShl 8 (v% 0))
  (.var (gXor (v% 9) (v% 0))
  (.var (gShr 8 (v% 2))
  (.var (gXor (v% 8) (v% 0))
  -- the reduction (bindings 40–47)
  (.var (gClmul false false (v% 0) (v% 50))
  (.var (gClmul true false (v% 1) (v% 51))
  (.var (gShl 8 (v% 0))
  (.var (gXor (v% 2) (v% 0))
  (.var (gShr 8 (v% 2))
  (.var (gXor (v% 7) (v% 1))
  (.var (gClmul false false (v% 1) (v% 56))
  (.var (gXor (v% 1) (v% 0))
  (.ret (.cons (v% 0) .nil)))))))))))))))))))))))))))))))))))))))))))))))))

/-- The loop body computes `aggStep` of the accumulator and the four blocks at the trip
    index. -/
theorem aggBodyNF_denote (n fuel : Nat) (s : BitVec 128) (i : BitVec 64)
    (h1 h2 h3 h4 : BitVec 128) (cnt : BitVec 64) (y : BitVec 128)
    (q0 q1 q2 q3 : Fin n → BitVec 128) :
    (aggBodyNF n).denote fuel (.cons s (.cons i
      (.cons (h4 ^^^ (h4 >>> (8 * 8))) (.cons (h4 >>> (8 * 8))
      (.cons (h3 ^^^ (h3 >>> (8 * 8))) (.cons (h3 >>> (8 * 8))
      (.cons (h2 ^^^ (h2 >>> (8 * 8))) (.cons (h2 >>> (8 * 8))
      (.cons (h1 ^^^ (h1 >>> (8 * 8))) (.cons (h1 >>> (8 * 8))
      (.cons (BitVec.ofNat 128 0x87)
      (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons cnt (.cons y
      (.cons q0 (.cons q1 (.cons q2 (.cons q3 .nil))))))))))))))))))))) =
      some (.cons (aggStep h1 h2 h3 h4 s (stackGet q0 i.toNat) (stackGet q1 i.toNat)
        (stackGet q2 i.toNat) (stackGet q3 i.toNat)) .nil) := by
  simp only [aggBodyNF, nf_denote_var, gClmul_denote, gXor_denote, gShr_denote, gShl_denote,
    gLoad_denote, lookup_here_extend, lookup_there_extend, NFProg.denote_ret]
  rfl

/-- **The aggregated GHASH loop** over `n` groups of four blocks: the Karatsuba middle
    operands of the keys and the constant `0x87` before the loop, then a counted loop over
    the group count carrying the accumulator `s` with body `aggBodyNF n`. -/
def ghashAggNF (n : Nat) : NFProg gf2Dialect (ghashAggCtx n) [p128] :=
  -- [h1 0, h2 1, h3 2, h4 3, cnt 4, y0 5, q0 6, …]
  .var (gConst 0x87)
  (.var (gShr 8 (v% 1))
  (.var (gXor (v% 2) (v% 0))
  (.var (gShr 8 (v% 4))
  (.var (gXor (v% 5) (v% 0))
  (.var (gShr 8 (v% 7))
  (.var (gXor (v% 8) (v% 0))
  (.var (gShr 8 (v% 10))
  (.var (gXor (v% 11) (v% 0))
  (NFProg.forLoop (d := gf2Dialect) (cs := [p128]) (v% 13) (.cons (v% 14) .nil)
    (aggBodyNF n) (.ret (.cons (v% 0) .nil)))))))))))

/-- **The aggregated loop folds the aggregated step** over the groups at the indices below
    the count, at every fuel. -/
theorem ghashAggNF_denote (n : Nat) (h1 h2 h3 h4 : BitVec 128) (cnt : BitVec 64)
    (y : BitVec 128) (q0 q1 q2 q3 : Fin n → BitVec 128) (fuel : Nat) :
    (ghashAggNF n).denote fuel (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons cnt
      (.cons y (.cons q0 (.cons q1 (.cons q2 (.cons q3 .nil)))))))))) =
      some (.cons ((List.range cnt.toNat).foldl (fun acc i =>
        agg4 h1 h2 h3 h4 acc (stackGet q0 i) (stackGet q1 i) (stackGet q2 i)
          (stackGet q3 i)) y) .nil) := by
  rw [ghashAggNF]
  simp only [nf_denote_var]
  rw [NFProg.denote_forLoop]
  erw [NFProg.foldlM_single (d := gf2Dialect) _
    (fun (acc : BitVec 128) (i : Nat) => aggStep h1 h2 h3 h4 acc
      (stackGet q0 (BitVec.ofNat 64 i).toNat) (stackGet q1 (BitVec.ofNat 64 i).toNat)
      (stackGet q2 (BitVec.ofNat 64 i).toNat) (stackGet q3 (BitVec.ofNat 64 i).toNat))
    (fun acc i => aggBodyNF_denote n fuel acc (BitVec.ofNat 64 i) h1 h2 h3 h4 cnt y
      q0 q1 q2 q3)]
  show some (HVector.cons (f := fun t : Gf2Ty => ⟦t⟧) (t := p128)
    (List.foldl (fun (acc : BitVec 128) (i : Nat) => aggStep h1 h2 h3 h4 acc
      (stackGet q0 (BitVec.ofNat 64 i).toNat) (stackGet q1 (BitVec.ofNat 64 i).toNat)
      (stackGet q2 (BitVec.ofNat 64 i).toNat) (stackGet q3 (BitVec.ofNat 64 i).toNat))
      y (List.range cnt.toNat)) .nil) = _
  refine congrArg (fun z : BitVec 128 =>
    some (HVector.cons (f := fun t : Gf2Ty => ⟦t⟧) (t := p128) z .nil)) ?_
  refine List.foldl_ext _ _ _ (fun acc i hi => ?_)
  rw [List.mem_range] at hi
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans hi cnt.isLt), aggStep_eq_agg4]

/-- A left fold of GHASH folds over block groups is the GHASH fold of the concatenated
    groups. -/
theorem foldl_ghashFold_flatMap (h : BitVec 128) (f : Nat → List (BitVec 128)) :
    (l : List Nat) → (y : BitVec 128) →
      l.foldl (fun acc i => ghashFold h acc (f i)) y = ghashFold h y (l.flatMap f)
  | [], _ => rfl
  | i :: l, y => by
      rw [List.foldl_cons, foldl_ghashFold_flatMap h f l, List.flatMap_cons]
      simp only [ghashFold, List.foldl_append]

/-- Group `i` of the four block arrays: `q₀[i], q₁[i], q₂[i], q₃[i]`. -/
def aggGroup {n : Nat} (q0 q1 q2 q3 : Fin n → BitVec 128) (i : Nat) : List (BitVec 128) :=
  [stackGet q0 i, stackGet q1 i, stackGet q2 i, stackGet q3 i]

/-- **The aggregated loop at the powers of `h` computes the GHASH fold** of the blocks of the
    groups below the count, in group order, at every fuel. -/
theorem ghashAggNF_denote_ghashFold (L : GF2Laws) (n : Nat) (h : BitVec 128)
    (cnt : BitVec 64) (y : BitVec 128) (q0 q1 q2 q3 : Fin n → BitVec 128) (fuel : Nat) :
    (ghashAggNF n).denote fuel (.cons h (.cons (mulRed h h) (.cons (mulRed (mulRed h h) h)
      (.cons (mulRed (mulRed (mulRed h h) h) h) (.cons cnt
      (.cons y (.cons q0 (.cons q1 (.cons q2 (.cons q3 .nil)))))))))) =
      some (.cons (ghashFold h y ((List.range cnt.toNat).flatMap (aggGroup q0 q1 q2 q3)))
        .nil) := by
  rw [ghashAggNF_denote, ← foldl_ghashFold_flatMap]
  simp only [agg4_eq L, aggGroup]
  rfl

/-- The aggregated loop has no `call`. -/
theorem ghashAggNF_callFree (n : Nat) : (ghashAggNF n).callFree = true := rfl

/-- **The lowered aggregated loop**: `ghashAggNF n` lowered by `NFProg.map gf2ToJasmin`, the
    value of `NFProg.map? gf2ToJasmin.toPartial`. -/
def ghashAggJ (n : Nat) : NFProg jasminDialect ((ghashAggCtx n).map Gf2Ty.toJ) [r128] :=
  NFProg.map gf2ToJasmin gf2RegionTypes (ghashAggNF n) (fun v => v)

/-- The lowered aggregated loop is the value of the partial lowering `NFProg.map?`. -/
theorem map?_ghashAggNF (n : Nat) :
    NFProg.map? gf2ToJasmin.toPartial gf2RegionTypes (ghashAggNF n) (fun v => v) =
      some (ghashAggJ n) :=
  NFProg.map?_toPartial _ _ _ _

/-- **The lowered aggregated loop folds the aggregated step**, at every fuel. -/
theorem ghashAggJ_denote (n : Nat) (h1 h2 h3 h4 : BitVec 128) (cnt : BitVec 64)
    (y : BitVec 128) (q0 q1 q2 q3 : Fin n → BitVec 128) (fuel : Nat) :
    (ghashAggJ n).denote fuel (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons cnt
      (.cons y (.cons q0 (.cons q1 (.cons q2 (.cons q3 .nil)))))))))) =
      some (.cons ((List.range cnt.toNat).foldl (fun acc i =>
        agg4 h1 h2 h3 h4 acc (stackGet q0 i) (stackGet q1 i) (stackGet q2 i)
          (stackGet q3 i)) y) .nil) := by
  have key := NFProg.map_denote_of_blockOpTransports gf2ToJasmin transId mapValJ
    gf2RegionTypes gf2ToJasmin_varTransports gf2ToJasmin_blockOpTransports
    gf2ToJasmin_mapValExtends gf2RegionTransports fuel (ghashAggNF n) (ghashAggNF_callFree n)
    (.cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons cnt
      (.cons y (.cons q0 (.cons q1 (.cons q2 (.cons q3 .nil))))))))))
  rw [ghashAggNF_denote] at key
  exact key

/-- **The lowered aggregated loop at the powers of `h` computes the GHASH fold** of the
    blocks of the groups below the count, in group order, at every fuel. -/
theorem ghashAggJ_denote_ghashFold (L : GF2Laws) (n : Nat) (h : BitVec 128)
    (cnt : BitVec 64) (y : BitVec 128) (q0 q1 q2 q3 : Fin n → BitVec 128) (fuel : Nat) :
    (ghashAggJ n).denote fuel (.cons h (.cons (mulRed h h) (.cons (mulRed (mulRed h h) h)
      (.cons (mulRed (mulRed (mulRed h h) h) h) (.cons cnt
      (.cons y (.cons q0 (.cons q1 (.cons q2 (.cons q3 .nil)))))))))) =
      some (.cons (ghashFold h y ((List.range cnt.toNat).flatMap (aggGroup q0 q1 q2 q3)))
        .nil) := by
  have key := NFProg.map_denote_of_blockOpTransports gf2ToJasmin transId mapValJ
    gf2RegionTypes gf2ToJasmin_varTransports gf2ToJasmin_blockOpTransports
    gf2ToJasmin_mapValExtends gf2RegionTransports fuel (ghashAggNF n) (ghashAggNF_callFree n)
    (.cons h (.cons (mulRed h h) (.cons (mulRed (mulRed h h) h)
      (.cons (mulRed (mulRed (mulRed h h) h) h) (.cons cnt
      (.cons y (.cons q0 (.cons q1 (.cons q2 (.cons q3 .nil))))))))))
  rw [ghashAggNF_denote_ghashFold L] at key
  exact key

end CatCrypt.Crypto.SecureCompilation.VIR.Gf2Aggregate
