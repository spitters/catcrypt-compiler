/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.SelectIdiom


@[expose] public section
set_option autoImplicit false

/-!
# C6 Instruction Selection: `select` over the homogeneous mask-blend idiom

This file lifts the BitVec-algebra keystone `selectW_eq_maskBlend`
(`SelectIdiom.lean`) to the `Com jasminDialect` program level: it builds the
two `Com`s the instruction-selection pass chooses between — the efficient
single-op `select` (`CMOVcc`) and the multi-op homogeneous-ALU mask-blend idiom
— and proves they have **the same denotation** for every input valuation.

## The two programs

Both are `Com jasminDialect Γ (.reg w)` over a context `Γ` holding the inputs
`cond : reg 1`, `a b : reg w` (via `Ctxt.Var`s).

* `selectIdiomCom cond a b` — the efficient form: a single `select w` op
  (`[reg 1, reg w, reg w] → reg w`, denoting `selectW`).

* `maskBlendCom cond a b` — the idiom over the homogeneous register-arithmetic
  alphabet, exactly the six ops that realise the keystone's right-hand side:

  ```
  let t1   = xor a b               -- a ^^^ b
  let cw   = castW 1 w cond        -- cond.zeroExtend w = ofNat w cond.toNat
  let zero = regConst w 0          -- 0#w
  let mask = sub zero cw           -- 0#w - ofNat w cond.toNat
  let t2   = and t1 mask           -- (a ^^^ b) &&& mask
  let r    = xor t2 b              -- ((a ^^^ b) &&& mask) ^^^ b
  ret r
  ```

  The `castW 1 w` op supplies the 1→w cast for the mask, and `regConst w 0`
  supplies the `0#w` minuend; the three `regArith` ops (`xor`/`sub`/`and`) are
  the homogeneous ALU operations. This covers **all** of the keystone's idiom
  (no sub-idiom shrink was needed).

## Soundness (`selectIdiom_denote`)

`(selectIdiomCom cond a b).denote V = (maskBlendCom cond a b).denote V` for all
valuations `V`. Both `.denote`s reduce — by unfolding `Com.denote` / `Expr.denote`
and the dialect signatures — to closed-form `BitVec` expressions; the equality
is then exactly `selectW_eq_maskBlend` after rewriting
`cond.zeroExtend w = BitVec.ofNat w cond.toNat` (`BitVec.toNat`-injectivity).

This is the genuine C6 result: a denotation-preserving idiom → efficient-op
instruction-selection step, proven at the `Com` level and reusable by the
emitter/optimizer to legally choose `select` over the 3-op mask-blend.

## Framework note

The repository's verified `Com`→`Com` peephole pass
(`VIR/Transforms/Peephole.lean`) is specialised to `catCryptDialect` (its
`buildAlgVar`/`tryConstFold3` rules dispatch on `CatCryptOp`); the `select`
instruction-selection here is over `jasminDialect` (the `selectW` op lives in
the Jasmin dialect). Rather than retrofit that pass, this file delivers the
standalone builder + soundness theorem — the primitive an instruction-selection
rule for `jasminDialect` would carry as its denotation-preservation obligation.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

open JasminDialect

/-! ## 1. The efficient single-op `select` program -/

/-- The efficient instruction-selection target: a one-op `Com` applying the
    dialect's `select w` op (`CMOVcc` data effect) to the condition and the two
    operands, returning its result.

    `select w : [reg 1, reg w, reg w] → reg w`, so its argument `HVector` is
    `cond, a, b`. -/
def selectIdiomCom {w : Nat} {Γ : Ctxt jasminDialect}
    (cond : Ctxt.Var Γ (.reg 1)) (a b : Ctxt.Var Γ (.reg w)) :
    Com jasminDialect Γ (.reg w) :=
  .var (.mk (.select w) rfl (.cons cond (.cons a (.cons b .nil))))
    (.ret .here)

/-! ## 2. The homogeneous mask-blend idiom program -/

/-- The mask-blend idiom as a multi-op `Com` over the homogeneous
    register-arithmetic alphabet, denoting the keystone's right-hand side
    `((a ^^^ b) &&& (0#w - ofNat w cond.toNat)) ^^^ b`.

    All `Var`s are weakened with `.there`s as new bindings are pushed onto the
    context. The six bindings (in order) are `t1 = a^^^b`, `cw = castW cond`,
    `zero = 0#w`, `mask = zero - cw`, `t2 = t1 &&& mask`, `r = t2 ^^^ b`. -/
def maskBlendCom {w : Nat} {Γ : Ctxt jasminDialect}
    (cond : Ctxt.Var Γ (.reg 1)) (a b : Ctxt.Var Γ (.reg w)) :
    Com jasminDialect Γ (.reg w) :=
  -- t1 = xor a b           : reg w
  .var (.mk (.regArith .xor w) rfl (.cons a (.cons b .nil)))
  -- cw = castW 1 w cond    : reg w
  (.var (.mk (.castW 1 w) rfl (.cons (cond.there) .nil))
  -- zero = regConst w 0    : reg w
  (.var (.mk (.regConst w 0) rfl .nil)
  -- mask = sub zero cw     : reg w   (zero = .here, cw = .there .here)
  (.var (.mk (.regArith .sub w) rfl (.cons .here (.cons (.there .here) .nil)))
  -- t2 = and t1 mask       : reg w   (mask = .here, t1 = .there .there .there .here)
  (.var (.mk (.regArith .and w) rfl
            (.cons (.there (.there (.there .here))) (.cons .here .nil)))
  -- r = xor t2 b           : reg w   (t2 = .here, b = b weakened by 5 .there's)
  (.var (.mk (.regArith .xor w) rfl
            (.cons .here (.cons (b.there.there.there.there.there) .nil)))
  (.ret .here))))))

/-! ## 3. Instruction-selection soundness -/

/-- **C6 instruction-selection soundness.**

    The efficient single-op `select` program computes exactly what the
    homogeneous-ALU mask-blend idiom program computes, for every valuation.
    This is the denotation-preservation obligation that licenses the emitter /
    optimizer to choose the `select` op over the 3-op (here 6-op with the cast
    and zero materialisation) mask-blend idiom.

    Proof: unfold both `Com.denote`s / `Expr.denote`s to their closed-form
    `BitVec` expressions; the residual equality is the keystone
    `selectW_eq_maskBlend` after rewriting the cast `cond.zeroExtend w` to
    `BitVec.ofNat w cond.toNat`. -/
theorem selectIdiom_denote {w : Nat} {Γ : Ctxt jasminDialect}
    (cond : Ctxt.Var Γ (.reg 1)) (a b : Ctxt.Var Γ (.reg w))
    (V : Ctxt.Valuation Γ) :
    (selectIdiomCom cond a b).denote V = (maskBlendCom cond a b).denote V := by
  -- Name the looked-up inputs (as `BitVec`s) to state the closed forms.
  let c : BitVec 1 := Ctxt.Var.lookup cond V
  let x : BitVec w := Ctxt.Var.lookup a V
  let y : BitVec w := Ctxt.Var.lookup b V
  -- Both `Com.denote`s reduce definitionally to closed-form `BitVec`
  -- expressions. The efficient program denotes `selectW c x y` (one `select`
  -- op); the idiom program denotes the mask-blend with the 1→w cast on `c`.
  have hL : (selectIdiomCom cond a b).denote V = selectW c x y := rfl
  have hR : (maskBlendCom cond a b).denote V
      = (((x ^^^ y) &&& (0#w - (c.setWidth w))) ^^^ y) := rfl
  rw [hL, hR]
  -- Rewrite the cast `c.setWidth w` to `BitVec.ofNat w c.toNat`, then apply
  -- the BitVec-algebra keystone.
  have hcast : c.setWidth w = BitVec.ofNat w c.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth]
  rw [hcast]
  exact selectW_eq_maskBlend c x y

end CatCrypt.Crypto.SecureCompilation.VIR
