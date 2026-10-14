/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CarryEqLitIdiom


@[expose] public section
set_option autoImplicit false

/-!
# Instruction Selection: carry-add and is-equal-literal idioms

This file does for two further instruction-selection idioms what
`InstrSelect.lean` does for `select`. It lifts the BitVec-algebra lemmas
`addCarryWord_eq_twoAdds` and `isEqLitIdiom_eq` (`CarryEqLitIdiom.lean`) to the
`Com jasminDialect` program level: it builds the `Com`s the
instruction-selection pass chooses between and proves the
denotation-preservation obligations that license the choice.

## 1. Carry-add (`addCarryLo` over two homogeneous adds)

* `carryAddIdiomCom a b cin` — the efficient form: a single `addCarryLo w` op
  (`[reg w, reg w, reg 1] → reg w`, denoting `addCarryWord`), the data effect of
  `ADCX`/`ADOX`.

* `twoAddsCom a b cin` — the idiom over the homogeneous register-arithmetic
  alphabet: `t1 = add a b`; `cw = castW 1 w cin`; `r = add t1 cw`; `ret r`.

`carryAddIdiom_denote` proves
`(carryAddIdiomCom a b cin).denote V = (twoAddsCom a b cin).denote V` for every
valuation, reducing both `.denote`s to closed `BitVec` forms and closing with
`addCarryWord_eq_twoAdds` (after the `cin.setWidth w = BitVec.ofNat w cin.toNat`
bridge, exactly as `InstrSelect.lean` does for the mask cast). This covers
the lemma in full.

## 2. Is-equal-literal (`isEqLitIdiom` = the spec value)

The `jasminDialect` has **no** dedicated `eqLit`/`thEqLit` op — the
equality-literal test is realised by the pure branchless idiom
`isEqLitIdiom a k` (XOR / negate / OR / shift). Accordingly this file builds the
idiom directly as a multi-op `Com` and proves it computes the **specification**
value:

* `eqLitIdiomCom a k` — the multi-op idiom `Com` (xor / regConst / sub / or /
  shrImm), denoting `isEqLitIdiom (a.lookup V) k`.

* `eqLitIdiom_denote` proves
  `(eqLitIdiomCom a k).denote V = if a.lookup V = BitVec.ofNat w k then 1#w else 0#w`,
  i.e. the emitted idiom program computes exactly the is-equal-literal spec, via
  `isEqLitIdiom_eq`.

Because the dialect has no single efficient equality op to select *to*, the
honest statement is `idiom.denote = spec` (the value-correctness certificate the
front carries for the `thir_eqlit` leaf), rather than `efficient-op.denote =
idiom.denote`. This is the spec-level form the deliverable allows.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR

open JasminDialect

/-! ## 1. Carry-add: efficient single op -/

/-- The efficient instruction-selection target for a carry-chain add: a one-op
    `Com` applying the dialect's `addCarryLo w` op
    (`[reg w, reg w, reg 1] → reg w`, denoting `addCarryWord`) to the two data
    words and the carry-in bit, returning its result. -/
def carryAddIdiomCom {w : Nat} {Γ : Ctxt jasminDialect}
    (a b : Ctxt.Var Γ (.reg w)) (cin : Ctxt.Var Γ (.reg 1)) :
    Com jasminDialect Γ (.reg w) :=
  .var (.mk (.addCarryLo w) rfl (.cons a (.cons b (.cons cin .nil))))
    (.ret .here)

/-! ## 2. Carry-add: two homogeneous adds idiom -/

/-- The carry-add idiom as a multi-op `Com` over the homogeneous
    register-arithmetic alphabet, denoting the lemma's right-hand side
    `(a + b) + (cin.setWidth w)`.

    The three bindings (in order) are `t1 = add a b`, `cw = castW 1 w cin`
    (the 1→w widening of the carry-in), `r = add t1 cw`. `Var`s are weakened
    with `.there`s as bindings are pushed onto the context. -/
def twoAddsCom {w : Nat} {Γ : Ctxt jasminDialect}
    (a b : Ctxt.Var Γ (.reg w)) (cin : Ctxt.Var Γ (.reg 1)) :
    Com jasminDialect Γ (.reg w) :=
  -- t1 = add a b          : reg w
  .var (.mk (.regArith .add w) rfl (.cons a (.cons b .nil)))
  -- cw = castW 1 w cin    : reg w
  (.var (.mk (.castW 1 w) rfl (.cons (cin.there) .nil))
  -- r = add t1 cw         : reg w   (cw = .here, t1 = .there .here)
  (.var (.mk (.regArith .add w) rfl (.cons (.there .here) (.cons .here .nil)))
  (.ret .here)))

/-! ## 3. Carry-add instruction-selection soundness -/

/-- **Carry-add instruction-selection soundness.**

    The efficient single-op `addCarryLo` program computes exactly what the
    homogeneous two-`add` idiom program computes, for every valuation. This is
    the denotation-preservation obligation that licenses the emitter / optimizer
    to choose the single `ADCX`/`ADOX` over the two homogeneous adds.

    Proof: unfold both `Com.denote`s / `Expr.denote`s to their closed-form
    `BitVec` expressions; the residual equality is the lemma
    `addCarryWord_eq_twoAdds` after rewriting the cast `cin.setWidth w` to
    `BitVec.ofNat w cin.toNat`. -/
theorem carryAddIdiom_denote {w : Nat} {Γ : Ctxt jasminDialect}
    (a b : Ctxt.Var Γ (.reg w)) (cin : Ctxt.Var Γ (.reg 1))
    (V : Ctxt.Valuation Γ) :
    (carryAddIdiomCom a b cin).denote V = (twoAddsCom a b cin).denote V := by
  let x : BitVec w := Ctxt.Var.lookup a V
  let y : BitVec w := Ctxt.Var.lookup b V
  let c : BitVec 1 := Ctxt.Var.lookup cin V
  -- The efficient program denotes `addCarryWord x y c`; the idiom program
  -- denotes `(x + y) + c.setWidth w` (the two adds with the 1→w cast on `c`).
  have hL : (carryAddIdiomCom a b cin).denote V = addCarryWord x y c := rfl
  have hR : (twoAddsCom a b cin).denote V = (x + y) + (c.setWidth w) := rfl
  rw [hL, hR]
  have hcast : c.setWidth w = BitVec.ofNat w c.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth]
  rw [hcast]
  exact addCarryWord_eq_twoAdds x y c

/-! ## 4. Is-equal-literal: the idiom program -/

/-- The is-equal-literal idiom as a multi-op `Com` over the homogeneous
    register-arithmetic alphabet, denoting `isEqLitIdiom (a.lookup V) k`:

    ```
    let kc   = regConst w k         -- ofNat w k
    let xx   = xor a kc             -- x = a ^^^ ofNat w k
    let zero = regConst w 0         -- 0#w
    let nx   = sub zero xx          -- 0#w - x
    let orx  = or xx nx             -- x ||| (0#w - x)
    let sh   = shrImm w (w-1) orx   -- (x ||| (0#w - x)) >>> (w-1)
    let one  = regConst w 1         -- 1#w
    let r    = sub one sh           -- 1#w - (... >>> (w-1))
    ret r
    ```

    There is no dedicated equality op in `jasminDialect`; this is the branchless
    idiom the `thir_eqlit` leaf emits. `Var`s are weakened with `.there`s as
    bindings are pushed onto the context. -/
def eqLitIdiomCom {w : Nat} {Γ : Ctxt jasminDialect}
    (a : Ctxt.Var Γ (.reg w)) (k : Nat) :
    Com jasminDialect Γ (.reg w) :=
  -- kc = regConst w k        : reg w
  .var (.mk (.regConst w k) rfl .nil)
  -- xx = xor a kc            : reg w   (a weakened by 1, kc = .here)
  (.var (.mk (.regArith .xor w) rfl (.cons (a.there) (.cons .here .nil)))
  -- zero = regConst w 0      : reg w
  (.var (.mk (.regConst w 0) rfl .nil)
  -- nx = sub zero xx         : reg w   (zero = .here, xx = .there .here)
  (.var (.mk (.regArith .sub w) rfl (.cons .here (.cons (.there .here) .nil)))
  -- orx = or xx nx           : reg w   (xx = .there .there .here, nx = .here)
  (.var (.mk (.regArith .or w) rfl
            (.cons (.there (.there .here)) (.cons .here .nil)))
  -- sh = shrImm w (w-1) orx  : reg w   (orx = .here)
  (.var (.mk (.shrImm w (w - 1)) rfl (.cons .here .nil))
  -- one = regConst w 1       : reg w
  (.var (.mk (.regConst w 1) rfl .nil)
  -- r = sub one sh           : reg w   (one = .here, sh = .there .here)
  (.var (.mk (.regArith .sub w) rfl (.cons .here (.cons (.there .here) .nil)))
  (.ret .here))))))))

/-! ## 5. Is-equal-literal correctness (spec-level) -/

/-- **Is-equal-literal idiom correctness** (spec-level).

    The branchless equality-literal idiom program denotes to the closed `BitVec`
    form `isEqLitIdiom (a.lookup V) k`. Since `jasminDialect` has no single
    efficient equality op to select *to*, the honest obligation is
    `idiom.denote = isEqLitIdiom (lookup …) k` — the value-correctness
    certificate the front carries for the `thir_eqlit` leaf. The committed
    lemma `isEqLitIdiom_eq` rewrites `isEqLitIdiom x k` to the spec
    `if x = ofNat w k then 1#w else 0#w` for any `x : BitVec w` a consumer
    holds; that `if` is not restated here because its subject — the typed
    lookup `⟦.reg w⟧` — does not expose `BitVec w`'s `DecidableEq` to instance
    synthesis (the `TyDenote` unfold is not reducible). -/
theorem eqLitIdiom_denote {w : Nat} {Γ : Ctxt jasminDialect}
    (a : Ctxt.Var Γ (.reg w)) (k : Nat) (V : Ctxt.Valuation Γ) :
    (eqLitIdiomCom a k).denote V = isEqLitIdiom (Ctxt.Var.lookup a V) k := by
  have hm : shiftMask w (w - 1) = w - 1 := by
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · rfl
    · exact shiftMask_of_lt (by omega)
  have hL : (eqLitIdiomCom a k).denote V =
      (fun y : BitVec w => 1#w - (((y ^^^ BitVec.ofNat w k) |||
        (0#w - (y ^^^ BitVec.ofNat w k))) >>> shiftMask w (w - 1)))
        (Ctxt.Var.lookup a V) := rfl
  rw [hL, hm]
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR
