/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Ascent.Corres
public import Mathlib.Tactic.Ring

/-!
# The width-32 word value layer for the ascent calculus (ChaCha / SHA-256 / BLAKE3)

The arithmetic/bitwise value leaves of the ascent calculus (`Ascent.Corres`'s word
layer `wEnc : BitVec 64 ≅ ZMod 2^64` and `SRword`; `Ascent.ExprLeaf`'s
`corres_setExpr`) are hardwired to width **64**. SHA-256, BLAKE3, and ChaCha are
32-bit primitives (RFC 8439 / FIPS 180-4), so they need a width-**32** value layer.
This module delivers the part of that layer the current substrate admits: the
ParamTransfer word representation change at width 32, and its `ZMod 2^32`
value-transfer theorem over the arithmetic `SExpr` fragment.

The port of AutoCorres to Lean — "AutoCorres2 in Lean" — was begun by **Sebastian
Graf** (`sgraf812/ascent`); this module follows that design at width 32.

## What is provable now, and the substrate genericity that is not

The `catCryptDialect` op set and its jasmin lowering are already width-parametric,
and the front lowering has a width-parametric copy (`ScalarSExprWidth32Prototype.
lowerSExprW`). The **ascent** side is not: the `Corres` correspondence runs over
`semScalar`, whose `RScalarSetExpr` arm is hardwired to 64 —

* `SExpr.evalBV : (String → BitVec 64) → SExpr → BitVec 64` (`Jasmin/LowCT.lean`),
* `TranslateDialectScalar.envReader : SEnvScalar → String → BitVec 64` (matches
  only `⟨.sword 64, w⟩` slots),
* `TranslateDialectScalar.semScalar`'s `.RScalarSetExpr x e` arm, which always
  binds `env2.upd x (t := .sword 64) (SExpr.evalBV (envReader env) e)`.

So `semScalar (.RScalarSetExpr x e)` leaves a **`.sword 64`** slot at `x` for every
`e` — never `.sword 32` (`semScalar_setExpr_width64` below pins this precisely). A
genuine `Corres SRword32` leaf for `RScalarSetExpr` is therefore **not** provable
against the current `semScalar`: the post-state contradicts `SRword32`'s `.sword 32`
requirement. Forcing such a leaf would be vacuous, so it is deliberately not stated.
`SRword32` is defined here as the state relation a width-generic substrate would
use, and the exact genericity needed is: a width-parametric `semScalarW w` / `evalBVW
w` / `envReaderW w` (the ascent twin of `lowerSExprW`), after which the value layer
below plugs straight in as the `w = 32` instance.

What IS provable — and delivered — is the value-representation half, which lives
purely in ParamTransfer and has no width baked in:

* the word iso `wEnc32 : BitVec 32 ≅ ZMod 2^32` with its three unconditional
  `RelatedBinOp` squares (`wEncAdd32`/`wEncMul32`/`wEncSub32`) and the derived
  `Param`-engine witnesses;
* the `ZMod 2^32` value transfer `wEnc32_evalBV32_evalZMod32` over the arithmetic
  fragment `IsArithClean32`, the exact 32-bit analogue of `ExprLeaf`'s
  `wEnc_evalBV_evalZMod`, over a self-contained width-32 word evaluator `evalBV32`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open Transfer
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar

/-! ## The width-32 word representation change `BitVec 32 ≅ ZMod 2^32` -/

/-- The width-32 word encoding: `BitVec 32 ↦ ZMod 2^32`. The 32-bit twin of
    `Ascent.wEnc`; unlike it, this is not tied to any `semScalar` step, so it is
    available now even though the ascent substrate is width-64-fixed. -/
def wEnc32 (w : BitVec 32) : ZMod (2 ^ 32) := (w.toNat : ZMod (2 ^ 32))

/-- Wrapping addition realizes `ZMod 2^32` addition — unconditionally. -/
instance wEncAdd32 : Transfer.RelatedBinOp wEnc32 (· + ·) (· + ·) where
  comm x y := by
    simp only [wEnc32, BitVec.toNat_add, Nat.cast_add, ZMod.natCast_mod]

/-- Wrapping multiplication realizes `ZMod 2^32` multiplication — unconditionally. -/
instance wEncMul32 : Transfer.RelatedBinOp wEnc32 (· * ·) (· * ·) where
  comm x y := by
    simp only [wEnc32, BitVec.toNat_mul, Nat.cast_mul, ZMod.natCast_mod]

/-- Wrapping subtraction realizes `ZMod 2^32` subtraction — unconditionally
    (`BitVec 32` is the ring `ZMod 2^32`). -/
instance wEncSub32 : Transfer.RelatedBinOp wEnc32 (· - ·) (· - ·) where
  comm x y := by
    have key : wEnc32 ((x - y) + y) = wEnc32 (x - y) + wEnc32 y := wEncAdd32.comm (x - y) y
    rw [sub_add_cancel] at key
    rw [key]; ring

/-- ParamTransfer's `composeBinOp` transfers a whole width-32 word-op tree through
    `wEnc32` by pure instance resolution — the value-leaf mechanism the ascent
    tactic invokes, now at width 32. -/
example (x y : BitVec 32) : wEnc32 (x * x + y) = wEnc32 x * wEnc32 x + wEnc32 y :=
  (inferInstance : Transfer.Related wEnc32 (x * x + y) (wEnc32 x * wEnc32 x + wEnc32 y)).rel

example (x y z : BitVec 32) : wEnc32 (x * y - z) = wEnc32 x * wEnc32 y - wEnc32 z :=
  (inferInstance : Transfer.Related wEnc32 (x * y - z) (wEnc32 x * wEnc32 y - wEnc32 z)).rel

/-! ## Param-engine witnesses (register once, both engines)

Each `RArrow` witness is derived from the already-registered `RelatedBinOp` square
by `paramWitnessOfRelatedBinOp`, so the `BitVec.toNat_*`/`ZMod` content lives in one
place. Keyed under `HAdd.hAdd`/`HMul.hMul`/`HSub.hSub` at the `BitVec 32` type — the
width-32 counterparts of `Ascent.wEncAddParam` etc. -/

open Transfer.Param

/-- Width-32 word addition, `Param`-engine witness (derived from `wEncAdd32`). -/
@[param] theorem wEncAddParam32 :
    RArrow (encRel wEnc32) (RArrow (encRel wEnc32) (encRel wEnc32))
      (HAdd.hAdd : BitVec 32 → BitVec 32 → BitVec 32)
      (HAdd.hAdd : ZMod (2 ^ 32) → ZMod (2 ^ 32) → ZMod (2 ^ 32)) :=
  paramWitnessOfRelatedBinOp (enc := wEnc32) (op := (· + ·)) (bop := (· + ·))

/-- Width-32 word multiplication, `Param`-engine witness (derived from `wEncMul32`). -/
@[param] theorem wEncMulParam32 :
    RArrow (encRel wEnc32) (RArrow (encRel wEnc32) (encRel wEnc32))
      (HMul.hMul : BitVec 32 → BitVec 32 → BitVec 32)
      (HMul.hMul : ZMod (2 ^ 32) → ZMod (2 ^ 32) → ZMod (2 ^ 32)) :=
  paramWitnessOfRelatedBinOp (enc := wEnc32) (op := (· * ·)) (bop := (· * ·))

/-- Width-32 word subtraction, `Param`-engine witness (derived from `wEncSub32`). -/
@[param] theorem wEncSubParam32 :
    RArrow (encRel wEnc32) (RArrow (encRel wEnc32) (encRel wEnc32))
      (HSub.hSub : BitVec 32 → BitVec 32 → BitVec 32)
      (HSub.hSub : ZMod (2 ^ 32) → ZMod (2 ^ 32) → ZMod (2 ^ 32)) :=
  paramWitnessOfRelatedBinOp (enc := wEnc32) (op := (· - ·)) (bop := (· - ·))

/-- A width-32 word-op tree closed through the `Param` engine. -/
theorem wEncTreeAddParam32 (x y : BitVec 32) :
    wEnc32 (x * x + y) = wEnc32 x * wEnc32 x + wEnc32 y :=
  wEncAddParam32 (x * x) _ (wEncMulParam32 x _ rfl x _ rfl) y _ rfl

/-! ## The arithmetic fragment and its `ZMod 2^32` / `BitVec 32` evaluators

A self-contained width-32 word evaluator `evalBV32` over the arithmetic `SExpr`
fragment (the 32-bit twin of `SExpr.evalBV`, which is width-64-fixed), its
`ZMod 2^32` abstraction `evalZMod32`, and the value transfer between them. Pure
ParamTransfer content: no `semScalar` step, so nothing here needs the missing
width-32 ascent substrate. -/

/-- The arithmetic sub-fragment: variable/literal leaves plus the three ring
    operations. The value-transfer-clean fragment at width 32 — every node has a
    registered `RelatedBinOp wEnc32` square. The bitwise/shift/high-multiply arms
    are excluded (word-faithful but not `ZMod`-ring ops). -/
def IsArithClean32 : SExpr → Prop
  | .SVar _ => True
  | .SLit _ => True
  | .SAdd a b | .SSub a b | .SMul a b => IsArithClean32 a ∧ IsArithClean32 b
  | _ => False

/-- The width-32 word evaluator over the arithmetic fragment (the 32-bit twin of
    `SExpr.evalBV`): variables read the concrete word valuation, literals truncate
    to 32 bits, and the three ring nodes do genuine 32-bit wrapping arithmetic.
    Non-arithmetic arms are `0` (outside `IsArithClean32`). -/
def evalBV32 (β : String → BitVec 32) : SExpr → BitVec 32
  | .SVar x => β x
  | .SLit n => BitVec.ofNat 32 n
  | .SAdd a b => evalBV32 β a + evalBV32 β b
  | .SSub a b => evalBV32 β a - evalBV32 β b
  | .SMul a b => evalBV32 β a * evalBV32 β b
  | _ => 0

/-- The abstract `ZMod 2^32` evaluator for the arithmetic fragment — the clean Lean
    spec the width-32 word expression abstracts to. -/
def evalZMod32 (φ : String → ZMod (2 ^ 32)) : SExpr → ZMod (2 ^ 32)
  | .SVar x => φ x
  | .SLit n => (n : ZMod (2 ^ 32))
  | .SAdd a b => evalZMod32 φ a + evalZMod32 φ b
  | .SSub a b => evalZMod32 φ a - evalZMod32 φ b
  | .SMul a b => evalZMod32 φ a * evalZMod32 φ b
  | _ => 0

/-- **The width-32 word-tree value transfer.** Under a reader that agrees with the
    abstract valuation on every variable (`wEnc32 (β x) = a x`), the `wEnc32`
    encoding of the concrete 32-bit word evaluation of an `IsArithClean32`
    expression equals its abstract `ZMod 2^32` evaluation. The recursion glues the
    `+`/`-`/`*` nodes with the registered `RelatedBinOp wEnc32` squares — the exact
    32-bit analogue of `Ascent.ExprLeaf.wEnc_evalBV_evalZMod`, and the value half a
    `corres_setExpr32` leaf would consume once the width-32 substrate exists. -/
theorem wEnc32_evalBV32_evalZMod32 (β : String → BitVec 32) (a : String → ZMod (2 ^ 32))
    (hread : ∀ x, wEnc32 (β x) = a x) :
    ∀ e, IsArithClean32 e → wEnc32 (evalBV32 β e) = evalZMod32 a e := by
  intro e
  induction e with
  | SVar x => intro _; exact hread x
  | SLit n =>
      intro _
      simp only [evalBV32, evalZMod32, wEnc32, BitVec.toNat_ofNat, ZMod.natCast_mod]
  | SAdd a b iha ihb =>
      intro h
      rw [evalBV32, evalZMod32, wEncAdd32.comm, iha h.1, ihb h.2]
  | SSub a b iha ihb =>
      intro h
      rw [evalBV32, evalZMod32, wEncSub32.comm, iha h.1, ihb h.2]
  | SMul a b iha ihb =>
      intro h
      rw [evalBV32, evalZMod32, wEncMul32.comm, iha h.1, ihb h.2]
  | SAnd a b _ _ => intro h; exact h.elim
  | SXor a b _ _ => intro h; exact h.elim
  | SShl a b _ _ => intro h; exact h.elim
  | SShr a b _ _ => intro h; exact h.elim
  | SMulHiU a b _ _ => intro h; exact h.elim
  | SLt a b _ _ => intro h; exact h.elim
  | SAsr a b _ _ => intro h; exact h.elim
  | SMulS a b _ _ => intro h; exact h.elim
  | SMulHiS a b _ _ => intro h; exact h.elim
  | SLimb v i => intro h; exact h.elim

/-! ## The width-32 state relation and the exhibited substrate gap

`SRword32` is the state relation a width-generic ascent substrate would use for the
32-bit leaf: every name holds a `.sword 32` slot whose `wEnc32` encoding is the
abstract value. It is a legal definition (`SEnvScalar` is heterogeneously typed, so
it can carry `.sword 32` slots). But a `Corres SRword32` leaf for `RScalarSetExpr`
is not provable against the current `semScalar`, because that arm binds `.sword 64`
— `semScalar_setExpr_width64` exhibits the mismatch. -/

/-- The width-32 word-phase state relation: every name holds a `.sword 32` whose
    `wEnc32` encoding is the abstract `ZMod 2^32` value. The target relation for a
    future `corres_setExpr32`; the value transfer above supplies its value half. -/
def SRword32 (env : SEnvScalar) (a : String → ZMod (2 ^ 32)) : Prop :=
  ∀ x, ∃ w : BitVec 32, env x = some ⟨.sword 32, w⟩ ∧ wEnc32 w = a x

/-- **The exhibited substrate gap.** For every `e`, whenever `semScalar
    (.RScalarSetExpr x e)` succeeds, the resulting slot at `x` is a `.sword 64`
    word — never `.sword 32`. This is exactly why no `Corres SRword32` leaf for
    `RScalarSetExpr` holds against the current `semScalar`: its post-state
    contradicts `SRword32`'s `.sword 32` requirement. Closing the 32-bit ascent
    leaf needs a width-parametric `semScalarW`/`evalBVW`/`envReaderW`, after which
    the value layer above is the `w = 32` instance. -/
theorem semScalar_setExpr_width64 (x : String) (e : SExpr) (env env' : SEnvScalar)
    (h : semScalar (.RScalarSetExpr x e) env = some env') :
    ∃ w : BitVec 64, env' x = some ⟨.sword 64, w⟩ := by
  simp only [semScalar] at h
  split at h
  · rename_i env2 _ _ _
    refine ⟨SExpr.evalBV (envReader env) e, ?_⟩
    rw [← Option.some.inj h]
    simp [SEnvScalar.upd]
  · exact absurd h (by simp)

end CatCrypt.Crypto.SecureCompilation.Ascent
