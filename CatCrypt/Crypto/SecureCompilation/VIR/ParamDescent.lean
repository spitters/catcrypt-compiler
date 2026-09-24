/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import Transfer

/-!
# Certifying dialect-lowering descent squares with ParamTransfer

The owned-emit pipeline lowers a `Com catCryptDialect` to a `Com jasminDialect`
via `DialectToJasminCom.cryptoDialectToJasminCom`, and the lowering's
denotation-preservation (`cryptoDialectToJasminCom_denote_eq`) is reduced — by
program induction — to a **per-leaf agreement square**
(`DialectJasminLeafAgrees`): for each lowered op, the Jasmin op denotation on the
transported operands equals the `ctTransTy`-transport of the source-dialect op
denotation. On the `regArith` fragment (`bvAdd/Sub/Mul/And/Or/Xor`) that square
is the commuting equation

```
ctTransTy (catCryptDenote.denote ⟨bvOp w⟩ ⟨a, b⟩)
  = jasminDenote.denote ⟨regArith bop w⟩ ⟨a, b⟩
```

with `ctTransTy = id` on `sword` (`ctTransTy_sword`) and `mapTy (.sword w) =
.reg w`, both denoting `BitVec w`. So the encoding is the **identity** on
`BitVec w`, and the square is exactly a Trocq `RelatedBinOp`:

```
enc (op_src a b) = op_tgt (enc a) (enc b),    enc = id.
```

This module is an architecture proof of concept: it
**registers those descent squares as `Transfer.RelatedBinOp` instances** and
discharges the lowering correctness of a *composite* op-tree with the
ParamTransfer engine's `param_solve` tactic, instead of a bespoke per-kernel
`*_lowering_denote` proof. The `RelatedBinOp` witnesses are computed from the
**real** dialect denotation instances `catCryptDenote` / `jasminDenote` (not a
self-authored spec), so the square carries the leaf-agreement content; the
descent through a composite is then synthesized by the engine.

ParamTransfer is a required `lake` dependency, used elsewhere by the
`Bridges/ReprTransfer*` proof-transfer layer (KZG/STARK/Halo2/Binius). Here it
enters the **owned-emit compiler descent**.

## Scope

* This certifies the `regArith` *leaf squares* and the *descent through a
  composite op-tree* of them, with the identity encoding. That is precisely the
  fragment `cryptoDialectToJasminCom`'s `DialectJasminLeafAgrees` discharges
  definitionally — the part where `param_solve` takes the place of the hand proof.
* It does **not** replace the `Com`-level program induction
  (`cryptoDialectToJasminCom_denote_eq`), the De Bruijn valuation transport
  (`ctMapValD_lookup`/`_extend`), or the `extCall` opaque-default leaf. Those are
  the binder/structural and opaque-leaf layers the engine's term translation
  `⟦·⟧` would need to be lifted to (see the scalability note at the foot of the
  file).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ParamDescent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open Transfer

/-! ## 1. Value-level op denotations, read off the REAL dialect instances

We extract the source/target op meaning by applying the dialect's own
`DialectDenote.denote` instance to a concrete two-operand `HVector`. These are
not new specifications — they are the exact denotations the leaf-agreement
square in `DialectToJasminComCorrect.lean` runs. -/

/-- The source-dialect denotation of a binary `sword w` op (whose signature is
    `[.sword w, .sword w] → .sword w`), applied to two operands. Computed from
    the real `catCryptDenote` instance. The `(op, hsig, hret)` triple lets us
    apply the instance whose `denote` is typed by `⟦ret op⟧`/`⟦sig op⟧`; on a
    concrete arithmetic op the two hypotheses are `rfl` and the whole thing
    reduces to the `BitVec` operation. -/
def srcDenote (op : CatCryptOp) (w : Nat)
    (hsig : DialectSignature.sig (d := catCryptDialect) op = [.sword w, .sword w])
    (hret : (⟦DialectSignature.ret (d := catCryptDialect) op⟧ : Type) = BitVec w)
    (a b : BitVec w) : BitVec w :=
  hret ▸ DialectDenote.denote (self := catCryptDenote) op
    (hsig ▸ (HVector.cons a (HVector.cons b HVector.nil)))

/-- The target-Jasmin denotation of `regArith bop w`, applied to two operands.
    Computed from the real `jasminDenote` instance. Its result type
    `⟦ret (regArith bop w)⟧ = ⟦.reg w⟧` is definitionally `BitVec w`. -/
def tgtDenote (bop : JasminBinOp) (w : Nat) (a b : BitVec w) : BitVec w :=
  DialectDenote.denote (self := jasminDenote) (JasminOp.regArith bop w)
    (HVector.cons a (HVector.cons b HVector.nil))

/-! The three arithmetic op denotations compute the expected `BitVec` operation.
These are `rfl` — the dialect denotation instance is definitional on these
arms — so they are leaf-agreement equations rather than assumptions. -/

@[simp] theorem srcDenote_bvAdd (w : Nat) (a b : BitVec w) :
    srcDenote (.bvAdd w) w rfl rfl a b = a + b := rfl

@[simp] theorem srcDenote_bvMul (w : Nat) (a b : BitVec w) :
    srcDenote (.bvMul w) w rfl rfl a b = a * b := rfl

@[simp] theorem srcDenote_bvXor (w : Nat) (a b : BitVec w) :
    srcDenote (.bvXor w) w rfl rfl a b = a ^^^ b := rfl

@[simp] theorem tgtDenote_add (w : Nat) (a b : BitVec w) :
    tgtDenote .add w a b = a + b := rfl

@[simp] theorem tgtDenote_mul (w : Nat) (a b : BitVec w) :
    tgtDenote .mul w a b = a * b := rfl

@[simp] theorem tgtDenote_xor (w : Nat) (a b : BitVec w) :
    tgtDenote .xor w a b = a ^^^ b := rfl

/-! ## 2. The descent squares as `RelatedBinOp` witnesses (identity encoding)

`ctTransTy = id` on `sword` (`CryptoToJasminComCorrect.ctTransTy_sword`) and both
`⟦.sword w⟧` and `⟦mapTy (.sword w)⟧ = ⟦.reg w⟧` are `BitVec w`, so the
leaf-agreement square is `id (srcDenote …) = tgtDenote … (id a) (id b)` — a
`Transfer.RelatedBinOp` at the identity encoding `id : BitVec w → BitVec w`.

Each instance's `comm` field is the commuting square, proved by reducing both
denotations (definitional). This is the witness the Trocq engine consumes; it is
never invented — it is the real per-op leaf agreement. -/

variable (w : Nat)

/-- The `bvAdd` lowering square: the source-dialect add realizes the Jasmin
    `regArith add` add, under the identity encoding. -/
instance addDescentSquare :
    RelatedBinOp (id : BitVec w → BitVec w)
      (srcDenote (.bvAdd w) w rfl rfl) (tgtDenote .add w) where
  comm a b := by simp

/-- The `bvMul` lowering square. -/
instance mulDescentSquare :
    RelatedBinOp (id : BitVec w → BitVec w)
      (srcDenote (.bvMul w) w rfl rfl) (tgtDenote .mul w) where
  comm a b := by simp

/-- The `bvXor` lowering square. -/
instance xorDescentSquare :
    RelatedBinOp (id : BitVec w → BitVec w)
      (srcDenote (.bvXor w) w rfl rfl) (tgtDenote .xor w) where
  comm a b := by simp

/-! ## 3. The certified squares — discharged by `param_solve`, not a hand proof

### 3a. A single leaf square

The lowering correctness of one `bvAdd` leaf — that the Jasmin add denotation
equals the (identity-transported) source add denotation — closed by the engine
rather than by `rfl`/`simp` on the denotations. -/

/-- **Single-leaf descent, certified by ParamTransfer.** The lowering square for
    `bvAdd` is discharged by `param_solve` consuming the registered
    `addDescentSquare` witness — the engine path, replacing a bespoke
    `bvAdd_lowering_denote`. -/
theorem bvAdd_leaf_certified (a b : BitVec w) :
    srcDenote (.bvAdd w) w rfl rfl a b = tgtDenote .add w a b := by
  param_solve

/-! ### 3b. A composite op-tree — the full descent

`(a * b) + c` in the source dialect lowers to `tgtAdd (tgtMul a b) c` in Jasmin.
`param_solve` **descends** through the cross-head op-tree (`bvAdd`↔`regArith add`
node, then `bvMul`↔`regArith mul` node), discharging each node by its registered
square and the leaves by the identity. This is the whole point: one tactic
certifies an arbitrary composite of registered lowering squares, so each new
kernel's lowering is `param_solve`, not a new induction. -/

/-- **Composite descent, certified by ParamTransfer.** The lowering of the
    op-tree `(a*b)+c` is synthesized by `param_solve` from the registered
    per-op squares — the generic descent the architecture wants. -/
theorem mulAdd_composite_certified (a b c : BitVec w) :
    srcDenote (.bvAdd w) w rfl rfl (srcDenote (.bvMul w) w rfl rfl a b) c
      = tgtDenote .add w (tgtDenote .mul w a b) c := by
  param_solve

/-- A three-op composite `(a*b) + (c*d)` exercising two `mul` nodes under an
    `add` node — closed by the same single `param_solve` descent. -/
theorem mulMulAdd_composite_certified (a b c d : BitVec w) :
    srcDenote (.bvAdd w) w rfl rfl
        (srcDenote (.bvMul w) w rfl rfl a b)
        (srcDenote (.bvMul w) w rfl rfl c d)
      = tgtDenote .add w (tgtDenote .mul w a b) (tgtDenote .mul w c d) := by
  param_solve

/-! ## 4. Relation to the hand-proven square + scalability

`bvAdd_leaf_certified` is the same content as the `regArith` arm of
`DialectToJasminCom`'s `DialectJasminLeafAgrees` discharge (`§6` of
`DialectToJasminComCorrect.lean`), but obtained through the ParamTransfer engine:
the per-op commuting squares are *registered* (`addDescentSquare` etc.) and the
descent is *synthesized* (`param_solve`). Adding a new lowered arithmetic op is a
one-line `instance … : RelatedBinOp …`; its composites then certify for free.

**Can this scale to the full `compileVia` descent?** Honest assessment:

* **Yes for the straight-line `regArith` leaf fragment and its op-trees** — the
  registered-square + `param_solve` shape is exactly right, and is the part the
  hand proof discharges definitionally. The engine *generalizes* the descent
  (any composite, no new lemma).
* **Missing: the binder/program layer.** `cryptoDialectToJasminCom_denote_eq` is
  a `Com` induction with a De Bruijn valuation transport (`ctMapValD_extend`)
  threaded through `.var`/`.ret`. `RelatedBinOp` is first-order (closed op-trees,
  no binders). Lifting `param_solve` to the program level needs the engine's
  dependent-Π / `forallTransfer` layer (`ParamForall`, `ParamForallNested`) to
  carry a `Related` through the `Ctxt.Valuation.extend`, i.e. a `Related` on
  *valuations* and a congruence for `Com.var`. The hierarchy (`Param map_k`) has
  the levels; what's absent is a registered `Com`-congruence head pair (an
  `hgcongr` correspondence for `.var`/`.ret`) and the valuation relation. This is
  the documented next step, not a wall.
* **Missing: the opaque `extCall` leaf.** Its square is parametric (both sides
  the canonical default, tied by `ctTransTy_default`), not an encoding equation;
  it fits the relation-generic residual `param_solve`'s module docstring flags,
  and would register as a `map0`/`map2a` `Param` rather than a `RelatedBinOp`.

**Composition with a high-dialect RelationalCompile front.** A RelationalCompile
front that emits its correctness as a `Related`/`Param` between the high-dialect
and `catCryptDialect` denotations composes with this layer by
`Transfer.Param.Param_trans` (relation composition, `map0`–`map3`): front
`Related high catCrypt` ∘ this `Related catCrypt jasmin` = `Related high jasmin`,
the end-to-end descent square, with no new hand proof — provided both expose
their squares as registered witnesses over a shared encoding. That transitive
composition is the architecture payoff both enablers are building toward. -/

end CatCrypt.Crypto.SecureCompilation.VIR.ParamDescent
