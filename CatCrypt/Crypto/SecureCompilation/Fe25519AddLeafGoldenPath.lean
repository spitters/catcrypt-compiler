/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.CtMemoryGoldenPath
public import CatCrypt.Crypto.SecureCompilation.CtMemoryGoldenPath
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ComInlineCall
public import CatCrypt.Crypto.SecureCompilation.VIR.ComInlineCall

/-!
# Golden path: the fe25519 field-add leaf as a word-level `Com jasminDialect`

The X25519 byte-level milestone walled because the deployed fe25519 field-op leaves
(`fe25519_{mul,sqr,add,sub,mul121666}`) ship as hand-authored `List (JInstr 64)`
blocks (MULX/ADCX/ADOX), not as `Com jasminDialect`. The MLIR-extension inlining
toolkit — `ComInlineCall.inlineCallCom` / `inlineCallCom_denote` — consumes a
*callee `Com jasminDialect`*, so a byte-level realization needs every field leaf
re-expressed as a front-generated `Com` whose denote is the field-op spec. This file
supplies the **simplest** such leaf, `fe25519_add`, on the golden path
(`FieldEmitGoldenPath` / `FieldSubBorrowGoldenPath` style: write the op as a `Com`,
prove `denote = spec`, no hand-authored bytes).

## Representation: radix 2⁵¹ (HACL\* `Curve25519_51`, the reference X25519)

A field element is five 64-bit limbs, `Fin 5 → BitVec 64`, each holding a
radix-2⁵¹ digit with headroom. In this representation **field addition is pointwise
per-limb** — `r i = a i + b i`, *no inter-limb carry, no reduction* — because the
spare bits absorb the growth (the lazy reduction happens later, inside `mul`/`sqr`).
This is exactly why HACL\* uses radix 2⁵¹: `add`/`sub` are carry-free. So the whole
field add is one word op (`regArith .add 64`) iterated over the five limbs, and the
minimal word-level generator is the **per-limb kernel** `fe25519Add51LimbCom`: load
`a[i]`, load `b[i]`, add. The array-shaped leaf is this kernel run over `i = 0..4`
through the (a) memref-loop carrier (`JasminLsemMemSourceTieWide.loopWide_export_faithful`).

The word op and the integer-reconstruction spec are curve-independent field
arithmetic — reusable by every EC curve that carries a reduced-radix field element.

## What is proved (all goals closed)

* `fe25519Add51LimbCom` — the per-limb add kernel as a `Com jasminDialect` over
  `[A, B, i]`, all in the `stackLoad`/`regArith .add` alphabet.
* `fe25519Add51LimbCom_denote` — `denote = stackGet A i + stackGet B i`, by `rfl`
  (the golden-path value step: the source's value is the functional field-add limb).
* `feAdd51_reconstruct` — the field-add SPEC: the pointwise limb sum reconstructs the
  exact integer sum `feToNat51 (a + b) = feToNat51 a + feToNat51 b`, under the
  radix-2⁵¹ no-wrap limb bound.
* `fe25519AddLimbFb` / `fe25519AddLimb_inlineCallCom_denote` — the leaf packaged as a
  `ComInlineCall.FunBodyN` and consumed by the (b) inliner `inlineCallCom_denote`:
  the inlined call-free program binds exactly the per-limb field-add value at the
  call site.

No open goals, no `native_decide`, no new axioms.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Fe25519AddLeaf

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComInlineCall

/-! ## 1. The radix-2⁵¹ field-element representation and the pointwise add spec -/

/-- A radix-2⁵¹ fe25519 field element: five 64-bit limbs. -/
abbrev Fe51 := Fin 5 → BitVec 64

/-- The integer value of a radix-2⁵¹ field element (five limbs, digit weight 2⁵¹). -/
def feToNat51 (f : Fe51) : Nat :=
  (f 0).toNat + (f 1).toNat * 2 ^ 51 + (f 2).toNat * 2 ^ 102
    + (f 3).toNat * 2 ^ 153 + (f 4).toNat * 2 ^ 204

/-- The pointwise field-add spec: radix-2⁵¹ add is carry-free, `r i = a i + b i`. -/
def feAdd51 (a b : Fe51) : Fe51 := fun i => a i + b i

/-- **The field-add spec reconstruction.** Under the radix-2⁵¹ no-wrap bound
    (each limb sum fits in a word — guaranteed by the ~11-bit headroom of the
    representation), the pointwise limb sum reconstructs the exact integer sum.
    This is the curve-independent correctness of the pointwise field add. -/
theorem feAdd51_reconstruct (a b : Fe51)
    (hb : ∀ i : Fin 5, (a i).toNat + (b i).toNat < 2 ^ 64) :
    feToNat51 (feAdd51 a b) = feToNat51 a + feToNat51 b := by
  simp only [feToNat51, feAdd51]
  have h : ∀ i : Fin 5, (a i + b i).toNat = (a i).toNat + (b i).toNat := by
    intro i
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (hb i)
  rw [h 0, h 1, h 2, h 3, h 4]
  ring

/-! ## 2. The per-limb add kernel as a word-level `Com jasminDialect`

`fe25519Add51LimbCom` over `[A : stackArr 64 5, B : stackArr 64 5, i : reg 64]`:
`ai := A[i] ; bi := B[i] ; s := ai + bi ; ret s`. Two `stackLoad`s and one
`regArith .add`, all on the golden-path alphabet. Since radix-2⁵¹ add is pointwise,
this per-limb kernel *is* the fe25519 add arithmetic (iterated over the five limbs). -/

/-- The per-limb fe25519 add kernel: `A[i] + B[i]`. -/
def fe25519Add51LimbCom :
    Com jasminDialect [.stackArr 64 5, .stackArr 64 5, .reg 64] (.reg 64) :=
  -- ai := A[i]      (A = .here, i = .there.there.here)
  .var { op := .stackLoad 64 5, retTy_eq := rfl,
         args := .cons .here (.cons (.there (.there .here)) .nil) }
  -- bi := B[i]      (B = .there.there.here, i = .there.there.there.here)
  (.var { op := .stackLoad 64 5, retTy_eq := rfl,
          args := .cons (.there (.there .here))
                    (.cons (.there (.there (.there .here))) .nil) }
  -- s := ai + bi    (ai = .there.here, bi = .here)
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there .here) (.cons .here .nil) }
    (.ret .here)))

/-- **Step value — `rfl`.** The per-limb source denotes the functional field-add
    limb `A[i] + B[i]` (the radix-2⁵¹ pointwise add value). -/
theorem fe25519Add51LimbCom_denote (a b : Fin 5 → BitVec 64) (i : BitVec 64) :
    Com.denote fe25519Add51LimbCom (.cons a (.cons b (.cons i .nil)))
      = stackGet a i.toNat + stackGet b i.toNat := rfl

/-! ## 3. The leaf packaged for the (b) inliner, and consumed by it

`ComInlineCall.inlineCallCom` splices a statically-known callee `Com` at a call
site; `inlineCallCom_denote` is its (leaf-agnostic) denotation law. Packaging the
per-limb kernel as a `FunBodyN` and feeding it through `inlineCallCom_denote` shows
the inlined **call-free** program binds exactly the per-limb field-add value — i.e.
the (b) toolkit consumes this front-generated leaf. -/

/-- The fe25519 add per-limb leaf as a `FunBodyN` (formals, return type, body). -/
def fe25519AddLimbFb : FunBodyN where
  argTys := [.stackArr 64 5, .stackArr 64 5, .reg 64]
  retTy  := .reg 64
  body   := fe25519Add51LimbCom

/-- **(b) consumes the leaf.** For any caller context `Γ`, call args, and
    continuation `body`, inlining the fe25519-add per-limb leaf yields a call-free
    `Com` whose denotation binds exactly the leaf's per-limb field-add value at the
    call site — a direct instance of `ComInlineCall.inlineCallCom_denote` on this
    front-generated leaf body. -/
theorem fe25519AddLimb_inlineCallCom_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (args : HVector (fun ty => Ctxt.Var Γ ty) fe25519AddLimbFb.argTys)
    (body : Com jasminDialect (fe25519AddLimbFb.retTy :: Γ) t)
    (V : Ctxt.Valuation Γ) :
    (inlineCallCom fe25519AddLimbFb.body args body).denote V
      = body.denote (Ctxt.Valuation.extend V
          (fe25519AddLimbFb.body.denote (Expr.lookupArgs args V))) :=
  inlineCallCom_denote fe25519AddLimbFb.body args body V

-- Note: `fe25519_add`'s named-call inlining is consumed non-vacuously via the leaf-agnostic
-- `inlineCallCom_denote` (above) and the separate `FuncRegistryN`/`RegistryConsistentN`
-- registry — NOT via a `jasminExtSem` arm. `jasminExtSem` stays the opaque oracle (all
-- width-64 returns = `default`, the invariant `JasminValTransport.jasminExtSem_reg`/
-- `jasminExtSem_stackArr64` and `DialectToJasminComCorrect` rely on); only width-16 lattice
-- leaves are non-default there.

end CatCrypt.Crypto.SecureCompilation.Fe25519AddLeaf
