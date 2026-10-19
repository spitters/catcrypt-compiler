/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminValTransport
public import CatCrypt.Crypto.SecureCompilation.VIR.DialectLoweringTransport

/-!
# `cryptoDialectToJasminCom` is denotation-preserving — UNDER leaf agreement

This file proves that the lowering
`cryptoDialectToJasminCom : Com catCryptDialect → Com jasminDialect` (from
`DialectToJasminCom.lean`) preserves `Com.denote`.

## Statement shape

`Com catCryptDialect` denotes into a plain value (`catCryptDenote` is a pure
`DialectDenote`), exactly like `Com jasminDialect`. So the statement is the
plain-value commuting square

    (cryptoDialectToJasminCom com).denote (ctMapValD V) = ctTransTy (com.denote V)

with **no** `SPComp` threading — the same shape as
`LatticeToJasminDenote.lowerLatticeToJasmin_denote_eq` (which is the structural
template followed here), specialised to the `Option`-valued front.

## Shared pieces

Because `catCryptDialect.Ty = CryptoTy`, a `Com catCryptDialect`'s De Bruijn
context `Γ : Ctxt catCryptDialect` *is* `CryptoSSA.Ctx = List CryptoTy`, with
the `mapTy`/`mapCtx` of `CryptoToJasminCom`. So the per-value
transport `ctTransTy` (and `ctTransTy_sword`/`ctTransTy_memref`/`ctTransTy_default`)
is imported from `JasminValTransport` (namespace `CryptoToJasminComCorrect`). This
module defines the **valuation** transport `ctMapValD` (over `Ctxt.Valuation`),
its lookup/extend commute lemmas, and the dialect-`Expr`-shaped leaf-agreement
predicate `DialectJasminLeafAgrees`.

## Scope

* `ctMapValD` / `ctMapValD_lookup` / `ctMapValD_extend` — the dialect valuation
  transport and its commute lemmas over `Ctxt.Var`.
* `DialectJasminLeafAgrees` — the per-`Expr` leaf-agreement predicate over
  `toJExprD`, threaded through the induction.
* `cryptoDialectToJasminCom_denote_eq` — the **general** parametric preservation
  theorem, by induction on the `Com`.
* `dialectJasminLeafAgrees_holds` — the *unconditional* discharge of the leaf
  predicate over the lowered fragment (arith/const leaves agree by computation;
  `extCall` leaves agree on the opaque canonical default via `ctTransTy_default`).
* `cryptoDialectToJasminCom_denote_eq'` — the hypothesis-free corollary.
* `regPassA1prime` — the result repackaged as a `DialectLoweringTransport`
  `TransportSquare`, composable in `CompilerLoweringRegistry`.

All proofs are complete. A concrete leaf-spec'd Jasmin `extCall` denotation (a
*functional* leaf, carried per-protocol) is a separate, stronger discharge
(`DialectToJasminComLeaf`); the stub denotation the meta-theorem uses is closed
here on the opaque default.
-/

@[expose] public section

set_option autoImplicit true -- SSA IR front: many context/type variables

namespace CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminCom
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect
  (ctTransTy ctTransTy_sword ctTransTy_memref ctTransTy_memrefW ctTransTy_default
   jasminExtSem_reg jasminExtSem_stackArr64)

/-! ## 1. The dialect valuation transport `ctMapValD`

We reuse the per-value transport `ctTransTy` from `CryptoToJasminComCorrect`
verbatim (it is keyed on `CryptoTy`/`mapTy`, which `catCryptDialect` shares). The
*valuation* transport is over `Ctxt.Valuation` (the dialect's
`HVector`-based valuation), so we define `ctMapValD`
— the `Ctxt.Valuation` analogue of `LatticeToJasminDenote.mapVal`. -/

/-- Transport a `catCryptDialect` valuation to the `mapTy`-mapped Jasmin context,
    applying `ctTransTy` per binding. -/
def ctMapValD {Γ : Ctx} :
    Ctxt.Valuation (d := catCryptDialect) Γ →
    Ctxt.Valuation (d := jasminDialect) (mapCtx Γ)
  | .nil => .nil
  | .cons (t := t) v rest => .cons (ctTransTy (t := t) v) (ctMapValD rest)

/-! ## 2. `ctMapValD` commutes with variable lookup

`(toJVarD v).lookup (ctMapValD V) = ctTransTy (v.lookup V)`. Both sides have Lean
type `⟦mapTy s⟧`. Proved by induction on the variable — the `Ctxt.Var`-shaped
analogue of `ctMapVal_lookup`. -/

/-- Variable lookup commutes with the valuation transport: looking up the
    translated dialect variable in the transported valuation yields `ctTransTy` of
    looking up the original variable. -/
theorem ctMapValD_lookup {Γ : Ctx} {s : CryptoTy} :
    (v : Ctxt.Var (d := catCryptDialect) Γ s) →
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) →
    (toJVarD v).lookup (ctMapValD V) = ctTransTy (v.lookup V)
  | .here, .cons _ _ => rfl
  | .there v, .cons _ rest => ctMapValD_lookup v rest

/-! ## 3. `ctMapValD` commutes with valuation extension

`ctMapValD (V.extend x) = (ctMapValD V).extend (ctTransTy x)`. Holds by `rfl`:
`Valuation.extend` is `.cons`, and `ctMapValD` is the matching `.cons`. -/

/-- `ctMapValD` commutes with valuation extension via `ctTransTy` on the new
    value. By `rfl`. -/
theorem ctMapValD_extend {Γ : Ctx} {t : CryptoTy}
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (x : CryptoTy.denote t) :
    ctMapValD (V.extend x) = (ctMapValD V).extend (ctTransTy (t := t) x) :=
  rfl

/-! ## 4. The leaf-agreement hypothesis

For one dialect expression `e` in the lowered fragment (`toJExprD e = some e'`),
the Jasmin lowering `e'` denotes (under the transported valuation) to the
`ctTransTy`-transport of `e`'s denotation. Both sides are plain values (no
`SPComp`), so the statement is the commuting square — no purity read-off.

This is the *parametric* hypothesis: the Jasmin `extCall` denotation here is a
stub, so we abstract over the fact that it agrees with the dialect op. A
concrete leaf-spec'd `extCall` semantics discharges it per leaf. -/

/-- Per-expression leaf agreement, quantified over all
    contexts/types/expressions/valuations so it slots into the program
    induction. For any `e` the front lowers to `e'`, the lowered Jasmin
    expression denotes to `ctTransTy` of `e`'s denotation. -/
def DialectJasminLeafAgrees : Prop :=
  ∀ {Γ : Ctx} {t : CryptoTy}
    (e : Expr catCryptDialect Γ t)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (e' : Expr jasminDialect (mapCtx Γ) (mapTy t)),
    toJExprD e = some e' → e'.denote (ctMapValD V) = ctTransTy (e.denote V)

/-! ## 5. The general preservation theorem

By induction on the `Com`. The `.ret` case is exactly `ctMapValD_lookup`; the
`.var` case uses `DialectJasminLeafAgrees` for the bound expression and the IH
for the body, with the `ctMapValD_extend` commute step. The `Option`/fragment
threading splits on the two `toJExprD` / recursive `cryptoDialectToJasminCom`
matches and the `none` branches are vacuous. -/

/-- **Preservation (general), parametric over leaf agreement.** Under the leaf
    agreement hypothesis `hLeaf`, `cryptoDialectToJasminCom` preserves denotation: whenever the front succeeds
    (`cryptoDialectToJasminCom com = some jcom`), the lowered Jasmin program on
    the transported valuation denotes to `ctTransTy` of the source dialect
    program's denotation.

    Since `ctTransTy` is the (computed) identity transport on the register/array
    forms that the lowered fragment produces, this states that the lowering
    preserves the denotation. -/
theorem cryptoDialectToJasminCom_denote_eq
    (hLeaf : DialectJasminLeafAgrees)
    {Γ : Ctx} {t : CryptoTy} :
    (com : Com catCryptDialect Γ t) →
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) →
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t)) →
    cryptoDialectToJasminCom com = some jcom →
    jcom.denote (ctMapValD V) = ctTransTy (com.denote V)
  | .ret v, V, jcom, hcom => by
      simp only [cryptoDialectToJasminCom, Option.some.injEq] at hcom
      subst hcom
      show (toJVarD v).lookup (ctMapValD V) = _
      exact ctMapValD_lookup v V
  | .var e body, V, jcom, hcom => by
      simp only [cryptoDialectToJasminCom] at hcom
      split at hcom
      · next e' he =>
          split at hcom
          · next body' hbody =>
              simp only [Option.some.injEq] at hcom
              subst hcom
              show body'.denote ((ctMapValD V).extend (e'.denote (ctMapValD V))) = _
              rw [hLeaf e V e' he, ← ctMapValD_extend V (e.denote V)]
              exact cryptoDialectToJasminCom_denote_eq hLeaf body
                (V.extend (e.denote V)) body' hbody
          · exact absurd hcom (by simp)
      · exact absurd hcom (by simp)

/-! ## 6. Unconditional discharge of `DialectJasminLeafAgrees`

The lowered fragment `toJExprD` accepts the same shapes `toJExpr` does: the six
`regArith` ops (`bvAdd/Sub/Mul/And/Or/Xor`), `bvConst → regConst`, and
`extCall → extCall`. On the `regArith`/`regConst` shapes the source dialect op
denotation and the jasmin op denotation compute the *same* `BitVec` operation, so
agreement is definitional after running both `Expr.denote`s. On `extCall` both
sides are the opaque canonical default (`CryptoTy.default retTy` resp.
`JasminTy.default (mapTy retTy)`), transported by `ctTransTy_default`. Every other
dialect op is outside the fragment (`toJExprD = none`), so the
`toJExprD e = some e'` premise is unsatisfiable and the case is vacuous.

The dialect-`Expr` constructor `Expr.mk op retTy_eq args` carries its `op` in a
field, and `toJExprD` matches `h : e.op`. So we case the proof on `e.op` (via the
generic `Expr` destructured as `⟨op, hop, args⟩`) and reduce `toJExprD`
accordingly. The dialect denotation threads the `retTy_eq ▸ …` cast and the `DialectDenote.denote` instance, which we
discharge with `simp [Expr.denote, …]` per op shape. -/

/-- The lowered jasmin `extCall` for a leaf returning a `sword`/`memref`-mapped
    type denotes to the jasmin canonical default — the dialect-`Expr` analogue of
    `CryptoToJasminComCorrect.extCall_denote_default`. `mapTy` produces only
    `.reg w` / `.stackArr 64 n`, and `jasminExtSem`'s non-default branches are all
    `.stackArr 16`, so the leaf falls through to `JasminTy.default`. -/
theorem extCallD_denote_default
    {Γ : Ctx} {retTy : CryptoTy} {argTys : List CryptoTy}
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) argTys)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (name : String)
    (e' : Expr jasminDialect (mapCtx Γ) (mapTy retTy))
    (he : toJExprD (Γ := Γ)
      ⟨CatCryptOp.extCall name argTys retTy, rfl, args⟩ = some e') :
    e'.denote (ctMapValD V) = JasminTy.default (mapTy retTy) := by
  cases retTy with
  | memrefW w n => simp only [toJExprD, reduceCtorEq] at he
  | sword w =>
      simp only [toJExprD, Option.some.injEq] at he; subst he
      exact jasminExtSem_reg _ _ _ _
  | bit =>
      simp only [toJExprD, Option.some.injEq] at he; subst he
      exact jasminExtSem_reg _ _ _ _
  | unit =>
      simp only [toJExprD, Option.some.injEq] at he; subst he
      exact jasminExtSem_reg _ _ _ _
  | pair a b =>
      simp only [toJExprD, Option.some.injEq] at he; subst he
      exact jasminExtSem_reg _ _ _ _
  | sum a b =>
      simp only [toJExprD, Option.some.injEq] at he; subst he
      exact jasminExtSem_reg _ _ _ _
  | memref n =>
      simp only [toJExprD, Option.some.injEq] at he; subst he
      exact jasminExtSem_stackArr64 _ _ _ _

/-- The source dialect `extCall` denotes to the opaque canonical default
    `CryptoTy.default retTy` (the `catCryptDenote` leaf is the deterministic opaque
    oracle). -/
theorem extCallD_src_denote
    {Γ : Ctx} {retTy : CryptoTy} {argTys : List CryptoTy}
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) argTys)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (name : String) :
    (Expr.denote (d := catCryptDialect)
      ⟨CatCryptOp.extCall name argTys retTy, rfl, args⟩ V) = CryptoTy.default retTy :=
  rfl

/-- **Pilot leaf discharge (extCall).** The opaque-leaf jasmin `extCall`
    denotation agrees with the opaque-leaf dialect `extCall` denotation on every
    leaf the front lowers: both are the canonical default, transported by
    `ctTransTy_default`. The dialect analogue of
    `CryptoToJasminComCorrect.leafAgrees_extCall`. No axiom, no open goals. -/
theorem leafAgrees_extCallD
    {Γ : Ctx} {retTy : CryptoTy} {argTys : List CryptoTy}
    (args : HVector (fun ty => Ctxt.Var (d := catCryptDialect) Γ ty) argTys)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (name : String)
    (e' : Expr jasminDialect (mapCtx Γ) (mapTy retTy))
    (he : toJExprD (Γ := Γ)
      ⟨CatCryptOp.extCall name argTys retTy, rfl, args⟩ = some e') :
    e'.denote (ctMapValD V)
      = ctTransTy (Expr.denote (d := catCryptDialect)
          ⟨CatCryptOp.extCall name argTys retTy, rfl, args⟩ V) := by
  rw [extCallD_src_denote args V name,
    extCallD_denote_default args V name e' he]
  exact ctTransTy_default.symm

/-! ## 7. Hypothesis-free corollary

With `dialectJasminLeafAgrees_holds` in hand, the general preservation theorem no
longer needs to assume leaf agreement. This is the unconditional form a
downstream caller wants. -/

/-- The jasmin runtime-indexed load `JasminDialect.stackGet` agrees pointwise with
    the dialect runtime-indexed load `CatCryptDialect.memGetDyn`: the two are
    defined identically (total mod-`n` access), so they agree by `cases n <;> rfl`.
    This bridges the `memrefGetDyn → stackLoad` lowering's denotation. -/
theorem stackGet_eq_memGetDyn {n : Nat} (arr : Fin n → BitVec 64) (k : Nat) :
    JasminDialect.stackGet arr k = CatCryptDialect.memGetDyn arr k := by
  cases n <;> rfl

/-- The jasmin runtime-indexed store `JasminDialect.stackSet` agrees pointwise with
    the dialect runtime-indexed store `CatCryptDialect.memSetDyn` (identical total
    mod-`n` update). Bridges the `memrefSetDyn → stackStore` lowering's
    denotation. -/
theorem stackSet_eq_memSetDyn {n : Nat} (arr : Fin n → BitVec 64) (k : Nat)
    (v : BitVec 64) :
    JasminDialect.stackSet arr k v = CatCryptDialect.memSetDyn arr k v := by
  cases n <;> rfl

/-- The dialect high-multiply word `CatCryptDialect.mulHiC` agrees with the jasmin
    `JasminDialect.mulHiW` — the two are defined identically, so `rfl`. Bridges the
    `bvMulHi → mulhi` lowering's denotation. -/
theorem mulHiW_eq_mulHiC {w : Nat} (a b : BitVec w) :
    JasminDialect.mulHiW a b = CatCryptDialect.mulHiC a b := rfl

/-- The dialect carry-chain data word `CatCryptDialect.addCarryWordC` agrees with
    the jasmin `JasminDialect.addCarryWord` (identical definitions). Bridges the
    `bvAddCarryLo → addCarryLo` lowering's denotation. -/
theorem addCarryWord_eq_addCarryWordC {w : Nat} (a b : BitVec w) (cin : BitVec 1) :
    JasminDialect.addCarryWord a b cin = CatCryptDialect.addCarryWordC a b cin := rfl

/-- The dialect carry-out bit `CatCryptDialect.carryOutBitC` agrees with the jasmin
    `JasminDialect.carryOutBit` (identical definitions). Bridges the
    `bvAddCarryHi → addCarryHi` lowering's denotation. -/
theorem carryOutBit_eq_carryOutBitC {w : Nat} (a b : BitVec w) (cin : BitVec 1) :
    JasminDialect.carryOutBit a b cin = CatCryptDialect.carryOutBitC a b cin := rfl

/-- On the bit type, `ctTransTy` is `BitVec.ofBool`. -/
theorem ctTransTy_bit (v : Bool) : ctTransTy (t := .bit) v = BitVec.ofBool v := rfl

/-- The jasmin equality comparison bit is `BitVec.ofBool` of the decided
    equality, the value the dialect `bvEq` denotes. Bridges the `bvEq → cmp .eq`
    lowering's denotation. -/
theorem cmpBit_eq_ofBool {w : Nat} (a b : BitVec w) :
    cmpBit .eq a b = BitVec.ofBool (decide (a = b)) := by
  unfold cmpBit JasminCmp.holds
  by_cases h : a = b <;> simp [h]

/-- `selectW` on the image of a boolean is the boolean conditional, the value the
    dialect `ite` denotes. Bridges the `ite → select` lowering's denotation. -/
theorem selectW_ofBool {w : Nat} (c : Bool) (a b : BitVec w) :
    selectW (BitVec.ofBool c) a b = if c then a else b := by
  unfold selectW
  cases c <;> simp

/-- The 1-bit register constant of a bit is its image. Bridges the
    `constBit → regConst 1` lowering's denotation. -/
theorem ofNat_toNat_eq_ofBool (b : Bool) : BitVec.ofNat 1 b.toNat = BitVec.ofBool b := by
  cases b <;> rfl

/-- Width-1 register `xor` on the images of two bits is the image of their `xor`. -/
theorem applyXor_ofBool (a b : Bool) :
    JasminBinOp.xor.apply (BitVec.ofBool a) (BitVec.ofBool b) = BitVec.ofBool (Bool.xor a b) := by
  cases a <;> cases b <;> rfl

/-- Width-1 register `and` on the images of two bits is the image of their conjunction. -/
theorem applyAnd_ofBool (a b : Bool) :
    JasminBinOp.and.apply (BitVec.ofBool a) (BitVec.ofBool b) = BitVec.ofBool (a && b) := by
  cases a <;> cases b <;> rfl

/-- Width-1 register `or` on the images of two bits is the image of their disjunction. -/
theorem applyOr_ofBool (a b : Bool) :
    JasminBinOp.or.apply (BitVec.ofBool a) (BitVec.ofBool b) = BitVec.ofBool (a || b) := by
  cases a <;> cases b <;> rfl

/-- The width-1 equality comparison on the images of two bits is the image of the
    negated `xor`, the value the dialect `eqBit` denotes. -/
theorem cmpBit_ofBool_eqBit (a b : Bool) :
    cmpBit .eq (BitVec.ofBool a) (BitVec.ofBool b) = BitVec.ofBool (Bool.xor a b).not := by
  cases a <;> cases b <;> rfl

/-- The width-1 comparison of the image of a bit with the immediate `0` is the image
    of the negated bit. Bridges the `not → cmpImm .eq 1 0` lowering's denotation. -/
theorem cmpBit_ofBool_zero (a : Bool) :
    cmpBit .eq (BitVec.ofBool a) (BitVec.ofNat 1 0) = BitVec.ofBool (!a) := by
  cases a <;> rfl

/-- `selectW` at width 1 on the images of three bits is the image of the boolean
    conditional. Bridges the `ite .bit → select 1` lowering's denotation. -/
theorem selectBit_ofBool (c a b : Bool) :
    selectW (BitVec.ofBool c) (BitVec.ofBool a) (BitVec.ofBool b)
      = BitVec.ofBool (if c then a else b) := by
  cases c <;> cases a <;> cases b <;> rfl

/-- A left rotation by `n` is the right rotation by `(w - n % w) % w`. Bridges the
    `bvRol → rorImm` lowering's denotation. -/
theorem rotateLeft_eq_rotateRight {w : Nat} (a : BitVec w) (n : Nat) :
    a.rotateLeft n = a.rotateRight ((w - n % w) % w) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact Subsingleton.elim _ _
  · rw [← BitVec.rotateLeft_mod_eq_rotateLeft]
    have hn : n % w < w := Nat.mod_lt _ hw
    generalize n % w = k at hn
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight]
    rcases Nat.eq_zero_or_pos k with rfl | hp
    · simp [hi]
    · rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (show w - k < w by omega),
        Nat.mod_eq_of_lt (show w - k < w by omega), show w - (w - k) = k by omega]

/-- **`DialectJasminLeafAgrees` is provable (no hypothesis, no axiom).** Every
    leaf the dialect front lowers agrees: the six `regArith` ops, `regConst`,
    the dynamic-memref ops, the word-native crypto ops (`andn → regArith
    andn`, `bvShiftLV/bvShiftRV → regArith shl/shr`, `bvRor → rorImm`,
    `bvShiftRA → sarImm`), the immediate logical shifts (`bvShiftL/bvShiftR →
    shlImm/shrImm`), and the bignum-ALU word splits (`bvMulHi → mulhi`,
    `bvAddCarryLo → addCarryLo`, `bvAddCarryHi → addCarryHi`), and the word
    select pair (`bvEq → cmp .eq`, `ite (.sword w) → select`), the bit ops
    (`constBit`/`constUnit → regConst`, `xor`/`and`/`or → regArith` at width 1,
    `eqBit → cmp .eq 1`, `not → cmpImm .eq 1 0`, `ite .bit → select 1`) and
    `bvRol → rorImm` all agree by
    computation (the lowering preserves the `BitVec` op), and `extCall` leaves
    agree on the opaque canonical default (`leafAgrees_extCallD`). Every other
    `CatCryptOp` is outside the fragment (`toJExprD = none`), so the
    `toJExprD e = some e'` premise is unsatisfiable and the case is vacuous. -/
theorem dialectJasminLeafAgrees_holds : DialectJasminLeafAgrees := by
  intro Γ t e V e' he
  obtain ⟨op, hop, args⟩ := e
  cases op
  case extCall name argTys retTy => cases hop; exact leafAgrees_extCallD args V name e' he
  -- Every other op: reduce `toJExprD` (the ops outside the fragment close here), split
  -- the argument vector, unfold both `lookupArgs` through the signatures, and transport
  -- each lookup by `ctMapValD_lookup`. The bit ops, constants, `bvEq`, `ite`, `bvRol`
  -- and the memref stores/loads close by their bridge lemmas; the rest by `rfl`.
  all_goals (try cases ‹SimdOp›) <;> (try cases ‹CryptoTy›) <;> cases hop
  all_goals simp only [toJExprD, reduceCtorEq] at he
  all_goals cases he
  all_goals rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩
  all_goals simp only [Expr.denote, eq_mp_eq_cast, cast_eq, mkBin, HVector.head, HVector.tail]
  all_goals
    iterate 3 (try (unfold Expr.lookupArgs; dsimp only [DialectSignature.sig, SimdOp.argTys]))
  all_goals try simp only [ctMapValD_lookup]
  case constBit.bit.refl.refl.nil => exact ofNat_toNat_eq_ofBool _
  case xor.bit.refl.refl.cons.cons.nil => exact applyXor_ofBool _ _
  case and.bit.refl.refl.cons.cons.nil => exact applyAnd_ofBool _ _
  case or.bit.refl.refl.cons.cons.nil => exact applyOr_ofBool _ _
  case not.bit.refl.refl.cons.nil => exact cmpBit_ofBool_zero _
  case eqBit.bit.refl.refl.cons.cons.nil => exact cmpBit_ofBool_eqBit _ _
  case bvConst.sword.refl.refl.nil | vconst128.sword.refl.refl.nil =>
    exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)
  case bvEq.bit.refl.refl.cons.cons.nil => exact cmpBit_eq_ofBool _ _
  case bvRol.sword.refl.refl.cons.nil => exact (rotateLeft_eq_rotateRight _ _).symm
  case ite.bit.refl.refl.cons.cons.cons.nil => exact selectBit_ofBool _ _ _
  case ite.sword.refl.refl.cons.cons.cons.nil => exact selectW_ofBool _ _ _
  case memrefSet.memref.refl.refl.cons.cons.nil => exact JasminDialect.stackSet_fin _ _ _
  case memrefSetDyn.memref.refl.refl.cons.cons.cons.nil => exact stackSet_eq_memSetDyn _ _ _
  case memrefGetDyn.sword.refl.refl.cons.cons.nil => exact stackGet_eq_memGetDyn _ _
  all_goals rfl

/-- A block `toJMultiD` gives an expression denotes, on the transported valuation, the
    transport of the expression's value: `bvNot` is the `xor` with the constant of all
    ones, and `bitToSword` is the select of the constant of all ones and `0`. -/
theorem toJMultiD_denote {Γ : Ctx} {t : CryptoTy} (e : Expr catCryptDialect Γ t)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (blk : Com jasminDialect (mapCtx Γ) (mapTy t)) (h : toJMultiD e = some blk) :
    blk.denote (ctMapValD V) = ctTransTy (e.denote V) := by
  obtain ⟨op, hop, args⟩ := e
  cases op with
  | bvNot w =>
      cases hop
      simp only [toJMultiD] at h; cases h
      show JasminBinOp.xor.apply ((toJVarD args.head).lookup (ctMapValD V))
        (BitVec.ofNat w (BitVec.allOnes w).toNat) = _
      rw [ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
      cases args with | cons a t => exact BitVec.xor_allOnes
  | bitToSword n =>
      cases hop
      simp only [toJMultiD] at h; cases h
      show selectW ((toJVarD args.head).lookup (ctMapValD V))
        (BitVec.ofNat n (BitVec.allOnes n).toNat) (BitVec.ofNat n 0) = _
      rw [ctMapValD_lookup, ctTransTy_bit, ctTransTy_sword, selectW_ofBool, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
      cases args with | cons a t => rfl
  | and =>
      cases hop
      simp only [toJMultiD] at h; cases h
      rw [bitBin64_and_denote _ _ _ _ _ ((ctMapValD_lookup _ V).trans (ctTransTy_bit _))
        ((ctMapValD_lookup _ V).trans (ctTransTy_bit _))]
      cases args with | cons a t => cases t with | cons b t2 => rfl
  | or =>
      cases hop
      simp only [toJMultiD] at h; cases h
      rw [bitBin64_or_denote _ _ _ _ _ ((ctMapValD_lookup _ V).trans (ctTransTy_bit _))
        ((ctMapValD_lookup _ V).trans (ctTransTy_bit _))]
      cases args with | cons a t => cases t with | cons b t2 => rfl
  | xor =>
      cases hop
      simp only [toJMultiD] at h; cases h
      rw [bitBin64_xor_denote _ _ _ _ _ ((ctMapValD_lookup _ V).trans (ctTransTy_bit _))
        ((ctMapValD_lookup _ V).trans (ctTransTy_bit _))]
      cases args with | cons a t => cases t with | cons b t2 => rfl
  | eqBit =>
      cases hop
      simp only [toJMultiD] at h; cases h
      rw [bitEq64_denote _ _ _ _ _ ((ctMapValD_lookup _ V).trans (ctTransTy_bit _))
        ((ctMapValD_lookup _ V).trans (ctTransTy_bit _))]
      cases args with | cons a t => cases t with | cons b t2 => rfl
  | not =>
      cases hop
      simp only [toJMultiD] at h; cases h
      rw [bitNot64_denote _ _ _ ((ctMapValD_lookup _ V).trans (ctTransTy_bit _))]
      cases args with | cons a t => rfl
  | _ => simp only [toJMultiD, reduceCtorEq] at h

/-- A block `toJBlockD` gives an expression denotes, on the transported valuation, the
    transport of the expression's value. -/
theorem toJBlockD_denote {Γ : Ctx} {t : CryptoTy} (e : Expr catCryptDialect Γ t)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (blk : Com jasminDialect (mapCtx Γ) (mapTy t)) (h : toJBlockD e = some blk) :
    blk.denote (ctMapValD V) = ctTransTy (e.denote V) := by
  unfold toJBlockD at h
  split at h
  · next b hm =>
      cases h
      exact toJMultiD_denote e V _ hm
  · split at h
    · next e' he =>
        cases h
        exact dialectJasminLeafAgrees_holds e V e' he
    · cases h

/-- **Preservation, unconditional.** `cryptoDialectToJasminCom_denote_eq` with the
    leaf-agreement hypothesis discharged by `dialectJasminLeafAgrees_holds`.
    `cryptoDialectToJasminCom` preserves denotation on the lowered fragment with
    no assumed hypothesis. -/
theorem cryptoDialectToJasminCom_denote_eq' {Γ : Ctx} {t : CryptoTy}
    (com : Com catCryptDialect Γ t)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t))
    (hcom : cryptoDialectToJasminCom com = some jcom) :
    jcom.denote (ctMapValD V) = ctTransTy (com.denote V) :=
  cryptoDialectToJasminCom_denote_eq dialectJasminLeafAgrees_holds com V jcom hcom

/-! ## 8. The result as a `DialectLoweringTransport.TransportSquare`

Repackage the preservation theorem as a `TransportSquare` (the Trocq map₁
transport square from `DialectLoweringTransport.lean`), so this dialect-native
pass can join `CompilerLoweringRegistry` by the same `comp`-by-transitivity
mechanism as the lattice passes. The square is the
`(lower c).denote (mapVal V) = transTy (c.denote V)` commuting square with
`g := com.denote`, `f := jcom.denote`, `φin := ctMapValD`, `φout := ctTransTy` —
its single field is exactly `cryptoDialectToJasminCom_denote_eq'`. -/

/-- **The A1′ transport square.** For any source `com : Com catCryptDialect Γ t`
    whose lowering succeeds (`cryptoDialectToJasminCom com = some
    jcom`), the dialect-native pass is a `DialectLoweringTransport.TransportSquare`
    from `com.denote` to `jcom.denote` along `(ctMapValD, ctTransTy)`. The
    analogue of the lattice route's `pass2_lowering_transport`, ready
    to be composed via `TransportSquare.comp` and registered in
    `CompilerLoweringRegistry`. -/
def regPassA1prime {Γ : Ctx} {t : CryptoTy}
    (com : Com catCryptDialect Γ t)
    (jcom : Com jasminDialect (mapCtx Γ) (mapTy t))
    (hcom : cryptoDialectToJasminCom com = some jcom) :
    DialectLoweringTransport.TransportSquare
      (g := fun V : Ctxt.Valuation (d := catCryptDialect) Γ => com.denote V)
      (φin := ctMapValD) (φout := ctTransTy)
      (f := fun V' => jcom.denote V') :=
  ⟨fun V => cryptoDialectToJasminCom_denote_eq' com V jcom hcom⟩

end CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect
