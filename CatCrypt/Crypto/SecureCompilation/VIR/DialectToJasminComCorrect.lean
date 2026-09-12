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

## Why this twin is structurally cleaner than the `CProg` one

`CryptoToJasminComCorrect` carries an extra wrinkle: the `CProg` side denotes
into the **monad** `SPComp` (`CProg.denote V : SPComp ⟦t⟧`), while the Jasmin
`Com.denote` produces a **plain value**. That file therefore has to read off the
pure value underneath each `SPComp.pure`, via `SPComp.pure_inj`.

The dialect side has *no* such wrinkle: `Com catCryptDialect` denotes into a plain
value (`catCryptDenote` is a pure `DialectDenote`), exactly like
`Com jasminDialect`. So the statement is the clean plain-value commuting square

    (cryptoDialectToJasminCom com).denote (ctMapValD V) = ctTransTy (com.denote V)

with **no** `SPComp` threading — the same shape as
`LatticeToJasminDenote.lowerLatticeToJasmin_denote_eq` (which is the structural
template followed here), specialised to the `Option`-valued front.

## Reuse from the `CProg` twin

Because `catCryptDialect.Ty = CryptoTy`, a `Com catCryptDialect`'s De Bruijn
context `Γ : Ctxt catCryptDialect` *is* `CryptoSSA.Ctx = List CryptoTy` — the same
context type `CProg` uses, and the same `mapTy`/`mapCtx`. So the per-value
transport `ctTransTy` (and `ctTransTy_sword`/`ctTransTy_memref`/`ctTransTy_default`)
are imported verbatim from `CryptoToJasminComCorrect`. The new pieces are the
**valuation** transport `ctMapValD` (over `Ctxt.Valuation`, not `CProg`'s `HVec`),
its lookup/extend commute lemmas, and the dialect-`Expr`-shaped leaf-agreement
predicate `DialectJasminLeafAgrees`.

## Scope

* `ctMapValD` / `ctMapValD_lookup` / `ctMapValD_extend` — the dialect valuation
  transport and its commute lemmas (the `Ctxt.Var`-shaped analogues of the
  `CVar`-shaped `ctMapVal_lookup`/`ctMapVal_extend`).
* `DialectJasminLeafAgrees` — the per-`Expr` leaf-agreement predicate over
  `toJExprD`, threaded through the induction (mirroring `JasminLeafAgrees`).
* `cryptoDialectToJasminCom_denote_eq` — the **general** parametric preservation
  theorem, by induction on the `Com`. This is the must-have.
* `dialectJasminLeafAgrees_holds` — the *unconditional* discharge of the leaf
  predicate over the lowered fragment (arith/const leaves agree by computation;
  `extCall` leaves agree on the opaque canonical default via `ctTransTy_default`).
* `cryptoDialectToJasminCom_denote_eq'` — the hypothesis-free corollary.
* `regPassA1prime` — the result repackaged as a `DialectLoweringTransport`
  `TransportSquare`, so it can join `CompilerLoweringRegistry` later.

0 sorries. The deferred piece is identical to the template's: a concrete
leaf-spec'd Jasmin `extCall` denotation (a *functional* leaf, carried
per-protocol) is a separate, stronger discharge; the stub denotation the
meta-theorem ships with is closed here on the opaque default.
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
  (ctTransTy ctTransTy_sword ctTransTy_memref ctTransTy_default
   jasminExtSem_reg jasminExtSem_stackArr64)

/-! ## 1. The dialect valuation transport `ctMapValD`

We reuse the per-value transport `ctTransTy` from `CryptoToJasminComCorrect`
verbatim (it is keyed on `CryptoTy`/`mapTy`, which `catCryptDialect` shares). The
*valuation* transport, however, is over `Ctxt.Valuation` (the dialect's
`HVector`-based valuation), not `CProg`'s `HVec`, so we define a fresh `ctMapValD`
— the `Ctxt.Valuation` analogue of `LatticeToJasminDenote.mapVal`. -/

/-- Transport a `catCryptDialect` valuation to the `mapTy`-mapped Jasmin context,
    applying `ctTransTy` per binding. The `Ctxt.Valuation` analogue of
    `CryptoToJasminComCorrect.ctMapVal`. -/
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
`SPComp`), so the statement is the clean commuting square — no purity read-off.

This is the *parametric* hypothesis: the Jasmin `extCall` denotation is a stub
today, so we abstract over the fact that it agrees with the dialect op. A
concrete leaf-spec'd `extCall` semantics would discharge it (the deferred
piece). -/

/-- Per-expression leaf agreement, quantified over all
    contexts/types/expressions/valuations so it slots into the program
    induction. For any `e` the front lowers to `e'`, the lowered Jasmin
    expression denotes to `ctTransTy` of `e`'s denotation. The dialect-`Expr`
    analogue of `CryptoToJasminComCorrect.JasminLeafAgrees`. -/
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
accordingly. Unlike the `CExpr` template — where each `CExpr` constructor is its
own inductive case and the denotation unfolds by `rfl` — the dialect denotation
threads the `retTy_eq ▸ …` cast and the `DialectDenote.denote` instance, which we
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
  simp only [toJExprD, Option.some.injEq] at he
  subst he
  show jasminExtSem name (argTys.map mapTy) (mapTy retTy) _ = _
  cases retTy with
  | sword w => exact jasminExtSem_reg _ _ _ _
  | bit => exact jasminExtSem_reg _ _ _ _
  | unit => exact jasminExtSem_reg _ _ _ _
  | pair a b => exact jasminExtSem_reg _ _ _ _
  | sum a b => exact jasminExtSem_reg _ _ _ _
  | memref n => exact jasminExtSem_stackArr64 _ _ _ _

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
    `CryptoToJasminComCorrect.leafAgrees_extCall`. No axiom, no `sorry`. -/
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

/-- **`DialectJasminLeafAgrees` is provable (no hypothesis, no axiom).** Every
    leaf the dialect front lowers agrees: the six `regArith` ops, `regConst`,
    the dynamic-memref ops, the word-native crypto ops (`andn → regArith
    andn`, `bvShiftLV/bvShiftRV → regArith shl/shr`, `bvRor → rorImm`,
    `bvShiftRA → sarImm`), the immediate logical shifts (`bvShiftL/bvShiftR →
    shlImm/shrImm`), and the bignum-ALU word splits (`bvMulHi → mulhi`,
    `bvAddCarryLo → addCarryLo`, `bvAddCarryHi → addCarryHi`) all agree by
    computation (the lowering preserves the `BitVec` op), and `extCall` leaves
    agree on the opaque canonical default (`leafAgrees_extCallD`). Every other
    `CatCryptOp` is outside the fragment (`toJExprD = none`), so the
    `toJExprD e = some e'` premise is unsatisfiable and the case is vacuous. The
    dialect analogue of `CryptoToJasminComCorrect.jasminLeafAgrees_holds`. -/
theorem dialectJasminLeafAgrees_holds : DialectJasminLeafAgrees := by
  intro Γ t e V e' he
  obtain ⟨op, hop, args⟩ := e
  cases op with
  | bvAdd w =>
      cases hop
      simp only [toJExprD] at he; cases he
      show JasminBinOp.add.apply ((toJVarD args.head).lookup (ctMapValD V))
        ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
      rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
        ctTransTy_sword]
      cases args with | cons a t => cases t with | cons b t2 => rfl
  | bvSub w =>
      cases hop
      simp only [toJExprD] at he; cases he
      show JasminBinOp.sub.apply ((toJVarD args.head).lookup (ctMapValD V))
        ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
      rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
        ctTransTy_sword]
      cases args with | cons a t => cases t with | cons b t2 => rfl
  | bvMul w =>
      cases hop
      simp only [toJExprD] at he; cases he
      show JasminBinOp.mul.apply ((toJVarD args.head).lookup (ctMapValD V))
        ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
      rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
        ctTransTy_sword]
      cases args with | cons a t => cases t with | cons b t2 => rfl
  | bvAnd w =>
      cases hop
      simp only [toJExprD] at he; cases he
      show JasminBinOp.and.apply ((toJVarD args.head).lookup (ctMapValD V))
        ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
      rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
        ctTransTy_sword]
      cases args with | cons a t => cases t with | cons b t2 => rfl
  | bvOr w =>
      cases hop
      simp only [toJExprD] at he; cases he
      show JasminBinOp.or.apply ((toJVarD args.head).lookup (ctMapValD V))
        ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
      rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
        ctTransTy_sword]
      cases args with | cons a t => cases t with | cons b t2 => rfl
  | bvXor w =>
      cases hop
      simp only [toJExprD] at he; cases he
      show JasminBinOp.xor.apply ((toJVarD args.head).lookup (ctMapValD V))
        ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
      rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
        ctTransTy_sword]
      cases args with | cons a t => cases t with | cons b t2 => rfl
  | bvConst w v =>
      cases hop
      simp only [toJExprD] at he; cases he
      rw [ctTransTy_sword]; show BitVec.ofNat w v.toNat = v
      simp [BitVec.ofNat_toNat]
  | extCall name argTys retTy =>
      cases hop
      exact leafAgrees_extCallD args V name e' he
  | andn w =>
      cases hop
      simp only [toJExprD] at he; cases he
      show JasminBinOp.andn.apply ((toJVarD args.head).lookup (ctMapValD V))
        ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
      rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
        ctTransTy_sword]
      cases args with | cons a t => cases t with | cons b t2 => rfl
  | bvShiftLV w =>
      cases hop
      simp only [toJExprD] at he; cases he
      show JasminBinOp.shl.apply ((toJVarD args.head).lookup (ctMapValD V))
        ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
      rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
        ctTransTy_sword]
      cases args with | cons a t => cases t with | cons b t2 => rfl
  | bvShiftRV w =>
      cases hop
      simp only [toJExprD] at he; cases he
      show JasminBinOp.shr.apply ((toJVarD args.head).lookup (ctMapValD V))
        ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
      rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
        ctTransTy_sword]
      cases args with | cons a t => cases t with | cons b t2 => rfl
  | bvRor w n =>
      -- Rotate-right by immediate lowers to `rorImm w n`; the jasmin denotation
      -- `a.rotateRight n` is *definitionally* the dialect denotation, and
      -- `ctTransTy` is the identity on `.sword w`.
      cases hop
      simp only [toJExprD] at he; cases he
      show ((toJVarD args.head).lookup (ctMapValD V) : BitVec w).rotateRight n = _
      rw [ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword]
      cases args with | cons a t => rfl
  | bvShiftRA w n =>
      -- Arithmetic right shift by immediate lowers to `sarImm w n`; the jasmin
      -- denotation `BitVec.sshiftRight a n` is definitionally the dialect
      -- denotation, `ctTransTy` identity on `.sword w`.
      cases hop
      simp only [toJExprD] at he; cases he
      show BitVec.sshiftRight ((toJVarD args.head).lookup (ctMapValD V) : BitVec w) n = _
      rw [ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword]
      cases args with | cons a t => rfl
  | memrefGetDyn n =>
      -- Dynamic load lowers to `stackLoad 64 n`; its jasmin denotation
      -- `stackGet arr i.toNat` is *definitionally* the dialect denotation
      -- `memGetDyn arr i.toNat` (the two are defined identically), and
      -- `ctTransTy` is the identity on `.sword 64`.
      cases hop
      simp only [toJExprD] at he; cases he
      show JasminDialect.stackGet
          ((toJVarD args.head).lookup (ctMapValD V))
          (((toJVarD args.tail.head).lookup (ctMapValD V)) : BitVec 64).toNat = _
      rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_memref, ctTransTy_sword,
        ctTransTy_sword]
      cases args with | cons a t => cases t with | cons i t2 =>
        rw [stackGet_eq_memGetDyn]; rfl
  | memrefSetDyn n =>
      -- Dynamic store lowers to `stackStore 64 n`; its jasmin denotation
      -- `stackSet arr i.toNat v` is definitionally the dialect denotation
      -- `memSetDyn arr i.toNat v`, and `ctTransTy` is the identity on
      -- `.memref n`.
      cases hop
      simp only [toJExprD] at he; cases he
      show JasminDialect.stackSet
          ((toJVarD args.head).lookup (ctMapValD V))
          (((toJVarD args.tail.head).lookup (ctMapValD V)) : BitVec 64).toNat
          ((toJVarD args.tail.tail.head).lookup (ctMapValD V)) = _
      rw [ctMapValD_lookup, ctMapValD_lookup, ctMapValD_lookup, ctTransTy_memref,
        ctTransTy_sword, ctTransTy_sword, ctTransTy_memref]
      cases args with
        | cons a t => cases t with | cons i t2 => cases t2 with | cons v t3 =>
          rw [stackSet_eq_memSetDyn]; rfl
  | bvShiftL w k =>
      -- Immediate logical left shift lowers to `shlImm w k`; the jasmin
      -- denotation `a <<< k` is definitionally the dialect denotation.
      cases hop
      simp only [toJExprD] at he; cases he
      show BitVec.shiftLeft ((toJVarD args.head).lookup (ctMapValD V) : BitVec w) k = _
      rw [ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword]
      cases args with | cons a t => rfl
  | bvShiftR w k =>
      -- Immediate logical right shift lowers to `shrImm w k`; the jasmin
      -- denotation `a >>> k` is definitionally the dialect denotation
      -- `BitVec.ushiftRight a k`.
      cases hop
      simp only [toJExprD] at he; cases he
      show BitVec.ushiftRight ((toJVarD args.head).lookup (ctMapValD V) : BitVec w) k = _
      rw [ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword]
      cases args with | cons a t => rfl
  | bvMulHi w =>
      -- High-multiply word lowers to `mulhi w`; the jasmin `mulHiW` is identical
      -- to the dialect `mulHiC`, and `ctTransTy` is the identity on `.sword w`.
      cases hop
      simp only [toJExprD] at he; cases he
      show JasminDialect.mulHiW ((toJVarD args.head).lookup (ctMapValD V))
        ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
      rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
        ctTransTy_sword]
      cases args with | cons a t => cases t with | cons b t2 =>
        rw [mulHiW_eq_mulHiC]; rfl
  | bvAddCarryLo w =>
      -- Carry-chain data word lowers to `addCarryLo w`; the jasmin
      -- `addCarryWord` is identical to the dialect `addCarryWordC`.
      cases hop
      simp only [toJExprD] at he; cases he
      show JasminDialect.addCarryWord ((toJVarD args.head).lookup (ctMapValD V))
        ((toJVarD args.tail.head).lookup (ctMapValD V))
        ((toJVarD args.tail.tail.head).lookup (ctMapValD V)) = _
      rw [ctMapValD_lookup, ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword,
        ctTransTy_sword, ctTransTy_sword, ctTransTy_sword]
      cases args with | cons a t => cases t with | cons b t2 => cases t2 with
        | cons cin t3 => rw [addCarryWord_eq_addCarryWordC]; rfl
  | bvAddCarryHi w =>
      -- Carry-out bit lowers to `addCarryHi w`; the jasmin `carryOutBit` is
      -- identical to the dialect `carryOutBitC`, and `ctTransTy` is the identity
      -- on `.sword 1`.
      cases hop
      simp only [toJExprD] at he; cases he
      show JasminDialect.carryOutBit ((toJVarD args.head).lookup (ctMapValD V))
        ((toJVarD args.tail.head).lookup (ctMapValD V))
        ((toJVarD args.tail.tail.head).lookup (ctMapValD V)) = _
      rw [ctMapValD_lookup, ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword,
        ctTransTy_sword, ctTransTy_sword, ctTransTy_sword]
      cases args with | cons a t => cases t with | cons b t2 => cases t2 with
        | cons cin t3 => rw [carryOutBit_eq_carryOutBitC]; rfl
  -- **128-bit SIMD ops.** The binary `vsimd op` lowers to jasmin `.vsimd op`; both
  -- sides denote by the *same* `SimdOp.denote op` waist, so agreement is
  -- definitional after the lookup transport and `ctTransTy_sword` (identity on
  -- `.sword 128`). The two UNARY `SimdOp`s (`vpshufd`/`vaeskeygen`) fall outside the
  -- binary `vsimd` fragment (`toJExprD = none`), so those sub-cases are vacuous.
  | vsimd op =>
      cases op with
      | gf2p8mulb =>
          cases hop
          simp only [toJExprD] at he; cases he
          show SimdOp.denote .gf2p8mulb ((toJVarD args.head).lookup (ctMapValD V))
            ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
          rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
            ctTransTy_sword]
          cases args with | cons a t => cases t with | cons b t2 => rfl
      | vpshufb =>
          cases hop
          simp only [toJExprD] at he; cases he
          show SimdOp.denote .vpshufb ((toJVarD args.head).lookup (ctMapValD V))
            ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
          rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
            ctTransTy_sword]
          cases args with | cons a t => cases t with | cons b t2 => rfl
      | clmul i =>
          cases hop
          simp only [toJExprD] at he; cases he
          show SimdOp.denote (.clmul i) ((toJVarD args.head).lookup (ctMapValD V))
            ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
          rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
            ctTransTy_sword]
          cases args with | cons a t => cases t with | cons b t2 => rfl
      | affineqb i =>
          cases hop
          simp only [toJExprD] at he; cases he
          show SimdOp.denote (.affineqb i) ((toJVarD args.head).lookup (ctMapValD V))
            ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
          rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
            ctTransTy_sword]
          cases args with | cons a t => cases t with | cons b t2 => rfl
      | bitwise b =>
          cases hop
          simp only [toJExprD] at he; cases he
          show SimdOp.denote (.bitwise b) ((toJVarD args.head).lookup (ctMapValD V))
            ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
          rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
            ctTransTy_sword]
          cases args with | cons a t => cases t with | cons b t2 => rfl
      | packed b lw =>
          cases hop
          simp only [toJExprD] at he; cases he
          show SimdOp.denote (.packed b lw) ((toJVarD args.head).lookup (ctMapValD V))
            ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
          rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
            ctTransTy_sword]
          cases args with | cons a t => cases t with | cons b t2 => rfl
      | varShift b lw =>
          cases hop
          simp only [toJExprD] at he; cases he
          show SimdOp.denote (.varShift b lw) ((toJVarD args.head).lookup (ctMapValD V))
            ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
          rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
            ctTransTy_sword]
          cases args with | cons a t => cases t with | cons b t2 => rfl
      | mulhi16 =>
          cases hop
          simp only [toJExprD] at he; cases he
          show SimdOp.denote .mulhi16 ((toJVarD args.head).lookup (ctMapValD V))
            ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
          rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
            ctTransTy_sword]
          cases args with | cons a t => cases t with | cons b t2 => rfl
      | vaesenc =>
          cases hop
          simp only [toJExprD] at he; cases he
          show SimdOp.denote .vaesenc ((toJVarD args.head).lookup (ctMapValD V))
            ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
          rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
            ctTransTy_sword]
          cases args with | cons a t => cases t with | cons b t2 => rfl
      | vaesenclast =>
          cases hop
          simp only [toJExprD] at he; cases he
          show SimdOp.denote .vaesenclast ((toJVarD args.head).lookup (ctMapValD V))
            ((toJVarD args.tail.head).lookup (ctMapValD V)) = _
          rw [ctMapValD_lookup, ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword,
            ctTransTy_sword]
          cases args with | cons a t => cases t with | cons b t2 => rfl
      | vaeskeygen r => simp only [toJExprD, reduceCtorEq] at he
      | vpshufd i => simp only [toJExprD, reduceCtorEq] at he
  -- The unary SIMD front ops (`vpshufdC`/`vaeskeygenC` → jasmin `.vsimd`;
  -- `vpsrldqC`/`vpslldqC` → jasmin `.vpsrldq`/`.vpslldq`). The front denotes with
  -- the same waist the jasmin op denotes (`SimdOp.denote (.vpshufd _) x x` resp. the
  -- byte-shift), so agreement is definitional.
  | vpshufdC imm =>
      cases hop
      simp only [toJExprD] at he; cases he
      show SimdOp.denote (.vpshufd imm) ((toJVarD args.head).lookup (ctMapValD V))
        ((toJVarD args.head).lookup (ctMapValD V)) = _
      rw [ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword]
      cases args with | cons a t => rfl
  | vaeskeygenC rcon =>
      cases hop
      simp only [toJExprD] at he; cases he
      show SimdOp.denote (.vaeskeygen rcon) ((toJVarD args.head).lookup (ctMapValD V))
        ((toJVarD args.head).lookup (ctMapValD V)) = _
      rw [ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword]
      cases args with | cons a t => rfl
  | vpsrldqC n =>
      cases hop
      simp only [toJExprD] at he; cases he
      show BitVec.ushiftRight ((toJVarD args.head).lookup (ctMapValD V) : BitVec 128)
        (n * 8) = _
      rw [ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword]
      cases args with | cons a t => rfl
  | vpslldqC n =>
      cases hop
      simp only [toJExprD] at he; cases he
      show BitVec.shiftLeft ((toJVarD args.head).lookup (ctMapValD V) : BitVec 128)
        (n * 8) = _
      rw [ctMapValD_lookup, ctTransTy_sword, ctTransTy_sword]
      cases args with | cons a t => rfl
  | vconst128 v =>
      cases hop
      simp only [toJExprD] at he; cases he
      rw [ctTransTy_sword]; show BitVec.ofNat 128 v.toNat = v
      simp [BitVec.ofNat_toNat]
  | _ => simp only [toJExprD, reduceCtorEq] at he

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
    whose `CProg`-free lowering succeeds (`cryptoDialectToJasminCom com = some
    jcom`), the dialect-native pass is a `DialectLoweringTransport.TransportSquare`
    from `com.denote` to `jcom.denote` along `(ctMapValD, ctTransTy)`. The
    `CProg`-free analogue of the lattice route's `pass2_lowering_transport`, ready
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
