/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-!
# The verified `Com[thir] → Com[catCrypt]` lowering (the HIGH-stack edge)

`ThirDialect.lean` lowers `Com thirDialect` **down** to `Com jasminDialect`
(flat, register/two-address). This file builds the complementary edge that
lifts a THIR-front body **up** into `catCryptDialect` — the dialect whose `Op`
set is the high algebraic crypto-SSA surface (`bvAdd`/`bvMul`/…/`extCall`,
the de-Bruijn `Com` mirror of `CExpr`). With this edge a hax-extracted body —
which today lands flat at `jasminDialect` — can instead descend the *high*
algebraic stack (`catCryptDialect → … → jasmin → ELF`), where the algebraic
optimizer, the relational-compile passes, and the field/limb rewrites live.

This is the structural unlock: it proves the `thir → catCrypt` edge **exists**
and is denotation-preserving for the common scalar-arith + let/var case.

## The type translation (the new ingredient vs `ThirDialect.lean`)

`thirDialect.Ty = JasminTy` whereas `catCryptDialect.Ty = CryptoTy`, so unlike
the flat `lowerThir` (which shared `Ty` and reused contexts verbatim) this edge
needs a **type map** `tcTy : JasminTy → CryptoTy`. The scalar register type
maps to the scalar word type:

    JasminTy.reg w  ↦  CryptoTy.sword w        (⟦·⟧ = BitVec w on both — defeq)

The denotations agree *definitionally* (`⟦.reg w⟧` and `⟦.sword w⟧` both reduce
to `BitVec w`), so the per-entry valuation transport `tcEntry` is the identity
on the covered (`reg`) fragment, and the variable-lookup lemma `vTc_lookup` is
**cast-free**. The non-`reg` JasminTy arms (`inlineInt`, `stackArr`, `bool`)
never appear in a covered THIR scalar body, so they map to a placeholder and
carry a default valuation entry; the soundness theorem is stated over the
`reg`-typed fragment where transport is exact.

## Covered op set (each arm denotation-preserving)

| `ThirOp`                               | `CatCryptOp`            |
|----------------------------------------|-------------------------|
| `thBin .add/.sub/.mul/.and/.or/.xor w` | `bvAdd/Sub/Mul/And/Or/Xor w` |
| `thShlImm w n`                         | `bvShiftL w n`          |
| `thShrImm w n`                         | `bvShiftR w n`          |
| `thConst w n`                          | `bvConst w (ofNat w n)` |
| (let / var / ret)                      | (structural)            |

Together with the structural `.var`/`.ret` recursion this is the straight-line
scalar-arith + immediate-shift + constant core a hax scalar/control body
produces. The lowering is `Option`-valued: it returns `none` exactly on the
ops with **no** `catCryptDialect` counterpart (listed below), so the covered
subset is faithful and gap-free.

## Uncovered ops (need new `CatCryptOp` constructors — a separate task)

* `thBinLit op w n` — register-OP-immediate. (Expressible as `bvConst` +
  `bvOp`, i.e. a 1→2 op EXPANSION like `lowerThir`'s; left for the follow-on
  that ports the expansion proof to the type-mapped setting.)
* `thBin .shl/.shr/.andn` — variable-amount logical shifts / `andn`:
  `catCryptDialect` has only the **immediate**-amount `bvShiftL/R` and no
  `andn`.
* `thRor w n` — bit rotate: no `bvRotr` in `catCryptDialect`.
* `thSarImm w n` — arithmetic right shift: no signed `bvAShiftR`.
* `thCast w w'` — width cast: no `bvCast`/`bvZeroExtend`.
* `thMulHi`, `thAddCarryLo`, `thAddCarryHi` — widening-mul hi word and the
  carry-chain data/carry words (the bignum ALU spine). `catCryptDialect` has
  `bvAdd64`/`bvAdc` (multi-output add-with-carry) but not the single-word
  `mulHiW`/`addCarryWord`/`carryOutBit` splits.
* `thSelect w` — branch-free CT select: no single `select`; `catCryptDialect`'s
  `ite` is a 3-arg conditional over an arbitrary `CryptoTy`, not the `reg 1`
  mask form.
* `thVpack bop` — AVX-512 8×u64 packed lane op: no SIMD op in
  `catCryptDialect`.
* `thExtCall` / `thEqLit` — opaque leaf call / tag test. (`catCryptDialect`
  *has* `extCall`; the leaf is wired but its arg-vector transport needs the
  general `tcTy`-mapped `argsTc`, deferred with the `thExtCall` arm.)
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ThirToCatCrypt

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
  (ThirOp thirDialect thirSignature thirDenote)

/-! ## 1. The type translation `JasminTy → CryptoTy` -/

/-- Map a Jasmin (THIR) value type to a CryptoSSA value type. The scalar
    register `reg w` maps to the scalar word `sword w` (both denote `BitVec w`,
    *definitionally*); the non-`reg` arms are dead on the covered scalar
    fragment and map to a placeholder `sword 0`. -/
def tcTy : JasminTy → CryptoTy
  | .reg w => .sword w
  | .stackArr _ _ => .sword 0
  | .inlineInt => .sword 0
  | .bool => .sword 0

/-- Pointwise type map on a context (newest binding at the head). -/
def tcCtx (Γ : Ctxt jasminDialect) : Ctxt catCryptDialect := Γ.map tcTy

@[simp] theorem tcCtx_cons (s : JasminTy) (Γ : Ctxt jasminDialect) :
    tcCtx (s :: Γ) = tcTy s :: tcCtx Γ := rfl

/-! ## 2. Valuation transport

A THIR valuation `Ctxt.Valuation Γ` carries a `BitVec w` at every `reg w`
binding; the transported `catCrypt` valuation carries the *same* `BitVec w` at
the corresponding `sword w` binding (the denotations are defeq), so on the
`reg` fragment `tcEntry` is the identity. The non-`reg` entries are dead and
carry the default `(0 : BitVec 0)`. -/

/-- Transport one valuation entry along `tcTy`. On `reg w` the denotation types
    `⟦.reg w⟧ = ⟦.sword w⟧` are defeq so this is the identity; the dead arms
    carry the default. -/
def tcEntry : (t : JasminTy) → ⟦t⟧ → ⟦tcTy t⟧
  | .reg _, x => x
  | .stackArr _ _, _ => (0 : BitVec 0)
  | .inlineInt, _ => (0 : BitVec 0)
  | .bool, _ => (0 : BitVec 0)

/-- Transport a whole THIR valuation to a `catCrypt` valuation. -/
def vTcVal {Γ : Ctxt jasminDialect} :
    Ctxt.Valuation Γ → Ctxt.Valuation (tcCtx Γ)
  | .nil => .nil
  | .cons (t := t) x rest => .cons (tcEntry t x) (vTcVal rest)

/-! ## 3. Variable transport (on the `reg` fragment) -/

/-- Transport a THIR variable of any type `t` to the `catCrypt` variable of type
    `tcTy t` in the mapped context. `tcCtx (s :: Γ) = tcTy s :: tcCtx Γ` reduces,
    so the de Bruijn indices line up; `.here ↦ .here`, `.there ↦ .there`. -/
def vTc {Γ : Ctxt jasminDialect} {t : JasminTy} :
    @Ctxt.Var thirDialect Γ t →
    @Ctxt.Var catCryptDialect (tcCtx Γ) (tcTy t)
  | .here => .here
  | .there v => .there (vTc v)

/-- Transport preserves variable lookup on the `reg` fragment, **cast-free**: on
    `reg` bindings `tcEntry` is the identity and `⟦.reg w⟧ = ⟦.sword w⟧` is
    defeq. -/
@[simp] theorem vTc_lookup {Γ : Ctxt jasminDialect} {w : Nat} :
    (v : @Ctxt.Var thirDialect Γ (.reg w)) → (V : Ctxt.Valuation Γ) →
    (vTc v).lookup (vTcVal V) = v.lookup V
  | .here, .cons _ _ => rfl
  | .there v, .cons _ rest => by
      show (vTc v).lookup (vTcVal rest) = v.lookup rest
      exact vTc_lookup v rest

/-! ## 4. The op-level lowering

Each covered `ThirOp` becomes a `catCryptDialect` `Expr` over the transported
operand variables. The lowering is `Option`-valued, declining (with `none`) the
ops that have no `catCryptDialect` image (§ module-doc table). Every covered arm
rebuilds the binding with the matching `CatCryptOp` and the transported argument
variables; because `tcTy (.reg w) = .sword w` the op signatures line up and the
`retTy_eq` witnesses are `rfl`. -/

/-- Build the binary `catCryptDialect` `Expr` for a register/register
    `JasminBinOp` over two transported `sword w` operand vars. The op tags
    `bvAdd/Sub/Mul/And/Or/Xor` and the word-native `bvShiftLV/bvShiftRV/andn`
    all have `sig = [sword w, sword w]` and `ret = sword w`, so `retTy_eq` is
    `rfl`. The variable shifts `.shl/.shr` map to the variable-amount
    `bvShiftLV/bvShiftRV` (denote `a <<< b.toNat` / `a >>> b.toNat`); `.andn`
    maps to `andn` (denote `(~~~a) &&& b`). Total over `JasminBinOp`. -/
def mkBinC {Γ : Ctxt jasminDialect} (bop : JasminBinOp) (w : Nat)
    (a b : @Ctxt.Var catCryptDialect (tcCtx Γ) (.sword w)) :
    Option (Expr catCryptDialect (tcCtx Γ) (.sword w)) :=
  match bop with
  | .add => some (Expr.mk (.bvAdd w) rfl (.cons a (.cons b .nil)))
  | .sub => some (Expr.mk (.bvSub w) rfl (.cons a (.cons b .nil)))
  | .mul => some (Expr.mk (.bvMul w) rfl (.cons a (.cons b .nil)))
  | .and => some (Expr.mk (.bvAnd w) rfl (.cons a (.cons b .nil)))
  | .or  => some (Expr.mk (.bvOr w)  rfl (.cons a (.cons b .nil)))
  | .xor => some (Expr.mk (.bvXor w) rfl (.cons a (.cons b .nil)))
  | .shl => some (Expr.mk (.bvShiftLV w) rfl (.cons a (.cons b .nil)))
  | .shr => some (Expr.mk (.bvShiftRV w) rfl (.cons a (.cons b .nil)))
  | .andn => some (Expr.mk (.andn w) rfl (.cons a (.cons b .nil)))

/-- Lower one THIR `.var` binding (op + transported operand vars) over a body
    already lowered to `Com catCryptDialect (sword w :: tcCtx Γ) t'`. Returns
    `none` on an uncovered op. The binary arms read the two `reg w` operand vars
    out of `args` and rebuild a `bvOp`; the immediate-shift / const arms rebuild
    the matching `bvShiftL/R` / `bvConst`. -/
def lowerVarStepTc {Γ : Ctxt jasminDialect} {t' : CryptoTy}
    (op : thirDialect.Op)
    (args : HVector (fun ty => @Ctxt.Var thirDialect Γ ty)
      (DialectSignature.sig (d := thirDialect) op))
    (bodyC : Com catCryptDialect (tcTy (DialectSignature.ret (d := thirDialect) op)
      :: tcCtx Γ) t') :
    Option (Com catCryptDialect (tcCtx Γ) t') :=
  match op, args, bodyC with
  | .thBin bop w, args, bodyC =>
      match mkBinC bop w (vTc (args.head)) (vTc (args.tail.head)) with
      | some e => some (.var e bodyC)
      | none => none
  | .thShlImm w n, args, bodyC =>
      let a := vTc (args.head)
      some (.var (Expr.mk (.bvShiftL w n) rfl (.cons a .nil)) bodyC)
  | .thShrImm w n, args, bodyC =>
      let a := vTc (args.head)
      some (.var (Expr.mk (.bvShiftR w n) rfl (.cons a .nil)) bodyC)
  | .thConst w n, _, bodyC =>
      some (.var (Expr.mk (.bvConst w (BitVec.ofNat w n)) rfl .nil) bodyC)
  -- Bit rotate-right by immediate `n` (denote `a.rotateRight n`) ↦ `bvRor w n`.
  | .thRor w n, args, bodyC =>
      let a := vTc (args.head)
      some (.var (Expr.mk (.bvRor w n) rfl (.cons a .nil)) bodyC)
  -- Arithmetic (signed) right shift by immediate `n` (denote
  -- `BitVec.sshiftRight a n`) ↦ `bvShiftRA w n`.
  | .thSarImm w n, args, bodyC =>
      let a := vTc (args.head)
      some (.var (Expr.mk (.bvShiftRA w n) rfl (.cons a .nil)) bodyC)
  -- High word of the widening multiply (denote `mulHiW a b`) ↦ `bvMulHi w`
  -- (denote `mulHiC a b`, identical).
  | .thMulHi w, args, bodyC =>
      let a := vTc (args.head)
      let b := vTc (args.tail.head)
      some (.var (Expr.mk (.bvMulHi w) rfl (.cons a (.cons b .nil))) bodyC)
  -- Carry-chain add data word (denote `addCarryWord a b cin`) ↦ `bvAddCarryLo w`
  -- (denote `addCarryWordC`, identical). The carry-in `cin : reg 1` transports
  -- to `sword 1`.
  | .thAddCarryLo w, args, bodyC =>
      let a := vTc (args.head)
      let b := vTc (args.tail.head)
      let cin := vTc (args.tail.tail.head)
      some (.var (Expr.mk (.bvAddCarryLo w) rfl
        (.cons a (.cons b (.cons cin .nil)))) bodyC)
  -- Carry-chain add carry-out bit (denote `carryOutBit a b cin`) ↦
  -- `bvAddCarryHi w` (denote `carryOutBitC`, identical); ret `reg 1 ↦ sword 1`.
  | .thAddCarryHi w, args, bodyC =>
      let a := vTc (args.head)
      let b := vTc (args.tail.head)
      let cin := vTc (args.tail.tail.head)
      some (.var (Expr.mk (.bvAddCarryHi w) rfl
        (.cons a (.cons b (.cons cin .nil)))) bodyC)
  | _, _, _ => none

/-- Lower a `Com thirDialect Γ t` to a `Com catCryptDialect (tcCtx Γ) (tcTy t)`.
    Structural on the `Com` constructor; each `.var` lowers its body first, then
    defers op-dispatch to `lowerVarStepTc`. Returns `none` exactly when some
    binding's op has no `catCryptDialect` image (the gaps of § module doc).
    The body's binding type is `tcTy (ret op)` after the `hret ▸` cast. -/
def lowerThirToCatCrypt : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com thirDialect Γ t → Option (Com catCryptDialect (tcCtx Γ) (tcTy t))
  | _, _, .ret v => some (.ret (vTc v))
  | _, _, .var (Expr.mk op hret args) body =>
      match lowerThirToCatCrypt body with
      | some bodyC =>
          -- `body : Com (ret op :: Γ) t` was lowered to
          -- `Com (tcTy (ret op) :: tcCtx Γ) (tcTy t)` (using `hret : ret op = t`
          -- transported to the binding type), feed it to the op step.
          lowerVarStepTc (t' := tcTy _) op args (hret ▸ bodyC)
      | none => none

/-! ## 5. Denotation preservation -/

/-- `Expr.lookupArgs` on a `cons` reduces to a `cons` of the head lookup and the
    tail lookups. Stated explicitly so `simp` can fire it through the `match`
    forms that `Com.denote`/`Expr.denote` leave behind. -/
@[simp] theorem lookupArgs_cons {d : Dialect} [TyDenote d.Ty] {Γ : Ctxt d}
    {t : d.Ty} {tys : List d.Ty} (v : Ctxt.Var Γ t)
    (rest : HVector (fun ty => Ctxt.Var Γ ty) tys) (V : Ctxt.Valuation Γ) :
    Expr.lookupArgs (.cons v rest) V = .cons (v.lookup V) (Expr.lookupArgs rest V) :=
  rfl

/-- `HVector.head` of a `cons` is the head element. Lets `simp` peel the
    operand projections that `Expr.denote` produces over `lookupArgs`. -/
@[simp] theorem hvector_head_cons {α : Type _} {f : α → Type _} {t : α}
    {tys : List α} (x : f t) (rest : HVector f tys) :
    (HVector.cons x rest).head = x := rfl

/-- `HVector.tail` of a `cons` is the tail vector. -/
@[simp] theorem hvector_tail_cons {α : Type _} {f : α → Type _} {t : α}
    {tys : List α} (x : f t) (rest : HVector f tys) :
    (HVector.cons x rest).tail = rest := rfl

/-- Head of the lookup of a `vTc`-headed argument vector bridges to the source
    lookup. `(lookupArgs (cons (vTc v) rest) (vTcVal V)).head = (vTc v).lookup
    (vTcVal V)` by `rfl`, then `vTc_lookup`. The `simp`-ready operand bridge for
    the `lowerVarStepTc_denote` arms. -/
@[simp] theorem lookupArgs_vTc_head {Γ : Ctxt jasminDialect} {w : Nat}
    {tys : List CryptoTy} (v : @Ctxt.Var thirDialect Γ (.reg w))
    (rest : HVector (fun ty => @Ctxt.Var catCryptDialect (tcCtx Γ) ty) tys)
    (V : Ctxt.Valuation Γ) :
    (Expr.lookupArgs (HVector.cons (vTc v) rest) (vTcVal V)).head = v.lookup V :=
  vTc_lookup v V

/-- Tail-head of the lookup of a 2+-element `vTc`-headed argument vector bridges
    to the second source lookup. -/
@[simp] theorem lookupArgs_vTc_tail_head {Γ : Ctxt jasminDialect} {w w' : Nat}
    {tys : List CryptoTy} (v : @Ctxt.Var thirDialect Γ (.reg w))
    (v' : @Ctxt.Var thirDialect Γ (.reg w'))
    (rest : HVector (fun ty => @Ctxt.Var catCryptDialect (tcCtx Γ) ty) tys)
    (V : Ctxt.Valuation Γ) :
    (Expr.lookupArgs (HVector.cons (vTc v) (HVector.cons (vTc v') rest))
      (vTcVal V)).tail.head = v'.lookup V :=
  vTc_lookup v' V

/-- Tail-tail-head bridge for a 3+-element `vTc`-headed argument vector (the
    carry-in operand of the bignum carry-chain arms). -/
@[simp] theorem lookupArgs_vTc_tail_tail_head {Γ : Ctxt jasminDialect}
    {w w' w'' : Nat} {tys : List CryptoTy}
    (v : @Ctxt.Var thirDialect Γ (.reg w)) (v' : @Ctxt.Var thirDialect Γ (.reg w'))
    (v'' : @Ctxt.Var thirDialect Γ (.reg w''))
    (rest : HVector (fun ty => @Ctxt.Var catCryptDialect (tcCtx Γ) ty) tys)
    (V : Ctxt.Valuation Γ) :
    (Expr.lookupArgs
      (HVector.cons (vTc v) (HVector.cons (vTc v') (HVector.cons (vTc v'') rest)))
      (vTcVal V)).tail.tail.head = v''.lookup V :=
  vTc_lookup v'' V

/-- The general (any-type) tagged form of `vTc_lookup`: transported lookup equals
    the `tcEntry`-tagged source lookup. On `reg` types `tcEntry` is the identity,
    recovering `vTc_lookup`. -/
theorem vTcVal_lookup_tagged {Γ : Ctxt jasminDialect} {t : JasminTy} :
    (v : @Ctxt.Var thirDialect Γ t) → (V : Ctxt.Valuation Γ) →
    (vTc v).lookup (vTcVal V) = tcEntry t (v.lookup V)
  | .here, .cons _ _ => rfl
  | .there v, .cons _ rest => by
      show (vTc v).lookup (vTcVal rest) = tcEntry t (v.lookup rest)
      exact vTcVal_lookup_tagged v rest

/-- `lowerVarStepTc` preserves denotation: when it lowers a binding (`some c`),
    denoting `c` against the transported valuation equals denoting the lowered
    body `bodyC` extended by the **transported THIR value** of that binding
    (`tcEntry (ret op) (thirDenote op …)`). Each covered arm reduces by `simp`
    using `vTc_lookup` (the two/one operand vars transport cast-free). -/
theorem lowerVarStepTc_denote {Γ : Ctxt jasminDialect} {t' : CryptoTy}
    (op : thirDialect.Op)
    (args : HVector (fun ty => @Ctxt.Var thirDialect Γ ty)
      (DialectSignature.sig (d := thirDialect) op))
    (bodyC : Com catCryptDialect (tcTy (DialectSignature.ret (d := thirDialect) op)
      :: tcCtx Γ) t')
    (V : Ctxt.Valuation Γ)
    (c : Com catCryptDialect (tcCtx Γ) t')
    (hstep : lowerVarStepTc op args bodyC = some c) :
    c.denote (vTcVal V)
      = bodyC.denote ((vTcVal V).extend
          (tcEntry (DialectSignature.ret (d := thirDialect) op)
            (DialectDenote.denote (self := thirDenote) op (Expr.lookupArgs args V)))) := by
  match op, args, bodyC with
  | .thBin bop w, .cons a₀ (.cons b₀ .nil), bodyC =>
      -- All nine `JasminBinOp`s lower (the six arith + `shl/shr/andn`). Unfold both
      -- denotations to the `lookupArgs` form, unfold the thir-side `JasminBinOp.apply`
      -- so it matches the dialect op denotation, peel `bodyC.denote` with `congr 1`,
      -- then bridge each operand lookup by `vTc_lookup` (cast-free on `reg`).
      cases bop <;>
        (simp only [lowerVarStepTc, mkBinC, Option.some.injEq] at hstep
         subst hstep
         simp only [Com.denote, Expr.denote, DialectDenote.denote, tcEntry,
           Ctxt.Valuation.extend, JasminBinOp.apply]
         apply congrArg
         repeat' (first | exact vTc_lookup _ V | congr 1))
  | .thShlImm w n, .cons a₀ .nil, bodyC =>
      simp only [lowerVarStepTc, Option.some.injEq] at hstep
      subst hstep
      simp only [Com.denote, Expr.denote, DialectDenote.denote, tcEntry,
        Ctxt.Valuation.extend]
      congr 3
      exact vTc_lookup _ V
  | .thShrImm w n, .cons a₀ .nil, bodyC =>
      simp only [lowerVarStepTc, Option.some.injEq] at hstep
      subst hstep
      simp only [Com.denote, Expr.denote, DialectDenote.denote, tcEntry,
        Ctxt.Valuation.extend, BitVec.ushiftRight_eq]
      congr 3
      exact vTc_lookup _ V
  | .thConst w n, .nil, bodyC =>
      simp only [lowerVarStepTc, Option.some.injEq] at hstep
      subst hstep
      rfl
  | .thRor w n, .cons a₀ .nil, bodyC =>
      -- `bvRor` denotes `a.rotateRight n`, identical to thir `thRor`; one operand.
      simp only [lowerVarStepTc, Option.some.injEq] at hstep
      subst hstep
      simp only [Com.denote, Expr.denote, DialectDenote.denote, tcEntry,
        Ctxt.Valuation.extend]
      congr 3
      exact vTc_lookup _ V
  | .thSarImm w n, .cons a₀ .nil, bodyC =>
      -- `bvShiftRA` denotes `BitVec.sshiftRight a n`, identical to thir `thSarImm`.
      simp only [lowerVarStepTc, Option.some.injEq] at hstep
      subst hstep
      simp only [Com.denote, Expr.denote, DialectDenote.denote, tcEntry,
        Ctxt.Valuation.extend]
      congr 3
      exact vTc_lookup _ V
  | .thMulHi w, .cons a₀ (.cons b₀ .nil), bodyC =>
      -- `bvMulHi` denotes `mulHiC` = thir `mulHiW` (identical defs); operands
      -- bridge cast-free.
      simp only [lowerVarStepTc, Option.some.injEq] at hstep
      subst hstep
      simp only [Com.denote, Expr.denote, DialectDenote.denote, tcEntry,
        Ctxt.Valuation.extend, CatCryptDialect.mulHiC, JasminDialect.mulHiW]
      apply congrArg
      repeat' (first | exact vTc_lookup _ V | congr 1)
  | .thAddCarryLo w, .cons a₀ (.cons b₀ (.cons c₀ .nil)), bodyC =>
      -- `bvAddCarryLo` denotes `addCarryWordC` = thir `addCarryWord`; the carry-in
      -- `reg 1 ↦ sword 1` operand bridges cast-free like the data words.
      simp only [lowerVarStepTc, Option.some.injEq] at hstep
      subst hstep
      simp only [Com.denote, Expr.denote, DialectDenote.denote, tcEntry,
        Ctxt.Valuation.extend, CatCryptDialect.addCarryWordC, JasminDialect.addCarryWord]
      apply congrArg
      repeat' (first | exact vTc_lookup _ V | congr 1)
  | .thAddCarryHi w, .cons a₀ (.cons b₀ (.cons c₀ .nil)), bodyC =>
      -- `bvAddCarryHi` denotes `carryOutBitC` = thir `carryOutBit`; ret `reg 1 ↦
      -- sword 1`.
      simp only [lowerVarStepTc, Option.some.injEq] at hstep
      subst hstep
      simp only [Com.denote, Expr.denote, DialectDenote.denote, tcEntry,
        Ctxt.Valuation.extend, CatCryptDialect.carryOutBitC, JasminDialect.carryOutBit]
      apply congrArg
      repeat' (first | exact vTc_lookup _ V | congr 1)

/-- **The main lowering soundness theorem.** When `lowerThirToCatCrypt c` succeeds
    (`some c'`), the lowered `Com catCryptDialect` denotes the **transported** THIR
    denotation: `c'.denote (vTcVal V) = tcEntry t (c.denote V)`. On the `reg`
    fragment `tcEntry` is the identity, so this is exact denotation preservation
    (the carriers `⟦tcTy t⟧` and `⟦t⟧` are defeq). Structural induction on `c`:
    `.ret` is `vTc_lookup` (cast-free on `reg`, and `tcEntry`-tagged in general);
    `.var` combines the body IH with `lowerVarStepTc_denote`. -/
theorem lowerThirToCatCrypt_denote : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com thirDialect Γ t) → (V : Ctxt.Valuation Γ) →
    (c' : Com catCryptDialect (tcCtx Γ) (tcTy t)) →
    lowerThirToCatCrypt c = some c' →
    c'.denote (vTcVal V) = tcEntry t (c.denote V)
  | _, _, .ret v, V, c', hc => by
      simp only [lowerThirToCatCrypt, Option.some.injEq] at hc
      subst hc
      simp only [Com.denote]
      exact vTcVal_lookup_tagged v V
  | _, _, .var (Expr.mk op hret args) body, V, c', hc => by
      -- Recurse on `body` FIRST (the literal subterm — keeps the termination
      -- measure happy), then `subst hret` to align the binding type.
      have ih := lowerThirToCatCrypt_denote body
        (V.extend (hret ▸ DialectDenote.denote (self := thirDenote) op
          (Expr.lookupArgs args V)))
      subst hret
      -- `lowerThirToCatCrypt (.var (Expr.mk op rfl args) body)` defers to
      -- `lowerVarStepTc op args (lowerThirToCatCrypt body)`; case on the body.
      simp only [lowerThirToCatCrypt] at hc
      cases hb : lowerThirToCatCrypt body with
      | none => rw [hb] at hc; simp only [reduceCtorEq] at hc
      | some bodyC =>
          rw [hb] at hc
          -- `c.denote V = body.denote (extend (thirDenote op (lookupArgs args V)))`
          simp only [Com.denote, Expr.denote]
          -- catCrypt side: `lowerVarStepTc_denote` rewrites `c'.denote` to
          -- `bodyC.denote (extend (tcEntry (ret op) (thirDenote op …)))`; the IH on
          -- `body` then turns `bodyC.denote (extend X)` into the THIR `body.denote`.
          rw [lowerVarStepTc_denote op args bodyC V c' hc]
          exact ih bodyC hb
  termination_by Γ t c => sizeOf c
  decreasing_by simp_wf

/-! ## 6. Smoke demonstrator: a scalar `add` kernel climbs to `catCryptDialect`

`let s = a + b; ret s` over `[reg 64, reg 64]`, the THIR-front image of a hax
scalar body that today lands flat at `jasminDialect`. We lower it **up** to
`catCryptDialect` (a `bvAdd` over `[sword 64, sword 64]`) and confirm the edge
both *succeeds* (`isSome`) and is denotation-preserving — so the body now reaches
the high algebraic stack. -/

/-- THIR-front `add` kernel: `let s = a + b; ret s` over two `reg 64` inputs. -/
def smokeAddThir : Com thirDialect [.reg 64, .reg 64] (.reg 64) :=
  .var (.mk (.thBin .add 64) rfl (.cons (.there .here) (.cons .here .nil)))
    (.ret .here)

/-- The edge succeeds: the scalar `add` kernel lifts into `catCryptDialect`
    (a `bvAdd 64` over `[sword 64, sword 64]`). -/
theorem smokeAddThir_lifts : (lowerThirToCatCrypt smokeAddThir).isSome := by
  decide

/-- The lifted `catCryptDialect` program. -/
noncomputable def smokeAddCatCrypt : Com catCryptDialect [.sword 64, .sword 64] (.sword 64) :=
  (lowerThirToCatCrypt smokeAddThir).get smokeAddThir_lifts

/-- The lift is denotation-preserving: the `catCryptDialect` `bvAdd` program
    denotes exactly the THIR `add` kernel, on every input (`reg`-fragment, so
    `tcEntry` is the identity). By `lowerThirToCatCrypt_denote`. -/
theorem smokeAddThir_lift_denote (V : Ctxt.Valuation (d := jasminDialect) [.reg 64, .reg 64]) :
    smokeAddCatCrypt.denote (vTcVal V) = tcEntry (.reg 64) (smokeAddThir.denote V) :=
  lowerThirToCatCrypt_denote smokeAddThir V smokeAddCatCrypt
    (Option.eq_some_of_isSome smokeAddThir_lifts)

end CatCrypt.Crypto.SecureCompilation.VIR.ThirToCatCrypt
