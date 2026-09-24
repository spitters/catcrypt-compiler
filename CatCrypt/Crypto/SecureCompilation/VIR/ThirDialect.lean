/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.ComInline
public import CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT

/-!
# THIR VIR dialect and the verified `Com[thir] → Com[jasmin]` lowering

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

A real `thirDialect : Dialect` for the THIR front, together with a structurally
recursive, denotation-preserving lowering `lowerThir : Com thirDialect Γ t →
Com jasminDialect Γ t`. This turns the bespoke per-function `thirToJasmin` emit
(`ThirToComFront.lean`) into the front stage of a uniform two-stage
`Com`-lowering spine: a function compiles `THIR-AST → Com[thir] → Com[jasmin]`,
and the second arrow is this generic, proved lowering rather than a
per-function builder.

## Why reuse `JasminTy`

`thirDialect.Ty := JasminTy` (with the existing `JasminTy` `TyDenote`), so
`Ctxt`, `Var` and `HVector` are **identical** between the two dialects. A
`lowerThir` is then a structural rewrite of `Com`, and its denotation argument
is op-by-op; no type translation is needed. The two dialects differ only in
their `Op` set: `ThirOp` is a higher-level surface than `JasminOp`.

## The op-expansion that justifies the dialect

Most `ThirOp`s lower 1:1 to the matching `JasminOp` (`thBin → regArith`,
`thRor → rorImm`, `thShrImm → shrImm`, `thShlImm → shlImm`, `thCast → castW`,
`thConst → regConst`). The exception is `thBinLit op w n` — a
register-OP-immediate (`[reg w] → reg w`, denoting `op.apply a (ofNat w n)`),
which has **no single jasmin op**. It lowers to **two** jasmin ops:

```
let lit = regConst w n      -- materialise the immediate
let out = regArith op w a lit
```

So `lowerThir` is an op-EXPANSION: the body after the expanded binding is
weakened through the inserted `regConst` binding. The weakening is `Com.rename`
(`MergeCom`) along `Ctxt.Hom.lift (Ctxt.Hom.weakenOne …)`, and its denotation
transparency is the standard de Bruijn substitution law (`Com.denote_rename`,
proved here from `ComInline`'s `Expr.denote_rename` and `Var.lookup_rename`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComInline (pullV)

/-! ## 1. The THIR op set -/

/-- Operation tags for the THIR dialect. A higher-level surface than `JasminOp`:
    the binops carry the register/register and register/immediate shapes of the
    THIR-ANF front, and `thBinLit` is the one op with no 1:1 jasmin image (it
    expands to a `regConst` + `regArith` pair). -/
inductive ThirOp where
  /-- Register/register binary op `[reg w, reg w] → reg w`. Lowers 1:1 to
      `regArith op w`. -/
  | thBin (op : JasminBinOp) (w : Nat)
  /-- Register-OP-immediate `[reg w] → reg w`, denoting `op.apply a (ofNat w n)`.
      The higher-level op: it lowers to **two** jasmin ops (`regConst w n` to a
      fresh var, then `regArith op w` on the original arg and that var). -/
  | thBinLit (op : JasminBinOp) (w n : Nat)
  /-- Native right-rotate by a compile-time `n`, `[reg w] → reg w`. Lowers 1:1
      to `rorImm w n`. -/
  | thRor (w n : Nat)
  /-- Native logical right-shift by a compile-time `n`, `[reg w] → reg w`.
      Lowers 1:1 to `shrImm w n`. -/
  | thShrImm (w n : Nat)
  /-- Native **arithmetic** right-shift by a compile-time `n`, `[reg w] → reg w`,
      denoting `BitVec.sshiftRight`. Lowers 1:1 to `sarImm w n`. The signed twin
      of `thShrImm`. -/
  | thSarImm (w n : Nat)
  /-- Native logical left-shift by a compile-time `n`, `[reg w] → reg w`. Lowers
      1:1 to `shlImm w n`. -/
  | thShlImm (w n : Nat)
  /-- Width cast `reg w → reg w'`. Lowers 1:1 to `castW w w'`. -/
  | thCast (w w' : Nat)
  /-- Nullary compile-time constant `[] → reg w`, `= ofNat w n`. Lowers 1:1 to
      `regConst w n`. -/
  | thConst (w n : Nat)
  /-- High word of the widening multiply `a * b`, `[reg w, reg w] → reg w`
      (`mulHiW`). The low word is the existing `thBin .mul w`; together they are
      MULX's `(hi, lo)`. Lowers 1:1 to `mulhi w`. The front unlock for
      bignum/EC/pairing field arithmetic (Class B). -/
  | thMulHi (w : Nat)
  /-- Carry-chain add **data** word `a + b + cin`, `[reg w, reg w, reg 1] →
      reg w` (`addCarryWord`). Lowers 1:1 to `addCarryLo w`. -/
  | thAddCarryLo (w : Nat)
  /-- Carry-chain add **carry-out** bit of `a + b + cin`, `[reg w, reg w, reg 1]
      → reg 1` (`carryOutBit`). The `reg 1` result threads into the next limb's
      carry-in. Lowers 1:1 to `addCarryHi w`. -/
  | thAddCarryHi (w : Nat)
  /-- Constant-time SELECT `if cond then a else b`, `[reg 1, reg w, reg w] →
      reg w` (`selectW`). The condition is a 1-bit register; both operands are
      always evaluated, so the op is branch-free. Lowers 1:1 to `select w`. The
      front's constant-time primitive for the canonical conditional-subtract, the
      ladder `cswap`, and a rejection sampler's conditional core. -/
  | thSelect (w : Nat)
  /-- Opaque external leaf call (single-result), `argTys → retTy`. The front
      handle for kernel-to-kernel COMPOSITION (treehash, FO transforms,
      Fiat-Shamir): a function calls an already-verified single-result leaf by
      name. Mirrors `JasminOp.extCall`; lowers 1:1 to it. The callee is opaque
      (`jasminExtSem name argTys retTy`), so its value-agreement is a separate
      leaf obligation. Single-result only (the multi-output `extCall` ABI is not
      modelled). The E5a front unlock for whole-protocol composition. -/
  | thExtCall (name : String) (argTys : List JasminTy) (retTy : JasminTy)
  /-- AVX-512 ZMM 8×u64 packed-lane op, `[reg 512, reg 512] → reg 512`
      (`zmmPackQ bop`): a per-64-bit-lane `bop` over two `reg 512` ZMM registers
      with no cross-lane carry. Lowers 1:1 to `JasminOp.vpackZMM bop`. The front
      handle for the homogeneous-512 SIMD lane surface (Poseidon2 MDS / RC-add,
      8-way packed add). The verified-chain image of `#VPADD_8u64` / `#VPSUB_8u64`
      / `#VPMULL_8u64` / `#VPSRL_8u64` (`bop = .add/.sub/.mul/.shr`). -/
  | thVpack (bop : JasminBinOp)
  /-- Compile-time-literal tag equality `a == ofNat w k`, `[reg w] → reg 1`,
      denoting `1` iff the register holds the constant `k` and `0` otherwise. The
      front handle for the canonical MATCH/enum dispatch: hax extracts an enum as
      an opaque `usize` tag (no ADT constructors survive extraction), so a `match
      tag { … }` is a sequence of tag tests `tag == k` each feeding a
      branch-free `thSelect` (E5b). The `reg 1` result threads into a `thSelect`
      condition exactly like a `carryOutBit`. Lowers 1:1 to the opaque single-
      result leaf `extCall "thir_eqlit_{w}_{k}" [reg w] (reg 1)`: there is no
      jasmin compare op in the carry-free alphabet, so the tag test is treated as
      an already-verified constant-time equality leaf (its value-agreement is a
      separate KAT-discharged obligation, exactly as the §18 `compress` leaf).
      The dispatch SELECT built on top of it is fully transparent. The leaf name
      is keyed on `w`/`k` so distinct tag tests are distinct callees. The compare
      is against a *public* compile-time constant, so it is constant-time. -/
  | thEqLit (w k : Nat)
  deriving DecidableEq

/-- The opaque-leaf name for the tag-equality op `thEqLit w k`: `a == k` is
    realised as a call to `thir_eqlit_{w}_{k} : [reg w] → reg 1`. Keyed on
    `w`/`k` so distinct tag tests lower to distinct (independently KAT-checked)
    callees. -/
def eqLitLeafName (w k : Nat) : String :=
  "thir_eqlit_" ++ toString w ++ "_" ++ toString k

/-! ## 2. The dialect -/

/-- The THIR dialect: `Op` is `ThirOp`, `Ty` reuses `JasminTy` (and its existing
    `TyDenote`). Sharing `Ty` with `jasminDialect` makes `Ctxt`/`Var`/`HVector`
    identical between the two, so `lowerThir` is a structural `Com` rewrite. -/
@[reducible] def thirDialect : Dialect :=
  { Op := ThirOp, Ty := JasminTy }

/-! ## 3. Op signatures -/

@[reducible] instance thirSignature : DialectSignature thirDialect where
  sig op := match op with
    | .thBin _ w => [.reg w, .reg w]
    | .thBinLit _ w _ => [.reg w]
    | .thRor w _ => [.reg w]
    | .thShrImm w _ => [.reg w]
    | .thSarImm w _ => [.reg w]
    | .thShlImm w _ => [.reg w]
    | .thCast w _ => [.reg w]
    | .thConst _ _ => []
    | .thMulHi w => [.reg w, .reg w]
    | .thAddCarryLo w => [.reg w, .reg w, .reg 1]
    | .thAddCarryHi w => [.reg w, .reg w, .reg 1]
    | .thSelect w => [.reg 1, .reg w, .reg w]
    | .thExtCall _ argTys _ => argTys
    | .thVpack _ => [.reg 512, .reg 512]
    | .thEqLit w _ => [.reg w]
  ret op := match op with
    | .thBin _ w => .reg w
    | .thBinLit _ w _ => .reg w
    | .thRor w _ => .reg w
    | .thShrImm w _ => .reg w
    | .thSarImm w _ => .reg w
    | .thShlImm w _ => .reg w
    | .thCast _ w' => .reg w'
    | .thConst w _ => .reg w
    | .thMulHi w => .reg w
    | .thAddCarryLo w => .reg w
    | .thAddCarryHi _ => .reg 1
    | .thSelect w => .reg w
    | .thExtCall _ _ retTy => retTy
    | .thVpack _ => .reg 512
    | .thEqLit _ _ => .reg 1

/-! ## 4. Op denotation -/

instance thirDenote : DialectDenote thirDialect where
  denote op := match op with
    | .thBin bop w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        bop.apply a b
    | .thBinLit bop w n => fun args =>
        let a : BitVec w := args.head
        bop.apply a (BitVec.ofNat w n)
    | .thRor w n => fun args =>
        let a : BitVec w := args.head
        a.rotateRight n
    | .thShrImm w n => fun args =>
        let a : BitVec w := args.head
        a >>> n
    | .thSarImm w n => fun args =>
        let a : BitVec w := args.head
        BitVec.sshiftRight a n
    | .thShlImm w n => fun args =>
        let a : BitVec w := args.head
        a <<< n
    | .thCast _ w' => fun args =>
        show BitVec w' from (args.head : BitVec _).zeroExtend w'
    | .thConst w n => fun _ => (BitVec.ofNat w n)
    | .thMulHi w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        mulHiW a b
    | .thAddCarryLo w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        let cin : BitVec 1 := args.tail.tail.head
        addCarryWord a b cin
    | .thAddCarryHi w => fun args =>
        let a : BitVec w := args.head
        let b : BitVec w := args.tail.head
        let cin : BitVec 1 := args.tail.tail.head
        carryOutBit a b cin
    | .thSelect w => fun args =>
        let cond : BitVec 1 := args.head
        let a : BitVec w := args.tail.head
        let b : BitVec w := args.tail.tail.head
        selectW cond a b
    | .thExtCall name argTys retTy => fun args => jasminExtSem name argTys retTy args
    | .thVpack bop => fun args =>
        let a : BitVec 512 := args.head
        let b : BitVec 512 := args.tail.head
        zmmPackQ bop a b
    | .thEqLit w k => fun args =>
        -- The tag test is an OPAQUE constant-time equality leaf (no jasmin
        -- compare op): its denotation is the leaf semantics of the `extCall`
        -- it lowers to, exactly as §18's `compress`. So `lowerVarStep` is
        -- denotation-`rfl` and the *value* of `a == k` is the leaf's separate
        -- (KAT-discharged) obligation, NOT an in-Lean `if a = ofNat w k`.
        (jasminExtSem (eqLitLeafName w k) [.reg w] (.reg 1) args : BitVec 1)

/-! ## 4b. Variable / args transport between the two dialects

`Ctxt.Var {d} Γ t` is indexed by the dialect `d` (the `here`/`there`
constructors don't mention `d.Op`, but the *type* still carries `d`), so a
`Var thirDialect Γ t` is not definitionally a `Var jasminDialect Γ t`. Since
both dialects share `Ty := JasminTy`, the contexts `Ctxt thirDialect` and
`Ctxt jasminDialect` are the **same** type (`List JasminTy`), so we transport a
variable structurally. `Valuation` is dialect-free (`HVector (fun t => ⟦t⟧) Γ`),
so one valuation serves both dialects; transport preserves lookup. -/

/-- Transport a THIR-dialect variable to the jasmin dialect (same `Ctxt`/`Ty`). -/
def vT {Γ : Ctxt jasminDialect} {t : JasminTy} :
    @Ctxt.Var thirDialect Γ t → @Ctxt.Var jasminDialect Γ t
  | .here => .here
  | .there v => .there (vT v)

/-- Transport an HVector of THIR-dialect variables to the jasmin dialect. -/
def argsT {Γ : Ctxt jasminDialect} :
    {tys : List JasminTy} →
    HVector (fun ty => @Ctxt.Var thirDialect Γ ty) tys →
    HVector (fun ty => @Ctxt.Var jasminDialect Γ ty) tys
  | [], .nil => .nil
  | _ :: _, .cons v rest => .cons (vT v) (argsT rest)

/-- Transport preserves variable lookup (the valuation type is dialect-free). -/
theorem vT_lookup {Γ : Ctxt jasminDialect} {t : JasminTy} :
    (v : @Ctxt.Var thirDialect Γ t) → (V : Ctxt.Valuation Γ) →
    (vT v).lookup V = v.lookup V
  | .here, .cons _ _ => rfl
  | .there v, .cons _ V => by
      show (vT v).lookup V = v.lookup V
      exact vT_lookup v V

/-- Transport commutes with argument lookup. -/
theorem argsT_lookupArgs {Γ : Ctxt jasminDialect} :
    {tys : List JasminTy} →
    (args : HVector (fun ty => @Ctxt.Var thirDialect Γ ty) tys) →
    (V : Ctxt.Valuation Γ) →
    Expr.lookupArgs (argsT args) V = Expr.lookupArgs args V
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, V => by
      show HVector.cons ((vT v).lookup V) (Expr.lookupArgs (argsT rest) V)
        = HVector.cons (v.lookup V) (Expr.lookupArgs rest V)
      rw [vT_lookup v V, argsT_lookupArgs rest V]

/-! ## 5. `Com.denote_rename` for `jasminDialect`

The de Bruijn substitution law for whole programs, proved from `ComInline`'s
`Expr.denote_rename` and `Var.lookup_rename`. Needed for the `thBinLit`
expansion arm, where the body is weakened through the inserted `regConst`
binding. `pullV` (from `ComInline`) characterises the renamed valuation. -/

/-- `pullV` through a `.there`-shifted hom drops the freshly-added head binding:
    pulling back along `fun v => (g v).there` against `x :: W` is the same as
    pulling back along `g` against `W`. -/
theorem pullV_there {Γ Δ : Ctxt jasminDialect} {s : JasminTy}
    (g : Ctxt.Hom Γ Δ) (x : ⟦s⟧) (W : Ctxt.Valuation Δ) :
    pullV (fun {_} v => (g v).there) (HVector.cons x W) = pullV g W := by
  induction Γ with
  | nil => rfl
  | cons a Γ ih =>
      simp only [pullV]
      congr 1
      exact ih (fun {_} v => g (.there v))

/-- Pulling back along the identity hom is the identity on valuations. -/
theorem pullV_id {Γ : Ctxt jasminDialect} (V : Ctxt.Valuation Γ) :
    pullV (fun {_} v => v) V = V := by
  induction Γ with
  | nil => cases V; rfl
  | cons a Γ ih =>
      match V with
      | .cons x W =>
          show HVector.cons _ (pullV (fun {_} v => ((fun {_} u => u) v).there)
            (HVector.cons x W)) = HVector.cons x W
          rw [pullV_there (fun {_} v => v) x W, ih W]
          rfl

/-- Pulling back along the double weakening `fun v => v.there.there` against a
    two-element-extended valuation drops both fresh head bindings. Stated in
    `HVector.cons` form so it fires as a `simp` lemma against the goal. -/
@[simp] theorem pullV_weaken2 {Γ : Ctxt jasminDialect} {s₁ s₂ : JasminTy}
    (a : ⟦s₁⟧) (b : ⟦s₂⟧) (W : Ctxt.Valuation Γ) :
    pullV (fun {_} v => Ctxt.Var.there (Ctxt.Var.there v))
        (HVector.cons a (HVector.cons b W)) = W := by
  rw [pullV_there (fun {_} v => Ctxt.Var.there v) a (HVector.cons b W),
    pullV_there (fun {_} v => v) b W, pullV_id]

/-- The exact pullback for the `thBinLit` expansion: pulling a valuation back
    along `lift (weakenOne)` against `a :: b :: W` keeps the head `a` and the
    tail `W`, dropping the inserted (middle) binding `b`. -/
theorem pullV_lift_weakenOne {Γ : Ctxt jasminDialect} {s s' : JasminTy}
    (a : ⟦s'⟧) (b : ⟦s⟧) (W : Ctxt.Valuation Γ) :
    pullV (Ctxt.Hom.lift (Ctxt.Hom.weakenOne Γ s))
        (HVector.cons a (HVector.cons b W))
      = HVector.cons a W := by
  show HVector.cons (a : ⟦s'⟧) (pullV (fun {_} v =>
      Ctxt.Var.there (Ctxt.Var.there v)) (HVector.cons a (HVector.cons b W)))
    = HVector.cons a W
  rw [pullV_weaken2]

/-- Renaming a `Com jasminDialect` and denoting it against `V` equals denoting
    the original against the pulled-back valuation. The whole-program analogue
    of `Expr.denote_rename`. -/
theorem Com.denote_rename {Γ Γ' : Ctxt jasminDialect} {t : JasminTy}
    (h : Ctxt.Hom Γ Γ') (c : Com jasminDialect Γ t) (V : Ctxt.Valuation Γ') :
    (Com.rename h c).denote V = c.denote (pullV h V) := by
  induction c generalizing Γ' with
  | ret v =>
      simp only [Com.rename, Com.denote]
      exact ComInline.Ctxt.Var.lookup_rename h v V
  | var e body ih =>
      simp only [Com.rename, Com.denote]
      rw [ih h.lift (V.extend ((e.rename h).denote V))]
      rw [ComInline.Expr.denote_rename h e V]
      congr 1
      show HVector.cons (e.denote (pullV h V)) (pullV (fun {_} v => (h v).there)
          (HVector.cons (e.denote (pullV h V)) V))
        = HVector.cons (e.denote (pullV h V)) (pullV h V)
      rw [pullV_there h (e.denote (pullV h V)) V]

/-! ## 6. The lowering `Com[thir] → Com[jasmin]`

Structural recursion on `Com thirDialect`, matching the op inside each binding.
`.ret` is unchanged; the six 1:1 ops rebuild the binding with the matching
jasmin op (the args HVector is reused — both dialects share `Ty`); `thBinLit`
expands to two jasmin bindings, weakening the lowered body through the inserted
`regConst` binding. -/

/-- Lower one THIR binding for op `op` over a body already lowered to
    `Com jasminDialect (ret op :: Γ) t`, producing the jasmin `Com Γ t`. No
    `hret`/`bt` cast is taken: the body's binding type is fixed to `ret op`, so
    every arm is cast-free. The six 1:1 arms rebind with the matching jasmin op
    (`argsT` transports the variable HVector); `thBinLit` EXPANDS to two bindings
    and weakens the body through the inserted `regConst` binding via
    `Com.rename`. -/
def lowerVarStep {Γ : Ctxt jasminDialect} {t : JasminTy}
    (op : thirDialect.Op)
    (args : HVector (fun ty => @Ctxt.Var thirDialect Γ ty)
      (DialectSignature.sig (d := thirDialect) op))
    (bodyJ : Com jasminDialect (DialectSignature.ret (d := thirDialect) op :: Γ) t) :
    Com jasminDialect Γ t :=
  match op, args, bodyJ with
  | .thBin bop w, args, bodyJ =>
      .var (Expr.mk (.regArith bop w) rfl (argsT args)) bodyJ
  | .thRor w n, args, bodyJ =>
      .var (Expr.mk (.rorImm w n) rfl (argsT args)) bodyJ
  | .thShrImm w n, args, bodyJ =>
      .var (Expr.mk (.shrImm w n) rfl (argsT args)) bodyJ
  | .thSarImm w n, args, bodyJ =>
      .var (Expr.mk (.sarImm w n) rfl (argsT args)) bodyJ
  | .thShlImm w n, args, bodyJ =>
      .var (Expr.mk (.shlImm w n) rfl (argsT args)) bodyJ
  | .thCast w w', args, bodyJ =>
      .var (Expr.mk (.castW w w') rfl (argsT args)) bodyJ
  | .thConst w n, args, bodyJ =>
      .var (Expr.mk (.regConst w n) rfl (argsT args)) bodyJ
  | .thMulHi w, args, bodyJ =>
      .var (Expr.mk (.mulhi w) rfl (argsT args)) bodyJ
  | .thAddCarryLo w, args, bodyJ =>
      .var (Expr.mk (.addCarryLo w) rfl (argsT args)) bodyJ
  | .thAddCarryHi w, args, bodyJ =>
      .var (Expr.mk (.addCarryHi w) rfl (argsT args)) bodyJ
  | .thSelect w, args, bodyJ =>
      .var (Expr.mk (.select w) rfl (argsT args)) bodyJ
  | .thExtCall name a r, args, bodyJ =>
      .var (Expr.mk (.extCall name a r) rfl (argsT args)) bodyJ
  | .thVpack bop, args, bodyJ =>
      .var (Expr.mk (.vpackZMM bop) rfl (argsT args)) bodyJ
  | .thEqLit w k, args, bodyJ =>
      -- Lower the tag test to the opaque single-result equality leaf
      -- `extCall (eqLitLeafName w k) [reg w] (reg 1)`. The `extCall`'s argTys
      -- `[reg w]` = the op's `sig`, and retTy `reg 1` = its `ret`, so `argsT
      -- args` typechecks and `retTy_eq` is `rfl`.
      .var (Expr.mk (.extCall (eqLitLeafName w k) [.reg w] (.reg 1)) rfl
        (argsT args)) bodyJ
  | .thBinLit bop w n, args, bodyJ =>
      -- bodyJ : Com (.reg w :: Γ) t (since ret (thBinLit) = .reg w).
      let a : @Ctxt.Var jasminDialect Γ (.reg w) := vT args.head
      let eLit : Expr jasminDialect Γ (.reg w) :=
        Expr.mk (.regConst w n) rfl .nil
      let eOut : Expr jasminDialect (.reg w :: Γ) (.reg w) :=
        Expr.mk (.regArith bop w) rfl (.cons (.there a) (.cons .here .nil))
      let bodyW' : Com jasminDialect (.reg w :: .reg w :: Γ) t :=
        Com.rename (Ctxt.Hom.lift (Ctxt.Hom.weakenOne Γ (.reg w))) bodyJ
      Com.var eLit (Com.var eOut bodyW')

/-- Lower a `Com thirDialect` to a `Com jasminDialect`. Structural on the `Com`
    constructor (`.ret`/`.var`); each `.var` defers its op-dispatch and the
    `thBinLit` expansion to `lowerVarStep` (casting the body's binding type
    `bt` to `ret op` via the expr's `retTy_eq` witness). -/
def lowerThir : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com thirDialect Γ t → Com jasminDialect Γ t
  | _, _, .ret v => .ret (vT v)
  | _, _, .var (Expr.mk op hret args) body =>
      lowerVarStep op args (hret ▸ lowerThir body : Com jasminDialect _ _)

/-! ## 7. Denotation preservation -/

/-- `lowerVarStep` preserves denotation: lowering one binding and denoting it
    equals denoting `bodyJ` extended by the **THIR** value of that binding
    (`Expr.denote (Expr.mk op hret args)` against the original valuation). The
    six 1:1 arms reduce by `simp`; the `thBinLit` arm uses `Com.denote_rename`
    (the inserted `regConst` binding is denotation-transparent) and the regConst
    value `= ofNat w n`. -/
theorem lowerVarStep_denote {Γ : Ctxt jasminDialect} {t : JasminTy}
    (op : thirDialect.Op)
    (args : HVector (fun ty => @Ctxt.Var thirDialect Γ ty)
      (DialectSignature.sig (d := thirDialect) op))
    (bodyJ : Com jasminDialect (DialectSignature.ret (d := thirDialect) op :: Γ) t)
    (V : Ctxt.Valuation Γ) :
    (lowerVarStep op args bodyJ).denote V
      = bodyJ.denote (V.extend
          (DialectDenote.denote (self := thirDenote) op (Expr.lookupArgs args V))) := by
  match op, args, bodyJ with
  | .thBin bop w, args, bodyJ =>
      simp only [lowerVarStep, Com.denote, Expr.denote, DialectDenote.denote,
        argsT_lookupArgs]
  | .thRor w n, args, bodyJ =>
      simp only [lowerVarStep, Com.denote, Expr.denote, DialectDenote.denote,
        argsT_lookupArgs]
  | .thShrImm w n, args, bodyJ =>
      simp only [lowerVarStep, Com.denote, Expr.denote, DialectDenote.denote,
        argsT_lookupArgs]
  | .thSarImm w n, args, bodyJ =>
      simp only [lowerVarStep, Com.denote, Expr.denote, DialectDenote.denote,
        argsT_lookupArgs]
  | .thShlImm w n, args, bodyJ =>
      simp only [lowerVarStep, Com.denote, Expr.denote, DialectDenote.denote,
        argsT_lookupArgs]
  | .thCast w w', args, bodyJ =>
      simp only [lowerVarStep, Com.denote, Expr.denote, DialectDenote.denote,
        argsT_lookupArgs]
  | .thConst w n, args, bodyJ =>
      simp only [lowerVarStep, Com.denote, Expr.denote, DialectDenote.denote]
  | .thMulHi w, args, bodyJ =>
      simp only [lowerVarStep, Com.denote, Expr.denote, DialectDenote.denote,
        argsT_lookupArgs]
  | .thAddCarryLo w, args, bodyJ =>
      simp only [lowerVarStep, Com.denote, Expr.denote, DialectDenote.denote,
        argsT_lookupArgs]
  | .thAddCarryHi w, args, bodyJ =>
      simp only [lowerVarStep, Com.denote, Expr.denote, DialectDenote.denote,
        argsT_lookupArgs]
  | .thSelect w, args, bodyJ =>
      simp only [lowerVarStep, Com.denote, Expr.denote, DialectDenote.denote,
        argsT_lookupArgs]
  | .thExtCall name a r, args, bodyJ =>
      simp only [lowerVarStep, Com.denote, Expr.denote, DialectDenote.denote,
        argsT_lookupArgs]
  | .thVpack bop, args, bodyJ =>
      simp only [lowerVarStep, Com.denote, Expr.denote, DialectDenote.denote,
        argsT_lookupArgs]
  | .thEqLit w k, args, bodyJ =>
      simp only [lowerVarStep, Com.denote, Expr.denote, DialectDenote.denote,
        argsT_lookupArgs]
  | .thBinLit bop w n, .cons a₀ .nil, bodyJ =>
      simp only [lowerVarStep, Com.denote, Expr.denote, DialectDenote.denote,
        Ctxt.Valuation.extend]
      rw [Com.denote_rename, pullV_lift_weakenOne]
      -- the inserted `regConst` binding (value `ofNat w n`) and the binop result
      -- compose to the THIR `thBinLit` denotation (`bop.apply (a₀.lookup V)
      -- (ofNat w n)`); the pullback dropped the inserted literal binding.
      congr 3
      exact vT_lookup a₀ V

/-- **The main lowering soundness theorem.** For every `Com thirDialect Γ t` the
    lowered `Com jasminDialect Γ t` has the same denotation, on every valuation.
    Structural induction on `c`: `.ret` is `vT_lookup`; `.var` combines the IH
    on the body with `lowerVarStep_denote`. -/
theorem lowerThir_denote : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (c : Com thirDialect Γ t) → (V : Ctxt.Valuation Γ) →
    (lowerThir c).denote V = c.denote V
  | _, _, .ret v, V => by
      simp only [lowerThir, Com.denote]; exact vT_lookup v V
  | _, _, .var (Expr.mk op hret args) body, V => by
      have ih := lowerThir_denote body
      subst hret
      simp only [lowerThir, Com.denote, Expr.denote]
      rw [lowerVarStep_denote op args (lowerThir body) V]
      exact ih _

/-! ## 8. Smoke demonstrator (the op-expansion)

A two-op `Com thirDialect` that uses `thBinLit` (the expanding op): on input
`x : BitVec 32`,

    let y = thBinLit .xor 32 255 x    -- y = x ^^^ (ofNat 32 255)
    ret y

`lowerThir smokeThir` expands the single `thBinLit` binding into the jasmin pair
`regConst 32 255; regArith xor`. The theorem checks the two denote equally. -/

/-- Smoke program over `[reg 32]` using the expanding `thBinLit` op. -/
def smokeThir : Com thirDialect [.reg 32] (.reg 32) :=
  .var (.mk (.thBinLit .xor 32 255) rfl (.cons .here .nil))
    (.ret .here)

/-- The op-expansion demonstrator: the lowered (2-op jasmin) program denotes
    exactly like the source (1-op thir) program, on every input. By
    `lowerThir_denote`; also checked on a concrete input below. -/
theorem smokeThir_lower_denote (V : Ctxt.Valuation (d := jasminDialect) [.reg 32]) :
    (lowerThir smokeThir).denote V = smokeThir.denote V :=
  lowerThir_denote smokeThir V

/-- Concrete check of the expansion: `5 ^^^ 255 = 250`. -/
example :
    (lowerThir smokeThir).denote (.cons (5 : BitVec 32) .nil)
      = ((5 : BitVec 32) ^^^ (BitVec.ofNat 32 255)) := by
  rw [smokeThir_lower_denote]
  show ((5 : BitVec 32) ^^^ BitVec.ofNat 32 255) = (5 : BitVec 32) ^^^ BitVec.ofNat 32 255
  rfl

/-! ## 9. The bounded FOR-loop front construct

The front's straight-line surface (`ThirOp` cascade) has no loop. This section
defines the **bounded for-loop** front construct as a thin wrapper over a THIR-dialect
loop body, lowered to the **existing** jasmin for-loop layer (`JForProg`,
`JasminPrint.lean` §7) — NOT a new `JasminOp`. A `ThirForProg` is the THIR analogue
of `JForProg`: a static public trip count `n` plus a loop-carried-accumulator
update `Com thirDialect [accTy] accTy`. Its lowering reuses the generic, proved
`lowerThir` on the body and the unchanged jasmin loop layer for the iteration
structure, so the round-loop / data-independent-loop shape compiles with no new
control-flow op.

### Constant-time note

The trip count `n` is a **public** compile-time field of `ThirForProg` (never a
runtime register), and the loop index ranges over the public sequence `0..n`. So
the loop is data-independent control flow and adds no CT obligation beyond its
body — exactly `JForProgCT`'s headline. A *secret-dependent* trip count (rejection
sampling) is NOT expressible here; it needs the runtime-`while` (`RWhileNz`) layer
and a fueled denotation, the flagged follow-on (`bench/thir_front_loop/Makefile`).

### Why this is the kernel→whole-primitive bridge

A whole-primitive driver (a SHA/BLAKE compression loop, an ARX round schedule, a
Horner/MAC accumulate, an NTT layer sweep) is a body run a public number of times
threading a register-state accumulator. The straight-line front could only emit one
unrolled kernel; `ThirForProg` emits the body **once** under a real `for i = 0 to n`.
-/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (JForProg)

/-- A bounded for-loop in the THIR front over a single loop-carried accumulator
    of type `accTy`. The THIR analogue of `JForProg`: a static public trip count
    `n` and a per-iteration update `Com thirDialect [accTy] accTy` whose one free
    de Bruijn variable (`.here`) is the accumulator. -/
structure ThirForProg (accTy : JasminTy) where
  /-- Static, public iteration count. -/
  n : Nat
  /-- The accumulator-update body in the THIR dialect: `acc ↦ body(acc)`. -/
  update : Com thirDialect [accTy] accTy

/-- One iteration of the THIR loop: run the THIR `update` body on the singleton
    accumulator valuation `[acc]`. -/
def ThirForProg.step {accTy : JasminTy} (p : ThirForProg accTy)
    (acc : ⟦accTy⟧) : ⟦accTy⟧ :=
  p.update.denote (.cons acc .nil)

/-- Total `n`-fold THIR denotation: iterate the THIR `step` `n` times from the
    initial accumulator. No fuel — `n` is the static public trip count. -/
def ThirForProg.denote {accTy : JasminTy} (p : ThirForProg accTy)
    (init : ⟦accTy⟧) : ⟦accTy⟧ :=
  (List.range p.n).foldl (fun acc _ => p.step acc) init

/-- Lower a THIR bounded for-loop to the EXISTING jasmin for-loop layer: the
    trip count is carried unchanged and the loop body is lowered by the generic,
    proved `lowerThir`. No new `JasminOp` or `JForProg` change — only the body's
    ops are expanded by `lowerThir`; the `for i = 0 to n` structure is the
    unchanged `JForProg`. -/
def ThirForProg.toJForProg {accTy : JasminTy} (p : ThirForProg accTy) :
    JForProg accTy :=
  { n := p.n, update := lowerThir p.update }

/-- One lowered iteration agrees with the THIR iteration: the jasmin loop body
    `lowerThir update` denotes exactly the THIR body, on every accumulator. This
    is `lowerThir_denote` specialised to the singleton accumulator valuation. -/
theorem toJForProg_step {accTy : JasminTy} (p : ThirForProg accTy)
    (acc : ⟦accTy⟧) :
    p.toJForProg.step acc = p.step acc := by
  show (lowerThir p.update).denote (.cons acc .nil)
    = p.update.denote (.cons acc .nil)
  exact lowerThir_denote p.update (.cons acc .nil)

/-- A `foldl` whose per-element function only depends on the accumulator, with two
    functions agreeing on every accumulator, coincides over any list and seed. The
    bridge from the lowered loop's fold to the THIR loop's fold. -/
theorem foldl_step_congr {accTy : JasminTy} {β : Type}
    (f g : ⟦accTy⟧ → ⟦accTy⟧) (hfg : ∀ acc, f acc = g acc) :
    ∀ (l : List β) (init : ⟦accTy⟧),
      l.foldl (fun acc _ => f acc) init = l.foldl (fun acc _ => g acc) init
  | [], _ => rfl
  | _ :: l, init => by
      rw [List.foldl_cons, List.foldl_cons, hfg init]
      exact foldl_step_congr f g hfg l (g init)

/-- **The bounded-FOR lowering soundness (`n`-fold denotation).** The lowered
    jasmin for-loop (`toJForProg`, run through the unchanged `JForProg.denote`)
    computes exactly the THIR loop's `n`-fold denotation, on every initial
    accumulator. The loop *structure* (the `n`-fold iteration of `JForProg.denote`)
    is the existing jasmin loop layer; the per-iteration body agreement is
    `toJForProg_step` (i.e. `lowerThir_denote`). Both sides are the same
    `List.range n` fold; they coincide because their per-step functions agree on
    every accumulator. -/
theorem toJForProg_denote {accTy : JasminTy} (p : ThirForProg accTy)
    (init : ⟦accTy⟧) :
    p.toJForProg.denote init = p.denote init := by
  show (List.range p.toJForProg.n).foldl (fun acc _ => p.toJForProg.step acc) init
    = (List.range p.n).foldl (fun acc _ => p.step acc) init
  exact foldl_step_congr (fun acc => p.toJForProg.step acc) (fun acc => p.step acc)
    (toJForProg_step p) (List.range p.n) init

/-! ## 10. Smoke demonstrator (a bounded loop over the expanding op)

A bounded THIR loop whose body is the §8 `thBinLit` xor-with-constant, iterated a
public number of times. Lowering threads each iteration through the
`regConst; regArith` expansion; the `n`-fold denotation is closed by
`toJForProg_denote` and checked on a concrete trip count below. -/

/-- Smoke loop: `acc := acc ^^^ (ofNat 32 255)`, 3 iterations. The body is the
    expanding `thBinLit` op; the loop is the new bounded-FOR front construct. -/
def smokeForThir : ThirForProg (.reg 32) :=
  { n := 3
    update :=
      .var (.mk (.thBinLit .xor 32 255) rfl (.cons .here .nil))
        (.ret .here) }

/-- The bounded-loop demonstrator: the lowered jasmin for-loop denotes exactly the
    THIR loop's `n`-fold, on every initial accumulator. By `toJForProg_denote`. -/
theorem smokeForThir_lower_denote (init : BitVec 32) :
    smokeForThir.toJForProg.denote init = smokeForThir.denote init :=
  toJForProg_denote smokeForThir init

/-- Concrete check: `x ^^^ 255` thrice is `x ^^^ 255` (xor is self-inverse, so an
    odd count is one xor). From `0`: `0 ^^^ 255 ^^^ 255 ^^^ 255 = 255`. -/
example : smokeForThir.toJForProg.denote (0 : BitVec 32) = (255 : BitVec 32) := by
  rw [smokeForThir_lower_denote]
  rfl

end CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
