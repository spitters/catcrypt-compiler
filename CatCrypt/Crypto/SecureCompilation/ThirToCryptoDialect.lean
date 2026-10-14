/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect

/-!
# The front-to-high-dialect edge: a verified `Com[thir] → Com[catCrypt]` lowering

The two verified hax/THIR ingestion lanes both terminate at `Com jasminDialect`
(`ThirToComFront.thirToJasmin`, `ThirDialect.lowerThir`), bypassing the high
crypto dialect stack (`catCryptDialect` / `fieldDialect` / `modArithDialect`).
`ThirFrontProbe.lean` proved the rank-1 single-op witness (`thBin .add ↦ bvAdd`,
one binding). **This file is the pass**: a structural, denotation-preserving
lowering `lowerThirToCrypto : Com thirDialect Γ t → Option (Com catCryptDialect
(mapCtx Γ) (mapTy t))` over the tractable `ThirOp` arms, lifted to whole
programs by structural induction.

## The type map and value transport

`thirDialect.Ty = JasminTy`, `catCryptDialect.Ty = CryptoTy`. The map
`mapTy (.reg w) = .sword w` carries the **identity** value transport: both
`(.reg w).denote` and `(.sword w).denote` are `BitVec w`. Unlike the thir→jasmin
lowering (which shares `Ty`), the contexts here differ as types, so variables
are transported structurally (`vC`/`argsC`), and the per-op square is the
identity transport on `BitVec w` (so each covered square is `rfl`/`simp`).

## Exactly which `ThirOp` arms are covered

**RANK-1 (1:1, denotations agree on `BitVec w`, square is `rfl`):**

| `ThirOp`                          | `CatCryptOp` image            |
|-----------------------------------|-------------------------------|
| `thBin .add/.sub/.mul w`          | `bvAdd/bvSub/bvMul w`         |
| `thBin .and/.or/.xor w`           | `bvAnd/bvOr/bvXor w`          |
| `thShrImm w n`                    | `bvShiftR w n`                |
| `thShlImm w n`                    | `bvShiftL w n`                |
| `thConst w n`                     | `bvConst w (ofNat w n)`       |
| `thExtCall name argTys (.reg w)`  | `extCall name [] (.sword w)` (opaque-default leaf) |
| `thEqLit w k`                     | `extCall (eqLitLeafName w k) [] (.sword 1)` (opaque-equality leaf) |

For the covered `thBin` arms `JasminBinOp.apply` is `a+b / a-b / a*b / a&&&b /
a|||b / a^^^b`, matching `catCryptDenote` for `bvAdd/…/bvXor` definitionally.
`thShrImm`'s `a >>> n` is `BitVec.ushiftRight a n = bvShiftR`'s denotation;
`thShlImm`'s `a <<< n = bvShiftL`'s. `thConst w n = ofNat w n = bvConst`'s
stored value. `thExtCall` to a `.reg w` result and `thEqLit` both lower to a
*nullary* opaque `extCall` leaf of the SAME callee name: the THIR leaf
(`jasminExtSem … (.reg w)` / `jasminExtSem (eqLitLeafName …) (.reg 1)`) falls
through to `JasminTy.default = 0`, and `catCryptDenote.extCall` denotes
`CryptoTy.default (.sword w) = 0`, so both sides are `0` and the square is `rfl`
(the args are semantically dead on both sides). Only a **register** return is
covered; a `stackArr`-return `thExtCall` would hit a non-default `jasminExtSem`
pattern and is residual.

**RANK-2 (op-expansion to a multi-binding catCrypt fragment, soundness via the
generic `Com.denote_rename`):**

| `ThirOp`                          | catCrypt expansion            |
|-----------------------------------|-------------------------------|
| `thBinLit op w n` (op ∈ add/sub/mul/and/or/xor) | `bvConst w (ofNat w n); bv⟨op⟩ w a lit` |
| `thRor w n`                       | `bvShiftR w (n%w); bvShiftL w (w - n%w); bvOr w` |

`thBinLit` materializes the immediate as a `bvConst` binding, then applies the
matching catCrypt binop to `(a, lit)`, weakening the already-lowered body
through the inserted const binding (mirroring `ThirDialect.lowerThir`'s
`regConst; regArith` pair). `thRor` realizes `BitVec.rotateRight a n =
a >>> (n%w) ||| a <<< (w - n%w)` (`BitVec.rotateRight_def`,
`BitVec.ushiftRight_eq`) as a `bvShiftR; bvShiftL; bvOr` triple, dropping the
two intermediate shift results from the body's view via the pullback
`pullV_lift_weaken2`. Both arms are proved through the dialect-generic de-Bruijn
substitution law `Generic.Com.denote_rename` (reproved here once, parametric in
the dialect). For `thBinLit`, only the six binops that have a catCrypt image are
covered; `shl/shr/andn` immediates are residual.

**RANK-3 / residual (NO denotation-matching `CatCryptOp` image — `none`):**

* `thSarImm w n` — `catCryptDialect`'s only right-shift is `bvShiftR` (logical
  `>>>`); there is no arithmetic / sign-extending shift op. A faithful image
  would need a sign-mask expansion over a `bvShiftR`-of-sign + select/or, which
  has no clean `BitVec.sshiftRight` identity in the existing op set — left as
  `none` (a new `bvShiftRA` op would be required).
* `thSelect` — `ite`'s condition is `.bit` (`Bool`); the thir condition is
  `.reg 1` (`BitVec 1`). The shape does not transfer without a `BitVec 1 → Bool`
  reinterpretation, so it is residual (not `rfl`).
* `thMulHi`, `thAddCarryLo`, `thAddCarryHi` — `catCryptDialect` has no
  high-multiply / single-word carry op (`bvAdd64`/`bvAdc` return *pairs* with a
  different shape — a multi-output op, not a `.sword w` result; routing the
  pair's lo/hi components would need a `.pair`-projecting follow-on op that the
  single-`ret` `lowerVarStepC` step has no slot for), so no 1:1 image; left
  residual rather than fabricated.
* `thVpack` — no packed-512-lane SIMD op in `catCryptDialect`.
* `thBin .shl/.shr/.andn`, `thBinLit .shl/.shr/.andn`, `thCast` — `shl`/`shr`
  take a *runtime* shift amount (no `bvShift*` image, which is immediate-only);
  `andn`/`thCast` have no image.

The lowering returns `none` whenever any binding uses a residual op; the
soundness theorem `lowerThirToCrypto_denote` is for the `some` case (a program
all of whose bindings are covered). **All goals closed.**
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ThirToCryptoDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp jasminDialect JasminTy)
open CatCrypt.Crypto.SecureCompilation.VIR.ThirDialect (ThirOp thirDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (CatCryptOp catCryptDialect)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)

/-! ## 1. The type/context map (identity value transport on `BitVec w`) -/

/-- The type map `thirDialect.Ty → catCryptDialect.Ty`: a `w`-bit register
    becomes a `w`-bit machine word. Total over `JasminTy`; the non-`.reg`
    constructors land on `.sword 0` (they are only reached by residual ops, which
    the lowering rejects). On the `.reg w` fragment the induced value transport is
    the identity (`⟦.reg w⟧ = ⟦.sword w⟧ = BitVec w`). -/
@[implicit_reducible]
def mapTy : JasminTy → CryptoTy
  | .reg w => .sword w
  | _ => .sword 0

/-- The context map: pointwise `mapTy`. -/
@[implicit_reducible]
def mapCtx (Γ : Ctxt thirDialect) : Ctxt catCryptDialect := Γ.map mapTy

/-- `mapCtx` of a `cons` is the `cons` of the mapped head onto the mapped tail
    (definitional `List.map_cons`). The structural compatibility that lets the
    de-Bruijn binding thread through the lowering. -/
theorem mapCtx_cons (t : JasminTy) (Γ : Ctxt thirDialect) :
    mapCtx (t :: Γ) = mapTy t :: mapCtx Γ := rfl

/-! ## 2. Variable / args transport across the type map

`Ctxt.Var Γ t` (thir) and `Ctxt.Var (mapCtx Γ) (mapTy t)` (catCrypt) are
different types because `mapTy` reshapes the context. We transport a variable
structurally; `mapCtx (t :: Γ) = mapTy t :: mapCtx Γ` (`mapCtx_cons`) makes the
`here`/`there` skeleton line up. -/

/-- Transport a THIR-dialect variable to the catCrypt dialect along `mapTy`. -/
def vC : {Γ : Ctxt thirDialect} → {t : JasminTy} →
    @Ctxt.Var thirDialect Γ t → @Ctxt.Var catCryptDialect (mapCtx Γ) (mapTy t)
  | _ :: _, _, .here => .here
  | _ :: _, _, .there v => .there (vC v)

/-- Transport an `HVector` of THIR variables to the catCrypt dialect. The result
    is indexed (over the **source** type list `tys`) by `fun ty => Var (mapCtx Γ)
    (mapTy ty)`. -/
def argsC : {Γ : Ctxt thirDialect} → {tys : List JasminTy} →
    HVector (fun ty => @Ctxt.Var thirDialect Γ ty) tys →
    HVector (fun ty => @Ctxt.Var catCryptDialect (mapCtx Γ) (mapTy ty)) tys
  | _, [], .nil => .nil
  | _, _ :: _, .cons v rest => .cons (vC v) (argsC rest)

/-! ## 3. The value transport and valuation transport (identity on the register
fragment)

`mapTy` is non-identity as a *type-tag* map, but `⟦.reg w⟧ = ⟦.sword w⟧ = BitVec
w`, so the induced value transport `transTy : ⟦t⟧ → ⟦mapTy t⟧` is the identity on
registers (and an unreached stub elsewhere). A valuation transport `mapVal`
retypes a source environment pointwise; on register contexts it is the identity
on the underlying `HVector`. -/

/-- The per-type value transport `⟦t⟧ → ⟦mapTy t⟧`. On `.reg w` it is the
    identity `BitVec w → BitVec w` (`⟦mapTy (.reg w)⟧ = BitVec w`); the non-`.reg`
    stub (`fun _ => 0`) is never reached by the accepted (register) ops. -/
def transTy : {t : JasminTy} → ⟦t⟧ → ⟦mapTy t⟧
  | .reg _, x => x
  | .stackArr _ _, _ => (0 : BitVec 0)
  | .inlineInt, _ => (0 : BitVec 0)
  | .bool, _ => (0 : BitVec 0)

/-- The valuation transport `Valuation Γ → Valuation (mapCtx Γ)`: pointwise
    `transTy`. On a register context it carries the underlying `HVector`
    unchanged. -/
def mapVal : {Γ : Ctxt thirDialect} → Ctxt.Valuation Γ →
    Ctxt.Valuation (mapCtx Γ)
  | [], .nil => .nil
  | _ :: _, .cons x V => .cons (transTy x) (mapVal V)

/-- **Variable-transport coherence.** Looking up the transported variable in the
    transported valuation equals transporting the source lookup. Structural
    induction on the variable; each step is definitional. -/
theorem vC_lookup : {Γ : Ctxt thirDialect} → {t : JasminTy} →
    (v : @Ctxt.Var thirDialect Γ t) → (V : Ctxt.Valuation Γ) →
    (vC v).lookup (mapVal V) = transTy (v.lookup V)
  | _ :: _, _, .here, .cons _ _ => rfl
  | _ :: _, _, .there v, .cons _ V => vC_lookup v V

/-- The register specialisation of `vC_lookup`: on `.reg w` the value transport
    `transTy` is the identity, so the transported lookup is the source lookup. -/
@[simp] theorem vC_lookup_reg {w : Nat} {Γ : Ctxt thirDialect}
    (v : @Ctxt.Var thirDialect Γ (.reg w)) (V : Ctxt.Valuation Γ) :
    (vC v).lookup (mapVal V) = v.lookup V := vC_lookup v V

/-- `lookupArgs` on a `cons` reduces (the def's `cons` equation, as a `simp`
    lemma so it fires inside the binop denotations). -/
@[simp] theorem lookupArgs_cons {d : Dialect} [TyDenote d.Ty] {Γ : Ctxt d}
    {t : d.Ty} {tys : List d.Ty} (v : @Ctxt.Var d Γ t)
    (rest : HVector (fun ty => @Ctxt.Var d Γ ty) tys)
    (V : Ctxt.Valuation Γ) :
    Expr.lookupArgs (.cons v rest) V = .cons (v.lookup V) (Expr.lookupArgs rest V) :=
  rfl

/-- The head of a looked-up `cons` arg list (catCrypt side) is the head var's
    lookup. A `@[simp]` `rfl` that fires on the compiled `HVector.head` /
    `match` projection appearing in the binop denotations. -/
@[simp] theorem argHead {Γ : Ctxt catCryptDialect} {t : CryptoTy} {tys : List CryptoTy}
    (v : @Ctxt.Var catCryptDialect Γ t)
    (rest : HVector (fun ty => @Ctxt.Var catCryptDialect Γ ty) tys)
    (V : Ctxt.Valuation Γ) :
    (Expr.lookupArgs (.cons v rest) V).head = v.lookup V := rfl

/-- The second element of a looked-up `cons cons` arg list (catCrypt side). -/
@[simp] theorem argSnd {Γ : Ctxt catCryptDialect} {t t' : CryptoTy} {tys : List CryptoTy}
    (v : @Ctxt.Var catCryptDialect Γ t)
    (w : @Ctxt.Var catCryptDialect Γ t')
    (rest : HVector (fun ty => @Ctxt.Var catCryptDialect Γ ty) tys)
    (V : Ctxt.Valuation Γ) :
    (Expr.lookupArgs (.cons v (.cons w rest)) V).tail.head = w.lookup V := rfl

/-- The thir-side head of a looked-up `cons` arg list. -/
@[simp] theorem argHeadT {Γ : Ctxt thirDialect} {t : JasminTy} {tys : List JasminTy}
    (v : @Ctxt.Var thirDialect Γ t)
    (rest : HVector (fun ty => @Ctxt.Var thirDialect Γ ty) tys)
    (V : Ctxt.Valuation Γ) :
    (Expr.lookupArgs (.cons v rest) V).head = v.lookup V := rfl

/-- The thir-side second element of a looked-up `cons cons` arg list. -/
@[simp] theorem argSndT {Γ : Ctxt thirDialect} {t t' : JasminTy} {tys : List JasminTy}
    (v : @Ctxt.Var thirDialect Γ t)
    (w : @Ctxt.Var thirDialect Γ t')
    (rest : HVector (fun ty => @Ctxt.Var thirDialect Γ ty) tys)
    (V : Ctxt.Valuation Γ) :
    (Expr.lookupArgs (.cons v (.cons w rest)) V).tail.head = w.lookup V := rfl

/-! ## 3b. The de-Bruijn substitution law for an arbitrary dialect

The expanding arms (`thBinLit`, `thRor`) insert one or two catCrypt bindings
*before* the already-lowered body, so the body must be weakened through the
inserted bindings. Soundness then needs `Com.denote_rename`: denoting a renamed
`Com` against `V` equals denoting the original against the **pullback** of `V`.
The jasmin instance lives in `ThirDialect`; we reprove the chain here once,
dialect-generically (it uses no dialect-specific fact), so it serves the
catCrypt target. -/

namespace Generic

set_option linter.unusedSectionVars false

variable {d : Dialect} [DialectSignature d] [TyDenote d.Ty] [DialectDenote d]

/-- Pullback of a `Valuation Γ'` along a context homomorphism `h : Γ → Γ'`. -/
def pullV : {Γ : Ctxt d} → {Γ' : Ctxt d} →
    Ctxt.Hom Γ Γ' → Ctxt.Valuation Γ' → Ctxt.Valuation Γ
  | [], _, _, _ => HVector.nil
  | _ :: _, _, h, V =>
      HVector.cons ((h Ctxt.Var.here).lookup V)
        (pullV (fun v => h (.there v)) V)

/-- Looking up a renamed variable in `V` equals looking up the original
    variable in the pullback of `V`. -/
theorem Var.lookup_rename {Γ Γ' : Ctxt d}
    (h : Ctxt.Hom Γ Γ') {t : d.Ty} (v : Ctxt.Var Γ t)
    (V : Ctxt.Valuation Γ') :
    (h v).lookup V = v.lookup (pullV h V) := by
  induction v with
  | here => rfl
  | @there Γ₀ t s w ih =>
      simp only [pullV]
      exact ih (fun v => h (.there v))

/-- Renaming arguments and looking them up against `V` equals looking up the
    original arguments against the pulled-back valuation. -/
theorem lookupArgs_renameVars {Γ Γ' : Ctxt d} (h : Ctxt.Hom Γ Γ') :
    {tys : List d.Ty} →
    (args : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    (V : Ctxt.Valuation Γ') →
    Expr.lookupArgs (HVector.renameVars h args) V
      = Expr.lookupArgs args (pullV h V)
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, V => by
      show HVector.cons _ _ = HVector.cons _ _
      congr 1
      · exact Var.lookup_rename h v V
      · exact lookupArgs_renameVars h rest V

/-- Renaming an `Expr` and denoting it against `V` equals denoting the original
    against the pulled-back valuation. -/
theorem Expr.denote_rename {Γ Γ' : Ctxt d} (h : Ctxt.Hom Γ Γ')
    {t : d.Ty} (e : Expr d Γ t) (V : Ctxt.Valuation Γ') :
    (e.rename h).denote V = e.denote (pullV h V) := by
  cases e with
  | mk op retTy_eq args =>
      simp only [Expr.rename, Expr.denote]
      rw [lookupArgs_renameVars h args V]

/-- `pullV` through a `.there`-shifted hom drops the freshly-added head binding. -/
theorem pullV_there {Γ Δ : Ctxt d} {s : d.Ty}
    (g : Ctxt.Hom Γ Δ) (x : ⟦s⟧) (W : Ctxt.Valuation Δ) :
    pullV (fun {_} v => (g v).there) (HVector.cons x W) = pullV g W := by
  induction Γ with
  | nil => rfl
  | cons a Γ ih =>
      simp only [pullV]
      congr 1
      exact ih (fun {_} v => g (.there v))

/-- Pulling back along the identity hom is the identity on valuations. -/
theorem pullV_id {Γ : Ctxt d} (V : Ctxt.Valuation Γ) :
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

/-- Pulling back along the double weakening drops both fresh head bindings. -/
@[simp] theorem pullV_weaken2 {Γ : Ctxt d} {s₁ s₂ : d.Ty}
    (a : ⟦s₁⟧) (b : ⟦s₂⟧) (W : Ctxt.Valuation Γ) :
    pullV (fun {_} v => Ctxt.Var.there (Ctxt.Var.there v))
        (HVector.cons a (HVector.cons b W)) = W := by
  rw [pullV_there (fun {_} v => Ctxt.Var.there v) a (HVector.cons b W),
    pullV_there (fun {_} v => v) b W, pullV_id]

/-- The exact pullback for a single-binding expansion: pulling back along
    `lift (weakenOne)` against `a :: b :: W` keeps `a` and `W`, dropping the
    inserted (middle) binding `b`. -/
theorem pullV_lift_weakenOne {Γ : Ctxt d} {s s' : d.Ty}
    (a : ⟦s'⟧) (b : ⟦s⟧) (W : Ctxt.Valuation Γ) :
    pullV (Ctxt.Hom.lift (Ctxt.Hom.weakenOne Γ s))
        (HVector.cons a (HVector.cons b W))
      = HVector.cons a W := by
  show HVector.cons (a : ⟦s'⟧) (pullV (fun {_} v =>
      Ctxt.Var.there (Ctxt.Var.there v)) (HVector.cons a (HVector.cons b W)))
    = HVector.cons a W
  rw [pullV_weaken2]

/-- Pulling back along the triple weakening drops all three fresh head bindings. -/
@[simp] theorem pullV_weaken3 {Γ : Ctxt d} {s₁ s₂ s₃ : d.Ty}
    (a : ⟦s₁⟧) (b : ⟦s₂⟧) (c : ⟦s₃⟧) (W : Ctxt.Valuation Γ) :
    pullV (fun {_} v => Ctxt.Var.there (Ctxt.Var.there (Ctxt.Var.there v)))
        (HVector.cons a (HVector.cons b (HVector.cons c W))) = W := by
  rw [pullV_there (fun {_} v => Ctxt.Var.there (Ctxt.Var.there v)) a
      (HVector.cons b (HVector.cons c W)), pullV_weaken2]

/-- The exact pullback for a two-binding expansion whose result binds at the
    head: pulling back along `lift (weakenOne ∘ weakenOne)` against
    `a :: b :: c :: W` keeps the head `a` and the deep tail `W`, dropping the two
    inserted (middle) bindings `b`, `c`. Used by the `thRor` expansion (the
    `bvShiftR; bvShiftL` results sit below the `bvOr` result). -/
theorem pullV_lift_weaken2 {Γ : Ctxt d} {s s' s'' : d.Ty}
    (a : ⟦s''⟧) (b : ⟦s⟧) (c : ⟦s'⟧) (W : Ctxt.Valuation Γ) :
    pullV (Ctxt.Hom.lift
        ((Ctxt.Hom.weakenOne (s' :: Γ) s).comp (Ctxt.Hom.weakenOne Γ s')))
        (HVector.cons a (HVector.cons b (HVector.cons c W)))
      = HVector.cons a W := by
  show HVector.cons (a : ⟦s''⟧) (pullV (fun {_} v =>
      Ctxt.Var.there (Ctxt.Var.there (Ctxt.Var.there v)))
      (HVector.cons a (HVector.cons b (HVector.cons c W))))
    = HVector.cons a W
  rw [pullV_weaken3]

/-- Renaming a `Com` and denoting it against `V` equals denoting the original
    against the pulled-back valuation. The whole-program analogue of
    `Expr.denote_rename`. -/
theorem Com.denote_rename {Γ Γ' : Ctxt d} {t : d.Ty}
    (h : Ctxt.Hom Γ Γ') (c : Com d Γ t) (V : Ctxt.Valuation Γ') :
    (Com.rename h c).denote V = c.denote (pullV h V) := by
  induction c generalizing Γ' with
  | ret v =>
      simp only [Com.rename, Com.denote]
      exact Var.lookup_rename h v V
  | var e body ih =>
      simp only [Com.rename, Com.denote]
      rw [ih h.lift (V.extend ((e.rename h).denote V))]
      rw [Expr.denote_rename h e V]
      congr 1
      show HVector.cons (e.denote (pullV h V)) (pullV (fun {_} v => (h v).there)
          (HVector.cons (e.denote (pullV h V)) V))
        = HVector.cons (e.denote (pullV h V)) (pullV h V)
      rw [pullV_there h (e.denote (pullV h V)) V]

end Generic

/-! ## 4. The per-binding lowering step (`Option`-valued, one op ↦ one block)

`lowerVarStepC op args bodyC` lowers one THIR binding for `op` over an
already-lowered catCrypt body, returning `none` on a residual op. The covered
1:1 arms rebind with the matching `CatCryptOp` (the args HVector built directly
from the two/one/zero `vC`-transported variables); `thConst`/`thExtCall` are the
nullary/extern arms. The expanding `thBinLit` and shape-changing ops are not in
this step (see §5/§6). -/

/-- The `thBinLit op w n` op-expansion: materialize the immediate as a
    `bvConst w (ofNat w n)` binding, then apply the binop `cop` (the catCrypt
    image of `op`) to `(a, lit)`, weakening the already-lowered body through the
    inserted const binding via `Com.rename`. Mirrors `ThirDialect.lowerVarStep`'s
    `thBinLit` arm (which expands to a jasmin `regConst; regArith` pair). Used
    only for the six covered binops (`add/sub/mul/and/or/xor`), where
    `cop`'s denotation is `a ⟨op⟩ lit`.

    `args.head` is the single source register (`thBinLit`'s `sig = [.reg w]`);
    the body binds `mapTy (.reg w) = .sword w`. -/
def binLitExpand {Γ : Ctxt thirDialect} {s : JasminTy}
    (cop : CatCryptOp) (w n : Nat)
    (args : HVector (fun ty => @Ctxt.Var thirDialect Γ ty) [JasminTy.reg w])
    (bodyC : Com catCryptDialect (.sword w :: mapCtx Γ) (mapTy s))
    (hsig : DialectSignature.sig (d := catCryptDialect) cop = [CryptoTy.sword w, .sword w] := by rfl)
    (hret : DialectSignature.ret (d := catCryptDialect) cop = CryptoTy.sword w := by rfl) :
    Com catCryptDialect (mapCtx Γ) (mapTy s) :=
  let a : @Ctxt.Var catCryptDialect (mapCtx Γ) (.sword w) := vC args.head
  let eLit : Expr catCryptDialect (mapCtx Γ) (.sword w) :=
    Expr.mk (.bvConst w (BitVec.ofNat w n)) rfl .nil
  let eOut : Expr catCryptDialect (.sword w :: mapCtx Γ) (.sword w) :=
    Expr.mk cop hret (hsig ▸ (.cons (.there a) (.cons .here .nil)))
  let bodyW : Com catCryptDialect (.sword w :: .sword w :: mapCtx Γ) (mapTy s) :=
    Com.rename (Ctxt.Hom.lift (Ctxt.Hom.weakenOne (mapCtx Γ) (.sword w))) bodyC
  Com.var eLit (Com.var eOut bodyW)

/-- Lower one THIR binding into a catCrypt `Com`, over an already-lowered body.
    `none` on any residual op. -/
def lowerVarStepC {Γ : Ctxt thirDialect} {s : JasminTy}
    (op : thirDialect.Op)
    (args : HVector (fun ty => @Ctxt.Var thirDialect Γ ty)
      (DialectSignature.sig (d := thirDialect) op))
    (bodyC : Com catCryptDialect
      (mapTy (DialectSignature.ret (d := thirDialect) op) :: mapCtx Γ) (mapTy s)) :
    Option (Com catCryptDialect (mapCtx Γ) (mapTy s)) :=
  match op, args, bodyC with
  | .thBin .add w, args, bodyC =>
      some (Com.var (Expr.mk (.bvAdd w) rfl
        (.cons (vC args.head) (.cons (vC args.tail.head) .nil))) bodyC)
  | .thBin .sub w, args, bodyC =>
      some (Com.var (Expr.mk (.bvSub w) rfl
        (.cons (vC args.head) (.cons (vC args.tail.head) .nil))) bodyC)
  | .thBin .mul w, args, bodyC =>
      some (Com.var (Expr.mk (.bvMul w) rfl
        (.cons (vC args.head) (.cons (vC args.tail.head) .nil))) bodyC)
  | .thBin .and w, args, bodyC =>
      some (Com.var (Expr.mk (.bvAnd w) rfl
        (.cons (vC args.head) (.cons (vC args.tail.head) .nil))) bodyC)
  | .thBin .or w, args, bodyC =>
      some (Com.var (Expr.mk (.bvOr w) rfl
        (.cons (vC args.head) (.cons (vC args.tail.head) .nil))) bodyC)
  | .thBin .xor w, args, bodyC =>
      some (Com.var (Expr.mk (.bvXor w) rfl
        (.cons (vC args.head) (.cons (vC args.tail.head) .nil))) bodyC)
  | .thShrImm w n, args, bodyC =>
      some (Com.var (Expr.mk (.bvShiftR w n) rfl (.cons (vC args.head) .nil)) bodyC)
  | .thShlImm w n, args, bodyC =>
      some (Com.var (Expr.mk (.bvShiftL w n) rfl (.cons (vC args.head) .nil)) bodyC)
  | .thConst w n, _, bodyC =>
      some (Com.var (Expr.mk (.bvConst w (BitVec.ofNat w n)) rfl .nil) bodyC)
  | .thExtCall name _ (.reg w), _, bodyC =>
      -- The leaf is opaque: `jasminExtSem name _ (.reg w)` falls through to
      -- `JasminTy.default (.reg w) = 0` (it has no special `.reg`-return
      -- pattern), and catCrypt's `extCall` denotes `CryptoTy.default (.sword w)
      -- = 0`. The args never affect either denotation, so we lower to the
      -- nullary opaque leaf `extCall name [] (.sword w)` of the SAME name: both
      -- denote `0 : BitVec w`. A non-`.reg` return is residual (a `stackArr`
      -- return could hit a non-default `jasminExtSem` pattern).
      some (Com.var (Expr.mk (.extCall name [] (.sword w)) rfl .nil) bodyC)
  | .thEqLit w k, _, bodyC =>
      -- `thEqLit` denotes the opaque equality leaf
      -- `jasminExtSem (eqLitLeafName w k) [.reg w] (.reg 1) = JasminTy.default
      -- (.reg 1) = 0`. We lower to the nullary opaque leaf `extCall
      -- (eqLitLeafName w k) [] (.sword 1)` of the SAME name: both denote
      -- `0 : BitVec 1`. (The KAT-discharged *value* obligation is identical on
      -- both sides — the leaf semantics — exactly as in the thir→jasmin path.)
      some (Com.var
        (Expr.mk (.extCall (ThirDialect.eqLitLeafName w k) [] (.sword 1)) rfl .nil)
        bodyC)
  | .thBinLit .add w n, args, bodyC => some (binLitExpand (.bvAdd w) w n args bodyC)
  | .thBinLit .sub w n, args, bodyC => some (binLitExpand (.bvSub w) w n args bodyC)
  | .thBinLit .mul w n, args, bodyC => some (binLitExpand (.bvMul w) w n args bodyC)
  | .thBinLit .and w n, args, bodyC => some (binLitExpand (.bvAnd w) w n args bodyC)
  | .thBinLit .or  w n, args, bodyC => some (binLitExpand (.bvOr  w) w n args bodyC)
  | .thBinLit .xor w n, args, bodyC => some (binLitExpand (.bvXor w) w n args bodyC)
  | .thRor w n, args, bodyC =>
      -- `a.rotateRight n = (a >>> (n % w)) ||| (a <<< (w - n % w))`
      -- (`BitVec.rotateRight_def`). Expand to the catCrypt triple
      -- `bvShiftR w (n % w); bvShiftL w (w - n % w); bvOr w`, weakening the body
      -- through the two inserted bindings.
      let a : @Ctxt.Var catCryptDialect (mapCtx Γ) (.sword w) := vC args.head
      let eShr : Expr catCryptDialect (mapCtx Γ) (.sword w) :=
        Expr.mk (.bvShiftR w (n % w)) rfl (.cons a .nil)
      let eShl : Expr catCryptDialect (.sword w :: mapCtx Γ) (.sword w) :=
        Expr.mk (.bvShiftL w (w - n % w)) rfl (.cons (.there a) .nil)
      let eOr : Expr catCryptDialect (.sword w :: .sword w :: mapCtx Γ) (.sword w) :=
        Expr.mk (.bvOr w) rfl (.cons (.there .here) (.cons .here .nil))
      -- The body's single binding (the rotated value) maps to the `bvOr`
      -- result at the head; the two intermediate shift results are inserted
      -- *below* it, so weaken the tail by two (`weakenOne ∘ weakenOne`) and keep
      -- the head (`lift`).
      let bodyW : Com catCryptDialect (.sword w :: .sword w :: .sword w :: mapCtx Γ)
          (mapTy s) :=
        Com.rename (Ctxt.Hom.lift
          ((Ctxt.Hom.weakenOne (CryptoTy.sword w :: mapCtx Γ) (CryptoTy.sword w)).comp
            (Ctxt.Hom.weakenOne (mapCtx Γ) (CryptoTy.sword w)))) bodyC
      some (Com.var eShr (Com.var eShl (Com.var eOr bodyW)))
  | _, _, _ => none

/-! ## 5. The whole-program lowering (`Option`-valued, structural) -/

/-- Lower a `Com thirDialect` to a `Com catCryptDialect` over the type map,
    structurally on the `.ret`/`.var` skeleton. `.ret` transports the returned
    variable; `.var` recursively lowers the body, then defers the op step to
    `lowerVarStepC`. Returns `none` as soon as any binding uses a residual op
    (the `Option`-bind threads the failure). -/
def lowerThirToCrypto : {Γ : Ctxt thirDialect} → {t : JasminTy} →
    Com thirDialect Γ t → Option (Com catCryptDialect (mapCtx Γ) (mapTy t))
  | _, _, .ret v => some (.ret (vC v))
  | _, _, .var (Expr.mk op hret args) body =>
      match lowerThirToCrypto body with
      | none => none
      | some bodyC => lowerVarStepC op args (hret ▸ bodyC)

/-! ## 6. Denotation preservation -/

/-- The shift-or form of a rotate right by `n % w` is unchanged when both shift
    counts are masked by `shiftMask w`. -/
theorem rotr_shiftOr_shiftMask {w : Nat} (z : BitVec w) (n : Nat) :
    z >>> shiftMask w (n % w) ||| z <<< shiftMask w (w - n % w)
      = z >>> (n % w) ||| z <<< (w - n % w) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [BitVec.of_length_zero]
  rw [shiftMask_of_lt (Nat.mod_lt n hw)]
  rcases Nat.eq_zero_or_pos (n % w) with h0 | hpos
  · have hww : shiftMask w w = 0 ∨ shiftMask w w = w := by
      unfold shiftMask
      split <;> (try split) <;> (try split) <;> (try split) <;> omega
    rw [h0, Nat.sub_zero]
    rcases hww with h | h <;> simp [h]
  · rw [shiftMask_of_lt (by omega : w - n % w < w)]

/-- **Per-binding soundness.** Whenever `lowerVarStepC op args bodyC` succeeds
    with `comC`, the lowered block denotes (under the transported valuation
    `mapVal V`) to `bodyC` evaluated with its first binding set to the *transport
    of the THIR op's value* on the source valuation. The rank-1 arms reduce by
    `vC_lookup` (the variable square) and `transTy` being the identity on the
    register fragment (the six binops, the two shifts, the const, the two opaque
    leaves match definitionally). The expanding `thBinLit`/`thRor` arms reduce
    their inserted bindings through `Generic.Com.denote_rename` + the matching
    pullback (`pullV_lift_weakenOne` / `pullV_lift_weaken2`) and the binop /
    `BitVec.rotateRight_def` identity. -/
theorem lowerVarStepC_denote {Γ : Ctxt thirDialect} {s : JasminTy}
    (op : thirDialect.Op)
    (args : HVector (fun ty => @Ctxt.Var thirDialect Γ ty)
      (DialectSignature.sig (d := thirDialect) op))
    (bodyC : Com catCryptDialect
      (mapTy (DialectSignature.ret (d := thirDialect) op) :: mapCtx Γ) (mapTy s))
    (comC : Com catCryptDialect (mapCtx Γ) (mapTy s))
    (h : lowerVarStepC op args bodyC = some comC)
    (V : Ctxt.Valuation Γ) :
    comC.denote (mapVal V)
      = bodyC.denote (Ctxt.Valuation.extend (mapVal V)
          (transTy (DialectDenote.denote (self := ThirDialect.thirDenote) op
            (Expr.lookupArgs args V)))) := by
  rcases op with bop|_|_|_|_|_|_|_|_|_|_|_|_|rt|_
  case thBin =>
    obtain ⟨a, b, r, rfl⟩ : ∃ a b r, args = .cons a (.cons b r) := by
      cases args with | cons a t => cases t with | cons b r => exact ⟨a, b, r, rfl⟩
    rcases bop with _|_|_|_|_|_|_|_|_ <;>
      first
        | (simp only [lowerVarStepC, Option.some.injEq] at h; subst h
           simp only [Com.denote, Expr.denote, DialectDenote.denote]
           congr 2 <;>
             ((repeat rw [lookupArgs_cons])
              simp only [HVector.head, HVector.tail, JasminBinOp.apply]
              congr 1 <;> exact vC_lookup_reg _ _))
        | exact absurd h (by simp [lowerVarStepC])
  case thShrImm w n =>
    obtain ⟨a, r, rfl⟩ : ∃ a r, args = .cons a r := by
      cases args with | cons a r => exact ⟨a, r, rfl⟩
    simp only [lowerVarStepC, Option.some.injEq] at h; subst h
    simp only [Com.denote, Expr.denote, DialectDenote.denote]
    congr 2 <;>
      ((repeat rw [lookupArgs_cons])
       simp only [HVector.head]
       congr 1 <;> exact vC_lookup_reg _ _)
  case thShlImm w n =>
    obtain ⟨a, r, rfl⟩ : ∃ a r, args = .cons a r := by
      cases args with | cons a r => exact ⟨a, r, rfl⟩
    simp only [lowerVarStepC, Option.some.injEq] at h; subst h
    simp only [Com.denote, Expr.denote, DialectDenote.denote]
    congr 2 <;>
      ((repeat rw [lookupArgs_cons])
       simp only [HVector.head]
       congr 1 <;> exact vC_lookup_reg _ _)
  case thConst w n =>
    simp only [lowerVarStepC, Option.some.injEq] at h; subst h; rfl
  case thExtCall name argTys rt =>
    rcases rt with w|_|_|_ <;>
      first
        | (simp only [lowerVarStepC, Option.some.injEq] at h; subst h;
           simp only [Com.denote, Expr.denote, DialectDenote.denote, transTy,
             CryptoTy.default, JasminDialect.jasminExtSem, JasminTy.default]; rfl)
        | exact absurd h (by simp [lowerVarStepC])
  case thEqLit w k =>
    simp only [lowerVarStepC, Option.some.injEq] at h; subst h
    simp only [Com.denote, Expr.denote, DialectDenote.denote, transTy,
      CryptoTy.default, JasminDialect.jasminExtSem, JasminTy.default]; rfl
  case thBinLit bop w n =>
    obtain ⟨a, r, rfl⟩ : ∃ a r, args = .cons a r := by
      cases args with | cons a r => exact ⟨a, r, rfl⟩
    obtain ⟨bodyC, rfl⟩ : ∃ bodyC' : Com catCryptDialect (CryptoTy.sword w :: mapCtx Γ) (mapTy s),
        bodyC' = bodyC := ⟨bodyC, rfl⟩
    rcases bop with _|_|_|_|_|_|_|_|_ <;>
      first
        | (simp only [lowerVarStepC, binLitExpand, Option.some.injEq] at h; subst h
           simp only [Com.denote, Expr.denote, DialectDenote.denote]
           rw [Generic.Com.denote_rename]
           simp only [Ctxt.Valuation.extend]
           rw [Generic.pullV_lift_weakenOne]
           congr 2 <;>
             ((repeat rw [lookupArgs_cons])
              simp only [HVector.head, HVector.tail, JasminBinOp.apply, transTy]
              congr 1 <;> exact vC_lookup_reg _ _))
        | exact absurd h (by simp [lowerVarStepC])
  case thRor w n =>
    obtain ⟨a, r, rfl⟩ : ∃ a r, args = .cons a r := by
      cases args with | cons a r => exact ⟨a, r, rfl⟩
    obtain ⟨bodyC, rfl⟩ : ∃ bodyC' : Com catCryptDialect (CryptoTy.sword w :: mapCtx Γ) (mapTy s),
        bodyC' = bodyC := ⟨bodyC, rfl⟩
    simp only [lowerVarStepC, Option.some.injEq] at h; subst h
    simp only [Com.denote, Expr.denote, DialectDenote.denote]
    rw [Generic.Com.denote_rename]
    simp only [Ctxt.Valuation.extend]
    -- The two inserted shift bindings (`bvShiftR`, `bvShiftL`) are dropped by the
    -- `lift (weakenOne ∘ weakenOne)` pullback (`pullV_lift_weaken2`); the `bvOr`
    -- of the two shift results is the source `rotateRight` value
    -- (`BitVec.rotateRight_def`, `BitVec.ushiftRight_eq`), with the register
    -- lookup transported by `vC_lookup_reg`.
    rw [Generic.pullV_lift_weaken2, BitVec.rotateRight_def, BitVec.ushiftRight_eq]
    generalize hz : (Expr.lookupArgs (HVector.cons a r) V).head = z
    rw [← rotr_shiftOr_shiftMask z n]
    have hg : (Expr.lookupArgs (HVector.cons (vC ((HVector.cons a r).head)) HVector.nil)
        (mapVal V)).head = z := hz ▸ vC_lookup_reg a V
    congr 1
    congr 1
    exact hg ▸ rfl
  all_goals exact absurd h (by simp [lowerVarStepC])

/-- **The whole-program lowering soundness.** Whenever `lowerThirToCrypto c`
    succeeds with `comC` (i.e. every binding of `c` uses a covered op), the
    lowered catCrypt program denotes — under the transported valuation
    `mapVal V` — to the transport of the source THIR denotation. Structural
    induction on `c`: the `.ret` case is the variable square `vC_lookup`; the
    `.var` case threads `lowerVarStepC_denote` (the per-binding square) through
    the IH on the body, with the bound value carried as `transTy (op-denote)`. -/
theorem lowerThirToCrypto_denote : {Γ : Ctxt thirDialect} → {t : JasminTy} →
    (c : Com thirDialect Γ t) →
    ∀ (comC : Com catCryptDialect (mapCtx Γ) (mapTy t)),
      lowerThirToCrypto c = some comC → ∀ (V : Ctxt.Valuation Γ),
        comC.denote (mapVal V) = transTy (c.denote V)
  | _, _, .ret v, comC, h, V => by
      simp only [lowerThirToCrypto, Option.some.injEq] at h
      subst h
      simp only [Com.denote]
      exact vC_lookup v V
  | _, _, .var e body, comC, h, V => by
      -- The body lowers to some `bodyC`, else `h` is `none = some comC`.
      obtain ⟨bodyC, hbody⟩ : ∃ bodyC, lowerThirToCrypto body = some bodyC := by
        rcases hb : lowerThirToCrypto body with _ | bodyC
        · obtain ⟨op, hret, args⟩ := e
          rw [lowerThirToCrypto, hb] at h; exact absurd h (by simp)
        · exact ⟨bodyC, rfl⟩
      -- Take the IH on the body FIRST (keeps `body` the literal subterm for the
      -- structural recursion), then peel the op leaf.
      have ih := fun V' => lowerThirToCrypto_denote body bodyC hbody V'
      obtain ⟨op, hret, args⟩ := e
      subst hret
      have hstep : lowerVarStepC op args bodyC = some comC := by
        simpa only [lowerThirToCrypto, hbody] using h
      simp only [Com.denote, Expr.denote]
      rw [lowerVarStepC_denote op args bodyC comC hstep V]
      exact ih (Ctxt.Valuation.extend V
        (DialectDenote.denote (self := ThirDialect.thirDenote) op
          (Expr.lookupArgs args V)))

/-! ## 7. Smoke demonstrator (the probe op, end-to-end through the pass)

The `ThirFrontProbe` witness `srcAdd` (`let s = thBin .add w x y; ret s`) lowers
through the *pass* (`lowerThirToCrypto`, not a hand-built target), and the
whole-program denotation square `lowerThirToCrypto_denote` discharges
preservation. This closes the loop the probe scoped: the probe hand-wrote
`tgtAdd` and checked `rfl`; here the pass *produces* the target and the soundness
theorem proves it. -/

/-- The probe's source program, expressed locally over the register fragment. -/
def smokeSrc (w : Nat) : Com thirDialect [.reg w, .reg w] (.reg w) :=
  .var (.mk (.thBin .add w) rfl (.cons .here (.cons (.there .here) .nil)))
    (.ret .here)

/-- The pass succeeds on the probe op and produces a `catCryptDialect` program. -/
theorem smokeSrc_lowers (w : Nat) :
    (lowerThirToCrypto (smokeSrc w)).isSome := by
  rfl

/-- **End-to-end through the pass.** For the `some` result `comC` of the pass on
    `smokeSrc`, the lowered program denotes (on the transported valuation) to the
    transport of the source — the probe's preservation, via the op-set pass
    and the whole-program soundness theorem rather than a hand-built target. -/
theorem smokeSrc_denote (w : Nat)
    (comC : Com catCryptDialect (mapCtx [JasminTy.reg w, JasminTy.reg w]) (mapTy (.reg w)))
    (h : lowerThirToCrypto (smokeSrc w) = some comC)
    (V : Ctxt.Valuation (d := thirDialect) [.reg w, .reg w]) :
    comC.denote (mapVal V) = transTy ((smokeSrc w).denote V) :=
  lowerThirToCrypto_denote (smokeSrc w) comC h V

end CatCrypt.Crypto.SecureCompilation.ThirToCryptoDialect
