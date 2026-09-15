/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS

/-!
# Multi-value block lowering

A multi-value lowering from a dialect `d` to a dialect `d'` maps each source type
`t` to a list of target types `mapTys t`, and each source variable to the list of
target variables that carry its encoding. A field element represented by four
limbs, an extension-field element represented by its base coordinates, and a
curve point represented by its coordinates are instances.

The context map is the flattening `ctxFlat mapTys`, defined by recursion so that
`ctxFlat m (t :: Γ) = m t ++ ctxFlat m Γ` holds definitionally
(`ctxFlat_eq_flatMap` identifies it with `List.flatMap`). A valuation is
encoded by appending the encodings of its entries (`flatVal`).

Each source op `op` is lowered to a closed multi-result block
`lowerOp op : MultiReturnCom d' (ctxFlat mapTys (sig op)) (mapTys (ret op))`,
whose inputs are the flattened argument registers. The whole-program lowering
`lowerR` is continuation-passing with a renaming accumulator, as in
`BlockLoweringCPS.blockLowerComR`: each block is renamed once into the target
context along `argsHom` and spliced with `spliceMultiK`, which hands the block's
result variables to the continuation once. Reasoning about renamings goes through
`pullV` and valuation extensionality; no cast along a context equation occurs.

## Main definitions

* `hvAppend`, `inlHom`, `inrHom`, `appendHom`: append of valuations and the
  renamings of an appended context.
* `ctxFlat`, `flatVal`: the flattened context and the flattened valuation.
* `spliceMultiK`: splice of a multi-result block with a once-applied continuation.
* `MultiBlockLoweringData d d'`: the type map `mapTys` and the per-op blocks.
* `MultiBlockLoweringData.lowerR`, `lowerRM`: the lowering of a `Com`, respectively
  a `MultiReturnCom`, through a renaming accumulator and a continuation.
* `MultiBlockLoweringData.lowerMulti`, `lowerMultiM`: the lowerings at the identity
  renaming, returning the result registers.
* `MultiBlockLoweringData.comp`: composition of two multi-value lowerings.

## Main results

* `pullV_appendHom`, `pullV_inlHom`, `pullV_inrHom`, `pullV_comp`: the pullback
  algebra of appended contexts.
* `spliceMultiK_denote`: the denotation of `spliceMultiK`.
* `MultiBlockLoweringData.lowerR_denote_on`, `lowerRM_denote_on`: the
  continuation-passing transport squares under the `Good`-gated block square.
* `MultiBlockLoweringData.multiFundamental_on`: for every `Good`-covered program
  `c`, `(lowerMulti c).denote (flatVal enc V) = enc (c.denote V)`.
* `MultiBlockLoweringData.multiFundamentalM_on`: the same for multi-result source
  programs.
* `MultiBlockLoweringData.comp_blockSquare`, `comp_fundamental`: the block square
  and the whole-program square of the composite of two multi-value lowerings.

The acceptance instance is `MultiBlockLoweringToy`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS

/-! ## 1. Appended contexts -/

section Append

variable {d : Dialect}

/-- Append of two heterogeneous vectors. -/
def hvAppend {f : d.Ty → Type} : {xs ys : List d.Ty} →
    HVector f xs → HVector f ys → HVector f (xs ++ ys)
  | [], _, .nil, B => B
  | _ :: _, _, .cons a A, B => .cons a (hvAppend A B)

/-- The renaming of `xs` into `xs ++ ys`. -/
def inlHom : {xs : Ctxt d} → (ys : Ctxt d) → {t : d.Ty} → Var xs t → Var (xs ++ ys) t
  | _, _, _, .here => .here
  | _, ys, _, .there v => .there (inlHom ys v)

/-- The renaming of `ys` into `xs ++ ys`. -/
def inrHom : (xs : Ctxt d) → {ys : Ctxt d} → {t : d.Ty} → Var ys t → Var (xs ++ ys) t
  | [], _, _, v => v
  | _ :: xs, _, _, v => .there (inrHom xs v)

/-- The renaming of `xs ++ ys` that acts as `f` on `xs` and as `g` on `ys`. -/
def appendHom : {xs ys Δ : Ctxt d} → Ctxt.Hom xs Δ → Ctxt.Hom ys Δ →
    {t : d.Ty} → Var (xs ++ ys) t → Var Δ t
  | [], _, _, _, g, _, v => g v
  | _ :: _, _, _, f, _, _, .here => f .here
  | _ :: _, _, _, f, g, _, .there v => appendHom (fun w => f (.there w)) g v

/-- The renaming of a vector of variables, indexed by position. -/
def hvToHom {Δ : Ctxt d} : {ts : Ctxt d} → HVector (fun u => Var Δ u) ts →
    {t : d.Ty} → Var ts t → Var Δ t
  | _, .cons x _, _, .here => x
  | _, .cons _ xs, _, .there v => hvToHom xs v

/-- The vector of variables of a renaming, listed by position. -/
def homToHV {Δ : Ctxt d} : (ts : Ctxt d) → Ctxt.Hom ts Δ → HVector (fun u => Var Δ u) ts
  | [], _ => .nil
  | _ :: ts, f => .cons (f .here) (homToHV ts (fun v => f (.there v)))

variable [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]

/-- Pulling back along a composite renaming is the composite of the pullbacks. -/
theorem pullV_comp {Γ₁ Γ₂ Γ₃ : Ctxt d} (f : Ctxt.Hom Γ₁ Γ₂) (g : Ctxt.Hom Γ₂ Γ₃)
    (W : Valuation Γ₃) : pullV (fun v => g (f v)) W = pullV f (pullV g W) :=
  valuation_ext _ _ fun v => by rw [lookup_pullV, lookup_pullV, lookup_pullV]

omit [DialectSignature d] [DialectDenote d] in
/-- Looking up an `inlHom` variable in an appended valuation. -/
theorem lookup_inlHom {ys : Ctxt d} (B : Valuation ys) :
    ∀ {xs : Ctxt d} {t : d.Ty} (v : Var xs t) (A : Valuation xs),
      (inlHom ys v).lookup (hvAppend A B) = v.lookup A
  | _, _, .here, .cons _ _ => rfl
  | _, _, .there v, .cons _ A => lookup_inlHom B v A

omit [DialectSignature d] [DialectDenote d] in
/-- Looking up an `inrHom` variable in an appended valuation. -/
theorem lookup_inrHom {ys : Ctxt d} (B : Valuation ys) :
    ∀ {xs : Ctxt d} (A : Valuation xs) {t : d.Ty} (v : Var ys t),
      (inrHom xs v).lookup (hvAppend A B) = v.lookup B
  | [], .nil, _, _ => rfl
  | _ :: _, .cons _ A, _, v => lookup_inrHom B A v

/-- The pullback along `inlHom` of an appended valuation is its left part. -/
theorem pullV_inlHom {xs ys : Ctxt d} (A : Valuation xs) (B : Valuation ys) :
    pullV (inlHom ys) (hvAppend A B) = A :=
  valuation_ext _ _ fun v => by rw [lookup_pullV]; exact lookup_inlHom B v A

/-- The pullback along `inrHom` of an appended valuation is its right part. -/
theorem pullV_inrHom {xs ys : Ctxt d} (A : Valuation xs) (B : Valuation ys) :
    pullV (inrHom xs) (hvAppend A B) = B :=
  valuation_ext _ _ fun v => by rw [lookup_pullV]; exact lookup_inrHom B A v

/-- Looking up an `appendHom` variable. -/
theorem lookup_appendHom {ys Δ : Ctxt d} (g : Ctxt.Hom ys Δ) (W : Valuation Δ) :
    ∀ {xs : Ctxt d} (f : Ctxt.Hom xs Δ) {t : d.Ty} (v : Var (xs ++ ys) t),
      (appendHom f g v).lookup W = v.lookup (hvAppend (pullV f W) (pullV g W))
  | [], _, _, v => (lookup_pullV g v W).symm
  | _ :: _, _, _, .here => rfl
  | _ :: _, f, _, .there v => lookup_appendHom g W (fun w => f (.there w)) v

/-- The pullback along `appendHom f g` appends the pullbacks along `f` and `g`. -/
theorem pullV_appendHom {xs ys Δ : Ctxt d} (f : Ctxt.Hom xs Δ) (g : Ctxt.Hom ys Δ)
    (W : Valuation Δ) :
    pullV (appendHom f g) W = hvAppend (pullV f W) (pullV g W) :=
  valuation_ext _ _ fun v => by rw [lookup_pullV]; exact lookup_appendHom g W f v

omit [DialectSignature d] [DialectDenote d] in
/-- The pullback along `hvToHom vs` looks up the variables `vs`. -/
theorem pullV_hvToHom {Δ : Ctxt d} (W : Valuation Δ) :
    ∀ {ts : Ctxt d} (vs : HVector (fun u => Var Δ u) ts),
      pullV (hvToHom vs) W = MultiReturnCom.lookupVars vs W
  | [], .nil => rfl
  | _ :: _, .cons x xs => by
      show HVector.cons _ (pullV (hvToHom xs) W) = HVector.cons _ _
      rw [pullV_hvToHom W xs]
      rfl

omit [DialectSignature d] [DialectDenote d] in
/-- Looking up the variables of a renaming is pulling back along it. -/
theorem lookupVars_homToHV {Δ : Ctxt d} (W : Valuation Δ) :
    ∀ (ts : Ctxt d) (f : Ctxt.Hom ts Δ),
      MultiReturnCom.lookupVars (homToHV ts f) W = pullV f W
  | [], _ => rfl
  | _ :: ts, f => by
      show HVector.cons _ (MultiReturnCom.lookupVars (homToHV ts _) W) = HVector.cons _ _
      rw [lookupVars_homToHV W ts]

omit [DialectSignature d] [DialectDenote d] in
/-- `MultiReturnCom.lookupVars` and `Expr.lookupArgs` agree. -/
theorem lookupVars_eq_lookupArgs {Γ : Ctxt d} (V : Valuation Γ) :
    ∀ {ts : Ctxt d} (vs : HVector (fun u => Var Γ u) ts),
      MultiReturnCom.lookupVars vs V = Expr.lookupArgs vs V
  | [], .nil => rfl
  | _ :: _, .cons _ xs => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [lookupVars_eq_lookupArgs V xs]

/-- Renaming a vector of variables and looking it up is looking it up against the
    pullback. -/
theorem lookupVars_renameVars {Γ Γ' : Ctxt d} (h : Ctxt.Hom Γ Γ') (V : Valuation Γ') :
    ∀ {ts : Ctxt d} (vs : HVector (fun u => Var Γ u) ts),
      MultiReturnCom.lookupVars (HVector.renameVars h vs) V
        = MultiReturnCom.lookupVars vs (pullV h V) := by
  intro ts vs
  rw [lookupVars_eq_lookupArgs, lookupVars_eq_lookupArgs, lookupArgs_renameVars]

/-- Renaming a multi-result program and denoting it is denoting the original
    against the pullback. -/
theorem multiReturnCom_denote_rename {Γ Γ' : Ctxt d} {ts : List d.Ty}
    (h : Ctxt.Hom Γ Γ') (m : MultiReturnCom d Γ ts) (V : Valuation Γ') :
    (MultiReturnCom.rename h m).denote V = m.denote (pullV h V) := by
  induction m generalizing Γ' with
  | ret vs =>
      simp only [MultiReturnCom.rename, MultiReturnCom.denote]
      exact lookupVars_renameVars h V vs
  | var e body ih =>
      simp only [MultiReturnCom.rename, MultiReturnCom.denote]
      rw [ih h.lift (Ctxt.Valuation.extend V ((e.rename h).denote V))]
      rw [Expr.denote_rename h e V]
      congr 1
      show HVector.cons (e.denote (pullV h V))
          (pullV (fun v => (h v).there) (HVector.cons (e.denote (pullV h V)) V))
        = HVector.cons (e.denote (pullV h V)) (pullV h V)
      rw [pullV_there h (e.denote (pullV h V)) V]

end Append

/-! ## 2. Flattened contexts and valuations -/

section Flat

variable {d d' : Dialect}

/-- The flattened context: each source type `t` contributes the target types
    `m t`. -/
@[reducible] def ctxFlat (m : d.Ty → List d'.Ty) : Ctxt d → Ctxt d'
  | [] => []
  | t :: Γ => m t ++ ctxFlat m Γ

/-- `ctxFlat` is `List.flatMap`. -/
theorem ctxFlat_eq_flatMap (m : d.Ty → List d'.Ty) (Γ : Ctxt d) :
    ctxFlat m Γ = Γ.flatMap m := by
  induction Γ with
  | nil => rfl
  | cons t Γ ih => simp [ctxFlat, ih]

/-- The renaming of the registers of the source variable `v` into the flattened
    context. -/
def varHom (m : d.Ty → List d'.Ty) : {Γ : Ctxt d} → {u : d.Ty} → Var Γ u →
    Ctxt.Hom (m u) (ctxFlat m Γ)
  | _ :: Γ, _, .here => fun w => inlHom (ctxFlat m Γ) w
  | t :: _, _, .there v => fun w => inrHom (m t) (varHom m v w)

/-- The renaming of the flattened argument context of a vector of source
    variables, through a renaming `ren` of the flattened context. -/
def argsHom (m : d.Ty → List d'.Ty) {Γ : Ctxt d} {Δ : Ctxt d'}
    (ren : Ctxt.Hom (ctxFlat m Γ) Δ) :
    {ts : Ctxt d} → HVector (fun u => Var Γ u) ts → Ctxt.Hom (ctxFlat m ts) Δ
  | [], .nil => fun v => nomatch v
  | _ :: _, .cons a rest => appendHom (fun w => ren (varHom m a w)) (argsHom m ren rest)

/-- The renaming of `ctxFlat m (xs ++ ys)` into
    `ctxFlat m xs ++ ctxFlat m ys`. -/
def splitHom (m : d.Ty → List d'.Ty) : (xs ys : Ctxt d) →
    Ctxt.Hom (ctxFlat m (xs ++ ys)) (ctxFlat m xs ++ ctxFlat m ys)
  | [], _ => fun v => v
  | x :: xs, ys =>
      appendHom (fun w => inlHom (ctxFlat m ys) (inlHom (ctxFlat m xs) w))
        (fun w => appendHom (fun u => inlHom (ctxFlat m ys) (inrHom (m x) u))
          (inrHom (m x ++ ctxFlat m xs)) (splitHom m xs ys w))

variable [TyDenote d.Ty] [TyDenote d'.Ty]

/-- The flattened valuation: the appended encodings of the entries. -/
def flatVal {m : d.Ty → List d'.Ty} (enc : ∀ {t : d.Ty}, ⟦t⟧ → Valuation (m t)) :
    {Γ : Ctxt d} → Valuation Γ → Valuation (ctxFlat m Γ)
  | [], .nil => .nil
  | _ :: _, .cons x V => hvAppend (enc x) (flatVal enc V)

variable [DialectSignature d'] [DialectDenote d']

omit [TyDenote d.Ty] in
/-- The pullback of a split flattened valuation. -/
theorem pullV_splitHom_flatVal {m : d.Ty → List d'.Ty} [TyDenote d.Ty]
    (enc : ∀ {t : d.Ty}, ⟦t⟧ → Valuation (m t)) :
    ∀ {xs ys : Ctxt d} (A : Valuation xs) (B : Valuation ys),
      pullV (splitHom m xs ys) (hvAppend (flatVal enc A) (flatVal enc B))
        = flatVal enc (hvAppend A B)
  | [], _, .nil, B => pullV_id _
  | x :: xs, ys, .cons a A, B => by
      have hF : pullV (fun w => inlHom (ctxFlat m ys) (inlHom (ctxFlat m xs) w))
          (hvAppend (hvAppend (enc a) (flatVal enc A)) (flatVal enc B)) = enc a := by
        rw [pullV_comp (fun w => inlHom (ctxFlat m xs) w) (fun w => inlHom (ctxFlat m ys) w),
          pullV_inlHom, pullV_inlHom]
      have hM : pullV (appendHom (fun u => inlHom (ctxFlat m ys) (inrHom (m x) u))
            (inrHom (m x ++ ctxFlat m xs)))
          (hvAppend (hvAppend (enc a) (flatVal enc A)) (flatVal enc B))
          = hvAppend (flatVal enc A) (flatVal enc B) := by
        rw [pullV_appendHom, pullV_comp (fun u => inrHom (m x) u)
          (fun w => inlHom (ctxFlat m ys) w), pullV_inlHom, pullV_inrHom, pullV_inrHom]
      have hG : pullV (fun w => appendHom (fun u => inlHom (ctxFlat m ys) (inrHom (m x) u))
            (inrHom (m x ++ ctxFlat m xs)) (splitHom m xs ys w))
          (hvAppend (hvAppend (enc a) (flatVal enc A)) (flatVal enc B))
          = flatVal enc (hvAppend A B) := by
        rw [pullV_comp (fun w => splitHom m xs ys w)
          (fun w => appendHom (fun u => inlHom (ctxFlat m ys) (inrHom (m x) u))
            (inrHom (m x ++ ctxFlat m xs)) w), hM, pullV_splitHom_flatVal enc A B]
      exact (pullV_appendHom _ _ _).trans (congrArg₂ hvAppend hF hG)

variable [DialectSignature d] [DialectDenote d]

omit [DialectSignature d] [DialectDenote d] in
/-- The pullback of a flattened valuation along `varHom v` is the encoding of the
    value of `v`. -/
theorem pullV_varHom_flatVal {m : d.Ty → List d'.Ty}
    (enc : ∀ {t : d.Ty}, ⟦t⟧ → Valuation (m t)) :
    ∀ {Γ : Ctxt d} {u : d.Ty} (v : Var Γ u) (V : Valuation Γ),
      pullV (varHom m v) (flatVal enc V) = enc (v.lookup V)
  | _ :: _, _, .here, .cons x V => pullV_inlHom (enc x) (flatVal enc V)
  | t :: _, _, .there v, .cons x V => by
      show pullV (fun w => inrHom (m t) (varHom m v w)) (hvAppend (enc x) (flatVal enc V))
        = enc (v.lookup V)
      rw [pullV_comp, pullV_inrHom, pullV_varHom_flatVal enc v V]

omit [DialectSignature d] [DialectDenote d] in
/-- The pullback along `argsHom ren args` of a valuation whose pullback along `ren`
    is a flattened valuation is the flattened valuation of the argument values. -/
theorem pullV_argsHom {m : d.Ty → List d'.Ty}
    (enc : ∀ {t : d.Ty}, ⟦t⟧ → Valuation (m t)) {Γ : Ctxt d} {Δ : Ctxt d'}
    (ren : Ctxt.Hom (ctxFlat m Γ) Δ) (W : Valuation Δ) (V : Valuation Γ)
    (hW : pullV ren W = flatVal enc V) :
    ∀ {ts : Ctxt d} (args : HVector (fun u => Var Γ u) ts),
      pullV (argsHom m ren args) W = flatVal enc (Expr.lookupArgs args V)
  | [], .nil => rfl
  | _ :: _, .cons a rest => by
      show pullV (appendHom (fun w => ren (varHom m a w)) (argsHom m ren rest)) W
        = hvAppend (enc (a.lookup V)) (flatVal enc (Expr.lookupArgs rest V))
      rw [pullV_appendHom, pullV_comp, hW, pullV_varHom_flatVal,
        pullV_argsHom enc ren W V hW rest]

end Flat

/-! ## 3. The multi-result splice -/

section SpliceK

variable {d : Dialect} [DialectSignature d]

/-- **Multi-result block splice with a once-applied continuation.**
    `spliceMultiK blk k` keeps the bindings of `blk` and, at its return vector
    `res`, emits `k ren res`, where `ren` renames the context of `blk` into the
    extended context. -/
def spliceMultiK : {Γ : Ctxt d} → {ts bs : List d.Ty} →
    MultiReturnCom d Γ ts →
    ({Δ : Ctxt d} → Ctxt.Hom Γ Δ → HVector (fun u => Var Δ u) ts → MultiReturnCom d Δ bs) →
    MultiReturnCom d Γ bs
  | _, _, _, .ret vs, k => k (fun x => x) vs
  | _, _, _, .var e blk, k =>
      .var e (spliceMultiK blk (fun ren res => k (fun x => ren (.there x)) res))

variable [TyDenote d.Ty] [DialectDenote d]

/-- **Denotation of `spliceMultiK`.** If `k ren res` denotes `G` whenever `ren`
    preserves lookups back to `W` and `res` holds the block's values, the spliced
    program denotes `G`. -/
theorem spliceMultiK_denote : {Γ : Ctxt d} → {ts bs : List d.Ty} →
    (blk : MultiReturnCom d Γ ts) →
    (k : {Δ : Ctxt d} → Ctxt.Hom Γ Δ → HVector (fun u => Var Δ u) ts →
      MultiReturnCom d Δ bs) →
    (W : Valuation Γ) → (G : ListDenote bs) →
    (∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ) (res : HVector (fun u => Var Δ u) ts)
        (W' : Valuation Δ),
        (∀ {s : d.Ty} (v : Var Γ s), (ren v).lookup W' = v.lookup W) →
        MultiReturnCom.lookupVars res W' = blk.denote W →
        (k ren res).denote W' = G) →
    (spliceMultiK blk k).denote W = G
  | _, _, _, .ret vs, _, W, _, hk => hk (fun x => x) vs W (fun _ => rfl) rfl
  | _, _, _, .var e blk, _, W, G, hk =>
      spliceMultiK_denote blk _ (Valuation.extend W (e.denote W)) G
        (fun ren res W' h1 h2 => hk (fun x => ren (.there x)) res W'
          (fun v => h1 (.there v)) h2)

end SpliceK

/-! ## 4. Coverage of multi-result programs -/

/-- A multi-result program is `Good`-covered when every let-bound expression
    satisfies `Good`. -/
def CoveredM {d : Dialect} [DialectSignature d]
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) :
    {Γ : Ctxt d} → {ts : List d.Ty} → MultiReturnCom d Γ ts → Prop
  | _, _, .ret _ => True
  | _, _, .var e body => Good e ∧ CoveredM Good body

/-! ## 5. Multi-value lowering data and the lowering -/

/-- **Multi-value block lowering data.** Each source type is represented by a list
    of target types, and each source op by a closed multi-result target block over
    the flattened argument registers, returning the registers of the result. -/
structure MultiBlockLoweringData (d d' : Dialect) [DialectSignature d]
    [DialectSignature d'] where
  /-- The target types representing a source type. -/
  mapTys : d.Ty → List d'.Ty
  /-- The block of a source op, over the flattened argument registers. -/
  lowerOp : (op : d.Op) →
    MultiReturnCom d' (ctxFlat mapTys (DialectSignature.sig op))
      (mapTys (DialectSignature.ret op))

namespace MultiBlockLoweringData

section Defs

variable {d d' : Dialect} [DialectSignature d] [DialectSignature d']

/-- The flattened context map of a multi-value lowering. -/
abbrev mapCtx (L : MultiBlockLoweringData d d') (Γ : Ctxt d) : Ctxt d' :=
  ctxFlat L.mapTys Γ

/-- The block of an expression, over the flattened registers of its arguments. -/
def exprBlock (L : MultiBlockLoweringData d d') {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) :
    MultiReturnCom d' (L.mapCtx (DialectSignature.sig e.op)) (L.mapTys t) :=
  cast (congrArg (fun s => MultiReturnCom d' (L.mapCtx (DialectSignature.sig e.op)) (L.mapTys s))
    e.retTy_eq) (L.lowerOp e.op)

/-- **The renaming-accumulator lowering of a let-binding.** Renames the block of
    `e` into `Δ` and splices it; the continuation `kBody` receives the extended
    renaming of `L.mapCtx (t :: Γ)`. -/
def lowerBind (L : MultiBlockLoweringData d d') {Γ : Ctxt d} {t : d.Ty} {Δ : Ctxt d'}
    {bs : List d'.Ty} (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (e : Expr d Γ t)
    (kBody : {Δ' : Ctxt d'} → Ctxt.Hom Δ Δ' → Ctxt.Hom (L.mapCtx (t :: Γ)) Δ' →
      MultiReturnCom d' Δ' bs) :
    MultiReturnCom d' Δ bs :=
  spliceMultiK (MultiReturnCom.rename (argsHom L.mapTys ren e.args) (L.exprBlock e))
    (fun ren' res => kBody ren' (appendHom (hvToHom res) (fun w => ren' (ren w))))

/-- **The continuation-passing lowering of a program.** `lowerR ren c k` lowers `c`
    through the renaming `ren` of the flattened source context into `Δ`, and passes
    the registers of the result to `k`. -/
def lowerR (L : MultiBlockLoweringData d d') :
    {Γ : Ctxt d} → {t : d.Ty} → {Δ : Ctxt d'} → {bs : List d'.Ty} →
    Ctxt.Hom (L.mapCtx Γ) Δ → Com d Γ t →
    ({Δ' : Ctxt d'} → Ctxt.Hom Δ Δ' → HVector (fun u => Var Δ' u) (L.mapTys t) →
      MultiReturnCom d' Δ' bs) →
    MultiReturnCom d' Δ bs
  | _, _, _, _, ren, .ret v, k =>
      k (fun x => x) (homToHV _ (fun w => ren (varHom L.mapTys v w)))
  | _, _, _, _, ren, .var e body, k =>
      L.lowerBind ren e (fun ren' renB =>
        L.lowerR renB body (fun ren'' vs => k (fun x => ren'' (ren' x)) vs))

/-- **The continuation-passing lowering of a multi-result program.** -/
def lowerRM (L : MultiBlockLoweringData d d') :
    {Γ : Ctxt d} → {ts : List d.Ty} → {Δ : Ctxt d'} → {bs : List d'.Ty} →
    Ctxt.Hom (L.mapCtx Γ) Δ → MultiReturnCom d Γ ts →
    ({Δ' : Ctxt d'} → Ctxt.Hom Δ Δ' → HVector (fun u => Var Δ' u) (L.mapCtx ts) →
      MultiReturnCom d' Δ' bs) →
    MultiReturnCom d' Δ bs
  | _, _, _, _, ren, .ret vs, k =>
      k (fun x => x) (homToHV _ (argsHom L.mapTys ren vs))
  | _, _, _, _, ren, .var e body, k =>
      L.lowerBind ren e (fun ren' renB =>
        L.lowerRM renB body (fun ren'' vs => k (fun x => ren'' (ren' x)) vs))

/-- **The multi-value lowering of a program**, returning the registers of its
    result. -/
def lowerMulti (L : MultiBlockLoweringData d d') {Γ : Ctxt d} {t : d.Ty}
    (c : Com d Γ t) : MultiReturnCom d' (L.mapCtx Γ) (L.mapTys t) :=
  L.lowerR (fun v => v) c (fun _ vs => .ret vs)

/-- **The multi-value lowering of a multi-result program**, returning the
    registers of its results. -/
def lowerMultiM (L : MultiBlockLoweringData d d') {Γ : Ctxt d} {ts : List d.Ty}
    (m : MultiReturnCom d Γ ts) : MultiReturnCom d' (L.mapCtx Γ) (L.mapCtx ts) :=
  L.lowerRM (fun v => v) m (fun _ vs => .ret vs)

end Defs

/-! ## 6. The fundamental theorem -/

section Fundamental

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
variable {d' : Dialect} [TyDenote d'.Ty] [DialectSignature d'] [DialectDenote d']

/-- The encoding of source values carried by a multi-value lowering. -/
abbrev Enc (L : MultiBlockLoweringData d d') := ∀ {t : d.Ty}, ⟦t⟧ → Valuation (L.mapTys t)

/-- **The `Good`-gated block square.** The block of every `Good` expression maps the
    flattened encoding of the argument values to the encoding of the op's value. -/
def BlockSquare (L : MultiBlockLoweringData d d') (enc : L.Enc)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) : Prop :=
  ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e →
    ∀ vals : Valuation (DialectSignature.sig e.op),
      (L.lowerOp e.op).denote (flatVal enc vals) = enc (DialectDenote.denote e.op vals)

/-- **Transport square of a lowered let-binding.** -/
theorem lowerBind_denote (L : MultiBlockLoweringData d d') (enc : L.Enc)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) (hBlk : L.BlockSquare enc Good)
    {Γ : Ctxt d} {t : d.Ty} {Δ : Ctxt d'} {bs : List d'.Ty}
    (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (e : Expr d Γ t) (hg : Good e)
    (kBody : {Δ' : Ctxt d'} → Ctxt.Hom Δ Δ' → Ctxt.Hom (L.mapCtx (t :: Γ)) Δ' →
      MultiReturnCom d' Δ' bs)
    (W : Valuation Δ) (V : Valuation Γ) (G : ListDenote bs)
    (hW : pullV ren W = flatVal enc V)
    (hk : ∀ {Δ' : Ctxt d'} (ren' : Ctxt.Hom Δ Δ') (renB : Ctxt.Hom (L.mapCtx (t :: Γ)) Δ')
        (W' : Valuation Δ'),
        (∀ {s : d'.Ty} (v : Var Δ s), (ren' v).lookup W' = v.lookup W) →
        pullV renB W' = flatVal enc (Valuation.extend V (e.denote V)) →
        (kBody ren' renB).denote W' = G) :
    (L.lowerBind ren e kBody).denote W = G := by
  refine spliceMultiK_denote _ _ W G (fun ren' res W' h1 h2 => hk ren' _ W' h1 ?_)
  have hW' : pullV ren' W' = W := valuation_ext _ _ fun v => by rw [lookup_pullV]; exact h1 v
  have hR : pullV (fun w => ren' (ren w)) W' = flatVal enc V := by
    rw [pullV_comp (fun w => ren w) (fun w => ren' w), hW', hW]
  have hL : pullV (hvToHom res) W' = enc (e.denote V) := by
    rw [pullV_hvToHom, h2, multiReturnCom_denote_rename, pullV_argsHom enc ren W V hW]
    rcases e with ⟨op, rfl, args⟩
    exact hBlk ⟨op, rfl, args⟩ hg _
  exact (pullV_appendHom (hvToHom res) (fun w => ren' (ren w)) W').trans
    (congrArg₂ hvAppend hL hR)

/-- **Continuation-passing transport square of `lowerR`.** -/
theorem lowerR_denote_on (L : MultiBlockLoweringData d d') (enc : L.Enc)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) (hBlk : L.BlockSquare enc Good) :
    ∀ {Γ : Ctxt d} {t : d.Ty} {Δ : Ctxt d'} {bs : List d'.Ty}
      (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (c : Com d Γ t)
      (k : {Δ' : Ctxt d'} → Ctxt.Hom Δ Δ' → HVector (fun u => Var Δ' u) (L.mapTys t) →
        MultiReturnCom d' Δ' bs)
      (W : Valuation Δ) (V : Valuation Γ) (G : ListDenote bs),
      CoveredCom Good c → pullV ren W = flatVal enc V →
      (∀ {Δ' : Ctxt d'} (ren' : Ctxt.Hom Δ Δ') (res : HVector (fun u => Var Δ' u) (L.mapTys t))
          (W' : Valuation Δ'),
          (∀ {s : d'.Ty} (v : Var Δ s), (ren' v).lookup W' = v.lookup W) →
          MultiReturnCom.lookupVars res W' = enc (c.denote V) →
          (k ren' res).denote W' = G) →
      (L.lowerR ren c k).denote W = G
  | _, _, _, _, ren, .ret v, k, W, V, G, _, hW, hk => by
      refine hk (fun x => x) _ W (fun _ => rfl) ?_
      rw [lookupVars_homToHV, pullV_comp, hW, pullV_varHom_flatVal]
      rfl
  | _, _, _, _, ren, .var e body, k, W, V, G, hc, hW, hk =>
      L.lowerBind_denote enc Good hBlk ren e hc.1 _ W V G hW
        (fun ren' renB W' h1 hB =>
          lowerR_denote_on L enc Good hBlk renB body _ W' _ G hc.2 hB
            (fun ren'' res W'' h1' h2' =>
              hk (fun x => ren'' (ren' x)) res W''
                (fun v => (h1' (ren' v)).trans (h1 v)) h2'))

/-- **Continuation-passing transport square of `lowerRM`.** -/
theorem lowerRM_denote_on (L : MultiBlockLoweringData d d') (enc : L.Enc)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) (hBlk : L.BlockSquare enc Good) :
    ∀ {Γ : Ctxt d} {ts : List d.Ty} {Δ : Ctxt d'} {bs : List d'.Ty}
      (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (m : MultiReturnCom d Γ ts)
      (k : {Δ' : Ctxt d'} → Ctxt.Hom Δ Δ' → HVector (fun u => Var Δ' u) (L.mapCtx ts) →
        MultiReturnCom d' Δ' bs)
      (W : Valuation Δ) (V : Valuation Γ) (G : ListDenote bs),
      CoveredM Good m → pullV ren W = flatVal enc V →
      (∀ {Δ' : Ctxt d'} (ren' : Ctxt.Hom Δ Δ') (res : HVector (fun u => Var Δ' u) (L.mapCtx ts))
          (W' : Valuation Δ'),
          (∀ {s : d'.Ty} (v : Var Δ s), (ren' v).lookup W' = v.lookup W) →
          MultiReturnCom.lookupVars res W' = flatVal enc (m.denote V) →
          (k ren' res).denote W' = G) →
      (L.lowerRM ren m k).denote W = G
  | _, _, _, _, ren, .ret vs, k, W, V, G, _, hW, hk => by
      refine hk (fun x => x) _ W (fun _ => rfl) ?_
      rw [lookupVars_homToHV, pullV_argsHom enc ren W V hW]
      show _ = flatVal enc (MultiReturnCom.lookupVars vs V)
      rw [lookupVars_eq_lookupArgs]
  | _, _, _, _, ren, .var e body, k, W, V, G, hc, hW, hk =>
      L.lowerBind_denote enc Good hBlk ren e hc.1 _ W V G hW
        (fun ren' renB W' h1 hB =>
          lowerRM_denote_on L enc Good hBlk renB body _ W' _ G hc.2 hB
            (fun ren'' res W'' h1' h2' =>
              hk (fun x => ren'' (ren' x)) res W''
                (fun v => (h1' (ren' v)).trans (h1 v)) h2'))

/-- **Fundamental theorem of multi-value block lowering.** Under the `Good`-gated
    block square, every `Good`-covered program lowers to a multi-result program
    that maps the flattened encoding of the inputs to the encoding of the source
    value. -/
theorem multiFundamental_on (L : MultiBlockLoweringData d d') (enc : L.Enc)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) (hBlk : L.BlockSquare enc Good)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (hc : CoveredCom Good c) (V : Valuation Γ) :
    (L.lowerMulti c).denote (flatVal enc V) = enc (c.denote V) :=
  L.lowerR_denote_on enc Good hBlk (fun v => v) c _ (flatVal enc V) V _ hc (pullV_id _)
    (fun _ _ _ _ h2 => h2)

/-- **Fundamental theorem of multi-value block lowering, multi-result source.** -/
theorem multiFundamentalM_on (L : MultiBlockLoweringData d d') (enc : L.Enc)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) (hBlk : L.BlockSquare enc Good)
    {Γ : Ctxt d} {ts : List d.Ty} (m : MultiReturnCom d Γ ts) (hm : CoveredM Good m)
    (V : Valuation Γ) :
    (L.lowerMultiM m).denote (flatVal enc V) = flatVal enc (m.denote V) :=
  L.lowerRM_denote_on enc Good hBlk (fun v => v) m _ (flatVal enc V) V _ hm (pullV_id _)
    (fun _ _ _ _ h2 => h2)

end Fundamental

/-! ## 7. Composition -/

section Comp

variable {d d' d'' : Dialect}
variable [DialectSignature d] [DialectSignature d'] [DialectSignature d'']

/-- The renaming of `ctxFlat m₂ (ctxFlat m₁ Γ)` into the flattened context of the
    composite type map. -/
def compHom (m₁ : d.Ty → List d'.Ty) (m₂ : d'.Ty → List d''.Ty) :
    (Γ : Ctxt d) → Ctxt.Hom (ctxFlat m₂ (ctxFlat m₁ Γ)) (ctxFlat (fun t => ctxFlat m₂ (m₁ t)) Γ)
  | [] => fun v => v
  | t :: Γ => fun v =>
      appendHom (inlHom _) (fun w => inrHom (ctxFlat m₂ (m₁ t)) (compHom m₁ m₂ Γ w))
        (splitHom m₂ (m₁ t) (ctxFlat m₁ Γ) v)

/-- **Composition of multi-value lowerings.** A source type is represented by the
    flattened representation of its first-stage types, and the block of a source op
    is the second-stage lowering of its first-stage block. -/
@[reducible] def comp (L₁ : MultiBlockLoweringData d d') (L₂ : MultiBlockLoweringData d' d'') :
    MultiBlockLoweringData d d'' where
  mapTys := fun t => L₂.mapCtx (L₁.mapTys t)
  lowerOp := fun op =>
    MultiReturnCom.rename (compHom L₁.mapTys L₂.mapTys (DialectSignature.sig op))
      (L₂.lowerMultiM (L₁.lowerOp op))

variable [TyDenote d.Ty] [TyDenote d'.Ty] [TyDenote d''.Ty]
variable [DialectDenote d] [DialectDenote d'] [DialectDenote d'']

/-- The encoding of the composite lowering: the second-stage flattening of the
    first-stage encoding. -/
def compEnc (L₁ : MultiBlockLoweringData d d') (L₂ : MultiBlockLoweringData d' d'')
    (enc₁ : L₁.Enc) (enc₂ : L₂.Enc) : (L₁.comp L₂).Enc :=
  fun x => flatVal enc₂ (enc₁ x)

omit [DialectDenote d] [DialectDenote d'] in
/-- The pullback along `compHom` of a composite flattened valuation. -/
theorem pullV_compHom (L₁ : MultiBlockLoweringData d d') (L₂ : MultiBlockLoweringData d' d'')
    (enc₁ : L₁.Enc) (enc₂ : L₂.Enc) :
    ∀ {Γ : Ctxt d} (V : Valuation Γ),
      pullV (compHom L₁.mapTys L₂.mapTys Γ) (flatVal (compEnc L₁ L₂ enc₁ enc₂) V)
        = flatVal enc₂ (flatVal enc₁ V)
  | [], .nil => rfl
  | t :: Γ, .cons x V => by
      show pullV (fun v => appendHom (inlHom _)
          (fun w => inrHom (ctxFlat L₂.mapTys (L₁.mapTys t)) (compHom L₁.mapTys L₂.mapTys Γ w))
          (splitHom L₂.mapTys (L₁.mapTys t) (ctxFlat L₁.mapTys Γ) v))
          (hvAppend (flatVal enc₂ (enc₁ x)) (flatVal (compEnc L₁ L₂ enc₁ enc₂) V))
        = flatVal enc₂ (hvAppend (enc₁ x) (flatVal enc₁ V))
      have hR : pullV (fun w => inrHom (ctxFlat L₂.mapTys (L₁.mapTys t))
            (compHom L₁.mapTys L₂.mapTys Γ w))
          (hvAppend (flatVal enc₂ (enc₁ x)) (flatVal (compEnc L₁ L₂ enc₁ enc₂) V))
          = flatVal enc₂ (flatVal enc₁ V) := by
        rw [pullV_comp (fun w => compHom L₁.mapTys L₂.mapTys Γ w)
          (fun w => inrHom (ctxFlat L₂.mapTys (L₁.mapTys t)) w), pullV_inrHom,
          pullV_compHom L₁ L₂ enc₁ enc₂ V]
      have hg := (pullV_appendHom (inlHom _)
          (fun w => inrHom (ctxFlat L₂.mapTys (L₁.mapTys t)) (compHom L₁.mapTys L₂.mapTys Γ w))
          (hvAppend (flatVal enc₂ (enc₁ x)) (flatVal (compEnc L₁ L₂ enc₁ enc₂) V))).trans
        (congrArg₂ hvAppend (pullV_inlHom _ _) hR)
      exact (pullV_comp _ _ _).trans ((congrArg (pullV (splitHom L₂.mapTys (L₁.mapTys t)
        (ctxFlat L₁.mapTys Γ))) hg).trans (pullV_splitHom_flatVal enc₂ _ _))

/-- **Block square of the composite lowering.** The composite's blocks satisfy the
    `Good₁`-gated block square when the first stage's blocks do, the second stage's
    blocks satisfy the `Good₂`-gated block square, and the first stage's blocks of
    `Good₁` expressions are `Good₂`-covered. -/
theorem comp_blockSquare (L₁ : MultiBlockLoweringData d d') (L₂ : MultiBlockLoweringData d' d'')
    (enc₁ : L₁.Enc) (enc₂ : L₂.Enc)
    (Good₁ : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (Good₂ : ∀ {Γ : Ctxt d'} {t : d'.Ty}, Expr d' Γ t → Prop)
    (hBlk₁ : L₁.BlockSquare enc₁ Good₁) (hBlk₂ : L₂.BlockSquare enc₂ Good₂)
    (hCov : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good₁ e → CoveredM Good₂ (L₁.lowerOp e.op)) :
    (L₁.comp L₂).BlockSquare (compEnc L₁ L₂ enc₁ enc₂) Good₁ := by
  intro Γ t e hg vals
  show (MultiReturnCom.rename (compHom L₁.mapTys L₂.mapTys (DialectSignature.sig e.op))
      (L₂.lowerMultiM (L₁.lowerOp e.op))).denote (flatVal (compEnc L₁ L₂ enc₁ enc₂) vals)
    = flatVal enc₂ (enc₁ (DialectDenote.denote e.op vals))
  exact (multiReturnCom_denote_rename _ _ _).trans (by
    rw [pullV_compHom, L₂.multiFundamentalM_on enc₂ Good₂ hBlk₂ _ (hCov e hg), hBlk₁ e hg vals])

/-- **Whole-program square of the composite lowering.** -/
theorem comp_fundamental (L₁ : MultiBlockLoweringData d d') (L₂ : MultiBlockLoweringData d' d'')
    (enc₁ : L₁.Enc) (enc₂ : L₂.Enc)
    (Good₁ : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (Good₂ : ∀ {Γ : Ctxt d'} {t : d'.Ty}, Expr d' Γ t → Prop)
    (hBlk₁ : L₁.BlockSquare enc₁ Good₁) (hBlk₂ : L₂.BlockSquare enc₂ Good₂)
    (hCov : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good₁ e → CoveredM Good₂ (L₁.lowerOp e.op))
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (hc : CoveredCom Good₁ c) (V : Valuation Γ) :
    ((L₁.comp L₂).lowerMulti c).denote (flatVal (compEnc L₁ L₂ enc₁ enc₂) V)
      = flatVal enc₂ (enc₁ (c.denote V)) :=
  (L₁.comp L₂).multiFundamental_on (compEnc L₁ L₂ enc₁ enc₂) Good₁
    (comp_blockSquare L₁ L₂ enc₁ enc₂ Good₁ Good₂ hBlk₁ hBlk₂ hCov) c hc V

end Comp

end MultiBlockLoweringData

end CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
