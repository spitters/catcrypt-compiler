/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.MergeCom
public import CatCrypt.Crypto.SecureCompilation.VIR.ComParametricityTransport

/-!
# Block-expanding `Com d → Com d'` descent functor (one-op→a-block lowering)

Dialect map, lowering status and upstream lineage: `VIR/DIALECTS.md`.

`ComParametricityTransport.LoweringData` is the *structural* (single-op→single-op)
lowering: its `lowerExpr : Expr d Γ t → Expr d' (mapCtx Γ) (mapTy t)` emits **one**
target `Expr` per source op, so `fundamental` lifts per-op leaf squares to the whole
program. That is exactly the shape that a byte-correct field descent CANNOT use: a
single BabyBear `fMul` realizes to a **block** of jasmin word ops (`a*b` then the
10-fold + 2-csub `bbReduce`), and a single `fAdd` to `a+b` then a conditional-subtract
block — one source op → *several* target bindings, under the non-identity encoding
`bbEnc : ZMod P → BitVec 64`. `ComParametricityTransport` explicitly excludes this
(`FieldDescent.lean` §8: "one op → a block of ops … the case a single-op `lowerExpr`
cannot express"), so the whole-program word assembly is currently only a *named
residual* (`Poseidon2WholePermCom.poseidon2_perm_com_denote_residual`).

This file supplies the missing compiler piece: a **block-expanding descent functor**
`Com d Γ t → Com d' (mapCtx Γ) (mapTy t)` where each source op expands to a whole
target BLOCK, with a `fundamental`-style whole-program denotation-preservation theorem
that consumes only the per-op **block** squares.

## The one new primitive: `Com.spliceCom`

`LoweringData.lowerCom`'s `var` arm is `.var (lowerExpr e) (lowerCom body)` — a single
`.var`, because the lowered op is a single `Expr`. Block expansion needs instead to
**splice a whole block** ahead of the lowered body: run the block, bind its result at
the head, then continue. That is `Com.spliceCom c k : Com d Γ s` for `c : Com d Γ t`,
`k : Com d (t :: Γ) s` — the let-composition (monadic bind) of `Com`, with denotation
`(spliceCom c k).denote V = k.denote (V.extend (c.denote V))`. It reuses the
`Ctxt.Hom`/`Com.rename` renaming infrastructure of `MergeCom`; its correctness is the
de Bruijn substitution law, ported dialect-generically here.

## What is proved (dialect-generic, `0` sorries)

* `Com.spliceCom` + `Com.spliceCom_denote` — the block-splice primitive and its
  denotation law (from generic `Com.denote_rename`).
* `BlockLoweringData` — the block-expanding lowering data (`lowerExprBlock` returns a
  whole `Com d'` block, not one `Expr`), `blockLowerCom` (the descent recursion, splicing
  each op's block), and `blockFundamental` — per-op block squares
  (`BlockOpTransports`) lift to whole-program preservation (`blockLowerCom_denote`).
* `Validation` — a toy dialect where one source op expands to a **2-binding**
  target block, and the whole-program square pops out on a multi-binding program from
  the block leaf alone (the block analogue of `ComParametricityTransport.Validation`).

## Wiring to `FieldPipelineEmitBB` (the follow-on flip)

Instantiating this at `d = fieldDialect`, `d' = jasminDialect`, with `mapTy (fp P) =
reg 64`, `transTy = bbEnc`, and `lowerExprBlock` the Poseidon2 word blocks
(`Poseidon2WholePermCom.emitAdd`/`emitMul` + the `emitSubBB` block), the per-op block
square `BlockOpTransports` at an `fAdd`/`fMul`/`fSub` node is exactly
`FieldDescentBabyBear.bbAdd_realizes`/`bbMul_realizes`/`bbSub_realizes` composed with
the block's own `emit*_denote_ret`. `blockFundamental` then delivers the whole-perm
`fieldPermComAt → (poseidon2PermComOut ())` transport that `FieldPipelineEmitBB` currently
carries only as the named residual. See §"Remaining work" in the report.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt

universe u v

/-! ## 1. Dialect-generic de Bruijn substitution laws

`ComInline`/`ThirDialect` prove these for `jasminDialect` only; the block splice needs
them over an arbitrary target dialect, so we port the four laws generically. The proofs
are the same structural inductions. -/

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]

/-- Pullback of a `Valuation Γ'` along a context homomorphism `h : Γ → Γ'`. -/
def pullV : {Γ Γ' : Ctxt d} → Ctxt.Hom Γ Γ' → Ctxt.Valuation Γ' → Ctxt.Valuation Γ
  | [], _, _, _ => .nil
  | _ :: _, _, h, V =>
      .cons ((h Ctxt.Var.here).lookup V) (pullV (fun v => h (Ctxt.Var.there v)) V)

/-- Looking up a renamed variable equals looking up the original in the pullback. -/
theorem Var.lookup_rename {Γ Γ' : Ctxt d}
    (h : Ctxt.Hom Γ Γ') {t : d.Ty} (v : Ctxt.Var Γ t) (V : Ctxt.Valuation Γ') :
    (h v).lookup V = v.lookup (pullV h V) := by
  induction v with
  | here => rfl
  | @there Γ₀ t s w ih => simp only [pullV]; exact ih (fun v => h (.there v))

/-- Renaming an args-HVector then looking it up equals looking up the original against
    the pulled-back valuation. -/
theorem lookupArgs_renameVars {Γ Γ' : Ctxt d} (h : Ctxt.Hom Γ Γ') :
    {tys : List d.Ty} → (args : HVector (fun ty => Ctxt.Var Γ ty) tys) →
    (V : Ctxt.Valuation Γ') →
    Expr.lookupArgs (HVector.renameVars h args) V = Expr.lookupArgs args (pullV h V)
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, V => by
      show HVector.cons _ _ = HVector.cons _ _
      congr 1
      · exact Var.lookup_rename h v V
      · exact lookupArgs_renameVars h rest V

/-- Renaming an `Expr` and denoting equals denoting the original against the pullback. -/
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
    pullV (fun v => (g v).there) (HVector.cons x W) = pullV g W := by
  induction Γ with
  | nil => rfl
  | cons a Γ ih => simp only [pullV]; congr 1; exact ih (fun v => g (.there v))

/-- Pulling back along the identity hom is the identity. -/
theorem pullV_id {Γ : Ctxt d} (V : Ctxt.Valuation Γ) :
    pullV (fun v => v) V = V := by
  induction Γ with
  | nil => cases V; rfl
  | cons a Γ ih =>
      match V with
      | .cons x W =>
          show HVector.cons _ (pullV (fun v => ((fun u => u) v).there) (HVector.cons x W))
            = HVector.cons x W
          rw [pullV_there (fun v => v) x W, ih W]
          rfl

/-- Pulling back along `lift (weakenOne)` against `a :: b :: W` keeps head `a` and tail
    `W`, dropping the inserted middle binding `b`. -/
theorem pullV_lift_weakenOne {Γ : Ctxt d} {s s' : d.Ty}
    (a : ⟦s'⟧) (b : ⟦s⟧) (W : Ctxt.Valuation Γ) :
    pullV (Ctxt.Hom.lift (Ctxt.Hom.weakenOne Γ s)) (HVector.cons a (HVector.cons b W))
      = HVector.cons a W := by
  show HVector.cons a
      (pullV (fun v => Ctxt.Var.there (Ctxt.Var.there v)) (HVector.cons a (HVector.cons b W)))
    = HVector.cons a W
  rw [pullV_there (fun v => Ctxt.Var.there v) a (HVector.cons b W),
    pullV_there (fun v => v) b W, pullV_id]

/-- Renaming a `Com` and denoting equals denoting the original against the pullback. -/
theorem Com.denote_rename {Γ Γ' : Ctxt d} {t : d.Ty}
    (h : Ctxt.Hom Γ Γ') (c : Com d Γ t) (V : Ctxt.Valuation Γ') :
    (Com.rename h c).denote V = c.denote (pullV h V) := by
  induction c generalizing Γ' with
  | ret v => simp only [Com.rename, Com.denote]; exact Var.lookup_rename h v V
  | var e body ih =>
      simp only [Com.rename, Com.denote]
      rw [ih h.lift (Ctxt.Valuation.extend V ((e.rename h).denote V))]
      rw [Expr.denote_rename h e V]
      congr 1
      show HVector.cons (e.denote (pullV h V))
          (pullV (fun v => (h v).there) (HVector.cons (e.denote (pullV h V)) V))
        = HVector.cons (e.denote (pullV h V)) (pullV h V)
      rw [pullV_there h (e.denote (pullV h V)) V]

/-! ## 2. The block-splice primitive `Com.spliceCom`

Run block `c`, bind its result at the head, continue with `k`. This is the
let-composition (monadic bind) of `Com` — the operation `LoweringData.lowerCom`'s
single-`.var` arm lacks, and the whole reason block expansion is outside the structural
framework. -/

/-- Substitute the head variable of a context by `v`: the hom `t :: Γ → Γ` sending
    `.here ↦ v` and `.there w ↦ w`. -/
def substHeadHom {Γ : Ctxt d} {t : d.Ty} (v : Ctxt.Var Γ t) : Ctxt.Hom (t :: Γ) Γ :=
  fun w => match w with
    | .here => v
    | .there u => u

/-- The pullback along `substHeadHom v` prepends `v`'s value to `V`. -/
theorem pullV_substHeadHom {Γ : Ctxt d} {t : d.Ty}
    (v : Ctxt.Var Γ t) (V : Ctxt.Valuation Γ) :
    pullV (substHeadHom v) V = HVector.cons (v.lookup V) V := by
  show HVector.cons ((substHeadHom v Ctxt.Var.here).lookup V)
      (pullV (fun w => substHeadHom v (Ctxt.Var.there w)) V)
    = HVector.cons (v.lookup V) V
  have h1 : (substHeadHom v Ctxt.Var.here) = v := rfl
  rw [h1]
  congr 1
  exact pullV_id V

/-- **The block-splice.** `spliceCom c k` runs `c`, binds its return value at the head,
    then runs `k`. Structural recursion on `c`: at a `ret v` we substitute `v` for `k`'s
    head; at a `var e body` we keep the binding and recurse, weakening `k` past the fresh
    binding. This is the `Com` let-composition the block-expanding descent splices per
    op. -/
def spliceCom : {Γ : Ctxt d} → {t s : d.Ty} →
    Com d Γ t → Com d (t :: Γ) s → Com d Γ s
  | _, _, _, .ret v, k => Com.rename (substHeadHom v) k
  | _, _, _, .var (t := bs) e body, k =>
      .var e (spliceCom body (Com.rename (Ctxt.Hom.lift (Ctxt.Hom.weakenOne _ bs)) k))

/-- **Block-splice denotation law.** `(spliceCom c k).denote V = k.denote (V.extend
    (c.denote V))` — run `c`, bind its result, run `k`. The single equation the
    block-expanding descent needs at each op. -/
theorem spliceCom_denote : {Γ : Ctxt d} → {t s : d.Ty} →
    (c : Com d Γ t) → (k : Com d (t :: Γ) s) → (V : Ctxt.Valuation Γ) →
    (spliceCom c k).denote V = k.denote (Ctxt.Valuation.extend V (c.denote V))
  | _, _, _, .ret v, k, V => by
      show (Com.rename (substHeadHom v) k).denote V = _
      rw [Com.denote_rename, pullV_substHeadHom]
      rfl
  | _, _, _, .var (t := bs) e body, k, V => by
      show (Com.var e (spliceCom body
        (Com.rename (Ctxt.Hom.lift (Ctxt.Hom.weakenOne _ bs)) k))).denote V = _
      simp only [Com.denote]
      rw [spliceCom_denote body _ (Ctxt.Valuation.extend V (e.denote V))]
      rw [Com.denote_rename]
      -- pull the weakened `k` back over the double-extended valuation: it drops the
      -- inserted middle binding `e.denote V`, keeping the body value and `V`.
      congr 1
      exact pullV_lift_weakenOne (body.denote (Ctxt.Valuation.extend V (e.denote V)))
        (e.denote V) V

/-! ## 3. The block-expanding lowering data + descent recursion

`BlockLoweringData` is `LoweringData` with `lowerExpr` upgraded to `lowerExprBlock`: each
source op maps to a whole target `Com` **block** (returning the op's value), not a single
`Expr`. `blockLowerCom` splices each block ahead of the lowered body. -/

/-- The data of a block-expanding lowering from dialect `d` to dialect `d'`. Identical to
    `ComParametricityTransport.LoweringData` except `lowerExprBlock` returns a whole
    target BLOCK (`Com d'`), the one field that lifts the single-op restriction. -/
structure BlockLoweringData (d d' : Dialect) [DialectSignature d] [DialectSignature d']
    where
  /-- Type map. -/
  mapTy : d.Ty → d'.Ty
  /-- Context map. -/
  mapCtx : Ctxt d → Ctxt d'
  /-- `cons`-compatibility of the context map. -/
  mapCtx_cons : ∀ (t : d.Ty) (Γ : Ctxt d), mapCtx (t :: Γ) = mapTy t :: mapCtx Γ
  /-- Variable transport. -/
  mapVar : ∀ {Γ : Ctxt d} {t : d.Ty}, Ctxt.Var Γ t → Ctxt.Var (mapCtx Γ) (mapTy t)
  /-- **Per-op block lowering:** each source `Expr` becomes a whole target `Com` BLOCK
      returning a value of the mapped return type. (The block expansion — one
      source op, several target bindings.) -/
  lowerExprBlock : ∀ {Γ : Ctxt d} {t : d.Ty},
    Expr d Γ t → Com d' (mapCtx Γ) (mapTy t)

namespace BlockLoweringData

variable {d d' : Dialect} [DialectSignature d] [DialectSignature d']

/-- **The block-expanding descent recursion.** A return becomes the mapped variable; a
    let-binding splices the op's target block ahead of the lowered body. This is the
    block analogue of `LoweringData.lowerCom`, with `spliceCom` in place of the single
    `.var`. -/
def blockLowerCom (L : BlockLoweringData d d') :
    {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → Com d' (L.mapCtx Γ) (L.mapTy t)
  | _, _, .ret v => .ret (L.mapVar v)
  | Γ, _, .var (t := bs) e body =>
      spliceCom (L.lowerExprBlock e) (L.mapCtx_cons bs Γ ▸ L.blockLowerCom body)

end BlockLoweringData

/-! ## 4. The whole-program transport square, from per-op block squares -/

variable {d' : Dialect} [TyDenote d'.Ty] [DialectSignature d'] [DialectDenote d']

/-- Value transport carried by a block lowering. -/
abbrev TransTy (L : BlockLoweringData d d') := ∀ {t : d.Ty}, ⟦t⟧ → ⟦L.mapTy t⟧

/-- Valuation transport carried by a block lowering. -/
abbrev MapVal (L : BlockLoweringData d d') :=
  ∀ {Γ : Ctxt d}, Ctxt.Valuation Γ → Ctxt.Valuation (L.mapCtx Γ)

/-- Variable-transport leaf coherence. -/
def VarTransports (L : BlockLoweringData d d') (transTy : TransTy L) (mapVal : MapVal L) :
    Prop :=
  ∀ {Γ : Ctxt d} {t : d.Ty} (v : Ctxt.Var Γ t) (V : Ctxt.Valuation Γ),
    (L.mapVar v).lookup (mapVal V) = transTy (v.lookup V)

/-- **Per-op BLOCK transport (the only op-specific obligation).** Each source op's target
    BLOCK denotes (under the mapped valuation) to the transport of the op's denotation.
    For the Poseidon2 field descent this is exactly `bbAdd_realizes`/`bbMul_realizes`/
    `bbSub_realizes` composed with the block's `emit*_denote_ret`. -/
def BlockOpTransports (L : BlockLoweringData d d')
    (transTy : TransTy L) (mapVal : MapVal L) : Prop :=
  ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t) (V : Ctxt.Valuation Γ),
    (L.lowerExprBlock e).denote (mapVal V) = transTy (e.denote V)

/-- Binding-threading coherence. -/
def MapValExtends (L : BlockLoweringData d d')
    (transTy : TransTy L) (mapVal : MapVal L) : Prop :=
  ∀ {Γ : Ctxt d} {t : d.Ty} (V : Ctxt.Valuation Γ) (x : ⟦t⟧),
    mapVal (Ctxt.Valuation.extend V x)
      = (L.mapCtx_cons t Γ ▸ Ctxt.Valuation.extend (mapVal V) (transTy x))

/-- **Fundamental lemma of block-expanding descent.** From the variable leaf, the per-op
    BLOCK square, and binding-threading, the whole descended program denotes to the
    transport of the source denotation — for **every** program, with no per-program
    induction beyond the `Com` skeleton. The block analogue of
    `ComParametricityTransport.fundamental`; the `.var` case uses `spliceCom_denote` +
    the block square in place of the single-`Expr` op square. -/
theorem blockFundamental
    (L : BlockLoweringData d d') (transTy : TransTy L) (mapVal : MapVal L)
    (hVar : VarTransports L transTy mapVal)
    (hOp : BlockOpTransports L transTy mapVal)
    (hExt : MapValExtends L transTy mapVal) :
    ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (V : Ctxt.Valuation Γ),
      (L.blockLowerCom c).denote (mapVal V) = transTy (c.denote V)
  | _, _, .ret v, V => by
      show (Com.ret (L.mapVar v)).denote (mapVal V) = _
      simpa [Com.denote] using hVar v V
  | Γ, _, .var (t := bs) e body, V => by
      show (spliceCom (L.lowerExprBlock e)
        (L.mapCtx_cons bs Γ ▸ L.blockLowerCom body)).denote (mapVal V) = _
      -- Splice-denote: run the block, bind its result, run the (cast) lowered body.
      rw [spliceCom_denote]
      -- The spliced head value is the block's denote = transport of `e.denote V`.
      have hleaf := hOp e V
      have IH := blockFundamental L transTy mapVal hVar hOp hExt body
        (Ctxt.Valuation.extend V (e.denote V))
      have hext := hExt V (e.denote V)
      rw [hleaf]
      -- Close the `mapCtx_cons` cast against the IH + binding-threading, exactly as
      -- `ComParametricityTransport.fundamental` closes its structural `var` case.
      grind [BlockLoweringData.blockLowerCom, Com.denote]

/-! ## 5. Validation — a one-op→2-block expansion, whole program from the leaf

To witness the machinery is non-vacuous (leaf in, whole program out) we instantiate at a
toy dialect where **one** source op expands to a **2-binding** target block. This is the
block analogue of `ComParametricityTransport.Validation` (which used a single-op identity
lowering); here the lowering emits more bindings than it consumes, exercising
`spliceCom`. -/

namespace Validation

/-- A one-type, one-op toy dialect: type `()` denoting `Nat`, a binary op `dup x y = x`.
    Same as `ComParametricityTransport.Validation.toyDialect`; enough to host a
    multi-binding block. -/
def toyDialect : Dialect where
  Op := Unit
  Ty := Unit

instance : TyDenote toyDialect.Ty where denote := fun _ => Nat
instance : DialectSignature toyDialect where
  sig := fun _ => [(), ()]
  ret := fun _ => ()
instance : DialectDenote toyDialect where denote := fun _ args => args.head

/-- The `dup` op applied to two variables. -/
def dupExpr {Γ : Ctxt toyDialect} (x y : Ctxt.Var Γ ()) : Expr toyDialect Γ () :=
  ⟨(), rfl, .cons x (.cons y .nil)⟩

/-- **The block-expanding self-lowering.** `mapTy`/`mapCtx`/`mapVar` are identities, but
    `lowerExprBlock` expands one `dup x y` into a **2-binding** block
    `let a = dup x y; let b = dup a y; ret b` (both denote `x`). This is the crux the
    single-op `LoweringData` cannot express. -/
def dupBlockLowering : BlockLoweringData toyDialect toyDialect where
  mapTy := id
  mapCtx := id
  mapCtx_cons := fun _ _ => rfl
  mapVar := fun v => v
  lowerExprBlock := fun {_ _} e =>
    -- read the two source args, then emit a 2-op block over them.
    match e with
    | ⟨(), _, .cons x (.cons y .nil)⟩ =>
        .var (dupExpr x y)
          (.var (dupExpr .here (.there y))
            (.ret .here))

/-- Identity value/valuation transports. -/
def idTransTy : TransTy dupBlockLowering := fun x => x
def idMapVal : MapVal dupBlockLowering := fun V => V

/-- Variable leaf: `rfl`. -/
theorem dupVarTransports : VarTransports dupBlockLowering idTransTy idMapVal :=
  fun _ _ => rfl

/-- **The per-op BLOCK leaf.** The 2-binding block for `dup x y` denotes to `x`, which is
    exactly `dup x y = x` (the source op's denotation). The block square — the
    obligation `blockFundamental` consumes, discharged here by evaluation. -/
theorem dupBlockOpTransports : BlockOpTransports dupBlockLowering idTransTy idMapVal := by
  intro Γ t e V
  rcases e with ⟨op, h, args⟩
  match op, args with
  | (), .cons x (.cons y .nil) =>
      -- block denote = head of `dup (dup x y) y` args = `dup x y` = `x.lookup V`.
      rfl

/-- Binding-threading: `rfl` for identity transport. -/
theorem dupMapValExtends : MapValExtends dupBlockLowering idTransTy idMapVal :=
  fun _ _ => rfl

/-- **Whole-program block-descent square, from the block leaf alone.** For *every* toy
    program, the block-expanded lowering (each `dup` → its 2-op block) preserves
    denotation — obtained from the three leaves by `blockFundamental`, no per-program
    induction. -/
theorem dupBlockLowerCom_denote {Γ : Ctxt toyDialect} {t : toyDialect.Ty}
    (c : Com toyDialect Γ t) (V : Ctxt.Valuation Γ) :
    (dupBlockLowering.blockLowerCom c).denote (idMapVal V) = idTransTy (c.denote V) :=
  blockFundamental dupBlockLowering idTransTy idMapVal
    dupVarTransports dupBlockOpTransports dupMapValExtends c V

/-- A concrete two-binding source program `let a = dup _ _; let b = dup a _; ret b`. -/
def sampleProg : Com toyDialect [()] () :=
  .var (dupExpr .here .here)
    (.var (dupExpr .here (.there .here))
      (.ret .here))

/-- **The whole-program square on the concrete program, block leaf in, program out.**
    Each source `dup` becomes its 2-op block, so the 2-binding source program lowers to a
    4-binding target program, and preservation still pops out of `blockFundamental` with
    no program-specific work. -/
theorem sampleProg_blockDescends (V : Ctxt.Valuation ([()] : Ctxt toyDialect)) :
    (dupBlockLowering.blockLowerCom sampleProg).denote (idMapVal V)
      = idTransTy (sampleProg.denote V) :=
  dupBlockLowerCom_denote sampleProg V

end Validation

end CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent
