/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent

/-!
# Coverage-gated, continuation-passing block lowering

`FieldDialectBlockDescent.BlockLoweringData` lowers a `Com d` program to a `Com d'`
program by expanding each source op into a target block, and `blockLowerCom`
splices each block ahead of the lowered body with `spliceCom`. Two properties of
that recursion are addressed here, for arbitrary source and target dialects and an
arbitrary type map `mapTy`.

* Coverage. `blockFundamental` requires the block square for every expression of
  the source dialect. `blockFundamental_on` requires it only for expressions
  satisfying a predicate `Good`, and concludes preservation for programs whose
  every let-bound expression is `Good` (`CoveredCom Good`).
* Cost. `spliceCom blk k` renames the continuation `k` once per binding of `blk`,
  so `blockLowerCom` is quadratic in program size. `blockLowerComK` threads a
  renaming accumulator instead: each source block is renamed once into the target
  context, and `spliceComK` applies the continuation once, at the block's return.
  Every binding is visited a bounded number of times.

The context map is only propositionally `cons`-compatible (`mapCtx_cons`), so the
renaming handed to the lowered body is the head-extension `consHom` precomposed
with the variable cast `castHom (L.mapCtx_cons u Γ)`.

## Main definitions

* `CoveredCom Good c`: every let-bound expression of `c` satisfies `Good`.
* `spliceComK`: block splice with the continuation applied once.
* `BlockLoweringData.blockLowerComR`: the lowering rendered over a target context
  through a renaming accumulator.
* `BlockLoweringData.blockLowerComK`: `blockLowerComR` at the identity renaming.

## Main results

* `coveredCom_rename`, `coveredCom_spliceCom`: renaming and splicing keep the operations
  of a block.
* `blockFundamental_on`: variable, `Good`-gated block and binding-threading squares
  give whole-program preservation for every `Good`-covered program.
* `spliceComK_denote`: the denotation of `spliceComK`.
* `BlockLoweringData.blockLowerComK_denote`: `blockLowerComK c` and
  `blockLowerCom c` denote the same function.
* `BlockLoweringData.blockLowerComK_denote_on`: the transport square for
  `blockLowerComK` on covered programs.

The instance at `derivedDialect → fieldDialect` is `BlockLoweringCPSDerivedToField`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent

/-! ## 1. Renaming and valuation lemmas -/

section Renaming

variable {d : Dialect} [DialectSignature d]

/-- Extend a renaming `f : Γ → Δ` to `a :: Γ → Δ` by sending the head to `x`. -/
def consHom {Γ Δ : Ctxt d} {a : d.Ty} (f : Ctxt.Hom Γ Δ) (x : Var Δ a) :
    ∀ {t : d.Ty}, Var (a :: Γ) t → Var Δ t
  | _, .here => x
  | _, .there w => f w

/-- The renaming that transports a variable along an equality of contexts. -/
def castHom {Γ₁ Γ₂ : Ctxt d} (h : Γ₁ = Γ₂) : Ctxt.Hom Γ₁ Γ₂ := fun v => h ▸ v

variable [TyDenote d.Ty] [DialectDenote d]

/-- Looking up `v` in the pullback along `f` is looking up `f v`. -/
theorem lookup_pullV {Γ Γ' : Ctxt d} (f : Ctxt.Hom Γ Γ') {t : d.Ty} (v : Var Γ t)
    (V : Valuation Γ') : v.lookup (pullV f V) = (f v).lookup V :=
  (Var.lookup_rename f v V).symm

omit [DialectSignature d] [DialectDenote d] in
/-- Two valuations of the same context that agree on every variable are equal. -/
theorem valuation_ext : {Γ : Ctxt d} → (V₁ V₂ : Valuation Γ) →
    (∀ {t : d.Ty} (v : Var Γ t), v.lookup V₁ = v.lookup V₂) → V₁ = V₂
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons x V₁, .cons y V₂, h => by
      have hx : x = y := h .here
      have hV : V₁ = V₂ := valuation_ext V₁ V₂ (fun v => h (.there v))
      subst hx hV
      rfl

/-- Denoting a program cast along a context equality is denoting the original
    against the pullback along `castHom`. -/
theorem Com.denote_cast {Γ₁ Γ₂ : Ctxt d} (h : Γ₁ = Γ₂) {t : d.Ty} (c : Com d Γ₁ t)
    (V : Valuation Γ₂) : (h ▸ c).denote V = c.denote (pullV (castHom h) V) := by
  subst h
  exact congrArg c.denote (pullV_id V).symm

end Renaming

/-! ## 2. Coverage and the gated fundamental lemma -/

section Coverage

variable {d : Dialect} [DialectSignature d]

/-- A program is `Good`-covered when every let-bound expression satisfies `Good`. -/
def CoveredCom (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop) :
    {Γ : Ctxt d} → {t : d.Ty} → Com d Γ t → Prop
  | _, _, .ret _ => True
  | _, _, .var e body => Good e ∧ CoveredCom Good body

/-- Under a predicate that holds of every expression, every program is covered. -/
theorem coveredCom_of_forall (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hG : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e) :
    ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t), CoveredCom Good c
  | _, _, .ret _ => trivial
  | _, _, .var e body => ⟨hG e, coveredCom_of_forall Good hG body⟩

/-- A renaming keeps the operations of a block. -/
theorem coveredCom_rename (Q : d.Op → Bool) :
    {Γ Γ' : Ctxt d} → {t : d.Ty} → (h : Ctxt.Hom Γ Γ') → (c : Com d Γ t) →
      CoveredCom (fun e => Q e.op = true) c →
        CoveredCom (fun e => Q e.op = true) (Com.rename h c)
  | _, _, _, _, .ret _, _ => trivial
  | _, _, _, h, .var _ body, hc => ⟨hc.1, coveredCom_rename Q h.lift body hc.2⟩

/-- **A splice of blocks has the operations of both.** -/
theorem coveredCom_spliceCom (Q : d.Op → Bool) :
    ∀ {Γ : Ctxt d} {t s : d.Ty} (c : Com d Γ t) (k : Com d (t :: Γ) s),
      CoveredCom (fun e => Q e.op = true) c → CoveredCom (fun e => Q e.op = true) k →
        CoveredCom (fun e => Q e.op = true) (spliceCom c k)
  | _, _, _, .ret _, k, _, hk => coveredCom_rename Q _ k hk
  | _, _, _, .var _ body, k, hc, hk =>
      ⟨hc.1, coveredCom_spliceCom Q body _ hc.2 (coveredCom_rename Q _ k hk)⟩

variable [TyDenote d.Ty] [DialectDenote d]
variable {d' : Dialect} [TyDenote d'.Ty] [DialectSignature d'] [DialectDenote d']

/-- **Coverage-gated fundamental lemma of block-expanding descent.** From the
    variable square, the block square for `Good` expressions, and binding-threading,
    every `Good`-covered program lowers by `blockLowerCom` to a program denoting the
    transport of its denotation. -/
theorem blockFundamental_on
    (L : BlockLoweringData d d') (transTy : TransTy L) (mapVal : MapVal L)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hVar : VarTransports L transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e →
      ∀ V : Valuation Γ, (L.lowerExprBlock e).denote (mapVal V) = transTy (e.denote V))
    (hExt : MapValExtends L transTy mapVal) :
    ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t), CoveredCom Good c →
      ∀ V : Valuation Γ, (L.blockLowerCom c).denote (mapVal V) = transTy (c.denote V)
  | _, _, .ret v, _, V => by
      show (Com.ret (L.mapVar v)).denote (mapVal V) = _
      simpa [Com.denote] using hVar v V
  | Γ, _, .var (t := bs) e body, hcov, V => by
      obtain ⟨hg, hbody⟩ := hcov
      show (spliceCom (L.lowerExprBlock e)
        (L.mapCtx_cons bs Γ ▸ L.blockLowerCom body)).denote (mapVal V) = _
      rw [spliceCom_denote, hBlk e hg V]
      have IH := blockFundamental_on L transTy mapVal Good hVar hBlk hExt body hbody
        (Valuation.extend V (e.denote V))
      have hext := hExt V (e.denote V)
      grind [BlockLoweringData.blockLowerCom, Com.denote]

end Coverage

/-! ## 3. The continuation-passing block splice -/

section SpliceK

variable {d : Dialect} [DialectSignature d]

/-- **Block splice with a once-applied continuation.** `spliceComK blk k` keeps the
    bindings of `blk` and, at its return variable `res`, emits `k ren res`, where
    `ren` renames the context of `blk` into the extended context. The continuation
    is applied exactly once, so the cost is linear in `blk` plus the cost of
    `k`. -/
def spliceComK : {Γ : Ctxt d} → {a b : d.Ty} →
    Com d Γ a → ({Δ : Ctxt d} → Ctxt.Hom Γ Δ → Var Δ a → Com d Δ b) → Com d Γ b
  | _, _, _, .ret v, k => k (fun x => x) v
  | _, _, _, .var e blk, k =>
      .var e (spliceComK blk (fun ren res => k (fun x => ren (.there x)) res))

variable [TyDenote d.Ty] [DialectDenote d]

/-- **Denotation of `spliceComK`.** If `k ren res` denotes `G` whenever `ren`
    preserves lookups back to `W` and `res` holds the block's value, the spliced
    program denotes `G`. -/
theorem spliceComK_denote : {Γ : Ctxt d} → {a b : d.Ty} →
    (blk : Com d Γ a) →
    (k : {Δ : Ctxt d} → Ctxt.Hom Γ Δ → Var Δ a → Com d Δ b) →
    (W : Valuation Γ) → (G : ⟦b⟧) →
    (∀ {Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ) (res : Var Δ a) (W' : Valuation Δ),
        (∀ {s : d.Ty} (v : Var Γ s), (ren v).lookup W' = v.lookup W) →
        res.lookup W' = blk.denote W →
        (k ren res).denote W' = G) →
    (spliceComK blk k).denote W = G
  | _, _, _, .ret v, k, W, G, hk => by
      show (k (fun x => x) v).denote W = G
      exact hk (fun x => x) v W (fun _ => rfl) rfl
  | _, _, _, .var e blk, k, W, G, hk => by
      show (spliceComK blk (fun ren res => k (fun x => ren (.there x)) res)).denote
          (Valuation.extend W (e.denote W)) = G
      exact spliceComK_denote blk _ (Valuation.extend W (e.denote W)) G
        (fun ren res W' h1 h2 => hk (fun x => ren (.there x)) res W'
          (fun v => h1 (.there v)) h2)

end SpliceK

end CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS

/-! ## 4. The renaming-accumulator lowering -/

namespace CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent.BlockLoweringData

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS

section Defs

variable {d d' : Dialect} [DialectSignature d] [DialectSignature d']

/-- The renaming handed to the lowered body of a let-binding of type `u`: the head
    of `L.mapCtx (u :: Γ)` goes to the block's result `res`, the tail through `ren`
    and then `ren'`. -/
def bodyHom (L : BlockLoweringData d d') {Γ : Ctxt d} {u : d.Ty} {Δ Δ' : Ctxt d'}
    (ren : Ctxt.Hom (L.mapCtx Γ) Δ) (ren' : Ctxt.Hom Δ Δ') (res : Var Δ' (L.mapTy u)) :
    Ctxt.Hom (L.mapCtx (u :: Γ)) Δ' :=
  fun v => consHom (fun w => ren' (ren w)) res (castHom (L.mapCtx_cons u Γ) v)

/-- **The renaming-accumulator lowering.** `blockLowerComR ren c` is
    `blockLowerCom c` renamed along `ren` into the target context `Δ`. Each source
    block is renamed once and spliced with `spliceComK`, whose continuation lowers
    the body under `bodyHom`. -/
def blockLowerComR (L : BlockLoweringData d d') :
    {Γ : Ctxt d} → {t : d.Ty} → {Δ : Ctxt d'} →
    Ctxt.Hom (L.mapCtx Γ) Δ → Com d Γ t → Com d' Δ (L.mapTy t)
  | _, _, _, ren, .ret v => .ret (ren (L.mapVar v))
  | _, _, _, ren, .var e body =>
      spliceComK (Com.rename ren (L.lowerExprBlock e))
        (fun ren' res => L.blockLowerComR (L.bodyHom ren ren' res) body)

/-- **The linear-time block lowering.** `blockLowerComR` at the identity renaming. -/
def blockLowerComK (L : BlockLoweringData d d') {Γ : Ctxt d} {t : d.Ty}
    (c : Com d Γ t) : Com d' (L.mapCtx Γ) (L.mapTy t) :=
  L.blockLowerComR (fun v => v) c

end Defs

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
variable {d' : Dialect} [TyDenote d'.Ty] [DialectSignature d'] [DialectDenote d']

omit [TyDenote d.Ty] [DialectDenote d] in
/-- **`blockLowerComR` denotes as the renamed `blockLowerCom`.** -/
theorem blockLowerComR_denote (L : BlockLoweringData d d') :
    ∀ {Γ : Ctxt d} {t : d.Ty} {Δ : Ctxt d'} (ren : Ctxt.Hom (L.mapCtx Γ) Δ)
      (c : Com d Γ t) (W : Valuation Δ),
      (L.blockLowerComR ren c).denote W = (L.blockLowerCom c).denote (pullV ren W)
  | _, _, _, ren, .ret v, W => by
      show (ren (L.mapVar v)).lookup W = (L.mapVar v).lookup (pullV ren W)
      exact Var.lookup_rename ren _ W
  | Γ, _, _, ren, .var (t := u) e body, W => by
      show (spliceComK (Com.rename ren (L.lowerExprBlock e))
          (fun ren' res => L.blockLowerComR (L.bodyHom ren ren' res) body)).denote W
        = (spliceCom (L.lowerExprBlock e)
            (L.mapCtx_cons u Γ ▸ L.blockLowerCom body)).denote (pullV ren W)
      rw [spliceCom_denote, Com.denote_cast]
      refine spliceComK_denote _ _ W _ (fun ren' res W' h1 h2 => ?_)
      rw [blockLowerComR_denote L (L.bodyHom ren ren' res) body W']
      refine congrArg _ (valuation_ext _ _ (fun v => ?_))
      rw [lookup_pullV, lookup_pullV]
      show (consHom (fun w => ren' (ren w)) res (castHom (L.mapCtx_cons u Γ) v)).lookup W'
        = (castHom (L.mapCtx_cons u Γ) v).lookup
            (Valuation.extend (pullV ren W) ((L.lowerExprBlock e).denote (pullV ren W)))
      generalize castHom (L.mapCtx_cons u Γ) v = w
      cases w with
      | here => exact h2.trans (Com.denote_rename ren _ W)
      | there w => exact (h1 (ren w)).trans (lookup_pullV ren w W).symm

omit [TyDenote d.Ty] [DialectDenote d] in
/-- **`blockLowerComK` and `blockLowerCom` denote the same function.** -/
theorem blockLowerComK_denote (L : BlockLoweringData d d') {Γ : Ctxt d} {t : d.Ty}
    (c : Com d Γ t) (W : Valuation (L.mapCtx Γ)) :
    (L.blockLowerComK c).denote W = (L.blockLowerCom c).denote W :=
  (L.blockLowerComR_denote (fun v => v) c W).trans (congrArg _ (pullV_id W))

/-- **Transport square for `blockLowerComK` on covered programs.** -/
theorem blockLowerComK_denote_on
    (L : BlockLoweringData d d') (transTy : TransTy L) (mapVal : MapVal L)
    (Good : ∀ {Γ : Ctxt d} {t : d.Ty}, Expr d Γ t → Prop)
    (hVar : VarTransports L transTy mapVal)
    (hBlk : ∀ {Γ : Ctxt d} {t : d.Ty} (e : Expr d Γ t), Good e →
      ∀ V : Valuation Γ, (L.lowerExprBlock e).denote (mapVal V) = transTy (e.denote V))
    (hExt : MapValExtends L transTy mapVal)
    {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t) (hc : CoveredCom Good c) (V : Valuation Γ) :
    (L.blockLowerComK c).denote (mapVal V) = transTy (c.denote V) :=
  (L.blockLowerComK_denote c (mapVal V)).trans
    (blockFundamental_on L transTy mapVal Good hVar hBlk hExt c hc V)

end CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent.BlockLoweringData
