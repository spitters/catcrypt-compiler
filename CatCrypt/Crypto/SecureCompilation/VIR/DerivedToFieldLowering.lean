/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDerivedOps
public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent

/-!
# `derivedDialect → fieldDialect`

`derivedDialect` gives prime-ir's `field.double` / `field.square` / `field.powui`
first-class ops. Its single value type `fp p` denotes `ZMod p`, the value
`fieldDialect`'s `fp p` also denotes, and each derived op is a fixed schedule of
`fAdd` / `fMul` / `fConst` / `fCopy`. This file lowers whole `Com derivedDialect`
programs to `Com fieldDialect`, which reaches bytes through
`fieldComToJasmin`.

`field.powui` carries a static exponent and expands to a multiplication chain, so
one source op becomes several target bindings. That is what
`FieldDialectBlockDescent.BlockLoweringData` provides: `lowerExprBlock` returns a
whole target block and `blockLowerCom` splices it ahead of the lowered body.
Whole-program denotation preservation follows from three leaf obligations via
`blockFundamental`, with no induction over programs.

## Main definitions

* `mapTy` / `mapCtx` / `mapVar`: the type, context and de Bruijn index transports.
* `doubleBlock` / `squareBlock` / `powBlock`: the target block each derived op
  expands to.
* `lowering`: the `BlockLoweringData derivedDialect fieldDialect`.
* `lowerDerivedToField`: the whole-program map `Com derivedDialect → Com fieldDialect`.

## Main results

* `powBlock_denote`: the multiplication chain for a static exponent `k` denotes
  `a ^ k`.
* `blockOpTransports`: each derived op's target block denotes to the op's own
  denotation — the only op-specific obligation.
* `lowerDerivedToField_denote`: the lowering preserves denotation for every
  program.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.DerivedToField

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDerivedOps
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent

/-! ## 1. Type, context and variable maps -/

/-- Both dialects' `fp p` denotes `ZMod p`, so the type map renames the tag. -/
@[reducible] def mapTy : DerivedTy → FieldTy
  | .fp p => .fp p

/-- Context map: `mapTy` pointwise. -/
@[reducible] def mapCtx (Γ : Ctxt derivedDialect) : Ctxt fieldDialect := Γ.map mapTy

/-- `List.map` is definitionally `cons`-compatible. -/
theorem mapCtx_cons (t : DerivedTy) (Γ : Ctxt derivedDialect) :
    mapCtx (t :: Γ) = mapTy t :: mapCtx Γ := rfl

/-- de Bruijn index transport along `mapTy`. -/
def mapVar {Γ : Ctxt derivedDialect} {t : DerivedTy} :
    Ctxt.Var Γ t → Ctxt.Var (d := fieldDialect) (mapCtx Γ) (mapTy t)
  | .here => .here
  | .there v => .there (mapVar v)

/-! ## 2. The target blocks and what they denote

Each block is a named `Com fieldDialect` with its denotation stated at `FieldTy`,
where the value type is `ZMod p` outright. Stating them here rather than inline in
the lowering keeps the op leaves in §5 to a rewrite: the goal's left-hand side is
literally `(block …).denote (mapVal V)`, which these lemmas match. -/

/-- `fieldDouble a` as a field block: one `fAdd` of `a` with itself. -/
def doubleBlock (p : Nat) {Γ : Ctxt fieldDialect} (a : Ctxt.Var Γ (FieldTy.fp p)) :
    Com fieldDialect Γ (FieldTy.fp p) :=
  .var ⟨.fAdd p, rfl, .cons a (.cons a .nil)⟩ (.ret .here)

/-- `fieldSquare a` as a field block: one `fMul` of `a` with itself. -/
def squareBlock (p : Nat) {Γ : Ctxt fieldDialect} (a : Ctxt.Var Γ (FieldTy.fp p)) :
    Com fieldDialect Γ (FieldTy.fp p) :=
  .var ⟨.fMul p, rfl, .cons a (.cons a .nil)⟩ (.ret .here)

/-- The value a field variable reads, named at `ZMod p`.

`⟦FieldTy.fp p⟧` is `ZMod p` up to unfolding, which unification sees but instance
search does not: writing `a.lookup V + a.lookup V` fails to find `HAdd
⟦FieldTy.fp p⟧ ⟦FieldTy.fp p⟧ _`. Fixing the type here once lets the block
denotations below be stated as ordinary field arithmetic. -/
def fval {Γ : Ctxt fieldDialect} {p : Nat} (a : Ctxt.Var Γ (FieldTy.fp p))
    (V : Ctxt.Valuation Γ) : ZMod p := a.lookup V

/-- The double block denotes `a + a`. -/
theorem doubleBlock_denote (p : Nat) {Γ : Ctxt fieldDialect}
    (a : Ctxt.Var Γ (FieldTy.fp p)) (V : Ctxt.Valuation Γ) :
    (doubleBlock p a).denote V = fval a V + fval a V := rfl

/-- The square block denotes `a * a`. -/
theorem squareBlock_denote (p : Nat) {Γ : Ctxt fieldDialect}
    (a : Ctxt.Var Γ (FieldTy.fp p)) (V : Ctxt.Valuation Γ) :
    (squareBlock p a).denote V = fval a V * fval a V := rfl

/-! ### The fixed-exponent multiplication chain -/

/-- `a ^ k` as a `fieldDialect` block. `k = 0` is the constant `1`, `k = 1` copies
    `a`, and each further step multiplies the running power by `a`. The exponent is
    a static op parameter, so this is a fixed schedule, not a secret-exponent
    loop. -/
def powBlock (p : Nat) : (k : Nat) → {Γ : Ctxt fieldDialect} →
    Ctxt.Var Γ (FieldTy.fp p) → Com fieldDialect Γ (FieldTy.fp p)
  | 0, _, _ => .var ⟨.fConst p 1, rfl, .nil⟩ (.ret .here)
  | 1, _, a => .var ⟨.fCopy p, rfl, .cons a .nil⟩ (.ret .here)
  | (k + 2), _, a =>
      spliceCom (powBlock p (k + 1) a)
        (.var ⟨.fMul p, rfl, .cons .here (.cons (.there a) .nil)⟩ (.ret .here))

/-- The chain computes the power: `powBlock p k a` denotes `a ^ k`. -/
theorem powBlock_denote (p : Nat) : (k : Nat) → {Γ : Ctxt fieldDialect} →
    (a : Ctxt.Var Γ (FieldTy.fp p)) → (V : Ctxt.Valuation Γ) →
    (powBlock p k a).denote V = (fval a V) ^ k
  | 0, _, _, _ => by rw [pow_zero]; rfl
  | 1, _, _, _ => by rw [pow_one]; rfl
  | (k + 2), _, a, V => by
      show (spliceCom (powBlock p (k + 1) a) _).denote V = _
      rw [spliceCom_denote]
      simp only [Com.denote, Expr.denote]
      rw [powBlock_denote p (k + 1) a V]
      -- The final binding reads the running power and `a`, so the goal is
      -- definitionally the product; only the exponent law is left.
      show fval a V ^ (k + 1) * fval a V = fval a V ^ (k + 2)
      exact (pow_succ (fval a V) (k + 1)).symm

/-! ## 3. The block lowering -/

/-- The block-expanding lowering. `fieldDouble a` becomes `fAdd a a`,
    `fieldSquare a` becomes `fMul a a`, and `fieldPow k a` becomes the `k`-step
    multiplication chain. -/
def lowering : BlockLoweringData derivedDialect fieldDialect where
  mapTy := mapTy
  mapCtx := mapCtx
  mapCtx_cons := mapCtx_cons
  mapVar := mapVar
  lowerExprBlock := fun {_ _} e =>
    match e with
    | ⟨.fieldDouble p, h, .cons a .nil⟩ =>
        congrArg mapTy h ▸ doubleBlock p (mapVar a)
    | ⟨.fieldSquare p, h, .cons a .nil⟩ =>
        congrArg mapTy h ▸ squareBlock p (mapVar a)
    | ⟨.fieldPow p k, h, .cons a .nil⟩ =>
        congrArg mapTy h ▸ powBlock p k (mapVar a)

/-! ## 4. The value and valuation transports -/

/-- Value transport. `⟦DerivedTy.fp p⟧` and `⟦FieldTy.fp p⟧` are both `ZMod p`, so
    the transport is the identity once the tag is matched. -/
def transTy : TransTy lowering := fun {t} =>
  match t with
  | .fp _ => id

/-- Valuation transport, by recursion on the context. -/
def mapValAux : (Γ : Ctxt derivedDialect) → Ctxt.Valuation Γ →
    Ctxt.Valuation (lowering.mapCtx Γ)
  | [], _ => .nil
  | (.fp _ :: _), .cons x V => .cons x (mapValAux _ V)

/-- Valuation transport as the framework's `MapVal`. -/
def mapVal : MapVal lowering := fun {Γ} V => mapValAux Γ V

/-! ## 5. The three leaf obligations -/

/-- A transported index reads the transported valuation to the same value. Stated
    at the bare `mapVar` / `mapVal`, which is the shape the op leaves below rewrite
    with; `varTransports` is this lemma at the framework's field projections. -/
theorem mapVar_lookup {Γ : Ctxt derivedDialect} {p : Nat} :
    (a : Ctxt.Var Γ (DerivedTy.fp p)) → (V : Ctxt.Valuation Γ) →
    fval (mapVar a) (mapVal V) = a.lookup V
  | .here, V => by cases V; rfl
  | .there (t := s) w, V => by
      cases s
      cases V with
      | cons _ V₀ => exact mapVar_lookup w V₀

/-- Variable leaf: a transported index reads the transported valuation. -/
theorem varTransports : VarTransports lowering transTy mapVal := by
  intro Γ t v V
  cases t
  exact mapVar_lookup v V

/-- Binding-threading: extending then transporting is transporting then extending. -/
theorem mapValExtends : MapValExtends lowering transTy mapVal := by
  intro Γ t V x
  cases t
  rfl

/-- **The per-op block leaf.** Each derived op's target block denotes to the op's
    own denotation: `fAdd a a = a + a` is `fieldDoubleF`, `fMul a a = a * a` is
    `fieldSquareF`, and the chain is `a ^ k`, which is `fieldPowF`. -/
theorem blockOpTransports : BlockOpTransports lowering transTy mapVal := by
  intro Γ t e V
  rcases e with ⟨op, h, args⟩
  cases op with
  | fieldDouble p =>
      cases h
      match args with
      | .cons a .nil =>
          simp only [lowering]
          rw [doubleBlock_denote p (mapVar a) (mapVal V), mapVar_lookup a V]
          rfl
  | fieldSquare p =>
      cases h
      match args with
      | .cons a .nil =>
          simp only [lowering]
          rw [squareBlock_denote p (mapVar a) (mapVal V), mapVar_lookup a V]
          rfl
  | fieldPow p k =>
      cases h
      match args with
      | .cons a .nil =>
          simp only [lowering]
          rw [powBlock_denote p k (mapVar a) (mapVal V), mapVar_lookup a V]
          rfl

/-! ## 6. Whole-program denotation preservation -/

/-- Lower a whole derived-dialect program to the field dialect. -/
def lowerDerivedToField {Γ : Ctxt derivedDialect} {t : DerivedTy}
    (c : Com derivedDialect Γ t) : Com fieldDialect (mapCtx Γ) (mapTy t) :=
  lowering.blockLowerCom c

/-- **`derivedDialect → fieldDialect` is denotation-preserving, for every
    program.** Obtained from the three leaves by `blockFundamental`; no induction
    over programs. `fieldDialect` lowers on to `jasminDialect`, so this connects
    the derived ops to the emit spine. -/
theorem lowerDerivedToField_denote {Γ : Ctxt derivedDialect} {t : DerivedTy}
    (c : Com derivedDialect Γ t) (V : Ctxt.Valuation Γ) :
    (lowerDerivedToField c).denote (mapVal V) = transTy (c.denote V) :=
  blockFundamental lowering transTy mapVal
    varTransports blockOpTransports mapValExtends c V

end CatCrypt.Crypto.SecureCompilation.VIR.DerivedToField
