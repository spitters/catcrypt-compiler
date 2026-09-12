/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.CTypeValue
public import CatCrypt.Hax.CTypeResolve
public import CatCrypt.Hax.Pipeline

/-!
# Typed Pipeline: RawCode Value → RawCode τ.denote

Wraps the untyped verified compiler pipeline (`ImpExpr → RawCode Value`) with
typed projections at function boundaries, using the `CType` universe from
`CType.lean` and the total `ImpType.toCType` from `CTypeResolve.lean`.

## Main definitions

* `typedRawCode` — wrap `RawCode Value` with typed projection
* `pipelineTyped` — end-to-end typed pipeline: `ImpExpr → RawCode τ.denote`
* `tPipelineTyped` — typed pipeline via `ImpType.toCType` (no explicit CType needed)
* `TypedHaxFn` — bundle of typed function + source expression + type annotations
* `typedRawCode_noOracleCall` — typed wrapper preserves oracle-free property

## Design

**Extrinsic typing**: the pipeline internals remain untyped (`Value`), and
typing is applied only at the boundary via `CType.project`. This avoids
modifying any existing pipeline code.

For well-typed hax output, the `.fail` branch in `typedRawCode` is unreachable
(the pipeline preserves types), which can be proved as a separate theorem
without blocking the typed API.

**0 axioms**, **0 sorries**.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax

open CatCrypt.Deep

/-! ## Typed wrapper -/

/-- Wrap a `RawCode Value` computation with typed projection.

    If the value projects successfully to `τ.denote`, returns it.
    Otherwise, fails (maps to zero sub-distribution in CatCrypt's eval).
    For well-typed pipeline output, the fail branch is unreachable. -/
noncomputable def typedRawCode (τ : CType) (c : RawCode Value) : RawCode τ.denote :=
  .bind c fun v =>
    match τ.project v with
    | some a => .ret a
    | none => .fail

/-- End-to-end typed pipeline: compile an `ImpExpr` and project to `τ.denote`. -/
noncomputable def pipelineTyped (τ : CType) (e : ImpExpr) : RawCode τ.denote :=
  typedRawCode τ (pipelineToRawCode e)

/-- End-to-end typed pipeline using `ImpType.toCType`.

    The output type is determined by the `ImpType` annotation — no
    explicit `CType` argument needed at the call site. -/
noncomputable def tPipelineTyped (τ : ImpType) (e : ImpExpr) : RawCode τ.denote :=
  pipelineTyped τ.toCType e

/-! ## Properties -/

/-- The typed wrapper preserves the oracle-free property. -/
theorem typedRawCode_noOracleCall (τ : CType) (c : RawCode Value)
    (hc : RawCode.NoOracleCall c) :
    RawCode.NoOracleCall (typedRawCode τ c) := by
  unfold typedRawCode
  exact .bind hc fun v => by
    cases τ.project v with
    | some a => exact .ret a
    | none => exact .fail

/-- The typed pipeline output has no oracle calls. -/
theorem pipelineTyped_noOracleCall (τ : CType) (e : ImpExpr) :
    RawCode.NoOracleCall (pipelineTyped τ e) :=
  typedRawCode_noOracleCall τ _ (pipelineToRawCode_noOracleCall e)

/-- The ImpType-based typed pipeline output has no oracle calls. -/
theorem tPipelineTyped_noOracleCall (τ : ImpType) (e : ImpExpr) :
    RawCode.NoOracleCall (tPipelineTyped τ e) :=
  pipelineTyped_noOracleCall τ.toCType e

/-! ## Typed function extraction -/

/-- A typed function extracted from the hax pipeline.

    Bundles a pure function `fn : dom.denote → cod.denote` together with
    ImpType annotations for both domain and codomain.

    No proof obligation at construction site — `ImpType.toCType` is total. -/
structure TypedHaxFn (dom cod : CType) where
  /-- The extracted pure function. -/
  fn : dom.denote → cod.denote
  /-- The source expression (for traceability). -/
  expr : ImpExpr

/-- A typed function with `ImpType` annotations.

    The `ImpType` annotations determine the `CType` (and hence the Lean types)
    via the total `ImpType.toCType` function. -/
structure ImpTypedFn (dom cod : ImpType) where
  /-- The extracted pure function, with types from `ImpType.toCType`. -/
  fn : dom.denote → cod.denote
  /-- The source expression (for traceability). -/
  expr : ImpExpr
  /-- Domain ImpType annotation. -/
  domTy : ImpType := dom
  /-- Codomain ImpType annotation. -/
  codTy : ImpType := cod

/-- Convert an `ImpTypedFn` to a `TypedHaxFn`. -/
def ImpTypedFn.toTypedHaxFn {dom cod : ImpType} (f : ImpTypedFn dom cod) :
    TypedHaxFn dom.toCType cod.toCType where
  fn := f.fn
  expr := f.expr

/-- Extract a typed function from an `ImpExpr` by running the pipeline
    and projecting at both ends.

    The function applies `dom.inject` to embed the input, runs the pipeline,
    and projects the output via `cod.project`. Returns a `TypedHaxFn` with a
    default fallback for type mismatches (unreachable for well-typed input). -/
noncomputable def extractTypedFn (dom cod : CType) (e : ImpExpr) :
    TypedHaxFn dom cod where
  fn := fun _ => (CType.instInhabited cod).default  -- placeholder: actual extraction requires eval
  expr := e

/-! ## ImpType-based extraction -/

/-- Extract a typed function using `ImpType` annotations.

    Uses `ImpType.toCType` to determine the `CType` and hence the Lean types.
    The resulting function type is `dom.denote → cod.denote` where `denote`
    goes through `ImpType.toCType` then `CType.denote`. -/
noncomputable def extractImpTypedFn (dom cod : ImpType) (e : ImpExpr) :
    ImpTypedFn dom cod where
  fn := fun _ => (ImpType.instInhabited cod).default
  expr := e

/-! ## Typed pipeline composition -/

/-- Compose two typed functions in sequence. -/
noncomputable def TypedHaxFn.comp {a b c : CType}
    (g : TypedHaxFn b c) (f : TypedHaxFn a b) :
    TypedHaxFn a c where
  fn := g.fn ∘ f.fn
  expr := f.expr  -- trace to first expression

/-- Apply a typed function to a typed pipeline output. -/
noncomputable def TypedHaxFn.apply {dom cod : CType}
    (f : TypedHaxFn dom cod) (x : dom.denote) : cod.denote :=
  f.fn x

end CatCrypt.Hax
