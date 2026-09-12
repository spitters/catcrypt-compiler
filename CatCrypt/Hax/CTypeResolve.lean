/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Hax.ImpType
public import CatCrypt.Hax.CType

/-!
# CType Resolution: ImpType → CType (Total)

Total function mapping every `ImpType` to a `CType`. This is the key
Phase 3 component that eliminates proof obligations at typed extraction
call sites.

## Design: Why Total?

The `toCType` function is **total** (not `Option CType`). This is possible because:

1. **Integer widths** are extracted from hax JSON (`U8`/`U16`/... → `IntWidth`)
2. **ADT field types** are extracted from hax JSON (struct fields → `List ImpType`)
3. **Eliminated types** (`ref`, `controlFlow`, `slice`) map to their inner type
4. **Degenerate cases** (`str`, `typeVar`, `unknown`) map to `.unit`

Consequences:
- `pipelineTyped` takes only an `ImpExpr` + `ImpType` — no proof obligation
- `TypedHaxFn` uses plain `Eq` constraints, not `Option`-unwrapping proofs
- No `wellTyped_projection` axiom needed

**0 axioms**, **0 sorries**.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax

/-! ## Width Translation -/

/-- Map an `IntWidth` to the corresponding unsigned `CType`. -/
def IntWidth.toCType : IntWidth → CType
  | .w8 => .u8
  | .w16 => .u16
  | .w32 => .u32
  | .w64 => .u64
  | .w128 => .u128
  | .wsize => .usize

/-! ## ImpType → CType Translation -/

mutual

/-- **Total** translation from `ImpType` to `CType`.

    Every `ImpType` maps to a `CType` — no partiality, no `Option`.
    Eliminated types (`ref`, `controlFlow`, `slice`) map to their
    inner/continuation type. Degenerate types map to `.unit`. -/
def ImpType.toCType : ImpType → CType
  | .bool => .bool
  | .unit => .unit
  | .uint w => w.toCType
  | .sint w => w.toCType    -- signed → same CType as unsigned
  | .int => .u64             -- unresolved width → 64-bit fallback
  | .str => .unit            -- strings don't appear in crypto code
  | .array inner n => .array inner.toCType n
  | .tuple ts => ImpType.listToCType ts
  | .option t => .option t.toCType
  | .result ok err => .result ok.toCType err.toCType
  | .controlFlow _brk cont => cont.toCType
  | .adt _name _args fields => ImpType.listToCType fields
  | .fn _params ret => ret.toCType
  | .ref inner _ => inner.toCType
  | .slice inner => .array inner.toCType 0
  | .typeVar _ => .unit
  | .unknown => .unit

/-- Convert a list of `ImpType`s to a `CType` product.

    `[]` → `.unit`, `[t]` → `t.toCType`, `[t₁, t₂, ...]` → nested pairs. -/
def ImpType.listToCType : List ImpType → CType
  | [] => .unit
  | [t] => ImpType.toCType t
  | t :: ts => .pair (ImpType.toCType t) (ImpType.listToCType ts)

end

/-! ## Properties -/

/-- Unsigned and signed integers of the same width map to the same CType. -/
theorem toCType_sint_eq_uint (w : IntWidth) :
    ImpType.toCType (.sint w) = ImpType.toCType (.uint w) := by
  cases w <;> rfl

/-- References are transparent to `toCType`. -/
theorem toCType_ref (inner : ImpType) (m : Bool) :
    ImpType.toCType (.ref inner m) = inner.toCType := by
  simp [ImpType.toCType]

/-- Control flow maps to the continuation type. -/
theorem toCType_controlFlow (brk cont : ImpType) :
    ImpType.toCType (.controlFlow brk cont) = cont.toCType := by
  simp [ImpType.toCType]

/-- Single-field ADTs unwrap to the field type (newtype pattern). -/
theorem toCType_adt_newtype (name : String) (args : List ImpType) (f : ImpType) :
    ImpType.toCType (.adt name args [f]) = f.toCType := by
  simp [ImpType.toCType, ImpType.listToCType]

/-- Empty ADTs (unit-like enums) map to `.unit`. -/
theorem toCType_adt_unit (name : String) (args : List ImpType) :
    ImpType.toCType (.adt name args []) = .unit := by
  simp [ImpType.toCType, ImpType.listToCType]

/-! ## Denoted Type -/

/-- The Lean type corresponding to an `ImpType`, via `CType.denote`. -/
abbrev ImpType.denote (τ : ImpType) : Type := τ.toCType.denote

/-! ## Common Fintype / DecidableEq / Nonempty from ImpType -/

/-- `Fintype` for any `ImpType`'s denotation. -/
noncomputable def ImpType.instFintype (τ : ImpType) : Fintype τ.denote :=
  CType.instFintype τ.toCType

/-- `DecidableEq` for any `ImpType`'s denotation. -/
def ImpType.instDecidableEq (τ : ImpType) : DecidableEq τ.denote :=
  CType.instDecidableEq τ.toCType

/-- `Inhabited` for any `ImpType`'s denotation. -/
def ImpType.instInhabited (τ : ImpType) : Inhabited τ.denote :=
  CType.instInhabited τ.toCType

/-- `Nonempty` for any `ImpType`'s denotation. -/
def ImpType.instNonempty (τ : ImpType) : Nonempty τ.denote :=
  CType.instNonempty τ.toCType

/-! ## Sanity Checks -/

-- Standard crypto types resolve correctly
example : ImpType.toCType (.uint .w8) = .u8 := rfl
example : ImpType.toCType (.uint .w32) = .u32 := rfl
example : ImpType.toCType (.uint .w64) = .u64 := rfl
example : ImpType.toCType (.uint .w128) = .u128 := rfl
example : ImpType.toCType (.uint .wsize) = .usize := rfl

-- Array types
example : ImpType.toCType (.array (.uint .w8) 16) = .array .u8 16 := rfl
example : ImpType.toCType (.array (.uint .w8) 32) = .array .u8 32 := rfl

-- Tuple types
example : ImpType.toCType (.tuple []) = .unit := rfl
example : ImpType.toCType (.tuple [.uint .w8]) = .u8 := rfl
example : ImpType.toCType (.tuple [.uint .w8, .bool]) = .pair .u8 .bool := rfl

-- ADT types
example : ImpType.toCType (.adt "MyStruct" [] [.uint .w32, .uint .w64]) =
    .pair .u32 .u64 := rfl

-- Denotation matches CType
example : ImpType.denote (.uint .w8) = UInt8 := rfl
example : ImpType.denote (.array (.uint .w8) 16) = Vector UInt8 16 := rfl
example : ImpType.denote (.tuple [.uint .w8, .bool]) = (UInt8 × Bool) := rfl

end CatCrypt.Hax
