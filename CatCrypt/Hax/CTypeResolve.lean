/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.ImpType
public import CatCrypt.Hax.AST
public import CatCrypt.Hax.CType

/-!
# CType Resolution: ImpType → CType (Total)

Total function mapping every `Hax.ImpType` to a `CType`, so that typed
extraction call sites carry no proof obligation.

## Design: Why Total?

The `toCType` function is **total** (not `Option CType`). This is possible because:

1. **Integer widths** are extracted from hax JSON (`U8`/`U16`/... → `IntWidth`)
2. **ADT types** carry only their name and type arguments in `Hax.ImpType`;
   a `StructTable` maps a struct name to its `CType`, and a name outside the
   table maps to `.unit`
3. **Eliminated types** (`ref`, `controlFlow`, `slice`) map to their inner type
4. **Degenerate cases** (`str`, `typeVar`, `unknown`) map to `.unit`

Consequences:
- `pipelineTyped` takes only an `ImpExpr` + `ImpType` — no proof obligation
- `TypedHaxFn` uses plain `Eq` constraints, not `Option`-unwrapping proofs
- No `wellTyped_projection` axiom needed

## Smart constructors and predicates on `Hax.ImpType`

`Hax.ImpType.uintBits`, `sintBits`, `byteArray`, `key256`, `block128`, `isCore`
and `isConcrete` are the CatCrypt-side helpers on the hax-lean type; they are
declared here in the `Hax.ImpType` namespace so that dot notation on a
`Hax.ImpType` reaches them.
-/

@[expose] public section

set_option autoImplicit false

namespace Hax.ImpType

/-! ## Smart Constructors -/

/-- Create an unsigned integer type from bit count. -/
def uintBits : Nat → ImpType
  | 8 => .uint .w8
  | 16 => .uint .w16
  | 32 => .uint .w32
  | 64 => .uint .w64
  | 128 => .uint .w128
  | _ => .int  -- fallback for unknown widths

/-- Create a signed integer type from bit count. -/
def sintBits : Nat → ImpType
  | 8 => .sint .w8
  | 16 => .sint .w16
  | 32 => .sint .w32
  | 64 => .sint .w64
  | 128 => .sint .w128
  | _ => .int

/-- Standard Rust array type: `[u8; n]`. -/
def byteArray (n : Nat) : ImpType := .array (.uint .w8) n

/-- Standard Rust key type: `[u8; 32]`. -/
abbrev key256 : ImpType := .byteArray 32

/-- Standard Rust block type: `[u8; 16]`. -/
abbrev block128 : ImpType := .byteArray 16

/-! ## Predicates -/

/-- An `ImpType` is "core" — survives all pipeline phases. -/
partial def isCore : ImpType → Bool
  | .bool | .unit | .uint _ | .sint _ | .int | .str => true
  | .tuple ts => ts.all isCore
  | .array e _ => e.isCore
  | .option a => a.isCore
  | .result ok err => ok.isCore && err.isCore
  | .adt _ _ => true
  | .ref _ _ | .slice _ | .controlFlow _ _ => false
  | .fn _ ret => ret.isCore
  | .typeVar _ | .unknown => true

/-- An `ImpType` is "concrete" — has no type variables or unknowns. -/
partial def isConcrete : ImpType → Bool
  | .typeVar _ | .unknown => false
  | .bool | .unit | .uint _ | .sint _ | .int | .str => true
  | .tuple ts => ts.all isConcrete
  | .array e _ => e.isConcrete
  | .option a => a.isConcrete
  | .result ok err => ok.isConcrete && err.isConcrete
  | .adt _ args => args.all isConcrete
  | .ref inner _ => inner.isConcrete
  | .slice inner => inner.isConcrete
  | .controlFlow brk cont => brk.isConcrete && cont.isConcrete
  | .fn params ret => params.all isConcrete && ret.isConcrete

end Hax.ImpType

/-! ## Width Translation -/

/-- Map an `IntWidth` to the corresponding unsigned `CType`. -/
def Hax.IntWidth.toCType : Hax.IntWidth → CatCrypt.Hax.CType
  | .w8 => .u8
  | .w16 => .u16
  | .w32 => .u32
  | .w64 => .u64
  | .w128 => .u128
  | .wsize => .usize

/-! ## Struct table -/

/-- The `CType` of each named struct.  `Hax.ImpType.adt` carries the struct's
    name and type arguments only; this table supplies the representation type
    of the struct's field tuple. -/
abbrev CatCrypt.Hax.StructTable := String → Option CatCrypt.Hax.CType

/-- The empty struct table: every `adt` maps to `.unit`. -/
def CatCrypt.Hax.emptyStructTable : CatCrypt.Hax.StructTable := fun _ => none

namespace Hax.ImpType

open CatCrypt.Hax (CType StructTable emptyStructTable)

/-! ## ImpType → CType Translation -/

mutual

/-- **Total** translation from `ImpType` to `CType`.

    Every `ImpType` maps to a `CType` — no partiality, no `Option`.
    Eliminated types (`ref`, `controlFlow`, `slice`) map to their
    inner/continuation type. An `adt` maps through the struct table `st`
    (`.unit` for a name outside it). Degenerate types map to `.unit`. -/
def toCType : ImpType → (st : StructTable := emptyStructTable) → CType
  | .bool, _ => .bool
  | .unit, _ => .unit
  | .uint w, _ => w.toCType
  | .sint w, _ => w.toCType    -- signed → same CType as unsigned
  | .int, _ => .u64             -- unresolved width → 64-bit fallback
  | .str, _ => .unit            -- strings don't appear in crypto code
  | .array inner n, st => .array (toCType inner st) n
  | .tuple ts, st => listToCType ts st
  | .option t, st => .option (toCType t st)
  | .result ok err, st => .result (toCType ok st) (toCType err st)
  | .controlFlow _brk cont, st => toCType cont st
  | .adt name _args, st => (st name).getD .unit
  | .fn _params ret, st => toCType ret st
  | .ref inner _, st => toCType inner st
  | .slice inner, st => .array (toCType inner st) 0
  | .typeVar _, _ => .unit
  | .unknown, _ => .unit

/-- Convert a list of `ImpType`s to a `CType` product.

    `[]` → `.unit`, `[t]` → `t.toCType`, `[t₁, t₂, ...]` → nested pairs. -/
def listToCType : List ImpType → (st : StructTable := emptyStructTable) → CType
  | [], _ => .unit
  | [t], st => toCType t st
  | t :: ts, st => .pair (toCType t st) (listToCType ts st)

end

/-- The Lean type corresponding to an `ImpType`, via `CType.denote`. -/
abbrev denote (τ : ImpType) : Type := τ.toCType.denote

end Hax.ImpType

namespace CatCrypt.Hax

open _root_.Hax (IntWidth ImpType)

/-! ## Properties -/

/-- Unsigned and signed integers of the same width map to the same CType. -/
theorem toCType_sint_eq_uint (w : IntWidth) (st : StructTable) :
    ImpType.toCType (.sint w) st = ImpType.toCType (.uint w) st := by
  cases w <;> rfl

/-- References are transparent to `toCType`. -/
theorem toCType_ref (inner : ImpType) (m : Bool) (st : StructTable) :
    ImpType.toCType (.ref inner m) st = inner.toCType st := by
  simp [ImpType.toCType]

/-- Control flow maps to the continuation type. -/
theorem toCType_controlFlow (brk cont : ImpType) (st : StructTable) :
    ImpType.toCType (.controlFlow brk cont) st = cont.toCType st := by
  simp [ImpType.toCType]

/-- An ADT in the struct table maps to its table entry. -/
theorem toCType_adt_of_table (name : String) (args : List ImpType) (st : StructTable)
    (τ : CType) (h : st name = some τ) :
    ImpType.toCType (.adt name args) st = τ := by
  simp [ImpType.toCType, h]

/-- An ADT outside the struct table maps to `.unit`. -/
theorem toCType_adt_of_none (name : String) (args : List ImpType) (st : StructTable)
    (h : st name = none) :
    ImpType.toCType (.adt name args) st = .unit := by
  simp [ImpType.toCType, h]

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
example : ImpType.toCType (.byteArray 32) = .array .u8 32 := rfl

-- Tuple types
example : ImpType.toCType (.tuple []) = .unit := rfl
example : ImpType.toCType (.tuple [.uint .w8]) = .u8 := rfl
example : ImpType.toCType (.tuple [.uint .w8, .bool]) = .pair .u8 .bool := rfl

-- ADT types resolve through the struct table
example : ImpType.toCType (.adt "MyStruct" [])
    (fun n => if n = "MyStruct" then some (.pair .u32 .u64) else none) =
    .pair .u32 .u64 := rfl
example : ImpType.toCType (.adt "MyStruct" []) = .unit := rfl

-- Denotation matches CType
example : ImpType.denote (.uint .w8) = UInt8 := rfl
example : ImpType.denote (.array (.uint .w8) 16) = Vector UInt8 16 := rfl
example : ImpType.denote (.tuple [.uint .w8, .bool]) = (UInt8 × Bool) := rfl

end CatCrypt.Hax
