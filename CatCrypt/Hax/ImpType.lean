/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

/-!
# ImpType: Hax Extraction Type Universe

Type annotations for hax-extracted Rust code. Each `ImpType` represents
a Rust type as seen in the hax JSON output, carrying enough information
(integer widths, ADT field types) for total translation to `CType`.

## Design

The `ImpType` universe is designed to make `toCType` **total** — every
`ImpType` maps to a `CType` without partiality. This eliminates proof
obligations at every typed extraction call site.

Key design choices:
- `IntWidth` carries exact bit-width (not just "integer")
- `adt` carries field types (not just name/args)
- Eliminated types (`ref`, `controlFlow`, `slice`) map to inner types
- Degenerate cases (`str`, `typeVar`, `unknown`) map to `.unit`

## Type correspondences (Rust → ImpType → CType → Lean)

| Rust type   | ImpType         | CType        | Lean type         |
|------------|-----------------|-------------|-------------------|
| `u8`       | `.uint .w8`     | `.u8`       | `UInt8`           |
| `u32`      | `.uint .w32`    | `.u32`      | `UInt32`          |
| `u64`      | `.uint .w64`    | `.u64`      | `UInt64`          |
| `[u8; 16]` | `.array (.uint .w8) 16` | `.array .u8 16` | `Vector UInt8 16` |
| `(A, B)`   | `.tuple [A, B]` | `.pair a b` | `a × b`           |
| `Option<T>`| `.option t`     | `.option t` | `Option t`        |

**0 axioms**, **0 sorries**.
-/

set_option autoImplicit false

namespace CatCrypt.Hax

/-! ## Integer Width -/

/-- Bit-width of a Rust integer type.

    Extracted from hax JSON: `"U8"` → `.w8`, `"U32"` → `.w32`, etc. -/
inductive IntWidth where
  | w8
  | w16
  | w32
  | w64
  | w128
  | wsize  -- platform-dependent, treated as 64-bit
  deriving DecidableEq, Repr, Inhabited

/-- Number of bits for an integer width. -/
def IntWidth.bits : IntWidth → Nat
  | .w8 => 8
  | .w16 => 16
  | .w32 => 32
  | .w64 => 64
  | .w128 => 128
  | .wsize => 64

/-! ## ImpType -/

/-- Type universe for hax-extracted Rust code.

    Carries enough structure for total translation to `CType`:
    - Integer widths distinguish `u8`/`u16`/`u32`/`u64`/`u128`/`usize`
    - ADT constructors carry field types (not just name + args)
    - Eliminated types have fallback mappings -/
inductive ImpType where
  /-- Boolean. -/
  | bool
  /-- Unit / void. -/
  | unit
  /-- Unsigned integer with known width. -/
  | uint (w : IntWidth)
  /-- Signed integer with known width. -/
  | sint (w : IntWidth)
  /-- Integer with unknown/unresolved width (backward compat). Maps to u64. -/
  | int
  /-- String type (rarely appears in crypto code). Maps to unit. -/
  | str
  /-- Tuple of types: `(T1, T2, ...)`. -/
  | tuple (tys : List ImpType)
  /-- Fixed-size array: `[T; n]`. -/
  | array (elem : ImpType) (n : Nat)
  /-- Option type: `Option<T>`. -/
  | option (a : ImpType)
  /-- Result type: `Result<T, E>`. -/
  | result (ok err : ImpType)
  /-- User-defined ADT (struct/enum). Carries name, generic args, and field types. -/
  | adt (name : String) (args : List ImpType) (fields : List ImpType)
  /-- Reference: `&T` or `&mut T`. Eliminated by dropReferences. -/
  | ref (inner : ImpType) (mutable : Bool)
  /-- Slice: `[T]`. Only appears pre-pipeline. -/
  | slice (inner : ImpType)
  /-- Control flow: `ControlFlow<B, C>`. Eliminated by cfIntoMonads. -/
  | controlFlow (brk cont : ImpType)
  /-- Function type: `fn(T1, ...) -> R`. -/
  | fn (params : List ImpType) (ret : ImpType)
  /-- Type variable (monomorphized away by hax). -/
  | typeVar (name : String)
  /-- Unknown/unresolved type (parser fallback). -/
  | unknown
  deriving Repr, Inhabited

/-! ## Smart Constructors -/

/-- Create an unsigned integer type from bit count. -/
def ImpType.uintBits : Nat → ImpType
  | 8 => .uint .w8
  | 16 => .uint .w16
  | 32 => .uint .w32
  | 64 => .uint .w64
  | 128 => .uint .w128
  | _ => .int  -- fallback for unknown widths

/-- Create a signed integer type from bit count. -/
def ImpType.sintBits : Nat → ImpType
  | 8 => .sint .w8
  | 16 => .sint .w16
  | 32 => .sint .w32
  | 64 => .sint .w64
  | 128 => .sint .w128
  | _ => .int

/-- Standard Rust array type: `[u8; n]`. -/
def ImpType.byteArray (n : Nat) : ImpType := .array (.uint .w8) n

/-- Standard Rust key type: `[u8; 32]`. -/
abbrev ImpType.key256 : ImpType := .byteArray 32

/-- Standard Rust block type: `[u8; 16]`. -/
abbrev ImpType.block128 : ImpType := .byteArray 16

/-! ## Predicates -/

/-- An `ImpType` is "core" — survives all pipeline phases. -/
partial def ImpType.isCore : ImpType → Bool
  | .bool | .unit | .uint _ | .sint _ | .int | .str => true
  | .tuple ts => ts.all ImpType.isCore
  | .array e _ => e.isCore
  | .option a => a.isCore
  | .result ok err => ok.isCore && err.isCore
  | .adt _ _ fields => fields.all ImpType.isCore
  | .ref _ _ | .slice _ | .controlFlow _ _ => false
  | .fn _ ret => ret.isCore
  | .typeVar _ | .unknown => true

/-- An `ImpType` is "concrete" — has no type variables or unknowns. -/
partial def ImpType.isConcrete : ImpType → Bool
  | .typeVar _ | .unknown => false
  | .bool | .unit | .uint _ | .sint _ | .int | .str => true
  | .tuple ts => ts.all ImpType.isConcrete
  | .array e _ => e.isConcrete
  | .option a => a.isConcrete
  | .result ok err => ok.isConcrete && err.isConcrete
  | .adt _ args fields => args.all ImpType.isConcrete && fields.all ImpType.isConcrete
  | .ref inner _ => inner.isConcrete
  | .slice inner => inner.isConcrete
  | .controlFlow brk cont => brk.isConcrete && cont.isConcrete
  | .fn params ret => params.all ImpType.isConcrete && ret.isConcrete

/-! ## Display -/

/-- Human-readable display of an `ImpType`. -/
partial def ImpType.toString : ImpType → String
  | .bool => "bool"
  | .unit => "()"
  | .uint w => s!"u{w.bits}"
  | .sint w => s!"i{w.bits}"
  | .int => "int"
  | .str => "str"
  | .tuple ts => s!"({", ".intercalate (ts.map ImpType.toString)})"
  | .array e n => s!"[{e.toString}; {n}]"
  | .option a => s!"Option<{a.toString}>"
  | .result ok err => s!"Result<{ok.toString}, {err.toString}>"
  | .adt name _ _ => name
  | .ref inner true => s!"&mut {inner.toString}"
  | .ref inner false => s!"&{inner.toString}"
  | .slice inner => s!"[{inner.toString}]"
  | .controlFlow brk cont => s!"ControlFlow<{brk.toString}, {cont.toString}>"
  | .fn params ret =>
    s!"fn({", ".intercalate (params.map ImpType.toString)}) -> {ret.toString}"
  | .typeVar name => name
  | .unknown => "?"

instance : ToString ImpType := ⟨ImpType.toString⟩

/-! ## Common Rust types as ImpType -/

namespace RustTypes

/-- `u8` -/
abbrev u8 : ImpType := .uint .w8
/-- `u16` -/
abbrev u16 : ImpType := .uint .w16
/-- `u32` -/
abbrev u32 : ImpType := .uint .w32
/-- `u64` -/
abbrev u64 : ImpType := .uint .w64
/-- `u128` -/
abbrev u128 : ImpType := .uint .w128
/-- `usize` -/
abbrev usize : ImpType := .uint .wsize
/-- `bool` -/
abbrev bool_ : ImpType := .bool

end RustTypes

end CatCrypt.Hax
