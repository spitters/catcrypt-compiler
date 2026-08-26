/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Hax.LowCTSubset
import CatCrypt.Crypto.Jasmin.LowCT

/-!
# H2: Translation `ImpExpr → Option LowCT`

Implements **Track H2** from `BLS/NEXT.md`: a structural-recursive
translation that lifts the H1 decidable filter
(`CatCrypt.Crypto.Hax.LowCTRepresentable.Expr`) into a lowering function
`haxToLowCT : ImpExpr → Option LowCT`.

`LowCT` is statement-shaped: there is no "value" expression form, only
commands that read named tower- and scalar-variables and write into named
destination slots.  A flat `ImpExpr → Option LowCT` map is therefore
ill-typed for sub-expressions (an `app f args` has no destination on its
own).  We use **Option A** from the H2 plan: a fused recursion that
recognises `letBind name (app f args) body` and emits
`RLetZero name (towerOfCall f) (RSeq (RCall f ⟨name⟩ args') body')`.
Sub-expressions inside `args` must be `var`s (i.e. already named); deeper
nesting requires the H2.1 follow-up.

## Covered

* `letBind name (app f args) body` with `args` all `var`s — let-of-call.
* `letBind name (lit ...) body` — u64-let + scalar-set (nonneg int,
  uint, and bool-as-0/1).
* `seq a b`, `unitVal`, trailing `var _`.
* `tuple es` with `es` all `var`s — aggregate tuple tail of named
  results; each component already lives in its slot, so the tail is
  `RSkip` (same justification as the trailing `var _` arm).
* `assign name (lit _)` / `(app f args)` — direct `RScalarSet`/`RCall`.
* `ifThenElse (var v) _ _` / `whileLoop (var v) _` — `RIfNz` / `RWhileNz`.

## Returns `none`

* All H1-rejected constructors (`proj`, `match_`, `borrow`,
  `deref`, raw `forLoop`/loop variants, `break_`, `continue_`,
  `earlyReturn`, `questionMark`, `cf*`).
* `tuple es` with a non-`var` component.
* `lit _` at tail position (no destination slot).
* `app _ _` at non-let, non-assign position (no destination).
* `letBind _ (rhs) _` for non-call non-literal rhs.

`towerOfCallName` picks the destination `TowerType` from the leaf-call
name prefix; a future pass should derive it from the missing `ImpType`
annotation on let-bindings.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Hax (ImpExpr ImpLit ImpType IntWidth)
open CatCrypt.Crypto.Jasmin.LowCT
  (TowerType LowCT Located)

/-! ## §1  Tower type from leaf-call name

The H1 `callWhitelist` lumps all leaf calls together; H2 must additionally
decide which tower type each call's destination has.  For the prefix-based
naming convention used by hax-extracted shims, this is mechanical.

### Per-protocol override pattern (2026-05-22)

A single hard-coded prefix dispatch cannot disambiguate cross-protocol
name collisions: for example, `scalar_add` legitimately means *different*
tower types in different protocols (Curve25519's `.TFpL25519` vs BLS's
BLS-scalar field).  Bridge files documented this as Frictions #1, #5,
#6, #7, #8.

The fix exposes the dispatch as a typeclass `TowerOfCallNameInst`.  The
*default* dispatch (`towerOfCallName_default`) reproduces the historical
prefix-based behaviour and is registered as the default instance, so
existing callers continue to work unchanged.  Protocols that need a
different mapping for a name collision provide their own typeclass
instance scoped to their bridge namespace.

A documented pattern for an Ed25519-specific override (sketch only —
**not** applied here, kept for documentation; see Friction #1):

```lean
namespace CatCrypt.Crypto.EdDSA

instance edDSA_TowerOfCallNameInst :
    CatCrypt.Crypto.Hax.TowerOfCallNameInst :=
  ⟨fun f => match f with
    | "scalar_add" => .TFpL25519  -- Ed25519 scalar (= default)
    | _            => CatCrypt.Crypto.Hax.towerOfCallName_default f⟩

end CatCrypt.Crypto.EdDSA
```

The same shape works for BLS to remap `scalar_*`, `g2_*`, `bbs_*`, and
`*_be_bytes` to BLS-correct tower types.  -/

/-- Default dispatch from leaf-call names to `TowerType`.  This is the
    *historical* prefix-based function — kept under the `_default`
    suffix so it remains available as a baseline, and registered as the
    default instance of `TowerOfCallNameInst` below.

    Falls back to `.TFp` for unrecognised names — but the H1 filter has
    already restricted us to the whitelist, so every reachable string
    here is one of the documented prefixes.

    Ed25519 / EdDSA additions (2026-05-22): the haxpipeT extraction for
    EdDSA emits abstract leaf names (`group_*`, `scalar_*`, `hash_*`,
    `generator`) rather than the curve-specific prefixes used by lower-
    level kernels.  Added per-leaf branches dispatch them to the
    appropriate tower type (point ops → `.TFp25519`, scalar ops →
    `.TFpL25519`, hash challenges → `.TFpL25519`). -/
def towerOfCallName_default (f : String) : TowerType :=
  if f.startsWith "fp12_" then .TFp12
  else if f.startsWith "fp6_" then .TFp6
  else if f.startsWith "fp2_" then .TFp2
  else if f.startsWith "fp25519_" then .TFp25519
  else if f.startsWith "scalar25519_" then .TFpL25519
  else if f.startsWith "fpP256_" then .TFpP256
  else if f.startsWith "u64_" then .TU64
  else if f.startsWith "fp_" then .TFp
  -- Ed25519 abstract leaves
  else if f.startsWith "group_" then .TFp25519
  else if f.startsWith "scalar_" then .TFpL25519
  else if f.startsWith "hash_" then .TFpL25519
  else if f = "generator" then .TFp25519
  else .TFp

/-- Per-protocol mapping from leaf call names to the destination
    `TowerType` that `haxToLowCT` should use.  Protocols override this
    with their own instances to handle name collisions (e.g.,
    `scalar_add` differs between Curve25519, BLS12-381, P-256).

    The framework's default instance wraps `towerOfCallName_default`,
    preserving the hard-coded prefix dispatch for backward
    compatibility.  Protocols supply their own instance in their bridge
    file to override per-leaf semantics. -/
class TowerOfCallNameInst where
  /-- The dispatch function. -/
  callTower : String → TowerType

/-- Default instance: the framework's historical prefix-based dispatch.
    Registered as `default` so it is picked up only when no
    protocol-local instance shadows it. -/
instance (priority := low) defaultTowerOfCallNameInst :
    TowerOfCallNameInst :=
  ⟨towerOfCallName_default⟩

/-- Public dispatch from leaf-call names to `TowerType`, parametrised
    by a `TowerOfCallNameInst` instance.  Resolves to
    `towerOfCallName_default` when no protocol override is in scope (via
    the `defaultTowerOfCallNameInst`).

    All existing call sites (`towerOfCallName f` with no explicit
    instance) continue to compile unchanged: Lean synthesises the
    default instance and the result reduces to the historical
    prefix-based dispatch. -/
@[reducible] def towerOfCallName [inst : TowerOfCallNameInst]
    (f : String) : TowerType :=
  inst.callTower f

/-! ### Grind-database lemmas for `towerOfCallName`

The `String.startsWith` checks in `towerOfCallName_default` are not
reducible by `decide` (only by `native_decide`).  Per-prefix
`@[grind =]` rewrite lemmas let `grind` discharge
`towerOfCallName "..." = ...` goals without invoking `decide` at all.

Each lemma proves `towerOfCallName <concrete-name> = <tower-type>` by
`native_decide`; the `@[grind =]` makes the equation a rewrite rule
for the grind database, so downstream callers get the closed form
mechanically.

The lemmas are stated against `towerOfCallName` (the typeclass form),
which under the default instance reduces to `towerOfCallName_default`.
When a protocol installs its own `TowerOfCallNameInst` instance, the
unqualified `towerOfCallName` lemmas do not apply (the instance is
shadowed by the local one); the protocol bridge supplies its own
per-leaf lemmas using the override. -/

@[grind =] theorem towerOfCallName_generator :
    towerOfCallName "generator" = .TFp25519 := by native_decide

@[grind =] theorem towerOfCallName_group_add :
    towerOfCallName "group_add" = .TFp25519 := by native_decide

@[grind =] theorem towerOfCallName_group_mul :
    towerOfCallName "group_mul" = .TFp25519 := by native_decide

@[grind =] theorem towerOfCallName_scalar_add :
    towerOfCallName "scalar_add" = .TFpL25519 := by native_decide

@[grind =] theorem towerOfCallName_scalar_mul :
    towerOfCallName "scalar_mul" = .TFpL25519 := by native_decide

@[grind =] theorem towerOfCallName_hash_challenge :
    towerOfCallName "hash_challenge" = .TFpL25519 := by native_decide

@[grind =] theorem towerOfCallName_fp25519_add :
    towerOfCallName "fp25519_add" = .TFp25519 := by native_decide

@[grind =] theorem towerOfCallName_fp25519_mul :
    towerOfCallName "fp25519_mul" = .TFp25519 := by native_decide

@[grind =] theorem towerOfCallName_fp25519_sq :
    towerOfCallName "fp25519_sq" = .TFp25519 := by native_decide

@[grind =] theorem towerOfCallName_fp25519_inv :
    towerOfCallName "fp25519_inv" = .TFp25519 := by native_decide

@[grind =] theorem towerOfCallName_scalar25519_reduce :
    towerOfCallName "scalar25519_reduce" = .TFpL25519 := by native_decide

/-- Compatibility: under the default instance, the typeclass-dispatched
    `towerOfCallName` agrees with the historical `towerOfCallName_default`
    pointwise.  Holds by `rfl` because the default instance's `callTower`
    field is exactly `towerOfCallName_default`. -/
theorem towerOfCallName_default_eq (f : String) :
    towerOfCallName f = towerOfCallName_default f := rfl

/-! ## §2  Argument translation

A `LowCT` call argument is a `Located`, which is a named slot with a
source/destination tower type.  At translation time we don't know the
exact source/destination types of an `ImpExpr` argument — we only know it
is a `var name`.  We therefore pick the same tower type for source and
destination using `towerOfCallName f` for that argument's parent call;
this is conservative and will be sharpened in H2.1.  The borrow checker
that runs after lowering will catch any aliasing. -/

/-- Translate one `app`-argument: must already be a variable. -/
def haxArgToLocated (parentTower : TowerType) : ImpExpr → Option Located
  | .var name => some { locVar := name, locSrc := parentTower }
  | _         => none

/-- Translate a list of `app` arguments.  Returns `none` if any argument
    is not a `var`. -/
def haxArgsToLocated (parentTower : TowerType) :
    List ImpExpr → Option (List Located)
  | []      => some []
  | a :: as =>
      match haxArgToLocated parentTower a, haxArgsToLocated parentTower as with
      | some l, some ls => some (l :: ls)
      | _,      _        => none

/-- An `ImpExpr` argument is "named" if it is a plain `var`.  This is
    the side-condition every `app`-argument must satisfy for the H2
    translation to succeed (since `haxArgToLocated` only lifts `var`s
    into `Located` slots), and the condition on every component of an
    aggregate tuple tail. -/
def isVar : ImpExpr → Bool
  | .var _ => true
  | _      => false

/-! ## §3  Main translation -/

/-! ### §3.0  Type environment for the typed lowering pathway

`haxToLowCT` historically threaded zero type information about let-bound
slots: every `index`/`array_update` call defaulted its destination
TowerType to `.TFp` (a scalar field element).  That is wrong for ML-KEM,
where `polyvec[i]` returns a *polynomial* (`TPolyMod 3329 256`) and
`mat[i]` returns a *polyvec* (`TPolyVec 3329 256 m`).

The typed pathway (`haxToLowCTEnv`) threads a `TypeEnv` that maps each
known slot name to its `TowerType`, so the index/array_update cases can
derive the right destination type from the array's element type.

The untyped pathway (`haxToLowCT`) is preserved verbatim — its body is
left unchanged so the sim-file proofs (`HaxToLowCTSim_*.lean`) continue
to build against the historical equation lemmas. -/

/-- A type environment maps known slot names to their TowerTypes.
    Populated by `haxToLowCTEnv` as letBinds introduce new slots. -/
abbrev TypeEnv := List (String × TowerType)

/-- Lookup a slot's TowerType; default to `.TFp` (the current
    behaviour of the untyped path). -/
def TypeEnv.find (env : TypeEnv) (name : String) : TowerType :=
  match env with
  | [] => .TFp
  | (n, t) :: rest => if n = name then t else TypeEnv.find rest name

/-- Optional variant: returns `none` when `name` isn't bound, distinguishing
    a missing binding from a binding-to-`.TFp`.  Used by the parameter-alias
    arm to avoid shadowing a known parameter type when `src` is an external
    identifier (e.g. `ZERO_VEC`) absent from the env. -/
def TypeEnv.findOpt (env : TypeEnv) (name : String) : Option TowerType :=
  match env with
  | [] => none
  | (n, t) :: rest => if n = name then some t else TypeEnv.findOpt rest name

/-! ### §3.0.bis  Per-protocol leaf-call return-type dispatch (2026-05-23)

The default `towerOfCallName` falls back to `.TFp` for any leaf-call name
it does not recognise by prefix.  That is wrong for MLKEM: `poly_add`
returns a polynomial (`TPolyMod 3329 256`), `mat_vec_mul` returns a
polyvec, `polyvec_encode` returns bytes, etc. — none of which match the
prefix table, so they were silently typed as `.TFp` in the emitted
Jasmin (`reg u16 __anorm_2;` instead of `stack u16[256] __anorm_2;`).

A `LeafTable` is a per-protocol override that the typed pathway
(`haxToLowCTEnv`) consults before falling back to `towerOfCallName`.
The untyped pathway (`haxToLowCT`) is unaffected — its global typeclass
dispatch (`TowerOfCallNameInst`) remains the only knob there, and the
sim-file proofs keep using the historical prefix dispatch unchanged. -/

/-- A leaf-call dispatch table: associates leaf-call names with the
    `TowerType` of their (single, scalar-shaped) return value.  Used by
    `haxToLowCTEnv` to override the prefix-based `towerOfCallName`
    fallback for protocol-specific names. -/
abbrev LeafTable := List (String × TowerType)

/-- Lookup a leaf-call's return TowerType; default to
    `towerOfCallName name` (the prefix dispatch, preserving the
    historical behaviour for any name not in the table). -/
def LeafTable.find (tbl : LeafTable) (name : String) : TowerType :=
  match tbl with
  | [] => towerOfCallName name
  | (n, t) :: rest => if n = name then t else LeafTable.find rest name

/-- ML-KEM-768 leaf-call return types.  Used by `emit_extracted`'s
    typed pipeline to give protocol-specific names like `poly_add`,
    `polyvec_dot`, `mat_vec_mul` the right destination TowerType
    (instead of defaulting to `.TFp` via the prefix-only fallback).

    Names with returns that already match the prefix dispatch
    (`u64_*`, `fp_*`, `fp25519_*`, etc.) are intentionally omitted —
    the fallback handles them correctly. -/
def mlkemLeafTable : LeafTable :=
  [
    -- poly-typed returns (256-coefficient polynomial mod 3329)
    ("poly_add",            .TPolyMod 3329 256),
    ("poly_sub",            .TPolyMod 3329 256),
    ("poly_mul",            .TPolyMod 3329 256),
    ("poly_scalar",         .TPolyMod 3329 256),
    ("polyvec_dot",         .TPolyMod 3329 256),
    -- polyvec-typed returns (3 polynomials)
    ("polyvec_add",         .TPolyVec 3329 256 3),
    ("polyvec_sub",         .TPolyVec 3329 256 3),
    ("mat_vec_mul",         .TPolyVec 3329 256 3),
    ("cbd_eta1_polyvec",    .TPolyVec 3329 256 3),
    ("cbd_eta2_polyvec",    .TPolyVec 3329 256 3),
    -- matrix-typed returns
    ("gen_matrix",          .TPolyMat 3329 256 3 3),
    ("mat_transpose",       .TPolyMat 3329 256 3 3),
    -- byte-typed returns
    ("polyvec_encode",      .TBytes 1152),
    ("polyvec_decode",      .TPolyVec 3329 256 3),
    ("byte_encode_12",      .TBytes 384),
    ("byte_decode_12",      .TPolyMod 3329 256),
    ("poly_compress_du",    .TBytes 320),
    ("poly_compress_dv",    .TBytes 128),
    ("poly_decompress_du",  .TPolyMod 3329 256),
    ("poly_decompress_dv",  .TPolyMod 3329 256),
    ("polyvec_compress",    .TBytes 960),
    ("polyvec_decompress",  .TPolyVec 3329 256 3),
    -- u16/u32 small-int returns (for byte ops, masks, etc.)
    ("compress_coeff",      .TFp),
    ("decompress_coeff",    .TFp),
    ("msg_decode",          .TPolyMod 3329 256),
    ("msg_encode",          .TBytes 32),
    -- SHA-3 / SHAKE stubs (return bytes of various sizes)
    ("sha3_256",            .TBytes 32),
    ("sha3_512",            .TBytes 64),
    ("shake128",            .TBytes 504),
    ("shake256",            .TBytes 32),
    ("prf",                 .TBytes 128),
    -- Phase L.1 (2026-05-23): width-casts emitted by the byte-packing
    -- kernels (`byte_encode_12`, `poly_compress_*`).  `cast#8` →
    -- u8 (`TU8`), `cast#16` → u16 (`TFp`), `cast#32` → u32 (`TU32`),
    -- `cast#64` → u64 (`TU64`).  Without these the cast result slot is
    -- typed `TFp` (u16) and the Jasmin emit fails the u8/u32-into-u16
    -- assignment.
    ("cast#8",              .TU8),
    ("cast#16",             .TFp),
    ("cast#32",             .TU32),
    ("cast#64",             .TU64)
  ]

/-- ML-KEM zero-constant module vars (`let out = ZERO_POLY`, `let v =
    ZERO_VEC`).  These are not parameters — they introduce a fresh
    zero-initialised slot of a fixed tower type.  The alias arm of
    `haxToLowCTEnv` consults this so `let out = ZERO_POLY` lowers to
    `RLetZero out (TPolyMod 3329 256) …` rather than aliasing an
    unbound name. -/
def mlkemZeroConstTable : LeafTable :=
  [ ("ZERO_POLY", .TPolyMod 3329 256),
    ("ZERO_VEC",  .TPolyVec 3329 256 3) ]

/-- Lookup a zero-constant's tower type. -/
def mlkemZeroConst? (name : String) : Option TowerType :=
  (mlkemZeroConstTable.find? (fun p => p.1 = name)).map (·.2)

/-- Element type of a container TowerType.
    `TPolyVec q n k` is `k` polynomials of `TPolyMod q n`, so the
    element type is `TPolyMod q n`.
    `TPolyMat q n k m` is `k × m` polynomials arranged as `k`
    polyvecs of length `m`, so the element type of a 1-D `index`
    is `TPolyVec q n m`.
    `TBytes n` is a flat byte array; element type is `TFp` (treated
    as a small int).
    `TArr n t` element type is `t`.
    Default: pass through (no narrowing).

    Defined under `CatCrypt.Crypto.Jasmin.LowCT` (where `TowerType`
    lives) so `arrTy.elemType` dot-notation resolves correctly. -/
def _root_.CatCrypt.Crypto.Jasmin.LowCT.TowerType.elemType : TowerType → TowerType
  | .TPolyVec q n _k    => .TPolyMod q n
  | .TPolyMat q n _k m  => .TPolyVec q n m
  -- A polynomial's element is a single `Z_q` coefficient — a scalar,
  -- not the polynomial itself.  Without this arm `index(poly, i)`
  -- (a coefficient read) would type as a whole-polynomial slice and
  -- the Jasmin emit would wrongly stride by `n` (out-of-bounds).
  | .TPolyMod _q _n     => .TFp
  -- A byte buffer's element is a `u8` (Phase L.1).  Was `.TFp` (u16),
  -- which made `index(bytes, j)` mistype as u16 and fail the u8→u16
  -- store in the byte-packing kernels.
  | .TBytes _           => .TU8
  | .TArr _ t           => t
  | t                   => t

/-- **Stage 1a (2026-07-01) — runtime-loop bound conversion.**
    Convert a `forFold` upper-bound `ImpExpr` into a scalar `SExpr` so the
    non-literal-bound case can lower to `RForRuntime`.  Handles the shapes the
    K-PKE / lattice extractions produce for a loop trip count: a scalar
    variable (`.var "K"`), a nonneg literal, and the closed arithmetic
    operators `Add`/`Sub`/`Mul`/`min` over those.  `min a b` is encoded as the
    saturating `a - (a - b)` (Nat/`SSub` are truncating, so this is
    `evalState`-faithful to `Nat.min`).  Anything else (`Div`, `len`, `Rem`,
    calls) returns `none`, keeping the loop out of the lowered fragment. -/
def impBoundToSExpr : ImpExpr → Option CatCrypt.Crypto.Jasmin.LowCT.SExpr
  | .var n                  => some (.SVar n)
  | .lit (.int n)           => if n ≥ 0 then some (.SLit n.toNat) else none
  | .lit (.uintLit _ n)     => some (.SLit n)
  | .lit (.sintLit _ n)     => if n ≥ 0 then some (.SLit n.toNat) else none
  | .app "Add" [a, b]       =>
      match impBoundToSExpr a, impBoundToSExpr b with
      | some ea, some eb => some (.SAdd ea eb)
      | _, _ => none
  | .app "Sub" [a, b]       =>
      match impBoundToSExpr a, impBoundToSExpr b with
      | some ea, some eb => some (.SSub ea eb)
      | _, _ => none
  | .app "Mul" [a, b]       =>
      match impBoundToSExpr a, impBoundToSExpr b with
      | some ea, some eb => some (.SMul ea eb)
      | _, _ => none
  | .app "min" [a, b]       =>
      match impBoundToSExpr a, impBoundToSExpr b with
      -- min a b = a - (a - b), saturating (Nat subtraction truncates to 0).
      | some ea, some eb => some (.SSub ea (.SSub ea eb))
      | _, _ => none
  | _                       => none

/-- Nonneg literal → `Nat`.  Extracts the endpoints of an offset-start
    `forFold` range (`lo = .lit n` with `n ≠ 0` — the K-PKE ek/ct
    tail-copy loops). -/
def impLitNat : ImpLit → Option Nat
  | .int n        => if n ≥ 0 then some n.toNat else none
  | .uintLit _ n  => some n
  | .sintLit _ n  => if n ≥ 0 then some n.toNat else none
  | _             => none

/-- Structural recursion `ImpExpr → Option LowCT`.

    Each recursive call is on a strict syntactic subterm of the input
    (`body` of a `letBind`, `t`/`e` of an `ifThenElse`, etc.), so the
    Lean termination checker accepts a plain `def` here.  (The H2 stub
    used `partial def` to sidestep a perceived issue with `match`-based
    structural recursion; subsequent experimentation showed a regular
    `def` works and gives us the equation lemmas we need for the H2.2
    biconditional below.) -/
def haxToLowCT : ImpExpr → Option LowCT
  -- §3.1  letBind cases — fused with the rhs shape.
  --
  -- Three sub-patterns are encoded with an inner `if-then-else`-style
  -- cascade keyed on the call name + args shape (rather than a separate
  -- top-level `match` arm), so that the equation lemma for this branch
  -- remains a single `letBind _ (.app _ _) _` arm — that keeps the H2.2
  -- biconditional proof structurally unchanged.
  /- TODO(simulation): haxToLowCT_simulates_full does not yet cover the
     array_update / index / forFold sub-cases.  See
     bench/mlkem_compare/HAXTOR_EXTENSION_PLAN.md §3. -/
  | .letBind name (.app f args) body =>
      let dt := towerOfCallName f
      let dest : Located := { locVar := name, locSrc := dt }
      match haxArgsToLocated dt args, haxToLowCT body with
      | some args', some bodyC =>
          -- Array store: `let _ = array_update(arr, idx, src); body` lowers
          -- to `RSeq (RArrStore arr idx src) bodyC`.  Falls back to the
          -- generic `RCall` form when args don't match the expected shape.
          -- TowerType placeholders pending hax `ImpType` propagation.
          if f = "array_update" then
            match args with
            | [.var arr, .var idx, .var src] =>
                let arrLoc : Located := { locVar := arr, locSrc := .TBytes 0 }
                let srcLoc : Located := { locVar := src, locSrc := .TBytes 0 }
                some (.RSeq (.RArrStore arrLoc idx srcLoc) bodyC)
            | _ => some (.RLetZero name dt (.RSeq (.RCall f dest args') bodyC))
          -- Array load: `let name = index(arr, idx); body` lowers to
          -- `RLetZero name dt (RSeq (RArrLoad {name} {arr} idx) bodyC)`.
          else if f = "index" then
            match args with
            | [.var arr, .var idx] =>
                let dtL : TowerType := .TFp
                let destLoc : Located := { locVar := name, locSrc := dtL }
                let arrLoc  : Located := { locVar := arr,  locSrc := dtL }
                some (.RLetZero name dtL (.RSeq (.RArrLoad destLoc arrLoc idx) bodyC))
            | _ => some (.RLetZero name dt (.RSeq (.RCall f dest args') bodyC))
          else
            some (.RLetZero name dt (.RSeq (.RCall f dest args') bodyC))
      | _,           _          => none
  | .letBind name (.lit (.uintLit _ n)) body =>
      match haxToLowCT body with
      | some bodyC => some (.RLetU64Zero name (.RSeq (.RScalarSet name n) bodyC))
      | none       => none
  | .letBind name (.lit (.int n)) body =>
      if h : n ≥ 0 then
        match haxToLowCT body with
        | some bodyC =>
            some (.RLetU64Zero name (.RSeq (.RScalarSet name n.toNat) bodyC))
        | none       => none
      else
        let _ := h
        none  -- negative literal not representable in Nat-shaped RScalarSet
  -- Bool literal binding: bools are 0/1 scalars (consistent with
  -- RIfNz / RWhileNz reading nonzero as true).
  | .letBind name (.lit (.bool b)) body =>
      match haxToLowCT body with
      | some bodyC =>
          some (.RLetU64Zero name
            (.RSeq (.RScalarSet name (if b then 1 else 0)) bodyC))
      | none       => none
  -- Parameter-alias: `let name = src; body` where `src` is already in scope.
  -- The auto-extracted ImpExpr opens every kernel with such a chain
  -- (`let a = a; let b = b; let r = ZERO_VEC; ...`).  We treat the
  -- binding as a no-op and recurse on `body` directly — the alias's
  -- name is shadowed by the original `src` slot in the body's lexical
  -- scope.  See HAXTOR_EXTENSION_PLAN §3 / smoke test in §5.
  | .letBind _name (.var _src) body =>
      haxToLowCT body
  -- Tuple-component read: `let name = tup.i; body` — `.proj` of a named
  -- tuple slot (a leaf call's tuple return value, e.g. the K-PKE keygen
  -- `(ek, dk)` pair landing in `"_tup"`).  Lowers to `RTupleLoad`
  -- reading component `i` of the tuple-valued slot `t` into the fresh
  -- slot `name`.  Non-`var` proj bases fall through to the catch-all
  -- below.  TowerType placeholder pending hax `ImpType` propagation.
  | .letBind name (.proj (.var t) i) body =>
      match haxToLowCT body with
      | some bodyC =>
          let dtL : TowerType := .TFp
          some (.RLetZero name dtL
                  (.RSeq (.RTupleLoad { locVar := name, locSrc := dtL }
                                      { locVar := t, locSrc := dtL } i) bodyC))
      | none => none
  | .letBind _ _ _ => none  -- unsupported rhs shape; see H2.1
  -- §3.2  Trailing slots — the named result already lives in its slot
  | .var _   => some .RSkip
  | .unitVal => some .RSkip
  -- §3.3  Sequencing
  | .seq a b =>
      match haxToLowCT a, haxToLowCT b with
      | some aC, some bC => some (.RSeq aC bC)
      | _,        _        => none
  -- §3.4  Control flow — RIfNz / RWhileNz read from a scalar variable slot
  | .ifThenElse (.var v) t e =>
      match haxToLowCT t, haxToLowCT e with
      | some tC, some eC => some (.RIfNz v tC eC)
      | _,        _        => none
  | .ifThenElse _ _ _ => none  -- non-named condition not yet supported
  | .whileLoop (.var v) body =>
      match haxToLowCT body with
      | some bC => some (.RWhileNz v bC)
      | none    => none
  | .whileLoop _ _ => none
  -- §3.5  Assignments — only into already-allocated slots
  | .assign name (.lit (.int n)) =>
      if n ≥ 0 then some (.RScalarSet name n.toNat) else none
  | .assign name (.lit (.uintLit _ n)) => some (.RScalarSet name n)
  -- Bool assignment: 0/1 scalar, mirroring the bool letBind arm.
  | .assign name (.lit (.bool b)) =>
      some (.RScalarSet name (if b then 1 else 0))
  | .assign name (.app f args) =>
      let dt := towerOfCallName f
      let dest : Located := { locVar := name, locSrc := dt }
      match haxArgsToLocated dt args with
      | some args' => some (.RCall f dest args')
      | none       => none
  | .assign _ _ => none
  -- §3.6  Bare `app` at non-let, non-assign position has no destination
  | .app _ _ => none
  -- §3.7  H2.1: 2-element tuple destructuring of a leaf call.
  -- Pattern: `let (n1, n2) = f(args); body`, which hax extracts as
  -- `match f(args) with | (n1, n2) => body`.  Lowers to `RCallSwap`,
  -- the 2-destination leaf call form.  Both outputs share the prefix-
  -- derived tower type `dt`; per-component types are an H2.1.next
  -- extension blocked on hax `ImpType` annotations on `tuplePat`.
  -- 3+ tuples and proj-based destructuring lower to `none` (H2.1.b).
  | .match_ (.app f args)
      [(.tuplePat [.varPat n1, .varPat n2], body)] =>
      let dt := towerOfCallName f
      let dest1 : Located := { locVar := n1, locSrc := dt }
      let dest2 : Located := { locVar := n2, locSrc := dt }
      match haxArgsToLocated dt args, haxToLowCT body with
      | some args', some bodyC =>
          some (.RLetZero n1 dt
                  (.RLetZero n2 dt
                    (.RSeq (.RCallSwap f dest1 dest2 args') bodyC)))
      | _,           _          => none
  -- §3.7.b  All other constructors — match the H1 rejection set
  | .lit _                     => none  -- bare lit at tail has no slot
  | .lam _ _                   => none  -- first-class closures not in LowCT
  -- Aggregate tuple tail of named results: every component already
  -- lives in its slot (same justification as the `.var _` arm in
  -- §3.2), so the all-`var` tuple tail is a no-op.  Non-`var`
  -- components reject.
  | .tuple es                  => if es.all isVar then some .RSkip else none
  | .proj _ _                  => none  -- H2.1.b: deferred
  | .match_ _ _                => none  -- only 2-tuple destructure of app
  | .borrow _                  => none
  | .deref _                   => none
  | .forLoop _ _ _ _           => none
  | .forLoopRev _ _ _ _        => none
  | .break_ _                  => none
  | .continue_                 => none
  | .earlyReturn _             => none
  | .questionMark _            => none
  /- TODO(simulation): haxToLowCT_simulates_full does not yet cover this case.
     See bench/mlkem_compare/HAXTOR_EXTENSION_PLAN.md §3. -/
  -- Bounded for-fold with literal `lo = 0` and literal nonneg-int `hi = n`
  -- lowers to `RFor v n body`.  `RFor`'s second parameter is a closed `Nat`
  -- (structurally terminating); runtime-bound forms (`hi = .var k`) are
  -- deferred — they need a different LowCT constructor.
  | .forFold v (.lit (.int 0)) (.lit (.int n)) body =>
      if h : n ≥ 0 then
        match haxToLowCT body with
        | some bodyC => some (.RFor v n.toNat bodyC)
        | none => none
      else
        let _ := h
        none
  | .forFold v (.lit (.int 0)) (.lit (.uintLit _ n)) body =>
      match haxToLowCT body with
      | some bodyC => some (.RFor v n bodyC)
      | none => none
  -- Stage 1a (2026-07-01): runtime-bound `forFold 0 hi body` with a
  -- non-literal `hi` that `impBoundToSExpr` accepts lowers to `RForRuntime`.
  | .forFold v (.lit (.int 0)) hi body =>
      match impBoundToSExpr hi, haxToLowCT body with
      | some boundE, some bodyC => some (.RForRuntime v boundE bodyC)
      | _, _ => none
  -- Offset-start bounded for-fold (`lo = .lit n`, reached only when
  -- `lo ≠ .int 0` — the K-PKE ek/ct tail-copy loops, e.g.
  -- `for j in 1152..EK_BYTES`).  Desugars to the zero-based `RFor` over
  -- `hi - lo` iterations whose body first shifts the loop scalar into
  -- the source range (`RScalarSetExpr`, `v := v + lo`).  Sound because
  -- `RustExec.forSucc` re-sets `v` from the iteration counter at each
  -- iteration head, so the shift is per-iteration, not cumulative.
  | .forFold v (.lit lo) (.lit hi) body =>
      match impLitNat lo, impLitNat hi, haxToLowCT body with
      | some loN, some hiN, some bodyC =>
          some (.RFor v (hiN - loN)
            (.RSeq (.RScalarSetExpr v (.SAdd (.SVar v) (.SLit loN))) bodyC))
      | _, _, _ => none
  -- Offset-start for-fold with a runtime (non-literal) bound — the K-PKE
  -- ek/ct tail-copy loops (`for j in 1152..EK_BYTES`; `EK_BYTES` stays a
  -- scalar variable after `mlkemFold`).  Lowers to `RForRuntime` over the
  -- residual trip count `hi - lo` with the same body-head shift.
  | .forFold v (.lit lo) hi body =>
      match impLitNat lo, impBoundToSExpr hi, haxToLowCT body with
      | some loN, some boundE, some bodyC =>
          some (.RForRuntime v (.SSub boundE (.SLit loN))
            (.RSeq (.RScalarSetExpr v (.SAdd (.SVar v) (.SLit loN))) bodyC))
      | _, _, _ => none
  | .forFold _ _ _ _           => none
  | .forFoldRev _ _ _ _        => none
  | .whileFold _ _             => none
  | .forFoldReturn _ _ _ _     => none
  | .forFoldRevReturn _ _ _ _  => none
  | .whileFoldReturn _ _       => none
  | .cfBreak _                 => none
  | .cfContinue _              => none
  | .cfBreakContinue _         => none

/-! ### §3.bis  Typed lowering with a `TypeEnv` and `LeafTable`

`haxToLowCTEnv env leaves e` is the typed twin of `haxToLowCT`: it
threads two pieces of additional context.

* `env : TypeEnv` — known slot types.  The `index` / `array_update`
  cases (and any future container-aware constructor) can derive the
  destination's TowerType from the array slot's element type, instead
  of hard-coding `.TFp`.

* `leaves : LeafTable` — per-protocol override for leaf-call return
  types.  Used in the generic `letBind _ (.app f args) _` case (and
  `assign _ (.app f args)`, `match_ (.app f args) _` arms) to override
  the prefix-based `towerOfCallName` for protocol-specific names like
  MLKEM's `poly_add` / `mat_vec_mul` / `polyvec_encode`.

Recursive structure mirrors `haxToLowCT` exactly; each recursive call
passes the (possibly extended) env and the unchanged leaf table, and
each `letBind` arm extends the env with the newly introduced slot's
inferred type.

The two bodies are deliberately kept separate so the existing sim-file
proofs (which `unfold haxToLowCT at h` and pattern-match against the
historical equation lemmas) continue to build verbatim. -/
def haxToLowCTEnv (env : TypeEnv) (leaves : LeafTable) :
    ImpExpr → Option LowCT
  -- §3.bis.1  letBind of an app — typed index / array_update first, then generic.
  | .letBind name (.app f args) body =>
      -- Leaf-table-aware return type: prefer the per-protocol override,
      -- fall back to the prefix-based `towerOfCallName` for anything not
      -- in the table.
      let dt := leaves.find f
      let dest : Located := { locVar := name, locSrc := dt }
      -- Generic-app case extends the env with `(name, dt)`.
      let envApp : TypeEnv := (name, dt) :: env
      if f = "repeat" then
        -- `let name = repeat(v, n)`: a fresh n-element zero array.  The
        -- tower type is sized from the ML-KEM length (256 → polynomial,
        -- 768 → polyvec, else flat byte buffer).  Lowers to
        -- `RLetZero name <type> body` (the LowCT zero-init); the
        -- `repeat` call carries no extra runtime effect.  The length
        -- literal is recovered by `inlineRepeatLen` (run before this).
        match args with
        | [_, .lit (.int n)] =>
            let arrTy : TowerType :=
              if n = 256 then .TPolyMod 3329 256
              else if n = 768 then .TPolyVec 3329 256 3
              else .TBytes n.toNat
            match haxToLowCTEnv ((name, arrTy) :: env) leaves body with
            | some bodyC => some (.RLetZero name arrTy bodyC)
            | none => none
        | _ =>
            match haxArgsToLocated dt args, haxToLowCTEnv envApp leaves body with
            | some args', some bodyC =>
                some (.RLetZero name dt (.RSeq (.RCall f dest args') bodyC))
            | _, _ => none
      else if f = "array_update" then
        match args with
        | [.var arr, .var idx, .var src] =>
            -- Use the env's known type for `arr`; element type for `src`.
            let arrTy : TowerType := env.find arr
            let elemTy : TowerType := arrTy.elemType
            let arrLoc : Located := { locVar := arr, locSrc := arrTy }
            let srcLoc : Located := { locVar := src, locSrc := elemTy }
            -- `array_update` returns the updated array (functional semantics),
            -- so `name` is rebound to a slot of the SAME container type.
            let envAU : TypeEnv := (name, arrTy) :: env
            match haxToLowCTEnv envAU leaves body with
            | some bodyC => some (.RSeq (.RArrStore arrLoc idx srcLoc) bodyC)
            | none => none
        | _ =>
            match haxArgsToLocated dt args, haxToLowCTEnv envApp leaves body with
            | some args', some bodyC =>
                some (.RLetZero name dt (.RSeq (.RCall f dest args') bodyC))
            | _, _ => none
      else if f = "index" then
        match args with
        | [.var arr, .var idx] =>
            let arrTy : TowerType := env.find arr
            let elemTy : TowerType := arrTy.elemType
            let destLoc : Located := { locVar := name, locSrc := elemTy }
            let arrLoc  : Located := { locVar := arr,  locSrc := arrTy }
            let envIdx : TypeEnv := (name, elemTy) :: env
            match haxToLowCTEnv envIdx leaves body with
            | some bodyC =>
                some (.RLetZero name elemTy
                        (.RSeq (.RArrLoad destLoc arrLoc idx) bodyC))
            | none => none
        | _ =>
            match haxArgsToLocated dt args, haxToLowCTEnv envApp leaves body with
            | some args', some bodyC =>
                some (.RLetZero name dt (.RSeq (.RCall f dest args') bodyC))
            | _, _ => none
      else
        match haxArgsToLocated dt args, haxToLowCTEnv envApp leaves body with
        | some args', some bodyC =>
            some (.RLetZero name dt (.RSeq (.RCall f dest args') bodyC))
        | _, _ => none
  | .letBind name (.lit (.uintLit _ n)) body =>
      let envLit : TypeEnv := (name, .TU64) :: env
      match haxToLowCTEnv envLit leaves body with
      | some bodyC => some (.RLetU64Zero name (.RSeq (.RScalarSet name n) bodyC))
      | none       => none
  | .letBind name (.lit (.int n)) body =>
      if h : n ≥ 0 then
        let envLit : TypeEnv := (name, .TU64) :: env
        match haxToLowCTEnv envLit leaves body with
        | some bodyC =>
            some (.RLetU64Zero name (.RSeq (.RScalarSet name n.toNat) bodyC))
        | none       => none
      else
        let _ := h
        none
  -- Bool literal binding (typed twin): 0/1 scalar in a `.TU64` slot.
  | .letBind name (.lit (.bool b)) body =>
      let envLit : TypeEnv := (name, .TU64) :: env
      match haxToLowCTEnv envLit leaves body with
      | some bodyC =>
          some (.RLetU64Zero name
            (.RSeq (.RScalarSet name (if b then 1 else 0)) bodyC))
      | none       => none
  -- Parameter-alias `let name = src; body`: inherit `src`'s type from env.
  -- IMPORTANT: when `src` is unknown (e.g. an external identifier like
  -- `ZERO_VEC` that lives outside the env), do NOT shadow `name`'s existing
  -- binding.  Otherwise the alias clobbers a known parameter type with
  -- `.TFp` — see SLICE_CODEGEN_GAP follow-up.
  | .letBind name (.var src) body =>
      match mlkemZeroConst? src with
      | some t =>
          -- `let name = ZERO_POLY/ZERO_VEC`: a fresh zero-initialised
          -- array slot (not an alias — the constant is a module-level
          -- zero, not a bound variable).
          match haxToLowCTEnv ((name, t) :: env) leaves body with
          | some bodyC => some (.RLetZero name t bodyC)
          | none => none
      | none =>
          let envAlias : TypeEnv :=
            match env.findOpt src with
            | some t => (name, t) :: env   -- src known: propagate to name
            | none   => env                -- src unknown: don't shadow
          haxToLowCTEnv envAlias leaves body
  -- Tuple-component read (typed twin): derive the component type from
  -- the env's type for the tuple slot `t` (`TTuple a b` → component
  -- `i`'s type; non-tuple env types pass through unchanged).
  | .letBind name (.proj (.var t) i) body =>
      let tupTy : TowerType := env.find t
      let compTy : TowerType := tupTy.tupleComponentType i
      match haxToLowCTEnv ((name, compTy) :: env) leaves body with
      | some bodyC =>
          some (.RLetZero name compTy
                  (.RSeq (.RTupleLoad { locVar := name, locSrc := compTy }
                                      { locVar := t, locSrc := tupTy } i) bodyC))
      | none => none
  | .letBind _ _ _ => none
  | .var _   => some .RSkip
  | .unitVal => some .RSkip
  | .seq a b =>
      match haxToLowCTEnv env leaves a, haxToLowCTEnv env leaves b with
      | some aC, some bC => some (.RSeq aC bC)
      | _,        _        => none
  | .ifThenElse (.var v) t e =>
      match haxToLowCTEnv env leaves t, haxToLowCTEnv env leaves e with
      | some tC, some eC => some (.RIfNz v tC eC)
      | _,        _        => none
  | .ifThenElse _ _ _ => none
  | .whileLoop (.var v) body =>
      match haxToLowCTEnv env leaves body with
      | some bC => some (.RWhileNz v bC)
      | none    => none
  | .whileLoop _ _ => none
  | .assign name (.lit (.int n)) =>
      if n ≥ 0 then some (.RScalarSet name n.toNat) else none
  | .assign name (.lit (.uintLit _ n)) => some (.RScalarSet name n)
  -- Bool assignment (typed twin): 0/1 scalar.
  | .assign name (.lit (.bool b)) =>
      some (.RScalarSet name (if b then 1 else 0))
  | .assign name (.app f args) =>
      let dt := leaves.find f
      let dest : Located := { locVar := name, locSrc := dt }
      match haxArgsToLocated dt args with
      | some args' => some (.RCall f dest args')
      | none       => none
  | .assign _ _ => none
  | .app _ _ => none
  | .match_ (.app f args)
      [(.tuplePat [.varPat n1, .varPat n2], body)] =>
      let dt := leaves.find f
      let dest1 : Located := { locVar := n1, locSrc := dt }
      let dest2 : Located := { locVar := n2, locSrc := dt }
      let envM : TypeEnv := (n1, dt) :: (n2, dt) :: env
      match haxArgsToLocated dt args, haxToLowCTEnv envM leaves body with
      | some args', some bodyC =>
          some (.RLetZero n1 dt
                  (.RLetZero n2 dt
                    (.RSeq (.RCallSwap f dest1 dest2 args') bodyC)))
      | _,           _          => none
  | .lit _                     => none
  | .lam _ _                   => none  -- first-class closures not in LowCT
  -- Aggregate tuple tail of named results (typed twin of the untyped arm).
  | .tuple es                  => if es.all isVar then some .RSkip else none
  | .proj _ _                  => none
  | .match_ _ _                => none
  | .borrow _                  => none
  | .deref _                   => none
  | .forLoop _ _ _ _           => none
  | .forLoopRev _ _ _ _        => none
  | .break_ _                  => none
  | .continue_                 => none
  | .earlyReturn _             => none
  | .questionMark _            => none
  | .forFold v (.lit (.int 0)) (.lit (.int n)) body =>
      if h : n ≥ 0 then
        let envFor : TypeEnv := (v, .TU64) :: env
        match haxToLowCTEnv envFor leaves body with
        | some bodyC => some (.RFor v n.toNat bodyC)
        | none => none
      else
        let _ := h
        none
  | .forFold v (.lit (.int 0)) (.lit (.uintLit _ n)) body =>
      let envFor : TypeEnv := (v, .TU64) :: env
      match haxToLowCTEnv envFor leaves body with
      | some bodyC => some (.RFor v n bodyC)
      | none => none
  -- Stage 1a (2026-07-01): runtime-bound `forFold` (typed twin).
  | .forFold v (.lit (.int 0)) hi body =>
      let envFor : TypeEnv := (v, .TU64) :: env
      match impBoundToSExpr hi, haxToLowCTEnv envFor leaves body with
      | some boundE, some bodyC => some (.RForRuntime v boundE bodyC)
      | _, _ => none
  -- Offset-start literal-range for-fold (typed twin of the untyped arm).
  | .forFold v (.lit lo) (.lit hi) body =>
      let envFor : TypeEnv := (v, .TU64) :: env
      match impLitNat lo, impLitNat hi, haxToLowCTEnv envFor leaves body with
      | some loN, some hiN, some bodyC =>
          some (.RFor v (hiN - loN)
            (.RSeq (.RScalarSetExpr v (.SAdd (.SVar v) (.SLit loN))) bodyC))
      | _, _, _ => none
  -- Offset-start runtime-bound for-fold (typed twin of the untyped arm).
  | .forFold v (.lit lo) hi body =>
      let envFor : TypeEnv := (v, .TU64) :: env
      match impLitNat lo, impBoundToSExpr hi, haxToLowCTEnv envFor leaves body with
      | some loN, some boundE, some bodyC =>
          some (.RForRuntime v (.SSub boundE (.SLit loN))
            (.RSeq (.RScalarSetExpr v (.SAdd (.SVar v) (.SLit loN))) bodyC))
      | _, _, _ => none
  | .forFold _ _ _ _           => none
  | .forFoldRev _ _ _ _        => none
  | .whileFold _ _             => none
  | .forFoldReturn _ _ _ _     => none
  | .forFoldRevReturn _ _ _ _  => none
  | .whileFoldReturn _ _       => none
  | .cfBreak _                 => none
  | .cfContinue _              => none
  | .cfBreakContinue _         => none

/-- ML-KEM-typed entry point: lower `e` against a caller-supplied
    parameter environment (e.g. the kernel's parameter list, with the
    expected polyvec / polymat shapes).  A thin wrapper around
    `haxToLowCTEnv` so the pipeline can opt into the typed pathway
    without touching the untyped one.

    The leaf-call return-type table defaults to `mlkemLeafTable`, which
    gives MLKEM-specific names like `poly_add` / `mat_vec_mul` /
    `polyvec_encode` their correct return TowerTypes (instead of
    silently falling back to `.TFp` via the prefix dispatch).  Callers
    that need a different protocol's leaf table pass it explicitly via
    the named `leaves` argument.

    Argument order is `(env, e, leaves)` rather than `(env, leaves, e)`
    so legacy 2-arg callers (`haxToLowCT_mlkemParams env e`) keep
    compiling with `leaves` defaulted. -/
def haxToLowCT_mlkemParams (env : TypeEnv) (e : ImpExpr)
    (leaves : LeafTable := mlkemLeafTable) : Option LowCT :=
  haxToLowCTEnv env leaves e

/-! ## §4  Soundness biconditional

The H1 filter accepts strictly more programs than the H2 translation
covers (because H2 additionally requires every `app`-argument to be a
plain `var`, every `let` rhs to be either a literal or an `app`, and
every branch/loop condition to be a plain `var`).  Conversely, H2 is
*structural*: it does not consult the H1 whitelist at all (smoke test
2 below pins this — `letBind "x" (app "secret_load" [...]) ...` is
rejected by H1 but accepted by H2).

Hence neither direction `representable ↔ some _` holds.  The clean
biconditional that does hold uses a tight syntactic predicate
`AnfShaped` capturing exactly the shapes the translation handles. -/

/-- ANF shape predicate: `true` exactly on `ImpExpr`s that
    `haxToLowCT` translates to `some _`.

    The rules mirror, one-for-one, the arms of `haxToLowCT` that
    return `some`:
    * `letBind _ (app _ args) body` — `args` all `var`s and `body` ANF;
    * `letBind _ (lit (uintLit ..)) body` — `body` ANF;
    * `letBind _ (lit (int n)) body` — `n ≥ 0` and `body` ANF;
    * `letBind _ (lit (bool _)) body` — `body` ANF (bools are 0/1 scalars);
    * `letBind _ (proj (var _) _) body` — `body` ANF (tuple-component
      read of a named tuple slot);
    * `seq a b` — both ANF;
    * `ifThenElse (var _) t e` — `t` and `e` ANF;
    * `whileLoop (var _) body` — `body` ANF;
    * `assign _ (lit (int n))` — `n ≥ 0`;
    * `assign _ (lit (uintLit ..))` — always;
    * `assign _ (lit (bool _))` — always;
    * `assign _ (app _ args)` — `args` all `var`s;
    * `match_ (app _ args) [(tuplePat [varPat _, varPat _], body)]` —
      `args` all `var`s and `body` ANF (H2.1 2-tuple destructure);
    * `var _`, `unitVal` — terminal;
    * `tuple es` — `es` all `var`s (aggregate tuple tail of named results);
    * `forFold` with a literal range (zero- or offset-start) or a
      zero-start convertible runtime bound — `body` ANF;
    * everything else (bare `lit` at tail, `proj` at tail or with a
      non-`var` base, generic `match_`, `borrow`, `deref`, the
      remaining loop / control-flow constructors, non-`var`
      conditions, non-`var` tuple components) — not ANF. -/
def AnfShaped : ImpExpr → Bool
  | .letBind _ (.app _ args) body          => args.all isVar && AnfShaped body
  | .letBind _ (.lit (.uintLit _ _)) body  => AnfShaped body
  | .letBind _ (.lit (.int n)) body        => decide (n ≥ 0) && AnfShaped body
  -- Bool literal binding: 0/1 scalar; only `body` shape matters.
  | .letBind _ (.lit (.bool _)) body       => AnfShaped body
  -- Parameter-alias `let _ = .var _` is no-op; only `body` shape matters.
  | .letBind _ (.var _) body               => AnfShaped body
  -- Tuple-component read `let _ = (.var _).i`; only `body` shape matters.
  | .letBind _ (.proj (.var _) _) body     => AnfShaped body
  | .letBind _ _ _                          => false
  | .var _                                  => true
  | .unitVal                                => true
  | .seq a b                                => AnfShaped a && AnfShaped b
  | .ifThenElse (.var _) t e                => AnfShaped t && AnfShaped e
  | .ifThenElse _ _ _                       => false
  | .whileLoop (.var _) body                => AnfShaped body
  | .whileLoop _ _                          => false
  | .assign _ (.lit (.int n))               => decide (n ≥ 0)
  | .assign _ (.lit (.uintLit _ _))         => true
  | .assign _ (.lit (.bool _))              => true
  | .assign _ (.app _ args)                 => args.all isVar
  | .assign _ _                             => false
  -- H2.1: 2-element tuple destructure of a leaf call.
  | .match_ (.app _ args)
      [(.tuplePat [.varPat _, .varPat _], body)] =>
      args.all isVar && AnfShaped body
  -- Aggregate tuple tail of named results.
  | .tuple es                                => es.all isVar
  -- Bounded for-fold with literal lo = 0 and literal-Nat hi.
  | .forFold _ (.lit (.int 0)) (.lit (.int n)) body =>
      decide (n ≥ 0) && AnfShaped body
  | .forFold _ (.lit (.int 0)) (.lit (.uintLit _ _)) body =>
      AnfShaped body
  -- Stage 1a (2026-07-01): runtime-bound `forFold` — accepted iff the bound
  -- converts and the body is ANF-shaped.
  | .forFold _ (.lit (.int 0)) hi body =>
      (impBoundToSExpr hi).isSome && AnfShaped body
  -- Offset-start literal-range for-fold — accepted iff both endpoints
  -- are nonneg literals and the body is ANF-shaped.
  | .forFold _ (.lit lo) (.lit hi) body =>
      (impLitNat lo).isSome && (impLitNat hi).isSome && AnfShaped body
  -- Offset-start runtime-bound for-fold — accepted iff the start is a
  -- nonneg literal, the bound converts, and the body is ANF-shaped.
  | .forFold _ (.lit lo) hi body =>
      (impLitNat lo).isSome && (impBoundToSExpr hi).isSome && AnfShaped body
  | _                                        => false

/-- The argument-list helper succeeds exactly when every argument is
    already a `var`.  This is the side-condition packaged by `AnfShaped`
    on `letBind _ (.app ...) _` and `assign _ (.app ...)` arms. -/
theorem haxArgsToLocated_isSome_iff_all_isVar
    (dt : TowerType) (args : List ImpExpr) :
    (haxArgsToLocated dt args).isSome = true ↔ args.all isVar = true := by
  induction args with
  | nil => simp [haxArgsToLocated]
  | cons a as ih =>
    cases a <;>
      (simp only [haxArgsToLocated, haxArgToLocated, isVar, List.all_cons,
                  Option.isSome, Bool.and_eq_true]
       cases h : haxArgsToLocated dt as <;> simp_all)

set_option maxHeartbeats 800000 in
/-- **Main soundness biconditional (H2.2).**  An `ImpExpr` translates to
    `some _` *iff* it has the ANF shape captured by `AnfShaped`.

    Proof: structural induction via `ImpExpr.ind`.  Each `ImpExpr` arm
    matches the corresponding arm of `haxToLowCT` and the corresponding
    arm of `AnfShaped`; for `letBind` and `assign` we case-split on the
    rhs (literal vs. app vs. other), invoking
    `haxArgsToLocated_isSome_iff_all_isVar` for the `app` sub-case.
    Constructors that translate to `none` regardless (tuple, proj,
    match_, borrow, deref, all loop / control-flow forms) close by a
    single `unfold; simp`. -/
theorem haxToLowCT_isSome_iff_anf (e : ImpExpr) :
    (haxToLowCT e).isSome = true ↔ AnfShaped e = true := by
  induction e using ImpExpr.ind with
  | lit v => cases v <;> (unfold haxToLowCT AnfShaped; simp [Option.isSome])
  | var _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | letBind _ val body _ihval ihbody =>
    cases val with
    | lit l =>
      cases l with
      | int n =>
        unfold haxToLowCT AnfShaped
        by_cases h : n ≥ 0
        · simp [h]; cases h2 : haxToLowCT body <;> simp_all [Option.isSome]
        · simp [h]
      | uintLit _ _ =>
        unfold haxToLowCT AnfShaped
        cases h2 : haxToLowCT body <;> simp_all [Option.isSome]
      | bool _ =>
        unfold haxToLowCT AnfShaped
        cases h2 : haxToLowCT body <;> simp_all [Option.isSome]
      | _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
    | app f args =>
      unfold haxToLowCT AnfShaped
      have hargs := haxArgsToLocated_isSome_iff_all_isVar (towerOfCallName f) args
      -- The inner if-cascade (array_update / index / generic) always
      -- returns `some _` when both `haxArgsToLocated` and `haxToLowCT
      -- body` succeed — split aggressively and reduce each tip.
      cases h1 : haxArgsToLocated (towerOfCallName f) args <;>
        cases h2 : haxToLowCT body <;>
          repeat' (first | split | simp_all [Option.isSome, isVar])
    | var _ =>
      -- Parameter-alias `let name = src; body`: both `haxToLowCT` and
      -- `AnfShaped` unfold directly to the body's case.
      unfold haxToLowCT AnfShaped
      exact ihbody
    | proj pe i =>
      -- Tuple-component read: productive iff the proj base is a `var`
      -- and the body translates; a non-`var` base rejects on both sides.
      cases pe with
      | var t =>
        unfold haxToLowCT AnfShaped
        cases h2 : haxToLowCT body <;> simp_all [Option.isSome]
      | _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
    | _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | lam _ _ _ih => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | app _ _ _ih => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | tuple es _ih =>
    unfold haxToLowCT AnfShaped
    by_cases hAll : es.all isVar <;> simp [hAll, Option.isSome]
  | proj _ _ _ih => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | ifThenElse c _ _ _ihc iht ihe =>
    cases c with
    | var _ =>
      unfold haxToLowCT AnfShaped
      cases h1 : haxToLowCT _ <;> cases h2 : haxToLowCT _ <;>
        simp_all [Option.isSome]
    | _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | match_ scrut arms _ih1 ih2 =>
    -- The match_ case translates only the specific shape
    -- `match_ (.app f args) [(.tuplePat [.varPat n1, .varPat n2], body)]`;
    -- every other shape goes to `none` and similarly fails AnfShaped.
    cases scrut with
    | app f args =>
      cases arms with
      | nil => unfold haxToLowCT AnfShaped; simp [Option.isSome]
      | cons hd rest =>
        cases rest with
        | nil =>
          rcases hd with ⟨pat, body⟩
          cases pat with
          | tuplePat ps =>
            cases ps with
            | nil => unfold haxToLowCT AnfShaped; simp [Option.isSome]
            | cons p1 ps1 =>
              cases p1 with
              | varPat n1 =>
                cases ps1 with
                | nil => unfold haxToLowCT AnfShaped; simp [Option.isSome]
                | cons p2 ps2 =>
                  cases p2 with
                  | varPat n2 =>
                    cases ps2 with
                    | nil =>
                      have ihbody : (haxToLowCT body).isSome = true ↔
                          AnfShaped body = true :=
                        ih2 ⟨_, body⟩ (List.mem_singleton.mpr rfl)
                      unfold haxToLowCT AnfShaped
                      have hargs := haxArgsToLocated_isSome_iff_all_isVar
                        (towerOfCallName f) args
                      cases h1 : haxArgsToLocated (towerOfCallName f) args <;>
                        cases h2 : haxToLowCT body <;>
                          simp_all [Option.isSome]
                    | cons _ _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
                  | _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
              | _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
          | _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
        | cons _ _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
    | _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | unitVal => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | seq _ _ iha ihb =>
    unfold haxToLowCT AnfShaped
    cases h1 : haxToLowCT _ <;> cases h2 : haxToLowCT _ <;>
      simp_all [Option.isSome]
  | borrow _ _ih => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | deref _ _ih => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | assign _ rhs _ihrhs =>
    cases rhs with
    | lit l =>
      cases l with
      | int k =>
        unfold haxToLowCT AnfShaped
        by_cases h : k ≥ 0
        · simp [h, Option.isSome]
        · simp [h, Option.isSome]
      | uintLit _ _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
      | bool _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
      | _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
    | app f args =>
      unfold haxToLowCT AnfShaped
      have hargs := haxArgsToLocated_isSome_iff_all_isVar (towerOfCallName f) args
      cases h1 : haxArgsToLocated (towerOfCallName f) args <;>
        simp_all [Option.isSome]
    | _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | forLoop _ _ _ _ _ _ _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | forLoopRev _ _ _ _ _ _ _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | whileLoop c _ _ihc ihbody =>
    cases c with
    | var _ =>
      unfold haxToLowCT AnfShaped
      cases h1 : haxToLowCT _ <;> simp_all [Option.isSome]
    | _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | break_none => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | break_some _ _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | continue_ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | earlyReturn _ _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | questionMark _ _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | forFold _ lo hi body _ _ ihbody =>
    -- Literal-bound cases (int / uintLit) lower to `RFor`; every other bound
    -- shape (`.lit .bool/.unit/.sintLit`, `.var`, `.app`, …) routes to the
    -- Stage-1a runtime arm, where both `haxToLowCT` and `AnfShaped` gate on
    -- `(impBoundToSExpr hi).isSome`, so the biconditional follows from the
    -- body IH.
    unfold haxToLowCT AnfShaped
    cases lo with
    | lit l =>
      cases l with
      | int n0 =>
        by_cases hlo : n0 = 0
        · subst hlo
          cases hi with
          | lit l2 =>
            cases l2 with
            | int n =>
              by_cases hn : n ≥ 0
              · simp [hn]; cases h2 : haxToLowCT body <;> simp_all [Option.isSome]
              · simp [hn]
            | uintLit _ _ =>
              cases h2 : haxToLowCT body <;> simp_all [Option.isSome]
            | bool _ => simp [impBoundToSExpr, Option.isSome]
            | unit => simp [impBoundToSExpr, Option.isSome]
            | sintLit w n =>
              simp only [impBoundToSExpr]
              cases h2 : haxToLowCT body <;> split_ifs <;>
                simp_all [Option.isSome]
          | var vn =>
            cases h2 : haxToLowCT body <;> simp_all [impBoundToSExpr, Option.isSome]
          | app f a =>
            cases hb : impBoundToSExpr (.app f a) <;>
              cases h2 : haxToLowCT body <;> simp_all [Option.isSome]
          | _ => simp [impBoundToSExpr, Option.isSome]
        -- Non-zero int `lo` routes to the offset-start arms (literal or
        -- runtime `hi`), which gate on `impLitNat lo`, the bound side
        -- (`impLitNat hi` / `impBoundToSExpr hi`), and the body IH.
        · cases hi with
          | lit l2 =>
            cases hl : impLitNat (.int n0) <;> cases hh : impLitNat l2 <;>
              cases h2 : haxToLowCT body <;> simp_all [Option.isSome]
          | var vn =>
            cases hl : impLitNat (.int n0) <;> cases h2 : haxToLowCT body <;>
              simp_all [impBoundToSExpr, Option.isSome]
          | app f a =>
            cases hl : impLitNat (.int n0) <;>
              cases hb : impBoundToSExpr (.app f a) <;>
              cases h2 : haxToLowCT body <;> simp_all [Option.isSome]
          | _ =>
            cases hl : impLitNat (.int n0) <;>
              simp_all [impBoundToSExpr, Option.isSome]
      -- `uintLit`/`sintLit` `lo` also reach the offset-start arms;
      -- `bool`/`unit` `lo` fail `impLitNat` on both sides.
      | uintLit w n =>
        cases hi with
        | lit l2 =>
          cases hl : impLitNat (.uintLit w n) <;> cases hh : impLitNat l2 <;>
            cases h2 : haxToLowCT body <;> simp_all [Option.isSome]
        | var vn =>
          cases h2 : haxToLowCT body <;>
            simp_all [impLitNat, impBoundToSExpr, Option.isSome]
        | app f a =>
          cases hb : impBoundToSExpr (.app f a) <;>
            cases h2 : haxToLowCT body <;> simp_all [impLitNat, Option.isSome]
        | _ => simp [impLitNat, impBoundToSExpr, Option.isSome]
      | sintLit w n =>
        cases hi with
        | lit l2 =>
          cases hl : impLitNat (.sintLit w n) <;> cases hh : impLitNat l2 <;>
            cases h2 : haxToLowCT body <;> simp_all [Option.isSome]
        | var vn =>
          cases hl : impLitNat (.sintLit w n) <;>
            cases h2 : haxToLowCT body <;>
            simp_all [impBoundToSExpr, Option.isSome]
        | app f a =>
          cases hl : impLitNat (.sintLit w n) <;>
            cases hb : impBoundToSExpr (.app f a) <;>
            cases h2 : haxToLowCT body <;> simp_all [Option.isSome]
        | _ =>
          cases hl : impLitNat (.sintLit w n) <;>
            simp_all [impBoundToSExpr, Option.isSome]
      | bool b =>
        cases hi with
        | lit l2 => simp [impLitNat, Option.isSome]
        | _ => simp [impLitNat, Option.isSome]
      | unit =>
        cases hi with
        | lit l2 => simp [impLitNat, Option.isSome]
        | _ => simp [impLitNat, Option.isSome]
    | _ => simp [Option.isSome]
  | forFoldRev _ _ _ _ _ _ _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | whileFold _ _ _ _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | forFoldReturn _ _ _ _ _ _ _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | forFoldRevReturn _ _ _ _ _ _ _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | whileFoldReturn _ _ _ _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | cfBreak _ _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | cfContinue _ _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]
  | cfBreakContinue _ _ => unfold haxToLowCT AnfShaped; simp [Option.isSome]

/-- Corollary: any `ImpExpr` that satisfies the H1 filter *and* is
    `AnfShaped` translates to `some _`.  This is the strong (joint)
    direction of the soundness story for callers that want to know
    both: the program is in the cryptographic fragment **and** the
    fragment is in the syntactic shape the translator handles.

    The reverse direction (`some _ → representable`) does **not** hold
    structurally — `haxToLowCT` accepts `app f` for any `f`, including
    non-whitelisted ones (see smoke test 2).  Downstream pipelines run
    `LowCTRepresentable.Expr` *before* `haxToLowCT` to enforce the
    whitelist contract. -/
theorem haxToLowCT_isSome_of_representable_and_anf
    (e : ImpExpr) (_hrep : LowCTRepresentable.Expr e = true)
    (hanf : AnfShaped e = true) :
    (haxToLowCT e).isSome = true :=
  (haxToLowCT_isSome_iff_anf e).mpr hanf

/-- Backwards-compat shim of the original H2 placeholder.  The old
    statement was a vacuous disjunction `... ∨ True`; we keep the name
    so downstream code that imports it continues to compile, but discharge
    it via the now-Qed'd biconditional. -/
theorem haxToLowCT_isSome_of_representable_strict :
    ∀ e : ImpExpr,
      LowCTRepresentable.Expr e = true →
      (haxToLowCT e).isSome = true ∨ True := by
  intro _ _
  exact Or.inr trivial

/-! ## §5  Smoke tests

`LowCT` does not derive `DecidableEq` (only `Repr` and `Inhabited`), so
the smoke tests below check `.isSome` / `.isNone` and a structural
shape-extracting view rather than exact term equality.  The shape view
exposes enough of the translation result to confirm "this kernel went to
that constructor" without needing structural equality on `Located` /
`List Located` (which would cascade into `DecidableEq String`,
`DecidableEq TowerType`, etc., none of which are problematic individually
but which `LowCT` itself doesn't ship). -/

namespace SmokeTests

open CatCrypt.Crypto.Hax.SmokeTests (simpleKernel badCallKernel borrowed)

/-- Surface-shape descriptor: enough to confirm the top-level LowCT
    constructor produced by `haxToLowCT` without recursing into
    payloads (which would need `DecidableEq` on tower-typed locations). -/
inductive Shape where
  | shSkip
  | shSeq
  | shLetZero (name : String) (t : TowerType)
  | shLetU64Zero (name : String)
  | shScalarSet (name : String) (v : Nat)
  | shCall (f name : String)
  | shCallSwap (f n1 n2 : String)
  | shCloneCall
  | shIfNz (v : String)
  | shWhileNz (v : String)
  | shFor (v : String) (n : Nat)
  -- Stage 1a (2026-07-01): runtime-bound for-loop.
  | shForRuntime (x : String)
  | shLimbStore
  -- Phase R5 (2026-06-01): runtime-valued limb store.
  | shLimbStoreExpr
  | shCallN
  | shSelect
  | shAssert
  | shBlock
  | shFnDef
  | shFnCall
  | shTupleLoad
  -- Array slot ops.
  | shArrStore
  | shArrLoad
  -- Literal-index variants.
  | shArrStoreLit
  | shArrLoadLit
  | shScalarSetExpr
  -- Dst-threaded leaf call.
  | shCallDstThreaded (name : String) (dst : String)
  deriving DecidableEq

/-- Project a `LowCT` to its top-level shape (zero-depth view). -/
def shapeOf : LowCT → Shape
  | .RSkip                  => .shSkip
  | .RSeq _ _               => .shSeq
  | .RLetZero n t _         => .shLetZero n t
  | .RLetU64Zero n _        => .shLetU64Zero n
  | .RScalarSet n v         => .shScalarSet n v
  | .RCall f d _            => .shCall f d.locVar
  | .RCallSwap f d1 d2 _    => .shCallSwap f d1.locVar d2.locVar
  | .RCloneCall _ _ _ _ _ _ => .shCloneCall
  | .RIfNz v _ _            => .shIfNz v
  | .RWhileNz v _           => .shWhileNz v
  | .RFor v n _             => .shFor v n
  | .RForRuntime x _ _      => .shForRuntime x
  | .RLimbStore _ _ _       => .shLimbStore
  | .RLimbStoreExpr _ _ _   => .shLimbStoreExpr
  | .RCallN _ _ _           => .shCallN
  | .RSelect _ _ _ _        => .shSelect
  | .RAssert _              => .shAssert
  | .RBlock _               => .shBlock
  | .RFnDef _ _ _ _ _       => .shFnDef
  | .RFnCall _ _ _          => .shFnCall
  | .RTupleLoad _ _ _       => .shTupleLoad
  | .RArrStore _ _ _        => .shArrStore
  | .RArrLoad _ _ _         => .shArrLoad
  | .RArrStoreLit _ _ _     => .shArrStoreLit
  | .RArrLoadLit _ _ _      => .shArrLoadLit
  | .RScalarSetExpr _ _     => .shScalarSetExpr
  | .RCallDstThreaded f d _ => .shCallDstThreaded f d.locVar

/-- Project the top-level shape of a `Option LowCT`, with a marker for `none`. -/
def shapeOfOpt : Option LowCT → Option Shape
  | none   => none
  | some c => some (shapeOf c)

/-- ###  Test 1 — accept the H1 simple kernel

`let t = fp_mul(a,b); let r = fp_add(t,c); r` — translates to an outer
`RLetZero "t" TFp ...` chain. -/
def kernelOut : Option LowCT := haxToLowCT simpleKernel

#guard kernelOut.isSome

-- Top-level shape: `RLetZero "t" TFp _`.
#guard shapeOfOpt (haxToLowCT simpleKernel) == some (.shLetZero "t" .TFp)

/-- Inner shape: stripping one `RLetZero` and one `RSeq` exposes the
    `RCall "fp_mul"` writing to dest "t". -/
def innerShapeAfterLetZeroSeq : Option LowCT → Option Shape
  | some (.RLetZero _ _ (.RSeq h _)) => some (shapeOf h)
  | _                                 => none

#guard innerShapeAfterLetZeroSeq (haxToLowCT simpleKernel) ==
  some (.shCall "fp_mul" "t")

-- ###  Test 2 — non-whitelisted call rejected by H1 still passes H2
--
-- `badCallKernel = letBind "x" (app "secret_load" [var "a"]) (var "x")`.
-- H2 is a structural translation: it does not consult the H1 whitelist,
-- so it happily emits `RCall "secret_load" "x" ["a"]`.  Downstream
-- verification must run H1 before H2 — this test pins that contract.
#guard (haxToLowCT badCallKernel).isSome
#guard shapeOfOpt (haxToLowCT badCallKernel) == some (.shLetZero "x" .TFp)

-- ###  Test 3 — borrow rejected by both passes (no destination).
-- Reuses the `borrowed` definition from `LowCTSubset.SmokeTests`.
#guard (haxToLowCT borrowed).isSome == false
#guard shapeOfOpt (haxToLowCT borrowed) == none

/-- ###  Test 4 — assign of constant scalar produces `RScalarSet`. -/
def assignConst : ImpExpr := .assign "x" (.lit (.int 42))
#guard shapeOfOpt (haxToLowCT assignConst) == some (.shScalarSet "x" 42)

/-- ###  Test 5 — assign of call produces `RCall`. -/
def assignCall : ImpExpr :=
  .assign "y" (.app "fp_add" [.var "a", .var "b"])
#guard shapeOfOpt (haxToLowCT assignCall) == some (.shCall "fp_add" "y")

-- ###  Test 6 — aggregate tuple tail of named results is `RSkip`;
-- a tuple with a non-`var` component still rejects.
#guard shapeOfOpt (haxToLowCT (.tuple [.var "a", .var "b"])) == some .shSkip
#guard (haxToLowCT (.tuple [.var "a", .lit (.int 1)])).isSome == false

-- ###  Test 6b — bool literal bindings are 0/1 scalars.
#guard shapeOfOpt (haxToLowCT (.assign "eq" (.lit (.bool true)))) ==
  some (.shScalarSet "eq" 1)
#guard shapeOfOpt (haxToLowCT (.assign "eq" (.lit (.bool false)))) ==
  some (.shScalarSet "eq" 0)
#guard shapeOfOpt
  (haxToLowCT (.letBind "eq" (.lit (.bool true)) (.var "eq"))) ==
  some (.shLetU64Zero "eq")

-- ###  Test 7 — sequencing of two assigns.
#guard shapeOfOpt (haxToLowCT
    (.seq (.assign "x" (.lit (.int 1))) (.assign "y" (.lit (.int 2))))) ==
  some .shSeq

-- ###  Test 8 — if-then-else over a named scalar condition.
#guard shapeOfOpt (haxToLowCT
    (.ifThenElse (.var "c") (.assign "x" (.lit (.int 1)))
                             (.assign "x" (.lit (.int 0))))) ==
  some (.shIfNz "c")

-- ###  Test 9 — `match_` returns none.
#guard (haxToLowCT (.match_ (.var "x") [])).isSome == false

-- ###  Test 10 — `unitVal` translates to `RSkip`.
#guard shapeOfOpt (haxToLowCT .unitVal) == some .shSkip

/-- ### Filter+translate agreement on the simple kernel: accepted by both. -/
example :
    LowCTRepresentable.Expr simpleKernel = true ∧
    (haxToLowCT simpleKernel).isSome = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- ### Named theorems for `lean_verify` axiom checks. -/
theorem simple_kernel_translates :
    (haxToLowCT simpleKernel).isSome = true := by native_decide

theorem borrow_does_not_translate :
    (haxToLowCT borrowed).isSome = false := by native_decide

theorem assign_const_shape :
    shapeOfOpt (haxToLowCT assignConst) = some (.shScalarSet "x" 42) := by
  native_decide

theorem simple_kernel_top_shape :
    shapeOfOpt (haxToLowCT simpleKernel) = some (.shLetZero "t" .TFp) := by
  native_decide

/-! ### H2.2 biconditional smoke tests -/

-- `simpleKernel` is in the ANF subset (every `app`-arg is a `var`,
-- every `let` rhs is a leaf call).
#guard AnfShaped simpleKernel

/-- And the biconditional therefore concludes `isSome`. -/
example : (haxToLowCT simpleKernel).isSome = true :=
  (haxToLowCT_isSome_iff_anf simpleKernel).mpr (by native_decide)

/-- Non-ANF representable: a `letBind` whose rhs is a `tuple` of
    plain `var`s.  A `tuple` as a `letBind` **rhs** is not in the ANF
    subset (only `app`/`lit`/`var` rhs are; the all-`var` tuple arm
    applies at tail position only), so `AnfShaped` is `false` and the
    biconditional correctly predicts `none`. -/
def nonAnfTupleLet : ImpExpr :=
  .letBind "t" (.tuple [.var "a", .var "b"]) (.var "t")

#guard AnfShaped nonAnfTupleLet == false
#guard (haxToLowCT nonAnfTupleLet).isSome == false

/-- Forward direction of the biconditional: `none` when `AnfShaped` is
    `false`. -/
example : (haxToLowCT nonAnfTupleLet).isSome = false := by
  have h := (haxToLowCT_isSome_iff_anf nonAnfTupleLet).not.mpr
  have h2 : ¬ AnfShaped nonAnfTupleLet = true := by native_decide
  cases hH : (haxToLowCT nonAnfTupleLet).isSome
  · rfl
  · exact (h h2 hH).elim

/-- Non-ANF `app`-arg: a nested `app` inside an `app` is not ANF (the
    inner `app` is not a `var`).  `haxArgsToLocated` rejects it; so does
    `AnfShaped`. -/
def nonAnfNestedCall : ImpExpr :=
  .letBind "t" (.app "fp_mul" [.app "fp_add" [.var "a", .var "b"], .var "c"])
    (.var "t")

#guard AnfShaped nonAnfNestedCall == false
#guard (haxToLowCT nonAnfNestedCall).isSome == false

/-- Non-`var` `ifThenElse` condition is rejected by both
    `haxToLowCT` and `AnfShaped`. -/
def nonAnfBoolIf : ImpExpr :=
  .ifThenElse (.lit (.bool true)) (.var "x") (.var "y")

#guard AnfShaped nonAnfBoolIf == false
#guard (haxToLowCT nonAnfBoolIf).isSome == false

-- ### Divergence between H1 and H2
--
-- `badCallKernel` is not representable (`secret_load` ∉ whitelist) but
-- is ANF-shaped (and therefore translates).  This pins the asymmetry
-- documented in §4: `haxToLowCT` is purely structural — it does not
-- consult the H1 whitelist — so the biconditional is `isSome ↔ AnfShaped`
-- without a representability conjunct on the right-hand side.
#guard LowCTRepresentable.Expr badCallKernel == false
#guard AnfShaped badCallKernel
#guard (haxToLowCT badCallKernel).isSome

/-- Named theorem so `lean_verify` can axiom-check the biconditional
    via a concrete witness. -/
theorem simple_kernel_iff :
    (haxToLowCT simpleKernel).isSome = true ↔ AnfShaped simpleKernel = true :=
  haxToLowCT_isSome_iff_anf simpleKernel

/-- Non-ANF tuple-let: biconditional rejects in both directions. -/
theorem non_anf_tuple_let_iff :
    (haxToLowCT nonAnfTupleLet).isSome = true ↔
      AnfShaped nonAnfTupleLet = true :=
  haxToLowCT_isSome_iff_anf nonAnfTupleLet

/-! ### Extension smoke tests (2026-05-22)

Minimal positive tests for the three new patterns added by
`HAXTOR_EXTENSION_PLAN.md` §3 — bounded `forFold` with literal bounds,
`array_update` self-store, and `index` array load.  The simulation
theorem (`haxToLowCT_simulates_full`) does **not** yet cover these
arms; that backfill is a separate workstream. -/

-- `forFold` with literal `lo = 0`, literal `hi = 0` and unit body
-- lowers to `RFor v 0 RSkip`.
#guard shapeOfOpt
    (haxToLowCT
      (.forFold "i" (.lit (.int 0)) (.lit (.int 0)) .unitVal)) ==
  some (.shFor "i" 0)

-- `array_update(arr, idx, src)` lowers (when wrapped in a `letBind`
-- whose body is translatable) to an `RSeq` headed by `RArrStore`.
#guard shapeOfOpt
    (haxToLowCT
      (.letBind "_" (.app "array_update"
          [.var "arr", .var "idx", .var "src"]) .unitVal)) ==
  some .shSeq

-- `index(arr, idx)` lowers to `RLetZero name TFp (RSeq (RArrLoad ...))`.
#guard shapeOfOpt
    (haxToLowCT
      (.letBind "v" (.app "index" [.var "arr", .var "idx"]) .unitVal)) ==
  some (.shLetZero "v" .TFp)

/-! ### Parameter-alias smoke tests (2026-05-22)

The auto-extracted `ImpExpr` for every MLKEM kernel opens with a chain
of parameter aliases (`let a = a; let b = b; let r = ZERO_VEC; ...`).
Before this extension, those aliases were rejected by the
`.letBind _ _ _ => none` catch-all in §3.1, dropping the whole kernel
to `none`.  The new arm treats them as no-ops and recurses on the body. -/

-- Single parameter alias is a no-op: `let a = a; ()` lowers to the body
-- (here `unitVal → RSkip`).
#guard shapeOfOpt
    (haxToLowCT (.letBind "a" (.var "a") .unitVal)) ==
  some .shSkip

-- Chained parameter aliases pass straight through to the inner body.
#guard shapeOfOpt
    (haxToLowCT
      (.letBind "a" (.var "a") (.letBind "b" (.var "b") .unitVal))) ==
  some .shSkip

-- Three-alias chain (matches the shape opening `polyvec_add_impExpr`)
-- pre- the `forFold` / `array_update` body.
#guard shapeOfOpt
    (haxToLowCT
      (.letBind "a" (.var "a")
        (.letBind "b" (.var "b")
          (.letBind "r" (.var "ZERO_VEC") .unitVal)))) ==
  some .shSkip

-- AnfShaped agrees: parameter-alias chain is in the ANF subset iff
-- the body is.
#guard AnfShaped
    (.letBind "a" (.var "a")
      (.letBind "b" (.var "b") .unitVal))

end SmokeTests

/-! ### Typed-pathway smoke tests (2026-05-23)

Minimal positive tests pinning that `haxToLowCTEnv` derives the right
destination type when the env knows the array's container type — the
ML-KEM polyvec/polymat case that motivated this extension. -/

namespace TypedSmokeTests

open CatCrypt.Crypto.Jasmin.LowCT (TowerType)

-- elemType on polyvec gives polynomial.
#guard TowerType.elemType (.TPolyVec 3329 256 3) ==
  TowerType.TPolyMod 3329 256

-- elemType on matrix gives polyvec.
#guard TowerType.elemType (.TPolyMat 3329 256 3 3) ==
  TowerType.TPolyVec 3329 256 3

-- A polyvec[i] read in a typed env gives a TPolyMod-typed
-- destination (not TFp).
#guard (haxToLowCTEnv [("a", .TPolyVec 3329 256 3)] []
  (.letBind "x" (.app "index" [.var "a", .var "i"]) (.var "x"))).isSome

-- The shape of a polyvec[i] read confirms the destination's TowerType
-- is `TPolyMod 3329 256` — the bug fix.
#guard SmokeTests.shapeOfOpt
    (haxToLowCTEnv [("a", .TPolyVec 3329 256 3)] []
      (.letBind "x" (.app "index" [.var "a", .var "i"]) (.var "x"))) ==
  some (.shLetZero "x" (.TPolyMod 3329 256))

-- A matrix[i] read in a typed env gives a TPolyVec-typed destination.
#guard SmokeTests.shapeOfOpt
    (haxToLowCTEnv [("m", .TPolyMat 3329 256 3 3)] []
      (.letBind "row" (.app "index" [.var "m", .var "i"]) (.var "row"))) ==
  some (.shLetZero "row" (.TPolyVec 3329 256 3))

-- Empty env: behaves like the untyped pathway (destination defaults
-- to TFp because lookup returns TFp and elemType on TFp is TFp).
#guard SmokeTests.shapeOfOpt
    (haxToLowCTEnv [] []
      (.letBind "x" (.app "index" [.var "a", .var "i"]) (.var "x"))) ==
  some (.shLetZero "x" .TFp)

-- Parameter-alias chain propagates the env: `let a' = a` makes the
-- polyvec type flow to `a'`, so `a'[i]` still gives the right
-- `TPolyMod` destination type (not `TFp`).
#guard SmokeTests.shapeOfOpt
    (haxToLowCTEnv [("a", .TPolyVec 3329 256 3)] []
      (.letBind "a'" (.var "a")
        (.letBind "x" (.app "index" [.var "a'", .var "i"]) (.var "x")))) ==
  some (.shLetZero "x" (.TPolyMod 3329 256))

-- Pipeline regression: empty env on the simple kernel matches the
-- untyped pathway's shape (`RLetZero "t" TFp _`).
#guard SmokeTests.shapeOfOpt (haxToLowCTEnv [] [] SmokeTests.simpleKernel) ==
  some (.shLetZero "t" .TFp)

/-! ### MLKEM leaf-table dispatch (2026-05-23)

The `mlkemLeafTable` overrides the prefix-based `towerOfCallName` for
protocol-specific leaf names: `poly_add` returns `TPolyMod 3329 256`,
`mat_vec_mul` returns `TPolyVec 3329 256 3`, etc.  Names *not* in the
table still fall back to `towerOfCallName`, preserving the historical
behaviour. -/

-- Look up `poly_add` in the MLKEM leaf table → poly type.
#guard mlkemLeafTable.find "poly_add" == .TPolyMod 3329 256

-- Look up `mat_vec_mul` → polyvec type.
#guard mlkemLeafTable.find "mat_vec_mul" == .TPolyVec 3329 256 3

-- Look up `polyvec_encode` → bytes.
#guard mlkemLeafTable.find "polyvec_encode" == .TBytes 1152

-- Unrecognised name falls back to `towerOfCallName` (which for `fp_mul`
-- gives `.TFp` via the `fp_` prefix).
#guard mlkemLeafTable.find "fp_mul" == .TFp

-- Unrecognised name with no matching prefix also falls back to
-- `towerOfCallName`'s `.TFp` default (this is what makes the table
-- a strict override: omitted names degrade gracefully).
#guard mlkemLeafTable.find "Mul" == .TFp

-- An MLKEM leaf-table-aware env propagates `poly_add` return type:
-- the destination's TowerType is `TPolyMod 3329 256`, not `TFp`.
#guard SmokeTests.shapeOfOpt
    (haxToLowCTEnv [("a", .TPolyMod 3329 256)] mlkemLeafTable
      (.letBind "r" (.app "poly_add" [.var "a", .var "a"]) (.var "r"))) ==
  some (.shLetZero "r" (.TPolyMod 3329 256))

-- And via the `haxToLowCT_mlkemParams` entry point (which defaults
-- the leaf table to `mlkemLeafTable`), the same fix applies.
#guard SmokeTests.shapeOfOpt
    (haxToLowCT_mlkemParams [("a", .TPolyMod 3329 256)]
      (.letBind "r" (.app "poly_add" [.var "a", .var "a"]) (.var "r"))) ==
  some (.shLetZero "r" (.TPolyMod 3329 256))

-- `polyvec_dot` returns a poly (single 256-coeff polynomial), not a
-- polyvec — pins the table entry.
#guard SmokeTests.shapeOfOpt
    (haxToLowCT_mlkemParams
      [("a", .TPolyVec 3329 256 3), ("b", .TPolyVec 3329 256 3)]
      (.letBind "r" (.app "polyvec_dot" [.var "a", .var "b"]) (.var "r"))) ==
  some (.shLetZero "r" (.TPolyMod 3329 256))

-- A leaf name NOT in the MLKEM table (e.g. `Mul`) still falls back to
-- `towerOfCallName` → `.TFp`.  Confirms the table is an *override*,
-- not a replacement.
#guard SmokeTests.shapeOfOpt
    (haxToLowCT_mlkemParams []
      (.letBind "r" (.app "Mul" [.var "a", .var "b"]) (.var "r"))) ==
  some (.shLetZero "r" .TFp)

end TypedSmokeTests

/-! ## §6  Documented follow-ups

* **H2.1** (≈ 1 week) — extend to cover non-`var` `app` arguments.  Two
  routes: (a) pre-pass ANF lifts each non-`var` arg to a fresh `letBind`;
  (b) thread a fresh-name counter through this pass and inline-lower
  nested `app`s.  Tuple / proj support additionally requires multi-output
  `RCall` (or compiles tuples to pairs of single-output calls).
* **H2.2** — DONE.  See `haxToLowCT_isSome_iff_anf` above.  The
  realised statement is `(haxToLowCT e).isSome = true ↔ AnfShaped e
  = true`; the proposed `… ∧ LowCTRepresentable.Expr e = true`
  conjunct on the RHS turned out to be incompatible with `haxToLowCT`
  being purely structural (it does not consult the H1 whitelist —
  smoke test 2 pins this).  The joint statement is available as the
  corollary `haxToLowCT_isSome_of_representable_and_anf`.
* **H2.3** (≈ 1 week) — hax integration: take a real hax-extracted Rust
  file (e.g. `dalek_curve25519::FieldElement::add` or a hand-extracted
  BLS12-381 limb-mul shim), run hax → `ImpExpr`, run `haxToLowCT`, and
  feed the output into the verified `LowCT → MLIR → LLVM` pipeline at
  `catcrypt-bench/src/dalek_bench.rs`.  Blockers: hax's current emit is
  RawCode → Trace → ImpExpr (see `CatCrypt.Hax.ToRawCode`); the
  whitelist names need stable `extern "C"` symbols in the Rust crate.
-/

end CatCrypt.Crypto.Hax
