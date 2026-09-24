/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCT
import all Init.Data.Repr
public import CatCrypt.Crypto.Jasmin.LowCT
public import Lean

/-!
# Reflect Lean value-level programs to `LowCT`

Modeled after `CatCrypt/Deep/Reflect.lean` (SPComp → RawCode). Walks a
Lean value-level expression over opaque `Fp25519` + opaque `fp_*` field
ops and produces an equivalent `LowCT` AST value plus a listing of
function arguments and return name (sufficient to drive the existing
`LowCTToMLIR.emitFunc`).

## User-facing surface

```lean
opaque axiom SomeX25519 : Unit  -- anchor module

-- Users import this file then write natural Lean:
noncomputable def halfstepLean (x2 z2 : Fp25519) : Fp25519 :=
  let A  := fp_add x2 z2
  let B  := fp_sub x2 z2
  let AA := fp_sqr A
  let BB := fp_sqr B
  fp_mul AA BB

-- Reify at elaboration:
def halfstepReified : ReifiedFunc := reifyLowCT% halfstepLean
-- ReifiedFunc bundles (argNames, body : LowCT, retName : String).
```

The reifier understands `let`-bindings (value-level `letE`) and function
parameters (top-level `lambdaE`). It does NOT reify arbitrary Lean —
the input must be a let-chain over known `fp_*` heads ending in either
a `fp_*` call or an already-bound variable.

Unknown heads produce a descriptive elaboration error.
-/

@[expose] public section

namespace CatCrypt.Crypto.Jasmin.LowCT

deriving instance Lean.ToExpr for SecretLevel

meta section

/-- Manual `ToExpr TowerType`. The auto-derived `deriving instance Lean.ToExpr`
    miscompiles this enum: it shifts every nullary constructor by +2 in the def
    order (`TU8 ↦ TFp25519`, `TFp25519 ↦ TFpL25519`, …), so a reified field type
    serialized back to a term came out wrong — making the whole `reifyLowCT%`
    lift emit the wrong field width. This explicit instance round-trips faithfully. -/
def towerTypeToExpr : TowerType → Lean.Expr
  | .TFp            => .const ``TowerType.TFp []
  | .TFp2           => .const ``TowerType.TFp2 []
  | .TFp6           => .const ``TowerType.TFp6 []
  | .TFp12          => .const ``TowerType.TFp12 []
  | .TU64           => .const ``TowerType.TU64 []
  | .TU8            => .const ``TowerType.TU8 []
  | .TU32           => .const ``TowerType.TU32 []
  | .TFp25519       => .const ``TowerType.TFp25519 []
  | .TFp25519_64    => .const ``TowerType.TFp25519_64 []
  | .TFpL25519      => .const ``TowerType.TFpL25519 []
  | .TFpP256        => .const ``TowerType.TFpP256 []
  | .TFp25519_4Bounded b =>
      Lean.mkApp (.const ``TowerType.TFp25519_4Bounded []) (Lean.toExpr b)
  | .TFpGen s n     =>
      Lean.mkApp2 (.const ``TowerType.TFpGen []) (Lean.toExpr s) (Lean.toExpr n)
  | .TFp2Gen s n    =>
      Lean.mkApp2 (.const ``TowerType.TFp2Gen []) (Lean.toExpr s) (Lean.toExpr n)
  | .TTuple a b     =>
      Lean.mkApp2 (.const ``TowerType.TTuple []) (towerTypeToExpr a) (towerTypeToExpr b)
  | .TBytes n       => Lean.mkApp (.const ``TowerType.TBytes []) (Lean.toExpr n)
  | .TArr n t       =>
      Lean.mkApp2 (.const ``TowerType.TArr []) (Lean.toExpr n) (towerTypeToExpr t)
  | .TPolyMod q n   =>
      Lean.mkApp2 (.const ``TowerType.TPolyMod []) (Lean.toExpr q) (Lean.toExpr n)
  | .TPolyVec q n k =>
      Lean.mkApp3 (.const ``TowerType.TPolyVec [])
        (Lean.toExpr q) (Lean.toExpr n) (Lean.toExpr k)
  | .TPolyMat q n k m =>
      Lean.mkApp4 (.const ``TowerType.TPolyMat [])
        (Lean.toExpr q) (Lean.toExpr n) (Lean.toExpr k) (Lean.toExpr m)


instance : Lean.ToExpr TowerType where
  toExpr := towerTypeToExpr
  toTypeExpr := .const ``TowerType []


deriving instance Lean.ToExpr for Located
deriving instance Lean.ToExpr for SExpr
-- Derive on the canonical inductive `LowCT`.
deriving instance Lean.ToExpr for LowCT

end            -- meta section

end CatCrypt.Crypto.Jasmin.LowCT

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT
open Lean Meta Elab

/-! ## 1. Opaque surface types + field-op symbols

Opaque constants and axioms, so the reifier can intercept calls before Lean
unfolds them. -/

opaque Fp25519.Impl : NonemptyType.{0}
/-- Opaque `Fp25519` element. Users write Lean source against this type;
    the reifier produces `LowCT`. Programs over this type are never
    evaluated — they're extracted to MLIR. -/
def Fp25519 : Type := Fp25519.Impl.type
instance : Nonempty Fp25519 := Fp25519.Impl.property

/-- An inhabitant so Lean can typecheck programs over `Fp25519`. -/
noncomputable opaque Fp25519.default : Fp25519

noncomputable instance : Inhabited Fp25519 := ⟨Fp25519.default⟩

/-- Field add. -/ axiom fp_add     : Fp25519 → Fp25519 → Fp25519
/-- Field sub. -/ axiom fp_sub     : Fp25519 → Fp25519 → Fp25519
/-- Field mul. -/ axiom fp_mul     : Fp25519 → Fp25519 → Fp25519
/-- Field sqr. -/ axiom fp_sqr     : Fp25519 → Fp25519
/-- `*121666`. -/ axiom fp_mul_a24 : Fp25519 → Fp25519
/-- Unary negation (opp). -/ axiom fp_opp : Fp25519 → Fp25519

/-! ### Extended Fp25519 ops (needed for Ed25519 / Ristretto255)

These close the gap between X25519's minimal surface and the Edwards
layer. Every op stays homogeneous in `Fp25519` so the reifier's
let-chain walker sees each one as a regular `fp_*` leaf.

- `fp_cmov a b sel` returns `a` if `sel` encodes 0, else `b`. The C
  backend implements this as a mask-and-merge using the low limb of
  `sel` (bits 63..1 ignored) — constant-time.
- `fp_is_neg x` returns a 5-limb Fp value whose low limb carries the
  sign bit of `x` (LSB of the canonical byte encoding). Callers that
  need a proper bit-typed value mask with `fp_cmov` first.
- `fp_sqrt_ratio_i u v` computes a canonical square root of `u/v`
  (Ed25519 decompression / Ristretto-style). Signals "no root" by
  the canonical encoding; callers in CT contexts branch via cmov. -/
/-- Repeated squaring `x^(2^n)` — fixed chain length baked into the leaf. -/
noncomputable opaque fp_sq2   : Fp25519 → Fp25519
noncomputable opaque fp_sq4   : Fp25519 → Fp25519
noncomputable opaque fp_sq8   : Fp25519 → Fp25519

/-- Inverse square root: `out = 1/sqrt(v)` via `pow_p58 · glue` addition
    chain, mirroring `curve25519-dalek/src/backend/serial/u64/field.rs`. -/
noncomputable opaque fp_invsqrt : Fp25519 → Fp25519

/-- Square root mod p via `sqrt(u/v) = u · v^((p-5)/8)` trick. -/
noncomputable opaque fp_sqrt_ratio_i : Fp25519 → Fp25519 → Fp25519

/-- Multiplicative inverse (Fermat's little theorem; ~265 fp_sqr + ~11 fp_mul). -/
noncomputable opaque fp_inv : Fp25519 → Fp25519

/-- CT conditional move: `sel` is a byte mask encoded into low limb of Fp25519. -/
noncomputable opaque fp_cmov : Fp25519 → Fp25519 → Fp25519 → Fp25519

/-- Extract sign bit of canonical encoding of `x`, returned in low limb. -/
noncomputable opaque fp_is_neg  : Fp25519 → Fp25519
/-- Test whether `x` is zero, low limb holds 1 / 0. -/
noncomputable opaque fp_is_zero : Fp25519 → Fp25519

/-! ### Scalar field (Curve25519 order `L`) ops

`FpL25519` is the Ed25519 scalar group, order
`L = 2^252 + 27742317777372353535851937790883648493`. Backed by
fiat-crypto's 4-limb Montgomery representation (`curve25519_scalar_64.c`).
The reifier sees `FpL25519` values as having TowerType `.TFpL25519`. -/

opaque FpL25519.Impl : NonemptyType.{0}
def FpL25519 : Type := FpL25519.Impl.type
instance : Nonempty FpL25519 := FpL25519.Impl.property
noncomputable opaque FpL25519.default : FpL25519
noncomputable instance : Inhabited FpL25519 := ⟨FpL25519.default⟩

/-- Scalar addition mod L. -/ axiom scalar_add : FpL25519 → FpL25519 → FpL25519
/-- Scalar subtraction mod L. -/ axiom scalar_sub : FpL25519 → FpL25519 → FpL25519
/-- Scalar multiplication mod L. -/ axiom scalar_mul : FpL25519 → FpL25519 → FpL25519
/-- Scalar negation. -/ axiom scalar_neg : FpL25519 → FpL25519
/-- Multiplicative inverse mod L (uses Bernstein's addition chain). -/
noncomputable opaque scalar_inv : FpL25519 → FpL25519

/-! ### NIST P-256 base field

`FpP256` is the NIST P-256 base field, order `p = 2²⁵⁶ - 2²²⁴ + 2¹⁹² + 2⁹⁶ - 1`.
Backed by fiat-crypto's 4-limb saturated-Montgomery representation
(`p256_64.c`). Reifier maps `FpP256` to `TowerType.TFpP256` →
`memref<4xi64>`. Demonstrates the pipeline's curve-agnosticism: same
authoring shape, different curve, different shim. -/

opaque FpP256.Impl : NonemptyType.{0}
def FpP256 : Type := FpP256.Impl.type
instance : Nonempty FpP256 := FpP256.Impl.property
noncomputable opaque FpP256.default : FpP256
noncomputable instance : Inhabited FpP256 := ⟨FpP256.default⟩

/-- P-256 field add (Montgomery domain). -/
noncomputable opaque fp256_add : FpP256 → FpP256 → FpP256
/-- P-256 field sub. -/
noncomputable opaque fp256_sub : FpP256 → FpP256 → FpP256
/-- P-256 field mul (Montgomery, saturated). -/
noncomputable opaque fp256_mul : FpP256 → FpP256 → FpP256
/-- P-256 field square. -/
noncomputable opaque fp256_sqr : FpP256 → FpP256
/-- P-256 field opp (negation). -/
noncomputable opaque fp256_opp : FpP256 → FpP256

/-! ### BLS-style base field `Fp` and quadratic extension `Fp2`

The straight-line curve programs in `LowCTToJasmin.lean §5`
(`g1Add` / `g1Dbl` / `g2Add`, Renes et al. projective/affine formulas)
are authored over a generic prime field `Fp` and its degree-2 extension
`Fp2`.  These map to the `TFp` / `TFp2` tower types (the BLS / pairing
surface), distinct from the curve25519 `Fp25519` surface.  The leaf
names match the `g1*`/`g2*` `RCall`s (`fp_mul`, `fp_add`, `fp_sub`,
`fp_sqr`, `fp2_mul`, `fp2_add`, `fp2_sub`). -/
opaque Fp.Impl : NonemptyType.{0}
def Fp : Type := Fp.Impl.type
instance : Nonempty Fp := Fp.Impl.property
noncomputable opaque Fp.default : Fp
noncomputable instance : Inhabited Fp := ⟨Fp.default⟩

/-- `Fp` mul. -/ axiom bls_fp_mul : Fp → Fp → Fp
/-- `Fp` add. -/ axiom bls_fp_add : Fp → Fp → Fp
/-- `Fp` sub. -/ axiom bls_fp_sub : Fp → Fp → Fp
opaque Fp2.Impl : NonemptyType.{0}
/-- `Fp` sqr. -/ axiom bls_fp_sqr : Fp → Fp

def Fp2 : Type := Fp2.Impl.type
instance : Nonempty Fp2 := Fp2.Impl.property
noncomputable opaque Fp2.default : Fp2
noncomputable instance : Inhabited Fp2 := ⟨Fp2.default⟩

/-- `Fp2` mul. -/ axiom bls_fp2_mul : Fp2 → Fp2 → Fp2
/-- `Fp2` add. -/ axiom bls_fp2_add : Fp2 → Fp2 → Fp2
/-- `Fp2` sub. -/ axiom bls_fp2_sub : Fp2 → Fp2 → Fp2

/-! ## 2.0  Extensible pattern registry

The `knownOps : List (Name × String × Nat × TowerType)` table
below is monolithic: every new field-op head requires an edit here.
The attribute-based registry lets external modules contribute patterns
without touching this file.

Workflow for a downstream user:

```lean
@[rust_cmd_pattern]
def myCustomOpPattern : LowCTPattern where
  name      := "my_custom_op"
  fnHead    := ``MyModule.my_custom_op
  arity     := 2
  towerType := .TFp25519
```

The reifier consults the registry **after** `knownOps` (so explicit
in-file entries take precedence).  Downstream modules register
patterns through this API without editing `knownOps`. -/

/-- A single pattern recogniser.  Maps a Lean constant
    name (the function head) to its LowCT leaf-call lowering.

    Multi-arg variants (e.g. tower-type families) can be registered as
    multiple `LowCTPattern` instances, one per arity / tower type. -/
structure LowCTPattern where
  /-- Display name; appears in the emitted `RCall`'s leaf name. -/
  name      : String
  /-- The Lean constant name to match (e.g. `` ``MyModule.foo``). -/
  fnHead    : Name
  /-- Expected number of fully-applied arguments. -/
  arity     : Nat
  /-- TowerType of the destination, and of every argument when `argTypes`
      is `none`. -/
  towerType : TowerType
  /-- Per-argument tower types of a heterogeneous leaf, in argument order.

      `none` is the homogeneous reading: the destination and every argument
      take `towerType`. `some ts` requires `ts.length = arity` and gives
      argument `i` the type `ts[i]`, leaving the destination at `towerType`;
      a scalar-times-point leaf is then `arity := 2`,
      `towerType := .TBytes 144`, `argTypes := some [.TBytes 48, .TBytes 144]`.

      A pattern carrying `argTypes` is matched against them by
      `patternArgMismatch?`. -/
  argTypes  : Option (List TowerType) := none
  deriving Inhabited


/-! ## 3. Reified output

`ReifiedFunc` bundles what `LowCTToMLIR.emitFunc` needs: ordered arg
list with types, return variable name, and the body `LowCT`. -/

structure ReifiedFunc where
  args    : List (String × TowerType)
  body    : LowCT
  retName : String
  /-- Ordered list of output slot names for a **multi-result** kernel,
      i.e. one whose pure-Lean reference returns a tuple `(o₀, o₁, …)`.
      Each entry is the in-scope variable the body writes its output to,
      matching the `&mut` slot ABI the emit consumers (`ppRustFunction`,
      `emitFunc`) expect.  For a single-output kernel this is `[retName]`;
      defaulted to `[]` so the existing hand-built `{ args, body, retName }`
      `ReifiedFunc` literals (the Vale leaves) keep elaborating unchanged. -/
  outNames : List String := []
  deriving Inhabited

meta section


/-- The registry is an `IO.Ref` to a list, populated at attribute-init
    time.  `MetaM` consults it via `LowCTPatternRegistry.lookup`. -/
initialize rustCmdPatternRegistry : IO.Ref (List LowCTPattern) ←
  IO.mkRef []

/-- Register a `LowCTPattern` value in the global registry.
    Called by the `@[rust_cmd_pattern]` attribute handler. -/
def LowCTPattern.register (p : LowCTPattern) : IO Unit :=
  rustCmdPatternRegistry.modify (p :: ·)

/-- Look up a pattern by Lean constant name.  Returns the first
    registered pattern whose `fnHead` matches.  Used by the reifier
    after `knownOps` lookup fails. -/
def LowCTPattern.lookup? (cn : Name) : IO (Option LowCTPattern) := do
  let table ← rustCmdPatternRegistry.get
  pure (table.find? (·.fnHead == cn))

/-- Snapshot the current registry contents (debug / audit helper). -/
def LowCTPattern.snapshot : IO (List LowCTPattern) :=
  rustCmdPatternRegistry.get

/-! ### `@[rust_cmd_pattern]` attribute

The attribute reads the marked `def`'s value (must reduce to a
`LowCTPattern`), evaluates it, and calls
`LowCTPattern.register`.

Usage:

```lean
@[rust_cmd_pattern]
def myCustomOpPattern : LowCTPattern where
  name      := "my_custom_op"
  fnHead    := ``MyModule.my_custom_op
  arity     := 2
  towerType := .TFp25519
```

The handler runs at attribute-application time, evaluates the
referenced declaration to a `LowCTPattern`, and inserts it into
the global registry.  The reifier consults the registry as a
fallback after the in-file `knownOps` table — so in-file entries
take precedence over registered instances. -/

/-- Persistent declaration extension storing the names of all
    `@[rust_cmd_pattern]`-tagged declarations.  We store *names*, not
    pre-evaluated values, because evaluating arbitrary user
    declarations at attribute-application time would require
    `unsafe` (`Lean.Meta.evalExpr` is `unsafe`).  The reifier looks up
    the actual `LowCTPattern` value at reify-time via
    `Lean.evalConst`, which is safe in the elaboration monad. -/
initialize rustCmdPatternExt :
    Lean.SimplePersistentEnvExtension Lean.Name (Array Lean.Name) ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn    := fun arr n => arr.push n
    addImportedFn := fun arrs => arrs.foldl (fun acc a => acc ++ a) #[]
  }


initialize Lean.registerBuiltinAttribute {
  name  := `rust_cmd_pattern
  descr := "Register a LowCTPattern in the dynamic reifier registry"
  add   := fun declName _stx _kind => do
    let env ← Lean.getEnv
    -- Sanity-check the declaration's type is LowCTPattern.
    let info ← match env.find? declName with
      | some i => pure i
      | none =>
          throwError "@[rust_cmd_pattern]: declaration not found: {declName}"
    let typeFn := info.type.getAppFn
    if !(typeFn.isConstOf ``LowCTPattern) then
      throwError
        "@[rust_cmd_pattern]: declaration {declName} has type {info.type}, expected LowCTPattern"
    -- Record the name in the persistent extension; the reifier will
    -- resolve it to a concrete LowCTPattern at reify time.
    Lean.modifyEnv fun env => rustCmdPatternExt.addEntry env declName
}

/-- All declarations currently tagged `@[rust_cmd_pattern]`.  Looked up
    by the reifier in `MetaM` via `Lean.Meta.evalExpr` (which is safe
    inside the elaboration monad). -/
def LowCTPattern.taggedDecls : Lean.MetaM (Array Lean.Name) := do
  let env ← Lean.getEnv
  pure (rustCmdPatternExt.getState env)

/-! ### Computable-body leaves: the `@[rust_cmd_pattern_computable]` sibling
    attribute

#### Problem

The default `@[rust_cmd_pattern]` workflow associates the Lean name `fnHead`
with the emitted LowCT leaf-name string. The associated Lean decl is almost
always an `axiom` or an `opaque` constant — uninterpreted on the Lean side, with
semantics supplied externally
(by the jasmin shim that implements the leaf), as in the rustcmd-emit
consumers MAYO, UOV, SNOVA, MQOM, Plonky3, ….

The bridge-side cost: the L3 correctness identity between the rustcmd leaf
and the Lean-level verified spec is a *cross-side axiom* (e.g.
`mayo_quadform_n8_eq_mqEvalN8` in `MAYO/MayoHaxLowCTBridge.lean`) — there
is no shared Lean body that both sides reduce to, so the bridge cannot be
closed by `rfl`.

Defining the leaf as a Lean `def` whose body IS the verified expression
would make the bridge identity `rfl`, but the plain reifier defeats it:

> When `reifyLowCT%` walks a let-chain, every let-value is normalised
> by `Lean.Meta.whnf` *before* the pattern table is consulted (see
> `reifyChain`, line 779). `whnf` runs at *default* transparency, which
> **unfolds regular `def`s**. So a let-bound `mayo_quadform_n8 s mat`,
> when the head is a `def`, gets reduced to the body's
> `mayoScalarOfGf16 (MqEvalVerified.mqEvalN8 …)` — the head is not
> the registered name, so the pattern match fails.

The obstruction is transparency, not arity: `LowCTPattern` is not a
typeclass, and its explicit `arity` field is unaffected by `def` vs `axiom`.

#### Solution (this section)

Two co-operating changes:

1. **The attribute `@[rust_cmd_pattern_computable]`** records the *same*
   `LowCTPattern` shape as `@[rust_cmd_pattern]` but *additionally* marks
   the head name as "match-before-whnf". The persistent extension storing
   tagged decls is shared with the regular `@[rust_cmd_pattern]` (so all
   existing consumers continue to work), and a parallel persistent
   extension `rustCmdPatternComputableExt` stores just the `fnHead`
   names that are computable defs.

2. **The reifier consults the computable-head set BEFORE running `whnf`.**
   If the un-whnf'd head of the let-value is a computable-head name, the
   match emits the leaf directly; otherwise the existing `whnf`-then-match
   path runs.

The downstream effect: a consumer can write

```
def mayo_quadform_n8 (s : MayoVecN8) (mat : MayoMat8x8) : MayoScalar :=
  mayoScalarOfGf16 (MqEvalVerified.mqEvalN8 (mayoVecN8ToVec s) (mayoMat8x8ToVec mat))

@[rust_cmd_pattern_computable]
def mayoQuadFormN8Pattern : LowCTPattern where
  name      := "mayo_quadform_n8"
  fnHead    := ``mayo_quadform_n8
  arity     := 2
  towerType := .TBytes 1
```

and prove the bridge identity by `rfl`. The hand-built
`LowCT` consumers (which name the leaf as a string) and the verified front
see the same `extCall "mayo_quadform_n8"` in both cases. The
difference is at the Lean equational layer: the def's body is visible
to `rfl`-based proofs in any module that imports the `def`.

#### Invariants

- `@[rust_cmd_pattern]` consumers continue to work bit-identically (we add
  to the registry, never remove or rename existing entries).
- The reifier's `whnf`-then-match path is unchanged for any name NOT in
  the computable set; only the small set of `@[rust_cmd_pattern_computable]`
  heads gets the "match-before-whnf" treatment.
- The downstream chain (`translate → cryptoDialectToJasminCom → emitAbiOrch…`) sees
  the same `RCall` shape regardless of whether the leaf is a `def`, an
  `opaque` constant or an `axiom` — the leaf name is just a string at that layer.

#### Bridge consequence (the headline win)

When the leaf is a computable `def`, the cross-side axiom in
`MayoHaxLowCTBridge.lean` / `UovHaxLowCTBridge.lean`
(`mayo_quadform_n8_eq_mqEvalN8`, `gf256_dot_l8_eq_evalMqL8`) becomes a
`rfl`-provable theorem — the bridge has *zero* cross-side axioms for the
leaf-to-spec correspondence. The structural bijection axioms remain (they
are one-sided byte-ABI claims, not leaf semantics). -/


/-- Persistent extension recording computable-bodied pattern decls.
    Stored as a list of names like `rustCmdPatternExt` but used for the
    "bypass `whnf`" check.  Decoupled so we can extend later without
    touching the regular pattern flow.

    Defined BEFORE the attribute below (forward references would fail).
    Uses the same `SimplePersistentEnvExtension` mechanism the regular
    `rustCmdPatternExt` uses — no second `IO.Ref` `initialize` block
    (Lean rejects multi-`IO.Ref`-init blocks in the same module with
    `cannot evaluate [init] declaration ... in the same module`). -/

initialize rustCmdPatternComputableExt :
    Lean.SimplePersistentEnvExtension Lean.Name (Array Lean.Name) ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn    := fun arr n => arr.push n
    addImportedFn := fun arrs => arrs.foldl (fun acc a => acc ++ a) #[]
  }

initialize Lean.registerBuiltinAttribute {
  name  := `rust_cmd_pattern_computable
  descr := "Register a LowCTPattern whose fnHead is a computable def \
            (matched before whnf-normalisation in the reifier)."
  add   := fun declName _stx _kind => do
    let env ← Lean.getEnv
    let info ← match env.find? declName with
      | some i => pure i
      | none =>
          throwError "@[rust_cmd_pattern_computable]: declaration not found: {declName}"
    let typeFn := info.type.getAppFn
    if !(typeFn.isConstOf ``LowCTPattern) then
      throwError
        "@[rust_cmd_pattern_computable]: declaration {declName} has type {info.type}, expected LowCTPattern"
    -- Record the name in the regular `rustCmdPatternExt` persistent
    -- extension — so `matchPattern?`'s normal consultation path finds
    -- the leaf (downstream modules see the registration post-import).
    -- We ALSO push to the computable side table so the reifier knows
    -- to bypass `whnf` on this head.
    Lean.modifyEnv fun env => rustCmdPatternExt.addEntry env declName
    Lean.modifyEnv fun env => rustCmdPatternComputableExt.addEntry env declName
}

/-- All declarations currently tagged `@[rust_cmd_pattern_computable]`.
    Consulted by the reifier *before* `whnf`-normalising a let-value, so
    that a `def`-bodied leaf whose body would otherwise be unfolded by
    `whnf` is still recognised as a leaf head.

    Backed by a `SimplePersistentEnvExtension` (same mechanism as the
    regular `rustCmdPatternExt`) — no `IO.Ref` for this registry.

    Wrapped via `unsafe` + `@[implemented_by]` opaque so consumers in
    the *same* module (e.g. the `#eval halfstepReified` smoke tests
    below) don't force same-module `[init]` evaluation of the
    underlying `SimplePersistentEnvExtension`.  This mirrors the
    `matchPattern? / matchPatternUnsafe` pattern just below. -/
unsafe def computableDeclsUnsafe : Lean.MetaM (Array Lean.Name) := do
  let env ← Lean.getEnv
  pure (rustCmdPatternComputableExt.getState env)

@[implemented_by computableDeclsUnsafe]
opaque LowCTPattern.computableDecls : Lean.MetaM (Array Lean.Name)

/-- Is the head of `e` registered as a `@[rust_cmd_pattern_computable]`
    leaf?  Used by the reifier to decide whether to bypass `whnf` (so
    that the head — a `def` rather than an `axiom` — is not unfolded
    before pattern matching).

    Wrapped as `unsafe` + `@[implemented_by]` opaque (same trick as
    `matchPattern?`) to avoid forcing same-module `[init]` evaluation of
    `rustCmdPatternComputableExt` when reachable from the file's own
    `#eval` smoke tests. -/
unsafe def isComputablePatternHeadUnsafe (e : Expr) : MetaM Bool := do
  let (cn, _) := e.getAppFnArgs
  let env ← Lean.getEnv
  let names := rustCmdPatternComputableExt.getState env
  pure (names.any (· == cn))

@[implemented_by isComputablePatternHeadUnsafe]
opaque isComputablePatternHead? (e : Expr) : MetaM Bool


/-! ## 2. Registry of known field-op heads

Each entry maps a Lean constant name to its LowCT leaf-call name,
arity, and tower type. The reifier uses the tower type to mark
argument/dest `Located`s correctly. -/

/-! ### ML-KEM polynomial surface (Z_3329[X]/(X^256+1))

Opaque `MlPoly` + the NTT-layer ops, exactly mirroring the `Fp25519`/`fp_*`
curve surface: a user writes natural Lean over these and the reifier produces a
`LowCT` whose leaves are the lattice NTT primitives. Homogeneous in `MlPoly`,
so the reifier's let-chain walker handles them like the `fp_*` leaves. This is
the ML-KEM analogue of the X25519 field surface — the verified Lean→LowCT lift
for the lattice layer. -/

opaque MlPoly.Impl : NonemptyType.{0}
/-- Opaque ML-KEM polynomial (NTT-or-coefficient form, `Z_3329[X]/(X^256+1)`). -/
def MlPoly : Type := MlPoly.Impl.type
instance : Nonempty MlPoly := MlPoly.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlPoly.default : MlPoly
noncomputable instance : Inhabited MlPoly := ⟨MlPoly.default⟩
/-- Forward NTT. -/      axiom mlk_ntt     : MlPoly → MlPoly
/-- Inverse NTT. -/      axiom mlk_invntt  : MlPoly → MlPoly
/-- NTT-domain basemul.-/axiom mlk_basemul : MlPoly → MlPoly → MlPoly
/-- Pointwise add. -/    axiom mlk_poly_add : MlPoly → MlPoly → MlPoly

opaque MlVec.Impl : NonemptyType.{0}
/-- ML-KEM-768 polynomial vector `(MlPoly)^3` (`TPolyVec 3329 256 3`). -/
def MlVec : Type := MlVec.Impl.type
instance : Nonempty MlVec := MlVec.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlVec.default : MlVec
noncomputable instance : Inhabited MlVec := ⟨MlVec.default⟩
opaque MlMat.Impl : NonemptyType.{0}
/-- ML-KEM-768 polynomial matrix `(MlPoly)^{3×3}` (`TPolyMat 3329 256 3 3`). -/
def MlMat : Type := MlMat.Impl.type
instance : Nonempty MlMat := MlMat.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlMat.default : MlMat
noncomputable instance : Inhabited MlMat := ⟨MlMat.default⟩
/-- Vector forward NTT (apply NTT to each of the 3 polynomials). -/
noncomputable opaque pv_ntt    : MlVec → MlVec
/-- Vector inverse NTT. -/
noncomputable opaque pv_invntt : MlVec → MlVec
/-- NTT-domain matrix-vector product `t̂ = Â ∘ ŝ` (per row: 3 basemuls accumulated),
    the core of ML-KEM keygen/encaps. -/
noncomputable opaque mlk_matvec : MlMat → MlVec → MlVec
/-- Pointwise polyvec addition. -/
noncomputable opaque pv_add : MlVec → MlVec → MlVec

/-! #### Coefficient-form ML-KEM arithmetic surface (Stage-L kernels).

These are the *coefficient-form* leaves used by the hand-authored
`MlkemLowCT.lean` kernels (`poly_madd_kernel`, `kpke_*`), distinct from
the NTT-form `mlk_basemul` / `mlk_matvec` leaves above.  The leaf
strings are the bare `poly_*` / `polyvec_*` / `mat_vec_mul` names that
the bridge / lowering passes bind.  Heterogeneous argument types
(`mat_vec_mul : MlMat → MlVec → MlVec`, `polyvec_dot : MlVec → MlVec →
MlPoly`) are threaded per-argument by the reifier. -/
/-- Coeff-form poly multiply (schoolbook / Karatsuba, leaf `poly_mul`). -/
noncomputable opaque mlk_poly_mul_c : MlPoly → MlPoly → MlPoly
/-- Coeff-form poly subtract (leaf `poly_sub`). -/
noncomputable opaque mlk_poly_sub_c : MlPoly → MlPoly → MlPoly
/-- Coeff-form polyvec add (leaf `polyvec_add`). -/
noncomputable opaque mlk_polyvec_add_c : MlVec → MlVec → MlVec
/-- Coeff-form polyvec dot product `⟨a, b⟩` → poly (leaf `polyvec_dot`). -/
noncomputable opaque mlk_polyvec_dot_c : MlVec → MlVec → MlPoly
/-- Coeff-form matrix·vector product (leaf `mat_vec_mul`). -/
noncomputable opaque mlk_mat_vec_mul_c : MlMat → MlVec → MlVec

opaque MlSeed.Impl : NonemptyType.{0}
/-- 32-byte ML-KEM keygen randomness `d` (`TBytes 32`). -/
def MlSeed : Type := MlSeed.Impl.type
instance : Nonempty MlSeed := MlSeed.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlSeed.default : MlSeed
noncomputable instance : Inhabited MlSeed := ⟨MlSeed.default⟩
opaque MlRhoSigma.Impl : NonemptyType.{0}
/-- `G(d) = ρ‖σ` (`TBytes 64`, SHA3-512 output: public seed ‖ noise seed). -/
def MlRhoSigma : Type := MlRhoSigma.Impl.type
instance : Nonempty MlRhoSigma := MlRhoSigma.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlRhoSigma.default : MlRhoSigma
noncomputable instance : Inhabited MlRhoSigma := ⟨MlRhoSigma.default⟩
opaque MlEncVec.Impl : NonemptyType.{0}
/-- ByteEncode'd polyvec (`TBytes 1152` = k·384, the public-key body). -/
def MlEncVec : Type := MlEncVec.Impl.type
instance : Nonempty MlEncVec := MlEncVec.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlEncVec.default : MlEncVec
noncomputable instance : Inhabited MlEncVec := ⟨MlEncVec.default⟩
/-- Seed expansion `ρ‖σ = G(d)` (SHA3-512 of the 32-byte randomness). -/
noncomputable opaque mlk_hash_g : MlSeed → MlRhoSigma
/-- Matrix expansion `Â = gen_matrix(ρ)` (SHAKE128 rejection sampling; reads `ρ`
    = first 32 bytes of `ρ‖σ`). -/
noncomputable opaque mlk_gen_matrix : MlRhoSigma → MlMat
/-- Secret vector `s = CBD_η(PRF(σ, nonces 0..2))` (reads `σ` = bytes 32..64). -/
noncomputable opaque mlk_cbd_s : MlRhoSigma → MlVec
/-- Error vector `e = CBD_η(PRF(σ, nonces 3..5))`. -/
noncomputable opaque mlk_cbd_e : MlRhoSigma → MlVec
/-- NTT-domain matrix-vector product with Montgomery normalization `frommont`
    (per row: `pointwise_acc` then `_poly_frommont`), as in formosa keypair —
    the result stays in the NTT domain (t̂ is stored NTT-domain, no invntt). -/
noncomputable opaque mlk_matvec_mont : MlMat → MlVec → MlVec
/-- Barrett reduce each coefficient to `[0, q)`. -/
noncomputable opaque mlk_pv_reduce : MlVec → MlVec
/-- ByteEncode a polyvec to its serialized form (`__polyvec_tobytes`). -/
noncomputable opaque mlk_encode_vec : MlVec → MlEncVec

/-! #### ML-KEM-768 encaps / decaps (K-PKE Encrypt / Decrypt cores).
Modelled on formosa `__indcpa_enc` / `__indcpa_dec`. The byte-serialization
leaves (decode/compress/decompress) are opaque here; for the KAT they need
stack-array reimplementations (formosa's are raw-memory-pointer ABIs). -/
opaque MlPubKey.Impl : NonemptyType.{0}
/-- ML-KEM-768 public key `ek = ByteEncode(t̂)‖ρ` (`TBytes 1184`). -/
def MlPubKey : Type := MlPubKey.Impl.type
instance : Nonempty MlPubKey := MlPubKey.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlPubKey.default : MlPubKey
noncomputable instance : Inhabited MlPubKey := ⟨MlPubKey.default⟩
opaque MlMsg.Impl : NonemptyType.{0}
/-- 32-byte message (`TBytes 32`). -/
def MlMsg : Type := MlMsg.Impl.type
instance : Nonempty MlMsg := MlMsg.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlMsg.default : MlMsg
noncomputable instance : Inhabited MlMsg := ⟨MlMsg.default⟩
opaque MlCipher.Impl : NonemptyType.{0}
/-- ML-KEM-768 ciphertext `c = Compress_du(u)‖Compress_dv(v)` (`TBytes 1088`). -/
def MlCipher : Type := MlCipher.Impl.type
instance : Nonempty MlCipher := MlCipher.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlCipher.default : MlCipher
noncomputable instance : Inhabited MlCipher := ⟨MlCipher.default⟩

-- Encaps (K-PKE.Encrypt) leaves:
/-- Decode `t̂` from the public key (`__polyvec_frombytes` of `ek[0:1152]`). -/
noncomputable opaque mlk_pk_decode : MlPubKey → MlVec
/-- Transposed matrix `Âᵀ = gen_matrix(ρ, transposed=1)` (ρ = `ek[1152:1184]`). -/
noncomputable opaque mlk_gen_matrix_T : MlPubKey → MlMat
/-- Message to poly `k = Decompress_1(m)` (`_i_poly_frommsg`). -/
noncomputable opaque mlk_frommsg : MlMsg → MlPoly
/-- Encaps noise `r = CBD(coins, nonces 0..2)`. -/
noncomputable opaque mlk_cbd_enc_r : MlSeed → MlVec
/-- Encaps error `e1 = CBD(coins, nonces 3..5)`. -/
noncomputable opaque mlk_cbd_enc_e1 : MlSeed → MlVec
/-- Encaps error `e2 = CBD(coins, nonce 6)` (single poly). -/
noncomputable opaque mlk_cbd_enc_e2 : MlSeed → MlPoly
opaque MlNoiseEnc.Impl : NonemptyType.{0}
/-- Bundle of all encaps CBD noise `(r‖e1‖e2)` = 7 polys (`TPolyVec 3329 256 7`).
    `mlk_cbd_enc_all coins` samples nonces 0..6 in a SINGLE leaf. On the AVX2
    backend this is **two** 4-way SHAKE256 permutations (nonces {0,1,2,3} and
    {4,5,6,7}, lane 7 discarded) instead of the three separate
    `_poly_getnoise_eta1_4x` calls (nonces {0..3},{3..6},{6..9}) the unfused
    `cbd_enc_{r,e1,e2}` triple emits — the same 2-call batching formosa's own
    avx2 `__indcpa_enc` uses. -/
def MlNoiseEnc : Type := MlNoiseEnc.Impl.type
instance : Nonempty MlNoiseEnc := MlNoiseEnc.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlNoiseEnc.default : MlNoiseEnc
noncomputable instance : Inhabited MlNoiseEnc := ⟨MlNoiseEnc.default⟩
/-- Sample all encaps noise (r,e1,e2) in one batched leaf. -/
noncomputable opaque mlk_cbd_enc_all : MlSeed → MlNoiseEnc
/-- Split `r` (polyvec, nonces 0..2) out of the noise bundle. -/
noncomputable opaque mlk_noise_r : MlNoiseEnc → MlVec
/-- Split `e1` (polyvec, nonces 3..5) out of the noise bundle. -/
noncomputable opaque mlk_noise_e1 : MlNoiseEnc → MlVec
/-- Split `e2` (single poly, nonce 6) out of the noise bundle. -/
noncomputable opaque mlk_noise_e2 : MlNoiseEnc → MlPoly
/-- `u = invntt(Âᵀ ∘ r̂)` (pointwise_acc + invntt per row, coefficient domain). -/
noncomputable opaque mlk_matvec_invntt : MlMat → MlVec → MlVec
/-- **Fused** `gen_matrix(ρ,1)` then `invntt(Âᵀ ∘ r̂)`: samples the transposed matrix
    `Â` into a leaf-local buffer and consumes it directly in the pointwise product, so
    the 2304-coefficient matrix never round-trips through an orchestration buffer (the
    single largest copy in the per-leaf budget). Semantically `mlk_matvec_invntt
    (mlk_gen_matrix_T pk) r̂`; emitted as one leaf, so the matrix copy is gone. -/
noncomputable opaque mlk_gen_matvec : MlPubKey → MlVec → MlVec
/-- `invntt(t̂ᵀ ∘ r̂)` (polyvec dot + invntt → single poly). -/
noncomputable opaque mlk_polyvec_dot : MlVec → MlVec → MlPoly
-- (single-poly add reuses the existing `mlk_poly_add`)
/-- Barrett reduce a single poly (`__poly_reduce`). -/
noncomputable opaque mlk_poly_reduce : MlPoly → MlPoly
/-- Compress + concat the ciphertext `Compress_du(u)‖Compress_dv(v)`. -/
noncomputable opaque mlk_compress_cipher : MlVec → MlPoly → MlCipher

-- Decaps (K-PKE.Decrypt) leaves:
/-- `u = Decompress_du(c1)` (`__polyvec_decompress`). -/
noncomputable opaque mlk_decompress_u : MlCipher → MlVec
/-- `v = Decompress_dv(c2)` (`_poly_decompress`). -/
noncomputable opaque mlk_decompress_v : MlCipher → MlPoly
/-- Decode `ŝ` from the secret key (`__polyvec_frombytes`). -/
noncomputable opaque mlk_sk_decode : MlEncVec → MlVec
/-- Single-poly subtraction `v - t` (`_poly_sub`). -/
noncomputable opaque mlk_poly_sub : MlPoly → MlPoly → MlPoly
/-- `m = Compress_1(mp)` (`_i_poly_tomsg`). -/
noncomputable opaque mlk_tomsg : MlPoly → MlMsg
/-- **Fused** encaps v-path `reduce(invntt(t̂ᵀ∘r̂) + e2 + k)` — the
    `mlk_polyvec_dot` + two `mlk_poly_add` + `mlk_poly_reduce` chain as ONE leaf, so
    the 256-coeff poly never crosses an orchestration buffer between the four steps
    (3 inter-leaf copies + 3 calls removed). Verified-fusion-backed (`JasminLeafFusion`). -/
noncomputable opaque mlk_v_acc : MlVec → MlVec → MlPoly → MlPoly → MlPoly
/-- **Fused** decaps decrypt `tomsg(reduce(v − invntt(ŝᵀ∘û)))` — the `mlk_polyvec_dot`
    + `mlk_poly_sub` + `mlk_poly_reduce` + `mlk_tomsg` chain as ONE leaf. -/
noncomputable opaque mlk_decrypt : MlVec → MlVec → MlPoly → MlMsg
opaque MlUV.Impl : NonemptyType.{0}
/-- `u‖v` bundle (3-poly `u` ++ 1-poly `v` = `TPolyVec 3329 256 4`), the encaps
    arith-core output; the C harness splits + compresses it. -/
def MlUV : Type := MlUV.Impl.type
instance : Nonempty MlUV := MlUV.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlUV.default : MlUV
noncomputable instance : Inhabited MlUV := ⟨MlUV.default⟩
/-- `Âᵀ = gen_matrix(ρ, transposed=1)` taking ρ as a bare 32-byte seed. -/
noncomputable opaque mlk_gen_matrix_T_rho : MlSeed → MlMat
/-- Concatenate `u` (polyvec) and `v` (poly) into the `u‖v` bundle. -/
noncomputable opaque mlk_uv_concat : MlVec → MlPoly → MlUV

/-! #### ML-KEM-768 FO transform (full KEM = INDCPA core + Fujisaki–Okamoto).
Faithful to formosa `__crypto_kem_enc_jazz` / `__crypto_kem_dec_jazz` (`kem.jinc`).

ENCAPS:  H = SHA3-256(pk‖, 1184);  kr = SHA3-512(m‖H) = K‖r';
         ct = INDCPA_enc(m, pk, r=kr[32:64]);  K = kr[0:32].
DECAPS:  m' = INDCPA_dec(ct, sk[0:1152]);  H = sk[2336:2368];
         kr = SHA3-512(m'‖H);  ctpc = INDCPA_enc(m', pk=sk[1152:2336], r=kr[32:64]);
         cnd = verify(ct, ctpc);  Kbar = SHAKE256(z=sk[2368:2400] ‖ ct, 32);
         K = cnd ? kr[0:32] : Kbar. -/

opaque MlSharedSecret.Impl : NonemptyType.{0}
/-- 32-byte FO shared secret `K` (`TBytes 32`). -/
def MlSharedSecret : Type := MlSharedSecret.Impl.type
instance : Nonempty MlSharedSecret := MlSharedSecret.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlSharedSecret.default : MlSharedSecret
noncomputable instance : Inhabited MlSharedSecret := ⟨MlSharedSecret.default⟩
opaque MlSecKeyFull.Impl : NonemptyType.{0}
/-- Full ML-KEM-768 secret key `sk = sk_pke‖pk‖H(pk)‖z` (`TBytes 2400`). -/
def MlSecKeyFull : Type := MlSecKeyFull.Impl.type
instance : Nonempty MlSecKeyFull := MlSecKeyFull.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlSecKeyFull.default : MlSecKeyFull
noncomputable instance : Inhabited MlSecKeyFull := ⟨MlSecKeyFull.default⟩
opaque MlKr.Impl : NonemptyType.{0}
/-- SHA3-512 digest `kr = K‖r'` (`TBytes 64`). -/
def MlKr : Type := MlKr.Impl.type
instance : Nonempty MlKr := MlKr.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlKr.default : MlKr
noncomputable instance : Inhabited MlKr := ⟨MlKr.default⟩
opaque MlHash32.Impl : NonemptyType.{0}
/-- 32-byte hash `H = SHA3-256(pk)` (`TBytes 32`). -/
def MlHash32 : Type := MlHash32.Impl.type
instance : Nonempty MlHash32 := MlHash32.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlHash32.default : MlHash32
noncomputable instance : Inhabited MlHash32 := ⟨MlHash32.default⟩
opaque MlCond.Impl : NonemptyType.{0}
/-- Constant-time selector `cnd ∈ {0,1}` from `verify` (`TBytes 8`, a `u64`). -/
def MlCond : Type := MlCond.Impl.type
instance : Nonempty MlCond := MlCond.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlCond.default : MlCond
noncomputable instance : Inhabited MlCond := ⟨MlCond.default⟩
opaque MlKemEnc.Impl : NonemptyType.{0}
/-- Bundled FO encaps output `K‖ct` (`TBytes 1120`); the C harness splits it. -/
def MlKemEnc : Type := MlKemEnc.Impl.type
instance : Nonempty MlKemEnc := MlKemEnc.Impl.property
/-- Axiomatic inhabitant. -/ axiom MlKemEnc.default : MlKemEnc
noncomputable instance : Inhabited MlKemEnc := ⟨MlKemEnc.default⟩

-- FO encaps leaves:
/-- `H = SHA3-256(pk[0:1184])` (`_isha3_256`). -/
noncomputable opaque mlk_hash_h : MlPubKey → MlHash32
/-- `kr = SHA3-512(m‖H)` (`_sha3_512_64`; concats `m` and `H` into a 64-byte buf). -/
noncomputable opaque mlk_hash_g_kem : MlMsg → MlHash32 → MlKr
/-- `K = kr[0:32]` (the shared secret). -/
noncomputable opaque mlk_kr_k : MlKr → MlSharedSecret
/-- `r' = kr[32:64]` (the INDCPA-enc coins). -/
noncomputable opaque mlk_kr_r : MlKr → MlSeed
/-- Bundle `K‖ct` into the 1120-byte encaps output. -/
noncomputable opaque mlk_kem_pack : MlSharedSecret → MlCipher → MlKemEnc

-- FO decaps leaves (the INDCPA decode/encode happen via the existing leaves
-- against slices of the full secret key):
/-- INDCPA secret key `sk_pke = sk[0:1152]` (decoded by `mlk_sk_decode`'s leaf). -/
noncomputable opaque mlk_sk_pke : MlSecKeyFull → MlEncVec
/-- Embedded public key `pk = sk[1152:2336]` (1184 bytes). -/
noncomputable opaque mlk_sk_pk : MlSecKeyFull → MlPubKey
/-- `H = sk[2336:2368]` (hash of the public key, stored at keygen). -/
noncomputable opaque mlk_sk_h : MlSecKeyFull → MlHash32
/-- `Kbar = SHAKE256(z=sk[2368:2400] ‖ ct, 32)` (`_shake256_1120_32`). -/
noncomputable opaque mlk_hash_j : MlSecKeyFull → MlCipher → MlSharedSecret
/-- `cnd = verify(ct, ctpc)` — `1` iff the re-encryption matches (`__verify`). -/
noncomputable opaque mlk_verify : MlCipher → MlCipher → MlCond
/-- `K = cnd ? Kgood : Kbar` (constant-time `__cmov`). -/
noncomputable opaque mlk_select : MlCond → MlSharedSecret → MlSharedSecret → MlSharedSecret

/-! ### ML-DSA (Dilithium) NTT poly surface (`Z_8380417[X]/(X^256+1)`)

The lattice-signature analogue of the `MlPoly` ML-KEM surface, kept entirely
separate so the ML-KEM ops are undisturbed. ML-DSA's modulus is `q = 8380417`
(23-bit), so each coefficient is a native `u32`; a polynomial is 256 `u32`s.

The TowerType is `.TArr 256 .TU32` — 256 × 4 bytes = 1024 bytes = `memref 128`
(`encodeTy` packs at `t.storageBytes` = 4 bytes/coeff) — so the width-native
front at `w = 32` lowers it directly to `stackArr 32 256`, i.e. the
`reg ptr u32[256]` / `stack u32[256]` ABI of the libjade dilithium NTT leaves
(`ntt_avx2` / `poly_pointwise_montgomery` / `invntt_tomont_avx2`). The
3-leaf round trip `invntt(pointwise(ntt a, ntt b))` carries the Montgomery
factors exactly as dilithium's own `poly_pointwise_montgomery` composition:
`ntt` introduces no scale, `poly_pointwise_montgomery` multiplies by `R⁻¹`,
`invntt_tomont` multiplies by `R`, so the factors cancel and the result is the
normal-domain negacyclic product mod `q`. -/

opaque MldsaPoly.Impl : NonemptyType.{0}
/-- Opaque ML-DSA polynomial (`Z_8380417[X]/(X^256+1)`, 256 `u32` coeffs). -/
def MldsaPoly : Type := MldsaPoly.Impl.type
instance : Nonempty MldsaPoly := MldsaPoly.Impl.property
/-- Axiomatic inhabitant. -/ axiom MldsaPoly.default : MldsaPoly
noncomputable instance : Inhabited MldsaPoly := ⟨MldsaPoly.default⟩
/-- Forward NTT (`ntt_avx2`/`fft`; no extra scaling). -/
noncomputable opaque mld_ntt : MldsaPoly → MldsaPoly
/-- Inverse NTT to Montgomery domain (`invntt_tomont_avx2`/`ifft_to_mont`; ×R). -/
noncomputable opaque mld_invntt : MldsaPoly → MldsaPoly
/-- NTT-domain pointwise Montgomery multiply (`poly_pointwise_montgomery`; ×R⁻¹). -/
noncomputable opaque mld_pointwise : MldsaPoly → MldsaPoly → MldsaPoly
/-- Coefficientwise add (`poly_add`; no scale change). Domain-agnostic: adding two
    `×R⁻¹`-domain pointwise products keeps them in the `×R⁻¹` domain, so a chain of
    `mld_pointwise` results may be accumulated before the single `mld_invntt`. -/
noncomputable opaque mld_poly_add : MldsaPoly → MldsaPoly → MldsaPoly

opaque MldsaPolyVecL.Impl : NonemptyType.{0}
/-- Opaque ML-DSA length-`l=5` polyvec (`5 × MldsaPoly`, contiguous `u32[1280]`).
    The lattice-signature analogue of the ML-KEM bundled polyvec the
    `polyvec_dot3` emit uses: ML-DSA's matrix-vector dot needs `out + 10`
    per-poly pointers `= 11 > 6` GP registers (the x86-64 export ABI limit), so
    the 5 component polys are passed as ONE `u32[1280]` buffer and `slice@{j·256}`-d
    into their 5 component polys inside the body — exactly how ML-KEM's
    `polyvec_dot3` sidesteps the same blocker for `k=3`. Encodes as
    `.TArr 1280 .TU32 → memref 640` (1280 coeffs × 4 bytes = 5120 bytes = 640 u64
    limbs), so `mldsaDotWidthOf` lowers it to `stack u32[1280]`, slicing
    into the `stack u32[256]` poly leaves with no width mismatch. -/
def MldsaPolyVecL : Type := MldsaPolyVecL.Impl.type
instance : Nonempty MldsaPolyVecL := MldsaPolyVecL.Impl.property
/-- Axiomatic inhabitant. -/ axiom MldsaPolyVecL.default : MldsaPolyVecL
noncomputable instance : Inhabited MldsaPolyVecL := ⟨MldsaPolyVecL.default⟩
/-- Component-`0` window `v[0:256]` of a length-5 polyvec (`slice@0`). -/
noncomputable opaque mld_vl_get0 : MldsaPolyVecL → MldsaPoly
/-- Component-`1` window `v[256:256]` (`slice@256`). -/
noncomputable opaque mld_vl_get1 : MldsaPolyVecL → MldsaPoly
/-- Component-`2` window `v[512:256]` (`slice@512`). -/
noncomputable opaque mld_vl_get2 : MldsaPolyVecL → MldsaPoly
/-- Component-`3` window `v[768:256]` (`slice@768`). -/
noncomputable opaque mld_vl_get3 : MldsaPolyVecL → MldsaPoly
/-- Component-`4` window `v[1024:256]` (`slice@1024`). -/
noncomputable opaque mld_vl_get4 : MldsaPolyVecL → MldsaPoly

/-! ### ML-DSA-65 kernel surface (`TPolyMod`/`TPolyVec`/`TPolyMat` slots)

The reification surface for the three top-level ML-DSA-65 kernels
(`mldsa_keygen_kernel` / `mldsa_sign_kernel` / `mldsa_verify_kernel`).
Distinct from the NTT-word `MldsaPoly` surface above (which maps to
`.TArr 256 .TU32` for the libjade NTT leaves): these map to the
`.TPolyMod 8380417 256` / `.TPolyVec 8380417 256 k` /
`.TPolyMat 8380417 256 6 5` tower types the hand-authored kernels use,
so the reified term emits the *same* `stack u32[…]` ABI the emit test
pins.  ML-DSA-65: `q = 8380417`, `n = 256`, `k = 6`, `l = 5`.

`MldBytes n` is a *size-indexed* byte buffer: the size travels in the
Lean type, so `bytes_concat_*`'s result type (`TBytes (m+n+…)`) is read
directly from the result let-binder's Lean type by the reifier, with no
fixed entry in `knownOps`.  The
result tower type is a function of the argument sizes, realized through
the dependent return type of the concat axioms. -/

opaque MldBytes.Impl : Nat → NonemptyType.{0}
/-- Size-indexed ML-DSA byte buffer (`MldBytes n ↦ .TBytes n`). -/
def MldBytes (x : Nat) : Type := (MldBytes.Impl x).type
instance (x : Nat) : Nonempty (MldBytes x) := (MldBytes.Impl x).property
/-- Axiomatic inhabitant. -/ axiom MldBytes.default (n : Nat) : MldBytes n
noncomputable instance (n : Nat) : Inhabited (MldBytes n) := ⟨MldBytes.default n⟩

opaque MldPoly.Impl : NonemptyType.{0}
/-- ML-DSA-65 polynomial (`Z_8380417[X]/(X^256+1)`, `.TPolyMod 8380417 256`). -/
def MldPoly : Type := MldPoly.Impl.type
instance : Nonempty MldPoly := MldPoly.Impl.property
/-- Axiomatic inhabitant. -/ axiom MldPoly.default : MldPoly
noncomputable instance : Inhabited MldPoly := ⟨MldPoly.default⟩
opaque MldVecL.Impl : NonemptyType.{0}
/-- Length-`l = 5` polyvec (`.TPolyVec 8380417 256 5`). -/
def MldVecL : Type := MldVecL.Impl.type
instance : Nonempty MldVecL := MldVecL.Impl.property
/-- Axiomatic inhabitant. -/ axiom MldVecL.default : MldVecL
noncomputable instance : Inhabited MldVecL := ⟨MldVecL.default⟩
opaque MldVecK.Impl : NonemptyType.{0}
/-- Length-`k = 6` polyvec (`.TPolyVec 8380417 256 6`). -/
def MldVecK : Type := MldVecK.Impl.type
instance : Nonempty MldVecK := MldVecK.Impl.property
/-- Axiomatic inhabitant. -/ axiom MldVecK.default : MldVecK
noncomputable instance : Inhabited MldVecK := ⟨MldVecK.default⟩
opaque MldMat.Impl : NonemptyType.{0}
/-- `k × l = 6 × 5` matrix (`.TPolyMat 8380417 256 6 5`). -/
def MldMat : Type := MldMat.Impl.type
instance : Nonempty MldMat := MldMat.Impl.property
/-- Axiomatic inhabitant. -/ axiom MldMat.default : MldMat
noncomputable instance : Inhabited MldMat := ⟨MldMat.default⟩

/-! #### Byte-side plumbing: concat (size-additive) + slice (size-erasing) -/

/-- Concatenate two byte buffers; result size is the sum (the
    dependent return type carries the summed `TBytes`). -/
noncomputable opaque mld_bytes_concat_2 {m n : Nat} : MldBytes m → MldBytes n → MldBytes (m + n)
/-- Concatenate three byte buffers. -/
axiom mld_bytes_concat_3 {m n p : Nat} :
  MldBytes m → MldBytes n → MldBytes p → MldBytes (m + n + p)
/-- Concatenate six byte buffers. -/
axiom mld_bytes_concat_6 {m n p r s t : Nat} :
  MldBytes m → MldBytes n → MldBytes p → MldBytes r → MldBytes s → MldBytes t →
  MldBytes (m + n + p + r + s + t)
/-- Slice `src[off..off+len]`.  The source argument is
    size-erased (reflects as `.TBytes 0` regardless of `m`) so the
    reified term emits the same bytes the hand-authored slice leaf does;
    the erasure is applied by the reifier's per-leaf typing hook, keyed
    on the `bytes_slice` leaf name. -/
noncomputable opaque mld_bytes_slice {m : Nat} (len : Nat) : MldBytes m → UInt64 → MldBytes len

/-! #### Hash / KDF leaves (fixed-size outputs) -/

/-- `H : SHAKE-256-32`. -/ axiom mld_hash_h32 {n : Nat} : MldBytes n → MldBytes 32
/-- `H : SHAKE-256-64`. -/ axiom mld_hash_h64 {n : Nat} : MldBytes n → MldBytes 64
/-- `H : SHAKE-256-128`. -/ axiom mld_hash_h128 {n : Nat} : MldBytes n → MldBytes 128

/-! #### Samplers / expanders -/

/-- ExpandA: `ρ → Â`. -/ axiom mld_expand_a : MldBytes 32 → MldMat
/-- ExpandS₁: `ρ' → s₁`. -/ axiom mld_expand_s1 : MldBytes 64 → MldVecL
/-- ExpandS₂: `ρ' → s₂`. -/ axiom mld_expand_s2 : MldBytes 64 → MldVecK
/-- ExpandMask: `(ρ', κ) → y`. -/ axiom mld_expand_mask : MldBytes 64 → UInt64 → MldVecL
/-- SampleInBall: `c̃[..32] → c`. -/ axiom mld_sample_in_ball : MldBytes 32 → MldPoly

/-! #### Poly / polyvec arithmetic -/

/-- In-place NTT on a poly. -/ axiom mld_poly_ntt : MldPoly → MldPoly
/-- Matrix·vector (`Â · ŝ`). -/ axiom mld_mat_vec_mul : MldMat → MldVecL → MldVecK
/-- Per-component NTT (length-`l`). -/ axiom mld_polyvec_l_ntt : MldVecL → MldVecL
/-- Per-component inverse NTT (length-`l`). -/ axiom mld_polyvec_l_invntt : MldVecL → MldVecL
/-- Componentwise add (length-`l`). -/ axiom mld_polyvec_l_add : MldVecL → MldVecL → MldVecL
/-- `dst[i] = c · a[i]` (poly scalar × length-`l` vec). -/
noncomputable opaque mld_polyvec_l_scalar_poly : MldPoly → MldVecL → MldVecL
/-- ∞-norm check (length-`l`) → `u64`. -/
noncomputable opaque mld_polyvec_l_norm_check : MldVecL → UInt64 → UInt64
/-- Per-component NTT (length-`k`). -/ axiom mld_polyvec_k_ntt : MldVecK → MldVecK
/-- Per-component inverse NTT (length-`k`). -/ axiom mld_polyvec_k_invntt : MldVecK → MldVecK
/-- Componentwise add (length-`k`). -/ axiom mld_polyvec_k_add : MldVecK → MldVecK → MldVecK
/-- Componentwise subtract (length-`k`). -/ axiom mld_polyvec_k_sub : MldVecK → MldVecK → MldVecK
/-- Negate every component (length-`k`). -/ axiom mld_polyvec_k_neg : MldVecK → MldVecK
/-- `dst[i] = c · a[i]` (poly scalar × length-`k` vec). -/
noncomputable opaque mld_polyvec_k_scalar_poly : MldPoly → MldVecK → MldVecK
/-- ∞-norm check (length-`k`) → `u64`. -/
noncomputable opaque mld_polyvec_k_norm_check : MldVecK → UInt64 → UInt64
/-- `t₁ · 2^d` fused NTT (verify-side). -/ axiom mld_polyvec_k_t1_shifted_ntt : MldVecK → MldVecK

/-! #### Decomposition (per-polyvec, length-`k`) -/

/-- `Power2Round` high component. -/ axiom mld_polyvec_k_power2round_hi : MldVecK → MldVecK
/-- `Power2Round` low component. -/ axiom mld_polyvec_k_power2round_lo : MldVecK → MldVecK
/-- `HighBits` poly-wise. -/ axiom mld_polyvec_k_high_bits : MldVecK → MldVecK
/-- `LowBits` poly-wise. -/ axiom mld_polyvec_k_low_bits : MldVecK → MldVecK
/-- `MakeHint(z, r)` poly-wise. -/ axiom mld_polyvec_k_make_hint : MldVecK → MldVecK → MldVecK
/-- `UseHint(h, r)` poly-wise. -/ axiom mld_polyvec_k_use_hint : MldVecK → MldVecK → MldVecK
/-- Hint 1-count → `u64`. -/ axiom mld_polyvec_k_hint_weight : MldVecK → UInt64

/-! #### Codec leaves (pack/unpack) -/

/-- Pack `s₁` (`l·128 = 640`). -/ axiom mld_polyvec_l_pack_eta : MldVecL → MldBytes 640
/-- Unpack `s₁`. -/ axiom mld_polyvec_l_unpack_eta : MldBytes 640 → MldVecL
/-- Pack `s₂` (`k·128 = 768`). -/ axiom mld_polyvec_k_pack_eta : MldVecK → MldBytes 768
/-- Unpack `s₂`. -/ axiom mld_polyvec_k_unpack_eta : MldBytes 768 → MldVecK
/-- Pack `t₁` (`k·320 = 1920`). -/ axiom mld_polyvec_k_pack_t1 : MldVecK → MldBytes 1920
/-- Unpack `t₁`. -/ axiom mld_polyvec_k_unpack_t1 : MldBytes 1920 → MldVecK
/-- Pack `t₀` (`k·416 = 2496`). -/ axiom mld_polyvec_k_pack_t0 : MldVecK → MldBytes 2496
/-- Unpack `t₀`. -/ axiom mld_polyvec_k_unpack_t0 : MldBytes 2496 → MldVecK
/-- Pack `z` (`l·640 = 3200`). -/ axiom mld_polyvec_l_pack_z : MldVecL → MldBytes 3200
/-- Unpack `z`. -/ axiom mld_polyvec_l_unpack_z : MldBytes 3200 → MldVecL
/-- Pack `w₁` (`k·192 = 1152`). -/ axiom mld_polyvec_k_pack_w1 : MldVecK → MldBytes 1152
/-- Hint encoding (`ω + k = 61`). -/ axiom mld_hint_pack : MldVecK → MldBytes 61
/-- Hint decoding. -/ axiom mld_hint_unpack : MldBytes 61 → MldVecK

/-! #### Accept / compare pseudo-leaves (→ `u64`) -/

/-- `accept = z_ok ∧ r0_ok ∧ h_wt ≤ ω`. -/
noncomputable opaque mld_sign_accept : UInt64 → UInt64 → UInt64 → UInt64
/-- Truncation-aware `c̃' == c̃` AND `z_ok`.  The two byte arguments are
    size-erased (reflect as `.TBytes 0`) like the slice source. -/
noncomputable opaque mld_verify_compare : MldBytes 64 → MldBytes 48 → UInt64 → UInt64

/-- Known field-op symbols recognized by the reifier. -/
meta def knownOps : List (Name × String × Nat × TowerType) :=
  [ (``fp_add,          "fp_add",          2, .TFp25519)
  , (``fp_sub,          "fp_sub",          2, .TFp25519)
  , (``fp_mul,          "fp_mul",          2, .TFp25519)
  , (``fp_sqr,          "fp_sqr",          1, .TFp25519)
  , (``fp_mul_a24,      "fp_mul_a24",      1, .TFp25519)
  , (``fp_opp,          "fp_opp",          1, .TFp25519)
  , (``fp_sq2,          "fp_sq2",          1, .TFp25519)
  , (``fp_sq4,          "fp_sq4",          1, .TFp25519)
  , (``fp_sq8,          "fp_sq8",          1, .TFp25519)
  , (``fp_invsqrt,      "fp_invsqrt",      1, .TFp25519)
  , (``fp_sqrt_ratio_i, "fp_sqrt_ratio_i", 2, .TFp25519)
  , (``fp_inv,          "fp_inv",          1, .TFp25519)
  , (``fp_cmov,         "fp_cmov",         3, .TFp25519)
  , (``fp_is_neg,       "fp_is_neg",       1, .TFp25519)
  , (``fp_is_zero,      "fp_is_zero",      1, .TFp25519)
  , (``scalar_add,      "scalar_add",      2, .TFpL25519)
  , (``scalar_sub,      "scalar_sub",      2, .TFpL25519)
  , (``scalar_mul,      "scalar_mul",      2, .TFpL25519)
  , (``scalar_neg,      "scalar_neg",      1, .TFpL25519)
  , (``scalar_inv,      "scalar_inv",      1, .TFpL25519)
  -- BLS-style base field `Fp` / extension `Fp2` (g1Add / g1Dbl / g2Add):
  , (``bls_fp_mul,      "fp_mul",          2, .TFp)
  , (``bls_fp_add,      "fp_add",          2, .TFp)
  , (``bls_fp_sub,      "fp_sub",          2, .TFp)
  , (``bls_fp_sqr,      "fp_sqr",          1, .TFp)
  , (``bls_fp2_mul,     "fp2_mul",         2, .TFp2)
  , (``bls_fp2_add,     "fp2_add",         2, .TFp2)
  , (``bls_fp2_sub,     "fp2_sub",         2, .TFp2)
  -- NIST P-256:
  , (``fp256_add,       "fp256_add",       2, .TFpP256)
  , (``fp256_sub,       "fp256_sub",       2, .TFpP256)
  , (``fp256_mul,       "fp256_mul",       2, .TFpP256)
  , (``fp256_sqr,       "fp256_sqr",       1, .TFpP256)
  , (``fp256_opp,       "fp256_opp",       1, .TFpP256)
  -- ML-KEM NTT layer (Z_3329[X]/(X^256+1)); leaf names match the lattice leaves.
  , (``mlk_ntt,         "ntt_3329_256",        1, .TPolyMod 3329 256)
  , (``mlk_invntt,      "ntt_invntt_3329_256", 1, .TPolyMod 3329 256)
  , (``mlk_basemul,     "ntt_basemul_3329_256", 2, .TPolyMod 3329 256)
  , (``mlk_poly_add,    "poly_add",            2, .TPolyMod 3329 256)
  -- ML-KEM coefficient-form arithmetic surface (MlkemLowCT.lean kernels);
  -- result type is the op's *output* type (args get their own type via the
  -- per-argument tower-type threading in `reifyChain`).
  , (``mlk_poly_mul_c,    "poly_mul",          2, .TPolyMod 3329 256)
  , (``mlk_poly_sub_c,    "poly_sub",          2, .TPolyMod 3329 256)
  , (``mlk_polyvec_add_c, "polyvec_add",       2, .TPolyVec 3329 256 3)
  , (``mlk_polyvec_dot_c, "polyvec_dot",       2, .TPolyMod 3329 256)
  , (``mlk_mat_vec_mul_c, "mat_vec_mul",       2, .TPolyVec 3329 256 3)
  -- ML-KEM-768 vector/matrix layer (k=3); result type is the polyvec.
  , (``pv_ntt,          "polyvec_ntt_3329_256_k3",    1, .TPolyVec 3329 256 3)
  , (``pv_invntt,       "polyvec_invntt_3329_256_k3", 1, .TPolyVec 3329 256 3)
  , (``mlk_matvec,      "matvec_acc_3329_256_k3",     2, .TPolyVec 3329 256 3)
  , (``pv_add,          "polyvec_add_3329_256_k3",    2, .TPolyVec 3329 256 3)
  -- ML-KEM-768 keygen byte-layer leaves (formosa __indcpa_keypair structure):
  , (``mlk_hash_g,      "sha3_512_32",                1, .TBytes 64)
  , (``mlk_gen_matrix,  "gen_matrix_3329_256_k3",     1, .TPolyMat 3329 256 3 3)
  , (``mlk_cbd_s,       "cbd_eta2_s_3329_256_k3",     1, .TPolyVec 3329 256 3)
  , (``mlk_cbd_e,       "cbd_eta2_e_3329_256_k3",     1, .TPolyVec 3329 256 3)
  , (``mlk_matvec_mont, "matvec_acc_mont_3329_256_k3", 2, .TPolyVec 3329 256 3)
  , (``mlk_pv_reduce,   "polyvec_reduce_3329_256_k3", 1, .TPolyVec 3329 256 3)
  , (``mlk_encode_vec,  "polyvec_encode_3329_256_k3", 1, .TBytes 1152)
  -- ML-KEM-768 encaps (K-PKE.Encrypt) leaves:
  , (``mlk_pk_decode,      "polyvec_frombytes_pk",          1, .TPolyVec 3329 256 3)
  , (``mlk_gen_matrix_T,   "gen_matrix_T_3329_256_k3",      1, .TPolyMat 3329 256 3 3)
  , (``mlk_frommsg,        "poly_frommsg",                  1, .TPolyMod 3329 256)
  , (``mlk_cbd_enc_r,      "cbd_enc_r_3329_256_k3",         1, .TPolyVec 3329 256 3)
  , (``mlk_cbd_enc_e1,     "cbd_enc_e1_3329_256_k3",        1, .TPolyVec 3329 256 3)
  , (``mlk_cbd_enc_e2,     "cbd_enc_e2_3329_256",           1, .TPolyMod 3329 256)
  -- Batched noise: one leaf samples all 7 encaps CBD polys (2 4-way perms),
  -- then 3 cheap split accessors carve out r / e1 / e2.
  , (``mlk_cbd_enc_all,    "cbd_enc_all_3329_256_k3",       1, .TPolyVec 3329 256 7)
  , (``mlk_noise_r,        "noise_split_r_3329_256_k3",     1, .TPolyVec 3329 256 3)
  , (``mlk_noise_e1,       "noise_split_e1_3329_256_k3",    1, .TPolyVec 3329 256 3)
  , (``mlk_noise_e2,       "noise_split_e2_3329_256",       1, .TPolyMod 3329 256)
  , (``mlk_matvec_invntt,  "matvec_invntt_3329_256_k3",     2, .TPolyVec 3329 256 3)
  , (``mlk_gen_matvec,     "gen_matvec_3329_256_k3",        2, .TPolyVec 3329 256 3)
  , (``mlk_polyvec_dot,    "polyvec_dot_invntt_3329_256_k3", 2, .TPolyMod 3329 256)
  , (``mlk_poly_reduce,    "poly_reduce",                   1, .TPolyMod 3329 256)
  , (``mlk_compress_cipher, "encrypt_compress_3329_256_k3", 2, .TBytes 1088)
  -- ML-KEM-768 decaps (K-PKE.Decrypt) leaves:
  , (``mlk_decompress_u,   "polyvec_decompress_3329_256_k3", 1, .TPolyVec 3329 256 3)
  , (``mlk_decompress_v,   "poly_decompress_3329_256",      1, .TPolyMod 3329 256)
  , (``mlk_sk_decode,      "polyvec_frombytes_sk",          1, .TPolyVec 3329 256 3)
  , (``mlk_poly_sub,       "poly_sub",                      2, .TPolyMod 3329 256)
  , (``mlk_tomsg,          "poly_tomsg",                    1, .TBytes 32)
  , (``mlk_v_acc,          "v_acc_3329_256_k3",             4, .TPolyMod 3329 256)
  , (``mlk_decrypt,        "decrypt_3329_256_k3",           3, .TBytes 32)
  -- encaps arith-core extras (KAT):
  , (``mlk_gen_matrix_T_rho, "gen_matrix_T_3329_256_k3",    1, .TPolyMat 3329 256 3 3)
  , (``mlk_uv_concat,      "uv_concat_k3",                  2, .TPolyVec 3329 256 4)
  -- ML-KEM-768 FO transform (full KEM) leaves:
  , (``mlk_hash_h,         "kem_hash_h",                    1, .TBytes 32)
  , (``mlk_hash_g_kem,     "kem_hash_g",                    2, .TBytes 64)
  , (``mlk_kr_k,           "kem_kr_k",                      1, .TBytes 32)
  , (``mlk_kr_r,           "kem_kr_r",                      1, .TBytes 32)
  , (``mlk_kem_pack,       "kem_pack",                      2, .TBytes 1120)
  , (``mlk_sk_pke,         "kem_sk_pke",                    1, .TBytes 1152)
  , (``mlk_sk_pk,          "kem_sk_pk",                     1, .TBytes 1184)
  , (``mlk_sk_h,           "kem_sk_h",                      1, .TBytes 32)
  , (``mlk_hash_j,         "kem_hash_j",                    2, .TBytes 32)
  , (``mlk_verify,         "kem_verify",                    2, .TBytes 8)
  , (``mlk_select,         "kem_select",                    3, .TBytes 32)
  -- ML-DSA (Dilithium) NTT layer (Z_8380417[X]/(X^256+1)); the leaf names are the
  -- `reg ptr u32[256]` shim wrappers in `ntt_leaves_dilithium.jinc`, which delegate
  -- to the libjade dilithium `ntt_avx2` / `poly_pointwise_montgomery` /
  -- `invntt_tomont_avx2` leaves (distinct names so the shim can `require` libjade
  -- without a self-collision — mirrors ML-KEM's `ntt_3329_256` wrapping `_poly_ntt`).
  , (``mld_ntt,            "mldsa_ntt_256",        1, .TArr 256 .TU32)
  , (``mld_invntt,         "mldsa_invntt_256",     1, .TArr 256 .TU32)
  , (``mld_pointwise,      "mldsa_pointwise_256",  2, .TArr 256 .TU32)
  , (``mld_poly_add,       "mldsa_poly_add_256",   2, .TArr 256 .TU32)
  -- ML-DSA length-5 polyvec component windows: `slice@{j·256}` sub-array leaves
  -- (constant-time, denotation-opaque) extracting the j-th `u32[256]` poly from a
  -- bundled `u32[1280]` polyvec — the register-ABI-saving bundling the dot uses.
  , (``mld_vl_get0,        "slice@0",              1, .TArr 256 .TU32)
  , (``mld_vl_get1,        "slice@256",            1, .TArr 256 .TU32)
  , (``mld_vl_get2,        "slice@512",            1, .TArr 256 .TU32)
  , (``mld_vl_get3,        "slice@768",            1, .TArr 256 .TU32)
  , (``mld_vl_get4,        "slice@1024",           1, .TArr 256 .TU32)
  -- ML-DSA-65 kernel surface (polynomial slots). For every entry the dest
  -- tower type is recovered from the result let-binder's Lean type
  -- (`leanTypeToTowerType`); the `tt` here is the natural result type used
  -- only as the fallback default for non-binder dests.  The two concat
  -- families and the slice are size-dependent: their dest type is read from
  -- the binder, and the slice source is size-erased.
  -- Byte-side plumbing:
  , (``mld_bytes_concat_2, "bytes_concat_2",       2, .TBytes 0)
  , (``mld_bytes_concat_3, "bytes_concat_3",       3, .TBytes 0)
  , (``mld_bytes_concat_6, "bytes_concat_6",       6, .TBytes 0)
  , (``mld_bytes_slice,    "bytes_slice",          2, .TBytes 0)
  -- Hash / KDF:
  , (``mld_hash_h32,       "hash_h32",             1, .TBytes 32)
  , (``mld_hash_h64,       "hash_h64",             1, .TBytes 64)
  , (``mld_hash_h128,      "hash_h128",            1, .TBytes 128)
  -- Samplers / expanders:
  , (``mld_expand_a,       "expand_a",             1, .TPolyMat 8380417 256 6 5)
  , (``mld_expand_s1,      "expand_s1",            1, .TPolyVec 8380417 256 5)
  , (``mld_expand_s2,      "expand_s2",            1, .TPolyVec 8380417 256 6)
  , (``mld_expand_mask,    "expand_mask",          2, .TPolyVec 8380417 256 5)
  , (``mld_sample_in_ball, "sample_in_ball",       1, .TPolyMod 8380417 256)
  -- Poly / polyvec arithmetic:
  , (``mld_poly_ntt,             "poly_ntt",              1, .TPolyMod 8380417 256)
  , (``mld_mat_vec_mul,          "mat_vec_mul",           2, .TPolyVec 8380417 256 6)
  , (``mld_polyvec_l_ntt,        "polyvec_l_ntt",         1, .TPolyVec 8380417 256 5)
  , (``mld_polyvec_l_invntt,     "polyvec_l_invntt",      1, .TPolyVec 8380417 256 5)
  , (``mld_polyvec_l_add,        "polyvec_l_add",         2, .TPolyVec 8380417 256 5)
  , (``mld_polyvec_l_scalar_poly,"polyvec_l_scalar_poly", 2, .TPolyVec 8380417 256 5)
  , (``mld_polyvec_l_norm_check, "polyvec_l_norm_check",  2, .TU64)
  , (``mld_polyvec_k_ntt,        "polyvec_k_ntt",         1, .TPolyVec 8380417 256 6)
  , (``mld_polyvec_k_invntt,     "polyvec_k_invntt",      1, .TPolyVec 8380417 256 6)
  , (``mld_polyvec_k_add,        "polyvec_k_add",         2, .TPolyVec 8380417 256 6)
  , (``mld_polyvec_k_sub,        "polyvec_k_sub",         2, .TPolyVec 8380417 256 6)
  , (``mld_polyvec_k_neg,        "polyvec_k_neg",         1, .TPolyVec 8380417 256 6)
  , (``mld_polyvec_k_scalar_poly,"polyvec_k_scalar_poly", 2, .TPolyVec 8380417 256 6)
  , (``mld_polyvec_k_norm_check, "polyvec_k_norm_check",  2, .TU64)
  , (``mld_polyvec_k_t1_shifted_ntt, "polyvec_k_t1_shifted_ntt", 1, .TPolyVec 8380417 256 6)
  -- Decomposition (per-polyvec, length-`k`):
  , (``mld_polyvec_k_power2round_hi, "polyvec_k_power2round_hi", 1, .TPolyVec 8380417 256 6)
  , (``mld_polyvec_k_power2round_lo, "polyvec_k_power2round_lo", 1, .TPolyVec 8380417 256 6)
  , (``mld_polyvec_k_high_bits,  "polyvec_k_high_bits",   1, .TPolyVec 8380417 256 6)
  , (``mld_polyvec_k_low_bits,   "polyvec_k_low_bits",    1, .TPolyVec 8380417 256 6)
  , (``mld_polyvec_k_make_hint,  "polyvec_k_make_hint",   2, .TPolyVec 8380417 256 6)
  , (``mld_polyvec_k_use_hint,   "polyvec_k_use_hint",    2, .TPolyVec 8380417 256 6)
  , (``mld_polyvec_k_hint_weight,"polyvec_k_hint_weight", 1, .TU64)
  -- Codec leaves:
  , (``mld_polyvec_l_pack_eta,   "polyvec_l_pack_eta",    1, .TBytes 640)
  , (``mld_polyvec_l_unpack_eta, "polyvec_l_unpack_eta",  1, .TPolyVec 8380417 256 5)
  , (``mld_polyvec_k_pack_eta,   "polyvec_k_pack_eta",    1, .TBytes 768)
  , (``mld_polyvec_k_unpack_eta, "polyvec_k_unpack_eta",  1, .TPolyVec 8380417 256 6)
  , (``mld_polyvec_k_pack_t1,    "polyvec_k_pack_t1",     1, .TBytes 1920)
  , (``mld_polyvec_k_unpack_t1,  "polyvec_k_unpack_t1",   1, .TPolyVec 8380417 256 6)
  , (``mld_polyvec_k_pack_t0,    "polyvec_k_pack_t0",     1, .TBytes 2496)
  , (``mld_polyvec_k_unpack_t0,  "polyvec_k_unpack_t0",   1, .TPolyVec 8380417 256 6)
  , (``mld_polyvec_l_pack_z,     "polyvec_l_pack_z",      1, .TBytes 3200)
  , (``mld_polyvec_l_unpack_z,   "polyvec_l_unpack_z",    1, .TPolyVec 8380417 256 5)
  , (``mld_polyvec_k_pack_w1,    "polyvec_k_pack_w1",     1, .TBytes 1152)
  , (``mld_hint_pack,            "hint_pack",             1, .TBytes 61)
  , (``mld_hint_unpack,          "hint_unpack",           1, .TPolyVec 8380417 256 6)
  -- Accept / compare pseudo-leaves:
  , (``mld_sign_accept,          "sign_accept",           3, .TU64)
  , (``mld_verify_compare,       "verify_compare",        3, .TU64) ]

/-- Match a fully-applied known op against the in-file `knownOps`
    table.  Returns `(leafName, argFVars, towerType, argTypes?)`; the
    `knownOps` entries are homogeneous, so `argTypes?` is `none`. -/
meta def matchOp? (e : Expr) :
    Option (String × Array Expr × TowerType × Option (List TowerType)) :=
  match e.getAppFnArgs with
  | (cn, args) =>
    match knownOps.find? (fun p => p.1 == cn) with
    | some (_, leafName, arity, tt) =>
      -- Keep only the *reifiable value* arguments (bound free variables):
      -- implicit size parameters (`{n : Nat}`) and explicit length
      -- literals (`bytes_slice`'s `len`) appear as non-fvar `Nat`
      -- arguments and are dropped here, so `arity` counts only the
      -- slots that become `Located`s.  Legacy ops (no implicits) are
      -- unaffected — all their arguments are already fvars.
      let valArgs := args.filter (·.isFVar)
      if valArgs.size == arity then some (leafName, valArgs, tt, none) else none
    | none => none

/-! ## 4. Reifier -/

/-- Extract the "user-chosen" binder name for a free variable, falling
    back to a generated name if the binder was anonymous. -/
def fvarDisplayName (fvarId : FVarId) : MetaM String := do
  let decl ← fvarId.getDecl
  pure decl.userName.toString

/-- Map a Lean-level binder type to the LowCT tower type used for a
    located slot of that type.

    `Fp25519 ↦ TFp25519`, `FpL25519 ↦ TFpL25519`, `FpP256 ↦ TFpP256`,
    and the various ML-KEM / ML-DSA surfaces to their `TPoly*` / `TBytes`
    / `TArr` forms.  The single-curve `Fp` / `Fp2` surfaces (BLS-style
    field) map to `TFp` / `TFp2`.  Anything else defaults to `TFp25519`
    (the X25519 surface). -/
def leanTypeToTowerType (t : Expr) : MetaM TowerType := do
  -- Size-indexed ML-DSA byte buffer `MldBytes n ↦ .TBytes n`: the size
  -- `n` travels in the Lean type, so the reified result tower type of a
  -- size-additive op (concat) is recovered from its result binder's type.
  if t.isAppOf ``MldBytes then
    if let some n ← getNatValue? (← whnf t.appArg!) then
      return .TBytes n
  if t.isConstOf ``FpL25519 then return .TFpL25519
  else if t.isConstOf ``FpP256 then return .TFpP256
  else if t.isConstOf ``Fp then return .TFp
  else if t.isConstOf ``Fp2 then return .TFp2
  else if t.isConstOf ``MlPoly then return .TPolyMod 3329 256
  else if t.isConstOf ``MlVec then return .TPolyVec 3329 256 3
  else if t.isConstOf ``MlMat then return .TPolyMat 3329 256 3 3
  else if t.isConstOf ``MlSeed then return .TBytes 32
  else if t.isConstOf ``MlRhoSigma then return .TBytes 64
  else if t.isConstOf ``MlEncVec then return .TBytes 1152
  else if t.isConstOf ``MlPubKey then return .TBytes 1184
  else if t.isConstOf ``MlMsg then return .TBytes 32
  else if t.isConstOf ``MlCipher then return .TBytes 1088
  else if t.isConstOf ``MlUV then return .TPolyVec 3329 256 4
  else if t.isConstOf ``MlSharedSecret then return .TBytes 32
  else if t.isConstOf ``MlSecKeyFull then return .TBytes 2400
  else if t.isConstOf ``MlKr then return .TBytes 64
  else if t.isConstOf ``MlHash32 then return .TBytes 32
  else if t.isConstOf ``MlCond then return .TBytes 8
  else if t.isConstOf ``MlKemEnc then return .TBytes 1120
  else if t.isConstOf ``MldsaPoly then return .TArr 256 .TU32
  else if t.isConstOf ``MldsaPolyVecL then return .TArr 1280 .TU32
  -- ML-DSA-65 kernel surface (polynomial slots):
  else if t.isConstOf ``MldPoly then return .TPolyMod 8380417 256
  else if t.isConstOf ``MldVecL then return .TPolyVec 8380417 256 5
  else if t.isConstOf ``MldVecK then return .TPolyVec 8380417 256 6
  else if t.isConstOf ``MldMat then return .TPolyMat 8380417 256 6 5
  -- `u64` / `Nat` scalar slots (slice offsets, norm-check bounds, accept flags):
  else if t.isConstOf ``UInt64 then return .TU64
  else if t.isConstOf ``Nat then return .TU64
  else return .TFp25519

/-- Tower type of an argument expression: if it is a free variable,
    use its declared Lean binder type (`leanTypeToTowerType`); otherwise
    fall back to the supplied default `tt` (the op's result type).  Used
    by the reifier to give each call argument its *own* surface tower
    type rather than the op's single registered result type. -/
def argTowerType (a : Expr) (default : TowerType) : MetaM TowerType := do
  if a.isFVar then
    let decl ← a.fvarId!.getDecl
    leanTypeToTowerType decl.type
  else
    pure default

/-- Byte-size-erasure hook.  A handful of leaves take a byte
    buffer whose size must be *erased* in the emitted `LowCT` (reflect as
    `.TBytes 0`) to match the hand-authored ABI the emit test pins:

    * `bytes_slice` source (argument 0) — sliced out of an opaque buffer
      whose full length is irrelevant to the leaf.
    * `verify_compare`'s two byte arguments (0 and 1) — the leaf knows the
      truncation, so its inputs are size-opaque.

    Returns the erased type when `(leafName, argIdx)` is one of those
    positions, else `none` (the per-argument binder type is used). -/
def erasedArgType? (leafName : String) (argIdx : Nat) : Option TowerType :=
  if leafName == "bytes_slice" ∧ argIdx == 0 then some (.TBytes 0)
  else if leafName == "verify_compare" ∧ (argIdx == 0 ∨ argIdx == 1) then some (.TBytes 0)
  else none

/-! ### Pattern matching against per-argument types

`patternArgMismatch?` decides whether a pattern whose `fnHead` already matches
the application head also fits its arguments, and describes the first
disagreement it finds.  The matcher below uses it in two ways: a pattern that
fits is the match, and a head whose every candidate pattern fails makes the
reifier raise the collected descriptions instead of returning `none`. -/

/-- The first disagreement between `p` and an application of `p.fnHead` to
    `args` at result type `resultTy`, or `none` when the pattern fits.

    The argument count is checked against `p.arity` for every pattern.  The
    remaining conditions apply to a pattern carrying `argTypes = some ts`, and
    leave a pattern without them matched on arity alone.

    * `ts.length` equals `p.arity`.
    * A Lean type that `leanTypeToTowerType` maps to a surface fixes the
      tower type at that position, and at the destination.  A Lean type
      outside that map — an opaque surface type such as a curve scalar or
      point — is not constrained by this condition.
    * An argument whose Lean type is the leaf's result type carries
      `p.towerType`, the type of the destination it could be written to.
    * The partition of argument positions by declared tower type agrees with
      their partition by Lean type: two positions carrying the same declared
      type have the same Lean type, and two positions carrying different
      declared types have different Lean types.

    Together the last two separate the argument widths of a heterogeneous
    leaf from its Lean signature, so a registration listing them in the wrong
    order, or collapsing two of them, is a mismatch rather than a match. -/
def patternArgMismatch? (p : LowCTPattern) (args : Array Expr)
    (resultTy : Expr) : MetaM (Option MessageData) := do
  if args.size != p.arity then
    return some m!"{p.name}: arity {p.arity}, applied to {args.size} arguments"
  match p.argTypes with
  | none => return none
  | some ts =>
    if ts.length != p.arity then
      return some
        m!"{p.name}: arity {p.arity}, but argTypes lists {ts.length} types"
    let resTy ← whnf resultTy
    -- `leanTypeToTowerType` answers `.TFp25519` both for that surface and for
    -- a Lean type it does not map, so only a non-default answer constrains a
    -- position.
    let resSurface ← leanTypeToTowerType resTy
    if resSurface != .TFp25519 ∧ resSurface != p.towerType then
      return some
        m!"{p.name}: the destination is declared {toString (repr p.towerType)} \
           but the result type {resTy} maps to {toString (repr resSurface)}"
    let tys ← args.mapM fun a => do whnf (← inferType a)
    for i in [0 : args.size] do
      let declared := ts[i]!
      let surface ← leanTypeToTowerType tys[i]!
      if surface != .TFp25519 ∧ surface != declared then
        return some
          m!"{p.name}: argument {i} is declared {toString (repr declared)} but \
             its Lean type {tys[i]!} maps to {toString (repr surface)}"
      if (← isDefEq tys[i]! resTy) ∧ declared != p.towerType then
        return some
          m!"{p.name}: argument {i} has the leaf's result type {resTy} but is \
             declared {toString (repr declared)} against the destination's \
             {toString (repr p.towerType)}"
      for j in [i + 1 : args.size] do
        let sameLean ← isDefEq tys[i]! tys[j]!
        if (ts[j]! == declared) != sameLean then
          return some
            (if sameLean then
              m!"{p.name}: arguments {i} and {j} have the same Lean type \
                 {tys[i]!} but are declared {toString (repr declared)} and \
                 {toString (repr ts[j]!)}"
             else
              m!"{p.name}: arguments {i} and {j} are both declared \
                 {toString (repr declared)} but have Lean types {tys[i]!} and \
                 {tys[j]!}")
    return none

/-- Match a fully-applied op against the dynamic
    `LowCTPattern` registry **and** the persistent
    `@[rust_cmd_pattern]`-tagged declarations.  Consulted *after*
    `matchOp?` fails, so in-file `knownOps` entries take precedence
    over registered instances.

    Two registries are consulted:
    1. `rustCmdPatternRegistry` — the `IO.Ref` populated by direct
       `LowCTPattern.register` calls (`initialize` blocks).
    2. `rustCmdPatternExt` — the persistent extension populated by
       `@[rust_cmd_pattern]` attribute applications.  Resolution
       requires `Lean.Meta.evalExpr`, which is `unsafe`; this
       function is therefore `unsafe` and exposed via
       `@[implemented_by]` for safe consumption.

    An application whose head matches no registered pattern gives `none`,
    which is the reifier's ordinary fall-through.  An application whose head
    does match, at a set of patterns none of which fits its arguments, raises
    an error listing each candidate's disagreement as reported by
    `patternArgMismatch?`, so a declined match is distinguishable from an
    unregistered head. -/
unsafe def matchPatternUnsafe (e : Expr) :
    MetaM (Option (String × Array Expr × TowerType × Option (List TowerType))) := do
  match e.getAppFnArgs with
  | (cn, args) =>
    let resultTy ← inferType e
    -- The first fitting pattern is the match; the disagreements of the
    -- patterns that share the head but do not fit are accumulated, and
    -- reported only if no pattern fits.  Both registries are walked in the
    -- same pass, the `IO.Ref` one first, so a fitting pattern stops the walk
    -- before the remaining tagged declarations are evaluated.
    let mut reasons : Array MessageData := #[]
    for p in (← (LowCTPattern.snapshot : IO _)) do
      if p.fnHead == cn then
        match ← patternArgMismatch? p args resultTy with
        | none   => return some (p.name, args, p.towerType, p.argTypes)
        | some r => reasons := reasons.push r
    let names ← LowCTPattern.taggedDecls
    for n in names do
      if let some _ := (← getEnv).find? n then
        let pat? ← try
            pure (some (← Lean.Meta.evalExpr LowCTPattern
              (Lean.mkConst ``LowCTPattern) (Lean.mkConst n)))
          catch _ => pure none
        if let some pat := pat? then
          if pat.fnHead == cn then
            match ← patternArgMismatch? pat args resultTy with
            | none   => return some (pat.name, args, pat.towerType, pat.argTypes)
            | some r => reasons := reasons.push r
    if reasons.isEmpty then
      return none
    throwError
      "reifier: the head {cn} is registered but no pattern fits this \
       application:{indentD (MessageData.joinSep reasons.toList Format.line)}"

/-- Safe wrapper over `matchPatternUnsafe`.  The `IO.Ref`-only path
    is sufficient if you don't use `@[rust_cmd_pattern]` and only
    register patterns via direct `LowCTPattern.register` calls. -/
@[implemented_by matchPatternUnsafe]
opaque matchPattern? (e : Expr) :
    MetaM (Option (String × Array Expr × TowerType × Option (List TowerType)))

/-- If the (whnf'd) expression `v` is a `u64` / `Nat` literal, return its
    `Nat` value.  Recognizes bare `Nat` literals, `UInt64.ofBitVec n#64`,
    and `{ toBitVec := n#64 }`.  Used by the reifier to emit
    `RLetU64Zero` + `RScalarSet` for `let off : u64 := n` scalar-constant
    bindings (the `bytes_slice` offset idiom in the byte-side kernels). -/
def scalarLitValue? (v : Expr) : MetaM (Option Nat) := do
  -- Only treat `v` as a scalar literal if its type is `Nat` or `UInt64`
  -- (so we never mis-read an opaque field element).
  let ty ← whnf (← inferType v)
  if ty.isConstOf ``Nat then
    let n ← whnf v
    getNatValue? n
  else if ty.isConstOf ``UInt64 then
    -- Reduce `BitVec.toNat (UInt64.toBitVec v)` to a ground `Nat`.
    let asNat ← whnf (← mkAppM ``BitVec.toNat #[← mkAppM ``UInt64.toBitVec #[v]])
    getNatValue? asNat
  else
    return none

/-- Walk the let-bindings of a telescope-extracted body, emitting an
    `RCall` (or scalar-constant `RLetU64Zero`/`RScalarSet`) for each known
    `let`-binder.  Returns the accumulated `LowCT` prefix; the caller then
    handles the final return expression (single var/op, or a tuple of
    output slots).  Shared by `reifyChain` (single output) and
    `reifyChainMulti` (tuple output). -/
partial def reifyBindings (bindings : Array Expr) (outNames : List String) :
    MetaM LowCT := do
  -- Each `x ∈ bindings` is an fvar; for let-binders we can recover its
  -- value via `FVarId.getValue?`. For lambda-binders we just track the
  -- name (no emitted op).
  --
  -- `outNames` lists the kernel's output slots (`&mut`-passed by the
  -- emit ABI): an intermediate let-bound *poly/byte* dest is declared
  -- with a preceding `RLetZero` (so the emit stack-allocates + zeroes
  -- it, matching the hand-authored `rc_let` convention), but an output
  -- slot is NOT redeclared (it is a caller-supplied slot).
  let mut acc : LowCT := .RSkip
  for x in bindings do
    let fvarId := x.fvarId!
    let decl ← fvarId.getDecl
    match decl with
    | LocalDecl.cdecl .. =>
        -- Lambda-bound parameter — no RCall to emit.
        pure ()
    | LocalDecl.ldecl (value := v) .. =>
        -- Scalar-literal `let off : u64 := n` binding: emit
        -- `RLetU64Zero name; RScalarSet name n` (matching the
        -- `rc_letU64` + `rc_set` DSL).  Checked BEFORE the op path so a
        -- bare numeral is never mis-handled as a leaf call.
        if let some n ← scalarLitValue? v then
          let nm ← fvarDisplayName fvarId
          acc := .RSeq acc (.RSeq (.RLetU64Zero nm .RSkip) (.RScalarSet nm n))
          continue
        -- Try the `whnf`-then-`matchOp?` path FIRST,
        -- so the in-file `knownOps` table (and the `#eval` smoke
        -- tests in this module) never touch the computable-pattern
        -- registry — that avoids forcing same-module `[init]` evaluation
        -- of `rustCmdPatternComputableExt` on table consumers.
        --
        -- Only if `matchOp?` fails do we consult the dynamic registry,
        -- and only then do we check `isComputablePatternHead?` (BEFORE
        -- running `whnf`), so that a `def`-bodied leaf's head isn't
        -- unfolded by `whnf` and lost — the "typeclass-arity" failure
        -- mode the L3 bridge agent flagged for Path B.
        let vReducedDefault ← whnf v
        let legacyMatch := matchOp? vReducedDefault
        let matchResult ← match legacyMatch with
          | some r => pure (some r)
          | none =>
              -- Table match failed.  Check the computable registry.  If the
              -- head is a registered computable leaf, match on the
              -- *un-whnf'd* `v` (so the head isn't unfolded); otherwise
              -- fall back to the dynamic registry on the whnf'd value.
              let computableHead ← isComputablePatternHead? v
              if computableHead then
                matchPattern? v
              else
                matchPattern? vReducedDefault
        let vReduced := vReducedDefault
        match matchResult with
        | some (leafName, argExprs, tt, argTys?) =>
            -- Convert each argExpr to its bound variable's string name,
            -- giving each its *own* surface tower type: the byte-size erasure
            -- hook first (specific `(leaf, argIdx)` positions at
            -- `.TBytes 0`), then the pattern's declared per-argument type
            -- when it carries one, then the Lean binder type, and the op's
            -- result type `tt` only as the last fallback.
            let argLocs ← argExprs.mapIdxM fun i a => do
              let a ← whnf a
              unless a.isFVar do
                throwError "reifyChain: op argument is not a bound variable:{indentExpr a}"
              let n ← fvarDisplayName a.fvarId!
              let argTT ← match erasedArgType? leafName i with
                | some e => pure e
                | none   =>
                  match argTys?.bind (·[i]?) with
                  | some t => pure t
                  | none   => argTowerType a tt
              pure ({ locVar := n, locSrc := argTT } : Located)
            let destName ← fvarDisplayName fvarId
            let args : List Located := argLocs.toList
            -- The dest tower type is read from the *result
            -- binder's* Lean type (so size-additive concat dests get the
            -- summed `.TBytes`), falling back to the op's registered `tt`
            -- when the binder type doesn't map to a surface (table ops).
            let destTT ← do
              let bt ← leanTypeToTowerType decl.type
              pure (if bt == .TFp25519 ∧ tt != .TFp25519 then tt else bt)
            let dest : Located :=
              { locVar := destName, locSrc := destTT }
            let call : LowCT := .RCall leafName dest args
            -- Declare the dest slot (`RLetZero`) unless it is an output
            -- slot (caller-supplied `&mut`).  Mirrors the hand-authored
            -- `rc_let` + `rc_call` pairing so the emit stack-allocates the
            -- intermediate poly/byte/scalar buffers.
            let decl : LowCT :=
              if outNames.contains destName then call
              else .RSeq (.RLetZero destName destTT .RSkip) call
            acc := .RSeq acc decl
        | none =>
            throwError
              "reifyChain: unsupported let-value (expected a known fp_*):{indentExpr vReduced}"
  pure acc

/-- Walk the telescope-extracted body of a let-chain + return expression,
    emitting an `RCall` for each known `fp_*` `let`-binder and returning
    the final result variable's name (single-output). -/
partial def reifyChain (bindings : Array Expr) (finalExpr : Expr) :
    MetaM (LowCT × String) := do
  -- Determine the output slot name first (the final fvar, if any) so the
  -- binding that writes it is not redeclared with an `RLetZero`.
  let finalReducedDefault ← whnf finalExpr
  let outName? ← if finalReducedDefault.isFVar then
      pure (some (← fvarDisplayName finalReducedDefault.fvarId!))
    else pure none
  let acc ← reifyBindings bindings (outName?.toList)
  -- Handle the final expression: either a bound variable (return it
  -- directly) or a call (emit one last RCall binding a fresh result
  -- name "__result"). Same computable-head fallback pattern as in the
  -- let-binder path above: table matchOp? FIRST (so the #eval
  -- smoke tests never touch the computable registry), then the
  -- computable check only if matchOp? failed.
  if finalReducedDefault.isFVar then
    let retName ← fvarDisplayName finalReducedDefault.fvarId!
    pure (acc, retName)
  else
    let legacyMatch := matchOp? finalReducedDefault
    let matchResult ← match legacyMatch with
      | some r => pure (some r)
      | none =>
          let computableHead ← isComputablePatternHead? finalExpr
          if computableHead then
            matchPattern? finalExpr
          else
            matchPattern? finalReducedDefault
    let finalReduced := finalReducedDefault
    match matchResult with
    | some (leafName, argExprs, tt, argTys?) =>
        let argLocs ← argExprs.mapIdxM fun i a => do
          let a ← whnf a
          unless a.isFVar do
            throwError "reifyChain: final op argument is not a bound variable:{indentExpr a}"
          let n ← fvarDisplayName a.fvarId!
          let argTT ← match erasedArgType? leafName i with
            | some e => pure e
            | none   =>
              match argTys?.bind (·[i]?) with
              | some t => pure t
              | none   => argTowerType a tt
          pure ({ locVar := n, locSrc := argTT } : Located)
        let retName := "__result"
        let args : List Located := argLocs.toList
        let dest : Located :=
          { locVar := retName, locSrc := tt }
        let call : LowCT := .RCall leafName dest args
        pure (.RSeq acc call, retName)
    | none =>
        throwError
          "reifyChain: final expression is neither a bound var nor a known fp_* op:{indentExpr finalReduced}"

/-- Flatten a (possibly nested, right-associated) `Prod.mk`-tuple
    expression into its component leaf expressions.  `(a, b, c)` parses as
    `Prod.mk a (Prod.mk b c)`, so the right component is recursively
    flattened.  A non-`Prod.mk` expression is a singleton leaf. -/
partial def flattenTuple (e : Expr) : Array Expr :=
  if e.isAppOfArity ``Prod.mk 4 then
    let a := e.appFn!.appArg!
    let b := e.appArg!
    #[a] ++ flattenTuple b
  else
    #[e]

/-- Multi-output variant of `reifyChain`: the final expression must be a
    **tuple** `(o₀, o₁, …)` whose components are each a bound variable.
    Each component's variable name becomes an output slot — the body
    (the let-chain) already wrote to those names — so no extra `RCall` is
    emitted.  Returns the chain body and the ordered list of output names.

    Requiring tuple components to be bound variables (rather than inline
    ops) keeps the output ABI explicit: every output is a named slot the
    body assigns, exactly the `&mut`-slot convention the emit consumers
    (`ppRustFunction` / `emitFunc`) read. -/
partial def reifyChainMulti (bindings : Array Expr) (finalExpr : Expr) :
    MetaM (LowCT × List String) := do
  let finalReduced ← whnf finalExpr
  let comps := flattenTuple finalReduced
  if comps.size < 2 then
    throwError
      "reifyChainMulti: expected a tuple of ≥2 output variables as the final \
       expression, got:{indentExpr finalReduced}"
  let outNames ← comps.mapM fun c => do
    let c ← whnf c
    unless c.isFVar do
      throwError
        "reifyChainMulti: tuple output component is not a bound variable \
         (bind each output to a `let` first):{indentExpr c}"
    fvarDisplayName c.fvarId!
  -- Walk the bindings with the output slots known, so the bindings that
  -- write the outputs are not redeclared with an `RLetZero`.
  let acc ← reifyBindings bindings outNames.toList
  pure (acc, outNames.toList)

/-- The tower type a reified body gives to the argument slot named `x`: the
    `locSrc` of the first `.RCall` argument of that name, or `none` when no
    call takes an argument of that name.

    The constructors traversed are those the reifier emits (`RSkip`, `RSeq`,
    `RLetZero`, `RLetU64Zero`, `RScalarSet`, `RCall`); any other node gives
    `none`. -/
partial def bodySlotTowerType? (x : String) : LowCT → Option TowerType
  | .RCall _ _ args => (args.find? (·.locVar == x)).map (·.locSrc)
  | .RSeq a b       => (bodySlotTowerType? x a).orElse fun _ => bodySlotTowerType? x b
  | .RLetZero _ _ b => bodySlotTowerType? x b
  | .RLetU64Zero _ b => bodySlotTowerType? x b
  | _ => none

/-- The tower type of a reified function's parameter `x` whose Lean binder
    type is `bt`.

    `leanTypeToTowerType` answers `.TFp25519` for a Lean type it does not
    map, which is what an opaque surface type such as a curve scalar or point
    gives.  For such a parameter the body is the better witness: a leaf whose
    pattern declares per-argument types has already stamped the slot with the
    declared type, and that type is used.  A parameter whose binder type maps
    to a surface keeps that surface. -/
def paramTowerType (body : LowCT) (x : String) (bt : TowerType) : TowerType :=
  if bt == .TFp25519 then (bodySlotTowerType? x body).getD bt else bt

/-- Reify a Lean expression `e : Fp25519 → … → Fp25519` into a
    `ReifiedFunc`. Lambdas give the argument list, lets become RCalls,
    the body's final expression becomes the return.

    Argument tower types are inferred from the Lean-level binder type
    via `leanTypeToTowerType` (defined above `reifyChain`), and for a binder
    type outside that map from the reified body via `paramTowerType`. -/
partial def reifyFunc (e : Expr) : MetaM ReifiedFunc := do
  -- Unfold Lean `def` references, then enter lambdas (parameters) and
  -- lets (intermediate bindings) separately, so we know which is which.
  let e ← whnf e
  lambdaTelescope e fun params inner => do
    -- `params` are lambda-bound function arguments; look up each binder's
    -- type via its FVarId so heterogeneous signatures work.
    let argEntries ← params.mapM fun b => do
      let name ← fvarDisplayName b.fvarId!
      let decl ← b.fvarId!.getDecl
      pure (name, ← leanTypeToTowerType decl.type)
    -- Now enter the let-chain (if any) inside the lambda body.
    letTelescope inner fun letVars finalExpr => do
      let allBinders := params ++ letVars
      let (body, retName) ← reifyChain allBinders finalExpr
      pure
        { args := argEntries.toList.map (fun (n, t) => (n, paramTowerType body n t))
          body := body
          retName := retName
          outNames := [retName] }

/-- Multi-result variant of `reifyFunc`: reify a pure-Lean reference
    `e : T₀ → … → (Oᵢ × …)` returning a **tuple** into a `ReifiedFunc`
    whose `outNames` lists all output slots in order.  `retName` is pinned
    to the first output (the "primary" formal return slot the single-output
    emit paths use); `outNames` carries the full `&mut` ABI. -/
partial def reifyFuncMulti (e : Expr) : MetaM ReifiedFunc := do
  let e ← whnf e
  lambdaTelescope e fun params inner => do
    let argEntries ← params.mapM fun b => do
      let name ← fvarDisplayName b.fvarId!
      let decl ← b.fvarId!.getDecl
      pure (name, ← leanTypeToTowerType decl.type)
    letTelescope inner fun letVars finalExpr => do
      let allBinders := params ++ letVars
      let (body, outNames) ← reifyChainMulti allBinders finalExpr
      let retName := outNames.headD "__result"
      pure
        { args := argEntries.toList.map (fun (n, t) => (n, paramTowerType body n t))
          body := body
          retName := retName
          outNames := outNames }

/-! ## 5. `reifyLowCT%` elaborator -/

/-- Build a Lean term of type `ReifiedFunc` from a reified bundle.  All
    `ReifiedFunc` fields are simple data (`String` / `List` / `LowCT`), so
    each component round-trips through `toExpr`. -/
def reifiedFuncToExpr (rf : ReifiedFunc) : MetaM Expr := do
  let argsTerm : Expr ← mkListLit
    (← mkAppM ``Prod #[mkConst ``String, mkConst ``TowerType])
    (rf.args.map (fun (n, t) =>
      mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String)
        (mkConst ``TowerType) (mkStrLit n) (toExpr t)))
  let bodyTerm := toExpr rf.body
  let retTerm  := mkStrLit rf.retName
  let outNamesTerm : Expr ←
    mkListLit (mkConst ``String) (rf.outNames.map mkStrLit)
  mkAppOptM ``ReifiedFunc.mk
    #[some argsTerm, some bodyTerm, some retTerm, some outNamesTerm]

/-- `reifyLowCT% e` — elaborates `e`, reifies it into a `ReifiedFunc`
    at elaboration time, and returns a Lean term of type `ReifiedFunc`. -/
elab "reifyLowCT% " e:term : term => do
  let e' ← Term.elabTerm e none
  let e' ← instantiateMVars e'
  let rf ← reifyFunc e'
  reifiedFuncToExpr rf

/-- `reifyLowCTMulti% e` — like `reifyLowCT%`, but for a pure-Lean
    reference whose body returns a **tuple** of output slots.  The reified
    `ReifiedFunc.outNames` lists those slots in order; the body writes to
    each named slot (the `&mut` ABI the emit consumers expect). -/
elab "reifyLowCTMulti% " e:term : term => do
  let e' ← Term.elabTerm e none
  let e' ← instantiateMVars e'
  let rf ← reifyFuncMulti e'
  reifiedFuncToExpr rf


end            -- meta section

/-! ## 6. Smoke tests: X25519 halfstep authored in natural Lean -/

/-- A Montgomery halfstep authored as a **pure Lean function** over
    opaque `Fp25519`. The reifier will turn this into a `LowCT`. -/
noncomputable def halfstepLean (x2 z2 : Fp25519) : Fp25519 :=
  let A  := fp_add x2 z2
  let B  := fp_sub x2 z2
  let AA := fp_sqr A
  let BB := fp_sqr B
  fp_mul AA BB

/-- Reified form — a `ReifiedFunc` built by walking the Lean expression. -/
def halfstepReified : ReifiedFunc :=
  reifyLowCT% halfstepLean

-- Inspect reified form at elaboration time.
#eval halfstepReified.args.length  -- expect 2 (x2, z2)
#eval halfstepReified.args.map Prod.fst
#eval halfstepReified.retName


/-! ## 7. Full ladder step — four separate functions authored as natural Lean -/

/-- `fullstep_x2 = AA * BB`, no shared prelude (see CSE-trap memory
    entry: shared work across single-return funcs kills perf). -/
noncomputable def fullstepX2Lean (_x1 x2 z2 _x3 _z3 : Fp25519) : Fp25519 :=
  let A  := fp_add x2 z2
  let B  := fp_sub x2 z2
  let AA := fp_sqr A
  let BB := fp_sqr B
  fp_mul AA BB

/-- `fullstep_z2 = E * (BB + 121666·E)`. -/
noncomputable def fullstepZ2Lean (_x1 x2 z2 _x3 _z3 : Fp25519) : Fp25519 :=
  let A  := fp_add x2 z2
  let B  := fp_sub x2 z2
  let AA := fp_sqr A
  let BB := fp_sqr B
  let E  := fp_sub AA BB
  let a24E := fp_mul_a24 E
  let inn  := fp_add BB a24E
  fp_mul E inn

/-- `fullstep_x3 = (DA+CB)²`. -/
noncomputable def fullstepX3Lean (_x1 x2 z2 x3 z3 : Fp25519) : Fp25519 :=
  let A     := fp_add x2 z2
  let B     := fp_sub x2 z2
  let C     := fp_add x3 z3
  let D     := fp_sub x3 z3
  let DA    := fp_mul D A
  let CB    := fp_mul C B
  let DApCB := fp_add DA CB
  fp_sqr DApCB

/-- `fullstep_z3 = x1 * (DA-CB)²`. -/
noncomputable def fullstepZ3Lean (x1 x2 z2 x3 z3 : Fp25519) : Fp25519 :=
  let A      := fp_add x2 z2
  let B      := fp_sub x2 z2
  let C      := fp_add x3 z3
  let D      := fp_sub x3 z3
  let DA     := fp_mul D A
  let CB     := fp_mul C B
  let DAmCB  := fp_sub DA CB
  let DAmCB2 := fp_sqr DAmCB
  fp_mul x1 DAmCB2

/-- Reified forms of the four full-step outputs. -/
def fullstepX2Reified : ReifiedFunc := reifyLowCT% fullstepX2Lean
def fullstepZ2Reified : ReifiedFunc := reifyLowCT% fullstepZ2Lean
def fullstepX3Reified : ReifiedFunc := reifyLowCT% fullstepX3Lean
def fullstepZ3Reified : ReifiedFunc := reifyLowCT% fullstepZ3Lean

/-! ## 8. Ed25519 Edwards point addition (extended coords)

RFC 8032 §5.1.4, using extended projective coordinates (X:Y:Z:T) with
x=X/Z, y=Y/Z, xy=T/Z. Inputs are two points plus the precomputed
`2d = 2 * (-121665/121666 mod p)` Ed25519 curve constant.

```
A = (Y1-X1) * (Y2-X2)
B = (Y1+X1) * (Y2+X2)
C = T1 * 2d * T2
D = 2 * Z1 * Z2
E = B - A
F = D - C
G = D + C
H = B + A
X3 = E * F   Y3 = G * H   T3 = E * H   Z3 = F * G
```

9 muls, 8 adds/subs. The caller passes `2d` and `2·Z1` as already-
prepared inputs to avoid per-iteration constant multiplication.

Per the CSE-trap lesson, we emit four separate `func.func`s (one per
output coord) and inline only each output's dependencies. -/

noncomputable def edwards_add_X3
    (x1 y1 t1 z1 x2 y2 t2 z2 two_d : Fp25519) : Fp25519 :=
  let ymx1 := fp_sub y1 x1
  let ymx2 := fp_sub y2 x2
  let ypx1 := fp_add y1 x1
  let ypx2 := fp_add y2 x2
  let A    := fp_mul ymx1 ymx2
  let B    := fp_mul ypx1 ypx2
  let t12  := fp_mul t1 t2
  let C    := fp_mul t12 two_d
  let z12  := fp_mul z1 z2
  let D    := fp_add z12 z12     -- 2 * Z1 * Z2
  let E    := fp_sub B A
  let F    := fp_sub D C
  fp_mul E F

noncomputable def edwards_add_Y3
    (x1 y1 t1 z1 x2 y2 t2 z2 two_d : Fp25519) : Fp25519 :=
  let ymx1 := fp_sub y1 x1
  let ymx2 := fp_sub y2 x2
  let ypx1 := fp_add y1 x1
  let ypx2 := fp_add y2 x2
  let A    := fp_mul ymx1 ymx2
  let B    := fp_mul ypx1 ypx2
  let t12  := fp_mul t1 t2
  let C    := fp_mul t12 two_d
  let z12  := fp_mul z1 z2
  let D    := fp_add z12 z12
  let G    := fp_add D C
  let H    := fp_add B A
  fp_mul G H

noncomputable def edwards_add_T3
    (x1 y1 t1 z1 x2 y2 t2 z2 two_d : Fp25519) : Fp25519 :=
  let ymx1 := fp_sub y1 x1
  let ymx2 := fp_sub y2 x2
  let ypx1 := fp_add y1 x1
  let ypx2 := fp_add y2 x2
  let A    := fp_mul ymx1 ymx2
  let B    := fp_mul ypx1 ypx2
  let E    := fp_sub B A
  let H    := fp_add B A
  fp_mul E H

noncomputable def edwards_add_Z3
    (x1 y1 t1 z1 x2 y2 t2 z2 two_d : Fp25519) : Fp25519 :=
  let ymx1 := fp_sub y1 x1
  let ymx2 := fp_sub y2 x2
  let ypx1 := fp_add y1 x1
  let ypx2 := fp_add y2 x2
  let A    := fp_mul ymx1 ymx2
  let B    := fp_mul ypx1 ypx2
  let t12  := fp_mul t1 t2
  let C    := fp_mul t12 two_d
  let z12  := fp_mul z1 z2
  let D    := fp_add z12 z12
  let F    := fp_sub D C
  let G    := fp_add D C
  fp_mul F G

/-- Reified Ed25519 Edwards-add (extended coords), 4 outputs. -/
def edwardsAddX3Reified : ReifiedFunc := reifyLowCT% edwards_add_X3
def edwardsAddY3Reified : ReifiedFunc := reifyLowCT% edwards_add_Y3
def edwardsAddT3Reified : ReifiedFunc := reifyLowCT% edwards_add_T3
def edwardsAddZ3Reified : ReifiedFunc := reifyLowCT% edwards_add_Z3

/-! ## 9. Ed25519 Edwards doubling (extended coords)

Dalek-style formula (`a = -1` for Ed25519):
```
A = X²
B = Y²
C = 2·Z²
D = -A                       (we use fp_opp or express as B-A-B)
E = (X+Y)² - A - B
G = D + B   = B - A
F = G - C
H = D - B   = -A - B = -(A+B) = fp_opp (A+B)
X3 = E·F   Y3 = G·H   T3 = E·H   Z3 = F·G
```
4 squarings + 4 muls + 7 adds/subs + 1 fp_opp = 16 ops. Per CSE-trap
rule, each output func.func inlines only what it needs. -/

noncomputable def edwards_dbl_X3 (X Y Z _T : Fp25519) : Fp25519 :=
  let A    := fp_sqr X
  let B    := fp_sqr Y
  let ApB  := fp_add A B
  let XpY  := fp_add X Y
  let XpY2 := fp_sqr XpY
  let E    := fp_sub XpY2 ApB
  let BmA  := fp_sub B A
  let ZZ   := fp_sqr Z
  let C    := fp_add ZZ ZZ
  let F    := fp_sub BmA C
  fp_mul E F

noncomputable def edwards_dbl_Y3 (X Y Z _T : Fp25519) : Fp25519 :=
  let A   := fp_sqr X
  let B   := fp_sqr Y
  let ApB := fp_add A B
  let BmA := fp_sub B A
  let H   := fp_opp ApB
  fp_mul BmA H

noncomputable def edwards_dbl_T3 (X Y Z _T : Fp25519) : Fp25519 :=
  let A    := fp_sqr X
  let B    := fp_sqr Y
  let ApB  := fp_add A B
  let XpY  := fp_add X Y
  let XpY2 := fp_sqr XpY
  let E    := fp_sub XpY2 ApB
  let H    := fp_opp ApB
  fp_mul E H

noncomputable def edwards_dbl_Z3 (X Y Z _T : Fp25519) : Fp25519 :=
  let A   := fp_sqr X
  let B   := fp_sqr Y
  let BmA := fp_sub B A
  let ZZ  := fp_sqr Z
  let C   := fp_add ZZ ZZ
  let F   := fp_sub BmA C
  fp_mul F BmA

/-- Reified Ed25519 Edwards doubling (extended coords), 4 outputs. -/
def edwardsDblX3Reified : ReifiedFunc := reifyLowCT% edwards_dbl_X3
def edwardsDblY3Reified : ReifiedFunc := reifyLowCT% edwards_dbl_Y3
def edwardsDblT3Reified : ReifiedFunc := reifyLowCT% edwards_dbl_T3
def edwardsDblZ3Reified : ReifiedFunc := reifyLowCT% edwards_dbl_Z3

/-! ## 10. Ed25519 mixed add (projective + affine precomputed)

For sliding-window scalar multiplication we add the running accumulator
(extended-coords point `P1`) to a table entry in precomputed affine
"Niels" form `(y+x, y-x, 2·d·xy)`. Saves 3 Fp muls vs. full add.

Inputs:
- `(X1,Y1,T1,Z1)` — current accumulator, extended coords.
- `(ypxa, ymxa, xy2d)` — table entry in Niels form for a precomputed
  point `Pa`, with `ypxa = ya + xa`, `ymxa = ya - xa`,
  `xy2d = 2·d·xa·ya` (already in the field, no affine Z).

Output: extended coords `(X3,Y3,T3,Z3) = P1 + Pa`.

Formulae (RFC 8032 / dalek):
```
A = (Y1 - X1) · ymxa
B = (Y1 + X1) · ypxa
C = T1 · xy2d
D = 2·Z1
E = B - A
F = D - C
G = D + C
H = B + A
X3 = E·F   Y3 = G·H   T3 = E·H   Z3 = F·G
```
7 muls + 7 adds/subs per output (prior to CSE across output funcs). -/

noncomputable def edwards_madd_X3
    (X1 Y1 T1 Z1 ypxa ymxa xy2d : Fp25519) : Fp25519 :=
  let ymx1 := fp_sub Y1 X1
  let ypx1 := fp_add Y1 X1
  let A    := fp_mul ymx1 ymxa
  let B    := fp_mul ypx1 ypxa
  let C    := fp_mul T1 xy2d
  let D    := fp_add Z1 Z1
  let E    := fp_sub B A
  let F    := fp_sub D C
  fp_mul E F

noncomputable def edwards_madd_Y3
    (X1 Y1 T1 Z1 ypxa ymxa xy2d : Fp25519) : Fp25519 :=
  let ymx1 := fp_sub Y1 X1
  let ypx1 := fp_add Y1 X1
  let A    := fp_mul ymx1 ymxa
  let B    := fp_mul ypx1 ypxa
  let C    := fp_mul T1 xy2d
  let D    := fp_add Z1 Z1
  let G    := fp_add D C
  let H    := fp_add B A
  fp_mul G H

noncomputable def edwards_madd_T3
    (X1 Y1 T1 Z1 ypxa ymxa xy2d : Fp25519) : Fp25519 :=
  let ymx1 := fp_sub Y1 X1
  let ypx1 := fp_add Y1 X1
  let A    := fp_mul ymx1 ymxa
  let B    := fp_mul ypx1 ypxa
  let E    := fp_sub B A
  let H    := fp_add B A
  fp_mul E H

noncomputable def edwards_madd_Z3
    (X1 Y1 T1 Z1 ypxa ymxa xy2d : Fp25519) : Fp25519 :=
  let ymx1 := fp_sub Y1 X1
  let ypx1 := fp_add Y1 X1
  let A    := fp_mul ymx1 ymxa
  let B    := fp_mul ypx1 ypxa
  let C    := fp_mul T1 xy2d
  let D    := fp_add Z1 Z1
  let F    := fp_sub D C
  let G    := fp_add D C
  fp_mul F G

def edwardsMaddX3Reified : ReifiedFunc := reifyLowCT% edwards_madd_X3
def edwardsMaddY3Reified : ReifiedFunc := reifyLowCT% edwards_madd_Y3
def edwardsMaddT3Reified : ReifiedFunc := reifyLowCT% edwards_madd_T3
def edwardsMaddZ3Reified : ReifiedFunc := reifyLowCT% edwards_madd_Z3

/-! ## 11. Ed25519 point compression

RFC 8032 §5.1.2. Given `(X:Y:Z:T)` extended Edwards coords, produce the
32-byte encoding of `(x = X/Z, y = Y/Z)` with the sign bit of `x`
folded into the high bit of the last byte of `y`.

The leaf ops here produce Fp-typed limb vectors; byte-packing and the
high-bit OR happen in the C wrapper (outside the reifiable surface).
The compress function returns the affine `y` coordinate with its
sign-bit-adjusted form; the wrapper then serializes.

Steps:
```
recip = 1 / Z
x_aff = X · recip
y_aff = Y · recip
sign  = fp_is_neg x_aff           (low limb carries the bit)
out   = y_aff  XOR  sign<<255     (done in the C wrapper)
```
We expose two reifiable functions: `edwards_compress_y` (= y·(1/Z))
and `edwards_compress_sign` (= low-bit sign of x·(1/Z)). -/

noncomputable def edwards_compress_y (X Y Z _T : Fp25519) : Fp25519 :=
  let recip := fp_inv Z
  fp_mul Y recip

noncomputable def edwards_compress_sign (X Y Z _T : Fp25519) : Fp25519 :=
  let recip := fp_inv Z
  let x_aff := fp_mul X recip
  fp_is_neg x_aff

def edwardsCompressYReified    : ReifiedFunc := reifyLowCT% edwards_compress_y
def edwardsCompressSignReified : ReifiedFunc := reifyLowCT% edwards_compress_sign

/-! ## 12. Ed25519 point decompression

RFC 8032 §5.1.3. Given the 32-byte encoding (passed as an Fp25519
carrying `y` in the low bits and the sign of `x` in the high bit,
already split by the C wrapper into two Fp inputs `y` and `sign`),
recover `(X,Y,Z,T)` on the curve.

Algorithm:
```
u = y² - 1
v = d·y² + 1        (d = Ed25519 curve parameter, wrapper-provided via `d`)
x = fp_sqrt_ratio_i u v
-- Fix sign: x ← (x if sign(x) == sign_bit else -x)
negx  := fp_opp x
x'    := fp_cmov x negx sign
Z := 1  (represented by caller-supplied `one`)
T := x' · y
```
We reify three functions (`decompress_X`, `decompress_T`, and an
auxiliary `decompress_u` computing `y² - 1` for diagnostics). `Y` is
copied through from the input. `Z = 1` is supplied by the caller. -/

noncomputable def edwards_decompress_X
    (y sign d_const : Fp25519) : Fp25519 :=
  let yy   := fp_sqr y
  let one  := fp_is_zero yy        -- dummy to bind "one": caller passes 1-limb
  let u    := fp_sub yy one
  let dyy  := fp_mul d_const yy
  let v    := fp_add dyy one
  let x    := fp_sqrt_ratio_i u v
  let negx := fp_opp x
  fp_cmov x negx sign

noncomputable def edwards_decompress_T
    (y sign d_const : Fp25519) : Fp25519 :=
  let yy   := fp_sqr y
  let one  := fp_is_zero yy
  let u    := fp_sub yy one
  let dyy  := fp_mul d_const yy
  let v    := fp_add dyy one
  let x    := fp_sqrt_ratio_i u v
  let negx := fp_opp x
  let xs   := fp_cmov x negx sign
  fp_mul xs y

def edwardsDecompressXReified : ReifiedFunc := reifyLowCT% edwards_decompress_X
def edwardsDecompressTReified : ReifiedFunc := reifyLowCT% edwards_decompress_T

/-! ## 13. Ed25519 scalar reduction / multiplication pieces

`scalar_reduce_64` maps a 64-byte uniform string (as two 32-byte halves
packed into two FpL25519 values — low and high) to a scalar mod L. The
fiat-crypto shim does the full Barrett-style reduction; we expose it
here so the signing-flow reifier can chain it with `scalar_mul` /
`scalar_add`.

For the scalar side `s = (r + h · a) mod L`:
```
ha := scalar_mul h a
s  := scalar_add r ha
```
Both reified-friendly as pure FpL25519 let-chains. -/

noncomputable def ed25519_scalar_s (r a h : FpL25519) : FpL25519 :=
  let ha := scalar_mul h a
  scalar_add r ha

def ed25519ScalarSReified : ReifiedFunc := reifyLowCT% ed25519_scalar_s

/-! ## 14. Ristretto255 compress / decompress

RFC (draft-irtf-cfrg-ristretto255) point compression.

Compress: given Edwards extended coords `(X,Y,Z,T)` on Ed25519 and the two
Ristretto-specific constants `SQRT_M1` = √−1 mod p and
`INVSQRT_A_MINUS_D` = 1/√(−1 − d), compute the canonical 32-byte "s" value
for the input equivalence class. Straight-line, ~25 fp ops.

Decompress: given `s` (validated: canonical, non-negative), the curve
constant `d`, and `one` = 1, recover `(X, Y, T)` with `Z = 1` supplied by
the caller. Three reified outputs (the `Z` coord is a constant, so not
emitted through MLIR). -/

noncomputable def ristretto_compress_s
    (X Y Z T sqrt_m1 invsqrt_a_minus_d one : Fp25519) : Fp25519 :=
  let ZpY       := fp_add Z Y
  let ZmY       := fp_sub Z Y
  let u1        := fp_mul ZpY ZmY
  let u2        := fp_mul X Y
  let u2_sq     := fp_sqr u2
  let u1_u2_sq  := fp_mul u1 u2_sq
  let invsqrt_v := fp_sqrt_ratio_i one u1_u2_sq
  let i1        := fp_mul invsqrt_v u1
  let i2        := fp_mul invsqrt_v u2
  let i2_T      := fp_mul i2 T
  let z_inv     := fp_mul i1 i2_T
  let iX        := fp_mul X sqrt_m1
  let iY        := fp_mul Y sqrt_m1
  let enchanted := fp_mul i1 invsqrt_a_minus_d
  let T_zinv    := fp_mul T z_inv
  let rot       := fp_is_neg T_zinv
  let X'        := fp_cmov X iY rot
  let Y'        := fp_cmov Y iX rot
  let den_inv'  := fp_cmov i2 enchanted rot
  let X'_zinv   := fp_mul X' z_inv
  let xn        := fp_is_neg X'_zinv
  let Y'_neg    := fp_opp Y'
  let Y''       := fp_cmov Y' Y'_neg xn
  let ZmY''     := fp_sub Z Y''
  let s_raw     := fp_mul den_inv' ZmY''
  let s_neg_fl  := fp_is_neg s_raw
  let s_neg     := fp_opp s_raw
  fp_cmov s_raw s_neg s_neg_fl

def ristrettoCompressSReified : ReifiedFunc :=
  reifyLowCT% ristretto_compress_s

/-! ### Ristretto decompress outputs (X, Y, T); caller supplies Z = 1.

Formulae (transcribed from `curve25519-dalek/src/ristretto.rs`):
```
ss  = s²
u1  = 1 - ss
u2  = 1 + ss
v   = -(d · u1² + u2²)
I   = sqrt_ratio_i(1, v · u2²)
Dx  = I · u2
Dy  = I · Dx · v
x   = |2s · Dx|      (canonicalize to non-negative)
y   = u1 · Dy
t   = x · y
```
The caller checks `!is_negative(t) && !is_zero(y)` before accepting. -/

noncomputable def ristretto_decompress_X
    (s d_const one : Fp25519) : Fp25519 :=
  let ss      := fp_sqr s
  let u1      := fp_sub one ss
  let u2      := fp_add one ss
  let u1_sq   := fp_sqr u1
  let u2_sq   := fp_sqr u2
  let du1     := fp_mul d_const u1_sq
  let sum     := fp_add du1 u2_sq
  let v       := fp_opp sum
  let v_u2sq  := fp_mul v u2_sq
  let Iv      := fp_sqrt_ratio_i one v_u2sq
  let Dx      := fp_mul Iv u2
  let twos    := fp_add s s
  let x_raw   := fp_mul twos Dx
  let x_neg   := fp_is_neg x_raw
  let x_opp   := fp_opp x_raw
  fp_cmov x_raw x_opp x_neg

noncomputable def ristretto_decompress_Y
    (s d_const one : Fp25519) : Fp25519 :=
  let ss      := fp_sqr s
  let u1      := fp_sub one ss
  let u2      := fp_add one ss
  let u1_sq   := fp_sqr u1
  let u2_sq   := fp_sqr u2
  let du1     := fp_mul d_const u1_sq
  let sum     := fp_add du1 u2_sq
  let v       := fp_opp sum
  let v_u2sq  := fp_mul v u2_sq
  let Iv      := fp_sqrt_ratio_i one v_u2sq
  let Dx      := fp_mul Iv u2
  let IvDx    := fp_mul Iv Dx
  let Dy      := fp_mul IvDx v
  fp_mul u1 Dy

noncomputable def ristretto_decompress_T
    (s d_const one : Fp25519) : Fp25519 :=
  let ss      := fp_sqr s
  let u1      := fp_sub one ss
  let u2      := fp_add one ss
  let u1_sq   := fp_sqr u1
  let u2_sq   := fp_sqr u2
  let du1     := fp_mul d_const u1_sq
  let sum     := fp_add du1 u2_sq
  let v       := fp_opp sum
  let v_u2sq  := fp_mul v u2_sq
  let Iv      := fp_sqrt_ratio_i one v_u2sq
  let Dx      := fp_mul Iv u2
  let twos    := fp_add s s
  let x_raw   := fp_mul twos Dx
  let x_neg   := fp_is_neg x_raw
  let x_opp   := fp_opp x_raw
  let x       := fp_cmov x_raw x_opp x_neg
  let IvDx    := fp_mul Iv Dx
  let Dy      := fp_mul IvDx v
  let y       := fp_mul u1 Dy
  fp_mul x y

def ristrettoDecompressXReified : ReifiedFunc := reifyLowCT% ristretto_decompress_X
def ristrettoDecompressYReified : ReifiedFunc := reifyLowCT% ristretto_decompress_Y
def ristrettoDecompressTReified : ReifiedFunc := reifyLowCT% ristretto_decompress_T

/-! ## ML-KEM: NTT poly-multiply authored in natural Lean

The lattice analogue of `halfstepLean` — the negacyclic poly product
`a ·  b = invntt(basemul(ntt a, ntt b))` over `Z_3329[X]/(X^256+1)`, written as a
pure Lean function over the opaque `MlPoly` surface, lifted to `LowCT` by the
same verified `reifyLowCT%`. This is the ML-KEM core arithmetic op entering the
Lean → LowCT → `Com catCryptDialect` → Jasmin pipeline, like the X25519 field step. -/
noncomputable def polyMulLean (a b : MlPoly) : MlPoly :=
  let ah := mlk_ntt a
  let bh := mlk_ntt b
  let ch := mlk_basemul ah bh
  mlk_invntt ch

def polyMulReified : ReifiedFunc := reifyLowCT% polyMulLean

/-! ### ML-KEM matrix-vector product (keygen/encaps core)

`t = invntt(Â ∘ ntt(s))` over the `k=3` polyvec/polymat tower — the heart of
ML-KEM-768 key generation (`t̂ = Â ∘ ŝ`). Written as natural Lean over the
opaque `MlVec`/`MlMat` surface; reified to a `LowCT` whose leaves are the
polyvec NTT + matrix-vector-accumulate primitives. This is the vector-level
analogue of `polyMulLean`, exercising the `TPolyVec`/`TPolyMat`
encodings (`memref 192` / `memref 576`) through the verified front. -/
noncomputable def matvecLean (A : MlMat) (s : MlVec) : MlVec :=
  let sh := pv_ntt s
  let th := mlk_matvec A sh
  pv_invntt th

def matvecReified : ReifiedFunc := reifyLowCT% matvecLean

/-! ### ML-KEM-768 key generation (indcpa core)

The full keygen lattice pipeline written in natural Lean over the byte+poly+matrix
surface, composing the hash/CBD/encode leaves (lowerable through the verified
front via its `TBytes` support) with the matrix-vector core:

  Â = gen_matrix(ρ);  s,e = cbd(σ);  t̂ = Â∘ntt(s) + ntt(e);  pk = encode(t̂).

Structurally faithful to formosa's `__indcpa_keypair` (so its own keygen is a valid
KAT oracle, sidestepping the FIPS-203-vs-Kyber-r3 version gap):

    ρ‖σ = G(d);  Â = gen_matrix(ρ);  s = CBD(σ,0..2);  e = CBD(σ,3..5);
    t̂ = frommont(Â ∘ ntt(s)) + ntt(e);  pk = ByteEncode(reduce(t̂)).

`s`/`e` use distinct PRF nonces; the matvec includes the per-row `_poly_frommont`
and the result stays NTT-domain (no invntt), matching formosa exactly. -/
noncomputable def keygenLean (d : MlSeed) : MlEncVec :=
  let rs   := mlk_hash_g d
  let aMat := mlk_gen_matrix rs
  let s    := mlk_cbd_s rs
  let e    := mlk_cbd_e rs
  let sh   := pv_ntt s
  let eh   := pv_ntt e
  let th   := mlk_matvec_mont aMat sh
  let tt   := pv_add th eh
  let tr   := mlk_pv_reduce tt
  mlk_encode_vec tr

def keygenReified : ReifiedFunc := reifyLowCT% keygenLean

/-- Keygen up to (and excluding) the ByteEncode: returns the NTT-domain `t̂`
    polyvec. Used for the KAT (compare `t̂` against formosa's pk decoded back to a
    polyvec, sidestepping `__polyvec_tobytes`'s raw-memory-pointer ABI). The
    encode is a separate, leaf-internal byte-packing. -/
noncomputable def keygenThatLean (d : MlSeed) : MlVec :=
  let rs   := mlk_hash_g d
  let aMat := mlk_gen_matrix rs
  let s    := mlk_cbd_s rs
  let e    := mlk_cbd_e rs
  let sh   := pv_ntt s
  let eh   := pv_ntt e
  let th   := mlk_matvec_mont aMat sh
  let tt   := pv_add th eh
  mlk_pv_reduce tt

def keygenThatReified : ReifiedFunc := reifyLowCT% keygenThatLean

/-! ### ML-KEM-768 encaps (K-PKE.Encrypt core), faithful to formosa `__indcpa_enc`

  Âᵀ = gen_matrix(ρ,1);  k = Decompress₁(m);
  r = CBD(coins,0..2);  e1 = CBD(coins,3..5);  e2 = CBD(coins,6);  r̂ = ntt(r);
  u = invntt(Âᵀ∘r̂) + e1;  v = invntt(t̂ᵀ∘r̂) + e2 + k;
  c = Compress_du(reduce u) ‖ Compress_dv(reduce v). -/
noncomputable def encapsLean (pk : MlPubKey) (msg : MlMsg) (coins : MlSeed) : MlCipher :=
  let tHat := mlk_pk_decode pk
  let aat  := mlk_gen_matrix_T pk
  let k    := mlk_frommsg msg
  let r    := mlk_cbd_enc_r coins
  let e1   := mlk_cbd_enc_e1 coins
  let e2   := mlk_cbd_enc_e2 coins
  let rHat := pv_ntt r
  let ar   := mlk_matvec_invntt aat rHat
  let u    := pv_add ar e1
  let v0   := mlk_polyvec_dot tHat rHat
  let v1   := mlk_poly_add v0 e2
  let v    := mlk_poly_add v1 k
  let u2   := mlk_pv_reduce u
  let v2   := mlk_poly_reduce v
  mlk_compress_cipher u2 v2

def encapsReified : ReifiedFunc := reifyLowCT% encapsLean

/-! ### ML-KEM-768 decaps (K-PKE.Decrypt core), faithful to formosa `__indcpa_dec`

  u = Decompress_du(c1);  v = Decompress_dv(c2);  ŝ = ByteDecode(sk);
  m = Compress₁( reduce( v − invntt(ŝᵀ ∘ ntt(u)) ) ). -/
noncomputable def decapsLean (c : MlCipher) (sk : MlEncVec) : MlMsg :=
  let u    := mlk_decompress_u c
  let v    := mlk_decompress_v c
  let sHat := mlk_sk_decode sk
  let uHat := pv_ntt u
  let t    := mlk_polyvec_dot sHat uHat
  let mp   := mlk_poly_sub v t
  let mp2  := mlk_poly_reduce mp
  mlk_tomsg mp2

def decapsReified : ReifiedFunc := reifyLowCT% decapsLean

/-- Decaps **arithmetic core** for the KAT: takes the already-decompressed `u`,`v`
    and decoded `ŝ` (byte (de)serialization done in the C harness, matching
    formosa), emits `m = tomsg(reduce(v − invntt(ŝᵀ ∘ ntt u)))`. No SHAKE, so no
    keccak register pressure. -/
noncomputable def decapsArithLean (u : MlVec) (v : MlPoly) (sHat : MlVec) : MlMsg :=
  let uHat := pv_ntt u
  let t    := mlk_polyvec_dot sHat uHat
  let mp   := mlk_poly_sub v t
  let mp2  := mlk_poly_reduce mp
  mlk_tomsg mp2

def decapsArithReified : ReifiedFunc := reifyLowCT% decapsArithLean

/-- Encaps **arithmetic core** for the KAT: takes the decoded `t̂` and the bare
    seeds (ρ for the matrix, `coins` for the noise), emits the pre-compress
    `u‖v`. The C harness does the pk/sk decode + ciphertext compress (matching
    formosa). SHAKE-bearing (gen_matrix + CBD), like keygen. -/
noncomputable def encapsArithLean (tHat : MlVec) (rho : MlSeed) (msg : MlMsg)
    (coins : MlSeed) : MlUV :=
  let aat  := mlk_gen_matrix_T_rho rho
  let k    := mlk_frommsg msg
  let r    := mlk_cbd_enc_r coins
  let e1   := mlk_cbd_enc_e1 coins
  let e2   := mlk_cbd_enc_e2 coins
  let rHat := pv_ntt r
  let ar   := mlk_matvec_invntt aat rHat
  let u    := pv_add ar e1
  let v0   := mlk_polyvec_dot tHat rHat
  let v1   := mlk_poly_add v0 e2
  let v    := mlk_poly_add v1 k
  let u2   := mlk_pv_reduce u
  let v2   := mlk_poly_reduce v
  mlk_uv_concat u2 v2

def encapsArithReified : ReifiedFunc := reifyLowCT% encapsArithLean

/-! ### ML-KEM-768 full KEM via the Fujisaki–Okamoto transform.

These compose the INDCPA cores (`encapsLean` / `decapsLean` bodies, inlined) with
the FO hashing/verify/select, faithful to formosa `__crypto_kem_enc_jazz` /
`__crypto_kem_dec_jazz`. Encaps' INDCPA randomness `r` is **derived** (`r=kr[32:64]`,
not a free `coins` input), so the INDCPA `encapsLean` body is inlined here with
`coins := r`. The two outputs (K, ct) are bundled into `K‖ct` (`MlKemEnc`, 1120
bytes) for the single-output ABI; the C harness splits them. -/

/-- FO encapsulation `(K, ct) = Encaps(pk, m)`:
      H = SHA3-256(pk);  kr = SHA3-512(m‖H);  r = kr[32:64];
      ct = INDCPA_enc(m, pk, r);  K = kr[0:32].  Output: `K‖ct`. -/
noncomputable def encapsKemLean (pk : MlPubKey) (msg : MlMsg) : MlKemEnc :=
  -- FO: derive (K, r) from (pk, m)
  let h    := mlk_hash_h pk
  let kr   := mlk_hash_g_kem msg h
  let kk   := mlk_kr_k kr
  let r    := mlk_kr_r kr
  -- INDCPA_enc(m, pk, r)  (== encapsLean body with coins := r)
  let tHat := mlk_pk_decode pk
  let k    := mlk_frommsg msg
  let nz   := mlk_cbd_enc_all r            -- batched noise: 2 4-way perms
  let rv   := mlk_noise_r nz
  let e1   := mlk_noise_e1 nz
  let e2   := mlk_noise_e2 nz
  let rHat := pv_ntt rv
  let ar   := mlk_gen_matvec pk rHat       -- fused gen_matrix + matvec (no 2304 copy)
  let u    := pv_add ar e1
  let v2   := mlk_v_acc tHat rHat e2 k     -- fused dot + e2 + k + reduce
  let u2   := mlk_pv_reduce u
  let ct   := mlk_compress_cipher u2 v2
  mlk_kem_pack kk ct

def encapsKemReified : ReifiedFunc := reifyLowCT% encapsKemLean

/-- FO decapsulation `K = Decaps(ct, sk)` with implicit rejection:
      m' = INDCPA_dec(ct, sk_pke);  H = sk.H;  kr = SHA3-512(m'‖H);
      ctpc = INDCPA_enc(m', pk, r=kr[32:64]);  cnd = verify(ct, ctpc);
      Kbar = SHAKE256(z‖ct);  K = cnd ? kr[0:32] : Kbar. -/
noncomputable def decapsKemLean (c : MlCipher) (sk : MlSecKeyFull) : MlSharedSecret :=
  -- INDCPA_dec(ct, sk_pke)  (== decapsLean body)
  let skPke := mlk_sk_pke sk
  let u     := mlk_decompress_u c
  let v     := mlk_decompress_v c
  let sHat  := mlk_sk_decode skPke
  let uHat  := pv_ntt u
  let mp    := mlk_decrypt sHat uHat v      -- fused dot + sub + reduce + tomsg
  -- FO: re-derive (K', r) from (m', H)
  let hh    := mlk_sk_h sk
  let kr    := mlk_hash_g_kem mp hh
  let kk    := mlk_kr_k kr
  let r     := mlk_kr_r kr
  -- INDCPA_enc(m', pk, r)  (== encapsLean body with pk := sk.pk, coins := r)
  let pk    := mlk_sk_pk sk
  let tHat  := mlk_pk_decode pk
  let kpoly := mlk_frommsg mp
  let nz    := mlk_cbd_enc_all r           -- batched noise: 2 4-way perms
  let rv    := mlk_noise_r nz
  let e1    := mlk_noise_e1 nz
  let e2    := mlk_noise_e2 nz
  let rHat  := pv_ntt rv
  let ar    := mlk_gen_matvec pk rHat      -- fused gen_matrix + matvec (no 2304 copy)
  let uu    := pv_add ar e1
  let vv2   := mlk_v_acc tHat rHat e2 kpoly  -- fused dot + e2 + k + reduce
  let uu2   := mlk_pv_reduce uu
  let ctpc  := mlk_compress_cipher uu2 vv2
  -- verify + implicit-rejection select
  let cnd   := mlk_verify c ctpc
  let kbar  := mlk_hash_j sk c
  mlk_select cnd kk kbar

def decapsKemReified : ReifiedFunc := reifyLowCT% decapsKemLean

/-! ## ML-DSA (Dilithium): NTT poly-multiply authored in natural Lean

The lattice-signature analogue of `polyMulLean`: the negacyclic poly product
`a · b = invntt(pointwise(ntt a, ntt b))` over `Z_8380417[X]/(X^256+1)`, written
as a pure Lean function over the opaque `MldsaPoly` surface, lifted to `LowCT`
by the SAME `reifyLowCT%`. The leaves are the libjade dilithium NTT primitives
(`ntt_avx2` / `poly_pointwise_montgomery` / `invntt_tomont_avx2`, all
`reg ptr u32[256]`); the Montgomery factors of the three leaves cancel over the
round trip (see the `MldsaPoly` surface docstring), so this computes the
normal-domain product mod `q`. -/
noncomputable def mldsaPolyMulLean (a b : MldsaPoly) : MldsaPoly :=
  let ah := mld_ntt a
  let bh := mld_ntt b
  let ch := mld_pointwise ah bh
  mld_invntt ch

def mldsaPolyMulReified : ReifiedFunc := reifyLowCT% mldsaPolyMulLean

/-! ## ML-DSA (Dilithium): polyvec dot-product authored in natural Lean

The inner product at the heart of ML-DSA's matrix-vector product `Â·ŝ` (keygen
`t = As`, sign `w = Ay`): one row of the product is

  `t = invntt( Σ_{j=0}^{l-1} pointwise(Â_j, ŝ_j) )`

with `l = 5` for ML-DSA-65.  Dilithium has no single polyvec-accumulate leaf
(unlike formosa-mlkem's `__polyvec_pointwise_acc`), so we COMPOSE the dot from
the per-poly leaves already wired for `mldsaPolyMulLean`: forward-NTT the 10
normal-domain inputs (5 matrix polys `a0..a4`, 5 secret polys `s0..s4`), form the
per-`j` pointwise products in NTT domain, accumulate them with `mld_poly_add`,
then a single `mld_invntt` (`invntt_tomont`, ×R) brings the accumulator back to
normal domain — the per-term `pointwise` (×R⁻¹) cancels the `invntt`'s R exactly
as in `mldsaPolyMulLean`, so the result is the normal-domain Σ_j (a_j·s_j) mod q.

The two operands (the matrix row `Â` and the secret vector `ŝ`) are passed as
two BUNDLED `MldsaPolyVecL` buffers — `out + 2` pointers, fitting the x86-64
export ABI — and `slice@{j·256}`-d into their 5 component polys inside the body,
exactly the register-ABI-saving bundling ML-KEM's `polyvec_dot3` uses for `k=3`.
This keeps the per-poly leaf composition (dilithium has no polyvec-accumulate
leaf) while staying within 6 GP registers. -/
noncomputable def mldsaDotLean (av sv : MldsaPolyVecL) : MldsaPoly :=
  let a0 := mld_vl_get0 av
  let a1 := mld_vl_get1 av
  let a2 := mld_vl_get2 av
  let a3 := mld_vl_get3 av
  let a4 := mld_vl_get4 av
  let s0 := mld_vl_get0 sv
  let s1 := mld_vl_get1 sv
  let s2 := mld_vl_get2 sv
  let s3 := mld_vl_get3 sv
  let s4 := mld_vl_get4 sv
  let a0h := mld_ntt a0
  let a1h := mld_ntt a1
  let a2h := mld_ntt a2
  let a3h := mld_ntt a3
  let a4h := mld_ntt a4
  let s0h := mld_ntt s0
  let s1h := mld_ntt s1
  let s2h := mld_ntt s2
  let s3h := mld_ntt s3
  let s4h := mld_ntt s4
  let p0  := mld_pointwise a0h s0h
  let p1  := mld_pointwise a1h s1h
  let p2  := mld_pointwise a2h s2h
  let p3  := mld_pointwise a3h s3h
  let p4  := mld_pointwise a4h s4h
  let acc1 := mld_poly_add p0 p1
  let acc2 := mld_poly_add acc1 p2
  let acc3 := mld_poly_add acc2 p3
  let acc4 := mld_poly_add acc3 p4
  mld_invntt acc4

def mldsaDotReified : ReifiedFunc := reifyLowCT% mldsaDotLean

/-! ## Multi-result reflection probe (tuple output)

A minimal 2-output reference returning `(polyvec_add a b, polyvec_dot a b)`,
to validate that `reifyLowCTMulti%` recovers the two named output slots
and emits a `borrowOk` body before the real multi-output kernels migrate.
Each output is bound to a `let` first (so it is a named slot the body
writes), matching the `&mut`-slot ABI the emit consumers read. -/
noncomputable def probeTwoOutLean (a b : MlVec) : MlVec × MlPoly :=
  let p := mlk_polyvec_add_c a b
  let q := mlk_polyvec_dot_c a b
  (p, q)

def probeTwoOutReified : ReifiedFunc := reifyLowCTMulti% probeTwoOutLean

#eval probeTwoOutReified.outNames                     -- [p, q]
#eval probeTwoOutReified.args.map Prod.fst            -- [a, b]

-- The two outputs are recovered, in order.
example : probeTwoOutReified.outNames = ["p", "q"] := by native_decide
-- The body assigns both output slots (`borrowOk` is checked downstream
-- in `MlkemLowCT.lean`, which imports the borrow checker).
example : probeTwoOutReified.args.map Prod.fst = ["a", "b"] := by native_decide

end CatCrypt.Crypto.Jasmin.LowCTReflect
