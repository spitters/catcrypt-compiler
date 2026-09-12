/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import HaxLean.ImpType
public meta import CatCrypt.Crypto.Jasmin.LowCT
public import CatCrypt.Crypto.Jasmin.LowCT
public meta import HaxLean.AST
public import HaxLean.AST
public import HaxLean.ImpType

/-!
# H1: LowCT Subset Filter for hax `ImpExpr`

This file implements **Track H1** from `BLS/NEXT.md`: a decidable predicate on
hax's existing imperative AST (`CatCrypt.Hax.ImpExpr` / `ImpType`) that decides
whether a given Rust function lies in the **tower-typed subset** representable
by `CatCrypt.Crypto.Jasmin.LowCT.LowCT`.

## Why a subset filter?

`LowCT` is a typed DSL over the BLS / Curve25519 / P-256 tower hierarchy
(`TFp`, `TFp2`, `TFp6`, `TFp12`, `TU64`, `TFp25519`, `TFpL25519`, `TFpP256`)
plus `u64` scalars; its borrow checker (`LowCTBorrowCheck.borrowOk`)
certifies memory safety statically.  hax, by contrast, can in principle emit
references, ADTs, `Result`, generic ADT projections, and arbitrary control
flow — none of which the verified `LowCT → MLIR → LLVM` pipeline accepts.

`LowCTRepresentable` is therefore a *gate*: a hax function passes only if
its `ImpExpr` body and `ImpType` annotations live in the cryptographic
fragment that the H2 translation pass will be able to lower into `LowCT`.

## Design choices

* **Reuse** the existing `CatCrypt.Hax.ImpExpr` AST rather than stub a
  fresh one — the codebase already has a Lean-side hax integration with
  semantics and phase passes (`CatCrypt/Hax/`).  Stubbing a parallel
  `Hax.RawCode` would duplicate work and diverge from what hax actually
  emits.
* **Tower marker via leaf-call whitelist + tower-typed ADT names.**  The
  hax AST does not (yet) carry a `TowerType` annotation directly; we
  instead recognise tower types by ADT name (e.g. `"Fp"`, `"Fp2"`,
  `"Scalar25519"`) using the same name list that downstream `HaxTypes`
  bridges already use, and we recognise tower-aware leaf calls by a
  whitelist (`fp_add`, `fp_mul`, `fp2_mul`, `scalar25519_add`, …).
* **Decidable `Bool` predicate** — uses `decide` / `native_decide` on
  smoke tests.

This file is **load-bearing for the H-track plan only**; nothing here is
imported by the verified `LowCT → MLIR` pipeline.  The follow-up
sessions H2/H3/H4 will lower an `ImpExpr` that passes this filter into a
concrete `LowCT`.

## Outline

1. `TowerOfImpType` — partial map `ImpType → Option TowerType`.
2. `binopWhitelist` / `callWhitelist` — CT-safe operations & functions.
3. `LowCTRepresentable.{Type,Expr,Stmt}` — the `Bool` filter.
4. `LowCTRepresentable.reason` — diagnostic version returning `Option String`.
5. Smoke tests (`decide`-checked).
6. Documented follow-ups (H2 / H3 / H4).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open _root_.Hax (ImpExpr ImpLit ImpType IntWidth)
open CatCrypt.Crypto.Jasmin.LowCT (TowerType)

/-! ## §1  Mapping `ImpType` → `TowerType`

The hax `ImpType` universe is open; the `LowCT` tower is closed.  Tower
elements appear in hax extraction as user-defined ADTs (`struct Fp([u64; 6])`
etc.), so we recognise them by **ADT name**.  This table mirrors the names
already used by downstream `*Bridges/HaxTypes.lean` files.
-/

/-- Decide whether a hax ADT name corresponds to a `TowerType`.

    Only the constructors currently exposed by `TowerType` in
    `Crypto/Jasmin/LowCT.lean` are mapped: `TFp`, `TFp2`, `TFp6`,
    `TFp12`, `TU64`. The `Fp25519` / `FpL25519` / `Scalar25519` / `FpP256`
    ADT names are returned as `none` here — they correspond to
    curve-specific TowerType extensions that have been factored out of
    the base inductive. When the broader `TowerType` is restored (or
    a curve-specific subtype is introduced), extend this table. -/
def towerOfAdtName : String → Option TowerType
  | "Fp"          => some .TFp
  | "Fp2"         => some .TFp2
  | "Fp6"         => some .TFp6
  | "Fp12"        => some .TFp12
  | "Fp25519"     => some .TFp25519
  | "Fp25519_64"  => some .TFp25519_64
  | _             => none

/-- Best-effort partial map `ImpType → TowerType`.  Returns `none` for
    types that are not tower-shaped (e.g. `Fp2`, `[u8; 32]`, `Option<T>`). -/
def towerOfImpType : ImpType → Option TowerType
  | .uint .w64                      => some .TU64
  | .adt name _                     => towerOfAdtName name
  | _                               => none

/-! ## §2  Whitelists -/

/-- Constant-time-safe binary operators.  Strings here mirror hax's
    operator naming (`"+"`, `"BitAnd"`, ...).  Comparison operators (`"<"`,
    `"=="`, …) are **not** included: they are control-dependent on secret
    inputs and require dedicated CT-safe leaf calls in `LowCT`. -/
def binopWhitelist : List String :=
  ["+", "-", "*", "^", "&", "|", "<<", ">>",
   "BitAnd", "BitOr", "BitXor", "Shl", "Shr",
   "Add", "Sub", "Mul"]

/-- Whitelist of leaf-call names that the `LowCT → MLIR` pipeline knows
    how to lower into `RCall` / `RCloneCall`.

    Categories:
    * `fp_*`, `fp2_*`, `fp6_*`, `fp12_*` — BLS12 tower arithmetic.
    * `fp25519_*`, `scalar25519_*` — Curve25519 (used by Ed25519 / X25519).
    * `fpP256_*` — NIST P-256.
    * `u64_*` — scalar u64 helpers (`u64_zero`, `u64_set_one`, …). -/
def callWhitelist : List String :=
  -- BLS12 base field
  ["fp_add", "fp_sub", "fp_mul", "fp_neg", "fp_inv", "fp_square", "fp_set_zero",
   "fp_set_one", "fp_copy",
   -- BLS12 quadratic / sextic / dodecic extensions
   "fp2_add", "fp2_sub", "fp2_mul", "fp2_neg", "fp2_square", "fp2_inv",
   "fp6_add", "fp6_mul", "fp6_square", "fp6_inv",
   "fp12_add", "fp12_mul", "fp12_square", "fp12_inv", "fp12_conj",
   -- Curve25519 base field & scalar
   "fp25519_add", "fp25519_sub", "fp25519_mul", "fp25519_square", "fp25519_inv",
   "scalar25519_add", "scalar25519_sub", "scalar25519_mul", "scalar25519_neg",
   -- P-256
   "fpP256_add", "fpP256_sub", "fpP256_mul", "fpP256_square", "fpP256_inv",
   -- u64 scalar helpers
   "u64_zero", "u64_set", "u64_add", "u64_sub", "u64_mul"]

/-! ## §3  Representability predicate (`Bool`) -/

/-- Are *all* components of a tuple type representable? -/
partial def LowCTRepresentable.Type : ImpType → Bool
  | .bool             => true
  | .unit             => true
  | .uint _           => true   -- any uX maps to TU64 (downcasts checked at H2)
  | .sint _           => false  -- LowCT is unsigned-only
  | .int              => false  -- ambiguous width
  | .str              => false
  | .tuple ts         => ts.all LowCTRepresentable.Type
  | .array elem _     => LowCTRepresentable.Type elem
  | .option _         => false  -- no `Option` in LowCT
  | .result _ _       => false  -- no `Result` in LowCT
  | .adt name _       => (towerOfAdtName name).isSome
  | .ref _ _          => false  -- references must be eliminated by Phase 1
  | .slice _          => false
  | .controlFlow _ _  => false
  | .fn _ _           => false  -- first-class fns not in LowCT
  | .typeVar _        => false
  | .unknown          => false

/-- Is a literal expressible as a `LowCT` constant?  We accept booleans,
    integers (which lower to `RScalarSet`/`RLimbStore`), and unit. -/
def LowCTRepresentable.Lit : ImpLit → Bool
  | .bool _       => true
  | .int _        => true
  | .unit         => true
  | .uintLit _ _  => true
  | .sintLit _ _  => false  -- signed not in LowCT

/-- Representable expressions.  Every reachable `ImpExpr` must belong to
    the tower-typed fragment. -/
partial def LowCTRepresentable.Expr : ImpExpr → Bool
  | .lit l                 => LowCTRepresentable.Lit l
  | .var _                 => true
  | .letBind _ v b         => LowCTRepresentable.Expr v && LowCTRepresentable.Expr b
  | .lam _ _               => false  -- first-class closures not in LowCT
  | .app f args            => callWhitelist.contains f && args.all LowCTRepresentable.Expr
  | .tuple es              => es.all LowCTRepresentable.Expr
  | .proj e _              => LowCTRepresentable.Expr e
  | .ifThenElse c t e      => LowCTRepresentable.Expr c && LowCTRepresentable.Expr t
                                && LowCTRepresentable.Expr e
  | .match_ _ _            => false  -- pattern matching not in LowCT (use ifThenElse)
  | .unitVal               => true
  | .seq e1 e2             => LowCTRepresentable.Expr e1 && LowCTRepresentable.Expr e2
  -- Phase-eliminated constructors: must have been removed before subset filter
  | .borrow _              => false
  | .deref _               => false
  | .assign _ rhs          => LowCTRepresentable.Expr rhs
  | .forLoop _ _ _ _       => false  -- must be functionalized first
  | .forLoopRev _ _ _ _    => false
  | .whileLoop c body      => LowCTRepresentable.Expr c && LowCTRepresentable.Expr body
  | .break_ none           => false
  | .break_ (some _)       => false
  | .continue_             => false
  | .earlyReturn _         => false
  | .questionMark _        => false
  -- Surviving fold constructors (post functionalization)
  | .forFold _ _ _ _       => false  -- bounded loops not in LowCT yet
  | .forFoldRev _ _ _ _    => false
  | .whileFold c body      => LowCTRepresentable.Expr c && LowCTRepresentable.Expr body
  | .forFoldReturn _ _ _ _ => false
  | .forFoldRevReturn _ _ _ _ => false
  | .whileFoldReturn c b   => LowCTRepresentable.Expr c && LowCTRepresentable.Expr b
  | .cfBreak _             => false
  | .cfContinue _          => false
  | .cfBreakContinue _     => false
  -- A type ascription is erased.
  | .typeAscription e _    => LowCTRepresentable.Expr e

/-- Top-level predicate.  We treat an `ImpExpr` body as a sequence of
    statements; representability of the whole body is representability of
    the expression. -/
def LowCTRepresentable.Stmt (e : ImpExpr) : Bool := LowCTRepresentable.Expr e

/-! ## §4  Diagnostic variant -/

/-- Diagnostic predicate: returns `none` if the expression is representable,
    or `some reason` describing the first non-representable construct.

    Useful for downstream hax-side tooling that wants to point users to a
    specific line ("rejected: `Result` types not supported"). -/
partial def LowCTRepresentable.reasonExpr : ImpExpr → Option String
  | .lit l =>
      if LowCTRepresentable.Lit l then none
      else some "literal not in LowCT subset (signed integer?)"
  | .var _ => none
  | .letBind _ v b =>
      (LowCTRepresentable.reasonExpr v).orElse (fun _ => LowCTRepresentable.reasonExpr b)
  | .lam _ _ => some "first-class closure not in LowCT subset"
  | .app f args =>
      if !callWhitelist.contains f then
        some s!"call to non-whitelisted function `{f}`"
      else
        args.foldl (fun acc a =>
          acc.orElse (fun _ => LowCTRepresentable.reasonExpr a)) none
  | .tuple es =>
      es.foldl (fun acc a =>
        acc.orElse (fun _ => LowCTRepresentable.reasonExpr a)) none
  | .proj e _ => LowCTRepresentable.reasonExpr e
  | .ifThenElse c t e =>
      (LowCTRepresentable.reasonExpr c).orElse (fun _ =>
        (LowCTRepresentable.reasonExpr t).orElse (fun _ =>
          LowCTRepresentable.reasonExpr e))
  | .match_ _ _      => some "pattern match not in LowCT subset (use if/else)"
  | .unitVal         => none
  | .seq e1 e2 =>
      (LowCTRepresentable.reasonExpr e1).orElse
        (fun _ => LowCTRepresentable.reasonExpr e2)
  | .borrow _        => some "borrow not eliminated (run dropReferences first)"
  | .deref _         => some "deref not eliminated (run dropReferences first)"
  | .assign _ rhs    => LowCTRepresentable.reasonExpr rhs
  | .forLoop _ _ _ _ =>
      some "raw for-loop not allowed (run functionalizeLoops first)"
  | .forLoopRev _ _ _ _ =>
      some "raw reverse for-loop not allowed (run functionalizeLoops first)"
  | .whileLoop c b =>
      (LowCTRepresentable.reasonExpr c).orElse (fun _ => LowCTRepresentable.reasonExpr b)
  | .break_ _        => some "`break` not in LowCT subset"
  | .continue_       => some "`continue` not in LowCT subset"
  | .earlyReturn _   => some "early return not in LowCT subset (run cfIntoMonads first)"
  | .questionMark _  => some "`?` operator not in LowCT subset"
  | .forFold _ _ _ _ => some "bounded for-fold not yet supported by LowCT"
  | .forFoldRev _ _ _ _ => some "bounded reverse for-fold not yet supported by LowCT"
  | .whileFold c b =>
      (LowCTRepresentable.reasonExpr c).orElse (fun _ => LowCTRepresentable.reasonExpr b)
  | .forFoldReturn _ _ _ _    => some "for-fold-return not in LowCT subset"
  | .forFoldRevReturn _ _ _ _ => some "reverse for-fold-return not in LowCT subset"
  | .whileFoldReturn c b =>
      (LowCTRepresentable.reasonExpr c).orElse (fun _ => LowCTRepresentable.reasonExpr b)
  | .cfBreak _         => some "control-flow break not in LowCT subset"
  | .cfContinue _      => some "control-flow continue not in LowCT subset"
  | .cfBreakContinue _ => some "nested break/continue not in LowCT subset"
  | .typeAscription e _ => LowCTRepresentable.reasonExpr e

/-- Top-level diagnostic predicate. -/
def LowCTRepresentable.reason (e : ImpExpr) : Option String :=
  LowCTRepresentable.reasonExpr e

/-! ## §5  Smoke tests -/

namespace SmokeTests

/-- Helper: BLS12 `Fp` value variable. -/
def fpVar (name : String) : ImpExpr := .var name

/-- Helper: build a tower-typed leaf call. -/
def fpAdd (x y : ImpExpr) : ImpExpr := .app "fp_add" [x, y]
def fpMul (x y : ImpExpr) : ImpExpr := .app "fp_mul" [x, y]

/-- ###  Test 1 — accept

A small representable kernel:
```
let t = fp_mul(a, b);
let r = fp_add(t, c);
r
```
-/
def simpleKernel : ImpExpr :=
  .letBind "t" (fpMul (fpVar "a") (fpVar "b"))
    (.letBind "r" (fpAdd (fpVar "t") (fpVar "c"))
      (fpVar "r"))

example : LowCTRepresentable.Stmt simpleKernel = true := by native_decide
example : LowCTRepresentable.reason simpleKernel = none := by native_decide

/-- ###  Test 2 — reject literal `unsupported`

An expression containing `Hax.Expr.unsupported` (modelled as a forbidden
constructor) — using `borrow` as a stand-in for "phase-eliminated /
explicitly unsupported": -/
def borrowed : ImpExpr := .borrow (fpVar "a")

example : LowCTRepresentable.Stmt borrowed = false := by native_decide
example : (LowCTRepresentable.reason borrowed).isSome = true := by native_decide

/-- ###  Test 3 — reject non-whitelisted call

`secret_load(a)` is not in `callWhitelist`, so the kernel must be rejected. -/
def badCallKernel : ImpExpr :=
  .letBind "x" (.app "secret_load" [fpVar "a"]) (fpVar "x")

example : LowCTRepresentable.Stmt badCallKernel = false := by native_decide
example : LowCTRepresentable.reason badCallKernel
        = some "call to non-whitelisted function `secret_load`" := by native_decide

/-- ### Test 4 — reject `Result` type at the type level. -/
example : LowCTRepresentable.Type (.result (.uint .w64) (.uint .w64)) = false := by
  native_decide

/-- ### Test 5 — accept `(u64, Fp)` tuple type. -/
example : LowCTRepresentable.Type
            (.tuple [.uint .w64, .adt "Fp" []]) = true := by native_decide

/-- ### Test 6 — reject `Option<u64>` type. -/
example : LowCTRepresentable.Type (.option (.uint .w64)) = false := by native_decide

/-- Named theorems for `lean_verify` axiom checks. -/
theorem simple_kernel_ok : LowCTRepresentable.Stmt simpleKernel = true := by native_decide
theorem bad_call_rejected : LowCTRepresentable.Stmt badCallKernel = false := by native_decide

end SmokeTests

/-! ## §6  Follow-up tracks

This file is the **starting point** of Track H1. The remaining work:

### H1 finish (≈ 2 weeks)

* Tighten `towerOfAdtName` against the actual hax extraction names used by
  the BLS12-381, Curve25519, P-256 crates.  Current names are educated
  guesses based on the existing `HaxTypes.lean` bridges.
* Recognise tower types via a Rust *marker trait* (e.g. `#[catcrypt(tower)]`)
  rather than name matching, to make the filter robust to renamings.
* Add a separate filter for **function signatures** (`ImpType.fn`): every
  parameter and return must be representable, plus the function must be
  marked `#[catcrypt(safe_kernel)]`.

### H2: type mapping `Hax.RawCode → LowCT` (≈ 1 week)

Skeleton — to live in a sibling file `LowCTLowering.lean`:

```lean
def lowerType : ImpType → Option TowerType := towerOfImpType
def lowerExpr : ImpExpr → Option LowCT := sorry  -- see notes
def lowerFn : ImpFn → Option LowCT := sorry
```

Key challenges:
* SSA-style fresh-name generation for intermediate `RLetZero` slots.
* Matching `app "fp_mul"` to the corresponding `RCall` with correctly typed
  `Located` arguments.
* Lowering `ifThenElse` over a `bool` to `RIfNz` (requires CT-safe scalar
  condition encoding).

### H3: borrow-check alignment (≈ 3 days)

Theorem statement:

```lean
theorem borrowOk_of_rustc_accepts (e : ImpExpr) (h : LowCTRepresentable.Stmt e)
    (ho : ∃ c, lowerExpr e = some c) :
    ∀ c, lowerExpr e = some c → LowCTBorrowCheck.borrowOk c
```

i.e. *if* hax/rustc produced `e` (so it borrow-checks in Rust) *and* `e`
passes our subset filter, then the lowered `LowCT` passes our borrow
checker too.  Proof relies on lowering using fresh `dest` names for every
call (no aliasing).

### H4: dalek as the first user (≈ 1 week)

Pick `dalek_curve25519::Scalar::add`, run hax → `ImpExpr`, run
`LowCTRepresentable.reason` to point out non-conformant constructs, fix
or add to the whitelist, and use the resulting `LowCT` in the
`catcrypt-bench/src/dalek_bench.rs` harness.
-/

end CatCrypt.Crypto.Hax
