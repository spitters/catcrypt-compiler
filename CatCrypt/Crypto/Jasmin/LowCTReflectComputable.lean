/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public meta import Std.Tactic.BVDecide.Reflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect

/-!
# `@[rust_cmd_pattern_computable]` — worked example

Sibling to `CatCrypt.Crypto.Jasmin.LowCTReflect`.  Shows the new
`@[rust_cmd_pattern_computable]` attribute (added 2026-05-28 to
`LowCTReflect.lean`) in action on a tiny computable-bodied leaf, and
proves that the cross-side identity between the registered head and its
verified body is `rfl`-provable.

This file is a **smoke test** for the metaprogramming extension; it is
deliberately small and self-contained, so any future change to the
`@[rust_cmd_pattern]`/`@[rust_cmd_pattern_computable]` macros can verify
the contract here before touching the larger consumers.

## What we demonstrate

1. A `noncomputable def` (`gf16ToyAdd`) whose body is a verified Lean
   expression (here, `BitVec.xor` over 4 bits as a stand-in for a
   GF(16) operation).
2. A `@[rust_cmd_pattern_computable]` registration tying `gf16ToyAdd`
   to a leaf-name string + arity + tower type.
3. A cross-side identity theorem proved by `rfl` — what would be a
   cross-side **axiom** under `@[rust_cmd_pattern]` (where the head
   is an `axiom`) becomes a **proved theorem** under
   `@[rust_cmd_pattern_computable]` (where the head is a `def` and
   the body is visible to definitional equality).

## Scaling out

The MAYO/UOV bridge consumers (`MayoKernelBridge.lean`,
`UovKernelBridge.lean`) still depend on opaque axioms because their
Rust↔Lean correspondence claims are about EMITTED ASSEMBLY behavior, not
Lean equational identities — so an `axiom` is the right shape there.
This file targets the OTHER use case: protocols whose "leaf" is a
Lean-level abstraction that has a real verified body the security proof
needs to see through.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.LowCTReflectComputable

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTReflect

/-! ## 1. Opaque surface type + computable-bodied leaf -/

/-- A toy 4-bit field element.  Used here only to anchor a tower type
    for the demonstration; the real GF(16) is in
    `CatCrypt.Crypto.Util.Gf16`. -/
abbrev Gf16Toy : Type := BitVec 4

/-- A computable-bodied "leaf": GF(16) addition (XOR over 4 bits).
    This is a `def` (not an `axiom`), so its body is visible to `rfl`. -/
def gf16ToyAdd (a b : Gf16Toy) : Gf16Toy := a ^^^ b

/-- Register `gf16ToyAdd` as a `@[rust_cmd_pattern_computable]` leaf.
    The reifier (when consulting the registry) will recognise the head
    `gf16ToyAdd` BEFORE running `whnf` — preventing `whnf` from unfolding
    the def body to `a ^^^ b` and losing the registered head. -/
@[rust_cmd_pattern_computable]
def gf16ToyAddPattern : LowCTPattern where
  name      := "gf16_toy_add"
  fnHead    := ``gf16ToyAdd
  arity     := 2
  towerType := .TBytes 1

/-! ## 2. Cross-side identity — provable by `rfl`

This is the headline win.  Under the legacy `@[rust_cmd_pattern]`
attribute, the leaf would be an `axiom` (no body), so the cross-side
identity between the leaf and its verified spec would be an `axiom`
too.  Under `@[rust_cmd_pattern_computable]`, the leaf has a `def`
body, so the cross-side identity reduces to `rfl`. -/

/-- The cross-side identity between the registered leaf and its verified
    spec.  In the legacy axiom shape, this would be a cross-side axiom;
    here, since the leaf IS the spec, it is `rfl`. -/
theorem gf16ToyAdd_eq_xor (a b : Gf16Toy) :
    gf16ToyAdd a b = a ^^^ b := rfl

/-- Round-trip: composing the leaf with itself twice over the same input
    yields the zero element (since `a ^^^ b ^^^ b = a` and then `a ^^^ a =
    0`).  A small sanity check that the def's body is exercised. -/
theorem gf16ToyAdd_idempotent (a : Gf16Toy) :
    gf16ToyAdd a a = (0 : Gf16Toy) := by
  unfold gf16ToyAdd
  bv_decide

/-! ## 3. Verification that the registry is populated

Read the registry's tagged-decls list at elaboration time (`run_meta`, so
the `meta` registry is accessible) to confirm `gf16ToyAddPattern`'s name
is recorded.  This is the same shape of inspection the `UovReflect.lean`
and `MayoReflect.lean` files use to verify their own registrations. -/

open Lean in
run_meta do
  let names ← LowCTPattern.computableDecls
  unless names.any (· == ``gf16ToyAddPattern) do
    throwError "gf16ToyAddPattern not found in computableDecls registry"

/-! ## 4. Architecture note — when to use `_computable` vs the legacy

Use `@[rust_cmd_pattern]` (legacy, head is an `axiom`) when:
* The leaf semantics live OUTSIDE Lean (Rust shim / jasmin .jinc body).
* The L3 bridge claim is about emitted-assembly byte behavior — not a
  Lean-level equational identity.
* Examples: `mayo_quadform_n8`, `gf256_dot_l8`, `snova_ring_dot_n4_l2`.
  Their bridge axiom (e.g. `mayo_quadform_n8_eq_jincModel`) is an
  irreducible ABI-encoding claim about a Rust binary.

Use `@[rust_cmd_pattern_computable]` (new, head is a `def`) when:
* The leaf has a real Lean body the security proof needs to see through.
* Example: a verified-pure-Lean computation that you want both registered
  with the reifier AND used as the reference body for `rfl`-based bridge
  identities.  No ABI axiom needed because the leaf IS the spec.

Both attributes share the same persistent registry shape (`LowCTPattern`)
and the same downstream pipeline (`translate → cryptoDialectToJasminCom →
emitAbiOrch...` sees an opaque `extCall "<leaf-name>"` regardless).
The only difference is whether the reifier's `whnf` is bypassed for the
head (yes for `_computable`, no for the legacy attribute).  -/

end CatCrypt.Crypto.Jasmin.LowCTReflectComputable
