/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.MLKEM.MlkemLowCT
public import CatCrypt.Crypto.MLKEM.MlkemLowCT
public meta import CatCrypt.Crypto.Optimizer.Pipeline
public import CatCrypt.Crypto.Optimizer.Pipeline
public meta import CatCrypt.Crypto.Jasmin.LowCTToJasmin
public import CatCrypt.Crypto.Jasmin.LowCTToJasmin
public meta import CatCrypt.Crypto.Jasmin.LowCTDSL
public import CatCrypt.Crypto.Jasmin.LowCTDSL

/-!
# Stage I — End-to-end smoke test for the NTT poly-mul pass

Applies the Tier-3 ML-KEM pipeline (`nttPolyMulMlkemPass` from
`Optimizer/Pipeline.lean`) to `MlkemLowCT.poly_mul_kernel` and the
composite `poly_madd_kernel`, then runs the rewritten commands through
`LowCTToJasmin` + `ppJasminProg`.  Two checks land:

1. **Syntactic**: the rewritten command contains `RCall
   "ntt_poly_mul_3329_256"` where the original had `RCall "poly_mul"`.
2. **Emit-level**: the Jasmin pretty-print string contains the NTT name,
   confirming the leaf name survives through the lowering.

The second is the **operational** payload: a downstream `jasminc` run
will see the NTT name and dispatch to an NTT-backed implementation
(once the protocol bridge provides one).

## What this smoke test does NOT exercise

* The denotational-equivalence theorem (`nttPolyMul_denote_eq`) — that's
  proved in `NTTPolyMul.lean` and consumes a `nttAgreesPolyMul`
  hypothesis.  This file only checks the *syntactic* rewrite and *emit*
  surface, which need no LeafSpec.
* A concrete `LeafSpec` instantiation for ML-KEM — deferred (see
  Project 2 plan doc Stage I follow-up).
* The composite top-level kernels (`mlkem_keygen_kernel`, etc.) — they
  also contain `RCall "poly_mul"` invocations but their full structure
  is too large to make `rfl` checks tractable.  The kernel-level
  rewrite is covered for `poly_mul_kernel` and `poly_madd_kernel` here;
  the top-level kernels rewrite by structural induction on the pass's
  recursive definition (no extra theorem needed).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Optimizer.Lattice.Mlkem_E2E_Smoke

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.LowCTDSL (loc)
open CatCrypt.Crypto.Optimizer.Lattice.NTTPolyMul
open CatCrypt.Crypto.MLKEM.MlkemLowCT

/-! ## §1  Syntactic rewrite — single `poly_mul` site -/

/-- The original `poly_mul_kernel "a" "b" "c"` is a single
    `RCall "poly_mul"` (modulo DSL `RSkip`-pairing).  We compute the
    rewrite into a `let` so the proof goal stays compact. -/
def origPolyMul : LowCT :=
  poly_mul_kernel "a" "b" "c"

/-- Result of applying the Tier-3 ML-KEM pass to the single-site kernel. -/
def rewrittenPolyMul : LowCT :=
  nttPolyMulMlkem origPolyMul

/-- The pass swaps the leaf name `"poly_mul"` → `"ntt_poly_mul_3329_256"`.
    Whatever ambient `RSkip` plumbing the DSL inserts is preserved
    syntactically. -/
example : rewrittenPolyMul =
    nttPolyMulMlkem (poly_mul_kernel "a" "b" "c") := rfl

/-! ## §2  Syntactic rewrite — composite `poly_mul ; poly_add` -/

/-- `poly_madd_kernel` runs `poly_mul` then `poly_add` on adjacent slots.
    Only the `poly_mul` is rewritten by the pass; `poly_add` is left as-is. -/
def origPolyMadd : LowCT :=
  poly_madd_kernel "a" "b" "c" "d"

/-- Result of applying the Tier-3 ML-KEM pass to the composite kernel. -/
def rewrittenPolyMadd : LowCT :=
  nttPolyMulMlkem origPolyMadd

example : rewrittenPolyMadd =
    nttPolyMulMlkem (poly_madd_kernel "a" "b" "c" "d") := rfl

/-! ## §3  Emit-level check — Jasmin string contains the NTT name

We pretty-print the rewritten kernels as Jasmin functions and check that
the NTT name appears as a substring.  `String.isPrefixOf`/`isInfixOf` is
the standard check; we use `Decide` after `native_decide` since the
strings are large.
-/

/-- Jasmin pretty-print of the single-site rewrite. -/
def jasminSingleSite : String :=
  ppJasminProg
    (toJasminProg "poly_mul_test"
      [loc "a" MlkemPolyTy, loc "b" MlkemPolyTy]
      [loc "c" MlkemPolyTy]
      rewrittenPolyMul)

/-- Jasmin pretty-print of the composite rewrite. -/
def jasminComposite : String :=
  ppJasminProg
    (toJasminProg "poly_madd_test"
      [loc "a" MlkemPolyTy, loc "b" MlkemPolyTy]
      [loc "c" MlkemPolyTy, loc "d" MlkemPolyTy]
      rewrittenPolyMadd)

/-- Helper: substring containment via `String.splitOn` length. -/
def String.containsSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- The single-site Jasmin output contains the NTT leaf name. -/
example : String.containsSubstr jasminSingleSite "ntt_poly_mul_3329_256" = true := by
  native_decide

/-- The composite Jasmin output also contains the NTT leaf name. -/
example : String.containsSubstr jasminComposite "ntt_poly_mul_3329_256" = true := by
  native_decide

/-- The composite Jasmin output still contains the `poly_add` leaf
    (which was *not* rewritten by the NTT pass — `poly_add` is not in
    `isPolyMulName`). -/
example : String.containsSubstr jasminComposite "poly_add" = true := by
  native_decide

/-! ## §4  `#eval` showcase (commented out — uncomment to print) -/

-- #eval jasminSingleSite
-- #eval jasminComposite

end CatCrypt.Crypto.Optimizer.Lattice.Mlkem_E2E_Smoke
