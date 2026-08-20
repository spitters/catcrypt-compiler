/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.LowCT

/-!
# CProg-free `LowCT.leakTrace` definition

This module carries the **CProg-free** core of the LowCT-side leakage
trace: the `LeakEvent` / `LeakTrace` observable types and the
structural function `LowCT.leakTrace : LowCT → LeakTrace`.

It is a function of LowCT *syntax only* — it never mentions `CProg`,
`CExpr`, `translate`, or any CryptoSSA front. Splitting it out lets the
live IrisBridge leakage chain (`LowCTVartimeLeak` →
`IrisBridge/LeakageRelational` → IrisBridge) depend on `LowCT.leakTrace`
without pulling in the CProg-stated agreement theorems of
`LowCTLeakTrace.lean` (which is on the CProg-deletion path).

The `LeakEvent` / `LeakTrace` types live in the
`...SecureCompilation.CryptoSSA` namespace so that existing
`open ...CryptoSSA` clients (and `LowCTLeakTrace.lean`'s CProg-side
agreement proofs) resolve `LeakEvent` / `LeakTrace` unchanged.

The table mapping each LowCT constructor to its emitted CryptoSSA prefix
(and hence its `leakTrace`) is documented in `LowCTLeakTrace.lean`, which
proves the agreement theorems against the CryptoSSA front.

**0 sorries**, standard axioms only.
-/

namespace CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-! ## §0. Leakage events and traces (CProg-free)

These are the observable leakage types. In the constant-time model, an
adversary can observe WHICH operations execute (and in what order), but
not the VALUES processed. The CProg-side instrumented semantics
(`CExpr.leakEvent`, `CProg.leakTrace`, …) live in `SSALeakage.lean` and
reuse these same types. -/

/-- Observable leakage events during program execution. -/
inductive LeakEvent where
  /-- A pure operation was executed. -/
  | pureOp (name : String)
  /-- A sampling operation was executed. -/
  | sampleOp
  deriving DecidableEq, Repr

/-- Leakage trace: sequence of observable events during execution. -/
abbrev LeakTrace := List LeakEvent

end CatCrypt.Crypto.SecureCompilation.CryptoSSA

namespace CatCrypt.Crypto.SecureCompilation.LowCTLeakTrace

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA

set_option autoImplicit false

/-! ## §1. Structural leak trace -/

/-- The leakage trace of a LowCT source program, as a structural
function of the program's syntax. The trace records which CryptoSSA
events the program emits after `translate`, in order.

For the no-control-flow fragment (everything except `RIfNz`,
`RWhileNz`, `RFor`), the trace is exact — `leakTrace_translate_id`
(in `LowCTLeakTrace.lean`) proves the equality with the post-translation
`CProg.leakTrace`. For `RIfNz` we over-approximate as the union of both
branches (matching the φ-merge worst case); for `RWhileNz`/`RFor` we
return the body's trace followed by the loop's static tail. -/
def LowCT.leakTrace : LowCT → LeakTrace
  | .RSkip                           => []
  | .RSeq c1 c2                      => leakTrace c1 ++ leakTrace c2
  | .RScalarSet _ _                  => [.pureOp "bvConst"]
  | .RLetU64Zero _ body              =>
      .pureOp "bvConst" :: leakTrace body
  | .RLetZero _ .TU64 body           =>
      .pureOp "bvConst" :: leakTrace body
  | .RLetZero _ .TFp body            =>
      .pureOp "memrefZero" :: leakTrace body
  | .RLetZero _ .TFp2 body           =>
      .pureOp "memrefZero" :: leakTrace body
  | .RLetZero _ .TFp6 body           =>
      .pureOp "memrefZero" :: leakTrace body
  | .RLetZero _ .TFp12 body          =>
      .pureOp "memrefZero" :: leakTrace body
  | .RLetZero _ .TFp25519 body       =>
      .pureOp "memrefZero" :: leakTrace body
  | .RLetZero _ .TFp25519_64 body    =>
      .pureOp "memrefZero" :: leakTrace body
  -- Phase D/E/I/K (2026-05-03): the new tower types translate to `none`
  -- in `LowCTToCryptoSSA`, so no events are emitted.
  | .RLetZero _ .TFpL25519 _         => []
  | .RLetZero _ .TFpP256 _           => []
  | .RLetZero _ (.TFp25519_4Bounded _) _ => []
  | .RLetZero _ (.TFpGen _ _) _      => []
  | .RLetZero _ (.TFp2Gen _ _) _     => []
  | .RLetZero _ (.TTuple _ _) _      => []
  | .RLetZero _ (.TBytes _) _        => []
  -- Phase Ext (2026-05-14): TArr similarly translates to `none`.
  | .RLetZero _ (.TArr _ _) _        => []
  -- Phase L stage 2/3 (2026-05-24): polynomial-mod-q / vec / mat now
  -- translate to a `memrefZero` allocation then the body's trace.
  | .RLetZero _ (.TPolyMod _ _) body    =>
      .pureOp "memrefZero" :: leakTrace body
  | .RLetZero _ (.TPolyVec _ _ _) body  =>
      .pureOp "memrefZero" :: leakTrace body
  | .RLetZero _ (.TPolyMat _ _ _ _) body =>
      .pureOp "memrefZero" :: leakTrace body
  -- Phase L.1 (2026-05-23): u8 / u32 scalars translate to `none`.
  | .RLetZero _ .TU8 _               => []
  | .RLetZero _ .TU32 _              => []
  | .RCall f _ _                     =>
      [.pureOp ("extCall:" ++ f)]
  | .RCloneCall _ _ _ innerF _ _     =>
      [.pureOp "extCall:clone", .pureOp ("extCall:" ++ innerF)]
  | .RIfNz _ ct cf                   =>
      -- Over-approximation: both branches contribute. Tight
      -- characterisation requires φ-merge case analysis.
      leakTrace ct ++ leakTrace cf
  -- CWhile uplift (#207, 2026-05-29): `translate` maps `RWhileNz e body`
  -- to `cwhile counter bodyProg`, where `bodyProg` is the body's program
  -- closed off by `letBind constUnit (ret here)` (one `constUnit` event).
  -- The placeholder `cwhile` denotation runs zero iterations, so the
  -- static leak trace is the body's trace followed by that unit tail.
  | .RWhileNz _ body                 =>
      leakTrace body ++ [.pureOp "constUnit"]
  -- `RFor x N body` is inline-unrolled by translate (2026-05-27): N iterations
  -- of `letBind (bvConst _)` (the `x := i` binding) plus body's leakTrace.
  | .RFor _ N body                   =>
      List.replicate N (.pureOp "bvConst" :: leakTrace body) |>.flatten
  -- Stage 1a (2026-07-01): `translate` declines the runtime loop (its trip
  -- count is not statically known), so it emits a single placeholder marker.
  | .RForRuntime _ _ _               =>
      [.pureOp "forRuntime"]
  | .RLimbStore _ _ _                =>
      [.pureOp "bvConst", .pureOp "memrefSet"]
  -- Phase F/G/H/L/M (2026-05-03): structural trace for the new constructors.
  | .RCallSwap f _ _ _               =>
      -- Two sequential single-out calls (matches LowCTToCryptoSSA).
      [.pureOp ("extCall:" ++ f), .pureOp ("extCall:" ++ f)]
  -- Multi-output `RCallN` emits one opaque `extCall` per destination
  -- (`dests.length` events), named by the destination's index through
  -- `callNLeafName` so the trace records the leaf names the call reads.
  -- The indices are positions in the syntax, so the trace remains a
  -- function of the program text alone.
  | .RCallN f dests _                =>
      dests.mapIdx (fun i _ => .pureOp ("extCall:" ++ callNLeafName f i))
  -- Phase H (#280): `translate` models cmov as a single opaque
  -- `extCall "select"` (both sources read unconditionally — CT).
  | .RSelect _ _ _ _                 =>
      [.pureOp "extCall:select"]
  | .RAssert _                       => []
  | .RBlock body                     => leakTrace body
  | .RFnDef _ _ _ body cont          => leakTrace body ++ leakTrace cont
  | .RFnCall f _ _                   =>
      [.pureOp ("extCall:" ++ f)]
  -- Phase FF (#288/REV-9): tuple component load translates to one opaque
  -- extCall whose name folds in the literal component index `idx` (CT — a
  -- compile-time constant, never a secret index).
  | .RTupleLoad _ _ idx              => [.pureOp ("extCall:" ++ ("tupleLoad:" ++ toString idx))]
  -- Dynamic-index array ops now translate to one opaque `extCall` (carrying the
  -- runtime index as an argument), mirroring the literal-index `RArrStoreLit`/
  -- `RArrLoadLit` leak shape — one public `pureOp` event (the op ran; no value).
  | .RArrStore _ _ _                 => [.pureOp ("extCall:" ++ "arrStoreDyn")]
  | .RArrLoad _ _ _                  => [.pureOp ("extCall:" ++ "arrLoadDyn")]
  | .RScalarSetExpr _ _              => []
  -- Phase DD (#280): literal-index array access now translates to a single
  -- opaque `extCall` whose name folds in the literal index (CT — the index
  -- is a compile-time constant, not a secret).  Dst-threaded leaf call still
  -- translates to `none`, so no events are emitted.
  | .RArrStoreLit _ idx _            => [.pureOp ("extCall:" ++ ("arrStore:" ++ toString idx))]
  | .RArrLoadLit _ _ idx             => [.pureOp ("extCall:" ++ ("arrLoad:" ++ toString idx))]
  -- Phase R5 (2026-06-01): runtime-valued limb store lowers (in the CryptoSSA
  -- front) to a single opaque `extCall ("limbStoreExpr:" ++ idx)`, like
  -- `RArrStoreLit`, so its structural trace is the matching `[extCall:…]`.
  | .RLimbStoreExpr _ idx _          => [.pureOp ("extCall:" ++ ("limbStoreExpr:" ++ toString idx))]
  -- Phase E2 (#207/REV-9): dst-threaded leaf call lowers (like `RCall`) to a
  -- single opaque `extCall f` — the dst-as-first-arg ABI is a call-name
  -- detail, not a leak distinction, so the structural trace is `[extCall:f]`.
  | .RCallDstThreaded f _ _          => [.pureOp ("extCall:" ++ f)]

end CatCrypt.Crypto.SecureCompilation.LowCTLeakTrace
