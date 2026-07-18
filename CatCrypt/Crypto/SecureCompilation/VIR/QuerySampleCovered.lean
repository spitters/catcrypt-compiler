/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectUnifiedDenote

set_option autoImplicit false

/-!
# The Plonky3 DuplexChallenger query sampler as one `IsCoveredSU` program

`Plonky3QuerySampleOwnedEmit` deploys the `DuplexChallenger<16,8>` sample/observe
wrapper as owned `Lcmd` control flow; the prior wall analysis showed its CONTROL
shape — `observe = if trigger { call duplex; store }`, `sample = if trigger {
call duplex_n; store }`, and the runtime absorb loop — needs an `RCond` (a
guarded forward branch, NOT the φ-merge) and a runtime `RWhileNz`, SEQUENCED,
which sits outside any single one of the five landed control fragments.

`TranslateDialectUnifiedDenote.IsCoveredSU` is exactly the closure that covers
it: an `RSeq` whose children may be `RCond`/`RWhileNz`.  This module models the
sampler's control skeleton as one `LowCT` program and descends it through the
unified front + denote:

* `querySampleLowCT` — the sampler control skeleton: the observe conditional, the
  sample conditional, and the runtime absorb loop, in one `RSeq` spine.  The
  Poseidon2 permute / duplex leaves are opaque `RCall`s (the round arithmetic is
  the called leaf, not modeled here).
* `querySample_coveredU` — `IsCoveredSU querySampleLowCT`, structural.
* `querySampleCovered_denote` — the whole-program denote, a direct
  `transU_denote` instantiation: the unified front descent denotes exactly the
  unified `semU` waist.
* the non-vacuity witnesses — a concrete run where `semU` TERMINATES with a value
  (the observe block FIRES, the sample block SKIPS, and the absorb loop counts
  down) and the front descent `transU` succeeds.  These refute the opaque-leaf
  vacuity trap: the denote hypothesis `semU … = some env'` is SATISFIABLE, and
  both the guard-true (fire) and guard-false (skip) legs of `RCond` are exercised.

## The guard-expressibility residual (the SLt/`srcClean` sub-wall)

The exact sampler triggers are `inlen == 8` (observe) and `inlen > 0 || outlen ==
0` (sample).  Encoding equality/disjunction as a precomputed word flag needs the
`SExpr` comparison `SLt` — but `srcClean` (the front-covered `SExpr` fragment)
maps `SLt` to `False` (no jasmin lowering for the compare), so an `RScalarSetExpr`
carrying an `SLt` flag is NOT `IsCoveredS`.  So the literal `== 8` / disjunctive
triggers are the named residual: closing them needs `SLt` (or a fused `==`) added
to `srcClean` with its jasmin lowering.

What the covered fragment DOES express is the natural nonzero guard `guardNz name`
(`name != 0`) on the sponge counters — and `inlen > 0` IS exactly `guardNz
"inlen"`.  So the witness sampler carries genuine data-dependent `!= 0` guards on
`inlen`/`outlen` (the observe fires iff `inlen != 0`, the sample iff `outlen !=
0`), and a genuine `SSub` countdown absorb loop (which `srcClean` DOES cover).
The CONTROL shape (`RSeq` of two `RCond`s and one `RWhileNz`) — the unification's
whole point — is delivered in full; only the compare-in-guard is the residual.

**0 sorries; no axioms beyond the front's existing set.**
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.QuerySampleCovered

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms (tmpName)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)

/-! ## 1. The absorb-loop countdown body (srcClean) -/

/-- The absorb-loop body's counter decrement `ctr := ctr -ₛ 1` (saturating
    `SSub`).  `srcClean` (so `IsCoveredS`), and it drives the `guardNz "ctr"`
    do-while to terminate in `ctr` trips. -/
def decCtr : SExpr := .SSub (.SVar "ctr") (.SLit 1)

/-- `"ctr"` (length 3) is not a `__sx` fresh temp, so `SVar "ctr"` is `srcClean`. -/
theorem not_isTmp_ctr : ¬ isTmpName "ctr" := by
  rintro ⟨k, hk⟩
  have hlen := congrArg String.length hk
  rw [tmpName, String.length_append] at hlen
  have h2 : "__sx".length = 4 := rfl
  have h3 : "ctr".length = 3 := rfl
  omega

/-- The countdown body is in the covered `SExpr` fragment. -/
theorem decCtr_srcClean : srcClean decCtr :=
  ⟨not_isTmp_ctr, by simp only [srcClean]; norm_num⟩

/-! ## 2. The sampler control skeleton -/

/-- The observe/sample duplex leaves as opaque `RCall`s (destination is the sponge
    state `st`; the round arithmetic is the called leaf). -/
def duplexFull : LowCT := .RCall "p3_fs_duplex" ⟨"st", .TU64⟩ []
def duplexN : LowCT := .RCall "p3_fs_duplex_n" ⟨"st", .TU64⟩ []

/-- **The DuplexChallenger query-sampler control skeleton**, one `LowCT` program:

    ```
    -- observe
    outlen := 0
    if inlen != 0 { call p3_fs_duplex ; inlen := 0 }
    -- sample
    if outlen != 0 { call p3_fs_duplex_n ; outlen := 8 }
    -- absorb (runtime-N)
    while ctr != 0 { ctr := ctr - 1 }
    ```

    The conditionals are `RCond` (guarded forward branch, NOT the φ-merge — the
    block does NOT run when the guard is zero); the absorb is a data-dependent
    `RWhileNz`.  The whole is one `RSeq` spine of two `RCond`s and one `RWhileNz`
    — outside any single one of the five landed fragments, inside `IsCoveredSU`.
    (The `!= 0` guards are the covered stand-in for the exact `== 8` /
    disjunctive triggers — see the module residual.) -/
def querySampleLowCT : LowCT :=
  .RSeq
    (.RSeq (.RScalarSet "outlen" 0)
      (.RIfNz "inlen" (.RSeq duplexFull (.RScalarSet "inlen" 0)) .RSkip))
    (.RSeq
      (.RIfNz "outlen" (.RSeq duplexN (.RScalarSet "outlen" 8)) .RSkip)
      (.RWhileNz "ctr" (.RScalarSetExpr "ctr" decCtr)))

/-! ## 3. Coverage: the sampler is `IsCoveredSU` -/

/-- **The sampler is covered by the unified predicate.**  Structural: the two
    conditionals are `rCond` (over straight-line `call; store` blocks), the absorb
    is `rWhile` (over the `srcClean` decrement), and the leading `outlen := 0` is
    an `ofCtl` leaf — all threaded by `rSeq`. -/
theorem querySample_coveredU : IsCoveredSU querySampleLowCT := by
  refine .rSeq
    (.rSeq (.ofCtl (.ofStraight (.rScalarSet _ _)) rfl)
      (.rCond (.rSeq (.ofCtl (.ofStraight (.rCall _ _ _)) rfl)
        (.ofCtl (.ofStraight (.rScalarSet _ _)) rfl))))
    (.rSeq
      (.rCond (.rSeq (.ofCtl (.ofStraight (.rCall _ _ _)) rfl)
        (.ofCtl (.ofStraight (.rScalarSet _ _)) rfl)))
      (.rWhile (.ofCtl (.ofStraight (.rScalarSetExpr _ _ decCtr_srcClean)) rfl)))

/-! ## 4. The whole-program denote (the deliverable) -/

/-- **Owned query-sampler whole-program denote.**  For any entry state consistent
    with the source env, whenever the unified front descent `transU` succeeds and
    the unified waist `semU` terminates (the observe/sample blocks fire per their
    guards, the absorb loop counts down within `fuel`), the emitted `Com`-prefix
    denotes exactly the `semU` waist.  A direct instantiation of `transU_denote`
    at `querySample_coveredU`: the sampler descends through the unified
    homomorphism that COMPOSES the five landed control-fragment lemmas. -/
theorem querySampleCovered_denote (fuel : Nat) {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env env' : SEnvScalar)
    (o : DTransOut Γ)
    (hc : ConsistentS vm V env)
    (htr : transU fuel vm env querySampleLowCT = some o)
    (hsem : semU fuel querySampleLowCT env = some env') :
    ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
      ConsistentS o.vm V' env' ∧
      ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
        ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' :=
  transU_denote fuel querySample_coveredU vm V env env' o hc htr hsem

/-! ## 5. Non-vacuity: a concrete run terminates and the front descends

The denote's `semU … = some env'` hypothesis is SATISFIABLE, and the front
descent `transU` succeeds — so the denote is not vacuous.  Concrete entry:
`inlen = 8` (the observe conditional FIRES), `outlen = 0` (the sample conditional
SKIPS — the guard-false leg, where the duplex call does NOT run), `ctr = 2` (a
2-trip absorb loop). -/

/-- A concrete entry env with the counters bound: `inlen = 8`, `outlen = 0`,
    `ctr = 2`. -/
def qsEnv0 : SEnvScalar :=
  SEnvScalar.upd (SEnvScalar.upd (SEnvScalar.upd (fun _ => none)
    "inlen" (t := .sword 64) (8 : BitVec 64))
    "outlen" (t := .sword 64) (0 : BitVec 64))
    "ctr" (t := .sword 64) (2 : BitVec 64)

/-- The matching entry varmap (the three counter slots). -/
def qsVm0 : VarMap [.sword 64, .sword 64, .sword 64] :=
  ((VarMap.empty.bind "inlen").bind "outlen").bind "ctr"

/-- **Non-vacuity (semantics).**  The unified waist TERMINATES on the concrete
    entry: the observe conditional fires (`inlen != 0`), the sample conditional
    skips (`outlen == 0`), and the absorb loop counts `ctr = 2` down to `0` within
    `fuel = 8`.  So the denote's `semU … = some env'` hypothesis is satisfiable —
    the run is genuine, not an unsatisfiable premise. -/
theorem querySample_semU_terminates :
    (semU 8 querySampleLowCT qsEnv0).isSome = true := by native_decide

/-- **Non-vacuity (front).**  The unified front descent SUCCEEDS on the concrete
    entry: every conditional selects a descent by its run-time guard, the absorb
    loop unrolls to its 2-trip run count, and every leaf (opaque duplex calls,
    stores, decrement) front-compiles. -/
theorem querySample_transU_isSome :
    (transU 8 qsVm0 qsEnv0 querySampleLowCT).isSome = true := by native_decide

/-- **The observe guard genuinely FIRES here** (`inlen = 8 != 0`): the duplex call
    DOES run on this entry — the guard-true leg of the `RCond` forward branch. -/
theorem querySample_observe_fires : guardNz "inlen" qsEnv0 = true := by native_decide

/-- **The sample guard genuinely SKIPS here** (`outlen = 0`): the duplex_n call
    does NOT run — the guard-false leg, the key `rCond_whole_denote` non-vacuity
    (distinguishing the genuine forward branch from a φ-merge that would run the
    block regardless). -/
theorem querySample_sample_skips : guardNz "outlen" qsEnv0 = false := by native_decide

/-- **The absorb loop trip count is the runtime counter** (`ctr = 2 ↦ 2` trips):
    a data-dependent loop, read off the run, not a static unroll. -/
theorem querySample_absorb_trips :
    scalarWhileTrips (fun e => semScalar (.RScalarSetExpr "ctr" decCtr) e)
      (guardNz "ctr") 8 qsEnv0 = 2 := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.QuerySampleCovered

