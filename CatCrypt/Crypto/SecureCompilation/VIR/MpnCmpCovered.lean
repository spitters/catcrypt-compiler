/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhileDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhileDenote

/-!
# MSB-first early-exit `mpn_cmp` whole-program denote through the covered `RWhileNz` fragment

GMP's `__gmpn_cmp(ap, bp, n)` scans two `n`-limb operands **MSB-first with a
data-dependent early exit** on the first differing limb and returns one of
`{-1, 0, +1}`. The per-limb body is straight-line (load the two limbs, compute
the difference, step the index down); the loop control is a `while` whose guard
combines *two* data-dependent conditions — "limbs remain" and "not yet differed"
— so the trip count is fixed at run time by the operand values (the early exit).

This is exactly the shape the `RWhileNz` waist denote closes
(`TranslateDialectWhileDenote.rWhileNz_whole_denote`): a data-dependent
`while (guard != 0)` over an `IsCoveredSCtl` body, denoted at the run's actual
trip count. This module re-sources `mpn_cmp` from a high-level `LowCT` term
(`mpnCmpLowCT = RWhileNz "ix" body`) through the **existing covered front** — no
new front — and banks the **whole-program machine denote** for it, the same
recipe as `Fe25519ScalarmultCovered` / `Shake256Covered`, but over the
data-dependent `RWhileNz` waist rather than the counted `RFor` / `RSeq` waist.

It strengthens the hand-authored `SpStep` schedule `MpnCmpEarlyExitFront` (a
verified-DSL step schedule with no machine denote) to a high-level
source descent whose loop region carries a fueled whole-program denote.

## Why the body is straight-line and the early exit is in the guard

`IsCoveredSCtl` (the fragment `rWhileNz_whole_denote` accepts as the loop body)
is `ofStraight` / `rFor` / `rIfNz` — it has **no** `RSeq`-of-control constructor.
The mpn_cmp per-limb body is naturally straight-line anyway: load `a[ix]`,
load `b[ix]`, compute the difference/sign, decrement `ix`. The MSB-first early
exit is not a forward jump *inside* the body — it is the loop **guard** going
false: the guard `ix != 0 && df == 0` stops the scan the moment a limb differs
(`df != 0`) or the operand is exhausted (`ix == 0`). This is precisely the
data-dependent trip count `scalarWhileTrips` reads off the run — the byte-level
`cmp ; Jcc ; jmp` early-exit shape is the downstream back-edge emitter's job
(`TranslateDialectDataWhile.rolledWhileNz`), and its value-level `{-1,0,+1}`
correctness is the external libgmp `__gmpn_cmp` KAT (opaque-leaf honesty: the
per-limb sign carrier `rs := a[ix] - b[ix]` is the arithmetic waist; the
`{-1,0,+1}` projection is the KAT obligation).

## What is banked

* `mpnCmpBody` — the straight-line per-limb scan step; `mpnCmpLowCT = RWhileNz "ix"`.
* `mpnCmp_coveredSWhile : IsCoveredSWhile mpnCmpLowCT` — the structural coverage.
* `mpnCmp_front_fires` — the covered front accepts the `RWhileNz` node (`isSome`).
* `mpnCmp_region_descends` — the trip-unrolled loop region descends through the front.
* `mpnCmpCovered_denote` — **the deliverable**: the fueled whole-program machine
  denote of the guard-driven `mpn_cmp` scan, via `rWhileNz_whole_denote` at the
  trip count read off the run.

**0 sorries; no axioms beyond the front's existing set.**
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.MpnCmpCovered

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located TowerType SExpr)

/-! ## 0. Fresh-temp exclusion for the source variable names

The `RScalarSetExpr` source variables (`ai`, `bi`, `ix`) must not collide with
the front's reserved `__sx` fresh-temp namespace (`srcClean`). Any name shorter
than the 4-char `__sx` prefix is safe. -/

/-- Any string shorter than the 4-char `__sx` temp prefix is not a fresh temp. -/
theorem not_isTmp_short (s : String) (hs : s.length < 4) : ¬ isTmpName s := by
  rintro ⟨k, hk⟩
  have hlen := congrArg String.length hk
  rw [tmpName, String.length_append] at hlen
  have h2 : "__sx".length = 4 := rfl
  omega

/-! ## 1. The high-level source: one MSB-first limb-scan step, wrapped in `RWhileNz`

Two `n`-limb operand arrays `a`/`b` (`.TBytes 32` = 4 saturated limbs),
a decrementing limb index `ix`, the per-step limbs `ai`/`bi`, the difference
flag `df` (nonzero iff `a[ix] != b[ix]`), and the sign carrier `rs`. Every
source name is length ≤ 3, so none is a `__sx` fresh temp. -/

/-- One MSB-first `mpn_cmp` limb-scan step (straight-line, `IsCoveredS`):

    * `ai := a[ix]`, `bi := b[ix]` — load the current limb pair (dynamic-index
      `RArrLoad`, the MSB-first decrementing scan reads at the running `ix`);
    * `df := ai ^ bi` — the difference flag: `xor` is nonzero *exactly* when the
      limbs differ, so the loop guard can early-exit on it with no comparison op;
    * `rs := ai - bi` — the sign carrier (compare-by-subtract; the `{-1,0,+1}`
      projection is the external libgmp `__gmpn_cmp` KAT);
    * `ix := ix - 1` — step the index down one limb (MSB-first descent). -/
def mpnCmpBody : LowCT :=
  .RSeq (.RArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes 32⟩ "ix")
    (.RSeq (.RArrLoad ⟨"bi", .TU64⟩ ⟨"b", .TBytes 32⟩ "ix")
      (.RSeq (.RScalarSetExpr "df" (.SXor (.SVar "ai") (.SVar "bi")))
        (.RSeq (.RScalarSetExpr "rs" (.SSub (.SVar "ai") (.SVar "bi")))
          (.RScalarSetExpr "ix" (.SSub (.SVar "ix") (.SLit 1))))))

/-- **The MSB-first early-exit `mpn_cmp` as one data-dependent `while`.** The
    guard variable is the limb index `ix`; the run-time guard predicate combines
    "limbs remain" and "not yet differed" (`mpnCmpGuard`), so the scan stops the
    moment a limb differs — the MSB-first early exit. A single `RWhileNz`, so it
    lives in the data-dependent-while covered fragment `IsCoveredSWhile`. -/
def mpnCmpLowCT : LowCT :=
  .RWhileNz "ix" mpnCmpBody

/-- The run-time loop guard: **limbs remain** (`ix != 0`) **and not yet differed**
    (`df == 0`). The `xor`-difference flag `df` going nonzero is the MSB-first
    early exit; `ix` reaching `0` is operand exhaustion (all limbs equal). This
    is the `SEnvScalar → Bool` predicate `scalarWhileTrips` reads to fix the
    data-dependent trip count. -/
def mpnCmpGuard : SEnvScalar → Bool :=
  fun e =>
    decide ((envReadU64 e "ix").getD 0 ≠ 0) && decide ((envReadU64 e "df").getD 0 = 0)

/-! ## 2. Coverage — the structural proofs

The per-limb body is straight-line covered (`IsCoveredS`); the whole kernel is a
data-dependent `while` over that straight-line body (`IsCoveredSWhile`, via the
`IsCoveredSCtl` embedding `ofStraight`). -/

/-- `df := ai ^ bi` is source-clean: both operands are non-`__sx` source names. -/
theorem dfClean : srcClean (SExpr.SXor (.SVar "ai") (.SVar "bi")) :=
  ⟨not_isTmp_short "ai" (by decide), not_isTmp_short "bi" (by decide)⟩

/-- `rs := ai - bi` is source-clean. -/
theorem rsClean : srcClean (SExpr.SSub (.SVar "ai") (.SVar "bi")) :=
  ⟨not_isTmp_short "ai" (by decide), not_isTmp_short "bi" (by decide)⟩

/-- `ix := ix - 1` is source-clean: `ix` is a non-`__sx` source name and `1 < 2^64`. -/
theorem ixClean : srcClean (SExpr.SSub (.SVar "ix") (.SLit 1)) :=
  ⟨not_isTmp_short "ix" (by decide), by norm_num [srcClean]⟩

/-- The `mpn_cmp` limb-scan step is straight-line covered (`IsCoveredS`): an
    `RSeq` of two dynamic-index loads and three source-clean scalar-`SExpr`
    assignments. -/
theorem mpnCmpBody_coveredS : IsCoveredS mpnCmpBody :=
  .rSeq (.rArrLoad ⟨"ai", .TU64⟩ ⟨"a", .TBytes 32⟩ "ix")
    (.rSeq (.rArrLoad ⟨"bi", .TU64⟩ ⟨"b", .TBytes 32⟩ "ix")
      (.rSeq (.rScalarSetExpr "df" _ dfClean)
        (.rSeq (.rScalarSetExpr "rs" _ rsClean)
          (.rScalarSetExpr "ix" _ ixClean))))

/-- The limb-scan step is control-covered (`IsCoveredSCtl`) as a straight-line
    body — the exact shape `rWhileNz_whole_denote` consumes as its loop body. -/
theorem mpnCmpBody_coveredSCtl : IsCoveredSCtl mpnCmpBody :=
  .ofStraight mpnCmpBody_coveredS

/-- **The whole `mpn_cmp` scan is data-dependent-`while` covered**
    (`IsCoveredSWhile`): an `RWhileNz` over the straight-line covered limb step.
    This is the fact that feeds the whole-program `RWhileNz`
    denote. -/
theorem mpnCmp_coveredSWhile : IsCoveredSWhile mpnCmpLowCT :=
  .rWhileNz mpnCmpBody_coveredSCtl

/-! ## 3. Concrete argument context — the front fires -/

/-- Argument context: the limb index `ix` (`.sword 64`) and the two operand
    arrays `a`/`b` (`.TBytes 32` → `.memref 4`, 4 saturated limbs). -/
def mpnCmpArgCtx : Ctx := [.sword 64, .memref 4, .memref 4]

/-- Name resolver binding `ix`/`a`/`b` to the three arguments. -/
def mpnCmpArgVM : VarMap mpnCmpArgCtx where
  lookup := fun s =>
    if s = "ix" then some ⟨.sword 64, .here⟩
    else if s = "a" then some ⟨.memref 4, .there .here⟩
    else if s = "b" then some ⟨.memref 4, .there (.there .here)⟩
    else none

/-- **The covered front accepts the whole `mpn_cmp` `RWhileNz` node.** The
    context-plumbing `RWhileNz` arm gates on the guard `ix` being a bound scalar
    (it is) and the loop body front-compiling (it does — the two dynamic-index
    loads resolve `a`/`b`/`ix`, and the three scalar-`SExpr` assignments lower),
    then hands the body off to the downstream back-edge emitter. -/
theorem mpnCmp_front_fires :
    (translateDialectControlTop mpnCmpArgVM mpnCmpLowCT).isSome := by
  native_decide

/-- **The trip-unrolled loop region descends through the front.** The `3`-fold copy of
    the limb step — the loop region run for `3` trips — descends through
    `loopWhileD` (the twin of the counted `loopRForD` unroll), the witness that
    the data-dependent scan region, run for any concrete trip count, is exactly
    that many sequenced body descents. -/
theorem mpnCmp_region_descends :
    (loopWhileD (translateBody := fun vm' => translateDialectControl vm' mpnCmpBody)
      mpnCmpArgVM 3).isSome := by
  native_decide

/-! ## 4. THE DELIVERABLE — the whole-program `RWhileNz` denote

For the guard-driven `mpn_cmp` scan that terminates within `fuel` (the explicit
termination hypothesis — the operand is finite, so the guard goes false within
`n` limbs), the front descent unrolled to the trip count read off the run
(`scalarWhileTrips … fuel`) denotes exactly the guard-driven `while` semantics
(`semScalarWhile`). Direct image of the `RWhileNz` waist homomorphism
`rWhileNz_whole_denote` at `mpnCmpBody`, discharged by the straight-line
coverage. The per-limb sign carrier is the arithmetic waist; the `{-1,0,+1}`
projection is the external libgmp `__gmpn_cmp` KAT. -/

/-- **Whole-program machine denote of the MSB-first early-exit `mpn_cmp` scan.**
    For any run-time guard predicate and fuel, context/valuation/env consistent
    triple on which the trip-unrolled front region descends and the guard-driven
    `while` waist terminates, the descended dialect-`Com` prefix denotes exactly
    the guard-driven `mpn_cmp` scan semantics (per-tail continuation). The trip
    count is data-dependent (the MSB-first early exit), so the denote is banked
    per-run at the trip count `scalarWhileTrips … fuel` read off the run. -/
theorem mpnCmpCovered_denote (guard : SEnvScalar → Bool) (fuel : Nat)
    {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env env' : SEnvScalar) (o : DTransOut Γ)
    (hc : ConsistentS vm V env)
    (htr : loopWhileD (translateBody := fun vm' => translateDialectControl vm' mpnCmpBody)
      vm (scalarWhileTrips (fun e => semScalar mpnCmpBody e) guard fuel env) = some o)
    (hrun : semScalarWhile (fun e => semScalar mpnCmpBody e) guard fuel env = some env') :
    ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
      ConsistentS o.vm V' env' ∧
      ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
        ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' :=
  rWhileNz_whole_denote mpnCmpBody_coveredSCtl guard fuel vm V env env' o hc htr hrun

/-- The deliverable, specialised to the natural `mpn_cmp` guard `mpnCmpGuard`
    ("limbs remain and not yet differed"). Records that the data-dependent
    early-exit guard the kernel actually runs feeds the whole-program denote. -/
theorem mpnCmpCovered_denote_guard (fuel : Nat)
    {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env env' : SEnvScalar) (o : DTransOut Γ)
    (hc : ConsistentS vm V env)
    (htr : loopWhileD (translateBody := fun vm' => translateDialectControl vm' mpnCmpBody)
      vm (scalarWhileTrips (fun e => semScalar mpnCmpBody e) mpnCmpGuard fuel env) = some o)
    (hrun : semScalarWhile (fun e => semScalar mpnCmpBody e) mpnCmpGuard fuel env = some env') :
    ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
      ConsistentS o.vm V' env' ∧
      ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
        ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' :=
  mpnCmpCovered_denote mpnCmpGuard fuel vm V env env' o hc htr hrun

/-! ## 5. Axiom audit -/

#print axioms mpnCmp_coveredSWhile
#print axioms mpnCmp_front_fires
#print axioms mpnCmp_region_descends
#print axioms mpnCmpCovered_denote

end CatCrypt.Crypto.SecureCompilation.VIR.MpnCmpCovered
