/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhileDenote

/-!
# ML-DSA `ExpandA` (`rej_uniform`) rejection sampler as a data-dependent `RWhileNz` whole-program denote

ML-DSA-65's matrix expansion (`ExpandA`, PQClean `ml-dsa-65/clean` `poly.c`
`rej_uniform`) rejection-samples uniform-mod-`q` coefficients from a SHAKE128 XOF
stream: read a 23-bit candidate `t = (b0 | b1<<8 | b2<<16) & 0x7FFFFF` from the
3-byte window, accept it iff `< q = 8380417`, advance the byte cursor `pos += 3`,
and repeat **until the output polynomial is full**. The number of windows is
decided at run time by how many candidates land below `q`, so this is a
*data-dependent* loop — not a fixed unroll and not a counted `RFor`. The
termination criterion (buffer full) is the `while (name != 0)` shape `RWhileNz`
models.

This re-sources that loop from a high-level `LowCT` term through the **canonical
front**, using the `RWhileNz` waist denote landed in
`TranslateDialectWhileDenote` (`rWhileNz_whole_denote` / `IsCoveredSWhile` /
`semScalarWhile`). It is the ML-DSA twin of the ML-KEM re-sourcing
`RejUniformCovered` (both are the `rej_uniform` control structure; ML-DSA reads a
23-bit candidate from a 3-byte window vs ML-KEM's 12-bit candidate) and shares
the same coverage / `isSome` / whole-program-denote recipe. The owned byte-exact
counterpart is `MLDSA.SamplerEmit` (`rejUniWindowBody` / `uniGuard`).

## The source term

`IsCoveredSCtl` (the body fragment the `RWhileNz` waist consumes) has no `RSeq`
over control, so a data-dependent loop body must be a *single* `RIfNz`/`RFor`/
straight-line node. We therefore model one `rej_uniform` window as an `RIfNz` on
the public accept flag `lt = (cand < q)` whose **both** branches advance the
cursor and read the next candidate — accept additionally stores the coefficient.
This is faithful to the sampler: every window either accepts-and-advances or
rejects-and-advances; the loop-carried candidate `cand` and accept flag `lt` are
refreshed each trip. The whole is wrapped in `RWhileNz "remaining"`, the
buffer-not-full guard.

* `rej_extract_cand` — opaque leaf: squeeze/extract the next 23-bit candidate from
  the (public) SHAKE128 byte stream at the cursor.
* `rej_lt_q` — opaque leaf: the public `< q` comparison, producing the accept flag.
* `rej_store` — opaque leaf: store an accepted coefficient into the output.
* `rej_advance` — opaque leaf: advance the byte cursor (`pos += 3`).

The candidate stream / hash squeeze and the arithmetic are **opaque leaves**
(their FIPS-204 correctness is the separate byte-KAT obligation, carried by the
owned-emit kernel `MLDSA.SamplerEmit`); what is banked here is the descent
of the **rejection control structure** — the data-dependent `while` — through the
canonical front, with a whole-program machine denote.

## CT note — the guard and the branch are PUBLIC

`ExpandA` expands the matrix `A` from the **public** seed `ρ`, so the XOF stream,
every `cand < q` decision, and the buffer-full guard are public by construction
(FIPS-204 §Algorithm 7). The `RWhileNz` guard `remaining` and the `RIfNz` flag
`lt` therefore leak nothing secret: this is the `RejectLoop.lean` public-guard
discipline (#460). A *secret*-dependent loop guard or accept branch would be a CT
violation (rejected by the `LowCT` `isCT` check); `ExpandA`'s `rej_uniform` is
admitted (it is the fully-public sampler — unlike `ExpandS`'s `rej_eta`, which
expands the secret vectors and only leaks the public rejection *count*). The
buffer index is a public counter, not a secret address.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.MLDSA.SamplerCovered

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

/-! ## 1. The high-level source: `rej_uniform` as a data-dependent `while` -/

/-- The (public) SHAKE128 XOF byte-stream / output bundle tower type — a byte
    buffer (rate-168 SHAKE128 block, ML-DSA `ExpandA`). -/
def bundleTy : TowerType := .TBytes 168

/-- A located byte-bundle slot (`buf`, `out`, `cand`). -/
def loc (n : String) : Located := { locVar := n, locSrc := bundleTy }

/-- A located 64-bit scalar slot (`pos` cursor, `lt` accept flag). -/
def locS (n : String) : Located := { locVar := n, locSrc := .TU64 }

/-- Advance the byte cursor (`pos += 3`) and read the next 23-bit candidate,
    recomputing the public accept flag `lt = (cand < q)`. Straight-line
    (`IsCoveredS`): an `RSeq` of the advance, extract, and compare leaves. Both
    `RWhileNz`-body branches share this tail — every window advances, whether the
    candidate is accepted or rejected. -/
def rejAdvanceExtract : LowCT :=
  .RSeq (.RCall "rej_advance" (locS "pos") [locS "pos"])
    (.RSeq (.RCall "rej_extract_cand" (loc "cand") [loc "buf", locS "pos"])
           (.RCall "rej_lt_q" (locS "lt") [loc "cand"]))

/-- The **accept** branch: store the accepted coefficient into the output, then
    advance + read the next candidate. Straight-line (`IsCoveredS`). -/
def acceptBranch : LowCT :=
  .RSeq (.RCall "rej_store" (loc "out") [loc "out", loc "cand"]) rejAdvanceExtract

/-- The `rej_uniform` **window body**: branch on the public accept flag `lt`. The
    accept branch stores the coefficient; both branches advance the cursor and
    read the next candidate. A single `RIfNz`, so it lives in the denote-carrying
    covered fragment `IsCoveredSCtl` (which has no `RSeq`-over-control — the
    advance/extract tail is folded into the branches). -/
def rejBody : LowCT :=
  .RIfNz "lt" acceptBranch rejAdvanceExtract

/-- **The whole `rej_uniform` rejection sampler as a data-dependent loop.**
    `RWhileNz "remaining"` — iterate the window body while the output polynomial is
    not full (`remaining != 0`). The trip count is fixed at run time by the public
    `< q` decisions, exactly the terminating guarded-loop shape `RWhileNz` models. -/
def rejUniformLowCT : LowCT :=
  .RWhileNz "remaining" rejBody

/-! ## 2. Coverage — the central structural proofs -/

/-- The advance-and-extract tail is straight-line covered. -/
theorem rejAdvanceExtract_coveredS : IsCoveredS rejAdvanceExtract :=
  .rSeq (.rCall "rej_advance" (locS "pos") [locS "pos"])
    (.rSeq (.rCall "rej_extract_cand" (loc "cand") [loc "buf", locS "pos"])
           (.rCall "rej_lt_q" (locS "lt") [loc "cand"]))

/-- The accept branch is straight-line covered. -/
theorem acceptBranch_coveredS : IsCoveredS acceptBranch :=
  .rSeq (.rCall "rej_store" (loc "out") [loc "out", loc "cand"]) rejAdvanceExtract_coveredS

/-- **The window body is Stage-2 covered** (`IsCoveredSCtl`): an `RIfNz` over two
    straight-line branches. This is the central fact — it feeds the
    `RWhileNz` whole-program denote (`rWhileNz_whole_denote`). -/
theorem rejBody_covered : IsCoveredSCtl rejBody :=
  .rIfNz (.ofStraight acceptBranch_coveredS) (.ofStraight rejAdvanceExtract_coveredS)

/-- **The whole rejection sampler is while-covered** (`IsCoveredSWhile`): an
    `RWhileNz` over the covered window body. Not expressible in `IsCoveredSCtl`
    (which has no `RWhileNz`) — this is exactly the data-dependent-loop arm. -/
theorem rejUniform_coveredWhile : IsCoveredSWhile rejUniformLowCT :=
  .rWhileNz rejBody_covered

/-! ## 3. Concrete argument context — the front fires -/

/-- The argument context: the byte bundles `buf`/`out`/`cand` and the 64-bit
    scalars `pos` (cursor), `lt` (accept flag), `remaining` (buffer-not-full
    guard). -/
def rejArgVM :=
  ((((((VarMap.empty.bind (t := encodeTy bundleTy) "buf").bind
      (t := encodeTy bundleTy) "out").bind
      (t := encodeTy bundleTy) "cand").bind
      (t := .sword 64) "pos").bind
      (t := .sword 64) "lt").bind
      (t := .sword 64) "remaining")

/-- **The canonical front fires on the whole `rej_uniform` rejection loop.** The
    `RWhileNz` arm gates on the guard `remaining` being a bound scalar and on the
    body front-compiling; the `RIfNz` on the bound accept flag `lt`; the leaf
    calls resolve their arguments. The data-dependent back-edge is emitted
    downstream (the `RejectLoop` / `rolledWhileNz` owned loop). -/
theorem rejUniform_front_fires :
    (translateDialectControl rejArgVM rejUniformLowCT).isSome := by
  native_decide

/-! ## 4. THE DELIVERABLE — the whole-program `RWhileNz` denote

For the `rej_uniform` rejection loop that terminates within `fuel` (the buffer is
finite — the explicit termination hypothesis), the canonical front unrolled to the
run's actual trip count denotes exactly the guard-driven do-while semantics
`semScalarWhile`. Direct image of the `RWhileNz` waist homomorphism
`rWhileNz_whole_denote` at `rejBody`, discharged by structural coverage
(`rejBody_covered`). The candidate stream / `< q` / store / advance are opaque
leaves; their FIPS-204 correctness is the separate byte-KAT obligation. -/

/-- **Whole-program machine denote of the ML-DSA `ExpandA` `rej_uniform`
    rejection sampler.** For any context/valuation/env consistent triple on which
    the front (unrolled to the data-dependent trip count `scalarWhileTrips`)
    descends and the guard-driven do-while `semScalarWhile` halts within `fuel`,
    the descended dialect-`Com` prefix denotes exactly the loop's guard-driven
    semantics (per-tail continuation). `guard` is the buffer-not-full predicate
    (`remaining != 0`); the body preservation is `translateDialectControl_denote_ctl`
    on `rejBody_covered`. -/
theorem rejUniformCovered_denote
    (guard : SEnvScalar → Bool) (fuel : Nat)
    {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env env' : SEnvScalar) (o : DTransOut Γ)
    (hc : ConsistentS vm V env)
    (htr : loopWhileD (translateBody := fun vm' => translateDialectControl vm' rejBody)
      vm (scalarWhileTrips (fun e => semScalar rejBody e) guard fuel env) = some o)
    (hrun : semScalarWhile (fun e => semScalar rejBody e) guard fuel env = some env') :
    ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
      ConsistentS o.vm V' env' ∧
      ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
        ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' :=
  rWhileNz_whole_denote rejBody_covered guard fuel vm V env env' o hc htr hrun

/-! ## 5. Axiom audit -/

#print axioms rejBody_covered
#print axioms rejUniform_coveredWhile
#print axioms rejUniform_front_fires
#print axioms rejUniformCovered_denote

end CatCrypt.Crypto.MLDSA.SamplerCovered
