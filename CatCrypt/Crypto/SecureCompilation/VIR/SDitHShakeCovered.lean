/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenoteSeqExt
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenoteSeqExt

/-!
# SDitH SHAKE128 sponge whole-program denote through the covered `RSeq`-of-control fragment

SDitH's commitment / PRG layer is SHAKE128. Its deployed owned leaf
(`SDitH/ShakeEmit.lean`, `Lsdith_shake128_into`) is a single-block sponge —
zero the 25-lane state, absorb the message rate block, apply the FIPS-202
`pad10*1` domain pad (SHAKE128 `0x1f`/`0x80`), permute with Keccak-f[1600], and
squeeze the digest rate block. That is exactly the FIPS-202 sponge shape
`absorb ; pad ; squeeze`: an absorb loop over the input rate blocks, the domain
pad, and a squeeze loop over the output rate blocks. Each phase is a counted loop
(`RFor`) over the opaque Keccak-f[1600] permutation, or a straight-line pad leaf,
and the three phases are sequenced with `RSeq`.

This re-sources the SDitH SHAKE128 sponge from a high-level `LowCT` term
(`sdithShakeLowCT = RSeq absorbLoop (RSeq padPhase squeezeLoop)`) through the
**existing covered-fragment front** — the same recipe as
`Shake256Covered.shake256Covered_denote` — and banks the whole-program machine
denote homomorphism for it. It strengthens the orchestration-front descent of the
same sponge (`ShakeEmit.shakeCom` / `ShakeDenote.shakeCom_denote`, a
`buildOrchComP` schedule with a leaf-oracle-parametric `Com.denote`) to a
high-level `RSeq`-of-control descent with a whole-program denote through the
canonical `translateDialectControl` front.

Keccak-f[1600] is an **opaque leaf** (`RCall "keccakf1600"`) — its permutation
correctness is the separate FIPS-202 KAT obligation (`bench/keccak_compare/`,
`sdith_kernel.s` SHAKE128 vs OpenSSL `EVP_shake128`), exactly as
`x25519_ladder_iter` and the `fe25519` field leaves are opaque in the exemplar.
The absorb rate-XOR and the domain pad are likewise opaque leaves; what is banked
here is the descent of the sponge **control structure** (the two counted loops
sequenced with the pad) through the canonical front, with a whole-program denote.

## What is banked

* `sdithShakeLowCT` — the sponge as `RSeq absorbLoop (RSeq padPhase squeezeLoop)`.
* `sdithShake_coveredSeq : IsCoveredSCtlSeq sdithShakeLowCT` — the structural
  coverage proof (an `RSeq` of two covered `RFor` loops and a straight-line pad
  leaf).
* `sdithShake_front_fires` — the covered front fires on the whole sponge
  (`native_decide`).
* `sdithShakeCovered_denote` — **the deliverable**: the whole-program machine
  denote of the sponge through the canonical front, via `transCtlSeq_denote_seq`
  and the `sdithShake_front_eq` bridge (`transCtlSeq = translateDialectControl`
  on this `RSeq`-of-leaves term).

## SHAKE128 block counts

SDitH SHAKE128 hashes a fixed single 32-byte block into a 32-byte digest: the
absorb block count (`⌈inlen / rate⌉` with `rate = 168`) and the squeeze block
count (`⌈outlen / rate⌉`) are both **1** — static, so `RFor` suffices, no
`RWhileNz` is needed. The `NSHARE = 8` commitment fold `acc ← SHAKE128(acc)`
(`ShakeEmit.sdith_commit_fold`) sequences eight of these single-block sponges
— a further static counted-loop layer, a separate obligation. A variable-length
streaming SHAKE128 XOF (runtime `inlen`/`outlen`) would need `RWhileNz`, the
data-dependent-count arm; that is not the SDitH usage here.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.SDitHShakeCovered

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

/-! ## 1. The high-level source: SHAKE128 as `absorb ; pad ; squeeze` -/

/-- Tower type of the 200-byte (25-lane) Keccak state bundle. -/
def bundleTy : TowerType := .TBytes 200

/-- A located slot of the state-bundle tower type. -/
def loc (n : String) : Located := { locVar := n, locSrc := bundleTy }

/-- Absorb block count for the SDitH SHAKE128 KAT input (single 32-byte block,
    `< rate = 168`, so `⌈inlen / rate⌉ = 1`, static). -/
def absorbBlocks : Nat := 1

/-- Squeeze block count for the SDitH SHAKE128 KAT output (single 32-byte digest,
    `⌈outlen / rate⌉ = 1`, static). -/
def squeezeBlocks : Nat := 1

/-- One absorb iteration: XOR the next input rate block into the state
    (`sdith_shake128_xor_block` opaque leaf), then permute in place
    (`keccakf1600` opaque leaf). Straight-line (`IsCoveredS`): an `RSeq` of two
    `RCall`s threading the state bundle. -/
def absorbBlockBody : LowCT :=
  .RSeq (.RCall "sdith_shake128_xor_block" (loc "state") [loc "state", loc "inp"])
        (.RCall "keccakf1600" (loc "state") [loc "state"])

/-- **The absorb phase**: `RFor` over the input rate blocks — a counted loop over
    the opaque XOR-in + permute leaf. A single `RFor`, so it lives in the
    denote-carrying covered fragment `IsCoveredSCtl`. -/
def absorbLoop : LowCT :=
  .RFor "i" absorbBlocks absorbBlockBody

/-- **The pad phase**: the FIPS-202 `pad10*1` domain pad (SHAKE128 `0x1f` suffix
    + `0x80` high bit), a straight-line opaque leaf on the state bundle. -/
def padPhase : LowCT :=
  .RCall "sdith_shake128_pad" (loc "state") [loc "state"]

/-- One squeeze iteration: permute in place (`keccakf1600` opaque leaf), then
    extract the next output rate block from the state
    (`sdith_shake128_extract_block` opaque leaf). Straight-line (`IsCoveredS`): an
    `RSeq` of two `RCall`s. -/
def squeezeBlockBody : LowCT :=
  .RSeq (.RCall "keccakf1600" (loc "state") [loc "state"])
        (.RCall "sdith_shake128_extract_block" (loc "out") [loc "state", loc "out"])

/-- **The squeeze phase**: `RFor` over the output rate blocks — a counted loop
    over the opaque permute + extract leaf. -/
def squeezeLoop : LowCT :=
  .RFor "k" squeezeBlocks squeezeBlockBody

/-- **The full SDitH SHAKE128 sponge as a multi-phase kernel:** the absorb loop
    *sequenced* with the pad and the squeeze loop — the top-level
    `RSeq (RFor …) (RSeq (RCall …) (RFor …))` shape. -/
def sdithShakeLowCT : LowCT :=
  .RSeq absorbLoop (.RSeq padPhase squeezeLoop)

/-! ## 2. Coverage — the structural proofs -/

/-- The absorb-block body is straight-line covered. -/
theorem absorbBlockBody_coveredS : IsCoveredS absorbBlockBody :=
  .rSeq (.rCall "sdith_shake128_xor_block" (loc "state") [loc "state", loc "inp"])
        (.rCall "keccakf1600" (loc "state") [loc "state"])

/-- The absorb loop is Stage-2 covered (`IsCoveredSCtl`): a bounded `RFor` over
    the straight-line absorb-block body. -/
theorem absorbLoop_covered : IsCoveredSCtl absorbLoop :=
  .rFor (.ofStraight absorbBlockBody_coveredS)

/-- The pad phase is straight-line covered. -/
theorem padPhase_coveredS : IsCoveredS padPhase :=
  .rCall "sdith_shake128_pad" (loc "state") [loc "state"]

/-- The squeeze-block body is straight-line covered. -/
theorem squeezeBlockBody_coveredS : IsCoveredS squeezeBlockBody :=
  .rSeq (.rCall "keccakf1600" (loc "state") [loc "state"])
        (.rCall "sdith_shake128_extract_block" (loc "out") [loc "state", loc "out"])

/-- The squeeze loop is Stage-2 covered (`IsCoveredSCtl`). -/
theorem squeezeLoop_covered : IsCoveredSCtl squeezeLoop :=
  .rFor (.ofStraight squeezeBlockBody_coveredS)

/-- **The full SDitH SHAKE128 sponge is control-sequencing covered**
    (`IsCoveredSCtlSeq`): the absorb loop sequenced with the pad leaf and the
    squeeze loop. Not expressible in `IsCoveredSCtl` (which has no
    `RSeq`-over-control) — this is exactly the `RSeq`-of-control increment. -/
theorem sdithShake_coveredSeq : IsCoveredSCtlSeq sdithShakeLowCT :=
  .rSeq (.ofCtl absorbLoop_covered)
    (.rSeq (.ofCtl (.ofStraight padPhase_coveredS)) (.ofCtl squeezeLoop_covered))

/-! ## 3. Concrete argument context — the front fires -/

/-- Three-argument context: the state, input, and output bundles. -/
def spongeArgCtx : Ctx :=
  [encodeTy bundleTy, encodeTy bundleTy, encodeTy bundleTy]

/-- Name resolver binding `state`/`inp`/`out` to the three bundle arguments. -/
def spongeArgVM : VarMap spongeArgCtx where
  lookup := fun s =>
    if s = "state" then some ⟨encodeTy bundleTy, .here⟩
    else if s = "inp" then some ⟨encodeTy bundleTy, .there .here⟩
    else if s = "out" then some ⟨encodeTy bundleTy, .there (.there .here)⟩
    else none

/-- **The covered front fires on the whole SDitH SHAKE128 sponge.** The two
    bounded `RFor` loops unroll through `loopRForD`, the pad leaf and
    permute leaves resolve their state/input/output arguments, the `RSeq` spine
    composes the phase prefixes, and the top-level terminator closes. -/
theorem sdithShake_front_fires :
    (translateDialectControlTop spongeArgVM sdithShakeLowCT).isSome := by
  native_decide

/-! ## 4. `transCtlSeq` coincides with the canonical front on this term

The control-sequencing front `transCtlSeq` folds `translateDialectControl` along
the `RSeq` spine with `ComCont.comp`; the canonical `translateDialectControl`
does the *same* (its `RSeq` arm recurses into itself). On leaves (`RFor`, `RCall`)
`transCtlSeq` delegates to `translateDialectControl` through its wildcard. So on
this pure `RSeq`-of-leaves term the two fronts coincide, letting the
canonical-front translation hypothesis feed the control-sequencing homomorphism
`transCtlSeq_denote_seq` directly. -/

/-- `RSeq` congruence for the two fronts: if both children agree pointwise, the
    sequence agrees. Both fronts share the identical `RSeq` arm (recurse into
    self, compose with `ComCont.comp`), so this is a one-layer unfold. -/
theorem transCtlSeq_rseq_congr {c₁ c₂ : LowCT}
    (h1 : ∀ {Δ : Ctx} (w : VarMap Δ), transCtlSeq w c₁ = translateDialectControl w c₁)
    (h2 : ∀ {Δ : Ctx} (w : VarMap Δ), transCtlSeq w c₂ = translateDialectControl w c₂)
    {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm (.RSeq c₁ c₂) = translateDialectControl vm (.RSeq c₁ c₂) := by
  simp only [transCtlSeq, translateDialectControl, h1, h2]
  rfl

/-- On the inner `RSeq padPhase squeezeLoop` (two leaves — an `RCall` and an
    `RFor`), `transCtlSeq` coincides with the canonical front. -/
theorem inner_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm (.RSeq padPhase squeezeLoop)
      = translateDialectControl vm (.RSeq padPhase squeezeLoop) :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => rfl) vm

/-- **The full sponge front-agreement.** `transCtlSeq` coincides with the
    canonical `translateDialectControl` on `sdithShakeLowCT`: the outer `RSeq`
    uses the congruence with the leaf `absorbLoop` (`RFor`, agrees by the
    `transCtlSeq` wildcard) and the inner sequence (`inner_front_eq`). -/
theorem sdithShake_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm sdithShakeLowCT = translateDialectControl vm sdithShakeLowCT :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => inner_front_eq _) vm

/-! ## 5. THE DELIVERABLE — the whole-program denote homomorphism

For the SDitH SHAKE128 sponge, the descended `Com catCryptDialect` prefix denotes
exactly the kernel's `semScalar` waist — the multi-phase whole-program denote
through the canonical front, banked via the control-sequencing homomorphism
`transCtlSeq_denote_seq` (which equals `translateDialectControl` on this
`RSeq`-of-leaves term by `sdithShake_front_eq`, so the canonical-front translation
hypothesis feeds it directly). Keccak-f[1600] (and the absorb-XOR / pad / extract)
are opaque leaves; their FIPS-202 correctness is the separate KAT obligation. -/

/-- **Whole-program machine denote of the SDitH SHAKE128 sponge** (absorb loop `;`
    pad `;` squeeze loop). For any context/valuation/env consistent triple on
    which the canonical front fires and the `semScalar` waist succeeds, the
    descended dialect-`Com` prefix denotes exactly the sponge's `semScalar`
    semantics (per-tail continuation). -/
theorem sdithShakeCovered_denote :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm sdithShakeLowCT = some o →
      semScalar sdithShakeLowCT env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com : Com catCryptDialect Γ t,
            o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro Γ vm V env env' o hc htr hsem
  rw [← sdithShake_front_eq vm] at htr
  exact transCtlSeq_denote_seq sdithShake_coveredSeq vm V env env' o hc htr hsem

/-! ## 6. Axiom audit -/

#print axioms sdithShake_coveredSeq
#print axioms sdithShake_front_fires
#print axioms sdithShake_front_eq
#print axioms sdithShakeCovered_denote

end CatCrypt.Crypto.SecureCompilation.VIR.SDitHShakeCovered
