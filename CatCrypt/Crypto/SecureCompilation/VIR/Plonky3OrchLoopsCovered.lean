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
public meta import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhileDenote
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectWhileDenote

/-!
# Plonky3 whole-prover orchestration loops through the covered `RSeq`-of-control fragment

`Plonky3OrchLoopsEmit` emits the whole-prover orchestration LOOPS — the
Merkle leaf level, the Merkle compress level, the FRI fold chain, the FRI query
loop, and the proof-of-work grind — as **owned-backend `loopLcmd` back-edges**
whose bodies `Lcall` the emitted field leaves. That module is the byte-level
emit: it pins the rendered `.L:/cmp/jne` control-flow shape and the composed
`.s`. What it does NOT carry is a **high-level-source descent with a
whole-program machine denote** — the deployed driver bodies there are
`buildOrchLoop`-generated `Lcmd`s, sourced one level below the canonical
`LowCT → Com catCryptDialect` front.

This module re-sources the *counted* orchestration loops from a high-level `LowCT`
term through the **existing covered-fragment front** — no new front — and banks the
whole-program denote homomorphism, the same recipe as
`MayoSolveCovered.mayoSolveCovered_denote` and
`Shake256Covered.shake256Covered_denote`.

The four **static-count** orchestration loops (the Fibonacci STARK shape
`bench_prove_emitted_a7.c` drives: domain 32, 8 queries) are each an `RFor` over
an opaque per-iteration field-leaf `RCall`, and the four are sequenced with
`RSeq`:

```
merkleLeaf (RFor 32) ; merkleCompress (RFor 16) ; friFold (RFor 32) ; friQuery (RFor 8)
```

This is exactly the shape the canonical front accepts after the `RSeq`-of-control
increment: `translateDialectControl` closes under `RSeq`-sequencing of control
blocks, so the whole counted-loop orchestration descends through the canonical
front and carries a **whole-program machine denote**
(`plonky3OrchLoopsCovered_denote`).

## Opaque leaves — the per-iteration field work, exactly the exemplar tier

Each per-iteration body is an **opaque leaf** (`RCall`), exactly as `keccakf1600`
is opaque in `Shake256Covered` and `x25519_ladder_iter` in the scalar-mult
exemplar. What is banked here is the descent of the orchestration's **control
structure** — the four static-count loops sequenced — through the canonical
front, with a whole-program denote. The per-iteration field arithmetic (the
Poseidon2 hash_leaf / compress, the BabyBear `fri_fold`) is the separate byte-KAT
obligation on the emitted leaves (`plonky3_compare`,
`Plonky3OrchLoopsEmit`'s per-kernel KATs), just as Keccak-f's permutation
correctness is the FIPS-202 KAT.

## The proof-of-work grind — the data-dependent `RWhileNz` arm

The four commit / fold / query loops are static-count (domain size 32, query
count 8 are compile-time), so `RFor` suffices. The **proof-of-work grind** is
different: it increments a nonce and re-hashes until the digest's low bits clear —
a **data-dependent, public** trip count (constant-time is preserved; only the
public grind bound bounds it). A runtime-count loop is an `RWhileNz`, which lives
OUTSIDE the static-count `RFor`+`RSeq` covered fragment. It is banked separately
here (`powGrindCovered_denote`) through the fueled while-region denote
`rWhileNz_whole_denote` (the `RWhileNz` whole-program waist denote): for a
guard-driven grind that terminates within `fuel`, the front descent unrolled to
the run's actual trip count denotes the guard-driven while semantics, over the
covered opaque hash-step body.

## What is banked

* `plonky3OrchLoopsLowCT` — the counted orchestration as
  `RSeq merkleLeaf (RSeq merkleCompress (RSeq friFold friQuery))`.
* `plonky3OrchLoops_coveredSeq : IsCoveredSCtlSeq plonky3OrchLoopsLowCT` — the
  structural coverage proof (an `RSeq` spine of four covered `RFor` phases over
  opaque leaves).
* `plonky3OrchLoops_front_fires` — the covered front fires on the whole counted
  orchestration (`native_decide`).
* `plonky3OrchLoopsCovered_denote` — **the deliverable**: the whole-program
  machine denote of the counted orchestration through the canonical front, via
  `transCtlSeq_denote_seq` and the `plonky3OrchLoops_front_eq` bridge.
* `powGrindCovered_denote` — the fueled whole-program denote of the PoW grind
  `RWhileNz`, via `rWhileNz_whole_denote`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3OrchLoopsCovered

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

/-! ## 0. Plonky3 Fibonacci-STARK orchestration parameters -/

/-- Merkle leaf level: 32 leaf hashes (domain size). -/
def pLeaves : Nat := 32
/-- Merkle compress level (widest): 16 nodes. -/
def pCompress : Nat := 16
/-- FRI fold layer (widest): m = 32 folds. -/
def pFold : Nat := 32
/-- FRI query loop: 8 queries. -/
def pQueries : Nat := 8

/-! ## 1. The high-level source: the counted orchestration as a phase sequence -/

/-- Tower type of a state bundle (row arrays, digest arrays, transcript). The
    per-iteration field work is opaque, so the concrete layout is the leaves' KAT
    concern, not the control descent's. -/
def bundleTy : TowerType := .TBytes 200

/-- A located slot of a state-bundle tower type. -/
def loc (n : String) : Located := { locVar := n, locSrc := bundleTy }

/-- One Merkle leaf iteration `L5[i] ← hash_leaf(mixed[i])` — an opaque per-leaf
    Poseidon2 leaf threading the leaf-digest array `L5`. -/
def merkleLeafStepBody : LowCT :=
  .RCall "plonky3_merkle_hash_leaf" (loc "L5") [loc "L5", loc "mixed"]

/-- **Phase 1 — Merkle leaf level:** `RFor` over the 32 leaves (domain size,
    static). A single `RFor`, so it lives in the denote-carrying covered fragment
    `IsCoveredSCtl`. -/
def merkleLeafLoop : LowCT :=
  .RFor "i" pLeaves merkleLeafStepBody

/-- One Merkle compress iteration `out[j] ← compress(L5[2j], L5[2j+1])` — an
    opaque Poseidon2-compress leaf threading the compressed-digest array `out`. -/
def merkleCompressStepBody : LowCT :=
  .RCall "plonky3_merkle_compress" (loc "out") [loc "out", loc "L5"]

/-- **Phase 2 — Merkle compress level (widest):** `RFor` over the 16 nodes
    (static). The compress-tree's inner descending levels (16→8→4→2→1) are the
    leaf's KAT concern; the widest level is the control descent here. -/
def merkleCompressLoop : LowCT :=
  .RFor "j" pCompress merkleCompressStepBody

/-- One FRI fold iteration `next[i] ← fri_fold(cur[i], cur[i+m], x, α)` — an opaque
    BabyBear fold leaf threading the folded-codeword array `next`. -/
def friFoldStepBody : LowCT :=
  .RCall "fri_fold" (loc "next") [loc "cur"]

/-- **Phase 3 — FRI fold layer (widest, m = 32):** `RFor` over the 32 folds
    (static). The FRI halving chain's inner descending layers are the leaf's KAT
    concern; the widest layer is the control descent here. -/
def friFoldLoop : LowCT :=
  .RFor "k" pFold friFoldStepBody

/-- One FRI query iteration: open a codeword + fold-layer position and check the
    Merkle auth path (a `compress` per path node) — an opaque leaf threading the
    per-query opening record `query`. -/
def friQueryStepBody : LowCT :=
  .RCall "plonky3_fri_query" (loc "query") [loc "query", loc "out", loc "cur"]

/-- **Phase 4 — FRI query loop:** `RFor` over the 8 queries (static). -/
def friQueryLoop : LowCT :=
  .RFor "q" pQueries friQueryStepBody

/-- **The full Plonky3 counted orchestration as a multi-phase kernel:** the Merkle
    leaf, Merkle compress, FRI fold, and FRI query phases *sequenced* — the
    top-level `RSeq (RFor …) (RSeq (RFor …) (RSeq (RFor …) (RFor …)))` shape. -/
def plonky3OrchLoopsLowCT : LowCT :=
  .RSeq merkleLeafLoop (.RSeq merkleCompressLoop (.RSeq friFoldLoop friQueryLoop))

/-! ## 2. Coverage — the central structural proofs -/

/-- The Merkle-leaf-step body is straight-line covered. -/
theorem merkleLeafStepBody_coveredS : IsCoveredS merkleLeafStepBody :=
  .rCall "plonky3_merkle_hash_leaf" (loc "L5") [loc "L5", loc "mixed"]

/-- The Merkle leaf loop is Stage-2 covered (`IsCoveredSCtl`): a bounded `RFor`
    over the straight-line leaf-hash step. -/
theorem merkleLeafLoop_covered : IsCoveredSCtl merkleLeafLoop :=
  .rFor (.ofStraight merkleLeafStepBody_coveredS)

/-- The Merkle-compress-step body is straight-line covered. -/
theorem merkleCompressStepBody_coveredS : IsCoveredS merkleCompressStepBody :=
  .rCall "plonky3_merkle_compress" (loc "out") [loc "out", loc "L5"]

/-- The Merkle compress loop is Stage-2 covered (`IsCoveredSCtl`). -/
theorem merkleCompressLoop_covered : IsCoveredSCtl merkleCompressLoop :=
  .rFor (.ofStraight merkleCompressStepBody_coveredS)

/-- The FRI-fold-step body is straight-line covered. -/
theorem friFoldStepBody_coveredS : IsCoveredS friFoldStepBody :=
  .rCall "fri_fold" (loc "next") [loc "cur"]

/-- The FRI fold loop is Stage-2 covered (`IsCoveredSCtl`). -/
theorem friFoldLoop_covered : IsCoveredSCtl friFoldLoop :=
  .rFor (.ofStraight friFoldStepBody_coveredS)

/-- The FRI-query-step body is straight-line covered. -/
theorem friQueryStepBody_coveredS : IsCoveredS friQueryStepBody :=
  .rCall "plonky3_fri_query" (loc "query") [loc "query", loc "out", loc "cur"]

/-- The FRI query loop is Stage-2 covered (`IsCoveredSCtl`). -/
theorem friQueryLoop_covered : IsCoveredSCtl friQueryLoop :=
  .rFor (.ofStraight friQueryStepBody_coveredS)

/-- **The full Plonky3 counted orchestration is control-sequencing covered**
    (`IsCoveredSCtlSeq`): the four counted phases sequenced. Not expressible in
    `IsCoveredSCtl` (which has no `RSeq`-over-control) — this is exactly the
    `RSeq`-of-control increment, a four-phase spine over opaque field leaves. -/
theorem plonky3OrchLoops_coveredSeq : IsCoveredSCtlSeq plonky3OrchLoopsLowCT :=
  .rSeq (.ofCtl merkleLeafLoop_covered)
    (.rSeq (.ofCtl merkleCompressLoop_covered)
      (.rSeq (.ofCtl friFoldLoop_covered) (.ofCtl friQueryLoop_covered)))

/-! ## 3. Concrete argument context — the front fires -/

/-- Five-argument context: the `L5`, `mixed`, `out`, `next`, `cur`, `query`
    bundles. -/
def orchArgCtx : Ctx :=
  [encodeTy bundleTy, encodeTy bundleTy, encodeTy bundleTy,
   encodeTy bundleTy, encodeTy bundleTy, encodeTy bundleTy]

/-- Name resolver binding `L5`/`mixed`/`out`/`next`/`cur`/`query` to the six bundle
    arguments. -/
def orchArgVM : VarMap orchArgCtx where
  lookup := fun s =>
    if s = "L5" then some ⟨encodeTy bundleTy, .here⟩
    else if s = "mixed" then some ⟨encodeTy bundleTy, .there .here⟩
    else if s = "out" then some ⟨encodeTy bundleTy, .there (.there .here)⟩
    else if s = "next" then some ⟨encodeTy bundleTy, .there (.there (.there .here))⟩
    else if s = "cur" then some ⟨encodeTy bundleTy, .there (.there (.there (.there .here)))⟩
    else if s = "query" then some ⟨encodeTy bundleTy, .there (.there (.there (.there (.there .here))))⟩
    else none

/-- **The covered front fires on the whole Plonky3 counted orchestration.** The
    four bounded `RFor` phases unroll through `loopRForD`, each opaque
    per-iteration field leaf resolves its bundle arguments, the `RSeq` spine
    composes the phase prefixes, and the top-level terminator closes. -/
theorem plonky3OrchLoops_front_fires :
    (translateDialectControlTop orchArgVM plonky3OrchLoopsLowCT).isSome := by
  native_decide

/-! ## 4. `transCtlSeq` coincides with the canonical front on this term -/

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

/-- On the innermost `RSeq friFoldLoop friQueryLoop` (two `RFor` leaves),
    `transCtlSeq` coincides with the canonical front. -/
theorem inner1_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm (.RSeq friFoldLoop friQueryLoop)
      = translateDialectControl vm (.RSeq friFoldLoop friQueryLoop) :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => rfl) vm

/-- On `RSeq merkleCompressLoop (RSeq friFoldLoop friQueryLoop)`, `transCtlSeq`
    coincides with the canonical front (leaf `RFor` + the inner sequence). -/
theorem inner2_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm (.RSeq merkleCompressLoop (.RSeq friFoldLoop friQueryLoop))
      = translateDialectControl vm (.RSeq merkleCompressLoop (.RSeq friFoldLoop friQueryLoop)) :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => inner1_front_eq _) vm

/-- **The full orchestration front-agreement.** `transCtlSeq` coincides with the
    canonical `translateDialectControl` on `plonky3OrchLoopsLowCT`: the outer
    `RSeq` uses the congruence with the leaf `merkleLeafLoop` (`RFor`, agrees by
    the `transCtlSeq` wildcard) and the inner two-phase sequence
    (`inner2_front_eq`). -/
theorem plonky3OrchLoops_front_eq {Γ : Ctx} (vm : VarMap Γ) :
    transCtlSeq vm plonky3OrchLoopsLowCT = translateDialectControl vm plonky3OrchLoopsLowCT :=
  transCtlSeq_rseq_congr (fun _ => rfl) (fun _ => inner2_front_eq _) vm

/-! ## 5. THE DELIVERABLE — the whole-program denote homomorphism

For the Plonky3 counted orchestration, the descended `Com catCryptDialect` prefix
denotes exactly the kernel's `semScalar` waist — the four-phase whole-program
denote through the canonical front, banked via the control-sequencing
homomorphism `transCtlSeq_denote_seq` (which equals `translateDialectControl` on
this `RSeq`-of-leaves term by `plonky3OrchLoops_front_eq`, so the canonical-front
translation hypothesis feeds it directly). The per-iteration field work
(Poseidon2 hash_leaf / compress, BabyBear fold, query auth-path) are opaque
leaves; their correctness is the separate byte-KAT obligation. -/

/-- **Whole-program machine denote of the Plonky3 counted orchestration**
    (Merkle leaf `;` Merkle compress `;` FRI fold `;` FRI query). For any
    context/valuation/env consistent triple on which the canonical front fires and
    the `semScalar` waist succeeds, the descended dialect-`Com` prefix denotes
    exactly the orchestration's `semScalar` semantics (per-tail continuation). -/
theorem plonky3OrchLoopsCovered_denote :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnvScalar) (o : DTransOut Γ),
      ConsistentS vm V env →
      translateDialectControl vm plonky3OrchLoopsLowCT = some o →
      semScalar plonky3OrchLoopsLowCT env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentS o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com : Com catCryptDialect Γ t,
            o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  intro Γ vm V env env' o hc htr hsem
  rw [← plonky3OrchLoops_front_eq vm] at htr
  exact transCtlSeq_denote_seq plonky3OrchLoops_coveredSeq vm V env env' o hc htr hsem

/-! ## 6. The proof-of-work grind — the data-dependent `RWhileNz` arm

The four commit / fold / query loops above are static-count, so `RFor` covers
them. The PoW grind's trip count is data-dependent (fixed at run time by when the
digest's low bits clear) but public, so it is an `RWhileNz` — outside the
static-count `RFor`+`RSeq` covered fragment. It is banked here through the fueled
while-region denote `rWhileNz_whole_denote`: for a guard-driven grind that halts
within `fuel`, the front descent unrolled to the run's actual trip count denotes
the guard-driven while semantics, over the covered opaque hash-step body. -/

/-- One PoW grind iteration: increment the nonce and re-hash (`hash(nonce)` whose
    low bits are then tested by the guard) — an opaque straight-line hash-step leaf
    threading the nonce/digest bundle. -/
def powGrindStepBody : LowCT :=
  .RCall "plonky3_pow_hash_step" (loc "nonce") [loc "nonce"]

/-- The PoW grind step body is straight-line covered. -/
theorem powGrindStepBody_coveredS : IsCoveredS powGrindStepBody :=
  .rCall "plonky3_pow_hash_step" (loc "nonce") [loc "nonce"]

/-- The PoW grind step body is Stage-2 covered (`IsCoveredSCtl`) — a straight-line
    body, the shape `rWhileNz_whole_denote` consumes. -/
theorem powGrindStepBody_coveredCtl : IsCoveredSCtl powGrindStepBody :=
  .ofStraight powGrindStepBody_coveredS

/-- **The PoW grind as a data-dependent `while`:** `RWhileNz` over the opaque
    hash-step body, gated on the (public) low-bit guard `nonce`. Outside the
    static-count covered fragment — the `RWhileNz` while-covered witness. -/
def powGrindWhile : LowCT :=
  .RWhileNz "nonce" powGrindStepBody

/-- The PoW grind `while` is while-covered (`IsCoveredSWhile`): an `RWhileNz` over
    the covered opaque hash-step body. -/
theorem powGrind_coveredWhile : IsCoveredSWhile powGrindWhile :=
  .rWhileNz powGrindStepBody_coveredCtl

/-- **Fueled whole-program denote of the PoW grind.** For a guard-driven grind
    over the opaque hash-step body that terminates within `fuel` (the explicit
    termination hypothesis — the public grind bound), the front descent unrolled
    to the trip count read off the run denotes exactly the guard-driven while
    semantics. Instantiates `rWhileNz_whole_denote` at the covered PoW body. -/
theorem powGrindCovered_denote
    (guard : SEnvScalar → Bool) (fuel : Nat)
    {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
    (env env' : SEnvScalar) (o : DTransOut Γ)
    (hc : ConsistentS vm V env)
    (htr : loopWhileD (translateBody := fun vm' => translateDialectControl vm' powGrindStepBody)
      vm (scalarWhileTrips (fun e => semScalar powGrindStepBody e) guard fuel env) = some o)
    (hrun : semScalarWhile (fun e => semScalar powGrindStepBody e) guard fuel env = some env') :
    ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
      ConsistentS o.vm V' env' ∧
      ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
        ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' :=
  rWhileNz_whole_denote powGrindStepBody_coveredCtl guard fuel vm V env env' o hc htr hrun

/-! ## 7. Axiom audit -/

#print axioms plonky3OrchLoops_coveredSeq
#print axioms plonky3OrchLoops_front_fires
#print axioms plonky3OrchLoops_front_eq
#print axioms plonky3OrchLoopsCovered_denote
#print axioms powGrind_coveredWhile
#print axioms powGrindCovered_denote

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3OrchLoopsCovered
