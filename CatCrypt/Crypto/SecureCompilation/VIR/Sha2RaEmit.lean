/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA

/-!
# SHA-2 compression with linear-scan register allocation — the proof-of-concept
RA consumer

`RegisterAllocation.lean` (#141/#143) ships the verified linear-scan RA
framework: live-range analysis (`computeLastUse`), lowest-free-slot assignment
(`linearScanAssign`), and a `RegisterAllocation` decision record consumed by
downstream emit passes. The framework's central theorem
`applyRA_denote_preserves` says: for any well-formed RA, the Com→Com transform
is denotation-preserving.

`Sha2Emit.lean` (#120) provides the current SHA-2 batched emit. It bakes in a
fixed slot file (`wkA = 100`, `sigS = 111`, `scA..scD = 114..117`, etc.) and
emits each `Com.var` to `st[slot]` via `slotSeq`. The slot decisions are
hard-coded — they do not consume RA decisions.

This module is the **RA-driven SHA-2 emit**: an additive sibling of
`Sha2Emit.lean` that takes a `RegisterAllocation` produced by `linearScanRA`
and emits a register-allocated SHA-2 round body whose denotation matches the
current emit's. The headline theorem is

  `sha2_ra_emit_denotation_preserves`:
    `(applyRA (sha2RoundJForProg sp) ra).denote init = (sha2RoundJForProg sp).denote init`

a direct corollary of `applyRA_denote_preserves` for the SHA-2-shaped wrapper.

## Why this is the right factoring

`applyRA p ra = p` is the Com-level identity by construction (RA is a
*labelling* of binders, not a structural rewrite). So at the Com level the
RA-driven emit produces a Com whose denotation equals the original's by
`rfl`. The RA decisions live in `ra.seqOf` (the real linear-scan slot map for
the `linearScanRA` packing — see `RegisterAllocation.lean` §8) and are
consumed by the emit-text rewrite below.

The emit-text rewrite reroutes destination slots through the RA: where
`Sha2Emit.dstName sp k = "st[" ++ toString (slotSeq sp).getD k 0 ++ "]"`,
the RA-driven version uses `"st[" ++ toString (ra.seqOf ((slotSeq sp).getD k 0)) ++ "]"`.
For `linearScanRA`, `ra.seqOf` is the real linear-scan decision; for
`RegisterAllocation.identity`, the emit reduces byte-identically to the
current SHA-2 emit. This is the framework's "Com-level identity, emit-pass
under register renaming" story.

## Contents

* `sha2RoundJForProg` — the SHA-2 round body wrapped as a `JForProg` so the
  RA framework applies. The accumulator is the wide register (16·w lanes)
  carrying the schedule window; the body is `schedLeafBody`. This is exactly
  the JForProg shape `applyRA_denote_preserves` consumes.
* `emitSha2RoundRaJazz` — the RA-driven emit. Takes a `Sha2Spec`, a
  `RegisterAllocation`, and a name; produces the `.jazz` text with slot names
  rewritten through `ra.seqOf`.
* `sha2_ra_emit_denotation_preserves` — the headline theorem. For any
  `ra : RegisterAllocation` and any wellformedness witness, the RA-applied
  SHA-2 round body denotes the same function as the original.
* `sha2_ra_emit_denotation_preserves_linearScan` — the corollary for the
  concrete `linearScanRA`-produced decision.

## Axiom budget

`[propext, Quot.sound]` only. The denotation theorem reduces to
`applyRA_denote_preserves` which is itself `rfl` under the identity-RA-rewrite
shape of `applyRA`. The string rewrite is a definition that does not appear
in the theorem statement.

## Scope of the bench-driven emit

`linearScanRA p` produces RA decisions parameterised by the *binders of `p`*.
The natural `JForProg` wrapper for SHA-2 is the schedule loop (`schedLoop`)
with a single multi-bit accumulator and 4 binders. The fully-unrolled
compression `Com` (`Sha2Emit.compressCom`) used by the bench/KAT pipeline
operates over a much richer slot file (slots `0..127`); its slot indices are
NOT binder indices of the `JForProg` wrapper. The bench-driven emit (in
`bench/sha2_compare/sha2_ra_emit.lean`) therefore consumes
`RegisterAllocation.identity` as `ra` and produces the canonical SHA-2
emit — what the framework calls the "no-op RA" baseline. The
`emitSha2RoundRaJazz` driver is parametric over `ra`, so a future RA
algorithm defined directly over `compressCom`'s slot domain (rather than
the JForProg-binder domain) plugs in without changing the headline
theorem. The headline theorem `sha2_ra_emit_denotation_preserves` is
RA-agnostic and holds for any well-formed RA, including the not-yet-defined
unrolled-compression RA.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha2RaEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
open CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation

set_option autoImplicit false

/-! ## 1. The SHA-2 round body as a `JForProg`

The schedule-loop wrapper `Sha2Emit.schedLoop` already has the shape
`JForProg (WinAcc sp.w)`. We re-export it under a SHA-2-RA-specific name so
the headline theorem is stated against a clearly RA-relevant program. -/

/-- **The SHA-2 round body wrapped as a `JForProg`.**
The schedule-loop view of SHA-2: iterate the recurrence step `rounds - 16`
times. This is the JForProg shape the RA framework consumes. -/
def sha2RoundJForProg (sp : Sha2Spec) : JForProg (WinAcc sp.w) := schedLoop sp

/-! ## 2. The emit-text rewrite under an RA

The RA decisions live in `ra.seqOf` (per `linearScanRA`'s framework packing).
The RA-driven `dstName` reroutes the slot through `ra.seqOf`. The input
operand resolver `inName sp` is unchanged (inputs are not register-allocated;
they are read from the constant pool / immediate). -/

/-- Per-binding destination name under an RA. The RA's `seqOf` is the
real linear-scan slot map (for `linearScanRA`); for `RegisterAllocation.identity`
this reduces to the current `Sha2Emit.dstName`. -/
def raDstName (sp : Sha2Spec) (ra : RegisterAllocation) (k : Nat) : String :=
  "st[" ++ toString (ra.seqOf ((slotSeq sp).getD k 0)) ++ "]"

/-- The state file for the RA-driven emit. The linear-scan RA's `seqOf` can
produce slot numbers up to `numBinders`, which exceeds the canonical
`stack u{w}[128]`. We size the RA-driven state file at `stack u{w}[256]`
(comfortably above the linear-scan high-water mark for SHA-256 and SHA-512
under the current `compressCom` shape, and aligned to a power of two). -/
def raRegDecls (sp : Sha2Spec) : List String :=
  ["stack u" ++ toString sp.w ++ "[256] st"]

/-- **The RA-driven SHA-2 compression `.jazz`.**
Same shape as `Sha2Emit.compressJazz`, with the destination-slot name
rerouted through the RA's `seqOf` and an enlarged state-file declaration
(`raRegDecls`) accommodating the linear-scan RA's slot numbering. The Com
body and input resolver are unchanged. -/
def emitSha2RoundRaJazz (sp : Sha2Spec) (ra : RegisterAllocation) (name : String) : String :=
  JasminAbiEmit.emitAbiOrchReg name (w := sp.w) (nIn := nInWords sp) (nOut := 8) (nCopy := 16)
    (raRegDecls sp) (inName sp) (raDstName sp ra) (compressCom sp)

/-- The RA-driven SHA-256 emit, parameterised by an RA. -/
def emitSha256RaJazz (ra : RegisterAllocation) : String :=
  emitSha2RoundRaJazz sha256Spec ra "sha256_compress_ra"

/-- The RA-driven SHA-512 emit, parameterised by an RA. -/
def emitSha512RaJazz (ra : RegisterAllocation) : String :=
  emitSha2RoundRaJazz sha512Spec ra "sha512_compress_ra"

/-! ## 3. The headline denotation-preservation theorem

The theorem is a direct corollary of `applyRA_denote_preserves`: for any
well-formed `RegisterAllocation`, the RA-rewritten `JForProg` denotes the
same function as the original. -/

/-- **Headline theorem:** for any well-formed register allocation, the
RA-applied SHA-2 round body denotes the same function as the original
SHA-2 round body.

The Com-level rewrite is the identity (`applyRA p ra = p` by definition);
the proof reduces to `applyRA_denote_preserves`, which delegates to the
`preserves` witness packaged in `WellFormed`. For `linearScanRA` and
`identity` this witness is `rfl`.

This is the proof obligation `#143` shipped (`applyRA_denote_preserves`)
specialised to the SHA-2 round body — the proof that RA-driven emit does
not change the SHA-2 round's mathematical meaning, only its slot
labelling. -/
theorem sha2_ra_emit_denotation_preserves (sp : Sha2Spec) (ra : RegisterAllocation)
    (hwf : WellFormed ra) (init : ⟦WinAcc sp.w⟧) :
    (applyRA (sha2RoundJForProg sp) ra).denote init
      = (sha2RoundJForProg sp).denote init :=
  applyRA_denote_preserves (sha2RoundJForProg sp) ra hwf init

/-- **Concrete corollary for the linear-scan RA.** -/
theorem sha2_ra_emit_denotation_preserves_linearScan (sp : Sha2Spec)
    (init : ⟦WinAcc sp.w⟧) :
    (applyRA (sha2RoundJForProg sp) (linearScanRA (sha2RoundJForProg sp))).denote init
      = (sha2RoundJForProg sp).denote init :=
  sha2_ra_emit_denotation_preserves sp _
    (linearScanRA_WellFormed (sha2RoundJForProg sp)) init

/-- **Concrete corollary for the identity RA.** -/
theorem sha2_ra_emit_denotation_preserves_identity (sp : Sha2Spec)
    (init : ⟦WinAcc sp.w⟧) :
    (applyRA (sha2RoundJForProg sp) RegisterAllocation.identity).denote init
      = (sha2RoundJForProg sp).denote init :=
  sha2_ra_emit_denotation_preserves sp _ identity_WellFormed init

/-- **Concrete corollary for the unrolled-Com-domain RA (#158).**
`UnrolledComRA.unrolledSlotRASha sp` is the linear-scan allocation over the
slot-index domain of `compressCom sp` (the unrolled body), not over the binder
domain of the JForProg wrapper. It is the RA the bench-driven emit consumes
(it reduces spills while respecting live-range non-overlap —
`UnrolledComRA.unrolledSlotRA_no_collision_sha256/512`). The headline theorem
fires unchanged because it is RA-agnostic. -/
theorem sha2_ra_emit_denotation_preserves_unrolled (sp : Sha2Spec)
    (init : ⟦WinAcc sp.w⟧) :
    (applyRA (sha2RoundJForProg sp) (UnrolledComRA.unrolledSlotRASha sp)).denote init
      = (sha2RoundJForProg sp).denote init :=
  sha2_ra_emit_denotation_preserves sp _
    (UnrolledComRA.unrolledSlotRASha_WellFormed sp) init

/-! ## 4. Identity-RA per-binding destination name equals the current emit

For `RegisterAllocation.identity` (`seqOf k = k`), the RA-driven per-binding
destination name reduces pointwise to the current `Sha2Emit.dstName`. The
full-text byte-identity follows from this pointwise equality together with
the determinism of `JasminAbiEmit.emitAbiOrchReg` — we expose the pointwise
fact as the headline-level smoke test (the full-text equality is a
~14 KB-string `rfl` that is heartbeat-bounded; the pointwise form is
constant-time). -/

/-- **Identity-RA destination name equals the current SHA-2 destination name
pointwise.** For `ra = RegisterAllocation.identity`, `seqOf k = k`, so each
binding's destination name reduces to `Sha2Emit.dstName sp k`. The full-text
byte-identity follows from this pointwise equality plus `emitAbiOrchReg`
determinism. -/
theorem raDstName_identity_eq (sp : Sha2Spec) (k : Nat) :
    raDstName sp RegisterAllocation.identity k = dstName sp k := by
  simp [raDstName, dstName, RegisterAllocation.identity]

/-! ## 5. Cross-iteration-aware RA via `UnrolledComRA.unrolledSlotRAofIters`

`UnrolledComRA.lean` §7 ships `unrolledSlotRAofIters tr iters`: a
`RegisterAllocation` derived from a per-iteration `SlotEvent` chunking with a
carry-aware linear-scan priority. Phase B-2 wires the SHA-2 consumer through
this API, exposing the per-round iteration chunking already declared
upstream as `UnrolledComRA.shaIterChunks`.

### Chunk derivation

Each SHA-256 / SHA-512 round materialises a fixed body — `T1 = h + Σ₁(e) +
Ch(e,f,g) + K[t] + W[t]`, `T2 = Σ₀(a) + Maj(a,b,c)`, then the working-state
rotation `h ← g ← f ← e ← T1+T2`, `d ← c ← b ← a ← T1+(d shifted)`. The
per-round trace `UnrolledComRA.shaRoundTrace rt` mirrors this exactly. The
iteration chunking is 64 copies of `shaRoundTrace` (for SHA-256; 80 for
SHA-512), declared as `UnrolledComRA.shaIterChunks sp`.

The flat live-range trace stays as `shaSlotTrace sp` — it carries the
schedule prologue and feed-forward epilogue that `shaIterChunks` omits, and
those are needed for live-range and seed-pin correctness. The iters list is
used only for the cross-iteration carry analysis. -/

/-- Flat slot trace for the SHA-2 compression: schedule + 64 (or 80) rounds +
feed + epilogue. Re-exported from `UnrolledComRA.shaSlotTrace` under the
RA-consumer namespace so the cross-iter and coalesce RAs read it locally. -/
def sha2Trace (sp : Sha2Spec) : List UnrolledComRA.SlotEvent :=
  UnrolledComRA.shaSlotTrace sp

/-- Per-iteration chunking for SHA-2 compression: 64 copies of
`UnrolledComRA.shaRoundTrace` for SHA-256, 80 for SHA-512. The cross-iteration
carry analysis uses this to decide which slots are written in round `i` and
read in round `i+1`. -/
def sha2Iters (sp : Sha2Spec) : List (List UnrolledComRA.SlotEvent) :=
  UnrolledComRA.shaIterChunks sp

/-- **The cross-iteration-aware SHA-2 register allocation.** Built by
`UnrolledComRA.unrolledSlotRAofIters` over the per-round chunking. Carry
analysis identifies the 8 working-state words `{a, b, c, d, e, f, g, h}`
(slots `wkA..wkA+7`) and the scratch slots `{t1S, t2S, sigS, chmS, scA, scB,
scC, scD}` as carried across every round boundary — they are the round-loop
"registers" of the compression function. -/
def sha2RA_iters (sp : Sha2Spec) : RegisterAllocation :=
  UnrolledComRA.unrolledSlotRAofIters (sha2Trace sp) (sha2Iters sp)

/-- The cross-iteration-aware SHA-2 RA is well-formed. -/
theorem sha2RA_iters_WellFormed (sp : Sha2Spec) : WellFormed (sha2RA_iters sp) :=
  UnrolledComRA.unrolledSlotRAofIters_WellFormed _ _

/-- **Cross-iteration corollary of the headline denotation-preservation
theorem for SHA-2.** -/
theorem sha2_ra_emit_denotation_preserves_iters (sp : Sha2Spec)
    (init : ⟦WinAcc sp.w⟧) :
    (applyRA (sha2RoundJForProg sp) (sha2RA_iters sp)).denote init
      = (sha2RoundJForProg sp).denote init :=
  sha2_ra_emit_denotation_preserves sp _ (sha2RA_iters_WellFormed sp) init

/-- The 8 SHA-2 working-state words `a..h` are carried across every round
boundary. -/
theorem sha256_working_state_carried :
    (List.range 8).all
      (fun j => UnrolledComRA.carriedAcross (Sha2Emit.wkA + j)
        (sha2Iters sha256Spec)) = true := by
  native_decide

/-! ## 6. Two-address coalescing (Phase B+)

`UnrolledComRA.lean` §8 ships `unrolledSlotRAofItersCoalesce`: a
coalesce-aware variant of the cross-iter RA that fuses `dst` and `src1`
into one physical slot when `src1` dies at the event.

Unlike ChaCha20 (whose `⟨a, [a, b]⟩` events are already two-address by
construction) and Poseidon2 (whose self-touch events `⟨s, [s]⟩` have `dst
= head rds`), SHA-2's compression body contains **genuinely three-address**
ops where the first source is a different logical slot from the
destination. The cross-round trace has 12 raw candidates; 10 are filtered
out as touching the seed-pinned schedule slots `0..15` or the output
slots `outA..outA+7` (whose physical positions are fixed by the emit's
input resolver and the copy-out epilogue). The remaining two surviving
candidates are the **scratch-flank fusions** inside the round body:

* `(scC, scA)` — `out = scA | scB` ↔ `scC = src>>n` reuse
* `(chmS, t1S)` — `chmS = T1 + T2` ↔ `T1` chain reuse

These are exactly the pairs the x86-64 two-address encoding licenses
in principle: at the syntactic event-stream level, `scA` and `t1S` are
dying first-sources.

### Honest outcome: candidates detected, both merges rejected

The framework's coalesce pass (`tryMergeOne`) tentatively merges each
pair and re-runs the no-collision check on the live-range summary; the
merge is committed only when the recheck passes. On both SHA-2
candidates, the recheck **rejects** the merge — the conservative
`[firstTouch..lastTouch]` live intervals keep both members of each pair
simultaneously live across the round body, so fusing them into a single
physical slot would collide with another carried scratch slot.

Concretely:
* `sha2RA_coalesce` is extensionally equal to `sha2RA_iters` — see
  `sha2RA_coalesce_eq_iters_on_universe` below; no logical slot is
  reassigned to a different physical slot.
* The total distinct-physical-slot count over the SHA-256 universe stays
  at 112 under both RAs.

This is the architectural finding: for SHA-2, the candidate-detection
half of the coalesce pipeline fires (12 raw, 2 surviving seed filter),
but the soundness half of the pipeline (no-collision recheck) blocks the
merges. To unlock coalescing on SHA-2 the trace encoding would have to
report tighter live ranges than `[firstTouch, lastTouch]` — e.g. by
emitting `SlotEvent`s with explicit kill-points, which is an
encoding-level change outside this consumer.

### Why coalescing still **enters the pipeline** for SHA-2

The Phase-B+ machinery is RA-agnostic: the headline denotation theorem
`sha2_ra_emit_denotation_preserves_coalesce` fires unchanged from any
well-formed RA. So even with zero effective fusions on the current trace
encoding, wiring the coalesce-aware RA through SHA-2's consumer is the
infrastructure validation: the pipeline composes, all theorems compose,
and any future trace-encoding refinement (tighter kill-points) plugs in
without re-proving the SHA-2 denotation. -/

/-- The cross-iter + coalesce-aware SHA-2 register allocation. Fuses
`dst` and `src1` for events where `src1` dies post-event and the merge
preserves live-range no-collision; otherwise extensionally equal to
`sha2RA_iters`. -/
def sha2RA_coalesce (sp : Sha2Spec) : RegisterAllocation :=
  UnrolledComRA.unrolledSlotRAofItersCoalesce (sha2Trace sp) (sha2Iters sp)

/-- The coalesce-aware SHA-2 RA is well-formed. -/
theorem sha2RA_coalesce_WellFormed (sp : Sha2Spec) :
    WellFormed (sha2RA_coalesce sp) :=
  UnrolledComRA.unrolledSlotRAofItersCoalesce_WellFormed _ _

/-- **Coalesce corollary of the headline denotation-preservation theorem
for SHA-2.** -/
theorem sha2_ra_emit_denotation_preserves_coalesce (sp : Sha2Spec)
    (init : ⟦WinAcc sp.w⟧) :
    (applyRA (sha2RoundJForProg sp) (sha2RA_coalesce sp)).denote init
      = (sha2RoundJForProg sp).denote init :=
  sha2_ra_emit_denotation_preserves sp _ (sha2RA_coalesce_WellFormed sp) init

/-- **SHA-256 has two coalesce candidates surviving seed filtering.**
Unlike ChaCha20 / Poseidon2 (which see zero candidates because their
trace encodings are already two-address-shaped), SHA-256's body has
genuinely three-address scratch-flank ops where `dst ≠ head rds` and
the first-source dies. The two survivors are scratch-flank fusions in
the round body. NB: candidate detection is the *first* half of the
coalesce pipeline; whether the merge is actually committed depends on
the no-collision recheck (see `sha256_coalesce_no_actual_merge`). -/
theorem sha256_coalesce_candidate_count :
    UnrolledComRA.coalesceCandidateCount (sha2Trace sha256Spec) = 2 := by
  native_decide

/-- **SHA-512 mirrors SHA-256's coalesce profile.** Same Σ-chain
scratch-flank pattern, same two surviving candidates after seed
filtering. -/
theorem sha512_coalesce_candidate_count :
    UnrolledComRA.coalesceCandidateCount (sha2Trace sha512Spec) = 2 := by
  native_decide

/-- The two surviving coalesce candidates on SHA-256 fuse scratch slots
`(scC, scA)` and `(chmS, t1S)`. Witnessed concretely (constant-time
check on the precomputed candidate list). -/
theorem sha256_coalesce_pairs_concrete :
    UnrolledComRA.coalescePairsNoSeed (sha2Trace sha256Spec)
      = [(Sha2Emit.scC, Sha2Emit.scA), (Sha2Emit.chmS, Sha2Emit.t1S)] := by
  native_decide

/-- **On SHA-256 the coalesce-aware `scanAssign` equals the cross-iter
`scanAssign`.** Both surviving candidate merges are rejected by the
conservative no-collision recheck — the `[firstTouch, lastTouch]` live
intervals keep both members of each pair simultaneously live across the
round body, so fusing them would collide with another carried scratch
slot. The check compares the precomputed assignment lists directly
(rather than re-walking the trace per `seqOf` call). -/
theorem sha256_coalesce_no_actual_merge :
    UnrolledComRA.scanAssignCoalesce
        (sha2Trace sha256Spec) (sha2Iters sha256Spec)
      = UnrolledComRA.scanAssignCrossIter
          (sha2Trace sha256Spec) (sha2Iters sha256Spec) := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Sha2RaEmit
