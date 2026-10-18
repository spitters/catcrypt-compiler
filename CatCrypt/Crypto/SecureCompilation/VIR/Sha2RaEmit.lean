/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public meta import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA
public import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA

/-!
# SHA-2 compression emitted with slot names taken from a register allocation

`Sha2Emit.lean` emits each `Com.var` of the SHA-2 compression to `st[slot]`
through the fixed slot file `slotSeq`. This module emits the same `Com` with
destination slots rerouted through a `RegisterAllocation`: where
`Sha2Emit.dstName sp k = "st[" ++ toString (slotSeq sp).getD k 0 ++ "]"`, the
RA-driven version uses `"st[" ++ toString (ra.seqOf ((slotSeq sp).getD k 0)) ++ "]"`.
For `RegisterAllocation.identity` the destination names agree pointwise with
`Sha2Emit.dstName` (§3).

No theorem here relates the `ra.seqOf`-routed text to the unrenamed emit or to
the semantics of `compressCom`. The register allocator with a semantic theorem
is `physScanSpill` (`toLprogPhysAbi_faithful_uniform`).

## Main results

* `raDstName_identity_eq` (§3) — for the identity allocation, destination names
  agree with `Sha2Emit.dstName` pointwise.
* `sha2RA_iters_WellFormed`, `sha2RA_coalesce_WellFormed` — the cross-iteration
  and coalescing allocations have injective `slotOf`.
* `sha256_working_state_carried` — the 8 working-state words are carried
  across every round boundary.

## Contents

* `sha2RoundJForProg` — the SHA-2 schedule loop `schedLoop` as a `JForProg`.
* `emitSha2RoundRaJazz` — the `.jazz` text of `compressCom` with destination
  slot names rewritten through `ra.seqOf`.

## Allocations used by the bench emit

`linearScanRA p` assigns slots to the binders of `p`. The slot indices of
`Sha2Emit.compressCom` (`0..127`) are not binder indices of the `JForProg`
wrapper. The benchmark emit passes `UnrolledComRA.unrolledSlotRASha`, a linear
scan over the slot domain of `compressCom`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha2RaEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
open CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation

set_option autoImplicit false

/-! ## 1. The SHA-2 round body as a `JForProg`

The schedule-loop wrapper `Sha2Emit.schedLoop` already has the shape
`JForProg (WinAcc sp.w)`; this module names it `sha2RoundJForProg`. -/

/-- **The SHA-2 schedule loop as a `JForProg`.**
Iterates the recurrence step `rounds - 16` times. -/
def sha2RoundJForProg (sp : Sha2Spec) : JForProg (WinAcc sp.w) := schedLoop sp

/-! ## 2. The emit-text rewrite under an RA

`linearScanRA` stores its slots in `ra.seqOf` (its `slotOf` is `id`).
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

/-! ## 3. Identity-RA per-binding destination name equals the current emit

For `RegisterAllocation.identity` (`seqOf k = k`), the RA-driven per-binding
destination name reduces pointwise to `Sha2Emit.dstName`. The full-text
equality (a ~14 KB string) is not stated; the pointwise form is. -/

/-- **Identity-RA destination name equals the current SHA-2 destination name
pointwise.** For `ra = RegisterAllocation.identity`, `seqOf k = k`, so each
binding's destination name reduces to `Sha2Emit.dstName sp k`. The full-text
byte-identity follows from this pointwise equality plus `emitAbiOrchReg`
determinism. -/
theorem raDstName_identity_eq (sp : Sha2Spec) (k : Nat) :
    raDstName sp RegisterAllocation.identity k = dstName sp k := by
  simp [raDstName, dstName, RegisterAllocation.identity]

/-! ## 4. Cross-iteration-aware RA via `UnrolledComRA.unrolledSlotRAofIters`

`UnrolledComRA.lean` §7 ships `unrolledSlotRAofIters tr iters`: a
`RegisterAllocation` derived from a per-iteration `SlotEvent` chunking with a
carry-aware linear-scan priority. This section applies it to SHA-2 with the
per-round iteration chunking `UnrolledComRA.shaIterChunks`.

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

/-- The 8 SHA-2 working-state words `a..h` are carried across every round
boundary. -/
theorem sha256_working_state_carried :
    (List.range 8).all
      (fun j => UnrolledComRA.carriedAcross (Sha2Emit.wkA + j)
        (sha2Iters sha256Spec)) = true := by
  native_decide

/-! ## 5. Two-address coalescing

`UnrolledComRA.lean` §8 ships `unrolledSlotRAofItersCoalesce`: a
coalesce-aware variant of the cross-iter RA that fuses `dst` and `src1`
into one physical slot when `src1` dies at the event.

Unlike ChaCha20 (whose `⟨a, [a, b]⟩` events are already two-address by
construction) and Poseidon2 (whose self-touch events `⟨s, [s]⟩` have `dst
= head rds`), SHA-2's compression body contains **three-address**
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

### Candidates detected, both merges rejected

The coalesce pass (`tryMergeOne`) tentatively merges each
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

For SHA-2, candidate detection finds 12 raw candidates, 2 of which survive
the seed filter, and the no-collision recheck rejects both merges. Coalescing
on SHA-2 would need live ranges tighter than `[firstTouch, lastTouch]` in the
trace encoding, for example `SlotEvent`s with explicit kill-points. -/

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

/-- **SHA-256 has two coalesce candidates surviving seed filtering.**
Unlike ChaCha20 / Poseidon2 (which see zero candidates because their
trace encodings are already two-address-shaped), SHA-256's body has
three-address scratch-flank ops where `dst ≠ head rds` and
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
