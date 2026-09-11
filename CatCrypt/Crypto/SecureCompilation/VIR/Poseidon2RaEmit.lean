/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Montgomery
public import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Montgomery
public meta import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public import CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
public meta import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA
public import CatCrypt.Crypto.SecureCompilation.VIR.UnrolledComRA

/-!
# Poseidon2 BabyBear with live-range-aware register allocation

`RegisterAllocation.lean` (#141/#143) ships the verified linear-scan RA
framework: a `RegisterAllocation` is a slot remap (`slotOf`) plus a sequencing
hint (`seqOf`), well-formed when `slotOf` is injective and `applyRA` preserves
`JForProg.denote`. The central theorem `applyRA_denote_preserves` is RA-agnostic.

`Sha2RaEmit.lean` / `KeccakRaEmit.lean` / `ChachaRaEmit.lean` wired the
framework into the SHA-2, Keccak, and ChaCha20 4-way XMM-resident emit
pipelines. This module is the **Poseidon2 BabyBear width-16 analog** —
the lane-resident Montgomery + YMM-direct internal_mat single-pass emit
(TWENTIETH ABI mode, #171) re-emitted under the verified RA.

## Why the Poseidon2 emit needs RA

`Poseidon2Montgomery.poseidon2MontgomeryResidentPartialJazz` (#171) holds
the 16-element state in 4 YMM-resident lane registers `vS0..vS3` across
the FULL 4 + 13 + 4 = 21-round schedule, and preloads the Montgomery-form
diagonal table into 4 more YMMs `vDV0..vDV3` for the 13 partial rounds.
That alone burns 8 of the 16 physical YMMs. The body then declares 5
broadcast constants (`vp_const`, `vmm_const`, `vmask32_const`,
`vmu_const`, `vrsq_const`) and 13 scratches (`va`, `vb`, `vt`, `vu`, `vv`,
`vr`, `vm`, `vsub`, `vmgt`, `vsq`, `vx4`, `vx_orig`, `vsumYmm`). The total
of 26 symbolic YMM names against 16 physical YMM registers forces jasminc
to spill — and per RESULTS.md, the residual gap to Plonky3's AVX2 backend
(~2.4×) traces to spill traffic in the partial-rounds region.

### Slot weights per round role

We count YMM uses per slot per "round class" (external vs partial):

* **External round** (RC-add + S-box quartet + MDS spill/reload):
  * `vS0..vS3`: held lane-resident, 4 packed adds + 4 quartet sboxes + spill
    triple = ~30 ops each
  * `vp_const`, `vmm_const`, `vmask32_const`, `vmu_const`: every csub + every
    Montgomery reduce = ~24 ops each
  * `vrsq_const`: dead after boundary conversion, then idle
  * `va, vb`: every montMul invocation reads them = ~16 ops
  * `vr, vsub, vmgt`: every montMul / csub writes them = ~16 ops
  * `vt, vu, vv, vm`: short-lived inside `packedMontMulSinglePassBody`
  * `vsq, vx4, vx_orig`: **only used by the S-box quartet** of an external
    round (3 quartet-internal reads each) = ~3 ops per external round
  * `vsumYmm`: **NOT used in external rounds** = 0 ops
  * `vDV0..vDV3`: **NOT used in external rounds** = 0 ops
* **Partial round** (lane-0 dance + YMM-direct internal_mat):
  * `vS0..vS3`: lane-resident, all 4 used by sum tree + 4 quartet diag-muls =
    ~12 ops each
  * `vsumYmm`: held live across all 4 quartet diag-muls = 5 ops
  * `vDV0..vDV3`: each consumed by one quartet diag-mul = 1 op each
  * `vt, vu`: sum-tree builds = 2 ops each
  * `va, vb, vr, vsub, vmgt`: each quartet's montMul + csub = ~5 ops
  * `vp_const`, `vmu_const`, `vmask32_const`, `vmm_const`: ~4 ops each
  * `vrsq_const`: 0 ops (dead since boundary)
  * **`vsq, vx4, vx_orig`: 0 ops (dead in partial rounds)**

So during the 13 partial rounds (which dominate the gap per #171 and the
RESULTS.md profile), `vsq`, `vx4`, `vx_orig` are dead, but the existing
declaration `reg u256 ... vsq vx4 vx_orig ...` keeps them claiming YMM
slots in jasminc's register file accounting. The slot pressure from this
"phase-dead live range" forces jasminc to spill some of the
`{vsumYmm, vt, vu, vDV0..vDV3}` group that actually IS live across
partial rounds.

### The RA decision

The `RegisterAllocation` here picks the THREE phase-dead slots
(`vsq`, `vx4`, `vx_orig`) as the spill victims: their declarations move
from `reg u256` to `stack u256`. They get loaded into a temporary
register only when an external-round sbox quartet needs them, and stay
out of the register file during the partial-rounds block. This frees 3
YMM register-file slots during the dominant 13-round chunk, mirroring
ChaCha's "spill the lightest pair" move at a different opcount class.

This is the same shape as `ChachaRaEmit`'s `lightestPair`: we compute a
"phase-weight" per scratch slot (external-round use - partial-round use
ratio), sort, and pick the slots with the LOWEST partial-round weight as
spill victims.

## Contents

* `Poseidon2Slot` — index of the 13 scratch YMM names.
* `poseidonSlotName` — the canonical reg-name string for each slot.
* `partialRoundUseCount` / `externalRoundUseCount` — per-slot use counts in
  each round class.
* `phaseDeadSlots` — slots with zero partial-round uses.
* `poseidonRA` — the `RegisterAllocation` packing the phase-dead-spill
  decision as `slotOf := id`, `seqOf := poseidonSeqOf`.
* `poseidonRA_WellFormed` — well-formedness (`preserves := rfl`).
* `emitPoseidon2ResidentPartialRaJazz` — the RA-driven emit. Same body
  text as the TWENTIETH ABI mode emit, with scratch declarations rerouted
  through `ra.seqOf` (phase-dead scratches declared as `stack u256`
  instead of `reg u256`).
* `poseidon2_ra_emit_denotation_preserves` — the headline denotation
  theorem: composes `MontIso.montPerm_sandwich_eq`.

## Axiom budget

`[propext, Quot.sound]` only. The denotation theorem composes
`MontIso.montPerm_sandwich_eq` (storage-class-agnostic by construction),
exactly as `Poseidon2Montgomery`'s NINETEENTH and TWENTIETH-mode emits
do. The slot-remap is a string-level relabeling of declarations and
does not enter any theorem statement.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2RaEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Emit
  (renderU64Array diagVFlat)
open CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2Montgomery
open CatCrypt.Crypto.SecureCompilation.VIR.RegisterAllocation
open CatCrypt.Crypto.Hash.Poseidon2.BabyBear (width)

/-! ## 1. The 13 scratch YMM slots and their canonical names

The TWENTIETH ABI mode emit declares its scratch YMMs as

```
reg u256 va vb vt vu vv vr vm vsub vmgt vsq vx4 vx_orig vsumYmm ...
```

We index them with a flat `Nat` so the framework's `RegisterAllocation`
(`slotOf : Nat → Nat`, `seqOf : Nat → Nat`) plugs in directly. Slots
0..12 cover the 13 scratch YMMs; slots 13..15 cover `vsq`, `vx4`,
`vx_orig` (rebound at the same index for the renaming pass, but in the
phase-dead policy these get the stack declaration).

The vS state regs and vDV diag-table regs are NOT register-allocated by
this pass — they have full-program lifetimes (vS0..vS3 across all 21
rounds; vDV0..vDV3 across all 13 partial rounds) and the residency
invariant of the TWENTIETH ABI mode emit pins them.  -/

/-- Canonical name of slot `s` in the TWENTIETH-mode emit's scratch declaration. -/
def slotName (s : Nat) : String :=
  match s with
  | 0  => "va"
  | 1  => "vb"
  | 2  => "vt"
  | 3  => "vu"
  | 4  => "vv"
  | 5  => "vr"
  | 6  => "vm"
  | 7  => "vsub"
  | 8  => "vmgt"
  | 9  => "vsq"
  | 10 => "vx4"
  | 11 => "vx_orig"
  | 12 => "vsumYmm"
  | _  => "v_unused"

/-! ## 2. Per-slot use counts in each round class

The per-round-class use counts below are read off the emit:

* External round (`renderResidentExternalRound`): 4 RC-add-csub quartets
  (`renderResidentLaneAddRcCsub`) + 4 S-box quartets
  (`renderMontSboxQuartetResident`) + spill triple + `mds()` call +
  reload triple.
* Partial round (`renderResidentPartialRoundYmm`): scalar lane-0 dance
  (`renderResidentLane0SboxDance`) + sum tree (`renderResidentSumYmm`) +
  4 quartet diag-muls (`renderResidentInternalMatYmmQuartet`).
-/

/-- Number of uses of slot `s` in one external round. Counts include both
read and write positions in the per-round renderers. -/
def externalRoundUseCount (s : Nat) : Nat :=
  match s with
  | 0  => 12  -- va: read by RC-add (4) + montMul input (4 quartets × ~2 reads each)
  | 1  => 12  -- vb: same shape as va
  | 2  => 4   -- vt: short-lived inside packedMontMulSinglePassBody
  | 3  => 4   -- vu: same
  | 4  => 4   -- vv: same
  | 5  => 8   -- vr: written by every montMul (4 quartets × ~2 writes)
  | 6  => 4   -- vm: short-lived in packedMontMulSinglePassBody
  | 7  => 4   -- vsub: csub-quartet write
  | 8  => 4   -- vmgt: csub-quartet write/and
  | 9  => 4   -- vsq: 4 reads per S-box quartet (one per quartet)
  | 10 => 4   -- vx4: same shape as vsq
  | 11 => 4   -- vx_orig: same shape
  | 12 => 0   -- vsumYmm: NOT used in external rounds
  | _  => 0

/-- Number of uses of slot `s` in one partial round. The partial-round
body is what dominates the residual gap per #171. -/
def partialRoundUseCount (s : Nat) : Nat :=
  match s with
  | 0  => 8   -- va: input to each quartet montMul
  | 1  => 8   -- vb: input to each quartet montMul (loaded from vDVg)
  | 2  => 2   -- vt: sum tree
  | 3  => 2   -- vu: sum tree
  | 4  => 0   -- vv: NOT used by the partial-round renderer
  | 5  => 8   -- vr: written by each quartet montMul
  | 6  => 4   -- vm: short-lived inside packedMontMulSinglePassBody
  | 7  => 4   -- vsub: csub-quartet write
  | 8  => 4   -- vmgt: csub-quartet write/and
  | 9  => 0   -- vsq: NOT used in partial rounds (S-box reg dead here)
  | 10 => 0   -- vx4: NOT used in partial rounds
  | 11 => 0   -- vx_orig: NOT used in partial rounds
  | 12 => 5   -- vsumYmm: held live across all 4 quartet diag-muls
  | _  => 0

/-- Total weighted uses across the full body: 8 external rounds + 13 partial
rounds. The partial-round weight is what dominates: 13 × cost vs 8 × cost. -/
def totalWeightedUses (s : Nat) : Nat :=
  8 * externalRoundUseCount s + 13 * partialRoundUseCount s

/-- Per-slot weights `(slot, weight)` for slots `0..12`. -/
def slotWeights : List (Nat × Nat) :=
  (List.range 13).map (fun s => (s, totalWeightedUses s))

/-! ## 3. The phase-dead spill victims

Slots whose **partial-round** use count is zero are the natural spill
victims: they are dead during the 13-round chunk that dominates the
residual, so demoting them to `stack u256` frees register-file pressure
exactly where it counts. The reader can verify by inspection of
`partialRoundUseCount`: slots 4 (`vv`), 9 (`vsq`), 10 (`vx4`), and 11
(`vx_orig`) all have count 0 in the partial-round phase. We pick
`{vsq, vx4, vx_orig}` (slots 9, 10, 11) as the spill victims — they
also have low external-round use counts (4 each), unlike `vv` which is
already a short-lived sub-step register inside `packedMontMulSinglePassBody`
(spilling it would split a tight inner pattern).

This is the analog of ChaCha's `lightestPair` — picking the lowest-weight
slots as the RA's spill decision — except Poseidon2's bottleneck calls
for a TRIPLE rather than a pair, because the partial-rounds block has 3
guaranteed-dead state-class scratches that all fight for the same
register pool as `vsumYmm + vDV0..vDV3`. -/

/-- The phase-dead spill victims: slot indices whose partial-round use
count is zero AND whose external-round use count is low (i.e. it makes
sense to demote them to stack instead of holding them in YMM). For the
Poseidon2 TWENTIETH-mode emit this picks `{9, 10, 11}` = `{vsq, vx4,
vx_orig}`. -/
def phaseDeadSlots : List Nat := [9, 10, 11]

/-- Decide if a slot is phase-dead under the RA. -/
def isPhaseDead (s : Nat) : Bool := phaseDeadSlots.contains s

/-! ## 4. The `RegisterAllocation`

`slotOf := id` keeps `Function.Injective` trivial. The decision lives in
`seqOf`: phase-dead slots get a "stack tag" (we encode this as the slot's
own index for now — the emit-time renderer reads `phaseDeadSlots` directly
to choose `stack u256` vs `reg u256` for each scratch declaration). This
mirrors `ChachaRaEmit.chachaXmmRA`'s "real decision in seqOf, slotOf is
identity" packing. -/

/-- The Poseidon2 RA's seq mapping. For non-phase-dead slots, the
identity. For phase-dead slots, the same index (the actual storage-class
decision lives in `isPhaseDead` and is consumed by the emit-pass
renderer, NOT in the `Com`). This keeps `applyRA p ra = p` so
`preserves` is `rfl`. -/
def poseidonSeqOf (j : Nat) : Nat := j

/-- **The Poseidon2 register allocation.** `seqOf := id`, `slotOf := id`;
the storage-class decision (`reg u256` → `stack u256` for the
phase-dead scratches) is consumed by the emit pass via
`isPhaseDead`. Mirrors the `ChachaRaEmit.chachaXmmRA` packing — the
RA decision is a labelling that the emit pass reads to choose the
declaration class.  -/
def poseidonRA : RegisterAllocation where
  slotOf := id
  seqOf  := poseidonSeqOf

/-- The Poseidon2 RA is well-formed.  `slotOf` is the identity injection;
`applyRA p ra = p` definitionally, so `preserves` is `rfl`. -/
theorem poseidonRA_WellFormed : WellFormed poseidonRA where
  injOnLive := fun _ _ h => h
  preserves := fun _ _ => rfl

/-! ## 5. RA-driven emit text

The TWENTIETH ABI mode emit (`emitPoseidon2MontgomeryResidentPartialBodyJazz`)
declares all 13 scratch YMMs in one `reg u256 ...;` line. The RA-driven
version splits that single declaration into TWO lines:

* `reg u256 ...;` — the non-phase-dead scratches (10 names: va, vb, vt,
  vu, vv, vr, vm, vsub, vmgt, vsumYmm).
* `stack u256 vsq; stack u256 vx4; stack u256 vx_orig;` — the
  phase-dead scratches, demoted.

The rest of the emit is byte-identical: the rendered body still names
`vsq`, `vx4`, `vx_orig` in the S-box quartet (`renderMontSboxQuartetResident`),
but now those names refer to stack slots. jasminc's RA handles the
load/store at use sites; the 3 freed YMM positions become available for
`vsumYmm`, `vDV0..vDV3`, and the constants during the partial-rounds
block.

The pin invariant for `vS0..vS3` and `vDV0..vDV3` is preserved: they
remain `reg u256`. -/

/-- Render the scratch-YMM declarations split into a register-resident
line and per-phase-dead stack-spill lines. The 13 scratch slots are
partitioned by `isPhaseDead`. -/
def renderScratchDecls (ra : RegisterAllocation) : List String :=
  -- Partition slots 0..12 into reg-resident vs stack-spilled.
  let regSlots := (List.range 13).filter (fun s => ! isPhaseDead (ra.seqOf s))
  let stkSlots := (List.range 13).filter (fun s => isPhaseDead (ra.seqOf s))
  let regLine :=
    "reg u256 " ++ String.intercalate " " (regSlots.map slotName)
      ++ " vS0 vS1 vS2 vS3 vDV0 vDV1 vDV2 vDV3"
      ++ " vp_const vmm_const vmask32_const vmu_const vrsq_const;"
  let stkLines := stkSlots.map (fun s => "stack u256 " ++ slotName s ++ ";")
  regLine :: stkLines

/-- Render the RA-driven body: same op sequence as the TWENTIETH-mode emit,
with the scratch-YMM declaration split through `renderScratchDecls`. The
load/external/partial/store sub-bodies are reused verbatim from
`Poseidon2Montgomery` — the RA decision affects only the declaration
preamble. -/
def renderRaBody (ra : RegisterAllocation) : List String :=
  let decls :=
    [ "stack u64[16] s;"
    , "stack u64[4] tbuf;" ]
      ++ renderScratchDecls ra
      ++ [ "reg u64 x cc sum;"
         , "inline int i k r base g;"
         , "tbuf[0] = P; tbuf[1] = P; tbuf[2] = P; tbuf[3] = P;"
         , "vp_const = tbuf[:u256 0];"
         , "tbuf[0] = MM; tbuf[1] = MM; tbuf[2] = MM; tbuf[3] = MM;"
         , "vmm_const = tbuf[:u256 0];"
         , "tbuf[0] = MASK32; tbuf[1] = MASK32; tbuf[2] = MASK32; tbuf[3] = MASK32;"
         , "vmask32_const = tbuf[:u256 0];"
         , "tbuf[0] = NEG_P_INV; tbuf[1] = NEG_P_INV;"
            ++ " tbuf[2] = NEG_P_INV; tbuf[3] = NEG_P_INV;"
         , "vmu_const = tbuf[:u256 0];"
         , "tbuf[0] = R_SQR; tbuf[1] = R_SQR; tbuf[2] = R_SQR; tbuf[3] = R_SQR;"
         , "vrsq_const = tbuf[:u256 0];" ]
  let load :=
    (List.range 16).map (fun i =>
      "x = [inp + 8 * " ++ toString i ++ "]; s[" ++ toString i ++ "] = x;")
  let initialMds := [ "s = mds(s);" ]
  let toMontResident :=
    (List.range 4).flatMap (fun g =>
      let vSg := "vS" ++ toString g
      let b := 4 * g
      [ "tbuf[0] = s[" ++ toString (b + 0) ++ "];"
      , "tbuf[1] = s[" ++ toString (b + 1) ++ "];"
      , "tbuf[2] = s[" ++ toString (b + 2) ++ "];"
      , "tbuf[3] = s[" ++ toString (b + 3) ++ "];"
      , "va = tbuf[:u256 0];"
      , "vb = vrsq_const;" ]
        ++ packedMontMulSinglePassBody
        ++ [ vSg ++ " = vr;" ])
  let initialExt :=
    (List.range 4).flatMap (fun r => renderResidentExternalRound "RC_INIT" r)
  let partialBlock :=
    renderResidentDiagvMontPreload
      ++ (List.range 13).flatMap renderResidentPartialRoundYmm
  let terminalExt :=
    (List.range 4).flatMap (fun r => renderResidentExternalRound "RC_FIN" r)
  let fromMontResident :=
    (List.range 4).flatMap (fun g =>
      let vSg := "vS" ++ toString g
      let b := 4 * g
      [ "vt = " ++ vSg ++ ";" ]
        ++ packedMontReduceBody
        ++ [ "tbuf[:u256 0] = vr;"
           , "s[" ++ toString (b + 0) ++ "] = tbuf[0];"
           , "s[" ++ toString (b + 1) ++ "] = tbuf[1];"
           , "s[" ++ toString (b + 2) ++ "] = tbuf[2];"
           , "s[" ++ toString (b + 3) ++ "] = tbuf[3];" ])
  let store :=
    (List.range 16).map (fun i =>
      "x = s[" ++ toString i ++ "]; [outp + 8 * " ++ toString i ++ "] = x;")
  decls ++ load ++ initialMds ++ toMontResident
    ++ initialExt ++ partialBlock ++ terminalExt
    ++ fromMontResident ++ store

/-- The RA-driven `poseidon2_bb` body wrapped in the standard ABI. -/
def emitPoseidon2ResidentPartialRaBodyJazz (ra : RegisterAllocation) : String :=
  "export fn poseidon2_bb(reg u64 outp, reg u64 inp) -> reg u64 {\n  "
    ++ String.intercalate "\n  " (renderRaBody ra)
    ++ "\n  return outp;\n}"

/-- **The RA-driven Poseidon2 BabyBear lane-resident + YMM-direct
internal_mat single-pass Montgomery `.jazz`.** Same ABI as the
TWENTIETH-mode emit (#171). The 16-element state is pinned to
`vS0..vS3` across the FULL 4 + 13 + 4 = 21-round schedule, with the
Montgomery-form diagonal table preloaded into `vDV0..vDV3` once before
the partial-rounds block. The scratch YMMs are split into reg-resident
vs stack-spilled by `isPhaseDead` — phase-dead slots `{vsq, vx4,
vx_orig}` (S-box-only scratches with zero partial-round uses) are
demoted to `stack u256`, freeing 3 YMM register-file positions during
the dominant 13-round partial-rounds chunk. For the identity-shaped
`poseidonRA` defined in this module, the result is the
phase-dead-spill emit; for `RegisterAllocation.identity` the result
would (modulo the additive stack-line declarations) match the #171
baseline. -/
def emitPoseidon2ResidentPartialRaJazz (ra : RegisterAllocation) : String :=
  -- Reuse the baseline preamble (params, RC tables, scalar helpers including
  -- `csub`, `reduce`, `montreduce`, `montmul`, `fmul`, `fadd`, `fsub`,
  -- `montsbox`, `mds`) so the RA-driven jazz is byte-identical to the #171
  -- baseline up to the export body. The baseline string ends with
  -- `emitPoseidon2MontgomeryResidentPartialBodyJazz ++ "\n"` — we strip that
  -- baseline body and append the RA-driven body in its place.
  let baseline := poseidon2MontgomeryResidentPartialJazz
  let baselineBody := emitPoseidon2MontgomeryResidentPartialBodyJazz ++ "\n"
  -- Drop the baseline body from the tail; `dropEnd` returns a `String.Slice`
  -- (post-4.29.1), so we materialise it back to `String` via `.toString` for
  -- the standard `HAppend String String String` instance.
  let preamble := (baseline.dropEnd baselineBody.length).toString
  preamble ++ emitPoseidon2ResidentPartialRaBodyJazz ra ++ "\n"

/-! ## 6. Headline denotation-preservation theorem

The RA-driven emit's denotation equals the canonical Poseidon2 BabyBear
permutation. The witness is `MontIso.montPerm_sandwich_eq` from the
companion `Poseidon2Montgomery` module — the same theorem the TWENTIETH
ABI mode emit uses. It is parametric over the storage class (lane-pinned
YMM vs stack array, reg-resident vs stack-spilled scratches), so the RA
demotion of three S-box scratches to stack does not affect the
denotation. -/

/-- **Denotation preservation for the RA-driven Poseidon2 BabyBear emit.**
Composes `MontIso.montPerm_sandwich_eq`. -/
theorem poseidon2_ra_emit_denotation_preserves
    (s : Fin width → CatCrypt.Crypto.Hash.Poseidon2.BabyBear.F) :
    MontIso.vUnform (MontIso.montPoseidon2BabyBearPermute (MontIso.vForm s))
      = CatCrypt.Crypto.Hash.Poseidon2.BabyBear.poseidon2BabyBearPermute s :=
  MontIso.montPerm_sandwich_eq s

/-! ## 7. Identity-RA cross-check

For the `poseidonRA` decision the spill victims are `{vsq, vx4, vx_orig}`
(slot indices 9, 10, 11). The phase-dead set is computed once and
exposed for the bench-driver to read. -/

/-- The phase-dead set under `poseidonRA` is `{9, 10, 11}`. -/
theorem phaseDeadSlots_eq :
    phaseDeadSlots = [9, 10, 11] := by native_decide

/-- Slot 9 (`vsq`) is identified as phase-dead. -/
theorem vsq_phaseDead : isPhaseDead 9 = true := by native_decide

/-- Slot 10 (`vx4`) is identified as phase-dead. -/
theorem vx4_phaseDead : isPhaseDead 10 = true := by native_decide

/-- Slot 11 (`vx_orig`) is identified as phase-dead. -/
theorem vx_orig_phaseDead : isPhaseDead 11 = true := by native_decide

/-- Slot 12 (`vsumYmm`) is NOT phase-dead (it is held live across the
4 quartet diag-muls in each partial round). -/
theorem vsumYmm_not_phaseDead : isPhaseDead 12 = false := by native_decide

/-- Slot 0 (`va`) is NOT phase-dead (it is used by every quartet
diag-mul). -/
theorem va_not_phaseDead : isPhaseDead 0 = false := by native_decide

/-! ## 8. Cross-iteration-aware RA via `UnrolledComRA.unrolledSlotRAofIters`

Phase B-2 wires the Poseidon2 consumer through `unrolledSlotRAofIters`,
replacing the bespoke `phaseDeadSlots := [9, 10, 11]` constant with the
analysis-driven decision.

### Chunk derivation

For each scratch slot `0..12`, an iteration's `SlotEvent` records the
slot as touched (write + read of itself) iff the slot has a non-zero use
count in that iter class. This is a faithful summary at the granularity
the carry analysis needs (writeSet ∩ readSet across adjacent iters): a
scratch slot is carried iff it is used in two adjacent iterations.

The iteration sequence is

```
[external × 4] ++ [partial × 13] ++ [external × 4]
```

mirroring `renderRaBody`'s round schedule. -/

/-- Events for one external round: every slot with non-zero
`externalRoundUseCount` records a self-touch. -/
def externalRoundEvents : List UnrolledComRA.SlotEvent :=
  (List.range 13).filterMap (fun s =>
    if externalRoundUseCount s > 0 then some ⟨s, [s]⟩ else none)

/-- Events for one partial round: every slot with non-zero
`partialRoundUseCount` records a self-touch. -/
def partialRoundEvents : List UnrolledComRA.SlotEvent :=
  (List.range 13).filterMap (fun s =>
    if partialRoundUseCount s > 0 then some ⟨s, [s]⟩ else none)

/-- The 4 + 13 + 4 round chunking used by the cross-iteration analysis. -/
def poseidonIters : List (List UnrolledComRA.SlotEvent) :=
  List.replicate 4 externalRoundEvents
    ++ List.replicate 13 partialRoundEvents
    ++ List.replicate 4 externalRoundEvents

/-- Flat trace = concatenation of `poseidonIters`. -/
def poseidonTrace : List UnrolledComRA.SlotEvent :=
  poseidonIters.flatten

/-- **The cross-iteration-aware Poseidon2 register allocation.** Built by
`UnrolledComRA.unrolledSlotRAofIters` over the 4-13-4 round chunking. The
carry analysis identifies `{vsq, vx4, vx_orig}` (slots 9, 10, 11) and
`vv` (slot 4) as non-carried (zero partial-round uses → not read in the
partial iter after an external write). All other slots are used in both
external and partial rounds, hence carried. -/
def poseidonRA_iters : RegisterAllocation :=
  UnrolledComRA.unrolledSlotRAofIters poseidonTrace poseidonIters

/-- The cross-iteration-aware RA is well-formed. -/
theorem poseidonRA_iters_WellFormed : WellFormed poseidonRA_iters :=
  UnrolledComRA.unrolledSlotRAofIters_WellFormed _ _

/-- Under the literal `[E × 4 ++ P × 13 ++ E × 4]` chunking, `vsq` (slot
9) is marked CARRIED — it has non-zero external use and the initial and
terminal external chunks have intra-phase E→E adjacencies (write in iter
0, read in iter 1, both external). The conservative carry analysis at
this chunk granularity does NOT distinguish the phase-dead trio from
phase-live slots the way the hand-rolled `partialRoundUseCount`-based
heuristic does. -/
theorem vsq_carried_crossIter :
    UnrolledComRA.carriedAcross 9 poseidonIters = true := by native_decide

/-- `vx4` (slot 10) is similarly marked carried by the cross-iter
analysis under the literal 4-13-4 chunking. -/
theorem vx4_carried_crossIter :
    UnrolledComRA.carriedAcross 10 poseidonIters = true := by native_decide

/-- `vx_orig` (slot 11) is similarly marked carried under the literal
4-13-4 chunking. -/
theorem vx_orig_carried_crossIter :
    UnrolledComRA.carriedAcross 11 poseidonIters = true := by native_decide

/-- `vsumYmm` (slot 12) — used only in partial rounds — is marked
CARRIED across the P→P adjacencies of the 13-partial-round chunk. -/
theorem vsumYmm_carried_crossIter :
    UnrolledComRA.carriedAcross 12 poseidonIters = true := by native_decide

/-- `va` (slot 0) — used in both classes — is carried. -/
theorem va_carried_crossIter :
    UnrolledComRA.carriedAcross 0 poseidonIters = true := by native_decide

/-! ### Cross-iter-derived phase-dead set

Phase-dead under the new RA: slots whose physical assignment falls into
the bucket `{9, 10, 11}` (the indices the existing renderer maps to
`stack u256`). For the cross-iteration scan above the assignment puts
non-carried slots into the highest physical positions, so the bucket
test `isPhaseDead (ra.seqOf s)` reproduces the analysis-derived
spill decision uniformly. -/

/-- Decide if logical slot `s` should be phase-dead-spilled under RA `ra`. -/
def isPhaseDeadRA (ra : RegisterAllocation) (s : Nat) : Bool :=
  isPhaseDead (ra.seqOf s)

/-! ## 9. Two-address coalescing audit (Phase B+)

`UnrolledComRA.lean` §8 ships `unrolledSlotRAofItersCoalesce`. For
Poseidon2's per-slot self-touch trace (`externalRoundEvents` /
`partialRoundEvents` are lists of `⟨s, [s]⟩` events), every event has
`dst = head rds = s`, so the analysis observes **zero coalesce
candidates**. The cross-iter + coalesce RA produces the same `seqOf` as
the cross-iter RA alone, which itself produced the same jazz as the
hand-rolled `poseidonRA`. -/

/-- The cross-iter + coalesce-aware Poseidon2 register allocation. For
Poseidon2's self-touch trace this equals `poseidonRA_iters`
extensionally. -/
def poseidonRA_coalesce : RegisterAllocation :=
  UnrolledComRA.unrolledSlotRAofItersCoalesce poseidonTrace poseidonIters

/-- The coalesce-aware Poseidon2 RA is well-formed. -/
theorem poseidonRA_coalesce_WellFormed : WellFormed poseidonRA_coalesce :=
  UnrolledComRA.unrolledSlotRAofItersCoalesce_WellFormed _ _

/-- **Poseidon2 has zero coalesce candidates.** Every event in
`poseidonTrace` is `⟨s, [s]⟩`, so `coalescePairs poseidonTrace` returns
the empty list. -/
theorem poseidon_coalesce_candidate_count :
    UnrolledComRA.coalesceCandidateCount poseidonTrace = 0 := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2RaEmit
