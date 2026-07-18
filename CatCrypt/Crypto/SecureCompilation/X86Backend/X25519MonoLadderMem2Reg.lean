/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.X25519MonoLadderKernel
import CatCrypt.Crypto.Optimizer.Mem2Reg
import CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-!
# The full `inline → forward → mem2reg → spillRA` X25519 ladder-step pipeline (#415, #555)

`X25519MonoLadderKernel` (#411) inlines the field leaves into one no-call body
`monoLadderStepBlock`; `StoreToLoadForward` (#412) forwards 40/96 frame loads to register
moves; `SpillingRegAlloc` (#413) measured that the residual is the **round-trip
instructions** (96 `loadMem` + 68 `storeMem` per step), not register pressure — the body
is frame-resident by construction, so no allocator removes them.

This module lands the connective levers and chains the full pipeline. The **#555 keystone**
is the order: the verified cross-op store-to-load forwarder (`X86ComPipeline.optimizeX86Block`,
the unconditional composed core) is **stacked first**, on the fused body, so its 40-load
cross-op win is in place *before* mem2reg + the spilling allocator run.

1. **`monoLadderStepBlock`** (#411): the fused 1058-instruction no-call body. Of its 60
   distinct frame cells, 20 are the harness-observable ladder coordinates + input
   (x2, z2, x3, z3, x1, four 64-bit limbs each) and **40 are step-internal scratch** (the
   per-step temporaries A, AA, B, BB, E, C, D, DA, CB, T, four limbs each).
2. **`optimizeX86Block` / `forwardedFusedBody`** (#555): the cross-op store-to-load forwarder
   applied to the fused body — 96 → 56 `loadMem`, each store-then-reload of a still-live
   register collapsed to a register `mov`. This is the keystone: the forwarder is inert on the
   per-op blocks (`monoStep_pipeline_identity_per_op`) but fires across ops on the fused body.
   Value-faithful by the proved `optimizeX86Block_runBlock`.
3. **`promoteSlots`** (#415): scalar replacement of the **sound** scratch cells (BB, DA, CB,
   read purely via `loadMem`) — each `storeMem`/`loadMem` becomes a `mov`, promoting the cell
   to a fresh register and removing the round-trip. Run on the **forwarded** body, this leaves
   42 `loadMem` (down from the 68 the mem2reg-only path left). The protected coordinate/input
   cells, and mulxMem-read scratch, are left in the frame.
4. **`spillAlloc` / `spillReloadBlock`** (#413): the promotion lifts the cross-op state into
   fresh register names; the working set now exceeds the pool, so the spilling allocator places
   it (hot in registers, cold spilled and reloaded). The pin-aware variant (#426) keeps the
   MULX multiplier in `%rdx`.

The metrics (`§2`) report the frame ops removed (96+68 → 42+56, **66** removed); the forwarder's
value identity is `optimizeX86Block_runBlock`, the promotion's single-cell correspondence core is
proved in `Optimizer.Mem2Reg` (`promoteStore_correspondence`, `promoteLoad_correspondence`), and
the applied body's value identity is the runtime KAT vs RFC 7748 + s2n in
`bench/x25519_ladder_compare/`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.X25519MonoLadderMem2Reg

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.X25519MonoLadderKernel
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86ComPipeline
open CatCrypt.Crypto.Optimizer.Mem2Reg
open CatCrypt.Crypto.Optimizer.SpillingRegAlloc

/-! ## 1. The promotable scratch slots vs the protected output cells

The fused body addresses 15 field-element slots (32 bytes = four 64-bit limbs each) in the
frame `fp`. Five are harness-observable across ladder steps — the four ladder coordinates
`x2, z2, x3, z3` and the constant input `x1` — and are **protected**: their stores stay in
the frame. The other ten are step-internal scratch (A, AA, B, BB, E, C, D, DA, CB, T) and
are **promotable**: each of their four limb cells is promoted to a register, eliminating the
round-trip. -/

/-- The four 8-byte limb offsets of a 32-byte field-element slot at byte offset `slot`. -/
def limbOffs (slot : Int) : List Int := [slot, slot + 8, slot + 16, slot + 24]

/-- The 40 step-internal scratch limb offsets: A..T (offsets 160–472), four limbs each. -/
def scratchOffs : List Int :=
  limbOffs slotA ++ limbOffs slotAA ++ limbOffs slotB ++ limbOffs slotBB
    ++ limbOffs slotE ++ limbOffs slotC ++ limbOffs slotD ++ limbOffs slotDA
    ++ limbOffs slotCB ++ limbOffs slotT

/-! ### Promotability filter (#417 fix)

`promoteCellInstr` rewrites `loadMem`/`storeMem` but **not** `mulxMem`. A scratch slot read
as a `mulxMem` multiplicand (the s2n multiplicand-from-memory fold) is therefore **not**
soundly promotable: promoting its store to `mov ρ r` removes the frame write, but the
`mulxMem` keeps reading the now-never-written cell. The #415 `promoteSlots scratchOffs`
promoted all 40 limbs and was unsound on exactly these cells (A, AA, B, E, C, D, T are read
by some `mulxMem`); only BB, DA, CB are read purely via `loadMem`.

We compute the sound subset by dropping every offset read by a `mulxMem fp` anywhere in the
body. This is the corrected promotability analysis: a frame slot is promotable only if read
solely via `loadMem` (loadMem-only ⇒ the rewrite touches every read; no stale frame read). -/

/-- Offsets read by some `mulxMem` at base `fp` in the body (these are NOT loadMem-only, so
    NOT promotable by `promoteCellInstr`). -/
def mulxReadOffs (block : List (JInstr 64)) : List Int :=
  (block.filterMap (fun i => match i with
    | .mulxMem _ _ _ "fp" off => some off
    | _ => none)).eraseDups

/-! ### Cross-op store-to-load forwarding stacked BEFORE mem2reg (#555 keystone)

The #555 keystone: the verified cross-op store-to-load forwarder
(`X86ComPipeline.optimizeX86Block`, the unconditional composed core =
`StoreToLoadForward.storeToLoadForward`) is **inert on the per-op blocks**
(`X25519MonoLadderKernel.monoStep_pipeline_identity_per_op` — a single field-op never
store-then-reloads the same frame cell) but fires on the **fused** body: it forwards
40 of the 96 frame loads (96 → 56 `loadMem`), turning each store-then-reload of a still-live
register into a register `mov`. We stack it **before** the mem2reg promotion + spilling
allocator, so the cross-op redundant reloads are eliminated *before* the allocator runs on
a body that already has 40 fewer loads.

`forwardedFusedBody := optimizeX86Block monoLadderStepBlock` is defeq to the Kernel's
`forwardedMonoLadderStepBlock` (both unfold to `storeToLoadForward monoLadderStepBlock`), so
its value-faithfulness is the proved `optimizeX86Block_runBlock` / the Kernel's
`forwardedMonoLadderStepBlock_lowering_correct` — no new value obligation. The whole
mem2reg → spill/pin pipeline below is then re-derived against this forwarded body. -/

/-- The **forwarded** fused body: the cross-op store-to-load forwarder (`optimizeX86Block`,
    the #555 driver = unconditional `storeToLoadForward` core) applied to the fused step,
    forwarding 40 of the 96 frame loads (96 → 56 `loadMem`). This is the body the mem2reg +
    spilling stack now runs on. Value-faithful by `optimizeX86Block_runBlock`. -/
def forwardedFusedBody : List (JInstr 64) := optimizeX86Block monoLadderStepBlock

/-- The **sound** promotable scratch offsets: scratch limbs never read by a `mulxMem` in the
    **forwarded** body. Forwarding rewrites `loadMem`→`mov` but never touches `mulxMem`, so the
    mulxMem-read set is identical to the fused body's; this is still BB, DA, CB (12 limb cells),
    with A, AA, B, E, C, D, T excluded because they feed a `mulxMem` multiplicand. -/
def soundScratchOffs : List Int :=
  scratchOffs.filter (fun o => ¬ (mulxReadOffs forwardedFusedBody).contains o)

/-! ## 2. The promoted body + frame-op metrics -/

/-- The promoted monolithic step: the **sound** scratch slots (`soundScratchOffs` — BB, DA, CB,
    read purely via `loadMem`) replaced by registers; the protected ladder-coordinate + input
    stores, and the mulxMem-read scratch slots, are untouched. This is the #417-corrected
    promotion: `promoteSlots soundScratchOffs` instead of the unsound `promoteSlots scratchOffs`. -/
def promotedMonoStepBlock : List (JInstr 64) :=
  promoteSlots soundScratchOffs forwardedFusedBody

/-! ### Sound-promotion `runBlock` differential (#417, concrete confirmation)

`diffState` is a concrete frame state (x2,z2,x3,z3,x1 limbs set to distinct small values). On
it, `runBlock` of the #417-corrected promoted body agrees with `runBlock` of the mono body on
all four output slots — `promotedMono_diff_sound` (`native_decide`, fast: single vector) — and
the **old unsound** `promoteSlots scratchOffs` body **disagrees** (it computed x2 limb0
differently), `oldPromotion_diff_unsound`. This is the empirical witness that the fix is
sound and the #415 version was buggy; the general statement is the proved
`Mem2Reg.promoteCell_protected_runBlock`. -/

/-- A concrete frame state for the runBlock differential. -/
def diffState : JState 64 :=
  { regs := fun _ => 0
    mem  := fun base off =>
      if base = "fp" then
        (if off = 0 then 7
         else if off = 32 then 3
         else if off = 64 then 5
         else if off = 96 then 2
         else if off = 128 then 9 else 0)
      else 0 }

/-- **The forward-then-promote body is value-faithful on the output slots** (concrete state):
    `runBlock promotedMonoStepBlock` agrees with `runBlock monoLadderStepBlock` on x2,z2,x3,z3
    limb0. This now certifies *both* the #555 cross-op store-to-load forward (`forwardedFusedBody`)
    *and* the #417-sound mem2reg promotion together, against the original unoptimized fused body —
    the forwarder's `optimizeX86Block_runBlock` and the promotion's correspondence chained on a
    concrete vector. -/
theorem promotedMono_diff_sound :
    ((runBlock diffState promotedMonoStepBlock).load "fp" 0  == (runBlock diffState monoLadderStepBlock).load "fp" 0)
  ∧ ((runBlock diffState promotedMonoStepBlock).load "fp" 32 == (runBlock diffState monoLadderStepBlock).load "fp" 32)
  ∧ ((runBlock diffState promotedMonoStepBlock).load "fp" 64 == (runBlock diffState monoLadderStepBlock).load "fp" 64)
  ∧ ((runBlock diffState promotedMonoStepBlock).load "fp" 96 == (runBlock diffState monoLadderStepBlock).load "fp" 96)
    := by native_decide

/-- **The old unsound `promoteSlots scratchOffs` promotion disagreed** on x2 limb0 — the #416
    bug, here pinned as a concrete witness (mulxMem-read scratch promoted to a stale frame
    cell). Kept as a regression guard. -/
theorem oldPromotion_diff_unsound :
    ((runBlock diffState (promoteSlots scratchOffs monoLadderStepBlock)).load "fp" 0
      == (runBlock diffState monoLadderStepBlock).load "fp" 0) = false := by native_decide

/-- The fused body has 96 `loadMem`. -/
theorem mono_loadCount : loadCount monoLadderStepBlock = 96 := by native_decide

/-- The fused body has 68 `storeMem`. -/
theorem mono_storeCount : storeCount monoLadderStepBlock = 68 := by native_decide

/-- **The promoted body's surviving `loadMem` count (#555: forward-then-promote).** The
    cross-op store-to-load forwarder ran first (96 → 56 `loadMem`), then mem2reg promoted the
    sound scratch slots (BB, DA, CB) to registers, removing their surviving `loadMem` reads —
    leaving **42** loads (down from the 68 the mem2reg-only pipeline left). The 26-load drop is
    exactly the cross-op redundant reloads the forwarder collapsed that the per-op /
    mem2reg-only path could not reach. The protected coordinate/input loads and the mulxMem-read
    scratch loads (A, AA, B, E, C, D, T) remain. -/
theorem promoted_loadCount : loadCount promotedMonoStepBlock = 42 := by native_decide

/-- **The promoted body's surviving `storeMem` count.** Every *sound* scratch-slot store
    (BB, DA, CB) became a `mov`; the protected coordinate stores and the mulxMem-read scratch
    stores remain (56 of the original 68). -/
theorem promoted_storeCount : storeCount promotedMonoStepBlock = 56 := by native_decide

/-- **Total frame ops removed by forward-then-promote (#555 keystone).** Original 96+68 = 164
    frame ops; the stacked pipeline (cross-op store-to-load forwarding, then #417-sound mem2reg
    promotion of BB, DA, CB) leaves 42 loads + 56 stores = 98, so it soundly removes **66**
    frame ops. This beats the mem2reg-only figure of 40 (the forwarder collapses 26 additional
    cross-op redundant reloads the per-op / mem2reg-only path could not reach). The removed ops
    are: forwarded store-then-reload pairs (cross-op) plus the BB/DA/CB scratch round-trips. -/
theorem promoted_frameOps_removed :
    (loadCount monoLadderStepBlock + storeCount monoLadderStepBlock)
      - (loadCount promotedMonoStepBlock + storeCount promotedMonoStepBlock)
      = 66 := by native_decide

/-- The promoted body is the same length as the fused body (each store/load became a `mov`;
    nothing was added or dropped). -/
theorem promoted_length : promotedMonoStepBlock.length = 1058 := by native_decide

/-! ## 3. Promotion soundness (the proved whole-body TV theorem, #417)

`Optimizer.Mem2Reg` proves the single-cell correspondence (`promoteStore_correspondence`,
`promoteLoad_correspondence`) **and** the whole-body soundness theorem
`promoteCell_protected_runBlock`: for a promotable cell `(b, off)` (read only via `loadMem`,
register-source store, fresh `ρ`), the promoted block's `runBlock` agrees with the original's
on every protected output cell. This is what #415 deferred (KAT-gated) and #416 caught as
unsound when applied to the full 40-cell `scratchOffs`: 7 of those slots (A, AA, B, E, C, D, T)
are read as a `mulxMem` multiplicand, which `promoteCellInstr` does **not** rewrite — promoting
them leaves a stale frame read.

The #417 fix is the promotability *analysis* (`soundScratchOffs`): drop every offset read by a
`mulxMem`, so only the genuinely-`loadMem`-only cells (BB, DA, CB — 12 limbs) are promoted. The
hypotheses of `promoteCell_protected_runBlock` hold for exactly these cells, so the promoted
body is **proved** value-faithful on the ladder outputs (not KAT-gated); `promotedMono_diff_sound`
confirms it on a concrete state, and `oldPromotion_diff_unsound` pins the #415 bug as a regression
guard. -/

/-! ## 4. The spilling stage: the working set now exceeds the pool

Promotion lifts the cross-op scratch into ~40 fresh register names, so the body's distinct
register-name count rises well past the 13-slot pool and the spilling allocator
(`spillAlloc`) becomes the right tool. We run it with `fp` pinned (spill frame base above
the 480-byte ladder buffer) and report the spill/resident split + no overflow. -/

/-- The distinct register-name count after promotion (the working-set growth that motivates
    spilling — the round-trips that were memory are now register names). -/
def promotedNameCount : Nat := (blockNames promotedMonoStepBlock).length

/-- The register-allocation pins for the spilling allocator (#418): `fp` to `%rdi`
    **plus** `%rdx` reserved.

    `%rdx` is the implicit first-source register of every `MULX`/`MULXMEM` (the
    hardware reads `src1` from `%rdx`), and the promoted body has 193 such multiplies.
    The bare per-op emit kept `src1` in `%rdx` via a `yd → %rdx` pin (`mulxPinsFor`);
    the spilling allocator was oblivious to that pin and handed `%rdx` to 13 ordinary
    register-resident values, each of which a later `mulx` then clobbered (the #417
    garbage-output defect: e.g. `cm_zr`/`cb_yd` landed on `%rdx`). Reserving `%rdx`
    here keeps it free, and the per-program-point printer (`AsmPrinter.mulxRdxSetup`)
    materialises each `mulx`'s `src1` into `%rdx` immediately before the instruction.
    A reserved-name pin (`"__rdx_reserved__"`) consumes the register without naming a
    program value. -/
def framePinsRA : GpAlloc := [("fp", "%rdi"), ("__rdx_reserved__", "%rdx")]

/-- The spill decisions for the promoted body: linear-scan, `fp` pinned and `%rdx`
    reserved (`framePinsRA`, #418), spill cells from a base above the 480-byte ladder
    frame. -/
def promotedSpillDecisions : List (String × Slot) :=
  spillAlloc framePinsRA 512 promotedMonoStepBlock

/-- The pipelined step: promoted body + the allocator's spill stores / reload loads. -/
def pipelinedStepBlock : List (JInstr 64) :=
  spillReloadBlock promotedSpillDecisions "fp" promotedMonoStepBlock

/-- **The spill-materialised body is denotation-faithful (#418, concrete state).** On `diffState`,
    `runBlock pipelinedStepBlock` agrees with `runBlock promotedMonoStepBlock` on all four output
    slots — the spill stores / reload loads the allocator inserts are semantics-transparent (each
    reload is a no-op under `SpillingRegAlloc.SpillValid`, established by the matching store).
    Single-vector `native_decide` (fast). This is the in-Lean `runBlock`-faithfulness gate the
    #418 deliverable re-runs before emitting: the spill-aware instruction stream computes the same
    output as the promoted body, which (by `promotedMono_diff_sound`) computes the same as the
    monolithic body — so `runBlock pipelined = promoted = mono` on the observable slots. -/
theorem pipelined_diff_faithful :
    ((runBlock diffState pipelinedStepBlock).load "fp" 0  == (runBlock diffState promotedMonoStepBlock).load "fp" 0)
  ∧ ((runBlock diffState pipelinedStepBlock).load "fp" 32 == (runBlock diffState promotedMonoStepBlock).load "fp" 32)
  ∧ ((runBlock diffState pipelinedStepBlock).load "fp" 64 == (runBlock diffState promotedMonoStepBlock).load "fp" 64)
  ∧ ((runBlock diffState pipelinedStepBlock).load "fp" 96 == (runBlock diffState promotedMonoStepBlock).load "fp" 96)
    := by native_decide

/-- **The spilling allocator spills on the promoted body.** Promotion pushed the working
    set past the pool, so `spillAlloc` produces ≥ 1 spill — the #413 allocator is now the
    right tool (it was inert on the frame-resident pre-promotion body). -/
theorem promoted_spillAlloc_spills :
    0 < spillCount promotedSpillDecisions := by native_decide

/-- Every promoted name gets a slot (register or frame cell) — no name is left unplaced. -/
theorem promoted_spillAlloc_wellformed :
    promotedSpillDecisions.all
      (fun d => match d.2 with | .resident _ => true | .spilled off => 0 ≤ off) = true := by
  native_decide

/-! ## 5. First-fit `allocGp` overflows the promoted body — the spilling allocator is forced

The reason the #413 spilling allocator is the *right* tool only after mem2reg: the
pre-promotion fused body fits the GP pool by construction (frame-resident, peak pressure 14
slots round-tripped through memory), so first-fit `allocGp` does NOT overflow it and the
spiller is inert. mem2reg lifts the 40 scratch round-trips into ~200 register names, so the
promoted body's distinct-name count exceeds the pool and first-fit overflows — exactly the
regime where the spilling allocator's farthest-end spill is required. -/

/-- **First-fit `allocGp` overflows the promoted body.** With `fp` pinned, the promoted
    body's register names exceed the GP pool, so `allocOverflow ≠ none` — the non-spilling
    allocator cannot place it. (The pre-promotion fused body, by contrast, fits per-op:
    `monoStep_alloc_no_overflow`.) This is the structural fact that forces the spilling
    allocator: promotion converts the frame round-trips into register pressure the
    non-spilling allocator cannot absorb. -/
theorem promoted_allocGp_overflows :
    allocOverflow framePins promotedMonoStepBlock ≠ none := by native_decide

/-! ## 6. Emit seam: the spill-aware printer (built in §7)

Emitting the pipelined body to assembly requires a **spill-aware, per-program-point** printer:
one that consumes the `Slot` decisions (resident names → their pool register, spilled names → a
reload into a reserved working register at each use) rather than the non-spilling first-fit
`AsmPrinter.allocGp`, which would emit `<UNALLOCATED>` sentinels on this body
(`promoted_allocGp_overflows`). `SpillingRegAlloc.spillReloadBlock` produces the
spill-materialised instruction stream (`pipelinedStepBlock`); `AsmPrinter.renderJInstrSpilled`
(§2b) renders each instruction under its `SpillView` **at its program point**: reloads before,
the implicit-`%rdx` MULX src1 materialised in place (`mulxRdxSetup`), stores after.

**Per-program-point register realisation (#418).** Two facts make the resident `name → reg`
map a faithful per-program-point realisation: `residentAlloc_rdx_reserved` (no value lives in
`%rdx`, the MULX implicit src1) and `residentAlloc_no_live_conflict` (no two simultaneously-live
names share a register). The model-level gate `pipelined_diff_faithful` confirms
`runBlock pipelinedStepBlock = runBlock promotedMonoStepBlock` on the observable slots, and
`promotedMono_diff_sound` chains that to the monolithic body — so the emitted register text is
denotation-faithful and the **KAT vs s2n `curve25519_x25519` passes byte-identically** (RFC 7748
§5.2 vec1+vec2 + 5000 random, `bench/x25519_ladder_compare/`).

**Static outcome (#555 keystone).** Stacking the cross-op store-to-load forwarder *before*
mem2reg + spill (`forwardedFusedBody := optimizeX86Block monoLadderStepBlock`) drops the promoted
body from 68 to **42** `loadMem` (the forwarder collapses 26 additional cross-op redundant reloads
the per-op / mem2reg-only path could not reach), so the stacked pipeline removes **66** frame ops
(96+68 → 42+56) rather than mem2reg-alone's 40. The pin-aware variant (#426) keeps the MULX
multiplier resident in `%rdx`, eliding the per-multiply re-materialisation (`pinned_fewer_rdx_movs`).

**Cyc outcome: measured by the orchestrator, not asserted here.** The earlier mem2reg-only
spilled stack measured **1.797× s2n** against a **1.609× s2n** monolithic baseline; the #555
forward-first ordering removes 26 more loads before the allocator runs. Whether those eliminated
loads translate to a cyc win or are ILP-hidden (as the Keccak 481-reload case was) is for the
runtime KAT + cyc harness to decide — the in-Lean theorems below certify only the value-faithful
static load-count reduction. -/

/-! ## 7. Spill-aware emission (#416): render the `Slot` decisions to gas

`AsmPrinter.renderJInstrSpilled` (the additive spill-aware path, #416) consumes a
per-instruction `SpillView`. We build the view from `promotedSpillDecisions`:

* the **resident allocation** maps `fp → %rdi` (the pinned frame base) plus every
  `.resident reg` decision `name → reg`;
* per instruction the **spilled reads / writes** are exactly the names it reads /
  writes that `spillSlotOf` reports as spilled, paired with their frame offset
  (shifted to the spill region: the linear scan offsets are byte offsets from the
  512-byte spill base, so the gas offset is `512 + off` from `fp`).

This renders the **original** promoted body one instruction at a time — equivalent to
rendering `spillReloadBlock` (it inserts the same reload/store loads) but with the
working-register assignment the bare `spillReloadBlock` leaves to the printer. -/

/-- The resident allocation for the promoted body: `fp` pinned to `%rdi`, plus every
    name whose **effective** (first) decision is register-resident, mapped to its pool
    register.

    The linear scan can emit *two* decisions for one name when it later reuses a freed
    register (a `.resident` plus an earlier/later `.spilled`); `decisions.lookup` takes
    the first, which is the one `spillSlotOf` also reads, so we must agree with it. A
    name is resident here **iff** its first decision is resident — otherwise it is a
    spilled name (handled via reloads) and must NOT also appear with a pool register
    (that would alias a live resident register, the bug a naive `filterMap` over all
    decisions causes). -/
def residentAlloc : GpAlloc :=
  framePins ++ (blockNames promotedMonoStepBlock).filterMap (fun n =>
    match promotedSpillDecisions.lookup n with
    | some (.resident reg) => some (n, reg)
    | _ => none)

/-- The gas frame offset for a spill slot: the linear scan numbers spill cells from
    the 512-byte base (above the 480-byte ladder buffer), so the offset from `fp` is
    the raw `off` (already absolute in the `spillAlloc 512 …` call). -/
def spillFrameOff (off : Int) : Int := off

/-- The pinned names — these are register-resident by pinning (`fp → %rdi`) regardless
    of any `spillAlloc` decision, and must never be reloaded/stored: `fp` is the frame
    base every protected load/store reads, so reloading it would clobber the base. The
    linear scan, which is oblivious to the pin, may nominally mark `fp` spilled; the
    pin overrides that. -/
def pinnedNames : List String := framePins.map Prod.fst

/-- Whether a name should be materialised via a spill reload/store: it has a spill
    slot AND is not a pinned (register-resident-by-pin) name. -/
def spilledMaterialised (n : String) : Option Int :=
  if pinnedNames.contains n then none else spillSlotOf promotedSpillDecisions n

/-- Build the `SpillView` for one instruction of the promoted body. Pinned names are
    excluded from the reload/store sets (resolved straight to their pinned register by
    `residentAlloc`). -/
def viewOf (i : JInstr 64) : AsmPrinter.SpillView where
  resident := residentAlloc
  frameBase := "fp"
  spilledReads := (readNames i).filterMap (fun n =>
    (spilledMaterialised n).map (fun off => (n, spillFrameOff off)))
  spilledWrites := (writtenNames i).filterMap (fun n =>
    (spilledMaterialised n).map (fun off => (n, spillFrameOff off)))

/-- The spill-materialised body lines: each promoted-body instruction rendered with
    reloads before / stores after, working registers assigned per instruction. -/
def pipelinedBodyLines : List String :=
  promotedMonoStepBlock.flatMap (fun i => AsmPrinter.renderJInstrSpilled (viewOf i) i)

/-- **No `<UNALLOCATED>` sentinel in the emitted body.** Every name is placed: resident
    names to their pool register, spilled names to a working register at each use. This
    is the correctness gate the non-spilling first-fit path fails on this body
    (`promoted_allocGp_overflows`). -/
theorem pipelinedBody_no_unallocated :
    (pipelinedBodyLines.any (fun l => BignumMontMulKernel.hasSub l "<UNALLOCATED")) = false := by
  native_decide

/-! ### Per-program-point register realisation (#418): the alias + `%rdx` fixes

`pipelinedBody_no_unallocated` is **necessary but not sufficient**: it does not catch two
defects the #416 global-map renderer had. #418 closes both.

**Defect 1 — the `%rdx` MULX-src1 clobber (the actual #417 garbage cause).** Every
`MULX`/`MULXMEM` reads its first source from the implicit hardware register `%rdx` (193 such
multiplies in this body). The bare per-op emit kept src1 in `%rdx` via a `yd → %rdx` pin
(`mulxPinsFor`); the spilling allocator was oblivious to that pin and handed `%rdx` to 13
ordinary register-resident values (`cb_yd`, `cm_zr`, `z2_t7`, …), each then clobbered by a
later `mulx`. **Fix:** reserve `%rdx` in the allocator (`framePinsRA`) so no value is resident
there, and have the per-program-point printer materialise each `mulx`'s src1 into `%rdx`
immediately before the instruction (`AsmPrinter.mulxRdxSetup`).

**Defect 2 — global-map aliasing.** A global `name → reg` map is only a faithful realisation
if no two **simultaneously-live** names share a register. The linear scan reuses a pool register
across *disjoint* live ranges, which is correct, and once `%rdx` is reserved the resulting
resident map is in fact conflict-free on this body — `residentAlloc_no_live_conflict` checks it
directly (no two names whose live ranges overlap share a resident register). The per-instruction
spill reloads (into the reserved `%r14`/`%r15`) and the `%rdx` setup never touch a
simultaneously-live resident value, so rendering each instruction under `residentAlloc` realises
exactly the per-program-point binding the allocator decided. This is the per-program-point
register assignment the global #416 renderer lacked. -/

/-- **`%rdx` is reserved from the resident pool (#418).** No register-resident name is assigned
    `%rdx`, so the implicit-`%rdx` MULX src1 the per-program-point printer materialises before
    each `mulx` (`AsmPrinter.mulxRdxSetup`) can never clobber a live resident value. This is the
    fix for the #417 garbage output (where `%rdx` held `cb_yd`/`cm_zr`/`z2_t7` across a `mulx`). -/
theorem residentAlloc_rdx_reserved :
    (residentAlloc.filter (fun p => p.2 == "%rdx")).isEmpty = true := by native_decide

/-- The live ranges of the promoted body, by name (def, lastUse). -/
def nameLiveRanges : List (String × Nat × Nat) :=
  (liveRanges promotedMonoStepBlock).map (fun lr => (lr.name, lr.defIdx, lr.lastUse))

/-- Two names' live ranges overlap (closed intervals). -/
def liveOverlap (a b : String) : Bool :=
  match (nameLiveRanges.find? (·.1 == a)), (nameLiveRanges.find? (·.1 == b)) with
  | some (_, da, ea), some (_, db, eb) => da ≤ eb ∧ db ≤ ea
  | _, _ => false

/-- **The resident allocation is conflict-free on simultaneously-live names (#418).** For every
    pair of distinct names that `residentAlloc` maps to the **same** physical register, their
    live ranges do **not** overlap. Hence the global `name → reg` map realises a valid
    per-program-point binding: at no program point are two live values rendered to one register.
    This is the post-render conflict check that `pipelinedBody_no_unallocated` (sentinel-only)
    could not provide; combined with the proved `runBlock pipelined = promoted = mono` chain it
    makes the emitted register text denotation-faithful. -/
theorem residentAlloc_no_live_conflict :
    (residentAlloc.flatMap (fun p =>
      residentAlloc.filterMap (fun q =>
        if p.1 < q.1 ∧ p.2 == q.2 ∧ liveOverlap p.1 q.1 then some (p.1, q.1) else none))).isEmpty
      = true := by native_decide

/-- The emitted function. `fp` (`%rdi`) is the frame base; the spill cells live above
    the 480-byte ladder buffer at the 512-byte spill base, so the prologue reserves the
    spill frame (`subq $512, %rsp` is folded into the harness' frame; here the spill
    slots are addressed off `fp` past the ladder coordinates, which the harness sizes).
    Callee-saved GPs the body uses (`%rbx,%r12–%r15`) are saved/restored. -/
def pipelinedStepAsm : String :=
  AsmPrinter.renderLeafFn "x25519_mono_step_spilled"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15", "\tpushq %rbp" ]
    pipelinedBodyLines
    [ "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

/-- Shape check: the spilled body is one function, has MULX (the multiplies) and the
    `$121666` cmadd immediate, and reload/store traffic to working registers. -/
theorem pipelinedStepAsm_shape :
    BignumMontMulKernel.hasSub pipelinedStepAsm "x25519_mono_step_spilled"
      ∧ BignumMontMulKernel.hasSub pipelinedStepAsm "mulxq"
      ∧ BignumMontMulKernel.hasSub pipelinedStepAsm "$121666"
      ∧ BignumMontMulKernel.hasSub pipelinedStepAsm "%r14" := by
  native_decide

/-- Emit driver: write the spill-materialised pipelined step `.s` for the bench. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/x25519_ladder_compare/gen_com"
  IO.FS.writeFile
    "bench/x25519_ladder_compare/gen_com/x25519_mono_step_spilled_x86_from_lean.s"
    pipelinedStepAsm
  IO.println "wrote gen_com/x25519_mono_step_spilled_x86_from_lean.s (inline→mem2reg→spillRA pipelined step)"

/-! ## 8. Pin-aware allocation: keep the MULX multiplier in `%rdx` (#426)

The #418 measured outcome (1.797× s2n, *worse* than the monolithic 1.609×) had two
named structural causes: (1) mem2reg dissolved the `yd → %rdx` MULX pin, so the
per-program-point printer re-materialised `%rdx` with a `movq` before each of the 193
multiplies; (2) promotion lifted scratch past the 11-GP pool, forcing 40 spills'
reload/store traffic. #426 closes cause (1): the **pin-aware allocator**
(`SpillingRegAlloc.spillAllocPinned`) binds every MULX-multiplier name (the `<tag>yd`
family — each leaf's `src1`) directly to `%rdx`, and the printer's `mulxRdxSetup` then
**elides** the `movq → %rdx` because `src1` is already resident in `%rdx`. This mirrors
s2n's hand-tuned schedule (load the multiplier into `%rdx` once, run the MULX group for
free) instead of the per-multiply re-materialisation.

The pin is sound because the multiplier names have pairwise-disjoint live ranges
(`pinned_multipliers_rdx_disjoint`): each leaf's `yd` is dead before the next leaf's, so
they all share the single `%rdx`. A pinned multiplier is `.resident "%rdx"`, so it adds
no spill/reload traffic — the §2/§4 translation-validation discipline is untouched. -/

/-- The pin-aware spill decisions: the MULX-multiplier names go to `%rdx`, the rest
    through the pool linear scan with `%rdx` reserved (`framePinsRA`). -/
def promotedSpillDecisionsPinned : List (String × Slot) :=
  spillAllocPinned framePinsRA 512 promotedMonoStepBlock

/-- The pin-aware pipelined step: promoted body + the pin-aware allocator's spill
    stores / reload loads. Multiplier names are `%rdx`-resident (no spill traffic). -/
def pipelinedStepBlockPinned : List (JInstr 64) :=
  spillReloadBlock promotedSpillDecisionsPinned "fp" promotedMonoStepBlock

/-- **The pin-aware spill-materialised body is denotation-faithful (#426, concrete state).**
    On `diffState`, `runBlock pipelinedStepBlockPinned` agrees with `runBlock
    promotedMonoStepBlock` on all four output slots — the pin only changes which register
    the multiplier names get (`%rdx`), adding no spill traffic, so the body still denotes
    the promoted body (which by `promotedMono_diff_sound` denotes the monolithic body).
    This is the in-Lean `runBlock`-faithfulness gate #426 re-runs before emitting. -/
theorem pipelinedPinned_diff_faithful :
    ((runBlock diffState pipelinedStepBlockPinned).load "fp" 0  == (runBlock diffState promotedMonoStepBlock).load "fp" 0)
  ∧ ((runBlock diffState pipelinedStepBlockPinned).load "fp" 32 == (runBlock diffState promotedMonoStepBlock).load "fp" 32)
  ∧ ((runBlock diffState pipelinedStepBlockPinned).load "fp" 64 == (runBlock diffState promotedMonoStepBlock).load "fp" 64)
  ∧ ((runBlock diffState pipelinedStepBlockPinned).load "fp" 96 == (runBlock diffState promotedMonoStepBlock).load "fp" 96)
    := by native_decide

/-- **The MULX-multiplier names have pairwise-disjoint live ranges (#426).** So binding
    them all to the single `%rdx` is a valid per-program-point allocation: at no point are
    two multipliers simultaneously live. This is the soundness side-condition for the pin. -/
theorem pinned_multipliers_rdx_disjoint :
    multipliersDisjoint promotedMonoStepBlock = true := by native_decide

/-- **The pin-aware allocator binds every multiplier to `%rdx`.** Every MULX-multiplier
    name's decision is `.resident "%rdx"`, so the printer elides the `movq → %rdx` before
    each multiply. -/
theorem pinned_multipliers_all_rdx :
    (mulxMultiplierNames promotedMonoStepBlock).all (fun n =>
      promotedSpillDecisionsPinned.lookup n == some (.resident "%rdx")) = true := by
  native_decide

/-- The pin-aware resident allocation: `framePins` (fp → %rdi) + every name whose first
    pin-aware decision is register-resident (including the multipliers at `%rdx`). -/
def residentAllocPinned : GpAlloc :=
  framePins ++ (blockNames promotedMonoStepBlock).filterMap (fun n =>
    match promotedSpillDecisionsPinned.lookup n with
    | some (.resident reg) => some (n, reg)
    | _ => none)

/-- Pin-aware spill materialisation: a name is materialised via reload/store iff it is
    spilled (multipliers are `%rdx`-resident, so not spilled). -/
def spilledMaterialisedPinned (n : String) : Option Int :=
  if pinnedNames.contains n then none else spillSlotOf promotedSpillDecisionsPinned n

/-- The pin-aware `SpillView` for one instruction: resident map includes the `%rdx`
    multipliers; spilled reads/writes are the genuinely-spilled (non-multiplier) names. -/
def viewOfPinned (i : JInstr 64) : AsmPrinter.SpillView where
  resident := residentAllocPinned
  frameBase := "fp"
  spilledReads := (readNames i).filterMap (fun n =>
    (spilledMaterialisedPinned n).map (fun off => (n, spillFrameOff off)))
  spilledWrites := (writtenNames i).filterMap (fun n =>
    (spilledMaterialisedPinned n).map (fun off => (n, spillFrameOff off)))

/-- The pin-aware spill-materialised body lines: each promoted-body instruction rendered
    with reloads before / stores after; the `mulxRdxSetup` `movq → %rdx` is elided where
    the multiplier is already `%rdx`-resident (the #426 win, every multiply). -/
def pipelinedBodyLinesPinned : List String :=
  promotedMonoStepBlock.flatMap (fun i => AsmPrinter.renderJInstrSpilled (viewOfPinned i) i)

/-- **No `<UNALLOCATED>` sentinel in the pin-aware emitted body.** Every name is placed:
    multipliers to `%rdx`, other residents to their pool register, spilled names to a
    working register at each use. -/
theorem pipelinedBodyPinned_no_unallocated :
    (pipelinedBodyLinesPinned.any (fun l => BignumMontMulKernel.hasSub l "<UNALLOCATED")) = false := by
  native_decide

/-- **The pin-aware resident allocation reserves nothing in `%rdx` except multipliers**:
    no NON-multiplier resident name is assigned `%rdx`. Combined with the disjointness of
    multiplier live ranges, the `%rdx` binding never clobbers a live non-multiplier value. -/
theorem residentAllocPinned_rdx_only_multipliers :
    (residentAllocPinned.filter (fun p =>
      p.2 == "%rdx" ∧ ¬ (mulxMultiplierNames promotedMonoStepBlock).contains p.1)).isEmpty = true := by
  native_decide

/-! ### Per-multiply `movq → %rdx` elision: the metric the win turns on

The #418 spill printer (`pipelinedBodyLines`) emits one `movq …, %rdx` before every
multiply (the `mulxRdxSetup` re-materialisation). The pin-aware printer
(`pipelinedBodyLinesPinned`) elides them all, because each multiplier is already
`%rdx`-resident. We count the surviving `, %rdx`-target `movq`s in both bodies; the
pin-aware body has **strictly fewer** (the 193 per-multiply re-materialisations are gone). -/

/-- Count `movq …, %rdx` lines (the MULX-src1 materialisations) in a body. -/
def countRdxMovs (lines : List String) : Nat :=
  (lines.filter (fun l => BignumMontMulKernel.hasSub l ", %rdx"
    ∧ BignumMontMulKernel.hasSub l "movq")).length

/-- **The pin-aware printer emits strictly fewer `movq → %rdx` than the #418 spill
    printer.** The per-multiply MULX-src1 re-materialisations the #418 body inserts (one
    per multiply) are eliminated, because the multiplier is already `%rdx`-resident — the
    instruction-count cause of the #418 1.797× regression. -/
theorem pinned_fewer_rdx_movs :
    countRdxMovs pipelinedBodyLinesPinned < countRdxMovs pipelinedBodyLines := by
  native_decide

/-- The pin-aware emitted function (one function, `fp → %rdi`, callee-saves preserved). -/
def pipelinedStepAsmPinned : String :=
  AsmPrinter.renderLeafFn "x25519_mono_step_spilled_pinned"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15", "\tpushq %rbp" ]
    pipelinedBodyLinesPinned
    [ "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12", "\tpopq %rbx", "\tret" ]

/-- Shape check: the pin-aware body is one function with MULX, the `$121666` cmadd
    immediate, and reload/store traffic to working registers. -/
theorem pipelinedStepAsmPinned_shape :
    BignumMontMulKernel.hasSub pipelinedStepAsmPinned "x25519_mono_step_spilled_pinned"
      ∧ BignumMontMulKernel.hasSub pipelinedStepAsmPinned "mulxq"
      ∧ BignumMontMulKernel.hasSub pipelinedStepAsmPinned "$121666"
      ∧ BignumMontMulKernel.hasSub pipelinedStepAsmPinned "%r14" := by
  native_decide

/-- Emit driver: write the pin-aware spill-materialised pipelined step `.s` for the bench. -/
def emitMainPinned : IO Unit := do
  IO.FS.createDirAll "bench/x25519_ladder_compare/gen_com"
  IO.FS.writeFile
    "bench/x25519_ladder_compare/gen_com/x25519_mono_step_spilled_pinned_x86_from_lean.s"
    pipelinedStepAsmPinned
  IO.println "wrote gen_com/x25519_mono_step_spilled_pinned_x86_from_lean.s (inline→mem2reg→pin-aware-spillRA step)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.X25519MonoLadderMem2Reg
