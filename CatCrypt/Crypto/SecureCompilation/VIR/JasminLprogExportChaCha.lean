/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ChaChaEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.ChaChaEmit

/-!
# Physical-register export of the ChaCha20 block: concrete no-collision check

`JasminLprogExport` adds the physical-register, two-address export
(`Com.toLprogPhys`) targeting the 15 usable x86-64 GP registers with stack
spill, plus the generic `PhysNoCollision` property and the two-address
denotation lemmas. This module discharges the **concrete** no-collision check
for the ChaCha20-block body (`ChaChaEmit.chachaBlockCom`): the linear-scan
physical assignment never maps two simultaneously-live logical slots to the same
physical slot, so the destructive two-address rewrite never clobbers a live
value.

The check is closed by `native_decide` over the precomputed per-live-slot
summary (axioms `[propext, Classical.choice, Quot.sound]` — the standard
`Decidable`-instance reflection footprint).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ChaChaEmit (chachaBlockCom)

/-- The per-binding logical-slot read/write trace of the ChaCha20-block body, as
    walked by the physical export (`comToLfundef`'s virtual body, then
    `bodyTrace`). 1616 events over a 1655-slot SSA universe; the linear scan
    packs them onto 25 physical slots (15 GP registers `RAX … R15` + 10 stack
    spill slots `k[0] … k[9]`). -/
def chachaPhysTrace : List PhysEvent :=
  bodyTrace (comToLfundef chachaBlockCom).lfd_body

/-- **No-collision for the ChaCha20-block physical allocation.** Any two distinct
    simultaneously-live logical slots of the ChaCha20-block body receive distinct
    physical slots under the linear-scan assignment. This is the KAT-safety
    property: the destructive two-address lowering (`mov dst,src0; op dst,src1`)
    is correct only when `dst` does not share a physical register with a still-live
    `src1` — which `PhysNoCollision` guarantees for all simultaneously-live slots.
    (Closed by `native_decide` over the precomputed summary.) -/
theorem physNoCollisionChaCha : PhysNoCollision chachaPhysTrace :=
  physNoCollision_of_boolB _ (by native_decide)

/-! ## Shift-count immediate substitution

The ChaCha20 ARX rotates feed their (compile-time-constant) shift amount as the
second source of a `SHL`/`SHR`. These resolve to the 7 shift-constant input
arguments at *slots* `32 … 38` (input words 32…38, carrying the distinct shift
amounts `shiftConsts 0 … 6 = 16,12,8,7,20,24,25`; see `ChaChaEmit.initBState`,
where `shc j = inVar (32 + j)`). x86 forces a *register* shift count into `CL`;
an `imm8` count needs no forced register.

Two routes are available to the physical export:

* `chachaImmSlots : ImmSlotMap` — the **slot-based** producer-level map. Keyed
  on the program-root argument slot index (matching `ChaChaEmit.chachaInName`'s
  textual jazz printer, which uses `if 32 ≤ i ∧ i < 39 then …`), this is robust
  against any SSA rename: the shift-constant *operands* are emitted as `.imm`
  at producer time, before the physical pass walks the body.
* `chachaShiftImm : ShiftImmOracle` — the legacy SSA-name-keyed oracle (kept
  for back-compat). The name-based key is brittle when the producer's SSA
  binding names are not literally `a32 … a38` at the SHL/SHR call sites.

The ChaCha bench passes the slot-based `chachaImmSlots`. -/

/-- The slot-based immediate map for the ChaCha20-block export.

    `resolveVar` computes `slot = curDepth - 1 - varIndex v`, so the producer's
    notion of "argument slot" reverses input order: the input `inVar i` (the
    `i`-th binding in `inCtxt = List.replicate 39 r32`) becomes argument slot
    `39 - 1 - i = 38 - i` (and renders as `argName (38 - i) = "a{38-i}"`).

    The 7 shift-constant inputs are `inVar 32 … inVar 38` (per
    `ChaChaEmit.initBState`'s `shc j = inVar (32 + j)`), which therefore land at
    argument *slots* `38 - 32 … 38 - 38 = 6 … 0`. Each holds `shiftConsts j`
    (`= shiftConstNat j`). Mapping back: argument slot `s ∈ [0, 7)` corresponds
    to shift-constant index `j = 38 - 32 - s = 6 - s`, holding
    `shiftConstNat (6 - s)`. -/
def chachaImmSlots : ImmSlotMap := fun slot =>
  if slot < 7 then some (ChaChaEmit.shiftConstNat (6 - slot))
  else none

/-- Legacy SSA-name-keyed shift-count immediate oracle. Kept for back-compat;
    prefer `chachaImmSlots`, which keys on the producer's argument *slot* and
    therefore works regardless of how the SSA binding names get rewritten by
    `physBody`'s remap. -/
def chachaShiftImm : ShiftImmOracle := fun name =>
  -- the shift constants are arguments a32 … a38
  match (List.range 7).find? (fun j => name == argName (32 + j)) with
  | some j => some (ChaChaEmit.shiftConstNat j)
  | none => none

/-! ## ABI prologue/epilogue maps for the 2-pointer SysV signature

The C-side ABI is:

```c
extern void chacha20_block(uint32_t *out, const uint32_t *inp);
```

`RDI = out` holds a pointer to a 16-word output buffer. `RSI = inp` holds a
pointer to a 16-word input buffer carrying the RFC 8439 §2.3.2 initial state
(constants `"expand 32-byte k"`, key, counter, nonce). The 7 ChaCha rotate
shift amounts are NOT in `inp`: the producer renders them as `#imm` operands
at producer time (`chachaImmSlots`), so they need no memory load.

The producer's argument slots map to the source `Com`'s De Bruijn indices via
`slot s = 38 - inVarIndex`. The ChaCha source layout in `inCtxt` is:

* `inVar 0 … inVar 15`   — the 16 state words  → arg slot `38 … 23`
* `inVar 16 … inVar 31`  — the 16 originals    → arg slot `22 …  7`
* `inVar 32 … inVar 38`  — the 7 shift consts  → arg slot ` 6 …  0`  (→ #imm)

The originals are the same byte values as the state (the C harness only
allocates 16 input words; both the "state" slots and the "originals" slots
read from the same `inp[k]` element). The map therefore loads each state slot
from `inp[k]` AND each original slot from `inp[k]`:

```
arg slot 23 (state word 15)  ← inp[15]  ([RSI + 60])
arg slot 24 (state word 14)  ← inp[14]  ([RSI + 56])
...
arg slot 38 (state word  0)  ← inp[ 0]  ([RSI +  0])
arg slot  7 (original 15)    ← inp[15]  ([RSI + 60])
arg slot  8 (original 14)    ← inp[14]  ([RSI + 56])
...
arg slot 22 (original  0)    ← inp[ 0]  ([RSI +  0])
arg slot  0 …  6              skipped — covered by chachaImmSlots
```
-/

/-- The ChaCha20 ABI input-load map: argument slot → `(base, byte-offset)` from
    which the prologue should load the slot's value. Slots 0…6 are skipped
    (they are constant shift amounts, covered by `chachaImmSlots`). -/
def chachaInLoadMap : InLoadMap := fun slot =>
  -- slot 23..38 = state words (`inVar (38 - slot)`); load from inp[38 - slot]
  if 23 ≤ slot ∧ slot ≤ 38 then
    let k := 38 - slot      -- 0..15
    some ("RSI", k * 4)
  -- slot 7..22 = originals (`inVar (38 - slot)`); originals 16..31 → inp[k-16]
  else if 7 ≤ slot ∧ slot ≤ 22 then
    let k := (38 - slot) - 16     -- 0..15
    some ("RSI", k * 4)
  else none

/-- The ChaCha20 ABI output-store map: 16 stores, one per output word. Output
    word `j` is the i-th binding from the end (the feed-forward emits words in
    order 0,1,…,15 as the last 16 bindings), and is stored to `out[j]` at byte
    offset `4 * j` from `RDI`. -/
def chachaOutStoreMap : OutStoreMap :=
  (List.range 16).map (fun j => ("RDI", j * 4))

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
