/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit

/-!
# ABI maps for the owned-RA linear export of Keccak-p[1600,24]

The linear-jasmin owned-RA path (`JasminLprogExport.Com.toLprogPhysAbi`,
task #453/#462/#470) regenerates a physical-register, two-address `Linear.lprog`
from a `Com jasminDialect` and feeds it to the patched jasmin `read_linear` /
`compile_lprog_to_asm`, which then ONLY encodes — no re-allocation. ChaCha20
(#453, 1.80×) and SHA-256 (#470, 1.26×) showed this removes the named-register
scheduling tax. This module provides the three producer-side maps for the
Keccak-p[1600,24] permutation body (`KeccakEmit.keccakF1600Com`) so the same
path applies to Keccak (task #472).

Keccak is **U64 throughout** (24 rounds, 25 × 64-bit state lanes, θ ρ π χ ι).

## Argument-slot model

`comToLfundef` assigns each input word `i` the argument slot
`slot = ctxtSize - 1 - i = nInputs - 1 - i` (the producer's De Bruijn reversal,
same model verified for ChaCha and SHA-256). The Keccak input layout
(`KeccakEmit.keccakF1600Com`'s `inCtxt`, length `nInputs = numSlots +
immList.length = 57 + immList.length`) is:

* inputs `0 .. 24`           — the 25 state lanes `A[x,y]`     → slots `nInputs-1 .. nInputs-25`
* inputs `25 .. 56`          — scratch/parity/B seeds          → (written before read; unloaded)
* inputs `firstImm .. nInputs-1` — the distinct immediates     → `#imm` (`keccakImmSlots`)

The scratch/parity/B seeds (`25 .. 56`) are NOT read before they are written
(`KeccakEmit.initBState` seeds them from input 0 only to type the slot file;
every one is overwritten before any read), so they need neither a memory load
nor an immediate — they map to `none` and are dropped.

The C-side ABI is the canonical 2-pointer SysV signature used by the existing
Keccak KAT harness (`bench/keccak_compare/keccak_ra_kat.c`):

```c
extern uint64_t *keccak_f1600(uint64_t *out, const uint64_t *inp);
//   inp[0..24] = the 25 state lanes (immediate slots are zero-padded, unused)
//   out receives the 25 permuted lanes
```

so `RSI = inp` and `RDI = out`. All operands are U64 (Keccak word width), so the
ABI loads of the 25 state lanes are 8-byte loads (`inp[i]` at byte `8*i`) and the
25 output stores are 8-byte stores (`out[j]` at byte `8*j`). The #470 jasmin
`read_linear` sizes spill/save cells at 8 bytes uniformly, covering Keccak's
U64 spills.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakEmit
  (keccakF1600Com nInputs numSlots firstImm immList)

/-- The Keccak immediate-slot map: argument slot → constant value, rendered as
    `#imm` at producer time.

    The immediates occupy inputs `firstImm .. nInputs-1` (the all-ones NOT mask,
    the 24 round constants, then the deduplicated ρ rotate amounts and their
    `64-n` complements — see `KeccakEmit.immList`). Input `firstImm + n` lands at
    argument slot `nInputs - 1 - (firstImm + n)`, and holds `immList[n]`. -/
def keccakImmSlots : ImmSlotMap := fun slot =>
  -- slot = nInputs - 1 - i ⇒ i = nInputs - 1 - slot. Immediate iff i ≥ firstImm.
  if slot + firstImm ≤ nInputs - 1 then
    -- i = nInputs - 1 - slot ≥ firstImm; immediate offset n = i - firstImm.
    let i := (nInputs - 1) - slot
    some (immList.getD (i - firstImm) 0)
  else none

/-- The Keccak ABI input-load map: argument slot → `(base, byte-offset)`. The 25
    state lanes occupy inputs `0 .. 24` (argument slots `nInputs-25 .. nInputs-1`)
    and are loaded from `inp[i]` (byte offset `8 * i` from `RSI`). The
    scratch/parity/B seeds (inputs `25 .. 56`) and the immediate inputs are not
    loaded (`none`): the seeds are written before read; the immediates are
    rendered as `#imm` by `keccakImmSlots`. -/
def keccakInLoadMap : InLoadMap := fun slot =>
  -- state lane iff i = nInputs-1-slot < 25, i.e. slot ≥ nInputs-25.
  if slot + 25 ≥ nInputs ∧ slot ≤ nInputs - 1 then
    let i := (nInputs - 1) - slot     -- 0..24
    some ("RSI", i * 8)
  else none

/-- The Keccak ABI output-store map: 25 stores, one per output lane `A[j]`.
    Output lane `j` is the `j`-th of the last 25 bindings (`emitOutStage` emits
    lanes `0..24` in order), stored to `out[j]` at byte offset `8 * j` from
    `RDI`. -/
def keccakOutStoreMap : OutStoreMap :=
  (List.range 25).map (fun j => ("RDI", j * 8))

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
