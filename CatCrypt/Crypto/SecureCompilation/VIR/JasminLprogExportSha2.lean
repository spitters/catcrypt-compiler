/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit

/-!
# ABI maps for the owned-RA linear export of the SHA-256 compression

The linear-jasmin owned-RA path (`JasminLprogExport.Com.toLprogPhysAbi`,
task #453/#462) regenerates a physical-register, two-address `Linear.lprog`
from a `Com jasminDialect` and feeds it to the patched jasmin
`read_linear` / `compile_lprog_to_asm`, which then ONLY encodes — no
re-allocation. ChaCha20 (#453) showed this removes the named-register
scheduling tax (1.80×). This module provides the three producer-side maps
for the SHA-256 compression body (`Sha2Emit.compressCom sha256Spec`) so the
same path applies to SHA-256.

## Argument-slot model

`comToLfundef` assigns each input word `i` the argument slot
`slot = ctxtSize - 1 - i = 269 - i` (verified empirically by the slot probe:
input `0 → slot 269`, input `i → slot 269 - i`). The SHA-256 input layout
(`Sha2Emit.compressCom`'s `inCtxt`) is:

* inputs `0..15`   — the 16 message words `M[0..15]`    → slots `269..254`
* inputs `16..23`  — the 8 chaining words `H[0..7]`     → slots `253..246`
* inputs `24..87`  — the 64 round constants `K[0..63]`  → slots `245..182`
* input  `199`     — the all-ones mask                  → slot  `70`
* inputs `200+n`   — the shift-amount literals `n`       → slot  `69 - n`

The C-side ABI is the canonical 2-pointer SysV signature used by the existing
KAT harness (`bench/sha2_compare/sha2_kat.c`):

```c
extern uint32_t *sha256_compress(uint32_t *out, const uint32_t *inp);
//   inp = [ M[0..15] | H[0..7] | K[0..63] ]   (88 u32 words)
//   out receives H'[0..7]
```

so `RSI = inp` and `RDI = out`. The all-ones mask and shift amounts are NOT in
`inp`: the producer renders them as `#imm` operands (`sha256ImmSlots`), so they
need no memory load. All operands are U32 (SHA-256 word width), matching the
linear path's `default_ws = U32` and 4-byte `k.N` spill slots, so no jasmin-side
width extension is needed.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
  (compressCom sha256Spec sha512Spec ctxtSize allOnesIdx)
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit.Resident (kConst)

/-- The SHA-256 immediate-slot map: argument slot → constant value, rendered as
    `#imm` at producer time.

    * slot `70` (input `199 = allOnesIdx`) → the all-ones mask `2^32 - 1`;
    * slot `s` with `39 ≤ s ≤ 69` (input `200 + n`, `n = 69 - s`) → the
      shift-amount literal `n`.

    The shift amounts are fed as the second source of `SHL`/`SHR` (x86 forces a
    register shift count into `CL`; an `#imm8` count needs no forced register);
    the all-ones mask is fed as the second source of `XOR` (a legal `XOR r/m,
    imm32`). -/
def sha256ImmSlots : ImmSlotMap := fun slot =>
  if slot = ctxtSize - 1 - allOnesIdx then       -- slot 70 = input 199 (mask)
    some (2 ^ 32 - 1)
  else if 39 ≤ slot ∧ slot ≤ 69 then             -- shift-amount literals
    some (69 - slot)                              -- input 200+n ↦ slot 69-n
  else none

/-- The SHA-256 ABI input-load map: argument slot → `(base, byte-offset)`. The
    message words (slots `254..269`), chaining words (slots `246..253`), and
    round constants (slots `182..245`) are loaded from `inp[269 - slot]` (byte
    offset `4 * (269 - slot)` from `RSI`). Slots `0..181` are skipped (constants
    covered by `sha256ImmSlots`, or unused). -/
def sha256InLoadMap : InLoadMap := fun slot =>
  if 182 ≤ slot ∧ slot ≤ ctxtSize - 1 then
    let k := (ctxtSize - 1) - slot     -- input index 0..87
    some ("RSI", k * 4)
  else none

/-- The SHA-256 ABI output-store map: 8 stores, one per output word `H'[j]`.
    Output word `j` is the `j`-th of the last 8 bindings (`emitFeed` emits words
    `0..7` in order), stored to `out[j]` at byte offset `4 * j` from `RDI`. -/
def sha256OutStoreMap : OutStoreMap :=
  (List.range 8).map (fun j => ("RDI", j * 4))

/-! ## SHA-512 maps (task #475)

SHA-512 (`Sha2Emit.sha512Spec`) shares the exact input layout with SHA-256 —
`ctxtSize = 270`, `allOnesIdx = 199`, message words `0..15`, chaining words
`16..23`, shift literals at `200 + n`, mask at `199` — and differs only in:

* **word width** U64 (`Rw 64`): the body's `regArith _ 64` ops carry the
  `":64"` tag (`JasminLprogExport.opToLinstrR`/`withWidthTag`), so the ABI
  input loads of the 16 + 8 + 80 = 104 words are 8-byte (`inp[i]` at byte
  `8*i`) and the 8 output stores are 8-byte (`out[j]` at byte `8*j`), exactly
  as in the Keccak U64 maps (`JasminLprogExportKeccak`);
* **round count** 80 (vs 64): the round constants `K[0..79]` occupy inputs
  `24..103` → argument slots `269..166` (vs SHA-256's `24..87` → `245..182`);
* **mask value** `2^64 - 1` (vs `2^32 - 1`), routed as a wide `movabs`
  immediate by `read_linear`'s `reloadScratch2` path (same as Keccak's NOT
  mask);
* **shift amounts** the SHA-512 sigma rotates `(28,34,39)/(14,18,41)/
  (1,8,7)/(19,61,6)` and their `64-n` complements range over `n ∈ [1,63]`
  (vs SHA-256's `[2,30]`), so the immediate-slot shift window is wider
  (`6 ≤ slot ≤ 68`, i.e. input `200+n`, `n = 69 - slot`).

The C-side ABI is the canonical 2-pointer SysV signature used by the existing
SHA-512 KAT harness:

```c
extern uint64_t *sha512_compress(uint64_t *out, const uint64_t *inp);
//   inp = [ M[0..15] | H[0..7] | K[0..79] ]   (104 u64 words)
//   out receives H'[0..7]
```

so `RSI = inp` and `RDI = out`. -/

/-- The SHA-512 immediate-slot map: argument slot → constant value, rendered as
    `#imm` at producer time.

    * slot `70` (input `199 = allOnesIdx`) → the all-ones mask `2^64 - 1`
      (a wide U64 immediate; `read_linear` materialises it via a `movabs`
      through `reloadScratch2`, as for Keccak's NOT mask);
    * slot `s` with `6 ≤ s ≤ 68` (input `200 + n`, `n = 69 - s ∈ [1,63]`) → the
      shift-amount literal `n` (rendered as `#imm8`, fed to `SHL`/`SHR`).

    Slot `69` (input `200`, shift amount `0`) is unused — every SHA-512 rotate
    amount and its `64-n` complement is in `[1,63]`. -/
def sha512ImmSlots : ImmSlotMap := fun slot =>
  if slot = ctxtSize - 1 - allOnesIdx then       -- slot 70 = input 199 (mask)
    some (2 ^ 64 - 1)
  else if 6 ≤ slot ∧ slot ≤ 68 then              -- shift-amount literals (1..63)
    some (69 - slot)                              -- input 200+n ↦ slot 69-n
  else none

/-- The SHA-512 ABI input-load map: argument slot → `(base, byte-offset)`. The
    message words (slots `254..269`), chaining words (slots `246..253`), and
    round constants `K[0..79]` (slots `166..245`) are loaded from `inp[269 -
    slot]` at byte offset `8 * (269 - slot)` from `RSI` (U64, 8-byte words).
    Slots `0..165` are skipped (constants covered by `sha512ImmSlots`, or
    unused). -/
def sha512InLoadMap : InLoadMap := fun slot =>
  if 166 ≤ slot ∧ slot ≤ ctxtSize - 1 then
    let k := (ctxtSize - 1) - slot     -- input index 0..103
    some ("RSI", k * 8)
  else none

/-- The SHA-512 ABI output-store map: 8 stores, one per output word `H'[j]`.
    Output word `j` is the `j`-th of the last 8 bindings (`emitFeed` emits words
    `0..7` in order), stored to `out[j]` at byte offset `8 * j` from `RDI`
    (U64, 8-byte words). -/
def sha512OutStoreMap : OutStoreMap :=
  (List.range 8).map (fun j => ("RDI", j * 8))

/-! ## Resident ABI maps (owned `_resident` / `_resident_wp` flip, task #179/#180)

The state-resident KAT harness (`bench/sha2_compare/sha2_vs_hacl_resident.c`,
lines 22-24) calls

```c
extern uint32_t *sha256_compress_resident(uint32_t *out, const uint32_t *inp);
//   inp = [ M[0..15] | H[0..7] ]   (24 u32 words — NO K[] table)
extern uint64_t *sha512_compress_resident(uint64_t *out, const uint64_t *inp);
//   inp = [ M[0..15] | H[0..7] ]   (24 u64 words)
```

i.e. the message + chaining words only; the 64/80 round constants `K[t]` are
**in-body immediates**, not a passed-in table. This is exactly what the owned
`Com.toLprogPhysAbi` ImmSlotMap path renders: an argument slot covered by the
ImmSlotMap is emitted as an `LOperand.imm` at producer time, so it never needs a
memory load.

The owned resident emit therefore reuses the **same scalar `compressCom`** body
(which already expands the schedule `W[16..N-1]` in-kernel from `M[0..15]` via
`emitSched` — `compressCom` does NOT take `W` as input) but swaps the ABI:

* `*ResidentInLoadMap` — load ONLY inputs `0..23` (`M | H`, slots `246..269`)
  from `inp`, at byte offset `(269 - slot)·cellBytes` from `RSI` (the SAME
  offset formula as the scalar map, restricted to the first 24 words);
* `*ResidentImmSlots` — render the mask + shift literals (as the scalar
  immSlots do) AND the round constants `K[0..rounds-1]` (slots covering inputs
  `24..23+rounds`) as immediates with their FIPS 180-4 values via `kConst`.

A K-immediate appears as the second source of `T1 += K[t]` (an `ADD`). On the
U32 (SHA-256) path `add r32, imm32` accepts any 32-bit immediate; on the U64
(SHA-512) path a wide `K[t] ≥ 2^31` is routed through `R14` by
`JasminLprogExport.materializeWideImm` (the `MOV:64` arm of `lowerTwoAddr`),
exactly as Keccak's ι round-constant XOR is. So no new legalization is needed —
only the two ABI maps below. The body (and hence the FIPS 180-4 digest) is
byte-identical to the scalar owned emit; only the K storage class (immediate vs
memory) and the `inp` width (24 vs 88/104) differ. -/

/-- The SHA-256 resident immediate-slot map: the scalar `sha256ImmSlots`
    (mask at slot 70, shift literals at slots 39..69) PLUS the 64 round
    constants `K[0..63]` rendered as immediates. Input `24 + t = K[t]` lands at
    argument slot `269 - (24 + t) = 245 - t`, so slot `s ∈ [182, 245]` carries
    `K[245 - s]`. -/
def sha256ResidentImmSlots : ImmSlotMap := fun slot =>
  if 182 ≤ slot ∧ slot ≤ 245 then
    some (kConst sha256Spec (245 - slot))     -- K[245 - slot]
  else sha256ImmSlots slot

/-- The SHA-256 resident input-load map: load ONLY inputs `0..23` (message words
    `M[0..15]` at slots `254..269`, chaining words `H[0..7]` at slots `246..253`)
    from `inp[269 - slot]` at byte offset `4 · (269 - slot)`. Slots `≤ 245`
    (the K table) are NOT loaded — they are immediates via
    `sha256ResidentImmSlots`. -/
def sha256ResidentInLoadMap : InLoadMap := fun slot =>
  if 246 ≤ slot ∧ slot ≤ ctxtSize - 1 then
    let k := (ctxtSize - 1) - slot     -- input index 0..23
    some ("RSI", k * 4)
  else none

/-- The SHA-512 resident immediate-slot map: the scalar `sha512ImmSlots`
    (mask + shift literals) PLUS the 80 round constants `K[0..79]` as
    immediates. Input `24 + t = K[t]` lands at slot `245 - t`, so slot
    `s ∈ [166, 245]` carries `K[245 - s]`. Wide values are materialised through
    `R14` by `materializeWideImm` (the `ADD:64` path). -/
def sha512ResidentImmSlots : ImmSlotMap := fun slot =>
  if 166 ≤ slot ∧ slot ≤ 245 then
    some (kConst sha512Spec (245 - slot))     -- K[245 - slot]
  else sha512ImmSlots slot

/-- The SHA-512 resident input-load map: load ONLY inputs `0..23` (`M | H`,
    slots `246..269`) from `inp[269 - slot]` at byte offset `8 · (269 - slot)`
    (U64, 8-byte words). The K table (slots `≤ 245`) is immediates. -/
def sha512ResidentInLoadMap : InLoadMap := fun slot =>
  if 246 ≤ slot ∧ slot ≤ ctxtSize - 1 then
    let k := (ctxtSize - 1) - slot     -- input index 0..23
    some ("RSI", k * 8)
  else none

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
