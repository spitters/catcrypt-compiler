/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.VIR.Poseidon2WholePermCom

/-!
# ABI maps for the owned-RA linear export of the Poseidon2-BabyBear permutation

The linear-jasmin owned-RA path (`JasminLprogExport.Com.toLprogPhysAbi`,
task #453/#462/#470/#472) regenerates a physical-register, two-address
`Linear.lprog` from a `Com jasminDialect` and feeds it to the patched jasmin
`read_linear` / `compile_lprog_to_asm`, which then ONLY encodes — no
re-allocation. ChaCha20 (#453, 1.80×), SHA-256 (#470, 1.26×) and Keccak (#472,
1.49×) showed this removes the named-register scheduling tax. This module
provides the producer-side maps for the whole Poseidon2-BabyBear width-16
permutation body (`Poseidon2WholePermCom.poseidon2PermComOut`) so the same path
applies to Poseidon2 (task #504).

Poseidon2-BabyBear is **U64 throughout**: 16 Baby Bear lanes carried as `reg 64`
canonical residues, all field arithmetic on u64 (add / sub / mul / and / shift)
with the reduction realised by the dialect's own `regArith` ops.

## Argument-slot model

`comToLfundef` assigns each input word `i` the argument slot
`slot = ctxtSize - 1 - i = 15 - i` (the producer's De Bruijn reversal, same
model verified for ChaCha / SHA-256 / Keccak). The Poseidon2 input layout
(`Poseidon2WholePermCom.inCtxt = List.replicate 16 r64`, length `16`) is:

* inputs `0 .. 15` — the 16 state lanes `s[0..15]` → slots `15 .. 0`.

Unlike SHA-256 / Keccak, Poseidon2 has **no immediate inputs**: the prime `P`,
fold multiplier `C`, mask `M`, the round constants `RC`, and the internal
diagonal `V` are all materialized inside the body by the dialect's nullary
`regConst` op, so the immediate-slot map is empty.

The C-side ABI is the canonical 2-pointer SysV signature used by the existing
Poseidon2 KAT harness (`bench/poseidon2_compare/poseidon2_kat.c`):

```c
extern uint64_t poseidon2_bb_permute(uint64_t *out, const uint64_t *inp);
//   inp[0..15] = the 16 state lanes (canonical residues in [0, p));
//   out receives the 16 permuted lanes.
```

so `RSI = inp` and `RDI = out`. All operands are U64, so the ABI loads of the
16 lanes are 8-byte loads (`inp[i]` at byte `8*i`) and the 16 output stores are
8-byte stores (`out[j]` at byte `8*j`). The #470 jasmin `read_linear` sizes
spill/save cells at 8 bytes uniformly, covering Poseidon2's U64 spills.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-- The Poseidon2 immediate-slot map: empty. All Baby Bear constants (`P`, `C`,
    `M`, the round constants, the internal diagonal `V`) are materialized inside
    the body via `regConst`, so no argument slot is an immediate. -/
def poseidon2ImmSlots : ImmSlotMap := fun _ => none

/-- The Poseidon2 ABI input-load map: argument slot → `(base, byte-offset)`.
    The 16 state lanes occupy inputs `0 .. 15` (argument slots `15 .. 0`) and are
    loaded from `inp[i]` (byte offset `8 * i` from `RSI`), where the input index
    is `i = 15 - slot`. -/
def poseidon2InLoadMap : InLoadMap := fun slot =>
  if slot ≤ 15 then
    let i := 15 - slot     -- input index 0..15
    some ("RSI", i * 8)
  else none

/-- The Poseidon2 ABI output-store map: 16 stores, one per output lane `s'[j]`.
    Output lane `j` is the `j`-th of the last 16 bindings
    (`Poseidon2WholePermCom.emitOutStage16` emits lanes `0..15` in order), stored
    to `out[j]` at byte offset `8 * j` from `RDI`. -/
def poseidon2OutStoreMap : OutStoreMap :=
  (List.range 16).map (fun j => ("RDI", j * 8))

/-! ## Phase-0 register-allocator translation-validation entry points (#476 RA)

The owned-RA producer proposes the residence map
`Poseidon2WholePermCom.slotTraceArr` (binding ordinal → `Fin 25` residence
class) to coalesce the ≈107 000 fresh-SSA names onto 25 logical slots. The
Phase-0 interference checker (`JasminLprogExport.interferenceOkB`,
`interferenceOk_of_boolB`) runs the precise point-wise liveness over the
**fresh-SSA** body and checks that map.

`poseidon2FreshTrace` is the fresh-SSA per-binding `PhysEvent` trace of the
whole permutation body (one unique slot per binding). `poseidon2ResidenceRho`
is the proposed logical→physical map. The orchestrator runs
`interferenceOkB poseidon2FreshTrace poseidon2ResidenceRho` on the compiled
exe — it is expected to return **`false`** (the residence collapse merges the
16 MDS lanes that are simultaneously live in the external-MDS step, so two
coexisting values are mapped to one class). Running it in-kernel via
`native_decide`/`decide` over the 107k body is intentionally NOT done here (it
would be a multi-minute in-kernel evaluation); it is a compiled `#eval`/run. -/

/-- The fresh-SSA (per-binding) `PhysEvent` trace of the whole Poseidon2
    permutation body — one unique logical slot per binding, before any residence
    coalescing. This is the trace the Phase-0 interference checker scans. -/
def poseidon2FreshTrace : List PhysEvent :=
  bodyTrace
    (comToLfundef Poseidon2WholePermCom.poseidon2PermComOut poseidon2ImmSlots).lfd_body

/-- The proposed logical→physical (residence) map for the owned-RA coalescing:
    fresh-SSA def-slot → `Fin 25` residence class, read off
    `Poseidon2WholePermCom.slotTraceArr`. -/
def poseidon2ResidenceRho : Nat → Nat :=
  proposedRho Poseidon2WholePermCom.slotTraceArr

/-- **Phase-0 checker verdict on the 107k Poseidon2 body** (orchestrator-run via
    the compiled exe): `interferenceOkB poseidon2FreshTrace poseidon2ResidenceRho`.
    Expected `false` — the residence collapse aliases simultaneously-live MDS
    lanes. Provided as a named `Bool` so the orchestrator can `#eval` it. -/
def poseidon2ResidenceCheck : Bool :=
  interferenceOkB poseidon2FreshTrace poseidon2ResidenceRho

/-- **Positive control** (orchestrator-run): the SAME fresh-SSA body under the
    identity map is accepted (`true`) — so the rejection above is the residence
    proposal's fault, not an intrinsically unallocatable body. -/
def poseidon2IdentityCheck : Bool :=
  interferenceOkB poseidon2FreshTrace id

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
