/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.VIR.Sntrup761MulEmit
import CatCrypt.Crypto.SecureCompilation.VIR.R3MulEmit

/-!
# ABI maps for the owned-AsmPrinter linear export of the sntrup761 poly-mul kernels

The owned-RA linear path (`JasminLprogExport.Com.toLprogPhysAbi`, task #537)
regenerates a physical-register, two-address `Linear.lprog` from a
`Com jasminDialect` and renders it to AT&T `.s` **directly** via
`LprogAsmPrinter.renderLprogAtt` — no `jasminc`. This module provides the three
producer-side maps so the sntrup761 `Z/q = Z/4591` polynomial-multiply kernel
(`Sntrup761MulEmit.sntrupMulCom`) and the `Z/3` trinary `R3_mult` kernel
(`R3MulEmit.r3MulCom`) take the same owned path the SHA-2 / ChaCha20
bodies do.

## Argument-slot model

`comToLfundef` assigns each input word `i` of `inCtxt = List.replicate 36 r64`
the argument slot `slot = ctxtSize - 1 - i = 35 - i` (the same reversal the
SHA-2 / ChaCha maps document). The sntrup input layout (identical for both
kernels) is:

* inputs `0..15`   — the 16 `a` coefficients          → slots `35..20`
* inputs `16..31`  — the 16 `b` coefficients           → slots `19..4`
* input  `32`      — the Barrett multiplier `m`         → slot  `3`
* input  `33`      — the modulus `q`                    → slot  `2`
* input  `34`      — the Barrett shift immediate        → slot  `1`  (→ #imm)
* input  `35`      — the sign-bit shift immediate `63`  → slot  `0`  (→ #imm)

## C-side ABI (unchanged — the byte-identical KAT contract)

```c
extern uint64_t *sntrup_mul(uint64_t *out, const uint64_t *inp);
extern uint64_t *r3_mul   (uint64_t *out, const uint64_t *inp);
//   inp = [ a[0..15] | b[0..15] | m | q | shiftA | 63 ]   (36 u64 words)
//   out receives the 31 reduced product coefficients out[0..30]
```

so `RSI = inp` and `RDI = out` — exactly the 2-pointer SysV wrapper
`Com.toLprogPhysAbi` emits (`abiArgs = ["RDI","RSI"]`). All operands are U64
(the `regArith _ 64` ops carry the `":64"` tag), so the owned spill stride is
8 bytes (`LprogAsmPrinter.spillCellBytes 64 = 8`) and the `inp`/`out` element
stride is 8 bytes.

The two shift immediates (`m`/`q` are NOT immediates — they are *runtime*
register reads, like `inp[32]`/`inp[33]` in the `.jazz` path) are rendered as
`#imm` operands at producer time (`*ImmSlots`), so they need no memory load.
`m` and `q` (slots 3 and 2) ARE loaded from `inp` (the C harness writes the
Barrett multiplier and modulus into `inp[32]`/`inp[33]`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## sntrup761 `Z/4591` kernel (`sntrupMulCom`) -/

/-- The immediate map for the `Z/4591` `sntrup_mul` export. The two shift
    amounts (`29` for the Barrett `⌊·/2^29⌋`, `63` for the sign-bit cond-sub)
    are inputs `34`/`35`, landing at argument slots `1`/`0`. They are the only
    `.imm` operands; `m`/`q` are runtime loads. -/
def sntrupImmSlots : ImmSlotMap := fun slot =>
  if slot = 1 then some 29        -- input 34 → slot 1 : the `>> 29` Barrett shift
  else if slot = 0 then some 63   -- input 35 → slot 0 : the `>> 63` sign-bit shift
  else none

/-- The `Z/4591` input-load map: argument slot → `(base, byte-offset)`. Slots
    `0`/`1` (the shift immediates) are skipped — covered by `sntrupImmSlots`.
    Slots `2..35` load `inp[35 - slot]` (the De Bruijn input `35 - slot`):
    `q` ← `inp[33]`, `m` ← `inp[32]`, `b[j]` ← `inp[16+j]`, `a[i]` ← `inp[i]`.
    The U64 element stride is 8 bytes. -/
def sntrupInLoadMap : InLoadMap := fun slot =>
  if 2 ≤ slot ∧ slot ≤ 35 then
    let k := 35 - slot     -- the De Bruijn input index (2 ≤ slot ≤ 35 ⇒ 0 ≤ k ≤ 33)
    some ("RSI", k * 8)
  else none

/-- The `Z/4591` output-store map: 31 stores, one per output coefficient. The
    finalize pass (`Sntrup761MulEmit.emitFinalize`) writes `out[0..30]` in order
    as the LAST 31 bindings, so output coefficient `j` is the `j`-th of the last
    31 bindings and is stored to `out[j]` at byte offset `8*j` from `RDI`. -/
def sntrupOutStoreMap : OutStoreMap :=
  (List.range Sntrup761MulEmit.outLen).map (fun j => ("RDI", j * 8))

/-! ## sntrup761 `Z/3` trinary kernel (`r3MulCom`) -/

/-- The immediate map for the `Z/3` `r3_mul` export. Identical structure to the
    `Z/4591` one, except the Barrett shift is `16` (for `q = 3`, `m = ⌊2^16/3⌋`)
    instead of `29`. -/
def r3ImmSlots : ImmSlotMap := fun slot =>
  if slot = 1 then some 16        -- input 34 → slot 1 : the `>> 16` Barrett shift
  else if slot = 0 then some 63   -- input 35 → slot 0 : the `>> 63` sign-bit shift
  else none

/-- The `Z/3` input-load map: identical to `sntrupInLoadMap` (same 36-word input
    layout). -/
def r3InLoadMap : InLoadMap := fun slot =>
  if 2 ≤ slot ∧ slot ≤ 35 then
    let k := 35 - slot
    some ("RSI", k * 8)
  else none

/-- The `Z/3` output-store map: 31 stores, identical layout to the `Z/4591` one. -/
def r3OutStoreMap : OutStoreMap :=
  (List.range R3MulEmit.outLen).map (fun j => ("RDI", j * 8))

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
