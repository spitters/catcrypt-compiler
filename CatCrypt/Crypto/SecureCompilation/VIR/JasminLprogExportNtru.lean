/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.VIR.Ntruhrss701MulEmit

/-!
# ABI maps for the owned-AsmPrinter linear export of the ntruhrss701 poly-mul kernel

The owned-RA linear path (`JasminLprogExport.Com.toLprogPhysAbi`, task #537/#656)
regenerates a physical-register, two-address `Linear.lprog` from a
`Com jasminDialect` and renders it to AT&T `.s` **directly** via
`LprogAsmPrinter.renderLprogAtt` — no `jasminc`. This module provides the
producer-side maps so the ntruhrss701 cyclic ring-multiply kernel
(`Ntruhrss701MulEmit.ntruMulCom`, the `Z/8192[x]/(x^16 − 1)` ring MAC,
FRONT-COMPILED via `translateDialectControl` + `cryptoDialectToJasminCom`) takes
the same owned path the SHA-2 / ChaCha20 / sntrup761 bodies do.

## Argument-slot model

`comToLfundef` assigns each input word `i` of `inCtxt = List.replicate 33 r64`
the argument slot `slot = ctxtSize - 1 - i = 32 - i` (the same reversal the
SHA-2 / ChaCha / sntrup maps document). The ntruhrss input layout is:

* inputs `0..15`   — the 16 `a` coefficients   → slots `32..17`
* inputs `16..31`  — the 16 `b` coefficients   → slots `16..1`
* input  `32`      — unused pad word            → slot  `0`  (never read)

The body is **uniformly U64** (the front lowers the `SExpr` word math as
`regArith _ 64`; the `Z/8192` mask `& 8191` is a front-materialised in-body
constant), so the owned spill stride is 8 bytes and the `inp`/`out` element
stride is **8 bytes** (`u64`). The two pointer args stay 64-bit
(`abiTyin = [64, 64]`).

## C-side ABI (the byte-identical KAT contract)

```c
extern uint64_t *ntru_mul(uint64_t *out, const uint64_t *inp);
//   inp = [ a[0..15] | b[0..15] | <unused> ]   (33 u64 words)
//   out receives the 16 reduced product coefficients out[0..15]
```

so `RSI = inp` and `RDI = out` — exactly the 2-pointer SysV wrapper
`Com.toLprogPhysAbi` emits (`abiArgs = ["RDI","RSI"]`). The mask `8191` is a
body constant (no `.imm` arg slot, no memory load); `inp[32]` is never read
(the KAT harness writes `inp[32] = 0`); `a`/`b` are loaded from `inp`
(`ntruInLoadMap`).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

/-! ## ntruhrss701 `Z/8192` kernel (`ntruMulCom`) -/

/-- The immediate map for the `Z/8192` `ntru_mul` export: none. The `& 8191`
    mask constant is materialised by the front as an in-body `regConst`
    binding, so no argument slot resolves to an immediate (input `32`, at
    slot `0`, is an unused pad word — neither loaded nor an immediate). -/
def ntruImmSlots : ImmSlotMap := fun _ => none

/-- The `Z/8192` input-load map: argument slot → `(base, byte-offset)`. Slot `0`
    (the unused pad word) is skipped. Slots `1..32` load `inp[32 - slot]` (the
    De Bruijn input `32 - slot`): `b[j]` ← `inp[16+j]`, `a[i]` ← `inp[i]`. The
    U64 element stride is 8 bytes. -/
def ntruInLoadMap : InLoadMap := fun slot =>
  if 1 ≤ slot ∧ slot ≤ 32 then
    let k := 32 - slot     -- the De Bruijn input index (1 ≤ slot ≤ 32 ⇒ 0 ≤ k ≤ 31)
    some ("RSI", k * 8)
  else none

/-- The `Z/8192` output-store map: 16 stores, one per output coefficient. The
    front's output-copy pass writes `o[0..15]` in order as the LAST 16
    bindings, so output coefficient `j` is the `j`-th of the last 16 bindings
    and is stored to `out[j]` at byte offset `8*j` from `RDI` (U64 stride). -/
def ntruOutStoreMap : OutStoreMap :=
  (List.range Ntruhrss701MulEmit.N).map (fun j => ("RDI", j * 8))

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
