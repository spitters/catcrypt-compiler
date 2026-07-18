/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf

/-!
# Multi-limb (array-argument) ABI splice: a 4-limb add through the OWNED backend

A **proof-of-concept** that the owned x86 ABI splice marshals *multi-limb / array*
arguments — the keystone that makes wide bignum/curve kernels emit **callable**.

The scalar splice (`deriveInLoad`/`deriveOutStore` in `CompileComToElf`) handles
only the `u64 → u64` case: each argument and result is a single machine word.
Wide kernels — a `[u64;N]` limb vector — take and return *arrays of limbs* that
the C side passes **by pointer**. This demo exercises the new additive helpers
`deriveInLoadArr` / `deriveOutStoreArr`, which lay every input array's limbs
**concatenated in the single `inp` (RSI) buffer** and every result limb
**concatenated in the single `out` (RDI) buffer** — the owned 2-pointer SysV
convention `f(out = RDI, inp = RSI)` the splice already emits.

## The kernel: `out[i] = a[i] + b[i] (mod 2^64)` (limbwise, no carry)

Four independent 64-bit limb adds, the simplest wide kernel that exercises the
multi-limb ABI in BOTH directions (8 input limbs in, 4 result limbs out):

    s0 = a0 + b0                        -- regArith .add 64
    s1 = a1 + b1
    s2 = a2 + b2
    s3 = a3 + b3
    ret s3                              -- s0..s3 are the LAST four bindings

The four sum bindings `s0..s3` are deliberately the **last four** `Lopn`s so the
output-store epilogue (`deriveOutStoreArr 4 8`) stores exactly them, in limb
order, to `out[0..3]`. This kernel is limbwise (no cross-limb carry) on purpose:
it isolates the ABI marshalling. A full carry-propagating 256-bit add needs the
ADCX/ADOX CF-chain emit form — a separate instruction-selection gap, since the
hardware carry flag is clobbered between the dialect's explicit-carry ops.

## ABI layout (what the C harness must pack)

```c
// out[i] = a[i] + b[i]  (limbwise mod 2^64, no cross-limb carry)
extern void bignum4_add(uint64_t *out,        // RDI -> out[0..3]
                        const uint64_t *inp);  // RSI -> [ a[0..3], b[0..3] ]
//   inp[0..3] = a   (input array 0, limbs at byte 0,8,16,24)
//   inp[4..7] = b   (input array 1, limbs at byte 32,40,48,56)
```

The input context is the 8-limb flattened concatenation `[a0,a1,a2,a3,b0,b1,b2,b3]`
in program-root order; `deriveInLoadArr 8 8` loads limb `slot` from
`[RSI + 8*slot]` (identity slot→offset — KAT-validated; the scalar reversal does
not carry over to the multi-input flattened context). The `limbInOffset [4,4] 8 i k`
helper documents which byte each limb of array `i` lands at — array 0 (`a`) at
bytes `0..24`, array 1 (`b`) at bytes `32..56`.

This is a **proof-of-concept for the ABI splice** (the wide marshalling):

* **Verified (printer shape)**: `bignum4AddOwnedAsm_shape` — the emitted `.s`
  carries the SysV leaf label and no unhandled-op sentinel, so the multi-limb
  splice produces a well-formed object (no `UNHANDLED-OP` from the eight loads /
  four stores).
* **KAT (value)**: the external `as`/`cc` harness in `bench/owned_bignum4_add_arrabi/`
  cross-checks `bignum4_add` against the limbwise reference `out[i]=a[i]+b[i]`
  over four vectors (incl. per-limb wraparound and a distinct-per-limb vector
  that would expose any offset-map aliasing) — byte-identical, no jasminc.
* **Trusted (thin)**: `renderLprogAtt` / `gas` / the SysV leaf ABI frame, exactly
  as for the scalar `Sha512ChMajThirOwnedEmit` path.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Bignum4AddArrAbiDemo

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf
  (deriveInLoadArr deriveOutStoreArr limbInOffset)

/-! ## 1. The 4-limb add `Com` (jasmin dialect, 8-limb input context)

Input context (program-root order, the C `inp` buffer concatenation):
`[a0, a1, a2, a3, b0, b1, b2, b3]`. The `Ctxt.Var` for root position `p` reaches
that slot through `p` `.there`s onto `.here`; because the context grows as we add
bindings, the same source limb is reached from progressively-deeper positions —
each binding is written with explicit de-Bruijn references at its own depth. -/

/-- Argument context: the eight input limbs `a0..a3, b0..b3`, each a `reg 64`. -/
abbrev addCtxt : Ctxt jasminDialect :=
  [.reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64, .reg 64]

/-- The 4-limb **limbwise** add `Com`: `out[i] = a[i] + b[i] (mod 2^64)` for
    `i = 0..3`, four independent `regArith add` bindings (NO carry propagation
    between limbs), emitted as the final four bindings so the output-store
    epilogue `deriveOutStoreArr 4 8` stores them to `out[0..3]`.

    Each limb's body is the IDENTICAL ref pattern `add(.there^7 .here, .there^3
    .here)`: at the arg context (depth 8) `a_i` and `b_i` sit 4 limbs apart
    (`a_i = .there^(7-i) .here`, `b_i = .there^(3-i) .here`), and every prior
    binding shifts both uniformly, so the relative offsets `(7, 3)` are constant
    across all four limbs. This isolates the multi-limb load/store ABI splice
    (`deriveInLoadArr`/`deriveOutStoreArr`) from cross-limb carry propagation —
    a full carry-chain 256-bit add needs the ADCX/ADOX CF-chain emit form
    (a distinct instruction-selection gap), not this ABI work. -/
def bignum4AddCom : Com jasminDialect addCtxt (.reg 64) :=
  -- s0 := a0 + b0   (depth 8: a0=.there^7 .here, b0=.there^3 .here)
  .var { op := .regArith .add 64, retTy_eq := rfl,
         args := .cons (.there (.there (.there (.there (.there (.there (.there .here)))))))  -- a0
                (.cons (.there (.there (.there .here))) .nil) }                               -- b0
  -- s1 := a1 + b1   (depth 9: a1 shifted to .there^7 .here, b1 to .there^3 .here)
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there .here))))))) -- a1
                 (.cons (.there (.there (.there .here))) .nil) }                              -- b1
  -- s2 := a2 + b2   (depth 10)
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there .here))))))) -- a2
                 (.cons (.there (.there (.there .here))) .nil) }                              -- b2
  -- s3 := a3 + b3   (depth 11)
  (.var { op := .regArith .add 64, retTy_eq := rfl,
          args := .cons (.there (.there (.there (.there (.there (.there (.there .here))))))) -- a3
                 (.cons (.there (.there (.there .here))) .nil) }                              -- b3
  (.ret .here)))) -- ret s3

/-! ## 2. Owned `Lprog` via the multi-limb ABI maps (no jasminc)

`deriveInLoadArr 8 8` loads the eight input limbs from `[RSI + 8*p]`;
`deriveOutStoreArr 4 8` stores the four result limbs to `[RDI + 8*j]`. The
`abiTyin` carries the 8-limb SysV input shape (eight `64`s). -/

/-- The 4-limb-add owned `Lprog` (`fname` `"bignum4_add"`), wide ABI splice. -/
def bignum4AddOwnedLprog : Lprog :=
  Com.toLprogPhysAbi bignum4AddCom "bignum4_add"
    (fun _ => none)                         -- shiftImm oracle (unused)
    (fun _ => none)                         -- immSlotMap (no input immediates)
    (deriveInLoadArr 8 8)                   -- inLoadMap: 8 limbs from [RSI + 8*p]
    (deriveOutStoreArr 4 8)                 -- outStoreMap: 4 result limbs to [RDI + 8*j]
    ["RDI", "RSI"]                          -- abiArgs (out, inp)
    [64, 64, 64, 64, 64, 64, 64, 64]        -- abiTyin (8 u64 input limbs)

/-- The rendered owned-backend AT&T `.s` for `bignum4_add` (no jasminc). -/
def bignum4AddOwnedAsm : String := renderLprogAtt bignum4AddOwnedLprog

/-! ## 3. Shape check on the emitted asm -/

/-- Substring test (mirrors `Sha512SigmaThirOwnedEmit.hasSub`). -/
def hasSub (s pat : String) : Bool := (s.splitOn pat).length > 1

/-- The emitted `.s` carries the SysV leaf label and has no unhandled-op
    sentinel — the eight multi-limb input loads (`inp[0..7]`) and four output
    stores (`out[0..3]`) all lower through the splice. Shape only; value
    correctness is the external KAT. -/
theorem bignum4AddOwnedAsm_shape :
    hasSub bignum4AddOwnedAsm "bignum4_add"
      ∧ hasSub bignum4AddOwnedAsm "UNHANDLED" = false := by native_decide

/-! ## 4. Emit driver -/

/-- Write the owned-backend `.s` for `bignum4_add` into the
    `bench/owned_bignum4_add_arrabi/gen` harness directory (no jasminc). -/
def emitMain : IO Unit := do
  let dir := "bench/owned_bignum4_add_arrabi/gen"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/bignum4_add_owned.s") bignum4AddOwnedAsm
  IO.println "WROTE bench/owned_bignum4_add_arrabi/gen/bignum4_add_owned.s"
  IO.println "  (4-limb limbwise add bignum4AddCom through Com[jasmin]"
  IO.println "   -> toLprogPhysAbi (deriveInLoadArr 8 8 / deriveOutStoreArr 4 8)"
  IO.println "   -> renderLprogAtt onto the OWNED x86 backend, NO jasminc;"
  IO.println "   wide MULTI-LIMB / array-argument ABI splice)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Bignum4AddArrAbiDemo
