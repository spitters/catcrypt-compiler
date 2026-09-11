/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
import all CatCrypt.Core.Heap
import all CatCrypt.Core.Location
import all CatCrypt.Crypto.CryptoWord
import all CatCrypt.Crypto.Jasmin.JasminAST
import all CatCrypt.Crypto.Jasmin.JasminOps
import all CatCrypt.Crypto.Jasmin.JasminTranslate
import all CatCrypt.Crypto.Jasmin.JasminTypes
import all CatCrypt.Crypto.Jasmin.JasminVar
import all CatCrypt.Crypto.Jasmin.LowCT
import all CatCrypt.Crypto.Jasmin.LowCTBorrowCheck
import all CatCrypt.Crypto.Jasmin.LowCTReflect
import all CatCrypt.Crypto.Jasmin.LowCTToJasmin
import all CatCrypt.Crypto.Primitives.AES128
import all CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.Types
import all CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.X86Intrinsics
import all CatCrypt.Crypto.SecureCompilation.VIR.Core
import all CatCrypt.Crypto.SecureCompilation.VIR.JForProgCT
import all CatCrypt.Crypto.SecureCompilation.VIR.JForProgNested
import all CatCrypt.Crypto.SecureCompilation.VIR.JForProgSemCorrect
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminAbiEmit
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminCTPredicate
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint
import all CatCrypt.Crypto.SecureCompilation.VIR.JasminPrintSemCorrect
import all CatCrypt.Crypto.SecureCompilation.VIR.LaneMap
import all CatCrypt.Crypto.SecureCompilation.VIR.LatticeDialect
import all CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasmin
import all CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenote
import all CatCrypt.Crypto.SecureCompilation.VIR.LatticeToJasminDenoteUncond
import all CatCrypt.Crypto.SecureCompilation.VIR.RobustSafety
import all CatCrypt.Crypto.SecureCompilation.VIR.VPClmulEmit
import all CatCrypt.Crypto.SecureCompilation.VIR.VectorReduce
import all CatCrypt.Crypto.SecureCompilation.VIR.YmmOpCore
import all CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
import all CatCrypt.Crypto.SecureCompilation.X86Backend.ElfObject
import all CatCrypt.Crypto.SecureCompilation.X86Backend.JasminModel
import all CatCrypt.Crypto.SecureCompilation.X86Backend.LeafBytes
import all CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll
import all CatCrypt.Crypto.SecureCompilation.X86Backend.Lowering
import all CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import all CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
import all CatCrypt.Crypto.SecureCompilation.X86Backend.Model
import all CatCrypt.Crypto.SecureCompilation.X86Backend.Preservation
import all CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Decoder
import all CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Lean
import all CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Validation
import all CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
import all CatCrypt.Crypto.SecureCompilation.X86Backend.TranslationValidation
import all CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
import all CatCrypt.Deep.Eval
import all CatCrypt.Deep.RawCode
import all CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
import all CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace
import all CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstrLeaq

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace
public import CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstrLeaq
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstrLeaq

/-!
# `FramingReconcile` — the System-V framing byte-residual between the two emit paths

`ComToFramedJInstrLeaq.framedLeaqText_eq_lprog` closed the body-to-`.text` byte
identity **under hypotheses** about the framing: it assumes the JInstr leaf's
prologue equals a `pushq`-callee-saved block (`hpush`), an *empty* arg-marshal
(`hmar : argMarshalBytes f.alloc f.args = []`), and an epilogue that is
`popq…++ret` (`hpop`). This module discharges the *physical-reality* question
those hypotheses leave open: **does the framing the real `Com.toLprogPhysAbi`
export carries actually byte-match the framing the JInstr gather produces?**

## The structural finding (read this first)

`framedLeaqText_eq_lprog`'s framing model — `pushq`/`leaq`/`popq`/`ret`, the
`LeafBytes`/`encodeLfundefBytes` model — is **not** the framing model
`Com.toLprogPhysAbi` uses. The physical export
(`JasminLprogExport.comToLfundefPhysAbi`) assembles its function as

```
lfd_body = buildPrologue ++ bodyWithRestore
```

so the *entire* System-V framing lives **inside `lfd_body`**, as ordinary
instructions the body byte encoder `LprogBytes.encodeLcmd` lays down — there is
no separate `prologueBytes`/`argMarshalBytes`/`epilogueBytes` segment on the
physical path. Concretely, `buildPrologue` (`asconSigma0`, the GoldenPath kernel)
emits, *as body `Linstr`s*:

* the arg-marshal `MOVQ R14, RSI` (park the input pointer in the reserved
  scratch `R14`);
* eight callee-saved red-zone spills `MOVQ qsave.X, X`
  (`X ∈ {RDI, RSI, RBX, RBP, R12, R13, R14, R15}`);

and the epilogue emits the matching `MOV`/`MOVQ` restores before the trailing
`Lret`. So the right reconciliation question is **not** "does a separate JInstr
`argMarshalBytes`/`prologueBytes` equal the `Lprog` framing" — on the physical
path `argMarshalBytes = []` genuinely holds (the marshal is IN the body) — but
rather: **does the JInstr gather cover those in-body `MOVQ` framing
instructions, so that gathering the FULL physical body (framing + ALU + shift)
byte-matches `encodeLcmd` of the same body?**

## The verdict: the framing does NOT gather — and the residual is ONE mnemonic

The whole physical body does **not** gather: `gatherJBlock3 physBody = none`
(§2 `#eval`). Of the 28 physical-body instructions, the 12 ALU-core ops
(`SHR/SHL:n:64`, `MOV:64`, `OR:64`, `XOR:64`) gather; the **15 `MOVQ` framing
ops** (9 prologue: 8 qsave spills + 1 arg-marshal, 6 epilogue restores) and one
`Lret` do not lower (the `Lret` is dropped by `gatherJBlock3` and supplied as
framing on both sides, so it is not a residual).

The residual is sharper than "stores are uncovered": the gather DOES cover
`%rsp`-relative spill/qsave stores and loads — but only under the `MOV` /
`MOV:64` mnemonic. `buildPrologue` emits the framing under the **`MOVQ`** synonym
mnemonic, and the gather's lowering table (`LoweringExtended.lowerAluJ`, reached
after `stripWidthTag`) keys on `"MOV"`, not `"MOVQ"`. `stripWidthTag "MOVQ" =
"MOVQ"` (it strips a `:64` width tag, not the `Q` synonym), so the framing
instructions fall through to `none`. The residual is exactly **the `MOVQ`
mnemonic-synonym gap in the gather**, nothing structural about stores.

## The reconciliation: the `Lprog` encoder already treats `MOVQ ≡ MOV:64`

Crucially, the `Lprog` byte encoder `LprogBytes.encodeLopn` emits **byte-identical**
output for `MOVQ` and `MOV:64` on both framing forms (§3):

* reg-reg arg-marshal `R14, RSI`  →  `48/49 89 F6` (`mov %rsi, %r14`) for either
  mnemonic — here `[0x49, 0x89, 0xF6]`;
* qsave store `qsave.RBX, RBX`    →  `[0x48, 0x89, 0x5C, 0x24, 0x68]`
  (`mov %rbx, off(%rsp)`) for either mnemonic.

And the `MOV:64`-mnemonic equivalent of each framing instruction **does** gather,
and its `encodeJBlock` bytes equal the `MOVQ` `encodeLopn` bytes exactly (§4).
So the full reconciliation is a *one-line* alias: if `buildPrologue` emitted
`MOV:64` instead of the `MOVQ` synonym (or, equivalently, the gather's lowering
added a `MOVQ ↦ MOV:64` arm), the entire physical body — framing included — would
gather AND byte-match `encodeLcmd physBody`, because the encoder already maps the
two mnemonics to the same bytes. No store-arm, no separate framing segment, and
no new trusted bytes are needed.

## What this means for the full-kernel byte identity

Combining with the body results already landed:

* the two-source ALU core byte-matches under `gatherJBlock3`
  (`GatherInPlace`, §4b′ — the self-`mov` removed by the in-place peephole);
* the count-in-tag shift OP byte-agrees (`encTagShift` in `encodeLopn`), leaving
  only the gather's per-shift materialise `mov` as the body residual;
* **the framing residual is exactly the `MOVQ ↦ MOV:64` mnemonic alias** (this
  file).

So the remaining gaps to a literal whole-physical-body byte identity are two
named, local lowering items: (1) the gather's per-shift materialise `mov` (a
shift-arm in-place peephole, `GatherInPlace` §4b), and (2) the `MOVQ` mnemonic
alias in the gather (this file). Neither is a structural mismatch, an encoder
bug, or a new-trust requirement — both encoders already agree on the bytes; the
gather's coverage table is what lags.

## Trust tier

No new trust. The `Lprog` framing bytes are `LprogBytes.encodeLopn` (the
gas-pinned tier `encodeLcmd` already carries), the gather bytes are
`ScalarEncoder.encodeJBlock`, and every theorem below is `decide +kernel` over
those (no `native_decide`, no `sorry`, no axiom). The `#eval`s are interpreter
evidence on the real `AsconLinear.asconSigma0Com` kernel, not part of any proof
term.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FramingReconcile

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.GatherInPlace
open CatCrypt.Crypto.SecureCompilation.X86Backend.LoweringExtendedCoverage
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather (physAlloc)

/-! ## 1. The framing instructions `buildPrologue` actually emits

Two representative framing instructions, exactly as `JasminLprogExport.buildPrologue`
emits them into `lfd_body` for `asconSigma0`: the reg-reg arg-marshal that parks
`RSI` in the reserved scratch `R14`, and a callee-saved red-zone qsave spill. Both
carry the **`MOVQ`** mnemonic (the 64-bit-only synonym), not `MOV:64`. -/

/-- The arg-marshal `Lopn` `buildPrologue` prepends to the body: `MOVQ R14, RSI`
    (park the SysV input pointer in the reserved scratch). -/
def argMarshalLopn : LinstrR := .Lopn [.reg "R14"] "MOVQ" [.reg "RSI"]

/-- One callee-saved red-zone qsave spill `buildPrologue` prepends to the body:
    `MOVQ qsave.RBX, RBX` (store `RBX` to its red-zone slot). -/
def qsaveSpillLopn : LinstrR := .Lopn [.reg "qsave.RBX"] "MOVQ" [.reg "RBX"]

/-! ## 2. The empirical verdict: the framing does NOT gather (the residual)

The whole-physical-body gather-coverage `#eval`s on `asconSigma0` (the `MOVQ`
framing is the only blocker) are re-homed in `GoldenPathByteIdentityDemo` (above
the chain) so this file is GoldenPath-free. The kernel-independent framing
`MOVQ ≡ MOV:64` byte-agreement theorems and `#eval`s (§3 onward) stay here. -/

/-! ## 3. The `Lprog` encoder maps `MOVQ ≡ MOV:64` (byte-identical framing)

`encodeLopn` (hence `encodeLcmd`) emits the SAME bytes for the framing
instructions whether the mnemonic is `MOVQ` or `MOV:64`. These are proved
`decide +kernel` against the literal x86 byte image. -/

/-- The arg-marshal `MOVQ R14, RSI` encodes to `mov %rsi, %r14`
    (`REX.WB 0x49`, `MOV 0x89`, `ModRM 0xF6`) — 3 bytes. -/
theorem encode_argMarshal_movq :
    encodeLopn 0 64 argMarshalLopn
      = [BitVec.ofNat 8 0x49, BitVec.ofNat 8 0x89, BitVec.ofNat 8 0xF6] := by
  decide +kernel

/-- The same bytes via the gather-covered `MOV:64` mnemonic: `encodeLopn` is
    mnemonic-agnostic between `MOVQ` and `MOV:64` on the reg-reg arg-marshal. -/
theorem encode_argMarshal_mov64 :
    encodeLopn 0 64 (.Lopn [.reg "R14"] "MOV:64" [.reg "RSI"])
      = [BitVec.ofNat 8 0x49, BitVec.ofNat 8 0x89, BitVec.ofNat 8 0xF6] := by
  decide +kernel

/-- **The arg-marshal framing is encoder-equal across the mnemonic synonym.** The
    `Lprog` byte encoder gives the same bytes for the `MOVQ` form `buildPrologue`
    emits and the `MOV:64` form the gather covers. -/
theorem encode_argMarshal_movq_eq_mov64 :
    encodeLopn 0 64 argMarshalLopn
      = encodeLopn 0 64 (.Lopn [.reg "R14"] "MOV:64" [.reg "RSI"]) := by
  rw [encode_argMarshal_movq, encode_argMarshal_mov64]

/-- The qsave spill `MOVQ qsave.RBX, RBX` encodes to `mov %rbx, off(%rsp)`
    (`REX.W 0x48`, `MOV 0x89`, `ModRM 0x5C`, `SIB 0x24`, `disp8 0x68`) — 5 bytes,
    a `%rsp`-relative red-zone store. -/
theorem encode_qsaveSpill_movq :
    encodeLopn 128 64 qsaveSpillLopn
      = [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x89, BitVec.ofNat 8 0x5C,
         BitVec.ofNat 8 0x24, BitVec.ofNat 8 0x68] := by
  decide +kernel

/-- The same bytes via the gather-covered `MOV:64` mnemonic on the qsave store. -/
theorem encode_qsaveSpill_mov64 :
    encodeLopn 128 64 (.Lopn [.reg "qsave.RBX"] "MOV:64" [.reg "RBX"])
      = [BitVec.ofNat 8 0x48, BitVec.ofNat 8 0x89, BitVec.ofNat 8 0x5C,
         BitVec.ofNat 8 0x24, BitVec.ofNat 8 0x68] := by
  decide +kernel

/-- **The qsave-spill framing is encoder-equal across the mnemonic synonym.** -/
theorem encode_qsaveSpill_movq_eq_mov64 :
    encodeLopn 128 64 qsaveSpillLopn
      = encodeLopn 128 64 (.Lopn [.reg "qsave.RBX"] "MOV:64" [.reg "RBX"]) := by
  rw [encode_qsaveSpill_movq, encode_qsaveSpill_mov64]

/-! ## 4. The residual is exactly the `MOVQ` mnemonic gap in the gather

The framing instructions, *as `MOVQ`*, gather to `none`; their `MOV:64`
equivalents gather, and the gathered block encodes byte-for-byte to the `Lprog`
framing bytes. So the framing byte-matches **iff** the gather aliases the `MOVQ`
mnemonic to `MOV:64`. -/

/-- **The arg-marshal does NOT gather as `MOVQ`.** `lowerLinstrExtCov3` has no
    `MOVQ` arm — `stripWidthTag "MOVQ" = "MOVQ" ∉ lowerAluJ`'s table — so the
    arg-marshal lowers to `none`. This is the residual. -/
theorem argMarshal_movq_not_covered :
    lowerLinstrExtCov3 argMarshalLopn = none := by
  decide +kernel

/-- **The qsave spill does NOT gather as `MOVQ`** — same `MOVQ`-mnemonic gap (the
    gather covers `MOV:64` stores to `%rsp`-relative slots, just not under the
    `MOVQ` synonym). -/
theorem qsaveSpill_movq_not_covered :
    lowerLinstrExtCov3 qsaveSpillLopn = none := by
  decide +kernel

/-- **The `MOV:64` arg-marshal DOES gather** — the gap is precisely the mnemonic
    synonym, not the instruction shape. -/
theorem argMarshal_mov64_covered :
    (lowerLinstrExtCov3 (.Lopn [.reg "R14"] "MOV:64" [.reg "RSI"])).isSome = true := by
  decide +kernel

/-- **The `MOV:64` qsave spill DOES gather** — `%rsp`-relative stores ARE covered;
    only the `MOVQ` synonym is missing. -/
theorem qsaveSpill_mov64_covered :
    (lowerLinstrExtCov3 (.Lopn [.reg "qsave.RBX"] "MOV:64" [.reg "RBX"])).isSome = true := by
  decide +kernel

-- The gathered `MOV:64` arg-marshal block, encoded under `physAlloc`, equals the
-- `MOVQ` `encodeLopn` framing bytes exactly. Prints `true` — the framing WOULD
-- byte-match if the gather covered the `MOVQ` mnemonic.
#eval (lowerLinstrExtCov3 (.Lopn [.reg "R14"] "MOV:64" [.reg "RSI"])).map (encodeJBlock physAlloc)
      == some (encodeLopn 0 64 argMarshalLopn)

/-! ## 5. The reconciliation statement (the framing closes under the `MOVQ` alias)

Packaging §3 + §4: each framing instruction's `MOV:64` equivalent gathers, and the
`Lprog` encoder gives identical bytes for the `MOVQ` form (`buildPrologue`) and the
`MOV:64` form (gather-covered). So aliasing `MOVQ ↦ MOV:64` in the gather makes the
framing gather AND byte-match `encodeLcmd`. The `decide +kernel` byte-encode of the
gathered `MOV:64` arg-marshal under `physAlloc` is the per-instruction witness. -/

/-- **Framing reconciliation witness (arg-marshal).** The gathered `MOV:64`
    arg-marshal block encodes (under the physical allocation) to exactly the `Lprog`
    framing bytes the `MOVQ` arg-marshal `encodeLopn` produces. Hence under a
    `MOVQ ↦ MOV:64` gather alias the arg-marshal framing byte-matches `encodeLcmd`. -/
theorem argMarshal_framing_byte_matches :
    (lowerLinstrExtCov3 (.Lopn [.reg "R14"] "MOV:64" [.reg "RSI"])).map (encodeJBlock physAlloc)
      = some (encodeLopn 0 64 argMarshalLopn) := by
  decide +kernel

end CatCrypt.Crypto.SecureCompilation.X86Backend.FramingReconcile
