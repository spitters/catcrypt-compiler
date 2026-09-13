/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

/-!
# Generic `Com → owned-x86 → ELF` driver

A single entry point that lowers a front-emitted jasmin-dialect `Com` (or its
physical-ABI `Lprog` form) all the way to an ELF `.o` byte image through the
**owned** x86 backend — no jasminc.

The byte path is `Com.toLprogPhysAbi → LprogBytes.encodeLprog{,Reloc} →
ByteArray`. Until now this chain was inlined verbatim in each producer
(`Sha256LinearMain`, `KeccakLinearMain`, `Fe25519LfundefBridge`,
`Plonky3ProveDriverBytes`, …); this module packages it as one function to call,
gate, and trust.

Scope: this is the **scalar `Lprog`** path (the register-arith / spill kernels
the front emits). SIMD / vector kernels that hand-build a `List VInst` go through
the `{Vec128,Avx512}Encoder` + `ElfObject.buildElfObject` directly and are not on
this path; unifying them would require lowering vector `Lopn`s through `Lprog`.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes

/-- `List (BitVec 8)` (the encoders' output) → `ByteArray` (what `IO.FS.writeBinFile`
    consumes). This is the adapter every byte-emitting producer inlines. -/
def bytesToByteArray (bs : List (BitVec 8)) : ByteArray :=
  ⟨(bs.map (fun b => UInt8.ofNat b.toNat)).toArray⟩

/-- Lower an `Lprog` to a single-object ELF `.o` image (no cross-object relocs).
    Matches the `Sha256LinearMain` / `KeccakLinearMain` byte path. -/
def compileLprogToElf (p : Lprog) : ByteArray :=
  bytesToByteArray (encodeLprog p)

/-- Lower an `Lprog` to an ELF `.o` image WITH cross-function / external-symbol
    relocations (the multi-symbol path). Matches the `Plonky3ProveDriverBytes` /
    `Fe25519LfundefBridge` byte path. -/
def compileLprogToElfReloc (p : Lprog) : ByteArray :=
  bytesToByteArray (encodeLprogReloc p)

/-- Generic owned-backend compile: front-emitted `Com` → ELF `.o` bytes, no jasminc.
    Parameter list mirrors `Com.toLprogPhysAbi`.

    **DEPRECATED for kernel emit.** This is the `Lprog`/`encodeLprog` byte path.
    The verified successor is `CompileComToElfJInstrFull6.compileComToElfJInstrFull6`
    — proven byte-identical (and it falls back here when a body is not
    `gatherJBlock6`-coverable, so re-pointing is always byte-safe). All GoldenPath
    kernels emit through it. `encodeLprog`/`compileComToElf` are **kept** as the
    byte-identity reference oracle, and the JInstr entries (`X86Backend/`) call
    `compileComToElf` as their legitimate fallback — those uses are exempt. Do NOT
    add new *kernel-level* `compileComToElf` call sites outside `X86Backend/`. -/
def compileComToElf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none)
    (abiW : Nat := 0) : ByteArray :=
  compileLprogToElf (Com.toLprogPhysAbi com fname shiftImm immSlotMap inLoadMap
    outStoreMap abiArgs abiTyin residence abiW)

/-! ## Derived ABI maps for `emitAbiOrchReg`-shaped kernels

For a kernel whose front emits via `emitAbiOrchReg` (the register-arith jasmin-text
path) the `Com` is over an `nInputs`-wide input context where positions `0..nCopy-1`
are loaded state words, positions `firstImm..nInputs-1` are baked immediates (values
`immList`, with `firstImm = numSlots`), and there are `nOut` outputs. `resolveVar`
numbers argument slots from the program root (`slot = curDepth-1-varIndex`), so an
input at position `p` maps to the REVERSED slot `nInputs-1-p`. These three derive
the owned-path ABI maps so a kernel becomes a one-liner. -/

/-- Immediates: position `p ∈ [firstImm, nInputs)` ↦ slot `nInputs-1-p`, baked as `immList[p-firstImm]`. -/
def deriveImmSlots (nInputs firstImm : Nat) (immList : List Nat) : ImmSlotMap := fun slot =>
  let p := nInputs - 1 - slot
  if firstImm ≤ p ∧ p < nInputs then some (immList.getD (p - firstImm) 0) else none

/-- State inputs: position `p ∈ [0, nCopy)` ↦ slot `nInputs-1-p`, loaded from `RSI` at `p*cellBytes`. -/
def deriveInLoad (nInputs nCopy cellBytes : Nat) : InLoadMap := fun slot =>
  let p := nInputs - 1 - slot
  if p < nCopy then some ("RSI", p * cellBytes) else none

/-- Outputs: word `j` of `nOut` stored to `out[j]` on `RDI` at `j*cellBytes`. -/
def deriveOutStore (nOut cellBytes : Nat) : OutStoreMap :=
  (List.range nOut).map (fun j => ("RDI", j * cellBytes))

/-! ## Multi-limb / array-argument ABI maps (wide bignum/curve kernels)

The scalar `deriveInLoad`/`deriveOutStore` above wire a kernel whose every
argument and result is a single machine word. **Wide** kernels — a `[u64;N]`
bignum / curve limb vector — take and return *arrays of limbs* that the C side
passes **by pointer**, not by value. The owned 2-pointer SysV convention the
splice already emits is `f(out = RDI, inp = RSI)` (confirmed by `buildPrologue`,
which parks `RSI` into the reserved scratch `R14` for all input loads, and the
epilogue, which reloads `RDI` for all output stores — there is only ONE input
pointer and ONE output pointer). So a wide kernel's multiple input arrays are
laid out **concatenated in the single `inp` (RSI) buffer**, and all result limbs
**concatenated in the single `out` (RDI) buffer**:

```c
// 4-limb add  out[0..3] = a[0..3] + b[0..3]  (with carry)
extern void bignum4_add(uint64_t *out,        // RDI  -> out[0..3]
                        const uint64_t *inp);  // RSI  -> [ a[0..3], b[0..3] ]
//   inp[0..3] = a, inp[4..7] = b              (one concatenated input buffer)
```

The marshalling is therefore *exactly* the scalar splice with more slots and
larger offsets — no new instruction is needed for the ABI itself: the existing
per-slot `[R14 + off]` load and `[R14 + off]` store already address any byte
offset. The new helpers below just compute the limb→slot→offset map for a kernel
whose input context is `nLimbsTotal` **limb-words** (the flattened concatenation
of every input array) and whose output is `nLimbsOut` **limb-words**.

### The slot→limb correspondence

For a wide kernel whose input context is the flattened limb vector (array 0's
limbs first, then array 1's, …), the two-pass RA assigns program-root limb
position `pos` to slot `pos`, and the C side packs the concatenated `inp` buffer
with that same limb at byte `pos * cellBytes`. So the load map is the **identity**
`slot ↦ ("RSI", slot * cellBytes)` — limb `slot` of the buffer into the body
register the RA gave slot `slot`. (The scalar `deriveInLoad`'s `nInputs-1-slot`
reversal is a no-op for single-input kernels, the only case it was used for; it
does NOT carry over to the multi-input flattened context — the 4-limb-add KAT,
`bench/owned_bignum4_add_arrabi`, pins this empirically: a reversed map computes
`a3+b3` into `out[0]`.) -/

/-- Multi-limb input load. The input context is `nLimbsTotal` limb-words — the
    flattened concatenation, in program-root order, of every input array. Limb
    `slot` is loaded from `[RSI + slot*cellBytes]` (identity slot→offset): the C
    side passes ONE concatenated `inp` buffer holding all input arrays back to
    back, so a kernel reading `a[0..k-1]` then `b[0..k-1]` finds `a` at
    `inp[0..k-1]` and `b` at `inp[k..2k-1]`. KAT-validated in
    `bench/owned_bignum4_add_arrabi`. -/
def deriveInLoadArr (nLimbsTotal cellBytes : Nat) : InLoadMap := fun slot =>
  if slot < nLimbsTotal then some ("RSI", slot * cellBytes) else none

/-- Multi-limb output store. The last `nLimbsOut` `Lopn` bindings are the result
    limbs (limb `j` = the `j`-th of the last `nLimbsOut`); each is stored to
    `[RDI + j*cellBytes]` — i.e. all result limbs concatenated in the single
    `out` buffer. Wide generalisation of `deriveOutStore`; `nLimbsOut = 1`
    recovers the scalar single-word store. -/
def deriveOutStoreArr (nLimbsOut cellBytes : Nat) : OutStoreMap :=
  (List.range nLimbsOut).map (fun j => ("RDI", j * cellBytes))

/-- The byte offset, within the concatenated `inp` (RSI) buffer, of limb `k` of
    input array `i`, when the kernel's input arrays have lengths `arrayLens`
    (program-root order). Each array occupies `len * cellBytes` consecutive
    bytes; array `i` starts after the prefix sum of the preceding arrays. This is
    the address a caller's C harness must respect when packing the `inp` buffer,
    and the offset `deriveInLoadArr` resolves for the corresponding limb slot. -/
def limbInOffset (arrayLens : List Nat) (cellBytes : Nat) (i k : Nat) : Nat :=
  ((arrayLens.take i).foldl (· + ·) 0 + k) * cellBytes

/-- The program-root limb position of limb `k` of input array `i` (the flattened
    index into the concatenated input context): the prefix sum of preceding array
    lengths, plus `k`. Composing with the reversed-slot convention
    (`slot = nLimbsTotal - 1 - p`) gives the argument slot `deriveInLoadArr`
    keys on; `limbInOffset = p * cellBytes`, so the two agree by construction. -/
def limbRootPos (arrayLens : List Nat) (i k : Nat) : Nat :=
  (arrayLens.take i).foldl (· + ·) 0 + k

/-- Compile a `Com` and write the ELF `.o` to disk. -/
def writeComElfObject {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) (outPath : System.FilePath)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none)
    (abiW : Nat := 0) : IO Unit := do
  let bytes := compileComToElf com fname shiftImm immSlotMap inLoadMap
    outStoreMap abiArgs abiTyin residence abiW
  IO.FS.writeBinFile outPath bytes

end CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf
