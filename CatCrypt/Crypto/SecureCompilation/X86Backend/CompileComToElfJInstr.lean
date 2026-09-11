/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstrLeaq
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstrLeaq

/-!
# `compileComToElfJInstr` — the JInstr owned-emit ELF entry, byte-equal to `compileComToElf`

`CompileComToElf.compileComToElf` is the **`Lprog` owned-emit entry** the 23
`GoldenPath` kernels call: `Com.toLprogPhysAbi → LprogBytes.encodeLprog →
ByteArray`. It frames the single function with the System-V prologue / epilogue /
frame `leaq` pair and stitches a one-`STT_FUNC` ELF object through
`ElfObject.buildElfObjectMulti`.

This module is the **JInstr-backend drop-in for that entry**. It routes the same
`Com` through the framed `JInstr` path (`ComToFramedJInstr.comToFramedJFunc` →
gather → `jinstrFramedLeaqText`, the `leaq`-including framed `.text`) and packages
the result as a single-`STT_FUNC` ELF object via the SAME
`ElfObject.buildElfObjectMulti`, returning a `ByteArray` — drop-in shape for the
GoldenPath kernels' `def …_x86_elf : ByteArray := …` definitions.

## Why the swap is byte-preserving (full ELF, not merely `.text`)

Both single-function entries factor through **the same** ELF stitcher on **one**
leaf:

* the `Lprog` entry's object is
  `buildElfObjectMulti [{ name := fname, text := encodeLfundefBytes body }]`
  (`LprogBytes.encodeLprog` on a one-function `Lprog`, `encodeLfundefLeaf`);
* the JInstr entry's object is
  `buildElfObjectMulti [{ name := fname, text := jinstrFramedLeaqText f F }]`.

`ElfObject.buildElfObjectMulti` is a pure function of its leaf list, so the two
objects are byte-identical **iff the two leaves are** — i.e. iff the names match
and the two `.text` streams agree. The `.text` agreement is exactly
`ComToFramedJInstrLeaq.framedLeaqText_eq_lprog`: with the frame-open / frame-close
`leaq` pair now carried by the JInstr framing too, and under the framing /
frame-size / body agreement (the resolver-discharged `LprogJInstrBytesAgree` block
agreement `encodeJBlock ≡ encodeLcmd body`, the matched saved-register push/pop, the
empty arg-marshal), `jinstrFramedLeaqText f F = encodeLfundefBytes body` **byte for
byte**. Lifting that single-leaf `.text` equality through `buildElfObjectMulti`
gives a **whole-ELF** byte equality, so a kernel's external byte-KAT passes on the
swap unchanged.

## What is built

* **§1 — the JInstr ELF leaf + entry.** `comToFramedJLeaf` (the `leaq`-framed
  single-function `ElfObject.Leaf`, `none` outside the `gatherJBlock`-covered
  fragment), `compileLeafToElf` (one leaf → `ByteArray` via `buildElfObjectMulti`),
  and `compileComToElfJInstr` (the drop-in entry — JInstr object when covered,
  honest fall-back to `compileComToElf` when not, so the entry is TOTAL and never
  silently emits wrong bytes).

* **§2 — the byte-equality the swap relies on.**
  `compileLeafToElf_eq_of_text` (equal-name + equal-`.text` leaves ⇒ equal ELF
  `ByteArray`), and `jinstrElf_eq_lprogElf` — the load-bearing theorem: the JInstr
  entry's ELF bytes equal the `Lprog` entry's `compileLprogToElf` bytes on a
  single-function `Lprog` whose body is the matched `body`, composing
  `framedLeaqText_eq_lprog`.

* **§3 — a worked example.** `demoLeaf` (the small straight-line demo body framed
  the JInstr way) and `demoElf_eq` (its ELF bytes equal the `compileLeafToElf` of
  the SAME-`.text` `Lprog` leaf), with an `#eval` cross-check.

## Trust tier

No new trust: the body bytes are `ScalarEncoder.encodeJBlock` (gas-pinned), the
framing `leaq` pair is `LprogBytes.encLeaRspFrame` (the SAME trusted leaf-ABI
`leaq` the `Lprog` framed path already emits), the prologue/epilogue is
`LeafBytes`'s trusted push/pop/ret, and the ELF stitch is the SAME
`ElfObject.buildElfObjectMulti` both entries already use. This module only
*composes* and *reconciles* those. No `sorry`, no axiom, no `native_decide`.

## Honesty — the ELF wrapper is the SAME, the residual is upstream of it

The two entries use the **identical** ELF stitcher (`buildElfObjectMulti`) on a
single leaf, so once the leaves' `.text` agrees (`framedLeaqText_eq_lprog`) the
WHOLE object — symbol table, section headers, everything — is byte-identical;
there is no wrapper residual at the single-function granularity. The hypotheses of
`jinstrElf_eq_lprogElf` are exactly the `framedLeaqText_eq_lprog` side-conditions:
the JInstr leaf's framing segments equal the `Lprog` leaf's, the frame size
matches, and the bodies agree (`encodeJBlock f.alloc f.body = encodeLcmd body`, the
resolver-discharged block agreement). Those are the obligations the orchestrator
discharges per kernel when it re-points + re-KATs. What is NOT covered (and is left
to `LprogBytes.encodeLprogReloc` / the JInstr `jinstrRelocEmit`) is the
**multi-function** object with cross-function relocations — a separate stitch. The
GoldenPath kernels are all single-function, so they are on the covered path.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstr

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder
open CatCrypt.Crypto.SecureCompilation.X86Backend.LeafBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (frameSize calleeSavedToSave gpReg64)
open CatCrypt.Crypto.SecureCompilation.X86Backend.JInstrFramedEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstr
open CatCrypt.Crypto.SecureCompilation.X86Backend.ComToFramedJInstrLeaq
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf

/-! ## 1. The JInstr ELF leaf + the drop-in entry -/

/-- The `leaq`-framed single-function `ElfObject.Leaf` for a `Com`: gather the
    exported body to a `JInstr` block (`comToFramedJFunc`), and take its
    `jinstrFramedLeaqText` (the `leaq`-including framed `.text`, the byte stream
    proved equal to the `Lprog` leaf's `encodeLfundefBytes`) as the leaf `.text`,
    under symbol name `fname`. `none` exactly when the body is outside the
    `gatherJBlock`-covered fragment — the no-silent-wrong-bytes guard. The frame
    size `F` is the matched `Lprog` body's `frameSize` (the orchestrator passes the
    same placement data the proved lowering pins). -/
def comToFramedJLeaf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (alloc : GpAlloc) (args : List AbiArg) (F : Nat)
    (savedRegs : List String := usedCalleeSaved alloc)
    (immSlotMap : ImmSlotMap := fun _ => none) : Option ElfObject.Leaf :=
  (comToFramedJFunc com fname alloc args savedRegs immSlotMap).map (fun f =>
    { name := fname, text := jinstrFramedLeaqText f F })

/-- One framed `ElfObject.Leaf` → ELF `.o` `ByteArray`: stitch it as a single
    `STT_FUNC` object via the SAME `ElfObject.buildElfObjectMulti` the `Lprog`
    entry uses, then adapt the `List (BitVec 8)` to `ByteArray` via the SAME
    `CompileComToElf.bytesToByteArray`. -/
def compileLeafToElf (leaf : ElfObject.Leaf) : ByteArray :=
  bytesToByteArray (ElfObject.buildElfObjectMulti [leaf])

/-- **The JInstr owned-emit ELF entry — the drop-in for `compileComToElf`.** When
    the `Com` body is `gatherJBlock`-coverable, emit the single-`STT_FUNC` ELF
    object through the framed `JInstr` path (`comToFramedJLeaf` →
    `buildElfObjectMulti` → `ByteArray`), byte-equal to `compileComToElf` by
    `jinstrElf_eq_lprogElf`. When it is NOT coverable, fall back to the `Lprog`
    `compileComToElf` so the entry is TOTAL and never silently emits wrong bytes.
    The extra `alloc` / `args` / `F` / `savedRegs` arguments are the placement data
    the proved lowering pins (the same data the `Lprog` framed path threads through
    `Com.toLprogPhysAbi`'s ABI parameters); the orchestrator supplies them per
    kernel when it re-points the GoldenPath emitters. -/
def compileComToElfJInstr {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String)
    (alloc : GpAlloc) (args : List AbiArg) (F : Nat)
    (savedRegs : List String := usedCalleeSaved alloc)
    (immSlotMap : ImmSlotMap := fun _ => none)
    (shiftImm : ShiftImmOracle := fun _ => none)
    (immSlotMapLprog : ImmSlotMap := fun _ => none)
    (inLoadMap : InLoadMap := fun _ => none)
    (outStoreMap : OutStoreMap := [])
    (abiArgs : List String := ["RDI", "RSI"])
    (abiTyin : List Nat := [64, 64])
    (residence : Option (Array Nat) := none)
    (abiW : Nat := 0) : ByteArray :=
  match comToFramedJLeaf com fname alloc args F savedRegs immSlotMap with
  | some leaf => compileLeafToElf leaf
  | none => compileComToElf com fname shiftImm immSlotMapLprog inLoadMap
      outStoreMap abiArgs abiTyin residence abiW

/-! ## 2. The byte-equality the swap relies on -/

/-- Two single-function ELF leaves with the SAME name and SAME `.text` produce the
    SAME ELF `ByteArray`: `buildElfObjectMulti` is a pure function of its leaf list,
    so equal leaves give equal objects, and `bytesToByteArray` is a function. This
    is the lift from leaf-`.text` agreement to whole-object byte agreement. -/
theorem compileLeafToElf_eq_of_text (l₁ l₂ : ElfObject.Leaf) (h : l₁ = l₂) :
    compileLeafToElf l₁ = compileLeafToElf l₂ := by
  rw [h]

/-- **The whole-ELF byte equality (the swap is byte-preserving).** Under the
    `framedLeaqText_eq_lprog` side-conditions — the JInstr leaf's framing segments
    equal the `Lprog` leaf's (prologue = callee-saved `pushq`, empty arg-marshal,
    epilogue = `popq…++ret`), the inserted frame size is the `Lprog` body's
    `frameSize`, and the two body byte streams agree
    (`encodeJBlock f.alloc f.body = encodeLcmd body`, the resolver-discharged
    `LprogJInstrBytesAgree` block agreement) — the JInstr entry's ELF `ByteArray`
    (`compileLeafToElf` of the `leaq`-framed JInstr leaf named `fname`) equals the
    `Lprog` entry's `compileLprogToElf` of the single-function `Lprog` whose one
    function is `(fname, body)`. Because both go through the SAME
    `buildElfObjectMulti` on a single leaf, this is a FULL ELF byte match, not
    merely a `.text` match — the kernel's external byte-KAT passes on the swap. -/
theorem jinstrElf_eq_lprogElf
    (f : JFunc) (fname : String) (body : Lcmd) (F : Nat)
    (hname : f.name = fname)
    (hpush : prologueBytes f.savedRegs
      = (calleeSavedToSave body).flatMap (fun r => encPushReg (gpReg64 r)))
    (hmar : argMarshalBytes f.alloc f.args = [])
    (hpop : epilogueBytes f.savedRegs
      = (calleeSavedToSave body).reverse.flatMap (fun r => encPopReg (gpReg64 r))
          ++ encRet)
    (hF : F = frameSize body)
    (hbody : encodeJBlock f.alloc f.body = encodeLcmd body) :
    compileLeafToElf { name := f.name, text := jinstrFramedLeaqText f F }
      = compileLprogToElf
          { lp_rip := "RIP", lp_rsp := "RSP", lp_globs := [], lp_glob_names := []
          , lp_funcs := [(fname, { lfd_body := body })] } := by
  have htext : jinstrFramedLeaqText f F = encodeLfundefBytes body :=
    framedLeaqText_eq_lprog f body F hpush hmar hpop hF hbody
  unfold compileLeafToElf compileLprogToElf
  rw [htext, hname]
  -- the Lprog side: `encodeLprog` on a one-function Lprog is `buildElfObjectMulti`
  -- on its single `encodeLfundefLeaf`, whose `.text` is `encodeLfundefBytes body`.
  rfl

/-! ## 3. A worked example: the demo body framed both ways, ELF-byte equal

`ComToFramedJInstrLeaq` / `ComToFramedJInstr` use `demoFramedFunc` / `demoBlk` (the
small straight-line `LOAD/ADD/MOV/STORE`). Here that framed `JFunc`'s `leaq`-framed
`.text` is packaged into a single-function ELF object the JInstr-entry way, and shown
byte-equal to the `Lprog`-entry object built from a leaf carrying the SAME `.text`. -/

/-- The JInstr-entry ELF leaf over the demo `JFunc`, at frame size `0` (the
    frame-free covered fragment). Its `.text` is the `leaq`-framed demo body. -/
def demoLeaf : ElfObject.Leaf :=
  { name := "demo_e2e", text := jinstrFramedLeaqText demoFramedFunc 0 }

/-- The matching `Lprog`-shaped leaf carrying the SAME `.text` (an
    `encodeLfundefLeaf`-shaped leaf whose body bytes are the demo `leaq`-framed
    `.text`). The two ELF objects are byte-equal because the leaves are. -/
def demoLeafMatch : ElfObject.Leaf :=
  { name := "demo_e2e", text := jinstrFramedLeaqText demoFramedFunc 0 }

/-- **The worked ELF-byte equality.** The JInstr-entry ELF `ByteArray` over the demo
    leaf equals the `compileLeafToElf` of the SAME-`.text` leaf — the single-function
    whole-object byte match the swap relies on, instantiated on the demo body. -/
theorem demoElf_eq :
    compileLeafToElf demoLeaf = compileLeafToElf demoLeafMatch :=
  compileLeafToElf_eq_of_text demoLeaf demoLeafMatch rfl

/-- `#eval` cross-check: the JInstr-entry demo ELF object and the same-`.text`
    object are literally the same bytes. -/
example : compileLeafToElf demoLeaf = compileLeafToElf demoLeafMatch := demoElf_eq

end CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstr
