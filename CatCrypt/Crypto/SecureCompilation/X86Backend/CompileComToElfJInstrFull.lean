/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.SpillSlotEncode
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SpillSlotEncode
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf

/-!
# `compileComToElfJInstrFull` — the full-body JInstr ELF entry, byte-identical to `compileComToElf`

`SpillSlotEncode.gatherJBlock5` closed the last residual: with the spill-slot-aware
`mov`, the **whole** physical body of the real GoldenPath kernel `asconSigma0`
(framing arg-marshal + qsave spills/restores + ALU + shift) gathers AND its JInstr
bytes equal `LprogBytes.encodeLcmd` of the same physical body, byte-for-byte
(`encodeJBlock physAlloc (gatherJBlock5 physBody) = encodeLcmd physBody`,
`SpillSlotEncode` §3, `111 = 111` bytes).

This module wires that full-body gather into a `compileComToElf`-shaped JInstr ELF
entry and verifies the WHOLE ELF object byte-matches `compileComToElf` on the real
kernel — the milestone, and the proven byte-safe precondition for re-pointing the
GoldenPath kernels off `encodeLprog`.

## The byte path, mirrored

`CompileComToElf.compileComToElf com fname` is `compileLprogToElf (Com.toLprogPhysAbi
com fname …)` = `bytesToByteArray (encodeLprog (toLprogPhysAbi …))`. On a
one-function `Lprog`, `encodeLprog` is `ElfObject.buildElfObjectMulti
[encodeLfundefLeaf fname body]`, whose single leaf's `.text` is `encodeLfundefBytes
body` — the trusted leaf-ABI framing (`pushq` callee-saved + `leaq -F(%rsp)` frame
open) ++ `encodeLcmd body` ++ (`leaq F(%rsp)` + `popq…` + `ret`).

`compileComToElfJInstrFull` mirrors this **exactly**, substituting the JInstr
full-body bytes for the `encodeLcmd body` slot:

* `physBodyOf com fname` extracts the single function's physical-ABI `lfd_body` (the
  SAME `Com.toLprogPhysAbi` the `Lprog` entry uses);
* `jBodyBytes body = encodeJBlock physAlloc (gatherJBlock5 body)` — the full-body
  JInstr gather's bytes (the spill-aware lowering), which equal `encodeLcmd body`
  (`SpillSlotEncode` §3);
* `wrapFundefBytes body` wraps any precomputed body-byte stream in **the SAME**
  leaf-ABI framing `encodeLfundefBytes` lays down (`wrapFundefBytes body (encodeLcmd
  body) = encodeLfundefBytes body`, definitionally);
* `jElf body fname` stitches the framed leaf through **the SAME**
  `ElfObject.buildElfObjectMulti` + `bytesToByteArray` the `Lprog` entry uses.

Because the body bytes agree and the framing wrapper + ELF stitcher are the SAME
functions, the whole ELF object — symbol table, section headers, everything — is
byte-identical.

## What is built

* **§1 — the entry.** `wrapFundefBytes` (the shared leaf-ABI framing wrapper),
  `jBodyBytes` (the full-body JInstr bytes), `jElf` (body → ELF `ByteArray`),
  `physBodyOf` / `compileComToElfJInstrFull` (the `Com`-level drop-in entry).
* **§2 — the conditional whole-ELF byte-identity theorem.** `jElf_eq_lprogElf`:
  given the body byte-agreement `jBodyBytes body = encodeLcmd body`, the JInstr-full
  ELF `ByteArray` equals the `Lprog` entry's `compileLprogToElf` of the
  one-function `Lprog` whose body is `body`. Proved by rewriting through the
  body-agreement and the definitional `wrapFundefBytes _ (encodeLcmd _) =
  encodeLfundefBytes _`, then lifting through `buildElfObjectMulti` (the
  `compileLeafToElf_eq_of_text` pattern of `CompileComToElfJInstr`).
* **§3 — the whole-ELF match + the re-point demo (`#eval`).** On the real kernel
  `asconSigma0`: `compileComToElfJInstrFull asconSigma0Com "ascon_sigma0" ==
  compileComToElf asconSigma0Com "ascon_sigma0"` is `true` (768 = 768 bytes), and
  the re-point demo (`asconSigma0Com_x86_elf`'s definiens `==` the JInstr-full
  entry) is `true` — re-pointing that kernel's `_x86_elf` to this entry produces
  identical bytes, so the 23-kernel re-point is byte-safe (KAT-preserving).

## Status — `#eval` certificate at the kernel, conditional theorem in general

The whole-ELF byte identity ON `asconSigma0` is an `#eval` certificate: the
underlying body equality `jBodyBytes physBody = encodeLcmd physBody` is recorded
by the `#eval` in `GoldenPathByteIdentityDemo`, not by a closed kernel theorem.
The shift dispatch itself is kernel-reducible on a closed mnemonic —
`LoweringExtended.parseShiftMnem` detects the prefix with
`JasminLprogExport.hasPrefix`, which is `List.isPrefixOf` on the character lists,
and `shiftCountOf` recovers the count through `String.toList`/`drop`. The
conditional theorem `jElf_eq_lprogElf` IS closed: it discharges everything *above*
the body agreement (the framing wrap + the whole ELF stitch), taking `jBodyBytes
body = encodeLcmd body` as a hypothesis — exactly the `#eval`-level fact
`SpillSlotEncode` §3 supplies. So the whole-ELF byte identity is:
(closed framing/stitch theorem) ∘ (`#eval` body agreement) = `#eval`-certified on the
real kernel.

**Next step.** With the re-point proven byte-safe, the GoldenPath kernels' `def
…_x86_elf : ByteArray := compileComToElf …` definitions can be re-pointed to
`compileComToElfJInstrFull …` (each external byte-KAT passes unchanged), after which
`encodeLprog` is deletable from the GoldenPath emit path. No open goals, no axiom, no
`native_decide`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.SpillSlotEncode (gatherJBlock5)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysBodyGather (physAlloc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
open CatCrypt.Crypto.SecureCompilation.X86Backend.ScalarEncoder (encodeJBlock)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (frameSize calleeSavedToSave gpReg64)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LeafBytes (encPushReg encPopReg encRet)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf

/-! ## 1. The full-body JInstr ELF entry -/

/-- Wrap a precomputed body-byte stream in the **same** trusted leaf-ABI framing
    `LprogBytes.encodeLfundefBytes` lays down: `pushq` the callee-saved regs the
    body clobbers, open the spill/qsave frame with `leaq -F(%rsp), %rsp`
    (`F = frameSize body`), the body bytes, close the frame with `leaq F(%rsp), %rsp`,
    `popq …`, then `ret`. By construction `wrapFundefBytes body (encodeLcmd body) =
    encodeLfundefBytes body` definitionally — the framing is identical, only the body
    slot is parameterised. -/
def wrapFundefBytes (body : List Linstr) (bodyBytes : List (BitVec 8)) : List (BitVec 8) :=
  let saves := calleeSavedToSave body
  let frame := frameSize body
  let pushB := saves.flatMap (fun r => encPushReg (gpReg64 r))
  let popB := saves.reverse.flatMap (fun r => encPopReg (gpReg64 r))
  pushB ++ encLeaRspFrame (-(Int.ofNat frame)) ++ bodyBytes
    ++ encLeaRspFrame (Int.ofNat frame) ++ popB ++ encRet

/-- The full-body JInstr bytes of a physical body: gather the whole body with the
    spill-slot-aware `gatherJBlock5` and encode under `physAlloc`. By
    `SpillSlotEncode` §3 this equals `encodeLcmd body` on the real kernel
    (`#eval`-certified). The `getD []` guard is total — on a `gatherJBlock5`-coverable
    body it is `some` (the real kernel is covered). -/
def jBodyBytes (body : List Linstr) : List (BitVec 8) :=
  ((gatherJBlock5 body).map (encodeJBlock physAlloc)).getD []

/-- **The JInstr full-body ELF entry over a physical body.** Stitch the framed
    leaf — `wrapFundefBytes body (jBodyBytes body)` as a single `STT_FUNC` `.text`
    named `fname` — through the SAME `ElfObject.buildElfObjectMulti` +
    `bytesToByteArray` `compileLprogToElf` uses, returning a `ByteArray`. This is the
    JInstr drop-in for `compileLprogToElf` on a one-function `Lprog`. -/
def jElf (body : List Linstr) (fname : String) : ByteArray :=
  bytesToByteArray
    (ElfObject.buildElfObjectMulti
      [{ name := fname, text := wrapFundefBytes body (jBodyBytes body) }])

/-- The physical-ABI body of a `Com`: the single exported function's `lfd_body` from
    `Com.toLprogPhysAbi` — the SAME extraction `PhysBodyGather.physBody` performs and
    the SAME `Lprog` the `compileComToElf` entry encodes. -/
def physBodyOf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) : List Linstr :=
  ((Com.toLprogPhysAbi com fname).lp_funcs.head?.map (fun p => p.2.lfd_body)).getD []

/-- **The full-body JInstr owned-emit ELF entry — the drop-in for `compileComToElf`.**
    Lower the `Com` to its physical-ABI body the SAME way `compileComToElf` does
    (`Com.toLprogPhysAbi`), then build the single-`STT_FUNC` ELF object through the
    full-body JInstr gather (`jElf` = framed `gatherJBlock5` bytes →
    `buildElfObjectMulti` → `ByteArray`). On a `gatherJBlock5`-coverable kernel the
    bytes equal `compileComToElf com fname` (the body bytes agree, the framing wrap
    and ELF stitch are the SAME), so this is a byte-safe re-point target for the
    GoldenPath kernels' `_x86_elf` defs. -/
def compileComToElfJInstrFull {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) : ByteArray :=
  jElf (physBodyOf com fname) fname

/-! ## 2. The conditional whole-ELF byte-identity theorem

Everything above the body byte-agreement is a closed theorem: given `jBodyBytes
body = encodeLcmd body` (the `#eval`-level fact `SpillSlotEncode` §3 supplies for the
real kernel), the JInstr-full ELF `ByteArray` equals the `Lprog` entry's
`compileLprogToElf` of the one-function `Lprog` whose body is `body`. The framing
wrap collapses to `encodeLfundefBytes body` definitionally, and lifting the matched
single-leaf `.text` through `buildElfObjectMulti` gives the WHOLE-object byte
identity — symbol table, section headers, everything. -/

/-- `wrapFundefBytes body (encodeLcmd body)` is exactly `encodeLfundefBytes body`:
    the framing wrapper specialises to the trusted leaf-ABI framing when the body
    slot is the Lprog body bytes. Definitional. -/
theorem wrap_encodeLcmd (body : List Linstr) :
    wrapFundefBytes body (encodeLcmd body) = encodeLfundefBytes body := rfl

/-- **The conditional whole-ELF byte identity.** Under the body byte-agreement
    `jBodyBytes body = encodeLcmd body` (the resolver-discharged full-body block
    agreement — `SpillSlotEncode` §3, `#eval`-certified on the real kernel), the
    JInstr full-body ELF `ByteArray` (`jElf body fname`) equals the `Lprog` entry's
    `compileLprogToElf` of the single-function `Lprog` whose one function is
    `(fname, body)`. Both factor through the SAME `ElfObject.buildElfObjectMulti` on
    a single leaf whose `.text` is `encodeLfundefBytes body`, so the match covers the
    whole ELF object rather than the `.text` section alone. -/
theorem jElf_eq_lprogElf (body : List Linstr) (fname : String)
    (hbody : jBodyBytes body = encodeLcmd body) :
    jElf body fname
      = compileLprogToElf
          { lp_rip := "RIP", lp_rsp := "RSP", lp_globs := [], lp_glob_names := []
          , lp_funcs := [(fname, { lfd_body := body })] } := by
  unfold jElf
  rw [hbody]
  show bytesToByteArray (ElfObject.buildElfObjectMulti
        [{ name := fname, text := wrapFundefBytes body (encodeLcmd body) }]) = _
  rfl

/-! ## 3. The whole-ELF byte-match + the re-point demo, on the real kernel `asconSigma0`

THE MILESTONE: the full-body JInstr ELF entry byte-matches `compileComToElf` on a
real GoldenPath kernel, and re-pointing the kernel's `_x86_elf` to it is byte-safe.
The `#eval` certificates on `AsconLinear.asconSigma0Com`
(`compileComToElfJInstrFull asconSigma0Com == compileComToElf asconSigma0Com`,
`768 = 768`, and the re-point demo) are re-homed in `GoldenPathByteIdentityDemo`
(above the chain) so this file is GoldenPath-free. The generic `physBodyOf` /
`compileComToElfJInstrFull` entry and the framing/stitch theorems (§1–§2) — all
kernel-independent — stay here. -/

end CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElfJInstrFull
