/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExportSha2
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit
public import CatCrypt.Crypto.SecureCompilation.VIR.Sha2RotateSelect
public import CatCrypt.Crypto.SecureCompilation.VIR.AesBitsliceEmit
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf
public import CatCrypt.Crypto.Optimizer.Batch8
public import CatCrypt.Crypto.Optimizer.Batch8Emit

/-!
# Compiled SHA-2 linear-jasmin owned-RA producer (task #469 / #462 / #475)

The `lean --run` interpreter cannot materialize `Sha2Emit.compressCom
sha256Spec` (it blows the interpreter recursion stack on `emitOp` and runs
the super-quadratic spec definitions of `nameSlot` / `physTable` /
`physBodyWithStores`). This module is the same producer as
`bench/sha2_linear_compare/sha256_linear.lean`, but compiled as a `lean_exe`
(`lake exe sha256linear`) so it runs as native code: the C call stack handles
`compressCom`, and the `@[implemented_by]` compiled paths in
`JasminLprogExport` fire (the spec's `O(n³)` `nameSlot` / `O(n²)` live-range
scan and `physTable` / per-position `bidx` recomputation are replaced by
single-pass `Array` / `Std.HashMap` builds).

The same compiled exe also emits the **SHA-512** owned-RA blob (task #475)
when invoked with the argument `sha512`: SHA-512 shares the input layout and
the producer chain, differing only in U64 word width (the `regArith _ 64`
ops carry the `":64"` tag), the 80-round constant table, the `2^64-1` mask,
and the wider sigma-rotate immediate window — all handled by the
`sha512ImmSlots` / `sha512InLoadMap` / `sha512OutStoreMap` maps in
`JasminLprogExportSha2`. The 80-round U64 body has higher GP register
pressure than SHA-256, so it spills more; `read_linear`'s #470 reserved
stack frame sizes itself from the emitted spill count (8-byte cells).
-/

@[expose] public section

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
  (Com.toLprogPhysAbi Com.writeLprogPhysAbiFile
   ImmSlotMap InLoadMap OutStoreMap Lprog
   sha256ImmSlots sha256InLoadMap sha256OutStoreMap
   sha512ImmSlots sha512InLoadMap sha512OutStoreMap
   sha256ResidentImmSlots sha256ResidentInLoadMap
   sha512ResidentImmSlots sha512ResidentInLoadMap)
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2Emit (compressCom sha256Spec sha512Spec inCtxt Rw)
open CatCrypt.Crypto.SecureCompilation.VIR.Sha2RotateSelect (compressComRor)
open CatCrypt.Crypto.Optimizer.Batch8 (batch8)
open CatCrypt.Crypto.Optimizer.Batch8Emit (batch8ToLprogPhysAbi)

/-! ## batch8 SoA reg-256 ABI maps (SHA-256 x8)

The batch8 widening (`Batch8.batch8`) packs eight `u32` SHA-256 lanes into one
256-bit YMM register per binding. `widen8Ctxt = Γ.map widen8Ty` preserves the
argument prefix length and order (the `#ROR` expansion adds body bindings, not
arguments), so these reg-256 maps reuse the SAME argument-slot indices as the
scalar `sha256*` maps in `JasminLprogExportSha2`, widening only the memory
stride from 4 to 32 bytes (one YMM = 8 lanes × 4 bytes). -/

/-- reg-256 immediate-slot map: empty. In the widened body every shift literal
    rides inside `.vpslld n` / `.vpsrld n` (the printer emits the immediate) and
    the all-ones mask moves from an immediate to a broadcast YMM load
    (`sha256InLoad256`, slot 70), so no argument slot is rendered as an
    immediate. -/
def sha256ImmSlots256 : ImmSlotMap := fun slot =>
  -- Shift-amount literals (input `200+n` ↦ slot `69-n`, so slots 39..69) are the
  -- per-lane shift COUNTS. They stay immediates (`n = 69 - slot`); the widened
  -- `vpsllvd`/`vpsrlvd` with a constant count is rendered as the immediate
  -- `vpslld`/`vpsrld $n` (a uniform per-lane shift). The all-ones mask (slot 70)
  -- is NOT an immediate here — it is a broadcast YMM loaded via `sha256InLoad256`,
  -- since a 256-bit constant cannot be a scalar immediate operand of `vpxor`.
  if 39 ≤ slot ∧ slot ≤ 69 then some (69 - slot) else none

/-- Byte offset from `RSI` of the pre-broadcast all-ones YMM the mask slot reads:
    just past the 88 loaded YMM words at slots 182..269, i.e.
    `(269 - 182 + 1) * 32 = 2816`. The KAT harness writes an all-ones YMM there. -/
def sha256Mask256Off : Nat := 2816

/-- reg-256 SoA input-load map: argument slot → `(base, byte offset)` with YMM
    stride 32. Slots 182..269 read word `269 - slot` from `RSI` at
    `(269 - slot) * 32` (constant slots read a pre-broadcast YMM, message and
    chaining slots read a SoA YMM — the KAT harness lays the buffer out so); slot
    70 (the all-ones mask) reads the broadcast YMM at `sha256Mask256Off`. -/
def sha256InLoad256 : InLoadMap := fun slot =>
  if 182 ≤ slot ∧ slot ≤ 269 then
    some ("RSI", (269 - slot) * 32)
  else if slot = 70 then
    some ("RSI", sha256Mask256Off)
  else none

/-- reg-256 SoA output-store map: eight YMM stores, output word `j` to `RDI` at
    byte offset `j * 32`. -/
def sha256OutStore256 : OutStoreMap :=
  (List.range 8).map (fun j => ("RDI", j * 32))

/-- Emit one SHA-2 variant's owned-RA `.lprogbin`, reporting the body size and
    the max spill slot index (so the #470 reserved-frame layout can be checked).
    `cellBytes` is 4 (U32, SHA-256) or 8 (U64, SHA-512). -/
def emitOne {w : Nat} (com : Com jasminDialect (inCtxt w) (Rw w))
    (fnName : String) (outPath : System.FilePath)
    (immSlots : ImmSlotMap) (inLoad : InLoadMap) (outStore : OutStoreMap)
    (cellBytes : Nat) : IO UInt32 := do
  IO.println s!"{fnName}: link 1/7 (Com -> ABI-wrapped Linear.lprog) [compiled]"
  let lp : Lprog :=
    Com.toLprogPhysAbi com fnName (fun _ => none) immSlots inLoad outStore
  IO.println s!"  functions     : {lp.lp_funcs.length}"
  match lp.lp_funcs.head? with
  | some (name, f) =>
      IO.println s!"  function name : {name}"
      IO.println s!"  args          : {f.lfd_arg.length} (2-pointer SysV ABI expected)"
      IO.println s!"  body linstrs  : {f.lfd_body.length} (prologue + two-addr + epilogue)"
      let mut maxSpill : Int := -1
      for li in f.lfd_body do
        match li.li_i with
        | .Lopn dsts _ srcs =>
            for o in (dsts ++ srcs) do
              match o with
              | .reg nm =>
                  if "k.".isPrefixOf nm then
                    match (nm.drop 2).toNat? with
                    | some k => if (k : Int) > maxSpill then maxSpill := k
                    | none => pure ()
              | _ => pure ()
        | _ => pure ()
      IO.println s!"  max spill k.N : {maxSpill} (reserved frame: {maxSpill + 1} cells * {cellBytes}B + 8 qsave)"
  | none => pure ()
  Com.writeLprogPhysAbiFile com fnName outPath (fun _ => none) immSlots inLoad outStore
  let sz := (← outPath.metadata).byteSize
  IO.println s!"link 1/7 OK : {outPath} written ({sz} bytes)"
  -- OWNED path (task #537): render the SAME `Lprog` to AT&T `.s` directly via
  -- `LprogAsmPrinter.renderLprogAtt`, removing the patched-jasmin encoder.
  -- Written as `<base>_x86_from_lean.s` next to the `.lprogbin`, assembled by
  -- `gas` exactly like the hand-authored `*_x86_from_lean.s` kernels.
  let base := (outPath.toString.dropEnd 9).toString   -- strip ".lprogbin"
  let ownedPath : System.FilePath := base ++ "_x86_from_lean.s"
  let asm := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned lp
  let t0 ← IO.monoNanosNow
  IO.FS.writeFile ownedPath asm
  let t1 ← IO.monoNanosNow
  IO.println s!"OWNED emit OK : {ownedPath} written ({asm.toUTF8.size} bytes, owned render {(t1 - t0) / 1000} us)"
  -- BYTES-DIRECT path (task #658): byte-encode the SAME `Lprog` straight to an
  -- ELF `.o` via `LprogBytes.encodeLprog` (the looped byte encoder, now covering
  -- the `%rsp`-relative spill/qsave slots this register-pressured body uses), with
  -- NO assembler. Also dump the function body's verified-encoder `.text` (the
  -- looped body bytes incl. every spill load/store) so the differential KAT can
  -- assert it is byte-identical to the gas-assembled `renderLprogAtt` `.text`.
  -- BYTES-DIRECT path, now via the GENERIC owned driver
  -- (`CompileComToElf.compileLprogToElf` = the packaged `encodeLprog` + ByteArray
  -- adapter; byte-identical to the former inline emit). `toBA` is the generic's
  -- adapter, reused below for the body-only `.text` bytes.
  let oBytes := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes.encodeLprog lp
  let oPath : System.FilePath := base ++ "_owned_enc.o"
  let toBA : List (BitVec 8) → ByteArray :=
    CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf.bytesToByteArray
  IO.FS.writeBinFile oPath
    (CatCrypt.Crypto.SecureCompilation.X86Backend.CompileComToElf.compileLprogToElf lp)
  -- the looped function body's `.text` bytes only (the differential-KAT target),
  -- plus the matching body-only `.s` the gas baseline assembles. Both use the SAME
  -- frame size + spill width (`frameSize` / `bodyIsU64`) the byte encoder computes
  -- internally, so the gas-assembled `.text` is the exact baseline for the encoder
  -- bytes — INCLUDING every `<off>(%rsp)` spill load/store (the SIB+disp bytes).
  match lp.lp_funcs.head? with
  | some (nm, f) =>
      let body := f.lfd_body
      let textBytes := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes.encodeLcmd body
      IO.FS.writeBinFile (base ++ "_owned_enc_text.bin") (toBA textBytes)
      let frame := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.frameSize body
      let spillW := if CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.bodyIsU64 body
                    then 64 else 32
      let bodyLines := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter.renderLcmd
                         frame spillW body ""
      let bodyS := "\t.text\n\t.globl " ++ nm ++ "_body\n" ++ nm ++ "_body:\n"
                     ++ String.intercalate "\n" bodyLines ++ "\n"
                     ++ "\t.section .note.GNU-stack,\"\",@progbits\n"
      IO.FS.writeFile (base ++ "_owned_body.s") bodyS
      IO.println s!"BYTES emit OK : {oPath} ({oBytes.length} bytes ELF), body .text = {textBytes.length} bytes (incl. spill slots, frame={frame}, spillW={spillW})"
  | none => pure ()
  return 0

/-- Emit the NATIVE-ROTATE SHA-2 compression body (`compressComRor`) as an
    OWNED AT&T `.s` directly at `outS`, exporting `fnName`. Every Σ/σ
    right-rotation is one `#ROR_w` (`.rorImm`) op rather than the `shr; shl; or`
    triple `compressCom` emits; the two are proved to write bit-for-bit identical
    values (`Sha2RotateSelect.emitRotrNative_value_eq_emitRotr_value`), so this is
    FIPS 180-4 compliant and KAT-identical to the canonical scalar emit.

    Both-spilled native single-source `#ROR` rotates are legalized through
    reserved scratch R15 (`JasminLprogExport.lowerNativeShiftRotate`), so the
    owned spilling RA never surfaces an illegal `movq mem,mem`. The ABI maps are
    the SAME owned-RA maps the `ra`/linear emit uses (unchanged input layout).
    No `.lprogbin` / byte-encoder siblings — only the AT&T `.s` the
    `sha2_ror_kat.c` harness assembles. -/
def emitRorS {w : Nat} (com : Com jasminDialect (inCtxt w) (Rw w))
    (fnName : String) (outS : System.FilePath)
    (immSlots : ImmSlotMap) (inLoad : InLoadMap) (outStore : OutStoreMap) : IO UInt32 := do
  IO.println s!"{fnName}: OWNED native-ROR emit (Com -> ABI Lprog -> AT&T .s) [compiled]"
  let lp : Lprog :=
    Com.toLprogPhysAbi com fnName (fun _ => none) immSlots inLoad outStore
  let asm := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned lp
  IO.FS.writeFile outS (asm ++ "\n")
  IO.println s!"OWNED emit OK : {outS} ({asm.toUTF8.size} bytes, symbol {fnName})"
  return 0

/-- Emit the STATE-RESIDENT SHA-2 compression body (`compressCom`) as an OWNED
    AT&T `.s` directly at `outS`, exporting `fnName`, under the **resident ABI**
    (`out[8], inp[24]` where `inp = [M[0..15] | H[0..7]]`). The round constants
    `K[t]` are rendered as in-body immediates (via `immSlots`), so `inp` carries
    NO `K[]` table — the kernel expands the message schedule `W[16..N-1]` from
    `M[0..15]` in-kernel (the SAME `compressCom`'s `emitSched`) and uses K as
    immediates. Same verified two-address body as the scalar `emitOne`; only the
    ABI maps differ. -/
def emitResidentS {w : Nat} (com : Com jasminDialect (inCtxt w) (Rw w))
    (fnName : String) (outS : System.FilePath)
    (immSlots : ImmSlotMap) (inLoad : InLoadMap) (outStore : OutStoreMap) : IO UInt32 := do
  IO.println s!"{fnName}: OWNED resident emit (Com -> ABI Lprog -> AT&T .s) [compiled]"
  let lp : Lprog :=
    Com.toLprogPhysAbi com fnName (fun _ => none) immSlots inLoad outStore
  let asm := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned lp
  IO.FS.writeFile outS (asm ++ "\n")
  IO.println s!"OWNED emit OK : {outS} ({asm.toUTF8.size} bytes, symbol {fnName})"
  return 0

/-- Emit the batch8 (8-lane SoA, reg-256/YMM) SHA-2 compression body as an OWNED
    AT&T `.s`. The scalar `com` is widened by `Batch8.batch8` (each covered `u32`
    lane op becomes its packed YMM block), wrapped by the reg-256 SoA ABI maps
    (`sha256ImmSlots256` / `sha256InLoad256` / `sha256OutStore256`, YMM stride
    32) and rendered by the owned backend `renderOwned`. The exported symbol is
    `<fnName>_x8`; the `.s` is written next to `outPath` as
    `<base>_x8_x86_from_lean.s`. `cellBytes` is the per-lane word width (4 for
    SHA-256 U32). Reached via the `batch8` CLI argument, separate from the
    scalar `emitOne`. -/
def emitOneBatch8 {w : Nat} (com : Com jasminDialect (inCtxt w) (Rw w))
    (fnName : String) (outPath : System.FilePath) (cellBytes : Nat) : IO UInt32 := do
  IO.println s!"{fnName}_x8: OWNED batch8 SoA emit (Com -> fused widen8+ABI Lprog -> AT&T .s) [compiled]"
  let lp : Lprog :=
    batch8ToLprogPhysAbi com (fnName ++ "_x8") (fun _ => none)
      sha256ImmSlots256 sha256InLoad256 sha256OutStore256 (abiW := 256)
  IO.println s!"  [stage] Lprog lowered: {lp.lp_funcs.length} func(s); rendering..."
  let asm := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwnedReserveVecScratch lp
  let base := (outPath.toString.dropEnd 9).toString   -- strip ".lprogbin"
  let ownedPath : System.FilePath := base ++ "_x8_x86_from_lean.s"
  IO.FS.writeFile ownedPath (asm ++ "\n")
  IO.println s!"OWNED batch8 emit OK : {ownedPath} ({asm.toUTF8.size} bytes, symbol {fnName}_x8, {cellBytes}B x8 lanes)"
  return 0

def main (args : List String) : IO UInt32 := do
  if args.contains "resident" then
    -- State-resident (#179) + W-pinned (#180) owned `.s` for the
    -- `sha2-vs-hacl-resident{,-wp}` harnesses. The `_resident` and `_resident_wp`
    -- symbols share ONE body: the harness cross-checks `wp == §9 resident == HACL*`
    -- (`sha2_vs_hacl_resident_wp.c` lines 65-68 / 168-171), so the digest is
    -- identical; the storage-class refinement (named GPRs for the schedule
    -- window) is the owned RA's spill decision, not a body difference.
    --   sha256_compress_resident(uint32_t *out, const uint32_t *inp)  (RDI=out, RSI=inp[24])
    --   sha512_compress_resident(uint64_t *out, const uint64_t *inp)
    IO.FS.createDirAll "bench/sha2_compare/gen"
    for nm in ["sha256_compress_resident", "sha256_compress_resident_wp"] do
      let _ ← emitResidentS (compressCom sha256Spec) nm
        ("bench/sha2_compare/gen/" ++ nm ++ ".s")
        sha256ResidentImmSlots sha256ResidentInLoadMap sha256OutStoreMap
    for nm in ["sha512_compress_resident", "sha512_compress_resident_wp"] do
      let _ ← emitResidentS (compressCom sha512Spec) nm
        ("bench/sha2_compare/gen/" ++ nm ++ ".s")
        sha512ResidentImmSlots sha512ResidentInLoadMap sha512OutStoreMap
    return 0
  else if args.contains "ror" then
    -- Native-rotate (#ROR) owned `.s` for the `sha2-ror-kat` harness:
    --   sha256_compress_ror(uint32_t *out, const uint32_t *inp)  (RDI=out, RSI=inp)
    --   sha512_compress_ror(uint64_t *out, const uint64_t *inp)
    IO.FS.createDirAll "bench/sha2_compare/gen"
    let _ ← emitRorS (compressComRor sha256Spec) "sha256_compress_ror"
      "bench/sha2_compare/gen/sha256_ror.s"
      sha256ImmSlots sha256InLoadMap sha256OutStoreMap
    let _ ← emitRorS (compressComRor sha512Spec) "sha512_compress_ror"
      "bench/sha2_compare/gen/sha512_ror.s"
      sha512ImmSlots sha512InLoadMap sha512OutStoreMap
    return 0
  else if args.contains "aes" then
    -- Bit-sliced AES S-box round (task #468): the carry-free `and`/`xor`/`not`
    -- body that jasminc's RA rejects ("no more free register" in the GF(2^8)
    -- bit-slice multiply). The owned linear-jasmin path spills the high
    -- register pressure to the stack. `aesInCtxt = inCtxt 64` definitionally,
    -- so `emitOne` (the generic SHA-2 producer) applies directly; cellBytes = 8
    -- (U64 bit-planes).
    emitOne AesBitsliceEmit.aesSboxRoundCom "aes_sbox_round"
      "bench/aes_compare/gen_com/aes_sbox_round.lprogbin"
      AesBitsliceEmit.aesSboxImmSlots AesBitsliceEmit.aesSboxInLoadMap
      AesBitsliceEmit.aesSboxOutStoreMap 8
  else if args.contains "sha512" then
    emitOne (compressCom sha512Spec) "sha512_compress"
      "bench/sha2_linear_compare/sha512.lprogbin"
      sha512ImmSlots sha512InLoadMap sha512OutStoreMap 8
  else if args.contains "batch8" then
    -- batch8 (8-lane SoA / YMM) owned `.s`: produces
    -- `sha256_compress_x8_x86_from_lean.s` for the batched byte-KAT harness.
    -- Runs in isolation from the scalar emit so the widening pass's peak
    -- footprint does not stack on top of the scalar render.
    emitOneBatch8 (compressCom sha256Spec) "sha256_compress"
      "bench/sha2_linear_compare/sha256.lprogbin" 4
  else
    emitOne (compressCom sha256Spec) "sha256_compress"
      "bench/sha2_linear_compare/sha256.lprogbin"
      sha256ImmSlots sha256InLoadMap sha256OutStoreMap 4
