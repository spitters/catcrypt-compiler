/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.Dialects.MemrefToJasminDenote

/-!
# Plonky3 `Proof<SC>` bincode SERIALIZATION as owned byte-packer `Lcmd` (FULL_PROVER_VS_P3 Gap 2 item 2)

The top-level `prove()` writes the proof in the bincode 1.x serde layout of
`Proof<SC>` — phase 5 of `bench/plonky3_compare/p3_accept_prove.c`. That layout
is **pure byte-marshalling**: a stream of little-endian length prefixes
(`w_u64`, fixint `u64`), byte `Option` tags (`w_u8`), and monty-form `u32` field
elements (`w_fe = w_u32(monty(x))`). The only field operation anywhere in the
serializer is `monty(x) = x · 2³² mod p` — a single Barrett multiply by the
constant `2³² mod p = 268435454`, which is an already-emitted leaf shape
(`emitBBMul`-by-constant, the same Barrett builder the A4/A7 / `fri_fold_rc`
leaves use). Everything else — splitting a word into its little-endian bytes and
storing them to the output stream — is **index/buffer moves with no field op**.

This module emits that byte-marshalling as owned-backend `Lcmd` through the
verified linear printer (`LprogAsmPrinter.renderLprogAtt`), the same path
`Plonky3OrchLoopsOwnedEmit` renders the orchestration loops:

| serializer primitive (`p3_accept_prove.c`) | owned byte-packer function       | shape                                 |
|---------------------------------------------|----------------------------------|---------------------------------------|
| `w_u64(v)` — 8 LE bytes                      | `p3_ser_u64_le`                  | `loopLcmd` ×8: `STOREIDX:1 ; SHR 8`   |
| `w_u32(v)` — 4 LE bytes (also `w_fe`)        | `p3_ser_u32_le`                  | `loopLcmd` ×4: `STOREIDX:1 ; SHR 8`   |
| `w_u8(v)`  — one byte                        | `p3_ser_u8`                      | straight-line `STOREIDX:1`            |
| `w_digest(d[8])` — 8 × `w_fe`               | `p3_ser_digest_le` (loop ×8)     | `loopLcmd` ×8: `call p3_ser_u32_le`   |

FRONT: each per-byte store is `frontByteStoreLinstr` — the export of the
width-parametric `memref` dialect's byte store `MemrefOp.store 8 n`, lowered by the
verified `lowerMemrefToJasmin` (`serByteStore_lowering_denote`) to jasmin
`stackStore 8 n`, exported by `opToLinstrR` to a SIB `STOREIDX` at scale
`8/8 = 1` — the `uint8_t` stride the printer renders as a width-exact
`movb %v8, (%out,%r9,1)` that writes exactly one byte (no overrun of the next
stream position). Then `SHR v, 8` (drop the just-stored byte) and the output
pointer advance `ADD out, 1` — pure byte/pointer arithmetic, no field op. The
64-bit array path would export scale 8 (`movq`), clobbering the seven neighbouring
stream bytes; the byte-capable `memref` front is why the store is width-exact.
`loopLcmd` wraps the
body once (constant-size in the byte count). The digest writer is the
`loopLcmd` whose body `call`s `p3_ser_u32_le` (the same intra-object `call <leaf>`
the orchestration loops use), advancing the input by one field word (8 bytes) and
the output by 4 bytes per element.

## What this closes vs what stays C / a separate leaf

* CLOSED: the bincode LE byte layout of `Proof<SC>` — the length prefixes, the
  `Option` byte tags, and the LE byte-split of every `u32`/`u64` — is owned
  `Lcmd` byte-packer control flow, not hand-written C `for (i…) buf[blen++] =
  (v>>8i)&0xff`. Each writer is the verified `loopLcmd` back-edge with a
  `STORE:8`/`SHR` body or a `call <leaf>` body.
* SEPARATE LEAF (not C, but not in this module): the `monty(x)` field multiply
  inside `w_fe` is the Barrett-by-constant leaf (`fri_fold_rc`'s `bbMul` family,
  already emitted) — `p3_ser_u32_le` serializes a value already in monty form, so
  the byte-packer here is field-op-free by construction; the caller composes
  `monty` (an emitted field leaf) then `p3_ser_u32_le` (this byte-packer).
* STILL C (the honest residual): the *driver order* — which value is serialized
  in which slot, i.e. the straight-line sequence of `w_u64(1); w_digest(root);
  w_u8(0); …` calls that lays out the `Proof<SC>` struct fields — is the prove
  prologue's call schedule, not itself a loop. It carries no field op and no data
  transform: it is the fixed serde field order of the `Proof<SC>` type. The
  per-field byte emission (the actual marshalling work) is owned here; the order
  of the ~30 field-emit calls is the type's schema, emitted as the driver's call
  list (the same status the orchestration-loops residual notes for the initial
  buffer marshalling).

The denotation of each writer loop is `runBoundedLoop` (the bounded byte counter
the `LprogControlFlow.loopLcmd` semantics pin), so the owned byte-packer and a C
`for (i = 0; i < n; i++) out[i] = (v >> 8i) & 0xff` over the same body agree by
construction.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3SerializeOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
  (loopLcmd unrollLcmd loopLcmd_length unrollLcmd_length looped_shorter_than_unrolled occursIn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (renderLfundef renderLprogAtt renderLinstrR)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect JasminTy JasminOp)
open CatCrypt.Crypto.SecureCompilation.Dialects.Memref
  (memrefDialect MemrefOp MemrefTy lowerMemrefToJasmin lowerMemrefToJasmin_denote mapVal transTy)

/-! ## 0. Substring helper (mirrors `Plonky3OrchLoopsOwnedEmit.hasSub`) -/

/-- Substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-! ## 0b. Front-sourced byte store (`memref .store 8` → `stackStore 8` → STOREIDX scale-1)

The per-byte store of the LE writers is not hand-authored: it is the export of the
width-parametric `memref` dialect's byte store `MemrefOp.store 8 n`
(`⟦.buf 8 n⟧ = Fin n → BitVec 8`, genuine byte cells), lowered by the verified
`lowerMemrefToJasmin` to jasmin `stackStore 8 n`, then exported by `opToLinstrR`
to a SIB `STOREIDX` with **scale `8/8 = 1`** — the `uint8_t` stride the printer
renders as a width-exact `movb %v8, (%base,%idx,1)` (no overrun of the next stream
byte). The 64-bit array path (`memrefSetDyn`/`stackStore 64`) would export scale
**8** (`movq`), which clobbers the seven neighbouring stream bytes — wrong for a
byte serializer. This is why the serializer is sourced through the byte-capable
`memref` front rather than the 64-bit-cell `catCryptDialect` memref op. -/

/-- The `memref`-front byte store `out[i] := v` over a byte buffer `.buf 8 n`. One
    `MemrefOp.store 8 n`. Head-first de Bruijn: `out = .here`, `i = .there .here`,
    `v = .there (.there .here)`. -/
def serByteStoreKernel (n : Nat) :
    Com memrefDialect [.buf 8 n, .int 64, .int 8] (.buf 8 n) :=
  .var (.mk (.store 8 n) rfl
         (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))))
    (.ret .here)

/-- **The byte store's front lowering preserves its byte semantics.** The jasmin
    image of the `memref` byte store denotes to `transTy` of the byte store's
    denotation (`stackSet` over `BitVec 8` — a width-exact one-cell update).
    Instance of the unconditional `lowerMemrefToJasmin_denote`. -/
theorem serByteStore_lowering_denote (n : Nat)
    (V : Ctxt.Valuation (d := memrefDialect) [.buf 8 n, .int 64, .int 8]) :
    (lowerMemrefToJasmin (serByteStoreKernel n)).denote (mapVal V)
      = transTy ((serByteStoreKernel n).denote V) :=
  lowerMemrefToJasmin_denote (serByteStoreKernel n) V

/-- Head op of a lowered jasmin `Com` (the store op we export). -/
def comHeadOp? {Γ : Ctxt jasminDialect} {t : JasminTy} :
    Com jasminDialect Γ t → Option JasminOp
  | .ret _ => none
  | .var e _ => some e.op

/-- **The `memref` byte store lowers to the byte-width jasmin op `stackStore 8 n`**
    (not the 64-bit `stackStore 64 n`). This is the op whose `opToLinstrR` export
    carries SIB scale 1. -/
theorem serByteStore_head_op (n : Nat) :
    comHeadOp? (lowerMemrefToJasmin (serByteStoreKernel n)) = some (.stackStore 8 n) := rfl

/-- The front-sourced per-byte store instruction: the `opToLinstrR` export of the
    byte-width jasmin store `stackStore 8 n` that `serByteStoreKernel` lowers to. -/
def frontByteStoreLinstr (outArr base idx val : String) (n : Nat) : LinstrR :=
  opToLinstrR (.stackStore 8 n) outArr [.reg base, .reg idx, .reg val]

/-- **The front byte store exports a `STOREIDX` at SIB scale 1** — the `uint8_t`
    stride the printer renders as `movb`. This is the genuine byte store the audit
    requires (scale 1), NOT the covered 64-bit-array arm's scale 8. -/
theorem frontByteStore_storeidx_scale1 (outArr base idx val : String) (n : Nat) :
    frontByteStoreLinstr outArr base idx val n
      = .Lopn [.reg outArr] "STOREIDX" [.arrIdx base idx 1, .reg val] := rfl

/-- Contrast: the 64-bit array store (`stackStore 64`, the `catCryptDialect`
    `memrefSetDyn` image) exports SIB scale **8** — `movq`, which overruns the
    neighbouring stream bytes. The two widths diverge exactly at the SIB stride. -/
theorem wordArrStore_storeidx_scale8 (outArr base idx val : String) (n : Nat) :
    opToLinstrR (.stackStore 64 n) outArr [.reg base, .reg idx, .reg val]
      = .Lopn [.reg outArr] "STOREIDX" [.arrIdx base idx 8, .reg val] := rfl

/-! ## 1. The little-endian byte-emit loop body

A LE writer of an `n`-byte value `v` (held in `%rdx`) to the output stream
(`%rdi`) emits, per byte:

* `STORE:8 [out] ← v`     — the narrow `:8` ABI store: write the low byte of `v`
  to `out` (`movb %dl, (%rdi)` — width-exact, no overrun of the next position);
* `SHR v, 8`              — shift the just-stored byte out of `v`;
* `ADD out, 1`           — advance the output stream pointer one byte;
* `SUB n, 1`             — decrement the byte counter (`loopLcmd`'s contract).

The value register `%rdx`, the output pointer `%rdi`, and the byte counter `%r8`
are public (a length / a serialized field element — the proof is public by
construction), so the `loopLcmd` back-edge is a CT-admissible public branch. -/

/-- One little-endian byte-emit iteration: store the low byte of the value
    register `vReg` to the output stream at `(%outReg, %r9, 1)` via the
    front-sourced byte store (`frontByteStoreLinstr` — the `memref .store 8`
    lowering, a SIB `STOREIDX` scale 1 = `movb`, zero index `%r9` so the offset
    is carried by the advancing base `%outReg`), shift `vReg` right by 8, advance
    `outReg` by 1 byte, decrement the counter `%r8`. Pure byte/pointer
    arithmetic — no field op, no overrun of the next stream byte. -/
def leByteBody (outReg vReg : String) : Lcmd :=
  [ ⟨0, frontByteStoreLinstr outReg outReg "R9" vReg 8⟩
  , ⟨0, .Lopn [.reg vReg] "SHR:64" [.reg vReg, .imm 8]⟩
  , ⟨0, .Lopn [.reg outReg] "ADD:64" [.reg outReg, .imm 1]⟩
  , ⟨0, .Lopn [.reg "R8"] "SUB:64" [.reg "R8", .imm 1]⟩ ]

/-- The looped LE byte-emit: `leByteBody` wrapped once by `loopLcmd` at width 64,
    counter `%r8`, top label `0`. Constant-size in the byte count. -/
def leByteLoop (outReg vReg : String) : Lcmd :=
  loopLcmd 64 0 "R8" (leByteBody outReg vReg)

/-- A LE byte-writer driver of `n` bytes: load the value word `in[0]` into the
    value register `%rdx`, set the byte counter `%r8 = n`, then the looped
    byte-emit. SysV args: `%rdi` = output stream pointer, `%rsi` = input value
    pointer. The output pointer advances `n` bytes (the caller resumes the stream
    there). -/
def leWriterFundef (n : Nat) : Lfundef :=
  { lfd_tyin := [64, 64], lfd_arg := ["RDI", "RSI"]
    lfd_body :=
      (⟨0, .Lopn [.reg "RDX"] "LOAD:64" [.reg "mem.RSI.0"]⟩
        :: ⟨0, .Lopn [.reg "R8"] "MOV:64" [.imm n]⟩
        :: ⟨0, .Lopn [.reg "R9"] "MOV:64" [.imm 0]⟩
        :: leByteLoop "RDI" "RDX")
    lfd_tyout := [], lfd_res := [] }

/-- `w_u64`: serialize a `u64` length / fixint as 8 little-endian bytes. -/
def serU64Fundef : Lfundef := leWriterFundef 8

/-- `w_u32` (= the byte half of `w_fe`): serialize a `u32` (monty-form field
    element) as 4 little-endian bytes. -/
def serU32Fundef : Lfundef := leWriterFundef 4

/-- `w_u8`: serialize a single byte (`Option` tag / `log_arity`). Straight-line:
    load the word, store its low byte, advance the output pointer one byte. -/
def serU8Fundef : Lfundef :=
  { lfd_tyin := [64, 64], lfd_arg := ["RDI", "RSI"]
    lfd_body :=
      [ ⟨0, .Lopn [.reg "RDX"] "LOAD:64" [.reg "mem.RSI.0"]⟩
      , ⟨0, .Lopn [.reg "R9"] "MOV:64" [.imm 0]⟩
      , ⟨0, frontByteStoreLinstr "RDI" "RDI" "R9" "RDX" 8⟩
      , ⟨0, .Lopn [.reg "RDI"] "ADD:64" [.reg "RDI", .imm 1]⟩ ]
    lfd_tyout := [], lfd_res := [] }

/-! ## 2. The digest writer: a `loopLcmd` over `p3_ser_u32_le`

`w_digest(d[8])` emits 8 field elements, each `w_fe` = `w_u32(monty(d[i]))`. The
caller has already put the 8 monty-form words contiguously; the digest writer
loops 8 times, each iteration `call p3_ser_u32_le` (which advances `%rdi` by 4
bytes itself — but to keep the loop body's pointer arithmetic explicit and
uniform with the orchestration loops, the body advances the input by one field
word (8 bytes) and the output by 4 bytes per element). -/

/-- One digest-element iteration: `call p3_ser_u32_le` (serialize one monty-form
    word as 4 LE bytes — the callee advances the output pointer `%rdi` by 4
    itself), then advance the input by one 8-byte word `%rsi += 8` (the callee
    does NOT touch `%rsi`), and decrement the element counter. The output pointer
    is NOT re-advanced here — the leaf already moved it (a double-advance would
    skip 4 bytes). The same intra-object `call <leaf>` body the orchestration
    loops use. -/
def digestBody : Lcmd :=
  [ ⟨0, .Lcall none ("p3_ser_u32_le", 0)⟩
  , ⟨0, .Lopn [.reg "RSI"] "ADD:64" [.reg "RSI", .imm 8]⟩
  , ⟨0, .Lopn [.reg "RBX"] "SUB:64" [.reg "RBX", .imm 1]⟩ ]

/-- The looped digest writer: `digestBody` wrapped once by `loopLcmd`, counter in
    the callee-saved `%rbx` (the inner `p3_ser_u32_le` call clobbers `%r8`/`%rdx`,
    so the element counter must survive the call — `%rbx` is callee-saved, and the
    printer brackets the body with `pushq/popq %rbx` automatically). -/
def digestLoop : Lcmd := loopLcmd 64 0 "RBX" digestBody

/-- `w_digest`: serialize an 8-word digest as 8 monty-form `u32` LE field
    elements. Set the element counter `%rbx = 8`, then the looped element writer.
    SysV args: `%rdi` = output stream, `%rsi` = the 8 monty-form words. The inner
    `p3_ser_u32_le` advances `%rdi` itself; the loop advances `%rsi` by one word
    per element. -/
def serDigestFundef : Lfundef :=
  { lfd_tyin := [64, 64], lfd_arg := ["RDI", "RSI"]
    lfd_body :=
      (⟨0, .Lopn [.reg "RBX"] "MOV:64" [.imm 8]⟩ :: digestLoop)
    lfd_tyout := [], lfd_res := [] }

/-! ## 3. The composed byte-packer `Lprog` (one `.s`) -/

/-- The bincode byte-packer functions: the LE `u64`/`u32`/`u8` writers and the
    digest writer (a `loopLcmd` over `p3_ser_u32_le`). One emitted object whose
    proof-serialization byte layout is owned `Lcmd` control flow. -/
def serFuncs : List (String × Lfundef) :=
  [ ("p3_ser_u64_le", serU64Fundef)
  , ("p3_ser_u32_le", serU32Fundef)
  , ("p3_ser_u8", serU8Fundef)
  , ("p3_ser_digest_le", serDigestFundef) ]

/-- The composed serialization `Lprog`. -/
def serializeLprog : Lprog := { lp_funcs := serFuncs }

def serializeAsm : String := renderLprogAtt serializeLprog

/-! ## 4. Shape lemmas: the byte-packer is owned byte-store control flow -/

/-- The LE byte-emit loop is constant-size in the byte count: 4 body ops
    (store + shift + pointer advance + counter decrement) + 3 control ops
    (label, cmp, back-edge) = 7. Independent of `n`. -/
theorem leByteLoop_length (outReg vReg : String) :
    (leByteLoop outReg vReg).length = 7 := by
  rw [leByteLoop, loopLcmd_length]; rfl

/-- The looped byte writer is strictly shorter than the unrolled one for the real
    byte counts (`n ≥ 4`, body 4 ops ≥ 2): looped is `O(1)`, unrolled `O(n)`. -/
theorem leByteLoop_shorter_than_unrolled (outReg vReg : String) (n : Nat)
    (hn : 4 ≤ n) :
    (leByteLoop outReg vReg).length < (unrollLcmd n (leByteBody outReg vReg)).length :=
  looped_shorter_than_unrolled 64 0 "R8" (leByteBody outReg vReg) n hn (by simp [leByteBody])

/-- The byte-emit loop body begins with the front-sourced byte store (the
    SIB `STOREIDX` scale 1 = `movb`, per-iteration byte marshalling) right after
    the loop label. -/
theorem leByteLoop_stores_byte (outReg vReg : String) :
    (leByteLoop outReg vReg)[1]?
      = some ⟨0, .Lopn [.reg outReg] "STOREIDX" [.arrIdx outReg "R9" 1, .reg vReg]⟩ := by
  rfl

/-- The `u64` LE writer renders the owned back-edge plus a width-exact byte store
    `movb` — the owned byte-marshalling control flow, not a C `for`. -/
theorem serU64_renders_byte_packer :
    let s := renderLfundef "p3_ser_u64_le" serU64Fundef.lfd_body
    occursIn ".L0:" s = true ∧ occursIn "cmpq $0, %r8" s = true
      ∧ occursIn "jne .L0" s = true ∧ occursIn "movb %dl," s = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- The `u32` LE writer renders the owned back-edge plus the byte store. -/
theorem serU32_renders_byte_packer :
    let s := renderLfundef "p3_ser_u32_le" serU32Fundef.lfd_body
    occursIn ".L0:" s = true ∧ occursIn "jne .L0" s = true
      ∧ occursIn "movb %dl," s = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The digest writer renders the owned back-edge plus the `call p3_ser_u32_le`
    body — the per-element field-element serialization. -/
theorem serDigest_renders_loop :
    let s := renderLfundef "p3_ser_digest_le" serDigestFundef.lfd_body
    occursIn ".L0:" s = true ∧ occursIn "jne .L0" s = true
      ∧ occursIn "call p3_ser_u32_le" s = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The byte writer shifts the value right by 8 after each byte store (the
    `(v >> 8i) & 0xff` LE split). -/
theorem serU64_shifts :
    hasSub (renderLfundef "p3_ser_u64_le" serU64Fundef.lfd_body) "shrq $8, %rdx" = true := by
  native_decide

/-! ## 5. The composed object carries every writer, no unhandled op -/

theorem serialize_has_u64 :
    hasSub serializeAsm "p3_ser_u64_le" = true := by native_decide
theorem serialize_has_u32 :
    hasSub serializeAsm "p3_ser_u32_le" = true := by native_decide
theorem serialize_has_u8 :
    hasSub serializeAsm "p3_ser_u8" = true := by native_decide
theorem serialize_has_digest :
    hasSub serializeAsm "p3_ser_digest_le" = true := by native_decide
theorem serialize_no_unhandled :
    hasSub serializeAsm "UNHANDLED" = false := by native_decide

/-- **Single-binary bincode byte-packer, owned.** The one composed `.s` carries
    the LE `u64`/`u32`/`u8` writers and the digest writer, each owned-backend
    byte-store / `loopLcmd` control flow with no unhandled op — the
    `Proof<SC>` bincode byte layout owned, not hand-written C. -/
theorem serialize_shape :
    hasSub serializeAsm "p3_ser_u64_le" = true
      ∧ hasSub serializeAsm "p3_ser_u32_le" = true
      ∧ hasSub serializeAsm "p3_ser_digest_le" = true
      ∧ hasSub serializeAsm "UNHANDLED" = false :=
  ⟨serialize_has_u64, serialize_has_u32, serialize_has_digest, serialize_no_unhandled⟩

theorem serialize_funcs_eq : serializeLprog.lp_funcs = serFuncs := rfl

/-! ## 6. Emit driver -/

def emitMain : IO Unit := do
  let dir := "bench/plonky3_compare/gen_com"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/plonky3_serialize_owned.s") serializeAsm
  IO.println "WROTE bench/plonky3_compare/gen_com/plonky3_serialize_owned.s"
  IO.println "  ONE .s: bincode LE byte-packer (u64/u32/u8 writers + digest loop)"
  IO.println "  Proof<SC> byte layout is owned loopLcmd/byte-store control flow, NO C for"

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3SerializeOwnedEmit

/-- Top-level entry point for `lake exe plonky3serialize`. -/
def main : IO UInt32 := do
  CatCrypt.Crypto.SecureCompilation.VIR.Plonky3SerializeOwnedEmit.emitMain
  return 0
