/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.MemrefToJasminDenote
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

set_option autoImplicit false

/-!
# `byteRolledForLoopN` — a byte-cell (`movb`, scale-1) rolled `ComL.forLoopN`

The scalar rolled front (`TranslateDialectRolledLoop.rolledForLoopN`) routes its
loop body through the LowCT / `catCryptDialect` front, whose memref cells are
64-bit words (`mapTy (.memref n) = .stackArr 64 n`): an `RArrStore` becomes a
`stackStore 64` and renders `movq`, SIB scale 8. A `.TU8` byte value fed to that
`RArrStore` drops to an opaque `extCall` — the loop still front-compiles
(`isSome = true`) but the emitted store is byte-WRONG (a 64-bit `movq`, clobbering
the 7 neighbouring byte cells).

This module adds the **byte-granular** rolled loop. Byte-width (`movb`, SIB
scale-1, `uint8_t`) indexed stores exist in the standalone width-parametric
`memref` dialect (`Dialects/Memref.lean`): `.buf 8 n → stackStore 8 → STOREIDX`
scale-1 → `movb`, validated end-to-end in `ByteMemrefFrontValidate`. The
combinator here wraps a `memref`-dialect byte loop *body* into a genuine
`ComL.forLoopN`, the byte twin of `rolledForLoopN`:

```
  body : Com memrefDialect [.buf 8 n, .int 64, *invBufs] (.buf 8 n)   -- byte load/store
    --(Memref.lowerMemrefToJasmin, denotation-preserving unconditionally)-->
  JLoopBodyN.update : Com jasminDialect [.stackArr 8 n, .reg 64, *invBufs.map] (.stackArr 8 n)
    --(ComL.forLoopN ⟨N, update⟩ init invs (.ret .here))-->  ComL  (ONE body copy + back-edge)
    --(ComL.toLprogPhysAbi / renderLprogAtt)-------------->  .s     (movb scale-1, real `jne`)
```

Unlike `rolledForLoopN` (which returns `Option`, declining when the scalar front
cannot cover the body), `byteRolledForLoopN` is **total**: the `memref → jasmin`
lowering (`lowerMemrefToJasmin`) is unconditional, so the byte loop is always a
well-formed `ComL`. The body context `[.buf 8 n, .int 64, *invBufs]` maps under
`MemrefTy.toJasmin` *definitionally* to `.stackArr 8 n :: .reg 64 :: invBufs.map
MemrefTy.toJasmin`, exactly the `JLoopBodyN.update` shape (`accTy = .stackArr 8 n`,
`invTys = invBufs.map MemrefTy.toJasmin`), so the `ComL.forLoopN` wrapper
typechecks without a transport.

## Demonstration: the little-endian `u64` serializer as a byte-copy loop

On a little-endian target the serialization `out[i] = (v >> 8·i) & 0xff` of a
`u64 v` **is** the byte copy of `v`'s in-memory representation: byte `i` of `v`
at address `&v + i` equals `(v >> 8·i) & 0xff`. So the LE-`u64` serializer is the
byte loop `out[i] := inp[i]` over `inp = (uint8_t*)&v`, `N = 8` — a `memref` byte
`load` + byte `store`, fully expressible in the `memref` dialect and rendering
`movzbl` (load, scale 1) + `movb` (store, scale 1) in a real rolled back-edge.
The byte VALUES are checked against the LE spec `(v >> 8·i) & 0xff` via `denote`
(`byteSer_denote_leBytes`).

## The arithmetic-input wall (why Plonky3's register writer cannot re-point yet)

`Plonky3SerializeOwnedEmit.leByteBody` is hand-authored `Lcmd` whose value lives
in a **register** `%rdx` and is split by an in-body `SHR %rdx, 8` each trip
(`STORE:8 ; SHR:64 ; ADD ; SUB`). Re-pointing THAT through a byte `memref` loop
needs the byte split `(v >> 8·i) & 0xff` computed *inside* the loop body — a
shift + mask. The `memref` dialect has only `load`/`store` (no arithmetic op),
and the only front that has the arithmetic (`catCryptDialect` / LowCT `SExpr`)
has only the 64-bit `stackStore 64` array store. No single verified front emits
one `Com jasminDialect` loop body combining `catCryptDialect` arithmetic with a
byte `stackStore 8`. This combinator therefore re-points a register-input LE
writer only after an ABI change to pass the value by byte-address
(`inp = &v`); the register-shift writer stays hand-authored until either
`catCryptDialect` grows a byte store or a verified jasmin-level graft of
`catCryptDialect`-arithmetic + `memref`-byte-store is built. See the report.

Invoke (in-model gate; the correctness gate is the byte-copy `denote` check +
the external `.s` KAT):
  lake env lean CatCrypt/Crypto/SecureCompilation/Dialects/ByteMemrefRolledLoop.lean
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.ByteMemrefRolledLoop

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.Dialects.Memref
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (renderLprogAtt renderLfundef)

/-! ## 1. The combinator: a byte-cell rolled `ComL.forLoopN` -/

/-- Wrap a `memref`-dialect byte-loop *body* into a genuine rolled `ComL.forLoopN`.

    * `body` is a `memref` program over `[.buf 8 n, .int 64, *invBufs]` (byte
      accumulator buffer `.here`, loop index `.there .here`, invariant byte
      buffers in the tail) returning the updated `.buf 8 n`. Its byte `store`
      lowers to `stackStore 8` → `STOREIDX` scale-1 → `movb`; a byte `load`
      lowers to `stackLoad 8` → `LOADIDX` scale-1 → `movzbl`.
    * `init` is the in-scope accumulator seed (the output byte buffer base);
    * `invs` are the in-scope invariant seeds (input byte-buffer bases).

    `Memref.lowerMemrefToJasmin body` has jasmin type
    `Com jasminDialect (.stackArr 8 n :: .reg 64 :: invBufs.map MemrefTy.toJasmin)
    (.stackArr 8 n)` — exactly the `JLoopBodyN.update` shape — so this is a
    `ComL.forLoopN` over `accTy = .stackArr 8 n`, `invTys = invBufs.map
    MemrefTy.toJasmin`, binding and returning the loop result (`.ret .here`).
    **Total** (no `Option`): the `memref → jasmin` lowering is unconditional. -/
def byteRolledForLoopN {Γouter : Ctxt jasminDialect}
    {n : Nat} {invBufs : List MemrefTy}
    (N : Nat)
    (body : Com memrefDialect (.buf 8 n :: .int 64 :: invBufs) (.buf 8 n))
    (init : Ctxt.Var Γouter (.stackArr 8 n))
    (invs : HVector (fun ty => Ctxt.Var Γouter ty) (invBufs.map MemrefTy.toJasmin)) :
    ComL Γouter (.stackArr 8 n) :=
  ComL.forLoopN ⟨N, lowerMemrefToJasmin body⟩ init invs (.ret .here)

/-! ## 2. The little-endian `u64` serializer body — a byte copy `out[i] := inp[i]`

Body context `[.buf 8 n, .int 64, .buf 8 n]` = `[out (acc), idx, inp (inv)]`
(`out = .here`, `idx = .there .here`, `inp = .there (.there .here)`). One trip:
load byte `inp[idx]` (a `movzbl`), store it to `out[idx]` (a `movb`). -/

/-- The LE serializer byte-copy loop body: `b := inp[idx]; out[idx] := b`. Pure
    `memref` byte `load` + byte `store` — the byte path, no arithmetic op. -/
def leCopyBody (n : Nat) :
    Com memrefDialect [.buf 8 n, .int 64, .buf 8 n] (.buf 8 n) :=
  -- b := inp[idx]   (inp = .there (.there .here), idx = .there .here)
  .var (.mk (.load 8 n) rfl
         (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
    -- context is now [.int 8 (b), .buf 8 n (out), .int 64 (idx), .buf 8 n (inp)]
    -- out[idx] := b   (out = .there .here, idx = .there (.there .here), b = .here)
    (.var (.mk (.store 8 n) rfl
            (.cons (.there .here)
              (.cons (.there (.there .here)) (.cons .here .nil))))
      (.ret .here))

/-- The deployed LE-`u64` byte count. -/
def n8 : Nat := 8

/-- The outer (kernel-argument) jasmin context: `out : uint8_t[8]` (accumulator
    seed `.here`), `inp : uint8_t[8]` (invariant seed `.there .here`). 2-pointer
    SysV ABI `p3_ser_u64_le(out, inp)` → `[RDI, RSI]`. -/
abbrev Γser : Ctxt jasminDialect := [.stackArr 8 n8, .stackArr 8 n8]

/-- The front-sourced LE-`u64` serializer as a byte-granular rolled loop
    (`byteRolledForLoopN` over the byte-copy body, `N = 8`). -/
def byteSerComL : ComL Γser (.stackArr 8 n8) :=
  byteRolledForLoopN (Γouter := Γser) (n := n8) (invBufs := [.buf 8 n8])
    n8 (leCopyBody n8) .here (.cons (.there .here) .nil)

/-! ## 3. Provenance: the serializer IS the combinator output -/

/-- **Provenance (rfl).** `byteSerComL` is definitionally the byte combinator
    applied to the byte-copy body — the whole rolled loop is front-sourced
    through `byteRolledForLoopN`, no hand-built `ComL`/`Com jasminDialect`. -/
theorem byteSer_provenance :
    byteSerComL
      = byteRolledForLoopN (Γouter := Γser) (n := n8) (invBufs := [.buf 8 n8])
          n8 (leCopyBody n8) .here (.cons (.there .here) .nil) := rfl

/-- **The loop body is the lowered `memref` byte body (rfl).** The
    `JLoopBodyN.update` inside the rolled loop is exactly
    `Memref.lowerMemrefToJasmin (leCopyBody 8)` — the verified byte lowering,
    not a hand-built jasmin `Com`. -/
theorem byteSer_body_is_lowered_memref :
    byteSerComL
      = ComL.forLoopN ⟨n8, lowerMemrefToJasmin (leCopyBody n8)⟩
          (.here) (.cons (.there .here) .nil) (.ret .here) := rfl

/-! ## 4. The byte VALUES: `out[i] = (v >> 8·i) & 0xff` (the LE spec)

`JLoopBodyN.denote ⟨8, update⟩ invs init` is the 8-fold of the byte-copy body
over the trip index. With `inp = leBytes v` (byte `i` = `(v >> 8·i) & 0xff`) and
any initial `out`, the fold copies every byte, so the result equals `leBytes v`
byte-for-byte — the little-endian serialization of `v`. -/

/-- The little-endian byte view of a `u64`: `leBytes v i = (v >> 8·i) & 0xff`. -/
def leBytes (v : BitVec 64) : Fin n8 → BitVec 8 :=
  fun i => BitVec.ofNat 8 (v.toNat / 2 ^ (8 * i.val) % 256)

/-- The lowered byte-copy loop body (`JLoopBodyN.update`). -/
def serUpdate : Com jasminDialect (.stackArr 8 n8 :: .reg 64 :: [.stackArr 8 n8]) (.stackArr 8 n8) :=
  lowerMemrefToJasmin (leCopyBody n8)

/-- Byte equality of two 8-cell byte buffers as a decidable `Bool`. -/
def bufEqB8 (f g : Fin n8 → BitVec 8) : Bool :=
  (List.finRange n8).all (fun j => f j == g j)

/-- The `JLoopBodyN.denote` fold of the serializer body, seeded with the LE bytes
    of `v` as the input buffer and an arbitrary initial output buffer. -/
def serDenote (v : BitVec 64) (out0 : Fin n8 → BitVec 8) : Fin n8 → BitVec 8 :=
  JLoopBodyN.denote ⟨n8, serUpdate⟩ (.cons (leBytes v) .nil) out0

/-- **Byte values = LE spec.** The rolled byte-copy serializer produces exactly
    `(v >> 8·i) & 0xff` for every output byte `i`, on a representative `v` and a
    non-trivial initial output buffer (so the check exercises the copy, not a
    coincidence with `out0`). This is the little-endian `u64` serialization. -/
theorem byteSer_denote_leBytes :
    bufEqB8 (serDenote 0x0123456789ABCDEF (fun _ => 0xEE)) (leBytes 0x0123456789ABCDEF) = true := by
  native_decide

/-- A second `v` (all output cells start at a different sentinel). -/
theorem byteSer_denote_leBytes' :
    bufEqB8 (serDenote 0xFEDCBA9876543210 (fun j => BitVec.ofNat 8 (j.val + 1)))
      (leBytes 0xFEDCBA9876543210) = true := by
  native_decide

/-- **Round-trip:** the emitted bytes reassemble to `v` little-endian
    (`Σ out[i]·256^i = v`) — an independent confirmation that the byte order is
    LE, not just that each cell matches `leBytes`. -/
theorem byteSer_roundtrip :
    ((List.finRange n8).foldr
        (fun (i : Fin n8) (acc : Nat) => ((serDenote 0x0123456789ABCDEF (fun _ => 0)) i).toNat + 256 * acc) 0)
      = (0x0123456789ABCDEF : Nat) := by
  native_decide

/-! ## 5. The decisive check — the emitted store is `movb` / SIB scale 1

The physical rolled export renders the byte `stackStore 8` as a `STOREIDX` at SIB
scale 1 → `movb`, and the byte `stackLoad 8` as a `LOADIDX` scale 1 → `movzbl`.
This is the check the word-store trap fails: `isSome = true` is NOT enough — a
64-bit `stackStore 64` would render `movq` at scale 8 and clobber 7 neighbouring
byte cells. -/

/-- Substring test (mirrors `Plonky3SerializeOwnedEmit.hasSub`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- The owned AT&T `.s` for the front-sourced LE-`u64` serializer
    (`p3_ser_u64_le`, byte-granular rolled loop). -/
def byteSerAsm : String :=
  renderLprogAtt
    (ComL.toLprogPhysAbi byteSerComL "p3_ser_u64_le" (argName 0) [argName 1]
      (fun _ => none) (fun _ => none) ["RDI", "RSI"] [64, 64])

/-- **Byte store, not word store.** The emitted kernel contains a `movb` store
    at SIB scale 1 — the width-exact one-byte write — and does NOT contain the
    64-bit `movq` at scale 8 that the word (`.memref`/`stackStore 64`) path would
    give. THE decisive check (per the word-store trap: `isSome` is not enough). -/
theorem byteSer_store_is_movb :
    hasSub byteSerAsm "movb" = true := by native_decide

/-- The byte load renders `movzbl` (scale-1 zero-extending byte load). -/
theorem byteSer_load_is_movzbl :
    hasSub byteSerAsm "movzbl" = true := by native_decide

/-- The SIB scale of the indexed byte access is 1 (`uint8_t` stride), not 8: the
    store renders `movb %dl, (%r14, %rbx, 1)` and the load `movzbl (%r14, %rbx, 1),
    %edx` — SIB stride 1. A word store would render scale `, 8)`. -/
theorem byteSer_scale1 :
    hasSub byteSerAsm ", 1)" = true ∧ hasSub byteSerAsm ", 8)" = false := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- The emit is a genuine rolled loop: a real `jne` back-edge and a loop label. -/
theorem byteSer_has_backedge :
    hasSub byteSerAsm "jne" = true ∧ hasSub byteSerAsm ".L" = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- No unhandled op leaked into the emit. -/
theorem byteSer_no_unhandled :
    hasSub byteSerAsm "UNHANDLED" = false := by native_decide

/-! ## 6. Emit driver -/

/-- Write the front-sourced byte-granular LE-`u64` serializer `.s`. -/
def writeEmit (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path byteSerAsm

end CatCrypt.Crypto.SecureCompilation.Dialects.ByteMemrefRolledLoop
