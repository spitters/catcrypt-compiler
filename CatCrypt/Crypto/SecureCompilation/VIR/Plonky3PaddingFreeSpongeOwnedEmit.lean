/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter

/-!
# Plonky3 `PaddingFreeSponge<16,8,8>` hash as owned `Lcmd` (no jasminc)

The Plonky3 Merkle leaf hash `MyHash = PaddingFreeSponge<Perm, 16, 8, 8>` absorbs
a 16-element BabyBear input as two rate-8 blocks over the Poseidon2-BabyBear
width-16 permutation, then squeezes the rate-8 digest. The **round arithmetic**
is the Poseidon2 permute, which is an emitted OWNED leaf
(`bench/poseidon2_compare/gen_com/poseidon2_bb_owned.s`, symbol `poseidon2_bb`,
KAT-matched against the upstream Plonky3 `PaddingFreeSponge<16,8,8>` digest and
the `test_default_babybear_poseidon2_width_16` vector). What remains is the
**sponge buffer movement** — the rate-overwrite absorb of each block and the
rate squeeze — which is pure word moves, no field op.

This module emits that sponge body as owned-backend `Lcmd` through the verified
linear printer (`renderLprogAtt`), in place of the jasminc `p2_hash_kat.s`. The
two exported symbols match the `p2_hash_kat.c` harness:

* `p2_perm16(out, in)` — the permutation alone (a thin `call poseidon2_bb`, the
  identical `(out:RDI, in:RSI)` pointer ABI);
* `p2_sponge16(out, in)` — the `PaddingFreeSponge<16,8,8>` hash, exactly
  mirroring `p2_hash_kat_link.jazz::p2_sponge16`:

  ```
  st[0..8] = in[0..8];  st[8..16] = 0       # block 0: overwrite rate
  st = perm(st)
  st[0..8] = in[8..16]                       # block 1: overwrite rate (keep capacity)
  st = perm(st)
  out[0..8] = st[0..8]                       # squeeze the rate
  ```

The two permute applications are `call poseidon2_bb` to the emitted owned leaf;
the rate/capacity buffer marshalling is owned `LOAD`/`STORE` word moves into a
frame-local 16-word state buffer and a 16-word permute-output buffer. There is
**no field op** in this body — the round arithmetic is the called permute leaf.

## Frame / ABI

`p2_sponge16(out:RDI, in:RSI)`. The input pointer is parked in the single
callee-saved `%rbx` (it must survive both `call poseidon2_bb`s, since block 1
reads `in[8..16]`); the output pointer is parked in a frame slot (reloaded after
the last permute). Parking exactly ONE callee-saved register makes the printer
emit ONE `pushq %rbx`, which (with the 16-aligned `leaq -F`) leaves `%rsp`
16-aligned at each `call` — the SysV pre-call alignment. Frame layout:

| region   | words | byte offset |
|----------|-------|-------------|
| `st[16]` | 16    | `0`         |
| `po[16]` | 16    | `128`       |
| `out-ptr`| 1     | `256`       |

The state buffer at `[%rsp+0]` and permute-output buffer at `[%rsp+128]` are the
permute leaf's `(out, in)` pointers (`leaq`'d into `%rdi`/`%rsi` before each
call); they sit in the owned frame, below the caller's frame, so the permute's
own frame never aliases them.

## What is verified vs trusted

* **Verified (leaf)**: the Poseidon2 permute is the emitted owned `poseidon2_bb`
  leaf (`Poseidon2.ScalarOwnedEmit`, rendered from the leaf-free field `Com`).
* **Verified (printer)**: the shape lemmas below pin that the emitted `.s`
  carries both export labels, issues two `call poseidon2_bb`, moves words
  (`LOAD`/`STORE`), and contains no `# UNHANDLED-OP`.
* **Trusted (thin)**: `renderLfundef` / the SysV leaf ABI frame + the sponge
  buffer-marshalling transcription of `p2_hash_kat_link.jazz::p2_sponge16`.

The byte-identity gate is the external `cc` KAT (`p2_hash_kat.c`): the digest
`p2_sponge16` produces over the canonical 16-word vector must equal the upstream
`PLONKY3_HASH_KAT`, with the owned `.s` (this module) + the owned permute `.s`
linked, no jasminc.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3PaddingFreeSpongeOwnedEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (renderLfundef renderLprogAtt)

/-! ## 0. Substring helper -/

/-- Substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- Count of non-overlapping occurrences of `needle` in `hay` (used to pin the
    exact two `call poseidon2_bb`). -/
def countSub (hay needle : String) : Nat :=
  (List.range (hay.length + 1)).countP (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-! ## 1. Owned `Lcmd` building blocks -/

/-- A base-pointer-relative memory operand `mem.<base>.<off>`. -/
def memOp (base : String) (off : Nat) : LOperand :=
  .reg ("mem." ++ base ++ "." ++ toString off)

/-- `n` consecutive u64 word copies `dst[k] ← src[k]` (`k = 0..n-1`), each a
    `LOAD` into `%rax` and a `STORE` back, at the given base + first-word offsets
    (8-byte stride). The scratch `%rax` is caller-saved; it is reloaded each
    word, so an interleaved `call` (which clobbers `%rax`) is harmless. -/
def copyWords (srcBase : String) (srcOff0 : Nat) (dstBase : String)
    (dstOff0 : Nat) (n : Nat) : Lcmd :=
  (List.range n).flatMap (fun k =>
    [ ⟨0, .Lopn [.reg "RAX"] "LOAD:64" [memOp srcBase (srcOff0 + 8 * k)]⟩
    , ⟨0, .Lopn [memOp dstBase (dstOff0 + 8 * k)] "STORE:64" [.reg "RAX"]⟩ ])

/-- `n` consecutive u64 zero-stores `dst[k] ← 0` (`k = 0..n-1`). `%rax` is set to
    `0` once, then stored `n` times. -/
def zeroWords (dstBase : String) (dstOff0 : Nat) (n : Nat) : Lcmd :=
  ⟨0, .Lopn [.reg "RAX"] "MOV:64" [.imm 0]⟩ ::
  (List.range n).map (fun k =>
    ⟨0, .Lopn [memOp dstBase (dstOff0 + 8 * k)] "STORE:64" [.reg "RAX"]⟩)

/-! ## 2. Frame offsets -/

/-- State buffer (16 words) base offset. -/
def stOff : Nat := 0
/-- Permute-output buffer (16 words) base offset. -/
def poOff : Nat := 128
/-- Output-pointer save slot. -/
def outPtrOff : Nat := 256
/-- The frame size (state 128 + permute-output 128 + out-ptr slot 8, 16-aligned). -/
def spongeFrame : Nat := 272

/-- The emitted owned permute leaf symbol (the KAT-matched scalar Poseidon2
    permute, `bench/poseidon2_compare/gen_com/poseidon2_bb_owned.s`). -/
def permSym : String := "poseidon2_bb"

/-! ## 3. `p2_perm16` — the permutation alone

`p2_perm16(out:RDI, in:RSI)` is the bare permute under the harness symbol: the
`(out, in)` pointer ABI is exactly `poseidon2_bb`'s, so the body forwards the
already-in-place argument registers with a single `call poseidon2_bb`. -/

def perm16Body : Lcmd :=
  -- An (inert) bare write of the callee-saved RBX makes the printer bracket the
  -- body with one `pushq %rbx`; together with the 16-aligned `leaq -F` this puts
  -- `%rsp` at the SysV 16-byte pre-call alignment for the `call poseidon2_bb`
  -- (`movq %rbx, %rbx` is a no-op; RBX is preserved by the push/pop). The `(out,
  -- in)` argument registers pass straight through to the permute leaf.
  [ ⟨0, .Lopn [.reg "RBX"] "MOV:64" [.reg "RBX"]⟩
  , ⟨0, .Lcall none (permSym, 0)⟩ ]

def perm16Fundef : Lfundef :=
  { lfd_tyin := [64, 64], lfd_arg := ["RDI", "RSI"]
    lfd_body := perm16Body
    lfd_tyout := [], lfd_res := [] }

/-! ## 4. `p2_sponge16` — `PaddingFreeSponge<16,8,8>` as an owned `ComL`

`p2_sponge16` is expressed as a straight-line `ComL` over three array roles — a
frame-local 16-word `state` and the two caller pointers `input` (RSI) and
`digest` (RDI) — and lowered to the SysV `.s` through the verified front node
`ComL.toLfundefPhysFramedAbi` (§7g‴ of `JasminLprogExport`). The permute leaf is
an in-place array `extCall poseidon2_bb(state)` (`out == in`; the leaf reads all
16 input words before writing any output, so aliasing is safe). No hand-authored
`Lcmd`/`Lcall` — the absorb/squeeze word moves and the three pointer calls are
GENERATED from this `ComL` by the front's direct offset-folding lowering.

The context is `Γ = [digest, input, state]`, which the front's `resolveVar`
convention names `a2 = digest`, `a1 = input`, `a0 = state`. -/

/-- A width-16 BabyBear stack array (a 16-word frame/pointer buffer). -/
abbrev SA : JasminTy := JasminTy.stackArr 64 16
/-- A 64-bit register value (an index or a moved word). -/
abbrev R64 : JasminTy := JasminTy.reg 64

/-- Absorb one word: `dst := state`, `src := input`, `state[dstI] := input[srcI]`.
    Pushes `idxSrc, w, idxDst, state'` (4 binders); the continuation receives the
    three array roles weakened past them. -/
def bAbsorb {Γ : Ctxt jasminDialect} {s : JasminTy}
    (st inp dg : Ctxt.Var Γ SA) (dstI srcI : Nat)
    (k : Ctxt.Var (SA :: R64 :: R64 :: R64 :: Γ) SA →
         Ctxt.Var (SA :: R64 :: R64 :: R64 :: Γ) SA →
         Ctxt.Var (SA :: R64 :: R64 :: R64 :: Γ) SA →
         ComL (SA :: R64 :: R64 :: R64 :: Γ) s) : ComL Γ s :=
  .var (.mk (.regConst 64 srcI) rfl .nil)
  (.var (.mk (.stackLoad 64 16) rfl (.cons (.there inp) (.cons .here .nil)))
  (.var (.mk (.regConst 64 dstI) rfl .nil)
  (.var (.mk (.stackStore 64 16) rfl
      (.cons (.there (.there (.there st))) (.cons .here (.cons (.there .here) .nil))))
  (k (.there (.there (.there (.there st))))
     (.there (.there (.there (.there inp))))
     (.there (.there (.there (.there dg))))))))

/-- Zero one capacity word `state[dstI] := 0`. Pushes `idx, z, state'`. -/
def bZero {Γ : Ctxt jasminDialect} {s : JasminTy}
    (st inp dg : Ctxt.Var Γ SA) (dstI : Nat)
    (k : Ctxt.Var (SA :: R64 :: R64 :: Γ) SA →
         Ctxt.Var (SA :: R64 :: R64 :: Γ) SA →
         Ctxt.Var (SA :: R64 :: R64 :: Γ) SA →
         ComL (SA :: R64 :: R64 :: Γ) s) : ComL Γ s :=
  .var (.mk (.regConst 64 dstI) rfl .nil)
  (.var (.mk (.regConst 64 0) rfl .nil)
  (.var (.mk (.stackStore 64 16) rfl
      (.cons (.there (.there st)) (.cons (.there .here) (.cons .here .nil))))
  (k (.there (.there (.there st)))
     (.there (.there (.there inp)))
     (.there (.there (.there dg))))))

/-- Squeeze one word `digest[i] := state[i]`. Pushes `idx, w, digest'`. -/
def bSqueeze {Γ : Ctxt jasminDialect} {s : JasminTy}
    (st inp dg : Ctxt.Var Γ SA) (i : Nat)
    (k : Ctxt.Var (SA :: R64 :: R64 :: Γ) SA →
         Ctxt.Var (SA :: R64 :: R64 :: Γ) SA →
         Ctxt.Var (SA :: R64 :: R64 :: Γ) SA →
         ComL (SA :: R64 :: R64 :: Γ) s) : ComL Γ s :=
  .var (.mk (.regConst 64 i) rfl .nil)
  (.var (.mk (.stackLoad 64 16) rfl (.cons (.there st) (.cons .here .nil)))
  (.var (.mk (.stackStore 64 16) rfl
      (.cons (.there (.there dg)) (.cons (.there .here) (.cons .here .nil))))
  (k (.there (.there (.there st)))
     (.there (.there (.there inp)))
     (.there (.there (.there dg))))))

/-- The in-place permute leaf `state := poseidon2_bb(state)` (`out == in`).
    Pushes one binder (the permuted-array result); the continuation keeps the
    fixed-base array roles weakened past it. -/
def bPerm {Γ : Ctxt jasminDialect} {s : JasminTy}
    (st inp dg : Ctxt.Var Γ SA)
    (k : Ctxt.Var (SA :: Γ) SA → Ctxt.Var (SA :: Γ) SA → Ctxt.Var (SA :: Γ) SA →
         ComL (SA :: Γ) s) : ComL Γ s :=
  .var (.mk (.extCall "poseidon2_bb" [SA] SA) rfl (.cons st .nil))
  (k (.there st) (.there inp) (.there dg))

/-- **`p2_sponge16` as a `ComL`.** `Γ = [digest, input, state]`. Absorb block 0
    (`state[0..8] := input[0..8]`, `state[8..16] := 0`), permute, absorb block 1
    (`state[0..8] := input[8..16]`, capacity kept in place), permute, squeeze
    (`digest[0..8] := state[0..8]`). -/
def spongeComL : ComL [SA, SA, SA] SA :=
  bAbsorb (.there (.there .here)) (.there .here) .here 0 0 <| fun st inp dg =>
  bAbsorb st inp dg 1 1 <| fun st inp dg =>
  bAbsorb st inp dg 2 2 <| fun st inp dg =>
  bAbsorb st inp dg 3 3 <| fun st inp dg =>
  bAbsorb st inp dg 4 4 <| fun st inp dg =>
  bAbsorb st inp dg 5 5 <| fun st inp dg =>
  bAbsorb st inp dg 6 6 <| fun st inp dg =>
  bAbsorb st inp dg 7 7 <| fun st inp dg =>
  bZero st inp dg 8 <| fun st inp dg =>
  bZero st inp dg 9 <| fun st inp dg =>
  bZero st inp dg 10 <| fun st inp dg =>
  bZero st inp dg 11 <| fun st inp dg =>
  bZero st inp dg 12 <| fun st inp dg =>
  bZero st inp dg 13 <| fun st inp dg =>
  bZero st inp dg 14 <| fun st inp dg =>
  bZero st inp dg 15 <| fun st inp dg =>
  bPerm st inp dg <| fun st inp dg =>
  bAbsorb st inp dg 0 8 <| fun st inp dg =>
  bAbsorb st inp dg 1 9 <| fun st inp dg =>
  bAbsorb st inp dg 2 10 <| fun st inp dg =>
  bAbsorb st inp dg 3 11 <| fun st inp dg =>
  bAbsorb st inp dg 4 12 <| fun st inp dg =>
  bAbsorb st inp dg 5 13 <| fun st inp dg =>
  bAbsorb st inp dg 6 14 <| fun st inp dg =>
  bAbsorb st inp dg 7 15 <| fun st inp dg =>
  bPerm st inp dg <| fun st inp dg =>
  bSqueeze st inp dg 0 <| fun st inp dg =>
  bSqueeze st inp dg 1 <| fun st inp dg =>
  bSqueeze st inp dg 2 <| fun st inp dg =>
  bSqueeze st inp dg 3 <| fun st inp dg =>
  bSqueeze st inp dg 4 <| fun st inp dg =>
  bSqueeze st inp dg 5 <| fun st inp dg =>
  bSqueeze st inp dg 6 <| fun st inp dg =>
  bSqueeze st inp dg 7 <| fun st _ _ =>
  .ret st

/-- The framed + caller-pointer ABI export of `p2_sponge16` (§7g‴). `state` is a
    16-word (128-byte) self-owned frame array at offset `0`; `input` (RSI) is
    parked in callee-saved `RBX` (survives both permute calls); `digest` (RDI) is
    parked in the frame slot at `128` and reloaded at the squeeze. The frame is
    144 bytes (128 state + 8 digest slot + 8 pad; with the forced `push %rbx`,
    `%rsp` is 16-aligned at each `call`). -/
def spongeFundef : Lfundef :=
  ComL.toLfundefPhysFramedAbi 144
    [("a0", 0)]              -- state: frame-local at offset 0
    [("a1", "RBX", "RSI")]   -- input: parked in RBX from RSI
    [("a2", 128, "RDI")]     -- digest: parked in frame slot 128 from RDI
    spongeComL

/-! ## 5. The composed sponge `Lprog` (one `.s`) -/

def spongeFuncs : List (String × Lfundef) :=
  [ ("p2_perm16", perm16Fundef), ("p2_sponge16", spongeFundef) ]

def spongeLprog : Lprog := { lp_funcs := spongeFuncs }

def spongeAsm : String := renderLprogAtt spongeLprog

/-! ## 6. Shape lemmas -/

theorem sponge_has_perm16 : hasSub spongeAsm "p2_perm16" = true := by native_decide
theorem sponge_has_sponge16 : hasSub spongeAsm "p2_sponge16" = true := by native_decide

/-- The composed object issues exactly the three `call poseidon2_bb` of the
    harness (one in `p2_perm16`, two in `p2_sponge16`'s two-block absorb). -/
theorem sponge_calls_perm_thrice :
    countSub spongeAsm "call poseidon2_bb" = 3 := by native_decide

/-- The sponge body moves words (the rate/capacity absorb + squeeze buffer
    marshalling): a word load and a word store. -/
theorem sponge_moves_words :
    hasSub spongeAsm "(%rsp), %rax" = true
      ∧ hasSub spongeAsm "%rax, " = true := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- No unhandled op in the emitted `.s` (every `Lopn`/`Lcall` rendered). -/
theorem sponge_no_unhandled : hasSub spongeAsm "UNHANDLED" = false := by native_decide

/-- **Owned `PaddingFreeSponge<16,8,8>`.** The one composed `.s` carries both
    harness symbols, the absorb/squeeze as owned `LOAD`/`STORE` word moves around
    `call poseidon2_bb` to the emitted owned permute leaf, with no unhandled op
    and no field op (the round arithmetic is the called permute). -/
theorem sponge_shape :
    hasSub spongeAsm "p2_perm16" = true
      ∧ hasSub spongeAsm "p2_sponge16" = true
      ∧ countSub spongeAsm "call poseidon2_bb" = 3
      ∧ hasSub spongeAsm "UNHANDLED" = false :=
  ⟨sponge_has_perm16, sponge_has_sponge16, sponge_calls_perm_thrice, sponge_no_unhandled⟩

theorem sponge_funcs_eq : spongeLprog.lp_funcs = spongeFuncs := rfl

/-! ## 7. Emit driver -/

def emitMain : IO Unit := do
  let dir := "bench/plonky3_compare/gen_com"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/p2_sponge_owned.s") spongeAsm
  IO.println "WROTE bench/plonky3_compare/gen_com/p2_sponge_owned.s"
  IO.println "  ONE .s: p2_perm16 + p2_sponge16 (PaddingFreeSponge<16,8,8>)"
  IO.println "  absorb/squeeze owned LOAD/STORE word moves + call poseidon2_bb (emitted owned permute leaf), NO jasminc"

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3PaddingFreeSpongeOwnedEmit

/-- Top-level entry point (`lake env lean --run` / `lake exe plonky3sponge`). -/
def main : IO UInt32 := do
  CatCrypt.Crypto.SecureCompilation.VIR.Plonky3PaddingFreeSpongeOwnedEmit.emitMain
  return 0
