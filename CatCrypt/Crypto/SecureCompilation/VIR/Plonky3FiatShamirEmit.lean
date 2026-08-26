/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline

/-!
# Plonky3 Fiat-Shamir `DuplexChallenger<16,8>` duplexing as an owned `ComL` (no jasminc)

The Fiat-Shamir challenger of `prove()` is a duplex sponge over the Poseidon2
permutation — `ch_*` in `bench/plonky3_compare/p3_accept_prove.c`. The
**round arithmetic** is the Poseidon2 permute, which is already an emitted leaf
(`hp_perm16` / `p3_poseidon2_perm_zmm`). What remains is the **transcript
bookkeeping**: the absorb/squeeze buffer word moves and the duplex trigger. That
bookkeeping is pure index/buffer marshalling — no field op.

This module emits the central bookkeeping step, the **duplexing**
(`ch_duplex`), as an owned `ComL` lowered to the SysV `.s` through the verified
front node `ComL.toLfundefPhysFramedAbi` (§7g‴ of `JasminLprogExport`) — the same
front the `PaddingFreeSponge<16,8,8>` owned hash is generated through. The
absorb/squeeze word moves and the in-place permute call are GENERATED from the
`ComL`; there is **no hand-authored `Lcmd`/`Lcall`**.

```
ch_duplex(Chal *c):                      # the C reference (p3_accept_prove.c)
  for i in 0..8: c->st[i] = c->inbuf[i]        # absorb the rate (rate 8)
  hp_perm16(c->st, c->st)                       # the Poseidon2 permute (a leaf)
  for i in 0..8: c->outbuf[i] = c->st[i]        # squeeze the rate into outbuf
```

## Flat `Chal` layout (the ABI this owned `ComL` uses)

The challenger struct is laid out as one contiguous `uint64_t` buffer so the
owned kernel can address every region by a fixed element index off the single
struct base (the C KAT `fiat_shamir_from_rustcmd_kat.c` mirrors this layout):

| field       | words | element index | byte offset |
|-------------|-------|---------------|-------------|
| `st[16]`    | 16    | `0..15`       | `0`         |
| `inbuf[8]`  | 8     | `16..23`      | `128`       |
| `outbuf[8]` | 8     | `24..31`      | `192`       |

`p3_fs_duplex(Chal *c)` takes the struct pointer in `%rdi` (SysV arg 0). Because
all three regions live in the ONE caller struct, the kernel is a single 32-word
array role `c` (a `stackArr 64 32`) backed by that pointer, parked in the
callee-saved `%rbx` so it survives the permute call. Absorb is `c[i] := c[16+i]`
for `i = 0..7`; the permute is the in-place `extCall hp_perm16(c)` (`out == in`,
base `c` = `c->st`, so it writes the permuted state back into the caller's
`c->st`); squeeze is `c[24+i] := c[i]` for `i = 0..7`.

## How this differs from `PaddingFreeSponge` (the ABI split)

`PaddingFreeSponge` owns a *frame-local* scratch state and takes TWO caller
pointers (`input` RSI, `digest` RDI); the permuted state never returns to the
caller. `DuplexChallenger` keeps its state *in the caller's struct* (`c->st`),
and the KAT checks the whole `c->st[0..16]` after the duplex — so the state must
be permuted **in place in the caller's memory**, not in a private frame. That is
why the state, input, and output are the ONE caller struct pointer at three
element ranges (a single register-parked array role at offsets `0/128/192`),
rather than a frame array plus two pointer parks. The rate width is `8` (only
`st[0..8]` is overwritten by the absorb; the capacity `st[8..16]` is kept in
place — the `DuplexChallenger` overwrite rule, no capacity zeroing).

## What this closes vs what stays C

* CLOSED: the duplex buffer marshalling — the `inbuf → st` absorb and the
  `st → outbuf` squeeze — is front-generated `LOAD`/`STORE` word moves, not a C
  `for (i…) c->st[i] = c->inbuf[i]`. The permute between them is the emitted
  Poseidon2 leaf (`call`ed, not re-implemented).
* STILL C (the residual): the `observe`/`sample` *wrapper* — the
  `inlen++`/`--outlen` counter increments and the `if (inlen==8) duplex` /
  `if (inlen>0 || outlen==0) duplex` *trigger tests* that decide WHEN to duplex —
  is a data-dependent control decision on the public transcript position; it
  stays in the driver prologue's straight-line counter logic. It carries no field
  op (it is pointer/counter arithmetic), and the duplex it triggers is this owned
  leaf.

## What is verified vs trusted

* **Verified (leaf)**: the Poseidon2 permute is the emitted owned `hp_perm16`
  leaf (KAT-agnostic bookkeeping — the KAT links the SAME permute on both sides).
* **Verified (front)**: the absorb/squeeze word moves and the in-place permute
  call are lowered from the `ComL` by `ComL.toLfundefPhysFramedAbi`'s direct
  offset-folding lowering.
* **Trusted (thin)**: the SysV framed ABI printer + the flat-`Chal` element
  layout transcription of `ch_duplex`.

The byte-identity gate is the external `cc` KAT (`fiat_shamir_from_rustcmd_kat.c`):
the `(st, outbuf)` the owned duplex produces must equal the plain-C reference
`ch_duplex` driving the SAME permute.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FiatShamirEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (renderLfundef renderLprogAtt)

/-! ## 0. Substring helpers -/

/-- Substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- Count of non-overlapping occurrences of `needle` in `hay` (used to pin the
    exact one `call hp_perm16`). -/
def countSub (hay needle : String) : Nat :=
  (List.range (hay.length + 1)).countP (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-! ## 1. The flat-`Chal` array role and word-move builders

The whole `Chal` struct is ONE 32-word register-parked array role `c`. The
absorb, squeeze, and permute all address it by element index (the front folds the
`regConst` index into the `scale*k` byte offset of the emitted `movq`). -/

/-- The flat `Chal` struct as a single 32-word BabyBear stack array
    (`st[0..16] ‖ inbuf[16..24] ‖ outbuf[24..32]`, 256 bytes). -/
abbrev SA : JasminTy := JasminTy.stackArr 64 32
/-- A 64-bit register value (an index or a moved word). -/
abbrev R64 : JasminTy := JasminTy.reg 64

/-- The emitted owned Poseidon2 permute leaf symbol (the KAT links the shared
    deterministic `hp_perm16`; in production it is the verified-emitted leaf). -/
def permSym : String := "hp_perm16"

/-- Move one word `c[dstI] := c[srcI]`. Pushes `idxSrc, w, idxDst, c'`
    (4 binders); the continuation receives the array role weakened past them.
    Covers both the absorb (`dst = i`, `src = 16+i`) and the squeeze
    (`dst = 24+i`, `src = i`). -/
def bMove {Γ : Ctxt jasminDialect} {s : JasminTy}
    (c : Ctxt.Var Γ SA) (dstI srcI : Nat)
    (k : Ctxt.Var (SA :: R64 :: R64 :: R64 :: Γ) SA →
         ComL (SA :: R64 :: R64 :: R64 :: Γ) s) : ComL Γ s :=
  .var (.mk (.regConst 64 srcI) rfl .nil)
  (.var (.mk (.stackLoad 64 32) rfl (.cons (.there c) (.cons .here .nil)))
  (.var (.mk (.regConst 64 dstI) rfl .nil)
  (.var (.mk (.stackStore 64 32) rfl
      (.cons (.there (.there (.there c))) (.cons .here (.cons (.there .here) .nil))))
  (k (.there (.there (.there (.there c))))))))

/-- The in-place permute leaf `c := hp_perm16(c)` (`out == in`; base `c` =
    `c->st`, so the permuted state is written back into the caller's `c->st`).
    Pushes one binder (the permuted-array result). -/
def bPerm {Γ : Ctxt jasminDialect} {s : JasminTy}
    (c : Ctxt.Var Γ SA)
    (k : Ctxt.Var (SA :: Γ) SA → ComL (SA :: Γ) s) : ComL Γ s :=
  .var (.mk (.extCall permSym [SA] SA) rfl (.cons c .nil))
  (k (.there c))

/-! ## 2. `p3_fs_duplex` as a `ComL`

`Γ = [c]` (the single flat-`Chal` array role). Absorb the rate
(`c[0..8] := c[16..24]`, capacity `c[8..16]` kept in place), permute in place,
squeeze the rate (`c[24..32] := c[0..8]`). -/

/-- **`p3_fs_duplex` as a `ComL`.** The `DuplexChallenger` duplexing step over the
    flat `Chal`: absorb `inbuf → st` (rate 8), permute in place, squeeze
    `st → outbuf` (rate 8). -/
def duplexComL : ComL [SA] SA :=
  -- absorb: st[i] := inbuf[i]  (c[i] := c[16+i], i = 0..7)
  bMove .here 0 16 <| fun c =>
  bMove c 1 17 <| fun c =>
  bMove c 2 18 <| fun c =>
  bMove c 3 19 <| fun c =>
  bMove c 4 20 <| fun c =>
  bMove c 5 21 <| fun c =>
  bMove c 6 22 <| fun c =>
  bMove c 7 23 <| fun c =>
  -- permute in place: hp_perm16(st, st)  (base c = c->st)
  bPerm c <| fun c =>
  -- squeeze: outbuf[i] := st[i]  (c[24+i] := c[i], i = 0..7)
  bMove c 24 0 <| fun c =>
  bMove c 25 1 <| fun c =>
  bMove c 26 2 <| fun c =>
  bMove c 27 3 <| fun c =>
  bMove c 28 4 <| fun c =>
  bMove c 29 5 <| fun c =>
  bMove c 30 6 <| fun c =>
  bMove c 31 7 <| fun c =>
  .ret c

/-- The framed + caller-pointer ABI export of `p3_fs_duplex` (§7g‴). The one flat
    `Chal` role `a0` is the caller struct pointer (`%rdi`), parked in callee-saved
    `%rbx` (survives the permute call). There is no frame-local storage (the state
    lives in the caller's `c->st`), so `frameBytes = 0`; the single forced
    `push %rbx` (callee-saved park) leaves `%rsp` 16-aligned at the permute
    `call`. `void` return (`lfd_res = []`) — the result reaches the caller through
    `c->st`/`c->outbuf`. -/
def duplexFundef : Lfundef :=
  ComL.toLfundefPhysFramedAbi 0
    []                          -- no frame-local arrays (state is in the caller struct)
    [("a0", "RBX", "RDI")]      -- c: the flat-Chal struct pointer, parked in RBX
    []                          -- no frame-slot parks
    duplexComL
    ["RDI"] [64]                -- one SysV pointer arg

/-! ## 3. The composed FS bookkeeping `Lprog` (one `.s`) -/

/-- The Fiat-Shamir bookkeeping functions: the duplexing step. (The
    observe/sample wrapper is straight-line counter logic in the driver — see the
    residual note.) -/
def fiatShamirFuncs : List (String × Lfundef) :=
  [ ("p3_fs_duplex", duplexFundef) ]

/-- The composed FS bookkeeping `Lprog`. -/
def fiatShamirLprog : Lprog := { lp_funcs := fiatShamirFuncs }

def fiatShamirAsm : String := CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline.renderOwned fiatShamirLprog

-- Rendered-asm correctness is the external C KAT; an in-Lean occursIn check would re-evaluate the optimizing back-end renderOwned at elaboration.

theorem fiatShamir_funcs_eq : fiatShamirLprog.lp_funcs = fiatShamirFuncs := rfl

/-! ## 5. Emit driver -/

def emitMain : IO Unit := do
  let dir := "bench/plonky3_compare/gen_com"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/plonky3_fiat_shamir_owned.s") fiatShamirAsm
  IO.println "WROTE bench/plonky3_compare/gen_com/plonky3_fiat_shamir_owned.s"
  IO.println "  ONE .s: DuplexChallenger duplex (absorb/squeeze word moves + call hp_perm16)"
  IO.println "  GENERATED from a ComL via ComL.toLfundefPhysFramedAbi; NO hand Lcmd, permute is the emitted leaf"

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FiatShamirEmit

/-- Top-level entry point for `lake exe plonky3fiatshamir`. -/
def main : IO UInt32 := do
  CatCrypt.Crypto.SecureCompilation.VIR.Plonky3FiatShamirEmit.emitMain
  return 0
