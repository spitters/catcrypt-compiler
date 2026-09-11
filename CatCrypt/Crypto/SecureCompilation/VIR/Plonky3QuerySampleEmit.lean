/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.VIR.QuerySampleBranchFront
public import CatCrypt.Crypto.SecureCompilation.VIR.QuerySampleBranchFront

/-!
# Plonky3 FRI query-index sampler (`sample_bits(5)`) as owned control flow (FULL_PROVER_VS_P3 Gap 2 item 2)

The gap-2 Fiat-Shamir work (`Plonky3FiatShamirEmit.lean`) emitted the
duplex **bookkeeping** — the absorb/squeeze buffer marshalling around the
Poseidon2 permute leaf — as owned `loopLcmd` word-move control flow
(`p3_fs_duplex`). What it left as straight-line C is the `observe`/`sample`
**wrapper**: the data-dependent counter logic in `bench/plonky3_compare/p3_accept_prove.c`
(`DuplexChallenger<16,8>`) that decides WHEN to duplex and extracts the query
index.

This module emits that wrapper as owned control flow:

```
ch_observe(Chal *c, uint64_t v):           # the C reference (p3_accept_prove.c)
  c->outlen = 0;
  c->inbuf[c->inlen++] = v % P;            # (v already field-reduced; bookkeeping store)
  if (c->inlen == 8) ch_duplex(c);         #   inlen reset to 0 by the duplex

ch_sample(Chal *c) -> uint64_t:
  if (c->inlen > 0 || c->outlen == 0) ch_duplex(c);   # inlen→0, outlen→8 on duplex
  return c->outbuf[--c->outlen];

ch_sample_bits5(Chal *c) -> uint64_t:
  return ch_sample(c) & 31;                # the 5-bit FRI query index
```

The counters (`inlen`/`outlen`) are addressed in the flat-`Chal` struct (held in
a callee-saved register across the `call`); the `if (==8)` / `if (>0 || ==0)`
trigger tests are owned `CMP`/`Lcond` forward conditionals (`LprogControlFlow`),
the `& 31` mask is an owned `regArith .and` (`AND:64`), and the duplex on the
trigger is a `call` to the emitted duplex from `Plonky3FiatShamirEmit`
(`p3_fs_duplex` for the full-absorb `inlen==8` case; a partial-absorb sibling
`p3_fs_duplex_n`, emitted here, for the `0 < inlen < 8` sample-path case). This
is index/counter/mask logic — **no field op** anywhere (the round arithmetic is
the called permute leaf inside the duplex).

## Flat `Chal` layout (the ABI this owned `Lcmd` uses)

Extends the gap-1 flat-`Chal` layout with the two `int` counters as `u64` words:

| field      | words | byte offset |
|------------|-------|-------------|
| `st[16]`   | 16    | `0`         |
| `inbuf[8]` | 8     | `128`       |
| `outbuf[8]`| 8     | `192`       |
| `inlen`    | 1     | `256`       |
| `outlen`   | 1     | `264`       |

## Partial absorb (the sample-path subtlety)

`p3_fs_duplex` (gap-1) absorbs all 8 inbuf words (the `inlen==8` observe-trigger
case, where the inbuf is exactly full). The C `ch_sample` triggers a duplex on
`inlen > 0`, where `inlen` may be `1..7` (a partial buffer); the C `ch_duplex`
then copies only `inlen` words (`for i < inlen`). So the sample path needs a
**counter-driven** absorb. `p3_fs_duplex_n` emits exactly that: the absorb is a
`loopLcmd` whose trip count is `inlen` (loaded from the struct), the squeeze is
the fixed 8-word copy, the permute is the same `call hp_perm16` leaf. The observe
path keeps the `inlen==8` full-absorb `p3_fs_duplex` (where 8-word copy = inlen
copy, so they agree). Both duplexes call the byte-identical emitted permute leaf,
so the whole wrapper is byte-identical to the C `ch_observe`/`ch_sample` over the
same permute.

## What this closes vs what stays C

* CLOSED: the `observe`/`sample`/`sample_bits` wrapper — the `inlen`/`outlen`
  counter loads/increments/decrements, the `if (==8)` / `if (>0 || ==0)` trigger
  tests as owned `CMP`/`Lcond` forward branches, the `& 31` mask as owned
  `AND:64`, and the partial-absorb duplex (`p3_fs_duplex_n`) — is owned control
  flow, not hand-written C. The full-absorb trigger calls the gap-1
  `p3_fs_duplex`.
* STILL C (residual): nothing of the counter/mask wrapper. The `% P`
  field-canonicalization of an observed value (`inbuf[inlen] = v % P`) is NOT
  emitted here — transcript values reaching `observe` are already field elements
  `< P` (the prover produces reduced openings), so the owned store is a straight
  word store of the already-reduced `v`; the `% P` is a field reduction (a field
  op), deliberately excluded from this index/counter/mask leaf and left to the
  value producer. The KAT feeds already-reduced values so the store is exact.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Plonky3QuerySampleEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogControlFlow
  (loopLcmd loopLcmd_length occursIn)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter
  (renderLfundef renderLprogAtt renderLinstrR)

/-! ## 0. Flat-`Chal` layout + substring helper (mirrors `Plonky3FiatShamirEmit`)

The flat-`Chal` offsets and the word-copy body are the same as the gap-1 duplex
(`Plonky3FiatShamirEmit`); they are restated here so this module links
against the gap-1 `p3_fs_duplex` and the `hp_perm16` permute as **external asm
symbols** (resolved by the linker, exactly as the gap-1 duplex links the permute)
without a Lean import that would pull in a second top-level `main`. -/

/-- Substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- The flat-`Chal` `st` byte offset. -/
def stOff : Nat := 0
/-- The flat-`Chal` `inbuf` byte offset. -/
def inbufOff : Nat := 128
/-- The flat-`Chal` `outbuf` byte offset. -/
def outbufOff : Nat := 192
/-- The Poseidon2 permute leaf symbol (the emitted leaf the duplex calls). -/
def permSym : String := "hp_perm16"

/-- One word-copy iteration `dst[i] ← src[i]` (`%rsi` src base, `%rdx` dst base,
    `%r8` counter): load, store, advance both pointers, decrement the counter.
    Same body as the gap-1 duplex's `wordCopyBody`. **FRONT-sourced** from the
    branch/runtime-loop front `QuerySampleBranchFront.wordCopyBodyFront` (the
    `wordCopySteps` schedule); byte-identical (`rfl`). -/
def wordCopyBody : Lcmd := QuerySampleBranchFront.wordCopyBodyFront

/-! ## 0b. Flat-`Chal` counter offsets -/

/-- `inlen` (the absorb counter) byte offset in the flat `Chal`. -/
def inlenOff : Nat := 256
/-- `outlen` (the squeeze pop counter) byte offset in the flat `Chal`. -/
def outlenOff : Nat := 264

/-- The full-absorb duplex symbol (gap-1 `Plonky3FiatShamirEmit`): absorbs
    all 8 inbuf words, permutes, squeezes 8 — the `inlen==8` observe trigger. -/
def duplexFullSym : String := "p3_fs_duplex"
/-- The partial-absorb duplex symbol (emitted here): absorbs `inlen` words. -/
def duplexNSym : String := "p3_fs_duplex_n"

/-- The flat-`Chal` layout + linked symbols this deploy hands the branch/runtime-
    loop front `QuerySampleBranchFront`. Single source of truth: the front's
    schedules are parametric over this config, so the deployed bodies below are
    the front's output at `qsCfg` (byte-identical, `rfl`). -/
def qsCfg : QuerySampleBranchFront.QSConfig :=
  { inbufOff := inbufOff, outbufOff := outbufOff, inlenOff := inlenOff, outlenOff := outlenOff
    permSym := permSym, duplexFullSym := duplexFullSym, duplexNSym := duplexNSym }

/-! ## 1. The partial-absorb duplex `p3_fs_duplex_n(Chal *c)`

Same shape as gap-1 `p3_fs_duplex` (absorb / permute / squeeze) but the absorb
trip count is the **runtime** `inlen` loaded from the struct, not the constant 8.
This is the sample-path duplex (`ch_sample` triggers on `inlen > 0`, where the
inbuf may be partially full). The squeeze is the fixed 8-word copy. -/

/-- The partial-absorb duplex body. `%rdi` = flat-`Chal` base `c`, saved in the
    callee-saved `%rbx`. Absorb loop counter `%r8` is loaded from `inlen` (so it
    copies exactly `inlen` words `st[i] ← inbuf[i]`); the squeeze counter is the
    constant 8. The permute is the in-place `call hp_perm16` leaf. **FRONT-sourced**
    from `QuerySampleBranchFront.duplexNBodyFront qsCfg` (the `duplexNSteps`
    schedule — a runtime-N `loopLcmd` whose count is `.load`ed from the struct,
    guarded by an `inlen==0` `condFwd` zero-trip skip); byte-identical (`rfl`). -/
def duplexNBody : Lcmd := QuerySampleBranchFront.duplexNBodyFront qsCfg

/-- `p3_fs_duplex_n(Chal *c)`: the partial-absorb duplexing step. SysV arg 0
    (`%rdi`) is the flat-`Chal` base; the absorb count is `c->inlen`. -/
def duplexNFundef : Lfundef :=
  { lfd_tyin := [64], lfd_arg := ["RDI"]
    lfd_body := duplexNBody
    lfd_tyout := [], lfd_res := [] }

/-! ## 2. `p3_fs_observe(Chal *c, uint64_t v)`

`%rdi` = c, `%rsi` = v (SysV args 0,1). Body:

```
outlen = 0
addr   = c + inbufOff + (inlen << 3)
*addr  = v                            # inbuf[inlen] = v (already field-reduced)
inlen += 1
if (inlen == 8) { p3_fs_duplex(c); inlen = 0 }
```

The trigger test is `CMP inlen,#8 ; Lcond NE skip` (skip the duplex when
`inlen ≠ 8`); on the taken branch it `call`s the full-absorb duplex and zeroes
`inlen`. `%rbx` holds `c` across the call (the printer brackets it push/pop). -/
-- **FRONT-sourced** from `QuerySampleBranchFront.observeBodyFront qsCfg` (the
-- `observeSteps` schedule — the `if (inlen==8)` trigger is a `condFwd`-skip
-- forward branch); byte-identical (`rfl`).
def observeBody : Lcmd := QuerySampleBranchFront.observeBodyFront qsCfg

/-- `p3_fs_observe(Chal *c, uint64_t v)`: append `v` to the absorb buffer, reset
    `outlen`, and duplex when the buffer fills (`inlen==8`). SysV args 0,1. -/
def observeFundef : Lfundef :=
  { lfd_tyin := [64, 64], lfd_arg := ["RDI", "RSI"]
    lfd_body := observeBody
    lfd_tyout := [], lfd_res := [] }

/-! ## 3. `p3_fs_sample(Chal *c) -> uint64_t`

`%rdi` = c, result in `%rax`. Body:

```
if (inlen > 0 || outlen == 0) { p3_fs_duplex_n(c); inlen = 0; outlen = 8 }
outlen -= 1
return outbuf[outlen]
```

The trigger is a disjunction. We test `inlen != 0` first (`Lcond NE do_dup`); if
`inlen == 0` we fall through to test `outlen != 0` (`Lcond NE skip` — skip the
duplex). On the `do_dup` branch: call the partial-absorb duplex, set `inlen = 0`,
`outlen = 8`. Then `outlen -= 1`; load `outbuf[outlen]` into `%rax`. -/
-- **FRONT-sourced** from `QuerySampleBranchFront.sampleBodyFront qsCfg` (the
-- `sampleSteps` schedule — the disjunctive `inlen>0 || outlen==0` trigger is two
-- `condFwd` forward branches to two labels); byte-identical (`rfl`).
def sampleBody : Lcmd := QuerySampleBranchFront.sampleBodyFront qsCfg

/-- `p3_fs_sample(Chal *c) -> uint64_t`: squeeze one word out of the sponge,
    re-duplexing when the input buffer is nonempty or the output is exhausted.
    SysV arg 0; result in `%rax`. -/
def sampleFundef : Lfundef :=
  { lfd_tyin := [64], lfd_arg := ["RDI"]
    lfd_body := sampleBody
    lfd_tyout := [64], lfd_res := ["RAX"] }

/-! ## 4. `p3_fs_sample_bits(Chal *c) -> uint64_t`

`return ch_sample(c) & 31`. `%rdi` = c, result in `%rax`. We `call p3_fs_sample`
(it returns the squeezed word in `%rax`) then mask with the owned `AND:64`. The
`& 31` is the owned `regArith .and` — index/mask logic, no field op. -/
-- **FRONT-sourced** from `QuerySampleBranchFront.sampleBitsBodyFront qsCfg` (the
-- `sampleBitsSteps` schedule — `call sample` then the owned `andImm` `& 31` mask,
-- case (c): a word ALU mask, not a sub-word byte store); byte-identical (`rfl`).
def sampleBitsBody : Lcmd := QuerySampleBranchFront.sampleBitsBodyFront qsCfg

/-- `p3_fs_sample_bits(Chal *c) -> uint64_t`: the 5-bit FRI query index —
    `sample() & 31`. SysV arg 0; result in `%rax`. -/
def sampleBitsFundef : Lfundef :=
  { lfd_tyin := [64], lfd_arg := ["RDI"]
    lfd_body := sampleBitsBody
    lfd_tyout := [64], lfd_res := ["RAX"] }

/-! ## 5. The composed query-sampler `Lprog` (one `.s`) -/

/-- The FRI query-index sampler functions: the partial-absorb duplex plus the
    observe / sample / sample_bits wrapper. (The full-absorb `p3_fs_duplex` and
    the permute leaf `hp_perm16` are external symbols, linked from the gap-1 `.s`
    and the emitted Poseidon2 leaf respectively.) -/
def querySampleFuncs : List (String × Lfundef) :=
  [ (duplexNSym, duplexNFundef)
  , ("p3_fs_observe", observeFundef)
  , ("p3_fs_sample", sampleFundef)
  , ("p3_fs_sample_bits", sampleBitsFundef) ]

/-- The composed query-sampler `Lprog`. -/
def querySampleLprog : Lprog := { lp_funcs := querySampleFuncs }

def querySampleAsm : String := renderLprogAtt querySampleLprog

/-! ## 6. Shape lemmas: the wrapper is owned counter/branch/mask control flow -/

/- `observe` renders the absorb-buffer index store and the `inlen==8` trigger:
    the public counter compare `cmpq $8,%rcx`, the forward skip `jne .L7`, the
    skip label `.L7:`, and the `call p3_fs_duplex` on the trigger. Owned counter
    branch, not a C `if (inlen==8)`. -/
#guard
  let s := renderLfundef "p3_fs_observe" observeFundef.lfd_body
  hasSub s "cmpq $8, %rcx" && occursIn ".L7:" s
    && occursIn "jne .L7" s && hasSub s "call p3_fs_duplex"

/- `sample` renders the `inlen > 0 || outlen == 0` disjunctive trigger (two
    `cmpq $0` tests + two `jne` branches) and the `call p3_fs_duplex_n`
    partial-absorb duplex. Owned counter branch, not a C `if (... || ...)`. -/
#guard
  let s := renderLfundef "p3_fs_sample" sampleFundef.lfd_body
  hasSub s "cmpq $0, %rcx" && occursIn "jne .L1" s
    && occursIn "jne .L2" s && hasSub s "call p3_fs_duplex_n"

/- `sample_bits` renders the `& 31` mask as the owned `AND:64` (`andq $31,%rax`)
    over the `call p3_fs_sample` result — the 5-bit query index, a mask op, no
    field op. -/
#guard
  let s := renderLfundef "p3_fs_sample_bits" sampleBitsFundef.lfd_body
  hasSub s "call p3_fs_sample" && hasSub s "andq $31, %rax"

/- The partial-absorb duplex renders the counter-driven absorb (the `inlen` load
    into the loop counter), the loop label/back-edge, and the `call hp_perm16`
    permute — same owned duplex shape as gap-1, with a runtime absorb count. -/
#guard
  let s := renderLfundef "p3_fs_duplex_n" duplexNFundef.lfd_body
  occursIn ".L0:" s && occursIn "jne .L0" s && hasSub s "call hp_perm16"

/-! ## 6b. Front validation: each deployed body IS the branch/runtime-loop front output

The deployed `*Body` defs are set `:= QuerySampleBranchFront.*Front qsCfg`, so each
equality below is `rfl` and the emitted `.s` is byte-identical (the render KATs in
§6 carry over verbatim). This is the loop-over-call `OrchLoopFront` validation
pattern (`buildOrchLoop_eq_*`) for the forward-branch / runtime-loop front. -/

theorem duplexNBody_front :
    duplexNBody = QuerySampleBranchFront.duplexNBodyFront qsCfg := rfl
theorem observeBody_front :
    observeBody = QuerySampleBranchFront.observeBodyFront qsCfg := rfl
theorem sampleBody_front :
    sampleBody = QuerySampleBranchFront.sampleBodyFront qsCfg := rfl
theorem sampleBitsBody_front :
    sampleBitsBody = QuerySampleBranchFront.sampleBitsBodyFront qsCfg := rfl
theorem wordCopyBody_front :
    wordCopyBody = QuerySampleBranchFront.wordCopyBodyFront := rfl

/-! ## 7. The composed object carries the wrapper, no unhandled op -/

theorem querySample_has_observe :
    hasSub querySampleAsm "p3_fs_observe" = true := by native_decide
theorem querySample_has_sample_bits :
    hasSub querySampleAsm "p3_fs_sample_bits" = true := by native_decide
theorem querySample_masks :
    hasSub querySampleAsm "andq $31, %rax" = true := by native_decide
theorem querySample_no_unhandled :
    hasSub querySampleAsm "UNHANDLED" = false := by native_decide

/-- **Owned FRI query-index sampler.** The one composed `.s` carries the
    `observe`/`sample`/`sample_bits` wrapper as owned counter/branch/mask control
    flow: the `inlen`/`outlen` counters in the flat-`Chal` struct, the `if (==8)`
    / `if (>0 || ==0)` triggers as `CMP`/`Lcond` forward branches, the `& 31` mask
    as `AND:64`, and the duplex on the trigger as a `call` to the emitted duplex —
    no unhandled op and no field op (the round arithmetic is the called permute
    leaf inside the duplex). -/
theorem querySample_shape :
    hasSub querySampleAsm "p3_fs_observe" = true
      ∧ hasSub querySampleAsm "p3_fs_sample_bits" = true
      ∧ hasSub querySampleAsm "andq $31, %rax" = true
      ∧ hasSub querySampleAsm "UNHANDLED" = false :=
  ⟨querySample_has_observe, querySample_has_sample_bits,
   querySample_masks, querySample_no_unhandled⟩

theorem querySample_funcs_eq : querySampleLprog.lp_funcs = querySampleFuncs := rfl

/-! ## 8. Emit driver -/

def emitMain : IO Unit := do
  let dir := "bench/plonky3_compare/gen_com"
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir ++ "/plonky3_query_sample_owned.s") querySampleAsm
  IO.println "WROTE bench/plonky3_compare/gen_com/plonky3_query_sample_owned.s"
  IO.println "  ONE .s: DuplexChallenger observe/sample/sample_bits wrapper"
  IO.println "  counters (inlen/outlen) + if(==8)/if(>0||==0) triggers + &31 mask owned control flow"
  IO.println "  duplex on trigger = call p3_fs_duplex (gap-1) / call p3_fs_duplex_n (partial absorb)"

end CatCrypt.Crypto.SecureCompilation.VIR.Plonky3QuerySampleEmit

/-- Top-level entry point for `lake exe plonky3querysample`. -/
def main : IO UInt32 := do
  CatCrypt.Crypto.SecureCompilation.VIR.Plonky3QuerySampleEmit.emitMain
  return 0
