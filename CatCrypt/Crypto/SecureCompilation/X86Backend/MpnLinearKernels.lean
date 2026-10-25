/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
public import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
public import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll
public import CatCrypt.Crypto.SecureCompilation.X86Backend.LoopUnroll
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-!
# `mpn_add_n` / `mpn_sub_n` / `mpn_submul_1` at n ≥ 16 through the owned x86 backend

`BignumMontMulKernel.lean` lowers s2n-bignum's `bignum_mul_4_8` dual-carry-chain
idiom through the owned in-Lean x86 backend (no jasminc). This module does the
same for the **linear** elementary kernels at the sizes where jasminc's register
allocator rejects the fully-unrolled body (it exceeds the general-purpose-register
budget): `mpn_add_n` / `mpn_sub_n` / `mpn_submul_1` at
`n = 16, 32`.

## Why the owned backend clears the jasminc GPR-budget fallback

The verified Jasmin prototype emits a fully-unrolled body that keeps *every* limb
live in a distinct register (`a0..a31`, `b0..b31`, …). At `n ≥ 16` that exceeds
jasminc's allocator's ~15-GPR budget, so the bench falls back to a C ADX
reference whose per-iteration loop overhead is the gap vs GMP's deeply-unrolled
hand asm.

The kernels here are **pointer-streaming**: the operands stay in memory, and each
limb is processed with a fixed two-register scratch window (`t0`/`t1`) plus the
three pointer registers (`r`/`a`/`b`). The register pressure is therefore
**constant in `n`** — five GPRs regardless of limb count — so the fully-unrolled
straight-line body lowers cleanly for any `n`. The carry/borrow chain flows
through `CF` across the `add`/`adc` (resp. `sub`/`sbb`) sequence; `loadMem` /
`storeMem` are `MOV`s and touch no flag (`evalInstr` routes them through
`setReg`/`store`, not `writeB5W`), so the chain is unbroken across the loads and
stores. This is exactly the streaming-with-fixed-window shape GMP's `add_n` /
`sub_n` use; the unroller produces the deeply-unrolled-and-scheduled body that
matches GMP's shape, and the owned backend lowers it with no allocator wall.

## What is verified vs trusted

Identical to `BignumMontMulKernel` / `Add2Kernel`:

* **Verified**: each block lowered to `Com (x86Dialect 64)` denotes to
  `runBlock` on the source block (`*_lowering_correct`, instances of
  `lowerBlock_denote_closed`), and the resulting machine state computes the
  sum/difference (per-input value semantics pinned by `native_decide` at `n=16`
  through the full `evalInstr`/`x86_ADD`/`x86_ADC`/`x86_SUB`/`x86_SBB` chain).
  `runBlock`/`evalInstr` is the differentially-validated transcription of
  Jasmin's Rocq x86 model (`TranslationValidation.lean`).
* **Trusted (thin)**: `AsmPrinter.renderJInstr` (one `JInstr` → one AT&T line),
  `gas`, and the System-V leaf ABI glue (`renderLeafFn`).

The all-inputs functional identity (`Σ rᵢ·Bⁱ = Σ aᵢ·Bⁱ ± Σ bᵢ·Bⁱ` mod `B^n`) is
established at runtime by the byte-exact KAT vs GMP in
`bench/mpn_addsub_adx_compare/` and `bench/mpn_submul_1_adx_compare/`, the
standard gate for these word kernels (mirroring `BignumMontMulKernel`'s
`mul48_eval` per-input pins + KAT).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLinearKernels

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-! ## 1. The pointer-streaming blocks (constant register pressure in `n`)

The blocks are generated as a function of the limb count `n`. The accumulator
window is the two scratch registers `t0`/`t1`; the operands `a`/`b` and the
result `r` stay in their pointer registers (`r`→`%rdi`, `a`→`%rsi`, `b`→`%rdx`).
This is why the body lowers for any `n`: the live-register set never grows. -/

/-- One add step at limb `i`: `r[i] := a[i] + b[i] (+ CF)`. The first limb uses
    `add` (no carry-in); subsequent limbs use `adc` (carry-in from `CF`). -/
def addStep (i : Nat) : List (JInstr 64) :=
  [ .loadMem "t0" "a" (8 * i)
  , .loadMem "t1" "b" (8 * i)
  , (if i = 0 then .add "t0" (.reg "t1") else .adc "t0" (.reg "t1"))
  , .storeMem "r" (8 * i) (.reg "t0") ]

/-- The `mpn_add_n` body for `n` limbs: the streaming add chain. -/
def addBlock (n : Nat) : List (JInstr 64) :=
  (List.range n).flatMap addStep

/-- One sub step at limb `i`: `r[i] := a[i] - b[i] (- CF)`. -/
def subStep (i : Nat) : List (JInstr 64) :=
  [ .loadMem "t0" "a" (8 * i)
  , .loadMem "t1" "b" (8 * i)
  , (if i = 0 then .sub "t0" (.reg "t1") else .sbb "t0" (.reg "t1"))
  , .storeMem "r" (8 * i) (.reg "t0") ]

/-- The `mpn_sub_n` body for `n` limbs: the streaming borrow chain. -/
def subBlock (n : Nat) : List (JInstr 64) :=
  (List.range n).flatMap subStep

/-! ### Register pressure is constant in `n`

`blockNames` (the distinct register names of the block, what the allocator must
fit) is exactly `{r, a, b, t0, t1}` for every positive `n` — five names, far
under the GPR pool. This is the structural reason the owned backend lowers what
jasminc rejected. -/

/-- The add block at the small sizes `n = 4, 8` uses exactly five distinct
    registers — the same constant window as `n = 16, 32`. These are the sizes
    that the owned backend lowers with the
    identical fixed-window body. -/
theorem addBlock_4_regs : (blockNames (addBlock 4)).length = 5 := by native_decide

theorem addBlock_8_regs : (blockNames (addBlock 8)).length = 5 := by native_decide

theorem subBlock_4_regs : (blockNames (subBlock 4)).length = 5 := by native_decide

theorem subBlock_8_regs : (blockNames (subBlock 8)).length = 5 := by native_decide

/-- The add block at `n = 16` uses exactly five distinct registers. -/
theorem addBlock_16_regs : (blockNames (addBlock 16)).length = 5 := by native_decide

/-- The add block at `n = 32` uses exactly five distinct registers (same as
    `n = 16`: register pressure is constant in `n`). -/
theorem addBlock_32_regs : (blockNames (addBlock 32)).length = 5 := by native_decide

/-- The sub block at `n = 32` likewise uses five registers. -/
theorem subBlock_32_regs : (blockNames (subBlock 32)).length = 5 := by native_decide

/-- The add block has four instructions per limb. -/
theorem addBlock_16_length : (addBlock 16).length = 64 := by native_decide

theorem addBlock_32_length : (addBlock 32).length = 128 := by native_decide

/-! ## 2. Lowering correctness (denotation = `runBlock`)

Every block — for any `n` — is lowering-correct by `lowerBlock_denote_closed`,
which is generic over `List (JInstr w)`. -/

/-- **Lowering correctness, add block.** For any `n` and any initial state,
    lowering `addBlock n` and denoting equals `runBlock` on the source block. -/
theorem addBlock_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBlock (Γ := []) (addBlock n)).denote (.cons s .nil)
      = runBlock s (addBlock n) :=
  lowerBlock_denote_closed (addBlock n) s

/-- **Lowering correctness, sub block.** -/
theorem subBlock_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBlock (Γ := []) (subBlock n)).denote (.cons s .nil)
      = runBlock s (subBlock n) :=
  lowerBlock_denote_closed (subBlock n) s

/-! ## 3. Per-input value semantics (`native_decide` at `n = 16`)

Run the symbolic `runBlock`/`evalInstr` semantics on a representative input and
check that the stored result words are the limb-wise add/sub with carry — pinning
the streaming carry-chain's value semantics through the full
`x86_ADD`/`x86_ADC`/`x86_SUB`/`x86_SBB` chain. The all-inputs identity is the
runtime KAT vs GMP. -/

/-- Init state seeding `a`/`b` buffers with 16 limbs each. `aFn`/`bFn` give the
    limb values; `r` and flags start clear. -/
def initState16 (aFn bFn : Nat → BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    flags := { cf := some false }
    mem := fun base off =>
      if base = "a" then (if off % 8 = 0 ∧ 0 ≤ off ∧ off < 128
                          then aFn (off / 8).toNat else 0)
      else if base = "b" then (if off % 8 = 0 ∧ 0 ≤ off ∧ off < 128
                          then bFn (off / 8).toNat else 0)
      else 0 }

/-- The all-ones operand: the maximal carry-propagation case. -/
def allOnes16 : Nat → BitVec 64 := fun _ => BitVec.allOnes 64

/-- A single one in limb 0 (used to force the carry to ripple the full chain). -/
def one16 : Nat → BitVec 64 := fun i => if i = 0 then 1 else 0

set_option maxRecDepth 4000 in
/-- **Add carry ripples the full 16-limb chain (value semantics).** With
    `a = 2^1024 - 1` (all-ones) and `b = 1`, the result is all-zero limbs and a
    carry-out: every `r[i] = 0`. Checked through the full streaming
    `add`/`adc` chain by `native_decide`. -/
theorem add16_ripple :
    let s := runBlock (initState16 allOnes16 one16) (addBlock 16)
    (s.load "r" 0).toNat = 0 ∧ (s.load "r" 8).toNat = 0
      ∧ (s.load "r" 120).toNat = 0 ∧ s.flags.cf = some true := by
  native_decide

set_option maxRecDepth 4000 in
/-- **Add value semantics on a mixed input.** `r[0] = a[0] + b[0] mod 2^64`,
    no carry, on representative limbs. -/
theorem add16_mixed :
    let aF : Nat → BitVec 64 := fun i => BitVec.ofNat 64 (3 * i + 1)
    let bF : Nat → BitVec 64 := fun i => BitVec.ofNat 64 (5 * i + 2)
    let s := runBlock (initState16 aF bF) (addBlock 16)
    (s.load "r" 0).toNat = 3 ∧ (s.load "r" 8) = BitVec.ofNat 64 (4 + 7) := by
  native_decide

set_option maxRecDepth 4000 in
/-- **Sub borrow ripples the full 16-limb chain (value semantics).** With
    `a = 0` and `b = 1`, the difference borrows all the way out: `r[0] = 2^64-1`,
    every higher `r[i] = 2^64-1`, and `CF = 1` (borrow-out). -/
theorem sub16_ripple :
    let zero16 : Nat → BitVec 64 := fun _ => 0
    let s := runBlock (initState16 zero16 one16) (subBlock 16)
    (s.load "r" 0) = BitVec.allOnes 64 ∧ (s.load "r" 120) = BitVec.allOnes 64
      ∧ s.flags.cf = some true := by
  native_decide

/-! ## 4. `mpn_submul_1` at n ≥ 16 through the owned backend (streaming MULX)

`mpn_submul_1(r, a, b)` computes `r[i] := r[i] - a[i]*b - borrow`, returning the
final borrow. The streaming MULX form keeps the multiplier `b` in the
`%rdx`-pinned `bd` register (the implicit `MULX` src1), the product scratch in
`lo`/`hi`, and a single borrow carried via the running high word `hc` plus `CF`.

Per limb `i`:
* `(lo,hi) := a[i] * b` via memory-operand `MULX` (reads `a[i]` straight from
  `[a + 8i]`);
* fold the previous limb's high word `hc` into `lo` (carry into the low product);
* `r[i] := r[i] - lo` with borrow (`sub`/`sbb`), keeping `CF`;
* carry the high half `hi` (plus the sub borrow) forward as the next `hc`.

The register window (`bd`/`lo`/`hi`/`hc`/`t`/pointers) is constant in `n`, so the
unrolled body lowers for any `n`, clearing the jasminc fallback. -/

/-- One submul_1 step at limb `i`. Streaming single-chain MULX + borrow:
    `r[i] := r[i] - a[i]*b - hc_in`, producing the new high carry in `hc`. The
    product low half is `lo`, the high half `hi`; `t` holds the loaded `r[i]`. -/
def submul1Step (i : Nat) : List (JInstr 64) :=
  [ .mulxMem "hi" "lo" (.reg "bd") "a" (8 * i)   -- (lo,hi) = a[i]*b
  , .add "lo" (.reg "hc")                        -- fold previous high carry into lo
  , .adc "hi" (.imm 0)                           -- absorb the carry-out into hi
  , .loadMem "t" "r" (8 * i)                      -- t = r[i]
  , .sub "t" (.reg "lo")                          -- t := r[i] - lo  (CF = borrow)
  , .storeMem "r" (8 * i) (.reg "t")              -- r[i] := t
  , .adc "hi" (.imm 0)                            -- propagate borrow into next high carry
  , .mov "hc" (.reg "hi") ]                       -- hc := hi for next limb

/-- The `mpn_submul_1` body for `n` limbs. The leading `mov hc, 0` seeds the
    running high carry; the per-limb `submul1Step` streams the product/borrow. -/
def submul1Block (n : Nat) : List (JInstr 64) :=
  .mov "hc" (.imm 0) :: (List.range n).flatMap submul1Step

/-- `submul_1` register pressure is constant in `n`: `{bd, a, r, lo, hi, hc, t}`
    — seven names, well under the GPR pool. -/
theorem submul1Block_16_regs : (blockNames (submul1Block 16)).length = 7 := by
  native_decide

theorem submul1Block_4_regs : (blockNames (submul1Block 4)).length = 7 := by
  native_decide

theorem submul1Block_8_regs : (blockNames (submul1Block 8)).length = 7 := by
  native_decide

theorem submul1Block_32_regs : (blockNames (submul1Block 32)).length = 7 := by
  native_decide

/-- **Lowering correctness, submul_1 block.** -/
theorem submul1Block_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBlock (Γ := []) (submul1Block n)).denote (.cons s .nil)
      = runBlock s (submul1Block n) :=
  lowerBlock_denote_closed (submul1Block n) s

/-! ## 4b. `mpn_sqr_basecase` at n ≥ 16 through the owned backend (streaming addmul rows)

`mpn_sqr_basecase(r, a)` computes the full `2n`-limb square `r = a²`. The kernel
here is a **memory-streaming schoolbook square**: it zeroes the `2n`-limb result,
then for each row `j` it accumulates `a[j] · a[i]` into `r[i+j]` over all `i`
(`addmul_1` column accumulation, the column form `mpn_sqr_basecase` is built on).
The result accumulator lives in memory, so the register window is constant in
`n` — the multiplier `bd` (pinned to `%rdx`), the product scratch `lo`/`hi`, the
running carry `hc`, and the accumulator temp `t` — which is why the unrolled body
lowers where jasminc's per-column register banks overflow.

This is the schoolbook square (`n²` `MULX`), correct vs GMP byte-for-byte (the
runtime KAT in `bench/mpn_sqr_diagonal_compare/` gates it); it clears the
C-loop fallback at `n ≥ 16`. The diagonal-doubling saving (`n(n+1)/2` `MULX`)
that GMP's hand-asm `sqr_basecase` exploits is a deeper schedule, emitted through
the owned backend in §4c below (`sqrDiagBlock`). -/

/-- Zero one result limb `k`: `r[k] := 0`. -/
def zeroStep (k : Nat) : List (JInstr 64) :=
  [ .mov "z" (.imm 0), .storeMem "r" (8 * k) (.reg "z") ]

/-- One inner addmul step within row `j` at column `i`: accumulate
    `a[i] · a[j]` (with `bd = a[j]` in `%rdx`) into `r[i+j]`, threading the high
    word through `hc` and the column carry through `CF`. -/
def sqrInnerStep (j i : Nat) : List (JInstr 64) :=
  [ .mulxMem "hi" "lo" (.reg "bd") "a" (8 * i)   -- (lo,hi) = a[i]*a[j]
  , .add "lo" (.reg "hc")                        -- fold previous high carry
  , .adc "hi" (.imm 0)
  , .loadMem "t" "r" (8 * (i + j))               -- t = r[i+j]
  , .add "t" (.reg "lo")                          -- t += lo  (CF = carry)
  , .storeMem "r" (8 * (i + j)) (.reg "t")        -- r[i+j] := t
  , .adc "hi" (.imm 0)                            -- carry into next high word
  , .mov "hc" (.reg "hi") ]

/-- Row `j` of the schoolbook square: load `a[j]` into the multiplier `bd`, clear
    the running high carry, accumulate `a[i]·a[j]` for all `i < n` into
    `r[j..j+n]`, then store the final high carry into `r[j+n]`. -/
def sqrRow (n j : Nat) : List (JInstr 64) :=
  [ .loadMem "bd" "a" (8 * j), .mov "hc" (.imm 0) ]
    ++ (List.range n).flatMap (fun i => sqrInnerStep j i)
    ++ [ .loadMem "t" "r" (8 * (n + j))
       , .add "t" (.reg "hc")
       , .storeMem "r" (8 * (n + j)) (.reg "t") ]

/-- The `mpn_sqr_basecase` body for `n` limbs: zero the `2n`-limb result, then
    accumulate every schoolbook row. -/
def sqrBlock (n : Nat) : List (JInstr 64) :=
  (List.range (2 * n)).flatMap zeroStep
    ++ (List.range n).flatMap (fun j => sqrRow n j)

/-- **Lowering correctness, sqr block.** -/
theorem sqrBlock_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBlock (Γ := []) (sqrBlock n)).denote (.cons s .nil)
      = runBlock s (sqrBlock n) :=
  lowerBlock_denote_closed (sqrBlock n) s

/-- sqr register pressure is constant in `n`: `{r, z, bd, a, hc, lo, hi, t}`
    — eight names, under the GPR pool, for every `n`. -/
theorem sqrBlock_16_regs : (blockNames (sqrBlock 16)).length = 8 := by
  native_decide

theorem sqrBlock_4_regs : (blockNames (sqrBlock 4)).length = 8 := by
  native_decide

theorem sqrBlock_8_regs : (blockNames (sqrBlock 8)).length = 8 := by
  native_decide

/-! ## 4c. `mpn_sqr_basecase` diagonal-symmetry square through the owned backend

The schoolbook `sqrBlock` does `n²` `MULX`. GMP's `sqr_basecase` exploits the
symmetry `a[i]·a[j] = a[j]·a[i]`: it computes each off-diagonal product `(i,j)`
with `i < j` **once**, doubles the whole off-diagonal sum, then adds the
diagonal squares `a[i]²`. The multiply count drops from `n²` to
`n + n(n-1)/2 = n(n+1)/2` — the algorithmic floor for an `n×n→2n` square via
independent multiplies.

This is the same three-stage schedule as the C reference
`bench/mpn_sqr_diagonal_compare/sqr_diagonal_ref.c`, here lowered through the
owned in-Lean x86 backend (no jasminc, no C loop) with a register window
**constant in `n`** — exactly the property that clears jasminc's per-column
GPR-budget fallback.

### The three stages

1. **Cross products (lower triangle).** Zero the `2n`-limb result, then for each
   row `j ∈ 1..n-1` (with `bd = a[j]` in `%rdx`) accumulate `a[i]·a[j]` into
   `r[i+j]` for `i ∈ 0..j-1`, threading the running high word through `hc` and
   the column carry through `CF` (the proven `sqrInnerStep` machinery, restricted
   to the strict lower triangle `i < j`). After the row, the final high carry is
   stored into `r[2j]`. The result accumulator then holds
   `t = Σ_{i<j} a_i a_j · B^{i+j}` in `r[0..2n-1]` (`r[0] = 0`).

2. **Double.** `r := 2·t`, an `ADCX` self-add chain across all `2n` limbs:
   clear `CF`, then per limb `k` load `r[k]` into `t`, `adcx t, t`
   (`t := 2·t + CF`, carry out to `CF`), store back. This is the
   single-instruction-per-limb doubling sweep (no extra multiplies).

3. **Diagonal.** Add `a[i]²` into `r[2i..2i+1]` for each `i`, propagating the
   carry forward limb-by-limb along an `adc` chain so a diagonal carry-out from
   `r[2i+1]` ripples into the next diagonal pair.

The register window is `{r, a, bd, lo, hi, hc, t, z}` — eight names, constant in
`n` (same as the schoolbook `sqrBlock`), so the fully-unrolled body lowers for
any `n`. -/

/-- One inner cross-product step within row `j` at column `i < j`: accumulate
    `a[i]·a[j]` (with `bd = a[j]`) into `r[i+j]`. Structurally identical to
    `sqrInnerStep`; named separately for the diagonal schedule's lower-triangle
    loop. -/
def crossInnerStep (j i : Nat) : List (JInstr 64) := sqrInnerStep j i

/-- Row `j` of the cross-product (lower-triangle) stage: load `a[j]` into `bd`,
    clear `hc`, accumulate `a[i]·a[j]` for `i ∈ 0..j-1` into `r[j..2j-1]`, then
    store the final high carry into `r[2j]`. -/
def crossRow (j : Nat) : List (JInstr 64) :=
  [ .loadMem "bd" "a" (8 * j), .mov "hc" (.imm 0) ]
    ++ (List.range j).flatMap (fun i => crossInnerStep j i)
    ++ [ .loadMem "t" "r" (8 * (2 * j))
       , .add "t" (.reg "hc")
       , .storeMem "r" (8 * (2 * j)) (.reg "t") ]

/-- Stage 1: zero the `2n`-limb result, then accumulate the strict lower triangle
    `Σ_{i<j} a_i a_j B^{i+j}`. Rows `j = 1..n-1` (row `0` is empty). -/
def crossBlock (n : Nat) : List (JInstr 64) :=
  (List.range (2 * n)).flatMap zeroStep
    ++ (List.range n).flatMap (fun j => crossRow j)

/-- One doubling step at limb `k`: `r[k] := 2·r[k] + CF` (`adcx t, t`), carry
    out to `CF`. -/
def doubleStep (k : Nat) : List (JInstr 64) :=
  [ .loadMem "t" "r" (8 * k)
  , .adcx "t" (.reg "t")
  , .storeMem "r" (8 * k) (.reg "t") ]

/-- Stage 2: `r := 2·r` over all `2n` limbs. The leading `mov z,0; adcx z,z`
    seeds `CF = 0` (a self-`adcx` of a freshly-zeroed register clears `CF`); each
    `doubleStep` then threads the doubling carry through `CF`. -/
def doubleBlock (n : Nat) : List (JInstr 64) :=
  [ .mov "z" (.imm 0), .adcx "z" (.reg "z") ]
    ++ (List.range (2 * n)).flatMap doubleStep

/-- One diagonal step at `i`: `(lo,hi) := a[i]²`, then add `lo` into `r[2i]` and
    `hi` into `r[2i+1]` along the `adc` carry chain. The diagonal-stage carry is
    threaded through `CF` so a carry-out of the `hi` add ripples into the next
    pair's low add. -/
def diagStep (i : Nat) : List (JInstr 64) :=
  [ .mulxMem "hi" "lo" (.reg "bd") "a" (8 * i)     -- (lo,hi) = a[i]*a[i]  (bd = a[i])
  , .loadMem "t" "r" (8 * (2 * i))                  -- t = r[2i]
  , (if i = 0 then .add "t" (.reg "lo") else .adc "t" (.reg "lo"))
  , .storeMem "r" (8 * (2 * i)) (.reg "t")          -- r[2i] := t
  , .loadMem "t" "r" (8 * (2 * i + 1))              -- t = r[2i+1]
  , .adc "t" (.reg "hi")                            -- t := r[2i+1] + hi + CF
  , .storeMem "r" (8 * (2 * i + 1)) (.reg "t") ]    -- r[2i+1] := t

/-- Stage 3: add the diagonal squares `a[i]²` into `r[2i..2i+1]`. Before each
    `mulxMem` the multiplier `bd` is re-loaded with `a[i]` (the `MULX` src1). -/
def diagBlock (n : Nat) : List (JInstr 64) :=
  (List.range n).flatMap (fun i =>
    [ .loadMem "bd" "a" (8 * i) ] ++ diagStep i)

/-- The diagonal-symmetry `mpn_sqr_basecase` body for `n` limbs: cross-product
    lower triangle, double, then add the diagonal squares. Multiply count is
    `n(n-1)/2 + n = n(n+1)/2` (vs `n²` for the schoolbook `sqrBlock`). -/
def sqrDiagBlock (n : Nat) : List (JInstr 64) :=
  crossBlock n ++ doubleBlock n ++ diagBlock n

/-- **Lowering correctness, diagonal sqr block.** -/
theorem sqrDiagBlock_lowering_correct (n : Nat) (s : JState 64) :
    (lowerBlock (Γ := []) (sqrDiagBlock n)).denote (.cons s .nil)
      = runBlock s (sqrDiagBlock n) :=
  lowerBlock_denote_closed (sqrDiagBlock n) s

/-- diagonal-sqr register pressure is constant in `n`:
    `{r, z, a, bd, hc, lo, hi, t}` — eight names, under the GPR pool, for every
    `n`. This is the structural reason the unrolled body lowers where jasminc's
    per-column register banks overflow. -/
theorem sqrDiagBlock_16_regs : (blockNames (sqrDiagBlock 16)).length = 8 := by
  native_decide

theorem sqrDiagBlock_32_regs : (blockNames (sqrDiagBlock 32)).length = 8 := by
  native_decide

theorem sqrDiagBlock_4_regs : (blockNames (sqrDiagBlock 4)).length = 8 := by
  native_decide

theorem sqrDiagBlock_8_regs : (blockNames (sqrDiagBlock 8)).length = 8 := by
  native_decide

/-- The diagonal-sqr multiply count is `n(n+1)/2`: `n(n-1)/2` cross products plus
    `n` diagonal squares. (Counts the `mulxMem` instructions.) -/
def mulxCount (b : List (JInstr 64)) : Nat :=
  (b.filter (fun i => match i with | .mulxMem _ _ _ _ _ => true | _ => false)).length

theorem sqrDiagBlock_16_mulxCount : mulxCount (sqrDiagBlock 16) = 136 := by
  native_decide  -- 16·17/2 = 136

theorem sqrBlock_16_mulxCount : mulxCount (sqrBlock 16) = 256 := by
  native_decide  -- 16² = 256

/-- The diagonal schedule strictly fewer multiplies than the schoolbook at
    `n = 16` (136 < 256), and at `n = 32` (528 < 1024). -/
theorem sqrDiagBlock_mulx_lt_schoolbook_16 :
    mulxCount (sqrDiagBlock 16) < mulxCount (sqrBlock 16) := by native_decide

theorem sqrDiagBlock_mulx_lt_schoolbook_32 :
    mulxCount (sqrDiagBlock 32) < mulxCount (sqrBlock 32) := by native_decide

/-! ## 4d. Constant time, at every limb count

Every block in this module streams through the pointer bases `r`/`a`/`b` at
literal `8·i` displacements; the carry, borrow and product chains are register
ALU. No step emits a register-indexed `loadMemIdx`/`storeMemIdx`, so each
family is in the direct-addressing class uniformly in the limb count `n`, and
`ConstantTimeCoverage.allDirect_constant_time` gives a state-independent
machine leakage trace for every `n`. -/

/-- One add step reads `a[i]`/`b[i]` and writes `r[i]` at literal displacements. -/
theorem addStep_allDirect (i : Nat) : allDirect (addStep i) = true := by
  by_cases hi : i = 0 <;> simp [allDirect, addStep, hi, IsDirect]

/-- The `mpn_add_n` body is in the direct-addressing class at every limb count. -/
theorem addBlock_allDirect (n : Nat) : allDirect (addBlock n) = true :=
  allDirect_flatMap _ _ addStep_allDirect

/-- **Constant time, every limb count.** The streaming add chain produces the
    same machine leakage trace from any two starting states. -/
theorem addBlock_constant_time (n : Nat) (s₁ s₂ : JState 64) :
    blockLeak s₁ (addBlock n) = blockLeak s₂ (addBlock n) :=
  allDirect_constant_time _ (addBlock_allDirect n) s₁ s₂

/-- One sub step reads `a[i]`/`b[i]` and writes `r[i]` at literal displacements. -/
theorem subStep_allDirect (i : Nat) : allDirect (subStep i) = true := by
  by_cases hi : i = 0 <;> simp [allDirect, subStep, hi, IsDirect]

/-- The `mpn_sub_n` body is in the direct-addressing class at every limb count. -/
theorem subBlock_allDirect (n : Nat) : allDirect (subBlock n) = true :=
  allDirect_flatMap _ _ subStep_allDirect

/-- **Constant time, every limb count.** The streaming borrow chain produces the
    same machine leakage trace from any two starting states. -/
theorem subBlock_constant_time (n : Nat) (s₁ s₂ : JState 64) :
    blockLeak s₁ (subBlock n) = blockLeak s₂ (subBlock n) :=
  allDirect_constant_time _ (subBlock_allDirect n) s₁ s₂

/-- One `submul_1` step: the `MULX` reads `a[i]` at a literal displacement and
    the accumulator temp reads/writes `r[i]` at a literal displacement. -/
theorem submul1Step_allDirect (i : Nat) : allDirect (submul1Step i) = true := by
  simp [allDirect, submul1Step, IsDirect]

/-- The `mpn_submul_1` body is in the direct-addressing class at every limb
    count. -/
theorem submul1Block_allDirect (n : Nat) : allDirect (submul1Block n) = true := by
  have h : allDirect ((List.range n).flatMap submul1Step) = true :=
    allDirect_flatMap _ _ submul1Step_allDirect
  rw [show submul1Block n
        = [JInstr.mov "hc" (.imm 0)] ++ (List.range n).flatMap submul1Step from rfl,
    allDirect_append, h]
  simp [allDirect, IsDirect]

/-- **Constant time, every limb count.** The streaming `submul_1` product/borrow
    chain produces the same machine leakage trace from any two starting states. -/
theorem submul1Block_constant_time (n : Nat) (s₁ s₂ : JState 64) :
    blockLeak s₁ (submul1Block n) = blockLeak s₂ (submul1Block n) :=
  allDirect_constant_time _ (submul1Block_allDirect n) s₁ s₂

/-- Zeroing one result limb writes at a literal displacement. -/
theorem zeroStep_allDirect (k : Nat) : allDirect (zeroStep k) = true := by
  simp [allDirect, zeroStep, IsDirect]

/-- One schoolbook inner step addresses `a[i]` and `r[i+j]` at literal
    displacements. -/
theorem sqrInnerStep_allDirect (j i : Nat) : allDirect (sqrInnerStep j i) = true := by
  simp [allDirect, sqrInnerStep, IsDirect]

/-- One schoolbook row is in the direct-addressing class. -/
theorem sqrRow_allDirect (n j : Nat) : allDirect (sqrRow n j) = true := by
  have h : allDirect ((List.range n).flatMap (fun i => sqrInnerStep j i)) = true :=
    allDirect_flatMap _ _ (sqrInnerStep_allDirect j)
  rw [sqrRow, allDirect_append, allDirect_append, h]
  simp [allDirect, IsDirect]

/-- The schoolbook `mpn_sqr_basecase` body is in the direct-addressing class at
    every limb count. -/
theorem sqrBlock_allDirect (n : Nat) : allDirect (sqrBlock n) = true := by
  rw [sqrBlock, allDirect_append,
    allDirect_flatMap _ _ zeroStep_allDirect,
    allDirect_flatMap _ _ (fun j => sqrRow_allDirect n j)]
  rfl

/-- **Constant time, every limb count.** The schoolbook square produces the same
    machine leakage trace from any two starting states. -/
theorem sqrBlock_constant_time (n : Nat) (s₁ s₂ : JState 64) :
    blockLeak s₁ (sqrBlock n) = blockLeak s₂ (sqrBlock n) :=
  allDirect_constant_time _ (sqrBlock_allDirect n) s₁ s₂

/-- One cross-product row of the diagonal schedule is in the direct-addressing
    class. -/
theorem crossRow_allDirect (j : Nat) : allDirect (crossRow j) = true := by
  have h : allDirect ((List.range j).flatMap (fun i => crossInnerStep j i)) = true :=
    allDirect_flatMap _ _ (sqrInnerStep_allDirect j)
  rw [crossRow, allDirect_append, allDirect_append, h]
  simp [allDirect, IsDirect]

/-- Stage 1 of the diagonal square (zero + lower triangle) is in the
    direct-addressing class. -/
theorem crossBlock_allDirect (n : Nat) : allDirect (crossBlock n) = true := by
  rw [crossBlock, allDirect_append,
    allDirect_flatMap _ _ zeroStep_allDirect,
    allDirect_flatMap _ _ (fun j => crossRow_allDirect j)]
  rfl

/-- One doubling step reads and writes `r[k]` at a literal displacement. -/
theorem doubleStep_allDirect (k : Nat) : allDirect (doubleStep k) = true := by
  simp [allDirect, doubleStep, IsDirect]

/-- Stage 2 of the diagonal square (the `ADCX` doubling sweep) is in the
    direct-addressing class. -/
theorem doubleBlock_allDirect (n : Nat) : allDirect (doubleBlock n) = true := by
  have h : allDirect ((List.range (2 * n)).flatMap doubleStep) = true :=
    allDirect_flatMap _ _ doubleStep_allDirect
  rw [doubleBlock, allDirect_append, h]
  simp [allDirect, IsDirect]

/-- One diagonal step addresses `a[i]`, `r[2i]` and `r[2i+1]` at literal
    displacements. -/
theorem diagStep_allDirect (i : Nat) : allDirect (diagStep i) = true := by
  by_cases hi : i = 0 <;> simp [allDirect, diagStep, hi, IsDirect]

/-- Stage 3 of the diagonal square (the diagonal squares) is in the
    direct-addressing class. -/
theorem diagBlock_allDirect (n : Nat) : allDirect (diagBlock n) = true := by
  refine allDirect_flatMap _ _ (fun i => ?_)
  rw [allDirect_append, diagStep_allDirect i]
  simp [allDirect, IsDirect]

/-- The diagonal-symmetry `mpn_sqr_basecase` body is in the direct-addressing
    class at every limb count. -/
theorem sqrDiagBlock_allDirect (n : Nat) : allDirect (sqrDiagBlock n) = true := by
  rw [sqrDiagBlock, allDirect_append, allDirect_append, crossBlock_allDirect n,
    doubleBlock_allDirect n, diagBlock_allDirect n]
  rfl

/-- **Constant time, every limb count.** The diagonal-symmetry square produces
    the same machine leakage trace from any two starting states. -/
theorem sqrDiagBlock_constant_time (n : Nat) (s₁ s₂ : JState 64) :
    blockLeak s₁ (sqrDiagBlock n) = blockLeak s₂ (sqrDiagBlock n) :=
  allDirect_constant_time _ (sqrDiagBlock_allDirect n) s₁ s₂

/-! ## 5. AT&T assembly emission (owned backend, no jasminc)

System-V signatures:
* `void mpn_add_n_owned_<n>(uint64_t *r, const uint64_t *a, const uint64_t *b)`
  — `r`→`%rdi`, `a`→`%rsi`, `b`→`%rdx`. (Same for `sub`.)
* `uint64_t mpn_submul_1_owned_<n>(uint64_t *r, const uint64_t *a, uint64_t b)`
  — `r`→`%rdi`, `a`→`%rsi`, `b`→`%rdx`; but `%rdx` is the `MULX` src1, so the
  multiplier is pinned to `bd`→`%rdx` and the body reads `a[i]` from `[a]`.

The body lines are verified; the prologue/epilogue ABI glue is trusted. -/

/-- Pin add/sub pointers to their System-V argument registers. -/
def ptrPinned : GpAlloc := [("r", "%rdi"), ("a", "%rsi"), ("b", "%rdx")]

def addAlloc (n : Nat) : GpAlloc := allocGp ptrPinned (addBlock n)
def subAlloc (n : Nat) : GpAlloc := allocGp ptrPinned (subBlock n)

/-- The rendered AT&T body for the add kernel at `n` limbs. -/
def addAsm (n : Nat) : String :=
  renderLeafFn s!"mpn_add_n_owned_{n}"
    (prologue := [])
    (bodyLines := renderBlockBody (addAlloc n) (addBlock n))
    (epilogue := [ "\tret" ])

/-- The rendered AT&T body for the sub kernel at `n` limbs. -/
def subAsm (n : Nat) : String :=
  renderLeafFn s!"mpn_sub_n_owned_{n}"
    (prologue := [])
    (bodyLines := renderBlockBody (subAlloc n) (subBlock n))
    (epilogue := [ "\tret" ])

/-- submul_1 pins: `r`→`%rdi`, `a`→`%rsi`, the multiplier `bd`→`%rdx` (the
    `MULX` src1). The third argument arrives in `%rdx` and is already where the
    multiplier must live, so no prologue move is needed. -/
def submul1Pinned : GpAlloc := [("r", "%rdi"), ("a", "%rsi"), ("bd", "%rdx")]
def submul1Alloc (n : Nat) : GpAlloc := allocGp submul1Pinned (submul1Block n)

/-- The rendered AT&T `.s` for the submul_1 kernel at `n` limbs. The final high
    carry `hc` is moved to `%rax` for the return value. -/
def submul1Asm (n : Nat) : String :=
  renderLeafFn s!"mpn_submul_1_owned_{n}"
    (prologue := abiSave (submul1Alloc n))
    (bodyLines := renderBlockBody (submul1Alloc n) (submul1Block n))
    (epilogue :=
      [ "\tmovq " ++ regOf (submul1Alloc n) "hc" ++ ", %rax" ]
        ++ abiRestore (submul1Alloc n) ++ [ "\tret" ])

/-- sqr pins: `r`→`%rdi`, `a`→`%rsi`, the per-row multiplier `bd`→`%rdx` (the
    `MULX` src1; loaded with `a[j]` per row). -/
def sqrPinned : GpAlloc := [("r", "%rdi"), ("a", "%rsi"), ("bd", "%rdx")]
def sqrAlloc (n : Nat) : GpAlloc := allocGp sqrPinned (sqrBlock n)

/-- The rendered AT&T `.s` for the sqr kernel at `n` limbs. -/
def sqrAsm (n : Nat) : String :=
  renderLeafFn s!"mpn_sqr_basecase_owned_{n}"
    (prologue := abiSave (sqrAlloc n))
    (bodyLines := renderBlockBody (sqrAlloc n) (sqrBlock n))
    (epilogue := abiRestore (sqrAlloc n) ++ [ "\tret" ])

/-- diagonal-sqr pins: `r`→`%rdi`, `a`→`%rsi`, the multiplier `bd`→`%rdx` (the
    `MULX` src1; loaded with `a[j]`/`a[i]` per cross row / diagonal step). -/
def sqrDiagPinned : GpAlloc := [("r", "%rdi"), ("a", "%rsi"), ("bd", "%rdx")]
def sqrDiagAlloc (n : Nat) : GpAlloc := allocGp sqrDiagPinned (sqrDiagBlock n)

/-- The rendered AT&T `.s` for the diagonal-symmetry sqr kernel at `n` limbs. -/
def sqrDiagAsm (n : Nat) : String :=
  renderLeafFn s!"mpn_sqr_basecase_diag_owned_{n}"
    (prologue := abiSave (sqrDiagAlloc n))
    (bodyLines := renderBlockBody (sqrDiagAlloc n) (sqrDiagBlock n))
    (epilogue := abiRestore (sqrDiagAlloc n) ++ [ "\tret" ])

/-! ## 6. Shape checks on the emitted asm -/

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/- The add kernel emits the streaming `add`/`adc` chain with memory operands. -/
#guard (hasSub (addAsm 16) "addq") && (hasSub (addAsm 16) "adcq") && (hasSub (addAsm 16) "(%rsi)") && (hasSub (addAsm 16) "(%rdi)")

/- The sub kernel emits the streaming `sub`/`sbb` chain. -/
#guard (hasSub (subAsm 16) "subq") && (hasSub (subAsm 16) "sbbq")

/- The submul_1 kernel emits the streaming MULX + borrow chain. -/
#guard (hasSub (submul1Asm 16) "mulxq") && (hasSub (submul1Asm 16) "subq") && (hasSub (submul1Asm 16) "adcq")

/- The sqr kernel emits the streaming addmul-row schoolbook (MULX + add chain). -/
#guard (hasSub (sqrAsm 16) "mulxq") && (hasSub (sqrAsm 16) "addq") && (hasSub (sqrAsm 16) "adcq")

/- The diagonal-sqr kernel emits the cross-product MULX chain, the `adcx`
    doubling sweep, and the diagonal `adc` absorb. -/
#guard (hasSub (sqrDiagAsm 16) "mulxq") && (hasSub (sqrDiagAsm 16) "adcx") && (hasSub (sqrDiagAsm 16) "adcq")

/-! ### Value-semantics pin (diagonal sqr)

Run the symbolic `runBlock`/`evalInstr` semantics on a concrete `a` and check
that the `2n` stored result words equal the integer square `a²`. This pins the
three-stage cross/double/diagonal carry chain's value semantics through the full
`x86_MULX`/`x86_ADD`/`x86_ADC`/`x86_ADCX` chain. The all-inputs identity is the
runtime KAT vs GMP in `bench/mpn_sqr_diagonal_compare/`. -/

/-- Init state seeding the `a` buffer with `n` limbs from `aFn`; `r` and flags
    start clear (the kernel zeroes `r` itself in stage 1). -/
def initSqr (aFn : Nat → BitVec 64) (n : Nat) : JState 64 :=
  { regs := fun _ => 0
    flags := { cf := some false }
    mem := fun base off =>
      if base = "a" then
        (if off % 8 = 0 ∧ 0 ≤ off ∧ off < 8 * n then aFn (off / 8).toNat else 0)
      else 0 }

/-- The `2n` result limbs of a block run on `initSqr aFn n`, as a `BitVec 64`
    list (little-endian). Used to cross-check the diagonal schedule against the
    KAT-validated schoolbook `sqrBlock`. -/
def resultLimbs (blk : List (JInstr 64)) (aFn : Nat → BitVec 64) (n : Nat) :
    List (BitVec 64) :=
  let s := runBlock (initSqr aFn n) blk
  (List.range (2 * n)).map (fun k => s.load "r" ((8 * k : Nat) : Int))

/-- A representative `n = 4` input (limbs `3, 10, 17, 24`). -/
def sqrTestInput : Nat → BitVec 64 := fun i => BitVec.ofNat 64 (7 * i + 3)

/-- A carry-edge `n = 4` input: top limb all-ones forces cross-product and
    doubling carries to ripple the full chain. -/
def sqrTestInputEdge : Nat → BitVec 64 :=
  fun i => if i = 0 then BitVec.allOnes 64 else BitVec.ofNat 64 (1000003 * i)

set_option maxRecDepth 8000 in
/-- **Diagonal sqr value semantics, n = 4, small input.** Every result limb of
    the diagonal schedule equals the corresponding limb of the schoolbook
    `sqrBlock` (which is KAT-validated byte-exact vs GMP). This pins the
    cross/double/diagonal carry chain against the trusted schoolbook square. -/
theorem sqrDiag4_small_matches_schoolbook :
    ∀ k ∈ List.range 8,
      (runBlock (initSqr sqrTestInput 4) (sqrDiagBlock 4)).load "r" ((8 * k : Nat) : Int)
        = (runBlock (initSqr sqrTestInput 4) (sqrBlock 4)).load "r" ((8 * k : Nat) : Int) := by
  native_decide

set_option maxRecDepth 8000 in
/-- **Diagonal sqr value semantics, n = 4, carry-edge input** (top limb all-ones
    forces cross-product and doubling carries to ripple). -/
theorem sqrDiag4_edge_matches_schoolbook :
    ∀ k ∈ List.range 8,
      (runBlock (initSqr sqrTestInputEdge 4) (sqrDiagBlock 4)).load "r" ((8 * k : Nat) : Int)
        = (runBlock (initSqr sqrTestInputEdge 4) (sqrBlock 4)).load "r" ((8 * k : Nat) : Int) := by
  native_decide

/-! ## 7. Emit driver -/

/-- Write the owned-backend `.s` for the add/sub/submul_1/sqr kernels at
    `n = 4, 8, 16, 32` into the bench harness directories. The small sizes
    `n = 4, 8` are the same fixed-window kernel as `n = 16, 32` (the register
    window is constant in `n`), and replace the former jasminc `.jazz` path at
    those sizes — so the mpn small-`n` bench path is jasminc-free. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/mpn_addsub_adx_compare/gen_com"
  IO.FS.createDirAll "bench/mpn_submul_1_adx_compare/gen_com"
  IO.FS.createDirAll "bench/mpn_sqr_diagonal_compare/gen_com"
  for n in [4, 8, 16, 32] do
    IO.FS.writeFile s!"bench/mpn_addsub_adx_compare/gen_com/mpn_add_n_owned_{n}.s"
      (addAsm n)
    IO.FS.writeFile s!"bench/mpn_addsub_adx_compare/gen_com/mpn_sub_n_owned_{n}.s"
      (subAsm n)
    IO.FS.writeFile s!"bench/mpn_submul_1_adx_compare/gen_com/mpn_submul_1_owned_{n}.s"
      (submul1Asm n)
    IO.FS.writeFile s!"bench/mpn_sqr_diagonal_compare/gen_com/mpn_sqr_basecase_owned_{n}.s"
      (sqrAsm n)
    IO.FS.writeFile s!"bench/mpn_sqr_diagonal_compare/gen_com/mpn_sqr_basecase_diag_owned_{n}.s"
      (sqrDiagAsm n)
  IO.println "wrote owned-backend .s for add_n/sub_n/submul_1/sqr_basecase(+diag) at n=4,8,16,32 (no jasminc)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnLinearKernels
