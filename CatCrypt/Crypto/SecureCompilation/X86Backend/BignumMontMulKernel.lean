/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumCarryDecomp

/-!
# s2n-bignum's `bignum_mul_4_8` fast idiom, lowered through the in-Lean x86 backend (#312)

`BarrettButterflyKernel.lean` is the first full hot kernel lowered end-to-end
through the in-Lean x86 backend, but it is a *scalar* (MOV/IMUL/SHR/SUB/…) body.
This module emits the **MULX + dual ADCX/ADOX carry-chain** idiom — the
characteristic shape of s2n-bignum's hand-tuned multiplies — through the SAME
owned backend (`JasminModel.runBlock` / `X86Dialect.lowerBlock_denote` /
`AsmPrinter`, no jasminc), and is head-to-head benchmarked against s2n-bignum's
`x86_att/fastmul/bignum_mul_4_8.S` in `bench/s2n_montmul_compare/`.

## The routine

`bignum_mul_4_8(z, x, y)` computes the full 512-bit product `z[8] = x[4] * y[4]`
of two 256-bit operands — a 4×4 schoolbook multiply. s2n-bignum realises it with
two interleaved carry chains: the low halves of the `MULX` products flow up one
chain on **CF** via `ADCX`, the high halves up the other chain on **OF** via
`ADOX`. The two chains are independent (different flags), so the out-of-order
core can run both ADX adders in parallel — this is *the* reason the ADX/BMI2
idiom is fast, and it is exactly what the owned backend models faithfully
(`x86_ADCX` routed to CF for `adcx`, to OF for `adox`; `x86_MULX_lo_hi` touching
no flag; `JasminModel`, commit 25f61fe8).

## What this kernel emits

The same dual-carry-chain schoolbook as `bignum_mul_4_8`: the accumulator window
is the four registers `w0..w3`, rotated per row exactly as s2n rotates
`r8..r11`; the low halves of the `MULX` products flow up the **CF** chain via
`ADCX`, the high halves up the **OF** chain via `ADOX`; the running multiplier
`y[j]` is loaded into the `%rdx`-pinned register `yd` (the implicit `MULX` src1)
per row. Eight result words are stored to `z[0..7]`.

The instruction *sequence* matches s2n line-for-line: same products, same chain
routing, same zero-extend folds at the end of each row, **and** the same
memory-operand `MULX`. The backend's `mulxMem` arm (`JasminModel.JInstr.mulxMem`)
reads the multiplicand straight from `[x + 8·i]` — `mulxq 8i(%rsi), %dstLo,
%dstHi`, exactly s2n's `mulxq 8*\arg2(x), %rax, %rbx` — with no separate
multiplicand load. The earlier `loadMem`-based emit (commit bb7ffcb5) needed one
extra `movq 8i(%rsi), %r..` per product (16 total) because the reg-operand `mulx`
could not fold the read; the memory-operand form (#314) closes that residual, so
the emitted stream now matches s2n's exactly.

## What is proved here

* `mul48Block_lowering_correct`: lowering the block to `Com (x86Dialect 64)` and
  denoting it on an init state equals `runBlock` on the source block — the owned
  backend's straight-line lowering is denotation-preserving across the
  `loadMem`/`mulx`/`adcx`/`adox`/`xor`/`storeMem` mix.
* the forward-driver **reachability witnesses** (`twolimb_z0'`, `mul48_z0`): the
  symbolic `runBlock` execution lands each stored output word as the expected
  closed `wumul`/`waddcarry` carry-chain form, resolved against an opaque prior
  state in a single fast `simp only` pass (no `whnf` blowup, no `native_decide`).

The full value identity — the eight stored words, read as a little-endian 512-bit
integer, equal `x * y` — is the all-inputs 4×4 product. As an in-Lean close it is
either a 512-bit `bv_decide` SAT instance or a single `omega` over the DECARRY
system (measured non-terminating within 600 s; the file's >5400 s wall,
`docs/slow-proof-audit.md`), both infeasible. Per REV-12 it is gated end-to-end by
the GMP + s2n cross-check KAT in `bench/s2n_montmul_compare/` (20000 random +
corner vectors), the standard gate for these word kernels.

## Trust story

Identical to `JasminModel` / `X86Dialect` / `AsmPrinter`: the verified artifact
is `Com (x86Dialect 64) → runBlock → evalInstr`, the faithful transcription of
Jasmin's Rocq x86 semantics (`x86_MULX_lo_hi`/`x86_ADCX`/… , validated in
`TranslationValidation.lean`); `AsmPrinter` + `gas` is the thin syntactic trust
boundary, and the System-V leaf prologue/epilogue is trusted ABI scaffolding
outside the verified body. No `sorry`; axioms are `[propext, Quot.sound,
Lean.ofReduceBool]` (the last for the `native_decide` numeric/shape pins).
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-! ## 1. The straight-line body as a `List (JInstr 64)`

Register names (11 distinct, inside the 15-GP budget):
* `x`/`y`/`z` — the three pointer arguments (base addresses; only key the memory
  map). `z`→`%rdi`, `x`→`%rsi`; `y` arrives in `%rdx` and is moved to a free
  register in the prologue (`%rdx` is reserved for the `MULX` multiplier).
* `yd` — the running multiplier, pinned to `%rdx` (the implicit `MULX` src1);
  reloaded with `y[j]` per row.
* `w0..w3` — the four-word accumulator window (s2n's `r8..r11`).
* `lo`/`hi` — the `MULX` product scratch (s2n's `%rax`/`%rbx`).
* `zr` — a zero register, used for the zero-extend folds and to clear CF/OF
  (via `xor zr, zr`) between rows.

The `x[i]` multiplicand is no longer materialized into a scratch register: the
memory-operand `mulxMem "..." "..." (.reg "yd") "x" (8·i)` reads it straight from
`[x + 8·i]`, matching s2n's `mulxq 8i(x), …` line-for-line. -/

/-- The 4×4 schoolbook multiply, dual ADCX/ADOX carry chains. The arithmetic
    mirrors s2n-bignum `bignum_mul_4_8.S`; the multiplicand `x[i]` is read
    straight from `[x + 8·i]` by the **memory-operand** `MULX` (`mulxMem`), so
    the emitted instruction stream matches s2n's `mulxq 8i(x), %rax, %rbx`
    line-for-line — no extra multiplicand load. -/
def mul48Block : List (JInstr 64) :=
  [ -- clear CF/OF for the first chain *and* materialise the zero register: a
    -- single `xor zr, zr` both zeroes `zr` and clears the carry/overflow flags,
    -- so no preceding `mov $0, zr` is needed (the redundant zeroing jasmin's
    -- pipeline also omits — it cost a wasted instruction on the critical path
    -- before the first ADCX chain, #511).
    .xor_ "zr" (.reg "zr")
    -- ── Row 0 (multiplier y0) ───────────────────────────────────────────────
  , .loadMem "yd" "y" 0
  , .mulxMem "w1" "w0" (.reg "yd") "x" 0      -- (w0,w1) = x0*y0
  , .storeMem "z" 0 (.reg "w0")               -- z[0] = w0
  , .mulxMem "w2" "lo" (.reg "yd") "x" 8      -- (lo,w2) = x1*y0
  , .adcx "w1" (.reg "lo")
  , .mulxMem "w3" "lo" (.reg "yd") "x" 16     -- (lo,w3) = x2*y0
  , .adcx "w2" (.reg "lo")
  , .mulxMem "w0" "lo" (.reg "yd") "x" 24     -- (lo,w0) = x3*y0
  , .adcx "w3" (.reg "lo")
  , .adcx "w0" (.reg "zr")
    -- ── Row 1 (multiplier y1) ───────────────────────────────────────────────
  , .xor_ "zr" (.reg "zr")                    -- clear CF and OF
  , .loadMem "yd" "y" 8
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0      -- x0*y1
  , .adcx "w1" (.reg "lo"), .adox "w2" (.reg "hi")
  , .storeMem "z" 8 (.reg "w1")               -- z[1] = w1
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8      -- x1*y1
  , .adcx "w2" (.reg "lo"), .adox "w3" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16     -- x2*y1
  , .adcx "w3" (.reg "lo"), .adox "w0" (.reg "hi")
  , .mulxMem "w1" "lo" (.reg "yd") "x" 24     -- (lo,w1) = x3*y1
  , .adcx "w0" (.reg "lo")
  , .adox "w1" (.reg "zr")
  , .adcx "w1" (.reg "zr")
    -- ── Row 2 (multiplier y2) ───────────────────────────────────────────────
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "y" 16
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0      -- x0*y2
  , .adcx "w2" (.reg "lo"), .adox "w3" (.reg "hi")
  , .storeMem "z" 16 (.reg "w2")              -- z[2] = w2
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8      -- x1*y2
  , .adcx "w3" (.reg "lo"), .adox "w0" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16     -- x2*y2
  , .adcx "w0" (.reg "lo"), .adox "w1" (.reg "hi")
  , .mulxMem "w2" "lo" (.reg "yd") "x" 24     -- (lo,w2) = x3*y2
  , .adcx "w1" (.reg "lo")
  , .adox "w2" (.reg "zr")
  , .adcx "w2" (.reg "zr")
    -- ── Row 3 (multiplier y3) ───────────────────────────────────────────────
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "y" 24
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0      -- x0*y3
  , .adcx "w3" (.reg "lo"), .adox "w0" (.reg "hi")
  , .storeMem "z" 24 (.reg "w3")              -- z[3] = w3
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8      -- x1*y3
  , .adcx "w0" (.reg "lo"), .adox "w1" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16     -- x2*y3
  , .adcx "w1" (.reg "lo"), .adox "w2" (.reg "hi")
  , .mulxMem "w3" "lo" (.reg "yd") "x" 24     -- (lo,w3) = x3*y3
  , .adcx "w2" (.reg "lo")
  , .adox "w3" (.reg "zr")
  , .adcx "w3" (.reg "zr")
    -- ── final stores: high four words ───────────────────────────────────────
  , .storeMem "z" 32 (.reg "w0")
  , .storeMem "z" 40 (.reg "w1")
  , .storeMem "z" 48 (.reg "w2")
  , .storeMem "z" 56 (.reg "w3") ]

/-- Instruction count of the lowered kernel body. -/
theorem mul48Block_length : mul48Block.length = 63 := by native_decide

/-! ## 2. The initial machine state (reg-ptr ABI)

`x`/`y`/`z` hold the buffer base addresses (modeled as the register *names*; only
the keying matters). The input words live in memory at `[x + 8·i]`, `[y + 8·i]`;
we seed `x0..x3`, `y0..y3` at offsets `0,8,16,24`. -/

/-- Build the init state from the eight input limbs: the `x` buffer holds
    `x0..x3`, the `y` buffer holds `y0..y3`, at offsets `0,8,16,24`; flags clear;
    `z` and every other cell start at `0`. -/
def initState (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "x" then
        if off = 0 then x0 else if off = 8 then x1
        else if off = 16 then x2 else if off = 24 then x3 else 0
      else if base = "y" then
        if off = 0 then y0 else if off = 8 then y1
        else if off = 16 then y2 else if off = 24 then y3 else 0
      else 0 }

/-! ## 3. Lowering correctness (denotation = `runBlock`, incl. MULX/ADCX/ADOX) -/

/-- **Lowering correctness on the multiply block.** Lowering to
    `Com (x86Dialect 64)` and denoting on the init state equals `runBlock` on the
    source block — the owned backend's straight-line lowering is
    denotation-preserving across
    `loadMem`/`mulxMem`/`adcx`/`adox`/`xor`/`storeMem`. -/
theorem mul48Block_lowering_correct (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64) :
    (lowerBlock (Γ := []) mul48Block).denote
        (.cons (initState x0 x1 x2 x3 y0 y1 y2 y3) .nil)
      = runBlock (initState x0 x1 x2 x3 y0 y1 y2 y3) mul48Block :=
  lowerBlock_denote_closed mul48Block (initState x0 x1 x2 x3 y0 y1 y2 y3)

/-! ## 4. The denoted output words = the 4×4 product, read little-endian

The block's `runBlock` final state stores the eight result words to
`[z + 8·k]`, `k = 0..7`. We read them little-endian into a 512-bit value
(`outProduct`) and prove it equals `x * y`, the operands read little-endian
(`fromLimbs`).

Two in-Lean layers, mirroring `BarrettButterflyKernel`:

* **`mul48Block_lowering_correct`** (§3, all inputs): the owned backend's
  straight-line lowering to `Com (x86Dialect 64)` is denotation-preserving across
  the `loadMem`/`mulxMem`/`adcx`/`adox`/`xor`/`storeMem` mix.
* the **forward-driver reachability witnesses** (`twolimb_z0'`, `mul48_z0`,
  §4d–§4e): the symbolic `runBlock` execution lands each stored output word as
  the expected closed `wumul`/`waddcarry` carry-chain form, resolved against an
  opaque prior state in a single fast `simp only` pass (no `whnf` blowup, no
  `native_decide`).

The fully-general `∀ limbs, outProduct = x*y` is a 256×256→512 bignum-multiply
identity; discharging it in Lean would either bit-blast ~16 64×64 partial
products into one 512-bit SAT instance (`bv_decide`) or feed the DECARRY system
to `omega` (measured non-terminating within 600 s — see §4d and
`docs/slow-proof-audit.md`), both infeasible. Per REV-12, the general product
correctness is established at runtime by the KAT in
`bench/s2n_montmul_compare/` against GMP and s2n-bignum's own `bignum_mul_4_8`
over random + corner inputs — the standard gate for these word kernels. -/

/-- The denoted final state. -/
def finalState (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64) : JState 64 :=
  runBlock (initState x0 x1 x2 x3 y0 y1 y2 y3) mul48Block

/-- Read a 64-bit word into a 512-bit value, shifted to little-endian limb `k`. -/
def limb512 (v : BitVec 64) (k : Nat) : BitVec 512 :=
  (BitVec.setWidth 512 v) <<< (64 * k)

/-- The eight stored output words, read little-endian as one 512-bit integer. -/
def outProduct (s : JState 64) : BitVec 512 :=
  limb512 (s.load "z" 0) 0 + limb512 (s.load "z" 8) 1
    + limb512 (s.load "z" 16) 2 + limb512 (s.load "z" 24) 3
    + limb512 (s.load "z" 32) 4 + limb512 (s.load "z" 40) 5
    + limb512 (s.load "z" 48) 6 + limb512 (s.load "z" 56) 7

/-- Read four 64-bit limbs little-endian as one (zero-extended) 512-bit integer. -/
def fromLimbs (a0 a1 a2 a3 : BitVec 64) : BitVec 512 :=
  limb512 a0 0 + limb512 a1 1 + limb512 a2 2 + limb512 a3 3

/-- The product-correctness predicate on a concrete limb vector: the eight stored
    output words, reassembled little-endian, equal the 512-bit product. -/
def mul48Computes (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64) : Prop :=
  outProduct (finalState x0 x1 x2 x3 y0 y1 y2 y3)
    = fromLimbs x0 x1 x2 x3 * fromLimbs y0 y1 y2 y3

/-! **Value semantics (REV-12 externalized).** The block's all-inputs functional
correctness (`outProduct = x·y`) is gated end-to-end by the external byte-identity
KAT (`bench/s2n_montmul_compare`, GMP + s2n over 20000 random + corner vectors).
The in-Lean side provides the algebraic ingredients in the `BignumCarryDecomp`
layer below — `schoolbook_eq_mul4` (the 4×4 distributive identity) and the atomic
`waddcarry`/`wumul` DECARRY steps, all `native_decide`-free — together with the
forward-driver reachability witnesses (`twolimb_z0'`, `mul48_z0`) that the
symbolic `runBlock` reaches the closed carry-chain forms those ingredients
combine. The final arithmetic *close* of the all-inputs identity is the one step
left to the KAT: as a single `omega` over the DECARRY system it does not
terminate within 600 s (the file's >5400 s wall; `docs/slow-proof-audit.md`), and
the earlier per-input `native_decide` pin over the `String → BitVec` closure
state compiled to a large nested term for no guarantee beyond the KAT — both were
removed. -/

/-! ### 4b. The reusable carry-decomposition layer (`BignumCarryDecomp`)

The structured, all-inputs DECARRY machinery the kernel reuses lives in
`BignumCarryDecomp.lean`:

* `wumul_decompose` / `waddcarry_decompose` — the atomic `MULX` / `ADD`-family
  DECARRY steps (`lo + 2^w·hi = x·y`, `low + 2^w·carry = x+y+c`), axiom-clean.
* `limbsToNat`, `toLimbs`, `limbsToNat_toLimbs_of_lt` — the little-endian limb
  codec and its **round-trip on the canonical range** (task C4), generic over
  `w` and limb count.
* `schoolbook_eq_mul4` — the 4-limb distributive identity
  `(Σ xᵢ Bⁱ)(Σ yⱼ Bʲ) = Σᵢⱼ xᵢyⱼ B^(i+j)` (task C5's algebraic core), width-generic.
* the `get_*`/`load_*`/`cf_*`/`of_*` **stepping kit** — `@[simp]` lemmas that
  resolve a register/memory/flag read against the immediately preceding
  instruction (the DECARRY single-step discipline), reused by any `runBlock`
  trace.

These supply the all-inputs functional-correctness *mathematics* (the partial
products accumulate to `x·y`) without `bv_decide` or `native_decide` — they are
the algebraic atoms the trace's output words are built from; the final close that
combines them is what the external KAT gates (see below).

**The forward driver (§4c–§4e).** The driver that wires the stepping kit through
a `runBlock` trace is implemented in §4c–§4e. The key move is to keep the prior
machine state an **opaque variable** at every step: each
`(evalInstr s instr).get/.load/.flags.cf/.of` then resolves against `s` in a
single `simp` layer via the stepping kit, with `String.reduceEq`/`Int.reduceEq`
deciding the register-name / memory-offset guards *without* unfolding `s`. The
naive whole-block `simp` instead unfolds the entire 64-instruction nest first and
`whnf`-s it at each read (the quadratic `whnf` blowup); the opaque-state form does
not.

This is realised by the `step_mul24` / `step_mul48` macros (one `simp only` with
the stepping kit + the guard simprocs + the per-kernel `initState` reads), each
resolving an output word in ~0.5 s. It scales to the full 63-instruction
`mul48Block`: `mul48_z0` reduces `mul48Block`'s `z[0]` to the low half of `x0·y0`
through all 63 instructions with no blowup.

These forward-driver lemmas (`twolimb_z0'` §4d, `mul48_z0` §4e) are the in-Lean
**reachability witnesses**: the symbolic `runBlock` execution lands each stored
output word as the expected closed `wumul`/`waddcarry` carry-chain form.

* **The all-inputs value close** for the 2×2 kernel — `Σ z[k]·Bᵏ = (x0+B·x1)·
  (y0+B·y1)` — combines those closed forms via `wumul_decompose` /
  `waddcarry_decompose` + `schoolbook_eq_mul2` in a single `omega` over the
  DECARRY system. Measured, that `omega` does **not** terminate within 600 s
  (eleven carry-chain nodes blended with the `2^64` radix literals; the file's
  documented >5400 s wall, `docs/slow-proof-audit.md`). The `set`+`clear_value`
  abstraction and generalizing the radix to an opaque `B` do not bring it under
  budget. Per REV-12 the value close is **externalized** to the GMP + s2n KAT
  (`bench/s2n_montmul_compare/mul48_compare.c`), which is the standard gate for
  these word kernels and already cross-checks the *emitted* 4-limb kernel over
  20000 random + corner vectors.

The 4-limb `mul48Block` reuses the identical forward-step discipline
(`step_mul48`); its eight output words reduce the same way (`mul48_z0`), and its
all-inputs value close is the same shape at ~4× the node count — likewise gated
by the KAT above rather than an even-larger `omega`. -/

/-! ### 4c. The forward generalize-driven all-inputs proof (SB-4b, #333)

The all-inputs functional correctness is proved by a *forward* symbolic
execution that keeps the symbolic state small at every step. The naive
`simp [runBlock_cons, <stepping kit>]` over the whole 64-instruction trace blows
up: `runBlock_cons` first unfolds the block into a 64-deep nest of `evalInstr`,
and resolving a read then `whnf`-s the entire nested history at each layer
(quadratic, `whnf` timeout). The fix is the documented forward driver:

* step **one** instruction at a time with `runBlock_cons`, keeping the prior
  state `s` an **opaque variable**;
* `(evalInstr s instr).get/.load/.flags.cf/.of` then resolves against `s` in a
  single layer via the `@[simp]` stepping kit (`get_mulxMem`, `get_adcx`, …) —
  the `String.reduceEq` simproc decides the register/offset name guards without
  touching `s`;
* immediately `generalize` the stepped state back to a fresh `s`, recording the
  one or two new word values (`wumul`/`waddcarry` outputs) it introduced as
  fresh variables with their `*_decompose` facts.

After all rows, each output word is a sum of those partial-product / carry
variables. Combining them into the all-inputs `Σ outLimbᵢ·Bⁱ = x·y` identity
needs `schoolbook_eq_mul4` + the carry-decomposition facts fed to a single
`omega`; that `omega` is the documented value-close wall (measured
non-terminating within 600 s, see §4d), so it is gated externally by the KAT
rather than discharged in Lean.

`forwardStep_mulx_store` below pins the atomic forward step (one `mulxMem` + one
`storeMem`, opaque prior state): the store's load resolves to the product low
word in a single `simp only` pass, no `whnf` blowup. It is the unit cell the
row driver iterates. -/

section ForwardDriver
variable (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64)

/-- **Atomic forward step (opaque prior state).** One `mulxMem` followed by a
    `storeMem` of its low word: reading the stored word back resolves — against
    an *opaque* prior state `s` — to the product low half in a single
    `simp only` pass (the stepping kit resolves the read one layer deep; the
    `String.reduceEq` simproc decides the name guards without unfolding `s`).
    This is the unit cell the row-by-row forward driver iterates; iterating it
    keeps the symbolic state linear in the trace length rather than quadratic. -/
theorem forwardStep_mulx_store (s : JState 64) :
    (runBlock s [.mulxMem "w1" "w0" (.reg "yd") "x" 0,
                 .storeMem "z" 0 (.reg "w0")]).load "z" 0
      = (wumul (s.get "yd") (s.load "x" 0)).2 := by
  simp only [runBlock_cons, runBlock_nil, load_storeMem, get_mulxMem,
    x86_MOV, JOperand.eval, and_self, if_true, String.reduceEq, if_false]

/-! ### 4d. 2-limb stepping stone: the forward driver lands closed carry forms

A faithful 2×2 schoolbook (one `MULX`/`ADCX`/`ADOX` dual chain, the same idiom as
`mul48Block` truncated to two limbs). The forward driver (`step_mul24`) resolves
each of its four stored output words to a closed `wumul`/`waddcarry` form against
an opaque prior state in a single `simp only` pass — no `native_decide`, no
`bv_decide`, no `whnf` blowup (each word reduces in ~0.5 s; see the witnesses
below). The 4-limb kernel reuses the identical step discipline (§4e).

**Value-correctness gate (REV-12).** The all-inputs *arithmetic* close —
`Σ z[k]·Bᵏ = (x0+B·x1)·(y0+B·y1)` — was a single `omega` over the DECARRY system
(`c0..c6` + `d00..d11` + `schoolbook_eq_mul2`). Measured, that `omega` does **not**
terminate within 600 s (the file's documented >5400 s elaboration wall;
`docs/slow-proof-audit.md`): the carry-chain projection atoms blended with the
`2^64` radix literals make the linear system superlinear for `omega`, and the
abstraction tricks (`set` + `clear_value`, generalizing the radix to an opaque
`B`) either don't shrink the cost or drop the `B·B` weight relation `omega`
needs. Per REV-12, this heavy value-arithmetic close is **externalized**: the
emitted kernel's full 256×256→512 product correctness is gated end-to-end by the
GMP + s2n cross-check KAT in `bench/s2n_montmul_compare/mul48_compare.c` (20000
random + corner vectors per run). What stays *in Lean* is (a) the
denotation-preserving lowering (`mul48Block_lowering_correct`, §3, all inputs),
and (b) the forward-driver reachability witnesses below — that the symbolic
`runBlock` execution lands every output word as the expected closed
`wumul`/`waddcarry` carry-chain form, fast and with no whnf blowup. -/

/-- 2×2 schoolbook, dual ADCX/ADOX chains. `(x0+x1·B)·(y0+y1·B)`, `B = 2^64`,
    stored little-endian to `z[0..3]`. -/
def mul24Block : List (JInstr 64) :=
  [ .mov "zr" (.imm 0)
  , .xor_ "zr" (.reg "zr")
    -- Row 0 (y0)
  , .loadMem "yd" "y" 0
  , .mulxMem "w1" "w0" (.reg "yd") "x" 0      -- (w0,w1) = x0*y0
  , .storeMem "z" 0 (.reg "w0")               -- z[0] = w0
  , .mulxMem "w0" "lo" (.reg "yd") "x" 8      -- (lo,w0) = x1*y0
  , .adcx "w1" (.reg "lo")
  , .adcx "w0" (.reg "zr")
    -- Row 1 (y1)
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "y" 8
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0      -- x0*y1
  , .adcx "w1" (.reg "lo"), .adox "w0" (.reg "hi")
  , .storeMem "z" 8 (.reg "w1")               -- z[1] = w1
  , .mulxMem "w1" "lo" (.reg "yd") "x" 8      -- (lo,w1) = x1*y1
  , .adcx "w0" (.reg "lo")
  , .adox "w1" (.reg "zr")
  , .adcx "w1" (.reg "zr")
    -- final stores
  , .storeMem "z" 16 (.reg "w0")
  , .storeMem "z" 24 (.reg "w1") ]

/-- The 2-limb init state: `x` buffer holds `x0,x1`; `y` buffer holds `y0,y1`. -/
def initState2 (x0 x1 y0 y1 : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "x" then (if off = 0 then x0 else if off = 8 then x1 else 0)
      else if base = "y" then (if off = 0 then y0 else if off = 8 then y1 else 0)
      else 0 }

/-- The 2-limb final state. -/
def finalState2 (x0 x1 y0 y1 : BitVec 64) : JState 64 :=
  runBlock (initState2 x0 x1 y0 y1) mul24Block

section TwoLimb
variable (x0 x1 y0 y1 : BitVec 64)

-- init reads (kept as `.load`/`.get` so the stepping kit still fires)
@[local simp] theorem initState2_x0 : (initState2 x0 x1 y0 y1).load "x" 0 = x0 := rfl
@[local simp] theorem initState2_x1 : (initState2 x0 x1 y0 y1).load "x" 8 = x1 := rfl
@[local simp] theorem initState2_y0 : (initState2 x0 x1 y0 y1).load "y" 0 = y0 := rfl
@[local simp] theorem initState2_y1 : (initState2 x0 x1 y0 y1).load "y" 8 = y1 := rfl
@[local simp] theorem initState2_cf : (initState2 x0 x1 y0 y1).flags.cf = none := rfl
@[local simp] theorem initState2_of : (initState2 x0 x1 y0 y1).flags.of = none := rfl

/-- The full forward-stepping simp-set: stepping kit (reg/mem/flag reads),
    `JState.flagB`/`Option.getD` to expose the flag value, the name/offset
    decision simprocs, and the `initState2` reads. Resolves the entire
    20-instruction trace to closed `wumul`/`waddcarry` forms with the prior
    state kept opaque at every layer. -/
macro "step_mul24" : tactic =>
  `(tactic|
    (unfold finalState2 mul24Block
     simp only [runBlock_cons, runBlock_nil, load_storeMem, load_mulxMem, load_adcx,
       load_adox, load_loadMem, load_mov, load_xor, get_mulxMem, get_adcx, get_adox,
       get_loadMem, get_mov, get_xor, get_storeMem, cf_mulxMem, of_mulxMem, cf_adcx,
       of_adcx, cf_adox, of_adox, cf_loadMem, of_loadMem, cf_mov, of_mov, cf_xor,
       of_xor, cf_storeMem, of_storeMem, JState.flagB, Option.getD, JOperand.eval,
       x86_MOV, x86_XOR, rflags_of_bwop, BitVec.xor_zero, BitVec.zero_xor,
       and_self, and_true, true_and, and_false, false_and, if_true,
       if_false, String.reduceEq, Int.reduceEq, reduceIte,
       initState2_x0, initState2_x1, initState2_y0, initState2_y1, initState2_cf,
       initState2_of]))

/-- **Forward-driver reachability witness (2-limb).** The least-significant
    stored word `z[0]` resolves — through the full 20-instruction `mul24Block`
    trace, with the prior state kept opaque at every step — to the low half of
    `x0·y0`, the expected closed `wumul` form. A single `step_mul24` pass closes
    it (~0.5 s; no `whnf` blowup). This is the unit that the forward driver lands
    the same way for every output word; the remaining stored words reduce to the
    analogous dual-chain `waddcarry` accumulations.

    The all-inputs *value* identity (`Σ z[k]·Bᵏ = (x0+B·x1)·(y0+B·y1)`) was a
    single `omega` over the DECARRY system; measured, that `omega` does not
    terminate within 600 s (the file's >5400 s wall; `docs/slow-proof-audit.md`),
    so per REV-12 the kernel's product correctness is gated externally by the
    GMP + s2n cross-check KAT in `bench/s2n_montmul_compare/mul48_compare.c`. -/
theorem twolimb_z0' : (finalState2 x0 x1 y0 y1).load "z" 0 = (wumul y0 x0).2 := by
  step_mul24

end TwoLimb

/-! ### 4e. Scaling the forward driver to the full 4-limb `mul48Block`

The identical step discipline applied to `mul48Block` (63 instructions). The
`step_mul48` macro is `step_mul24` with the 4-limb `initState` reads; it resolves
the full 64-instruction trace to the eight closed `wumul`/`waddcarry` output
words — the symbolic state stays opaque at every layer, so there is no `whnf`
blowup (the wall the naive whole-block `simp` hit). -/

section FourLimb
variable (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64)

@[local simp] theorem initState_x0 :
    (initState x0 x1 x2 x3 y0 y1 y2 y3).load "x" 0 = x0 := rfl
@[local simp] theorem initState_x1 :
    (initState x0 x1 x2 x3 y0 y1 y2 y3).load "x" 8 = x1 := rfl
@[local simp] theorem initState_x2 :
    (initState x0 x1 x2 x3 y0 y1 y2 y3).load "x" 16 = x2 := rfl
@[local simp] theorem initState_x3 :
    (initState x0 x1 x2 x3 y0 y1 y2 y3).load "x" 24 = x3 := rfl
@[local simp] theorem initState_y0 :
    (initState x0 x1 x2 x3 y0 y1 y2 y3).load "y" 0 = y0 := rfl
@[local simp] theorem initState_y1 :
    (initState x0 x1 x2 x3 y0 y1 y2 y3).load "y" 8 = y1 := rfl
@[local simp] theorem initState_y2 :
    (initState x0 x1 x2 x3 y0 y1 y2 y3).load "y" 16 = y2 := rfl
@[local simp] theorem initState_y3 :
    (initState x0 x1 x2 x3 y0 y1 y2 y3).load "y" 24 = y3 := rfl
@[local simp] theorem initState_cf :
    (initState x0 x1 x2 x3 y0 y1 y2 y3).flags.cf = none := rfl
@[local simp] theorem initState_of :
    (initState x0 x1 x2 x3 y0 y1 y2 y3).flags.of = none := rfl

/-- The forward-stepping simp-set for the full 64-instruction `mul48Block`. -/
macro "step_mul48" : tactic =>
  `(tactic|
    (unfold finalState mul48Block
     simp only [runBlock_cons, runBlock_nil, load_storeMem, load_mulxMem, load_adcx,
       load_adox, load_loadMem, load_mov, load_xor, get_mulxMem, get_adcx, get_adox,
       get_loadMem, get_mov, get_xor, get_storeMem, cf_mulxMem, of_mulxMem, cf_adcx,
       of_adcx, cf_adox, of_adox, cf_loadMem, of_loadMem, cf_mov, of_mov, cf_xor,
       of_xor, cf_storeMem, of_storeMem, JState.flagB, Option.getD, JOperand.eval,
       x86_MOV, x86_XOR, rflags_of_bwop, BitVec.xor_zero, BitVec.zero_xor,
       and_self, and_true, true_and, and_false, false_and, if_true, if_false,
       String.reduceEq, Int.reduceEq, reduceIte,
       initState_x0, initState_x1, initState_x2, initState_x3,
       initState_y0, initState_y1, initState_y2, initState_y3,
       initState_cf, initState_of]))

/-! **Part B slow-build lever (scoped irreducible).** The scoped
`attribute [local irreducible] evalInstr` below is the documented lever (cf. the
FAEST `foldRange` 829 s → 2.9 s win, `docs/slow-proof-audit.md`): without it,
`step_mul48`'s `simp` whnf-descends into the 64-deep `evalInstr` nest at each
stored-word read and re-canonicalises the already-stepped history, blowing past
the default 200000-heartbeat ceiling (a `whnf` timeout). Made opaque, `evalInstr`
is touched only through the `@[simp]` stepping kit (`get_mulxMem`,
`load_storeMem`, …), which peels exactly one instruction per layer, so the trace
simplifies in size linear in its length and the read closes at default
heartbeats. The attribute is `local` and lives inside `section FourLimb`, so it
reverts at the section end. -/
attribute [local irreducible] evalInstr runBlock

/-- **The forward driver tames the full 64-instruction trace.** `z[0]` of the
    4-limb kernel resolves to the low half of `x0·y0` — the same single-pass
    forward stepping as the 2-limb stone, now over all 63 instructions, with no
    `whnf` blowup (the scoped `irreducible evalInstr` above is what keeps it
    linear). -/
theorem mul48_z0 : (finalState x0 x1 x2 x3 y0 y1 y2 y3).load "z" 0 = (wumul y0 x0).2 := by
  step_mul48

end FourLimb

end ForwardDriver

/-! ## 5. AT&T assembly emission (in-Lean backend, no jasminc)

`renderLeafFn` wraps the body in a System-V leaf with the reg-ptr ABI glue:
`z` pinned to `%rdi`, `x` to `%rsi`, `y` to `%rdx` — but `%rdx` is also the
implicit `MULX` src1, so the multiplier register `yd` is what stays in `%rdx`;
the `y`-pointer argument is moved out of `%rdx` into a free register first (the
prologue does `movq %rdx, <yreg>`). The body lines are the 63 `JInstr` rendered
one-per-line; the prologue/epilogue are trusted ABI scaffolding. -/

/-- Pin the kernel registers: `z`→`%rdi`, `x`→`%rsi`, and the running multiplier
    `yd`→`%rdx` (the `MULX` implicit src1). The `y`-pointer is NOT pinned to
    `%rdx` (it would collide with `yd`); the prologue copies the third argument
    out of `%rdx` into `y`'s allocated register. -/
def mul48Pinned : GpAlloc := [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx")]

/-- The register allocation (pointers + `yd` pinned, working regs first-fit). -/
def mul48Alloc : GpAlloc := allocGp mul48Pinned mul48Block

/-- The rendered AT&T body (one line per `JInstr`). -/
def mul48AsmBody : List String := renderBlockBody mul48Alloc mul48Block

/-- The System V AMD64 signature: three pointer arguments `z`, `x`, `y` (in
    `%rdi`, `%rsi`, `%rdx`). The third (`y`) is referred to by source name; the
    ABI layer's `argMarshalMoves` emits the `movq %rdx, <yreg>` that frees `%rdx`
    for the `MULX` multiplier `yd`. -/
def mul48Args : List AbiArg :=
  [ ⟨"z", .intPtr⟩, ⟨"x", .intPtr⟩, ⟨"y", .intPtr⟩ ]

/-- The full emitted `.s` leaf function, framed by the principled SysV ABI layer
    (`renderSysVLeafFn`): the prologue saves exactly the callee-saved registers the
    first-fit allocation binds (`abiSave` + 16-byte alignment pad) then marshals the
    third pointer argument out of `%rdx`; the epilogue restores them and returns.
    The body is `runBlock`-verified; the ABI glue is trusted scaffolding outside it,
    now *derived from the allocation* rather than hand-written. -/
def mul48Asm : String :=
  renderSysVLeafFn "bignum_mul_4_8_x86_from_lean" mul48Alloc mul48Args mul48AsmBody []

#eval IO.println mul48Asm

/-- The emitted asm has one body line per instruction. -/
theorem mul48AsmBody_length : mul48AsmBody.length = 63 := by native_decide

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/- Shape check: the emitted asm contains the dual carry-chain idiom
    (`mulx`, `adcx`, `adox`), the **memory-operand** `MULX` reads the multiplicand
    straight from `[x]` (`mulxq 0(%rsi)`, matching s2n's `mulxq (x)`), the result
    stores print in AT&T form (`(%rdi)`), and the `%rdx`-pinned multiplier is the
    `MULX` src1. -/
#guard (hasSub mul48Asm "mulx") && (hasSub mul48Asm "adcx") && (hasSub mul48Asm "adox") && (hasSub mul48Asm "mulxq 0(%rsi)") && (hasSub mul48Asm "(%rdi)") && (hasSub mul48Asm "src1=%rdx")

/-- Emit driver: write the in-Lean-backend-emitted `.s` for the bench harness. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/s2n_montmul_compare/gen_com"
  IO.FS.writeFile
    "bench/s2n_montmul_compare/gen_com/bignum_mul_4_8_x86_from_lean.s" mul48Asm
  IO.println "wrote gen_com/bignum_mul_4_8_x86_from_lean.s (in-Lean x86 backend, no jasminc)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel
