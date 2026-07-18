/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel

/-!
# Curve25519 field-multiply `fe25519_mul`, lowered through the in-Lean x86 backend (#380)

`BignumMontMulKernel.lean` emits the bare 4×4→8 schoolbook (`bignum_mul_4_8`)
through the owned x86 backend (MULX + dual ADCX/ADOX, no jasminc), at s2n parity
on the 256×256→512 multiply. This module composes that schoolbook with the
`2^255 - 19` Solinas reduction to emit the full **Curve25519 field-multiply**
`fe25519_mul(z, x, y) = (x · y) mod p25519`, 4-limb radix-64 (saturated), through
the SAME owned backend.

This isolates HALF (a) of the X25519 self-emit gap (the field-multiply code-gen
quality) from HALF (b) (the Montgomery-ladder-step scheduling/residency): it is
the field-arithmetic kernel that the ladder step calls.

## The routine

`fe25519_mul(z[4], x[4], y[4])`: `z := (x · y) mod (2^255 - 19)`, all operands
4-limb little-endian radix-64. The reference is s2n-bignum's
`x86_att/curve25519/bignum_mul_p25519.S` (HOL-Light–verified), the matching
saturated-4×64 field-mul; the field arithmetic is identical to dalek's serial
`FieldElement51` mul up to representation (5×51 vs 4×64), so the C bench
cross-checks against both.

## What this kernel emits

1. **Schoolbook (the `bignum_mul_4_8` lever):** the same dual-carry-chain 4×4
   schoolbook as `BignumMontMulKernel.mul48Block` — low halves of the `MULX`
   products up the **CF** chain via `ADCX`, high halves up the **OF** chain via
   `ADOX`, memory-operand `MULX` reading `x[i]` straight from `[x + 8·i]` — but
   the eight product words are kept **register-resident** in `t0..t7` (no
   intermediate stores; the ladder needs the product in registers to fold).

2. **Fused-quotient-estimate Solinas reduce (`2^256 ≡ 38 (mod p)`):** the port
   of s2n-bignum's `bignum_mul_p25519` reduce. Estimate the quotient `q` of the
   `2^255` division from the top of `38·h₃ + l₃`, precompute `19·q`, then fold
   the high half `t0..t3 += 38·(t4..t7)` in a single dual ADCX/ADOX `MULX` pass
   that simultaneously injects the `19·q` correction (one carry chain, no
   separate carry-recapture). A final canonical conditional subtract of `p` —
   amount `= 19` iff the sign bit of `t₃ − (q&1)·2⁶³` is set, else `0`, then
   clear bit 255 — brings the result into `[0, p)`, the canonical residue GMP
   and s2n produce. This replaces the prior straight Solinas fold +
   carry-recapture + two `shr/imul/and` rounds + explicit add-19 subtract (the
   reduce drops from 64 to 39 instructions). It uses only the owned backend's
   modelled instructions (`mulx`/`adcx`/`adox`/`add`/`adc`/`imul`/`shl`/`shr`/
   `sub`/`sbb`/`and`); s2n's `bt`/`lea`/`cmovns`/`btr` are expressed with the
   supported `shr`/`shl`/`imul` + sign-bit-of-difference idiom.

## What is proved here

* `feMulBlock_lowering_correct`: lowering the block to `Com (x86Dialect 64)` and
  denoting it on the init state equals `runBlock` on the source block — the owned
  backend's straight-line lowering is denotation-preserving across the
  full `loadMem`/`mulxMem`/`mulx`/`adcx`/`adox`/`add`/`adc`/`imul`/`shr`/`and`/
  `sbb`/`storeMem` mix (reusing `lowerBlock_denote_closed`).
* `feMul_eval`: on representative limb vectors the symbolic `runBlock` output,
  read little-endian, equals `(x·y) mod p25519` — checked through the full
  `evalInstr`/`wumul`/`waddcarry` chain by `native_decide`. This pins the value
  semantics of the schoolbook + reduction.

The all-inputs `z = (x·y) mod p` identity is the runtime KAT in
`bench/x25519_fieldmul_compare/` against GMP (`mpz` reduction mod p) AND
s2n-bignum's own `bignum_mul_p25519` over fixed + random inputs — the standard
gate for these word kernels (mirrors `bignum_mul_4_8`'s KAT discipline).

## Spec cross-reference (formosa-25519 — agreement on the spec, not a proof port)

The same mathematical fact `(x · y) mod p25519` is *functionally verified* upstream
in formosa-25519:
`proof/crypto_scalarmult/curve25519/amd64/mulx/CorrectnessProof_Mulx.ec`,
`lemma h_mul_rsr_mulx (_f _g : zp) : hoare [M.__mul4_rsr : … ==> inzpRep4 res = _f * _g]`
(with `ph_mul_rsr_mulx` the lossless `phoare` form, and `h_sqr_rr_mulx` / `h_mul_a24_mulx`
the squaring and `·a24` companions). That proof is an EasyCrypt pHoare triple over EC's
own pWhile *extraction of the Jasmin source* `__mul4_rsr` — a different semantic object
from this module's `runBlock`/`evalInstr` x86 machine model. There is **no** mechanized
EasyCrypt→Lean proof transport (Trocq is same-prover; EC has no Lean exporter), so this is
a citation of *spec agreement* only: CatCrypt's `feMul_eval` re-derives the identical
public field-multiply spec `= (x·y) mod p25519` **independently** against its own machine
semantics. It is **not** a proof port and adds **no** axiom/hypothesis — the owned route
stays `#print axioms`-free of any foreign or jasminc obligation. The formosa lemma is the
*peer* functional result; ours is the in-Lean re-proof of the same arithmetic fact.

## Trust story

Identical to `BignumMontMulKernel` / `JasminModel` / `X86Dialect` / `AsmPrinter`:
the verified artifact is `Com (x86Dialect 64) → runBlock → evalInstr`, the
faithful transcription of Jasmin's Rocq x86 semantics; `AsmPrinter` + `gas` is
the syntactic trust boundary, and the System-V leaf prologue/epilogue is trusted
ABI scaffolding outside the verified body. No `sorry`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter

/-! ## 1. The straight-line body as a `List (JInstr 64)`

Register names:
* `x`/`y`/`z` — pointer arguments. `z`→`%rdi`, `x`→`%rsi`; `y` arrives in `%rdx`
  and is moved out (the prologue does `movq %rdx, <yreg>`) so `%rdx` is free for
  the `MULX` multiplier.
* `yd` — the running `MULX` multiplier, pinned to `%rdx`.
* `t0..t7` — the eight schoolbook product words, register-resident.
* `lo`/`hi` — `MULX` product scratch.
* `zr` — a zero register (zero-extend folds and CF/OF clearing), pinned to `%rbp`.
* The reduction's fold-carry / quotient / mask scratch reuses the now-dead
  schoolbook scratch names `lo`/`hi` (no fresh names) to stay within the GP pool.

The schoolbook half is `mul48Block` with the eight final stores replaced by
keeping `t4..t7` (the high half) in registers; the reduction half then folds
them in. -/

/-- The full Curve25519 field-multiply: 4×4 dual-chain schoolbook into eight
    register-resident product words `t0..t7`, then the s2n fused-quotient-estimate
    `2^255-19` reduce — one dual-carry `38·high` fold with the `19·q` quotient
    correction injected in the same pass, and a single canonical conditional
    subtract. -/
def feMulBlock : List (JInstr 64) :=
  [ -- zero register, clear CF/OF for the first chain
    .mov "zr" (.imm 0)
  , .xor_ "zr" (.reg "zr")
    -- ── Schoolbook Row 0 (multiplier y0) ────────────────────────────────────
  , .loadMem "yd" "y" 0
  , .mulxMem "t1" "t0" (.reg "yd") "x" 0      -- (t0,t1) = x0*y0
  , .mulxMem "t2" "lo" (.reg "yd") "x" 8      -- (lo,t2) = x1*y0
  , .adcx "t1" (.reg "lo")
  , .mulxMem "t3" "lo" (.reg "yd") "x" 16     -- (lo,t3) = x2*y0
  , .adcx "t2" (.reg "lo")
  , .mulxMem "t4" "lo" (.reg "yd") "x" 24     -- (lo,t4) = x3*y0
  , .adcx "t3" (.reg "lo")
  , .adcx "t4" (.reg "zr")
    -- ── Row 1 (multiplier y1) ───────────────────────────────────────────────
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "y" 8
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0      -- x0*y1
  , .adcx "t1" (.reg "lo"), .adox "t2" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8      -- x1*y1
  , .adcx "t2" (.reg "lo"), .adox "t3" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16     -- x2*y1
  , .adcx "t3" (.reg "lo"), .adox "t4" (.reg "hi")
  , .mulxMem "t5" "lo" (.reg "yd") "x" 24     -- (lo,t5) = x3*y1
  , .adcx "t4" (.reg "lo")
  , .adox "t5" (.reg "zr")
  , .adcx "t5" (.reg "zr")
    -- ── Row 2 (multiplier y2) ───────────────────────────────────────────────
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "y" 16
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0      -- x0*y2
  , .adcx "t2" (.reg "lo"), .adox "t3" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8      -- x1*y2
  , .adcx "t3" (.reg "lo"), .adox "t4" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16     -- x2*y2
  , .adcx "t4" (.reg "lo"), .adox "t5" (.reg "hi")
  , .mulxMem "t6" "lo" (.reg "yd") "x" 24     -- (lo,t6) = x3*y2
  , .adcx "t5" (.reg "lo")
  , .adox "t6" (.reg "zr")
  , .adcx "t6" (.reg "zr")
    -- ── Row 3 (multiplier y3) ───────────────────────────────────────────────
  , .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "y" 24
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0      -- x0*y3
  , .adcx "t3" (.reg "lo"), .adox "t4" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8      -- x1*y3
  , .adcx "t4" (.reg "lo"), .adox "t5" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16     -- x2*y3
  , .adcx "t5" (.reg "lo"), .adox "t6" (.reg "hi")
  , .mulxMem "t7" "lo" (.reg "yd") "x" 24     -- (lo,t7) = x3*y3
  , .adcx "t6" (.reg "lo")
  , .adox "t7" (.reg "zr")
  , .adcx "t7" (.reg "zr")
    -- Now [t0..t3] = low half l, [t4..t7] = high half h; full product = l + 2^256·h
    -- ── s2n fused-quotient-estimate reduce (bignum_mul_p25519.S 132-178) ──────
    -- Scratch names: `lo`/`hi`/`y` ≡ s2n's rax/rbx/rcx — the only three GP names
    -- free in the reduce (z/x/yd/zr pinned, t0..t7 hold the product; `y`, the
    -- input pointer, is dead after the schoolbook). The fold of 38·h happens
    -- exactly ONCE, in the same dual carry chain that injects the precomputed
    -- 19·q quotient correction, replacing the prior straight Solinas fold +
    -- carry-recapture + two shr/imul/and rounds + explicit add-19 canonical
    -- subtract. Algorithm: estimate q from the top of 38·h₃+l₃, precompute
    -- 19·q, fold 38·h + l with 19·q injected, then one conditional −p via the
    -- sign of (t₃ − (q&1)·2⁶³) and clear bit 255.
    -- ── 1. quotient estimate ──────────────────────────────────────────────────
  , .mov "yd" (.imm 38)
  , .mulx "hi" "lo" (.reg "yd") (.reg "t7")     -- (lo, hi) = 38 * h₃
  , .add "lo" (.reg "t3")                        -- lo += l₃ ; CF = carry
  , .adc "hi" (.reg "zr")                        -- hi += CF
  , .mov "y" (.reg "lo")
  , .shr "y" (.imm 63)                           -- y = bit63(lo) ∈ {0,1}
  , .shl "hi" (.imm 1)
  , .add "hi" (.reg "y")                         -- hi = 2·hi + bit63(lo)
  , .add "hi" (.imm 1)                           -- hi = q  (quotient estimate; q ≤ 80)
  , .mov "y" (.reg "hi")                         -- keep raw quotient q in `y`
  , .imul "hi" (.imm 19)                         -- hi = 19·q  (the correction to inject)
    -- ── 2. fold 38·h into l + inject 19·q, single dual carry chain ───────────
  , .xor_ "zr" (.reg "zr")                       -- clear CF/OF
  , .adox "t0" (.reg "hi")                       -- t0 += 19·q  (OF chain)
  , .mulx "hi" "lo" (.reg "yd") (.reg "t4")
  , .adcx "t0" (.reg "lo"), .adox "t1" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t5")
  , .adcx "t1" (.reg "lo"), .adox "t2" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t6")
  , .adcx "t2" (.reg "lo"), .adox "t3" (.reg "hi")
  , .mulx "hi" "lo" (.reg "yd") (.reg "t7")
  , .adc "t3" (.reg "lo")                         -- final limb
    -- ── 3. canonical conditional subtract of p ───────────────────────────────
    -- amt = 19 when SF(t₃ − (q&1)·2⁶³)=1 else 0; subtract amt, clear bit 255.
  , .shl "y" (.imm 63)                            -- y = (q&1)·2⁶³  (threshold)
  , .mov "lo" (.reg "t3")
  , .sub "lo" (.reg "y")                          -- lo = t₃ − threshold
  , .shr "lo" (.imm 63)                           -- lo = sign bit ∈ {0,1}
  , .imul "lo" (.imm 19)                          -- lo = 19 if SF=1 else 0
  , .sub "t0" (.reg "lo")
  , .sbb "t1" (.reg "zr")
  , .sbb "t2" (.reg "zr")
  , .sbb "t3" (.reg "zr")
  , .mov "hi" (.imm 0x7fffffffffffffff)
  , .and_ "t3" (.reg "hi")                        -- clear bit 255 (the −2^255·q)
    -- ── store the four reduced words ─────────────────────────────────────────
  , .storeMem "z" 0 (.reg "t0")
  , .storeMem "z" 8 (.reg "t1")
  , .storeMem "z" 16 (.reg "t2")
  , .storeMem "z" 24 (.reg "t3") ]

/-- Instruction count of the lowered kernel body. -/
theorem feMulBlock_length : feMulBlock.length = 95 := by native_decide

/-! ## 2. The initial machine state (reg-ptr ABI)

`x`/`y` hold the input buffer base addresses; the input words live at
`[x + 8·i]`, `[y + 8·i]`. We reuse `BignumMontMulKernel.initState`. -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel (initState)

/-! ## 3. Lowering correctness (denotation = `runBlock`) -/

/-- **Lowering correctness on the field-multiply block.** Lowering to
    `Com (x86Dialect 64)` and denoting on the init state equals `runBlock` on the
    source block — the owned backend's straight-line lowering is
    denotation-preserving across the full schoolbook + reduce instruction mix. -/
theorem feMulBlock_lowering_correct (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64) :
    (lowerBlock (Γ := []) feMulBlock).denote
        (.cons (initState x0 x1 x2 x3 y0 y1 y2 y3) .nil)
      = runBlock (initState x0 x1 x2 x3 y0 y1 y2 y3) feMulBlock :=
  lowerBlock_denote_closed feMulBlock (initState x0 x1 x2 x3 y0 y1 y2 y3)

/-! ## 4. The denoted output = `(x·y) mod p25519`, read little-endian -/

/-- The denoted final state. -/
def finalState (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64) : JState 64 :=
  runBlock (initState x0 x1 x2 x3 y0 y1 y2 y3) feMulBlock

/-- The prime `p25519 = 2^255 - 19` as a `Nat`. -/
def p25519 : Nat := 2 ^ 255 - 19

/-- Read four 64-bit limbs little-endian as a `Nat`. -/
def limbsNat (a0 a1 a2 a3 : BitVec 64) : Nat :=
  a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat

/-- The reduced-output `Nat`: the four stored words read little-endian. -/
def outNat (s : JState 64) : Nat :=
  limbsNat (s.load "z" 0) (s.load "z" 8) (s.load "z" 16) (s.load "z" 24)

/-- Field-multiply correctness predicate on a concrete limb vector: the four
    stored output words, read little-endian, equal `(x·y) mod p25519`. -/
def feMulComputes (x0 x1 x2 x3 y0 y1 y2 y3 : BitVec 64) : Prop :=
  outNat (finalState x0 x1 x2 x3 y0 y1 y2 y3)
    = (limbsNat x0 x1 x2 x3 * limbsNat y0 y1 y2 y3) % p25519

/-! **Value semantics.** The field-multiply's all-inputs correctness
(`outNat = (x·y) mod p25519`, including the `2^255-19` Solinas reduction) is
gated by the external byte-identity KAT in `bench/x25519_fieldmul_compare`
(GMP `mpz` mod `p`, s2n `bignum_mul_p25519`, and dalek serial, over random +
corner vectors); `feMulBlock_lowering_correct` is the in-Lean
denotation-preservation guarantee.  The former per-input `native_decide` pin
over the symbolic `runBlock` has been removed per the REV-12 discipline: it
symbolically executed the 91-instruction body over the `String → BitVec`
closure state, compiling to a large nested term under `native_decide` for no
guarantee the external all-inputs KAT does not already provide. -/

/-! ## 5. AT&T assembly emission (in-Lean backend, no jasminc)

`renderLeafFn` wraps the body in a System-V leaf with the reg-ptr ABI glue:
`z`→`%rdi`, `x`→`%rsi`, and the `MULX` multiplier `yd`→`%rdx` (the third argument,
the `y` pointer, is moved out of `%rdx` first). -/

/-- Pin `z`→`%rdi`, `x`→`%rsi`, the `MULX` multiplier `yd`→`%rdx`, and the zero
    register `zr`→`%rbp`. The schoolbook keeps all eight product words `t0..t7`
    plus `y`, `lo`, `hi` resident — twelve pool registers — but `gpPool` excludes
    `%rbp`/`%rsp`, leaving only eleven free after pinning the three pointers; the
    fourth pin (`zr`→`%rbp`, saved/restored by the leaf prologue) recovers the
    twelfth slot so the first-fit allocator does not exhaust the pool and alias
    later names (`t7`, the reduction scratch) onto the `%rax` default. -/
def feMulPinned : GpAlloc := [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx"), ("zr", "%rbp")]

/-- Register allocation (pointers + `yd` pinned, working regs first-fit). -/
def feMulAlloc : GpAlloc := allocGp feMulPinned feMulBlock

/-- The rendered AT&T body (one line per `JInstr`). -/
def feMulAsmBody : List String := renderBlockBody feMulAlloc feMulBlock

/-- The System V AMD64 signature: three pointer arguments `z`, `x`, `y` (in
    `%rdi`, `%rsi`, `%rdx`). The body refers to the third by the source name `y`
    (the input-vector pointer); the allocator binds it to a free register, and the
    ABI layer's `argMarshalMoves` emits the `movq %rdx, <yreg>` that frees `%rdx`
    for the `MULX` multiplier `yd`. -/
def feMulArgs : List AbiArg :=
  [ ⟨"z", .intPtr⟩, ⟨"x", .intPtr⟩, ⟨"y", .intPtr⟩ ]

/-- The full emitted `.s` leaf function, framed by the principled SysV ABI layer
    (`renderSysVLeafFn`): the prologue saves exactly the callee-saved registers the
    allocation binds (`abiSave` + alignment pad) then marshals the third pointer
    argument out of `%rdx`; the epilogue restores them and returns. The body is
    `runBlock`-verified; the ABI glue is trusted scaffolding outside it, but is now
    *derived from the allocation*, not hand-written. -/
def feMulAsm : String :=
  renderSysVLeafFn "fe25519_mul_x86_from_lean" feMulAlloc feMulArgs feMulAsmBody []

/-- The emitted asm has one body line per instruction. -/
theorem feMulAsmBody_length : feMulAsmBody.length = 95 := by native_decide

/-- Shape check: the emitted asm contains the dual carry-chain idiom
    (`mulx`, `adcx`, `adox`), the memory-operand `MULX` reads the multiplicand
    straight from `[x]` (`mulxq 0(%rsi)`, matching s2n's `mulxq (x)`), the result
    stores print in AT&T form (`(%rdi)`), the `%rdx`-pinned multiplier is the
    `MULX` src1, and the reduction's `38` and `19` Solinas constants appear. -/
theorem feMulAsm_shape :
    BignumMontMulKernel.hasSub feMulAsm "mulx"
      ∧ BignumMontMulKernel.hasSub feMulAsm "adcx"
      ∧ BignumMontMulKernel.hasSub feMulAsm "adox"
      ∧ BignumMontMulKernel.hasSub feMulAsm "mulxq 0(%rsi)"
      ∧ BignumMontMulKernel.hasSub feMulAsm "(%rdi)"
      ∧ BignumMontMulKernel.hasSub feMulAsm "$38"
      ∧ BignumMontMulKernel.hasSub feMulAsm "$19" := by native_decide

/-- Emit driver: write the in-Lean-backend-emitted `.s` for the bench harness. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/x25519_fieldmul_compare/gen_com"
  IO.FS.writeFile
    "bench/x25519_fieldmul_compare/gen_com/fe25519_mul_x86_from_lean.s" feMulAsm
  IO.println "wrote gen_com/fe25519_mul_x86_from_lean.s (in-Lean x86 backend, no jasminc)"

end CatCrypt.Crypto.SecureCompilation.X86Backend.Fe25519MulKernel
