/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
import CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
import CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-!
# The AES-XTS tweak GF(2^128) doubling kernel through the owned x86 backend

XTS-AES (IEEE Std 1619-2007) advances the per-block tweak `T` by multiplying it
by the primitive element `x` ("α") in `GF(2^128)` with reduction polynomial
`x^128 + x^7 + x^2 + x + 1`, between consecutive 16-byte data blocks. The tweak
is a **little-endian** 128-bit value, so the α-multiply is the GF(2^128)
*doubling* primitive:

* left-shift the 128-bit value by one bit;
* if the bit shifted out of the top was `1`, XOR the low byte with the reduction
  constant `0x87` (= `x^7 + x^2 + x + 1`).

This is the same operation the reference `ref_gf128_mul_x` in s2n-bignum's
`tests/ref_aes_xts.c` computes byte-by-byte; here it is a straight-line
`List (JInstr 64)` over the two 64-bit halves `(lo, hi)` of the little-endian
tweak, lowered through the owned in-Lean x86 backend (no jasminc).

## Constant-time

The doubling is a fixed shift + conditional XOR. Crucially the XOR is realised
*branchlessly*: the carry bit `c = hi >> 63` is sign-extended to a mask
(`neg c` → all-ones iff `c = 1`), the reduction constant is `and`-ed with the
mask, then XORed in. There is **no data-dependent branch** and **no
data-dependent memory address** — every memory access is direct
(`base + compile-time displacement`). Hence the kernel passes the decidable
`allDirect` check and `ConstantTimeCoverage.allDirect_constant_time` gives a
machine-leakage trace independent of the (secret) tweak value.

## ABI

`void aes_xts_double(uint8_t *t)` — in-place doubling of the 16-byte
little-endian tweak `t[0..16)`. `lo = t[0..8)`, `hi = t[8..16)`.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.XtsTweakKernel

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Dialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstantTimeCoverage

/-! ## 1. The doubling block as `List (JInstr 64)`

`t` (the tweak base pointer) lives in `%rdi`. The window is
`{t, lo, hi, c, d, m}` — six names. -/

/-- The GF(2^128) doubling (mul-by-x) body on the little-endian tweak at
    `[t]` (low 8 bytes) / `[t+8]` (high 8 bytes).

    Computes `2·V` in `GF(2^128)` where `V` is the little-endian 128-bit value
    `lo + 2^64·hi`:
    * `c := hi >> 63`          (the bit shifted out of the top — the overflow);
    * `d := lo >> 63`          (the bit crossing from `lo` into `hi`);
    * `hi := (hi << 1) | d`;
    * `lo := lo << 1`;
    * `c := -c`                (mask: all-ones iff overflow, else 0);
    * `m := 0x87 & c`          (the reduction constant, gated by the mask);
    * `lo := lo ^ m`.

    The conditional reduction is branchless (`neg`/`and`/`xor`), so the control
    flow and memory-address sequence are independent of the tweak value. -/
def xtsDoubleBlock : List (JInstr 64) :=
  [ .loadMem "lo" "t" 0          -- lo = t[0..8)
  , .loadMem "hi" "t" 8          -- hi = t[8..16)
  , .mov "c" (.reg "hi")         -- c  = hi
  , .shr "c" (.imm 63)           -- c  = hi >> 63       (overflow bit)
  , .mov "d" (.reg "lo")         -- d  = lo
  , .shr "d" (.imm 63)           -- d  = lo >> 63       (bit lo→hi)
  , .shl "hi" (.imm 1)           -- hi = hi << 1
  , .or_ "hi" (.reg "d")         -- hi = (hi << 1) | (lo >> 63)
  , .shl "lo" (.imm 1)           -- lo = lo << 1
  , .neg "c"                     -- c  = -c   (all-ones iff overflow)
  , .mov "m" (.imm 0x87)         -- m  = 0x87
  , .and_ "m" (.reg "c")         -- m  = overflow ? 0x87 : 0
  , .xor_ "lo" (.reg "m")        -- lo = lo ^ m          (conditional reduce)
  , .storeMem "t" 0 (.reg "lo")  -- t[0..8)  = lo
  , .storeMem "t" 8 (.reg "hi") ]-- t[8..16) = hi

/-- Register pressure: `{t, lo, hi, c, d, m}` — six names. -/
theorem xtsDoubleBlock_regs : (blockNames xtsDoubleBlock).length = 6 := by native_decide

/-! ## 2. Lowering correctness (denotation = `runBlock`) -/

/-- **Lowering correctness.** Lowering `xtsDoubleBlock` and denoting equals
    `runBlock` on the source block, for any initial state. -/
theorem xtsDoubleBlock_lowering_correct (s : JState 64) :
    (lowerBlock (Γ := []) xtsDoubleBlock).denote (.cons s .nil)
      = runBlock s xtsDoubleBlock :=
  lowerBlock_denote_closed xtsDoubleBlock s

/-! ## 3. Value semantics (`native_decide` on representative tweaks)

We pin the GF(2^128) doubling's value semantics on the two regimes that matter:
*no overflow* (top bit `0` ⇒ plain shift) and *overflow* (top bit `1` ⇒ shift
then XOR `0x87` into the low byte). The all-inputs identity vs the IEEE-1619
reference is the runtime KAT in `bench/aes_xts_compare/`. -/

/-- Seed state: `lo`/`hi` from the two limb values, all else clear. -/
def initTweak (loV hiV : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    flags := {}
    mem := fun base off =>
      if base = "t" then
        (if off = 0 then loV else if off = 8 then hiV else 0)
      else 0 }

/-- **No-overflow case.** With the top bit of `hi` clear, doubling is the plain
    128-bit left shift: `lo' = lo << 1`, `hi' = (hi << 1) | (lo >> 63)`, and the
    low byte is *not* XORed with `0x87`. Checked through the full
    `runBlock`/`evalInstr` chain. Here `V = 0x0000…0001` (`lo = 1`, `hi = 0`)
    doubles to `V' = 0x0000…0002`. -/
theorem xtsDouble_no_overflow :
    let s := runBlock (initTweak 1 0) xtsDoubleBlock
    s.load "t" 0 = (2 : BitVec 64) ∧ s.load "t" 8 = (0 : BitVec 64) := by
  native_decide

/-- **Overflow case (the reduction).** With the top bit of `hi` set, the bit
    shifts out and the low byte is XORed with `0x87`. Here
    `V = 2^127` (`lo = 0`, `hi = 2^63 = 0x8000000000000000`) doubles to
    `2^128 ≡ x^7 + x^2 + x + 1 = 0x87` (`lo' = 0x87`, `hi' = 0`). -/
theorem xtsDouble_overflow :
    let s := runBlock (initTweak 0 0x8000000000000000) xtsDoubleBlock
    s.load "t" 0 = (0x87 : BitVec 64) ∧ s.load "t" 8 = (0 : BitVec 64) := by
  native_decide

/-- **Carry across the limb boundary.** A bit at position 63 of `lo` crosses
    into bit 0 of `hi`. `V = 2^63` (`lo = 2^63`, `hi = 0`) doubles to `2^64`
    (`lo' = 0`, `hi' = 1`), no reduction. -/
theorem xtsDouble_limb_carry :
    let s := runBlock (initTweak 0x8000000000000000 0) xtsDoubleBlock
    s.load "t" 0 = (0 : BitVec 64) ∧ s.load "t" 8 = (1 : BitVec 64) := by
  native_decide

/-! ## 4. Constant-time (by construction)

Every instruction of `xtsDoubleBlock` uses direct addressing — the two
`loadMem`/`storeMem` use a compile-time displacement (`0` / `8`), and the rest
are register/immediate ALU ops with no memory operand. So the decidable
`allDirect` check passes, and `allDirect_constant_time` gives a tweak-independent
machine-leakage trace. The conditional reduction is the branchless `neg`/`and`/
`xor` mask idiom, so there is no secret-dependent control flow either. -/

/-- The doubling kernel is all-direct (no register-indexed memory addressing). -/
theorem xtsDoubleBlock_allDirect : allDirect xtsDoubleBlock = true := by native_decide

/-- **Constant-time.** `xtsDoubleBlock` produces the same machine-leakage trace
    from any two initial states — its observable control-flow + memory-address
    sequence is a function of the program text alone, independent of the (secret)
    tweak value. -/
theorem xtsDoubleBlock_constant_time (s₁ s₂ : JState 64) :
    blockLeak s₁ xtsDoubleBlock = blockLeak s₂ xtsDoubleBlock :=
  allDirect_constant_time xtsDoubleBlock xtsDoubleBlock_allDirect s₁ s₂

/-! ## 5. Emit to assembly

`aes_xts_double(uint8_t *t)`: `t`→`%rdi`. The scratch window `{lo,hi,c,d,m}` is
allocated to caller-saved registers, so no callee-saved save/restore is needed;
the leaf is a straight `ret`. -/

/-- Pin the tweak pointer to its System-V first argument register. -/
def doublePinned : GpAlloc := [("t", "%rdi")]

def doubleAlloc : GpAlloc := allocGp doublePinned xtsDoubleBlock

/-- The rendered AT&T `.s` for the XTS tweak doubling kernel. -/
def doubleAsm : String :=
  renderLeafFn "aes_xts_double"
    (prologue := abiSave doubleAlloc)
    (bodyLines := renderBlockBody doubleAlloc xtsDoubleBlock)
    (epilogue := abiRestore doubleAlloc ++ [ "\tret" ])

/-- Local substring test (`needle` occurs in `hay`). -/
def hasSub (hay needle : String) : Bool :=
  (List.range (hay.length + 1)).any (fun i =>
    needle == String.ofList (hay.toList.drop i |>.take needle.length))

/-- The emitted asm contains the doubling shift chain, the `0x87` reduction
    constant, and the in-place tweak load/store via `%rdi`. -/
theorem doubleAsm_shape :
    hasSub doubleAsm "shlq"
      ∧ hasSub doubleAsm "shrq"
      ∧ hasSub doubleAsm "negq"
      ∧ hasSub doubleAsm "$135"        -- 0x87 immediate
      ∧ hasSub doubleAsm "(%rdi)" := by native_decide

/-- Emit driver: write `aes_xts_double.s` under the bench dir. -/
def emitMain : IO Unit := do
  IO.FS.createDirAll "bench/aes_xts_compare/gen"
  IO.FS.writeFile "bench/aes_xts_compare/gen/aes_xts_double.s" doubleAsm
  IO.println "WROTE bench/aes_xts_compare/gen/aes_xts_double.s (owned x86 backend, NO jasminc)"

/-! ## Artifact generation at elaboration

The `.s` is written while this module elaborates, so `lake` owns the dependency
between the kernel source and the bench artifact. -/

#eval emitMain

end CatCrypt.Crypto.SecureCompilation.X86Backend.XtsTweakKernel
