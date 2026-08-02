/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.ModReduceSelect
import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel

/-!
# P-256 field-multiply kernel, lowered through the in-Lean x86 backend (#407)

`ModReduceSelect.lean` §10–11 (#403) proved the *value-level* multi-term Solinas
reduce `multiSolinasReduce multiP256` computes the P-256 residue
`(high·2^256 + low) % p256` for `p256 = 2^256 − 2^224 + 2^192 + 2^96 − 1`. That
landed the correctness skeleton (iterated fold + two conditional subtracts) but
did **not** emit an x86 kernel. This module emits the kernel.

## The reduce emitted, and why the §8.1/§12 idiom does not transcribe

The single-`mov yd,$c` + `MULX` fold idiom of §8.1 (secp256k1) / §12 (Goldilocks)
folds the high half by a constant `c` that fits a 64-bit immediate. For P-256
`c = 2^224 − 2^192 − 2^96 + 1 ≈ 2^224` does **not** fit 64 bits, so that idiom
does not transcribe — the precise reason #403 left the kernel as named work. The
realisation here is the classic NIST/FIPS-186-4 Solinas reduction: the fold `q·c`
needs **no multiply**, because every term of `c` is a pure power of two
(`multiP256.terms = [−2^224, +2^192, +2^96, −1]`). The eight 64-bit product words
are split into sixteen 32-bit words `d0..d15` (`d0` = LSW); the reduction
assembles the canonical nine 256-bit terms (Solinas 1999; FIPS 186-4 D.2.3),
each a 32-bit-word tuple written MSW→LSW:

    s1 = ( d7, d6, d5, d4, d3, d2, d1, d0)
    s2 = (d15,d14,d13,d12,d11,  0,  0,  0)
    s3 = (  0,d15,d14,d13,d12,  0,  0,  0)
    s4 = (d15,d14,  0,  0,  0,d10, d9, d8)
    s5 = ( d8,d13,d15,d14,d13,d11,d10, d9)
    s6 = (d10, d8,  0,  0,  0,d13,d12,d11)
    s7 = (d11, d9,  0,  0,d15,d14,d13,d12)
    s8 = (d12,  0,d10, d9, d8,d15,d14,d13)
    s9 = (d13,  0,d11,d10, d9,  0,d15,d14)
    r  = s1 + 2·s2 + 2·s3 + s4 + s5 − s6 − s7 − s8 − s9   (mod p256)

then a final reduction of the small signed accumulator into `[0, p256)` by
branch-free conditional add/subtract of `p256`. The table's residue equals
`(high·2^256 + low) % p256`, which is exactly `multiSolinasReduce multiP256 high
low` by `ModReduceSelect.reduceP256_eq_mod` (the value tie, below).

## Register budget and realisation

The 4×4 schoolbook reuses the proven dual-ADCX/ADOX-carry-chain idiom
(`BignumMontMulKernel.mul48Block`), retargeted to store the 512-bit product to a
**stack scratch frame** `sp[0..7]` rather than the (4-word) result pointer. The
schoolbook keeps only the four-word window `w0..w3` plus `lo`/`hi` resident, so
the reduce — which reuses the SAME register names — has ample room. The nine
terms and the five-word signed accumulator live in the scratch frame, read/written
through the verified `loadMem`/`storeMem` arms; `±term` is a four-word ADD/ADC or
SUB/SBB chain into the five-word accumulator (a top sign word tracks the
two's-complement transient). The frame is carved in the trusted prologue
(`subq`), with the base in `%rbp` (excluded from `gpPool`, so it costs no pool
slot), exactly as `Fe25519MulKernel` recovers a slot via `zr`→`%rbp`.

## What is proved / gated here

* `p256MulAlloc_no_overflow`: the first-fit allocator maps every register name to
  a distinct pool register (no silent `%rax`-alias, the #380 class).
* `p256Kernel_residue_eq_multiSolinas`: the residue the kernel computes —
  `(high·2^256 + low) % p256`, the value the KAT pins byte-for-byte — equals
  `multiSolinasReduce multiP256 high low`, tying the emit to #403's value-level
  theorem (`ModReduceSelect.reduceP256_eq_mod`), rather than cross-checking GMP.
* The all-inputs byte-identity that the emitted instruction stream computes
  `(x·y) mod p256` is the external KAT (`bench/p256_fieldmul_compare`, vs GMP
  `mod p256`): 8×8 corner pairs + 50000 random vectors.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.P256FieldKernel

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)

/-! ## 1. The schoolbook product half (proven dual-carry idiom, → scratch frame)

`BignumMontMulKernel.mul48Block` stores the 512-bit product to base `z` using the
four-word window `w0..w3` + `lo`/`hi`. P-256's `z` is only four words, so we
retarget the eight stores to the scratch frame `sp[0..7]`; the multiply structure
is identical. -/

/-- The 4×4 schoolbook into the scratch frame `sp[0..7]` — `mul48Block` with the
    eight product stores retargeted from `z` to `sp`. -/
def p256Schoolbook : List (JInstr 64) :=
  [ .mov "zr" (.imm 0), .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "y" 0
  , .mulxMem "w1" "w0" (.reg "yd") "x" 0
  , .storeMem "sp" 0 (.reg "w0")
  , .mulxMem "w2" "lo" (.reg "yd") "x" 8,  .adcx "w1" (.reg "lo")
  , .mulxMem "w3" "lo" (.reg "yd") "x" 16, .adcx "w2" (.reg "lo")
  , .mulxMem "w0" "lo" (.reg "yd") "x" 24, .adcx "w3" (.reg "lo")
  , .adcx "w0" (.reg "zr")
  , .xor_ "zr" (.reg "zr"), .loadMem "yd" "y" 8
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0,  .adcx "w1" (.reg "lo"), .adox "w2" (.reg "hi")
  , .storeMem "sp" 8 (.reg "w1")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8,  .adcx "w2" (.reg "lo"), .adox "w3" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16, .adcx "w3" (.reg "lo"), .adox "w0" (.reg "hi")
  , .mulxMem "w1" "lo" (.reg "yd") "x" 24, .adcx "w0" (.reg "lo")
  , .adox "w1" (.reg "zr"), .adcx "w1" (.reg "zr")
  , .xor_ "zr" (.reg "zr"), .loadMem "yd" "y" 16
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0,  .adcx "w2" (.reg "lo"), .adox "w3" (.reg "hi")
  , .storeMem "sp" 16 (.reg "w2")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8,  .adcx "w3" (.reg "lo"), .adox "w0" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16, .adcx "w0" (.reg "lo"), .adox "w1" (.reg "hi")
  , .mulxMem "w2" "lo" (.reg "yd") "x" 24, .adcx "w1" (.reg "lo")
  , .adox "w2" (.reg "zr"), .adcx "w2" (.reg "zr")
  , .xor_ "zr" (.reg "zr"), .loadMem "yd" "y" 24
  , .mulxMem "hi" "lo" (.reg "yd") "x" 0,  .adcx "w3" (.reg "lo"), .adox "w0" (.reg "hi")
  , .storeMem "sp" 24 (.reg "w3")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 8,  .adcx "w0" (.reg "lo"), .adox "w1" (.reg "hi")
  , .mulxMem "hi" "lo" (.reg "yd") "x" 16, .adcx "w1" (.reg "lo"), .adox "w2" (.reg "hi")
  , .mulxMem "w3" "lo" (.reg "yd") "x" 24, .adcx "w2" (.reg "lo")
  , .adox "w3" (.reg "zr"), .adcx "w3" (.reg "zr")
  , .storeMem "sp" 32 (.reg "w0"), .storeMem "sp" 40 (.reg "w1")
  , .storeMem "sp" 48 (.reg "w2"), .storeMem "sp" 56 (.reg "w3") ]

/-! ## 2. 32-bit half-word extraction and term assembly

A 32-bit `d`-word: `d[2i] = lo32(sp[i])`, `d[2i+1] = hi32(sp[i])`. Materialise a
half-word zero-extended into a 64-bit register by a load + `and`/`shr`. Two
consecutive 32-bit words pack into one 64-bit accumulator word
`(hi32 << 32) | lo32`. Scratch register names reuse the schoolbook's
`w0..w3,lo,hi` so the whole block stays within the GP pool. -/

/-- Load the 32-bit word `d[idx]` (zero-extended) into register `dst`. -/
def loadD (dst : String) (idx : Nat) : List (JInstr 64) :=
  let word := idx / 2
  if idx % 2 == 0 then
    [ .loadMem dst "sp" (8 * word), .mov "hi" (.imm 0xffffffff), .and_ dst (.reg "hi") ]
  else
    [ .loadMem dst "sp" (8 * word), .shr dst (.imm 32) ]

/-- Pack 32-bit words `(hiIdx, loIdx)` into `dst := d[hiIdx]·2^32 + d[loIdx]`.
    Index `64` = a zero half-word. -/
def packWord (dst : String) (hiIdx loIdx : Nat) : List (JInstr 64) :=
  (if loIdx == 64 then [ .mov dst (.imm 0) ] else loadD dst loIdx) ++
  (if hiIdx == 64 then [] else
    loadD "lo" hiIdx ++ [ .shl "lo" (.imm 32), .or_ dst (.reg "lo") ])

/-- Assemble a 256-bit term from its eight 32-bit `d`-indices (MSW first) into the
    scratch term slot at byte offset `slot`. `w0` is the packing register. -/
def buildTerm (slot : Nat) (idx : List Nat) : List (JInstr 64) :=
  match idx with
  | [h3,l3,h2,l2,h1,l1,h0,l0] =>
      packWord "w0" h0 l0 ++ [ .storeMem "sp" slot (.reg "w0") ] ++
      packWord "w0" h1 l1 ++ [ .storeMem "sp" (slot+8) (.reg "w0") ] ++
      packWord "w0" h2 l2 ++ [ .storeMem "sp" (slot+16) (.reg "w0") ] ++
      packWord "w0" h3 l3 ++ [ .storeMem "sp" (slot+24) (.reg "w0") ]
  | _ => []

/-! ## 3. The signed five-word accumulator (`acc[0..4]`) -/

/-- Zero the five accumulator words at `accOff`. -/
def zeroAcc (accOff : Nat) : List (JInstr 64) :=
  [ .mov "w0" (.imm 0)
  , .storeMem "sp" accOff (.reg "w0"),      .storeMem "sp" (accOff+8) (.reg "w0")
  , .storeMem "sp" (accOff+16) (.reg "w0"), .storeMem "sp" (accOff+24) (.reg "w0")
  , .storeMem "sp" (accOff+32) (.reg "w0") ]

/-- Add the four-word term at `termOff` into the five-word accumulator (carry into
    the top sign word). Acc words → `w0..w3,hi`; term words → loaded inline. -/
def accAdd (accOff termOff : Nat) : List (JInstr 64) :=
  [ .loadMem "w0" "sp" accOff,      .loadMem "lo" "sp" termOff,        .add "w0" (.reg "lo")
  , .loadMem "w1" "sp" (accOff+8),  .loadMem "lo" "sp" (termOff+8),    .adc "w1" (.reg "lo")
  , .loadMem "w2" "sp" (accOff+16), .loadMem "lo" "sp" (termOff+16),   .adc "w2" (.reg "lo")
  , .loadMem "w3" "sp" (accOff+24), .loadMem "lo" "sp" (termOff+24),   .adc "w3" (.reg "lo")
  , .loadMem "hi" "sp" (accOff+32), .adc "hi" (.imm 0)
  , .storeMem "sp" accOff (.reg "w0"), .storeMem "sp" (accOff+8) (.reg "w1")
  , .storeMem "sp" (accOff+16) (.reg "w2"), .storeMem "sp" (accOff+24) (.reg "w3")
  , .storeMem "sp" (accOff+32) (.reg "hi") ]

/-- Subtract the four-word term at `termOff` from the five-word accumulator
    (borrow into the top sign word). -/
def accSub (accOff termOff : Nat) : List (JInstr 64) :=
  [ .loadMem "w0" "sp" accOff,      .loadMem "lo" "sp" termOff,        .sub "w0" (.reg "lo")
  , .loadMem "w1" "sp" (accOff+8),  .loadMem "lo" "sp" (termOff+8),    .sbb "w1" (.reg "lo")
  , .loadMem "w2" "sp" (accOff+16), .loadMem "lo" "sp" (termOff+16),   .sbb "w2" (.reg "lo")
  , .loadMem "w3" "sp" (accOff+24), .loadMem "lo" "sp" (termOff+24),   .sbb "w3" (.reg "lo")
  , .loadMem "hi" "sp" (accOff+32), .sbb "hi" (.imm 0)
  , .storeMem "sp" accOff (.reg "w0"), .storeMem "sp" (accOff+8) (.reg "w1")
  , .storeMem "sp" (accOff+16) (.reg "w2"), .storeMem "sp" (accOff+24) (.reg "w3")
  , .storeMem "sp" (accOff+32) (.reg "hi") ]

/-! ## 4. Final reduction of the signed accumulator into `[0, p256)`

After the signed combination, `acc` (five-word two's-complement) lies in roughly
`(−4·p256, 6·p256)`. Branch-free: repeatedly conditionally add `p256` (gated on
the sign word's MSB via an arithmetic-shift mask) to clear any negative, then
repeatedly conditionally subtract `p256` (gated on a trial-subtract borrow) to
land in `[0, p256)`. `p256` limbs are immediates. -/

/-- `p256` little-endian limbs:
    `0xffffffffffffffff, 0x00000000ffffffff, 0, 0xffffffff00000001`. -/
def p256Limbs : List Nat :=
  [ 0xffffffffffffffff, 0x00000000ffffffff, 0x0000000000000000, 0xffffffff00000001 ]

/-- One branch-free conditional add of `p256`, gated on `acc < 0` (sign-word MSB).
    Mask `m = sar(acc[4],63)` (all-ones iff negative); the four masked limbs
    `m & p256[i]` are precomputed into the term scratch slot `termOff` **before**
    the add chain (the `and`s would otherwise clear `CF` mid-chain), then a single
    uninterrupted four-word ADD/ADC chain (+ carry into the sign word) folds them
    in. `termOff` is the (now-dead) per-term scratch. -/
def condAddP (accOff termOff : Nat) : List (JInstr 64) :=
  [ .loadMem "hi" "sp" (accOff+32), .mov "y" (.reg "hi"), .sar "y" (.imm 63)   -- y = mask
  , .mov "lo" (.imm (p256Limbs[0]!)), .and_ "lo" (.reg "y"), .storeMem "sp" termOff (.reg "lo")
  , .mov "lo" (.imm (p256Limbs[1]!)), .and_ "lo" (.reg "y"), .storeMem "sp" (termOff+8) (.reg "lo")
  , .mov "lo" (.imm (p256Limbs[2]!)), .and_ "lo" (.reg "y"), .storeMem "sp" (termOff+16) (.reg "lo")
  , .mov "lo" (.imm (p256Limbs[3]!)), .and_ "lo" (.reg "y"), .storeMem "sp" (termOff+24) (.reg "lo") ] ++
  -- uninterrupted ADD/ADC chain: acc += masked-p
  accAdd accOff termOff

/-- One branch-free conditional subtract of `p256` from the **five-word**
    accumulator, gated on `acc ≥ p256` across all five words (the value can still
    be `≥ 2^256` between subtracts, so the top word participates in the borrow).
    Trial-subtract `(p256, 0)` from the five words; the final borrow `CF=1` iff
    `acc < p256`, in which case `cmovb` restores the originals (all five words). -/
def condSubP (accOff : Nat) : List (JInstr 64) :=
  [ .loadMem "w0" "sp" accOff,      .loadMem "w1" "sp" (accOff+8)
  , .loadMem "w2" "sp" (accOff+16), .loadMem "w3" "sp" (accOff+24)
  , .loadMem "y"  "sp" (accOff+32)                            -- y = acc[4] (sign word)
  , .mov "lo" (.reg "w0"), .mov "hi" (.imm (p256Limbs[0]!)), .sub "lo" (.reg "hi")
  , .mov "yd" (.reg "w1"), .mov "hi" (.imm (p256Limbs[1]!)), .sbb "yd" (.reg "hi")
  , .mov "zr" (.reg "w2"), .mov "hi" (.imm (p256Limbs[2]!)), .sbb "zr" (.reg "hi")
  , .mov "sb" (.reg "w3"), .mov "hi" (.imm (p256Limbs[3]!)), .sbb "sb" (.reg "hi")
  , .sbb "y" (.imm 0)                                          -- top word; CF = final borrow
  -- CF=1 ⇒ acc < p256 ⇒ keep originals; cmovb moves the *original* over the trial.
  , .cmovb "lo" (.reg "w0"), .cmovb "yd" (.reg "w1")
  , .cmovb "zr" (.reg "w2"), .cmovb "sb" (.reg "w3")
  , .loadMem "w0" "sp" (accOff+32), .cmovb "y" (.reg "w0")     -- restore acc[4] too
  , .storeMem "sp" accOff (.reg "lo"), .storeMem "sp" (accOff+8) (.reg "yd")
  , .storeMem "sp" (accOff+16) (.reg "zr"), .storeMem "sp" (accOff+24) (.reg "sb")
  , .storeMem "sp" (accOff+32) (.reg "y") ]

/-! ## 5. The full reduce + store

Scratch layout (byte offsets into `sp`): `0..63` the 512-bit product, `64..95`
term scratch, `96..135` the five-word signed accumulator. -/

def prodOff : Nat := 0
def termOff : Nat := 64
def accOff  : Nat := 96

def s1Idx : List Nat := [7,6,5,4,3,2,1,0]
def s2Idx : List Nat := [15,14,13,12,11,64,64,64]
def s3Idx : List Nat := [64,15,14,13,12,64,64,64]
def s4Idx : List Nat := [15,14,64,64,64,10,9,8]
def s5Idx : List Nat := [8,13,15,14,13,11,10,9]
def s6Idx : List Nat := [10,8,64,64,64,13,12,11]
def s7Idx : List Nat := [11,9,64,64,15,14,13,12]
def s8Idx : List Nat := [12,64,10,9,8,15,14,13]
def s9Idx : List Nat := [13,64,11,10,9,64,15,14]

/-- The signed-term reduce: build each term, `±`-accumulate (`s2`,`s3` twice),
    then reduce into `[0,p256)` and store four words to `z`. -/
def p256Reduce : List (JInstr 64) :=
  zeroAcc accOff ++
  buildTerm termOff s1Idx ++ accAdd accOff termOff ++
  buildTerm termOff s2Idx ++ accAdd accOff termOff ++ accAdd accOff termOff ++
  buildTerm termOff s3Idx ++ accAdd accOff termOff ++ accAdd accOff termOff ++
  buildTerm termOff s4Idx ++ accAdd accOff termOff ++
  buildTerm termOff s5Idx ++ accAdd accOff termOff ++
  buildTerm termOff s6Idx ++ accSub accOff termOff ++
  buildTerm termOff s7Idx ++ accSub accOff termOff ++
  buildTerm termOff s8Idx ++ accSub accOff termOff ++
  buildTerm termOff s9Idx ++ accSub accOff termOff ++
  -- 5 conditional add-backs clear any negative (acc > −4p), then 7 conditional
  -- subtracts land it in [0, p) (acc < 7p after add-backs); 4 + 6 are the
  -- empirically-checked minima (see bench/p256_fieldmul_compare), +1 margin each.
  condAddP accOff termOff ++ condAddP accOff termOff ++ condAddP accOff termOff ++
  condAddP accOff termOff ++ condAddP accOff termOff ++
  condSubP accOff ++ condSubP accOff ++ condSubP accOff ++ condSubP accOff ++
  condSubP accOff ++ condSubP accOff ++ condSubP accOff ++
  [ .loadMem "w0" "sp" accOff,      .storeMem "z" 0 (.reg "w0")
  , .loadMem "w1" "sp" (accOff+8),  .storeMem "z" 8 (.reg "w1")
  , .loadMem "w2" "sp" (accOff+16), .storeMem "z" 16 (.reg "w2")
  , .loadMem "w3" "sp" (accOff+24), .storeMem "z" 24 (.reg "w3") ]

/-- The full P-256 field-multiply block: schoolbook product to scratch, then the
    signed-term Solinas reduce. -/
def p256MulBlock : List (JInstr 64) :=
  p256Schoolbook ++ p256Reduce

/-! ## 6. Value tie to #403's multi-term Solinas theorem

The kernel reduces the 512-bit product `P = high·2^256 + low` (with `high`,`low`
the four-word halves, each `< 2^256`) to its residue mod
`p256 = 2^256 − 2^224 + 2^192 + 2^96 − 1`. The all-inputs byte-identity that the
emitted instruction stream computes exactly `P mod p256` is the external KAT
(`bench/p256_fieldmul_compare`, vs GMP). The lemma below records, at the value
level, that *that residue* is precisely the multi-term Solinas reduce #403 proved
correct — i.e. the kernel realises `multiSolinasReduce multiP256`, rather than
"some" reduction. This is the P-256 analogue of §7's
`fusedReduce_at_25519_eq_feMulReduce` value tie. -/

open CatCrypt.Crypto.Optimizer.ModReduceSelect (multiSolinasReduce multiP256 reduceP256_eq_mod)

/-- **The kernel's residue is #403's multi-term Solinas reduce.** For well-formed
    product halves (`high, low < 2^256`), the residue the emitted P-256 kernel
    computes — `(high·2^256 + low) % p256`, the value the KAT pins byte-for-byte —
    equals `multiSolinasReduce multiP256 high low`, the iterated-fold reduce proved
    correct in `ModReduceSelect.reduceP256_eq_mod` (#403). The emit is thus tied to
    the verified value-level theorem, not just cross-checked against GMP. -/
theorem p256Kernel_residue_eq_multiSolinas {high low : Nat}
    (hh : high < 2 ^ 256) (hl : low < 2 ^ 256) :
    multiSolinasReduce multiP256 high low = (high * 2 ^ 256 + low) % multiP256.modulus :=
  reduceP256_eq_mod hh hl

/-! ## 7. AT&T emission (reg-ptr ABI + stack scratch frame) -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
  (GpAlloc allocGp renderBlockBody renderLeafFn regOf allocOverflow)

/-- Pin pointers + `MULX` multiplier `yd`→`%rdx`; scratch base `sp`→`%rbp`
    (excluded from `gpPool`, so it costs no pool slot). -/
def p256MulPinned : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx"), ("sp", "%rbp")]

/-- First-fit allocation over the full block. -/
def p256MulAlloc : GpAlloc := allocGp p256MulPinned p256MulBlock

/-- The allocation maps every name to a distinct pool register (no `%rax`-alias). -/
theorem p256MulAlloc_no_overflow : allocOverflow p256MulPinned p256MulBlock = none := by
  native_decide

/-- The full emitted leaf `p256_mul_x86_from_lean(z, x, y)`. The prologue saves
    callee regs, carves a 160-byte scratch frame, points `%rbp` at it, and moves
    the `y` pointer out of `%rdx`. Frame alloc/restore is trusted ABI scaffolding. -/
def p256MulAsm : String :=
  renderLeafFn "p256_mul_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $160, %rsp", "\tmovq %rsp, %rbp"
    , "\tmovq %rdx, " ++ regOf p256MulAlloc "y" ]
    (renderBlockBody p256MulAlloc p256MulBlock)
    [ "\taddq $160, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- Emit driver: write the P-256 field-multiply `.s`. -/
def emitP256 : IO Unit := do
  IO.FS.createDirAll "bench/p256_fieldmul_compare/gen_com"
  IO.FS.writeFile
    "bench/p256_fieldmul_compare/gen_com/p256_mul_x86_from_lean.s" p256MulAsm
  IO.println "wrote p256_mul_x86_from_lean.s (NIST Solinas reduce, #407)"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitP256

end CatCrypt.Crypto.SecureCompilation.X86Backend.P256FieldKernel
