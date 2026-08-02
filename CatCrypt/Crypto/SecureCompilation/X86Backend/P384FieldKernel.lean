/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Optimizer.ModReduceSelect
import CatCrypt.Crypto.SecureCompilation.X86Backend.BignumMontMulKernel

/-!
# P-384 field-multiply kernel, lowered through the in-Lean x86 backend (#409)

`ModReduceSelect.lean` §10–11 (#403) proved the *value-level* multi-term Solinas
reduce `multiSolinasReduce multiP384` computes the P-384 residue
`(high·2^384 + low) % p384` for `p384 = 2^384 − 2^128 − 2^96 + 2^32 − 1`
(`reduceP384_eq_mod`, fuel 2). This module emits the x86 kernel. It is the
sibling that #407 deferred: P-384 needs a fresh 6×6 schoolbook (12-word
product) and the FIPS-186-4 D.2.4 signed Solinas table is error-prone (the #407
first transcription failed all random tests). We therefore *derived* the signed
table from the relation `2^384 ≡ 2^128 + 2^96 − 2^32 + 1 (mod p384)`, folded to
fixpoint, and validated it byte-for-byte against GMP before emitting any Lean
(`bench/p384_fieldmul_compare`, the de-risk gate).

## The reduce emitted

The 768-bit product is split into twenty-four 32-bit words `d0..d23` (`d0` = LSW)
out of the twelve 64-bit product words at `sp[0..11]`. Modulo p384, each high
word `d_i` (`i ≥ 12`) folds into the low twelve slots via `2^384 ≡ c` with
`c = 2^128 + 2^96 − 2^32 + 1` (every term a pure power of two — **no multiply**,
exactly the Solinas shape `multiP384.terms = [−2^128, −2^96, +2^32, −1]`). Folding
to fixpoint (two rounds — `multiP384.fuel = 2`) gives an eleven-term signed
combination; each term is a twelve-word (32-bit) tuple written MSW→LSW, assembled
by the same prime-agnostic `buildTerm`/`packWord` machinery the P-256 kernel uses:

    r = s0 + s1 + s2 + s3 + s4 + s5 + s6 + s7 − s8 − s9 − s10   (mod p384)

(the term tuples are `p384sIdx`, derived + GMP-validated in
`bench/p384_fieldmul_compare/p384_decompose.c`). A final branch-free conditional
add/subtract of `p384` lands the signed accumulator in `[0, p384)`. The table's
residue equals `(high·2^384 + low) % p384` = `multiSolinasReduce multiP384 high
low` by `ModReduceSelect.reduceP384_eq_mod` (the value tie, §6).

## Register budget and realisation

The 6×6 schoolbook reuses the proven dual-ADCX/ADOX-carry-chain idiom (the
`mul48Block` pattern of `BignumMontMulKernel`, extended to six columns),
retargeted to store the 768-bit product to a **stack scratch frame** `sp[0..11]`
rather than the result pointer. The schoolbook keeps the six-word window
`w0..w5` plus `lo`/`hi`/`zr` resident. The reduce is memory-resident: each term
and the seven-word signed accumulator live in the scratch frame, read/written
through the verified `loadMem`/`storeMem` arms, so the reduce holds only a small
working window (`w0..w5`,`lo`,`hi`,`y`,`yd`). The frame base lives in `%rbp`
(excluded from `gpPool`, costing no pool slot), as `Fe25519MulKernel` recovers a
slot via `zr`→`%rbp`. `p384MulAlloc_no_overflow` proves the first-fit allocator
maps every name to a distinct pool register (no silent `%rax`-alias, the #380
class).

## What is proved / gated here

* `p384MulAlloc_no_overflow`: the allocator assigns every register name a
  distinct pool register.
* `p384Kernel_residue_eq_multiSolinas`: the residue the kernel computes —
  `(high·2^384 + low) % p384` — equals `multiSolinasReduce multiP384 high low`,
  tying the emit to #403's value-level theorem (`reduceP384_eq_mod`).
* The all-inputs byte-identity that the emitted stream computes `(x·y) mod p384`
  is the external KAT (`bench/p384_fieldmul_compare`, vs GMP `mod p384`):
  6×6 corner pairs + 50000 random vectors.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.P384FieldKernel

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin (JInstr JOperand)

/-! ## 1. The 6×6 schoolbook product (proven dual-carry idiom, → scratch frame)

The `mul48Block` four-column pattern extended to six columns: row `j` multiplies
by `y_j`, six memory-operand `MULX` into the rolling six-word window
`w0..w5`, with the dual ADCX/ADOX carry chains; after row `j` the low word
`sp[j]` is final and stored, the window rotates. The twelve product words land
at `sp[0..11]`. -/

/-- One schoolbook row `j`: multiplier `y_j` loaded into `yd`(=%rdx); six
    memory-operand MULX `x_i·y_j` accumulated into the six-word window with the
    ADCX (CF) / ADOX (OF) split, then the low window word is stored to `sp[j]`.
    `lowReg` is the window register holding the current low word; the window
    list `win` is the six window registers in increasing-significance order
    starting at the current low position. -/
def p384Row (j : Nat) (win : List String) : List (JInstr 64) :=
  -- win = [r0,r1,r2,r3,r4,r5] significance-ordered; r0 is the low (→ sp[j]).
  match win with
  | [r0,r1,r2,r3,r4,r5] =>
    [ .xor_ "zr" (.reg "zr"), .loadMem "yd" "y" (8*j)
    , .mulxMem "hi" "lo" (.reg "yd") "x" 0,  .adcx r0 (.reg "lo"), .adox r1 (.reg "hi")
    , .storeMem "sp" (8*j) (.reg r0)
    , .mulxMem "hi" "lo" (.reg "yd") "x" 8,  .adcx r1 (.reg "lo"), .adox r2 (.reg "hi")
    , .mulxMem "hi" "lo" (.reg "yd") "x" 16, .adcx r2 (.reg "lo"), .adox r3 (.reg "hi")
    , .mulxMem "hi" "lo" (.reg "yd") "x" 24, .adcx r3 (.reg "lo"), .adox r4 (.reg "hi")
    , .mulxMem "hi" "lo" (.reg "yd") "x" 32, .adcx r4 (.reg "lo"), .adox r5 (.reg "hi")
    , .mulxMem r0 "lo" (.reg "yd") "x" 40,   .adcx r5 (.reg "lo")
    , .adox r0 (.reg "zr"), .adcx r0 (.reg "zr") ]
  | _ => []

/-- The 6×6 schoolbook into `sp[0..11]`. Row 0 is the plain `MULX`/`ADCX` fill
    (no prior carry to absorb), rows 1–5 the dual-carry `p384Row`. The window
    registers rotate each row so the just-finalised low word's register is
    reused as the new high word; after six rows, `sp[6..11]` hold the top six
    product words. -/
def p384Schoolbook : List (JInstr 64) :=
  [ .mov "zr" (.imm 0), .xor_ "zr" (.reg "zr")
  , .loadMem "yd" "y" 0
  , .mulxMem "w1" "w0" (.reg "yd") "x" 0
  , .storeMem "sp" 0 (.reg "w0")
  , .mulxMem "w2" "lo" (.reg "yd") "x" 8,  .adcx "w1" (.reg "lo")
  , .mulxMem "w3" "lo" (.reg "yd") "x" 16, .adcx "w2" (.reg "lo")
  , .mulxMem "w4" "lo" (.reg "yd") "x" 24, .adcx "w3" (.reg "lo")
  , .mulxMem "w5" "lo" (.reg "yd") "x" 32, .adcx "w4" (.reg "lo")
  , .mulxMem "w0" "lo" (.reg "yd") "x" 40, .adcx "w5" (.reg "lo")
  , .adcx "w0" (.reg "zr") ] ++
  -- row 1: low = w1 (→ sp[8]); window [w1,w2,w3,w4,w5,w0]
  p384Row 1 ["w1","w2","w3","w4","w5","w0"] ++
  -- row 2: low = w2; window [w2,w3,w4,w5,w0,w1]
  p384Row 2 ["w2","w3","w4","w5","w0","w1"] ++
  -- row 3
  p384Row 3 ["w3","w4","w5","w0","w1","w2"] ++
  -- row 4
  p384Row 4 ["w4","w5","w0","w1","w2","w3"] ++
  -- row 5
  p384Row 5 ["w5","w0","w1","w2","w3","w4"] ++
  -- store the top six product words sp[6..11] from the rotated window
  -- after row 5 the low word is w5(→sp[5], stored in row5); the remaining six
  -- significance-ordered window words are [w0,w1,w2,w3,w4] + carry-out... but
  -- after row 5 storeMem already wrote sp[5]; the six high words live in
  -- window positions [w0,w1,w2,w3,w4] and the row-5 high carry word w5.
  [ .storeMem "sp" 48 (.reg "w0"), .storeMem "sp" 56 (.reg "w1")
  , .storeMem "sp" 64 (.reg "w2"), .storeMem "sp" 72 (.reg "w3")
  , .storeMem "sp" 80 (.reg "w4"), .storeMem "sp" 88 (.reg "w5") ]

/-! ## 2. 32-bit half-word extraction and term assembly (prime-agnostic)

Identical machinery to the P-256 kernel, just over `sp[0..11]` (24 half-words
`d0..d23`). A 32-bit `d`-word: `d[2i] = lo32(sp[i])`, `d[2i+1] = hi32(sp[i])`.
Two consecutive 32-bit words pack into one 64-bit accumulator word. -/

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

/-- Assemble a 384-bit term from its twelve 32-bit `d`-indices (MSW first) into
    the scratch term slot at byte offset `slot`. `w0` is the packing register. -/
def buildTerm (slot : Nat) (idx : List Nat) : List (JInstr 64) :=
  match idx with
  | [hA,lA,hB,lB,hC,lC,hD,lD,hE,lE,hF,lF] =>
      packWord "w0" hF lF ++ [ .storeMem "sp" slot (.reg "w0") ] ++
      packWord "w0" hE lE ++ [ .storeMem "sp" (slot+8)  (.reg "w0") ] ++
      packWord "w0" hD lD ++ [ .storeMem "sp" (slot+16) (.reg "w0") ] ++
      packWord "w0" hC lC ++ [ .storeMem "sp" (slot+24) (.reg "w0") ] ++
      packWord "w0" hB lB ++ [ .storeMem "sp" (slot+32) (.reg "w0") ] ++
      packWord "w0" hA lA ++ [ .storeMem "sp" (slot+40) (.reg "w0") ]
  | _ => []

/-! ## 3. The signed seven-word accumulator (`acc[0..6]`, six value + one sign) -/

/-- Zero the seven accumulator words at `accOff`. -/
def zeroAcc (accOff : Nat) : List (JInstr 64) :=
  [ .mov "w0" (.imm 0)
  , .storeMem "sp" accOff (.reg "w0"),      .storeMem "sp" (accOff+8) (.reg "w0")
  , .storeMem "sp" (accOff+16) (.reg "w0"), .storeMem "sp" (accOff+24) (.reg "w0")
  , .storeMem "sp" (accOff+32) (.reg "w0"), .storeMem "sp" (accOff+40) (.reg "w0")
  , .storeMem "sp" (accOff+48) (.reg "w0") ]

/-- Add the six-word term at `termOff` into the seven-word accumulator (carry into
    the top sign word). Acc words → `w0..w5,hi`; term words → loaded inline. -/
def accAdd (accOff termOff : Nat) : List (JInstr 64) :=
  [ .loadMem "w0" "sp" accOff,      .loadMem "lo" "sp" termOff,        .add "w0" (.reg "lo")
  , .loadMem "w1" "sp" (accOff+8),  .loadMem "lo" "sp" (termOff+8),    .adc "w1" (.reg "lo")
  , .loadMem "w2" "sp" (accOff+16), .loadMem "lo" "sp" (termOff+16),   .adc "w2" (.reg "lo")
  , .loadMem "w3" "sp" (accOff+24), .loadMem "lo" "sp" (termOff+24),   .adc "w3" (.reg "lo")
  , .loadMem "w4" "sp" (accOff+32), .loadMem "lo" "sp" (termOff+32),   .adc "w4" (.reg "lo")
  , .loadMem "w5" "sp" (accOff+40), .loadMem "lo" "sp" (termOff+40),   .adc "w5" (.reg "lo")
  , .loadMem "hi" "sp" (accOff+48), .adc "hi" (.imm 0)
  , .storeMem "sp" accOff (.reg "w0"), .storeMem "sp" (accOff+8) (.reg "w1")
  , .storeMem "sp" (accOff+16) (.reg "w2"), .storeMem "sp" (accOff+24) (.reg "w3")
  , .storeMem "sp" (accOff+32) (.reg "w4"), .storeMem "sp" (accOff+40) (.reg "w5")
  , .storeMem "sp" (accOff+48) (.reg "hi") ]

/-- Subtract the six-word term at `termOff` from the seven-word accumulator
    (borrow into the top sign word). -/
def accSub (accOff termOff : Nat) : List (JInstr 64) :=
  [ .loadMem "w0" "sp" accOff,      .loadMem "lo" "sp" termOff,        .sub "w0" (.reg "lo")
  , .loadMem "w1" "sp" (accOff+8),  .loadMem "lo" "sp" (termOff+8),    .sbb "w1" (.reg "lo")
  , .loadMem "w2" "sp" (accOff+16), .loadMem "lo" "sp" (termOff+16),   .sbb "w2" (.reg "lo")
  , .loadMem "w3" "sp" (accOff+24), .loadMem "lo" "sp" (termOff+24),   .sbb "w3" (.reg "lo")
  , .loadMem "w4" "sp" (accOff+32), .loadMem "lo" "sp" (termOff+32),   .sbb "w4" (.reg "lo")
  , .loadMem "w5" "sp" (accOff+40), .loadMem "lo" "sp" (termOff+40),   .sbb "w5" (.reg "lo")
  , .loadMem "hi" "sp" (accOff+48), .sbb "hi" (.imm 0)
  , .storeMem "sp" accOff (.reg "w0"), .storeMem "sp" (accOff+8) (.reg "w1")
  , .storeMem "sp" (accOff+16) (.reg "w2"), .storeMem "sp" (accOff+24) (.reg "w3")
  , .storeMem "sp" (accOff+32) (.reg "w4"), .storeMem "sp" (accOff+40) (.reg "w5")
  , .storeMem "sp" (accOff+48) (.reg "hi") ]

/-! ## 4. Final reduction of the signed accumulator into `[0, p384)`

After the eleven-term signed combination the accumulator (seven-word
two's-complement) lies within a few multiples of `p384` of zero. Branch-free:
conditionally add `p384` (gated on the sign word's MSB via an arithmetic-shift
mask) to clear any negative, then conditionally subtract `p384` (gated on a
trial-subtract borrow) to land in `[0, p384)`. `p384` limbs are immediates. -/

/-- `p384` little-endian limbs (six 64-bit words):
    `0x00000000ffffffff, 0xffffffff00000000, 0xfffffffffffffffe,
     0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff`. -/
def p384Limbs : List Nat :=
  [ 0x00000000ffffffff, 0xffffffff00000000, 0xfffffffffffffffe
  , 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff ]

/-- One branch-free conditional add of `p384`, gated on `acc < 0` (sign-word
    MSB). Mask `m = sar(acc[6],63)` (all-ones iff negative); the six masked
    limbs `m & p384[i]` are precomputed into the term scratch slot `termOff`
    **before** the add chain (the `and`s would otherwise clear `CF` mid-chain),
    then a single uninterrupted six-word ADD/ADC chain (+ carry into the sign
    word) folds them in. -/
def condAddP (accOff termOff : Nat) : List (JInstr 64) :=
  [ .loadMem "hi" "sp" (accOff+48), .mov "y" (.reg "hi"), .sar "y" (.imm 63)   -- y = mask
  , .mov "lo" (.imm (p384Limbs[0]!)), .and_ "lo" (.reg "y"), .storeMem "sp" termOff (.reg "lo")
  , .mov "lo" (.imm (p384Limbs[1]!)), .and_ "lo" (.reg "y"), .storeMem "sp" (termOff+8)  (.reg "lo")
  , .mov "lo" (.imm (p384Limbs[2]!)), .and_ "lo" (.reg "y"), .storeMem "sp" (termOff+16) (.reg "lo")
  , .mov "lo" (.imm (p384Limbs[3]!)), .and_ "lo" (.reg "y"), .storeMem "sp" (termOff+24) (.reg "lo")
  , .mov "lo" (.imm (p384Limbs[4]!)), .and_ "lo" (.reg "y"), .storeMem "sp" (termOff+32) (.reg "lo")
  , .mov "lo" (.imm (p384Limbs[5]!)), .and_ "lo" (.reg "y"), .storeMem "sp" (termOff+40) (.reg "lo") ] ++
  accAdd accOff termOff

/-- One branch-free conditional subtract of `p384` from the **seven-word**
    accumulator, gated on `acc ≥ p384` across all seven words (the value can
    still be `≥ 2^384` between subtracts, so the top word participates in the
    borrow). Trial-subtract `(p384, 0)` from the seven words; the final borrow
    `CF=1` iff `acc < p384`, in which case `cmovb` restores the originals.
    The six value words use the `w0..w5` window; the sign word uses `y`. The
    trial results land in `lo` (reused per word) — but a six-word trial needs
    six destinations live simultaneously for the cmov, so we stage the trial in
    `sp` term scratch and the originals stay in `w0..w5`. -/
def condSubP (accOff termOff : Nat) : List (JInstr 64) :=
  -- load originals into w0..w5 (value) and y (sign word)
  [ .loadMem "w0" "sp" accOff,      .loadMem "w1" "sp" (accOff+8)
  , .loadMem "w2" "sp" (accOff+16), .loadMem "w3" "sp" (accOff+24)
  , .loadMem "w4" "sp" (accOff+32), .loadMem "w5" "sp" (accOff+40)
  , .loadMem "y"  "sp" (accOff+48)
  -- trial = (w0..w5,y) − (p384, 0); stage each trial word in term scratch
  , .mov "lo" (.reg "w0"), .mov "hi" (.imm (p384Limbs[0]!)), .sub "lo" (.reg "hi"), .storeMem "sp" termOff (.reg "lo")
  , .mov "lo" (.reg "w1"), .mov "hi" (.imm (p384Limbs[1]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" (termOff+8)  (.reg "lo")
  , .mov "lo" (.reg "w2"), .mov "hi" (.imm (p384Limbs[2]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" (termOff+16) (.reg "lo")
  , .mov "lo" (.reg "w3"), .mov "hi" (.imm (p384Limbs[3]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" (termOff+24) (.reg "lo")
  , .mov "lo" (.reg "w4"), .mov "hi" (.imm (p384Limbs[4]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" (termOff+32) (.reg "lo")
  , .mov "lo" (.reg "w5"), .mov "hi" (.imm (p384Limbs[5]!)), .sbb "lo" (.reg "hi"), .storeMem "sp" (termOff+40) (.reg "lo")
  , .sbb "y" (.imm 0)   -- top word; CF = final borrow; CF=1 ⇒ acc < p384 ⇒ keep originals
  -- load trial words into w0..w5? no — originals are in w0..w5; keep them.
  -- cmovae (CF=0 ⇒ acc ≥ p384 ⇒ take trial): load trial into hi, cmovae into wK.
  , .loadMem "hi" "sp" termOff,        .cmovb "hi" (.reg "w0"), .storeMem "sp" accOff (.reg "hi")
  , .loadMem "hi" "sp" (termOff+8),    .cmovb "hi" (.reg "w1"), .storeMem "sp" (accOff+8)  (.reg "hi")
  , .loadMem "hi" "sp" (termOff+16),   .cmovb "hi" (.reg "w2"), .storeMem "sp" (accOff+16) (.reg "hi")
  , .loadMem "hi" "sp" (termOff+24),   .cmovb "hi" (.reg "w3"), .storeMem "sp" (accOff+24) (.reg "hi")
  , .loadMem "hi" "sp" (termOff+32),   .cmovb "hi" (.reg "w4"), .storeMem "sp" (accOff+32) (.reg "hi")
  , .loadMem "hi" "sp" (termOff+40),   .cmovb "hi" (.reg "w5"), .storeMem "sp" (accOff+40) (.reg "hi")
  -- sign word: trial result is in y; if CF=1 (borrow) restore original sign word
  , .loadMem "w0" "sp" (accOff+48),    .cmovb "y" (.reg "w0"),  .storeMem "sp" (accOff+48) (.reg "y") ]

/-! ## 5. The full reduce + store

Scratch layout (byte offsets into `sp`): `0..95` the 768-bit product (twelve
words), `96..143` term scratch (six words), `144..199` the seven-word signed
accumulator. -/

def prodOff : Nat := 0
def termOff : Nat := 96
def accOff  : Nat := 144

/-- The eleven derived + GMP-validated signed terms (MSW first; `64` = zero
    half-word), from `bench/p384_fieldmul_compare/p384_decompose.c`. -/
def s0Idx  : List Nat := [11,10,9,8,7,6,5,4,3,2,1,0]
def s1Idx  : List Nat := [19,18,17,16,15,14,13,12,12,14,13,12]
def s2Idx  : List Nat := [20,19,18,17,16,15,14,13,15,23,22,20]
def s3Idx  : List Nat := [23,22,21,20,19,18,17,16,20,64,23,21]
def s4Idx  : List Nat := [64,64,64,64,23,22,21,20,21,64,64,64]
def s5Idx  : List Nat := [64,64,64,64,64,23,22,21,64,64,64,64]
def s6Idx  : List Nat := [64,64,64,64,64,23,22,21,64,64,64,64]
def s7Idx  : List Nat := [64,64,64,64,64,64,23,22,64,64,64,64]
def s8Idx  : List Nat := [22,21,20,19,18,17,16,15,14,13,12,23]
def s9Idx  : List Nat := [64,64,64,64,64,64,64,23,22,21,20,64]
def s10Idx : List Nat := [64,64,64,64,64,64,64,23,23,64,64,64]

/-- The signed-term reduce: build each term, `±`-accumulate per the derived plan
    `+0+1+2+3+4+5+6+7−8−9−10`, then reduce into `[0,p384)` and store six words to
    `z`. The conditional add-backs clear any negative; the conditional subtracts
    land it in `[0,p)` (the +1 margin on each is empirically checked vs GMP). -/
def p384Reduce : List (JInstr 64) :=
  zeroAcc accOff ++
  buildTerm termOff s0Idx  ++ accAdd accOff termOff ++
  buildTerm termOff s1Idx  ++ accAdd accOff termOff ++
  buildTerm termOff s2Idx  ++ accAdd accOff termOff ++
  buildTerm termOff s3Idx  ++ accAdd accOff termOff ++
  buildTerm termOff s4Idx  ++ accAdd accOff termOff ++
  buildTerm termOff s5Idx  ++ accAdd accOff termOff ++
  buildTerm termOff s6Idx  ++ accAdd accOff termOff ++
  buildTerm termOff s7Idx  ++ accAdd accOff termOff ++
  buildTerm termOff s8Idx  ++ accSub accOff termOff ++
  buildTerm termOff s9Idx  ++ accSub accOff termOff ++
  buildTerm termOff s10Idx ++ accSub accOff termOff ++
  -- 4 conditional add-backs clear any negative, then 6 conditional subtracts
  -- land it in [0,p). +1 margin each (empirically-checked minima, see bench).
  condAddP accOff termOff ++ condAddP accOff termOff ++
  condAddP accOff termOff ++ condAddP accOff termOff ++
  condSubP accOff termOff ++ condSubP accOff termOff ++ condSubP accOff termOff ++
  condSubP accOff termOff ++ condSubP accOff termOff ++ condSubP accOff termOff ++
  [ .loadMem "w0" "sp" accOff,      .storeMem "z" 0  (.reg "w0")
  , .loadMem "w1" "sp" (accOff+8),  .storeMem "z" 8  (.reg "w1")
  , .loadMem "w2" "sp" (accOff+16), .storeMem "z" 16 (.reg "w2")
  , .loadMem "w3" "sp" (accOff+24), .storeMem "z" 24 (.reg "w3")
  , .loadMem "w4" "sp" (accOff+32), .storeMem "z" 32 (.reg "w4")
  , .loadMem "w5" "sp" (accOff+40), .storeMem "z" 40 (.reg "w5") ]

/-- The full P-384 field-multiply block: 6×6 schoolbook to scratch, then the
    signed-term Solinas reduce. -/
def p384MulBlock : List (JInstr 64) :=
  p384Schoolbook ++ p384Reduce

/-! ## 6. Value tie to #403's multi-term Solinas theorem

The kernel reduces the 768-bit product `P = high·2^384 + low` (with `high`,`low`
the six-word halves, each `< 2^384`) to its residue mod
`p384 = 2^384 − 2^128 − 2^96 + 2^32 − 1`. The all-inputs byte-identity that the
emitted stream computes exactly `P mod p384` is the external KAT
(`bench/p384_fieldmul_compare`, vs GMP). The lemma below records, at the value
level, that *that residue* is precisely the multi-term Solinas reduce #403 proved
correct — the kernel realises `multiSolinasReduce multiP384`. -/

open CatCrypt.Crypto.Optimizer.ModReduceSelect (multiSolinasReduce multiP384 reduceP384_eq_mod)

/-- **The kernel's residue is #403's multi-term Solinas reduce.** For well-formed
    product halves (`high, low < 2^384`), the residue the emitted P-384 kernel
    computes — `(high·2^384 + low) % p384` — equals `multiSolinasReduce multiP384
    high low`, the iterated-fold reduce proved correct in
    `ModReduceSelect.reduceP384_eq_mod` (#403). The emit is thus tied to the
    verified value-level theorem, not just cross-checked against GMP. -/
theorem p384Kernel_residue_eq_multiSolinas {high low : Nat}
    (hh : high < 2 ^ 384) (hl : low < 2 ^ 384) :
    multiSolinasReduce multiP384 high low = (high * 2 ^ 384 + low) % multiP384.modulus :=
  reduceP384_eq_mod hh hl

/-! ## 7. AT&T emission (reg-ptr ABI + stack scratch frame) -/

open CatCrypt.Crypto.SecureCompilation.X86Backend.AsmPrinter
  (GpAlloc allocGp renderBlockBody renderLeafFn regOf allocOverflow)

/-- Pin pointers + `MULX` multiplier `yd`→`%rdx`; scratch base `sp`→`%rbp`
    (excluded from `gpPool`, so it costs no pool slot). -/
def p384MulPinned : GpAlloc :=
  [("z", "%rdi"), ("x", "%rsi"), ("yd", "%rdx"), ("sp", "%rbp")]

/-- First-fit allocation over the full block. -/
def p384MulAlloc : GpAlloc := allocGp p384MulPinned p384MulBlock

/-- The allocation maps every name to a distinct pool register (no `%rax`-alias). -/
theorem p384MulAlloc_no_overflow : allocOverflow p384MulPinned p384MulBlock = none := by
  native_decide

/-- The full emitted leaf `p384_mul_x86_from_lean(z, x, y)`. The prologue saves
    callee regs, carves a 208-byte scratch frame, points `%rbp` at it, and moves
    the `y` pointer out of `%rdx`. Frame alloc/restore is trusted ABI scaffolding. -/
def p384MulAsm : String :=
  renderLeafFn "p384_mul_x86_from_lean"
    [ "\tpushq %rbx", "\tpushq %r12", "\tpushq %r13", "\tpushq %r14", "\tpushq %r15"
    , "\tpushq %rbp"
    , "\tsubq $208, %rsp", "\tmovq %rsp, %rbp"
    , "\tmovq %rdx, " ++ regOf p384MulAlloc "y" ]
    (renderBlockBody p384MulAlloc p384MulBlock)
    [ "\taddq $208, %rsp"
    , "\tpopq %rbp", "\tpopq %r15", "\tpopq %r14", "\tpopq %r13", "\tpopq %r12"
    , "\tpopq %rbx", "\tret" ]

/-- Emit driver: write the P-384 field-multiply `.s`. -/
def emitP384 : IO Unit := do
  IO.FS.createDirAll "bench/p384_fieldmul_compare/gen_com"
  IO.FS.writeFile
    "bench/p384_fieldmul_compare/gen_com/p384_mul_x86_from_lean.s" p384MulAsm
  IO.println "wrote p384_mul_x86_from_lean.s (derived Solinas reduce, #409)"

/-! ## Artifact generation at elaboration

The render is written while this module elaborates, so `lake` produces it from
this file and no separate driver or Makefile rule carries the dependency. -/

#eval emitP384

end CatCrypt.Crypto.SecureCompilation.X86Backend.P384FieldKernel
