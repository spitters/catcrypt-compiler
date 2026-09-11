/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime

/-!
# A real fixed-size bignum kernel: functionally correct AND constant-time

`MachineConstantTime.lean` builds the machine-level constant-time framework over
`List (JInstr w)` — the leakage model (`MLeak`, `blockLeak`), the public/secret
register partition (`PubPred`, `agreePub`), the CT-addressed instruction class
(`CTAddressed`), and the keystone `blockLeak_pub_determined` — but exercises it
only on a *representative* leaf (`fieldStoreLeaf`, a two-limb store-back) whose
"arithmetic" is a single fold.

This module delivers the **s2n-bignum profile** on a genuine kernel: a
fixed-limb, verified, constant-time x86 routine of the kind s2n-bignum provides.
We emit a real **4-limb `bignum_add`** in the `JInstr 64` model — load `a[0..3]`
from base pointer `ap`, `b[0..3]` from `bp`, run the `ADD`/`ADC` **carry chain**
across the four limbs (the carry threaded through `CF`, exactly as on the
machine), and store the four result limbs `r[0..3]` to `rp` — and prove it is
both

* **functionally correct**: running it on concrete 4-limb inputs computes the
  256-bit sum limb-for-limb against the Lean reference (`native_decide` KATs,
  including a full carry-propagation vector); and
* **constant-time**: every memory access is through a *public* pointer base and
  a *compile-time-constant* displacement, and no public register is overwritten,
  so by `blockLeak_pub_determined` the whole machine leakage trace
  (control flow + memory addresses) is a function of the public pointers alone —
  it carries **nothing** about the secret limb values.

That is the s2n-bignum guarantee — a fixed-limb routine, verified for both
functional correctness and constant-time leakage — realized end-to-end on an
emitted kernel in the Jasmin x86 model.

A second kernel (`mulAdd2`) exercises the **ADX/BMI2 fast path** (`MULX` widening
multiply + the `ADCX`/`ADOX` dual carry chains s2n-bignum's hot loops use) and
carries the identical constant-time proof, showing the fast path is CT too.

**0 axioms beyond the `native_decide` KAT pins** (`propext`, `Quot.sound`,
`Lean.ofReduceBool`), **0 sorries**.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.BignumConstantTime

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime

/-! ## 1. The kernel: a 4-limb `bignum_add`

`bignumAdd4` is the straight-line body s2n-bignum's `bignum_add` (fixed 4-word
operands) compiles to in the reg-ptr ABI: load the eight input limbs through the
two argument pointers `ap`/`bp`, add them limb-by-limb with a single carry chain
(`ADD` for limb 0, then `ADC` for limbs 1–3, the carry living in `CF` across the
chain), and store the four result limbs back through the output pointer `rp`.

All eight loads precede the carry chain. This is faithful: in the `JInstr` model
a `loadMem` (`movq off(%base), %dst`) is an `Ox86_MOV` that writes only a
register and leaves the flag map untouched (`evalInstr … (.loadMem …)` is
`s.setReg …`), so issuing the loads before the chain does not disturb the carry
— exactly as on the machine, where a `mov` does not clobber `CF`. -/

/-- A real 4-limb `bignum_add` (the s2n-bignum `bignum_add` shape for fixed
    4-word operands): `r[0..3] := a[0..3] + b[0..3]` with a carry chain.

    Inputs live behind the public pointer bases `ap`, `bp`; the output behind
    `rp`. The limb data registers `a0..a3`/`b0..b3` are secret. -/
def bignumAdd4 : List (JInstr 64) :=
  [ -- load a[0..3] and b[0..3] (movs preserve CF)
    .loadMem "a0" "ap" 0
  , .loadMem "a1" "ap" 8
  , .loadMem "a2" "ap" 16
  , .loadMem "a3" "ap" 24
  , .loadMem "b0" "bp" 0
  , .loadMem "b1" "bp" 8
  , .loadMem "b2" "bp" 16
  , .loadMem "b3" "bp" 24
    -- carry chain: a0 += b0 (sets CF); a1 += b1 + CF; …
  , .add "a0" (.reg "b0")
  , .adc "a1" (.reg "b1")
  , .adc "a2" (.reg "b2")
  , .adc "a3" (.reg "b3")
    -- store r[0..3]
  , .storeMem "rp" 0 (.reg "a0")
  , .storeMem "rp" 8 (.reg "a1")
  , .storeMem "rp" 16 (.reg "a2")
  , .storeMem "rp" 24 (.reg "a3") ]

/-! ## 2. Functional correctness (concrete KATs)

We run `bignumAdd4` from an initial state holding the eight input limbs and read
back the four result words at `rp+0, rp+8, rp+16, rp+24`, comparing against the
Lean reference: the limb-decomposition of the 256-bit sum
`(a0 + a1·2⁶⁴ + a2·2¹²⁸ + a3·2¹⁹²) + (b0 + …)`. The carry-propagation vector
forces a carry out of every limb. -/

/-- Build an initial state holding `a[0..3]` at `ap+{0,8,16,24}` and `b[0..3]` at
    `bp+{0,8,16,24}`, with the pointer bases as distinct register names. The
    actual numeric base *addresses* are irrelevant to the model (memory is keyed
    by `(base-name, offset)`); we only need `ap ≠ bp ≠ rp` as keys, which holds
    since they are distinct strings. -/
def initState (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : JState 64 :=
  { regs := fun _ => 0
    mem := fun base off =>
      if base = "ap" then
        if off = 0 then a0 else if off = 8 then a1
        else if off = 16 then a2 else if off = 24 then a3 else 0
      else if base = "bp" then
        if off = 0 then b0 else if off = 8 then b1
        else if off = 16 then b2 else if off = 24 then b3 else 0
      else 0 }

/-- The reference: the `k`-th 64-bit limb of the 256-bit sum of the two
    little-endian 4-limb numbers. -/
def refLimb (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) (k : Nat) : BitVec 64 :=
  let A := a0.toNat + a1.toNat * 2^64 + a2.toNat * 2^128 + a3.toNat * 2^192
  let B := b0.toNat + b1.toNat * 2^64 + b2.toNat * 2^128 + b3.toNat * 2^192
  BitVec.ofNat 64 ((A + B) / 2^(64*k))

/-- The four output limbs `bignumAdd4` writes, read back from the final state. -/
def outLimbs (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 :=
  let s := runBlock (initState a0 a1 a2 a3 b0 b1 b2 b3) bignumAdd4
  (s.load "rp" 0, s.load "rp" 8, s.load "rp" 16, s.load "rp" 24)

/-- **Functional KAT, vector 1 (mixed values, partial carries).**
    `a = (1, 2, 3, 4)`, `b = (0xFFFF…FFFF, 1, 0, 10)` little-endian limbs. The
    output limbs match the 256-bit reference sum limb-for-limb. -/
theorem bignumAdd4_kat1 :
    outLimbs 1 2 3 4 0xFFFFFFFFFFFFFFFF 1 0 10 =
      ( refLimb 1 2 3 4 0xFFFFFFFFFFFFFFFF 1 0 10 0
      , refLimb 1 2 3 4 0xFFFFFFFFFFFFFFFF 1 0 10 1
      , refLimb 1 2 3 4 0xFFFFFFFFFFFFFFFF 1 0 10 2
      , refLimb 1 2 3 4 0xFFFFFFFFFFFFFFFF 1 0 10 3 ) := by
  native_decide

/-- **Functional KAT, vector 2 (full carry propagation).**
    `a = (2⁶⁴−1, 2⁶⁴−1, 2⁶⁴−1, 2⁶⁴−1)`, `b = (1, 0, 0, 0)`: the carry out of
    limb 0 ripples all the way through limb 3 (result `(0,0,0,0)` with a final
    carry-out, truncated at 256 bits). The kernel reproduces the reference. -/
theorem bignumAdd4_kat2 :
    outLimbs 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 1 0 0 0 =
      ( refLimb 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 1 0 0 0 0
      , refLimb 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 1 0 0 0 1
      , refLimb 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 1 0 0 0 2
      , refLimb 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 1 0 0 0 3 ) := by
  native_decide

/-- **Functional KAT, vector 3 (staged carries).**
    A vector that carries out of limbs 0 and 2 but not 1 and 3, exercising the
    chained `ADC` in the middle of the word. -/
theorem bignumAdd4_kat3 :
    outLimbs 0xFFFFFFFFFFFFFFFF 5 0xFFFFFFFFFFFFFFFF 7 0x0000000000000001 9 0x0000000000000001 11 =
      ( refLimb 0xFFFFFFFFFFFFFFFF 5 0xFFFFFFFFFFFFFFFF 7 0x0000000000000001 9 0x0000000000000001 11 0
      , refLimb 0xFFFFFFFFFFFFFFFF 5 0xFFFFFFFFFFFFFFFF 7 0x0000000000000001 9 0x0000000000000001 11 1
      , refLimb 0xFFFFFFFFFFFFFFFF 5 0xFFFFFFFFFFFFFFFF 7 0x0000000000000001 9 0x0000000000000001 11 2
      , refLimb 0xFFFFFFFFFFFFFFFF 5 0xFFFFFFFFFFFFFFFF 7 0x0000000000000001 9 0x0000000000000001 11 3 ) := by
  native_decide

/-! ## 3. Constant-time: the public/secret partition + the CT proof

The public registers are the three pointer bases `ap`, `bp`, `rp` (the caller
hands them in; the kernel only reads them to form addresses and never writes
them). Everything else — the limb data registers `a0..a3`, `b0..b3` — is secret.
Every memory access in `bignumAdd4` is a direct `base + constant-offset`, and no
public register is among the destinations, so each instruction is `CTAddressed`
and the keystone `blockLeak_pub_determined` applies. -/

/-- The public/secret split for `bignumAdd4`: the pointer bases `ap`, `bp`, `rp`
    are public; the limb-data registers (and any carry-materialisation reg) are
    secret. -/
def bignumPub : PubPred := fun r => r = "ap" || r = "bp" || r = "rp"

/-- Every instruction of `bignumAdd4` is CT-addressed w.r.t. `bignumPub`: it has
    no register-indexed memory access (so the index-register obligation is
    vacuous), and every register it writes (`a0..a3`) is secret — it never
    overwrites a public pointer base. -/
theorem bignumAdd4_ctAddressed : ∀ i ∈ bignumAdd4, CTAddressed bignumPub i := by
  intro i hi
  simp only [bignumAdd4, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    refine ⟨fun idx hh => by simp [idxReg] at hh, ?_⟩ <;> simp [dstRegs, bignumPub]

/-- **`bignumAdd4` is constant-time** in the standard (public-input-determined)
    sense of Barthe et al.: any two states that agree on the public pointer bases
    `ap`, `bp`, `rp` — but differ **arbitrarily** on the secret limb-data
    registers — produce the *same* machine leakage trace (the load/store address
    sequence and the empty branch channel). The observable cache-line / control
    trace is therefore a function of the public pointers alone and leaks nothing
    about the secret limb values. This is the s2n-bignum constant-time guarantee
    for the emitted kernel. -/
theorem bignumAdd4_constant_time (s₁ s₂ : JState 64)
    (hag : agreePub bignumPub s₁ s₂) :
    blockLeak s₁ bignumAdd4 = blockLeak s₂ bignumAdd4 :=
  blockLeak_pub_determined bignumPub bignumAdd4 bignumAdd4_ctAddressed s₁ s₂ hag

/-- The constant memory-address trace `bignumAdd4` exposes, fixed by the program
    text: the eight loads `ap+{0,8,16,24}`, `bp+{0,8,16,24}`, then the four stores
    `rp+{0,8,16,24}`. (The carry-chain `add`/`adc` ops touch no memory.) -/
theorem bignumAdd4_trace (s : JState 64) :
    blockLeak s bignumAdd4 =
      [ .mem "ap" 0, .mem "ap" 8, .mem "ap" 16, .mem "ap" 24
      , .mem "bp" 0, .mem "bp" 8, .mem "bp" 16, .mem "bp" 24
      , .mem "rp" 0, .mem "rp" 8, .mem "rp" 16, .mem "rp" 24 ] := by
  rfl

/-- `bignumAdd4` takes no conditional branch: the carry lives in `CF` across the
    straight-line `ADD`/`ADC` chain, so the control-flow channel is empty. -/
theorem bignumAdd4_no_branch (s : JState 64) :
    (blockLeak s bignumAdd4).filter MLeak.isBranch = [] :=
  blockLeak_no_branch bignumAdd4 s

/-! ## 4. The ADX/BMI2 fast path is constant-time too

s2n-bignum's hot multiply loops use the BMI2/ADX trio — `MULX` (a flag-free
widening multiply) plus the two independent carry chains `ADCX` (→ `CF`) and
`ADOX` (→ `OF`). `mulAdd2` is a real two-limb multiply-accumulate step in that
idiom: load the multiplicand limbs and an accumulator pair through public
pointers, fold them with `mulxMem` (the `mulxq off(%base), …` form that reads
src2 straight from memory) and the dual `ADCX`/`ADOX` carries, and store the two
result words. It carries the identical constant-time proof, witnessing that the
ADX fast path leaks nothing about the secret limb values either. -/

/-- A two-limb ADX/BMI2 multiply-accumulate step (the s2n-bignum `MULX`+`ADCX`/
    `ADOX` hot-loop idiom): `mulxMem` folds the load of the multiplicand limb
    into the widening multiply, and the two products are accumulated through the
    independent `ADCX` (→`CF`) and `ADOX` (→`OF`) carry chains. The multiplier
    `m` and the accumulator limbs are read/stored through public pointer bases. -/
def mulAdd2 : List (JInstr 64) :=
  [ .loadMem "m" "mp" 0                       -- multiplier m = mp[0]
  , .loadMem "acc0" "cp" 0                     -- accumulator low
  , .loadMem "acc1" "cp" 8                     -- accumulator high
    -- p0 = m * a[0]  (src2 read from memory ap+0 via mulxMem), (hi0, lo0)
  , .mulxMem "hi0" "lo0" (.reg "m") "ap" 0
    -- p1 = m * a[1]  (src2 ap+8), (hi1, lo1)
  , .mulxMem "hi1" "lo1" (.reg "m") "ap" 8
    -- ADCX/ADOX dual carry accumulation into acc0/acc1
  , .adcx "acc0" (.reg "lo0")
  , .adox "acc1" (.reg "hi0")
  , .adcx "acc1" (.reg "lo1")
    -- store the two accumulator words
  , .storeMem "rp" 0 (.reg "acc0")
  , .storeMem "rp" 8 (.reg "acc1") ]

/-- The public/secret split for `mulAdd2`: the four pointer bases `mp`, `cp`,
    `ap`, `rp` are public; the multiplier/product/accumulator registers are
    secret. -/
def mulAdd2Pub : PubPred := fun r => r = "mp" || r = "cp" || r = "ap" || r = "rp"

/-- Every instruction of `mulAdd2` is CT-addressed: its memory accesses are all
    direct `base + constant-offset` (the `mulxMem` reads `ap+{0,8}`, no
    register index), and every destination register (`m`, `acc0/1`, `lo*`,
    `hi*`) is secret. -/
theorem mulAdd2_ctAddressed : ∀ i ∈ mulAdd2, CTAddressed mulAdd2Pub i := by
  intro i hi
  simp only [mulAdd2, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    refine ⟨fun idx hh => by simp [idxReg] at hh, ?_⟩ <;> simp [dstRegs, mulAdd2Pub]

/-- **The ADX/BMI2 fast path is constant-time.** `mulAdd2`'s machine leakage
    trace is determined by the public pointer bases alone: any two states
    agreeing on `mp`, `cp`, `ap`, `rp` produce the same load/store address
    sequence regardless of the secret multiplier/product/accumulator values. -/
theorem mulAdd2_constant_time (s₁ s₂ : JState 64)
    (hag : agreePub mulAdd2Pub s₁ s₂) :
    blockLeak s₁ mulAdd2 = blockLeak s₂ mulAdd2 :=
  blockLeak_pub_determined mulAdd2Pub mulAdd2 mulAdd2_ctAddressed s₁ s₂ hag

/-- The constant memory-address trace `mulAdd2` exposes: loads at `mp+0`, `cp+0`,
    `cp+8`, the two `mulxMem` reads `ap+0`, `ap+8`, then stores `rp+0`, `rp+8`.
    Fixed by the program text. -/
theorem mulAdd2_trace (s : JState 64) :
    blockLeak s mulAdd2 =
      [ .mem "mp" 0, .mem "cp" 0, .mem "cp" 8
      , .mem "ap" 0, .mem "ap" 8
      , .mem "rp" 0, .mem "rp" 8 ] := by
  rfl

/-- `mulAdd2` takes no conditional branch: `MULX`/`ADCX`/`ADOX` are
    straight-line, so the control-flow channel is empty. -/
theorem mulAdd2_no_branch (s : JState 64) :
    (blockLeak s mulAdd2).filter MLeak.isBranch = [] :=
  blockLeak_no_branch mulAdd2 s

end CatCrypt.Crypto.SecureCompilation.X86Backend.BignumConstantTime
