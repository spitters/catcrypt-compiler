/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmLowering
public import CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmLowering

/-!
# The whole SHA-256 block compression, lowered through the owned AArch64 backend

`ArmLowering.lean` lowers the ChaCha quarter-round through the 32-bit
`W`-register GP-ALU subset; `ArmBignumKernel.lean` lowers s2n's
`bignum_add_p256` through the 64-bit `X`-register path. This module is a
**whole-primitive** A64 functional benchmark: the complete SHA-256 (FIPS 180-4
§6.2) block compression `f(H, M) = H'` — the 64-round transformation over the
eight chaining words with the message schedule `W[0..63]` and the round constants
`K[0..63]` — built as a single register-named `AOp` block, lowered through the
verified `armBlock_lowering_denote` theorem, run on the `AState` 32-bit machine,
and pinned **byte-identical to the official FIPS 180-4 KAT** (the `"abc"`
one-block digest `ba7816bf…f20015ad`).

SHA-256 is pure GP-ALU — `ADD` (wrapping `u32`), `AND`/`ORR`/`EOR`, the native
right-rotate `ROR` (the `Σ`/`σ` mixers), and the logical shift `LSR` (`σ`'s third
term) — so the lowering is the *same* one-rule-per-constructor pass `toAInst`, and
the whole 64-round body rides the existing `armBlock_lowering_denote` (no new
instruction, no new model op, no new custom axiom). The A64 `ROR` makes each
`rotr` a single instruction (vs the x86 SIMD `shl;shr;or` idiom) — and SHA-256's
`Ch`/`Maj` are written in the **`not`-free** algebraic forms

    Ch(e,f,g)  = g ^ (e & (f ^ g))
    Maj(a,b,c) = (a & b) ^ (c & (a ^ b))

so the body needs no complement op (the dialect's `not` is unused): every op is
one of `ADD`/`AND`/`ORR`/`EOR`/`ROR`/`LSR`.

## What is emitted, and the trust boundary

* `compressBlock`: the verified `AOp` body for one SHA-256 block — the 48-step
  message-schedule expansion `W[16..63]` followed by the 64 rounds and the 8-word
  feed-forward, over a register file (working words `a..h`, the 16-word sliding
  schedule window `w0..w15`, the per-round constants `k0..k63` and scratch). It is
  a straight-line register-to-register block.
* `compress_lowering_correct`: `armBlock_lowering_denote` on this body — running
  the lowered `AInst` block on the `AState` model equals the direct machine fold,
  for every initial state (no new custom axioms).
* `sha256_abc_kat`: the value KAT — seeding the register file with the `"abc"`
  one-block message words `M[0..15]` (the padded block) and the SHA-256 initial
  hash `H0`, running the lowered body, and reading the eight output words
  `out0..out7` back: byte-identical to the FIPS 180-4 digest
  `ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c b410ff61 f20015ad`.

The seeding of `W[t]` (the message words and the schedule literals) and `K[t]`
(the round constants) into named registers is the trusted ABI scaffolding — the
A64-leaf load posture of `ArmBignumKernel`'s `ldp`s and the x86 leaf-prologue.
The emitted leaf `.s` (`bench/arm_compare/sha256_a64_emit.lean`) keeps `a..h` and
the schedule window register-resident and loads `K[t]`/`M[t]` from the argument
buffers; its qemu-aarch64 KAT against the same FIPS digest is in
`bench/arm_compare/` (`sha256-a64-kat`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmSha256Kernel

open CatCrypt.Crypto.SecureCompilation.ARMBackend

/-! ## 1. SHA-256 round constants `K[0..63]` (FIPS 180-4 §4.2.2) -/

/-- The 64 SHA-256 round constants (the first 32 bits of the fractional parts of
    the cube roots of the first 64 primes), FIPS 180-4 §4.2.2. -/
def k256 : Nat → Nat
  |  0 => 0x428a2f98 |  1 => 0x71374491 |  2 => 0xb5c0fbcf |  3 => 0xe9b5dba5
  |  4 => 0x3956c25b |  5 => 0x59f111f1 |  6 => 0x923f82a4 |  7 => 0xab1c5ed5
  |  8 => 0xd807aa98 |  9 => 0x12835b01 | 10 => 0x243185be | 11 => 0x550c7dc3
  | 12 => 0x72be5d74 | 13 => 0x80deb1fe | 14 => 0x9bdc06a7 | 15 => 0xc19bf174
  | 16 => 0xe49b69c1 | 17 => 0xefbe4786 | 18 => 0x0fc19dc6 | 19 => 0x240ca1cc
  | 20 => 0x2de92c6f | 21 => 0x4a7484aa | 22 => 0x5cb0a9dc | 23 => 0x76f988da
  | 24 => 0x983e5152 | 25 => 0xa831c66d | 26 => 0xb00327c8 | 27 => 0xbf597fc7
  | 28 => 0xc6e00bf3 | 29 => 0xd5a79147 | 30 => 0x06ca6351 | 31 => 0x14292967
  | 32 => 0x27b70a85 | 33 => 0x2e1b2138 | 34 => 0x4d2c6dfc | 35 => 0x53380d13
  | 36 => 0x650a7354 | 37 => 0x766a0abb | 38 => 0x81c2c92e | 39 => 0x92722c85
  | 40 => 0xa2bfe8a1 | 41 => 0xa81a664b | 42 => 0xc24b8b70 | 43 => 0xc76c51a3
  | 44 => 0xd192e819 | 45 => 0xd6990624 | 46 => 0xf40e3585 | 47 => 0x106aa070
  | 48 => 0x19a4c116 | 49 => 0x1e376c08 | 50 => 0x2748774c | 51 => 0x34b0bcb5
  | 52 => 0x391c0cb3 | 53 => 0x4ed8aa4a | 54 => 0x5b9cca4f | 55 => 0x682e6ff3
  | 56 => 0x748f82ee | 57 => 0x78a5636f | 58 => 0x84c87814 | 59 => 0x8cc70208
  | 60 => 0x90befffa | 61 => 0xa4506ceb | 62 => 0xbef9a3f7 | 63 => 0xc67178f2
  |  _ => 0

/-- The SHA-256 initial hash value `H0[0..7]` (FIPS 180-4 §5.3.3). -/
def h0 : Nat → Nat
  | 0 => 0x6a09e667 | 1 => 0xbb67ae85 | 2 => 0x3c6ef372 | 3 => 0xa54ff53a
  | 4 => 0x510e527f | 5 => 0x9b05688c | 6 => 0x1f83d9ab | 7 => 0x5be0cd19
  | _ => 0

/-! ## 2. Register-name scheme for the compression's register file

Every value lives in a uniquely named SSA register:
* `a..h`  — the eight working words `wkName 0..7` (`a,b,c,d,e,f,g,h`);
* `w{i}`  — schedule slot `W[i]` (`i = 0..63`); the sliding window is realised by
  giving each `W[t]` its own name (so the verified block is pure straight-line
  SSA — register reuse is the printer's allocation problem, handled there);
* `k{t}`  — the round constant `K[t]` (`t = 0..63`), seeded as an input;
* `s{n}`  — a fresh scratch name per binding (`fresh` counter), so the block is
  single-assignment.

The `not`-free `Ch`/`Maj` keep the op set to `ADD`/`AND`/`ORR`/`EOR`/`ROR`/`LSR`. -/

/-- Name of working word `j` (`0..7` ↔ `a..h`). -/
def wkName : Nat → String
  | 0 => "a" | 1 => "b" | 2 => "c" | 3 => "d"
  | 4 => "e" | 5 => "f" | 6 => "g" | 7 => "h"
  | _ => "a"

/-- Name of schedule slot `W[i]`. -/
def wName (i : Nat) : String := "w" ++ toString i

/-- Name of round-constant input `K[t]`. -/
def kName (t : Nat) : String := "k" ++ toString t

/-- Name of the `n`-th fresh scratch register. -/
def scName (n : Nat) : String := "s" ++ toString n

/-! ## 3. The builder: a state-threaded straight-line `AOp` emitter

We thread a *fresh-name counter* and accumulate `AOp`s in reverse. Each helper
emits its ops and returns the name holding its result plus the bumped counter.
Because every binding gets a fresh `s{n}` name (or writes one of the fixed
`a..h`/`w{i}` names), the block is single-assignment and rides the verified
`armBlock_lowering_denote` directly. -/

/-- Builder state: ops emitted so far (reversed) and the next fresh index. -/
structure BState where
  /-- Accumulated ops, in reverse order. -/
  ops : List AOp
  /-- Next fresh scratch index. -/
  fresh : Nat

/-- Emit one binary op `dst := a <op> b` (record it). -/
def emit (st : BState) (mk : String → String → String → AOp)
    (dst a b : String) : BState :=
  { st with ops := mk dst a b :: st.ops }

/-- Allocate a fresh scratch name and bump the counter. -/
def freshName (st : BState) : String × BState :=
  (scName st.fresh, { st with fresh := st.fresh + 1 })

/-- Emit `dst := ROR a, #imm` into a fresh name; return that name. -/
def emitRor (st : BState) (a : String) (imm : Nat) : String × BState :=
  let (d, st1) := freshName st
  (d, { st1 with ops := AOp.rotr d a imm :: st1.ops })

/-- Emit `dst := LSR a, #imm` into a fresh name; return that name. -/
def emitShr (st : BState) (a : String) (imm : Fin 32) : String × BState :=
  let (d, st1) := freshName st
  (d, { st1 with ops := AOp.shr d a imm :: st1.ops })

/-- Emit `dst := a <bin> b` into a fresh name; return that name. -/
def emitBin (st : BState) (mk : String → String → String → AOp)
    (a b : String) : String × BState :=
  let (d, st1) := freshName st
  (d, { st1 with ops := mk d a b :: st1.ops })

/-! ### Σ/σ mixers and Ch/Maj (the `not`-free forms) -/

/-- `Σ0(x) = ror(x,2) ^ ror(x,13) ^ ror(x,22)`. -/
def bigSig0 (st : BState) (x : String) : String × BState :=
  let (r1, st) := emitRor st x 2
  let (r2, st) := emitRor st x 13
  let (r3, st) := emitRor st x 22
  let (t,  st) := emitBin st AOp.xor r1 r2
  emitBin st AOp.xor t r3

/-- `Σ1(x) = ror(x,6) ^ ror(x,11) ^ ror(x,25)`. -/
def bigSig1 (st : BState) (x : String) : String × BState :=
  let (r1, st) := emitRor st x 6
  let (r2, st) := emitRor st x 11
  let (r3, st) := emitRor st x 25
  let (t,  st) := emitBin st AOp.xor r1 r2
  emitBin st AOp.xor t r3

/-- `σ0(x) = ror(x,7) ^ ror(x,18) ^ (x >> 3)`. -/
def smallSig0 (st : BState) (x : String) : String × BState :=
  let (r1, st) := emitRor st x 7
  let (r2, st) := emitRor st x 18
  let (r3, st) := emitShr st x 3
  let (t,  st) := emitBin st AOp.xor r1 r2
  emitBin st AOp.xor t r3

/-- `σ1(x) = ror(x,17) ^ ror(x,19) ^ (x >> 10)`. -/
def smallSig1 (st : BState) (x : String) : String × BState :=
  let (r1, st) := emitRor st x 17
  let (r2, st) := emitRor st x 19
  let (r3, st) := emitShr st x 10
  let (t,  st) := emitBin st AOp.xor r1 r2
  emitBin st AOp.xor t r3

/-- `Ch(e,f,g) = g ^ (e & (f ^ g))` — the `not`-free choose. -/
def chFn (st : BState) (e f g : String) : String × BState :=
  let (t1, st) := emitBin st AOp.xor f g
  let (t2, st) := emitBin st AOp.and e t1
  emitBin st AOp.xor g t2

/-- `Maj(a,b,c) = (a & b) ^ (c & (a ^ b))` — the `not`-free majority. -/
def majFn (st : BState) (a b c : String) : String × BState :=
  let (t1, st) := emitBin st AOp.and a b
  let (t2, st) := emitBin st AOp.xor a b
  let (t3, st) := emitBin st AOp.and c t2
  emitBin st AOp.xor t1 t3

/-! ### 4. The message-schedule expansion `W[16..63]`

`W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]`, each `W[t]` written to its
own name `w{t}`. -/

/-- Emit `W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]` into name `w{t}`. -/
def schedStep (st : BState) (t : Nat) : BState :=
  let (s1, st) := smallSig1 st (wName (t - 2))
  let (s0, st) := smallSig0 st (wName (t - 15))
  let (a1, st) := emitBin st AOp.add s1 (wName (t - 7))
  let (a2, st) := emitBin st AOp.add a1 s0
  -- final add writes the fixed schedule name `w{t}`
  emit st AOp.add (wName t) a2 (wName (t - 16))

/-- Expand `W[16..63]` (48 steps). -/
def emitSched (st : BState) : BState :=
  (List.range 48).foldl (fun st i => schedStep st (i + 16)) st

/-! ### 5. One compression round (FIPS 180-4 §6.2.2)

`T1 = h + Σ1(e) + Ch(e,f,g) + K[t] + W[t]; T2 = Σ0(a) + Maj(a,b,c)`, then the
working-word shift `h=g; g=f; f=e; e=d+T1; d=c; c=b; b=a; a=T1+T2`. The shift is
realised by writing the eight fixed `a..h` names from temporaries (high to low),
matching the x86 emit's `cp` discipline. -/

/-- Emit one round `t`. -/
def roundStep (st : BState) (t : Nat) : BState :=
  let a := wkName 0; let b := wkName 1; let c := wkName 2; let d := wkName 3
  let e := wkName 4; let f := wkName 5; let g := wkName 6; let h := wkName 7
  -- T1 = h + Σ1(e) + Ch(e,f,g) + K[t] + W[t]
  let (s1, st) := bigSig1 st e
  let (ch, st) := chFn st e f g
  let (t1, st) := emitBin st AOp.add h s1
  let (t1, st) := emitBin st AOp.add t1 ch
  let (t1, st) := emitBin st AOp.add t1 (kName t)
  let (t1, st) := emitBin st AOp.add t1 (wName t)
  -- T2 = Σ0(a) + Maj(a,b,c)
  let (s0, st) := bigSig0 st a
  let (mj, st) := majFn st a b c
  let (t2, st) := emitBin st AOp.add s0 mj
  -- new e = d + T1 ; new a = T1 + T2  (into fresh temps, then shift)
  let (newE, st) := emitBin st AOp.add d t1
  let (newA, st) := emitBin st AOp.add t1 t2
  -- working-word shift (high to low): h←g, g←f, f←e, e←newE, d←c, c←b, b←a, a←newA
  let st := emit st (fun d s _ => AOp.mov d s) h g g
  let st := emit st (fun d s _ => AOp.mov d s) g f f
  let st := emit st (fun d s _ => AOp.mov d s) f e e
  let st := emit st (fun d s _ => AOp.mov d s) e newE newE
  let st := emit st (fun d s _ => AOp.mov d s) d c c
  let st := emit st (fun d s _ => AOp.mov d s) c b b
  let st := emit st (fun d s _ => AOp.mov d s) b a a
  emit st (fun d s _ => AOp.mov d s) a newA newA

/-- Run the 64 rounds. -/
def emitRounds (st : BState) : BState :=
  (List.range 64).foldl (fun st t => roundStep st t) st

/-! ### 6. The 8-word feed-forward `out[j] = H0[j] + working[j]`

The chaining-word inputs are seeded into names `in0..in7`; the output words are
the fixed names `out0..out7`. -/

/-- Name of input chaining word `H[j]`. -/
def inName (j : Nat) : String := "in" ++ toString j

/-- Name of output word `j`. -/
def outName (j : Nat) : String := "out" ++ toString j

/-- Emit `out[j] = H[j] + working[j]` for `j = 0..7`. -/
def emitFeed (st : BState) : BState :=
  (List.range 8).foldl
    (fun st j => emit st AOp.add (outName j) (inName j) (wkName j)) st

/-! ## 7. The whole SHA-256 compression `AOp` block -/

/-- The complete SHA-256 block compression as a straight-line `AOp` block:
    expand `W[16..63]`, run the 64 rounds, feed-forward. The ops are emitted in
    reverse during the build, so the final block is the reverse of `ops`. -/
def compressBlock : List AOp :=
  let st0 : BState := { ops := [], fresh := 0 }
  let st := emitSched st0
  let st := emitRounds st
  let st := emitFeed st
  st.ops.reverse

/-! ## 8. Lowering correctness (the lowering theorem instantiated)

`armBlock_lowering_denote` on the whole SHA-256 body: running the lowered `AInst`
block on the `AState` model equals the direct machine fold, for every initial
state. No new custom axioms. -/

/-- **Lowering correctness on the whole SHA-256 compression.** Running the lowered
    body on the A64 model equals the direct machine fold — `armBlock_lowering_denote`
    instantiated on `compressBlock`. -/
theorem compress_lowering_correct (s : AState) :
    runABlock s (lowerABlock compressBlock)
      = compressBlock.foldl (fun st op => evalAInst st (toAInst op)) s :=
  armBlock_lowering_denote compressBlock s

/-! ## 9. The FIPS 180-4 `"abc"` one-block KAT

The padded one-block message for `"abc"` (FIPS 180-4 §B.1):
`M = 0x61626380 0x00000000 … 0x00000018` (the 3 message bytes, the `0x80`
terminator, then zeros, then the 64-bit length `24`). We seed the 16 message
words into `w0..w15`, the round constants into `k0..k63`, and the initial hash
into `in0..in7` and `a..h`; running the lowered body and reading `out0..out7`
back must give the published digest `ba7816bf…f20015ad`. -/

/-- The padded `"abc"` one-block message words `M[0..15]` (FIPS 180-4 §B.1). -/
def abcMsg : Nat → Nat
  | 0 => 0x61626380 | 15 => 0x00000018 | _ => 0x00000000

/-- The initial `AState` for the `"abc"` KAT: schedule slots `w0..w15` ← the
    padded message words; working words `a..h` ← `H0`; chaining inputs
    `in0..in7` ← `H0`; round constants `k0..k63` ← `K[t]`. -/
def abcInit : AState :=
  { regs := fun r =>
      -- message words → w0..w15
      (List.range 16).foldr
        (fun i acc => if r = wName i then BitVec.ofNat 32 (abcMsg i) else acc)
      -- working words a..h ← H0, chaining inputs in0..in7 ← H0
      ((List.range 8).foldr
        (fun j acc =>
          if r = wkName j then BitVec.ofNat 32 (h0 j)
          else if r = inName j then BitVec.ofNat 32 (h0 j) else acc)
      -- round constants k0..k63 ← K[t]
        ((List.range 64).foldr
          (fun t acc => if r = kName t then BitVec.ofNat 32 (k256 t) else acc)
          0)) }

/-- The lowered-and-run SHA-256 compression on the `"abc"` block. -/
def abcRun : AState := runABlock abcInit (lowerABlock compressBlock)

/-- **SHA-256 FIPS 180-4 `"abc"` KAT.** The eight output words `out0..out7` equal
    the published one-block digest
    `ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c b410ff61 f20015ad`,
    byte-identical — the whole 64-round compression lowered through the owned A64
    backend produces the FIPS-correct digest. -/
theorem sha256_abc_kat :
    (abcRun.get "out0" = 0xba7816bf) ∧ (abcRun.get "out1" = 0x8f01cfea) ∧
    (abcRun.get "out2" = 0x414140de) ∧ (abcRun.get "out3" = 0x5dae2223) ∧
    (abcRun.get "out4" = 0xb00361a3) ∧ (abcRun.get "out5" = 0x96177a9c) ∧
    (abcRun.get "out6" = 0xb410ff61) ∧ (abcRun.get "out7" = 0xf20015ad) := by
  native_decide

end CatCrypt.Crypto.SecureCompilation.ARMBackend.ArmSha256Kernel
