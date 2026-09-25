/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

/-!
# The Grain LFSR constant generation of Poseidon

The procedure of `generate_parameters_grain.sage` (Grassi, Khovratovich,
Rechberger, Roy, Schofnegger, *Poseidon: A New Hash Function for Zero-Knowledge
Proof Systems*, USENIX Security 2021) that produces the round constants and the
Cauchy MDS matrix of a Poseidon instance, for a prime field and the S-box `x ^ α`.

An 80-bit LFSR with feedback `b₆₂ ⊕ b₅₁ ⊕ b₃₈ ⊕ b₂₃ ⊕ b₁₃ ⊕ b₀` is initialised with
the field type, S-box type, field size, width and round counts followed by thirty
ones, and run for 160 discarded steps. Its output is read in pairs; the second bit
of a pair is kept when the first is `1` (the self-shrinking generator). Each field
element is an `n`-bit output, most significant bit first: a round constant is
redrawn while it is `≥ p`, and the `2 t` points of the Cauchy matrix are reduced
modulo `p`.

`step` is one LFSR step. `block` computes sixteen steps at once with word
operations; `blockAgrees` compares it with sixteen applications of `step`, and is
evaluated as a static check where the constants are instantiated
(`Hash.Poseidon.BN254`). The loops draw from a fuel bound (`pairFuel` reads per
output, 64 draws per round constant); the reference procedure is unbounded.

## Main definitions

* `State`, `step`, `block`: the LFSR.
* `init`: the initialised state.
* `bits`, `fieldElem`, `fieldElems`, `reducedElems`: the output stream.
* `constants p n t rf rp`: the round constants and the Cauchy points.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hash.Poseidon.Grain

/-- The 80-bit Grain LFSR state. Entry `k` of the bit sequence is bit `k` of `lo`
    for `k < 64` and bit `k - 64` of `hi` for `64 ≤ k < 80`; the other bits of `hi`
    are zero. -/
structure State where
  /-- Entries `0 … 63`. -/
  lo : UInt64
  /-- Entries `64 … 79`. -/
  hi : UInt64

/-- One step of the Grain LFSR: the new bit `b₆₂ ⊕ b₅₁ ⊕ b₃₈ ⊕ b₂₃ ⊕ b₁₃ ⊕ b₀` is
    returned and appended as entry 79 while entry 0 is dropped. -/
def step (s : State) : Bool × State :=
  let x := s.lo
  let b := ((x >>> 62) ^^^ (x >>> 51) ^^^ (x >>> 38) ^^^ (x >>> 23) ^^^ (x >>> 13) ^^^ x) &&& 1
  (b == 1, ⟨(x >>> 1) ||| ((s.hi &&& 1) <<< 63), (s.hi >>> 1) ||| (b <<< 15)⟩)

/-- Sixteen steps at once: bit `j` of the returned word is the output of step `j`.
    Each of the sixteen new bits depends only on entries of the current state, since
    the largest tap is 62 and `62 + 15 < 80`; the entries `o … o + 15` are the low
    sixteen bits of `lo >>> o`, completed by `hi` for `o > 48`. -/
def block (s : State) : UInt64 × State :=
  let lo := s.lo
  let hi := s.hi
  let b := (((lo >>> 62) ||| (hi <<< 2)) ^^^ ((lo >>> 51) ||| (hi <<< 13)) ^^^ (lo >>> 38) ^^^
    (lo >>> 23) ^^^ (lo >>> 13) ^^^ lo) &&& 0xFFFF
  (b, ⟨(lo >>> 16) ||| (hi <<< 48), b⟩)

/-- `k` single steps: their outputs, the first as bit `0`, and the final state. -/
def steps : Nat → State → UInt64 × State
  | 0, s => (0, s)
  | k + 1, s =>
    let (b, s₁) := step s
    let (w, s₂) := steps k s₁
    ((w <<< 1) ||| (if b then 1 else 0), s₂)

/-- Whether `block` agrees with sixteen single steps on `m` consecutive blocks from
    `s`: outputs, `lo` and `hi`. -/
def blockAgrees : Nat → State → Bool
  | 0, _ => true
  | m + 1, s =>
    let (b, s₁) := block s
    let (w, s₂) := steps 16 s
    b == w && s₁.lo == s₂.lo && s₁.hi == s₂.hi && blockAgrees m s₁

/-- The `w` bits of `v`, most significant first. -/
def bitsMSB (w v : Nat) : List Bool := (List.range w).reverse.map v.testBit

/-- The 80 initial bits: the field type (2 bits), the S-box type (4 bits), the field
    size `n` (12 bits), the width `t` (12 bits), the full and partial round counts
    (10 bits each) and thirty ones. -/
def initBits (field sbox n t rf rp : Nat) : List Bool :=
  bitsMSB 2 field ++ bitsMSB 4 sbox ++ bitsMSB 12 n ++ bitsMSB 12 t ++ bitsMSB 10 rf ++
    bitsMSB 10 rp ++ List.replicate 30 true

/-- The natural whose bit `k` is entry `k` of the list. -/
def ofBitsLSB : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * ofBitsLSB bs

/-- The state holding the 80 entries of a bit list. -/
def ofBits (bs : List Bool) : State :=
  ⟨UInt64.ofNat (ofBitsLSB (bs.take 64)), UInt64.ofNat (ofBitsLSB (bs.drop 64))⟩

/-- `k` blocks, their output discarded. -/
def skipBlocks : Nat → State → State
  | 0, s => s
  | k + 1, s => skipBlocks k (block s).2

/-- The LFSR state after initialisation and the 160 discarded steps (ten blocks). -/
def init (field sbox n t rf rp : Nat) : State :=
  skipBlocks 10 (ofBits (initBits field sbox n t rf rp))

/-- The output stream: the LFSR state and the pending pairs of the current block,
    the next pair in the two low bits of `buf`. -/
structure Gen where
  /-- The LFSR state after the current block. -/
  s : State
  /-- The pending bits of the current block. -/
  buf : UInt64
  /-- The number of pending pairs. -/
  n : Nat

/-- The outputs of four pairs `x = c₀ o₀ c₁ o₁ c₂ o₂ c₃ o₃` (least significant bit
    first): their number and their value, first output most significant. -/
def byteOut (x : Nat) : Nat × Nat :=
  (List.range 4).foldl (fun (e : Nat × Nat) i =>
    if x.testBit (2 * i) then (e.1 + 1, 2 * e.2 + (x.testBit (2 * i + 1)).toNat) else e) (0, 0)

/-- `byteOut` for every byte. -/
def byteTable : Array (Nat × Nat) := (Array.range 256).map byteOut

/-- `k` output bits of the self-shrinking generator, accumulated most significant
    first onto `acc`: the LFSR output is read in pairs, and the second bit of a pair
    is output when the first is `1`. The stream is `s` preceded by the `n` pending
    pairs of `buf`; a new block is drawn when none is pending. While at least four
    pairs are pending and at least four bits are wanted, four pairs are read at once
    through `byteTable`. At most `fuel` such reads are made. -/
def bitsAux : (fuel k acc : Nat) → State → UInt64 → Nat → Nat × Gen
  | 0, _, acc, s, buf, n => (acc, ⟨s, buf, n⟩)
  | _ + 1, 0, acc, s, buf, n => (acc, ⟨s, buf, n⟩)
  | f + 1, k + 1, acc, s, _, 0 =>
    let (b, s') := block s
    bitsAux f (k + 1) acc s' b 8
  | f + 1, k + 1, acc, s, buf, n + 1 =>
    if 4 ≤ n + 1 ∧ 4 ≤ k + 1 then
      let e := byteTable[(buf &&& 0xFF).toNat]!
      bitsAux f (k + 1 - e.1) (acc * 2 ^ e.1 + e.2) s (buf >>> 8) (n - 3)
    else if buf &&& 1 == 1 then bitsAux f k (2 * acc + ((buf >>> 1) &&& 1).toNat) s (buf >>> 2) n
    else bitsAux f (k + 1) acc s (buf >>> 2) n

/-- `k` output bits from the stream `g`. -/
def bits (fuel k acc : Nat) (g : Gen) : Nat × Gen := bitsAux fuel k acc g.s g.buf g.n

/-- The pair budget of one `n`-bit output. -/
def pairFuel : Nat := 4096

/-- An `n`-bit output below `p`, by rejection: outputs `≥ p` are discarded. At most
    `fuel` outputs are drawn. -/
def fieldElem (p n : Nat) : (fuel : Nat) → Gen → Nat × Gen
  | 0, g => (0, g)
  | f + 1, g =>
    let (v, g') := bits pairFuel n 0 g
    if v < p then (v, g') else fieldElem p n f g'

/-- `count` rejection-sampled field elements. -/
def fieldElems (p n : Nat) : (count : Nat) → Gen → List Nat × Gen
  | 0, g => ([], g)
  | c + 1, g =>
    let (v, g₁) := fieldElem p n 64 g
    let (vs, g₂) := fieldElems p n c g₁
    (v :: vs, g₂)

/-- `count` `n`-bit outputs reduced modulo `p`. -/
def reducedElems (p n : Nat) : (count : Nat) → Gen → List Nat × Gen
  | 0, g => ([], g)
  | c + 1, g =>
    let (v, g₁) := bits pairFuel n 0 g
    let (vs, g₂) := reducedElems p n c g₁
    (v % p :: vs, g₂)

/-- The Poseidon parameters of the reference Grain procedure for a prime field
    (field type `1`) with the S-box `x ^ α` (S-box type `0`): the `(rf + rp) · t`
    round constants, followed in the same stream by the `2 t` values `x₀ … x_{t-1},
    y₀ … y_{t-1}` of the Cauchy MDS matrix. -/
def constants (p n t rf rp : Nat) : List Nat × List Nat :=
  let g : Gen := ⟨init 1 0 n t rf rp, 0, 0⟩
  let (c, g) := fieldElems p n ((rf + rp) * t) g
  (c, (reducedElems p n (2 * t) g).1)

end CatCrypt.Crypto.Hash.Poseidon.Grain
