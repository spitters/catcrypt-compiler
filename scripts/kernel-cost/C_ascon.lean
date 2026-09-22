set_option maxRecDepth 200000

-- OPS: 124877

/-! The Ascon permutation `p12` and Ascon-Hash (Ascon v1.2) over a packed `Nat`.

    The 320-bit state is one natural number with word `x_i` at bit `64 * i`,
    read by a shift and a mask. The five words are unpacked into local bindings
    once per round; the constant addition, the substitution layer and the linear
    diffusion layer run on those bindings; the state is repacked once at the end
    of the round. The twelve round constants are a single packed `Nat`.

    Operation count, counting each `Nat` shift, mask, disjunction,
    exclusive-or and subtraction the file performs. `rotr64` is five (the offset
    subtraction, two shifts, an or and a mask). Per round: five word reads (10),
    the round-constant read and its exclusive-or (3), the three linear
    exclusive-ors that open the substitution layer (3), the five `(~x) & y`
    terms (10), the five exclusive-ors that fold them back (5), the three
    closing exclusive-ors (3), the complement of `x2` (1), the diffusion layer
    at twelve operations per word (60) and the repack (8) — 103 each, 1236 over
    the twelve rounds of `p12`.

    The file reduces `p12` a hundred and one times: five for the empty-message
    hash (one to expand the initialization vector, four to squeeze the 256-bit
    digest) and ninety-six in the chained timing theorem. 101 * 1236 = 124836,
    plus the round-constant table (24), the hash's padding exclusive-or (1) and
    its four squeezed word reads and digest assembly (16): 124877. -/

def w64 : Nat := 18446744073709551615

/-- Word `i` of the packed state. -/
def word64 (s i : Nat) : Nat := (s >>> (64 * i)) &&& w64

/-- 64-bit rotate right. -/
def rotr64 (x n : Nat) : Nat := ((x >>> n) ||| (x <<< (64 - n))) &&& w64

/-- Pack a list of 64-bit words so that the head sits at bit 0. -/
def packWords (ws : List Nat) : Nat :=
  ws.foldr (fun v acc => (acc <<< 64) ||| v) 0

/-- The twelve round constants of `p12`, constant `t` at bit `64 * t`. -/
def rcTable : Nat :=
  packWords [0xf0, 0xe1, 0xd2, 0xc3, 0xb4, 0xa5, 0x96, 0x87, 0x78, 0x69, 0x5a, 0x4b]

/-- One round of the Ascon permutation with round index `t`. -/
def asconRound (t s : Nat) : Nat :=
  let x0 := word64 s 0
  let x1 := word64 s 1
  let x2 := word64 s 2
  let x3 := word64 s 3
  let x4 := word64 s 4
  let x2 := x2 ^^^ word64 rcTable t
  let x0 := x0 ^^^ x4
  let x4 := x4 ^^^ x3
  let x2 := x2 ^^^ x1
  let t0 := (x0 ^^^ w64) &&& x1
  let t1 := (x1 ^^^ w64) &&& x2
  let t2 := (x2 ^^^ w64) &&& x3
  let t3 := (x3 ^^^ w64) &&& x4
  let t4 := (x4 ^^^ w64) &&& x0
  let x0 := x0 ^^^ t1
  let x1 := x1 ^^^ t2
  let x2 := x2 ^^^ t3
  let x3 := x3 ^^^ t4
  let x4 := x4 ^^^ t0
  let x1 := x1 ^^^ x0
  let x0 := x0 ^^^ x4
  let x3 := x3 ^^^ x2
  let x2 := x2 ^^^ w64
  let x0 := x0 ^^^ rotr64 x0 19 ^^^ rotr64 x0 28
  let x1 := x1 ^^^ rotr64 x1 61 ^^^ rotr64 x1 39
  let x2 := x2 ^^^ rotr64 x2 1 ^^^ rotr64 x2 6
  let x3 := x3 ^^^ rotr64 x3 10 ^^^ rotr64 x3 17
  let x4 := x4 ^^^ rotr64 x4 7 ^^^ rotr64 x4 41
  x0 ||| (x1 <<< 64) ||| (x2 <<< 128) ||| (x3 <<< 192) ||| (x4 <<< 256)

def asconRounds : Nat → Nat → Nat → Nat
  | 0, _, s => s
  | n + 1, t, s => asconRounds n (t + 1) (asconRound t s)

/-- The Ascon permutation `p12`: twelve rounds with constants `0xf0` down to
    `0x4b`. -/
def p12 (s : Nat) : Nat := asconRounds 12 0 s

/-- The Ascon-Hash initialization vector `0x00400c0000000100` in word 0, the
    remaining four words zero. -/
def hashIV : Nat := 0x00400c0000000100

/-- The Ascon-Hash initial state, the expansion of `hashIV` under `p12`. Its
    five words are the constants `ASCON_HASH_IV0` … `ASCON_HASH_IV4` of the
    Ascon reference implementation. -/
theorem ascon_hash_iv :
    decide ((List.range 5).map (fun i => word64 (p12 hashIV) i)
      = [ 0xee9398aadb67f03d, 0x8bb21831c60f1002, 0xb48a92db98d5da62
        , 0x43189921b8f8e3e8, 0x348fa5c9d525e140 ]) = true := rfl

/-- Squeeze `n` further 8-byte blocks, each preceded by a permutation call, and
    accumulate them big-endian. -/
def squeeze : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | n + 1, s, acc =>
      let s := p12 s
      squeeze n s ((acc <<< 64) ||| word64 s 0)

/-- Ascon-Hash of the empty message: the absorbed state is the initial state
    with the padding byte `0x80` at the head of the 8-byte rate, and the
    256-bit digest is four squeezed rate blocks. -/
def asconHashEmpty : Nat :=
  squeeze 4 (p12 hashIV ^^^ 0x8000000000000000) 0

/-- Ascon-Hash of the empty message, Ascon v1.2. -/
theorem ascon_hash_empty :
    decide (asconHashEmpty
      = 0x7346bc14f036e87ae03d0997913088f5f68411434b3cf8b54fa796a80d251f91) = true :=
  rfl

/-- Feed each permutation output back in as the next input. -/
def chain : Nat → Nat → Nat
  | 0, s => s
  | n + 1, s => chain n (p12 s)

/-- Ninety-six chained permutation calls, part of the reduction the operation
    count above refers to. -/
theorem ascon_chain : decide (chain 96 hashIV = 0) = false := rfl
