set_option maxRecDepth 200000

-- OPS: 19520

/-! ChaCha20 block function (RFC 8439 §2.3) over a packed `Nat` state.

    The sixteen 32-bit words live in the low 512 bits of one natural number,
    lane `i` at bit `32 * i`. Lane access is a shift and a mask; the sixteen
    lanes are extracted into local bindings once per double round, the eight
    quarter-rounds run on those bindings, and the state is repacked once.

    Operation count. One quarter-round is four additions, four exclusive-ors
    and four rotations, so twelve 32-bit operations; a block is twenty rounds
    of four quarter-rounds, 20 * 4 * 12 = 960, plus the sixteen feed-forward
    additions, 976 per block. The timing theorem chains twenty blocks:
    20 * 976 = 19520. -/

def w32 : Nat := 4294967295

/-- Lane `i` of the packed state. -/
def lane (s i : Nat) : Nat := (s >>> (32 * i)) &&& w32

/-- 32-bit rotate left. -/
def rotl32 (x n : Nat) : Nat := ((x <<< n) ||| (x >>> (32 - n))) &&& w32

/-- The quarter-round as a function of four lane values. -/
def qr4 (a b c d : Nat) : Nat × Nat × Nat × Nat :=
  let a := (a + b) &&& w32
  let d := rotl32 (d ^^^ a) 16
  let c := (c + d) &&& w32
  let b := rotl32 (b ^^^ c) 12
  let a := (a + b) &&& w32
  let d := rotl32 (d ^^^ a) 8
  let c := (c + d) &&& w32
  let b := rotl32 (b ^^^ c) 7
  (a, b, c, d)

/-- One double round — four column quarter-rounds then four diagonal ones —
    over lanes unpacked once and repacked once. -/
def doubleRound (s : Nat) : Nat :=
  let x0 := lane s 0; let x1 := lane s 1; let x2 := lane s 2; let x3 := lane s 3
  let x4 := lane s 4; let x5 := lane s 5; let x6 := lane s 6; let x7 := lane s 7
  let x8 := lane s 8; let x9 := lane s 9; let x10 := lane s 10; let x11 := lane s 11
  let x12 := lane s 12; let x13 := lane s 13; let x14 := lane s 14; let x15 := lane s 15
  let (x0, x4, x8, x12) := qr4 x0 x4 x8 x12
  let (x1, x5, x9, x13) := qr4 x1 x5 x9 x13
  let (x2, x6, x10, x14) := qr4 x2 x6 x10 x14
  let (x3, x7, x11, x15) := qr4 x3 x7 x11 x15
  let (x0, x5, x10, x15) := qr4 x0 x5 x10 x15
  let (x1, x6, x11, x12) := qr4 x1 x6 x11 x12
  let (x2, x7, x8, x13) := qr4 x2 x7 x8 x13
  let (x3, x4, x9, x14) := qr4 x3 x4 x9 x14
  x0 ||| (x1 <<< 32) ||| (x2 <<< 64) ||| (x3 <<< 96)
    ||| (x4 <<< 128) ||| (x5 <<< 160) ||| (x6 <<< 192) ||| (x7 <<< 224)
    ||| (x8 <<< 256) ||| (x9 <<< 288) ||| (x10 <<< 320) ||| (x11 <<< 352)
    ||| (x12 <<< 384) ||| (x13 <<< 416) ||| (x14 <<< 448) ||| (x15 <<< 480)

def rounds : Nat → Nat → Nat
  | 0, s => s
  | n + 1, s => rounds n (doubleRound s)

/-- Pack a list of 32-bit words into one natural number, the head at bit 0. -/
def packWords (ws : List Nat) : Nat :=
  ws.foldr (fun v acc => (acc <<< 32) ||| v) 0

/-- The RFC 8439 §2.3.2 input state: the four constants, the key
    `00 01 02 … 1f`, block counter `1`, nonce `00 00 00 09 00 00 00 4a
    00 00 00 00`. -/
def initState : Nat :=
  packWords
    [ 0x61707865, 0x3320646e, 0x79622d32, 0x6b206574
    , 0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c
    , 0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c
    , 0x00000001, 0x09000000, 0x4a000000, 0x00000000 ]

/-- Twenty rounds followed by the lane-wise feed-forward addition. -/
def chacha20Block (s : Nat) : Nat :=
  let t := rounds 10 s
  packWords ((List.range 16).map (fun i => (lane t i + lane s i) &&& w32))

/-- The keystream block of RFC 8439 §2.3.2, as the sixteen 32-bit words the
    document prints. -/
def rfc8439Block : Nat :=
  packWords
    [ 0xe4e7f110, 0x15593bd1, 0x1fdd0f50, 0xc47120a3
    , 0xc7f4d1c7, 0x0368c033, 0x9aaa2204, 0x4e6cd4c3
    , 0x466482d2, 0x09aa9f07, 0x05d7c214, 0xa2028bd9
    , 0xd19c12b5, 0xb94e16de, 0xe883d0cb, 0x4e3c50a2 ]

/-- RFC 8439 §2.3.2, "Test Vector for the ChaCha20 Block Function". -/
theorem chacha20_rfc8439_block : chacha20Block initState = rfc8439Block := rfl

/-- Feed each block's output back in as the next block's input. -/
def blocks : Nat → Nat → Nat
  | 0, s => s
  | n + 1, s => blocks n (chacha20Block s)

/-- Twenty chained blocks, the reduction the operation count above refers to. -/
theorem chacha20_chain : decide (blocks 20 initState = 0) = false := rfl
