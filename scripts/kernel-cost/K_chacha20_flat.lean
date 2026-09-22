set_option maxRecDepth 200000

/-! ChaCha20 block with the lanes unpacked once per double round rather than
    per quarter-round.

    `K_chacha20.lean` keeps the state packed and every quarter-round reads four
    lanes and writes four, at two and five operations respectively, so lane
    access costs 224 operations per double round against 224 of arithmetic.
    Here the sixteen lanes are extracted into local bindings once, the eight
    quarter-rounds run on them directly, and the state is repacked once — 112
    lane operations per double round. Same arithmetic, same result. -/

def w32 : Nat := 4294967295

def lane (s i : Nat) : Nat := (s >>> (32 * i)) &&& w32

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

/-- One double round over unpacked lanes, repacking once at the end. -/
def doubleRoundFlat (s : Nat) : Nat :=
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

def roundsFlat : Nat → Nat → Nat
  | 0, s => s
  | n + 1, s => roundsFlat n (doubleRoundFlat s)

def initState : Nat :=
  let ws : List Nat :=
    [ 0x61707865, 0x3320646e, 0x79622d32, 0x6b206574
    , 0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c
    , 0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c
    , 0x00000001, 0x09000000, 0x4a000000, 0x00000000 ]
  ws.foldr (fun v acc => (acc <<< 32) ||| v) 0

def chacha20BlockFlat (s : Nat) : Nat :=
  let t := roundsFlat 10 s
  (List.range 16).foldl
    (fun acc i => acc ||| (((lane t i + lane s i) &&& w32) <<< (32 * i))) 0

def blocksFlat : Nat → Nat → Nat
  | 0, s => s
  | n + 1, s => blocksFlat n (chacha20BlockFlat s)

theorem tCF : decide (blocksFlat 50 initState = 0) = false := rfl
