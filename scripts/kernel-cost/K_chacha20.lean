set_option maxRecDepth 200000

/-! ChaCha20 block (RFC 8439 §2.3) with the sixteen 32-bit words packed into the
    low 512 bits of one natural number, lane `i` at bit `32 * i`.

    This is the representation the kernel backend prescribes for aggregate
    state: one GMP value, with lane access by shift and mask. Twenty rounds are
    eighty quarter-rounds; each quarter-round reads four lanes, writes four,
    and costs four adds, four xors and four rotations. -/

def w32 : Nat := 4294967295

/-- Lane `i` of the packed state. -/
def lane (s i : Nat) : Nat := (s >>> (32 * i)) &&& w32

/-- Replace lane `i` of the packed state. -/
def setLane (s i v : Nat) : Nat :=
  (s &&& (((2 ^ 512 - 1) ^^^ (w32 <<< (32 * i))))) ||| ((v &&& w32) <<< (32 * i))

/-- 32-bit rotate left. -/
def rotl32 (x n : Nat) : Nat := ((x <<< n) ||| (x >>> (32 - n))) &&& w32

/-- One quarter-round on lanes `a b c d` of the packed state. -/
def qr (s a b c d : Nat) : Nat :=
  let va := lane s a; let vb := lane s b; let vc := lane s c; let vd := lane s d
  let va := (va + vb) &&& w32
  let vd := rotl32 (vd ^^^ va) 16
  let vc := (vc + vd) &&& w32
  let vb := rotl32 (vb ^^^ vc) 12
  let va := (va + vb) &&& w32
  let vd := rotl32 (vd ^^^ va) 8
  let vc := (vc + vd) &&& w32
  let vb := rotl32 (vb ^^^ vc) 7
  setLane (setLane (setLane (setLane s a va) b vb) c vc) d vd

/-- One double round: four column rounds then four diagonal rounds. -/
def doubleRound (s : Nat) : Nat :=
  let s := qr s 0 4 8 12
  let s := qr s 1 5 9 13
  let s := qr s 2 6 10 14
  let s := qr s 3 7 11 15
  let s := qr s 0 5 10 15
  let s := qr s 1 6 11 12
  let s := qr s 2 7 8 13
  let s := qr s 3 4 9 14
  s

def rounds : Nat → Nat → Nat
  | 0, s => s
  | n + 1, s => rounds n (doubleRound s)

/-- The RFC 8439 §2.3.2 state: the four constants, a key of `00 01 … 1f`, a
    block counter of `1` and the nonce `09000000 4a000000 00000000`. -/
def initState : Nat :=
  let ws : List Nat :=
    [ 0x61707865, 0x3320646e, 0x79622d32, 0x6b206574
    , 0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c
    , 0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c
    , 0x00000001, 0x09000000, 0x4a000000, 0x00000000 ]
  ws.foldr (fun v acc => (acc <<< 32) ||| v) 0

/-- Twenty rounds, then the feed-forward addition lane by lane. -/
def chacha20Block (s : Nat) : Nat :=
  let t := rounds 10 s
  (List.range 16).foldl (fun acc i => setLane acc i ((lane t i + lane s i) &&& w32)) 0

/-- Chain the block function so the measurement is above the startup noise. -/
def blocks : Nat → Nat → Nat
  | 0, s => s
  | n + 1, s => blocks n (chacha20Block s)

theorem tC : decide (blocks 50 initState = 0) = false := rfl
