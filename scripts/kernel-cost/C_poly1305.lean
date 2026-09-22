set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

-- OPS: 6000

/-! Poly1305 one-time authenticator (RFC 8439 §2.5) over `Nat`.

    The accumulator, the key halves and each message block are single natural
    numbers; a block is absorbed by `acc := (acc + n) * r mod (2^130 - 5)`,
    which is the representation the kernel reduces fastest — one multiplication
    and one modulus on GMP values rather than five limb products.

    Operation count. One block step is one addition, one multiplication and one
    modular reduction, counted as three 130-bit operations. The published
    vector absorbs three blocks. The timing theorem runs 2000 chained block
    steps: 2000 * 3 = 6000. -/

/-- The Poly1305 prime. -/
def p1305 : Nat := 2 ^ 130 - 5

/-- The clamping mask applied to the first key half. -/
def clampMask : Nat := 0x0ffffffc0ffffffc0ffffffc0fffffff

/-- Interpret a byte list as a little-endian natural number. -/
def leNat (bs : List Nat) : Nat :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b) 0

/-- Absorb one message block: append the high `1` bit, add and multiply. -/
def absorb (r acc : Nat) (block : List Nat) : Nat :=
  ((acc + leNat (block ++ [1])) * r) % p1305

/-- Absorb a message sixteen bytes at a time. The first argument is a fuel
    bound, so the recursion is structural and the kernel unfolds it. -/
def absorbAll (r : Nat) : Nat → Nat → List Nat → Nat
  | 0, acc, _ => acc
  | _, acc, [] => acc
  | f + 1, acc, bs => absorbAll r f (absorb r acc (bs.take 16)) (bs.drop 16)

/-- The tag: absorb every block, add the second key half, truncate to 128 bits. -/
def poly1305 (key msg : List Nat) : Nat :=
  let r := leNat (key.take 16) &&& clampMask
  let s := leNat (key.drop 16)
  let acc := absorbAll r msg.length 0 msg
  (acc + s) % (2 ^ 128)

/-- The RFC 8439 §2.5.2 key
    `85:d6:be:78:57:55:6d:33:7f:44:52:fe:42:d5:06:a8:
     01:03:80:8a:fb:0d:b2:fd:4a:bf:f6:af:41:49:f5:1b`. -/
def rfcKey : List Nat :=
  [ 0x85, 0xd6, 0xbe, 0x78, 0x57, 0x55, 0x6d, 0x33
  , 0x7f, 0x44, 0x52, 0xfe, 0x42, 0xd5, 0x06, 0xa8
  , 0x01, 0x03, 0x80, 0x8a, 0xfb, 0x0d, 0xb2, 0xfd
  , 0x4a, 0xbf, 0xf6, 0xaf, 0x41, 0x49, 0xf5, 0x1b ]

/-- The RFC 8439 §2.5.2 message, the ASCII bytes of
    `Cryptographic Forum Research Group`. -/
def rfcMsg : List Nat :=
  [ 0x43, 0x72, 0x79, 0x70, 0x74, 0x6f, 0x67, 0x72, 0x61
  , 0x70, 0x68, 0x69, 0x63, 0x20, 0x46, 0x6f, 0x72, 0x75
  , 0x6d, 0x20, 0x52, 0x65, 0x73, 0x65, 0x61, 0x72, 0x63
  , 0x68, 0x20, 0x47, 0x72, 0x6f, 0x75, 0x70 ]

/-- The RFC 8439 §2.5.2 tag
    `a8:06:1d:c1:30:51:36:c6:c2:2b:8b:af:0c:01:27:a9`. -/
def rfcTag : Nat :=
  leNat
    [ 0xa8, 0x06, 0x1d, 0xc1, 0x30, 0x51, 0x36, 0xc6
    , 0xc2, 0x2b, 0x8b, 0xaf, 0x0c, 0x01, 0x27, 0xa9 ]

/-- RFC 8439 §2.5.2, "Poly1305 Example and Test Vector". -/
theorem poly1305_rfc8439_tag : poly1305 rfcKey rfcMsg = rfcTag := rfl

/-- Chain the block step, feeding each accumulator back as the next block. -/
def chain (r : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => chain r n (((acc + acc + 1) * r) % p1305)

/-- Two thousand chained block steps, the reduction the operation count above
    refers to. -/
theorem poly1305_chain :
    decide (chain (leNat (rfcKey.take 16) &&& clampMask) 2000 1 = 0) = false := rfl
