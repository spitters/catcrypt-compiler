set_option maxRecDepth 4000000
set_option maxHeartbeats 40000000
set_option exponentiation.threshold 400

-- OPS: 332276

/-! Curve25519 field arithmetic over five 51-bit limbs and the X25519 scalar
    multiplication (RFC 7748) over a packed `Nat`.

    A field element is one natural number holding five limbs at a 64-bit
    stride, limb `i` at bit `64 * i`, read by a shift and a mask. Limbs carry
    51-bit values after a multiplication and stay below `2 ^ 55` after an
    addition or a subtraction, so the stride never overflows. `feMul` forms the
    twenty-five limb products with the `19`-fold wrap of the terms above the
    top limb, then runs the six-step carry chain and repacks once; `feAdd` and
    `feSub` are limbwise and leave the result uncarried, `feSub` adding the
    multiple `8 * (2 ^ 255 - 19)` so that the limb differences stay
    non-negative.

    The Montgomery ladder is the RFC 7748 section 5 pseudocode: 255 iterations
    over the clamped scalar, each a conditional swap driven by an
    exclusive-or mask, four squarings, five multiplications, one multiplication
    by `121665` and eight additions or subtractions. The final inversion is the
    `2 ^ 255 - 21` addition chain, 254 squarings and 11 multiplications.

    Operation count, counting each `Nat` shift, mask, or, exclusive-or,
    addition, subtraction, multiplication, exponentiation and modulus the file
    performs. `feMul` is 20 limb reads, 49 operations forming the five
    accumulators, 19 in the carry chain and 8 to repack: 96, and `feSq` calls
    it. `feMul121665` is 42, `feAdd` 33 and `feSub` 38. One ladder iteration is
    12 for the bit and the conditional swap plus 1190 for its eighteen field
    operations: 1202, and the loop runs 255 times for 306510, with 7 for the
    closing conditional swap. The inversion is 265 * 96 = 25440. The final
    multiplication and the conversion to a residue add 115, and decoding the
    scalar and the u-coordinate 204: 332276. -/

def w64 : Nat := 18446744073709551615

/-- `2 ^ 51 - 1`, the limb mask. -/
def m51 : Nat := 2251799813685247

def p25519 : Nat := 2 ^ 255 - 19

/-- Limb `i` of a packed field element. -/
def lmb (f i : Nat) : Nat := (f >>> (64 * i)) &&& w64

/-- Pack five limbs, limb `i` at bit `64 * i`. -/
def mk (h0 h1 h2 h3 h4 : Nat) : Nat :=
  h0 ||| (h1 <<< 64) ||| (h2 <<< 128) ||| (h3 <<< 192) ||| (h4 <<< 256)

/-- The carry chain: propagate the bits above 51 through the limbs, wrapping
    the top carry into limb 0 with the factor 19. -/
def carry (r0 r1 r2 r3 r4 : Nat) : Nat :=
  let c := r0 >>> 51; let r0 := r0 &&& m51; let r1 := r1 + c
  let c := r1 >>> 51; let r1 := r1 &&& m51; let r2 := r2 + c
  let c := r2 >>> 51; let r2 := r2 &&& m51; let r3 := r3 + c
  let c := r3 >>> 51; let r3 := r3 &&& m51; let r4 := r4 + c
  let c := r4 >>> 51; let r4 := r4 &&& m51; let r0 := r0 + 19 * c
  let c := r0 >>> 51; let r0 := r0 &&& m51; let r1 := r1 + c
  mk r0 r1 r2 r3 r4

/-- Field multiplication: the limbs are unpacked once, the twenty-five products
    are accumulated into five columns, and the result is carried and packed
    once. -/
def feMul (f g : Nat) : Nat :=
  let f0 := lmb f 0; let f1 := lmb f 1; let f2 := lmb f 2
  let f3 := lmb f 3; let f4 := lmb f 4
  let g0 := lmb g 0; let g1 := lmb g 1; let g2 := lmb g 2
  let g3 := lmb g 3; let g4 := lmb g 4
  carry
    (f0 * g0 + 19 * (f1 * g4 + f2 * g3 + f3 * g2 + f4 * g1))
    (f0 * g1 + f1 * g0 + 19 * (f2 * g4 + f3 * g3 + f4 * g2))
    (f0 * g2 + f1 * g1 + f2 * g0 + 19 * (f3 * g4 + f4 * g3))
    (f0 * g3 + f1 * g2 + f2 * g1 + f3 * g0 + 19 * (f4 * g4))
    (f0 * g4 + f1 * g3 + f2 * g2 + f3 * g1 + f4 * g0)

def feSq (f : Nat) : Nat := feMul f f

/-- Multiplication by the curve constant `a24 = 121665`, carried so that the
    result is again a 51-bit limb vector. -/
def feMul121665 (f : Nat) : Nat :=
  carry (121665 * lmb f 0) (121665 * lmb f 1) (121665 * lmb f 2)
    (121665 * lmb f 3) (121665 * lmb f 4)

/-- Limbwise addition, left uncarried. -/
def feAdd (f g : Nat) : Nat :=
  mk (lmb f 0 + lmb g 0) (lmb f 1 + lmb g 1) (lmb f 2 + lmb g 2)
     (lmb f 3 + lmb g 3) (lmb f 4 + lmb g 4)

/-- Limbwise subtraction, left uncarried. The added constants are the limbs of
    `8 * (2 ^ 255 - 19)`, which is zero modulo the prime and exceeds every
    admissible limb of `g`. -/
def feSub (f g : Nat) : Nat :=
  mk (lmb f 0 + 18014398509481832 - lmb g 0)
     (lmb f 1 + 18014398509481976 - lmb g 1)
     (lmb f 2 + 18014398509481976 - lmb g 2)
     (lmb f 3 + 18014398509481976 - lmb g 3)
     (lmb f 4 + 18014398509481976 - lmb g 4)

/-- Split a natural number below `2 ^ 255` into five 51-bit limbs. -/
def feFromNat (v : Nat) : Nat :=
  mk (v &&& m51) ((v >>> 51) &&& m51) ((v >>> 102) &&& m51)
     ((v >>> 153) &&& m51) ((v >>> 204) &&& m51)

/-- The residue a limb vector represents. -/
def feToNat (f : Nat) : Nat :=
  (lmb f 0 + (lmb f 1 <<< 51) + (lmb f 2 <<< 102) + (lmb f 3 <<< 153)
    + (lmb f 4 <<< 204)) % p25519

/-- `n` repeated squarings. -/
def feSqN : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => feSqN n (feSq x)

/-- The inverse, as `z ^ (p - 2)` along the `2 ^ 255 - 21` addition chain. -/
def feInv (z : Nat) : Nat :=
  let t0 := feSq z
  let t1 := feSqN 2 t0
  let t1 := feMul z t1
  let t0 := feMul t0 t1
  let t2 := feSq t0
  let t1 := feMul t1 t2
  let t2 := feSqN 5 t1
  let t1 := feMul t2 t1
  let t2 := feSqN 10 t1
  let t2 := feMul t2 t1
  let t3 := feSqN 20 t2
  let t2 := feMul t3 t2
  let t2 := feSqN 10 t2
  let t1 := feMul t2 t1
  let t2 := feSqN 50 t1
  let t2 := feMul t2 t1
  let t3 := feSqN 100 t2
  let t2 := feMul t3 t2
  let t2 := feSqN 50 t2
  let t1 := feMul t2 t1
  let t1 := feSqN 5 t1
  feMul t1 t0

/-- The all-ones mask over the five limb positions, the conditional-swap
    mask when the swap bit is 1. -/
def allOnes : Nat := 2 ^ 320 - 1

/-- The Montgomery ladder of RFC 7748 section 5. The first argument counts the
    remaining scalar bits, the next holds the pending swap bit, and the four
    that follow are the projective coordinates. -/
def ladder (x1 k : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | 0, swap, x2, z2, x3, z3 =>
      let m := swap * allOnes
      (x2 ^^^ ((x2 ^^^ x3) &&& m), z2 ^^^ ((z2 ^^^ z3) &&& m))
  | t + 1, swap, x2, z2, x3, z3 =>
      let kt := (k >>> t) &&& 1
      let m := (swap ^^^ kt) * allOnes
      let dx := (x2 ^^^ x3) &&& m
      let dz := (z2 ^^^ z3) &&& m
      let x2 := x2 ^^^ dx; let x3 := x3 ^^^ dx
      let z2 := z2 ^^^ dz; let z3 := z3 ^^^ dz
      let a := feAdd x2 z2
      let aa := feSq a
      let b := feSub x2 z2
      let bb := feSq b
      let e := feSub aa bb
      let c := feAdd x3 z3
      let d := feSub x3 z3
      let da := feMul d a
      let cb := feMul c b
      let x3 := feSq (feAdd da cb)
      let z3 := feMul x1 (feSq (feSub da cb))
      let x2 := feMul aa bb
      let z2 := feMul e (feAdd aa (feMul121665 e))
      ladder x1 k t kt x2 z2 x3 z3

/-- Interpret a byte list as a little-endian natural number. -/
def leNat (bs : List Nat) : Nat := bs.foldr (fun b acc => (acc <<< 8) ||| b) 0

/-- The RFC 7748 scalar clamping: clear the three low bits and the top bit, set
    bit 254. -/
def clamp (bs : List Nat) : Nat :=
  let v := leNat bs
  ((v &&& (allOnes - 7)) &&& (2 ^ 255 - 1)) ||| (2 ^ 254)

/-- X25519 on a 32-byte scalar and a 32-byte u-coordinate, the result as the
    little-endian natural number its output bytes encode. -/
def x25519 (kb ub : List Nat) : Nat :=
  let u := feFromNat (leNat ub &&& (2 ^ 255 - 1))
  match ladder u (clamp kb) 255 0 (feFromNat 1) (feFromNat 0) u (feFromNat 1) with
  | (x2, z2) => feToNat (feMul x2 (feInv z2))

/-- The private key `a` of RFC 7748 section 6.1. -/
def aliceSk : List Nat :=
  [ 0x77, 0x07, 0x6d, 0x0a, 0x73, 0x18, 0xa5, 0x7d
  , 0x3c, 0x16, 0xc1, 0x72, 0x51, 0xb2, 0x66, 0x45
  , 0xdf, 0x4c, 0x2f, 0x87, 0xeb, 0xc0, 0x99, 0x2a
  , 0xb1, 0x77, 0xfb, 0xa5, 0x1d, 0xb9, 0x2c, 0x2a ]

/-- The public key `X25519(a, 9)` of RFC 7748 section 6.1. -/
def alicePk : List Nat :=
  [ 0x85, 0x20, 0xf0, 0x09, 0x89, 0x30, 0xa7, 0x54
  , 0x74, 0x8b, 0x7d, 0xdc, 0xb4, 0x3e, 0xf7, 0x5a
  , 0x0d, 0xbf, 0x3a, 0x0d, 0x26, 0x38, 0x1a, 0xf4
  , 0xeb, 0xa4, 0xa9, 0x8e, 0xaa, 0x9b, 0x4e, 0x6a ]

/-- The base point, the u-coordinate 9. -/
def basePoint : List Nat := 9 :: List.replicate 31 0

/-- RFC 7748 section 6.1: `X25519(a, 9)` is Alice's public key. -/
theorem x25519_rfc7748_alice : x25519 aliceSk basePoint = leNat alicePk := rfl
