set_option maxRecDepth 400000

-- OPS: 102667

/-! The ML-KEM number-theoretic transform (FIPS 203, 256 points, q = 3329) over
    a packed `Nat`.

    A polynomial is one natural number holding 256 coefficients below 3329,
    coefficient `i` at bit `12 * i`. A layer reads its input state once, two
    operations per coefficient, and builds its output state once, two operations
    per coefficient, so neither the read-modify-write of a lane nor an
    intermediate list of coefficients occurs: `ctBlock` and `gsBlock` take the
    layer's input `s` and an accumulator `acc`, and every write is
    `acc ||| (v <<< p)`.

    The forward transform is seven Cooley-Tukey layers with half-width `len`
    from 128 down to 2, the inverse seven Gentleman-Sande layers with `len` from
    2 up to 128 followed by the scaling by `128⁻¹ = 3303`.

    The twist constants are computed rather than tabulated: `zeta k` is
    `17 ^ brv7 k mod 3329`, with `brv7` the seven-bit reversal. In Montgomery
    form, `zeta k * 2285 mod 3329` taken to `(-q/2, q/2]`, the first eight
    values are `-1044, -758, -359, -1517, 1493, 1422, 287, 202`, the head of the
    `zetas` table of the ML-KEM reference implementation.

    Operation count, counting each `Nat` shift, mask, or, addition,
    subtraction, multiplication, exponentiation and modulus the file performs.
    A Cooley-Tukey butterfly is 18 operations and a Gentleman-Sande butterfly
    17; each layer runs 128 of them, and the block walk adds two per block, 254
    over the 127 blocks of a direction, with one more per layer for `12 * len`.
    A forward transform is 7 * 128 * 18 + 254 + 7 = 16389 and an inverse
    7 * 128 * 17 + 254 + 7 = 15493. The scaling pass is 256 * 7 = 1792 and
    building `samplePoly` another 1792. `brv7` is 25 operations and `zeta` 27;
    the two directions consume 254 twists, 254 * 27 = 6858, with 508 more for
    the twist indices. The round trip is
    16389 + 15493 + 1792 + 6858 + 508 + 1792 = 42832, and each of the three
    further forward transforms in the chained theorem costs
    16389 + 127 * 27 + 127 = 19945: 42832 + 3 * 19945 = 102667. -/

def q : Nat := 3329

/-- Seven-bit reversal. -/
def brv7 (k : Nat) : Nat :=
  ((k &&& 1) <<< 6) ||| (((k >>> 1) &&& 1) <<< 5) ||| (((k >>> 2) &&& 1) <<< 4)
    ||| (((k >>> 3) &&& 1) <<< 3) ||| (((k >>> 4) &&& 1) <<< 2)
    ||| (((k >>> 5) &&& 1) <<< 1) ||| ((k >>> 6) &&& 1)

/-- The `k`-th twist constant, `17 ^ brv7 k mod q`. -/
def zeta (k : Nat) : Nat := (17 ^ brv7 k) % q

/-- The twists of the forward layer that has `chunks` blocks: indices `chunks`
    through `2 * chunks - 1`. -/
def zsFwd (chunks : Nat) : List Nat :=
  (List.range chunks).map (fun c => zeta (chunks + c))

/-- The twists of the inverse layer that has `chunks` blocks: the same indices
    in descending order. -/
def zsInv (chunks : Nat) : List Nat :=
  (List.range chunks).map (fun c => zeta (2 * chunks - 1 - c))

/-- The Cooley-Tukey butterflies of one block: `n` pairs at bit distance `w`,
    the first at bit `p` of the layer input `s`, written into `acc`. -/
def ctBlock (z w : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, p, s, acc =>
      let a := (s >>> p) &&& 4095
      let b := (s >>> (p + w)) &&& 4095
      let t := (z * b) % q
      ctBlock z w n (p + 12) s
        (acc ||| (((a + t) % q) <<< p) ||| (((a + q - t) % q) <<< (p + w)))

/-- The Gentleman-Sande butterflies of one block, the same layout as
    `ctBlock`. -/
def gsBlock (z w : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, p, s, acc =>
      let a := (s >>> p) &&& 4095
      let b := (s >>> (p + w)) &&& 4095
      gsBlock z w n (p + 12) s
        (acc ||| (((a + b) % q) <<< p) ||| (((z * (b + q - a)) % q) <<< (p + w)))

/-- One Cooley-Tukey layer: one twist constant per block of `2 * len`
    coefficients. The recursion is structural in the twist list. -/
def ctWalk (len : Nat) : List Nat → Nat → Nat → Nat → Nat
  | [], _, _, acc => acc
  | z :: zs, p, s, acc => ctWalk len zs (p + 24 * len) s (ctBlock z (12 * len) len p s acc)

/-- One Gentleman-Sande layer, the same block structure as `ctWalk`. -/
def gsWalk (len : Nat) : List Nat → Nat → Nat → Nat → Nat
  | [], _, _, acc => acc
  | z :: zs, p, s, acc => gsWalk len zs (p + 24 * len) s (gsBlock z (12 * len) len p s acc)

/-- The forward layer of half-width `len` on `chunks` blocks. -/
def ctLayer (len chunks s : Nat) : Nat := ctWalk len (zsFwd chunks) 0 s 0

/-- The inverse layer of half-width `len` on `chunks` blocks. -/
def gsLayer (len chunks s : Nat) : Nat := gsWalk len (zsInv chunks) 0 s 0

/-- Multiply every coefficient by `128⁻¹ = 3303`. -/
def scaleInv : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, p, s, acc =>
      scaleInv n (p + 12) (s >>> 12) (acc ||| ((((s &&& 4095) * 3303) % q) <<< p))

/-- The forward transform: seven Cooley-Tukey layers. -/
def ntt (s : Nat) : Nat :=
  ctLayer 2 64 (ctLayer 4 32 (ctLayer 8 16 (ctLayer 16 8
    (ctLayer 32 4 (ctLayer 64 2 (ctLayer 128 1 s))))))

/-- The inverse transform: seven Gentleman-Sande layers and the scaling. -/
def invNtt (s : Nat) : Nat :=
  scaleInv 256 0
    (gsLayer 128 1 (gsLayer 64 2 (gsLayer 32 4 (gsLayer 16 8
      (gsLayer 8 16 (gsLayer 4 32 (gsLayer 2 64 s))))))) 0

/-- A polynomial whose coefficient `i` is `(i * i + 7 * i + 1) mod q`. -/
def packSample : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => packSample n ((acc <<< 12) ||| ((n * n + 7 * n + 1) % q))

def samplePoly : Nat := packSample 256 0

/-- `128 * 3303 = 1 mod q`, the scaling the inverse transform applies. -/
theorem mlkem_inv128 : 128 * 3303 % q = 1 := rfl

/-- `17` has order 256 modulo `q`: its 128th power is `-1`. -/
theorem mlkem_zeta_order : 17 ^ 128 % q = q - 1 := rfl

/-- The head of the `zetas` table of the ML-KEM reference implementation, in
    Montgomery form and reduced to `(-q/2, q/2]`. -/
theorem mlkem_zetas_head :
    decide ((List.range 8).map
        (fun k => let v := (zeta k * 2285) % q
                  if v > 1664 then (v : Int) - 3329 else (v : Int))
      = [-1044, -758, -359, -1517, 1493, 1422, 287, 202]) = true := rfl

/-- `invNtt` inverts `ntt` on `samplePoly`. This is an internal consistency
    check of the two transforms against each other, not an external test
    vector. -/
theorem mlkem_ntt_roundtrip : invNtt (ntt samplePoly) = samplePoly := rfl

/-- Feed each transform output back in as the next input. -/
def chain : Nat → Nat → Nat
  | 0, s => s
  | n + 1, s => chain n (ntt s)

/-- Three chained forward transforms, part of the reduction the operation count
    above refers to. -/
theorem mlkem_ntt_chain : decide (chain 3 samplePoly = 0) = false := rfl
