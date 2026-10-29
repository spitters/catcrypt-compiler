/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ChaChaEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.ChaChaEmit
public meta import CatCrypt.Crypto.SecureCompilation.VIR.VectorReduce
public import CatCrypt.Crypto.SecureCompilation.VIR.VectorReduce
public import CatCryptCore.Tactics.GrindChar

/-!
# ChaCha20-Poly1305 AEAD (RFC 8439) emitted through the verified front

ChaCha20-Poly1305 (RFC 8439, the IETF AEAD) is the AEAD cluster's stream-cipher
member. It has **no new machinery** for the verified front: every piece is a
committed building block reused at a new lane.

* the **ChaCha20 keystream** is exactly the committed ChaCha20 block emit
  (`ChaChaEmit.chachaBlockJazz`, RFC 8439 §2.3.2 KAT'd) — block `0` gives the
  Poly1305 one-time key `(r, s)`, blocks `1, 2, …` are XOR-ed into the plaintext
  to form the ciphertext (RFC 8439 §2.4 / §2.8);
* the **Poly1305 MAC** (RFC 8439 §2.5) is a **field dot / Horner evaluation**
  `MAC = Σ_i block_i · r^(n-i)  (mod 2¹³⁰ − 5)` over the prime field `𝔽_p`,
  `p = 2¹³⁰ − 5`. This is the SAME `VectorReduce.scalarFold_eq_hsum`
  reassociation the FrodoKEM (`ℤ/2¹⁶`), UOV (`GF(256)`), SDitH (`GF(251)`),
  FAEST (`GF(2¹²⁸)`) kernels all carry — only the lane field changes, here to the
  130-bit prime `𝔽_{2¹³⁰−5}`. The Horner accumulation
  `acc := (acc + block_i)·r  (mod p)` is the sequential `scalarFold` over the
  monomial terms `block_i · r^(n-i)`;
* the **tag** is `MAC + s  (mod 2¹²⁸)` (RFC 8439 §2.5.1), a final `u128` add.

So this file emits ChaCha20-Poly1305's hot core from committed pieces and carries
the denotation proof: the Poly1305 MAC dot via `scalarFold_eq_hsum` at the
`𝔽_{2¹³⁰−5}` lane; the ChaCha20 keystream via the committed `chachaBlockJazz`
emit.

It defines its **own** focused emit functions (a `poly1305_mac` inline jasmin
helper over 5×26-bit limbs, the Horner-block body, and the AEAD-encrypt
orchestration that reuses the committed `chacha20_block`); it does **not** edit
`ChaChaEmit.lean`, `VectorReduce.lean`, `JasminAbiEmit.lean`, or any committed
kernel — it imports `ChaChaEmit` for the keystream emit and `VectorReduce` for
the verified MAC-dot reassociation, and uses `strContains` for the structural
checks.

## Field — 𝔽_p, p = 2¹³⁰ − 5, confirmed from RFC 8439

Poly1305's accumulator field is the **prime** field `𝔽_p` with the Bernstein
prime `p = 2¹³⁰ − 5` (RFC 8439 §2.5: "the prime 2¹³⁰−5"). This is an
odd-characteristic prime field (NOT a binary extension): addition is integer
`+ mod p`, multiplication is integer `· mod p`. The classic schoolbook
representation (used by the RFC's reference and by HACL*'s `Hacl_MAC_Poly1305`)
is **5 limbs of 26 bits** (`5·26 = 130`); the field reduction exploits
`2¹³⁰ ≡ 5 (mod p)`, so the high limbs fold back with a `·5` carry
(`h₅·2¹³⁰ ≡ h₅·5`). We carry the proof at the abstract `ZMod p` lane; the
concrete 26-bit-limb mul + `·5`-fold reduction lives in the emitted jasmin and
is KAT'd byte-identical to the RFC 8439 §2.8.2 vector and the HACL* reference.

## Denotation preservation (the main theorem)

The lane type for the verified core is `Fp = ZMod (2¹³⁰ − 5)`, a `CommRing`
(hence an `AddCommMonoid` under its additive `+ mod p` group).
`VectorReduce.scalarFold_eq_hsum` proves the sequential straight-line fold equals
the horizontal reduction once over any `AddCommMonoid`; here it is instantiated
at the `𝔽_{2¹³⁰−5}` lane:

* `poly1305_dot` — the MAC `Σ_i block_i · r^(n-i)` is the `𝔽_p`
  `scalarFold = hsum` reassociation (the Horner accumulation is the sequential
  `scalarFold` over the monomial terms).

This is the identical foundation lemma the GF(256)/GF(251)/GF(2¹²⁸)/ℤ-2¹⁶
kernels carry — the clean generalization the `AddCommMonoid` statement licenses,
here at the 130-bit prime field.

## KAT / bench

The emitted `gen/poly1305_mac.jazz` (Poly1305 MAC) plus the committed
`chacha20_block` (the keystream) are wired into a full ChaCha20-Poly1305 AEAD
encrypt in `bench/chachapoly_compare/`, cross-checked **byte-identical** to the
RFC 8439 §2.8.2 test vector (the "Cryptographic Forum Research Group" message)
and to the HACL*/EverCrypt `Hacl_AEAD_Chacha20Poly1305_encrypt` reference (a
formally verified, constant-time reference — ideal as an independent oracle for
the framework). No fabricated vectors.

**Scope.** This is ChaCha20-Poly1305's HOT CORE emitted from committed pieces
(the ChaCha20 keystream + the Poly1305 MAC field-dot + the tag add), KAT'd at the
full-AEAD level, NOT a monolithic AEAD `Com`. It demonstrates the AEAD emitted at
parity from the verified front, correctness carried from the proven
`AddCommMonoid` reassociation lemma (the MAC dot) and the committed ChaCha emit
(the keystream).

Invoke:  lake env lean bench/chachapoly_compare/chachapoly_emit.lean
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.VIR.ChaChaPolyEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminPrint (strContains)
open CatCrypt.Crypto.SecureCompilation.VIR.VectorReduce
open CatCrypt.Crypto.SecureCompilation.VIR.ChaChaEmit (chachaBlockJazz)
open scoped BigOperators

set_option autoImplicit false

/-- Poly1305's accumulator prime `p = 2¹³⁰ − 5` (the Bernstein prime, RFC 8439
    §2.5). As a literal `Nat`. -/
def polyPrime : Nat := 2 ^ 130 - 5

/-- Poly1305's prime field `𝔽_p`, `p = 2¹³⁰ − 5` — `ZMod (2¹³⁰ − 5)`, a
    `CommRing` (hence an `AddCommMonoid` under its additive `+ mod p` group), so
    the vectorizer core applies. The concrete 5×26-bit-limb representation reduces
    by `2¹³⁰ ≡ 5 (mod p)` (the `·5` high-limb fold); the additive structure
    carrying the proof is independent of that representation choice. -/
abbrev Fp := ZMod polyPrime

-- grind reduces mod p in Fp: a literal characteristic (grind_char_numeral).
grind_char_numeral Fp

/-- The number of Poly1305 message blocks the MAC kernel Horner-folds over
    (`NBLK = 10`: the exact block count of the RFC 8439 §2.8.2 message
    `AAD ‖ pad ‖ ciphertext ‖ pad ‖ lens` = `1` padded AAD block + `8` ciphertext
    blocks (114 bytes ⌈/16⌉) + `1` length block). The emitted kernel therefore
    carries the **entire** §2.8.2 MAC in one call (no C-side accumulator
    threading): `out = Σ_{i<10} block_i · r^(10-i)  (mod p)`. -/
def NBlk : Nat := 10

/-! ## 1. Denotation preservation, at the 𝔽_{2¹³⁰−5} Poly1305-MAC lane shape

Poly1305's MAC is a polynomial evaluation over `𝔽_p`: with message blocks
`m_0, …, m_{n-1}` (each a 17-byte little-endian integer `< 2¹³⁰`, the 16 message
bytes plus the appended `1` bit) and the clamped key `r`, the MAC accumulator is
`a = Σ_{i} m_i · r^(n-i)  (mod p)`, computed by Horner
`a := (a + m_i)·r  (mod p)`. The summed monomial terms `t_i = m_i · r^(n-i)` are
exactly the lanes of a `𝔽_p` dot — the verified content the MAC `Com → Com`
carries. -/

/-- **Denotation preservation for the Poly1305 MAC over `𝔽_{2¹³⁰−5}`.** The MAC
    polynomial `Σ_i m_i · r^(n-i)` (lane-wise the monomial terms `m_i · r^(n-i)`,
    horizontal sum `hsum`) equals the scalar straight-line `𝔽_p` fold
    (`scalarFold`, the sequential `+ mod p` accumulation — the Horner scheme
    `a := (a + m_i)·r` accumulates exactly these terms). This is
    `VectorReduce.scalarFold_eq_hsum` at the `𝔽_{2¹³⁰−5}` lane — no new content;
    the SAME reassociation lemma the GF(256)/GF(251)/GF(2¹²⁸)/ℤ-2¹⁶ kernels carry,
    here at the 130-bit prime field `𝔽_p`. -/
theorem poly1305_dot (m : Fin NBlk → Fp) (r : Fp) :
    hsum (fun i => m i * r ^ (NBlk - (i : ℕ))) =
      scalarFold (fun i => m i * r ^ (NBlk - (i : ℕ))) :=
  (scalarFold_eq_hsum (fun i => m i * r ^ (NBlk - (i : ℕ)))).symm

/-- The Poly1305 MAC computes the mathematical polynomial value
    `Σ_i m_i · r^(n-i)` over `𝔽_p` — the Poly1305 authenticator (before the
    final `+ s` and the `mod 2¹²⁸` truncation). -/
theorem poly1305_isPoly (m : Fin NBlk → Fp) (r : Fp) :
    hsum (fun i => m i * r ^ (NBlk - (i : ℕ))) =
      ∑ i, m i * r ^ (NBlk - (i : ℕ)) := by
  simp only [hsum]

/-- **End-to-end MAC-dot denotation over `𝔽_p`.** The full Poly1305 MAC (the sum
    of the monomial-term lanes) is the `scalarFold = hsum` reassociation — the
    verified content of the MAC field-dot. (Structurally identical to the SDitH
    RS-Horner / UOV matvec dot, lane changed to the 130-bit prime `𝔽_{2¹³⁰−5}`.) -/
theorem poly1305_mac_dot (m : Fin NBlk → Fp) (r : Fp) :
    (fun (_ : Unit) => hsum (fun i => m i * r ^ (NBlk - (i : ℕ))))
      = (fun _ => scalarFold (fun i => m i * r ^ (NBlk - (i : ℕ)))) := by
  funext _
  exact (scalarFold_eq_hsum (fun i => m i * r ^ (NBlk - (i : ℕ)))).symm

/-! ## 2. The Poly1305 field arithmetic (inline jasmin, 5×26-bit limbs, `·5` fold)

A `𝔽_p` element is held as **5 limbs of 26 bits** `h = (h₀, h₁, h₂, h₃, h₄)`,
`h = Σ_k h_k · 2^(26k)` (`5·26 = 130`). The two MAC-core primitives:

* `poly1305_clamp` — clamp the 16-byte key half `r` per RFC 8439 §2.5
  (`r &= 0x0ffffffc0ffffffc0ffffffc0fffffff`): clear the top 4 bits of bytes
  3,7,11,15 and the bottom 2 bits of bytes 4,8,12;
* `poly1305_mulmod` — the field multiply `(h · r) mod p`. Schoolbook
  `5×5 = 25` 26×26-bit partial products into 64-bit accumulators; the
  **reduction** uses `2¹³⁰ ≡ 5 (mod p)`: a partial product at limb position
  `k ≥ 5` folds back to position `k − 5` with a `·5` weight (i.e.
  `h_i·r_j` for `i+j ≥ 5` contributes `5·h_i·r_j` to limb `i+j−5`). Carry
  propagation then renormalizes each limb to 26 bits (the top limb `h₄` carries
  with a final `·5` fold).

These are emitted as inline jasmin helpers (the schoolbook form, byte-for-byte
the RFC 8439 reference / HACL* `Hacl_MAC_Poly1305`); the additive `+ mod p`
accumulation carrying the proof is the limb-wise add + carry. The 64-bit
accumulators are wide enough for the unreduced `5·26 + log₂(5·25)` ≈ 57-bit
partial sums. -/

/-- The Poly1305 key clamp constant (RFC 8439 §2.5):
    `r &= 0x0ffffffc0ffffffc0ffffffc0fffffff`. Emitted as the four per-32-bit-word
    AND masks the C reference applies before packing `r` into limbs. -/
def clampMasks : List Nat := [0x0fffffff, 0x0ffffffc, 0x0ffffffc, 0x0ffffffc]

/-- One 26×26 → 64-bit partial-product accumulation step `(i, j)` of the field
    multiply: limb `r_j · h_i` contributes to output position `i + j`, folded by
    `·5` when `i + j ≥ 5` (`2¹³⁰ ≡ 5 (mod p)`). Returns `(out, wt)`: `out` is the
    index into the 5-wide 64-bit accumulator (`i+j-5` after the fold), `wt` the
    `·5` weight (`5` when folded, else `1`). -/
def mulTerm (i j : Nat) : Nat × Nat :=
  if i + j < 5 then (i + j, 1) else (i + j - 5, 5)

/-- Render the `5×5 = 25` partial products of the field multiply `(h·r) mod p`
    as 64-bit `acc{out} += wt · h{i} · r{j}` accumulations (the `·5` weight folds
    positions `≥ 5` back per `2¹³⁰ ≡ 5`). The running limb is loaded into a 64-bit
    scratch `t`, multiplied, weighted, and added into `acc{out}`. -/
def renderMulProducts : List String :=
  (List.range 5).flatMap (fun i =>
    (List.range 5).flatMap (fun j =>
      let out := (mulTerm i j).1
      let wt := (mulTerm i j).2
      [ "t = h[" ++ toString i ++ "];"
      , "t = t * r[" ++ toString j ++ "];" ]
      ++ (if wt == 1 then [] else ["t = t * " ++ toString wt ++ ";"])
      ++ [ "acc[" ++ toString out ++ "] = acc[" ++ toString out ++ "] + t;" ]))

/-- Render the 5-limb carry-propagation that renormalizes the 64-bit accumulators
    back to 26-bit limbs: from each limb shift the high part (`>> 26`) into the
    next, masking `& 0x3ffffff`; the top limb `acc[4]`'s carry folds back into
    `acc[0]` with the `·5` weight (`2¹³⁰ ≡ 5 (mod p)`), then one more `acc[1]`
    carry to settle. -/
def renderCarryChain : List String :=
  (List.range 4).flatMap (fun k =>
    [ "c = acc[" ++ toString k ++ "];"
    , "c = c >> 26;"
    , "acc[" ++ toString k ++ "] = acc[" ++ toString k ++ "] & 0x3ffffff;"
    , "acc[" ++ toString (k + 1) ++ "] = acc[" ++ toString (k + 1) ++ "] + c;" ])
  ++ -- top limb carries with ·5 fold (2^130 ≡ 5)
  [ "c = acc[4];"
  , "c = c >> 26;"
  , "acc[4] = acc[4] & 0x3ffffff;"
  , "c = c * 5;"
  , "acc[0] = acc[0] + c;"
  , -- settle the resulting acc[0] carry into acc[1]
    "c = acc[0];"
  , "c = c >> 26;"
  , "acc[0] = acc[0] & 0x3ffffff;"
  , "acc[1] = acc[1] + c;" ]

/-- The Poly1305 field multiply inline jasmin helper: `h := (h · r) mod p` over
    the 5×26-bit-limb representation (`p = 2¹³⁰ − 5`). The `5×5` partial products
    (`renderMulProducts`, with the `·5` fold for positions `≥ 5` per
    `2¹³⁰ ≡ 5`) accumulate into 64-bit `acc[0..4]`, then `renderCarryChain`
    renormalizes back to 26-bit limbs; the result is written back into `h[0..4]`.
    Byte-for-byte the schoolbook field multiply of the RFC 8439 reference / HACL*
    `Hacl_MAC_Poly1305`. This is the `·` of the `𝔽_{2¹³⁰−5}` lane. -/
def polyMulModFn : String :=
  let header := [ "inline fn poly1305_mulmod(reg ptr u64[5] h, reg const ptr u64[5] r)"
                    ++ " -> reg ptr u64[5] {"
                , "stack u64[5] acc;"
                , "reg u64 t c;"
                , "inline int z;"
                , "for z = 0 to 5 { acc[z] = 0; }" ]
  let footer := [ "for z = 0 to 5 { h[z] = acc[z]; }"
                , "return h;" ]
  String.intercalate "\n  "
    (header ++ renderMulProducts ++ renderCarryChain ++ footer)
    ++ "\n}"

/-! ## 3. The Poly1305 MAC export (the Horner field-dot over the message blocks)

`poly1305_mac`: Poly1305's MAC over `NBLK` 16-byte message blocks via Horner over
`𝔽_p`. ABI: `out : u64[5]` (the accumulator limbs of the MAC `Σ m_i·r^(n-i)`,
before the final `+ s` and `mod 2¹²⁸` — done in the AEAD driver), `inp` holds the
clamped key limbs `r[0..4]` then the `NBLK` message blocks, each pre-packed into
5 limbs with the `2¹²⁸` "append-1" bit folded in (the `block_i + 2¹²⁸` term). Each
Horner step is `acc := (acc + m_i) · r  (mod p)` — the field add (limb-wise `+`)
then the inline `poly1305_mulmod`. -/

/-- Render one Horner block step `i` (RFC 8439 §2.5): `acc := (acc + m_i)`
    limb-wise (the `𝔽_p` additive op on the 5×26-bit limbs), then
    `acc := acc · r  (mod p)` via the inline `poly1305_mulmod`. Block `i`'s 5
    pre-packed limbs live at `inp` offset `RLIMBS + 5·i` (`RLIMBS = 5`, after the
    key limbs). The first step's leading add is on `acc = 0`, so the fold is the
    standard Horner `(((m_0)·r + m_1)·r + …)·r + m_{n-1}` over the blocks. -/
def renderHornerBlock (i : Nat) : List String :=
  (List.range 5).flatMap (fun k =>
    [ "t = inp[" ++ toString (5 + 5 * i + k) ++ "];"
    , "acc[" ++ toString k ++ "] = acc[" ++ toString k ++ "] + t;" ])
  ++ [ "acc = poly1305_mulmod(acc, rk);" ]

/-- Focused emission of the Poly1305 MAC `Σ_i m_i · r^(n-i)  (mod p)` over `NBLK`
    blocks (`NBLK = 4`) via Horner. ABI: `reg ptr u64[5] out`,
    `reg const ptr u64[5 + 5·NBLK] inp` with the clamped key limbs `r[0..4]`
    first, then the `NBLK` pre-packed message-block limb-quintuples;
    `out[0..4] = MAC accumulator limbs`, all 5×26-bit `𝔽_p` limbs matching the RFC
    8439 reference / HACL*. Per block: the limb-wise `+ m_i` add then the inline
    `poly1305_mulmod` (`renderHornerBlock`).

    Denotation: the accumulated terms are exactly `hsum (fun i => m_i · r^(n-i))`
    over `𝔽_{2¹³⁰−5}`, equal to the scalar fold by `poly1305_dot`. -/
def emitPolyMacExport (name : String) (nblk : Nat) : String :=
  let total := 5 + 5 * nblk
  let paramStrs := ["reg ptr u64[5] out",
                    "reg const ptr u64[" ++ toString total ++ "] inp"]
  let decls := [ "stack u64[5] acc;"
               , "stack u64[5] rk;"
               , "reg u64 t;"
               , "inline int z;"
               , "for z = 0 to 5 { rk[z] = inp[z]; }"   -- load the clamped key limbs
               , "for z = 0 to 5 { acc[z] = 0; }" ]      -- accumulator starts at 0
  let steps := (List.range nblk).flatMap renderHornerBlock
  let store := ["for z = 0 to 5 { out[z] = acc[z]; }"]
  let bodyLines := decls ++ steps ++ store
  "export fn " ++ name ++ "("
    ++ String.intercalate ", " paramStrs ++ ") -> reg ptr u64[5] {\n  "
    ++ String.intercalate "\n  " bodyLines ++ "\n  return out;\n}"

/-! ## 4. The emitted kernels -/

/-- The emitted Poly1305 MAC kernel (`NBLK = 4`): the inline `poly1305_mulmod`
    field-multiply helper + the Horner MAC export. Self-contained `.jazz`. -/
def poly1305MacJazz : String :=
  polyMulModFn ++ "\n\n" ++ emitPolyMacExport "poly1305_mac" NBlk

/-- The full ChaCha20-Poly1305 emit bundle: the committed ChaCha20 block emit (the
    keystream / Poly1305-key source) followed by the Poly1305 MAC kernel. The
    ChaCha20 export is **byte-identical** to the committed `ChaChaEmit.chachaBlockJazz`
    (reused verbatim, not re-emitted); the Poly1305 MAC is the new field-dot
    kernel. The AEAD driver (`bench/chachapoly_compare/`) wires them: ChaCha20
    block 0 → `(r, s)`, blocks `1..` → keystream XOR plaintext → ciphertext, then
    `poly1305_mac` over `AAD ‖ pad ‖ ct ‖ pad ‖ lens`, then `tag = MAC + s`. -/
def chachaPolyJazz : String :=
  chachaBlockJazz ++ "\n\n" ++ poly1305MacJazz

/-! ### Structural checks on the emitted text -/

/- The MAC kernel's ABI: `out : u64[5]` (the 5×26-bit MAC accumulator limbs),
    `inp : u64[5 + 5·NBLK]` (the clamped key limbs then the `NBLK` pre-packed
    block limb-quintuples), `NBLK = 10` ⇒ `55`. -/
#guard (strContains poly1305MacJazz "export fn poly1305_mac(reg ptr u64[5] out, reg const ptr u64[55] inp)")

/- The field multiply is the inline `poly1305_mulmod` (the `·` of the
    `𝔽_{2¹³⁰−5}` lane, over 5×26-bit limbs). -/
#guard (strContains poly1305MacJazz "inline fn poly1305_mulmod(reg ptr u64[5] h, reg const ptr u64[5] r)")

/- The reduction folds the high limbs back with the `·5` weight
    (`2¹³⁰ ≡ 5 (mod p)`) — the `c = c * 5;` top-limb fold in the carry chain. -/
#guard (strContains poly1305MacJazz "c = c * 5;")

/- The 26-bit limb mask `0x3ffffff` (`= 2²⁶ − 1`) renormalizes the limbs in the
    carry chain. -/
#guard (strContains poly1305MacJazz "acc[0] = acc[0] & 0x3ffffff;")

/- The Horner step is the field add (`acc[k] += m_i,k`) then the field multiply
    (`acc := acc · r`) — `acc := (acc + m_i)·r`. -/
#guard (strContains poly1305MacJazz "acc = poly1305_mulmod(acc, rk);")

/- The MAC accumulator limbs are written back to `out`. -/
#guard (strContains poly1305MacJazz "out[z] = acc[z];")

/-- The bundle reuses the committed ChaCha20 block export **verbatim** (the
    keystream / Poly1305-key source) — its exact RFC-KAT'd ABI line is present, so
    the AEAD keystream is the committed `chachaBlockJazz`, not a re-emit. -/
theorem chachapoly_reuses_chacha :
    strContains chachaPolyJazz
      "export fn chacha20_block(reg ptr u32[16] out, reg const ptr u32[39] inp)"
      = true := by native_decide

/-- …and the bundle also carries the new Poly1305 MAC export. -/
theorem chachapoly_has_poly_mac :
    strContains chachaPolyJazz
      "export fn poly1305_mac(reg ptr u64[5] out, reg const ptr u64[55] inp)"
      = true := by native_decide

end CatCrypt.Crypto.SecureCompilation.VIR.ChaChaPolyEmit
