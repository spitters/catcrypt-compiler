/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Primitives.HMAC
public meta import CatCrypt.Crypto.Primitives.HMAC
public import CatCryptCore.Tactics.KatGuard

/-!
# SHA-256 and HMAC-SHA256 on inputs of any length

`mdIterate comp iv msg` pads `msg` as FIPS 180-4 §5.1.1 prescribes (a `0x80` byte, zero
bytes, and the 64-bit big-endian bit length, to a multiple of 64 bytes), splits the result
into 64-byte blocks and folds the compression function `comp` over them from `iv`. The
compression function is a parameter, so the padding and the block split are independent of
it. `sha256Multi` is `mdIterate` at the compression `SHA256.compress` from `SHA256.hInit`,
serialized by `SHA256.serializeState`, and `hmacSha256Multi` is HMAC-SHA256 (RFC 2104)
over it for keys and messages of any length.

## Main results

* `sha256Multi_eq_sha256Short`: on a message of at most 55 bytes, `sha256Multi` is the
  byte list of `SHA256.sha256Short`.
* `sha256Multi_eq_sha256TwoBlock`: on a 64-byte block followed by at most 55 bytes,
  `sha256Multi` is the byte list of `SHA256.sha256TwoBlock`.
* `hmacSha256_eq_hmacSha256Multi`: for a key of at most 64 bytes and a message of at most
  55 bytes, `HMAC.hmacSha256` is `hmacSha256Multi`.

## References

* FIPS 180-4, §5.1.1 and §6.2 — SHA-256
* RFC 2104 — HMAC; RFC 4231 — HMAC-SHA256 test vectors
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Primitives.HMACMulti

open CatCrypt.Crypto.Primitives.SHA256 CatCrypt.Crypto.Primitives.HMAC

/-! ## Padding and block split -/

/-- The eight bytes of the 64-bit big-endian encoding of `bitLen` (FIPS 180-4, §5.1.1). -/
def lengthBytes (bitLen : Nat) : List UInt8 :=
  List.ofFn fun (j : Fin 8) => ((bitLen >>> (8 * (7 - j.val))) % 256).toUInt8

/-- FIPS 180-4 §5.1.1 padding of a byte message: the message, a `0x80` byte, the least
number of zero bytes that makes the total length a multiple of 64, and the 64-bit
big-endian bit length of the message. -/
def sha256Pad (msg : List UInt8) : List UInt8 :=
  msg ++ [0x80] ++ List.replicate ((119 - msg.length % 64) % 64) 0 ++
    lengthBytes (8 * msg.length)

/-- The 64-byte blocks of a byte list, in order; a last partial block is filled with zero
bytes. -/
def toBlocks : List UInt8 → List (Fin 64 → UInt8)
  | [] => []
  | b :: bs => listToBlock64 (b :: bs) :: toBlocks ((b :: bs).drop 64)
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; omega

/-! ## The iterated hash -/

/-- Merkle–Damgård iteration with SHA-256 padding: the fold of the compression function
`comp` from `iv` over the 64-byte blocks of `sha256Pad msg`. -/
def mdIterate {σ : Type} (comp : σ → (Fin 64 → UInt8) → σ) (iv : σ) (msg : List UInt8) :
    σ :=
  (toBlocks (sha256Pad msg)).foldl comp iv

/-- `SHA256.compress` on a state held as a vector of eight words. The chaining state between
blocks is a vector, so evaluating the iterated hash computes each compression once. -/
def compressVec (v : Vector UInt32 8) (block : Fin 64 → UInt8) : Vector UInt32 8 :=
  Vector.ofFn (compress (fun i => v[i]) block)

/-- SHA-256 (FIPS 180-4) of a byte message of any length, as its list of 32 bytes. -/
def sha256Multi (msg : List UInt8) : List UInt8 :=
  let v := mdIterate compressVec (Vector.ofFn hInit) msg
  List.ofFn (serializeState fun i => v[i])

/-- HMAC key preparation (RFC 2104): a key longer than 64 bytes is replaced by its SHA-256
hash; the result is padded with zero bytes to 64 bytes. -/
def prepareKeyMulti (key : List UInt8) : List UInt8 :=
  let k := if key.length > 64 then sha256Multi key else key
  k ++ List.replicate (64 - k.length) 0

/-- HMAC-SHA256 (RFC 2104) for keys and messages of any length:
`SHA256((K ⊕ opad) || SHA256((K ⊕ ipad) || text))`. -/
def hmacSha256Multi (key msg : List UInt8) : List UInt8 :=
  let k := prepareKeyMulti key
  sha256Multi (xorPad k opadByte ++ sha256Multi (xorPad k ipadByte ++ msg))

/-! ## Block-level facts -/

/-- The block of a list whose first 64 bytes are `l` is the block of `l`. -/
theorem listToBlock64_append_of_length (l r : List UInt8) (h : l.length = 64) :
    listToBlock64 (l ++ r) = listToBlock64 l := by
  funext i
  grind [listToBlock64]

/-- The block of the byte list of a block is that block. -/
theorem listToBlock64_ofFn (f : Fin 64 → UInt8) : listToBlock64 (List.ofFn f) = f := by
  funext i
  grind [listToBlock64]

/-- A 64-byte list is the byte list of its block. -/
theorem ofFn_listToBlock64 (l : List UInt8) (h : l.length = 64) :
    List.ofFn (listToBlock64 l) = l := by
  apply List.ext_getElem
  · simp [h]
  · grind [listToBlock64]

/-- The blocks of `l ++ r` for a 64-byte `l` are the block of `l` followed by the blocks
of `r`. -/
theorem toBlocks_append_of_length (l r : List UInt8) (h : l.length = 64) :
    toBlocks (l ++ r) = listToBlock64 l :: toBlocks r := by
  cases l with
  | nil => simp at h
  | cons b bs =>
    rw [List.cons_append, toBlocks, ← List.cons_append,
      listToBlock64_append_of_length _ _ h, List.drop_left' h]

/-- The final padded block of a tail of at most 55 bytes is `padFinal`. -/
theorem lastBlock_eq (t : List UInt8) (L : Nat) (ht : t.length ≤ 55) :
    t ++ [0x80] ++ List.replicate (55 - t.length) 0 ++ lengthBytes L =
      List.ofFn (padFinal t L) := by
  apply List.ext_getElem
  · simp [lengthBytes]
    omega
  · intro i h1 h2
    simp only [List.getElem_ofFn, padFinal, lengthBytes, List.getElem_append]
    grind

/-- The padding of `pre ++ t`, for `pre` a whole number of blocks and `t` of at most 55
bytes, is `pre` followed by the single block `padFinal t` of the total bit length. -/
theorem sha256Pad_of_short (pre t : List UInt8) (hp : pre.length % 64 = 0)
    (ht : t.length ≤ 55) :
    sha256Pad (pre ++ t) = pre ++ List.ofFn (padFinal t (8 * (pre.length + t.length))) := by
  have hz : (119 - (pre ++ t).length % 64) % 64 = 55 - t.length := by
    simp only [List.length_append]
    omega
  rw [sha256Pad, hz, ← lastBlock_eq t _ ht]
  simp

/-- On a message of at most 55 bytes, the iteration is one compression of `padFinal`. -/
theorem mdIterate_short {σ : Type} (comp : σ → (Fin 64 → UInt8) → σ) (iv : σ)
    (msg : List UInt8) (h : msg.length ≤ 55) :
    mdIterate comp iv msg = comp iv (padFinal msg (8 * msg.length)) := by
  have := sha256Pad_of_short [] msg rfl h
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at this
  rw [mdIterate, this, ← List.append_nil (List.ofFn _),
    toBlocks_append_of_length _ _ (by simp), listToBlock64_ofFn]
  simp [toBlocks]

/-- On a block followed by at most 55 bytes, the iteration is two compressions. -/
theorem mdIterate_twoBlock {σ : Type} (comp : σ → (Fin 64 → UInt8) → σ) (iv : σ)
    (block : Fin 64 → UInt8) (tail : List UInt8) (h : tail.length ≤ 55) :
    mdIterate comp iv (List.ofFn block ++ tail) =
      comp (comp iv block) (padFinal tail (8 * (64 + tail.length))) := by
  have := sha256Pad_of_short (List.ofFn block) tail (by simp) h
  simp only [List.length_ofFn] at this
  rw [mdIterate, this, toBlocks_append_of_length _ _ (by simp), listToBlock64_ofFn,
    ← List.append_nil (List.ofFn (padFinal _ _)),
    toBlocks_append_of_length _ _ (by simp), listToBlock64_ofFn]
  simp [toBlocks]

/-! ## Agreement with the bounded definitions -/

/-- Reading a state vector built from a state function gives that function. -/
theorem getElem_vector_ofFn (f : Fin 8 → UInt32) :
    (fun i : Fin 8 => (Vector.ofFn f)[i]) = f := by
  funext i
  simp

/-- The single-block padding is the final-block padding at the message's own bit length. -/
theorem padShort_eq_padFinal (msg : List UInt8) :
    padShort msg = padFinal msg (8 * msg.length) := by
  funext i
  simp only [padShort, padFinal]

/-- On a message of at most 55 bytes, `sha256Multi` is `sha256Short`. -/
theorem sha256Multi_eq_sha256Short (msg : List UInt8) (h : msg.length ≤ 55) :
    sha256Multi msg = List.ofFn (sha256Short msg) := by
  simp only [sha256Multi, mdIterate_short _ _ _ h, sha256Short, padShort_eq_padFinal,
    compressVec, getElem_vector_ofFn]

/-- On a 64-byte block followed by a tail of at most 55 bytes, `sha256Multi` is
`sha256TwoBlock`. -/
theorem sha256Multi_eq_sha256TwoBlock (block : Fin 64 → UInt8) (tail : List UInt8)
    (h : tail.length ≤ 55) :
    sha256Multi (List.ofFn block ++ tail) =
      List.ofFn (sha256TwoBlock block tail (64 + tail.length)) := by
  simp only [sha256Multi, mdIterate_twoBlock _ _ _ _ h, sha256TwoBlock, compressVec,
    getElem_vector_ofFn]

/-- On a 64-byte list followed by at most 55 bytes, `sha256Multi` is `sha256TwoBlock`. -/
theorem sha256Multi_append_of_length (l tail : List UInt8) (hl : l.length = 64)
    (h : tail.length ≤ 55) :
    sha256Multi (l ++ tail) =
      List.ofFn (sha256TwoBlock (listToBlock64 l) tail (l.length + tail.length)) := by
  have := sha256Multi_eq_sha256TwoBlock (listToBlock64 l) tail h
  rwa [ofFn_listToBlock64 l hl, ← hl] at this

/-- On a key of at most 64 bytes, the two key preparations agree. -/
theorem prepareKeyMulti_eq_prepareKey (key : List UInt8) (h : key.length ≤ 64) :
    prepareKeyMulti key = prepareKey key := by
  simp only [prepareKeyMulti, prepareKey, gt_iff_lt, Nat.not_lt.mpr h, ite_false]

/-- A padded key of at most 64 bytes has 64 bytes. -/
theorem xorPad_prepareKey_length (key : List UInt8) (h : key.length ≤ 64) (b : UInt8) :
    (xorPad (prepareKey key) b).length = 64 := by
  simp only [xorPad, prepareKey, List.length_map, gt_iff_lt, Nat.not_lt.mpr h, ite_false,
    List.length_append, List.length_replicate]
  omega

/-- For a key of at most 64 bytes and a message of at most 55 bytes, the two-block
`hmacSha256` is `hmacSha256Multi`. -/
theorem hmacSha256_eq_hmacSha256Multi (key msg : List UInt8) (hk : key.length ≤ 64)
    (hm : msg.length ≤ 55) :
    hmacSha256 key msg = hmacSha256Multi key msg := by
  simp only [hmacSha256Multi, prepareKeyMulti_eq_prepareKey key hk]
  rw [sha256Multi_append_of_length _ _ (xorPad_prepareKey_length key hk _) hm,
    sha256Multi_append_of_length _ _ (xorPad_prepareKey_length key hk _) (by simp), hmacSha256]

/-! ## Known-answer check: RFC 4231 test case 7 (131-byte key, 152-byte message) -/

set_option linter.hashCommand false in
set_option kat.ms 3000 in
#kat hmacSha256Multi (List.replicate 131 0xaa)
    ("This is a test using a larger than block-size key and a larger than block-size data. " ++
      "The key needs to be hashed before being used by the HMAC algorithm.").toUTF8.toList ==
  [0x9b, 0x09, 0xff, 0xa7, 0x1b, 0x94, 0x2f, 0xcb, 0x27, 0x63, 0x5f, 0xbc, 0xd5, 0xb0, 0xe9,
    0x44, 0xbf, 0xdc, 0x63, 0x64, 0x4f, 0x07, 0x13, 0x93, 0x8a, 0x7f, 0x51, 0x53, 0x5c, 0x3a,
    0x35, 0xe2]

end CatCrypt.Crypto.Primitives.HMACMulti
