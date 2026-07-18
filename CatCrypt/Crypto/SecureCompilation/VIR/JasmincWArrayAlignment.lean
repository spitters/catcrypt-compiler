/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.JasmincSemAlignment

/-!
# Aligning our element-indexed stack arrays with jasmin's byte-addressed `WArray`

`JasmincSemAlignment.lean` discharges the ALU/cast obligations and records the
load/store correspondence as the §4 residual: our `stackLoad`/`stackStore`
(element-indexed: a `stackArr w n` is `Fin n → BitVec w`, `stackGet arr k`
reads index `k`, `stackSet arr k v` updates it — `JasminDialect.lean`) must
correspond to jasmin's `WArray.get`/`WArray.set` (byte-addressed: a jasmin
`array len` is a `len`-byte array; `get len al aa ws a p` reads a `word ws` and
`set` writes one; for an `AAscale` access at element index `p` the byte offset
is `p * (ws/8)`, with little-endian byte assembly).

This file discharges that residual. It transcribes jasmin's `WArray` **value**
model (each `def` annotated with the `warray_.v` / `memory_model.v` line it
mirrors), builds the element ↔ byte encoding between our `stackArr w n` and a
byte array `jByteArr (n * (w / 8))`, proves the encode/decode round trip, and
proves the load/store correspondence (`stackGet` ↔ scaled `WArray.get`,
`stackSet` ↔ scaled `WArray.set`). The final bundle `stackMem_agrees_jasmin`
is the byte-memory analogue of `JasmincSemAlignment.alu_cast_agrees_jasmin`.

## Scope and what is *not* modelled

* **Byte-multiple widths.** We restrict to `w ∈ {8, 16, 32, 64}` (`w` a
  multiple of `8`), which is exactly the set our jasmin emitter uses (`reg u8/
  u16/u32/u64` array elements). The byte count per element is `w / 8`, and
  `8 * (w / 8) = w` holds for these widths — the round trip relies on this.
* **The `is_init` mask is a *safety* concern, not a *value* concern.** jasmin's
  `WArray.get8`/`set8` (`warray_.v:93/98`) additionally assert `in_bound` and
  `is_init` (returning `ErrOob`/`ErrAddrUndef` on failure). Those guard memory
  safety (no out-of-bounds / uninitialised reads); they do not change the *value*
  read on a successful access. Since our `stackArr` is a total `Fin n → BitVec w`
  (always in bounds, always initialised), we model the value layer only and omit
  the `is_init`/`in_bound` masks. The safety side is enforced upstream by the
  type `Fin n` and is orthogonal to the value correspondence proved here.

## jasmin source mirrored

* `proofs/lang/warray_.v` — `WArray.array`, `get8`/`set8`, `get`/`set`,
  `mk_scale`.
* `proofs/lang/memory_model.v` — `LE.encode`/`decode`/`wread8`, `CoreMem.read`/
  `write` (little-endian byte assembly of a `word ws`).
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasmincWArrayAlignment

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. jasmin's `WArray` value model, transcribed

A jasmin `WArray.array len` (`warray_.v:27`) is a `len`-byte map. At the value
layer (dropping the `is_init`/`in_bound` safety masks; see the module note) it
is a total function from byte index to `u8 = word U8 = BitVec 8`. -/

/-- jasmin byte array: `WArray.array nbytes` at the value layer
    (`warray_.v:27`, `arr_data : Mz.t u8`, here total). -/
@[reducible] def jByteArr (nbytes : Nat) : Type := Fin nbytes → BitVec 8

/-- jasmin `WArray.get8 m i` value (`warray_.v:93`), dropping the
    `in_bound`/`is_init` asserts: byte `i` of the array. -/
def jGet8 {nbytes : Nat} (m : jByteArr nbytes) (i : Fin nbytes) : BitVec 8 := m i

/-- jasmin `WArray.set8 m i v` value (`warray_.v:98`), dropping the `in_bound`
    assert: the array with byte `i` overwritten by `v` (`Mz.set`). -/
def jSet8 {nbytes : Nat} (m : jByteArr nbytes) (i : Fin nbytes) (v : BitVec 8) :
    jByteArr nbytes := fun j => if j = i then v else m j

/-! ### Little-endian byte split/join of a single `word w`

`memory_model.v:39` `LE.wread8 ws v k = nth 0 (LE.encode v) k` with
`LE.encode = split_vec U8` (`memory_model.v:17`): byte `k` of `v` is its `k`-th
little-endian byte, i.e. bits `[8k, 8k+8)` of `v`. We mirror `LE.wread8` with
`BitVec.extractLsb'`. `LE.decode = make_vec` (`memory_model.v:18`) reassembles
the bytes little-endian; we mirror it with an OR-fold of width-`w` shifted
bytes — the same bit layout `make_vec`/`wcat` produces. -/

/-- byte `k` (little-endian) of a `word w`: bits `[8k, 8k+8)`.
    Mirrors `LE.wread8` (`memory_model.v:39`) / `LE.encode = split_vec U8`. -/
def leByte {w : Nat} (v : BitVec w) (k : Nat) : BitVec 8 :=
  BitVec.extractLsb' (8 * k) 8 v

/-- reassemble the first `c` little-endian bytes produced by `bytes` into a
    `word w`. `decodeAux w c bytes = ⊕_{k < c} (bytes k).setWidth w <<< (8*k)`.
    Mirrors `LE.decode = make_vec` (`memory_model.v:18`): little-endian byte
    concatenation. -/
def decodeAux (w : Nat) : (c : Nat) → (bytes : Nat → BitVec 8) → BitVec w
  | 0, _ => 0
  | (c + 1), bytes =>
      decodeAux w c bytes ||| ((bytes c).setWidth w <<< (8 * c))

/-- Decode `nbytes = w / 8` little-endian bytes (read from `bytes`) into a
    `word w`. Mirrors `LE.decode sz l` (`memory_model.v:18, 151`). -/
def leDecode (w : Nat) (bytes : Nat → BitVec 8) : BitVec w :=
  decodeAux w (w / 8) bytes

/-! ### Bit-level characterisation of the decode

`decodeAux` is an OR of disjoint windows: byte `k` lands in bits `[8k, 8k+8)`.
So bit `i` of `decodeAux w c bytes` is bit `(i % 8)` of byte `(i / 8)` whenever
`i / 8 < c` (and `i < w`), else `false`. -/

theorem getLsbD_decodeAux (w : Nat) (bytes : Nat → BitVec 8) (c i : Nat) :
    (decodeAux w c bytes).getLsbD i =
      (decide (i / 8 < c) && (bytes (i / 8)).getLsbD (i % 8) && decide (i < w)) := by
  induction c with
  | zero => simp [decodeAux]
  | succ c ih =>
      simp only [decodeAux, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_setWidth, ih]
      rcases Nat.lt_trichotomy (i / 8) c with h | h | h
      · -- byte lives strictly before `c`: the new window contributes nothing.
        have h1 : i < 8 * c := by omega
        have h2 : i / 8 < c + 1 := by omega
        simp [h, h1, h2]
      · -- byte is exactly `c`: this is the window that holds bit `i`.
        subst h
        have h1 : i - 8 * (i / 8) = i % 8 := by omega
        have h2 : ¬ i < 8 * (i / 8) := by omega
        have h3 : i / 8 < i / 8 + 1 := by omega
        have h4 : i % 8 ≤ i := Nat.mod_le _ _
        simp only [h1, h2, h3, Nat.lt_irrefl, decide_false, Bool.false_and,
          Bool.false_or, decide_true, Bool.true_and]
        by_cases hw : i < w
        · have : i % 8 < w := by omega
          simp [hw, this]
        · simp [hw]
      · -- byte index past `c`: out of this byte's 8-bit window, contributes nothing.
        have h1 : ¬ i / 8 < c := by omega
        have h2 : ¬ i / 8 < c + 1 := by omega
        have h5 : 8 ≤ i - 8 * c := by omega
        simp [h1, h2, BitVec.getLsbD_of_ge (bytes c) (i - 8 * c) h5]

/-- bit `i` of byte `k = i/8` (extracted by `leByte`) is bit `i` of `v` itself:
    `(leByte v (i/8)).getLsbD (i%8) = v.getLsbD i`. -/
theorem getLsbD_leByte_div {w : Nat} (v : BitVec w) (i : Nat) :
    (leByte v (i / 8)).getLsbD (i % 8) = v.getLsbD i := by
  simp only [leByte, BitVec.getLsbD_extractLsb']
  have h1 : i % 8 < 8 := Nat.mod_lt _ (by omega)
  have h2 : 8 * (i / 8) + i % 8 = i := by omega
  simp [h1, h2]

/-- **Single-element little-endian round trip.** For a byte-multiple width
    (`8 * (w / 8) = w`, i.e. `w ∈ {8,16,32,…}`), splitting a `word w` into its
    little-endian bytes (`leByte`) and reassembling (`leDecode`) is the
    identity. This is jasmin's `LE.decodeK` (`memory_model.v:26`,
    `decode (encode w) = w`) in our bit model. -/
theorem leDecode_leByte {w : Nat} (hw : 8 * (w / 8) = w) (v : BitVec w) :
    leDecode w (leByte v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [leDecode, getLsbD_decodeAux, getLsbD_leByte_div]
  have hdiv : i / 8 < w / 8 := by omega
  simp [hdiv, hi]

/-- `decodeAux` only consults bytes `< c`, so it respects pointwise agreement
    of the byte stream there. -/
theorem decodeAux_congr (w c : Nat) {f g : Nat → BitVec 8}
    (h : ∀ k < c, f k = g k) : decodeAux w c f = decodeAux w c g := by
  induction c with
  | zero => rfl
  | succ c ih =>
      simp only [decodeAux]
      rw [ih (fun k hk => h k (by omega)), h c (by omega)]

/-- `leDecode` only consults bytes `< w / 8`. -/
theorem leDecode_congr (w : Nat) {f g : Nat → BitVec 8}
    (h : ∀ k < w / 8, f k = g k) : leDecode w f = leDecode w g :=
  decodeAux_congr w (w / 8) h

/-! ## 2. The element ↔ byte encoding

Our `stackArr w n = Fin n → BitVec w` is element-indexed; jasmin's array is
byte-indexed (`jByteArr (n * (w / 8))`). A `w`-bit element occupies `w / 8`
contiguous bytes; element `k`'s bytes are `[k * (w / 8), k * (w / 8) + w / 8)`,
little-endian. `encode` lays the elements out into that byte map; `decode` reads
them back. -/

/-- the per-element byte width `w / 8`, abbreviated. -/
@[reducible] def bw (w : Nat) : Nat := w / 8

/-- Encode an element-indexed `stackArr w n` into the byte-indexed jasmin array
    `jByteArr (n * (w / 8))`. Byte `b` is byte `(b % (w/8))` (little-endian) of
    element `(b / (w/8))`. -/
def encode {w n : Nat} (a : Fin n → BitVec w) : jByteArr (n * bw w) :=
  fun b => leByte (a ⟨b.val / bw w, by
      -- `b.val < n * (w/8)` and `w/8 > 0` give `b.val / (w/8) < n`.
      have hb := b.isLt
      have hcomm : n * bw w = bw w * n := Nat.mul_comm _ _
      have hmul : b.val < bw w * n := by omega
      exact Nat.div_lt_of_lt_mul hmul⟩) (b.val % bw w)

/-! ### jasmin's scaled `WArray.get` / `WArray.set` (the `AAscale` accessors)

`WArray.get len al AAscale ws a p = CoreMem.read a al (p * mk_scale AAscale ws) ws`
(`warray_.v:147`) with `mk_scale AAscale ws = wsize_size ws = ws / 8`
(`warray_.v:22`). `CoreMem.read` (`memory_model.v:148`) reads `ws / 8` bytes
`get a (ptr + k)` for `k ∈ [0, ws/8)` and assembles them little-endian
(`LE.decode`). So at element index `p = k` the byte offset is `k * (w / 8)` and
we read `w / 8` little-endian bytes. (We drop the `is_aligned_if`/`is_init`/
`in_bound` asserts; see the module note — they are safety, not value.) -/

/-- jasmin `WArray.get len Aligned AAscale w a k` value (`warray_.v:147`,
    `CoreMem.read … (k * (w/8)) w`): little-endian `word w` at byte offset
    `k * (w / 8)`. Out-of-range bytes read `0` (our arrays are always in range,
    so this default is never reached for `k < n`). -/
def jArrGetScaled (w n : Nat) (a : jByteArr (n * bw w)) (k : Nat) : BitVec w :=
  leDecode w (fun i => if h : k * bw w + i < n * bw w then a ⟨k * bw w + i, h⟩ else 0)

/-- jasmin `WArray.set Aligned AAscale a k v` value (`warray_.v:150`,
    `CoreMem.write … (k * (w/8)) v`): overwrite the `w / 8` little-endian bytes
    of element `k` (byte offset `k * (w / 8)`) with the bytes of `v`; other bytes
    unchanged. -/
def jArrSetScaled (w n : Nat) (a : jByteArr (n * bw w)) (k : Nat) (v : BitVec w) :
    jByteArr (n * bw w) :=
  fun b => if (k * bw w ≤ b.val) ∧ (b.val < k * bw w + bw w)
           then leByte v (b.val - k * bw w) else a b

/-! ### The scaled accessors decompose into the byte primitives `jGet8`/`jSet8`

`WArray.get`/`set` are defined via `CoreMem.read`/`write`, themselves built from
the per-byte `get8`/`set8` (`warray_.v:93/98`, our `jGet8`/`jSet8`). These two
lemmas record that decomposition: a scaled get is the little-endian assembly of
per-byte `jGet8` reads, and a scaled set is a per-byte `jSet8` write inside the
window (identity outside). They keep the §1 byte transcriptions load-bearing. -/

/-- A scaled `WArray.get` is `LE.decode` over per-byte `jGet8` reads at the
    scaled offset (`memory_model.v:148-151`, `CoreMem.read` = `decode ∘ map get`). -/
theorem jArrGetScaled_eq_decode_jGet8 (w n : Nat) (a : jByteArr (n * bw w)) (k : Nat) :
    jArrGetScaled w n a k =
      leDecode w (fun i => if h : k * bw w + i < n * bw w
                           then jGet8 a ⟨k * bw w + i, h⟩ else 0) := rfl

/-- A scaled `WArray.set` writes the window byte-by-byte with `jSet8`: byte
    `b` in `[k*bw, k*bw+bw)` becomes byte `(b - k*bw)` of `v`, others unchanged
    (`memory_model.v:153-156`, `CoreMem.write` = iterated `set8` of `encode v`). -/
theorem jArrSetScaled_apply (w n : Nat) (a : jByteArr (n * bw w)) (k : Nat)
    (v : BitVec w) (b : Fin (n * bw w)) :
    jArrSetScaled w n a k v b =
      if (k * bw w ≤ b.val) ∧ (b.val < k * bw w + bw w)
      then leByte v (b.val - k * bw w) else jGet8 a b := rfl

/-- Decode a jasmin byte array back to an element-indexed `stackArr w n`:
    element `k` is jasmin's scaled `WArray.get` at element index `k`. -/
def decode {w n : Nat} (m : jByteArr (n * bw w)) : Fin n → BitVec w :=
  fun k => jArrGetScaled w n m k.val

/-! ### Encode/decode round trip

`decode (encode a) = a`: laying out elements into the byte map and reading them
back is the identity (for byte-multiple widths). The key index facts are
`(k * bw + i) / bw = k` and `(k * bw + i) % bw = i` for `i < bw`. -/

theorem decode_encode {w n : Nat} (hw : 8 * (w / 8) = w) (hpos : 0 < w / 8)
    (a : Fin n → BitVec w) : decode (encode a) = a := by
  funext k
  simp only [decode, jArrGetScaled, encode]
  rw [show a k = leDecode w (leByte (a k)) from (leDecode_leByte hw (a k)).symm]
  apply leDecode_congr
  intro i hi
  -- byte index `k*bw + i` is in range; it decodes to byte `i` of element `k`.
  have hkn : k.val < n := k.isLt
  have hbpos : 0 < bw w := hpos
  have hbi : i < bw w := hi
  have hrange : k.val * bw w + i < n * bw w := by
    have hle : k.val * bw w + bw w ≤ n * bw w := by
      calc k.val * bw w + bw w = (k.val + 1) * bw w := by ring
        _ ≤ n * bw w := Nat.mul_le_mul_right _ (by omega)
    omega
  have hdiv : (k.val * bw w + i) / bw w = k.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hbpos, Nat.div_eq_of_lt hbi, Nat.zero_add]
  have hmod : (k.val * bw w + i) % bw w = i := by
    rw [Nat.mul_comm, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hbi
  simp only [hrange, dif_pos, hmod]
  congr 2
  exact Fin.ext hdiv

/-! ## 3. Load / store correspondence (the §4 residual, discharged)

The actual alignment obligation: our element-indexed `stackGet`/`stackSet` IS
jasmin's byte-addressed scaled `WArray.get`/`WArray.set` under the `encode`
bijection. -/

/-- **Load correspondence.** Reading element `k` (`k < n`) of our stack array
    equals jasmin's scaled `WArray.get` (`warray_.v:147`) of the byte image at
    element index `k`. So our `stackLoad` denotation IS jasmin's `WArray.get`. -/
theorem stackGet_eq_jArrGetScaled {w n : Nat} (hw : 8 * (w / 8) = w)
    (hpos : 0 < w / 8) (a : Fin n → BitVec w) (k : Nat) (hk : k < n) :
    stackGet a k = jArrGetScaled w n (encode a) k := by
  -- `jArrGetScaled … k = decode (encode a) ⟨k,hk⟩ = a ⟨k,hk⟩` by the round trip,
  -- and `stackGet a k = a ⟨k,hk⟩` since `k < n`.
  have hdec : jArrGetScaled w n (encode a) k = a ⟨k, hk⟩ := by
    have := congrFun (decode_encode hw hpos a) ⟨k, hk⟩
    simpa [decode] using this
  rw [hdec]
  -- `stackGet a k = a ⟨k % n, _⟩ = a ⟨k, _⟩` since `k < n`.
  have : stackGet a k = a ⟨k, hk⟩ := by
    have h := stackGet_id a ⟨k, hk⟩
    simpa using h
  rw [this]

/-- `stackSet a k v` at an in-range index `j < n`, with the stored index `k < n`,
    is `v` when `j = k` and `a ⟨j,_⟩` otherwise (the `% n` reductions are the
    identity here). The plumbing lemma behind the store correspondence. -/
theorem stackSet_apply_lt {w n : Nat} (a : Fin n → BitVec w) (k : Nat) (v : BitVec w)
    (j : Nat) (hj : j < n) (hk : k < n) :
    stackSet a k v ⟨j, hj⟩ = if j = k then v else a ⟨j, hj⟩ := by
  cases n with
  | zero => exact absurd hk (by omega)
  | succ m =>
      simp only [stackSet]
      have hkmod : k % (m + 1) = k := Nat.mod_eq_of_lt hk
      by_cases hjk : j = k
      · rw [if_pos (Fin.ext (by simp [hkmod, hjk])), if_pos hjk]
      · rw [if_neg, if_neg hjk]
        intro hcontra
        exact hjk (by have := Fin.mk.injEq .. ▸ hcontra; omega)

/-- **Store correspondence (naturality).** Updating element `k` (`k < n`) of our
    stack array and *then* encoding equals jasmin's scaled `WArray.set`
    (`warray_.v:150`) applied to the byte image. So our `stackStore` denotation
    IS jasmin's `WArray.set`: `encode ∘ stackSet = jArrSetScaled ∘ encode`. -/
theorem encode_stackSet_eq_jArrSetScaled {w n : Nat} (hpos : 0 < w / 8)
    (a : Fin n → BitVec w) (k : Nat) (hk : k < n) (v : BitVec w) :
    encode (stackSet a k v) = jArrSetScaled w n (encode a) k v := by
  funext b
  have hbpos : 0 < bw w := hpos
  have hcomm : n * bw w = bw w * n := Nat.mul_comm _ _
  -- element index `j = b/bw` and within-element byte `r = b%bw` of byte `b`.
  have hbeq : b.val / bw w * bw w + b.val % bw w = b.val := Nat.div_add_mod' b.val (bw w)
  have hjmod : b.val % bw w < bw w := Nat.mod_lt _ hbpos
  have hjlt : b.val / bw w < n := by
    have := b.isLt; exact Nat.div_lt_of_lt_mul (by omega)
  simp only [encode, jArrSetScaled]
  rw [stackSet_apply_lt a k v (b.val / bw w) hjlt hk]
  by_cases hjk : b.val / bw w = k
  · -- `b` lies in element `k`'s byte window: both sides read `leByte v (b%bw)`.
    have hwin : k * bw w ≤ b.val ∧ b.val < k * bw w + bw w := by
      constructor <;> [skip; skip] <;> rw [← hjk] <;> omega
    have hsub : b.val - k * bw w = b.val % bw w := by rw [← hjk]; omega
    simp only [hjk, hwin, and_self, if_pos, hsub]
  · -- `b` lies in a different element: both sides read `leByte (a ⟨b/bw,_⟩) (b%bw)`.
    have hwin : ¬ (k * bw w ≤ b.val ∧ b.val < k * bw w + bw w) := by
      rintro ⟨h1, h2⟩
      exact hjk (Nat.div_eq_of_lt_le h1 (by rw [Nat.add_one_mul]; omega))
    simp only [hjk, if_neg, not_false_iff, hwin]

/-! ## 4. The discharged memory obligation, bundled

The byte-memory analogue of `JasmincSemAlignment.alu_cast_agrees_jasmin`: our
element-indexed `stackGet`/`stackSet` are exactly jasmin's byte-addressed scaled
`WArray.get`/`WArray.set` under the `encode` bijection. With this, the §4
load/store residual of `JasmincSemAlignment.lean` is discharged — the remaining
trust shrinks to the §1 transcriptions (`jByteArr`, `jGet8`/`jSet8`, the
little-endian `leByte`/`leDecode`, `jArrGetScaled`/`jArrSetScaled`) mirroring
jasmin's `warray_.v`/`memory_model.v` definitions, eyeball-checkable line by
line, plus the documented omissions (the `is_init`/`in_bound`/`is_aligned_if`
safety masks, which do not affect the value read on a successful access). -/

/-- **The discharged load/store half of the alignment**, bundled (the §4
    residual of `JasmincSemAlignment.lean`). For byte-multiple widths `w`
    (`8 * (w / 8) = w` and `0 < w / 8`, i.e. `w ∈ {8,16,32,64}` — every width our
    jasmin emitter uses):

    1. **load**: our `stackGet a k` (`JasminDialect.stackLoad`) equals jasmin's
       scaled `WArray.get` (`warray_.v:147`) of the byte image at element `k`;
    2. **store**: encoding after our `stackSet a k v` (`JasminDialect.stackStore`)
       equals jasmin's scaled `WArray.set` (`warray_.v:150`) on the byte image.

    Together these say our element-indexed stack-array load/store IS jasmin's
    byte-addressed `WArray` load/store at the `AAscale` position. -/
theorem stackMem_agrees_jasmin {w n : Nat} (hw : 8 * (w / 8) = w) (hpos : 0 < w / 8) :
    (∀ (a : Fin n → BitVec w) (k : Nat), k < n →
        stackGet a k = jArrGetScaled w n (encode a) k)
    ∧ (∀ (a : Fin n → BitVec w) (k : Nat), k < n → ∀ (v : BitVec w),
        encode (stackSet a k v) = jArrSetScaled w n (encode a) k v) :=
  ⟨fun a k hk => stackGet_eq_jArrGetScaled hw hpos a k hk,
   fun a k hk v => encode_stackSet_eq_jArrSetScaled hpos a k hk v⟩

end CatCrypt.Crypto.SecureCompilation.VIR.JasmincWArrayAlignment
