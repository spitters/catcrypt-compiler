/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AesKernelRegistryEntry
public import CatCrypt.Crypto.SecureCompilation.GenericFieldEmitValue

/-!
# Concrete realizers for the AES-128 and field-op kernel rows — KAT-free

The AES block-cipher row (`AesKernelRegistryEntry`) and the field add/mul rows
(`GenericFieldEmitValue.FieldEmitRealizes`) each reduce a protocol's emit
obligation to a *leaf-realization* predicate — "the emitted kernel's leaf bytes
decode to `aes128_encrypt key` / to `(· + ·)` / `(· * ·)` over `ZMod q`".  Their
non-vacuity witnesses (`aesTableEntry`, `fieldEmitRealizes_canonical`) exhibit a
realizing `LeafSpec`, but `fieldEmitRealizes_canonical` does so only
**parametrically** over an abstract `encode`/`decode` pair with a *hypothesised*
section (`hsection : ∀ z, decode (encode z) = z`).

This module makes those sections **concrete and proved**, mirroring
`ConcreteNttRealizer.lean` (the concrete `encodeP`/`decodeP` byte codec with
`decodeP_encodeP` proved for all inputs, then an UNCONDITIONAL realization).  We
exhibit, for AES and for field add/mul:

* a genuine `RustVal .TFp = JArray 48 = Fin 48 → BitVec 8` byte carrier with a
  concrete `encode`/`decode` pair (no constructor-wrapping of a function, no
  `axiom`), and
* a **proved** round-trip `decode (encode x) = x` for **all** inputs (the
  byte-level fact a KAT would *assert*; here a theorem), and
* a spec-computing realizer `LeafSpec` under which the row's realization holds
  **unconditionally** — `aes_realizes_concrete` (`KernelRealizes`),
  `fieldAdd_realizes_concrete` / `fieldMul_realizes_concrete` (`KernelRealizes2`)
  — no KAT hypothesis.

## The byte codecs

* **AES** (`State = Fin 16 → UInt8`, 16 bytes): `encodeA` lays the 16 state bytes
  into the first 16 of the 48 carrier bytes (slot `i` ← `(s i).toBitVec`,
  little-endian byte order = state index order), zero in the tail.  `decodeA`
  reads byte slot `i` back as `(a i).toUInt8`.  The round-trip is the per-byte
  `BitVec`↔`UInt8` involution `(b.toBitVec).toUInt8 = b`.
* **Field** (`ZMod q`, single element): `encodeF` lays `(x.val)` little-endian
  into the first `width` carrier bytes (`width = ⌈log₂ q / 8⌉`-style, taken as a
  parameter with `q < 2^(8·width)`), zero in the tail.  `decodeF` reads the
  `width` bytes back base-256 mod `q`.  The round-trip is the base-256
  digit-reconstruction fact, valid whenever `q < 2^(8·width)`.

## HONEST scope — what this proves and what it does NOT

* **Proved (unconditional Lean theorem):** there are *concrete*, round-trip
  -verified byte codecs and *concrete*, spec-computing realizer `LeafSpec`s under
  which the AES / field-add / field-mul row realizations hold for **all** inputs
  — strictly stronger than *assuming* a KAT, because the byte-level
  decode-equals-spec fact is a theorem here, not a test vector.
* **NOT proved (the remaining residual):** that the *jasmin-emitted machine bytes*
  of the real AES / field-op kernels equal these realizers.  That equality —
  actual emitted assembly ≡ the realizer `LeafSpec` — is the owned-machine-code
  route and is a separate follow-up.  This file removes the *encoding* KAT (the
  `decode ∘ encode = id` assumption) for these families; it does **not** remove
  the *machine-code* obligation.

## References
* NIST FIPS 197 (AES-128)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.ProtocolEmitRealizes
open CatCrypt.Crypto.SecureCompilation.GenericKernelRealization
open CatCrypt.Crypto.SecureCompilation.AesKernelRegistryEntry
open CatCrypt.Crypto.SecureCompilation.GenericFieldEmitValue
open CatCrypt.Crypto.Primitives.AES128

/-! ## §1  AES: a concrete 16-into-48-byte codec over `RustVal .TFp`

`RustVal .TFp = JArray 48 = Fin 48 → BitVec 8`.  The AES carrier
`State = Fin 16 → UInt8` fits in the first 16 bytes.  `encodeA` writes
`(s i).toBitVec` into slot `i` (`i < 16`), `0` into the tail; `decodeA` reads slot
`i` back as `(a i).toUInt8`.  The round-trip is the per-byte involution
`(b.toBitVec).toUInt8 = b`. -/

/-- Encode a 16-byte AES state into the first 16 of the 48 carrier bytes
    (`slot i ← (s i).toBitVec` for `i < 16`, zero in the tail). -/
def encodeA (s : State) : RustVal .TFp :=
  fun b => if h : b.val < 16 then (s ⟨b.val, h⟩).toBitVec else 0

/-- Decode a carrier value back into a 16-byte AES state:
    `state i ← UInt8.ofBitVec (a i)` reading carrier byte slot `i`. -/
def decodeA (a : RustVal .TFp) : State :=
  fun i => UInt8.ofBitVec (a ⟨i.val, Nat.lt_of_lt_of_le i.isLt (by decide)⟩)

/-- **The verified AES round-trip (the crux).**  Decoding the concrete byte
    encoding of any AES state returns the state unchanged — for **all** inputs.
    The byte-level fact a KAT would merely *assert*; here a theorem. -/
theorem decodeA_encodeA (s : State) : decodeA (encodeA s) = s := by
  funext i
  simp only [decodeA, encodeA]
  rw [dif_pos (Nat.lt_of_lt_of_le i.isLt (by decide))]

/-- The concrete AES realizer's `CallSpec`: at the AES leaf it decodes the sole
    `.TFp` argument, applies `aes128_encrypt key`, and re-encodes via `encodeA`;
    off-leaf it returns `oldDest`. -/
def aesCallSpec (key : Key128) (leaf : String) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if fname = leaf then
      let pick : (Σ t : TowerType, RustVal t) → State := fun a =>
        if ht : a.1 = TowerType.TFp then decodeA (ht ▸ a.2) else (fun _ => 0)
      match args with
      | a :: _ =>
          if hd : _dt = TowerType.TFp then
            hd ▸ encodeA (aes128_encrypt key (pick a))
          else oldDest
      | _ => oldDest
    else oldDest

/-- The concrete AES realizer `LeafSpec`. -/
def aesLeafSpec (key : Key128) (leaf : String) (limbStore : LimbStoreSpec) :
    LeafSpec :=
  { call := aesCallSpec key leaf, limbStore := limbStore }

/-- **Unconditional AES kernel realization (no KAT, no abstract section).**  The
    concrete realizer `aesLeafSpec key …` decodes its leaf-call value to
    `aes128_encrypt key` of its decoded input for **every** input — proved by the
    round-trip `decodeA_encodeA`, not assumed via a test vector. -/
theorem aes_realizes_concrete (key : Key128) (leaf : String)
    (limbStore : LimbStoreSpec) :
    KernelRealizes decodeA (aes128_encrypt key) leaf
      (aesLeafSpec key leaf limbStore) := by
  intro xVal oldDest
  show decodeA (aesCallSpec key leaf leaf .TFp [.TFp] oldDest [⟨.TFp, xVal⟩])
    = aes128_encrypt key (decodeA xVal)
  simp only [aesCallSpec, ite_true, dite_true]
  rw [decodeA_encodeA]

/-- The AES realization is a row of the generic `AesKernelRealizes` seam — by
    `Iff.rfl` (`aes_iff_kernel`), with the encoding section now a *theorem*
    rather than an assumed KAT. -/
theorem aes_realizes_concrete' (key : Key128) (leaf : String)
    (limbStore : LimbStoreSpec) :
    AesKernelRealizes key decodeA leaf (aesLeafSpec key leaf limbStore) :=
  aes_realizes_concrete key leaf limbStore

/-! ## §2  Field add/mul: a concrete single-element base-256 codec over `RustVal .TFp`

A single `ZMod q` element laid out `width` bytes little-endian into the first
`width` of the 48 carrier bytes (`width = ⌈log₂ q / 8⌉`, a parameter with the
fitting hypothesis `q < 2^(8·width)`), zero in the tail.  `decodeF` reads the
`width` bytes back base-256, mod `q`.  The round-trip is a base-256 digit
-reconstruction fact (`Nat.ofDigits`-style), valid whenever `q < 2^(8·width)`. -/

/-- Encode a single `ZMod q` element into the first `width` carrier bytes,
    little-endian base-256 of `x.val`; zero in the tail.  (`width` must satisfy
    `width ≤ 48` and `q < 2^(8·width)` for the round-trip and fit.) -/
def encodeF {q : ℕ} [NeZero q] (width : ℕ) (x : ZMod q) : RustVal .TFp :=
  fun b =>
    if _h : b.val < width then BitVec.ofNat 8 ((x.val / 256 ^ b.val) % 256) else 0

/-- Decode the first `width` carrier bytes as a base-256 little-endian natural
    number, reduced mod `q`. -/
def decodeF {q : ℕ} [NeZero q] (width : ℕ) (a : RustVal .TFp) : ZMod q :=
  ((Finset.range width).sum
    (fun j => 256 ^ j * (a ⟨j % 48, Nat.mod_lt _ (by decide)⟩).toNat) : ℕ)

/-- Base-256 little-endian digit reconstruction: the `width`-digit base-256
    expansion of any natural `x` sums to `x % 256^width`.  Proved by induction on
    `width` from `Nat.mod_mul`.  (Standalone `Nat` arithmetic — the engine of the
    field round-trip.) -/
theorem base256_digit_sum (x : ℕ) :
    ∀ width : ℕ, (Finset.range width).sum
        (fun j => 256 ^ j * ((x / 256 ^ j) % 256)) = x % 256 ^ width := by
  intro width
  induction width with
  | zero => simp [Nat.mod_one]
  | succ w ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      rw [Nat.mod_mul]

/-- **The verified field round-trip (the crux).**  For `width ≤ 48` and
    `q < 2^(8·width)`, decoding the concrete base-256 byte encoding of a `ZMod q`
    element returns it unchanged — for **all** inputs.  The byte-level fact a KAT
    would merely *assert*; here a theorem. -/
theorem decodeF_encodeF {q : ℕ} [NeZero q] (width : ℕ) (hw : width ≤ 48)
    (hq : q < 2 ^ (8 * width)) (x : ZMod q) :
    decodeF width (encodeF width x) = x := by
  have hxval : x.val < 2 ^ (8 * width) := lt_of_lt_of_le (ZMod.val_lt x) (le_of_lt hq)
  simp only [decodeF, encodeF]
  -- Each byte slot `j < width` reads back `(x.val / 256^j) % 256`.
  have hbytes : ∀ j ∈ Finset.range width,
      256 ^ j *
        ((if h : (⟨j % 48, Nat.mod_lt _ (by decide)⟩ : Fin 48).val < width then
          BitVec.ofNat 8 ((x.val / 256 ^ (⟨j % 48, Nat.mod_lt _ (by decide)⟩ : Fin 48).val) % 256)
          else 0)).toNat
      = 256 ^ j * ((x.val / 256 ^ j) % 256) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjm : j % 48 = j := Nat.mod_eq_of_lt (lt_of_lt_of_le hj hw)
    simp only [hjm]
    rw [dif_pos hj, BitVec.toNat_ofNat]
    have hlt : (x.val / 256 ^ j) % 256 < 2 ^ 8 := Nat.mod_lt _ (by decide)
    rw [Nat.mod_eq_of_lt hlt]
  rw [Finset.sum_congr rfl hbytes]
  -- The base-256 digit sum reconstructs `x.val` since `x.val < 256^width`.
  have h256 : (256 : ℕ) ^ width = 2 ^ (8 * width) := by
    rw [pow_mul]; norm_num
  have hxlt : x.val < 256 ^ width := by rw [h256]; exact hxval
  have hrecon : (Finset.range width).sum (fun j => 256 ^ j * ((x.val / 256 ^ j) % 256))
      = x.val := by
    rw [base256_digit_sum x.val width, Nat.mod_eq_of_lt hxlt]
  rw [hrecon, ZMod.natCast_val, ZMod.cast_id]

/-- The concrete field-binop realizer's `CallSpec`: at the field leaf it decodes
    the two `.TFp` arguments, applies the binop `op` in `ZMod q`, and re-encodes
    via `encodeF`; off-leaf it returns `oldDest`. -/
def fieldBinopRealizerCallSpec {q : ℕ} [NeZero q] (width : ℕ)
    (op : ZMod q → ZMod q → ZMod q) (leaf : String) : CallSpec :=
  fieldBinopCallSpec q (decodeF width) op (encodeF width) leaf

/-- The concrete field add/mul realizer `LeafSpec`. -/
def fieldBinopLeafSpec {q : ℕ} [NeZero q] (width : ℕ)
    (op : ZMod q → ZMod q → ZMod q) (leaf : String) (limbStore : LimbStoreSpec) :
    LeafSpec :=
  { call := fieldBinopRealizerCallSpec width op leaf, limbStore := limbStore }

/-- The add-specialized leaf spec. -/
def fieldAddLeafSpec (q : ℕ) [NeZero q] (width : ℕ) (leaf : String)
    (limbStore : LimbStoreSpec) : LeafSpec :=
  fieldBinopLeafSpec width ((· + ·) : ZMod q → ZMod q → ZMod q) leaf limbStore

/-- The mul-specialized leaf spec. -/
def fieldMulLeafSpec (q : ℕ) [NeZero q] (width : ℕ) (leaf : String)
    (limbStore : LimbStoreSpec) : LeafSpec :=
  fieldBinopLeafSpec width ((· * ·) : ZMod q → ZMod q → ZMod q) leaf limbStore

/-- **Unconditional field-binop kernel realization (no KAT, no abstract
    section).**  For `width ≤ 48` and `q < 2^(8·width)`, the concrete realizer
    `fieldBinopLeafSpec width op …` decodes its leaf-call value to `op` of its two
    decoded inputs for **every** input — proved by the round-trip
    `decodeF_encodeF`, not assumed. -/
theorem fieldBinop_realizes_concrete {q : ℕ} [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width))
    (op : ZMod q → ZMod q → ZMod q) (leaf : String) (limbStore : LimbStoreSpec) :
    KernelRealizes2 (decodeF width) op leaf
      (fieldBinopLeafSpec width op leaf limbStore) := by
  intro aVal bVal oldDest
  show decodeF width (fieldBinopRealizerCallSpec width op leaf leaf .TFp
      [.TFp, .TFp] oldDest [⟨.TFp, aVal⟩, ⟨.TFp, bVal⟩])
    = op (decodeF width aVal) (decodeF width bVal)
  simp only [fieldBinopRealizerCallSpec, fieldBinopCallSpec, ite_true, dite_true]
  rw [decodeF_encodeF width hw hq]

/-- **Unconditional field-ADD realization.** -/
theorem fieldAdd_realizes_concrete (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width))
    (leaf : String) (limbStore : LimbStoreSpec) :
    KernelRealizes2 (decodeF (q := q) width) ((· + ·) : ZMod q → ZMod q → ZMod q) leaf
      (fieldAddLeafSpec q width leaf limbStore) :=
  fieldBinop_realizes_concrete width hw hq (· + ·) leaf limbStore

/-- **Unconditional field-MUL realization.** -/
theorem fieldMul_realizes_concrete (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width))
    (leaf : String) (limbStore : LimbStoreSpec) :
    KernelRealizes2 (decodeF (q := q) width) ((· * ·) : ZMod q → ZMod q → ZMod q) leaf
      (fieldMulLeafSpec q width leaf limbStore) :=
  fieldBinop_realizes_concrete width hw hq (· * ·) leaf limbStore

/-- The field-add realization is also an instance of the generic
    `FieldEmitRealizes` seam (`KernelRealizes2` is defeq to it), with the encoding
    section now a *theorem*. -/
theorem fieldAdd_realizes_FieldEmit (q : ℕ) [NeZero q] (width : ℕ)
    (hw : width ≤ 48) (hq : q < 2 ^ (8 * width))
    (leaf : String) (limbStore : LimbStoreSpec) :
    FieldEmitRealizes q (decodeF (q := q) width) (· + ·) leaf
      (fieldAddLeafSpec q width leaf limbStore) :=
  fieldAdd_realizes_concrete q width hw hq leaf limbStore

end CatCrypt.Crypto.SecureCompilation.ConcreteSymFieldRealizer
