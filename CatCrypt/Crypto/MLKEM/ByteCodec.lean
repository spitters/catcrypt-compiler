/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.List.OfFn

/-!
# FIPS 203 ByteEncode / ByteDecode (general bit width)

Computable byte packing for ML-KEM, FIPS 203 §4.2.1 (Algorithms 5 and 6).
`byteEncode d` packs 256 coefficients of `ZMod m`, each carried in `d` bits,
little-endian into `32 * d` bytes; `byteDecode d m` is the inverse.

The coefficients are treated as `d`-bit little-endian digits. The packing goes
through a single natural number `N` — the little-endian value of the coefficient
digits in base `2 ^ d`, equal to the little-endian value of the output bytes in
base `256`. The round-trip `byteDecode d m (byteEncode d f) = f` holds whenever
each coefficient fits in `d` bits, i.e. `m ≤ 2 ^ d` (covering `m = 2 ^ d` for
`d < 12` and `m = 3329 ≤ 4096` for `d = 12`).

## References

* NIST FIPS 203 §4.2.1, Algorithm 5 (ByteEncode), Algorithm 6 (ByteDecode)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.ByteCodec

/-! ## Little-endian positional packing over the naturals -/

/-- Little-endian value of the digit list `xs` in base `base` (least significant
    digit first). -/
def packLE (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + base * packLE base xs

/-- Split `N` into `len` little-endian base-`base` digits (least significant
    digit first). -/
def unpackLE (base : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | (len + 1), N => (N % base) :: unpackLE base len (N / base)

/-- `unpackLE` always produces exactly `len` digits. -/
theorem length_unpackLE (base len N : ℕ) : (unpackLE base len N).length = len := by
  induction len generalizing N with
  | zero => rfl
  | succ len ih => simp [unpackLE, ih]

/-- Every digit produced by `unpackLE` is below the base. -/
theorem unpackLE_lt (base : ℕ) (hb : 0 < base) (len N : ℕ) :
    ∀ x ∈ unpackLE base len N, x < base := by
  induction len generalizing N with
  | zero => simp [unpackLE]
  | succ len ih =>
    intro x hx
    rw [unpackLE, List.mem_cons] at hx
    rcases hx with h | h
    · subst h; exact Nat.mod_lt _ hb
    · exact ih (N / base) x h

/-- A packed value is bounded by the base raised to the number of digits. -/
theorem packLE_lt (base : ℕ) (hb : 0 < base) :
    ∀ (xs : List ℕ), (∀ x ∈ xs, x < base) → packLE base xs < base ^ xs.length := by
  intro xs
  induction xs with
  | nil => intro _; simp only [packLE, List.length_nil, pow_zero]; omega
  | cons x xs ih =>
    intro h
    have hx : x < base := h x (List.mem_cons_self)
    have hxs : ∀ y ∈ xs, y < base := fun y hy => h y (List.mem_cons_of_mem x hy)
    have hP : packLE base xs < base ^ xs.length := ih hxs
    have hmul : base * Nat.succ (packLE base xs) ≤ base * base ^ xs.length :=
      Nat.mul_le_mul (le_refl base) (Nat.succ_le_of_lt hP)
    have hstep : base * packLE base xs + base ≤ base * base ^ xs.length := by
      rw [Nat.mul_succ] at hmul; exact hmul
    simp only [packLE, List.length_cons, pow_succ']
    omega

/-- `packLE` inverts `unpackLE` up to reduction modulo `base ^ len`. -/
theorem packLE_unpackLE (base len N : ℕ) :
    packLE base (unpackLE base len N) = N % base ^ len := by
  induction len generalizing N with
  | zero => simp [unpackLE, packLE, pow_zero, Nat.mod_one]
  | succ len ih =>
    simp only [unpackLE, packLE]
    rw [ih (N / base), pow_succ', Nat.mod_mul]

/-- `unpackLE` inverts `packLE` on digit lists that fit in the base. -/
theorem unpackLE_packLE (base : ℕ) (hb : 0 < base) :
    ∀ (xs : List ℕ), (∀ x ∈ xs, x < base) →
      unpackLE base xs.length (packLE base xs) = xs := by
  intro xs
  induction xs with
  | nil => simp [unpackLE, packLE]
  | cons x xs ih =>
    intro h
    have hx : x < base := h x (List.mem_cons_self)
    have hxs : ∀ y ∈ xs, y < base := fun y hy => h y (List.mem_cons_of_mem x hy)
    have hhead : (x + base * packLE base xs) % base = x := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]
    have htail : (x + base * packLE base xs) / base = packLE base xs := by
      rw [Nat.add_comm, Nat.mul_add_div hb, Nat.div_eq_of_lt hx, Nat.add_zero]
    simp only [List.length_cons, packLE, unpackLE]
    rw [hhead, htail, ih hxs]

/-! ## Byte-level helpers -/

/-- Reading back a byte built from a value below `256` returns that value. -/
theorem toNat_ofNat_lt {x : ℕ} (h : x < 256) : (UInt8.ofNat x).toNat = x := by
  rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- Reading the `i`-th entry of `List.ofFn g` returns `g i`. -/
theorem getD_ofFn_val {n : ℕ} (g : Fin n → ℕ) (i : Fin n) :
    (List.ofFn g).getD i.val 0 = g i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt]

/-! ## ByteEncode and ByteDecode -/

/-- FIPS 203 Algorithm 5: pack 256 coefficients of `ZMod m`, each as a `d`-bit
    little-endian digit, into `32 * d` bytes (LSB first). -/
def byteEncode (d : ℕ) {m : ℕ} (f : Fin 256 → ZMod m) : List UInt8 :=
  (unpackLE 256 (32 * d)
      (packLE (2 ^ d) (List.ofFn (fun j => (f j).val)))).map (fun n => UInt8.ofNat n)

/-- FIPS 203 Algorithm 6: unpack `32 * d` bytes into 256 coefficients of
    `ZMod m`, reading `d`-bit little-endian digits. -/
def byteDecode (d m : ℕ) (bs : List UInt8) : Fin 256 → ZMod m :=
  fun i =>
    ((unpackLE (2 ^ d) 256 (packLE 256 (bs.map (fun b => b.toNat)))).getD i.val 0 : ZMod m)

/-- The encoding is lossless: decoding an encoded coefficient vector recovers it,
    provided every coefficient fits in `d` bits (`m ≤ 2 ^ d`). -/
theorem byteDecode_byteEncode (d m : ℕ) [NeZero m] (hm : m ≤ 2 ^ d)
    (f : Fin 256 → ZMod m) :
    byteDecode d m (byteEncode d f) = f := by
  have h2d : 0 < 2 ^ d := Nat.two_pow_pos d
  have hlt : ∀ j : Fin 256, (f j).val < 2 ^ d := fun j =>
    lt_of_lt_of_le (ZMod.val_lt (f j)) hm
  have hmem : ∀ x ∈ List.ofFn (fun j => (f j).val), x < 2 ^ d := by
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    exact hlt j
  have hlen : (List.ofFn (fun j => (f j).val)).length = 256 := by
    rw [List.length_ofFn]
  have hpow : (2 ^ d) ^ 256 = 256 ^ (32 * d) := by
    have e1 : (2 ^ d) ^ 256 = 2 ^ (d * 256) := (pow_mul 2 d 256).symm
    have e2 : (256 : ℕ) ^ (32 * d) = 2 ^ (8 * (32 * d)) := by
      rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_mul]
    have e3 : d * 256 = 8 * (32 * d) := by omega
    rw [e1, e2, e3]
  funext i
  simp only [byteDecode, byteEncode]
  set N0 := packLE (2 ^ d) (List.ofFn (fun j => (f j).val)) with hN0def
  have hN0lt : N0 < 256 ^ (32 * d) := by
    rw [hN0def]
    have h := packLE_lt (2 ^ d) h2d (List.ofFn (fun j => (f j).val)) hmem
    rw [hlen, hpow] at h
    exact h
  have hbytes : ((unpackLE 256 (32 * d) N0).map (fun n => UInt8.ofNat n)).map
      (fun b => b.toNat) = unpackLE 256 (32 * d) N0 := by
    rw [List.map_map]
    have hcong : (unpackLE 256 (32 * d) N0).map
          ((fun b : UInt8 => b.toNat) ∘ fun n => UInt8.ofNat n)
        = (unpackLE 256 (32 * d) N0).map id := by
      apply List.map_congr_left
      intro x hx
      simp only [Function.comp_apply, id_eq]
      exact toNat_ofNat_lt (unpackLE_lt 256 (by omega) (32 * d) N0 x hx)
    rw [hcong, List.map_id]
  have hrecover : packLE 256 (unpackLE 256 (32 * d) N0) = N0 := by
    rw [packLE_unpackLE, Nat.mod_eq_of_lt hN0lt]
  have hcoeff : unpackLE (2 ^ d) 256 N0 = List.ofFn (fun j => (f j).val) := by
    have h := unpackLE_packLE (2 ^ d) h2d (List.ofFn (fun j => (f j).val)) hmem
    rw [hlen] at h
    rw [hN0def]
    exact h
  rw [hbytes, hrecover, hcoeff, getD_ofFn_val (fun j => (f j).val) i]
  exact ZMod.natCast_zmod_val (f i)

end CatCrypt.Crypto.MLKEM.ByteCodec
