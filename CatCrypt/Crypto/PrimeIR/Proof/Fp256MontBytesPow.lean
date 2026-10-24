/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.PrimeIR.Proof.Fp256Mont
public import CatCrypt.Hax.BitScan

/-!
# Byte conversion and exponentiation of the Montgomery P-256 field of `primeir-hax`

Specifications of the methods `pow`, `from_bytes` and `to_bytes` of the `Field` instance
of `Fp256Mont` in the extraction, on canonical limbs valued by `montVal`. Each loop of
the extraction is rewritten as a fold (`Hax.foldRange` for a counting loop, `downFold`
for a descending one) and the value is obtained from an invariant of the fold.

## Main definitions

* `powTable`, `powStep`, `powDigit` — the table of sixteen powers, one window step and
  the four-bit window of `Field::pow`.
* `leWord`, `fbBuf`, `fbStep` — a word of `bytes_le_to_limbs`, the 32-byte buffer of a
  chunk and one chunk step of `Field::from_bytes`.
* `wordNat`, `chunkNat` — the little-endian numbers of 8 and of 32 base-256 digits.

## Main results

* `Field_pow_val` — on canonical limbs `a` and an exponent `e` of 64-bit limbs,
  `Field_pow a e` is canonical with value `montVal a ^ leValue 64 e`: the power to the
  number the limbs encode, least significant limb first.
* `Field_from_bytes_val` — on a byte array of any length, `Field_from_bytes` is
  canonical with value the little-endian number of the bytes, cast to the field.
* `Field_to_bytes_val` — on canonical limbs, `Field_to_bytes` returns 32 bytes whose
  little-endian number is the canonical representative `(montVal a).val`.
* `canon_ext` — canonical limbs are determined by their Montgomery value.
* `fp256MontCtModel_powLaws`, `fp256MontCtModel_byteLaws` — the field model
  `fp256MontCtModel` satisfies `FieldModel.PowLaws` and `FieldModel.ByteLaws` at
  32 bytes; `FieldModel.ByteLaws.from_bytes_to_bytes` then gives the round trip.

`Field_pow`, `Field_from_bytes` and `Field_to_bytes` are the extracted methods of the
`Field` implementation of `Fp256Mont`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PrimeIR.Fp256Mont

open Primeir
open CatCrypt.Util (P256 Fp256)

/-! ## `to_bytes` -/

/-- Byte `j` of a word, as `limbs_to_bytes_le` computes it. -/
def byteAt (r j : Int) : Int := Hax.castVal_w 8 (Hax.shr_w 64 r (Hax.mul 8 j))

/-- `Hax.array_update` is `List.set` on the entries. -/
theorem array_update_eq_set {α : Type} (a : Array α) (i : Int) (v : α) :
    Hax.array_update a i v = (a.toList.set i.toNat v).toArray := by
  unfold Hax.array_update
  dsimp only
  split
  · rfl
  · rw [List.set_eq_of_length_le (by rw [Array.length_toList]; omega)]

/-- Thirty-two successive updates of the zero array of length 32 give the array of the
    written values. -/
theorem upd32 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20
    v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 : Int) :
    Hax.array_update (Hax.array_update (Hax.array_update (Hax.array_update
    (Hax.array_update (Hax.array_update (Hax.array_update (Hax.array_update
    (Hax.array_update (Hax.array_update (Hax.array_update (Hax.array_update
    (Hax.array_update (Hax.array_update (Hax.array_update (Hax.array_update
    (Hax.array_update (Hax.array_update (Hax.array_update (Hax.array_update
    (Hax.array_update (Hax.array_update (Hax.array_update (Hax.array_update
    (Hax.array_update (Hax.array_update (Hax.array_update (Hax.array_update
    (Hax.array_update (Hax.array_update (Hax.array_update (Hax.array_update
      (Hax.repeat_ (0 : Int) 32) 0 v0) 1 v1) 2 v2) 3 v3) 4 v4) 5 v5) 6 v6) 7 v7) 8 v8) 9 v9)
      10 v10) 11 v11) 12 v12) 13 v13) 14 v14) 15 v15) 16 v16) 17 v17) 18 v18) 19 v19)
      20 v20) 21 v21) 22 v22) 23 v23) 24 v24) 25 v25) 26 v26) 27 v27) 28 v28) 29 v29)
      30 v30) 31 v31
      = #[v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17,
        v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31] := by
  simp [array_update_eq_set, Hax.repeat_, List.replicate]

/-- `limbs_to_bytes_le` on four limbs is the array of their 32 bytes. -/
theorem limbs_to_bytes_le_eq (r0 r1 r2 r3 : Int) :
    limbs_to_bytes_le #[r0, r1, r2, r3] =
      #[byteAt r0 0, byteAt r0 1, byteAt r0 2, byteAt r0 3, byteAt r0 4, byteAt r0 5,
        byteAt r0 6, byteAt r0 7, byteAt r1 0, byteAt r1 1, byteAt r1 2, byteAt r1 3,
        byteAt r1 4, byteAt r1 5, byteAt r1 6, byteAt r1 7, byteAt r2 0, byteAt r2 1,
        byteAt r2 2, byteAt r2 3, byteAt r2 4, byteAt r2 5, byteAt r2 6, byteAt r2 7,
        byteAt r3 0, byteAt r3 1, byteAt r3 2, byteAt r3 3, byteAt r3 4, byteAt r3 5,
        byteAt r3 6, byteAt r3 7] := by
  unfold limbs_to_bytes_le
  dsimp only
  have inner : ∀ (out : Array Int) (i : Int),
      Hax.whileFold (out, (0 : Int)) (fun _ => true) (fun (x : Array Int × Int) =>
        if Hax.lt x.2 (8 : Int) then
          Hax.cfContinue (Hax.array_update x.1 (Hax.add (Hax.mul (8 : Int) i) x.2)
            (Hax.castVal_w 8 (Hax.shr_w 64 (Hax.index #[r0, r1, r2, r3] i)
              (Hax.mul (8 : Int) x.2))), Hax.add x.2 (1 : Int))
        else Hax.cfBreak (x.1, x.2))
        = ControlFlow.Break (Hax.foldRange 0 8 out (fun j out =>
            Hax.array_update out (Hax.add (Hax.mul (8 : Int) i) j)
              (Hax.castVal_w 8 (Hax.shr_w 64 (Hax.index #[r0, r1, r2, r3] i)
                (Hax.mul (8 : Int) j)))), 8) := fun out i =>
    whileFold_count_gen (fun (s : Array Int) (j : Int) => (s, j)) 8 _ _
      (fun s j => rfl) 8 0 out (by norm_num)
  rw [whileFold_count_gen (fun (s : Array Int) (j : Int) => (s, j)) 4
    (fun i out => Hax.foldRange 0 8 out (fun j out =>
            Hax.array_update out (Hax.add (Hax.mul (8 : Int) i) j)
              (Hax.castVal_w 8 (Hax.shr_w 64 (Hax.index #[r0, r1, r2, r3] i)
                (Hax.mul (8 : Int) j))))) _
    (fun s j => by
      dsimp only
      rw [inner]
      rfl) 4 0 _ (by norm_num)]
  dsimp only [ControlFlow.merge]
  rw [foldRange_four]
  simp only [fr08]
  exact upd32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Byte `j` of a 64-bit word is the word divided by `2 ^ (8 j)`, modulo `256`. -/
theorem byteAt_eq {r : Int} (hr : W64 r) (j : ℕ) : byteAt r j = r / 2 ^ (8 * j) % 256 := by
  have h0 : (0 : Int) ≤ r / 2 ^ (8 * j) := Int.ediv_nonneg hr.1 (by positivity)
  have hs : Hax.shr_w 64 r (Hax.mul 8 (j : Int)) = r / 2 ^ (8 * j) := by
    rw [show Hax.mul 8 (j : Int) = ((8 * j : ℕ) : Int) by simp [Hax.mul]]
    exact shr_of_lt (w := 64) (8 * j) hr.1 hr.2
  rw [byteAt, hs, castVal_mod h0]
  norm_num

/-- `byteAt` is a byte. -/
theorem byteAt_isByte (r j : Int) : 0 ≤ byteAt r j ∧ byteAt r j < 2 ^ 8 := by
  have h : (0 : ℕ) < 2 ^ 8 := by norm_num
  have := Nat.mod_lt (Hax.shr_w 64 r (Hax.mul 8 j)).toNat h
  simp only [byteAt, Hax.castVal_w, Hax.mod2w]
  omega

/-- The eight bytes of a 64-bit word are its little-endian digits in base `256`. -/
theorem word_bytes {r : Int} (hr : W64 r) (acc : ℕ) :
    (byteAt r 0).toNat + 2 ^ 8 * ((byteAt r 1).toNat + 2 ^ 8 * ((byteAt r 2).toNat +
      2 ^ 8 * ((byteAt r 3).toNat + 2 ^ 8 * ((byteAt r 4).toNat + 2 ^ 8 * ((byteAt r 5).toNat +
      2 ^ 8 * ((byteAt r 6).toNat + 2 ^ 8 * ((byteAt r 7).toNat + 2 ^ 8 * acc)))))))
      = r.toNat + 2 ^ 64 * acc := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr.1
  have hn : n < 2 ^ 64 := by have := hr.2; omega
  have hb : ∀ j : ℕ, (byteAt (n : Int) (j : Int)).toNat = n / 256 ^ j % 256 := by
    intro j
    rw [byteAt_eq hr j, show ((n : Int) / 2 ^ (8 * j) % 256) = ((n / 256 ^ j % 256 : ℕ) : Int) by
      push_cast; rw [pow_mul]; norm_num, Int.toNat_natCast]
  have e0 := hb 0
  have e1 := hb 1
  have e2 := hb 2
  have e3 := hb 3
  have e4 := hb 4
  have e5 := hb 5
  have e6 := hb 6
  have e7 := hb 7
  simp only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at e0 e1 e2 e3 e4 e5 e6 e7
  rw [e0, e1, e2, e3, e4, e5, e6, e7, Int.toNat_natCast]
  have hd : ∀ j : ℕ, n / 256 ^ (j + 1) = n / 256 ^ j / 256 := fun j => by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  have d1 := hd 0
  have d2 := hd 1
  have d3 := hd 2
  have d4 := hd 3
  have d5 := hd 4
  have d6 := hd 5
  have d7 := hd 6
  have d8 := hd 7
  have h8 : n / 256 ^ (7 + 1) = 0 := Nat.div_eq_of_lt (by norm_num; omega)
  simp only [Nat.reduceAdd, pow_zero, pow_one, Nat.div_one] at d2 d3 d4 d5 d6 d7 d8 h8 ⊢
  clear d1 hb hd e0 e1 e2 e3 e4 e5 e6 e7 hr
  generalize n / 256 ^ 2 = q2 at *
  generalize n / 256 ^ 3 = q3 at *
  generalize n / 256 ^ 4 = q4 at *
  generalize n / 256 ^ 5 = q5 at *
  generalize n / 256 ^ 6 = q6 at *
  generalize n / 256 ^ 7 = q7 at *
  generalize n / 256 ^ 8 = q8 at *
  have m0 := Nat.mod_add_div n 256
  have m1 := Nat.mod_add_div (n / 256) 256
  have m2 := Nat.mod_add_div q2 256
  have m3 := Nat.mod_add_div q3 256
  have m4 := Nat.mod_add_div q4 256
  have m5 := Nat.mod_add_div q5 256
  have m6 := Nat.mod_add_div q6 256
  have m7 := Nat.mod_add_div q7 256
  rw [← d2] at m1
  rw [← d3] at m2
  rw [← d4] at m3
  rw [← d5] at m4
  rw [← d6] at m5
  rw [← d7] at m6
  rw [← d8, h8] at m7
  norm_num
  linarith

/-! ## `pow`: the loops -/

open CatCrypt.Hax.BitScan (downFold whileFold_countdown whileFold_countdown_int)

/-- The four-bit window `s` of an exponent limb, as `Field::pow` computes it. -/
def powDigit (limb s : Int) : Int :=
  Hax.castVal_w Hax.usizeBits
    (Hax.bitand_w 64 (Hax.shr_w 64 limb (Hax.mul (4 : Int) s)) (15 : Int))

/-- One window step of `Field::pow` on the accumulator and the flag that records whether
    a nonzero window has been read. -/
def powStep (table : Array (Array Int)) (limb s : Int) (st : Array Int × Bool) :
    Array Int × Bool :=
  if Hax.bne st.2 0 then
    if Hax.bne (powDigit limb s) (0 : Int) then
      (mont_mul_limbs (sqr_n st.1 (4 : Int)) (Hax.index table (powDigit limb s)), st.2)
    else (sqr_n st.1 (4 : Int), st.2)
  else if Hax.bne (powDigit limb s) (0 : Int) then (Hax.index table (powDigit limb s), true)
  else st

/-- The window table of `Field::pow`: sixteen entries, filled from index `2` by
    multiplying the previous entry by `a`. -/
def powTable (a : Array Int) : Array (Array Int) :=
  Hax.foldRange 2 16
    (Hax.array_update (Hax.array_update
      (Hax.repeat_ (Hax.repeat_ (0 : Int) (4 : Int)) (16 : Int)) (0 : Int) R_LIMBS) (1 : Int) a)
    (fun i table =>
      Hax.array_update table i (mont_mul_limbs (Hax.index table (Hax.sub i (1 : Int))) a))

/-- `Field::pow` of `Fp256Mont` as two nested descending folds of `powStep`: over the
    limbs of the exponent from the last, and over the sixteen windows of a limb from
    the top. -/
theorem Field_pow_eq (a e : Array Int) :
    Field_pow a e = (downFold (fun k st => downFold (fun s st =>
      powStep (powTable a) (Hax.index e (k : Int)) (s : Int) st) 16 st) e.size
        (R_LIMBS, false)).1 := by
  unfold Field_pow
  dsimp only
  rw [whileFold_count_gen (fun (s : Array (Array Int)) (j : Int) => (s, j)) 16
    (fun i table =>
      Hax.array_update table i (mont_mul_limbs (Hax.index table (Hax.sub i (1 : Int))) a))
    _ (fun s j => rfl) 14 2 _ (by norm_num)]
  dsimp only [ControlFlow.merge]
  rw [show Hax.array_len e = ((e.size : ℕ) : Int) from rfl]
  rw [whileFold_countdown (fun k st => downFold (fun s st =>
      powStep (powTable a) (Hax.index e k) (s : Int) st) 16 st) _ ?_ e.size _]
  · rfl
  · intro k st
    obtain ⟨acc, started⟩ := st
    dsimp only
    rw [show (16 : Int) = ((16 : ℕ) : Int) from rfl,
      whileFold_countdown (fun s st =>
        powStep (powTable a) (Hax.index e (Hax.sub k 1)) s st) _ ?_ 16 (acc, started)]
    intro s st
    obtain ⟨acc, started⟩ := st
    unfold powStep powDigit
    dsimp only
    split_ifs <;> rfl

/-! ## `from_bytes`: the loops -/

/-- Word `i` of `bytes_le_to_limbs`: the bytes `8 i + 7, …, 8 i` shifted in from the
    top. -/
def leWord (b : Array Int) (i : Int) : Int :=
  downFold (fun j acc => Hax.bitor_w 64 (Hax.shl_w 64 acc (8 : Int))
    (Hax.castVal_w 64 (Hax.index b (Hax.add (Hax.mul (8 : Int) i) (j : Int))))) 8 0

/-- `bytes_le_to_limbs` is the array of its four words. -/
theorem bytes_le_to_limbs_eq (b : Array Int) :
    bytes_le_to_limbs b = #[leWord b 0, leWord b 1, leWord b 2, leWord b 3] := by
  unfold bytes_le_to_limbs
  dsimp only
  rw [whileFold_count_gen (fun (s : Array Int) (j : Int) => (s, j)) 4
    (fun i v => Hax.array_update v i (leWord b i)) _ ?_ 4 0 _ (by norm_num)]
  · dsimp only [ControlFlow.merge]
    rw [foldRange_four]
    rfl
  · intro v i
    dsimp only
    rw [show (8 : Int) = ((8 : ℕ) : Int) from rfl,
      whileFold_countdown (fun j acc => Hax.bitor_w 64 (Hax.shl_w 64 acc (8 : Int))
        (Hax.castVal_w 64 (Hax.index b (Hax.add (Hax.mul (8 : Int) i) j)))) _ ?_ 8 0]
    · rfl
    · intro j acc
      rfl

/-- The 32-byte buffer of chunk `k` in `Field::from_bytes`: the bytes at
    `32 k, …, 32 k + 31` that lie inside the input, the others zero. -/
def fbBuf (bytes : Array Int) (k : Int) : Array Int :=
  Hax.foldRange (Hax.mul (32 : Int) k)
    (if Hax.gt (Hax.add (Hax.mul (32 : Int) k) (32 : Int)) (Hax.array_len bytes)
      then Hax.array_len bytes else Hax.add (Hax.mul (32 : Int) k) (32 : Int))
    (Hax.repeat_ (0 : Int) (32 : Int))
    (fun i buf => Hax.array_update buf (Hax.sub i (Hax.mul (32 : Int) k)) (Hax.index bytes i))

/-- One chunk step of `Field::from_bytes`: the accumulator times `2 ^ 256`, plus the
    chunk. -/
noncomputable def fbStep (bytes : Array Int) (k : Int) (acc : Array Int) : Array Int :=
  Field_add (Field_mul acc R2_LIMBS) (Fp256Mont_from_canonical_bytes (fbBuf bytes k))

/-- `Field::from_bytes` of `Fp256Mont` as a descending fold of `fbStep` over the
    32-byte chunks of the input. -/
theorem Field_from_bytes_eq (bytes : Array Int) :
    Field_from_bytes bytes
      = downFold (fun k acc => fbStep bytes (k : Int) acc) ((bytes.size + 31) / 32)
          #[0, 0, 0, 0] := by
  have hcopy : ∀ (st en : Int), Hax.whileFold (Hax.repeat_ (0 : Int) (32 : Int), st)
      (fun _ => true) (fun x : Array Int × Int =>
        if Hax.lt x.2 en then
          Hax.cfContinue (Hax.array_update x.1 (Hax.sub x.2 st) (Hax.index bytes x.2),
            Hax.add x.2 (1 : Int))
        else Hax.cfBreak (x.1, x.2))
      = ControlFlow.Break (Hax.foldRange st en (Hax.repeat_ (0 : Int) (32 : Int))
          (fun i buf => Hax.array_update buf (Hax.sub i st) (Hax.index bytes i)),
          if st ≤ en then en else st) := by
    intro st en
    by_cases h : st ≤ en
    · rw [ite_eq_left h]
      exact whileFold_count_gen (fun (s : Array Int) (j : Int) => (s, j)) en _ _
        (fun s j => rfl) (en - st).toNat st _ (by omega)
    · rw [ite_eq_right h, Hax.foldRange_stop _ _ _ _ (by omega)]
      exact Hax.whileFold_eq_of_fuel (n := 1)
        (by simp [Hax.whileFoldFuel, Hax.lt, Hax.cfBreak, show ¬ st < en by omega])
  unfold Field_from_bytes
  dsimp only
  rw [show Hax.div (Hax.add (Hax.array_len bytes) (31 : Int)) (32 : Int)
      = (((bytes.size + 31) / 32 : ℕ) : Int) by
    simp [Hax.div, Hax.add, Hax.array_len],
    whileFold_countdown (fun k acc => fbStep bytes k acc) _ ?_ ((bytes.size + 31) / 32) _]
  · rfl
  · intro k acc
    dsimp only
    rw [hcopy]
    rfl

variable [PrimeirDeps]

/-- `Field::to_bytes` of `Fp256Mont` on canonical limbs: 32 bytes, the little-endian
    digits of the canonical representative of the Montgomery value. -/
theorem Field_to_bytes_val {a : Array Int} (ha : Canon a) :
    (Field_to_bytes a).size = 32 ∧ IsDigits 8 (Field_to_bytes a) ∧
      leValue 8 (Field_to_bytes a) = (montVal a).val := by
  obtain ⟨r0, r1, r2, r3, he, h0, h1, h2, h3, hlt, hv⟩ := to_canonical_limbs_val ha
  have hE : Field_to_bytes a = limbs_to_bytes_le #[r0, r1, r2, r3] := by
    rw [← he]; rfl
  rw [hE, limbs_to_bytes_le_eq]
  refine ⟨rfl, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> exact byteAt_isByte _ _
  · have hn := val4_nonneg h0 h1 h2 h3
    have hval : (montVal a).val = (val4 r0 r1 r2 r3).toNat := by
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hn
      rw [← hv, hm, Int.cast_natCast, ZMod.val_natCast_of_lt, Int.toNat_natCast]
      have := pZ_eq; omega
    rw [hval]
    simp only [leValue, List.foldr_cons, List.foldr_nil]
    rw [word_bytes h3 0, word_bytes h2, word_bytes h1, word_bytes h0]
    unfold val4 W64 at *
    omega

/-! ## `pow`: the value -/

/-- Entry `d` of the window table is canonical and has the value `x ^ d`. -/
theorem powTable_val {a : Array Int} (ha : Canon a) {d : Int} (hd0 : 0 ≤ d) (hd : d < 16) :
    Canon (Hax.index (powTable a) d) ∧
      montVal (Hax.index (powTable a) d) = montVal a ^ d.toNat := by
  have key := Hax.foldRange_induct (P := fun (i : Int) (t : Array (Array Int)) =>
      t.size = 16 ∧ ∀ d : Int, 0 ≤ d → d < i →
        Canon (Hax.index t d) ∧ montVal (Hax.index t d) = montVal a ^ d.toNat)
    (lo := 2) (hi := 16)
    (f := fun i table =>
      Hax.array_update table i (mont_mul_limbs (Hax.index table (Hax.sub i (1 : Int))) a))
    (init := Hax.array_update (Hax.array_update
      (Hax.repeat_ (Hax.repeat_ (0 : Int) (4 : Int)) (16 : Int)) (0 : Int) R_LIMBS) (1 : Int) a)
    (by norm_num) ?_ ?_
  · exact key.2 d hd0 hd
  · have hsz : (Hax.array_update (Hax.repeat_ (Hax.repeat_ (0 : Int) (4 : Int)) (16 : Int))
        (0 : Int) R_LIMBS).size = 16 := by
      rw [Hax.size_array_update_eq, Hax.size_repeat_]; rfl
    refine ⟨by rw [Hax.size_array_update_eq, hsz], ?_⟩
    intro d h0 h2
    have hd : d = 0 ∨ d = 1 := by omega
    rcases hd with rfl | rfl
    · rw [Hax.index_array_update_of_ne _ (by rw [hsz]; decide) (by decide),
        Hax.index_array_update_same _ (by rw [Hax.size_repeat_]; decide)]
      exact ⟨canon_R, by rw [montVal_R]; simp⟩
    · rw [Hax.index_array_update_same _ (by rw [hsz]; decide)]
      exact ⟨ha, by simp⟩
  · intro i t hi2 hi16 ⟨hs, ih⟩
    refine ⟨by rw [Hax.size_array_update_eq, hs], ?_⟩
    intro d h0 hlt
    by_cases hdi : d = i
    · subst hdi
      rw [Hax.index_array_update_same _ (by rw [hs]; omega)]
      obtain ⟨hc, hv⟩ := ih (Hax.sub d 1) (by simp only [Hax.sub]; omega)
        (by simp only [Hax.sub]; omega)
      obtain ⟨hc', hv'⟩ := mont_mul_limbs_val hc ha
      refine ⟨hc', ?_⟩
      rw [hv', hv, ← pow_succ]
      congr 1
      simp only [Hax.sub]
      omega
    · rw [Hax.index_array_update_of_ne _ (by rw [hs]; omega) (by omega)]
      exact ih d h0 (by omega)

omit [PrimeirDeps] in
/-- The window `s` of a 64-bit limb is its base-16 digit `s`. -/
theorem powDigit_eq {limb : Int} (hl : W64 limb) (s : ℕ) :
    powDigit limb s = ((limb.toNat / 16 ^ s % 16 : ℕ) : Int) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hl.1
  have hn : n < 2 ^ 64 := by have := hl.2; omega
  have hs' : Hax.shr_w 64 (n : Int) (Hax.mul 4 (s : Int)) = ((n / 16 ^ s : ℕ) : Int) := by
    rw [show Hax.mul 4 (s : Int) = ((4 * s : ℕ) : Int) by simp [Hax.mul],
      shr_of_lt (w := 64) (4 * s) hl.1 hl.2, pow_mul]
    norm_num
  have hlt : n / 16 ^ s < 2 ^ 64 := lt_of_le_of_lt (Nat.div_le_self _ _) hn
  have hand : Hax.bitand_w 64 ((n / 16 ^ s : ℕ) : Int) 15 = ((n / 16 ^ s % 16 : ℕ) : Int) := by
    simp only [Hax.bitand_w, Int.toNat_natCast, Nat.mod_eq_of_lt hlt]
    rw [show ((15 : Int).toNat % 2 ^ 64) = 2 ^ 4 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  rw [powDigit, hs', hand, Int.toNat_natCast]
  apply castVal_of_lt (by positivity)
  have h16 : n / 16 ^ s % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hb := System.Platform.numBits_eq
  unfold Hax.usizeBits
  rcases hb with hb | hb <;> rw [hb] <;> omega

/-- The invariant of `Field::pow`: the accumulator is canonical with value `x ^ E`, and
    `E = 0` while no nonzero window has been read. -/
@[reducible] def PowInv (x : Fp256) (st : Array Int × Bool) (E : ℕ) : Prop :=
  Canon st.1 ∧ montVal st.1 = x ^ E ∧ (st.2 = false → E = 0)

/-- One window step multiplies the exponent by `16` and adds the window. -/
theorem powStep_inv {a : Array Int} (ha : Canon a) {limb : Int} (hl : W64 limb) (s : ℕ)
    {st : Array Int × Bool} {E : ℕ} (h : PowInv (montVal a) st E) :
    PowInv (montVal a) (powStep (powTable a) limb s st)
      (16 * E + limb.toNat / 16 ^ s % 16) := by
  obtain ⟨acc, started⟩ := st
  obtain ⟨hc, hv, hE⟩ := h
  have hd := powDigit_eq hl s
  generalize limb.toNat / 16 ^ s % 16 = d at hd ⊢
  have hd16 : d < 16 := by
    have := powDigit_eq hl s
    rw [hd] at this
    have h16 : limb.toNat / 16 ^ s % 16 < 16 := Nat.mod_lt _ (by norm_num)
    omega
  obtain ⟨tc, tv⟩ := powTable_val ha (d := (d : Int)) (by positivity) (by omega)
  rw [Int.toNat_natCast] at tv
  have hne : Hax.bne (d : Int) (0 : Int) = decide (d ≠ 0) := by
    rw [Hax.bne_def_decide]; simp
  unfold powStep
  rw [hd, hne]
  cases started
  · have hE0 : E = 0 := hE rfl
    subst hE0
    rw [ite_eq_right (by decide : ¬ (Hax.bne false 0 = true))]
    by_cases hd0 : d = 0
    · rw [ite_eq_right (by simp [hd0])]
      exact ⟨hc, by rw [hv, hd0], fun _ => by omega⟩
    · rw [ite_eq_left (by simp [hd0])]
      exact ⟨tc, by rw [tv]; congr 1; omega, fun h => absurd (show true = false from h) (by decide)⟩
  · rw [ite_eq_left (by decide : Hax.bne true 0 = true)]
    obtain ⟨sc, sv⟩ := sqr_n_val hc 4
    simp only [Nat.cast_ofNat] at sc sv
    by_cases hd0 : d = 0
    · rw [ite_eq_right (by simp [hd0])]
      refine ⟨sc, ?_, fun h => absurd (show true = false from h) (by decide)⟩
      rw [sv, hv, ← pow_mul, hd0]
      congr 1
      omega
    · rw [ite_eq_left (by simp [hd0])]
      obtain ⟨mc, mv⟩ := mont_mul_limbs_val sc tc
      refine ⟨mc, ?_, fun h => absurd (show true = false from h) (by decide)⟩
      rw [mv, sv, tv, hv, ← pow_mul, ← pow_add]
      congr 1
      omega

/-- The windows `m - 1, …, 0` of a limb shift the exponent by `16 ^ m` and add the limb
    modulo `16 ^ m`. -/
theorem powLimb_inv {a : Array Int} (ha : Canon a) {limb : Int} (hl : W64 limb) (m : ℕ)
    {st : Array Int × Bool} {E : ℕ} (h : PowInv (montVal a) st E) :
    PowInv (montVal a)
      (downFold (fun s st => powStep (powTable a) limb (s : Int) st) m st)
      (E * 16 ^ m + limb.toNat % 16 ^ m) := by
  induction m generalizing st E with
  | zero => simpa [downFold, Nat.mod_one] using h
  | succ m ih =>
    rw [downFold]
    have h2 := ih (powStep_inv ha hl m h)
    have he : (16 * E + limb.toNat / 16 ^ m % 16) * 16 ^ m + limb.toNat % 16 ^ m
        = E * 16 ^ (m + 1) + limb.toNat % 16 ^ (m + 1) := by
      rw [Nat.mod_pow_succ]; ring
    rw [he] at h2
    exact h2

omit [PrimeirDeps] in
/-- The little-endian value of the first `m + 1` digits adds digit `m` at weight
    `(2 ^ w) ^ m`. -/
theorem foldr_take_succ (w : ℕ) (l : List Int) (m : ℕ) (hm : m < l.length) :
    (l.take (m + 1)).foldr (fun x acc => x.toNat + 2 ^ w * acc) 0
      = (l.take m).foldr (fun x acc => x.toNat + 2 ^ w * acc) 0 + (2 ^ w) ^ m * l[m].toNat := by
  induction l generalizing m with
  | nil => simp at hm
  | cons x l ih =>
    cases m with
    | zero => simp
    | succ m =>
      have hm' : m < l.length := by simpa using hm
      simp only [List.take_succ_cons, List.foldr_cons, List.getElem_cons_succ]
      rw [ih m hm']
      ring

/-- The limbs `m - 1, …, 0` of the exponent shift the exponent by `(2 ^ 64) ^ m` and add
    the little-endian value of the first `m` limbs. -/
theorem powLimbs_inv {a : Array Int} (ha : Canon a) {e : Array Int} (he : IsDigits 64 e)
    (m : ℕ) (hm : m ≤ e.size) {st : Array Int × Bool} {E : ℕ}
    (h : PowInv (montVal a) st E) :
    PowInv (montVal a)
      (downFold (fun k st => downFold (fun s st =>
        powStep (powTable a) (Hax.index e (k : Int)) (s : Int) st) 16 st) m st)
      (E * (2 ^ 64) ^ m
        + (e.toList.take m).foldr (fun x acc => x.toNat + 2 ^ 64 * acc) 0) := by
  induction m generalizing st E with
  | zero => simpa [downFold] using h
  | succ m ih =>
    rw [downFold]
    have hidx : Hax.index e (m : Int) = e.toList[m]'(by simpa using hm) := by
      rw [Hax.index_eq_getElem (by simpa using hm)]
      simp
    have hl : W64 (Hax.index e (m : Int)) := by
      rw [hidx]; exact he _ (List.getElem_mem _)
    have h1 := powLimb_inv ha hl 16 h
    have hlt : (Hax.index e (m : Int)).toNat < 16 ^ 16 := by
      have := hl.2; omega
    rw [Nat.mod_eq_of_lt hlt] at h1
    have h2 := ih (by omega) h1
    have he' : (E * 16 ^ 16 + (Hax.index e (m : Int)).toNat) * (2 ^ 64) ^ m
          + (e.toList.take m).foldr (fun x acc => x.toNat + 2 ^ 64 * acc) 0
        = E * (2 ^ 64) ^ (m + 1)
          + (e.toList.take (m + 1)).foldr (fun x acc => x.toNat + 2 ^ 64 * acc) 0 := by
      rw [foldr_take_succ 64 e.toList m (by simpa using hm), ← hidx,
        show (16 : ℕ) ^ 16 = 2 ^ 64 by norm_num]
      ring
    rw [he'] at h2
    exact h2

/-- `Field::pow` of `Fp256Mont` on canonical limbs and an exponent of 64-bit limbs:
    canonical limbs of the Montgomery value to the power the limbs encode,
    little-endian. -/
theorem Field_pow_val {a e : Array Int} (ha : Canon a) (he : IsDigits 64 e) :
    Canon (Field_pow a e) ∧ montVal (Field_pow a e) = montVal a ^ leValue 64 e := by
  have h0 : PowInv (montVal a) (R_LIMBS, false) 0 :=
    ⟨canon_R, by rw [montVal_R, pow_zero], fun _ => rfl⟩
  obtain ⟨hc, hv, -⟩ := powLimbs_inv ha he e.size le_rfl h0
  rw [Field_pow_eq]
  refine ⟨hc, ?_⟩
  rw [hv]
  congr 1
  rw [zero_mul, zero_add, leValue, List.take_of_length_le (by simp)]

/-! ## `from_bytes`: the value -/

omit [PrimeirDeps] in
/-- Shifting an accumulator below `256 ^ t` by a byte and or-ing a byte in appends the
    byte as the lowest base-256 digit. -/
theorem orShl {acc x : Int} (t : ℕ) (ht : t < 8) (ha0 : 0 ≤ acc) (ha : acc < 256 ^ t)
    (hx0 : 0 ≤ x) (hx : x < 256) :
    Hax.bitor_w 64 (Hax.shl_w 64 acc (8 : Int)) (Hax.castVal_w 64 x) = acc * 256 + x ∧
      0 ≤ acc * 256 + x ∧ acc * 256 + x < 256 ^ (t + 1) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le ha0
  obtain ⟨y, rfl⟩ := Int.eq_ofNat_of_zero_le hx0
  have hy : y < 256 := by omega
  have hm : m < 256 ^ t := by exact_mod_cast ha
  have h7 : 256 ^ t ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm7 : m * 256 + y < 2 ^ 64 := by
    have : m < 256 ^ 7 := lt_of_lt_of_le hm h7
    norm_num at this ⊢
    omega
  have hbd : m * 256 + y < 256 ^ (t + 1) := by
    have := Nat.mul_le_mul_right 256 (Nat.succ_le_of_lt hm)
    rw [pow_succ]
    omega
  refine ⟨?_, by positivity, by exact_mod_cast hbd⟩
  have hsh : Hax.shl_w 64 (m : Int) (8 : Int) = ((m * 256 : ℕ) : Int) := by
    rw [show (8 : Int) = ((8 : ℕ) : Int) from rfl, shl_of_nonneg (w := 64) 8 (by positivity)]
    push_cast
    rw [Int.emod_eq_of_lt (by positivity) (by omega)]
  have hc : Hax.castVal_w 64 (y : Int) = (y : Int) :=
    castVal_of_lt (by positivity) (by omega)
  rw [hsh, hc]
  simp only [Hax.bitor_w, Int.toNat_natCast]
  have h1 : m * 256 < 2 ^ 64 := lt_of_le_of_lt (Nat.le_add_right _ _) hm7
  have h2 : y < 2 ^ 64 := lt_of_le_of_lt (Nat.le_add_left _ _) hm7
  have h3 : y < 2 ^ 8 := hy
  have h4 : m * 256 = m <<< 8 := by rw [Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, h4, ← Nat.shiftLeft_add_eq_or_of_lt h3 m,
    Nat.shiftLeft_eq]
  push_cast
  norm_num

omit [PrimeirDeps] in
/-- A descending fold of eight steps unrolls. -/
theorem downFold_eight {α : Type} (g : ℕ → α → α) (acc : α) :
    downFold g 8 acc = g 0 (g 1 (g 2 (g 3 (g 4 (g 5 (g 6 (g 7 acc))))))) := rfl

/-- The natural number with the eight base-256 digits `d o, …, d (o + 7)`, little-endian. -/
def wordNat (d : ℕ → ℕ) (o : ℕ) : ℕ :=
  d o + 256 * (d (o + 1) + 256 * (d (o + 2) + 256 * (d (o + 3) + 256 * (d (o + 4) +
    256 * (d (o + 5) + 256 * (d (o + 6) + 256 * d (o + 7)))))))

/-- The natural number with the 32 base-256 digits `d 0, …, d 31`, little-endian. -/
def chunkNat (d : ℕ → ℕ) : ℕ :=
  wordNat d 0 + 2 ^ 64 * (wordNat d 8 + 2 ^ 64 * (wordNat d 16 + 2 ^ 64 * wordNat d 24))

omit [PrimeirDeps] in
/-- A word of `bytes_le_to_limbs` over eight bytes is their little-endian number, below
    `2 ^ 64`. -/
theorem leWord_val {b : Array Int} {i : Int} {d : ℕ → ℕ} {o : ℕ}
    (hd : ∀ j : ℕ, j < 8 →
      Hax.index b (Hax.add (Hax.mul (8 : Int) i) (j : Int)) = (d (o + j) : Int) ∧
        d (o + j) < 256) :
    leWord b i = (wordNat d o : Int) ∧ wordNat d o < 2 ^ 64 := by
  have hx : ∀ j : ℕ, j < 8 → (0 : Int) ≤ (d (o + j) : Int) ∧ (d (o + j) : Int) < 256 :=
    fun j hj => ⟨by positivity, by exact_mod_cast (hd j hj).2⟩
  unfold leWord
  rw [downFold_eight]
  rw [(hd 0 (by norm_num)).1, (hd 1 (by norm_num)).1, (hd 2 (by norm_num)).1,
    (hd 3 (by norm_num)).1, (hd 4 (by norm_num)).1, (hd 5 (by norm_num)).1,
    (hd 6 (by norm_num)).1, (hd 7 (by norm_num)).1]
  obtain ⟨e7, p7, q7⟩ := orShl (acc := 0) 0 (by norm_num) le_rfl (by norm_num)
    (hx 7 (by norm_num)).1 (hx 7 (by norm_num)).2
  rw [e7]
  obtain ⟨e6, p6, q6⟩ := orShl 1 (by norm_num) p7 q7 (hx 6 (by norm_num)).1 (hx 6 (by norm_num)).2
  rw [e6]
  obtain ⟨e5, p5, q5⟩ := orShl 2 (by norm_num) p6 q6 (hx 5 (by norm_num)).1 (hx 5 (by norm_num)).2
  rw [e5]
  obtain ⟨e4, p4, q4⟩ := orShl 3 (by norm_num) p5 q5 (hx 4 (by norm_num)).1 (hx 4 (by norm_num)).2
  rw [e4]
  obtain ⟨e3, p3, q3⟩ := orShl 4 (by norm_num) p4 q4 (hx 3 (by norm_num)).1 (hx 3 (by norm_num)).2
  rw [e3]
  obtain ⟨e2, p2, q2⟩ := orShl 5 (by norm_num) p3 q3 (hx 2 (by norm_num)).1 (hx 2 (by norm_num)).2
  rw [e2]
  obtain ⟨e1, p1, q1⟩ := orShl 6 (by norm_num) p2 q2 (hx 1 (by norm_num)).1 (hx 1 (by norm_num)).2
  rw [e1]
  obtain ⟨e0, p0, q0⟩ := orShl 7 (by norm_num) p1 q1 (hx 0 (by norm_num)).1 (hx 0 (by norm_num)).2
  rw [e0]
  have he : ((((((((0 * 256 + (d (o + 7) : Int)) * 256 + d (o + 6)) * 256 + d (o + 5)) * 256
      + d (o + 4)) * 256 + d (o + 3)) * 256 + d (o + 2)) * 256 + d (o + 1)) * 256 + d (o + 0))
      = (wordNat d o : Int) := by
    unfold wordNat
    rw [show o + 0 = o from rfl]
    push_cast
    ring
  rw [he] at q0 ⊢
  exact ⟨rfl, by norm_num at q0; exact_mod_cast q0⟩

omit [PrimeirDeps] in
theorem R2_LIMBS_eq :
    R2_LIMBS = #[3, 18446744056529682431, 18446744073709551614, 21474836477] := rfl

omit [PrimeirDeps] in
/-- `R2_LIMBS` is canonical. -/
theorem canon_R2 : Canon R2_LIMBS := by
  rw [R2_LIMBS_eq]
  exact ⟨_, _, _, _, rfl, by norm_num [W64], by norm_num [W64], by norm_num [W64],
    by norm_num [W64], by norm_num [val4, pZ]⟩

omit [PrimeirDeps] in
/-- `R2_LIMBS` has Montgomery value `2 ^ 256`. -/
theorem montVal_R2 : montVal R2_LIMBS = 2 ^ 256 := by
  rw [R2_LIMBS_eq]
  have hv : val4 3 18446744056529682431 18446744073709551614 21474836477
      = 2 ^ 256 * 2 ^ 256 % pZ := by
    norm_num [val4, pZ]
  simp only [montVal, limbVal_lit, hv, intCast_emod_pZ]
  rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, mul_assoc, mul_inv_cancel₀ two_pow_ne_zero,
    mul_one]

/-- `from_canonical_bytes` on a buffer of 32 bytes: canonical limbs whose Montgomery
    value is the little-endian number of the bytes. -/
theorem from_canonical_bytes_val {buf : Array Int} {d : ℕ → ℕ}
    (hd : ∀ m : ℕ, m < 32 → Hax.index buf (m : Int) = (d m : Int) ∧ d m < 256) :
    Canon (Fp256Mont_from_canonical_bytes buf) ∧
      montVal (Fp256Mont_from_canonical_bytes buf) = (chunkNat d : Fp256) := by
  have w : ∀ i : ℕ, i < 4 → leWord buf (i : Int) = (wordNat d (8 * i) : Int) ∧
      wordNat d (8 * i) < 2 ^ 64 := fun i hi => leWord_val (fun j hj => by
    have := hd (8 * i + j) (by omega)
    simpa [Hax.add, Hax.mul] using this)
  obtain ⟨e0, b0⟩ := w 0 (by norm_num)
  obtain ⟨e1, b1⟩ := w 1 (by norm_num)
  obtain ⟨e2, b2⟩ := w 2 (by norm_num)
  obtain ⟨e3, b3⟩ := w 3 (by norm_num)
  simp only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.mul_zero, Nat.mul_one,
    Nat.reduceMul] at e0 e1 e2 e3 b0 b1 b2 b3
  have W : ∀ n : ℕ, n < 2 ^ 64 → W64 (n : Int) := fun n h =>
    ⟨by positivity, by exact_mod_cast h⟩
  obtain ⟨r0, r1, r2, r3, hr, hr0, hr1, hr2, hr3, hv⟩ :=
    reduce_once_spec (W _ b0) (W _ b1) (W _ b2) (W _ b3) (Or.inl rfl) (by
      unfold val4 pZ
      omega)
  obtain ⟨hc, hm⟩ := canon_of_emod hr0 hr1 hr2 hr3 hv
  obtain ⟨hc', hv'⟩ := mont_mul_limbs_val hc canon_R2
  have hE : Fp256Mont_from_canonical_bytes buf = mont_mul_limbs #[r0, r1, r2, r3] R2_LIMBS := by
    rw [← hr, ← e0, ← e1, ← e2, ← e3, ← bytes_le_to_limbs_eq]
    rfl
  rw [hE]
  refine ⟨hc', ?_⟩
  rw [hv', hm, montVal_R2, mul_assoc, inv_mul_cancel₀ two_pow_ne_zero, mul_one]
  simp only [val4, chunkNat]
  push_cast
  ring

omit [PrimeirDeps] in
/-- `List.getD` inside the list is the entry. -/
theorem getD_of_lt {l : List Int} {i : ℕ} (h : i < l.length) (d : Int) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

omit [PrimeirDeps] in
/-- `List.getD` past the end of the list is the default. -/
theorem getD_of_le {l : List Int} {i : ℕ} (h : l.length ≤ i) (d : Int) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

omit [PrimeirDeps] in
/-- Every entry of the zero array reads as `0`. -/
theorem index_repeat_zero (n m : Int) : Hax.index (Hax.repeat_ (0 : Int) n) m = 0 := by
  unfold Hax.index
  split_ifs <;> simp [Hax.repeat_]

omit [PrimeirDeps] in
/-- Entry `m` of the 32-entry buffer filled from positions `st, …, en - 1` of `bytes`. -/
theorem copy_index (bytes : Array Int) (st en : Int) (m : ℕ) (hm : m < 32) :
    Hax.index (Hax.foldRange st en (Hax.repeat_ (0 : Int) (32 : Int))
      (fun i buf => Hax.array_update buf (Hax.sub i st) (Hax.index bytes i))) (m : Int)
      = if st + m < en then Hax.index bytes (st + m) else 0 := by
  by_cases h : st ≤ en
  · have key := Hax.foldRange_induct (P := fun (i : Int) (buf : Array Int) =>
        buf.size = 32 ∧ ∀ m : ℕ, m < 32 →
          Hax.index buf (m : Int) = if st + m < i then Hax.index bytes (st + m) else 0)
      (lo := st) (hi := en)
      (f := fun i buf => Hax.array_update buf (Hax.sub i st) (Hax.index bytes i))
      (init := Hax.repeat_ (0 : Int) (32 : Int)) h ?_ ?_
    · exact key.2 m hm
    · refine ⟨by rw [Hax.size_repeat_]; rfl, fun m _ => ?_⟩
      rw [index_repeat_zero, ite_eq_right (by omega)]
    · intro i buf hi1 hi2 ⟨hs, ih⟩
      refine ⟨by rw [Hax.size_array_update_eq, hs], fun m hm => ?_⟩
      by_cases hmi : st + m = i
      · have hsub : Hax.sub i st = (m : Int) := by simp only [Hax.sub]; omega
        rw [hsub, Hax.index_array_update_same _ (by rw [hs, Int.toNat_natCast]; exact hm),
          ite_eq_left (by omega), hmi]
      · rw [Hax.index_array_update_of_ne _ (by rw [hs, Int.toNat_natCast]; exact hm)
          (by simp only [Hax.sub]; omega), ih m hm]
        by_cases hlt : st + m < i
        · rw [ite_eq_left hlt, ite_eq_left (by omega)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]
  · rw [Hax.foldRange_stop _ _ _ _ (by omega), index_repeat_zero, ite_eq_right (by omega)]

omit [PrimeirDeps] in
/-- Entry `m` of the buffer of chunk `k` is byte `32 k + m` of the input, or `0` past its
    end. -/
theorem fbBuf_index {bytes : Array Int} (hb : IsDigits 8 bytes) (k m : ℕ) (hm : m < 32) :
    Hax.index (fbBuf bytes (k : Int)) (m : Int)
        = ((bytes.toList.getD (32 * k + m) 0).toNat : Int) ∧
      (bytes.toList.getD (32 * k + m) 0).toNat < 256 := by
  have hbyte : ∀ n : ℕ, 0 ≤ bytes.toList.getD n 0 ∧ bytes.toList.getD n 0 < 256 := by
    intro n
    by_cases hn : n < bytes.toList.length
    · rw [getD_of_lt hn]
      have := hb _ (List.getElem_mem hn)
      norm_num at this
      exact this
    · rw [getD_of_le (by omega)]
      norm_num
  refine ⟨?_, by have := hbyte (32 * k + m); omega⟩
  rw [Int.toNat_of_nonneg (hbyte _).1, fbBuf, copy_index _ _ _ m hm]
  show (if (32 : Int) * k + m <
      (if decide ((bytes.size : Int) < 32 * k + 32) = true then (bytes.size : Int)
      else 32 * k + 32) then Hax.index bytes ((32 : Int) * k + m) else 0) = _
  have hcond : ((32 : Int) * k + m <
      if decide ((bytes.size : Int) < 32 * k + 32) = true then (bytes.size : Int)
      else 32 * k + 32) ↔ 32 * k + m < bytes.size := by
    split_ifs with hc
    · omega
    · simp only [decide_eq_true_eq] at hc
      omega
  by_cases hlt : 32 * k + m < bytes.size
  · have hnat : ((32 : Int) * k + m).toNat = 32 * k + m := by omega
    rw [ite_eq_left (hcond.mpr hlt), Hax.index_eq_getElem (by rw [hnat]; exact hlt),
      getD_of_lt (by simpa using hlt)]
    simp [hnat]
  · rw [ite_eq_right (fun h => hlt (hcond.mp h)), getD_of_le (by simpa using hlt)]

omit [PrimeirDeps] in
/-- The little-endian value of a list of bytes from position `i` splits off `n` digits. -/
theorem foldr_drop_split (l : List Int) (i n : ℕ) :
    (l.drop i).foldr (fun x acc => x.toNat + 2 ^ 8 * acc) 0
      = ∑ m ∈ Finset.range n, (l.getD (i + m) 0).toNat * 256 ^ m
        + 256 ^ n * (l.drop (i + n)).foldr (fun x acc => x.toNat + 2 ^ 8 * acc) 0 := by
  have step : ∀ i : ℕ, (l.drop i).foldr (fun x acc => x.toNat + 2 ^ 8 * acc) 0
      = (l.getD i 0).toNat
        + 256 * (l.drop (i + 1)).foldr (fun x acc => x.toNat + 2 ^ 8 * acc) 0 := by
    intro i
    by_cases h : i < l.length
    · rw [List.drop_eq_getElem_cons h, List.foldr_cons, getD_of_lt h]
      norm_num
    · rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega),
        getD_of_le (by omega)]
      simp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, step (i + n), pow_succ, Nat.add_assoc]
    ring

omit [PrimeirDeps] in
/-- The little-endian value from position `32 k` is chunk `k` plus `2 ^ 256` times the
    value from position `32 (k + 1)`. -/
theorem foldr_drop_chunk (l : List Int) (k : ℕ) :
    (l.drop (32 * k)).foldr (fun x acc => x.toNat + 2 ^ 8 * acc) 0
      = chunkNat (fun m => (l.getD (32 * k + m) 0).toNat)
        + 2 ^ 256 * (l.drop (32 * (k + 1))).foldr (fun x acc => x.toNat + 2 ^ 8 * acc) 0 := by
  rw [foldr_drop_split l (32 * k) 32, show 32 * (k + 1) = 32 * k + 32 by ring]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, chunkNat, wordNat]
  ring

/-- `Field::from_bytes` of `Fp256Mont` on a byte array of any length: canonical limbs
    whose Montgomery value is the little-endian number of the bytes, reduced modulo
    `p`. -/
theorem Field_from_bytes_val {bytes : Array Int} (hb : IsDigits 8 bytes) :
    Canon (Field_from_bytes bytes) ∧
      montVal (Field_from_bytes bytes) = (leValue 8 bytes : Fp256) := by
  have key : ∀ (n : ℕ) (acc : Array Int), Canon acc →
      montVal acc = (((bytes.toList.drop (32 * n)).foldr
        (fun x acc => x.toNat + 2 ^ 8 * acc) 0 : ℕ) : Fp256) →
      Canon (downFold (fun k acc => fbStep bytes (k : Int) acc) n acc) ∧
        montVal (downFold (fun k acc => fbStep bytes (k : Int) acc) n acc)
          = (leValue 8 bytes : Fp256) := by
    intro n
    induction n with
    | zero => intro acc hc hv; exact ⟨hc, by rw [downFold, hv]; rfl⟩
    | succ n ih =>
      intro acc hc hv
      rw [downFold]
      obtain ⟨cc, cv⟩ := from_canonical_bytes_val
        (d := fun m => (bytes.toList.getD (32 * n + m) 0).toNat)
        (fun m hm => fbBuf_index hb n m hm)
      obtain ⟨mc, mv⟩ := mont_mul_limbs_val hc canon_R2
      obtain ⟨ac, av⟩ := add_mod_val mc cc
      refine ih _ ac ?_
      rw [show fbStep bytes (n : Int) acc = add_mod (mont_mul_limbs acc R2_LIMBS)
        (Fp256Mont_from_canonical_bytes (fbBuf bytes (n : Int))) from rfl, av, mv, cv, hv,
        montVal_R2, foldr_drop_chunk bytes.toList n]
      push_cast
      ring
  rw [Field_from_bytes_eq]
  refine key _ _ canon_zero ?_
  rw [montVal_zero, List.drop_eq_nil_of_le (by rw [Array.length_toList]; omega)]
  simp

/-! ## The laws of `pow`, `from_bytes` and `to_bytes` for the field model -/

omit [PrimeirDeps] in
/-- Canonical limbs with the same Montgomery value are the same array. -/
theorem canon_ext {a b : Array Int} (ha : Canon a) (hb : Canon b) (h : montVal a = montVal b) :
    a = b := by
  obtain ⟨a0, a1, a2, a3, rfl, ha0, ha1, ha2, ha3, hA⟩ := ha
  obtain ⟨b0, b1, b2, b3, rfl, hb0, hb1, hb2, hb3, hB⟩ := hb
  simp only [montVal, limbVal_lit] at h
  have h' := mul_right_cancel₀ (inv_ne_zero two_pow_ne_zero) h
  have hA0 := val4_nonneg ha0 ha1 ha2 ha3
  have hB0 := val4_nonneg hb0 hb1 hb2 hb3
  rw [ZMod.intCast_eq_intCast_iff', ← pZ_eq, Int.emod_eq_of_lt hA0 hA,
    Int.emod_eq_of_lt hB0 hB] at h'
  have e0 : a0 = b0 := by unfold val4 W64 at *; omega
  have e1 : a1 = b1 := by unfold val4 W64 at *; omega
  have e2 : a2 = b2 := by unfold val4 W64 at *; omega
  have e3 : a3 = b3 := by unfold val4 W64 at *; omega
  rw [e0, e1, e2, e3]

/-- The Montgomery P-256 field model satisfies the law of `pow`. -/
theorem fp256MontCtModel_powLaws : fp256MontCtModel.toFieldModel.PowLaws where
  pow_eq _ _ ha he := (Field_pow_val ha he).2
  pow_valid _ _ ha he := (Field_pow_val ha he).1

/-- The Montgomery P-256 field model satisfies the laws of `from_bytes` and `to_bytes`,
    with encodings of 32 bytes. -/
theorem fp256MontCtModel_byteLaws : fp256MontCtModel.toFieldModel.ByteLaws 32 where
  from_bytes_eq _ hb := (Field_from_bytes_val hb).2
  from_bytes_valid _ hb := (Field_from_bytes_val hb).1
  to_bytes_size _ ha := (Field_to_bytes_val ha).1
  to_bytes_isDigits _ ha := (Field_to_bytes_val ha).2.1
  to_bytes_eq a ha :=
    (congrArg (fun n : ℕ => (n : Fp256)) (Field_to_bytes_val ha).2.2).trans
      (ZMod.natCast_zmod_val (montVal a))
  to_bytes_canonical _ _ ha hb h := by rw [canon_ext ha hb h]

end CatCrypt.Crypto.PrimeIR.Fp256Mont
