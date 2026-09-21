/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedCheck10

/-!
# Correctness of the shipped `ed25519_point_add` machine code

`Imported.Ed25519PointAddShipped.ed25519PointAddShippedBlock` is the body of the function
`ed25519_point_add(u64 *out, const u64 *inp)` as printed by the owned backend.
`Ed25519PointAddShippedParts` carries the flag-aware symbolic executor, the generated
program `paG` and the ten part checks; this module gives the values of the generated
blocks and states the correctness of the block.

## Main results

* `paG_val`: the sixteen output handles of `paG` hold the four coordinates of `paSpec`.
* `paCanon_correct`: for a name-keyed state whose eight input coordinates are below
  `p25519`, the canonical block stores the four coordinates of `paSpec` at `%rdi`.
* `paShipped_correct_addr`: the same over `runBlockA` on the imported block, when the
  cells of `paCells` occupy pairwise disjoint eight-byte ranges.
* `paSpec_addSpec`: in `ZMod p25519` the four values of `paSpec` are the coordinates of
  `Ed25519PointAddCompile.addSpec` at `ed25519D`.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519PointAddShipped
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.FieldReduceIdioms
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof

/-! ## 12. The values of the field blocks -/

/-- The limbs of `2^256 - p25519` as words. -/
def kCV : List (BitVec 64) :=
  [BitVec.ofNat 64 19, BitVec.ofNat 64 0, BitVec.ofNat 64 0, BitVec.ofNat 64 (2 ^ 63)]

/-- The limbs of `p25519` as words. -/
def pV : List (BitVec 64) :=
  [BitVec.ofNat 64 (2 ^ 64 - 19), BitVec.ofNat 64 (2 ^ 64 - 1), BitVec.ofNat 64 (2 ^ 64 - 1),
   BitVec.ofNat 64 (2 ^ 63 - 1)]

theorem kCE_eval (ρ : Nat → BitVec 64) : kCE.map (WE.eval ρ) = kCV := rfl

theorem pWE_eval (ρ : Nat → BitVec 64) : pWE.map (WE.eval ρ) = pV := rfl

theorem bignumVal_kCV : bignumVal kCV = 2 ^ 255 + 19 := by
  simp only [kCV, bignumVal, BitVec.toNat_ofNat]
  norm_num

theorem bignumVal_pV : bignumVal pV = 2 ^ 255 - 19 := by
  simp only [pV, bignumVal, BitVec.toNat_ofNat]
  norm_num

theorem lit0_le_one (ρ : Nat → BitVec 64) : ((WE.lit 0).eval ρ).toNat ≤ 1 := by
  show (BitVec.ofNat 64 0).toNat ≤ 1
  decide +kernel

theorem lit1_le_one (ρ : Nat → BitVec 64) : ((WE.lit 1).eval ρ).toNat ≤ 1 := by
  show (BitVec.ofNat 64 1).toNat ≤ 1
  decide +kernel

/-- The split of a carry-chain result into its low limbs and its top limb. -/
theorem split_top (l : List (BitVec 64)) (k : Nat) (hl : l.length = k + 1) :
    bignumVal l = bignumVal l.dropLast + (2 ^ 64) ^ k * (l.getLastD 0).toNat := by
  have hne : l ≠ [] := by intro h; rw [h] at hl; simp at hl
  have hsplit : l.dropLast ++ [l.getLast hne] = l := List.dropLast_concat_getLast hne
  have hdl : l.dropLast.length = k := by
    have hc := congrArg List.length hsplit
    simp only [List.length_append, List.length_cons, List.length_nil, hl] at hc
    omega
  have hgd : l.getLastD 0 = l.getLast hne := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    rfl
  have hbs := bignumVal_snoc l.dropLast (l.getLast hne)
  rw [hsplit, hdl] at hbs
  rw [hbs, hgd]
  ring


theorem lit0_eval (ρ : Nat → BitVec 64) : (WE.lit 0).eval ρ = 0 := rfl

theorem feSelG_length (z : WE) : ∀ (as bs : List WE) (n : Nat), as.length = bs.length →
    (feSelG z as bs n).1.length = as.length ∧ (feSelG z as bs n).2.length = as.length
  | [], [], _, _ => by simp [feSelG]
  | a :: as, b :: bs, n, hl => by
      have ih := feSelG_length z as bs (n + 1) (by simpa using hl)
      simp only [feSelG, List.length_cons]
      omega
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

theorem feCsubG_length (xs : List WE) (n : Nat) (h4 : xs.length = 4) :
    (feCsubG xs n).2.length = 4 := by
  have hlen : xs.length = kCE.length := by rw [h4]; rfl
  obtain ⟨-, hdl⟩ := feAdcG_length xs kCE (.lit 0) n hlen
  simp only [feCsubG]
  rw [(feSelG_length _ _ xs _ (by rw [List.length_dropLast, hdl, h4])).2,
    List.length_dropLast, hdl, h4]

theorem feCsubG_val (ρ : Nat → BitVec 64) (xs : List WE) (n : Nat)
    (h : Holds ρ n (feCsubG xs n).1) (h4 : xs.length = 4) :
    bignumVal ((feCsubG xs n).2.map (WE.eval ρ))
      = (if 2 ^ 255 - 19 ≤ bignumVal (xs.map (WE.eval ρ))
         then bignumVal (xs.map (WE.eval ρ)) - (2 ^ 255 - 19)
         else bignumVal (xs.map (WE.eval ρ))) := by
  have hlen : xs.length = kCE.length := by rw [h4]; rfl
  simp only [feCsubG] at h ⊢
  rw [holds_append] at h
  obtain ⟨hd, hs⟩ := h
  have hdv := feAdcG_val ρ xs kCE (.lit 0) n hd (lit0_le_one ρ)
  rw [kCE_eval, lit0_eval] at hdv
  obtain ⟨-, hdl⟩ := feAdcG_length xs kCE (.lit 0) n hlen
  rw [h4] at hdl
  have hkl : (xs.map (WE.eval ρ)).length = kCV.length := by simp [h4, kCV]
  have hDval : bignumVal (addLimbs (xs.map (WE.eval ρ)) kCV 0)
      = bignumVal (xs.map (WE.eval ρ)) + (2 ^ 255 + 19) := by
    rw [addLimbs_val' _ _ _ (by decide +kernel) hkl, bignumVal_kCV]
    rfl
  have hDlen : (addLimbs (xs.map (WE.eval ρ)) kCV 0).length = 5 := by
    rw [addLimbs_length _ _ _ hkl]
    simp [h4]
  have hsplit := split_top (addLimbs (xs.map (WE.eval ρ)) kCV 0) 4 hDlen
  have hXlt : bignumVal (xs.map (WE.eval ρ)) < 2 ^ 256 := by
    have := bignumVal_lt (xs.map (WE.eval ρ))
    simp only [List.length_map, h4] at this
    norm_num at this
    exact this
  have hDdl : bignumVal (addLimbs (xs.map (WE.eval ρ)) kCV 0).dropLast < 2 ^ 256 := by
    have := bignumVal_lt (addLimbs (xs.map (WE.eval ρ)) kCV 0).dropLast
    rw [List.length_dropLast, hDlen] at this
    norm_num at this
    exact this
  have hpow : ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 := by norm_num
  rw [hpow, hDval] at hsplit
  -- the select
  have hsl := feSelG_val ρ ((feAdcG xs kCE (.lit 0) n).2.getLastD (.lit 0))
    (feAdcG xs kCE (.lit 0) n).2.dropLast xs _ hs
    (by rw [List.length_dropLast, hdl, h4])
  rw [hsl]
  have hz : WE.eval ρ ((feAdcG xs kCE (.lit 0) n).2.getLastD (.lit 0))
      = (addLimbs (xs.map (WE.eval ρ)) kCV 0).getLastD 0 := by
    rw [← hdv, ← lit0_eval ρ, List.getLastD_map]
  have hdrop : ((feAdcG xs kCE (.lit 0) n).2.dropLast).map (WE.eval ρ)
      = (addLimbs (xs.map (WE.eval ρ)) kCV 0).dropLast := by
    rw [List.map_dropLast, hdv]
  rw [hz, hdrop]
  have htop := ((addLimbs (xs.map (WE.eval ρ)) kCV 0).getLastD 0).isLt
  simp only [selL]
  split
  · rename_i hz0
    rw [if_neg (by omega)]
  · rename_i hz0
    have h1 : ((addLimbs (xs.map (WE.eval ρ)) kCV 0).getLastD 0).toNat = 1 := by omega
    rw [h1] at hsplit
    rw [if_pos (by omega)]
    omega


theorem bnlt4 (l : List (BitVec 64)) (h : l.length = 4) : bignumVal l < 2 ^ 256 := by
  have h2 := bignumVal_lt l
  rw [h, show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num] at h2
  exact h2

theorem feAddG_length (xs ys : List WE) (n : Nat) (h4 : xs.length = 4) (h4' : ys.length = 4) :
    (feAddG xs ys n).2.length = 4 := by
  obtain ⟨-, hdl⟩ := feAdcG_length xs ys (.lit 0) n (by rw [h4, h4'])
  rw [h4] at hdl
  simp only [feAddG]
  exact feCsubG_length _ _ (by rw [List.length_dropLast, hdl])

theorem feAddG_val (ρ : Nat → BitVec 64) (xs ys : List WE) (n : Nat)
    (h : Holds ρ n (feAddG xs ys n).1) (h4 : xs.length = 4) (h4' : ys.length = 4)
    (hx : bignumVal (xs.map (WE.eval ρ)) < 2 ^ 255 - 19)
    (hy : bignumVal (ys.map (WE.eval ρ)) < 2 ^ 255 - 19) :
    bignumVal ((feAddG xs ys n).2.map (WE.eval ρ))
      = (bignumVal (xs.map (WE.eval ρ)) + bignumVal (ys.map (WE.eval ρ))) % (2 ^ 255 - 19) := by
  simp only [feAddG] at h ⊢
  rw [holds_append] at h
  obtain ⟨hd, hc⟩ := h
  have hlen : xs.length = ys.length := by rw [h4, h4']
  have hdv := feAdcG_val ρ xs ys (.lit 0) n hd (lit0_le_one ρ)
  rw [lit0_eval] at hdv
  obtain ⟨-, hdl⟩ := feAdcG_length xs ys (.lit 0) n hlen
  rw [h4] at hdl
  have hml : (xs.map (WE.eval ρ)).length = (ys.map (WE.eval ρ)).length := by
    simp [h4, h4']
  have hDval : bignumVal (addLimbs (xs.map (WE.eval ρ)) (ys.map (WE.eval ρ)) 0)
      = bignumVal (xs.map (WE.eval ρ)) + bignumVal (ys.map (WE.eval ρ)) := by
    rw [addLimbs_val' _ _ _ (by decide +kernel) hml]
    rfl
  have hDlen : (addLimbs (xs.map (WE.eval ρ)) (ys.map (WE.eval ρ)) 0).length = 5 := by
    rw [addLimbs_length _ _ _ hml]
    simp [h4]
  have hsplit := split_top (addLimbs (xs.map (WE.eval ρ)) (ys.map (WE.eval ρ)) 0) 4 hDlen
  rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num, hDval] at hsplit
  have hddl := bnlt4 (addLimbs (xs.map (WE.eval ρ)) (ys.map (WE.eval ρ)) 0).dropLast
    (by rw [List.length_dropLast, hDlen])
  have hdrop : ((feAdcG xs ys (.lit 0) n).2.dropLast).map (WE.eval ρ)
      = (addLimbs (xs.map (WE.eval ρ)) (ys.map (WE.eval ρ)) 0).dropLast := by
    rw [List.map_dropLast, hdv]
  have hlow : bignumVal (((feAdcG xs ys (.lit 0) n).2.dropLast).map (WE.eval ρ))
      = bignumVal (xs.map (WE.eval ρ)) + bignumVal (ys.map (WE.eval ρ)) := by
    rw [hdrop]
    omega
  have hcv := feCsubG_val ρ (feAdcG xs ys (.lit 0) n).2.dropLast _ hc
    (by rw [List.length_dropLast, hdl])
  rw [hcv, hlow]
  split <;> omega
theorem feSubG_length (xs ys : List WE) (n : Nat) (h4 : xs.length = 4) (h4' : ys.length = 4) :
    (feSubG xs ys n).2.length = 4 := by
  have hnl : xs.length = (ys.map notW).length := by simp [h4, h4']
  obtain ⟨-, hdl⟩ := feAdcG_length xs (ys.map notW) (.lit 1) n hnl
  rw [h4] at hdl
  have hd4 : (feAdcG xs (ys.map notW) (.lit 1) n).2.dropLast.length = 4 := by
    rw [List.length_dropLast, hdl]
  obtain ⟨-, hel⟩ := feAdcG_length (feAdcG xs (ys.map notW) (.lit 1) n).2.dropLast pWE (.lit 0)
    (n + (feAdcG xs (ys.map notW) (.lit 1) n).1.length) (by rw [hd4]; rfl)
  rw [hd4] at hel
  simp only [feSubG]
  rw [(feSelG_length _ _ _ _ (by rw [hd4, List.length_dropLast, hel])).2, hd4]

theorem feSubG_val (ρ : Nat → BitVec 64) (xs ys : List WE) (n : Nat)
    (h : Holds ρ n (feSubG xs ys n).1) (h4 : xs.length = 4) (h4' : ys.length = 4)
    (hx : bignumVal (xs.map (WE.eval ρ)) < 2 ^ 255 - 19)
    (hy : bignumVal (ys.map (WE.eval ρ)) < 2 ^ 255 - 19) :
    bignumVal ((feSubG xs ys n).2.map (WE.eval ρ))
      = (bignumVal (xs.map (WE.eval ρ)) + (2 ^ 255 - 19 - bignumVal (ys.map (WE.eval ρ))))
        % (2 ^ 255 - 19) := by
  simp only [feSubG] at h ⊢
  rw [holds_append, holds_append] at h
  obtain ⟨hd, he, hs⟩ := h
  have hnl : xs.length = (ys.map notW).length := by simp [h4, h4']
  have hdv := feAdcG_val ρ xs (ys.map notW) (.lit 1) n hd (lit1_le_one ρ)
  rw [notW_map] at hdv
  obtain ⟨-, hdl⟩ := feAdcG_length xs (ys.map notW) (.lit 1) n hnl
  rw [h4] at hdl
  set Dg := (feAdcG xs (ys.map notW) (.lit 1) n).2.dropLast with hDg
  have hd4 : Dg.length = 4 := by rw [hDg, List.length_dropLast, hdl]
  set m := n + (feAdcG xs (ys.map notW) (.lit 1) n).1.length with hmdef
  have hml : (xs.map (WE.eval ρ)).length = (notLimbs (ys.map (WE.eval ρ))).length := by
    simp [notLimbs, h4, h4']
  have hnv := notLimbs_val (ys.map (WE.eval ρ))
  simp only [List.length_map, h4'] at hnv
  rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num] at hnv
  set D := addLimbs (xs.map (WE.eval ρ)) (notLimbs (ys.map (WE.eval ρ))) ((WE.lit 1).eval ρ)
    with hDdef
  have hDval : bignumVal D = bignumVal (xs.map (WE.eval ρ))
      + bignumVal (notLimbs (ys.map (WE.eval ρ))) + 1 := by
    rw [hDdef, addLimbs_val' _ _ _ (lit1_le_one ρ) hml]
    congr 1
  have hDlen : D.length = 5 := by
    rw [hDdef, addLimbs_length _ _ _ hml]
    simp [h4]
  have hsplit := split_top D 4 hDlen
  rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num, hDval] at hsplit
  have hXlt := bnlt4 (xs.map (WE.eval ρ)) (by simp [h4])
  have hddl := bnlt4 D.dropLast (by rw [List.length_dropLast, hDlen])
  have htop := (D.getLastD 0).isLt
  have hdrop : Dg.map (WE.eval ρ) = D.dropLast := by
    rw [hDg, List.map_dropLast, hdv]
  have hev := feAdcG_val ρ Dg pWE (.lit 0) m he (lit0_le_one ρ)
  rw [pWE_eval, lit0_eval, hdrop] at hev
  obtain ⟨-, hel⟩ := feAdcG_length Dg pWE (.lit 0) m (by rw [hd4]; rfl)
  rw [hd4] at hel
  have hel2 : (D.dropLast).length = pV.length := by
    rw [List.length_dropLast, hDlen]; rfl
  have hEval : bignumVal (addLimbs D.dropLast pV 0)
      = bignumVal D.dropLast + (2 ^ 255 - 19) := by
    rw [addLimbs_val' _ _ _ (by decide +kernel) hel2, bignumVal_pV]
    rfl
  have hElen : (addLimbs D.dropLast pV 0).length = 5 := by
    rw [addLimbs_length _ _ _ hel2, List.length_dropLast, hDlen]
  have hesplit := split_top (addLimbs D.dropLast pV 0) 4 hElen
  rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num, hEval] at hesplit
  have hedl := bnlt4 (addLimbs D.dropLast pV 0).dropLast
    (by rw [List.length_dropLast, hElen])
  have hetop := ((addLimbs D.dropLast pV 0).getLastD 0).isLt
  have hsl := feSelG_val ρ ((feAdcG xs (ys.map notW) (.lit 1) n).2.getLastD (.lit 0))
    Dg (feAdcG Dg pWE (.lit 0) m).2.dropLast _ hs
    (by rw [hd4, List.length_dropLast, hel])
  rw [hsl]
  have hz : WE.eval ρ ((feAdcG xs (ys.map notW) (.lit 1) n).2.getLastD (.lit 0))
      = D.getLastD 0 := by
    rw [← hdv, ← lit0_eval ρ, List.getLastD_map]
  have hdrop2 : ((feAdcG Dg pWE (.lit 0) m).2.dropLast).map (WE.eval ρ)
      = (addLimbs D.dropLast pV 0).dropLast := by
    rw [List.map_dropLast, hev]
  rw [hz, hdrop, hdrop2]
  simp only [selL]
  split <;> omega


/-! ## 13. The product row and the schoolbook product -/

theorem bignumVal_append : ∀ (l1 l2 : List (BitVec 64)),
    bignumVal (l1 ++ l2) = bignumVal l1 + (2 ^ 64) ^ l1.length * bignumVal l2
  | [], l2 => by simp [bignumVal]
  | a :: l1, l2 => by
      have ih := bignumVal_append l1 l2
      simp only [List.cons_append, bignumVal, List.length_cons, ih, pow_succ]
      ring

theorem mulhi_le (a b : BitVec 64) : (mulhi a b).toNat ≤ 2 ^ 64 - 2 := by
  have h := mulWide_lo_hi a b
  have ha := a.isLt
  have hb := b.isLt
  have hab : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  norm_num at hab ⊢
  omega

theorem rowW_val : ∀ (xs : List (BitVec 64)) (w h c : BitVec 64), c.toNat ≤ 1 →
    h.toNat + c.toNat < 2 ^ 64 →
    bignumVal (rowW xs w h c) = bignumVal xs * w.toNat + h.toNat + c.toNat
  | [], w, h, c, _, hb => by
      have hz : (h + BitVec.ofNat 64 0 + c).toNat = h.toNat + c.toNat := by
        have h0 : (BitVec.ofNat 64 0).toNat = 0 := by decide +kernel
        rw [BitVec.toNat_add, BitVec.toNat_add, h0, Nat.add_zero,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [rowW, bignumVal, hz]
      omega
  | x :: xs, w, h, c, hc, hb => by
      have hmx := mulWide_lo_hi x w
      have hhi := mulhi_le x w
      have hadc := adc_toNat' (x * w) h c
      have hc' := adc_carry_le' (x * w) h c hc
      have ih := rowW_val xs w (mulhi x w)
        (bSltu (x * w + h) (x * w) + bSltu (x * w + h + c) (x * w + h)) hc' (by omega)
      simp only [rowW, bignumVal, ih]
      generalize hP : bignumVal xs * w.toNat = P
      have hx : x.toNat * w.toNat = (x * w).toNat + (mulhi x w).toNat * 2 ^ 64 := by omega
      calc (x * w + h + c).toNat
            + 2 ^ 64 * (P + (mulhi x w).toNat
              + (bSltu (x * w + h) (x * w) + bSltu (x * w + h + c) (x * w + h)).toNat)
          = ((x * w + h + c).toNat
              + (bSltu (x * w + h) (x * w) + bSltu (x * w + h + c) (x * w + h)).toNat * 2 ^ 64)
            + 2 ^ 64 * P + (mulhi x w).toNat * 2 ^ 64 := by ring
        _ = (x.toNat + 2 ^ 64 * bignumVal xs) * w.toNat + h.toNat + c.toNat := by
            rw [hadc]
            rw [Nat.add_mul, hx]
            rw [show 2 ^ 64 * bignumVal xs * w.toNat = 2 ^ 64 * (bignumVal xs * w.toNat) from by
              ring, hP]
            omega


theorem feAccG_length (i : Nat) (xs : List WE) (y : WE) (acc : List WE) (n : Nat)
    (h4 : xs.length = 4) (hacc : acc.length = i + 4) :
    (feAccG i xs y acc n).2.length = i + 5 := by
  have hdl : (acc.drop i ++ [WE.lit 0]).length = 5 := by
    simp [List.length_drop, hacc]
  have hrl := (feRowG_length xs y (.lit 0) (.lit 0) n).2
  rw [h4] at hrl
  obtain ⟨-, hsl⟩ := feAdcG_length (acc.drop i ++ [.lit 0]) (feRowG xs y (.lit 0) (.lit 0) n).2
    (.lit 0) (n + (feRowG xs y (.lit 0) (.lit 0) n).1.length) (by rw [hdl, hrl])
  rw [hdl] at hsl
  simp only [feAccG, List.length_append, List.length_take, List.length_dropLast, hsl, hacc]
  omega

theorem feAccG_val (ρ : Nat → BitVec 64) (i : Nat) (xs : List WE) (y : WE) (acc : List WE)
    (n : Nat) (h : Holds ρ n (feAccG i xs y acc n).1) (h4 : xs.length = 4)
    (hacc : acc.length = i + 4)
    (hb : bignumVal (acc.map (WE.eval ρ))
        + (2 ^ 64) ^ i * (bignumVal (xs.map (WE.eval ρ)) * (y.eval ρ).toNat)
      < (2 ^ 64) ^ i * 2 ^ 320) :
    bignumVal ((feAccG i xs y acc n).2.map (WE.eval ρ))
      = bignumVal (acc.map (WE.eval ρ))
        + (2 ^ 64) ^ i * (bignumVal (xs.map (WE.eval ρ)) * (y.eval ρ).toNat) := by
  simp only [feAccG] at h ⊢
  rw [holds_append] at h
  obtain ⟨hr, hs⟩ := h
  have hrv := feRowG_val ρ xs y (.lit 0) (.lit 0) n hr (lit0_le_one ρ)
  rw [lit0_eval] at hrv
  have hrl := (feRowG_length xs y (.lit 0) (.lit 0) n).2
  rw [h4] at hrl
  have hdl : (acc.drop i ++ [WE.lit 0]).length = 5 := by simp [List.length_drop, hacc]
  set X := bignumVal (xs.map (WE.eval ρ)) with hX
  set Y := (y.eval ρ).toNat with hY
  set A := (acc.drop i ++ [WE.lit 0]).map (WE.eval ρ) with hA
  set R := rowW (xs.map (WE.eval ρ)) (y.eval ρ) 0 0 with hR
  have hrw : bignumVal R = X * Y := by
    rw [hR, rowW_val _ _ _ _ (by decide +kernel) (by decide +kernel)]
    simp [hX, hY]
  have hsv := feAdcG_val ρ (acc.drop i ++ [.lit 0]) (feRowG xs y (.lit 0) (.lit 0) n).2
    (.lit 0) _ hs (lit0_le_one ρ)
  rw [hrv, lit0_eval, ← hA] at hsv
  obtain ⟨-, hsl⟩ := feAdcG_length (acc.drop i ++ [.lit 0])
    (feRowG xs y (.lit 0) (.lit 0) n).2 (.lit 0)
    (n + (feRowG xs y (.lit 0) (.lit 0) n).1.length) (by rw [hdl, hrl])
  rw [hdl] at hsl
  have hAv : bignumVal A = bignumVal ((acc.map (WE.eval ρ)).drop i) := by
    rw [hA, List.map_append, bignumVal_append]
    simp only [List.map_drop, List.map_cons, List.map_nil, bignumVal]
    rw [lit0_eval]
    show bignumVal ((acc.map (WE.eval ρ)).drop i)
      + (2 ^ 64) ^ ((acc.map (WE.eval ρ)).drop i).length * ((0 : BitVec 64).toNat + 2 ^ 64 * 0)
      = bignumVal ((acc.map (WE.eval ρ)).drop i)
    simp
  have hAl : A.length = 5 := by rw [hA, List.length_map, hdl]
  have hRl : R.length = 5 := by rw [hR, rowW_length, List.length_map, h4]
  have hSv : bignumVal (addLimbs A R 0) = bignumVal A + bignumVal R := by
    rw [addLimbs_val' _ _ _ (by decide +kernel) (by rw [hAl, hRl])]
    rfl
  have hSl : (addLimbs A R 0).length = 6 := by
    rw [addLimbs_length _ _ _ (by rw [hAl, hRl]), hAl]
  have hsplit := split_top (addLimbs A R 0) 5 hSl
  have hsplitacc := bignumVal_take_drop i (acc.map (WE.eval ρ))
  rw [show ((2 : Nat) ^ 64) ^ 5 = 2 ^ 320 from by norm_num, hSv, hAv, hrw] at hsplit
  have hcarry : ((addLimbs A R 0).getLastD 0).toNat = 0 := by
    have hmul : (2 ^ 64) ^ i * (bignumVal ((acc.map (WE.eval ρ)).drop i) + X * Y)
        < (2 ^ 64) ^ i * 2 ^ 320 := by
      rw [Nat.mul_add]
      omega
    have hlt := Nat.lt_of_mul_lt_mul_left hmul
    have hb2 := ((addLimbs A R 0).getLastD 0).isLt
    rcases Nat.eq_zero_or_pos ((addLimbs A R 0).getLastD 0).toNat with hz | hz
    · exact hz
    · exfalso
      have : 2 ^ 320 * 1 ≤ 2 ^ 320 * ((addLimbs A R 0).getLastD 0).toNat :=
        Nat.mul_le_mul_left _ hz
      omega
  rw [List.map_append, bignumVal_append, List.map_take, List.map_dropLast, hsv]
  rw [List.length_take, List.length_map, hacc, show min i (i + 4) = i from by omega]
  have hdl2 : bignumVal (addLimbs A R 0).dropLast
      = bignumVal ((acc.map (WE.eval ρ)).drop i) + X * Y := by
    rw [hcarry] at hsplit
    omega
  rw [hdl2, Nat.mul_add]
  omega


theorem feRowG_out_length (xs : List WE) (w h c : WE) (n : Nat) (h4 : xs.length = 4) :
    (feRowG xs w h c n).2.length = 5 := by
  have := (feRowG_length xs w h c n).2
  rw [h4] at this
  exact this

theorem feProdG_length (xs : List WE) (y0 y1 y2 y3 : WE) (n : Nat) (h4 : xs.length = 4) :
    (feProdG xs y0 y1 y2 y3 n).2.length = 8 := by
  simp only [feProdG]
  rw [feAccG_length 3 xs y3 _ _ h4 (by
    rw [feAccG_length 2 xs y2 _ _ h4 (by
      rw [feAccG_length 1 xs y1 _ _ h4 (by rw [feRowG_out_length _ _ _ _ _ h4])])])]

theorem feProdG_val (ρ : Nat → BitVec 64) (xs : List WE) (y0 y1 y2 y3 : WE) (n : Nat)
    (h : Holds ρ n (feProdG xs y0 y1 y2 y3 n).1) (h4 : xs.length = 4) :
    bignumVal ((feProdG xs y0 y1 y2 y3 n).2.map (WE.eval ρ))
      = bignumVal (xs.map (WE.eval ρ))
        * bignumVal [y0.eval ρ, y1.eval ρ, y2.eval ρ, y3.eval ρ] := by
  simp only [feProdG] at h ⊢
  rw [holds_append, holds_append, holds_append] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  set A0 := (feRowG xs y0 (.lit 0) (.lit 0) n).2 with hA0
  set m0 := n + (feRowG xs y0 (.lit 0) (.lit 0) n).1.length with hm0
  set A1 := (feAccG 1 xs y1 A0 m0).2 with hA1
  set m1 := m0 + (feAccG 1 xs y1 A0 m0).1.length with hm1
  set A2 := (feAccG 2 xs y2 A1 m1).2 with hA2
  set m2 := m1 + (feAccG 2 xs y2 A1 m1).1.length with hm2
  set X := bignumVal (xs.map (WE.eval ρ)) with hX
  have hXlt : X < 2 ^ 256 := bnlt4 _ (by simp [h4])
  have hy0 := (y0.eval ρ).isLt
  have hy1 := (y1.eval ρ).isLt
  have hy2 := (y2.eval ρ).isLt
  have hy3 := (y3.eval ρ).isLt
  have hr0 := feRowG_val ρ xs y0 (.lit 0) (.lit 0) n h0 (lit0_le_one ρ)
  rw [lit0_eval, ← hA0] at hr0
  have hv0 : bignumVal (A0.map (WE.eval ρ)) = X * (y0.eval ρ).toNat := by
    rw [hr0, rowW_val _ _ _ _ (by decide +kernel) (by decide +kernel)]
    simp [hX]
  have hl0 : A0.length = 1 + 4 := by rw [hA0, feRowG_out_length _ _ _ _ _ h4]
  have hb1 : bignumVal (A0.map (WE.eval ρ))
      + (2 ^ 64) ^ 1 * (X * (y1.eval ρ).toNat) < (2 ^ 64) ^ 1 * 2 ^ 320 := by
    rw [hv0]
    calc X * (y0.eval ρ).toNat + (2 ^ 64) ^ 1 * (X * (y1.eval ρ).toNat)
        = X * ((y0.eval ρ).toNat + 2 ^ 64 * (y1.eval ρ).toNat) := by ring
      _ < 2 ^ 256 * 2 ^ 128 := Nat.mul_lt_mul'' hXlt (by omega)
      _ = (2 ^ 64) ^ 1 * 2 ^ 320 := by norm_num
  have hv1 := feAccG_val ρ 1 xs y1 A0 m0 h1 h4 hl0 hb1
  rw [hv0, ← hA1] at hv1
  have hl1 : A1.length = 2 + 4 := by rw [hA1, feAccG_length 1 xs y1 A0 m0 h4 hl0]
  have hb2 : bignumVal (A1.map (WE.eval ρ))
      + (2 ^ 64) ^ 2 * (X * (y2.eval ρ).toNat) < (2 ^ 64) ^ 2 * 2 ^ 320 := by
    rw [hv1]
    calc X * (y0.eval ρ).toNat + (2 ^ 64) ^ 1 * (X * (y1.eval ρ).toNat)
          + (2 ^ 64) ^ 2 * (X * (y2.eval ρ).toNat)
        = X * ((y0.eval ρ).toNat + 2 ^ 64 * (y1.eval ρ).toNat
            + 2 ^ 128 * (y2.eval ρ).toNat) := by ring
      _ < 2 ^ 256 * 2 ^ 192 := Nat.mul_lt_mul'' hXlt (by omega)
      _ = (2 ^ 64) ^ 2 * 2 ^ 320 := by norm_num
  have hv2 := feAccG_val ρ 2 xs y2 A1 m1 h2 h4 hl1 hb2
  rw [hv1, ← hA2] at hv2
  have hl2 : A2.length = 3 + 4 := by rw [hA2, feAccG_length 2 xs y2 A1 m1 h4 hl1]
  have hb3 : bignumVal (A2.map (WE.eval ρ))
      + (2 ^ 64) ^ 3 * (X * (y3.eval ρ).toNat) < (2 ^ 64) ^ 3 * 2 ^ 320 := by
    rw [hv2]
    calc X * (y0.eval ρ).toNat + (2 ^ 64) ^ 1 * (X * (y1.eval ρ).toNat)
          + (2 ^ 64) ^ 2 * (X * (y2.eval ρ).toNat) + (2 ^ 64) ^ 3 * (X * (y3.eval ρ).toNat)
        = X * ((y0.eval ρ).toNat + 2 ^ 64 * (y1.eval ρ).toNat
            + 2 ^ 128 * (y2.eval ρ).toNat + 2 ^ 192 * (y3.eval ρ).toNat) := by ring
      _ < 2 ^ 256 * 2 ^ 256 := Nat.mul_lt_mul'' hXlt (by omega)
      _ = (2 ^ 64) ^ 3 * 2 ^ 320 := by norm_num
  have hv3 := feAccG_val ρ 3 xs y3 A2 m2 h3 h4 hl2 hb3
  rw [hv2] at hv3
  rw [hv3]
  simp only [bignumVal]
  ring


theorem lit38_toNat (ρ : Nat → BitVec 64) : ((WE.lit 38).eval ρ).toNat = 38 := by
  show (BitVec.ofNat 64 38).toNat = 38
  decide +kernel

theorem feFoldG_length (S : List WE) (n : Nat) (h5 : S.length = 5) :
    (feFoldG S n).2.length = 4 := by
  simp only [feFoldG]
  set M := (feRowG (S.drop 4) (.lit 38) (.lit 0) (.lit 0) n).2 with hM
  have hMl : M.length = 2 := by
    rw [hM, (feRowG_length _ _ _ _ _).2, List.length_drop, h5]
  set n3 := n + (feRowG (S.drop 4) (.lit 38) (.lit 0) (.lit 0) n).1.length with hn3
  set U := (feAdcG (S.take 4) (M ++ [.lit 0, .lit 0]) (.lit 0) n3).2 with hU
  have hUl : U.length = 5 := by
    rw [hU, (feAdcG_length _ _ _ _ (by
      rw [List.length_take, h5, List.length_append, hMl]; rfl)).2, List.length_take, h5]
    omega
  set n4 := n3 + (feAdcG (S.take 4) (M ++ [.lit 0, .lit 0]) (.lit 0) n3).1.length with hn4
  set mm := selWE (U.getLastD (.lit 0)) (.lit 38) (.lit 0) with hmm
  set V := (feAdcG U.dropLast [mm, .lit 0, .lit 0, .lit 0] (.lit 0) n4).2 with hV
  have hVl : V.length = 5 := by
    rw [hV, (feAdcG_length _ _ _ _ (by
      rw [List.length_dropLast, hUl]; rfl)).2, List.length_dropLast, hUl]
  refine feCsubG_length _ _ (feCsubG_length _ _ ?_)
  rw [List.length_dropLast, hVl]

theorem feRedG_length (ps : List WE) (n : Nat) (h8 : ps.length = 8) :
    (feRedG ps n).2.length = 4 := by
  simp only [feRedG]
  have hRl : (feRowG (ps.drop 4) (.lit 38) (.lit 0) (.lit 0) n).2.length = 5 := by
    rw [(feRowG_length _ _ _ _ _).2, List.length_drop, h8]
  refine feFoldG_length _ _ ?_
  rw [List.length_dropLast, (feAdcG_length _ _ _ _ (by
    rw [List.length_append, List.length_take, h8, hRl]; rfl)).2,
    List.length_append, List.length_take, h8]
  simp


theorem selW_toNat (c : BitVec 64) :
    (selW c (BitVec.ofNat 64 38) (BitVec.ofNat 64 0)).toNat = if c.toNat = 0 then 0 else 38 := by
  simp only [selW]
  split
  · decide +kernel
  · decide +kernel

theorem feFoldG_val (ρ : Nat → BitVec 64) (S : List WE) (n : Nat)
    (h : Holds ρ n (feFoldG S n).1) (h5 : S.length = 5)
    (hs4 : bignumVal ((S.map (WE.eval ρ)).drop 4) < 64) :
    bignumVal ((feFoldG S n).2.map (WE.eval ρ))
      = bignumVal (S.map (WE.eval ρ)) % (2 ^ 255 - 19) := by
  simp only [feFoldG] at h ⊢
  rw [holds_append, holds_append, holds_append, holds_append] at h
  obtain ⟨hm, hu, hv, hc1, hc2⟩ := h
  set Slo := bignumVal ((S.map (WE.eval ρ)).take 4) with hSlo
  set S4 := bignumVal ((S.map (WE.eval ρ)).drop 4) with hS4
  have hSsplit : bignumVal (S.map (WE.eval ρ)) = Slo + 2 ^ 256 * S4 := by
    have hts := bignumVal_take_drop 4 (S.map (WE.eval ρ))
    rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num] at hts
    exact hts
  have hSlolt : Slo < 2 ^ 256 :=
    bnlt4 _ (by simp [List.length_take, List.length_map, h5])
  set Mg := (feRowG (S.drop 4) (.lit 38) (.lit 0) (.lit 0) n).2 with hMg
  set n3 := n + (feRowG (S.drop 4) (.lit 38) (.lit 0) (.lit 0) n).1.length with hn3
  have hMl : Mg.length = 2 := by
    rw [hMg, (feRowG_length _ _ _ _ _).2, List.length_drop, h5]
  have hMv := feRowG_val ρ (S.drop 4) (.lit 38) (.lit 0) (.lit 0) n hm (lit0_le_one ρ)
  rw [lit0_eval, ← hMg, List.map_drop] at hMv
  have hMval : bignumVal (Mg.map (WE.eval ρ)) = S4 * 38 := by
    rw [hMv, rowW_val _ _ _ _ (by decide +kernel) (by decide +kernel), lit38_toNat]
    simp [hS4]
  set Ug := (feAdcG (S.take 4) (Mg ++ [.lit 0, .lit 0]) (.lit 0) n3).2 with hUg
  set n4 := n3 + (feAdcG (S.take 4) (Mg ++ [.lit 0, .lit 0]) (.lit 0) n3).1.length with hn4
  have hUlenIn : (S.take 4).length = (Mg ++ [WE.lit 0, WE.lit 0]).length := by
    rw [List.length_take, h5, List.length_append, hMl]
    rfl
  have hUv := feAdcG_val ρ (S.take 4) (Mg ++ [.lit 0, .lit 0]) (.lit 0) n3 hu (lit0_le_one ρ)
  rw [lit0_eval, ← hUg, List.map_take, List.map_append] at hUv
  have hUl : Ug.length = 5 := by
    rw [hUg, (feAdcG_length _ _ _ _ hUlenIn).2, List.length_take, h5]
    omega
  have hMzeros : bignumVal (Mg.map (WE.eval ρ) ++ [WE.lit 0, WE.lit 0].map (WE.eval ρ))
      = S4 * 38 := by
    rw [bignumVal_append, hMval]
    simp only [List.map_cons, List.map_nil, bignumVal, lit0_eval]
    simp
  have hUval : bignumVal (Ug.map (WE.eval ρ)) = Slo + S4 * 38 := by
    rw [hUv, addLimbs_val' _ _ _ (by decide +kernel) (by
      rw [List.length_take, List.length_map, h5, List.length_append, List.length_map,
        List.length_map, hMl]
      rfl), hMzeros, hSlo]
    simp
  have hUsplit := split_top (Ug.map (WE.eval ρ)) 4 (by rw [List.length_map, hUl])
  rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num, hUval] at hUsplit
  set U := bignumVal (Ug.map (WE.eval ρ)).dropLast with hU
  set cu := ((Ug.map (WE.eval ρ)).getLastD 0).toNat with hcu
  have hUlt : U < 2 ^ 256 :=
    bnlt4 _ (by simp [List.length_dropLast, List.length_map, hUl])
  have hcu1 : cu ≤ 1 := by
    rcases Nat.lt_or_ge cu 2 with hc | hc
    · omega
    · exfalso
      have : 2 ^ 256 * 2 ≤ 2 ^ 256 * cu := Nat.mul_le_mul_left _ hc
      omega
  set mm := selWE (Ug.getLastD (.lit 0)) (.lit 38) (.lit 0) with hmm
  have hmmv : (mm.eval ρ).toNat = if cu = 0 then 0 else 38 := by
    rw [hmm, selWE_eval]
    show (selW (WE.eval ρ (Ug.getLastD (WE.lit 0))) (BitVec.ofNat 64 38)
      (BitVec.ofNat 64 0)).toNat = _
    rw [selW_toNat, hcu, ← lit0_eval ρ, List.getLastD_map]
  set Vg := (feAdcG Ug.dropLast [mm, .lit 0, .lit 0, .lit 0] (.lit 0) n4).2 with hVg
  set n5 := n4 + (feAdcG Ug.dropLast [mm, .lit 0, .lit 0, .lit 0] (.lit 0) n4).1.length with hn5
  have hVlenIn : Ug.dropLast.length = [mm, WE.lit 0, WE.lit 0, WE.lit 0].length := by
    rw [List.length_dropLast, hUl]
    rfl
  have hVv := feAdcG_val ρ Ug.dropLast [mm, .lit 0, .lit 0, .lit 0] (.lit 0) n4 hv
    (lit0_le_one ρ)
  rw [lit0_eval, ← hVg, List.map_dropLast] at hVv
  have hVl : Vg.length = 5 := by
    rw [hVg, (feAdcG_length _ _ _ _ hVlenIn).2, List.length_dropLast, hUl]
  have hVval : bignumVal (Vg.map (WE.eval ρ)) = U + (if cu = 0 then 0 else 38) := by
    rw [hVv, addLimbs_val' _ _ _ (by decide +kernel) (by
      rw [List.length_dropLast, List.length_map, hUl]
      rfl), ← hU, ← hmmv]
    simp only [List.map_cons, List.map_nil, bignumVal, lit0_eval]
    simp
  have hVsplit := split_top (Vg.map (WE.eval ρ)) 4 (by rw [List.length_map, hVl])
  rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num, hVval] at hVsplit
  set V := bignumVal (Vg.map (WE.eval ρ)).dropLast with hV
  have hVlt : V < 2 ^ 256 :=
    bnlt4 _ (by simp [List.length_dropLast, List.length_map, hVl])
  have hcv : ((Vg.map (WE.eval ρ)).getLastD 0).toNat = 0 := by
    rcases Nat.eq_zero_or_pos ((Vg.map (WE.eval ρ)).getLastD 0).toNat with hz | hz
    · exact hz
    · exfalso
      have hge : 2 ^ 256 * 1 ≤ 2 ^ 256 * ((Vg.map (WE.eval ρ)).getLastD 0).toNat :=
        Nat.mul_le_mul_left _ hz
      by_cases hcu0 : cu = 0
      · rw [if_pos hcu0] at hVsplit
        rw [hcu0] at hUsplit
        omega
      · rw [if_neg hcu0] at hVsplit
        have hcu1' : cu = 1 := by omega
        rw [hcu1'] at hUsplit
        omega
  have hVfin : V = U + (if cu = 0 then 0 else 38) := by
    rw [hcv] at hVsplit
    omega
  have hVd4 : Vg.dropLast.length = 4 := by rw [List.length_dropLast, hVl]
  have hd1 := feCsubG_val ρ Vg.dropLast n5 hc1 hVd4
  rw [List.map_dropLast, ← hV] at hd1
  set C1 := (feCsubG Vg.dropLast n5).2 with hC1
  have hC1l : C1.length = 4 := by rw [hC1]; exact feCsubG_length _ _ hVd4
  have hd2 := feCsubG_val ρ C1 (n5 + (feCsubG Vg.dropLast n5).1.length) hc2 hC1l
  rw [hd1] at hd2
  rw [hd2]
  have hkey : bignumVal (S.map (WE.eval ρ)) = V + (2 ^ 255 - 19) * (2 * (S4 + cu)) := by
    by_cases hcu0 : cu = 0
    · rw [if_pos hcu0] at hVfin
      rw [hcu0] at hUsplit
      rw [hcu0]
      omega
    · have hcu1' : cu = 1 := by omega
      rw [if_neg hcu0] at hVfin
      rw [hcu1'] at hUsplit
      rw [hcu1']
      omega
  rw [hkey, Nat.add_mul_mod_self_left]
  exact CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519.csub_twice_eq_mod V
    hVlt


theorem feRedG_val (ρ : Nat → BitVec 64) (ps : List WE) (n : Nat)
    (h : Holds ρ n (feRedG ps n).1) (h8 : ps.length = 8)
    (hlt : bignumVal (ps.map (WE.eval ρ)) < 2 ^ 510) :
    bignumVal ((feRedG ps n).2.map (WE.eval ρ))
      = bignumVal (ps.map (WE.eval ρ)) % (2 ^ 255 - 19) := by
  simp only [feRedG] at h ⊢
  rw [holds_append, holds_append] at h
  obtain ⟨hr, hs, hf⟩ := h
  set L := bignumVal ((ps.map (WE.eval ρ)).take 4) with hL
  set H := bignumVal ((ps.map (WE.eval ρ)).drop 4) with hH
  have hPsplit : bignumVal (ps.map (WE.eval ρ)) = L + 2 ^ 256 * H := by
    have hts := bignumVal_take_drop 4 (ps.map (WE.eval ρ))
    rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num] at hts
    exact hts
  have hLlt : L < 2 ^ 256 := bnlt4 _ (by simp [List.length_take, List.length_map, h8])
  have hHlt : H < 2 ^ 254 := by
    rcases Nat.lt_or_ge H (2 ^ 254) with hc | hc
    · exact hc
    · exfalso
      have : 2 ^ 256 * 2 ^ 254 ≤ 2 ^ 256 * H := Nat.mul_le_mul_left _ hc
      norm_num at this
      omega
  set Rg := (feRowG (ps.drop 4) (.lit 38) (.lit 0) (.lit 0) n).2 with hRg
  set n1 := n + (feRowG (ps.drop 4) (.lit 38) (.lit 0) (.lit 0) n).1.length with hn1
  have hRl : Rg.length = 5 := by
    rw [hRg, (feRowG_length _ _ _ _ _).2, List.length_drop, h8]
  have hRv := feRowG_val ρ (ps.drop 4) (.lit 38) (.lit 0) (.lit 0) n hr (lit0_le_one ρ)
  rw [lit0_eval, ← hRg, List.map_drop] at hRv
  have hRval : bignumVal (Rg.map (WE.eval ρ)) = H * 38 := by
    rw [hRv, rowW_val _ _ _ _ (by decide +kernel) (by decide +kernel), lit38_toNat]
    simp [hH]
  set Sg := (feAdcG (ps.take 4 ++ [.lit 0]) Rg (.lit 0) n1).2 with hSg
  have hSlenIn : (ps.take 4 ++ [WE.lit 0]).length = Rg.length := by
    rw [List.length_append, List.length_take, h8, hRl]
    rfl
  have hSv := feAdcG_val ρ (ps.take 4 ++ [.lit 0]) Rg (.lit 0) n1 hs (lit0_le_one ρ)
  rw [lit0_eval, ← hSg, List.map_append, List.map_take] at hSv
  have hSl : Sg.length = 6 := by
    rw [hSg, (feAdcG_length _ _ _ _ hSlenIn).2, List.length_append, List.length_take, h8]
    simp
  have hAzeros : bignumVal ((ps.map (WE.eval ρ)).take 4 ++ [WE.lit 0].map (WE.eval ρ)) = L := by
    rw [bignumVal_append]
    simp only [List.map_cons, List.map_nil, bignumVal, lit0_eval]
    simp [hL]
  have hSval : bignumVal (Sg.map (WE.eval ρ)) = L + H * 38 := by
    rw [hSv, addLimbs_val' _ _ _ (by decide +kernel) (by
      rw [List.length_append, List.length_take, List.length_map, h8, List.length_map,
        List.length_map, hRl]
      rfl), hAzeros, hRval]
    simp
  have hSsplit := split_top (Sg.map (WE.eval ρ)) 5 (by rw [List.length_map, hSl])
  rw [show ((2 : Nat) ^ 64) ^ 5 = 2 ^ 320 from by norm_num, hSval] at hSsplit
  have hSdl : bignumVal (Sg.map (WE.eval ρ)).dropLast < 2 ^ 320 := by
    have h2 := bignumVal_lt (Sg.map (WE.eval ρ)).dropLast
    rw [List.length_dropLast, List.length_map, hSl,
      show ((2 : Nat) ^ 64) ^ (6 - 1) = 2 ^ 320 from by norm_num] at h2
    exact h2
  have hcs : ((Sg.map (WE.eval ρ)).getLastD 0).toNat = 0 := by
    rcases Nat.eq_zero_or_pos ((Sg.map (WE.eval ρ)).getLastD 0).toNat with hz | hz
    · exact hz
    · exfalso
      have hge : 2 ^ 320 * 1 ≤ 2 ^ 320 * ((Sg.map (WE.eval ρ)).getLastD 0).toNat :=
        Nat.mul_le_mul_left _ hz
      omega
  have hSdlval : bignumVal (Sg.dropLast.map (WE.eval ρ)) = L + H * 38 := by
    rw [List.map_dropLast, hcs] at *
    omega
  have hSd5 : Sg.dropLast.length = 5 := by rw [List.length_dropLast, hSl]
  -- the fifth limb of the folded value is small
  have hfsplit := bignumVal_take_drop 4 (Sg.dropLast.map (WE.eval ρ))
  rw [show ((2 : Nat) ^ 64) ^ 4 = 2 ^ 256 from by norm_num, hSdlval] at hfsplit
  have hs4 : bignumVal ((Sg.dropLast.map (WE.eval ρ)).drop 4) < 64 := by
    rcases Nat.lt_or_ge (bignumVal ((Sg.dropLast.map (WE.eval ρ)).drop 4)) 64 with hc | hc
    · exact hc
    · exfalso
      have : 2 ^ 256 * 64 ≤ 2 ^ 256 * bignumVal ((Sg.dropLast.map (WE.eval ρ)).drop 4) :=
        Nat.mul_le_mul_left _ hc
      omega
  have hfold := feFoldG_val ρ Sg.dropLast _ hf hSd5 hs4
  rw [hfold, hSdlval, hPsplit]
  have hmod : L + 2 ^ 256 * H = (L + H * 38) + (2 ^ 255 - 19) * (2 * H) := by ring_nf
  rw [hmod, Nat.add_mul_mod_self_left]


theorem map4 (ρ : Nat → BitVec 64) : ∀ (ys : List WE), ys.length = 4 →
    ys.map (WE.eval ρ) = [(ys.getD 0 (.lit 0)).eval ρ, (ys.getD 1 (.lit 0)).eval ρ,
      (ys.getD 2 (.lit 0)).eval ρ, (ys.getD 3 (.lit 0)).eval ρ]
  | [_, _, _, _], _ => rfl
  | [], h => by simp at h
  | [_], h => by simp at h
  | [_, _], h => by simp at h
  | [_, _, _], h => by simp at h
  | _ :: _ :: _ :: _ :: _ :: _, h => by simp at h

theorem feMulG_length (xs ys : List WE) (n : Nat) (h4 : xs.length = 4) :
    (feMulG xs ys n).2.length = 4 := by
  simp only [feMulG]
  exact feRedG_length _ _ (feProdG_length xs _ _ _ _ n h4)

theorem feMulG_val (ρ : Nat → BitVec 64) (xs ys : List WE) (n : Nat)
    (h : Holds ρ n (feMulG xs ys n).1) (h4 : xs.length = 4) (h4' : ys.length = 4)
    (hx : bignumVal (xs.map (WE.eval ρ)) < 2 ^ 255 - 19)
    (hy : bignumVal (ys.map (WE.eval ρ)) < 2 ^ 255 - 19) :
    bignumVal ((feMulG xs ys n).2.map (WE.eval ρ))
      = bignumVal (xs.map (WE.eval ρ)) * bignumVal (ys.map (WE.eval ρ)) % (2 ^ 255 - 19) := by
  simp only [feMulG] at h ⊢
  rw [holds_append] at h
  obtain ⟨hp, hr⟩ := h
  set Pg := (feProdG xs (ys.getD 0 (.lit 0)) (ys.getD 1 (.lit 0)) (ys.getD 2 (.lit 0))
    (ys.getD 3 (.lit 0)) n).2 with hPg
  have hpv := feProdG_val ρ xs (ys.getD 0 (.lit 0)) (ys.getD 1 (.lit 0)) (ys.getD 2 (.lit 0))
    (ys.getD 3 (.lit 0)) n hp h4
  rw [← hPg, ← map4 ρ ys h4'] at hpv
  have hpl : Pg.length = 8 := by
    rw [hPg]
    exact feProdG_length xs _ _ _ _ n h4
  have hplt : bignumVal (Pg.map (WE.eval ρ)) < 2 ^ 510 := by
    rw [hpv]
    calc bignumVal (xs.map (WE.eval ρ)) * bignumVal (ys.map (WE.eval ρ))
        < 2 ^ 255 * 2 ^ 255 := Nat.mul_lt_mul'' (by omega) (by omega)
      _ = 2 ^ 510 := by norm_num
  rw [feRedG_val ρ Pg _ hr hpl hplt, hpv]

theorem slots_eval (ρ : Nat → BitVec 64) : ∀ (es : List WE) (n : Nat), Holds ρ n es →
    ((List.range es.length).map (fun i => (WE.v (n + i) : WE))).map (WE.eval ρ)
      = es.map (WE.eval ρ)
  | [], _, _ => rfl
  | e :: es, n, h => by
      obtain ⟨h0, hr⟩ := h
      have ih := slots_eval ρ es (n + 1) hr
      simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      refine congrArg₂ List.cons (by simpa only [WE.eval, Nat.add_zero] using h0) ?_
      rw [← ih, List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_def, WE.eval]
      congr 1
      omega

theorem feCopyG_val (ρ : Nat → BitVec 64) (xs : List WE) (n : Nat)
    (h : Holds ρ n (feCopyG xs n).1) :
    (feCopyG xs n).2.map (WE.eval ρ) = xs.map (WE.eval ρ) := by
  simp only [feCopyG] at h ⊢
  have hl : (xs.map (fun x => orWE x x)).length = xs.length := by simp
  have := slots_eval ρ (xs.map (fun x => orWE x x)) n h
  rw [hl] at this
  rw [this, List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_def, orWE, WE.eval]
  rw [or_xor_and]
  simp

theorem feCopyG_length (xs : List WE) (n : Nat) (h4 : xs.length = 4) :
    (feCopyG xs n).2.length = 4 := by
  simp only [feCopyG, List.length_map, List.length_range, h4]


/-! ## 14. The value of the program -/

/-- The four output coordinates on the natural values of the eight input coordinates,
    each reduced modulo `p25519`. -/
def paSpec (x1 y1 z1 t1 x2 y2 z2 t2 : Nat) : Nat × Nat × Nat × Nat :=
  let p := 2 ^ 255 - 19
  let a := ((y1 + (p - x1)) % p * ((y2 + (p - x2)) % p)) % p
  let b := ((y1 + x1) % p * ((y2 + x2) % p)) % p
  let c := ((t1 * twoDNat) % p * t2) % p
  let dv := ((z1 + z1) % p * z2) % p
  let e := (b + (p - a)) % p
  let f := (dv + (p - c)) % p
  let g := (dv + c) % p
  let hh := (b + a) % p
  ((e * f) % p, (g * hh) % p, (f * g) % p, (e * hh) % p)

theorem twoDLimbs_val (ρ : Nat → BitVec 64) :
    bignumVal (twoDLimbs.map (WE.eval ρ)) = twoDNat := by
  show bignumVal [BitVec.ofNat 64 (twoDNat % 2 ^ 64),
    BitVec.ofNat 64 (twoDNat / 2 ^ 64 % 2 ^ 64),
    BitVec.ofNat 64 (twoDNat / 2 ^ 128 % 2 ^ 64),
    BitVec.ofNat 64 (twoDNat / 2 ^ 192 % 2 ^ 64)] = twoDNat
  simp only [bignumVal, BitVec.toNat_ofNat, twoDNat]
  norm_num

theorem twoDLimbs_length : twoDLimbs.length = 4 := rfl

theorem twoDNat_lt : twoDNat < 2 ^ 255 - 19 := by
  rw [twoDNat]
  norm_num

theorem mod_lt_p (a : Nat) : a % (2 ^ 255 - 19) < 2 ^ 255 - 19 :=
  Nat.mod_lt _ (by norm_num)



theorem slotsFrom_length (b : Nat) : (slotsFrom b 4).length = 4 := by simp [slotsFrom]

theorem paB1_len : paB1.2.length = 4 :=
  feSubG_length _ _ _ (slotsFrom_length 29) (slotsFrom_length 25)
theorem paB2_len : paB2.2.length = 4 :=
  feSubG_length _ _ _ (slotsFrom_length 45) (slotsFrom_length 41)
theorem paB3_len : paB3.2.length = 4 := feMulG_length _ _ _ paB1_len
theorem paB4_len : paB4.2.length = 4 :=
  feAddG_length _ _ _ (slotsFrom_length 29) (slotsFrom_length 25)
theorem paB5_len : paB5.2.length = 4 :=
  feAddG_length _ _ _ (slotsFrom_length 45) (slotsFrom_length 41)
theorem paB6_len : paB6.2.length = 4 := feMulG_length _ _ _ paB4_len
theorem paB8_len : paB8.2.length = 4 := feMulG_length _ _ _ (slotsFrom_length 37)
theorem paB9_len : paB9.2.length = 4 := feMulG_length _ _ _ paB8_len
theorem paB10_len : paB10.2.length = 4 :=
  feAddG_length _ _ _ (slotsFrom_length 33) (slotsFrom_length 33)
theorem paB11_len : paB11.2.length = 4 := feMulG_length _ _ _ paB10_len
theorem paB12_len : paB12.2.length = 4 := feSubG_length _ _ _ paB6_len paB3_len
theorem paB13_len : paB13.2.length = 4 := feSubG_length _ _ _ paB11_len paB9_len
theorem paB14_len : paB14.2.length = 4 := feAddG_length _ _ _ paB11_len paB9_len
theorem paB15_len : paB15.2.length = 4 := feAddG_length _ _ _ paB6_len paB3_len
theorem paB16_len : paB16.2.length = 4 := feMulG_length _ _ _ paB12_len
theorem paB17_len : paB17.2.length = 4 := feMulG_length _ _ _ paB14_len
theorem paB18_len : paB18.2.length = 4 := feMulG_length _ _ _ paB12_len
theorem paB19_len : paB19.2.length = 4 := feMulG_length _ _ _ paB13_len
theorem paC1_len : paC1.2.length = 4 := feCopyG_length _ _ paB16_len
theorem paC2_len : paC2.2.length = 4 := feCopyG_length _ _ paB17_len
theorem paC3_len : paC3.2.length = 4 := feCopyG_length _ _ paB19_len
theorem paC4_len : paC4.2.length = 4 := feCopyG_length _ _ paB18_len

/-- The value of a limb list of the program, as a natural. -/
def bv (ρ : Nat → BitVec 64) (l : List WE) : Nat := bignumVal (l.map (WE.eval ρ))

theorem paG_val (ρ : Nat → BitVec 64) (h : Holds ρ 57 paG.1)
    (hx1 : bv ρ (slotsFrom 25 4) < 2 ^ 255 - 19)
    (hy1 : bv ρ (slotsFrom 29 4) < 2 ^ 255 - 19)
    (hz1 : bv ρ (slotsFrom 33 4) < 2 ^ 255 - 19)
    (ht1 : bv ρ (slotsFrom 37 4) < 2 ^ 255 - 19)
    (hx2 : bv ρ (slotsFrom 41 4) < 2 ^ 255 - 19)
    (hy2 : bv ρ (slotsFrom 45 4) < 2 ^ 255 - 19)
    (hz2 : bv ρ (slotsFrom 49 4) < 2 ^ 255 - 19)
    (ht2 : bv ρ (slotsFrom 53 4) < 2 ^ 255 - 19) :
    bv ρ paC1.2 = (paSpec (bv ρ (slotsFrom 25 4)) (bv ρ (slotsFrom 29 4))
        (bv ρ (slotsFrom 33 4)) (bv ρ (slotsFrom 37 4)) (bv ρ (slotsFrom 41 4))
        (bv ρ (slotsFrom 45 4)) (bv ρ (slotsFrom 49 4)) (bv ρ (slotsFrom 53 4))).1
      ∧ bv ρ paC2.2 = (paSpec (bv ρ (slotsFrom 25 4)) (bv ρ (slotsFrom 29 4))
        (bv ρ (slotsFrom 33 4)) (bv ρ (slotsFrom 37 4)) (bv ρ (slotsFrom 41 4))
        (bv ρ (slotsFrom 45 4)) (bv ρ (slotsFrom 49 4)) (bv ρ (slotsFrom 53 4))).2.1
      ∧ bv ρ paC3.2 = (paSpec (bv ρ (slotsFrom 25 4)) (bv ρ (slotsFrom 29 4))
        (bv ρ (slotsFrom 33 4)) (bv ρ (slotsFrom 37 4)) (bv ρ (slotsFrom 41 4))
        (bv ρ (slotsFrom 45 4)) (bv ρ (slotsFrom 49 4)) (bv ρ (slotsFrom 53 4))).2.2.1
      ∧ bv ρ paC4.2 = (paSpec (bv ρ (slotsFrom 25 4)) (bv ρ (slotsFrom 29 4))
        (bv ρ (slotsFrom 33 4)) (bv ρ (slotsFrom 37 4)) (bv ρ (slotsFrom 41 4))
        (bv ρ (slotsFrom 45 4)) (bv ρ (slotsFrom 49 4)) (bv ρ (slotsFrom 53 4))).2.2.2 := by
  simp only [paG] at h
  rw [holds_append] at h
  obtain ⟨g1, h⟩ := h
  rw [show 57 + paB1.1.length = paN1 from rfl, holds_append] at h
  obtain ⟨g2, h⟩ := h
  rw [show paN1 + paB2.1.length = paN2 from rfl, holds_append] at h
  obtain ⟨g3, h⟩ := h
  rw [show paN2 + paB3.1.length = paN3 from rfl, holds_append] at h
  obtain ⟨g4, h⟩ := h
  rw [show paN3 + paB4.1.length = paN4 from rfl, holds_append] at h
  obtain ⟨g5, h⟩ := h
  rw [show paN4 + paB5.1.length = paN5 from rfl, holds_append] at h
  obtain ⟨g6, h⟩ := h
  rw [show paN5 + paB6.1.length = paN6 from rfl, holds_append] at h
  obtain ⟨g8, h⟩ := h
  rw [show paN6 + paB8.1.length = paN8 from rfl, holds_append] at h
  obtain ⟨g9, h⟩ := h
  rw [show paN8 + paB9.1.length = paN9 from rfl, holds_append] at h
  obtain ⟨g10, h⟩ := h
  rw [show paN9 + paB10.1.length = paN10 from rfl, holds_append] at h
  obtain ⟨g11, h⟩ := h
  rw [show paN10 + paB11.1.length = paN11 from rfl, holds_append] at h
  obtain ⟨g12, h⟩ := h
  rw [show paN11 + paB12.1.length = paN12 from rfl, holds_append] at h
  obtain ⟨g13, h⟩ := h
  rw [show paN12 + paB13.1.length = paN13 from rfl, holds_append] at h
  obtain ⟨g14, h⟩ := h
  rw [show paN13 + paB14.1.length = paN14 from rfl, holds_append] at h
  obtain ⟨g15, h⟩ := h
  rw [show paN14 + paB15.1.length = paN15 from rfl, holds_append] at h
  obtain ⟨g16, h⟩ := h
  rw [show paN15 + paB16.1.length = paN16 from rfl, holds_append] at h
  obtain ⟨g17, h⟩ := h
  rw [show paN16 + paB17.1.length = paN17 from rfl, holds_append] at h
  obtain ⟨g18, h⟩ := h
  rw [show paN17 + paB18.1.length = paN18 from rfl, holds_append] at h
  obtain ⟨g19, h⟩ := h
  rw [show paN18 + paB19.1.length = paN19 from rfl, holds_append] at h
  obtain ⟨gc1, h⟩ := h
  rw [holds_append] at h
  obtain ⟨gc2, h⟩ := h
  rw [holds_append] at h
  obtain ⟨gc3, gc4⟩ := h
  simp only [bv] at hx1 hy1 hz1 ht1 hx2 hy2 hz2 ht2 ⊢
  have v1 : bignumVal (paB1.2.map (WE.eval ρ))
      = (bignumVal ((slotsFrom 29 4).map (WE.eval ρ))
        + (2 ^ 255 - 19 - bignumVal ((slotsFrom 25 4).map (WE.eval ρ)))) % (2 ^ 255 - 19) :=
    feSubG_val ρ _ _ 57 g1 (slotsFrom_length 29) (slotsFrom_length 25) hy1 hx1
  have v2 : bignumVal (paB2.2.map (WE.eval ρ))
      = (bignumVal ((slotsFrom 45 4).map (WE.eval ρ))
        + (2 ^ 255 - 19 - bignumVal ((slotsFrom 41 4).map (WE.eval ρ)))) % (2 ^ 255 - 19) :=
    feSubG_val ρ _ _ paN1 g2 (slotsFrom_length 45) (slotsFrom_length 41) hy2 hx2
  have v3 : bignumVal (paB3.2.map (WE.eval ρ))
      = bignumVal (paB1.2.map (WE.eval ρ)) * bignumVal (paB2.2.map (WE.eval ρ))
        % (2 ^ 255 - 19) :=
    feMulG_val ρ _ _ paN2 g3 paB1_len paB2_len (by rw [v1]; exact mod_lt_p _)
      (by rw [v2]; exact mod_lt_p _)
  have v4 : bignumVal (paB4.2.map (WE.eval ρ))
      = (bignumVal ((slotsFrom 29 4).map (WE.eval ρ))
        + bignumVal ((slotsFrom 25 4).map (WE.eval ρ))) % (2 ^ 255 - 19) :=
    feAddG_val ρ _ _ paN3 g4 (slotsFrom_length 29) (slotsFrom_length 25) hy1 hx1
  have v5 : bignumVal (paB5.2.map (WE.eval ρ))
      = (bignumVal ((slotsFrom 45 4).map (WE.eval ρ))
        + bignumVal ((slotsFrom 41 4).map (WE.eval ρ))) % (2 ^ 255 - 19) :=
    feAddG_val ρ _ _ paN4 g5 (slotsFrom_length 45) (slotsFrom_length 41) hy2 hx2
  have v6 : bignumVal (paB6.2.map (WE.eval ρ))
      = bignumVal (paB4.2.map (WE.eval ρ)) * bignumVal (paB5.2.map (WE.eval ρ))
        % (2 ^ 255 - 19) :=
    feMulG_val ρ _ _ paN5 g6 paB4_len paB5_len (by rw [v4]; exact mod_lt_p _)
      (by rw [v5]; exact mod_lt_p _)
  have v8' := feMulG_val ρ (slotsFrom 37 4) twoDLimbs paN6 g8 (slotsFrom_length 37)
    twoDLimbs_length ht1 (by rw [twoDLimbs_val]; exact twoDNat_lt)
  rw [twoDLimbs_val] at v8'
  have v8 : bignumVal (paB8.2.map (WE.eval ρ))
      = bignumVal ((slotsFrom 37 4).map (WE.eval ρ)) * twoDNat % (2 ^ 255 - 19) := v8'
  have v9 : bignumVal (paB9.2.map (WE.eval ρ))
      = bignumVal (paB8.2.map (WE.eval ρ)) * bignumVal ((slotsFrom 53 4).map (WE.eval ρ))
        % (2 ^ 255 - 19) :=
    feMulG_val ρ _ _ paN8 g9 paB8_len (slotsFrom_length 53) (by rw [v8]; exact mod_lt_p _) ht2
  have v10 : bignumVal (paB10.2.map (WE.eval ρ))
      = (bignumVal ((slotsFrom 33 4).map (WE.eval ρ))
        + bignumVal ((slotsFrom 33 4).map (WE.eval ρ))) % (2 ^ 255 - 19) :=
    feAddG_val ρ _ _ paN9 g10 (slotsFrom_length 33) (slotsFrom_length 33) hz1 hz1
  have v11 : bignumVal (paB11.2.map (WE.eval ρ))
      = bignumVal (paB10.2.map (WE.eval ρ)) * bignumVal ((slotsFrom 49 4).map (WE.eval ρ))
        % (2 ^ 255 - 19) :=
    feMulG_val ρ _ _ paN10 g11 paB10_len (slotsFrom_length 49)
      (by rw [v10]; exact mod_lt_p _) hz2
  have v12 : bignumVal (paB12.2.map (WE.eval ρ))
      = (bignumVal (paB6.2.map (WE.eval ρ))
        + (2 ^ 255 - 19 - bignumVal (paB3.2.map (WE.eval ρ)))) % (2 ^ 255 - 19) :=
    feSubG_val ρ _ _ paN11 g12 paB6_len paB3_len (by rw [v6]; exact mod_lt_p _)
      (by rw [v3]; exact mod_lt_p _)
  have v13 : bignumVal (paB13.2.map (WE.eval ρ))
      = (bignumVal (paB11.2.map (WE.eval ρ))
        + (2 ^ 255 - 19 - bignumVal (paB9.2.map (WE.eval ρ)))) % (2 ^ 255 - 19) :=
    feSubG_val ρ _ _ paN12 g13 paB11_len paB9_len (by rw [v11]; exact mod_lt_p _)
      (by rw [v9]; exact mod_lt_p _)
  have v14 : bignumVal (paB14.2.map (WE.eval ρ))
      = (bignumVal (paB11.2.map (WE.eval ρ)) + bignumVal (paB9.2.map (WE.eval ρ)))
        % (2 ^ 255 - 19) :=
    feAddG_val ρ _ _ paN13 g14 paB11_len paB9_len (by rw [v11]; exact mod_lt_p _)
      (by rw [v9]; exact mod_lt_p _)
  have v15 : bignumVal (paB15.2.map (WE.eval ρ))
      = (bignumVal (paB6.2.map (WE.eval ρ)) + bignumVal (paB3.2.map (WE.eval ρ)))
        % (2 ^ 255 - 19) :=
    feAddG_val ρ _ _ paN14 g15 paB6_len paB3_len (by rw [v6]; exact mod_lt_p _)
      (by rw [v3]; exact mod_lt_p _)
  have v16 : bignumVal (paB16.2.map (WE.eval ρ))
      = bignumVal (paB12.2.map (WE.eval ρ)) * bignumVal (paB13.2.map (WE.eval ρ))
        % (2 ^ 255 - 19) :=
    feMulG_val ρ _ _ paN15 g16 paB12_len paB13_len (by rw [v12]; exact mod_lt_p _)
      (by rw [v13]; exact mod_lt_p _)
  have v17 : bignumVal (paB17.2.map (WE.eval ρ))
      = bignumVal (paB14.2.map (WE.eval ρ)) * bignumVal (paB15.2.map (WE.eval ρ))
        % (2 ^ 255 - 19) :=
    feMulG_val ρ _ _ paN16 g17 paB14_len paB15_len (by rw [v14]; exact mod_lt_p _)
      (by rw [v15]; exact mod_lt_p _)
  have v18 : bignumVal (paB18.2.map (WE.eval ρ))
      = bignumVal (paB12.2.map (WE.eval ρ)) * bignumVal (paB15.2.map (WE.eval ρ))
        % (2 ^ 255 - 19) :=
    feMulG_val ρ _ _ paN17 g18 paB12_len paB15_len (by rw [v12]; exact mod_lt_p _)
      (by rw [v15]; exact mod_lt_p _)
  have v19 : bignumVal (paB19.2.map (WE.eval ρ))
      = bignumVal (paB13.2.map (WE.eval ρ)) * bignumVal (paB14.2.map (WE.eval ρ))
        % (2 ^ 255 - 19) :=
    feMulG_val ρ _ _ paN18 g19 paB13_len paB14_len (by rw [v13]; exact mod_lt_p _)
      (by rw [v14]; exact mod_lt_p _)
  have w1 : bignumVal (paC1.2.map (WE.eval ρ)) = bignumVal (paB16.2.map (WE.eval ρ)) :=
    congrArg bignumVal (feCopyG_val ρ paB16.2 paN19 gc1)
  have w2 : bignumVal (paC2.2.map (WE.eval ρ)) = bignumVal (paB17.2.map (WE.eval ρ)) :=
    congrArg bignumVal (feCopyG_val ρ paB17.2 _ gc2)
  have w3 : bignumVal (paC3.2.map (WE.eval ρ)) = bignumVal (paB19.2.map (WE.eval ρ)) :=
    congrArg bignumVal (feCopyG_val ρ paB19.2 (paN19 + paC1.1.length + paC2.1.length) gc3)
  have w4 : bignumVal (paC4.2.map (WE.eval ρ)) = bignumVal (paB18.2.map (WE.eval ρ)) :=
    congrArg bignumVal
      (feCopyG_val ρ paB18.2 (paN19 + paC1.1.length + paC2.1.length + paC3.1.length) gc4)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [w1, v16, v12, v13, v6, v3, v11, v9, v1, v2, v4, v5, v8, v10, paSpec]
  · simp only [w2, v17, v14, v15, v6, v3, v11, v9, v1, v2, v4, v5, v8, v10, paSpec]
  · simp only [w3, v19, v13, v14, v11, v9, v8, v10, paSpec]
  · simp only [w4, v18, v12, v15, v6, v3, v1, v2, v4, v5, paSpec]


/-! ## 15. The canonical block -/

/-- The canonical block is the concatenation of the canonical parts, each from the abstract
    state after the previous part. -/
theorem canonD_pointAdd :
    canonD shippedBank ed25519PointAddShippedBlock =
      canonFromD shippedBank {} ed25519PointAddShippedPart01 ++
      (canonFromD shippedBank (paState 1) ed25519PointAddShippedPart02 ++
      (canonFromD shippedBank (paState 2) ed25519PointAddShippedPart03 ++
      (canonFromD shippedBank (paState 3) ed25519PointAddShippedPart04 ++
      (canonFromD shippedBank (paState 4) ed25519PointAddShippedPart05 ++
      (canonFromD shippedBank (paState 5) ed25519PointAddShippedPart06 ++
      (canonFromD shippedBank (paState 6) ed25519PointAddShippedPart07 ++
      (canonFromD shippedBank (paState 7) ed25519PointAddShippedPart08 ++
      (canonFromD shippedBank (paState 8) ed25519PointAddShippedPart09 ++
      canonFromD shippedBank (paState 9) ed25519PointAddShippedPart10)))))))) := by
  unfold canonD ed25519PointAddShippedBlock
  simp only [List.append_assoc]
  rw [canonFromD_append, pointAdd_D_part01.2, canonFromD_append, pointAdd_D_part02.2,
    canonFromD_append, pointAdd_D_part03.2, canonFromD_append, pointAdd_D_part04.2,
    canonFromD_append, pointAdd_D_part05.2, canonFromD_append, pointAdd_D_part06.2,
    canonFromD_append, pointAdd_D_part07.2, canonFromD_append, pointAdd_D_part08.2,
    canonFromD_append, pointAdd_D_part09.2]

/-- The cells the canonical block reads or writes: the sixteen output limbs at `%rdi`, the
    thirty-two input limbs at `%rsi`, and the stack cells at `-128` and `0, 8, …, 392`. -/
def paCells : List (String × Int) :=
  (List.range 16).map (fun i => ("%rdi", ((8 * i : Nat) : Int))) ++
  (List.range 32).map (fun i => ("%rsi", ((8 * i : Nat) : Int))) ++
  (("%rsp", -128) :: (List.range 50).map (fun i => ("%rsp", ((8 * i : Nat) : Int))))

theorem pa_foot1 :
    footOK paCells (canonFromD shippedBank {} ed25519PointAddShippedPart01) = true := by
  decide +kernel
theorem pa_foot2 :
    footOK paCells (canonFromD shippedBank (paState 1) ed25519PointAddShippedPart02)
      = true := by decide +kernel
theorem pa_foot3 :
    footOK paCells (canonFromD shippedBank (paState 2) ed25519PointAddShippedPart03)
      = true := by decide +kernel
theorem pa_foot4 :
    footOK paCells (canonFromD shippedBank (paState 3) ed25519PointAddShippedPart04)
      = true := by decide +kernel
theorem pa_foot5 :
    footOK paCells (canonFromD shippedBank (paState 4) ed25519PointAddShippedPart05)
      = true := by decide +kernel
theorem pa_foot6 :
    footOK paCells (canonFromD shippedBank (paState 5) ed25519PointAddShippedPart06)
      = true := by decide +kernel
theorem pa_foot7 :
    footOK paCells (canonFromD shippedBank (paState 6) ed25519PointAddShippedPart07)
      = true := by decide +kernel
theorem pa_foot8 :
    footOK paCells (canonFromD shippedBank (paState 7) ed25519PointAddShippedPart08)
      = true := by decide +kernel
theorem pa_foot9 :
    footOK paCells (canonFromD shippedBank (paState 8) ed25519PointAddShippedPart09)
      = true := by decide +kernel
theorem pa_foot10 :
    footOK paCells (canonFromD shippedBank (paState 9) ed25519PointAddShippedPart10)
      = true := by decide +kernel

theorem pa_foot : footOK paCells (canonD shippedBank ed25519PointAddShippedBlock) = true := by
  rw [canonD_pointAdd]
  simp only [footOK_append, pa_foot1, pa_foot2, pa_foot3, pa_foot4, pa_foot5, pa_foot6,
    pa_foot7, pa_foot8, pa_foot9, pa_foot10, Bool.and_self]


/-! ## 16. The canonical block computes the addition -/

/-- The entry slot values: slots `25 .. 56` hold the input cells of `%rsi`, and slots
    `16 .. 24` the literals of `cK`. -/
def rho0 (st : JState 64) (j : Nat) : BitVec 64 :=
  if 25 ≤ j ∧ j < 57 then st.mem "%rsi" ((8 * (j - 25) : Nat) : Int)
  else if 16 ≤ j ∧ j < 25 then BitVec.ofNat 64 (cLits.getD (j - 16) 0)
  else 0

/-- The slot values of the addition on the input cells of `st`. -/
def rhoPA (st : JState 64) : Nat → BitVec 64 := wrun 57 paStmts (rho0 st)

theorem paStmts_wf : wfB 57 paStmts = true := by decide +kernel



theorem paC1_eq : paC1.2 = [.v 2352, .v 2353, .v 2354, .v 2355] := by decide +kernel
theorem paC2_eq : paC2.2 = [.v 2356, .v 2357, .v 2358, .v 2359] := by decide +kernel
theorem paC3_eq : paC3.2 = [.v 2360, .v 2361, .v 2362, .v 2363] := by decide +kernel
theorem paC4_eq : paC4.2 = [.v 2364, .v 2365, .v 2366, .v 2367] := by decide +kernel

theorem paOuts_eq : paOuts = [.v 2352, .v 2353, .v 2354, .v 2355, .v 2356, .v 2357,
    .v 2358, .v 2359, .v 2360, .v 2361, .v 2362, .v 2363, .v 2364, .v 2365, .v 2366,
    .v 2367] := by decide +kernel

theorem holds_rhoPA (st : JState 64) : Holds (rhoPA st) 57 paStmts :=
  holds_wrun _ _ _ paStmts_wf

theorem rhoPA_const (st : JState 64) (j c : Nat) (h : cK j = some c) :
    rhoPA st j = BitVec.ofNat 64 c := by
  unfold cK at h
  split_ifs at h with hj
  have hlt : j - 16 < cLits.length := by
    rcases Nat.lt_or_ge (j - 16) cLits.length with hc | hc
    · exact hc
    · rw [List.getElem?_eq_none hc] at h
      cases h
  have hj25 : j < 25 := by
    have : cLits.length = 9 := by decide +kernel
    omega
  have hgd : cLits.getD (j - 16) 0 = c := by
    rw [List.getD_eq_getElem?_getD, h]
    rfl
  rw [rhoPA, wrun_below _ _ _ _ (by omega), rho0]
  rw [if_neg (by omega), if_pos ⟨hj, hj25⟩, hgd]

theorem paIn_holds (st : JState 64) : MapHolds (rhoPA st) paIn st := by
  intro p hp
  simp only [paIn, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  simp only [Loc.val, WE.eval, rhoPA]
  rw [wrun_below _ _ _ _ (by omega)]
  simp only [rho0]
  rw [if_pos ⟨by omega, by omega⟩]
  congr 2
  omega


/-- The value of input coordinate `k`: the four limbs at `%rsi + 32k`. -/
def paInVal (st : JState 64) (k : Nat) : Nat :=
  bignumVal ((List.range 4).map fun i => st.mem "%rsi" ((8 * (4 * k + i) : Nat) : Int))

/-- The value of output coordinate `k`: the four limbs at `%rdi + 32k`. -/
def paOutVal (s : JState 64) (k : Nat) : Nat :=
  bignumVal ((List.range 4).map fun i => s.mem "%rdi" ((8 * (4 * k + i) : Nat) : Int))

theorem slots_eq_in (st : JState 64) (k : Nat) (hk : k < 8) :
    (slotsFrom (25 + 4 * k) 4).map (WE.eval (rhoPA st))
      = (List.range 4).map fun i => st.mem "%rsi" ((8 * (4 * k + i) : Nat) : Int) := by
  simp only [slotsFrom, List.map_map]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simp only [Function.comp_def, WE.eval, rhoPA]
  rw [wrun_below _ _ _ _ (by omega), rho0, if_pos ⟨by omega, by omega⟩]
  congr 2
  omega

theorem bv_in (st : JState 64) (k : Nat) (hk : k < 8) :
    bv (rhoPA st) (slotsFrom (25 + 4 * k) 4) = paInVal st k := by
  rw [bv, slots_eq_in st k hk, paInVal]

set_option maxRecDepth 8000 in
/-- **The canonical block computes the addition.** For every name-keyed state whose eight
    input coordinates are below `p25519`, the canonical block stores at `%rdi` the four
    coordinates of `paSpec` on those values, each below `p25519`. -/
theorem paCanon_correct (st : JState 64)
    (b0 : paInVal st 0 < 2 ^ 255 - 19) (b1 : paInVal st 1 < 2 ^ 255 - 19)
    (b2 : paInVal st 2 < 2 ^ 255 - 19) (b3 : paInVal st 3 < 2 ^ 255 - 19)
    (b4 : paInVal st 4 < 2 ^ 255 - 19) (b5 : paInVal st 5 < 2 ^ 255 - 19)
    (b6 : paInVal st 6 < 2 ^ 255 - 19) (b7 : paInVal st 7 < 2 ^ 255 - 19) :
    paOutVal (runBlock st (canonD shippedBank ed25519PointAddShippedBlock)) 0
        = (paSpec (paInVal st 0) (paInVal st 1) (paInVal st 2) (paInVal st 3)
            (paInVal st 4) (paInVal st 5) (paInVal st 6) (paInVal st 7)).1
      ∧ paOutVal (runBlock st (canonD shippedBank ed25519PointAddShippedBlock)) 1
        = (paSpec (paInVal st 0) (paInVal st 1) (paInVal st 2) (paInVal st 3)
            (paInVal st 4) (paInVal st 5) (paInVal st 6) (paInVal st 7)).2.1
      ∧ paOutVal (runBlock st (canonD shippedBank ed25519PointAddShippedBlock)) 2
        = (paSpec (paInVal st 0) (paInVal st 1) (paInVal st 2) (paInVal st 3)
            (paInVal st 4) (paInVal st 5) (paInVal st 6) (paInVal st 7)).2.2.1
      ∧ paOutVal (runBlock st (canonD shippedBank ed25519PointAddShippedBlock)) 3
        = (paSpec (paInVal st 0) (paInVal st 1) (paInVal st 2) (paInVal st 3)
            (paInVal st 4) (paInVal st 5) (paInVal st 6) (paInVal st 7)).2.2.2 := by
  have hH := holds_rhoPA st
  have hK : ∀ (a j c : Nat), j < a → cK j = some c → rhoPA st j = BitVec.ofNat 64 c :=
    fun _ j c _ hc => rhoPA_const st j c hc
  have hsp : ∀ (l l1 l2 : List WE) (m n : Nat), l = l1 ++ l2 → l1.length = m →
      Holds (rhoPA st) n l → Holds (rhoPA st) n l1 ∧ Holds (rhoPA st) (n + m) l2 := by
    intro l l1 l2 m n he hm h
    subst he
    subst hm
    exact (holds_append (rhoPA st) l1 l2 n).1 h
  obtain ⟨k1, r2⟩ := hsp paR1 paSl1 paR2 182 57 (List.take_append_drop 182 paR1).symm
    paSl1_len hH
  obtain ⟨k2, r3⟩ := hsp paR2 paSl2 paR3 260 239 (List.take_append_drop 260 paR2).symm
    paSl2_len r2
  obtain ⟨k3, r4⟩ := hsp paR3 paSl3 paR4 263 499 (List.take_append_drop 263 paR3).symm
    paSl3_len r3
  obtain ⟨k4, r5⟩ := hsp paR4 paSl4 paR5 258 762 (List.take_append_drop 258 paR4).symm
    paSl4_len r4
  obtain ⟨k5, r6⟩ := hsp paR5 paSl5 paR6 250 1020 (List.take_append_drop 250 paR5).symm
    paSl5_len r5
  obtain ⟨k6, r7⟩ := hsp paR6 paSl6 paR7 225 1270 (List.take_append_drop 225 paR6).symm
    paSl6_len r6
  obtain ⟨k7, r8⟩ := hsp paR7 paSl7 paR8 253 1495 (List.take_append_drop 253 paR7).symm
    paSl7_len r7
  obtain ⟨k8, r9⟩ := hsp paR8 paSl8 paR9 248 1748 (List.take_append_drop 248 paR8).symm
    paSl8_len r8
  obtain ⟨k9, k10⟩ := hsp paR9 paSl9 paSl10 255 1996 (List.take_append_drop 255 paR9).symm
    paSl9_len r9
  clear hsp r2 r3 r4 r5 r6 r7 r8 r9
  have znone : ∀ (s : JState 64), ZfHolds (rhoPA st) none s := fun _ e he => by cases he
  have cnone : ∀ (s : JState 64), CfHolds (rhoPA st) none s := fun _ e he => by cases he
  obtain ⟨q1, c1, -⟩ := partCheck2_sound 57 paSl1 paIn none none paMap1
    (some (aoWE (.v 238))) none _ pa_part1 (rhoPA st)
    k1 (hK 57) st (paIn_holds st) (cnone st) (znone st)
  obtain ⟨s1, hs1⟩ : ∃ s,
      runBlock st (canonFromD shippedBank {} ed25519PointAddShippedPart01) = s := ⟨_, rfl⟩
  rw [hs1] at q1 c1
  obtain ⟨q2, c2, -⟩ := partCheck2_sound 239 paSl2 paMap1 (some (aoWE (.v 238)))
    none paMap2 none none _ pa_part2 (rhoPA st)
    k2 (hK 239) s1 q1 c1 (znone _)
  obtain ⟨s2, hs2⟩ : ∃ s,
      runBlock s1 (canonFromD shippedBank (paState 1) ed25519PointAddShippedPart02) = s :=
    ⟨_, rfl⟩
  rw [hs2] at q2 c2
  obtain ⟨q3, c3, -⟩ := partCheck2_sound 499 paSl3 paMap2 none none paMap3
    (some (.v 761)) none _ pa_part3 (rhoPA st)
    k3 (hK 499) s2 q2 c2 (znone _)
  obtain ⟨s3, hs3⟩ : ∃ s,
      runBlock s2 (canonFromD shippedBank (paState 2) ed25519PointAddShippedPart03) = s :=
    ⟨_, rfl⟩
  rw [hs3] at q3 c3
  obtain ⟨q4, c4, -⟩ := partCheck2_sound 762 paSl4 paMap3 (some (.v 761)) none
    paMap4 (some (.v 1019)) none _ pa_part4 (rhoPA st)
    k4 (hK 762) s3 q3 c3 (znone _)
  obtain ⟨s4, hs4⟩ : ∃ s,
      runBlock s3 (canonFromD shippedBank (paState 3) ed25519PointAddShippedPart04) = s :=
    ⟨_, rfl⟩
  rw [hs4] at q4 c4
  obtain ⟨q5, c5, -⟩ := partCheck2_sound 1020 paSl5 paMap4 (some (.v 1019))
    none paMap5 (some (.v 1269)) none _ pa_part5 (rhoPA st)
    k5 (hK 1020) s4 q4 c4 (znone _)
  obtain ⟨s5, hs5⟩ : ∃ s,
      runBlock s4 (canonFromD shippedBank (paState 4) ed25519PointAddShippedPart05) = s :=
    ⟨_, rfl⟩
  rw [hs5] at q5 c5
  obtain ⟨q6, c6, -⟩ := partCheck2_sound 1270 paSl6 paMap5 (some (.v 1269))
    none paMap6 (some (aoWE (.v 1494))) none _ pa_part6 (rhoPA st)
    k6 (hK 1270) s5 q5 c5 (znone _)
  obtain ⟨s6, hs6⟩ : ∃ s,
      runBlock s5 (canonFromD shippedBank (paState 5) ed25519PointAddShippedPart06) = s :=
    ⟨_, rfl⟩
  rw [hs6] at q6 c6
  obtain ⟨q7, c7, -⟩ := partCheck2_sound 1495 paSl7 paMap6
    (some (aoWE (.v 1494))) none paMap7 (some (.v 1747)) none _ pa_part7 (rhoPA st)
    k7 (hK 1495) s6 q6 c6 (znone _)
  obtain ⟨s7, hs7⟩ : ∃ s,
      runBlock s6 (canonFromD shippedBank (paState 6) ed25519PointAddShippedPart07) = s :=
    ⟨_, rfl⟩
  rw [hs7] at q7 c7
  obtain ⟨q8, c8, -⟩ := partCheck2_sound 1748 paSl8 paMap7 (some (.v 1747))
    none paMap8 none none _ pa_part8 (rhoPA st)
    k8 (hK 1748) s7 q7 c7 (znone _)
  obtain ⟨s8, hs8⟩ : ∃ s,
      runBlock s7 (canonFromD shippedBank (paState 7) ed25519PointAddShippedPart08) = s :=
    ⟨_, rfl⟩
  rw [hs8] at q8 c8
  obtain ⟨q9, c9, -⟩ := partCheck2_sound 1996 paSl9 paMap8 none none paMap9
    (some (aoWE (.v 2250))) none _ pa_part9 (rhoPA st)
    k9 (hK 1996) s8 q8 c8 (znone _)
  obtain ⟨s9, hs9⟩ : ∃ s,
      runBlock s8 (canonFromD shippedBank (paState 8) ed25519PointAddShippedPart09) = s :=
    ⟨_, rfl⟩
  rw [hs9] at q9 c9
  obtain ⟨q10, -, -⟩ := partCheck2_sound 2251 paSl10 paMap9
    (some (aoWE (.v 2250))) none paOut none none _ pa_part10 (rhoPA st)
    k10 (hK 2251) s9 q9 c9 (znone _)
  clear q1 q2 q3 q4 q5 q6 q7 q8 q9 c1 c2 c3 c4 c5 c6 c7 c8 c9
  rw [← hs9, ← hs8, ← hs7, ← hs6, ← hs5, ← hs4, ← hs3, ← hs2, ← hs1] at q10
  simp only [← runBlock_cat, List.append_assoc] at q10
  rw [← canonD_pointAdd] at q10
  generalize runBlock st (canonD shippedBank ed25519PointAddShippedBlock) = out at q10 ⊢
  have hmem : ∀ j, j < 16 → out.mem "%rdi" ((8 * j : Nat) : Int) = rhoPA st (2352 + j) := by
    intro j hj
    have hin : (Loc.cell "%rdi" ((8 * j : Nat) : Int), WE.v (2352 + j)) ∈ paOut := by
      simp only [paOut, List.mem_map, List.mem_range]
      exact ⟨j, hj, by rw [paOuts_eq]; interval_cases j <;> rfl⟩
    have := q10 _ hin
    simpa only [Loc.val, WE.eval] using this
  have hg : ∀ k, k < 4 → paOutVal out k
      = bignumVal ((List.range 4).map fun i => rhoPA st (2352 + (4 * k + i))) := by
    intro k hk
    simp only [paOutVal]
    refine congrArg bignumVal ?_
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    exact hmem (4 * k + i) (by omega)
  have hbv : ∀ k, k < 8 → bv (rhoPA st) (slotsFrom (25 + 4 * k) 4) = paInVal st k :=
    fun k hk => bv_in st k hk
  have hv := paG_val (rhoPA st) hH
    (by rw [show (25 : Nat) = 25 + 4 * 0 from rfl, hbv 0 (by omega)]; exact b0)
    (by rw [show (29 : Nat) = 25 + 4 * 1 from rfl, hbv 1 (by omega)]; exact b1)
    (by rw [show (33 : Nat) = 25 + 4 * 2 from rfl, hbv 2 (by omega)]; exact b2)
    (by rw [show (37 : Nat) = 25 + 4 * 3 from rfl, hbv 3 (by omega)]; exact b3)
    (by rw [show (41 : Nat) = 25 + 4 * 4 from rfl, hbv 4 (by omega)]; exact b4)
    (by rw [show (45 : Nat) = 25 + 4 * 5 from rfl, hbv 5 (by omega)]; exact b5)
    (by rw [show (49 : Nat) = 25 + 4 * 6 from rfl, hbv 6 (by omega)]; exact b6)
    (by rw [show (53 : Nat) = 25 + 4 * 7 from rfl, hbv 7 (by omega)]; exact b7)
  rw [show (25 : Nat) = 25 + 4 * 0 from rfl, show (29 : Nat) = 25 + 4 * 1 from rfl,
    show (33 : Nat) = 25 + 4 * 2 from rfl, show (37 : Nat) = 25 + 4 * 3 from rfl,
    show (41 : Nat) = 25 + 4 * 4 from rfl, show (45 : Nat) = 25 + 4 * 5 from rfl,
    show (49 : Nat) = 25 + 4 * 6 from rfl, show (53 : Nat) = 25 + 4 * 7 from rfl,
    hbv 0 (by omega), hbv 1 (by omega), hbv 2 (by omega), hbv 3 (by omega),
    hbv 4 (by omega), hbv 5 (by omega), hbv 6 (by omega), hbv 7 (by omega)] at hv
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  simp only [bv, paC1_eq, paC2_eq, paC3_eq, paC4_eq, List.map_cons, List.map_nil,
    WE.eval] at hv1 hv2 hv3 hv4
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hg 0 (by omega), ← hv1]; rfl
  · rw [hg 1 (by omega), ← hv2]; rfl
  · rw [hg 2 (by omega), ← hv3]; rfl
  · rw [hg 3 (by omega), ← hv4]; rfl


/-! ## 17. The address machine -/

/-- The value of input coordinate `k` of the address state: the four words at
    `%rsi + 32k`. -/
def paInValA (sa : AState) (k : Nat) : Nat :=
  bignumVal ((List.range 4).map fun i =>
    read64 sa.mem (sa.regs "%rsi" + BitVec.ofInt 64 ((8 * (4 * k + i) : Nat) : Int)))

/-- The value of output coordinate `k` after the block: the four words at `%rdi + 32k`. -/
def paOutValA (sa : AState) (k : Nat) : Nat :=
  bignumVal ((List.range 4).map fun i =>
    read64 (runBlockA sa ed25519PointAddShippedBlock).mem
      (sa.regs "%rdi" + BitVec.ofInt 64 ((8 * (4 * k + i) : Nat) : Int)))

theorem paInValA_eq (sa : AState) (k : Nat) (_hk : k < 8) :
    paInValA sa k = paInVal (jOf shippedBank sa) k := by
  have hsi : shippedBank "%rsi" = some "%rsi" := by simp [shippedBank]
  simp only [paInValA, paInVal, jOf]
  refine congrArg bignumVal (List.map_congr_left ?_)
  intro i _
  rw [absMem_shipped _ _ _ _ hsi]

set_option maxRecDepth 8000 in
/-- **The shipped block computes the addition.** When the cells of `paCells` occupy
    pairwise disjoint eight-byte ranges and the eight input coordinates at `%rsi + 32k`
    are below `p25519`, `runBlockA` of the imported block leaves at `%rdi + 32k` the four
    coordinates of `paSpec` on those values. -/
theorem paShipped_correct_addr (sa : AState)
    (hsep : Separated shippedBank sa.regs paCells)
    (b0 : paInValA sa 0 < 2 ^ 255 - 19) (b1 : paInValA sa 1 < 2 ^ 255 - 19)
    (b2 : paInValA sa 2 < 2 ^ 255 - 19) (b3 : paInValA sa 3 < 2 ^ 255 - 19)
    (b4 : paInValA sa 4 < 2 ^ 255 - 19) (b5 : paInValA sa 5 < 2 ^ 255 - 19)
    (b6 : paInValA sa 6 < 2 ^ 255 - 19) (b7 : paInValA sa 7 < 2 ^ 255 - 19) :
    paOutValA sa 0 = (paSpec (paInValA sa 0) (paInValA sa 1) (paInValA sa 2)
        (paInValA sa 3) (paInValA sa 4) (paInValA sa 5) (paInValA sa 6)
        (paInValA sa 7)).1
      ∧ paOutValA sa 1 = (paSpec (paInValA sa 0) (paInValA sa 1) (paInValA sa 2)
        (paInValA sa 3) (paInValA sa 4) (paInValA sa 5) (paInValA sa 6)
        (paInValA sa 7)).2.1
      ∧ paOutValA sa 2 = (paSpec (paInValA sa 0) (paInValA sa 1) (paInValA sa 2)
        (paInValA sa 3) (paInValA sa 4) (paInValA sa 5) (paInValA sa 6)
        (paInValA sa 7)).2.2.1
      ∧ paOutValA sa 3 = (paSpec (paInValA sa 0) (paInValA sa 1) (paInValA sa 2)
        (paInValA sa 3) (paInValA sa 4) (paInValA sa 5) (paInValA sa 6)
        (paInValA sa 7)).2.2.2 := by
  obtain ⟨-, -, hKc⟩ := runBlockA_simD_on shippedBank ed25519PointAddShippedBlock paCells
    ed25519PointAdd_disciplinedD
    (readsBeforeWritesFromB_of_reads _ (footOK_reads pa_foot) false)
    (footOK_writes pa_foot) sa hsep
  have hdi : shippedBank "%rdi" = some "%rdi" := by simp [shippedBank]
  have hout : ∀ k, k < 4 → paOutValA sa k
      = paOutVal (runBlock (jOf shippedBank sa)
        (canonD shippedBank ed25519PointAddShippedBlock)) k := by
    intro k hk
    simp only [paOutValA, paOutVal]
    refine congrArg bignumVal (List.map_congr_left ?_)
    intro i hi
    simp only [List.mem_range] at hi
    have hmem : ("%rdi", ((8 * (4 * k + i) : Nat) : Int)) ∈ paCells :=
      List.mem_append_left _ (List.mem_append_left _
        (List.mem_map.2 ⟨4 * k + i, List.mem_range.2 (show 4 * k + i < 16 by omega), rfl⟩))
    rw [← hKc _ hmem, absMem_shipped _ _ _ _ hdi]
  have hin : ∀ k, k < 8 → paInValA sa k = paInVal (jOf shippedBank sa) k :=
    fun k hk => paInValA_eq sa k hk
  rw [hin 0 (by omega)] at b0
  rw [hin 1 (by omega)] at b1
  rw [hin 2 (by omega)] at b2
  rw [hin 3 (by omega)] at b3
  rw [hin 4 (by omega)] at b4
  rw [hin 5 (by omega)] at b5
  rw [hin 6 (by omega)] at b6
  rw [hin 7 (by omega)] at b7
  rw [hin 0 (by omega), hin 1 (by omega), hin 2 (by omega), hin 3 (by omega),
    hin 4 (by omega), hin 5 (by omega), hin 6 (by omega), hin 7 (by omega)]
  have hc := paCanon_correct (jOf shippedBank sa) b0 b1 b2 b3 b4 b5 b6 b7
  rw [hout 0 (by omega), hout 1 (by omega), hout 2 (by omega), hout 3 (by omega)]
  exact hc


/-! ## 18. The coordinates of the source formula -/

open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (p25519)
open CatCrypt.Crypto.SecureCompilation.Algebraic.Ed25519PointAdd (addSpec)
open CatCrypt.Util (ed25519D)

theorem cast_mod_p (a : Nat) :
    ((a % (2 ^ 255 - 19) : Nat) : ZMod p25519) = (a : ZMod p25519) :=
  ZMod.natCast_mod a _

theorem cast_sub_p (x : Nat) (h : x ≤ 2 ^ 255 - 19) :
    (((2 ^ 255 - 19 - x : Nat)) : ZMod p25519) = -(x : ZMod p25519) := by
  rw [Nat.cast_sub h]
  show (p25519 : ZMod p25519) - (x : ZMod p25519) = _
  rw [ZMod.natCast_self]
  ring

theorem cast_twoDNat : ((twoDNat : Nat) : ZMod p25519) = ed25519D + ed25519D := by
  decide +kernel


/-- **The natural-number coordinates are the coordinates of `addSpec`.** In `ZMod p25519`
    the four values of `paSpec` are the four coordinates of the extended-coordinate
    addition of `Ed25519PointAddCompile.addSpec` at the curve constant `ed25519D`. -/
theorem paSpec_addSpec (x1 y1 z1 t1 x2 y2 z2 t2 : Nat)
    (hx1 : x1 ≤ 2 ^ 255 - 19) (hx2 : x2 ≤ 2 ^ 255 - 19) :
    (((paSpec x1 y1 z1 t1 x2 y2 z2 t2).1 : Nat) : ZMod p25519)
        = (addSpec ed25519D (x1 : ZMod p25519) (y1 : ZMod p25519) (z1 : ZMod p25519)
          (t1 : ZMod p25519) (x2 : ZMod p25519) (y2 : ZMod p25519) (z2 : ZMod p25519)
          (t2 : ZMod p25519)).1
      ∧ (((paSpec x1 y1 z1 t1 x2 y2 z2 t2).2.1 : Nat) : ZMod p25519)
        = (addSpec ed25519D (x1 : ZMod p25519) (y1 : ZMod p25519) (z1 : ZMod p25519)
          (t1 : ZMod p25519) (x2 : ZMod p25519) (y2 : ZMod p25519) (z2 : ZMod p25519)
          (t2 : ZMod p25519)).2.1
      ∧ (((paSpec x1 y1 z1 t1 x2 y2 z2 t2).2.2.1 : Nat) : ZMod p25519)
        = (addSpec ed25519D (x1 : ZMod p25519) (y1 : ZMod p25519) (z1 : ZMod p25519)
          (t1 : ZMod p25519) (x2 : ZMod p25519) (y2 : ZMod p25519) (z2 : ZMod p25519)
          (t2 : ZMod p25519)).2.2.1
      ∧ (((paSpec x1 y1 z1 t1 x2 y2 z2 t2).2.2.2 : Nat) : ZMod p25519)
        = (addSpec ed25519D (x1 : ZMod p25519) (y1 : ZMod p25519) (z1 : ZMod p25519)
          (t1 : ZMod p25519) (x2 : ZMod p25519) (y2 : ZMod p25519) (z2 : ZMod p25519)
          (t2 : ZMod p25519)).2.2.2 := by
  have hle : ∀ a : Nat, a % (2 ^ 255 - 19) ≤ 2 ^ 255 - 19 := fun a => le_of_lt (mod_lt_p a)
  have hsub : ∀ a : Nat, ((2 ^ 255 - 19 - a % (2 ^ 255 - 19) : Nat) : ZMod p25519)
      = -((a % (2 ^ 255 - 19) : Nat) : ZMod p25519) := fun a => cast_sub_p _ (hle a)
  simp only [paSpec, addSpec]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Nat.cast_mul, Nat.cast_add, cast_mod_p, hsub, cast_sub_p x1 hx1,
      cast_sub_p x2 hx2, cast_twoDNat] <;>
    ring

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519PointAddShippedProof
