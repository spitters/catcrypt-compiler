/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.HeapAbs
public import CatCrypt.Crypto.SecureCompilation.Ascent.EcMultiLimbMul

/-!
# A multi-limb add kernel over the generic value abstraction

_Part of the AutoCorres-in-Lean ascent begun by Sebastian Graf (`sgraf812/ascent`)._

The `n`-limb add-with-carry kernel `adcxBlock (ds.zip ss)` — one `adcx dᵢ sᵢ` per
limb, least significant first — is given a forward simulation whose state relation
is assembled from the generic abstractions of `HeapAbs`: the two register windows
`ds` and `ss` read as their base-`2^64` values through `limbWindowAbs`, paired by
`ValueAbs.pair`, with the carry flag alongside (`SRcarryOf`). The abstract step
`feAddAbs n` adds the two values with the carry-in modulo `2^(64·n)` and writes the
carry-out. No relation and no congruence lemma is written for the kernel; the
value content is the register-fold identity `adcxAbs_window` over the existing
chain leaf `corresJ_adcxChain`.

`feAddN_capstone` is stated for any limb count; `feAdd4_capstone` is its four-limb
(`2^256`) instance, and `feAdd4_capstone_field` reads the result in `ZMod p`
through `limbWindowFieldAbs` when no carry leaves the window.

## Main results

* `adcxAbs_frame`: the `adcx` fold leaves registers outside its destinations alone.
* `adcxAbs_window`: the recomposed destination window after the fold, plus the
  carry-out at weight `2^(64·n)`, equals the sum of the two input windows and the
  carry-in.
* `feAddN_capstone`, `feAdd4_capstone`: the kernel refines `feAddAbs` over
  `SRcarryOf ((limbWindowAbs ds).pair (limbWindowAbs ss))`.
* `feAdd4_capstone_field`: the four-limb window after the kernel refines the field
  sum through `limbWindowFieldAbs` when the sum does not overflow.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## Arithmetic of one add-with-carry limb and of a limb window -/

/-- One add-with-carry limb recomposes: the output word plus the carry-out at
    weight `2^64` is the true sum `x + y + b`. -/
theorem add_carry_recompose (x y : BitVec 64) (b : Bool) :
    (add_carry x y (if b then 1 else 0)).toNat
        + 2 ^ 64 * (if decide (2 ^ 64 ≤ x.toNat + y.toNat + (if b then 1 else 0)) then 1 else 0)
      = x.toNat + y.toNat + (if b then 1 else 0) := by
  have hx := x.isLt
  have hy := y.isLt
  have hval : (add_carry x y (if b then 1 else 0)).toNat
      = (x.toNat + y.toNat + (if b then 1 else 0)) % 2 ^ 64 := by
    rw [add_carry, BitVec.toNat_ofNat]
  have hc : (if b then 1 else 0 : ℕ) ≤ 1 := by cases b <;> simp
  rw [hval]
  generalize (if b then 1 else 0 : ℕ) = c at hc ⊢
  by_cases h : 2 ^ 64 ≤ x.toNat + y.toNat + c
  · rw [decide_eq_true h, if_pos rfl]; omega
  · rw [decide_eq_false h]; simp only [Bool.false_eq_true, ↓reduceIte]; omega

/-- The base-`2^64` recomposition of a limb list is below `2^(64·length)`. -/
theorem limbVal_lt : ∀ l : List (BitVec 64), limbVal l < 2 ^ (64 * l.length)
  | [] => by simp [limbVal]
  | x :: xs => by
      have ih := limbVal_lt xs
      have hx := x.isLt
      rw [limbVal, List.length_cons, Nat.mul_succ, pow_add]
      omega

/-! ## The `adcx` fold on a register window -/

/-- Registers outside the destination list are untouched by the `adcx` fold. -/
theorem adcxAbs_frame : ∀ (pairs : List (String × String)) (a : ACarry) (r : String),
    r ∉ pairs.map Prod.fst → (adcxAbs pairs a).regs r = a.regs r
  | [], _, _, _ => rfl
  | (d, s) :: ps, a, r, hr => by
      have hrd : r ≠ d := fun h => hr (by simp [h])
      have hrs : r ∉ ps.map Prod.fst := fun h => hr (List.mem_cons_of_mem _ h)
      rw [adcxAbs, adcxAbs_frame ps _ r hrs]
      simp [adcStep, hrd]

/-- The recomposed destination window after the `adcx` fold, plus the carry-out at
    weight `2^(64·n)`, equals the sum of the two input windows and the carry-in.
    Destinations are pairwise distinct and disjoint from the sources. -/
theorem adcxAbs_window : ∀ (ds ss : List String) (a : ACarry),
    ds.length = ss.length → ds.Nodup → (∀ r ∈ ds, r ∉ ss) →
    limbVal (ds.map (adcxAbs (ds.zip ss) a).regs)
        + 2 ^ (64 * ds.length) * (if (adcxAbs (ds.zip ss) a).cf then 1 else 0)
      = limbVal (ds.map a.regs) + limbVal (ss.map a.regs) + (if a.cf then 1 else 0)
  | [], [], a, _, _, _ => by simp [limbVal, adcxAbs]
  | [], _ :: _, _, h, _, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | d :: ds, s :: ss, a, hlen, hnd, hdisj => by
      have hlen' : ds.length = ss.length := by simpa using hlen
      have hnd' : ds.Nodup := hnd.of_cons
      have hdnot : d ∉ ds := (List.nodup_cons.mp hnd).1
      have hdisj' : ∀ r ∈ ds, r ∉ ss := fun r hr hrs =>
        hdisj r (List.mem_cons_of_mem _ hr) (List.mem_cons_of_mem _ hrs)
      have hds : d ∉ ss := fun h => hdisj d (List.mem_cons_self) (List.mem_cons_of_mem _ h)
      have hdss : d ≠ s := fun h => hdisj d (List.mem_cons_self) (h ▸ List.mem_cons_self)
      have ih := adcxAbs_window ds ss (adcStep d s a) hlen' hnd' hdisj'
      -- the later limbs read the stepped state as `a` on every name other than `d`
      have hmapd : ds.map (adcStep d s a).regs = ds.map a.regs :=
        List.map_congr_left fun r hr => by
          simp [adcStep, show r ≠ d from fun h => hdnot (h ▸ hr)]
      have hmaps : ss.map (adcStep d s a).regs = ss.map a.regs :=
        List.map_congr_left fun r hr => by
          simp [adcStep, show r ≠ d from fun h => hds (h ▸ hr)]
      -- the head limb is written once and then framed
      have hhead : (adcxAbs ((d, s) :: ds.zip ss) a).regs d
          = add_carry (a.regs d) (a.regs s) (if a.cf then 1 else 0) := by
        rw [adcxAbs, adcxAbs_frame (ds.zip ss) (adcStep d s a) d
          (by rw [List.map_fst_zip hlen'.le]; exact hdnot)]
        simp [adcStep]
      have hcf : (adcStep d s a).cf = decide (2 ^ 64 ≤ (a.regs d).toNat + (a.regs s).toNat
          + (if a.cf then 1 else 0)) := rfl
      have hrec := add_carry_recompose (a.regs d) (a.regs s) a.cf
      rw [List.zip_cons_cons, List.map_cons, List.map_cons, List.map_cons, limbVal, limbVal,
        limbVal, hhead, adcxAbs, List.length_cons, Nat.mul_succ, pow_add]
      rw [hmapd, hmaps] at ih
      rw [← hcf] at hrec
      have hb0 : (if a.cf then 1 else 0 : ℕ) ≤ 1 := by cases a.cf <;> simp
      have hb1 : (if (adcStep d s a).cf then 1 else 0 : ℕ) ≤ 1 := by
        cases (adcStep d s a).cf <;> simp
      generalize (if a.cf then 1 else 0 : ℕ) = b0 at ih hrec hb0 ⊢
      generalize (if (adcStep d s a).cf then 1 else 0 : ℕ) = b1 at ih hrec hb1 ⊢
      generalize limbVal (ds.map (adcxAbs (ds.zip ss) (adcStep d s a)).regs) = W at ih ⊢
      generalize limbVal (ds.map a.regs) = X at ih ⊢
      generalize limbVal (ss.map a.regs) = Y at ih ⊢
      generalize (2 : ℕ) ^ (64 * ds.length) = K at ih ⊢
      generalize (adcxAbs (ds.zip ss) (adcStep d s a)).cf = c at ih ⊢
      cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at ih ⊢ <;> omega

/-! ## The capstone over the generic abstraction -/

/-- The abstract `n`-limb add step on `((x, y), cf)`: `x := (x + y + cf) mod 2^(64·n)`,
    `y` unchanged, `cf :=` the carry-out. -/
def feAddAbs (n : ℕ) (a : (ℕ × ℕ) × Bool) : (ℕ × ℕ) × Bool :=
  (((a.1.1 + a.1.2 + (if a.2 then 1 else 0)) % 2 ^ (64 * n), a.1.2),
    decide (2 ^ (64 * n) ≤ a.1.1 + a.1.2 + (if a.2 then 1 else 0)))

/-- **The `n`-limb add capstone.** The kernel `adcxBlock (ds.zip ss)` refines
    `feAddAbs ds.length` over the state relation assembled from the generic
    abstractions: the windows `ds` and `ss` read through `limbWindowAbs`, paired,
    with the carry flag. Destinations are pairwise distinct and disjoint from the
    sources. -/
theorem feAddN_capstone (ds ss : List String) (hlen : ds.length = ss.length)
    (hnd : ds.Nodup) (hdisj : ∀ r ∈ ds, r ∉ ss) :
    CorresJ (SRcarryOf ((limbWindowAbs ds).pair (limbWindowAbs ss))) (fun _ => True)
      (feAddAbs ds.length) (adcxBlock (ds.zip ss)) := by
  intro st a hSR _
  obtain ⟨⟨hx, hy⟩, hcf⟩ := hSR
  obtain ⟨hr, hc⟩ := corresJ_adcxChain (ds.zip ss) st ⟨st.regs, a.2⟩ ⟨fun _ => rfl, hcf⟩ trivial
  set a₀ : ACarry := ⟨st.regs, a.2⟩ with ha₀
  have hregs : (runBlock st (adcxBlock (ds.zip ss))).regs = (adcxAbs (ds.zip ss) a₀).regs :=
    funext hr
  have hwin := adcxAbs_window ds ss a₀ hlen hnd hdisj
  have hlt := limbVal_lt (ds.map (adcxAbs (ds.zip ss) a₀).regs)
  rw [List.length_map] at hlt
  change limbVal (ds.map st.regs) = a.1.1 at hx
  change limbVal (ss.map st.regs) = a.1.2 at hy
  rw [hx, hy] at hwin
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- the destination window is the modular sum
    change limbVal (ds.map (runBlock st (adcxBlock (ds.zip ss))).regs) = _
    rw [hregs]
    show _ = (a.1.1 + a.1.2 + (if a.2 then 1 else 0)) % 2 ^ (64 * ds.length)
    rw [← hwin, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · -- the source window is framed
    change limbVal (ss.map (runBlock st (adcxBlock (ds.zip ss))).regs) = a.1.2
    rw [hregs, ← hy]
    congr 1
    refine List.map_congr_left fun r hr => adcxAbs_frame _ _ r ?_
    rw [List.map_fst_zip hlen.le]
    exact fun h => hdisj r h hr
  · -- the carry-out
    show _ = decide (2 ^ (64 * ds.length) ≤ a.1.1 + a.1.2 + (if a.2 then 1 else 0))
    rw [hc]
    rw [← hwin]
    generalize limbVal (ds.map (adcxAbs (ds.zip ss) a₀).regs) = W at hlt
    generalize (2 : ℕ) ^ (64 * ds.length) = K at hlt
    cases (adcxAbs (ds.zip ss) a₀).cf
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
      exact (decide_eq_false (by omega)).symm
    · simp only [↓reduceIte, Nat.mul_one]
      exact (decide_eq_true (by omega)).symm

/-- **The four-limb add capstone** (`2^256`): `feAddN_capstone` at the register
    windows `[d0, d1, d2, d3]` and `[s0, s1, s2, s3]`. -/
theorem feAdd4_capstone (d0 d1 d2 d3 s0 s1 s2 s3 : String)
    (hnd : [d0, d1, d2, d3].Nodup) (hdisj : ∀ r ∈ [d0, d1, d2, d3], r ∉ [s0, s1, s2, s3]) :
    CorresJ (SRcarryOf ((limbWindowAbs [d0, d1, d2, d3]).pair (limbWindowAbs [s0, s1, s2, s3])))
      (fun _ => True) (feAddAbs 4)
      [.adcx d0 (.reg s0), .adcx d1 (.reg s1), .adcx d2 (.reg s2), .adcx d3 (.reg s3)] :=
  feAddN_capstone [d0, d1, d2, d3] [s0, s1, s2, s3] rfl hnd hdisj

/-- **The four-limb add capstone in the field.** When the carry-in is clear and the
    sum does not overflow `2^256`, the destination window after the kernel refines
    the field sum `(x + y : ZMod p)` through `limbWindowFieldAbs`. -/
theorem feAdd4_capstone_field (p : ℕ) (d0 d1 d2 d3 s0 s1 s2 s3 : String)
    (hnd : [d0, d1, d2, d3].Nodup) (hdisj : ∀ r ∈ [d0, d1, d2, d3], r ∉ [s0, s1, s2, s3])
    (st : JState 64) (x y : ℕ)
    (hSR : SRcarryOf ((limbWindowAbs [d0, d1, d2, d3]).pair (limbWindowAbs [s0, s1, s2, s3]))
      st ((x, y), false))
    (hsum : x + y < 2 ^ (64 * 4)) :
    (limbWindowFieldAbs [d0, d1, d2, d3] p).Refines
      (runBlock st [.adcx d0 (.reg s0), .adcx d1 (.reg s1), .adcx d2 (.reg s2), .adcx d3 (.reg s3)]).regs
      ((x : ZMod p) + (y : ZMod p)) := by
  have h := feAdd4_capstone d0 d1 d2 d3 s0 s1 s2 s3 hnd hdisj st ((x, y), false) hSR trivial
  obtain ⟨⟨hx, _⟩, _⟩ := h
  refine ⟨x + y, ?_, ?_⟩
  · change limbVal _ = x + y
    change limbVal _ = (x + y + 0) % 2 ^ (64 * 4) at hx
    rw [hx, Nat.add_zero, Nat.mod_eq_of_lt hsum]
  · show ((x + y : ℕ) : ZMod p) = (x : ZMod p) + (y : ZMod p)
    push_cast
    rfl

end CatCrypt.Crypto.SecureCompilation.Ascent
