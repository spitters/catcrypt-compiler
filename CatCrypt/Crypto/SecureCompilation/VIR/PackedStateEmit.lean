/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.RangeDomain
public import CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric
public import Mathlib.Data.ZMod.Basic

/-!
# A packed-state IR: one sixteen-lane state per vector register

The IR of a program that keeps one state of sixteen 32-bit words in one vector register
and computes on it with lane-wise modular arithmetic, lane permutations and lane blends
(superword-level parallelism within one program). A program is a straight-line list of
instructions over the registers `PReg = Fin 24`; each instruction writes one register.
The instructions are

* `cst d c`: the constant vector `c`;
* `mov d a`: a copy;
* `add d a b`, `sub d a b`, `mul d a b`: lane-wise modular sum, difference and
  Montgomery product;
* `perm d a idx`: lane `j` of `d` is lane `idx j` of `a` (a lane permutation, or any
  lane gather, by a constant index vector);
* `blend d a b m`: lane `j` of `d` is lane `j` of `a` where `m j` holds, else lane `j`
  of `b` (a constant mask).

`exec A` runs a program over any lane algebra `A` (`LaneAlg`): a value type with a sum,
a difference, a product and the reading of a constant word. Two instances matter:

* `wordAlg mp`: 32-bit words, the sum `maddW`, difference `msubW` and Montgomery
  product `mmulW` modulo `p` with radix `2^32`, each computed with an unsigned minimum
  in place of the conditional correction (the forms the vector machine computes);
* `fieldAlg mp`: `ZMod p`, reading a constant word `w` as `w · 2^-32`.

`exec_sim` states that on the Montgomery forms `enc p x = x · 2^32 mod p` the two runs
agree: when every register the program reads before writing holds the Montgomery form of
a field vector, every register it defines holds the Montgomery form of the field run's
value. The definedness side is the Boolean check `defRun`; the constants must be words
below `p` (`CstBelow`).

## Main definitions

* `PReg`, `PInstr`, `LaneAlg`, `Regs`, `PInstr.step`, `exec`: the IR and its run.
* `MontParams`, `MontParams.Valid`, `maddW`, `msubW`, `mmulW`, `wordAlg`: the word
  semantics.
* `enc`, `fieldAlg`: the Montgomery form and the field semantics.
* `defRun`, `CstBelow`: the definedness check and the constant range condition.

## Main results

* `exec_append`, `exec_preserve`: the run of a concatenation; registers a program does
  not write keep their value.
* `maddW_enc`, `msubW_enc`, `mmulW_enc`, `enc_dec`: the word operations realize the
  field operations on Montgomery forms.
* `dec_enc`, `ofNat_val_eq_enc`: the field reading of a Montgomery form; the canonical
  word of `x` is the Montgomery form of `x · 2^-32`.
* `exec_sim`: the word run on Montgomery forms is the Montgomery form of the field run.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.PackedStateEmit

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (mulHiW)
open CatCrypt.Crypto.SecureCompilation.RangeDomain (umin)
open CatCrypt.Crypto.Optimizer.Rewrite.MontgomeryRedcGeneric (redcSub_lt redcSub_mul_R_modEq)

/-! ## 1. The IR and its run over a lane algebra -/

/-- The registers of the packed-state IR. -/
abbrev PReg := Fin 24

/-- A packed-state instruction; each writes its destination `d`. -/
inductive PInstr where
  /-- The constant vector `c`. -/
  | cst (d : PReg) (c : Fin 16 → BitVec 32)
  /-- A copy of `a`. -/
  | mov (d a : PReg)
  /-- The lane-wise sum. -/
  | add (d a b : PReg)
  /-- The lane-wise difference. -/
  | sub (d a b : PReg)
  /-- The lane-wise product. -/
  | mul (d a b : PReg)
  /-- Lane `j` is lane `idx j` of `a`. -/
  | perm (d a : PReg) (idx : Fin 16 → Fin 16)
  /-- Lane `j` is lane `j` of `a` where `m j`, else lane `j` of `b`. -/
  | blend (d a b : PReg) (m : Fin 16 → Bool)

/-- The register an instruction writes. -/
def PInstr.dst : PInstr → PReg
  | .cst d _ => d
  | .mov d _ => d
  | .add d _ _ => d
  | .sub d _ _ => d
  | .mul d _ _ => d
  | .perm d _ _ => d
  | .blend d _ _ _ => d

/-- The registers an instruction reads. -/
def PInstr.srcs : PInstr → List PReg
  | .cst _ _ => []
  | .mov _ a => [a]
  | .add _ a b => [a, b]
  | .sub _ a b => [a, b]
  | .mul _ a b => [a, b]
  | .perm _ a _ => [a]
  | .blend _ a b _ => [a, b]

/-- A lane algebra: the value type of one lane, its sum, difference and product, and the
    value a constant word denotes. -/
structure LaneAlg (α : Type) where
  /-- The sum. -/
  add : α → α → α
  /-- The difference. -/
  sub : α → α → α
  /-- The product. -/
  mul : α → α → α
  /-- The value of a constant word. -/
  cst : BitVec 32 → α

/-- A register file: sixteen lanes per register. -/
abbrev Regs (α : Type) := PReg → Fin 16 → α

/-- The vector an instruction computes. -/
def PInstr.val {α : Type} (A : LaneAlg α) (R : Regs α) : PInstr → Fin 16 → α
  | .cst _ c => fun j => A.cst (c j)
  | .mov _ a => R a
  | .add _ a b => fun j => A.add (R a j) (R b j)
  | .sub _ a b => fun j => A.sub (R a j) (R b j)
  | .mul _ a b => fun j => A.mul (R a j) (R b j)
  | .perm _ a idx => fun j => R a (idx j)
  | .blend _ a b m => fun j => if m j then R a j else R b j

/-- One instruction: its destination set to the vector it computes. -/
def PInstr.step {α : Type} (A : LaneAlg α) (R : Regs α) (i : PInstr) : Regs α :=
  Function.update R i.dst (i.val A R)

/-- The run of a program. -/
def exec {α : Type} (A : LaneAlg α) : List PInstr → Regs α → Regs α
  | [], R => R
  | i :: is, R => exec A is (i.step A R)

@[simp] theorem exec_nil {α : Type} (A : LaneAlg α) (R : Regs α) : exec A [] R = R := rfl

@[simp] theorem exec_cons {α : Type} (A : LaneAlg α) (i : PInstr) (is : List PInstr)
    (R : Regs α) : exec A (i :: is) R = exec A is (i.step A R) := rfl

/-- The run of a concatenation is the run of the second part after the first. -/
theorem exec_append {α : Type} (A : LaneAlg α) :
    ∀ (p q : List PInstr) (R : Regs α), exec A (p ++ q) R = exec A q (exec A p R)
  | [], _, _ => rfl
  | i :: is, q, R => exec_append A is q (i.step A R)

/-- A register no instruction of the program writes keeps its value. -/
theorem exec_preserve {α : Type} (A : LaneAlg α) :
    ∀ (p : List PInstr) (R : Regs α) (r : PReg), (∀ i ∈ p, i.dst ≠ r) → exec A p R r = R r
  | [], _, _, _ => rfl
  | i :: is, R, r, h => by
    rw [exec_cons, exec_preserve A is _ r (fun i' hi' => h i' (List.mem_cons_of_mem _ hi'))]
    exact Function.update_of_ne (h i List.mem_cons_self).symm _ _

/-! ## 2. The word semantics -/

/-- The parameters of Montgomery arithmetic modulo `p` with radix `2^32`: the modulus,
    `mu = p⁻¹ mod 2^32` and `rinv = 2^-32 mod p`. -/
structure MontParams where
  /-- The modulus. -/
  p : Nat
  /-- `p⁻¹ mod 2^32`. -/
  mu : Nat
  /-- `2^-32 mod p`. -/
  rinv : Nat

/-- The conditions the word semantics needs: `0 < p < 2^31`, `mu · p ≡ 1 mod 2^32`
    with `mu < 2^32`, and `2^32 · rinv ≡ 1 mod p`. -/
structure MontParams.Valid (mp : MontParams) : Prop where
  p_pos : 0 < mp.p
  p_lt : mp.p < 2 ^ 31
  mu_lt : mp.mu < 2 ^ 32
  mu_mul : mp.mu * mp.p % 2 ^ 32 = 1
  rinv_mul : 2 ^ 32 * mp.rinv % mp.p = 1

/-- The modular sum on words below `p`: `min(a + b, a + b − p)`, unsigned. -/
def maddW (p a b : BitVec 32) : BitVec 32 := umin (a + b) (a + b - p)

/-- The modular difference on words below `p`: `min(a − b, a − b + p)`, unsigned. -/
def msubW (p a b : BitVec 32) : BitVec 32 := umin (a - b) (a - b + p)

/-- The Montgomery product on words below `p`: with `d = hi(a·b) − hi(lo(a·b)·mu·p)`,
    `min(d, d + p)`, unsigned. -/
def mmulW (p mu a b : BitVec 32) : BitVec 32 :=
  umin (mulHiW a b - mulHiW (a * b * mu) p) (mulHiW a b - mulHiW (a * b * mu) p + p)

/-- The word semantics: the modular sum and difference and the Montgomery product modulo
    `mp.p`; a constant is its word. -/
def wordAlg (mp : MontParams) : LaneAlg (BitVec 32) where
  add := maddW (BitVec.ofNat 32 mp.p)
  sub := msubW (BitVec.ofNat 32 mp.p)
  mul := mmulW (BitVec.ofNat 32 mp.p) (BitVec.ofNat 32 mp.mu)
  cst := id

/-- The Montgomery form of `x : ZMod p` as a word: `x.val · 2^32 mod p`. -/
def enc (p : Nat) (x : ZMod p) : BitVec 32 := BitVec.ofNat 32 ((x.val * 2 ^ 32) % p)

/-- The field semantics: `ZMod p`, a constant word `w` read as `w · 2^-32`. -/
def fieldAlg (mp : MontParams) : LaneAlg (ZMod mp.p) where
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  cst := fun w => (w.toNat : ZMod mp.p) * (mp.rinv : ZMod mp.p)

/-! ## 3. The word operations realize the field operations -/

section Words

variable {mp : MontParams} (hv : mp.Valid)
include hv

theorem MontParams.Valid.pW_toNat : (BitVec.ofNat 32 mp.p).toNat = mp.p := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by have := hv.p_lt; omega)

theorem MontParams.Valid.muW_toNat : (BitVec.ofNat 32 mp.mu).toNat = mp.mu := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hv.mu_lt

theorem MontParams.Valid.neZero : NeZero mp.p := ⟨by have := hv.p_pos; omega⟩

theorem MontParams.Valid.one_lt : 1 < mp.p := by
  rcases Nat.lt_or_ge 1 mp.p with h | h
  · exact h
  · have h' := hv.rinv_mul
    have e : mp.p = 1 := by have := hv.p_pos; omega
    rw [e, Nat.mod_one] at h'
    exact absurd h' (by norm_num)

theorem enc_toNat (x : ZMod mp.p) : (enc mp.p x).toNat = (x.val * 2 ^ 32) % mp.p := by
  have := hv.p_pos
  have := hv.p_lt
  unfold enc
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by omega)) (by omega))

theorem enc_lt (x : ZMod mp.p) : (enc mp.p x).toNat < mp.p := by
  have := hv.p_pos
  rw [enc_toNat hv]; exact Nat.mod_lt _ (by omega)

/-- The Montgomery form cast back to `ZMod p` is `x · 2^32`. -/
theorem enc_cast (x : ZMod mp.p) :
    (((enc mp.p x).toNat : Nat) : ZMod mp.p) = x * (2 ^ 32 : ZMod mp.p) := by
  haveI := hv.neZero
  rw [enc_toNat hv, ZMod.natCast_mod]
  rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_pow, Nat.cast_ofNat]

/-- A word below `p` whose cast is `x · 2^32` is the Montgomery form of `x`. -/
theorem eq_enc (w : BitVec 32) (x : ZMod mp.p) (hw : w.toNat < mp.p)
    (hc : ((w.toNat : Nat) : ZMod mp.p) = x * (2 ^ 32 : ZMod mp.p)) : w = enc mp.p x := by
  haveI := hv.neZero
  apply BitVec.eq_of_toNat_eq
  have h1 : w.toNat = ((w.toNat : Nat) : ZMod mp.p).val := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hw]
  have h2 : (enc mp.p x).toNat = ((((enc mp.p x).toNat : Nat) : ZMod mp.p)).val := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (enc_lt hv x)]
  rw [h1, h2, hc, enc_cast hv]

/-- `2^32 · rinv = 1` in `ZMod p`. -/
theorem R_mul_rinv : (2 ^ 32 : ZMod mp.p) * (mp.rinv : ZMod mp.p) = 1 := by
  have h : ((2 ^ 32 * mp.rinv : Nat) : ZMod mp.p) = ((1 : Nat) : ZMod mp.p) := by
    rw [ZMod.natCast_eq_natCast_iff', hv.rinv_mul, Nat.mod_eq_of_lt hv.one_lt]
  rwa [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at h

/-- The field reading of a Montgomery form is the element. -/
theorem dec_enc (x : ZMod mp.p) :
    ((enc mp.p x).toNat : ZMod mp.p) * (mp.rinv : ZMod mp.p) = x := by
  rw [enc_cast hv, mul_assoc, R_mul_rinv hv, mul_one]

/-- The canonical word of `x` is the Montgomery form of `x · 2^-32`. -/
theorem ofNat_val_eq_enc (x : ZMod mp.p) :
    BitVec.ofNat 32 x.val = enc mp.p (x * (mp.rinv : ZMod mp.p)) := by
  haveI := hv.neZero
  have hx : x.val < 2 ^ 32 := lt_trans (ZMod.val_lt x) (by have := hv.p_lt; omega)
  apply eq_enc hv
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]; exact ZMod.val_lt x
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, ZMod.natCast_zmod_val, mul_assoc,
      mul_comm (mp.rinv : ZMod mp.p), R_mul_rinv hv, mul_one]

/-- A constant word below `p` is the Montgomery form of its field reading. -/
theorem enc_dec (w : BitVec 32) (hw : w.toNat < mp.p) :
    enc mp.p ((w.toNat : ZMod mp.p) * (mp.rinv : ZMod mp.p)) = w := by
  refine (eq_enc hv w _ hw ?_).symm
  rw [mul_assoc, mul_comm (mp.rinv : ZMod mp.p), R_mul_rinv hv, mul_one]

/-- The modular sum of two words below `p`. -/
theorem maddW_toNat (a b : BitVec 32) (ha : a.toNat < mp.p) (hb : b.toNat < mp.p) :
    (maddW (BitVec.ofNat 32 mp.p) a b).toNat = (a.toNat + b.toNat) % mp.p := by
  have hp := hv.p_lt
  have hP := hv.pW_toNat
  unfold maddW umin
  have hab : (a + b).toNat = a.toNat + b.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  by_cases hge : mp.p ≤ a.toNat + b.toNat
  · have hs : (a + b - BitVec.ofNat 32 mp.p).toNat = a.toNat + b.toNat - mp.p := by
      rw [BitVec.toNat_sub, hab, hP]; omega
    rw [ite_eq_right (by omega), hs]
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
  · have hs : (a + b - BitVec.ofNat 32 mp.p).toNat = a.toNat + b.toNat + 2 ^ 32 - mp.p := by
      rw [BitVec.toNat_sub, hab, hP]; omega
    rw [ite_eq_left (by omega), hab, Nat.mod_eq_of_lt (by omega)]

/-- The modular difference of two words below `p`. -/
theorem msubW_toNat (a b : BitVec 32) (ha : a.toNat < mp.p) (hb : b.toNat < mp.p) :
    (msubW (BitVec.ofNat 32 mp.p) a b).toNat
      = if b.toNat ≤ a.toNat then a.toNat - b.toNat else a.toNat + mp.p - b.toNat := by
  have hp := hv.p_lt
  have hP := hv.pW_toNat
  unfold msubW umin
  by_cases hle : b.toNat ≤ a.toNat
  · have h1 : (a - b).toNat = a.toNat - b.toNat := by rw [BitVec.toNat_sub]; omega
    have h2 : (a - b + BitVec.ofNat 32 mp.p).toNat = a.toNat - b.toNat + mp.p := by
      rw [BitVec.toNat_add, h1, hP]; omega
    rw [ite_eq_left (by omega), ite_eq_left hle, h1]
  · have h1 : (a - b).toNat = a.toNat + 2 ^ 32 - b.toNat := by rw [BitVec.toNat_sub]; omega
    have h2 : (a - b + BitVec.ofNat 32 mp.p).toNat = a.toNat + mp.p - b.toNat := by
      rw [BitVec.toNat_add, h1, hP]; omega
    rw [ite_eq_right (by omega), ite_eq_right hle, h2]

/-- The unsigned minimum `min(h − u, h − u + p)` for `h, u < p`. -/
theorem uminSub_toNat (h u : BitVec 32) (hh : h.toNat < mp.p) (hu : u.toNat < mp.p) :
    (umin (h - u) (h - u + BitVec.ofNat 32 mp.p)).toNat
      = if u.toNat ≤ h.toNat then h.toNat - u.toNat else h.toNat + mp.p - u.toNat := by
  have e := msubW_toNat hv h u hh hu
  unfold msubW at e
  exact e

/-- **Montgomery reduction, value level.** For `A, B < p`, with `lo = A·B mod 2^32`,
    `hi = A·B / 2^32`, `m = lo·mu mod 2^32` and `u = m·p / 2^32`: `hi, u < p` and
    `(hi − u) · 2^32 = A·B` in `ZMod p`. -/
theorem montRedc_nat (A B : Nat) (hA : A < mp.p) (hB : B < mp.p) :
    A * B / 2 ^ 32 < mp.p ∧ ((A * B % 2 ^ 32) * mp.mu % 2 ^ 32) * mp.p / 2 ^ 32 < mp.p ∧
    (((A * B / 2 ^ 32 : Nat) : ZMod mp.p)
        - ((((A * B % 2 ^ 32) * mp.mu % 2 ^ 32) * mp.p / 2 ^ 32 : Nat) : ZMod mp.p))
      * (2 ^ 32 : ZMod mp.p) = (A : ZMod mp.p) * (B : ZMod mp.p) := by
  have hp := hv.p_lt
  have hμ : mp.mu * mp.p ≡ 1 [MOD 2 ^ 32] := by unfold Nat.ModEq; rw [hv.mu_mul]; rfl
  have hT : A * B < mp.p * 2 ^ 32 :=
    lt_of_lt_of_le (Nat.mul_lt_mul'' hA hB) (Nat.mul_le_mul_left _ (by omega))
  obtain ⟨h1, h2⟩ := redcSub_lt mp.p (2 ^ 32) mp.mu (A * B) (by norm_num) hv.p_pos hT
  refine ⟨h1, h2, ?_⟩
  have h := (ZMod.intCast_eq_intCast_iff _ _ mp.p).mpr
    (redcSub_mul_R_modEq mp.p (2 ^ 32) mp.mu (A * B) hμ)
  have hR : (((2 ^ 32 : Nat) : Int) : ZMod mp.p) = (2 ^ 32 : ZMod mp.p) := by
    rw [Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat]
  simp only [Int.cast_mul, Int.cast_sub, hR, Int.cast_natCast, Nat.cast_mul] at h
  exact h

/-- The Montgomery product of two words below `p`, as a natural number. -/
theorem mmulW_toNat (a b : BitVec 32) (ha : a.toNat < mp.p) (hb : b.toNat < mp.p) :
    (mmulW (BitVec.ofNat 32 mp.p) (BitVec.ofNat 32 mp.mu) a b).toNat
      = (if ((a.toNat * b.toNat % 2 ^ 32) * mp.mu % 2 ^ 32) * mp.p / 2 ^ 32
            ≤ a.toNat * b.toNat / 2 ^ 32
          then a.toNat * b.toNat / 2 ^ 32
            - ((a.toNat * b.toNat % 2 ^ 32) * mp.mu % 2 ^ 32) * mp.p / 2 ^ 32
          else a.toNat * b.toNat / 2 ^ 32 + mp.p
            - ((a.toNat * b.toNat % 2 ^ 32) * mp.mu % 2 ^ 32) * mp.p / 2 ^ 32) := by
  have hp := hv.p_lt
  obtain ⟨hhi, hu, -⟩ := montRedc_nat hv a.toNat b.toNat ha hb
  have hhiW : (mulHiW a b).toNat = a.toNat * b.toNat / 2 ^ 32 := by
    unfold mulHiW; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have huW : (mulHiW (a * b * BitVec.ofNat 32 mp.mu) (BitVec.ofNat 32 mp.p)).toNat
      = ((a.toNat * b.toNat % 2 ^ 32) * mp.mu % 2 ^ 32) * mp.p / 2 ^ 32 := by
    unfold mulHiW
    rw [BitVec.toNat_ofNat, BitVec.toNat_mul, BitVec.toNat_mul, hv.muW_toNat, hv.pW_toNat]
    exact Nat.mod_eq_of_lt (by omega)
  unfold mmulW
  rw [uminSub_toNat hv _ _ (by rw [hhiW]; exact hhi) (by rw [huW]; exact hu), hhiW, huW]

/-- **The modular sum realizes the field sum on Montgomery forms.** -/
theorem maddW_enc (x y : ZMod mp.p) :
    maddW (BitVec.ofNat 32 mp.p) (enc mp.p x) (enc mp.p y) = enc mp.p (x + y) := by
  have hA := enc_lt hv x
  have hB := enc_lt hv y
  apply eq_enc hv
  · rw [maddW_toNat hv _ _ hA hB]; exact Nat.mod_lt _ hv.p_pos
  · rw [maddW_toNat hv _ _ hA hB, ZMod.natCast_mod, Nat.cast_add, enc_cast hv, enc_cast hv]
    ring

/-- **The modular difference realizes the field difference on Montgomery forms.** -/
theorem msubW_enc (x y : ZMod mp.p) :
    msubW (BitVec.ofNat 32 mp.p) (enc mp.p x) (enc mp.p y) = enc mp.p (x - y) := by
  have hA := enc_lt hv x
  have hB := enc_lt hv y
  apply eq_enc hv
  · rw [msubW_toNat hv _ _ hA hB]; split <;> omega
  · rw [msubW_toNat hv _ _ hA hB, sub_mul, ← enc_cast hv, ← enc_cast hv]
    split
    · rw [Nat.cast_sub (by assumption)]
    · rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]

/-- **The Montgomery product realizes the field product on Montgomery forms.** -/
theorem mmulW_enc (x y : ZMod mp.p) :
    mmulW (BitVec.ofNat 32 mp.p) (BitVec.ofNat 32 mp.mu) (enc mp.p x) (enc mp.p y)
      = enc mp.p (x * y) := by
  have hAP : (enc mp.p x).toNat < mp.p := enc_lt hv x
  have hBP : (enc mp.p y).toNat < mp.p := enc_lt hv y
  obtain ⟨hhi, hu, hcong⟩ := montRedc_nat hv _ _ hAP hBP
  apply eq_enc hv
  · rw [mmulW_toNat hv _ _ hAP hBP]
    split <;> omega
  · rw [mmulW_toNat hv _ _ hAP hBP]
    have hxy : ((enc mp.p x).toNat : ZMod mp.p) * ((enc mp.p y).toNat : ZMod mp.p)
        = x * y * (2 ^ 32 : ZMod mp.p) * (2 ^ 32 : ZMod mp.p) := by
      rw [enc_cast hv, enc_cast hv]; ring
    have key : (((enc mp.p x).toNat * (enc mp.p y).toNat / 2 ^ 32 : Nat) : ZMod mp.p)
        - (((((enc mp.p x).toNat * (enc mp.p y).toNat % 2 ^ 32) * mp.mu % 2 ^ 32) * mp.p
            / 2 ^ 32 : Nat) : ZMod mp.p)
        = x * y * (2 ^ 32 : ZMod mp.p) := by
      have h := congrArg (· * (mp.rinv : ZMod mp.p)) (hcong.trans hxy)
      simp only [mul_assoc _ (2 ^ 32 : ZMod mp.p) (mp.rinv : ZMod mp.p), R_mul_rinv hv,
        mul_one] at h
      exact h
    rw [← key]
    split
    · rw [Nat.cast_sub (by assumption)]
    · rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]

end Words

/-! ## 4. Definedness and the simulation of the field run -/

/-- One definedness step: the instruction's sources must be defined, and then its
    destination is. -/
def defStep (D : PReg → Bool) (i : PInstr) : Option (PReg → Bool) :=
  if i.srcs.all D then some (Function.update D i.dst true) else none

/-- The definedness check of a program from the defined registers `D`: `none` when an
    instruction reads a register not defined before it, else the registers defined at
    the end. -/
def defRun : (PReg → Bool) → List PInstr → Option (PReg → Bool)
  | D, [] => some D
  | D, i :: is => (defStep D i).bind fun D' => defRun D' is

/-- A constant instruction's words lie below `p`. -/
def CstBelow (p : Nat) : PInstr → Prop
  | .cst _ c => ∀ j, (c j).toNat < p
  | _ => True

/-- One instruction preserves the Montgomery-form relation on the defined registers. -/
theorem step_sim {mp : MontParams} (hv : mp.Valid) (i : PInstr) (hc : CstBelow mp.p i)
    (D D' : PReg → Bool) (hd : defStep D i = some D') (W : Regs (BitVec 32))
    (R : Regs (ZMod mp.p)) (hW : ∀ r, D r = true → W r = fun j => enc mp.p (R r j)) :
    ∀ r, D' r = true →
      i.step (wordAlg mp) W r = fun j => enc mp.p (i.step (fieldAlg mp) R r j) := by
  unfold defStep at hd
  split at hd
  · rename_i hs
    cases hd
    have hsrc : ∀ a ∈ i.srcs, W a = fun j => enc mp.p (R a j) :=
      fun a ha => hW a (List.all_eq_true.mp hs a ha)
    intro r hr
    unfold PInstr.step
    by_cases hrd : r = i.dst
    · subst hrd
      rw [Function.update_self, Function.update_self]
      funext j
      cases i with
      | cst d c => exact (enc_dec hv (c j) (hc j)).symm
      | mov d a =>
        simp only [PInstr.val]
        exact congrFun (hsrc a (by simp [PInstr.srcs])) j
      | add d a b =>
        simp only [PInstr.val, wordAlg, fieldAlg]
        rw [hsrc a (by simp [PInstr.srcs]), hsrc b (by simp [PInstr.srcs])]
        exact maddW_enc hv _ _
      | sub d a b =>
        simp only [PInstr.val, wordAlg, fieldAlg]
        rw [hsrc a (by simp [PInstr.srcs]), hsrc b (by simp [PInstr.srcs])]
        exact msubW_enc hv _ _
      | mul d a b =>
        simp only [PInstr.val, wordAlg, fieldAlg]
        rw [hsrc a (by simp [PInstr.srcs]), hsrc b (by simp [PInstr.srcs])]
        exact mmulW_enc hv _ _
      | perm d a idx =>
        simp only [PInstr.val]
        rw [hsrc a (by simp [PInstr.srcs])]
      | blend d a b m =>
        simp only [PInstr.val]
        rw [hsrc a (by simp [PInstr.srcs]), hsrc b (by simp [PInstr.srcs])]
        split <;> rfl
    · rw [Function.update_of_ne hrd, Function.update_of_ne hrd]
      rw [Function.update_of_ne hrd] at hr
      exact hW r hr
  · cases hd

/-- **The word run simulates the field run on Montgomery forms.** When the program's
    constants lie below `p` and its definedness check from `D` succeeds with `D'`, a word
    register file holding on every register of `D` the Montgomery form of the field
    register file holds, after the run, on every register of `D'` the Montgomery form of
    the field run's value. -/
theorem exec_sim {mp : MontParams} (hv : mp.Valid) :
    ∀ (prog : List PInstr) (D D' : PReg → Bool) (W : Regs (BitVec 32))
      (R : Regs (ZMod mp.p)), (∀ i ∈ prog, CstBelow mp.p i) → defRun D prog = some D' →
      (∀ r, D r = true → W r = fun j => enc mp.p (R r j)) →
      ∀ r, D' r = true →
        exec (wordAlg mp) prog W r = fun j => enc mp.p (exec (fieldAlg mp) prog R r j)
  | [], D, D', W, R, _, hd, hW => by
    simp only [defRun, Option.some.injEq] at hd
    subst hd
    exact hW
  | i :: is, D, D', W, R, hc, hd, hW => by
    simp only [defRun, Option.bind_eq_some_iff] at hd
    obtain ⟨D1, hd1, hd2⟩ := hd
    exact exec_sim hv is D1 D' _ _ (fun i' hi' => hc i' (List.mem_cons_of_mem _ hi')) hd2
      (step_sim hv i (hc i List.mem_cons_self) D D1 hd1 W R hW)

end CatCrypt.Crypto.SecureCompilation.VIR.PackedStateEmit
