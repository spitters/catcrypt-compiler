/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.VIR.ComRange
public meta import CatCrypt.Crypto.SecureCompilation.VIR.MultiReturnCom
public import CatCrypt.Crypto.SecureCompilation.VIR.ComRange
public import CatCrypt.Crypto.SecureCompilation.VIR.MultiReturnCom
public import CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttWordSigned
public meta import CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttWordSigned

/-!
# Exact integer semantics of straight-line `Com jasminDialect` under range bounds

A word program computes an integer program when no binding leaves its lane. This module
gives the integer program, `Com.denoteZ`, and one bounds-indexed theorem relating it to
the word program, `denote_eq_denoteZ_of_boundsOk`. An algebraic statement about a
template is then stated once over `denoteZ`, with no side condition per binding.

A `w`-bit word is read as an integer by `rd signed`: `toNat` when `signed` is `false`,
`toInt` when it is `true`. Both readings are congruent to `toNat` modulo `2^w`, so a
reading in an interval is a member of it in the sense of `Iv.Mem`. The lane of the
reading is `[0, 2^w)` or `[-2^(w-1), 2^(w-1))` (`fitsLane`).

The exact fragment is: `regArith` `add`, `sub`, `mul`; `and` of nonnegative operands
(with a mask `2^k - 1` it is the residue mod `2^k`, `andZ_mask`); `shl` and `shr` by a
count whose interval is one point; `regConst w n` as `n mod 2^w`; `mulhi w` of
nonnegative operands as `⌊a·b / 2^w⌋`; `shrImm` of a nonnegative operand and `sarImm` of
an operand in the signed lane as floor division; `shlImm` as multiplication by `2^n`;
`castW w w'` as the identity, for a nonnegative operand or `w' ≤ w`. Every other
operation has no exact image (`exactIv? = none`), and a program that uses one fails
`boundsOk`.

`boundsOk s ivs c out` runs over the intervals that `rangeAnalysis ivs c` computes (the
abstract environment of `analyze`). A binding passes when its interval and its exact
image under `opZ`, both computed from the intervals of its operands, fit the lane of its
result; the exact image of a subtraction whose subtrahend is a Barrett product of the
minuend (`barrettRule?`) is the Barrett interval. The returned interval must lie in
`out`.

## Main definitions

* `rd`, `fitsLane`: the integer reading of a word and the lane test of an interval.
* `opZ`, `Com.denoteZ`, `MultiReturnCom.denoteZ`: the integer semantics.
* `exactIv?`: the exact image of an operation on intervals.
* `boundsOk`, `boundsOkMR`: the bounds checks.
* `analyzeMR`, `rangeAnalysisMR`: the range analysis of a multi-return program, with the
  intervals of its returned variables.
* `BoundedBlock`, `BoundedBlock.ofBoundsOk`: a program with input and output intervals,
  a decidable side condition and a specification over integer readings.
* `wordSchedBlock`: the word schedules of the lazy NTT as bounded blocks.

## Main results

* `exactIv_sound`: the integer semantics of an operation lies in its exact image and is
  congruent to the word it computes.
* `denote_eq_denoteZ_of_boundsOk`, `denoteMR_eq_denoteZ_of_boundsOk`: when the bounds
  check passes and the input readings lie in their intervals, the readings of the results
  are the integer semantics and lie in the output intervals.
* `rangeAnalysisMR_sound`: every returned value lies in its returned interval.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange

/-! ## 1. Integer readings of words and lanes -/

/-- The integer a `w`-bit word stands for: `toInt` when `signed`, else `toNat`. -/
def rd (signed : Bool) {w : Nat} (x : BitVec w) : ℤ :=
  if signed then x.toInt else (x.toNat : ℤ)

/-- The integer reading of a value of type `t`; `0` for a type other than `reg w`. -/
def rdT (signed : Bool) : (t : JasminTy) → ⟦t⟧ → ℤ
  | .reg _, x => rd signed x
  | _, _ => 0

/-- The interval `i` lies in the lane of `w`-bit words read with `signed`:
    `[0, 2^w)` unsigned, `[-2^(w-1), 2^(w-1))` signed. -/
def fitsLane (signed : Bool) (w : Nat) (i : Iv) : Bool :=
  if signed then decide (-2 ^ w ≤ 2 * i.1) && decide (2 * i.2 < 2 ^ w)
  else decide (0 ≤ i.1) && decide (i.2 < 2 ^ w)

theorem toInt_emod {w : Nat} (x : BitVec w) : x.toInt % 2 ^ w = (x.toNat : ℤ) := by
  have h := BitVec.toNat_ofInt (n := w) x.toInt
  rw [BitVec.ofInt_toInt] at h
  have hnn : 0 ≤ x.toInt % 2 ^ w := Int.emod_nonneg _ (by positivity)
  push_cast at h
  rw [h, Int.toNat_of_nonneg hnn]

theorem rd_emod (s : Bool) {w : Nat} (x : BitVec w) : rd s x % 2 ^ w = (x.toNat : ℤ) := by
  cases s
  · exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (Iv.toNat_lt_int x)
  · exact toInt_emod x

/-- An integer `z` is congruent to `y.toNat` modulo `2^w` iff `y = BitVec.ofInt w z`. -/
theorem ofInt_eq_iff {w : Nat} (z : ℤ) (y : BitVec w) :
    BitVec.ofInt w z = y ↔ z % 2 ^ w = (y.toNat : ℤ) := by
  constructor
  · intro h
    subst h
    rw [BitVec.toNat_ofInt]
    push_cast
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))]
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt]; push_cast; rw [h]; simp

theorem ofInt_rd (s : Bool) {w : Nat} (x : BitVec w) : BitVec.ofInt w (rd s x) = x :=
  (ofInt_eq_iff _ _).2 (rd_emod s x)

/-- A nonnegative reading is the unsigned value. -/
theorem rd_of_nonneg {s : Bool} {w : Nat} {x : BitVec w} (h : 0 ≤ rd s x) :
    rd s x = (x.toNat : ℤ) := by
  cases s
  · rfl
  · simp only [rd, if_true] at h ⊢
    rw [BitVec.toInt_eq_toNat_cond] at h ⊢
    split
    · rfl
    · rename_i hc
      rw [if_neg hc] at h
      have := Iv.toNat_lt_int x
      push_cast at h
      omega

/-- The reading lies in the lane. -/
theorem rd_lane (s : Bool) {w : Nat} (x : BitVec w) :
    (if s then -2 ^ w ≤ 2 * rd s x ∧ 2 * rd s x < 2 ^ w
      else 0 ≤ rd s x ∧ rd s x < 2 ^ w) := by
  cases s
  · exact ⟨Int.natCast_nonneg _, Iv.toNat_lt_int x⟩
  · exact ⟨BitVec.le_two_mul_toInt, BitVec.two_mul_toInt_lt⟩

/-- An integer of a lane-fitting interval congruent to `x` modulo `2^w` is the reading
    of `x`. -/
theorem rd_eq_of_fits {s : Bool} {w : Nat} {x : BitVec w} {r : Iv} {z : ℤ}
    (hf : fitsLane s w r = true) (h1 : r.1 ≤ z) (h2 : z ≤ r.2)
    (hz : z % 2 ^ w = (x.toNat : ℤ)) : rd s x = z := by
  have hM : (0 : ℤ) < 2 ^ w := by positivity
  have hc : (rd s x - z) % 2 ^ w = 0 := by
    rw [Int.sub_emod, rd_emod, hz, sub_self, Int.zero_emod]
  obtain ⟨k, hk⟩ := Int.dvd_of_emod_eq_zero hc
  have hl := rd_lane s x
  have hb : -2 ^ w < rd s x - z ∧ rd s x - z < 2 ^ w := by
    cases s
    · simp only [fitsLane, Bool.false_eq_true, if_false, Bool.and_eq_true,
        decide_eq_true_eq] at hf hl
      constructor <;> linarith [hf.1, hf.2, hl.1, hl.2]
    · simp only [fitsLane, if_true, Bool.and_eq_true, decide_eq_true_eq] at hf hl
      constructor <;> linarith [hf.1, hf.2, hl.1, hl.2]
  rw [hk] at hb
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · nlinarith
  · rw [hk0, mul_zero] at hk; linarith
  · nlinarith

/-- A reading in `i` gives membership in `i` in the sense of `Iv.Mem`. -/
theorem mem_of_rd {s : Bool} {w : Nat} {x : BitVec w} {i : Iv} (h1 : i.1 ≤ rd s x)
    (h2 : rd s x ≤ i.2) : i.Mem w x :=
  ⟨rd s x, h1, h2, rd_emod s x⟩

/-- A word in `i` (`Iv.Mem`) with `i` in the lane has its reading in `i`. -/
theorem rd_mem_of_fits {s : Bool} {w : Nat} {x : BitVec w} {i : Iv}
    (hf : fitsLane s w i = true) (h : i.Mem w x) : i.1 ≤ rd s x ∧ rd s x ≤ i.2 := by
  obtain ⟨v, h1, h2, hv⟩ := h
  rw [rd_eq_of_fits hf h1 h2 hv]
  exact ⟨h1, h2⟩

/-! ## 2. Typed forms -/

/-- `fitsLane` at a type: `false` for a type other than `reg w`. -/
def fitsT (s : Bool) : JasminTy → Iv → Bool
  | .reg w, i => fitsLane s w i
  | _, _ => false

/-- The reading of `y` lies in `i`; no condition for a type other than `reg w`. -/
def ivZ (s : Bool) : (t : JasminTy) → Iv → ⟦t⟧ → Prop
  | .reg _, i, x => i.1 ≤ rd s x ∧ rd s x ≤ i.2
  | _, _, _ => True

/-- `z` is congruent to the word `y` modulo `2^w` when `t = reg w`; false otherwise. -/
def CongT : (t : JasminTy) → ℤ → ⟦t⟧ → Prop
  | .reg w, z, y => z % 2 ^ w = ((y : BitVec w).toNat : ℤ)
  | _, _, _ => False

theorem rdT_eq_of_cong {s : Bool} : ∀ (t : JasminTy) {r : Iv} {y : ⟦t⟧} {z : ℤ},
    fitsT s t r = true → r.1 ≤ z → z ≤ r.2 → CongT t z y → rdT s t y = z
  | .reg _, _, _, _, hf, h1, h2, hc => rd_eq_of_fits hf h1 h2 hc
  | .stackArr _ _, _, _, _, hf, _, _, _ => by cases hf
  | .inlineInt, _, _, _, hf, _, _, _ => by cases hf
  | .bool, _, _, _, hf, _, _, _ => by cases hf

theorem ivZ_of_valMem {s : Bool} : ∀ (t : JasminTy) {i : Iv} {y : ⟦t⟧},
    fitsT s t i = true → valMem t i y → ivZ s t i y
  | .reg _, _, _, hf, hm => rd_mem_of_fits hf hm
  | .stackArr _ _, _, _, _, _ => trivial
  | .inlineInt, _, _, _, _ => trivial
  | .bool, _, _, _, _ => trivial

theorem valMem_of_ivZ {s : Bool} : ∀ (t : JasminTy) {i : Iv} {y : ⟦t⟧},
    ivZ s t i y → valMem t i y
  | .reg _, _, _, h => mem_of_rd h.1 h.2
  | .stackArr _ _, _, _, _ => trivial
  | .inlineInt, _, _, _ => trivial
  | .bool, _, _, _ => trivial

/-! ## 3. The exact integer semantics -/

/-- A vector of integers, one per entry of `l`. -/
abbrev ZVec (l : List JasminTy) := HVector (fun _ => ℤ) l

/-- The bitwise `and` of two nonnegative integers. -/
def andZ (a b : ℤ) : ℤ := ((a.toNat &&& b.toNat : ℕ) : ℤ)

/-- The `and` with the mask `2^k - 1` of a nonnegative integer is its residue mod `2^k`. -/
theorem andZ_mask {a : ℤ} (ha : 0 ≤ a) (k : ℕ) : andZ a (2 ^ k - 1) = a % 2 ^ k := by
  have e : ((2 : ℤ) ^ k - 1).toNat = 2 ^ k - 1 := by
    have : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have h2 : ((2 ^ k : ℕ) : ℤ) = 2 ^ k := by push_cast; rfl
    omega
  have ha' : a = (a.toNat : ℤ) := (Int.toNat_of_nonneg ha).symm
  unfold andZ
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  conv_rhs => rw [ha']
  push_cast; rfl

/-- The integer semantics of a binary operator: `+`, `-`, `*`, `and`, and the shifts
    `a · 2^b`, `⌊a / 2^b⌋`; `0` for the operators outside the fragment. -/
def binZ : JasminBinOp → ℤ → ℤ → ℤ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .and, a, b => andZ a b
  | .shl, a, b => a * 2 ^ b.toNat
  | .shr, a, b => a / 2 ^ b.toNat
  | _, _, _ => 0

variable {Γ : JCtxt}

/-- The integer semantics of an operation on the integer values `Z` of its context:
    `regArith` by `binZ`, `regConst w n` as `n mod 2^w`, `mulhi w` as `⌊a·b / 2^w⌋`,
    `shrImm`/`sarImm` by `n` as `⌊a / 2^n⌋`, `shlImm` by `n` as `a · 2^n`, `castW` as the
    identity; `0` for every other operation. -/
def opZ (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op))
    (Z : ZVec Γ) : ℤ :=
  match op, args with
  | .regArith bop _, args => binZ bop (hget Z args.head) (hget Z args.tail.head)
  | .regConst w n, _ => ((n % 2 ^ w : ℕ) : ℤ)
  | .mulhi w, args => hget Z args.head * hget Z args.tail.head / 2 ^ w
  | .shrImm _ n, args => hget Z args.head / 2 ^ n
  | .sarImm _ n, args => hget Z args.head / 2 ^ n
  | .shlImm _ n, args => hget Z args.head * 2 ^ n
  | .castW _ _, args => hget Z args.head
  | _, _ => 0

/-- The integer semantics of a program: each binding by `opZ`, the result the value of
    the returned variable. -/
def _root_.CatCrypt.Crypto.SecureCompilation.VIR.Com.denoteZ :
    {Γ : JCtxt} → {t : JasminTy} → Com jasminDialect Γ t → ZVec Γ → ℤ
  | _, _, .ret v, Z => hget Z v
  | _, _, .var e body, Z => body.denoteZ (HVector.cons (opZ e.op e.args Z) Z)

/-- The integer values of the returned variables. -/
def lookupZ : {ts : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) ts → ZVec Γ → ZVec ts
  | [], .nil, _ => .nil
  | _ :: _, .cons v vs, Z => .cons (hget Z v) (lookupZ vs Z)

/-- The integer semantics of a multi-return program. -/
def _root_.CatCrypt.Crypto.SecureCompilation.VIR.MultiReturnCom.denoteZ :
    {Γ : JCtxt} → {ts : List JasminTy} → MultiReturnCom jasminDialect Γ ts → ZVec Γ →
      ZVec ts
  | _, _, .ret vs, Z => lookupZ vs Z
  | _, _, .var e body, Z => body.denoteZ (HVector.cons (opZ e.op e.args Z) Z)

/-- The integer readings of a vector of values. -/
def zvals (s : Bool) : {ts : List JasminTy} → HVector (fun t => ⟦t⟧) ts → ZVec ts
  | [], .nil => .nil
  | t :: _, .cons x xs => .cons (rdT s t x) (zvals s xs)

/-- Every value of `xs` has its reading in its interval of `ivs`. -/
def ValsIn (s : Bool) : {ts : List JasminTy} → HVector (fun _ => Iv) ts →
    HVector (fun t => ⟦t⟧) ts → Prop
  | [], .nil, .nil => True
  | t :: _, .cons i is, .cons x xs => ivZ s t i x ∧ ValsIn s is xs

theorem hget_zvals (s : Bool) : ∀ {ts : JCtxt} {t : JasminTy}
    (xs : HVector (fun t => ⟦t⟧) ts) (v : Ctxt.Var ts t),
    hget (zvals s xs) v = rdT s t (v.lookup xs)
  | _ :: _, _, .cons _ _, .here => rfl
  | _ :: _, _, .cons _ xs, .there v => hget_zvals s xs v

theorem ValsIn.hget {s : Bool} : ∀ {ts : JCtxt} {ivs : HVector (fun _ => Iv) ts}
    {xs : HVector (fun t => ⟦t⟧) ts}, ValsIn s ivs xs →
    ∀ {t : JasminTy} (v : Ctxt.Var ts t), ivZ s t (hget ivs v) (v.lookup xs)
  | _ :: _, .cons _ _, .cons _ _, h, _, .here => h.1
  | _ :: _, .cons _ _, .cons _ _, h, _, .there v => ValsIn.hget h.2 v

/-! ## 4. The exact image of an operation -/

/-- The interval of all products of a member of `a` and a member of `b`. -/
def ivMulZ (a b : Iv) : Iv :=
  (min (min (a.1 * b.1) (a.1 * b.2)) (min (a.2 * b.1) (a.2 * b.2)),
   max (max (a.1 * b.1) (a.1 * b.2)) (max (a.2 * b.1) (a.2 * b.2)))

theorem mul_mem_seg {a1 a2 x : ℤ} (y : ℤ) (h1 : a1 ≤ x) (h2 : x ≤ a2) :
    min (a1 * y) (a2 * y) ≤ x * y ∧ x * y ≤ max (a1 * y) (a2 * y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right h1 hy),
      le_trans (mul_le_mul_of_nonneg_right h2 hy) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right h2 hy),
      le_trans (mul_le_mul_of_nonpos_right h1 hy) (le_max_left _ _)⟩

theorem mem_ivMulZ {a b : Iv} {x y : ℤ} (hx1 : a.1 ≤ x) (hx2 : x ≤ a.2) (hy1 : b.1 ≤ y)
    (hy2 : y ≤ b.2) : (ivMulZ a b).1 ≤ x * y ∧ x * y ≤ (ivMulZ a b).2 := by
  obtain ⟨l, u⟩ := mul_mem_seg y hx1 hx2
  have e1 := mul_mem_seg a.1 hy1 hy2
  have e2 := mul_mem_seg a.2 hy1 hy2
  rw [mul_comm b.1, mul_comm b.2, mul_comm y] at e1 e2
  exact ⟨le_trans (min_le_min e1.1 e2.1) l, le_trans u (max_le_max e1.2 e2.2)⟩

variable (A : AEnv Γ)

/-- The image under `binZ bop` of the intervals of `a` and `b`, when the operator is in
    the exact fragment for them: `and` and `shr` need nonnegative operands, the shift
    counts a one-point interval, and a Barrett remainder (`barrettRule?`) takes the
    Barrett interval. -/
def binExact? (w : Nat) (bop : JasminBinOp) (a b : Ctxt.Var Γ (.reg w)) : Option Iv :=
  match bop with
  | .add => some ((hget A a).1.1 + (hget A b).1.1, (hget A a).1.2 + (hget A b).1.2)
  | .sub =>
    match barrettRule? A a b with
    | some r =>
      if 0 ≤ (hget A b).1.1 then some r
      else some ((hget A a).1.1 - (hget A b).1.2, (hget A a).1.2 - (hget A b).1.1)
    | none => some ((hget A a).1.1 - (hget A b).1.2, (hget A a).1.2 - (hget A b).1.1)
  | .mul => some (ivMulZ (hget A a).1 (hget A b).1)
  | .and =>
    if 0 ≤ (hget A a).1.1 ∧ 0 ≤ (hget A b).1.1 then
      some (0, min (hget A a).1.2 (hget A b).1.2)
    else none
  | .shl =>
    match ivSingle? (hget A b).1 with
    | some k => some ((hget A a).1.1 * 2 ^ k, (hget A a).1.2 * 2 ^ k)
    | none => none
  | .shr =>
    match ivSingle? (hget A b).1 with
    | some k =>
      if 0 ≤ (hget A a).1.1 then some ((hget A a).1.1 / 2 ^ k, (hget A a).1.2 / 2 ^ k)
      else none
    | none => none
  | _ => none

/-- The image under `opZ` of the intervals of the operands, when the operation is in the
    exact fragment for them; `none` otherwise. -/
def exactIv? (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op)) :
    Option Iv :=
  match op, args with
  | .regArith bop w, args => binExact? A w bop args.head args.tail.head
  | .regConst w n, _ => some (ivConst w n)
  | .mulhi w, args =>
    let ia := (hget A args.head).1
    let ib := (hget A args.tail.head).1
    if 0 ≤ ia.1 ∧ 0 ≤ ib.1 then some (ia.1 * ib.1 / 2 ^ w, ia.2 * ib.2 / 2 ^ w) else none
  | .shrImm _ n, args =>
    let ia := (hget A args.head).1
    if 0 ≤ ia.1 then some (ia.1 / 2 ^ n, ia.2 / 2 ^ n) else none
  | .sarImm w n, args =>
    let ia := (hget A args.head).1
    if fitsLane true w ia then some (ia.1 / 2 ^ n, ia.2 / 2 ^ n) else none
  | .shlImm _ n, args =>
    let ia := (hget A args.head).1
    some (ia.1 * 2 ^ n, ia.2 * 2 ^ n)
  | .castW w w', args =>
    let ia := (hget A args.head).1
    if 0 ≤ ia.1 ∨ w' ≤ w then some ia else none
  | _, _ => none

/-! ## 5. Soundness of the exact image -/

/-- The integer values `Z` are the readings of `V`, and each reading lies in its
    interval of `A`. -/
def ZOK (s : Bool) (V : Ctxt.Valuation Γ) (Z : ZVec Γ) : Prop :=
  ∀ (t : JasminTy) (v : Ctxt.Var Γ t),
    hget Z v = rdT s t (v.lookup V) ∧ ivZ s t (hget A v).1 (v.lookup V)

variable {A} {s : Bool} {V : Ctxt.Valuation Γ} {Z : ZVec Γ}

theorem ZOK.reg (h : ZOK A s V Z) {w : Nat} (v : Ctxt.Var Γ (.reg w)) :
    hget Z v = rd s (regVal V v) ∧ (hget A v).1.1 ≤ rd s (regVal V v) ∧
      rd s (regVal V v) ≤ (hget A v).1.2 :=
  h (.reg w) v

theorem ZOK.cons (h : ZOK A s V Z) {t : JasminTy} {a : AVal} {y : ⟦t⟧} {z : ℤ}
    (hz : z = rdT s t y) (hy : ivZ s t a.1 y) :
    ZOK (HVector.cons (f := fun _ => AVal) a A) s (V.extend y) (HVector.cons z Z) := by
  intro u v
  cases v with
  | here => exact ⟨hz, hy⟩
  | there v => exact h u v

/-- The Barrett remainder of nonnegative operands is exact and lies in its interval. -/
theorem barrett_exact (hA : EnvOK A V) (hZ : ZOK A s V Z) {w : Nat}
    {a b : Ctxt.Var Γ (.reg w)} {r : Iv} (h : barrettRule? A a b = some r)
    (hb0 : 0 ≤ (hget A b).1.1) :
    r.1 ≤ rd s (regVal V a) - rd s (regVal V b) ∧
      rd s (regVal V a) - rd s (regVal V b) ≤ r.2 := by
  obtain ⟨-, ha1, ha2⟩ := hZ.reg a
  obtain ⟨-, hb1, -⟩ := hZ.reg b
  unfold barrettRule? at h
  split at h
  · rename_i ℓ s' m t p hs
    split at h
    · rename_i hl
      have hb := (hA.reg b).2
      rw [hs] at hb
      have hy := hb.holds a hl
      unfold ivBarrett? at h
      split at h
      · rename_i hc
        obtain ⟨hx0, -, hmp⟩ := hc
        cases h
        have hxa := rd_of_nonneg (le_trans hx0 ha1)
        have hyb := rd_of_nonneg (le_trans hb0 hb1)
        rw [hxa] at ha2 ⊢
        rw [hyb]
        have hX : (regVal V a).toNat ≤ (hget A a).1.2.toNat := by omega
        obtain ⟨hle, hub⟩ := barrett_nat _ _ s' t m p hX hmp
        change (regVal V b).toNat = _ at hy
        rw [hy]
        generalize (regVal V a).toNat / 2 ^ s' * m / 2 ^ t * p = Q at hle hub ⊢
        generalize barrettBound (hget A a).1.2.toNat s' t m p = B at hub ⊢
        constructor <;> simp only <;> omega
      · cases h
    · cases h
  · cases h

theorem binExact_sound (hA : EnvOK A V) (hZ : ZOK A s V Z) {w : Nat} (bop : JasminBinOp)
    (a b : Ctxt.Var Γ (.reg w)) {r : Iv} (h : binExact? A w bop a b = some r) :
    r.1 ≤ binZ bop (hget Z a) (hget Z b) ∧ binZ bop (hget Z a) (hget Z b) ≤ r.2 ∧
      binZ bop (hget Z a) (hget Z b) % 2 ^ w
        = ((bop.apply (regVal V a) (regVal V b)).toNat : ℤ) := by
  obtain ⟨hza, ha1, ha2⟩ := hZ.reg a
  obtain ⟨hzb, hb1, hb2⟩ := hZ.reg b
  rw [hza, hzb]
  have hM : (0 : ℤ) < 2 ^ w := by positivity
  cases bop with
  | add =>
    simp only [binExact?, Option.some.injEq] at h
    subst h
    refine ⟨by simp only [binZ]; omega, by simp only [binZ]; omega, ?_⟩
    rw [← ofInt_eq_iff]
    simp only [binZ, JasminBinOp.apply]
    rw [BitVec.ofInt_add, ofInt_rd, ofInt_rd]
  | sub =>
    have hc : (rd s (regVal V a) - rd s (regVal V b)) % 2 ^ w
        = ((regVal V a - regVal V b).toNat : ℤ) := by
      rw [← ofInt_eq_iff, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, ofInt_rd,
        ofInt_rd, BitVec.sub_eq_add_neg]
    simp only [binZ, JasminBinOp.apply]
    refine ⟨?_, ?_, hc⟩ <;>
    · simp only [binExact?] at h
      split at h
      · rename_i r' hr
        split at h
        · rename_i hb0
          cases h
          have := barrett_exact hA hZ hr hb0
          omega
        · cases h; simp only; omega
      · cases h; simp only; omega
  | mul =>
    simp only [binExact?, Option.some.injEq] at h
    subst h
    obtain ⟨l, u⟩ := mem_ivMulZ ha1 ha2 hb1 hb2
    refine ⟨l, u, ?_⟩
    rw [← ofInt_eq_iff]
    simp only [binZ, JasminBinOp.apply]
    rw [BitVec.ofInt_mul, ofInt_rd, ofInt_rd]
  | and =>
    simp only [binExact?] at h
    split at h
    · rename_i hc
      cases h
      have hxa := rd_of_nonneg (le_trans hc.1 ha1)
      have hyb := rd_of_nonneg (le_trans hc.2 hb1)
      rw [hxa] at ha2 ⊢
      rw [hyb] at hb2 ⊢
      have e1 : (regVal V a).toNat &&& (regVal V b).toNat ≤ (regVal V a).toNat :=
        Nat.and_le_left
      have e2 : (regVal V a).toNat &&& (regVal V b).toNat ≤ (regVal V b).toNat :=
        Nat.and_le_right
      have hlt := (regVal V a).isLt
      simp only [binZ, andZ, Int.toNat_natCast, JasminBinOp.apply, BitVec.toNat_and]
      refine ⟨by simp, by simp only [le_min_iff]; omega, ?_⟩
      exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by
        have : ((regVal V a).toNat &&& (regVal V b).toNat : ℤ) < 2 ^ w := by
          exact_mod_cast lt_of_le_of_lt e1 hlt
        exact_mod_cast this)
    · cases h
  | shl =>
    simp only [binExact?] at h
    split at h
    · rename_i k hk
      cases h
      unfold ivSingle? at hk
      split at hk
      · rename_i hc
        cases hk
        have hyk : rd s (regVal V b) = (hget A b).1.1 := by omega
        have hyb := rd_of_nonneg (s := s) (x := regVal V b) (by omega)
        have hn : (regVal V b).toNat = (hget A b).1.1.toNat := by omega
        have hp : (0 : ℤ) ≤ 2 ^ (hget A b).1.1.toNat := by positivity
        simp only [binZ, JasminBinOp.apply, hyk, hn]
        refine ⟨mul_le_mul_of_nonneg_right ha1 hp, mul_le_mul_of_nonneg_right ha2 hp, ?_⟩
        rw [← ofInt_eq_iff, BitVec.ofInt_mul, ofInt_rd, BitVec.shiftLeft_eq_mul_twoPow]
        congr 1
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofInt, BitVec.toNat_twoPow]
        push_cast
        rw [Int.toNat_emod (by positivity) (by positivity)]
        norm_cast
      · cases hk
    · cases h
  | shr =>
    simp only [binExact?] at h
    split at h
    · rename_i k hk
      split at h
      · rename_i ha0
        cases h
        unfold ivSingle? at hk
        split at hk
        · rename_i hc
          cases hk
          have hyk : rd s (regVal V b) = (hget A b).1.1 := by omega
          have hyb := rd_of_nonneg (s := s) (x := regVal V b) (by omega)
          have hn : (regVal V b).toNat = (hget A b).1.1.toNat := by omega
          have hxa := rd_of_nonneg (le_trans ha0 ha1)
          have hp : (0 : ℤ) < 2 ^ (hget A b).1.1.toNat := by positivity
          simp only [binZ, JasminBinOp.apply, hyk, hn]
          refine ⟨Int.ediv_le_ediv hp ha1, Int.ediv_le_ediv hp ha2, ?_⟩
          rw [hxa, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
          have hlt := (regVal V a).isLt
          push_cast
          refine Int.emod_eq_of_lt (by positivity) ?_
          have : (regVal V a).toNat / 2 ^ (hget A b).1.1.toNat < 2 ^ w :=
            lt_of_le_of_lt (Nat.div_le_self _ _) hlt
          exact_mod_cast this
        · cases hk
      · cases h
    · cases h
  | or => cases h
  | xor => cases h
  | andn => cases h

theorem shl_cong {w : Nat} (x : BitVec w) (k : Nat) :
    (rd s x * 2 ^ k) % 2 ^ w = ((x <<< k).toNat : ℤ) := by
  rw [← ofInt_eq_iff, BitVec.ofInt_mul, ofInt_rd, BitVec.shiftLeft_eq_mul_twoPow]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, BitVec.toNat_twoPow]
  push_cast
  rw [Int.toNat_emod (by positivity) (by positivity)]
  norm_cast

theorem shr_cong {w : Nat} (x : BitVec w) (k : Nat) :
    ((x.toNat : ℤ) / 2 ^ k) % 2 ^ w = ((x >>> k).toNat : ℤ) := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hlt := x.isLt
  push_cast
  refine Int.emod_eq_of_lt (by positivity) ?_
  have : x.toNat / 2 ^ k < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) hlt
  exact_mod_cast this

/-- **Soundness of the exact image.** When `exactIv?` gives `r`, the integer semantics of
    the operation on the readings lies in `r` and is congruent to the word it computes. -/
theorem exactIv_sound (hA : EnvOK A V) (hZ : ZOK A s V Z) (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op))
    {r : Iv} (h : exactIv? A op args = some r) :
    r.1 ≤ opZ op args Z ∧ opZ op args Z ≤ r.2 ∧
      CongT (DialectSignature.ret (d := jasminDialect) op) (opZ op args Z)
        (DialectDenote.denote op (Expr.lookupArgs args V)) := by
  have hM : (0 : ℤ) < 2 ^ 0 := by positivity
  cases op with
  | regArith bop w =>
    match args with
    | .cons a (.cons b .nil) => exact binExact_sound hA hZ bop a b h
  | regConst w n =>
    simp only [exactIv?, Option.some.injEq] at h
    subst h
    refine ⟨le_refl _, le_refl _, ?_⟩
    show ((n % 2 ^ w : ℕ) : ℤ) % 2 ^ w = ((BitVec.ofNat w n).toNat : ℤ)
    rw [BitVec.toNat_ofNat]
    exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Nat.mod_lt _ (by positivity))
  | mulhi w =>
    match args with
    | .cons a (.cons b .nil) =>
      obtain ⟨hza, ha1, ha2⟩ := hZ.reg a
      obtain ⟨hzb, hb1, hb2⟩ := hZ.reg b
      simp only [exactIv?, HVector.head, HVector.tail] at h
      split at h
      · rename_i hc
        cases h
        have hxa := rd_of_nonneg (le_trans hc.1 ha1)
        have hyb := rd_of_nonneg (le_trans hc.2 hb1)
        have hp : (0 : ℤ) < 2 ^ w := by positivity
        show _ ≤ hget Z a * hget Z b / 2 ^ w ∧ hget Z a * hget Z b / 2 ^ w ≤ _ ∧
          hget Z a * hget Z b / 2 ^ w % 2 ^ w = ((mulHiW (regVal V a) (regVal V b)).toNat : ℤ)
        rw [hza, hzb]
        refine ⟨Int.ediv_le_ediv hp (Int.mul_le_mul ha1 hb1 hc.2 (by omega)),
          Int.ediv_le_ediv hp (Int.mul_le_mul ha2 hb2 (by omega) (by omega)), ?_⟩
        rw [hxa, hyb, mulHiW, BitVec.toNat_ofNat]
        push_cast
        rfl
      · cases h
  | shrImm w n =>
    match args with
    | .cons a .nil =>
      obtain ⟨hza, ha1, ha2⟩ := hZ.reg a
      simp only [exactIv?, HVector.head] at h
      split at h
      · rename_i hc
        cases h
        have hxa := rd_of_nonneg (le_trans hc ha1)
        have hp : (0 : ℤ) < 2 ^ n := by positivity
        show _ ≤ hget Z a / 2 ^ n ∧ hget Z a / 2 ^ n ≤ _ ∧
          hget Z a / 2 ^ n % 2 ^ w = ((regVal V a >>> n).toNat : ℤ)
        rw [hza]
        refine ⟨Int.ediv_le_ediv hp ha1, Int.ediv_le_ediv hp ha2, ?_⟩
        rw [hxa]
        exact shr_cong _ n
      · cases h
  | sarImm w n =>
    match args with
    | .cons a .nil =>
      obtain ⟨hza, ha1, ha2⟩ := hZ.reg a
      simp only [exactIv?, HVector.head] at h
      split at h
      · rename_i hc
        cases h
        have hp : (0 : ℤ) < 2 ^ n := by positivity
        show _ ≤ hget Z a / 2 ^ n ∧ hget Z a / 2 ^ n ≤ _ ∧
          hget Z a / 2 ^ n % 2 ^ w = ((BitVec.sshiftRight (regVal V a) n).toNat : ℤ)
        rw [hza]
        refine ⟨Int.ediv_le_ediv hp ha1, Int.ediv_le_ediv hp ha2, ?_⟩
        have hx : rd s (regVal V a) = (regVal V a).toInt := by
          cases s
          · simp only [fitsLane, if_true, Bool.and_eq_true, decide_eq_true_eq] at hc
            have hl := rd_lane false (regVal V a)
            simp only [Bool.false_eq_true, if_false] at hl
            simp only [rd, Bool.false_eq_true, if_false] at ha2 hl ⊢
            have e2 : ((2 ^ w : ℕ) : ℤ) = 2 ^ w := by push_cast; rfl
            have hlt : 2 * (regVal V a).toNat < 2 ^ w := by
              have : (2 * (regVal V a).toNat : ℤ) < ((2 ^ w : ℕ) : ℤ) := by omega
              exact_mod_cast this
            rw [BitVec.toInt_eq_toNat_cond, if_pos hlt]
          · rfl
        rw [hx, ← toInt_emod, BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
        push_cast; rfl
      · cases h
  | shlImm w n =>
    match args with
    | .cons a .nil =>
      obtain ⟨hza, ha1, ha2⟩ := hZ.reg a
      simp only [exactIv?, Option.some.injEq] at h
      subst h
      have hp : (0 : ℤ) ≤ 2 ^ n := by positivity
      show _ ≤ hget Z a * 2 ^ n ∧ hget Z a * 2 ^ n ≤ _ ∧
        hget Z a * 2 ^ n % 2 ^ w = ((regVal V a <<< n).toNat : ℤ)
      rw [hza]
      exact ⟨mul_le_mul_of_nonneg_right ha1 hp, mul_le_mul_of_nonneg_right ha2 hp,
        shl_cong _ n⟩
  | castW w w' =>
    match args with
    | .cons a .nil =>
      obtain ⟨hza, ha1, ha2⟩ := hZ.reg a
      simp only [exactIv?, HVector.head] at h
      split at h
      · rename_i hc
        cases h
        show _ ≤ hget Z a ∧ hget Z a ≤ _ ∧
          hget Z a % 2 ^ w' = (((regVal V a).zeroExtend w').toNat : ℤ)
        rw [hza]
        refine ⟨ha1, ha2, ?_⟩
        rw [BitVec.toNat_setWidth]
        rcases hc with hc | hc
        · rw [rd_of_nonneg (le_trans hc ha1)]
          push_cast; rfl
        · rw [← Int.emod_emod_of_dvd _ (pow_dvd_pow (2 : ℤ) hc), rd_emod]
          push_cast; rfl
      · cases h
  | _ => cases h

/-! ## 6. The bounds check of a program -/

/-- A binding passes when its interval from the range analysis and its exact image both
    fit the lane of its result type. -/
def bindOk (s : Bool) (A : AEnv Γ) (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op)) :
    Bool :=
  fitsT s (DialectSignature.ret (d := jasminDialect) op) (opAbs A op args).1 &&
    match exactIv? A op args with
    | some r => fitsT s (DialectSignature.ret (d := jasminDialect) op) r
    | none => false

/-- A passing binding extends both invariants. -/
theorem bindOk_step (hA : EnvOK A V) (hZ : ZOK A s V Z) (op : JasminOp)
    (args : HVector (fun ty => Ctxt.Var Γ ty) (DialectSignature.sig (d := jasminDialect) op))
    (h : bindOk s A op args = true) :
    EnvOK (HVector.cons (f := fun _ => AVal) (opAbs A op args) A)
        (V.extend (DialectDenote.denote op (Expr.lookupArgs args V))) ∧
      ZOK (HVector.cons (f := fun _ => AVal) (opAbs A op args) A) s
        (V.extend (DialectDenote.denote op (Expr.lookupArgs args V)))
        (HVector.cons (opZ op args Z) Z) := by
  simp only [bindOk, Bool.and_eq_true] at h
  obtain ⟨hf, hr⟩ := h
  split at hr
  · rename_i r hex
    obtain ⟨h1, h2, hc⟩ := exactIv_sound hA hZ op args hex
    have hv := opAbs_sound hA op args
    exact ⟨hA.cons hv,
      hZ.cons (rdT_eq_of_cong _ hr h1 h2 hc).symm (ivZ_of_valMem _ hf hv.valMem)⟩
  · cases hr

/-- `bindOk_step` at an expression. -/
theorem bindOk_step_expr (hA : EnvOK A V) (hZ : ZOK A s V Z) {t : JasminTy}
    (e : Expr jasminDialect Γ t) (h : bindOk s A e.op e.args = true) :
    EnvOK (HVector.cons (f := fun _ => AVal) (exprAbs A e) A) (V.extend (e.denote V)) ∧
      ZOK (HVector.cons (f := fun _ => AVal) (exprAbs A e) A) s (V.extend (e.denote V))
        (HVector.cons (opZ e.op e.args Z) Z) := by
  rcases e with ⟨op, rfl, args⟩
  exact bindOk_step hA hZ op args h

/-- The interval `i` of a returned value lies in `o`; a value of a type other than
    `reg w` passes. -/
def retOk : JasminTy → Iv → Iv → Bool
  | .reg _, i, o => decide (o.1 ≤ i.1) && decide (i.2 ≤ o.2)
  | _, _, _ => true

theorem ivZ_of_retOk : ∀ {t : JasminTy} {i o : Iv} {y : ⟦t⟧}, retOk t i o = true →
    ivZ s t i y → ivZ s t o y
  | .reg _, _, _, _, h, hy => by
    simp only [retOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨le_trans h.1 hy.1, le_trans hy.2 h.2⟩
  | .stackArr _ _, _, _, _, _, _ => trivial
  | .inlineInt, _, _, _, _, _ => trivial
  | .bool, _, _, _, _, _ => trivial

/-- The bounds check of `c` from the abstract environment `A`: every binding passes
    `bindOk` with the intervals of `analyze`, and the returned interval lies in `out`. -/
def checkCom (s : Bool) : {Γ : JCtxt} → {t : JasminTy} → AEnv Γ → Com jasminDialect Γ t →
    Iv → Bool
  | _, t, A, .ret v, out => retOk t (hget A v).1 out
  | _, _, A, .var e body, out =>
    bindOk s A e.op e.args &&
      checkCom s (HVector.cons (f := fun _ => AVal) (exprAbs A e) A) body out

/-- The bounds check of `c` from the input intervals `ivs`, over the intervals of
    `rangeAnalysis ivs c`: every binding is in the exact fragment with its exact image and
    its interval in the lane read with `s`, and the returned interval lies in `out`. -/
def boundsOk (s : Bool) (ivs : HVector (fun _ => Iv) Γ) {t : JasminTy}
    (c : Com jasminDialect Γ t) (out : Iv) : Bool :=
  checkCom s (AEnv.ofIvs ivs) c out

theorem checkCom_sound : ∀ {Γ : JCtxt} {t : JasminTy} (c : Com jasminDialect Γ t) (A : AEnv Γ)
    (V : Ctxt.Valuation Γ) (Z : ZVec Γ) (out : Iv), EnvOK A V → ZOK A s V Z →
    checkCom s A c out = true → rdT s t (c.denote V) = c.denoteZ Z ∧ ivZ s t out (c.denote V)
  | _, _, .ret v, A, V, Z, _, _, hZ, h => by
    obtain ⟨hz, hi⟩ := hZ _ v
    exact ⟨hz.symm, ivZ_of_retOk h hi⟩
  | _, _, .var e body, _, _, _, out, hA, hZ, h => by
    replace h := (Bool.and_eq_true _ _).mp h
    obtain ⟨hs1, hs2⟩ := bindOk_step_expr hA hZ e h.1
    exact checkCom_sound body _ _ _ out hs1 hs2 h.2

theorem envOK_ofIvs {ivs : HVector (fun _ => Iv) Γ} (hV : ValsIn s ivs V) :
    EnvOK (AEnv.ofIvs ivs) V := by
  intro u v
  rw [hget_ofIvs]
  cases u with
  | reg w =>
    have h := hV.hget v
    exact ⟨mem_of_rd h.1 h.2, SymOK.none _ _ _⟩
  | _ => trivial

theorem zok_ofIvs {ivs : HVector (fun _ => Iv) Γ} (hV : ValsIn s ivs V) :
    ZOK (AEnv.ofIvs ivs) s V (zvals s V) := by
  intro t v
  refine ⟨hget_zvals s V v, ?_⟩
  rw [hget_ofIvs]
  exact hV.hget v

/-- **The word program computes the integer program.** When the bounds check passes and
    every input reading lies in its interval, the reading of the result is the integer
    semantics of the program on the input readings, and it lies in `out`. -/
theorem denote_eq_denoteZ_of_boundsOk {w : Nat} (s : Bool) (ivs : HVector (fun _ => Iv) Γ)
    (c : Com jasminDialect Γ (.reg w)) (out : Iv) (h : boundsOk s ivs c out = true)
    (V : Ctxt.Valuation Γ) (hV : ValsIn s ivs V) :
    rd s (c.denote V) = c.denoteZ (zvals s V) ∧
      out.1 ≤ rd s (c.denote V) ∧ rd s (c.denote V) ≤ out.2 :=
  checkCom_sound c _ V _ out (envOK_ofIvs hV) (zok_ofIvs hV) h

/-! ## 7. Multi-return programs -/

/-- The intervals of the returned variables, read at their levels in `A`. -/
def retIvs (A : AEnv Γ) : {ts : List JasminTy} → HVector (fun ty => Ctxt.Var Γ ty) ts →
    List Iv
  | [], .nil => []
  | _ :: _, .cons v vs => (hget A v).1 :: retIvs A vs

/-- The range analysis of a multi-return program: the intervals of its bindings in order,
    and the intervals of its returned variables. -/
def analyzeMR : {Γ : JCtxt} → {ts : List JasminTy} → AEnv Γ →
    MultiReturnCom jasminDialect Γ ts → List Iv × List Iv
  | _, _, A, .ret vs => ([], retIvs A vs)
  | _, _, A, .var e body =>
    let r := analyzeMR (HVector.cons (f := fun _ => AVal) (exprAbs A e) A) body
    ((exprAbs A e).1 :: r.1, r.2)

/-- `analyzeMR` from the input intervals `ivs`. -/
def rangeAnalysisMR (ivs : HVector (fun _ => Iv) Γ) {ts : List JasminTy}
    (c : MultiReturnCom jasminDialect Γ ts) : List Iv × List Iv :=
  analyzeMR (AEnv.ofIvs ivs) c

/-- Every value of `xs` is a member of its interval of `is`. -/
def ValsMem : {ts : List JasminTy} → List Iv → HVector (fun t => ⟦t⟧) ts → Prop
  | [], _, .nil => True
  | _ :: _, [], _ => False
  | t :: _, i :: is, .cons x xs => valMem t i x ∧ ValsMem is xs

theorem retIvs_sound (hA : EnvOK A V) : ∀ {ts : List JasminTy}
    (vs : HVector (fun ty => Ctxt.Var Γ ty) ts),
    ValsMem (retIvs A vs) (MultiReturnCom.lookupVars vs V)
  | [], .nil => trivial
  | _ :: _, .cons v vs => ⟨(hA _ v).valMem, retIvs_sound hA vs⟩

theorem analyzeMR_sound : ∀ {Γ : JCtxt} {ts : List JasminTy}
    (c : MultiReturnCom jasminDialect Γ ts) (A : AEnv Γ) (V : Ctxt.Valuation Γ),
    EnvOK A V → ValsMem (analyzeMR A c).2 (c.denote V)
  | _, _, .ret vs, _, _, hA => retIvs_sound hA vs
  | _, _, .var e body, _, _, hA => analyzeMR_sound body _ _ (hA.cons (exprAbs_sound hA e))

/-- Soundness of the multi-return range analysis: when every register input lies in its
    interval, every returned value lies in its returned interval. -/
theorem rangeAnalysisMR_sound (ivs : HVector (fun _ => Iv) Γ) {ts : List JasminTy}
    (c : MultiReturnCom jasminDialect Γ ts) (V : Ctxt.Valuation Γ)
    (hV : ∀ (w : Nat) (v : Ctxt.Var Γ (.reg w)), (hget ivs v).Mem w (v.lookup V)) :
    ValsMem (rangeAnalysisMR ivs c).2 (c.denote V) := by
  refine analyzeMR_sound c _ V ?_
  intro u v
  rw [hget_ofIvs]
  cases u with
  | reg w => exact ⟨hV w v, SymOK.none _ _ _⟩
  | _ => trivial

/-- The returned intervals lie in `outs`. -/
def retsOk (s : Bool) (A : AEnv Γ) : {ts : List JasminTy} →
    HVector (fun ty => Ctxt.Var Γ ty) ts → HVector (fun _ => Iv) ts → Bool
  | [], .nil, .nil => true
  | t :: _, .cons v vs, .cons o os => retOk t (hget A v).1 o && retsOk s A vs os

/-- The bounds check of a multi-return program from the abstract environment `A`. -/
def checkMR (s : Bool) : {Γ : JCtxt} → {ts : List JasminTy} → AEnv Γ →
    MultiReturnCom jasminDialect Γ ts → HVector (fun _ => Iv) ts → Bool
  | _, _, A, .ret vs, outs => retsOk s A vs outs
  | _, _, A, .var e body, outs =>
    bindOk s A e.op e.args &&
      checkMR s (HVector.cons (f := fun _ => AVal) (exprAbs A e) A) body outs

/-- The bounds check of a multi-return program from the input intervals `ivs`, over the
    intervals of `rangeAnalysisMR ivs c`. -/
def boundsOkMR (s : Bool) (ivs : HVector (fun _ => Iv) Γ) {ts : List JasminTy}
    (c : MultiReturnCom jasminDialect Γ ts) (outs : HVector (fun _ => Iv) ts) : Bool :=
  checkMR s (AEnv.ofIvs ivs) c outs

theorem retsOk_sound (hZ : ZOK A s V Z) : ∀ {ts : List JasminTy}
    (vs : HVector (fun ty => Ctxt.Var Γ ty) ts) (outs : HVector (fun _ => Iv) ts),
    retsOk s A vs outs = true →
    zvals s (MultiReturnCom.lookupVars vs V) = lookupZ vs Z ∧
      ValsIn s outs (MultiReturnCom.lookupVars vs V)
  | [], .nil, .nil, _ => ⟨rfl, trivial⟩
  | _ :: _, .cons v vs, .cons _ os, h => by
    replace h := (Bool.and_eq_true _ _).mp h
    obtain ⟨hz, hi⟩ := hZ _ v
    obtain ⟨e, hr⟩ := retsOk_sound hZ vs os h.2
    refine ⟨?_, ivZ_of_retOk h.1 hi, hr⟩
    show HVector.cons _ _ = HVector.cons _ _
    rw [e, hz]

theorem checkMR_sound : ∀ {Γ : JCtxt} {ts : List JasminTy}
    (c : MultiReturnCom jasminDialect Γ ts) (A : AEnv Γ) (V : Ctxt.Valuation Γ) (Z : ZVec Γ)
    (outs : HVector (fun _ => Iv) ts), EnvOK A V → ZOK A s V Z →
    checkMR s A c outs = true →
    zvals s (c.denote V) = c.denoteZ Z ∧ ValsIn s outs (c.denote V)
  | _, _, .ret vs, _, _, _, outs, _, hZ, h => retsOk_sound hZ vs outs h
  | _, _, .var e body, _, _, _, outs, hA, hZ, h => by
    replace h := (Bool.and_eq_true _ _).mp h
    obtain ⟨hs1, hs2⟩ := bindOk_step_expr hA hZ e h.1
    exact checkMR_sound body _ _ _ outs hs1 hs2 h.2

/-- **The multi-return word program computes the integer program.** -/
theorem denoteMR_eq_denoteZ_of_boundsOk (s : Bool) (ivs : HVector (fun _ => Iv) Γ)
    {ts : List JasminTy} (c : MultiReturnCom jasminDialect Γ ts)
    (outs : HVector (fun _ => Iv) ts) (h : boundsOkMR s ivs c outs = true)
    (V : Ctxt.Valuation Γ) (hV : ValsIn s ivs V) :
    zvals s (c.denote V) = c.denoteZ (zvals s V) ∧ ValsIn s outs (c.denote V) :=
  checkMR_sound c _ V _ outs (envOK_ofIvs hV) (zok_ofIvs hV) h

/-! ## 8. Bounded blocks -/

/-- A multi-return program with input and output intervals, a decidable side condition
    `ok` and a specification `spec` over the integer readings: when `ok` holds and every
    input reading lies in its interval, every output reading lies in its interval and
    `spec` relates the input and output readings. -/
structure BoundedBlock where
  /-- The input context. -/
  Γ : JCtxt
  /-- The output types. -/
  ts : List JasminTy
  /-- The program. -/
  prog : MultiReturnCom jasminDialect Γ ts
  /-- The reading of words: `toInt` when `true`, `toNat` when `false`. -/
  signed : Bool
  /-- The input intervals. -/
  inIv : HVector (fun _ => Iv) Γ
  /-- The output intervals. -/
  outIv : HVector (fun _ => Iv) ts
  /-- The side condition. -/
  ok : Bool
  /-- The specification over the input and output readings. -/
  spec : ZVec Γ → ZVec ts → Prop
  /-- The correctness of the block under its side condition. -/
  denote_of_ok : ok = true → ∀ V : Ctxt.Valuation Γ, ValsIn signed inIv V →
    ValsIn signed outIv (prog.denote V) ∧ spec (zvals signed V) (zvals signed (prog.denote V))

/-- The bounded block of a multi-return program certified by `boundsOkMR`: its
    specification is that the output readings are the integer semantics `denoteZ`. -/
def BoundedBlock.ofBoundsOk (s : Bool) (ivs : HVector (fun _ => Iv) Γ) {ts : List JasminTy}
    (c : MultiReturnCom jasminDialect Γ ts) (outs : HVector (fun _ => Iv) ts) :
    BoundedBlock where
  Γ := Γ
  ts := ts
  prog := c
  signed := s
  inIv := ivs
  outIv := outs
  ok := boundsOkMR s ivs c outs
  spec zin zout := zout = c.denoteZ zin
  denote_of_ok h V hV :=
    ⟨(denoteMR_eq_denoteZ_of_boundsOk s ivs c outs h V hV).2,
      (denoteMR_eq_denoteZ_of_boundsOk s ivs c outs h V hV).1⟩

/-! ## 9. The `ComRange` checks through `boundsOk`

`bbMul64.take 12` is the product and Barrett reduction of `bbMul64`, ending at the
Barrett remainder; the rest of `bbMul64` is the conditional subtract of `p`, which reads
the sign bit of `r - p` by a logical shift and so lies outside the exact fragment. -/

/- On inputs below `p`, the product and Barrett reduction of `bbMul64` compute their
   integer semantics at 64 bits unsigned, with the remainder in `[0, 2p - 1]`. -/
#kat (build 64 [.reg 64, .reg 64] (bbMul64.take 12)).map (fun c =>
    boundsOk false (bbInputs 64) c (0, 4026531841))
  == some true

/- The low products of the Montgomery multiply of `bbMont32` wrap modulo `2^32`, so the
   program lies outside the exact fragment at 32 bits, unsigned or signed. -/
#kat (build 32 [.reg 32, .reg 32] bbMont32).map (fun c =>
    boundsOk false (bbInputs 32) c (0, 2013265920) || boundsOk true (bbInputs 32) c
      (0, 2013265920))
  == some false

/-! ## 10. The word schedules of the lazy NTT as bounded blocks

The side condition of a word schedule is the closed-form condition `WordSched.Ok`
(`SchedOk` or `SSchedOk`), decided on `ℕ`, and its correctness is `nttProgG_denote`;
`rangeAnalysis` is not run on the transform program. -/

section WordSched

open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate

/-- The interval vector with every entry `i`. -/
def hvConst (i : Iv) : (l : List JasminTy) → HVector (fun _ => Iv) l
  | [] => .nil
  | _ :: l => .cons i (hvConst i l)

/-- Entry `i` of an integer vector, `0` past its end. -/
def hvGetZ : {l : List JasminTy} → ZVec l → ℕ → ℤ
  | [], _, _ => 0
  | _ :: _, .cons z _, 0 => z
  | _ :: _, .cons _ zs, i + 1 => hvGetZ zs i

theorem hvGetZ_zvals (s : Bool) (w : ℕ) : ∀ (n : ℕ)
    (X : HVector (fun t => ⟦t⟧) (List.replicate n (Rw w))) (i : ℕ),
    hvGetZ (zvals s X) i = if i < n then rd s (hvGetG (Rw w) (0 : BitVec w) X i) else 0
  | 0, .nil, _ => rfl
  | _ + 1, .cons _ _, 0 => rfl
  | n + 1, .cons _ X, i + 1 => by
    show hvGetZ (zvals s X) i = _
    rw [hvGetZ_zvals s w n X i]
    simp only [Nat.add_lt_add_iff_right]
    rfl

theorem valsIn_const (s : Bool) (w : ℕ) (iv : Iv) : ∀ (n : ℕ)
    (X : HVector (fun t => ⟦t⟧) (List.replicate n (Rw w))),
    ValsIn s (hvConst iv _) X ↔ ∀ i < n,
      iv.1 ≤ rd s (hvGetG (Rw w) (0 : BitVec w) X i) ∧
        rd s (hvGetG (Rw w) (0 : BitVec w) X i) ≤ iv.2
  | 0, .nil => ⟨fun _ _ hi => absurd hi (Nat.not_lt_zero _), fun _ => trivial⟩
  | n + 1, .cons x X => by
    have e : ValsIn s (hvConst iv (List.replicate (n + 1) (Rw w))) (HVector.cons x X) ↔
        ivZ s (Rw w) iv x ∧ ValsIn s (hvConst iv _) X := Iff.rfl
    rw [e, valsIn_const s w iv n X]
    constructor
    · rintro ⟨h0, h⟩ i hi
      cases i with
      | zero => exact h0
      | succ i => exact h i (by omega)
    · intro h
      exact ⟨h 0 (by omega), fun i hi => h (i + 1) (by omega)⟩

theorem lanesVal_eq (w : ℕ) (g : ℕ → BitVec w) : ∀ (n off : ℕ)
    (X : Ctxt.Valuation (List.replicate n (Rw w))),
    (∀ i < n, g (off + i) = hvGetG (Rw w) (0 : BitVec w) X i) → lanesVal (Rw w) g n off = X
  | 0, _, .nil, _ => rfl
  | n + 1, off, .cons x X, h => by
    have h0 : g off = x := h 0 (by omega)
    have ih := lanesVal_eq w g n (off + 1) X (fun i hi => by
      rw [show off + 1 + i = off + (i + 1) by omega]
      exact h (i + 1) (by omega))
    rw [← ih, ← h0]
    rfl

/-- The reading of a word schedule: unsigned for `unsignedMont`, signed for
    `signedMont`. -/
def wordSigned : WordSched → Bool
  | .unsignedMont _ _ => false
  | .signedMont _ => true

theorem rd_wordSigned (sch : WordSched) (x : BitVec sch.width) :
    rd (wordSigned sch) x = sch.val x := by
  cases sch <;> rfl

/-- The specification of a word schedule over integer readings: every output lane is
    `nttSpec` of the input lanes modulo `q`. -/
def wordSchedSpec (P : NttParams) (sch : WordSched)
    (zin zout : ZVec (List.replicate (2 ^ P.logN) (Rw sch.width))) : Prop :=
  ∀ i < 2 ^ P.logN, ((hvGetZ zout i : ℤ) : ZMod P.q)
    = nttSpec (P.psi : ZMod P.q) P.layers P.logN (fun j => ((hvGetZ zin j : ℤ) : ZMod P.q)) i

theorem wordSchedBlock_denote (P : NttParams) (sch : WordSched)
    (hok : decide (P.Ok ∧ sch.Ok P) = true)
    (V : Ctxt.Valuation (List.replicate (2 ^ P.logN) (Rw sch.width)))
    (hV : ValsIn (wordSigned sch) (hvConst (0, (P.q : ℤ) - 1) _) V) :
    ValsIn (wordSigned sch) (hvConst (1 - (sch.bound P : ℤ), (sch.bound P : ℤ) - 1) _)
        ((nttProgG P sch).denote V) ∧
      wordSchedSpec P sch (zvals (wordSigned sch) V)
        (zvals (wordSigned sch) ((nttProgG P sch).denote V)) := by
  obtain ⟨hP, hs⟩ := of_decide_eq_true hok
  have hq : 0 < P.q := by have := hP.2.2.1; omega
  rw [valsIn_const] at hV
  let f : ℕ → ℕ := fun j =>
    if j < 2 ^ P.logN then (hvGetG (Rw sch.width) (0 : BitVec sch.width) V j).toNat else 0
  have hfj : ∀ j < 2 ^ P.logN,
      (f j : ℤ) = rd (wordSigned sch) (hvGetG (Rw sch.width) (0 : BitVec sch.width) V j) :=
    fun j hj => by
      simp only [f, if_pos hj]
      exact (rd_of_nonneg (hV j hj).1).symm
  have hf : ∀ j, f j < P.q := fun j => by
    by_cases hj : j < 2 ^ P.logN
    · have h1 := hfj j hj
      have h2 := (hV j hj).2
      omega
    · simp only [f, if_neg hj]
      exact hq
  have hVf : lanesVal (Rw sch.width) (fun j => BitVec.ofNat sch.width (f j)) (2 ^ P.logN) 0
      = V :=
    lanesVal_eq _ _ _ _ V (fun i hi => by
      simp only [f, Nat.zero_add, if_pos hi, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  have key := nttProgG_denote P hP sch hs f hf
  rw [hVf] at key
  refine ⟨(valsIn_const _ _ _ _ _).2 fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨h1, -⟩ := key i hi
    rw [rd_wordSigned]
    rw [abs_lt] at h1
    constructor <;> omega
  · obtain ⟨-, h2⟩ := key i hi
    rw [hvGetZ_zvals, if_pos hi, rd_wordSigned, h2]
    congr 1
    funext j
    rw [hvGetZ_zvals]
    split
    · rename_i hj
      rw [← hfj j hj, Int.cast_natCast]
    · rename_i hj
      simp [f, hj]

/-- A word schedule of the lazy NTT as a bounded block: inputs in `[0, q - 1]`, outputs
    below the schedule's bound in absolute value, side condition `P.Ok ∧ sch.Ok P`
    decided on `ℕ`, and correctness `nttProgG_denote`. -/
def wordSchedBlock (P : NttParams) (sch : WordSched) : BoundedBlock where
  Γ := List.replicate (2 ^ P.logN) (Rw sch.width)
  ts := List.replicate (2 ^ P.logN) (Rw sch.width)
  prog := nttProgG P sch
  signed := wordSigned sch
  inIv := hvConst (0, (P.q : ℤ) - 1) _
  outIv := hvConst (1 - (sch.bound P : ℤ), (sch.bound P : ℤ) - 1) _
  ok := decide (P.Ok ∧ sch.Ok P)
  spec := wordSchedSpec P sch
  denote_of_ok := wordSchedBlock_denote P sch

/-- The ML-KEM signed 16-bit word schedule passes its side condition by `decide`. -/
theorem wordSchedBlock_mlkemSigned_ok :
    (wordSchedBlock mlkemNtt (.signedMont mlkemSigned)).ok = true := by
  decide

/- From lanes below `mlkemSigned.bnd 6 = 7 q` in absolute value (`q = 3329`),
   `rangeAnalysisMR` bounds every returned lane of layer 6 of
   `nttProgSW mlkemNtt mlkemSigned` below `mlkemSigned.bnd 7 = 8 q` in absolute value,
   inside the signed 16-bit lane. -/
set_option kat.ms 3000 in
#kat
  let r := rangeAnalysisMR (hvConst (1 - 7 * 3329, 7 * 3329 - 1) _)
    (chainD (Rw 16) 256 (sLayerLaneProgW mlkemNtt mlkemSigned) [6] (Ctxt.Hom.id _))
  r.1.length == 256 * 17 &&
  r.2.all fun i => decide (1 - 8 * 3329 ≤ i.1 ∧ i.2 ≤ 8 * 3329 - 1) && fitsLane true 16 i

end WordSched

end CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact
