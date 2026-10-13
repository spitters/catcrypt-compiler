/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttWord

/-!
# The signed Montgomery NTT lowered to `jasminDialect` words

The signed schedule of the negacyclic NTT keeps every lane as a signed
representative in a `w`-bit two's-complement word, multiplies by a centred
Montgomery twiddle in a `2 w`-bit word, and reduces with the signed Montgomery
reduction of radix `2 ^ w`:
`u = (a − t · q) >> w` with `t = (a · q') mods 2 ^ w` and `q · q' ≡ 1 (mod 2 ^ w)`.
The butterfly is `x + u` on the lower lane and `x − u` on the upper lane, with no
offset.  This is the forward NTT of the ML-KEM reference implementation at
`w = 16`, `q = 3329`, `q' = 62209` (the reference's `QINV = −3327`).

A schedule `SignedSched` fixes the word width, the Montgomery constant and a
per-layer bound table; `SSchedOk` is its decidable side condition.  The bound
theorem `schedule_bounds` and the congruence theorem `sRun_cast` are proved once
over the schedule, and `nttProgSW_denote` lowers the schedule to a
`MultiReturnCom jasminDialect` program on `2 ^ M` lanes of `w`-bit registers:
every output word, read as a signed integer, is below the table's last bound in
absolute value and congruent modulo `q` to `nttSpec`.  `mlkemSigned` is the
ML-KEM reference schedule, with bound `(ℓ + 1) · q` after `ℓ` layers.

The signed lowering and the unsigned lowering `nttProgUW` are the two instances of
`WordSched`; `nttProgG_denote` states their common correctness theorem.

The signed inverse transform runs the Gentleman–Sande layers `L − 1, …, 0` on
signed representatives: the lower lane is `u + v`, reduced by the signed Barrett
reduction `a − ((v · a + 2 ^ s / 2) >> s) · q` at the layers of a reduction
schedule, and the upper lane is the signed Montgomery product of `u − v` by the
centred inverse twiddle; a final signed Montgomery product scales every lane. A
`SignedInvSched` fixes the reduction schedule and a per-layer bound table;
`SInvOk` is its decidable side condition, and `inttProgSW_denote` states that every
output word is below the schedule's output bound and congruent modulo `q` to
`inttSpec`. `mlkemSignedInv` is the inverse NTT of the ML-KEM reference, with
Barrett at every layer and scaling `mont ^ 2 / 128`. `InvWordSched` collects the
unsigned and the signed inverse lowerings, with `inttProgG_denote`.

## Main definitions

* `SignedSched`, `SSchedOk` — a signed Montgomery schedule and its side condition.
* `zsN`, `zs`, `zEnc` — the twiddle of a block in Montgomery form, centred, and
  encoded as a `2 w`-bit constant.
* `smont`, `sLayer`, `sRun` — the signed Montgomery reduction, one layer and a run
  of layers on signed representatives.
* `sextW`, `smontW` — sign extension from `w` to `2 w` bits by a zero extension
  and two shifts, and the signed Montgomery multiply on words.
* `sLaneProg`, `semSW`, `sLayerLaneProgW`, `nttProgSW` — the butterfly lane
  schedule, one layer on word lanes, its lane schedules, and the transform program.
* `mlkemSigned`, `mldsaSigned` — the ML-KEM reference schedule and the ML-DSA
  signed 32-bit schedule.
* `WordSched`, `nttProgG` — the word schedules, unsigned and signed, and their
  transform program.
* `sbarrett`, `sbarrettW` — the signed Barrett reduction on integers and on words.
* `SignedInvSched`, `SInvOk`, `sInvLayer`, `sInvRun` — a signed inverse schedule,
  its side condition, and its layers on signed representatives.
* `smontTail`, `sbarrettTail`, `sInvLaneProg`, `invSemSW`, `inttProgSW` — the word
  schedules of the reductions, the inverse lanes, one inverse stage on word lanes,
  and the inverse transform program.
* `mlkemSignedInv` — the ML-KEM reference inverse schedule.
* `InvWordSched`, `inttProgG` — the inverse word schedules and their program.

## Main results

* `smont_mul_radix`, `smont_bound` — the signed Montgomery reduction divides by the
  radix modulo `q`, and its size.
* `schedule_bounds` — every lane after `k` layers is below the table's bound.
* `sRun_cast` — the run on signed representatives casts to `run` over `ZMod q`.
* `smontW_toInt` — on in-range operands the word multiply is `smont`.
* `nttProgSW_denote` — the signed word lowering computes `nttSpec`.
* `mlkemSigned_ok` — the ML-KEM reference schedule satisfies `SSchedOk`.
* `nttProgG_denote` — both word schedules compute `nttSpec`.
* `sbarrett_cast`, `sbarrett_bound`, `sbarrettW_toInt` — the Barrett reduction is
  congruent to its argument, its size, and its word form.
* `sInvRun_bounds`, `sInvRun_cast` — the inverse bound and congruence theorems.
* `inttProgSW_denote` — the signed inverse word lowering computes `inttSpec`.
* `mlkemSignedInv_ok`, `mlkemSignedInv_denote` — the ML-KEM reference inverse.
* `inttProgG_denote` — both inverse word schedules compute `inttSpec`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV pullV_id)
open CatCrypt.Crypto.Lattice.BitReversalGeneric (bitrev)

/-! ## 1. The signed Montgomery reduction on integers -/

/-- The signed Montgomery reduction of radix `2 ^ w`:
`(a − t · q) / 2 ^ w` with `t` the balanced residue of `a · qinv` modulo `2 ^ w`. -/
def smont (w q qinv : ℕ) (a : ℤ) : ℤ :=
  (a - (a * qinv).bmod (2 ^ w) * q) / (2 ^ w : ℕ)

/-- With `q · qinv ≡ 1 (mod 2 ^ w)` the division in `smont` is exact. -/
theorem smont_mul (w q qinv : ℕ) (hN : (q * qinv) % 2 ^ w = 1) (a : ℤ) :
    smont w q qinv a * (2 ^ w : ℕ) = a - (a * qinv).bmod (2 ^ w) * q := by
  have h1 : ((2 ^ w : ℕ) : ℤ) ∣ ((a * qinv).bmod (2 ^ w) - a * qinv) := Int.dvd_bmod_sub_self
  have h2 : ((2 ^ w : ℕ) : ℤ) ∣ ((1 : ℤ) - q * qinv) := by
    have h := Nat.div_add_mod (q * qinv) (2 ^ w)
    rw [hN] at h
    refine ⟨-((q * qinv / 2 ^ w : ℕ) : ℤ), ?_⟩
    have h' : ((q * qinv : ℕ) : ℤ) = ((2 ^ w : ℕ) : ℤ) * ((q * qinv / 2 ^ w : ℕ) : ℤ) + 1 := by
      exact_mod_cast h.symm
    push_cast at h' ⊢
    linarith
  have hd : ((2 ^ w : ℕ) : ℤ) ∣ (a - (a * qinv).bmod (2 ^ w) * q) := by
    have e : a - (a * qinv).bmod (2 ^ w) * q
        = a * (1 - q * qinv) - ((a * qinv).bmod (2 ^ w) - a * qinv) * q := by ring
    rw [e]
    exact dvd_sub (Dvd.dvd.mul_left h2 a) (Dvd.dvd.mul_right h1 _)
  exact Int.ediv_mul_cancel hd

/-- The Montgomery quotient is a balanced residue modulo `2 ^ w`. -/
theorem bmod_two_pow_bounds (w : ℕ) (x : ℤ) :
    -((2 ^ w : ℕ) : ℤ) ≤ 2 * x.bmod (2 ^ w) ∧ 2 * x.bmod (2 ^ w) < (2 ^ w : ℕ) := by
  have hp : 0 < 2 ^ w := Nat.two_pow_pos w
  have h1 := @Int.le_bmod x (2 ^ w) hp
  have h2 := @Int.bmod_lt x (2 ^ w) hp
  omega

/-- The size of the signed Montgomery reduction:
`2 · 2 ^ w · |smont a| ≤ 2 |a| + 2 ^ w · q`. -/
theorem smont_bound (w q qinv : ℕ) (hN : (q * qinv) % 2 ^ w = 1) (a : ℤ) :
    2 * (2 ^ w : ℕ) * |smont w q qinv a| ≤ 2 * |a| + (2 ^ w : ℕ) * q := by
  have he := smont_mul w q qinv hN a
  obtain ⟨h1, h2⟩ := bmod_two_pow_bounds w (a * qinv)
  generalize (a * qinv).bmod (2 ^ w) = t at he h1 h2
  generalize ((2 ^ w : ℕ) : ℤ) = R at he h1 h2 ⊢
  have hq : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  rw [show 2 * R * |smont w q qinv a| = 2 * |smont w q qinv a * R| by
    rw [abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ R by omega)]; ring, he]
  rcases abs_cases (a - t * q) with ⟨h, _⟩ | ⟨h, _⟩ <;>
  rcases abs_cases a with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [h, h'] <;> nlinarith

/-- The signed Montgomery reduction divides by the radix modulo `q`. -/
theorem smont_mul_radix (w q qinv : ℕ) (hN : (q * qinv) % 2 ^ w = 1) (a : ℤ) :
    ((smont w q qinv a : ℤ) : ZMod q) * ((2 ^ w : ℕ) : ZMod q) = (a : ZMod q) := by
  have h := congrArg (fun z : ℤ => (z : ZMod q)) (smont_mul w q qinv hN a)
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, ZMod.natCast_self, mul_zero,
    sub_zero] at h
  exact_mod_cast h

/-! ## 2. Signed schedules and their layers -/

/-- A signed Montgomery schedule: lanes are `w`-bit two's-complement words, the
Montgomery radix is `2 ^ w` with constant `qinv`, and every lane after `ℓ` layers
is below `bnd ℓ` in absolute value. -/
structure SignedSched where
  /-- The lane word width; products are formed at `2 w` bits. -/
  w : ℕ
  /-- The Montgomery constant, `q · qinv ≡ 1 (mod 2 ^ w)`. -/
  qinv : ℕ
  /-- The per-layer bound table. -/
  bnd : ℕ → ℕ

variable (P : NttParams) (T : SignedSched)

/-- The twiddle of block `k` in Montgomery form: `ψ ^ BitRev_L k · 2 ^ w mod q`. -/
def zsN (k : ℕ) : ℕ := P.psi ^ bitrev P.layers k * 2 ^ T.w % P.q

/-- The centred twiddle of block `k`: the representative of `zsN k` in
`[−q / 2, q / 2]`. -/
def zs (k : ℕ) : ℤ := if 2 * zsN P T k ≤ P.q then (zsN P T k : ℤ) else (zsN P T k : ℤ) - P.q

/-- Layer `ℓ` on signed representatives. -/
def sLayer (ℓ : ℕ) (f : ℕ → ℤ) (i : ℕ) : ℤ :=
  if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ) then
    f i + smont T.w P.q T.qinv
      (zs P T (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)))
        * f (i + 2 ^ (P.logN - 1 - ℓ)))
  else
    f (i - 2 ^ (P.logN - 1 - ℓ)) - smont T.w P.q T.qinv
      (zs P T (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))) * f i)

/-- `k` layers on signed representatives starting at layer `ℓ`. -/
def sRun : (k ℓ : ℕ) → (ℕ → ℤ) → ℕ → ℤ
  | 0, _, f => f
  | k + 1, ℓ, f => sRun k (ℓ + 1) (sLayer P T ℓ f)

/-- The side condition of a signed schedule, decidable on `ℕ`: the radix is
coprime to `q` with Montgomery constant `qinv`; for every layer count up to `L`
the bound fits a signed lane word and the Montgomery numerator fits a signed
double word; and the table grows at each layer by at least the size of a reduced
twiddle product. -/
def SSchedOk : Prop :=
  Nat.Coprime (2 ^ T.w) P.q ∧ (P.q * T.qinv) % 2 ^ T.w = 1 ∧
    (∀ ℓ, ℓ < P.layers + 1 →
      2 * T.bnd ℓ ≤ 2 ^ T.w ∧ T.bnd ℓ * P.q + 2 ^ T.w * P.q < 2 ^ (2 * T.w)) ∧
    ∀ ℓ, ℓ < P.layers → T.bnd ℓ ≤ T.bnd (ℓ + 1) ∧
      T.bnd ℓ * P.q + 2 ^ T.w * P.q ≤ 2 * 2 ^ T.w * (T.bnd (ℓ + 1) - T.bnd ℓ)

instance : Decidable (SSchedOk P T) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem zsN_lt (hq : 0 < P.q) (k : ℕ) : zsN P T k < P.q := Nat.mod_lt _ hq

/-- The centred twiddle is at most `q / 2` in absolute value. -/
theorem zs_abs (hq : 0 < P.q) (k : ℕ) : 2 * |zs P T k| ≤ P.q := by
  have h := zsN_lt P T hq k
  unfold zs
  split
  · rw [abs_of_nonneg (by positivity)]; omega
  · rw [abs_of_neg (by omega)]; omega

/-- The centred twiddle is `ψ ^ BitRev_L k · 2 ^ w` in `ZMod q`. -/
theorem zs_cast (k : ℕ) :
    ((zs P T k : ℤ) : ZMod P.q) = ((P.psi ^ bitrev P.layers k * 2 ^ T.w : ℕ) : ZMod P.q) := by
  unfold zs
  split
  · rw [Int.cast_natCast, zsN, ZMod.natCast_mod]
  · rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_self, sub_zero, zsN,
      ZMod.natCast_mod]

/-- A reduced twiddle product of a lane below `bnd ℓ` grows the bound by at most
`bnd (ℓ + 1) − bnd ℓ`. -/
theorem smont_zs_le (hT : SSchedOk P T) (hq : 0 < P.q) (ℓ : ℕ) (hl : ℓ < P.layers) (k : ℕ)
    (x : ℤ) (hx : |x| < T.bnd ℓ) :
    |smont T.w P.q T.qinv (zs P T k * x)| ≤ (T.bnd (ℓ + 1) : ℤ) - T.bnd ℓ := by
  obtain ⟨_, hN, _, hg⟩ := hT
  obtain ⟨hle, hgrow⟩ := hg ℓ hl
  have hb := smont_bound T.w P.q T.qinv hN (zs P T k * x)
  have hz := zs_abs P T hq k
  have hgrow' : (T.bnd ℓ : ℤ) * P.q + (2 ^ T.w : ℕ) * P.q
      ≤ 2 * (2 ^ T.w : ℕ) * ((T.bnd (ℓ + 1) : ℤ) - T.bnd ℓ) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) (Nat.sub_add_cancel hle)
    simp only [Nat.cast_add] at this
    have h2 : ((T.bnd ℓ * P.q + 2 ^ T.w * P.q : ℕ) : ℤ)
        ≤ ((2 * 2 ^ T.w * (T.bnd (ℓ + 1) - T.bnd ℓ) : ℕ) : ℤ) := by exact_mod_cast hgrow
    push_cast [Nat.cast_sub hle] at h2 ⊢
    linarith
  have hR : (0 : ℤ) < 2 * (2 ^ T.w : ℕ) := by positivity
  have hzx : 2 * |zs P T k * x| ≤ P.q * |x| := by
    rw [abs_mul]; nlinarith [abs_nonneg x, abs_nonneg (zs P T k)]
  have hqx : (P.q : ℤ) * |x| ≤ T.bnd ℓ * P.q := by
    nlinarith [abs_nonneg x, (Int.natCast_nonneg P.q)]
  refine le_of_mul_le_mul_left ?_ hR
  linarith

/-- One layer on signed representatives below `bnd ℓ` stays below `bnd (ℓ + 1)`. -/
theorem sLayer_bound (hT : SSchedOk P T) (hq : 0 < P.q) (ℓ : ℕ) (hl : ℓ < P.layers)
    (f : ℕ → ℤ) (hf : ∀ j, |f j| < T.bnd ℓ) (i : ℕ) : |sLayer P T ℓ f i| < T.bnd (ℓ + 1) := by
  unfold sLayer
  generalize 2 ^ (P.logN - 1 - ℓ) = len
  generalize 2 ^ ℓ + i / (len + len) = k
  split
  · have hu := smont_zs_le P T hT hq ℓ hl k _ (hf (i + len))
    have := hf i
    calc |f i + smont T.w P.q T.qinv (zs P T k * f (i + len))|
        ≤ |f i| + |smont T.w P.q T.qinv (zs P T k * f (i + len))| := abs_add_le _ _
      _ < T.bnd (ℓ + 1) := by linarith
  · have hu := smont_zs_le P T hT hq ℓ hl k _ (hf i)
    have := hf (i - len)
    calc |f (i - len) - smont T.w P.q T.qinv (zs P T k * f i)|
        ≤ |f (i - len)| + |smont T.w P.q T.qinv (zs P T k * f i)| := abs_sub _ _
      _ < T.bnd (ℓ + 1) := by linarith

/-- **The bound theorem.** From inputs below `bnd ℓ` in absolute value, after `k`
more layers every lane is below `bnd (ℓ + k)`. -/
theorem schedule_bounds (hT : SSchedOk P T) (hq : 0 < P.q) :
    ∀ (k ℓ : ℕ) (f : ℕ → ℤ), ℓ + k ≤ P.layers → (∀ j, |f j| < T.bnd ℓ) →
      ∀ j, |sRun P T k ℓ f j| < T.bnd (ℓ + k)
  | 0, _, _, _, hf => hf
  | k + 1, ℓ, f, hk, hf => by
      rw [show ℓ + (k + 1) = ℓ + 1 + k from by omega]
      exact schedule_bounds hT hq k (ℓ + 1) _ (by omega)
        (sLayer_bound P T hT hq ℓ (by omega) f hf)

/-- A reduced twiddle product is the twiddle times the operand in `ZMod q`. -/
theorem smont_zs_cast (hT : SSchedOk P T) (k : ℕ) (x : ℤ) :
    ((smont T.w P.q T.qinv (zs P T k * x) : ℤ) : ZMod P.q)
      = zt (P.psi : ZMod P.q) P.layers k * (x : ZMod P.q) := by
  obtain ⟨hcop, hN, _, _⟩ := hT
  have h := smont_mul_radix T.w P.q T.qinv hN (zs P T k * x)
  rw [Int.cast_mul, zs_cast] at h
  have hu : IsUnit ((2 ^ T.w : ℕ) : ZMod P.q) := ⟨ZMod.unitOfCoprime _ hcop, rfl⟩
  apply hu.mul_left_inj.mp
  rw [h, zt]
  push_cast
  ring

/-- One layer on signed representatives casts to `layerFn`. -/
theorem sLayer_cast (hT : SSchedOk P T) (ℓ : ℕ) (f : ℕ → ℤ) (i : ℕ) :
    ((sLayer P T ℓ f i : ℤ) : ZMod P.q)
      = layerFn (P.psi : ZMod P.q) P.layers P.logN ℓ (fun j => (f j : ZMod P.q)) i := by
  unfold sLayer layerFn
  generalize 2 ^ (P.logN - 1 - ℓ) = len
  generalize 2 ^ ℓ + i / (len + len) = k
  split
  · rw [Int.cast_add, smont_zs_cast P T hT]
  · rw [Int.cast_sub, smont_zs_cast P T hT]

/-- **The congruence theorem.** `k` layers on signed representatives cast to `k`
layers of `run` over `ZMod q`. -/
theorem sRun_cast (hT : SSchedOk P T) :
    ∀ (k ℓ : ℕ) (f : ℕ → ℤ) (i : ℕ), ((sRun P T k ℓ f i : ℤ) : ZMod P.q)
        = run (P.psi : ZMod P.q) P.layers P.logN k ℓ (fun j => (f j : ZMod P.q)) i
  | 0, _, _, _ => rfl
  | k + 1, ℓ, f, i => by
      have hlayer : (fun j => ((sLayer P T ℓ f j : ℤ) : ZMod P.q))
          = layerFn (P.psi : ZMod P.q) P.layers P.logN ℓ (fun j => (f j : ZMod P.q)) :=
        funext (sLayer_cast P T hT ℓ f)
      rw [sRun, sRun_cast hT k (ℓ + 1) _ i, hlayer]
      rfl

/-! ## 3. The signed Montgomery multiply on words -/

/-- Sign extension from `w` to `2 w` bits: a zero extension, a left shift by `w`
and an arithmetic right shift by `w`. -/
def sextW {w : ℕ} (x : BitVec w) : BitVec (2 * w) :=
  BitVec.sshiftRight (x.zeroExtend (2 * w) <<< w) w

theorem sextW_toInt {w : ℕ} (x : BitVec w) : (sextW x).toInt = x.toInt := by
  rw [sextW, BitVec.toInt_sshiftRight, BitVec.toInt_shiftLeft, Int.shiftRight_eq_div_pow]
  have hz : (x.zeroExtend (2 * w)).toNat = x.toNat := by
    rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
    exact lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [hz, Nat.shiftLeft_eq, BitVec.toInt_eq_toNat_bmod x]
  obtain ⟨c, hc⟩ := @Int.dvd_bmod_sub_self (x.toNat : ℤ) (2 ^ w)
  obtain ⟨h1, h2⟩ := bmod_two_pow_bounds w (x.toNat : ℤ)
  generalize (x.toNat : ℤ).bmod (2 ^ w) = t at hc h1 h2 ⊢
  have hR : (0 : ℤ) < (2 ^ w : ℕ) := by positivity
  have hRR : ((2 ^ (2 * w) : ℕ) : ℤ) = (2 ^ w : ℕ) * (2 ^ w : ℕ) := by
    push_cast; rw [two_mul, pow_add]
  have e : ((x.toNat * 2 ^ w : ℕ) : ℤ) = t * (2 ^ w : ℕ) + (2 ^ (2 * w) : ℕ) * (-c) := by
    rw [hRR]; push_cast at hc ⊢; linear_combination (-(2 : ℤ) ^ w) * hc
  rw [e, Int.add_mul_bmod_self_left, Int.bmod_eq_of_le_mul_two (by rw [hRR]; nlinarith)
    (by rw [hRR]; nlinarith), Int.mul_ediv_cancel _ (by omega)]

/-- Truncating a `2 w`-bit word to `w` bits takes its signed value to the balanced
residue modulo `2 ^ w`. -/
theorem toInt_zeroExtend_half {w : ℕ} (y : BitVec (2 * w)) :
    (y.zeroExtend w).toInt = y.toInt.bmod (2 ^ w) := by
  rw [BitVec.zeroExtend_eq_setWidth, BitVec.toInt_setWidth, BitVec.toInt_eq_toNat_bmod y,
    Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 (by omega))]

/-- The signed Montgomery multiply of `x` by the constant `z` on `w`-bit words:
`a = sext x · z` and `t = (a mod 2 ^ w) · qinv` in `w` bits, then
`(a − sext t · q) >> w` truncated to `w` bits. -/
def smontW (w q qinv z : ℕ) (x : BitVec w) : BitVec w :=
  (BitVec.sshiftRight (sextW x * BitVec.ofNat (2 * w) z
    - sextW ((sextW x * BitVec.ofNat (2 * w) z).zeroExtend w * BitVec.ofNat w qinv)
      * BitVec.ofNat (2 * w) q) w).zeroExtend w

/-- On in-range operands the signed Montgomery word multiply is `smont`. -/
theorem smontW_toInt (w q qinv z : ℕ) (x : BitVec w) (zv : ℤ)
    (hz : (BitVec.ofNat (2 * w) z).toInt = zv) (hq : 2 * q < 2 ^ (2 * w))
    (ha : 2 * |zv * x.toInt| + (2 ^ w : ℕ) * q < (2 ^ (2 * w) : ℕ))
    (hu : 2 * |smont w q qinv (zv * x.toInt)| < (2 ^ w : ℕ)) :
    (smontW w q qinv z x).toInt = smont w q qinv (zv * x.toInt) := by
  have hRR : ((2 ^ (2 * w) : ℕ) : ℤ) = (2 ^ w : ℕ) * (2 ^ w : ℕ) := by
    push_cast; rw [two_mul, pow_add]
  have hR : (0 : ℤ) < (2 ^ w : ℕ) := by positivity
  have hq0 : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  have hqv : (BitVec.ofNat (2 * w) q).toInt = q := by
    rw [BitVec.toInt_ofNat']
    exact Int.bmod_eq_of_le_mul_two (by omega) (by omega)
  have hA : (sextW x * BitVec.ofNat (2 * w) z).toInt = zv * x.toInt := by
    rw [BitVec.toInt_mul, sextW_toInt, hz, mul_comm]
    apply Int.bmod_eq_of_le_mul_two <;>
    rcases abs_cases (zv * x.toInt) with ⟨h, _⟩ | ⟨h, _⟩ <;> nlinarith
  unfold smontW
  generalize sextW x * BitVec.ofNat (2 * w) z = a at hA
  have hT : (sextW (a.zeroExtend w * BitVec.ofNat w qinv)).toInt
      = (zv * x.toInt * qinv).bmod (2 ^ w) := by
    rw [sextW_toInt, BitVec.toInt_mul, toInt_zeroExtend_half, hA, BitVec.toInt_ofNat',
      Int.bmod_mul_bmod, Int.mul_bmod_bmod]
  obtain ⟨ht1, ht2⟩ := bmod_two_pow_bounds w (zv * x.toInt * qinv)
  generalize sextW (a.zeroExtend w * BitVec.ofNat w qinv) = tw at hT
  set t := (zv * x.toInt * qinv).bmod (2 ^ w) with ht
  have hRq : ((2 ^ w : ℕ) : ℤ) * q < (2 ^ w : ℕ) * (2 ^ w : ℕ) := by
    rw [hRR] at ha; linarith [abs_nonneg (zv * x.toInt)]
  have hTQ : (tw * BitVec.ofNat (2 * w) q).toInt = t * q := by
    rw [BitVec.toInt_mul, hT, hqv]
    apply Int.bmod_eq_of_le_mul_two <;> rw [hRR] <;>
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * t + (2 ^ w : ℕ) by linarith) hq0,
      mul_nonneg (show (0 : ℤ) ≤ (2 ^ w : ℕ) - 2 * t by linarith) hq0]
  have hD : (a - tw * BitVec.ofNat (2 * w) q).toInt = zv * x.toInt - t * q := by
    rw [BitVec.toInt_sub, hA, hTQ]
    apply Int.bmod_eq_of_le_mul_two <;>
    rcases abs_cases (zv * x.toInt) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [hRR] at ha ⊢ <;> nlinarith
  have hS : (BitVec.sshiftRight (a - tw * BitVec.ofNat (2 * w) q) w).toInt
      = smont w q qinv (zv * x.toInt) := by
    rw [BitVec.toInt_sshiftRight, hD, Int.shiftRight_eq_div_pow, smont, ht]
  rw [toInt_zeroExtend_half, hS]
  exact Int.bmod_eq_of_le_mul_two
    (by rcases abs_cases (smont w q qinv (zv * x.toInt)) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)
    (by rcases abs_cases (smont w q qinv (zv * x.toInt)) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)

/-! ## 4. The butterfly lane schedule on `w`-bit words -/

/-- A `shlImm w n` expression. -/
def shlE {Γ : Ctxt jasminDialect} (w n : ℕ) (v : Var Γ (.reg w)) :
    Expr jasminDialect Γ (.reg w) :=
  { op := .shlImm w n, retTy_eq := rfl, args := .cons v .nil }

/-- A `sarImm w n` expression. -/
def sarE {Γ : Ctxt jasminDialect} (w n : ℕ) (v : Var Γ (.reg w)) :
    Expr jasminDialect Γ (.reg w) :=
  { op := .sarImm w n, retTy_eq := rfl, args := .cons v .nil }

/-- One signed butterfly lane on `w`-bit words: the signed Montgomery product `u`
of `a[ib]` by the constant `z`, then `a[ia] + u` when `up`, and `a[ia] − u`
otherwise. -/
def sLaneProg (w q qinv z : ℕ) : (n : ℕ) → ℕ → ℕ → Bool → Com jasminDialect (Ctxs w n) (.reg w)
  | 0, _, _, _ => .var (constE w 0) (.ret .here)
  | n + 1, ia, ib, up =>
      .var (castE w (2 * w) (laneVarG (Rw w) n ib))
      (.var (shlE (2 * w) w .here)
      (.var (sarE (2 * w) w .here)
      (.var (constE (2 * w) z)
      (.var (binE .mul (2 * w) (.there .here) .here)
      (.var (castE (2 * w) w .here)
      (.var (constE w qinv)
      (.var (binE .mul w (.there .here) .here)
      (.var (castE w (2 * w) .here)
      (.var (shlE (2 * w) w .here)
      (.var (sarE (2 * w) w .here)
      (.var (constE (2 * w) q)
      (.var (binE .mul (2 * w) (.there .here) .here)
      (.var (binE .sub (2 * w)
        (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .here)
      (.var (sarE (2 * w) w .here)
      (.var (castE (2 * w) w .here)
      (if up then
        .var (binE .add w (thereN [Rw w, Rw (2 * w), Rw (2 * w), Rw (2 * w), Rw (2 * w),
          Rw (2 * w), Rw (2 * w), Rw (2 * w), Rw w, Rw w, Rw w, Rw (2 * w), Rw (2 * w),
          Rw (2 * w), Rw (2 * w), Rw (2 * w)] (laneVarG (Rw w) n ia)) .here) (.ret .here)
      else
        .var (binE .sub w (thereN [Rw w, Rw (2 * w), Rw (2 * w), Rw (2 * w), Rw (2 * w),
          Rw (2 * w), Rw (2 * w), Rw (2 * w), Rw w, Rw w, Rw w, Rw (2 * w), Rw (2 * w),
          Rw (2 * w), Rw (2 * w), Rw (2 * w)] (laneVarG (Rw w) n ia)) .here) (.ret .here)))))))))))))))))

theorem sLaneProg_denote (w q qinv z n ia ib : ℕ) (up : Bool) (V : Valuation (Ctxs w (n + 1))) :
    (sLaneProg w q qinv z (n + 1) ia ib up).denote V
      = if up then (show BitVec w from (laneVarG (Rw w) n ia).lookup V)
          + smontW w q qinv z ((laneVarG (Rw w) n ib).lookup V)
        else (show BitVec w from (laneVarG (Rw w) n ia).lookup V)
          - smontW w q qinv z ((laneVarG (Rw w) n ib).lookup V) := by
  cases up <;> rfl

/-! ## 5. One signed layer on word lanes and the transform program -/

/-- The centred twiddle of block `k` as a `2 w`-bit constant. -/
def zEnc (k : ℕ) : ℕ := (zs P T k % ((2 ^ (2 * T.w) : ℕ) : ℤ)).toNat

/-- Under `SSchedOk`, `2 q < 2 ^ (2 w)`. -/
theorem two_q_lt (hT : SSchedOk P T) (hq : 1 < P.q) : 2 * P.q < 2 ^ (2 * T.w) := by
  have h := (hT.2.2.1 0 (by omega)).2
  rcases Nat.eq_zero_or_pos T.w with hw | hw
  · rw [hw] at h; simp at h; omega
  · have : 2 ≤ 2 ^ T.w := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ T.w := Nat.pow_le_pow_right (by norm_num) hw
    nlinarith

theorem zEnc_toInt (hT : SSchedOk P T) (hq : 1 < P.q) (k : ℕ) :
    (BitVec.ofNat (2 * T.w) (zEnc P T k)).toInt = zs P T k := by
  have hz := zs_abs P T (by omega) k
  have h2 := two_q_lt P T hT hq
  have hpos : (0 : ℤ) < ((2 ^ (2 * T.w) : ℕ) : ℤ) := by positivity
  rw [BitVec.toInt_ofNat', zEnc, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)),
    Int.emod_bmod]
  have h2' : (2 * P.q : ℤ) < ((2 ^ (2 * T.w) : ℕ) : ℤ) := by exact_mod_cast h2
  exact Int.bmod_eq_of_le_mul_two
    (by rcases abs_cases (zs P T k) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)
    (by rcases abs_cases (zs P T k) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)

/-- On a lane below `bnd ℓ`, the signed Montgomery word multiply by a twiddle is
`smont`. -/
theorem smontW_zs (hT : SSchedOk P T) (hq : 1 < P.q) (ℓ : ℕ) (hl : ℓ < P.layers) (k : ℕ)
    (x : BitVec T.w) (hx : |x.toInt| < T.bnd ℓ) :
    (smontW T.w P.q T.qinv (zEnc P T k) x).toInt = smont T.w P.q T.qinv (zs P T k * x.toInt) := by
  have hz := zs_abs P T (by omega) k
  have hprod := (hT.2.2.1 ℓ (by omega)).2
  have hfit := (hT.2.2.1 (ℓ + 1) (by omega)).1
  have hu := smont_zs_le P T hT (by omega) ℓ hl k _ hx
  refine smontW_toInt _ _ _ _ x _ (zEnc_toInt P T hT hq k) (two_q_lt P T hT hq) ?_ ?_
  · have hzx : 2 * |zs P T k * x.toInt| ≤ P.q * |x.toInt| := by
      rw [abs_mul]; nlinarith [abs_nonneg x.toInt, abs_nonneg (zs P T k)]
    have hqx : (P.q : ℤ) * |x.toInt| ≤ T.bnd ℓ * P.q := by
      nlinarith [abs_nonneg x.toInt, (Int.natCast_nonneg P.q)]
    have hprod' : ((T.bnd ℓ * P.q + 2 ^ T.w * P.q : ℕ) : ℤ) < ((2 ^ (2 * T.w) : ℕ) : ℤ) := by
      exact_mod_cast hprod
    push_cast at hprod' ⊢
    linarith
  · have hfit' : ((2 * T.bnd (ℓ + 1) : ℕ) : ℤ) ≤ ((2 ^ T.w : ℕ) : ℤ) := by exact_mod_cast hfit
    push_cast at hfit' ⊢
    linarith [abs_nonneg x.toInt]

/-- Layer `ℓ` of the signed schedule on word lanes. -/
def semSW (ℓ : ℕ) (g : ℕ → BitVec T.w) (i : ℕ) : BitVec T.w :=
  if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ) then
    g i + smontW T.w P.q T.qinv
      (zEnc P T (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))))
      (g (i + 2 ^ (P.logN - 1 - ℓ)))
  else
    g (i - 2 ^ (P.logN - 1 - ℓ)) - smontW T.w P.q T.qinv
      (zEnc P T (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)))) (g i)

/-- The lane schedules of signed layer `ℓ` on `2 ^ logN` word lanes. -/
def sLayerLaneProgW (ℓ i : ℕ) : Com jasminDialect (Ctxs T.w (2 ^ P.logN)) (.reg T.w) :=
  if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ) then
    sLaneProg T.w P.q T.qinv
      (zEnc P T (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))))
      (2 ^ P.logN) i (i + 2 ^ (P.logN - 1 - ℓ)) true
  else
    sLaneProg T.w P.q T.qinv
      (zEnc P T (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))))
      (2 ^ P.logN) (i - 2 ^ (P.logN - 1 - ℓ)) i false

theorem sLayerLaneProgW_denote (ℓ : ℕ) (hl : ℓ < P.logN) (g : ℕ → BitVec T.w) (i : ℕ)
    (hi : i < 2 ^ P.logN) :
    (sLayerLaneProgW P T ℓ i).denote (lanesVal (Rw T.w) g (2 ^ P.logN) 0)
      = semSW P T ℓ g i := by
  have hpart := layer_partner_lt P.logN ℓ i hl hi
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ P.logN = m + 1 := ⟨2 ^ P.logN - 1, by
    have := Nat.two_pow_pos P.logN; omega⟩
  unfold sLayerLaneProgW semSW
  generalize 2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) = k
  revert hpart hi
  rw [hm]
  intro hi hpart
  generalize 2 ^ (P.logN - 1 - ℓ) = len at hpart ⊢
  split
  · next hlt =>
    rw [sLaneProg_denote, if_pos rfl, laneVarG_lookup (Rw T.w) g m i 0 (by omega),
      laneVarG_lookup (Rw T.w) g m (i + len) 0 (by have := hpart hlt; omega)]
    simp only [Nat.zero_add]
  · next hlt =>
    rw [sLaneProg_denote, if_neg (by simp), laneVarG_lookup (Rw T.w) g m (i - len) 0 (by omega),
      laneVarG_lookup (Rw T.w) g m i 0 (by omega)]
    simp only [Nat.zero_add]

/-- On signed representatives below `bnd ℓ`, one word layer is `sLayer` read as
words. -/
theorem semSW_ofInt (hT : SSchedOk P T) (hq : 1 < P.q) (ℓ : ℕ) (hl : ℓ < P.layers)
    (f : ℕ → ℤ) (hf : ∀ j, |f j| < T.bnd ℓ) :
    semSW P T ℓ (fun j => BitVec.ofInt T.w (f j))
      = fun i => BitVec.ofInt T.w (sLayer P T ℓ f i) := by
  have hfit := (hT.2.2.1 ℓ (by omega)).1
  have hofi : ∀ j, (BitVec.ofInt T.w (f j)).toInt = f j := fun j => by
    have hfit' : ((2 * T.bnd ℓ : ℕ) : ℤ) ≤ ((2 ^ T.w : ℕ) : ℤ) := by exact_mod_cast hfit
    push_cast at hfit'
    have := hf j
    rw [BitVec.toInt_ofInt]
    exact Int.bmod_eq_of_le_mul_two
      (by push_cast; rcases abs_cases (f j) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)
      (by push_cast; rcases abs_cases (f j) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)
  funext i
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt]
  unfold semSW sLayer
  generalize 2 ^ (P.logN - 1 - ℓ) = len
  generalize 2 ^ ℓ + i / (len + len) = k
  split
  · rw [BitVec.toInt_add, hofi, smontW_zs P T hT hq ℓ hl k _ (by rw [hofi]; exact hf _), hofi]
  · rw [BitVec.toInt_sub, hofi, smontW_zs P T hT hq ℓ hl k _ (by rw [hofi]; exact hf _), hofi]

/-- The signed Montgomery transform program on `2 ^ logN` lanes of `w`-bit words. -/
def nttProgSW : MultiReturnCom jasminDialect (Ctxs T.w (2 ^ P.logN)) (Ctxs T.w (2 ^ P.logN)) :=
  chainD (Rw T.w) (2 ^ P.logN) (sLayerLaneProgW P T) (List.range P.layers) (Ctxt.Hom.id _)

theorem sRun_succ_last :
    ∀ (k ℓ : ℕ) (f : ℕ → ℤ), sRun P T (k + 1) ℓ f = sLayer P T (ℓ + k) (sRun P T k ℓ f)
  | 0, _, _ => rfl
  | k + 1, ℓ, f => by
      rw [sRun, sRun_succ_last k (ℓ + 1), show ℓ + 1 + k = ℓ + (k + 1) from by omega]
      rfl

theorem foldl_semSW (hT : SSchedOk P T) (hq : 1 < P.q) (f : ℕ → ℤ)
    (hf : ∀ j, |f j| < T.bnd 0) :
    ∀ k, k ≤ P.layers → (List.range k).foldl (fun g ℓ => semSW P T ℓ g)
        (fun j => BitVec.ofInt T.w (f j)) = fun j => BitVec.ofInt T.w (sRun P T k 0 f j)
  | 0, _ => rfl
  | k + 1, hk => by
      rw [List.range_succ, List.foldl_append, foldl_semSW hT hq f hf k (by omega),
        List.foldl_cons, List.foldl_nil, sRun_succ_last, Nat.zero_add]
      have hb := schedule_bounds P T hT (by omega) k 0 f (by omega) hf
      rw [Nat.zero_add] at hb
      exact semSW_ofInt P T hT hq k (by omega) _ hb

/-- **The signed word lowering.** For a parameter record satisfying
`NttParams.Ok`, a signed schedule satisfying `SSchedOk`, and inputs below `bnd 0`
in absolute value, every output word of `nttProgSW`, read as a signed integer, is
below `bnd L` in absolute value, and cast to `ZMod q` it is `nttSpec`. -/
theorem nttProgSW_denote (hP : P.Ok) (hT : SSchedOk P T) (f : ℕ → ℤ)
    (hf : ∀ j, |f j| < T.bnd 0) (i : ℕ) (hi : i < 2 ^ P.logN) :
    |(hvGetG (Rw T.w) (0 : BitVec T.w) ((nttProgSW P T).denote
        (lanesVal (Rw T.w) (fun j => BitVec.ofInt T.w (f j)) (2 ^ P.logN) 0)) i).toInt|
        < T.bnd P.layers ∧
    (((hvGetG (Rw T.w) (0 : BitVec T.w) ((nttProgSW P T).denote
        (lanesVal (Rw T.w) (fun j => BitVec.ofInt T.w (f j)) (2 ^ P.logN) 0)) i).toInt : ℤ)
        : ZMod P.q)
      = nttSpec (P.psi : ZMod P.q) P.layers P.logN (fun j => (f j : ZMod P.q)) i := by
  have hq : 1 < P.q := hP.2.2.1
  have hLM := hP.2.1
  rw [nttProgSW, chainD_denote (Rw T.w) (2 ^ P.logN) (0 : BitVec T.w) _ (semSW P T)
    (List.range P.layers)
    (fun ℓ hℓ g j hj => sLayerLaneProgW_denote P T ℓ
      (by have := List.mem_range.mp hℓ; omega) g j hj)
    (Ctxt.Hom.id _) _ _ (pullV_id _)]
  erw [foldl_semSW P T hT hq f hf P.layers le_rfl]
  rw [hvGetG_lanesVal _ _ _ _ _ _ hi, Nat.zero_add]
  have hlt := schedule_bounds P T hT (by omega) P.layers 0 f (by omega) hf i
  rw [Nat.zero_add] at hlt
  have hfit := (hT.2.2.1 P.layers (by omega)).1
  have hfit' : ((2 * T.bnd P.layers : ℕ) : ℤ) ≤ ((2 ^ T.w : ℕ) : ℤ) := by exact_mod_cast hfit
  push_cast at hfit'
  have hval : (BitVec.ofInt T.w (sRun P T P.layers 0 f i)).toInt = sRun P T P.layers 0 f i := by
    rw [BitVec.toInt_ofInt]
    exact Int.bmod_eq_of_le_mul_two
      (by push_cast; rcases abs_cases (sRun P T P.layers 0 f i) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)
      (by push_cast; rcases abs_cases (sRun P T P.layers 0 f i) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)
  rw [hval]
  refine ⟨hlt, ?_⟩
  rw [sRun_cast P T hT P.layers 0 f i]
  exact run_spec _ P.layers P.logN (P.psi_pow hP) hP.1 hLM _ i hi

/-! ## 6. The ML-KEM reference schedule -/

/-- The forward NTT schedule of the ML-KEM reference implementation: signed 16-bit
lanes, radix `2 ^ 16`, Montgomery constant `62209 = −3327 mod 2 ^ 16`, and bound
`(ℓ + 1) · q` after `ℓ` layers. -/
def mlkemSigned : SignedSched := ⟨16, 62209, fun ℓ => (ℓ + 1) * 3329⟩

theorem mlkemSigned_ok : SSchedOk mlkemNtt mlkemSigned := by decide

/-- The ML-KEM reference schedule on signed 16-bit words: from inputs below `q` in
absolute value, every output word is below `8 q` in absolute value and is
`nttSpec` at `ψ = 17`, `L = 7` modulo `q`. -/
theorem mlkemSigned_denote (f : ℕ → ℤ) (hf : ∀ j, |f j| < 3329) (i : ℕ) (hi : i < 256) :
    |(hvGetG (Rw 16) (0 : BitVec 16) ((nttProgSW mlkemNtt mlkemSigned).denote
        (lanesVal (Rw 16) (fun j => BitVec.ofInt 16 (f j)) 256 0)) i).toInt| < 8 * 3329 ∧
    (((hvGetG (Rw 16) (0 : BitVec 16) ((nttProgSW mlkemNtt mlkemSigned).denote
        (lanesVal (Rw 16) (fun j => BitVec.ofInt 16 (f j)) 256 0)) i).toInt : ℤ) : ZMod 3329)
      = nttSpec (17 : ZMod 3329) 7 8 (fun j => (f j : ZMod 3329)) i :=
  nttProgSW_denote mlkemNtt mlkemSigned mlkemNtt_ok mlkemSigned_ok f
    (fun j => by simpa [mlkemSigned] using hf j) i hi

/-! ## 7. Word schedules -/

/-- A word schedule of the lazy Montgomery NTT: unsigned representatives in
`S.w`-bit words with offset subtraction (`nttProgUW`), or signed representatives in
`w`-bit words (`nttProgSW`). -/
inductive WordSched where
  /-- The unsigned schedule `S` with radix `2 ^ logR` on `S.w`-bit lanes. -/
  | unsignedMont (S : LazySched) (logR : ℕ)
  /-- The signed schedule `T` on `T.w`-bit lanes. -/
  | signedMont (T : SignedSched)

/-- The lane word width of a word schedule. -/
def WordSched.width : WordSched → ℕ
  | .unsignedMont S _ => S.w
  | .signedMont T => T.w

/-- The integer a lane word stands for: its unsigned value, or its signed value. -/
def WordSched.val : (s : WordSched) → BitVec s.width → ℤ
  | .unsignedMont _ _, x => (x.toNat : ℤ)
  | .signedMont _, x => x.toInt

/-- The bound on the absolute value of every output lane. -/
def WordSched.bound : WordSched → ℕ
  | .unsignedMont S _ => bnd P S P.layers
  | .signedMont T => T.bnd P.layers

/-- The side condition of a word schedule, decidable on `ℕ`. -/
def WordSched.Ok : WordSched → Prop
  | .unsignedMont S logR => SchedOk P S ∧ UWordOk P S logR
  | .signedMont T => SSchedOk P T ∧ P.q ≤ T.bnd 0

instance : (s : WordSched) → Decidable (s.Ok P)
  | .unsignedMont S logR => inferInstanceAs (Decidable (SchedOk P S ∧ UWordOk P S logR))
  | .signedMont T => inferInstanceAs (Decidable (SSchedOk P T ∧ P.q ≤ T.bnd 0))

/-- The transform program of a word schedule on `2 ^ logN` lanes. -/
def nttProgG : (s : WordSched) →
    MultiReturnCom jasminDialect (Ctxs s.width (2 ^ P.logN)) (Ctxs s.width (2 ^ P.logN))
  | .unsignedMont S logR => nttProgUW P S logR
  | .signedMont T => nttProgSW P T

/-- **Both word lowerings compute the transform.** For a word schedule satisfying
its side condition and inputs below `q`, every output lane stands for an integer
below the schedule's bound in absolute value, congruent modulo `q` to
`nttSpec`. -/
theorem nttProgG_denote (hP : P.Ok) (s : WordSched) (hs : s.Ok P) (f : ℕ → ℕ)
    (hf : ∀ j, f j < P.q) (i : ℕ) (hi : i < 2 ^ P.logN) :
    |s.val (hvGetG (Rw s.width) (0 : BitVec s.width) ((nttProgG P s).denote
        (lanesVal (Rw s.width) (fun j => BitVec.ofNat s.width (f j)) (2 ^ P.logN) 0)) i)|
        < s.bound P ∧
    ((s.val (hvGetG (Rw s.width) (0 : BitVec s.width) ((nttProgG P s).denote
        (lanesVal (Rw s.width) (fun j => BitVec.ofNat s.width (f j)) (2 ^ P.logN) 0)) i)
        : ℤ) : ZMod P.q)
      = nttSpec (P.psi : ZMod P.q) P.layers P.logN (fun j => (f j : ZMod P.q)) i := by
  cases s with
  | unsignedMont S logR =>
    obtain ⟨hS, hW⟩ := hs
    obtain ⟨h1, h2⟩ := nttProgUW_denote P S logR hP hS hW f hf i hi
    refine ⟨?_, ?_⟩
    · show |((_ : ℕ) : ℤ)| < (bnd P S P.layers : ℤ)
      rw [abs_of_nonneg (Int.natCast_nonneg _)]
      exact_mod_cast h1
    · show (((_ : ℕ) : ℤ) : ZMod P.q) = _
      rw [Int.cast_natCast]
      exact h2
  | signedMont T =>
    obtain ⟨hT, hb⟩ := hs
    have hofn : (fun j => BitVec.ofNat T.w (f j)) = fun j => BitVec.ofInt T.w (f j : ℤ) :=
      funext fun j => (BitVec.ofInt_natCast T.w (f j)).symm
    have h := nttProgSW_denote P T hP hT (fun j => (f j : ℤ))
      (fun j => by rw [abs_of_nonneg (Int.natCast_nonneg _)]; have := hf j; omega) i hi
    simp only [Int.cast_natCast] at h
    rw [← hofn] at h
    exact h

/-- The ML-KEM unsigned 16-bit word schedule satisfies its side condition. -/
theorem mlkemUnsignedWord_ok : (WordSched.unsignedMont mlkemLazy 16).Ok mlkemNtt :=
  ⟨mlkemLazy_ok, mlkemUWord_ok⟩

/-- The ML-KEM reference signed 16-bit word schedule satisfies its side condition. -/
theorem mlkemSignedWord_ok : (WordSched.signedMont mlkemSigned).Ok mlkemNtt :=
  ⟨mlkemSigned_ok, by decide⟩

/-- The ML-DSA unsigned 32-bit word schedule satisfies its side condition. -/
theorem mldsaUnsignedWord_ok : (WordSched.unsignedMont mldsaLazy 32).Ok mldsaNtt :=
  ⟨mldsaLazy_ok, mldsaUWord_ok⟩

/-- The ML-DSA signed schedule: signed 32-bit lanes, radix `2 ^ 32`, Montgomery
constant `58728449 = q⁻¹ mod 2 ^ 32`, and bound `(ℓ + 1) · q` after `ℓ` layers. -/
def mldsaSigned : SignedSched := ⟨32, 58728449, fun ℓ => (ℓ + 1) * 8380417⟩

/-- The ML-DSA signed 32-bit word schedule satisfies its side condition. -/
theorem mldsaSignedWord_ok : (WordSched.signedMont mldsaSigned).Ok mldsaNtt := by decide

/-! ## 8. The signed Barrett reduction -/

/-- The signed Barrett reduction of shift `s` and constant `v`:
`a − t · q` with `t = (v · a + ⌊2 ^ s / 2⌋) >> s`. The ML-KEM reference is
`s = 26`, `v = 20159 = round(2 ^ 26 / q)`. -/
def sbarrett (s q v : ℕ) (a : ℤ) : ℤ :=
  a - ((v * a + (2 ^ s / 2 : ℕ)) / (2 ^ s : ℕ)) * q

/-- The signed Barrett reduction is congruent to its argument modulo `q`. -/
theorem sbarrett_cast (s q v : ℕ) (a : ℤ) : ((sbarrett s q v a : ℤ) : ZMod q) = (a : ZMod q) := by
  simp [sbarrett]

/-- The size of the signed Barrett reduction: for a constant with
`2 · |2 ^ s − q · v| ≤ q`, `2 · 2 ^ s · |sbarrett a| ≤ q · |a| + q · 2 ^ s`. -/
theorem sbarrett_bound (s q v : ℕ) (hv : 2 * |((2 ^ s : ℕ) : ℤ) - q * v| ≤ q) (a : ℤ) :
    2 * (2 ^ s : ℕ) * |sbarrett s q v a| ≤ q * |a| + q * (2 ^ s : ℕ) := by
  have hD : (0 : ℤ) < (2 ^ s : ℕ) := by positivity
  have hh : ((2 ^ s : ℕ) : ℤ) - 1 ≤ 2 * ((2 ^ s / 2 : ℕ) : ℤ) ∧
      2 * ((2 ^ s / 2 : ℕ) : ℤ) ≤ (2 ^ s : ℕ) := by
    rcases Nat.eq_zero_or_pos s with h0 | hs
    · subst h0; norm_num
    · have : 2 ^ s = 2 * 2 ^ (s - 1) := by rw [← pow_succ']; congr 1; omega
      rw [this]; push_cast; omega
  have hdm := Int.mul_ediv_add_emod ((v : ℤ) * a + (2 ^ s / 2 : ℕ)) (2 ^ s : ℕ)
  have hr0 := Int.emod_nonneg ((v : ℤ) * a + (2 ^ s / 2 : ℕ)) (ne_of_gt hD)
  have hr1 := Int.emod_lt_of_pos ((v : ℤ) * a + (2 ^ s / 2 : ℕ)) hD
  unfold sbarrett
  generalize ((v : ℤ) * a + (2 ^ s / 2 : ℕ)) / (2 ^ s : ℕ) = t at hdm
  generalize ((v : ℤ) * a + (2 ^ s / 2 : ℕ)) % (2 ^ s : ℕ) = ρ at hdm hr0 hr1
  generalize ((2 ^ s / 2 : ℕ) : ℤ) = h at hdm hh
  generalize ((2 ^ s : ℕ) : ℤ) = D at hdm hh hr1 hD hv ⊢
  have hq : (0 : ℤ) ≤ q := Int.natCast_nonneg q
  have he : 2 * D * (a - t * q) = 2 * (a * (D - q * v)) + q * (2 * ρ - 2 * h) := by
    linear_combination (-2 * (q : ℤ)) * hdm
  have hae : 2 * |a * (D - q * v)| ≤ q * |a| := by
    rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg (D - q * v)]
  have hrh : |2 * ρ - 2 * h| ≤ D := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [show 2 * D * |a - t * q| = |2 * D * (a - t * q)| by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℤ) < 2 * D)], he]
  calc |2 * (a * (D - q * v)) + q * (2 * ρ - 2 * h)|
      ≤ |2 * (a * (D - q * v))| + |q * (2 * ρ - 2 * h)| := abs_add_le _ _
    _ ≤ q * |a| + q * D := by
      have h2 : |2 * (a * (D - q * v))| = 2 * |a * (D - q * v)| := by rw [abs_mul, abs_two]
      have h3 : |(q : ℤ) * (2 * ρ - 2 * h)| ≤ q * D := by
        rw [abs_mul, abs_of_nonneg hq]; exact mul_le_mul_of_nonneg_left hrh hq
      linarith

/-- Two integers congruent modulo `m` have the same balanced residue. -/
theorem bmod_eq_of_modEq {a b : ℤ} {m : ℕ} (h : a ≡ b [ZMOD m]) : a.bmod m = b.bmod m := by
  unfold Int.bmod
  rw [h.eq]

/-- The signed Barrett reduction on `w`-bit words, with products at `2 w` bits:
`a = sext x`, `t = (a · v + ⌊2 ^ s / 2⌋) >> s`, and `a − t · q` truncated to
`w` bits. -/
def sbarrettW (w s q v : ℕ) (x : BitVec w) : BitVec w :=
  (sextW x - BitVec.sshiftRight (sextW x * BitVec.ofNat (2 * w) v
    + BitVec.ofNat (2 * w) (2 ^ s / 2)) s * BitVec.ofNat (2 * w) q).zeroExtend w

/-- When `v · x + ⌊2 ^ s / 2⌋` fits a signed double word and the result fits a
signed word, the Barrett word reduction is `sbarrett`. -/
theorem sbarrettW_toInt (w s q v : ℕ) (x : BitVec w)
    (ha : 2 * |(v : ℤ) * x.toInt + (2 ^ s / 2 : ℕ)| < (2 ^ (2 * w) : ℕ))
    (hr : 2 * |sbarrett s q v x.toInt| < (2 ^ w : ℕ)) :
    (sbarrettW w s q v x).toInt = sbarrett s q v x.toInt := by
  have hA : (sextW x * BitVec.ofNat (2 * w) v + BitVec.ofNat (2 * w) (2 ^ s / 2)).toInt
      = (v : ℤ) * x.toInt + (2 ^ s / 2 : ℕ) := by
    rw [BitVec.toInt_add, BitVec.toInt_mul, sextW_toInt, BitVec.toInt_ofNat', BitVec.toInt_ofNat',
      Int.mul_bmod_bmod, Int.bmod_add_bmod, Int.add_bmod_bmod, mul_comm]
    generalize (v : ℤ) * x.toInt + (2 ^ s / 2 : ℕ) = X at ha ⊢
    apply Int.bmod_eq_of_le_mul_two <;>
    rcases abs_cases X with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  unfold sbarrettW
  generalize sextW x * BitVec.ofNat (2 * w) v + BitVec.ofNat (2 * w) (2 ^ s / 2) = y at hA
  have hT : (BitVec.sshiftRight y s).toInt = ((v : ℤ) * x.toInt + (2 ^ s / 2 : ℕ)) / (2 ^ s : ℕ) := by
    rw [BitVec.toInt_sshiftRight, hA, Int.shiftRight_eq_div_pow]
  generalize BitVec.sshiftRight y s = tw at hT
  have hmod : (sextW x - tw * BitVec.ofNat (2 * w) q).toInt ≡ sbarrett s q v x.toInt
      [ZMOD ((2 ^ (2 * w) : ℕ) : ℤ)] := by
    rw [BitVec.toInt_sub, BitVec.toInt_mul, sextW_toInt, hT, BitVec.toInt_ofNat', sbarrett]
    refine (Int.bmod_emod ..).trans ?_
    refine Int.ModEq.sub_left _ ((Int.bmod_emod ..).trans ?_)
    exact Int.ModEq.mul_left _ (Int.bmod_emod ..)
  rw [toInt_zeroExtend_half, bmod_eq_of_modEq (m := 2 ^ w)
    (hmod.of_dvd (by exact_mod_cast Nat.pow_dvd_pow 2 (by omega)))]
  exact Int.bmod_eq_of_le_mul_two
    (by rcases abs_cases (sbarrett s q v x.toInt) with ⟨h, _⟩ | ⟨h, _⟩ <;> push_cast at hr ⊢ <;>
      linarith)
    (by rcases abs_cases (sbarrett s q v x.toInt) with ⟨h, _⟩ | ⟨h, _⟩ <;> push_cast at hr ⊢ <;>
      linarith)

/-! ## 9. Signed inverse schedules and their layers -/

/-- A signed inverse schedule: lanes are `w`-bit two's-complement words, the
Montgomery radix is `2 ^ w` with constant `qinv`, the Barrett reduction has shift
`bshift` and constant `bconst`, inverse layer `ℓ` reduces its lower lane by Barrett
exactly when `red ℓ`, every lane entering inverse layer `ℓ` is below `bnd (ℓ + 1)`
and leaving it below `bnd ℓ` in absolute value, and every output lane of the
scaling stage is below `bout`. -/
structure SignedInvSched where
  /-- The lane word width; products are formed at `2 w` bits. -/
  w : ℕ
  /-- The Montgomery constant, `q · qinv ≡ 1 (mod 2 ^ w)`. -/
  qinv : ℕ
  /-- The Barrett shift. -/
  bshift : ℕ
  /-- The Barrett constant, `round (2 ^ bshift / q)`. -/
  bconst : ℕ
  /-- The reduction schedule: the inverse layers whose lower lane is Barrett-reduced. -/
  red : ℕ → Bool
  /-- The per-layer bound table. -/
  bnd : ℕ → ℕ
  /-- The bound on the output of the scaling stage. -/
  bout : ℕ

variable (U : SignedInvSched)

/-- The balanced residue modulo `q` is at most `q / 2` in absolute value. -/
theorem two_abs_bmod_le (x : ℤ) (q : ℕ) (hq : 0 < q) : 2 * |x.bmod q| ≤ q := by
  have h1 := @Int.le_bmod x q hq
  have h2 := @Int.bmod_lt x q hq
  rcases abs_cases (x.bmod q) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

theorem bmod_cast (x : ℤ) (q : ℕ) : ((x.bmod q : ℤ) : ZMod q) = (x : ZMod q) :=
  (ZMod.intCast_eq_intCast_iff' _ _ _).mpr Int.bmod_emod

/-- The inverse twiddle of block `k` in Montgomery form, centred: the balanced
residue of `ψ ^ (2 ^ (L + 1) − BitRev_L k) · 2 ^ w` modulo `q`. -/
def zsInvS (k : ℕ) : ℤ :=
  ((P.psi ^ (2 ^ (P.layers + 1) - bitrev P.layers k) * 2 ^ U.w : ℕ) : ℤ).bmod P.q

/-- The scaling constant `s` in Montgomery form, centred: the balanced residue of
`s · 2 ^ w` modulo `q`. -/
def zscS (s : ℕ) : ℤ := ((s * 2 ^ U.w : ℕ) : ℤ).bmod P.q

/-- Inverse layer `ℓ` on signed representatives: the lower lane is `u + v`,
Barrett-reduced when `red ℓ`, and the upper lane is the signed Montgomery product
of `u − v` by the centred inverse twiddle. -/
def sInvLayer (ℓ : ℕ) (f : ℕ → ℤ) (i : ℕ) : ℤ :=
  if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ) then
    if U.red ℓ then sbarrett U.bshift P.q U.bconst (f i + f (i + 2 ^ (P.logN - 1 - ℓ)))
    else f i + f (i + 2 ^ (P.logN - 1 - ℓ))
  else
    smont U.w P.q U.qinv
      (zsInvS P U (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)))
        * (f (i - 2 ^ (P.logN - 1 - ℓ)) - f i))

/-- Inverse layers `k − 1, …, 0` on signed representatives. -/
def sInvRun : (k : ℕ) → (ℕ → ℤ) → ℕ → ℤ
  | 0, f => f
  | k + 1, f => sInvRun k (sInvLayer P U k f)

/-- The side condition of a signed inverse schedule, decidable on `ℕ`: the
Montgomery constant and the Barrett constant are correct; every bound fits a signed
lane word; at each inverse layer a sum or difference of two lanes fits a signed
word, the Montgomery numerator and the Barrett product fit a signed double word,
and the bound table covers the reduced lanes; the scaling stage fits and is below
`bout`. -/
def SInvOk : Prop :=
  Nat.Coprime (2 ^ U.w) P.q ∧ (P.q * U.qinv) % 2 ^ U.w = 1 ∧ 2 * P.q < 2 ^ (2 * U.w) ∧
    2 * (((2 ^ U.bshift : ℕ) : ℤ) - P.q * U.bconst).natAbs ≤ P.q ∧
    (∀ ℓ, ℓ < P.layers + 1 → 2 * U.bnd ℓ ≤ 2 ^ U.w) ∧
    (∀ ℓ, ℓ < P.layers → 4 * U.bnd (ℓ + 1) ≤ 2 ^ U.w ∧
      2 * P.q * U.bnd (ℓ + 1) + 2 ^ U.w * P.q ≤ 2 * 2 ^ U.w * U.bnd ℓ ∧
      2 * P.q * U.bnd (ℓ + 1) + 2 ^ U.w * P.q < 2 ^ (2 * U.w) ∧
      (if U.red ℓ then
        P.q * (2 * U.bnd (ℓ + 1)) + P.q * 2 ^ U.bshift ≤ 2 * 2 ^ U.bshift * U.bnd ℓ ∧
          2 * (U.bconst * (2 * U.bnd (ℓ + 1)) + 2 ^ U.bshift / 2) < 2 ^ (2 * U.w)
      else 2 * U.bnd (ℓ + 1) ≤ U.bnd ℓ)) ∧
    P.q * U.bnd 0 + 2 ^ U.w * P.q ≤ 2 * 2 ^ U.w * U.bout ∧
    P.q * U.bnd 0 + 2 ^ U.w * P.q < 2 ^ (2 * U.w) ∧ 2 * U.bout ≤ 2 ^ U.w

instance : Decidable (SInvOk P U) := by unfold SInvOk; infer_instance

/-- A signed Montgomery product by a centred constant of an operand below `b` is
bounded by `q · b + 2 ^ w · q` over `2 · 2 ^ w`. -/
theorem smont_bmod_lt (w q qinv : ℕ) (hN : (q * qinv) % 2 ^ w = 1) (hq : 0 < q) (c : ℤ)
    (x : ℤ) (b : ℕ) (hx : |x| < b) :
    2 * (2 ^ w : ℕ) * |smont w q qinv (c.bmod q * x)| < q * b + (2 ^ w : ℕ) * q := by
  have hb := smont_bound w q qinv hN (c.bmod q * x)
  have hz := two_abs_bmod_le c q hq
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hzx : 2 * |c.bmod q * x| ≤ q * |x| := by
    rw [abs_mul]; nlinarith [abs_nonneg x, abs_nonneg (c.bmod q)]
  have hqx : (q : ℤ) * |x| < q * b := mul_lt_mul_of_pos_left hx hq'
  linarith

/-- One inverse layer on signed representatives below `bnd (ℓ + 1)` stays below
`bnd ℓ`. -/
theorem sInvLayer_bound (hU : SInvOk P U) (hq : 0 < P.q) (ℓ : ℕ) (hl : ℓ < P.layers)
    (f : ℕ → ℤ) (hf : ∀ j, |f j| < U.bnd (ℓ + 1)) (i : ℕ) :
    |sInvLayer P U ℓ f i| < U.bnd ℓ := by
  obtain ⟨_, hN, _, hv, _, hlay, _⟩ := hU
  obtain ⟨_, hup, _, hlow⟩ := hlay ℓ hl
  have hR : (0 : ℤ) < 2 * (2 ^ U.w : ℕ) := by positivity
  unfold sInvLayer
  generalize 2 ^ (P.logN - 1 - ℓ) = len
  generalize 2 ^ ℓ + i / (len + len) = k
  split
  · have hs : |f i + f (i + len)| < ((2 * U.bnd (ℓ + 1) : ℕ) : ℤ) := by
      have := abs_add_le (f i) (f (i + len))
      have := hf i; have := hf (i + len); push_cast; linarith
    cases hr : U.red ℓ
    · rw [hr] at hlow
      simp only [Bool.false_eq_true, if_false] at hlow ⊢
      have : ((2 * U.bnd (ℓ + 1) : ℕ) : ℤ) ≤ U.bnd ℓ := by exact_mod_cast hlow
      linarith
    · rw [hr] at hlow
      simp only [if_true] at hlow ⊢
      have hv' : 2 * |((2 ^ U.bshift : ℕ) : ℤ) - P.q * U.bconst| ≤ P.q := by
        rw [Int.abs_eq_natAbs]; exact_mod_cast hv
      have hb := sbarrett_bound U.bshift P.q U.bconst hv' (f i + f (i + len))
      have hq' : (0 : ℤ) < P.q := by exact_mod_cast hq
      have h1 : (P.q : ℤ) * |f i + f (i + len)| < P.q * ((2 * U.bnd (ℓ + 1) : ℕ) : ℤ) :=
        mul_lt_mul_of_pos_left hs hq'
      have h2 : ((P.q * (2 * U.bnd (ℓ + 1)) + P.q * 2 ^ U.bshift : ℕ) : ℤ)
          ≤ ((2 * 2 ^ U.bshift * U.bnd ℓ : ℕ) : ℤ) := by exact_mod_cast hlow.1
      have hD : (0 : ℤ) < 2 * (2 ^ U.bshift : ℕ) := by positivity
      refine lt_of_mul_lt_mul_left ?_ hD.le
      push_cast at h1 h2 hb ⊢
      linarith
  · have hd : |f (i - len) - f i| < ((2 * U.bnd (ℓ + 1) : ℕ) : ℤ) := by
      have := abs_sub (f (i - len)) (f i)
      have := hf i; have := hf (i - len); push_cast; linarith
    have hb := smont_bmod_lt U.w P.q U.qinv hN hq
      (((P.psi ^ (2 ^ (P.layers + 1) - bitrev P.layers k) * 2 ^ U.w : ℕ) : ℤ)) _ _ hd
    have h2 : ((2 * P.q * U.bnd (ℓ + 1) + 2 ^ U.w * P.q : ℕ) : ℤ)
        ≤ ((2 * 2 ^ U.w * U.bnd ℓ : ℕ) : ℤ) := by exact_mod_cast hup
    refine lt_of_mul_lt_mul_left ?_ hR.le
    unfold zsInvS
    push_cast at hb h2 ⊢
    linarith

/-- **The inverse bound theorem.** From inputs below `bnd k` in absolute value,
after inverse layers `k − 1, …, 0` every lane is below `bnd 0`. -/
theorem sInvRun_bounds (hU : SInvOk P U) (hq : 0 < P.q) :
    ∀ (k : ℕ) (f : ℕ → ℤ), k ≤ P.layers → (∀ j, |f j| < U.bnd k) →
      ∀ j, |sInvRun P U k f j| < U.bnd 0
  | 0, _, _, hf => hf
  | k + 1, f, hk, hf =>
      sInvRun_bounds hU hq k _ (by omega) (sInvLayer_bound P U hU hq k (by omega) f hf)

theorem zsInvS_cast (k : ℕ) :
    ((zsInvS P U k : ℤ) : ZMod P.q)
      = ((P.psi ^ (2 ^ (P.layers + 1) - bitrev P.layers k) * 2 ^ U.w : ℕ) : ZMod P.q) := by
  rw [zsInvS, bmod_cast, Int.cast_natCast]

/-- A signed Montgomery product by a centred constant `c · 2 ^ w` is `c` times the
operand in `ZMod q`. -/
theorem smont_bmod_cast (w q qinv : ℕ) (hcop : Nat.Coprime (2 ^ w) q)
    (hN : (q * qinv) % 2 ^ w = 1) (c : ℕ) (x : ℤ) :
    ((smont w q qinv ((((c * 2 ^ w : ℕ) : ℤ)).bmod q * x) : ℤ) : ZMod q)
      = (c : ZMod q) * (x : ZMod q) := by
  have h := smont_mul_radix w q qinv hN ((((c * 2 ^ w : ℕ) : ℤ)).bmod q * x)
  rw [Int.cast_mul, bmod_cast, Int.cast_natCast] at h
  have hu : IsUnit ((2 ^ w : ℕ) : ZMod q) := ⟨ZMod.unitOfCoprime _ hcop, rfl⟩
  apply hu.mul_left_inj.mp
  rw [h]
  push_cast
  ring

/-- One inverse layer on signed representatives casts to `invLayerFn`. -/
theorem sInvLayer_cast (hU : SInvOk P U) (ℓ : ℕ) (f : ℕ → ℤ) (i : ℕ) :
    ((sInvLayer P U ℓ f i : ℤ) : ZMod P.q)
      = invLayerFn (P.psi : ZMod P.q) P.layers P.logN ℓ (fun j => (f j : ZMod P.q)) i := by
  obtain ⟨hcop, hN, _⟩ := hU
  unfold sInvLayer invLayerFn
  generalize 2 ^ (P.logN - 1 - ℓ) = len
  generalize 2 ^ ℓ + i / (len + len) = k
  split
  · cases U.red ℓ <;> simp [sbarrett_cast]
  · rw [zsInvS, smont_bmod_cast _ _ _ hcop hN, ztInv, Int.cast_sub]
    push_cast
    ring

/-- **The inverse congruence theorem.** Inverse layers `k − 1, …, 0` on signed
representatives cast to `invRun` over `ZMod q`. -/
theorem sInvRun_cast (hU : SInvOk P U) :
    ∀ (k : ℕ) (f : ℕ → ℤ) (i : ℕ), ((sInvRun P U k f i : ℤ) : ZMod P.q)
        = invRun (P.psi : ZMod P.q) P.layers P.logN k (fun j => (f j : ZMod P.q)) i
  | 0, _, _ => rfl
  | k + 1, f, i => by
      have hlayer : (fun j => ((sInvLayer P U k f j : ℤ) : ZMod P.q))
          = invLayerFn (P.psi : ZMod P.q) P.layers P.logN k (fun j => (f j : ZMod P.q)) :=
        funext (sInvLayer_cast P U hU k f)
      rw [sInvRun, sInvRun_cast hU k _ i, hlayer]
      rfl

/-! ## 10. The signed inverse transform on words -/

/-- The signed Montgomery multiply of the word variable `v` by the constant `z`, as
the `jasminDialect` schedule of `smontW`. -/
def smontTail (w q qinv z : ℕ) {Γ : Ctxt jasminDialect} (v : Var Γ (Rw w)) :
    Com jasminDialect Γ (Rw w) :=
  .var (castE w (2 * w) v)
  (.var (shlE (2 * w) w .here)
  (.var (sarE (2 * w) w .here)
  (.var (constE (2 * w) z)
  (.var (binE .mul (2 * w) (.there .here) .here)
  (.var (castE (2 * w) w .here)
  (.var (constE w qinv)
  (.var (binE .mul w (.there .here) .here)
  (.var (castE w (2 * w) .here)
  (.var (shlE (2 * w) w .here)
  (.var (sarE (2 * w) w .here)
  (.var (constE (2 * w) q)
  (.var (binE .mul (2 * w) (.there .here) .here)
  (.var (binE .sub (2 * w)
    (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .here)
  (.var (sarE (2 * w) w .here)
  (.var (castE (2 * w) w .here) (.ret .here))))))))))))))))

theorem smontTail_denote (w q qinv z : ℕ) {Γ : Ctxt jasminDialect} (v : Var Γ (Rw w))
    (V : Valuation Γ) :
    (smontTail w q qinv z v).denote V = smontW w q qinv z (show BitVec w from v.lookup V) := rfl

/-- The signed Barrett reduction of the word variable `v`, as the `jasminDialect`
schedule of `sbarrettW`. -/
def sbarrettTail (w s q v : ℕ) {Γ : Ctxt jasminDialect} (x : Var Γ (Rw w)) :
    Com jasminDialect Γ (Rw w) :=
  .var (castE w (2 * w) x)
  (.var (shlE (2 * w) w .here)
  (.var (sarE (2 * w) w .here)
  (.var (constE (2 * w) v)
  (.var (binE .mul (2 * w) (.there .here) .here)
  (.var (constE (2 * w) (2 ^ s / 2))
  (.var (binE .add (2 * w) (.there .here) .here)
  (.var (sarE (2 * w) s .here)
  (.var (constE (2 * w) q)
  (.var (binE .mul (2 * w) (.there .here) .here)
  (.var (binE .sub (2 * w) (.there (.there (.there (.there (.there (.there (.there .here)))))))
    .here)
  (.var (castE (2 * w) w .here) (.ret .here))))))))))))

theorem sbarrettTail_denote (w s q v : ℕ) {Γ : Ctxt jasminDialect} (x : Var Γ (Rw w))
    (V : Valuation Γ) :
    (sbarrettTail w s q v x).denote V = sbarrettW w s q v (show BitVec w from x.lookup V) := rfl

/-- One signed Gentleman–Sande lane on `w`-bit words: `a[ia] + a[ib]`,
Barrett-reduced when `red`, when `up`; the signed Montgomery product of
`a[ia] − a[ib]` by the constant `z` otherwise. -/
def sInvLaneProg (w q qinv bs bv z : ℕ) (red : Bool) :
    (n : ℕ) → ℕ → ℕ → Bool → Com jasminDialect (Ctxs w n) (.reg w)
  | 0, _, _, _ => .var (constE w 0) (.ret .here)
  | n + 1, ia, ib, up =>
      if up then
        .var (binE .add w (laneVarG (Rw w) n ia) (laneVarG (Rw w) n ib))
          (if red then sbarrettTail w bs q bv .here else .ret .here)
      else
        .var (binE .sub w (laneVarG (Rw w) n ia) (laneVarG (Rw w) n ib))
          (smontTail w q qinv z .here)

theorem sInvLaneProg_denote (w q qinv bs bv z : ℕ) (red : Bool) (n ia ib : ℕ) (up : Bool)
    (V : Valuation (Ctxs w (n + 1))) :
    (sInvLaneProg w q qinv bs bv z red (n + 1) ia ib up).denote V
      = if up then
          (if red then sbarrettW w bs q bv
            ((show BitVec w from (laneVarG (Rw w) n ia).lookup V) + (laneVarG (Rw w) n ib).lookup V)
          else (show BitVec w from (laneVarG (Rw w) n ia).lookup V)
            + (laneVarG (Rw w) n ib).lookup V)
        else smontW w q qinv z
          ((show BitVec w from (laneVarG (Rw w) n ia).lookup V) - (laneVarG (Rw w) n ib).lookup V) := by
  cases up <;> cases red <;> rfl

/-- One signed scaling lane on `w`-bit words: the signed Montgomery product of
`a[i]` by the constant `z`. -/
def sScaleLaneProg (w q qinv z : ℕ) : (n : ℕ) → ℕ → Com jasminDialect (Ctxs w n) (.reg w)
  | 0, _ => .var (constE w 0) (.ret .here)
  | n + 1, i => smontTail w q qinv z (laneVarG (Rw w) n i)

/-- A centred constant as a `2 w`-bit constant. -/
def cEnc (w : ℕ) (c : ℤ) : ℕ := (c % ((2 ^ (2 * w) : ℕ) : ℤ)).toNat

theorem cEnc_toInt (w q : ℕ) (c : ℤ) (hc : 2 * |c| ≤ q) (hq : 2 * q < 2 ^ (2 * w)) :
    (BitVec.ofNat (2 * w) (cEnc w c)).toInt = c := by
  have hpos : (0 : ℤ) < ((2 ^ (2 * w) : ℕ) : ℤ) := by positivity
  rw [BitVec.toInt_ofNat', cEnc, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)),
    Int.emod_bmod]
  have h2' : (2 * q : ℤ) < ((2 ^ (2 * w) : ℕ) : ℤ) := by exact_mod_cast hq
  exact Int.bmod_eq_of_le_mul_two
    (by rcases abs_cases c with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)
    (by rcases abs_cases c with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)

/-- Stage `st` of the signed inverse transform on word lanes: the scaling by `s`
for `none`; for `some ℓ`, inverse layer `ℓ`. -/
def invSemSW (s : ℕ) : Option ℕ → (ℕ → BitVec U.w) → ℕ → BitVec U.w
  | none, g, i => smontW U.w P.q U.qinv (cEnc U.w (zscS P U s)) (g i)
  | some ℓ, g, i =>
      if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ) then
        (if U.red ℓ then sbarrettW U.w U.bshift P.q U.bconst (g i + g (i + 2 ^ (P.logN - 1 - ℓ)))
        else g i + g (i + 2 ^ (P.logN - 1 - ℓ)))
      else
        smontW U.w P.q U.qinv
          (cEnc U.w (zsInvS P U (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)))))
          (g (i - 2 ^ (P.logN - 1 - ℓ)) - g i)

/-- The lane schedules of signed inverse stage `st` on `2 ^ logN` word lanes. -/
def sInvLaneProgW (s : ℕ) : Option ℕ → ℕ → Com jasminDialect (Ctxs U.w (2 ^ P.logN)) (.reg U.w)
  | none, i => sScaleLaneProg U.w P.q U.qinv (cEnc U.w (zscS P U s)) (2 ^ P.logN) i
  | some ℓ, i =>
      if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ) then
        sInvLaneProg U.w P.q U.qinv U.bshift U.bconst
          (cEnc U.w (zsInvS P U (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)))))
          (U.red ℓ) (2 ^ P.logN) i (i + 2 ^ (P.logN - 1 - ℓ)) true
      else
        sInvLaneProg U.w P.q U.qinv U.bshift U.bconst
          (cEnc U.w (zsInvS P U (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)))))
          (U.red ℓ) (2 ^ P.logN) (i - 2 ^ (P.logN - 1 - ℓ)) i false

theorem sInvLaneProgW_denote (s : ℕ) (st : Option ℕ) (hst : ∀ ℓ, st = some ℓ → ℓ < P.logN)
    (g : ℕ → BitVec U.w) (i : ℕ) (hi : i < 2 ^ P.logN) :
    (sInvLaneProgW P U s st i).denote (lanesVal (Rw U.w) g (2 ^ P.logN) 0)
      = invSemSW P U s st g i := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ P.logN = m + 1 := ⟨2 ^ P.logN - 1, by
    have := Nat.two_pow_pos P.logN; omega⟩
  cases st with
  | none =>
    simp only [sInvLaneProgW, invSemSW]
    revert hi
    rw [hm]
    intro hi
    rw [sScaleLaneProg.eq_2, smontTail_denote, laneVarG_lookup (Rw U.w) g m i 0 (by omega),
      Nat.zero_add]
  | some ℓ =>
    have hpart := layer_partner_lt P.logN ℓ i (hst ℓ rfl) hi
    simp only [sInvLaneProgW, invSemSW]
    generalize 2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) = k
    revert hpart hi
    rw [hm]
    intro hi hpart
    generalize 2 ^ (P.logN - 1 - ℓ) = len at hpart ⊢
    split
    · next hlt =>
      rw [sInvLaneProg_denote, if_pos rfl, laneVarG_lookup (Rw U.w) g m i 0 (by omega),
        laneVarG_lookup (Rw U.w) g m (i + len) 0 (by have := hpart hlt; omega)]
      simp only [Nat.zero_add]
    · next hlt =>
      rw [sInvLaneProg_denote, if_neg (by simp),
        laneVarG_lookup (Rw U.w) g m (i - len) 0 (by omega),
        laneVarG_lookup (Rw U.w) g m i 0 (by omega)]
      simp only [Nat.zero_add]

/-- The signed inverse transform program of scaling constant `s` on `2 ^ logN`
lanes of `w`-bit words: inverse layers `L − 1, …, 0`, each lower lane
Barrett-reduced at the layers of the reduction schedule, then every lane
multiplied by `s`. -/
def inttProgSW (s : ℕ) :
    MultiReturnCom jasminDialect (Ctxs U.w (2 ^ P.logN)) (Ctxs U.w (2 ^ P.logN)) :=
  chainD (Rw U.w) (2 ^ P.logN) (sInvLaneProgW P U s) (invStages P.layers) (Ctxt.Hom.id _)

/-- A signed integer of absolute value below `2 ^ w / 2` is its own balanced residue
modulo `2 ^ w`. -/
theorem bmod_two_pow_of_abs {w : ℕ} (x : ℤ) (b : ℕ) (hx : |x| < b) (hb : 2 * b ≤ 2 ^ w) :
    x.bmod (2 ^ w) = x := by
  have hb' : ((2 * b : ℕ) : ℤ) ≤ ((2 ^ w : ℕ) : ℤ) := by exact_mod_cast hb
  push_cast at hb'
  exact Int.bmod_eq_of_le_mul_two
    (by push_cast; rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)
    (by push_cast; rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)

/-- A signed integer of absolute value below `2 ^ w / 2` is its own `w`-bit word. -/
theorem toInt_ofInt_of_abs {w : ℕ} (x : ℤ) (b : ℕ) (hx : |x| < b) (hb : 2 * b ≤ 2 ^ w) :
    (BitVec.ofInt w x).toInt = x := by
  rw [BitVec.toInt_ofInt]
  exact_mod_cast bmod_two_pow_of_abs x b hx hb

/-- The sum of two `w`-bit words of signed integers below `2 ^ w / 4` is their sum. -/
theorem toInt_add_ofInt {w : ℕ} (x y : ℤ) (b : ℕ) (hx : |x| < b) (hy : |y| < b)
    (hb : 4 * b ≤ 2 ^ w) : (BitVec.ofInt w x + BitVec.ofInt w y).toInt = x + y := by
  rw [BitVec.toInt_add, toInt_ofInt_of_abs x b hx (by omega),
    toInt_ofInt_of_abs y b hy (by omega)]
  exact_mod_cast bmod_two_pow_of_abs (x + y) (2 * b)
    (by have := abs_add_le x y; push_cast; linarith) (by omega)

/-- The difference of two `w`-bit words of signed integers below `2 ^ w / 4` is
their difference. -/
theorem toInt_sub_ofInt {w : ℕ} (x y : ℤ) (b : ℕ) (hx : |x| < b) (hy : |y| < b)
    (hb : 4 * b ≤ 2 ^ w) : (BitVec.ofInt w x - BitVec.ofInt w y).toInt = x - y := by
  rw [BitVec.toInt_sub, toInt_ofInt_of_abs x b hx (by omega),
    toInt_ofInt_of_abs y b hy (by omega)]
  exact_mod_cast bmod_two_pow_of_abs (x - y) (2 * b)
    (by have := abs_sub x y; push_cast; linarith) (by omega)

/-- On signed representatives below `bnd (ℓ + 1)`, one inverse word layer is
`sInvLayer` read as words. -/
theorem invSemSW_ofInt (hU : SInvOk P U) (hq : 1 < P.q) (s ℓ : ℕ) (hl : ℓ < P.layers)
    (f : ℕ → ℤ) (hf : ∀ j, |f j| < U.bnd (ℓ + 1)) :
    invSemSW P U s (some ℓ) (fun j => BitVec.ofInt U.w (f j))
      = fun i => BitVec.ofInt U.w (sInvLayer P U ℓ f i) := by
  have hU' := hU
  obtain ⟨_, hN, h2q, _, hfit, hlay, _⟩ := hU'
  obtain ⟨h4, _, hprod, hlow⟩ := hlay ℓ hl
  clear hlay
  funext i
  apply BitVec.eq_of_toInt_eq
  have hbr := sInvLayer_bound P U hU (by omega) ℓ hl f hf i
  have hfl := hfit ℓ (by omega)
  rw [toInt_ofInt_of_abs _ _ hbr hfl]
  simp only [invSemSW, sInvLayer] at hbr ⊢
  generalize 2 ^ (P.logN - 1 - ℓ) = len at hbr ⊢
  generalize 2 ^ ℓ + i / (len + len) = k at hbr ⊢
  by_cases hlt : i % (len + len) < len
  · simp only [if_pos hlt] at hbr ⊢
    have hsum := toInt_add_ofInt (w := U.w) _ _ _ (hf i) (hf (i + len)) h4
    by_cases hr : U.red ℓ = true
    · simp only [if_pos hr] at hlow hbr ⊢
      have hs : |f i + f (i + len)| < 2 * U.bnd (ℓ + 1) := by
        have := abs_add_le (f i) (f (i + len))
        have := hf i; have := hf (i + len); linarith
      rw [sbarrettW_toInt _ _ _ _ _ ?_ ?_, hsum]
      · rw [hsum]
        have hb2 : ((2 * (U.bconst * (2 * U.bnd (ℓ + 1)) + 2 ^ U.bshift / 2) : ℕ) : ℤ)
            < ((2 ^ (2 * U.w) : ℕ) : ℤ) := by exact_mod_cast hlow.2
        have hvx : |(U.bconst : ℤ) * (f i + f (i + len))| ≤ U.bconst * (2 * U.bnd (ℓ + 1)) := by
          rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg _)]
          exact mul_le_mul_of_nonneg_left hs.le (Int.natCast_nonneg _)
        have := abs_add_le ((U.bconst : ℤ) * (f i + f (i + len))) ((2 ^ U.bshift / 2 : ℕ) : ℤ)
        rw [abs_of_nonneg (Int.natCast_nonneg ((2 ^ U.bshift / 2 : ℕ)))] at this
        push_cast at hb2 this hvx ⊢
        linarith
      · rw [hsum]
        have hfl' : ((2 * U.bnd ℓ : ℕ) : ℤ) ≤ ((2 ^ U.w : ℕ) : ℤ) := by exact_mod_cast hfl
        push_cast at hfl' ⊢
        linarith
    · simp only [if_neg hr]
      exact hsum
  · simp only [if_neg hlt] at hbr ⊢
    have hdiff := toInt_sub_ofInt (w := U.w) _ _ _ (hf (i - len)) (hf i) h4
    have hd : |f (i - len) - f i| < ((2 * U.bnd (ℓ + 1) : ℕ) : ℤ) := by
      have := abs_sub (f (i - len)) (f i)
      have := hf i; have := hf (i - len); push_cast; linarith
    have hz := two_abs_bmod_le
      (((P.psi ^ (2 ^ (P.layers + 1) - bitrev P.layers k) * 2 ^ U.w : ℕ) : ℤ)) P.q (by omega)
    rw [smontW_toInt _ _ _ _ _ (zsInvS P U k) (cEnc_toInt _ _ _ hz h2q) (by omega) ?_ ?_, hdiff]
    · rw [hdiff]
      have hzx : 2 * |zsInvS P U k * (f (i - len) - f i)| ≤ P.q * |f (i - len) - f i| := by
        rw [abs_mul, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hz (abs_nonneg _)
      have hq' : (0 : ℤ) ≤ P.q := Int.natCast_nonneg _
      have hqd : (P.q : ℤ) * |f (i - len) - f i| ≤ P.q * ((2 * U.bnd (ℓ + 1) : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left hd.le hq'
      have hp' : ((2 * P.q * U.bnd (ℓ + 1) + 2 ^ U.w * P.q : ℕ) : ℤ)
          < ((2 ^ (2 * U.w) : ℕ) : ℤ) := by exact_mod_cast hprod
      push_cast at hp' hqd ⊢
      linarith
    · rw [hdiff]
      have hfl' : ((2 * U.bnd ℓ : ℕ) : ℤ) ≤ ((2 ^ U.w : ℕ) : ℤ) := by exact_mod_cast hfl
      push_cast at hfl' ⊢
      linarith

theorem foldl_invSemSW (hU : SInvOk P U) (hq : 1 < P.q) (s : ℕ) :
    ∀ (k : ℕ) (f : ℕ → ℤ), k ≤ P.layers → (∀ j, |f j| < U.bnd k) →
      ((List.range k).reverse.map some).foldl (fun g st => invSemSW P U s st g)
          (fun j => BitVec.ofInt U.w (f j)) = fun j => BitVec.ofInt U.w (sInvRun P U k f j)
  | 0, _, _, _ => rfl
  | k + 1, f, hk, hf => by
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons, List.foldl_cons, invSemSW_ofInt P U hU hq s k (by omega) f hf,
        foldl_invSemSW hU hq s k _ (by omega)
          (sInvLayer_bound P U hU (by omega) k (by omega) f hf)]
      rfl

/-- **The signed inverse word lowering.** For a parameter record satisfying
`NttParams.Ok`, a signed inverse schedule satisfying `SInvOk`, and inputs below
`bnd L` in absolute value, every output word of `inttProgSW`, read as a signed
integer, is below `bout` in absolute value, and cast to `ZMod q` it is
`inttSpec`. -/
theorem inttProgSW_denote (hP : P.Ok) (hU : SInvOk P U) (s : ℕ) (f : ℕ → ℤ)
    (hf : ∀ j, |f j| < U.bnd P.layers) (i : ℕ) (hi : i < 2 ^ P.logN) :
    |(hvGetG (Rw U.w) (0 : BitVec U.w) ((inttProgSW P U s).denote
        (lanesVal (Rw U.w) (fun j => BitVec.ofInt U.w (f j)) (2 ^ P.logN) 0)) i).toInt|
        < U.bout ∧
    (((hvGetG (Rw U.w) (0 : BitVec U.w) ((inttProgSW P U s).denote
        (lanesVal (Rw U.w) (fun j => BitVec.ofInt U.w (f j)) (2 ^ P.logN) 0)) i).toInt : ℤ)
        : ZMod P.q)
      = inttSpec (P.psi : ZMod P.q) P.layers P.logN (s : ZMod P.q)
          (fun j => (f j : ZMod P.q)) i := by
  have hq : 1 < P.q := hP.2.2.1
  have hLM := hP.2.1
  rw [inttProgSW, chainD_denote (Rw U.w) (2 ^ P.logN) (0 : BitVec U.w) _ (invSemSW P U s)
    (invStages P.layers)
    (fun st hst g j hj => sInvLaneProgW_denote P U s st (fun ℓ hℓ => by
        subst hℓ
        simp only [invStages, List.mem_append, List.mem_map, List.mem_reverse, List.mem_range,
          List.mem_singleton] at hst
        rcases hst with ⟨ℓ', h1, h2⟩ | h0
        · cases h2; omega
        · cases h0) g j hj)
    (Ctxt.Hom.id _) _ _ (pullV_id _)]
  rw [hvGetG_lanesVal _ _ _ _ _ _ hi, Nat.zero_add, invStages, List.foldl_append]
  erw [foldl_invSemSW P U hU hq s P.layers f le_rfl hf]
  rw [List.foldl_cons, List.foldl_nil]
  have hU' := hU
  obtain ⟨hcop, hN, h2q, _, hfit, _, hsc1, hsc2, hsc3⟩ := hU'
  have hb := sInvRun_bounds P U hU (by omega) P.layers f le_rfl hf
  have hx := toInt_ofInt_of_abs (w := U.w) _ _ (hb i) (hfit 0 (by omega))
  have hz := two_abs_bmod_le (((s * 2 ^ U.w : ℕ) : ℤ)) P.q (by omega)
  have hu := smont_bmod_lt U.w P.q U.qinv hN (by omega) (((s * 2 ^ U.w : ℕ) : ℤ)) _ _ (hb i)
  have hR : (0 : ℤ) < 2 * (2 ^ U.w : ℕ) := by positivity
  have hs1 : ((P.q * U.bnd 0 + 2 ^ U.w * P.q : ℕ) : ℤ) ≤ ((2 * 2 ^ U.w * U.bout : ℕ) : ℤ) := by
    exact_mod_cast hsc1
  have hs2 : ((P.q * U.bnd 0 + 2 ^ U.w * P.q : ℕ) : ℤ) < ((2 ^ (2 * U.w) : ℕ) : ℤ) := by
    exact_mod_cast hsc2
  have hs3 : ((2 * U.bout : ℕ) : ℤ) ≤ ((2 ^ U.w : ℕ) : ℤ) := by exact_mod_cast hsc3
  have hlt : |smont U.w P.q U.qinv (zscS P U s * sInvRun P U P.layers f i)| < U.bout := by
    refine lt_of_mul_lt_mul_left ?_ hR.le
    unfold zscS
    push_cast at hu hs1 ⊢
    linarith
  have hw : (smontW U.w P.q U.qinv (cEnc U.w (zscS P U s))
      (BitVec.ofInt U.w (sInvRun P U P.layers f i))).toInt
      = smont U.w P.q U.qinv (zscS P U s * sInvRun P U P.layers f i) := by
    rw [smontW_toInt _ _ _ _ _ (zscS P U s) (cEnc_toInt _ _ _ hz h2q) (by omega) ?_ ?_, hx]
    · rw [hx]
      have hzx : 2 * |zscS P U s * sInvRun P U P.layers f i|
          ≤ P.q * |sInvRun P U P.layers f i| := by
        rw [abs_mul, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hz (abs_nonneg _)
      have hqd : (P.q : ℤ) * |sInvRun P U P.layers f i| ≤ P.q * U.bnd 0 :=
        mul_le_mul_of_nonneg_left (hb i).le (Int.natCast_nonneg _)
      push_cast at hs2 ⊢
      linarith
    · rw [hx]
      push_cast at hs3 ⊢
      linarith
  simp only [invSemSW]
  rw [hw]
  refine ⟨hlt, ?_⟩
  rw [zscS, smont_bmod_cast _ _ _ hcop hN, sInvRun_cast P U hU, inttSpec]

/-! ## 11. The ML-KEM reference inverse schedule -/

/-- The inverse NTT schedule of the ML-KEM reference implementation: signed 16-bit
lanes, radix `2 ^ 16`, Montgomery constant `62209 = −3327 mod 2 ^ 16`, Barrett
shift `26` with constant `20159 = round (2 ^ 26 / q)` applied to the lower lane at
every inverse layer, and bound `q` on every lane. -/
def mlkemSignedInv : SignedInvSched := ⟨16, 62209, 26, 20159, fun _ => true, fun _ => 3329, 3329⟩

theorem mlkemSignedInv_ok : SInvOk mlkemNtt mlkemSignedInv := by decide

/-- The scaling constant `512 = 2 ^ 16 / 2 ^ 7 mod q` of the ML-KEM reference has the
centred Montgomery form `1441`, the reference's `mont ^ 2 / 128`. -/
theorem mlkemSignedInv_scale : zscS mlkemNtt mlkemSignedInv 512 = 1441 := by decide

/-- The ML-KEM reference inverse schedule on signed 16-bit words: from inputs below
`q` in absolute value, every output word is below `q` in absolute value and is
`inttSpec` at `ψ = 17`, `L = 7` with scaling `512` modulo `q`, the inverse
transform followed by multiplication by the Montgomery radix `2 ^ 16`. -/
theorem mlkemSignedInv_denote (f : ℕ → ℤ) (hf : ∀ j, |f j| < 3329) (i : ℕ) (hi : i < 256) :
    |(hvGetG (Rw 16) (0 : BitVec 16) ((inttProgSW mlkemNtt mlkemSignedInv 512).denote
        (lanesVal (Rw 16) (fun j => BitVec.ofInt 16 (f j)) 256 0)) i).toInt| < 3329 ∧
    (((hvGetG (Rw 16) (0 : BitVec 16) ((inttProgSW mlkemNtt mlkemSignedInv 512).denote
        (lanesVal (Rw 16) (fun j => BitVec.ofInt 16 (f j)) 256 0)) i).toInt : ℤ) : ZMod 3329)
      = inttSpec (17 : ZMod 3329) 7 8 512 (fun j => (f j : ZMod 3329)) i :=
  inttProgSW_denote mlkemNtt mlkemSignedInv mlkemNtt_ok mlkemSignedInv_ok 512 f
    (fun j => by simpa [mlkemSignedInv] using hf j) i hi

/-! ## 12. Inverse word schedules -/

/-- A word schedule of the inverse transform: unsigned representatives in `S.w`-bit
words (`inttProgUW`), or signed representatives in `w`-bit words with Barrett
reductions (`inttProgSW`). -/
inductive InvWordSched where
  /-- The unsigned schedule `S` with radix `2 ^ logR` on `S.w`-bit lanes. -/
  | unsignedMont (S : LazySched) (logR : ℕ)
  /-- The signed inverse schedule `U` on `U.w`-bit lanes. -/
  | signedMont (U : SignedInvSched)

/-- The lane word width of an inverse word schedule. -/
def InvWordSched.width : InvWordSched → ℕ
  | .unsignedMont S _ => S.w
  | .signedMont U => U.w

/-- The integer a lane word stands for: its unsigned value, or its signed value. -/
def InvWordSched.val : (s : InvWordSched) → BitVec s.width → ℤ
  | .unsignedMont _ _, x => (x.toNat : ℤ)
  | .signedMont _, x => x.toInt

/-- The bound on the absolute value of every output lane. -/
def InvWordSched.bound : InvWordSched → ℕ
  | .unsignedMont _ _ => 2 * P.q
  | .signedMont U => U.bout

/-- The side condition of an inverse word schedule, decidable on `ℕ`. -/
def InvWordSched.Ok : InvWordSched → Prop
  | .unsignedMont S logR => SchedOk P S ∧ UWordOk P S logR ∧ UInvWordOk P S
  | .signedMont U => SInvOk P U ∧ P.q ≤ U.bnd P.layers

instance : (s : InvWordSched) → Decidable (s.Ok P)
  | .unsignedMont S logR =>
    inferInstanceAs (Decidable (SchedOk P S ∧ UWordOk P S logR ∧ UInvWordOk P S))
  | .signedMont U => inferInstanceAs (Decidable (SInvOk P U ∧ P.q ≤ U.bnd P.layers))

/-- The inverse transform program of scaling constant `c` of an inverse word
schedule on `2 ^ logN` lanes. -/
def inttProgG : (s : InvWordSched) → ℕ →
    MultiReturnCom jasminDialect (Ctxs s.width (2 ^ P.logN)) (Ctxs s.width (2 ^ P.logN))
  | .unsignedMont S logR, c => inttProgUW P S logR c
  | .signedMont U, c => inttProgSW P U c

/-- **Both inverse word lowerings compute the inverse transform.** For an inverse
word schedule satisfying its side condition and inputs below `q`, every output lane
stands for an integer below the schedule's bound in absolute value, congruent
modulo `q` to `inttSpec`. -/
theorem inttProgG_denote (hP : P.Ok) (s : InvWordSched) (hs : s.Ok P) (c : ℕ) (f : ℕ → ℕ)
    (hf : ∀ j, f j < P.q) (i : ℕ) (hi : i < 2 ^ P.logN) :
    |s.val (hvGetG (Rw s.width) (0 : BitVec s.width) ((inttProgG P s c).denote
        (lanesVal (Rw s.width) (fun j => BitVec.ofNat s.width (f j)) (2 ^ P.logN) 0)) i)|
        < s.bound P ∧
    ((s.val (hvGetG (Rw s.width) (0 : BitVec s.width) ((inttProgG P s c).denote
        (lanesVal (Rw s.width) (fun j => BitVec.ofNat s.width (f j)) (2 ^ P.logN) 0)) i)
        : ℤ) : ZMod P.q)
      = inttSpec (P.psi : ZMod P.q) P.layers P.logN (c : ZMod P.q)
          (fun j => (f j : ZMod P.q)) i := by
  cases s with
  | unsignedMont S logR =>
    obtain ⟨hS, hW, hI⟩ := hs
    obtain ⟨h1, h2⟩ := inttProgUW_denote P S logR hP hS hW hI c f
      (fun j => by have := hf j; have := hI.1; omega)
      (fun j => by have := hf j; have := hI.2; omega) i hi
    refine ⟨?_, ?_⟩
    · show |((_ : ℕ) : ℤ)| < ((2 * P.q : ℕ) : ℤ)
      rw [abs_of_nonneg (Int.natCast_nonneg _)]
      exact_mod_cast h1
    · show (((_ : ℕ) : ℤ) : ZMod P.q) = _
      rw [Int.cast_natCast]
      exact h2
  | signedMont U =>
    obtain ⟨hU, hb⟩ := hs
    have hofn : (fun j => BitVec.ofNat U.w (f j)) = fun j => BitVec.ofInt U.w (f j : ℤ) :=
      funext fun j => (BitVec.ofInt_natCast U.w (f j)).symm
    have h := inttProgSW_denote P U hP hU c (fun j => (f j : ℤ))
      (fun j => by rw [abs_of_nonneg (Int.natCast_nonneg _)]; have := hf j; omega) i hi
    simp only [Int.cast_natCast] at h
    rw [← hofn] at h
    exact h

/-- The ML-KEM unsigned 16-bit inverse word schedule satisfies its side condition. -/
theorem mlkemUnsignedInvWord_ok : (InvWordSched.unsignedMont mlkemLazy 16).Ok mlkemNtt :=
  ⟨mlkemLazy_ok, mlkemUWord_ok, mlkemUInvWord_ok⟩

/-- The ML-DSA unsigned 32-bit inverse word schedule satisfies its side condition. -/
theorem mldsaUnsignedInvWord_ok : (InvWordSched.unsignedMont mldsaLazy 32).Ok mldsaNtt :=
  ⟨mldsaLazy_ok, mldsaUWord_ok, mldsaUInvWord_ok⟩

/-- The ML-KEM reference signed 16-bit inverse word schedule satisfies its side
condition. -/
theorem mlkemSignedInvWord_ok : (InvWordSched.signedMont mlkemSignedInv).Ok mlkemNtt :=
  ⟨mlkemSignedInv_ok, by decide⟩

end CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
