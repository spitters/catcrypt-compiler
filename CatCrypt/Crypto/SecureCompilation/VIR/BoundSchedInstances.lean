/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.BoundSched
public import CatCrypt.Crypto.SecureCompilation.VIR.PointwiseAcc

/-!
# The closed-form schedule conditions as bound schedules

Each of the four closed-form side conditions of the word templates is an instance of
`BoundSched.Ok`: the lazy unsigned NTT (`SchedOk`), the signed Montgomery NTT (`SSchedOk`), the
base multiplication (`BasemulSched.Ok`) and the row accumulation (`AccSched.Ok`). The transfer
of a bound through a signed Montgomery reduction is `cdiv (2 |a| + 2 ^ w q) (2 · 2 ^ w)`, the
bound of `smont_bound`. The signed Montgomery reduction of a double-width word is a bounded
block, `smontBlock`, whose contract is `smontAccW_spec`.

## Main definitions

* `cdiv`: division rounded up.
* `schedBound`, `sschedBound`, `basemulBound`, `accBound`: the bound schedules of the four
  templates.
* `smontProg`, `smontBlock`: the signed Montgomery reduction as a program and as a bounded
  block.

## Main results

* `schedBound_ok`, `sschedBound_ok`, `basemulBound_ok`, `accBound_ok`: each closed-form
  condition gives `BoundSched.Ok` of its schedule.
* `smontBlock_sound`: the contract of the reduction block.
* `mlkemSigned_boundSched_ok`, `mlkemBasemul_boundSched_ok`, `mlkemAcc3_boundSched_ok`: the
  ML-KEM instances, from the existing certificates.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.BoundSchedInstances

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange
open CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
open CatCrypt.Crypto.SecureCompilation.VIR.BasemulWord
open CatCrypt.Crypto.SecureCompilation.VIR.PointwiseAcc

/-! ## 1. Division rounded up -/

/-- Division rounded up. -/
def cdiv (x y : ℕ) : ℕ := (x + y - 1) / y

theorem cdiv_le {x y b : ℕ} (hy : 0 < y) (h : x ≤ y * b) : cdiv x y ≤ b := by
  unfold cdiv
  have : (x + y - 1) / y < b + 1 := by
    rw [Nat.div_lt_iff_lt_mul hy, Nat.add_mul, Nat.one_mul, Nat.mul_comm b y]
    omega
  omega

/-! ## 2. The four templates -/

/-- The bound schedule of a lazy unsigned NTT schedule: one stage per layer, the bound
    `bnd P S`, the transfer of a layer `q` after a reduced layer and `b + off · q`
    otherwise. -/
def schedBound (P : NttParams) (S : LazySched) : BoundSched where
  n := P.layers
  bnd := NegacyclicNttTemplate.bnd P S
  xfer j b := if S.red j then P.q else b + S.off * P.q
  fits _ b := decide (b ≤ S.R ∧ b + S.off * P.q ≤ 2 ^ S.w)
  const := decide (2 ≤ S.off ∧ 0 < S.R ∧ Nat.Coprime S.R P.q ∧
    (P.q * S.qinv) % S.R = S.R - 1 ∧ 2 * P.q * S.R ≤ 2 ^ (2 * S.w))

theorem schedBound_ok (P : NttParams) (S : LazySched) (h : SchedOk P S) :
    (schedBound P S).Ok := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨decide_eq_true ⟨h1, h2, h3, h4, h5⟩, fun _ _ => le_of_eq rfl,
    fun j hj => decide_eq_true (h6 j hj)⟩

/-- The bound schedule of a signed Montgomery NTT schedule: one stage per layer, the bound
    table `T.bnd`, the transfer of a layer `b` plus the bound of a reduced twiddle
    product. -/
def sschedBound (P : NttParams) (T : SignedSched) : BoundSched where
  n := P.layers
  bnd := T.bnd
  xfer _ b := b + cdiv (b * P.q + 2 ^ T.w * P.q) (2 * 2 ^ T.w)
  fits _ b := decide (2 * b ≤ 2 ^ T.w ∧ b * P.q + 2 ^ T.w * P.q < 2 ^ (2 * T.w))
  const := decide (Nat.Coprime (2 ^ T.w) P.q ∧ (P.q * T.qinv) % 2 ^ T.w = 1)

theorem sschedBound_ok (P : NttParams) (T : SignedSched) (h : SSchedOk P T) :
    (sschedBound P T).Ok := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨decide_eq_true ⟨h1, h2⟩, fun j hj => ?_, fun j hj => decide_eq_true (h3 j hj)⟩
  obtain ⟨hle, hg⟩ := h4 j hj
  have hc := cdiv_le (by positivity) hg
  have hsub := Nat.add_sub_cancel' hle
  show T.bnd j + cdiv (T.bnd j * P.q + 2 ^ T.w * P.q) (2 * 2 ^ T.w) ≤ T.bnd (j + 1)
  omega

/-- The bound schedule of the base multiplication: two stages, the inputs within `inB`, the
    inner reduction within `midB` and the outputs within `outB`. -/
def basemulBound (S : BasemulSched) : BoundSched where
  n := 2
  bnd
    | 0 => S.inB
    | 1 => S.midB
    | _ => S.outB
  xfer j b := if j = 0 then cdiv (2 * (b * b) + 2 ^ S.w * S.q) (2 * 2 ^ S.w)
    else max (cdiv (2 * (S.inB * S.inB) + b * S.q + 2 ^ S.w * S.q) (2 * 2 ^ S.w))
      (cdiv (4 * (S.inB * S.inB) + 2 ^ S.w * S.q) (2 * 2 ^ S.w))
  fits j b := j == 0 || decide (2 * b < 2 ^ S.w)
  const := decide ((S.q * S.qinv) % 2 ^ S.w = 1 ∧ 2 * S.q < 2 ^ (2 * S.w))

theorem basemulBound_ok (S : BasemulSched) (h : S.Ok) : (basemulBound S).Ok := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hD : 0 < 2 * 2 ^ S.w := by positivity
  refine ⟨decide_eq_true ⟨h1, h2⟩, fun j hj => ?_, fun j hj => ?_⟩
  · rcases j with _ | _ | j
    · exact cdiv_le hD h3
    · exact max_le (cdiv_le hD h5) (cdiv_le hD h6)
    · change j + 1 + 1 < 2 at hj; omega
  · rcases j with _ | _ | _ | j
    · rfl
    · simp [basemulBound, h4]
    · simp [basemulBound, h7]
    · change j + 1 + 1 + 1 < 3 at hj; omega

/-- The bound schedule of the row accumulation over `k` terms: two stages, the operands
    within `inA` and `inB`, the inner reduction within `midB` and the outputs within
    `outB`. -/
def accBound (S : AccSched) (k : ℕ) : BoundSched where
  n := 2
  bnd
    | 0 => S.inA * S.inB
    | 1 => S.midB
    | _ => S.outB
  xfer j b := if j = 0 then cdiv (2 * (k * b) + 2 ^ S.w * S.q) (2 * 2 ^ S.w)
    else max (cdiv (2 * (k * (S.inA * S.inB)) + b * S.q + 2 ^ S.w * S.q) (2 * 2 ^ S.w))
      (cdiv (2 * (2 * k * (S.inA * S.inB)) + 2 ^ S.w * S.q) (2 * 2 ^ S.w))
  fits j b := j == 0 || decide (2 * b < 2 ^ S.w)
  const := decide ((S.q * S.qinv) % 2 ^ S.w = 1 ∧ 2 * S.q < 2 ^ (2 * S.w))

theorem accBound_ok (S : AccSched) (k : ℕ) (h : S.Ok k) : (accBound S k).Ok := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hD : 0 < 2 * 2 ^ S.w := by positivity
  refine ⟨decide_eq_true ⟨h1, h2⟩, fun j hj => ?_, fun j hj => ?_⟩
  · rcases j with _ | _ | j
    · exact cdiv_le hD h3
    · exact max_le (cdiv_le hD h5) (cdiv_le hD h6)
    · change j + 1 + 1 < 2 at hj; omega
  · rcases j with _ | _ | _ | j
    · rfl
    · simp [accBound, h4]
    · simp [accBound, h7]
    · change j + 1 + 1 + 1 < 3 at hj; omega

/-! ## 3. The signed Montgomery reduction as a bounded block -/

/-- The signed Montgomery reduction `redK` of the double-width input word. -/
def smontProg (w q qinv : ℕ) : MultiReturnCom jasminDialect [Rd w] [Rw w] :=
  Com.toMulti (redK w q qinv .here (.ret .here))

/-- The side condition of the reduction block on inputs within `A` and outputs within `M`
    in absolute value. -/
def smontOk (w q qinv A M : ℕ) : Prop :=
  (q * qinv) % 2 ^ w = 1 ∧ 2 * q < 2 ^ (2 * w) ∧ 2 * A + 2 ^ w * q ≤ 2 * 2 ^ w * M ∧
    2 * M < 2 ^ w

instance (w q qinv A M : ℕ) : Decidable (smontOk w q qinv A M) := by
  unfold smontOk; infer_instance

theorem smontBlock_sound (w q qinv A M : ℕ) (hok : decide (smontOk w q qinv A M) = true)
    (V : Valuation [Rd w])
    (hV : ValsIn true (.cons (-(A : ℤ), (A : ℤ)) .nil) V) :
    ValsIn true (.cons (-(M : ℤ), (M : ℤ)) .nil) ((smontProg w q qinv).denote V) ∧
      hvGetZ (zvals true ((smontProg w q qinv).denote V)) 0
        = smont w q qinv (hvGetZ (zvals true V) 0) := by
  obtain ⟨hN, hq, hAM, hMR⟩ := of_decide_eq_true hok
  match V, hV with
  | .cons a .nil, ⟨⟨hlo, hhi⟩, _⟩ =>
    have ha : 2 * |a.toInt| ≤ 2 * (A : ℤ) := by
      have e : rd true a = a.toInt := rfl
      rw [e] at hlo hhi
      have := abs_le.mpr ⟨hlo, hhi⟩
      linarith
    have hM : 2 * (A : ℤ) + ((2 ^ w : ℕ) : ℤ) * q ≤ 2 * ((2 ^ w : ℕ) : ℤ) * M := by
      exact_mod_cast hAM
    have hMR' : 2 * (M : ℤ) < ((2 ^ w : ℕ) : ℤ) := by exact_mod_cast hMR
    obtain ⟨e, hb⟩ := smontAccW_spec w q qinv hN hq a ha hM hMR'
    have hd : (smontProg w q qinv).denote (.cons a .nil)
        = .cons (smontAccW w q qinv a) .nil := by
      rw [smontProg, Com.denote_toMulti]
      simp only [smontAccW, sextW_eq_masked]
      rfl
    rw [hd]
    refine ⟨⟨?_, trivial⟩, ?_⟩
    · show -(M : ℤ) ≤ (smontAccW w q qinv a).toInt ∧ (smontAccW w q qinv a).toInt ≤ M
      rw [e]
      exact abs_le.mp hb
    · show (smontAccW w q qinv a).toInt = smont w q qinv a.toInt
      exact e

/-- **The signed Montgomery reduction as a bounded block**: one double-width input within
    `A` in absolute value, one output within `M`, signed readings, side condition
    `smontOk`, and specification `zout = smont zin`. -/
def smontBlock (w q qinv A M : ℕ) : BoundedBlock where
  Γ := [Rd w]
  ts := [Rw w]
  prog := smontProg w q qinv
  signed := true
  inIv := .cons (-(A : ℤ), (A : ℤ)) .nil
  outIv := .cons (-(M : ℤ), (M : ℤ)) .nil
  ok := decide (smontOk w q qinv A M)
  spec zin zout := hvGetZ zout 0 = smont w q qinv (hvGetZ zin 0)
  denote_of_ok := smontBlock_sound w q qinv A M

/-! ## 4. The ML-KEM instances -/

/-- The ML-KEM signed NTT schedule as a bound schedule, from `mlkemSigned_ok`. -/
theorem mlkemSigned_boundSched_ok : (sschedBound mlkemNtt mlkemSigned).Ok :=
  sschedBound_ok mlkemNtt mlkemSigned mlkemSigned_ok

/-- The ML-KEM base multiplication as a bound schedule, from `mlkemBasemul_ok`. -/
theorem mlkemBasemul_boundSched_ok : (basemulBound mlkemBasemul).Ok :=
  basemulBound_ok mlkemBasemul mlkemBasemul_ok

/-- The ML-KEM row accumulation at `k = 3` as a bound schedule, from `mlkemAcc3_ok`. -/
theorem mlkemAcc3_boundSched_ok : (accBound mlkemAcc3 3).Ok :=
  accBound_ok mlkemAcc3 3 mlkemAcc3_ok

end CatCrypt.Crypto.SecureCompilation.VIR.BoundSchedInstances
