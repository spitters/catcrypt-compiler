/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# The lazy Montgomery NTT lowered to `jasminDialect` words

`VIR/NegacyclicNttTemplate.lean` runs the layers of the negacyclic NTT on
unsigned representatives under a lazy Montgomery schedule (`lazyRun`) and bounds
every lane by `bnd ℓ`.  This file emits those layers as a
`MultiReturnCom jasminDialect` program on `2 ^ M` lanes of 64-bit registers and
proves, once for every parameter record and schedule satisfying the decidable
side conditions, that every output word is the representative `lazyRun` computes:
the bound on the representatives is what keeps every addition, product and
Montgomery numerator of the word program from wrapping.  Its lanes are then
below `bnd L` and congruent modulo `q` to `nttSpec`.

The butterfly is word for word the Montgomery multiply
`u = (T + ((T · q') & (R − 1)) · q) >> log R` with `T = y · z`, followed by
`x + u` on the lower lane and `x + off · q − u` on the upper lane.

## Main definitions

* `laneVarG`, `lanesVal`, `hvGetG` — lanes of a context `List.replicate n τ` in
  any dialect, the valuation reading a lane function, and a lane of a
  replicated-type denotation.
* `chainD` — a sequence of stages over a lane-schedule family in any dialect.
* `montW` — the Montgomery multiply on words.
* `montLaneProg` — the `jasminDialect` schedule of one butterfly lane.
* `semW`, `lazyLaneProgW`, `nttProgW` — one lazy layer on word lanes, its lane
  schedules, and the transform program.
* `WordOk` — the decidable side condition of the word lowering.

## Main results

* `chainD_denote` — `chainD` denotes the left fold of the stage semantics.
* `montW_toNat` — on in-range operands the Montgomery word multiply is
  `Number.montgomeryReduce`.
* `montLaneProg_denote`, `lazyLaneProgW_denote` — the lane schedules denote their
  word expressions.
* `semW_ofNat` — on representatives below `bnd ℓ`, one word layer is `lazyLayer`
  read as words.
* `nttProgW_denote` — every output word of `nttProgW` is below `bnd L`, and cast
  to `ZMod q` it is `nttSpec`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV pullV_id)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
  (hvToHom homToHV pullV_hvToHom lookupVars_homToHV)
open CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldGeneral (Com.foldVarN Com.foldVarN_denote
  Com.denoteN)
open CatCrypt.Crypto.Number (montgomeryReduce)

/-! ## 1. Lanes in any dialect -/

section Lanes

variable {d : Dialect} [TyDenote d.Ty] (τ : d.Ty)

/-- The variable at lane `i` of an `n+1`-lane context, clamping past the end to
lane `0`. -/
def laneVarG : (n i : ℕ) → Var (List.replicate (n + 1) τ) τ
  | _, 0 => .here
  | 0, _ + 1 => .here
  | n + 1, i + 1 => .there (laneVarG n i)

/-- The valuation reading the lane function `f` from index `off` into an
`n`-lane context. -/
def lanesVal (f : ℕ → ⟦τ⟧) : (n off : ℕ) → Valuation (List.replicate n τ)
  | 0, _ => .nil
  | n + 1, off => .cons (f off) (lanesVal f n (off + 1))

theorem laneVarG_lookup (f : ℕ → ⟦τ⟧) :
    ∀ (n i off : ℕ), i ≤ n → (laneVarG τ n i).lookup (lanesVal τ f (n + 1) off) = f (off + i)
  | _, 0, off, _ => by simp only [laneVarG, lanesVal, Nat.add_zero]; rfl
  | 0, _ + 1, _, h => absurd h (by omega)
  | n + 1, i + 1, off, h => by
      show (laneVarG τ n i).lookup (lanesVal τ f (n + 1) (off + 1)) = f (off + (i + 1))
      rw [laneVarG_lookup f n i (off + 1) (by omega)]
      congr 1
      omega

/-- Lane `i` of a replicated-type denotation, `dflt` past its end. -/
def hvGetG (dflt : ⟦τ⟧) : {m : ℕ} → ListDenote (List.replicate m τ) → ℕ → ⟦τ⟧
  | 0, _, _ => dflt
  | _ + 1, .cons x _, 0 => x
  | _ + 1, .cons _ r, i + 1 => hvGetG dflt r i

theorem hvGetG_lanesVal (dflt : ⟦τ⟧) (f : ℕ → ⟦τ⟧) :
    ∀ (n off i : ℕ), i < n → hvGetG τ dflt (lanesVal τ f n off) i = f (off + i)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, off, 0, _ => by simp only [lanesVal, hvGetG, Nat.add_zero]
  | n + 1, off, i + 1, h => by
      show hvGetG τ dflt (lanesVal τ f n (off + 1)) i = f (off + (i + 1))
      rw [hvGetG_lanesVal dflt f n (off + 1) i (by omega)]
      congr 1
      omega

theorem eq_lanesVal (dflt : ⟦τ⟧) (f : ℕ → ⟦τ⟧) :
    ∀ (n off : ℕ) (hv : Valuation (List.replicate n τ)),
      (∀ i, i < n → hvGetG τ dflt hv i = f (off + i)) → hv = lanesVal τ f n off
  | 0, _, .nil, _ => rfl
  | n + 1, off, .cons x r, h => by
      have h0 := h 0 (by omega)
      simp only [hvGetG, Nat.add_zero] at h0
      have hr : r = lanesVal τ f n (off + 1) := by
        refine eq_lanesVal dflt f n (off + 1) r fun i hi => ?_
        have := h (i + 1) (by omega)
        simp only [hvGetG] at this
        rw [this]; congr 1; omega
      rw [h0, hr]
      rfl

theorem hvGetG_denoteN [DialectSignature d] [DialectDenote d] {Γ : Ctxt d} (dflt : ⟦τ⟧) :
    ∀ (m : ℕ) (f : ℕ → Com d Γ τ) (V : Valuation Γ) (i : ℕ),
      i < m → hvGetG τ dflt (Com.denoteN m f V) i = (f i).denote V
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, _, 0, _ => rfl
  | m + 1, f, V, i + 1, h =>
      hvGetG_denoteN dflt m (fun j => f (j + 1)) V i (Nat.lt_of_succ_lt_succ h)

/-- The stages `sts`, in order, each the `n` lane schedules `fam st` emitted over
the result variables of the previous stage; with no stage, the lanes `h` names. -/
def chainD [DialectSignature d] {ι : Type} (n : ℕ)
    (fam : ι → ℕ → Com d (List.replicate n τ) τ) :
    List ι → {Γ : Ctxt d} → Ctxt.Hom (List.replicate n τ) Γ →
      MultiReturnCom d Γ (List.replicate n τ)
  | [], _, h => .ret (homToHV _ h)
  | st :: sts, _, h =>
      Com.foldVarN n (fam st) h (fun {_} _ vs => chainD n fam sts (hvToHom vs))

/-- `chainD` denotes the left fold of the stage semantics `sem`, when each lane
schedule of each stage denotes its lane of `sem`. -/
theorem chainD_denote [DialectSignature d] [DialectDenote d] {ι : Type} (n : ℕ)
    (dflt : ⟦τ⟧) (fam : ι → ℕ → Com d (List.replicate n τ) τ)
    (sem : ι → (ℕ → ⟦τ⟧) → ℕ → ⟦τ⟧) :
    ∀ (sts : List ι), (∀ st, st ∈ sts → ∀ (g : ℕ → ⟦τ⟧) (i : ℕ), i < n →
        (fam st i).denote (lanesVal τ g n 0) = sem st g i) →
      ∀ {Γ : Ctxt d} (h : Ctxt.Hom (List.replicate n τ) Γ) (V : Valuation Γ)
        (f : ℕ → ⟦τ⟧), pullV h V = lanesVal τ f n 0 →
      (chainD τ n fam sts h).denote V = lanesVal τ (sts.foldl (fun g st => sem st g) f) n 0
  | [], _, _, h, V, f, hV => by
      show MultiReturnCom.lookupVars (homToHV _ h) V = _
      rw [lookupVars_homToHV, hV]
      rfl
  | st :: sts, hfam, _, h, V, f, hV => by
      refine Com.foldVarN_denote n _ h V _ _ ?_
      intro Γ' h' vs V' _ hvs
      refine chainD_denote n dflt fam sem sts
        (fun st' hst' => hfam st' (List.mem_cons_of_mem _ hst')) (hvToHom vs) V' (sem st f) ?_
      rw [pullV_hvToHom, hvs, hV]
      refine eq_lanesVal τ dflt _ n 0 _ fun i hi => ?_
      rw [hvGetG_denoteN τ dflt _ _ _ i hi, Nat.zero_add]
      exact hfam st List.mem_cons_self f i hi

end Lanes

/-! ## 2. The Montgomery multiply on words -/

/-- The Montgomery multiply of `y` by the constant `z` on 64-bit words:
`(T + ((T · qinv) & (R − 1)) · q) >> logR` with `T = y · z`. -/
def montW (q R qinv logR z : ℕ) (y : BitVec 64) : BitVec 64 :=
  (y * BitVec.ofNat 64 z + ((y * BitVec.ofNat 64 z * BitVec.ofNat 64 qinv)
    &&& BitVec.ofNat 64 (R - 1)) * BitVec.ofNat 64 q) >>> (BitVec.ofNat 64 logR).toNat

/-- On in-range operands the Montgomery word multiply is `montgomeryReduce`. -/
theorem montW_toNat (q R qinv logR z : ℕ) (y : BitVec 64) (hR : R = 2 ^ logR)
    (hlog : logR ≤ 64) (hzq : z < q) (hy : y.toNat ≤ R) (h2 : 2 * q * R ≤ 2 ^ 64)
    (hqi : qinv < 2 ^ 64) :
    (montW q R qinv logR z y).toNat = montgomeryReduce q R qinv (z * y.toNat) := by
  have hRpos : 0 < R := by rw [hR]; exact Nat.two_pow_pos _
  have h2' : 2 * q * R = R * q + R * q := by ring
  have hq64 : q < 2 ^ 64 := by nlinarith
  have hR64 : R ≤ 2 ^ 64 := by nlinarith
  have hz64 : z < 2 ^ 64 := by omega
  have hT : y.toNat * z < R * q := by
    calc y.toNat * z ≤ R * z := Nat.mul_le_mul_right _ hy
      _ < R * q := Nat.mul_lt_mul_of_pos_left hzq hRpos
  have hTw : (y * BitVec.ofNat 64 z).toNat = y.toNat * z := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hz64, Nat.mod_eq_of_lt (by omega)]
  have hmask : (BitVec.ofNat 64 (R - 1)).toNat = 2 ^ logR - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hR]
  have hm : ((y * BitVec.ofNat 64 z * BitVec.ofNat 64 qinv) &&& BitVec.ofNat 64 (R - 1)).toNat
      = (y.toNat * z * qinv) % R := by
    rw [BitVec.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_mul, hTw,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqi, hR,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hlog)]
  have hmR : (y.toNat * z * qinv) % R < R := Nat.mod_lt _ hRpos
  have hmq : (y.toNat * z * qinv) % R * q < R * q := Nat.mul_lt_mul_of_pos_right hmR (by omega)
  have hlogw : (BitVec.ofNat 64 logR).toNat = logR := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := logR); omega)]
  have hmqw : (((y * BitVec.ofNat 64 z * BitVec.ofNat 64 qinv) &&& BitVec.ofNat 64 (R - 1))
      * BitVec.ofNat 64 q).toNat = (y.toNat * z * qinv) % R * q := by
    rw [BitVec.toNat_mul, hm, BitVec.toNat_ofNat q, Nat.mod_eq_of_lt hq64]
    exact Nat.mod_eq_of_lt (by omega)
  have hsum : (y * BitVec.ofNat 64 z + ((y * BitVec.ofNat 64 z * BitVec.ofNat 64 qinv)
      &&& BitVec.ofNat 64 (R - 1)) * BitVec.ofNat 64 q).toNat
      = y.toNat * z + (y.toNat * z * qinv) % R * q := by
    rw [BitVec.toNat_add, hTw, hmqw]
    exact Nat.mod_eq_of_lt (by omega)
  rw [montW, BitVec.toNat_ushiftRight, hsum, hlogw, Nat.shiftRight_eq_div_pow, ← hR,
    montgomeryReduce, Nat.mul_comm z]

/-! ## 3. The butterfly lane schedule -/

/-- A `regConst 64 n` expression. -/
def constW {Γ : Ctxt jasminDialect} (n : ℕ) : Expr jasminDialect Γ (.reg 64) :=
  { op := .regConst 64 n, retTy_eq := rfl, args := .nil }

/-- A `regArith op 64` expression. -/
def binW {Γ : Ctxt jasminDialect} (op : JasminBinOp) (a b : Var Γ (.reg 64)) :
    Expr jasminDialect Γ (.reg 64) :=
  { op := .regArith op 64, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- The 64-bit register type. -/
abbrev R64 : jasminDialect.Ty := JasminTy.reg 64

/-- The 64-bit lane context. -/
abbrev Ctxw (n : ℕ) : Ctxt jasminDialect := List.replicate n R64

/-- A variable carried past the bindings `Δ`. -/
def thereN {Γ : Ctxt jasminDialect} {t : jasminDialect.Ty} :
    (Δ : List jasminDialect.Ty) → Var Γ t → Var (Δ ++ Γ) t
  | [], v => v
  | _ :: Δ, v => .there (thereN Δ v)

/-- One butterfly lane on 64-bit words: the Montgomery product `u` of `a[ib]` by
the constant `z`, then `a[ia] + u` when `up`, and `a[ia] + offq − u` otherwise. -/
def montLaneProg (q R qinv logR offq z : ℕ) :
    (n : ℕ) → ℕ → ℕ → Bool → Com jasminDialect (Ctxw n) (.reg 64)
  | 0, _, _, _ => .var (constW 0) (.ret .here)
  | n + 1, ia, ib, up =>
      .var (constW z)
      (.var (binW .mul (laneVarG R64 n ib).there .here)
      (.var (constW qinv)
      (.var (binW .mul (.there .here) .here)
      (.var (constW (R - 1))
      (.var (binW .and (.there .here) .here)
      (.var (constW q)
      (.var (binW .mul (.there .here) .here)
      (.var (binW .add (.there (.there (.there (.there (.there (.there .here)))))) .here)
      (.var (constW logR)
      (.var (binW .shr (.there .here) .here)
      (if up then
        .var (binW .add (thereN (List.replicate 11 R64) (laneVarG R64 n ia)) .here) (.ret .here)
      else
        .var (constW offq)
        (.var (binW .add (thereN (List.replicate 12 R64) (laneVarG R64 n ia)) .here)
        (.var (binW .sub .here (.there (.there .here))) (.ret .here))))))))))))))

theorem montLaneProg_denote (q R qinv logR offq z n ia ib : ℕ) (up : Bool)
    (V : Valuation (Ctxw (n + 1))) :
    (montLaneProg q R qinv logR offq z (n + 1) ia ib up).denote V
      = if up then (show BitVec 64 from (laneVarG R64 n ia).lookup V)
          + montW q R qinv logR z ((laneVarG R64 n ib).lookup V)
        else (show BitVec 64 from (laneVarG R64 n ia).lookup V) + BitVec.ofNat 64 offq
          - montW q R qinv logR z ((laneVarG R64 n ib).lookup V) := by
  cases up <;> rfl

/-! ## 4. One lazy layer on word lanes -/

variable (P : NttParams) (S : LazySched) (logR : ℕ)

/-- Layer `ℓ` of the lazy schedule on word lanes. -/
def semW (ℓ : ℕ) (g : ℕ → BitVec 64) (i : ℕ) : BitVec 64 :=
  if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ) then
    g i + montW P.q S.R S.qinv logR
      (zr P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))))
      (g (i + 2 ^ (P.logN - 1 - ℓ)))
  else
    g (i - 2 ^ (P.logN - 1 - ℓ)) + BitVec.ofNat 64 (S.off * P.q)
      - montW P.q S.R S.qinv logR
        (zr P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)))) (g i)

/-- The lane schedules of lazy layer `ℓ` on `2 ^ logN` word lanes. -/
def lazyLaneProgW (ℓ i : ℕ) : Com jasminDialect (Ctxw (2 ^ P.logN)) (.reg 64) :=
  if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ) then
    montLaneProg P.q S.R S.qinv logR (S.off * P.q)
      (zr P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))))
      (2 ^ P.logN) i (i + 2 ^ (P.logN - 1 - ℓ)) true
  else
    montLaneProg P.q S.R S.qinv logR (S.off * P.q)
      (zr P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))))
      (2 ^ P.logN) (i - 2 ^ (P.logN - 1 - ℓ)) i false

theorem lazyLaneProgW_denote (ℓ : ℕ) (hl : ℓ < P.logN) (g : ℕ → BitVec 64) (i : ℕ)
    (hi : i < 2 ^ P.logN) :
    (lazyLaneProgW P S logR ℓ i).denote (lanesVal R64 g (2 ^ P.logN) 0)
      = semW P S logR ℓ g i := by
  have hpart := layer_partner_lt P.logN ℓ i hl hi
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ P.logN = m + 1 := ⟨2 ^ P.logN - 1, by
    have := Nat.two_pow_pos P.logN; omega⟩
  unfold lazyLaneProgW semW
  generalize 2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) = k
  revert hpart hi
  rw [hm]
  intro hi hpart
  generalize 2 ^ (P.logN - 1 - ℓ) = len at hpart ⊢
  split
  · next hlt =>
    rw [montLaneProg_denote, if_pos rfl, laneVarG_lookup R64 g m i 0 (by omega),
      laneVarG_lookup R64 g m (i + len) 0 (by have := hpart hlt; omega)]
    simp only [Nat.zero_add]
  · next hlt =>
    rw [montLaneProg_denote, if_neg (by simp), laneVarG_lookup R64 g m (i - len) 0 (by omega),
      laneVarG_lookup R64 g m i 0 (by omega)]
    simp only [Nat.zero_add]

/-- The side condition of the word lowering, decidable on `ℕ`: the radix is
`2 ^ logR` with `logR ≤ 64`, the schedule's words are at most 32 bits wide, the
Montgomery constant fits a word, and no layer is reduced. -/
def WordOk : Prop :=
  S.R = 2 ^ logR ∧ logR ≤ 64 ∧ S.w ≤ 32 ∧ S.qinv < 2 ^ 64 ∧
    ∀ ℓ, ℓ < P.layers → S.red ℓ = false

instance : Decidable (WordOk P S logR) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- On representatives below `bnd ℓ`, one word layer is `lazyLayer` read as
words. -/
theorem semW_ofNat (hS : SchedOk P S) (hW : WordOk P S logR) (hq : 0 < P.q) (ℓ : ℕ)
    (hl : ℓ < P.layers) (f : ℕ → ℕ) (hf : ∀ j, f j < bnd P S ℓ) :
    semW P S logR ℓ (fun j => BitVec.ofNat 64 (f j))
      = fun i => BitVec.ofNat 64 (lazyLayer P S ℓ f i) := by
  obtain ⟨hR, hlog, hw, hqi, hred⟩ := hW
  obtain ⟨hoff, hRpos, _, hN, hRw, hb⟩ := hS
  have hbℓ := hb ℓ (by omega)
  have hw64 : (2 : ℕ) ^ S.w ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hw
  have h2w : (2 : ℕ) ^ (2 * S.w) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h32 : (2 : ℕ) ^ 32 < 2 ^ 64 := by norm_num
  have hfw : ∀ j, f j < 2 ^ 64 := fun j => by have := hf j; omega
  have hoffq : 2 * P.q ≤ S.off * P.q := Nat.mul_le_mul_right _ hoff
  funext i
  have hofn : ∀ j, (BitVec.ofNat 64 (f j)).toNat = f j := fun j => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hfw j)]
  apply BitVec.eq_of_toNat_eq
  simp only [semW, lazyLayer, hred ℓ hl, Bool.false_eq_true, if_false]
  generalize 2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) = k
  generalize 2 ^ (P.logN - 1 - ℓ) = len
  have hmont : ∀ j, (montW P.q S.R S.qinv logR (zr P S k) (BitVec.ofNat 64 (f j))).toNat
      = tmul P S k (f j) := fun j => by
    rw [montW_toNat _ _ _ _ _ _ hR hlog (zr_lt P S hq k) (by rw [hofn]; have := hf j; omega)
      (by omega) hqi, hofn, tmul]
  have ht : ∀ j, tmul P S k (f j) < 2 * P.q := fun j =>
    tmul_lt P S hq hRpos hN k (f j) (by have := hf j; omega)
  split
  · rw [BitVec.toNat_add, hofn, hmont, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := hf i; have := ht (i + len); omega)]
  · have hoq : (BitVec.ofNat 64 (S.off * P.q)).toNat = S.off * P.q := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hadd : (BitVec.ofNat 64 (f (i - len)) + BitVec.ofNat 64 (S.off * P.q)).toNat
        = f (i - len) + S.off * P.q := by
      rw [BitVec.toNat_add, hofn, hoq, Nat.mod_eq_of_lt (by have := hf (i - len); omega)]
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hadd, hmont]; have := ht i; omega), hadd,
      hmont,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf (i - len); omega)]

/-! ## 5. The transform program -/

/-- The lazy Montgomery transform program on `2 ^ logN` lanes of 64-bit words. -/
def nttProgW : MultiReturnCom jasminDialect (Ctxw (2 ^ P.logN)) (Ctxw (2 ^ P.logN)) :=
  chainD R64 (2 ^ P.logN) (lazyLaneProgW P S logR) (List.range P.layers) (Ctxt.Hom.id _)

theorem lazyRun_succ_last :
    ∀ (k ℓ : ℕ) (f : ℕ → ℕ), lazyRun P S (k + 1) ℓ f = lazyLayer P S (ℓ + k) (lazyRun P S k ℓ f)
  | 0, _, _ => rfl
  | k + 1, ℓ, f => by
      rw [lazyRun, lazyRun_succ_last k (ℓ + 1), show ℓ + 1 + k = ℓ + (k + 1) from by omega]
      rfl

theorem foldl_semW (hS : SchedOk P S) (hW : WordOk P S logR) (hq : 0 < P.q) (f : ℕ → ℕ)
    (hf : ∀ j, f j < P.q) :
    ∀ k, k ≤ P.layers → (List.range k).foldl (fun g ℓ => semW P S logR ℓ g)
        (fun j => BitVec.ofNat 64 (f j)) = fun j => BitVec.ofNat 64 (lazyRun P S k 0 f j)
  | 0, _ => rfl
  | k + 1, hk => by
      rw [List.range_succ, List.foldl_append, foldl_semW hS hW hq f hf k (by omega),
        List.foldl_cons, List.foldl_nil, lazyRun_succ_last, Nat.zero_add]
      have hb := lazyRun_lt P S hS hq k 0 f (by omega) hf
      rw [Nat.zero_add] at hb
      exact semW_ofNat P S logR hS hW hq k (by omega) _ hb

/-- **The word lowering.** For a parameter record satisfying `NttParams.Ok`, a
schedule satisfying `SchedOk` and `WordOk`, and inputs below `q`, every output
word of `nttProgW` is below `bnd L` (no lane wraps), and cast to `ZMod q` it is
`nttSpec`. -/
theorem nttProgW_denote (hP : P.Ok) (hS : SchedOk P S) (hW : WordOk P S logR) (f : ℕ → ℕ)
    (hf : ∀ j, f j < P.q) (i : ℕ) (hi : i < 2 ^ P.logN) :
    (hvGetG R64 (0 : BitVec 64) ((nttProgW P S logR).denote
        (lanesVal R64 (fun j => BitVec.ofNat 64 (f j)) (2 ^ P.logN) 0)) i).toNat
        < bnd P S P.layers ∧
    (((hvGetG R64 (0 : BitVec 64) ((nttProgW P S logR).denote
        (lanesVal R64 (fun j => BitVec.ofNat 64 (f j)) (2 ^ P.logN) 0)) i).toNat : ℕ) : ZMod P.q)
      = nttSpec (P.psi : ZMod P.q) P.layers P.logN (fun j => (f j : ZMod P.q)) i := by
  have hq : 0 < P.q := by have := hP.2.2.1; omega
  have hLM := hP.2.1
  rw [nttProgW, chainD_denote R64 (2 ^ P.logN) (0 : BitVec 64) _ (semW P S logR)
    (List.range P.layers)
    (fun ℓ hℓ g j hj => lazyLaneProgW_denote P S logR ℓ
      (by have := List.mem_range.mp hℓ; omega) g j hj)
    (Ctxt.Hom.id _) _ _ (pullV_id _)]
  erw [foldl_semW P S logR hS hW hq f hf P.layers le_rfl]
  rw [hvGetG_lanesVal _ _ _ _ _ _ hi, Nat.zero_add]
  have hlt := lazyRun_lt P S hS hq P.layers 0 f (by omega) hf i
  rw [Nat.zero_add] at hlt
  have hb := (hS.2.2.2.2.2 P.layers (by omega)).2
  have hw : (2 : ℕ) ^ S.w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by have := hW.2.2.1; omega)
  have hval : (BitVec.ofNat 64 (lazyRun P S P.layers 0 f i)).toNat
      = lazyRun P S P.layers 0 f i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hval]
  refine ⟨hlt, ?_⟩
  rw [lazyRun_cast P S hS hq P.layers 0 f (by omega) hf i]
  exact run_spec _ P.layers P.logN (P.psi_pow hP) hP.1 hLM _ i hi

/-- The ML-KEM word schedule: radix `2 ^ 16`. -/
theorem mlkemWord_ok : WordOk mlkemNtt mlkemLazy 16 := by decide

/-- The ML-DSA word schedule: radix `2 ^ 32`. -/
theorem mldsaWord_ok : WordOk mldsaNtt mldsaLazy 32 := by decide

end CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
