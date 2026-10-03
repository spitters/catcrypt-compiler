/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttInverse
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

`nttProgW` and `inttProgW` keep products and reductions inside 64-bit lanes.
`nttProgUW` and `inttProgUW` are the lowerings at the schedule's word width
`S.w`: lanes are `S.w`-bit registers, the product and the Montgomery step are
formed at `2 S.w` bits between two `castW`s, and at the layers `S.red` marks the
lane is reduced modulo `q` by an unsigned Barrett reduction
`a − ((a · m) >> k) · q`, exact by `mul_div_eq_div_of_lt` under `UWordOk`.

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
* `montTail`, `gsLaneProgW`, `scaleLaneProgW` — the Montgomery multiply of a
  word variable by a constant, the Gentleman–Sande lane and the scaling lane.
* `zrc`, `zrInv`, `invSemW`, `invLaneProgW`, `invStagesW`, `inttProgW` — a
  constant and an inverse twiddle in Montgomery form, one inverse stage on word
  lanes, its lane schedules, the stage list, and the inverse transform program.
* `InvWordOk` — the decidable side condition of the inverse word lowering.
* `constE`, `binE`, `castE`, `shrE`, `Rw`, `Ctxs` — expression builders and lane
  contexts at a width `w`.
* `umontW`, `ubarW`, `redW` — the Montgomery multiply and the Barrett reduction on
  `w`-bit words with products at `2 w` bits, and the reduction at a marked layer.
* `uTail`, `uLaneProg`, `semUW`, `uLayerLaneProgW`, `nttProgUW` — the lane
  schedules, one layer and the transform program at the schedule's width.
* `barK`, `barM`, `BarOk`, `UWordOk` — the Barrett shift and constant of a
  schedule, the Barrett side condition and the decidable side condition of the
  lowering at the schedule's width.
* `umontTail`, `uGsLaneProg`, `uScaleLaneProg`, `invSemUW`, `invLaneProgUW`,
  `inttProgUW`, `UInvWordOk` — the inverse transform at the schedule's width and
  its side condition.

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
* `montW_zrc` — the Montgomery word multiply by `c · R mod q` of an operand at
  most `R` is below `2 q` and congruent to `c` times the operand.
* `inttProgW_denote` — every output word of `inttProgW` is below `2 q`, and cast
  to `ZMod q` it is `inttSpec`.
* `inttProgW_nttProgW` — `inttProgW` after `nttProgW` returns its input modulo
  `q`, with every word below `2 q`.
* `umontW_toNat`, `mul_div_eq_div_of_lt`, `ubarW_toNat` — the Montgomery word
  multiply at `2 w` bits is `montgomeryReduce`, exact division by a constant, and
  the Barrett word reduction is the remainder modulo `q`.
* `nttProgUW_denote`, `inttProgUW_denote`, `inttProgUW_nttProgUW` — the
  lowerings at the schedule's width compute `nttSpec`, `inttSpec` and the round
  trip.
* `mlkemUWord_ok`, `mldsaUWord_ok`, `mlkemLazyRed3_ok`, `mlkemUInvWord_ok`,
  `mldsaUInvWord_ok` — the side conditions of the ML-KEM 16-bit, ML-DSA 32-bit
  and ML-KEM 16-bit reduced schedules, by kernel `decide`.
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
open CatCrypt.Crypto.Number (montgomeryReduce montgomeryReduce_correct)
open CatCrypt.Crypto.Optimizer.Lattice.BitReversalGeneric (bitrev)

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

theorem hvGetG_of_le (dflt : ⟦τ⟧) :
    ∀ {m : ℕ} (hv : ListDenote (List.replicate m τ)) (i : ℕ), m ≤ i → hvGetG τ dflt hv i = dflt
  | 0, _, _, _ => rfl
  | _ + 1, .cons _ _, 0, h => absurd h (by omega)
  | _ + 1, .cons _ r, i + 1, h => hvGetG_of_le dflt r i (by omega)

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

/-! ## 6. The inverse transform on words -/

/-- The Montgomery multiply of the word variable `v` by the constant `z`, as the
`jasminDialect` schedule of `montW`. -/
def montTail (q R qinv logR z : ℕ) {Γ : Ctxt jasminDialect} (v : Var Γ R64) :
    Com jasminDialect Γ R64 :=
  .var (constW z)
  (.var (binW .mul v.there .here)
  (.var (constW qinv)
  (.var (binW .mul (.there .here) .here)
  (.var (constW (R - 1))
  (.var (binW .and (.there .here) .here)
  (.var (constW q)
  (.var (binW .mul (.there .here) .here)
  (.var (binW .add (.there (.there (.there (.there (.there (.there .here)))))) .here)
  (.var (constW logR)
  (.var (binW .shr (.there .here) .here) (.ret .here)))))))))))

theorem montTail_denote (q R qinv logR z : ℕ) {Γ : Ctxt jasminDialect} (v : Var Γ R64)
    (V : Valuation Γ) :
    (montTail q R qinv logR z v).denote V
      = montW q R qinv logR z (show BitVec 64 from v.lookup V) := rfl

/-- One Gentleman–Sande lane on 64-bit words: the Montgomery product by the
constant `z` of `a[ia] + a[ib]` when `up`, and of `a[ia] + offq − a[ib]`
otherwise. -/
def gsLaneProgW (q R qinv logR offq z : ℕ) :
    (n : ℕ) → ℕ → ℕ → Bool → Com jasminDialect (Ctxw n) (.reg 64)
  | 0, _, _, _ => .var (constW 0) (.ret .here)
  | n + 1, ia, ib, up =>
      if up then
        .var (binW .add (laneVarG R64 n ia) (laneVarG R64 n ib))
          (montTail q R qinv logR z .here)
      else
        .var (constW offq)
        (.var (binW .add (laneVarG R64 n ia).there .here)
        (.var (binW .sub .here (thereN (List.replicate 2 R64) (laneVarG R64 n ib)))
        (montTail q R qinv logR z .here)))

theorem gsLaneProgW_denote (q R qinv logR offq z n ia ib : ℕ) (up : Bool)
    (V : Valuation (Ctxw (n + 1))) :
    (gsLaneProgW q R qinv logR offq z (n + 1) ia ib up).denote V
      = montW q R qinv logR z
          (if up then (show BitVec 64 from (laneVarG R64 n ia).lookup V)
            + (laneVarG R64 n ib).lookup V
          else (show BitVec 64 from (laneVarG R64 n ia).lookup V) + BitVec.ofNat 64 offq
            - (laneVarG R64 n ib).lookup V) := by
  cases up <;> rfl

/-- One scaling lane on 64-bit words: the Montgomery product of `a[i]` by the
constant `z`. -/
def scaleLaneProgW (q R qinv logR z : ℕ) : (n : ℕ) → ℕ → Com jasminDialect (Ctxw n) (.reg 64)
  | 0, _ => .var (constW 0) (.ret .here)
  | n + 1, i => montTail q R qinv logR z (laneVarG R64 n i)

/-- The constant `c` in Montgomery form: `c · R mod q`. -/
def zrc (c : ℕ) : ℕ := c * S.R % P.q

/-- The inverse twiddle of block `k` in Montgomery form:
`ψ ^ (2 ^ (L + 1) − BitRev_L k) · R mod q`. -/
def zrInv (k : ℕ) : ℕ := zrc P S (P.psi ^ (2 ^ (P.layers + 1) - bitrev P.layers k))

/-- Stage `st` of the inverse transform on word lanes: the scaling by `s` for
`none`; for `some ℓ`, inverse layer `ℓ`, whose lower lane is the Montgomery
product of `u + v` by `1` and whose upper lane is the Montgomery product of
`u + 2 q − v` by the inverse twiddle. -/
def invSemW (s : ℕ) : Option ℕ → (ℕ → BitVec 64) → ℕ → BitVec 64
  | none, g, i => montW P.q S.R S.qinv logR (zrc P S s) (g i)
  | some ℓ, g, i =>
      if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ) then
        montW P.q S.R S.qinv logR (zrc P S 1) (g i + g (i + 2 ^ (P.logN - 1 - ℓ)))
      else
        montW P.q S.R S.qinv logR
          (zrInv P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))))
          (g (i - 2 ^ (P.logN - 1 - ℓ)) + BitVec.ofNat 64 (2 * P.q) - g i)

/-- The lane schedules of inverse word stage `st` on `2 ^ logN` lanes. -/
def invLaneProgW (s : ℕ) : Option ℕ → ℕ → Com jasminDialect (Ctxw (2 ^ P.logN)) (.reg 64)
  | none, i => scaleLaneProgW P.q S.R S.qinv logR (zrc P S s) (2 ^ P.logN) i
  | some ℓ, i =>
      if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ) then
        gsLaneProgW P.q S.R S.qinv logR (2 * P.q) (zrc P S 1) (2 ^ P.logN)
          i (i + 2 ^ (P.logN - 1 - ℓ)) true
      else
        gsLaneProgW P.q S.R S.qinv logR (2 * P.q)
          (zrInv P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))))
          (2 ^ P.logN) (i - 2 ^ (P.logN - 1 - ℓ)) i false

/-- The inverse word stages: the scaling, then layers `L - 1, …, 0`. -/
def invStagesW (L : ℕ) : List (Option ℕ) := none :: (List.range L).reverse.map some

theorem invLaneProgW_denote (s : ℕ) (st : Option ℕ) (hst : ∀ ℓ, st = some ℓ → ℓ < P.logN)
    (g : ℕ → BitVec 64) (i : ℕ) (hi : i < 2 ^ P.logN) :
    (invLaneProgW P S logR s st i).denote (lanesVal R64 g (2 ^ P.logN) 0)
      = invSemW P S logR s st g i := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ P.logN = m + 1 := ⟨2 ^ P.logN - 1, by
    have := Nat.two_pow_pos P.logN; omega⟩
  cases st with
  | none =>
    simp only [invLaneProgW, invSemW]
    revert hi
    rw [hm]
    intro hi
    rw [scaleLaneProgW.eq_2, montTail_denote, laneVarG_lookup R64 g m i 0 (by omega), Nat.zero_add]
  | some ℓ =>
    have hpart := layer_partner_lt P.logN ℓ i (hst ℓ rfl) hi
    simp only [invLaneProgW, invSemW]
    generalize 2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) = k
    revert hpart hi
    rw [hm]
    intro hi hpart
    generalize 2 ^ (P.logN - 1 - ℓ) = len at hpart ⊢
    split
    · next hlt =>
      rw [gsLaneProgW_denote, if_pos rfl, laneVarG_lookup R64 g m i 0 (by omega),
        laneVarG_lookup R64 g m (i + len) 0 (by have := hpart hlt; omega)]
      simp only [Nat.zero_add]
    · next hlt =>
      rw [gsLaneProgW_denote, if_neg (by simp), laneVarG_lookup R64 g m (i - len) 0 (by omega),
        laneVarG_lookup R64 g m i 0 (by omega)]
      simp only [Nat.zero_add]

/-- The inverse transform program of scaling constant `s` on `2 ^ logN` lanes
of 64-bit words: every lane multiplied by `s`, then inverse layers
`L - 1, …, 0`, each lane reduced below `2 q` by a Montgomery multiply. -/
def inttProgW (s : ℕ) : MultiReturnCom jasminDialect (Ctxw (2 ^ P.logN)) (Ctxw (2 ^ P.logN)) :=
  chainD R64 (2 ^ P.logN) (invLaneProgW P S logR s) (invStagesW P.layers) (Ctxt.Hom.id _)

/-- The side condition of the inverse word lowering, decidable on `ℕ`: a sum of
two lanes below `2 q` is at most `R`. -/
def InvWordOk : Prop := 4 * P.q ≤ S.R

instance : Decidable (InvWordOk P S) := inferInstanceAs (Decidable (_ ≤ _))

/-- Under `SchedOk` and `WordOk` the radix is below `2 ^ 64`. -/
theorem R_lt_word (hS : SchedOk P S) (hW : WordOk P S logR) (hq : 0 < P.q) :
    S.R < 2 ^ 64 := by
  have h2w : (2 : ℕ) ^ (2 * S.w) ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by norm_num) (by have := hW.2.2.1; omega)
  have hRw := hS.2.2.2.2.1
  have hRpos := hS.2.1
  have : 2 * S.R ≤ 2 * P.q * S.R := by nlinarith
  omega

/-- The Montgomery word multiply by a constant `c` in Montgomery form, on an
operand at most `R`, is below `2 q` and congruent to `c` times the operand. -/
theorem montW_zrc (hS : SchedOk P S) (hW : WordOk P S logR) (hq : 0 < P.q) (c : ℕ)
    (y : BitVec 64) (hy : y.toNat ≤ S.R) :
    (montW P.q S.R S.qinv logR (zrc P S c) y).toNat < 2 * P.q ∧
    (((montW P.q S.R S.qinv logR (zrc P S c) y).toNat : ℕ) : ZMod P.q)
      = (c : ZMod P.q) * (y.toNat : ZMod P.q) := by
  obtain ⟨hR, hlog, hw, hqi, _⟩ := hW
  obtain ⟨_, hRpos, hcop, hN, hRw, _⟩ := hS
  have h2w : (2 : ℕ) ^ (2 * S.w) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hzq : zrc P S c < P.q := Nat.mod_lt _ hq
  rw [montW_toNat _ _ _ _ _ _ hR hlog hzq hy (by omega) hqi]
  have hT : zrc P S c * y.toNat < S.R * P.q := by
    have h1 : zrc P S c * y.toNat ≤ zrc P S c * S.R := Nat.mul_le_mul_left _ hy
    have h2 : zrc P S c * S.R < P.q * S.R := Nat.mul_lt_mul_of_pos_right hzq hRpos
    rw [Nat.mul_comm S.R]
    omega
  obtain ⟨hlt, hmod⟩ := montgomeryReduce_correct P.q S.R S.qinv _ hq hRpos hN hT
  refine ⟨hlt, ?_⟩
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  rw [Nat.cast_mul, Nat.cast_mul, zrc, ZMod.natCast_mod, Nat.cast_mul] at hcast
  have hu : IsUnit ((S.R : ℕ) : ZMod P.q) := ⟨ZMod.unitOfCoprime S.R hcop, rfl⟩
  apply hu.mul_left_inj.mp
  rw [zrc, hcast]
  ring

/-- On lanes below `2 q`, one inverse word layer stays below `2 q` and casts to
`invLayerFn`. -/
theorem invSemW_layer (hS : SchedOk P S) (hW : WordOk P S logR) (hI : InvWordOk P S)
    (hq : 0 < P.q) (s ℓ : ℕ) (g : ℕ → BitVec 64) (hg : ∀ j, (g j).toNat < 2 * P.q) (i : ℕ) :
    (invSemW P S logR s (some ℓ) g i).toNat < 2 * P.q ∧
    (((invSemW P S logR s (some ℓ) g i).toNat : ℕ) : ZMod P.q)
      = invLayerFn (P.psi : ZMod P.q) P.layers P.logN ℓ (fun j => ((g j).toNat : ZMod P.q)) i := by
  have hR64 := R_lt_word P S logR hS hW hq
  unfold InvWordOk at hI
  simp only [invSemW, invLayerFn, zrInv]
  generalize 2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) = k
  generalize 2 ^ (P.logN - 1 - ℓ) = len
  split
  · have hsum : (g i + g (i + len)).toNat = (g i).toNat + (g (i + len)).toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := hg i; have := hg (i + len); omega)]
    obtain ⟨h1, h2⟩ := montW_zrc P S logR hS hW hq 1 _
      (by rw [hsum]; have := hg i; have := hg (i + len); omega)
    refine ⟨h1, ?_⟩
    rw [h2, hsum]
    push_cast
    ring
  · have hoq : (BitVec.ofNat 64 (2 * P.q)).toNat = 2 * P.q := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hadd : (g (i - len) + BitVec.ofNat 64 (2 * P.q)).toNat = (g (i - len)).toNat + 2 * P.q := by
      rw [BitVec.toNat_add, hoq, Nat.mod_eq_of_lt (by have := hg (i - len); omega)]
    have hsub : (g (i - len) + BitVec.ofNat 64 (2 * P.q) - g i).toNat
        = (g (i - len)).toNat + 2 * P.q - (g i).toNat := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hadd]; have := hg i; omega), hadd]
    obtain ⟨h1, h2⟩ := montW_zrc P S logR hS hW hq
      (P.psi ^ (2 ^ (P.layers + 1) - bitrev P.layers k)) _
      (by rw [hsub]; have := hg i; have := hg (i - len); omega)
    refine ⟨h1, ?_⟩
    rw [h2, hsub, Nat.cast_sub (by have := hg i; omega), Nat.cast_add, Nat.cast_mul,
      ZMod.natCast_self, Nat.cast_pow, ztInv]
    ring

theorem foldl_invSemW_layers (hS : SchedOk P S) (hW : WordOk P S logR) (hI : InvWordOk P S)
    (hq : 0 < P.q) (s : ℕ) :
    ∀ (k : ℕ) (g : ℕ → BitVec 64), (∀ j, (g j).toNat < 2 * P.q) →
      (∀ j, ((((List.range k).reverse.map some).foldl
          (fun g st => invSemW P S logR s st g) g) j).toNat < 2 * P.q) ∧
      (fun j => (((((List.range k).reverse.map some).foldl
          (fun g st => invSemW P S logR s st g) g) j).toNat : ZMod P.q))
        = invRun (P.psi : ZMod P.q) P.layers P.logN k (fun j => ((g j).toNat : ZMod P.q))
  | 0, _, hg => ⟨hg, rfl⟩
  | k + 1, g, hg => by
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons, List.foldl_cons]
      have hl := fun j => invSemW_layer P S logR hS hW hI hq s k g hg j
      obtain ⟨h1, h2⟩ := foldl_invSemW_layers hS hW hI hq s k _ (fun j => (hl j).1)
      refine ⟨h1, ?_⟩
      rw [h2, invRun]
      congr 1
      funext j
      exact (hl j).2

/-- **The inverse word lowering, on words.** For a parameter record satisfying
`NttParams.Ok`, a schedule satisfying `SchedOk`, `WordOk` and `InvWordOk`, and
input words at most `R`, every output word of `inttProgW` is below `2 q`, and
cast to `ZMod q` it is `inttSpec` of the input words. -/
theorem inttProgW_denote_words (hP : P.Ok) (hS : SchedOk P S) (hW : WordOk P S logR)
    (hI : InvWordOk P S) (s : ℕ) (g : ℕ → BitVec 64) (hg : ∀ j, (g j).toNat ≤ S.R) (i : ℕ)
    (hi : i < 2 ^ P.logN) :
    (hvGetG R64 (0 : BitVec 64) ((inttProgW P S logR s).denote
        (lanesVal R64 g (2 ^ P.logN) 0)) i).toNat < 2 * P.q ∧
    (((hvGetG R64 (0 : BitVec 64) ((inttProgW P S logR s).denote
        (lanesVal R64 g (2 ^ P.logN) 0)) i).toNat : ℕ) : ZMod P.q)
      = inttSpec (P.psi : ZMod P.q) P.layers P.logN (s : ZMod P.q)
          (fun j => ((g j).toNat : ZMod P.q)) i := by
  have hq : 0 < P.q := by have := hP.2.2.1; omega
  rw [inttProgW, chainD_denote R64 (2 ^ P.logN) (0 : BitVec 64) _ (invSemW P S logR s)
    (invStagesW P.layers)
    (fun st hst h j hj => invLaneProgW_denote P S logR s st (fun ℓ hℓ => by
        subst hℓ
        simp only [invStagesW, List.mem_cons, List.mem_map, List.mem_reverse,
          List.mem_range] at hst
        rcases hst with h0 | ⟨ℓ', h1, h2⟩
        · cases h0
        · cases h2; have := hP.2.1; omega) h j hj)
    (Ctxt.Hom.id _) _ _ (pullV_id _)]
  rw [hvGetG_lanesVal _ _ _ _ _ _ hi, Nat.zero_add, invStagesW, List.foldl_cons]
  have hsc := fun j => montW_zrc P S logR hS hW hq s (g j) (hg j)
  obtain ⟨h1, h2⟩ := foldl_invSemW_layers P S logR hS hW hI hq s P.layers
    (invSemW P S logR s none g) (fun j => (hsc j).1)
  refine ⟨h1 i, (congrFun h2 i).trans ?_⟩
  rw [inttSpec,
    show (fun j => (((invSemW P S logR s none g j).toNat : ℕ) : ZMod P.q))
      = fun j => (s : ZMod P.q) * ((g j).toNat : ZMod P.q) from funext fun j => (hsc j).2,
    invRun_smul]

/-- **The inverse word lowering.** For a parameter record satisfying
`NttParams.Ok`, a schedule satisfying `SchedOk`, `WordOk` and `InvWordOk`, and
inputs at most `R`, every output word of `inttProgW` is below `2 q`, and cast to
`ZMod q` it is `inttSpec`. -/
theorem inttProgW_denote (hP : P.Ok) (hS : SchedOk P S) (hW : WordOk P S logR)
    (hI : InvWordOk P S) (s : ℕ) (f : ℕ → ℕ) (hf : ∀ j, f j ≤ S.R) (i : ℕ)
    (hi : i < 2 ^ P.logN) :
    (hvGetG R64 (0 : BitVec 64) ((inttProgW P S logR s).denote
        (lanesVal R64 (fun j => BitVec.ofNat 64 (f j)) (2 ^ P.logN) 0)) i).toNat < 2 * P.q ∧
    (((hvGetG R64 (0 : BitVec 64) ((inttProgW P S logR s).denote
        (lanesVal R64 (fun j => BitVec.ofNat 64 (f j)) (2 ^ P.logN) 0)) i).toNat : ℕ) : ZMod P.q)
      = inttSpec (P.psi : ZMod P.q) P.layers P.logN (s : ZMod P.q)
          (fun j => (f j : ZMod P.q)) i := by
  have hq : 0 < P.q := by have := hP.2.2.1; omega
  have hR64 := R_lt_word P S logR hS hW hq
  have hfw : ∀ j, (BitVec.ofNat 64 (f j)).toNat = f j := fun j => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf j; omega)]
  have := inttProgW_denote_words P S logR hP hS hW hI s _
    (fun j => by rw [hfw]; exact hf j) i hi
  simpa only [hfw] using this

/-- **The word round trip.** For a scaling constant with `ScaleOk` and inputs
below `q`, lane `i` of `inttProgW` applied to the output words of `nttProgW` is
below `2 q` and casts to input `i` in `ZMod q`. -/
theorem inttProgW_nttProgW (hP : P.Ok) (hS : SchedOk P S) (hW : WordOk P S logR)
    (hI : InvWordOk P S) (s : ℕ) (hs : ScaleOk P s) (f : ℕ → ℕ) (hf : ∀ j, f j < P.q) (i : ℕ)
    (hi : i < 2 ^ P.logN) :
    (hvGetG R64 (0 : BitVec 64) ((inttProgW P S logR s).denote ((nttProgW P S logR).denote
        (lanesVal R64 (fun j => BitVec.ofNat 64 (f j)) (2 ^ P.logN) 0))) i).toNat < 2 * P.q ∧
    (((hvGetG R64 (0 : BitVec 64) ((inttProgW P S logR s).denote ((nttProgW P S logR).denote
        (lanesVal R64 (fun j => BitVec.ofNat 64 (f j)) (2 ^ P.logN) 0))) i).toNat : ℕ)
        : ZMod P.q) = (f i : ZMod P.q) := by
  have heq : (nttProgW P S logR).denote
        (lanesVal R64 (fun j => BitVec.ofNat 64 (f j)) (2 ^ P.logN) 0)
      = lanesVal R64 (fun j => hvGetG R64 (0 : BitVec 64) ((nttProgW P S logR).denote
          (lanesVal R64 (fun j => BitVec.ofNat 64 (f j)) (2 ^ P.logN) 0)) j) (2 ^ P.logN) 0 :=
    eq_lanesVal R64 (0 : BitVec 64) _ (2 ^ P.logN) 0 _ (fun j _ => by rw [Nat.zero_add])
  have hb : ∀ j, (hvGetG R64 (0 : BitVec 64) ((nttProgW P S logR).denote
      (lanesVal R64 (fun j => BitVec.ofNat 64 (f j)) (2 ^ P.logN) 0)) j).toNat ≤ S.R := by
    intro j
    by_cases hj : j < 2 ^ P.logN
    · have := (nttProgW_denote P S logR hP hS hW f hf j hj).1
      have := bnd_le_R P S hS P.layers le_rfl
      omega
    · rw [hvGetG_of_le R64 _ _ j (by omega)]
      simp
  rw [heq]
  obtain ⟨h1, h2⟩ := inttProgW_denote_words P S logR hP hS hW hI s _ hb i hi
  refine ⟨h1, ?_⟩
  rw [h2, inttSpec, invRun_congr _ P.layers P.logN P.layers hP.2.1 _
    (nttSpec (P.psi : ZMod P.q) P.layers P.logN (fun j => (f j : ZMod P.q)))
    (fun j hj => (nttProgW_denote P S logR hP hS hW f hf j hj).2) i hi]
  exact inttSpec_nttSpec _ P.layers P.logN (P.psi_pow hP) hP.1 hP.2.1 _ (hs.cast P s) _ i hi

/-- The ML-KEM inverse word schedule: `4 q ≤ 2 ^ 16`. -/
theorem mlkemInvWord_ok : InvWordOk mlkemNtt mlkemLazy := by decide

/-- The ML-DSA inverse word schedule: `4 q ≤ 2 ^ 32`. -/
theorem mldsaInvWord_ok : InvWordOk mldsaNtt mldsaLazy := by decide

/-! ## 7. Words of the schedule's width -/

/-- A `regConst w n` expression. -/
def constE {Γ : Ctxt jasminDialect} (w n : ℕ) : Expr jasminDialect Γ (.reg w) :=
  { op := .regConst w n, retTy_eq := rfl, args := .nil }

/-- A `regArith op w` expression. -/
def binE {Γ : Ctxt jasminDialect} (op : JasminBinOp) (w : ℕ) (a b : Var Γ (.reg w)) :
    Expr jasminDialect Γ (.reg w) :=
  { op := .regArith op w, retTy_eq := rfl, args := .cons a (.cons b .nil) }

/-- A `castW a b` expression. -/
def castE {Γ : Ctxt jasminDialect} (a b : ℕ) (v : Var Γ (.reg a)) :
    Expr jasminDialect Γ (.reg b) :=
  { op := .castW a b, retTy_eq := rfl, args := .cons v .nil }

/-- A `shrImm w n` expression. -/
def shrE {Γ : Ctxt jasminDialect} (w n : ℕ) (v : Var Γ (.reg w)) :
    Expr jasminDialect Γ (.reg w) :=
  { op := .shrImm w n, retTy_eq := rfl, args := .cons v .nil }

/-- The `w`-bit register type. -/
abbrev Rw (w : ℕ) : jasminDialect.Ty := JasminTy.reg w

/-- The `w`-bit lane context. -/
abbrev Ctxs (w n : ℕ) : Ctxt jasminDialect := List.replicate n (Rw w)

/-- The Montgomery multiply of `y` by the constant `z` on `w`-bit words, with the
product and the reduction at `2 w` bits: `T = zext y · z`, then
`(T + ((T · qinv) & (R − 1)) · q) >> logR` truncated to `w` bits. -/
def umontW (w q R qinv logR z : ℕ) (y : BitVec w) : BitVec w :=
  ((y.zeroExtend (2 * w) * BitVec.ofNat (2 * w) z
    + ((y.zeroExtend (2 * w) * BitVec.ofNat (2 * w) z * BitVec.ofNat (2 * w) qinv)
      &&& BitVec.ofNat (2 * w) (R - 1)) * BitVec.ofNat (2 * w) q) >>> logR).zeroExtend w

/-- On in-range operands whose reduction fits a word, the Montgomery word multiply
at `2 w` bits is `montgomeryReduce`. -/
theorem umontW_toNat (w q R qinv logR z : ℕ) (y : BitVec w) (hR : R = 2 ^ logR)
    (hlog : logR ≤ 2 * w) (hzq : z < q) (hy : y.toNat ≤ R) (h2 : 2 * q * R ≤ 2 ^ (2 * w))
    (hfit : montgomeryReduce q R qinv (z * y.toNat) < 2 ^ w) :
    (umontW w q R qinv logR z y).toNat = montgomeryReduce q R qinv (z * y.toNat) := by
  have hRpos : 0 < R := by rw [hR]; exact Nat.two_pow_pos _
  have h2' : 2 * q * R = R * q + R * q := by ring
  have hq64 : q < 2 ^ (2 * w) := by nlinarith
  have hR64 : R ≤ 2 ^ (2 * w) := by nlinarith
  have hz64 : z < 2 ^ (2 * w) := by omega
  have hw2 : (2 : ℕ) ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hyz : (y.zeroExtend (2 * w)).toNat = y.toNat := by
    rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (lt_of_lt_of_le y.isLt hw2)]
  have hT : y.toNat * z < R * q := by
    calc y.toNat * z ≤ R * z := Nat.mul_le_mul_right _ hy
      _ < R * q := Nat.mul_lt_mul_of_pos_left hzq hRpos
  have hTw : (y.zeroExtend (2 * w) * BitVec.ofNat (2 * w) z).toNat = y.toNat * z := by
    rw [BitVec.toNat_mul, hyz, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hz64,
      Nat.mod_eq_of_lt (by omega)]
  have hmask : (BitVec.ofNat (2 * w) (R - 1)).toNat = 2 ^ logR - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hR]
  have hdvd : R ∣ 2 ^ (2 * w) := hR ▸ Nat.pow_dvd_pow 2 hlog
  have hm : ((y.zeroExtend (2 * w) * BitVec.ofNat (2 * w) z * BitVec.ofNat (2 * w) qinv)
      &&& BitVec.ofNat (2 * w) (R - 1)).toNat = (y.toNat * z * qinv) % R := by
    rw [BitVec.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_mul, hTw,
      BitVec.toNat_ofNat, ← hR, Nat.mod_mod_of_dvd _ hdvd, Nat.mul_mod (y.toNat * z),
      Nat.mod_mod_of_dvd _ hdvd, ← Nat.mul_mod]
  have hmR : (y.toNat * z * qinv) % R < R := Nat.mod_lt _ hRpos
  have hmq : (y.toNat * z * qinv) % R * q < R * q := Nat.mul_lt_mul_of_pos_right hmR (by omega)
  have hmqw : (((y.zeroExtend (2 * w) * BitVec.ofNat (2 * w) z * BitVec.ofNat (2 * w) qinv)
      &&& BitVec.ofNat (2 * w) (R - 1)) * BitVec.ofNat (2 * w) q).toNat
      = (y.toNat * z * qinv) % R * q := by
    rw [BitVec.toNat_mul, hm, BitVec.toNat_ofNat q, Nat.mod_eq_of_lt hq64]
    exact Nat.mod_eq_of_lt (by omega)
  have hsum : (y.zeroExtend (2 * w) * BitVec.ofNat (2 * w) z
      + ((y.zeroExtend (2 * w) * BitVec.ofNat (2 * w) z * BitVec.ofNat (2 * w) qinv)
      &&& BitVec.ofNat (2 * w) (R - 1)) * BitVec.ofNat (2 * w) q).toNat
      = y.toNat * z + (y.toNat * z * qinv) % R * q := by
    rw [BitVec.toNat_add, hTw, hmqw]
    exact Nat.mod_eq_of_lt (by omega)
  have hmr : montgomeryReduce q R qinv (z * y.toNat)
      = (y.toNat * z + (y.toNat * z * qinv) % R * q) / 2 ^ logR := by
    rw [montgomeryReduce, ← hR, Nat.mul_comm z]
  rw [umontW, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    hsum, Nat.shiftRight_eq_div_pow, ← hmr, Nat.mod_eq_of_lt hfit]

/-- **Exact division by a constant.** For `D ≤ m · q` and `V · (m · q − D) ≤ D`, the
quotient `⌊x · m / D⌋` of every `x < V` is `⌊x / q⌋`. -/
theorem mul_div_eq_div_of_lt (q D m x V : ℕ) (hq : 0 < q) (hD : 0 < D) (hm : D ≤ m * q)
    (hx : x < V) (he : V * (m * q - D) ≤ D) : x * m / D = x / q := by
  obtain ⟨e, he'⟩ : ∃ e, m * q = D + e := ⟨m * q - D, by omega⟩
  rw [he', Nat.add_sub_cancel_left] at he
  have hxe : x * e < D := by
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · simp [h0, hD]
    · calc x * e < V * e := Nat.mul_lt_mul_of_pos_right hx hpos
        _ ≤ D := he
  have hdm := Nat.div_add_mod x q
  have hr := Nat.mod_lt x hq
  apply Nat.div_eq_of_lt_le
  · refine Nat.le_of_mul_le_mul_left ?_ hq
    calc q * (x / q * D) = (q * (x / q)) * D := by ring
      _ ≤ x * D := Nat.mul_le_mul_right _ (by omega)
      _ ≤ x * (D + e) := Nat.mul_le_mul_left _ (by omega)
      _ = q * (x * m) := by rw [← he']; ring
  · refine Nat.lt_of_mul_lt_mul_left (a := q) ?_
    calc q * (x * m) = x * D + x * e := by
          rw [show q * (x * m) = x * (m * q) by ring, he']; ring
      _ < x * D + D := by omega
      _ = (x + 1) * D := by ring
      _ ≤ (q * (x / q) + q) * D := Nat.mul_le_mul_right _ (by omega)
      _ = q * ((x / q + 1) * D) := by ring

/-- The unsigned Barrett reduction of `x` on `w`-bit words, with products at `2 w`
bits: `a = zext x`, `t = (a · m) >> k`, and `a − t · q` truncated to `w` bits. -/
def ubarW (w q k m : ℕ) (x : BitVec w) : BitVec w :=
  (x.zeroExtend (2 * w) - ((x.zeroExtend (2 * w) * BitVec.ofNat (2 * w) m) >>> k)
    * BitVec.ofNat (2 * w) q).zeroExtend w

/-- For a word below `V` with `V · m ≤ 2 ^ (2 w)`, `2 ^ k ≤ m · q` and
`V · (m · q − 2 ^ k) ≤ 2 ^ k`, the Barrett word reduction is the remainder modulo
`q`. -/
theorem ubarW_toNat (w q k m V : ℕ) (x : BitVec w) (hq : 0 < q) (hqw : q ≤ 2 ^ w)
    (hx : x.toNat < V) (hVm : V * m ≤ 2 ^ (2 * w)) (hm : 2 ^ k ≤ m * q)
    (he : V * (m * q - 2 ^ k) ≤ 2 ^ k) :
    (ubarW w q k m x).toNat = x.toNat % q := by
  have hw2 : (2 : ℕ) ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hxw := x.isLt
  have hyz : (x.zeroExtend (2 * w)).toNat = x.toNat := by
    rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (lt_of_lt_of_le hxw hw2)]
  have hk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, Nat.zero_mul] at hm; omega
    · exact h0
  have hxm : x.toNat * m < 2 ^ (2 * w) :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hx hmpos) hVm
  have hp : (x.zeroExtend (2 * w) * BitVec.ofNat (2 * w) m).toNat = x.toNat * m := by
    rw [BitVec.toNat_mul, hyz, BitVec.toNat_ofNat, Nat.mul_mod_mod, Nat.mod_eq_of_lt hxm]
  have ht : ((x.zeroExtend (2 * w) * BitVec.ofNat (2 * w) m) >>> k).toNat = x.toNat / q := by
    rw [BitVec.toNat_ushiftRight, hp, Nat.shiftRight_eq_div_pow,
      mul_div_eq_div_of_lt q (2 ^ k) m x.toNat V hq hk hm hx he]
  have hdq : x.toNat / q * q ≤ x.toNat := Nat.div_mul_le_self _ _
  have htq : (((x.zeroExtend (2 * w) * BitVec.ofNat (2 * w) m) >>> k)
      * BitVec.ofNat (2 * w) q).toNat = x.toNat / q * q := by
    rw [BitVec.toNat_mul, ht, BitVec.toNat_ofNat, Nat.mul_mod_mod,
      Nat.mod_eq_of_lt (by omega)]
  have hdm := Nat.div_add_mod x.toNat q
  have hr := Nat.mod_lt x.toNat hq
  rw [ubarW, BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def, htq, hyz]; exact hdq), htq, hyz,
    Nat.mod_eq_of_lt (by rw [Nat.mul_comm] at hdm; omega)]
  rw [Nat.mul_comm] at hdm
  omega

/-- The word `x`, Barrett-reduced when `red`. -/
def redW (red : Bool) (w q k m : ℕ) (x : BitVec w) : BitVec w :=
  if red then ubarW w q k m x else x

/-- The tail of a lane schedule: the unsigned Barrett reduction of `v` at `2 w` bits
when `red`, and `v` otherwise. -/
def uTail (red : Bool) (w q k m : ℕ) {Γ : Ctxt jasminDialect} (v : Var Γ (Rw w)) :
    Com jasminDialect Γ (Rw w) :=
  if red then
    .var (castE w (2 * w) v)
    (.var (constE (2 * w) m)
    (.var (binE .mul (2 * w) (.there .here) .here)
    (.var (shrE (2 * w) k .here)
    (.var (constE (2 * w) q)
    (.var (binE .mul (2 * w) (.there .here) .here)
    (.var (binE .sub (2 * w) (.there (.there (.there (.there (.there .here))))) .here)
    (.var (castE (2 * w) w .here) (.ret .here))))))))
  else .ret v

theorem uTail_denote (red : Bool) (w q k m : ℕ) {Γ : Ctxt jasminDialect} (v : Var Γ (Rw w))
    (V : Valuation Γ) :
    (uTail red w q k m v).denote V = redW red w q k m (show BitVec w from v.lookup V) := by
  cases red <;> rfl

/-- One butterfly lane on `w`-bit words with products at `2 w` bits: the Montgomery
product `u` of `a[ib]` by the constant `z`, then `a[ia] + u` when `up` and
`a[ia] + offq − u` otherwise, Barrett-reduced when `red`. -/
def uLaneProg (w q R qinv logR offq z k m : ℕ) (red : Bool) :
    (n : ℕ) → ℕ → ℕ → Bool → Com jasminDialect (Ctxs w n) (Rw w)
  | 0, _, _, _ => .var (constE w 0) (.ret .here)
  | n + 1, ia, ib, up =>
      .var (castE w (2 * w) (laneVarG (Rw w) n ib))
      (.var (constE (2 * w) z)
      (.var (binE .mul (2 * w) (.there .here) .here)
      (.var (constE (2 * w) qinv)
      (.var (binE .mul (2 * w) (.there .here) .here)
      (.var (constE (2 * w) (R - 1))
      (.var (binE .and (2 * w) (.there .here) .here)
      (.var (constE (2 * w) q)
      (.var (binE .mul (2 * w) (.there .here) .here)
      (.var (binE .add (2 * w) (.there (.there (.there (.there (.there (.there .here))))))
        .here)
      (.var (shrE (2 * w) logR .here)
      (.var (castE (2 * w) w .here)
      (if up then
        .var (binE .add w (thereN (Rw w :: List.replicate 11 (Rw (2 * w)))
          (laneVarG (Rw w) n ia)) .here) (uTail red w q k m .here)
      else
        .var (constE w offq)
        (.var (binE .add w (thereN (Rw w :: Rw w :: List.replicate 11 (Rw (2 * w)))
          (laneVarG (Rw w) n ia)) .here)
        (.var (binE .sub w .here (.there (.there .here)))
          (uTail red w q k m .here)))))))))))))))

theorem uLaneProg_denote (w q R qinv logR offq z k m : ℕ) (red : Bool) (n ia ib : ℕ)
    (up : Bool) (V : Valuation (Ctxs w (n + 1))) :
    (uLaneProg w q R qinv logR offq z k m red (n + 1) ia ib up).denote V
      = redW red w q k m (if up then (show BitVec w from (laneVarG (Rw w) n ia).lookup V)
          + umontW w q R qinv logR z ((laneVarG (Rw w) n ib).lookup V)
        else (show BitVec w from (laneVarG (Rw w) n ia).lookup V) + BitVec.ofNat w offq
          - umontW w q R qinv logR z ((laneVarG (Rw w) n ib).lookup V)) := by
  cases up <;> cases red <;> rfl

/-- The Barrett shift of a schedule: `w + ⌊log₂ q⌋`. -/
def barK : ℕ := S.w + Nat.log2 P.q

/-- The Barrett constant of a schedule: `⌈2 ^ barK / q⌉`. -/
def barM : ℕ := (2 ^ barK P S + P.q - 1) / P.q

theorem barM_mul_ge (hq : 0 < P.q) : 2 ^ barK P S ≤ barM P S * P.q := by
  have h := Nat.div_add_mod (2 ^ barK P S + P.q - 1) P.q
  have hr := Nat.mod_lt (2 ^ barK P S + P.q - 1) hq
  rw [barM, Nat.mul_comm]
  omega

/-- Layer `ℓ` of the lazy schedule on `S.w`-bit word lanes, Barrett-reduced at the
layers `S.red` marks. -/
def semUW (ℓ : ℕ) (g : ℕ → BitVec S.w) (i : ℕ) : BitVec S.w :=
  redW (S.red ℓ) S.w P.q (barK P S) (barM P S)
    (if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ) then
      g i + umontW S.w P.q S.R S.qinv logR
        (zr P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))))
        (g (i + 2 ^ (P.logN - 1 - ℓ)))
    else
      g (i - 2 ^ (P.logN - 1 - ℓ)) + BitVec.ofNat S.w (S.off * P.q)
        - umontW S.w P.q S.R S.qinv logR
          (zr P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)))) (g i))

/-- The lane schedules of lazy layer `ℓ` on `2 ^ logN` lanes of `S.w`-bit words. -/
def uLayerLaneProgW (ℓ i : ℕ) : Com jasminDialect (Ctxs S.w (2 ^ P.logN)) (Rw S.w) :=
  if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ) then
    uLaneProg S.w P.q S.R S.qinv logR (S.off * P.q)
      (zr P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))))
      (barK P S) (barM P S) (S.red ℓ) (2 ^ P.logN) i (i + 2 ^ (P.logN - 1 - ℓ)) true
  else
    uLaneProg S.w P.q S.R S.qinv logR (S.off * P.q)
      (zr P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))))
      (barK P S) (barM P S) (S.red ℓ) (2 ^ P.logN) (i - 2 ^ (P.logN - 1 - ℓ)) i false

theorem uLayerLaneProgW_denote (ℓ : ℕ) (hl : ℓ < P.logN) (g : ℕ → BitVec S.w) (i : ℕ)
    (hi : i < 2 ^ P.logN) :
    (uLayerLaneProgW P S logR ℓ i).denote (lanesVal (Rw S.w) g (2 ^ P.logN) 0)
      = semUW P S logR ℓ g i := by
  have hpart := layer_partner_lt P.logN ℓ i hl hi
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ P.logN = m + 1 := ⟨2 ^ P.logN - 1, by
    have := Nat.two_pow_pos P.logN; omega⟩
  unfold uLayerLaneProgW semUW
  generalize 2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) = k
  revert hpart hi
  rw [hm]
  intro hi hpart
  generalize 2 ^ (P.logN - 1 - ℓ) = len at hpart ⊢
  split
  · next hlt =>
    rw [uLaneProg_denote, if_pos rfl, laneVarG_lookup (Rw S.w) g m i 0 (by omega),
      laneVarG_lookup (Rw S.w) g m (i + len) 0 (by have := hpart hlt; omega)]
    simp only [Nat.zero_add]
  · next hlt =>
    rw [uLaneProg_denote, if_neg (by simp),
      laneVarG_lookup (Rw S.w) g m (i - len) 0 (by omega),
      laneVarG_lookup (Rw S.w) g m i 0 (by omega)]
    simp only [Nat.zero_add]

/-- The Barrett side condition at a bound `V`: `V · m ≤ 2 ^ (2 w)` and
`V · (m · q − 2 ^ k) ≤ 2 ^ k`. -/
def BarOk (V : ℕ) : Prop :=
  V * barM P S ≤ 2 ^ (2 * S.w) ∧ V * (barM P S * P.q - 2 ^ barK P S) ≤ 2 ^ barK P S

instance (V : ℕ) : Decidable (BarOk P S V) := inferInstanceAs (Decidable (_ ∧ _))

/-- The side condition of the lowering at the schedule's word width, decidable on
`ℕ`: the radix is `2 ^ logR` with `logR ≤ 2 w`, and at every reduced layer the
Barrett reduction is exact below the layer's bound plus the offset. -/
def UWordOk : Prop :=
  S.R = 2 ^ logR ∧ logR ≤ 2 * S.w ∧
    ∀ ℓ, ℓ < P.layers → S.red ℓ = true → BarOk P S (bnd P S ℓ + S.off * P.q)

instance : Decidable (UWordOk P S logR) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- On a word below the bound `bnd ℓ + off · q` of the unreduced layer value,
`redW` at layer `ℓ` is the reduction of `lazyLayer`. -/
theorem redW_layer (hS : SchedOk P S) (hW : UWordOk P S logR) (hq : 0 < P.q) (ℓ : ℕ)
    (hl : ℓ < P.layers) (W : BitVec S.w) (v : ℕ) (hWv : W.toNat = v)
    (hv : v < bnd P S ℓ + S.off * P.q) :
    (redW (S.red ℓ) S.w P.q (barK P S) (barM P S) W).toNat
      = (BitVec.ofNat S.w (if S.red ℓ then v % P.q else v)).toNat := by
  have hb := (hS.2.2.2.2.2 ℓ (by omega)).2
  have hqw : P.q ≤ 2 ^ S.w := by
    have : P.q ≤ S.off * P.q := Nat.le_mul_of_pos_left _ (by have := hS.1; omega)
    omega
  cases hr : S.red ℓ
  · simp only [redW, Bool.false_eq_true, if_false, BitVec.toNat_ofNat]
    rw [hWv, Nat.mod_eq_of_lt (a := v) (by omega)]
  · obtain ⟨hVm, he⟩ := hW.2.2 ℓ hl hr
    simp only [redW, if_true, BitVec.toNat_ofNat]
    rw [ubarW_toNat S.w P.q (barK P S) (barM P S) _ W hq hqw (by rw [hWv]; exact hv) hVm
      (barM_mul_ge P S hq) he, hWv,
      Nat.mod_eq_of_lt (a := v % P.q) (by have := Nat.mod_lt v hq; omega)]

/-- On representatives below `bnd ℓ`, one word layer at the schedule's width is
`lazyLayer` read as words. -/
theorem semUW_ofNat (hS : SchedOk P S) (hW : UWordOk P S logR) (hq : 0 < P.q) (ℓ : ℕ)
    (hl : ℓ < P.layers) (f : ℕ → ℕ) (hf : ∀ j, f j < bnd P S ℓ) :
    semUW P S logR ℓ (fun j => BitVec.ofNat S.w (f j))
      = fun i => BitVec.ofNat S.w (lazyLayer P S ℓ f i) := by
  obtain ⟨hR, hlog, _⟩ := hW
  obtain ⟨hoff, hRpos, _, hN, hRw, hb⟩ := hS
  have hbℓ := hb ℓ (by omega)
  have hoffq : 2 * P.q ≤ S.off * P.q := Nat.mul_le_mul_right _ hoff
  have hfw : ∀ j, f j < 2 ^ S.w := fun j => by have := hf j; omega
  funext i
  have hofn : ∀ j, (BitVec.ofNat S.w (f j)).toNat = f j := fun j => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hfw j)]
  apply BitVec.eq_of_toNat_eq
  have hlay := redW_layer P S logR ⟨hoff, hRpos, ‹_›, hN, hRw, hb⟩ ⟨hR, hlog, ‹_›⟩ hq ℓ hl
  simp only [semUW, lazyLayer]
  generalize 2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) = k
  generalize 2 ^ (P.logN - 1 - ℓ) = len
  have ht : ∀ j, tmul P S k (f j) < 2 * P.q := fun j =>
    tmul_lt P S hq hRpos hN k (f j) (by have := hf j; omega)
  have hmont : ∀ j, (umontW S.w P.q S.R S.qinv logR (zr P S k)
      (BitVec.ofNat S.w (f j))).toNat = tmul P S k (f j) := fun j => by
    rw [umontW_toNat _ _ _ _ _ _ _ hR hlog (zr_lt P S hq k)
      (by rw [hofn]; have := hf j; omega) hRw
      (by rw [hofn]; have := ht j; rw [tmul] at this; omega), hofn, tmul]
  split
  · refine hlay _ _ ?_ (by have := hf i; have := ht (i + len); omega)
    rw [BitVec.toNat_add, hofn, hmont, Nat.mod_eq_of_lt (by
      have := hf i; have := ht (i + len); omega)]
  · have hoq : (BitVec.ofNat S.w (S.off * P.q)).toNat = S.off * P.q := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hf 0; omega)]
    have hadd : (BitVec.ofNat S.w (f (i - len)) + BitVec.ofNat S.w (S.off * P.q)).toNat
        = f (i - len) + S.off * P.q := by
      rw [BitVec.toNat_add, hofn, hoq, Nat.mod_eq_of_lt (by have := hf (i - len); omega)]
    refine hlay _ _ ?_ (by have := hf (i - len); have := ht i; omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hadd, hmont]; have := ht i; omega),
      hadd, hmont]

/-- The lazy Montgomery transform program on `2 ^ logN` lanes of `S.w`-bit words,
with products and reductions at `2 S.w` bits. -/
def nttProgUW : MultiReturnCom jasminDialect (Ctxs S.w (2 ^ P.logN)) (Ctxs S.w (2 ^ P.logN)) :=
  chainD (Rw S.w) (2 ^ P.logN) (uLayerLaneProgW P S logR) (List.range P.layers)
    (Ctxt.Hom.id _)

theorem foldl_semUW (hS : SchedOk P S) (hW : UWordOk P S logR) (hq : 0 < P.q) (f : ℕ → ℕ)
    (hf : ∀ j, f j < P.q) :
    ∀ k, k ≤ P.layers → (List.range k).foldl (fun g ℓ => semUW P S logR ℓ g)
        (fun j => BitVec.ofNat S.w (f j)) = fun j => BitVec.ofNat S.w (lazyRun P S k 0 f j)
  | 0, _ => rfl
  | k + 1, hk => by
      rw [List.range_succ, List.foldl_append, foldl_semUW hS hW hq f hf k (by omega),
        List.foldl_cons, List.foldl_nil, lazyRun_succ_last, Nat.zero_add]
      have hb := lazyRun_lt P S hS hq k 0 f (by omega) hf
      rw [Nat.zero_add] at hb
      exact semUW_ofNat P S logR hS hW hq k (by omega) _ hb

/-- **The word lowering at the schedule's width.** For a parameter record satisfying
`NttParams.Ok`, a schedule satisfying `SchedOk` and `UWordOk`, and inputs below
`q`, every output word of `nttProgUW` is below `bnd L`, and cast to `ZMod q` it is
`nttSpec`. -/
theorem nttProgUW_denote (hP : P.Ok) (hS : SchedOk P S) (hW : UWordOk P S logR) (f : ℕ → ℕ)
    (hf : ∀ j, f j < P.q) (i : ℕ) (hi : i < 2 ^ P.logN) :
    (hvGetG (Rw S.w) (0 : BitVec S.w) ((nttProgUW P S logR).denote
        (lanesVal (Rw S.w) (fun j => BitVec.ofNat S.w (f j)) (2 ^ P.logN) 0)) i).toNat
        < bnd P S P.layers ∧
    (((hvGetG (Rw S.w) (0 : BitVec S.w) ((nttProgUW P S logR).denote
        (lanesVal (Rw S.w) (fun j => BitVec.ofNat S.w (f j)) (2 ^ P.logN) 0)) i).toNat : ℕ)
        : ZMod P.q)
      = nttSpec (P.psi : ZMod P.q) P.layers P.logN (fun j => (f j : ZMod P.q)) i := by
  have hq : 0 < P.q := by have := hP.2.2.1; omega
  have hLM := hP.2.1
  rw [nttProgUW, chainD_denote (Rw S.w) (2 ^ P.logN) (0 : BitVec S.w) _ (semUW P S logR)
    (List.range P.layers)
    (fun ℓ hℓ g j hj => uLayerLaneProgW_denote P S logR ℓ
      (by have := List.mem_range.mp hℓ; omega) g j hj)
    (Ctxt.Hom.id _) _ _ (pullV_id _)]
  erw [foldl_semUW P S logR hS hW hq f hf P.layers le_rfl]
  rw [hvGetG_lanesVal _ _ _ _ _ _ hi, Nat.zero_add]
  have hlt := lazyRun_lt P S hS hq P.layers 0 f (by omega) hf i
  rw [Nat.zero_add] at hlt
  have hb := (hS.2.2.2.2.2 P.layers (by omega)).2
  have hval : (BitVec.ofNat S.w (lazyRun P S P.layers 0 f i)).toNat
      = lazyRun P S P.layers 0 f i := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hval]
  refine ⟨hlt, ?_⟩
  rw [lazyRun_cast P S hS hq P.layers 0 f (by omega) hf i]
  exact run_spec _ P.layers P.logN (P.psi_pow hP) hP.1 hLM _ i hi

/-- The ML-KEM schedule at its 16-bit width: radix `2 ^ 16`. -/
theorem mlkemUWord_ok : UWordOk mlkemNtt mlkemLazy 16 := by decide

/-- The ML-DSA schedule at its 32-bit width: radix `2 ^ 32`. -/
theorem mldsaUWord_ok : UWordOk mldsaNtt mldsaLazy 32 := by decide

/-- An ML-KEM schedule on 16-bit words with a Barrett reduction after layer `3`. -/
def mlkemLazyRed3 : LazySched := ⟨2 ^ 16, 3327, 2, fun ℓ => ℓ == 3, 16⟩

theorem mlkemLazyRed3_ok : SchedOk mlkemNtt mlkemLazyRed3 ∧ UWordOk mlkemNtt mlkemLazyRed3 16 := by
  decide

/-! ## 8. The inverse transform on words of the schedule's width -/

/-- The Montgomery multiply of the `w`-bit word variable `v` by the constant `z`, as
the `jasminDialect` schedule of `umontW`. -/
def umontTail (w q R qinv logR z : ℕ) {Γ : Ctxt jasminDialect} (v : Var Γ (Rw w)) :
    Com jasminDialect Γ (Rw w) :=
  .var (castE w (2 * w) v)
  (.var (constE (2 * w) z)
  (.var (binE .mul (2 * w) (.there .here) .here)
  (.var (constE (2 * w) qinv)
  (.var (binE .mul (2 * w) (.there .here) .here)
  (.var (constE (2 * w) (R - 1))
  (.var (binE .and (2 * w) (.there .here) .here)
  (.var (constE (2 * w) q)
  (.var (binE .mul (2 * w) (.there .here) .here)
  (.var (binE .add (2 * w) (.there (.there (.there (.there (.there (.there .here)))))) .here)
  (.var (shrE (2 * w) logR .here)
  (.var (castE (2 * w) w .here) (.ret .here))))))))))))

theorem umontTail_denote (w q R qinv logR z : ℕ) {Γ : Ctxt jasminDialect} (v : Var Γ (Rw w))
    (V : Valuation Γ) :
    (umontTail w q R qinv logR z v).denote V
      = umontW w q R qinv logR z (show BitVec w from v.lookup V) := rfl

/-- One Gentleman–Sande lane on `w`-bit words: the Montgomery product by the
constant `z` of `a[ia] + a[ib]` when `up`, and of `a[ia] + offq − a[ib]`
otherwise. -/
def uGsLaneProg (w q R qinv logR offq z : ℕ) :
    (n : ℕ) → ℕ → ℕ → Bool → Com jasminDialect (Ctxs w n) (Rw w)
  | 0, _, _, _ => .var (constE w 0) (.ret .here)
  | n + 1, ia, ib, up =>
      if up then
        .var (binE .add w (laneVarG (Rw w) n ia) (laneVarG (Rw w) n ib))
          (umontTail w q R qinv logR z .here)
      else
        .var (constE w offq)
        (.var (binE .add w (laneVarG (Rw w) n ia).there .here)
        (.var (binE .sub w .here (thereN [Rw w, Rw w] (laneVarG (Rw w) n ib)))
        (umontTail w q R qinv logR z .here)))

theorem uGsLaneProg_denote (w q R qinv logR offq z n ia ib : ℕ) (up : Bool)
    (V : Valuation (Ctxs w (n + 1))) :
    (uGsLaneProg w q R qinv logR offq z (n + 1) ia ib up).denote V
      = umontW w q R qinv logR z
          (if up then (show BitVec w from (laneVarG (Rw w) n ia).lookup V)
            + (laneVarG (Rw w) n ib).lookup V
          else (show BitVec w from (laneVarG (Rw w) n ia).lookup V) + BitVec.ofNat w offq
            - (laneVarG (Rw w) n ib).lookup V) := by
  cases up <;> rfl

/-- One scaling lane on `w`-bit words: the Montgomery product of `a[i]` by the
constant `z`. -/
def uScaleLaneProg (w q R qinv logR z : ℕ) :
    (n : ℕ) → ℕ → Com jasminDialect (Ctxs w n) (Rw w)
  | 0, _ => .var (constE w 0) (.ret .here)
  | n + 1, i => umontTail w q R qinv logR z (laneVarG (Rw w) n i)

/-- Stage `st` of the inverse transform on `S.w`-bit word lanes: the scaling by `s`
for `none`; for `some ℓ`, inverse layer `ℓ`, whose lower lane is the Montgomery
product of `u + v` by `1` and whose upper lane is the Montgomery product of
`u + 2 q − v` by the inverse twiddle. -/
def invSemUW (s : ℕ) : Option ℕ → (ℕ → BitVec S.w) → ℕ → BitVec S.w
  | none, g, i => umontW S.w P.q S.R S.qinv logR (zrc P S s) (g i)
  | some ℓ, g, i =>
      if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ) then
        umontW S.w P.q S.R S.qinv logR (zrc P S 1) (g i + g (i + 2 ^ (P.logN - 1 - ℓ)))
      else
        umontW S.w P.q S.R S.qinv logR
          (zrInv P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))))
          (g (i - 2 ^ (P.logN - 1 - ℓ)) + BitVec.ofNat S.w (2 * P.q) - g i)

/-- The lane schedules of inverse stage `st` on `2 ^ logN` lanes of `S.w`-bit
words. -/
def invLaneProgUW (s : ℕ) : Option ℕ → ℕ → Com jasminDialect (Ctxs S.w (2 ^ P.logN)) (Rw S.w)
  | none, i => uScaleLaneProg S.w P.q S.R S.qinv logR (zrc P S s) (2 ^ P.logN) i
  | some ℓ, i =>
      if i % (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) < 2 ^ (P.logN - 1 - ℓ) then
        uGsLaneProg S.w P.q S.R S.qinv logR (2 * P.q) (zrc P S 1) (2 ^ P.logN)
          i (i + 2 ^ (P.logN - 1 - ℓ)) true
      else
        uGsLaneProg S.w P.q S.R S.qinv logR (2 * P.q)
          (zrInv P S (2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ))))
          (2 ^ P.logN) (i - 2 ^ (P.logN - 1 - ℓ)) i false

theorem invLaneProgUW_denote (s : ℕ) (st : Option ℕ) (hst : ∀ ℓ, st = some ℓ → ℓ < P.logN)
    (g : ℕ → BitVec S.w) (i : ℕ) (hi : i < 2 ^ P.logN) :
    (invLaneProgUW P S logR s st i).denote (lanesVal (Rw S.w) g (2 ^ P.logN) 0)
      = invSemUW P S logR s st g i := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ P.logN = m + 1 := ⟨2 ^ P.logN - 1, by
    have := Nat.two_pow_pos P.logN; omega⟩
  cases st with
  | none =>
    simp only [invLaneProgUW, invSemUW]
    revert hi
    rw [hm]
    intro hi
    rw [uScaleLaneProg.eq_2, umontTail_denote, laneVarG_lookup (Rw S.w) g m i 0 (by omega),
      Nat.zero_add]
  | some ℓ =>
    have hpart := layer_partner_lt P.logN ℓ i (hst ℓ rfl) hi
    simp only [invLaneProgUW, invSemUW]
    generalize 2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) = k
    revert hpart hi
    rw [hm]
    intro hi hpart
    generalize 2 ^ (P.logN - 1 - ℓ) = len at hpart ⊢
    split
    · next hlt =>
      rw [uGsLaneProg_denote, if_pos rfl, laneVarG_lookup (Rw S.w) g m i 0 (by omega),
        laneVarG_lookup (Rw S.w) g m (i + len) 0 (by have := hpart hlt; omega)]
      simp only [Nat.zero_add]
    · next hlt =>
      rw [uGsLaneProg_denote, if_neg (by simp),
        laneVarG_lookup (Rw S.w) g m (i - len) 0 (by omega),
        laneVarG_lookup (Rw S.w) g m i 0 (by omega)]
      simp only [Nat.zero_add]

/-- The inverse transform program of scaling constant `s` on `2 ^ logN` lanes of
`S.w`-bit words, with products and reductions at `2 S.w` bits. -/
def inttProgUW (s : ℕ) :
    MultiReturnCom jasminDialect (Ctxs S.w (2 ^ P.logN)) (Ctxs S.w (2 ^ P.logN)) :=
  chainD (Rw S.w) (2 ^ P.logN) (invLaneProgUW P S logR s) (invStagesW P.layers)
    (Ctxt.Hom.id _)

/-- The side condition of the inverse lowering at the schedule's width, decidable on
`ℕ`: a sum of two lanes below `2 q` is at most `R` and fits a word. -/
def UInvWordOk : Prop := 4 * P.q ≤ S.R ∧ 4 * P.q ≤ 2 ^ S.w

instance : Decidable (UInvWordOk P S) := inferInstanceAs (Decidable (_ ∧ _))

/-- The Montgomery word multiply at the schedule's width by a constant `c` in
Montgomery form, on an operand at most `R`, is below `2 q` and congruent to `c`
times the operand. -/
theorem umontW_zrc (hS : SchedOk P S) (hW : UWordOk P S logR) (hq : 0 < P.q) (c : ℕ)
    (y : BitVec S.w) (hy : y.toNat ≤ S.R) :
    (umontW S.w P.q S.R S.qinv logR (zrc P S c) y).toNat < 2 * P.q ∧
    (((umontW S.w P.q S.R S.qinv logR (zrc P S c) y).toNat : ℕ) : ZMod P.q)
      = (c : ZMod P.q) * (y.toNat : ZMod P.q) := by
  obtain ⟨hR, hlog, _⟩ := hW
  obtain ⟨hoff, hRpos, hcop, hN, hRw, hb⟩ := hS
  have hb0 := (hb 0 (by omega)).2
  have hoffq : 2 * P.q ≤ S.off * P.q := Nat.mul_le_mul_right _ hoff
  have hzq : zrc P S c < P.q := Nat.mod_lt _ hq
  have hT : zrc P S c * y.toNat < S.R * P.q := by
    have h1 : zrc P S c * y.toNat ≤ zrc P S c * S.R := Nat.mul_le_mul_left _ hy
    have h2 : zrc P S c * S.R < P.q * S.R := Nat.mul_lt_mul_of_pos_right hzq hRpos
    rw [Nat.mul_comm S.R]
    omega
  obtain ⟨hlt, hmod⟩ := montgomeryReduce_correct P.q S.R S.qinv _ hq hRpos hN hT
  have hbnd0 : bnd P S 0 = P.q := rfl
  rw [umontW_toNat _ _ _ _ _ _ _ hR hlog hzq hy hRw (by omega)]
  refine ⟨hlt, ?_⟩
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  rw [Nat.cast_mul, Nat.cast_mul, zrc, ZMod.natCast_mod, Nat.cast_mul] at hcast
  have hu : IsUnit ((S.R : ℕ) : ZMod P.q) := ⟨ZMod.unitOfCoprime S.R hcop, rfl⟩
  apply hu.mul_left_inj.mp
  rw [zrc, hcast]
  ring

/-- On lanes below `2 q`, one inverse word layer at the schedule's width stays below
`2 q` and casts to `invLayerFn`. -/
theorem invSemUW_layer (hS : SchedOk P S) (hW : UWordOk P S logR) (hI : UInvWordOk P S)
    (hq : 0 < P.q) (s ℓ : ℕ) (g : ℕ → BitVec S.w) (hg : ∀ j, (g j).toNat < 2 * P.q) (i : ℕ) :
    (invSemUW P S logR s (some ℓ) g i).toNat < 2 * P.q ∧
    (((invSemUW P S logR s (some ℓ) g i).toNat : ℕ) : ZMod P.q)
      = invLayerFn (P.psi : ZMod P.q) P.layers P.logN ℓ (fun j => ((g j).toNat : ZMod P.q)) i := by
  obtain ⟨hIR, hIw⟩ := hI
  simp only [invSemUW, invLayerFn, zrInv]
  generalize 2 ^ ℓ + i / (2 ^ (P.logN - 1 - ℓ) + 2 ^ (P.logN - 1 - ℓ)) = k
  generalize 2 ^ (P.logN - 1 - ℓ) = len
  split
  · have hsum : (g i + g (i + len)).toNat = (g i).toNat + (g (i + len)).toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := hg i; have := hg (i + len); omega)]
    obtain ⟨h1, h2⟩ := umontW_zrc P S logR hS hW hq 1 _
      (by rw [hsum]; have := hg i; have := hg (i + len); omega)
    refine ⟨h1, ?_⟩
    rw [h2, hsum]
    push_cast
    ring
  · have hoq : (BitVec.ofNat S.w (2 * P.q)).toNat = 2 * P.q := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hadd : (g (i - len) + BitVec.ofNat S.w (2 * P.q)).toNat
        = (g (i - len)).toNat + 2 * P.q := by
      rw [BitVec.toNat_add, hoq, Nat.mod_eq_of_lt (by have := hg (i - len); omega)]
    have hsub : (g (i - len) + BitVec.ofNat S.w (2 * P.q) - g i).toNat
        = (g (i - len)).toNat + 2 * P.q - (g i).toNat := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hadd]; have := hg i; omega), hadd]
    obtain ⟨h1, h2⟩ := umontW_zrc P S logR hS hW hq
      (P.psi ^ (2 ^ (P.layers + 1) - bitrev P.layers k)) _
      (by rw [hsub]; have := hg i; have := hg (i - len); omega)
    refine ⟨h1, ?_⟩
    rw [h2, hsub, Nat.cast_sub (by have := hg i; omega), Nat.cast_add, Nat.cast_mul,
      ZMod.natCast_self, Nat.cast_pow, ztInv]
    ring

theorem foldl_invSemUW_layers (hS : SchedOk P S) (hW : UWordOk P S logR)
    (hI : UInvWordOk P S) (hq : 0 < P.q) (s : ℕ) :
    ∀ (k : ℕ) (g : ℕ → BitVec S.w), (∀ j, (g j).toNat < 2 * P.q) →
      (∀ j, ((((List.range k).reverse.map some).foldl
          (fun g st => invSemUW P S logR s st g) g) j).toNat < 2 * P.q) ∧
      (fun j => (((((List.range k).reverse.map some).foldl
          (fun g st => invSemUW P S logR s st g) g) j).toNat : ZMod P.q))
        = invRun (P.psi : ZMod P.q) P.layers P.logN k (fun j => ((g j).toNat : ZMod P.q))
  | 0, _, hg => ⟨hg, rfl⟩
  | k + 1, g, hg => by
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons, List.foldl_cons]
      have hl := fun j => invSemUW_layer P S logR hS hW hI hq s k g hg j
      obtain ⟨h1, h2⟩ := foldl_invSemUW_layers hS hW hI hq s k _ (fun j => (hl j).1)
      refine ⟨h1, ?_⟩
      rw [h2, invRun]
      congr 1
      funext j
      exact (hl j).2

/-- **The inverse word lowering at the schedule's width, on words.** For a parameter
record satisfying `NttParams.Ok`, a schedule satisfying `SchedOk`, `UWordOk` and
`UInvWordOk`, and input words at most `R`, every output word of `inttProgUW` is
below `2 q`, and cast to `ZMod q` it is `inttSpec` of the input words. -/
theorem inttProgUW_denote_words (hP : P.Ok) (hS : SchedOk P S) (hW : UWordOk P S logR)
    (hI : UInvWordOk P S) (s : ℕ) (g : ℕ → BitVec S.w) (hg : ∀ j, (g j).toNat ≤ S.R) (i : ℕ)
    (hi : i < 2 ^ P.logN) :
    (hvGetG (Rw S.w) (0 : BitVec S.w) ((inttProgUW P S logR s).denote
        (lanesVal (Rw S.w) g (2 ^ P.logN) 0)) i).toNat < 2 * P.q ∧
    (((hvGetG (Rw S.w) (0 : BitVec S.w) ((inttProgUW P S logR s).denote
        (lanesVal (Rw S.w) g (2 ^ P.logN) 0)) i).toNat : ℕ) : ZMod P.q)
      = inttSpec (P.psi : ZMod P.q) P.layers P.logN (s : ZMod P.q)
          (fun j => ((g j).toNat : ZMod P.q)) i := by
  have hq : 0 < P.q := by have := hP.2.2.1; omega
  rw [inttProgUW, chainD_denote (Rw S.w) (2 ^ P.logN) (0 : BitVec S.w) _ (invSemUW P S logR s)
    (invStagesW P.layers)
    (fun st hst h j hj => invLaneProgUW_denote P S logR s st (fun ℓ hℓ => by
        subst hℓ
        simp only [invStagesW, List.mem_cons, List.mem_map, List.mem_reverse,
          List.mem_range] at hst
        rcases hst with h0 | ⟨ℓ', h1, h2⟩
        · cases h0
        · cases h2; have := hP.2.1; omega) h j hj)
    (Ctxt.Hom.id _) _ _ (pullV_id _)]
  rw [hvGetG_lanesVal _ _ _ _ _ _ hi, Nat.zero_add, invStagesW, List.foldl_cons]
  have hsc := fun j => umontW_zrc P S logR hS hW hq s (g j) (hg j)
  obtain ⟨h1, h2⟩ := foldl_invSemUW_layers P S logR hS hW hI hq s P.layers
    (invSemUW P S logR s none g) (fun j => (hsc j).1)
  refine ⟨h1 i, (congrFun h2 i).trans ?_⟩
  rw [inttSpec,
    show (fun j => (((invSemUW P S logR s none g j).toNat : ℕ) : ZMod P.q))
      = fun j => (s : ZMod P.q) * ((g j).toNat : ZMod P.q) from funext fun j => (hsc j).2,
    invRun_smul]

/-- **The inverse word lowering at the schedule's width.** For a parameter record
satisfying `NttParams.Ok`, a schedule satisfying `SchedOk`, `UWordOk` and
`UInvWordOk`, and inputs at most `R` and below `2 ^ w`, every output word of
`inttProgUW` is below `2 q`, and cast to `ZMod q` it is `inttSpec`. -/
theorem inttProgUW_denote (hP : P.Ok) (hS : SchedOk P S) (hW : UWordOk P S logR)
    (hI : UInvWordOk P S) (s : ℕ) (f : ℕ → ℕ) (hf : ∀ j, f j ≤ S.R)
    (hfw : ∀ j, f j < 2 ^ S.w) (i : ℕ) (hi : i < 2 ^ P.logN) :
    (hvGetG (Rw S.w) (0 : BitVec S.w) ((inttProgUW P S logR s).denote
        (lanesVal (Rw S.w) (fun j => BitVec.ofNat S.w (f j)) (2 ^ P.logN) 0)) i).toNat
        < 2 * P.q ∧
    (((hvGetG (Rw S.w) (0 : BitVec S.w) ((inttProgUW P S logR s).denote
        (lanesVal (Rw S.w) (fun j => BitVec.ofNat S.w (f j)) (2 ^ P.logN) 0)) i).toNat : ℕ)
        : ZMod P.q)
      = inttSpec (P.psi : ZMod P.q) P.layers P.logN (s : ZMod P.q)
          (fun j => (f j : ZMod P.q)) i := by
  have hofn : ∀ j, (BitVec.ofNat S.w (f j)).toNat = f j := fun j => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hfw j)]
  have := inttProgUW_denote_words P S logR hP hS hW hI s _
    (fun j => by rw [hofn]; exact hf j) i hi
  simpa only [hofn] using this

/-- **The word round trip at the schedule's width.** For a scaling constant with
`ScaleOk` and inputs below `q`, lane `i` of `inttProgUW` applied to the output words
of `nttProgUW` is below `2 q` and casts to input `i` in `ZMod q`. -/
theorem inttProgUW_nttProgUW (hP : P.Ok) (hS : SchedOk P S) (hW : UWordOk P S logR)
    (hI : UInvWordOk P S) (s : ℕ) (hs : ScaleOk P s) (f : ℕ → ℕ) (hf : ∀ j, f j < P.q)
    (i : ℕ) (hi : i < 2 ^ P.logN) :
    (hvGetG (Rw S.w) (0 : BitVec S.w) ((inttProgUW P S logR s).denote
        ((nttProgUW P S logR).denote
        (lanesVal (Rw S.w) (fun j => BitVec.ofNat S.w (f j)) (2 ^ P.logN) 0))) i).toNat
        < 2 * P.q ∧
    (((hvGetG (Rw S.w) (0 : BitVec S.w) ((inttProgUW P S logR s).denote
        ((nttProgUW P S logR).denote
        (lanesVal (Rw S.w) (fun j => BitVec.ofNat S.w (f j)) (2 ^ P.logN) 0))) i).toNat : ℕ)
        : ZMod P.q) = (f i : ZMod P.q) := by
  have heq : (nttProgUW P S logR).denote
        (lanesVal (Rw S.w) (fun j => BitVec.ofNat S.w (f j)) (2 ^ P.logN) 0)
      = lanesVal (Rw S.w) (fun j => hvGetG (Rw S.w) (0 : BitVec S.w)
          ((nttProgUW P S logR).denote
          (lanesVal (Rw S.w) (fun j => BitVec.ofNat S.w (f j)) (2 ^ P.logN) 0)) j)
          (2 ^ P.logN) 0 :=
    eq_lanesVal (Rw S.w) (0 : BitVec S.w) _ (2 ^ P.logN) 0 _ (fun j _ => by rw [Nat.zero_add])
  have hb : ∀ j, (hvGetG (Rw S.w) (0 : BitVec S.w) ((nttProgUW P S logR).denote
      (lanesVal (Rw S.w) (fun j => BitVec.ofNat S.w (f j)) (2 ^ P.logN) 0)) j).toNat
        ≤ S.R := by
    intro j
    by_cases hj : j < 2 ^ P.logN
    · have := (nttProgUW_denote P S logR hP hS hW f hf j hj).1
      have := bnd_le_R P S hS P.layers le_rfl
      omega
    · rw [hvGetG_of_le (Rw S.w) _ _ j (by omega)]
      simp
  rw [heq]
  obtain ⟨h1, h2⟩ := inttProgUW_denote_words P S logR hP hS hW hI s _ hb i hi
  refine ⟨h1, ?_⟩
  rw [h2, inttSpec, invRun_congr _ P.layers P.logN P.layers hP.2.1 _
    (nttSpec (P.psi : ZMod P.q) P.layers P.logN (fun j => (f j : ZMod P.q)))
    (fun j hj => (nttProgUW_denote P S logR hP hS hW f hf j hj).2) i hi]
  exact inttSpec_nttSpec _ P.layers P.logN (P.psi_pow hP) hP.1 hP.2.1 _ (hs.cast P s) _ i hi

/-- The ML-KEM inverse schedule at its 16-bit width: `4 q ≤ 2 ^ 16`. -/
theorem mlkemUInvWord_ok : UInvWordOk mlkemNtt mlkemLazy := by decide

/-- The ML-DSA inverse schedule at its 32-bit width: `4 q ≤ 2 ^ 32`. -/
theorem mldsaUInvWord_ok : UInvWordOk mldsaNtt mldsaLazy := by decide

end CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
