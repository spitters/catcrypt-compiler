/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate

/-!
# The inverse negacyclic NTT as one `fieldDialect` template

The inverse transforms of FIPS 203 (Algorithm 10) and FIPS 204 (Algorithm 42)
run the layers of `VIR/NegacyclicNttTemplate.lean` backwards with the
Gentleman–Sande butterfly `(u, v) ↦ (u + v, z⁻¹ · (u − v))` and multiply every
lane by `s = (2 ^ L)⁻¹`.  Here `z⁻¹` is the inverse twiddle
`ψ ^ (2 ^ (L + 1) − BitRev_L k)`, the inverse of `ψ ^ BitRev_L k` whenever
`ψ ^ (2 ^ L) = -1`.

Each Gentleman–Sande layer undoes the Cooley–Tukey layer of the same index up to
a factor `2`, in both orders, on every lane function; so `L` inverse layers
undo `L` forward layers up to `2 ^ L`, and the scaled inverse inverts `nttSpec`
on the first `2 ^ M` lanes in both directions.

## Main definitions

* `ztInv` — the inverse twiddle of a block index.
* `invLayerFn`, `invRun` — one inverse layer on lane functions, and the inverse
  layers `k - 1, …, 0`.
* `inttSpec` — the scaled inverse transform `s · invRun L`.
* `chainG` — a sequence of stages, each emitted by `Com.foldVarN` over the
  result variables of the previous one, for an arbitrary family of lane
  schedules.
* `gsLaneProg`, `scaleLaneProg`, `invStageProg`, `invStages` — the lane schedules
  of an inverse layer and of the scaling, and the stage list.
* `inttProg` — the inverse transform program.

## Main results

* `invLayerFn_layerFn`, `layerFn_invLayerFn` — an inverse layer and the forward
  layer of the same index compose to multiplication by `2`, in both orders.
* `invRun_run`, `run_invRun` — `k` inverse layers and `k` forward layers compose
  to multiplication by `2 ^ k`.
* `inttSpec_nttSpec`, `nttSpec_inttSpec` — for `s · 2 ^ L = 1`, the scaled
  inverse inverts `nttSpec` on the first `2 ^ M` lanes, in both orders.
* `chainG_denote` — `chainG` denotes the left fold of the stage semantics.
* `inttProg_denote` — lane `i` of `inttProg` is `inttSpec` at `i`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV pullV_id)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
  (hvToHom homToHV pullV_hvToHom lookupVars_homToHV)
open CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldMultiReturn (F constE addE subE mulE)
open CatCrypt.Crypto.SecureCompilation.VIR.NttStageFieldGeneral
open CatCrypt.Crypto.Lattice.BitReversalGeneric
  (bitrev toBits fromBits fromBits_lt toBits_length)

/-! ## 1. The inverse twiddle -/

theorem bitrev_lt_pow (L k : ℕ) : bitrev L k < 2 ^ L := by
  have := fromBits_lt (toBits L k).reverse
  simpa [bitrev, toBits_length] using this

section Algebra

variable {R : Type*} [CommRing R]

/-- The inverse twiddle of block index `k`: `ψ ^ (2 ^ (L + 1) - BitRev_L k)`. -/
def ztInv (ψ : R) (L k : ℕ) : R := ψ ^ (2 ^ (L + 1) - bitrev L k)

theorem zt_mul_ztInv (ψ : R) (L : ℕ) (hψ : ψ ^ (2 ^ L) = -1) (k : ℕ) :
    zt ψ L k * ztInv ψ L k = 1 := by
  have hlt := bitrev_lt_pow L k
  rw [zt, ztInv, ← pow_add,
    show bitrev L k + (2 ^ (L + 1) - bitrev L k) = 2 ^ L * 2 from by rw [pow_succ]; omega,
    pow_mul, hψ, neg_one_sq]

/-! ## 2. Lanes of a block -/

/-- The partner of a lower lane is the upper lane of the same block. -/
theorem partner_up (len i : ℕ) (h : i % (len + len) < len) :
    (i + len) % (len + len) = i % (len + len) + len ∧
      (i + len) / (len + len) = i / (len + len) := by
  have hpos : 0 < len + len := by omega
  have hdm := Nat.div_add_mod i (len + len)
  have hr := Nat.mod_lt i hpos
  generalize i / (len + len) = a at hdm ⊢
  generalize i % (len + len) = r at hdm h hr ⊢
  have he : i + len = (r + len) + (len + len) * a := by omega
  rw [he, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hpos,
    Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
  omega

/-- The partner of an upper lane is the lower lane of the same block. -/
theorem partner_down (len i : ℕ) (h : ¬ i % (len + len) < len) :
    len ≤ i ∧ (i - len) % (len + len) = i % (len + len) - len ∧
      (i - len) / (len + len) = i / (len + len) := by
  rcases Nat.eq_zero_or_pos len with h0 | h0
  · subst h0; simp
  have hpos : 0 < len + len := by omega
  have hdm := Nat.div_add_mod i (len + len)
  have hr := Nat.mod_lt i hpos
  generalize i / (len + len) = a at hdm ⊢
  generalize i % (len + len) = r at hdm h hr ⊢
  have he : i - len = (r - len) + (len + len) * a := by omega
  refine ⟨by omega, ?_⟩
  rw [he, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hpos,
    Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
  omega

/-! ## 3. The inverse layers on lane functions -/

/-- Inverse layer `ℓ`: the lower lane of each butterfly becomes `u + v` and the
upper `ztInv ψ L k · (u − v)`, with `k = 2 ^ ℓ + c` for block `c`. -/
def invLayerFn (ψ : R) (L M ℓ : ℕ) (f : ℕ → R) (i : ℕ) : R :=
  if i % (2 ^ (M - 1 - ℓ) + 2 ^ (M - 1 - ℓ)) < 2 ^ (M - 1 - ℓ) then
    f i + f (i + 2 ^ (M - 1 - ℓ))
  else
    ztInv ψ L (2 ^ ℓ + i / (2 ^ (M - 1 - ℓ) + 2 ^ (M - 1 - ℓ)))
      * (f (i - 2 ^ (M - 1 - ℓ)) - f i)

/-- The inverse layers `k - 1, …, 0`, applied in that order. -/
def invRun (ψ : R) (L M : ℕ) : (k : ℕ) → (ℕ → R) → ℕ → R
  | 0, f => f
  | k + 1, f => invRun ψ L M k (invLayerFn ψ L M k f)

/-- An inverse layer after the forward layer of the same index multiplies every
lane by `2`. -/
theorem invLayerFn_layerFn (ψ : R) (L M : ℕ) (hψ : ψ ^ (2 ^ L) = -1) (ℓ : ℕ)
    (a : ℕ → R) : invLayerFn ψ L M ℓ (layerFn ψ L M ℓ a) = fun i => 2 * a i := by
  funext i
  simp only [invLayerFn, layerFn]
  have hpos : 0 < 2 ^ (M - 1 - ℓ) := Nat.two_pow_pos _
  generalize 2 ^ (M - 1 - ℓ) = len at hpos ⊢
  have hr := Nat.mod_lt i (show 0 < len + len by omega)
  by_cases h : i % (len + len) < len
  · obtain ⟨hm, hd⟩ := partner_up len i h
    have hn : ¬ (i + len) % (len + len) < len := by omega
    simp only [ite_eq_left h, ite_eq_right hn, hd, Nat.add_sub_cancel]
    ring
  · obtain ⟨hle, hm, hd⟩ := partner_down len i h
    have hn : (i - len) % (len + len) < len := by omega
    simp only [ite_eq_right h, ite_eq_left hn, hd, Nat.sub_add_cancel hle]
    linear_combination (2 * a i) * zt_mul_ztInv ψ L hψ (2 ^ ℓ + i / (len + len))

/-- A forward layer after the inverse layer of the same index multiplies every
lane by `2`. -/
theorem layerFn_invLayerFn (ψ : R) (L M : ℕ) (hψ : ψ ^ (2 ^ L) = -1) (ℓ : ℕ)
    (a : ℕ → R) : layerFn ψ L M ℓ (invLayerFn ψ L M ℓ a) = fun i => 2 * a i := by
  funext i
  simp only [invLayerFn, layerFn]
  have hpos : 0 < 2 ^ (M - 1 - ℓ) := Nat.two_pow_pos _
  generalize 2 ^ (M - 1 - ℓ) = len at hpos ⊢
  have hr := Nat.mod_lt i (show 0 < len + len by omega)
  by_cases h : i % (len + len) < len
  · obtain ⟨hm, hd⟩ := partner_up len i h
    have hn : ¬ (i + len) % (len + len) < len := by omega
    simp only [ite_eq_left h, ite_eq_right hn, hd, Nat.add_sub_cancel]
    linear_combination (a i - a (i + len)) * zt_mul_ztInv ψ L hψ (2 ^ ℓ + i / (len + len))
  · obtain ⟨hle, hm, hd⟩ := partner_down len i h
    have hn : (i - len) % (len + len) < len := by omega
    simp only [ite_eq_right h, ite_eq_left hn, hd, Nat.sub_add_cancel hle]
    linear_combination (-(a (i - len) - a i)) * zt_mul_ztInv ψ L hψ (2 ^ ℓ + i / (len + len))

theorem layerFn_smul (ψ : R) (L M ℓ : ℕ) (c : R) (f : ℕ → R) :
    layerFn ψ L M ℓ (fun j => c * f j) = fun i => c * layerFn ψ L M ℓ f i := by
  funext i
  simp only [layerFn]
  split <;> ring

theorem invLayerFn_smul (ψ : R) (L M ℓ : ℕ) (c : R) (f : ℕ → R) :
    invLayerFn ψ L M ℓ (fun j => c * f j) = fun i => c * invLayerFn ψ L M ℓ f i := by
  funext i
  simp only [invLayerFn]
  split <;> ring

theorem run_smul (ψ : R) (L M : ℕ) (c : R) :
    ∀ (k ℓ : ℕ) (f : ℕ → R), run ψ L M k ℓ (fun j => c * f j) = fun i => c * run ψ L M k ℓ f i
  | 0, _, _ => rfl
  | k + 1, ℓ, f => by
      rw [run, layerFn_smul, run_smul ψ L M c k (ℓ + 1)]
      rfl

theorem invRun_smul (ψ : R) (L M : ℕ) (c : R) :
    ∀ (k : ℕ) (f : ℕ → R), invRun ψ L M k (fun j => c * f j) = fun i => c * invRun ψ L M k f i
  | 0, _ => rfl
  | k + 1, f => by
      rw [invRun, invLayerFn_smul, invRun_smul ψ L M c k]
      rfl

/-- The last of `k + 1` forward layers is layer `ℓ + k`. -/
theorem run_succ_last (ψ : R) (L M : ℕ) :
    ∀ (k ℓ : ℕ) (f : ℕ → R), run ψ L M (k + 1) ℓ f = layerFn ψ L M (ℓ + k) (run ψ L M k ℓ f)
  | 0, _, _ => rfl
  | k + 1, ℓ, f => by
      rw [run, run_succ_last ψ L M k (ℓ + 1), show ℓ + 1 + k = ℓ + (k + 1) from by omega]
      rfl

/-- `k` inverse layers after the first `k` forward layers multiply by `2 ^ k`. -/
theorem invRun_run (ψ : R) (L M : ℕ) (hψ : ψ ^ (2 ^ L) = -1) (a : ℕ → R) :
    ∀ k : ℕ, invRun ψ L M k (run ψ L M k 0 a) = fun i => 2 ^ k * a i
  | 0 => by funext i; simp [invRun, run]
  | k + 1 => by
      rw [run_succ_last, Nat.zero_add, invRun, invLayerFn_layerFn ψ L M hψ, invRun_smul,
        invRun_run ψ L M hψ a k]
      funext i
      ring

/-- The first `k` forward layers after `k` inverse layers multiply by `2 ^ k`. -/
theorem run_invRun (ψ : R) (L M : ℕ) (hψ : ψ ^ (2 ^ L) = -1) :
    ∀ (k : ℕ) (v : ℕ → R), run ψ L M k 0 (invRun ψ L M k v) = fun i => 2 ^ k * v i
  | 0, v => by funext i; simp [invRun, run]
  | k + 1, v => by
      rw [run_succ_last, Nat.zero_add, invRun, run_invRun ψ L M hψ k, layerFn_smul,
        layerFn_invLayerFn ψ L M hψ]
      funext i
      ring

/-- An inverse layer below `M` reads lanes below `2 ^ M` only. -/
theorem invLayerFn_congr (ψ : R) (L M ℓ : ℕ) (hl : ℓ < M) (f g : ℕ → R)
    (h : ∀ j, j < 2 ^ M → f j = g j) (i : ℕ) (hi : i < 2 ^ M) :
    invLayerFn ψ L M ℓ f i = invLayerFn ψ L M ℓ g i := by
  have hpart := layer_partner_lt M ℓ i hl hi
  simp only [invLayerFn]
  split
  · next hlt => rw [h i hi, h _ (hpart hlt)]
  · rw [h i hi, h _ (lt_of_le_of_lt (Nat.sub_le _ _) hi)]

theorem invRun_congr (ψ : R) (L M : ℕ) :
    ∀ (k : ℕ), k ≤ M → ∀ (f g : ℕ → R), (∀ j, j < 2 ^ M → f j = g j) →
      ∀ i, i < 2 ^ M → invRun ψ L M k f i = invRun ψ L M k g i
  | 0, _, _, _, h, i, hi => h i hi
  | k + 1, hk, f, g, h, i, hi =>
      invRun_congr ψ L M k (by omega) _ _
        (fun j hj => invLayerFn_congr ψ L M k (by omega) f g h j hj) i hi

/-- `nttSpec` reads lanes below `2 ^ M` only. -/
theorem nttSpec_congr (ψ : R) (L M : ℕ) (hLM : L ≤ M) (f g : ℕ → R)
    (h : ∀ j, j < 2 ^ M → f j = g j) (i : ℕ) :
    nttSpec ψ L M f i = nttSpec ψ L M g i := by
  have hB : (2 : ℕ) ^ M = 2 ^ L * 2 ^ (M - L) := by rw [← pow_add]; congr 1; omega
  have hpos : 0 < (2 : ℕ) ^ (M - L) := Nat.two_pow_pos _
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' : s + 1 ≤ 2 ^ L := Finset.mem_range.mp hs
  have hmul : (s + 1) * 2 ^ (M - L) ≤ 2 ^ L * 2 ^ (M - L) := Nat.mul_le_mul_right _ hs'
  have hr := Nat.mod_lt i hpos
  rw [h _ (by rw [Nat.add_mul, one_mul] at hmul; omega)]

/-- The scaled inverse transform: `s` times `L` inverse layers. -/
def inttSpec (ψ : R) (L M : ℕ) (s : R) (v : ℕ → R) (i : ℕ) : R :=
  s * invRun ψ L M L v i

/-- **The inverse inverts the transform.** For `s · 2 ^ L = 1`, the scaled inverse
of `nttSpec` returns the input on the first `2 ^ M` lanes. -/
theorem inttSpec_nttSpec (ψ : R) (L M : ℕ) (hψ : ψ ^ (2 ^ L) = -1) (hL : 0 < L)
    (hLM : L ≤ M) (s : R) (hs : s * 2 ^ L = 1) (w : ℕ → R) (i : ℕ) (hi : i < 2 ^ M) :
    inttSpec ψ L M s (nttSpec ψ L M w) i = w i := by
  rw [inttSpec, invRun_congr ψ L M L hLM _ (run ψ L M L 0 w)
    (fun j hj => (run_spec ψ L M hψ hL hLM w j hj).symm) i hi, invRun_run ψ L M hψ w L,
    ← mul_assoc, hs, one_mul]

/-- **The transform inverts the inverse.** For `s · 2 ^ L = 1`, `nttSpec` of the
scaled inverse returns the input on the first `2 ^ M` lanes. -/
theorem nttSpec_inttSpec (ψ : R) (L M : ℕ) (hψ : ψ ^ (2 ^ L) = -1) (hL : 0 < L)
    (hLM : L ≤ M) (s : R) (hs : s * 2 ^ L = 1) (v : ℕ → R) (i : ℕ) (hi : i < 2 ^ M) :
    nttSpec ψ L M (inttSpec ψ L M s v) i = v i := by
  rw [← run_spec ψ L M hψ hL hLM _ i hi]
  show run ψ L M L 0 (fun j => s * invRun ψ L M L v j) i = v i
  rw [run_smul, run_invRun ψ L M hψ L v]
  show s * (2 ^ L * v i) = v i
  rw [← mul_assoc, hs, one_mul]

end Algebra

/-! ## 4. A sequence of stages over a lane-schedule family -/

/-- The stages `sts`, in order, each the `n` lane schedules `fam st` emitted over
the result variables of the previous stage; with no stage, the lanes `h` names. -/
def chainG {ι : Type} (q n : ℕ) (fam : ι → ℕ → Com fieldDialect (Ctxn q n) (F q)) :
    List ι → {Γ : Ctxt fieldDialect} → Ctxt.Hom (Ctxn q n) Γ →
      MultiReturnCom fieldDialect Γ (List.replicate n (F q))
  | [], _, h => .ret (homToHV _ h)
  | st :: sts, _, h =>
      Com.foldVarN n (fam st) h (fun {_} _ vs => chainG q n fam sts (hvToHom vs))

/-- `chainG` denotes the left fold of the stage semantics `sem`, when each lane
schedule of each stage denotes its lane of `sem`. -/
theorem chainG_denote {ι : Type} (q n : ℕ) (fam : ι → ℕ → Com fieldDialect (Ctxn q n) (F q))
    (sem : ι → (ℕ → ZMod q) → ℕ → ZMod q) :
    ∀ (sts : List ι), (∀ st, st ∈ sts → ∀ (g : ℕ → ZMod q) (i : ℕ), i < n →
        PolyToField.fpDenote (fam st i) (fnVal q g n 0) = sem st g i) →
      ∀ {Γ : Ctxt fieldDialect} (h : Ctxt.Hom (Ctxn q n) Γ) (V : Valuation Γ)
        (f : ℕ → ZMod q), pullV h V = fnVal q f n 0 →
      (chainG q n fam sts h).denote V = fnVal q (sts.foldl (fun g st => sem st g) f) n 0
  | [], _, _, h, V, f, hV => by
      show MultiReturnCom.lookupVars (homToHV _ h) V = _
      rw [lookupVars_homToHV, hV]
      rfl
  | st :: sts, hfam, _, h, V, f, hV => by
      refine Com.foldVarN_denote n _ h V _ _ ?_
      intro Γ' h' vs V' _ hvs
      refine chainG_denote q n fam sem sts (fun st' hst' => hfam st' (List.mem_cons_of_mem _ hst'))
        (hvToHom vs) V' (sem st f) ?_
      rw [pullV_hvToHom, hvs, hV]
      refine eq_fnVal q _ n 0 _ fun i hi => ?_
      rw [hvGetD_denoteN _ _ _ i hi, Nat.zero_add]
      exact hfam st List.mem_cons_self f i hi

/-! ## 5. The inverse program -/

/-- The Gentleman–Sande lane schedule at width `n`: `a[ia] + a[ib]` when `up`,
and `z · (a[ia] − a[ib])` otherwise. -/
def gsLaneProg (q : ℕ) : (n : ℕ) → ZMod q → ℕ → ℕ → Bool → Com fieldDialect (Ctxn q n) (F q)
  | 0, z, _, _, _ => .var (constE z) (.ret .here)
  | n + 1, z, ia, ib, up =>
      if up then .var (addE (laneVar q n ia) (laneVar q n ib)) (.ret .here)
      else
        .var (constE z)
          (.var (subE (.there (laneVar q n ia)) (.there (laneVar q n ib)))
            (.var (mulE (.there .here) .here) (.ret .here)))

theorem gsLaneProg_denote (q n : ℕ) (z : ZMod q) (ia ib : ℕ) (up : Bool)
    (V : Valuation (Ctxn q (n + 1))) :
    PolyToField.fpDenote (gsLaneProg q (n + 1) z ia ib up) V
      = if up then fpv (laneVar q n ia) V + fpv (laneVar q n ib) V
        else z * (fpv (laneVar q n ia) V - fpv (laneVar q n ib) V) := by
  cases up <;> rfl

/-- The scaling lane schedule at width `n`: `s · a[i]`. -/
def scaleLaneProg (q : ℕ) : (n : ℕ) → ZMod q → ℕ → Com fieldDialect (Ctxn q n) (F q)
  | 0, s, _ => .var (constE s) (.ret .here)
  | n + 1, s, i => .var (constE s) (.var (mulE .here (.there (laneVar q n i))) (.ret .here))

theorem scaleLaneProg_denote (q n : ℕ) (s : ZMod q) (i : ℕ) (V : Valuation (Ctxn q (n + 1))) :
    PolyToField.fpDenote (scaleLaneProg q (n + 1) s i) V = s * fpv (laneVar q n i) V := rfl

/-- The lane schedules of an inverse stage: inverse layer `ℓ` for `some ℓ`, the
scaling by `s` for `none`. -/
def invStageProg (q n M L : ℕ) (ψ s : ZMod q) : Option ℕ → ℕ → Com fieldDialect (Ctxn q n) (F q)
  | some ℓ, i =>
      if i % (2 ^ (M - 1 - ℓ) + 2 ^ (M - 1 - ℓ)) < 2 ^ (M - 1 - ℓ) then
        gsLaneProg q n (ztInv ψ L (2 ^ ℓ + i / (2 ^ (M - 1 - ℓ) + 2 ^ (M - 1 - ℓ))))
          i (i + 2 ^ (M - 1 - ℓ)) true
      else
        gsLaneProg q n (ztInv ψ L (2 ^ ℓ + i / (2 ^ (M - 1 - ℓ) + 2 ^ (M - 1 - ℓ))))
          (i - 2 ^ (M - 1 - ℓ)) i false
  | none, i => scaleLaneProg q n s i

/-- The semantics of an inverse stage on lane functions. -/
def invStageFn (q M L : ℕ) (ψ s : ZMod q) : Option ℕ → (ℕ → ZMod q) → ℕ → ZMod q
  | some ℓ => invLayerFn ψ L M ℓ
  | none => fun f i => s * f i

/-- The inverse stages: layers `L - 1, …, 0`, then the scaling. -/
def invStages (L : ℕ) : List (Option ℕ) := (List.range L).reverse.map some ++ [none]

theorem invStageProg_denote (q M L : ℕ) (ψ s : ZMod q) (st : Option ℕ)
    (hst : ∀ ℓ, st = some ℓ → ℓ < M) (f : ℕ → ZMod q) (i : ℕ) (hi : i < 2 ^ M) :
    PolyToField.fpDenote (invStageProg q (2 ^ M) M L ψ s st i) (fnVal q f (2 ^ M) 0)
      = invStageFn q M L ψ s st f i := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ M = m + 1 := ⟨2 ^ M - 1, by have := Nat.two_pow_pos M; omega⟩
  cases st with
  | none =>
    simp only [invStageProg, invStageFn]
    rw [hm]
    rw [hm] at hi
    rw [scaleLaneProg_denote, fnVal_lookup q f m i 0 (by omega), Nat.zero_add]
  | some ℓ =>
    have hl := hst ℓ rfl
    have hpart := layer_partner_lt M ℓ i hl hi
    simp only [invStageProg, invStageFn, invLayerFn]
    rw [hm] at hi hpart
    rw [hm]
    generalize 2 ^ (M - 1 - ℓ) = len at hpart ⊢
    split
    · next hlt =>
      rw [gsLaneProg_denote, ite_eq_left rfl, fnVal_lookup q f m i 0 (by omega),
        fnVal_lookup q f m (i + len) 0 (by have := hpart hlt; omega)]
      simp
    · next hlt =>
      rw [gsLaneProg_denote, ite_eq_right (by simp), fnVal_lookup q f m (i - len) 0 (by omega),
        fnVal_lookup q f m i 0 (by omega)]
      simp

theorem foldl_invLayers (q M L : ℕ) (ψ s : ZMod q) :
    ∀ (k : ℕ) (f : ℕ → ZMod q),
      ((List.range k).reverse.map some).foldl (fun g st => invStageFn q M L ψ s st g) f
        = invRun ψ L M k f
  | 0, _ => rfl
  | k + 1, f => by
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons, List.foldl_cons, foldl_invLayers q M L ψ s k]
      rfl

theorem foldl_invStages (q M L : ℕ) (ψ s : ZMod q) (f : ℕ → ZMod q) :
    (invStages L).foldl (fun g st => invStageFn q M L ψ s st g) f = inttSpec ψ L M s f := by
  rw [invStages, List.foldl_append, foldl_invLayers]
  rfl

/-- The inverse transform program of `P` with scaling constant `s`, on
`2 ^ logN` lanes. -/
def inttProg (P : NttParams) (s : ℕ) :
    MultiReturnCom fieldDialect (Ctxn P.q (2 ^ P.logN)) (List.replicate (2 ^ P.logN) (F P.q)) :=
  chainG P.q (2 ^ P.logN)
    (invStageProg P.q (2 ^ P.logN) P.logN P.layers (P.psi : ZMod P.q) (s : ZMod P.q))
    (invStages P.layers) (Ctxt.Hom.id _)

/-- **The inverse value theorem.** Lane `i` of `inttProg P s` on the lanes `v` is
`inttSpec` at `i`. -/
theorem inttProg_denote (P : NttParams) (hP : P.Ok) (s : ℕ) (v : ℕ → ZMod P.q) (i : ℕ)
    (hi : i < 2 ^ P.logN) :
    hvGetD ((inttProg P s).denote (fnVal P.q v (2 ^ P.logN) 0)) i
      = inttSpec (P.psi : ZMod P.q) P.layers P.logN (s : ZMod P.q) v i := by
  rw [inttProg, chainG_denote P.q (2 ^ P.logN) _
    (invStageFn P.q P.logN P.layers (P.psi : ZMod P.q) (s : ZMod P.q)) (invStages P.layers)
    (fun st hst g j hj => invStageProg_denote P.q P.logN P.layers _ _ st
      (fun ℓ hℓ => by
        subst hℓ
        simp only [invStages, List.mem_append, List.mem_map, List.mem_reverse,
          List.mem_range, List.mem_singleton] at hst
        rcases hst with ⟨ℓ', h1, h2⟩ | h3
        · cases h2; have := hP.2.1; omega
        · cases h3)
      g j hj)
    (Ctxt.Hom.id _) _ v (pullV_id _), hvGetD_fnVal _ _ _ _ _ hi, Nat.zero_add,
    foldl_invStages]

/-- The scaling side condition, decidable on `ℕ`: `s · 2 ^ L ≡ 1 (mod q)`. -/
def ScaleOk (P : NttParams) (s : ℕ) : Prop := s * 2 ^ P.layers % P.q = 1 % P.q

instance (P : NttParams) (s : ℕ) : Decidable (ScaleOk P s) :=
  inferInstanceAs (Decidable (_ = _))

theorem ScaleOk.cast (P : NttParams) (s : ℕ) (h : ScaleOk P s) :
    (s : ZMod P.q) * 2 ^ P.layers = 1 := by
  have := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
  simpa using this

/-- **The inverse program inverts the transform program.** -/
theorem inttProg_nttSpec (P : NttParams) (hP : P.Ok) (s : ℕ) (hs : ScaleOk P s)
    (w : ℕ → ZMod P.q) (i : ℕ) (hi : i < 2 ^ P.logN) :
    hvGetD ((inttProg P s).denote
      (fnVal P.q (nttSpec (P.psi : ZMod P.q) P.layers P.logN w) (2 ^ P.logN) 0)) i = w i := by
  rw [inttProg_denote P hP s _ i hi]
  exact inttSpec_nttSpec _ P.layers P.logN (P.psi_pow hP) hP.1 hP.2.1 _ (hs.cast P s) w i hi

/-- FIPS 203: `128⁻¹ = 3303` modulo `3329`. -/
theorem mlkem_scaleOk : ScaleOk mlkemNtt 3303 := by decide

/-- FIPS 204: `256⁻¹ = 8347681` modulo `8380417`. -/
theorem mldsa_scaleOk : ScaleOk mldsaNtt 8347681 := by decide

end CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
