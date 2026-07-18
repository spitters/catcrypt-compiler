/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.CompileFromHaxCompress

/-!
# General-N value-correctness of the SHA-256 compression loop

The per-round value-preservation lemma `roundBody_denote` (one compression round
denotes to exactly the FIPS `roundFn`, value-preserving, for any round `r` and any
read operands satisfying the stability hypotheses) and — built on it by induction —
`compUnroll_denote`, giving the whole compression loop's value. The compression
analogue of §9's `schedStep_denote` / `schedUnroll_denoteScalar`. The read operands
are required to be stable off the round-local scratch (`RL`) plus the future output
names (`aN j`/`eN j`, `j ≥ r`); `readUnder` bridges this to each block's local
read hypothesis.
-/

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxCompress

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp)

/-- Round-local scratch/temp names (dead after the round). -/
def RL : List String :=
  ["ba","bb","bc","bx","ca","cb","cc","ma","mb","mc","mx","s1","s2","s3","s4",
   "u7","u8","u9","kc","t1","t2"]

/-- Derive a block's 2-scratch read hypothesis from the round-wide stability `hX`
    plus the current env's agreement with `ρ` off `RL`. -/
theorem readUnder {nIn : Nat} (I : Fin nIn → BitVec 32) (rr : Nat)
    (ρ ρk : String → Option (BitVec 32)) (X : ImpExpr) (v : BitVec 32)
    (hX : ∀ ρ', (∀ y, y ∉ RL → y ≠ aN rr → y ≠ eN rr → ρ' y = ρ y) →
        denoteAtomExpr ["in"] I X ρ' = some v)
    (agreek : ∀ y, y ∉ RL → ρk y = ρ y)
    (s1 s2 : String) (hs1 : s1 ∈ RL) (hs2 : s2 ∈ RL) :
    ∀ ρ', (∀ y, y ≠ s1 → y ≠ s2 → ρ' y = ρk y) →
      denoteAtomExpr ["in"] I X ρ' = some v := by
  intro ρ' hag
  apply hX
  intro y hy _ _
  have h1 : y ≠ s1 := fun h => hy (by rw [h]; exact hs1)
  have h2 : y ≠ s2 := fun h => hy (by rw [h]; exact hs2)
  rw [hag y h1 h2, agreek y hy]

set_option maxHeartbeats 1000000 in
theorem roundBody_denote {nIn : Nat} (I : Fin nIn → BitVec 32)
    (ρ : String → Option (BitVec 32)) (r : Nat)
    (aE bE cE dE eE fE gE hE : ImpExpr) (va vb vc vd ve vf vg vh : BitVec 32)
    (cont : ImpExpr) (h_ones : ρ "__ones" = some (BitVec.ofNat 32 4294967295))
    (haE : ∀ ρ', (∀ y, y ∉ RL → y ≠ aN r → y ≠ eN r → ρ' y = ρ y) → denoteAtomExpr ["in"] I aE ρ' = some va)
    (hbE : ∀ ρ', (∀ y, y ∉ RL → y ≠ aN r → y ≠ eN r → ρ' y = ρ y) → denoteAtomExpr ["in"] I bE ρ' = some vb)
    (hcE : ∀ ρ', (∀ y, y ∉ RL → y ≠ aN r → y ≠ eN r → ρ' y = ρ y) → denoteAtomExpr ["in"] I cE ρ' = some vc)
    (hdE : ∀ ρ', (∀ y, y ∉ RL → y ≠ aN r → y ≠ eN r → ρ' y = ρ y) → denoteAtomExpr ["in"] I dE ρ' = some vd)
    (heE : ∀ ρ', (∀ y, y ∉ RL → y ≠ aN r → y ≠ eN r → ρ' y = ρ y) → denoteAtomExpr ["in"] I eE ρ' = some ve)
    (hfE : ∀ ρ', (∀ y, y ∉ RL → y ≠ aN r → y ≠ eN r → ρ' y = ρ y) → denoteAtomExpr ["in"] I fE ρ' = some vf)
    (hgE : ∀ ρ', (∀ y, y ∉ RL → y ≠ aN r → y ≠ eN r → ρ' y = ρ y) → denoteAtomExpr ["in"] I gE ρ' = some vg)
    (hhE : ∀ ρ', (∀ y, y ∉ RL → y ≠ aN r → y ≠ eN r → ρ' y = ρ y) → denoteAtomExpr ["in"] I hE ρ' = some vh) :
    ∃ ρ', ImpExpr.denoteScalar ["in"] I (roundBody r aE bE cE dE eE fE gE hE cont) ρ
            = ImpExpr.denoteScalar ["in"] I cont ρ'
        ∧ ρ' (aN r) = some (roundFn (St.mk va vb vc vd ve vf vg vh) (kBV r) (inpGet I (8 + r))).a
        ∧ ρ' (eN r) = some (roundFn (St.mk va vb vc vd ve vf vg vh) (kBV r) (inpGet I (8 + r))).e
        ∧ ∀ y, y ∉ RL → y ≠ aN r → y ≠ eN r → ρ' y = ρ y := by
  unfold roundBody
  rw [bigSigBlock_denote I ρ 6 11 25 "s1" eE ve
        (readUnder I r ρ ρ eE ve heE (fun _ _ => rfl) "ba" "bb" (by decide) (by decide))]
  set ρ1 : String → Option (BitVec 32) :=
    (fun y => if y = "s1" then some (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25)
              else if y = "bx" then some (ve.rotateRight 6 ^^^ ve.rotateRight 11)
              else if y = "bc" then some (ve.rotateRight 25)
              else if y = "bb" then some (ve.rotateRight 11)
              else if y = "ba" then some (ve.rotateRight 6) else ρ y) with hρ1def
  have hneRL : ∀ (y : String), y ∉ RL → ∀ s : String, s ∈ RL → y ≠ s :=
    fun y hy s hs h => hy (by rw [h]; exact hs)
  have agree1 : ∀ y, y ∉ RL → ρ1 y = ρ y := by
    intro y hy
    simp only [hρ1def, if_neg (hneRL y hy "s1" (by decide)), if_neg (hneRL y hy "bx" (by decide)),
      if_neg (hneRL y hy "bc" (by decide)), if_neg (hneRL y hy "bb" (by decide)),
      if_neg (hneRL y hy "ba" (by decide))]
  have h_ones1 : ρ1 "__ones" = some (BitVec.ofNat 32 4294967295) := by
    rw [agree1 "__ones" (by decide)]; exact h_ones
  rw [chBlock_denote I ρ1 "s2" eE fE gE ve vf vg h_ones1
        (readUnder I r ρ ρ1 eE ve heE agree1 "ca" "cb" (by decide) (by decide))
        (readUnder I r ρ ρ1 fE vf hfE agree1 "ca" "cb" (by decide) (by decide))
        (readUnder I r ρ ρ1 gE vg hgE agree1 "ca" "cb" (by decide) (by decide))]
  set ρ2 : String → Option (BitVec 32) :=
    (fun y => if y = "s2" then some (chFn ve vf vg)
              else if y = "cc" then some ((ve ^^^ BitVec.ofNat 32 4294967295) &&& vg)
              else if y = "cb" then some (ve ^^^ BitVec.ofNat 32 4294967295)
              else if y = "ca" then some (ve &&& vf) else ρ1 y) with hρ2def
  have agree2 : ∀ y, y ∉ RL → ρ2 y = ρ y := by
    intro y hy
    rw [hρ2def]
    simp only [if_neg (hneRL y hy "s2" (by decide)), if_neg (hneRL y hy "cc" (by decide)),
      if_neg (hneRL y hy "cb" (by decide)), if_neg (hneRL y hy "ca" (by decide))]
    exact agree1 y hy
  have hvarlk : ∀ nm : String, ("in":String) ≠ nm →
      denoteAtomExpr ["in"] I (ImpExpr.var nm) = fun env => env nm := by
    intro nm hnm; funext env; simp only [denoteAtomExpr, idxOf_arr_none hnm]
  have hh := hhE ρ2 (fun y hy _ _ => agree2 y hy)
  have hs1 : ρ2 "s1" = some (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25) := by
    rw [hρ2def]
    simp only [String.reduceEq, reduceIte]
    rw [hρ1def]; simp only [String.reduceEq, reduceIte]
  have hs2 : ρ2 "s2" = some (chFn ve vf vg) := by
    rw [hρ2def]; simp only [String.reduceEq, reduceIte]
  have hkc : ∀ env, denoteAtomExpr ["in"] I (ImpExpr.lit (ImpLit.int (kVal r))) env
      = some (kBV r) := by
    intro env; simp only [denoteAtomExpr, litNat?, Int.toNat, kBV, Option.map_some]
  have hrd : ∀ env, denoteAtomExpr ["in"] I (rdIn (8 + r)) env = some (inpGet I (8 + r)) := by
    intro env; rw [rdIn]; exact denoteAtomExpr_indexLit I "in" (8 + r) env
  simp only [ImpExpr.denoteScalar, recogBin, JasminBinOp.apply,
    hvarlk "s1" (by decide), hvarlk "s2" (by decide), hvarlk "u7" (by decide),
    hvarlk "u8" (by decide), hvarlk "u9" (by decide), hvarlk "kc" (by decide),
    hkc, hrd, hh, hs1, hs2, String.reduceEq, reduceIte,
    true_or, or_false, or_self, Option.bind_some, Option.map_some]
  -- env after the 5 adds
  set ρ3 : String → Option (BitVec 32) :=
    (fun y => if y = "t1" then some (vh + (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25)
                  + chFn ve vf vg + kBV r + inpGet I (8 + r))
              else if y = "u9" then some (vh + (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25)
                  + chFn ve vf vg + kBV r)
              else if y = "kc" then some (kBV r)
              else if y = "u8" then some (vh + (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25)
                  + chFn ve vf vg)
              else if y = "u7" then some (vh + (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25))
              else ρ2 y) with hρ3def
  have agree3 : ∀ y, y ∉ RL → ρ3 y = ρ y := by
    intro y hy
    rw [hρ3def]
    simp only [if_neg (hneRL y hy "t1" (by decide)), if_neg (hneRL y hy "u9" (by decide)),
      if_neg (hneRL y hy "kc" (by decide)), if_neg (hneRL y hy "u8" (by decide)),
      if_neg (hneRL y hy "u7" (by decide))]
    exact agree2 y hy
  rw [bigSigBlock_denote I ρ3 2 13 22 "s3" aE va
        (readUnder I r ρ ρ3 aE va haE agree3 "ba" "bb" (by decide) (by decide))]
  set ρ4 : String → Option (BitVec 32) :=
    (fun y => if y = "s3" then some (va.rotateRight 2 ^^^ va.rotateRight 13 ^^^ va.rotateRight 22)
              else if y = "bx" then some (va.rotateRight 2 ^^^ va.rotateRight 13)
              else if y = "bc" then some (va.rotateRight 22)
              else if y = "bb" then some (va.rotateRight 13)
              else if y = "ba" then some (va.rotateRight 2) else ρ3 y) with hρ4def
  have agree4 : ∀ y, y ∉ RL → ρ4 y = ρ y := by
    intro y hy
    rw [hρ4def]
    simp only [if_neg (hneRL y hy "s3" (by decide)), if_neg (hneRL y hy "bx" (by decide)),
      if_neg (hneRL y hy "bc" (by decide)), if_neg (hneRL y hy "bb" (by decide)),
      if_neg (hneRL y hy "ba" (by decide))]
    exact agree3 y hy
  rw [majBlock_denote I ρ4 "s4" aE bE cE va vb vc
        (readUnder I r ρ ρ4 aE va haE agree4 "ma" "mb" (by decide) (by decide))
        (readUnder I r ρ ρ4 bE vb hbE agree4 "ma" "mb" (by decide) (by decide))
        (readUnder I r ρ ρ4 cE vc hcE agree4 "ma" "mb" (by decide) (by decide))]
  set ρ5 : String → Option (BitVec 32) :=
    (fun y => if y = "s4" then some (majFn va vb vc)
              else if y = "mx" then some ((va &&& vb) ^^^ (va &&& vc))
              else if y = "mc" then some (vb &&& vc)
              else if y = "mb" then some (va &&& vc)
              else if y = "ma" then some (va &&& vb) else ρ4 y) with hρ5def
  have agree5 : ∀ y, y ∉ RL → ρ5 y = ρ y := by
    intro y hy
    rw [hρ5def]
    simp only [if_neg (hneRL y hy "s4" (by decide)), if_neg (hneRL y hy "mx" (by decide)),
      if_neg (hneRL y hy "mc" (by decide)), if_neg (hneRL y hy "mb" (by decide)),
      if_neg (hneRL y hy "ma" (by decide))]
    exact agree4 y hy
  have hs3 : ρ5 "s3" = some (va.rotateRight 2 ^^^ va.rotateRight 13 ^^^ va.rotateRight 22) := by
    rw [hρ5def]; simp only [String.reduceEq, reduceIte]
    rw [hρ4def]; simp only [String.reduceEq, reduceIte]
  have hs4 : ρ5 "s4" = some (majFn va vb vc) := by
    rw [hρ5def]; simp only [String.reduceEq, reduceIte]
  have ht1 : ρ5 "t1" = some (vh + (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25)
      + chFn ve vf vg + kBV r + inpGet I (8 + r)) := by
    rw [hρ5def]; simp only [String.reduceEq, reduceIte]
    rw [hρ4def]; simp only [String.reduceEq, reduceIte]
    rw [hρ3def]; simp only [String.reduceEq, reduceIte]
  have hdd := hdE ρ5 (fun y hy _ _ => agree5 y hy)
  simp only [ImpExpr.denoteScalar, recogBin, JasminBinOp.apply,
    hvarlk "s3" (by decide), hvarlk "s4" (by decide), hvarlk "t1" (by decide),
    hvarlk "t2" (by decide), hs3, hs4, ht1, hdd, String.reduceEq, reduceIte,
    true_or, or_false, or_self, Option.bind_some, Option.map_some]
  -- name distinctness: aN/eN start with 'q', literals don't
  have ht1aN : ("t1":String) ≠ aN r := by
    intro h
    have hh : ("t1":String).toList = (aN r).toList := congrArg String.toList h
    rw [aN, String.toList_append, show ("qa".toList) = ['q','a'] from rfl,
        show (("t1":String).toList) = ['t','1'] from rfl, String.toList_ofList] at hh
    simp only [List.cons_append, List.cons.injEq] at hh
    exact absurd hh.1 (by decide)
  have haNeN : aN r ≠ eN r := by
    intro h
    have hh : (aN r).toList = (eN r).toList := congrArg String.toList h
    rw [aN, eN, String.toList_append, String.toList_append,
        show ("qa".toList) = ['q','a'] from rfl, show ("qe".toList) = ['q','e'] from rfl,
        String.toList_ofList] at hh
    simp only [List.cons_append, List.cons.injEq] at hh
    exact absurd hh.2.1 (by decide)
  -- the final `dE` read (env extended at `aN r`/`t2`, which `dE` does not reference)
  have hd_ext : denoteAtomExpr ["in"] I dE (fun y =>
      if y = aN r then some (vh + (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25)
          + chFn ve vf vg + kBV r + inpGet I (8 + r)
          + ((va.rotateRight 2 ^^^ va.rotateRight 13 ^^^ va.rotateRight 22) + majFn va vb vc))
        else if y = "t2" then some ((va.rotateRight 2 ^^^ va.rotateRight 13 ^^^ va.rotateRight 22)
            + majFn va vb vc) else ρ5 y) = some vd := by
    apply hdE
    intro y hy hy1 _
    rw [if_neg hy1, if_neg (hneRL y hy "t2" (by decide))]
    exact agree5 y hy
  rw [hd_ext]
  simp only [if_neg ht1aN, Option.bind_some, Option.map_some]
  refine ⟨_, rfl, ?_, ?_, ?_⟩
  · -- ρ' (aN r) = roundFn.a
    simp only [if_neg haNeN, reduceIte, roundFn, bigSigma0, bigSigma1]
  · -- ρ' (eN r) = roundFn.e
    simp only [reduceIte, roundFn, bigSigma1]
  · -- agreement off RL, ≠ aN r, ≠ eN r
    intro y hy hy1 hy2
    simp only [if_neg hy2, if_neg hy1, if_neg (hneRL y hy "t2" (by decide))]
    exact agree5 y hy

/-! ## Name-distinctness facts for the output names `aN`/`eN` -/

theorem aN_data (r : Nat) : (aN r).toList = 'q' :: 'a' :: List.replicate (r + 1) 'I' := by
  simp [aN, String.toList_append, String.toList_ofList]

theorem eN_data (r : Nat) : (eN r).toList = 'q' :: 'e' :: List.replicate (r + 1) 'I' := by
  simp [eN, String.toList_append, String.toList_ofList]

theorem aN_ne_eN (r s : Nat) : aN r ≠ eN s := by
  intro h; have hh := congrArg String.toList h
  rw [aN_data, eN_data] at hh
  simp only [List.cons.injEq] at hh
  exact absurd hh.2.1 (by decide)

theorem aN_inj {r s : Nat} (h : aN r = aN s) : r = s := by
  have hh := congrArg String.toList h
  rw [aN_data, aN_data] at hh
  simp only [List.cons.injEq, List.replicate_inj, true_and] at hh
  omega

theorem eN_inj {r s : Nat} (h : eN r = eN s) : r = s := by
  have hh := congrArg String.toList h
  rw [eN_data, eN_data] at hh
  simp only [List.cons.injEq, List.replicate_inj, true_and] at hh
  omega

theorem aN_notin_RL (r : Nat) : aN r ∉ RL := by
  intro h
  have hq : (aN r).toList.head? = some 'q' := by simp [aN_data]
  simp only [RL, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    (rw [h] at hq; revert hq; decide)

theorem eN_notin_RL (r : Nat) : eN r ∉ RL := by
  intro h
  have hq : (eN r).toList.head? = some 'q' := by simp [eN_data]
  simp only [RL, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    (rw [h] at hq; revert hq; decide)

/-! ## The compression unroller is value-preserving (general-N induction) -/

/-- The forward iteration of `roundFn` over `count` rounds starting at round `r`. -/
def stIter {nIn : Nat} (I : Fin nIn → BitVec 32) (st : St) : (r count : Nat) → St
  | _, 0 => st
  | r, c + 1 => stIter I (roundFn st (kBV r) (inpGet I (8 + r))) (r + 1) c

/-- `denoteScalar` of a bare `var` is its atom read (the catch-all case). -/
theorem denoteScalar_var {nIn : Nat} (I : Fin nIn → BitVec 32) (nm : String)
    (ρ : String → Option (BitVec 32)) :
    ImpExpr.denoteScalar ["in"] I (ImpExpr.var nm) ρ = denoteAtomExpr ["in"] I (ImpExpr.var nm) ρ :=
  rfl

/-- A read operand's value is stable off the round-local scratch `RL` and the future
    output names `aN j`/`eN j` (`j ≥ r`). -/
abbrev ReadStable {nIn : Nat} (I : Fin nIn → BitVec 32) (ρ : String → Option (BitVec 32))
    (r : Nat) (X : ImpExpr) (v : BitVec 32) : Prop :=
  ∀ ρ', (∀ y, y ∉ RL → (∀ j, r ≤ j → y ≠ aN j ∧ y ≠ eN j) → ρ' y = ρ y) →
    denoteAtomExpr ["in"] I X ρ' = some v

/-- **The compression unroller is value-preserving.** `compUnroll count r` (the
    `count`-round chain from round `r`, threading the eight working-word read
    operands) denotes to the final `a` word of the FIPS iteration `stIter`, given the
    `__ones` materialisation, the `denoteScalar` a-read for the base, and the eight
    `ReadStable` operand hypotheses. Proved by induction on `count`. -/
theorem compUnroll_denote {nIn : Nat} (I : Fin nIn → BitVec 32) :
    ∀ (count r : Nat) (aE bE cE dE eE fE gE hE : ImpExpr) (st : St)
      (ρ : String → Option (BitVec 32)),
      ρ "__ones" = some (BitVec.ofNat 32 4294967295) →
      ImpExpr.denoteScalar ["in"] I aE ρ = some st.a →
      ReadStable I ρ r aE st.a → ReadStable I ρ r bE st.b → ReadStable I ρ r cE st.c →
      ReadStable I ρ r dE st.d → ReadStable I ρ r eE st.e → ReadStable I ρ r fE st.f →
      ReadStable I ρ r gE st.g → ReadStable I ρ r hE st.h →
      ImpExpr.denoteScalar ["in"] I (compUnroll count r aE bE cE dE eE fE gE hE) ρ
        = some (stIter I st r count).a
  | 0, r, aE, bE, cE, dE, eE, fE, gE, hE, st, ρ, _, haDS, _, _, _, _, _, _, _, _ => by
      simp only [compUnroll, stIter]; exact haDS
  | c + 1, r, aE, bE, cE, dE, eE, fE, gE, hE, st, ρ, h_ones, _, haE, hbE, hcE, hdE,
      heE, hfE, hgE, hhE => by
      simp only [compUnroll]
      -- one round via roundBody_denote (weaken ReadStable to the round-local hyps)
      obtain ⟨ρ', hden, haN, heN, hag⟩ :=
        roundBody_denote I ρ r aE bE cE dE eE fE gE hE st.a st.b st.c st.d st.e st.f st.g st.h
          (compUnroll c (r + 1) (.var (aN r)) aE bE cE (.var (eN r)) eE fE gE) h_ones
          (fun ρ'' h => haE ρ'' (fun y hy hj => h y hy (hj r (le_refl r)).1 (hj r (le_refl r)).2))
          (fun ρ'' h => hbE ρ'' (fun y hy hj => h y hy (hj r (le_refl r)).1 (hj r (le_refl r)).2))
          (fun ρ'' h => hcE ρ'' (fun y hy hj => h y hy (hj r (le_refl r)).1 (hj r (le_refl r)).2))
          (fun ρ'' h => hdE ρ'' (fun y hy hj => h y hy (hj r (le_refl r)).1 (hj r (le_refl r)).2))
          (fun ρ'' h => heE ρ'' (fun y hy hj => h y hy (hj r (le_refl r)).1 (hj r (le_refl r)).2))
          (fun ρ'' h => hfE ρ'' (fun y hy hj => h y hy (hj r (le_refl r)).1 (hj r (le_refl r)).2))
          (fun ρ'' h => hgE ρ'' (fun y hy hj => h y hy (hj r (le_refl r)).1 (hj r (le_refl r)).2))
          (fun ρ'' h => hhE ρ'' (fun y hy hj => h y hy (hj r (le_refl r)).1 (hj r (le_refl r)).2))
      rw [hden]
      -- the post-round env agrees with ρ off RL, aN r, eN r
      have hcarry : ∀ (X : ImpExpr) (v : BitVec 32), ReadStable I ρ r X v →
          ReadStable I ρ' (r + 1) X v := by
        intro X v hX ρ'' h
        apply hX
        intro y hy hj
        rw [h y hy (fun j hj' => hj j (by omega)), hag y hy (hj r (le_refl r)).1 (hj r (le_refl r)).2]
      -- ReadStable for a freshly-output var name
      have hVarStable : ∀ (nm : String) (v : BitVec 32), nm ∉ RL →
          (∀ j, r + 1 ≤ j → nm ≠ aN j ∧ nm ≠ eN j) → ("in" : String) ≠ nm →
          ρ' nm = some v → ReadStable I ρ' (r + 1) (.var nm) v := by
        intro nm v hnmRL hnmj hin hρnm ρ'' h
        rw [show denoteAtomExpr ["in"] I (.var nm) ρ'' = ρ'' nm from by
              simp only [denoteAtomExpr, idxOf_arr_none hin]]
        rw [h nm hnmRL hnmj]; exact hρnm
      have hin_aN : ("in" : String) ≠ aN r := by
        intro he; have hd := aN_data r; rw [← he] at hd; simp at hd
      have hin_eN : ("in" : String) ≠ eN r := by
        intro he; have hd := eN_data r; rw [← he] at hd; simp at hd
      have hon_aN : ("__ones" : String) ≠ aN r := by
        intro he; have hd := aN_data r; rw [← he] at hd; simp at hd
      have hon_eN : ("__ones" : String) ≠ eN r := by
        intro he; have hd := eN_data r; rw [← he] at hd; simp at hd
      have hkey := compUnroll_denote I c (r + 1) (.var (aN r)) aE bE cE (.var (eN r)) eE fE gE
        (roundFn st (kBV r) (inpGet I (8 + r))) ρ'
        (by rw [hag "__ones" (by decide) hon_aN hon_eN]; exact h_ones)
        (by rw [denoteScalar_var, show denoteAtomExpr ["in"] I (.var (aN r)) ρ' = ρ' (aN r) from by
              simp only [denoteAtomExpr, idxOf_arr_none hin_aN]]; exact haN)
        (hVarStable (aN r) _ (aN_notin_RL r)
          (fun j hj => ⟨fun he => by have := aN_inj he; omega, aN_ne_eN r j⟩) hin_aN haN)
        (hcarry aE st.a haE) (hcarry bE st.b hbE) (hcarry cE st.c hcE)
        (hVarStable (eN r) _ (eN_notin_RL r)
          (fun j hj => ⟨fun he => (aN_ne_eN j r he.symm).elim, fun he => by have := eN_inj he; omega⟩)
          hin_eN heN)
        (hcarry eE st.e heE) (hcarry fE st.f hfE) (hcarry gE st.g hgE)
      exact hkey

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxCompress
