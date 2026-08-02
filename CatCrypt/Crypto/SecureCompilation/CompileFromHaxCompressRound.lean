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

§1 gives the single-binding denotation steps (`letBin_denote`, `letAdd_denote`,
`letLit_denote`) that carry the round body's seven adds and its constant
materialisation one binding at a time, alongside the four block lemmas of
`CompileFromHaxCompress` §7.
-/

namespace CatCrypt.Crypto.SecureCompilation.CompileFromHaxCompress

open CatCrypt.Hax
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp)

/-! ## §1  Round-local scratch and the single-binding denotation steps -/

/-- Round-local scratch/temp names (dead after the round). -/
def RL : List String :=
  ["ba","bb","bc","bx","ca","cb","cc","ma","mb","mc","mx","s1","s2","s3","s4",
   "u7","u8","u9","kc","t1","t2"]

/-- A name outside `RL` differs from every name in `RL`. -/
theorem ne_of_notMem_RL {y : String} (hy : y ∉ RL) {s : String} (hs : s ∈ RL) :
    y ≠ s := fun h => hy (by rw [h]; exact hs)

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
  rw [hag y (ne_of_notMem_RL hy hs1) (ne_of_notMem_RL hy hs2), agreek y hy]

/-- A `var` that is not the array parameter reads the local environment. -/
theorem denoteAtom_var {nIn : Nat} (I : Fin nIn → BitVec 32) (nm : String)
    (h : ("in" : String) ≠ nm) (ρ : String → Option (BitVec 32)) :
    denoteAtomExpr ["in"] I (ImpExpr.var nm) ρ = ρ nm := by
  simp only [denoteAtomExpr, idxOf_arr_none h]

/-- Binding a recognised binary ALU application of two atom operands runs the
    continuation in the environment extended at the bound name. -/
theorem letBin_denote {nIn : Nat} (I : Fin nIn → BitVec 32)
    (ρ : String → Option (BitVec 32)) (x f : String) {op : JasminBinOp}
    (hf : recogBin f = some op) {X Y : ImpExpr} {vx vy : BitVec 32}
    (hX : denoteAtomExpr ["in"] I X ρ = some vx)
    (hY : denoteAtomExpr ["in"] I Y ρ = some vy) (cont : ImpExpr) :
    ImpExpr.denoteScalar ["in"] I (.letBind x (.app f [X, Y]) cont) ρ
      = ImpExpr.denoteScalar ["in"] I cont
          (fun y => if y = x then some (op.apply vx vy) else ρ y) := by
  simp only [ImpExpr.denoteScalar, hf, hX, hY, Option.bind_some, Option.map_some]

/-- The `wrapping_add` instance of `letBin_denote`. -/
theorem letAdd_denote {nIn : Nat} (I : Fin nIn → BitVec 32)
    (ρ : String → Option (BitVec 32)) (x : String) {X Y : ImpExpr}
    {vx vy : BitVec 32} (hX : denoteAtomExpr ["in"] I X ρ = some vx)
    (hY : denoteAtomExpr ["in"] I Y ρ = some vy) (cont : ImpExpr) :
    ImpExpr.denoteScalar ["in"] I (.letBind x (.app "wrapping_add" [X, Y]) cont) ρ
      = ImpExpr.denoteScalar ["in"] I cont
          (fun y => if y = x then some (vx + vy) else ρ y) :=
  letBin_denote I ρ x "wrapping_add" (op := JasminBinOp.add) (by simp [recogBin]) hX hY cont

/-- Binding a literal constant runs the continuation in the environment extended
    at the bound name with the constant. -/
theorem letLit_denote {nIn : Nat} (I : Fin nIn → BitVec 32)
    (ρ : String → Option (BitVec 32)) (x : String) {l : ImpLit} {n : Nat}
    (hl : litNat? l = some n) (cont : ImpExpr) :
    ImpExpr.denoteScalar ["in"] I (.letBind x (.lit l) cont) ρ
      = ImpExpr.denoteScalar ["in"] I cont
          (fun y => if y = x then some (BitVec.ofNat 32 n) else ρ y) := by
  simp only [ImpExpr.denoteScalar, denoteAtomExpr, hl, Option.map_some,
    Option.bind_some]

/-- Extending an environment at a round-local scratch name preserves its
    agreement with `ρ` off `RL`. -/
theorem agree_ext {ρ ρk : String → Option (BitVec 32)} {x : String} (hx : x ∈ RL)
    (v : BitVec 32) (h : ∀ y, y ∉ RL → ρk y = ρ y) :
    ∀ y, y ∉ RL → (fun z => if z = x then some v else ρk z) y = ρ y := by
  intro y hy
  simp only [if_neg (ne_of_notMem_RL hy hx)]
  exact h y hy

/-! ## §2  Name-distinctness facts for the output names `aN`/`eN` -/

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

/-- A scratch name of `RL` is not a round-output name. -/
theorem RL_ne_aN {s : String} (hs : s ∈ RL) (r : Nat) : s ≠ aN r :=
  fun h => aN_notin_RL r (h ▸ hs)

/-! ## §3  The round body is value-preserving -/

set_option linter.unusedSimpArgs false in
/-- **One compression round denotes to the FIPS round.** The round body for round
    `r`, run on read operands denoting `va..vh` stably off the round-local scratch
    and the round's two output names, runs `cont` in an environment binding
    `aN r`/`eN r` to the `a`/`e` words of `roundFn` and agreeing with `ρ`
    elsewhere. The round is traversed in twelve steps, each rewriting one binding
    group: the four block lemmas of `CompileFromHaxCompress` §7 and the eight
    single-binding steps of §1. -/
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
  -- Σ₁(e)
  rw [bigSigBlock_denote I ρ 6 11 25 "s1" eE ve
        (readUnder I r ρ ρ eE ve heE (fun _ _ => rfl) "ba" "bb" (by decide) (by decide))]
  set ρ1 : String → Option (BitVec 32) :=
    (fun y => if y = "s1" then some (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25)
              else if y = "bx" then some (ve.rotateRight 6 ^^^ ve.rotateRight 11)
              else if y = "bc" then some (ve.rotateRight 25)
              else if y = "bb" then some (ve.rotateRight 11)
              else if y = "ba" then some (ve.rotateRight 6) else ρ y) with hρ1def
  have agree1 : ∀ y, y ∉ RL → ρ1 y = ρ y := by
    intro y hy
    simp only [hρ1def, if_neg (ne_of_notMem_RL hy (show "s1" ∈ RL by decide)),
      if_neg (ne_of_notMem_RL hy (show "bx" ∈ RL by decide)),
      if_neg (ne_of_notMem_RL hy (show "bc" ∈ RL by decide)),
      if_neg (ne_of_notMem_RL hy (show "bb" ∈ RL by decide)),
      if_neg (ne_of_notMem_RL hy (show "ba" ∈ RL by decide))]
  have h_ones1 : ρ1 "__ones" = some (BitVec.ofNat 32 4294967295) := by
    rw [agree1 "__ones" (by decide)]; exact h_ones
  -- Ch(e,f,g)
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
    simp only [if_neg (ne_of_notMem_RL hy (show "s2" ∈ RL by decide)),
      if_neg (ne_of_notMem_RL hy (show "cc" ∈ RL by decide)),
      if_neg (ne_of_notMem_RL hy (show "cb" ∈ RL by decide)),
      if_neg (ne_of_notMem_RL hy (show "ca" ∈ RL by decide))]
    exact agree1 y hy
  -- u7 := h + Σ₁
  have hs1 : ρ2 "s1" = some (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25) := by
    rw [hρ2def]; simp only [String.reduceEq, reduceIte]
    rw [hρ1def]; simp only [String.reduceEq, reduceIte]
  have hs2 : ρ2 "s2" = some (chFn ve vf vg) := by
    rw [hρ2def]; simp only [String.reduceEq, reduceIte]
  rw [letAdd_denote I ρ2 "u7" (hhE ρ2 (fun y hy _ _ => agree2 y hy))
        ((denoteAtom_var I "s1" (by decide) ρ2).trans hs1)]
  set ρ3 : String → Option (BitVec 32) :=
    (fun y => if y = "u7"
              then some (vh + (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25))
              else ρ2 y) with hρ3def
  have agree3 : ∀ y, y ∉ RL → ρ3 y = ρ y := by
    rw [hρ3def]; exact agree_ext (by decide) _ agree2
  -- u8 := u7 + Ch
  have hu7 : ρ3 "u7"
      = some (vh + (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25)) := by
    rw [hρ3def]; simp only [String.reduceEq, reduceIte]
  have hs2' : ρ3 "s2" = some (chFn ve vf vg) := by
    rw [hρ3def]; simp only [String.reduceEq, reduceIte]; exact hs2
  rw [letAdd_denote I ρ3 "u8" ((denoteAtom_var I "u7" (by decide) ρ3).trans hu7)
        ((denoteAtom_var I "s2" (by decide) ρ3).trans hs2')]
  set ρ4 : String → Option (BitVec 32) :=
    (fun y => if y = "u8"
              then some (vh + (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25)
                  + chFn ve vf vg)
              else ρ3 y) with hρ4def
  have agree4 : ∀ y, y ∉ RL → ρ4 y = ρ y := by
    rw [hρ4def]; exact agree_ext (by decide) _ agree3
  -- kc := K[r]
  rw [letLit_denote I ρ4 "kc" (l := .int (kVal r)) (n := kVal r) (by simp [litNat?])]
  set ρ5 : String → Option (BitVec 32) :=
    (fun y => if y = "kc" then some (BitVec.ofNat 32 (kVal r)) else ρ4 y) with hρ5def
  have agree5 : ∀ y, y ∉ RL → ρ5 y = ρ y := by
    rw [hρ5def]; exact agree_ext (by decide) _ agree4
  -- u9 := u8 + K[r]
  have hu8 : ρ5 "u8"
      = some (vh + (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25)
          + chFn ve vf vg) := by
    rw [hρ5def]; simp only [String.reduceEq, reduceIte]
    rw [hρ4def]; simp only [String.reduceEq, reduceIte]
  have hkc : ρ5 "kc" = some (BitVec.ofNat 32 (kVal r)) := by
    rw [hρ5def]; simp only [String.reduceEq, reduceIte]
  rw [letAdd_denote I ρ5 "u9" ((denoteAtom_var I "u8" (by decide) ρ5).trans hu8)
        ((denoteAtom_var I "kc" (by decide) ρ5).trans hkc)]
  set ρ6 : String → Option (BitVec 32) :=
    (fun y => if y = "u9"
              then some (vh + (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25)
                  + chFn ve vf vg + BitVec.ofNat 32 (kVal r))
              else ρ5 y) with hρ6def
  have agree6 : ∀ y, y ∉ RL → ρ6 y = ρ y := by
    rw [hρ6def]; exact agree_ext (by decide) _ agree5
  -- t1 := u9 + W[r]
  have hu9 : ρ6 "u9"
      = some (vh + (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25)
          + chFn ve vf vg + BitVec.ofNat 32 (kVal r)) := by
    rw [hρ6def]; simp only [String.reduceEq, reduceIte]
  rw [letAdd_denote I ρ6 "t1" ((denoteAtom_var I "u9" (by decide) ρ6).trans hu9)
        (show denoteAtomExpr ["in"] I (rdIn (8 + r)) ρ6 = some (inpGet I (8 + r)) by
          rw [rdIn]; exact denoteAtomExpr_indexLit I "in" (8 + r) ρ6)]
  set ρ7 : String → Option (BitVec 32) :=
    (fun y => if y = "t1"
              then some (vh + (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25)
                  + chFn ve vf vg + BitVec.ofNat 32 (kVal r) + inpGet I (8 + r))
              else ρ6 y) with hρ7def
  have agree7 : ∀ y, y ∉ RL → ρ7 y = ρ y := by
    rw [hρ7def]; exact agree_ext (by decide) _ agree6
  -- Σ₀(a)
  rw [bigSigBlock_denote I ρ7 2 13 22 "s3" aE va
        (readUnder I r ρ ρ7 aE va haE agree7 "ba" "bb" (by decide) (by decide))]
  set ρ8 : String → Option (BitVec 32) :=
    (fun y => if y = "s3" then some (va.rotateRight 2 ^^^ va.rotateRight 13 ^^^ va.rotateRight 22)
              else if y = "bx" then some (va.rotateRight 2 ^^^ va.rotateRight 13)
              else if y = "bc" then some (va.rotateRight 22)
              else if y = "bb" then some (va.rotateRight 13)
              else if y = "ba" then some (va.rotateRight 2) else ρ7 y) with hρ8def
  have agree8 : ∀ y, y ∉ RL → ρ8 y = ρ y := by
    intro y hy
    rw [hρ8def]
    simp only [if_neg (ne_of_notMem_RL hy (show "s3" ∈ RL by decide)),
      if_neg (ne_of_notMem_RL hy (show "bx" ∈ RL by decide)),
      if_neg (ne_of_notMem_RL hy (show "bc" ∈ RL by decide)),
      if_neg (ne_of_notMem_RL hy (show "bb" ∈ RL by decide)),
      if_neg (ne_of_notMem_RL hy (show "ba" ∈ RL by decide))]
    exact agree7 y hy
  -- Maj(a,b,c)
  rw [majBlock_denote I ρ8 "s4" aE bE cE va vb vc
        (readUnder I r ρ ρ8 aE va haE agree8 "ma" "mb" (by decide) (by decide))
        (readUnder I r ρ ρ8 bE vb hbE agree8 "ma" "mb" (by decide) (by decide))
        (readUnder I r ρ ρ8 cE vc hcE agree8 "ma" "mb" (by decide) (by decide))]
  set ρ9 : String → Option (BitVec 32) :=
    (fun y => if y = "s4" then some (majFn va vb vc)
              else if y = "mx" then some ((va &&& vb) ^^^ (va &&& vc))
              else if y = "mc" then some (vb &&& vc)
              else if y = "mb" then some (va &&& vc)
              else if y = "ma" then some (va &&& vb) else ρ8 y) with hρ9def
  have agree9 : ∀ y, y ∉ RL → ρ9 y = ρ y := by
    intro y hy
    rw [hρ9def]
    simp only [if_neg (ne_of_notMem_RL hy (show "s4" ∈ RL by decide)),
      if_neg (ne_of_notMem_RL hy (show "mx" ∈ RL by decide)),
      if_neg (ne_of_notMem_RL hy (show "mc" ∈ RL by decide)),
      if_neg (ne_of_notMem_RL hy (show "mb" ∈ RL by decide)),
      if_neg (ne_of_notMem_RL hy (show "ma" ∈ RL by decide))]
    exact agree8 y hy
  -- t2 := Σ₀ + Maj
  have hs3 : ρ9 "s3"
      = some (va.rotateRight 2 ^^^ va.rotateRight 13 ^^^ va.rotateRight 22) := by
    rw [hρ9def]; simp only [String.reduceEq, reduceIte]
    rw [hρ8def]; simp only [String.reduceEq, reduceIte]
  have hs4 : ρ9 "s4" = some (majFn va vb vc) := by
    rw [hρ9def]; simp only [String.reduceEq, reduceIte]
  rw [letAdd_denote I ρ9 "t2" ((denoteAtom_var I "s3" (by decide) ρ9).trans hs3)
        ((denoteAtom_var I "s4" (by decide) ρ9).trans hs4)]
  set ρ10 : String → Option (BitVec 32) :=
    (fun y => if y = "t2"
              then some ((va.rotateRight 2 ^^^ va.rotateRight 13 ^^^ va.rotateRight 22)
                  + majFn va vb vc)
              else ρ9 y) with hρ10def
  have agree10 : ∀ y, y ∉ RL → ρ10 y = ρ y := by
    rw [hρ10def]; exact agree_ext (by decide) _ agree9
  have ht1 : ρ10 "t1" = some (vh + (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25)
      + chFn ve vf vg + BitVec.ofNat 32 (kVal r) + inpGet I (8 + r)) := by
    rw [hρ10def]; simp only [String.reduceEq, reduceIte]
    rw [hρ9def]; simp only [String.reduceEq, reduceIte]
    rw [hρ8def]; simp only [String.reduceEq, reduceIte]
    rw [hρ7def]; simp only [String.reduceEq, reduceIte]
  have ht2 : ρ10 "t2"
      = some ((va.rotateRight 2 ^^^ va.rotateRight 13 ^^^ va.rotateRight 22)
          + majFn va vb vc) := by
    rw [hρ10def]; simp only [String.reduceEq, reduceIte]
  -- a' := t1 + t2
  rw [letAdd_denote I ρ10 (aN r) ((denoteAtom_var I "t1" (by decide) ρ10).trans ht1)
        ((denoteAtom_var I "t2" (by decide) ρ10).trans ht2)]
  set ρ11 : String → Option (BitVec 32) :=
    (fun y => if y = aN r
              then some (vh + (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25)
                  + chFn ve vf vg + BitVec.ofNat 32 (kVal r) + inpGet I (8 + r)
                  + ((va.rotateRight 2 ^^^ va.rotateRight 13 ^^^ va.rotateRight 22)
                      + majFn va vb vc))
              else ρ10 y) with hρ11def
  have agree11 : ∀ y, y ∉ RL → y ≠ aN r → ρ11 y = ρ y := by
    intro y hy hy1
    rw [hρ11def]; simp only [if_neg hy1]; exact agree10 y hy
  -- e' := d + t1
  rw [letAdd_denote I ρ11 (eN r)
        (hdE ρ11 (fun y hy hy1 _ => agree11 y hy hy1))
        ((denoteAtom_var I "t1" (by decide) ρ11).trans
          (by rw [hρ11def]; simp only [if_neg (RL_ne_aN (show "t1" ∈ RL by decide) r)]
              exact ht1))]
  set ρ12 : String → Option (BitVec 32) :=
    (fun y => if y = eN r
              then some (vd + (vh + (ve.rotateRight 6 ^^^ ve.rotateRight 11 ^^^ ve.rotateRight 25)
                  + chFn ve vf vg + BitVec.ofNat 32 (kVal r) + inpGet I (8 + r)))
              else ρ11 y) with hρ12def
  refine ⟨ρ12, rfl, ?_, ?_, ?_⟩
  · simp only [hρ12def, if_neg (aN_ne_eN r r), hρ11def, if_true,
      roundFn, bigSigma0, bigSigma1, kBV]
  · simp only [hρ12def, if_true, roundFn, bigSigma1, kBV]
  · intro y hy hy1 hy2
    rw [hρ12def]; simp only [if_neg hy2]
    exact agree11 y hy hy1

/-! ## §4  The compression unroller is value-preserving (general-N induction) -/

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
        rw [denoteAtom_var I nm hin ρ'', h nm hnmRL hnmj]; exact hρnm
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
        (by rw [denoteScalar_var, denoteAtom_var I (aN r) hin_aN ρ']; exact haN)
        (hVarStable (aN r) _ (aN_notin_RL r)
          (fun j hj => ⟨fun he => by have := aN_inj he; omega, aN_ne_eN r j⟩) hin_aN haN)
        (hcarry aE st.a haE) (hcarry bE st.b hbE) (hcarry cE st.c hcE)
        (hVarStable (eN r) _ (eN_notin_RL r)
          (fun j hj => ⟨fun he => (aN_ne_eN j r he.symm).elim, fun he => by have := eN_inj he; omega⟩)
          hin_eN heN)
        (hcarry eE st.e heE) (hcarry fE st.f hfE) (hcarry gE st.g hgE)
      exact hkey

end CatCrypt.Crypto.SecureCompilation.CompileFromHaxCompress
