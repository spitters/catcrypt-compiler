/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Guards
public import CatCrypt.Crypto.SecureCompilation.Dialects.LeafOracleScalar

/-!
# The total abstraction at a leaf oracle

`ascendGL L fuel` (`Guards.lean`) abstracts an opaque leaf call to the unsupported
guard, since `semU` binds its destination to `CryptoTy.default`. This module states
the abstraction over `semUL ls fuel`, the waist semantics at a leaf oracle `ls`, and
lets it take an abstract function per leaf name.

## Abstract leaves

An argument of a leaf call is abstracted by `absArg L a x`: the word `a x`, or, for a
layout array `x` of length `n`, the vector of its `n` element values. `vEnc` is the
same abstraction of a concrete typed value. An abstract leaf `f : List AVal → ZMod 2^64`
is sound for the oracle `ls` at a name (`LeafAbs ls name f`) when the oracle's
`u64` result, encoded by `wEnc`, is `f` of the encoded arguments. `AbsLeaves` gives an
optional abstract leaf per name, and `LeavesSound ls lf` says each is sound.

`ascendGLL lf L fuel` is `ascendGL L fuel` with three arms that consult `lf`:

* `RCall fname dst args` goes through `corresL_call` when `lf fname` is given, `dst`
  is an unreserved `u64` word and every argument is a layout array or an unreserved
  non-temp word name;
* `RSelect dst sel src0 src1` goes through `corresL_selectLeaf` at the name
  `"select"` when one of `sel`, `src0`, `src1` is a layout array, so that `semScalarL`
  takes its leaf arm; the leaf receives `src0` and `src1`, as the front's `extCall`
  does, and not the selector;
* `RArrLoadLit dst src idx` goes through `corresL_arrLoadLitLeaf` at the name
  `"arrLoad:idx"` when `src` is not a `TArr _ .TU64` array held in the layout.

Every other arm is the arm of `ascendGL`, and `ascendGLL noLeaves L fuel` is
`ascendGL L fuel` (`ascendGLL_noLeaves`).

## Main definitions

* `CorresL`, `CorresUL` — `Corres` and `CorresU` over `semScalarL ls` and `semUL ls`
* `AVal`, `vEnc`, `absArg`, `argOkB` — abstraction of leaf arguments
* `LeafAbs`, `AbsLeaves`, `LeavesSound`, `noLeaves`, `leafOfAbs` — abstract leaves
* `ascendGLL` — the total abstraction with abstract leaves

## Main results

* `corresL_default_iff`, `corresUL_default_iff` — at `defaultLeaf` the relations are
  `Corres` and `CorresU`
* `corresL_leafWord`, `corresL_call`, `corresL_selectLeaf`, `corresL_arrLoadLitLeaf` —
  the leaf rules
* `ascendGLL_sound` — soundness at `semUL ls fuel` under `LeavesSound ls lf`
* `ascendGLL_noLeaves`, `ascendGL_sound_of_ascendGLL` — the specialisation to
  `ascendGL_sound`
* `leafAbs_leafOfAbs` — every abstract leaf is sound for the oracle `leafOfAbs`
* `leafK_corres` — a kernel with an `"arrLoad:0"` read of a `TBytes 8` array and a
  `"select"` over it, refined to its abstract program
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle
open CatCrypt.Crypto.SecureCompilation.Dialects.LeafOracleScalar

/-! ## Correspondence at a leaf oracle -/

/-- `Corres` over `semScalarL ls`. -/
def CorresL {AState : Type} (ls : SemLeafSpec) (SR : SEnvScalar → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : LowCT) : Prop :=
  ∀ env a, SR env a → P a → ∃ env', semScalarL ls c env = some env' ∧ SR env' (fa a)

/-- `CorresU` over `semUL ls fuel`. -/
def CorresUL {AState : Type} (ls : SemLeafSpec) (fuel : Nat) (SR : SEnvScalar → AState → Prop)
    (P : AState → Prop) (fa : AState → AState) (c : LowCT) : Prop :=
  ∀ env a, SR env a → P a → ∃ env', semUL ls fuel c env = some env' ∧ SR env' (fa a)

/-- At the default oracle `CorresL` is `Corres`. -/
theorem corresL_default_iff {AState : Type} {SR : SEnvScalar → AState → Prop}
    {P : AState → Prop} {fa : AState → AState} {c : LowCT} :
    CorresL defaultLeaf SR P fa c ↔ Corres SR P fa c := by
  simp only [CorresL, Corres, semScalarL_default]

/-- At the default oracle `CorresUL` is `CorresU`. -/
theorem corresUL_default_iff {AState : Type} {fuel : Nat} {SR : SEnvScalar → AState → Prop}
    {P : AState → Prop} {fa : AState → AState} {c : LowCT} :
    CorresUL defaultLeaf fuel SR P fa c ↔ CorresU fuel SR P fa c := by
  simp only [CorresUL, CorresU, semUL_default]

section Structural

variable {AState : Type} (ls : SemLeafSpec) (SR : SEnvScalar → AState → Prop)

/-- A `Corres` result transfers to `CorresL ls` on a command on which `semScalarL ls`
    is `semScalar`. -/
theorem corresL_of_corres_eq {P : AState → Prop} {fa : AState → AState} {c : LowCT}
    (h : Corres SR P fa c) (heq : ∀ env, semScalarL ls c env = semScalar c env) :
    CorresL ls SR P fa c := by
  intro env a hSR hP
  obtain ⟨env', hs, hSR'⟩ := h env a hSR hP
  exact ⟨env', (heq env).trans hs, hSR'⟩

theorem corresUL_weaken {fuel : Nat} {P P' : AState → Prop} {fa : AState → AState}
    {c : LowCT} (h : CorresUL ls fuel SR P fa c) (himp : ∀ a, P' a → P a) :
    CorresUL ls fuel SR P' fa c := by
  intro env a hSR hP'; exact h env a hSR (himp a hP')

theorem corresUL_block {fuel : Nat} {P : AState → Prop} {fa : AState → AState}
    {body : LowCT} (h : CorresUL ls fuel SR P fa body) :
    CorresUL ls fuel SR P fa (.RBlock body) := by
  intro env a hSR hP
  obtain ⟨env', hstep, hSR'⟩ := h env a hSR hP
  exact ⟨env', hstep, hSR'⟩

theorem corresUL_seq {fuel : Nat} {P Q : AState → Prop} {fa ga : AState → AState}
    {c₁ c₂ : LowCT} (h₁ : CorresUL ls fuel SR P fa c₁) (h₂ : CorresUL ls fuel SR Q ga c₂)
    (hpre : ∀ a, P a → Q (fa a)) :
    CorresUL ls fuel SR P (fun a => ga (fa a)) (.RSeq c₁ c₂) := by
  intro env a hSR hP
  obtain ⟨env₁, hstep₁, hSR₁⟩ := h₁ env a hSR hP
  obtain ⟨env₂, hstep₂, hSR₂⟩ := h₂ env₁ (fa a) hSR₁ (hpre a hP)
  exact ⟨env₂, by simp only [semUL, hstep₁, Option.bind_some, hstep₂], hSR₂⟩

/-- On a node that is not seq-like, a `CorresL` leaf is a `CorresUL` leaf. -/
theorem corresUL_of_corresL {fuel : Nat} {P : AState → Prop} {fa : AState → AState}
    {c : LowCT} (hne : isSeqLike c = false) (h : CorresL ls SR P fa c) :
    CorresUL ls fuel SR P fa c := by
  intro env a hSR hP
  obtain ⟨env', hstep, hSR'⟩ := h env a hSR hP
  exact ⟨env', by rw [semUL_leaf ls fuel env hne]; exact hstep, hSR'⟩

/-- The guarded conditional `RIfNz name thenBlk RSkip` at `semUL`. -/
theorem corresUL_cond {fuel : Nat} {P : AState → Prop} {fb : AState → AState}
    {name : String} {thenBlk : LowCT} (g : AState → Bool)
    (hg : ∀ env a, SR env a → guardNz name env = g a)
    (hbody : CorresUL ls fuel SR P fb thenBlk) :
    CorresUL ls fuel SR (fun a => g a = true → P a) (fun a => if g a then fb a else a)
      (.RIfNz name thenBlk .RSkip) := by
  intro env a hSR hP
  have hgu : guardNz name env = g a := hg env a hSR
  show ∃ env', semScalarCond (fun e => semUL ls fuel thenBlk e) (guardNz name) env = some env' ∧
    SR env' (if g a = true then fb a else a)
  by_cases hga : g a = true
  · obtain ⟨env', hstep, hSR'⟩ := hbody env a hSR (hP hga)
    refine ⟨env', ?_, ?_⟩
    · simp only [semScalarCond, hgu, hga, cond_true, hstep]
    · simp only [hga, if_true]; exact hSR'
  · simp only [Bool.not_eq_true] at hga
    refine ⟨env, ?_, ?_⟩
    · simp only [semScalarCond, hgu, hga, cond_false]
    · simp only [hga, Bool.false_eq_true, if_false]; exact hSR

theorem corresUL_whileNz_aux {fuel : Nat} {Q : AState → Prop} {fb : AState → AState}
    {name : String} {body : LowCT} (g : AState → Bool)
    (hg : ∀ env a, SR env a → guardNz name env = g a)
    (hbody : CorresUL ls fuel SR Q fb body) :
    ∀ (k : Nat) (env : SEnvScalar) (a : AState), SR env a → ahalts g fb k a →
      atrips Q g fb k a →
      ∃ env', semScalarWhile (fun e => semUL ls fuel body e) (guardNz name) k env = some env' ∧
        SR env' (awhile g fb k a) := by
  intro k
  induction k with
  | zero => intro env a _ hh _; exact hh.elim
  | succ k ih =>
      intro env a hSR hh ht
      obtain ⟨env₁, hstep, hSR₁⟩ := hbody env a hSR ht.1
      by_cases hga : g (fb a) = true
      · obtain ⟨env', hrun, hSR'⟩ := ih env₁ (fb a) hSR₁ (hh hga) (ht.2 hga)
        refine ⟨env', ?_, ?_⟩
        · simp only [semScalarWhile, hstep, hg env₁ (fb a) hSR₁, hga, if_true, hrun]
        · simp only [awhile, hga, if_true]; exact hSR'
      · simp only [Bool.not_eq_true] at hga
        refine ⟨env₁, ?_, ?_⟩
        · simp only [semScalarWhile, hstep, hg env₁ (fb a) hSR₁, hga, Bool.false_eq_true,
            if_false]
        · simp only [awhile, hga, Bool.false_eq_true, if_false]; exact hSR₁

/-- The do-while rule at `semUL`. -/
theorem corresUL_whileNz {fuel : Nat} {Q : AState → Prop} {fb : AState → AState}
    {name : String} {body : LowCT} (g : AState → Bool)
    (hg : ∀ env a, SR env a → guardNz name env = g a)
    (hbody : CorresUL ls fuel SR Q fb body) :
    CorresUL ls fuel SR (fun a => ahalts g fb fuel a ∧ atrips Q g fb fuel a)
      (awhile g fb fuel) (.RWhileNz name body) := by
  intro env a hSR hP
  exact corresUL_whileNz_aux ls SR g hg hbody fuel env a hSR hP.1 hP.2

/-- The counted-loop rule at `semUL`, with a trip-indexed precondition. -/
theorem corresUL_for_trips {fuel : Nat} {Q : AState → Prop} {fb : AState → AState}
    {x : String} {body : LowCT} (setA : Nat → AState → AState)
    (hset : ∀ env a n, SR env a →
      SR (env.upd x (t := .sword 64) (BitVec.ofNat 64 n)) (setA n a))
    (hbody : CorresUL ls fuel SR Q fb body) :
    ∀ N : Nat, CorresUL ls fuel SR (fun a => ∀ n, n < N → Q (setA n (forFold setA fb n a)))
      (forFold setA fb N) (.RFor x N body) := by
  intro N
  induction N with
  | zero => intro env a hSR _; exact ⟨env, rfl, hSR⟩
  | succ n ih =>
      intro env a hSR hP
      obtain ⟨envPre, hPre, hSRPre⟩ := ih env a hSR (fun k hk => hP k (by omega))
      obtain ⟨env', hstep, hSR'⟩ :=
        hbody _ _ (hset envPre _ n hSRPre) (hP n (Nat.lt_succ_self n))
      refine ⟨env', ?_, hSR'⟩
      have hPre' : semRForD (fun e => semUL ls fuel body e) x n env = some envPre := hPre
      show semRForD (fun e => semUL ls fuel body e) x (n + 1) env = some env'
      simp only [semRForD, hPre', hstep]

end Structural

/-- A node carrying the `unsupported` guard: the precondition never holds. -/
theorem corresUL_unsupported (ls : SemLeafSpec) (SRf : SEnvScalar → AField → Prop)
    (fuel : Nat) (c : LowCT) (ctor : String) :
    CorresUL ls fuel SRf (guardsHold [Guard.unsupported ctor]) id c :=
  fun _ _ _ h => (h _ (List.mem_singleton.mpr rfl)).elim

/-- On a loop-free command `semUL ls fuel` is `semScalarL ls`. -/
theorem semUL_eq_semScalarL_of_loopFree (ls : SemLeafSpec) (fuel : Nat) :
    ∀ (c : LowCT), loopFree c = true → ∀ env, semUL ls fuel c env = semScalarL ls c env := by
  intro c
  induction c with
  | RSeq c₁ c₂ ih₁ ih₂ =>
      intro h env
      simp only [loopFree, Bool.and_eq_true] at h
      simp only [semUL, semScalarL, ih₁ h.1, ih₂ h.2]
  | RBlock body ih =>
      intro h env
      simp only [semUL, semScalarL, ih h]
  | RFor x N body ih =>
      intro h env
      simp only [semUL, semScalarL, ih h]
  | RWhileNz name body _ => intro h; simp [loopFree] at h
  | RIfNz name thenBr elseBr _ _ =>
      intro h env
      have hne : elseBr ≠ .RSkip := by
        rintro rfl; simp [loopFree] at h
      exact semUL_leaf ls fuel env (isSeqLike_rIfNz_of_ne name thenBr elseBr hne)
  | _ => intro _ env; exact semUL_leaf ls fuel env rfl

/-! ## The word and array leaves at a leaf oracle -/

/-- The dynamic-index array read over a layout, at the oracle `ls`. -/
theorem corresL_arrLoad_oracle (ls : SemLeafSpec) (L : ArrLayout) (dst src : Located)
    (idxVar : String) (m : Nat)
    (hdst : dst.locSrc = .TU64) (hsz : (src.locVar, m + 1) ∈ L)
    (hdk : arrKeyB L dst.locVar = false) (hit : ¬ isTmpName idxVar)
    (hik : arrKeyB L idxVar = false) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setVal dst.locVar (a (elemKey src.locVar ((a idxVar).val % (m + 1)))) a)
      (.RArrLoad dst src idxVar) := by
  intro env a hSR _
  obtain ⟨_, av, hav, havE⟩ := hSR.2 _ hsz
  have hav' : env src.locVar = some ⟨.memref (m + 1), av⟩ := hav
  obtain ⟨iv, hiv, hivE⟩ := hSR.1 idxVar hit hik
  refine ⟨env.upd dst.locVar (t := .sword 64) (memGetDyn av iv.toNat), ?_, ?_⟩
  · simp only [semScalarL, Located.locDst, hdst, hav', hiv]
  · refine srwordL_set dst.locVar (memGetDyn av iv.toNat) _ hdk ?_ hSR
      (by simp [SEnvScalar.upd]) (fun y _ hy => by simp [SEnvScalar.upd, hy])
    rw [val_of_wEnc hivE]
    exact havE ⟨iv.toNat % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩

/-- The dynamic-index array write over a layout, at the oracle `ls`. -/
theorem corresL_arrStore_oracle (ls : SemLeafSpec) (L : ArrLayout) (arr src : Located)
    (idxVar : String) (m : Nat)
    (harr : encodeTy arr.locSrc = .memref (m + 1)) (hsz : (arr.locVar, m + 1) ∈ L)
    (hit : ¬ isTmpName idxVar) (hik : arrKeyB L idxVar = false)
    (hst : ¬ isTmpName src.locVar) (hsk : arrKeyB L src.locVar = false) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setVal (elemKey arr.locVar ((a idxVar).val % (m + 1))) (a src.locVar) a)
      (.RArrStore arr idxVar src) := by
  intro env a hSR _
  obtain ⟨_, av, hav, _⟩ := hSR.2 _ hsz
  have hav' : env arr.locVar = some ⟨.memref (m + 1), av⟩ := hav
  obtain ⟨iv, hiv, hivE⟩ := hSR.1 idxVar hit hik
  obtain ⟨sv, hsv, hsvE⟩ := hSR.1 src.locVar hst hsk
  refine ⟨env.upd arr.locVar (t := encodeTy arr.locSrc) (harr.symm ▸ memSetDyn av iv.toNat sv),
    ?_, ?_⟩
  · simp only [semScalarL, Located.locDst, hav', hiv, hsv, harr, dif_pos]
  · show SRwordL L _ (setVal (elemKey arr.locVar ((a idxVar).val % (m + 1))) (a src.locVar) a)
    rw [val_of_wEnc hivE]
    refine srwordL_arrWrite arr.locVar (m + 1) (iv.toNat % (m + 1)) av
      (memSetDyn av iv.toNat sv) sv _ hsvE hSR hsz hav' (fun j => ?_) (fun y => ?_)
    · by_cases h : j.val = iv.toNat % (m + 1) <;> simp [memSetDyn, h, Fin.ext_iff]
    · by_cases hy : y = arr.locVar
      · simp only [SEnvScalar.upd, if_pos hy]
        exact congrArg some (sigma_memref harr _)
      · simp [SEnvScalar.upd, hy]

/-- The literal-index word read of a `TArr _ .TU64` layout array, at the oracle `ls`. -/
theorem corresL_arrLoadLit_oracle (ls : SemLeafSpec) (L : ArrLayout) (dst src : Located)
    (idx k m : Nat) (hdst : dst.locSrc = .TU64) (hsrc : src.locSrc = .TArr k .TU64)
    (hsz : (src.locVar, m + 1) ∈ L) (hidx : idx < m + 1)
    (hlit : idx < 2 ^ 64) (hdk : arrKeyB L dst.locVar = false) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setVal dst.locVar (a (elemKey src.locVar idx)) a)
      (.RArrLoadLit dst src idx) := by
  intro env a hSR _
  obtain ⟨_, av, hav, havE⟩ := hSR.2 _ hsz
  have hav' : env src.locVar = some ⟨.memref (m + 1), av⟩ := hav
  refine ⟨env.upd dst.locVar (t := .sword 64) (memGetDyn av (BitVec.ofNat 64 idx).toNat),
    semScalarL_rArrLoadLit_word ls dst src idx env k (m + 1) av hdst hsrc hav', ?_⟩
  refine srwordL_set dst.locVar (memGetDyn av (BitVec.ofNat 64 idx).toNat) _ hdk ?_ hSR
    (by simp [SEnvScalar.upd]) (fun y _ hy => by simp [SEnvScalar.upd, hy])
  have hk : (⟨(BitVec.ofNat 64 idx).toNat % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩ :
      Fin (m + 1)) = ⟨idx, hidx⟩ := Fin.ext (litIdx_mod hidx hlit)
  show wEnc (av ⟨(BitVec.ofNat 64 idx).toNat % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩) = _
  rw [hk]
  exact havE ⟨idx, hidx⟩

/-- The literal-index word write to a `TArr _ .TU64` layout array, at the oracle `ls`. -/
theorem corresL_arrStoreLit_oracle (ls : SemLeafSpec) (L : ArrLayout) (arr src : Located)
    (idx k m : Nat) (harr : arr.locSrc = .TArr k .TU64)
    (hsz : (arr.locVar, m + 1) ∈ L) (hidx : idx < m + 1) (hlit : idx < 2 ^ 64)
    (hst : ¬ isTmpName src.locVar) (hsk : arrKeyB L src.locVar = false) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setVal (elemKey arr.locVar idx) (a src.locVar) a)
      (.RArrStoreLit arr idx src) := by
  intro env a hSR _
  obtain ⟨_, av, hav, _⟩ := hSR.2 _ hsz
  have hav' : env arr.locVar = some ⟨.memref (m + 1), av⟩ := hav
  obtain ⟨sv, hsv, hsvE⟩ := hSR.1 src.locVar hst hsk
  refine ⟨env.upd arr.locVar (t := .memref (m + 1))
      (memSetDyn av (BitVec.ofNat 64 idx).toNat sv),
    semScalarL_rArrStoreLit_word ls arr src idx env k (m + 1) av sv harr hav' hsv, ?_⟩
  refine srwordL_arrWrite arr.locVar (m + 1) idx av
    (memSetDyn av (BitVec.ofNat 64 idx).toNat sv) sv _ hsvE hSR hsz hav' (fun j => ?_)
    (fun y => rfl)
  have hk := litIdx_mod hidx hlit
  show (if j = ⟨(BitVec.ofNat 64 idx).toNat % (m + 1), Nat.mod_lt _ (Nat.succ_pos m)⟩
    then sv else av j) = _
  by_cases h : j.val = idx
  · rw [if_pos (Fin.ext (h.trans hk.symm)), if_pos h]
  · rw [if_neg (fun hj => h ((congrArg Fin.val hj).trans hk)), if_neg h]

/-- The constant-time word select over a layout, at the oracle `ls`. -/
theorem corresL_select_oracle (ls : SemLeafSpec) (L : ArrLayout) (dst : Located)
    (sel : String) (src0 src1 : Located)
    (hdst : dst.locSrc = .TU64) (hdk : arrKeyB L dst.locVar = false)
    (hst : ¬ isTmpName sel) (hsk : arrKeyB L sel = false)
    (h0t : ¬ isTmpName src0.locVar) (h0k : arrKeyB L src0.locVar = false)
    (h1t : ¬ isTmpName src1.locVar) (h1k : arrKeyB L src1.locVar = false) :
    CorresL ls (SRwordL L) (fun _ => True) (selSet sel dst.locVar src0.locVar src1.locVar)
      (.RSelect dst sel src0 src1) := by
  intro env a hSR _
  obtain ⟨sw, hsw, hswE⟩ := hSR.1 sel hst hsk
  obtain ⟨aw, haw, hawE⟩ := hSR.1 src0.locVar h0t h0k
  obtain ⟨cw, hcw, hcwE⟩ := hSR.1 src1.locVar h1t h1k
  refine ⟨env.upd dst.locVar (t := .sword 64) (selectWord sw aw cw),
    semScalarL_rSelect_word ls dst sel src0 src1 env sw aw cw hdst hsw haw hcw, ?_⟩
  refine srwordL_set dst.locVar (selectWord sw aw cw) _ hdk ?_ hSR
    (by simp [SEnvScalar.upd]) (fun y _ hy => by simp [SEnvScalar.upd, hy])
  by_cases hz : sw = 0#64
  · have haz : a sel = 0 := hswE ▸ (wEnc_eq_zero_iff sw).mpr hz
    rw [selectWord, if_pos hz, if_pos haz, hawE]
  · have haz : ¬ a sel = 0 := fun h => hz ((wEnc_eq_zero_iff sw).mp (hswE ▸ h))
    rw [selectWord, if_neg hz, if_neg haz, hcwE]

/-! ## Abstract leaves -/

/-- The abstraction of a leaf argument: a `u64` word, an array of `u64` words, or a value
    of any other type. -/
inductive AVal where
  | word (z : ZMod (2 ^ 64))
  | arr (n : Nat) (v : Fin n → ZMod (2 ^ 64))
  | other

/-- The abstraction of a typed value: `wEnc` of a `u64` word, `wEnc` of each element of a
    `.memref` array, `other` on every other type. -/
def vEnc : ((t : CryptoTy) × ⟦t⟧) → AVal
  | ⟨.sword 64, w⟩ => .word (wEnc w)
  | ⟨.memref n, av⟩ => .arr n (fun j => wEnc (av j))
  | _ => .other

/-- The abstraction of the argument name `x` on the abstract store: the element values of
    a layout array, the word at `x` otherwise. -/
def absArg (L : ArrLayout) (a : AField) (x : String) : AVal :=
  match layoutSize L x with
  | some n => .arr n (fun j => a (elemKey x j))
  | none => .word (a x)

/-- The argument name `x` is a layout array, or a non-temp name the layout does not
    reserve. Under `SRwordL L` such a name is bound to a value `vEnc` abstracts to
    `absArg L a x`. -/
def argOkB (L : ArrLayout) (x : String) : Bool :=
  match layoutSize L x with
  | some _ => true
  | none => notTmpB x && !arrKeyB L x

theorem vEnc_env_srwordL {L : ArrLayout} {env : SEnvScalar} {a : AField} {x : String}
    (hSR : SRwordL L env a) (hx : argOkB L x = true) :
    ∃ v, env x = some v ∧ vEnc v = absArg L a x := by
  unfold argOkB at hx
  unfold absArg
  rcases hs : layoutSize L x with _ | n
  · simp only [hs, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hx
    obtain ⟨w, hw, hwe⟩ := hSR.1 x (notTmpB_sound x hx.1) hx.2
    exact ⟨_, hw, by simp [vEnc, hwe]⟩
  · obtain ⟨_, av, hav, havE⟩ := hSR.2 _ (layoutSize_mem hs)
    refine ⟨_, hav, ?_⟩
    simp only [vEnc]
    congr 1
    funext j
    exact havE j

/-- Under `SRwordL L`, the argument values of names satisfying `argOkB` abstract to the
    abstract arguments, none of them `other`. -/
theorem argVals_srwordL {L : ArrLayout} {env : SEnvScalar} {a : AField}
    (hSR : SRwordL L env a) :
    ∀ (names : List String), (∀ x ∈ names, argOkB L x = true) →
      (argVals env names).map vEnc = names.map (absArg L a) ∧
        ∀ v ∈ argVals env names, vEnc v ≠ .other
  | [], _ => ⟨rfl, by simp [argVals]⟩
  | x :: xs, h => by
      obtain ⟨v, hv, hve⟩ := vEnc_env_srwordL hSR (h x (List.mem_cons_self))
      obtain ⟨ih1, ih2⟩ :=
        argVals_srwordL hSR xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
      have hcons : argVals env (x :: xs) = v :: argVals env xs := by
        simp [argVals, hv]
      refine ⟨by rw [hcons, List.map_cons, List.map_cons, hve, ih1], ?_⟩
      rw [hcons]
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · rw [hve]; unfold absArg; split <;> simp
      · exact ih2 u hu

/-- The abstract leaf `f` is sound for the oracle `ls` at `name`: on arguments none of
    which is abstracted to `other`, the `u64` value of the oracle, encoded, is `f` of
    the abstracted arguments. -/
def LeafAbs (ls : SemLeafSpec) (name : String) (f : List AVal → ZMod (2 ^ 64)) : Prop :=
  ∀ vals : List ((t : CryptoTy) × ⟦t⟧), (∀ v ∈ vals, vEnc v ≠ .other) →
    wEnc (ls name (.sword 64) vals) = f (vals.map vEnc)

/-- A word-valued leaf node over a layout: if `c` binds the word `dst` to the oracle at
    `name` on the arguments `names`, and `f` is sound for the oracle at `name`, then `c`
    abstracts to `dst := f (abstract arguments)`. -/
theorem corresL_leafWord (ls : SemLeafSpec) (L : ArrLayout) (c : LowCT) (name dst : String)
    (names : List String) (f : List AVal → ZMod (2 ^ 64)) (hf : LeafAbs ls name f)
    (hdk : arrKeyB L dst = false) (hargs : ∀ x ∈ names, argOkB L x = true)
    (hsem : ∀ env a, SRwordL L env a →
      semScalarL ls c env =
        some (env.upd dst (t := .sword 64) (ls name (.sword 64) (argVals env names)))) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setVal dst (f (names.map (absArg L a))) a) c := by
  intro env a hSR _
  obtain ⟨hmap, hne⟩ := argVals_srwordL hSR names hargs
  refine ⟨_, hsem env a hSR, ?_⟩
  refine srwordL_set dst (ls name (.sword 64) (argVals env names)) (f (names.map (absArg L a)))
    hdk ?_ hSR (by simp [SEnvScalar.upd]) (fun y _ hy => by simp [SEnvScalar.upd, hy])
  rw [hf _ hne, hmap]

/-- **The leaf call rule.** `RCall fname dst args` with `dst` an unreserved `u64` word and
    each argument a layout array or an unreserved non-temp word name abstracts to
    `dst := f (abstract arguments)`, for an abstract leaf `f` sound for the oracle at
    `fname`. -/
theorem corresL_call (ls : SemLeafSpec) (L : ArrLayout) (fname : String) (dst : Located)
    (args : List Located) (f : List AVal → ZMod (2 ^ 64)) (hf : LeafAbs ls fname f)
    (hd : dst.locSrc = .TU64) (hdk : arrKeyB L dst.locVar = false)
    (hargs : ∀ x ∈ locNames args, argOkB L x = true) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setVal dst.locVar (f ((locNames args).map (absArg L a))) a)
      (.RCall fname dst args) := by
  obtain ⟨dv, dt⟩ := dst
  simp only at hd hdk ⊢
  subst hd
  exact corresL_leafWord ls L _ fname dv (locNames args) f hf hdk hargs
    (fun env _ _ => semScalarL_rCall ls fname ⟨dv, .TU64⟩ args env)

/-- A name held in the layout is not bound to a `u64` word. -/
theorem srwordL_layout_not_word {L : ArrLayout} {env : SEnvScalar} {a : AField} {y : String}
    (hSR : SRwordL L env a) (hy : (layoutSize L y).isSome = true) (w : BitVec 64)
    (hw : env y = some ⟨.sword 64, w⟩) : False := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hy
  obtain ⟨_, av, hav, _⟩ := hSR.2 _ (layoutSize_mem hn)
  have hav' : env y = some ⟨.memref n, av⟩ := hav
  rw [hav'] at hw
  simp at hw

/-- **The `"select"` leaf rule.** A select into an unreserved `u64` word one of whose
    selector and sources is a layout array takes the leaf arm of `semScalarL`, and
    abstracts to `dst := f [src0, src1]` for an abstract leaf `f` sound for the oracle at
    `"select"`. -/
theorem corresL_selectLeaf (ls : SemLeafSpec) (L : ArrLayout) (dst : Located) (sel : String)
    (src0 src1 : Located) (f : List AVal → ZMod (2 ^ 64)) (hf : LeafAbs ls "select" f)
    (hd : dst.locSrc = .TU64) (hdk : arrKeyB L dst.locVar = false)
    (h0 : argOkB L src0.locVar = true) (h1 : argOkB L src1.locVar = true)
    (harr : ((layoutSize L sel).isSome || (layoutSize L src0.locVar).isSome ||
      (layoutSize L src1.locVar).isSome) = true) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setVal dst.locVar (f ((locNames [src0, src1]).map (absArg L a))) a)
      (.RSelect dst sel src0 src1) := by
  obtain ⟨dv, dt⟩ := dst
  simp only at hd hdk ⊢
  subst hd
  refine corresL_leafWord ls L _ "select" dv _ f hf hdk
    (by simp [locNames, h0, h1]) (fun env a hSR => ?_)
  refine semScalarL_rSelect_leaf ls ⟨dv, .TU64⟩ sel src0 src1 env (fun s x c _ hs hx hc => ?_)
  simp only [Bool.or_eq_true] at harr
  rcases harr with (h | h) | h
  · exact srwordL_layout_not_word hSR h s hs
  · exact srwordL_layout_not_word hSR h x hx
  · exact srwordL_layout_not_word hSR h c hc

/-- **The `"arrLoad:idx"` leaf rule.** A literal-index read into an unreserved `u64` word
    from a source that is not a `TArr _ .TU64` array held in the layout (a byte, `u32` or
    field-element array, for instance) takes the leaf arm of `semScalarL`, and abstracts
    to `dst := f [src]` for an abstract leaf `f` sound for the oracle at `"arrLoad:idx"`. -/
theorem corresL_arrLoadLitLeaf (ls : SemLeafSpec) (L : ArrLayout) (dst src : Located)
    (idx : Nat) (f : List AVal → ZMod (2 ^ 64)) (hf : LeafAbs ls ("arrLoad:" ++ toString idx) f)
    (hd : dst.locSrc = .TU64) (hdk : arrKeyB L dst.locVar = false)
    (hs : argOkB L src.locVar = true)
    (hnw : isU64ArrB src.locSrc = false ∨ layoutSize L src.locVar = none) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setVal dst.locVar (f ((locNames [src]).map (absArg L a))) a)
      (.RArrLoadLit dst src idx) := by
  obtain ⟨dv, dt⟩ := dst
  simp only at hd hdk ⊢
  subst hd
  refine corresL_leafWord ls L _ _ dv _ f hf hdk (by simp [locNames, hs])
    (fun env a hSR => ?_)
  refine semScalarL_rArrLoadLit_leaf ls ⟨dv, .TU64⟩ src idx env (fun k n arr _ hsrc hsv => ?_)
  rcases hnw with h | h
  · rw [hsrc] at h; exact absurd h (by simp [isU64ArrB])
  · unfold argOkB at hs
    simp only [h, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hs
    obtain ⟨w, hw, _⟩ := hSR.1 _ (notTmpB_sound _ hs.1) hs.2
    rw [hw] at hsv
    simp at hsv

/-- An optional abstract leaf per leaf name. -/
abbrev AbsLeaves : Type := String → Option (List AVal → ZMod (2 ^ 64))

/-- No abstract leaf: every leaf call keeps the unsupported guard. -/
def noLeaves : AbsLeaves := fun _ => none

/-- Every abstract leaf of `lf` is sound for the oracle `ls` at its name. -/
def LeavesSound (ls : SemLeafSpec) (lf : AbsLeaves) : Prop :=
  ∀ name f, lf name = some f → LeafAbs ls name f

theorem leavesSound_noLeaves (ls : SemLeafSpec) : LeavesSound ls noLeaves :=
  fun _ _ h => by cases h

/-- The oracle realising a family of abstract leaves on `u64` destinations: at `.sword 64`
    it returns the word whose `wEnc` encoding is the abstract value; at every other type
    it returns the default. -/
def leafOfAbs (fs : String → List AVal → ZMod (2 ^ 64)) : SemLeafSpec :=
  fun name retTy vals =>
    match retTy with
    | .sword 64 => (BitVec.ofNat 64 (fs name (vals.map vEnc)).val : BitVec 64)
    | t => CryptoTy.default t

/-- Every abstract leaf is sound for the oracle `leafOfAbs` at its name. -/
theorem leafAbs_leafOfAbs (fs : String → List AVal → ZMod (2 ^ 64)) (name : String) :
    LeafAbs (leafOfAbs fs) name (fs name) := by
  intro vals _
  show wEnc (BitVec.ofNat 64 (fs name (vals.map vEnc)).val) = _
  simp only [wEnc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (ZMod.val_lt _), ZMod.natCast_zmod_val]

/-! ## The total abstraction with abstract leaves -/

/-- The abstraction of `RCall fname dst args`: the abstract leaf `lf fname` on a word
    destination and abstractable arguments; unsupported otherwise. -/
def callAbsL (lf : AbsLeaves) (L : ArrLayout) (fname : String) (dst : Located)
    (args : List Located) : List Guard × (AField → AField) :=
  match lf fname with
  | some f =>
      if dst.locSrc = .TU64 ∧ arrKeyB L dst.locVar = false ∧
          (locNames args).all (argOkB L) = true then
        ([], fun a => setVal dst.locVar (f ((locNames args).map (absArg L a))) a)
      else unsupportedAbs "RCall"
  | none => unsupportedAbs "RCall"

/-- The abstraction of `RSelect dst sel src0 src1`: the abstract leaf `lf "select"` when
    one of the selector and sources is a layout array, `selectAbs` otherwise. -/
def selectAbsL (lf : AbsLeaves) (L : ArrLayout) (dst : Located) (sel : String)
    (src0 src1 : Located) : List Guard × (AField → AField) :=
  match lf "select" with
  | some f =>
      if dst.locSrc = .TU64 ∧ arrKeyB L dst.locVar = false ∧ argOkB L src0.locVar = true ∧
          argOkB L src1.locVar = true ∧
          ((layoutSize L sel).isSome || (layoutSize L src0.locVar).isSome ||
            (layoutSize L src1.locVar).isSome) = true then
        ([], fun a => setVal dst.locVar (f ((locNames [src0, src1]).map (absArg L a))) a)
      else selectAbs L dst sel src0 src1
  | none => selectAbs L dst sel src0 src1

/-- The abstraction of `RArrLoadLit dst src idx`: the abstract leaf `lf "arrLoad:idx"`
    when `src` is not a `TArr _ .TU64` array held in the layout, `arrLoadLitAbs`
    otherwise. -/
def arrLoadLitAbsL (lf : AbsLeaves) (L : ArrLayout) (dst src : Located) (idx : Nat) :
    List Guard × (AField → AField) :=
  match lf ("arrLoad:" ++ toString idx) with
  | some f =>
      if dst.locSrc = .TU64 ∧ arrKeyB L dst.locVar = false ∧ argOkB L src.locVar = true ∧
          (isU64ArrB src.locSrc = false ∨ layoutSize L src.locVar = none) then
        ([], fun a => setVal dst.locVar (f ((locNames [src]).map (absArg L a))) a)
      else arrLoadLitAbs L dst src idx
  | none => arrLoadLitAbs L dst src idx

/-- The total abstraction over a layout with abstract leaves `lf`: `ascendGL` with the
    `RCall`, `RSelect` and `RArrLoadLit` arms consulting `lf`. -/
def ascendGLL (lf : AbsLeaves) (L : ArrLayout) (fuel : Nat) :
    LowCT → List Guard × (AField → AField)
  | .RSkip => ([], id)
  | .RBlock body => ascendGLL lf L fuel body
  | .RSeq c₁ c₂ =>
      ((ascendGLL lf L fuel c₁).1 ++
          (ascendGLL lf L fuel c₂).1.map (Guard.after (ascendGLL lf L fuel c₁).2),
        fun a => (ascendGLL lf L fuel c₂).2 ((ascendGLL lf L fuel c₁).2 a))
  | .RScalarSet x n => if arrKeyB L x then unsupportedAbs "RScalarSet" else ([], setLit x n)
  | .RScalarSetExpr x e => ascendExprL L x e
  | .RAssert label => ([Guard.assert label], id)
  | .RLetU64Zero x body =>
      if arrKeyB L x then unsupportedAbs "RLetU64Zero"
      else if loopFree body then
        ((ascendGLL lf L fuel body).1.map (Guard.after (setLit x 0)),
          fun a => (ascendGLL lf L fuel body).2 (setLit x 0 a))
      else unsupportedAbs "RLetU64Zero"
  | .RIfNz name thenBr elseBr => ascendIf L name thenBr elseBr (ascendGLL lf L fuel thenBr)
  | .RWhileNz name body =>
      if arrKeyB L name then unsupportedAbs "RWhileNz"
      else if notTmpB name then
        (Guard.loopHalts name fuel (ascendGLL lf L fuel body).2 ::
            (ascendGLL lf L fuel body).1.map
              (Guard.loopBody name fuel (ascendGLL lf L fuel body).2),
          awhile (nzB name) (ascendGLL lf L fuel body).2 fuel)
      else unsupportedAbs "RWhileNz"
  | .RFor x N body =>
      if arrKeyB L x then unsupportedAbs "RFor"
      else
        ((ascendGLL lf L fuel body).1.map (Guard.everyTrip x N (ascendGLL lf L fuel body).2),
          forFold (setLit x) (ascendGLL lf L fuel body).2 N)
  | .RArrLoad dst src idxVar => arrLoadAbs L dst src idxVar
  | .RArrStore arr idxVar src => arrStoreAbs L arr idxVar src
  | .RLimbStore loc idx v => limbStoreAbs L loc idx v
  | .RLetZero _ _ _ => unsupportedAbs "RLetZero"
  | .RCall fname dst args => callAbsL lf L fname dst args
  | .RCallSwap _ _ _ _ => unsupportedAbs "RCallSwap"
  | .RCloneCall _ _ _ _ _ _ => unsupportedAbs "RCloneCall"
  | .RCallN _ _ _ => unsupportedAbs "RCallN"
  | .RSelect dst sel src0 src1 => selectAbsL lf L dst sel src0 src1
  | .RLimbStoreExpr _ _ _ => unsupportedAbs "RLimbStoreExpr"
  | .RFnDef _ _ _ _ _ => unsupportedAbs "RFnDef"
  | .RFnCall _ _ _ => unsupportedAbs "RFnCall"
  | .RTupleLoad _ _ _ => unsupportedAbs "RTupleLoad"
  | .RArrStoreLit arr idx src => arrStoreLitAbs L arr idx src
  | .RArrLoadLit dst src idx => arrLoadLitAbsL lf L dst src idx
  | .RCallDstThreaded _ _ _ => unsupportedAbs "RCallDstThreaded"
  | .RForRuntime _ _ _ => unsupportedAbs "RForRuntime"

/-- Without abstract leaves `ascendGLL` is `ascendGL`. -/
theorem ascendGLL_noLeaves (L : ArrLayout) (fuel : Nat) :
    ∀ c : LowCT, ascendGLL noLeaves L fuel c = ascendGL L fuel c := by
  intro c
  induction c with
  | RSeq c₁ c₂ ih₁ ih₂ => simp only [ascendGLL, ascendGL, ih₁, ih₂]
  | RBlock body ih => simp only [ascendGLL, ascendGL, ih]
  | RLetU64Zero x body ih => simp only [ascendGLL, ascendGL, ih]
  | RIfNz name thenBr elseBr ihT _ => simp only [ascendGLL, ascendGL, ihT]
  | RWhileNz name body ih => simp only [ascendGLL, ascendGL, ih]
  | RFor x N body ih => simp only [ascendGLL, ascendGL, ih]
  | _ => rfl

/-! ## Soundness -/

theorem corresUL_arrLoadAbs (ls : SemLeafSpec) (L : ArrLayout) (fuel : Nat)
    (dst src : Located) (idxVar : String) :
    CorresUL ls fuel (SRwordL L) (guardsHold (arrLoadAbs L dst src idxVar).1)
      (arrLoadAbs L dst src idxVar).2 (.RArrLoad dst src idxVar) := by
  unfold arrLoadAbs
  rcases hs : layoutSize L src.locVar with _ | _ | m
  · exact corresUL_unsupported _ _ _ _ _
  · exact corresUL_unsupported _ _ _ _ _
  · dsimp only
    by_cases hc : dst.locSrc = .TU64 ∧ arrKeyB L dst.locVar = false ∧
        notTmpB idxVar = true ∧ arrKeyB L idxVar = false
    · rw [if_pos hc]
      obtain ⟨hdst, hdk, hit, hik⟩ := hc
      exact corresUL_weaken _ _
        (corresUL_of_corresL _ _ rfl
          (corresL_arrLoad_oracle ls L dst src idxVar m hdst (layoutSize_mem hs) hdk
            (notTmpB_sound _ hit) hik))
        (fun _ _ => trivial)
    · rw [if_neg hc]
      exact corresUL_unsupported _ _ _ _ _

theorem corresUL_arrStoreAbs (ls : SemLeafSpec) (L : ArrLayout) (fuel : Nat)
    (arr : Located) (idxVar : String) (src : Located) :
    CorresUL ls fuel (SRwordL L) (guardsHold (arrStoreAbs L arr idxVar src).1)
      (arrStoreAbs L arr idxVar src).2 (.RArrStore arr idxVar src) := by
  unfold arrStoreAbs
  rcases hs : layoutSize L arr.locVar with _ | _ | m
  · exact corresUL_unsupported _ _ _ _ _
  · exact corresUL_unsupported _ _ _ _ _
  · dsimp only
    by_cases hc : encodeTy arr.locSrc = .memref (m + 1) ∧ notTmpB idxVar = true ∧
        arrKeyB L idxVar = false ∧ notTmpB src.locVar = true ∧ arrKeyB L src.locVar = false
    · rw [if_pos hc]
      obtain ⟨harr, hit, hik, hst, hsk⟩ := hc
      exact corresUL_weaken _ _
        (corresUL_of_corresL _ _ rfl
          (corresL_arrStore_oracle ls L arr src idxVar m harr (layoutSize_mem hs)
            (notTmpB_sound _ hit) hik (notTmpB_sound _ hst) hsk))
        (fun _ _ => trivial)
    · rw [if_neg hc]
      exact corresUL_unsupported _ _ _ _ _

theorem corresUL_limbStoreAbs (ls : SemLeafSpec) (L : ArrLayout) (fuel : Nat)
    (loc : Located) (idx : Nat) (v : BitVec 64) :
    CorresUL ls fuel (SRwordL L) (guardsHold (limbStoreAbs L loc idx v).1)
      (limbStoreAbs L loc idx v).2 (.RLimbStore loc idx v) := by
  unfold limbStoreAbs
  rcases hs : layoutSize L loc.locVar with _ | n
  · exact corresUL_unsupported _ _ _ _ _
  · dsimp only
    by_cases hc : idx < n
    · rw [if_pos hc]
      exact corresUL_weaken _ _
        (corresUL_of_corresL _ _ rfl
          (corresL_of_corres_eq _ _
            (corresL_limbStore L loc idx v n (layoutSize_mem hs) hc) (fun _ => rfl)))
        (fun _ _ => trivial)
    · rw [if_neg hc]
      exact corresUL_unsupported _ _ _ _ _

theorem corresUL_arrLoadLitAbs (ls : SemLeafSpec) (L : ArrLayout) (fuel : Nat)
    (dst src : Located) (idx : Nat) :
    CorresUL ls fuel (SRwordL L) (guardsHold (arrLoadLitAbs L dst src idx).1)
      (arrLoadLitAbs L dst src idx).2 (.RArrLoadLit dst src idx) := by
  unfold arrLoadLitAbs
  rcases hs : layoutSize L src.locVar with _ | _ | m
  · exact corresUL_unsupported _ _ _ _ _
  · exact corresUL_unsupported _ _ _ _ _
  · dsimp only
    by_cases hc : dst.locSrc = .TU64 ∧ isU64ArrB src.locSrc = true ∧
        arrKeyB L dst.locVar = false ∧ idx < m + 1 ∧ idx < 2 ^ 64
    · rw [if_pos hc]
      obtain ⟨hdst, hu, hdk, hidx, hlit⟩ := hc
      obtain ⟨k, hsrc⟩ := isU64ArrB_sound hu
      exact corresUL_weaken _ _
        (corresUL_of_corresL _ _ rfl
          (corresL_arrLoadLit_oracle ls L dst src idx k m hdst hsrc (layoutSize_mem hs) hidx
            hlit hdk))
        (fun _ _ => trivial)
    · rw [if_neg hc]
      exact corresUL_unsupported _ _ _ _ _

theorem corresUL_arrStoreLitAbs (ls : SemLeafSpec) (L : ArrLayout) (fuel : Nat)
    (arr : Located) (idx : Nat) (src : Located) :
    CorresUL ls fuel (SRwordL L) (guardsHold (arrStoreLitAbs L arr idx src).1)
      (arrStoreLitAbs L arr idx src).2 (.RArrStoreLit arr idx src) := by
  unfold arrStoreLitAbs
  rcases hs : layoutSize L arr.locVar with _ | _ | m
  · exact corresUL_unsupported _ _ _ _ _
  · exact corresUL_unsupported _ _ _ _ _
  · dsimp only
    by_cases hc : isU64ArrB arr.locSrc = true ∧ idx < m + 1 ∧ idx < 2 ^ 64 ∧
        notTmpB src.locVar = true ∧ arrKeyB L src.locVar = false
    · rw [if_pos hc]
      obtain ⟨hu, hidx, hlit, hst, hsk⟩ := hc
      obtain ⟨k, harr⟩ := isU64ArrB_sound hu
      exact corresUL_weaken _ _
        (corresUL_of_corresL _ _ rfl
          (corresL_arrStoreLit_oracle ls L arr src idx k m harr (layoutSize_mem hs) hidx hlit
            (notTmpB_sound _ hst) hsk))
        (fun _ _ => trivial)
    · rw [if_neg hc]
      exact corresUL_unsupported _ _ _ _ _

theorem corresUL_selectAbs (ls : SemLeafSpec) (L : ArrLayout) (fuel : Nat) (dst : Located)
    (sel : String) (src0 src1 : Located) :
    CorresUL ls fuel (SRwordL L) (guardsHold (selectAbs L dst sel src0 src1).1)
      (selectAbs L dst sel src0 src1).2 (.RSelect dst sel src0 src1) := by
  unfold selectAbs
  by_cases hc : dst.locSrc = .TU64 ∧ arrKeyB L dst.locVar = false ∧ notTmpB sel = true ∧
      arrKeyB L sel = false ∧ notTmpB src0.locVar = true ∧ arrKeyB L src0.locVar = false ∧
      notTmpB src1.locVar = true ∧ arrKeyB L src1.locVar = false
  · rw [if_pos hc]
    obtain ⟨hdst, hdk, hst, hsk, h0t, h0k, h1t, h1k⟩ := hc
    exact corresUL_weaken _ _
      (corresUL_of_corresL _ _ rfl
        (corresL_select_oracle ls L dst sel src0 src1 hdst hdk (notTmpB_sound _ hst) hsk
          (notTmpB_sound _ h0t) h0k (notTmpB_sound _ h1t) h1k))
      (fun _ _ => trivial)
  · rw [if_neg hc]
    exact corresUL_unsupported _ _ _ _ _

/-- Soundness of the total abstraction with abstract leaves: under its guards and sound
    abstract leaves, `ascendGLL lf L fuel c` is a `CorresUL ls fuel (SRwordL L)`
    correspondent of `c`. -/
theorem ascendGLL_sound (ls : SemLeafSpec) (lf : AbsLeaves) (hlf : LeavesSound ls lf)
    (L : ArrLayout) (fuel : Nat) :
    ∀ c : LowCT,
      CorresUL ls fuel (SRwordL L) (guardsHold (ascendGLL lf L fuel c).1)
        (ascendGLL lf L fuel c).2 c := by
  intro c
  induction c
  case RSkip =>
    show CorresUL ls fuel (SRwordL L) (guardsHold []) id .RSkip
    exact corresUL_weaken _ _
      (corresUL_of_corresL _ _ rfl (corresL_of_corres_eq _ _ (corres_skip _) (fun _ => rfl)))
      (fun _ _ => trivial)
  case RBlock body ih =>
    show CorresUL ls fuel (SRwordL L) (guardsHold (ascendGLL lf L fuel body).1)
      (ascendGLL lf L fuel body).2 (.RBlock body)
    exact corresUL_block _ _ ih
  case RSeq c₁ c₂ ih₁ ih₂ =>
    show CorresUL ls fuel (SRwordL L)
      (guardsHold ((ascendGLL lf L fuel c₁).1 ++
        (ascendGLL lf L fuel c₂).1.map (Guard.after (ascendGLL lf L fuel c₁).2)))
      (fun a => (ascendGLL lf L fuel c₂).2 ((ascendGLL lf L fuel c₁).2 a)) (.RSeq c₁ c₂)
    refine corresUL_seq _ _
      (corresUL_weaken _ _ ih₁ (fun a h => (guardsHold_append.mp h).1)) ih₂ (fun a h => ?_)
    exact guardsHold_map_after.mp (guardsHold_append.mp h).2
  case RScalarSet x n =>
    simp only [ascendGLL]
    rcases hk : arrKeyB L x
    · simp only [Bool.false_eq_true, if_false]
      exact corresUL_weaken _ _
        (corresUL_of_corresL _ _ rfl
          (corresL_of_corres_eq _ _ (corresL_setScalar L x n hk) (fun _ => rfl)))
        (fun _ _ => trivial)
    · simp only [if_true]
      exact corresUL_unsupported _ _ _ _ _
  case RScalarSetExpr x e =>
    have h := ascendGL_sound L fuel (.RScalarSetExpr x e)
    intro env a hSR hP
    obtain ⟨env', hstep, hSR'⟩ := h env a hSR hP
    refine ⟨env', ?_, hSR'⟩
    rw [semUL_leaf ls fuel env rfl]
    rw [semU_leaf fuel env rfl] at hstep
    exact hstep
  case RAssert label =>
    show CorresUL ls fuel (SRwordL L) (guardsHold [Guard.assert label]) id (.RAssert label)
    exact corresUL_weaken _ _
      (corresUL_of_corresL _ _ rfl
        (corresL_of_corres_eq _ _ (corres_assert _ label) (fun _ => rfl)))
      (fun _ _ => trivial)
  case RLetU64Zero x body ih =>
    simp only [ascendGLL]
    rcases hk : arrKeyB L x
    · rcases hlfr : loopFree body
      · simp only [Bool.false_eq_true, if_false]
        exact corresUL_unsupported _ _ _ _ _
      · simp only [Bool.false_eq_true, if_false, if_true]
        intro env a hSR hP
        obtain ⟨env', hstep, hSRf⟩ :=
          ih _ _ (srwordL_upd_lit x 0 hk hSR) (guardsHold_map_after.mp hP)
        refine ⟨env', ?_, hSRf⟩
        show semScalarL ls body (env.upd x (t := .sword 64) (0 : BitVec 64)) = some env'
        rw [← semUL_eq_semScalarL_of_loopFree ls fuel body hlfr]
        exact hstep
    · simp only [if_true]
      exact corresUL_unsupported _ _ _ _ _
  case RIfNz name thenBr elseBr ihT _ =>
    simp only [ascendGLL]
    unfold ascendIf
    rcases hsk : isSkipB elseBr
    · simp only [Bool.false_eq_true, if_false]
      have hne : elseBr ≠ .RSkip := fun h => by
        rw [h] at hsk; exact Bool.false_ne_true hsk.symm
      rcases ht : asSingleScalarSet thenBr with _ | ⟨nv, tv⟩
      · exact corresUL_unsupported _ _ _ _ _
      · rcases he : asSingleScalarSet elseBr with _ | ⟨nv', ev⟩
        · exact corresUL_unsupported _ _ _ _ _
        · dsimp only
          by_cases hc : nv = nv' ∧ notTmpB name = true ∧ arrKeyB L name = false ∧
              arrKeyB L nv = false
          · rw [if_pos hc]
            obtain ⟨hnv, hnt, hk, hkv⟩ := hc
            subst hnv
            obtain rfl := asSingleScalarSet_some ht
            obtain rfl := asSingleScalarSet_some he
            exact corresUL_weaken _ _
              (corresUL_of_corresL _ _ (isSeqLike_rIfNz_of_ne _ _ _ hne)
                (corresL_of_corres_eq _ _
                  (corresL_if L name nv tv ev (notTmpB_sound name hnt) hk hkv)
                  (fun _ => rfl)))
              (fun _ _ => trivial)
          · rw [if_neg hc]
            exact corresUL_unsupported _ _ _ _ _
    · obtain rfl := (isSkipB_iff elseBr).mp hsk
      simp only [if_true]
      rcases hk : arrKeyB L name
      · simp only [Bool.false_eq_true, if_false]
        rcases hnt : notTmpB name
        · simp only [Bool.false_eq_true, if_false]
          exact corresUL_unsupported _ _ _ _ _
        · simp only [if_true]
          exact corresUL_weaken _ _
            (corresUL_cond _ _ (nzB name)
              (fun env a hSR => guardNz_srwordL (notTmpB_sound name hnt) hk hSR) ihT)
            (fun a h => guardsHold_map_whenNz.mp h)
      · simp only [if_true]
        exact corresUL_unsupported _ _ _ _ _
  case RWhileNz name body ih =>
    simp only [ascendGLL]
    rcases hk : arrKeyB L name
    · rcases hnt : notTmpB name
      · simp only [Bool.false_eq_true, if_false]
        exact corresUL_unsupported _ _ _ _ _
      · simp only [Bool.false_eq_true, if_false, if_true]
        refine corresUL_weaken _ _
          (corresUL_whileNz _ _ (nzB name)
            (fun env a hSR => guardNz_srwordL (notTmpB_sound name hnt) hk hSR) ih)
          (fun a h => ?_)
        refine ⟨h _ (List.mem_cons.mpr (Or.inl rfl)), guardsHold_map_loopBody.mp ?_⟩
        exact fun g hg => h g (List.mem_cons.mpr (Or.inr hg))
    · simp only [if_true]
      exact corresUL_unsupported _ _ _ _ _
  case RFor x N body ih =>
    simp only [ascendGLL]
    rcases hk : arrKeyB L x
    · simp only [Bool.false_eq_true, if_false]
      exact corresUL_weaken _ _
        (corresUL_for_trips _ _ (setLit x) (fun env a n hSR => srwordL_upd_lit x n hk hSR) ih N)
        (fun a h => guardsHold_map_everyTrip.mp h)
    · simp only [if_true]
      exact corresUL_unsupported _ _ _ _ _
  case RArrLoad dst src idxVar => exact corresUL_arrLoadAbs ls L fuel dst src idxVar
  case RArrStore arr idxVar src => exact corresUL_arrStoreAbs ls L fuel arr idxVar src
  case RLimbStore loc idx v => exact corresUL_limbStoreAbs ls L fuel loc idx v
  case RArrStoreLit arr idx src => exact corresUL_arrStoreLitAbs ls L fuel arr idx src
  case RCall fname dst args =>
    show CorresUL ls fuel (SRwordL L) (guardsHold (callAbsL lf L fname dst args).1)
      (callAbsL lf L fname dst args).2 (.RCall fname dst args)
    unfold callAbsL
    rcases hl : lf fname with _ | f
    · exact corresUL_unsupported _ _ _ _ _
    · dsimp only
      by_cases hc : dst.locSrc = .TU64 ∧ arrKeyB L dst.locVar = false ∧
          (locNames args).all (argOkB L) = true
      · rw [if_pos hc]
        obtain ⟨hd, hdk, hall⟩ := hc
        exact corresUL_weaken _ _
          (corresUL_of_corresL _ _ rfl
            (corresL_call ls L fname dst args f (hlf _ _ hl) hd hdk
              (fun x hx => List.all_eq_true.mp hall x hx)))
          (fun _ _ => trivial)
      · rw [if_neg hc]
        exact corresUL_unsupported _ _ _ _ _
  case RSelect dst sel src0 src1 =>
    show CorresUL ls fuel (SRwordL L) (guardsHold (selectAbsL lf L dst sel src0 src1).1)
      (selectAbsL lf L dst sel src0 src1).2 (.RSelect dst sel src0 src1)
    unfold selectAbsL
    rcases hl : lf "select" with _ | f
    · exact corresUL_selectAbs ls L fuel dst sel src0 src1
    · dsimp only
      by_cases hc : dst.locSrc = .TU64 ∧ arrKeyB L dst.locVar = false ∧
          argOkB L src0.locVar = true ∧ argOkB L src1.locVar = true ∧
          ((layoutSize L sel).isSome || (layoutSize L src0.locVar).isSome ||
            (layoutSize L src1.locVar).isSome) = true
      · rw [if_pos hc]
        obtain ⟨hd, hdk, h0, h1, harr⟩ := hc
        exact corresUL_weaken _ _
          (corresUL_of_corresL _ _ rfl
            (corresL_selectLeaf ls L dst sel src0 src1 f (hlf _ _ hl) hd hdk h0 h1 harr))
          (fun _ _ => trivial)
      · rw [if_neg hc]
        exact corresUL_selectAbs ls L fuel dst sel src0 src1
  case RArrLoadLit dst src idx =>
    show CorresUL ls fuel (SRwordL L) (guardsHold (arrLoadLitAbsL lf L dst src idx).1)
      (arrLoadLitAbsL lf L dst src idx).2 (.RArrLoadLit dst src idx)
    unfold arrLoadLitAbsL
    rcases hl : lf ("arrLoad:" ++ toString idx) with _ | f
    · exact corresUL_arrLoadLitAbs ls L fuel dst src idx
    · dsimp only
      by_cases hc : dst.locSrc = .TU64 ∧ arrKeyB L dst.locVar = false ∧
          argOkB L src.locVar = true ∧
          (isU64ArrB src.locSrc = false ∨ layoutSize L src.locVar = none)
      · rw [if_pos hc]
        obtain ⟨hd, hdk, hs, hnw⟩ := hc
        exact corresUL_weaken _ _
          (corresUL_of_corresL _ _ rfl
            (corresL_arrLoadLitLeaf ls L dst src idx f (hlf _ _ hl) hd hdk hs hnw))
          (fun _ _ => trivial)
      · rw [if_neg hc]
        exact corresUL_arrLoadLitAbs ls L fuel dst src idx
  all_goals exact corresUL_unsupported _ _ _ _ _

/-- `ascendGL_sound` is the instance of `ascendGLL_sound` at the default oracle without
    abstract leaves. -/
theorem ascendGL_sound_of_ascendGLL (L : ArrLayout) (fuel : Nat) (c : LowCT) :
    CorresU fuel (SRwordL L) (guardsHold (ascendGL L fuel c).1) (ascendGL L fuel c).2 c := by
  have h := ascendGLL_sound defaultLeaf noLeaves (leavesSound_noLeaves _) L fuel c
  rw [ascendGLL_noLeaves] at h
  exact corresUL_default_iff.mp h

/-- On a loop-free command the abstraction with abstract leaves is a `CorresL`
    correspondent. -/
theorem ascendGLL_sound_scalar (ls : SemLeafSpec) (lf : AbsLeaves) (hlf : LeavesSound ls lf)
    (L : ArrLayout) (fuel : Nat) (c : LowCT) (hlfr : loopFree c = true) :
    CorresL ls (SRwordL L) (guardsHold (ascendGLL lf L fuel c).1) (ascendGLL lf L fuel c).2 c := by
  intro env a hSR hP
  obtain ⟨env', hstep, hSR'⟩ := ascendGLL_sound ls lf hlf L fuel c env a hSR hP
  refine ⟨env', ?_, hSR'⟩
  rw [← semUL_eq_semScalarL_of_loopFree ls fuel c hlfr]
  exact hstep

/-! ## A kernel with leaf calls

`leafK` is the literal-index read `y := B[0]` from an array `B` of type `TBytes 8`, which
is not a `u64` word array, so the front emits the opaque leaf `extCall "arrLoad:0"`,
followed by the select `r := select(s, B, y)` with an array source, which the front
emits as the opaque leaf `extCall "select"` over `B` and `y`. `TBytes 8` is encoded as
`.memref 1`. The abstract leaf `leafKAbs` is the same function at every name and
distinguishes the two nodes by the number of arguments: on one argument it is element
`0` of that argument, on two it is element `0` of the first plus the second. Over the
layout `[("B", 1)]` at the oracle `leafOfAbs leafKAbs` the abstraction carries no guard
(`leafK_guards`), `leafK_corres` refines the kernel to `leafKProg`, and `leafK_value`
evaluates `leafKProg` on a store related to a concrete environment (`leafK_srwordL`). -/

/-- The layout with one array `B` of one `u64` element. -/
def leafLayout : ArrLayout := [("B", 1)]

/-- Element `0` of an abstract array argument, `0` on any other argument. -/
def avalElem0 : AVal → ZMod (2 ^ 64)
  | .arr (_ + 1) v => v 0
  | _ => 0

/-- The abstract word of an abstract word argument, `0` on any other argument. -/
def avalWord : AVal → ZMod (2 ^ 64)
  | .word z => z
  | _ => 0

/-- The abstract leaf of `leafK`, the same at every name: on one argument, element `0`
    of that argument (the `"arrLoad:0"` read); on two, element `0` of the first plus the
    word of the second (the `"select"` node). -/
def leafKAbs (_name : String) (args : List AVal) : ZMod (2 ^ 64) :=
  match args with
  | [x] => avalElem0 x
  | [x, y] => avalElem0 x + avalWord y
  | _ => 0

/-- The abstract leaf family of `leafK`: `leafKAbs` at every name. -/
def leafKLeaves : AbsLeaves := fun name => some (leafKAbs name)

theorem leavesSound_leafK : LeavesSound (leafOfAbs leafKAbs) leafKLeaves := by
  intro name f h
  cases h
  exact leafAbs_leafOfAbs leafKAbs name

/-- `y := B[0]; r := select(s, B, y)`. -/
def leafK : LowCT :=
  .RSeq (.RArrLoadLit ⟨"y", .TU64⟩ ⟨"B", .TBytes 8⟩ 0)
    (.RSelect ⟨"r", .TU64⟩ "s" ⟨"B", .TBytes 8⟩ ⟨"y", .TU64⟩)

/-- The abstract program of `leafK`. -/
def leafKProg (a : AField) : AField :=
  let a₁ := setVal "y" (a (elemKey "B" 0)) a
  setVal "r" (a₁ (elemKey "B" 0) + a₁ "y") a₁

/-- The abstraction of `leafK` carries no guard. -/
theorem leafK_guards (fuel : Nat) : (ascendGLL leafKLeaves leafLayout fuel leafK).1 = [] := by
  rfl

/-- The abstraction of `leafK` is `leafKProg`. -/
theorem leafK_prog (fuel : Nat) :
    (ascendGLL leafKLeaves leafLayout fuel leafK).2 = leafKProg := by
  rfl

/-- `leafK` refines `leafKProg` over `SRwordL [("B", 1)]` at the oracle
    `leafOfAbs leafKAbs`, on every store. -/
theorem leafK_corres :
    CorresL (leafOfAbs leafKAbs) (SRwordL leafLayout) (fun _ => True) leafKProg leafK := by
  have h := ascendGLL_sound_scalar _ _ leavesSound_leafK leafLayout 0 leafK rfl
  rw [leafK_guards, leafK_prog] at h
  intro env a hSR _
  exact h env a hSR (guardsHold_nil a)

/-- A store binding `B` to the one-element array holding `7` and every other name to the
    zero word. -/
def leafEnv : SEnvScalar :=
  fun s => if s = "B" then some ⟨.memref 1, fun _ => (7 : BitVec 64)⟩
    else some ⟨.sword 64, (0 : BitVec 64)⟩

/-- The abstract store with element `0` of `B` equal to `7` and every other name `0`. -/
def leafStore : AField := fun s => if s = elemKey "B" 0 then 7 else 0

/-- The relation of `leafK_corres` holds between `leafEnv` and `leafStore`. -/
theorem leafK_srwordL : SRwordL leafLayout leafEnv leafStore := by
  refine ⟨fun x _ hx => ?_, fun p hp => ?_⟩
  · have hxB : x ≠ "B" := by rintro rfl; exact absurd hx (by decide)
    have hxk : x ≠ elemKey "B" 0 := by
      rintro rfl; exact absurd hx (by decide)
    exact ⟨0, by simp [leafEnv, hxB], by simp [wEnc, leafStore, hxk]⟩
  · simp only [leafLayout, List.mem_singleton] at hp
    subst hp
    refine ⟨notTmpB_sound "B" rfl, fun _ => 7, by simp [leafEnv], fun j => ?_⟩
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [wEnc, leafStore]

/-- On `leafStore` the abstract program sets `r` to `7 + 7`. -/
theorem leafK_value : leafKProg leafStore "r" = 14 := by
  decide

end CatCrypt.Crypto.SecureCompilation.Ascent
