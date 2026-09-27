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

An abstract array leaf `g : List AVal → Nat → ZMod 2^64` is sound at a name
(`LeafAbsArr ls name g`) when cell `j` of the oracle's `.memref n` result, encoded, is
`g` of the encoded arguments at `j`; `AbsArrLeaves` gives an optional abstract array leaf
per name and `ArrLeavesSound ls lfa` says each is sound. Its abstract write is
`setCells s n (g args)`, the write of cells `0, …, n - 1` of the layout array `s`;
`cellLeaf k f` is the array leaf writing cell `k` to `f` of the arguments and keeping the
other cells, and `setCells_cellLeaf` identifies its write with `setVal (elemKey s k)`.

## Leaf steps

Every leaf node binds one destination, or a sequence of destinations, to the oracle.
`leafDstStep ls name dst names` is the binding of `dst` at its encoded type to the
oracle at `name` on the argument names `names`; `leafDstAbs ctor lf lfa L name dst names`
abstracts it to the word leaf `lf name` when `dst` is an unreserved `u64` word and to the
array leaf `lfa name` when `dst` is a layout array whose type encodes to its layout
length, and to the unsupported guard at `ctor` otherwise. `AbsStep SR step p` says the
abstraction `p` is sound for the environment transformer `step`, `seqAbs` composes two
abstractions as the `RSeq` arm does, and `corresL_of_absStep` turns a step abstraction
into a `CorresL` statement.

`ascendGLL lf lfa L fuel` is `ascendGL L fuel` with these arms consulting `lf` and `lfa`:

* `RCall fname dst args`, `RCallDstThreaded fname dst args` and `RTupleLoad dst src idx`
  are `leafDstAbs` at `fname`, at `fname` on `dst :: args`, and at `"tupleLoad:idx"` on
  `[src]`;
* `RCallSwap fname dest1 dest2 args` is the sequence of the two `leafDstAbs` bindings at
  `fname`, and `RCloneCall cv _ oldDest innerF newDest args` the `leafDstAbs` binding of
  `cv`, typed as `oldDest`, at `"clone"` on `[oldDest]` followed by the binding of
  `newDest` at `innerF`, the layout giving `cv` and `oldDest` the same length if any;
* `RCallN fname dests args` is the fold `callNAbsL` of the `leafDstAbs` bindings of the
  destinations at `callNLeafName fname i`, when a leaf at the name of output `0` is given;
* `RSelect dst sel src0 src1` is `leafDstAbs` at `"select"` on `sel, src0, src1` when
  `dst` is a layout array and an array leaf at `"select"` is given, and otherwise goes
  through `corresL_selectLeaf` when one of `sel`, `src0`, `src1` is a layout array and a
  word leaf at `"select"` is given; the leaf receives `sel`, `src0` and `src1`, as the
  front's `extCall` does;
* `RArrStoreLit arr idx src` is `leafDstAbs` at `"arrStore:idx"` on `[arr, src]` when an
  array leaf at that name is given and the node is not a word write to a `TArr _ .TU64`
  array;
* `RArrLoadLit dst src idx` goes through `corresL_arrLoadLitLeaf` at the name
  `"arrLoad:idx"` when `src` is not a `TArr _ .TU64` array held in the layout.

Every other arm is the arm of `ascendGL`, and `ascendGLL noLeaves noArrLeaves L fuel` is
`ascendGL L fuel` (`ascendGLL_noLeaves`).

## Main definitions

* `CorresL`, `CorresUL` — `Corres` and `CorresU` over `semScalarL ls` and `semUL ls`
* `AVal`, `vEnc`, `absArg`, `argOkB` — abstraction of leaf arguments
* `LeafAbs`, `AbsLeaves`, `LeavesSound`, `noLeaves`, `leafOfAbs` — abstract word leaves
* `setCells`, `LeafAbsArr`, `AbsArrLeaves`, `ArrLeavesSound`, `noArrLeaves`, `cellLeaf`,
  `leafOfAbsArr` — abstract array leaves
* `leafDstStep`, `AbsStep`, `seqAbs`, `leafDstAbs` — leaf steps and their abstraction
* `ascendGLL` — the total abstraction with abstract leaves

## Main results

* `corresL_default_iff`, `corresUL_default_iff` — at `defaultLeaf` the relations are
  `Corres` and `CorresU`
* `corresL_leafWord`, `corresL_leafArr` — the generic word and array leaf rules
* `corresL_call`, `corresL_callArr`, `corresL_selectLeaf`, `corresL_selectArrLeaf`,
  `corresL_arrLoadLitLeaf`, `corresL_arrStoreLitLeaf`, `corresL_arrStoreLitCell`,
  `corresL_callDstThreaded`, `corresL_callDstThreadedArr`, `corresL_tupleLoadLeaf`,
  `corresL_tupleLoadArrLeaf`, `corresL_callSwap`, `corresL_cloneCall`, `corresL_callN` —
  the leaf rules per form
* `absStep_leafDst`, `absStep_callN`, `leafDstAbs_cases` — the step abstractions
* `ascendGLL_sound` — soundness at `semUL ls fuel` under `LeavesSound ls lf` and
  `ArrLeavesSound ls lfa`
* `ascendGLL_noLeaves`, `ascendGL_sound_of_ascendGLL` — the specialisation to
  `ascendGL_sound`
* `leafAbs_leafOfAbs`, `leafAbs_leafOfAbsArr`, `leafAbsArr_leafOfAbsArr` — every family of
  abstract leaves is sound for the oracle `leafOfAbs`, or `leafOfAbsArr`
* `leafK_corres` — a kernel with an `"arrLoad:0"` read of a `TBytes 8` array and a
  `"select"` over it, refined to its abstract program
* `leafK2_corres` — a kernel with an `"arrStore:3"` write to a `TBytes 8` array, a
  `"tupleLoad:1"` read, an `RCallN`, an `RCallDstThreaded`, an `RCallSwap` and an
  `RCloneCall`, refined to its abstract program
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms (inlineArithRecipe)
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

/-- A `Corres` result transfers to `CorresL ls` on a command on which `semScalarL ls` is
    `semScalar` at every environment the state relation admits. -/
theorem corresL_of_corres_eqOn {P : AState → Prop} {fa : AState → AState} {c : LowCT}
    (h : Corres SR P fa c)
    (heq : ∀ env a, SR env a → semScalarL ls c env = semScalar c env) :
    CorresL ls SR P fa c := by
  intro env a hSR hP
  obtain ⟨env', hs, hSR'⟩ := h env a hSR hP
  exact ⟨env', (heq env a hSR).trans hs, hSR'⟩

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
  | ⟨.memrefW 64 n, av⟩ => .arr n (fun j => wEnc (av j))
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
    abstracts to `dst := f [sel, src0, src1]` for an abstract leaf `f` sound for the
    oracle at `"select"`. -/
theorem corresL_selectLeaf (ls : SemLeafSpec) (L : ArrLayout) (dst : Located) (sel : String)
    (src0 src1 : Located) (f : List AVal → ZMod (2 ^ 64)) (hf : LeafAbs ls "select" f)
    (hd : dst.locSrc = .TU64) (hdk : arrKeyB L dst.locVar = false)
    (hs : argOkB L sel = true)
    (h0 : argOkB L src0.locVar = true) (h1 : argOkB L src1.locVar = true)
    (harr : ((layoutSize L sel).isSome || (layoutSize L src0.locVar).isSome ||
      (layoutSize L src1.locVar).isSome) = true) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setVal dst.locVar (f ((sel :: locNames [src0, src1]).map (absArg L a))) a)
      (.RSelect dst sel src0 src1) := by
  obtain ⟨dv, dt⟩ := dst
  simp only at hd hdk ⊢
  subst hd
  refine corresL_leafWord ls L _ "select" dv _ f hf hdk
    (by simp [locNames, hs, h0, h1]) (fun env a hSR => ?_)
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

/-! ## Abstract leaves writing a layout array -/

/-- The store update writing cells `0, …, n - 1` of the layout array `s` to
    `g 0, …, g (n - 1)`. -/
def setCells (s : String) : Nat → (Nat → ZMod (2 ^ 64)) → AField → AField
  | 0, _, a => a
  | k + 1, g, a => setVal (elemKey s k) (g k) (setCells s k g a)

theorem setCells_ne (s : String) (g : Nat → ZMod (2 ^ 64)) (a : AField) (y : String) :
    ∀ n, (∀ j, j < n → y ≠ elemKey s j) → setCells s n g a y = a y
  | 0, _ => rfl
  | k + 1, h => by
      simp only [setCells, setVal, if_neg (h k (Nat.lt_succ_self k))]
      exact setCells_ne s g a y k (fun j hj => h j (Nat.lt_succ_of_lt hj))

theorem setCells_elemKey (s : String) (g : Nat → ZMod (2 ^ 64)) (a : AField) (j : Nat) :
    ∀ n, j < n → setCells s n g a (elemKey s j) = g j
  | 0, h => absurd h (Nat.not_lt_zero j)
  | k + 1, h => by
      simp only [setCells, setVal]
      by_cases hjk : j = k
      · subst hjk; simp
      · rw [if_neg (fun he => hjk (elemKey_inj he).2)]
        exact setCells_elemKey s g a j k (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h) hjk)

/-- A write of every cell of the layout array `s`, cell `j` encoding `g j`, preserves the
    relation against `setCells s n g`. -/
theorem srwordL_arrWriteAll {L : ArrLayout} {env env' : SEnvScalar} {a : AField} (s : String)
    (n : Nat) (av av' : Fin n → BitVec 64) (g : Nat → ZMod (2 ^ 64))
    (hSR : SRwordL L env a) (hmem : (s, n) ∈ L) (hs : env s = some ⟨.memref n, av⟩)
    (hav' : ∀ j : Fin n, wEnc (av' j) = g j)
    (henv' : ∀ y, env' y = if y = s then some ⟨.memref n, av'⟩ else env y) :
    SRwordL L env' (setCells s n g a) := by
  refine ⟨fun y hy hyk => ?_, fun p hp => ?_⟩
  · have hys : y ≠ s := ne_of_arrKeyB hyk (arrKeyB_name hmem)
    obtain ⟨w, hw, hwe⟩ := hSR.1 y hy hyk
    refine ⟨w, by rw [henv', if_neg hys, hw], ?_⟩
    rw [setCells_ne s g a y n (fun j _ => ne_of_arrKeyB hyk (arrKeyB_elemKey hmem _ _))]
    exact hwe
  · obtain ⟨hnt, bv, hbv, hbvE⟩ := hSR.2 p hp
    refine ⟨hnt, ?_⟩
    obtain ⟨p1, p2⟩ := p
    simp only at hnt hbv hbvE ⊢
    by_cases hps : p1 = s
    · subst hps
      rw [hs] at hbv
      simp only [Option.some.injEq, Sigma.mk.inj_iff, CryptoSSA.CryptoTy.memref.injEq] at hbv
      obtain ⟨rfl, _⟩ := hbv
      refine ⟨av', by rw [henv', if_pos rfl], fun j => ?_⟩
      rw [hav' j, setCells_elemKey _ g a j _ j.isLt]
    · refine ⟨bv, by rw [henv', if_neg hps, hbv], fun j => ?_⟩
      rw [setCells_ne s g a _ n (fun _ _ h => hps (elemKey_inj h).1)]
      exact hbvE j

/-- The abstract leaf `g` writing a layout array is sound for the oracle `ls` at `name`:
    on arguments none of which is abstracted to `other`, cell `j` of the oracle's
    `.memref n` value, encoded, is `g` of the abstracted arguments at `j`. -/
def LeafAbsArr (ls : SemLeafSpec) (name : String) (g : List AVal → Nat → ZMod (2 ^ 64)) :
    Prop :=
  ∀ (n : Nat) (vals : List ((t : CryptoTy) × ⟦t⟧)), (∀ v ∈ vals, vEnc v ≠ .other) →
    ∀ j : Fin n, wEnc (ls name (.memref n) vals j) = g (vals.map vEnc) j

/-- An optional abstract leaf writing a layout array per leaf name. -/
abbrev AbsArrLeaves : Type := String → Option (List AVal → Nat → ZMod (2 ^ 64))

/-- No abstract array leaf. -/
def noArrLeaves : AbsArrLeaves := fun _ => none

/-- Every abstract array leaf of `lfa` is sound for the oracle `ls` at its name. -/
def ArrLeavesSound (ls : SemLeafSpec) (lfa : AbsArrLeaves) : Prop :=
  ∀ name g, lfa name = some g → LeafAbsArr ls name g

theorem arrLeavesSound_noArrLeaves (ls : SemLeafSpec) : ArrLeavesSound ls noArrLeaves :=
  fun _ _ h => by cases h

/-- Cell `j` of an abstract array argument; `0` outside its range and on any other
    argument. -/
def avalCell : AVal → Nat → ZMod (2 ^ 64)
  | .arr n v, j => if h : j < n then v ⟨j, h⟩ else 0
  | _, _ => 0

/-- The abstract array leaf writing cell `k` of its first argument to `f` of the arguments
    and keeping every other cell. -/
def cellLeaf (k : Nat) (f : List AVal → ZMod (2 ^ 64)) : List AVal → Nat → ZMod (2 ^ 64) :=
  fun args j => if j = k then f args else avalCell (args.headD .other) j

/-- On the abstract store, `setCells` of a `cellLeaf` over the array's own cells is the
    write of the one cell. -/
theorem setCells_cellLeaf {L : ArrLayout} {s : String} {n : Nat} (hs : layoutSize L s = some n)
    (k : Nat) (hk : k < n) (f : List AVal → ZMod (2 ^ 64)) (rest : List AVal) (a : AField) :
    setCells s n (cellLeaf k f (absArg L a s :: rest)) a =
      setVal (elemKey s k) (f (absArg L a s :: rest)) a := by
  funext y
  by_cases hy : ∃ j, j < n ∧ y = elemKey s j
  · obtain ⟨j, hj, rfl⟩ := hy
    rw [setCells_elemKey s _ a j n hj]
    simp only [cellLeaf, setVal, List.headD_cons, absArg, hs, avalCell, dif_pos hj]
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [if_neg hjk, if_neg (fun h => hjk (elemKey_inj h).2)]
  · rw [setCells_ne s _ a y n (fun j hj h => hy ⟨j, hj, h⟩)]
    simp only [setVal]
    rw [if_neg (fun h => hy ⟨k, hk, h⟩)]

/-- The oracle realising a family of abstract word leaves on `u64` destinations and a
    family of abstract array leaves on `.memref n` destinations; at every other type it
    returns the default. -/
def leafOfAbsArr (fs : String → List AVal → ZMod (2 ^ 64))
    (gs : String → List AVal → Nat → ZMod (2 ^ 64)) : SemLeafSpec :=
  fun name retTy vals =>
    match retTy with
    | .sword 64 => (BitVec.ofNat 64 (fs name (vals.map vEnc)).val : BitVec 64)
    | .memref _ => fun j => (BitVec.ofNat 64 (gs name (vals.map vEnc) j).val : BitVec 64)
    | t => CryptoTy.default t

theorem leafAbs_leafOfAbsArr (fs : String → List AVal → ZMod (2 ^ 64))
    (gs : String → List AVal → Nat → ZMod (2 ^ 64)) (name : String) :
    LeafAbs (leafOfAbsArr fs gs) name (fs name) := by
  intro vals _
  show wEnc (BitVec.ofNat 64 (fs name (vals.map vEnc)).val) = _
  simp only [wEnc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (ZMod.val_lt _), ZMod.natCast_zmod_val]

theorem leafAbsArr_leafOfAbsArr (fs : String → List AVal → ZMod (2 ^ 64))
    (gs : String → List AVal → Nat → ZMod (2 ^ 64)) (name : String) :
    LeafAbsArr (leafOfAbsArr fs gs) name (gs name) := by
  intro n vals _ j
  show wEnc (BitVec.ofNat 64 (gs name (vals.map vEnc) j).val) = _
  simp only [wEnc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (ZMod.val_lt _), ZMod.natCast_zmod_val]

/-! ## Leaf steps

A leaf node binds one destination to the oracle; a multi-destination node is a sequence
of such bindings. `leafDstStep ls name dst names` is the binding of `dst` at its encoded
type to the oracle at `name` on the argument names `names`; `AbsStep L step p` says the
abstraction `p` is sound for the environment transformer `step` over `SRwordL L`, and
`seqAbs` composes abstractions as the `RSeq` arm does. -/

/-- The binding of `dst` at its encoded type to the oracle at `name` on the arguments
    `names`. -/
def leafDstStep (ls : SemLeafSpec) (name : String) (dst : Located) (names : List String)
    (env : SEnvScalar) : SEnvScalar :=
  env.upd dst.locVar (t := encodeTy dst.locSrc) (ls name (encodeTy dst.locSrc) (argVals env names))

/-- `p` abstracts the environment transformer `step` over `SRwordL L`: under the guards
    of `p`, related states step to related states. -/
def AbsStep (SR : SEnvScalar → AField → Prop) (step : SEnvScalar → SEnvScalar)
    (p : List Guard × (AField → AField)) : Prop :=
  ∀ env a, SR env a → guardsHold p.1 a → SR (step env) (p.2 a)

/-- The sequential composition of two abstractions, as in the `RSeq` arm. -/
def seqAbs (p q : List Guard × (AField → AField)) : List Guard × (AField → AField) :=
  (p.1 ++ q.1.map (Guard.after p.2), fun a => q.2 (p.2 a))

theorem absStep_seq {SR : SEnvScalar → AField → Prop} {s₁ s₂ : SEnvScalar → SEnvScalar}
    {p q : List Guard × (AField → AField)} (h₁ : AbsStep SR s₁ p) (h₂ : AbsStep SR s₂ q) :
    AbsStep SR (fun env => s₂ (s₁ env)) (seqAbs p q) := by
  intro env a hSR hg
  obtain ⟨hg₁, hg₂⟩ := guardsHold_append.mp hg
  exact h₂ _ _ (h₁ env a hSR hg₁) (guardsHold_map_after.mp hg₂)

theorem absStep_unsupported {SR : SEnvScalar → AField → Prop} (step : SEnvScalar → SEnvScalar)
    (ctor : String) : AbsStep SR step (unsupportedAbs ctor) :=
  fun _ _ _ h => (h _ (List.mem_singleton.mpr rfl)).elim

/-- A `CorresL` statement from an abstracted step, when `semScalarL ls` on `c` is `step`
    under the guards. -/
theorem corresL_of_absStep (ls : SemLeafSpec) {SR : SEnvScalar → AField → Prop} {c : LowCT}
    {step : SEnvScalar → SEnvScalar} {p : List Guard × (AField → AField)}
    (hsem : ∀ env a, SR env a → guardsHold p.1 a → semScalarL ls c env = some (step env))
    (h : AbsStep SR step p) : CorresL ls SR (guardsHold p.1) p.2 c :=
  fun env a hSR hP => ⟨step env, hsem env a hSR hP, h env a hSR hP⟩

/-- The `CorresUL` form of `corresL_of_absStep` on a node that is not seq-like. -/
theorem corresUL_of_absStep (ls : SemLeafSpec) {SR : SEnvScalar → AField → Prop} {fuel : Nat}
    {c : LowCT} (hne : isSeqLike c = false) {step : SEnvScalar → SEnvScalar}
    {p : List Guard × (AField → AField)}
    (hsem : ∀ env a, SR env a → guardsHold p.1 a → semScalarL ls c env = some (step env))
    (h : AbsStep SR step p) : CorresUL ls fuel SR (guardsHold p.1) p.2 c :=
  corresUL_of_corresL ls SR hne (corresL_of_absStep ls hsem h)

/-- The word leaf step: binding the unreserved word `dst` to a sound abstract leaf at
    `name` on abstractable arguments preserves `SRwordL L` against the abstract write. -/
theorem srwordL_leafWord_step (ls : SemLeafSpec) (L : ArrLayout) {env : SEnvScalar} {a : AField}
    (name dst : String) (names : List String) (f : List AVal → ZMod (2 ^ 64))
    (hf : LeafAbs ls name f) (hdk : arrKeyB L dst = false)
    (hargs : ∀ x ∈ names, argOkB L x = true) (hSR : SRwordL L env a) :
    SRwordL L (env.upd dst (t := .sword 64) (ls name (.sword 64) (argVals env names)))
      (setVal dst (f (names.map (absArg L a))) a) := by
  obtain ⟨hmap, hne⟩ := argVals_srwordL hSR names hargs
  refine srwordL_set dst (ls name (.sword 64) (argVals env names)) (f (names.map (absArg L a)))
    hdk ?_ hSR (by simp [SEnvScalar.upd]) (fun y _ hy => by simp [SEnvScalar.upd, hy])
  rw [hf _ hne, hmap]

/-- The array leaf step: binding the layout array `dst` of length `n` to a sound abstract
    array leaf at `name` on abstractable arguments preserves `SRwordL L` against
    `setCells`. -/
theorem srwordL_leafArr_step (ls : SemLeafSpec) (L : ArrLayout) {env : SEnvScalar} {a : AField}
    (name dst : String) (n : Nat) (names : List String) (g : List AVal → Nat → ZMod (2 ^ 64))
    (hg : LeafAbsArr ls name g) (hsz : layoutSize L dst = some n)
    (hargs : ∀ x ∈ names, argOkB L x = true) (hSR : SRwordL L env a) :
    SRwordL L (env.upd dst (t := .memref n) (ls name (.memref n) (argVals env names)))
      (setCells dst n (g (names.map (absArg L a))) a) := by
  obtain ⟨hmap, hne⟩ := argVals_srwordL hSR names hargs
  obtain ⟨_, av, hav, _⟩ := hSR.2 _ (layoutSize_mem hsz)
  refine srwordL_arrWriteAll dst n av _ _ hSR (layoutSize_mem hsz) hav (fun j => ?_)
    (fun y => rfl)
  rw [hg n _ hne j, hmap]

/-- An array-valued leaf node over a layout: if `c` binds the layout array `dst` of length
    `n`, whose type encodes to `.memref n`, to the oracle at `name` on the arguments
    `names`, and `g` is sound for the oracle at `name`, then `c` abstracts to
    `setCells dst n (g (abstract arguments))`. -/
theorem corresL_leafArr (ls : SemLeafSpec) (L : ArrLayout) (c : LowCT) (name : String)
    (dst : Located) (n : Nat) (names : List String) (g : List AVal → Nat → ZMod (2 ^ 64))
    (hg : LeafAbsArr ls name g) (hsz : layoutSize L dst.locVar = some n)
    (henc : encodeTy dst.locSrc = .memref n) (hargs : ∀ x ∈ names, argOkB L x = true)
    (hsem : ∀ env a, SRwordL L env a →
      semScalarL ls c env = some (leafDstStep ls name dst names env)) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setCells dst.locVar n (g (names.map (absArg L a))) a) c := by
  intro env a hSR _
  refine ⟨_, hsem env a hSR, ?_⟩
  unfold leafDstStep
  generalize encodeTy dst.locSrc = T at henc ⊢
  subst henc
  exact srwordL_leafArr_step ls L name dst.locVar n names g hg hsz hargs hSR

/-! ## The leaf rules of the array-writing and multi-destination forms -/

theorem argOkB_of_layoutSize {L : ArrLayout} {x : String} {n : Nat}
    (hsz : layoutSize L x = some n) : argOkB L x = true := by
  unfold argOkB; rw [hsz]

theorem argOk_pair {L : ArrLayout} {arr src : Located} {n : Nat}
    (hsz : layoutSize L arr.locVar = some n) (hs : argOkB L src.locVar = true) :
    ∀ x ∈ locNames [arr, src], argOkB L x = true := by
  intro x hx
  simp only [locNames, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl
  · exact argOkB_of_layoutSize hsz
  · exact hs

/-- **The `"arrStore:idx"` leaf rule.** A literal-index write to the layout array `arr` of
    length `n`, whose type encodes to `.memref n`, that is not a word write to a
    `TArr _ .TU64` array (the array has another type, or the source is a layout array),
    takes the leaf arm of `semScalarL` and abstracts to `setCells arr n (g [arr, src])` for
    an abstract array leaf `g` sound for the oracle at `"arrStore:idx"`. -/
theorem corresL_arrStoreLitLeaf (ls : SemLeafSpec) (L : ArrLayout) (arr src : Located)
    (idx n : Nat) (g : List AVal → Nat → ZMod (2 ^ 64))
    (hg : LeafAbsArr ls ("arrStore:" ++ toString idx) g)
    (hsz : layoutSize L arr.locVar = some n) (henc : encodeTy arr.locSrc = .memref n)
    (hs : argOkB L src.locVar = true)
    (hnw : isU64ArrB arr.locSrc = false ∨ (layoutSize L src.locVar).isSome = true) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setCells arr.locVar n (g ((locNames [arr, src]).map (absArg L a))) a)
      (.RArrStoreLit arr idx src) := by
  refine corresL_leafArr ls L _ _ arr n _ g hg hsz henc (argOk_pair hsz hs)
    (fun env a hSR => ?_)
  refine semScalarL_rArrStoreLit_leaf ls arr src idx env (fun k m a v harr _ hs => ?_)
  rcases hnw with h | h
  · rw [harr] at h; exact absurd h (by simp [isU64ArrB])
  · exact srwordL_layout_not_word hSR h v hs

/-- **The one-cell form of the `"arrStore:idx"` leaf rule.** When the abstract array leaf
    is `cellLeaf k f`, the write of cell `k < n` to `f [arr, src]` keeping the other cells,
    the node abstracts to `A[k] := f [arr, src]`. -/
theorem corresL_arrStoreLitCell (ls : SemLeafSpec) (L : ArrLayout) (arr src : Located)
    (idx n k : Nat) (f : List AVal → ZMod (2 ^ 64))
    (hf : LeafAbsArr ls ("arrStore:" ++ toString idx) (cellLeaf k f))
    (hsz : layoutSize L arr.locVar = some n) (henc : encodeTy arr.locSrc = .memref n)
    (hk : k < n) (hs : argOkB L src.locVar = true)
    (hnw : isU64ArrB arr.locSrc = false ∨ (layoutSize L src.locVar).isSome = true) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setVal (elemKey arr.locVar k) (f ((locNames [arr, src]).map (absArg L a))) a)
      (.RArrStoreLit arr idx src) := by
  intro env a hSR _
  obtain ⟨env', hs', hSR'⟩ :=
    corresL_arrStoreLitLeaf ls L arr src idx n _ hf hsz henc hs hnw env a hSR trivial
  refine ⟨env', hs', ?_⟩
  show SRwordL L env'
    (setVal (elemKey arr.locVar k) (f [absArg L a arr.locVar, absArg L a src.locVar]) a)
  rw [← setCells_cellLeaf hsz k hk f [absArg L a src.locVar] a]
  exact hSR'

/-- A select into a destination whose type encodes to a `.memref` takes the leaf arm of
    `semScalarL`, binding the destination by `leafDstStep` at `"select"`. -/
theorem semScalarL_rSelect_leafDst (ls : SemLeafSpec) (dst : Located) (sel : String)
    (src0 src1 : Located) (env : SEnvScalar) {n : Nat} (henc : encodeTy dst.locSrc = .memref n) :
    semScalarL ls (.RSelect dst sel src0 src1) env =
      some (leafDstStep ls "select" dst (sel :: locNames [src0, src1]) env) :=
  semScalarL_rSelect_leaf ls dst sel src0 src1 env
    (fun _ _ _ hd _ _ _ => by rw [hd] at henc; exact absurd henc (by simp [encodeTy]))

/-- **The `"select"` leaf rule into an array.** A select into the layout array `dst` of
    length `n`, whose type encodes to `.memref n`, takes the leaf arm of `semScalarL` and
    abstracts to `setCells dst n (g [sel, src0, src1])` for an abstract array leaf `g`
    sound for the oracle at `"select"`. -/
theorem corresL_selectArrLeaf (ls : SemLeafSpec) (L : ArrLayout) (dst : Located) (sel : String)
    (src0 src1 : Located) (n : Nat) (g : List AVal → Nat → ZMod (2 ^ 64))
    (hg : LeafAbsArr ls "select" g) (hsz : layoutSize L dst.locVar = some n)
    (henc : encodeTy dst.locSrc = .memref n) (hs : argOkB L sel = true)
    (h0 : argOkB L src0.locVar = true) (h1 : argOkB L src1.locVar = true) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setCells dst.locVar n (g ((sel :: locNames [src0, src1]).map (absArg L a))) a)
      (.RSelect dst sel src0 src1) :=
  corresL_leafArr ls L _ "select" dst n _ g hg hsz henc (by simp [locNames, hs, h0, h1])
    (fun env _ _ => semScalarL_rSelect_leafDst ls dst sel src0 src1 env henc)

open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms (inlineArithRecipe) in
/-- **The leaf call rule into an array.** `RCall fname dst args` with `fname` outside
    `inlineArithTable` and `dst` a layout array of length `n` whose type encodes to
    `.memref n` abstracts to `setCells dst n (g (abstract arguments))` for an abstract
    array leaf `g` sound for the oracle at `fname`. -/
theorem corresL_callArr (ls : SemLeafSpec) (L : ArrLayout) (fname : String)
    (hni : inlineArithRecipe fname = none) (dst : Located)
    (args : List Located) (n : Nat) (g : List AVal → Nat → ZMod (2 ^ 64))
    (hg : LeafAbsArr ls fname g) (hsz : layoutSize L dst.locVar = some n)
    (henc : encodeTy dst.locSrc = .memref n) (hargs : ∀ x ∈ locNames args, argOkB L x = true) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setCells dst.locVar n (g ((locNames args).map (absArg L a))) a)
      (.RCall fname dst args) :=
  corresL_leafArr ls L _ fname dst n _ g hg hsz henc hargs
    (fun env _ _ => semScalarL_rCall_of_recipe_none ls hni dst args env)

/-- **The destination-threaded call rule.** `RCallDstThreaded fname dst args` with `dst` an
    unreserved `u64` word abstracts to `dst := f (abstract dst :: abstract arguments)`
    for an abstract leaf `f` sound for the oracle at `fname`. -/
theorem corresL_callDstThreaded (ls : SemLeafSpec) (L : ArrLayout) (fname : String)
    (dst : Located) (args : List Located) (f : List AVal → ZMod (2 ^ 64))
    (hf : LeafAbs ls fname f) (hd : dst.locSrc = .TU64) (hdk : arrKeyB L dst.locVar = false)
    (hargs : ∀ x ∈ locNames (dst :: args), argOkB L x = true) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setVal dst.locVar (f ((locNames (dst :: args)).map (absArg L a))) a)
      (.RCallDstThreaded fname dst args) := by
  obtain ⟨dv, dt⟩ := dst
  simp only at hd hdk hargs ⊢
  subst hd
  exact corresL_leafWord ls L _ fname dv _ f hf hdk hargs (fun _ _ _ => rfl)

/-- **The destination-threaded call rule into an array.** With `dst` a layout array of
    length `n` whose type encodes to `.memref n`, the node abstracts to
    `setCells dst n (g (abstract dst :: abstract arguments))`. -/
theorem corresL_callDstThreadedArr (ls : SemLeafSpec) (L : ArrLayout) (fname : String)
    (dst : Located) (args : List Located) (n : Nat) (g : List AVal → Nat → ZMod (2 ^ 64))
    (hg : LeafAbsArr ls fname g) (hsz : layoutSize L dst.locVar = some n)
    (henc : encodeTy dst.locSrc = .memref n)
    (hargs : ∀ x ∈ locNames (dst :: args), argOkB L x = true) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setCells dst.locVar n (g ((locNames (dst :: args)).map (absArg L a))) a)
      (.RCallDstThreaded fname dst args) :=
  corresL_leafArr ls L _ fname dst n _ g hg hsz henc hargs (fun _ _ _ => rfl)

/-- **The `"tupleLoad:idx"` leaf rule.** `RTupleLoad dst src idx` with `dst` an unreserved
    `u64` word and `src` a layout array or an unreserved non-temp word abstracts to
    `dst := f [src]` for an abstract leaf `f` sound for the oracle at `"tupleLoad:idx"`. -/
theorem corresL_tupleLoadLeaf (ls : SemLeafSpec) (L : ArrLayout) (dst src : Located) (idx : Nat)
    (f : List AVal → ZMod (2 ^ 64)) (hf : LeafAbs ls ("tupleLoad:" ++ toString idx) f)
    (hd : dst.locSrc = .TU64) (hdk : arrKeyB L dst.locVar = false)
    (hs : argOkB L src.locVar = true) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setVal dst.locVar (f ((locNames [src]).map (absArg L a))) a)
      (.RTupleLoad dst src idx) := by
  obtain ⟨dv, dt⟩ := dst
  simp only at hd hdk ⊢
  subst hd
  exact corresL_leafWord ls L _ _ dv _ f hf hdk (by simp [locNames, hs]) (fun _ _ _ => rfl)

/-- **The `"tupleLoad:idx"` leaf rule into an array.** With `dst` a layout array of length
    `n` whose type encodes to `.memref n`, the node abstracts to
    `setCells dst n (g [src])`. -/
theorem corresL_tupleLoadArrLeaf (ls : SemLeafSpec) (L : ArrLayout) (dst src : Located)
    (idx n : Nat) (g : List AVal → Nat → ZMod (2 ^ 64))
    (hg : LeafAbsArr ls ("tupleLoad:" ++ toString idx) g)
    (hsz : layoutSize L dst.locVar = some n) (henc : encodeTy dst.locSrc = .memref n)
    (hs : argOkB L src.locVar = true) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a => setCells dst.locVar n (g ((locNames [src]).map (absArg L a))) a)
      (.RTupleLoad dst src idx) :=
  corresL_leafArr ls L _ _ dst n _ g hg hsz henc (by simp [locNames, hs]) (fun _ _ _ => rfl)

/-- **The two-destination call rule.** `RCallSwap fname dest1 dest2 args` with both
    destinations unreserved `u64` words abstracts to the two writes
    `dest1 := f (abstract arguments)`, then `dest2 := f (abstract arguments)` read after
    the first write, for an abstract leaf `f` sound for the oracle at `fname`. -/
theorem corresL_callSwap (ls : SemLeafSpec) (L : ArrLayout) (fname : String)
    (dest1 dest2 : Located) (args : List Located) (f : List AVal → ZMod (2 ^ 64))
    (hf : LeafAbs ls fname f) (h1 : dest1.locSrc = .TU64) (h1k : arrKeyB L dest1.locVar = false)
    (h2 : dest2.locSrc = .TU64) (h2k : arrKeyB L dest2.locVar = false)
    (hargs : ∀ x ∈ locNames args, argOkB L x = true) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a =>
        let a₁ := setVal dest1.locVar (f ((locNames args).map (absArg L a))) a
        setVal dest2.locVar (f ((locNames args).map (absArg L a₁))) a₁)
      (.RCallSwap fname dest1 dest2 args) := by
  obtain ⟨d1, t1⟩ := dest1
  obtain ⟨d2, t2⟩ := dest2
  simp only at h1 h1k h2 h2k ⊢
  subst h1 h2
  intro env a hSR _
  exact ⟨_, rfl, srwordL_leafWord_step ls L fname d2 _ f hf h2k hargs
    (srwordL_leafWord_step ls L fname d1 _ f hf h1k hargs hSR)⟩

/-- **The clone-and-call rule.** `RCloneCall cv _ oldDest innerF newDest args` with the
    clone variable and the new destination unreserved `u64` words and the old destination
    an unreserved non-temp word abstracts to `cv := fc [oldDest]`, then
    `newDest := f (abstract arguments)` read after that write, for abstract leaves `fc` and
    `f` sound for the oracle at `"clone"` and at `innerF`. -/
theorem corresL_cloneCall (ls : SemLeafSpec) (L : ArrLayout) (cv : String) (tt : TowerType)
    (oldDest : Located) (innerF : String) (newDest : Located) (args : List Located)
    (fc f : List AVal → ZMod (2 ^ 64)) (hfc : LeafAbs ls "clone" fc) (hf : LeafAbs ls innerF f)
    (hcv : arrKeyB L cv = false) (hosz : layoutSize L oldDest.locVar = none)
    (hoa : argOkB L oldDest.locVar = true)
    (hn : newDest.locSrc = .TU64) (hnk : arrKeyB L newDest.locVar = false)
    (hargs : ∀ x ∈ locNames args, argOkB L x = true) :
    CorresL ls (SRwordL L) (fun _ => True)
      (fun a =>
        let a₁ := setVal cv (fc [absArg L a oldDest.locVar]) a
        setVal newDest.locVar (f ((locNames args).map (absArg L a₁))) a₁)
      (.RCloneCall cv tt oldDest innerF newDest args) := by
  obtain ⟨nv, nt⟩ := newDest
  simp only at hn hnk ⊢
  subst hn
  intro env a hSR _
  have ho := hoa
  unfold argOkB at ho
  rw [hosz] at ho
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at ho
  obtain ⟨w, hw, _⟩ := hSR.1 _ (notTmpB_sound _ ho.1) ho.2
  refine ⟨_, semScalarL_rCloneCall ls cv tt oldDest innerF ⟨nv, .TU64⟩ args env (.sword 64) w hw,
    ?_⟩
  exact srwordL_leafWord_step ls L innerF nv _ f hf hnk hargs
    (srwordL_leafWord_step ls L "clone" cv [oldDest.locVar] fc hfc hcv
      (by simpa using hoa) hSR)

/-! ## The total abstraction with abstract leaves -/

/-- The abstraction of a node binding `dst` to the oracle at `name` on the argument names
    `names`: the word leaf `lf name` on an unreserved `u64` word, the array leaf `lfa name`
    on a layout array whose type encodes to its layout length; unsupported at `ctor`
    otherwise. -/
def leafDstAbs (ctor : String) (lf : AbsLeaves) (lfa : AbsArrLeaves) (L : ArrLayout)
    (name : String) (dst : Located) (names : List String) : List Guard × (AField → AField) :=
  match lf name, lfa name with
  | none, none => unsupportedAbs ctor
  | of, og =>
      match layoutSize L dst.locVar with
      | none =>
          match of with
          | some f =>
              if dst.locSrc = .TU64 ∧ arrKeyB L dst.locVar = false ∧
                  names.all (argOkB L) = true then
                ([], fun a => setVal dst.locVar (f (names.map (absArg L a))) a)
              else unsupportedAbs ctor
          | none => unsupportedAbs ctor
      | some n =>
          match og with
          | some g =>
              if encodeTy dst.locSrc = .memref n ∧ names.all (argOkB L) = true then
                ([], fun a => setCells dst.locVar n (g (names.map (absArg L a))) a)
              else unsupportedAbs ctor
          | none => unsupportedAbs ctor

/-- `leafDstAbs` is unsupported, a word leaf on an unreserved `u64` word, or an array
    leaf on a layout array whose type encodes to its layout length. -/
theorem leafDstAbs_spec (ctor : String) (lf : AbsLeaves) (lfa : AbsArrLeaves) (L : ArrLayout)
    (name : String) (dst : Located) (names : List String) :
    leafDstAbs ctor lf lfa L name dst names = unsupportedAbs ctor ∨
    (∃ f, lf name = some f ∧ layoutSize L dst.locVar = none ∧ dst.locSrc = .TU64 ∧
      arrKeyB L dst.locVar = false ∧ (∀ x ∈ names, argOkB L x = true) ∧
      leafDstAbs ctor lf lfa L name dst names =
        ([], fun a => setVal dst.locVar (f (names.map (absArg L a))) a)) ∨
    (∃ g n, lfa name = some g ∧ layoutSize L dst.locVar = some n ∧
      encodeTy dst.locSrc = .memref n ∧ (∀ x ∈ names, argOkB L x = true) ∧
      leafDstAbs ctor lf lfa L name dst names =
        ([], fun a => setCells dst.locVar n (g (names.map (absArg L a))) a)) := by
  unfold leafDstAbs
  rcases hl : lf name with _ | f <;> rcases hla : lfa name with _ | g
  · exact Or.inl rfl
  all_goals
    rcases hsz : layoutSize L dst.locVar with _ | n <;> dsimp only
  all_goals try exact Or.inl rfl
  all_goals split_ifs with hc
  all_goals try exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨g, n, rfl, rfl, hc.1, fun x hx => List.all_eq_true.mp hc.2 x hx, rfl⟩)
  · exact Or.inr (Or.inl ⟨f, rfl, rfl, hc.1, hc.2.1, fun x hx => List.all_eq_true.mp hc.2.2 x hx,
      rfl⟩)
  · exact Or.inr (Or.inl ⟨f, rfl, rfl, hc.1, hc.2.1, fun x hx => List.all_eq_true.mp hc.2.2 x hx,
      rfl⟩)
  · exact Or.inr (Or.inr ⟨g, n, rfl, rfl, hc.1, fun x hx => List.all_eq_true.mp hc.2 x hx, rfl⟩)

/-- Under sound leaves, `leafDstAbs` abstracts `leafDstStep`. -/
theorem absStep_leafDst (ls : SemLeafSpec) (lf : AbsLeaves) (lfa : AbsArrLeaves)
    (hlf : LeavesSound ls lf) (hlfa : ArrLeavesSound ls lfa) (L : ArrLayout) (ctor name : String)
    (dst : Located) (names : List String) :
    AbsStep (SRwordL L) (leafDstStep ls name dst names) (leafDstAbs ctor lf lfa L name dst names) := by
  rcases leafDstAbs_spec ctor lf lfa L name dst names with h | ⟨f, hl, _, hd, hdk, hargs, h⟩ |
    ⟨g, n, hla, hsz, henc, hargs, h⟩
  · rw [h]; exact absStep_unsupported _ _
  · rw [h]
    intro env a hSR _
    have hT : encodeTy dst.locSrc = .sword 64 := by rw [hd]; rfl
    unfold leafDstStep
    generalize encodeTy dst.locSrc = T at hT ⊢
    subst hT
    exact srwordL_leafWord_step ls L name dst.locVar names f (hlf _ _ hl) hdk hargs hSR
  · rw [h]
    intro env a hSR _
    unfold leafDstStep
    generalize encodeTy dst.locSrc = T at henc ⊢
    subst henc
    exact srwordL_leafArr_step ls L name dst.locVar n names g (hlfa _ _ hla) hsz hargs hSR

/-- The guards of `leafDstAbs` hold only in its word or array case. -/
theorem leafDstAbs_cases {ctor : String} {lf : AbsLeaves} {lfa : AbsArrLeaves} {L : ArrLayout}
    {name : String} {dst : Located} {names : List String} {a : AField}
    (hg : guardsHold (leafDstAbs ctor lf lfa L name dst names).1 a) :
    (layoutSize L dst.locVar = none ∧ dst.locSrc = .TU64 ∧ arrKeyB L dst.locVar = false ∧
        ∀ x ∈ names, argOkB L x = true) ∨
      (∃ n, layoutSize L dst.locVar = some n ∧ encodeTy dst.locSrc = .memref n ∧
        ∀ x ∈ names, argOkB L x = true) := by
  rcases leafDstAbs_spec ctor lf lfa L name dst names with h | ⟨_, _, hsz, hd, hdk, hargs, _⟩ |
    ⟨_, n, _, hsz, henc, hargs, _⟩
  · rw [h] at hg; exact (hg _ (List.mem_singleton.mpr rfl)).elim
  · exact Or.inl ⟨hsz, hd, hdk, hargs⟩
  · exact Or.inr ⟨n, hsz, henc, hargs⟩

/-- The abstraction of `RCall fname dst args`: `leafDstAbs` at `fname` on the arguments.
    A call of a name in `inlineArithTable` into a `.TFp` slot is unsupported: the front
    lowers it inline and `semScalarL` binds the inline value, not the leaf oracle. -/
def callAbsL (lf : AbsLeaves) (lfa : AbsArrLeaves) (L : ArrLayout) (fname : String)
    (dst : Located) (args : List Located) : List Guard × (AField → AField) :=
  if dst.locSrc = .TFp ∧ (inlineArithRecipe fname).isSome then unsupportedAbs "RCall"
  else leafDstAbs "RCall" lf lfa L fname dst (locNames args)

/-- Outside the inline arithmetic case the `RCall` value is the leaf oracle at the encoded
    destination type. -/
theorem inlineRCallVal_eq_of_not_inline (ls : SemLeafSpec) (f : String) (tt : TowerType)
    (vals : List ((t : CryptoTy) × ⟦t⟧)) (hn : ¬ (tt = .TFp ∧ (inlineArithRecipe f).isSome)) :
    inlineRCallVal ls f tt vals = ls f (encodeTy tt) vals := by
  cases tt <;> try rfl
  have hrec : inlineArithRecipe f = none := by
    cases h : inlineArithRecipe f with
    | none => rfl
    | some r => exact absurd ⟨rfl, by simp [h]⟩ hn
  exact withInlineArith_of_recipe_none ls hrec (.memref 6) vals

/-- The abstraction of `RCallDstThreaded fname dst args`: `leafDstAbs` at `fname` on the
    destination followed by the arguments. -/
def callDstThreadedAbsL (lf : AbsLeaves) (lfa : AbsArrLeaves) (L : ArrLayout) (fname : String)
    (dst : Located) (args : List Located) : List Guard × (AField → AField) :=
  leafDstAbs "RCallDstThreaded" lf lfa L fname dst (locNames (dst :: args))

/-- The abstraction of `RTupleLoad dst src idx`: `leafDstAbs` at `"tupleLoad:idx"` on the
    source. -/
def tupleLoadAbsL (lf : AbsLeaves) (lfa : AbsArrLeaves) (L : ArrLayout) (dst src : Located)
    (idx : Nat) : List Guard × (AField → AField) :=
  leafDstAbs "RTupleLoad" lf lfa L ("tupleLoad:" ++ toString idx) dst (locNames [src])

/-- The abstraction of `RCallSwap fname dest1 dest2 args`: the sequence of the two
    `leafDstAbs` bindings at `fname` on the arguments, when a leaf at `fname` is given. -/
def callSwapAbsL (lf : AbsLeaves) (lfa : AbsArrLeaves) (L : ArrLayout) (fname : String)
    (dest1 dest2 : Located) (args : List Located) : List Guard × (AField → AField) :=
  match lf fname, lfa fname with
  | none, none => unsupportedAbs "RCallSwap"
  | _, _ =>
      seqAbs (leafDstAbs "RCallSwap" lf lfa L fname dest1 (locNames args))
        (leafDstAbs "RCallSwap" lf lfa L fname dest2 (locNames args))

/-- The abstraction of `RCloneCall cv _ oldDest innerF newDest args`: the `leafDstAbs`
    binding of the clone variable, typed as the old destination, at `"clone"` on the old
    destination, then the `leafDstAbs` binding of the new destination at `innerF` on the
    arguments; the layout gives the clone variable and the old destination the same
    length, if any. -/
def cloneCallAbsL (lf : AbsLeaves) (lfa : AbsArrLeaves) (L : ArrLayout) (cv : String)
    (oldDest : Located) (innerF : String) (newDest : Located) (args : List Located) :
    List Guard × (AField → AField) :=
  match lf "clone", lfa "clone" with
  | none, none => unsupportedAbs "RCloneCall"
  | _, _ =>
      if layoutSize L oldDest.locVar = layoutSize L cv then
        seqAbs (leafDstAbs "RCloneCall" lf lfa L "clone" ⟨cv, oldDest.locSrc⟩ [oldDest.locVar])
          (leafDstAbs "RCloneCall" lf lfa L innerF newDest (locNames args))
      else unsupportedAbs "RCloneCall"

/-- The abstraction of the destination fold of `RCallN fname dests args` from output `i`:
    destination `i` through `leafDstAbs` at `callNLeafName fname i` on the arguments, then
    the rest. -/
def callNAbsL (lf : AbsLeaves) (lfa : AbsArrLeaves) (L : ArrLayout) (fname : String)
    (args : List Located) : List Located → Nat → List Guard × (AField → AField)
  | [], _ => ([], id)
  | d :: rest, i =>
      seqAbs (leafDstAbs "RCallN" lf lfa L (callNLeafName fname i) d (locNames args))
        (callNAbsL lf lfa L fname args rest (i + 1))

/-- The abstraction of `RCallN fname dests args`: the destination fold from output `0`,
    when a leaf at the name of output `0` is given. -/
def callNTopAbsL (lf : AbsLeaves) (lfa : AbsArrLeaves) (L : ArrLayout) (fname : String)
    (dests args : List Located) : List Guard × (AField → AField) :=
  match lf (callNLeafName fname 0), lfa (callNLeafName fname 0) with
  | none, none => unsupportedAbs "RCallN"
  | _, _ => callNAbsL lf lfa L fname args dests 0

/-- The abstraction of `RSelect dst sel src0 src1` into a word: the abstract leaf
    `lf "select"` when one of the selector and sources is a layout array, `selectAbs`
    otherwise. -/
def selectWordAbsL (lf : AbsLeaves) (L : ArrLayout) (dst : Located) (sel : String)
    (src0 src1 : Located) : List Guard × (AField → AField) :=
  match lf "select" with
  | some f =>
      if dst.locSrc = .TU64 ∧ arrKeyB L dst.locVar = false ∧ argOkB L sel = true ∧
          argOkB L src0.locVar = true ∧ argOkB L src1.locVar = true ∧
          ((layoutSize L sel).isSome || (layoutSize L src0.locVar).isSome ||
            (layoutSize L src1.locVar).isSome) = true then
        ([], fun a => setVal dst.locVar (f ((sel :: locNames [src0, src1]).map (absArg L a))) a)
      else selectAbs L dst sel src0 src1
  | none => selectAbs L dst sel src0 src1

/-- The abstraction of `RSelect dst sel src0 src1`: `leafDstAbs` at `"select"` on the
    selector and the sources when the destination is a layout array and an array leaf at
    `"select"` is given, `selectWordAbsL` otherwise. -/
def selectAbsL (lf : AbsLeaves) (lfa : AbsArrLeaves) (L : ArrLayout) (dst : Located)
    (sel : String) (src0 src1 : Located) : List Guard × (AField → AField) :=
  match lfa "select" with
  | some _ =>
      match layoutSize L dst.locVar with
      | some _ => leafDstAbs "RSelect" lf lfa L "select" dst (sel :: locNames [src0, src1])
      | none => selectWordAbsL lf L dst sel src0 src1
  | none => selectWordAbsL lf L dst sel src0 src1

/-- The abstraction of `RArrStoreLit arr idx src`: `leafDstAbs` at `"arrStore:idx"` on
    the array and the source when an array leaf at that name is given and the node is
    not a word write to a `TArr _ .TU64` array (the array has another type, or the
    source is a layout array), `arrStoreLitAbs` otherwise. -/
def arrStoreLitAbsL (lf : AbsLeaves) (lfa : AbsArrLeaves) (L : ArrLayout) (arr : Located)
    (idx : Nat) (src : Located) : List Guard × (AField → AField) :=
  match lfa ("arrStore:" ++ toString idx) with
  | some _ =>
      if isU64ArrB arr.locSrc = false ∨ (layoutSize L src.locVar).isSome = true then
        leafDstAbs "RArrStoreLit" lf lfa L ("arrStore:" ++ toString idx) arr (locNames [arr, src])
      else arrStoreLitAbs L arr idx src
  | none => arrStoreLitAbs L arr idx src

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

/-- The total abstraction over a layout with abstract word leaves `lf` and array leaves
    `lfa`: `ascendGL` with the leaf arms `RCall`, `RCallSwap`, `RCloneCall`, `RCallN`,
    `RSelect`, `RTupleLoad`, `RArrStoreLit`, `RArrLoadLit` and `RCallDstThreaded`
    consulting `lf` and `lfa`. -/
def ascendGLL (lf : AbsLeaves) (lfa : AbsArrLeaves) (L : ArrLayout) (fuel : Nat) :
    LowCT → List Guard × (AField → AField)
  | .RSkip => ([], id)
  | .RBlock body => ascendGLL lf lfa L fuel body
  | .RSeq c₁ c₂ =>
      ((ascendGLL lf lfa L fuel c₁).1 ++
          (ascendGLL lf lfa L fuel c₂).1.map (Guard.after (ascendGLL lf lfa L fuel c₁).2),
        fun a => (ascendGLL lf lfa L fuel c₂).2 ((ascendGLL lf lfa L fuel c₁).2 a))
  | .RScalarSet x n => if arrKeyB L x then unsupportedAbs "RScalarSet" else ([], setLit x n)
  | .RScalarSetExpr x e => ascendExprL L x e
  | .RAssert label => ([Guard.assert label], id)
  | .RLetU64Zero x body =>
      if arrKeyB L x then unsupportedAbs "RLetU64Zero"
      else if loopFree body then
        ((ascendGLL lf lfa L fuel body).1.map (Guard.after (setLit x 0)),
          fun a => (ascendGLL lf lfa L fuel body).2 (setLit x 0 a))
      else unsupportedAbs "RLetU64Zero"
  | .RIfNz name thenBr elseBr => ascendIf L name thenBr elseBr (ascendGLL lf lfa L fuel thenBr)
  | .RWhileNz name body =>
      if arrKeyB L name then unsupportedAbs "RWhileNz"
      else if notTmpB name then
        (Guard.loopHalts name fuel (ascendGLL lf lfa L fuel body).2 ::
            (ascendGLL lf lfa L fuel body).1.map
              (Guard.loopBody name fuel (ascendGLL lf lfa L fuel body).2),
          awhile (nzB name) (ascendGLL lf lfa L fuel body).2 fuel)
      else unsupportedAbs "RWhileNz"
  | .RFor x N body =>
      if arrKeyB L x then unsupportedAbs "RFor"
      else
        ((ascendGLL lf lfa L fuel body).1.map
            (Guard.everyTrip x N (ascendGLL lf lfa L fuel body).2),
          forFold (setLit x) (ascendGLL lf lfa L fuel body).2 N)
  | .RArrLoad dst src idxVar => arrLoadAbs L dst src idxVar
  | .RArrStore arr idxVar src => arrStoreAbs L arr idxVar src
  | .RLimbStore loc idx v => limbStoreAbs L loc idx v
  | .RLetZero _ _ _ => unsupportedAbs "RLetZero"
  | .RCall fname dst args => callAbsL lf lfa L fname dst args
  | .RCallSwap fname dest1 dest2 args => callSwapAbsL lf lfa L fname dest1 dest2 args
  | .RCloneCall cv _ oldDest innerF newDest args =>
      cloneCallAbsL lf lfa L cv oldDest innerF newDest args
  | .RCallN fname dests args => callNTopAbsL lf lfa L fname dests args
  | .RSelect dst sel src0 src1 => selectAbsL lf lfa L dst sel src0 src1
  | .RLimbStoreExpr _ _ _ => unsupportedAbs "RLimbStoreExpr"
  | .RFnDef _ _ _ _ _ => unsupportedAbs "RFnDef"
  | .RFnCall _ _ _ => unsupportedAbs "RFnCall"
  | .RTupleLoad dst src idx => tupleLoadAbsL lf lfa L dst src idx
  | .RArrStoreLit arr idx src => arrStoreLitAbsL lf lfa L arr idx src
  | .RArrLoadLit dst src idx => arrLoadLitAbsL lf L dst src idx
  | .RCallDstThreaded fname dst args => callDstThreadedAbsL lf lfa L fname dst args
  | .RForRuntime _ _ _ => unsupportedAbs "RForRuntime"
  | .RCopy _ _ => unsupportedAbs "RCopy"

/-- Without abstract leaves `ascendGLL` is `ascendGL`. -/
theorem ascendGLL_noLeaves (L : ArrLayout) (fuel : Nat) :
    ∀ c : LowCT, ascendGLL noLeaves noArrLeaves L fuel c = ascendGL L fuel c := by
  intro c
  induction c with
  | RSeq c₁ c₂ ih₁ ih₂ => simp only [ascendGLL, ascendGL, ih₁, ih₂]
  | RBlock body ih => simp only [ascendGLL, ascendGL, ih]
  | RLetU64Zero x body ih => simp only [ascendGLL, ascendGL, ih]
  | RIfNz name thenBr elseBr ihT _ => simp only [ascendGLL, ascendGL, ihT]
  | RWhileNz name body ih => simp only [ascendGLL, ascendGL, ih]
  | RFor x N body ih => simp only [ascendGLL, ascendGL, ih]
  | RCall f dst args =>
      show callAbsL noLeaves noArrLeaves L f dst args = unsupportedAbs "RCall"
      unfold callAbsL
      split <;> rfl
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
          (corresL_of_corres_eqOn _ _
            (corresL_limbStore L loc idx v n (layoutSize_mem hs) hc)
            (fun env _ hSR => by
              obtain ⟨_, av, hav, _⟩ := hSR.2 _ (layoutSize_mem hs)
              have hav' : env loc.locVar = some ⟨.memref n, av⟩ := hav
              simp only [semScalarL, semScalar, hav'])))
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

/-- The word case of the `RSelect` arm. -/
theorem corresUL_selectWordAbsL (ls : SemLeafSpec) (lf : AbsLeaves) (hlf : LeavesSound ls lf)
    (L : ArrLayout) (fuel : Nat) (dst : Located) (sel : String) (src0 src1 : Located) :
    CorresUL ls fuel (SRwordL L) (guardsHold (selectWordAbsL lf L dst sel src0 src1).1)
      (selectWordAbsL lf L dst sel src0 src1).2 (.RSelect dst sel src0 src1) := by
  unfold selectWordAbsL
  rcases hl : lf "select" with _ | f
  · exact corresUL_selectAbs ls L fuel dst sel src0 src1
  · dsimp only
    by_cases hc : dst.locSrc = .TU64 ∧ arrKeyB L dst.locVar = false ∧
        argOkB L sel = true ∧ argOkB L src0.locVar = true ∧ argOkB L src1.locVar = true ∧
        ((layoutSize L sel).isSome || (layoutSize L src0.locVar).isSome ||
          (layoutSize L src1.locVar).isSome) = true
    · rw [if_pos hc]
      obtain ⟨hd, hdk, hs, h0, h1, harr⟩ := hc
      exact corresUL_weaken _ _
        (corresUL_of_corresL _ _ rfl
          (corresL_selectLeaf ls L dst sel src0 src1 f (hlf _ _ hl) hd hdk hs h0 h1 harr))
        (fun _ _ => trivial)
    · rw [if_neg hc]
      exact corresUL_selectAbs ls L fuel dst sel src0 src1

/-- The destination fold of `RCallN` is abstracted by `callNAbsL` from every output
    index. -/
theorem absStep_callN (ls : SemLeafSpec) (lf : AbsLeaves) (lfa : AbsArrLeaves)
    (hlf : LeavesSound ls lf) (hlfa : ArrLeavesSound ls lfa) (L : ArrLayout) (fname : String)
    (args : List Located) :
    ∀ (dests : List Located) (i : Nat),
      AbsStep (SRwordL L) (semCallNDestsL ls fname args dests i)
        (callNAbsL lf lfa L fname args dests i)
  | [], _ => fun _ _ h _ => h
  | d :: rest, i => by
      show AbsStep (SRwordL L)
        (fun env => semCallNDestsL ls fname args rest (i + 1)
          (leafDstStep ls (callNLeafName fname i) d (locNames args) env)) _
      exact absStep_seq
        (absStep_leafDst ls lf lfa hlf hlfa L "RCallN" (callNLeafName fname i) d (locNames args))
        (absStep_callN ls lf lfa hlf hlfa L fname args rest (i + 1))

/-- **The multi-destination call rule.** `RCallN fname dests args` abstracts to the fold
    `callNAbsL` of the destination bindings from output `0`, under its guards and sound
    leaves. -/
theorem corresL_callN (ls : SemLeafSpec) (lf : AbsLeaves) (lfa : AbsArrLeaves)
    (hlf : LeavesSound ls lf) (hlfa : ArrLeavesSound ls lfa) (L : ArrLayout) (fname : String)
    (dests args : List Located) :
    CorresL ls (SRwordL L) (guardsHold (callNAbsL lf lfa L fname args dests 0).1)
      (callNAbsL lf lfa L fname args dests 0).2 (.RCallN fname dests args) :=
  corresL_of_absStep ls (fun _ _ _ _ => rfl) (absStep_callN ls lf lfa hlf hlfa L fname args dests 0)

/-- Soundness of the total abstraction with abstract leaves: under its guards and sound
    abstract leaves, `ascendGLL lf lfa L fuel c` is a `CorresUL ls fuel (SRwordL L)`
    correspondent of `c`. -/
theorem ascendGLL_sound (ls : SemLeafSpec) (lf : AbsLeaves) (lfa : AbsArrLeaves)
    (hlf : LeavesSound ls lf) (hlfa : ArrLeavesSound ls lfa) (L : ArrLayout) (fuel : Nat) :
    ∀ c : LowCT,
      CorresUL ls fuel (SRwordL L) (guardsHold (ascendGLL lf lfa L fuel c).1)
        (ascendGLL lf lfa L fuel c).2 c := by
  intro c
  induction c
  case RSkip =>
    show CorresUL ls fuel (SRwordL L) (guardsHold []) id .RSkip
    exact corresUL_weaken _ _
      (corresUL_of_corresL _ _ rfl (corresL_of_corres_eq _ _ (corres_skip _) (fun _ => rfl)))
      (fun _ _ => trivial)
  case RBlock body ih =>
    show CorresUL ls fuel (SRwordL L) (guardsHold (ascendGLL lf lfa L fuel body).1)
      (ascendGLL lf lfa L fuel body).2 (.RBlock body)
    exact corresUL_block _ _ ih
  case RSeq c₁ c₂ ih₁ ih₂ =>
    show CorresUL ls fuel (SRwordL L)
      (guardsHold ((ascendGLL lf lfa L fuel c₁).1 ++
        (ascendGLL lf lfa L fuel c₂).1.map (Guard.after (ascendGLL lf lfa L fuel c₁).2)))
      (fun a => (ascendGLL lf lfa L fuel c₂).2 ((ascendGLL lf lfa L fuel c₁).2 a)) (.RSeq c₁ c₂)
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
  case RCall fname dst args =>
    show CorresUL ls fuel (SRwordL L) (guardsHold (callAbsL lf lfa L fname dst args).1)
      (callAbsL lf lfa L fname dst args).2 (.RCall fname dst args)
    unfold callAbsL
    split
    · exact corresUL_unsupported _ _ _ _ _
    · rename_i hn
      exact corresUL_of_absStep ls rfl
        (fun env _ _ _ => by
          rw [semScalarL_rCall, inlineRCallVal_eq_of_not_inline ls fname dst.locSrc _ hn]; rfl)
        (absStep_leafDst ls lf lfa hlf hlfa L "RCall" fname dst (locNames args))
  case RCallDstThreaded fname dst args =>
    exact corresUL_of_absStep ls rfl (fun _ _ _ _ => rfl)
      (absStep_leafDst ls lf lfa hlf hlfa L "RCallDstThreaded" fname dst (locNames (dst :: args)))
  case RTupleLoad dst src idx =>
    exact corresUL_of_absStep ls rfl (fun _ _ _ _ => rfl)
      (absStep_leafDst ls lf lfa hlf hlfa L "RTupleLoad" ("tupleLoad:" ++ toString idx) dst
        (locNames [src]))
  case RCallSwap fname dest1 dest2 args =>
    show CorresUL ls fuel (SRwordL L) (guardsHold (callSwapAbsL lf lfa L fname dest1 dest2 args).1)
      (callSwapAbsL lf lfa L fname dest1 dest2 args).2 (.RCallSwap fname dest1 dest2 args)
    unfold callSwapAbsL
    rcases lf fname with _ | f <;> rcases lfa fname with _ | g
    · exact corresUL_unsupported _ _ _ _ _
    all_goals
      exact corresUL_of_absStep ls rfl (fun _ _ _ _ => rfl)
        (absStep_seq
          (absStep_leafDst ls lf lfa hlf hlfa L "RCallSwap" fname dest1 (locNames args))
          (absStep_leafDst ls lf lfa hlf hlfa L "RCallSwap" fname dest2 (locNames args)))
  case RCloneCall cv tt oldDest innerF newDest args =>
    show CorresUL ls fuel (SRwordL L)
      (guardsHold (cloneCallAbsL lf lfa L cv oldDest innerF newDest args).1)
      (cloneCallAbsL lf lfa L cv oldDest innerF newDest args).2
      (.RCloneCall cv tt oldDest innerF newDest args)
    unfold cloneCallAbsL
    rcases lf "clone" with _ | f <;> rcases lfa "clone" with _ | g
    · exact corresUL_unsupported _ _ _ _ _
    all_goals
      by_cases hsz : layoutSize L oldDest.locVar = layoutSize L cv
      · rw [if_pos hsz]
        refine corresUL_of_absStep ls rfl (fun env a hSR hg => ?_)
          (absStep_seq
            (absStep_leafDst ls lf lfa hlf hlfa L "RCloneCall" "clone" ⟨cv, oldDest.locSrc⟩
              [oldDest.locVar])
            (absStep_leafDst ls lf lfa hlf hlfa L "RCloneCall" innerF newDest (locNames args)))
        have hg₁ := (guardsHold_append.mp hg).1
        suffices hold : ∃ old : ⟦encodeTy oldDest.locSrc⟧,
            env oldDest.locVar = some ⟨encodeTy oldDest.locSrc, old⟩ by
          obtain ⟨old, hold⟩ := hold
          rw [semScalarL_rCloneCall ls cv tt oldDest innerF newDest args env _ old hold]
          rfl
        rcases leafDstAbs_cases hg₁ with ⟨hcv, hd, _, hargs⟩ | ⟨n, hcv, henc, _⟩
        · have hT : encodeTy oldDest.locSrc = .sword 64 := by
            rw [show oldDest.locSrc = .TU64 from hd]; rfl
          have ho := hargs oldDest.locVar (List.mem_singleton_self _)
          unfold argOkB at ho
          rw [hsz, hcv] at ho
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at ho
          obtain ⟨w, hw, _⟩ := hSR.1 _ (notTmpB_sound _ ho.1) ho.2
          rw [hT]
          exact ⟨w, hw⟩
        · have hn : layoutSize L oldDest.locVar = some n := hsz.trans hcv
          obtain ⟨_, av, hav, _⟩ := hSR.2 _ (layoutSize_mem hn)
          rw [show encodeTy oldDest.locSrc = .memref n from henc]
          exact ⟨av, hav⟩
      · rw [if_neg hsz]
        exact corresUL_unsupported _ _ _ _ _
  case RCallN fname dests args =>
    show CorresUL ls fuel (SRwordL L) (guardsHold (callNTopAbsL lf lfa L fname dests args).1)
      (callNTopAbsL lf lfa L fname dests args).2 (.RCallN fname dests args)
    unfold callNTopAbsL
    rcases lf (callNLeafName fname 0) with _ | f <;> rcases lfa (callNLeafName fname 0) with _ | g
    · exact corresUL_unsupported _ _ _ _ _
    all_goals
      exact corresUL_of_absStep ls rfl (fun _ _ _ _ => rfl)
        (absStep_callN ls lf lfa hlf hlfa L fname args dests 0)
  case RSelect dst sel src0 src1 =>
    show CorresUL ls fuel (SRwordL L) (guardsHold (selectAbsL lf lfa L dst sel src0 src1).1)
      (selectAbsL lf lfa L dst sel src0 src1).2 (.RSelect dst sel src0 src1)
    unfold selectAbsL
    rcases lfa "select" with _ | g
    · exact corresUL_selectWordAbsL ls lf hlf L fuel dst sel src0 src1
    · rcases hsz : layoutSize L dst.locVar with _ | n
      · exact corresUL_selectWordAbsL ls lf hlf L fuel dst sel src0 src1
      · refine corresUL_of_absStep ls rfl (fun env a hSR hg => ?_)
          (absStep_leafDst ls lf lfa hlf hlfa L "RSelect" "select" dst
            (sel :: locNames [src0, src1]))
        rcases leafDstAbs_cases hg with ⟨hsz', _⟩ | ⟨_, _, henc, _⟩
        · rw [hsz] at hsz'; cases hsz'
        · exact semScalarL_rSelect_leafDst ls dst sel src0 src1 env henc
  case RArrStoreLit arr idx src =>
    show CorresUL ls fuel (SRwordL L) (guardsHold (arrStoreLitAbsL lf lfa L arr idx src).1)
      (arrStoreLitAbsL lf lfa L arr idx src).2 (.RArrStoreLit arr idx src)
    unfold arrStoreLitAbsL
    rcases lfa ("arrStore:" ++ toString idx) with _ | g
    · exact corresUL_arrStoreLitAbs ls L fuel arr idx src
    · by_cases hc : isU64ArrB arr.locSrc = false ∨ (layoutSize L src.locVar).isSome = true
      · rw [if_pos hc]
        refine corresUL_of_absStep ls rfl (fun env a hSR _ => ?_)
          (absStep_leafDst ls lf lfa hlf hlfa L "RArrStoreLit" ("arrStore:" ++ toString idx) arr
            (locNames [arr, src]))
        refine semScalarL_rArrStoreLit_leaf ls arr src idx env (fun k n a v harr _ hs => ?_)
        rcases hc with h | h
        · rw [harr] at h; exact absurd h (by simp [isU64ArrB])
        · exact srwordL_layout_not_word hSR h v hs
      · rw [if_neg hc]
        exact corresUL_arrStoreLitAbs ls L fuel arr idx src
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
  have h := ascendGLL_sound defaultLeaf noLeaves noArrLeaves (leavesSound_noLeaves _)
    (arrLeavesSound_noArrLeaves _) L fuel c
  rw [ascendGLL_noLeaves] at h
  exact corresUL_default_iff.mp h

/-- On a loop-free command the abstraction with abstract leaves is a `CorresL`
    correspondent. -/
theorem ascendGLL_sound_scalar (ls : SemLeafSpec) (lf : AbsLeaves) (lfa : AbsArrLeaves)
    (hlf : LeavesSound ls lf) (hlfa : ArrLeavesSound ls lfa) (L : ArrLayout) (fuel : Nat)
    (c : LowCT) (hlfr : loopFree c = true) :
    CorresL ls (SRwordL L) (guardsHold (ascendGLL lf lfa L fuel c).1)
      (ascendGLL lf lfa L fuel c).2 c := by
  intro env a hSR hP
  obtain ⟨env', hstep, hSR'⟩ := ascendGLL_sound ls lf lfa hlf hlfa L fuel c env a hSR hP
  refine ⟨env', ?_, hSR'⟩
  rw [← semUL_eq_semScalarL_of_loopFree ls fuel c hlfr]
  exact hstep

/-! ## A kernel with leaf calls

`leafK` is the literal-index read `y := B[0]` from an array `B` of type `TBytes 8`, which
is not a `u64` word array, so the front emits the opaque leaf `extCall "arrLoad:0"`,
followed by the select `r := select(s, B, y)` with an array source, which the front
emits as the opaque leaf `extCall "select"` over `s`, `B` and `y`. `TBytes 8` is encoded
as `.memref 1`. The abstract leaf `leafKAbs` is the same function at every name and
distinguishes the two nodes by the number of arguments: on one argument it is element
`0` of that argument, on three it is the first word plus element `0` of the second plus
the third word. Over the
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
    of that argument (the `"arrLoad:0"` read); on three, the word of the first plus
    element `0` of the second plus the word of the third (the `"select"` node on the
    selector and the two sources). -/
def leafKAbs (_name : String) (args : List AVal) : ZMod (2 ^ 64) :=
  match args with
  | [x] => avalElem0 x
  | [s, x, y] => avalWord s + avalElem0 x + avalWord y
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
  setVal "r" (a₁ "s" + a₁ (elemKey "B" 0) + a₁ "y") a₁

/-- The abstraction of `leafK` carries no guard. -/
theorem leafK_guards (fuel : Nat) :
    (ascendGLL leafKLeaves noArrLeaves leafLayout fuel leafK).1 = [] := by
  rfl

/-- The abstraction of `leafK` is `leafKProg`. -/
theorem leafK_prog (fuel : Nat) :
    (ascendGLL leafKLeaves noArrLeaves leafLayout fuel leafK).2 = leafKProg := by
  rfl

/-- `leafK` refines `leafKProg` over `SRwordL [("B", 1)]` at the oracle
    `leafOfAbs leafKAbs`, on every store. -/
theorem leafK_corres :
    CorresL (leafOfAbs leafKAbs) (SRwordL leafLayout) (fun _ => True) leafKProg leafK := by
  have h := ascendGLL_sound_scalar _ _ _ leavesSound_leafK (arrLeavesSound_noArrLeaves _)
    leafLayout 0 leafK rfl
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

/-- On `leafStore` the abstract program sets `r` to `0 + 7 + 7`. -/
theorem leafK_value : leafKProg leafStore "r" = 14 := by
  decide

/-! ## A kernel with array-writing and multi-destination leaves

`leafK2` writes byte `3` of the `TBytes 8` array `B` from the word `x` (the leaf
`"arrStore:3"`, an array leaf writing cell `0` of `B`), reads component `1` of the tuple
`T : TTuple TU64 TU64`, encoded as `.memref 2`, into `y` (`"tupleLoad:1"`), calls the
two-output leaf `addc` on `x, y` into `c, s` (`"callN:addc#0"`, `"callN:addc#1"`), threads
`s` through `acc` on `c, B`, calls `sw` on `c` into `x` then `y`, and clones `s` into `z`
before calling `neg` on `z` into `r`. The abstract leaves `leafK2Abs` and `leafK2ArrAbs`
are the same at every name and distinguish the nodes by the shape of the argument list.
Over the layout `[("B", 1), ("T", 2)]` at the oracle `leafOfAbsArr leafK2Abs leafK2ArrAbs`
the abstraction carries no guard (`leafK2_guards`), `leafK2_corres` refines the kernel to
`leafK2Prog`, and `leafK2_value` evaluates `leafK2Prog` on a store related to a concrete
environment (`leafK2_srwordL`). -/

/-- The layout with the one-element array `B` and the two-element tuple `T`. -/
def leafLayout2 : ArrLayout := [("B", 1), ("T", 2)]

/-- The abstract word leaf of `leafK2`, the same at every name: a word `w` alone gives
    `w + 1` (`"sw"` on `[c]`, `"clone"` on `[s]`, `"neg"` on `[z]`); an array alone gives
    its cell `1` (`"tupleLoad:1"` on `[T]`); two arguments give the sum of their words
    (`"callN:addc#0"` and `"callN:addc#1"` on `[x, y]`); three give the sum of the first
    two words and cell `0` of the third (`"acc"` on `[s, c, B]`). -/
def leafK2Abs (_name : String) (args : List AVal) : ZMod (2 ^ 64) :=
  match args with
  | [.word w] => w + 1
  | [x] => avalCell x 1
  | [x, y] => avalWord x + avalWord y
  | [x, y, z] => avalWord x + avalWord y + avalCell z 0
  | _ => 0

/-- The abstract array leaf of `leafK2`, the same at every name: cell `0` of the first
    argument becomes cell `0` of the first argument plus the word of the second
    (`"arrStore:3"` on `[B, x]`). -/
def leafK2ArrAbs (_name : String) : List AVal → Nat → ZMod (2 ^ 64) :=
  cellLeaf 0 (fun args => avalCell (args.headD .other) 0 + avalWord (args.getD 1 .other))

/-- The abstract word leaf family of `leafK2`: `leafK2Abs` at every name. -/
def leafK2Leaves : AbsLeaves := fun name => some (leafK2Abs name)

/-- The abstract array leaf family of `leafK2`: `leafK2ArrAbs` at every name. -/
def leafK2ArrLeaves : AbsArrLeaves := fun name => some (leafK2ArrAbs name)

theorem leavesSound_leafK2 :
    LeavesSound (leafOfAbsArr leafK2Abs leafK2ArrAbs) leafK2Leaves := by
  intro name f h
  cases h
  exact leafAbs_leafOfAbsArr leafK2Abs leafK2ArrAbs name

theorem arrLeavesSound_leafK2 :
    ArrLeavesSound (leafOfAbsArr leafK2Abs leafK2ArrAbs) leafK2ArrLeaves := by
  intro name g h
  cases h
  exact leafAbsArr_leafOfAbsArr leafK2Abs leafK2ArrAbs name

/-- `B[3] := x; y := T.1; (c, s) := addc(x, y); s := acc(s, c, B); (x, y) := sw(c);
    z := clone(s); r := neg(z)`. -/
def leafK2 : LowCT :=
  .RSeq (.RArrStoreLit ⟨"B", .TBytes 8⟩ 3 ⟨"x", .TU64⟩)
    (.RSeq (.RTupleLoad ⟨"y", .TU64⟩ ⟨"T", .TTuple .TU64 .TU64⟩ 1)
      (.RSeq (.RCallN "addc" [⟨"c", .TU64⟩, ⟨"s", .TU64⟩] [⟨"x", .TU64⟩, ⟨"y", .TU64⟩])
        (.RSeq (.RCallDstThreaded "acc" ⟨"s", .TU64⟩ [⟨"c", .TU64⟩, ⟨"B", .TBytes 8⟩])
          (.RSeq (.RCallSwap "sw" ⟨"x", .TU64⟩ ⟨"y", .TU64⟩ [⟨"c", .TU64⟩])
            (.RCloneCall "z" .TU64 ⟨"s", .TU64⟩ "neg" ⟨"r", .TU64⟩ [⟨"z", .TU64⟩])))))

/-- The abstract program of `leafK2`. -/
def leafK2Prog (a : AField) : AField :=
  let a₁ := setVal (elemKey "B" 0) (a (elemKey "B" 0) + a "x") a
  let a₂ := setVal "y" (a₁ (elemKey "T" 1)) a₁
  let a₃ := setVal "c" (a₂ "x" + a₂ "y") a₂
  let a₄ := setVal "s" (a₃ "x" + a₃ "y") a₃
  let a₅ := setVal "s" (a₄ "s" + a₄ "c" + a₄ (elemKey "B" 0)) a₄
  let a₆ := setVal "x" (a₅ "c" + 1) a₅
  let a₇ := setVal "y" (a₆ "c" + 1) a₆
  let a₈ := setVal "z" (a₇ "s" + 1) a₇
  setVal "r" (a₈ "z" + 1) a₈

/-- The abstraction of `leafK2` carries no guard. -/
theorem leafK2_guards (fuel : Nat) :
    (ascendGLL leafK2Leaves leafK2ArrLeaves leafLayout2 fuel leafK2).1 = [] := by
  rfl

/-- The abstraction of `leafK2` is `leafK2Prog`. -/
theorem leafK2_prog (fuel : Nat) :
    (ascendGLL leafK2Leaves leafK2ArrLeaves leafLayout2 fuel leafK2).2 = leafK2Prog := by
  rfl

/-- `leafK2` refines `leafK2Prog` over `SRwordL [("B", 1), ("T", 2)]` at the oracle
    `leafOfAbsArr leafK2Abs leafK2ArrAbs`, on every store. -/
theorem leafK2_corres :
    CorresL (leafOfAbsArr leafK2Abs leafK2ArrAbs) (SRwordL leafLayout2) (fun _ => True)
      leafK2Prog leafK2 := by
  have h := ascendGLL_sound_scalar _ _ _ leavesSound_leafK2 arrLeavesSound_leafK2 leafLayout2 0
    leafK2 rfl
  rw [leafK2_guards, leafK2_prog] at h
  intro env a hSR _
  exact h env a hSR (guardsHold_nil a)

/-- A store binding `B` to the one-element array holding `7`, `T` to the two-element
    array holding `0, 5`, `x` to `2` and every other name to the zero word. -/
def leafEnv2 : SEnvScalar :=
  fun s => if s = "B" then some ⟨.memref 1, fun _ => (7 : BitVec 64)⟩
    else if s = "T" then some ⟨.memref 2, fun j => if j = 1 then (5 : BitVec 64) else 0⟩
    else if s = "x" then some ⟨.sword 64, (2 : BitVec 64)⟩
    else some ⟨.sword 64, (0 : BitVec 64)⟩

/-- The abstract store with `B[0] = 7`, `T[1] = 5`, `x = 2` and every other name `0`. -/
def leafStore2 : AField :=
  fun s => if s = elemKey "B" 0 then 7 else if s = elemKey "T" 1 then 5
    else if s = "x" then 2 else 0

/-- The relation of `leafK2_corres` holds between `leafEnv2` and `leafStore2`. -/
theorem leafK2_srwordL : SRwordL leafLayout2 leafEnv2 leafStore2 := by
  refine ⟨fun x _ hx => ?_, fun p hp => ?_⟩
  · have hxB : x ≠ "B" := by rintro rfl; exact absurd hx (by decide)
    have hxT : x ≠ "T" := by rintro rfl; exact absurd hx (by decide)
    have hxk : x ≠ elemKey "B" 0 := by rintro rfl; exact absurd hx (by decide)
    have hxk' : x ≠ elemKey "T" 1 := by rintro rfl; exact absurd hx (by decide)
    by_cases hxx : x = "x"
    · subst hxx
      exact ⟨2, by simp [leafEnv2], by decide⟩
    · exact ⟨0, by simp [leafEnv2, hxB, hxT, hxx], by simp [wEnc, leafStore2, hxk, hxk', hxx]⟩
  · simp only [leafLayout2, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · refine ⟨notTmpB_sound "B" rfl, fun _ => 7, by simp [leafEnv2], fun j => ?_⟩
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      decide
    · refine ⟨notTmpB_sound "T" rfl, fun j => if j = 1 then 5 else 0, by simp [leafEnv2],
        fun j => ?_⟩
      fin_cases j <;> decide

/-- On `leafStore2` the abstract program sets `B[0]` to `9`, `x` to `8` and `r` to `25`. -/
theorem leafK2_value :
    leafK2Prog leafStore2 (elemKey "B" 0) = 9 ∧ leafK2Prog leafStore2 "x" = 8 ∧
      leafK2Prog leafStore2 "r" = 25 := by
  decide

end CatCrypt.Crypto.SecureCompilation.Ascent
