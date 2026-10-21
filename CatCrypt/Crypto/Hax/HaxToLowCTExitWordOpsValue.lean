/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module -- deprecated_module: ignore

public import CatCrypt.Crypto.Hax.HaxToLowCTExitWordOps
public import CatCrypt.Crypto.Hax.HaxToLowCTPlaced
public import CatCrypt.Crypto.SecureCompilation.Dialects.GuardedAgree

/-!
# The value of the scalar lowerings of the typed exit front

The typed front applies four passes to the output `c` of the typed exit front:
`scalarizeNarrowOps`, `scalarizeWordOps`, `scalarizeSignedOps` and `scalarizeExitOps`.
The first three rewrite a binding `RLetZero x t (RSeq (RCall f dest args) body)`; the
typed exit front produces no such binding (`noLetCall`), so on its output they are the
identity (`wordPasses_of_noLetCall`). The fourth, `scalarizeExitIn W I`, replaces a
marshalled word call

```
RSeq (RLetZero exitCallName dr k) (RSeq (RScalarSetExpr n (SLimb exitCallName 0)) body)
```

by the assignment `RSeq (RScalarSetExpr n se) body` of the scalar expression `se` of the
call.

This module proves that a `RustExec` run of `c` is tracked by the guarded scalar semantics
of the pass output: `semScalar` of the guarded conversion `ifConvert` of
`scalarizeExitIn W I c`, the semantics `semScalarGuarded` gives at an empty bound list.
`semScalar` itself does not model a conditional other than a φ-merge of two constants, and
the function frame `exitFunction` of the typed exit front ends in such a conditional, so the
guarded conversion is the scalar semantics of every body the front emits.

The relation `ExitScalRel c c'` states that `c'` is `c` with some marshalled calls of the
`u64` word operations `exitWordOps` replaced by their scalar expressions (`wordOpSExpr`),
over the scalar fragment of `IsCoveredSCtlGuarded` without array accesses. The leaf
semantics enters through `ExitWordLaw`: a limb store writes the word into limb `0` of a slot
of at least `8` bytes, and a call of `exitWordOps` writes the natural-number operation
`wordOpNat` of the limbs `0` of its two argument slots into limb `0`. A marshalled call is
then computed by the leaf in wrapping `u64` arithmetic, as its scalar expression is by
`SExpr.evalBV`, and no range condition is needed on it.

`RustExec` evaluates every other scalar expression over `Nat` (`SExpr.evalState`), and the
guarded semantics over `BitVec 64`. The two agree on an expression at a state when its
`Nat` value is below `2^64` and is the value of its wrapping evaluation (`ExprAgreeAt`); the
run condition `AgreeRun` asks this of every expression the run assigns. It follows from the
in-range condition `GuardedAgree.InRangeG` (`agreeRun_of_inRangeG`) and, unlike it, holds on
the masked wrapping expressions of the typed front (`widthMask 64 (SAdd a b)` on an
overflowing sum).

## Main definitions

* `ExprAgreeAt`, `AgreeRun` — the agreement of the `Nat` and wrapping evaluations.
* `exitWordOps`, `ExitWordLaw` — the word calls and the leaf law they are computed by.
* `marshalOk` — the slot sizes of a marshalled call.
* `ExitScalRel` — a program and its lowering by the pass.
* `exitScalB` — a Boolean test on the input of the pass.

## Main results

* `scalarizeSignedIn_of_noLetCall`, `wordPasses_of_noLetCall` — the three binding passes
  are the identity on the output of the typed exit front.
* `agreeRun_of_inRangeG` — the in-range condition gives the agreement condition.
* `marshal_run` — a run of a marshalled call writes the leaf value of the call slot.
* `ExitScalRel.covered` — the lowered program is in the guarded fragment.
* `exitScal_taken` — under an absent or set guard flag, the guarded conversion of the
  lowered program tracks a `RustExec` run of the input.
* `exitScal_semScalar` — the top-level form: `semScalar` of `ifConvert none S 0 c'`.
* `exitScal_semScalarGuarded` — the closed form at `semScalarGuarded`.
* `exitScalB_sound` — an input accepted by `exitScalB I` is related to its lowering by
  `scalarizeExitIn W I`.
-/

deprecated_module "haxToLowCT is the legacy hax front, outside compileA's path: compileA compiles \
  through haxToNF (Haxc.NFChain); this module remains for the SurfaceDeps bridges \
  (*HaxLowCTBridge) and the kernel producers that use it."
  (since := "2026-10-21")

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
  (EnvBoundOn ScalarInRange envReader_of_envBoundOn envBoundOn_updExpr scalarInRange_upd
    envBoundOn_mono towerOK)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLt
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuarded
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedAgree

/-! ## 1. The binding passes on the output of the typed exit front -/

theorem signedLetIn_of_notSeqCall {W I : List String} {x : String} {t : TowerType}
    {b : LowCT} (hb : notSeqCall b = true) : signedLetIn W I x t b = .RLetZero x t b := by
  rw [signedLetIn.eq_def]
  split <;> simp_all [notSeqCall]

theorem scalarizeSignedIn_of_noLetCall : ∀ (c : LowCT) (W I : List String),
    noLetCall c = true → scalarizeSignedIn W I c = c
  | .RSeq a b, W, I, h => by
    simp only [noLetCall, Bool.and_eq_true] at h
    simp [scalarizeSignedIn, scalarizeSignedIn_of_noLetCall a W I h.1,
      scalarizeSignedIn_of_noLetCall b W I h.2]
  | .RLetZero x t b, W, I, h => by
    simp only [noLetCall, Bool.and_eq_true] at h
    rw [scalarizeSignedIn, scalarizeSignedIn_of_noLetCall b _ _ h.2,
      signedLetIn_of_notSeqCall h.1]
  | .RLetU64Zero x b, W, I, h => by
    simp only [noLetCall] at h
    simp [scalarizeSignedIn, scalarizeSignedIn_of_noLetCall b _ _ h]
  | .RIfNz v a b, W, I, h => by
    simp only [noLetCall, Bool.and_eq_true] at h
    simp [scalarizeSignedIn, scalarizeSignedIn_of_noLetCall a W I h.1,
      scalarizeSignedIn_of_noLetCall b W I h.2]
  | .RWhileNz v b, W, I, h => by
    simp only [noLetCall] at h
    simp [scalarizeSignedIn, scalarizeSignedIn_of_noLetCall b W I h]
  | .RFor i n b, W, I, h => by
    simp only [noLetCall] at h
    simp [scalarizeSignedIn, scalarizeSignedIn_of_noLetCall b _ _ h]
  | .RForRuntime i e b, W, I, h => by
    simp only [noLetCall] at h
    simp [scalarizeSignedIn, scalarizeSignedIn_of_noLetCall b _ _ h]
  | .RBlock b, W, I, h => by
    simp only [noLetCall] at h
    simp [scalarizeSignedIn, scalarizeSignedIn_of_noLetCall b W I h]
  | .RSkip, _, _, _ | .RScalarSet _ _, _, _, _ | .RCall _ _ _, _, _, _
  | .RCallSwap _ _ _ _, _, _, _ | .RCloneCall _ _ _ _ _ _, _, _, _
  | .RLimbStore _ _ _, _, _, _ | .RLimbStoreExpr _ _ _, _, _, _ | .RCallN _ _ _, _, _, _
  | .RSelect _ _ _ _, _, _, _ | .RAssert _, _, _, _ | .RFnDef _ _ _ _ _, _, _, _
  | .RFnCall _ _ _, _, _, _ | .RTupleLoad _ _ _, _, _, _ | .RArrStore _ _ _, _, _, _
  | .RArrLoad _ _ _, _, _, _ | .RArrStoreLit _ _ _, _, _, _ | .RArrLoadLit _ _ _, _, _, _
  | .RScalarSetExpr _ _, _, _, _ | .RCallDstThreaded _ _ _, _, _, _
  | .RCopy _ _, _, _, _ => by simp [scalarizeSignedIn]

/-- **The binding passes on a program without a call-headed binding.** `scalarizeNarrowOps`,
    `scalarizeWordOps` and `scalarizeSignedOps S` leave a program satisfying `noLetCall`
    unchanged. -/
theorem wordPasses_of_noLetCall {c : LowCT} (h : noLetCall c = true) (S : List String) :
    scalarizeSignedOps S (scalarizeWordOps (scalarizeNarrowOps c)) = c := by
  rw [scalarize_of_noLetCall h, scalarizeSignedOps, scalarizeSignedIn_of_noLetCall c S S h]

/-! ## 2. The agreement of the `Nat` and wrapping evaluations -/

/-- The scalar expression `e` has at the scalar heap `σ` a `Nat` value below `2^64`, and
    its wrapping value at the words of `σ` is that value. -/
def ExprAgreeAt (σ : String → Nat) (e : SExpr) : Prop :=
  e.eval σ < 2 ^ 64 ∧ e.evalBV (SExpr.liftEnv σ) = BitVec.ofNat 64 (e.eval σ)

theorem exprAgreeAt_of_inRange {σ : String → Nat} {e : SExpr} (h : e.inRange σ) :
    ExprAgreeAt σ e :=
  ⟨SExpr.eval_lt_of_inRange σ e h, SExpr.evalBV_eq_ofNat_eval σ e h⟩

/-- The agreement condition of a run: every scalar expression the run of `c` from `rs`
    assigns satisfies `ExprAgreeAt` at the state it is evaluated in. -/
def AgreeRun (N : Nat) (L : LeafSpec) : LowCT → RustState → Prop
  | .RSeq a b, rs => AgreeRun N L a rs ∧ ∀ r1, RustExec N L a rs r1 → AgreeRun N L b r1
  | .RLetU64Zero x b, rs => AgreeRun N L b (rsSetScalar rs x 0)
  | .RScalarSetExpr _ e, rs => ExprAgreeAt rs.rsScalar e
  | .RIfNz g t e, rs => (rs.rsScalar g ≠ 0 → AgreeRun N L t rs) ∧
      (rs.rsScalar g = 0 → AgreeRun N L e rs)
  | _, _ => True

theorem exprAgreeAt_SLimb (σ : String → Nat) (v : String) (i : Nat) :
    ExprAgreeAt σ (.SLimb v i) :=
  ⟨by simp [SExpr.eval], by simp [SExpr.eval, SExpr.evalBV]⟩

/-- **The in-range condition gives the agreement condition.** -/
theorem agreeRun_of_inRangeG {N : Nat} {L : LeafSpec} :
    ∀ (c : LowCT) (rs : RustState), InRangeG N L c rs → AgreeRun N L c rs := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro rs h
      exact ⟨iha rs h.1, fun r1 hr1 => ihb r1 (h.2 r1 hr1)⟩
  | RLetU64Zero x b ih => intro rs h; exact ih _ h
  | RScalarSetExpr x e => intro rs h; exact exprAgreeAt_of_inRange h
  | RIfNz g t e iht ihe =>
      intro rs h
      exact ⟨fun hg => iht rs (h.1 hg), fun hg => ihe rs (h.2 hg)⟩
  | _ => intro _ _; trivial

/-! ## 3. The word calls and their leaf law -/

/-- The `u64` word calls whose natural-number operation `wordOpNat` is defined and below
    `2^64` on every pair of words. -/
def exitWordOps : List String :=
  ["wrapping_add#64", "wrapping_sub#64", "wrapping_mul#64", "mulhi#64", "BitAnd#64",
    "BitXor#64"]

theorem exitWordOps_total {f : String} (hf : f ∈ exitWordOps) (a b : Nat) :
    ∃ r, wordOpNat f a b = some r ∧ r < 2 ^ 64 := by
  simp only [exitWordOps, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, rfl, Nat.mod_lt _ (by norm_num)⟩
  · exact ⟨_, rfl, Nat.mod_lt _ (by norm_num)⟩
  · exact ⟨_, rfl, Nat.mod_lt _ (by norm_num)⟩
  · exact ⟨_, rfl, sexprMulHiU_lt _ _⟩
  · exact ⟨_, rfl, Nat.and_lt_two_pow _ (Nat.mod_lt _ (by norm_num))⟩
  · exact ⟨_, rfl, Nat.xor_lt_two_pow (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))⟩

/-- The scalar expression of a word call on two variables reads exactly the two
    variables, and is `ltClean` when they are no temporaries. -/
theorem wordOpSExpr_vars {f a b : String} {se : SExpr}
    (h : wordOpSExpr f (.SVar a) (.SVar b) = some se) :
    (∀ P : String → Prop, varsIn P se ↔ P a ∧ P b) ∧
      (¬ isTmpName a → ¬ isTmpName b → ltClean se) := by
  unfold wordOpSExpr at h
  split at h <;> (try cases h) <;>
    exact ⟨fun P => Iff.rfl, fun ha hb => ⟨ha, hb⟩⟩

/-- **The leaf law of the word calls.** A limb store at limb `0` of a slot of at least `8`
    bytes writes the word into limb `0`; a call of `exitWordOps` into a slot of at least `8`
    bytes writes into limb `0` the value `wordOpNat` gives on the limbs `0` of its two
    argument slots. -/
structure ExitWordLaw (L : LeafSpec) : Prop where
  limbStore : ∀ (loc : Located) (old : RustVal loc.locDst) (w : BitVec 64),
    8 ≤ loc.locDst.storageBytes → towerLimb (L.limbStore loc old 0 w) 0 = w.toNat
  call : ∀ f, f ∈ exitWordOps → ∀ (dt : TowerType) (dts : List TowerType) (old : RustVal dt)
    (p q : Σ t : TowerType, RustVal t) (r : Nat), 8 ≤ dt.storageBytes →
    wordOpNat f (towerLimb p.2 0) (towerLimb q.2 0) = some r →
    towerLimb (L.call f dt dts old [p, q]) 0 = r

/-! ## 4. The run of a marshalled call -/

/-- The argument slots and the call slot of the marshalled call `k` have at least `8`
    bytes. -/
def marshalOk : LowCT → Bool
  | .RLetZero _ _ (.RSeq (.RLimbStoreExpr l _ _) k) => exitMarshalOk l.locDst && marshalOk k
  | .RCall _ d _ => exitMarshalOk d.locDst
  | _ => false

/-- The argument slots a call reads, related to the scalar names the marshalling pairs
    `ms` give their slots. -/
theorem marshal_args (rs : RustState) (ms : List (String × String))
    (hinv : ∀ m x, ms.lookup m = some x →
      ∃ p, rs.rsTower m = some p ∧ towerLimb p.2 0 = rs.rsScalar x) :
    ∀ (ls : List Located) (xs : List String),
      ls.mapM (fun l => ms.lookup l.locVar) = some xs →
      (∀ a ∈ ls, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      List.Forall₂ (fun (p : Σ t : TowerType, RustVal t) x => towerLimb p.2 0 = rs.rsScalar x)
        (ls.filterMap (fun a => rs.rsTower a.locVar)) xs
  | [], xs, h, _ => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact .nil
  | l :: ls, xs, h, hty => by
    rw [List.mapM_cons] at h
    rcases hl : ms.lookup l.locVar with _ | x
    · simp [hl] at h
    · rcases hls : ls.mapM (fun l => ms.lookup l.locVar) with _ | xs'
      · simp [hl, hls] at h
      · simp only [hl, hls, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        obtain ⟨v, hv⟩ := hty l (by simp)
        obtain ⟨p, hp, hpx⟩ := hinv _ _ hl
        rw [hv] at hp
        cases hp
        rw [List.filterMap_cons, hv]
        exact .cons hpx (marshal_args rs ms hinv ls xs' hls (fun a ha => hty a (by simp [ha])))

/-- **The run of a marshalled call.** A run of a marshalled call `k` whose arguments the
    pairs `ms` and the stores of `k` give leaves the scalar heap unchanged and writes the call
    slot `exitCallName` with the leaf value of the call on argument slots whose limbs `0` are
    the scalar arguments. -/
theorem marshal_run {N : Nat} {L : LeafSpec} (hL : ExitWordLaw L) :
    ∀ (k : LowCT) (ms : List (String × String)) (f : String) (xs : List String),
      exitCallArgs ms k = some (f, xs) → marshalOk k = true →
      ∀ rs r, RustExec N L k rs r → ScalarInRange rs →
      (∀ m x, ms.lookup m = some x →
        ∃ p, rs.rsTower m = some p ∧ towerLimb p.2 0 = rs.rsScalar x) →
      r.rsScalar = rs.rsScalar ∧
        ∃ (dt : TowerType) (dts : List TowerType) (old : RustVal dt)
          (args : List (Σ t : TowerType, RustVal t)),
          8 ≤ dt.storageBytes ∧ r.rsTower exitCallName = some ⟨dt, L.call f dt dts old args⟩ ∧
          List.Forall₂ (fun (p : Σ t : TowerType, RustVal t) x => towerLimb p.2 0 = rs.rsScalar x)
            args xs := by
  intro k ms f xs
  fun_induction exitCallArgs ms k with
  | case1 ms t l x k ih =>
      intro hk hok rs r hrun hir hinv
      simp only [marshalOk, Bool.and_eq_true] at hok
      cases hrun with
      | letZero _ _ _ _ _ hb =>
        cases hb with
        | seq _ _ _ r1 _ h1 h2 =>
          cases h1 with
          | limbStoreExpr _ _ _ _ old hlk =>
            have hst : 8 ≤ l.locDst.storageBytes := of_decide_eq_true hok.1
            obtain ⟨hsc, rest⟩ := ih hk hok.2 _ r h2 hir (by
              intro m' x' hm'
              simp only [List.lookup] at hm'
              by_cases hmm : m' = l.locVar
              · subst hmm
                simp only [beq_self_eq_true, Option.some.injEq] at hm'
                subst hm'
                refine ⟨⟨l.locDst, L.limbStore l old 0 (BitVec.ofNat 64 (rs.rsScalar x))⟩,
                  ?_, ?_⟩
                · simp only [locatedUpdate]
                  exact rsSetTower_same _ _ _
                · show towerLimb (L.limbStore l old 0 (BitVec.ofNat 64 (rs.rsScalar x))) 0 =
                    rs.rsScalar x
                  rw [hL.limbStore l old _ hst, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hir x)]
              · have hne : (m' == l.locVar) = false := by simp [hmm]
                rw [hne] at hm'
                obtain ⟨p, hp, hpx⟩ := hinv m' x' hm'
                refine ⟨p, ?_, hpx⟩
                simp only [locatedUpdate]
                rw [rsSetTower_other _ _ _ _ (Ne.symm hmm), rsSetTower_other _ _ _ _ (Ne.symm hmm)]
                exact hp)
            exact ⟨hsc, rest⟩
  | case2 ms m t l x k hl =>
      intro hk
      cases hk
  | case3 ms g d ls hd =>
      intro hk hok rs r hrun hir hinv
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hk
      obtain ⟨xs', hxs, rfl, rfl⟩ := hk
      simp only [marshalOk] at hok
      cases hrun with
      | call _ _ _ _ old argList hlk hargs hty =>
        refine ⟨rfl, d.locDst, ls.map (·.locDst), old, argList, of_decide_eq_true hok, ?_, ?_⟩
        · simp only [locatedUpdate]
          rw [← hd]
          exact rsSetTower_same _ _ _
        · subst hargs
          exact marshal_args rs ms hinv ls xs' hxs hty
  | case4 ms g d ls hd =>
      intro hk
      cases hk
  | case5 =>
      intro hk
      cases hk

/-! ## 5. The relation of a program and its lowering -/

/-- `ExitScalRel c c'`: `c'` is `c` with marshalled calls of `exitWordOps` on two scalar
    names replaced by the assignment of their scalar expression, over the scalar commands of
    the guarded fragment (no array access). -/
inductive ExitScalRel : LowCT → LowCT → Prop
  | skip : ExitScalRel .RSkip .RSkip
  | scalarSet {x : String} {n : Nat} (hx : srcName x) (hn : n < 2 ^ 64) :
      ExitScalRel (.RScalarSet x n) (.RScalarSet x n)
  | scalarSetExpr {x : String} {e : SExpr} (hx : srcName x) (he : ltClean e)
      (hv : varsIn srcName e) : ExitScalRel (.RScalarSetExpr x e) (.RScalarSetExpr x e)
  | seq {a a' b b' : LowCT} : ExitScalRel a a' → ExitScalRel b b' →
      ExitScalRel (.RSeq a b) (.RSeq a' b')
  | letU64Zero {x : String} {b b' : LowCT} (hx : srcName x) : ExitScalRel b b' →
      ExitScalRel (.RLetU64Zero x b) (.RLetU64Zero x b')
  | ifNz {g : String} {t t' e e' : LowCT} (hg : srcName g) : ExitScalRel t t' →
      ExitScalRel e e' → ExitScalRel (.RIfNz g t e) (.RIfNz g t' e')
  | call {dr : TowerType} {k : LowCT} {n f a b : String} {se : SExpr} {body body' : LowCT}
      (hk : exitCallArgs [] k = some (f, [a, b])) (hf : f ∈ exitWordOps)
      (hse : wordOpSExpr f (.SVar a) (.SVar b) = some se) (hm : marshalOk k = true)
      (hn : srcName n) (ha : srcName a) (hb : srcName b) :
      ExitScalRel body body' →
      ExitScalRel
        (.RSeq (.RLetZero exitCallName dr k)
          (.RSeq (.RScalarSetExpr n (.SLimb exitCallName 0)) body))
        (.RSeq (.RScalarSetExpr n se) body')

/-- **The lowered program is in the guarded fragment**, with no array operand. -/
theorem ExitScalRel.covered {c c' : LowCT} (h : ExitScalRel c c') :
    IsCoveredSCtlGuarded c' ∧ towerOK (fun _ => False) c' := by
  induction h with
  | skip => exact ⟨.rSkip, trivial⟩
  | scalarSet hx hn => exact ⟨.rScalarSet hx hn, id⟩
  | scalarSetExpr hx he hv => exact ⟨.rScalarSetExpr hx he hv, id⟩
  | seq _ _ iha ihb => exact ⟨.rSeq iha.1 ihb.1, ⟨iha.2, ihb.2⟩⟩
  | letU64Zero hx _ ih => exact ⟨.rLetU64Zero hx ih.1, ⟨id, ih.2⟩⟩
  | ifNz hg _ _ iht ihe => exact ⟨.rIfNz hg iht.1 ihe.1, ⟨iht.2, ihe.2⟩⟩
  | call hk hf hse hm hn ha hb _ ih =>
      obtain ⟨hvars, hcl⟩ := wordOpSExpr_vars hse
      exact ⟨.rSeq (.rScalarSetExpr hn (hcl ha.1 hb.1) ((hvars srcName).mpr ⟨ha, hb⟩)) ih.1,
        ⟨id, ih.2⟩⟩

/-! ## 6. The simulation -/

theorem envBoundOn_congr {rs rs' : RustState} {env : SEnvScalar} {B : String → Prop}
    (h : rs'.rsScalar = rs.rsScalar) (he : EnvBoundOn rs env B) : EnvBoundOn rs' env B := by
  intro x hx hnt
  rw [h]
  exact he x hx hnt

theorem letZero_inv {N : Nat} {L : LeafSpec} {x : String} {t : TowerType} {b : LowCT}
    {rs r : RustState} (h : RustExec N L (.RLetZero x t b) rs r) :
    RustExec N L b (rsSetTower rs x ⟨t, default⟩) r := by
  cases h with
  | letZero _ _ _ _ _ hb => exact hb

theorem setExpr_inv {N : Nat} {L : LeafSpec} {x : String} {e : SExpr} {rs r : RustState}
    (h : RustExec N L (.RScalarSetExpr x e) rs r) : r = rsSetScalar rs x (e.evalState rs) := by
  cases h
  rfl

/-- Inversion of a run of a marshalled call followed by the copy of its limb `0`. -/
theorem seg_run_inv {N : Nat} {L : LeafSpec} {dr : TowerType} {km : LowCT} {n : String}
    {body : LowCT} {rs rs' : RustState}
    (h : RustExec N L (.RSeq (.RLetZero exitCallName dr km)
      (.RSeq (.RScalarSetExpr n (.SLimb exitCallName 0)) body)) rs rs') :
    ∃ r1, RustExec N L (.RLetZero exitCallName dr km) rs r1 ∧
      RustExec N L (.RScalarSetExpr n (.SLimb exitCallName 0)) r1
        (rsSetScalar r1 n ((SExpr.SLimb exitCallName 0).evalState r1)) ∧
      RustExec N L km (rsSetTower rs exitCallName ⟨dr, default⟩) r1 ∧
      RustExec N L body (rsSetScalar r1 n ((SExpr.SLimb exitCallName 0).evalState r1)) rs' := by
  cases h with
  | seq _ _ _ r1 _ h1 h2 =>
    cases h2 with
    | seq _ _ _ r2 _ h3 h4 =>
      rw [setExpr_inv h3] at h4
      exact ⟨r1, h1, .scalarSetExpr _ _ _, letZero_inv h1, h4⟩

/-- The scalar the copy of limb `0` of the call slot writes is a word. -/
theorem slimb_evalState_lt (r : RustState) :
    (SExpr.SLimb exitCallName 0).evalState r < 2 ^ 64 := by
  simp only [SExpr.evalState, rsTowerLimb]
  split
  · exact towerLimb_lt _ _
  · norm_num

/-- **The guarded conversion of the lowered program tracks the input's run.** Under the
    absent flag or a flag slot holding `1`, a `RustExec` run of `c` satisfying the agreement
    condition is tracked by the `semScalar` run of the guarded conversion of `c'`: its output
    environment binds every name bound after `c'` to the word of its output value. -/
theorem exitScal_taken {N : Nat} {L : LeafSpec} (hL : ExitWordLaw L) {c c' : LowCT}
    (h : ExitScalRel c c') :
    ∀ (flag : Option String) (S : List String) (k : Nat) (B : String → Prop)
      (rs rs' : RustState) (env : SEnvScalar),
      RustExec N L c rs rs' → AgreeRun N L c rs → readsG B c' →
      FlagOn flag k env → SrcList S → Bound env S → (∀ y, B y → y ∈ S) →
      EnvBoundOn rs env B → ScalarInRange rs →
      ∃ env', semScalar (ifConvert flag S k c').1 env = some env' ∧
        EnvBoundOn rs' env' (afterG B c') ∧ ScalarInRange rs' ∧
        Bound env' (ifConvert flag S k c').2.1 ∧
        (∀ i, i < k → env' (guardName i) = env (guardName i)) := by
  induction h with
  | skip =>
      intro flag S k B rs rs' env hexec _ _ _ _ hb _ henv hir
      cases hexec
      exact ⟨env, rfl, henv, hir, hb, fun _ _ => rfl⟩
  | @scalarSet x n hx hn =>
      intro flag S k B rs rs' env hexec _ _ hf hS hb _ henv hir
      cases hexec
      obtain ⟨env2, hs2, hotb⟩ := gWrite_taken (v := .SLit n) (S := S) hf hx hn trivial hb
      obtain ⟨hb1, hg1⟩ :=
        write_facts (w := (SExpr.SLit n).evalBV (envReader env)) hotb hx hS hb
      exact ⟨_, hs2, envBoundOn_updExpr henv hotb x n, scalarInRange_upd hir x hn, hb1,
        fun i _ => hg1 i⟩
  | @scalarSetExpr x e hx he _ =>
      intro flag S k B rs rs' env hexec hIR hr hf hS hb hB henv hir
      cases hexec
      rw [SExpr.evalState_eq_eval rs e (limbFree_of_ltClean e he)]
      obtain ⟨env2, hs2, hotb⟩ := gWrite_taken (v := elimLt e) (S := S) hf hx
        (srcClean_elimLt e he) (varsIn_elimLt e (varsIn_mono (bndP_of_sub hB hb) e hr)) hb
      have hval : (elimLt e).evalBV (envReader env) = BitVec.ofNat 64 (e.eval rs.rsScalar) := by
        rw [evalBV_elimLt, evalBV_congr_varsIn B (envReader env) (SExpr.liftEnv rs.rsScalar)
          (fun s hs => envReader_of_envBoundOn henv s hs (hS s (hB s hs)).1) e he hr]
        exact hIR.2
      rw [hval] at hs2
      obtain ⟨hb1, hg1⟩ :=
        write_facts (w := BitVec.ofNat 64 (e.eval rs.rsScalar)) hotb hx hS hb
      exact ⟨_, hs2, envBoundOn_updExpr henv hotb x _, scalarInRange_upd hir x hIR.1, hb1,
        fun i _ => hg1 i⟩
  | @seq a a' b b' hab _ iha ihb =>
      intro flag S k B rs rs' env hexec hIR hr hf hS hb hB henv hir
      cases hexec with
      | seq _ _ _ r1 _ h1 h2 =>
          simp only [ifConvert]
          obtain ⟨env1, hs1, henv1, hir1, hb1, hg1⟩ :=
            iha flag S k B rs r1 env h1 hIR.1 hr.1 hf hS hb hB henv hir
          obtain ⟨hSa, _, hBa, hka⟩ := ifConvert_static hab.covered.1 flag S k B hS hB
          obtain ⟨env2, hs2, henv2, hir2, hb2, hg2⟩ :=
            ihb flag (ifConvert flag S k a').2.1 (ifConvert flag S k a').2.2 (afterG B a') r1 rs'
              env1 h2 (hIR.2 r1 h1) hr.2 (flagOn_mono hf hka hg1) hSa hb1 hBa henv1 hir1
          exact ⟨env2, by rw [semScalar_seq, hs1, Option.bind_some]; exact hs2, henv2, hir2,
            hb2, fun i hi => (hg2 i (by omega)).trans (hg1 i hi)⟩
  | @letU64Zero x b b' hx _ ihb =>
      intro flag S k B rs rs' env hexec hIR hr hf hS hb hB henv hir
      cases hexec with
      | letU64Zero _ _ _ _ hbody =>
          simp only [ifConvert]
          obtain ⟨env2, hs2, hotb⟩ := gWrite_taken (v := .SLit 0) (S := S) hf hx
            (show (0 : Nat) < 2 ^ 64 by decide) trivial hb
          obtain ⟨hb1, hg1⟩ :=
            write_facts (w := (SExpr.SLit 0).evalBV (envReader env)) hotb hx hS hb
          have henv1 := envBoundOn_updExpr henv hotb x 0
          obtain ⟨env3, hs3, henv3, hir3, hb3, hg3⟩ :=
            ihb flag (x :: S) k (fun y => B y ∨ y = x) _ rs' _ hbody hIR hr
              (flagOn_mono hf (le_refl k) (fun i _ => hg1 i)) (srcList_cons hx hS) hb1
              (sub_cons x hB) henv1 (scalarInRange_upd hir x (by norm_num))
          exact ⟨env3, by rw [semScalar_seq, hs2, Option.bind_some]; exact hs3, henv3, hir3,
            hb3, fun i hi => (hg3 i hi).trans (hg1 i)⟩
  | @ifNz g t t' e e' hg htt hee iht ihe =>
      intro flag S k B rs rs' env hexec hIR hr hf hS hb hB henv hir
      obtain ⟨hg', ht', he'⟩ := hr
      obtain ⟨hct', htt'⟩ := htt.covered
      obtain ⟨hce', hte'⟩ := hee.covered
      have hgS := hB g hg'
      simp only [ifConvert]
      obtain ⟨env3, hs3, hft, hfe, hfr3⟩ := semScalar_flags (flag := flag) (k := k)
        (.RSeq (ifConvert (some (guardName k)) S (k + 2) t').1
          (ifConvert (some (guardName (k + 1))) (ifConvert (some (guardName k)) S (k + 2) t').2.1
            (ifConvert (some (guardName k)) S (k + 2) t').2.2 e').1)
        hg (hb g hgS)
        (fun f hfe => by obtain ⟨j, rfl, hj, _⟩ := hf f hfe; exact Or.inr ⟨j, rfl, hj⟩)
        (fun f hfe => by obtain ⟨j, rfl, _, h1⟩ := hf f hfe; rw [h1]; rfl)
      have hgv : envReader env g = BitVec.ofNat 64 (rs.rsScalar g) :=
        envReader_of_envBoundOn henv g hg' hg.1
      have hnz : ltWord 0#64 (envReader env g)
          = BitVec.ofNat 64 (if 0 < rs.rsScalar g then 1 else 0) := by
        rw [hgv]; exact ltWord_ofNat (by norm_num) (hir g)
      have ho : ∀ a : BitVec 64, (1 : BitVec 64) * a = a := fun a => by simp
      rw [flagVal_of_flagOn hf, ho, hnz] at hft
      rw [flagVal_of_flagOn hf, ho, hnz] at hfe
      have hpres3 : ∀ y ∈ S, env3 y = env y := fun y hy =>
        hfr3 y (hS y hy).1 (srcName_ne_guardName (hS y hy) k)
          (srcName_ne_guardName (hS y hy) (k + 1))
      have hb3 : Bound env3 S := fun y hy => by
        rw [readU64_eq_of_env (hpres3 y hy)]; exact hb y hy
      have henv3 : EnvBoundOn rs env3 B := fun y hy hnt => by
        rw [hpres3 y (hB y hy)]; exact henv y hy hnt
      have hg3 : ∀ i, i < k → env3 (guardName i) = env (guardName i) := fun i hi =>
        hfr3 _ (not_isTmpName_guardName i)
          (fun h => by have := guardName_injective h; omega)
          (fun h => by have := guardName_injective h; omega)
      obtain ⟨hSt, hsubT, _, hkt⟩ := ifConvert_static hct' (some (guardName k)) S (k + 2) B hS hB
      cases hexec with
      | ifTrue _ _ _ _ _ v hv hv0 hct =>
          have hpos : 0 < rs.rsScalar g := by subst hv; omega
          rw [if_pos hpos] at hft hfe
          obtain ⟨envT, hsT, henvT, hirT, hbT, hgT⟩ :=
            iht (some (guardName k)) S (k + 2) B rs rs' env3 hct (hIR.1 (by omega)) ht'
              (fun f hfe' => by cases hfe'; exact ⟨k, rfl, by omega, by rw [hft]; rfl⟩)
              hS hb3 hB henv3 hir
          have hfeT : envReadU64 envT (guardName (k + 1)) = some 0 := by
            rw [readU64_eq_of_env (hgT (k + 1) (by omega)), hfe]; rfl
          obtain ⟨envE, hsE, hpresE, hbE, hgE, -⟩ := ifConvert_skipped hce' (fun _ => False)
            (fun _ => .TU64) (fun _ h => h.elim) (k + 1)
            (ifConvert (some (guardName k)) S (k + 2) t').2.1
            (ifConvert (some (guardName k)) S (k + 2) t').2.2 B envT (by omega) hfeT hSt hbT
            (fun y hy => hsubT y (hB y hy)) he' hte' (arrTy_of_towerOK_false hte')
            (fun _ h => h.elim)
          refine ⟨envE, ?_, ?_, hirT, hbE, ?_⟩
          · rw [hs3, semScalar_seq, hsT, Option.bind_some]; exact hsE
          · intro y hy hnt
            rw [hpresE y (hsubT y (hB y hy))]
            exact henvT y (le_afterG t' B y hy) hnt
          · intro i hi
            rw [hgE i (by omega), hgT i (by omega)]; exact hg3 i hi
      | ifFalse _ _ _ _ _ hz hce =>
          have hnpos : ¬ 0 < rs.rsScalar g := by omega
          rw [if_neg hnpos] at hft hfe
          obtain ⟨envT, hsT, hpresT, hbT, hgT, -⟩ := ifConvert_skipped hct' (fun _ => False)
            (fun _ => .TU64) (fun _ h => h.elim) k S (k + 2) B env3 (by omega)
            (by rw [hft]; rfl) hS hb3 hB ht' htt' (arrTy_of_towerOK_false htt')
            (fun _ h => h.elim)
          have henvT : EnvBoundOn rs envT B := fun y hy hnt => by
            rw [hpresT y (hB y hy)]; exact henv3 y hy hnt
          obtain ⟨envE, hsE, henvE, hirE, hbE, hgE⟩ :=
            ihe (some (guardName (k + 1))) (ifConvert (some (guardName k)) S (k + 2) t').2.1
              (ifConvert (some (guardName k)) S (k + 2) t').2.2 B rs rs' envT hce (hIR.2 hz) he'
              (fun f hfe' => by
                cases hfe'
                exact ⟨k + 1, rfl, by omega, by
                  rw [readU64_eq_of_env (hgT (k + 1) (by omega)), hfe]; rfl⟩)
              hSt hbT (fun y hy => hsubT y (hB y hy)) henvT hir
          refine ⟨envE, ?_, envBoundOn_mono henvE (fun y hy => le_afterG e' B y hy), hirE, hbE,
            ?_⟩
          · rw [hs3, semScalar_seq, hsT, Option.bind_some]; exact hsE
          · intro i hi
            rw [hgE i (by omega), hgT i (by omega)]; exact hg3 i hi
  | @call dr km n f a b se body body' hk hf hse hm hn ha hb _ ihb =>
      intro flag S k B rs rs' env hexec hIR hr hfl hS hbd hB henv hir
      obtain ⟨hvars, hcl⟩ := wordOpSExpr_vars hse
      have hcl' : ltClean se := hcl ha.1 hb.1
      obtain ⟨hBa, hBb⟩ := (hvars B).mp hr.1
      obtain ⟨r1, h1, h3, hk1, h4⟩ := seg_run_inv hexec
      have hIRb := (hIR.2 r1 h1).2 _ h3
      obtain ⟨hsc, dt, dts, old, args, hdt, htw, hF⟩ :=
        marshal_run hL km [] f [a, b] hk hm _ r1 hk1 hir (fun _ _ h => by cases h)
      obtain ⟨pa, pb, rfl, hpa, hpb⟩ : ∃ pa pb, args = [pa, pb] ∧
          towerLimb pa.2 0 = rs.rsScalar a ∧ towerLimb pb.2 0 = rs.rsScalar b := by
        cases hF with
        | cons h1 hF =>
          cases hF with
          | cons h2 hF => cases hF; exact ⟨_, _, rfl, h1, h2⟩
      obtain ⟨r, hr0, hrlt⟩ := exitWordOps_total hf (rs.rsScalar a) (rs.rsScalar b)
      have hlimb : towerLimb (L.call f dt dts old [pa, pb]) 0 = r :=
        hL.call f hf dt dts old pa pb r hdt (by rw [hpa, hpb]; exact hr0)
      have hval_n : (SExpr.SLimb exitCallName 0).evalState r1 = r := by
        simp only [SExpr.evalState, rsTowerLimb, htw]
        exact hlimb
      have hsev : se.evalBV (SExpr.liftEnv rs.rsScalar) = BitVec.ofNat 64 r := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrlt]
        refine wordOpSExpr_evalBV (SExpr.liftEnv rs.rsScalar) hse ?_ hrlt
        simp only [SExpr.evalBV, SExpr.liftEnv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hir a),
          Nat.mod_eq_of_lt (hir b)]
        exact hr0
      obtain ⟨env2, hs2, hotb⟩ := gWrite_taken (v := elimLt se) (S := S) hfl hn
        (srcClean_elimLt se hcl') (varsIn_elimLt se (varsIn_mono (bndP_of_sub hB hbd) se hr.1))
        hbd
      have hval : (elimLt se).evalBV (envReader env) = BitVec.ofNat 64 r := by
        rw [evalBV_elimLt, evalBV_congr_varsIn B (envReader env) (SExpr.liftEnv rs.rsScalar)
          (fun s hs => envReader_of_envBoundOn henv s hs (hS s (hB s hs)).1) se hcl' hr.1]
        exact hsev
      rw [hval] at hs2
      obtain ⟨hb1, hg1⟩ := write_facts (w := BitVec.ofNat 64 r) hotb hn hS hbd
      have henv1 : EnvBoundOn (rsSetScalar r1 n ((SExpr.SLimb exitCallName 0).evalState r1))
          (env2.upd n (t := .sword 64) (BitVec.ofNat 64 r)) (fun y => B y ∨ y = n) := by
        refine envBoundOn_congr ?_ (envBoundOn_updExpr henv hotb n r)
        funext y
        simp only [rsSetScalar, hval_n, hsc]
        rfl
      have hir1 : ScalarInRange (rsSetScalar r1 n ((SExpr.SLimb exitCallName 0).evalState r1)) := by
        intro y
        simp only [rsSetScalar, hval_n]
        split
        · exact hrlt
        · rw [hsc]; exact hir y
      obtain ⟨env3, hs3, henv3, hir3, hb3, hg3⟩ :=
        ihb flag (n :: S) k (fun y => B y ∨ y = n) _ rs' _ h4 hIRb hr.2
          (flagOn_mono hfl (le_refl k) (fun i _ => hg1 i)) (srcList_cons hn hS) hb1
          (sub_cons n hB) henv1 hir1
      simp only [ifConvert]
      exact ⟨env3, by rw [semScalar_seq, hs2, Option.bind_some]; exact hs3, henv3, hir3,
        hb3, fun i hi => (hg3 i hi).trans (hg1 i)⟩

/-- **The lowered program at top level.** A `RustExec` run of `c` satisfying the agreement
    condition, from a state whose scalars are words and which the environment `env` reflects
    on the names `B`, is tracked by `semScalar` of the guarded conversion of `c'` from the
    bound list `S ⊇ B`: its output environment binds every name bound after `c'` to the
    word of its output value. -/
theorem exitScal_semScalar {N : Nat} {L : LeafSpec} (hL : ExitWordLaw L) {c c' : LowCT}
    (h : ExitScalRel c c') {S : List String} {B : String → Prop} {rs rs' : RustState}
    {env : SEnvScalar} (hexec : RustExec N L c rs rs') (hag : AgreeRun N L c rs)
    (hreads : readsG B c') (hS : SrcList S) (hb : Bound env S) (hB : ∀ y, B y → y ∈ S)
    (henv : EnvBoundOn rs env B) (hir : ScalarInRange rs) :
    ∃ env', semScalar (ifConvert none S 0 c').1 env = some env' ∧
      EnvBoundOn rs' env' (afterG B c') ∧ ScalarInRange rs' := by
  obtain ⟨env', hs, henv', hir', _, _⟩ := exitScal_taken hL h none S 0 B rs rs' env hexec hag
    hreads (fun _ h => by cases h) hS hb hB henv hir
  exact ⟨env', hs, henv', hir'⟩

/-- **The closed form.** For a lowered program every read of which follows a write, a
    `RustExec` run of `c` satisfying the agreement condition from a state whose scalars are
    words is tracked by `semScalarGuarded c'` from the empty environment. -/
theorem exitScal_semScalarGuarded {N : Nat} {L : LeafSpec} (hL : ExitWordLaw L)
    {c c' : LowCT} (h : ExitScalRel c c') {rs rs' : RustState}
    (hexec : RustExec N L c rs rs') (hag : AgreeRun N L c rs)
    (hreads : readsG (fun _ => False) c') (hir : ScalarInRange rs) :
    ∃ env', semScalarGuarded c' (fun _ => none) = some env' ∧
      EnvBoundOn rs' env' (afterG (fun _ => False) c') ∧ ScalarInRange rs' :=
  exitScal_semScalar hL h hexec hag hreads (fun _ h => by cases h) (fun _ h => by cases h)
    (fun _ h => h.elim) (fun _ h => h.elim) hir

/-! ## 7. The Boolean test on the input of the pass -/

/-- The Boolean test on the input `c` of `scalarizeExitIn W I`: the scalar commands of the
    guarded fragment over source names, no signed comparison `signedCmpFix I` rewrites, and
    marshalled calls of `exitWordOps` on two source names with slots of at least `8` bytes. -/
def exitScalB (I : List String) : LowCT → Bool
  | .RSeq (.RLetZero c _ k) (.RSeq (.RScalarSetExpr n (.SLimb c' 0)) b) =>
      decide (c = exitCallName) && decide (c' = exitCallName) && marshalOk k && srcNameB n &&
        (match exitCallArgs [] k with
          | some (f, [x, y]) => exitWordOps.contains f && srcNameB x && srcNameB y
          | _ => false) && exitScalB I b
  | .RSeq a b => exitScalB I a && exitScalB I b
  | .RLetU64Zero x b => srcNameB x && exitScalB I b
  | .RIfNz g t e => srcNameB g && exitScalB I t && exitScalB I e
  | .RScalarSetExpr x e => (signedCmpFix I e).isNone && srcNameB x && ltCleanSrcB e
  | .RScalarSet x n => srcNameB x && decide (n < 2 ^ 64)
  | .RSkip => true
  | _ => false

theorem wordOpSExpr_of_mem {f : String} (hf : f ∈ exitWordOps) (a b : SExpr) :
    ∃ se, wordOpSExpr f a b = some se := by
  simp only [exitWordOps, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- **The pass on an accepted input.** An input `c` accepted by `exitScalB I` is related by
    `ExitScalRel` to its lowering `scalarizeExitIn W I c`. -/
theorem exitScalB_sound (W I : List String) :
    ∀ c : LowCT, exitScalB I c = true → ExitScalRel c (scalarizeExitIn W I c) := by
  intro c
  fun_induction exitScalB I c with
  | case1 c dr k n c' b ih =>
      intro h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨hc, hc'⟩, hm⟩, hn⟩, hcall⟩, hb⟩ := h
      subst hc hc'
      split at hcall
      · rename_i f x y hk
        simp only [Bool.and_eq_true, List.contains_iff_mem] at hcall
        obtain ⟨⟨hf, hx⟩, hy⟩ := hcall
        obtain ⟨se, hse⟩ := wordOpSExpr_of_mem hf (.SVar x) (.SVar y)
        have hlow : exitLowerCall W I exitCallName exitCallName k = some se := by
          simp only [exitLowerCall, and_self, if_true, hk, Option.bind_some]
          exact exitOpSExpr_word hse
        rw [scalarizeExitIn, hlow]
        exact .call hk hf hse hm (srcName_of_srcNameB hn) (srcName_of_srcNameB hx)
          (srcName_of_srcNameB hy) (ih hb)
      · cases hcall
  | case2 a b hne iha ihb =>
      intro h
      simp only [Bool.and_eq_true] at h
      rw [scalarizeExitIn.eq_def]
      split
      · rename_i c₀ dr₀ k₀ n₀ c₀' b₀ heq
        simp only [LowCT.RSeq.injEq] at heq
        exact (hne _ _ _ _ _ _ heq.1 heq.2).elim
      · rename_i heq
        cases heq
      · rename_i a' b' _ heq
        simp only [LowCT.RSeq.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact .seq (iha h.1) (ihb h.2)
      all_goals simp_all
  | case3 x b ih =>
      intro h
      simp only [Bool.and_eq_true] at h
      simp only [scalarizeExitIn]
      exact .letU64Zero (srcName_of_srcNameB h.1) (ih h.2)
  | case4 g t e iht ihe =>
      intro h
      simp only [Bool.and_eq_true] at h
      simp only [scalarizeExitIn]
      exact .ifNz (srcName_of_srcNameB h.1.1) (iht h.1.2) (ihe h.2)
  | case5 x e =>
      intro h
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
      obtain ⟨⟨hfix, hx⟩, he⟩ := h
      simp only [scalarizeExitIn, hfix, Option.getD_none]
      exact .scalarSetExpr (srcName_of_srcNameB hx) (ltCleanSrcB_sound e he).1
        (ltCleanSrcB_sound e he).2
  | case6 x n =>
      intro h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [scalarizeExitIn]
      exact .scalarSet (srcName_of_srcNameB h.1) h.2
  | case7 =>
      intro _
      simp only [scalarizeExitIn]
      exact .skip
  | case8 =>
      intro h
      simp_all

/-! ## 8. Expressions agreeing at every heap of words -/

/-- A sum or product of variables and literals: its wrapping value is the image of its
    `Nat` value under `BitVec.ofNat 64` at every heap. -/
def homB : SExpr → Bool
  | .SVar _ | .SLit _ => true
  | .SAdd a b | .SMul a b => homB a && homB b
  | _ => false

theorem homB_sound : ∀ e : SExpr, homB e = true →
    ∀ σ : String → Nat, e.evalBV (SExpr.liftEnv σ) = BitVec.ofNat 64 (e.eval σ) := by
  intro e
  induction e with
  | SVar x => intro _ σ; rfl
  | SLit n => intro _ σ; rfl
  | SAdd a b iha ihb =>
      intro h σ
      simp only [homB, Bool.and_eq_true] at h
      simp only [SExpr.evalBV, SExpr.eval, iha h.1 σ, ihb h.2 σ, BitVec.ofNat_add]
  | SMul a b iha ihb =>
      intro h σ
      simp only [homB, Bool.and_eq_true] at h
      simp only [SExpr.evalBV, SExpr.eval, iha h.1 σ, ihb h.2 σ, BitVec.ofNat_mul]
  | _ => intro h; simp [homB] at h

/-- The literal `2^64 - 1`, the mask of a `u64`. -/
def isMask64 : SExpr → Bool
  | .SLit m => m == 2 ^ 64 - 1
  | _ => false

/-- A right-shift count the check accepts: a literal below 64. The word shift masks its count
    (`shiftMask 64`) while the natural-number shift does not, so the two agree only below 64. -/
def shrCountOk : SExpr → Bool
  | .SLit k => decide (k < 64)
  | _ => false

theorem eval_lt_of_shrCountOk {σ : String → Nat} : ∀ {b : SExpr}, shrCountOk b = true →
    b.eval σ < 64
  | .SLit k, h => by simpa [shrCountOk, SExpr.eval] using h

/-- The expressions that agree at every heap of words (`agreeAllB_sound`): variables,
    literals below `2^64`, limb reads, a sum or product of variables and literals masked to
    `64` bits, the wrapping difference `((a + (2^64 - 1) - b) + 1) &&& (2^64 - 1)` of agreeing
    expressions, conjunctions, exclusive disjunctions, right shifts, comparisons and high
    product words `SMulHiU` of agreeing expressions, the complement `1 - (a < b)` and the sum
    `(a < b) + (c < d)` of comparisons. -/
def agreeAllB : SExpr → Bool
  | .SAnd (.SAdd (.SSub (.SAdd a (.SLit m)) b) (.SLit 1)) (.SLit m') =>
      isMask64 (.SLit m) && isMask64 (.SLit m') && agreeAllB a && agreeAllB b
  | .SVar _ => true
  | .SLit n => decide (n < 2 ^ 64)
  | .SLimb _ _ => true
  | .SAnd a b => (homB a && isMask64 b) || (agreeAllB a && agreeAllB b)
  | .SXor a b => agreeAllB a && agreeAllB b
  | .SShr a b => agreeAllB a && agreeAllB b && shrCountOk b
  | .SLt a b => agreeAllB a && agreeAllB b
  | .SSub (.SLit 1) (.SLt a b) => agreeAllB a && agreeAllB b
  | .SAdd (.SLt a b) (.SLt c d) => agreeAllB a && agreeAllB b && agreeAllB c && agreeAllB d
  | .SMulHiU a b => agreeAllB a && agreeAllB b
  | _ => false

theorem exprAgreeAt_lt {σ : String → Nat} {a b : SExpr} (ha : ExprAgreeAt σ a)
    (hb : ExprAgreeAt σ b) : ExprAgreeAt σ (.SLt a b) ∧
      (SExpr.SLt a b).eval σ ≤ 1 := by
  have hA : (a.evalBV (SExpr.liftEnv σ)).toNat = a.eval σ := by
    rw [ha.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha.1]
  have hB : (b.evalBV (SExpr.liftEnv σ)).toNat = b.eval σ := by
    rw [hb.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb.1]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [SExpr.eval]; split <;> norm_num
  · simp only [SExpr.evalBV, SExpr.eval, hA, hB]; split <;> rfl
  · simp only [SExpr.eval]; split <;> norm_num

/-- The wrapping difference `((a + (2^64 - 1) - b) + 1) &&& (2^64 - 1)` of agreeing
    expressions agrees. -/
theorem exprAgreeAt_wrapSub {σ : String → Nat} {a b : SExpr} (ha : ExprAgreeAt σ a)
    (hb : ExprAgreeAt σ b) :
    ExprAgreeAt σ (.SAnd (.SAdd (.SSub (.SAdd a (.SLit (2 ^ 64 - 1))) b) (.SLit 1))
      (.SLit (2 ^ 64 - 1))) := by
  obtain ⟨ha, ha2⟩ := ha
  obtain ⟨hb, hb2⟩ := hb
  have hM : (2 ^ 64 - 1) % 2 ^ 64 = 2 ^ 64 - 1 := Nat.mod_eq_of_lt (by omega)
  have he : (SExpr.SAnd (.SAdd (.SSub (.SAdd a (.SLit (2 ^ 64 - 1))) b) (.SLit 1))
      (.SLit (2 ^ 64 - 1))).eval σ = (a.eval σ + (2 ^ 64 - 1) - b.eval σ + 1) % 2 ^ 64 := by
    rw [← Nat.and_two_pow_sub_one_eq_mod]
    rfl
  rw [ExprAgreeAt, he]
  refine ⟨Nat.mod_lt _ (by omega), ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [SExpr.evalBV, SExpr.evalBV, SExpr.evalBV, SExpr.evalBV, SExpr.evalBV, SExpr.evalBV,
    SExpr.evalBV, ha2, hb2, BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_sub,
    BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, hM, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  omega

/-- The right shift of agreeing expressions agrees. -/
theorem exprAgreeAt_shr {σ : String → Nat} {a b : SExpr} (ha : ExprAgreeAt σ a)
    (hb : ExprAgreeAt σ b) (hb64 : b.eval σ < 64) : ExprAgreeAt σ (.SShr a b) := by
  obtain ⟨ha, ha2⟩ := ha
  obtain ⟨hb, hb2⟩ := hb
  have hlt : a.eval σ >>> b.eval σ < 2 ^ 64 := lt_of_le_of_lt (Nat.shiftRight_le _ _) ha
  refine ⟨hlt, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [SExpr.evalBV, SExpr.eval, ha2, hb2, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hlt,
    SecureCompilation.VIR.shiftMask_of_lt hb64]

/-- **Agreement at every heap of words.** -/
theorem agreeAllB_sound : ∀ e : SExpr, agreeAllB e = true →
    ∀ σ : String → Nat, (∀ y, σ y < 2 ^ 64) → ExprAgreeAt σ e := by
  intro e
  fun_induction agreeAllB e with
  | case1 a m b m' iha ihb =>
      intro h σ hσ
      simp only [Bool.and_eq_true, isMask64, beq_iff_eq] at h
      obtain ⟨⟨⟨rfl, rfl⟩, ha⟩, hb⟩ := h
      exact exprAgreeAt_wrapSub (iha ha σ hσ) (ihb hb σ hσ)
  | case2 x => intro _ σ hσ; exact ⟨hσ x, rfl⟩
  | case3 n =>
      intro h σ _
      have hn : n < 2 ^ 64 := of_decide_eq_true h
      exact ⟨hn, rfl⟩
  | case4 v i => intro _ σ _; exact exprAgreeAt_SLimb σ v i
  | case5 a b _ iha ihb =>
      intro h σ hσ
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨hh, hm⟩ | ⟨ha, hb⟩
      · cases b with
        | SLit m =>
            simp only [isMask64, beq_iff_eq] at hm
            subst hm
            have hv := homB_sound a hh σ
            have hmod : a.eval σ &&& (2 ^ 64 - 1) = a.eval σ % 2 ^ 64 :=
              Nat.and_two_pow_sub_one_eq_mod _ 64
            refine ⟨?_, ?_⟩
            · simp only [SExpr.eval, hmod]; exact Nat.mod_lt _ (by norm_num)
            · apply BitVec.eq_of_toNat_eq
              simp only [SExpr.evalBV, SExpr.eval, hv, BitVec.toNat_and, BitVec.toNat_ofNat, hmod]
              rw [Nat.mod_eq_of_lt (show 2 ^ 64 - 1 < 2 ^ 64 by norm_num),
                Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
        | _ => simp [isMask64] at hm
      · have hA := iha ha σ hσ
        have hB := ihb hb σ hσ
        have hlt : a.eval σ &&& b.eval σ < 2 ^ 64 := Nat.and_lt_two_pow _ hB.1
        refine ⟨hlt, ?_⟩
        apply BitVec.eq_of_toNat_eq
        simp only [SExpr.evalBV, SExpr.eval, hA.2, hB.2, BitVec.toNat_and, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hA.1, Nat.mod_eq_of_lt hB.1, Nat.mod_eq_of_lt hlt]
  | case6 a b iha ihb =>
      intro h σ hσ
      simp only [Bool.and_eq_true] at h
      have hA := iha h.1 σ hσ
      have hB := ihb h.2 σ hσ
      have hlt : a.eval σ ^^^ b.eval σ < 2 ^ 64 := Nat.xor_lt_two_pow hA.1 hB.1
      refine ⟨hlt, ?_⟩
      apply BitVec.eq_of_toNat_eq
      simp only [SExpr.evalBV, SExpr.eval, hA.2, hB.2, BitVec.toNat_xor, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hA.1, Nat.mod_eq_of_lt hB.1, Nat.mod_eq_of_lt hlt]
  | case7 a b iha ihb =>
      intro h σ hσ
      simp only [Bool.and_eq_true] at h
      exact exprAgreeAt_shr (iha h.1.1 σ hσ) (ihb h.1.2 σ hσ) (eval_lt_of_shrCountOk h.2)
  | case8 a b iha ihb =>
      intro h σ hσ
      simp only [Bool.and_eq_true] at h
      exact (exprAgreeAt_lt (iha h.1 σ hσ) (ihb h.2 σ hσ)).1
  | case9 a b iha ihb =>
      intro h σ hσ
      simp only [Bool.and_eq_true] at h
      obtain ⟨hl, hle⟩ := exprAgreeAt_lt (iha h.1 σ hσ) (ihb h.2 σ hσ)
      refine ⟨by simp only [SExpr.eval]; omega, ?_⟩
      apply BitVec.eq_of_toNat_eq
      have hl2 := hl.2
      simp only [SExpr.evalBV, SExpr.eval] at hl2 ⊢
      rw [hl2]
      simp only [SExpr.eval] at hle
      split <;> simp_all
  | case10 a b c d iha ihb ihc ihd =>
      intro h σ hσ
      simp only [Bool.and_eq_true] at h
      obtain ⟨h1, h1le⟩ := exprAgreeAt_lt (iha h.1.1.1 σ hσ) (ihb h.1.1.2 σ hσ)
      obtain ⟨h2, h2le⟩ := exprAgreeAt_lt (ihc h.1.2 σ hσ) (ihd h.2 σ hσ)
      refine ⟨by simp only [SExpr.eval] at h1le h2le ⊢; omega, ?_⟩
      show (SExpr.SLt a b).evalBV _ + (SExpr.SLt c d).evalBV _ =
        BitVec.ofNat 64 ((SExpr.SLt a b).eval σ + (SExpr.SLt c d).eval σ)
      rw [h1.2, h2.2, BitVec.ofNat_add]
  | case11 a b iha ihb =>
      intro h σ hσ
      simp only [Bool.and_eq_true] at h
      have hA := iha h.1 σ hσ
      have hB := ihb h.2 σ hσ
      refine ⟨sexprMulHiU_lt _ _, ?_⟩
      simp only [SExpr.evalBV, SExpr.eval, hA.2, hB.2, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hA.1, Nat.mod_eq_of_lt hB.1]
  | case12 =>
      intro h
      simp_all

/-- Every scalar expression `c` assigns agrees at every heap of words (`agreeAllB`). -/
def setExprsAgreeB : LowCT → Bool
  | .RSeq a b => setExprsAgreeB a && setExprsAgreeB b
  | .RLetU64Zero _ b => setExprsAgreeB b
  | .RIfNz _ t e => setExprsAgreeB t && setExprsAgreeB e
  | .RScalarSetExpr _ e => agreeAllB e
  | _ => true

/-- A run of a related input whose expressions agree at every heap of words keeps the
    scalars words. -/
theorem exitScal_inRange {N : Nat} {L : LeafSpec} (hL : ExitWordLaw L) {c c' : LowCT}
    (h : ExitScalRel c c') :
    setExprsAgreeB c = true → ∀ rs r, RustExec N L c rs r → ScalarInRange rs →
      ScalarInRange r := by
  induction h with
  | skip => intro _ rs r hr hir; cases hr; exact hir
  | scalarSet hx hn => intro _ rs r hr hir; cases hr; exact scalarInRange_upd hir _ hn
  | @scalarSetExpr x e hx he _ =>
      intro ha rs r hr hir
      cases hr
      rw [SExpr.evalState_eq_eval rs e (limbFree_of_ltClean e he)]
      exact scalarInRange_upd hir x (agreeAllB_sound e ha rs.rsScalar hir).1
  | seq _ _ iha ihb =>
      intro ha rs r hr hir
      simp only [setExprsAgreeB, Bool.and_eq_true] at ha
      cases hr with
      | seq _ _ _ r1 _ h1 h2 => exact ihb ha.2 r1 r h2 (iha ha.1 rs r1 h1 hir)
  | letU64Zero hx _ ih =>
      intro ha rs r hr hir
      cases hr with
      | letU64Zero _ _ _ _ hb => exact ih ha _ r hb (scalarInRange_upd hir _ (by norm_num))
  | ifNz hg _ _ iht ihe =>
      intro ha rs r hr hir
      simp only [setExprsAgreeB, Bool.and_eq_true] at ha
      cases hr with
      | ifTrue _ _ _ _ _ _ _ _ hct => exact iht ha.1 rs r hct hir
      | ifFalse _ _ _ _ _ _ hce => exact ihe ha.2 rs r hce hir
  | @call dr km n f a b se body body' hk hf hse hm hn ha hb _ ih =>
      intro hag rs r hr hir
      have hbody : setExprsAgreeB body = true := by simpa [setExprsAgreeB, agreeAllB] using hag
      obtain ⟨r1, -, -, hk1, h4⟩ := seg_run_inv hr
      obtain ⟨hsc, -⟩ := marshal_run hL km [] f [a, b] hk hm _ r1 hk1 hir
        (fun _ _ h => by cases h)
      refine ih hbody _ r h4 ?_
      intro y
      simp only [rsSetScalar]
      split
      · exact slimb_evalState_lt r1
      · rw [hsc]; exact hir y

/-- **The agreement condition from the expressions.** For a related input every scalar
    expression of which agrees at every heap of words (`setExprsAgreeB`), every run from a
    state whose scalars are words satisfies the agreement condition. -/
theorem agreeRun_of_setExprsAgreeB {N : Nat} {L : LeafSpec} (hL : ExitWordLaw L)
    {c c' : LowCT} (h : ExitScalRel c c') :
    setExprsAgreeB c = true → ∀ rs, ScalarInRange rs → AgreeRun N L c rs := by
  induction h with
  | skip => intro _ _ _; trivial
  | scalarSet => intro _ _ _; trivial
  | @scalarSetExpr x e _ _ _ =>
      intro ha rs hir
      exact agreeAllB_sound e ha rs.rsScalar hir
  | @seq a a' b b' hab _ iha ihb =>
      intro ha rs hir
      simp only [setExprsAgreeB, Bool.and_eq_true] at ha
      exact ⟨iha ha.1 rs hir, fun r1 h1 => ihb ha.2 r1 (exitScal_inRange hL hab ha.1 rs r1 h1 hir)⟩
  | letU64Zero _ _ ih =>
      intro ha rs hir
      exact ih ha _ (scalarInRange_upd hir _ (by norm_num))
  | ifNz _ _ _ iht ihe =>
      intro ha rs hir
      simp only [setExprsAgreeB, Bool.and_eq_true] at ha
      exact ⟨fun _ => iht ha.1 rs hir, fun _ => ihe ha.2 rs hir⟩
  | @call dr km n f a b se body body' hk hf hse hm hn ha hb hrel ih =>
      intro hag rs hir
      have hbody : setExprsAgreeB body = true := by simpa [setExprsAgreeB, agreeAllB] using hag
      refine ⟨trivial, fun r1 h1 => ⟨exprAgreeAt_SLimb _ _ _, fun r2 h3 => ?_⟩⟩
      rw [setExpr_inv h3]
      obtain ⟨hsc, -⟩ := marshal_run hL km [] f [a, b] hk hm _ r1 (letZero_inv h1) hir
        (fun _ _ h => by cases h)
      refine ih hbody _ ?_
      intro y
      simp only [rsSetScalar]
      split
      · exact slimb_evalState_lt r1
      · rw [hsc]; exact hir y

end CatCrypt.Crypto.Hax
