/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.HaxToLowCTExitWordOpsValueLoop

/-!
# The word-array scalarisation of the typed exit front

The typed exit front lowers an element access of a `u64` word array through a tower slot.
A load of element `i` of the array `s` into the scalar `a` is

```
RLetZero c TFp (RSeq (RArrLoad ⟨c, TFp⟩ ⟨s, TArr n TU64⟩ i) (RSeq (RScalarSetExpr a (SLimb c 0)) k))
```

(the element is loaded into the zeroed slot `c` and its limb `0` copied into `a`), and a
store of the scalar `x` into element `i` of the array `arr` is

```
RLetZero m TU64 (RSeq (RLimbStoreExpr ⟨m, TU64⟩ 0 (SVar x)) (RArrStore ⟨arr, TArr n TU64⟩ i ⟨m, TU64⟩))
```

(the scalar is marshalled into limb `0` of the zeroed word slot `m`, which is stored).
`scalarizeArrIn` replaces the load by `RSeq (RSeq (RScalarSet a 0) (RArrLoad ⟨a, TU64⟩ ⟨s,
TArr n TU64⟩ i)) k` and the store by `RArrStore ⟨arr, TArr n TU64⟩ i ⟨x, TU64⟩`: word-array
accesses through a `TU64` word slot, the arms of the guarded fragment `IsCoveredSCtlGuarded`.
The zero write binds `a` before the load, so the guarded conversion `ifConvert` reads it as a
bound word.

The relation `ExitArrRel T c c'` states that `c'` is `c` with such accesses of the arrays
named by `T` replaced, over the scalar commands of the guarded fragment without conditionals;
every scalar expression passes `agreeWordB`, so its `Nat` value and its wrapping value agree
at every heap of words. A `RustExec` run of `c` is tracked by `semScalar` of the guarded
conversion of `c'` (`exitArr_taken`, `exitArr_semScalar`). The arrays of the run and of the
environment are related through a word view `ArrView L` of the leaf semantics `L`: the view of
each array of `T` in the run is the memref the environment binds (`ArrOn`), a load of an
element in bounds reads limb `0` of the view's word, and a store of a marshalled word in
bounds writes it into the view. Every access of the run is in bounds (`ArrRun`).

`ExitArrRelL` adds runtime-count loops on the spine of sequences and word binders, whose trip
bodies are related by `ExitArrRel`; a run is tracked by the guarded semantics with loops
`GuardedRouteSeq.semG` (`exitArrL_semG`).

The exit frame of a function returning an array ends in a tail that resets the return flag
`r`, copies the array into the result slot `s` (`RCopy`) and tests the flag; its run loop
guards every trip by the flag and counts to `n - 0`. `exitFrameNorm` removes the tail, the
trip guard (when the trip body leaves the flag unwritten) and the `- 0`, so that the program
is binders around one runtime-count loop over a count variable, the shape the loop route of
the compiler reads. A run of the frame gives a run of the normalised program ending in a state
that agrees with it off `r` and `s` and whose array is the result slot's value
(`exitFrameNorm_run`). `exitArrLower` is the normalisation followed by the scalarisation, with
its check `exitArrOk` and its value theorem `exitArrLower_semG`.

## Main definitions

* `scalarizeArrIn` — the pass.
* `ArrView` — a word view of the arrays of a leaf semantics, with its load and store laws.
* `ArrOn`, `ArrRun`, `readsA` — the array relation, the bounds condition of a run and the
  read condition of the output.
* `agreeWordB` — the expressions whose `Nat` and wrapping values agree at every heap of words.
* `ExitArrRel`, `ExitArrRelL` — a program and its scalarisation, without and with loops.
* `exitArrB`, `exitArrBL` — the Boolean tests on the input of the pass.
* `ArrRunL`, `readsAL` — the bounds and read conditions with loops.
* `scalarKeepsB`, `exitRunNorm`, `exitFrameTail`, `exitFrameNorm` — the exit-frame
  normalisation.
* `arrNames`, `exitArrLower`, `exitArrOk` — the word-array lowering and its check.

## Main results

* `ExitArrRel.covered` — the scalarised program is in the guarded fragment.
* `exitArr_taken` — under an absent or set guard flag, the guarded conversion of the
  scalarised program tracks a `RustExec` run of the input.
* `exitArr_semScalar` — the top-level form: `semScalar` of `ifConvert none S 0 c'`.
* `exitArrB_sound`, `exitArrBL_sound` — an accepted input is related to its scalarisation, at
  the array names `Ts`.
* `exitArrLoop_trips`, `exitArrL_semG` — the trip fold and `semG` track a run with loops.
* `rustExec_scalarKeeps`, `rFor_guard_elim`, `exitRunNorm_run`, `exitFrameNorm_run` — the
  runs of the normalised exit frame.
* `exitArrLower_semG` — the value of the word-array lowering in `semG`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Hax

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (encodeTy)
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect (memGetDyn memSetDyn)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
  (EnvBoundOn ScalarInRange envReader_of_envBoundOn envBoundOn_updExpr scalarInRange_upd)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLt
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuarded
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedAgree

/-! ## 1. The pass -/

/-- The pass replacing every load of a word-array element through a tower slot whose limb `0`
    is copied into a scalar, and every store of a scalar marshalled into a word slot, by the
    word-array access through a `TU64` word slot, through sequences, bindings, branches and
    loops. -/
def scalarizeArrIn : LowCT → LowCT
  | .RLetZero c .TFp (.RSeq (.RArrLoad d s i) (.RSeq (.RScalarSetExpr a (.SLimb c' 0)) k)) =>
      if d.locVar = c ∧ c' = c then
        .RSeq (.RSeq (.RScalarSet a 0) (.RArrLoad ⟨a, .TU64⟩ s i)) (scalarizeArrIn k)
      else
        .RLetZero c .TFp
          (.RSeq (.RArrLoad d s i) (.RSeq (.RScalarSetExpr a (.SLimb c' 0)) (scalarizeArrIn k)))
  | .RLetZero m .TU64 (.RSeq (.RLimbStoreExpr l 0 (.SVar x)) (.RArrStore arr i src)) =>
      if l.locVar = m ∧ src.locVar = m then .RArrStore arr i ⟨x, .TU64⟩
      else .RLetZero m .TU64 (.RSeq (.RLimbStoreExpr l 0 (.SVar x)) (.RArrStore arr i src))
  | .RSeq a b => .RSeq (scalarizeArrIn a) (scalarizeArrIn b)
  | .RLetZero x t b => .RLetZero x t (scalarizeArrIn b)
  | .RLetU64Zero x b => .RLetU64Zero x (scalarizeArrIn b)
  | .RIfNz v t e => .RIfNz v (scalarizeArrIn t) (scalarizeArrIn e)
  | .RForRuntime x bd b => .RForRuntime x bd (scalarizeArrIn b)
  | c => c

/-! ## 2. The word view of the arrays -/

/-- **A word view of the arrays of the leaf semantics `L`.** `view n v` is the memref of `n`
    words of an array `v` of type `TArr n TU64`, and `inb n v k` states that `k` is an element
    index of `v`. At an index in bounds, the load of the element into limb `0` of a zeroed
    `TFp` slot reads the view's word, and the store of a word marshalled into limb `0` of a
    zeroed `TU64` slot writes it into the view. -/
structure ArrView (L : LeafSpec) where
  /-- The words of an array. -/
  view : (n : Nat) → RustVal (.TArr n .TU64) → ⟦encodeTy (.TArr n .TU64)⟧
  /-- The element indices of an array. -/
  inb : (n : Nat) → RustVal (.TArr n .TU64) → Nat → Prop
  /-- The load law. -/
  load : ∀ (c : String) (n : Nat) (a : RustVal (.TArr n .TU64)) (k : Nat), inb n a k →
    towerLimb (L.arrLoad ⟨c, .TFp⟩ default ⟨.TArr n .TU64, a⟩ k) 0 =
      (memGetDyn (view n a) k).toNat
  /-- The store law. -/
  store : ∀ (arr m : String) (n : Nat) (old : RustVal (.TArr n .TU64)) (k : Nat)
    (w : BitVec 64), inb n old k →
    view n (L.arrStore ⟨arr, .TArr n .TU64⟩ old k ⟨.TU64, L.limbStore ⟨m, .TU64⟩ default 0 w⟩) =
      memSetDyn (view n old) k w

variable {N : Nat} {L : LeafSpec}

/-- The environment binds every array named by `T` to the view of its value in the run. -/
def ArrOn (V : ArrView L) (rs : RustState) (env : SEnvScalar) (T : String → Prop) : Prop :=
  ∀ y, T y → ∃ (n : Nat) (v : RustVal (.TArr n .TU64)),
    rs.rsTower y = some ⟨.TArr n .TU64, v⟩ ∧ env y = some ⟨encodeTy (.TArr n .TU64), V.view n v⟩

/-- The bounds condition of a run: every element index a run of `c` from `rs` loads or stores
    is an element index (`ArrView.inb`) of the array it accesses. -/
def ArrRun (V : ArrView L) : LowCT → RustState → Prop
  | .RSeq a b, rs => ArrRun V a rs ∧ ∀ r1, RustExec N L a rs r1 → ArrRun V b r1
  | .RLetU64Zero x b, rs => ArrRun V b (rsSetScalar rs x 0)
  | .RLetZero x t b, rs => ArrRun V b (rsSetTower rs x ⟨t, default⟩)
  | .RArrLoad _ src i, rs => ∀ (n : Nat) (v : RustVal (.TArr n .TU64)),
      rs.rsTower src.locVar = some ⟨.TArr n .TU64, v⟩ → V.inb n v (rs.rsScalar i)
  | .RArrStore arr i _, rs => ∀ (n : Nat) (v : RustVal (.TArr n .TU64)),
      rs.rsTower arr.locVar = some ⟨.TArr n .TU64, v⟩ → V.inb n v (rs.rsScalar i)
  | _, _ => True

/-- Every read of `c` is in the bound set at the point of the read: `readsG`, with the stored
    word of a store read as well. -/
def readsA (B : String → Prop) : LowCT → Prop
  | .RSeq a b => readsA B a ∧ readsA (afterG B a) b
  | .RLetU64Zero x b => readsA (fun y => B y ∨ y = x) b
  | .RArrStore _ i src => B i ∧ B src.locVar
  | c => readsG B c

/-- The expressions that agree at every heap of words: those of `agreeAllB`, and a variable
    plus the literal `0` (the offset of a loop index from a zero lower bound). -/
def agreeWordB : SExpr → Bool
  | .SAdd (.SVar _) (.SLit 0) => true
  | e => agreeAllB e

theorem agreeWordB_sound (e : SExpr) (h : agreeWordB e = true) (σ : String → Nat)
    (hσ : ∀ y, σ y < 2 ^ 64) : ExprAgreeAt σ e := by
  unfold agreeWordB at h
  split at h
  · rename_i v
    refine ⟨by simpa [SExpr.eval] using hσ v, ?_⟩
    simp [SExpr.evalBV, SExpr.eval, SExpr.liftEnv]
  · exact agreeAllB_sound e h σ hσ

/-! ## 3. The relation -/

/-- `ExitArrRel T c c'`: `c'` is `c` with loads and stores of elements of the word arrays
    named by `T` replaced by word-array accesses through a `TU64` word slot, over the scalar
    commands of the guarded fragment without conditionals, writing no name of `T`, whose
    expressions agree at every heap of words (`agreeWordB`). -/
inductive ExitArrRel (T : String → Prop) : LowCT → LowCT → Prop
  | skip : ExitArrRel T .RSkip .RSkip
  | scalarSet {x : String} {n : Nat} (hx : srcName x) (hxT : ¬ T x) (hn : n < 2 ^ 64) :
      ExitArrRel T (.RScalarSet x n) (.RScalarSet x n)
  | scalarSetExpr {x : String} {e : SExpr} (hx : srcName x) (hxT : ¬ T x) (he : ltClean e)
      (hv : varsIn srcName e) (ha : agreeWordB e = true) :
      ExitArrRel T (.RScalarSetExpr x e) (.RScalarSetExpr x e)
  | seq {a a' b b' : LowCT} : ExitArrRel T a a' → ExitArrRel T b b' →
      ExitArrRel T (.RSeq a b) (.RSeq a' b')
  | letU64Zero {x : String} {b b' : LowCT} (hx : srcName x) (hxT : ¬ T x) :
      ExitArrRel T b b' → ExitArrRel T (.RLetU64Zero x b) (.RLetU64Zero x b')
  | load {c a s i : String} {n : Nat} {k k' : LowCT} (hc : ¬ T c) (ha : srcName a)
      (haT : ¬ T a) (hai : a ≠ i) (hs : srcName s) (hsT : T s) (hi : srcName i) :
      ExitArrRel T k k' →
      ExitArrRel T
        (.RLetZero c .TFp (.RSeq (.RArrLoad ⟨c, .TFp⟩ ⟨s, .TArr n .TU64⟩ i)
          (.RSeq (.RScalarSetExpr a (.SLimb c 0)) k)))
        (.RSeq (.RSeq (.RScalarSet a 0) (.RArrLoad ⟨a, .TU64⟩ ⟨s, .TArr n .TU64⟩ i)) k')
  | store {m x arr i : String} {n : Nat} (hm : ¬ T m) (hx : srcName x) (harr : srcName arr)
      (harrT : T arr) (hi : srcName i) :
      ExitArrRel T
        (.RLetZero m .TU64 (.RSeq (.RLimbStoreExpr ⟨m, .TU64⟩ 0 (.SVar x))
          (.RArrStore ⟨arr, .TArr n .TU64⟩ i ⟨m, .TU64⟩)))
        (.RArrStore ⟨arr, .TArr n .TU64⟩ i ⟨x, .TU64⟩)

/-- **The scalarised program is in the guarded fragment.** -/
theorem ExitArrRel.covered {T : String → Prop} {c c' : LowCT} (h : ExitArrRel T c c') :
    IsCoveredSCtlGuarded c' := by
  induction h with
  | skip => exact .rSkip
  | scalarSet hx _ hn => exact .rScalarSet hx hn
  | scalarSetExpr hx _ he hv _ => exact .rScalarSetExpr hx he hv
  | seq _ _ iha ihb => exact .rSeq iha ihb
  | letU64Zero hx _ _ ih => exact .rLetU64Zero hx ih
  | load _ ha _ _ hs _ hi _ ih =>
      exact .rSeq (.rSeq (.rScalarSet ha (by norm_num)) (.rArrLoad ha hs hi)) ih
  | store _ hx harr _ hi => exact .rArrStore harr hi hx

/-! ## 4. The simulation -/

theorem arrOn_congr {V : ArrView L} {rs rs' : RustState} {env env' : SEnvScalar}
    {T : String → Prop} (h : ArrOn V rs env T) (hr : ∀ y, T y → rs'.rsTower y = rs.rsTower y)
    (he : ∀ y, T y → env' y = env y) : ArrOn V rs' env' T := by
  intro y hy
  obtain ⟨n, v, h1, h2⟩ := h y hy
  exact ⟨n, v, (hr y hy).trans h1, (he y hy).trans h2⟩

/-- A name bound to a word is not a name of `T`. -/
theorem not_T_of_word {V : ArrView L} {rs : RustState} {env : SEnvScalar} {T : String → Prop}
    (h : ArrOn V rs env T) {y : String} {w : BitVec 64} (hy : env y = some ⟨.sword 64, w⟩) :
    ¬ T y := by
  intro hT
  obtain ⟨n, v, -, h2⟩ := h y hT
  rw [hy] at h2
  have := congrArg (fun p : Option ((t : CryptoTy) × ⟦t⟧) => p.map Sigma.fst) h2
  simp [encodeTy] at this

theorem not_T_of_bound {V : ArrView L} {rs : RustState} {env : SEnvScalar} {T : String → Prop}
    (h : ArrOn V rs env T) {S : List String} (hb : Bound env S) {y : String} (hy : y ∈ S) :
    ¬ T y := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hb y hy)
  exact not_T_of_word h (env_of_readU64 hw)

/-- An array name the environment binds at its type determines the type of a successful
    lookup of it. -/
theorem lookup_arr {rs : RustState} {y : String} {n n' : Nat} {v : RustVal (.TArr n' .TU64)}
    {w : RustVal (.TArr n .TU64)} (h : rs.rsTower y = some ⟨.TArr n' .TU64, v⟩)
    (hl : locatedLookup rs ⟨y, .TArr n .TU64⟩ = some w) : ∃ e : n' = n, e ▸ v = w := by
  simp only [locatedLookup, h] at hl
  split at hl
  · rename_i he
    have hn : n' = n := by cases he; rfl
    subst hn
    cases hl
    exact ⟨rfl, rfl⟩
  · cases hl

theorem lookup_self {rs : RustState} {y : String} {t : TowerType} {w : RustVal t}
    (hl : locatedLookup (rsSetTower rs y ⟨t, default⟩) ⟨y, t⟩ = some w) : w = default := by
  simp only [locatedLookup, rsSetTower_same, dif_pos] at hl
  exact (Option.some.inj hl).symm

theorem ifConvert_seq (flag : Option String) (S : List String) (k : Nat) (a b : LowCT) :
    ifConvert flag S k (.RSeq a b) =
      (.RSeq (ifConvert flag S k a).1
        (ifConvert flag (ifConvert flag S k a).2.1 (ifConvert flag S k a).2.2 b).1,
        (ifConvert flag (ifConvert flag S k a).2.1 (ifConvert flag S k a).2.2 b).2.1,
        (ifConvert flag (ifConvert flag S k a).2.1 (ifConvert flag S k a).2.2 b).2.2) := rfl

theorem ifConvert_scalarSet (flag : Option String) (S : List String) (k : Nat) (x : String)
    (n : Nat) : ifConvert flag S k (.RScalarSet x n) = (gWrite flag S x (.SLit n), x :: S, k) :=
  rfl

/-- **The guarded conversion of the scalarised program tracks the input's run.** Under the
    absent flag or a flag slot holding `1`, a `RustExec` run of `c` whose accesses are in
    bounds (`ArrRun`), from a state whose scalars are words, which `env` reflects on the names
    `B` and whose arrays of `T` it binds to their views (`ArrOn`), is tracked by `semScalar` of
    the guarded conversion of `c'`: its output environment binds every name bound after `c'`
    to the word of its output value and every array of `T` to its view. -/
theorem exitArr_taken (V : ArrView L) {T : String → Prop} (hT : ∀ y, T y → srcName y)
    {c c' : LowCT} (h : ExitArrRel T c c') :
    ∀ (flag : Option String) (S : List String) (k : Nat) (B : String → Prop)
      (rs rs' : RustState) (env : SEnvScalar),
      RustExec N L c rs rs' → ArrRun (N := N) V c rs → readsA B c' →
      FlagOn flag k env → SrcList S → Bound env S → (∀ y, B y → y ∈ S) →
      EnvBoundOn rs env B → ScalarInRange rs → ArrOn V rs env T →
      ∃ env', semScalar (ifConvert flag S k c').1 env = some env' ∧
        EnvBoundOn rs' env' (afterG B c') ∧ ScalarInRange rs' ∧
        Bound env' (ifConvert flag S k c').2.1 ∧
        (∀ i, i < k → env' (guardName i) = env (guardName i)) ∧ ArrOn V rs' env' T := by
  induction h with
  | skip =>
      intro flag S k B rs rs' env hexec _ _ _ _ hb _ henv hir hA
      cases hexec
      exact ⟨env, rfl, henv, hir, hb, fun _ _ => rfl, hA⟩
  | @scalarSet x n hx hxT hn =>
      intro flag S k B rs rs' env hexec _ _ hf hS hb _ henv hir hA
      cases hexec
      obtain ⟨env2, hs2, hotb⟩ := gWrite_taken (v := .SLit n) (S := S) hf hx hn trivial hb
      obtain ⟨hb1, hg1⟩ :=
        write_facts (w := (SExpr.SLit n).evalBV (envReader env)) hotb hx hS hb
      refine ⟨_, hs2, envBoundOn_updExpr henv hotb x n, scalarInRange_upd hir x hn, hb1,
        fun i _ => hg1 i, arrOn_congr hA (fun _ _ => rfl) fun y hy => ?_⟩
      rw [upd_ne (fun e : y = x => hxT (e ▸ hy))]
      exact hotb y (Or.inl (hT y hy).1)
  | @scalarSetExpr x e hx hxT he _ hag =>
      intro flag S k B rs rs' env hexec _ hr hf hS hb hB henv hir hA
      cases hexec
      have hIR := agreeWordB_sound e hag rs.rsScalar hir
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
      refine ⟨_, hs2, envBoundOn_updExpr henv hotb x _, scalarInRange_upd hir x hIR.1, hb1,
        fun i _ => hg1 i, arrOn_congr hA (fun _ _ => rfl) fun y hy => ?_⟩
      rw [upd_ne (fun e : y = x => hxT (e ▸ hy))]
      exact hotb y (Or.inl (hT y hy).1)
  | @seq a a' b b' hab _ iha ihb =>
      intro flag S k B rs rs' env hexec hrun hr hf hS hb hB henv hir hA
      cases hexec with
      | seq _ _ _ r1 _ h1 h2 =>
          rw [ifConvert_seq]
          obtain ⟨env1, hs1, henv1, hir1, hb1, hg1, hA1⟩ :=
            iha flag S k B rs r1 env h1 hrun.1 hr.1 hf hS hb hB henv hir hA
          obtain ⟨hSa, _, hBa, hka⟩ := ifConvert_static hab.covered flag S k B hS hB
          obtain ⟨env2, hs2, henv2, hir2, hb2, hg2, hA2⟩ :=
            ihb flag (ifConvert flag S k a').2.1 (ifConvert flag S k a').2.2 (afterG B a') r1 rs'
              env1 h2 (hrun.2 r1 h1) hr.2 (flagOn_mono hf hka hg1) hSa hb1 hBa henv1 hir1 hA1
          exact ⟨env2, by rw [semScalar_seq, hs1, Option.bind_some]; exact hs2, henv2, hir2,
            hb2, fun i hi => (hg2 i (by omega)).trans (hg1 i hi), hA2⟩
  | @letU64Zero x b b' hx hxT _ ihb =>
      intro flag S k B rs rs' env hexec hrun hr hf hS hb hB henv hir hA
      cases hexec with
      | letU64Zero _ _ _ _ hbody =>
          simp only [ifConvert]
          obtain ⟨env2, hs2, hotb⟩ := gWrite_taken (v := .SLit 0) (S := S) hf hx
            (show (0 : Nat) < 2 ^ 64 by decide) trivial hb
          obtain ⟨hb1, hg1⟩ :=
            write_facts (w := (SExpr.SLit 0).evalBV (envReader env)) hotb hx hS hb
          have henv1 := envBoundOn_updExpr henv hotb x 0
          have hA1 : ArrOn V (rsSetScalar rs x 0)
              (env2.upd x (t := .sword 64) ((SExpr.SLit 0).evalBV (envReader env))) T :=
            arrOn_congr hA (fun _ _ => rfl) fun y hy => by
              rw [upd_ne (fun e : y = x => hxT (e ▸ hy))]
              exact hotb y (Or.inl (hT y hy).1)
          obtain ⟨env3, hs3, henv3, hir3, hb3, hg3, hA3⟩ :=
            ihb flag (x :: S) k (fun y => B y ∨ y = x) _ rs' _ hbody hrun hr
              (flagOn_mono hf (le_refl k) (fun i _ => hg1 i)) (srcList_cons hx hS) hb1
              (sub_cons x hB) henv1 (scalarInRange_upd hir x (by norm_num)) hA1
          exact ⟨env3, by rw [semScalar_seq, hs2, Option.bind_some]; exact hs3, henv3, hir3,
            hb3, fun i hi => (hg3 i hi).trans (hg1 i), hA3⟩
  | @load c a s i n kk kk' hc ha haT hai hs hsT hi hrel ih =>
      intro flag S k B rs rs' env hexec hrun hr hf hS hb hB henv hir hA
      have hcs : c ≠ s := fun e => hc (e ▸ hsT)
      have hsa : s ≠ a := fun e => haT (e ▸ hsT)
      simp only [ArrRun] at hrun
      simp only [readsA, readsG, afterG] at hr
      cases hexec with
      | letZero _ _ _ _ _ hb0 =>
      cases hb0 with
      | seq _ _ _ r1 _ h1 h2 =>
      have hrunK := hrun.2 r1 h1
      cases h2 with
      | seq _ _ _ r2 _ h3 h4 =>
      have hrunK' := hrunK.2 r2 h3
      rw [setExpr_inv h3] at h4 hrunK'
      cases h1 with
      | arrLoad _ _ _ _ idx oldV srcV hidx hold hsrc =>
      subst hidx
      have hold' := lookup_self hold
      subst hold'
      rw [locatedLookup_rsSetTower_other _ _ _ _ hcs] at hsrc
      obtain ⟨n', v, hv, henvs⟩ := hA s hsT
      obtain ⟨rfl, rfl⟩ := lookup_arr hv hsrc
      have hinb : V.inb n' v (rs.rsScalar i) :=
        hrun.1 n' v (by rw [rsSetTower_other _ _ _ _ hcs]; exact hv)
      set wv := memGetDyn (V.view n' v) (rs.rsScalar i) with hwv
      have hev : (SExpr.SLimb c 0).evalState (locatedUpdate (rsSetTower rs c ⟨.TFp, default⟩)
          ⟨c, .TFp⟩ (L.arrLoad ⟨c, .TFp⟩ default ⟨.TArr n' .TU64, v⟩
            ((rsSetTower rs c ⟨.TFp, default⟩).rsScalar i))) = wv.toNat := by
        simp only [SExpr.evalState, rsTowerLimb, locatedUpdate, rsSetTower_same]
        exact V.load c n' v _ hinb
      rw [hev] at h4 hrunK'
      rw [ifConvert_seq, ifConvert_seq, ifConvert_scalarSet]
      dsimp only
      rw [ifConvert_arrLoad_out]
      obtain ⟨env2, hs2, hotb⟩ := gWrite_taken (v := .SLit 0) (S := S) hf ha
        (show (0 : Nat) < 2 ^ 64 by decide) trivial hb
      obtain ⟨hb1, hg1⟩ :=
        write_facts (w := (SExpr.SLit 0).evalBV (envReader env)) hotb ha hS hb
      set env1 := env2.upd a (t := .sword 64) ((SExpr.SLit 0).evalBV (envReader env))
        with henv1def
      have hfr1 : ∀ y, ¬ isTmpName y → y ≠ a → env1 y = env y := fun y hy hya => by
        rw [henv1def, upd_ne hya]; exact hotb y (Or.inl hy)
      have hi1 : env1 i = some ⟨.sword 64, BitVec.ofNat 64 (rs.rsScalar i)⟩ := by
        rw [hfr1 i hi.1 (Ne.symm hai)]
        exact henv i (hr.1.2.resolve_right (Ne.symm hai)) hi.1
      have hs1 : env1 s = some ⟨encodeTy (.TArr n' .TU64), V.view n' v⟩ := by
        rw [hfr1 s hs.1 hsa]; exact henvs
      have hf1 : FlagOn flag k env1 := flagOn_mono hf (le_refl k) (fun j _ => hg1 j)
      obtain ⟨env3, hs3, hd3, hfr3⟩ := ifConvert_load_on (S := a :: S) hf1 hi1 upd_self hs1
        hi.1 ha hs
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hir i)] at hd3
      have hfr31 : ∀ y, srcName y → y ≠ a → env3 y = env y := fun y hy hya =>
        (hfr3 y hy.1 hya (srcName_ne_guardName hy k) (srcName_ne_guardName hy (k + 1))).trans
          (hfr1 y hy.1 hya)
      have hk' : k ≤ (ifConvert flag (a :: S) k
          (.RArrLoad ⟨a, .TU64⟩ ⟨s, .TArr n' .TU64⟩ i)).2.2 := by
        cases flag <;> simp [ifConvert]
      have hg3 : ∀ j, j < k → env3 (guardName j) = env (guardName j) := fun j hj =>
        (hfr3 _ (not_isTmpName_guardName j) (fun e => srcName_ne_guardName ha j e.symm)
          (guardName_ne (by omega)) (guardName_ne (by omega))).trans (hg1 j)
      have henv3 : EnvBoundOn (rsSetScalar (locatedUpdate (rsSetTower rs c ⟨.TFp, default⟩)
          ⟨c, .TFp⟩ (L.arrLoad ⟨c, .TFp⟩ default ⟨.TArr n' .TU64, v⟩
            ((rsSetTower rs c ⟨.TFp, default⟩).rsScalar i))) a wv.toNat) env3
          (fun y => B y ∨ y = a) := by
        intro y hy hnt
        by_cases hya : y = a
        · subst hya
          rw [hd3]
          simp [rsSetScalar, hwv]
        · have hBy := hy.resolve_right hya
          rw [hfr31 y (hS y (hB y hBy)) hya, henv y hBy hnt]
          simp [rsSetScalar, hya, locatedUpdate, rsSetTower]
      have hb3 : Bound env3 (a :: S) := by
        intro y hy
        by_cases hya : y = a
        · subst hya; rw [readU64_of_env hd3]; rfl
        · have hyS := List.mem_of_ne_of_mem hya hy
          rw [readU64_eq_of_env (hfr31 y (hS y hyS) hya)]
          exact hb y hyS
      have hA3 : ArrOn V (rsSetScalar (locatedUpdate (rsSetTower rs c ⟨.TFp, default⟩)
          ⟨c, .TFp⟩ (L.arrLoad ⟨c, .TFp⟩ default ⟨.TArr n' .TU64, v⟩
            ((rsSetTower rs c ⟨.TFp, default⟩).rsScalar i))) a wv.toNat) env3 T := by
        refine arrOn_congr hA (fun y hy => ?_) (fun y hy => hfr31 y (hT y hy)
          (fun e => haT (e ▸ hy)))
        have hyc : c ≠ y := fun e => hc (e ▸ hy)
        simp only [rsSetScalar, locatedUpdate]
        rw [rsSetTower_other _ _ _ _ hyc, rsSetTower_other _ _ _ _ hyc]
      obtain ⟨env4, hs4, henv4, hir4, hb4, hg4, hA4⟩ :=
        ih flag (a :: S) _ (fun y => B y ∨ y = a) _ rs' env3 h4 hrunK' hr.2
          (flagOn_mono hf hk' hg3) (srcList_cons ha hS) hb3 (sub_cons a hB) henv3
          (scalarInRange_upd hir a wv.isLt) hA3
      exact ⟨env4, by
          rw [semScalar_seq, semScalar_seq, hs2, Option.bind_some, hs3, Option.bind_some]
          exact hs4, henv4, hir4, hb4, fun j hj => (hg4 j (by omega)).trans (hg3 j hj), hA4⟩
  | @store m x arr i n hm hx harr harrT hi =>
      intro flag S k B rs rs' env hexec hrun hr hf hS hb hB henv hir hA
      have hma : m ≠ arr := fun e => hm (e ▸ harrT)
      simp only [ArrRun] at hrun
      simp only [readsA] at hr
      cases hexec with
      | letZero _ _ _ _ _ hb0 =>
      cases hb0 with
      | seq _ _ _ r1 _ h1 h2 =>
      have hrunS := hrun.2 r1 h1
      cases h1 with
      | limbStoreExpr _ _ _ _ oldM hlm =>
      have hlm' := lookup_self hlm
      subst hlm'
      cases h2 with
      | arrStore _ _ _ _ idx oldA srcV hidx hla hls =>
      subst hidx
      simp only [locatedLookup, locatedUpdate, rsSetTower_same, dif_pos, Option.some.injEq]
        at hls
      subst hls
      simp only [locatedUpdate] at hla hrunS
      rw [locatedLookup_rsSetTower_other _ _ _ _ hma,
        locatedLookup_rsSetTower_other _ _ _ _ hma] at hla
      obtain ⟨n', v, hv, henva⟩ := hA arr harrT
      obtain ⟨rfl, rfl⟩ := lookup_arr hv hla
      have hinb : V.inb n' v (rs.rsScalar i) :=
        hrunS n' v (by rw [rsSetTower_other _ _ _ _ hma, rsSetTower_other _ _ _ _ hma]; exact hv)
      have hlaw := V.store arr m n' v (rs.rsScalar i) (BitVec.ofNat 64 (rs.rsScalar x)) hinb
      obtain ⟨env', hs', ha', hfr'⟩ := ifConvert_store_on (S := S) (k := k) hf
        (henv i hr.1 hi.1) henva (henv x hr.2 hx.1) hi.1 harr hx
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hir i), ← hlaw] at ha'
      have hfr : ∀ y, srcName y → y ≠ arr → env' y = env y := fun y hy hya =>
        hfr' y hy.1 hya (srcName_ne_guardName hy k) (srcName_ne_guardName hy (k + 1))
          (srcName_ne_guardName hy (k + 2))
      rw [ifConvert_arrStore_out]
      refine ⟨env', hs', ?_, hir, ?_, ?_, ?_⟩
      · intro y hy hnt
        have hya : y ≠ arr := fun e => not_T_of_word hA (henv y hy hnt) (e ▸ harrT)
        rw [hfr y (hS y (hB y hy)) hya]
        exact henv y hy hnt
      · intro y hy
        have hya : y ≠ arr := fun e => not_T_of_bound hA hb hy (e ▸ harrT)
        rw [readU64_eq_of_env (hfr y (hS y hy) hya)]
        exact hb y hy
      · intro j hj
        exact hfr' _ (not_isTmpName_guardName j)
          (fun e => srcName_ne_guardName harr j e.symm) (guardName_ne (by omega))
          (guardName_ne (by omega)) (guardName_ne (by omega))
      · intro y hy
        by_cases hya : y = arr
        · subst hya
          exact ⟨n', _, rsSetTower_same _ _ _, ha'⟩
        · obtain ⟨n'', w, hw, hew⟩ := hA y hy
          have hym : m ≠ y := fun e => hm (e ▸ hy)
          refine ⟨n'', w, ?_, (hfr y (hT y hy) hya).trans hew⟩
          simp only [locatedUpdate, rsSetTower_other _ _ _ _ (Ne.symm hya),
            rsSetTower_other _ _ _ _ hym]
          exact hw

/-- **The scalarised program at top level.** A `RustExec` run of `c` whose accesses are in
    bounds, from a state whose scalars are words, which `env` reflects on the names `B` and
    whose arrays of `T` it binds to their views, is tracked by `semScalar` of the guarded
    conversion of `c'` from the bound list `S ⊇ B`. -/
theorem exitArr_semScalar (V : ArrView L) {T : String → Prop} (hT : ∀ y, T y → srcName y)
    {c c' : LowCT} (h : ExitArrRel T c c') {S : List String} {B : String → Prop}
    {rs rs' : RustState} {env : SEnvScalar} (hexec : RustExec N L c rs rs')
    (hrun : ArrRun (N := N) V c rs) (hreads : readsA B c') (hS : SrcList S)
    (hb : Bound env S) (hB : ∀ y, B y → y ∈ S) (henv : EnvBoundOn rs env B)
    (hir : ScalarInRange rs) (hA : ArrOn V rs env T) :
    ∃ env', semScalar (ifConvert none S 0 c').1 env = some env' ∧
      EnvBoundOn rs' env' (afterG B c') ∧ ScalarInRange rs' ∧
      Bound env' (ifConvert none S 0 c').2.1 ∧ ArrOn V rs' env' T := by
  obtain ⟨env', hs, henv', hir', hb', -, hA'⟩ := exitArr_taken V hT h none S 0 B rs rs' env
    hexec hrun hreads (fun _ h => by cases h) hS hb hB henv hir hA
  exact ⟨env', hs, henv', hir', hb', hA'⟩

/-! ## 5. The Boolean test on the input of the pass -/

/-- The Boolean test on the input `c` of `scalarizeArrIn`, at the array names `Ts`: the scalar
    commands of the guarded fragment without conditionals over source names outside `Ts`,
    whose expressions pass `agreeWordB`; the load of an element of a word array of `Ts` through
    a `TFp` slot outside `Ts` into a source name outside `Ts` other than the index; and the
    store of a source name marshalled through a `TU64` slot outside `Ts` into an element of a
    word array of `Ts`. -/
def exitArrB (Ts : List String) : LowCT → Bool
  | .RLetZero c .TFp (.RSeq (.RArrLoad d s i) (.RSeq (.RScalarSetExpr a (.SLimb c' 0)) k)) =>
      decide (d = ⟨c, .TFp⟩) && c' == c && !Ts.contains c && srcNameB a && !Ts.contains a &&
        a != i && srcNameB s.locVar && Ts.contains s.locVar && isWordArrB s.locSrc &&
        srcNameB i && exitArrB Ts k
  | .RLetZero m .TU64 (.RSeq (.RLimbStoreExpr l 0 (.SVar x)) (.RArrStore arr i src)) =>
      decide (l = ⟨m, .TU64⟩) && decide (src = ⟨m, .TU64⟩) && !Ts.contains m && srcNameB x &&
        srcNameB arr.locVar && Ts.contains arr.locVar && isWordArrB arr.locSrc && srcNameB i
  | .RSeq a b => exitArrB Ts a && exitArrB Ts b
  | .RLetU64Zero x b => srcNameB x && !Ts.contains x && exitArrB Ts b
  | .RScalarSetExpr x e => srcNameB x && !Ts.contains x && ltCleanSrcB e && agreeWordB e
  | .RScalarSet x n => srcNameB x && !Ts.contains x && decide (n < 2 ^ 64)
  | .RSkip => true
  | _ => false

/-- **The pass on an accepted input.** An input accepted by `exitArrB Ts` is related by
    `ExitArrRel` at the names of `Ts` to its scalarisation `scalarizeArrIn c`. -/
theorem exitArrB_sound (Ts : List String) :
    ∀ c : LowCT, exitArrB Ts c = true → ExitArrRel (· ∈ Ts) c (scalarizeArrIn c) := by
  intro c
  fun_induction exitArrB Ts c with
  | case1 c d s i a c' k ih =>
      intro h
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd, hc'⟩, hc⟩, ha⟩, haT⟩, hai⟩, hs⟩, hsT⟩, hsw⟩, hi⟩, hk⟩ := h
      subst hd hc'
      obtain ⟨n, hn⟩ := exists_of_isWordArrB hsw
      obtain ⟨sv, st⟩ := s
      simp only at hn hs hsT
      subst hn
      simp only [scalarizeArrIn, and_self, if_true]
      exact .load hc (srcName_of_srcNameB ha) haT hai (srcName_of_srcNameB hs) hsT
        (srcName_of_srcNameB hi) (ih hk)
  | case2 m l x arr i src =>
      intro h
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨hl, hsrc⟩, hm⟩, hx⟩, harr⟩, harrT⟩, hw⟩, hi⟩ := h
      subst hl hsrc
      obtain ⟨n, hn⟩ := exists_of_isWordArrB hw
      obtain ⟨av, at'⟩ := arr
      simp only at hn harr harrT
      subst hn
      simp only [scalarizeArrIn, and_self, if_true]
      exact .store hm (srcName_of_srcNameB hx) (srcName_of_srcNameB harr) harrT
        (srcName_of_srcNameB hi)
  | case3 a b iha ihb =>
      intro h
      simp only [Bool.and_eq_true] at h
      simp only [scalarizeArrIn]
      exact .seq (iha h.1) (ihb h.2)
  | case4 x b ih =>
      intro h
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not] at h
      simp only [scalarizeArrIn]
      exact .letU64Zero (srcName_of_srcNameB h.1.1) h.1.2 (ih h.2)
  | case5 x e =>
      intro h
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not] at h
      obtain ⟨⟨⟨hx, hxT⟩, he⟩, hag⟩ := h
      simp only [scalarizeArrIn]
      exact .scalarSetExpr (srcName_of_srcNameB hx) hxT (ltCleanSrcB_sound e he).1
        (ltCleanSrcB_sound e he).2 hag
  | case6 x n =>
      intro h
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not, decide_eq_true_eq] at h
      simp only [scalarizeArrIn]
      exact .scalarSet (srcName_of_srcNameB h.1.1) h.1.2 h.2
  | case7 => intro _; exact .skip
  | case8 => intro h; simp_all

/-! ## 6. Runtime-count loops -/

section Loops

open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge (envBoundOn_mono)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLoop (guardedTrips guardedTripCmd)
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRouteSeq
  (loopFreeB semG boundG boundVal semG_of_loopFree boundG_of_loopFree loopFreeB_of_covered)

/-- `ExitArrRelL T c c'`: `c'` is the scalarisation of `c`, where `c` is built from loop-free
    parts related by `ExitArrRel T` by sequences, word binders outside `T` and runtime-count
    loops over an index outside `T` whose trip bodies are related by `ExitArrRel T`. -/
inductive ExitArrRelL (T : String → Prop) : LowCT → LowCT → Prop
  | base {c c' : LowCT} : ExitArrRel T c c' → ExitArrRelL T c c'
  | seq {a a' b b' : LowCT} : ExitArrRelL T a a' → ExitArrRelL T b b' →
      ExitArrRelL T (.RSeq a b) (.RSeq a' b')
  | letU64Zero {x : String} {b b' : LowCT} (hx : srcName x) (hxT : ¬ T x) :
      ExitArrRelL T b b' → ExitArrRelL T (.RLetU64Zero x b) (.RLetU64Zero x b')
  | loop {x : String} {bd : SExpr} {body body' : LowCT} (hx : srcName x) (hxT : ¬ T x)
      (hb : loopBoundB bd = true) : ExitArrRel T body body' →
      ExitArrRelL T (.RForRuntime x bd body) (.RForRuntime x bd body')

theorem ExitArrRel.loopFreeB_right {T : String → Prop} {c c' : LowCT} (h : ExitArrRel T c c') :
    loopFreeB c' = true :=
  loopFreeB_of_covered h.covered

theorem ExitArrRel.loopFreeB_left {T : String → Prop} {c c' : LowCT} (h : ExitArrRel T c c') :
    loopFreeB c = true := by
  induction h <;> simp_all [loopFreeB]

/-- A loop-free scalarisation of the relation with loops is one of the loop-free relation. -/
theorem ExitArrRelL.toBase {T : String → Prop} {c c' : LowCT} (h : ExitArrRelL T c c')
    (hf : loopFreeB c' = true) : ExitArrRel T c c' := by
  induction h with
  | base h => exact h
  | seq _ _ iha ihb =>
      simp only [loopFreeB, Bool.and_eq_true] at hf
      exact .seq (iha hf.1) (ihb hf.2)
  | letU64Zero hx hxT _ ih =>
      simp only [loopFreeB] at hf
      exact .letU64Zero hx hxT (ih hf)
  | loop => simp [loopFreeB] at hf

/-- The reads of a program with loops are bound: `readsA` on its loop-free parts, and on a
    loop the variables of the bound and the reads of the trip body with the index bound. -/
def readsAL (B : String → Prop) : LowCT → Prop
  | .RSeq a b => readsAL B a ∧ readsAL (afterG B a) b
  | .RLetU64Zero x b => readsAL (fun y => B y ∨ y = x) b
  | .RForRuntime x bd body => varsIn B bd ∧ readsA (fun y => B y ∨ y = x) body
  | c => readsA B c

theorem readsA_of_readsAL : ∀ {c : LowCT} {B : String → Prop}, loopFreeB c = true →
    readsAL B c → readsA B c := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro B hf h
      simp only [loopFreeB, Bool.and_eq_true] at hf
      exact ⟨iha hf.1 h.1, ihb hf.2 h.2⟩
  | RLetU64Zero x b ih =>
      intro B hf h
      exact ih hf h
  | RForRuntime => intro _ hf; simp [loopFreeB] at hf
  | _ => intro _ _ h; exact h

/-- The bounds condition of a run of a program with loops: `ArrRun` on its loop-free parts,
    and on a loop `ArrRun` of the trip body at the entry state of every trip. -/
def ArrRunL (V : ArrView L) : LowCT → RustState → Prop
  | .RSeq a b, rs => ArrRunL V a rs ∧ ∀ r1, RustExec N L a rs r1 → ArrRunL V b r1
  | .RLetU64Zero x b, rs => ArrRunL V b (rsSetScalar rs x 0)
  | .RForRuntime x bd body, rs => ∀ t, t < bd.evalState rs → ∀ r,
      RustExec N L (.RFor x t body) rs r → ArrRun (N := N) V body (rsSetScalar r x t)
  | c, rs => ArrRun (N := N) V c rs

theorem arrRun_of_arrRunL {V : ArrView L} : ∀ {c : LowCT} {rs : RustState},
    loopFreeB c = true → ArrRunL (N := N) V c rs → ArrRun (N := N) V c rs := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro rs hf h
      simp only [loopFreeB, Bool.and_eq_true] at hf
      exact ⟨iha hf.1 h.1, fun r1 hr1 => ihb hf.2 (h.2 r1 hr1)⟩
  | RLetU64Zero x b ih =>
      intro rs hf h
      exact ih hf h
  | RForRuntime => intro _ hf; simp [loopFreeB] at hf
  | _ => intro _ _ h; exact h

/-- **The trip fold tracks the trips of a related loop.** For trip bodies related by
    `ExitArrRel T` and reading names of `B` and the index, `n ≤ 2^64` trips of a `RustExec`
    run of `RFor x n body`, each in bounds, from a state reflected on `B` by `env` whose arrays
    of `T` it binds to their views, are tracked by `n` trips of `guardedTrips x S body'`. -/
theorem exitArrLoop_trips (V : ArrView L) {T : String → Prop} (hT : ∀ y, T y → srcName y)
    {body body' : LowCT} (hrel : ExitArrRel T body body') {x : String} {S : List String}
    {B : String → Prop} (hx : srcName x) (hxT : ¬ T x) (hS : SrcList S)
    (hB : ∀ y, B y → y ∈ S) (hreads : readsA (fun y => B y ∨ y = x) body') {rs : RustState}
    {env : SEnvScalar} :
    ∀ (n : Nat) {rs' : RustState}, n ≤ 2 ^ 64 → RustExec N L (.RFor x n body) rs rs' →
      (∀ t, t < n → ∀ r, RustExec N L (.RFor x t body) rs r →
        ArrRun (N := N) V body (rsSetScalar r x t)) →
      EnvBoundOn rs env B → Bound env S → ScalarInRange rs → ArrOn V rs env T →
      ∃ env', guardedTrips x S body' n env = some env' ∧ EnvBoundOn rs' env' B ∧
        Bound env' S ∧ ScalarInRange rs' ∧ ArrOn V rs' env' T
  | 0, _, _, hexec, _, henv, hb, hir, hA => by
      cases hexec
      exact ⟨env, rfl, henv, hb, hir, hA⟩
  | n + 1, _, hn, hexec, hrun, henv, hb, hir, hA => by
      cases hexec with
      | forSucc _ _ _ _ r₁ _ hf hbd =>
          obtain ⟨e₁, he₁, henv₁, hb₁, hir₁, hA₁⟩ := exitArrLoop_trips V hT hrel hx hxT hS hB
            hreads n (by omega) hf (fun t ht r hr => hrun t (by omega) r hr) henv hb hir hA
          have hb0 : Bound (e₁.upd x (t := .sword 64) (BitVec.ofNat 64 n)) (x :: S) := by
            intro y hy
            by_cases hyx : y = x
            · subst hyx; rw [readU64_of_env upd_self]; rfl
            · rw [readU64_eq_of_env (upd_ne hyx)]
              exact hb₁ y (List.mem_of_ne_of_mem hyx hy)
          have henv0 : EnvBoundOn (rsSetScalar r₁ x n)
              (e₁.upd x (t := .sword 64) (BitVec.ofNat 64 n)) (fun y => B y ∨ y = x) := by
            intro y hy hnt
            by_cases hyx : y = x
            · subst hyx; rw [upd_self]; simp [rsSetScalar]
            · rw [upd_ne hyx, henv₁ y (hy.resolve_right hyx) hnt]
              simp [rsSetScalar, hyx]
          have hA0 : ArrOn V (rsSetScalar r₁ x n)
              (e₁.upd x (t := .sword 64) (BitVec.ofNat 64 n)) T :=
            arrOn_congr hA₁ (fun _ _ => rfl) fun y hy => upd_ne (fun e : y = x => hxT (e ▸ hy))
          obtain ⟨env', hs, henv', hir', hbd', -, hA'⟩ :=
            exitArr_taken V hT hrel none (x :: S) 0 (fun y => B y ∨ y = x) (rsSetScalar r₁ x n)
              _ _ hbd (hrun n (by omega) r₁ hf) hreads (fun _ h => by cases h)
              (srcList_cons hx hS) hb0 (sub_cons x hB) henv0
              (scalarInRange_upd hir₁ x (by omega)) hA0
          obtain ⟨_, hsubS, _, _⟩ := ifConvert_static hrel.covered none (x :: S) 0
            (fun y => B y ∨ y = x) (srcList_cons hx hS) (sub_cons x hB)
          refine ⟨env', ?_, envBoundOn_mono henv' (fun y hy => le_afterG body' _ y (Or.inl hy)),
            fun y hy => hbd' y (hsubS y (List.mem_cons_of_mem _ hy)), hir', hA'⟩
          simp only [guardedTrips, he₁, Option.bind_some]
          exact hs

/-- The loop-free case of `exitArrL_semG`. -/
theorem exitArr_semG (V : ArrView L) {T : String → Prop} (hT : ∀ y, T y → srcName y)
    {c c' : LowCT} (h : ExitArrRel T c c') (S : List String) (B : String → Prop)
    (rs rs' : RustState) (env : SEnvScalar) (hexec : RustExec N L c rs rs')
    (hrun : ArrRunL (N := N) V c rs) (hr : readsAL B c') (hS : SrcList S) (hb : Bound env S)
    (hB : ∀ y, B y → y ∈ S) (henv : EnvBoundOn rs env B) (hir : ScalarInRange rs)
    (hA : ArrOn V rs env T) :
    ∃ env', semG S c' env = some env' ∧ EnvBoundOn rs' env' (afterG B c') ∧
      ScalarInRange rs' ∧ Bound env' (boundG S c') ∧ SrcList (boundG S c') ∧
      (∀ y, afterG B c' y → y ∈ boundG S c') ∧ ArrOn V rs' env' T := by
  obtain ⟨env', hs, henv', hir', hb', -, hA'⟩ := exitArr_taken V hT h none S 0 B rs rs' env
    hexec (arrRun_of_arrRunL h.loopFreeB_left hrun) (readsA_of_readsAL h.loopFreeB_right hr)
    (fun _ h => by cases h) hS hb hB henv hir hA
  obtain ⟨hSa, -, hBa, -⟩ := ifConvert_static h.covered none S 0 B hS hB
  rw [semG_of_loopFree h.loopFreeB_right, boundG_of_loopFree h.loopFreeB_right]
  exact ⟨env', hs, henv', hir', hb', hSa, hBa, hA'⟩

/-- **`semG` of the scalarised program tracks the input's run.** A `RustExec` run of `c` in
    bounds (`ArrRunL`), from a state whose scalars are words, which `env` reflects on the
    names `B ⊆ S` and whose arrays of `T` it binds to their views, is tracked by `semG S c'`:
    its output environment binds every name bound after `c'` to the word of its output value,
    binds the bound list after `c'`, and binds every array of `T` to its view. -/
theorem exitArrL_semG (V : ArrView L) {T : String → Prop} (hT : ∀ y, T y → srcName y)
    {c c' : LowCT} (h : ExitArrRelL T c c') :
    ∀ (S : List String) (B : String → Prop) (rs rs' : RustState) (env : SEnvScalar),
      RustExec N L c rs rs' → ArrRunL (N := N) V c rs → readsAL B c' → SrcList S →
      Bound env S → (∀ y, B y → y ∈ S) → EnvBoundOn rs env B → ScalarInRange rs →
      ArrOn V rs env T →
      ∃ env', semG S c' env = some env' ∧ EnvBoundOn rs' env' (afterG B c') ∧
        ScalarInRange rs' ∧ Bound env' (boundG S c') ∧ SrcList (boundG S c') ∧
        (∀ y, afterG B c' y → y ∈ boundG S c') ∧ ArrOn V rs' env' T := by
  induction h with
  | base h => exact exitArr_semG V hT h
  | @seq a a' b b' hab hbb iha ihb =>
      intro S B rs rs' env hexec hrun hr hS hb hB henv hir hA
      by_cases hf : loopFreeB (.RSeq a' b') = true
      · exact exitArr_semG V hT ((ExitArrRelL.seq hab hbb).toBase hf) S B rs rs' env hexec
          hrun hr hS hb hB henv hir hA
      · have hf' : (loopFreeB a' && loopFreeB b') = false := by
          simpa [loopFreeB] using hf
        cases hexec with
        | seq _ _ _ r1 _ h1 h2 =>
            obtain ⟨e₁, hs₁, henv₁, hir₁, hb₁, hS₁, hB₁, hA₁⟩ :=
              iha S B rs r1 env h1 hrun.1 hr.1 hS hb hB henv hir hA
            obtain ⟨e₂, hs₂, henv₂, hir₂, hb₂, hS₂, hB₂, hA₂⟩ :=
              ihb (boundG S a') (afterG B a') r1 rs' e₁ h2 (hrun.2 r1 h1) hr.2 hS₁ hb₁ hB₁
                henv₁ hir₁ hA₁
            refine ⟨e₂, ?_, henv₂, hir₂, ?_, ?_, ?_, hA₂⟩
            · simp only [semG, hf', Bool.false_eq_true, if_false, hs₁, Option.bind_some]
              exact hs₂
            · simp only [boundG, hf', Bool.false_eq_true, if_false]; exact hb₂
            · simp only [boundG, hf', Bool.false_eq_true, if_false]; exact hS₂
            · simp only [boundG, hf', Bool.false_eq_true, if_false]; exact hB₂
  | @letU64Zero x b b' hx hxT hbb ih =>
      intro S B rs rs' env hexec hrun hr hS hb hB henv hir hA
      by_cases hf : loopFreeB b' = true
      · exact exitArr_semG V hT ((ExitArrRelL.letU64Zero hx hxT hbb).toBase
          (by simpa [loopFreeB])) S B rs rs' env hexec hrun hr hS hb hB henv hir hA
      · have hf' : loopFreeB b' = false := by simpa using hf
        cases hexec with
        | letU64Zero _ _ _ _ hbody =>
            obtain ⟨env2, hs2, hotb⟩ := gWrite_taken (v := .SLit 0) (S := S) (flag := none)
              (k := 0) (fun _ h => by cases h) hx (show (0 : Nat) < 2 ^ 64 by decide) trivial hb
            obtain ⟨hb1, -⟩ :=
              write_facts (w := (SExpr.SLit 0).evalBV (envReader env)) hotb hx hS hb
            have henv1 := envBoundOn_updExpr henv hotb x 0
            have hA1 : ArrOn V (rsSetScalar rs x 0)
                (env2.upd x (t := .sword 64) ((SExpr.SLit 0).evalBV (envReader env))) T :=
              arrOn_congr hA (fun _ _ => rfl) fun y hy => by
                rw [upd_ne (fun e : y = x => hxT (e ▸ hy))]
                exact hotb y (Or.inl (hT y hy).1)
            obtain ⟨env3, hs3, henv3, hir3, hb3, hS3, hB3, hA3⟩ :=
              ih (x :: S) (fun y => B y ∨ y = x) _ rs' _ hbody hrun hr (srcList_cons hx hS) hb1
                (sub_cons x hB) henv1 (scalarInRange_upd hir x (by norm_num)) hA1
            refine ⟨env3, ?_, henv3, hir3, ?_, ?_, ?_, hA3⟩
            · simp only [semG, hf', Bool.false_eq_true, if_false, hs2, Option.bind_some]
              exact hs3
            · simp only [boundG, hf', Bool.false_eq_true, if_false]; exact hb3
            · simp only [boundG, hf', Bool.false_eq_true, if_false]; exact hS3
            · simp only [boundG, hf', Bool.false_eq_true, if_false]; exact hB3
  | @loop x bd body body' hx hxT hbd hrel =>
      intro S B rs rs' env hexec hrun hr hS hb hB henv hir hA
      have hcnt := boundVal_eq_evalState hbd hr.1 henv hir
      cases hexec with
      | forRuntime _ _ _ _ _ hf =>
          obtain ⟨env', hs, henv', hb', hir', hA'⟩ := exitArrLoop_trips V hT hrel hx hxT hS hB
            hr.2 (bd.evalState rs) (evalState_le_of_loopBoundB hbd hir).le hf hrun henv hb hir hA
          refine ⟨env', ?_, henv', hir', hb', hS, hB, hA'⟩
          simp only [semG, hcnt]
          exact hs

/-- The Boolean test on the input of `scalarizeArrIn` for programs with loops, at the array
    names `Ts`: accepted by `exitArrB Ts`, or a sequence or word binder outside `Ts` of accepted
    parts, or a runtime-count loop over a source-name index outside `Ts` with a bound of
    `loopBoundB` and a trip body accepted by `exitArrB Ts`. -/
def exitArrBL (Ts : List String) : LowCT → Bool
  | .RSeq a b => exitArrB Ts (.RSeq a b) || (exitArrBL Ts a && exitArrBL Ts b)
  | .RLetU64Zero x b =>
      exitArrB Ts (.RLetU64Zero x b) || (srcNameB x && !Ts.contains x && exitArrBL Ts b)
  | .RForRuntime x bd body =>
      srcNameB x && !Ts.contains x && loopBoundB bd && exitArrB Ts body
  | c => exitArrB Ts c

/-- **The pass on an accepted input with loops.** An input accepted by `exitArrBL Ts` is
    related by `ExitArrRelL` at the names of `Ts` to its scalarisation. -/
theorem exitArrBL_sound (Ts : List String) :
    ∀ c : LowCT, exitArrBL Ts c = true → ExitArrRelL (· ∈ Ts) c (scalarizeArrIn c) := by
  intro c
  induction c with
  | RSeq a b iha ihb =>
      intro h
      simp only [exitArrBL, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨ha, hb⟩
      · exact .base (exitArrB_sound Ts _ h)
      · simp only [scalarizeArrIn]
        exact .seq (iha ha) (ihb hb)
  | RLetU64Zero x b ih =>
      intro h
      simp only [exitArrBL, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true',
        List.contains_eq_mem, decide_eq_false_iff_not] at h
      rcases h with h | ⟨⟨hx, hxT⟩, hb⟩
      · exact .base (exitArrB_sound Ts _ h)
      · simp only [scalarizeArrIn]
        exact .letU64Zero (srcName_of_srcNameB hx) hxT (ih hb)
  | RForRuntime x bd body =>
      intro h
      simp only [exitArrBL, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
        decide_eq_false_iff_not] at h
      obtain ⟨⟨⟨hx, hxT⟩, hbd⟩, hb⟩ := h
      simp only [scalarizeArrIn]
      exact .loop (srcName_of_srcNameB hx) hxT hbd (exitArrB_sound Ts body hb)
  | _ => intro h; exact .base (exitArrB_sound Ts _ h)

end Loops

/-! ## 7. The exit frame of a function returning an array -/

/-- The command leaves the scalar `s` unwritten: no scalar write, word binder or loop index
    names `s`, and no command outside those listed. -/
def scalarKeepsB (s : String) : LowCT → Bool
  | .RSkip => true
  | .RSeq a b => scalarKeepsB s a && scalarKeepsB s b
  | .RLetU64Zero x b => x != s && scalarKeepsB s b
  | .RLetZero _ _ b => scalarKeepsB s b
  | .RScalarSet x _ => x != s
  | .RScalarSetExpr x _ => x != s
  | .RIfNz _ a b => scalarKeepsB s a && scalarKeepsB s b
  | .RArrLoad _ _ _ => true
  | .RArrStore _ _ _ => true
  | .RLimbStoreExpr _ _ _ => true
  | .RCopy _ _ => true
  | .RFor x _ b => x != s && scalarKeepsB s b
  | .RForRuntime x _ b => x != s && scalarKeepsB s b
  | _ => false

/-- **Scalar frame.** A run of a command that `scalarKeepsB s` accepts leaves the scalar `s`
    unchanged. -/
theorem rustExec_scalarKeeps {s : String} {c : LowCT} {rs rs' : RustState}
    (h : RustExec N L c rs rs') (hk : scalarKeepsB s c = true) :
    rs'.rsScalar s = rs.rsScalar s := by
  induction h with
  | skip => rfl
  | seq _ _ _ _ _ _ _ ih1 ih2 =>
      simp only [scalarKeepsB, Bool.and_eq_true] at hk
      rw [ih2 hk.2, ih1 hk.1]
  | letZero _ _ _ _ _ _ ih =>
      exact ih hk
  | letU64Zero x _ _ _ _ ih =>
      simp only [scalarKeepsB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
      rw [ih hk.2]
      simp [rsSetScalar, Ne.symm hk.1]
  | scalarSet x _ _ =>
      simp only [scalarKeepsB, bne_iff_ne, ne_eq] at hk
      simp [rsSetScalar, Ne.symm hk]
  | ifTrue _ _ _ _ _ _ _ _ _ ih =>
      simp only [scalarKeepsB, Bool.and_eq_true] at hk
      exact ih hk.1
  | ifFalse _ _ _ _ _ _ _ ih =>
      simp only [scalarKeepsB, Bool.and_eq_true] at hk
      exact ih hk.2
  | forZero => rfl
  | forSucc x _ _ _ _ _ _ _ ih1 ih2 =>
      simp only [scalarKeepsB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
      rw [ih2 hk.2, ← ih1 (by simp [scalarKeepsB, hk.1, hk.2])]
      simp [rsSetScalar, Ne.symm hk.1]
  | forRuntime _ _ _ _ _ _ ih =>
      simp only [scalarKeepsB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk
      exact ih (by simp [scalarKeepsB, hk.1, hk.2])
  | scalarSetExpr x _ _ =>
      simp only [scalarKeepsB, bne_iff_ne, ne_eq] at hk
      simp [rsSetScalar, Ne.symm hk]
  | limbStoreExpr => rfl
  | arrStore => rfl
  | arrLoad => rfl
  | copy => rfl
  | _ => simp [scalarKeepsB] at hk

/-- The loop bound `e - 0` as `e`. -/
def normBound : SExpr → SExpr
  | .SSub e (.SLit 0) => e
  | e => e

theorem normBound_evalState (e : SExpr) (rs : RustState) :
    (normBound e).evalState rs = e.evalState rs := by
  unfold normBound
  split
  · simp [SExpr.evalState]
  · rfl

/-- A counted loop whose trip body is guarded by a zero flag `r` it leaves unwritten runs its
    trip body unguarded, and keeps `r` zero. -/
theorem rFor_guard_elim {x r : String} {body : LowCT} (hxr : x ≠ r)
    (hk : scalarKeepsB r body = true) :
    ∀ (n : Nat) {rs rs' : RustState}, RustExec N L (.RFor x n (.RIfNz r .RSkip body)) rs rs' →
      rs.rsScalar r = 0 → RustExec N L (.RFor x n body) rs rs' ∧ rs'.rsScalar r = 0
  | 0, _, _, h, h0 => by cases h; exact ⟨.forZero _ _ _, h0⟩
  | n + 1, _, _, h, h0 => by
      cases h with
      | forSucc _ _ _ _ r₁ _ hf hb =>
          obtain ⟨hf', h1⟩ := rFor_guard_elim hxr hk n hf h0
          have hg : (rsSetScalar r₁ x n).rsScalar r = 0 := by simp [rsSetScalar, Ne.symm hxr, h1]
          cases hb with
          | ifTrue _ _ _ _ _ v hv hv0 _ => exact absurd (hv ▸ hg) hv0
          | ifFalse _ _ _ _ _ _ hb =>
              exact ⟨.forSucc _ _ _ _ _ _ hf' hb, (rustExec_scalarKeeps hb hk).trans hg⟩

/-- The run loop of the exit frame, `RLetU64Zero r (RLetU64Zero v (RForRuntime x b (RIfNz r
    RSkip body)))`, with a trip body leaving the flag `r` unwritten, with the flag test removed
    and the bound `normBound b`; every other command unchanged. -/
def exitRunNorm : LowCT → LowCT
  | .RLetU64Zero r (.RLetU64Zero v (.RForRuntime x bd (.RIfNz r' .RSkip body))) =>
      if r' = r ∧ v ≠ r ∧ x ≠ r ∧ scalarKeepsB r body = true then
        .RLetU64Zero r (.RLetU64Zero v (.RForRuntime x (normBound bd) body))
      else .RLetU64Zero r (.RLetU64Zero v (.RForRuntime x bd (.RIfNz r' .RSkip body)))
  | c => c

/-- **The run loop keeps its runs.** -/
theorem exitRunNorm_run {c : LowCT} {rs rs' : RustState} (h : RustExec N L c rs rs') :
    RustExec N L (exitRunNorm c) rs rs' := by
  unfold exitRunNorm
  split
  · rename_i r v x bd r' body
    split
    · rename_i hc
      obtain ⟨rfl, hvr, hxr, hk⟩ := hc
      cases h with
      | letU64Zero _ _ _ _ h =>
      cases h with
      | letU64Zero _ _ _ _ h =>
      cases h with
      | forRuntime _ _ _ _ _ h =>
      have h0 : (rsSetScalar (rsSetScalar rs r' 0) v 0).rsScalar r' = 0 := by
        simp [rsSetScalar, Ne.symm hvr]
      obtain ⟨h', -⟩ := rFor_guard_elim hxr hk _ h h0
      refine .letU64Zero _ _ _ _ (.letU64Zero _ _ _ _ (.forRuntime _ _ _ _ _ ?_))
      rw [normBound_evalState]
      exact h'
    · exact h
  · exact h

/-- The flag, the result slot and the returned array of an exit frame
    `RLetU64Zero r (RLetU64Zero s (RSeq (RSeq (RSeq K (RScalarSet r 0)) (RCopy d a))
    (RIfNz r t RSkip)))` whose copy writes `s` from an array `a ≠ s`. -/
def exitFrameTail : LowCT → Option (String × String × String)
  | .RLetU64Zero r (.RLetU64Zero s (.RSeq (.RSeq (.RSeq _ (.RScalarSet r' 0)) (.RCopy d a))
      (.RIfNz r'' _ .RSkip))) =>
      if r' = r ∧ r'' = r ∧ d.locVar = s ∧ a.locVar ≠ s then some (r, s, a.locVar) else none
  | _ => none

/-- **The exit frame of a function returning an array, normalised.** On an exit frame
    (`exitFrameTail`), the frame without its tail (the flag reset, the copy of the array into
    the result slot and the flag test), around the normalised run loop `exitRunNorm K`; every
    other command unchanged. -/
def exitFrameNorm (c : LowCT) : LowCT :=
  match c, exitFrameTail c with
  | .RLetU64Zero r (.RLetU64Zero s (.RSeq (.RSeq (.RSeq K _) _) _)), some _ =>
      .RLetU64Zero r (.RLetU64Zero s (exitRunNorm K))
  | c, _ => c

/-- **Denotation of the exit-frame normalisation.** A run of `c` gives a run of
    `exitFrameNorm c` from the same state. Off an exit frame the two runs end in the same state;
    on an exit frame with flag `r`, result slot `s` and returned array `a`, they agree on every
    scalar other than `r` and every tower slot other than `s`, and the result slot of the
    original run holds the array `a` of the normalised run. -/
theorem exitFrameNorm_run {c : LowCT} {rs rs' : RustState} (h : RustExec N L c rs rs') :
    ∃ rs1, RustExec N L (exitFrameNorm c) rs rs1 ∧
      match exitFrameTail c with
      | none => rs1 = rs'
      | some (r, s, a) => (∀ y, y ≠ r → rs1.rsScalar y = rs'.rsScalar y) ∧
          (∀ y, y ≠ s → rs1.rsTower y = rs'.rsTower y) ∧ rs'.rsTower s = rs1.rsTower a := by
  cases ht : exitFrameTail c with
  | none =>
      refine ⟨rs', ?_, rfl⟩
      have hn : exitFrameNorm c = c := by
        unfold exitFrameNorm
        split
        · rename_i heq; rw [ht] at heq; cases heq
        · rfl
      rw [hn]; exact h
  | some p =>
      obtain ⟨r, s, a⟩ := p
      obtain ⟨K, d, a', t, rfl, hd, ha', has⟩ : ∃ K d a' t,
          c = .RLetU64Zero r (.RLetU64Zero s (.RSeq (.RSeq (.RSeq K (.RScalarSet r 0))
            (.RCopy d a')) (.RIfNz r t .RSkip))) ∧ d.locVar = s ∧ a'.locVar = a ∧ a ≠ s := by
        unfold exitFrameTail at ht
        split at ht
        · rename_i r₀ s₀ K₀ r' d₀ a₀ r'' t₀
          split at ht
          · rename_i hc
            obtain ⟨rfl, rfl, hd, has⟩ := hc
            cases ht
            exact ⟨K₀, d₀, a₀, t₀, rfl, hd, rfl, has⟩
          · cases ht
        · cases ht
      have hn : exitFrameNorm (.RLetU64Zero r (.RLetU64Zero s (.RSeq (.RSeq (.RSeq K
          (.RScalarSet r 0)) (.RCopy d a')) (.RIfNz r t .RSkip)))) =
          .RLetU64Zero r (.RLetU64Zero s (exitRunNorm K)) := by
        unfold exitFrameNorm
        rw [ht]
      rw [hn]
      dsimp only
      subst hd ha'
      obtain ⟨dn, dt⟩ := d
      obtain ⟨an, at'⟩ := a'
      cases h with
      | letU64Zero _ _ _ _ h =>
      cases h with
      | letU64Zero _ _ _ _ h =>
      cases h with
      | seq _ _ _ rC _ h h4 =>
      cases h with
      | seq _ _ _ rS _ h h3 =>
      cases h with
      | seq _ _ _ rK _ hK h2 =>
      cases h2
      cases h3 with
      | copy _ _ _ hty srcV hl =>
      simp only [Located.locDst] at hty
      subst hty
      cases h4 with
      | ifTrue _ _ _ _ _ v hv hv0 _ =>
          exact absurd (by rw [← hv]; simp [locatedUpdate, rsSetTower, rsSetScalar]) hv0
      | ifFalse _ _ _ _ _ _ h4 =>
      cases h4
      refine ⟨rK, .letU64Zero _ _ _ _ (.letU64Zero _ _ _ _ (exitRunNorm_run hK)), ?_, ?_, ?_⟩
      · intro y hy
        simp [locatedUpdate, rsSetTower, rsSetScalar, hy]
      · intro y hy
        simp only [locatedUpdate, Located.locDst]
        rw [rsSetTower_other _ _ _ _ (Ne.symm hy)]
        rfl
      · simp only [locatedUpdate, Located.locDst, rsSetTower_same]
        simp only [locatedLookup, Located.locDst] at hl
        have hl' : (rsSetScalar rK r 0).rsTower an = rK.rsTower an := rfl
        rw [hl'] at hl
        split at hl
        · rename_i t' w hw
          split at hl
          · rename_i he
            subst he
            cases hl
            exact hw.symm
          · cases hl
        · cases hl

/-! ## 8. The word-array lowering of the typed exit front -/

open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedRouteSeq (semG)

/-- The names of the arrays a command loads from or stores into. -/
def arrNames : LowCT → List String
  | .RSeq a b => arrNames a ++ arrNames b
  | .RLetU64Zero _ b => arrNames b
  | .RLetZero _ _ b => arrNames b
  | .RBlock b => arrNames b
  | .RIfNz _ t e => arrNames t ++ arrNames e
  | .RForRuntime _ _ b => arrNames b
  | .RFor _ _ b => arrNames b
  | .RWhileNz _ b => arrNames b
  | .RArrLoad _ src _ => [src.locVar]
  | .RArrStore arr _ _ => [arr.locVar]
  | _ => []

/-- **The word-array lowering** of an output of the typed exit front: the exit-frame
    normalisation `exitFrameNorm`, then the scalarisation `scalarizeArrIn`. -/
def exitArrLower (c : LowCT) : LowCT := scalarizeArrIn (exitFrameNorm c)

/-- The check of the word-array lowering: the normalised program is accepted by `exitArrBL`
    at the names of the arrays it accesses, all of them source names. -/
def exitArrOk (c : LowCT) : Bool :=
  (arrNames (exitFrameNorm c)).all srcNameB &&
    exitArrBL (arrNames (exitFrameNorm c)) (exitFrameNorm c)

/-- **The value of the word-array lowering.** Let `c` pass `exitArrOk`, with `T` the arrays the
    normalised program accesses. A `RustExec` run of `c` from `rs` to `rs'` gives a run of the
    normalised program `exitFrameNorm c` from `rs` to a state `rs1` related to `rs'` as
    `exitFrameNorm_run` states; when that run is in bounds (`ArrRunL`), and `env` reflects `rs`
    on the names `B ⊆ S` and binds the arrays of `T` to their views, `semG S` of the lowered
    program `exitArrLower c` runs to an environment binding every name bound after it to the
    word of its value in `rs1`, and the arrays of `T` to their views in `rs1`. -/
theorem exitArrLower_semG (V : ArrView L) {c : LowCT} (hok : exitArrOk c = true)
    {S : List String} {B : String → Prop} {rs rs' : RustState} {env : SEnvScalar}
    (hexec : RustExec N L c rs rs')
    (hrun : ArrRunL (N := N) V (exitFrameNorm c) rs)
    (hreads : readsAL B (exitArrLower c)) (hS : SrcList S) (hb : Bound env S)
    (hB : ∀ y, B y → y ∈ S) (henv : EnvBoundOn rs env B) (hir : ScalarInRange rs)
    (hA : ArrOn V rs env (· ∈ arrNames (exitFrameNorm c))) :
    ∃ rs1 env', RustExec N L (exitFrameNorm c) rs rs1 ∧
      (match exitFrameTail c with
        | none => rs1 = rs'
        | some (r, s, a) => (∀ y, y ≠ r → rs1.rsScalar y = rs'.rsScalar y) ∧
            (∀ y, y ≠ s → rs1.rsTower y = rs'.rsTower y) ∧ rs'.rsTower s = rs1.rsTower a) ∧
      semG S (exitArrLower c) env = some env' ∧
      EnvBoundOn rs1 env' (afterG B (exitArrLower c)) ∧ ScalarInRange rs1 ∧
      ArrOn V rs1 env' (· ∈ arrNames (exitFrameNorm c)) := by
  simp only [exitArrOk, Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨rs1, h1, hf⟩ := exitFrameNorm_run hexec
  obtain ⟨env', hs, henv', hir', -, -, -, hA'⟩ := exitArrL_semG V
    (fun y hy => srcName_of_srcNameB (hok.1 y hy)) (exitArrBL_sound _ _ hok.2) S B rs rs1 env
    h1 hrun hreads hS hb hB henv hir hA
  exact ⟨rs1, env', h1, hf, hs, henv', hir', hA'⟩

end CatCrypt.Crypto.Hax
