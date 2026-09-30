/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.GuardedAgree

/-!
# `RustExec` agrees with the guarded scalar semantics on a runtime-trip loop

A `RustExec` run of `RFor x n body` is a sequence of per-trip runs: trip `t` runs
`body` from the state reached after `t` trips, with the counter `x` set to `t`
(`rustExec_rFor_trips`, and `rustExec_rForRuntime_trips` for `RForRuntime`, whose
trip count is the value of the bound in the entry state).

The loop is not converted; each trip is. The trip command `guardedTripCmd x S body`
is the guarded conversion of `body` with the bound list `x :: S`, where `S` lists the
scalar names bound before the loop. `guardedTrips` folds it over the trips: trip `t`
runs it on the environment of the previous trip updated at `x` to the word `t`.

`guardedLoop_agree` applies `ifConvert_taken` once per trip. For a body in the
guarded fragment `IsCoveredSCtlGuarded` whose reads are bound by a set `B` of names
bound before the loop, together with `x`, the invariant `LoopInv` (the names of `B`
bound to the words of their values, the list `S` bound, the scalars in `u64` range,
and the word view of the tower names `T` at the types `τ`) holds after every trip,
and `guardedTrips` succeeds. The array oracles satisfy `LawfulArr` when `T` is
inhabited. The in-range side condition of the loop is `InRangeLoop`: `InRangeG` of
the body at the entry state of every trip.

On scalar-slot bodies (`IsScalarCmd`), `inRangeLoopBL` checks `InRangeLoop` along the
`runKL` run over an association-list store, trip by trip with `inRangeRunBL`
(`inRangeLoop_of_inRangeLoopBL`).

## Main definitions

* `ForTrips`: the per-trip runs of a counted loop along a sequence of states
* `guardedTripCmd`, `guardedTrips`: the converted trip and its fold over the trips
* `LoopInv`, `InRangeLoop`: the loop invariant and the in-range condition of a loop
* `inRangeLoopBL`: a sound Boolean check of `InRangeLoop` for a scalar-slot body

## Main results

* `rustExec_rFor_trips`, `rustExec_rFor_of_trips`: a run of `RFor x n body` is a
  sequence of `n` per-trip runs, and conversely
* `rustExec_rForRuntime_trips`: the same for `RForRuntime`
* `inRangeG_of_inRangeRunBL`: `inRangeRunBL` gives `InRangeG` for a scalar-slot command
* `inRangeLoop_of_inRangeLoopBL`: soundness of `inRangeLoopBL`
* `guardedTrip_agree`: one trip of the conversion tracks one trip of the run
* `guardedLoop_agree_rFor`, `guardedLoop_agree`: the trip fold tracks the run of
  `RFor` and of `RForRuntime`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLoop

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.RustExecSemScalarBridge
  (EnvBoundOn ScalarInRange scalarInRange_upd envBoundOn_mono towerOK TowerWordsOn
    towerWordsOn_updScalar)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectGuarded
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedAgree
open CatCrypt.Crypto.SecureCompilation.Dialects.GuardedUnroll

variable {N : Nat} {leafSpec : LeafSpec}

/-! ## Per-trip runs of a counted loop -/

/-- The per-trip runs of `RFor x n body` along the states `st`: trip `t < n` runs
    `body` from `st t` with the counter `x` set to `t`, to `st (t + 1)`. -/
def ForTrips (N : Nat) (leafSpec : LeafSpec) (x : String) (body : LowCT) (n : Nat)
    (st : Nat → RustState) : Prop :=
  ∀ t, t < n → RustExec N leafSpec body (rsSetScalar (st t) x t) (st (t + 1))

/-- Inversion of a run of `RFor x n body` into its `n` per-trip runs. -/
theorem rustExec_rFor_trips {x : String} {body : LowCT} :
    ∀ (n : Nat) {rs rs' : RustState}, RustExec N leafSpec (.RFor x n body) rs rs' →
      ∃ st : Nat → RustState, st 0 = rs ∧ st n = rs' ∧ ForTrips N leafSpec x body n st
  | 0, rs, _, h => by
      cases h
      exact ⟨fun _ => rs, rfl, rfl, fun _ ht => absurd ht (Nat.not_lt_zero _)⟩
  | n + 1, _, rs', h => by
      cases h with
      | forSucc _ _ _ _ r₁ _ hf hb =>
          obtain ⟨st, h0, hn, htr⟩ := rustExec_rFor_trips n hf
          refine ⟨fun t => if t ≤ n then st t else rs', ?_, ?_, ?_⟩
          · dsimp only; rw [if_pos (Nat.zero_le _)]; exact h0
          · dsimp only; rw [if_neg (by omega)]
          · intro t ht
            dsimp only
            by_cases htn : t < n
            · rw [if_pos (by omega), if_pos (by omega)]
              exact htr t htn
            · obtain rfl : t = n := by omega
              rw [if_pos le_rfl, if_neg (by omega), hn]
              exact hb

/-- `n` per-trip runs along `st` are a run of `RFor x n body` from `st 0` to `st n`. -/
theorem rustExec_rFor_of_trips {x : String} {body : LowCT} {st : Nat → RustState} :
    ∀ (n : Nat), ForTrips N leafSpec x body n st →
      RustExec N leafSpec (.RFor x n body) (st 0) (st n)
  | 0, _ => .forZero x body (st 0)
  | n + 1, h =>
      .forSucc x n body (st 0) (st n) (st (n + 1))
        (rustExec_rFor_of_trips n (fun t ht => h t (by omega))) (h n (by omega))

/-- Inversion of a run of `RForRuntime x bound body` into its per-trip runs; the trip
    count is the value of `bound` in the entry state. -/
theorem rustExec_rForRuntime_trips {x : String} {bound : SExpr} {body : LowCT}
    {rs rs' : RustState} (h : RustExec N leafSpec (.RForRuntime x bound body) rs rs') :
    ∃ st : Nat → RustState, st 0 = rs ∧ st (bound.evalState rs) = rs' ∧
      ForTrips N leafSpec x body (bound.evalState rs) st := by
  cases h with
  | forRuntime _ _ _ _ _ hf => exact rustExec_rFor_trips _ hf

/-! ## The in-range condition of a loop -/

/-- The in-range condition of `RFor x n body` from `rs`: `InRangeG` of the body at
    the entry state of every trip. -/
def InRangeLoop (N : Nat) (leafSpec : LeafSpec) (x : String) (body : LowCT) (n : Nat)
    (rs : RustState) : Prop :=
  ∀ t, t < n → ∀ r, RustExec N leafSpec (.RFor x t body) rs r →
    InRangeG N leafSpec body (rsSetScalar r x t)

/-- `inRangeRunBL` over a store gives `InRangeG` of a scalar-slot command at the
    store state. -/
theorem inRangeG_of_inRangeRunBL {c : LowCT} (hc : IsScalarCmd c) (k : Nat)
    (tw : String → Option (Σ t : TowerType, RustVal t)) {l : List (String × Nat)}
    (h : inRangeRunBL k c l = true) : InRangeG N leafSpec c (storeState tw l) :=
  inRangeRunB_sound k c _ hc (by rw [inRangeRunB_storeState]; exact h)

/-- The Boolean check of `InRangeLoop` over a store: `d` trips from trip `j`, each
    checked by `inRangeRunBL` and run by `runKL`. -/
def inRangeLoopBL (k : Nat) (x : String) (body : LowCT) :
    Nat → Nat → List (String × Nat) → Bool
  | _, 0, _ => true
  | j, d + 1, l => inRangeRunBL k body (insertL l x j) &&
      match runKL k body (insertL l x j) with
      | some l' => inRangeLoopBL k x body (j + 1) d l'
      | none => false

theorem inRangeLoopBL_sound {x : String} {body : LowCT} (hc : IsScalarCmd body) (k : Nat)
    (tw : String → Option (Σ t : TowerType, RustVal t)) :
    ∀ (d j : Nat) (l : List (String × Nat)) (st : Nat → RustState),
      inRangeLoopBL k x body j d l = true → st j = storeState tw l →
      ∀ t, j ≤ t → t < j + d →
        (∀ i, j ≤ i → i < t →
          RustExec N leafSpec body (rsSetScalar (st i) x i) (st (i + 1))) →
        InRangeG N leafSpec body (rsSetScalar (st t) x t) := by
  intro d
  induction d with
  | zero => intro j _ _ _ _ t hjt ht; omega
  | succ d ih =>
      intro j l st h hj t hjt ht htr
      simp only [inRangeLoopBL, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      by_cases htj : t = j
      · subst htj
        rw [hj, rsSetScalar_storeState]
        exact inRangeG_of_inRangeRunBL hc k tw h1
      · cases hr : runKL k body (insertL l x j) with
        | none => rw [hr] at h2; cases h2
        | some l' =>
            rw [hr] at h2
            have hrun : RustExec N leafSpec body (rsSetScalar (st j) x j) (storeState tw l') := by
              rw [hj, rsSetScalar_storeState]
              exact runK_rustExec k body _ _ (by rw [runK_storeState, hr]; rfl)
            have hj1 : st (j + 1) = storeState tw l' :=
              (rustExec_deterministic hrun hc (htr j le_rfl (by omega))).symm
            exact ih (j + 1) l' st h2 hj1 t (by omega) (by omega)
              (fun i hi hit => htr i (by omega) hit)

/-- Soundness of `inRangeLoopBL`: on a scalar-slot body, a check of `n` trips from
    trip `0` over the store `l` gives `InRangeLoop` at the store state. -/
theorem inRangeLoop_of_inRangeLoopBL {x : String} {body : LowCT} (hc : IsScalarCmd body)
    (k : Nat) (tw : String → Option (Σ t : TowerType, RustVal t)) {n : Nat}
    {l : List (String × Nat)} (h : inRangeLoopBL k x body 0 n l = true) :
    InRangeLoop N leafSpec x body n (storeState tw l) := by
  intro t ht r hr
  obtain ⟨st, h0, hn, htr⟩ := rustExec_rFor_trips t hr
  rw [← hn]
  exact inRangeLoopBL_sound hc k tw n 0 l st h h0 t (Nat.zero_le _) (by omega)
    (fun i _ hit => htr i hit)

/-! ## The converted trip and its fold -/

/-- The trip command: the guarded conversion of `body` with the bound list `x :: S`. -/
def guardedTripCmd (x : String) (S : List String) (body : LowCT) : LowCT :=
  (ifConvert none (x :: S) 0 body).1

/-- The fold of the trip command over `n` trips: trip `t` runs it on the
    environment of the previous trip updated at `x` to the word `t`. -/
def guardedTrips (x : String) (S : List String) (body : LowCT) :
    Nat → SEnvScalar → Option SEnvScalar
  | 0, env => some env
  | n + 1, env => (guardedTrips x S body n env).bind fun e =>
      semScalar (guardedTripCmd x S body) (e.upd x (t := .sword 64) (BitVec.ofNat 64 n))

/-- The loop invariant: the names of `B` are bound to the words of their values, the
    names of `S` are bound words, every scalar is in `u64` range, and the tower names
    `T` are in the word view at the types `τ`. -/
def LoopInv (B : String → Prop) (S : List String) (T : String → Prop)
    (τ : String → TowerType) (rs : RustState) (env : SEnvScalar) : Prop :=
  EnvBoundOn rs env B ∧ Bound env S ∧ ScalarInRange rs ∧ TowerWordsOn rs env T ∧
    TowerTyped rs T τ

/-- One trip: from a state and environment in `LoopInv`, the trip command run on the
    environment updated at `x` to the word `t` tracks the run of `body` from the state
    with the counter at `t`, and the invariant holds after it. -/
theorem guardedTrip_agree {body : LowCT} (hc : IsCoveredSCtlGuarded body)
    {x : String} {S : List String} {B T : String → Prop} {τ : String → TowerType}
    (hT : ∀ y, T y → srcName y) (hlaw : (∃ y, T y) → LawfulArr leafSpec)
    (hx : srcName x) (hxT : ¬ T x) (hS : SrcList S) (hST : ∀ y ∈ S, ¬ T y)
    (hB : ∀ y, B y → y ∈ S) (hreads : readsG (fun y => B y ∨ y = x) body)
    (htok : towerOK T body) (hty : ArrTy τ body)
    {t : Nat} (ht : t < 2 ^ 64) {r r' : RustState} {env : SEnvScalar}
    (hexec : RustExec N leafSpec body (rsSetScalar r x t) r')
    (hIR : InRangeG N leafSpec body (rsSetScalar r x t))
    (hinv : LoopInv B S T τ r env) :
    ∃ env', semScalar (guardedTripCmd x S body)
        (env.upd x (t := .sword 64) (BitVec.ofNat 64 t)) = some env' ∧
      LoopInv B S T τ r' env' := by
  obtain ⟨henv, hb, hir, htw, htyT⟩ := hinv
  have hSx : SrcList (x :: S) := srcList_cons hx hS
  have hsub : ∀ y, (B y ∨ y = x) → y ∈ x :: S := by
    rintro y (hy | rfl)
    · exact List.mem_cons_of_mem _ (hB y hy)
    · exact List.mem_cons_self
  have hb0 : Bound (env.upd x (t := .sword 64) (BitVec.ofNat 64 t)) (x :: S) := by
    intro y hy
    by_cases hyx : y = x
    · subst hyx; rw [readU64_of_env upd_self]; rfl
    · rw [readU64_eq_of_env (upd_ne hyx)]
      exact hb y (List.mem_of_ne_of_mem hyx hy)
  have henv0 : EnvBoundOn (rsSetScalar r x t) (env.upd x (t := .sword 64) (BitVec.ofNat 64 t))
      (fun y => B y ∨ y = x) := by
    intro y hy hnt
    by_cases hyx : y = x
    · subst hyx; rw [upd_self]; simp [rsSetScalar]
    · rw [upd_ne hyx, henv y (hy.resolve_right hyx) hnt]
      simp [rsSetScalar, hyx]
  have htw0 : TowerWordsOn (rsSetScalar r x t) (env.upd x (t := .sword 64) (BitVec.ofNat 64 t))
      T := towerWordsOn_updScalar (cnt := 0) htw (fun _ _ => rfl) x hxT _ t
  have hST' : ∀ y ∈ x :: S, ¬ T y := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hxT
    · exact hST y hy
  obtain ⟨env', hs, henv', hir', hb', _, htw', htyT'⟩ :=
    ifConvert_taken hc T τ hT hlaw none (x :: S) 0 (fun y => B y ∨ y = x)
      (rsSetScalar r x t) r' _ hexec hIR hreads (fun _ h => by cases h) hSx hb0 hsub
      henv0 (scalarInRange_upd hir x ht) htok hty htw0 htyT hST'
  obtain ⟨_, hsubS, _, _⟩ := ifConvert_static hc none (x :: S) 0 (fun y => B y ∨ y = x) hSx hsub
  exact ⟨env', hs, envBoundOn_mono henv' (fun y hy => le_afterG body _ y (Or.inl hy)),
    fun y hy => hb' y (hsubS y (List.mem_cons_of_mem _ hy)), hir', htw', htyT'⟩

/-- Agreement on a counted loop: for a body in the guarded fragment, a run of
    `RFor x n body` (`n ≤ 2^64`) from a state and environment in `LoopInv`, whose
    trips satisfy `InRangeLoop`, is tracked by the trip fold `guardedTrips`, and
    `LoopInv` holds at the end. -/
theorem guardedLoop_agree_rFor {body : LowCT} (hc : IsCoveredSCtlGuarded body)
    {x : String} {S : List String} {B T : String → Prop} {τ : String → TowerType}
    (hT : ∀ y, T y → srcName y) (hlaw : (∃ y, T y) → LawfulArr leafSpec)
    (hx : srcName x) (hxT : ¬ T x) (hS : SrcList S) (hST : ∀ y ∈ S, ¬ T y)
    (hB : ∀ y, B y → y ∈ S) (hreads : readsG (fun y => B y ∨ y = x) body)
    (htok : towerOK T body) (hty : ArrTy τ body) {rs : RustState} {env : SEnvScalar}
    (hinv : LoopInv B S T τ rs env) :
    ∀ (n : Nat) {rs' : RustState}, n ≤ 2 ^ 64 →
      RustExec N leafSpec (.RFor x n body) rs rs' → InRangeLoop N leafSpec x body n rs →
      ∃ env', guardedTrips x S body n env = some env' ∧ LoopInv B S T τ rs' env'
  | 0, _, _, hexec, _ => by
      cases hexec
      exact ⟨env, rfl, hinv⟩
  | n + 1, _, hn, hexec, hIRL => by
      cases hexec with
      | forSucc _ _ _ _ r₁ _ hf hb =>
          obtain ⟨e₁, he₁, hinv₁⟩ := guardedLoop_agree_rFor hc hT hlaw hx hxT hS hST hB
            hreads htok hty hinv n (by omega) hf (fun t ht r hr => hIRL t (by omega) r hr)
          obtain ⟨env', hs, hinv'⟩ := guardedTrip_agree hc hT hlaw hx hxT hS hST hB hreads
            htok hty (by omega) hb (hIRL n (by omega) r₁ hf) hinv₁
          refine ⟨env', ?_, hinv'⟩
          simp only [guardedTrips, he₁, Option.bind_some]
          exact hs

/-- Agreement on a runtime-trip loop: for a body in the guarded fragment, a run of
    `RForRuntime x bound body` from a state and environment in `LoopInv`, whose trip
    count `bound.evalState rs` is at most `2^64` and whose trips satisfy
    `InRangeLoop`, is tracked by `guardedTrips` over that trip count, and `LoopInv`
    holds at the end. -/
theorem guardedLoop_agree {body : LowCT} (hc : IsCoveredSCtlGuarded body)
    {x : String} {bound : SExpr} {S : List String} {B T : String → Prop}
    {τ : String → TowerType}
    (hT : ∀ y, T y → srcName y) (hlaw : (∃ y, T y) → LawfulArr leafSpec)
    (hx : srcName x) (hxT : ¬ T x) (hS : SrcList S) (hST : ∀ y ∈ S, ¬ T y)
    (hB : ∀ y, B y → y ∈ S) (hreads : readsG (fun y => B y ∨ y = x) body)
    (htok : towerOK T body) (hty : ArrTy τ body) {rs rs' : RustState} {env : SEnvScalar}
    (hinv : LoopInv B S T τ rs env)
    (hexec : RustExec N leafSpec (.RForRuntime x bound body) rs rs')
    (hn : bound.evalState rs ≤ 2 ^ 64)
    (hIRL : InRangeLoop N leafSpec x body (bound.evalState rs) rs) :
    ∃ env', guardedTrips x S body (bound.evalState rs) env = some env' ∧
      LoopInv B S T τ rs' env' := by
  cases hexec with
  | forRuntime _ _ _ _ _ hf =>
      exact guardedLoop_agree_rFor hc hT hlaw hx hxT hS hST hB hreads htok hty hinv _ hn hf hIRL

end CatCrypt.Crypto.SecureCompilation.Dialects.GuardedLoop
