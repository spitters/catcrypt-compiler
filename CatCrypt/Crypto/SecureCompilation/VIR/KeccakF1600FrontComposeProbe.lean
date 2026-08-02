/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/

import CatCrypt.Crypto.SecureCompilation.VIR.KeccakF1600FrontComposeShape

/-!
# PROBE: N-round front-composed Keccak-p[1600] — 24-round closure

The shape-interpreter engine + scalar-lowering simulation keystones live in the
sibling `KeccakF1600FrontComposeShape` (split out to halve peak elaboration
memory). This module keeps the Keccak-specific round recomposition
(`WSBlock`/`blockOK`, the per-generator well-scopedness lemmas, `round_wellscoped`)
and the 24-round closure (`shapeRun24_ok` / `front24_isSome` / `lowered24_isSome`).
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakF1600FrontComposeProbe

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.VIR.KeccakRoundFrontEmit
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms

set_option autoImplicit false

open CatCrypt.Crypto.Jasmin.LowCT in
/-- A straight-line block of `RScalarSetExpr` statements is *well-scoped from*
    `bound` when each statement's `SExpr` is accepted and reads only names already
    bound (the initial `bound` plus earlier targets). Purely syntactic and
    `SLit`-value-invisible, hence round-index independent. -/
def WSBlock (bound : List String) : List LowCT → Bool
  | [] => true
  | (.RScalarSetExpr x e) :: rest =>
      ShapeAccepts e && (baseVars e).all (fun n => decide (n ∈ bound)) &&
        WSBlock (x :: bound) rest
  | _ :: _ => false

open CatCrypt.Crypto.Jasmin.LowCT in
/-- The target slot names a block binds, in order. -/
def blockTargets : List LowCT → List String
  | [] => []
  | (.RScalarSetExpr x _) :: rest => x :: blockTargets rest
  | _ :: rest => blockTargets rest

theorem allMem_of {l bound : List String}
    (h : l.all (fun n => decide (n ∈ bound)) = true) : ∀ n ∈ l, n ∈ bound :=
  fun n hn => of_decide_eq_true (List.all_eq_true.mp h n hn)

open CatCrypt.Crypto.Jasmin.LowCT in
/-- `shapeTranslate` threads through a `seqAll`-cons via `Option.bind`. -/
theorem shapeTranslate_seqAll_cons (σ : ShapeMap) (c : LowCT) (cs : List LowCT) :
    shapeTranslate σ (seqAll (c :: cs)) =
      (shapeTranslate σ c).bind (fun σ' => shapeTranslate σ' (seqAll cs)) := by
  cases cs with
  | nil => cases hc : shapeTranslate σ c <;> simp [seqAll, shapeTranslate, hc]
  | cons d ds => cases hc : shapeTranslate σ c <;> simp [seqAll, shapeTranslate, hc]

open CatCrypt.Crypto.Jasmin.LowCT in
/-- **Semantic block success.** A block well-scoped from `bound`, run from a shape
    binding all of `bound` at `.sword 64`, succeeds; the result preserves every
    `.sword 64` binding and binds every block target at `.sword 64`. Induction on
    the statement list — σ-parametric, NO `native_decide`. -/
theorem blockOK : ∀ (stmts : List LowCT) {bound : List String} {σ : ShapeMap},
    WSBlock bound stmts = true →
    (∀ n ∈ bound, shapeLookup σ n = some (.sword 64)) →
    ∃ σ', shapeTranslate σ (seqAll stmts) = some σ' ∧
      (∀ m, shapeLookup σ m = some (.sword 64) → shapeLookup σ' m = some (.sword 64)) ∧
      (∀ n ∈ blockTargets stmts, shapeLookup σ' n = some (.sword 64)) := by
  intro stmts
  induction stmts with
  | nil =>
      intro bound σ _ _
      exact ⟨σ, by simp [seqAll, shapeTranslate], fun m hm => hm, by simp [blockTargets]⟩
  | cons s rest ih =>
      intro bound σ hws hb
      cases s
      case RScalarSetExpr x e =>
          simp only [WSBlock, Bool.and_eq_true] at hws
          obtain ⟨⟨hacc, hsub⟩, hwsrest⟩ := hws
          obtain ⟨σ₁, nm, c, hlow, hnm, hmon⟩ :=
            shapeLowerSExpr_ok e (cnt := 0) hacc (fun n hn => hb n (allMem_of hsub n hn))
          have hstep : shapeTranslate σ (.RScalarSetExpr x e)
              = some (shapeBind σ₁ x (.sword 64)) := by
            simp only [shapeTranslate, hlow, hnm]
          have hb' : ∀ n ∈ (x :: bound),
              shapeLookup (shapeBind σ₁ x (.sword 64)) n = some (.sword 64) := by
            intro n hn
            rcases List.mem_cons.mp hn with rfl | hn
            · simp [shapeBind, shapeLookup]
            · exact shapeBind_pres (hmon n (hb n hn))
          obtain ⟨σ', hrest, hmonrest, htgt⟩ := ih hwsrest hb'
          refine ⟨σ', ?_, ?_, ?_⟩
          · rw [shapeTranslate_seqAll_cons, hstep]; simpa using hrest
          · exact fun m hm => hmonrest m (shapeBind_pres (hmon m hm))
          · intro t ht
            rcases List.mem_cons.mp (by simpa [blockTargets] using ht) with heq | ht
            · rw [heq]; exact hmonrest x (by simp [shapeBind, shapeLookup])
            · exact htgt t ht
      all_goals simp [WSBlock] at hws

/-- The 25 state-lane names `a0…a24`. -/
def aLaneNames : List String := (List.range 25).map aN

/-- The round invariant: `a0…a24` all bound at `.sword 64`. -/
def GoodShape (σ : ShapeMap) : Prop := ∀ n ∈ aLaneNames, shapeLookup σ n = some (.sword 64)

open CatCrypt.Crypto.Jasmin.LowCT in
/-- The r-independent prefix of a round (θ-C, θ-D, θ-apply, ρ∘π, χ). -/
def firstPart : List LowCT :=
  (List.range 5).map cStmt ++ (List.range 5).map dStmt ++ (List.range 25).map pStmt
  ++ (List.range 25).map bStmt ++ (List.range 25).map hStmt

open CatCrypt.Crypto.Jasmin.LowCT in
/-- The flat `RScalarSetExpr` statement list of one round: the r-independent
    prefix plus the 25-lane ι+write-back (the only round-index-dependent part).
    `roundBodyR r = seqAll (roundStmts r)` by definition. -/
def roundStmts (r : Nat) : List LowCT := firstPart ++ (List.range 25).map (aBackStmt r)

theorem roundBodyR_eq_seqAll (r : Nat) : roundBodyR r = seqAll (roundStmts r) := rfl

open CatCrypt.Crypto.Jasmin.LowCT in
/-- The `bound` a straight-line block leaves after threading (targets prepended). -/
def boundAfter : List LowCT → List String → List String
  | [], bound => bound
  | (.RScalarSetExpr x _) :: rest, bound => boundAfter rest (x :: bound)
  | _ :: rest, bound => boundAfter rest bound

open CatCrypt.Crypto.Jasmin.LowCT in
/-- `WSBlock` splits over an append: the prefix is well-scoped from `bound` and
    the suffix from the bound the prefix leaves. -/
theorem WSBlock_append (l1 l2 : List LowCT) (bound : List String) :
    WSBlock bound (l1 ++ l2) = (WSBlock bound l1 && WSBlock (boundAfter l1 bound) l2) := by
  induction l1 generalizing bound with
  | nil => simp [WSBlock, boundAfter]
  | cons s rest ih =>
      cases s
      case RScalarSetExpr x e =>
          simp only [List.cons_append, WSBlock, boundAfter, ih, Bool.and_assoc]
      all_goals simp [WSBlock, boundAfter]

open CatCrypt.Crypto.Jasmin.LowCT in
/-- `WSBlock` over the ι+write-back list is round-index independent: `aBackStmt r`
    and `aBackStmt 0` have the same target, `ShapeAccepts`, and `baseVars` (only
    the `SLit` round constant differs, and the shape ignores `SLit` values). -/
theorem WSBlock_aBack_congr (r : Nat) (l : List Nat) (bound : List String) :
    WSBlock bound (l.map (aBackStmt r)) = WSBlock bound (l.map (aBackStmt 0)) := by
  induction l generalizing bound with
  | nil => rfl
  | cons i rest ih =>
      cases i with
      | zero => simp [List.map, aBackStmt, WSBlock, ShapeAccepts, baseVars, ih]
      | succ k => simp [List.map, aBackStmt, WSBlock, ih]

/-! ### Structural (`decide`-free) well-scopedness of one round

`round_wellscoped` used to `decide` well-scopedness over each Keccak sub-block, but
each `decide (n ∈ bound)` scans a growing 100+-name string alist, so the kernel
`decide` is quadratic and stalls (and `native_decide` OOMs gcc C-gen). The
replacement below reasons at the GENERATOR level: name-membership is by structural
`List.map`/`List.range` lemmas (no alist scan), each θ/ρ/π/χ/ι builder has one
small scope contract, and a single `WSBlock_map` induction lifts each builder to
its whole `(List.range k).map` block. The blocks recompose via `WSBlock_append`.
No `decide`/`native_decide` touches a block larger than one ~10-node builder. -/

/-- Name-level membership: `f k` is in `(List.range n).map f` when `k < n`. Replaces
    the alist-scanning `decide (f k ∈ …)` with a structural `List.mem_map` step. -/
theorem mapN_mem {f : Nat → String} {k n : Nat} (h : k < n) :
    f k ∈ (List.range n).map f :=
  List.mem_map.mpr ⟨k, List.mem_range.mpr h, rfl⟩

/-- Every `a`-lane name is in `aLaneNames` (the 25-lane invariant carrier). -/
theorem aN_mem {i : Nat} (h : i < 25) : aN i ∈ aLaneNames := mapN_mem h

/-! #### `WSBlock` over a `List.map`-generated block, by induction on the map

A `(List.range k).map f` block is well-scoped from `bound` whenever
each `f i` is a single `RScalarSetExpr` that is `ShapeAccepts`ed and reads only
names already in `bound`. The growing bound-set threaded by `WSBlock` is handled by
monotonicity (`List.mem_cons_of_mem`): a read valid at the block-start bound stays
valid as targets are prepended. NO `decide` over the block. -/
theorem WSBlock_map (f : Nat → LowCT) : ∀ (l : List Nat) (bound : List String),
    (∀ i ∈ l, ∃ x e, f i = LowCT.RScalarSetExpr x e ∧ ShapeAccepts e = true ∧
        ∀ n ∈ baseVars e, n ∈ bound) →
    WSBlock bound (l.map f) = true := by
  intro l
  induction l with
  | nil => intro bound _; rfl
  | cons i rest ih =>
      intro bound h
      obtain ⟨x, e, hfi, hacc, hreads⟩ := h i List.mem_cons_self
      simp only [List.map_cons, hfi, WSBlock, Bool.and_eq_true]
      refine ⟨⟨hacc, ?_⟩, ?_⟩
      · simp only [List.all_eq_true, decide_eq_true_eq]
        exact hreads
      · apply ih
        intro j hj
        obtain ⟨x', e', hfj, hacc', hreads'⟩ := h j (List.mem_cons_of_mem i hj)
        exact ⟨x', e', hfj, hacc', fun n hn => List.mem_cons_of_mem x (hreads' n hn)⟩

/-! #### `boundAfter` membership (no reverse bookkeeping)

`boundAfter l bound` is `bound` grown by every target of `l`. We only need that it
contains (a) everything already in `bound` and (b) every block target — proved by a
direct induction, never materialising the reversed list. -/

/-- Everything in `bound` survives into `boundAfter l bound`. -/
theorem mem_boundAfter_of_mem_bound (l : List LowCT) {bound : List String} {n : String}
    (h : n ∈ bound) : n ∈ boundAfter l bound := by
  induction l generalizing bound with
  | nil => exact h
  | cons s rest ih =>
      cases s
      case RScalarSetExpr x e => exact ih (bound := x :: bound) (List.mem_cons_of_mem x h)
      all_goals exact ih h

/-- Every block target of `l` lands in `boundAfter l bound`. -/
theorem mem_boundAfter_of_mem_targets (l : List LowCT) {bound : List String} {n : String}
    (h : n ∈ blockTargets l) : n ∈ boundAfter l bound := by
  induction l generalizing bound with
  | nil => simp [blockTargets] at h
  | cons s rest ih =>
      cases s
      case RScalarSetExpr x e =>
          rcases List.mem_cons.mp h with rfl | h'
          · exact mem_boundAfter_of_mem_bound rest List.mem_cons_self
          · exact ih (bound := x :: bound) h'
      all_goals exact ih h

open CatCrypt.Crypto.Jasmin.LowCT in
/-- `blockTargets` distributes over append. -/
theorem blockTargets_append (l1 l2 : List LowCT) :
    blockTargets (l1 ++ l2) = blockTargets l1 ++ blockTargets l2 := by
  induction l1 with
  | nil => rfl
  | cons s rest ih => cases s <;> simp [blockTargets, ih]

/-- A block's own targets land in `boundAfter (l1 ++ l2) bound` when it is `l2`. -/
theorem mem_boundAfter_last (l1 l2 : List LowCT) (bound : List String) {n : String}
    (h : n ∈ blockTargets l2) : n ∈ boundAfter (l1 ++ l2) bound := by
  apply mem_boundAfter_of_mem_targets
  rw [blockTargets_append]
  exact List.mem_append_right _ h

/-! #### Per-generator target-name identities (θ/ρ/π/χ blocks)

Each block's `blockTargets` is exactly the mapped name list — proved by induction on
the index list, unfolding one builder. `blockTargets_map_aBack` already exists. -/

theorem blockTargets_map_cStmt (l : List Nat) : blockTargets (l.map cStmt) = l.map cN := by
  induction l with
  | nil => rfl
  | cons i rest ih => simp only [List.map_cons, cStmt, blockTargets, ih]

theorem blockTargets_map_dStmt (l : List Nat) : blockTargets (l.map dStmt) = l.map dN := by
  induction l with
  | nil => rfl
  | cons i rest ih => simp only [List.map_cons, dStmt, blockTargets, ih]

theorem blockTargets_map_pStmt (l : List Nat) : blockTargets (l.map pStmt) = l.map pN := by
  induction l with
  | nil => rfl
  | cons i rest ih => simp only [List.map_cons, pStmt, blockTargets, ih]

theorem blockTargets_map_hStmt (l : List Nat) : blockTargets (l.map hStmt) = l.map hN := by
  induction l with
  | nil => rfl
  | cons i rest ih => simp only [List.map_cons, hStmt, blockTargets, ih]

/-- The ρ∘π lane index `π(i)` bound by `bStmt i`. -/
def bIdx (i : Nat) : Nat := (i / 5 % 5) + 5 * ((2 * (i % 5) + 3 * (i / 5)) % 5)

theorem blockTargets_map_bStmt (l : List Nat) :
    blockTargets (l.map bStmt) = l.map (fun i => bN (bIdx i)) := by
  induction l with
  | nil => rfl
  | cons i rest ih => simp only [List.map_cons, bStmt, bIdx, blockTargets, ih]

/-- `π` is a permutation of `Fin 25` (single small `decide` over `Nat` lists — no
    strings, no growing bound). -/
theorem bIdx_all : ∀ i ∈ List.range 25, i ∈ (List.range 25).map bIdx := by decide

/-- Surjectivity of `π` at the name level: every `b`-lane `bN i` (`i < 25`) is a
    target of the `bStmt` block. -/
theorem bN_mem_bTargets {i : Nat} (h : i < 25) :
    bN i ∈ (List.range 25).map (fun j => bN (bIdx j)) := by
  obtain ⟨j, hj, hji⟩ := List.mem_map.mp (bIdx_all i (List.mem_range.mpr h))
  exact List.mem_map.mpr ⟨j, hj, by rw [hji]⟩

/-! #### Per-block well-scopedness (each via one `WSBlock_map`) -/

/-- θ-C block: reads `a`-lanes. -/
theorem ws_cblock (bound : List String) (ha : ∀ n ∈ aLaneNames, n ∈ bound) :
    WSBlock bound ((List.range 5).map cStmt) = true := by
  apply WSBlock_map
  intro i hi
  have hi5 : i < 5 := List.mem_range.mp hi
  refine ⟨cN i, xorVars [aN i, aN (i + 5), aN (i + 10), aN (i + 15), aN (i + 20)], rfl, ?_, ?_⟩
  · simp [xorVars, ShapeAccepts]
  · intro n hn
    simp only [xorVars, baseVars, List.nil_append, List.singleton_append, List.cons_append,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, List.append_assoc, or_false] at hn
    apply ha
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> exact aN_mem (by omega)

/-- θ-D block: reads `c`-lanes. -/
theorem ws_dblock (bound : List String) (hc : ∀ n ∈ (List.range 5).map cN, n ∈ bound) :
    WSBlock bound ((List.range 5).map dStmt) = true := by
  apply WSBlock_map
  intro i hi
  have hi5 : i < 5 := List.mem_range.mp hi
  refine ⟨dN i, .SXor (.SVar (cN ((i + 4) % 5))) (rotLE (cN ((i + 1) % 5)) 1), rfl, ?_, ?_⟩
  · simp [rotLE, ShapeAccepts]
  · intro n hn
    simp only [rotLE, baseVars, List.nil_append, List.append_nil, List.singleton_append,
      List.cons_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      List.append_assoc, or_false] at hn
    apply hc
    rcases hn with rfl | rfl | rfl <;> exact mapN_mem (Nat.mod_lt _ (by norm_num))

/-- θ-apply block: reads `a`-lanes and `d`-lanes. -/
theorem ws_pblock (bound : List String) (ha : ∀ n ∈ aLaneNames, n ∈ bound)
    (hd : ∀ n ∈ (List.range 5).map dN, n ∈ bound) :
    WSBlock bound ((List.range 25).map pStmt) = true := by
  apply WSBlock_map
  intro i hi
  have hi25 : i < 25 := List.mem_range.mp hi
  refine ⟨pN i, .SXor (.SVar (aN i)) (.SVar (dN (i % 5))), rfl, ?_, ?_⟩
  · simp [ShapeAccepts]
  · intro n hn
    simp only [baseVars, List.nil_append, List.singleton_append, List.cons_append,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl
    · exact ha _ (aN_mem hi25)
    · exact hd _ (mapN_mem (Nat.mod_lt _ (by norm_num)))

/-- ρ∘π block: reads `p`-lanes. -/
theorem ws_bblock (bound : List String) (hp : ∀ n ∈ (List.range 25).map pN, n ∈ bound) :
    WSBlock bound ((List.range 25).map bStmt) = true := by
  apply WSBlock_map
  intro i hi
  have hi25 : i < 25 := List.mem_range.mp hi
  refine ⟨bN (bIdx i),
    (if KeccakEmit.rhoOffset i == 0 then .SVar (pN i) else rotLE (pN i) (KeccakEmit.rhoOffset i)),
    ?_, ?_, ?_⟩
  · simp [bStmt, bIdx]
  · cases KeccakEmit.rhoOffset i == 0 <;> simp [rotLE, ShapeAccepts]
  · intro n hn
    apply hp
    have hnp : n = pN i := by
      revert hn; cases KeccakEmit.rhoOffset i == 0 <;>
        simp [rotLE, baseVars, List.mem_cons, List.mem_singleton, List.not_mem_nil]
    rw [hnp]; exact mapN_mem hi25

/-- χ block: reads `b`-lanes (all of them via the ρ∘π permutation). -/
theorem ws_hblock (bound : List String) (hb : ∀ k, k < 25 → bN k ∈ bound) :
    WSBlock bound ((List.range 25).map hStmt) = true := by
  apply WSBlock_map
  intro i hi
  have hi25 : i < 25 := List.mem_range.mp hi
  refine ⟨hN i, .SXor (.SVar (bN i))
      (.SAnd (notE (bN ((i % 5 + 1) % 5 + 5 * (i / 5)))) (.SVar (bN ((i % 5 + 2) % 5 + 5 * (i / 5))))),
      rfl, ?_, ?_⟩
  · simp [notE, ShapeAccepts]
  · intro n hn
    simp only [notE, baseVars, List.nil_append, List.append_nil, List.singleton_append,
      List.cons_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      List.append_assoc, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact hb i hi25
    · exact hb _ (by omega)
    · exact hb _ (by omega)

/-- ι + write-back block: reads `h`-lanes (round-index independent — `SLit RC[r]`
    contributes no read). -/
theorem ws_abackblock (r : Nat) (bound : List String)
    (hh : ∀ n ∈ (List.range 25).map hN, n ∈ bound) :
    WSBlock bound ((List.range 25).map (aBackStmt r)) = true := by
  apply WSBlock_map
  intro i hi
  have hi25 : i < 25 := List.mem_range.mp hi
  rcases eq_or_ne i 0 with rfl | hne
  · refine ⟨aN 0, .SXor (.SVar (hN 0)) (.SLit (KeccakEmit.roundConst r)), rfl, ?_, ?_⟩
    · simp [ShapeAccepts]
    · intro n hn
      simp only [baseVars, List.nil_append, List.append_nil, List.singleton_append,
        List.cons_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hn
      subst hn; exact hh _ (mapN_mem (by norm_num))
  · refine ⟨aN i, .SVar (hN i), ?_, ?_, ?_⟩
    · simp only [aBackStmt, beq_iff_eq, hne, if_neg, reduceIte]
    · simp [ShapeAccepts]
    · intro n hn
      simp only [baseVars, List.nil_append, List.append_nil, List.singleton_append,
        List.cons_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hn
      subst hn; exact hh _ (mapN_mem hi25)

/-- One round is well-scoped from the a-lanes — proved by structural recomposition of
    the six θ/ρ/π/χ/ι sub-blocks (`WSBlock_append` + the per-block `ws_*` lemmas).
    Name-membership is by `List.map`/`List.range` lemmas and the `π`-permutation
    `decide` over `Nat` lists; NO `decide`/`native_decide` touches a growing string
    bound-set, so no kernel-`decide` stall / gcc-`native_decide` OOM. -/
theorem round_wellscoped (r : Nat) : WSBlock aLaneNames (roundStmts r) = true := by
  rw [roundStmts]
  simp only [firstPart]
  rw [WSBlock_append, WSBlock_append, WSBlock_append, WSBlock_append, WSBlock_append]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- θ-C from the a-lanes
    exact ws_cblock aLaneNames (fun n h => h)
  · -- θ-D reads c-lanes (the whole prefix so far)
    apply ws_dblock
    intro n hn
    exact mem_boundAfter_of_mem_targets _ (by rw [blockTargets_map_cStmt]; exact hn)
  · -- θ-apply reads a-lanes (in bound) and d-lanes (last block of the prefix)
    apply ws_pblock
    · intro n hn; exact mem_boundAfter_of_mem_bound _ hn
    · intro n hn; exact mem_boundAfter_last _ _ _ (by rw [blockTargets_map_dStmt]; exact hn)
  · -- ρ∘π reads p-lanes (last block of the prefix)
    apply ws_bblock
    intro n hn
    exact mem_boundAfter_last _ _ _ (by rw [blockTargets_map_pStmt]; exact hn)
  · -- χ reads all b-lanes (last block of the prefix, via π-surjectivity)
    apply ws_hblock
    intro k hk
    exact mem_boundAfter_last _ _ _ (by rw [blockTargets_map_bStmt]; exact bN_mem_bTargets hk)
  · -- ι + write-back reads h-lanes (last block of the prefix)
    apply ws_abackblock
    intro n hn
    exact mem_boundAfter_last _ _ _ (by rw [blockTargets_map_hStmt]; exact hn)

/-- The write-back list binds exactly `a0…a24`, in order (round-index blind). -/
theorem blockTargets_map_aBack (r : Nat) (l : List Nat) :
    blockTargets (l.map (aBackStmt r)) = l.map aN := by
  induction l with
  | nil => rfl
  | cons i rest ih =>
      cases i with
      | zero => simp [List.map, aBackStmt, blockTargets, ih]
      | succ k => simp [List.map, aBackStmt, blockTargets, ih]

/-- Every a-lane is a write-back target of the round. -/
theorem aLane_mem_blockTargets (r : Nat) : ∀ n ∈ aLaneNames, n ∈ blockTargets (roundStmts r) := by
  intro n hn
  rw [roundStmts, blockTargets_append, blockTargets_map_aBack]
  exact List.mem_append.mpr (Or.inr hn)

/-- **One round preserves the a-lane invariant.** From a `GoodShape`, the round
    translates and rebinds all a-lanes at `.sword 64`. Uses the semantic `blockOK`
    and the syntactic `round_wellscoped`; NO per-round `native_decide`. -/
theorem round_step (r : Nat) {σ : ShapeMap} (hgs : GoodShape σ) :
    ∃ σ', shapeTranslate σ (roundBodyR r) = some σ' ∧ GoodShape σ' := by
  rw [roundBodyR_eq_seqAll]
  obtain ⟨σ', hst, _, htgt⟩ := blockOK (roundStmts r) (round_wellscoped r) hgs
  exact ⟨σ', hst, fun n hn => htgt n (aLane_mem_blockTargets r n hn)⟩

/-- **A list of rounds preserves the a-lane invariant** (induction on the list —
    O(rounds), each step is `round_step`, no `native_decide`). -/
theorem roundsList_step : ∀ (rs : List Nat) {σ : ShapeMap}, GoodShape σ →
    ∃ σ', shapeTranslate σ (seqAll (rs.map roundBodyR)) = some σ' ∧ GoodShape σ' := by
  intro rs
  induction rs with
  | nil => intro σ hgs; exact ⟨σ, by simp [seqAll, shapeTranslate], hgs⟩
  | cons r rest ih =>
      intro σ hgs
      rw [List.map_cons, shapeTranslate_seqAll_cons]
      obtain ⟨σ1, hst1, hgs1⟩ := round_step r hgs
      rw [hst1, Option.bind_some]
      exact ih hgs1

open CatCrypt.Crypto.Jasmin.LowCT in
/-- `shapeTranslate` threads through a `seqAll` of an append via `Option.bind`. -/
theorem shapeTranslate_seqAll_append (σ : ShapeMap) (l1 l2 : List LowCT) :
    shapeTranslate σ (seqAll (l1 ++ l2)) =
      (shapeTranslate σ (seqAll l1)).bind (fun σ' => shapeTranslate σ' (seqAll l2)) := by
  induction l1 generalizing σ with
  | nil => simp [seqAll, shapeTranslate]
  | cons c cs ih =>
      rw [List.cons_append, shapeTranslate_seqAll_cons, shapeTranslate_seqAll_cons]
      cases shapeTranslate σ c <;> simp [ih]

/-- The output-copy block is well-scoped from the a-lanes (concrete, `decide`). -/
theorem oCopy_wellscoped : WSBlock aLaneNames ((List.range 25).map oCopyStmt) = true := by decide

/-- The output-copy block binds exactly `o0…o24`. -/
theorem blockTargets_map_oCopy (l : List Nat) :
    blockTargets (l.map oCopyStmt) = l.map oN := by
  induction l with
  | nil => rfl
  | cons i rest ih => simp [List.map, oCopyStmt, blockTargets, ih]

/-- `srcShape` binds all a-lanes at `.sword 64`. -/
theorem shapeLookup_map_const (t : CryptoTy) :
    ∀ (names : List String) (n : String), n ∈ names →
      shapeLookup (names.map (fun m => (m, t))) n = some t := by
  intro names
  induction names with
  | nil => intro n hn; simp at hn
  | cons m rest ih =>
      intro n hn
      simp only [List.map, shapeLookup]
      split
      · rfl
      · rename_i hne
        rcases List.mem_cons.mp hn with rfl | hn
        · exact absurd rfl hne
        · exact ih n hn

theorem goodShape_srcShape : GoodShape srcShape :=
  fun n hn => shapeLookup_map_const _ wordNames n hn

/-- **The compositional 24-round shape run.** Threads the a-lane invariant through
    all 24 rounds (`roundsList_step`, O(rounds)) and the 25-lane output copy
    (`blockOK`), landing `o24` at `.sword 64` — the single `native_decide` gate is
    `round_wellscoped` (one round, syntactic). -/
theorem shapeRun24_ok' :
    (shapeTranslate srcShape (fullBody 24)).bind (fun σ => shapeLookup σ (oN 24))
      = some (.sword 64) := by
  obtain ⟨σR, hstR, hgsR⟩ := roundsList_step (List.range 24) goodShape_srcShape
  obtain ⟨σF, hstF, _, htgtF⟩ :=
    blockOK ((List.range 25).map oCopyStmt) oCopy_wellscoped hgsR
  have hfull : shapeTranslate srcShape (fullBody 24) = some σF := by
    show shapeTranslate srcShape
      (seqAll ((List.range 24).map roundBodyR ++ (List.range 25).map oCopyStmt)) = some σF
    rw [shapeTranslate_seqAll_append, hstR, Option.bind_some, hstF]
  rw [hfull, Option.bind_some]
  exact htgtF (oN 24) (by rw [blockTargets_map_oCopy]; exact List.mem_map_of_mem (by decide))

/-! ### The 24-round closure (compositional `isSome`)

Assembling the pieces: the shape run of the whole body succeeds (`shapeRun24_ok`,
the single cheap `native_decide`), `shapeTranslate_sim` transfers that success to
the real front `translateDialectControl` (which coincides with
`translateDialectFull` on this straight-line body), the `o24` lane resolves, the
`ContGood` prefix applies to the `ret` terminator, and the pure-arith backend
`cryptoDialectToJasminCom` lowers the result — all without ever materialising the
~9768-binding lowered `Com` that OOMs the monolithic `native_decide`. -/

/-- **The 24-round shape run succeeds and `o24` resolves at `.sword 64`.**
    Discharged per-round compositionally (`shapeRun24_ok'`): the a-lane invariant
    is threaded through all 24 rounds and the output copy, so the ONLY
    `native_decide` is the syntactic single-round well-scopedness check
    (`round_wellscoped`) — no multi-round decide, no `fullBody` evaluation. -/
theorem shapeRun24_ok :
    (shapeTranslate srcShape (fullBody 24)).bind (fun σ => shapeLookup σ (oN 24))
      = some (.sword 64) := shapeRun24_ok'

/-! #### The body lies in the covered fragment

`translateDialectControl_eq_full_of_covered` already relates the two fronts on
`IsCovered` bodies. What is left is membership: every statement the Keccak
generators emit is a single `RScalarSetExpr`, and `seqAll` of covered statements
is covered. The `RSeq` spine is traversed by induction, so the cost does not
grow with the round count. -/

open CatCrypt.Crypto.Jasmin.LowCT in
/-- A `seqAll` chain of covered statements is covered. -/
theorem covered_seqAll : ∀ (l : List LowCT), (∀ c ∈ l, IsCovered c) → IsCovered (seqAll l)
  | [], _ => IsCovered.rSkip
  | [c], h => h c List.mem_cons_self
  | c :: d :: cs, h =>
      IsCovered.rSeq (h c List.mem_cons_self)
        (covered_seqAll (d :: cs) fun x hx => h x (List.mem_cons_of_mem c hx))

theorem covered_cStmt (i : Nat) : IsCovered (cStmt i) := .rScalarSetExpr _ _
theorem covered_dStmt (i : Nat) : IsCovered (dStmt i) := .rScalarSetExpr _ _
theorem covered_pStmt (i : Nat) : IsCovered (pStmt i) := .rScalarSetExpr _ _
theorem covered_bStmt (i : Nat) : IsCovered (bStmt i) := .rScalarSetExpr _ _
theorem covered_hStmt (i : Nat) : IsCovered (hStmt i) := .rScalarSetExpr _ _
theorem covered_oCopyStmt (i : Nat) : IsCovered (oCopyStmt i) := .rScalarSetExpr _ _

theorem covered_aBackStmt (r i : Nat) : IsCovered (aBackStmt r i) := by
  unfold aBackStmt; split <;> exact .rScalarSetExpr _ _

/-- One round body is covered: every statement of `roundStmts` is a single
    `RScalarSetExpr`. -/
theorem covered_roundBodyR (r : Nat) : IsCovered (roundBodyR r) := by
  rw [roundBodyR_eq_seqAll]
  apply covered_seqAll
  intro c hc
  simp only [roundStmts, firstPart, List.mem_append, List.mem_map] at hc
  obtain (((((⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) | ⟨i, _, rfl⟩) | ⟨i, _, rfl⟩) | ⟨i, _, rfl⟩)
    | ⟨i, _, rfl⟩) := hc
  exacts [covered_cStmt i, covered_dStmt i, covered_pStmt i, covered_bStmt i,
    covered_hStmt i, covered_aBackStmt r i]

/-- The `N`-round body plus the output copy is covered. -/
theorem covered_fullBody (N : Nat) : IsCovered (fullBody N) := by
  unfold fullBody
  apply covered_seqAll
  intro c hc
  simp only [List.mem_append, List.mem_map] at hc
  obtain (⟨r, _, rfl⟩ | ⟨i, _, rfl⟩) := hc
  · exact covered_roundBodyR r
  · exact covered_oCopyStmt i

/-- On the straight-line `RSeq`/`RScalarSetExpr` body, the control front and the
    straight-line front coincide: the control arms `RFor`/`RIfNz`/`RWhileNz` do
    not occur, so `translateDialectControl` delegates to `translateDialectFull`. -/
theorem tdc_eq_tdf_fullBody :
    translateDialectControl srcVM (fullBody 24)
      = translateDialectFull srcVM (fullBody 24) :=
  translateDialectControl_eq_full_of_covered srcVM (covered_fullBody 24)

/-- **The 24-round front translates, and its emitted prefix is pure-arith.** -/
theorem front24_spec : ∃ c, frontFull 24 = some c ∧ PureLower c := by
  obtain ⟨σF, hST, hSL⟩ : ∃ σF, shapeTranslate srcShape (fullBody 24) = some σF ∧
      shapeLookup σF (oN 24) = some (.sword 64) := by
    have h := shapeRun24_ok
    cases hc : shapeTranslate srcShape (fullBody 24) with
    | none => rw [hc] at h; simp at h
    | some σF => exact ⟨σF, rfl, by rw [hc] at h; simpa using h⟩
  obtain ⟨o, htf, hago, hcgo⟩ := shapeTranslate_sim (fullBody 24) hST srcVM agrees_srcVM
  obtain ⟨v, hvlk⟩ := lookup_sword_of_agrees hago hSL
  obtain ⟨c, hc, hpl⟩ := hcgo (Com.ret (toVIRVar v)) trivial
  exact ⟨c, by simp only [frontFull, tdc_eq_tdf_fullBody, htf, hvlk, hc], hpl⟩

/-- **The 24-round front-composed Keccak `Com` exists** — `isSome` discharged
    compositionally, with no monolithic `native_decide` over the lowered `Com`. -/
theorem front24_isSome : (frontFull 24).isSome := by
  obtain ⟨c, hfc, _⟩ := front24_spec; rw [hfc]; rfl

/-- **The 24-round front lowers to jasmin end-to-end.** The `loweredFull 24`
    `isSome` is proved by structural composition of `lowerSExpr_sim` /
    `shapeTranslate_sim` / backend totality, gated on the one cheap alist
    `native_decide` (`shapeRun24_ok`). -/
theorem lowered24_isSome : (loweredFull 24).isSome := by
  obtain ⟨c, hfc, hpl⟩ := front24_spec
  simp only [loweredFull, hfc, Option.bind_some]
  exact cryptoDialectToJasminCom_isSome_of_pureLower c hpl

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakF1600FrontComposeProbe
