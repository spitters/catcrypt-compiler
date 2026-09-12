/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpTotal
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed

/-!
# Termination of the frame-relative secp256k1 doubling body

`Secp256k1PointOpFrontFramed.jacDblBodyFramed` re-tiles the `dbl-2009-l` doubling
body so every field element lives in a slot of a single memref frame `F`. Each
brick binds the reduction constants, loads its two operands from their frame
slots, runs one of the shared `feMulHalves` / `feAddHalves` / `feSubHalves` brick
bodies, and stores the eight result half-limbs back to the output frame slot.

The dynamic-index array arms `semScalar` uses for the frame load and store never
decline: `RArrLoad` binds its destination at 64-bit word type on every shape, and
`RArrStore` rebinds the frame pointer on every shape. So the only command that can
decline is a scalar assignment whose `SExpr` reads an unbound word slot, and each
brick binds every word it reads locally (the constants and the operand half-limbs
it loads from the frame). Every brick therefore runs from any environment, and the
whole body is the flattening of those bricks.

## Main results

* `arrLoad1_runs`, `runsFrom_arrLoadRange` — the frame-load arm runs on any
  environment, binding its destination at 64-bit word type.
* `idxCells_runs`, `constInit_runs` — the per-brick index and reduction-constant
  blocks run and bind their names.
* `loadField_runs` — the frame load binds a field element's eight half-limb slots.
* `storeFlat_runs` — the frame store runs from an environment binding the eight
  source half-limb slots, and leaves those slots bound.
* `emitFOpFramed_runs` — one frame-relative brick runs from any environment.
* `jacDblBodyFramed_runs` — the whole frame-relative doubling body runs from any
  environment to a defined exit environment.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedValue

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront (seqAll sv mask32 cc0 cc1 pl32)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (feH feMulHalves feAddHalves feSubHalves FOp plNames constInit loadField jacDblSchedule)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
  (HeadOk notTmp_of_len headOk_op mask32_lt lt64_32 lt64_zero
   notTmp_ZZ notTmp_CC0 notTmp_CC1 namesClean_plNames)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote
  (semScalar_seqAll_cons semScalar_seqAll_append)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpTotal
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpWholeBody (fopOut)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeAddSubBrick
  (hd hdAppend neOfHd sib2Ne subNe hd_feHN)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip (semScalar_setExpr_run)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpPrologue (notTmp_ix)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed
  (emitFOpFramed idxCells storeFieldTo brickFn slotOfDbl dblNames frameCells
   jacDblBodyFramed)

/-! ## 1. The frame-load arm runs -/

/-- **One frame load binds its destination at 64-bit word type on any shape.**
    The dynamic-index `RArrLoad` returns a word slot whether or not the source is
    a memref and the index a word. -/
theorem arrLoad1_runs (B : String → Prop) (v : String) (src : Located) (idxVar : String)
    (hnt : ¬ isTmpName v) :
    RunsFrom B (fun y => y = v) [LowCT.RArrLoad ⟨v, .TU64⟩ src idxVar] := by
  intro env _
  have hstep : ∃ w : BitVec 64,
      semScalar (LowCT.RArrLoad ⟨v, .TU64⟩ src idxVar) env
        = some (env.upd v (t := .sword 64) w) := by
    simp only [semScalar]
    split <;> exact ⟨_, rfl⟩
  obtain ⟨w, hw⟩ := hstep
  refine ⟨env.upd v (t := .sword 64) w, ?_, ?_, ?_⟩
  · show semScalar (seqAll [LowCT.RArrLoad ⟨v, .TU64⟩ src idxVar]) env = _
    rw [show seqAll [LowCT.RArrLoad ⟨v, .TU64⟩ src idxVar]
          = LowCT.RArrLoad ⟨v, .TU64⟩ src idxVar from rfl]
    exact hw
  · rintro x ⟨hxt, vv, hvv⟩
    by_cases hxv : x = v
    · subst hxv; exact ⟨hxt, w, by simp [SEnvScalar.upd]⟩
    · exact ⟨hxt, vv, by rw [SEnvScalar.upd, if_neg hxv]; exact hvv⟩
  · rintro x rfl
    exact ⟨hnt, w, by simp [SEnvScalar.upd]⟩

/-- **A block extended by a `List.range`-indexed family of frame loads.** Each
    trip appends a `RArrLoad` binding `nm i` at 64-bit word type. -/
theorem runsFrom_arrLoadRange {B W : String → Prop} {l : List LowCT}
    (nm : Nat → String) (src : Nat → Located) (idxV : Nat → String)
    (h : RunsFrom B W l) :
    ∀ n : Nat, (∀ i, i < n → ¬ isTmpName (nm i)) →
      RunsFrom B (fun y => W y ∨ ∃ i, i < n ∧ y = nm i)
        (l ++ (List.range n).map (fun i => LowCT.RArrLoad ⟨nm i, .TU64⟩ (src i) (idxV i))) := by
  intro n
  induction n with
  | zero =>
      intro _
      have hl : l ++ (List.range 0).map
          (fun i => LowCT.RArrLoad ⟨nm i, .TU64⟩ (src i) (idxV i)) = l := by simp
      rw [hl]
      refine runsFrom_mono h (fun _ hx => hx) (fun x hx => ?_)
      rcases hx with hx | ⟨i, hi, -⟩
      · exact hx
      · exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      intro hnt
      have hprev := ih (fun i hi => hnt i (by omega))
      have hs := runsFrom_append hprev
        (arrLoad1_runs (fun y => W y ∨ ∃ i, i < n ∧ y = nm i) (nm n) (src n) (idxV n)
          (hnt n (by omega)))
        (fun _ hx => Or.inr hx)
      have hl : l ++ (List.range (n + 1)).map
            (fun i => LowCT.RArrLoad ⟨nm i, .TU64⟩ (src i) (idxV i))
          = (l ++ (List.range n).map
              (fun i => LowCT.RArrLoad ⟨nm i, .TU64⟩ (src i) (idxV i)))
            ++ [LowCT.RArrLoad ⟨nm n, .TU64⟩ (src n) (idxV n)] := by
        rw [List.range_succ, List.map_append, List.append_assoc]; simp
      rw [hl]
      refine runsFrom_mono hs (fun _ hx => hx) (fun x hx => ?_)
      rcases hx with hx | ⟨i, hi, rfl⟩
      · exact Or.inl (Or.inl hx)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact Or.inl (Or.inr ⟨i, hlt, rfl⟩)
        · exact Or.inr rfl

/-! ## 2. The per-brick blocks run -/

/-- **A block extended by a `List.range`-indexed family of scalar-assignment
    pairs**, each reading only names the block already binds. -/
theorem runsFrom_flatMapRange2 {B W : String → Prop} {l : List LowCT}
    (n1 n2 : Nat → String) (e1 e2 : Nat → SExpr) (h : RunsFrom B W l) (n : Nat)
    (hnt1 : ∀ i, i < n → ¬ isTmpName (n1 i)) (hnt2 : ∀ i, i < n → ¬ isTmpName (n2 i))
    (hrd1 : ∀ i, i < n → ReadsFrom W (e1 i)) (hrd2 : ∀ i, i < n → ReadsFrom W (e2 i)) :
    RunsFrom B (fun y => W y ∨ ∃ i, i < n ∧ (y = n1 i ∨ y = n2 i))
      (l ++ (List.range n).flatMap
        (fun i => [LowCT.RScalarSetExpr (n1 i) (e1 i), LowCT.RScalarSetExpr (n2 i) (e2 i)])) := by
  induction n with
  | zero =>
      have hl : l ++ (List.range 0).flatMap
          (fun i => [LowCT.RScalarSetExpr (n1 i) (e1 i), LowCT.RScalarSetExpr (n2 i) (e2 i)])
          = l := by simp
      rw [hl]
      refine runsFrom_mono h (fun _ hx => hx) (fun x hx => ?_)
      rcases hx with hx | ⟨i, hi, -⟩
      · exact hx
      · exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      have hprev := ih (fun i hi => hnt1 i (by omega)) (fun i hi => hnt2 i (by omega))
        (fun i hi => hrd1 i (by omega)) (fun i hi => hrd2 i (by omega))
      have hs := runsFrom_snoc2 hprev (hnt1 n (by omega)) (hnt2 n (by omega))
        (readsFrom_mono (hrd1 n (by omega)) (fun _ hx => Or.inl hx))
        (readsFrom_mono (hrd2 n (by omega)) (fun _ hx => Or.inl (Or.inl hx)))
      have hl : l ++ (List.range (n + 1)).flatMap
            (fun i => [LowCT.RScalarSetExpr (n1 i) (e1 i), LowCT.RScalarSetExpr (n2 i) (e2 i)])
          = (l ++ (List.range n).flatMap
              (fun i => [LowCT.RScalarSetExpr (n1 i) (e1 i), LowCT.RScalarSetExpr (n2 i) (e2 i)]))
            ++ [LowCT.RScalarSetExpr (n1 n) (e1 n), LowCT.RScalarSetExpr (n2 n) (e2 n)] := by
        rw [List.range_succ, List.flatMap_append, List.append_assoc]; simp
      rw [hl]
      refine runsFrom_mono hs (fun _ hx => hx) (fun x hx => ?_)
      rcases hx with hx | ⟨i, hi, hxi⟩
      · exact Or.inl (Or.inl (Or.inl hx))
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact Or.inl (Or.inl (Or.inr ⟨i, hlt, hxi⟩))
        · rcases hxi with rfl | rfl
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr rfl

/-- **The frame load binds a field element's eight half-limb slots.** The four
    dynamic-index reads bind `{fe}u0..3` at word type on any frame shape, and the
    eight splits then bind `{fe}h0..7`. -/
theorem loadField_runs {B : String → Prop} (fw : Nat) (arr : String) (o : Nat)
    (fe : String) (hfe : HeadOk fe) :
    RunsFrom B (fun y => B y ∨ ∃ k, k < 8 ∧ y = s!"{fe}h{k}")
      (loadField fw arr o fe) := by
  have hntu : ∀ j, j < 4 → ¬ isTmpName s!"{fe}u{j}" :=
    fun j _ => HeadOk.notTmp (HeadOk.append (HeadOk.append hfe _) _)
  have harr := runsFrom_arrLoadRange (B := B) (W := B) (l := [])
    (fun j => s!"{fe}u{j}") (fun _ => (⟨arr, .TBytes fw⟩ : Located))
    (fun j => s!"ix{o + j}") (runsFrom_nil B) 4 hntu
  have hfm := runsFrom_flatMapRange2 (n1 := fun j => s!"{fe}h{2 * j}")
    (n2 := fun j => s!"{fe}h{2 * j + 1}")
    (e1 := fun j => .SAnd (sv s!"{fe}u{j}") (.SLit mask32))
    (e2 := fun j => .SShr (sv s!"{fe}u{j}") (.SLit 32))
    harr 4
    (fun j _ => HeadOk.notTmp (HeadOk.append (HeadOk.append hfe _) _))
    (fun j _ => HeadOk.notTmp (HeadOk.append (HeadOk.append hfe _) _))
    (fun j hj => readsFrom_and
      (readsFrom_var (hntu j hj) (Or.inr ⟨j, hj, rfl⟩)) (readsFrom_lit mask32_lt))
    (fun j hj => readsFrom_shr
      (readsFrom_var (hntu j hj) (Or.inr ⟨j, hj, rfl⟩)) (readsFrom_lit (by norm_num)))
  rw [show loadField fw arr o fe
        = ([] ++ (List.range 4).map (fun j =>
            (LowCT.RArrLoad ⟨s!"{fe}u{j}", .TU64⟩ (⟨arr, .TBytes fw⟩ : Located) s!"ix{o + j}")))
          ++ (List.range 4).flatMap (fun j =>
            [LowCT.RScalarSetExpr s!"{fe}h{2 * j}" (.SAnd (sv s!"{fe}u{j}") (.SLit mask32)),
             LowCT.RScalarSetExpr s!"{fe}h{2 * j + 1}" (.SShr (sv s!"{fe}u{j}") (.SLit 32))])
        from rfl]
  refine runsFrom_mono hfm (fun _ hx => hx) (fun x hx => ?_)
  rcases hx with hB | ⟨k, hk, rfl⟩
  · exact Or.inl (Or.inl hB)
  · refine Or.inr ?_
    interval_cases k
    · exact ⟨0, by omega, Or.inl rfl⟩
    · exact ⟨0, by omega, Or.inr rfl⟩
    · exact ⟨1, by omega, Or.inl rfl⟩
    · exact ⟨1, by omega, Or.inr rfl⟩
    · exact ⟨2, by omega, Or.inl rfl⟩
    · exact ⟨2, by omega, Or.inr rfl⟩
    · exact ⟨3, by omega, Or.inl rfl⟩
    · exact ⟨3, by omega, Or.inr rfl⟩

/-- **The per-brick reduction constants block runs and binds its names.** -/
theorem constInit_runs (B : String → Prop) :
    RunsFrom B (fun y => B y ∨ y = "ZZ" ∨ y = "CC0" ∨ y = "CC1" ∨ ∃ i, i < 8 ∧ y = s!"PL{i}")
      constInit := by
  have h3 := runsFrom_snoc3 (runsFrom_nil B) notTmp_ZZ notTmp_CC0 notTmp_CC1
    (@readsFrom_lit _ 0 (by norm_num)) (@readsFrom_lit _ cc0 (by norm_num [cc0]))
    (@readsFrom_lit _ cc1 (by norm_num [cc1]))
  have hmap := runsFrom_mapRange (fun i => s!"PL{i}")
    (fun i => (.SLit (pl32.getD i 0) : SExpr)) h3 8
    (fun i _ => HeadOk.notTmp (HeadOk.append (⟨'P', ['L'], rfl, by decide⟩ : HeadOk "PL") _))
    (fun i hi => @readsFrom_lit _ (pl32.getD i 0) (by interval_cases i <;> decide))
  refine runsFrom_mono hmap (fun _ hx => hx) (fun x hx => ?_)
  rcases hx with hB | rfl | rfl | rfl | ⟨i, hi, rfl⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inl hB)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr rfl)))
  · exact Or.inl (Or.inl (Or.inr rfl))
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr ⟨i, hi, rfl⟩

/-- **A single literal scalar assignment runs from any environment.** The `SLit`
    lowering always makes progress, so no bound on the literal is needed. -/
theorem runsFrom_litSetExpr (B : String → Prop) (x : String) (n : Nat) (hnt : ¬ isTmpName x) :
    RunsFrom B (fun y => y = x) [LowCT.RScalarSetExpr x (SExpr.SLit n)] := by
  intro env hB
  have hlow : (semLowerSExpr env 0 (SExpr.SLit n)).isSome := by
    simp only [semLowerSExpr, Option.isSome_some]
  obtain ⟨env', hsem, hval, hfr⟩ := semScalar_setExpr_run (y := x) hlow
  refine ⟨env', hsem, ?_, ?_⟩
  · rintro y ⟨hyt, v, hv⟩
    by_cases hyx : y = x
    · subst hyx; exact ⟨hyt, _, hval⟩
    · exact ⟨hyt, v, by rw [hfr y hyt hyx]; exact hv⟩
  · rintro y rfl
    exact ⟨hnt, _, hval⟩

/-- **The per-brick index block runs and preserves every bound name.** The
    cell-index assignments are literals, so the block runs from any environment;
    its exit set is the entry set. -/
theorem idxCells_runs (B : String → Prop) (cells : List Nat) : RunsFrom B B (idxCells cells) := by
  induction cells with
  | nil => exact runsFrom_nil B
  | cons c cs ih =>
      rw [show idxCells (c :: cs)
            = [LowCT.RScalarSetExpr s!"ix{c}" (SExpr.SLit c)] ++ idxCells cs from rfl]
      exact runsFrom_mono
        (runsFrom_append (runsFrom_litSetExpr B s!"ix{c}" c (notTmp_ix c)) ih
          (fun x hx => Or.inl hx))
        (fun _ h => h) (fun x hx => Or.inr hx)

/-- **The dynamic-index frame store runs on any shape.** It rebinds the frame
    pointer and leaves every other slot alone. -/
theorem arrStore_runs (arr' src : Located) (idxV : String) (env : SEnvScalar) :
    ∃ env', semScalar (LowCT.RArrStore arr' idxV src) env = some env'
      ∧ ∀ s, s ≠ arr'.locVar → env' s = env s := by
  simp only [semScalar]
  split <;>
    first
      | exact ⟨_, rfl, fun s hs => by simp only [SEnvScalar.upd, if_neg hs]⟩
      | (split <;> exact ⟨_, rfl, fun s hs => by simp only [SEnvScalar.upd, if_neg hs]⟩)

/-- **The frame store runs from an environment binding the source half-limbs.**
    Each trip recombines two half-limbs into a `u64` and stores it; the store
    rebinds only the frame pointer, so the half-limb slots survive every trip. -/
theorem storeFlat_runs (fw : Nat) (arr : String) (o : Nat) (fe : String) (hfe : HeadOk fe)
    (hFarr : ∀ k, k < 8 → s!"{fe}h{k}" ≠ arr) :
    ∀ n, n ≤ 4 → ∀ env : SEnvScalar,
      (∀ k, k < 8 → ∃ v : BitVec 64, env s!"{fe}h{k}" = some ⟨.sword 64, v⟩) →
      ∃ env', semScalar (seqAll ((List.range n).flatMap (fun j =>
          [LowCT.RScalarSetExpr s!"{fe}o{j}"
             (.SAdd (sv s!"{fe}h{2*j}") (.SShl (sv s!"{fe}h{2*j+1}") (.SLit 32))),
           LowCT.RArrStore (⟨arr, .TBytes fw⟩ : Located) s!"ix{o + j}"
             (⟨s!"{fe}o{j}", .TU64⟩ : Located)]))) env = some env'
        ∧ (∀ k, k < 8 → ∃ v : BitVec 64, env' s!"{fe}h{k}" = some ⟨.sword 64, v⟩) := by
  intro n
  induction n with
  | zero => intro _ env hb; exact ⟨env, rfl, hb⟩
  | succ n ih =>
      intro hle env hb
      obtain ⟨env1, hs1, hb1⟩ := ih (by omega) env hb
      have hn4 : n < 4 := by omega
      have h2n : 2 * n < 8 := by omega
      have h2n1 : 2 * n + 1 < 8 := by omega
      have hntH : ∀ m : Nat, ¬ isTmpName s!"{fe}h{m}" :=
        fun m => HeadOk.notTmp (HeadOk.append (HeadOk.append hfe _) _)
      have hrd : ReadsFrom (fun z => ∃ k, k < 8 ∧ z = s!"{fe}h{k}")
          (SExpr.SAdd (sv s!"{fe}h{2*n}") (.SShl (sv s!"{fe}h{2*n+1}") (.SLit 32))) :=
        readsFrom_add (readsFrom_var (hntH _) ⟨2*n, h2n, rfl⟩)
          (readsFrom_shr (readsFrom_var (hntH _) ⟨2*n+1, h2n1, rfl⟩) (readsFrom_lit (by norm_num)))
      have hlow : (semLowerSExpr env1 0
          (SExpr.SAdd (sv s!"{fe}h{2*n}") (.SShl (sv s!"{fe}h{2*n+1}") (.SLit 32)))).isSome := by
        obtain ⟨e2, nm, cnt, hh, -⟩ := semLowerSExpr_run _ env1 0 hrd.1
          (fun s hs => by
            obtain ⟨k, hk, rfl⟩ := hrd.2 s hs
            obtain ⟨v, hv⟩ := hb1 k hk
            simp only [envReadU64, hv, Option.isSome_some])
        rw [hh]; rfl
      obtain ⟨env2, hset, -, hsetfr⟩ := semScalar_setExpr_run
        (y := s!"{fe}o{n}") hlow
      obtain ⟨env', hstore, hstfr⟩ := arrStore_runs (⟨arr, .TBytes fw⟩ : Located)
        (⟨s!"{fe}o{n}", .TU64⟩ : Located) s!"ix{o + n}" env2
      have hstep : semScalar (seqAll ((List.range (n + 1)).flatMap (fun j =>
          [LowCT.RScalarSetExpr s!"{fe}o{j}"
             (.SAdd (sv s!"{fe}h{2*j}") (.SShl (sv s!"{fe}h{2*j+1}") (.SLit 32))),
           LowCT.RArrStore (⟨arr, .TBytes fw⟩ : Located) s!"ix{o + j}"
             (⟨s!"{fe}o{j}", .TU64⟩ : Located)]))) env = some env' := by
        rw [List.range_succ, List.flatMap_append, semScalar_seqAll_append, hs1, Option.bind_some]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rw [semScalar_seqAll_cons, hset, Option.bind_some,
          show seqAll [LowCT.RArrStore (⟨arr, .TBytes fw⟩ : Located) s!"ix{o + n}"
              (⟨s!"{fe}o{n}", .TU64⟩ : Located)]
            = LowCT.RArrStore (⟨arr, .TBytes fw⟩ : Located) s!"ix{o + n}"
              (⟨s!"{fe}o{n}", .TU64⟩ : Located) from rfl,
          hstore]
      refine ⟨env', hstep, fun k hk => ?_⟩
      obtain ⟨v, hv⟩ := hb1 k hk
      refine ⟨v, ?_⟩
      rw [hstfr s!"{fe}h{k}" (hFarr k hk),
        hsetfr s!"{fe}h{k}" (hntH k)
          (sib2Ne (q := fe) (t := "h") (u := "o") (ct := 'h') (cu := 'o')
            (rfl) (rfl) (by decide) (toString k) (toString n))]
      exact hv

/-! ## 3. One frame-relative brick runs -/

/-- The word set a brick's operand load leaves bound: the reduction constants and
    the two operands' eight half-limb slots. -/
def Bbody (pfx : String) : String → Prop := fun y =>
  ((y = "ZZ" ∨ y = "CC0" ∨ y = "CC1" ∨ ∃ i, i < 8 ∧ y = s!"PL{i}")
    ∨ ∃ k, k < 8 ∧ y = s!"{pfx ++ "A"}h{k}") ∨ ∃ k, k < 8 ∧ y = s!"{pfx ++ "B"}h{k}"

/-- **The constant and operand-load prefix of a brick runs**, binding the
    reduction constants and both operands' half-limb slots. -/
theorem pre_runs (fw : Nat) (frame pfx : String) (oa ob : Nat) (cells : List Nat)
    (hpfx : HeadOk pfx) :
    RunsFrom (fun _ => False) (Bbody pfx)
      (idxCells cells ++ constInit
        ++ loadField fw frame oa (pfx ++ "A") ++ loadField fw frame ob (pfx ++ "B")) := by
  have h1 := runsFrom_trans (idxCells_runs (fun _ => False) cells)
    (constInit_runs (fun _ => False))
  have h2 := runsFrom_trans h1 (loadField_runs fw frame oa (pfx ++ "A") (HeadOk.append hpfx "A"))
  have h3 := runsFrom_trans h2 (loadField_runs fw frame ob (pfx ++ "B") (HeadOk.append hpfx "B"))
  refine runsFrom_mono h3 (fun _ h => h) (fun x hx => ?_)
  simp only [Bbody] at hx
  rcases hx with (hc | ha) | hb
  · exact Or.inl (Or.inl (Or.inr hc))
  · exact Or.inl (Or.inr ha)
  · exact Or.inr hb

theorem bbody_zz (pfx : String) : Bbody pfx "ZZ" := Or.inl (Or.inl (Or.inl rfl))
theorem bbody_cc0 (pfx : String) : Bbody pfx "CC0" := Or.inl (Or.inl (Or.inr (Or.inl rfl)))
theorem bbody_cc1 (pfx : String) : Bbody pfx "CC1" :=
  Or.inl (Or.inl (Or.inr (Or.inr (Or.inl rfl))))

theorem bbody_pl (pfx : String) : AllIn (Bbody pfx) plNames := by
  intro k hk
  have hk8 : k < 8 := by simpa [plNames] using hk
  rw [show plNames[k]! = s!"PL{k}" from by rw [plNames]; exact map_range_getBang 8 _ k hk8]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr ⟨k, hk8, rfl⟩))))

theorem bbody_hA (pfx : String) : AllIn (Bbody pfx) (feH (pfx ++ "A")) := by
  intro k hk
  have hk8 : k < 8 := by simpa [feH] using hk
  rw [show (feH (pfx ++ "A"))[k]! = s!"{pfx ++ "A"}h{k}" from by
    rw [feH]; exact map_range_getBang 8 _ k hk8]
  exact Or.inl (Or.inr ⟨k, hk8, rfl⟩)

theorem bbody_hB (pfx : String) : AllIn (Bbody pfx) (feH (pfx ++ "B")) := by
  intro k hk
  have hk8 : k < 8 := by simpa [feH] using hk
  rw [show (feH (pfx ++ "B"))[k]! = s!"{pfx ++ "B"}h{k}" from by
    rw [feH]; exact map_range_getBang 8 _ k hk8]
  exact Or.inr ⟨k, hk8, rfl⟩

theorem bbody_src (pfx : String) (hpfx : HeadOk pfx) : SrcSet (Bbody pfx) := by
  intro y hy
  simp only [Bbody] at hy
  rcases hy with (((rfl | rfl | rfl | ⟨i, hi, rfl⟩) | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩)
  · exact notTmp_ZZ
  · exact notTmp_CC0
  · exact notTmp_CC1
  · exact HeadOk.notTmp (HeadOk.append (⟨'P', ['L'], rfl, by decide⟩ : HeadOk "PL") _)
  · exact HeadOk.notTmp (HeadOk.append (HeadOk.append (HeadOk.append hpfx "A") "h") _)
  · exact HeadOk.notTmp (HeadOk.append (HeadOk.append (HeadOk.append hpfx "B") "h") _)

/-- The two spellings of the output field element's half-limb slot agree: the
    copy block writes `s!"{pfx}Oh{k}"`, the frame store reads `s!"{pfx ++ "O"}h{k}"`. -/
theorem oh_bridge (pfx : String) (k : Nat) : s!"{pfx}Oh{k}" = s!"{pfx ++ "O"}h{k}" := by
  simp only [show ∀ s : String, toString s = s from fun _ => rfl,
    show ("Oh" : String) = "O" ++ "h" from rfl, String.append_assoc]

/-- The copy block's `mapRange` exit binds the eight output half-limb slots, in
    the spelling the frame store reads them. -/
theorem copies_bound_store {pfx : String} {W : String → Prop} {env2 : SEnvScalar}
    (hbnd : ∀ x, (fun y => W y ∨ ∃ k, k < 8 ∧ y = s!"{pfx}Oh{k}") x → WordBound env2 x) :
    ∀ k, k < 8 → ∃ v : BitVec 64, env2 s!"{pfx ++ "O"}h{k}" = some ⟨.sword 64, v⟩ := by
  intro k hk
  obtain ⟨-, v, hv⟩ := hbnd s!"{pfx}Oh{k}" (Or.inr ⟨k, hk, rfl⟩)
  exact ⟨v, by rw [← oh_bridge pfx k]; exact hv⟩

/-- The output slot names of a `fop{idx}` brick are distinct from the frame
    pointer `F`. -/
theorem oh_ne_F (idx : Nat) : ∀ k, k < 8 → s!"{s!"fop{idx}" ++ "O"}h{k}" ≠ "F" := by
  intro k _
  exact neOfHd (hdAppend (hdAppend (hdAppend (hdAppend rfl)))) (rfl : hd "F" = some 'F')
    (by decide)

/-- **The common assembly of a frame-relative brick.** Given the brick body and
    its result names (with the operand-load precondition discharged by the
    reduction constants and both frame loads), the constant/load prefix, the
    brick, the copy block and the frame store compose into a run. -/
theorem framed_assemble (fw idx : Nat) (slotOf : String → Nat) (a b o : String)
    (env : SEnvScalar) (pfx : String) (hpfxeq : pfx = s!"fop{idx}") (hpfx : HeadOk pfx)
    (bc : List LowCT) (br : List String) (hbr8 : br.length = 8)
    (hbrick : ∃ W, SrcSet W ∧ (∀ x, Bbody pfx x → W x) ∧ RunsFrom (Bbody pfx) W bc ∧ AllIn W br) :
    ∃ env', semScalar (seqAll (
      idxCells ((List.range 4).map (4 * slotOf a + ·) ++ (List.range 4).map (4 * slotOf b + ·)
          ++ (List.range 4).map (4 * slotOf o + ·))
        ++ constInit ++ loadField fw "F" (4 * slotOf a) (pfx ++ "A")
        ++ loadField fw "F" (4 * slotOf b) (pfx ++ "B")
        ++ bc
        ++ (List.range 8).map (fun k => LowCT.RScalarSetExpr s!"{pfx}Oh{k}" (sv (br[k]!)))
        ++ storeFieldTo fw "F" (4 * slotOf o) (pfx ++ "O"))) env = some env' := by
  obtain ⟨W, hWs, hWb, hRun, hAllBr⟩ := hbrick
  have hpre := pre_runs fw "F" pfx (4 * slotOf a) (4 * slotOf b)
    ((List.range 4).map (4 * slotOf a + ·) ++ (List.range 4).map (4 * slotOf b + ·)
      ++ (List.range 4).map (4 * slotOf o + ·)) hpfx
  have hbrickT := runsFrom_trans hpre hRun
  have hcopies := runsFrom_mapRange (fun k => s!"{pfx}Oh{k}") (fun k => sv (br[k]!)) hbrickT 8
    (fun k _ => HeadOk.notTmp (HeadOk.append (HeadOk.append hpfx "Oh") _))
    (fun k hk => readsFrom_var (hWs _ (hAllBr k (by rw [hbr8]; exact hk)))
      (hAllBr k (by rw [hbr8]; exact hk)))
  obtain ⟨env2, hbig, -, hbnd⟩ := hcopies env (fun _ h => h.elim)
  obtain ⟨env', hstore, -⟩ := storeFlat_runs fw "F" (4 * slotOf o) (pfx ++ "O")
    (HeadOk.append hpfx "O") (by rw [hpfxeq]; exact oh_ne_F idx) 4 (le_refl 4) env2
    (copies_bound_store hbnd)
  refine ⟨env', ?_⟩
  rw [semScalar_seqAll_append, hbig, Option.bind_some]
  exact hstore

/-- **One frame-relative doubling brick runs from any environment.** The array
    load and store never decline, and the brick binds every word it reads (the
    reduction constants and the operand half-limbs it loads from the frame). -/
theorem emitFOpFramed_runs (fw : Nat) (slotOf : String → Nat) (idx : Nat) (op : FOp)
    (env : SEnvScalar) :
    ∃ env', semScalar (seqAll (emitFOpFramed fw "F" slotOf idx op)) env = some env' := by
  have hpfx : HeadOk s!"fop{idx}" :=
    HeadOk.append (⟨'f', ['o', 'p'], rfl, by decide⟩ : HeadOk "fop") _
  cases op with
  | mul o a b =>
      refine framed_assemble fw idx slotOf a b o env s!"fop{idx}" rfl hpfx
        (feMulHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A")) (feH (s!"fop{idx}" ++ "B"))).1
        (feMulHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A")) (feH (s!"fop{idx}" ++ "B"))).2
        (feMulHalves_len _ _ _) ?_
      exact feMulHalves_runs (B := Bbody s!"fop{idx}") (s!"fop{idx}" ++ "C")
        (feH (s!"fop{idx}" ++ "A")) (feH (s!"fop{idx}" ++ "B")) (HeadOk.append hpfx "C")
        (bbody_src _ hpfx) (bbody_zz _) (bbody_cc0 _) (bbody_cc1 _)
        (bbody_pl _) (bbody_hA _) (bbody_hB _) (by simp [feH]) (by simp [feH])
  | add o a b =>
      refine framed_assemble fw idx slotOf a b o env s!"fop{idx}" rfl hpfx
        (feAddHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A")) (feH (s!"fop{idx}" ++ "B"))).1
        (feAddHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A")) (feH (s!"fop{idx}" ++ "B"))).2
        (feAddHalves_len _ _ _) ?_
      exact feAddHalves_runs (B := Bbody s!"fop{idx}") (s!"fop{idx}" ++ "C")
        (feH (s!"fop{idx}" ++ "A")) (feH (s!"fop{idx}" ++ "B")) (HeadOk.append hpfx "C")
        (bbody_src _ hpfx) (bbody_zz _) (bbody_pl _) (bbody_hA _) (bbody_hB _)
        (by simp [feH]) (by simp [feH])
  | sub o a b =>
      refine framed_assemble fw idx slotOf a b o env s!"fop{idx}" rfl hpfx
        (feSubHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A")) (feH (s!"fop{idx}" ++ "B"))).1
        (feSubHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A")) (feH (s!"fop{idx}" ++ "B"))).2
        (feSubHalves_len (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A")) (feH (s!"fop{idx}" ++ "B"))
          (by simp [feH])) ?_
      exact feSubHalves_runs (B := Bbody s!"fop{idx}") (s!"fop{idx}" ++ "C")
        (feH (s!"fop{idx}" ++ "A")) (feH (s!"fop{idx}" ++ "B")) (HeadOk.append hpfx "C")
        (bbody_src _ hpfx) (bbody_zz _) (bbody_pl _) (bbody_hA _) (bbody_hB _)

/-! ## 4. The whole frame-relative doubling body runs -/

/-- **A `mapIdx`-indexed flattening of blocks that each run from any environment
    runs from any environment.** -/
theorem mapIdxFlatten_runs :
    ∀ (ops : List FOp) (g : Nat → FOp → List LowCT),
      (∀ i op env, ∃ env', semScalar (seqAll (g i op)) env = some env') →
      ∀ env, ∃ env', semScalar (seqAll ((ops.mapIdx g).flatten)) env = some env' := by
  intro ops
  induction ops with
  | nil => intro g _ env; exact ⟨env, rfl⟩
  | cons op rest ih =>
      intro g hg env
      rw [List.mapIdx_cons, List.flatten_cons, semScalar_seqAll_append]
      obtain ⟨e1, he1⟩ := hg 0 op env
      rw [he1, Option.bind_some]
      exact ih (fun i => g (i + 1)) (fun i op' env' => hg (i + 1) op' env') e1

/-- **The frame-relative `jacDbl` body runs to completion from any environment.**
    Each of the nineteen frame-relative bricks binds every word it reads and the
    frame load and store never decline, so the whole body's waist semantics is
    defined on every input environment. -/
theorem jacDblBodyFramed_runs (env : SEnvScalar) :
    ∃ env', semScalar jacDblBodyFramed env = some env' :=
  mapIdxFlatten_runs jacDblSchedule
    (fun i op => emitFOpFramed (8 * frameCells) "F" slotOfDbl i op)
    (fun i op e => emitFOpFramed_runs (8 * frameCells) slotOfDbl i op e) env

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedValue
