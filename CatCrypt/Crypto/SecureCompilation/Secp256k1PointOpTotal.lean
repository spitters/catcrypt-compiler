/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpAddVertical

/-!
# Termination of the front-compiled secp256k1 point-op bodies

`Secp256k1PointOpWholeBody.jacDblBody_cells` reads the output frame off a
*successful* run of `Secp256k1PointOpFront.jacDblBody`. This module supplies the
run: every command the body emits is a scalar assignment whose `SExpr` reads only
names already bound at 64-bit word type, so the scalar waist semantics
`TranslateDialectScalar.semScalar` never declines.

## The block-run predicate

`RunsFrom B W l` is the triple the development threads: from any environment
binding the name set `B`, the command list `l` runs to completion, the exit
environment still binds every source name the entry bound, and it binds `W`. It
composes over `++` with no side conditions, because `WordBound` carries the
non-temporary condition the frame clause of a scalar assignment needs.

The generator-level proofs mirror `Secp256k1PointOpFrontCovered`: each `Id`-monad
loop of `genMul` / `genAdd` / `genSub` is handled by a loop invariant over the
same named step functions, so no generated command list is reduced.

## Main results

* `binNode_run`, `semLowerSExpr_run` — the `SExpr` lowering makes progress when
  every variable it reads is bound at 64-bit word type.
* `WordBound`, `RunsFrom`, `runsFrom_nil`, `runsFrom_append`, `runsFrom_setExpr`,
  `runsFrom_snoc` — the block-run triple and its composition.
* `ReadsFrom` and its combinators — a `srcClean` expression whose reads lie in a
  name set.
* `forIn_list_inv_mem`, `forIn_range_inv_lt` — a loop invariant for an
  `Id`-monad `forIn` over `[:n]` with the trip index bounded.
* `genAdd_len`, `genSub_len`, `genAdd_runs`, `genSub_runs` — the two ripple
  builders: the length of their result-name lists, and the run of the commands
  they emit from a bound operand set.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpTotal

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms (tmpName)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelectAdequacy
  (srcClean_vars_not_tmp)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront
  (seqAll sv genMul genAdd genSub genFold mask32)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
  (HeadOk forIn_range_inv arrayToList_getBang mask32_lt lt64_32 lt64_zero
   AddS SubS MulI MulO genAddStep genAddRun genAdd_eq genSubStep genSubRun genSub_eq
   genMulInnerStep genMulOuterStep genMulRun genMul_eq NamesClean namesClean_plNames
   namesClean_feH notTmp_ZZ notTmp_CC0 notTmp_CC1 headOk_op headOk_of_headOkB FOpOkB
   jacDblSchedule_ok headOk_X headOk_Y headOk_Z jacAddSchedule_ok
   headOk_X1 headOk_Y1 headOk_Z1 headOk_X2 headOk_Y2 headOk_Z2)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpAddVertical
  (AddPrologueEntry jacAddPrologue jacAddPrologue_run jacAddPrologue_value jacAddBody_split
   jacAddSchedule_out jacAddSchedule_ix jacAddBody_cells idxConst2_run loadCoordA_run
   constVals_load slots_keep slots_trans hd_X1 hd_Y1 hd_Z1 hd_X2 hd_Y2 hd_Z2)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpBrickScope
  (jacAddSchedule_waist_scope)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpWholeBody
  (fopOut SlotsBound slotsBound_reads jacDblBody_split jacDblSchedule_out jacDblSchedule_ix
   jacDblPrologue_frame jacDblBody_cells)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (feMulHalves feAddHalves feSubHalves plNames feH emitFOp runSchedule FOp jacDblSchedule
   jacDblBody jacDblSpec pointCells jacAddSchedule jacAddBody jacAddSpec)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrameRoundTrip
  (semScalar_setExpr_run)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpPrologue
  (semScalar_append_run PrologueEntry ConstVals jacDblPrologue jacDblPrologue_run
   idxConst_run loadCoord_run constVals_load3 feHN_keep_load hd_X hd_Y hd_Z)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeAddSubBrick
  (feHN headOk_of_hd hd_feHN)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpBrickScope
  (jacDblSchedule_waist_scope)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpEpilogue (pointOpEpilogue_cells)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontDenote (semScalar_seqAll_append)

/-! ## 1. Progress of the `SExpr` lowering

`semLowerSExpr` declines exactly when a variable it reads is not bound at
`.sword 64`. The fresh-temp bookkeeping (`OnlyTmpBelow` / `ResultOK`) is what
makes the binary arms compose: the second operand's lowering allocates temps
above the first operand's result name, so the first result stays readable. -/

/-- One binary node of the lowering, on readable operand slots. -/
theorem binNode_run {env : SEnvScalar} {na nb : String} {cnt : Nat}
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (ha : (envReadU64 env na).isSome) (hb : (envReadU64 env nb).isSome) :
    ∃ (env' : SEnvScalar) (nm : String) (cnt' : Nat),
      binNode env na nb cnt f = some (env', nm, cnt') ∧ cnt' = cnt + 1
        ∧ OnlyTmpBelow env env' cnt ∧ ResultOK nm cnt' ∧ (envReadU64 env' nm).isSome := by
  obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp hb
  refine ⟨env.upd (tmpName cnt) (t := .sword 64) (f va vb), tmpName cnt, cnt + 1, ?_, rfl,
    onlyTmpBelow_upd (onlyTmpBelow_refl env cnt) (le_refl _),
    Or.inr ⟨cnt, Nat.lt_succ_self _, rfl⟩, ?_⟩
  · simp only [binNode, hva, hvb]
  · rw [envReadU64_upd_self]; rfl

/-- **The `SExpr` lowering makes progress on bound reads.** A `srcClean`
    expression whose variables are all bound at 64-bit word type lowers to a
    defined result, touching only fresh temporaries. -/
theorem semLowerSExpr_run :
    ∀ (e : SExpr) (env : SEnvScalar) (cnt : Nat), srcClean e →
      (∀ s ∈ sexprVars e, (envReadU64 env s).isSome) →
      ∃ (env₂ : SEnvScalar) (nm : String) (cnt' : Nat),
        semLowerSExpr env cnt e = some (env₂, nm, cnt') ∧ cnt ≤ cnt'
          ∧ OnlyTmpBelow env env₂ cnt ∧ ResultOK nm cnt'
          ∧ (envReadU64 env₂ nm).isSome := by
  intro e
  induction e with
  | SVar x =>
      intro env cnt hcl hb
      have hread := hb x (by simp [sexprVars])
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hread
      refine ⟨env, x, cnt, ?_, le_refl _, onlyTmpBelow_refl env cnt, Or.inl hcl, hread⟩
      simp only [semLowerSExpr, hv]
  | SLit n =>
      intro env cnt _ _
      refine ⟨env.upd (tmpName cnt) (t := .sword 64) (BitVec.ofNat 64 n), tmpName cnt,
        cnt + 1, rfl, Nat.le_succ _,
        onlyTmpBelow_upd (onlyTmpBelow_refl env cnt) (le_refl _),
        Or.inr ⟨cnt, Nat.lt_succ_self _, rfl⟩, ?_⟩
      rw [envReadU64_upd_self]; rfl
  | SAdd a b iha ihb | SSub a b iha ihb | SMul a b iha ihb | SAnd a b iha ihb
  | SXor a b iha ihb | SShl a b iha ihb | SShr a b iha ihb | SMulHiU a b iha ihb =>
      intro env cnt hcl hb
      obtain ⟨env1, na, c1, hA, hleA, hotbA, hrokA, hreadA⟩ :=
        iha env cnt hcl.1
          (fun s hs => hb s (by simp only [sexprVars, List.mem_append]; exact Or.inl hs))
      have hb1 : ∀ s ∈ sexprVars b, (envReadU64 env1 s).isSome := by
        intro s hs
        rw [readU64_stable hotbA (Or.inl (srcClean_vars_not_tmp b hcl.2 s hs))]
        exact hb s (by simp only [sexprVars, List.mem_append]; exact Or.inr hs)
      obtain ⟨env2, nb, c2, hB, hleB, hotbB, hrokB, hreadB⟩ := ihb env1 c1 hcl.2 hb1
      have hna2 : (envReadU64 env2 na).isSome := by
        rw [readU64_stable hotbB hrokA]; exact hreadA
      obtain ⟨env3, nm, c3, hbn, hc3, hotb3, hrok3, hread3⟩ :=
        binNode_run (cnt := c2) _ hna2 hreadB
      have hle3 : cnt ≤ c3 := by omega
      refine ⟨env3, nm, c3, ?_, hle3, ?_, hrok3, hread3⟩
      · simp only [semLowerSExpr, hA, hB]; exact hbn
      · exact onlyTmpBelow_trans (onlyTmpBelow_trans hotbA hotbB hleA) hotb3
          (le_trans hleA hleB)
  | SLt a b _ _ => intro _ _ hcl; exact hcl.elim
  | SAsr a b _ _ => intro _ _ hcl; exact hcl.elim
  | SMulS a b _ _ => intro _ _ hcl; exact hcl.elim
  | SMulHiS a b _ _ => intro _ _ hcl; exact hcl.elim
  | SLimb v i => intro _ _ hcl; exact hcl.elim

/-! ## 2. Word-bound names and the block-run triple -/

/-- A source name bound at 64-bit word type. -/
def WordBound (env : SEnvScalar) (x : String) : Prop :=
  ¬ isTmpName x ∧ ∃ v : BitVec 64, env x = some ⟨.sword 64, v⟩

theorem wordBound_read {env : SEnvScalar} {x : String} (h : WordBound env x) :
    (envReadU64 env x).isSome := by
  obtain ⟨-, v, hv⟩ := h
  simp only [envReadU64, hv, Option.isSome_some]

/-- A name set outside the front's reserved fresh-temporary namespace. -/
def SrcSet (B : String → Prop) : Prop := ∀ x, B x → ¬ isTmpName x

theorem srcSet_or {W : String → Prop} {x : String} (hW : SrcSet W) (hx : ¬ isTmpName x) :
    SrcSet (fun y => W y ∨ y = x) := by
  rintro y (h | rfl)
  · exact hW y h
  · exact hx

/-- **The block-run triple.** From every environment binding `B`, the command
    list runs to completion; the exit environment keeps every source name the
    entry bound and binds `W`. -/
def RunsFrom (B W : String → Prop) (l : List LowCT) : Prop :=
  ∀ env : SEnvScalar, (∀ x, B x → WordBound env x) →
    ∃ env', semScalar (seqAll l) env = some env'
      ∧ (∀ x, WordBound env x → WordBound env' x)
      ∧ (∀ x, W x → WordBound env' x)

theorem runsFrom_nil (B : String → Prop) : RunsFrom B B [] :=
  fun env hB => ⟨env, rfl, fun _ h => h, hB⟩

/-- Strengthening the entry set and weakening the exit set. -/
theorem runsFrom_mono {B B₂ W W₂ : String → Prop} {l : List LowCT}
    (h : RunsFrom B W l) (hB : ∀ x, B x → B₂ x) (hW : ∀ x, W₂ x → W x) :
    RunsFrom B₂ W₂ l := by
  intro env hB₂
  obtain ⟨env', hs, hfr, hw⟩ := h env (fun x hx => hB₂ x (hB x hx))
  exact ⟨env', hs, hfr, fun x hx => hw x (hW x hx)⟩

/-- The entry set is still bound at the exit. -/
theorem runsFrom_addPre {B W : String → Prop} {l : List LowCT} (h : RunsFrom B W l) :
    RunsFrom B (fun x => W x ∨ B x) l := by
  intro env hB
  obtain ⟨env', hs, hfr, hw⟩ := h env hB
  exact ⟨env', hs, hfr, fun x hx => hx.elim (hw x) (fun hb => hfr x (hB x hb))⟩

/-- **Two blocks in sequence.** The second block's entry set may draw on the
    first block's exit set. -/
theorem runsFrom_append {B W₁ B' W₂ : String → Prop} {l₁ l₂ : List LowCT}
    (h₁ : RunsFrom B W₁ l₁) (h₂ : RunsFrom B' W₂ l₂)
    (hsub : ∀ x, B' x → B x ∨ W₁ x) :
    RunsFrom B (fun x => W₁ x ∨ W₂ x) (l₁ ++ l₂) := by
  intro env hB
  obtain ⟨e1, hs1, hfr1, hw1⟩ := h₁ env hB
  obtain ⟨e2, hs2, hfr2, hw2⟩ :=
    h₂ e1 (fun x hx => (hsub x hx).elim (fun h => hfr1 x (hB x h)) (hw1 x))
  exact ⟨e2, semScalar_append_run hs1 hs2, fun x hx => hfr2 x (hfr1 x hx),
    fun x hx => hx.elim (fun h => hfr2 x (hw1 x h)) (hw2 x)⟩

/-! ## 3. Expressions read from a name set -/

/-- A `srcClean` expression all of whose `SVar` leaves lie in `R`. -/
def ReadsFrom (R : String → Prop) (e : SExpr) : Prop :=
  srcClean e ∧ ∀ s ∈ sexprVars e, R s

theorem readsFrom_mono {R R' : String → Prop} {e : SExpr} (h : ReadsFrom R e)
    (hr : ∀ x, R x → R' x) : ReadsFrom R' e :=
  ⟨h.1, fun s hs => hr s (h.2 s hs)⟩

theorem readsFrom_var {R : String → Prop} {x : String} (hnt : ¬ isTmpName x) (hx : R x) :
    ReadsFrom R (sv x) := by
  refine ⟨hnt, fun s hs => ?_⟩
  simp only [sv, sexprVars, List.mem_cons, List.not_mem_nil, or_false] at hs
  exact hs ▸ hx

theorem readsFrom_lit {R : String → Prop} {n : Nat} (hn : n < 2 ^ 64) :
    ReadsFrom R (SExpr.SLit n) := by
  refine ⟨hn, fun s hs => ?_⟩
  simp [sexprVars] at hs

theorem readsFrom_add {R : String → Prop} {a b : SExpr} (ha : ReadsFrom R a)
    (hb : ReadsFrom R b) : ReadsFrom R (SExpr.SAdd a b) :=
  ⟨⟨ha.1, hb.1⟩, fun s hs => by
    simp only [sexprVars, List.mem_append] at hs; exact hs.elim (ha.2 s) (hb.2 s)⟩

theorem readsFrom_sub {R : String → Prop} {a b : SExpr} (ha : ReadsFrom R a)
    (hb : ReadsFrom R b) : ReadsFrom R (SExpr.SSub a b) :=
  ⟨⟨ha.1, hb.1⟩, fun s hs => by
    simp only [sexprVars, List.mem_append] at hs; exact hs.elim (ha.2 s) (hb.2 s)⟩

theorem readsFrom_mul {R : String → Prop} {a b : SExpr} (ha : ReadsFrom R a)
    (hb : ReadsFrom R b) : ReadsFrom R (SExpr.SMul a b) :=
  ⟨⟨ha.1, hb.1⟩, fun s hs => by
    simp only [sexprVars, List.mem_append] at hs; exact hs.elim (ha.2 s) (hb.2 s)⟩

theorem readsFrom_and {R : String → Prop} {a b : SExpr} (ha : ReadsFrom R a)
    (hb : ReadsFrom R b) : ReadsFrom R (SExpr.SAnd a b) :=
  ⟨⟨ha.1, hb.1⟩, fun s hs => by
    simp only [sexprVars, List.mem_append] at hs; exact hs.elim (ha.2 s) (hb.2 s)⟩

theorem readsFrom_xor {R : String → Prop} {a b : SExpr} (ha : ReadsFrom R a)
    (hb : ReadsFrom R b) : ReadsFrom R (SExpr.SXor a b) :=
  ⟨⟨ha.1, hb.1⟩, fun s hs => by
    simp only [sexprVars, List.mem_append] at hs; exact hs.elim (ha.2 s) (hb.2 s)⟩

theorem readsFrom_shl {R : String → Prop} {a b : SExpr} (ha : ReadsFrom R a)
    (hb : ReadsFrom R b) : ReadsFrom R (SExpr.SShl a b) :=
  ⟨⟨ha.1, hb.1⟩, fun s hs => by
    simp only [sexprVars, List.mem_append] at hs; exact hs.elim (ha.2 s) (hb.2 s)⟩

theorem readsFrom_shr {R : String → Prop} {a b : SExpr} (ha : ReadsFrom R a)
    (hb : ReadsFrom R b) : ReadsFrom R (SExpr.SShr a b) :=
  ⟨⟨ha.1, hb.1⟩, fun s hs => by
    simp only [sexprVars, List.mem_append] at hs; exact hs.elim (ha.2 s) (hb.2 s)⟩

/-- **One scalar assignment.** -/
theorem runsFrom_setExpr {R : String → Prop} {x : String} {e : SExpr}
    (hnt : ¬ isTmpName x) (hrd : ReadsFrom R e) :
    RunsFrom R (fun y => y = x) [LowCT.RScalarSetExpr x e] := by
  intro env hB
  have hlow : (semLowerSExpr env 0 e).isSome := by
    obtain ⟨env₂, nm, cnt', hh, -⟩ :=
      semLowerSExpr_run e env 0 hrd.1 (fun s hs => wordBound_read (hB s (hrd.2 s hs)))
    rw [hh]
    rfl
  obtain ⟨env', hsem, hval, hfr⟩ := semScalar_setExpr_run (y := x) hlow
  refine ⟨env', hsem, ?_, ?_⟩
  · rintro y ⟨hyt, v, hv⟩
    by_cases hyx : y = x
    · subst hyx; exact ⟨hyt, _, hval⟩
    · exact ⟨hyt, v, by rw [hfr y hyt hyx]; exact hv⟩
  · rintro y rfl
    exact ⟨hnt, _, hval⟩

/-- **A block extended by one scalar assignment**, whose reads lie in the
    block's exit set. -/
theorem runsFrom_snoc {B W : String → Prop} {l : List LowCT} {x : String} {e : SExpr}
    (h : RunsFrom B W l) (hnt : ¬ isTmpName x) (hrd : ReadsFrom W e) :
    RunsFrom B (fun y => W y ∨ y = x) (l ++ [LowCT.RScalarSetExpr x e]) :=
  runsFrom_append h
    (runsFrom_setExpr (R := fun s => B s ∨ W s) hnt
      (readsFrom_mono hrd (fun _ hx => Or.inr hx)))
    (fun _ hs => hs)

/-- Two blocks in sequence, the second entered at the first's exit set. -/
theorem runsFrom_trans {B W₁ W₂ : String → Prop} {l₁ l₂ : List LowCT}
    (h₁ : RunsFrom B W₁ l₁) (h₂ : RunsFrom W₁ W₂ l₂) :
    RunsFrom B W₂ (l₁ ++ l₂) :=
  runsFrom_mono (runsFrom_append h₁ h₂ (fun _ hx => Or.inr hx)) (fun _ h => h)
    (fun _ hx => Or.inr hx)

/-- A block extended by two scalar assignments. -/
theorem runsFrom_snoc2 {B W : String → Prop} {l : List LowCT} {x₁ x₂ : String}
    {e₁ e₂ : SExpr} (h : RunsFrom B W l) (h₁ : ¬ isTmpName x₁) (h₂ : ¬ isTmpName x₂)
    (r₁ : ReadsFrom W e₁) (r₂ : ReadsFrom (fun y => W y ∨ y = x₁) e₂) :
    RunsFrom B (fun y => (W y ∨ y = x₁) ∨ y = x₂)
      (l ++ [LowCT.RScalarSetExpr x₁ e₁, LowCT.RScalarSetExpr x₂ e₂]) := by
  have hlist : l ++ [LowCT.RScalarSetExpr x₁ e₁, LowCT.RScalarSetExpr x₂ e₂]
      = (l ++ [LowCT.RScalarSetExpr x₁ e₁]) ++ [LowCT.RScalarSetExpr x₂ e₂] := by simp
  rw [hlist]
  exact runsFrom_snoc (runsFrom_snoc h h₁ r₁) h₂ r₂

/-- A block extended by three scalar assignments. -/
theorem runsFrom_snoc3 {B W : String → Prop} {l : List LowCT} {x₁ x₂ x₃ : String}
    {e₁ e₂ e₃ : SExpr} (h : RunsFrom B W l) (h₁ : ¬ isTmpName x₁) (h₂ : ¬ isTmpName x₂)
    (h₃ : ¬ isTmpName x₃) (r₁ : ReadsFrom W e₁)
    (r₂ : ReadsFrom (fun y => W y ∨ y = x₁) e₂)
    (r₃ : ReadsFrom (fun y => (W y ∨ y = x₁) ∨ y = x₂) e₃) :
    RunsFrom B (fun y => ((W y ∨ y = x₁) ∨ y = x₂) ∨ y = x₃)
      (l ++ [LowCT.RScalarSetExpr x₁ e₁, LowCT.RScalarSetExpr x₂ e₂,
             LowCT.RScalarSetExpr x₃ e₃]) := by
  have hlist : l ++ [LowCT.RScalarSetExpr x₁ e₁, LowCT.RScalarSetExpr x₂ e₂,
        LowCT.RScalarSetExpr x₃ e₃]
      = ((l ++ [LowCT.RScalarSetExpr x₁ e₁]) ++ [LowCT.RScalarSetExpr x₂ e₂])
        ++ [LowCT.RScalarSetExpr x₃ e₃] := by simp
  rw [hlist]
  exact runsFrom_snoc (runsFrom_snoc (runsFrom_snoc h h₁ r₁) h₂ r₂) h₃ r₃

/-- **A block extended by a `List.range`-indexed family of scalar
    assignments**, each reading only names the block already binds. -/
theorem runsFrom_mapRange {B W : String → Prop} {l : List LowCT}
    (nm : Nat → String) (ex : Nat → SExpr) (h : RunsFrom B W l) :
    ∀ n : Nat, (∀ i, i < n → ¬ isTmpName (nm i)) → (∀ i, i < n → ReadsFrom W (ex i)) →
      RunsFrom B (fun y => W y ∨ ∃ i, i < n ∧ y = nm i)
        (l ++ (List.range n).map (fun i => LowCT.RScalarSetExpr (nm i) (ex i))) := by
  intro n
  induction n with
  | zero =>
      intro _ _
      have hl : l ++ (List.range 0).map (fun i => LowCT.RScalarSetExpr (nm i) (ex i)) = l := by
        simp
      rw [hl]
      refine runsFrom_mono h (fun _ hx => hx) (fun x hx => ?_)
      rcases hx with hx | ⟨i, hi, -⟩
      · exact hx
      · exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      intro hnt hrd
      have hprev := ih (fun i hi => hnt i (by omega)) (fun i hi => hrd i (by omega))
      have hs := runsFrom_snoc hprev (hnt n (by omega))
        (readsFrom_mono (hrd n (by omega)) (fun x hx => Or.inl hx))
      have hl : l ++ (List.range (n + 1)).map (fun i => LowCT.RScalarSetExpr (nm i) (ex i))
          = (l ++ (List.range n).map (fun i => LowCT.RScalarSetExpr (nm i) (ex i)))
            ++ [LowCT.RScalarSetExpr (nm n) (ex n)] := by
        rw [List.range_succ, List.map_append, List.append_assoc]
        simp
      rw [hl]
      refine runsFrom_mono hs (fun _ hx => hx) (fun x hx => ?_)
      rcases hx with hx | ⟨i, hi, rfl⟩
      · exact Or.inl (Or.inl hx)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact Or.inl (Or.inr ⟨i, hlt, rfl⟩)
        · exact Or.inr rfl

/-- A loop invariant that shrinks with the trips remaining. -/
theorem forIn_list_inv_tail {σ α : Type} (P : List α → σ → Prop)
    (f : α → σ → Id (ForInStep σ)) (Q : α → Prop)
    (hstep : ∀ a, Q a → ∀ l s s', P (a :: l) s → f a s = ForInStep.yield s' → P l s')
    (hdone : ∀ a, Q a → ∀ l s s', P (a :: l) s → f a s = ForInStep.done s' → P [] s') :
    ∀ (l : List α), (∀ a ∈ l, Q a) → ∀ (init : σ), P l init → P [] (forIn l init f) := by
  intro l
  induction l with
  | nil => intro _ init h; exact h
  | cons a as ih =>
      intro hQ init h
      rw [List.forIn_cons]
      show P [] (match f a init with | .done b => (pure b : Id σ) | .yield b => forIn as b f)
      cases hfa : f a init with
      | done b => exact hdone a (hQ a (.head _)) as init b h hfa
      | yield b =>
          exact ih (fun x hx => hQ x (.tail _ hx)) b (hstep a (hQ a (.head _)) as init b h hfa)

/-- `forIn_list_inv_tail` at a `[:n]` range, with the trip index bounded. -/
theorem forIn_range_inv_tail {σ : Type} (P : List Nat → σ → Prop) (n : Nat)
    (f : Nat → σ → Id (ForInStep σ)) (init : σ) (hinit : P (List.range n) init)
    (hstep : ∀ a, a < n → ∀ l s s', P (a :: l) s → f a s = ForInStep.yield s' → P l s')
    (hdone : ∀ a, a < n → ∀ l s s', P (a :: l) s → f a s = ForInStep.done s' → P [] s') :
    P [] (forIn [:n] init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hsz : List.range' 0 ([:n] : Std.Legacy.Range).size 1 = List.range n := by
    simp [Std.Legacy.Range.size, List.range_eq_range']
  rw [hsz]
  exact forIn_list_inv_tail P f (fun a => a < n) hstep hdone (List.range n)
    (fun a ha => List.mem_range.mp ha) init hinit

/-- The loop invariant of `runsFrom_forInLoop`: an exit set extending `W₀` under
    which the commands emitted so far run and every already-processed trip's
    destination is bound. -/
abbrev LoopInv (B W₀ : String → Prop) (nm : Nat → String) (n : Nat)
    (rem : List Nat) (cmds : List LowCT) : Prop :=
  ∃ W : String → Prop, SrcSet W ∧ (∀ x, W₀ x → W x)
    ∧ (∀ i, i < n → i ∉ rem → W (nm i)) ∧ RunsFrom B W cmds

/-- **A block extended by one scalar assignment per trip of a `[:n]` loop.**
    Each trip appends a command binding `nm a` and reading only names the block
    already binds; the exit binds the block's exit set and every `nm i`. -/
theorem runsFrom_forInLoop {B W₀ : String → Prop} (nm : Nat → String) (n : Nat)
    (f : Nat → List LowCT → Id (ForInStep (List LowCT))) (base : List LowCT)
    (h0 : RunsFrom B W₀ base) (hS : SrcSet W₀)
    (hnt : ∀ i, i < n → ¬ isTmpName (nm i))
    (hbody : ∀ a, a < n → ∀ (W : String → Prop) (l : List LowCT), SrcSet W →
        (∀ x, W₀ x → W x) → RunsFrom B W l →
        ∃ l', f a l = ForInStep.yield l' ∧ RunsFrom B (fun y => W y ∨ y = nm a) l') :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, W₀ x → W x) ∧ (∀ i, i < n → W (nm i))
      ∧ RunsFrom B W (forIn [:n] base f : Id (List LowCT)) := by
  have hstep : ∀ a, a < n → ∀ (rem : List Nat) (s s' : List LowCT),
      LoopInv B W₀ nm n (a :: rem) s → f a s = ForInStep.yield s' →
      LoopInv B W₀ nm n rem s' := by
    intro a ha rem s s' hs hy
    obtain ⟨W, hWs, hWb, hWn, hWr⟩ := hs
    obtain ⟨l', hfl, hrun⟩ := hbody a ha W s hWs hWb hWr
    have hs'eq : s' = l' := by
      rw [hfl] at hy
      injection hy with h
      exact h.symm
    subst hs'eq
    refine ⟨fun y => W y ∨ y = nm a, srcSet_or hWs (hnt a ha),
      fun x hx => Or.inl (hWb x hx), ?_, hrun⟩
    intro i hi hmem
    by_cases hia : i = a
    · exact Or.inr (by rw [hia])
    · exact Or.inl (hWn i hi
        (fun hc => (List.mem_cons.mp hc).elim hia (fun h => hmem h)))
  have hdone : ∀ a, a < n → ∀ (rem : List Nat) (s s' : List LowCT),
      LoopInv B W₀ nm n (a :: rem) s → f a s = ForInStep.done s' →
      LoopInv B W₀ nm n [] s' := by
    intro a ha rem s s' hs hy
    obtain ⟨W, hWs, hWb, -, hWr⟩ := hs
    obtain ⟨l', hfl, -⟩ := hbody a ha W s hWs hWb hWr
    rw [hfl] at hy
    exact absurd hy (by simp)
  obtain ⟨W, hWs', hWb, hWn, hWr⟩ :=
    forIn_range_inv_tail (LoopInv B W₀ nm n) n f base
      ⟨W₀, hS, fun _ h => h, fun i hi hmem => absurd (List.mem_range.mpr hi) hmem, h0⟩
      hstep hdone
  exact ⟨W, hWs', hWb, fun i hi => hWn i hi (by simp), hWr⟩

/-- `runsFrom_forInLoop` with the exit set named. -/
theorem runsFrom_forInRange {B W₀ : String → Prop} (nm : Nat → String) (n : Nat)
    (f : Nat → List LowCT → Id (ForInStep (List LowCT))) (base : List LowCT)
    (h0 : RunsFrom B W₀ base) (hS : SrcSet W₀)
    (hnt : ∀ i, i < n → ¬ isTmpName (nm i))
    (hbody : ∀ a, a < n → ∀ (W : String → Prop) (l : List LowCT), SrcSet W →
        (∀ x, W₀ x → W x) → RunsFrom B W l →
        ∃ l', f a l = ForInStep.yield l' ∧ RunsFrom B (fun y => W y ∨ y = nm a) l') :
    RunsFrom B (fun y => W₀ y ∨ ∃ i, i < n ∧ y = nm i)
      (forIn [:n] base f : Id (List LowCT)) := by
  obtain ⟨W, hWs, hWb, hWn, hWr⟩ := runsFrom_forInLoop nm n f base h0 hS hnt hbody
  refine runsFrom_mono hWr (fun _ h => h) (fun x hx => ?_)
  rcases hx with h | ⟨i, hi, rfl⟩
  · exact hWb x h
  · exact hWn i hi

theorem map_range_getBang {α : Type} [Inhabited α] (n : Nat) (f : Nat → α) (i : Nat)
    (hi : i < n) : ((List.range n).map f)[i]! = f i := by
  have h : i < ((List.range n).map f).length := by simpa using hi
  rw [getElem!_pos _ i h]
  simp

/-! ## 4. Loop and list helpers -/

/-- A state predicate preserved by every step of an `Id`-monad `forIn` over a
    list, at the elements of that list. -/
theorem forIn_list_inv_mem {σ α : Type} (P : σ → Prop) (f : α → σ → Id (ForInStep σ)) :
    ∀ (l : List α) (init : σ), P init →
      (∀ a ∈ l, ∀ s s', P s → f a s = ForInStep.yield s' → P s') →
      (∀ a ∈ l, ∀ s s', P s → f a s = ForInStep.done s' → P s') →
      P (forIn l init f) := by
  intro l
  induction l with
  | nil => intro init h _ _; exact h
  | cons a as ih =>
      intro init h hy hd
      rw [List.forIn_cons]
      show P (match f a init with | .done b => (pure b : Id σ) | .yield b => forIn as b f)
      cases hfa : f a init with
      | done b => exact hd a (.head _) init b h hfa
      | yield b =>
          exact ih b (hy a (.head _) init b h hfa)
            (fun x hx => hy x (.tail _ hx)) (fun x hx => hd x (.tail _ hx))

/-- The loop invariant of `Secp256k1PointOpFrontCovered.forIn_range_inv` with the
    trip index bounded by the range's upper end. -/
theorem forIn_range_inv_lt {σ : Type} (P : σ → Prop) (n : Nat)
    (f : Nat → σ → Id (ForInStep σ)) (init : σ) (hinit : P init)
    (hstep : ∀ i, i < n → ∀ s s', P s → f i s = ForInStep.yield s' → P s')
    (hdone : ∀ i, i < n → ∀ s s', P s → f i s = ForInStep.done s' → P s') :
    P (forIn [:n] init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  refine forIn_list_inv_mem P f _ init hinit ?_ ?_
  · intro a ha; exact hstep a (by simpa using ha)
  · intro a ha; exact hdone a (by simpa using ha)

theorem arraySet_inv_lt (a : Array String) (p : Nat) (v : String) (Q : String → Prop)
    (hq : ∀ j, j < a.size → Q (a[j]!)) (hv : Q v) :
    ∀ k, k < a.size → Q ((a.set! p v)[k]!) := by
  intro k hk
  have hk' : k < (a.setIfInBounds p v).size := by rw [Array.size_setIfInBounds]; exact hk
  have hqa : Q a[k] := by have := hq k hk; rwa [getElem!_pos a k hk] at this
  show Q ((a.setIfInBounds p v)[k]!)
  rw [getElem!_pos (a.setIfInBounds p v) k hk', Array.getElem_setIfInBounds]
  split
  · exact hv
  · exact hqa

theorem size_set! (a : Array String) (p : Nat) (v : String) :
    (a.set! p v).size = a.size := by
  simp [Array.set!]

theorem getD_of_lt {B : String → Prop} {l : List String} {d : String} (hd : B d)
    (h : ∀ k, k < l.length → B (l[k]!)) (i : Nat) : B (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD]
  cases hl : l[i]? with
  | none => simpa using hd
  | some v =>
      have hi : i < l.length := by
        by_contra hc
        rw [List.getElem?_eq_none (Nat.le_of_not_lt hc)] at hl
        simp at hl
      have hk := h i hi
      rw [List.getElem!_eq_getElem?_getD, hl] at hk
      simpa using hk

/-- Every name of a list lies in `W`. -/
def AllIn (W : String → Prop) (l : List String) : Prop := ∀ k, k < l.length → W (l[k]!)

theorem allIn_mono {W W' : String → Prop} {l : List String} (h : AllIn W l)
    (hw : ∀ x, W x → W' x) : AllIn W' l := fun k hk => hw _ (h k hk)

theorem allIn_pair {W : String → Prop} {a b : String} (ha : W a) (hb : W b) :
    AllIn W [a, b] := by
  intro k hk
  simp only [List.length_cons, List.length_nil] at hk
  interval_cases k
  · simpa using ha
  · simpa using hb

theorem allIn_single {W : String → Prop} {a : String} (ha : W a) : AllIn W [a] := by
  intro k hk
  simp only [List.length_cons, List.length_nil] at hk
  interval_cases k
  simpa using ha

theorem allIn_append {W : String → Prop} {l₁ l₂ : List String} (h₁ : AllIn W l₁)
    (h₂ : AllIn W l₂) : AllIn W (l₁ ++ l₂) := by
  intro k hk
  simp only [List.length_append] at hk
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_append]
  split
  · next hlt =>
      have hv := h₁ k hlt
      rw [List.getElem!_eq_getElem?_getD] at hv
      exact hv
  · next hge =>
      have hv := h₂ (k - l₁.length) (by omega)
      rw [List.getElem!_eq_getElem?_getD] at hv
      exact hv

theorem allIn_take {W : String → Prop} {l : List String} (h : AllIn W l) (n : Nat) :
    AllIn W (l.take n) := by
  intro k hk
  have hkl : k < l.length := lt_of_lt_of_le hk (by simp)
  have hkn : k < n := lt_of_lt_of_le hk (by simp)
  have := h k hkl
  rw [List.getElem!_eq_getElem?_getD] at this ⊢
  rwa [List.getElem?_take_of_lt hkn]

theorem allIn_drop {W : String → Prop} {l : List String} (h : AllIn W l) (n : Nat) :
    AllIn W (l.drop n) := by
  intro k hk
  have := h (n + k) (by simp only [List.length_drop] at hk; omega)
  rw [List.getElem!_eq_getElem?_getD] at this ⊢
  rwa [List.getElem?_drop]

/-! ## 5. The ripple add and the ripple subtract

`genAdd` and `genSub` are one `Id`-monad loop each, over a mutable carry (or
borrow), the command list, and the result array. The loop invariant carries an
exit set `W` extending the entry set `B`, under which the commands emitted so far
run and the carry and every result slot are bound. -/

/-- The number of result names `genAdd` returns. -/
theorem genAdd_len (zero : String) (aN bN : List String) (pfx : String) :
    (genAdd zero aN bN pfx).2.length = max aN.length bN.length + 1 := by
  have key : (genAddRun zero aN bN pfx).snd.snd.size = max aN.length bN.length + 1 := by
    unfold genAddRun
    refine forIn_range_inv (fun r : AddS => r.snd.snd.size = max aN.length bN.length + 1)
      _ (genAddStep zero aN bN pfx) _ (by simp) ?_ ?_
    · intro i s s' hs hy
      simp only [genAddStep] at hy
      injection hy with hy
      subst hy
      rw [show ((s.snd.snd.set! i s!"{pfx}s{i}").size) = s.snd.snd.size from size_set! _ _ _]
      exact hs
    · intro i s s' _ hd
      simp only [genAddStep] at hd
      injection hd
  rw [genAdd_eq]
  simp only [Array.length_toList, size_set!]
  exact key

/-- The number of difference names `genSub` returns. -/
theorem genSub_len (zero : String) (aN pN : List String) (pfx : String) :
    (genSub zero aN pN pfx).2.1.length = aN.length := by
  have key : (genSubRun zero aN pN pfx).snd.snd.size = aN.length := by
    unfold genSubRun
    refine forIn_range_inv (fun r : SubS => r.snd.snd.size = aN.length)
      _ (genSubStep zero aN pN pfx) _ (by simp) ?_ ?_
    · intro i s s' hs hy
      simp only [genSubStep] at hy
      injection hy with hy
      subst hy
      rw [show ((s.snd.snd.set! i s!"{pfx}d{i}").size) = s.snd.snd.size from size_set! _ _ _]
      exact hs
    · intro i s s' _ hd
      simp only [genSubStep] at hd
      injection hd
  rw [genSub_eq]
  simp only [Array.length_toList]
  exact key

/-- The loop invariant of `genAdd`: an exit set extending the entry set, under
    which the emitted commands run and the carry and result slots are bound. -/
def QAdd (B : String → Prop) (n : Nat) : AddS → Prop := fun r =>
  ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x) ∧ RunsFrom B W r.snd.fst
    ∧ W r.fst ∧ r.snd.snd.size = n + 1 ∧ (∀ k, k < n + 1 → W (r.snd.snd[k]!))

/-- **`genAdd` runs from a bound operand set.** With the zero slot and both
    operand lists bound, the ripple add's commands run, and the exit binds the
    entry set together with all `max |a| |b| + 1` result names. -/
theorem genAdd_runs {B : String → Prop} (zero : String) (aN bN : List String)
    (pfx : String) (hp : HeadOk pfx) (hz : B zero) (hBs : SrcSet B)
    (hA : AllIn B aN) (hBn : AllIn B bN) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x)
      ∧ RunsFrom B W (genAdd zero aN bN pfx).1
      ∧ AllIn W (genAdd zero aN bN pfx).2 := by
  have key : QAdd B (max aN.length bN.length) (genAddRun zero aN bN pfx) := by
    unfold genAddRun
    refine forIn_range_inv (QAdd B (max aN.length bN.length)) _ (genAddStep zero aN bN pfx) _
      ⟨B, hBs, fun _ h => h, runsFrom_nil B, hz, by simp, fun k hk => by
          rw [getElem!_pos _ k (by simpa using hk)]
          simpa using hz⟩ ?_ ?_
    · intro i s s' hs hy
      simp only [genAddStep] at hy
      injection hy with hy
      subst hy
      obtain ⟨W, hWs, hWb, hWr, hWc, hsz, hres⟩ := hs
      have htn : ¬ isTmpName (s!"{pfx}t{i}") :=
        HeadOk.notTmp (HeadOk.append (HeadOk.append hp _) _)
      have hsn : ¬ isTmpName (s!"{pfx}s{i}") :=
        HeadOk.notTmp (HeadOk.append (HeadOk.append hp _) _)
      have hkn : ¬ isTmpName (s!"{pfx}k{i}") :=
        HeadOk.notTmp (HeadOk.append (HeadOk.append hp _) _)
      have hai : W (aN.getD i zero) :=
        getD_of_lt (hWb zero hz) (fun k hk => hWb _ (hA k hk)) i
      have hbi : W (bN.getD i zero) :=
        getD_of_lt (hWb zero hz) (fun k hk => hWb _ (hBn k hk)) i
      refine ⟨fun y => ((W y ∨ y = s!"{pfx}t{i}") ∨ y = s!"{pfx}s{i}") ∨ y = s!"{pfx}k{i}",
        srcSet_or (srcSet_or (srcSet_or hWs htn) hsn) hkn,
        fun x hx => Or.inl (Or.inl (Or.inl (hWb x hx))), ?_, Or.inr rfl, ?_, ?_⟩
      · refine runsFrom_snoc (runsFrom_snoc (runsFrom_snoc hWr htn ?_) hsn ?_) hkn ?_
        · exact readsFrom_add (readsFrom_add (readsFrom_var (hWs _ hai) hai)
            (readsFrom_var (hWs _ hbi) hbi)) (readsFrom_var (hWs _ hWc) hWc)
        · exact readsFrom_and (readsFrom_var htn (Or.inr rfl)) (readsFrom_lit mask32_lt)
        · exact readsFrom_shr (readsFrom_var htn (Or.inl (Or.inr rfl)))
            (readsFrom_lit lt64_32)
      · rw [size_set!]; exact hsz
      · intro k hk
        exact arraySet_inv_lt s.snd.snd i s!"{pfx}s{i}"
          (fun y => ((W y ∨ y = s!"{pfx}t{i}") ∨ y = s!"{pfx}s{i}") ∨ y = s!"{pfx}k{i}")
          (fun j hj => Or.inl (Or.inl (Or.inl (hres j (by rw [hsz] at hj; exact hj)))))
          (Or.inl (Or.inr rfl)) k (by rw [hsz]; exact hk)
    · intro i s s' _ hd
      simp only [genAddStep] at hd
      injection hd
  obtain ⟨W, hWs, hWb, hWr, hWc, hsz, hres⟩ := key
  refine ⟨W, hWs, hWb, ?_, ?_⟩
  · rw [genAdd_eq]; exact hWr
  · intro k hk
    rw [genAdd_len] at hk
    rw [genAdd_eq]
    simp only [arrayToList_getBang]
    exact arraySet_inv_lt _ _ _ W (fun j hj => hres j (by rw [hsz] at hj; exact hj)) hWc k
      (by rw [hsz]; exact hk)

/-- The loop invariant of `genSub`: an exit set extending the entry set, under
    which the emitted commands run and the borrow and difference slots are
    bound. -/
def QSub (B : String → Prop) (n : Nat) : SubS → Prop := fun r =>
  ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x) ∧ RunsFrom B W r.snd.fst
    ∧ W r.fst ∧ r.snd.snd.size = n ∧ (∀ k, k < n → W (r.snd.snd[k]!))

/-- **`genSub` runs from a bound operand set.** With the zero slot, the minuend
    list and the subtrahend list bound, the ripple subtract's commands run, and
    the exit binds the entry set, all `|a|` difference names and the final
    borrow. -/
theorem genSub_runs {B : String → Prop} (zero : String) (aN pN : List String)
    (pfx : String) (hp : HeadOk pfx) (hz : B zero) (hBs : SrcSet B)
    (hA : AllIn B aN) (hP : AllIn B pN) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x)
      ∧ RunsFrom B W (genSub zero aN pN pfx).1
      ∧ AllIn W (genSub zero aN pN pfx).2.1
      ∧ W (genSub zero aN pN pfx).2.2 := by
  have hbig : (4294967296 : Nat) < 2 ^ 64 := by norm_num
  have hone : (1 : Nat) < 2 ^ 64 := by norm_num
  have key : QSub B aN.length (genSubRun zero aN pN pfx) := by
    unfold genSubRun
    refine forIn_range_inv_lt (QSub B aN.length) _ (genSubStep zero aN pN pfx) _
      ⟨B, hBs, fun _ h => h, runsFrom_nil B, hz, by simp, fun k hk => by
          rw [getElem!_pos _ k (by simpa using hk)]
          simpa using hz⟩ ?_ ?_
    · intro i hi s s' hs hy
      simp only [genSubStep] at hy
      injection hy with hy
      subst hy
      obtain ⟨W, hWs, hWb, hWr, hWc, hsz, hres⟩ := hs
      have htn : ¬ isTmpName (s!"{pfx}t{i}") :=
        HeadOk.notTmp (HeadOk.append (HeadOk.append hp _) _)
      have hdn : ¬ isTmpName (s!"{pfx}d{i}") :=
        HeadOk.notTmp (HeadOk.append (HeadOk.append hp _) _)
      have hhn : ¬ isTmpName (s!"{pfx}h{i}") :=
        HeadOk.notTmp (HeadOk.append (HeadOk.append hp _) _)
      have hbn : ¬ isTmpName (s!"{pfx}b{i}") :=
        HeadOk.notTmp (HeadOk.append (HeadOk.append hp _) _)
      have hai : W (aN[i]!) := hWb _ (hA i hi)
      have hpi : W (pN.getD i zero) :=
        getD_of_lt (hWb zero hz) (fun k hk => hWb _ (hP k hk)) i
      refine ⟨fun y => ((((W y ∨ y = s!"{pfx}t{i}") ∨ y = s!"{pfx}d{i}")
            ∨ y = s!"{pfx}h{i}") ∨ y = s!"{pfx}b{i}"),
        srcSet_or (srcSet_or (srcSet_or (srcSet_or hWs htn) hdn) hhn) hbn,
        fun x hx => Or.inl (Or.inl (Or.inl (Or.inl (hWb x hx)))), ?_, Or.inr rfl, ?_, ?_⟩
      · refine runsFrom_snoc (runsFrom_snoc (runsFrom_snoc
          (runsFrom_snoc hWr htn ?_) hdn ?_) hhn ?_) hbn ?_
        · exact readsFrom_sub (readsFrom_sub
            (readsFrom_add (readsFrom_var (hWs _ hai) hai) (readsFrom_lit hbig))
            (readsFrom_var (hWs _ hpi) hpi)) (readsFrom_var (hWs _ hWc) hWc)
        · exact readsFrom_and (readsFrom_var htn (Or.inr rfl)) (readsFrom_lit mask32_lt)
        · exact readsFrom_shr (readsFrom_var htn (Or.inl (Or.inr rfl)))
            (readsFrom_lit lt64_32)
        · exact readsFrom_sub (readsFrom_lit hone) (readsFrom_var hhn (Or.inr rfl))
      · rw [size_set!]; exact hsz
      · intro k hk
        exact arraySet_inv_lt s.snd.snd i s!"{pfx}d{i}"
          (fun y => ((((W y ∨ y = s!"{pfx}t{i}") ∨ y = s!"{pfx}d{i}")
            ∨ y = s!"{pfx}h{i}") ∨ y = s!"{pfx}b{i}"))
          (fun j hj => Or.inl (Or.inl (Or.inl (Or.inl
            (hres j (by rw [hsz] at hj; exact hj))))))
          (Or.inl (Or.inl (Or.inr rfl))) k (by rw [hsz]; exact hk)
    · intro i _ s s' _ hd
      simp only [genSubStep] at hd
      injection hd
  obtain ⟨W, hWs, hWb, hWr, hWc, hsz, hres⟩ := key
  refine ⟨W, hWs, hWb, ?_, ?_, ?_⟩
  · rw [genSub_eq]; exact hWr
  · intro k hk
    rw [genSub_len] at hk
    rw [genSub_eq]
    simp only [arrayToList_getBang]
    exact hres k hk
  · rw [genSub_eq]; exact hWc

/-! ## 6. The operand-scanning multiply and the Solinas fold

`genMul` is two nested loops over a mutable column accumulator. The inner
invariant adds the running carry to the outer one; both carry the accumulator's
size, which bounds the column index `i + j` the inner step reads. -/

/-- The number of result names `genMul` returns. -/
theorem genMul_len (zero : String) (aN bN : List String) (pfx : String) :
    (genMul zero aN bN pfx).2.length = aN.length + bN.length := by
  have hinner : ∀ (i : Nat) (s : MulI),
      s.fst.size = aN.length + bN.length →
      (forIn [:bN.length] s (genMulInnerStep zero aN bN pfx i) : Id MulI).fst.size
        = aN.length + bN.length := by
    intro i s hs
    refine forIn_range_inv (fun r : MulI => r.fst.size = aN.length + bN.length)
      _ (genMulInnerStep zero aN bN pfx i) _ hs ?_ ?_
    · intro j t t' ht hy
      simp only [genMulInnerStep] at hy
      injection hy with hy
      subst hy
      rw [size_set!]
      exact ht
    · intro j t t' _ hd
      simp only [genMulInnerStep] at hd
      injection hd
  have key : (genMulRun zero aN bN pfx).fst.size = aN.length + bN.length := by
    unfold genMulRun
    refine forIn_range_inv (fun r : MulO => r.fst.size = aN.length + bN.length)
      _ (genMulOuterStep zero aN bN pfx) _ (by simp) ?_ ?_
    · intro i s s' hs hy
      simp only [genMulOuterStep] at hy
      injection hy with hy
      subst hy
      rw [size_set!]
      exact hinner i ⟨s.fst, zero, s.snd⟩ hs
    · intro i s s' _ hd
      simp only [genMulOuterStep] at hd
      injection hd
  rw [genMul_eq]
  simpa using key

/-- The inner-loop invariant of `genMul`: the outer invariant together with the
    running column carry. -/
def QMulI (B : String → Prop) (m : Nat) : MulI → Prop := fun r =>
  ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x) ∧ RunsFrom B W r.snd.snd
    ∧ W r.snd.fst ∧ r.fst.size = m ∧ (∀ k, k < m → W (r.fst[k]!))

/-- The outer-loop invariant of `genMul`: an exit set extending the entry set,
    under which the emitted commands run and every column slot is bound. -/
def QMulO (B : String → Prop) (m : Nat) : MulO → Prop := fun r =>
  ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x) ∧ RunsFrom B W r.snd
    ∧ r.fst.size = m ∧ (∀ k, k < m → W (r.fst[k]!))

/-- **`genMul` runs from a bound operand set.** With the zero slot and both
    operand lists bound, the operand-scanning multiply's commands run, and the
    exit binds the entry set together with all `|a| + |b|` column names. -/
theorem genMul_runs {B : String → Prop} (zero : String) (aN bN : List String)
    (pfx : String) (hp : HeadOk pfx) (hz : B zero) (hBs : SrcSet B)
    (hA : AllIn B aN) (hBn : AllIn B bN) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x)
      ∧ RunsFrom B W (genMul zero aN bN pfx).1
      ∧ AllIn W (genMul zero aN bN pfx).2 := by
  set m := aN.length + bN.length with hm
  have hstepI : ∀ i, i < aN.length → ∀ j, j < bN.length → ∀ (s s' : MulI),
      QMulI B m s → genMulInnerStep zero aN bN pfx i j s = ForInStep.yield s' →
        QMulI B m s' := by
    intro i hi j hj s s' hs hy
    simp only [genMulInnerStep] at hy
    injection hy with hy
    subst hy
    obtain ⟨W, hWs, hWb, hWr, hWc, hsz, hres⟩ := hs
    have htn : ¬ isTmpName (s!"{pfx}t{i}_{j}") :=
      HeadOk.notTmp (HeadOk.append (HeadOk.append (HeadOk.append (HeadOk.append hp _) _) _) _)
    have hpn : ¬ isTmpName (s!"{pfx}p{i}_{j}") :=
      HeadOk.notTmp (HeadOk.append (HeadOk.append (HeadOk.append (HeadOk.append hp _) _) _) _)
    have hkn : ¬ isTmpName (s!"{pfx}k{i}_{j}") :=
      HeadOk.notTmp (HeadOk.append (HeadOk.append (HeadOk.append (HeadOk.append hp _) _) _) _)
    have hai : W (aN[i]!) := hWb _ (hA i hi)
    have hbj : W (bN[j]!) := hWb _ (hBn j hj)
    have hacc : W (s.fst[i + j]!) := hres (i + j) (by omega)
    refine ⟨fun y => ((W y ∨ y = s!"{pfx}t{i}_{j}") ∨ y = s!"{pfx}p{i}_{j}")
          ∨ y = s!"{pfx}k{i}_{j}",
      srcSet_or (srcSet_or (srcSet_or hWs htn) hpn) hkn,
      fun x hx => Or.inl (Or.inl (Or.inl (hWb x hx))), ?_, Or.inr rfl, ?_, ?_⟩
    · refine runsFrom_snoc (runsFrom_snoc (runsFrom_snoc hWr htn ?_) hpn ?_) hkn ?_
      · exact readsFrom_add (readsFrom_add
          (readsFrom_mul (readsFrom_var (hWs _ hai) hai) (readsFrom_var (hWs _ hbj) hbj))
          (readsFrom_var (hWs _ hacc) hacc)) (readsFrom_var (hWs _ hWc) hWc)
      · exact readsFrom_and (readsFrom_var htn (Or.inr rfl)) (readsFrom_lit mask32_lt)
      · exact readsFrom_shr (readsFrom_var htn (Or.inl (Or.inr rfl))) (readsFrom_lit lt64_32)
    · rw [size_set!]; exact hsz
    · intro k hk
      exact arraySet_inv_lt s.fst (i + j) s!"{pfx}p{i}_{j}"
        (fun y => ((W y ∨ y = s!"{pfx}t{i}_{j}") ∨ y = s!"{pfx}p{i}_{j}")
          ∨ y = s!"{pfx}k{i}_{j}")
        (fun l hl => Or.inl (Or.inl (Or.inl (hres l (by rw [hsz] at hl; exact hl)))))
        (Or.inl (Or.inr rfl)) k (by rw [hsz]; exact hk)
  have key : QMulO B m (genMulRun zero aN bN pfx) := by
    unfold genMulRun
    refine forIn_range_inv_lt (QMulO B m) _ (genMulOuterStep zero aN bN pfx) _
      ⟨B, hBs, fun _ h => h, runsFrom_nil B, by simp [hm], fun k hk => by
          rw [getElem!_pos _ k (by simp; omega)]
          simpa using hz⟩ ?_ ?_
    · intro i hi s s' hs hy
      simp only [genMulOuterStep] at hy
      injection hy with hy
      subst hy
      obtain ⟨W, hWs, hWb, hWr, hsz, hres⟩ := hs
      have hinit : QMulI B m ⟨s.fst, zero, s.snd⟩ :=
        ⟨W, hWs, hWb, hWr, hWb zero hz, hsz, hres⟩
      have hin : QMulI B m
          ((forIn [:bN.length] (⟨s.fst, zero, s.snd⟩)
            (genMulInnerStep zero aN bN pfx i) : Id MulI)) := by
        refine forIn_range_inv_lt (QMulI B m) _ _ _ hinit (hstepI i hi) ?_
        intro j _ t t' _ hd
        simp only [genMulInnerStep] at hd
        injection hd
      obtain ⟨W', hWs', hWb', hWr', hWc', hsz', hres'⟩ := hin
      refine ⟨W', hWs', hWb', hWr', ?_, ?_⟩
      · rw [size_set!]; exact hsz'
      · intro k hk
        exact arraySet_inv_lt _ (i + bN.length) _ W'
          (fun l hl => hres' l (by rw [hsz'] at hl; exact hl)) hWc' k (by rw [hsz']; exact hk)
    · intro i _ s s' _ hd
      simp only [genMulOuterStep] at hd
      injection hd
  obtain ⟨W, hWs, hWb, hWr, hsz, hres⟩ := key
  refine ⟨W, hWs, hWb, ?_, ?_⟩
  · rw [genMul_eq]; exact hWr
  · intro k hk
    rw [genMul_len] at hk
    rw [genMul_eq]
    simp only [arrayToList_getBang]
    exact hres k hk

/-- The `genFold` case split, as the equation the run and length proofs use. -/
theorem genFold_cases (zero c0N c1N : String) (full : List String) (pfx : String) :
    genFold zero c0N c1N full pfx =
      if (full.drop 8).isEmpty then ([], full)
      else ((genMul zero [c0N, c1N] (full.drop 8) (pfx ++ "m")).1
              ++ (genAdd zero (full.take 8)
                    (genMul zero [c0N, c1N] (full.drop 8) (pfx ++ "m")).2 (pfx ++ "a")).1,
            (genAdd zero (full.take 8)
              (genMul zero [c0N, c1N] (full.drop 8) (pfx ++ "m")).2 (pfx ++ "a")).2) := rfl

/-- **A fold keeps at least eight result names.** -/
theorem genFold_len_ge (zero c0N c1N : String) (full : List String) (pfx : String)
    (h8 : 8 ≤ full.length) : 8 ≤ (genFold zero c0N c1N full pfx).2.length := by
  rw [genFold_cases]
  split
  · exact h8
  · rw [genAdd_len]
    have : (full.take 8).length = 8 := by simp; omega
    omega

/-- **`genFold` runs from a bound name set.** -/
theorem genFold_runs {B : String → Prop} (zero c0N c1N : String) (full : List String)
    (pfx : String) (hp : HeadOk pfx) (hz : B zero) (hBs : SrcSet B)
    (hc0 : B c0N) (hc1 : B c1N) (hf : AllIn B full) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x)
      ∧ RunsFrom B W (genFold zero c0N c1N full pfx).1
      ∧ AllIn W (genFold zero c0N c1N full pfx).2 := by
  rw [genFold_cases]
  split
  · exact ⟨B, hBs, fun _ h => h, runsFrom_nil B, hf⟩
  · obtain ⟨W₁, hWs₁, hWb₁, hWr₁, hn₁⟩ :=
      genMul_runs (B := B) zero [c0N, c1N] (full.drop 8) (pfx ++ "m")
        (HeadOk.append hp _) hz hBs (allIn_pair hc0 hc1) (allIn_drop hf 8)
    obtain ⟨W₂, hWs₂, hWb₂, hWr₂, hn₂⟩ :=
      genAdd_runs (B := W₁) zero (full.take 8)
        (genMul zero [c0N, c1N] (full.drop 8) (pfx ++ "m")).2 (pfx ++ "a")
        (HeadOk.append hp _) (hWb₁ zero hz) hWs₁
        (allIn_mono (allIn_take hf 8) hWb₁) hn₁
    refine ⟨fun x => W₁ x ∨ W₂ x, ?_, fun x hx => Or.inl (hWb₁ x hx),
      runsFrom_append hWr₁ hWr₂ (fun x hx => Or.inr hx), fun k hk => Or.inr (hn₂ k hk)⟩
    rintro y (h | h)
    · exact hWs₁ y h
    · exact hWs₂ y h

/-! ## 7. The three field bricks

Each brick chains the builders with `runsFrom_trans`, appends the branch-free
select mask, and closes with the eight-command select loop, handled by
`runsFrom_forInRange`. -/

/-- The `feMul` brick returns eight result names. -/
theorem feMulHalves_len (pfx : String) (A Bn : List String) :
    (feMulHalves pfx A Bn).2.length = 8 := rfl

/-- The `feAdd` brick returns eight result names. -/
theorem feAddHalves_len (pfx : String) (A Bn : List String) :
    (feAddHalves pfx A Bn).2.length = 8 := rfl

/-- The `feSub` brick returns eight result names. -/
theorem feSubHalves_len (pfx : String) (A Bn : List String) (hA8 : A.length = 8) :
    (feSubHalves pfx A Bn).2.length = 8 := by
  show ((genAdd "ZZ" (genSub "ZZ" A Bn (pfx ++ "S")).2.1
      ((List.range 8).map (fun i => s!"{pfx}PM{i}")) (pfx ++ "A")).2.take 8).length = 8
  rw [List.length_take, genAdd_len, genSub_len, hA8]
  simp

/-- **The `feMul` brick runs from a bound operand set.** -/
theorem feMulHalves_runs {B : String → Prop} (pfx : String) (A Bn : List String)
    (hp : HeadOk pfx) (hBs : SrcSet B) (hz : B "ZZ") (hc0 : B "CC0") (hc1 : B "CC1")
    (hpl : AllIn B plNames) (hA : AllIn B A) (hBn : AllIn B Bn)
    (hA8 : A.length = 8) (hB8 : Bn.length = 8) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x)
      ∧ RunsFrom B W (feMulHalves pfx A Bn).1
      ∧ AllIn W (feMulHalves pfx A Bn).2 := by
  obtain ⟨W1, hs1, hb1, hr1, hn1⟩ :=
    genMul_runs (B := B) "ZZ" A Bn (pfx ++ "M") (HeadOk.append hp _) hz hBs hA hBn
  have hl1 : 8 ≤ (genMul "ZZ" A Bn (pfx ++ "M")).2.length := by
    rw [genMul_len, hA8, hB8]; omega
  obtain ⟨W2, hs2, hb2, hr2, hn2⟩ :=
    genFold_runs (B := W1) "ZZ" "CC0" "CC1" _ (pfx ++ "F1") (HeadOk.append hp _)
      (hb1 _ hz) hs1 (hb1 _ hc0) (hb1 _ hc1) hn1
  have hl2 := genFold_len_ge "ZZ" "CC0" "CC1" _ (pfx ++ "F1") hl1
  obtain ⟨W3, hs3, hb3, hr3, hn3⟩ :=
    genFold_runs (B := W2) "ZZ" "CC0" "CC1" _ (pfx ++ "F2") (HeadOk.append hp _)
      (hb2 _ (hb1 _ hz)) hs2 (hb2 _ (hb1 _ hc0)) (hb2 _ (hb1 _ hc1)) hn2
  have hl3 := genFold_len_ge "ZZ" "CC0" "CC1" _ (pfx ++ "F2") hl2
  obtain ⟨W4, hs4, hb4, hr4, hn4⟩ :=
    genFold_runs (B := W3) "ZZ" "CC0" "CC1" _ (pfx ++ "F3") (HeadOk.append hp _)
      (hb3 _ (hb2 _ (hb1 _ hz))) hs3 (hb3 _ (hb2 _ (hb1 _ hc0)))
      (hb3 _ (hb2 _ (hb1 _ hc1))) hn3
  have hl4 := genFold_len_ge "ZZ" "CC0" "CC1" _ (pfx ++ "F3") hl3
  obtain ⟨W5, hs5, hb5, hr5, hn5⟩ :=
    genFold_runs (B := W4) "ZZ" "CC0" "CC1" _ (pfx ++ "F4") (HeadOk.append hp _)
      (hb4 _ (hb3 _ (hb2 _ (hb1 _ hz)))) hs4 (hb4 _ (hb3 _ (hb2 _ (hb1 _ hc0))))
      (hb4 _ (hb3 _ (hb2 _ (hb1 _ hc1)))) hn4
  have hl5 := genFold_len_ge "ZZ" "CC0" "CC1" _ (pfx ++ "F4") hl4
  have hB5 : ∀ x, B x → W5 x := fun x hx => hb5 _ (hb4 _ (hb3 _ (hb2 _ (hb1 _ hx))))
  have hlo8 : ((genFold "ZZ" "CC0" "CC1"
      (genFold "ZZ" "CC0" "CC1"
        (genFold "ZZ" "CC0" "CC1"
          (genFold "ZZ" "CC0" "CC1" (genMul "ZZ" A Bn (pfx ++ "M")).2 (pfx ++ "F1")).2
            (pfx ++ "F2")).2 (pfx ++ "F3")).2 (pfx ++ "F4")).2.take 8).length = 8 := by
    rw [List.length_take]
    omega
  obtain ⟨W6, hs6, hb6, hr6, hn6, hbw⟩ :=
    genSub_runs (B := W5) "ZZ" _ plNames (pfx ++ "S") (HeadOk.append hp _)
      (hB5 _ hz) hs5 (allIn_take hn5 8) (allIn_mono hpl hB5)
  have hB6 : ∀ x, B x → W6 x := fun x hx => hb6 _ (hB5 x hx)
  have hdlen := genSub_len "ZZ"
    ((genFold "ZZ" "CC0" "CC1"
        (genFold "ZZ" "CC0" "CC1"
          (genFold "ZZ" "CC0" "CC1"
            (genFold "ZZ" "CC0" "CC1" (genMul "ZZ" A Bn (pfx ++ "M")).2 (pfx ++ "F1")).2
              (pfx ++ "F2")).2 (pfx ++ "F3")).2 (pfx ++ "F4")).2.take 8)
    plNames (pfx ++ "S")
  have hMMR : ¬ isTmpName (pfx ++ "MMR") := HeadOk.notTmp (HeadOk.append hp _)
  have hMM : ¬ isTmpName (pfx ++ "MM") := HeadOk.notTmp (HeadOk.append hp _)
  have hNM : ¬ isTmpName (pfx ++ "NM") := HeadOk.notTmp (HeadOk.append hp _)
  have hRnt : ∀ i, i < 8 →
      ¬ isTmpName (((List.range 8).map (fun j => s!"{pfx}R{j}"))[i]!) := by
    intro i hi
    rw [map_range_getBang 8 _ i hi]
    exact HeadOk.notTmp (HeadOk.append (HeadOk.append hp _) _)
  have htail := runsFrom_snoc3
    (runsFrom_trans (runsFrom_trans (runsFrom_trans (runsFrom_trans
      (runsFrom_trans hr1 hr2) hr3) hr4) hr5) hr6)
    hMMR hMM hNM
    (readsFrom_sub (readsFrom_lit lt64_zero) (readsFrom_var (hs6 _ hbw) hbw))
    (readsFrom_and (readsFrom_var hMMR (Or.inr rfl)) (readsFrom_lit mask32_lt))
    (readsFrom_xor (readsFrom_var hMM (Or.inr rfl)) (readsFrom_lit mask32_lt))
  have hlo : ∀ i, i < 8 → W6 (((genFold "ZZ" "CC0" "CC1"
      (genFold "ZZ" "CC0" "CC1"
        (genFold "ZZ" "CC0" "CC1"
          (genFold "ZZ" "CC0" "CC1" (genMul "ZZ" A Bn (pfx ++ "M")).2 (pfx ++ "F1")).2
            (pfx ++ "F2")).2 (pfx ++ "F3")).2 (pfx ++ "F4")).2.take 8)[i]!) :=
    fun i hi => hb6 _ (allIn_take hn5 8 i (by rw [hlo8]; exact hi))
  have hdi : ∀ i, i < 8 → W6 ((genSub "ZZ"
      ((genFold "ZZ" "CC0" "CC1"
        (genFold "ZZ" "CC0" "CC1"
          (genFold "ZZ" "CC0" "CC1"
            (genFold "ZZ" "CC0" "CC1" (genMul "ZZ" A Bn (pfx ++ "M")).2 (pfx ++ "F1")).2
              (pfx ++ "F2")).2 (pfx ++ "F3")).2 (pfx ++ "F4")).2.take 8)
      plNames (pfx ++ "S")).2.1[i]!) := fun i hi => hn6 i (by rw [hdlen, hlo8]; exact hi)
  have hsrc7 : SrcSet (fun y => ((W6 y ∨ y = pfx ++ "MMR") ∨ y = pfx ++ "MM")
      ∨ y = pfx ++ "NM") := by
    rintro y (((h | rfl) | rfl) | rfl)
    · exact hs6 y h
    · exact hMMR
    · exact hMM
    · exact hNM
  refine ⟨fun y => (((W6 y ∨ y = pfx ++ "MMR") ∨ y = pfx ++ "MM") ∨ y = pfx ++ "NM")
      ∨ ∃ i, i < 8 ∧ y = ((List.range 8).map (fun j => s!"{pfx}R{j}"))[i]!, ?_, ?_, ?_, ?_⟩
  · rintro y (h | ⟨i, hi, rfl⟩)
    · exact hsrc7 y h
    · exact hRnt i hi
  · exact fun x hx => Or.inl (Or.inl (Or.inl (Or.inl (hB6 x hx))))
  · unfold feMulHalves
    refine runsFrom_forInRange (fun i => ((List.range 8).map (fun j => s!"{pfx}R{j}"))[i]!)
      8 _ _ htail hsrc7 hRnt ?_
    intro a ha W l hWs hWb hWr
    refine ⟨_, rfl, runsFrom_snoc hWr (hRnt a ha) (readsFrom_add ?_ ?_)⟩
    · exact readsFrom_and
        (readsFrom_var (hs6 _ (hlo a ha)) (hWb _ (Or.inl (Or.inl (Or.inl (hlo a ha))))))
        (readsFrom_var hMM (hWb _ (Or.inl (Or.inr rfl))))
    · exact readsFrom_and
        (readsFrom_var (hs6 _ (hdi a ha)) (hWb _ (Or.inl (Or.inl (Or.inl (hdi a ha))))))
        (readsFrom_var hNM (hWb _ (Or.inr rfl)))
  · intro k hk
    rw [feMulHalves_len] at hk
    exact Or.inr ⟨k, hk, rfl⟩

/-- **The `feAdd` brick runs from a bound operand set.** -/
theorem feAddHalves_runs {B : String → Prop} (pfx : String) (A Bn : List String)
    (hp : HeadOk pfx) (hBs : SrcSet B) (hz : B "ZZ")
    (hpl : AllIn B plNames) (hA : AllIn B A) (hBn : AllIn B Bn)
    (hA8 : A.length = 8) (hB8 : Bn.length = 8) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x)
      ∧ RunsFrom B W (feAddHalves pfx A Bn).1
      ∧ AllIn W (feAddHalves pfx A Bn).2 := by
  obtain ⟨W1, hs1, hb1, hr1, hn1⟩ :=
    genAdd_runs (B := B) "ZZ" A Bn (pfx ++ "A") (HeadOk.append hp _) hz hBs hA hBn
  have hl1 : (genAdd "ZZ" A Bn (pfx ++ "A")).2.length = 9 := by
    rw [genAdd_len, hA8, hB8]
    norm_num
  obtain ⟨W2, hs2, hb2, hr2, hn2, hbw⟩ :=
    genSub_runs (B := W1) "ZZ" _ (plNames ++ ["ZZ"]) (pfx ++ "S") (HeadOk.append hp _)
      (hb1 _ hz) hs1 hn1
      (allIn_append (allIn_mono hpl hb1) (allIn_single (hb1 _ hz)))
  have hl2 := genSub_len "ZZ" (genAdd "ZZ" A Bn (pfx ++ "A")).2 (plNames ++ ["ZZ"])
    (pfx ++ "S")
  have hB2 : ∀ x, B x → W2 x := fun x hx => hb2 _ (hb1 x hx)
  have hMMR : ¬ isTmpName (pfx ++ "MMR") := HeadOk.notTmp (HeadOk.append hp _)
  have hMM : ¬ isTmpName (pfx ++ "MM") := HeadOk.notTmp (HeadOk.append hp _)
  have hNM : ¬ isTmpName (pfx ++ "NM") := HeadOk.notTmp (HeadOk.append hp _)
  have hRnt : ∀ i, i < 8 →
      ¬ isTmpName (((List.range 8).map (fun j => s!"{pfx}R{j}"))[i]!) := by
    intro i hi
    rw [map_range_getBang 8 _ i hi]
    exact HeadOk.notTmp (HeadOk.append (HeadOk.append hp _) _)
  have htail := runsFrom_snoc3 (runsFrom_trans hr1 hr2) hMMR hMM hNM
    (readsFrom_sub (readsFrom_lit lt64_zero) (readsFrom_var (hs2 _ hbw) hbw))
    (readsFrom_and (readsFrom_var hMMR (Or.inr rfl)) (readsFrom_lit mask32_lt))
    (readsFrom_xor (readsFrom_var hMM (Or.inr rfl)) (readsFrom_lit mask32_lt))
  have hsi : ∀ i, i < 8 → W2 ((genAdd "ZZ" A Bn (pfx ++ "A")).2[i]!) :=
    fun i hi => hb2 _ (hn1 i (by rw [hl1]; omega))
  have hdi : ∀ i, i < 8 → W2 ((genSub "ZZ" (genAdd "ZZ" A Bn (pfx ++ "A")).2
      (plNames ++ ["ZZ"]) (pfx ++ "S")).2.1[i]!) :=
    fun i hi => hn2 i (by rw [hl2, hl1]; omega)
  have hsrc3 : SrcSet (fun y => ((W2 y ∨ y = pfx ++ "MMR") ∨ y = pfx ++ "MM")
      ∨ y = pfx ++ "NM") := by
    rintro y (((h | rfl) | rfl) | rfl)
    · exact hs2 y h
    · exact hMMR
    · exact hMM
    · exact hNM
  refine ⟨fun y => (((W2 y ∨ y = pfx ++ "MMR") ∨ y = pfx ++ "MM") ∨ y = pfx ++ "NM")
      ∨ ∃ i, i < 8 ∧ y = ((List.range 8).map (fun j => s!"{pfx}R{j}"))[i]!, ?_, ?_, ?_, ?_⟩
  · rintro y (h | ⟨i, hi, rfl⟩)
    · exact hsrc3 y h
    · exact hRnt i hi
  · exact fun x hx => Or.inl (Or.inl (Or.inl (Or.inl (hB2 x hx))))
  · unfold feAddHalves
    refine runsFrom_forInRange (fun i => ((List.range 8).map (fun j => s!"{pfx}R{j}"))[i]!)
      8 _ _ htail hsrc3 hRnt ?_
    intro a ha W l hWs hWb hWr
    refine ⟨_, rfl, runsFrom_snoc hWr (hRnt a ha) (readsFrom_add ?_ ?_)⟩
    · exact readsFrom_and
        (readsFrom_var (hs2 _ (hsi a ha)) (hWb _ (Or.inl (Or.inl (Or.inl (hsi a ha))))))
        (readsFrom_var hMM (hWb _ (Or.inl (Or.inr rfl))))
    · exact readsFrom_and
        (readsFrom_var (hs2 _ (hdi a ha)) (hWb _ (Or.inl (Or.inl (Or.inl (hdi a ha))))))
        (readsFrom_var hNM (hWb _ (Or.inr rfl)))
  · intro k hk
    rw [feAddHalves_len] at hk
    exact Or.inr ⟨k, hk, rfl⟩

/-- **The `feSub` brick runs from a bound operand set.** -/
theorem feSubHalves_runs {B : String → Prop} (pfx : String) (A Bn : List String)
    (hp : HeadOk pfx) (hBs : SrcSet B) (hz : B "ZZ")
    (hpl : AllIn B plNames) (hA : AllIn B A) (hBn : AllIn B Bn) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x)
      ∧ RunsFrom B W (feSubHalves pfx A Bn).1
      ∧ AllIn W (feSubHalves pfx A Bn).2 := by
  obtain ⟨W1, hs1, hb1, hr1, hn1, hbw⟩ :=
    genSub_runs (B := B) "ZZ" A Bn (pfx ++ "S") (HeadOk.append hp _) hz hBs hA hBn
  have hpll : plNames.length = 8 := by simp [plNames]
  have hMMR : ¬ isTmpName (pfx ++ "MMR") := HeadOk.notTmp (HeadOk.append hp _)
  have hMM : ¬ isTmpName (pfx ++ "MM") := HeadOk.notTmp (HeadOk.append hp _)
  have hPMnt : ∀ i, i < 8 →
      ¬ isTmpName (((List.range 8).map (fun j => s!"{pfx}PM{j}"))[i]!) := by
    intro i hi
    rw [map_range_getBang 8 _ i hi]
    exact HeadOk.notTmp (HeadOk.append (HeadOk.append hp _) _)
  have h2 := runsFrom_snoc2 hr1 hMMR hMM
    (readsFrom_sub (readsFrom_lit lt64_zero) (readsFrom_var (hs1 _ hbw) hbw))
    (readsFrom_and (readsFrom_var hMMR (Or.inr rfl)) (readsFrom_lit mask32_lt))
  have hsrc2 : SrcSet (fun y => (W1 y ∨ y = pfx ++ "MMR") ∨ y = pfx ++ "MM") :=
    srcSet_or (srcSet_or hs1 hMMR) hMM
  obtain ⟨W4, hs4, hb4, hr4, hn4⟩ :=
    genAdd_runs
      (B := fun y => ((W1 y ∨ y = pfx ++ "MMR") ∨ y = pfx ++ "MM")
        ∨ ∃ i, i < 8 ∧ y = ((List.range 8).map (fun j => s!"{pfx}PM{j}"))[i]!)
      "ZZ" (genSub "ZZ" A Bn (pfx ++ "S")).2.1
      ((List.range 8).map (fun j => s!"{pfx}PM{j}")) (pfx ++ "A") (HeadOk.append hp _)
      (Or.inl (Or.inl (Or.inl (hb1 _ hz))))
      (by
        rintro y ((h | ⟨i, hi, rfl⟩))
        · exact hsrc2 y h
        · exact hPMnt i hi)
      (fun k hk => Or.inl (Or.inl (Or.inl (hn1 k hk))))
      (fun k hk => Or.inr ⟨k, by simpa using hk, rfl⟩)
  refine ⟨W4, hs4, fun x hx => hb4 _ (Or.inl (Or.inl (Or.inl (hb1 x hx)))), ?_,
    allIn_take hn4 8⟩
  unfold feSubHalves
  refine runsFrom_trans ?_ hr4
  refine runsFrom_forInRange (fun i => ((List.range 8).map (fun j => s!"{pfx}PM{j}"))[i]!)
    8 _ _ h2 hsrc2 hPMnt ?_
  intro a ha W l hWs hWb hWr
  have hpa : W1 (plNames[a]!) := hb1 _ (hpl a (by rw [hpll]; exact ha))
  exact ⟨_, rfl, runsFrom_snoc hWr (hPMnt a ha)
    (readsFrom_and (readsFrom_var (hs1 _ hpa) (hWb _ (Or.inl (Or.inl hpa))))
      (readsFrom_var hMM (hWb _ (Or.inr rfl))))⟩

/-! ## 8. One schedule entry

A brick's entry set is the reduction constants together with the half-limb slots
of the field elements a schedule prefix has already written; its exit set is the
same with the entry's own output field element appended. -/

/-- The two input field elements of a schedule entry. -/
def fopArgs : FOp → String × String
  | .mul _ a b => (a, b)
  | .add _ a b => (a, b)
  | .sub _ a b => (a, b)

/-- The names a brick may read: the reduction constants and the half-limb slots
    of the field elements a schedule prefix has written. -/
def BrickBound (S : List String) : String → Prop :=
  fun y => y = "ZZ" ∨ y = "CC0" ∨ y = "CC1" ∨ (∃ i, i < 8 ∧ y = plNames[i]!)
    ∨ ∃ fe ∈ S, ∃ k, k < 8 ∧ y = (feH fe)[k]!

theorem brickBound_pl (S : List String) : AllIn (BrickBound S) plNames := by
  intro k hk
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, by simpa [plNames] using hk, rfl⟩)))

theorem brickBound_feH {S : List String} {fe : String} (h : fe ∈ S) :
    AllIn (BrickBound S) (feH fe) := by
  intro k hk
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨fe, h, k, by simpa [feH] using hk, rfl⟩)))

theorem brickBound_src {S : List String} (hS : ∀ fe ∈ S, HeadOk fe) :
    SrcSet (BrickBound S) := by
  rintro y (rfl | rfl | rfl | ⟨i, -, rfl⟩ | ⟨fe, hfe, k, -, rfl⟩)
  · exact notTmp_ZZ
  · exact notTmp_CC0
  · exact notTmp_CC1
  · exact namesClean_plNames i
  · exact namesClean_feH fe (hS fe hfe) k

/-- The exit set of a brick refines the entry set extended by the output. -/
theorem brickBound_snoc_sub {S : List String} {o : String} {W₁ : String → Prop}
    (hb₁ : ∀ x, BrickBound S x → W₁ x) :
    ∀ y, BrickBound (S ++ [o]) y → (W₁ y ∨ ∃ k, k < 8 ∧ y = s!"{o}h{k}") := by
  rintro y (h | h | h | h | ⟨fe, hfe, k, hk, rfl⟩)
  · exact Or.inl (hb₁ y (Or.inl h))
  · exact Or.inl (hb₁ y (Or.inr (Or.inl h)))
  · exact Or.inl (hb₁ y (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (hb₁ y (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · rcases List.mem_append.mp hfe with hin | hin
    · exact Or.inl (hb₁ _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨fe, hin, k, hk, rfl⟩)))))
    · rcases List.mem_singleton.mp hin with rfl
      exact Or.inr ⟨k, hk, by simp only [feH]; exact map_range_getBang 8 _ k hk⟩

/-- **The copy block at the end of an emitted brick.** -/
theorem wire_runs {B W₁ : String → Prop} {o : String} {cr : List LowCT × List String}
    (hoO : HeadOk o) (hlen : cr.2.length = 8) (hs₁ : SrcSet W₁)
    (hr₁ : RunsFrom B W₁ cr.1) (hn₁ : AllIn W₁ cr.2) :
    RunsFrom B (fun y => W₁ y ∨ ∃ k, k < 8 ∧ y = s!"{o}h{k}")
      (cr.1 ++ (List.range 8).map
        (fun k => LowCT.RScalarSetExpr s!"{o}h{k}" (sv (cr.2[k]!)))) :=
  runsFrom_mapRange (fun k => s!"{o}h{k}") (fun k => sv (cr.2[k]!)) hr₁ 8
    (fun _ _ => HeadOk.notTmp (HeadOk.append (HeadOk.append hoO _) _))
    (fun i hi => readsFrom_var (hs₁ _ (hn₁ i (by rw [hlen]; exact hi)))
      (hn₁ i (by rw [hlen]; exact hi)))

/-- **One emitted brick runs.** From the reduction constants and the half-limb
    slots of the field elements written so far, the brick and its copy block run,
    and the exit adds the output field element's eight slots. -/
theorem emitFOp_runs (idx : Nat) (op : FOp) (S : List String)
    (hS : ∀ fe ∈ S, HeadOk fe) (hok : FOpOkB op = true)
    (ha : (fopArgs op).1 ∈ S) (hb : (fopArgs op).2 ∈ S) :
    RunsFrom (BrickBound S) (BrickBound (S ++ [fopOut op])) (emitFOp idx op) := by
  cases op with
  | mul o a b =>
      simp only [FOpOkB, Bool.and_eq_true] at hok
      obtain ⟨W₁, hs₁, hb₁, hr₁, hn₁⟩ :=
        feMulHalves_runs (B := BrickBound S) s!"op{idx}" (feH a) (feH b) (headOk_op idx)
          (brickBound_src hS) (Or.inl rfl) (Or.inr (Or.inl rfl))
          (Or.inr (Or.inr (Or.inl rfl))) (brickBound_pl S) (brickBound_feH ha)
          (brickBound_feH hb) (by simp [feH]) (by simp [feH])
      exact runsFrom_mono
        (wire_runs (headOk_of_headOkB o hok.1.1) (feMulHalves_len _ _ _) hs₁ hr₁ hn₁)
        (fun _ h => h) (brickBound_snoc_sub hb₁)
  | add o a b =>
      simp only [FOpOkB, Bool.and_eq_true] at hok
      obtain ⟨W₁, hs₁, hb₁, hr₁, hn₁⟩ :=
        feAddHalves_runs (B := BrickBound S) s!"op{idx}" (feH a) (feH b) (headOk_op idx)
          (brickBound_src hS) (Or.inl rfl) (brickBound_pl S) (brickBound_feH ha)
          (brickBound_feH hb) (by simp [feH]) (by simp [feH])
      exact runsFrom_mono
        (wire_runs (headOk_of_headOkB o hok.1.1) (feAddHalves_len _ _ _) hs₁ hr₁ hn₁)
        (fun _ h => h) (brickBound_snoc_sub hb₁)
  | sub o a b =>
      simp only [FOpOkB, Bool.and_eq_true] at hok
      obtain ⟨W₁, hs₁, hb₁, hr₁, hn₁⟩ :=
        feSubHalves_runs (B := BrickBound S) s!"op{idx}" (feH a) (feH b) (headOk_op idx)
          (brickBound_src hS) (Or.inl rfl) (brickBound_pl S) (brickBound_feH ha)
          (brickBound_feH hb)
      exact runsFrom_mono
        (wire_runs (headOk_of_headOkB o hok.1.1) (feSubHalves_len _ _ _ (by simp [feH]))
          hs₁ hr₁ hn₁)
        (fun _ h => h) (brickBound_snoc_sub hb₁)

/-! ## 9. A whole schedule -/

/-- The field elements a schedule appends to the written set. -/
def addOuts (S : List String) (ops : List FOp) : List String :=
  ops.foldl (fun acc op => acc ++ [fopOut op]) S

theorem addOuts_nil (S : List String) : addOuts S [] = S := rfl

theorem addOuts_cons (S : List String) (op : FOp) (rest : List FOp) :
    addOuts S (op :: rest) = addOuts (S ++ [fopOut op]) rest := rfl

/-- Every entry of a schedule reads field elements a previous entry wrote.

    Stated as an inductive over `List.Mem` rather than a `Bool` decision
    procedure. Deciding it costs the kernel a `String` equality per candidate —
    roughly eight hundred of them across the doubling schedule, measured at 227 s
    for the single `by decide`. The membership constructors `List.Mem.head` and
    `List.Mem.tail` carry the same information structurally, with no `String`
    equality reduced anywhere, and the whole obligation then elaborates inside
    the module's import time. -/
inductive InputsOk : List String → List FOp → Prop
  | nil {S : List String} : InputsOk S []
  | cons {S : List String} {op : FOp} {rest : List FOp} :
      (fopArgs op).1 ∈ S → (fopArgs op).2 ∈ S →
      InputsOk (S ++ [fopOut op]) rest → InputsOk S (op :: rest)

/-- Discharge an `InputsOk` obligation for a literal schedule without deciding a
    single `String` equality. -/
macro "inputs_ok" : tactic =>
  `(tactic| repeat' first
      | exact InputsOk.nil
      | refine InputsOk.cons ?_ ?_ ?_
      | exact List.Mem.head _
      | apply List.Mem.tail)

/-- The output field element of a head-clean schedule entry is head-clean. -/
theorem headOk_fopOut {op : FOp} (h : FOpOkB op = true) : HeadOk (fopOut op) := by
  cases op with
  | mul o a b => simp only [FOpOkB, Bool.and_eq_true] at h; exact headOk_of_headOkB o h.1.1
  | add o a b => simp only [FOpOkB, Bool.and_eq_true] at h; exact headOk_of_headOkB o h.1.1
  | sub o a b => simp only [FOpOkB, Bool.and_eq_true] at h; exact headOk_of_headOkB o h.1.1

/-- **A whole schedule of bricks runs.** -/
-- The generator is tied to `emitFOp` at SOME index, not at its own: the tail of
-- the induction runs `fun i => g (i + 1)`, so pinning `g i op = emitFOp i op`
-- would demand `emitFOp (i + 1) op = emitFOp i op`. Totality does not depend on
-- which index a brick uses — `emitFOp_runs` is generic in it — so the existential
-- is the right hypothesis, and it is what makes the recursion typecheck.
theorem brickFold_runs : ∀ (ops : List FOp) (S : List String) (g : Nat → FOp → List LowCT),
    (∀ fe ∈ S, HeadOk fe) → (∀ i op, ∃ j, g i op = emitFOp j op) →
    (∀ op ∈ ops, FOpOkB op = true) → InputsOk S ops →
    RunsFrom (BrickBound S) (BrickBound (addOuts S ops)) ((ops.mapIdx g).flatten) := by
  intro ops
  induction ops with
  | nil => intro S _ _ _ _ _; rw [addOuts_nil]; exact runsFrom_nil _
  | cons op rest ih =>
      intro S g hS hg hok hio
      cases hio with
      | cons hia hib hirest =>
        have hS' : ∀ fe ∈ S ++ [fopOut op], HeadOk fe := by
          intro fe hfe
          rcases List.mem_append.mp hfe with hin | hin
          · exact hS fe hin
          · rcases List.mem_singleton.mp hin with rfl
            exact headOk_fopOut (hok op (.head _))
        obtain ⟨j, hj⟩ := hg 0 op
        rw [List.mapIdx_cons, List.flatten_cons, hj, addOuts_cons]
        -- Bind the induction hypothesis first. Nested inside `runsFrom_trans` its
        -- type is unified against the goal jointly, and that unification does not
        -- terminate within the heartbeat budget.
        have hih := ih (S ++ [fopOut op]) (fun i => g (i + 1)) hS'
          (fun i o' => hg (i + 1) o') (fun o' ho' => hok o' (.tail _ ho')) hirest
        exact runsFrom_trans (emitFOp_runs j op S hS (hok op (.head _)) hia hib) hih

/-- **The doubling schedule runs** from the reduction constants and the three
    input coordinates' half-limb slots. -/
theorem jacDblSchedule_runs :
    RunsFrom (BrickBound ["X", "Y", "Z"])
      (BrickBound (addOuts ["X", "Y", "Z"] jacDblSchedule))
      (runSchedule jacDblSchedule) := by
  refine brickFold_runs jacDblSchedule ["X", "Y", "Z"] (fun i op => emitFOp i op) ?_
    (fun i op => ⟨i, rfl⟩) jacDblSchedule_ok (by inputs_ok)
  intro fe hfe
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfe
  rcases hfe with rfl | rfl | rfl
  · exact headOk_X
  · exact headOk_Y
  · exact headOk_Z

/-! ## 10. The prologue's bound names

`Secp256k1PointOpPrologue.jacDblPrologue_run` reports the half-limb *readout*
(`BrickScope`) and the schedule-name value tie; neither states that a slot is
bound. This section re-runs the prologue's three stages and reads off the
bindings: the reduction constants from `ConstVals`, and the coordinate slots
from the two half-limb conjuncts of `loadCoord_run`. -/

/-- The eight half-limb slots of a field element, from its four low and four
    high halves. -/
theorem slots_of_halves {fe : String} {E : SEnvScalar}
    (hlo : ∀ j, j < 4 → ∃ v : BitVec 64, E s!"{fe}h{2 * j}" = some ⟨.sword 64, v⟩)
    (hhi : ∀ j, j < 4 → ∃ v : BitVec 64, E s!"{fe}h{2 * j + 1}" = some ⟨.sword 64, v⟩) :
    ∀ k, k < 8 → ∃ v : BitVec 64, E (feHN fe k) = some ⟨.sword 64, v⟩ := by
  intro k hk
  interval_cases k
  · exact hlo 0 (by norm_num)
  · exact hhi 0 (by norm_num)
  · exact hlo 1 (by norm_num)
  · exact hhi 1 (by norm_num)
  · exact hlo 2 (by norm_num)
  · exact hhi 2 (by norm_num)
  · exact hlo 3 (by norm_num)
  · exact hhi 3 (by norm_num)

/-- A half-limb name read out of `feH`. -/
theorem feH_getBang {fe : String} {k : Nat} (hk : k < 8) : (feH fe)[k]! = feHN fe k := by
  simp only [feH]
  exact map_range_getBang 8 _ k hk

/-- **The `jacDbl` prologue binds every name a brick reads.** -/
theorem jacDblPrologue_bound {n : Nat} {env env₁ : SEnvScalar} {a : Fin n → BitVec 64}
    (hP : env "P" = some ⟨.memref n, a⟩)
    (hSem : semScalar (seqAll jacDblPrologue) env = some env₁) :
    ∀ x, BrickBound ["X", "Y", "Z"] x → WordBound env₁ x := by
  obtain ⟨E2, hs2, hFI2, hCV2, -⟩ := idxConst_run hP
  obtain ⟨E3, hs3, hloX, hhiX, hFI3, hfr3⟩ :=
    loadCoord_run (o := 0) (fe := "X") (c := 'X') rfl (by decide) (by decide) (by decide)
      (by norm_num) hFI2
  obtain ⟨E4, hs4, hloY, hhiY, hFI4, hfr4⟩ :=
    loadCoord_run (o := 4) (fe := "Y") (c := 'Y') rfl (by decide) (by decide) (by decide)
      (by norm_num) hFI3
  obtain ⟨E5, hs5, hloZ, hhiZ, -, hfr5⟩ :=
    loadCoord_run (o := 8) (fe := "Z") (c := 'Z') rfl (by decide) (by decide) (by decide)
      (by norm_num) hFI4
  have hrun : semScalar (seqAll jacDblPrologue) env = some E5 :=
    semScalar_append_run (semScalar_append_run (semScalar_append_run hs2 hs3) hs4) hs5
  rw [hSem] at hrun
  obtain rfl : env₁ = E5 := Option.some.inj hrun
  have hCV5 : ConstVals env₁ := constVals_load3 hfr3 hfr4 hfr5 hCV2
  have hntX : ∀ k : Nat, ¬ isTmpName (feHN "X" k) :=
    fun k => HeadOk.notTmp (headOk_of_hd (hd_feHN hd_X k) (by decide))
  have hntY : ∀ k : Nat, ¬ isTmpName (feHN "Y" k) :=
    fun k => HeadOk.notTmp (headOk_of_hd (hd_feHN hd_Y k) (by decide))
  have hntZ : ∀ k : Nat, ¬ isTmpName (feHN "Z" k) :=
    fun k => HeadOk.notTmp (headOk_of_hd (hd_feHN hd_Z k) (by decide))
  have hSX : ∀ k, k < 8 → ∃ v : BitVec 64, env₁ (feHN "X" k) = some ⟨.sword 64, v⟩ := by
    intro k hk
    rw [feHN_keep_load hfr5 (hntX k) hk (by decide),
      feHN_keep_load hfr4 (hntX k) hk (by decide)]
    exact slots_of_halves (fe := "X") (fun j hj => ⟨_, hloX j hj⟩)
      (fun j hj => ⟨_, hhiX j hj⟩) k hk
  have hSY : ∀ k, k < 8 → ∃ v : BitVec 64, env₁ (feHN "Y" k) = some ⟨.sword 64, v⟩ := by
    intro k hk
    rw [feHN_keep_load hfr5 (hntY k) hk (by decide)]
    exact slots_of_halves (fe := "Y") (fun j hj => ⟨_, hloY j hj⟩)
      (fun j hj => ⟨_, hhiY j hj⟩) k hk
  have hSZ : ∀ k, k < 8 → ∃ v : BitVec 64, env₁ (feHN "Z" k) = some ⟨.sword 64, v⟩ :=
    slots_of_halves (fe := "Z") (fun j hj => ⟨_, hloZ j hj⟩) (fun j hj => ⟨_, hhiZ j hj⟩)
  rintro x (rfl | rfl | rfl | ⟨i, hi, rfl⟩ | ⟨fe, hfe, k, hk, rfl⟩)
  · exact ⟨notTmp_ZZ, _, hCV5.zz⟩
  · exact ⟨notTmp_CC0, _, hCV5.lo⟩
  · exact ⟨notTmp_CC1, _, hCV5.hi⟩
  · refine ⟨namesClean_plNames i, ?_⟩
    rw [show plNames[i]! = s!"PL{i}" from by
      simp only [plNames]; exact map_range_getBang 8 _ i hi]
    exact ⟨_, hCV5.pl i hi⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfe
    rcases hfe with rfl | rfl | rfl
    · exact ⟨namesClean_feH "X" headOk_X k, by rw [feH_getBang hk]; exact hSX k hk⟩
    · exact ⟨namesClean_feH "Y" headOk_Y k, by rw [feH_getBang hk]; exact hSY k hk⟩
    · exact ⟨namesClean_feH "Z" headOk_Z k, by rw [feH_getBang hk]; exact hSZ k hk⟩

/-! ## 11. The whole `jacDbl` body -/

/-- **The `jacDbl` body runs to completion.** From an entry environment
    satisfying `Secp256k1PointOpPrologue.PrologueEntry` whose `out` holds a
    12-cell frame, the prologue binds every name the schedule reads, the schedule
    binds the three output field elements' half-limb slots, and the three store
    blocks then run. -/
theorem jacDblBody_runs {n : Nat} {env : SEnvScalar} {a : Fin n → BitVec 64}
    {b : Fin 12 → BitVec 64} {X Y Z : Nat}
    (hE : PrologueEntry env a X Y Z)
    (hout : env "out" = some ⟨.memref 12, b⟩) :
    ∃ env', semScalar jacDblBody env = some env' := by
  obtain ⟨E1, hs1, hsc1, -⟩ := jacDblPrologue_run env a X Y Z hE
  obtain ⟨E2, hs2, -, hW2⟩ := jacDblSchedule_runs E1 (jacDblPrologue_bound hE.frame hs1)
  obtain ⟨hFI1, ho1⟩ := jacDblPrologue_frame hE.frame hs1
  have hb2 : E2 "out" = some ⟨.memref 12, b⟩ := by
    rw [jacDblSchedule_out hs2, ho1]
    exact hout
  have hix2 : ∀ i, i < 12 → E2 s!"ix{i}" = some ⟨.sword 64, BitVec.ofNat 64 i⟩ := by
    intro i hi
    rw [jacDblSchedule_ix i hi hs2]
    exact hFI1.idx i hi
  have hslots : ∀ fe : String, fe ∈ addOuts ["X", "Y", "Z"] jacDblSchedule →
      SlotsBound E2 fe := by
    intro fe hfe k hk
    have hb := hW2 _ (brickBound_feH hfe k (by simpa [feH] using hk))
    rw [feH_getBang hk] at hb
    exact hb.2
  obtain ⟨env'', -, hsem3, -, -⟩ :=
    pointOpEpilogue_cells (jacDblSchedule_waist_scope E1 E2 hsc1 hs2) hb2 hix2
      (slotsBound_reads (hslots "Xp" (by decide)))
      (slotsBound_reads (hslots "Yp" (by decide)))
      (slotsBound_reads (hslots "Zp" (by decide)))
  refine ⟨env'', ?_⟩
  rw [jacDblBody_split, semScalar_seqAll_append, hs1, Option.bind_some,
    semScalar_seqAll_append, hs2, Option.bind_some]
  exact hsem3

/-- **The `jacDbl` body's output frame, unconditionally.** The existential form
    of `Secp256k1PointOpWholeBody.jacDblBody_cells`: from a `PrologueEntry`
    environment whose `out` holds a 12-cell frame, `Secp256k1PointOpFront.jacDblBody`
    runs, and its final environment holds `Secp256k1PointOpFront.pointCells` of
    `jacDblSpec X Y Z` at `out`. -/
theorem jacDblBody_cells_total {n : Nat} {env : SEnvScalar} {a : Fin n → BitVec 64}
    {b : Fin 12 → BitVec 64} {X Y Z : Nat}
    (hE : PrologueEntry env a X Y Z)
    (hout : env "out" = some ⟨.memref 12, b⟩) :
    ∃ (env' : SEnvScalar) (fr : Fin 12 → BitVec 64),
      semScalar jacDblBody env = some env'
        ∧ env' "out" = some ⟨.memref 12, fr⟩
        ∧ ∀ m : Fin 12, (fr m).toNat = (pointCells (jacDblSpec X Y Z)).getD m.val 0 := by
  obtain ⟨env', hrun⟩ := jacDblBody_runs hE hout
  obtain ⟨fr, hfr, hcells⟩ := jacDblBody_cells hE hout hrun
  exact ⟨env', fr, hrun, hfr, hcells⟩

/-! ## 12. The whole `jacAdd` body

The addition schedule reads six input coordinates out of two frames; everything
else is the doubling argument at a longer schedule. -/

/-- **The addition schedule runs** from the reduction constants and the six input
    coordinates' half-limb slots. -/
theorem jacAddSchedule_runs :
    RunsFrom (BrickBound ["X1", "Y1", "Z1", "X2", "Y2", "Z2"])
      (BrickBound (addOuts ["X1", "Y1", "Z1", "X2", "Y2", "Z2"] jacAddSchedule))
      (runSchedule jacAddSchedule) := by
  refine brickFold_runs jacAddSchedule ["X1", "Y1", "Z1", "X2", "Y2", "Z2"]
    (fun i op => emitFOp i op) ?_ (fun i op => ⟨i, rfl⟩) jacAddSchedule_ok (by inputs_ok)
  intro fe hfe
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfe
  rcases hfe with rfl | rfl | rfl | rfl | rfl | rfl
  · exact headOk_X1
  · exact headOk_Y1
  · exact headOk_Z1
  · exact headOk_X2
  · exact headOk_Y2
  · exact headOk_Z2

/-- **The `jacAdd` prologue binds every name a brick reads.** -/
theorem jacAddPrologue_bound {n : Nat} {env env₁ : SEnvScalar} {a1 a2 : Fin n → BitVec 64}
    (hP1 : env "P1" = some ⟨.memref n, a1⟩) (hP2 : env "P2" = some ⟨.memref n, a2⟩)
    (hSem : semScalar (seqAll jacAddPrologue) env = some env₁) :
    ∀ x, BrickBound ["X1", "Y1", "Z1", "X2", "Y2", "Z2"] x → WordBound env₁ x := by
  obtain ⟨E2, hs2, hFI2, hCV2, -, -⟩ := idxConst2_run hP1 hP2
  obtain ⟨E3, hs3, hloX1, hhiX1, hFI3, hfr3⟩ :=
    loadCoordA_run (o := 0) (arrN := "P1") (fe := "X1") rfl (by decide) (by decide)
      (by decide) rfl rfl (by norm_num) hFI2.frame1 hFI2
  obtain ⟨E4, hs4, hloY1, hhiY1, hFI4, hfr4⟩ :=
    loadCoordA_run (o := 4) (arrN := "P1") (fe := "Y1") rfl (by decide) (by decide)
      (by decide) rfl rfl (by norm_num) hFI3.frame1 hFI3
  obtain ⟨E5, hs5, hloZ1, hhiZ1, hFI5, hfr5⟩ :=
    loadCoordA_run (o := 8) (arrN := "P1") (fe := "Z1") rfl (by decide) (by decide)
      (by decide) rfl rfl (by norm_num) hFI4.frame1 hFI4
  obtain ⟨E6, hs6, hloX2, hhiX2, hFI6, hfr6⟩ :=
    loadCoordA_run (o := 0) (arrN := "P2") (fe := "X2") rfl (by decide) (by decide)
      (by decide) rfl rfl (by norm_num) hFI5.frame2 hFI5
  obtain ⟨E7, hs7, hloY2, hhiY2, hFI7, hfr7⟩ :=
    loadCoordA_run (o := 4) (arrN := "P2") (fe := "Y2") rfl (by decide) (by decide)
      (by decide) rfl rfl (by norm_num) hFI6.frame2 hFI6
  obtain ⟨E8, hs8, hloZ2, hhiZ2, -, hfr8⟩ :=
    loadCoordA_run (o := 8) (arrN := "P2") (fe := "Z2") rfl (by decide) (by decide)
      (by decide) rfl rfl (by norm_num) hFI7.frame2 hFI7
  have hrun : semScalar (seqAll jacAddPrologue) env = some E8 :=
    semScalar_append_run (semScalar_append_run (semScalar_append_run
      (semScalar_append_run (semScalar_append_run (semScalar_append_run hs2 hs3) hs4)
        hs5) hs6) hs7) hs8
  rw [hSem] at hrun
  obtain rfl : env₁ = E8 := Option.some.inj hrun
  have hCV8 : ConstVals env₁ :=
    constVals_load hfr8 hd_Z2 (by decide) (by decide)
      (fun j hj => by interval_cases j <;> decide)
      (constVals_load hfr7 hd_Y2 (by decide) (by decide)
        (fun j hj => by interval_cases j <;> decide)
        (constVals_load hfr6 hd_X2 (by decide) (by decide)
          (fun j hj => by interval_cases j <;> decide)
          (constVals_load hfr5 hd_Z1 (by decide) (by decide)
            (fun j hj => by interval_cases j <;> decide)
            (constVals_load hfr4 hd_Y1 (by decide) (by decide)
              (fun j hj => by interval_cases j <;> decide)
              (constVals_load hfr3 hd_X1 (by decide) (by decide)
                (fun j hj => by interval_cases j <;> decide) hCV2)))))
  have kX1 : ∀ k, k < 8 → env₁ (feHN "X1" k) = E3 (feHN "X1" k) :=
    slots_trans (slots_keep hfr8 hd_X1 (by decide) (by decide))
      (slots_trans (slots_keep hfr7 hd_X1 (by decide) (by decide))
        (slots_trans (slots_keep hfr6 hd_X1 (by decide) (by decide))
          (slots_trans (slots_keep hfr5 hd_X1 (by decide) (by decide))
            (slots_keep hfr4 hd_X1 (by decide) (by decide)))))
  have kY1 : ∀ k, k < 8 → env₁ (feHN "Y1" k) = E4 (feHN "Y1" k) :=
    slots_trans (slots_keep hfr8 hd_Y1 (by decide) (by decide))
      (slots_trans (slots_keep hfr7 hd_Y1 (by decide) (by decide))
        (slots_trans (slots_keep hfr6 hd_Y1 (by decide) (by decide))
          (slots_keep hfr5 hd_Y1 (by decide) (by decide))))
  have kZ1 : ∀ k, k < 8 → env₁ (feHN "Z1" k) = E5 (feHN "Z1" k) :=
    slots_trans (slots_keep hfr8 hd_Z1 (by decide) (by decide))
      (slots_trans (slots_keep hfr7 hd_Z1 (by decide) (by decide))
        (slots_keep hfr6 hd_Z1 (by decide) (by decide)))
  have kX2 : ∀ k, k < 8 → env₁ (feHN "X2" k) = E6 (feHN "X2" k) :=
    slots_trans (slots_keep hfr8 hd_X2 (by decide) (by decide))
      (slots_keep hfr7 hd_X2 (by decide) (by decide))
  have kY2 : ∀ k, k < 8 → env₁ (feHN "Y2" k) = E7 (feHN "Y2" k) :=
    slots_keep hfr8 hd_Y2 (by decide) (by decide)
  have sX1 : ∀ k, k < 8 → ∃ v : BitVec 64, env₁ (feHN "X1" k) = some ⟨.sword 64, v⟩ := by
    intro k hk
    rw [kX1 k hk]
    exact slots_of_halves (fe := "X1") (fun j hj => ⟨_, hloX1 j hj⟩)
      (fun j hj => ⟨_, hhiX1 j hj⟩) k hk
  have sY1 : ∀ k, k < 8 → ∃ v : BitVec 64, env₁ (feHN "Y1" k) = some ⟨.sword 64, v⟩ := by
    intro k hk
    rw [kY1 k hk]
    exact slots_of_halves (fe := "Y1") (fun j hj => ⟨_, hloY1 j hj⟩)
      (fun j hj => ⟨_, hhiY1 j hj⟩) k hk
  have sZ1 : ∀ k, k < 8 → ∃ v : BitVec 64, env₁ (feHN "Z1" k) = some ⟨.sword 64, v⟩ := by
    intro k hk
    rw [kZ1 k hk]
    exact slots_of_halves (fe := "Z1") (fun j hj => ⟨_, hloZ1 j hj⟩)
      (fun j hj => ⟨_, hhiZ1 j hj⟩) k hk
  have sX2 : ∀ k, k < 8 → ∃ v : BitVec 64, env₁ (feHN "X2" k) = some ⟨.sword 64, v⟩ := by
    intro k hk
    rw [kX2 k hk]
    exact slots_of_halves (fe := "X2") (fun j hj => ⟨_, hloX2 j hj⟩)
      (fun j hj => ⟨_, hhiX2 j hj⟩) k hk
  have sY2 : ∀ k, k < 8 → ∃ v : BitVec 64, env₁ (feHN "Y2" k) = some ⟨.sword 64, v⟩ := by
    intro k hk
    rw [kY2 k hk]
    exact slots_of_halves (fe := "Y2") (fun j hj => ⟨_, hloY2 j hj⟩)
      (fun j hj => ⟨_, hhiY2 j hj⟩) k hk
  have sZ2 : ∀ k, k < 8 → ∃ v : BitVec 64, env₁ (feHN "Z2" k) = some ⟨.sword 64, v⟩ :=
    slots_of_halves (fe := "Z2") (fun j hj => ⟨_, hloZ2 j hj⟩) (fun j hj => ⟨_, hhiZ2 j hj⟩)
  rintro x (rfl | rfl | rfl | ⟨i, hi, rfl⟩ | ⟨fe, hfe, k, hk, rfl⟩)
  · exact ⟨notTmp_ZZ, _, hCV8.zz⟩
  · exact ⟨notTmp_CC0, _, hCV8.lo⟩
  · exact ⟨notTmp_CC1, _, hCV8.hi⟩
  · refine ⟨namesClean_plNames i, ?_⟩
    rw [show plNames[i]! = s!"PL{i}" from by
      simp only [plNames]; exact map_range_getBang 8 _ i hi]
    exact ⟨_, hCV8.pl i hi⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hfe
    rcases hfe with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨namesClean_feH "X1" headOk_X1 k, by rw [feH_getBang hk]; exact sX1 k hk⟩
    · exact ⟨namesClean_feH "Y1" headOk_Y1 k, by rw [feH_getBang hk]; exact sY1 k hk⟩
    · exact ⟨namesClean_feH "Z1" headOk_Z1 k, by rw [feH_getBang hk]; exact sZ1 k hk⟩
    · exact ⟨namesClean_feH "X2" headOk_X2 k, by rw [feH_getBang hk]; exact sX2 k hk⟩
    · exact ⟨namesClean_feH "Y2" headOk_Y2 k, by rw [feH_getBang hk]; exact sY2 k hk⟩
    · exact ⟨namesClean_feH "Z2" headOk_Z2 k, by rw [feH_getBang hk]; exact sZ2 k hk⟩

/-- **The `jacAdd` body runs to completion.** -/
theorem jacAddBody_runs {n : Nat} {env : SEnvScalar} {a1 a2 : Fin n → BitVec 64}
    {b : Fin 12 → BitVec 64} {X1 Y1 Z1 X2 Y2 Z2 : Nat}
    (hE : AddPrologueEntry env a1 a2 X1 Y1 Z1 X2 Y2 Z2)
    (hout : env "out" = some ⟨.memref 12, b⟩) :
    ∃ env', semScalar jacAddBody env = some env' := by
  obtain ⟨E1, hs1, -, -, -, -⟩ := jacAddPrologue_run env a1 a2 X1 Y1 Z1 X2 Y2 Z2 hE
  obtain ⟨hsc1, -, hFI1, ho1⟩ :=
    jacAddPrologue_value env E1 a1 a2 X1 Y1 Z1 X2 Y2 Z2 hE hs1
  obtain ⟨E2, hs2, -, hW2⟩ :=
    jacAddSchedule_runs E1 (jacAddPrologue_bound hE.frame1 hE.frame2 hs1)
  have hb2 : E2 "out" = some ⟨.memref 12, b⟩ := by
    rw [jacAddSchedule_out hs2, ho1]
    exact hout
  have hix2 : ∀ i, i < 12 → E2 s!"ix{i}" = some ⟨.sword 64, BitVec.ofNat 64 i⟩ := by
    intro i hi
    rw [jacAddSchedule_ix i hi hs2]
    exact hFI1.idx i hi
  have hslots : ∀ fe : String,
      fe ∈ addOuts ["X1", "Y1", "Z1", "X2", "Y2", "Z2"] jacAddSchedule →
      SlotsBound E2 fe := by
    intro fe hfe k hk
    have hb := hW2 _ (brickBound_feH hfe k (by simpa [feH] using hk))
    rw [feH_getBang hk] at hb
    exact hb.2
  obtain ⟨env'', -, hsem3, -, -⟩ :=
    pointOpEpilogue_cells (jacAddSchedule_waist_scope E1 E2 hsc1 hs2) hb2 hix2
      (slotsBound_reads (hslots "Xp" (by decide)))
      (slotsBound_reads (hslots "Yp" (by decide)))
      (slotsBound_reads (hslots "Zp" (by decide)))
  refine ⟨env'', ?_⟩
  rw [jacAddBody_split, semScalar_seqAll_append, hs1, Option.bind_some,
    semScalar_seqAll_append, hs2, Option.bind_some]
  exact hsem3

/-- **The `jacAdd` body's output frame, unconditionally.** The existential form
    of `Secp256k1PointOpAddVertical.jacAddBody_cells`. -/
theorem jacAddBody_cells_total {n : Nat} {env : SEnvScalar} {a1 a2 : Fin n → BitVec 64}
    {b : Fin 12 → BitVec 64} {X1 Y1 Z1 X2 Y2 Z2 : Nat}
    (hE : AddPrologueEntry env a1 a2 X1 Y1 Z1 X2 Y2 Z2)
    (hout : env "out" = some ⟨.memref 12, b⟩) :
    ∃ (env' : SEnvScalar) (fr : Fin 12 → BitVec 64),
      semScalar jacAddBody env = some env'
        ∧ env' "out" = some ⟨.memref 12, fr⟩
        ∧ ∀ m : Fin 12, (fr m).toNat
            = (pointCells (jacAddSpec X1 Y1 Z1 X2 Y2 Z2)).getD m.val 0 := by
  obtain ⟨env', hrun⟩ := jacAddBody_runs hE hout
  obtain ⟨fr, hfr, hcells⟩ := jacAddBody_cells hE hout hrun
  exact ⟨env', fr, hrun, hfr, hcells⟩

end CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpTotal
