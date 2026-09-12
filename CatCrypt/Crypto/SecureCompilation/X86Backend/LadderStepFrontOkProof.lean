/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.LadderStepCovered
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
public import CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpTotal

/-!
# The framed secp256k1 ladder step satisfies the front-success gate

`LadderTripFrontSpec.LadderStepFrontOk` is the gate
`(frontLoopBodyJ ladderVMBody "F" ladderStepFramed).isSome`. The totality
module `TranslateDialectTotality` reduces such a gate to a derivation of the
reads-bound judgment `TransTotal σ₀ ladderStepFramed σ'` whose exit map binds
the frame accumulator `F` at the 256-cell memref type. This module supplies the
derivation, generator-level: no emitted command list is reduced.

The walk threads name-to-type maps of one shape only: `nameTysOf C` claims the
frame `F` at `.memref 256` and every name of a set `C` at `.sword 64`. Every
scalar bind in the ladder-step generators is at `.sword 64`, every frame load
binds its destination at `.sword 64`, and every frame store rebinds `F` at
`.memref 256`, so the shape is preserved along the whole step and the σ-walk
becomes the name-set walk `TransFrom`, mirroring the block-run triple
`Secp256k1PointOpTotal.RunsFrom`: an entry set of names the commands read, an
exit set of names they bind, composition over `++`, and the `Id`-monad loop
invariants of the `genMul` / `genAdd` / `genSub` builders.

## Main results

* `Long2` / `BindOk` / `NameOk` / `nameTysOf` and its update laws — the
  ladder-shaped name-to-type maps and their closure under the front's bindings.
* `TransSteps` / `transSteps_seqAll` — the list form of `TransTotal` and its
  reassociation onto `seqAll`.
* `TransFrom` and its combinators (`transFrom_append`, `transFrom_trans`,
  `transFrom_widen`, `transFrom_setExpr`, `transFrom_arrLoad1`,
  `transFrom_arrStore1`, `transFrom_mapRange`, `transFrom_forInRange`,
  `transFrom_chunkList`) — the reads-bound walk over command lists.
* `genAdd_trans` / `genSub_trans` / `genMul_trans` / `genFold_trans` — the limb
  builders emit reads-bound commands from a bound operand set.
* `feMulHalves_trans` / `feAddHalves_trans` / `feSubHalves_trans` — the three
  field bricks emit reads-bound commands from a bound operand set.
* `transFrom_idxCells` / `transFrom_constInit` / `transFrom_loadField` /
  `transFrom_storeRange` / `transFrom_pre` / `transFrom_framedAssemble` — the
  frame-relative gadgets a brick is assembled from.
* `SelfWalk`, `selfWalk_emitFOpFramed`, `selfWalk_emitSelectFramed`,
  `selfWalk_mapIdxFlatten`, `selfWalk_selectTrip` — a framed brick binds every
  name it reads, so it walks from the frame alone, and such walks compose.
* `transFrom_ladderBitFetch` — the per-trip key-bit fetch is reads-bound from
  the loop index.
* `ladderStepFramed_transTotal` — the whole framed ladder step carries a
  `TransTotal` derivation from the loop-body entry map, with the exit map
  claiming `F` at `.memref 256`.
* `ladderStepFrontOk` — `LadderStepFrontOk` holds: the scalar rolled-loop
  front accepts the framed ladder step.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.LadderStepFrontOkProof

open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar (isTmpName)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
  (NameTys TransTotal SrcTys VmApprox BoundAt boundAt_bind_self boundAt_bind_of_ne
   frontLoopBodyJ_total)
open CatCrypt.Crypto.SecureCompilation.Secp256k1FeMulFront
  (seqAll sv genMul genAdd genSub genFold mask32 pl32 cc0 cc1)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFront
  (FOp constInit loadField feH plNames feMulHalves feAddHalves feSubHalves
   jacDblSchedule jacAddSchedule)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontCovered
  (HeadOk forIn_range_inv arrayToList_getBang mask32_lt lt64_32 lt64_zero
   notTmp_of_len notTmp_empty notTmp_ZZ notTmp_CC0 notTmp_CC1 headOk_PL
   AddS SubS MulI MulO genAddStep genAddRun genAdd_eq genSubStep genSubRun genSub_eq
   genMulInnerStep genMulOuterStep genMulRun genMul_eq NamesClean namesClean_plNames
   pl32_mem_lt getD_lt_of_mem_lt)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpTotal
  (ReadsFrom readsFrom_var readsFrom_lit readsFrom_add readsFrom_sub readsFrom_mul
   readsFrom_and readsFrom_xor readsFrom_shl readsFrom_shr readsFrom_mono
   SrcSet srcSet_or AllIn allIn_mono allIn_pair allIn_single allIn_append allIn_take
   allIn_drop map_range_getBang forIn_range_inv_lt forIn_range_inv_tail
   arraySet_inv_lt size_set! getD_of_lt
   genAdd_len genSub_len genMul_len genFold_len_ge genFold_cases
   feMulHalves_len feAddHalves_len feSubHalves_len)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramed
  (idxCells storeFieldTo emitFOpFramed brickFn)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFramedValue
  (Bbody bbody_src oh_bridge)
open CatCrypt.Crypto.SecureCompilation.Secp256k1PointOpFrontFramedLadder
  (emitSelectFramed selBody selectTrip ladderBitFetch ladderStepFramed
   ladderFrameCells slotLadDbl slotLadAdd slotLadSel ladderBitBase notTmp_ladkeybit)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LadderTripFrontSpec
  (ladderΓbody ladderVMBody LadderStepFrontOk)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LadderStepCovered
  (slotLadDbl_lt slotLadAdd_lt)

/-! ## 1. Names that are never the frame name -/

/-- A name of length at least two — in particular never the one-character frame
    name `"F"`. -/
def Long2 (s : String) : Prop := 2 ≤ s.length

theorem Long2.ne_frame {s : String} (h : Long2 s) : s ≠ "F" := by
  intro hs
  have h1 : (2 : Nat) ≤ "F".length := hs ▸ h
  have h2 : "F".length = 1 := rfl
  omega

theorem Long2.append {s : String} (h : Long2 s) (u : String) : Long2 (s ++ u) := by
  unfold Long2 at *
  rw [String.length_append]
  omega

/-- A name that a front binding may target: outside the fresh-temp namespace and
    distinct from the frame name. -/
def BindOk (x : String) : Prop := ¬ isTmpName x ∧ x ≠ "F"

/-- A head-clean name of length at least two: the shape every private name of
    the ladder-step generators has. -/
structure NameOk (s : String) : Prop where
  head : HeadOk s
  long : Long2 s

theorem NameOk.append {s : String} (h : NameOk s) (u : String) : NameOk (s ++ u) :=
  ⟨h.head.append u, h.long.append u⟩

theorem NameOk.bindOk {s : String} (h : NameOk s) : BindOk s :=
  ⟨h.head.notTmp, h.long.ne_frame⟩

theorem NameOk.notTmp {s : String} (h : NameOk s) : ¬ isTmpName s := h.head.notTmp

/-- A name-list all of whose entries a front binding may target. -/
def BindOkList (l : List String) : Prop := ∀ k : Nat, k < l.length → BindOk (l[k]!)

/-! ## 2. Ladder-shaped name-to-type maps -/

open Classical in
/-- The name-to-type map claiming the frame `F` at the 256-cell memref type and
    every name of `C` at 64-bit word type. -/
noncomputable def nameTysOf (C : String → Prop) : NameTys :=
  fun x => if x = "F" then some (.memref 256) else if C x then some (.sword 64) else none

theorem nameTysOf_frame (C : String → Prop) : nameTysOf C "F" = some (.memref 256) := by
  simp [nameTysOf]

theorem nameTysOf_mem {C : String → Prop} {x : String} (hx : C x) (hxF : x ≠ "F") :
    nameTysOf C x = some (.sword 64) := by
  simp [nameTysOf, hxF, hx]

/-- A map of ladder shape claims no fresh temporary when its word set does not. -/
theorem srcTys_nameTysOf {C : String → Prop} (hC : SrcSet C) : SrcTys (nameTysOf C) := by
  intro x hx
  by_cases hxF : x = "F"
  · exact hxF ▸ notTmp_of_len _ (by decide)
  · by_cases hxC : C x
    · exact hC x hxC
    · simp [nameTysOf, hxF, hxC] at hx

/-- A word binding away from the frame name grows the word set. -/
theorem nameTysOf_upd_word {C : String → Prop} {x : String} (hxF : x ≠ "F") :
    (nameTysOf C).upd x (.sword 64) = nameTysOf (fun y => C y ∨ y = x) := by
  funext y
  simp only [CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality.NameTys.upd,
    nameTysOf]
  by_cases hyF : y = "F"
  · have hFx : ¬ ("F" = x) := fun h => hxF h.symm
    simp [hyF, hFx]
  · by_cases hyx : y = x
    · subst hyx
      simp [hyF]
    · by_cases hyC : C y <;> simp [hyx, hyF, hyC]

/-- Rebinding the frame at its own type fixes the map. -/
theorem nameTysOf_upd_frame (C : String → Prop) :
    (nameTysOf C).upd "F" (.memref 256) = nameTysOf C := by
  funext y
  simp only [CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality.NameTys.upd,
    nameTysOf]
  by_cases hy : y = "F" <;> simp [hy]

/-! ## 3. The judgment on command lists -/

/-- The reads-bound judgment threaded through a command list: each command
    carries `TransTotal` from the running map, which its bindings update. -/
inductive TransSteps : NameTys → List LowCT → NameTys → Prop
  | nil (σ : NameTys) : TransSteps σ [] σ
  | cons {σ σ₁ σ₂ : NameTys} {c : LowCT} {l : List LowCT} :
      TransTotal σ c σ₁ → TransSteps σ₁ l σ₂ → TransSteps σ (c :: l) σ₂

theorem TransSteps.append {σ₂ : NameTys} :
    ∀ {l₁ : List LowCT} {σ σ₁ : NameTys} {l₂ : List LowCT},
      TransSteps σ l₁ σ₁ → TransSteps σ₁ l₂ σ₂ → TransSteps σ (l₁ ++ l₂) σ₂ := by
  intro l₁
  induction l₁ with
  | nil =>
      intro σ σ₁ l₂ h₁ h₂
      cases h₁
      exact h₂
  | cons c cs ih =>
      intro σ σ₁ l₂ h₁ h₂
      cases h₁ with
      | cons hc hcs => exact .cons hc (ih hcs h₂)

/-- A `TransSteps` walk of a list is a `TransTotal` derivation of its `seqAll`
    sequencing. -/
theorem transSteps_seqAll : ∀ {l : List LowCT} {σ σ' : NameTys},
    TransSteps σ l σ' → TransTotal σ (seqAll l) σ'
  | [], _, _, h => by cases h; exact .rSkip
  | [_], _, _, h => by
      cases h with
      | cons hc ht => cases ht; exact hc
  | _ :: _ :: _, _, _, h => by
      cases h with
      | cons hc ht => exact .rSeq hc (transSteps_seqAll ht)

/-! ## 4. The reads-bound walk

`TransFrom B W l` mirrors `Secp256k1PointOpTotal.RunsFrom` at the judgment
level: from any temporary-free word set `C` extending `B` and avoiding the
frame name, the list carries a `TransSteps` walk from `nameTysOf C` to a map of
the same shape whose word set extends `C` and binds `W`. -/

/-- The reads-bound walk triple over ladder-shaped maps. -/
def TransFrom (B W : String → Prop) (l : List LowCT) : Prop :=
  ∀ C : String → Prop, SrcSet C → ¬ C "F" → (∀ x, B x → C x) →
    ∃ D : String → Prop, SrcSet D ∧ ¬ D "F" ∧ (∀ x, C x → D x) ∧ (∀ x, W x → D x) ∧
      TransSteps (nameTysOf C) l (nameTysOf D)

theorem transFrom_nil (B : String → Prop) : TransFrom B B [] :=
  fun C hs hF hb => ⟨C, hs, hF, fun _ h => h, hb, .nil _⟩

/-- Strengthening the entry set and weakening the exit set. -/
theorem transFrom_mono {B B₂ W W₂ : String → Prop} {l : List LowCT}
    (h : TransFrom B W l) (hB : ∀ x, B x → B₂ x) (hW : ∀ x, W₂ x → W x) :
    TransFrom B₂ W₂ l := by
  intro C hs hF hb
  obtain ⟨D, hsD, hDF, hCD, hWD, hts⟩ := h C hs hF (fun x hx => hb x (hB x hx))
  exact ⟨D, hsD, hDF, hCD, fun x hx => hWD x (hW x hx), hts⟩

/-- The entry set is still bound at the exit. -/
theorem transFrom_addPre {B W : String → Prop} {l : List LowCT} (h : TransFrom B W l) :
    TransFrom B (fun x => W x ∨ B x) l := by
  intro C hs hF hb
  obtain ⟨D, hsD, hDF, hCD, hWD, hts⟩ := h C hs hF hb
  exact ⟨D, hsD, hDF, hCD,
    fun x hx => hx.elim (hWD x) (fun hbx => hCD x (hb x hbx)), hts⟩

/-- **Two blocks in sequence.** The second block's entry set may draw on the
    first block's exit set. -/
theorem transFrom_append {B W₁ B' W₂ : String → Prop} {l₁ l₂ : List LowCT}
    (h₁ : TransFrom B W₁ l₁) (h₂ : TransFrom B' W₂ l₂)
    (hsub : ∀ x, B' x → B x ∨ W₁ x) :
    TransFrom B (fun x => W₁ x ∨ W₂ x) (l₁ ++ l₂) := by
  intro C hs hF hb
  obtain ⟨D₁, hs₁, hF₁, hCD₁, hW₁, hts₁⟩ := h₁ C hs hF hb
  obtain ⟨D₂, hs₂, hF₂, hD₁₂, hW₂, hts₂⟩ :=
    h₂ D₁ hs₁ hF₁ (fun x hx => (hsub x hx).elim (fun h => hCD₁ x (hb x h)) (hW₁ x))
  exact ⟨D₂, hs₂, hF₂, fun x hx => hD₁₂ x (hCD₁ x hx),
    fun x hx => hx.elim (fun h => hD₁₂ x (hW₁ x h)) (hW₂ x), hts₁.append hts₂⟩

/-- Two blocks in sequence, the second entered at the first's exit set. -/
theorem transFrom_trans {B W₁ W₂ : String → Prop} {l₁ l₂ : List LowCT}
    (h₁ : TransFrom B W₁ l₁) (h₂ : TransFrom W₁ W₂ l₂) :
    TransFrom B W₂ (l₁ ++ l₂) :=
  transFrom_mono (transFrom_append h₁ h₂ (fun _ hx => Or.inr hx)) (fun _ h => h)
    (fun _ hx => Or.inr hx)

/-- A single command in front of a block. -/
theorem transFrom_cons {B W₁ W₂ : String → Prop} {c : LowCT} {l : List LowCT}
    (h₁ : TransFrom B W₁ [c]) (h₂ : TransFrom (fun y => B y ∨ W₁ y) W₂ l) :
    TransFrom B (fun y => W₁ y ∨ W₂ y) (c :: l) :=
  transFrom_append h₁ h₂ (fun _ hx => hx)

/-- **One scalar assignment.** The bound name is outside the fresh-temp
    namespace and away from the frame name; the expression reads from the entry
    set. -/
theorem transFrom_setExpr {R : String → Prop} {x : String} {e : SExpr}
    (hx : BindOk x) (hrd : ReadsFrom R e) :
    TransFrom R (fun y => y = x) [LowCT.RScalarSetExpr x e] := by
  obtain ⟨hnt, hxF⟩ := hx
  intro C hs hF hb
  refine ⟨fun y => C y ∨ y = x, srcSet_or hs hnt, ?_, fun y hy => Or.inl hy,
    fun y hy => Or.inr hy, ?_⟩
  · rintro (h | h)
    · exact hF h
    · exact hxF h.symm
  · have harm : TransTotal (nameTysOf C) (.RScalarSetExpr x e)
        ((nameTysOf C).upd x (.sword 64)) :=
      TransTotal.rScalarSetExpr x e hnt hrd.1 (fun y hy =>
        nameTysOf_mem (hb y (hrd.2 y hy))
          (fun hyF => hF (hyF ▸ hb y (hrd.2 y hy))))
    exact nameTysOf_upd_word hxF ▸ TransSteps.cons harm (.nil _)

/-- **One dynamic-index frame load** into a `u64` destination: the index must be
    bound; the destination is bound at `.sword 64`. -/
theorem transFrom_arrLoad1 {d ix : String} (fw : Nat) (hd : BindOk d) :
    TransFrom (fun y => y = ix) (fun y => y = d)
      [LowCT.RArrLoad ⟨d, .TU64⟩ ⟨"F", .TBytes fw⟩ ix] := by
  obtain ⟨hnt, hdF⟩ := hd
  intro C hs hF hb
  refine ⟨fun y => C y ∨ y = d, srcSet_or hs hnt, ?_, fun y hy => Or.inl hy,
    fun y hy => Or.inr hy, ?_⟩
  · rintro (h | h)
    · exact hF h
    · exact hdF h.symm
  · have hix : (nameTysOf C ix).isSome := by
      rw [nameTysOf_mem (hb ix rfl) (fun h => hF (h ▸ hb ix rfl))]
      rfl
    have harm : TransTotal (nameTysOf C) (.RArrLoad ⟨d, .TU64⟩ ⟨"F", .TBytes fw⟩ ix)
        ((nameTysOf C).upd d (.sword 64)) :=
      TransTotal.rArrLoad ⟨d, .TU64⟩ ⟨"F", .TBytes fw⟩ ix hnt
        (by rw [nameTysOf_frame]; rfl) hix
    exact nameTysOf_upd_word hdF ▸ TransSteps.cons harm (.nil _)

/-- **One dynamic-index frame store** of a bound `u64` word at a bound index:
    the store rebinds the frame at its own type, so the word set is unchanged. -/
theorem transFrom_arrStore1 {ix s : String} (fw : Nat)
    (henc : encodeTy (.TBytes fw) = CryptoTy.memref 256) :
    TransFrom (fun y => y = ix ∨ y = s) (fun _ => False)
      [LowCT.RArrStore ⟨"F", .TBytes fw⟩ ix ⟨s, .TU64⟩] := by
  intro C hs hF hb
  refine ⟨C, hs, hF, fun _ h => h, fun _ h => h.elim, ?_⟩
  have hix : (nameTysOf C ix).isSome := by
    rw [nameTysOf_mem (hb ix (Or.inl rfl)) (fun h => hF (h ▸ hb ix (Or.inl rfl)))]
    rfl
  have hsrc : (nameTysOf C s).isSome := by
    rw [nameTysOf_mem (hb s (Or.inr rfl)) (fun h => hF (h ▸ hb s (Or.inr rfl)))]
    rfl
  have harm : TransTotal (nameTysOf C) (.RArrStore ⟨"F", .TBytes fw⟩ ix ⟨s, .TU64⟩)
      ((nameTysOf C).upd "F" (encodeTy (.TBytes fw))) :=
    TransTotal.rArrStore ⟨"F", .TBytes fw⟩ ix ⟨s, .TU64⟩
      (notTmp_of_len "F" (by decide)) (by rw [nameTysOf_frame]; rfl) hsrc hix
  rw [henc, nameTysOf_upd_frame] at harm
  exact TransSteps.cons harm (.nil _)

/-- **A block extended by one scalar assignment** whose reads lie in the
    block's exit set. -/
theorem transFrom_snoc {B W : String → Prop} {l : List LowCT} {x : String} {e : SExpr}
    (h : TransFrom B W l) (hx : BindOk x) (hrd : ReadsFrom W e) :
    TransFrom B (fun y => W y ∨ y = x) (l ++ [LowCT.RScalarSetExpr x e]) :=
  transFrom_append h
    (transFrom_setExpr (R := fun s => B s ∨ W s) hx
      (readsFrom_mono hrd (fun _ hx => Or.inr hx)))
    (fun _ hs => hs)

/-- A block extended by two scalar assignments. -/
theorem transFrom_snoc2 {B W : String → Prop} {l : List LowCT} {x₁ x₂ : String}
    {e₁ e₂ : SExpr} (h : TransFrom B W l) (h₁ : BindOk x₁) (h₂ : BindOk x₂)
    (r₁ : ReadsFrom W e₁)
    (r₂ : ReadsFrom (fun y => W y ∨ y = x₁) e₂) :
    TransFrom B (fun y => (W y ∨ y = x₁) ∨ y = x₂)
      (l ++ [LowCT.RScalarSetExpr x₁ e₁, LowCT.RScalarSetExpr x₂ e₂]) := by
  have hlist : l ++ [LowCT.RScalarSetExpr x₁ e₁, LowCT.RScalarSetExpr x₂ e₂]
      = (l ++ [LowCT.RScalarSetExpr x₁ e₁]) ++ [LowCT.RScalarSetExpr x₂ e₂] := by simp
  rw [hlist]
  exact transFrom_snoc (transFrom_snoc h h₁ r₁) h₂ r₂

/-- A block extended by three scalar assignments. -/
theorem transFrom_snoc3 {B W : String → Prop} {l : List LowCT} {x₁ x₂ x₃ : String}
    {e₁ e₂ e₃ : SExpr} (h : TransFrom B W l) (h₁ : BindOk x₁)
    (h₂ : BindOk x₂) (h₃ : BindOk x₃) (r₁ : ReadsFrom W e₁)
    (r₂ : ReadsFrom (fun y => W y ∨ y = x₁) e₂)
    (r₃ : ReadsFrom (fun y => (W y ∨ y = x₁) ∨ y = x₂) e₃) :
    TransFrom B (fun y => ((W y ∨ y = x₁) ∨ y = x₂) ∨ y = x₃)
      (l ++ [LowCT.RScalarSetExpr x₁ e₁, LowCT.RScalarSetExpr x₂ e₂,
             LowCT.RScalarSetExpr x₃ e₃]) := by
  have hlist : l ++ [LowCT.RScalarSetExpr x₁ e₁, LowCT.RScalarSetExpr x₂ e₂,
        LowCT.RScalarSetExpr x₃ e₃]
      = ((l ++ [LowCT.RScalarSetExpr x₁ e₁]) ++ [LowCT.RScalarSetExpr x₂ e₂])
        ++ [LowCT.RScalarSetExpr x₃ e₃] := by simp
  rw [hlist]
  exact transFrom_snoc (transFrom_snoc (transFrom_snoc h h₁ r₁) h₂ r₂) h₃ r₃

/-- **A block extended by a `List.range`-indexed family of scalar
    assignments**, each reading only names the block already binds. -/
theorem transFrom_mapRange {B W : String → Prop} {l : List LowCT}
    (nm : Nat → String) (ex : Nat → SExpr) (h : TransFrom B W l) :
    ∀ n : Nat, (∀ i, i < n → BindOk (nm i)) →
      (∀ i, i < n → ReadsFrom W (ex i)) →
      TransFrom B (fun y => W y ∨ ∃ i, i < n ∧ y = nm i)
        (l ++ (List.range n).map (fun i => LowCT.RScalarSetExpr (nm i) (ex i))) := by
  intro n
  induction n with
  | zero =>
      intro _ _
      have hl : l ++ (List.range 0).map (fun i => LowCT.RScalarSetExpr (nm i) (ex i))
          = l := by simp
      rw [hl]
      refine transFrom_mono h (fun _ hx => hx) (fun x hx => ?_)
      rcases hx with hx | ⟨i, hi, -⟩
      · exact hx
      · exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      intro hnt hrd
      have hprev := ih (fun i hi => hnt i (by omega)) (fun i hi => hrd i (by omega))
      have hs := transFrom_snoc hprev (hnt n (by omega))
        (readsFrom_mono (hrd n (by omega)) (fun x hx => Or.inl hx))
      have hl : l ++ (List.range (n + 1)).map (fun i => LowCT.RScalarSetExpr (nm i) (ex i))
          = (l ++ (List.range n).map (fun i => LowCT.RScalarSetExpr (nm i) (ex i)))
            ++ [LowCT.RScalarSetExpr (nm n) (ex n)] := by
        rw [List.range_succ, List.map_append, List.append_assoc]
        simp
      rw [hl]
      refine transFrom_mono hs (fun _ hx => hx) (fun x hx => ?_)
      rcases hx with hx | ⟨i, hi, rfl⟩
      · exact Or.inl (Or.inl hx)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact Or.inl (Or.inr ⟨i, hlt, rfl⟩)
        · exact Or.inr rfl

/-- The loop invariant of `transFrom_forInRange`: an exit set extending `W₀`
    under which the commands emitted so far walk and every already-processed
    trip's destination is bound. -/
abbrev TLoopInv (B W₀ : String → Prop) (nm : Nat → String) (n : Nat)
    (rem : List Nat) (cmds : List LowCT) : Prop :=
  ∃ W : String → Prop, SrcSet W ∧ (∀ x, W₀ x → W x)
    ∧ (∀ i, i < n → i ∉ rem → W (nm i)) ∧ TransFrom B W cmds

/-- **A block extended by one scalar assignment per trip of a `[:n]` loop.**
    Each trip appends a command binding `nm a` and reading only names the block
    already binds; the exit binds the block's exit set and every `nm i`. -/
theorem transFrom_forInRange {B W₀ : String → Prop} (nm : Nat → String) (n : Nat)
    (f : Nat → List LowCT → Id (ForInStep (List LowCT))) (base : List LowCT)
    (h0 : TransFrom B W₀ base) (hS : SrcSet W₀)
    (hnt : ∀ i, i < n → BindOk (nm i))
    (hbody : ∀ a, a < n → ∀ (W : String → Prop) (l : List LowCT), SrcSet W →
        (∀ x, W₀ x → W x) → TransFrom B W l →
        ∃ l', f a l = ForInStep.yield l' ∧ TransFrom B (fun y => W y ∨ y = nm a) l') :
    TransFrom B (fun y => W₀ y ∨ ∃ i, i < n ∧ y = nm i)
      (forIn [:n] base f : Id (List LowCT)) := by
  have hstep : ∀ a, a < n → ∀ (rem : List Nat) (s s' : List LowCT),
      TLoopInv B W₀ nm n (a :: rem) s → f a s = ForInStep.yield s' →
      TLoopInv B W₀ nm n rem s' := by
    intro a ha rem s s' hs hy
    obtain ⟨W, hWs, hWb, hWn, hWr⟩ := hs
    obtain ⟨l', hfl, hrun⟩ := hbody a ha W s hWs hWb hWr
    have hs'eq : s' = l' := by
      rw [hfl] at hy
      injection hy with h
      exact h.symm
    subst hs'eq
    refine ⟨fun y => W y ∨ y = nm a, srcSet_or hWs (hnt a ha).1,
      fun x hx => Or.inl (hWb x hx), ?_, hrun⟩
    intro i hi hmem
    by_cases hia : i = a
    · exact Or.inr (by rw [hia])
    · exact Or.inl (hWn i hi
        (fun hc => (List.mem_cons.mp hc).elim hia (fun h => hmem h)))
  have hdone : ∀ a, a < n → ∀ (rem : List Nat) (s s' : List LowCT),
      TLoopInv B W₀ nm n (a :: rem) s → f a s = ForInStep.done s' →
      TLoopInv B W₀ nm n [] s' := by
    intro a ha rem s s' hs hy
    obtain ⟨W, hWs, hWb, -, hWr⟩ := hs
    obtain ⟨l', hfl, -⟩ := hbody a ha W s hWs hWb hWr
    rw [hfl] at hy
    exact absurd hy (by simp)
  obtain ⟨W, hWs', hWb, hWn, hWr⟩ :=
    forIn_range_inv_tail (TLoopInv B W₀ nm n) n f base
      ⟨W₀, hS, fun _ h => h, fun i hi hmem => absurd (List.mem_range.mpr hi) hmem, h0⟩
      hstep hdone
  refine transFrom_mono hWr (fun _ h => h) (fun x hx => ?_)
  rcases hx with h | ⟨i, hi, rfl⟩
  · exact hWb x h
  · exact hWn i hi (by simp)

/-! ## 5. The limb builders

`genAdd` / `genSub` / `genMul` are `Id`-monad loops over a mutable carry, the
command list and the result array. The loop invariant carries a word set
extending the entry set, under which the commands emitted so far walk and the
carry and every result slot are bound. -/

/-- The loop invariant of `genAdd`: a word set extending the entry set, under
    which the emitted commands walk and the carry and result slots are bound. -/
def QAddT (B : String → Prop) (n : Nat) : AddS → Prop := fun r =>
  ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x) ∧ TransFrom B W r.snd.fst
    ∧ W r.fst ∧ r.snd.snd.size = n + 1 ∧ (∀ k, k < n + 1 → W (r.snd.snd[k]!))

/-- **`genAdd` emits reads-bound commands from a bound operand set.** -/
theorem genAdd_trans {B : String → Prop} (zero : String) (aN bN : List String)
    (pfx : String) (hp : NameOk pfx) (hz : B zero) (hBs : SrcSet B)
    (hA : AllIn B aN) (hBn : AllIn B bN) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x)
      ∧ TransFrom B W (genAdd zero aN bN pfx).1
      ∧ AllIn W (genAdd zero aN bN pfx).2 := by
  have key : QAddT B (max aN.length bN.length) (genAddRun zero aN bN pfx) := by
    unfold genAddRun
    refine forIn_range_inv (QAddT B (max aN.length bN.length)) _ (genAddStep zero aN bN pfx) _
      ⟨B, hBs, fun _ h => h, transFrom_nil B, hz, by simp, fun k hk => by
          rw [getElem!_pos _ k (by simpa using hk)]
          simpa using hz⟩ ?_ ?_
    · intro i s s' hs hy
      simp only [genAddStep] at hy
      injection hy with hy
      subst hy
      obtain ⟨W, hWs, hWb, hWr, hWc, hsz, hres⟩ := hs
      have htn : BindOk (s!"{pfx}t{i}") := ((hp.append _).append _).bindOk
      have hsn : BindOk (s!"{pfx}s{i}") := ((hp.append _).append _).bindOk
      have hkn : BindOk (s!"{pfx}k{i}") := ((hp.append _).append _).bindOk
      have hai : W (aN.getD i zero) :=
        getD_of_lt (hWb zero hz) (fun k hk => hWb _ (hA k hk)) i
      have hbi : W (bN.getD i zero) :=
        getD_of_lt (hWb zero hz) (fun k hk => hWb _ (hBn k hk)) i
      refine ⟨fun y => ((W y ∨ y = s!"{pfx}t{i}") ∨ y = s!"{pfx}s{i}") ∨ y = s!"{pfx}k{i}",
        srcSet_or (srcSet_or (srcSet_or hWs htn.1) hsn.1) hkn.1,
        fun x hx => Or.inl (Or.inl (Or.inl (hWb x hx))), ?_, Or.inr rfl, ?_, ?_⟩
      · refine transFrom_snoc (transFrom_snoc (transFrom_snoc hWr htn ?_) hsn ?_) hkn ?_
        · exact readsFrom_add (readsFrom_add (readsFrom_var (hWs _ hai) hai)
            (readsFrom_var (hWs _ hbi) hbi)) (readsFrom_var (hWs _ hWc) hWc)
        · exact readsFrom_and (readsFrom_var htn.1 (Or.inr rfl)) (readsFrom_lit mask32_lt)
        · exact readsFrom_shr (readsFrom_var htn.1 (Or.inl (Or.inr rfl)))
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

/-- The loop invariant of `genSub`: a word set extending the entry set, under
    which the emitted commands walk and the borrow and difference slots are
    bound. -/
def QSubT (B : String → Prop) (n : Nat) : SubS → Prop := fun r =>
  ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x) ∧ TransFrom B W r.snd.fst
    ∧ W r.fst ∧ r.snd.snd.size = n ∧ (∀ k, k < n → W (r.snd.snd[k]!))

/-- **`genSub` emits reads-bound commands from a bound operand set.** -/
theorem genSub_trans {B : String → Prop} (zero : String) (aN pN : List String)
    (pfx : String) (hp : NameOk pfx) (hz : B zero) (hBs : SrcSet B)
    (hA : AllIn B aN) (hP : AllIn B pN) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x)
      ∧ TransFrom B W (genSub zero aN pN pfx).1
      ∧ AllIn W (genSub zero aN pN pfx).2.1
      ∧ W (genSub zero aN pN pfx).2.2 := by
  have hbig : (4294967296 : Nat) < 2 ^ 64 := by norm_num
  have hone : (1 : Nat) < 2 ^ 64 := by norm_num
  have key : QSubT B aN.length (genSubRun zero aN pN pfx) := by
    unfold genSubRun
    refine forIn_range_inv_lt (QSubT B aN.length) _ (genSubStep zero aN pN pfx) _
      ⟨B, hBs, fun _ h => h, transFrom_nil B, hz, by simp, fun k hk => by
          rw [getElem!_pos _ k (by simpa using hk)]
          simpa using hz⟩ ?_ ?_
    · intro i hi s s' hs hy
      simp only [genSubStep] at hy
      injection hy with hy
      subst hy
      obtain ⟨W, hWs, hWb, hWr, hWc, hsz, hres⟩ := hs
      have htn : BindOk (s!"{pfx}t{i}") := ((hp.append _).append _).bindOk
      have hdn : BindOk (s!"{pfx}d{i}") := ((hp.append _).append _).bindOk
      have hhn : BindOk (s!"{pfx}h{i}") := ((hp.append _).append _).bindOk
      have hbn : BindOk (s!"{pfx}b{i}") := ((hp.append _).append _).bindOk
      have hai : W (aN[i]!) := hWb _ (hA i hi)
      have hpi : W (pN.getD i zero) :=
        getD_of_lt (hWb zero hz) (fun k hk => hWb _ (hP k hk)) i
      refine ⟨fun y => ((((W y ∨ y = s!"{pfx}t{i}") ∨ y = s!"{pfx}d{i}")
            ∨ y = s!"{pfx}h{i}") ∨ y = s!"{pfx}b{i}"),
        srcSet_or (srcSet_or (srcSet_or (srcSet_or hWs htn.1) hdn.1) hhn.1) hbn.1,
        fun x hx => Or.inl (Or.inl (Or.inl (Or.inl (hWb x hx)))), ?_, Or.inr rfl, ?_, ?_⟩
      · refine transFrom_snoc (transFrom_snoc (transFrom_snoc
          (transFrom_snoc hWr htn ?_) hdn ?_) hhn ?_) hbn ?_
        · exact readsFrom_sub (readsFrom_sub
            (readsFrom_add (readsFrom_var (hWs _ hai) hai) (readsFrom_lit hbig))
            (readsFrom_var (hWs _ hpi) hpi)) (readsFrom_var (hWs _ hWc) hWc)
        · exact readsFrom_and (readsFrom_var htn.1 (Or.inr rfl)) (readsFrom_lit mask32_lt)
        · exact readsFrom_shr (readsFrom_var htn.1 (Or.inl (Or.inr rfl)))
            (readsFrom_lit lt64_32)
        · exact readsFrom_sub (readsFrom_lit hone) (readsFrom_var hhn.1 (Or.inr rfl))
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

/-- The inner-loop invariant of `genMul`: the outer invariant together with the
    running column carry. -/
def QMulIT (B : String → Prop) (m : Nat) : MulI → Prop := fun r =>
  ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x) ∧ TransFrom B W r.snd.snd
    ∧ W r.snd.fst ∧ r.fst.size = m ∧ (∀ k, k < m → W (r.fst[k]!))

/-- The outer-loop invariant of `genMul`: a word set extending the entry set,
    under which the emitted commands walk and every column slot is bound. -/
def QMulOT (B : String → Prop) (m : Nat) : MulO → Prop := fun r =>
  ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x) ∧ TransFrom B W r.snd
    ∧ r.fst.size = m ∧ (∀ k, k < m → W (r.fst[k]!))

/-- **`genMul` emits reads-bound commands from a bound operand set.** -/
theorem genMul_trans {B : String → Prop} (zero : String) (aN bN : List String)
    (pfx : String) (hp : NameOk pfx) (hz : B zero) (hBs : SrcSet B)
    (hA : AllIn B aN) (hBn : AllIn B bN) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x)
      ∧ TransFrom B W (genMul zero aN bN pfx).1
      ∧ AllIn W (genMul zero aN bN pfx).2 := by
  set m := aN.length + bN.length with hm
  have hstepI : ∀ i, i < aN.length → ∀ j, j < bN.length → ∀ (s s' : MulI),
      QMulIT B m s → genMulInnerStep zero aN bN pfx i j s = ForInStep.yield s' →
        QMulIT B m s' := by
    intro i hi j hj s s' hs hy
    simp only [genMulInnerStep] at hy
    injection hy with hy
    subst hy
    obtain ⟨W, hWs, hWb, hWr, hWc, hsz, hres⟩ := hs
    have htn : BindOk (s!"{pfx}t{i}_{j}") :=
      ((((hp.append _).append _).append _).append _).bindOk
    have hpn : BindOk (s!"{pfx}p{i}_{j}") :=
      ((((hp.append _).append _).append _).append _).bindOk
    have hkn : BindOk (s!"{pfx}k{i}_{j}") :=
      ((((hp.append _).append _).append _).append _).bindOk
    have hai : W (aN[i]!) := hWb _ (hA i hi)
    have hbj : W (bN[j]!) := hWb _ (hBn j hj)
    have hacc : W (s.fst[i + j]!) := hres (i + j) (by omega)
    refine ⟨fun y => ((W y ∨ y = s!"{pfx}t{i}_{j}") ∨ y = s!"{pfx}p{i}_{j}")
          ∨ y = s!"{pfx}k{i}_{j}",
      srcSet_or (srcSet_or (srcSet_or hWs htn.1) hpn.1) hkn.1,
      fun x hx => Or.inl (Or.inl (Or.inl (hWb x hx))), ?_, Or.inr rfl, ?_, ?_⟩
    · refine transFrom_snoc (transFrom_snoc (transFrom_snoc hWr htn ?_) hpn ?_) hkn ?_
      · exact readsFrom_add (readsFrom_add
          (readsFrom_mul (readsFrom_var (hWs _ hai) hai) (readsFrom_var (hWs _ hbj) hbj))
          (readsFrom_var (hWs _ hacc) hacc)) (readsFrom_var (hWs _ hWc) hWc)
      · exact readsFrom_and (readsFrom_var htn.1 (Or.inr rfl)) (readsFrom_lit mask32_lt)
      · exact readsFrom_shr (readsFrom_var htn.1 (Or.inl (Or.inr rfl)))
          (readsFrom_lit lt64_32)
    · rw [size_set!]; exact hsz
    · intro k hk
      exact arraySet_inv_lt s.fst (i + j) s!"{pfx}p{i}_{j}"
        (fun y => ((W y ∨ y = s!"{pfx}t{i}_{j}") ∨ y = s!"{pfx}p{i}_{j}")
          ∨ y = s!"{pfx}k{i}_{j}")
        (fun l hl => Or.inl (Or.inl (Or.inl (hres l (by rw [hsz] at hl; exact hl)))))
        (Or.inl (Or.inr rfl)) k (by rw [hsz]; exact hk)
  have key : QMulOT B m (genMulRun zero aN bN pfx) := by
    unfold genMulRun
    refine forIn_range_inv_lt (QMulOT B m) _ (genMulOuterStep zero aN bN pfx) _
      ⟨B, hBs, fun _ h => h, transFrom_nil B, by simp [hm], fun k hk => by
          rw [getElem!_pos _ k (by simp; omega)]
          simpa using hz⟩ ?_ ?_
    · intro i hi s s' hs hy
      simp only [genMulOuterStep] at hy
      injection hy with hy
      subst hy
      obtain ⟨W, hWs, hWb, hWr, hsz, hres⟩ := hs
      have hinit : QMulIT B m ⟨s.fst, zero, s.snd⟩ :=
        ⟨W, hWs, hWb, hWr, hWb zero hz, hsz, hres⟩
      have hin : QMulIT B m
          ((forIn [:bN.length] (⟨s.fst, zero, s.snd⟩)
            (genMulInnerStep zero aN bN pfx i) : Id MulI)) := by
        refine forIn_range_inv_lt (QMulIT B m) _ _ _ hinit (hstepI i hi) ?_
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

/-- **`genFold` emits reads-bound commands from a bound name set.** -/
theorem genFold_trans {B : String → Prop} (zero c0N c1N : String) (full : List String)
    (pfx : String) (hp : NameOk pfx) (hz : B zero) (hBs : SrcSet B)
    (hc0 : B c0N) (hc1 : B c1N) (hf : AllIn B full) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x)
      ∧ TransFrom B W (genFold zero c0N c1N full pfx).1
      ∧ AllIn W (genFold zero c0N c1N full pfx).2 := by
  rw [genFold_cases]
  split
  · exact ⟨B, hBs, fun _ h => h, transFrom_nil B, hf⟩
  · obtain ⟨W₁, hWs₁, hWb₁, hWr₁, hn₁⟩ :=
      genMul_trans (B := B) zero [c0N, c1N] (full.drop 8) (pfx ++ "m")
        (hp.append _) hz hBs (allIn_pair hc0 hc1) (allIn_drop hf 8)
    obtain ⟨W₂, hWs₂, hWb₂, hWr₂, hn₂⟩ :=
      genAdd_trans (B := W₁) zero (full.take 8)
        (genMul zero [c0N, c1N] (full.drop 8) (pfx ++ "m")).2 (pfx ++ "a")
        (hp.append _) (hWb₁ zero hz) hWs₁
        (allIn_mono (allIn_take hf 8) hWb₁) hn₁
    refine ⟨fun x => W₁ x ∨ W₂ x, ?_, fun x hx => Or.inl (hWb₁ x hx),
      transFrom_append hWr₁ hWr₂ (fun x hx => Or.inr hx), fun k hk => Or.inr (hn₂ k hk)⟩
    rintro y (h | h)
    · exact hWs₁ y h
    · exact hWs₂ y h

/-! ## 6. The three field bricks

Each brick chains the builders with `transFrom_trans`, appends the branch-free
select mask, and closes with the eight-command select loop, handled by
`transFrom_forInRange`. -/

/-- **The `feMul` brick emits reads-bound commands from a bound operand set.** -/
theorem feMulHalves_trans {B : String → Prop} (pfx : String) (A Bn : List String)
    (hp : NameOk pfx) (hBs : SrcSet B) (hz : B "ZZ") (hc0 : B "CC0") (hc1 : B "CC1")
    (hpl : AllIn B plNames) (hA : AllIn B A) (hBn : AllIn B Bn)
    (hA8 : A.length = 8) (hB8 : Bn.length = 8) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x)
      ∧ TransFrom B W (feMulHalves pfx A Bn).1
      ∧ AllIn W (feMulHalves pfx A Bn).2 := by
  obtain ⟨W1, hs1, hb1, hr1, hn1⟩ :=
    genMul_trans (B := B) "ZZ" A Bn (pfx ++ "M") (hp.append _) hz hBs hA hBn
  have hl1 : 8 ≤ (genMul "ZZ" A Bn (pfx ++ "M")).2.length := by
    rw [genMul_len, hA8, hB8]; omega
  obtain ⟨W2, hs2, hb2, hr2, hn2⟩ :=
    genFold_trans (B := W1) "ZZ" "CC0" "CC1" _ (pfx ++ "F1") (hp.append _)
      (hb1 _ hz) hs1 (hb1 _ hc0) (hb1 _ hc1) hn1
  have hl2 := genFold_len_ge "ZZ" "CC0" "CC1" _ (pfx ++ "F1") hl1
  obtain ⟨W3, hs3, hb3, hr3, hn3⟩ :=
    genFold_trans (B := W2) "ZZ" "CC0" "CC1" _ (pfx ++ "F2") (hp.append _)
      (hb2 _ (hb1 _ hz)) hs2 (hb2 _ (hb1 _ hc0)) (hb2 _ (hb1 _ hc1)) hn2
  have hl3 := genFold_len_ge "ZZ" "CC0" "CC1" _ (pfx ++ "F2") hl2
  obtain ⟨W4, hs4, hb4, hr4, hn4⟩ :=
    genFold_trans (B := W3) "ZZ" "CC0" "CC1" _ (pfx ++ "F3") (hp.append _)
      (hb3 _ (hb2 _ (hb1 _ hz))) hs3 (hb3 _ (hb2 _ (hb1 _ hc0)))
      (hb3 _ (hb2 _ (hb1 _ hc1))) hn3
  have hl4 := genFold_len_ge "ZZ" "CC0" "CC1" _ (pfx ++ "F3") hl3
  obtain ⟨W5, hs5, hb5, hr5, hn5⟩ :=
    genFold_trans (B := W4) "ZZ" "CC0" "CC1" _ (pfx ++ "F4") (hp.append _)
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
    genSub_trans (B := W5) "ZZ" _ plNames (pfx ++ "S") (hp.append _)
      (hB5 _ hz) hs5 (allIn_take hn5 8) (allIn_mono hpl hB5)
  have hB6 : ∀ x, B x → W6 x := fun x hx => hb6 _ (hB5 x hx)
  have hdlen := genSub_len "ZZ"
    ((genFold "ZZ" "CC0" "CC1"
        (genFold "ZZ" "CC0" "CC1"
          (genFold "ZZ" "CC0" "CC1"
            (genFold "ZZ" "CC0" "CC1" (genMul "ZZ" A Bn (pfx ++ "M")).2 (pfx ++ "F1")).2
              (pfx ++ "F2")).2 (pfx ++ "F3")).2 (pfx ++ "F4")).2.take 8)
    plNames (pfx ++ "S")
  have hMMR : BindOk (pfx ++ "MMR") := (hp.append _).bindOk
  have hMM : BindOk (pfx ++ "MM") := (hp.append _).bindOk
  have hNM : BindOk (pfx ++ "NM") := (hp.append _).bindOk
  have hRnt : ∀ i, i < 8 →
      BindOk (((List.range 8).map (fun j => s!"{pfx}R{j}"))[i]!) := by
    intro i hi
    rw [map_range_getBang 8 _ i hi]
    exact ((hp.append _).append _).bindOk
  have htail := transFrom_snoc3
    (transFrom_trans (transFrom_trans (transFrom_trans (transFrom_trans
      (transFrom_trans hr1 hr2) hr3) hr4) hr5) hr6)
    hMMR hMM hNM
    (readsFrom_sub (readsFrom_lit lt64_zero) (readsFrom_var (hs6 _ hbw) hbw))
    (readsFrom_and (readsFrom_var hMMR.1 (Or.inr rfl)) (readsFrom_lit mask32_lt))
    (readsFrom_xor (readsFrom_var hMM.1 (Or.inr rfl)) (readsFrom_lit mask32_lt))
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
    · exact hMMR.1
    · exact hMM.1
    · exact hNM.1
  refine ⟨fun y => (((W6 y ∨ y = pfx ++ "MMR") ∨ y = pfx ++ "MM") ∨ y = pfx ++ "NM")
      ∨ ∃ i, i < 8 ∧ y = ((List.range 8).map (fun j => s!"{pfx}R{j}"))[i]!, ?_, ?_, ?_, ?_⟩
  · rintro y (h | ⟨i, hi, rfl⟩)
    · exact hsrc7 y h
    · exact (hRnt i hi).1
  · exact fun x hx => Or.inl (Or.inl (Or.inl (Or.inl (hB6 x hx))))
  · unfold feMulHalves
    refine transFrom_forInRange (fun i => ((List.range 8).map (fun j => s!"{pfx}R{j}"))[i]!)
      8 _ _ htail hsrc7 hRnt ?_
    intro a ha W l hWs hWb hWr
    refine ⟨_, rfl, transFrom_snoc hWr (hRnt a ha) (readsFrom_add ?_ ?_)⟩
    · exact readsFrom_and
        (readsFrom_var (hs6 _ (hlo a ha)) (hWb _ (Or.inl (Or.inl (Or.inl (hlo a ha))))))
        (readsFrom_var hMM.1 (hWb _ (Or.inl (Or.inr rfl))))
    · exact readsFrom_and
        (readsFrom_var (hs6 _ (hdi a ha)) (hWb _ (Or.inl (Or.inl (Or.inl (hdi a ha))))))
        (readsFrom_var hNM.1 (hWb _ (Or.inr rfl)))
  · intro k hk
    rw [feMulHalves_len] at hk
    exact Or.inr ⟨k, hk, rfl⟩

/-- **The `feAdd` brick emits reads-bound commands from a bound operand set.** -/
theorem feAddHalves_trans {B : String → Prop} (pfx : String) (A Bn : List String)
    (hp : NameOk pfx) (hBs : SrcSet B) (hz : B "ZZ")
    (hpl : AllIn B plNames) (hA : AllIn B A) (hBn : AllIn B Bn)
    (hA8 : A.length = 8) (hB8 : Bn.length = 8) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x)
      ∧ TransFrom B W (feAddHalves pfx A Bn).1
      ∧ AllIn W (feAddHalves pfx A Bn).2 := by
  obtain ⟨W1, hs1, hb1, hr1, hn1⟩ :=
    genAdd_trans (B := B) "ZZ" A Bn (pfx ++ "A") (hp.append _) hz hBs hA hBn
  have hl1 : (genAdd "ZZ" A Bn (pfx ++ "A")).2.length = 9 := by
    rw [genAdd_len, hA8, hB8]
    norm_num
  obtain ⟨W2, hs2, hb2, hr2, hn2, hbw⟩ :=
    genSub_trans (B := W1) "ZZ" _ (plNames ++ ["ZZ"]) (pfx ++ "S") (hp.append _)
      (hb1 _ hz) hs1 hn1
      (allIn_append (allIn_mono hpl hb1) (allIn_single (hb1 _ hz)))
  have hl2 := genSub_len "ZZ" (genAdd "ZZ" A Bn (pfx ++ "A")).2 (plNames ++ ["ZZ"])
    (pfx ++ "S")
  have hB2 : ∀ x, B x → W2 x := fun x hx => hb2 _ (hb1 x hx)
  have hMMR : BindOk (pfx ++ "MMR") := (hp.append _).bindOk
  have hMM : BindOk (pfx ++ "MM") := (hp.append _).bindOk
  have hNM : BindOk (pfx ++ "NM") := (hp.append _).bindOk
  have hRnt : ∀ i, i < 8 →
      BindOk (((List.range 8).map (fun j => s!"{pfx}R{j}"))[i]!) := by
    intro i hi
    rw [map_range_getBang 8 _ i hi]
    exact ((hp.append _).append _).bindOk
  have htail := transFrom_snoc3 (transFrom_trans hr1 hr2) hMMR hMM hNM
    (readsFrom_sub (readsFrom_lit lt64_zero) (readsFrom_var (hs2 _ hbw) hbw))
    (readsFrom_and (readsFrom_var hMMR.1 (Or.inr rfl)) (readsFrom_lit mask32_lt))
    (readsFrom_xor (readsFrom_var hMM.1 (Or.inr rfl)) (readsFrom_lit mask32_lt))
  have hsi : ∀ i, i < 8 → W2 ((genAdd "ZZ" A Bn (pfx ++ "A")).2[i]!) :=
    fun i hi => hb2 _ (hn1 i (by rw [hl1]; omega))
  have hdi : ∀ i, i < 8 → W2 ((genSub "ZZ" (genAdd "ZZ" A Bn (pfx ++ "A")).2
      (plNames ++ ["ZZ"]) (pfx ++ "S")).2.1[i]!) :=
    fun i hi => hn2 i (by rw [hl2, hl1]; omega)
  have hsrc3 : SrcSet (fun y => ((W2 y ∨ y = pfx ++ "MMR") ∨ y = pfx ++ "MM")
      ∨ y = pfx ++ "NM") := by
    rintro y (((h | rfl) | rfl) | rfl)
    · exact hs2 y h
    · exact hMMR.1
    · exact hMM.1
    · exact hNM.1
  refine ⟨fun y => (((W2 y ∨ y = pfx ++ "MMR") ∨ y = pfx ++ "MM") ∨ y = pfx ++ "NM")
      ∨ ∃ i, i < 8 ∧ y = ((List.range 8).map (fun j => s!"{pfx}R{j}"))[i]!, ?_, ?_, ?_, ?_⟩
  · rintro y (h | ⟨i, hi, rfl⟩)
    · exact hsrc3 y h
    · exact (hRnt i hi).1
  · exact fun x hx => Or.inl (Or.inl (Or.inl (Or.inl (hB2 x hx))))
  · unfold feAddHalves
    refine transFrom_forInRange (fun i => ((List.range 8).map (fun j => s!"{pfx}R{j}"))[i]!)
      8 _ _ htail hsrc3 hRnt ?_
    intro a ha W l hWs hWb hWr
    refine ⟨_, rfl, transFrom_snoc hWr (hRnt a ha) (readsFrom_add ?_ ?_)⟩
    · exact readsFrom_and
        (readsFrom_var (hs2 _ (hsi a ha)) (hWb _ (Or.inl (Or.inl (Or.inl (hsi a ha))))))
        (readsFrom_var hMM.1 (hWb _ (Or.inl (Or.inr rfl))))
    · exact readsFrom_and
        (readsFrom_var (hs2 _ (hdi a ha)) (hWb _ (Or.inl (Or.inl (Or.inl (hdi a ha))))))
        (readsFrom_var hNM.1 (hWb _ (Or.inr rfl)))
  · intro k hk
    rw [feAddHalves_len] at hk
    exact Or.inr ⟨k, hk, rfl⟩

/-- **The `feSub` brick emits reads-bound commands from a bound operand set.** -/
theorem feSubHalves_trans {B : String → Prop} (pfx : String) (A Bn : List String)
    (hp : NameOk pfx) (hBs : SrcSet B) (hz : B "ZZ")
    (hpl : AllIn B plNames) (hA : AllIn B A) (hBn : AllIn B Bn) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x)
      ∧ TransFrom B W (feSubHalves pfx A Bn).1
      ∧ AllIn W (feSubHalves pfx A Bn).2 := by
  obtain ⟨W1, hs1, hb1, hr1, hn1, hbw⟩ :=
    genSub_trans (B := B) "ZZ" A Bn (pfx ++ "S") (hp.append _) hz hBs hA hBn
  have hpll : plNames.length = 8 := by simp [plNames]
  have hMMR : BindOk (pfx ++ "MMR") := (hp.append _).bindOk
  have hMM : BindOk (pfx ++ "MM") := (hp.append _).bindOk
  have hPMnt : ∀ i, i < 8 →
      BindOk (((List.range 8).map (fun j => s!"{pfx}PM{j}"))[i]!) := by
    intro i hi
    rw [map_range_getBang 8 _ i hi]
    exact ((hp.append _).append _).bindOk
  have h2 := transFrom_snoc2 hr1 hMMR hMM
    (readsFrom_sub (readsFrom_lit lt64_zero) (readsFrom_var (hs1 _ hbw) hbw))
    (readsFrom_and (readsFrom_var hMMR.1 (Or.inr rfl)) (readsFrom_lit mask32_lt))
  have hsrc2 : SrcSet (fun y => (W1 y ∨ y = pfx ++ "MMR") ∨ y = pfx ++ "MM") :=
    srcSet_or (srcSet_or hs1 hMMR.1) hMM.1
  obtain ⟨W4, hs4, hb4, hr4, hn4⟩ :=
    genAdd_trans
      (B := fun y => ((W1 y ∨ y = pfx ++ "MMR") ∨ y = pfx ++ "MM")
        ∨ ∃ i, i < 8 ∧ y = ((List.range 8).map (fun j => s!"{pfx}PM{j}"))[i]!)
      "ZZ" (genSub "ZZ" A Bn (pfx ++ "S")).2.1
      ((List.range 8).map (fun j => s!"{pfx}PM{j}")) (pfx ++ "A") (hp.append _)
      (Or.inl (Or.inl (Or.inl (hb1 _ hz))))
      (by
        rintro y ((h | ⟨i, hi, rfl⟩))
        · exact hsrc2 y h
        · exact (hPMnt i hi).1)
      (fun k hk => Or.inl (Or.inl (Or.inl (hn1 k hk))))
      (fun k hk => Or.inr ⟨k, by simpa using hk, rfl⟩)
  refine ⟨W4, hs4, fun x hx => hb4 _ (Or.inl (Or.inl (Or.inl (hb1 x hx)))), ?_,
    allIn_take hn4 8⟩
  unfold feSubHalves
  refine transFrom_trans ?_ hr4
  refine transFrom_forInRange (fun i => ((List.range 8).map (fun j => s!"{pfx}PM{j}"))[i]!)
    8 _ _ h2 hsrc2 hPMnt ?_
  intro a ha W l hWs hWb hWr
  have hpa : W1 (plNames[a]!) := hb1 _ (hpl a (by rw [hpll]; exact ha))
  exact ⟨_, rfl, transFrom_snoc hWr (hPMnt a ha)
    (readsFrom_and (readsFrom_var (hs1 _ hpa) (hWb _ (Or.inl (Or.inl hpa))))
      (readsFrom_var hMM.1 (hWb _ (Or.inr rfl))))⟩

/-! ## 7. Widening, and the frame-relative gadgets -/

/-- The walk's ambient word set is carried along, so a walk from a smaller
    entry set is a walk from any larger one, with the larger set still bound at
    the exit. -/
theorem transFrom_widen {Bc Wc V : String → Prop} {l : List LowCT}
    (h : TransFrom Bc Wc l) (hV : ∀ x, Bc x → V x) :
    TransFrom V (fun y => V y ∨ Wc y) l := by
  intro C hs hF hb
  obtain ⟨D, hsD, hDF, hCD, hWD, hts⟩ := h C hs hF (fun x hx => hb x (hV x hx))
  exact ⟨D, hsD, hDF, hCD,
    fun x hx => hx.elim (fun h => hCD x (hb x h)) (hWD x), hts⟩

/-- A `List.map` is the `flatMap` of its singletons. -/
theorem map_eq_flatMap_singleton {α β : Type} (l : List α) (f : α → β) :
    l.map f = l.flatMap (fun a => [f a]) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- **A block extended by one chunk per element of a list**, each chunk read
    from the block's entry set. -/
theorem transFrom_chunkList {B : String → Prop} {α : Type} (g : α → List LowCT)
    (Wc : α → String → Prop) (hBs : SrcSet B) :
    ∀ l : List α, (∀ a ∈ l, SrcSet (Wc a)) → (∀ a ∈ l, TransFrom B (Wc a) (g a)) →
      ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x)
        ∧ (∀ a ∈ l, ∀ x, Wc a x → W x)
        ∧ TransFrom B W (l.flatMap g) := by
  intro l
  induction l with
  | nil =>
      intro _ _
      exact ⟨B, hBs, fun _ h => h, fun a ha => absurd ha (by simp), transFrom_nil B⟩
  | cons a t ih =>
      intro hWs hg
      obtain ⟨W, hWsW, hBW, hWc, hWr⟩ :=
        ih (fun b hb => hWs b (List.mem_cons_of_mem _ hb))
          (fun b hb => hg b (List.mem_cons_of_mem _ hb))
      have hsa : SrcSet (Wc a) := hWs a List.mem_cons_self
      have hV : SrcSet (fun y => B y ∨ Wc a y) := by
        rintro y (hy | hy)
        · exact hBs y hy
        · exact hsa y hy
      have hhead : TransFrom B (fun y => B y ∨ Wc a y) (g a) :=
        transFrom_mono (transFrom_addPre (hg a List.mem_cons_self)) (fun _ h => h)
          (fun x hx => hx.elim (fun h => Or.inr h) (fun h => Or.inl h))
      have htail : TransFrom (fun y => B y ∨ Wc a y) (fun y => (B y ∨ Wc a y) ∨ W y)
          (t.flatMap g) :=
        transFrom_widen (V := fun y => B y ∨ Wc a y) hWr (fun x hx => Or.inl hx)
      refine ⟨fun y => (B y ∨ Wc a y) ∨ W y, ?_, fun x hx => Or.inl (Or.inl hx), ?_, ?_⟩
      · rintro y (hy | hy)
        · exact hV y hy
        · exact hWsW y hy
      · intro b hb x hx
        rcases List.mem_cons.mp hb with rfl | hbt
        · exact Or.inl (Or.inr hx)
        · exact Or.inr (hWc b hbt x hx)
      · have hlist : (a :: t).flatMap g = g a ++ t.flatMap g := by simp
        rw [hlist]
        exact transFrom_trans hhead htail

/-- The cell-index scalar prefix. -/
theorem nameOk_ix : NameOk "ix" :=
  ⟨⟨'i', ['x'], rfl, by decide⟩, (by decide : 2 ≤ "ix".length)⟩

/-- The `p`-limb constant prefix. -/
theorem nameOk_PL : NameOk "PL" :=
  ⟨⟨'P', ['L'], rfl, by decide⟩, (by decide : 2 ≤ "PL".length)⟩

/-- **The cell-index binds are reads-bound**, and bind every named cell. -/
theorem transFrom_idxCells {B : String → Prop} (hBs : SrcSet B) (cells : List Nat)
    (h : ∀ c ∈ cells, c < 2 ^ 64) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x) ∧ (∀ c ∈ cells, W s!"ix{c}")
      ∧ TransFrom B W (idxCells cells) := by
  have hmap : idxCells cells
      = cells.flatMap (fun i => [LowCT.RScalarSetExpr s!"ix{i}" (SExpr.SLit i)]) :=
    map_eq_flatMap_singleton _ _
  rw [hmap]
  obtain ⟨W, hWs, hBW, hWc, hWr⟩ := transFrom_chunkList
    (g := fun i => [LowCT.RScalarSetExpr s!"ix{i}" (SExpr.SLit i)])
    (Wc := fun i => fun y => y = s!"ix{i}") hBs cells
    (fun c _ y hy => hy ▸ (nameOk_ix.append _).notTmp)
    (fun c hc => transFrom_setExpr (nameOk_ix.append _).bindOk (readsFrom_lit (h c hc)))
  exact ⟨W, hWs, hBW, fun c hc => hWc c hc _ rfl, hWr⟩

/-- The reduction constants and the eight `p`-limb constants. -/
def ConstBound : String → Prop := fun y =>
  y = "ZZ" ∨ y = "CC0" ∨ y = "CC1" ∨ ∃ i, i < 8 ∧ y = s!"PL{i}"

theorem constBound_src : SrcSet ConstBound := by
  rintro y (rfl | rfl | rfl | ⟨i, -, rfl⟩)
  · exact notTmp_ZZ
  · exact notTmp_CC0
  · exact notTmp_CC1
  · exact (nameOk_PL.append _).notTmp

/-- **The constant prologue is reads-bound**, and binds the reduction constants
    and the eight `p`-limb constants. -/
theorem transFrom_constInit {B : String → Prop} (hBs : SrcSet B) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, B x → W x) ∧ (∀ x, ConstBound x → W x)
      ∧ TransFrom B W constInit := by
  have hzz : BindOk "ZZ" := ⟨notTmp_ZZ, by decide⟩
  have hc0 : BindOk "CC0" := ⟨notTmp_CC0, by decide⟩
  have hc1 : BindOk "CC1" := ⟨notTmp_CC1, by decide⟩
  have h3 := transFrom_snoc3 (transFrom_nil B) hzz hc0 hc1
    (@readsFrom_lit _ 0 (by norm_num)) (@readsFrom_lit _ cc0 (by norm_num [cc0]))
    (@readsFrom_lit _ cc1 (by norm_num [cc1]))
  have hmap := transFrom_mapRange (fun i => s!"PL{i}")
    (fun i => (.SLit (pl32.getD i 0) : SExpr)) h3 8
    (fun i _ => (nameOk_PL.append _).bindOk)
    (fun i _ => @readsFrom_lit _ (pl32.getD i 0)
      (getD_lt_of_mem_lt pl32_mem_lt (by norm_num) i))
  refine ⟨_, ?_, fun x hx => Or.inl (Or.inl (Or.inl (Or.inl hx))), ?_, hmap⟩
  · rintro y ((((hB | rfl) | rfl) | rfl) | ⟨i, hi, rfl⟩)
    · exact hBs y hB
    · exact notTmp_ZZ
    · exact notTmp_CC0
    · exact notTmp_CC1
    · exact (nameOk_PL.append _).notTmp
  · rintro y (rfl | rfl | rfl | ⟨i, hi, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl (Or.inr rfl)))
    · exact Or.inl (Or.inl (Or.inr rfl))
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨i, hi, rfl⟩

/-- **A block extended by a `List.range`-indexed family of dynamic-index frame
    loads**, each at an index the block already binds. -/
theorem transFrom_arrLoadRange {B W : String → Prop} {l : List LowCT}
    (nm : Nat → String) (fw : Nat) (idxV : Nat → String) (h : TransFrom B W l) :
    ∀ n : Nat, (∀ i, i < n → BindOk (nm i)) → (∀ i, i < n → W (idxV i)) →
      TransFrom B (fun y => W y ∨ ∃ i, i < n ∧ y = nm i)
        (l ++ (List.range n).map
          (fun i => LowCT.RArrLoad ⟨nm i, .TU64⟩ ⟨"F", .TBytes fw⟩ (idxV i))) := by
  intro n
  induction n with
  | zero =>
      intro _ _
      have hl : l ++ (List.range 0).map
          (fun i => LowCT.RArrLoad ⟨nm i, .TU64⟩ (⟨"F", .TBytes fw⟩ : Located) (idxV i))
          = l := by simp
      rw [hl]
      refine transFrom_mono h (fun _ hx => hx) (fun x hx => ?_)
      rcases hx with hx | ⟨i, hi, -⟩
      · exact hx
      · exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      intro hnt hidx
      have hprev := ih (fun i hi => hnt i (by omega)) (fun i hi => hidx i (by omega))
      have hs := transFrom_append hprev
        (transFrom_arrLoad1 (d := nm n) (ix := idxV n) fw (hnt n (by omega)))
        (fun x hx => Or.inr (Or.inl (hx ▸ hidx n (by omega))))
      have hl : l ++ (List.range (n + 1)).map
            (fun i => LowCT.RArrLoad ⟨nm i, .TU64⟩ (⟨"F", .TBytes fw⟩ : Located) (idxV i))
          = (l ++ (List.range n).map
              (fun i => LowCT.RArrLoad ⟨nm i, .TU64⟩ (⟨"F", .TBytes fw⟩ : Located) (idxV i)))
            ++ [LowCT.RArrLoad ⟨nm n, .TU64⟩ (⟨"F", .TBytes fw⟩ : Located) (idxV n)] := by
        rw [List.range_succ, List.map_append, List.append_assoc]; simp
      rw [hl]
      refine transFrom_mono hs (fun _ hx => hx) (fun x hx => ?_)
      rcases hx with hx | ⟨i, hi, rfl⟩
      · exact Or.inl (Or.inl hx)
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact Or.inl (Or.inr ⟨i, hlt, rfl⟩)
        · exact Or.inr rfl

/-- **A block extended by a `List.range`-indexed family of scalar-assignment
    pairs**, each reading only names the block already binds. -/
theorem transFrom_flatMapRange2 {B W : String → Prop} {l : List LowCT}
    (n1 n2 : Nat → String) (e1 e2 : Nat → SExpr) (h : TransFrom B W l) (n : Nat)
    (hnt1 : ∀ i, i < n → BindOk (n1 i)) (hnt2 : ∀ i, i < n → BindOk (n2 i))
    (hrd1 : ∀ i, i < n → ReadsFrom W (e1 i)) (hrd2 : ∀ i, i < n → ReadsFrom W (e2 i)) :
    TransFrom B (fun y => W y ∨ ∃ i, i < n ∧ (y = n1 i ∨ y = n2 i))
      (l ++ (List.range n).flatMap
        (fun i => [LowCT.RScalarSetExpr (n1 i) (e1 i),
                   LowCT.RScalarSetExpr (n2 i) (e2 i)])) := by
  induction n with
  | zero =>
      have hl : l ++ (List.range 0).flatMap
          (fun i => [LowCT.RScalarSetExpr (n1 i) (e1 i), LowCT.RScalarSetExpr (n2 i) (e2 i)])
          = l := by simp
      rw [hl]
      refine transFrom_mono h (fun _ hx => hx) (fun x hx => ?_)
      rcases hx with hx | ⟨i, hi, -⟩
      · exact hx
      · exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
      have hprev := ih (fun i hi => hnt1 i (by omega)) (fun i hi => hnt2 i (by omega))
        (fun i hi => hrd1 i (by omega)) (fun i hi => hrd2 i (by omega))
      have hs := transFrom_snoc2 hprev (hnt1 n (by omega)) (hnt2 n (by omega))
        (readsFrom_mono (hrd1 n (by omega)) (fun _ hx => Or.inl hx))
        (readsFrom_mono (hrd2 n (by omega)) (fun _ hx => Or.inl (Or.inl hx)))
      have hl : l ++ (List.range (n + 1)).flatMap
            (fun i => [LowCT.RScalarSetExpr (n1 i) (e1 i), LowCT.RScalarSetExpr (n2 i) (e2 i)])
          = (l ++ (List.range n).flatMap
              (fun i => [LowCT.RScalarSetExpr (n1 i) (e1 i),
                         LowCT.RScalarSetExpr (n2 i) (e2 i)]))
            ++ [LowCT.RScalarSetExpr (n1 n) (e1 n), LowCT.RScalarSetExpr (n2 n) (e2 n)] := by
        rw [List.range_succ, List.flatMap_append, List.append_assoc]; simp
      rw [hl]
      refine transFrom_mono hs (fun _ hx => hx) (fun x hx => ?_)
      rcases hx with hx | ⟨i, hi, hxi⟩
      · exact Or.inl (Or.inl (Or.inl hx))
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact Or.inl (Or.inl (Or.inr ⟨i, hlt, hxi⟩))
        · rcases hxi with rfl | rfl
          · exact Or.inl (Or.inr rfl)
          · exact Or.inr rfl

/-- **The frame load is reads-bound** from the four cell indices it reads, and
    binds the field element's eight half-limb slots. -/
theorem transFrom_loadField {B : String → Prop} (fw o : Nat) (fe : String)
    (hfe : NameOk fe) (hix : ∀ j, j < 4 → B s!"ix{o + j}") :
    TransFrom B (fun y => B y ∨ ∃ k, k < 8 ∧ y = s!"{fe}h{k}")
      (loadField fw "F" o fe) := by
  have hntu : ∀ j, j < 4 → BindOk s!"{fe}u{j}" :=
    fun j _ => ((hfe.append _).append _).bindOk
  have harr := transFrom_arrLoadRange (B := B) (W := B) (l := [])
    (fun j => s!"{fe}u{j}") fw (fun j => s!"ix{o + j}") (transFrom_nil B) 4 hntu hix
  have hfm := transFrom_flatMapRange2 (n1 := fun j => s!"{fe}h{2 * j}")
    (n2 := fun j => s!"{fe}h{2 * j + 1}")
    (e1 := fun j => .SAnd (sv s!"{fe}u{j}") (.SLit mask32))
    (e2 := fun j => .SShr (sv s!"{fe}u{j}") (.SLit 32))
    harr 4
    (fun j _ => ((hfe.append _).append _).bindOk)
    (fun j _ => ((hfe.append _).append _).bindOk)
    (fun j hj => readsFrom_and
      (readsFrom_var (hntu j hj).1 (Or.inr ⟨j, hj, rfl⟩)) (readsFrom_lit mask32_lt))
    (fun j hj => readsFrom_shr
      (readsFrom_var (hntu j hj).1 (Or.inr ⟨j, hj, rfl⟩)) (readsFrom_lit lt64_32))
  rw [show loadField fw "F" o fe
        = ([] ++ (List.range 4).map (fun j =>
            (LowCT.RArrLoad ⟨s!"{fe}u{j}", .TU64⟩
              (⟨"F", .TBytes fw⟩ : Located) s!"ix{o + j}")))
          ++ (List.range 4).flatMap (fun j =>
            [LowCT.RScalarSetExpr s!"{fe}h{2 * j}" (.SAnd (sv s!"{fe}u{j}") (.SLit mask32)),
             LowCT.RScalarSetExpr s!"{fe}h{2 * j + 1}" (.SShr (sv s!"{fe}u{j}") (.SLit 32))])
        from rfl]
  refine transFrom_mono hfm (fun _ hx => hx) (fun x hx => ?_)
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

/-- **The frame store is reads-bound** from the field element's half-limb slots
    and the four cell indices it stores at. -/
theorem transFrom_storeRange {B W : String → Prop} {l : List LowCT} (fw o : Nat)
    (fe : String) (hfe : NameOk fe)
    (henc : encodeTy (.TBytes fw) = CryptoTy.memref 256) (h : TransFrom B W l)
    (hh : ∀ k, k < 8 → W s!"{fe}h{k}") (hix : ∀ j, j < 4 → W s!"ix{o + j}")
    (hWs : SrcSet W) :
    ∀ n : Nat, n ≤ 4 →
      TransFrom B (fun y => W y ∨ ∃ j, j < n ∧ y = s!"{fe}o{j}")
        (l ++ (List.range n).flatMap (fun j =>
          [LowCT.RScalarSetExpr s!"{fe}o{j}"
             (.SAdd (sv s!"{fe}h{2 * j}") (.SShl (sv s!"{fe}h{2 * j + 1}") (.SLit 32))),
           LowCT.RArrStore (⟨"F", .TBytes fw⟩ : Located) s!"ix{o + j}"
             (⟨s!"{fe}o{j}", .TU64⟩ : Located)])) := by
  intro n
  induction n with
  | zero =>
      intro _
      have hl : l ++ (List.range 0).flatMap (fun j =>
          [LowCT.RScalarSetExpr s!"{fe}o{j}"
             (.SAdd (sv s!"{fe}h{2 * j}") (.SShl (sv s!"{fe}h{2 * j + 1}") (.SLit 32))),
           LowCT.RArrStore (⟨"F", .TBytes fw⟩ : Located) s!"ix{o + j}"
             (⟨s!"{fe}o{j}", .TU64⟩ : Located)]) = l := by simp
      rw [hl]
      refine transFrom_mono h (fun _ hx => hx) (fun x hx => ?_)
      rcases hx with hx | ⟨j, hj, -⟩
      · exact hx
      · exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hon : BindOk s!"{fe}o{n}" := ((hfe.append _).append _).bindOk
      have hset := transFrom_snoc hprev hon
        (readsFrom_add
          (readsFrom_var (hWs _ (hh (2 * n) (by omega))) (Or.inl (hh (2 * n) (by omega))))
          (readsFrom_shl
            (readsFrom_var (hWs _ (hh (2 * n + 1) (by omega)))
              (Or.inl (hh (2 * n + 1) (by omega))))
            (readsFrom_lit lt64_32)))
      have hstore := transFrom_append hset
        (transFrom_arrStore1 (ix := s!"ix{o + n}") (s := s!"{fe}o{n}") fw henc)
        (fun x hx => hx.elim
          (fun hxi => Or.inr (Or.inl (Or.inl (hxi ▸ hix n (by omega)))))
          (fun hxo => Or.inr (Or.inr hxo)))
      have hl : l ++ (List.range (n + 1)).flatMap (fun j =>
            [LowCT.RScalarSetExpr s!"{fe}o{j}"
               (.SAdd (sv s!"{fe}h{2 * j}") (.SShl (sv s!"{fe}h{2 * j + 1}") (.SLit 32))),
             LowCT.RArrStore (⟨"F", .TBytes fw⟩ : Located) s!"ix{o + j}"
               (⟨s!"{fe}o{j}", .TU64⟩ : Located)])
          = ((l ++ (List.range n).flatMap (fun j =>
              [LowCT.RScalarSetExpr s!"{fe}o{j}"
                 (.SAdd (sv s!"{fe}h{2 * j}") (.SShl (sv s!"{fe}h{2 * j + 1}") (.SLit 32))),
               LowCT.RArrStore (⟨"F", .TBytes fw⟩ : Located) s!"ix{o + j}"
                 (⟨s!"{fe}o{j}", .TU64⟩ : Located)]))
            ++ [LowCT.RScalarSetExpr s!"{fe}o{n}"
                 (.SAdd (sv s!"{fe}h{2 * n}") (.SShl (sv s!"{fe}h{2 * n + 1}") (.SLit 32)))])
            ++ [LowCT.RArrStore (⟨"F", .TBytes fw⟩ : Located) s!"ix{o + n}"
                 (⟨s!"{fe}o{n}", .TU64⟩ : Located)] := by
        rw [List.range_succ, List.flatMap_append, List.append_assoc, List.append_assoc]
        simp
      rw [hl]
      refine transFrom_mono hstore (fun _ hx => hx) (fun x hx => ?_)
      rcases hx with hx | ⟨j, hj, rfl⟩
      · exact Or.inl (Or.inl (Or.inl hx))
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
        · exact Or.inl (Or.inl (Or.inr ⟨j, hlt, rfl⟩))
        · exact Or.inl (Or.inr rfl)

/-! ## 8. The framed bricks -/

/-- **The constant and operand-load prefix of a framed brick is reads-bound**,
    and binds the brick body's entry set together with every cell index it
    binds. -/
theorem transFrom_pre (fw : Nat) (pfx : String) (oa ob : Nat) (cells : List Nat)
    (hpfx : NameOk pfx) (hcells : ∀ c ∈ cells, c < 2 ^ 64)
    (hca : ∀ j, j < 4 → (oa + j) ∈ cells) (hcb : ∀ j, j < 4 → (ob + j) ∈ cells) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, Bbody pfx x → W x)
      ∧ (∀ c ∈ cells, W s!"ix{c}")
      ∧ TransFrom (fun _ => False) W
        (idxCells cells ++ constInit ++ loadField fw "F" oa (pfx ++ "A")
          ++ loadField fw "F" ob (pfx ++ "B")) := by
  have hFalse : SrcSet (fun _ => False) := fun _ h => h.elim
  obtain ⟨W1, hs1, -, hix1, hr1⟩ := transFrom_idxCells hFalse cells hcells
  obtain ⟨W2, hs2, hb2, hconst2, hr2⟩ := transFrom_constInit hs1
  have hrA := transFrom_loadField (B := W2) fw oa (pfx ++ "A") (hpfx.append _)
    (fun j hj => hb2 _ (hix1 _ (hca j hj)))
  have hrB := transFrom_loadField
    (B := fun y => W2 y ∨ ∃ k, k < 8 ∧ y = s!"{pfx ++ "A"}h{k}") fw ob (pfx ++ "B")
    (hpfx.append _) (fun j hj => Or.inl (hb2 _ (hix1 _ (hcb j hj))))
  refine ⟨_, ?_, ?_, ?_, transFrom_trans (transFrom_trans (transFrom_trans hr1 hr2) hrA) hrB⟩
  · rintro y ((hy | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩)
    · exact hs2 y hy
    · exact (((hpfx.append "A").append "h").append _).notTmp
    · exact (((hpfx.append "B").append "h").append _).notTmp
  · rintro y (((rfl | rfl | rfl | ⟨i, hi, rfl⟩) | ⟨k, hk, rfl⟩) | ⟨k, hk, rfl⟩)
    · exact Or.inl (Or.inl (hconst2 _ (Or.inl rfl)))
    · exact Or.inl (Or.inl (hconst2 _ (Or.inr (Or.inl rfl))))
    · exact Or.inl (Or.inl (hconst2 _ (Or.inr (Or.inr (Or.inl rfl)))))
    · exact Or.inl (Or.inl (hconst2 _ (Or.inr (Or.inr (Or.inr ⟨i, hi, rfl⟩)))))
    · exact Or.inl (Or.inr ⟨k, hk, rfl⟩)
    · exact Or.inr ⟨k, hk, rfl⟩
  · exact fun c hc => Or.inl (Or.inl (hb2 _ (hix1 c hc)))

/-- **The common assembly of a frame-relative brick is reads-bound.** Given a
    reads-bound brick body over the operand-load entry set, the constant/load
    prefix, the body, the copy block and the frame store compose into one
    reads-bound walk from the frame alone. -/
theorem transFrom_framedAssemble (fw sa sb so : Nat) (pfx : String)
    (hpfx : NameOk pfx) (henc : encodeTy (.TBytes fw) = CryptoTy.memref 256)
    (hsa : 4 * sa + 3 < 2 ^ 64) (hsb : 4 * sb + 3 < 2 ^ 64) (hso : 4 * so + 3 < 2 ^ 64)
    (bc : List LowCT) (br : List String) (hbr8 : br.length = 8)
    (hbrick : ∃ W : String → Prop, SrcSet W ∧ (∀ x, Bbody pfx x → W x)
      ∧ TransFrom (Bbody pfx) W bc ∧ AllIn W br) :
    ∃ W : String → Prop, SrcSet W ∧ TransFrom (fun _ => False) W
      (idxCells ((List.range 4).map (4 * sa + ·) ++ (List.range 4).map (4 * sb + ·)
          ++ (List.range 4).map (4 * so + ·))
        ++ constInit
        ++ loadField fw "F" (4 * sa) (pfx ++ "A")
        ++ loadField fw "F" (4 * sb) (pfx ++ "B")
        ++ bc
        ++ (List.range 8).map (fun k => LowCT.RScalarSetExpr s!"{pfx}Oh{k}" (sv (br[k]!)))
        ++ storeFieldTo fw "F" (4 * so) (pfx ++ "O")) := by
  obtain ⟨Wb, hWbs, hWbb, hWbr, hWbn⟩ := hbrick
  set cells := (List.range 4).map (4 * sa + ·) ++ (List.range 4).map (4 * sb + ·)
      ++ (List.range 4).map (4 * so + ·) with hcellsdef
  have hmemL : ∀ (s : Nat) (j : Nat), j < 4 → (4 * s + j) ∈ (List.range 4).map (4 * s + ·) :=
    fun s j hj => List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  have hcells : ∀ c ∈ cells, c < 2 ^ 64 := by
    intro c hcm
    rcases List.mem_append.mp hcm with hcab | hco
    · rcases List.mem_append.mp hcab with hca | hcb
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hca
        have := List.mem_range.mp hj
        omega
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hcb
        have := List.mem_range.mp hj
        omega
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hco
      have := List.mem_range.mp hj
      omega
  obtain ⟨Wp, hsp, hbp, hixp, hrp⟩ := transFrom_pre fw pfx (4 * sa) (4 * sb) cells hpfx
    hcells (fun j hj => List.mem_append_left _ (List.mem_append_left _ (hmemL sa j hj)))
    (fun j hj => List.mem_append_left _ (List.mem_append_right _ (hmemL sb j hj)))
  have hbody : TransFrom Wp (fun y => Wp y ∨ Wb y) bc :=
    transFrom_widen (V := Wp) hWbr hbp
  have hsbody : SrcSet (fun y => Wp y ∨ Wb y) := by
    rintro y (hy | hy)
    · exact hsp y hy
    · exact hWbs y hy
  have hcopies := transFrom_mapRange (fun k => s!"{pfx}Oh{k}") (fun k => sv (br[k]!))
    (transFrom_trans hrp hbody) 8
    (fun k _ => ((hpfx.append _).append _).bindOk)
    (fun k hk => readsFrom_var (hWbs _ (hWbn k (by rw [hbr8]; exact hk)))
      (Or.inr (hWbn k (by rw [hbr8]; exact hk))))
  have hscop : SrcSet (fun y => (Wp y ∨ Wb y) ∨ ∃ k, k < 8 ∧ y = s!"{pfx}Oh{k}") := by
    rintro y (hy | ⟨k, hk, rfl⟩)
    · exact hsbody y hy
    · exact ((hpfx.append _).append _).notTmp
  have hstore := transFrom_storeRange (fw := fw) (o := 4 * so) (fe := pfx ++ "O")
    (hpfx.append _) henc hcopies
    (fun k hk => Or.inr ⟨k, hk, (oh_bridge pfx k).symm⟩)
    (fun j hj => Or.inl (Or.inl (hixp _ (List.mem_append_right _ (hmemL so j hj)))))
    hscop 4 (le_refl 4)
  refine ⟨_, ?_, hstore⟩
  rintro y (hy | ⟨j, hj, rfl⟩)
  · exact hscop y hy
  · exact (((hpfx.append _).append _).append _).notTmp

/-- Every `plNames` entry lies in the brick-body entry set. -/
theorem bbody_pl (pfx : String) : AllIn (Bbody pfx) plNames := by
  intro k hk
  have hk8 : k < 8 := by simpa [plNames] using hk
  rw [show plNames[k]! = s!"PL{k}" from by
    simp only [plNames]; exact map_range_getBang 8 _ k hk8]
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr ⟨k, hk8, rfl⟩))))

/-- The first operand's half-limb slots lie in the brick-body entry set. -/
theorem bbody_feA (pfx : String) : AllIn (Bbody pfx) (feH (pfx ++ "A")) := by
  intro k hk
  have hk8 : k < 8 := by simpa [feH] using hk
  rw [show (feH (pfx ++ "A"))[k]! = s!"{pfx ++ "A"}h{k}" from by
    simp only [feH]; exact map_range_getBang 8 _ k hk8]
  exact Or.inl (Or.inr ⟨k, hk8, rfl⟩)

/-- The second operand's half-limb slots lie in the brick-body entry set. -/
theorem bbody_feB (pfx : String) : AllIn (Bbody pfx) (feH (pfx ++ "B")) := by
  intro k hk
  have hk8 : k < 8 := by simpa [feH] using hk
  rw [show (feH (pfx ++ "B"))[k]! = s!"{pfx ++ "B"}h{k}" from by
    simp only [feH]; exact map_range_getBang 8 _ k hk8]
  exact Or.inr ⟨k, hk8, rfl⟩

/-- **A framed field-op brick is reads-bound from the frame alone**: it binds
    every cell index, constant and operand half-limb it reads. -/
theorem emitFOpFramed_trans (fw : Nat) (slotOf : String → Nat) (idx : Nat) (op : FOp)
    (henc : encodeTy (.TBytes fw) = CryptoTy.memref 256)
    (hslot : ∀ s, 4 * slotOf s + 3 < 2 ^ 64) :
    ∃ W : String → Prop, SrcSet W
      ∧ TransFrom (fun _ => False) W (emitFOpFramed fw "F" slotOf idx op) := by
  have hpfx : NameOk s!"fop{idx}" :=
    ⟨HeadOk.append (⟨'f', ['o', 'p'], rfl, by decide⟩ : HeadOk "fop") _,
     Long2.append (show (2 : Nat) ≤ "fop".length by decide) _⟩
  have hC : NameOk (s!"fop{idx}" ++ "C") := hpfx.append _
  have hsrc := bbody_src s!"fop{idx}" hpfx.head
  have hfeH8 : ∀ fe : String, (feH fe).length = 8 := by intro fe; simp [feH]
  cases op with
  | mul o a b =>
      exact transFrom_framedAssemble fw (slotOf a) (slotOf b) (slotOf o) _ hpfx henc
        (hslot a) (hslot b) (hslot o)
        (feMulHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A"))
          (feH (s!"fop{idx}" ++ "B"))).1
        (feMulHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A"))
          (feH (s!"fop{idx}" ++ "B"))).2
        (feMulHalves_len _ _ _)
        (feMulHalves_trans _ _ _ hC hsrc (Or.inl (Or.inl (Or.inl rfl)))
          (Or.inl (Or.inl (Or.inr (Or.inl rfl))))
          (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))
          (bbody_pl _) (bbody_feA _) (bbody_feB _) (hfeH8 _) (hfeH8 _))
  | add o a b =>
      exact transFrom_framedAssemble fw (slotOf a) (slotOf b) (slotOf o) _ hpfx henc
        (hslot a) (hslot b) (hslot o)
        (feAddHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A"))
          (feH (s!"fop{idx}" ++ "B"))).1
        (feAddHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A"))
          (feH (s!"fop{idx}" ++ "B"))).2
        (feAddHalves_len _ _ _)
        (feAddHalves_trans _ _ _ hC hsrc (Or.inl (Or.inl (Or.inl rfl)))
          (bbody_pl _) (bbody_feA _) (bbody_feB _) (hfeH8 _) (hfeH8 _))
  | sub o a b =>
      exact transFrom_framedAssemble fw (slotOf a) (slotOf b) (slotOf o) _ hpfx henc
        (hslot a) (hslot b) (hslot o)
        (feSubHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A"))
          (feH (s!"fop{idx}" ++ "B"))).1
        (feSubHalves (s!"fop{idx}" ++ "C") (feH (s!"fop{idx}" ++ "A"))
          (feH (s!"fop{idx}" ++ "B"))).2
        (feSubHalves_len _ _ _ (hfeH8 _))
        (feSubHalves_trans _ _ _ hC hsrc (Or.inl (Or.inl (Or.inl rfl)))
          (bbody_pl _) (bbody_feA _) (bbody_feB _))

/-! ## 9. Frame-only walks

A framed brick binds every cell index, constant and operand half-limb it reads,
so it walks from the frame alone. Such walks compose over `++` with no side
condition, which is what carries the two point-op bodies and the select trip. -/

/-- A command list whose reads are bound by the names it binds itself: it walks
    from the frame alone. -/
def SelfWalk (l : List LowCT) : Prop :=
  ∃ W : String → Prop, SrcSet W ∧ TransFrom (fun _ => False) W l

theorem selfWalk_nil : SelfWalk [] :=
  ⟨fun _ => False, fun _ h => h.elim, transFrom_nil _⟩

/-- Two frame-only walks in sequence. -/
theorem selfWalk_append {l₁ l₂ : List LowCT} (h₁ : SelfWalk l₁) (h₂ : SelfWalk l₂) :
    SelfWalk (l₁ ++ l₂) := by
  obtain ⟨W₁, hs₁, hr₁⟩ := h₁
  obtain ⟨W₂, hs₂, hr₂⟩ := h₂
  refine ⟨fun y => W₁ y ∨ W₂ y, ?_, transFrom_trans hr₁
    (transFrom_widen (V := W₁) hr₂ (fun _ h => h.elim))⟩
  rintro y (hy | hy)
  · exact hs₁ y hy
  · exact hs₂ y hy

/-- A block extended by a frame-only walk. -/
theorem transFrom_snocSelf {B W : String → Prop} {l₁ l₂ : List LowCT}
    (h : TransFrom B W l₁) (hSW : SelfWalk l₂) (hWs : SrcSet W) :
    ∃ W' : String → Prop, SrcSet W' ∧ TransFrom B W' (l₁ ++ l₂) := by
  obtain ⟨W₂, hs₂, hr₂⟩ := hSW
  refine ⟨fun y => W y ∨ W₂ y, ?_, transFrom_trans h
    (transFrom_widen (V := W) hr₂ (fun _ h => h.elim))⟩
  rintro y (hy | hy)
  · exact hWs y hy
  · exact hs₂ y hy

/-- **A framed field-op brick walks from the frame alone.** -/
theorem selfWalk_emitFOpFramed (fw : Nat) (slotOf : String → Nat) (idx : Nat) (op : FOp)
    (henc : encodeTy (.TBytes fw) = CryptoTy.memref 256)
    (hslot : ∀ s, 4 * slotOf s + 3 < 2 ^ 64) :
    SelfWalk (emitFOpFramed fw "F" slotOf idx op) :=
  emitFOpFramed_trans fw slotOf idx op henc hslot

/-- **A whole schedule of framed bricks walks from the frame alone.** -/
theorem selfWalk_mapIdxFlatten : ∀ (ops : List FOp) (g : Nat → FOp → List LowCT),
    (∀ i op, SelfWalk (g i op)) → SelfWalk ((ops.mapIdx g).flatten) := by
  intro ops
  induction ops with
  | nil => intro g _; exact selfWalk_nil
  | cons op rest ih =>
      intro g hg
      rw [List.mapIdx_cons, List.flatten_cons]
      exact selfWalk_append (hg 0 op) (ih (fun i => g (i + 1)) (fun i o' => hg (i + 1) o'))

/-! ## 10. The select brick and the key-bit fetch -/

/-- **The select brick body is reads-bound** from the operand-load entry set,
    and binds its eight per-limb select results. -/
theorem selBody_trans (fw cbit : Nat) (pfx : String) (hpfx : NameOk pfx)
    (hc : cbit < 2 ^ 64) :
    ∃ W : String → Prop, SrcSet W ∧ (∀ x, Bbody pfx x → W x)
      ∧ TransFrom (Bbody pfx) W (selBody fw cbit pfx).1
      ∧ AllIn W (selBody fw cbit pfx).2 := by
  have hix : BindOk s!"{pfx}ixbit" := (hpfx.append _).bindOk
  have hbit : BindOk s!"{pfx}bit" := (hpfx.append _).bindOk
  have hsrc := bbody_src pfx hpfx.head
  have hstep1 := transFrom_snoc (transFrom_nil (Bbody pfx)) hix (readsFrom_lit hc)
  have hstep2 := transFrom_append hstep1
    (transFrom_arrLoad1 (d := s!"{pfx}bit") (ix := s!"{pfx}ixbit") fw hbit)
    (fun x hx => Or.inr (hx ▸ Or.inr rfl))
  have hA : ∀ k, k < 8 → Bbody pfx s!"{pfx ++ "A"}h{k}" := fun k hk => Or.inl (Or.inr ⟨k, hk, rfl⟩)
  have hB : ∀ k, k < 8 → Bbody pfx s!"{pfx ++ "B"}h{k}" := fun k hk => Or.inr ⟨k, hk, rfl⟩
  have hmap := transFrom_mapRange (fun k => s!"{pfx}Sel{k}")
    (fun k => (.SXor (sv s!"{pfx ++ "B"}h{k}")
      (.SAnd (.SXor (sv s!"{pfx ++ "A"}h{k}") (sv s!"{pfx ++ "B"}h{k}"))
        (.SMul (sv s!"{pfx}bit") (.SLit 4294967295))) : SExpr))
    hstep2 8
    (fun k _ => ((hpfx.append "Sel").append _).bindOk)
    (fun k hk => readsFrom_xor
      (readsFrom_var (hsrc _ (hB k hk)) (Or.inl (Or.inl (hB k hk))))
      (readsFrom_and
        (readsFrom_xor
          (readsFrom_var (hsrc _ (hA k hk)) (Or.inl (Or.inl (hA k hk))))
          (readsFrom_var (hsrc _ (hB k hk)) (Or.inl (Or.inl (hB k hk)))))
        (readsFrom_mul (readsFrom_var hbit.1 (Or.inr rfl))
          (readsFrom_lit (by norm_num)))))
  refine ⟨_, ?_, fun x hx => Or.inl (Or.inl (Or.inl hx)), hmap, ?_⟩
  · rintro y ((((hy | rfl) | rfl) | ⟨k, hk, rfl⟩))
    · exact hsrc y hy
    · exact hix.1
    · exact hbit.1
    · exact ((hpfx.append "Sel").append _).notTmp
  · intro k hk
    have hk8 : k < 8 := by simpa [selBody] using hk
    rw [show (selBody fw cbit pfx).2[k]! = s!"{pfx}Sel{k}" from by
      simp only [selBody]; exact map_range_getBang 8 _ k hk8]
    exact Or.inr ⟨k, hk8, rfl⟩

/-- **A framed select brick walks from the frame alone.** -/
theorem selfWalk_emitSelectFramed (fw : Nat) (slotOf : String → Nat) (idx : Nat)
    (s a b o : String) (henc : encodeTy (.TBytes fw) = CryptoTy.memref 256)
    (ha : 4 * slotOf a + 3 < 2 ^ 64) (hb : 4 * slotOf b + 3 < 2 ^ 64)
    (ho : 4 * slotOf o + 3 < 2 ^ 64) (hs : 4 * slotOf s < 2 ^ 64) :
    SelfWalk (emitSelectFramed fw slotOf idx s a b o) := by
  have hpfx : NameOk s!"fop{idx}" :=
    ⟨HeadOk.append (⟨'f', ['o', 'p'], rfl, by decide⟩ : HeadOk "fop") _,
     Long2.append (show (2 : Nat) ≤ "fop".length by decide) _⟩
  exact transFrom_framedAssemble fw (slotOf a) (slotOf b) (slotOf o) _ hpfx henc ha hb ho
    (selBody fw (4 * slotOf s) s!"fop{idx}").1 (selBody fw (4 * slotOf s) s!"fop{idx}").2
    (by simp [selBody])
    (selBody_trans fw (4 * slotOf s) s!"fop{idx}" hpfx hs)

/-- The per-trip key-bit fetch's three scratch names. -/
theorem nameOk_ladixkey : NameOk "ladixkey" :=
  ⟨⟨'l', ['a', 'd', 'i', 'x', 'k', 'e', 'y'], rfl, by decide⟩,
   (by decide : 2 ≤ "ladixkey".length)⟩

theorem nameOk_ladkeybit : NameOk "ladkeybit" :=
  ⟨⟨'l', ['a', 'd', 'k', 'e', 'y', 'b', 'i', 't'], rfl, by decide⟩,
   (by decide : 2 ≤ "ladkeybit".length)⟩

theorem nameOk_ladixbit : NameOk "ladixbit" :=
  ⟨⟨'l', ['a', 'd', 'i', 'x', 'b', 'i', 't'], rfl, by decide⟩,
   (by decide : 2 ≤ "ladixbit".length)⟩

/-- The ladder frame's byte width encodes as the 256-cell memref type. -/
theorem encodeTy_ladderFrame :
    encodeTy (.TBytes (8 * ladderFrameCells)) = CryptoTy.memref 256 := rfl

/-- **The per-trip key-bit fetch is reads-bound** from the loop index alone. -/
theorem transFrom_ladderBitFetch :
    ∃ W : String → Prop, SrcSet W ∧ TransFrom (fun y => y = "i") W ladderBitFetch := by
  have hi : ¬ isTmpName "i" := notTmp_of_len "i" (by decide)
  have h1 := transFrom_snoc (transFrom_nil (fun y => y = "i")) nameOk_ladixkey.bindOk
    (readsFrom_add (readsFrom_var hi rfl)
      (readsFrom_lit (show ladderBitBase < 2 ^ 64 by decide)))
  have h2 := transFrom_append h1
    (transFrom_arrLoad1 (d := "ladkeybit") (ix := "ladixkey") (8 * ladderFrameCells)
      nameOk_ladkeybit.bindOk)
    (fun x hx => Or.inr (hx ▸ Or.inr rfl))
  have h3 := transFrom_snoc h2 nameOk_ladixbit.bindOk
    (readsFrom_lit (show 4 * slotLadSel "bit" < 2 ^ 64 by decide))
  have h4 := transFrom_append h3
    (transFrom_arrStore1 (ix := "ladixbit") (s := "ladkeybit") (8 * ladderFrameCells)
      encodeTy_ladderFrame)
    (fun x hx => hx.elim (fun h => Or.inr (h ▸ Or.inr rfl))
      (fun h => Or.inr (h ▸ Or.inl (Or.inr rfl))))
  refine ⟨_, ?_, h4⟩
  rintro y ((((hy | rfl) | rfl) | rfl) | hy)
  · exact hy ▸ hi
  · exact nameOk_ladixkey.notTmp
  · exact nameOk_ladkeybit.notTmp
  · exact nameOk_ladixbit.notTmp
  · exact hy.elim

/-! ## 11. The framed ladder step and the front-success gate -/

/-- **The select trip walks from the frame alone**, at the concrete
    `slotLadSel` cell indices. -/
theorem selfWalk_selectTrip : SelfWalk selectTrip := by
  refine selfWalk_append (selfWalk_append ?_ ?_) ?_
  all_goals
    exact selfWalk_emitSelectFramed (8 * ladderFrameCells) slotLadSel _ _ _ _ _
      encodeTy_ladderFrame (by decide) (by decide) (by decide) (by decide)

/-- **The doubling bricks walk from the frame alone**, at the `slotLadDbl` cell
    indices. -/
theorem selfWalk_ladderDbl :
    SelfWalk ((jacDblSchedule.mapIdx
      (fun i op => emitFOpFramed (8 * ladderFrameCells) "F" slotLadDbl i op)).flatten) :=
  selfWalk_mapIdxFlatten _ _ (fun i op =>
    selfWalk_emitFOpFramed _ _ i op encodeTy_ladderFrame slotLadDbl_lt)

/-- **The addition bricks walk from the frame alone**, at the `slotLadAdd` cell
    indices. -/
theorem selfWalk_ladderAdd :
    SelfWalk ((jacAddSchedule.mapIdx
      (fun i op => emitFOpFramed (8 * ladderFrameCells) "F" slotLadAdd i op)).flatten) :=
  selfWalk_mapIdxFlatten _ _ (fun i op =>
    selfWalk_emitFOpFramed _ _ i op encodeTy_ladderFrame slotLadAdd_lt)

/-- **The framed ladder step's command list is reads-bound** from the loop
    index alone: the key-bit fetch reads it, and the doubling bricks, the
    addition bricks and the select trip bind everything else they read. -/
theorem transFrom_ladderStepList :
    ∃ W : String → Prop, SrcSet W ∧ TransFrom (fun y => y = "i") W
      (ladderBitFetch
        ++ (jacDblSchedule.mapIdx
          (fun i op => emitFOpFramed (8 * ladderFrameCells) "F" slotLadDbl i op)).flatten
        ++ (jacAddSchedule.mapIdx
          (fun i op => emitFOpFramed (8 * ladderFrameCells) "F" slotLadAdd i op)).flatten
        ++ selectTrip) := by
  obtain ⟨W0, hs0, hr0⟩ := transFrom_ladderBitFetch
  obtain ⟨W1, hs1, hr1⟩ := transFrom_snocSelf hr0 selfWalk_ladderDbl hs0
  obtain ⟨W2, hs2, hr2⟩ := transFrom_snocSelf hr1 selfWalk_ladderAdd hs1
  exact transFrom_snocSelf hr2 selfWalk_selectTrip hs2

/-- The loop-body entry map: the frame at the 256-cell memref type, the loop
    index at 64-bit word type, nothing else claimed. -/
noncomputable def ladderEntryTys : NameTys := nameTysOf (fun y => y = "i")

/-- The entry map claims no fresh temporary. -/
theorem srcTys_ladderEntryTys : SrcTys ladderEntryTys :=
  srcTys_nameTysOf (fun x hx => hx ▸ notTmp_of_len "i" (by decide))

/-- A claim of a ladder-shaped map is either the frame at the memref type or a
    word-set name at word type. -/
theorem nameTysOf_eq_some {C : String → Prop} {x : String} {t : CryptoTy}
    (h : nameTysOf C x = some t) :
    (x = "F" ∧ t = CryptoTy.memref 256) ∨ (x ≠ "F" ∧ C x ∧ t = CryptoTy.sword 64) := by
  by_cases hxF : x = "F"
  · subst hxF
    rw [nameTysOf_frame] at h
    exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  · by_cases hC : C x
    · rw [nameTysOf_mem hC hxF] at h
      exact Or.inr ⟨hxF, hC, (Option.some.inj h).symm⟩
    · exact absurd h (by simp [nameTysOf, hxF, hC])

/-- The entry map lower-bounds the ladder loop-body `VarMap`. -/
theorem vmApprox_ladderVMBody : VmApprox ladderEntryTys ladderVMBody := by
  intro x t hx
  rcases nameTysOf_eq_some (C := fun y => y = "i") hx with ⟨rfl, rfl⟩ | ⟨hxF, rfl, rfl⟩
  · exact boundAt_bind_self _ "F" _
  · exact boundAt_bind_of_ne "F" (.memref 256) hxF
      (boundAt_bind_self VarMap.empty "i" (.sword 64))

/-- **The framed ladder step carries a reads-bound derivation** from the loop-body
    entry map, and its exit map claims the frame at the accumulator type. -/
theorem ladderStepFramed_transTotal :
    ∃ σ' : NameTys, TransTotal ladderEntryTys ladderStepFramed σ'
      ∧ σ' "F" = some (.memref 256) := by
  obtain ⟨W, -, hr⟩ := transFrom_ladderStepList
  obtain ⟨D, -, -, -, -, hts⟩ := hr (fun y => y = "i")
    (fun x hx => hx ▸ notTmp_of_len "i" (by decide)) (by decide) (fun _ h => h)
  exact ⟨nameTysOf D, transSteps_seqAll hts, nameTysOf_frame D⟩

/-- **The scalar rolled-loop front accepts the framed ladder step**: the
    `LadderTripFrontSpec.LadderStepFrontOk` gate holds, with no evaluation of
    the step's command list. -/
theorem ladderStepFrontOk : LadderStepFrontOk := by
  obtain ⟨σ', hT, hacc⟩ := ladderStepFramed_transTotal
  exact frontLoopBodyJ_total (accCTy := .memref 256) ladderVMBody "F" ladderStepFramed
    hT srcTys_ladderEntryTys vmApprox_ladderVMBody hacc

end CatCrypt.Crypto.SecureCompilation.X86Backend.LadderStepFrontOkProof
