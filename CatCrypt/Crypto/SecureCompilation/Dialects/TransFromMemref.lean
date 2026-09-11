/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality

/-!
# The reads-bound walk over multi-memref name-to-type maps

`TranslateDialectTotality.frontLoopBodyJ_total` reduces the rolled-loop front's
success gate `(frontLoopBodyJ …).isSome` to a `TransTotal` derivation of the
reads-bound judgment. This module carries the walk layer that assembles such a
derivation for a straight-line body, generalized from the single-frame form in
`X86Backend/LadderStepFrontOkProof` to a **set** of memref names, each claimed
at its own memref type.

The map shape is `nameTysM Mem C`: a fixed memref-name map `Mem : String →
Option CryptoTy` claiming each memref name at its type, and a growing word set
`C` claiming every other bound name at `.sword 64`. The walk keeps `C` disjoint
from the memref domain, so a word binding grows `C` and a memref store rebinds
its name at its own type, fixing the shape.

## Main results

* `SrcSet` / `ReadsFrom` and the expression builders — the temp-freshness and
  reads-bound predicates over the covered `SExpr` fragment.
* `notTmp_of_headNe` — a name whose first character is not `_` is not a fresh
  temporary.
* `TransSteps` / `TransSteps.append` — the list form of `TransTotal`.
* `nameTysM` and its update laws (`nameTysM_mem` / `nameTysM_word` /
  `nameTysM_upd_word` / `nameTysM_upd_mem` / `srcTys_nameTysM`).
* `TransFromM` and its combinators (`transFromM_nil` / `transFromM_mono` /
  `transFromM_append` / `transFromM_trans` / `transFromM_setExpr` /
  `transFromM_snoc` / `transFromM_snoc3` / `transFromM_arrLoad1` /
  `transFromM_arrStore1` and their snoc forms) — the reads-bound walk over a
  command list.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TransFromMemref

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (encodeTy)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
  (isTmpName srcClean)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
  (NameTys TransTotal SrcTys VmApprox BoundAt boundAt_bind_self boundAt_bind_of_ne)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr Located)

/-! ## 1. Temp-freshness and reads-bound predicates -/

/-- A name set outside the front's reserved fresh-temporary namespace. -/
def SrcSet (B : String → Prop) : Prop := ∀ x, B x → ¬ isTmpName x

theorem srcSet_or {W : String → Prop} {x : String} (hW : SrcSet W) (hx : ¬ isTmpName x) :
    SrcSet (fun y => W y ∨ y = x) := by
  rintro y (h | rfl)
  · exact hW y h
  · exact hx

/-- A name whose first character is not `_` is not a fresh temporary. -/
theorem notTmp_of_headNe {s : String} {c : Char} {t : List Char}
    (hs : s.toList = c :: t) (hc : c ≠ '_') : ¬ isTmpName s := by
  rintro ⟨k, hk⟩
  have hd := congrArg String.toList hk
  rw [CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectArms.tmpName,
      String.toList_append, hs] at hd
  simp only [show "__sx".toList = ['_', '_', 's', 'x'] from rfl,
    List.cons_append, List.nil_append] at hd
  injection hd with h1 _
  exact hc h1

/-- A `srcClean` expression all of whose `SVar` leaves lie in `R`. -/
def ReadsFrom (R : String → Prop) (e : SExpr) : Prop :=
  srcClean e ∧ ∀ s ∈ sexprVars e, R s

theorem readsFrom_mono {R R' : String → Prop} {e : SExpr} (h : ReadsFrom R e)
    (hr : ∀ x, R x → R' x) : ReadsFrom R' e :=
  ⟨h.1, fun s hs => hr s (h.2 s hs)⟩

theorem readsFrom_var {R : String → Prop} {x : String} (hnt : ¬ isTmpName x) (hx : R x) :
    ReadsFrom R (SExpr.SVar x) := by
  refine ⟨hnt, fun s hs => ?_⟩
  simp only [sexprVars, List.mem_cons, List.not_mem_nil, or_false] at hs
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

theorem readsFrom_shr {R : String → Prop} {a b : SExpr} (ha : ReadsFrom R a)
    (hb : ReadsFrom R b) : ReadsFrom R (SExpr.SShr a b) :=
  ⟨⟨ha.1, hb.1⟩, fun s hs => by
    simp only [sexprVars, List.mem_append] at hs; exact hs.elim (ha.2 s) (hb.2 s)⟩

theorem readsFrom_shl {R : String → Prop} {a b : SExpr} (ha : ReadsFrom R a)
    (hb : ReadsFrom R b) : ReadsFrom R (SExpr.SShl a b) :=
  ⟨⟨ha.1, hb.1⟩, fun s hs => by
    simp only [sexprVars, List.mem_append] at hs; exact hs.elim (ha.2 s) (hb.2 s)⟩

/-! ## 2. The judgment on command lists -/

/-- The reads-bound judgment threaded through a command list. -/
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

/-! ## 3. Multi-memref name-to-type maps -/

open Classical in
/-- The name-to-type map claiming each memref name of `Mem` at its type and every
    name of the word set `C` at 64-bit word type. -/
noncomputable def nameTysM (Mem : String → Option CryptoTy) (C : String → Prop) :
    NameTys :=
  fun x => match Mem x with
    | some t => some t
    | none => if C x then some (.sword 64) else none

theorem nameTysM_mem {Mem : String → Option CryptoTy} {C : String → Prop}
    {x : String} {t : CryptoTy} (h : Mem x = some t) : nameTysM Mem C x = some t := by
  simp [nameTysM, h]

theorem nameTysM_word {Mem : String → Option CryptoTy} {C : String → Prop}
    {x : String} (hm : Mem x = none) (hc : C x) :
    nameTysM Mem C x = some (.sword 64) := by
  simp [nameTysM, hm, hc]

theorem nameTysM_isSome_of_mem {Mem : String → Option CryptoTy} {C : String → Prop}
    {x : String} {t : CryptoTy} (h : Mem x = some t) :
    (nameTysM Mem C x).isSome := by rw [nameTysM_mem h]; rfl

theorem nameTysM_none {Mem : String → Option CryptoTy} {C : String → Prop}
    {x : String} (hm : Mem x = none) (hc : ¬ C x) : nameTysM Mem C x = none := by
  simp [nameTysM, hm, hc]

theorem nameTysM_isSome_of_word {Mem : String → Option CryptoTy} {C : String → Prop}
    {x : String} (hc : C x) : (nameTysM Mem C x).isSome := by
  unfold nameTysM
  cases hm : Mem x with
  | none => simp [hc]
  | some t => rfl

/-- A word binding away from the memref domain grows the word set. -/
theorem nameTysM_upd_word {Mem : String → Option CryptoTy} {C : String → Prop}
    {x : String} (hm : Mem x = none) :
    (nameTysM Mem C).upd x (.sword 64) = nameTysM Mem (fun y => C y ∨ y = x) := by
  funext y
  by_cases hyx : y = x
  · subst hyx
    simp [CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality.NameTys.upd,
      nameTysM, hm]
  · simp only [CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality.NameTys.upd,
      if_neg hyx, nameTysM]
    cases Mem y with
    | none => by_cases hc : C y <;> simp [hyx, hc]
    | some t => rfl

/-- Rebinding a memref name at its own type fixes the map. -/
theorem nameTysM_upd_mem {Mem : String → Option CryptoTy} {C : String → Prop}
    {x : String} {t : CryptoTy} (h : Mem x = some t) :
    (nameTysM Mem C).upd x t = nameTysM Mem C := by
  funext y
  by_cases hyx : y = x
  · subst hyx
    simp [CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality.NameTys.upd,
      nameTysM, h]
  · simp only [CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality.NameTys.upd,
      if_neg hyx]

/-- A multi-memref map claims no fresh temporary when neither its memref names
    nor its word set do. -/
theorem srcTys_nameTysM {Mem : String → Option CryptoTy} {C : String → Prop}
    (hMem : ∀ x t, Mem x = some t → ¬ isTmpName x) (hC : SrcSet C) :
    SrcTys (nameTysM Mem C) := by
  intro x hx
  unfold nameTysM at hx
  cases hm : Mem x with
  | none =>
      rw [hm] at hx
      by_cases hxC : C x
      · exact hC x hxC
      · simp [hxC] at hx
  | some t => exact hMem x t hm

/-! ## 4. The reads-bound walk -/

/-- The reads-bound walk triple over multi-memref maps: from any temporary-free
    word set `C` extending `B` and disjoint from the memref domain, the list
    carries a `TransSteps` walk to a map of the same shape whose word set extends
    `C` and binds `W`. -/
def TransFromM (Mem : String → Option CryptoTy) (B W : String → Prop)
    (l : List LowCT) : Prop :=
  ∀ C : String → Prop, SrcSet C → (∀ x, C x → Mem x = none) → (∀ x, B x → C x) →
    ∃ D : String → Prop, SrcSet D ∧ (∀ x, D x → Mem x = none) ∧ (∀ x, C x → D x)
      ∧ (∀ x, W x → D x) ∧ TransSteps (nameTysM Mem C) l (nameTysM Mem D)

variable {Mem : String → Option CryptoTy}

theorem transFromM_nil (B : String → Prop) : TransFromM Mem B B [] :=
  fun C hs hCm hb => ⟨C, hs, hCm, fun _ h => h, hb, .nil _⟩

/-- Strengthening the entry set and weakening the exit set. -/
theorem transFromM_mono {B B₂ W W₂ : String → Prop} {l : List LowCT}
    (h : TransFromM Mem B W l) (hB : ∀ x, B x → B₂ x) (hW : ∀ x, W₂ x → W x) :
    TransFromM Mem B₂ W₂ l := by
  intro C hs hCm hb
  obtain ⟨D, hsD, hDm, hCD, hWD, hts⟩ := h C hs hCm (fun x hx => hb x (hB x hx))
  exact ⟨D, hsD, hDm, hCD, fun x hx => hWD x (hW x hx), hts⟩

/-- **Two blocks in sequence.** The second block's entry set may draw on the
    first block's exit set. -/
theorem transFromM_append {B W₁ B' W₂ : String → Prop} {l₁ l₂ : List LowCT}
    (h₁ : TransFromM Mem B W₁ l₁) (h₂ : TransFromM Mem B' W₂ l₂)
    (hsub : ∀ x, B' x → B x ∨ W₁ x) :
    TransFromM Mem B (fun x => W₁ x ∨ W₂ x) (l₁ ++ l₂) := by
  intro C hs hCm hb
  obtain ⟨D₁, hs₁, hDm₁, hCD₁, hW₁, hts₁⟩ := h₁ C hs hCm hb
  obtain ⟨D₂, hs₂, hDm₂, hD₁₂, hW₂, hts₂⟩ :=
    h₂ D₁ hs₁ hDm₁ (fun x hx => (hsub x hx).elim (fun h => hCD₁ x (hb x h)) (hW₁ x))
  exact ⟨D₂, hs₂, hDm₂, fun x hx => hD₁₂ x (hCD₁ x hx),
    fun x hx => hx.elim (fun h => hD₁₂ x (hW₁ x h)) (hW₂ x), hts₁.append hts₂⟩

/-- Two blocks in sequence, the second entered at the first's exit set. -/
theorem transFromM_trans {B W₁ W₂ : String → Prop} {l₁ l₂ : List LowCT}
    (h₁ : TransFromM Mem B W₁ l₁) (h₂ : TransFromM Mem W₁ W₂ l₂) :
    TransFromM Mem B W₂ (l₁ ++ l₂) :=
  transFromM_mono (transFromM_append h₁ h₂ (fun _ hx => Or.inr hx)) (fun _ h => h)
    (fun _ hx => Or.inr hx)

/-- **One scalar assignment.** The bound name is outside the fresh-temp namespace
    and off the memref domain; the expression reads from the entry set. -/
theorem transFromM_setExpr {R : String → Prop} {x : String} {e : SExpr}
    (hx : ¬ isTmpName x) (hxm : Mem x = none) (hrd : ReadsFrom R e) :
    TransFromM Mem R (fun y => y = x) [LowCT.RScalarSetExpr x e] := by
  intro C hs hCm hb
  refine ⟨fun y => C y ∨ y = x, srcSet_or hs hx, ?_, fun y hy => Or.inl hy,
    fun y hy => Or.inr hy, ?_⟩
  · rintro y (h | rfl)
    · exact hCm y h
    · exact hxm
  · have harm : TransTotal (nameTysM Mem C) (.RScalarSetExpr x e)
        ((nameTysM Mem C).upd x (.sword 64)) :=
      TransTotal.rScalarSetExpr x e hx hrd.1 (fun y hy =>
        nameTysM_word (hCm y (hb y (hrd.2 y hy))) (hb y (hrd.2 y hy)))
    exact nameTysM_upd_word hxm ▸ TransSteps.cons harm (.nil _)

/-- **One dynamic-index memref load** into a `u64` destination: the memref name is
    claimed by `Mem`, the index is a bound word, the destination is bound at
    `.sword 64`. -/
theorem transFromM_arrLoad1 {d m ix : String} {mty : CatCrypt.Crypto.Jasmin.LowCT.TowerType}
    {tm : CryptoTy} (hd : ¬ isTmpName d) (hdm : Mem d = none) (hmem : Mem m = some tm) :
    TransFromM Mem (fun y => y = ix) (fun y => y = d)
      [LowCT.RArrLoad ⟨d, .TU64⟩ ⟨m, mty⟩ ix] := by
  intro C hs hCm hb
  refine ⟨fun y => C y ∨ y = d, srcSet_or hs hd, ?_, fun y hy => Or.inl hy,
    fun y hy => Or.inr hy, ?_⟩
  · rintro y (h | rfl)
    · exact hCm y h
    · exact hdm
  · have hix : (nameTysM Mem C ix).isSome := nameTysM_isSome_of_word (hb ix rfl)
    have harm : TransTotal (nameTysM Mem C) (.RArrLoad ⟨d, .TU64⟩ ⟨m, mty⟩ ix)
        ((nameTysM Mem C).upd d (.sword 64)) :=
      TransTotal.rArrLoad ⟨d, .TU64⟩ ⟨m, mty⟩ ix hd (nameTysM_isSome_of_mem hmem) hix
    exact nameTysM_upd_word hdm ▸ TransSteps.cons harm (.nil _)

/-- **One dynamic-index memref store** of a bound `u64` word at a bound index into
    a memref name of `Mem`, rebinding it at its own type. -/
theorem transFromM_arrStore1 {m ix s : String}
    {mty : CatCrypt.Crypto.Jasmin.LowCT.TowerType} {tm : CryptoTy}
    (hmt : ¬ isTmpName m) (hmem : Mem m = some tm) (henc : encodeTy mty = tm) :
    TransFromM Mem (fun y => y = ix ∨ y = s) (fun _ => False)
      [LowCT.RArrStore ⟨m, mty⟩ ix ⟨s, .TU64⟩] := by
  intro C hs hCm hb
  refine ⟨C, hs, hCm, fun _ h => h, fun _ h => h.elim, ?_⟩
  have hix : (nameTysM Mem C ix).isSome := nameTysM_isSome_of_word (hb ix (Or.inl rfl))
  have hsrc : (nameTysM Mem C s).isSome := nameTysM_isSome_of_word (hb s (Or.inr rfl))
  have harm : TransTotal (nameTysM Mem C) (.RArrStore ⟨m, mty⟩ ix ⟨s, .TU64⟩)
      ((nameTysM Mem C).upd m (encodeTy mty)) :=
    TransTotal.rArrStore ⟨m, mty⟩ ix ⟨s, .TU64⟩ hmt (nameTysM_isSome_of_mem hmem) hsrc hix
  rw [henc, nameTysM_upd_mem hmem] at harm
  exact TransSteps.cons harm (.nil _)

/-- **A block extended by one scalar assignment** whose reads lie in the block's
    exit set. -/
theorem transFromM_snoc {B W : String → Prop} {l : List LowCT} {x : String} {e : SExpr}
    (h : TransFromM Mem B W l) (hx : ¬ isTmpName x) (hxm : Mem x = none)
    (hrd : ReadsFrom W e) :
    TransFromM Mem B (fun y => W y ∨ y = x) (l ++ [LowCT.RScalarSetExpr x e]) :=
  transFromM_append h
    (transFromM_setExpr (R := fun s => B s ∨ W s) hx hxm
      (readsFrom_mono hrd (fun _ hx => Or.inr hx)))
    (fun _ hs => hs)

/-- A block extended by three scalar assignments. -/
theorem transFromM_snoc3 {B W : String → Prop} {l : List LowCT} {x₁ x₂ x₃ : String}
    {e₁ e₂ e₃ : SExpr} (h : TransFromM Mem B W l)
    (h₁ : ¬ isTmpName x₁) (h₁m : Mem x₁ = none)
    (h₂ : ¬ isTmpName x₂) (h₂m : Mem x₂ = none)
    (h₃ : ¬ isTmpName x₃) (h₃m : Mem x₃ = none)
    (r₁ : ReadsFrom W e₁)
    (r₂ : ReadsFrom (fun y => W y ∨ y = x₁) e₂)
    (r₃ : ReadsFrom (fun y => (W y ∨ y = x₁) ∨ y = x₂) e₃) :
    TransFromM Mem B (fun y => ((W y ∨ y = x₁) ∨ y = x₂) ∨ y = x₃)
      (l ++ [LowCT.RScalarSetExpr x₁ e₁, LowCT.RScalarSetExpr x₂ e₂,
             LowCT.RScalarSetExpr x₃ e₃]) := by
  have hlist : l ++ [LowCT.RScalarSetExpr x₁ e₁, LowCT.RScalarSetExpr x₂ e₂,
        LowCT.RScalarSetExpr x₃ e₃]
      = ((l ++ [LowCT.RScalarSetExpr x₁ e₁]) ++ [LowCT.RScalarSetExpr x₂ e₂])
        ++ [LowCT.RScalarSetExpr x₃ e₃] := by simp
  rw [hlist]
  exact transFromM_snoc (transFromM_snoc (transFromM_snoc h h₁ h₁m r₁) h₂ h₂m r₂) h₃ h₃m r₃

/-- **A block extended by one memref load** whose index lies in the block's exit
    set. -/
theorem transFromM_snocLoad {B W : String → Prop} {l : List LowCT} {d m ix : String}
    {mty : CatCrypt.Crypto.Jasmin.LowCT.TowerType} {tm : CryptoTy}
    (h : TransFromM Mem B W l) (hd : ¬ isTmpName d) (hdm : Mem d = none)
    (hmem : Mem m = some tm) (hix : W ix) :
    TransFromM Mem B (fun y => W y ∨ y = d)
      (l ++ [LowCT.RArrLoad ⟨d, .TU64⟩ ⟨m, mty⟩ ix]) :=
  transFromM_append h (transFromM_arrLoad1 hd hdm hmem)
    (fun x hx => Or.inr (hx ▸ hix))

/-- **A block extended by one memref store** whose index and source lie in the
    block's exit set. -/
theorem transFromM_snocStore {B W : String → Prop} {l : List LowCT} {m ix s : String}
    {mty : CatCrypt.Crypto.Jasmin.LowCT.TowerType} {tm : CryptoTy}
    (h : TransFromM Mem B W l) (hmt : ¬ isTmpName m) (hmem : Mem m = some tm)
    (henc : encodeTy mty = tm) (hix : W ix) (hsrc : W s) :
    TransFromM Mem B W (l ++ [LowCT.RArrStore ⟨m, mty⟩ ix ⟨s, .TU64⟩]) :=
  transFromM_mono
    (transFromM_append h (transFromM_arrStore1 hmt hmem henc)
      (fun x hx => hx.elim (fun h => Or.inr (h ▸ hix)) (fun h => Or.inr (h ▸ hsrc))))
    (fun _ h => h) (fun x hx => Or.inl hx)

end CatCrypt.Crypto.SecureCompilation.Dialects.TransFromMemref
