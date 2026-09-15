/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FrontLoopBodyArrMemNWalk
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontDenote
public import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontTotal

/-!
# The front-compiled `mpn_cmp` limb body is an `ArrMemN` member

`FrontLoopBodyArrMemNWalk.frontLoopBodyJ_arrMemN_of_judged` reduces
`ArrMemN cmpUpdate` to a `TransArrN` derivation of the `mpn_cmp` limb body over
the three-memref name-to-type map, together with the entry-map / accumulator
facts already established for the front-success gate.

This module assembles that `TransArrN` derivation by a reads-bound walk over the
body's command list — the memref-typed twin of `MpnCmpFrontTotal.cmpFrontOk`,
built from a `TransFromArr` combinator layer mirroring the `TransFromM` layer of
`Dialects.TransFromMemref` with `TransArrN` in place of `TransTotal`. Feeding the
derivation to the end lemma closes `ArrMemN cmpUpdate`, with no reduction of the
body command list.

## Main results

* `cmpLimbBody_transArrN` — `TransArrN (nameTysM cmpMem cmpB0) cmpLimbBodyLowCT`
  to a map of the same shape.
* `cmpUpdate_arrMemN` — the front-compiled `mpn_cmp` limb body is a member of the
  array-returning stack-memory fragment `ArrMemN`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpArrMemN

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA (encodeTy)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar (isTmpName srcClean notTmp_of_headNe)
open CatCrypt.Crypto.SecureCompilation.Dialects.CarryChainSelect (sexprVars)
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectTotality
  (NameTys SrcTys VmApprox)
open CatCrypt.Crypto.SecureCompilation.Dialects.TransFromMemref
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemSourceTieArrUncond (ArrMemN)
open CatCrypt.Crypto.SecureCompilation.VIR.FrontLoopBodyArrMemNWalk
  (TransArrN frontLoopBodyJ_arrMemN_of_judged)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontTotal
  (cmpMem cmpMem_rp cmpMem_ap cmpMem_bp cmpB0 cmpB0_srcSet cmpB0_disjoint
   cmpMem_notTmp vmApprox_cmp)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnMul1FrontEmit
  (seqAll sv ltuCmds notE orE ones)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontEmit
  (cmpLimbBodyLowCT vmBody NR NU apLoc bpLoc rpLoc)
open CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpFrontDenote (cmpUpdate cmpUpdate_eq)
open CatCrypt.Crypto.Jasmin.LowCT (LowCT SExpr TowerType Located)

/-! ## 1. The memref-typed reads-bound list walk -/

/-- The list form of `TransArrN`: a per-command sequencing to a threaded map. -/
inductive TransStepsArr : NameTys → List LowCT → NameTys → Prop
  | nil (σ : NameTys) : TransStepsArr σ [] σ
  | cons {σ σ₁ σ₂ : NameTys} {c : LowCT} {l : List LowCT} :
      TransArrN σ c σ₁ → TransStepsArr σ₁ l σ₂ → TransStepsArr σ (c :: l) σ₂

theorem TransStepsArr.append {σ₂ : NameTys} :
    ∀ {l₁ : List LowCT} {σ σ₁ : NameTys} {l₂ : List LowCT},
      TransStepsArr σ l₁ σ₁ → TransStepsArr σ₁ l₂ σ₂ → TransStepsArr σ (l₁ ++ l₂) σ₂ := by
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

/-- A `TransStepsArr` walk of a list is a `TransArrN` derivation of its `seqAll`
    sequencing. -/
theorem transStepsArr_seqAll : ∀ {l : List LowCT} {σ σ' : NameTys},
    TransStepsArr σ l σ' → TransArrN σ (seqAll l) σ'
  | [], _, _, h => by cases h; exact .rSkip
  | [_], _, _, h => by
      cases h with
      | cons hc ht => cases ht; exact hc
  | _ :: _ :: _, _, _, h => by
      cases h with
      | cons hc ht => exact .rSeq hc (transStepsArr_seqAll ht)

/-! ## 2. The reads-bound walk over multi-memref maps -/

/-- The memref-typed reads-bound walk triple: the `TransArrN` twin of
    `TransFromM`, producing a `TransStepsArr` walk over the command list. -/
def TransFromArr (Mem : String → Option CryptoTy) (B W : String → Prop)
    (l : List LowCT) : Prop :=
  ∀ C : String → Prop, SrcSet C → (∀ x, C x → Mem x = none) → (∀ x, B x → C x) →
    ∃ D : String → Prop, SrcSet D ∧ (∀ x, D x → Mem x = none) ∧ (∀ x, C x → D x)
      ∧ (∀ x, W x → D x) ∧ TransStepsArr (nameTysM Mem C) l (nameTysM Mem D)

variable {Mem : String → Option CryptoTy}

theorem transFromArr_nil (B : String → Prop) : TransFromArr Mem B B [] :=
  fun C hs hCm hb => ⟨C, hs, hCm, fun _ h => h, hb, .nil _⟩

/-- Strengthening the entry set and weakening the exit set. -/
theorem transFromArr_mono {B B₂ W W₂ : String → Prop} {l : List LowCT}
    (h : TransFromArr Mem B W l) (hB : ∀ x, B x → B₂ x) (hW : ∀ x, W₂ x → W x) :
    TransFromArr Mem B₂ W₂ l := by
  intro C hs hCm hb
  obtain ⟨D, hsD, hDm, hCD, hWD, hts⟩ := h C hs hCm (fun x hx => hb x (hB x hx))
  exact ⟨D, hsD, hDm, hCD, fun x hx => hWD x (hW x hx), hts⟩

/-- **Two blocks in sequence.** The second block's entry set may draw on the
    first block's exit set. -/
theorem transFromArr_append {B W₁ B' W₂ : String → Prop} {l₁ l₂ : List LowCT}
    (h₁ : TransFromArr Mem B W₁ l₁) (h₂ : TransFromArr Mem B' W₂ l₂)
    (hsub : ∀ x, B' x → B x ∨ W₁ x) :
    TransFromArr Mem B (fun x => W₁ x ∨ W₂ x) (l₁ ++ l₂) := by
  intro C hs hCm hb
  obtain ⟨D₁, hs₁, hDm₁, hCD₁, hW₁, hts₁⟩ := h₁ C hs hCm hb
  obtain ⟨D₂, hs₂, hDm₂, hD₁₂, hW₂, hts₂⟩ :=
    h₂ D₁ hs₁ hDm₁ (fun x hx => (hsub x hx).elim (fun h => hCD₁ x (hb x h)) (hW₁ x))
  exact ⟨D₂, hs₂, hDm₂, fun x hx => hD₁₂ x (hCD₁ x hx),
    fun x hx => hx.elim (fun h => hD₁₂ x (hW₁ x h)) (hW₂ x), hts₁.append hts₂⟩

/-- **One scalar assignment.** The bound name is outside the fresh-temp namespace
    and off the memref domain; the expression reads from the entry set. -/
theorem transFromArr_setExpr {R : String → Prop} {x : String} {e : SExpr}
    (hx : ¬ isTmpName x) (hxm : Mem x = none) (hrd : ReadsFrom R e) :
    TransFromArr Mem R (fun y => y = x) [LowCT.RScalarSetExpr x e] := by
  intro C hs hCm hb
  refine ⟨fun y => C y ∨ y = x, srcSet_or hs hx, ?_, fun y hy => Or.inl hy,
    fun y hy => Or.inr hy, ?_⟩
  · rintro y (h | rfl)
    · exact hCm y h
    · exact hxm
  · have harm : TransArrN (nameTysM Mem C) (.RScalarSetExpr x e)
        ((nameTysM Mem C).upd x (.sword 64)) :=
      TransArrN.rScalarSetExpr x e hx hrd.1 (fun y hy =>
        nameTysM_word (hCm y (hb y (hrd.2 y hy))) (hb y (hrd.2 y hy)))
    exact nameTysM_upd_word hxm ▸ TransStepsArr.cons harm (.nil _)

/-- **One dynamic-index memref load** into a `u64` destination: the memref name is
    claimed by `Mem` at `.memref n`, the index is a bound word, the destination is
    bound at `.sword 64`. -/
theorem transFromArr_arrLoad1 {d m ix : String} {mty : TowerType} {n : Nat}
    (hd : ¬ isTmpName d) (hdm : Mem d = none) (hmem : Mem m = some (.memref n)) :
    TransFromArr Mem (fun y => y = ix) (fun y => y = d)
      [LowCT.RArrLoad ⟨d, .TU64⟩ ⟨m, mty⟩ ix] := by
  intro C hs hCm hb
  refine ⟨fun y => C y ∨ y = d, srcSet_or hs hd, ?_, fun y hy => Or.inl hy,
    fun y hy => Or.inr hy, ?_⟩
  · rintro y (h | rfl)
    · exact hCm y h
    · exact hdm
  · have hi : nameTysM Mem C ix = some (.sword 64) :=
      nameTysM_word (hCm ix (hb ix rfl)) (hb ix rfl)
    have harm : TransArrN (nameTysM Mem C) (.RArrLoad ⟨d, .TU64⟩ ⟨m, mty⟩ ix)
        ((nameTysM Mem C).upd d (.sword 64)) :=
      TransArrN.rArrLoad ⟨d, .TU64⟩ ⟨m, mty⟩ ix n hd rfl (nameTysM_mem hmem) hi
    exact nameTysM_upd_word hdm ▸ TransStepsArr.cons harm (.nil _)

/-- **One dynamic-index memref store** of a bound `u64` word at a bound index into
    a memref name of `Mem`, rebinding it at its own type. -/
theorem transFromArr_arrStore1 {m ix s : String} {mty : TowerType} {n : Nat}
    (hmt : ¬ isTmpName m) (hmem : Mem m = some (.memref n))
    (henc : encodeTy mty = .memref n) :
    TransFromArr Mem (fun y => y = ix ∨ y = s) (fun _ => False)
      [LowCT.RArrStore ⟨m, mty⟩ ix ⟨s, .TU64⟩] := by
  intro C hs hCm hb
  refine ⟨C, hs, hCm, fun _ h => h, fun _ h => h.elim, ?_⟩
  have hix : nameTysM Mem C ix = some (.sword 64) :=
    nameTysM_word (hCm ix (hb ix (Or.inl rfl))) (hb ix (Or.inl rfl))
  have hsrc : nameTysM Mem C s = some (.sword 64) :=
    nameTysM_word (hCm s (hb s (Or.inr rfl))) (hb s (Or.inr rfl))
  have harm : TransArrN (nameTysM Mem C) (.RArrStore ⟨m, mty⟩ ix ⟨s, .TU64⟩)
      ((nameTysM Mem C).upd m (encodeTy mty)) :=
    TransArrN.rArrStore ⟨m, mty⟩ ix ⟨s, .TU64⟩ n hmt (nameTysM_mem hmem) henc hsrc hix
  rw [henc, nameTysM_upd_mem hmem] at harm
  exact TransStepsArr.cons harm (.nil _)

/-- **A block extended by one scalar assignment** whose reads lie in the block's
    exit set. -/
theorem transFromArr_snoc {B W : String → Prop} {l : List LowCT} {x : String} {e : SExpr}
    (h : TransFromArr Mem B W l) (hx : ¬ isTmpName x) (hxm : Mem x = none)
    (hrd : ReadsFrom W e) :
    TransFromArr Mem B (fun y => W y ∨ y = x) (l ++ [LowCT.RScalarSetExpr x e]) :=
  transFromArr_append h
    (transFromArr_setExpr (R := fun s => B s ∨ W s) hx hxm
      (readsFrom_mono hrd (fun _ hx => Or.inr hx)))
    (fun _ hs => hs)

/-- A block extended by three scalar assignments. -/
theorem transFromArr_snoc3 {B W : String → Prop} {l : List LowCT} {x₁ x₂ x₃ : String}
    {e₁ e₂ e₃ : SExpr} (h : TransFromArr Mem B W l)
    (h₁ : ¬ isTmpName x₁) (h₁m : Mem x₁ = none)
    (h₂ : ¬ isTmpName x₂) (h₂m : Mem x₂ = none)
    (h₃ : ¬ isTmpName x₃) (h₃m : Mem x₃ = none)
    (r₁ : ReadsFrom W e₁)
    (r₂ : ReadsFrom (fun y => W y ∨ y = x₁) e₂)
    (r₃ : ReadsFrom (fun y => (W y ∨ y = x₁) ∨ y = x₂) e₃) :
    TransFromArr Mem B (fun y => ((W y ∨ y = x₁) ∨ y = x₂) ∨ y = x₃)
      (l ++ [LowCT.RScalarSetExpr x₁ e₁, LowCT.RScalarSetExpr x₂ e₂,
             LowCT.RScalarSetExpr x₃ e₃]) := by
  have hlist : l ++ [LowCT.RScalarSetExpr x₁ e₁, LowCT.RScalarSetExpr x₂ e₂,
        LowCT.RScalarSetExpr x₃ e₃]
      = ((l ++ [LowCT.RScalarSetExpr x₁ e₁]) ++ [LowCT.RScalarSetExpr x₂ e₂])
        ++ [LowCT.RScalarSetExpr x₃ e₃] := by simp
  rw [hlist]
  exact transFromArr_snoc (transFromArr_snoc (transFromArr_snoc h h₁ h₁m r₁) h₂ h₂m r₂)
    h₃ h₃m r₃

/-- **A block extended by one memref load** whose index lies in the block's exit
    set. -/
theorem transFromArr_snocLoad {B W : String → Prop} {l : List LowCT} {d m ix : String}
    {mty : TowerType} {n : Nat}
    (h : TransFromArr Mem B W l) (hd : ¬ isTmpName d) (hdm : Mem d = none)
    (hmem : Mem m = some (.memref n)) (hix : W ix) :
    TransFromArr Mem B (fun y => W y ∨ y = d)
      (l ++ [LowCT.RArrLoad ⟨d, .TU64⟩ ⟨m, mty⟩ ix]) :=
  transFromArr_append h (transFromArr_arrLoad1 hd hdm hmem)
    (fun x hx => Or.inr (hx ▸ hix))

/-- **A block extended by one memref store** whose index and source lie in the
    block's exit set. -/
theorem transFromArr_snocStore {B W : String → Prop} {l : List LowCT} {m ix s : String}
    {mty : TowerType} {n : Nat}
    (h : TransFromArr Mem B W l) (hmt : ¬ isTmpName m) (hmem : Mem m = some (.memref n))
    (henc : encodeTy mty = .memref n) (hix : W ix) (hsrc : W s) :
    TransFromArr Mem B W (l ++ [LowCT.RArrStore ⟨m, mty⟩ ix ⟨s, .TU64⟩]) :=
  transFromArr_mono
    (transFromArr_append h (transFromArr_arrStore1 hmt hmem henc)
      (fun x hx => hx.elim (fun h => Or.inr (h ▸ hix)) (fun h => Or.inr (h ▸ hsrc))))
    (fun _ h => h) (fun x hx => Or.inl hx)

/-- **The three-command `ltuCmds` block emits reads-bound commands** from a bound
    operand set: it binds `dst ++ "q"`, `dst ++ "r"` and `dst`, reading only names
    the block already binds. -/
theorem transFromArr_ltuCmds {B W : String → Prop} {l : List LowCT} {dst : String}
    {x y : SExpr} (h : TransFromArr Mem B W l)
    (hq : ¬ isTmpName (dst ++ "q")) (hqm : Mem (dst ++ "q") = none)
    (hr : ¬ isTmpName (dst ++ "r")) (hrm : Mem (dst ++ "r") = none)
    (hd : ¬ isTmpName dst) (hdm : Mem dst = none)
    (hx : ReadsFrom W x) (hy : ReadsFrom W y) :
    TransFromArr Mem B (fun z => ((W z ∨ z = dst ++ "q") ∨ z = dst ++ "r") ∨ z = dst)
      (l ++ ltuCmds dst x y) := by
  have hones : ones < 2 ^ 64 := by decide
  unfold ltuCmds
  refine transFromArr_snoc3 h hq hqm hr hrm hd hdm ?_ ?_ ?_
  · exact readsFrom_and (readsFrom_xor hx (readsFrom_lit hones)) hy
  · exact readsFrom_and
      (readsFrom_xor (readsFrom_xor (readsFrom_mono hx (fun _ h => Or.inl h))
        (readsFrom_mono hy (fun _ h => Or.inl h))) (readsFrom_lit hones))
      (readsFrom_sub (readsFrom_mono hx (fun _ h => Or.inl h))
        (readsFrom_mono hy (fun _ h => Or.inl h)))
  · exact readsFrom_shr
      (readsFrom_xor
        (readsFrom_xor (readsFrom_var hq (Or.inl (Or.inr rfl)))
          (readsFrom_var hr (Or.inr rfl)))
        (readsFrom_and (readsFrom_var hq (Or.inl (Or.inr rfl)))
          (readsFrom_var hr (Or.inr rfl))))
      (readsFrom_lit (by decide : (63 : Nat) < 2 ^ 64))

/-! ## 3. The memref-typed derivation of the `mpn_cmp` limb body -/

/-- A pinned scalar read from a bound name. -/
def rdVar {R : String → Prop} (nm : String) {c : Char} {t : List Char}
    (hh : nm.toList = c :: t) (hc : c ≠ '_') (hm : R nm) : ReadsFrom R (sv nm) :=
  readsFrom_var (x := nm) (notTmp_of_headNe hh hc) hm

/-- **The memref-typed reads-bound walk accepts the `mpn_cmp` limb body.** The
    array-op arms carry the memref-cell typing, refining the front-success gate's
    `TransTotal` derivation to `TransArrN`, with no reduction of the body command
    list. -/
theorem cmpLimbBody_transArrN :
    ∃ D : String → Prop,
      TransArrN (nameTysM cmpMem cmpB0) cmpLimbBodyLowCT (nameTysM cmpMem D) := by
  have hlit1 : (1 : Nat) < 2 ^ 64 := by decide
  have hlit0 : (0 : Nat) < 2 ^ 64 := by decide
  have h0 : TransFromArr cmpMem cmpB0 cmpB0 [] := transFromArr_nil (Mem := cmpMem) cmpB0
  have h1 := transFromArr_snoc (x := "top") h0 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (rdVar "n" rfl (by decide) (Or.inr rfl)) (readsFrom_lit hlit1))
  have h2 := transFromArr_snoc (x := "j") h1 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (rdVar "top" rfl (by decide) (by decide))
      (rdVar "idx" rfl (by decide) (by decide)))
  have h3 := transFromArr_snoc (x := "z") h2 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_lit hlit0)
  have h4 := transFromArr_snocLoad (d := "x") (ix := "j") (mty := .TBytes (8 * NU)) h3
    (notTmp_of_headNe rfl (by decide)) (by decide) cmpMem_ap (by decide)
  have h5 := transFromArr_snocLoad (d := "y") (ix := "j") (mty := .TBytes (8 * NU)) h4
    (notTmp_of_headNe rfl (by decide)) (by decide) cmpMem_bp (by decide)
  have h6 := transFromArr_snocLoad (d := "prev") (ix := "z") (mty := .TBytes (8 * NR)) h5
    (notTmp_of_headNe rfl (by decide)) (by decide) cmpMem_rp (by decide)
  have h7 := transFromArr_ltuCmds (dst := "lt") h6
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (rdVar "x" rfl (by decide) (by decide)) (rdVar "y" rfl (by decide) (by decide))
  have h8 := transFromArr_ltuCmds (dst := "gt") h7
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (rdVar "y" rfl (by decide) (by decide)) (rdVar "x" rfl (by decide) (by decide))
  have h9 := transFromArr_snoc (x := "step") h8 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (rdVar "gt" rfl (by decide) (by decide))
      (rdVar "lt" rfl (by decide) (by decide)))
  have h10 := transFromArr_ltuCmds (dst := "nz") h9
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_lit hlit0) (rdVar "prev" rfl (by decide) (by decide))
  have h11 := transFromArr_snoc (x := "keep") h10 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_sub (rdVar "nz" rfl (by decide) (by decide)) (readsFrom_lit hlit1))
  have h12 := transFromArr_snoc (x := "dif") h11 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_xor (rdVar "step" rfl (by decide) (by decide))
      (rdVar "prev" rfl (by decide) (by decide)))
  have h13 := transFromArr_snoc (x := "out") h12 (notTmp_of_headNe rfl (by decide)) (by decide)
    (readsFrom_xor (rdVar "prev" rfl (by decide) (by decide))
      (readsFrom_and (rdVar "keep" rfl (by decide) (by decide))
        (rdVar "dif" rfl (by decide) (by decide))))
  have h14 := transFromArr_snocStore (m := "rp") (ix := "z") (s := "out")
    (mty := .TBytes (8 * NR)) h13
    (notTmp_of_headNe rfl (by decide)) cmpMem_rp rfl (by decide) (by decide)
  obtain ⟨D, _, _, _, _, hts⟩ :=
    h14 cmpB0 cmpB0_srcSet cmpB0_disjoint (fun _ h => h)
  refine ⟨D, ?_⟩
  have hT : TransArrN (nameTysM cmpMem cmpB0) cmpLimbBodyLowCT (nameTysM cmpMem D) :=
    transStepsArr_seqAll hts
  exact hT

/-! ## 4. The front-compiled update is `ArrMemN` -/

/-- **The front-compiled `mpn_cmp` limb body is an `ArrMemN` member.** Feeds the
    memref-typed derivation of the body to
    `frontLoopBodyJ_arrMemN_of_judged` at the one-word result array `rp`, with no
    reduction of the body command list. -/
theorem cmpUpdate_arrMemN : ArrMemN cmpUpdate := by
  obtain ⟨D, hT⟩ := cmpLimbBody_transArrN
  exact frontLoopBodyJ_arrMemN_of_judged vmBody "rp" cmpLimbBodyLowCT hT
    (srcTys_nameTysM cmpMem_notTmp cmpB0_srcSet) vmApprox_cmp
    (nameTysM_mem cmpMem_rp) cmpUpdate_eq

end CatCrypt.Crypto.SecureCompilation.X86Backend.MpnCmpArrMemN
