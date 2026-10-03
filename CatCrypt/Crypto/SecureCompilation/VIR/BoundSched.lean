/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgRel

/-!
# Bound schedules and the composition of bounded blocks

A bound schedule `BoundSched` is a sequence of `n` stages with a bound table `bnd`, a
transfer function `xfer` on bounds, a per-stage lane check `fits` and a check `const` on the
constants. Its side condition `BoundSched.Ok` is decidable: the constants are valid, for every
stage `j < n` the transfer of the bound is within the next bound, `xfer j (bnd j) ≤ bnd (j + 1)`,
and every bound `bnd j` with `j ≤ n` fits its lane.

The bounded blocks of `ComRangeExact` compose sequentially (`BoundedBlock.seq`), in parallel
on appended contexts (`BoundedBlock.lanes`), and by iteration over a table of interval
vectors (`BoundedBlock.iterate`).

## Main definitions

* `mrSeq`, `mrLanes`: sequential and parallel composition of multi-return programs.
* `BoundedBlock.seq`, `BoundedBlock.lanes`: the composite bounded blocks.
* `BlockTable`, `BoundedBlock.iterate`: a stage-indexed family of blocks over one context
  with an interval vector per stage, and the block of its first `n` stages.
* `BoundSched`, `BoundSched.Ok`: the bound schedule and its decidable side condition.

## Main results

* `mrSeq_denote`, `mrLanes_denote`: the composites denote the composite semantics.
* `BoundedBlock.seq_sound`, `BoundedBlock.lanes_sound`: the contracts of the composites.
* `BlockTable.iterProg_denote`, `BlockTable.iterate_sound`: the iterated program denotes the
  fold of the stage semantics, and its contract, by `NFProg.foldlM_rel_graded`.
* `BoundSched.run_rel`: under `BoundSched.Ok`, a run of stage steps that send the stage-`j`
  relation `dec w = a ∧ Bd (bnd j) w` to the relation at the transferred bound ends in the
  stage-`n` relation, by `NFProg.foldlM_rel_graded`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open CatCrypt.Crypto.SecureCompilation.VIR.ComRange
open CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV pullV_id)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (lookup_pullV valuation_ext)
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend inlHom inrHom hvToHom
  homToHV spliceMultiK spliceMultiK_denote multiReturnCom_denote_rename pullV_hvToHom
  lookupVars_homToHV lookupVars_renameVars pullV_inlHom pullV_inrHom pullV_comp)

/-! ## 1. Composition of multi-return programs -/

section Prog

variable {d : Dialect} [DialectSignature d]

/-- The sequential composite: `c₂` runs on the results of `c₁`. -/
def mrSeq {Γ ts us : Ctxt d} (c₁ : MultiReturnCom d Γ ts) (c₂ : MultiReturnCom d ts us) :
    MultiReturnCom d Γ us :=
  spliceMultiK c₁ fun _ res => c₂.rename (hvToHom res)

/-- The parallel composite on appended contexts: `c₁` on the left part, `c₂` on the right
    part, results appended. -/
def mrLanes {Γ₁ Γ₂ ts₁ ts₂ : Ctxt d} (c₁ : MultiReturnCom d Γ₁ ts₁)
    (c₂ : MultiReturnCom d Γ₂ ts₂) : MultiReturnCom d (Γ₁ ++ Γ₂) (ts₁ ++ ts₂) :=
  spliceMultiK (c₁.rename (inlHom Γ₂)) fun ren r₁ =>
    spliceMultiK (c₂.rename (fun v => ren (inrHom Γ₁ v))) fun ren₂ r₂ =>
      .ret (hvAppend (HVector.renameVars ren₂ r₁) r₂)

variable [TyDenote d.Ty] [DialectDenote d]

omit [DialectSignature d] in
/-- Looking up an appended vector of variables appends the lookups. -/
theorem lookupVars_hvAppend {Δ : Ctxt d} (W : Valuation Δ) :
    ∀ {xs ys : Ctxt d} (r₁ : HVector (fun u => Var Δ u) xs) (r₂ : HVector (fun u => Var Δ u) ys),
      MultiReturnCom.lookupVars (hvAppend r₁ r₂) W
        = hvAppend (MultiReturnCom.lookupVars r₁ W) (MultiReturnCom.lookupVars r₂ W)
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons _ r₁, r₂ => by
      show HVector.cons _ _ = HVector.cons _ _
      rw [lookupVars_hvAppend W r₁ r₂]

/-- A renaming whose lookups in `W'` agree with `W` pulls `W'` back to `W`. -/
theorem pullV_of_lookup {Γ Δ : Ctxt d} (ren : Ctxt.Hom Γ Δ) (W : Valuation Γ)
    (W' : Valuation Δ) (h : ∀ {s : d.Ty} (v : Var Γ s), (ren v).lookup W' = v.lookup W) :
    pullV ren W' = W :=
  valuation_ext _ _ fun v => by rw [lookup_pullV]; exact h v

/-- **The sequential composite denotes the composite of the denotations.** -/
theorem mrSeq_denote {Γ ts us : Ctxt d} (c₁ : MultiReturnCom d Γ ts)
    (c₂ : MultiReturnCom d ts us) (V : Valuation Γ) :
    (mrSeq c₁ c₂).denote V = c₂.denote (c₁.denote V) :=
  spliceMultiK_denote c₁ _ V _ fun _ res W' _ hres => by
    rw [multiReturnCom_denote_rename, pullV_hvToHom, hres]

/-- **The parallel composite denotes the appended denotations.** -/
theorem mrLanes_denote {Γ₁ Γ₂ ts₁ ts₂ : Ctxt d} (c₁ : MultiReturnCom d Γ₁ ts₁)
    (c₂ : MultiReturnCom d Γ₂ ts₂) (A : Valuation Γ₁) (B : Valuation Γ₂) :
    (mrLanes c₁ c₂).denote (hvAppend A B) = hvAppend (c₁.denote A) (c₂.denote B) :=
  spliceMultiK_denote _ _ (hvAppend A B) _ fun ren r₁ W' hren hr₁ =>
    spliceMultiK_denote _ _ W' _ fun ren₂ r₂ W'' hren₂ hr₂ => by
      have e₁ := pullV_of_lookup ren _ W' hren
      have e₂ := pullV_of_lookup ren₂ _ W'' hren₂
      show MultiReturnCom.lookupVars _ W'' = _
      rw [lookupVars_hvAppend, lookupVars_renameVars, e₂, hr₁, hr₂,
        multiReturnCom_denote_rename, multiReturnCom_denote_rename, pullV_inlHom,
        pullV_comp (inrHom Γ₁) ren, e₁, pullV_inrHom]

end Prog

/-! ## 2. Readings and intervals of appended vectors -/

/-- `hvAppend` at the jasmin types. -/
local notation "hvAppendJ" => hvAppend (d := jasminDialect)

theorem zvals_hvAppend (s : Bool) : ∀ {xs ys : JCtxt} (A : HVector (fun t => ⟦t⟧) xs)
    (B : HVector (fun t => ⟦t⟧) ys),
    zvals s (hvAppendJ A B) = hvAppendJ (zvals s A) (zvals s B)
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons _ A, B => by
      show HVector.cons _ (zvals s (hvAppendJ A B)) = HVector.cons _ _
      rw [zvals_hvAppend s A B]

theorem valsIn_hvAppend (s : Bool) : ∀ {xs ys : JCtxt} (I : HVector (fun _ => Iv) xs)
    (J : HVector (fun _ => Iv) ys) (A : HVector (fun t => ⟦t⟧) xs)
    (B : HVector (fun t => ⟦t⟧) ys),
    ValsIn s (hvAppendJ I J) (hvAppendJ A B) ↔ ValsIn s I A ∧ ValsIn s J B
  | [], _, .nil, _, .nil, _ => ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | _ :: _, _, .cons _ I, J, .cons _ A, B => by
      show _ ∧ ValsIn s (hvAppendJ I J) (hvAppendJ A B) ↔ (_ ∧ ValsIn s I A) ∧ _
      rw [valsIn_hvAppend s I J A B, and_assoc]

/-- Every vector over an appended list is an appended vector. -/
theorem exists_hvAppend {d : Dialect} {f : d.Ty → Type} :
    ∀ {xs ys : List d.Ty} (V : HVector f (xs ++ ys)), ∃ A B, V = hvAppend A B
  | [], _, V => ⟨.nil, V, rfl⟩
  | _ :: _, _, .cons x V => by
      obtain ⟨A, B, rfl⟩ := exists_hvAppend V
      exact ⟨.cons x A, B, rfl⟩

/-! ## 3. Sequential and parallel bounded blocks -/

namespace BoundedBlock

/-- The specification of a sequential composite: some intermediate reading relates the input
    to it by the first specification and it to the output by the second. -/
def seqSpec (B₁ B₂ : BoundedBlock) (hΓ : B₁.ts = B₂.Γ) (zin : ZVec B₁.Γ) (zout : ZVec B₂.ts) :
    Prop :=
  ∃ zm : ZVec B₁.ts, B₁.spec zin zm ∧ B₂.spec (hΓ ▸ zm) zout

theorem seq_sound (B₁ B₂ : BoundedBlock) (hΓ : B₁.ts = B₂.Γ) (hs : B₂.signed = B₁.signed)
    (hlink : ∀ W : HVector (fun t => ⟦t⟧) B₁.ts, ValsIn B₁.signed B₁.outIv W →
      ValsIn B₂.signed B₂.inIv (hΓ ▸ W))
    (hok : (B₁.ok && B₂.ok) = true) (V : Valuation B₁.Γ) (hV : ValsIn B₁.signed B₁.inIv V) :
    ValsIn B₁.signed B₂.outIv ((mrSeq B₁.prog (hΓ ▸ B₂.prog)).denote V) ∧
      seqSpec B₁ B₂ hΓ (zvals B₁.signed V)
        (zvals B₁.signed ((mrSeq B₁.prog (hΓ ▸ B₂.prog)).denote V)) := by
  obtain ⟨h₁, h₂⟩ := Bool.and_eq_true _ _ ▸ hok
  obtain ⟨Γ₂, ts₂, prog₂, s₂, inIv₂, outIv₂, ok₂, spec₂, den₂⟩ := B₂
  dsimp only at hΓ hs hlink h₂ ⊢
  subst hΓ hs
  rw [mrSeq_denote]
  obtain ⟨hW, hsp₁⟩ := B₁.denote_of_ok h₁ V hV
  obtain ⟨hU, hsp₂⟩ := den₂ h₂ _ (hlink _ hW)
  exact ⟨hU, _, hsp₁, hsp₂⟩

/-- **The sequential composite of two bounded blocks.** The output types of `B₁` are the
    input context of `B₂`, both read words alike, and every output of `B₁` in its intervals
    is an input of `B₂` in its intervals. -/
def seq (B₁ B₂ : BoundedBlock) (hΓ : B₁.ts = B₂.Γ) (hs : B₂.signed = B₁.signed)
    (hlink : ∀ W : HVector (fun t => ⟦t⟧) B₁.ts, ValsIn B₁.signed B₁.outIv W →
      ValsIn B₂.signed B₂.inIv (hΓ ▸ W)) : BoundedBlock where
  Γ := B₁.Γ
  ts := B₂.ts
  prog := mrSeq B₁.prog (hΓ ▸ B₂.prog)
  signed := B₁.signed
  inIv := B₁.inIv
  outIv := B₂.outIv
  ok := B₁.ok && B₂.ok
  spec := seqSpec B₁ B₂ hΓ
  denote_of_ok hok V hV := seq_sound B₁ B₂ hΓ hs hlink hok V hV

/-- The specification of a parallel composite: the input and output readings split into
    the parts the two specifications relate. -/
def lanesSpec (B₁ B₂ : BoundedBlock) (zin : ZVec (B₁.Γ ++ B₂.Γ))
    (zout : ZVec (B₁.ts ++ B₂.ts)) : Prop :=
  ∃ z₁ z₂ o₁ o₂, zin = hvAppendJ z₁ z₂ ∧ zout = hvAppendJ o₁ o₂ ∧ B₁.spec z₁ o₁ ∧
    B₂.spec z₂ o₂

theorem lanes_sound (B₁ B₂ : BoundedBlock) (hs : B₂.signed = B₁.signed)
    (hok : (B₁.ok && B₂.ok) = true) (V : HVector (fun t => ⟦t⟧) (B₁.Γ ++ B₂.Γ))
    (hV : ValsIn B₁.signed (hvAppendJ B₁.inIv B₂.inIv) V) :
    ValsIn B₁.signed (hvAppendJ B₁.outIv B₂.outIv) ((mrLanes B₁.prog B₂.prog).denote V) ∧
      lanesSpec B₁ B₂ (zvals B₁.signed V)
        (zvals B₁.signed ((mrLanes B₁.prog B₂.prog).denote V)) := by
  obtain ⟨h₁, h₂⟩ := Bool.and_eq_true _ _ ▸ hok
  obtain ⟨Γ₂, ts₂, prog₂, s₂, inIv₂, outIv₂, ok₂, spec₂, den₂⟩ := B₂
  dsimp only at hs h₂ hV ⊢
  subst hs
  obtain ⟨A, B, rfl⟩ := exists_hvAppend (d := jasminDialect) V
  rw [valsIn_hvAppend] at hV
  rw [mrLanes_denote, valsIn_hvAppend, zvals_hvAppend, zvals_hvAppend]
  obtain ⟨hA, hsA⟩ := B₁.denote_of_ok h₁ A hV.1
  obtain ⟨hB, hsB⟩ := den₂ h₂ B hV.2
  exact ⟨⟨hA, hB⟩, _, _, _, _, rfl, rfl, hsA, hsB⟩

/-- **The parallel composite of two bounded blocks** on the appended input context, with
    appended intervals; both blocks read words alike. -/
def lanes (B₁ B₂ : BoundedBlock) (hs : B₂.signed = B₁.signed) : BoundedBlock where
  Γ := B₁.Γ ++ B₂.Γ
  ts := B₁.ts ++ B₂.ts
  prog := mrLanes B₁.prog B₂.prog
  signed := B₁.signed
  inIv := hvAppendJ B₁.inIv B₂.inIv
  outIv := hvAppendJ B₁.outIv B₂.outIv
  ok := B₁.ok && B₂.ok
  spec := lanesSpec B₁ B₂
  denote_of_ok hok V hV := lanes_sound B₁ B₂ hs hok V hV

end BoundedBlock

/-! ## 4. Iteration over a table of intervals -/

/-- A stage-indexed family of programs over one context `Γ` with a table of interval
    vectors: stage `j` sends inputs in `iv j` to outputs in `iv (j + 1)` related by
    `spec j`, under its side condition `ok j`. -/
structure BlockTable (Γ : JCtxt) where
  /-- The reading of words. -/
  signed : Bool
  /-- The program of stage `j`. -/
  prog : ℕ → MultiReturnCom jasminDialect Γ Γ
  /-- The interval vector before stage `j`. -/
  iv : ℕ → HVector (fun _ => Iv) Γ
  /-- The side condition of stage `j`. -/
  ok : ℕ → Bool
  /-- The specification of stage `j` over input and output readings. -/
  spec : ℕ → ZVec Γ → ZVec Γ → Prop
  /-- The correctness of stage `j` under its side condition. -/
  denote_of_ok : ∀ j, ok j = true → ∀ V : Valuation Γ, ValsIn signed (iv j) V →
    ValsIn signed (iv (j + 1)) ((prog j).denote V) ∧
      spec j (zvals signed V) (zvals signed ((prog j).denote V))

namespace BlockTable

variable {Γ : JCtxt} (T : BlockTable Γ)

/-- The first `n` stages, in order. -/
def iterProg : ℕ → MultiReturnCom jasminDialect Γ Γ
  | 0 => .ret (homToHV Γ fun v => v)
  | n + 1 => mrSeq (iterProg n) (T.prog n)

/-- The readings reachable from `zin` through the specifications of the first `n` stages. -/
def reach : ℕ → ZVec Γ → ZVec Γ → Prop
  | 0, zin, z => z = zin
  | n + 1, zin, z => ∃ zm, reach n zin zm ∧ T.spec n zm z

theorem foldlM_some {α β : Type} (F : α → β → α) :
    ∀ (l : List β) (a : α), l.foldlM (fun a j => some (F a j)) a = some (l.foldl F a)
  | [], _ => rfl
  | j :: l, a => foldlM_some F l (F a j)

/-- **The iterated program denotes the fold of the stage semantics.** -/
theorem iterProg_denote : ∀ (n : ℕ) (V : Valuation Γ),
    (T.iterProg n).denote V = (List.range' 0 n).foldl (fun W j => (T.prog j).denote W) V
  | 0, V => by
      show MultiReturnCom.lookupVars _ V = V
      rw [lookupVars_homToHV, pullV_id]
  | n + 1, V => by
      rw [iterProg, mrSeq_denote, iterProg_denote n, List.range'_concat, List.foldl_append]
      simp

/-- **The contract of the first `n` stages**, by `NFProg.foldlM_rel_graded` with the
    relation family `ValsIn (iv j) W ∧ reach j zin (zvals W)`. -/
theorem iterate_sound (n : ℕ) (hok : ((List.range n).all T.ok) = true) (V : Valuation Γ)
    (hV : ValsIn T.signed (T.iv 0) V) :
    ValsIn T.signed (T.iv n) ((T.iterProg n).denote V) ∧
      T.reach n (zvals T.signed V) (zvals T.signed ((T.iterProg n).denote V)) := by
  have hj : ∀ j, j < n → T.ok j = true := fun j hj => by
    rw [List.all_eq_true] at hok
    exact hok j (List.mem_range.mpr hj)
  have h := NFProg.foldlM_rel_graded
    (R := fun j (_ : Unit) (W : Valuation Γ) =>
      ValsIn T.signed (T.iv j) W ∧ T.reach j (zvals T.signed V) (zvals T.signed W))
    (f := fun _ _ => some ()) (g := fun W j => some ((T.prog j).denote W)) 0 n
    (fun i _ hi _ W ⟨hW, hr⟩ => by
      obtain ⟨hW', hs⟩ := T.denote_of_ok i (hj i (by omega)) W hW
      exact .some ⟨hW', _, hr, hs⟩) () V ⟨hV, rfl⟩
  rw [foldlM_some (fun _ _ => ()), foldlM_some, Nat.zero_add] at h
  cases h with
  | some h => rw [iterProg_denote]; exact h

end BlockTable

namespace BoundedBlock

/-- **The bounded block of the first `n` stages of a table**: inputs in `iv 0`, outputs in
    `iv n`, side condition every `ok j` with `j < n`, specification `reach n`. -/
def iterate {Γ : JCtxt} (T : BlockTable Γ) (n : ℕ) : BoundedBlock where
  Γ := Γ
  ts := Γ
  prog := T.iterProg n
  signed := T.signed
  inIv := T.iv 0
  outIv := T.iv n
  ok := (List.range n).all T.ok
  spec := T.reach n
  denote_of_ok hok V hV := T.iterate_sound n hok V hV

end BoundedBlock

/-! ## 5. Bound schedules -/

/-- A bound schedule of `n` stages: the bound `bnd j` before stage `j`, the bound
    `xfer j b` after stage `j` on inputs within `b`, the lane check `fits j b` of a bound at
    stage `j`, and the check `const` of the constants. -/
structure BoundSched where
  /-- The number of stages. -/
  n : ℕ
  /-- The bound table. -/
  bnd : ℕ → ℕ
  /-- The transfer of a bound through stage `j`. -/
  xfer : ℕ → ℕ → ℕ
  /-- The bound `b` fits the lane at stage `j`. -/
  fits : ℕ → ℕ → Bool
  /-- The constants are valid. -/
  const : Bool

namespace BoundSched

/-- The side condition of a bound schedule: the constants are valid, every transferred
    bound is within the next bound, and every bound fits its lane. -/
def Ok (S : BoundSched) : Prop :=
  S.const = true ∧ (∀ j, j < S.n → S.xfer j (S.bnd j) ≤ S.bnd (j + 1)) ∧
    ∀ j, j < S.n + 1 → S.fits j (S.bnd j) = true

instance (S : BoundSched) : Decidable S.Ok :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **Soundness of a bound schedule, relational form.** Let `dec` read a concrete state
    as an abstract one and `Bd b w` say that `w` lies within the bound `b`, monotone in `b`.
    If every stage step sends states related at `bnd j` (`dec w = a ∧ Bd (bnd j) w`) to
    results related at `xfer j (bnd j)`, then under `S.Ok` the run of the `n` stages sends
    states related at `bnd 0` to results related at `bnd n`. -/
theorem run_rel (S : BoundSched) (hS : S.Ok) {α α' : Type} (dec : α' → α)
    (Bd : ℕ → α' → Prop) (hBd : ∀ b b' w, b ≤ b' → Bd b w → Bd b' w)
    (f : α → ℕ → Option α) (g : α' → ℕ → Option α')
    (hstep : ∀ j, j < S.n → S.fits j (S.bnd j) = true → ∀ a w, dec w = a → Bd (S.bnd j) w →
      Option.Rel (fun a' w' => dec w' = a' ∧ Bd (S.xfer j (S.bnd j)) w') (f a j) (g w j))
    (a : α) (w : α') (ha : dec w = a) (hw : Bd (S.bnd 0) w) :
    Option.Rel (fun a' w' => dec w' = a' ∧ Bd (S.bnd S.n) w')
      ((List.range' 0 S.n).foldlM f a) ((List.range' 0 S.n).foldlM g w) := by
  obtain ⟨-, hx, hf⟩ := hS
  have h := NFProg.foldlM_rel_graded (R := fun j a w => dec w = a ∧ Bd (S.bnd j) w)
    (f := f) (g := g) 0 S.n (fun i _ hi a w ⟨h₁, h₂⟩ => by
      have hi' : i < S.n := by omega
      have hr := hstep i hi' (hf i (by omega)) a w h₁ h₂
      revert hr
      rcases f a i with _ | b <;> rcases g w i with _ | b' <;> intro hr <;> cases hr
      · exact .none
      · rename_i hb
        exact .some ⟨hb.1, hBd _ _ _ (hx i hi') hb.2⟩) a w ⟨ha, hw⟩
  rwa [Nat.zero_add] at h

end BoundSched

end CatCrypt.Crypto.SecureCompilation.VIR.ComRangeExact
