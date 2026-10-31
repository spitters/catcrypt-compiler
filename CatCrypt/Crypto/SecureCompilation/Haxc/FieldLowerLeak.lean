/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldLower
public import CatCrypt.Crypto.Hax.NFFieldSumLeak
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFMapLeak
public import CatCrypt.Crypto.SecureCompilation.Dialects.NFDceLeak

/-!
# The leakage transformer of the field lowering

`lowerF P` translates a program of `nfFieldDialect` to a program of `jasminDialect`: an
operation of the left summand to no binding or to one constant binding, an operation of
the right summand to the block `fieldCom P (opCom op)` of the Montgomery template, and a
counted loop to a counted loop with the same trip count. The events of the translated
program are therefore the `trip` events of the source with the events of the blocks and of
the constants in between.

`BlocksCT P Pj` states that the block of every operation with an argument that `opGoodB P`
accepts emits, at the leakage model `jLeakModel Pj`, the same events from every two
valuations: the events of a block do not depend on the words of its arrays. It follows
from the level check `blocksCheck P Pj` of the seven blocks with every array secret
(`blocksCT_of_check`); no proof of that check for every limb count is given here, so
`BlocksCT` is a hypothesis of the statements below. Under this hypothesis the
events of a run of the translated program are a function of the events of the run of the
source (`lowerF_leak`): the function reads the trace along the structure of the source
program, drops the events of each source binding, and emits the events of its block. The
statement holds at every leakage model of `nfFieldDialect`.

`ifFree_lowerF`: a translated program has no branch.

## Main definitions

* `BlocksCT` — the events of the blocks of the template do not depend on the valuation.
* `blockCheck`, `blocksCheck` — the level check of the blocks with every array secret.
* `BindSyn` — the conclusion of the leakage statement of a binding.
* `LeakSim` — a translated program runs, at related valuations, to related results with
  the events a transformer reads off the source events.

## Main results

* `blocksCT_of_check` — blocks the level checker accepts satisfy `BlocksCT`.
* `spliceNF?_leakSyn` — the leakage run of a block followed by a continuation.
* `bindF_syn` — the leakage statement of a translated binding.
* `forIterLeak_sim` — matched steps give matched iterations.
* `lowerF_leak` — the leakage transformer of `lowerF`.
* `lowerF_leak2` — two source runs with equal events give two target runs with equal events.
* `ifFree_lowerF` — a translated program is branch-free.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldLower

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectCoproduct
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend hvToHom pullV_hvToHom)
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (LimbParams)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (eConst)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.Hax.NFFieldSum (nfFieldDialect nfFieldDenote)
open Ctxt (Var Valuation)

variable {n : Nat} (P : LimbParams n) (Pj : JLeakParams)

/-! ## 1. The hypothesis on the blocks -/

/-- **The events of the blocks of the template do not depend on the valuation**: the block
    `fieldCom P (opCom op)` of every operation with an argument that `opGoodB P` accepts
    emits the same events at the leakage model `jLeakModel Pj` from every two valuations of
    its arrays. -/
def BlocksCT : Prop :=
  ∀ (op : fieldDialect.Op), opGoodB P op = true → DialectSignature.sig op ≠ [] →
    ∀ W₁ W₂ : Valuation (arrCtx n (DialectSignature.sig op) ++ [arrTy n]),
      Com.ctLeak (jLeakModel Pj) (fieldCom P (opCom op)) W₁ =
        Com.ctLeak (jLeakModel Pj) (fieldCom P (opCom op)) W₂

/-- The level check of the block of `op` at the leakage model `jLeakModel Pj`, with every
    array secret. -/
def blockCheck (op : fieldDialect.Op) : Bool :=
  Com.levelCheck (jLeakModel Pj) (fieldCom P (opCom op)) (allSecret _)

/-- **The level check of the blocks of the template**: the block of each of the seven
    operations with an argument that `opGoodB P` accepts passes the level checker with
    every array secret. -/
def blocksCheck : Bool :=
  blockCheck P Pj (.fAdd P.p) && blockCheck P Pj (.fSub P.p) && blockCheck P Pj (.fNeg P.p) &&
    blockCheck P Pj (.fMul P.p) && blockCheck P Pj (.fCopy P.p) &&
    blockCheck P Pj (.fieldDouble P.p) && blockCheck P Pj (.fieldSquare P.p)

/-- **Blocks the level checker accepts emit valuation-independent events**, from
    `levelCheck_sound` at the secret labels. -/
theorem blocksCT_of_check (h : blocksCheck P Pj = true) : BlocksCT P Pj := by
  simp only [blocksCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  intro op hg hne W₁ W₂
  have hc : blockCheck P Pj op = true := by
    cases op with
    | fAdd q => have e : q = P.p := by simpa [opGoodB] using hg
                subst e; exact h1
    | fSub q => have e : q = P.p := by simpa [opGoodB] using hg
                subst e; exact h2
    | fNeg q => have e : q = P.p := by simpa [opGoodB] using hg
                subst e; exact h3
    | fMul q => have e : q = P.p := by simpa [opGoodB] using hg
                subst e; exact h4
    | fCopy q => have e : q = P.p := by simpa [opGoodB] using hg
                 subst e; exact h5
    | fieldDouble q => have e : q = P.p := by simpa [opGoodB] using hg
                       subst e; exact h6
    | fieldSquare q => have e : q = P.p := by simpa [opGoodB] using hg
                       subst e; exact h7
    | fInv q => simp [opGoodB] at hg
    | fConst q c => exact absurd rfl hne
  exact levelCheck_sound (jLeakModel Pj) _ _ hc W₁ W₂ (pubEqV_allSecret W₁ W₂)

/-- The valuation of the arrays of a block with every word zero. -/
def zeroArrVal : (ts : List FieldTy) → Valuation (d := jasminDialect) (arrCtx n ts ++ [arrTy n])
  | [] => .cons (t := arrTy n) (fun _ => 0) .nil
  | _ :: ts => .cons (t := arrTy n) (fun _ => 0) (zeroArrVal ts)

/-- A vector of arrays with a first array is the vector of a nonempty list. -/
theorem headArr_some {Θ : Ctxt jasminDialect} :
    ∀ {ts : List FieldTy} (as : HVector (fun t => Var Θ t) (arrCtx n ts)) (o : Var Θ (arrTy n)),
      headArr as = some o → ts ≠ []
  | [], _, _, h => by simp [headArr] at h
  | _ :: _, _, _, _ => by simp

/-! ## 2. The leakage run of a splice -/

/-- **A block followed by a partial continuation.** A program `spliceNF? blk k` returns is
    the bindings of `blk` in front of a program `k h res` returns; its leakage run from `W`
    is the run of that program from an extension of `W` that keeps every lookup and holds
    the value of the block at `res`, with the events of the block in front. -/
theorem spliceNF?_leakSyn {us : List JasminTy} :
    ∀ {Θ : Ctxt jasminDialect} {a : JasminTy} (blk : Com jasminDialect Θ a)
      (k : {Θ' : Ctxt jasminDialect} → Ctxt.Hom Θ Θ' → Var Θ' a →
        Option (NFProg jasminDialect Θ' us))
      (q : NFProg jasminDialect Θ us), NFProg.spliceNF? blk k = some q →
      ∃ (Θ' : Ctxt jasminDialect) (h : Ctxt.Hom Θ Θ') (res : Var Θ' a)
        (q' : NFProg jasminDialect Θ' us), k h res = some q' ∧
          ∀ W : Valuation Θ, ∃ W' : Valuation Θ', Pres h W W' ∧
            res.lookup W' = blk.denote W ∧
            ∀ (M : LeakModel jasminDialect) (fuel : Nat), NFProg.leakRun M fuel q W =
              (NFProg.leakRun M fuel q' W').map fun r => (r.1, Com.ctLeak M blk W ++ r.2)
  | _, _, .ret v, _, q, hq =>
      ⟨_, fun x => x, v, q, hq, fun W => ⟨W, fun _ => rfl, rfl, fun M fuel => by
        cases NFProg.leakRun M fuel q W <;> rfl⟩⟩
  | _, _, .var e blk, k, q, hq => by
      simp only [NFProg.spliceNF?] at hq
      obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp hq
      obtain ⟨Θ', h, res, q', hk, H⟩ := spliceNF?_leakSyn blk _ q₁ hq₁
      refine ⟨Θ', fun x => h (.there x), res, q', hk, fun W => ?_⟩
      obtain ⟨W', hp, hres, hl⟩ := H (W.extend (e.denote W))
      refine ⟨W', fun v => hp (.there v), hres, fun M fuel => ?_⟩
      simp only [NFProg.leakRun]
      rw [hl M fuel, Option.map_map]
      cases NFProg.leakRun M fuel q' W' with
      | none => rfl
      | some r =>
          show some _ = some _
          simp only [Function.comp, Com.ctLeak, List.append_assoc]

/-! ## 3. The bindings -/

/-- The conclusion of the leakage statement of a binding whose values are given by `Sem`:
    a renaming of the carrier context, a reading, a program of the continuation and a list
    of events, none depending on the valuations, such that at valuations related along `ρ`
    the reading is related to the bound value at an extension of the carrier valuation, and
    the translated program runs as the continuation's program from that extension with the
    events in front. -/
def BindSyn {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
    {t : nfFieldDialect.Ty} {us : List JasminTy} (Sem : Valuation Δ → ⟦t⟧ → Prop)
    (k : BindK n Θ t us) (q : NFProg jasminDialect Θ us) : Prop :=
  ∃ (Θ' : Ctxt jasminDialect) (h : Ctxt.Hom Θ Θ') (r : Rd n Θ' t)
    (q' : NFProg jasminDialect Θ' us) (E : List CTLeak), k h r = some q' ∧
      ∀ (X : Valuation Δ) (W : Valuation Θ), JAgree P ρ X W → ∀ x, Sem X x →
        ∃ W' : Valuation Θ', Pres h W W' ∧ r.rel P W' x ∧
          ∀ fuel : Nat, NFProg.leakRun (jLeakModel Pj) fuel q W =
            (NFProg.leakRun (jLeakModel Pj) fuel q' W').map fun s => (s.1, E ++ s.2)

theorem bindSyn_id {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
    {t : nfFieldDialect.Ty} {us : List JasminTy} (Sem : Valuation Δ → ⟦t⟧ → Prop)
    (k : BindK n Θ t us) (q : NFProg jasminDialect Θ us) (r : Rd n Θ t)
    (hq : k (fun v => v) r = some q)
    (hr : ∀ (X : Valuation Δ) (W : Valuation Θ), JAgree P ρ X W → ∀ x, Sem X x → r.rel P W x) :
    BindSyn P Pj ρ Sem k q :=
  ⟨_, fun v => v, r, q, [], hq, fun X W hA x hx => ⟨W, fun _ => rfl, hr X W hA x hx,
    fun fuel => by cases NFProg.leakRun (jLeakModel Pj) fuel q W <;> rfl⟩⟩

/-- The loop counter: no target binding. -/
theorem ctrArm_syn {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
    {us : List JasminTy} (lo : Var Δ (.inl .int)) (i : Var Δ (.inl (.word 64)))
    (k : BindK n Θ (.inl (.word 64)) us) (q : NFProg jasminDialect Θ us)
    (hq : ctrArm ρ lo i k = some q) :
    BindSyn P Pj ρ (t := .inl (.word 64))
      (fun X x => (fun (a : Int) (b : BitVec 64) =>
        if 0 ≤ a ∧ a + (b.toNat : Int) < 2 ^ 64 then
          some (BitVec.ofNat 64 (a + (b.toNat : Int)).toNat)
        else none) (lo.lookup X) (i.lookup X) = some x) k q := by
  unfold ctrArm at hq
  split at hq
  · rename_i hlo
    obtain ⟨w, hw, hq⟩ := Option.bind_eq_some_iff.mp hq
    refine bindSyn_id P Pj ρ _ k q (.var w) hq fun X W hA x hx => ?_
    have h2 : (ρ i).rel P W (i.lookup X) := hA _ i
    have e : ρ i = .var w := Rd.eq_of_var? hw
    rw [e] at h2
    change BitVec.toNat (w.lookup W) = BitVec.toNat (i.lookup X) at h2
    change BitVec.toNat (w.lookup W) = BitVec.toNat x
    rw [lit_zero P hA lo hlo] at hx
    beta_reduce at hx
    rw [zero_add] at hx
    split at hx
    · obtain rfl := Option.some.inj hx
      rw [h2, Int.toNat_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
    · cases hx
  · cases hq

/-- The trip count: no target binding, or the binding of a constant. -/
theorem tripArm_syn {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
    {us : List JasminTy} {t : NfTy} (lo : Var Δ (.inl .int)) (hi : Var Δ (.inl t))
    (k : BindK n Θ (.inl (.word 64)) us) (q : NFProg jasminDialect Θ us)
    (hq : tripArm ρ lo hi k = some q) :
    BindSyn P Pj ρ (t := .inl (.word 64))
      (fun X x => (NfTy.toInt? t (hi.lookup X)).map
        (fun h => BitVec.ofNat 64 (h - (lo.lookup X : Int)).toNat) = some x) k q := by
  unfold tripArm at hq
  split at hq
  · rename_i hlo
    split at hq
    · rename_i w hhi
      refine bindSyn_id P Pj ρ _ k q (.var w) hq fun X W hA x hx => ?_
      rw [lit_zero P hA lo hlo] at hx
      have h2 : (ρ hi).rel P W (hi.lookup X) := hA _ hi
      have e : ρ hi = .var w := hhi
      rw [e] at h2
      change BitVec.toNat (w.lookup W) = BitVec.toNat x
      change JRel P (.inl t) (hi.lookup X) (w.lookup W) at h2
      have hw := (w.lookup W).isLt
      cases t <;> simp only [NfTy.toInt?, Option.map_none, Option.map_some,
        reduceCtorEq, Option.some.injEq] at hx <;> subst hx <;> simp only [JRel] at h2 <;>
        simp only [BitVec.toNat_ofNat] <;> omega
    · rename_i z hhi
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      refine ⟨_, fun v => .there v, .var .here, q',
        opLeak (jLeakModel Pj) (.regConst 64 z.toNat) .nil, hq', fun X W hA x hx => ?_⟩
      beta_reduce at hx
      rw [lit_zero P hA lo hlo] at hx
      have h2 : (ρ hi).rel P W (hi.lookup X) := hA _ hi
      refine ⟨W.extend (BitVec.ofNat 64 z.toNat), fun _ => rfl, ?_, fun fuel => rfl⟩
      have e : ρ hi = .lit z := hhi
      rw [e] at h2
      change BitVec.toNat (BitVec.ofNat 64 z.toNat) = BitVec.toNat x
      cases t <;> (simp only [Rd.rel, litRel] at h2; try exact h2.elim) <;>
        (simp only [NfTy.toInt?, Option.map_some, Option.some.injEq] at hx
         subst hx
         rw [h2, Int.sub_zero])
    · cases hq
  · cases hq

/-- **The left arm.** -/
theorem leftArm_syn (L : NfLeafTable) {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect}
    (ρ : JRen n Δ Θ) {us : List JasminTy} :
    ∀ (op : NfOp) (args : HVector (fun t => Var Δ t) ((DialectSignature.sig op).map Sum.inl))
      (k : BindK n Θ (.inl (DialectSignature.ret op)) us) (q : NFProg jasminDialect Θ us),
      leftArm ρ op args k = some q →
        BindSyn P Pj ρ (t := .inl (DialectSignature.ret op))
          (fun X x => nfDenoteOp L op (unmapInl (Expr.lookupArgs args X)) = some x) k q
  | .named _ op, args, k, q, hq => leftArm_syn L ρ op args k q hq
  | .ilit t z, _, k, q, hq => by
      cases t <;> simp only [leftArm, reduceCtorEq] at hq
      · rename_i w _
        refine bindSyn_id P Pj ρ (t := .inl (.word w)) _ k q (.lit z) hq fun X W hA x hx => ?_
        change NfTy.ofLit? (.word w) z = some x at hx
        simp only [NfTy.ofLit?] at hx
        split at hx
        · rename_i hr
          obtain rfl := Option.some.inj hx
          have h0 : (z.toNat : Int) = z := Int.toNat_of_nonneg hr.1
          have h1 : z.toNat < 2 ^ w := by
            have h2 := hr.2
            rw [← h0] at h2
            exact_mod_cast h2
          show ((BitVec.ofNat w z.toNat).toNat : Int) = z
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, h0]
        · cases hx
      · exact bindSyn_id P Pj ρ (t := .inl .int) _ k q (.lit z) hq
          fun X W hA x hx => (Option.some.inj hx).symm
  | .constUnit, _, k, q, hq =>
      bindSyn_id P Pj ρ (t := .inl .unit) _ k q .none hq fun _ _ _ _ _ => trivial
  | .ctr, .cons lo (.cons i .nil), k, q, hq => ctrArm_syn P Pj ρ lo i k q hq
  | .trip _, .cons lo (.cons hi .nil), k, q, hq => tripArm_syn P Pj ρ lo hi k q hq
  | .const _ _, _, _, _, hq | .constBit _, _, _, _, hq
  | .bin _ _, _, _, _, hq | .un _ _, _, _, _, hq | .cast _ _, _, _, _, hq
  | .scast _ _, _, _, _, hq | .cmp _ _, _, _, _, hq | .andB, _, _, _, hq
  | .orB, _, _, _, hq | .xorB, _, _, _, hq | .eqB, _, _, _, hq
  | .notB, _, _, _, hq | .index _ _, _, _, _, hq | .update _ _, _, _, _, hq
  | .arrLit _ _, _, _, _, hq | .arrRepeat _ _, _, _, _, hq
  | .mkPair _ _, _, _, _, hq | .fst _ _, _, _, _, hq | .snd _ _, _, _, _, hq
  | .call _ _ _, _, _, _, hq | .tnilV, _, _, _, hq
  | .tconsV _ _, _, _, _, hq | .thead _ _, _, _, _, hq
  | .ttail _ _, _, _, _, hq | .boundInt _, _, _, _, hq => by simp [leftArm] at hq

/-- **The right arm**: the events of the block of the operation, under `BlocksCT`. -/
theorem rightArm_syn (hn : n < 2 ^ 64) (hB : BlocksCT P Pj)
    {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ) {us : List JasminTy}
    (op : fieldDialect.Op)
    (args : HVector (fun t => Var Δ t) ((DialectSignature.sig op).map Sum.inr))
    (k : BindK n Θ (.inr (DialectSignature.ret op)) us) (q : NFProg jasminDialect Θ us)
    (hq : rightArm P ρ op args k = some q) :
    BindSyn P Pj ρ (t := .inr (DialectSignature.ret op))
      (fun X x => DialectDenote.denote op (unmapInr (Expr.lookupArgs args X)) = x) k q := by
  unfold rightArm at hq
  split at hq
  · rename_i hg
    obtain ⟨as, has, hq⟩ := Option.bind_eq_some_iff.mp hq
    obtain ⟨o, ho, hq⟩ := Option.bind_eq_some_iff.mp hq
    have hne := headArr_some as o ho
    obtain ⟨Θ', h, res, q', hk, H⟩ := spliceNF?_leakSyn _ _ q hq
    refine ⟨Θ', h, .var res, q',
      Com.ctLeak (jLeakModel Pj) (fieldCom P (opCom op)) (zeroArrVal _), hk,
      fun X W hA x hx => ?_⟩
    subst hx
    obtain ⟨W', hp, hres, hl⟩ := H W
    refine ⟨W', hp, ?_, fun fuel => ?_⟩
    · change arrLimbs (res.lookup W') n 0 = encL P _
      rw [hres, FieldDialectBlockDescent.Com.denote_rename, pullV_hvToHom, lookupVars_hvAppend,
        show MultiReturnCom.lookupVars (HVector.cons o HVector.nil) W =
          HVector.cons (o.lookup W) .nil from rfl,
        fieldCom_denote P hn (opCom op)
          (GoodVB_sound P (opCom op) (by simp [GoodVB, opCom, hg]))
          (unmapInr (Expr.lookupArgs args X)) _ _ (fldArrs_rel P hA args as has), opCom_denote]
    · rw [hl (jLeakModel Pj) fuel, NFProg.Com.ctLeak_rename_pullV,
        hB op hg hne _ (zeroArrVal _)]
  · cases hq

/-- **The leakage statement of a translated binding.** -/
theorem bindF_syn (L : NfLeafTable) (hn : n < 2 ^ 64)
    (hB : BlocksCT P Pj) {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect}
    (ρ : JRen n Δ Θ) {us : List JasminTy} :
    ∀ {t : nfFieldDialect.Ty} (e : Expr nfFieldDialect Δ t) (k : BindK n Θ t us)
      (q : NFProg jasminDialect Θ us), bindF P ρ e k = some q →
        BindSyn P Pj ρ
          (fun X x => @Expr.denoteM nfFieldDialect Option _ _ (nfFieldDenote L) Δ t e X = some x)
          k q
  | _, ⟨.inl op, rfl, args⟩, k, q, hq => leftArm_syn P Pj L ρ op args k q hq
  | _, ⟨.inr op, rfl, args⟩, k, q, hq => by
      obtain ⟨Θ', h, r, q', E, hk, H⟩ := rightArm_syn P Pj hn hB ρ op args k q hq
      exact ⟨Θ', h, r, q', E, hk, fun X W hA x hx => H X W hA x (Option.some.inj hx)⟩

/-! ## 4. The loop -/

/-- Iterations whose steps are matched at related tuples, with the events `er` reads off the
    source events, are matched by the iterations of the second loop, with the events
    `iterErase er` reads off. -/
theorem forIterLeak_sim {cs : List nfFieldDialect.Ty}
    (step : Nat → Valuation cs → Option (Valuation cs × List CTLeak))
    (step' : Nat → Valuation (d := jasminDialect) (cs.map (jTy n)) →
      Option (Valuation (d := jasminDialect) (cs.map (jTy n)) × List CTLeak))
    (er : List CTLeak → List CTLeak × List CTLeak)
    (hs : ∀ i A A' r, JRelV P A A' → step i A = some r →
      ∃ R' E, step' i A' = some (R', E) ∧ JRelV P r.1 R' ∧
        ∀ rest, er (r.2 ++ rest) = (E, rest)) :
    ∀ (is : List Nat) (A : Valuation cs) (A' : Valuation (d := jasminDialect) (cs.map (jTy n)))
      (q : Valuation cs × List CTLeak), JRelV P A A' → forIterLeak step is A = some q →
        ∃ R' E, forIterLeak step' is A' = some (R', E) ∧ JRelV P q.1 R' ∧
          ∀ rest, iterErase er is.length (q.2 ++ rest) = (E, rest)
  | [], A, A', q, hA, h => by
      simp only [forIterLeak, Option.some.injEq] at h
      subst h
      exact ⟨A', [], rfl, hA, fun rest => rfl⟩
  | i :: is, A, A', q, hA, h => by
      simp only [forIterLeak, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, q', hq', rfl⟩ := h
      obtain ⟨R₁, E₁, h₁, hR₁, e₁⟩ := hs i A A' r hA hr
      obtain ⟨R₂, E₂, h₂, hR₂, e₂⟩ := forIterLeak_sim step step' er hs is r.1 R₁ q' hR₁ hq'
      refine ⟨R₂, E₁ ++ E₂, ?_, hR₂, fun rest => ?_⟩
      · simp only [forIterLeak, h₁, Option.bind_some, h₂, Option.map_some]
      · simp only [List.length_cons, iterErase, List.append_assoc, e₁, e₂]

/-! ## 5. The transformer -/

/-- The leakage run of a program of `nfFieldDialect` at the leaf table `L` and the leakage
    model `M`. -/
abbrev SLeakL (L : NfLeafTable) (M : LeakModel nfFieldDialect) (fuel : Nat)
    {Δ : Ctxt nfFieldDialect} {ts : List nfFieldDialect.Ty} (p : NFProg nfFieldDialect Δ ts)
    (X : Valuation Δ) : Option (Valuation ts × List CTLeak) :=
  @NFProg.leakRunM nfFieldDialect _ _ _ _ (nfFieldDenote L) M fuel Δ ts p X

/-- **A translated program runs with the events a transformer reads off the source
    events.** At valuations related along `ρ` and every pair of fuels, a leakage run of
    `prog` that succeeds is matched by a leakage run of `q` to related results, whose events
    are those `T` returns on the source events followed by any rest, with that rest left. -/
def LeakSim (L : NfLeafTable) (M : LeakModel nfFieldDialect) {Δ : Ctxt nfFieldDialect}
    {ts : List nfFieldDialect.Ty} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
    (prog : NFProg nfFieldDialect Δ ts) (q : NFProg jasminDialect Θ (ts.map (jTy n)))
    (T : List CTLeak → List CTLeak × List CTLeak) : Prop :=
  ∀ (fuel fuel' : Nat) (X : Valuation Δ) (W : Valuation Θ), JAgree P ρ X W →
    ∀ r, SLeakL L M fuel prog X = some r →
      ∃ R' E, NFProg.leakRun (jLeakModel Pj) fuel' q W = some (R', E) ∧ JRelV P r.1 R' ∧
        ∀ rest, T (r.2 ++ rest) = (E, rest)

/-- **The leakage transformer of the field lowering.** Under `BlocksCT`, the events of a
    run of a lowered program are a function of the events of the run of its source, at every
    leaf table and every leakage model of `nfFieldDialect`. -/
theorem lowerF_leak (L : NfLeafTable) (M : LeakModel nfFieldDialect) (hn : n < 2 ^ 64)
    (hB : BlocksCT P Pj) :
    ∀ {Δ : Ctxt nfFieldDialect} {ts : List nfFieldDialect.Ty}
      (prog : NFProg nfFieldDialect Δ ts) {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
      (q : NFProg jasminDialect Θ (ts.map (jTy n))), lowerF P prog ρ = some q →
      ∃ T, LeakSim P Pj L M ρ prog q T
  | _, _, .ret vs, _, ρ, q, h => by
      obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨fun tr => ([], tr), fun fuel fuel' X W hA r hr => ?_⟩
      cases hr
      exact ⟨_, [], rfl, retVars_rel P hA vs ws hws, fun rest => rfl⟩
  | _, _, .var e k, _, ρ, q, h => by
      obtain ⟨Θ', g, rd, q', E₀, hk, H⟩ := bindF_syn P Pj L hn hB ρ e _ q h
      obtain ⟨Tk, hTk⟩ := lowerF_leak L M hn hB k (ρ.lift g rd) q' hk
      refine ⟨fun tr => (E₀ ++ (Tk (tr.drop (evCount (M.kind e.op)))).1,
        (Tk (tr.drop (evCount (M.kind e.op)))).2), fun fuel fuel' X W hA r hr => ?_⟩
      simp only [SLeakL, NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hr
      obtain ⟨x, hx, s, hs, rfl⟩ := hr
      obtain ⟨W', hp, hrel, hl⟩ := H X W hA x hx
      obtain ⟨R', E, hE, hR, hT⟩ := hTk fuel fuel' _ W' (hA.lift P hp rd x hrel) s hs
      refine ⟨R', E₀ ++ E, ?_, hR, fun rest => ?_⟩
      · rw [hl fuel', hE]
        rfl
      · have hlen := Expr.ctLeak_length M e X
        have hdrop : (Expr.ctLeak M e X ++ (s.2 ++ rest)).drop (evCount (M.kind e.op)) =
            s.2 ++ rest := by rw [← hlen, List.drop_left]
        simp only [List.append_assoc, hdrop, hT]
  | _, _, .forLoop (cs := cs) count inits body k, _, ρ, q, h => by
      simp only [lowerF] at h
      split at h
      · rename_i c hc
        obtain ⟨ivs, hivs, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨Tb, hTb⟩ := lowerF_leak L M hn hB body _ b hb
        obtain ⟨Tk, hTk⟩ := lowerF_leak L M hn hB k _ k' hk
        refine ⟨fun tr => match tr with
          | .trip m :: tr' => (.trip m :: ((iterErase Tb m tr').1 ++
              (Tk (iterErase Tb m tr').2).1), (Tk (iterErase Tb m tr').2).2)
          | _ => ([], tr), fun fuel fuel' X W hA r hr => ?_⟩
        simp only [SLeakL, NFProg.leakRunM, Option.bind_eq_some_iff, Option.map_eq_some_iff]
          at hr
        obtain ⟨a, ha, s, hs, rfl⟩ := hr
        have hcnt : BitVec.toNat (c.lookup W) = BitVec.toNat (count.lookup X) := by
          have h0 : (ρ count).rel P W (count.lookup X) := hA _ count
          rw [hc] at h0
          exact h0
        have hAj : ∀ j : Nat, JAgree P
            (JRen.lift ρ (s := .inl (.word 64)) (fun v => .there v) (.var .here))
            (HVector.cons (HasWord64.ofNat (d := nfFieldDialect) j) X)
            (HVector.cons (HasWord64.ofNat (d := jasminDialect) j) W) := fun j =>
          hA.lift P (h := fun v => .there v) (fun _ => rfl) (.var .here) _ rfl
        obtain ⟨A', E₁, h₁, hR₁, e₁⟩ := forIterLeak_sim P
          (fun i acc => SLeakL L M fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := nfFieldDialect) i) X)))
          (fun i acc => NFProg.leakRun (jLeakModel Pj) fuel' b
            (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) W)))
          Tb
          (fun j acc acc' r1 hr hr1 =>
            hTb fuel fuel'
              (hvAppend acc (.cons (HasWord64.ofNat (d := nfFieldDialect) j) X))
              (hvAppend acc' (.cons (HasWord64.ofNat (d := jasminDialect) j) W))
              (JAgree.app P (hAj j) cs acc acc' hr) r1 hr1)
          _ _ _ a (retVars_rel P hA inits ivs hivs) ha
        obtain ⟨R', E₂, h₂, hR₂, e₂⟩ := hTk fuel fuel' _ _ (JAgree.app P hA cs a.1 A' hR₁) s hs
        refine ⟨R', .trip (BitVec.toNat (count.lookup X)) :: (E₁ ++ E₂), ?_, hR₂,
          fun rest => ?_⟩
        · change ((forIterLeak
              (fun i acc => NFProg.leakRun (jLeakModel Pj) fuel' b
                (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) W)))
              (List.range (BitVec.toNat (c.lookup W))) (Expr.lookupArgs ivs W)).bind fun r =>
              (NFProg.leakRun (jLeakModel Pj) fuel' k' (hvAppend r.1 W)).map fun q =>
                (q.1, CTLeak.trip (BitVec.toNat (c.lookup W)) :: (r.2 ++ q.2))) = _
          rw [hcnt]
          erw [h₁]
          rw [Option.bind_some, h₂]
          rfl
        · simp only [List.length_range] at e₁
          simp only [List.cons_append, List.append_assoc, e₁, e₂]
          rfl
      · cases h
  | _, _, .ifThenElse _ _ _ _, _, _, _, h => by simp [lowerF] at h
  | _, _, .whileLoop _ _ _, _, _, _, h => by simp [lowerF] at h
  | _, _, .call _ _ _, _, _, _, h => by simp [lowerF] at h

/-- **The field lowering at two runs.** Under `BlocksCT`, two leakage runs of `prog` that
    succeed from valuations related along `ρ` to `W₁` and `W₂` give two leakage runs of the
    lowered program from `W₁` and `W₂`, with equal events when the source events are
    equal. -/
theorem lowerF_leak2 (L : NfLeafTable) (M : LeakModel nfFieldDialect) (hn : n < 2 ^ 64)
    (hB : BlocksCT P Pj) (fuel fuel' : Nat)
    {Δ : Ctxt nfFieldDialect} {ts : List nfFieldDialect.Ty} (prog : NFProg nfFieldDialect Δ ts)
    {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ) (q : NFProg jasminDialect Θ (ts.map (jTy n)))
    (h : lowerF P prog ρ = some q) {X₁ X₂ : Valuation Δ} {W₁ W₂ : Valuation Θ}
    (hA₁ : JAgree P ρ X₁ W₁) (hA₂ : JAgree P ρ X₂ W₂) {r₁ r₂ : Valuation ts × List CTLeak}
    (h₁ : SLeakL L M fuel prog X₁ = some r₁) (h₂ : SLeakL L M fuel prog X₂ = some r₂) :
    ∃ s₁ s₂, NFProg.leakRun (jLeakModel Pj) fuel' q W₁ = some s₁ ∧
      NFProg.leakRun (jLeakModel Pj) fuel' q W₂ = some s₂ ∧ JRelV P r₁.1 s₁.1 ∧
      JRelV P r₂.1 s₂.1 ∧ (r₁.2 = r₂.2 → s₁.2 = s₂.2) := by
  obtain ⟨T, hT⟩ := lowerF_leak P Pj L M hn hB prog ρ q h
  obtain ⟨R₁, E₁, k₁, hR₁, e₁⟩ := hT fuel fuel' X₁ W₁ hA₁ r₁ h₁
  obtain ⟨R₂, E₂, k₂, hR₂, e₂⟩ := hT fuel fuel' X₂ W₂ hA₂ r₂ h₂
  refine ⟨_, _, k₁, k₂, hR₁, hR₂, fun he => ?_⟩
  have h1 := e₁ []
  have h2 := e₂ []
  rw [he] at h1
  rw [h1] at h2
  exact (Prod.mk.inj h2).1

/-! ## 6. Branch-freedom -/

/-- A translated binding is branch-free when every program of its continuation is. -/
theorem ifFree_bindF {Δ : Ctxt nfFieldDialect} {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
    {us : List JasminTy} {t : nfFieldDialect.Ty} (e : Expr nfFieldDialect Δ t)
    (k : BindK n Θ t us)
    (hk : ∀ {Θ' : Ctxt jasminDialect} (h : Ctxt.Hom Θ Θ') (r : Rd n Θ' t) q,
      k h r = some q → NFProg.ifFree q = true)
    (q : NFProg jasminDialect Θ us) (hq : bindF P ρ e k = some q) : NFProg.ifFree q = true := by
  obtain ⟨op, rfl, args⟩ := e
  cases op with
  | inl op =>
      change leftArm ρ op args k = some q at hq
      induction op with
      | named _ op ih => exact ih args k hk hq
      | ilit t z =>
          cases t <;> simp only [leftArm, reduceCtorEq] at hq <;> exact hk _ _ q hq
      | constUnit => exact hk _ _ q hq
      | ctr =>
          simp only [leftArm, ctrArm] at hq
          split at hq
          · obtain ⟨w, -, hq⟩ := Option.bind_eq_some_iff.mp hq
            exact hk _ _ q hq
          · cases hq
      | trip _ =>
          simp only [leftArm, tripArm] at hq
          split at hq
          · split at hq
            · exact hk _ _ q hq
            · obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
              simpa only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.true_and] using
                hk _ _ q' hq'
            · cases hq
          · cases hq
      | _ => simp [leftArm] at hq
  | inr op =>
      change rightArm P ρ op args k = some q at hq
      unfold rightArm at hq
      split at hq
      · obtain ⟨as, -, hq⟩ := Option.bind_eq_some_iff.mp hq
        obtain ⟨o, -, hq⟩ := Option.bind_eq_some_iff.mp hq
        exact NFProg.ifFree_spliceNF? _ _ (fun ren res q' hq' => hk ren (.var res) q' hq') q hq
      · cases hq

/-- **A lowered program is branch-free.** -/
theorem ifFree_lowerF :
    ∀ {Δ : Ctxt nfFieldDialect} {ts : List nfFieldDialect.Ty}
      (prog : NFProg nfFieldDialect Δ ts) {Θ : Ctxt jasminDialect} (ρ : JRen n Δ Θ)
      (q : NFProg jasminDialect Θ (ts.map (jTy n))), lowerF P prog ρ = some q →
      NFProg.ifFree q = true
  | _, _, .ret vs, _, ρ, q, h => by
      obtain ⟨ws, -, rfl⟩ := Option.map_eq_some_iff.mp h
      rfl
  | _, _, .var e k, _, ρ, q, h =>
      ifFree_bindF P ρ e _ (fun g r q' hq' => ifFree_lowerF k (ρ.lift g r) q' hq') q h
  | _, _, .forLoop (cs := cs) count inits body k, _, ρ, q, h => by
      simp only [lowerF] at h
      split at h
      · obtain ⟨ivs, -, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
        have h1 := ifFree_lowerF body _ b hb
        have h2 := ifFree_lowerF k _ k' hk
        simp only [NFProg.ifFree, NFProg.ctSafeNF, NFProg.nodesOk, Bool.and_eq_true] at h1 h2 ⊢
        exact ⟨h1, h2⟩
      · cases h
  | _, _, .ifThenElse _ _ _ _, _, _, _, h => by simp [lowerF] at h
  | _, _, .whileLoop _ _ _, _, _, _, h => by simp [lowerF] at h
  | _, _, .call _ _ _, _, _, _, h => by simp [lowerF] at h

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldLower
