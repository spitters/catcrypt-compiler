/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgWiden
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionExportTests
public import CatCrypt.Crypto.SecureCompilation.Haxc.CallsAll

/-!
# The widened program is exportable by the region back half

The region back half exports a structured Jasmin program that passes `regionExportableB`:
the operations of its bindings are in the stack-memory fragment `opMemB`, its exit-flag
loops carry register types and its calls are at the word signatures `wordSig`
(`regionExportableB_eq`). This module states that `widenJ` keeps the first two and makes
the third hold at the widened signatures: every block `opBlock?` gives an operation of
`opMemB` has its operations in `opMemB` (at a narrow width, at width `64`), and `wideTy`
sends no register type to an array type.

## Main results

* `opBlock?_isSome` — `widenP` accepts every operation of `opMemB`.
* `opBlock?_opMemB` — the block of an operation of `opMemB` has its operations in
  `opMemB`.
* `widenJ_isSome` — `widenJ` returns a program for every program whose operations are in
  `opMemB`.
* `widenJ_regionExportable` — a program whose operations are in `opMemB`, whose exit-flag
  loops carry register types and whose calls are at signatures that `wordSig` accepts after
  widening widens to a program that passes `regionExportableB`.
* `widenJ_regionExportable_of_exportable` — the same for a program that passes
  `regionExportableB` itself.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords

open Ctxt (Var Valuation)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (CoveredCom)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminImageOps (allOps_map? covered_of_allOps)
open CatCrypt.Crypto.SecureCompilation.Haxc.ExportComplete (whileRegB regionExportableB_eq)
open CatCrypt.Crypto.SecureCompilation.Haxc.ChainTotal (callsAll callsAll_map?)

/-! ## 1. The blocks -/

/-- `widenP` accepts every operation of `opMemB`. -/
theorem opBlock?_isSome {Γ : Ctxt jasminDialect} (op : JasminOp)
    (args : HVector (fun t => Var Γ t) (DialectSignature.sig (d := jasminDialect) op))
    (h : opMemB op = true) : (opBlock? op args).isSome = true := by
  cases op <;> simp_all [opMemB, opBlock?] <;> rfl

/-- **The blocks stay in the fragment.** The block of an operation of `opMemB` has its
    operations in `opMemB`. -/
theorem opBlock?_opMemB {Γ : Ctxt jasminDialect} (op : JasminOp)
    (args : HVector (fun t => Var Γ t) (DialectSignature.sig (d := jasminDialect) op))
    (hop : opMemB op = true)
    (blk : Com jasminDialect (Γ.map wideTy)
      (wideTy (DialectSignature.ret (d := jasminDialect) op)))
    (h : opBlock? op args = some blk) : CoveredCom (fun e => opMemB e.op = true) blk := by
  cases op <;> simp only [opBlock?, reduceCtorEq] at h <;> (injection h with h; subst h)
  case regArith bop w =>
    unfold arithBlock
    split
    · rename_i hn
      have hW := wideW_of_narrow hn
      cases bop <;> simp [CoveredCom, withMask, countThen, opMemB, hW]
    · simp [CoveredCom, opMemB]
  case castW w w' =>
    unfold castBlock
    split
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      simp [CoveredCom, withMask, opMemB, wideW_of_narrow h.1]
    · simp [CoveredCom, withMask, opMemB]
  case mulhi w =>
    unfold mulhiBlock
    split
    · rename_i hn
      have hW := wideW_of_narrow hn
      have := le32_of_narrow hn
      simp [CoveredCom, opMemB, hW]
      omega
    · simp [CoveredCom, opMemB]
  case addCarryLo w =>
    unfold addLoBlock
    split
    · rename_i hn
      simp [CoveredCom, withMask, opMemB, wideW_of_narrow hn]
    · simp [CoveredCom, opMemB]
  case addCarryHi w =>
    unfold addHiBlock
    split
    · rename_i hn
      have := le32_of_narrow hn
      simp [CoveredCom, opMemB, wideW_of_narrow hn]
      omega
    · simp [CoveredCom, opMemB]
  case rorImm w k =>
    unfold rorBlock
    split
    · rename_i hn
      have := le32_of_narrow hn
      have := pos_of_narrow hn
      have := Nat.mod_lt k (show 0 < w by omega)
      simp [CoveredCom, withMask, opMemB, wideW_of_narrow hn]
      omega
    · rename_i hn
      simp only [opMemB, decide_eq_true_eq] at hop
      simp [CoveredCom, opMemB, wideW_of_not (by simpa using hn), hop]
  case sarImm w k =>
    unfold sarBlock
    split
    · rename_i hn
      have := le32_of_narrow hn
      simp only [opMemB, decide_eq_true_eq] at hop
      have h32 : 2 ^ w ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) this
      simp [CoveredCom, withMask, opMemB, wideW_of_narrow hn]
      omega
    · rename_i hn
      simp only [opMemB, decide_eq_true_eq] at hop
      simp [CoveredCom, opMemB, wideW_of_not (by simpa using hn), hop]
  case shlImm w k =>
    unfold shlBlock
    split
    · rename_i hn
      have := shiftMask_lt32 (le32_of_narrow hn) k
      simp [CoveredCom, withMask, opMemB, wideW_of_narrow hn]
      omega
    · rename_i hn
      simp only [opMemB, decide_eq_true_eq] at hop
      simp [CoveredCom, opMemB, wideW_of_not (by simpa using hn), hop]
  case shrImm w k =>
    simp only [opMemB, decide_eq_true_eq] at hop
    unfold wideCount
    by_cases hn : narrowB w = true
    · have := shiftMask_lt32 (le32_of_narrow hn) k
      simp [CoveredCom, opMemB, wideW_of_narrow hn, hn]
      omega
    · simp [CoveredCom, opMemB, wideW_of_not (by simpa using hn), hn, hop]
  case regConst w n =>
    simp only [opMemB, decide_eq_true_eq] at hop
    have := Nat.lt_of_lt_of_le hop (le_wideW w)
    simp [CoveredCom, opMemB, this]
  all_goals simp_all [CoveredCom, opMemB]

/-- The block of an expression of `opMemB` has its operations in `opMemB`. -/
theorem exprBlock?_opMemB {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
    (hop : opMemB e.op = true) (blk : Com jasminDialect (Γ.map wideTy) (wideTy t))
    (h : exprBlock? e = some blk) : CoveredCom (fun e => opMemB e.op = true) blk := by
  obtain ⟨op, rfl, args⟩ := e
  exact opBlock?_opMemB op args hop blk h

/-! ## 2. The programs -/

/-- `widenJ` returns a program for every program whose operations are in `opMemB`. -/
theorem widenJ_isSome {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : p.allOps opMemB = true) : (widenJ p).isSome = true :=
  (NFProg.isSome_map?_iff widenP widenP_regionTypes p (fun v => v)).mpr
    (NFProg.Covered.mono (fun e (he : opMemB e.op = true) => by
      obtain ⟨op, rfl, args⟩ := e
      exact opBlock?_isSome op args he) (covered_of_allOps opMemB p hp))

/-- `wideTy` sends no register type to an array type. -/
theorem isRegTy_wideTy (t : JasminTy) : isRegTy (wideTy t) = isRegTy t := by
  cases t <;> rfl

/-- Splicing a block keeps `whileRegB` of the continuations. -/
theorem whileRegB_spliceNF? {ts : List JasminTy} :
    {Δ : Ctxt jasminDialect} → {a : JasminTy} → (blk : Com jasminDialect Δ a) →
    (k : {Δ' : Ctxt jasminDialect} → Ctxt.Hom Δ Δ' → Var Δ' a →
      Option (NFProg jasminDialect Δ' ts)) →
    (∀ {Δ' : Ctxt jasminDialect} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a) q,
      k ren res = some q → whileRegB q = true) →
    ∀ q, NFProg.spliceNF? blk k = some q → whileRegB q = true
  | _, _, .ret v, _, hk, q, hq => hk _ v q hq
  | _, _, .var _ blk, _, hk, q, hq => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
      exact whileRegB_spliceNF? blk _ (fun _ res q h => hk _ res q h) q' hq'

/-- Casting the first result type keeps `whileRegB`. -/
theorem whileRegB_castRetHead {Δ : Ctxt jasminDialect} {a b : JasminTy} {ts : List JasminTy}
    (h : a = b) (p : NFProg jasminDialect Δ (a :: ts)) :
    whileRegB (NFProg.castRetHead h p) = whileRegB p := by
  subst h; rfl

/-- `map?` along `widenP` keeps `whileRegB`. -/
theorem whileRegB_map? {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : whileRegB p = true) :
    ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom (widenP.mapCtx Γ) Δ) q,
      NFProg.map? widenP widenP_regionTypes p ren = some q → whileRegB q = true := by
  induction p with
  | ret => intro _ _ q hq; cases hq; rfl
  | var e k ih =>
      intro _ ren q hq
      obtain ⟨blk, _, hq⟩ := Option.bind_eq_some_iff.mp hq
      exact whileRegB_spliceNF? _ _ (fun _ _ q' h => ih hp _ q' h) q hq
  | forLoop _ _ _ _ ihb ihk =>
      intro _ ren q hq
      simp only [whileRegB, Bool.and_eq_true] at hp
      obtain ⟨b, hb, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [whileRegB, Bool.and_eq_true]
      exact ⟨ihb hp.1 _ b hb, ihk hp.2 _ k' hk⟩
  | ifThenElse _ _ _ _ iht ihe ihk =>
      intro _ ren q hq
      simp only [whileRegB, Bool.and_eq_true] at hp
      obtain ⟨a, ha, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b, hb, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [whileRegB, Bool.and_eq_true]
      exact ⟨⟨iht hp.1.1 _ a ha, ihe hp.1.2 _ b hb⟩, ihk hp.2 _ k' hk⟩
  | whileLoop _ _ _ ihb ihk =>
      intro _ ren q hq
      simp only [whileRegB, Bool.and_eq_true] at hp
      obtain ⟨b, hb, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [whileRegB, Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, ihk hp.2 _ k' hk⟩
      · simpa [widenP, List.all_map, Function.comp_def, isRegTy_wideTy] using hp.1.1
      · rw [whileRegB_castRetHead]
        exact ihb hp.1.2 _ b hb
  | call _ _ _ ih =>
      intro _ ren q hq
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp hq
      exact ih hp _ k' hk

/-- `wordCalls` is `callsAll` at the word signatures. -/
theorem wordCalls_eq_callsAll {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) : wordCalls p = callsAll (fun _ as rs => wordSig as rs) p := by
  induction p <;> simp_all [wordCalls, callsAll]

/-- **Completeness for the region back half.** A program whose operations are in `opMemB`,
    whose exit-flag loops carry register types and whose calls are at signatures that
    `wordSig` accepts after widening widens to a program that passes `regionExportableB`. -/
theorem widenJ_regionExportable {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hops : p.allOps opMemB = true)
    (hwhile : whileRegB p = true)
    (hcalls : callsAll (fun _ as rs => wordSig (as.map wideTy) (rs.map wideTy)) p = true)
    (q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)) (hq : widenJ p = some q) :
    regionExportableB q = true := by
  rw [regionExportableB_eq]
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, whileRegB_map? p hwhile _ q hq⟩, ?_⟩
  · exact allOps_map? widenP widenP_regionTypes opMemB p
      (NFProg.Covered.mono (fun e he blk hblk => exprBlock?_opMemB e he blk hblk)
        (covered_of_allOps opMemB p hops)) _ q hq
  · rw [wordCalls_eq_callsAll]
    exact callsAll_map? widenP widenP_regionTypes _ p hcalls _ hq

/-- A word signature stays a word signature after widening. -/
theorem wordSig_map_wideTy {as rs : List JasminTy} (h : wordSig as rs = true) :
    wordSig (as.map wideTy) (rs.map wideTy) = true := by
  rw [wordSig_iff] at h ⊢
  obtain ⟨ha, hr⟩ := h
  refine ⟨fun t ht => ?_, ?_⟩
  · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    have := ha t' ht'
    cases t' <;> simp_all [callArgTy, wideTy, wideW, narrowB]
  · rcases hr with rfl | ⟨n, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨n, rfl⟩

/-- A program whose calls are at word signatures has its calls at signatures that stay word
    signatures after widening. -/
theorem callsAll_wideTy_of_wordSig {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (h : callsAll (fun _ as rs => wordSig as rs) p = true) :
    callsAll (fun _ as rs => wordSig (as.map wideTy) (rs.map wideTy)) p = true := by
  induction p <;> simp_all [callsAll, wordSig_map_wideTy]

/-- **Completeness at an exportable program.** A program that passes `regionExportableB`
    widens to a program that passes `regionExportableB`. -/
theorem widenJ_regionExportable_of_exportable {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)) (hq : widenJ p = some q) :
    regionExportableB q = true := by
  rw [regionExportableB_eq] at hp
  simp only [Bool.and_eq_true] at hp
  obtain ⟨⟨hops, hwhile⟩, hcalls⟩ := hp
  rw [wordCalls_eq_callsAll] at hcalls
  exact widenJ_regionExportable p hops hwhile (callsAll_wideTy_of_wordSig p hcalls) q hq

end CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords
