/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.NFMapLeak
public import CatCrypt.Crypto.Hax.NFInline
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegionsAbi
public import CatCrypt.Crypto.SecureCompilation.VIR.TransArgsLaws

@[expose] public section

set_option autoImplicit false

/-!
# The legalisation of a structured program by a block

A legalisation of a structured program of `jasminDialect` rewrites every binding into a block
of `jasminDialect` that denotes the value of the binding. The pass `legalizeBy isB blk`
returns the program itself when no binding is an operation of the test `isB`, and otherwise
maps every binding `e` of every region to the block `blk e`, by `NFProg.map` along the block
lowering `legalLowering blk` of `jasminDialect` into itself. Its instances are the rotate
legalisation `legalizeRor` (`RorLegal`) and the and-not legalisation `legalizeAndn`
(`AndnLegal`); both are proved and neither is applied: the region legalisation
`legalizeRegion` of the region back half is the identity.

The theorems of this module hold for every block that denotes the value of the binding: the
pass keeps the denotation; when the block emits the events of the binding, it keeps the
leakage run and constant time; it keeps every test that reads only the calls; and when the
block of every binding of an operation `acc` binds operations of the stack-memory fragment
`opMemB` only, it sends every program of `regionExportableByB acc` to a program of
`regionExportableB`.

## Main definitions

* `legalLowering` — the block lowering of `jasminDialect` into itself by a block.
* `legalizeBy` — the pass on a program with one result.
* `CallTest` — the tests of a program that read only its calls.
* `regionExportableByB` — the test `regionExportableB` with a test `acc` of the operations in
  place of `opMemB` at the bindings.

## Main results

* `legalizeBy_eq_of_none` — the pass is the identity on a program with no operation of `isB`.
* `legalizeBy_denoteAt`, `legalizeBy_denote` — the pass keeps the denotation.
* `legalizeBy_leakRun`, `nfct_legalizeBy` — the pass keeps the leakage run and constant time.
* `legalizeBy_callTest`, `legalizeBy_callFree_eq` — the pass keeps every test that reads only
  the calls, among them the absence of `call`.
* `regionExportableB_legalizeBy` — completeness of `regionExportableB` on the image of the
  pass.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (BlockLoweringData)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs transArgs_id_heq)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (Expr.ctLeak Com.ctLeak)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
  (regionExportableB bindMemNB wordSig isRegTy)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS (CoveredCom coveredCom_rename)
open Ctxt (Var Valuation)

/-! ## 1. The lowering and the pass -/

/-- **The block lowering of `jasminDialect` into itself by the block `blk`**: types, contexts
    and variables are unchanged, and a binding `e` becomes `blk e`. -/
def legalLowering
    (blk : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Expr jasminDialect Γ t →
      Com jasminDialect Γ t) :
    BlockLoweringData jasminDialect jasminDialect where
  mapTy := fun t => t
  mapCtx := fun Γ => Γ
  mapCtx_cons := fun _ _ => rfl
  mapVar := fun v => v
  lowerExprBlock := blk

/-- The lowering `legalLowering blk` sends the trip-counter type and the bit type to
    themselves. -/
theorem legalLowering_regionTypes
    (blk : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Expr jasminDialect Γ t →
      Com jasminDialect Γ t) :
    NFProg.RegionTypes (legalLowering blk) := ⟨rfl, rfl⟩

/-- The lowering of a program with one result by `NFProg.map` along `legalLowering blk`. -/
def legalMap
    (blk : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Expr jasminDialect Γ t →
      Com jasminDialect Γ t)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t]) :
    NFProg jasminDialect Γ [t] :=
  NFProg.map (legalLowering blk) (legalLowering_regionTypes blk) p (fun v => v)

/-- **The legalisation by the block `blk`** of a program with one result: the program itself
    when no binding is an operation of `isB`, and `legalMap blk` of it otherwise. -/
def legalizeBy (isB : JasminOp → Bool)
    (blk : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Expr jasminDialect Γ t →
      Com jasminDialect Γ t)
    {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t]) :
    NFProg jasminDialect Γ [t] :=
  if p.allOps (fun op => !isB op) then p else legalMap blk p

variable {isB : JasminOp → Bool}
  {blk : {Γ : Ctxt jasminDialect} → {t : JasminTy} → Expr jasminDialect Γ t →
    Com jasminDialect Γ t}

/-- **On a program with no operation of `isB` the pass is the identity.** -/
theorem legalizeBy_eq_of_none {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} (h : p.allOps (fun op => !isB op) = true) :
    legalizeBy isB blk p = p := by
  rw [legalizeBy, ite_eq_left h]

/-- `NFProg.map` along `legalLowering blk` returns `legalMap blk`. -/
theorem map?_legalLowering {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) :
    NFProg.map? (legalLowering blk).toPartial (legalLowering_regionTypes blk) p (fun v => v)
      = some (legalMap blk p) :=
  NFProg.map?_toPartial _ _ _ _

/-- The transport of a valuation of one type along the identity is the valuation. -/
theorem transArgs_id_single {t : JasminTy} (r : Valuation (d := jasminDialect) [t]) :
    transArgs (fun t => t) (fun x => x) r = r := by
  cases r with
  | cons x xs => cases xs; rfl

/-- Every call environment agrees with itself along the identity transport. -/
private theorem callEnv_transports_legal (E : CallEnv jasminDialect)
    (C : String → List JasminTy → List JasminTy → Prop) :
    E.Transports E (fun as => as.map (legalLowering blk).mapTy)
      (fun x => transArgs (legalLowering blk).mapTy (fun x => x) x) C := by
  intro f as rs x _
  exact call_eq_map_of_heq E f (List.map_id' as) (List.map_id' rs) (transArgs_id_heq x) _ _
    (fun r => r) (fun r => transArgs_id_heq r) Option.map_id'.symm

/-! ## 2. Denotation and leakage -/

/-- **The pass keeps the denotation** at every call environment and fuel, for a block that
    denotes the value of the binding. -/
theorem legalizeBy_denoteAt
    (hden : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
      (V : Valuation Γ), (blk e).denote V = e.denote V)
    (E : CallEnv jasminDialect) (fuel : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) (V : Valuation Γ) :
    (legalizeBy isB blk p).denoteAt E fuel V = p.denoteAt E fuel V := by
  unfold legalizeBy
  split
  · rfl
  · have key := NFProg.map?_denoteAt (legalLowering blk).toPartial (fun x => x) (fun V => V)
      (legalLowering_regionTypes blk) (fun _ => True) (fun _ _ => rfl)
      (fun e _ blk' hblk V => by cases hblk; exact hden e V) (fun _ _ => rfl)
      ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ E E fuel p
      (NFProg.covered_of_forall _ (fun _ => trivial) p) (callEnv_transports_legal (blk := blk) E _)
      (fun v => v) V V (FieldDialectBlockDescent.pullV_id _) (legalMap blk p)
      (map?_legalLowering p)
    refine key.trans ?_
    cases NFProg.denoteAt E fuel p V with
    | none => rfl
    | some r => exact congrArg some (transArgs_id_single r)

/-- **The pass keeps the denotation**, at every fuel. -/
theorem legalizeBy_denote [CallDenote jasminDialect]
    (hden : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
      (V : Valuation Γ), (blk e).denote V = e.denote V)
    (fuel : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t]) :
    (legalizeBy isB blk p).denote fuel = p.denote fuel := by
  funext V
  exact legalizeBy_denoteAt hden CallDenote.env fuel p V

/-- **The pass keeps the leakage run** at leakage parameters `Pj` at every fuel, for a block
    that denotes the value of the binding and emits its events at `Pj`. -/
theorem legalizeBy_leakRun {Pj : JLeakParams}
    (hden : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
      (V : Valuation Γ), (blk e).denote V = e.denote V)
    (hleak : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
      (V : Valuation Γ),
      Com.ctLeak (jLeakModel Pj) (blk e) V = Expr.ctLeak (jLeakModel Pj) e V)
    (fuel : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy} (p : NFProg jasminDialect Γ [t])
    (V : Valuation Γ) :
    Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel (legalizeBy isB blk p) V
      = Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel p V := by
  unfold legalizeBy
  split
  · rfl
  · have key := NFProg.map?_leakRun (legalLowering blk).toPartial (fun x => x) (fun V => V)
      (jLeakModel Pj) (jLeakModel Pj) (legalLowering_regionTypes blk) (fun _ => True)
      (fun _ _ => rfl)
      (fun e _ blk' hblk V => by cases hblk; exact hden e V)
      (fun e _ blk' hblk V => by cases hblk; exact hleak e V) (fun _ _ => rfl)
      ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩ fuel p
      (NFProg.covered_of_forall _ (fun _ => trivial) p) (fun v => v) V V
      (FieldDialectBlockDescent.pullV_id _) (legalMap blk p) (map?_legalLowering p)
    refine key.trans ?_
    cases Dialects.NFLeak.NFProg.leakRun (jLeakModel Pj) fuel p V with
    | none => rfl
    | some r => exact congrArg some (Prod.ext (transArgs_id_single r.1) rfl)

/-- **The pass keeps constant time at the source events** at leakage parameters `Pj`, for a
    block that denotes the value of the binding and emits its events at `Pj`. -/
theorem nfct_legalizeBy {Pj : JLeakParams}
    (hden : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
      (V : Valuation Γ), (blk e).denote V = e.denote V)
    (hleak : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t)
      (V : Valuation Γ),
      Com.ctLeak (jLeakModel Pj) (blk e) V = Expr.ctLeak (jLeakModel Pj) e V)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    {L : ComLevelCheck.Labels Γ} {fuel : Nat}
    (h : Dialects.NFLeak.NFCT (jLeakModel Pj) L fuel p) :
    Dialects.NFLeak.NFCT (jLeakModel Pj) L fuel (legalizeBy isB blk p) := by
  intro V₁ V₂ hpub
  rw [legalizeBy_leakRun hden hleak, legalizeBy_leakRun hden hleak]
  exact h V₁ V₂ hpub

/-! ## 3. The tests that read only the calls -/

/-- **A test that reads only the calls** of a program: `F` is `true` at a return, ignores a
    binding, is the conjunction of its values at the parts of a loop or a branch, and at a
    call of `f` the conjunction of `c f` with its value at the continuation. `callFree` is
    the test at `c = fun _ => false`. -/
structure CallTest (c : String → Bool)
    (F : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts → Bool) :
    Prop where
  ret : ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (vs : HVector (fun t => Var Γ t) ts),
    F (NFProg.ret vs) = true
  var : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
    (e : Expr jasminDialect Γ t) (k : NFProg jasminDialect (t :: Γ) ts), F (.var e k) = F k
  forLoop : ∀ {Γ : Ctxt jasminDialect} {cs ts : List JasminTy}
    (count : Var Γ (HasWord64.word (d := jasminDialect))) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ HasWord64.word (d := jasminDialect) :: Γ) cs)
    (k : NFProg jasminDialect (cs ++ Γ) ts), F (.forLoop count inits body k) = (F body && F k)
  ifThenElse : ∀ {Γ : Ctxt jasminDialect} {rs ts : List JasminTy}
    (cond : Var Γ (HasBitType.bit (d := jasminDialect))) (thn els : NFProg jasminDialect Γ rs)
    (k : NFProg jasminDialect (rs ++ Γ) ts),
    F (.ifThenElse cond thn els k) = (F thn && F els && F k)
  whileLoop : ∀ {Γ : Ctxt jasminDialect} {cs ts : List JasminTy}
    (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ Γ) (HasBitType.bit (d := jasminDialect) :: cs))
    (k : NFProg jasminDialect (cs ++ Γ) ts), F (.whileLoop inits body k) = (F body && F k)
  call : ∀ {Γ : Ctxt jasminDialect} {as rs ts : List JasminTy} (f : String)
    (args : HVector (fun t => Var Γ t) as) (k : NFProg jasminDialect (rs ++ Γ) ts),
    F (.call f args k) = (c f && F k)

/-- `callFree` reads only the calls. -/
theorem callTest_callFree : CallTest (fun _ => false) NFProg.callFree :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl⟩

/-- A block spliced before continuations whose programs all have the value `b` of a test
    that reads only the calls gives a program with the value `b`. -/
private theorem splice_callTest_aux {c : String → Bool}
    {F : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts → Bool}
    (hF : CallTest c F) {ts : List JasminTy} (b : Bool) :
    {Δ : Ctxt jasminDialect} → {a : JasminTy} → (blk : Com jasminDialect Δ a) →
    (k : {Δ' : Ctxt jasminDialect} → Ctxt.Hom Δ Δ' → Var Δ' a →
      Option (NFProg jasminDialect Δ' ts)) →
    (∀ {Δ' : Ctxt jasminDialect} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a)
      (q : NFProg jasminDialect Δ' ts), k ren res = some q → F q = b) →
    ∀ {q : NFProg jasminDialect Δ ts}, NFProg.spliceNF? blk k = some q → F q = b
  | _, _, .ret v, _, hk, _, h => hk _ v _ h
  | _, _, .var _ blk, k, hk, _, h => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      exact (hF.var _ _).trans
        (splice_callTest_aux hF b blk _ (fun ren res q hq => hk _ res q hq) hq')

/-- `map?` along `legalLowering blk` keeps the value of a test that reads only the calls. -/
private theorem map_callTest_aux {c : String → Bool}
    {F : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts → Bool}
    (hF : CallTest c F) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom Γ Δ)
      {q : NFProg jasminDialect Δ (ts.map (legalLowering blk).mapTy)},
      NFProg.map? (legalLowering blk).toPartial (legalLowering_regionTypes blk) p ren
        = some q → F q = F p := by
  induction p with
  | ret vs =>
      intro Δ ren q h
      cases h
      exact (hF.ret _).trans (hF.ret _).symm
  | var e k ih =>
      intro Δ ren q h
      obtain ⟨blk', -, h⟩ := Option.bind_eq_some_iff.mp h
      exact (splice_callTest_aux hF _ _ _ (fun ren' res q' hq' => ih _ hq') h).trans
        (hF.var e k).symm
  | forLoop count inits body k ihb ihk =>
      intro Δ ren q h
      obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      exact (hF.forLoop _ _ _ _).trans ((congrArg₂ (fun x y => x && y) (ihb _ hb)
        (ihk _ hk)).trans (hF.forLoop count inits body k).symm)
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren q h
      obtain ⟨t', ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      exact (hF.ifThenElse _ _ _ _).trans ((congrArg₂ (fun x y => x && y)
        (congrArg₂ (fun x y => x && y) (iht _ ht) (ihe _ he)) (ihk _ hk)).trans
        (hF.ifThenElse cond thn els k).symm)
  | whileLoop inits body k ihb ihk =>
      intro Δ ren q h
      obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      have hc : ∀ {Δ' : Ctxt jasminDialect} {x y : JasminTy} {cs : List JasminTy} (e : x = y)
          (r : NFProg jasminDialect Δ' (x :: cs)), F (NFProg.castRetHead e r) = F r :=
        fun e _ => by subst e; rfl
      exact (hF.whileLoop _ _ _).trans ((congrArg₂ (fun x y => x && y)
        ((hc _ b').trans (ihb _ hb)) (ihk _ hk)).trans (hF.whileLoop inits body k).symm)
  | call f args k ih =>
      intro Δ ren q h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      exact (hF.call _ _ _).trans ((congrArg (fun y => c f && y) (ih _ hk)).trans
        (hF.call f args k).symm)

/-- **The pass keeps the value of every test that reads only the calls.** -/
theorem legalizeBy_callTest {c : String → Bool}
    {F : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → NFProg jasminDialect Γ ts → Bool}
    (hF : CallTest c F) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : F (legalizeBy isB blk p) = F p := by
  unfold legalizeBy
  split
  · rfl
  · exact map_callTest_aux hF p (fun v => v) (map?_legalLowering p)

/-- **The pass keeps the absence of `call` and its presence.** -/
theorem legalizeBy_callFree_eq {Γ : Ctxt jasminDialect} {t : JasminTy}
    (p : NFProg jasminDialect Γ [t]) : (legalizeBy isB blk p).callFree = p.callFree :=
  legalizeBy_callTest callTest_callFree p

/-! ## 4. Completeness of the region export test on the image of the pass -/

/-- **The test `regionExportableB` with the test `acc` of the operations** in place of
    `opMemB` at the bindings, by the same recursion. -/
def regionExportableByB (acc : JasminOp → Bool) : {Γ : Ctxt jasminDialect} →
    {ts : List JasminTy} → NFProg jasminDialect Γ ts → Bool
  | _, _, .ret _ => true
  | _, _, .var e k => acc e.op && regionExportableByB acc k
  | _, _, .forLoop _ _ body k => regionExportableByB acc body && regionExportableByB acc k
  | _, _, .ifThenElse _ thn els k =>
      regionExportableByB acc thn && regionExportableByB acc els && regionExportableByB acc k
  | _, _, .whileLoop (cs := cs) _ body k =>
      cs.all isRegTy && regionExportableByB acc body && regionExportableByB acc k
  | _, _, .call (as := as) (rs := rs) _ _ k => wordSig as rs && regionExportableByB acc k

/-- At the test `opMemB` the test `regionExportableByB` is `regionExportableB`. -/
theorem regionExportableByB_opMemB {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) : regionExportableByB opMemB p = regionExportableB p := by
  induction p with
  | ret => rfl
  | var e k ih => simp only [regionExportableByB, regionExportableB, bindMemNB, ih]
  | forLoop _ _ _ _ ihb ihk => simp only [regionExportableByB, regionExportableB, ihb, ihk]
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [regionExportableByB, regionExportableB, iht, ihe, ihk]
  | whileLoop _ _ _ ihb ihk => simp only [regionExportableByB, regionExportableB, ihb, ihk]
  | call _ _ _ ih => simp only [regionExportableByB, regionExportableB, ih]

/-- A block of operations of `opMemB` spliced before continuations that pass
    `regionExportableB` gives a program that passes it. -/
private theorem splice_regionExportableB_aux {ts : List JasminTy} :
    {Δ : Ctxt jasminDialect} → {a : JasminTy} → (blk : Com jasminDialect Δ a) →
    (k : {Δ' : Ctxt jasminDialect} → Ctxt.Hom Δ Δ' → Var Δ' a →
      Option (NFProg jasminDialect Δ' ts)) →
    CoveredCom (fun e' => opMemB e'.op = true) blk →
    (∀ {Δ' : Ctxt jasminDialect} (ren : Ctxt.Hom Δ Δ') (res : Var Δ' a)
      (q : NFProg jasminDialect Δ' ts), k ren res = some q → regionExportableB q = true) →
    ∀ {q : NFProg jasminDialect Δ ts}, NFProg.spliceNF? blk k = some q →
      regionExportableB q = true
  | _, _, .ret v, _, _, hk, _, h => hk _ v _ h
  | _, _, .var _ blk, k, hb, hk, _, h => by
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [regionExportableB, bindMemNB, Bool.and_eq_true]
      exact ⟨hb.1, splice_regionExportableB_aux blk _ hb.2 (fun ren res q hq => hk _ res q hq)
        hq'⟩

/-- `map?` along `legalLowering blk` sends a program of `regionExportableByB acc` to a program
    of `regionExportableB`, when the block of every binding of `acc` binds operations of
    `opMemB` only. -/
private theorem map_regionExportableB_aux {acc : JasminOp → Bool}
    (hcov : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t),
      acc e.op = true → CoveredCom (fun e' => opMemB e'.op = true) (blk e))
    {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableByB acc p = true) :
    ∀ {Δ : Ctxt jasminDialect} (ren : Ctxt.Hom Γ Δ)
      {q : NFProg jasminDialect Δ (ts.map (legalLowering blk).mapTy)},
      NFProg.map? (legalLowering blk).toPartial (legalLowering_regionTypes blk) p ren
        = some q → regionExportableB q = true := by
  induction p with
  | ret vs =>
      intro Δ ren q h
      cases h
      rfl
  | var e k ih =>
      intro Δ ren q h
      simp only [regionExportableByB, Bool.and_eq_true] at hp
      obtain ⟨blk', hblk, h⟩ := Option.bind_eq_some_iff.mp h
      cases hblk
      exact splice_regionExportableB_aux _ _
        (coveredCom_rename opMemB ren _ (hcov e hp.1))
        (fun ren' res q' hq' => ih hp.2 _ hq') h
  | forLoop count inits body k ihb ihk =>
      intro Δ ren q h
      simp only [regionExportableByB, Bool.and_eq_true] at hp
      obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [regionExportableB, Bool.and_eq_true]
      exact ⟨ihb hp.1 _ hb, ihk hp.2 _ hk⟩
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ ren q h
      simp only [regionExportableByB, Bool.and_eq_true] at hp
      obtain ⟨t', ht, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨e', he, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [regionExportableB, Bool.and_eq_true]
      exact ⟨⟨iht hp.1.1 _ ht, ihe hp.1.2 _ he⟩, ihk hp.2 _ hk⟩
  | whileLoop inits body k ihb ihk =>
      intro Δ ren q h
      simp only [regionExportableByB, Bool.and_eq_true] at hp
      obtain ⟨b', hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      have hc : ∀ {Δ' : Ctxt jasminDialect} {x y : JasminTy} {cs : List JasminTy} (e : x = y)
          (r : NFProg jasminDialect Δ' (x :: cs)),
          regionExportableB (NFProg.castRetHead e r) = regionExportableB r :=
        fun e _ => by subst e; rfl
      simp only [regionExportableB, Bool.and_eq_true]
      refine ⟨⟨?_, (hc _ b').trans (ihb hp.1.2 _ hb)⟩, ihk hp.2 _ hk⟩
      exact (congrArg (fun l => l.all isRegTy) (List.map_id' _)).trans hp.1.1
  | call f args k ih =>
      intro Δ ren q h
      simp only [regionExportableByB, Bool.and_eq_true] at hp
      obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [regionExportableB, Bool.and_eq_true]
      refine ⟨?_, ih hp.2 _ hk⟩
      exact (congrArg₂ wordSig (List.map_id' _) (List.map_id' _)).trans hp.1

/-- A program of `regionExportableByB acc` with no operation of `isB` passes
    `regionExportableB`, when every operation of `acc` and not of `isB` is of `opMemB`. -/
private theorem regionExportableB_of_none {acc : JasminOp → Bool}
    (hkeep : ∀ op, acc op = true → isB op = false → opMemB op = true)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} (hp : regionExportableByB acc p = true)
    (hn : p.allOps (fun op => !isB op) = true) : regionExportableB p = true := by
  induction p with
  | ret => rfl
  | var e k ih =>
      simp only [regionExportableByB, NFProg.allOps, Bool.and_eq_true] at hp hn
      simp only [regionExportableB, bindMemNB, Bool.and_eq_true]
      exact ⟨hkeep _ hp.1 (by simpa using hn.1), ih hp.2 hn.2⟩
  | forLoop _ _ _ _ ihb ihk =>
      simp only [regionExportableByB, NFProg.allOps, Bool.and_eq_true] at hp hn
      simp only [regionExportableB, Bool.and_eq_true]
      exact ⟨ihb hp.1 hn.1, ihk hp.2 hn.2⟩
  | ifThenElse _ _ _ _ iht ihe ihk =>
      simp only [regionExportableByB, NFProg.allOps, Bool.and_eq_true] at hp hn
      simp only [regionExportableB, Bool.and_eq_true]
      exact ⟨⟨iht hp.1.1 hn.1.1, ihe hp.1.2 hn.1.2⟩, ihk hp.2 hn.2⟩
  | whileLoop _ _ _ ihb ihk =>
      simp only [regionExportableByB, NFProg.allOps, Bool.and_eq_true] at hp hn
      simp only [regionExportableB, Bool.and_eq_true]
      exact ⟨⟨hp.1.1, ihb hp.1.2 hn.1⟩, ihk hp.2 hn.2⟩
  | call _ _ _ ih =>
      simp only [regionExportableByB, NFProg.allOps, Bool.and_eq_true] at hp hn
      simp only [regionExportableB, Bool.and_eq_true]
      exact ⟨hp.1, ih hp.2 hn⟩

/-- **Completeness of the region export test on the image of the pass.** When the block of
    every binding of an operation of `acc` binds operations of `opMemB` only, and every
    operation of `acc` and not of `isB` is of `opMemB`, a program of `regionExportableByB acc`
    passes `regionExportableB` after `legalizeBy isB blk`. -/
theorem regionExportableB_legalizeBy {acc : JasminOp → Bool}
    (hcov : ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (e : Expr jasminDialect Γ t),
      acc e.op = true → CoveredCom (fun e' => opMemB e'.op = true) (blk e))
    (hkeep : ∀ op, acc op = true → isB op = false → opMemB op = true)
    {Γ : Ctxt jasminDialect} {t : JasminTy} {p : NFProg jasminDialect Γ [t]}
    (hp : regionExportableByB acc p = true) :
    regionExportableB (legalizeBy isB blk p) = true := by
  unfold legalizeBy
  split
  · rename_i hn
    exact regionExportableB_of_none hkeep hp hn
  · exact map_regionExportableB_aux hcov p hp (fun v => v) (map?_legalLowering p)

end CatCrypt.Crypto.SecureCompilation.Haxc
