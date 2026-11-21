/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3Handlers
public import CatCrypt.Crypto.SecureCompilation.Haxc.ExportChainOps

/-!
# The events of the narrowed chain program at word kernels

Let every linked function of a module `m` take words and integers and return a `64`-bit word.
Then every call that `extChain` keeps in its output, and that `narrowPrep` keeps after it, is
a call of a reduce-multiply or field head (`innerHead`), or a call whose argument and result
types are no stack arrays (`regCallB`):

* the translation `nfToCatExt` calls only declarations of `fieldDeclsFor`, which are the
  linked declarations of `linkedDecls m` (at the argument types `sigVariants` gives the word
  and integer parameters) and the declarations of field heads;
* every later step of the chain keeps `callsLoopsAll` (`extChain_callsLoopsAll` is the same
  argument at `wordSig`), and the montify pass adds only reduce-multiply heads;
* the widening fixes the absence of stack arrays, and mask elimination, dead-binding
  elimination and the carry pairs keep the calls.

The tree `mfTree` answers an inner head in place and makes every other call one event at its
signature, so every event of the tree has no array argument and no array result. When the
callees of the table `T` have register results and no array arguments, `EvOK T` is that
condition, which gives the hypothesis `hev` of
`NFCallTreeR3Handlers.r3FA_of_shape_linkedHandlers`.

## Main results

* `extChain_callsAll_regCallB`: the calls of the output of `extChain` at the linked
  declarations of a module of word parameters.
* `narrowPrep_callsAll_regCallB`: `narrowPrep` keeps `callsAll regCallB`.
* `allEv_mfTree_of_callsAll`: the events of `mfTree` of a program of `callsAll regCallB`.
* `allEv_evOK_of_linkedWords`: the hypothesis `hev` of `r3FA_of_shape_linkedHandlers` from
  `hpar` and `hword`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3Ev

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgPasses
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin
  catToJasmin_regionTypes)
open CatCrypt.Crypto.SecureCompilation.VIR.NarrowWords (wideTy narrowPrep maskElimGo
  carryPairGo carryInsert)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (tableOf entryCtx hax64NFWordTy)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (TreeCallEnv nfCallSig obind ofoldl
  owhileIter treeAt pureReader)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont (mfTree mfEnv innerHead)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montTag?)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain (EvOK)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs (resLen)
open CatCrypt.Crypto.SecureCompilation.Haxc.ChainTotal (callsAll callsAll_rename?)
open CatCrypt.Crypto.SecureCompilation.Haxc.ExportChainOps
open _root_.Hax.FieldTag (fieldHeadB)
open Ctxt (Valuation)

/-! ## The signatures of the calls -/

/-- A type of `jasminDialect` other than a stack array. -/
def notArrTy : JasminTy → Bool
  | .stackArr _ _ => false
  | _ => true

/-- **The calls of word kernels**: a call of an inner head (`innerHead`), answered inside
    `mfTree`, or a call whose argument and result types are no stack arrays. -/
def regCallB (f : String) (as rs : List JasminTy) : Bool :=
  innerHead f || (as.all notArrTy && rs.all notArrTy)

/-- The widening keeps the absence of a stack array. -/
@[simp] theorem notArrTy_wideTy (t : JasminTy) : notArrTy (wideTy t) = notArrTy t := by
  cases t <;> rfl

/-- `regCallB` does not change under the widening of the signature. -/
theorem regCallB_wideTy :
    (fun f as rs => regCallB f (as.map wideTy) (rs.map wideTy)) = regCallB := by
  funext f as rs
  simp [regCallB, List.all_map, Function.comp_def]

/-- Argument types without a stack array have no array position. -/
theorem arrArgsOf_of_notArr : ∀ {as : List JasminTy}, as.all notArrTy = true →
    arrArgsOf as = fun _ => none
  | [], _ => rfl
  | t :: as, h => by
      simp only [List.all_cons, Bool.and_eq_true] at h
      funext i
      cases i with
      | zero => cases t <;> simp_all [notArrTy, arrArgsOf]
      | succ i => rw [arrArgsOf_cons_succ, arrArgsOf_of_notArr h.2]

/-- Result types without a stack array have no result length. -/
theorem resLen_of_notArr {rs : List JasminTy} (h : rs.all notArrTy = true) : resLen rs = none := by
  unfold resLen
  split <;> simp_all [notArrTy]

/-! ## The narrow-word stages -/

/-- Mask elimination keeps `callsAll C`: it keeps every call at its symbol and signature. -/
theorem callsAll_maskElimGo (C : String → List JasminTy → List JasminTy → Bool)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ {Δ : Ctxt jasminDialect} (A : NarrowWords.Facts Γ) (ren : Ctxt.Hom Γ Δ),
      callsAll C (maskElimGo p A ren) = callsAll C p := by
  induction p with
  | ret vs => intro Δ A ren; rfl
  | var e k ih =>
      intro Δ A ren
      simp only [maskElimGo]
      split
      · split
        · exact ih _ _
        · exact ih _ _
      · exact ih _ _
  | forLoop count inits body k ihb ihk =>
      intro Δ A ren
      simp only [maskElimGo, callsAll, ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro Δ A ren
      simp only [maskElimGo, callsAll, iht, ihe, ihk]
  | whileLoop inits body k ihb ihk =>
      intro Δ A ren
      simp only [maskElimGo, callsAll, ihb, ihk]
  | call f args k ih =>
      intro Δ A ren
      simp only [maskElimGo, callsAll, ih]

/-- The carry pairs keep `callsAll C`: an inserted binding is no call. -/
theorem callsAll_carryPairGo (C : String → List JasminTy → List JasminTy → Bool)
    {Γ : Ctxt jasminDialect} {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) :
    ∀ prev : Option (Nat × List Nat), callsAll C (carryPairGo prev p) = callsAll C p := by
  induction p with
  | ret vs => intro prev; rfl
  | var e k ih =>
      intro prev
      unfold carryPairGo
      split
      · split
        · simp only [callsAll, ih]
        · unfold carryInsert
          split
          · rename_i e' k' he hk
            simp only [callsAll, callsAll_rename? _ _ hk, ih]
          · simp only [callsAll, ih]
      · simp only [callsAll, ih]
  | forLoop count inits body k ihb ihk =>
      intro prev
      simp only [carryPairGo, callsAll, ihb, ihk]
  | ifThenElse cond thn els k iht ihe ihk =>
      intro prev
      simp only [carryPairGo, callsAll, iht, ihe, ihk]
  | whileLoop inits body k ihb ihk =>
      intro prev
      simp only [carryPairGo, callsAll, ihb, ihk]
  | call fn args k ih =>
      intro prev
      simp only [carryPairGo, callsAll, ih]

/-- **The narrow-word stages keep `callsAll regCallB`.** -/
theorem narrowPrep_callsAll_regCallB {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    {p : NFProg jasminDialect Γ ts} {q : NFProg jasminDialect (Γ.map wideTy) (ts.map wideTy)}
    (hq : narrowPrep p = some q) (hp : callsAll regCallB p = true) :
    callsAll regCallB q = true := by
  obtain ⟨q₀, h₀, rfl⟩ := NarrowWords.narrowPrep_eq_some.mp hq
  have hw : callsAll regCallB q₀ = true := by
    refine ChainTotal.callsAll_map? NarrowWords.widenP NarrowWords.widenP_regionTypes regCallB p
      ?_ _ h₀
    rw [show (fun f as rs => regCallB f (as.map NarrowWords.widenP.mapTy)
      (rs.map NarrowWords.widenP.mapTy)) = regCallB from regCallB_wideTy]
    exact hp
  rw [NarrowWords.carryPair, callsAll_carryPairGo]
  refine FieldDialectStep.callsAll_dce _ _ ?_
  rw [NarrowWords.maskElim, callsAll_maskElimGo]
  exact hw

/-! ## The calls of the chain -/

/-- The argument types `sigVariants` gives at parameter types of words and integers are words
    and integers. -/
theorem mem_sigVariants_words : ∀ {ps as : List NfTy},
    (∀ p ∈ ps, p = .word 64 ∨ p = .int) → as ∈ sigVariants ps → ∀ a ∈ as, a = .word 64 ∨ a = .int
  | [], as, _, h => by
      simp only [sigVariants, List.mem_singleton] at h
      subst h
      simp
  | p :: ps, as, hps, h => by
      simp only [sigVariants, List.mem_flatMap, List.mem_map] at h
      obtain ⟨a, ha, as', has', rfl⟩ := h
      have hp := hps p List.mem_cons_self
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · split at ha <;> simp at ha <;> grind
      · exact mem_sigVariants_words (fun q hq => hps q (List.mem_cons_of_mem _ hq)) has' b hb

/-- **The calls of the translation at the linked declarations of a module of word parameters**:
    a call of a field head, or a call of a linked function at words and integers to a `64`-bit
    word. -/
theorem regCallB_of_mem_fieldDeclsFor {m : HaxModule}
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    {Γ : Ctxt nfDialect} {ts : List NfTy} (p : NFProg nfDialect Γ ts) {d : ExtDecl}
    (hd : d ∈ fieldDeclsFor (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit) p) :
    regCallB d.name ((d.args.map catTy).map catToJasmin.mapTy)
      ([catTy d.ret].map catToJasmin.mapTy) = true := by
  unfold fieldDeclsFor at hd
  rcases List.mem_append.mp hd with hd | hd
  · have hd' := (List.mem_filter.mp hd).1
    simp only [linkedDecls, List.mem_flatMap, List.mem_filter, List.mem_map] at hd'
    obtain ⟨l, ⟨hl, -⟩, as, ⟨has, -⟩, rfl⟩ := hd'
    obtain ⟨hps, hres⟩ := hpar l hl
    have hw := mem_sigVariants_words (ps := l.params.map (·.2))
      (fun p hp => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
        exact hps x hx) has
    have hall : ((as.map catTy).map catToJasmin.mapTy).all notArrTy = true := by
      simp only [List.all_map, List.all_eq_true, Function.comp_apply]
      intro a ha
      rcases hw a ha with rfl | rfl <;> rfl
    simp only [regCallB, hall, hres, Bool.true_and]
    simp only [Bool.or_eq_true]
    right
    rfl
  · have hf : fieldHeadB d.name = true := by
      rcases mem_fieldDeclsOf p hd with ⟨m, q, ht, -⟩ | ⟨m, q, k, hm, -⟩
      · exact _root_.Hax.FieldTag.fieldHeadB_iff.mpr (Or.inl ⟨m, q, ht⟩)
      · exact _root_.Hax.FieldTag.fieldHeadB_iff.mpr (Or.inr ⟨m, q, k, hm⟩)
    simp [regCallB, innerHead, hf]

/-- **Every call of a program `extChain` returns at the linked declarations of a module of word
    parameters is of `regCallB`**: the translation calls declarations of `fieldDeclsFor`
    (`regCallB_of_mem_fieldDeclsFor`), and every later step keeps `callsLoopsAll`. -/
theorem extChain_callsAll_regCallB {m : HaxModule}
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    {Γ : Ctxt nfDialect} {t : NfTy}
    {p : NFProg nfDialect Γ [t]} {q : NFProg jasminDialect (mapCtx (Γ.map catTy))
      [mapTy (catTy t)]}
    (h : (extChain (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit) Γ t).run p = some q) :
    callsAll regCallB q = true := by
  simp only [extChain, extChainCore, Chain.run, Option.bind_eq_some_iff] at h
  obtain ⟨p0, hp0, p1, hp1, p2, hp2, p3, hp3, r, hr, r1, hr1, j, hj, j1, hj1, j2, hj2, j3, hj3,
    j4, hj4, j5, hj5, hq⟩ := h
  obtain rfl := Option.some.inj hq
  change some (NFProg.abortElim NfOp.isAbort p) = some p0 at hp0
  cases hp0
  change (if outTyB t then some p1 else none) = some p2 at hp2
  change some (NFProg.dce p2) = some p3 at hp3
  change nfToCatExt (fieldDeclsFor _ p3) p3 TRd.id = some r at hr
  cases hp3; cases hr1; cases hj1; cases hj3; cases hj4; cases hj5
  have h0 : callsLoopsAll (fun f as rs => regCallB f (as.map catToJasmin.mapTy)
      (rs.map catToJasmin.mapTy)) (fun _ => true) r = true := by
    refine callsLoopsAll_of_loops _ _ r (callsLoopsAll_true r) ?_
    intro f as rs hc
    obtain ⟨d, hd, rfl, rfl, rfl, -⟩ := nfToCatExt_calls _ _ TRd.id r hr f as rs hc
    exact regCallB_of_mem_fieldDeclsFor hpar _ hd
  have h1 := (callsLoopsAll_nfGo (d := catCryptDialect) _ _
    CatCrypt.Crypto.Optimizer.Rewrite.AegraphCat.catRules (Ctxt.Hom.id _) (∅, ∅)
    r).trans h0
  have h2 := callsLoopsAll_map? catToJasmin catToJasmin_regionTypes regCallB (fun _ => true) _
    h1 _ hj
  have h3 := callsLoopsAll_montifyPass _ _ (fun p hp => by simp [regCallB, innerHead, hp]) _ h2
  have h4 := callsLoopsAll_fieldDialect _ _ h3 hj2
  have h5 := callsLoopsAll_lowerSel _ _ _ h4 (fun v => v)
  refine callsAll_of_callsLoopsAll (d := jasminDialect) regCallB (fun _ => true) _ ?_
  unfold CatCrypt.Crypto.Optimizer.Rewrite.AegraphNF.aegraphOptNF
    CatCrypt.Crypto.Optimizer.Rewrite.RangeNFLoop.loopRange
  rw [callsLoopsAll_nfGo (d := jasminDialect), callsLoopsAll_carriedGo]
  exact h5

/-! ## The events of the tree -/

section Tree

variable {E : EventSig} {G : E.Event → Prop}

/-- `obind` of a tree and continuations whose events meet `G` has its events in `G`. -/
theorem allEv_obind {α β : Type} {t : CallTree E (Option α)} {k : α → CallTree E (Option β)}
    (ht : AllEv G t) (hk : ∀ a, AllEv G (k a)) : AllEv G (obind t k) := by
  induction t with
  | ret o =>
      cases o with
      | none => trivial
      | some a => exact hk a
  | vis e c ih => exact ⟨ht.1, fun a => ih a (ht.2 a)⟩

/-- `AllEv` is monotone in the condition. -/
theorem allEv_mono {R : Type} {G' : E.Event → Prop} (hG : ∀ e, G e → G' e) :
    ∀ {t : CallTree E R}, AllEv G t → AllEv G' t := by
  intro t
  induction t with
  | ret _ => intro _; trivial
  | vis e c ih => exact fun ht => ⟨hG e ht.1, fun a => ih a (ht.2 a)⟩

/-- A fold of steps whose events meet `G` has its events in `G`. -/
theorem allEv_ofoldl {α β : Type} {f : β → α → CallTree E (Option β)}
    (hf : ∀ b a, AllEv G (f b a)) : ∀ (l : List α) (b : β), AllEv G (ofoldl f l b)
  | [], _ => trivial
  | a :: l, b => allEv_obind (hf b a) fun b' => allEv_ofoldl hf l b'

/-- An exit-flag iteration of a body whose events meet `G` has its events in `G`. -/
theorem allEv_owhileIter {d : Dialect.{0, 0}} [TyDenote d.Ty] [HasBoolBit d] {cs : List d.Ty}
    {s : Valuation cs → CallTree E (Option (Valuation (HasBitType.bit (d := d) :: cs)))}
    (hs : ∀ a, AllEv G (s a)) : ∀ (n : Nat) (a : Valuation cs),
      AllEv G (owhileIter s n a)
  | 0, _ => trivial
  | n + 1, a => allEv_obind (hs a) fun r => by
      split
      · exact allEv_owhileIter hs n _
      · trivial

end Tree

/-- **The condition on an event of word kernels**: no array argument and no array result. -/
def RegEv (e : (nfCallSig jasminDialect).Event) : Prop :=
  arrArgsOf e.argTys = (fun _ => none) ∧ resLen e.resTys = none

/-- **The events of the tree of a program of `callsAll regCallB` have no array argument and no
    array result**: an inner head is answered in place, every other call is one event at its
    signature. -/
theorem allEv_mfTree_of_callsAll (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : callsAll regCallB p = true) :
    ∀ V : Valuation Γ, AllEv RegEv (mfTree fuel p V) := by
  induction p with
  | ret vs => intro V; trivial
  | var e k ih => exact fun V => allEv_obind trivial fun _ => ih hp _
  | forLoop _ _ _ _ ihb ihk =>
    simp only [callsAll, Bool.and_eq_true] at hp
    exact fun V => allEv_obind (allEv_ofoldl (fun _ _ => ihb hp.1 _) _ _) fun _ => ihk hp.2 _
  | ifThenElse _ _ _ _ iht ihe ihk =>
    simp only [callsAll, Bool.and_eq_true] at hp
    intro V
    refine allEv_obind ?_ fun _ => ihk hp.2 _
    split
    · exact iht hp.1.1 V
    · exact ihe hp.1.2 V
  | whileLoop _ _ _ ihb ihk =>
    simp only [callsAll, Bool.and_eq_true] at hp
    exact fun V => allEv_obind (allEv_owhileIter (fun _ => ihb hp.1 _) _ _) fun _ => ihk hp.2 _
  | call f args k ih =>
    simp only [callsAll, Bool.and_eq_true] at hp
    obtain ⟨h1, h2⟩ := hp
    intro V
    refine allEv_obind ?_ fun _ => ih h2 _
    unfold mfEnv
    dsimp only
    split
    · trivial
    · rename_i hi
      simp only [regCallB, hi, Bool.false_or, Bool.and_eq_true] at h1
      exact ⟨⟨arrArgsOf_of_notArr h1.1, resLen_of_notArr h1.2⟩, fun _ => trivial⟩

/-- **At a table of callees with register results and no array arguments, `EvOK` is `RegEv`.** -/
theorem evOK_of_regEv {T : CalleeTab}
    (hT : ∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = fun _ => none)
    {e : (nfCallSig jasminDialect).Event} (he : RegEv e) : EvOK T e := by
  obtain ⟨ha, hr⟩ := he
  refine ⟨?_, ?_⟩
  · rw [ha]
    unfold calleeAAT
    cases hl : T.lookup e.name with
    | none => simp [hl]
    | some c =>
        have hc : c ∈ T.fns := List.mem_of_find?_eq_some hl
        simp [hl, (hT c hc).2]
  · rw [hr]
    unfold calleeAOT
    cases hl : T.lookup e.name with
    | none => simp [hl]
    | some c =>
        have hc : c ∈ T.fns := List.mem_of_find?_eq_some hl
        obtain ⟨r, hr'⟩ := (hT c hc).1
        simp [hl, hr']

/-! ## The hypothesis `hev` -/

/-- **The hypothesis `hev` of `r3FA_of_shape_linkedHandlers` at word kernels.** When every linked
    function of `m` takes words and integers to a `64`-bit word (`hpar`) and the callee data of
    the linked functions have register results and no array arguments (`hword`), every event of
    the tree of the narrowed chain program meets `EvOK T` at every sub-table `T` of the callee
    data. -/
theorem allEv_evOK_of_linkedWords {m : HaxModule} {σ : AbiLayout}
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    (hword : ∀ c ∈ m.linked.filterMap LinkedFn.calleeData, (∃ r, c.res = .reg r)
      ∧ c.arrArgs = (fun _ => none) ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true) :
    ∀ (T : CalleeTab), T.fns.Sublist (m.linked.filterMap LinkedFn.calleeData) →
      ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
        (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)])
        (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy)
          ([mapTy (catTy q.1)].map NarrowWords.wideTy)), haxToNF σ m = some q →
      (extChain (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit) _ q.1).run q.2
        = some p → NarrowWords.narrowPrep p = some q' →
      ∀ (tf : Nat) (V : Ctxt.Valuation (entryCtx (abiEntry σ))),
        AllEv (EvOK T) (mfTree tf q' (NarrowWords.mapVal (ctMapValD (mapVal V)))) := by
  intro T hT q p q' _ hp hq' tf V
  have hcalls := narrowPrep_callsAll_regCallB hq' (extChain_callsAll_regCallB hpar hp)
  have hT' : ∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = fun _ => none := fun c hc =>
    ⟨(hword c (hT.subset hc)).1, (hword c (hT.subset hc)).2.1⟩
  exact allEv_mono (fun _ he => evOK_of_regEv hT' he)
    (allEv_mfTree_of_callsAll tf q' hcalls _)

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3Ev
