/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeResult

/-!
# The composed event relation against the separation contracts

`NFProgCallTreeR3.ruttF_front_compileRegion` relates a source call event to a target event at the
composition of the event relations of the front (`FrontRE`), of the chain (`ChainRE`) and of the
back half (`BackRE T`). The statement `R3StatementF` relates them by `contractRE`, whose guarded
form is `NFProgCallTreeContract.contractREG`. Two facts carry the composition over:

* every event of a target tree is the call of the linked reader at the entry state of a call
  (`allEvT_targetTree`), so a relation with a family of target trees holds at the event relation
  restricted to such events (`RuttF.and_target`);
* at word and integer argument types, the encodings of the arguments of a leaf call are the words
  of the arguments of the call of `jasminDialect` the chain relates to it, as source integers
  (`encAll_wordsOf`).

With them, a source call related to a target call event of the linked reader at the composition
of the three relations is related to it by `contractREG` (`contractREG_of_comp`), at a module whose
linked functions are linked kernels with scalar parameters and register results.

## Main definitions

* `AllEvT`: every event of a tree satisfies a predicate.
* `IsCallEv`: the call of the linked reader at the entry state of a call.

## Main results

* `allEvT_targetTree`: every event of a target tree of `aMachine` is a call of the reader at the
  entry state of a call.
* `RuttF.and_target`: a relation with a family of trees whose events satisfy a predicate holds at
  the event relation restricted to the predicate.
* `encAll_wordsOf`: the encodings of word and integer arguments related along the chain are the
  words of the transported arguments.
* `contractREG_of_comp`: the composed event relation at call events of the linked reader implies
  `contractREG`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (wordsOf)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr callOps)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCallProbe (entryOf)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (enc encAll)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn wordVal)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig)
open _root_.Hax

/-! ## The events of the target trees -/

/-- Every event of a tree satisfies the predicate `P`. -/
def AllEvT {E : EventSig} {R : Type} (P : E.Event → Prop) : CallTree E R → Prop
  | .ret _ => True
  | .vis e k => P e ∧ ∀ a, AllEvT P (k a)

/-- **The call of a reader at the entry state of a call**: a linked call event whose arguments are
    the values the reader `rd` reads at its entry state, which is the entry state of a call from
    some state with some return index. -/
def IsCallEv (rd : String → AState → List Value) (e : (kSig AState).Event) : Prop :=
  ∃ ret sA, KCall.entry e = entryOf ret sA ∧ KCall.call e = ⟨e.call.name, rd e.call.name e.entry⟩

/-- **The events of a target tree are calls of the reader at the entry of a call.** -/
theorem allEvT_targetTree (prog : List RInstr) (sym : Nat → String)
    (rd : String → AState → List Value) :
    ∀ (fuel pc : Nat) (s : AState), AllEvT (IsCallEv rd) (targetTree aMachine prog sym rd fuel pc s)
  | 0, _, _ => trivial
  | fuel + 1, pc, s => by
    simp only [targetTree]
    split
    · refine ⟨⟨pc + 1, s, rfl, rfl⟩, fun r => ?_⟩
      cases r with
      | some sc => exact allEvT_targetTree prog sym rd fuel _ _
      | none => trivial
    · split
      · trivial
      · trivial
      · exact allEvT_targetTree prog sym rd fuel _ _

/-- **A relation with a family of trees whose events satisfy a predicate** holds at the event
    relation restricted to target events that satisfy the predicate. -/
theorem RuttF.and_target {E₁ E₂ : EventSig} {R₁ R₂ : Type} {h₁ : ∀ e : E₁.Event, E₁.Resp e}
    {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} {P : E₂.Event → Prop} {t₁ : CallTree E₁ R₁}
    {T : Nat → CallTree E₂ R₂} (h : RuttF h₁ RE RA RR Fail t₁ T) :
    (∀ n, AllEvT P (T n)) → RuttF h₁ (fun e₁ e₂ => RE e₁ e₂ ∧ P e₂) RA RR Fail t₁ T := by
  induction h with
  | ret n hT h => exact fun _ => .ret n hT h
  | fail h => exact fun _ => .fail h
  | @vis e₁ e₂ k₁ T K n hT he _ ih =>
    intro hP
    have h0 := hP (n + 0)
    rw [hT 0] at h0
    refine .vis n hT ⟨he, h0.1⟩ fun a₁ a₂ ha => ih a₁ a₂ ha fun m => ?_
    have hm := hP (n + m)
    rw [hT m] at hm
    exact hm.2 a₂
  | skip _ ih => exact fun hP => .skip (ih hP)

/-! ## The arguments along the chain -/

/-- **The encodings of word and integer arguments along the chain.** At argument types each a
    word of 64 bits or an integer, the encodings of arguments related by `VRelL` to arguments of
    `catCryptDialect` are the words of their transports to `jasminDialect` and through the
    widening, as source integers. -/
theorem encAll_wordsOf : ∀ (as : List NfTy), (∀ a ∈ as, a = .word 64 ∨ a = .int) →
    ∀ (x : HVector NfTy.denote as) (y : Ctxt.Valuation (d := catCryptDialect) (as.map catTy)),
      VRelL as x y →
      encAll as x = (wordsOf (transArgs NarrowWords.widenP.mapTy
        (fun x => NarrowWords.transTy x)
        (transArgs catToJasmin.mapTy (fun x => ctTransTy x) y))).map wordVal
  | [], _, .nil, .nil, _ => rfl
  | a :: as, ha, .cons x xs, .cons y ys, ⟨hxy, hr⟩ => by
    have ih := encAll_wordsOf as (fun b hb => ha b (List.mem_cons_of_mem _ hb)) xs ys hr
    rcases ha a List.mem_cons_self with rfl | rfl
    · rw [encAll, ih]
      change _ = List.map wordVal
        ((NarrowWords.transTy (ctTransTy (t := catTy (NfTy.word 64)) y)).setWidth 64 ::
          wordsOf (transArgs NarrowWords.widenP.mapTy (fun x => NarrowWords.transTy x)
            (transArgs catToJasmin.mapTy (fun x => ctTransTy x) ys)))
      cases hxy
      rfl
    · rw [encAll, ih]
      change _ = List.map wordVal
        ((NarrowWords.transTy (ctTransTy (t := catTy NfTy.int) y)).setWidth 64 ::
          wordsOf (transArgs NarrowWords.widenP.mapTy (fun x => NarrowWords.transTy x)
            (transArgs catToJasmin.mapTy (fun x => ctTransTy x) ys)))
      rw [List.map_cons]
      congr 1
      change Value.int x = Value.int _
      rw [show x = (y.toNat : Int) from hxy]
      rfl

/-! ## The composed event relation -/

section Comp

open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain (CompRE)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBack (BackRE)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCompose (FrontRE)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion (ChainRE)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG
  contractREG_of_backRE)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall

/-- The parameters of the data of a callee without array positions are scalars. -/
theorem ins_scalar_of_arrArgs {c : CalleeData} (h : c.arrArgs = fun _ => none) :
    ∀ p ∈ c.ins, p.2 = .scalar := by
  intro p hp
  simp only [CalleeData.ins, h, List.mem_mapIdx] at hp
  obtain ⟨i, -, rfl⟩ := hp
  rfl

/-- **The composed event relation at call events of the linked reader implies `contractREG`.**
    Let the linked functions of `m` have distinct names and each be a linked kernel, the functions
    of the table `T` be among their data, each with a register result and no array position, and
    the leaf calls the front relates to source calls have word and integer argument types. A
    source call related to a target call event of the linked reader at the entry of a call by the
    composition of the event relations of the front, the chain and the back half is related to it
    by `contractREG`. -/
theorem contractREG_of_comp {m : HaxModule} {T : CalleeTab}
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hsub : T.fns.Sublist (m.linked.filterMap LinkedFn.calleeData))
    (hword : ∀ c ∈ T.fns, (∃ r, c.res = .reg r) ∧ c.arrArgs = (fun _ => none))
    (hty : ∀ e₀ e₁, FrontRE m e₀ e₁ → ∀ a ∈ e₁.argTys, a = .word 64 ∨ a = .int)
    {e₀ : linkSig.Event} {e₅ : (kSig AState).Event}
    (h : CompRE (FrontRE m) (CompRE ChainRE
      (fun e₄ e₅ => BackRE T e₄ e₅ ∧ IsCallEv (linkRead m) e₅)) e₀ e₅) :
    contractREG m e₀ e₅ := by
  obtain ⟨e₁, hF, e₄, ⟨e₃, ⟨e₂, hE, hM⟩, hW⟩, hB, ret, sA, hent, hcall⟩ := h
  have htyF := hty e₀ e₁ hF
  obtain ⟨hn1, ha1, l, hl, -⟩ := hF
  obtain ⟨n₂, as₂, rs₂, xs₂⟩ := e₂
  obtain ⟨hn2, hty2, -, hv2⟩ := hE
  dsimp only at hn2 hty2
  subst hty2
  subst hM
  subst hW
  -- The source call at the words of the call event of `jasminDialect`.
  have he₀ : e₀ = ⟨e₁.name, (wordsOf (transArgs NarrowWords.widenP.mapTy
      (fun x => NarrowWords.transTy x)
      (transArgs catToJasmin.mapTy (fun x => ctTransTy x) xs₂))).map wordVal⟩ := by
    obtain ⟨n₀, a₀⟩ := e₀
    dsimp only at hn1 ha1 hl ⊢
    rw [hn1, ha1, encAll_wordsOf _ htyF _ _ hv2]
  generalize hev : (⟨n₂, ((e₁.argTys.map catTy).map catToJasmin.mapTy).map
      NarrowWords.widenP.mapTy, (rs₂.map catToJasmin.mapTy).map NarrowWords.widenP.mapTy,
      transArgs NarrowWords.widenP.mapTy (fun x => NarrowWords.transTy x)
        (transArgs catToJasmin.mapTy (fun x => ctTransTy x) xs₂)⟩ :
      NFProgCallTree.NFCall jasminDialect) = ev at hB
  have hevn : ev.name = e₀.name := by rw [← hev, ← hn1, ← hn2]
  have hevw : (wordsOf (transArgs NarrowWords.widenP.mapTy (fun x => NarrowWords.transTy x)
      (transArgs catToJasmin.mapTy (fun x => ctTransTy x) xs₂))) = wordsOf ev.args := by
    rw [← hev]
  -- The target event at the linked reader.
  obtain ⟨⟨cn, cargs⟩, entry⟩ := e₅
  dsimp only at hent hcall
  subst hent
  obtain ⟨hn5, c, hc, hw5⟩ := id hB
  dsimp only at hn5
  simp only [LinkCall.mk.injEq] at hcall
  obtain ⟨-, rfl⟩ := hcall
  subst hn5
  -- The linked function of the callee.
  have hl' : m.linked.find? (·.name == ev.name) = some l := by rw [hevn]; exact hl
  obtain ⟨hcm, hcn⟩ := CalleeTab.lookup_spec hc
  obtain ⟨l', hl'm, hlc⟩ := List.mem_filterMap.mp (hsub.subset hcm)
  have hn' := (CatCrypt.Crypto.Hax.LinkedFn.calleeData_eq hlc).2.1
  have hll : l' = l := by
    have h1 := find?_name_of_nodup hnd hl'm
    rw [← hn', hcn, hl'] at h1
    exact (Option.some.inj h1).symm
  subst hll
  obtain ⟨⟨r, hres⟩, harr⟩ := hword c hcm
  have hkind : kernelKind l' c = .ins l' c.ins c.resReg := by
    simp only [kernelKind, hres]
  have htop := ((hk l' hl'm).kind_facts hlc).1
  rw [hkind] at htop
  obtain ⟨-, hL, -⟩ := htop
  rw [he₀, hevw, show e₁.name = ev.name by rw [hevn, hn1]]
  exact contractREG_of_backRE (hk l' hl'm) hl' hc hL (ins_scalar_of_arrArgs harr) ret sA hB

end Comp

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvent
