/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3Shape

/-!
# The calls of the source program of the entry, from the typing of the front

The source program `nfSrcProgC` of the entry of a module is typed by `crateSigOf` at the prepared
callees followed by the linked functions, and every round of the inlining `HaxModule.inline?`
checks that each call of a function of the module has a body in the library of the prepared
callees. Together they give `GoodCall` at every call of the program except for the argument
types of a call of a linked function: `crateSigOf` lets an argument of type `int` fit a parameter
of type `word 64` (`argTysFit`), while `GoodCall` asks the parameter types themselves. At a call
without an argument of type `int` the two agree, since the parameters of a linked function that
`haxToNF` accepts are words or arrays of words (`linkSigOk`).

## Main definitions

* `IntArgFree`: a call without an argument of type `int`.

## Main results

* `opsNB_hasOp`: an operation of a program of `opsNB P` satisfies `P`.
* `argTysFit_eq`: argument types that fit parameter types other than `int`, none of them `int`,
  are the parameter types.
* `goodCallE`: `GoodCall` at every operation of the source program of the entry, from the
  translation of the module and calls without an argument of type `int`.
* `r3FG_of_shape_int`: the conclusion of `R3StatementFG` at a module, from its shape, with
  `GoodCall` of the entry replaced by calls without an argument of type `int`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeGoodCall

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.Hax (HaxModule ModFn LinkedFn find?_prep)
open CatCrypt.Crypto.Hax.ImpToNF (CrateFn crateSigOf argTysFit hax64SigOf hax64NFWordTy entryCtx)
open CatCrypt.Crypto.Hax.NFInline (crateOp crateLib crateCallOp crateInlineOk noCrateCall
  crateInline? crateInline?_eq_some)
open CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete (frontOp opsNB)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontModule (OpOk GoodCall)

/-- A call without an argument of type `int`. -/
def IntArgFree (_ : String) (as : List NfTy) (_ : NfTy) : Prop := NfTy.int ∉ as

/-- **An operation of a program of `opsNB P` satisfies `P`.** -/
theorem opsNB_hasOp {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
    [HasBoolBit d] {P : d.Op → Bool} {W : List d.Ty → Bool} {Γ : Ctxt d} {ts : List d.Ty}
    (p : NFProg d Γ ts) (hp : opsNB P p W = true) : ∀ o, p.HasOp o → P o = true := by
  induction p with
  | ret => intro o h; cases h
  | var e k ih =>
    simp only [opsNB, Bool.and_eq_true] at hp
    intro o h
    rcases h with h | h
    · exact h ▸ hp.1
    · exact ih hp.2 o h
  | forLoop _ _ body k ihb ihk =>
    simp only [opsNB, Bool.and_eq_true] at hp
    intro o h
    rcases h with h | h
    · exact ihb hp.1 o h
    · exact ihk hp.2 o h
  | ifThenElse _ thn els k iht ihe ihk =>
    simp only [opsNB, Bool.and_eq_true] at hp
    intro o h
    rcases h with h | h | h
    · exact iht hp.1.1 o h
    · exact ihe hp.1.2 o h
    · exact ihk hp.2 o h
  | whileLoop _ body k ihb ihk =>
    simp only [opsNB, Bool.and_eq_true] at hp
    intro o h
    rcases h with h | h
    · exact ihb hp.1.2 o h
    · exact ihk hp.2 o h
  | call => simp [opsNB] at hp

/-- A type of `hax64NFWordTy` is `int` or the `64`-bit word. -/
theorem wordTy_cases {t : NfTy} (h : hax64NFWordTy t = true) : t = .int ∨ t = .word 64 := by
  unfold hax64NFWordTy at h
  split at h <;> simp_all

/-- **Argument types that fit parameter types other than `int`, none of them `int`, are the
    parameter types.** -/
theorem argTysFit_eq : ∀ {ps as : List NfTy}, argTysFit ps as = true → (∀ p ∈ ps, p ≠ .int) →
    NfTy.int ∉ as → as = ps
  | [], [], _, _, _ => rfl
  | p :: ps, a :: as, h, hp, ha => by
    simp only [argTysFit, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    simp only [List.mem_cons, not_or] at ha
    have hp' : p ≠ .int := hp p List.mem_cons_self
    have hpa : a = p := by
      rcases h.1 with h1 | h1
      · exact h1.symm
      · obtain ⟨h1, h2⟩ := h1
        rcases wordTy_cases h1 with rfl | rfl
        · exact absurd rfl hp'
        rcases wordTy_cases h2 with rfl | rfl
        · exact absurd rfl ha.1
        rfl
    rw [hpa, argTysFit_eq h.2 (fun q hq => hp q (List.mem_cons_of_mem _ hq)) ha.2]
  | [], _ :: _, h, _, _ => by simp [argTysFit] at h
  | _ :: _, [], h, _, _ => by simp [argTysFit] at h

/-- A parameter type of a linked function whose signature passes `linkSigOk` is no `int`. -/
theorem param_ne_int {l : LinkedFn} (h : linkSigOk l = true) : ∀ p ∈ l.params.map (·.2),
    p ≠ .int := by
  intro p hp
  simp only [linkSigOk, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have := h.1 q hq
  intro he
  rw [he] at this
  simp [linkResOk] at this

/-- The first linked callee of a module with a name is the callee of the first linked
    function with the name. -/
theorem find?_linkedFns (m : HaxModule) (g : String) :
    m.linkedFns.find? (·.name == g) = (m.linked.find? (·.name == g)).map LinkedFn.callee := by
  rw [HaxModule.linkedFns, List.find?_map]
  rfl

/-- **`GoodCall` at an operation the front types and the inlining checks.** An operation typed
    by the call typing of the entry, whose call of a function of `m` has a body in the library of
    the prepared callees, and whose call has no argument of type `int`, satisfies `GoodCall m`,
    when the linked functions pass `linkSigOk`. -/
theorem goodCall_of_op {m : HaxModule} (hsig : ∀ l ∈ m.linked, linkSigOk l = true) :
    ∀ o : NfOp, frontOp (crateSigOf (m.prepared nfBody ++ m.linkedFns) hax64SigOf) o = true →
      (crateCallOp (m.prepared nfBody) o = true →
        ((crateLib (m.prepared nfBody) m.linkSig).op o).isSome = true) →
      OpOk IntArgFree o → OpOk (GoodCall m) o := by
  intro o
  induction o with
  | named n o ih => exact ih
  | call f as r =>
    intro hS hC hI
    simp only [frontOp, decide_eq_true_eq] at hS
    simp only [OpOk, IntArgFree] at hI
    simp only [OpOk, GoodCall]
    unfold crateSigOf at hS
    rw [List.find?_append, HaxModule.prepared, find?_prep, find?_linkedFns] at hS
    cases hf : m.fns.find? (·.name == f) with
    | some fn =>
      rw [hf] at hS
      simp only [Option.map_some, Option.some_or] at hS
      split at hS
      · refine ⟨?_, ?_⟩
        · have h1 : crateCallOp (m.prepared nfBody) (.call f as r) = true := by
            simp only [crateCallOp, HaxModule.prepared, find?_prep, hf, Option.map_some,
              Option.isSome_some]
          exact hC h1
        · exact (Option.some.inj hS).symm
      · cases hS
    | none =>
      rw [hf] at hS
      simp only [Option.map_none, Option.none_or] at hS
      cases hl : m.linked.find? (·.name == f) with
      | some l =>
        rw [hl] at hS
        simp only [Option.map_some] at hS
        split at hS
        · rename_i hfit
          have hmem := List.mem_of_find?_eq_some hl
          exact ⟨argTysFit_eq hfit (param_ne_int (hsig l hmem)) hI,
            (Option.some.inj hS).symm⟩
        · cases hS
      | none =>
        rw [hl] at hS
        exact hS
  | _ => intro _ _ _; trivial

/-- **`GoodCall` at every operation of the source program of the entry.** When `haxToNF`
    returns `q` on `m` with the source program `p` of the entry, and no call of `p` has an
    argument of type `int`, every operation of `p` satisfies `GoodCall m`: the call typing of
    the front gives the result type of a function of `m`, the parameter types of a linked
    function and the typing `hax64SigOf` of every other call, and the inlining rounds give a body
    in the library to every call of a function of `m`. -/
theorem goodCallE {m : HaxModule} {σ : AbiLayout}
    {q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]}
    {p : NFProg nfDialect (entryCtx (abiEntry σ)) [q.1]} (hq : haxToNF σ m = some q)
    (hp : nfSrcProgC (m.prepared nfBody ++ m.linkedFns) σ (bindConsts σ.consts m.entry)
      = some ⟨q.1, p⟩)
    (hint : ∀ o, p.HasOp o → OpOk IntArgFree o) :
    ∀ o, p.HasOp o → OpOk (GoodCall m) o := by
  obtain ⟨-, -, -, p', hp', hinl⟩ := haxToNF_eq_some hq
  have hpp : p' = p := by
    rw [hp] at hp'
    exact eq_of_heq (Sigma.mk.inj (Option.some.inj hp')).2.symm
  subst hpp
  have hsig := (haxToNF_eq_some_sig hq).1
  have hops : opsNB (frontOp (crateSigOf (m.prepared nfBody ++ m.linkedFns) hax64SigOf)) p'
      (fun cs => cs.all CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB) = true := by
    unfold nfSrcProgC at hp
    split at hp
    · obtain ⟨o, ho, ho'⟩ := Option.map_eq_some_iff.mp hp
      have key : ∀ (s s' : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t]), s = s' →
          opsNB (frontOp (crateSigOf (m.prepared nfBody ++ m.linkedFns) hax64SigOf)) s.2
            (fun cs => cs.all CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB) = true →
          opsNB (frontOp (crateSigOf (m.prepared nfBody ++ m.linkedFns) hax64SigOf)) s'.2
            (fun cs => cs.all CatCrypt.Crypto.Hax.ImpToNF.whileCarryOkB) = true := by
        rintro s s' rfl h
        exact h
      exact key ⟨o.t, o.prog⟩ ⟨q.1, p'⟩ ho' (FrontComplete.impToNF_prog_frontOpLoop _ _ _ _ o ho)
    · cases hp
  have hok : crateInlineOk (m.prepared nfBody) m.depth p' m.linkSig = true :=
    (crateInline?_eq_some (show crateInline? (m.prepared nfBody) m.depth p' m.linkSig
      = some q.2 from hinl)).1
  intro o ho
  refine goodCall_of_op hsig o (opsNB_hasOp p' hops o ho) ?_ (hint o ho)
  intro hc
  cases hd : m.depth with
  | zero =>
    rw [hd] at hok
    simp only [crateInlineOk, Bool.and_eq_true] at hok
    have hn := (CatCrypt.Crypto.Hax.NFInline.noCrateCall_iff _ _).mp hok.2 o ho
    rw [hc] at hn
    cases hn
  | succ n =>
    rw [hd] at hok
    simp only [crateInlineOk, NFProg.inlineIterOk, Bool.and_eq_true] at hok
    have ha := (NFProg.allOps_iff _ p').mp hok.1.1 o ho
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at ha
    rcases ha with ha | ha
    · exact ha
    · rw [hc] at ha; cases ha

section Statement

open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin)
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee (CalleeRun)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageAddrCallMeets (CalleeKind)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (tableOf entryCtx EntryVals)
open CatCrypt.Crypto.Hax (HaxModule)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (TreeCallEnv nfCallSig NFCall treeAt)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig leafHandler linkReader
  OutRel ExtRE ExtRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt (MapRE MapRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain (CompRE CompRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont (mfTree innerHead)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeEvents (AllEv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefChain (EvOK)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRefBack (BackRE BackRA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCompose (answerOut FrontRE FrontRA
  FrontRR)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion (ChainRE ChainRA ChainRR)
open _root_.Hax

open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeR3 (keepL)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeKinds (contractRunOf summaryOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (contractRAC)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (OutTy)
open CatCrypt.Crypto.Hax (LinkedFn)

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLinkReloc (regionProg)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTarget (symOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeRegion (eq_none_of_outRel mfTree_castProg)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (pureReader eventEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContracts (R3StatementFG)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeTyped (FrontRET)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeModule (GoodEv)
open CatCrypt.Crypto.Hax.NFInline (crateOp)

/-- **The conclusion of `R3StatementFG` at a module, from its shape, with calls without an
    argument of type `int`.** The statement of `NFCallTreeR3Shape.r3FG_of_shape` with the typing
    `GoodCall` of the calls of the source program of the entry replaced by calls without an
    argument of type `int` (`goodCallE`). -/
theorem r3FG_of_shape_int {m : HaxModule} {σ : AbiLayout} {fname : String} {P : Lprog}
    {bytes : List (BitVec 8)} (hc : compileA m σ fname = some (P, bytes))
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hn : narrowOk m σ = false) (hpt : pairTailOf m σ = none)
    (hcf : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]), haxToNF σ m = some q →
      (extChain (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit) _ q.1).run q.2
        = some p → p.callFree = false)
    (tE : TreeCallEnv leafSig nfDialect)
    (htE : ∀ (f : String) (as rs : List NfTy) (x : Ctxt.Valuation (d := nfDialect) as),
      tE.call f as rs x = .ret none)
    (h₂ : ∀ e : (nfCallSig catCryptDialect).Event, (nfCallSig catCryptDialect).Resp e)
    (h₃ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (hh₂ : ∀ e₁ e₂, ExtRE e₁ e₂ → ExtRA e₁ e₂
      (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e₁) (h₂ e₂))
    (hh₃ : ∀ e₁ e₂, MapRE catToJasmin (fun x => ctTransTy x) e₁ e₂ →
      MapRA catToJasmin (fun x => ctTransTy x) e₁ e₂ (h₂ e₁) (h₃ e₂))
    (hinner : ∀ (f : String) (as rs : List JasminTy) (x : Ctxt.Valuation (d := jasminDialect) as),
      innerHead f = true →
        h₃ ⟨f, as, rs, x⟩ = (montEnv (fieldEnv CallEnv.empty)).call f as rs x)
    (hhC : ∀ e₁ e₂, ChainRE e₁ e₂ → ChainRA e₁ e₂
      (leafHandler (tableOf (m.linkTable CatCrypt.Crypto.Hax.hax64WExit)) e₁) (h₃ e₂))
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    (hword : ∀ c ∈ m.linked.filterMap LinkedFn.calleeData, (∃ r, c.res = .reg r)
      ∧ c.arrArgs = (fun _ => none) ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true)
    (hin : ∀ l ∈ m.linked, innerHead l.name = false) (d : CalleeKind) (tr₀ : List CTLeak)
    (hev : ∀ (T : CalleeTab), T.fns.Sublist (m.linked.filterMap LinkedFn.calleeData) →
      ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
        (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)])
        (q' : NFProg jasminDialect ((nfCtx σ).map NarrowWords.wideTy)
          ([mapTy (catTy q.1)].map NarrowWords.wideTy)), haxToNF σ m = some q →
      (extChain (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit) _ q.1).run q.2
        = some p → NarrowWords.narrowPrep p = some q' →
      ∀ (tf : Nat) (V : Ctxt.Valuation (entryCtx (abiEntry σ))),
        AllEv (GoodEv m d T h₃) (mfTree tf q' (NarrowWords.mapVal (ctMapValD (mapVal V)))))
    (hspine : NFCallTreeInlineSpine.spineArgsOk m.entry.erase = true)
    (hfs : ∀ f ∈ m.fns, NFCallTreeInlineSpine.spineArgsOk f.texpr.erase = true)
    (hint : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg nfDialect (entryCtx (abiEntry σ)) [q.1]), haxToNF σ m = some q →
      nfSrcProgC (m.prepared nfBody ++ m.linkedFns) σ (bindConsts σ.consts m.entry)
        = some ⟨q.1, p⟩ → ∀ o, p.HasOp o → NFCallTreeFrontModule.OpOk IntArgFree o)
    (hgood : ∀ g as r b, crateOp (m.prepared nfBody) (.call g as r) m.linkSig = some b →
      ∀ o, b.HasOp o → NFCallTreeFrontModule.OpOk (NFCallTreeFrontModule.GoodCall m) o) :
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      decodeLprog bytes = some (pc ++ shiftProg pc.length Q) ∧
      ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
        ∀ fuelC fuel,
          RuttF (linkHandler m) (contractREG m) (contractRAC m) (resRel σ sa) srcFail
            (nfTree (moduleTreeTable m CatCrypt.Crypto.Hax.hax64WExit fuelC) fuel
              m.entry.erase env)
            (fun fuelT => targetTree aMachine pc sym (linkRead m) fuelT 0 sa) :=
  NFCallTreeR3Shape.r3FG_of_shape hc hnd hk hn hpt hcf tE htE h₂ h₃ hh₂ hh₃ hinner hhC hpar hword
    hin d tr₀ hev hspine hfs (fun q p hq hp => goodCallE hq hp (hint q p hq hp)) hgood

end Statement

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeGoodCall
