/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls

/-!
# Target families from segments of the target run

A relation by `RuttF` between a source call tree and the family of the target trees of a
decoded program is built from a simulation cut at the calls of the target program: an
invariant between source trees and target positions and states such that, from every related
pair, the target reaches a return without call matched by the source leaf, or reaches a `call`
whose linked event is related to the source event and whose answers, related to the source
answers, return to related pairs; a source event that the target does not perform keeps the
invariant at the answer of the source handler. The fuel of each segment is then the length of
its path of steps (`targetTree_of_reaches`, `targetTree_of_reaches_call`).

The back half without a table of linked functions accepts printed bodies of the class
`printedAddrWB` only, which hold no call, so the program its bytes decode to holds no
instruction `call` and its halting runs are paths without call.

## Main definitions

* `SegSim`: a simulation of a source call tree by the target program cut at its calls.

## Main results

* `ruttF_of_segSim`: a simulation cut at the calls relates every related source tree to the
  family of the target trees from its target position and state.
* `noCall_of_printedAddrWB`, `noCall_of_regionBack`, `noCall_of_compileRegion`: the decoded
  program of a body of `printedAddrWB`, of `regionBack` without a table and of `compileRegion`
  holds no `call`.
* `regionBack_correct_noCall`: `regionBack_correct` with a halting path without call.
* `ruttF_compileRegion_callFree'`: the back half on a program without `call` at a target fuel
  per segment, without a hypothesis on the decoded program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsBack

open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr callOps retOps)

/-! ## Simulations cut at the calls of the target -/

section Seg

variable {σ : Type} (M : Machine σ) (prog : List RInstr) (sym : Nat → String)
  (rd : String → σ → List _root_.Hax.Value)
  {E₁ : EventSig} {R₁ : Type} (h₁ : ∀ e : E₁.Event, E₁.Resp e)
  (RE : E₁.Event → (kSig σ).Event → Prop)
  (RA : (e₁ : E₁.Event) → (e₂ : (kSig σ).Event) → E₁.Resp e₁ → (kSig σ).Resp e₂ → Prop)
  (RR : R₁ → Option σ → Prop) (Fail : R₁ → Prop)

/-- The linked event of a `call` of the target `tg` reached in the state `s`: the call of the
    symbol `sym tg` at the arguments `rd` reads off the entry state after the stack operations
    of the call. -/
def callEvent (pc tg : Nat) (s : σ) : (kSig σ).Event :=
  (⟨⟨sym tg, rd (sym tg) ((callOps (pc + 1)).foldl M.exec s)⟩,
    (callOps (pc + 1)).foldl M.exec s⟩ : KCall σ)

/-- **A simulation of source call trees by the target program cut at its calls.** From every
    source tree and target index and state related by `Inv`: a failed source leaf; a source
    leaf matched by a halting path without call to a state related to it by `RR`; a source
    event matched by a path of steps to a `call` whose linked event `RE` relates to it, at every
    answer related to a source answer by `RA` the source continuation being a failed leaf or the
    answer a returned state from which the target continues after the call related to the
    source continuation at that answer; or a source
    event that the target does not perform, the source continuation at the answer of the
    source handler related to the same index and state. -/
def SegSim (Inv : CallTree E₁ R₁ → Nat → σ → Prop) : Prop :=
  ∀ t₁ pc s, Inv t₁ pc s →
    (∃ r₁, t₁ = .ret r₁ ∧ (Fail r₁ ∨ ∃ s', HaltsNoCall M prog pc s s' ∧ RR r₁ (some s')))
    ∨ ∃ e₁ k₁, t₁ = .vis e₁ k₁ ∧
      ((∃ pc' tg s', Reaches M prog pc s pc' s' ∧ prog[pc']? = some (.call tg)
          ∧ RE e₁ (callEvent M sym rd pc' tg s')
          ∧ ∀ a₁ a₂, RA e₁ (callEvent M sym rd pc' tg s') a₁ a₂ →
            (∃ r, k₁ a₁ = .ret r ∧ Fail r)
            ∨ ∃ sc, a₂ = some sc ∧ Inv (k₁ a₁) (pc' + 1) (retOps.foldl M.exec sc))
        ∨ Inv (k₁ (h₁ e₁)) pc s)

/-- **A simulation cut at the calls gives the relation with the target family.** Under a
    simulation `SegSim` with the invariant `Inv`, every source tree related by `Inv` to an
    index and a state is related by `RuttF` to the family of the target trees from them. -/
theorem ruttF_of_segSim {Inv : CallTree E₁ R₁ → Nat → σ → Prop}
    (hS : SegSim M prog sym rd h₁ RE RA RR Fail Inv) :
    ∀ (t₁ : CallTree E₁ R₁) (pc : Nat) (s : σ), Inv t₁ pc s →
      RuttF h₁ RE RA RR Fail t₁ fun n => targetTree M prog sym rd n pc s := by
  intro t₁
  induction t₁ with
  | ret r₁ =>
    intro pc s hI
    rcases hS _ pc s hI with ⟨r, hr, hf | ⟨s', hh, hR⟩⟩ | ⟨e₁, k₁, he, -⟩
    · cases hr; exact .fail hf
    · cases hr
      obtain ⟨n, hn⟩ := targetTree_of_haltsNoCall M prog sym rd hh
      exact .ret n (hn 0) hR
    · cases he
  | vis e₁ k₁ ih =>
    intro pc s hI
    rcases hS _ pc s hI with ⟨r, hr, -⟩ | ⟨e, k, he, hc | hk⟩
    · cases hr
    · cases he
      obtain ⟨pc', tg, s', hr, hcall, hE, hA⟩ := hc
      obtain ⟨n, hn⟩ := targetTree_of_reaches_call M prog sym rd hr hcall
      refine .vis n hn hE fun a₁ a₂ ha => ?_
      rcases hA a₁ a₂ ha with ⟨r, hr, hf⟩ | ⟨sc, rfl, hI'⟩
      · rw [hr]; exact .fail hf
      · exact ih a₁ _ _ hI'
    · cases he
      exact .skip (ih _ pc s hk)

end Seg

/-! ## The back half without a table halts without a call -/

section NoCall

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lcmd Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysAbiShape (DShape leaFrame)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeGen (shapeOf shapesD shapeOfBytes_ok)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodeLayout
  (decodableLcmd decodeLprog_encodeLfundefBytes fundefLayout fundefItems)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedCFG
  (blkOf shapesOf_spec expectedFrom_fundef)
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrW
  (printedAddrWB bodyFactsW_of targetsOK_ofW)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog Params)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytes (encodeLfundefBytes)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree

/-- A decoded instruction `call` of a shape comes from a shape of a call. -/
theorem shape_of_mem_blkOf {body : Lcmd} {shs : List DShape} {sh : DShape} {tg : Nat}
    (h : RInstr.call tg ∈ blkOf body shs sh) :
    ∃ l, sh = .one (.call l) ∨ sh = .one (.callSym l) := by
  rcases sh with (_ | _ | _ | _ | _) | pcs <;>
    simp_all [blkOf, DShape.ops']

/-- An instruction whose shape is that of a call is a call. -/
theorem lcall_of_shapeOf {P : Params} {i : JasminLprogExport.LinstrR}
    {l : JasminLprogExport.LLabel} {sh : DShape} (hs : shapeOf P i = some sh)
    (hc : sh = .one (.call l) ∨ sh = .one (.callSym l)) :
    ∃ ra f l', i = .Lcall ra (f, l') := by
  cases i with
  | Lopn ds o ss =>
    simp only [shapeOf] at hs
    rcases shapeOfBytes_ok hs with ⟨q, rfl, -⟩ | ⟨pcs, rfl, -⟩ <;> rcases hc with h | h <;>
      cases h
  | Lcall ra t => exact ⟨ra, t.1, t.2, rfl⟩
  | _ => rcases hc with rfl | rfl <;> simp only [shapeOf] at hs <;> (try split at hs) <;> simp_all

/-- **The decoded program of a body of `printedAddrWB` holds no `call`.** -/
theorem noCall_of_printedAddrWB {body : Lcmd} (h : printedAddrWB body = true)
    {prog : List RInstr} (hd : decodeLprog (encodeLfundefBytes body) = some prog) :
    ∀ (i tg : Nat), prog[i]? ≠ some (RInstr.call tg) := by
  obtain ⟨shs, hF⟩ := bodyFactsW_of h
  have hdec : decodableLcmd body = true := by
    simp only [printedAddrWB, Bool.and_eq_true] at h
    exact h.1.1.1.1.1
  obtain ⟨hl, hsh⟩ := shapesOf_spec _ body shs hF.shapes
  have hdecode : decodeLprog (encodeLfundefBytes body) =
      some (.op (leaFrame (-(Int.ofNat (Params.ofBody body).frame)))
        :: (shs.flatMap (blkOf body shs)
          ++ [.op (leaFrame (Int.ofNat (Params.ofBody body).frame)), .ret])) := by
    refine decodeLprog_encodeLfundefBytes hdec ?_
    rw [fundefLayout, fundefItems,
      show shapesD (Params.ofBody body) body = shs by
        rw [shapesD, show DecodeGen.shapesOf (Params.ofBody body) body = some shs from hF.shapes]; rfl]
    exact expectedFrom_fundef body shs hl.symm (targetsOK_ofW hF)
  rw [hd, Option.some.injEq] at hdecode
  subst hdecode
  have hcall := Haxc.callsTabB_iff.mp (Haxc.callsTabB_nil_of_printedAddrWB h)
  intro i tg hi
  have hm := List.mem_of_getElem? hi
  simp only [List.mem_cons, List.mem_append, List.mem_flatMap] at hm
  rcases hm with hm | ⟨sh, hsh', hm⟩ | hm
  · cases hm
  · obtain ⟨l, hl'⟩ := shape_of_mem_blkOf hm
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hsh'
    obtain ⟨ra, f, l', hx⟩ := lcall_of_shapeOf (hsh k (by omega) hk) hl'
    exact absurd (hcall _ (List.getElem_mem _) ra f l' hx) (by simp)
  · simp at hm

/-- **On a program without `call`, a halting run is a halting path without call.** -/
theorem haltsNoCall_of_halts {M : Machine AState} {prog : List RInstr}
    (hnc : ∀ (i tg : Nat), prog[i]? ≠ some (RInstr.call tg)) {pc : Nat} {s s' : AState}
    (h : Halts M prog pc s s') : HaltsNoCall M prog pc s s' := by
  suffices H : ∀ {pc : Nat} {s s' : AState}, HaltsC M prog pc s s' → HaltsNoCall M prog pc s s'
    from H h
  intro pc s s' h
  induction h with
  | ret hret => exact ⟨_, .refl _ _, hret⟩
  | go hs _ ih =>
    obtain ⟨pc'', hr, hret⟩ := ih
    exact ⟨pc'', .next hs hr, hret⟩
  | call hp _ _ _ _ => exact absurd hp (hnc _ _)

/-- **The decoded program of the back half without a table holds no `call`.** -/
theorem noCall_of_regionBack {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog}
    {bytes : List (BitVec 8)} (h : Haxc.regionBack σ a p = some (P, bytes))
    {prog : List RInstr} (hd : decodeLprog bytes = some prog) :
    ∀ (i tg : Nat), prog[i]? ≠ some (RInstr.call tg) := by
  obtain ⟨-, r0, r, b, cert, -, rfl, hb, hco, -⟩ := Haxc.regionBack_spec h
  rw [LprogBytes.encodeLfundefBytesChecked_eq hb] at hd
  have hpr : printedAddrWB b = true := by
    simp only [Haxc.regionCoB, Haxc.renImageB, Haxc.calleeImgBT_none, Bool.and_eq_true] at hco
    exact Haxc.regionPrintedB_of_regionImgB hco.2.2.1.1.1.1.2
  exact noCall_of_printedAddrWB hpr hd

/-- **The decoded program of `compileRegion` holds no `call`.** -/
theorem noCall_of_compileRegion {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog}
    {bytes : List (BitVec 8)} (h : Haxc.compileRegion σ a p = some (P, bytes))
    {prog : List RInstr} (hd : decodeLprog bytes = some prog) :
    ∀ (i tg : Nat), prog[i]? ≠ some (RInstr.call tg) := by
  obtain ⟨-, q, -, hb⟩ := Haxc.compileRegion_eq_some.mp h
  exact noCall_of_regionBack hb hd

/-- **Correctness of the back half without a table, by a halting path without call.** The
    statement of `regionBack_correct` with the halting run of the decoded bytes a path of steps
    to a return that passes no `call`. -/
theorem regionBack_correct_noCall {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect}
    {t : JasminTy} {p : NFProg jasminDialect Γ [t]} {P : Lprog}
    {bytes : List (BitVec 8)} (h : Haxc.regionBack σ a p = some (P, bytes))
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa V) (hreg : σ.Regions sa)
    (fuel : Nat) {v : Ctxt.Valuation (d := jasminDialect) [t]}
    (hv : p.denote fuel V = some v) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ HaltsNoCall aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (denVal t
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v))
      ∧ sa'.regs "%rsp" = sa.regs "%rsp" := by
  obtain ⟨prog, sa', hd, hh, hR, hsp, -⟩ := Haxc.regionBack_correct h sa V hV hreg fuel hv
  exact ⟨prog, sa', hd, haltsNoCall_of_halts (noCall_of_regionBack h hd) hh, hR, hsp⟩

/-- **The back half on a program without `call`, at a target fuel per segment, without a
    hypothesis on the decoded program.** `ruttF_compileRegion_callFree` with the absence of the
    instruction `call` from `noCall_of_compileRegion`. -/
theorem ruttF_compileRegion_callFree'
    (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (RE : (nfCallSig jasminDialect).Event → (kSig AState).Event → Prop)
    (RA : (e₁ : (nfCallSig jasminDialect).Event) → (e₂ : (kSig AState).Event) →
      (nfCallSig jasminDialect).Resp e₁ → (kSig AState).Resp e₂ → Prop)
    {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {P : Lprog}
    {bytes : List (BitVec 8)} (h : Haxc.compileRegion σ a p = some (P, bytes))
    (hcf : p.callFree = true) {prog : List RInstr} (hd : decodeLprog bytes = some prog)
    (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value)
    (sa : AState) (V : Ctxt.Valuation Γ) (hV : AbiValOf σ sa (NarrowWords.mapVal V))
    (hreg : σ.Regions sa) (fuel : Nat) :
    RuttF h₁ RE RA
      (NFProgCallTreeExt.OutRel fun (v : Ctxt.Valuation (d := jasminDialect) [t]) (s' : AState) =>
        σ.ResultOf sa s' (denVal (NarrowWords.wideTy t) (NarrowWords.transTy
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v))))
      (fun o => o = none) (NFProgCallTreeMont.mfTree fuel p V)
      (fun fuelT => targetTree aMachine prog sym rd fuelT 0 sa) :=
  ruttF_compileRegion_callFree h₁ RE RA h hcf hd (noCall_of_compileRegion h hd) sym rd sa V hV
    hreg fuel

end NoCall

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCallsBack
