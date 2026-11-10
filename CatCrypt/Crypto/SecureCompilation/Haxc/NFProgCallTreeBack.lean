/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain
public import CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree

/-!
# The region back half at the level of call trees, on programs without `call`

The back half `compileRegion` compiles the output of `extChainCore` (the narrow-word stages
`narrowPrep`, then `regionBack`) to bytes that decode to a calling body. Its correctness at the
level of denotations on a program without `call` is `compileRegion_correct`: a run of the source
to a value is a halting run of the decoded program to a state from which the layout reads back
the widened value. This module ports it to the call trees: the tree `mfTree` of a program
without `call` is a leaf, and the target tree `targetTree` of a decoded program without the
instruction `call` is the leaf of its fuelled run. Composed after `ruttS_extChainCore`, the
source call tree of the program of `nfDialect` is related to the target tree of the decoded
bytes.

The decoded program is assumed to hold no instruction `call`; on a calling body the back half
relates source call events to the target call events of `targetTree`, which this module does
not cover.

## Main results

* `targetTree_of_run`: on a program without `call`, a fuelled run is a leaf of the target tree
  at that fuel.
* `run_of_halts_noCall`: on a program without `call`, a halting run is a fuelled run.
* `mfTree_eq_ret_denote`: the tree `mfTree` of a program without `call` is the leaf of its
  denotation.
* `ruttS_compileRegion_callFree`: the stage lemma of `compileRegion` on a program without
  `call`, from `mfTree` to the target tree.
* `ruttS_extChainCore_compileRegion_callFree`: the steps of `extChainCore` and the back half,
  from the call tree of the source program of `nfDialect` to the target tree of the bytes.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeBack

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringExtend (transArgs)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.SecureCompilation.VIR.NFProgCatToJasmin (catToJasmin)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOpt
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeChain
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree (targetTree)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkContract (RuttS)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify (montEnv)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax.ImpToNF (tableOf)
open Ctxt (Var Valuation)

/-! ## The target tree of a program without `call` -/

section Target

variable {σ : Type}

/-- **On a program without `call`, a fuelled run is a leaf of the target tree** at that fuel,
    at every symbol map and reader of arguments. -/
theorem targetTree_of_run {M : Machine σ} {prog : List RInstr} (sym : Nat → String)
    (rd : String → σ → List _root_.Hax.Value)
    (hnc : ∀ (i t : Nat), prog[i]? ≠ some (RInstr.call t)) :
    ∀ {fuel pc : Nat} {s s' : σ}, run M prog fuel pc s = some s' →
      targetTree M prog sym rd fuel pc s = .ret (some s') := by
  intro fuel
  induction fuel with
  | zero => intro pc s s' h; simp [run] at h
  | succ fuel ih =>
    intro pc s s' h
    simp only [run] at h
    simp only [targetTree]
    split
    · rename_i t ht
      exact absurd ht (hnc _ _)
    · split at h
      · cases h
      · rename_i s₁ hs
        cases h
        simp only [hs]
      · rename_i pc' s₁ hs
        simp only [hs]
        exact ih h

/-- **On a program without `call`, a halting run is a fuelled run.** -/
theorem run_of_halts_noCall {M : Machine σ} {prog : List RInstr}
    (hnc : ∀ (i t : Nat), prog[i]? ≠ some (RInstr.call t)) {pc : Nat} {s s' : σ}
    (h : Halts M prog pc s s') : ∃ fuel, run M prog fuel pc s = some s' := by
  suffices H : ∀ {pc : Nat} {s s' : σ}, HaltsC M prog pc s s' → HaltsNoCall M prog pc s s' from
    run_of_haltsNoCall (H h)
  intro pc s s' h
  induction h with
  | ret hret => exact ⟨_, .refl _ _, hret⟩
  | go hs _ ih =>
    obtain ⟨pc'', hr, hret⟩ := ih
    exact ⟨pc'', .next hs hr, hret⟩
  | call hp _ _ _ _ => exact absurd hp (hnc _ _)

end Target

/-! ## The back half on a program without `call` -/

section Back

open NarrowWords (wideTy)

/-- **The tree `mfTree` of a program without `call` is the leaf of its denotation.** -/
theorem mfTree_eq_ret_denote (fuel : Nat) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : p.callFree = true) (V : Valuation Γ) :
    mfTree fuel p V = .ret (p.denote fuel V) := by
  obtain ⟨o, ho⟩ := treeAt_ret_of_callFree mfEnv fuel p hp V
  have hi := interp_mfTree CallEnv.empty fuel p V
  rw [mfTree, ho] at hi ⊢
  change o = p.denoteAt (montEnv (fieldEnv CallEnv.empty)) fuel V at hi
  rw [hi, NFProg.denoteAt_of_callFree p hp _ CallEnv.empty]
  rfl

/-- **The stage lemma of `compileRegion` on a program without `call` at the tree level.** For a
    result `(P, bytes)` of `compileRegion σ a p` on a program `p` without `call`, whose bytes
    decode to a program `prog` without the instruction `call`: from every entry state `sa`
    satisfying `σ.Regions` at which `σ` reads the widened valuation `mapVal V`, at every fuel,
    some target fuel relates the tree `mfTree` of `p` at `V` to the target tree of `prog` from
    `sa`, at every handler, event and answer relation, symbol map and reader of arguments: a
    source result is matched by a return state from which `σ` reads back its widened value. -/
theorem ruttS_compileRegion_callFree
    (h₁ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (RE : (nfCallSig jasminDialect).Event → (TargetCallTree.kSig AState).Event → Prop)
    (RA : (e₁ : (nfCallSig jasminDialect).Event) → (e₂ : (TargetCallTree.kSig AState).Event) →
      (nfCallSig jasminDialect).Resp e₁ → (TargetCallTree.kSig AState).Resp e₂ → Prop)
    {σ : AbiLayout} {a : AbiNames} {Γ : Ctxt jasminDialect} {t : JasminTy}
    {p : NFProg jasminDialect Γ [t]} {P : VIR.JasminLprogExport.Lprog}
    {bytes : List (BitVec 8)} (h : compileRegion σ a p = some (P, bytes))
    (hcf : p.callFree = true) {prog : List RInstr} (hd : decodeLprog bytes = some prog)
    (hnc : ∀ (i tg : Nat), prog[i]? ≠ some (RInstr.call tg))
    (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value)
    (sa : AState) (V : Valuation Γ) (hV : AbiValOf σ sa (NarrowWords.mapVal V))
    (hreg : σ.Regions sa) (fuel : Nat) :
    ∃ fuelT, RuttS h₁ RE RA
      (OutRel fun (v : Valuation (d := jasminDialect) [t]) (s' : AState) =>
        σ.ResultOf sa s' (denVal (wideTy t) (NarrowWords.transTy
          (Ctxt.Var.lookup (d := jasminDialect) (Γ := [t]) (t := t) .here v))))
      (fun o => o = none) (mfTree fuel p V) (targetTree aMachine prog sym rd fuelT 0 sa) := by
  rw [mfTree_eq_ret_denote fuel p hcf V]
  cases hv : p.denote fuel V with
  | none => exact ⟨0, .fail rfl⟩
  | some v =>
    obtain ⟨prog', sa', hd', hh, hR, -⟩ := compileRegion_correct h sa V hV hreg fuel hv
    rw [hd] at hd'
    cases hd'
    obtain ⟨fuelT, hrun⟩ := run_of_halts_noCall hnc hh
    refine ⟨fuelT, ?_⟩
    rw [targetTree_of_run sym rd hnc hrun]
    exact .ret fun x hx => by cases hx; exact ⟨sa', rfl, hR⟩

end Back

/-! ## The steps of `extChainCore` and the back half -/

section Compose

open NarrowWords (wideTy)

/-- **The steps of `extChainCore` and the back half at the tree level, on a program without
    `call`.** Under the hypotheses of `ruttS_extChainCore`, for a program `p` that the chain
    turns into `q`, a program without `call` that `compileRegion σ a` compiles to bytes
    decoding to a program `prog` without the instruction `call`, and an entry state `sa`
    satisfying `σ.Regions` at which `σ` reads the transported and widened valuation: at every
    fuel at least the source fuel `tf`, some target fuel relates the tree of `p` at `linkReader`
    and the handler of the leaf table of `bi` to the target tree of `prog` from `sa`, a source
    result read back from the return state through `VRelL`, the transport and the widening. -/
theorem ruttS_extChainCore_compileRegion_callFree
    {bi : _root_.Hax.Builtins} (hbi : SubTable bi)
    (D : List ExtDecl) (tE : TreeCallEnv leafSig nfDialect)
    (h₂ : ∀ e : (nfCallSig catCryptDialect).Event, (nfCallSig catCryptDialect).Resp e)
    (h₃ : ∀ e : (nfCallSig jasminDialect).Event, (nfCallSig jasminDialect).Resp e)
    (hh₂ : ∀ e₁ e₂, ExtRE e₁ e₂ → ExtRA e₁ e₂ (leafHandler (tableOf bi) e₁) (h₂ e₂))
    (hh₃ : ∀ e₁ e₂, MapRE catToJasmin (fun x => ctTransTy x) e₁ e₂ →
      MapRA catToJasmin (fun x => ctTransTy x) e₁ e₂ (h₂ e₁) (h₃ e₂))
    (hinner : ∀ (f : String) (as rs : List JasminTy) (x : Valuation (d := jasminDialect) as),
      innerHead f = true →
        h₃ ⟨f, as, rs, x⟩ = (montEnv (fieldEnv CallEnv.empty)).call f as rs x)
    (RE : (nfCallSig jasminDialect).Event → (TargetCallTree.kSig AState).Event → Prop)
    (RA : (e₁ : (nfCallSig jasminDialect).Event) → (e₂ : (TargetCallTree.kSig AState).Event) →
      (nfCallSig jasminDialect).Resp e₁ → (TargetCallTree.kSig AState).Resp e₂ → Prop)
    {Γ : Ctxt nfDialect} {t : NfTy} {p : NFProg nfDialect Γ [t]}
    {q : NFProg jasminDialect (mapCtx (Γ.map catTy)) [mapTy (catTy t)]}
    (hq : (extChainCore D Γ t).run p = some q) (hcf : q.callFree = true)
    {σ : AbiLayout} {a : AbiNames} {P : VIR.JasminLprogExport.Lprog}
    {bytes : List (BitVec 8)} (h : compileRegion σ a q = some (P, bytes))
    {prog : List RInstr} (hd : decodeLprog bytes = some prog)
    (hnc : ∀ (i tg : Nat), prog[i]? ≠ some (RInstr.call tg))
    (sym : Nat → String) (rd : String → AState → List _root_.Hax.Value)
    (V : Valuation Γ) (hin : ∀ (s : NfTy) (v : Var Γ s), InRange s (v.lookup V))
    (sa : AState) (hV : AbiValOf σ sa (NarrowWords.mapVal (ctMapValD (mapVal V))))
    (hreg : σ.Regions sa) (tf fuel : Nat) (hle : tf ≤ fuel) :
    ∃ fuelT, RuttS (leafHandler (tableOf bi))
      (CompRE (CompRE ExtRE (MapRE catToJasmin fun x => ctTransTy x)) RE)
      (CompRA (CompRE ExtRE (MapRE catToJasmin fun x => ctTransTy x)) RE
        (CompRA ExtRE (MapRE catToJasmin fun x => ctTransTy x) ExtRA
          (MapRA catToJasmin fun x => ctTransTy x)) RA)
      (Relation.Comp
        (Relation.Comp (OutRel (VRelL [t]))
          (OutRel fun x y => y = transArgs catToJasmin.mapTy (fun x => ctTransTy x) x))
        (OutRel fun (v : Valuation (d := jasminDialect) [mapTy (catTy t)]) (s' : AState) =>
          σ.ResultOf sa s' (denVal (wideTy (mapTy (catTy t))) (NarrowWords.transTy
            (Ctxt.Var.lookup (d := jasminDialect) (Γ := [mapTy (catTy t)])
              (t := mapTy (catTy t)) .here v)))))
      (fun o => o = none)
      (treeAt linkReader tE tf p V) (targetTree aMachine prog sym rd fuelT 0 sa) := by
  obtain ⟨fuelT, hT⟩ := ruttS_compileRegion_callFree h₃ RE RA h hcf hd hnc sym rd sa _ hV hreg
    fuel
  refine ⟨fuelT, RuttS.trans (h₁ := h₃) ?_ ?_
    (ruttS_extChainCore hbi D tE h₂ h₃ hh₂ hh₃ hinner hq V hin tf fuel hle) hT⟩
  · rintro e₀ e ⟨e₁, he₁, he₂⟩ e₁' he₁' he₂'
    exact ⟨h₂ e₁', hh₂ _ _ he₁', hh₃ _ _ he₂'⟩
  · rintro r₀ r₁ ⟨r, h₁, h₂⟩ rfl
    have : r = none := by
      cases r with
      | none => rfl
      | some a => obtain ⟨b, hb, -⟩ := h₂ a rfl; cases hb
    subst this
    cases r₀ with
    | none => rfl
    | some a => obtain ⟨b, hb, -⟩ := h₁ a rfl; cases hb

end Compose

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeBack
