/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeLive
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionBackend

/-!
# Call trees related to the runs of a body without its array self-moves

The pass `selfNop` of the region backend replaces each pair of a load of an array cell and the
store of it back into the same cell (`selfPairB`) by two copies of the index register onto
itself. Its correctness for halting runs is `lsemFuelMemF_selfNop_calls`, under a liveness
certificate of the identity renaming. A pair takes two steps on each side, and the state between
the two steps of the body is related to the state between the two copies only through the state
before the pair. The relation `NopRel` is the relation of the states at the positions that are
not the store of a pair (`NopNorm`), or a state after the load of a pair with the state after
the first copy (`NopMid`). Under it a step of the body is matched by a step of the rewritten
body (`nop_step`), and a call tree related to the states of the body by
`NFProgCallTreeExport.TSim` is related to the states of the rewritten body (`tsim_selfNop`).

## Main definitions

* `NopNorm`, `NopMid`, `NopRel`: the relations of the states of the body and of the body
  without its array self-moves.

## Main results

* `nop_step`: a step of the body is matched by a step of the rewritten body.
* `selfPairB_callShadow`, `selfNop_getElem?_callShadow`: a call is not the load of a pair, and
  the rewritten body keeps it.
* `tsim_selfNop`: a call tree related to a state of the body is related to every state of the
  rewritten body that `NopRel` relates to it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeSelfNop

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renOperand)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa callShadow retRes CallRes lpc_retRes)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (NextPc)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCall (steps_of_step_rel)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (arrArgsOf wordsOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim CallOut CallRet)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExportTransfer (TSim.transfer)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs (callResOf resLen callOut_retRes)

section SelfNop

variable {fn : String} {B : List LinstrRM} {k0 : Nat} {Lr : Nat → List String}
  {AN : List String}

/-- **The relation at a position that is not the store of a pair**: `RelF2` of the identity at
    the live register names and the arrays `AN`, from `k0` on, in the function `fn`. -/
def NopNorm (fn : String) (B : List LinstrRM) (k0 : Nat) (Lr : Nat → List String)
    (AN : List String) (s s' : LstateMF) : Prop :=
  RelF2 id (· ∈ Lr s.prog.base.lpc) (· ∈ AN) s s' ∧ k0 ≤ s.prog.base.lpc
    ∧ (decide (0 < s.prog.base.lpc) && selfPairB k0 Lr B (s.prog.base.lpc - 1)) = false
    ∧ s.prog.lfn = fn

/-- **The relation between the two steps of a pair**: the state after the load of a pair from a
    state `s₀` and the state after the first copy from a state related to `s₀`. -/
def NopMid (fn : String) (B : List LinstrRM) (k0 : Nat) (Lr : Nat → List String)
    (AN : List String) (u v : LstateMF) : Prop :=
  ∃ (s₀ s₀' : LstateMF) (t a z : String) (sc w n : Nat), NopNorm fn B k0 Lr AN s₀ s₀'
    ∧ selfPairB k0 Lr B s₀.prog.base.lpc = true
    ∧ B[s₀.prog.base.lpc]? = some (.Lopn [.reg t] "LOADIDX" [.arrIdx a z sc], .load w n)
    ∧ B[s₀.prog.base.lpc + 1]?
      = some (.Lopn [.reg a] "STOREIDX" [.arrIdx a z sc, .reg t], .store w n)
    ∧ z ≠ t ∧ (∀ x ∈ Lr (s₀.prog.base.lpc + 2), x ≠ t ∧ x ∈ Lr s₀.prog.base.lpc)
    ∧ evalInstrPMemF (singletonProgM fn B)
        (.Lopn [.reg t] "LOADIDX" [.arrIdx a z sc], .load w n) s₀ = some u
    ∧ evalInstrPMemF (singletonProgM fn (selfNop k0 Lr B))
        (.Lopn [.reg z] (withWidthTag 64 "MOV") [.reg z], .reg none) s₀' = some v

/-- The relation of the states of the body and of the body without its array self-moves. -/
def NopRel (fn : String) (B : List LinstrRM) (k0 : Nat) (Lr : Nat → List String)
    (AN : List String) (s s' : LstateMF) : Prop :=
  NopNorm fn B k0 Lr AN s s' ∨ NopMid fn B k0 Lr AN s s'

/-- The instruction fetched by a singleton program. -/
theorem fetch_singleton (X : List LinstrRM) (x : LstatePM) :
    findInstrMem (singletonProgM fn X) x = if x.lfn = fn then X[x.base.lpc]? else none := rfl

/-- **A step of the body is matched by a step of the body without its array self-moves.** -/
theorem nop_step {I : Isa} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao) {P₁ : LprogM}
    (hC : LiveCert id k0 (singletonProgM fn B) P₁ (fun k r => r ∈ Lr k) (fun _ r => r ∈ AN))
    (hK : LiveCalls id k0 (singletonProgM fn B) (fun k r => r ∈ Lr k) (fun _ r => r ∈ AN) aa ao)
    {s s' u : LstateMF} (hR : NopRel fn B k0 Lr AN s s')
    (h : I.lsemStepPMemF (singletonProgM fn B) s = some u) :
    ∃ u', I.lsemStepPMemF (singletonProgM fn (selfNop k0 Lr B)) s' = some u'
      ∧ NopRel fn B k0 Lr AN u u' := by
  have hcg : ∀ (i : LinstrRM) {x y : LstateMF}, I.step P₁ i x = some y →
      I.step (singletonProgM fn (selfNop k0 Lr B)) i x = some y :=
    fun i _ _ hxy => step_congr_calls hle hcl (P := P₁)
      (P' := singletonProgM fn (selfNop k0 Lr B))
      hC.lfn (fun l => (hC.lbl l).trans (findLabelMem_selfNop k0 Lr B l).symm) i hxy
  have hx86 : ∀ (P : LprogM) (i : LinstrRM) (x : LstateMF),
      LprogIsa.shadowCall? i.1 = none → I.step P i x = evalInstrPMemF P i x :=
    fun P i x hi => LprogIsa.Isa.CallLocal.step_eq I hle hcl P hi x
  unfold Isa.lsemStepPMemF at h ⊢
  rcases hR with ⟨hR, hk, hsec, hfn⟩ | ⟨s₀, s₀', t, a, z, sc, w, n, hN, hp, hi, hj, hzt, hdead,
      hld, hnop⟩
  · have hpc : s'.prog.base.lpc = s.prog.base.lpc := hR.1.1.1
    have hlfn : s'.prog.lfn = s.prog.lfn := hR.2.1
    rw [fetch_singleton, ite_eq_left hfn] at h
    cases hget : B[s.prog.base.lpc]? with
    | none => rw [hget] at h; cases h
    | some i =>
    rw [hget] at h
    replace h : I.step (singletonProgM fn B) i s = some u := h
    by_cases hp : selfPairB k0 Lr B s.prog.base.lpc = true
    · obtain ⟨t0, a, z, sc, w, m, hi, hj, hzt, hdead⟩ := selfPairB_spec hp
      obtain rfl : i = _ := Option.some.inj (hget.symm.trans hi)
      rw [hx86 _ _ _ (by simp only [LprogIsa.shadowCall?]; rfl)] at h
      obtain ⟨v1, hv1, -⟩ := selfNop_step (singletonProgM fn (selfNop k0 Lr B)) z s'
      have hg1 : findInstrMem (singletonProgM fn (selfNop k0 Lr B)) s'.prog
          = some (.Lopn [.reg z] (withWidthTag 64 "MOV") [.reg z], .reg none) := by
        rw [fetch_singleton, ite_eq_left (hlfn.trans hfn), hpc, selfNop, List.getElem?_mapIdx,
          hi]
        simp [hp, selfNopI]
      rw [hg1]
      refine ⟨v1, ?_, .inr ⟨s, s', t0, a, z, sc, w, m, ⟨hR, hk, hsec, hfn⟩, hp, hi, hj, hzt,
        hdead, h, hv1⟩⟩
      show I.step _ _ s' = some v1
      rw [hx86 _ _ _ (by simp only [LprogIsa.shadowCall?]; rfl)]
      exact hv1
    · have hp' : selfPairB k0 Lr B s.prog.base.lpc = false := Bool.eq_false_of_not_eq_true hp
      have hnx := step_next_calls hcl _ i s u h
      obtain ⟨u', hu', hRu, hku⟩ := step_live_calls hle hcl hC hK i hk hget hR h
      rw [JasminLsemFuseMulHi.renRM_id] at hu'
      replace hu' := hcg i hu'
      have hg : findInstrMem (singletonProgM fn (selfNop k0 Lr B)) s'.prog = some i := by
        rw [fetch_singleton, ite_eq_left (hlfn.trans hfn), hpc, selfNop, List.getElem?_mapIdx,
          hget]
        simp [hp', hsec]
      rw [hg]
      exact ⟨u', hu', .inl ⟨hRu, hku, selfPairB_next hnx.2 hp', hnx.1.trans hfn⟩⟩
  · obtain ⟨hR, hk, hsec, hfn⟩ := hN
    have hpc : s₀'.prog.base.lpc = s₀.prog.base.lpc := hR.1.1.1
    have hlfn : s₀'.prog.lfn = s₀.prog.lfn := hR.2.1
    have hnx := X86Backend.AllocCheck.LcmdCFG.evalInstrPMemF_next _ _ s₀ s hld
    have hspc : s.prog.base.lpc = s₀.prog.base.lpc + 1 := hnx.2
    rw [fetch_singleton, ite_eq_left (hnx.1.trans hfn), hspc, hj] at h
    replace h : I.step (singletonProgM fn B)
        (.Lopn [.reg a] "STOREIDX" [.arrIdx a z sc, .reg t], .store w n) s = some u := h
    rw [hx86 _ _ _ (by simp only [LprogIsa.shadowCall?]; rfl)] at h
    obtain ⟨hla, hlm, hlv, hpc2, hfn2, hzf2, hcf2, hof2⟩ := selfMove_steps t a z sc w n hzt hld h
    obtain ⟨v1, hv1, v1lv, v1la, v1lm, v1pc, v1fn, v1zf, v1cf, v1of⟩ :=
      selfNop_step (singletonProgM fn (selfNop k0 Lr B)) z s₀'
    have hvs : s' = v1 := Option.some.inj (hnop.symm.trans hv1)
    subst hvs
    obtain ⟨v2, hv2, v2lv, v2la, v2lm, v2pc, v2fn, v2zf, v2cf, v2of⟩ :=
      selfNop_step (singletonProgM fn (selfNop k0 Lr B)) z s'
    have hg2 : findInstrMem (singletonProgM fn (selfNop k0 Lr B)) s'.prog
        = some (.Lopn [.reg z] (withWidthTag 64 "MOV") [.reg z], .reg none) := by
      rw [fetch_singleton, ite_eq_left (v1fn.trans (hlfn.trans hfn)), v1pc, hpc, selfNop,
        List.getElem?_mapIdx, hj]
      simp [hp, selfNopI]
    rw [hg2]
    refine ⟨v2, by
        show I.step _ _ s' = some v2
        rw [hx86 _ _ _ (by simp only [LprogIsa.shadowCall?]; rfl)]
        exact hv2,
      .inl ⟨?_, ?_, ?_, ?_⟩⟩
    · refine ⟨⟨⟨?_, fun r hr => ?_⟩, fun r hr => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · show v2.prog.base.lpc = u.prog.base.lpc
        rw [v2pc, v1pc, hpc, hpc2]
      · rw [hpc2] at hr
        obtain ⟨hne, hin⟩ := hdead r hr
        rw [hlv r hne, v2lv, v1lv]
        exact hR.1.1.2 r hin
      · rw [hla, v2la, v1la]
        exact hR.1.2.1 r hr
      · rw [hlm, v2lm, v1lm]
        exact hR.1.2.2
      · rw [hfn2, v2fn, v1fn]
        exact hlfn
      · rw [hzf2, v2zf, v1zf]
        exact hR.2.2.1
      · rw [hcf2, v2cf, v1cf]
        exact hR.2.2.2.1
      · rw [hof2, v2of, v1of]
        exact hR.2.2.2.2
    · rw [hpc2]
      omega
    · rw [hpc2, show s₀.prog.base.lpc + 2 - 1 = s₀.prog.base.lpc + 1 from rfl,
        Bool.and_eq_false_iff]
      right
      by_contra hc
      obtain ⟨t1, a1, z1, sc1, w1, m1, hi1, -⟩ :=
        selfPairB_spec (Bool.eq_true_of_not_eq_false hc)
      rw [hj] at hi1
      cases congrArg Prod.snd (Option.some.inj hi1)
    · exact hfn2.trans hfn

/-- A shadow instruction of a call is not the load of a pair. -/
theorem selfPairB_callShadow {k : Nat} {dst f : String} {srcs : List LOperand} {tag : MemTag}
    (hb : B[k]? = some (callShadow dst f srcs, tag)) : selfPairB k0 Lr B k = false := by
  by_contra hc
  obtain ⟨t, a, z, sc, w, n, hi, -⟩ := selfPairB_spec (Bool.eq_true_of_not_eq_false hc)
  rw [hb] at hi
  have h1 := congrArg (fun i : LinstrRM => LprogIsa.shadowCall? i.1) (Option.some.inj hi)
  simp only [LprogIsa.shadowCall?_callShadow] at h1
  exact absurd h1 (by simp only [LprogIsa.shadowCall?]; exact nofun)

/-- The body without its array self-moves keeps a shadow instruction of a call at a position
    that is not the store of a pair. -/
theorem selfNop_getElem?_callShadow {k : Nat} {dst f : String} {srcs : List LOperand}
    {tag : MemTag} (hb : B[k]? = some (callShadow dst f srcs, tag))
    (hsec : (decide (0 < k) && selfPairB k0 Lr B (k - 1)) = false) :
    (selfNop k0 Lr B)[k]? = some (callShadow dst f srcs, tag) := by
  rw [selfNop, List.getElem?_mapIdx, hb]
  simp [selfPairB_callShadow hb, hsec]

/-- **A call tree related to the states of the body is related to the states of the body
    without its array self-moves.** Under a liveness certificate of the identity renaming from
    `k0` on with the call condition `LiveCalls` at `aa` and `ao`, let every event at a call site
    of the body have the array positions `aa` and the result length `ao` of its symbol. A tree
    related by `TSim` to `s` at the call sites and the states after the calls of the body is
    related to every state `s'` that `NopRel` relates to `s`, at the call sites and the states
    after the calls of `selfNop k0 Lr B`, at every end condition that `NopRel` carries `Post`
    to. -/
theorem tsim_selfNop {I : Isa} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hle : x86Isa.StepLe I) (hcl : I.CallLocal x86Isa aa ao) {P₁ : LprogM}
    (hC : LiveCert id k0 (singletonProgM fn B) P₁ (fun k r => r ∈ Lr k) (fun _ r => r ∈ AN))
    (hK : LiveCalls id k0 (singletonProgM fn B) (fun k r => r ∈ Lr k) (fun _ r => r ∈ AN) aa ao)
    (hev : ∀ e u, NFProgCallTreeExport.CallSite (singletonProgM fn B) e u →
      arrArgsOf e.argTys = aa e.name ∧ resLen e.resTys = ao e.name)
    {α : Type} {Post Post' : α → LstateMF → Prop}
    (hpost : ∀ x m m', NopRel fn B k0 Lr AN m m' → Post x m → Post' x m')
    {t : CallTree (nfCallSig jasminDialect) (Option α)} {s s' : LstateMF}
    (hR : NopRel fn B k0 Lr AN s s')
    (h : TSim I (singletonProgM fn B) (NFProgCallTreeExport.CallSite (singletonProgM fn B))
      (CallRet (singletonProgM fn B)) t s Post) :
    TSim I (singletonProgM fn (selfNop k0 Lr B))
      (NFProgCallTreeExport.CallSite (singletonProgM fn (selfNop k0 Lr B)))
      (CallRet (singletonProgM fn (selfNop k0 Lr B))) t s' Post' := by
  -- a call site is a state of `NopNorm`
  have hnorm : ∀ {e u u'}, NopRel fn B k0 Lr AN u u' →
      NFProgCallTreeExport.CallSite (singletonProgM fn B) e u → NopNorm fn B k0 Lr AN u u' := by
    rintro e u u' (hN | ⟨s₀, s₀', t, a, z, sc, w, n, -, -, -, hj, -, -, hld, -⟩)
      ⟨dst, srcs, tag, k, hat, hfk, -, -⟩
    · exact hN
    · exfalso
      have hnx := X86Backend.AllocCheck.LcmdCFG.evalInstrPMemF_next _ _ s₀ u hld
      have hk : k = s₀.prog.base.lpc + 1 := hat.2.symm.trans hnx.2
      have hfk' : B[k]? = some (callShadow dst e.name srcs, tag) := hfk
      rw [hk, hj] at hfk'
      have h1 := congrArg (fun i : LinstrRM => LprogIsa.shadowCall? i.1) (Option.some.inj hfk')
      simp only [LprogIsa.shadowCall?_callShadow] at h1
      exact absurd h1.symm (by simp only [LprogIsa.shadowCall?]; exact nofun)
  refine TSim.transfer (NopRel fn B k0 Lr AN) ?_ ?_ ?_ hpost hR h
  · intro n s t s' hs hR
    obtain ⟨t', ht', hRt⟩ := steps_of_step_rel I I (NopRel fn B k0 Lr AN)
      (fun s s' u hR hu => nop_step hle hcl hC hK hR hu) n s s' t hR hs
    exact ⟨n, t', ht', hRt⟩
  · intro e u u' hR hsi
    obtain ⟨⟨⟨hRn, hRa, hRm⟩, hfn', -⟩, hk0, hsec, hfn⟩ := hnorm hR hsi
    obtain ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩ := hsi
    obtain ⟨haa, -⟩ := hev e u ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩
    have hpc' : u'.prog.base.lpc = u.prog.base.lpc := hRn.1
    rw [hat.2] at hRn hk0 hsec
    have hu := hC.uses _ _ hk0 hfk
    obtain ⟨hcA, -⟩ := hK _ _ dst e.name srcs hk0 hfk rfl
    have hid : srcs.map (renOperand id) = srcs := by
      have : renOperand id = fun o => o := by
        funext o
        cases o <;> rfl
      rw [this, List.map_id']
    have hrd' := argsRead_ren (σ := id) ⟨hRn, hRa, hRm⟩ 0 srcs
      (fun o ho n hn => hu n (List.mem_flatMap.mpr ⟨o, ho, hn⟩))
      (fun m n A h1 h2 => hcA m n A (by simpa using h1) h2)
    rw [hid] at hrd'
    refine ⟨dst, srcs, tag, k, ⟨hfn'.trans hat.1, by rw [hpc', hat.2]⟩,
      selfNop_getElem?_callShadow (B := B) hfk hsec, hlen, ?_⟩
    rw [haa, hrd', ← haa]
    exact hrd
  · intro e u u' a v' hR hsi hq
    obtain ⟨⟨⟨hRn, hRa, hRm⟩, hfn', hz, hcf, hof⟩, hk0, hsec, hfn⟩ := hnorm hR hsi
    obtain ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩ := hsi
    obtain ⟨-, hao⟩ := hev e u ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩
    have hpc' : u'.prog.base.lpc = u.prog.base.lpc := hRn.1
    rw [hat.2] at hRn hk0 hsec
    obtain ⟨dst', srcs', tag', k', res, hat', hf', rfl, hout⟩ := hq
    have hk' : k' = k := by rw [← hat'.2, hpc', hat.2]
    subst hk'
    have hfk' : (selfNop k0 Lr B)[k']? = some (callShadow dst' e.name srcs', tag') := hf'
    rw [selfNop_getElem?_callShadow (B := B) hfk hsec] at hfk'
    simp only [Option.some.injEq, Prod.mk.injEq, callShadow, LinstrR.Lopn.injEq,
      List.cons.injEq, LOperand.reg.injEq, and_true] at hfk'
    obtain ⟨⟨rfl, -⟩, -⟩ := hfk'
    obtain ⟨rfl, hxlen, hback⟩ := callOut_retRes hout
    have hKr := hC.fallR _ _ hk0 hfk
    have hKa := hC.fallA _ _ hk0 hfk
    obtain ⟨-, hcO⟩ := hK _ _ dst e.name srcs hk0 hfk rfl
    rw [regDefs_callShadow] at hKr
    rw [arrDefs_callShadow] at hKa
    refine ⟨retRes dst (callResOf e.resTys res) u,
      ⟨dst, srcs, tag, k', res, hat, hfk, rfl, hback dst u⟩, .inl ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [lpc_retRes, hat.2]
      cases hx : callResOf e.resTys res with
      | word r =>
          exact ⟨⟨relN_setReg_keeps hRn hKr r, fun a ha => hRa a (hKa.sub a ha), hRm⟩,
            (LprogIsa.lfn_retRes _ _ _).trans
              (hfn'.trans (LprogIsa.lfn_retRes _ _ _).symm), hz, hcf, hof⟩
      | arr a =>
          rw [hx] at hxlen
          obtain ⟨hd, hKa'⟩ := hcO _ (hao.symm.trans hxlen.symm)
          have hsub : ∀ r, r ∈ Lr (k' + 1) → r ∈ Lr k' := fun r hr => by
            rcases hKr r hr with h1 | h1
            · obtain rfl : dst = r := by simpa using h1
              exact hd
            · exact h1.1
          exact ⟨RelM2.setArr_keeps ⟨hRn, hRa, hRm⟩ hKa' hsub a,
            (LprogIsa.lfn_retRes _ _ _).trans
              (hfn'.trans (LprogIsa.lfn_retRes _ _ _).symm), hz, hcf, hof⟩
    · rw [lpc_retRes, hat.2]
      omega
    · rw [lpc_retRes, hat.2, show k' + 1 - 1 = k' from rfl, selfPairB_callShadow (B := B) hfk,
        Bool.and_false]
    · exact (LprogIsa.lfn_retRes _ _ _).trans hfn

end SelfNop

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeSelfNop
