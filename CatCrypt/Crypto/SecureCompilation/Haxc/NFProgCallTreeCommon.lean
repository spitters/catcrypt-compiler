/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs

/-!
# Call trees related to the runs of a body rewritten onto the common names of its callees

The rewriting `LprogCallCut.commonCallsT?` replaces each shadow instruction of a call of a
symbol of a table by its form on the common names of the callee (`LprogCallCut.commonSeq`):
the copies of the word operands into the argument names, the shadow instruction on those names,
and the copy of a word result from the result name. Its correctness for runs with procedure
summaries is `LprogCallCut.steps_commonT`, under the relation `LprogCallCut.OffRel` of states
that agree off the common names, at the position map `expPosT`. With calls as events, a step of
the x86 flag machine is not a call, and is matched by one step of the rewritten body
(`common_step_x86`); a call site of the body is matched by the copies and a call site of the
rewritten body, and the state after the call of the rewritten body by the copy of the result
and a state related to the state after the call of the body (`tsim_common`).

A transfer of `NFProgCallTreeExport.TSim` that allows steps of the second program before a call
site and after a call (`TSim.transfer'`) carries the relation through such a rewriting.

## Main results

* `TSim.transfer'`: a simulation of runs that reaches a call site of the second program by
  steps from a state related to a call site, and a related state by steps from each state after
  the call, carries `TSim`.
* `common_step_x86`: a step of the x86 flag machine on a body is a step on its rewriting onto
  common names.
* `common_site`: a call site of the body is matched by the copies and a call site of the
  rewriting, and each state after its call by the copy of the result and a related state.
* `tsim_common`: a call tree related to a state of the body is related to every state of the
  rewriting that `OffRel` relates to it.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCommon

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs (evalInstrPMemF_shadowCall)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_step)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim)

/-! ## Transfer with steps around the calls -/

/-- **A simulation with steps around the calls carries the relation of call trees and states.**
    Let `R` carry runs of `I` on `P` to runs of `I'` on `P'`; from a state related to a call
    site of `P`, let steps of `P'` reach a call site of `P'`, from which every state after the
    call at an answer is reached from a state after the call of `P` at that answer, and reaches
    by steps a state related to it. A tree related by `TSim` to `s` at `Post` is related to every
    state that `R` relates to `s`, at every end condition that `R` carries `Post` to. -/
theorem TSim.transfer' {E : EventSig} {I I' : Isa} {P P' : LprogM}
    {Site Site' : E.Event → LstateMF → Prop}
    {Q Q' : (e : E.Event) → LstateMF → E.Resp e → LstateMF → Prop} {α : Type}
    {Post Post' : α → LstateMF → Prop} (R : LstateMF → LstateMF → Prop)
    (hst : ∀ (n : Nat) (s t s' : LstateMF), Steps I P n s t → R s s' →
      ∃ k' t', Steps I' P' k' s' t' ∧ R t t')
    (hsite : ∀ e u u', R u u' → Site e u → ∃ k u'', Steps I' P' k u' u'' ∧ Site' e u''
      ∧ ∀ a v', Q' e u'' a v' → ∃ v, Q e u a v ∧ ∃ k' v'', Steps I' P' k' v' v'' ∧ R v v'')
    (hpost : ∀ x m m', R m m' → Post x m → Post' x m') :
    ∀ {t : CallTree E (Option α)} {s s' : LstateMF}, R s s' →
      TSim I P Site Q t s Post → TSim I' P' Site' Q' t s' Post'
  | .ret none, _, _, _, _ => trivial
  | .ret (some x), s, s', hR, ⟨k, m, hs, hp⟩ => by
      obtain ⟨k', m', hs', hRm⟩ := hst k s m s' hs hR
      exact ⟨k', m', hs', hpost x m m' hRm hp⟩
  | .vis e c, s, s', hR, ⟨k, u, hs, hsi, hc⟩ => by
      obtain ⟨k', u', hs', hRu⟩ := hst k s u s' hs hR
      obtain ⟨k₁, u'', hs₁, hsi', hans⟩ := hsite e u u' hRu hsi
      refine ⟨k' + k₁, u'', hs'.trans hs₁, hsi', fun a v' hq' => ?_⟩
      obtain ⟨v, hq, k₂, v'', hs₂, hRv⟩ := hans a v' hq'
      exact NFProgCallTreeExport.TSim.steps hs₂
        (TSim.transfer' R hst hsite hpost hRv (hc a v hq))

/-! ## A step of the x86 flag machine -/

/-- **A step of the x86 flag machine on a body is a step on its rewriting onto common names.**
    Under `CommonSimT` at the names `N`, from states related by `OffRel N` along `expPosT`, a
    step of `x86Isa` on `B`, which is not a call, is matched by a step of `x86Isa` on the
    rewriting `B'` to related states. -/
theorem common_step_x86 {T : ProcTable}
    {tab : String → Option (CallShape × List String × String)}
    {N : List String} {fn : String} {B B' : List LinstrRM} (hB : commonCallsT? tab B = some B')
    (hc : CommonSimT T tab N B) {s u s' : LstateMF}
    (h : x86Isa.lsemStepPMemF (singletonProgM fn B) s = some u)
    (hr : OffRel N (expPosT tab B) s s') :
    ∃ u', x86Isa.lsemStepPMemF (singletonProgM fn B') s' = some u' ∧
      OffRel N (expPosT tab B) u u' := by
  obtain ⟨L', hL, rfl⟩ := hr
  unfold Isa.lsemStepPMemF at h
  cases hfi : findInstrMem (singletonProgM fn B) s.prog with
  | none => rw [hfi] at h; cases h
  | some i =>
    rw [hfi] at h
    replace h : x86Isa.step (singletonProgM fn B) i s = some u := h
    unfold findInstrMem at hfi
    split at hfi
    · rename_i hfn
      replace hfi : B[s.prog.base.reg.lpc]? = some i := hfi
      have hmem : i ∈ B := List.mem_of_getElem? hfi
      obtain ⟨is, pre, post, his, hB', hpre⟩ := commonCallsT?_split hB hfi
      have hsucc := expPosT_succ tab hfi
      rw [← hpre] at hsucc ⊢
      have hat : atPc (singletonProgM fn B') pre.length (setRL L' pre.length s) := ⟨hfn, rfl⟩
      cases hs : shadowCall? i.fst with
      | none =>
        have his' := commonCallT?_none his hs
        subst his'
        have hget : (singletonProgM fn B').body[pre.length]? = some i := by
          change B'[pre.length]? = some i
          rw [hB']
          simp
        have hlen : expLenT tab i = 1 := by simp [expLenT, hs]
        rw [hlen] at hsucc
        suffices hsuff : ∃ u', x86Isa.step (singletonProgM fn B') i (setRL L' pre.length s)
            = some u' ∧ OffRel N (expPosT tab B) u u' by
          obtain ⟨u', hu', hrel⟩ := hsuff
          exact ⟨u', by rw [lsemStepPMemF_of_atPc _ hat hget]; exact hu', hrel⟩
        cases hctl : isCtl i.fst with
        | false =>
          obtain ⟨L'', hL'', hstep⟩ := offCongr_step (hc.congr i hmem hctl hs) hctl _
            (singletonProgM fn B') pre.length hL h
          have hpc : u.prog.base.reg.lpc = s.prog.base.reg.lpc + 1 := by
            have hu := x86Isa_pcFree.lpc_succ _ hctl h
            rw [hu]
            rfl
          exact ⟨_, hstep, L'', hL'', by rw [hpc, hsucc]⟩
        | true =>
          rw [x86Isa.step_ctl _ i s hctl] at h
          rw [x86Isa.step_ctl _ i _ hctl]
          obtain ⟨ir, tag⟩ := i
          cases ir with
          | Llabel k l =>
              simp only [ctlStep, Option.some.injEq] at h
              subst h
              refine ⟨_, rfl, L', hL, ?_⟩
              change setRL L' (pre.length + 1) s
                = setRL L' (expPosT tab B (s.prog.base.reg.lpc + 1)) s
              rw [hsucc]
          | Lcond c l =>
              simp only [ctlStep] at h ⊢
              rw [hc.cond c l tag hmem s L' _ hL]
              split at h
              · rw [ite_eq_left (by assumption)]
                unfold evalJumpMem at h ⊢
                cases hl : findLabelMem l (singletonProgM fn B).body with
                | none => rw [hl] at h; cases h
                | some q =>
                    rw [hl] at h
                    rw [show findLabelMem l (singletonProgM fn B').body
                      = some (expPosT tab B q) from findLabelMem_commonCallsT? l hB hl]
                    simp only [Option.map_some, Option.some.injEq] at h
                    subst h
                    refine ⟨_, rfl, L', hL, ?_⟩
                    change setRL L' (expPosT tab B q + 1) s = setRL L' (expPosT tab B (q + 1)) s
                    rw [expPosT_label_succ tab (B := B) hl]
              · rw [ite_eq_right (by assumption)]
                simp only [Option.some.injEq] at h
                subst h
                refine ⟨_, rfl, L', hL, ?_⟩
                change setRL L' (pre.length + 1) s
                  = setRL L' (expPosT tab B (s.prog.base.reg.lpc + 1)) s
                rw [hsucc]
          | Lgoto tgt =>
              obtain ⟨g, l⟩ := tgt
              simp only [ctlStep] at h ⊢
              split at h
              · rw [ite_eq_left (by assumption)]
                unfold evalJumpMem at h ⊢
                cases hl : findLabelMem l (singletonProgM fn B).body with
                | none => rw [hl] at h; cases h
                | some q =>
                    rw [hl] at h
                    rw [show findLabelMem l (singletonProgM fn B').body
                      = some (expPosT tab B q) from findLabelMem_commonCallsT? l hB hl]
                    simp only [Option.map_some, Option.some.injEq] at h
                    subst h
                    refine ⟨_, rfl, L', hL, ?_⟩
                    change setRL L' (expPosT tab B q + 1) s = setRL L' (expPosT tab B (q + 1)) s
                    rw [expPosT_label_succ tab (B := B) hl]
              · cases h
          | _ => simp [isCtl] at hctl
      | some q =>
        rw [x86Isa_step, evalInstrPMemF_shadowCall _ i s (by rw [hs]; simp)] at h
        cases h
    · cases hfi

/-! ## The form of a call on common names -/

section Site

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (evalOperandN LstateN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (arrArgsOf wordsOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (CallOut CallRet)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs (callResOf resLen callOut_retRes)

/-- The step of a copy on the x86 flag machine. -/
theorem x86_step_movI (P : LprogM) (dst src : String) (s : LstateMF) :
    x86Isa.step P (LprogCallCut.movI dst src) s = some (movS dst src s) := by
  rw [x86Isa_step]
  exact JasminLsemExportRewrites.evalInstrPMemF_movReg P dst src (.reg none) s

/-- The copies run on the x86 flag machine. -/
theorem runI_moves_x86 (P : LprogM) :
    ∀ (ps : List (String × String)) (s : LstateMF),
      runI x86Isa P (ps.map fun p => LprogCallCut.movI p.1 p.2) s = some (movesF ps s)
  | [], _ => rfl
  | p :: ps, s => by
      simp only [List.map_cons, runI, x86_step_movI, Option.bind_some, movesF]
      exact runI_moves_x86 P ps _

/-- **The summary answering a fixed result** on `n` arguments with the array positions `aa`. -/
def constSummary (n : Nat) (aa : Nat → Option Nat) : CallRes → ProcSummary
  | .word r => { arity := n, run := fun _ => some r, arrArgs := aa }
  | .arr (n := m) a =>
      ⟨n, fun _ => none, aa, some m, fun k _ => if h : k = m then some (h ▸ a) else none⟩

theorem constSummary_result (n : Nat) (aa : Nat → Option Nat) (x : CallRes)
    (vs : List (BitVec 64)) : (constSummary n aa x).result vs = some x := by
  cases x with
  | word r => rfl
  | arr a => simp [constSummary, ProcSummary.result]

theorem constSummary_arrArgs (n : Nat) (aa : Nat → Option Nat) (x : CallRes) :
    (constSummary n aa x).arrArgs = aa := by
  cases x <;> rfl

theorem constSummary_arity (n : Nat) (aa : Nat → Option Nat) (x : CallRes) :
    (constSummary n aa x).arity = n := by
  cases x <;> rfl

/-- **The step of the summary answering a fixed result** writes it, when the operands are as
    many as its arguments and are read. -/
theorem procStep_constSummary {n : Nat} {aa : Nat → Option Nat} (x : CallRes) (dst : String)
    {srcs : List LOperand} {s : LstateMF} (hl : srcs.length = n)
    (hr : (argsRead aa s.prog.base 0 srcs).isSome) :
    procStep (constSummary n aa x) dst srcs s = some (retRes dst x s) := by
  obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp hr
  unfold procStep
  rw [constSummary_arity, ite_eq_left hl, constSummary_arrArgs, hvs]
  simp only [Option.bind_some, constSummary_result, Option.map_some]

/-- **A call site of a body is matched by the copies and a call site of its rewriting onto
    common names**, and the state after the call of the rewriting by the copy of the result
    and a state related to the state after the call of the body. Under `CommonSimT` at the
    names `N`, let the shape of the entry of the symbol of the event `e` have word positions
    where the arguments of `e` are words, and a word result unless it is an out result. -/
theorem common_site {T : ProcTable}
    {tab : String → Option (CallShape × List String × String)}
    {N : List String} {fn : String} {B B' : List LinstrRM} (hB : commonCallsT? tab B = some B')
    (hc : CommonSimT T tab N B) {e : NFCall jasminDialect} {s s' : LstateMF}
    (hr : OffRel N (expPosT tab B) s s')
    (hsi : NFProgCallTreeExport.CallSite (singletonProgM fn B) e s)
    (hev : ∀ sh args res, tab e.name = some (sh, args, res) →
      (∀ i, sh.arrArgs i = none → arrArgsOf e.argTys i = none)
      ∧ (sh.out = false → resLen e.resTys = none)) :
    ∃ k u'', Steps x86Isa (singletonProgM fn B') k s' u''
      ∧ NFProgCallTreeExport.CallSite (singletonProgM fn B') e u''
      ∧ ∀ a v', CallRet (singletonProgM fn B') e u'' a v' →
        ∃ v, CallRet (singletonProgM fn B) e s a v
          ∧ ∃ k' v'', Steps x86Isa (singletonProgM fn B') k' v' v''
            ∧ OffRel N (expPosT tab B) v v'' := by
  obtain ⟨L', hL, rfl⟩ := hr
  obtain ⟨d, srcs, tag, p, hat, hfk, hlenA, hrd⟩ := hsi
  have hfi : B[p]? = some (callShadow d e.name srcs, tag) := hfk
  have hpc : s.prog.base.reg.lpc = p := hat.2
  have hmem : (callShadow d e.name srcs, tag) ∈ B := List.mem_of_getElem? hfi
  have hs : shadowCall? (callShadow d e.name srcs, tag).fst = some (d, e.name, srcs) :=
    shadowCall?_callShadow d e.name srcs
  obtain ⟨is, pre, post, his, hB', hpre⟩ := commonCallsT?_split hB hfi
  obtain ⟨sh, args, res, xs, htab, hxs, hlen, rfl⟩ := commonCallT?_some his hs
  obtain ⟨haa, hro⟩ := hev sh args res htab
  have hN := hc.names e.name sh args res htab
  have hxN := hc.ops _ hmem d e.name srcs xs hs hxs
  have hnd := hc.nodup e.name sh args res htab
  have hsrcs := regNames?_eq hxs
  subst hsrcs
  have hsucc := expPosT_succ tab hfi
  have hlenE : expLenT tab (callShadow d e.name (xs.map LOperand.reg), tag)
      = commonLen sh args.length := by
    simp [expLenT, shadowCall?_callShadow, htab]
  rw [hlenE, ← hpre] at hsucc
  rw [hpc, ← hpre]
  -- the state of the rewriting at the form, and the copies
  set s0 := setRL L' pre.length s with hs0
  set ps := commonPairs sh 0 args xs with hps
  set dst' := if sh.out then d else res with hdst'
  set ops := (commonOps sh 0 args xs).map LOperand.reg with hops
  have hxa : ∀ x ∈ xs, x ∉ args := fun x hx ha => hxN x hx (hN x (List.mem_cons_of_mem _ ha))
  have hB'' : (singletonProgM fn B').body = pre ++ (ps.map fun q => LprogCallCut.movI q.1 q.2)
      ++ ((callShadow dst' e.name ops, MemTag.reg none)
        :: ((if sh.out then [] else [LprogCallCut.movI d res]) ++ post)) := by
    show B' = _
    rw [hB', commonSeq]
    cases hout : sh.out <;> simp [hout, hdst', hps, hops]
  have hat0 : atPc (singletonProgM fn B') pre.length s0 := ⟨hat.1, rfl⟩
  have hrun1 : x86Isa.runL (singletonProgM fn B') (ps.map fun q => LprogCallCut.movI q.1 q.2) s0
      = some (movesF ps s0) := by
    rw [← runI_eq_runL]
    exact runI_moves_x86 _ ps s0
  obtain ⟨hst1, hat1⟩ := steps_of_runL x86Isa (singletonProgM fn B') _ pre _ s0 _ hB'' hat0
    (fun i hi u u' hu => by
      obtain ⟨q, -, rfl⟩ := List.mem_map.mp hi
      rw [x86_step_movI] at hu
      cases hu
      exact ⟨rfl, rfl⟩) hrun1
  set u1 := movesF ps s0 with hu1
  rw [List.length_map] at hat1 hst1
  -- the arguments read at the call site of the rewriting
  have hsub := commonPairs_sublist sh 0 args xs
  have hfst : ∀ q ∈ ps, q.1 ∈ args := fun q hq => (List.of_mem_zip (hsub.subset hq)).1
  have hsnd : ∀ q ∈ ps, q.2 ∈ xs := fun q hq => (List.of_mem_zip (hsub.subset hq)).2
  have hnd' : (ps.map Prod.fst).Nodup :=
    (hsub.map Prod.fst).nodup (by rw [List.map_fst_zip (by omega)]; exact hnd)
  have hnf : ∀ r, r ∉ args → r ∉ ps.map Prod.fst := by
    intro r hr hm
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact hr (hfst q hq)
  have hU1 : ∀ q ∈ ps, u1.prog.base.reg.lvm q.1 = s.prog.base.reg.lvm q.2 := fun q hq => by
    rw [hu1, lvm_movesF_of_mem _ s0 hnd' (fun q' hq' => hnf _ (hxa _ (hsnd q' hq'))) q hq]
    exact hL _ (hxN _ (hsnd q hq))
  have hU2 : ∀ x ∈ xs, u1.prog.base.reg.lvm x = s.prog.base.reg.lvm x := fun x hx => by
    rw [hu1, lvm_movesF_of_not_mem _ s0 x (hnf x (hxa x hx))]
    exact hL x (hxN x hx)
  have hla : u1.prog.base.larr = s.prog.base.larr := by
    rw [hu1, movesF_eq_regUpd]
    rfl
  have hread : argsRead (arrArgsOf e.argTys) u1.prog.base 0 ops = some (wordsOf e.args) := by
    rw [hops, argsRead_commonOps haa hla 0 args xs hlen.symm hU1 hU2]
    exact hrd
  have hopsl : ops.length = e.argTys.length := by
    rw [hops, List.length_map, commonOps_length sh 0 args xs hlen.symm, ← hlen, ← hlenA,
      List.length_map]
  have hcallAt : (singletonProgM fn B').body[pre.length + ps.length]?
      = some (callShadow dst' e.name ops, MemTag.reg none) := by
    rw [hB'', List.append_assoc, List.getElem?_append_right (by omega),
      List.getElem?_append_right (by simp)]
    simp
  refine ⟨ps.length, u1, hst1, ⟨dst', ops, .reg none, pre.length + ps.length, hat1, hcallAt,
    hopsl, hread⟩, ?_⟩
  -- the state after the call
  rintro a v' ⟨dst'', ops', tag'', k', rv, hatk, hfk', rfl, hout⟩
  obtain rfl : k' = pre.length + ps.length := hatk.2.symm.trans hat1.2
  rw [hcallAt] at hfk'
  simp only [Option.some.injEq, Prod.mk.injEq, callShadow, LinstrR.Lopn.injEq,
    List.cons.injEq, LOperand.reg.injEq, and_true] at hfk'
  obtain ⟨⟨h1, -, h2⟩, -⟩ := hfk'
  subst h1 h2
  obtain ⟨rfl, hxlen, hback⟩ := callOut_retRes hout
  set x := callResOf e.resTys rv with hx
  refine ⟨retRes d x s, ⟨d, xs.map LOperand.reg, tag, p, rv, hat, hfk, rfl, hback d s⟩, ?_⟩
  -- the run of the form with the summary answering `x`
  set pr := constSummary xs.length (arrArgsOf e.argTys) x with hpr
  have hro' : sh.out = false → pr.RetWord := by
    intro hout0
    have h1 := hxlen.trans (hro hout0)
    rw [hpr]
    cases hxc : x with
    | word r => rfl
    | arr a => rw [hxc] at h1; cases h1
  have haa' : ∀ i, sh.arrArgs i = none → pr.arrArgs i = none := fun i hi => by
    rw [hpr, constSummary_arrArgs]
    exact haa i hi
  have hrd0 : (argsRead (arrArgsOf e.argTys) s0.prog.base 0 (xs.map LOperand.reg)).isSome := by
    rw [argsRead_congr (b := s.prog.base) (b' := s0.prog.base) _ rfl 0 _ (fun o ho => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ho
        simp only [evalOperandN, LstateN.getW]
        rw [show s0.prog.base.reg.lvm y = L' y from rfl, hL y (hxN y hy)]), hrd]
    rfl
  have hstep0 : procStep pr d (xs.map LOperand.reg) s0 = some (retRes d x s0) :=
    procStep_constSummary x d (by rw [List.length_map]) hrd0
  obtain ⟨L₂, hrun, hL₂⟩ := commonCall_sim (T := fun _ => some pr) (f := e.name) rfl haa' hro'
    (singletonProgM fn B') res d hlen hnd hxa hstep0
  have hstepC : (x86Isa.withProcs fun _ => some pr).step (singletonProgM fn B')
      (callShadow dst' e.name ops, .reg none) u1 = some (retRes dst' x u1) := by
    show (match procCall? (fun _ => some pr) (callShadow dst' e.name ops) with
      | some q => procStep q.1 q.2.1 q.2.2 u1
      | none => _) = _
    rw [procCall?_callShadow]
    simp only [Option.map_some]
    refine procStep_constSummary x dst' ?_ ?_
    · rw [hopsl, ← hlenA, List.length_map]
    · simp only [hread, Option.isSome_some]
  rw [commonSeq, runI_append, runI_moves, ← hps] at hrun
  simp only [Option.bind_some] at hrun
  have hk : pre.length + 1 + (wordCount sh 0 args.length + if sh.out then 0 else 1)
      = pre.length + commonLen sh args.length := by
    rw [commonLen]
    omega
  cases hout0 : sh.out with
  | false =>
      simp only [hout0, Bool.false_eq_true, ite_false] at hrun hdst'
      rw [← hops] at hrun
      simp only [runI, show s0 = setRL L' pre.length s from rfl] at hrun
      rw [hdst'] at hstepC
      rw [hstepC] at hrun
      simp only [Option.bind_some, step_movI, Option.some.injEq] at hrun
      have hmovAt : (singletonProgM fn B').body[pre.length + ps.length + 1]?
          = some (LprogCallCut.movI d res) := by
        rw [hB'', hout0]
        simp only [Bool.false_eq_true, ite_false, List.append_assoc]
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by simp; omega),
          show pre.length + ps.length + 1 - pre.length - (ps.map fun q =>
            LprogCallCut.movI q.1 q.2).length = 1 by simp; omega]
        rfl
      have hat2 : atPc (singletonProgM fn B') (pre.length + ps.length + 1) (retRes dst' x u1) :=
        ⟨by rw [LprogIsa.lfn_retRes]; exact hat1.1, by rw [LprogIsa.lpc_retRes, hat1.2]⟩
      refine ⟨1, _, Steps.one (by rw [lsemStepPMemF_of_atPc _ hat2 hmovAt, x86_step_movI]),
        L₂, fun r hr' => ?_, ?_⟩
      · have hra : r ∉ args := fun ha => hr' (hN r (List.mem_cons_of_mem _ ha))
        have hrr : r ≠ res := fun he => hr' (hN r (he ▸ List.mem_cons_self))
        rw [hL₂ r hra hrr, lvm_retRes, lvm_retRes]
        have hLr := hL r hr'
        cases x with
        | word w =>
            change (if r = d then _ else L' r) = (if r = d then _ else s.prog.base.reg.lvm r)
            split
            · rfl
            · exact hLr
        | arr a => exact hLr
      · have hl : (retRes d x s).prog.base.reg.lpc = p + 1 := by
          rw [← hpc]
          cases x <;> rfl
        rw [hl, hsucc, ← hk, hdst', hrun, hout0]
        simp only [Bool.false_eq_true, ite_false]
        cases x <;> rfl
  | true =>
      simp only [hout0, ite_true] at hrun hdst'
      rw [← hops] at hrun
      simp only [runI, show s0 = setRL L' pre.length s from rfl] at hrun
      rw [hdst'] at hstepC
      rw [hstepC] at hrun
      simp only [Option.bind_some, Option.some.injEq] at hrun
      refine ⟨0, _, Steps.refl _ _ _, L₂, fun r hr' => ?_, ?_⟩
      · have hra : r ∉ args := fun ha => hr' (hN r (List.mem_cons_of_mem _ ha))
        have hrr : r ≠ res := fun he => hr' (hN r (he ▸ List.mem_cons_self))
        rw [hL₂ r hra hrr, lvm_retRes, lvm_retRes]
        have hLr := hL r hr'
        cases x with
        | word w =>
            change (if r = d then _ else L' r) = (if r = d then _ else s.prog.base.reg.lvm r)
            split
            · rfl
            · exact hLr
        | arr a => exact hLr
      · have hl : (retRes d x s).prog.base.reg.lpc = p + 1 := by
          rw [← hpc]
          cases x <;> rfl
        rw [hl, hsucc, ← hk, hdst', hrun, hout0]
        simp only [ite_true]
        cases x <;> rfl

/-- **A call tree related to the states of a body is related to the states of its rewriting onto
    common names.** Under `CommonSimT` at the names `N`, let every event at a call site of `B`
    meet the shape of the entry of its symbol: word positions where its arguments are words,
    and a word result unless the shape has an out result. A tree related by `TSim` on the x86
    flag machine to `s`, at the call sites and the states after the calls of `B`, is related to
    every state that `OffRel N` relates to `s` along `expPosT`, at the call sites and the states
    after the calls of the rewriting, at every end condition that `OffRel N` carries `Post`
    to. -/
theorem tsim_common {T : ProcTable}
    {tab : String → Option (CallShape × List String × String)}
    {N : List String} {fn : String} {B B' : List LinstrRM} (hB : commonCallsT? tab B = some B')
    (hc : CommonSimT T tab N B)
    (hev : ∀ e u, NFProgCallTreeExport.CallSite (singletonProgM fn B) e u →
      ∀ sh args res, tab e.name = some (sh, args, res) →
        (∀ i, sh.arrArgs i = none → arrArgsOf e.argTys i = none)
        ∧ (sh.out = false → resLen e.resTys = none))
    {α : Type} {Post Post' : α → LstateMF → Prop}
    (hpost : ∀ x m m', OffRel N (expPosT tab B) m m' → Post x m → Post' x m')
    {t : CallTree (nfCallSig jasminDialect) (Option α)} {s s' : LstateMF}
    (hr : OffRel N (expPosT tab B) s s')
    (h : TSim x86Isa (singletonProgM fn B) (NFProgCallTreeExport.CallSite (singletonProgM fn B))
      (CallRet (singletonProgM fn B)) t s Post) :
    TSim x86Isa (singletonProgM fn B')
      (NFProgCallTreeExport.CallSite (singletonProgM fn B'))
      (CallRet (singletonProgM fn B')) t s' Post' := by
  refine TSim.transfer' (OffRel N (expPosT tab B)) ?_
    (fun e u u' hr hsi => common_site hB hc hr hsi (hev e u hsi)) hpost hr h
  intro n s t s' hs hr
  obtain ⟨t', ht', hrt⟩ := Ascent.IsaCall.steps_of_step_rel x86Isa x86Isa
    (OffRel N (expPosT tab B)) (fun s s' u hr hu => common_step_x86 hB hc hu hr) n s s' t hr hs
  exact ⟨n, t', ht', hrt⟩

end Site

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCommon
