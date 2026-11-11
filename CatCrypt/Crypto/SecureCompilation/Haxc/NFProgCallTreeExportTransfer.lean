/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls

/-!
# Call trees related to runs, carried through simulations of programs

A call tree related by `NFProgCallTreeExport.TSim` to a state of a program `P` is related to
every state of a program `P'` that a simulation relates to it, when the simulation carries runs
of `P` to runs of `P'`, call sites of `P` to call sites of `P'`, and the states after a call of
`P'` back to states after the call of `P` (`TSim.transfer`). A simulation of single steps by
runs, with no bound on the steps of `P'` that match one step of `P`, carries runs
(`steps_sim_of_step`). The relocation of a body between a prefix and a suffix is one
(`tsim_relocate`). The passes that rewrite the exported code of a region into its
reference are simulations of this kind; each relates the call tree of the program to the
states of the rewritten code.

A source tree whose interpretation under the source handler fails is related by `RuttF` to
every family of target trees: its events are skipped at the answers of the handler
(`ruttF_of_fail`).

## Main results

* `steps_sim_of_step`: a simulation of single steps by runs is a simulation of runs.
* `TSim.transfer`: a simulation of runs that carries call sites and the states after the calls
  carries `TSim`.
* `tsim_relocate`: a tree related to the states of a body is related to the shifted states of
  the body between a prefix and a suffix, at the call sites of the larger program.
* `ruttF_of_fail`: a source tree failing under the source handler is related to every family.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExportTransfer

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (LprogM)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (LstateMF)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeCalls (RuttF)

/-! ## Simulations of runs -/

/-- A run of `n + 1` steps is a step followed by a run of `n` steps. -/
theorem steps_succ {I : Isa} {P : LprogM} {n : Nat} {s t : LstateMF}
    (h : Steps I P (n + 1) s t) : ∃ u, I.lsemStepPMemF P s = some u ∧ Steps I P n u t := by
  simp only [Steps, CatCrypt.Crypto.SecureCompilation.Ascent.CutPoint.iter,
    Option.bind_eq_some_iff] at h
  exact h

/-- **A simulation of single steps by runs is a simulation of runs.** If every step of `I` on
    `P` from a state related by `R` to `s'` is matched by a run of `I'` on `P'` from `s'` to a
    state related to the state after the step, every run of `I` on `P` is matched by a run of
    `I'` on `P'`. -/
theorem steps_sim_of_step {I I' : Isa} {P P' : LprogM} (R : LstateMF → LstateMF → Prop)
    (h1 : ∀ s u s', I.lsemStepPMemF P s = some u → R s s' →
      ∃ k' u', Steps I' P' k' s' u' ∧ R u u') :
    ∀ (n : Nat) (s t s' : LstateMF), Steps I P n s t → R s s' →
      ∃ k' t', Steps I' P' k' s' t' ∧ R t t'
  | 0, s, t, s', h, hR => by
      have hst : s = t := Option.some.inj h
      subst hst
      exact ⟨0, s', Steps.refl I' P' s', hR⟩
  | n + 1, s, t, s', h, hR => by
      obtain ⟨u, hu, hn⟩ := steps_succ h
      obtain ⟨k1, u', hs1, hRu⟩ := h1 s u s' hu hR
      obtain ⟨k2, t', hs2, hRt⟩ := steps_sim_of_step R h1 n u t u' hn hRu
      exact ⟨k1 + k2, t', hs1.trans hs2, hRt⟩

/-- **A simulation carries the relation of call trees and states.** Let `R` relate states of
    `P` to states of `P'`, carry runs of `I` on `P` to runs of `I'` on `P'`, carry the call
    sites `Site` to the call sites `Site'`, and carry every state after a call of `P'` at an
    answer (`Q'`) back to a state after the call of `P` at that answer (`Q`) related to it. A
    tree related by `TSim` to `s` at the end condition `Post` is related to every state that
    `R` relates to `s`, at every end condition that `R` carries `Post` to. -/
theorem TSim.transfer {E : EventSig} {I I' : Isa} {P P' : LprogM}
    {Site Site' : E.Event → LstateMF → Prop}
    {Q Q' : (e : E.Event) → LstateMF → E.Resp e → LstateMF → Prop} {α : Type}
    {Post Post' : α → LstateMF → Prop} (R : LstateMF → LstateMF → Prop)
    (hst : ∀ (n : Nat) (s t s' : LstateMF), Steps I P n s t → R s s' →
      ∃ k' t', Steps I' P' k' s' t' ∧ R t t')
    (hsite : ∀ e u u', R u u' → Site e u → Site' e u')
    (hans : ∀ e u u' a v', R u u' → Site e u → Q' e u' a v' → ∃ v, Q e u a v ∧ R v v')
    (hpost : ∀ x m m', R m m' → Post x m → Post' x m') :
    ∀ {t : CallTree E (Option α)} {s s' : LstateMF}, R s s' →
      TSim I P Site Q t s Post → TSim I' P' Site' Q' t s' Post'
  | .ret none, _, _, _, _ => trivial
  | .ret (some x), s, s', hR, ⟨k, m, hs, hp⟩ => by
      obtain ⟨k', m', hs', hRm⟩ := hst k s m s' hs hR
      exact ⟨k', m', hs', hpost x m m' hRm hp⟩
  | .vis e c, s, s', hR, ⟨k, u, hs, hsi, hc⟩ => by
      obtain ⟨k', u', hs', hRu⟩ := hst k s u s' hs hR
      refine ⟨k', u', hs', hsite e u u' hRu hsi, fun a v' hq' => ?_⟩
      obtain ⟨v, hq, hRv⟩ := hans e u u' a v' hRu hsi hq'
      exact TSim.transfer R hst hsite hans hpost hRv (hc a v hq)

/-! ## Relocation of the code -/

section Relocate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (singletonProgM)
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCall (StepRelocates shiftPc LabelsFresh
  steps_relocate)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (CallOut CallRet)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall)

/-- **The state after a call commutes with the shift of the counter.** -/
theorem callOut_shiftPc {dst : String} {k : Nat} :
    ∀ {rs : List JasminTy} {v : Ctxt.Valuation (d := jasminDialect) rs} {u v' : LstateMF},
      CallOut dst rs v (shiftPc k u) v' → ∃ w, CallOut dst rs v u w ∧ v' = shiftPc k w := by
  intro rs v u v' h
  unfold CallOut at h ⊢
  split at h
  · exact ⟨_, rfl, h⟩
  · exact ⟨_, rfl, h⟩
  · exact h.elim

/-- **A call tree related to the states of a body is related to the shifted states of the body
    placed between a prefix and a suffix.** Under `StepRelocates` and `LabelsFresh`, a tree
    related by `TSim` to `s` on `B`, at the call sites and the states after the calls of `B`,
    is related to the shift of `s` by the length of `pre` on `pre ++ B ++ post`, at the call
    sites and the states after the calls of that program, at every end condition that holds at
    the shift of each state where `Post` holds. -/
theorem tsim_relocate {I : Isa} {fn : String} {pre B post : List LinstrRM}
    (hreloc : StepRelocates I fn pre B post) (hfresh : LabelsFresh pre B) {α : Type}
    {Post Post' : α → LstateMF → Prop}
    (hpost : ∀ x m, Post x m → Post' x (shiftPc pre.length m))
    {t : CallTree (nfCallSig jasminDialect) (Option α)} {s : LstateMF}
    (h : TSim I (singletonProgM fn B) (NFProgCallTreeExport.CallSite (singletonProgM fn B))
      (CallRet (singletonProgM fn B)) t s Post) :
    TSim I (singletonProgM fn (pre ++ B ++ post))
      (NFProgCallTreeExport.CallSite (singletonProgM fn (pre ++ B ++ post)))
      (CallRet (singletonProgM fn (pre ++ B ++ post))) t (shiftPc pre.length s) Post' := by
  have hfetch : ∀ (k : Nat) (i : LinstrRM), (singletonProgM fn B).body[k]? = some i →
      (singletonProgM fn (pre ++ B ++ post)).body[pre.length + k]? = some i := by
    intro k i hk
    have hk' : B[k]? = some i := hk
    have hlt : k < B.length := (List.getElem?_eq_some_iff.mp hk').1
    show (pre ++ B ++ post)[pre.length + k]? = some i
    rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hlt]
    exact hk'
  have hargs : ∀ (aa : Nat → Option Nat) (u : LstateMF) (srcs : List LOperand),
      LprogIsa.argsRead aa (shiftPc pre.length u).prog.base 0 srcs
        = LprogIsa.argsRead aa u.prog.base 0 srcs :=
    fun aa u srcs => LprogIsa.argsRead_congr (b := u.prog.base)
      (b' := (shiftPc pre.length u).prog.base) aa rfl 0 srcs (fun o _ => by cases o <;> rfl)
  refine TSim.transfer (fun s s' => s' = shiftPc pre.length s) ?_ ?_ ?_ ?_ rfl h
  · rintro n s t _ hs rfl
    exact ⟨n, shiftPc pre.length t, steps_relocate I fn post hreloc hfresh hs, rfl⟩
  · rintro e u _ rfl ⟨dst, srcs, tag, k, hat, hf, hlen, hrd⟩
    exact ⟨dst, srcs, tag, pre.length + k, ⟨hat.1, by
      show pre.length + u.prog.base.lpc = pre.length + k
      rw [hat.2]⟩, hfetch k _ hf, hlen, (hargs _ u srcs).trans hrd⟩
  · rintro e u _ a v' rfl ⟨dst0, srcs0, tag0, k0, hat0, hf0, -, -⟩
      ⟨dst, srcs, tag, k, res, hat, hf, rfl, hout⟩
    have hk : k = pre.length + k0 := by
      rw [← hat.2, ← hat0.2]
      rfl
    subst hk
    rw [hfetch k0 _ hf0] at hf
    simp only [Option.some.injEq, Prod.mk.injEq, LprogIsa.callShadow, LinstrR.Lopn.injEq,
      List.cons.injEq, LOperand.reg.injEq, and_true] at hf
    obtain ⟨⟨rfl, -⟩, -⟩ := hf
    obtain ⟨w, hw, rfl⟩ := callOut_shiftPc hout
    exact ⟨w, ⟨dst0, srcs0, tag0, k0, res, hat0, hf0, rfl, hw⟩, rfl⟩
  · rintro x m _ rfl hp
    exact hpost x m hp

end Relocate

/-! ## Source trees that fail -/

/-- **A source tree failing under the source handler is related to every family.** If the
    interpretation of `t₁` under `h₁` is a failed leaf, `t₁` is related by `RuttF` to every
    family of target trees: each event of `t₁` on the path of the answers of `h₁` is skipped. -/
theorem ruttF_of_fail {E₁ E₂ : EventSig} {R₁ R₂ : Type} {h₁ : ∀ e : E₁.Event, E₁.Resp e}
    {RE : E₁.Event → E₂.Event → Prop}
    {RA : (e₁ : E₁.Event) → (e₂ : E₂.Event) → E₁.Resp e₁ → E₂.Resp e₂ → Prop}
    {RR : R₁ → R₂ → Prop} {Fail : R₁ → Prop} (T : Nat → CallTree E₂ R₂) :
    ∀ {t₁ : CallTree E₁ R₁}, Fail (interp h₁ t₁) → RuttF h₁ RE RA RR Fail t₁ T
  | .ret _, h => .fail h
  | .vis e k, h => .skip (ruttF_of_fail T (t₁ := k (h₁ e)) h)

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExportTransfer
