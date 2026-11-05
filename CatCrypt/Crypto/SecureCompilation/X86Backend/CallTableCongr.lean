/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CheckedIsaCall

@[expose] public section

set_option autoImplicit false

/-!
# The checks of calling bodies under tables that agree on the called names

Two procedure tables `T` and `T'` agree on a body `B` (`ProcTable.DomEq T T' B`) when, for
the symbol of every shadow instruction of a call in `B`, both tables hold a summary of the
same arity or both hold none. The Boolean checks of calling bodies read the table only
through `procCall?`, and of its result only whether it is present and the destination, so
they are equal under two tables that agree on the bodies they inspect. A
check passed at one table is therefore a check passed at every table that agrees with it,
and the soundness theorems of the checks apply at that table.

## Main definitions

* `ProcTable.DomEq`: agreement of two tables on the arities of the symbols called in a body.

## Main results

* `ProcTable.DomEq.procCall?_map_snd`: agreeing tables give the same destination and
  operands at a shadow instruction of the body.
* `sites_congr`, `isCutB_congr`, `cutOkB_congr`, `isCutRevB_congr`, `segWalk_congr`,
  `blockInvOkP_congr`, `idxInvCheckPB_congr`, `calleeSegB_congr`: the checks are equal under
  agreeing tables.
* `domEq_cutAt`: agreement on a body gives agreement on its cut programs.
* `domEq_of_symsB`: tables that agree on the symbols accepted by a predicate agree on a body
  that calls only such symbols.
* `refRun_checked_of_domEq`, `calleeSegB_soundK_of_domEq`: `CheckedIsaCall.refRun_checked`
  and `CalleeSegCheck.calleeSegB_soundK` from checks passed at an agreeing table.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem

/-- **Agreement of two procedure tables on a body**: for the symbol of every shadow
    instruction of a call in `B`, the two tables hold summaries of the same arity, or both
    hold none. -/
def ProcTable.DomEq (T T' : ProcTable) (B : List LinstrRM) : Prop :=
  ∀ i ∈ B, ∀ q, shadowCall? i.fst = some q →
    (T q.2.1).map (·.arity) = (T' q.2.1).map (·.arity)

namespace ProcTable.DomEq

variable {T T' : ProcTable} {B C : List LinstrRM}

theorem symm (h : DomEq T T' B) : DomEq T' T B := fun i hi q hq => (h i hi q hq).symm

theorem mono (h : DomEq T T' B) (hC : ∀ j ∈ C, j ∈ B ∨ shadowCall? j.fst = none) :
    DomEq T T' C := fun j hj q hq => by
  rcases hC j hj with hj | hn
  · exact h j hj q hq
  · rw [hn] at hq; cases hq

/-- **Agreeing tables give the same destination and operands** at a shadow instruction of
    the body. -/
theorem procCall?_map_snd (h : DomEq T T' B) {i : LinstrRM} (hi : i ∈ B) :
    (procCall? T i.fst).map Prod.snd = (procCall? T' i.fst).map Prod.snd := by
  unfold procCall?
  cases hs : shadowCall? i.fst with
  | none => rfl
  | some q =>
      have e := h i hi q hs
      simp only [Option.bind_some]
      cases h1 : T q.2.1 <;> cases h2 : T' q.2.1 <;> simp_all

theorem procCall?_isSome (h : DomEq T T' B) {i : LinstrRM} (hi : i ∈ B) :
    (procCall? T i.fst).isSome = (procCall? T' i.fst).isSome := by
  have e := congrArg Option.isSome (h.procCall?_map_snd hi)
  simpa only [Option.isSome_map] using e

end ProcTable.DomEq

end CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CallTableCongr

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa ProcTable ProcSummary procCall?
  shadowCall?)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa)
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.CheckedIsaCall
open CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck
open CatCrypt.Crypto.SecureCompilation.X86Backend.IdxInvCheck (IdxFact SFact)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG (CFG Block Term)

variable {T T' : ProcTable}

/-! ## 1. The checks of the cut programs -/

theorem isProcB_congr {B : List LinstrRM} (h : ProcTable.DomEq T T' B) {i : LinstrRM}
    (hi : i ∈ B) : isProcB T i = isProcB T' i :=
  h.procCall?_isSome hi

/-- **The sites of a body are the same under agreeing tables.** -/
theorem sites_congr {B : List LinstrRM} (h : ProcTable.DomEq T T' B) :
    sites T B = sites T' B := by
  unfold sites
  refine List.filter_congr fun p _ => ?_
  cases hb : B[p]? with
  | none => rfl
  | some i => simp only [Option.any_some, isProcB_congr h (List.mem_of_getElem? hb)]

theorem isCutB_congr [DecidableEq LinstrR] {fn : String} {B : List LinstrRM}
    (h : ProcTable.DomEq T T' B) (e x : Option Nat) (C : List LinstrRM) (φ : Nat → Nat) :
    isCutB T fn B e x C φ = isCutB T' fn B e x C φ := by
  unfold isCutB
  congr 3
  refine List.all_congr rfl fun p => ?_
  cases hb : B[p]? with
  | none => rfl
  | some i => simp only [h.procCall?_isSome (List.mem_of_getElem? hb)]

/-- **The check of the cut programs is the same under agreeing tables.** -/
theorem cutOkB_congr [DecidableEq LinstrR] {fn : String} {fin : LLabel} {B : List LinstrRM}
    (h : ProcTable.DomEq T T' B) : cutOkB T fn fin B = cutOkB T' fn fin B := by
  simp only [cutOkB, sites_congr h, isCutB_congr h]

/-- **The reverse check of a cut is the same under tables that agree on the body and on
    the cut.** -/
theorem isCutRevB_congr {B C : List LinstrRM} (hB : ProcTable.DomEq T T' B)
    (hC : ProcTable.DomEq T T' C) (x : Option Nat) (φ : Nat → Nat) :
    isCutRevB T B x C φ = isCutRevB T' B x C φ := by
  have hCi : ∀ k : Nat, (C[k]?).any (isProcB T) = (C[k]?).any (isProcB T') := fun k => by
    cases hc : C[k]? with
    | none => rfl
    | some j => simp only [Option.any_some, isProcB_congr hC (List.mem_of_getElem? hc)]
  unfold isCutRevB
  rw [hCi]
  congr 1
  refine List.all_congr rfl fun p => ?_
  cases hb : B[p]? with
  | none => rfl
  | some i =>
      have e := hB.procCall?_isSome (List.mem_of_getElem? hb)
      simp only [← Option.not_isSome, e, hCi]

/-- **Agreement on a body gives agreement on its cut programs.** -/
theorem domEq_cutAt {fn : String} {fin : LLabel} {B : List LinstrRM}
    (h : ProcTable.DomEq T T' B) (e x : Option Nat) :
    ProcTable.DomEq T T' (cutAt fn fin B e x) := by
  have hexit : shadowCall? (exitI fn fin).fst = none := rfl
  have hfin : shadowCall? (finI fin).fst = none := rfl
  have hO : (match x with
      | none => exitI fn fin
      | some p => (B[p]?).getD (exitI fn fin)) ∈ B ∨
      shadowCall? (match x with
        | none => exitI fn fin
        | some p => (B[p]?).getD (exitI fn fin)).fst = none := by
    cases x with
    | none => exact Or.inr hexit
    | some p =>
        cases hb : B[p]? with
        | none => simp only [hb, Option.getD_none]; exact Or.inr hexit
        | some i => simp only [hb, Option.getD_some]; exact Or.inl (List.mem_of_getElem? hb)
  have hset : ∀ j ∈ (match x with | none => B | some p => B.set p (exitI fn fin)),
      j ∈ B ∨ shadowCall? j.fst = none := by
    intro j hj
    cases x with
    | none => exact Or.inl hj
    | some p =>
        rcases List.mem_or_eq_of_mem_set hj with hj | rfl
        · exact Or.inl hj
        · exact Or.inr hexit
  have key : ∀ (B' : List LinstrRM) (O : LinstrRM),
      (∀ j ∈ B', j ∈ B ∨ shadowCall? j.fst = none) → (O ∈ B ∨ shadowCall? O.fst = none) →
      ∀ j ∈ (match e with
        | none => B' ++ [O, finI fin]
        | some p => B'.drop (p + 1) ++ [O] ++ B'.take p ++ [(B'[p]?).getD O, finI fin]),
        j ∈ B ∨ shadowCall? j.fst = none := by
    intro B' O hB' hO' j hj
    cases e with
    | none =>
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with hj | rfl | rfl
        · exact hB' j hj
        · exact hO'
        · exact Or.inr hfin
    | some p =>
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with ((hj | rfl) | hj) | rfl | rfl
        · exact hB' j (List.mem_of_mem_drop hj)
        · exact hO'
        · exact hB' j (List.mem_of_mem_take hj)
        · cases hg : B'[p]? with
          | none => exact hO'
          | some i => exact hB' i (List.mem_of_getElem? hg)
        · exact Or.inr hfin
  exact h.mono (key _ _ hset hO)

/-! ## 2. The bounds check with calls -/

/-- **The segmented walk is the same under tables that agree on the stretch.** -/
theorem segWalk_congr (cs : List IdxFact) {is : List LinstrRM} (h : ProcTable.DomEq T T' is) :
    ∀ (F : List SFact) (ss : SSt), segWalk T cs F ss is = segWalk T' cs F ss is := by
  induction is with
  | nil => intro F ss; rfl
  | cons i is ih =>
      intro F ss
      have hm := h.procCall?_map_snd List.mem_cons_self
      have ht := ih (h.mono fun j hj => Or.inl (List.mem_cons_of_mem _ hj))
      simp only [segWalk]
      cases h1 : procCall? T i.fst <;> cases h2 : procCall? T' i.fst <;>
        rw [h1, h2] at hm <;> simp only [Option.map_none, Option.map_some, reduceCtorEq,
          Option.some.injEq] at hm
      · simp only [ht]
      · simp only [hm, ht]

private theorem mem_list_of_mem_bodyAt {B : List LinstrRM} {b : Block} {Tm : Term} {j : LinstrRM}
    (hj : j ∈ bodyAt B b Tm) : j ∈ B :=
  List.mem_of_mem_drop (List.mem_of_mem_take hj)

theorem blockInvOkP_congr {ann : List (List IdxFact)} {B : List LinstrRM}
    (h : ProcTable.DomEq T T' B) (G : CFG) (k : Nat) :
    blockInvOkP T ann B G k = blockInvOkP T' ann B G k := by
  unfold blockInvOkP
  split
  · rfl
  · rw [segWalk_congr _ (h.mono fun j hj => Or.inl (mem_list_of_mem_bodyAt hj))]

/-- **The bounds check with calls is the same under tables that agree on the body.** -/
theorem idxInvCheckPB_congr {entry : List IdxFact} {ann : List (List IdxFact)}
    {B : List LinstrRM} (h : ProcTable.DomEq T T' B) :
    idxInvCheckPB T entry ann B = idxInvCheckPB T' entry ann B := by
  have e : blockInvOkP T ann B = blockInvOkP T' ann B :=
    funext fun G => funext fun k => blockInvOkP_congr h G k
  simp only [idxInvCheckPB, e]

/-! ## 3. The checks of the segments -/

/-- **The checks of the segments are the same under tables that agree on the reference and
    on the image.** -/
theorem calleeSegB_congr {fn : String} {fin : LLabel}
    {ins : Option Nat → List String} {outs : List String} {ref img : List LinstrRM}
    (hr : ProcTable.DomEq T T' ref) (hi : ProcTable.DomEq T T' img) :
    calleeSegB T fn fin ins outs ref img = calleeSegB T' fn fin ins outs ref img := by
  simp only [calleeSegB, siteMap, sites_congr hr, sites_congr hi]

/-- **Tables that agree on the symbols accepted by `ok` agree on a body whose every shadow
    instruction of a call calls such a symbol.** -/
theorem domEq_of_symsB {ok : String → Bool} {B : List LinstrRM} (h : callSymsB ok B = true)
    (hf : ∀ f, ok f = true → (T f).map (·.arity) = (T' f).map (·.arity)) :
    ProcTable.DomEq T T' B := by
  intro i hi q hq
  have hm := List.all_eq_true.mp h i hi
  rw [hq, Option.all_some] at hm
  exact hf _ hm

/-! ## 4. Soundness at an agreeing table -/

/-- **`refRun_checked` from a bounds check passed at an agreeing table.** If
    `idxInvCheckPB T₀ entry ann B` accepts and `T₀` agrees with `T` on `B`, a halting run of
    `x86Isa.withProcs T` on the singleton program over `B` from a state at pc `0` of that
    function whose registers satisfy the entry facts is a halting run of
    `x86IsaK.withProcs T`, to the same state. -/
theorem refRun_checked_of_domEq {T₀ : ProcTable} {entry : List IdxFact}
    {ann : List (List IdxFact)} {B : List LinstrRM} (h : idxInvCheckPB T₀ entry ann B = true)
    (hD : ProcTable.DomEq T₀ T B) (fn : String) (s t : LstateMF) (hfn : s.prog.lfn = fn)
    (hpc : s.prog.base.reg.lpc = 0)
    (hent : ∀ f ∈ entry, f.holds s.prog.base.reg.lvm s.prog.base.larr) (fuel : Nat)
    (hrun : (x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn B) fuel s = some t) :
    (x86IsaK.withProcs T).lsemFuelMemF (singletonProgM fn B) fuel s = some t :=
  refRun_checked ((idxInvCheckPB_congr hD).symm.trans h) fn s t hfn hpc hent fuel hrun

/-- **`calleeSegB_soundK` from checks of the segments passed at an agreeing table.** Where
    at every site of `ref` the summary at `T` of the symbol has no word-array result or the
    destination is among the operands, if `calleeSegB T₀` accepts and `T₀` agrees with `T`
    on `ref` and `img`, then under `CutCheckSoundI` at `T` every halting run of
    `x86IsaK.withProcs T` on `ref` from a state of `fn` at the counter `0` is matched by a
    halting run on `img` from the same state, the end states agreeing on `outs`, the arrays
    and the word memory. -/
theorem calleeSegB_soundK_of_domEq {T₀ : ProcTable} {fn : String} {fin : LLabel}
    {ins : Option Nat → List String} {outs : List String} {ref img : List LinstrRM}
    (h : calleeSegB T₀ fn fin ins outs ref img = true)
    (hDr : ProcTable.DomEq T₀ T ref) (hDi : ProcTable.DomEq T₀ T img)
    (hsound : CutCheckSoundI x86IsaK T outs fn ref img (cutAt fn fin ref) (cutAt fn fin img))
    (s t : LstateMF) (hfn : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 0) (fuel : Nat)
    (hrun : (x86IsaK.withProcs T).lsemFuelMemF (singletonProgM fn ref) fuel s = some t)
    (hres : ∀ (p : Nat) (d f : String) (xs : List String) (pr : ProcSummary),
      shadowAt ref p = some (d, f, xs.map LOperand.reg) → T f = some pr → pr.RetWord ∨ d ∈ xs) :
    ∃ fuel' t', (x86IsaK.withProcs T).lsemFuelMemF (singletonProgM fn img) fuel' s = some t'
      ∧ Obs outs t t' :=
  calleeSegB_soundK ((calleeSegB_congr hDr hDi).symm.trans h) hsound s t hfn hpc fuel hrun hres

end CatCrypt.Crypto.SecureCompilation.X86Backend.CallTableCongr
