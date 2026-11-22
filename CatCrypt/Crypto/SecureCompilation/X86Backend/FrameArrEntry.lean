/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions

/-!
# Entry contents of write-first arrays

An array of the frame holds arbitrary words when the function is entered. The array `A` is
write-first in a code when no path of the control-flow graph from the entry reads `A`, or
leaves the code with `A` observed, before an instruction writes all its cells. This is the
negation of liveness at the entry (`CoalesceComplete.PLive`), so it covers straight code,
loops and branches. A zeroing, a store of a new array version and a call with an array result
write all cells of their destination.

At a call, the semantics of a procedure summary reads the words of every array operand, the
destination operand of an out kernel among them. An array whose first mention is the out
operand of such a call is write-first at the positions `rd` whose words the result depends
on. This dependence is the hypothesis `CallReads` of the instruction set, and for a table of
summaries it follows from `ReadsOnly` of each summary. The call still requires the operand to
be an array of the declared length, so at such an array the two entry states have the same
shape.

## Main definitions

* `WriteFirst`, `writeFirstB`: the predicate and its decision.
* `withArrs`: a state with its arrays replaced.
* `ArgsAgree`, `CallReads`: agreement of two argument lists on the positions read, and an
  instruction set whose calls depend on these positions only.
* `maskWords`, `ReadsOnly`: the same dependence for a procedure summary.
* `AgreeOn`: the agreement of two final states on the observed names.
* `zeroReachB`: no jump in front of the first zeroing of a name passes it.

## Main results

* `zeroFirstB_writeFirst`, `zeroFirstB_writeFirst_straight`: an array first mentioned by its
  zeroing is write-first.
* `writeFirst_of_needClosed`, `writeFirst_of_coCfgB`: an array outside the entry list of a
  liveness certificate is write-first.
* `lsemFuelMemF_congr_writeFirst`: runs from entry states that are equal off the write-first
  arrays halt alike and agree on the observed names; `lsemFuelMemF_congr_writeFirst_procs`
  and `lsemFuelMemF_congr_writeFirst_noCalls` are its instances with a table of linked
  procedures and without calls.
* `zeroFirstB_exportR_fresh`, `writeFirst_exportR_fresh`: the export of an array zeroing
  zeroes its root before any other mention.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.FrameArrEntry

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (exportR Exported
  bindOps)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN (LstateN evalOperandN)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin (isLopnB isLopnB_isLopn)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa ProcTable ProcSummary CallRes
  callShadow shadowCall? shadowCall?_callShadow eq_callShadow_of_shadowCall? retRes retWord
  retArr argRead argsRead procStep procCall?)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa.Isa (procArrArgs procOut)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs (evalInstrPMemF_shadowCall
  x86Isa_refusesProcs)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_lsemFuelMemF)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstGuard (constTakenB GuardInv
  guardInv_zero guardInv_step guardInv_retRes takenAt_of_guardInv)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (arrReads arrWrite
  CoRel zeroDst? zeroFirstB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg
open CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete

/-! ## 1. The predicate -/

/-- **The array `A` is write-first in `code`**, whose observed names are `obs`: no path from
    the entry reaches an instruction that reads `A`, or the end of the code with `A` in
    `obs`, before an instruction writes all cells of `A`. The array positions read by the
    calls are `rd`, and the lengths of their array results are `ao`. -/
def WriteFirst (A : String) (code : List LinstrRM) (obs : List String)
    (rd : String → Nat → Option Nat := fun _ _ => none)
    (ao : String → Option Nat := fun _ => none) : Prop :=
  ¬ PLive code rd ao obs 0 A

/-- An array outside the entry of a solution of the liveness equations is write-first. -/
theorem writeFirst_of_needClosed {A : String} {code : List LinstrRM} {obs : List String}
    {rd : String → Nat → Option Nat} {ao : String → Option Nat} {L : Nat → List String}
    (hn : NeedClosed code rd ao (fun k r => r ∈ L k) obs) (hA : A ∉ L 0) :
    WriteFirst A code obs rd ao :=
  fun h => hA (pLive_least hn 0 A h)

/-- An array outside the entry list of a certificate that the coalescing check accepts is
    write-first. -/
theorem writeFirst_of_coCfgB {σ : String → String} {A : String} {code : List LinstrRM}
    {obs : List String} {rd : String → Nat → Option Nat} {ao : String → Option Nat}
    {L : Nat → List String} (hc : coCfgB σ code L obs rd ao = true) (hA : A ∉ L 0) :
    WriteFirst A code obs rd ao :=
  writeFirst_of_needClosed ((coCfgB_iff σ code L obs rd ao).mp hc).2.1 hA

/-! ## 2. The decision -/

/-- The positions after the label `lbl`. -/
def jumpL (code : List LinstrRM) (lbl : LLabel) : List Nat :=
  ((findLabelMem lbl code).map (· + 1)).toList

/-- The control-flow successors `CoalesceComplete.SuccA` as a list. -/
def succL (code : List LinstrRM) (k : Nat) : CoArm → List Nat
  | .call _ _ _ | .arr | .seq | .op => [k + 1]
  | .cc lbl => (if constTakenB code k then [] else [k + 1]) ++ jumpL code lbl
  | .goto lbl => jumpL code lbl
  | .bad => []

/-- `succL` lists the successors of `SuccA`. -/
theorem mem_succL {code : List LinstrRM} {k k' : Nat} {a : CoArm} :
    k' ∈ succL code k a ↔ SuccA code k a k' := by
  cases a <;> simp [succL, SuccA, jumpL, JumpTo] <;> grind

/-- The array `A` is live before the position `k` when it is live after the positions `U`. -/
def needPosB (A : String) (code : List LinstrRM) (rd : String → Nat → Option Nat)
    (ao : String → Option Nat) (U : Finset Nat) (k : Nat) : Bool :=
  match code[k]? with
  | some i => (rdArr rd i).contains A
      || (wrArr ao i != some A && (succL code k (armOf i)).any fun k' => decide (k' ∈ U))
  | none => false

/-- One backward pass over the positions of the code. -/
def livePass (A : String) (code : List LinstrRM) (rd : String → Nat → Option Nat)
    (ao : String → Option Nat) (U : Finset Nat) : Finset Nat :=
  (List.range code.length).foldr
    (fun k U => if needPosB A code rd ao U k then insert k U else U) U

/-- The backward passes, until one adds no position. -/
def liveClose (A : String) (code : List LinstrRM) (rd : String → Nat → Option Nat)
    (ao : String → Option Nat) : Nat → Finset Nat → Finset Nat
  | 0, U => U
  | fuel + 1, U =>
      let U' := livePass A code rd ao U
      if U'.card = U.card then U else liveClose A code rd ao fuel U'

/-- The positions before which `A` is live. -/
def livePos (A : String) (code : List LinstrRM) (obs : List String)
    (rd : String → Nat → Option Nat) (ao : String → Option Nat) : Finset Nat :=
  liveClose A code rd ao (code.length + 2) (if A ∈ obs then {code.length} else ∅)

/-- **The decision of `WriteFirst`.** -/
def writeFirstB (A : String) (code : List LinstrRM) (obs : List String)
    (rd : String → Nat → Option Nat := fun _ _ => none)
    (ao : String → Option Nat := fun _ => none) : Bool :=
  decide (0 ∉ livePos A code obs rd ao)

section Decision

variable {A : String} {code : List LinstrRM} {obs : List String}
  {rd : String → Nat → Option Nat} {ao : String → Option Nat}

/-- The condition of a pass is monotone in the live positions. -/
theorem needPosB_mono {U V : Finset Nat} (hUV : U ⊆ V) {k : Nat}
    (h : needPosB A code rd ao U k = true) : needPosB A code rd ao V k = true := by
  unfold needPosB at h ⊢
  grind

/-- A pass over any list of positions only adds positions. -/
theorem subset_foldr_pass (l : List Nat) (U : Finset Nat) :
    U ⊆ l.foldr (fun k U => if needPosB A code rd ao U k then insert k U else U) U := by
  induction l <;> grind

/-- A pass adds every position at which its condition holds. -/
theorem mem_foldr_pass {U : Finset Nat} {k : Nat} (h : needPosB A code rd ao U k = true) :
    ∀ {l : List Nat}, k ∈ l →
      k ∈ l.foldr (fun k U => if needPosB A code rd ao U k then insert k U else U) U := by
  intro l hk
  induction l with
  | nil => simp at hk
  | cons j l ih =>
      have := needPosB_mono (subset_foldr_pass (A := A) (code := code) (rd := rd) (ao := ao) l U) h
      grind

/-- A property closed under the condition of a pass holds after the pass. -/
theorem livePass_invariant (P : Nat → Prop)
    (hP : ∀ U k, k < code.length → (∀ x ∈ U, P x) → needPosB A code rd ao U k = true → P k)
    {U : Finset Nat} (hU : ∀ x ∈ U, P x) : ∀ x ∈ livePass A code rd ao U, P x := by
  unfold livePass
  have hr : ∀ k ∈ List.range code.length, k < code.length := fun k hk => List.mem_range.mp hk
  revert hr
  generalize List.range code.length = l
  intro hr
  induction l <;> grind

/-- A property closed under the condition of a pass holds after the passes. -/
theorem liveClose_invariant (P : Nat → Prop)
    (hP : ∀ U k, k < code.length → (∀ x ∈ U, P x) → needPosB A code rd ao U k = true → P k) :
    ∀ (fuel : Nat) {U : Finset Nat}, (∀ x ∈ U, P x) →
      ∀ x ∈ liveClose A code rd ao fuel U, P x
  | 0, _, hU => hU
  | fuel + 1, U, hU => by
      simp only [liveClose]
      split
      · exact hU
      · exact liveClose_invariant P hP fuel (livePass_invariant P hP hU)

/-- The passes only add positions. -/
theorem subset_liveClose : ∀ (fuel : Nat) (U : Finset Nat),
    U ⊆ liveClose A code rd ao fuel U
  | 0, _ => Finset.Subset.refl _
  | fuel + 1, U => by
      simp only [liveClose]
      split
      · exact Finset.Subset.refl _
      · exact (subset_foldr_pass _ U).trans (subset_liveClose fuel _)

/-- The passes reach a fixed point within the fuel. -/
theorem livePass_liveClose : ∀ (fuel : Nat) {U : Finset Nat},
    (∀ x ∈ U, x ≤ code.length) → code.length + 1 < U.card + fuel →
    livePass A code rd ao (liveClose A code rd ao fuel U) = liveClose A code rd ao fuel U
  | 0, U, hU, hf => by
      have : U.card ≤ (Finset.range (code.length + 1)).card :=
        Finset.card_le_card fun x hx => Finset.mem_range.mpr (Nat.lt_succ_of_le (hU x hx))
      grind
  | fuel + 1, U, hU, hf => by
      have hs : U ⊆ livePass A code rd ao U := subset_foldr_pass _ U
      simp only [liveClose]
      split
      · exact (Finset.eq_of_subset_of_card_le hs (by omega)).symm
      · have := Finset.card_le_card hs
        exact livePass_liveClose fuel
          (livePass_invariant (· ≤ code.length) (fun _ _ hk _ _ => Nat.le_of_lt hk) hU)
          (by omega)

/-- The computed positions are the positions at which `A` is live. -/
theorem mem_livePos_iff {k : Nat} :
    k ∈ livePos A code obs rd ao ↔ PLive code rd ao obs k A := by
  constructor
  · refine liveClose_invariant (fun k => PLive code rd ao obs k A) ?_ _ ?_ k
    · intro U k hk hU h
      unfold needPosB at h
      rw [List.getElem?_eq_getElem hk] at h
      simp only [Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem, bne_iff_ne, ne_eq,
        List.any_eq_true, decide_eq_true_eq] at h
      rcases h with h | ⟨hw, k', hs, hk'⟩
      · exact .read (List.getElem?_eq_getElem hk) h
      · exact .step (List.getElem?_eq_getElem hk) (mem_succL.mp hs) (Ne.symm hw) (hU k' hk')
    · intro x hx
      split at hx
      · rw [Finset.mem_singleton.mp hx]
        exact .obs ‹_›
      · simp at hx
  · have hst : livePass A code rd ao (livePos A code obs rd ao) = livePos A code obs rd ao :=
      livePass_liveClose _ (by grind) (by omega)
    have hmem : ∀ j, j < code.length →
        needPosB A code rd ao (livePos A code obs rd ao) j = true →
        j ∈ livePos A code obs rd ao := by
      intro j hj h
      rw [← hst]
      exact mem_foldr_pass h (List.mem_range.mpr hj)
    intro h
    generalize hr : A = r at h
    induction h with
    | obs ho =>
        subst hr
        exact subset_liveClose _ _ (by simp [ho])
    | @read j i r hi hrd =>
        subst hr
        exact hmem j (List.getElem?_eq_some_iff.mp hi).1 (by simp [needPosB, hi, hrd])
    | @step j j' i r hi hs hw _ ih =>
        subst hr
        refine hmem j (List.getElem?_eq_some_iff.mp hi).1 ?_
        simp only [needPosB, hi, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
          List.any_eq_true, decide_eq_true_eq]
        exact Or.inr ⟨Ne.symm hw, j', mem_succL.mpr hs, ih rfl⟩

/-- **`writeFirstB` decides `WriteFirst`.** -/
theorem writeFirstB_iff : writeFirstB A code obs rd ao = true ↔ WriteFirst A code obs rd ao := by
  simp [writeFirstB, WriteFirst, mem_livePos_iff]

/-- `WriteFirst` is decidable, by `writeFirstB`. -/
instance : Decidable (WriteFirst A code obs rd ao) := decidable_of_iff _ writeFirstB_iff

end Decision

/-! ## 3. An array first mentioned by its zeroing -/

/-- A register operand of a call at an array position is an operand of the call. -/
theorem mem_of_mem_callArrRegs {a : Nat → Option Nat} {x : String} :
    ∀ {j : Nat} {os : List LOperand}, x ∈ callArrRegs a j os → LOperand.reg x ∈ os := by
  intro j os
  induction os generalizing j with
  | nil => simp [callArrRegs]
  | cons o os ih => cases o <;> grind [callArrRegs]

/-- The array names an instruction reads are names of the instruction. -/
theorem rdArr_sub_instrNames {rd : String → Nat → Option Nat} {i : LinstrRM} {r : String}
    (h : r ∈ rdArr rd i) : r ∈ instrNames i.1 := by
  have har : r ∈ arrReads i → r ∈ instrNames i.1 := by
    obtain ⟨w, t⟩ := i
    cases t <;> simp [arrReads] <;>
      simp only [loadStruct?, storeStruct?, storeImmStruct?] <;>
      grind [instrNames, opNames]
  have hcall : ∀ dst f srcs, shadowCall? i.1 = some (dst, f, srcs) →
      r ∈ callArrRegs (rd f) 0 srcs → r ∈ instrNames i.1 := by
    intro dst f srcs hs hr
    rw [eq_callShadow_of_shadowCall? hs]
    simp only [callShadow, instrNames, List.mem_flatMap]
    exact ⟨.reg r, List.mem_append_right _ (mem_of_mem_callArrRegs hr), by simp [opNames]⟩
  unfold rdArr armOf at h
  grind [rdArrA]

/-- A tagged zeroing of `A` reads no array, writes `A` and is followed by the next
    position. -/
theorem zero_facts {A : String} {z : LinstrRM} {w n : Nat} (hz : zeroDst? z = some A)
    (ht : z.2 = .zero w n) (rd : String → Nat → Option Nat) (ao : String → Option Nat) :
    rdArr rd z = [] ∧ wrArr ao z = some A := by
  obtain ⟨wire, tag⟩ := z
  subst ht
  unfold zeroDst? at hz
  split at hz
  · rename_i d opn ss heq
    simp only at heq
    subst heq
    split at hz
    · rename_i ho
      subst ho
      cases hz
      have hs : shadowCall? (LinstrR.Lopn [.reg A] "ZEROARR" ss) = none := by
        simp [shadowCall?]
      simp [rdArr, wrArr, armOf, hs, arrShapeB, zeroStruct?, rdArrA, wrArrA, arrReads, arrWrite]
    · cases hz
  · cases hz

/-- **An array zeroed at the position `p` is write-first** when no instruction in front of
    `p` mentions it or continues past `p`. -/
theorem writeFirst_of_zero {A : String} {code : List LinstrRM} {obs : List String}
    {rd : String → Nat → Option Nat} {ao : String → Option Nat} {p w n : Nat} {z : LinstrRM}
    (hp : code[p]? = some z) (hz : zeroDst? z = some A) (ht : z.2 = .zero w n)
    (hpre : ∀ k i, k < p → code[k]? = some i →
      A ∉ instrNames i.1 ∧ ∀ k', Succ code k i k' → k' ≤ p) :
    WriteFirst A code obs rd ao := by
  obtain ⟨hr, hw⟩ := zero_facts hz ht rd ao
  have hlen : p < code.length := (List.getElem?_eq_some_iff.mp hp).1
  have hn : NeedClosed code rd ao (fun k r => r = A → p < k) obs := by
    refine ⟨fun _ _ _ => hlen, fun k i hi => ⟨fun r hrd hA => ?_, fun k' r hs hne hk' hA => ?_⟩⟩
    · subst hA
      rcases Nat.lt_trichotomy k p with hk | hk | hk
      · exact absurd (rdArr_sub_instrNames hrd) (hpre k i hk hi).1
      · grind
      · exact hk
    · subst hA
      rcases Nat.lt_trichotomy k p with hk | hk | hk
      · have := (hpre k i hk hi).2 k' hs
        have := hk' rfl
        omega
      · grind
      · exact hk
  exact fun h => Nat.not_lt_zero p (pLive_least hn 0 A h rfl)

/-- The check that the first zeroing of `A` carries its zero tag and that no instruction in
    front of it continues past it. -/
def zeroReachB (A : String) (code : List LinstrRM) : Bool :=
  let p := code.findIdx fun i => zeroDst? i == some A
  (match code[p]? with
    | some (_, .zero _ _) => true
    | _ => false)
  && (List.range p).all fun k =>
    match code[k]? with
    | some i => (succL code k (armOf i)).all fun k' => decide (k' ≤ p)
    | none => true

/-- The facts of `zeroFirstB`: the first zeroing of `A` exists, and no instruction in front
    of it mentions `A`. -/
theorem zeroFirstB_spec {A : String} : ∀ {code : List LinstrRM}, zeroFirstB A code = true →
    ∃ z, code[code.findIdx fun i => zeroDst? i == some A]? = some z ∧ zeroDst? z = some A ∧
      ∀ k i, k < (code.findIdx fun i => zeroDst? i == some A) → code[k]? = some i →
        A ∉ instrNames i.1 := by
  intro code h
  induction code with
  | nil => simp [zeroFirstB] at h
  | cons j is ih =>
      by_cases hj : zeroDst? j = some A
      · exact ⟨j, by simp [List.findIdx_cons, hj], hj, by simp [List.findIdx_cons, hj]⟩
      · simp only [zeroFirstB, hj, ite_false] at h
        split at h
        · simp at h
        · rename_i hm
          obtain ⟨z, h1, h2, h3⟩ := ih h
          refine ⟨z, by simpa [List.findIdx_cons, hj] using h1, h2, fun k i hk hi => ?_⟩
          cases k <;> grind

/-- **An array first mentioned by its zeroing is write-first**, when no jump in front of the
    zeroing passes it (`zeroReachB`). -/
theorem zeroFirstB_writeFirst {A : String} {code : List LinstrRM} {obs : List String}
    {rd : String → Nat → Option Nat} {ao : String → Option Nat}
    (h : zeroFirstB A code = true) (hj : zeroReachB A code = true) :
    WriteFirst A code obs rd ao := by
  obtain ⟨⟨wire, tag⟩, hp, hz, hm⟩ := zeroFirstB_spec h
  simp only [zeroReachB, hp, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hj
  cases tag with
  | zero w n =>
      refine writeFirst_of_zero hp hz rfl fun k i hk hi => ⟨hm k i hk hi, fun k' hs => ?_⟩
      have := hj.2 k hk
      simp only [hi, List.all_eq_true, decide_eq_true_eq] at this
      exact this k' (mem_succL.mpr hs)
  | _ => simp at hj

/-- An operation has no successor but the next position. -/
theorem succ_of_isLopn {code : List LinstrRM} {k k' : Nat} {i : LinstrRM} (hi : IsLopn i)
    (h : Succ code k i k') : k' = k + 1 := by
  have hf : flagCondCC? i = none := flagCondCC?_of_isLopn hi
  obtain ⟨d, o, s, he⟩ := hi
  unfold Succ armOf at h
  grind [SuccA]

/-- **On straight code an array first mentioned by its zeroing is write-first.** -/
theorem zeroFirstB_writeFirst_straight {A : String} {code : List LinstrRM} {obs : List String}
    {rd : String → Nat → Option Nat} {ao : String → Option Nat}
    (h : zeroFirstB A code = true) (hs : ∀ i ∈ code, IsLopn i)
    (ht : ∀ i ∈ code, zeroDst? i = some A → ∃ w n, i.2 = .zero w n) :
    WriteFirst A code obs rd ao := by
  obtain ⟨z, hp, hz, hm⟩ := zeroFirstB_spec h
  obtain ⟨w, n, hw⟩ := ht z (List.mem_of_getElem? hp) hz
  refine writeFirst_of_zero hp hz hw fun k i hk hi => ⟨hm k i hk hi, fun k' hs' => ?_⟩
  have := succ_of_isLopn (hs i (List.mem_of_getElem? hi)) hs'
  omega

/-! ## 4. The calls -/

/-- The shape of an array cell: the width of its words and their number. -/
def cellShape (c : ArrCell) : Nat × Nat := (c.1, c.2.1)

/-- The argument lists `os` from the position `j` agree in two states on the positions read:
    at an array position outside `rd` both operands are readable or neither is, and at
    every other position the argument words are equal. -/
def ArgsAgree (aa rd : Nat → Option Nat) (b b' : LstateM) : Nat → List LOperand → Prop
  | _, [] => True
  | j, o :: os =>
      (if (aa j).isSome && (rd j).isNone then
          (argRead aa b' j o).isSome = (argRead aa b j o).isSome
        else argRead aa b' j o = argRead aa b j o)
      ∧ ArgsAgree aa rd b b' (j + 1) os

/-- **The calls of `I` depend on the positions `rd` only.** Every step of `I` is a step of `J`,
    or a call that writes its result to the destination and that `I` takes, to the same
    result, from every state in which the arguments agree on the positions read
    (`ArgsAgree`). The array positions are `aa` and the result lengths are `ao`. -/
def CallReads (I J : Isa) (aa rd : String → Nat → Option Nat) (ao : String → Option Nat) :
    Prop :=
  ∀ (P : LprogM) (i : LinstrRM) (s t : LstateMF), I.step P i s = some t →
    J.step P i s = some t ∨
      ∃ (dst f : String) (srcs : List LOperand) (x : CallRes),
        i.1 = callShadow dst f srcs ∧ t = retRes dst x s ∧
        (∀ s' : LstateMF, ArgsAgree (aa f) (rd f) s.prog.base s'.prog.base 0 srcs →
          I.step P i s' = some (retRes dst x s')) ∧
        x.len = ao f

/-- Operands that agree at all array positions have the same argument words. -/
theorem ArgsAgree.argsRead_eq {aa : Nat → Option Nat} {b b' : LstateM} :
    ∀ {j : Nat} {os : List LOperand}, ArgsAgree aa aa b b' j os →
      argsRead aa b' j os = argsRead aa b j os := by
  intro j os h
  induction os generalizing j with
  | nil => rfl
  | cons o os ih => cases ha : aa j <;> grind [ArgsAgree, argsRead]

/-- Operands that agree at all array positions agree at the positions read. -/
theorem ArgsAgree.of_full {aa rd : Nat → Option Nat} {b b' : LstateM} :
    ∀ {j : Nat} {os : List LOperand}, ArgsAgree aa aa b b' j os → ArgsAgree aa rd b b' j os := by
  intro j os h
  induction os generalizing j with
  | nil => trivial
  | cons o os ih => cases ha : aa j <;> grind [ArgsAgree]

/-- Calls that depend on the positions `rd` only depend on all array positions only. -/
theorem CallReads.full {I J : Isa} {aa rd : String → Nat → Option Nat}
    {ao : String → Option Nat} (h : CallReads I J aa rd ao) : CallReads I J aa aa ao := by
  intro P i s t hs
  rcases h P i s t hs with hx | ⟨dst, f, srcs, x, hi, ht, hf, hl⟩
  · exact Or.inl hx
  · exact Or.inr ⟨dst, f, srcs, x, hi, ht, fun s' ha => hf s' ha.of_full, hl⟩

/-- **Local calls depend on all their array positions.** -/
theorem callReads_of_callLocal {I J : Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (h : I.CallLocal J aa ao) : CallReads I J aa aa ao := by
  intro P i s t hs
  rcases h P i s t hs with hx | ⟨dst, f, srcs, x, hi, ht, hf, hl⟩
  · exact Or.inl hx
  · refine Or.inr ⟨dst, f, srcs, x, hi, ht, fun s' ha => ?_, hl⟩
    have hst := hf P i.2 dst srcs s' rfl ha.argsRead_eq
    rwa [← hi] at hst

/-- The argument words from the position `j`, for `c` operands, with the words of the array
    positions outside `rd` replaced by zeros. -/
def maskWords (aa rd : Nat → Option Nat) : Nat → Nat → List (BitVec 64) → List (BitVec 64)
  | _, 0, vs => vs
  | j, c + 1, vs =>
      let n := (aa j).getD 1
      (if (aa j).isSome && (rd j).isNone then List.replicate n 0 else vs.take n)
        ++ maskWords aa rd (j + 1) c (vs.drop n)

/-- **The result of the summary `pr` depends on the positions `rd` only**: argument words
    that are equal outside the other array positions have equal results. For a linked out
    kernel with the destination outside `rd` this says that the kernel does not read its out
    operand. -/
def ReadsOnly (pr : ProcSummary) (rd : Nat → Option Nat) : Prop :=
  ∀ vs vs', maskWords pr.arrArgs rd 0 pr.arity vs' = maskWords pr.arrArgs rd 0 pr.arity vs →
    pr.result vs' = pr.result vs

/-- The mask of the words from the position `j` at all array positions is the identity. -/
theorem maskWords_full (aa : Nat → Option Nat) :
    ∀ (c j : Nat) (vs : List (BitVec 64)), maskWords aa aa j c vs = vs := by
  intro c
  induction c with
  | zero => intro j vs; rfl
  | succ c ih => intro j vs; cases ha : aa j <;> cases vs <;> simp [maskWords, ih, ha]

/-- The number of argument words of an operand. -/
theorem argRead_length {aa : Nat → Option Nat} {b : LstateM} {j : Nat} {o : LOperand}
    {v : List (BitVec 64)} (h : argRead aa b j o = some v) : v.length = (aa j).getD 1 := by
  unfold argRead at h
  cases ha : aa j <;> cases o <;> simp_all <;> grind

/-- Arguments that agree on the positions read have words with the same mask. -/
theorem ArgsAgree.mask {aa rd : Nat → Option Nat} {b b' : LstateM} :
    ∀ {os : List LOperand} {j : Nat} {vs : List (BitVec 64)}, ArgsAgree aa rd b b' j os →
      argsRead aa b j os = some vs →
      ∃ vs', argsRead aa b' j os = some vs' ∧
        maskWords aa rd j os.length vs' = maskWords aa rd j os.length vs := by
  intro os
  induction os with
  | nil => intro j vs _ h; exact ⟨vs, h, rfl⟩
  | cons o os ih =>
      intro j vs ha h
      simp only [argsRead, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, r, hr, rfl⟩ := h
      obtain ⟨r', hr', hm⟩ := ih ha.2 hr
      obtain ⟨v', hv', hhead⟩ : ∃ v', argRead aa b' j o = some v' ∧
          (((aa j).isSome && (rd j).isNone) = false → v' = v) := by
        have := ha.1
        split at this
        · rw [hv] at this
          obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.mp this
          exact ⟨v', hv', by grind⟩
        · exact ⟨v, this.trans hv, fun _ => rfl⟩
      refine ⟨v' ++ r', by simp [argsRead, hv', hr'], ?_⟩
      have hl := argRead_length hv
      have hl' := argRead_length hv'
      simp only [List.length_cons, maskWords]
      rw [List.drop_left' hl', List.drop_left' hl, List.take_left' hl', List.take_left' hl, hm]
      grind

/-- **The instruction set with a table of procedures** whose results depend on the positions
    `rd` only has calls that depend on these positions only. -/
theorem withProcs_callReads (T : ProcTable) {rd : String → Nat → Option Nat}
    (hk : ∀ f pr, T f = some pr → pr.Kinded)
    (hr : ∀ f pr, T f = some pr → ReadsOnly pr (rd f)) :
    CallReads (x86Isa.withProcs T) x86Isa (procArrArgs T) rd (procOut T) := by
  intro P i s t h
  cases hq : procCall? T i.1 with
  | none => exact Or.inl (by rwa [x86Isa.withProcs_step_of_none T P i s hq] at h)
  | some q =>
      obtain ⟨pr, dst, srcs⟩ := q
      right
      simp only [procCall?, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hq
      obtain ⟨⟨dst', f, srcs'⟩, hsh, pr', hf, hpr⟩ := hq
      simp only [Prod.mk.injEq] at hpr
      obtain ⟨rfl, rfl, rfl⟩ := hpr
      obtain ⟨wire, tag⟩ := i
      obtain rfl : wire = callShadow dst' f srcs' := eq_callShadow_of_shadowCall? hsh
      rw [x86Isa.withProcs_step_callShadow T hf P dst' srcs' tag s] at h
      unfold procStep at h
      split at h
      · rename_i hlen
        obtain ⟨vs, hvs, hres⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hres
        have haa : procArrArgs T f = pr'.arrArgs := by simp only [procArrArgs, hf]
        refine ⟨dst', f, srcs', x, rfl, rfl, fun s' ha => ?_, ?_⟩
        · rw [haa] at ha
          obtain ⟨vs', hvs', hm⟩ := ha.mask hvs
          rw [x86Isa.withProcs_step_callShadow T hf P dst' srcs' tag s', procStep]
          simp [hlen, hvs', hr f pr' hf vs vs' (by rwa [← hlen]), hx]
        · rw [ProcSummary.len_of_result (hk f pr' hf) hx, procOut, hf, Option.bind_some]
      · cases h

/-! ## 5. One step -/

/-- The renaming of the array positions by the identity is the identity. -/
theorem renArr_id (i : LinstrRM) : renArr id i = i := by
  obtain ⟨w, tag⟩ := i
  have hA : ∀ ss : List LOperand, ss.map (renOpA id) = ss := fun ss =>
    (List.map_congr_left fun o _ => by cases o <;> rfl).trans (List.map_id ss)
  have hR : ∀ ss : List LOperand, ss.map (renOpR id) = ss := fun ss =>
    (List.map_congr_left fun o _ => by cases o <;> rfl).trans (List.map_id ss)
  have hC : renCallW id w = w := by
    unfold renCallW
    split
    · rename_i dst f srcs hs
      rw [hR, id_eq]
      exact (eq_callShadow_of_shadowCall? hs).symm
    · rfl
  cases tag <;> simp only [renArr, renLoad, renStore, renZero, renStoreImm] <;> grind

/-- A code of admitted shapes under a renaming has admitted shapes under the identity, at
    all array positions. -/
theorem classOK_id {σ : String → String} {code : List LinstrRM}
    {aa aa' : String → Nat → Option Nat} {ao : String → Option Nat}
    (h : ClassOK σ code aa ao) : ClassOK id code aa' ao := by
  intro k i hi
  have hc := h k i hi
  have hfix : ∀ (a : Nat → Option Nat) (os : List LOperand) (j : Nat),
      callOpsFix id a j os = true := by
    intro a os
    induction os with
    | nil => simp [callOpsFix]
    | cons o os ih => intro j; cases o <;> simp [callOpsFix, ih]
  revert hc
  cases armOf i <;> simp only [ClassA, renArr_id] <;> grind

/-- A code that the coalescing check accepts has admitted shapes under the identity. -/
theorem classOK_of_coCfgB {σ : String → String} {code : List LinstrRM} {L : Nat → List String}
    {obs : List String} {aa aa' : String → Nat → Option Nat} {ao : String → Option Nat}
    (h : coCfgB σ code L obs aa ao = true) : ClassOK id code aa' ao :=
  classOK_id ((coCfgB_iff σ code L obs aa ao).mp h).1

/-- A step of `lsemStepMem` of an instruction that writes no array leaves the arrays. -/
theorem lsemStepMem_larr_none {i : LinstrRM} {s t : LstateM} (hw : arrWrite i = none)
    (h : lsemStepMem i s = some t) : t.larr = s.larr := by
  unfold lsemStepMem at h
  repeat' split at h
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp h; rfl)
    | (cases h; rfl)
    | (cases h; done)
    | simp_all [arrWrite]

/-- A step of the flag machine of an instruction that writes no array leaves the arrays. -/
theorem evalInstrPMemF_larr_none {P : LprogM} {i : LinstrRM} {s t : LstateMF}
    (hw : arrWrite i = none) (h : evalInstrPMemF P i s = some t) :
    t.prog.base.larr = s.prog.base.larr := by
  have hL : ∀ p, evalInstrPMemL P i s.prog = some p → p.base.larr = s.prog.base.larr := by
    intro p hp
    unfold evalInstrPMemL at hp
    repeat' split at hp
    all_goals first
      | (cases hp; rfl)
      | exact JasminLsemExportTransfer.evalJumpMem_larr _ _ _ _ hp
      | (obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hp; exact lsemStepMem_larr_none hw hb)
      | cases hp
  unfold evalInstrPMemF at h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | (cases h; exact (withALUFlags_larr ..).trans (hL _ ‹_›))
    | (obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
       exact JasminLsemExportTransfer.evalJumpMem_larr _ _ _ _ hp)
    | (obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
       first
        | (unfold carryStep at hb; grind [LstateM.setReg, LstateM.nextPc])
        | (unfold wideStep at hb; grind [LstateM.setReg, LstateM.nextPc]))
    | cases h

/-- Two states whose arrays have the same shapes step to two states whose arrays have the
    same shapes. -/
theorem lsemStepMem_shapes {i : LinstrRM} {s s' t t' : LstateM}
    (hS : ∀ r, cellShape (s'.larr r) = cellShape (s.larr r))
    (h : lsemStepMem i s = some t) (h' : lsemStepMem i s' = some t') :
    ∀ r, cellShape (t'.larr r) = cellShape (t.larr r) := by
  cases hw : arrWrite i with
  | none =>
      intro r
      rw [lsemStepMem_larr_none hw h, lsemStepMem_larr_none hw h', hS r]
  | some d =>
      obtain ⟨w, tag⟩ := i
      intro r
      cases tag <;> simp only [arrWrite, Option.map_eq_some_iff, reduceCtorEq] at hw
      case store =>
        obtain ⟨⟨d', b, x, v⟩, hs, rfl⟩ := hw
        simp only [lsemStepMem, hs] at h h'
        split at h <;> cases h
        split at h' <;> cases h'
        simp only [LstateM.larr_nextPc, LstateM.larr_setArr]
        split
        · rfl
        · exact hS r
      case zero =>
        simp only [lsemStepMem, hw, Option.some.injEq] at h h'
        grind [cellShape, LstateM.setArr, LstateM.nextPc]
      case storeImm =>
        obtain ⟨⟨d', b, v, k⟩, hs, rfl⟩ := hw
        simp only [lsemStepMem, hs] at h h'
        split at h <;> cases h
        split at h' <;> cases h'
        simp only [LstateM.larr_nextPc, LstateM.larr_setArr]
        split
        · rfl
        · exact hS r

/-- **A step of the flag machine keeps equal shapes** at an instruction of an admitted
    shape. -/
theorem evalInstrPMemF_shapes {P : LprogM} {code : List LinstrRM} {i : LinstrRM}
    {aa : String → Nat → Option Nat} {ao : String → Option Nat} {s s' t t' : LstateMF}
    (hc : ClassA id code aa ao i (armOf i))
    (hS : ∀ r, cellShape (s'.prog.base.larr r) = cellShape (s.prog.base.larr r))
    (h : evalInstrPMemF P i s = some t) (h' : evalInstrPMemF P i s' = some t') :
    ∀ r, cellShape (t'.prog.base.larr r) = cellShape (t.prog.base.larr r) := by
  cases hsh : arrShapeB i with
  | false =>
      intro r
      have hw := arrWrite_of_arrShapeB hsh
      rw [evalInstrPMemF_larr_none hw h, evalInstrPMemF_larr_none hw h', hS r]
  | true =>
      have hn : shadowCall? i.1 = none := by
        by_contra hne
        rw [evalInstrPMemF_shadowCall _ i s hne] at h
        cases h
      have harm : armOf i = .arr := by simp [armOf, hn, hsh]
      rw [harm] at hc
      have hp := hc.1
      simp only [plainArrB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
      obtain ⟨⟨⟨⟨⟨hl, h1⟩, h2⟩, hk⟩, hw⟩, ha⟩ := hp
      have key : ∀ {u v : LstateMF}, evalInstrPMemF P i u = some v →
          ∃ b, lsemStepMem i u.prog.base = some b ∧ v.prog.base.larr = b.larr := by
        intro u v huv
        have hI := isLopnB_isLopn hl
        unfold evalInstrPMemF at huv
        simp only [h1, h2, flagCondCC?_of_isLopn hI] at huv
        rw [evalInstrPMemL_lopn _ _ _ hI] at huv
        cases hb : lsemStepMem i u.prog.base with
        | none => simp [hb, hk, hw] at huv
        | some b =>
            simp only [hb, Option.map_some, Option.some.injEq] at huv
            subst huv
            exact ⟨b, rfl, withALUFlags_larr ..⟩
      obtain ⟨b, hb, e⟩ := key h
      obtain ⟨b', hb', e'⟩ := key h'
      rw [e, e']
      exact lsemStepMem_shapes hS hb hb'

/-- Operands whose arrays agree on the positions read, and have the same shapes at the
    other array positions, agree on the positions read. -/
theorem argsAgree_of_rel {aa rd : Nat → Option Nat} {b b' : LstateM} (hreg : b'.reg = b.reg)
    (hS : (∀ r, cellShape (b'.larr r) = cellShape (b.larr r)) ∨ rd = aa) :
    ∀ {j : Nat} {os : List LOperand},
      (∀ x ∈ callArrRegs rd j os, b'.larr x = b.larr x) → ArgsAgree aa rd b b' j os := by
  intro j os
  induction os generalizing j with
  | nil => exact fun _ => trivial
  | cons o os ih =>
      intro hv
      refine ⟨?_, ih fun x hx => hv x (by cases o <;> grind [callArrRegs])⟩
      cases ha : aa j with
      | none => simp [argRead, ha, hreg]
      | some n =>
          cases o with
          | reg x =>
              cases hd : rd j with
              | none =>
                  rcases hS with hS | rfl
                  · have := hS x
                    simp only [cellShape, Prod.mk.injEq] at this
                    simp [argRead, ha, LstateM.getArr]
                    grind
                  · simp [ha] at hd
              | some m =>
                  have := hv x (by simp [callArrRegs, hd])
                  simp only [ha, Option.isSome_some, Option.isNone_some, Bool.and_false,
                    Bool.false_eq_true, ite_false, argRead]
                  unfold LstateM.getArr
                  rw [this]
          | _ => simp [argRead, ha]

/-- The liveness equations have a solution by lists, the least one. -/
theorem exists_liveList (code : List LinstrRM) (rd : String → Nat → Option Nat)
    (ao : String → Option Nat) (obs : List String) :
    ∃ L : Nat → List String, ∀ k r, r ∈ L k ↔ PLive code rd ao obs k r := by
  classical
  refine ⟨fun k => (obs ++ code.flatMap (rdArr rd)).filter fun r =>
    decide (PLive code rd ao obs k r), fun k r => ?_⟩
  simp only [List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
  intro h
  induction h <;> grind

/-! ## 6. The runs -/

/-- **Two final states agree on the observed names `obs`**: they have equal registers, word
    memory, flags and function, and their arrays are equal on `obs`. -/
structure AgreeOn (obs : List String) (t t' : LstateMF) : Prop where
  /-- The registers, the word memory, the carry and overflow flags and the observed arrays. -/
  base : CoRel id obs t.prog.base t'.prog.base
  /-- The function. -/
  lfn : t'.prog.lfn = t.prog.lfn
  /-- The zero flag. -/
  zf : t'.zf = t.zf

/-- Agreement on the observed names is transitive. -/
theorem AgreeOn.trans {obs : List String} {a b c : LstateMF} (h : AgreeOn obs a b)
    (h' : AgreeOn obs b c) : AgreeOn obs a c :=
  ⟨⟨h'.base.reg.trans h.base.reg, h'.base.mem.trans h.base.mem, h'.base.cf.trans h.base.cf,
    h'.base.of.trans h.base.of, fun r hr => (h'.base.arr r hr).trans (h.base.arr r hr)⟩,
    h'.lfn.trans h.lfn, h'.zf.trans h.zf⟩

/-- The relation of the coalescing at the identity is symmetric. -/
theorem coRel_id_symm {L : List String} {s s' : LstateM} (h : CoRel id L s s') :
    CoRel id L s' s :=
  ⟨h.reg.symm, h.mem.symm, h.cf.symm, h.of.symm, fun r hr => (h.arr r hr).symm⟩

/-- **A halting run is matched** from a state that agrees on the names live under `rd`, and
    has arrays of the same shapes when `rd` omits array positions, by a halting run. -/
theorem lsemFuelMemF_sim {I : Isa} {aa rd : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I) (hcl : CallReads I x86Isa aa rd ao)
    {fn : String} {code : List LinstrRM} (hcls : ClassOK id code rd ao) {obs : List String}
    {L : Nat → List String} (hL : ∀ k r, r ∈ L k ↔ PLive code rd ao obs k r) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, s.prog.lfn = fn → s.prog.base.lpc ≤ code.length →
      GuardInv code s → CoRel id (L s.prog.base.lpc) s.prog.base s'.prog.base →
      s'.prog.lfn = s.prog.lfn → s'.zf = s.zf →
      ((∀ r, cellShape (s'.prog.base.larr r) = cellShape (s.prog.base.larr r)) ∨ rd = aa) →
      I.lsemFuelMemF (singletonProgM fn code) fuel s = some t →
      ∃ t', I.lsemFuelMemF (singletonProgM fn code) fuel s' = some t' ∧ AgreeOn obs t t' := by
  have hn : NeedClosed code rd ao (fun k r => r ∈ L k) obs := by
    simp only [hL]
    exact pLive_needClosed code rd ao obs
  have hco : coCfgB id code L obs rd ao = true :=
    (coCfgB_iff id code L obs rd ao).mpr ⟨hcls, hn, fun _ _ _ _ _ _ _ hne => hne⟩
  have hmap : code.map (renArr id) = code :=
    (List.map_congr_left fun i _ => renArr_id i).trans (List.map_id code)
  have hfetch : ∀ {s s' : LstateMF}, s.prog.lfn = fn →
      CoRel id (L s.prog.base.lpc) s.prog.base s'.prog.base → s'.prog.lfn = s.prog.lfn →
      findInstrMem (singletonProgM fn code) s.prog = code[s.prog.base.lpc]?
        ∧ findInstrMem (singletonProgM fn code) s'.prog = code[s.prog.base.lpc]? := by
    intro s s' hf hR hfn
    exact ⟨findInstrMem_singleton fn code s.prog hf, by
      rw [findInstrMem_singleton fn code s'.prog (hfn.trans hf), coRel_lpc hR]⟩
  have hhalt : ∀ {s s' : LstateMF}, s.prog.base.lpc ≤ code.length →
      code[s.prog.base.lpc]? = none → CoRel id (L s.prog.base.lpc) s.prog.base s'.prog.base →
      CoRel id obs s.prog.base s'.prog.base := by
    intro s s' hpc hb hR
    have hlen : s.prog.base.lpc = code.length := by
      have := List.getElem?_eq_none_iff.mp hb
      omega
    rw [hlen] at hR
    exact hR.mono hn.1
  intro fuel
  induction fuel with
  | zero =>
      intro s s' t hf hpc hg hR hfn hz hS h
      obtain ⟨e1, e2⟩ := hfetch hf hR hfn
      unfold Isa.lsemFuelMemF at h ⊢
      rw [e1] at h
      rw [e2]
      cases hb : code[s.prog.base.lpc]? with
      | none =>
          simp only [hb, Option.some.injEq] at h ⊢
          subst h
          exact ⟨_, rfl, hhalt hpc hb hR, hfn, hz⟩
      | some i => simp [hb] at h
  | succ fuel ih =>
      intro s s' t hf hpc hg hR hfn hz hS h
      obtain ⟨e1, e2⟩ := hfetch hf hR hfn
      unfold Isa.lsemFuelMemF at h ⊢
      rw [e1] at h
      rw [e2]
      cases hb : code[s.prog.base.lpc]? with
      | none =>
          simp only [hb, Option.some.injEq] at h ⊢
          subst h
          exact ⟨_, rfl, hhalt hpc hb hR, hfn, hz⟩
      | some i =>
          simp only [hb] at h ⊢
          have hlt := (List.getElem?_eq_some_iff.mp hb).1
          cases he : I.step (singletonProgM fn code) i s with
          | none => simp [he] at h
          | some u =>
              simp only [he] at h
              rcases hcl _ i s u he with hx | ⟨dst, f, srcs, x, hi, rfl, hfwd, hlen⟩
              · obtain ⟨u', hu', hRu, hfu, hfs, hzu, hleu⟩ := evalInstrPMemF_coalesce
                  (coCfgB_instr hco hb) hlt (takenAt_of_guardInv hg hb) hR hfn hz hx
                rw [hmap, renArr_id] at hu'
                simp only [hle _ _ _ _ hu']
                exact ih (hfs.trans hf) hleu (guardInv_step hg hb hx) hRu hfu hzu
                  (hS.imp_left fun hS => evalInstrPMemF_shapes (hcls _ _ hb) hS hx hu') h
              · have harm : armOf i = .call dst f srcs := by
                  simp [armOf, hi, shadowCall?_callShadow]
                have hag : ArgsAgree (aa f) (rd f) s.prog.base s'.prog.base 0 srcs :=
                  argsAgree_of_rel hR.reg (hS.imp_right fun h => congrFun h f) fun y hy =>
                    hR.arr y ((hn.2 _ _ hb).1 y (by simpa [rdArr, harm, rdArrA] using hy))
                simp only [hfwd s' hag]
                have hafter : ∀ r ∈ L (s.prog.base.lpc + 1), some r ≠ wrArr ao i →
                    s'.prog.base.larr r = s.prog.base.larr r := fun r hr hw =>
                  hR.arr r ((hn.2 _ _ hb).2 _ r (by simp [Succ, harm, SuccA]) hw hr)
                refine ih ((LprogIsa.lfn_retRes dst x s).trans hf)
                  (by rw [LprogIsa.lpc_retRes]; exact hlt) (guardInv_retRes hg hb hi) ?_
                  (by rw [LprogIsa.lfn_retRes, LprogIsa.lfn_retRes]; exact hfn)
                  (by cases x <;> exact hz) ?_ h
                · rw [LprogIsa.lpc_retRes]
                  cases x with
                  | word v =>
                      exact coRel_nextPc (coRel_setReg
                        ⟨hR.reg, hR.mem, hR.cf, hR.of, fun r hr => hafter r hr
                          (by simp [wrArr, harm, wrArrA, ← hlen, CallRes.len])⟩ dst v)
                  | arr a =>
                      refine ⟨?_, hR.mem, hR.cf, hR.of, fun r hr => ?_⟩
                      · simp [retArr, hR.reg]
                      · simp only [LprogIsa.retRes_arr, retArr, LstateM.nextPc, LstateM.setArr,
                          id_eq]
                        split
                        · rfl
                        · exact hafter r hr (by
                            simpa [wrArr, harm, wrArrA, ← hlen, CallRes.len])
                · refine hS.imp_left fun hS r => ?_
                  cases x with
                  | word v => simpa [retWord] using hS r
                  | arr a =>
                      simp only [LprogIsa.retRes_arr, retArr, LstateM.nextPc, LstateM.setArr]
                      split
                      · rfl
                      · exact hS r

/-- Two runs from states that agree on the names live under `rd` halt alike and agree on
    the observed names. -/
theorem lsemFuelMemF_rel {I : Isa} {aa rd : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I) (hcl : CallReads I x86Isa aa rd ao)
    {fn : String} {code : List LinstrRM} (hcls : ClassOK id code rd ao) {obs : List String}
    {L : Nat → List String} (hL : ∀ k r, r ∈ L k ↔ PLive code rd ao obs k r) (fuel : Nat)
    {s s' : LstateMF} (hf : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 0)
    (hR : CoRel id (L 0) s.prog.base s'.prog.base) (hfn : s'.prog.lfn = s.prog.lfn)
    (hz : s'.zf = s.zf)
    (hS : (∀ r, cellShape (s'.prog.base.larr r) = cellShape (s.prog.base.larr r)) ∨ rd = aa) :
    Option.Rel (AgreeOn obs) (I.lsemFuelMemF (singletonProgM fn code) fuel s)
      (I.lsemFuelMemF (singletonProgM fn code) fuel s') := by
  have hpc' : s'.prog.base.lpc = 0 := (coRel_lpc hR).trans hpc
  have fwd := fun t => lsemFuelMemF_sim (t := t) hle hcl hcls hL fuel hf (by omega)
    (guardInv_zero code hpc) (by rw [hpc]; exact hR) hfn hz hS
  have bwd := fun t => lsemFuelMemF_sim (t := t) hle hcl hcls hL fuel (hfn.trans hf) (by omega)
    (guardInv_zero code hpc') (by rw [hpc']; exact coRel_id_symm hR) hfn.symm hz.symm
    (hS.imp_left fun h r => (h r).symm)
  cases h : I.lsemFuelMemF (singletonProgM fn code) fuel s with
  | some t =>
      obtain ⟨t', ht', hag⟩ := fwd t h
      rw [ht']
      exact .some hag
  | none =>
      cases h' : I.lsemFuelMemF (singletonProgM fn code) fuel s' with
      | some t' =>
          obtain ⟨t, ht, -⟩ := bwd t' h'
          rw [h] at ht
          cases ht
      | none => exact .none

/-- The state `s` with the arrays `M`. -/
def withArrs (s : LstateMF) (M : String → ArrCell) : LstateMF :=
  { s with prog := { s.prog with base := { s.prog.base with larr := M } } }

/-- **Runs do not observe the entry contents of write-first arrays.** Let the calls of `I`
    depend on the positions `rd` only, let `code` be of admitted shapes, and let every name of
    `As` be write-first at `rd`. Let the arrays `M` equal those of `s` off `As`, and have
    their shape at every name of `As` that is not write-first at all the array positions
    `aa` (an array first written as the out operand of a call). Then, at every fuel, the runs
    from `s` and from `s` with the arrays `M` halt alike, with equal registers, word memory
    and flags and equal arrays on the observed names `obs`. -/
theorem lsemFuelMemF_congr_writeFirst {I : Isa} {aa rd : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I) (hcl : CallReads I x86Isa aa rd ao)
    {σ : String → String} {fn : String} {code : List LinstrRM} (hcls : ClassOK σ code aa ao)
    {obs As : List String} (hwf : ∀ A ∈ As, WriteFirst A code obs rd ao) {s : LstateMF}
    (hf : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 0) {M : String → ArrCell}
    (hM : ∀ r, r ∉ As → M r = s.prog.base.larr r)
    (hshape : ∀ A ∈ As, WriteFirst A code obs aa ao ∨
      cellShape (M A) = cellShape (s.prog.base.larr A))
    (fuel : Nat) :
    Option.Rel (AgreeOn obs) (I.lsemFuelMemF (singletonProgM fn code) fuel s)
      (I.lsemFuelMemF (singletonProgM fn code) fuel (withArrs s M)) := by
  classical
  obtain ⟨Lr, hLr⟩ := exists_liveList code rd ao obs
  obtain ⟨La, hLa⟩ := exists_liveList code aa ao obs
  -- the intermediate state takes `M` at the arrays whose shape a run observes
  let N : String → ArrCell := fun r =>
    if PLive code aa ao obs 0 r then M r else s.prog.base.larr r
  have h₁ := lsemFuelMemF_rel hle hcl (classOK_id hcls) hLr fuel (s := s) (s' := withArrs s N)
    hf hpc ⟨rfl, rfl, rfl, rfl, fun r hr => by
      have := hM r fun hA => hwf r hA ((hLr 0 r).mp hr)
      grind [withArrs]⟩ rfl rfl (Or.inl fun r => by
      by_cases hA : r ∈ As
      · have := hshape r hA
        grind [withArrs, WriteFirst]
      · grind [withArrs])
  have h₂ := lsemFuelMemF_rel hle hcl.full (classOK_id hcls) hLa fuel (s := withArrs s N)
    (s' := withArrs s M) hf hpc ⟨rfl, rfl, rfl, rfl, fun r hr => by
      have := (hLa 0 r).mp hr
      grind [withArrs]⟩ rfl rfl (Or.inr rfl)
  revert h₁ h₂
  generalize I.lsemFuelMemF (singletonProgM fn code) fuel s = a
  generalize I.lsemFuelMemF (singletonProgM fn code) fuel (withArrs s N) = b
  generalize I.lsemFuelMemF (singletonProgM fn code) fuel (withArrs s M) = c
  intro h₁ h₂
  cases h₁ with
  | none => exact h₂
  | some h => cases h₂ with
    | some h' => exact .some (h.trans h')

/-- **Entry independence at a table of linked procedures**: `lsemFuelMemF_congr_writeFirst`
    at `x86Isa.withProcs T`, for summaries of their declared result kinds whose results
    depend on the positions `rd` only. -/
theorem lsemFuelMemF_congr_writeFirst_procs (T : ProcTable)
    {rd : String → Nat → Option Nat} (hk : ∀ f pr, T f = some pr → pr.Kinded)
    (hr : ∀ f pr, T f = some pr → ReadsOnly pr (rd f)) {σ : String → String} {fn : String}
    {code : List LinstrRM} (hcls : ClassOK σ code (procArrArgs T) (procOut T))
    {obs As : List String} (hwf : ∀ A ∈ As, WriteFirst A code obs rd (procOut T))
    {s : LstateMF} (hf : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 0) {M : String → ArrCell}
    (hM : ∀ r, r ∉ As → M r = s.prog.base.larr r)
    (hshape : ∀ A ∈ As, WriteFirst A code obs (procArrArgs T) (procOut T) ∨
      cellShape (M A) = cellShape (s.prog.base.larr A))
    (fuel : Nat) :
    Option.Rel (AgreeOn obs)
      ((x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn code) fuel s)
      ((x86Isa.withProcs T).lsemFuelMemF (singletonProgM fn code) fuel (withArrs s M)) :=
  lsemFuelMemF_congr_writeFirst (x86Isa.withProcs_stepLe (x86Isa_refusesProcs T))
    (withProcs_callReads T hk hr) hcls hwf hf hpc hM hshape fuel

/-- **Entry independence without calls**: at the flag machine the entry contents and the
    shapes of write-first arrays are not observed. -/
theorem lsemFuelMemF_congr_writeFirst_noCalls {σ : String → String} {fn : String}
    {code : List LinstrRM} (hcls : ClassOK σ code (fun _ _ => none) (fun _ => none))
    {obs As : List String} (hwf : ∀ A ∈ As, WriteFirst A code obs)
    {s : LstateMF} (hf : s.prog.lfn = fn) (hpc : s.prog.base.lpc = 0) {M : String → ArrCell}
    (hM : ∀ r, r ∉ As → M r = s.prog.base.larr r) (fuel : Nat) :
    Option.Rel (AgreeOn obs) (lsemFuelMemF (singletonProgM fn code) fuel s)
      (lsemFuelMemF (singletonProgM fn code) fuel (withArrs s M)) := by
  rw [← x86Isa_lsemFuelMemF]
  exact lsemFuelMemF_congr_writeFirst (Isa.StepLe.refl x86Isa)
    (callReads_of_callLocal (Isa.CallLocal.refl x86Isa fun _ _ => none)) hcls hwf hf hpc hM
    (fun A hA => Or.inl (hwf A hA)) fuel

/-- **Every summary depends only on all its array positions.** -/
theorem readsOnly_full (pr : ProcSummary) : ReadsOnly pr pr.arrArgs := by
  intro vs vs' h
  rw [maskWords_full, maskWords_full] at h
  rw [h]

/-! ## 7. Fresh roots of the export -/

/-- The export of an array zeroing starts with the tagged zeroing of its root. -/
theorem exportR_zero_code {nArgs : Nat} {fn : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackZero w n) = .stackArr w n)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.stackZero w n)))
    (k : NFProg jasminDialect (.stackArr w n :: Γ) ts) {d l : Nat} {I : LprogIsa.IsaData}
    {r : Exported}
    (h : exportR nArgs fn (.var ⟨JasminOp.stackZero w n, heq, args⟩ k) d l I = some r) :
    ∃ (z : LinstrRM) (rest : List LinstrRM), r.code = z :: rest ∧
      zeroDst? z = some (regName d) ∧ z.2 = .zero w n := by
  simp only [exportR, Option.map_eq_some_iff] at h
  obtain ⟨rk, -, rfl⟩ := h
  simp only [Exported.prepend, bindOps, straightOpsMem_zero]
  exact ⟨_, _, rfl, by simp [zeroDst?, opToLinstrR], rfl⟩

/-- A name that the prefix does not mention and the code zeroes first is zeroed first in
    the whole. -/
theorem zeroFirstB_append {A : String} {pre is : List LinstrRM}
    (hpre : ∀ i ∈ pre, A ∉ instrNames i.1) (h : zeroFirstB A is = true) :
    zeroFirstB A (pre ++ is) = true := by
  induction pre <;> grind [zeroFirstB]

/-- **The export of an array zeroing zeroes its fresh root before any other mention**: behind
    every prefix that does not mention the root `regName d`, `zeroFirstB` accepts it. An
    array literal is exported as this zeroing followed by its stores. -/
theorem zeroFirstB_exportR_fresh {nArgs : Nat} {fn : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackZero w n) = .stackArr w n)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.stackZero w n)))
    (k : NFProg jasminDialect (.stackArr w n :: Γ) ts) {d l : Nat} {I : LprogIsa.IsaData}
    {r : Exported}
    (h : exportR nArgs fn (.var ⟨JasminOp.stackZero w n, heq, args⟩ k) d l I = some r)
    {pre : List LinstrRM} (hpre : ∀ i ∈ pre, regName d ∉ instrNames i.1) :
    zeroFirstB (regName d) (pre ++ r.code) = true := by
  obtain ⟨z, rest, hc, hz, -⟩ := exportR_zero_code heq args k h
  exact zeroFirstB_append hpre (by simp [hc, zeroFirstB, hz])

/-- **The fresh root of an exported array zeroing is write-first** behind a straight prefix
    that does not mention it, whatever loops, branches and calls follow. -/
theorem writeFirst_exportR_fresh {nArgs : Nat} {fn : String} {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.stackZero w n) = .stackArr w n)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.stackZero w n)))
    (k : NFProg jasminDialect (.stackArr w n :: Γ) ts) {d l : Nat} {I : LprogIsa.IsaData}
    {r : Exported}
    (h : exportR nArgs fn (.var ⟨JasminOp.stackZero w n, heq, args⟩ k) d l I = some r)
    {pre : List LinstrRM} (hpre : ∀ i ∈ pre, regName d ∉ instrNames i.1)
    (hs : ∀ i ∈ pre, IsLopn i) {obs : List String} {rd : String → Nat → Option Nat}
    {ao : String → Option Nat} :
    WriteFirst (regName d) (pre ++ r.code) obs rd ao := by
  obtain ⟨z, rest, hc, hz, ht⟩ := exportR_zero_code heq args k h
  refine writeFirst_of_zero (p := pre.length) (z := z) (by simp [hc]) hz ht fun q i hq hi => ?_
  rw [List.getElem?_append_left hq] at hi
  have hm := List.mem_of_getElem? hi
  refine ⟨hpre i hm, fun q' hq' => ?_⟩
  have := succ_of_isLopn (hs i hm) hq'
  omega

/-! ## 8. Two instances -/

/-- A code that zeroes the array `a` of two words and then reads its cell `0`. -/
def zeroThenRead : List LinstrRM :=
  [(.Lopn [.reg "a"] "ZEROARR" [.imm 2, .imm 64], .zero 64 2),
   (.Lopn [.reg "i"] (withWidthTag 64 "MOV") [.imm 0], .reg none),
   (.Lopn [.reg "d"] "LOADIDX" [.arrIdx "a" "i" 8], .load 64 2)]

/-- The array of `zeroThenRead` is first mentioned by its zeroing and is write-first. -/
theorem zeroThenRead_writeFirst : WriteFirst "a" zeroThenRead [] :=
  zeroFirstB_writeFirst (by decide +kernel) (by decide +kernel)

/-- `zeroThenRead` halts from the empty entry state. -/
theorem zeroThenRead_halts :
    (lsemFuelMemF (singletonProgM "f" zeroThenRead) 3
      { prog := { base := {}, lfn := "f" }, zf := false }).isSome = true := by
  decide +kernel

/-- **An array zeroed and then read**: the run of `zeroThenRead` from every entry state does
    not observe the cell that `a` holds at entry. -/
theorem zeroThenRead_congr {s : LstateMF} (hf : s.prog.lfn = "f") (hpc : s.prog.base.lpc = 0)
    {M : String → ArrCell} (hM : ∀ r, r ≠ "a" → M r = s.prog.base.larr r) (fuel : Nat) :
    Option.Rel (AgreeOn []) (lsemFuelMemF (singletonProgM "f" zeroThenRead) fuel s)
      (lsemFuelMemF (singletonProgM "f" zeroThenRead) fuel (withArrs s M)) :=
  lsemFuelMemF_congr_writeFirst_noCalls (As := ["a"])
    (classOK_of_coCfgB (σ := id) (aa := fun _ _ => none) (obs := [])
      (L := fun k => if k = 1 ∨ k = 2 then ["a"] else []) (by decide +kernel))
    (by simpa using zeroThenRead_writeFirst) hf hpc (by simpa using hM) fuel

/-- A table of two linked procedures: `fill` writes two zero words to its out operand and
    `sum` returns the sum of the two words of its operand. -/
def fillSumTable : ProcTable := fun f =>
  if f = "fill" then
    some { arity := 1, run := fun _ => none, arrArgs := fun j => if j = 0 then some 2 else none,
           out := some 2, runOut := fun _ _ => some fun _ => 0 }
  else if f = "sum" then
    some { arity := 1, run := fun vs => some (vs.foldr (· + ·) 0),
           arrArgs := fun j => if j = 0 then some 2 else none }
  else none

/-- The positions read in `fillSumTable`: all array positions but the out operand of
    `fill`. -/
def fillSumReads : String → Nat → Option Nat := fun f j =>
  if f = "fill" then none else procArrArgs fillSumTable f j

/-- A code whose first mention of the array `a` is the out operand of a call of `fill`, and
    whose later call of `sum` reads it. -/
def fillThenSum : List LinstrRM :=
  [(callShadow "a" "fill" [.reg "a"], .reg none),
   (callShadow "r" "sum" [.reg "a"], .reg none)]

/-- The array of `fillThenSum` is write-first at the positions read. -/
theorem fillThenSum_writeFirst :
    WriteFirst "a" fillThenSum [] fillSumReads (procOut fillSumTable) :=
  writeFirstB_iff.mp (by decide +kernel)

/-- `fillThenSum` halts from an entry state at which `a` holds two words. -/
theorem fillThenSum_halts :
    ((x86Isa.withProcs fillSumTable).lsemFuelMemF (singletonProgM "f" fillThenSum) 2
      { prog := { base := { larr := fun _ => ⟨64, 2, fun _ => 7⟩ }, lfn := "f" },
        zf := false }).isSome = true := by
  decide +kernel

/-- **An array first written as the out operand of a linked call and then read by a later
    call**: the run of `fillThenSum` does not observe the words that `a` holds at entry. -/
theorem fillThenSum_congr {s : LstateMF} (hf : s.prog.lfn = "f") (hpc : s.prog.base.lpc = 0)
    {M : String → ArrCell} (hM : ∀ r, r ≠ "a" → M r = s.prog.base.larr r)
    (hshape : cellShape (M "a") = cellShape (s.prog.base.larr "a")) (fuel : Nat) :
    Option.Rel (AgreeOn [])
      ((x86Isa.withProcs fillSumTable).lsemFuelMemF (singletonProgM "f" fillThenSum) fuel s)
      ((x86Isa.withProcs fillSumTable).lsemFuelMemF (singletonProgM "f" fillThenSum) fuel
        (withArrs s M)) := by
  refine lsemFuelMemF_congr_writeFirst_procs fillSumTable (rd := fillSumReads) (As := ["a"])
    ?_ ?_ (classOK_of_coCfgB (σ := id) (aa := procArrArgs fillSumTable) (obs := [])
      (L := fun k => if k ≤ 1 then ["a"] else []) (by decide +kernel))
    (by simpa using fillThenSum_writeFirst) hf hpc (by simpa using hM)
    (by simpa using Or.inr hshape) fuel
  · intro f pr h
    unfold fillSumTable at h
    grind [ProcSummary.Kinded]
  · intro f pr h
    by_cases hfill : f = "fill"
    · subst hfill
      simp only [fillSumTable, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact fun _ _ _ => rfl
    · have hrd : fillSumReads f = pr.arrArgs := by
        funext j
        simp [fillSumReads, hfill, procArrArgs, h]
      rw [hrd]
      exact readsOnly_full pr

end CatCrypt.Crypto.SecureCompilation.X86Backend.FrameArrEntry
