/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg

@[expose] public section

set_option autoImplicit false

/-!
# Completeness of the coalescing check of a body

`ImageCoalesceCfg.coCfgB σ C L obs aa ao` checks a renaming `σ` of the array names of the
body `C` against a liveness certificate `L`. This module characterises the check exactly
as the conjunction of three properties, and states when it accepts the least certificate.

Every instruction of `C` falls into one arm (`CoArm`) of the check `coInstrB`. For each
instruction the arm fixes the array names it reads (`rdArr`), the array name it writes
(`wrArr`) and its control-flow successors (`succ`).

* `ClassOK σ C aa ao`: every instruction has an admitted shape: no refused arm, no
  compile-time-offset memory tag, jumps to labels inside the body, flag-machine
  recognisers that do not read an array instruction before and after renaming, and `σ`
  fixes the word operands and the word destination of every call.
* `NeedClosed C aa ao P obs`: the predicate `P : Nat → String → Prop` is closed under the
  backward liveness equations: `obs` is live at the end, the names an instruction reads
  are live before it, and a name live at a successor and not written by the instruction
  is live before it.
* `Interf σ C ao P`: at every instruction writing the array name `d`, no name `r ≠ d`
  live after it shares the image of `d` under `σ`.

## Main definitions

* `CoArm`, `armOf`: the arm of the check that runs an instruction.
* `rdArr`, `wrArr`, `succ`: the array names read, the array name written, the successors.
* `ClassOK`, `NeedClosed`, `Interf`: the three conjuncts of the check.
* `PLive`: the array names live at each position, the least predicate closed under the
  liveness equations.
* `NoRealAlias`: `σ` separates every written name from the names live after the write,
  and fixes the names live at entry.

## Main results

* `coInstrB_iff`, `coCfgB_iff`: the check of an instruction and of a body is exactly the
  conjunction of the three properties at the certificate `fun k r => r ∈ L k`.
* `interf_mono`: `Interf` holds at every predicate below one where it holds.
* `pLive_needClosed`, `pLive_least`: `PLive` is the least solution of `NeedClosed`.
* `coCfgB_complete`: an admitted body, a closed certificate below `PLive`, and a renaming
  without real aliasing pass the check.
-/

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageStraightRoute (arrReads arrWrite)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (shadowCall?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ImageCoalesceCfg

/-! ## 1. The arms of the check -/

/-- The arm of `coInstrB` that checks an instruction: a shadow instruction of a call, an
    instruction with an array position, an instruction falling through to the next
    position only, a conditional jump to a label, an unconditional jump to a label, any
    other operation, and a refused instruction. -/
inductive CoArm where
  | call (dst f : String) (srcs : List LOperand)
  | arr
  | seq
  | cc (lbl : LLabel)
  | goto (lbl : LLabel)
  | op
  | bad

/-- The arm of `coInstrB` that checks the instruction `i`. -/
def armOf (i : LinstrRM) : CoArm :=
  match shadowCall? i.1 with
  | some (dst, f, srcs) => .call dst f srcs
  | none =>
  if arrShapeB i then .arr
  else if (cmpArgs? i).isSome || (movRegArgs? i).isSome then .seq
  else match flagCondCC? i with
  | some (_, lbl) => .cc lbl
  | none =>
    match i.1 with
    | .Llabel _ _ => .seq
    | .Lcond _ lbl => .cc lbl
    | .Lgoto (_, lbl) => .goto lbl
    | .Lopn _ _ _ =>
        if (carryArgs? i).isSome || (wideArgs? i).isSome then .seq else .op
    | _ => .bad

/-- The check of the instruction `i` at position `k` by the arm `a`. -/
def armCheck (σ : String → String) (body : List LinstrRM) (L : Nat → List String) (k : Nat)
    (i : LinstrRM) (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    CoArm → Bool
  | .call dst f srcs => callB σ L k aa ao i.2 dst f srcs
  | .arr => plainArrB i && plainArrB (renArr σ i) && coArrStepB σ i (L (k + 1))
      && subB (arrReads i ++ (L (k + 1)).filter fun r => some r != arrWrite i) (L k)
  | .seq => subB (L (k + 1)) (L k)
  | .cc lbl => subB (L (k + 1)) (L k) && jumpB body L k lbl
  | .goto lbl => jumpB body L k lbl
  | .op => coArrStepB σ i (L (k + 1))
      && subB (arrReads i ++ (L (k + 1)).filter fun r => some r != arrWrite i) (L k)
  | .bad => false

theorem coInstrB_eq_armCheck (σ : String → String) (body : List LinstrRM)
    (L : Nat → List String) (k : Nat) (i : LinstrRM) (aa : String → Nat → Option Nat)
    (ao : String → Option Nat) :
    coInstrB σ body L k i aa ao = armCheck σ body L k i aa ao (armOf i) := by
  unfold coInstrB armOf
  rcases h1 : shadowCall? i.1 with _ | ⟨dst, f, srcs⟩
  · dsimp only
    by_cases h2 : arrShapeB i = true
    · simp only [h2, ↓reduceIte]; rfl
    by_cases h3 : ((cmpArgs? i).isSome || (movRegArgs? i).isSome) = true
    · simp only [h2, h3, ↓reduceIte]; rfl
    simp only [h2, h3, Bool.false_eq_true, ↓reduceIte]
    rcases h4 : flagCondCC? i with _ | ⟨_, lbl⟩
    · dsimp only
      rcases h5 : i.1 with _ | _ | _ | _ | _ <;> try rfl
      by_cases h6 : ((carryArgs? i).isSome || (wideArgs? i).isSome) = true
      · simp only [h6, ↓reduceIte]; rfl
      · simp only [h6, Bool.false_eq_true, ↓reduceIte]; rfl
    · rfl
  · rfl

/-! ## 2. Reads, writes and successors -/

/-- The register operands of a call at the array positions `a`, from the argument
    position `j`. -/
def callArrRegs (a : Nat → Option Nat) : Nat → List LOperand → List String
  | _, [] => []
  | j, .reg x :: os => if (a j).isSome then x :: callArrRegs a (j + 1) os
      else callArrRegs a (j + 1) os
  | j, _ :: os => callArrRegs a (j + 1) os

/-- `σ` fixes every register operand of a call outside the array positions `a`, from the
    argument position `j`. -/
def callOpsFix (σ : String → String) (a : Nat → Option Nat) : Nat → List LOperand → Bool
  | _, [] => true
  | j, o :: os =>
      (match o with
        | .reg x => (a j).isSome || σ x == x
        | _ => true)
      && callOpsFix σ a (j + 1) os

/-- The array names an instruction reads, by its arm: the array operands of a call, and
    the base of a runtime-indexed load or store. -/
def rdArrA (aa : String → Nat → Option Nat) (i : LinstrRM) : CoArm → List String
  | .call _ f srcs => callArrRegs (aa f) 0 srcs
  | .arr | .op => arrReads i
  | _ => []

/-- The array names the instruction `i` reads. -/
def rdArr (aa : String → Nat → Option Nat) (i : LinstrRM) : List String :=
  rdArrA aa i (armOf i)

/-- The array name an instruction writes, by its arm: the destination of a call with an
    array result, and the destination of a runtime-indexed store. -/
def wrArrA (ao : String → Option Nat) (i : LinstrRM) : CoArm → Option String
  | .call dst f _ => (ao f).map fun _ => dst
  | .arr | .op => arrWrite i
  | _ => none

/-- The array name the instruction `i` writes. -/
def wrArr (ao : String → Option Nat) (i : LinstrRM) : Option String :=
  wrArrA ao i (armOf i)

/-- The position `k'` is the position after the label `lbl` of `body`. -/
def JumpTo (body : List LinstrRM) (lbl : LLabel) (k' : Nat) : Prop :=
  ∃ p, findLabelMem lbl body = some p ∧ k' = p + 1

/-- The label `lbl`, when it is in `body`, is at a position `p` with `p + 1 ≤ body.length`. -/
def JumpOK (body : List LinstrRM) (lbl : LLabel) : Prop :=
  ∀ p, findLabelMem lbl body = some p → p + 1 ≤ body.length

/-- The control-flow successors of an instruction at position `k`, by its arm. -/
def SuccA (body : List LinstrRM) (k : Nat) : CoArm → Nat → Prop
  | .call _ _ _ | .arr | .seq | .op => fun k' => k' = k + 1
  | .cc lbl => fun k' => k' = k + 1 ∨ JumpTo body lbl k'
  | .goto lbl => JumpTo body lbl
  | .bad => fun _ => False

/-- The control-flow successors of the instruction `i` at position `k`. -/
def Succ (body : List LinstrRM) (k : Nat) (i : LinstrRM) (k' : Nat) : Prop :=
  SuccA body k (armOf i) k'

/-- The tag of an instruction is no compile-time-offset memory tag. -/
def TagOK (i : LinstrRM) : Prop := i.2 ≠ .loadC ∧ i.2 ≠ .storeC

/-- The shape conditions of the check, by the arm. -/
def ClassA (σ : String → String) (body : List LinstrRM) (aa : String → Nat → Option Nat)
    (ao : String → Option Nat) (i : LinstrRM) : CoArm → Prop
  | .call dst f srcs =>
      callTagB i.2 = true ∧ callOpsFix σ (aa f) 0 srcs = true ∧ (ao f = none → σ dst = dst)
  | .arr => plainArrB i = true ∧ plainArrB (renArr σ i) = true ∧ TagOK i
  | .seq => True
  | .cc lbl | .goto lbl => JumpOK body lbl
  | .op => TagOK i
  | .bad => False

/-! ## 3. The three conjuncts -/

/-- **Every instruction of `body` has an admitted shape.** -/
def ClassOK (σ : String → String) (body : List LinstrRM) (aa : String → Nat → Option Nat)
    (ao : String → Option Nat) : Prop :=
  ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → ClassA σ body aa ao i (armOf i)

/-- The liveness equations at the instruction `i` at position `k`: the names it reads are
    in `P k`, and a name in `P k'` at a successor `k'` that `i` does not write is in
    `P k`. -/
def NeedAt (body : List LinstrRM) (aa : String → Nat → Option Nat) (ao : String → Option Nat)
    (P : Nat → String → Prop) (k : Nat) (i : LinstrRM) : Prop :=
  (∀ r ∈ rdArr aa i, P k r) ∧ ∀ k' r, Succ body k i k' → some r ≠ wrArr ao i → P k' r → P k r

/-- **The predicate `P` is closed under the backward liveness equations of `body`**, with
    the names `obs` read after the body. -/
def NeedClosed (body : List LinstrRM) (aa : String → Nat → Option Nat)
    (ao : String → Option Nat) (P : Nat → String → Prop) (obs : List String) : Prop :=
  (∀ r ∈ obs, P body.length r) ∧ ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → NeedAt body aa ao P k i

/-- **No write is aliased under `σ`**: at every instruction writing the array name `d`, no
    name `r ≠ d` in `P (k + 1)` shares the image of `d` under `σ`. -/
def Interf (σ : String → String) (body : List LinstrRM) (ao : String → Option Nat)
    (P : Nat → String → Prop) : Prop :=
  ∀ (k : Nat) (i : LinstrRM), body[k]? = some i → ∀ d, wrArr ao i = some d → ∀ r, P (k + 1) r → r ≠ d → σ r ≠ σ d

theorem interf_mono {σ : String → String} {body : List LinstrRM} {ao : String → Option Nat}
    {P Q : Nat → String → Prop} (hPQ : ∀ k r, P k r → Q k r) (h : Interf σ body ao Q) :
    Interf σ body ao P :=
  fun k i hi d hd r hr hne => h k i hi d hd r (hPQ _ _ hr) hne

/-! ## 4. The least solution -/

/-- **The array names live at each position of `body`** when the names `obs` are read
    after it: the least predicate closed under the liveness equations. -/
inductive PLive (body : List LinstrRM) (aa : String → Nat → Option Nat)
    (ao : String → Option Nat) (obs : List String) : Nat → String → Prop
  | obs {r : String} : r ∈ obs → PLive body aa ao obs body.length r
  | read {k : Nat} {i : LinstrRM} {r : String} : body[k]? = some i → r ∈ rdArr aa i →
      PLive body aa ao obs k r
  | step {k k' : Nat} {i : LinstrRM} {r : String} : body[k]? = some i → Succ body k i k' →
      some r ≠ wrArr ao i → PLive body aa ao obs k' r → PLive body aa ao obs k r

theorem pLive_needClosed (body : List LinstrRM) (aa : String → Nat → Option Nat)
    (ao : String → Option Nat) (obs : List String) :
    NeedClosed body aa ao (PLive body aa ao obs) obs :=
  ⟨fun _ hr => .obs hr, fun _ _ hi =>
    ⟨fun _ hr => .read hi hr, fun _ _ hs hw hr => .step hi hs hw hr⟩⟩

theorem pLive_least {body : List LinstrRM} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} {obs : List String} {P : Nat → String → Prop}
    (hP : NeedClosed body aa ao P obs) : ∀ k r, PLive body aa ao obs k r → P k r := by
  intro k r h
  induction h with
  | obs hr => exact hP.1 _ hr
  | read hi hr => exact (hP.2 _ _ hi).1 _ hr
  | step hi hs hw _ ih => exact (hP.2 _ _ hi).2 _ _ hs hw ih

/-- **No real aliasing**: `σ` separates every written name from the names live after the
    write, and fixes every name live at entry. -/
def NoRealAlias (σ : String → String) (body : List LinstrRM) (aa : String → Nat → Option Nat)
    (ao : String → Option Nat) (obs : List String) : Prop :=
  Interf σ body ao (PLive body aa ao obs) ∧ ∀ r, PLive body aa ao obs 0 r → σ r = r

/-! ## 5. Exactness of the check -/

theorem subB_iff {A B : List String} : subB A B = true ↔ ∀ r ∈ A, r ∈ B := by
  simp [subB]

theorem callOpsB_iff (σ : String → String) (a : Nat → Option Nat) (live : List String) :
    ∀ (j : Nat) (os : List LOperand), callOpsB σ a live j os = true ↔
      callOpsFix σ a j os = true ∧ ∀ x ∈ callArrRegs a j os, x ∈ live := by
  intro j os
  induction os generalizing j with
  | nil => simp [callOpsB, callOpsFix, callArrRegs]
  | cons o os ih =>
    cases o with
    | reg x =>
      cases h : (a j).isSome <;>
        simp [callOpsB, callOpsFix, callArrRegs, h, ih] <;> tauto
    | _ => simp [callOpsB, callOpsFix, callArrRegs, ih]

theorem coArrStepB_iff (σ : String → String) (i : LinstrRM) (after : List String) :
    coArrStepB σ i after = true ↔
      TagOK i ∧ ∀ d, arrWrite i = some d → ∀ r ∈ after, r ≠ d → σ r ≠ σ d := by
  rcases i with ⟨w, t⟩
  cases t <;> simp [coArrStepB, arrWrite, TagOK]
  split
  · rename_i d a b c hs
    rw [hs]
    constructor
    · intro h d' x y z hd r hr hne
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, -, -, -⟩ := hd
      have := List.all_eq_true.mp h r hr
      simp_all
    · intro h
      refine List.all_eq_true.mpr fun r hr => ?_
      by_cases hrd : r = d
      · simp [hrd]
      · simpa [hrd] using h d a b c rfl r hr hrd
  · simp_all
  split
  · rename_i d hs
    rw [hs]
    constructor
    · intro h d' hd r hr hne
      simp only [Option.some.injEq] at hd
      subst hd
      have := List.all_eq_true.mp h r hr
      simp_all
    · intro h
      refine List.all_eq_true.mpr fun r hr => ?_
      by_cases hrd : r = d
      · simp [hrd]
      · simpa [hrd] using h d rfl r hr hrd
  · simp_all
  split
  · rename_i d a b c hs
    rw [hs]
    constructor
    · intro h d' x y z hd r hr hne
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, -, -, -⟩ := hd
      have := List.all_eq_true.mp h r hr
      simp_all
    · intro h
      refine List.all_eq_true.mpr fun r hr => ?_
      by_cases hrd : r = d
      · simp [hrd]
      · simpa [hrd] using h d a b c rfl r hr hrd
  · simp_all

theorem jumpB_iff (body : List LinstrRM) (L : Nat → List String) (k : Nat) (lbl : LLabel) :
    jumpB body L k lbl = true ↔
      JumpOK body lbl ∧ ∀ k', JumpTo body lbl k' → ∀ r ∈ L k', r ∈ L k := by
  unfold jumpB JumpOK JumpTo
  split <;> simp_all [subB_iff]

/-- **The check of one instruction is exactly** its shape conditions, its liveness
    equations and its aliasing condition at the certificate `L`. -/
theorem coInstrB_iff (σ : String → String) (body : List LinstrRM) (L : Nat → List String)
    (k : Nat) (i : LinstrRM) (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    coInstrB σ body L k i aa ao = true ↔
      ClassA σ body aa ao i (armOf i) ∧ NeedAt body aa ao (fun k r => r ∈ L k) k i ∧
        ∀ d, wrArr ao i = some d → ∀ r ∈ L (k + 1), r ≠ d → σ r ≠ σ d := by
  rw [coInstrB_eq_armCheck]
  unfold NeedAt rdArr wrArr Succ
  generalize armOf i = a
  cases a with
  | call dst f srcs =>
    simp only [armCheck, callB, ClassA, rdArrA, wrArrA, SuccA, Bool.and_eq_true,
      callOpsB_iff]
    cases ao f <;> simp [subB_iff] <;> grind
  | _ => simp [armCheck, ClassA, rdArrA, wrArrA, SuccA, subB_iff, coArrStepB_iff, jumpB_iff] <;> grind

/-- **The coalescing check of a body is exactly** `ClassOK`, `NeedClosed` and `Interf` at
    the certificate `fun k r => r ∈ L k`. -/
theorem coCfgB_iff (σ : String → String) (body : List LinstrRM) (L : Nat → List String)
    (obs : List String) (aa : String → Nat → Option Nat) (ao : String → Option Nat) :
    coCfgB σ body L obs aa ao = true ↔
      ClassOK σ body aa ao ∧ NeedClosed body aa ao (fun k r => r ∈ L k) obs ∧
        Interf σ body ao (fun k r => r ∈ L k) := by
  unfold coCfgB
  rw [Bool.and_eq_true, subB_iff, List.all_eq_true]
  constructor
  · rintro ⟨hobs, h⟩
    have h' : ∀ (k : Nat) (i : LinstrRM), body[k]? = some i →
        coInstrB σ body L k i aa ao = true := fun k i hi => by
      have := h k (List.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1)
      rwa [hi] at this
    simp only [coInstrB_iff] at h'
    exact ⟨fun k i hi => (h' k i hi).1, ⟨hobs, fun k i hi => (h' k i hi).2.1⟩,
      fun k i hi => (h' k i hi).2.2⟩
  · rintro ⟨hc, ⟨hobs, hn⟩, hi⟩
    refine ⟨hobs, fun k _ => ?_⟩
    split
    · exact (coInstrB_iff σ body L k _ aa ao).mpr ⟨hc k _ ‹_›, hn k _ ‹_›, hi k _ ‹_›⟩
    · rfl

/-- **Completeness of the coalescing check**: an admitted body, a certificate closed under
    the liveness equations and contained in `PLive`, and a renaming without real aliasing
    pass the check. -/
theorem coCfgB_complete {σ : String → String} {body : List LinstrRM} {L : Nat → List String}
    {obs : List String} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hc : ClassOK σ body aa ao) (hn : NeedClosed body aa ao (fun k r => r ∈ L k) obs)
    (hL : ∀ k, ∀ r ∈ L k, PLive body aa ao obs k r) (ha : NoRealAlias σ body aa ao obs) :
    coCfgB σ body L obs aa ao = true :=
  (coCfgB_iff σ body L obs aa ao).mpr ⟨hc, hn, interf_mono hL ha.1⟩

end CatCrypt.Crypto.SecureCompilation.X86Backend.CoalesceComplete
