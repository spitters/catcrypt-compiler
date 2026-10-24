/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgOpt
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPrint
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold

/-!
# The side conditions of the printed body through the passes

The side conditions `physImgSideB` of the region gate read four predicates on intermediate
bodies of the printer: `PhysImgFold.copyNoSlotB` and `PhysImgFold.cellBaseFreeB` after the
basic-block optimiser, `PhysImgPrint.flagTiedB` after the register re-allocation, and
`cellBaseFreeB` on the printed body. Each predicate is a check of every instruction, so a
pass keeps it when every instruction of its output is an instruction of its input or a
rewritten form on which the check holds. This module proves that the predicates hold on
those bodies when they hold on the allocated body, pass by pass: the high-product fusion
`fuseMulHiBody`, every sublist (the dead-write elimination), the five sub-passes of
`optimizeBasicBlocks`, the constant-index fold `foldIndexedBody`, the re-allocation
`reallocBody`, the two-address legalisation `twoAddrBody` and the compare-spill reload
`cmpReload`.

The copy propagation rewrites a source register only into a fact source, a general-purpose
register or an immediate (`OpRw`), and never the first source of an operation whose single
destination it is; the load CSE redirects a move onto another register. Every instruction
the fusion writes is a `MOVQ`, `MOV:64` or `MULX` with one register source among the
operands of its `MULXHI`, `RDX` and the reload scratches (`FuseOut`). A flag-only compare
has the fixed printer shape in the re-allocation, so the re-allocation keeps its names.
The redirect of a 64-bit copy by the load CSE onto a holder is the one rewrite that can read
an array slot. On a body with no 64-bit move between two memory names (`memMovFreeB`) every
holder of a redirect is a register name (`LoadCSE.loadCSEAux_pointwise_reg`), and an array
slot, a `qsave.` slot, is a memory name.

## Main results

* `forall_fuseMulHiBody`, `forall_optimizeBasicBlocks`: a check of every instruction through
  the fusion and the optimiser.
* `cellBaseFreeB_fuseMulHiBody`, `cellBaseFreeB_elimReloads`, `cellBaseFreeB_reloadElimBody`,
  `cellBaseFreeB_scheduleBody`, `cellBaseFreeB_copyPropagateBody`, `cellBaseFreeB_loadCSE`,
  `cellBaseFreeB_optimizeBasicBlocks`, `cellBaseFreeB_foldIndexedBody`,
  `cellBaseFreeB_reallocBody`, `cellBaseFreeB_twoAddrBody`, `cellBaseFreeB_cmpReload`: every
  pass keeps `cellBaseFreeB`.
* `flagTiedB_fuseMulHiBody`, `flagTiedB_elimReloads`, `flagTiedB_reloadElimBody`,
  `flagTiedB_scheduleBody`, `flagTiedB_copyPropagateBody`, `flagTiedB_loadCSE`,
  `flagTiedB_optimizeBasicBlocks`, `flagTiedB_foldIndexedBody`, `flagTiedB_reallocBody`:
  every pass up to the re-allocation keeps `flagTiedB`.
* `copyNoSlotB_fuseMulHiBody`, `copyNoSlotB_elimReloads`, `copyNoSlotB_reloadElimBody`,
  `copyNoSlotB_scheduleBody`, `copyNoSlotB_copyPropagateBody`, `copyNoSlotB_loadCSE`,
  `copyNoSlotB_optimizeBasicBlocks`: the fusion keeps `copyNoSlotB` when no operand of a
  `MULXHI` is an array slot (`mulHiNoSlotB`), and the load CSE under `memMovFreeB`.
* `cellBaseFreeB_sublist`, `flagTiedB_sublist`, `copyNoSlotB_sublist`: every sublist keeps the
  predicates.
* `copyNoSlotB_postOpt`, `cellBaseFreeB_postOpt`, `flagTiedB_reallocStage`,
  `cellBaseFreeB_printedChain`: conjuncts 4, 5, 7 and 9 of `physImgSideB` from the predicates
  on the allocated body, for every sublist of its fusion.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit (slotArr_none_of_prefix isArrImmB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold (copyNoSlotB cellBaseFreeB
  gpNameB_prefix isPhysGP_eq_gpNameB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPrint (flagTiedB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data tieBase)

variable {slotArr : String → Option (String × Nat)}

/-! ## 1. The predicates instruction by instruction -/

/-- The instruction has no register-indexed first source. -/
def NoIdxFst (j : Linstr) : Prop :=
  ∀ ds o x y sc ss, j.li_i ≠ .Lopn ds o (.arrIdx x y sc :: ss)

/-- The base of a register-indexed first source of the instruction is no cell name, and so is
    the register first source of a `ZEROARR` or `STOREIMM`. -/
def CellOk (j : Linstr) : Prop :=
  (∀ ds o x y sc ss, j.li_i = .Lopn ds o (.arrIdx x y sc :: ss) →
    hasPrefix x "mem." = false) ∧
  ∀ ds o x ss, j.li_i = .Lopn ds o (.reg x :: ss) → isArrImmB j.li_i = true →
    hasPrefix x "mem." = false

/-- A flag-only compare of the instruction with a register as its first source is tied. -/
def TiedI (j : Linstr) : Prop :=
  ∀ d opn x c, j.li_i = .Lopn [.reg d] opn [.reg x, c] →
    x86Data.flagOnly (tieBase opn) = true → x = d

/-- A 64-bit copy into a register of the instruction reads no array slot. -/
def CopyOk (slotArr : String → Option (String × Nat)) (j : Linstr) : Prop :=
  ∀ d x, j.li_i = .Lopn [.reg d] "MOV:64" [.reg x] → slotArr x = none

theorem cellBaseFreeB_iff {b : Lcmd} : cellBaseFreeB b = true ↔ ∀ j ∈ b, CellOk j := by
  unfold cellBaseFreeB
  rw [List.all_eq_true]
  refine forall₂_congr fun j _ => ?_
  constructor
  · intro h
    refine ⟨fun ds o x y sc ss he => ?_, fun ds o x ss he hai => ?_⟩
    · rw [he] at h
      simpa using h
    · rw [he] at h hai
      simpa [hai] using h
  · rintro ⟨h1, h2⟩
    split
    · rename_i ds o x y sc ss he
      simpa using h1 ds o x y sc ss he
    · rename_i ds o x ss he
      cases hai : isArrImmB (.Lopn ds o (.reg x :: ss))
      · simp
      · simpa [hai] using h2 ds o x ss he (by rw [he]; exact hai)
    · rfl

theorem flagTiedB_iff {b : Lcmd} : flagTiedB b = true ↔ ∀ j ∈ b, TiedI j := by
  unfold flagTiedB
  rw [List.all_eq_true]
  refine forall₂_congr fun j _ => ?_
  constructor
  · intro h d opn x c he hf
    rw [he] at h
    have h' : (!(x86Data.flagOnly (tieBase opn)) || x == d) = true := h
    rw [hf] at h'
    simpa using h'
  · intro h
    split
    · rename_i d opn x c he
      cases hf : x86Data.flagOnly (tieBase opn)
      · rfl
      · rw [h d opn x c he hf]; simp
    · rfl

theorem copyNoSlotB_iff {b : Lcmd} :
    copyNoSlotB slotArr b = true ↔ ∀ j ∈ b, CopyOk slotArr j := by
  unfold copyNoSlotB
  rw [List.all_eq_true]
  refine forall₂_congr fun j _ => ?_
  constructor
  · intro h d x he
    rw [he] at h
    simpa using h
  · intro h
    split
    · rename_i d x he
      simpa using h d x he
    · rfl

theorem cellOk_of_noIdxFst {j : Linstr} (h : NoIdxFst j) (h2 : isArrImmB j.li_i = false) :
    CellOk j :=
  ⟨fun ds o x y sc ss he => absurd he (h ds o x y sc ss),
    fun _ _ _ _ _ hai => by rw [h2] at hai; cases hai⟩

/-- A predicate on every instruction of a body holds on every sublist. -/
theorem forall_of_sublist {P : Linstr → Prop} {b b' : Lcmd} (hs : b'.Sublist b)
    (h : ∀ j ∈ b, P j) : ∀ j ∈ b', P j :=
  fun j hj => h j (hs.subset hj)

/-- A predicate on every instruction of a body holds on every permutation. -/
theorem forall_of_perm {P : Linstr → Prop} {b b' : Lcmd} (hs : b'.Perm b)
    (h : ∀ j ∈ b, P j) : ∀ j ∈ b', P j :=
  fun j hj => h j (hs.subset hj)

/-- Under the slot hypothesis, a general-purpose name is no array slot. -/
theorem slotArr_physGP (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {x : String} (h : LcmdCopyPropagate.isPhysGP x = true) : slotArr x = none :=
  slotArr_none_of_prefix hq (gpNameB_prefix (by rwa [← isPhysGP_eq_gpNameB])).1

/-! ## 2. The high-product fusion -/

/-- An instruction written by a fusion site of `MULXHI d, [s1, s2]`: a `MOVQ`, `MOV:64` or
    `MULX` with one register source among `s1`, `s2`, `d`, `RDX` and the reload scratches. -/
def FuseOut (d s1 s2 : String) (r : Linstr) : Prop :=
  ∃ ds o y, r.li_i = .Lopn ds o [.reg y] ∧ (o = "MOVQ" ∨ o = "MOV:64" ∨ o = "MULX") ∧
    (y = s1 ∨ y = s2 ∨ y = d ∨ y = "RDX" ∨ y = reloadScratch ∨ y = reloadScratch2)

/-- One step of the fusion writes the instruction itself, or a block of `FuseOut`
    instructions of a `MULXHI`. -/
theorem fuseMulHiAux_cons_out (s : Bool) (env : ScratchEnv) (pend : List (String × String))
    (i : Linstr) (rest : Lcmd) :
    ∃ L env' pend', fuseMulHiAux s env pend (i :: rest) = L ++ fuseMulHiAux s env' pend' rest ∧
      (L = [i] ∨ ∃ d opn s1 s2, i.li_i = .Lopn [.reg d] opn [.reg s1, .reg s2] ∧
        isMulHiMnem opn = true ∧ ∀ r ∈ L, FuseOut d s1 s2 r) := by
  rw [fuseMulHiAux]
  split
  · rename_i d opn s1 s2 heq
    split
    · exact ⟨[i], _, _, rfl, Or.inl rfl⟩
    · rename_i hlo
      by_cases hhi : isMulHiMnem opn = true
      · simp only [hhi, ite_true]
        split
        · split
          · split
            · refine ⟨_, _, _, rfl, Or.inr ⟨d, opn, s1, s2, heq, hhi, ?_⟩⟩
              intro r hr
              unfold squareSite at hr
              split at hr <;>
                simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
                  or_false] at hr <;>
                rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
                exact ⟨_, _, _, rfl, by simp, by simp [reloadScratch, reloadScratch2]⟩
            · exact ⟨[i], _, _, rfl, Or.inl rfl⟩
          · split
            · exact ⟨[i], _, _, rfl, Or.inl rfl⟩
            · have hassoc : ∀ (a b c e t : Lcmd) (x y : Linstr),
                  a ++ x :: (b ++ y :: ((c ++ e) ++ t)) =
                    (a ++ x :: (b ++ y :: (c ++ e))) ++ t := by
                intros; simp
              refine ⟨_, _, _, hassoc _ _ _ _ _ _ _, Or.inr ⟨d, opn, s1, s2, heq, hhi, ?_⟩⟩
              intro r hr
              simp only [List.mem_append, List.mem_cons] at hr
              rcases hr with h | rfl | h | rfl | h | h
              · split at h
                · simp only [List.mem_singleton] at h; subst h
                  exact ⟨_, _, _, rfl, by simp, by simp [reloadScratch, reloadScratch2]⟩
                · simp at h
              · exact ⟨_, _, _, rfl, by simp, by simp [reloadScratch, reloadScratch2]⟩
              · split at h
                · simp only [List.mem_singleton] at h; subst h
                  exact ⟨_, _, _, rfl, by simp, by simp⟩
                · simp at h
              · refine ⟨_, _, _, rfl, by simp, ?_⟩
                (try split_ifs) <;> simp [reloadScratch, reloadScratch2]
              · split at h
                · simp only [List.mem_singleton] at h; subst h
                  refine ⟨_, _, _, rfl, by simp, ?_⟩
                  (try split_ifs) <;> simp [reloadScratch, reloadScratch2]
                · simp at h
              · split at h
                · simp only [List.mem_singleton] at h; subst h
                  exact ⟨_, _, _, rfl, by simp, by simp [reloadScratch, reloadScratch2]⟩
                · simp at h
        · exact ⟨[i], _, _, rfl, Or.inl rfl⟩
      · simp only [hhi, ite_false, Bool.false_eq_true]
        exact ⟨[i], _, _, rfl, Or.inl rfl⟩
  · exact ⟨[i], _, _, rfl, Or.inl rfl⟩

/-- Every instruction of the fusion is an instruction of the body or a `FuseOut` instruction
    of a `MULXHI` of the body. -/
theorem mem_fuseMulHiAux (s : Bool) :
    ∀ (b : Lcmd) (env : ScratchEnv) (pend : List (String × String)) (r : Linstr),
      r ∈ fuseMulHiAux s env pend b → r ∈ b ∨ ∃ i ∈ b, ∃ d opn s1 s2,
        i.li_i = .Lopn [.reg d] opn [.reg s1, .reg s2] ∧ isMulHiMnem opn = true ∧
          FuseOut d s1 s2 r
  | [], env, pend, r, hr => by rw [fuseMulHiAux] at hr; cases hr
  | i :: rest, env, pend, r, hr => by
    obtain ⟨L, env', pend', he, hL⟩ := fuseMulHiAux_cons_out s env pend i rest
    rw [he, List.mem_append] at hr
    rcases hr with hr | hr
    · rcases hL with rfl | ⟨d, opn, s1, s2, heq, hhi, hout⟩
      · simp only [List.mem_singleton] at hr
        exact Or.inl (by simp [hr])
      · exact Or.inr ⟨i, by simp, d, opn, s1, s2, heq, hhi, hout r hr⟩
    · rcases mem_fuseMulHiAux s rest env' pend' r hr with h | ⟨j, hj, h⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, h⟩

/-- A predicate that holds on every instruction of a body, and on every `FuseOut`
    instruction of each of its `MULXHI`s, holds on every instruction of its fusion. -/
theorem forall_fuseMulHiBody (s : Bool) {P : Linstr → Prop} {b : Lcmd} (h : ∀ j ∈ b, P j)
    (hsite : ∀ i ∈ b, ∀ d opn s1 s2, i.li_i = .Lopn [.reg d] opn [.reg s1, .reg s2] →
      isMulHiMnem opn = true → ∀ r, FuseOut d s1 s2 r → P r) :
    ∀ j ∈ fuseMulHiBody b s, P j := by
  intro j hj
  rcases mem_fuseMulHiAux s b [] [] j hj with hj | ⟨i, hi, d, opn, s1, s2, heq, hhi, hout⟩
  · exact h j hj
  · exact hsite i hi d opn s1 s2 heq hhi j hout

theorem cellOk_of_fuseOut {d s1 s2 : String} {r : Linstr} (h : FuseOut d s1 s2 r) :
    CellOk r := by
  obtain ⟨ds, o, y, hr, ho, -⟩ := h
  refine cellOk_of_noIdxFst (fun ds' o' x y' sc ss he => by rw [hr] at he; simp at he) ?_
  rw [hr]
  rcases ho with rfl | rfl | rfl <;> simp [isArrImmB]

theorem tiedI_of_fuseOut {d s1 s2 : String} {r : Linstr} (h : FuseOut d s1 s2 r) : TiedI r := by
  obtain ⟨ds, o, y, hr, -, -⟩ := h
  intro d' opn x c he
  rw [hr] at he
  simp at he

/-- **`cellBaseFreeB_fuseMulHiBody`**: the fusion keeps `cellBaseFreeB`. -/
theorem cellBaseFreeB_fuseMulHiBody (s : Bool) {b : Lcmd} (h : cellBaseFreeB b = true) :
    cellBaseFreeB (fuseMulHiBody b s) = true :=
  cellBaseFreeB_iff.mpr (forall_fuseMulHiBody s (cellBaseFreeB_iff.mp h)
    fun _ _ _ _ _ _ _ _ _ hr => cellOk_of_fuseOut hr)

/-- **`flagTiedB_fuseMulHiBody`**: the fusion keeps `flagTiedB`. -/
theorem flagTiedB_fuseMulHiBody (s : Bool) {b : Lcmd} (h : flagTiedB b = true) :
    flagTiedB (fuseMulHiBody b s) = true :=
  flagTiedB_iff.mpr (forall_fuseMulHiBody s (flagTiedB_iff.mp h)
    fun _ _ _ _ _ _ _ _ _ hr => tiedI_of_fuseOut hr)

/-- No operand of a `MULXHI` the fusion may rewrite is an array slot. -/
def mulHiNoSlotB (slotArr : String → Option (String × Nat)) (b : Lcmd) : Bool :=
  b.all fun i => match i.li_i with
    | .Lopn [.reg d] opn [.reg s1, .reg s2] =>
        !isMulHiMnem opn || ((slotArr d).isNone && (slotArr s1).isNone && (slotArr s2).isNone)
    | _ => true

/-- **`copyNoSlotB_fuseMulHiBody`**: the fusion keeps `copyNoSlotB` when every array slot is a
    `qsave.` slot and no operand of a `MULXHI` is an array slot. -/
theorem copyNoSlotB_fuseMulHiBody (s : Bool)
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {b : Lcmd}
    (h : copyNoSlotB slotArr b = true) (hm : mulHiNoSlotB slotArr b = true) :
    copyNoSlotB slotArr (fuseMulHiBody b s) = true := by
  refine copyNoSlotB_iff.mpr (forall_fuseMulHiBody s (copyNoSlotB_iff.mp h) ?_)
  rintro i hi d opn s1 s2 heq hhi r ⟨ds, o, y, hr, -, hy⟩ d' x hx
  rw [hr] at hx
  simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at hx
  obtain ⟨-, -, rfl⟩ := hx
  have hmi := List.all_eq_true.mp hm i hi
  rw [heq] at hmi
  simp only [hhi, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    Option.isNone_iff_eq_none] at hmi
  have hgp : ∀ n, n = "RDX" ∨ n = reloadScratch ∨ n = reloadScratch2 →
      slotArr n = none := by
    rintro n (rfl | rfl | rfl) <;> exact slotArr_none_of_prefix hq (by decide)
  rcases hy with rfl | rfl | rfl | hy
  · exact hmi.1.2
  · exact hmi.2
  · exact hmi.1.1
  · exact hgp _ hy

/-! ## 3. The copy propagation and the load CSE -/

section Opt

open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate

/-- A source operand `a'` the copy propagation writes in place of `a` in an operation with
    destinations `dsts`: `a` itself, or a fact source in place of a register that is not the
    single destination. -/
def OpRw (dsts : List LOperand) (a a' : LOperand) : Prop :=
  a' = a ∨ ∃ u, a = .reg u ∧ isFactSrc a' = true ∧ ∀ d, dsts = [.reg d] → u ≠ d

theorem opRw_rewriteOperand {facts : List MoveFact} (hf : ∀ f ∈ facts, isFactSrc f.2.1 = true)
    (w : Nat) (ai : Bool) (dsts : List LOperand) (ds : Option String)
    (hds : ∀ d, dsts = [.reg d] → isPhysGP d = true → ds = some d) (a : LOperand) :
    OpRw dsts a (rewriteOperand facts w ai ds a) := by
  cases a with
  | reg u =>
    simp only [rewriteOperand]
    by_cases hc : (isPhysGP u && ds != some u) = true
    · rw [ite_eq_left hc]
      cases hl : lookupFact facts u with
      | none => exact Or.inl rfl
      | some p =>
        obtain ⟨v, fw⟩ := p
        dsimp only
        split
        · right
          refine ⟨u, rfl, hf _ (lookupFact_mem hl), fun d hd => ?_⟩
          rintro rfl
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
          exact hc.2 (hds u hd hc.1)
        · exact Or.inl rfl
    · rw [ite_eq_right hc]; exact Or.inl rfl
  | _ => exact Or.inl rfl

theorem mem_foldl_killFacts : ∀ (l : List String) (facts : List MoveFact) (f : MoveFact),
    f ∈ l.foldl killFacts facts → f ∈ facts
  | [], _, _, h => h
  | _ :: l, _, f, h => (mem_killFacts (mem_foldl_killFacts l _ f h)).1

/-- Every instruction of the forward move propagation is an instruction of the body, or an
    operation of the body whose sources are rewritten by `OpRw`. -/
theorem mem_propagateAux : ∀ (b : Lcmd) (facts : List MoveFact),
    (∀ f ∈ facts, isFactSrc f.2.1 = true) → ∀ r ∈ propagateAux facts b, ∃ i ∈ b,
      r = i ∨
      ∃ dsts opn srcs g, i.li_i = .Lopn dsts opn srcs ∧ (∀ a, OpRw dsts a (g a)) ∧
        r = { i with li_i := .Lopn dsts opn (srcs.map g) }
  | [], _, _, r, hr => by simp [propagateAux] at hr
  | i :: rest, facts, hf, r, hr => by
    have lift : (∃ j ∈ rest, r = j ∨ ∃ dsts opn srcs g, j.li_i = .Lopn dsts opn srcs ∧
        (∀ a, OpRw dsts a (g a)) ∧ r = { j with li_i := .Lopn dsts opn (srcs.map g) }) →
        ∃ j ∈ i :: rest, r = j ∨ ∃ dsts opn srcs g, j.li_i = .Lopn dsts opn srcs ∧
          (∀ a, OpRw dsts a (g a)) ∧ r = { j with li_i := .Lopn dsts opn (srcs.map g) } :=
      fun ⟨j, hj, h⟩ => ⟨j, List.mem_cons_of_mem _ hj, h⟩
    rw [propagateAux] at hr
    split at hr
    · rename_i dsts opn srcs heq
      split at hr
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨i, List.mem_cons_self, Or.inr ⟨dsts, opn, srcs, _, heq,
            opRw_rewriteOperand hf _ _ dsts _ (fun d hd hp => by subst hd; simp [hp]), rfl⟩⟩
        · refine lift (mem_propagateAux rest _ ?_ r hr)
          intro f hfm
          split at hfm
          · rename_i d src w hms
            split at hfm
            · exact hf f (mem_foldl_killFacts _ _ f hfm)
            · rcases List.mem_cons.mp hfm with rfl | hfm
              · obtain ⟨_, _, _, hs, _⟩ := moveShape_inv hms
                exact hs
              · exact hf f (mem_foldl_killFacts _ _ f hfm)
          · exact hf f (mem_foldl_killFacts _ _ f hfm)
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨_, List.mem_cons_self, Or.inl rfl⟩
        · exact lift (mem_propagateAux rest [] (by simp) r hr)
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨_, List.mem_cons_self, Or.inl rfl⟩
      · exact lift (mem_propagateAux rest [] (by simp) r hr)

/-- A predicate closed under the source rewrites `OpRw`. -/
def RwClosed (P : Linstr → Prop) : Prop :=
  ∀ (i : Linstr) dsts opn srcs (g : LOperand → LOperand), P i →
    i.li_i = .Lopn dsts opn srcs →
    (∀ a, OpRw dsts a (g a)) → P { i with li_i := .Lopn dsts opn (srcs.map g) }

/-- A predicate closed under the redirects of a 64-bit register move (`isMov64Mnem`) onto
    another source register. -/
def MvClosed (P : Linstr → Prop) : Prop :=
  ∀ (i : Linstr) (d mn s r : String), P i → i.li_i = .Lopn [.reg d] mn [.reg s] →
    CatCrypt.Crypto.Optimizer.LoadCSE.isMov64Mnem mn = true →
    P { i with li_i := .Lopn [.reg d] mn [.reg r] }

theorem forall_copyPropagateBody {P : Linstr → Prop} (hP : RwClosed P) {b : Lcmd}
    (h : ∀ j ∈ b, P j) : ∀ j ∈ copyPropagateBody b, P j := by
  intro j hj
  obtain ⟨i, hi, hji⟩ := mem_propagateAux b [] (by simp) j
    ((deadElimBody_sublist _).subset hj)
  rcases hji with rfl | ⟨dsts, opn, srcs, g, he, hg, rfl⟩
  · exact h _ hi
  · exact hP i dsts opn srcs g (h i hi) he hg

theorem forall_loadCSE {P : Linstr → Prop} (hP : MvClosed P) {b : Lcmd} (h : ∀ j ∈ b, P j) :
    ∀ j ∈ CatCrypt.Crypto.Optimizer.LoadCSE.loadCSE b, P j := by
  intro j hj
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hj
  rw [CatCrypt.Crypto.Optimizer.LoadCSE.loadCSE_eq] at hn
  rcases CatCrypt.Crypto.Optimizer.LoadCSE.loadCSEAux_pointwise [] b n with
    he | ⟨i, d, s, r, mn, h', hb, hw, -, -, he⟩
  · rw [he] at hn
    exact h j (List.mem_of_getElem? hn)
  · rw [he, Option.some.injEq] at hn
    subst hn
    exact hP i d mn s r (h i (List.mem_of_getElem? hb))
      (CatCrypt.Crypto.Optimizer.LoadCSE.asWideReload_eq hw).1
      (CatCrypt.Crypto.Optimizer.LoadCSE.asWideReload_eq hw).2

open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad (elimReloads elimReloads_sublist)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim (reloadElimBody
  reloadElimBody_sublist)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler (scheduleBody scheduleBody_perm)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (optimizeBasicBlocks
  optRunBody splitStraightRuns splitStraightRuns_flatten bodyAllModeled)

/-- The body the load CSE of a modeled run reads: the run after `elimReloads`,
    `reloadElimBody`, `scheduleBody` and `copyPropagateBody`. -/
def preLoad (seg : Lcmd) : Lcmd :=
  copyPropagateBody (scheduleBody (reloadElimBody (elimReloads seg)))

/-- A predicate closed under `OpRw` that holds on a run holds on the body `preLoad` of it. -/
theorem forall_preLoad {P : Linstr → Prop} (hP : RwClosed P) {seg : Lcmd}
    (h : ∀ j ∈ seg, P j) : ∀ j ∈ preLoad seg, P j :=
  forall_copyPropagateBody hP (forall_of_perm (scheduleBody_perm _)
    (forall_of_sublist (reloadElimBody_sublist _)
      (forall_of_sublist (elimReloads_sublist _) h)))

/-- **The basic-block optimiser keeps a predicate on every instruction** when, on every
    modeled run on which it holds, it holds on the output of the load CSE. -/
theorem forall_optimizeBasicBlocks {P : Linstr → Prop} {b : Lcmd} (h : ∀ j ∈ b, P j)
    (hrun : ∀ seg ∈ splitStraightRuns b, bodyAllModeled seg = true → (∀ j ∈ seg, P j) →
      ∀ j ∈ CatCrypt.Crypto.Optimizer.LoadCSE.loadCSE (preLoad seg), P j) :
    ∀ j ∈ optimizeBasicBlocks b, P j := by
  intro j hj
  unfold optimizeBasicBlocks at hj
  obtain ⟨seg', hseg', hj⟩ := List.mem_flatten.mp hj
  obtain ⟨seg, hseg, rfl⟩ := List.mem_map.mp hseg'
  have hP : ∀ j ∈ seg, P j := fun j hj' =>
    h j (by rw [← splitStraightRuns_flatten b]; exact List.mem_flatten.mpr ⟨seg, hseg, hj'⟩)
  split at hj
  · unfold optRunBody at hj
    split at hj
    · rename_i hm
      exact hrun seg hseg hm hP j hj
    · exact hP j hj
  · exact hP j hj

/-- A predicate closed under `OpRw` and the move redirects is kept by the optimiser. -/
theorem forall_optimizeBasicBlocks_closed {P : Linstr → Prop} (hrw : RwClosed P)
    (hmv : MvClosed P) {b : Lcmd} (h : ∀ j ∈ b, P j) : ∀ j ∈ optimizeBasicBlocks b, P j :=
  forall_optimizeBasicBlocks h fun _ _ _ hs => forall_loadCSE hmv (forall_preLoad hrw hs)

/-! ### The base condition through the optimiser -/

theorem cellOk_rwClosed : RwClosed CellOk := by
  intro i dsts opn srcs g hi he hg
  refine ⟨fun ds o x y sc ss he' => ?_, fun ds o x ss he' hai => ?_⟩
  · dsimp only at he'
    simp only [LinstrR.Lopn.injEq] at he'
    obtain ⟨rfl, rfl, hs⟩ := he'
    cases srcs with
    | nil => cases hs
    | cons a srcs =>
      simp only [List.map_cons, List.cons.injEq] at hs
      rcases hg a with ha | ⟨u, rfl, hf, -⟩
      · rw [hs.1] at ha
        exact hi.1 _ _ _ _ _ _ (by rw [he, ← ha])
      · rw [hs.1] at hf
        cases hf
  · have hai' : isArrImmB i.li_i = true := by rw [he]; exact hai
    dsimp only at he'
    simp only [LinstrR.Lopn.injEq] at he'
    obtain ⟨rfl, rfl, hs⟩ := he'
    cases srcs with
    | nil => cases hs
    | cons a srcs =>
      simp only [List.map_cons, List.cons.injEq] at hs
      rcases hg a with ha | ⟨u, rfl, hf, -⟩
      · rw [hs.1] at ha
        exact hi.2 _ _ _ _ (by rw [he, ← ha]) hai'
      · rw [hs.1] at hf
        exact (gpNameB_prefix (by rw [← isPhysGP_eq_gpNameB]; exact hf)).2

theorem cellOk_mvClosed : MvClosed CellOk := by
  intro i d mn s r _ _ hmn
  refine ⟨fun ds o x y sc ss he => by simp at he, fun ds o x ss he hai => ?_⟩
  dsimp only at he hai
  simp only [LinstrR.Lopn.injEq] at he
  obtain ⟨-, rfl, -⟩ := he
  simp only [CatCrypt.Crypto.Optimizer.LoadCSE.isMov64Mnem, Bool.or_eq_true, beq_iff_eq] at hmn
  rcases hmn with rfl | rfl <;> simp [isArrImmB] at hai

/-- **`cellBaseFreeB_elimReloads`**: the redundant-reload elimination keeps `cellBaseFreeB`. -/
theorem cellBaseFreeB_elimReloads {b : Lcmd} (h : cellBaseFreeB b = true) :
    cellBaseFreeB (elimReloads b) = true :=
  cellBaseFreeB_iff.mpr (forall_of_sublist (elimReloads_sublist _) (cellBaseFreeB_iff.mp h))

/-- **`cellBaseFreeB_reloadElimBody`**: the spill-reload elimination keeps `cellBaseFreeB`. -/
theorem cellBaseFreeB_reloadElimBody {b : Lcmd} (h : cellBaseFreeB b = true) :
    cellBaseFreeB (reloadElimBody b) = true :=
  cellBaseFreeB_iff.mpr (forall_of_sublist (reloadElimBody_sublist _) (cellBaseFreeB_iff.mp h))

/-- **`cellBaseFreeB_scheduleBody`**: the scheduler keeps `cellBaseFreeB`. -/
theorem cellBaseFreeB_scheduleBody {b : Lcmd} (h : cellBaseFreeB b = true) :
    cellBaseFreeB (scheduleBody b) = true :=
  cellBaseFreeB_iff.mpr (forall_of_perm (scheduleBody_perm _) (cellBaseFreeB_iff.mp h))

/-- **`cellBaseFreeB_copyPropagateBody`**: the copy propagation keeps `cellBaseFreeB`. -/
theorem cellBaseFreeB_copyPropagateBody {b : Lcmd} (h : cellBaseFreeB b = true) :
    cellBaseFreeB (copyPropagateBody b) = true :=
  cellBaseFreeB_iff.mpr (forall_copyPropagateBody cellOk_rwClosed (cellBaseFreeB_iff.mp h))

/-- **`cellBaseFreeB_loadCSE`**: the load CSE keeps `cellBaseFreeB`. -/
theorem cellBaseFreeB_loadCSE {b : Lcmd} (h : cellBaseFreeB b = true) :
    cellBaseFreeB (CatCrypt.Crypto.Optimizer.LoadCSE.loadCSE b) = true :=
  cellBaseFreeB_iff.mpr (forall_loadCSE cellOk_mvClosed (cellBaseFreeB_iff.mp h))

/-- **`cellBaseFreeB_optimizeBasicBlocks`**: the basic-block optimiser keeps
    `cellBaseFreeB`. -/
theorem cellBaseFreeB_optimizeBasicBlocks {b : Lcmd} (h : cellBaseFreeB b = true) :
    cellBaseFreeB (optimizeBasicBlocks b) = true :=
  cellBaseFreeB_iff.mpr (forall_optimizeBasicBlocks_closed cellOk_rwClosed cellOk_mvClosed
    (cellBaseFreeB_iff.mp h))

/-! ### The tied compares through the optimiser -/

theorem tiedI_rwClosed : RwClosed TiedI := by
  intro i dsts opn srcs g hi he hg d opn' x c he' hf
  dsimp only at he'
  simp only [LinstrR.Lopn.injEq] at he'
  obtain ⟨rfl, rfl, hs⟩ := he'
  rcases srcs with _ | ⟨a, _ | ⟨c', _ | ⟨_, _⟩⟩⟩ <;>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, reduceCtorEq, and_false,
      and_true] at hs
  rcases hg a with ha | ⟨u, rfl, -, hu⟩
  · rw [hs.1] at ha
    exact hi d opn x c' (by rw [he, ← ha]) hf
  · exact absurd (hi d opn u c' he hf) (hu d rfl)

theorem tiedI_mvClosed : MvClosed TiedI := by
  intro i d mn s r _ _ _ d' opn x c he
  simp at he

/-- **`flagTiedB_elimReloads`**: the redundant-reload elimination keeps `flagTiedB`. -/
theorem flagTiedB_elimReloads {b : Lcmd} (h : flagTiedB b = true) :
    flagTiedB (elimReloads b) = true :=
  flagTiedB_iff.mpr (forall_of_sublist (elimReloads_sublist _) (flagTiedB_iff.mp h))

/-- **`flagTiedB_reloadElimBody`**: the spill-reload elimination keeps `flagTiedB`. -/
theorem flagTiedB_reloadElimBody {b : Lcmd} (h : flagTiedB b = true) :
    flagTiedB (reloadElimBody b) = true :=
  flagTiedB_iff.mpr (forall_of_sublist (reloadElimBody_sublist _) (flagTiedB_iff.mp h))

/-- **`flagTiedB_scheduleBody`**: the scheduler keeps `flagTiedB`. -/
theorem flagTiedB_scheduleBody {b : Lcmd} (h : flagTiedB b = true) :
    flagTiedB (scheduleBody b) = true :=
  flagTiedB_iff.mpr (forall_of_perm (scheduleBody_perm _) (flagTiedB_iff.mp h))

/-- **`flagTiedB_copyPropagateBody`**: the copy propagation keeps `flagTiedB`: it rewrites the
    first source of a compare only when that source is not the destination. -/
theorem flagTiedB_copyPropagateBody {b : Lcmd} (h : flagTiedB b = true) :
    flagTiedB (copyPropagateBody b) = true :=
  flagTiedB_iff.mpr (forall_copyPropagateBody tiedI_rwClosed (flagTiedB_iff.mp h))

/-- **`flagTiedB_loadCSE`**: the load CSE keeps `flagTiedB`. -/
theorem flagTiedB_loadCSE {b : Lcmd} (h : flagTiedB b = true) :
    flagTiedB (CatCrypt.Crypto.Optimizer.LoadCSE.loadCSE b) = true :=
  flagTiedB_iff.mpr (forall_loadCSE tiedI_mvClosed (flagTiedB_iff.mp h))

/-- **`flagTiedB_optimizeBasicBlocks`**: the basic-block optimiser keeps `flagTiedB`. -/
theorem flagTiedB_optimizeBasicBlocks {b : Lcmd} (h : flagTiedB b = true) :
    flagTiedB (optimizeBasicBlocks b) = true :=
  flagTiedB_iff.mpr (forall_optimizeBasicBlocks_closed tiedI_rwClosed tiedI_mvClosed
    (flagTiedB_iff.mp h))

/-! ### The copy condition through the optimiser -/

theorem copyOk_rwClosed (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) :
    RwClosed (CopyOk slotArr) := by
  intro i dsts opn srcs g hi he hg d x he'
  dsimp only at he'
  simp only [LinstrR.Lopn.injEq] at he'
  obtain ⟨rfl, rfl, hs⟩ := he'
  rcases srcs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, reduceCtorEq, and_false,
      and_true] at hs
  rcases hg a with ha | ⟨u, rfl, hf, -⟩
  · rw [hs] at ha
    exact hi d x (by rw [he, ← ha])
  · rw [hs] at hf
    exact slotArr_physGP hq hf

/-- No 64-bit move of the body is between two memory names. -/
def memMovFreeB (b : Lcmd) : Bool :=
  b.all fun j => !CatCrypt.Crypto.Optimizer.LoadCSE.isMemToMemMov j.li_i

theorem memMovFreeB_iff {b : Lcmd} :
    memMovFreeB b = true ↔
      ∀ j ∈ b, CatCrypt.Crypto.Optimizer.LoadCSE.isMemToMemMov j.li_i = false := by
  simp [memMovFreeB, List.all_eq_true]

/-- A slot name is no general-purpose name. -/
theorem gpNameB_of_isSlotName {n : String}
    (h : CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim.isSlotName n = true) :
    JasminLsemAddrImage.gpNameB n = false := by
  rw [CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim.isSlotName_eq_hasPrefix] at h
  cases hg : JasminLsemAddrImage.gpNameB n with
  | false => rfl
  | true =>
    simp only [JasminLsemAddrImage.gpNameB, List.contains_iff_mem, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> revert h <;> decide +kernel

/-- A physical general-purpose register is no memory name. -/
theorem isMemName_of_isPhysGP {n : String} (h : isPhysGP n = true) :
    CatCrypt.Crypto.Optimizer.LoadCSE.isMemName n = false := by
  cases hm : CatCrypt.Crypto.Optimizer.LoadCSE.isMemName n with
  | false => rfl
  | true =>
    have hg := gpNameB_of_isSlotName (n := n) hm
    rw [← PhysImgFold.isPhysGP_eq_gpNameB, h] at hg
    cases hg

theorem memMov_rwClosed :
    RwClosed (fun j => CatCrypt.Crypto.Optimizer.LoadCSE.isMemToMemMov j.li_i = false) := by
  intro i dsts opn srcs g hi he hg
  dsimp only
  cases hw : CatCrypt.Crypto.Optimizer.LoadCSE.asWideReload (.Lopn dsts opn (srcs.map g)) with
  | none => simp [CatCrypt.Crypto.Optimizer.LoadCSE.isMemToMemMov, hw]
  | some p =>
    obtain ⟨d, s', mn⟩ := p
    have hl := (CatCrypt.Crypto.Optimizer.LoadCSE.asWideReload_eq hw).1
    simp only [LinstrR.Lopn.injEq] at hl
    obtain ⟨rfl, rfl, hs⟩ := hl
    rcases srcs with _ | ⟨a, _ | ⟨_, _⟩⟩ <;>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, reduceCtorEq, and_false,
        and_true] at hs
    rcases hg a with ha | ⟨u, rfl, hf, -⟩
    · rw [ha] at hs
      subst hs
      rw [he] at hi
      simpa [List.map_cons, List.map_nil, ha] using hi
    · rw [hs] at hf
      simp only [CatCrypt.Crypto.Optimizer.LoadCSE.isMemToMemMov, hw,
        isMemName_of_isPhysGP (by simpa [isFactSrc] using hf), Bool.and_false]

/-- The redirects of the load CSE keep `CopyOk` on a body with no 64-bit move between two
    memory names, when every array slot is a `qsave.` slot: every holder of a redirect is a
    register name. -/
theorem copyOk_loadCSE
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {b : Lcmd}
    (h : ∀ j ∈ b, CopyOk slotArr j)
    (hm : ∀ j ∈ b, CatCrypt.Crypto.Optimizer.LoadCSE.isMemToMemMov j.li_i = false) :
    ∀ j ∈ CatCrypt.Crypto.Optimizer.LoadCSE.loadCSE b, CopyOk slotArr j := by
  intro j hj
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hj
  rw [CatCrypt.Crypto.Optimizer.LoadCSE.loadCSE_eq] at hn
  rcases CatCrypt.Crypto.Optimizer.LoadCSE.loadCSEAux_pointwise_reg [] b
      CatCrypt.Crypto.Optimizer.LoadCSE.memHolderRegKey_nil hm n with
    he | ⟨i, d, s, r, mn, -, -, -, hr, he⟩
  · rw [he] at hn
    exact h j (List.mem_of_getElem? hn)
  · rw [he, Option.some.injEq] at hn
    subst hn
    intro d' x hx
    dsimp only at hx
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at hx
    rw [← hx.2.2]
    refine slotArr_none_of_prefix hq ?_
    have hs := CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim.isSlotName_eq_hasPrefix r
    rw [show CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim.isSlotName r =
      CatCrypt.Crypto.Optimizer.LoadCSE.isMemName r from rfl, hr] at hs
    cases hk : hasPrefix r "qsave." with
    | false => rfl
    | true => simp [hk] at hs

/-- **`copyNoSlotB_elimReloads`**: the redundant-reload elimination keeps `copyNoSlotB`. -/
theorem copyNoSlotB_elimReloads {b : Lcmd} (h : copyNoSlotB slotArr b = true) :
    copyNoSlotB slotArr (elimReloads b) = true :=
  copyNoSlotB_iff.mpr (forall_of_sublist (elimReloads_sublist _) (copyNoSlotB_iff.mp h))

/-- **`copyNoSlotB_reloadElimBody`**: the spill-reload elimination keeps `copyNoSlotB`. -/
theorem copyNoSlotB_reloadElimBody {b : Lcmd} (h : copyNoSlotB slotArr b = true) :
    copyNoSlotB slotArr (reloadElimBody b) = true :=
  copyNoSlotB_iff.mpr (forall_of_sublist (reloadElimBody_sublist _) (copyNoSlotB_iff.mp h))

/-- **`copyNoSlotB_scheduleBody`**: the scheduler keeps `copyNoSlotB`. -/
theorem copyNoSlotB_scheduleBody {b : Lcmd} (h : copyNoSlotB slotArr b = true) :
    copyNoSlotB slotArr (scheduleBody b) = true :=
  copyNoSlotB_iff.mpr (forall_of_perm (scheduleBody_perm _) (copyNoSlotB_iff.mp h))

/-- **`copyNoSlotB_copyPropagateBody`**: the copy propagation keeps `copyNoSlotB` when every
    array slot is a `qsave.` slot: its fact sources are general-purpose registers. -/
theorem copyNoSlotB_copyPropagateBody
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {b : Lcmd}
    (h : copyNoSlotB slotArr b = true) : copyNoSlotB slotArr (copyPropagateBody b) = true :=
  copyNoSlotB_iff.mpr (forall_copyPropagateBody (copyOk_rwClosed hq) (copyNoSlotB_iff.mp h))

/-- **`copyNoSlotB_loadCSE`**: the load CSE keeps `copyNoSlotB` when every array slot is a
    `qsave.` slot and no 64-bit move is between two memory names (`memMovFreeB`). -/
theorem copyNoSlotB_loadCSE
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {b : Lcmd}
    (h : copyNoSlotB slotArr b = true) (hm : memMovFreeB b = true) :
    copyNoSlotB slotArr (CatCrypt.Crypto.Optimizer.LoadCSE.loadCSE b) = true :=
  copyNoSlotB_iff.mpr (copyOk_loadCSE hq (copyNoSlotB_iff.mp h) (memMovFreeB_iff.mp hm))

/-- **`copyNoSlotB_optimizeBasicBlocks`**: the basic-block optimiser keeps `copyNoSlotB` when
    every array slot is a `qsave.` slot and no 64-bit move is between two memory names. -/
theorem copyNoSlotB_optimizeBasicBlocks
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {b : Lcmd}
    (h : copyNoSlotB slotArr b = true) (hm : memMovFreeB b = true) :
    copyNoSlotB slotArr (optimizeBasicBlocks b) = true := by
  have hP : ∀ j ∈ b, CopyOk slotArr j ∧
      CatCrypt.Crypto.Optimizer.LoadCSE.isMemToMemMov j.li_i = false :=
    fun j hj => ⟨copyNoSlotB_iff.mp h j hj, memMovFreeB_iff.mp hm j hj⟩
  have hrw : RwClosed (fun j => CopyOk slotArr j ∧
      CatCrypt.Crypto.Optimizer.LoadCSE.isMemToMemMov j.li_i = false) :=
    fun i dsts opn srcs g hi he hg =>
      ⟨copyOk_rwClosed hq i dsts opn srcs g hi.1 he hg,
        memMov_rwClosed i dsts opn srcs g hi.2 he hg⟩
  refine copyNoSlotB_iff.mpr fun j hj => (forall_optimizeBasicBlocks hP ?_ j hj).1
  intro seg _ _ hs
  have hpre := forall_preLoad hrw hs
  intro k hk
  exact ⟨copyOk_loadCSE hq (fun j hj => (hpre j hj).1) (fun j hj => (hpre j hj).2) k hk,
    CatCrypt.Crypto.Optimizer.LoadCSE.loadCSE_noMemToMemMov _ (fun j hj => (hpre j hj).2) k hk⟩

end Opt

/-! ## 4. The constant-index fold -/

section Fold

open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold (mem_constIndexFoldBody
  foldCore_getElem? foldInstr_cases dropDeadCore_sublist spellMemInstr_cases)

theorem forall_dropDeadImmBody {P : Linstr → Prop} {b : Lcmd} (h : ∀ j ∈ b, P j) :
    ∀ j ∈ dropDeadImmBody b, P j := by
  unfold dropDeadImmBody
  dsimp only
  split
  · exact forall_of_sublist (dropDeadCore_sublist _ b) h
  · exact h

theorem forall_spellMemBody {P : Linstr → Prop}
    (hP : ∀ i : Linstr, P i → P { i with li_i := spellMemInstr i.li_i }) {b : Lcmd}
    (h : ∀ j ∈ b, P j) : ∀ j ∈ spellMemBody b, P j := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
  exact hP i (h i hi)

/-- Every instruction of the fold is an instruction of the body or the folded form of one:
    a direct load, a direct store or an immediate copy. -/
theorem mem_constIndexFoldBody_cases {b : Lcmd} {j : Linstr} (hj : j ∈ constIndexFoldBody b) :
    j ∈ b ∨ (∃ d B off, j.li_i = .Lopn [.reg d] "LOAD" [.arr B off]) ∨
      (∃ d B off vn, j.li_i = .Lopn [.reg d] "STORE" [.arr B off, .reg vn]) ∨
      (∃ d n, j.li_i = .Lopn [.reg d] "MOV:64" [.imm n]) := by
  unfold constIndexFoldBody at hj
  dsimp only at hj
  split at hj
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hj
    obtain ⟨i, e, h1, h2, -⟩ := foldCore_getElem? _ _ b [] k _ (List.getElem?_eq_getElem hk)
    rw [h2]
    rcases foldInstr_cases _ e i.li_i with hf | ⟨d, B, x, sc, off, -, hf⟩ |
        ⟨d, B, x, sc, vn, off, -, hf⟩ | ⟨d, x, n, -, hf, -⟩
    · left
      have : ({ i with li_i := i.li_i } : Linstr) = i := rfl
      rw [hf, this]
      exact List.mem_of_getElem? h1
    · exact Or.inr (Or.inl ⟨d, B, off, hf⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨d, B, off, vn, hf⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨d, n, hf⟩))
  · exact Or.inl hj

/-- **`cellBaseFreeB_foldIndexedBody`**: the constant-index fold, the removal of dead
    immediate moves and the array-ABI spelling keep `cellBaseFreeB`. -/
theorem cellBaseFreeB_foldIndexedBody {b : Lcmd} (h : cellBaseFreeB b = true) :
    cellBaseFreeB (foldIndexedBody b) = true := by
  have h0 := cellBaseFreeB_iff.mp h
  have h1 : ∀ j ∈ constIndexFoldBody b, CellOk j := fun j hj =>
    (mem_constIndexFoldBody hj).elim (h0 j) fun hn =>
      (PhysImgFold.mem_constIndexFoldBody_arrImm hj).elim (h0 j) (cellOk_of_noIdxFst hn)
  refine cellBaseFreeB_iff.mpr (forall_spellMemBody ?_ (forall_dropDeadImmBody h1))
  intro i hi
  rcases spellMemInstr_cases i.li_i with he | ⟨d, B, off, -, o, he, ho⟩ |
      ⟨d, B, off, vn, -, o, he, ho⟩
  · have : ({ i with li_i := spellMemInstr i.li_i } : Linstr) = i := by rw [he]
    rw [this]; exact hi
  all_goals
    refine cellOk_of_noIdxFst (fun ds o' x y sc ss hc => ?_) ?_
    · dsimp only at hc
      rw [he] at hc
      simp at hc
    · dsimp only
      rw [he]
      rcases ho with rfl | rfl <;> simp [isArrImmB]

/-- **`flagTiedB_foldIndexedBody`**: the constant-index fold, the removal of dead immediate
    moves and the array-ABI spelling keep `flagTiedB`: the fold rewrites no compare. -/
theorem flagTiedB_foldIndexedBody {b : Lcmd} (h : flagTiedB b = true) :
    flagTiedB (foldIndexedBody b) = true := by
  have h0 := flagTiedB_iff.mp h
  have h1 : ∀ j ∈ constIndexFoldBody b, TiedI j := by
    intro j hj
    rcases mem_constIndexFoldBody_cases hj with hj | ⟨_, _, _, he⟩ | ⟨_, _, _, _, he⟩ |
        ⟨_, _, he⟩
    · exact h0 j hj
    all_goals
      intro d opn x c hc
      rw [he] at hc
      simp at hc
  refine flagTiedB_iff.mpr (forall_spellMemBody ?_ (forall_dropDeadImmBody h1))
  intro i hi
  rcases spellMemInstr_cases i.li_i with he | ⟨d, B, off, -, o, he, -⟩ |
      ⟨d, B, off, vn, -, o, he, -⟩
  · have : ({ i with li_i := spellMemInstr i.li_i } : Linstr) = i := by rw [he]
    rw [this]; exact hi
  all_goals
    intro d' opn x c hc
    dsimp only at hc
    rw [he] at hc
    simp at hc

end Fold

/-! ## 5. The register re-allocation -/

section Realloc

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogAsmPrinter (stripAbiTag)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocCfg (annotate_fst)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpReallocLeak (Piece.toLcmd pieces_flatten)

/-- Every instruction of the re-allocation of a run carries the mnemonic of an instruction of
    the run. -/
theorem goAcc_opn {abi : IsaAbi} (lend : List String) :
    ∀ (ann : List (FI × List String)) (m : LprogGpRealloc.Cur) (cs : List String)
      (acc out : List FI), goAcc lend m ann cs acc abi = some out →
      ∀ j ∈ out, j ∈ acc ∨ ∃ p ∈ ann, j.opn = p.1.opn := by
  intro ann
  induction ann with
  | nil =>
    intro m cs acc out h j hj
    cases cs with
    | cons _ _ => simp [goAcc] at h
    | nil =>
      simp only [goAcc] at h
      split at h
      · cases h; exact Or.inl (by simpa using hj)
      · cases h
  | cons p rest ih =>
    intro m cs acc out h j hj
    obtain ⟨i, la⟩ := p
    have lift : (j ∈ acc ∨ ∃ p ∈ rest, j.opn = p.1.opn) →
        j ∈ acc ∨ ∃ p ∈ (i, la) :: rest, j.opn = p.1.opn :=
      fun h' => h'.imp id fun ⟨p, hp, he⟩ => ⟨p, List.mem_cons_of_mem _ hp, he⟩
    have push : ∀ (c' : String) (args : List LOperand),
        (j ∈ (⟨i.ii, c', i.opn, args⟩ : FI) :: acc ∨ ∃ p ∈ rest, j.opn = p.1.opn) →
        j ∈ acc ∨ ∃ p ∈ (i, la) :: rest, j.opn = p.1.opn := by
      intro c' args h'
      rcases h' with h' | ⟨p, hp, he⟩
      · rcases List.mem_cons.mp h' with rfl | h'
        · exact Or.inr ⟨(i, la), List.mem_cons_self, rfl⟩
        · exact Or.inl h'
      · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, he⟩
    cases cs with
    | nil => simp [goAcc] at h
    | cons c cs =>
      simp only [goAcc] at h
      split at h
      · split at h
        · split at h
          · split at h
            · exact lift (ih _ cs acc out h j hj)
            · split at h
              · exact lift (ih _ cs acc out h j hj)
              · split at h
                · exact push _ _ (ih _ cs _ out h j hj)
                · cases h
          · cases h
        · split at h
          · exact push _ _ (ih _ cs _ out h j hj)
          · cases h
      · cases h

theorem reallocRun_opn {abi : IsaAbi} (lend : List String) (is : List FI) :
    ∀ j ∈ reallocRun lend is abi, ∃ i ∈ is, j.opn = i.opn := by
  unfold reallocRun reallocWith
  split
  · rename_i out hf
    obtain ⟨cs, _, hcs⟩ := List.exists_of_findSome?_eq_some hf
    intro j hj
    rcases goAcc_opn lend _ {} cs [] out hcs j hj with h | ⟨p, hp, he⟩
    · cases h
    · exact ⟨p.1, annotate_fst lend is p hp, he⟩
  · intro j hj
    exact ⟨j, hj, rfl⟩

/-- Every instruction of the re-allocated body is an instruction of the body or no `ZEROARR`
    or `STOREIMM`: a re-allocated run carries the mnemonics of fragment instructions. -/
theorem reallocBody_mem_arrImm {abi : IsaAbi} (res : List String) (body : Lcmd) :
    ∀ li ∈ reallocBody res body abi, li ∈ body ∨ isArrImmB li.li_i = false := by
  unfold reallocBody
  dsimp only
  have hspec := (LprogGpReallocCfg.pieces_spec
    (recog := LcmdCopyPropagate.isRecognizedOpn) body).2.2.1
  have hbar := (LprogGpReallocCfg.pieces_spec
    (recog := LcmdCopyPropagate.isRecognizedOpn) body).2.2.2
  generalize pieces body LcmdCopyPropagate.isRecognizedOpn = ps at hspec hbar
  induction ps with
  | nil => intro li hli; simp at hli
  | cons p ps ih =>
    intro li hli
    have ih' := ih (fun is h => hspec is (List.mem_cons_of_mem _ h))
      (fun l h => hbar l (List.mem_cons_of_mem _ h))
    rw [List.foldr_cons] at hli
    split at hli
    · rename_i is
      rcases List.mem_append.1 hli with hli | hli
      · right
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hli
        obtain ⟨i, hi, he⟩ := reallocRun_opn _ is j hj
        obtain ⟨li', -, hf⟩ := hspec is List.mem_cons_self i hi
        have hz := PhysImgFold.fragOf?_opn_ne hf
        simp [FI.toL, FI.toR, isArrImmB, he, hz.1, hz.2]
      · exact ih' li hli
    · rename_i li'
      rcases List.mem_cons.1 hli with rfl | hli
      · exact Or.inl (hbar _ List.mem_cons_self).1
      · exact ih' li hli

/-- **`cellBaseFreeB_reallocBody`**: the register re-allocation keeps `cellBaseFreeB`: every
    instruction of a re-allocated run has direct sources and is no `ZEROARR` or `STOREIMM`. -/
theorem cellBaseFreeB_reallocBody {abi : IsaAbi} (res : List String)
    {b : Lcmd} (h : cellBaseFreeB b = true) :
    cellBaseFreeB (reallocBody res b abi) = true := by
  have h0 := cellBaseFreeB_iff.mp h
  refine cellBaseFreeB_iff.mpr fun j hj => ?_
  rcases LprogGpReallocCT.reallocBody_mem res b j hj with hj' | hd
  · exact h0 j hj'
  · rcases reallocBody_mem_arrImm res b j hj with hj' | hai
    · exact h0 j hj'
    · refine cellOk_of_noIdxFst (fun ds o x y sc ss he => ?_) hai
      rw [he] at hd
      simp [AllocCTPreservation.linstrRDirect, AllocCTPreservation.isIndexed] at hd

/-- A mnemonic whose ABI-stripped form is `ANDN` has no flag-only base. -/
theorem flagOnly_of_stripAbiTag_andn {opn : String} (h : stripAbiTag opn = "ANDN") :
    x86Data.flagOnly (tieBase opn) = false := by
  have hp : ['A', 'N', 'D', 'N'] <+: opn.toList := by
    unfold stripAbiTag at h
    split at h
    · have hl : opn.toList.takeWhile (· != ':') = ['A', 'N', 'D', 'N'] := by
        simpa using congrArg String.toList h
      exact hl ▸ List.takeWhile_prefix _
    · unfold stripWidthTag at h
      split at h
      · have hl : opn.toList.takeWhile (· != '^') = ['A', 'N', 'D', 'N'] := by
          simpa using congrArg String.toList h
        exact hl ▸ List.takeWhile_prefix _
      · split at h
        · have hl : opn.toList.dropLast.dropLast.dropLast = ['A', 'N', 'D', 'N'] := by
            have := congrArg String.toList h
            simpa using this
          exact hl ▸ ((List.dropLast_prefix _).trans ((List.dropLast_prefix _).trans
            (List.dropLast_prefix _)))
        · subst h; exact List.prefix_refl _
  have key : tieBase opn ≠ "CMP" ∧ tieBase opn ≠ "TEST" := by
    obtain ⟨t, ht⟩ := hp
    have ht' : (tieBase opn).toList =
        'A' :: 'N' :: 'D' :: 'N' :: t.takeWhile (fun c => c != ':' && c != '^') := by
      unfold tieBase; rw [String.toList_ofList, ← ht]; simp [List.takeWhile]
    constructor <;> intro he <;> rw [he] at ht' <;> simp at ht'
  simp [key.1, key.2]

/-- A re-allocated fragment instruction of a tied input is tied: the destination location `c`
    respects the printer shape of the input, and is the destination itself when that is no
    location. -/
theorem tiedI_rename {abi : IsaAbi} {m : Cur} {i : FI} {c : String}
    (hs : shapeOk m i c abi = true) (ht : TiedI i.toL) (hc : isLoc i.d abi = false → c = i.d) :
    TiedI (FI.toL ⟨i.ii, c, i.opn, i.srcs.map (fun o => renOp m o abi)⟩) := by
  intro d opn x c' he hf
  simp only [FI.toL, FI.toR, LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq,
    and_true] at he
  obtain ⟨rfl, rfl, hsr⟩ := he
  rcases hsrc : i.srcs with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;>
    simp only [hsrc, List.map_cons, List.map_nil, List.cons.injEq, reduceCtorEq, and_false,
      and_true, List.map_nil] at hsr
  obtain ⟨ha, -⟩ := hsr
  unfold shapeOk shapeOf at hs
  split_ifs at hs with h1 h2 h3
  · simp [hsrc] at h1
  · simp only [Bool.and_eq_true, beq_iff_eq] at h2
    rw [flagOnly_of_stripAbiTag_andn h2.1] at hf
    cases hf
  · simp only [Bool.and_eq_true, hsrc, List.head?_cons] at h3
    have ha' : a = .reg i.d := by simpa using h3.2
    subst ha'
    dsimp only at hs
    simp only [beq_iff_eq] at hs
    simp only [renOp] at ha
    split_ifs at ha with hl
    · simp only [LOperand.reg.injEq] at ha
      rw [hs, ha]
    · simp only [LOperand.reg.injEq] at ha
      rw [← ha]
      exact (hc (by simpa using hl)).symm
  · dsimp only at hs
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hs
    obtain ⟨rfl, hr⟩ := hs
    have hti := ht i.d i.opn
    cases a with
    | reg y =>
      have hy : x = y := by
        simp only [renOp] at ha
        split_ifs at ha with hl
        · simp only [LOperand.reg.injEq] at ha
          rw [← ha]
          exact hr y (by simp [FI.reads, hsrc, opReads, hl])
        · simpa using ha.symm
      subst hy
      exact hti x b (by simp [FI.toL, FI.toR, hsrc]) hf
    | _ => simp [renOp] at ha

/-- **The check of a run keeps tied compares**: every output instruction of `goAcc` is an
    accumulated one or a renamed input instruction. -/
theorem goAcc_tiedI {abi : IsaAbi} (lend : List String) :
    ∀ (ann : List (FI × List String)) (m : Cur) (cs : List String) (acc out : List FI),
      goAcc lend m ann cs acc abi = some out → (∀ j ∈ acc, TiedI j.toL) →
        (∀ p ∈ ann, TiedI p.1.toL) → ∀ j ∈ out, TiedI j.toL := by
  intro ann
  induction ann with
  | nil =>
    intro m cs acc out h hacc _ j hj
    cases cs with
    | cons _ _ => simp [goAcc] at h
    | nil =>
      simp only [goAcc] at h
      split at h
      · cases h; exact hacc j (by simpa using hj)
      · cases h
  | cons p rest ih =>
    intro m cs acc out h hacc hann
    obtain ⟨i, la⟩ := p
    have hi : TiedI i.toL := hann (i, la) (by simp)
    have hrest : ∀ p ∈ rest, TiedI p.1.toL := fun p hp => hann p (by simp [hp])
    cases cs with
    | nil => simp [goAcc] at h
    | cons c cs =>
      simp only [goAcc] at h
      have push : ∀ c', shapeOk m i c' abi = true → (isLoc i.d abi = false → c' = i.d) →
          ∀ j ∈ (⟨i.ii, c', i.opn, i.srcs.map (fun o => renOp m o abi)⟩ : FI) :: acc,
            TiedI j.toL := by
        intro c' hs hc j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact tiedI_rename hs hi hc
        · exact hacc j hj
      split at h
      · split at h
        · rename_i hloc
          split at h
          · rename_i hok
            simp only [Bool.and_eq_true] at hok
            split at h
            · exact ih _ cs acc out h hacc hrest
            · split at h
              · exact ih _ cs acc out h hacc hrest
              · split at h
                · exact ih _ cs _ out h (push c hok.2 (by simp [hloc])) hrest
                · cases h
          · cases h
        · rename_i hloc
          split at h
          · rename_i hok
            exact ih _ cs _ out h (push i.d hok (fun _ => rfl)) hrest
          · cases h
      · cases h

/-- **The re-allocation of a run keeps tied compares.** -/
theorem reallocRun_tiedI {abi : IsaAbi} (lend : List String) (is : List FI)
    (h : ∀ i ∈ is, TiedI i.toL) : ∀ j ∈ reallocRun lend is abi, TiedI j.toL := by
  unfold reallocRun reallocWith
  split
  · rename_i out hf
    obtain ⟨cs, _, hcs⟩ := List.exists_of_findSome?_eq_some hf
    exact goAcc_tiedI lend _ {} cs [] out hcs (by simp)
      (fun p hp => h p.1 (annotate_fst lend is p hp))
  · exact h

/-- **`flagTiedB_reallocBody`**: the register re-allocation keeps `flagTiedB`: a flag-only
    compare has the fixed printer shape, so its names are kept. -/
theorem flagTiedB_reallocBody {abi : IsaAbi} (res : List String) {b : Lcmd}
    (h : flagTiedB b = true) : flagTiedB (reallocBody res b abi) = true := by
  have h0 := flagTiedB_iff.mp h
  have hps : ∀ p ∈ pieces b, ∀ j ∈ Piece.toLcmd p, TiedI j := by
    intro p hp j hj
    exact h0 j (by
      rw [← pieces_flatten b]
      exact List.mem_flatten.mpr ⟨Piece.toLcmd p, List.mem_map_of_mem hp, hj⟩)
  refine flagTiedB_iff.mpr ?_
  unfold reallocBody
  dsimp only
  generalize pieces b = ps at hps
  induction ps with
  | nil => intro j hj; simp at hj
  | cons p ps ih =>
    intro j hj
    have ih' := ih (fun q hq => hps q (List.mem_cons_of_mem _ hq))
    rw [List.foldr_cons] at hj
    split at hj
    · rename_i is
      rcases List.mem_append.mp hj with hj | hj
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
        exact reallocRun_tiedI _ is (fun i hi => hps (.run is) (by simp) i.toL
          (List.mem_map_of_mem hi)) k hk
      · exact ih' j hj
    · rename_i li
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hps (.bar j) (by simp) j (by simp [Piece.toLcmd])
      · exact ih' j hj

end Realloc

/-! ## 6. The two-address legalisation and the compare-spill reload -/

section Print

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi IsaData)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (legalizeInstr twoAddrBody
  scratchRoute isRegOrImm)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload (cmpReload cmpReloadI)

/-- Every instruction of the legalisation of `i` is `i` or has no register-indexed first
    source. -/
theorem legalizeInstr_noIdxFst (ok : Bool) (i : Linstr) (I : IsaData) :
    ∀ r ∈ legalizeInstr ok i I, r = i ∨ NoIdxFst r := by
  unfold legalizeInstr
  split
  · rename_i d opn a b hi
    split
    · split
      · simp
      · split
        · split <;> simp [NoIdxFst]
        · split
          · simp
          · rename_i hreg
            have ha : ∀ x y sc, a ≠ .arrIdx x y sc := by
              rintro x y sc rfl; simp [isRegOrImm] at hreg
            split
            · simp [NoIdxFst, ha]
            · split
              · simp [NoIdxFst]
              · split
                · split <;> simp [NoIdxFst, scratchRoute, ha]
                · simp
    · simp
  · simp

/-- The instruction is an operation under the mnemonic `o`, a move mnemonic, or the move
    `MOV` tagged at a width `w`. -/
def MnOf (o : String) (r : LinstrR) : Prop :=
  ∃ ds o' ss, r = .Lopn ds o' ss ∧
    (o' = o ∨ o' ∈ PhysImgEmit.movMnems ∨ ∃ w, o' = withWidthTag w "MOV")

/-- Every instruction of the two-address legalisation of an operation under `o` is an
    operation under `o` or a move mnemonic. -/
theorem legalizeInstr_mnOf (ok : Bool) (i : Linstr) {ds : List LOperand} {o : String}
    {ss : List LOperand} (hi : i.li_i = .Lopn ds o ss) :
    ∀ r ∈ legalizeInstr ok i x86Data, MnOf o r.li_i := by
  have hself : MnOf o i.li_i := ⟨ds, o, ss, hi, Or.inl rfl⟩
  have hmov : ∀ m, TwoAddrLegalize.movFor o = some m →
      m ∈ PhysImgEmit.movMnems ∨ ∃ w, m = withWidthTag w "MOV" := by
    intro m hm
    rcases TwoAddrLegalize.movFor_cases hm with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨w, -, rfl⟩
    · exact Or.inl (by decide +kernel)
    · exact Or.inl (by decide +kernel)
    · exact Or.inr ⟨w, rfl⟩
  intro r hr
  unfold legalizeInstr at hr
  split at hr
  · rename_i d opn a b he
    rw [hi] at he
    cases he
    split at hr
    · split at hr
      · simp only [List.mem_singleton] at hr; subst hr; exact hself
      · rename_i m hm
        have hm' := hmov m hm
        split at hr
        · split at hr
          · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, _, _, rfl, Or.inl rfl⟩
          · simp only [List.mem_singleton] at hr; subst hr; exact hself
        · split at hr
          · simp only [List.mem_singleton] at hr; subst hr; exact hself
          · split at hr
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl
              · exact ⟨_, _, _, rfl, Or.inr hm'⟩
              · exact ⟨_, _, _, rfl, Or.inl rfl⟩
            · split at hr
              · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, _, _, rfl, Or.inl rfl⟩
              · split at hr
                · split at hr <;>
                    simp only [scratchRoute, List.mem_cons, List.not_mem_nil, or_false] at hr <;>
                    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
                    exact ⟨_, _, _, rfl, by
                      first
                      | exact Or.inl rfl
                      | exact Or.inr hm'
                      | exact Or.inr (Or.inl (by simp [PhysImgEmit.movMnems]))⟩
                · simp only [List.mem_singleton] at hr; subst hr; exact hself
    · simp only [List.mem_singleton] at hr; subst hr; exact hself
  · simp only [List.mem_singleton] at hr; subst hr; exact hself

/-- The x86 two-address legalisation leaves a `ZEROARR` or `STOREIMM` alone. -/
theorem legalizeInstr_arrImm (ok : Bool) (i : Linstr) (hai : isArrImmB i.li_i = true) :
    legalizeInstr ok i x86Data = [i] := by
  unfold legalizeInstr
  split
  · rename_i d opn a b he
    rw [he] at hai
    have ho : opn = "ZEROARR" ∨ opn = "STOREIMM" := by simpa [isArrImmB] using hai
    have ht : TwoAddrLegalize.needsTie opn b = false := by
      unfold TwoAddrLegalize.needsTie
      rw [Bool.or_eq_false_iff, Bool.and_eq_false_iff]
      rcases ho with rfl | rfl <;> exact ⟨by decide +kernel, Or.inl (by decide +kernel)⟩
    simp only [ht, Bool.false_and, Bool.false_eq_true, ite_false]
  · rfl

/-- **`cellBaseFreeB_twoAddrBody`**: the x86 two-address legalisation keeps `cellBaseFreeB`. -/
theorem cellBaseFreeB_twoAddrBody {b : Lcmd} (h : cellBaseFreeB b = true) :
    cellBaseFreeB (twoAddrBody b x86Data) = true := by
  have h0 := cellBaseFreeB_iff.mp h
  refine cellBaseFreeB_iff.mpr fun r hr => ?_
  obtain ⟨i, hi, hr⟩ := List.mem_flatMap.mp hr
  by_cases hai : isArrImmB i.li_i = true
  · rw [legalizeInstr_arrImm _ i hai, List.mem_singleton] at hr
    subst hr
    exact h0 r hi
  rcases legalizeInstr_noIdxFst _ i x86Data r hr with rfl | hn
  · exact h0 r hi
  · refine cellOk_of_noIdxFst hn ?_
    cases hil : i.li_i with
    | Lopn ds o ss =>
      obtain ⟨ds', o', ss', he, ho⟩ := legalizeInstr_mnOf _ i hil r hr
      rw [he]
      rcases ho with rfl | ho
      · rw [hil] at hai
        simpa [isArrImmB] using hai
      · rcases ho with ho | ⟨w, rfl⟩
        · simp only [PhysImgEmit.movMnems, List.mem_cons, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl | rfl | rfl <;> simp [isArrImmB]
        · simp (disch := decide +kernel) [isArrImmB, withWidthTag_ne_of_tagSepFree]
    | _ =>
      have : ∀ ok, legalizeInstr ok i x86Data = [i] := fun ok => by unfold legalizeInstr; rw [hil]
      rw [this, List.mem_singleton] at hr
      subst hr
      rw [hil]; rfl

/-- **`cellBaseFreeB_cmpReload`**: the compare-spill reload keeps `cellBaseFreeB`. -/
theorem cellBaseFreeB_cmpReload {abi : IsaAbi} {b : Lcmd} (h : cellBaseFreeB b = true) :
    cellBaseFreeB (cmpReload b abi) = true := by
  have h0 := cellBaseFreeB_iff.mp h
  refine cellBaseFreeB_iff.mpr fun r hr => ?_
  obtain ⟨i, hi, hr⟩ := List.mem_flatMap.mp hr
  unfold cmpReloadI at hr
  split at hr
  · rename_i opn d s heq
    have hc : stripWidthTag opn = "CMP" := by
      unfold CmpSpillReload.spillCmp? at heq
      split at heq
      · split_ifs at heq with hc
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨rfl, -, -⟩ := heq
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact hc.1.1.1
      · cases heq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      refine cellOk_of_noIdxFst (fun ds o x y sc ss he => by simp at he) ?_
    · simp only [isArrImmB, CmpSpillReload.movOf]
      split_ifs <;> rfl
    · simp only [isArrImmB, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
      constructor <;> rintro rfl <;> revert hc <;> decide +kernel
  · rw [List.mem_singleton] at hr
    subst hr
    exact h0 r hi

end Print

/-! ## 7. The conjuncts on the printed chain -/

section Chain

open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (IsaAbi)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (optimizeBasicBlocks
  splitStraightRuns bodyAllModeled)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ConstIndexFold (foldIndexedBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogGpRealloc (reallocBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (twoAddrBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CmpSpillReload (cmpReload)

/-- **`cellBaseFreeB_sublist`**: a sublist keeps `cellBaseFreeB`. -/
theorem cellBaseFreeB_sublist {b b' : Lcmd} (hs : b'.Sublist b) (h : cellBaseFreeB b = true) :
    cellBaseFreeB b' = true :=
  cellBaseFreeB_iff.mpr (forall_of_sublist hs (cellBaseFreeB_iff.mp h))

/-- **`flagTiedB_sublist`**: a sublist keeps `flagTiedB`. -/
theorem flagTiedB_sublist {b b' : Lcmd} (hs : b'.Sublist b) (h : flagTiedB b = true) :
    flagTiedB b' = true :=
  flagTiedB_iff.mpr (forall_of_sublist hs (flagTiedB_iff.mp h))

/-- **`copyNoSlotB_sublist`**: a sublist keeps `copyNoSlotB`. -/
theorem copyNoSlotB_sublist {b b' : Lcmd} (hs : b'.Sublist b)
    (h : copyNoSlotB slotArr b = true) : copyNoSlotB slotArr b' = true :=
  copyNoSlotB_iff.mpr (forall_of_sublist hs (copyNoSlotB_iff.mp h))

/-- **Conjunct 4 of the side conditions.** When every array slot is a `qsave.` slot, no 64-bit
    copy of the allocated body `b0` reads an array slot, no operand of a `MULXHI` of `b0` is an
    array slot, `b1` is a sublist of the fusion of `b0` (the dead-write elimination
    `deadWriteRet` gives one), and no 64-bit move of `b1` is between two memory names, no
    64-bit copy of the optimised `b1` reads an array slot. -/
theorem copyNoSlotB_postOpt
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {b0 b1 : Lcmd}
    (h : copyNoSlotB slotArr b0 = true) (hm : mulHiNoSlotB slotArr b0 = true)
    (hs : b1.Sublist (fuseMulHiBody b0 true)) (hh : memMovFreeB b1 = true) :
    copyNoSlotB slotArr (optimizeBasicBlocks b1) = true :=
  copyNoSlotB_optimizeBasicBlocks hq
    (copyNoSlotB_sublist hs (copyNoSlotB_fuseMulHiBody true hq h hm)) hh

/-- **Conjunct 5 of the side conditions.** When no indexed access of the allocated body `b0`
    has a cell base and `b1` is a sublist of the fusion of `b0`, no indexed access of the
    optimised `b1` has a cell base. -/
theorem cellBaseFreeB_postOpt {b0 b1 : Lcmd} (h : cellBaseFreeB b0 = true)
    (hs : b1.Sublist (fuseMulHiBody b0 true)) :
    cellBaseFreeB (optimizeBasicBlocks b1) = true :=
  cellBaseFreeB_optimizeBasicBlocks (cellBaseFreeB_sublist hs (cellBaseFreeB_fuseMulHiBody true h))

/-- **Conjunct 9 of the side conditions.** When no indexed access of the allocated body `b0`
    has a cell base and `b1` is a sublist of the fusion of `b0`, no indexed access of the
    printed body of `b1` (the optimiser, the fold, the re-allocation, the two-address
    legalisation and the compare-spill reload) has a cell base. -/
theorem cellBaseFreeB_printedChain {abi : IsaAbi} (res : List String) {b0 b1 : Lcmd}
    (h : cellBaseFreeB b0 = true) (hs : b1.Sublist (fuseMulHiBody b0 true)) :
    cellBaseFreeB
      (cmpReload (twoAddrBody (reallocBody res (foldIndexedBody (optimizeBasicBlocks b1)))) abi)
      = true :=
  cellBaseFreeB_cmpReload (cellBaseFreeB_twoAddrBody (cellBaseFreeB_reallocBody res
    (cellBaseFreeB_foldIndexedBody (cellBaseFreeB_postOpt h hs))))

/-- **Conjunct 7 of the side conditions.** When every flag-only compare of the allocated body
    `b0` with a register first source is tied and `b1` is a sublist of the fusion of `b0`,
    so is every such compare of the re-allocated, folded and optimised `b1`. -/
theorem flagTiedB_reallocStage (res : List String) {b0 b1 : Lcmd} (h : flagTiedB b0 = true)
    (hs : b1.Sublist (fuseMulHiBody b0 true)) :
    flagTiedB (reallocBody res (foldIndexedBody (optimizeBasicBlocks b1))) = true :=
  flagTiedB_reallocBody res (flagTiedB_foldIndexedBody (flagTiedB_optimizeBasicBlocks
    (flagTiedB_sublist hs (flagTiedB_fuseMulHiBody true h))))

end Chain

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSidePass
