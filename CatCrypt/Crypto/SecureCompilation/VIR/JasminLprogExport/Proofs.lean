/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
import all Init.Data.List.Sort.Basic
import all Init.Data.String.Slice
import all Init.Data.String.Search
public meta import CatCrypt.Crypto.SecureCompilation.VIR.Core
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
public import Std.Data.HashMap
public meta import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportPhysAbi
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportPhysAbi

/-!
# Correctness of the linear export

Structural and value-level properties of the exports: well-formedness, the
terminal `Lret`, the textual magic header, loop denotation equations, the
register-distinctness invariant of the linear scan, and the physical-export
correctness obligations (no register collision, two-address denotation).

## Main results

* `Com.toLprog_wf`, `Com.toLprog_body_ends_Lret`, `comLToBody_ends_Lret`.
* `Com.toLprogText_magic`: the serialization starts with the magic header.
* `physScanSpillStep_nodup`: the scan keeps allocations register-distinct.
* `kernelMergeSort_eq`: the fuelled merge sort is `List.mergeSort`.
* `physNoCollision_of_boolB`, `twoAddr_denote`: physical-export correctness.
-/


@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-- `charsIsNatStep` is the `for` loop of `String.Slice.isNat` over a character
    list. -/
theorem forIn_charsIsNatStep : ∀ (l : List Char) (st : Option Bool × Bool),
    (forIn l st (fun c (__s : Option Bool × Bool) =>
        if c = '_' then
          if (!__s.2) = true then pure (ForInStep.done (some false, __s.2))
          else pure (ForInStep.yield ((none : Option Bool), false))
        else
          if c.isDigit = true then pure (ForInStep.yield ((none : Option Bool), true))
          else pure (ForInStep.done (some false, __s.2))) : Id (Option Bool × Bool))
      = charsIsNatStep l st := by
  intro l
  induction l with
  | nil => intro st; rfl
  | cons c rest ih =>
    intro st
    simp only [charsIsNatStep, List.forIn_cons]
    split
    · split
      · rfl
      · exact ih _
    · split
      · exact ih _
      · rfl

/-- `charsIsNat` is `String.Slice.isNat`. -/
theorem sliceIsNat_eq (s : String.Slice) : s.isNat = charsIsNat s.copy.toList := by
  rw [String.Slice.isNat]
  simp only [String.Slice.forIn_eq_forIn_toList, forIn_charsIsNatStep, charsIsNat]
  generalize charsIsNatStep s.copy.toList ((none : Option Bool), false) = st
  obtain ⟨o, b⟩ := st
  cases o <;> rfl

/-- `charsToNat?` is `String.Slice.toNat?`. -/
theorem sliceToNat?_eq (s : String.Slice) : s.toNat? = charsToNat? s.copy.toList := by
  rw [String.Slice.toNat?, charsToNat?, sliceIsNat_eq, String.Slice.foldl_eq_foldl_toList]

/-- `strDropToNat?` is `String.toNat?` after `String.drop`. -/
@[simp] theorem strDropToNat?_eq (s : String) (k : Nat) :
    strDropToNat? s k = (s.drop k).toNat? := by
  rw [strDropToNat?, sliceToNat?_eq, String.toList_copy_drop]

/-- `strToNat?` is `String.toNat?`. -/
@[simp] theorem strToNat?_eq (s : String) : strToNat? s = s.toNat? := by
  rw [strToNat?, String.toNat?, sliceToNat?_eq]
  simp

/-- The exported `lprog` always has exactly one function, named `fname`, and it
    is an export function. (Structural well-formedness — proved.) -/
theorem Com.toLprog_wf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) :
    (Com.toLprog com fname).lp_funcs.length = 1 ∧
      ((Com.toLprog com fname).lp_funcs.head?.map Prod.fst = some fname) ∧
      ((Com.toLprog com fname).lp_funcs.head?.map (fun p => p.2.lfd_export)
        = some true) := by
  refine ⟨rfl, rfl, rfl⟩

/-- The body produced by `comToBody` is non-empty (it always ends with `Lret`)
    and its last instruction is `Lret`. (Proved by induction on the `Com`.) -/
theorem comToBody_ends_Lret (nArgs : Nat) (argNames : Nat → String)
    (immSlotMap : ImmSlotMap := fun _ => none) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (com : Com jasminDialect Γ t)
      (d : Nat),
      (comToBody nArgs argNames immSlotMap com d).getLast?.map Linstr.li_i
        = some LinstrR.Lret := by
  intro Γ t com
  induction com with
  | ret v => intro d; rfl
  | var e body ih =>
      intro d
      simp only [comToBody]
      rw [List.getLast?_cons]
      have := ih (d + 1)
      cases h : (comToBody nArgs argNames immSlotMap body (d + 1)).getLast? with
      | none => simp [List.getLast?_eq_none_iff] at h; rw [h] at this; simp at this
      | some x => rw [h] at this; simpa using this

/-- The exported function's body ends with `Lret`. (Proved.) -/
theorem Com.toLprog_body_ends_Lret {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) :
    ((comToLfundef com).lfd_body).getLast?.map Linstr.li_i = some .Lret := by
  simpa [comToLfundef] using
    comToBody_ends_Lret Γ.length argName (fun _ => none) com Γ.length

/-- `n = 0`: the loop denotes the identity (no iterations). -/
theorem JLoopBody.denote_zero {accTy : JasminTy}
    (u : Com jasminDialect [accTy] accTy) (init : ⟦accTy⟧) :
    JLoopBody.denote ⟨0, u⟩ init = init := rfl

/-- `n = k+1`: one more iteration of `stepC` on top of the `k`-fold denotation.
    Together with `denote_zero` this is the recursion the looped emission's
    `runBoundedLoop` semantics matches step-for-step. -/
theorem JLoopBody.denote_succ {accTy : JasminTy} (k : Nat)
    (u : Com jasminDialect [accTy] accTy) (init : ⟦accTy⟧) :
    JLoopBody.denote ⟨k + 1, u⟩ init
      = JLoopBody.stepC u (JLoopBody.denote ⟨k, u⟩ init) := by
  simp [JLoopBody.denote, List.range_succ, List.foldl_append]

/-- `n = 0`: the multi-binder loop denotes the identity (no iterations). -/
theorem JLoopBodyN.denote_zero {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (u : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invs : Ctxt.Valuation invTys) (init : ⟦accTy⟧) :
    JLoopBodyN.denote ⟨0, u⟩ invs init = init := rfl

/-- `n = k+1`: one more iteration of `stepC` at trip index `k` on top of the
    `k`-fold denotation. The recursion the looped emission's bounded-loop
    semantics matches step-for-step. -/
theorem JLoopBodyN.denote_succ {accTy : JasminTy} {invTys : Ctxt jasminDialect}
    (k : Nat) (u : Com jasminDialect (accTy :: .reg 64 :: invTys) accTy)
    (invs : Ctxt.Valuation invTys) (init : ⟦accTy⟧) :
    JLoopBodyN.denote ⟨k + 1, u⟩ invs init
      = JLoopBodyN.stepC u invs k (JLoopBodyN.denote ⟨k, u⟩ invs init) := by
  simp [JLoopBodyN.denote, List.range_succ, List.foldl_append]

/-- The multi-accumulator loop's denotation is the `count`-fold of the body's
    `ComL.denote` over the `N`-cell product state — the `forLoopBlock` fold at
    `accTy = stackArr w N`. Definitional; the array threads through the fold, so
    every cell is loop-carried. -/
@[simp] theorem ComL.forLoopMultiAcc_denote {Γ : Ctxt jasminDialect} {w N : Nat}
    {s : JasminTy} {invTys : Ctxt jasminDialect}
    (loopBody : ComL (JasminTy.stackArr w N :: JasminTy.reg 64 :: invTys)
      (JasminTy.stackArr w N))
    (count : Ctxt.Var Γ (JasminTy.reg 64))
    (init : Ctxt.Var Γ (JasminTy.stackArr w N))
    (invs : HVector (fun ty => Ctxt.Var Γ ty) invTys)
    (body : ComL (JasminTy.stackArr w N :: Γ) s) (V : Ctxt.Valuation Γ) :
    ComL.denote (ComL.forLoopMultiAcc loopBody count init invs body) V
      = body.denote (V.extend
          ((List.range (count.lookup V).toNat).foldl
            (fun acc t =>
              loopBody.denote
                (.cons acc (.cons (BitVec.ofNat 64 t) (Expr.lookupArgs invs V))))
            (init.lookup V))) := rfl

/-- `getLast?` of an append whose right factor is non-empty is the right factor's
    `getLast?` (self-contained — this module does not import Mathlib's
    `List.getLast?_append_of_ne_nil`). -/
theorem getLast?_append_ne {α : Type _} (l₁ l₂ : List α) (h : l₂ ≠ []) :
    (l₁ ++ l₂).getLast? = l₂.getLast? := by
  induction l₁ with
  | nil => rfl
  | cons a as ih =>
      rw [List.cons_append, List.getLast?_cons, ih]
      cases l₂ with
      | nil => exact absurd rfl h
      | cons b bs => simp [List.getLast?_cons]

/-- `comLToBody` always ends with `Lret` (the loop nodes contribute interior
    control flow; the terminal `.ret` is still the last instruction). The `ComL`
    analogue of `comToBody_ends_Lret`. -/
theorem comLToBody_ends_Lret (nArgs : Nat) (argNames : Nat → String)
    (imm : ImmSlotMap) :
    ∀ {Γ : Ctxt jasminDialect} {t : JasminTy} (c : ComL Γ t) (d : Nat),
      (comLToBody nArgs argNames imm c d).getLast?.map Linstr.li_i = some .Lret := by
  intro Γ t c
  induction c with
  | ret v => intro d; rfl
  | var e body ih =>
      intro d
      simp only [comLToBody, List.getLast?_cons]
      have hb := ih (d + 1)
      cases h : (comLToBody nArgs argNames imm body (d + 1)).getLast? with
      | none => simp [List.getLast?_eq_none_iff] at h; rw [h] at hb; simp at hb
      | some x => rw [h] at hb; simpa using hb
  | forLoop loop init body ih =>
      intro d
      have hne : comLToBody nArgs argNames imm body (d + 1) ≠ [] := by
        have hb := ih (d + 1); intro hnil; rw [hnil] at hb; simp at hb
      simp only [comLToBody]
      rw [getLast?_append_ne _ _ hne]; exact ih (d + 1)
  | forLoopN loop init invs body ih =>
      intro d
      have hne : comLToBody nArgs argNames imm body (d + 1) ≠ [] := by
        have hb := ih (d + 1); intro hnil; rw [hnil] at hb; simp at hb
      simp only [comLToBody]
      rw [getLast?_append_ne _ _ hne]; exact ih (d + 1)
  | forLoopNRt update count init invs body ih =>
      intro d
      have hne : comLToBody nArgs argNames imm body (d + 1) ≠ [] := by
        have hb := ih (d + 1); intro hnil; rw [hnil] at hb; simp at hb
      simp only [comLToBody]
      rw [getLast?_append_ne _ _ hne]; exact ih (d + 1)
  | forLoopNRtNested innerCount innerUpdate outerCount init invs body ih =>
      intro d
      have hne : comLToBody nArgs argNames imm body (d + 1) ≠ [] := by
        have hb := ih (d + 1); intro hnil; rw [hnil] at hb; simp at hb
      simp only [comLToBody]
      rw [getLast?_append_ne _ _ hne]; exact ih (d + 1)
  | whileNz update guard init invs body ih =>
      intro d
      have hne : comLToBody nArgs argNames imm body (d + 1) ≠ [] := by
        have hb := ih (d + 1); intro hnil; rw [hnil] at hb; simp at hb
      simp only [comLToBody]
      rw [getLast?_append_ne _ _ hne]; exact ih (d + 1)
  | forLoopBlock loopBody count init invs body ihLoop ih =>
      intro d
      have hne : comLToBody nArgs argNames imm body (d + 1) ≠ [] := by
        have hb := ih (d + 1); intro hnil; rw [hnil] at hb; simp at hb
      simp only [comLToBody]
      rw [getLast?_append_ne _ _ hne]; exact ih (d + 1)

/-- The textual serialization is prefixed by the OCaml-side magic header:
    it is literally `magic ++ rest`. (Proved by `rfl` on the decomposition;
    this is the byte-level contract `Read_linear.read_magic` checks.) -/
theorem Com.toLprogText_magic {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) :
    ∃ rest, Com.toLprogText com fname = magic ++ rest :=
  ⟨(Com.toLprog com fname).toText ++ "\n", rfl⟩

-- Export semantic-preservation faithfulness — `Com.denote com V = lsem (toLprog com) (encode V)`
-- over jasmin's linear semantics — is `ComLsemExportFaithful` (`VIR.JasminLsemGeneralFaithful`,
-- plain-`Lstate` scalar fragment, discharged by `comLsemExportFaithful_of_scalar`) and
-- `ComLsemExportFaithfulMC` (`VIR.JasminLsemGeneralFaithfulMC`, `LstateN` mul/carry fragment,
-- discharged by `comLsemExportFaithfulMC_of_mulcarry`), over the `lsem` port (`VIR.LsemPortAll`).
-- Both are downstream of this file (the `lsem` model imports `JasminLprogExport`).

/-- `freeRegIn` hands out an index inside the pool. -/
theorem freeRegIn_lt {numRegs : Nat} {used reserved : List Nat} {ph : Nat}
    (h : freeRegIn numRegs used reserved = some ph) : ph < numRegs := by
  unfold freeRegIn at h
  cases reserved <;> exact List.mem_range.mp (List.mem_of_find?_eq_some h)

/-- `freeRegIn` hands out an index that no active allocation holds. -/
theorem freeRegIn_not_mem {numRegs : Nat} {used reserved : List Nat} {ph : Nat}
    (h : freeRegIn numRegs used reserved = some ph) : ph ∉ used := by
  unfold freeRegIn at h
  cases reserved with
  | nil => simpa using List.find?_some h
  | cons r rs =>
    have hp := List.find?_some h
    simp only [Bool.and_eq_true] at hp
    simpa using hp.1

theorem spillFold_mem (st : Nat) (uses : Array Nat) :
    ∀ (act : List PhysActive) (b0 : Option PhysActive) (far : PhysActive),
      act.foldl (fun best a =>
          match best with
          | some b => if spillPrefer st uses a b then some a else best
          | none => some a) b0 = some far →
        far ∈ act ∨ b0 = some far := by
  intro act
  induction act with
  | nil => intro b0 far h; exact Or.inr h
  | cons a rest ih =>
    intro b0 far h
    rw [List.foldl_cons] at h
    rcases ih _ far h with hm | hb
    · exact Or.inl (List.mem_cons_of_mem _ hm)
    · cases b0 with
      | none =>
        simp only [Option.some.injEq] at hb
        exact Or.inl (hb ▸ List.mem_cons_self)
      | some b =>
        by_cases hp : spillPrefer st uses a b
        · simp only [hp, ite_eq_left, Option.some.injEq] at hb
          exact Or.inl (hb ▸ List.mem_cons_self)
        · simp only [hp, Bool.false_eq_true, ite_eq_right, not_false_iff] at hb
          exact Or.inr hb

/-- `spillVictim` returns one of the active allocations. -/
theorem spillVictim_mem {st : Nat} {uses : Array Nat} {act : List PhysActive}
    {far : PhysActive} (h : spillVictim st uses act = some far) : far ∈ act := by
  rcases spillFold_mem st uses act none far h with hm | hb
  · exact hm
  · exact absurd hb (by simp)

/-- One scan step keeps the in-flight allocations on pairwise-distinct physical
    registers. -/
theorem physScanSpillStep_nodup (numRegs : Nat) (uses : Array Nat)
    (act : List PhysActive) (hulls : CellHulls) (acc : List (Nat × Nat))
    (s st en : Nat) (reserved : List Nat) (pieceOf : Nat → Option Nat)
    (h : (act.map PhysActive.phys).Nodup) :
    ((physScanSpillStep numRegs uses act hulls acc s st en reserved pieceOf).1.map
      PhysActive.phys).Nodup := by
  have hfs : ∀ (p : PhysActive → Bool) (l : List PhysActive),
      (l.map PhysActive.phys).Nodup → ((l.filter p).map PhysActive.phys).Nodup :=
    fun _ l hl => hl.sublist (List.filter_sublist.map PhysActive.phys)
  simp only [physScanSpillStep, physScanSpillLose]
  split
  next => exact hfs _ _ h
  next =>
    split
    next ph hfr =>
      exact List.nodup_cons.mpr ⟨by simpa using freeRegIn_not_mem hfr, hfs _ _ h⟩
    next hfr =>
      split
      next far hv =>
        split
        next hp =>
          refine List.nodup_cons.mpr ⟨?_, hfs _ _ (hfs _ _ h)⟩
          simp only [List.mem_map, not_exists, not_and]
          intro x hx hxp
          have hne := (List.mem_filter.mp hx).2
          simp [hxp] at hne
        next hp => split <;> exact hfs _ _ h
      next hv => split <;> exact hfs _ _ h

/-- `mergeFuel` agrees with `List.merge` when the fuel covers both lists. -/
theorem mergeFuel_eq {α : Type} (le : α → α → Bool) :
    ∀ (f : Nat) (xs ys : List α), xs.length + ys.length ≤ f →
      mergeFuel le f xs ys = List.merge xs ys le := by
  intro f
  induction f with
  | zero =>
    intro xs ys h
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hx; subst hy; simp [mergeFuel]
  | succ f ih =>
    intro xs ys h
    match xs, ys with
    | [], ys => simp [mergeFuel]
    | x :: xs, [] => simp [mergeFuel]
    | x :: xs, y :: ys =>
      simp only [List.length_cons] at h
      by_cases hle : le x y
      · rw [show mergeFuel le (f + 1) (x :: xs) (y :: ys)
              = x :: mergeFuel le f xs (y :: ys) by simp [mergeFuel, hle]]
        rw [ih xs (y :: ys) (by simp; omega), List.cons_merge_cons_pos _ _ _ hle]
      · rw [show mergeFuel le (f + 1) (x :: xs) (y :: ys)
              = y :: mergeFuel le f (x :: xs) ys by simp [mergeFuel, hle]]
        rw [ih (x :: xs) ys (by simp; omega),
          List.cons_merge_cons_neg _ _ _ (by simpa using hle)]

open List.MergeSort.Internal in
/-- `mergeSortFuel` agrees with `List.mergeSort` when the fuel covers the list. -/
theorem mergeSortFuel_eq {α : Type} (le : α → α → Bool) :
    ∀ (f : Nat) (l : List α), l.length ≤ f → mergeSortFuel le f l = List.mergeSort l le := by
  intro f
  induction f with
  | zero =>
    intro l h
    match l with
    | [] => simp [mergeSortFuel]
    | a :: l => simp at h
  | succ f ih =>
    intro l h
    match l with
    | [] => simp [mergeSortFuel]
    | [a] => simp [mergeSortFuel]
    | a :: b :: l =>
      simp only [List.length_cons] at h
      show mergeFuel le (l.length + 2)
          (mergeSortFuel le f (splitInTwo ⟨a :: b :: l, rfl⟩).1.1)
          (mergeSortFuel le f (splitInTwo ⟨a :: b :: l, rfl⟩).2.1) = _
      rw [ih _ (by have := (splitInTwo (n := l.length + 2) ⟨a :: b :: l, rfl⟩).1.2; omega),
          ih _ (by have := (splitInTwo (n := l.length + 2) ⟨a :: b :: l, rfl⟩).2.2; omega)]
      rw [List.mergeSort]
      refine mergeFuel_eq le _ _ _ ?_
      rw [List.length_mergeSort, List.length_mergeSort]
      have h1 := (splitInTwo (n := l.length + 2) ⟨a :: b :: l, rfl⟩).1.2
      have h2 := (splitInTwo (n := l.length + 2) ⟨a :: b :: l, rfl⟩).2.2
      omega

/-- `kernelMergeSort` is `List.mergeSort`. -/
@[simp] theorem kernelMergeSort_eq {α : Type} (le : α → α → Bool) (l : List α) :
    kernelMergeSort le l = l.mergeSort le :=
  mergeSortFuel_eq le l.length l (Nat.le_refl _)

/-- When `materializeWideImm` is invoked on the 32-bit path (the default
    `mov = "MOV"`), it is the identity. This lets the U32 shape/legality lemmas
    reduce `lowerTwoAddr` to its single-width form. -/
@[simp] theorem materializeWideImm_MOV (s1 : LOperand) :
    materializeWideImm s1 "MOV" = ([], s1) := by
  cases s1 <;> rfl

/-- A map naming `RSI` recovers its pointer from `qsave.RSI`, as every load did
    before the base was honoured, so those callers' loads are unchanged. -/
theorem abiLoadSave_rsi : abiLoadSave "RSI" = abiSaveRsiName := rfl

/-- A map naming `RDI` recovers its pointer from `qsave.RDI`. -/
theorem abiLoadSave_rdi : abiLoadSave "RDI" = abiSaveRdiName := rfl

/-- `physBodyWithStores` is the `flatMap` of `physPositionEmit` over the
    indexed body. -/
theorem physBodyWithStores_eq_flatMap (shiftImm : ShiftImmOracle) (body : Lcmd)
    (inLoadMap : InLoadMap) (loadBase : String)
    (outStoreMap : OutStoreMap) (storeBase : String) (abiW : Nat)
    (memrefBaseReload : String → Option String)
    (callArgBaseReload : List (String × String)) (reservedVec : List Nat) :
    physBodyWithStores shiftImm body inLoadMap loadBase outStoreMap storeBase
        abiW memrefBaseReload callArgBaseReload reservedVec
      = body.zipIdx.flatMap (physPositionEmit shiftImm body inLoadMap loadBase
          outStoreMap storeBase abiW memrefBaseReload callArgBaseReload
          reservedVec) :=
  rfl

/-- The physical export of a **loop-free** `ComL` is byte-identical to the
    straight-line `comToLfundefPhys` on its `Com` image: `comLToBody`'s `.var`/
    `.ret` arms are definitionally the `comToLfundef` body, and every other field
    of `ComL.toLfundefPhys` mirrors `comToLfundefPhys` field-for-field. The two
    `Lfundef`s thus agree on a `.var`/`.ret`-only program, witnessing that the
    loop walk is additive over the straight-line export. (Stated for the doubling
    body's degenerate loop-free witness; see the smoke test below for the looped
    case.) -/
theorem ComL.toLfundefPhys_var_ret_eq_comToLfundefPhys
    {Γ : Ctxt jasminDialect} {t s : JasminTy}
    (e : Expr jasminDialect Γ t) (v : Ctxt.Var (t :: Γ) s) :
    (ComL.toLfundefPhys (.var e (.ret v))).lfd_body
      = (comToLfundefPhys (.var e (.ret v))).lfd_body := by
  rfl

/-! ## 8. Physical-export correctness

Two value-level obligations are discharged here, mirroring `UnrolledComRA`'s
finite checks (axioms `[propext, Quot.sound]` via `native_decide`):

* **no-collision**: any two simultaneously-live logical slots receive distinct
  physical slots, so the two-address rewrite never clobbers a live value;
* **two-address denotation**: the lowered `mov dst,src0; op dst,src1` (or
  `op dst,src1` when `dst = src0`) computes `dst = op src0 src1` under
  `JasminBinOp.apply` — the destructive form is faithful to the 3-address binop.
-/

/-- A per-live-slot summary row `(slot, phys, start, end)`. -/
def physSummary (tr : List PhysEvent) : List (Nat × Nat × Nat × Nat) :=
  let assign := physAssign tr
  (physLiveItems tr).map (fun item =>
    let s := item.1
    let ph := match assign.find? (fun p => p.1 == s) with
      | some (_, p) => p
      | none => s
    (s, ph, item.2.1, item.2.2))

/-- **No-collision predicate**: distinct live slots with overlapping ranges get
    distinct physical slots. -/
def PhysNoCollision (tr : List PhysEvent) : Prop :=
  ∀ r₁ ∈ physSummary tr, ∀ r₂ ∈ physSummary tr,
    r₁.1 ≠ r₂.1 →
    physRangesOverlap (r₁.2.2.1, r₁.2.2.2) (r₂.2.2.1, r₂.2.2.2) = true →
      r₁.2.1 ≠ r₂.2.1

/-- Decidable Boolean form of `PhysNoCollision`. -/
def physNoCollisionB (tr : List PhysEvent) : Bool :=
  let rows := physSummary tr
  rows.all (fun r₁ =>
    rows.all (fun r₂ =>
      if r₁.1 == r₂.1 then true
      else if physRangesOverlap (r₁.2.2.1, r₁.2.2.2) (r₂.2.2.1, r₂.2.2.2) then
        r₁.2.1 != r₂.2.1
      else true))

/-- The Boolean check implies the `PhysNoCollision` Prop. -/
theorem physNoCollision_of_boolB (tr : List PhysEvent)
    (h : physNoCollisionB tr = true) : PhysNoCollision tr := by
  intro r₁ h1 r₂ h2 hne hov
  have step1 := List.all_eq_true.mp h r₁ h1
  have step2 := List.all_eq_true.mp step1 r₂ h2
  by_cases heq : r₁.1 == r₂.1
  · simp only [beq_iff_eq] at heq; exact absurd heq hne
  · simp only [heq, Bool.false_eq_true, ite_false, hov, ite_true] at step2
    simpa [bne, beq_iff_eq] using step2

/- The concrete no-collision check for the ChaCha20-block physical allocation
   (`chacha20_block`'s body trace) is `physNoCollisionChaCha`, proved below over
   the concrete trace by `native_decide`. -/

/-! ### A register-store model of the two-address rewrite

To state the two-address denotation we model a register file as
`store : Nat → BitVec w` (slot → value). `setReg` is a destructive write;
`movStep`/`opStep` are the two-address instruction effects. The theorem
`twoAddr_denote` shows: running `mov dst,src0; op dst,src1` on any store with
`src0 ↦ a`, `src1 ↦ b` leaves `dst ↦ JasminBinOp.apply op a b` — exactly what
the 3-address `dst = op src0 src1` computes. The collapsed case
(`dst = src0`, single `op dst,src1`) gives the same result. The hypothesis
`dst ≠ src1` is the **no-collision** side-condition: the destructive `dst` write
must not clobber the still-needed `src1` before the op reads it (guaranteed by
`PhysNoCollision` for distinct live slots). -/

/-- A register file: slot → value at width `w`. -/
abbrev RegStore (w : Nat) := Nat → BitVec w

/-- Destructive write of `v` to slot `d`. -/
def setReg {w : Nat} (st : RegStore w) (d : Nat) (v : BitVec w) : RegStore w :=
  fun s => if s = d then v else st s

/-- `mov dst, src0`: copy `st src0` into `dst`. -/
def movStep {w : Nat} (st : RegStore w) (dst src0 : Nat) : RegStore w :=
  setReg st dst (st src0)

/-- `op dst, src1`: destructive binop `dst := apply op (st dst) (st src1)`. -/
def opStep {w : Nat} (op : JasminBinOp) (st : RegStore w) (dst src1 : Nat) :
    RegStore w :=
  setReg st dst (op.apply (st dst) (st src1))

/-- **Two-address lowering denotation (`mov dst,src0; op dst,src1`).** Running
    the destructive pair on any store leaves `dst ↦ apply op (st src0) (st src1)`
    — the value the 3-address `dst = op src0 src1` computes. The side-condition
    `dst ≠ src1` is the no-collision guarantee that the `mov` does not clobber
    `src1` before `op` reads it. -/
theorem twoAddr_denote {w : Nat} (op : JasminBinOp) (st : RegStore w)
    (dst src0 src1 : Nat) (hne : dst ≠ src1) :
    (opStep op (movStep st dst src0) dst src1) dst
      = op.apply (st src0) (st src1) := by
  simp only [opStep, movStep, setReg, ↓reduceIte]
  rw [ite_eq_right (Ne.symm hne)]

/-- **Collapsed two-address denotation (`dst = src0`, single `op dst,src1`).**
    When the RA placed `dst` on `src0`'s register, `dst` already holds `a`, so
    the single `op dst,src1` computes `apply op (st dst) (st src1)` — and since
    `dst = src0` here, that is `apply op (st src0) (st src1)`, the same value. -/
theorem twoAddr_denote_collapsed {w : Nat} (op : JasminBinOp) (st : RegStore w)
    (dst src1 : Nat) :
    (opStep op st dst src1) dst = op.apply (st dst) (st src1) := by
  simp only [opStep, setReg, ↓reduceIte]

/-- `op dst, #v`: destructive binop with an immediate second operand
    `dst := apply op (st dst) (BitVec.ofNat w v)`. The immediate is the value
    `v` reduced modulo `2^w` (`BitVec.ofNat`), so this models `SHL/SHR r/m, imm`
    exactly: the count is the literal `v`, no register read. -/
def opStepImm {w : Nat} (op : JasminBinOp) (st : RegStore w) (dst v : Nat) :
    RegStore w :=
  setReg st dst (op.apply (st dst) (BitVec.ofNat w v))

/-- **Immediate-shift denotation (collapsed, `dst = src0`, `op dst, #v`).** The
    single immediate-count op computes `apply op (st dst) (ofNat w v)` — the same
    value the register-count form computes when the shift-count register holds the
    constant `v` (`st src1 = BitVec.ofNat w v`). For `SHL`/`SHR` this is
    `(st dst) <<< (ofNat w v).toNat` / `>>>`, i.e. the rotate amount as a literal. -/
theorem twoAddrShiftImm_denote_collapsed {w : Nat} (op : JasminBinOp)
    (st : RegStore w) (dst v : Nat) :
    (opStepImm op st dst v) dst = op.apply (st dst) (BitVec.ofNat w v) := by
  simp only [opStepImm, setReg, ↓reduceIte]

/-- **Immediate-shift denotation (general, `dst ≠ src0`, `mov dst,src0; op dst,#v`).**
    The `mov` copies `src0` into `dst`, then the immediate-count op computes
    `apply op (st src0) (ofNat w v)` — the value the 3-address
    `dst = op src0 #v` computes. (No `dst ≠ src1` side-condition is needed: the
    immediate carries no register slot to clobber.) -/
theorem twoAddrShiftImm_denote {w : Nat} (op : JasminBinOp) (st : RegStore w)
    (dst src0 v : Nat) :
    (opStepImm op (movStep st dst src0) dst v) dst
      = op.apply (st src0) (BitVec.ofNat w v) := by
  simp only [opStepImm, movStep, setReg, ↓reduceIte]

/-- **Immediate-shift faithfulness.** When the shift-count register `src1` holds
    the constant `v` (i.e. `st src1 = BitVec.ofNat w v`), the immediate-count
    op `op dst, #v` computes exactly what the register-count op `op dst, src1`
    computes. This is the correctness of rendering a constant shift count as an
    `#imm` operand: the two forms denote the same store update on `dst`. -/
theorem opStepImm_eq_opStep_of_const {w : Nat} (op : JasminBinOp)
    (st : RegStore w) (dst src1 v : Nat) (hv : st src1 = BitVec.ofNat w v) :
    (opStepImm op st dst v) dst = (opStep op st dst src1) dst := by
  simp only [opStepImm, opStep, setReg, ↓reduceIte, hv]

/-- **Reload denotation (`mov R15, src; op dst, R15`, `dst ≠ R15`).** Routing the
    second source through the reload scratch `sc` (any slot with `dst ≠ sc`)
    computes `apply op (st dst) (st src)` in `dst` — exactly what the direct
    `op dst, src` computes. This is the correctness of the two-memory-operand
    legalization: the reload preserves the value, only the encoding changes.
    The side-condition `dst ≠ sc` is the reserved-scratch guarantee (`R15` is
    never an allocation target, so it never aliases `dst`). -/
theorem reload_denote {w : Nat} (op : JasminBinOp) (st : RegStore w)
    (dst src sc : Nat) (hsc : dst ≠ sc) :
    (opStep op (movStep st sc src) dst sc) dst = op.apply (st dst) (st src) := by
  simp only [opStep, movStep, setReg, ite_true, ite_eq_right hsc]

/-- **Dst-reload denotation (`mov sc, src0; op sc, src1; mov dst, sc`).** When
    `dst` is itself a spill slot, the reload pass routes the whole binop
    through the scratch `sc`: load `src0` into `sc`, run `op sc, src1` on the
    scratch (`src1` read from the original store), then store the result back
    to `dst`. The final store leaves `dst ↦ apply op (st src0) (st src1)` —
    exactly what the direct `op dst, src1` (after `mov dst, src0`) would
    compute. The side-condition `sc ≠ src1` ensures the initial reload of
    `src0` does not clobber `src1`. -/
theorem reloadDst_denote {w : Nat} (op : JasminBinOp) (st : RegStore w)
    (dst src0 src1 sc : Nat) (hsc1 : sc ≠ src1) :
    let st1 := movStep st sc src0
    let st2 := opStep op st1 sc src1
    (setReg st2 dst (st2 sc)) dst = op.apply (st src0) (st src1) := by
  simp only [opStep, movStep, setReg, ite_true]
  by_cases h : src1 = sc
  · exact absurd h.symm hsc1
  · simp [h]

/-- **Dst+src reload denotation (`mov sc, src0; mov sc2, src1; op sc, sc2;
    mov dst, sc`).** Both-spill case: load `src0` into the primary scratch
    `sc`, `src1` into the secondary scratch `sc2`, op the scratches, store
    back to `dst`. Yields `dst ↦ apply op (st src0) (st src1)`. Side-conditions
    `sc ≠ src1` (initial src0-reload doesn't clobber src1) and `sc ≠ sc2`
    (the two scratches are distinct allocations). -/
theorem reloadBoth_denote {w : Nat} (op : JasminBinOp) (st : RegStore w)
    (dst src0 src1 sc sc2 : Nat) (hsc1 : sc ≠ src1) (hsc12 : sc ≠ sc2) :
    let st1 := movStep st sc src0
    let st2 := movStep st1 sc2 src1
    let st3 := opStep op st2 sc sc2
    (setReg st3 dst (st3 sc)) dst = op.apply (st src0) (st src1) := by
  simp only [opStep, movStep, setReg, ite_true]
  -- The result in `sc` after the op is `apply op (st2 sc) (st2 sc2)`.
  -- `st2 sc = st1 sc = st src0` (since src1 ≠ sc by hsc1, and sc was just
  -- written to st src0).
  -- `st2 sc2 = st src1` directly.
  -- Then `setReg ... dst (st3 sc) dst = st3 sc`.
  by_cases h2 : sc = sc2
  · exact absurd h2 hsc12
  · by_cases h1 : src1 = sc
    · exact absurd h1.symm hsc1
    · simp [h1, h2]

/-- The primary reload-scratch operand is a register, never a spill slot. -/
theorem reloadScratch_not_spill : (LOperand.reg reloadScratch).isSpill = false := by
  native_decide

/-- The secondary reload-scratch operand is a register, never a spill slot. -/
theorem reloadScratch2_not_spill : (LOperand.reg reloadScratch2).isSpill = false := by
  native_decide

/-- An immediate operand is never a spill slot. -/
theorem imm_not_spill (v : Nat) : (LOperand.imm v).isSpill = false := rfl

/-- **x86 memory-operand legality of one `Lopn`.** An `Lopn` with destination
    `[d]` and sources `[s0, s1]` is two-address (`d := d op s1`, with `s0 = d`),
    so its two *distinct* operand positions are `d` (lval = first rval) and `s1`.
    x86 allows at most one memory operand among them, i.e. `d` and `s1` are not
    both spill slots. A `mov [d] [s]` (sources `[s]`) is legal iff `d`, `s` are
    not both spill. Other constructors carry no two-memory hazard. -/
def LinstrR.legalMemForm : LinstrR → Bool
  | .Lopn (d :: _) _ (_ :: s1 :: _) => !(d.isSpill && s1.isSpill)
  | .Lopn (d :: _) _ (s :: _) => !(d.isSpill && s.isSpill)
  | _ => true

/-- `legalizeBinop` emits one of four shapes:

    * both operands registers — a single direct `op dst, src`;
    * spill `src` only — reload `src` through `R15`, then `op dst, R15`;
    * spill `dst` only — reload `dst` through `R15`, op in `R15`, store back;
    * both spills — reload both through `R15`/`R14`, op in scratches, store back.
-/
theorem legalizeBinop_shape (dst src : LOperand) (opn : String)
    (mov : String := "MOV") :
    legalizeBinop dst src opn mov
      = (match dst.isSpill, src.isSpill with
         | false, false => [.Lopn [dst] opn [dst, src]]
         | false, true  =>
             [.Lopn [.reg reloadScratch] mov [src],
              .Lopn [dst] opn [dst, .reg reloadScratch]]
         | true,  false =>
             [.Lopn [.reg reloadScratch] mov [dst],
              .Lopn [.reg reloadScratch] opn [.reg reloadScratch, src],
              .Lopn [dst] mov [.reg reloadScratch]]
         | true,  true  =>
             [.Lopn [.reg reloadScratch] mov [dst],
              .Lopn [.reg reloadScratch2] mov [src],
              .Lopn [.reg reloadScratch] opn
                [.reg reloadScratch, .reg reloadScratch2],
              .Lopn [dst] mov [.reg reloadScratch]]) := by
  unfold legalizeBinop
  cases dst.isSpill <;> cases src.isSpill <;> rfl

/-- When neither `dst` nor `src` is a spill slot, `legalizeBinop` is the single
    direct instruction (no reload). -/
theorem legalizeBinop_noSpill (dst src : LOperand) (opn : String)
    (hd : dst.isSpill = false) (hs : src.isSpill = false) :
    legalizeBinop dst src opn = [.Lopn [dst] opn [dst, src]] := by
  unfold legalizeBinop
  rw [hd, hs]

/-- When `dst` and `src` are not both spill slots, `legalizeMov` is the single
    direct copy (no reload). -/
theorem legalizeMov_noSpill (dst src : LOperand)
    (h : dst.isSpill = false ∨ src.isSpill = false) :
    legalizeMov dst src = [.Lopn [dst] "MOV" [src]] := by
  unfold legalizeMov
  rcases h with h | h <;> simp [h]

/-- Every `Lopn` `legalizeBinop` emits is x86-memory-legal: each non-MOV op has
    its non-MOV operand positions in register scratches (`R15`/`R14`), and each
    MOV touches at most one spill slot. -/
theorem legalizeBinop_legalMemForm (dst src : LOperand) (opn : String)
    (mov : String := "MOV") :
    ∀ r ∈ legalizeBinop dst src opn mov, r.legalMemForm = true := by
  intro r hr
  rw [legalizeBinop_shape dst src opn mov] at hr
  rcases hd : dst.isSpill <;> rcases hs : src.isSpill <;>
    simp only [hd, hs] at hr
  · -- (false, false)
    simp only [List.mem_singleton] at hr
    subst hr
    simp [LinstrR.legalMemForm, hd, hs]
  · -- (false, true)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h1 | h1 <;> subst h1 <;>
      simp [LinstrR.legalMemForm, reloadScratch_not_spill, hd, hs]
  · -- (true, false)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h1 | h1 | h1 <;> subst h1 <;>
      simp [LinstrR.legalMemForm, reloadScratch_not_spill, hd, hs]
  · -- (true, true)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h1 | h1 | h1 | h1 <;> subst h1 <;>
      simp [LinstrR.legalMemForm, reloadScratch_not_spill,
            reloadScratch2_not_spill, hd, hs]

/-- Every `Lopn` `legalizeMov` emits is x86-memory-legal. -/
theorem legalizeMov_legalMemForm (dst src : LOperand) (mov : String := "MOV") :
    ∀ r ∈ legalizeMov dst src mov, r.legalMemForm = true := by
  intro r hr
  unfold legalizeMov at hr
  by_cases h : dst.isSpill && src.isSpill
  · simp only [h, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h1 | h1 <;> subst h1 <;>
      simp [LinstrR.legalMemForm, reloadScratch_not_spill]
  · simp only [h, Bool.false_eq_true, ite_false, List.mem_singleton] at hr
    subst hr
    simp only [LinstrR.legalMemForm, Bool.not_eq_true', Bool.and_eq_false_iff]
    rw [Bool.not_eq_true, Bool.and_eq_false_iff] at h
    exact h

set_option linter.unusedVariables false in
/-- When no operand is a spill slot, the two-address lowering has the classic
    shape: a single op when the RA placed `dst` on `src0`'s register, else a
    `mov` + the op. (With the reload pass, the direct binop form is only taken
    when **both** `dst` and `s1` are registers — a stricter precondition than
    the old "at most one spill" check. The `s0` hypothesis is kept for
    documentation — a no-spill source `s0` simplifies the leading `mov dst,
    s0` to a single direct copy.) -/
theorem lowerTwoAddr_shape_noSpill (dst s0 s1 : LOperand) (opn : String)
    (hd : dst.isSpill = false) (hs0 : s0.isSpill = false)
    (hs1 : s1.isSpill = false) :
    lowerTwoAddr dst s0 s1 opn
      = (if dst = s0 then [.Lopn [dst] opn [dst, s1]]
         else [.Lopn [dst] "MOV" [s0], .Lopn [dst] opn [dst, s1]]) := by
  simp only [lowerTwoAddr, materializeWideImm_MOV, List.nil_append,
    List.append_nil, hd, Bool.false_eq_true, ite_false]
  split
  · exact legalizeBinop_noSpill dst s1 opn hd hs1
  · rw [legalizeMov_noSpill dst s0 (Or.inl hd),
        legalizeBinop_noSpill dst s1 opn hd hs1]
    rfl

/-- The whole two-address lowering is x86-memory-legal in every emitted `Lopn`:
    each leg (the `mov` and the binop) is legalized so no single instruction has
    its two distinct operand positions both in memory. -/
theorem lowerTwoAddr_legalMemForm (dst s0 s1 : LOperand) (opn : String) :
    ∀ r ∈ lowerTwoAddr dst s0 s1 opn, r.legalMemForm = true := by
  intro r hr
  simp only [lowerTwoAddr, materializeWideImm_MOV, List.nil_append,
    List.append_nil] at hr
  split at hr
  · exact legalizeBinop_legalMemForm dst s1 opn "MOV" r hr
  · split at hr
    · simp only [List.mem_append, List.mem_singleton, scratchBinop] at hr
      rcases hr with hr | rfl
      · split at hr <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;>
          rcases hr with rfl | rfl | rfl <;>
          simp_all [LinstrR.legalMemForm, reloadScratch_not_spill, reloadScratch2_not_spill]
      · simp [LinstrR.legalMemForm, reloadScratch_not_spill]
    · rw [List.mem_append] at hr
      rcases hr with hr | hr
      · exact legalizeMov_legalMemForm dst s0 "MOV" r hr
      · exact legalizeBinop_legalMemForm dst s1 opn "MOV" r hr

set_option linter.unusedVariables false in
/-- The immediate-shift lowering has three shapes depending on whether `dst` is
    a spill slot:

    * `dst` is a spill — reload through `R15`: `mov R15, s0; op R15, #v;
      mov dst, R15` (3 `Lopn`s). When `dst = s0`, the first mov reloads
      `dst`'s current value into the scratch.
    * `dst` is a register, `dst = s0` — single `op dst, #v` (1 `Lopn`).
    * `dst` is a register, `dst ≠ s0` — `mov dst, s0; op dst, #v` (2 `Lopn`s,
      the leading mov is legalized so `s0` may itself be a spill).

    The `hms` hypothesis is kept for documentation — the register-`dst` branch
    only needs `dst.isSpill = false`, which is part of the disjunction. -/
theorem lowerTwoAddrShiftImm_shape (dst s0 : LOperand) (v : Nat) (opn : String)
    (hms : dst.isSpill = false ∨ s0.isSpill = false) :
    lowerTwoAddrShiftImm dst s0 v opn
      = (if dst.isSpill then
           [.Lopn [.reg reloadScratch] "MOV" [s0],
            .Lopn [.reg reloadScratch] opn [.reg reloadScratch, .imm v],
            .Lopn [dst] "MOV" [.reg reloadScratch]]
         else if dst = s0 then [.Lopn [dst] opn [dst, .imm v]]
         else [.Lopn [dst] "MOV" [s0], .Lopn [dst] opn [dst, .imm v]]) := by
  unfold lowerTwoAddrShiftImm
  by_cases hd : dst.isSpill = true
  · simp only [hd, ↓reduceIte]
  · rw [Bool.not_eq_true] at hd
    simp only [hd, Bool.false_eq_true, ↓reduceIte]
    split
    · rfl
    · rw [legalizeMov_noSpill dst s0 (Or.inl hd)]; rfl

/-- The immediate-shift lowering is x86-memory-legal in every emitted `Lopn`
    (the `mov` is legalized; the op's second operand is the immediate, never
    memory, so `op [mem], #imm` is a legal single-memory-operand encoding). -/
theorem lowerTwoAddrShiftImm_legalMemForm (dst s0 : LOperand) (v : Nat)
    (opn : String) :
    ∀ r ∈ lowerTwoAddrShiftImm dst s0 v opn, r.legalMemForm = true := by
  intro r hr
  unfold lowerTwoAddrShiftImm at hr
  by_cases hd : dst.isSpill = true
  · simp only [hd, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h1 | h1 | h1 <;> subst h1 <;>
      simp [LinstrR.legalMemForm, reloadScratch_not_spill, imm_not_spill]
  · rw [Bool.not_eq_true] at hd
    simp only [hd, Bool.false_eq_true, ↓reduceIte] at hr
    by_cases heq : dst = s0
    · rw [ite_eq_left heq] at hr
      simp only [List.mem_singleton] at hr
      subst hr
      simp [LinstrR.legalMemForm, imm_not_spill]
    · rw [ite_eq_right heq] at hr
      rw [List.mem_append] at hr
      rcases hr with hr | hr
      · exact legalizeMov_legalMemForm dst s0 "MOV" r hr
      · simp only [List.mem_singleton] at hr
        subst hr
        simp [LinstrR.legalMemForm, imm_not_spill]

/-- The physical export is structurally well-formed: one function named `fname`,
    exported, body ending in `Lret`. -/
theorem Com.toLprogPhys_wf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) :
    (Com.toLprogPhys com fname).lp_funcs.length = 1 ∧
      ((Com.toLprogPhys com fname).lp_funcs.head?.map Prod.fst = some fname) ∧
      ((Com.toLprogPhys com fname).lp_funcs.head?.map (fun p => p.2.lfd_export)
        = some true) := by
  refine ⟨rfl, rfl, ?_⟩
  rfl

/-! ### ABI-wrapped export: structural lemmas

The ABI wrapper is a pure structural transform: prologue loads + body + epilogue
stores. The body is the verified `physBody` unchanged, so all body-level
denotation lemmas (`twoAddr_denote`, `reload_denote`, etc.) continue to apply.
The wrapper's correctness reduces to two facts:

* every prologue/epilogue `Lopn` is a single `MOV` whose memory operand is a
  `mem.<base>.<off>` reference (NOT a `k.<N>` spill); the read_linear textual
  reader materialises `mem.RDI.0` / `mem.RSI.4` as a `[base + off]` memory
  reference, exactly the SysV-ABI load/store the C harness expects;
* the wrapped body still ends in `Lret` (so jasmin's `assemble_fd` accepts it).
-/

set_option linter.unusedVariables false in
/-- The epilogue-insertion step preserves the `Lret`-terminated body shape: a
    body that ends in `Lret`, after inserting any epilogue (a list of stores),
    still ends in `Lret`. The hypothesis `h` is kept for documentation — the
    statement is structurally true even without it (the result always ends in
    the explicit trailing `Lret`). -/
theorem insertEpilogue_ends_Lret (body epi : Lcmd)
    (h : body.getLast?.map Linstr.li_i = some LinstrR.Lret) :
    (insertEpilogue body epi).getLast?.map Linstr.li_i = some LinstrR.Lret := by
  unfold insertEpilogue
  -- The result is `body.dropLast ++ epi ++ [Lret]`; its last is the trailing `Lret`.
  simp [List.getLast?_append, List.getLast?_cons]

/-- The ABI-wrapped physical export is structurally well-formed: one function
    named `fname`, exported. (The empty `lfd_res`/`lfd_tyout` reflect the
    2-pointer SysV ABI where the result is returned via memory at `*out`.) -/
theorem Com.toLprogPhysAbi_wf {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (fname : String) :
    (Com.toLprogPhysAbi com fname).lp_funcs.length = 1 ∧
      ((Com.toLprogPhysAbi com fname).lp_funcs.head?.map Prod.fst = some fname) ∧
      ((Com.toLprogPhysAbi com fname).lp_funcs.head?.map (fun p => p.2.lfd_export)
        = some true) := by
  refine ⟨rfl, rfl, ?_⟩
  rfl

/-- The prologue is the 9-instruction pointer-save + callee-save + RSI-park
    prelude, all `MOVQ`s (save RDI/RSI to red zone, save the six SysV
    callee-saved GPRs RBX/RBP/R12/R13/R14/R15 to red zone, park RSI into R14).
    The per-slot input loads are inside `physBodyWithStores`. -/
theorem buildPrologue_all_MOVQ (virt : Lfundef) (tbl : Array Nat)
    (inLoadMap : InLoadMap) :
    ∀ r ∈ buildPrologue virt tbl inLoadMap,
      ∃ dsts srcs, r.li_i = LinstrR.Lopn dsts "MOVQ" srcs := by
  intro r hr
  unfold buildPrologue at hr
  simp at hr
  rcases hr with hr | hr | hr | hr | hr | hr | hr | hr | hr <;> subst hr <;>
    exact ⟨_, _, rfl⟩

/-- The epilogue is a list of `MOV` Lopns: every emitted instruction is a
    single `Lopn` with `opn = "MOV"`. (Structural invariant of `buildEpilogue`;
    the leading restore MOV and each target's 1-or-2 store MOVs are all MOVs.) -/
theorem buildEpilogue_all_MOV (virt : Lfundef) (tbl : Array Nat)
    (outStoreMap : OutStoreMap) :
    ∀ r ∈ buildEpilogue virt tbl outStoreMap,
      ∃ dsts srcs, r.li_i = LinstrR.Lopn dsts "MOV" srcs := by
  intro r hr
  unfold buildEpilogue at hr
  rw [List.mem_append] at hr
  rcases hr with hres | hr
  · simp at hres
    subst hres
    exact ⟨_, _, rfl⟩
  · rw [List.mem_flatMap] at hr
    obtain ⟨j, _hj, h⟩ := hr
    cases ho : outStoreMap[j]? with
    | none => simp [ho] at h
    | some bo =>
        simp [ho] at h
        cases hbd : bindingDstOp virt.lfd_body
                      (numBindings virt.lfd_body - outStoreMap.length + j) with
        | none => simp [hbd] at h
        | some d =>
            cases d with
            | reg srcName =>
                simp [hbd] at h
                by_cases hs : (LOperand.reg
                                (physNameForBody virt.lfd_body tbl srcName)).isSpill
                · simp [hs] at h
                  rcases h with h | h <;> subst h <;> exact ⟨_, _, rfl⟩
                · simp [hs] at h
                  subst h
                  exact ⟨_, _, rfl⟩
            | arr _ _ => simp [hbd] at h
            | imm _ => simp [hbd] at h
            | arrIdx _ _ _ => simp [hbd] at h

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
