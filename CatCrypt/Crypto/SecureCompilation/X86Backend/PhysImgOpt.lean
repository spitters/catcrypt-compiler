/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSched
public import CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold

/-!
# The image class under the basic-block optimiser

The basic-block optimiser `LprogOptPipeline.optimizeBasicBlocks` runs, on each run of modeled
straight-line instructions, the passes `elimReloads`, `reloadElimBody`, `scheduleBody`,
`copyPropagateBody` and `loadCSE`. This module proves that each pass keeps the image class
`physImgB` of the whole body when it rewrites one segment `b` of a body `A ++ b ++ C`, under a
decidable side condition on `b`, and so does the optimiser.

A pass that deletes instructions keeps the class when every deleted instruction is transparent to
the reload scan (`physImgB_ctx_kept_of_transparent`), or when the scan of every kept access passes
it (`physImgB_kept_of_passThru`). A pass that rewrites instructions at fixed positions keeps the
class when the reload scan of its output dominates that of its input (`physImgB_of_dom`); the
forward environments of `loadCSE` and of the move propagation carry this dominance as an
invariant (`LoadInv`, `PropInv`). The dead-move elimination deletes only moves into names that no
reload scan carries across them, because every carried general-purpose name is live
(`deLive_claim`).

## Main results

* `physImgB_elimReloads_ctx`, `physImgB_elimReloads`: the redundant-reload elimination, under
  `elimSideB`.
* `physImgB_reloadElimBody_ctx`, `physImgB_reloadElimBody`: the spill-reload elimination, under
  `reloadPairSideB`.
* `physImgB_scheduleBody_ctx`: the scheduler.
* `physImgB_deadElimBody_ctx`, `physImgB_propagateAux_ctx`, `physImgB_copyPropagateBody_ctx`,
  `physImgB_copyPropagateBody`: the copy propagation, on a modeled body.
* `physImgB_loadCSE_ctx`, `physImgB_loadCSE`: the load CSE, under `loadSideB`.
* `physImgB_optRunBody_ctx`, `physImgB_optimizeBasicBlocks`: the basic-block optimiser, under
  `optSideB` on every run.

Every result about the scheduler or the copy propagation assumes that every array slot is a
`qsave.` slot, which the region layout gives.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgOpt

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrImage
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrMem (slotMov? cellParts?)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogStoreToLoad
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline (instrModeled bodyAllModeled)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgEmit
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgPass
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold (slotMov?_single)

variable {slotArr : String → Option (String × Nat)}

/-! ## 1. The scan at an operation with a single destination -/

/-- A modeled instruction is an operation with a single register destination. -/
theorem instrModeled_shape {i : Linstr} (h : instrModeled i = true) :
    ∃ d o ss, i.li_i = .Lopn [.reg d] o ss := by
  unfold instrModeled at h
  split at h
  · exact ⟨_, _, _, ‹_›⟩
  · cases h

/-- The value the reload scan gives the destination of a move from `s` placed at position `k`:
    the scan of `s` for a general-purpose name that is no array slot, and `s` itself
    otherwise. -/
def movScan (slotArr : String → Option (String × Nat)) (W : Lcmd) (k : Nat) (s : String) :
    Option String :=
  if (slotArr s).isNone && gpNameB s then reloadOf slotArr W k s else some s

/-- The scan behind an operation with the single destination `d`, for a name other than `d`. -/
theorem reloadOf_succ_single {W : Lcmd} {k : Nat} {j : Linstr} {d o : String}
    {ss : List LOperand} (hW : W[k]? = some j) (hj : j.li_i = .Lopn [.reg d] o ss) {x : String}
    (hx : x ≠ d) :
    reloadOf slotArr W (k + 1) x = if (slotArr d).isNone then reloadOf slotArr W k x else none := by
  cases hm : slotMov? j.li_i with
  | some p =>
    obtain ⟨d', q⟩ := p
    have hd' : d' = d := by rw [hj] at hm; exact slotMov?_single hm
    subst hd'
    rw [reloadOf_succ_some hW hm, if_neg (Ne.symm hx)]
  | none =>
    rw [reloadOf_succ_lopn hW hm hj]
    simp only [List.any_cons, List.any_nil, Bool.or_false, dstHitB]
    by_cases hs : (slotArr d).isNone = true
    · simp [hs, Ne.symm hx]
    · simp only [Bool.not_eq_true, Option.isNone_eq_false_iff] at hs
      have hn : (slotArr d).isNone = false := by simpa using hs
      simp only [hs, Bool.or_true, if_true, hn, Bool.false_eq_true, if_false]

/-- The scan behind a move `slotMov?` into `d` from `s`, for the name `d`. -/
theorem reloadOf_succ_mov {W : Lcmd} {k : Nat} {j : Linstr} {d s : String}
    (hW : W[k]? = some j) (hm : slotMov? j.li_i = some (d, s)) :
    reloadOf slotArr W (k + 1) d = movScan slotArr W k s := by
  rw [reloadOf_succ_some hW hm, if_pos rfl]; rfl

/-- The scan behind an operation with the single destination `d` that is no move `slotMov?`,
    for the name `d`. -/
theorem reloadOf_succ_noMov {W : Lcmd} {k : Nat} {j : Linstr} {d o : String}
    {ss : List LOperand} (hW : W[k]? = some j) (hj : j.li_i = .Lopn [.reg d] o ss)
    (hm : slotMov? j.li_i = none) : reloadOf slotArr W (k + 1) d = none := by
  rw [reloadOf_succ_lopn hW hm hj]
  simp [dstHitB]

/-- A move of `slotMov?` is a reload of `asReload`. -/
theorem asReload_of_slotMov {r : LinstrR} {p : String × String} (h : slotMov? r = some p) :
    asReload r = some p := by
  unfold slotMov? at h
  split at h
  · rename_i dst opn src
    split_ifs at h with h1 h2
    cases h
    have hm : isMovMnem opn = true := by
      rcases h1 with rfl | rfl
      · rfl
      · decide
    simp [asReload, hm]
  · cases h

/-- The reload of an operation with the single destination `d` reloads into `d`. -/
theorem asReload_single {d o : String} {ss : List LOperand} {d' s : String}
    (h : asReload (.Lopn [.reg d] o ss) = some (d', s)) : d' = d := by
  unfold asReload at h
  split at h
  · rename_i heq
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at heq
    obtain ⟨rfl, -, -⟩ := heq
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.symm
  · cases h

/-- The destination names of an operation with a single register destination. -/
theorem writtenNames_single (d o : String) (ss : List LOperand) :
    writtenNames (.Lopn [.reg d] o ss) = [d] := rfl

/-! ## 2. Deleting instructions inside a context -/

/-- **Deleting transparent instructions of a segment.** Let the marks `Mb` of the segment `b` of
    a body `A ++ b ++ C` in the class delete only instructions after each of which a reload scan
    resolves only if it resolves in front of the instruction. Then the body with the kept
    instructions of `b` is in the class. -/
theorem physImgB_ctx_kept_of_transparent {A C : Lcmd} {Mb : List (Linstr × Bool)}
    (h : physImgB slotArr (A ++ Mb.map Prod.fst ++ C) = true)
    (htr : ∀ p j, Mb[p]? = some (j, true) → ∀ y,
      (accArr slotArr (A ++ Mb.map Prod.fst ++ C) (A.length + p + 1) y).isSome = true →
      (accArr slotArr (A ++ Mb.map Prod.fst ++ C) (A.length + p) y).isSome = true) :
    physImgB slotArr (A ++ (Mb.filter (fun p => !p.2)).map Prod.fst ++ C) = true := by
  let M := A.map (fun i => (i, false)) ++ Mb ++ C.map (fun i => (i, false))
  have hM : M.map Prod.fst = A ++ Mb.map Prod.fst ++ C := by
    simp [M, List.map_map, Function.comp_def]
  have hK : (M.filter (fun p => !p.2)).map Prod.fst =
      A ++ (Mb.filter (fun p => !p.2)).map Prod.fst ++ C := by
    simp [M, List.filter_append, List.filter_map, Function.comp_def, List.map_map]
  rw [← hK]
  refine physImgB_kept_of_transparent (by rw [hM]; exact h) fun p j hp y hy => ?_
  rw [hM] at hy ⊢
  have hA : A.length ≤ p := by
    by_contra hlt
    push Not at hlt
    rw [show M = A.map (fun i => (i, false)) ++ (Mb ++ C.map (fun i => (i, false))) by
      simp [M], List.getElem?_append_left (by simpa using hlt)] at hp
    simp at hp
  obtain ⟨p', rfl⟩ : ∃ p', p = A.length + p' := ⟨p - A.length, by omega⟩
  have hp' : (Mb ++ C.map (fun i => (i, false)))[p']? = some (j, true) := by
    rw [show M = A.map (fun i => (i, false)) ++ (Mb ++ C.map (fun i => (i, false))) by
      simp [M], List.getElem?_append_right (by simp)] at hp
    simpa using hp
  have hlt : p' < Mb.length := by
    by_contra hge
    push Not at hge
    rw [List.getElem?_append_right hge] at hp'
    simp at hp'
  rw [List.getElem?_append_left hlt] at hp'
  exact htr p' j hp' y hy

/-! ## 3. The redundant-reload elimination `elimReloads` -/

/-- The marks of `elimAux`: each instruction with the flag that the pass deletes it. -/
def elimMarks : Held → Lcmd → List (Linstr × Bool)
  | _, [] => []
  | h, i :: is => (i, !(stepReload h i.li_i).1) :: elimMarks (stepReload h i.li_i).2 is

theorem elimMarks_fst : ∀ (h : Held) (b : Lcmd), (elimMarks h b).map Prod.fst = b
  | _, [] => rfl
  | h, i :: is => by simp [elimMarks, elimMarks_fst _ is]

theorem elimMarks_kept : ∀ (h : Held) (b : Lcmd),
    ((elimMarks h b).filter (fun p => !p.2)).map Prod.fst = elimAux h b
  | _, [] => rfl
  | h, i :: is => by
    rw [elimAux_cons]
    cases hk : (stepReload h i.li_i).1 <;>
      simp [elimMarks, hk, elimMarks_kept _ is]

/-- A reload whose source is an array slot. -/
def slotSrcReloadB (slotArr : String → Option (String × Nat)) (j : Linstr) : Bool :=
  match asReload j.li_i with
  | some (_, s) => (slotArr s).isSome
  | none => false

/-- No instruction writes an array slot after a reload from an array slot; the flag records
    whether such a reload came before. A reload from any other name may precede an array-slot
    write: the prologue of the physical ABI export saves the callee-saved registers into their
    `qsave.` slots, which are no array slots, and only then saves the argument registers that
    carry array bases into their array slots, and every move from an array slot comes after
    these saves. -/
def slotAfterSlotReloadFreeB (slotArr : String → Option (String × Nat)) : Bool → Lcmd → Bool
  | _, [] => true
  | seen, i :: is =>
      (!seen || (writtenNames i.li_i).all fun q => (slotArr q).isNone) &&
        slotAfterSlotReloadFreeB slotArr (seen || slotSrcReloadB slotArr i) is

/-- A reload into an array slot reads no array slot. -/
def saveSrcB (slotArr : String → Option (String × Nat)) (b : Lcmd) : Bool :=
  b.all fun j =>
    match asReload j.li_i with
    | some (d, s) => (slotArr d).isNone || (slotArr s).isNone
    | none => true

/-- **The side condition of `elimReloads`.** The body is modeled, no instruction writes an
    array slot after a reload from an array slot, and a reload into an array slot reads no
    array slot. -/
def elimSideB (slotArr : String → Option (String × Nat)) (b : Lcmd) : Bool :=
  bodyAllModeled b && slotAfterSlotReloadFreeB slotArr false b && saveSrcB slotArr b

theorem mem_of_lookup : ∀ (h : List (String × String)) (r k : String),
    h.lookup r = some k → (r, k) ∈ h
  | [], _, _, hl => by simp at hl
  | (a, b) :: t, r, k, hl => by
    by_cases hra : r = a
    · subst hra; simp at hl; subst hl; simp
    · have : t.lookup r = some k := by
        simpa [List.lookup, beq_eq_false_iff_ne.mpr hra] using hl
      exact List.mem_cons_of_mem _ (mem_of_lookup t r k this)

theorem lookup_unique {β : Type} : ∀ (h : List (String × β)) (r : String) (K k : β),
    (h.map Prod.fst).Nodup → (r, K) ∈ h → h.lookup r = some k → K = k
  | [], _, _, _, _, hm, _ => by simp at hm
  | (a, b) :: t, r, K, k, hn, hm, hl => by
    simp only [List.map_cons, List.nodup_cons] at hn
    by_cases hra : r = a
    · subst hra
      simp at hl
      subst hl
      rcases List.mem_cons.mp hm with he | he
      · cases he; rfl
      · exact absurd (List.mem_map.mpr ⟨_, he, rfl⟩) hn.1
    · have hl' : t.lookup r = some k := by
        simpa [List.lookup, beq_eq_false_iff_ne.mpr hra] using hl
      rcases List.mem_cons.mp hm with he | he
      · cases he; exact absurd rfl hra
      · exact lookup_unique t r K k hn.2 he hl'

theorem nodup_filter_fst {β : Type} {h : List (String × β)} (hn : (h.map Prod.fst).Nodup)
    (P : String × β → Bool) : ((h.filter P).map Prod.fst).Nodup :=
  hn.sublist ((List.filter_sublist).map _)

/-- The invariant of the forward scan of `elimReloads` at position `N` of the whole body `W`,
    after the prefix `P` of the segment: the held registers are distinct, each binding
    `R ↦ (K, m)` is recorded by a reload of `P` under the mnemonic `m`, and a binding whose
    recording move `R ← K` under `m` is a move of `slotMov?` resolves the register whenever a
    move from its source would. -/
def ElimInv (slotArr : String → Option (String × Nat)) (W P : Lcmd) (N : Nat) (h : Held) :
    Prop :=
  (h.map Prod.fst).Nodup ∧ ∀ R K m, (R, K, m) ∈ h →
    (∃ j ∈ P, asReload j.li_i = some (R, K) ∧ reloadMnem j.li_i = m) ∧
      (slotMov? (.Lopn [.reg R] m [.reg K]) = some (R, K) →
        ((movScan slotArr W N K).bind slotArr).isSome = true →
        ((reloadOf slotArr W N R).bind slotArr).isSome = true)

section ElimStep

variable {W : Lcmd} {N : Nat} {i : Linstr} {d o : String} {ss : List LOperand}

theorem reloadOf_succ_ne (hW : W[N]? = some i) (hj : i.li_i = .Lopn [.reg d] o ss)
    {x : String} (hx : x ≠ d) (hd : (slotArr d).isNone = true) :
    reloadOf slotArr W (N + 1) x = reloadOf slotArr W N x := by
  rw [reloadOf_succ_single hW hj hx, if_pos hd]

theorem movScan_succ_ne (hW : W[N]? = some i) (hj : i.li_i = .Lopn [.reg d] o ss)
    {K : String} (hK : K ≠ d) (hd : (slotArr d).isNone = true) :
    movScan slotArr W (N + 1) K = movScan slotArr W N K := by
  unfold movScan
  rw [reloadOf_succ_ne hW hj hK hd]

/-- A move from `s` behind the move `d ← s` resolves only where it resolves in front of it. -/
theorem movScan_succ_mov (hW : W[N]? = some i) (hj : i.li_i = .Lopn [.reg d] o ss)
    {s : String} (hm : slotMov? i.li_i = some (d, s))
    (h : ((movScan slotArr W (N + 1) s).bind slotArr).isSome = true) :
    ((movScan slotArr W N s).bind slotArr).isSome = true := by
  unfold movScan at h ⊢
  by_cases hc : ((slotArr s).isNone && gpNameB s) = true
  · rw [if_pos hc] at h ⊢
    by_cases hsd : s = d
    · subst hsd
      rw [reloadOf_succ_mov hW hm] at h
      unfold movScan at h
      rwa [if_pos hc] at h
    · rw [reloadOf_succ_single hW hj hsd] at h
      split_ifs at h
      · exact h
      · simp at h
  · rw [if_neg hc] at h ⊢
    exact h

/-- The source of a reload that reads no array slot is no array slot. -/
theorem elim_slotd {R K : String} {j : Linstr} (hr : asReload j.li_i = some (R, K))
    (hns : slotSrcReloadB slotArr j = false) : (slotArr K).isNone = true := by
  unfold slotSrcReloadB at hns
  rw [hr] at hns
  simpa using hns

/-- A binding whose register and source the instruction does not write keeps its implication. -/
theorem elim_imp_surv (hW : W[N]? = some i) (hj : i.li_i = .Lopn [.reg d] o ss)
    {R K : String} (hR : R ≠ d) (hK : K ≠ d)
    (hslotd : (slotArr d).isSome = true → (slotArr K).isNone = true)
    (himp : ((movScan slotArr W N K).bind slotArr).isSome = true →
      ((reloadOf slotArr W N R).bind slotArr).isSome = true)
    (hV : ((movScan slotArr W (N + 1) K).bind slotArr).isSome = true) :
    ((reloadOf slotArr W (N + 1) R).bind slotArr).isSome = true := by
  by_cases hd : (slotArr d).isNone = true
  · rw [reloadOf_succ_ne hW hj hR hd]
    rw [movScan_succ_ne hW hj hK hd] at hV
    exact himp hV
  · have hd' : (slotArr d).isSome = true :=
      Option.isSome_iff_ne_none.mpr (by simpa using hd)
    have hKn := hslotd hd'
    exfalso
    unfold movScan at hV
    split_ifs at hV with hc
    · rw [reloadOf_succ_single hW hj hK, if_neg hd] at hV
      simp at hV
    · simp only [Option.bind_some] at hV
      simp only [Option.isNone_iff_eq_none] at hKn
      rw [hKn] at hV
      simp at hV

/-- **The deleted reload is transparent.** A reload `d ← s` that, when it is a move of
    `slotMov?`, has a binding resolving `d` whenever a move from `s` would adds no resolving
    scan. -/
theorem elim_transp (hW : W[N]? = some i) (hj : i.li_i = .Lopn [.reg d] o ss)
    {s : String} (hr : asReload i.li_i = some (d, s))
    (himp : slotMov? i.li_i = some (d, s) →
      ((movScan slotArr W N s).bind slotArr).isSome = true →
      ((reloadOf slotArr W N d).bind slotArr).isSome = true) :
    ∀ y, (accArr slotArr W (N + 1) y).isSome = true →
      (accArr slotArr W N y).isSome = true := by
  intro y hy
  unfold accArr at hy ⊢
  by_cases hyd : y = d
  · subst hyd
    cases hm : slotMov? i.li_i with
    | some p =>
      have hp : p = (y, s) := by
        have := asReload_of_slotMov hm
        rw [hr] at this
        exact (Option.some.inj this).symm
      subst hp
      rw [reloadOf_succ_mov hW hm] at hy
      exact himp hm hy
    | none =>
      rw [reloadOf_succ_noMov hW hj hm] at hy
      simp at hy
  · rw [reloadOf_succ_single hW hj hyd] at hy
    split_ifs at hy
    · exact hy
    · simp at hy

/-- **One step of the scan of `elimReloads` keeps the invariant.** -/
theorem elimInv_step {P : Lcmd} {h : Held} (hW : W[N]? = some i)
    (hj : i.li_i = .Lopn [.reg d] o ss)
    (hslot : (slotArr d).isSome = true → ∀ j ∈ P, slotSrcReloadB slotArr j = false)
    (hinv : ElimInv slotArr W P N h) :
    ElimInv slotArr W (P ++ [i]) (N + 1) (stepReload h i.li_i).2 := by
  obtain ⟨hnd, hall⟩ := hinv
  have horig : ∀ R K m, (R, K, m) ∈ h →
      ∃ j ∈ P ++ [i], asReload j.li_i = some (R, K) ∧ reloadMnem j.li_i = m := by
    intro R K m hm
    obtain ⟨j, hjP, hjr⟩ := (hall R K m hm).1
    exact ⟨j, List.mem_append_left _ hjP, hjr⟩
  have hslotd : ∀ R K m, (R, K, m) ∈ h → (slotArr d).isSome = true →
      (slotArr K).isNone = true := by
    intro R K m hm hd
    obtain ⟨j, hjP, hjr, -⟩ := (hall R K m hm).1
    exact elim_slotd hjr (hslot hd j hjP)
  have surv : ∀ R K m, (R, K, m) ∈ h → R ≠ d → K ≠ d →
      (∃ j ∈ P ++ [i], asReload j.li_i = some (R, K) ∧ reloadMnem j.li_i = m) ∧
      (slotMov? (.Lopn [.reg R] m [.reg K]) = some (R, K) →
        ((movScan slotArr W (N + 1) K).bind slotArr).isSome = true →
        ((reloadOf slotArr W (N + 1) R).bind slotArr).isSome = true) := by
    intro R K m hm hR hK
    exact ⟨horig R K m hm, fun hex hV =>
      elim_imp_surv hW hj hR hK (hslotd R K m hm) ((hall R K m hm).2 hex) hV⟩
  have hnew : ∀ s, asReload i.li_i = some (d, s) →
      (∃ j ∈ P ++ [i], asReload j.li_i = some (d, s) ∧
          reloadMnem j.li_i = reloadMnem i.li_i) ∧
      (slotMov? (.Lopn [.reg d] (reloadMnem i.li_i) [.reg s]) = some (d, s) →
        ((movScan slotArr W (N + 1) s).bind slotArr).isSome = true →
        ((reloadOf slotArr W (N + 1) d).bind slotArr).isSome = true) := by
    intro s hr
    refine ⟨⟨i, by simp, hr, rfl⟩, fun hm hV => ?_⟩
    rw [← asReload_eq_reloadMnem hr] at hm
    rw [reloadOf_succ_mov hW hm]
    exact movScan_succ_mov hW hj hm hV
  have hset : ∀ s, asReload i.li_i = some (d, s) →
      ElimInv slotArr W (P ++ [i]) (N + 1)
        (((h.killReg d).killSlot d).set d (s, reloadMnem i.li_i)) := by
    intro s hr
    refine ⟨?_, fun R K m hm => ?_⟩
    · simp only [HeldOf.set, HeldOf.killReg, HeldOf.killSlot, List.map_append, List.map_cons,
        List.map_nil]
      refine List.nodup_append.mpr ⟨nodup_filter_fst (nodup_filter_fst (nodup_filter_fst hnd _)
        _) _, List.nodup_singleton _, ?_⟩
      intro a ha b' hb'
      simp only [List.mem_singleton] at hb'
      subst hb'
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      simp only [List.mem_filter, decide_eq_true_eq] at he
      exact he.2
    · rcases mem_set hm with ⟨hm1, hR⟩ | heq
      · obtain ⟨hm2, hK⟩ := mem_killSlot hm1
        obtain ⟨hm3, -⟩ := mem_killReg hm2
        exact surv R K m hm3 hR hK
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact hnew K hr
  cases har : asReload i.li_i with
  | none =>
    have hst : (stepReload h i.li_i).2 = (h.killReg d).killSlot d := by
      unfold stepReload
      rw [har]
      simp [hj, writtenNames_single]
    rw [hst]
    refine ⟨nodup_filter_fst (nodup_filter_fst hnd _) _, fun R K m hm => ?_⟩
    obtain ⟨hm1, hK⟩ := mem_killSlot hm
    obtain ⟨hm2, hR⟩ := mem_killReg hm1
    exact surv R K m hm2 hR hK
  | some p =>
    obtain ⟨d', s⟩ := p
    have hd' : d' = d := by rw [hj] at har; exact asReload_single har
    subst hd'
    by_cases hf : h.find d' = some (s, reloadMnem i.li_i)
    · have hst : (stepReload h i.li_i).2 = h := by simp [stepReload, har, hf]
      rw [hst]
      have hmem : (d', s, reloadMnem i.li_i) ∈ h := mem_of_find hf
      have hi := asReload_eq_reloadMnem har
      refine ⟨hnd, fun R K m hm => ?_⟩
      by_cases hR : R = d'
      · subst hR
        have hK : (K, m) = (s, reloadMnem i.li_i) := lookup_unique h R (K, m) _ hnd hm hf
        simp only [Prod.mk.injEq] at hK
        obtain ⟨rfl, rfl⟩ := hK
        exact hnew K har
      · by_cases hK : K = d'
        · subst hK
          refine ⟨horig R K m hm, fun hex hV => ?_⟩
          have hdn : (slotArr K).isNone = true := by
            by_cases hd : (slotArr K).isSome = true
            · exact hslotd R K m hm hd
            · simpa using hd
          rw [reloadOf_succ_ne hW hj hR hdn]
          refine (hall R K m hm).2 hex ?_
          unfold movScan at hV ⊢
          split_ifs at hV ⊢ with hc
          · cases hm' : slotMov? i.li_i with
            | some p =>
              have hp : p = (K, s) := by
                have := asReload_of_slotMov hm'
                rw [har] at this
                exact (Option.some.inj this).symm
              subst hp
              rw [reloadOf_succ_mov hW hm'] at hV
              exact (hall K s _ hmem).2 (by rw [← hi]; exact hm') hV
            | none =>
              rw [reloadOf_succ_noMov hW hj hm'] at hV
              simp at hV
          · exact hV
        · exact surv R K m hm hR hK
    · have hst : (stepReload h i.li_i).2 =
          ((h.killReg d').killSlot d').set d' (s, reloadMnem i.li_i) := by
        simp [stepReload, har, hf]
      rw [hst]; exact hset s har

end ElimStep

/-- Every instruction that the scan of `elimReloads` deletes from the rest `rest` of the segment
    `b = P ++ rest` of `A ++ b ++ C` is transparent. -/
theorem elim_marks_transp {A b C : Lcmd} :
    ∀ (rest P : Lcmd) (h : Held), b = P ++ rest → (∀ j ∈ rest, instrModeled j = true) →
      slotAfterSlotReloadFreeB slotArr (P.any (slotSrcReloadB slotArr)) rest = true →
      ElimInv slotArr (A ++ b ++ C) P (A.length + P.length) h →
      ∀ p j, (elimMarks h rest)[p]? = some (j, true) → ∀ y,
        (accArr slotArr (A ++ b ++ C) (A.length + P.length + p + 1) y).isSome = true →
        (accArr slotArr (A ++ b ++ C) (A.length + P.length + p) y).isSome = true
  | [], _, _, _, _, _, _, p, j, hp, _, _ => by simp [elimMarks] at hp
  | i :: is, P, h, hb, hmod, hside, hinv, p, j, hp, y, hy => by
    obtain ⟨d, o, ss, hj⟩ := instrModeled_shape (hmod i (by simp))
    have hW : (A ++ b ++ C)[A.length + P.length]? = some i := by
      rw [hb, List.append_assoc, List.getElem?_append_right (by omega),
        show A.length + P.length - A.length = P.length by omega, List.append_assoc,
        List.getElem?_append_right le_rfl, Nat.sub_self]
      rfl
    simp only [slotAfterSlotReloadFreeB, Bool.and_eq_true] at hside
    have hslot : (slotArr d).isSome = true → ∀ j ∈ P, slotSrcReloadB slotArr j = false := by
      intro hd
      have h1 := hside.1
      rw [hj, writtenNames_single] at h1
      have hdn : (slotArr d).isNone = false := by simpa using hd
      simp only [List.all_cons, List.all_nil, hdn, Bool.and_true, Bool.or_false,
        Bool.not_eq_true'] at h1
      exact fun j hj => by simpa using List.any_eq_false.mp h1 j hj
    cases p with
    | zero =>
      simp only [elimMarks, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq,
        Bool.not_eq_true'] at hp
      obtain ⟨hij, hk⟩ := hp
      subst hij
      obtain ⟨d', s, hr, hf⟩ := stepReload_drop_is_held_reload h i.li_i hk
      have hd' : d' = d := by rw [hj] at hr; exact asReload_single hr
      subst hd'
      exact elim_transp hW hj hr (fun hm => (hinv.2 d' s _ (mem_of_find hf)).2
        (by rw [← asReload_eq_reloadMnem hr]; exact hm)) y hy
    | succ p =>
      simp only [elimMarks, List.getElem?_cons_succ] at hp
      have hinv' := elimInv_step hW hj hslot hinv
      have ih := elim_marks_transp (A := A) (b := b) (C := C) is (P ++ [i]) _ (by simp [hb])
        (fun j hj => hmod j (by simp [hj]))
        (by rw [List.any_append]; simpa using hside.2)
        (by simpa [Nat.add_assoc] using hinv') p j hp y
      simp only [List.length_append, List.length_singleton] at ih
      rw [show A.length + P.length + (p + 1) = A.length + (P.length + 1) + p by omega]
      exact ih (by rw [show A.length + (P.length + 1) + p + 1 =
        A.length + P.length + (p + 1) + 1 by omega]; exact hy)

/-- **`elimReloads` keeps the image class inside a context.** Rewriting a segment `b` of a body
    `A ++ b ++ C` in the class by the redundant-reload elimination keeps the class, under the
    side condition `elimSideB`. -/
theorem physImgB_elimReloads_ctx {A b C : Lcmd} (h : physImgB slotArr (A ++ b ++ C) = true)
    (hside : elimSideB slotArr b = true) :
    physImgB slotArr (A ++ elimReloads b ++ C) = true := by
  simp only [elimSideB, Bool.and_eq_true] at hside
  obtain ⟨⟨hmod, hfree⟩, -⟩ := hside
  rw [elimReloads, ← elimMarks_kept [] b]
  refine physImgB_ctx_kept_of_transparent (by rw [elimMarks_fst]; exact h) ?_
  intro p j hp y hy
  rw [elimMarks_fst] at hy ⊢
  have := elim_marks_transp (A := A) (C := C) b [] [] rfl
    (fun j hj => List.all_eq_true.mp hmod j hj) (by simpa using hfree)
    ⟨List.nodup_nil, fun _ _ _ hm => by simp at hm⟩ p j hp y
  simpa using this hy

/-- **`elimReloads` keeps the image class.** -/
theorem physImgB_elimReloads {b : Lcmd} (h : physImgB slotArr b = true)
    (hside : elimSideB slotArr b = true) : physImgB slotArr (elimReloads b) = true := by
  simpa using physImgB_elimReloads_ctx (A := []) (C := []) (by simpa using h) hside

/-! ## 4. The spill-reload elimination `reloadElimBody` -/

section ReloadElim

open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim

/-- Deleting one transparent instruction inside a context keeps the class. -/
theorem physImgB_drop_one {A C : Lcmd} {j : Linstr} (h : physImgB slotArr (A ++ j :: C) = true)
    (htr : ∀ y, (accArr slotArr (A ++ j :: C) (A.length + 1) y).isSome = true →
      (accArr slotArr (A ++ j :: C) A.length y).isSome = true) :
    physImgB slotArr (A ++ C) = true := by
  have := physImgB_ctx_kept_of_transparent (A := A) (C := C) (Mb := [(j, true)])
    (by simpa using h) (fun p j' hp y hy => by
      cases p with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq, and_true] at hp
        subst hp
        simpa using htr y (by simpa using hy)
      | succ p => simp at hp)
  simpa using this

/-- **The side condition of `reloadElimBody`.** No reload that the sweep deletes, a reload
    directly after the spill of the same register into the same slot, reloads an array slot or a
    general-purpose name. -/
def reloadPairSideB (slotArr : String → Option (String × Nat)) : Lcmd → Bool
  | i :: j :: rest =>
      (!isRedundantReloadL i j ||
        (match spillLoadKey j with
          | some (slot, _, _) => (slotArr slot).isNone && !gpNameB slot
          | none => true)) && reloadPairSideB slotArr (j :: rest)
  | _ => true

theorem dropReloadsLcmd_head (j : Linstr) (t : Lcmd) :
    ∃ t', dropReloadsLcmd (j :: t) = j :: t' := by
  rw [dropReloadsLcmd_cons]
  generalize dropReloadsLcmd t = k
  cases k with
  | nil => exact ⟨[], rfl⟩
  | cons j' r =>
    simp only [consDropL]
    split_ifs
    · exact ⟨r, rfl⟩
    · exact ⟨j' :: r, rfl⟩

/-- The reload after a spill of the same register into a slot that is no array slot is
    transparent. -/
theorem reloadElim_transp {A C : Lcmd} {i j : Linstr} (hred : isRedundantReloadL i j = true)
    (hside : match spillLoadKey j with
      | some (slot, _, _) => (slotArr slot).isNone = true ∧ gpNameB slot = false
      | none => True) :
    ∀ y, (accArr slotArr (A ++ [i] ++ j :: C) ((A ++ [i]).length + 1) y).isSome = true →
      (accArr slotArr (A ++ [i] ++ j :: C) (A ++ [i]).length y).isSome = true := by
  obtain ⟨slot, r, mn, hsi, hlj⟩ := keys_of_isRedundantReloadL hred
  obtain ⟨hj, hs, -, -⟩ := spillLoadKey_eq hlj
  rw [hlj] at hside
  have hW : (A ++ [i] ++ j :: C)[(A ++ [i]).length]? = some j := by simp
  intro y hy
  unfold accArr at hy ⊢
  by_cases hyr : y = r
  · subst hyr
    cases hm : slotMov? j.li_i with
    | some p =>
      have hp : p = (y, slot) := by
        have hm' := asReload_of_slotMov hm
        rw [hj] at hm'
        simp only [asReload] at hm'
        split_ifs at hm'
        exact (Option.some.inj hm').symm
      subst hp
      rw [reloadOf_succ_mov hW hm] at hy
      unfold movScan at hy
      rw [hside.2] at hy
      simp only [Bool.and_false, Bool.false_eq_true, if_false, Option.bind_some] at hy
      have h1 := hside.1
      simp only [Option.isNone_iff_eq_none] at h1
      rw [h1] at hy
      simp at hy
    | none =>
      rw [reloadOf_succ_noMov hW hj hm] at hy
      simp at hy
  · rw [reloadOf_succ_single hW hj hyr] at hy
    split_ifs at hy
    · exact hy
    · simp at hy

/-- The sweep `dropReloadsLcmd` keeps the image class inside a context. -/
theorem physImgB_dropReloadsLcmd_ctx :
    ∀ (b A C : Lcmd), physImgB slotArr (A ++ b ++ C) = true →
      reloadPairSideB slotArr b = true → physImgB slotArr (A ++ dropReloadsLcmd b ++ C) = true
  | [], _, _, h, _ => by simpa using h
  | [i], A, C, h, _ => by simpa [dropReloadsLcmd, consDropL] using h
  | i :: j :: t, A, C, h, hside => by
    simp only [reloadPairSideB, Bool.and_eq_true] at hside
    have ih := physImgB_dropReloadsLcmd_ctx (j :: t) (A ++ [i]) C (by simpa using h) hside.2
    obtain ⟨t', ht'⟩ := dropReloadsLcmd_head j t
    rw [dropReloadsLcmd_cons, ht']
    rw [ht'] at ih
    simp only [consDropL]
    split_ifs with hred
    · have hs := hside.1
      rw [hred] at hs
      simp only [Bool.not_true, Bool.false_or] at hs
      have hs' : match spillLoadKey j with
          | some (slot, _, _) => (slotArr slot).isNone = true ∧ gpNameB slot = false
          | none => True := by
        revert hs; cases spillLoadKey j <;> simp
      have := physImgB_drop_one (A := A ++ [i]) (C := t' ++ C) (j := j) (by simpa using ih)
        (reloadElim_transp hred hs')
      simpa using this
    · simpa using ih

/-- **`reloadElimBody` keeps the image class inside a context**, when no reload it deletes
    reads an array slot (`reloadPairSideB`). -/
theorem physImgB_reloadElimBody_ctx {A b C : Lcmd} (h : physImgB slotArr (A ++ b ++ C) = true)
    (hside : reloadPairSideB slotArr b = true) :
    physImgB slotArr (A ++ reloadElimBody b ++ C) = true := by
  unfold reloadElimBody
  split
  · exact physImgB_dropReloadsLcmd_ctx b A C h hside
  · exact h

/-- **`reloadElimBody` keeps the image class.** -/
theorem physImgB_reloadElimBody {b : Lcmd} (h : physImgB slotArr b = true)
    (hside : reloadPairSideB slotArr b = true) : physImgB slotArr (reloadElimBody b) = true := by
  simpa using physImgB_reloadElimBody_ctx (A := []) (C := []) (by simpa using h) hside

end ReloadElim

/-! ## 5. The scheduler inside a context -/

section Sched

open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler (scheduleBody)
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgSched

/-- **The scheduler keeps the image class inside a context**, when every array slot is a frame
    slot `qsave.R`. -/
theorem physImgB_scheduleBody_ctx
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {A b C : Lcmd}
    (h : physImgB slotArr (A ++ b ++ C) = true) :
    physImgB slotArr (A ++ scheduleBody b ++ C) = true := by
  have hr : Relation.ReflTransGen SchedSwap (A ++ b ++ C) (A ++ scheduleBody b ++ C) :=
    (scheduleBody_schedSwap b).lift (fun x => A ++ x ++ C) fun x y hs => by
      obtain ⟨A', C', u, v, rfl, rfl, hi⟩ := hs
      exact ⟨A ++ A', C' ++ C, u, v, by simp, by simp, hi⟩
  generalize A ++ scheduleBody b ++ C = b' at hr ⊢
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact physImgB_schedSwap hq hs ih

end Sched

/-! ## 6. A rewrite at fixed positions under a dominating scan -/

section Dom

open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold (DomOn domOn_step)

/-- **The class under a rewrite at fixed positions, from the dominance of the scans.** Let `b'`
    have the length of `b`, which is in the class, and let the reload scan of `b'` dominate that
    of `b` at every position on a set `S` holding the bases of the accesses of `b'`. Let the
    instruction of `b'` at each position be that of `b`, or have no access and no array-slot
    destination; and let a move of `b` be a move into the same name in `b'`, unless an
    instruction of `b` in front of it is no move. Then `b'` is in the class.
    `PhysImgFold.physImgB_of_pointwise` is the case where the dominance follows step by step. -/
theorem physImgB_of_dom {S : String → Prop} {b b' : Lcmd}
    (h : physImgB slotArr b = true) (hlen : b'.length = b.length)
    (hdom : ∀ k, DomOn slotArr S (fun y => reloadOf slotArr b k y)
      (fun y => reloadOf slotArr b' k y))
    (hpt : ∀ (k : Nat) (i i' : Linstr), b[k]? = some i → b'[k]? = some i' →
      i' = i ∨ (isAccB i'.li_i = false ∧ DstOk slotArr i'.li_i) ∨
        ∃ ds o b0 j0 v v', i.li_i = .Lopn ds o [.arrIdx b0 j0 8, .reg v] ∧
          i'.li_i = .Lopn ds o [.arrIdx b0 j0 8, .reg v'])
    (hbase : ∀ (k : Nat) (i' : Linstr), b'[k]? = some i' →
      ∀ ds o x y ss, i'.li_i = .Lopn ds o (.arrIdx x y 8 :: ss) → S x)
    (hent : ∀ (k : Nat) (i i' : Linstr), b[k]? = some i → b'[k]? = some i' →
      (∀ d s, slotMov? i.li_i = some (d, s) → ∃ s', slotMov? i'.li_i = some (d, s')) ∨
        ∃ (p : Nat) (j : Linstr), p < k ∧ b[p]? = some j ∧ slotMov? j.li_i = none) :
    physImgB slotArr b' = true := by
  have hentry : ∀ k R, entryRegB b k R = true → entryRegB b' k R = true := by
    intro k R he
    unfold entryRegB at he ⊢
    rw [List.all_eq_true] at he ⊢
    intro j' hj'
    obtain ⟨p, hp, hpj⟩ := List.getElem_of_mem hj'
    simp only [List.length_take] at hp
    have hpk : p < k := by omega
    have hpb : p < b.length := by omega
    have hb'p : b'[p]? = some j' := by
      rw [← hpj, List.getElem_take]; exact List.getElem?_eq_getElem _
    have hbp : b[p]? = some b[p] := List.getElem?_eq_getElem hpb
    have hmv := he b[p] (List.mem_iff_getElem.mpr ⟨p, by simp; omega, by simp⟩)
    rcases hent p b[p] j' hbp hb'p with hmv' | ⟨p', j, hp', hj, hjm⟩
    · cases hm : slotMov? b[p].li_i with
      | none => rw [hm] at hmv; cases hmv
      | some ds =>
        obtain ⟨d, s⟩ := ds
        rw [hm] at hmv
        obtain ⟨s', hs'⟩ := hmv' d s hm
        rw [hs']
        exact hmv
    · have hp'b : p' < b.length := by omega
      have := he b[p'] (List.mem_iff_getElem.mpr ⟨p', by simp; omega, by simp⟩)
      rw [List.getElem?_eq_getElem hp'b, Option.some.injEq] at hj
      rw [hj, hjm] at this
      cases this
  have hacc : ∀ k x, S x → (accArr slotArr b k x).isSome = true →
      (accArr slotArr b' k x).isSome = true := by
    intro k x hx ha
    simp only [accArr, Option.isSome_bind] at ha ⊢
    cases hr : reloadOf slotArr b k x with
    | none => rw [hr] at ha; cases ha
    | some q =>
      rw [hr] at ha
      have ha' : (slotArr q).isSome = true := by simpa using ha
      have := hdom k x hx q hr ha'
      simp only at this
      rw [this]
      exact ha
  unfold physImgB
  rw [List.all_eq_true]
  intro k hkr
  have hkb' : k < b'.length := List.mem_range.mp hkr
  have hk' : b'[k]? = some b'[k] := List.getElem?_eq_getElem hkb'
  have hk : b[k]? = some b[k] := List.getElem?_eq_getElem (by omega)
  rw [hk', Bool.and_eq_true]
  obtain ⟨h1, h2⟩ := PhysImgFold.physImgB_getElem h hk
  rcases hpt k b[k] b'[k] hk hk' with heq | ⟨hna, hdst⟩ | ⟨ds, o, b0, j0, v, v', hi, hi'⟩
  · rw [heq]
    refine ⟨accOkB_of_base (fun x hx ha => hacc k x ?_ ha) h1,
      slotWriteB_mono (hentry k) _ h2⟩
    obtain ⟨ds, o, y, ss, hx'⟩ := hx
    exact hbase k b'[k] hk' ds o x y ss (by rw [heq]; exact hx')
  · exact ⟨accOkB_of_not_acc _ _ _ hna, slotWriteB_of_dstOk hdst _ _⟩
  · rw [hi] at h1 h2
    rw [hi']
    have e1 : accOkB slotArr b' k (.Lopn ds o [.arrIdx b0 j0 8, .reg v']) =
        accOkB slotArr b' k (.Lopn ds o [.arrIdx b0 j0 8, .reg v]) := by
      simp only [accOkB]
      rcases ds with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> (try cases x) <;> rfl
    have e2 : slotWriteB slotArr b' k (.Lopn ds o [.arrIdx b0 j0 8, .reg v']) =
        slotWriteB slotArr b' k (.Lopn ds o [.arrIdx b0 j0 8, .reg v]) := by
      simp [slotWriteB, slotMov?]
    rw [e1, e2]
    refine ⟨accOkB_of_base (fun x hx ha => hacc k x ?_ ha) h1,
      slotWriteB_mono (hentry k) _ h2⟩
    obtain ⟨ds', o', y, ss, hx'⟩ := hx
    simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.arrIdx.injEq] at hx'
    obtain ⟨-, -, ⟨rfl, -, -⟩, -⟩ := hx'
    exact hbase k b'[k] hk' ds o b0 j0 [.reg v'] hi'

/-- The dominance of the scans is kept along a common suffix of instructions. -/
theorem domOn_reloadOf_common {S : String → Prop} (hS : ∀ q, gpNameB q = true → S q)
    {b b' : Lcmd} {m : Nat}
    (hm : DomOn slotArr S (fun y => reloadOf slotArr b m y) (fun y => reloadOf slotArr b' m y))
    (hcom : ∀ k, m ≤ k → b[k]? = b'[k]?) :
    ∀ n, DomOn slotArr S (fun y => reloadOf slotArr b (m + n) y)
      (fun y => reloadOf slotArr b' (m + n) y)
  | 0 => hm
  | n + 1 => by
    have ih := domOn_reloadOf_common hS hm hcom n
    rw [show m + (n + 1) = (m + n) + 1 by omega]
    cases hb : b[m + n]? with
    | none =>
      intro x _ q hf
      simp only at hf
      rw [PhysImgFold.reloadOf_succ_none slotArr hb] at hf
      cases hf
    | some i =>
      have hb' : b'[m + n]? = some i := by rw [← hcom _ (by omega)]; exact hb
      intro x hx q hf hq
      simp only at hf ⊢
      rw [PhysImgFold.reloadOf_succ_eq slotArr hb] at hf
      rw [PhysImgFold.reloadOf_succ_eq slotArr hb']
      exact domOn_step hS ih i x hx q hf hq

end Dom

/-! ## 7. The cross-register load CSE `loadCSE` -/

section LoadCSE

open CatCrypt.Crypto.Optimizer.LoadCSE
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold (DomOn domOn_step dstOk_single)

/-- A redirect of a move from `s` onto a holder `r` keeps the reload scan: `r` is a
    general-purpose name that is no array slot, or an array slot, or a move from `s` resolves
    to no array slot. -/
def goodHoldB (slotArr : String → Option (String × Nat)) (s r : String) : Bool :=
  (gpNameB r && (slotArr r).isNone) || (slotArr r).isSome || (!gpNameB s && (slotArr s).isNone)

/-- The rewrite of `i` into `i'` by `loadCSE` is a redirect `d ← s` to `d ← r` that keeps the
    reload scan (`goodHoldB`), into a destination that is no array slot, of a 64-bit move that
    is no move `slotMov?`, or of a move `slotMov?` into a move `slotMov?`. -/
def loadRewriteOkB (slotArr : String → Option (String × Nat)) (i i' : Linstr) : Bool :=
  match asWideReload i.li_i, i'.li_i with
  | some (d, s, _), .Lopn [.reg _] _ [.reg r] =>
      r == s || ((slotArr d).isNone && goodHoldB slotArr s r &&
        ((slotMov? i.li_i).isNone || slotMov? i'.li_i == some (d, r)))
  | _, _ => true

/-- `loadRewriteOkB` at every position of the forward scan of `loadCSE`. -/
def loadChkB (slotArr : String → Option (String × Nat)) : LoadEnv → Lcmd → Bool
  | _, [] => true
  | h, i :: is => loadRewriteOkB slotArr i (stepLoad h i).1 && loadChkB slotArr (stepLoad h i).2 is

/-- A 64-bit move from an array slot. -/
def slotLoadB (slotArr : String → Option (String × Nat)) (j : Linstr) : Bool :=
  match asWideReload j.li_i with
  | some (_, s, _) => (slotArr s).isSome
  | none => false

/-- No instruction writes an array slot after a 64-bit move from an array slot; the flag records
    whether such a move came before. -/
def slotAfterSlotLoadFreeB (slotArr : String → Option (String × Nat)) : Bool → Lcmd → Bool
  | _, [] => true
  | seen, i :: is =>
      (!seen || (writtenNames i.li_i).all fun q => (slotArr q).isNone) &&
        slotAfterSlotLoadFreeB slotArr (seen || slotLoadB slotArr i) is

/-- Every 64-bit move into a general-purpose name is a move of `slotMov?`: no 64-bit move into
    a general-purpose name reads a cell. -/
def wideMovB (b : Lcmd) : Bool :=
  b.all fun j =>
    match asWideReload j.li_i with
    | some (d, _, _) => !gpNameB d || (slotMov? j.li_i).isSome
    | none => true

/-- **The side condition of `loadCSE`.** The body is modeled, its 64-bit moves into
    general-purpose names read no cell,
    every redirect keeps the reload scan (`loadChkB`), a move into an array slot reads no array
    slot, and no instruction writes an array slot after a 64-bit move from an array slot. -/
def loadSideB (slotArr : String → Option (String × Nat)) (b : Lcmd) : Bool :=
  bodyAllModeled b && wideMovB b && loadChkB slotArr [] b && saveSrcB slotArr b &&
    slotAfterSlotLoadFreeB slotArr false b

/-- The scan `g` resolves the destination of a move from `r` to every array slot to which the
    scan `f` resolves the destination of a move from `s`. -/
def MovDom (slotArr : String → Option (String × Nat)) (W W' : Lcmd) (k : Nat) (s r : String) :
    Prop :=
  ∀ q, movScan slotArr W k s = some q → (slotArr q).isSome = true →
    movScan slotArr W' k r = some q

theorem movDom_of_dom {W W' : Lcmd} {k : Nat}
    (h : DomOn slotArr (fun _ => True) (fun y => reloadOf slotArr W k y)
      (fun y => reloadOf slotArr W' k y)) (s : String) : MovDom slotArr W W' k s s := by
  intro q hq hs
  unfold movScan at hq ⊢
  split_ifs at hq ⊢
  · exact h s trivial q hq hs
  · exact hq

theorem asReload_of_asWideReload {r : LinstrR} {d s mn : String}
    (h : asWideReload r = some (d, s, mn)) : asReload r = some (d, s) := by
  obtain ⟨rfl, hm⟩ := asWideReload_eq h
  have : isMovMnem mn = true := by
    simp only [isMov64Mnem, Bool.or_eq_true, beq_iff_eq] at hm
    rcases hm with rfl | rfl
    · decide
    · rfl
  simp [asReload, this]

/-- The invariant of the forward scan of `loadCSE` at position `N`, after the prefix `P` of the
    segment: the scan of the output dominates that of the input, every binding `s ↦ r` is
    recorded by a 64-bit move of `P` from `s` into `r`, and a binding that keeps the scan
    (`goodHoldB`) carries the scan of `s` to `r`. -/
def LoadInv (slotArr : String → Option (String × Nat)) (W W' P : Lcmd) (N : Nat)
    (env : LoadEnv) : Prop :=
  DomOn slotArr (fun _ => True) (fun y => reloadOf slotArr W N y)
      (fun y => reloadOf slotArr W' N y) ∧
    ∀ s r, (s, r) ∈ env → (∃ j ∈ P, ∃ mn, asWideReload j.li_i = some (r, s, mn)) ∧
      (goodHoldB slotArr s r = true → MovDom slotArr W W' N s r)

section LoadStep

variable {W W' : Lcmd} {N : Nat} {i i' : Linstr} {d o o' : String} {ss ss' : List LOperand}

/-- The dominance behind two operations with the same single destination, for the other
    names. -/
theorem dom_succ_ne (hW : W[N]? = some i) (hW' : W'[N]? = some i')
    (hj : i.li_i = .Lopn [.reg d] o ss) (hj' : i'.li_i = .Lopn [.reg d] o' ss')
    (hdom : DomOn slotArr (fun _ => True) (fun y => reloadOf slotArr W N y)
      (fun y => reloadOf slotArr W' N y)) {x : String} (hx : x ≠ d) {q : String}
    (hf : reloadOf slotArr W (N + 1) x = some q) (hq : (slotArr q).isSome = true) :
    reloadOf slotArr W' (N + 1) x = some q := by
  rw [reloadOf_succ_single hW hj hx] at hf
  rw [reloadOf_succ_single hW' hj' hx]
  split_ifs at hf ⊢
  exact hdom x trivial q hf hq

/-- A binding whose names the instruction does not write keeps carrying the scan. -/
theorem movDom_surv (hW : W[N]? = some i) (hW' : W'[N]? = some i')
    (hj : i.li_i = .Lopn [.reg d] o ss) (hj' : i'.li_i = .Lopn [.reg d] o' ss')
    {s r : String} (hs : s ≠ d) (hr : r ≠ d)
    (hslotd : (slotArr d).isSome = true → (slotArr s).isNone = true)
    (h : MovDom slotArr W W' N s r) : MovDom slotArr W W' (N + 1) s r := by
  intro q hq hqs
  by_cases hd : (slotArr d).isNone = true
  · rw [movScan_succ_ne hW hj hs hd] at hq
    rw [movScan_succ_ne hW' hj' hr hd]
    exact h q hq hqs
  · have hsn := hslotd (Option.isSome_iff_ne_none.mpr (by simpa using hd))
    exfalso
    unfold movScan at hq
    split_ifs at hq with hc
    · rw [reloadOf_succ_single hW hj hs, if_neg hd] at hq
      cases hq
    · cases hq
      simp only [Option.isNone_iff_eq_none] at hsn
      rw [hsn] at hqs
      cases hqs

/-- Behind an operation into `d`, a move from `s` resolves to no array slot when `s ↦ d` keeps
    the reload scan (`goodHoldB`), `d` is no general-purpose name that is no array slot, and
    one of `d` and `s` is no array slot. -/
theorem movScan_succ_noSlot (hW : W[N]? = some i) (hj : i.li_i = .Lopn [.reg d] o ss)
    {s : String} (hsv : ((slotArr d).isNone || (slotArr s).isNone) = true)
    (hg : goodHoldB slotArr s d = true) (hcd : ¬ ((slotArr d).isNone && gpNameB d) = true)
    {q : String} (hq : movScan slotArr W (N + 1) s = some q)
    (hqs : (slotArr q).isSome = true) : False := by
  unfold movScan at hq
  simp only [goodHoldB, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hg
  rcases hg with ⟨⟨hgp, hgn⟩ | hds⟩ | ⟨hgs, hsn⟩
  · exact hcd (by simp [hgp, hgn])
  · have hdn' : ¬ (slotArr d).isNone = true := by
      rw [Option.isNone_iff_eq_none]; exact Option.isSome_iff_ne_none.mp hds
    have hsn : (slotArr s).isNone = true := by
      simp only [Bool.or_eq_true] at hsv
      exact hsv.resolve_left hdn'
    have hne : s ≠ d := by
      rintro rfl
      rw [Option.isNone_iff_eq_none] at hsn
      rw [hsn] at hds
      cases hds
    split_ifs at hq with hc
    · rw [reloadOf_succ_single hW hj hne, if_neg hdn'] at hq
      cases hq
    · cases hq
      simp only [Option.isNone_iff_eq_none] at hsn
      rw [hsn] at hqs; cases hqs
  · rw [if_neg (by simp [hgs])] at hq
    cases hq
    simp only [Option.isNone_iff_eq_none] at hsn
    rw [hsn] at hqs; cases hqs

/-- The output instruction of one step of `loadCSE`: the input, or the redirect of a 64-bit
    move onto the holder of its source. -/
theorem stepLoad_out (env : LoadEnv) {s mn : String} (har : asWideReload i.li_i = some (d, s, mn)) :
    ((stepLoad env i).1 = i ∨ ∃ r, env.find s = some r ∧
        (stepLoad env i).1 = { i with li_i := .Lopn [.reg d] mn [.reg r] }) ∧
      (stepLoad env i).2 = ((env.killReg d).killSlot d).set s d := by
  unfold stepLoad
  rw [har]
  cases hf : env.find s with
  | none => simp [hf]
  | some r =>
    simp only [hf]
    split_ifs <;> simp

/-- **One step of the scan of `loadCSE` keeps the invariant**, and the output instruction is the
    input or a move with no access and no array-slot destination into the same name. -/
theorem loadInv_step {b P : Lcmd} {env : LoadEnv} (hW : W[N]? = some i)
    (hW' : W'[N]? = some (stepLoad env i).1) (hj : i.li_i = .Lopn [.reg d] o ss)
    (hib : i ∈ b) (hwide : wideMovB b = true)
    (hchk : loadRewriteOkB slotArr i (stepLoad env i).1 = true)
    (hsave : saveSrcB slotArr b = true)
    (hslot : (slotArr d).isSome = true → ∀ j ∈ P, slotLoadB slotArr j = false)
    (hinv : LoadInv slotArr W W' P N env) :
    LoadInv slotArr W W' (P ++ [i]) (N + 1) (stepLoad env i).2 ∧
      ((stepLoad env i).1 = i ∨ (isAccB (stepLoad env i).1.li_i = false ∧
        DstOk slotArr (stepLoad env i).1.li_i ∧ ∀ d' s', slotMov? i.li_i = some (d', s') →
          ∃ s'', slotMov? (stepLoad env i).1.li_i = some (d', s''))) := by
  obtain ⟨hdom, hall⟩ := hinv
  have hslotd : ∀ s r, (s, r) ∈ env → (slotArr d).isSome = true → (slotArr s).isNone = true := by
    intro s r hm hd
    obtain ⟨j, hjP, mn, hjr⟩ := (hall s r hm).1
    have := hslot hd j hjP
    simp only [slotLoadB, hjr] at this
    simpa using this
  have horig : ∀ s r, (s, r) ∈ env → ∃ j ∈ P ++ [i], ∃ mn, asWideReload j.li_i = some (r, s, mn) := by
    intro s r hm
    obtain ⟨j, hjP, mn, hjr⟩ := (hall s r hm).1
    exact ⟨j, List.mem_append_left _ hjP, mn, hjr⟩
  cases har : asWideReload i.li_i with
  | none =>
    have hst : stepLoad env i = (i, (env.killReg d).killSlot d) := by
      unfold stepLoad
      rw [har]
      simp [hj, writtenNames_single]
    rw [hst] at hW' ⊢
    refine ⟨⟨fun x _ q hf hq => ?_, fun s r hm => ?_⟩, Or.inl rfl⟩
    · simp only at hf ⊢
      rw [PhysImgFold.reloadOf_succ_eq slotArr hW] at hf
      rw [PhysImgFold.reloadOf_succ_eq slotArr hW']
      exact domOn_step (fun _ _ => trivial) hdom i x trivial q hf hq
    · simp only [LoadEnv.killReg, LoadEnv.killSlot, List.mem_filter, decide_eq_true_eq] at hm
      exact ⟨horig s r hm.1.1, fun hg =>
        movDom_surv hW hW' hj hj hm.2 hm.1.2 (hslotd s r hm.1.1) ((hall s r hm.1.1).2 hg)⟩
  | some p =>
    obtain ⟨d', s, mn⟩ := p
    obtain ⟨hi, hmn⟩ := asWideReload_eq har
    have hd' : d' = d := by rw [hj] at hi; cases hi; rfl
    subst hd'
    have hsv : ((slotArr d').isNone || (slotArr s).isNone) = true := by
      have := List.all_eq_true.mp hsave i hib
      rw [asReload_of_asWideReload har] at this
      exact this
    obtain ⟨hout, henv⟩ := stepLoad_out (d := d') env har
    cases hsm0 : slotMov? i.li_i
    case none =>
      have hgd : gpNameB d' = false := by
        have := List.all_eq_true.mp hwide i hib
        simpa [har, hsm0] using this
      have hT : ∃ o' ss', (stepLoad env i).1.li_i = .Lopn [.reg d'] o' ss' ∧
          ((stepLoad env i).1 = i ∨ (isAccB (stepLoad env i).1.li_i = false ∧
            DstOk slotArr (stepLoad env i).1.li_i)) := by
        rcases hout with heq | ⟨r, hf, heq⟩
        · rw [heq]; exact ⟨o, ss, hj, Or.inl rfl⟩
        · rw [heq] at hchk ⊢
          simp only [loadRewriteOkB, har] at hchk
          by_cases hrs : r = s
          · subst hrs
            have hii : ({ i with li_i := .Lopn [.reg d'] mn [.reg r] } : Linstr) = i := by
              cases i; simp only at hi ⊢; rw [hi]
            rw [hii]
            exact ⟨o, ss, hj, Or.inl rfl⟩
          · have hrs' : (r == s) = false := beq_eq_false_iff_ne.mpr hrs
            simp only [hrs', Bool.false_or, Bool.and_eq_true] at hchk
            obtain ⟨⟨hdn, -⟩, -⟩ := hchk
            refine ⟨mn, [.reg r], rfl, Or.inr ⟨?_, dstOk_single (by simpa using hdn)⟩⟩
            simp only [isAccB, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
            simp only [isMov64Mnem, Bool.or_eq_true, beq_iff_eq] at hmn
            rcases hmn with rfl | rfl <;> exact ⟨by decide, by decide⟩
      obtain ⟨o', ss', hj', hpt⟩ := hT
      rw [henv]
      refine ⟨⟨fun x _ q hf hq => ?_, fun s' r' hm => ?_⟩, ?_⟩
      · simp only at hf ⊢
        by_cases hx : x = d'
        · subst hx
          rw [reloadOf_succ_noMov hW hj hsm0] at hf
          cases hf
        · exact dom_succ_ne hW hW' hj hj' hdom hx hf hq
      · simp only [LoadEnv.set, LoadEnv.killReg, LoadEnv.killSlot, List.mem_append,
          List.mem_filter, List.mem_singleton, Prod.mk.injEq, decide_eq_true_eq] at hm
        rcases hm with ⟨⟨⟨hm, hr⟩, hs⟩, -⟩ | ⟨rfl, rfl⟩
        · exact ⟨horig s' r' hm, fun hg =>
            movDom_surv hW hW' hj hj' hs hr (hslotd s' r' hm) ((hall s' r' hm).2 hg)⟩
        · exact ⟨⟨i, by simp, mn, har⟩, fun hg q hq hqs =>
            (movScan_succ_noSlot hW hj hsv hg (by simp [hgd]) hq hqs).elim⟩
      · rcases hpt with h1 | ⟨h1, h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, h2, fun d'' s'' h => by cases h⟩
    have hsm : slotMov? i.li_i = some (d', s) := by
      have := asReload_of_slotMov hsm0
      rw [asReload_of_asWideReload har] at this
      rw [hsm0, Option.some.inj this]
    -- the output's move and the binding it reads
    have hT : ∃ t, slotMov? (stepLoad env i).1.li_i = some (d', t) ∧
        (stepLoad env i).1.li_i = .Lopn [.reg d'] mn [.reg t] ∧
        MovDom slotArr W W' N s t ∧
        ((stepLoad env i).1 = i ∨ (isAccB (stepLoad env i).1.li_i = false ∧
          DstOk slotArr (stepLoad env i).1.li_i)) := by
      rcases hout with heq | ⟨r, hf, heq⟩
      · rw [heq]; exact ⟨s, hsm, hi, movDom_of_dom hdom s, Or.inl rfl⟩
      · rw [heq] at hchk ⊢
        simp only [loadRewriteOkB, har] at hchk
        by_cases hrs : r = s
        · subst hrs
          have hii : ({ i with li_i := .Lopn [.reg d'] mn [.reg r] } : Linstr) = i := by
            cases i; simp only at hi ⊢; rw [hi]
          rw [hii]
          exact ⟨r, hsm, hi, movDom_of_dom hdom r, Or.inl rfl⟩
        · have hrs' : (r == s) = false := beq_eq_false_iff_ne.mpr hrs
          simp only [hrs', hsm, Option.isNone_some, Bool.false_or, Bool.and_eq_true,
            beq_iff_eq] at hchk
          obtain ⟨⟨hdn, hg⟩, hm'⟩ := hchk
          refine ⟨r, by simpa using hm', rfl, (hall s r (mem_of_lookup env s r hf)).2 hg,
            Or.inr ⟨?_, ?_⟩⟩
          · simp only [isAccB, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
            simp only [isMov64Mnem, Bool.or_eq_true, beq_iff_eq] at hmn
            rcases hmn with rfl | rfl <;> exact ⟨by decide, by decide⟩
          · exact dstOk_single (by simpa using hdn)
    obtain ⟨t, hmt, hj', hMt, hpt⟩ := hT
    rw [henv]
    refine ⟨⟨fun x _ q hf hq => ?_, fun s' r' hm => ?_⟩, ?_⟩
    · simp only at hf ⊢
      by_cases hx : x = d'
      · subst hx
        rw [reloadOf_succ_mov hW hsm] at hf
        rw [reloadOf_succ_mov hW' hmt]
        exact hMt q hf hq
      · exact dom_succ_ne hW hW' hj hj' hdom hx hf hq
    · simp only [LoadEnv.set, LoadEnv.killReg, LoadEnv.killSlot, List.mem_append,
        List.mem_filter, List.mem_singleton, Prod.mk.injEq, decide_eq_true_eq] at hm
      rcases hm with ⟨⟨⟨hm, hr⟩, hs⟩, -⟩ | ⟨rfl, rfl⟩
      · exact ⟨horig s' r' hm, fun hg =>
          movDom_surv hW hW' hj hj' hs hr (hslotd s' r' hm) ((hall s' r' hm).2 hg)⟩
      · refine ⟨⟨i, by simp, mn, har⟩, fun hg q hq hqs => ?_⟩
        by_cases hcd : ((slotArr r').isNone && gpNameB r') = true
        · -- the destination is a general-purpose name: the output scan reads the moved source
          unfold movScan at hq
          have hrn : (slotArr r').isNone = true := by
            simp only [Bool.and_eq_true] at hcd; exact hcd.1
          unfold movScan
          rw [if_pos hcd, reloadOf_succ_mov hW' hmt]
          refine hMt q ?_ hqs
          by_cases hsd : s' = r'
          · subst hsd
            rw [if_pos hcd, reloadOf_succ_mov hW hsm] at hq
            exact hq
          · unfold movScan
            split_ifs at hq ⊢ with hc
            · rwa [reloadOf_succ_ne hW hj hsd hrn] at hq
            · exact hq
        · exact (movScan_succ_noSlot hW hj hsv hg hcd hq hqs).elim
    · rcases hpt with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2, fun d'' s'' h => by
          rw [← hsm0, hsm] at h
          cases h
          exact ⟨t, hmt⟩⟩

end LoadStep

/-- The positions of the forward scan of `loadCSE` over the rest `rest` of the segment
    `b = P ++ rest` of `A ++ b ++ C`: the scan of the output dominates that of the input, and
    each output instruction is the input one or a move with no access and no array-slot
    destination into the same name. -/
theorem load_main {A b C : Lcmd} (hwide : wideMovB b = true) (hsave : saveSrcB slotArr b = true) :
    ∀ (rest P Q : Lcmd) (env : LoadEnv), b = P ++ rest → Q.length = P.length →
      loadCSE b = Q ++ loadCSEAux env rest → (∀ j ∈ rest, instrModeled j = true) →
      loadChkB slotArr env rest = true →
      slotAfterSlotLoadFreeB slotArr (P.any (slotLoadB slotArr)) rest = true →
      LoadInv slotArr (A ++ b ++ C) (A ++ loadCSE b ++ C) P (A.length + P.length) env →
      (∀ p, p ≤ rest.length → DomOn slotArr (fun _ => True)
        (fun y => reloadOf slotArr (A ++ b ++ C) (A.length + P.length + p) y)
        (fun y => reloadOf slotArr (A ++ loadCSE b ++ C) (A.length + P.length + p) y)) ∧
      (∀ (p : Nat) (i i' : Linstr), rest[p]? = some i → (loadCSEAux env rest)[p]? = some i' →
        i' = i ∨ (isAccB i'.li_i = false ∧ DstOk slotArr i'.li_i ∧
          ∀ d s, slotMov? i.li_i = some (d, s) → ∃ s', slotMov? i'.li_i = some (d, s')))
  | [], _, _, _, _, _, _, _, _, _, hinv => by
    refine ⟨fun p hp => ?_, fun p _ _ hp => by simp at hp⟩
    simp only [List.length_nil, Nat.le_zero] at hp
    subst hp
    exact hinv.1
  | i :: is, P, Q, env, hb, hQ, hout, hmod, hchk, hside, hinv => by
    obtain ⟨d, o, ss, hj⟩ := instrModeled_shape (hmod i (by simp))
    have hW : (A ++ b ++ C)[A.length + P.length]? = some i := by
      rw [hb, List.append_assoc, List.getElem?_append_right (by omega),
        show A.length + P.length - A.length = P.length by omega, List.append_assoc,
        List.getElem?_append_right le_rfl, Nat.sub_self]
      rfl
    have hW' : (A ++ loadCSE b ++ C)[A.length + P.length]? = some (stepLoad env i).1 := by
      rw [hout, loadCSEAux_cons, List.append_assoc, List.getElem?_append_right (by omega),
        show A.length + P.length - A.length = P.length by omega, List.append_assoc,
        List.getElem?_append_right (by omega), ← hQ, Nat.sub_self]
      rfl
    have hib : i ∈ b := by rw [hb]; simp
    simp only [loadChkB, Bool.and_eq_true] at hchk
    simp only [slotAfterSlotLoadFreeB, Bool.and_eq_true] at hside
    have hslot : (slotArr d).isSome = true → ∀ j ∈ P, slotLoadB slotArr j = false := by
      intro hd
      have h1 := hside.1
      rw [hj, writtenNames_single] at h1
      have hdn : (slotArr d).isNone = false := by simpa using hd
      simp only [List.all_cons, List.all_nil, hdn, Bool.and_true, Bool.or_false,
        Bool.not_eq_true'] at h1
      exact fun j hj => by simpa using List.any_eq_false.mp h1 j hj
    obtain ⟨hinv', hpt⟩ := loadInv_step (b := b) hW hW' hj hib hwide hchk.1 hsave hslot hinv
    have ih := load_main (A := A) (C := C) hwide hsave is (P ++ [i]) (Q ++ [(stepLoad env i).1])
      (stepLoad env i).2 (by simp [hb]) (by simp [hQ]) (by rw [hout, loadCSEAux_cons]; simp)
      (fun j hj => hmod j (by simp [hj])) hchk.2 (by rw [List.any_append]; simpa using hside.2)
      (by simpa [Nat.add_assoc] using hinv')
    refine ⟨fun p hp => ?_, fun p j j' hp hp' => ?_⟩
    · cases p with
      | zero => simpa using hinv.1
      | succ p =>
        have := ih.1 p (by simp at hp; omega)
        simp only [List.length_append, List.length_singleton] at this
        rwa [show A.length + P.length + (p + 1) = A.length + (P.length + 1) + p by omega]
    · cases p with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, loadCSEAux_cons] at hp hp'
        subst hp hp'
        exact hpt
      | succ p =>
        simp only [List.getElem?_cons_succ, loadCSEAux_cons] at hp hp'
        exact ih.2 p j j' hp hp'

/-- **`loadCSE` keeps the image class inside a context**, under the side condition
    `loadSideB`. -/
theorem physImgB_loadCSE_ctx {A b C : Lcmd} (h : physImgB slotArr (A ++ b ++ C) = true)
    (hside : loadSideB slotArr b = true) :
    physImgB slotArr (A ++ loadCSE b ++ C) = true := by
  simp only [loadSideB, Bool.and_eq_true] at hside
  obtain ⟨⟨⟨⟨hmod, hwide⟩, hchk⟩, hsave⟩, hfree⟩ := hside
  have hm := load_main (A := A) (C := C) hwide hsave b [] [] [] rfl rfl
    (by rw [loadCSE_eq]; rfl) (fun j hj => List.all_eq_true.mp hmod j hj) hchk
    (by simpa using hfree)
    ⟨fun x _ q hf _ => by
      simp only [List.length_nil, Nat.add_zero] at hf ⊢
      rw [List.append_assoc, reloadOf_append_left _ _ _ _ _ le_rfl] at hf
      rw [List.append_assoc, reloadOf_append_left _ _ _ _ _ le_rfl]
      exact hf, fun _ _ hm => by simp at hm⟩
  have hlen : (loadCSE b).length = b.length := loadCSE_length b
  have hpos : ∀ (k : Nat) (i i' : Linstr), (A ++ b ++ C)[k]? = some i →
      (A ++ loadCSE b ++ C)[k]? = some i' →
      i' = i ∨ (isAccB i'.li_i = false ∧ DstOk slotArr i'.li_i ∧
        ∀ d s, slotMov? i.li_i = some (d, s) → ∃ s', slotMov? i'.li_i = some (d, s')) := by
    intro k i i' hk hk'
    rcases Nat.lt_or_ge k A.length with hA | hA
    · rw [List.append_assoc, List.getElem?_append_left hA] at hk hk'
      rw [hk] at hk'; cases hk'; exact Or.inl rfl
    obtain ⟨p, rfl⟩ : ∃ p, k = A.length + p := ⟨k - A.length, by omega⟩
    rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      at hk hk'
    rcases Nat.lt_or_ge p b.length with hb | hb
    · rw [List.getElem?_append_left hb] at hk
      rw [List.getElem?_append_left (by omega), loadCSE_eq] at hk'
      exact (hm.2 p i i' (by simpa using hk) hk')
    · rw [List.getElem?_append_right hb] at hk
      rw [List.getElem?_append_right (by omega), hlen] at hk'
      rw [hk] at hk'; cases hk'; exact Or.inl rfl
  refine physImgB_of_dom (S := fun _ => True) h (by simp [hlen]) (fun k => ?_)
    (fun k i i' hk hk' => (hpos k i i' hk hk').imp id fun h => Or.inl ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ => trivial)
    (fun k i i' hk hk' => Or.inl fun d s hs => by
      rcases hpos k i i' hk hk' with rfl | ⟨-, -, h3⟩
      · exact ⟨s, hs⟩
      · exact h3 d s hs)
  rcases Nat.lt_or_ge k (A.length + b.length) with hk | hk
  · rcases Nat.lt_or_ge k A.length with hA | hA
    · intro x _ q hf _
      simp only at hf ⊢
      rw [List.append_assoc, reloadOf_append_left _ _ _ _ _ hA.le] at hf
      rw [List.append_assoc, reloadOf_append_left _ _ _ _ _ hA.le]
      exact hf
    · have := hm.1 (k - A.length) (by simp; omega)
      simpa [show A.length + (k - A.length) = k by omega] using this
  · have h0 := hm.1 b.length (by simp)
    simp only [List.length_nil, Nat.add_zero] at h0
    have := domOn_reloadOf_common (fun _ _ => trivial) h0 (fun k hk' => by
      rw [List.append_assoc, List.append_assoc, List.getElem?_append_right (by omega),
        List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
        List.getElem?_append_right (by omega), hlen]) (k - (A.length + b.length))
    simpa [show A.length + b.length + (k - (A.length + b.length)) = k by omega] using this

/-- **`loadCSE` keeps the image class.** -/
theorem physImgB_loadCSE {b : Lcmd} (h : physImgB slotArr b = true)
    (hside : loadSideB slotArr b = true) : physImgB slotArr (loadCSE b) = true := by
  simpa using physImgB_loadCSE_ctx (A := []) (C := []) (by simpa using h) hside

end LoadCSE

/-! ## 8. Deleting instructions that the scans pass -/

/-- The reload scan for `y` passes the instruction `j`, carrying `y` or ending, and finds no
    result inside it. -/
def PassThru (slotArr : String → Option (String × Nat)) (j : Linstr) (y : String) : Prop :=
  (scanExit slotArr [j] 1 y = some y ∨ scanExit slotArr [j] 1 y = none) ∧
    reloadOf slotArr [j] 1 y = none

/-- The array scans of the kept instructions of a marked body, when the scan of the input
    passes every deleted instruction. `PhysImgPass.accArr_kept_of_passed` is the case of
    deleted instructions that are no moves into the carried name. -/
theorem accArr_kept_of_passThru : ∀ (M : List (Linstr × Bool)) (x : String),
    (∀ p j, M[p]? = some (j, true) → ∀ y,
      scanExit slotArr ((M.map Prod.fst).drop (p + 1)) (M.length - (p + 1)) x = some y →
      PassThru slotArr j y) →
    (accArr slotArr (M.map Prod.fst) M.length x).isSome = true →
    (accArr slotArr ((M.filter (fun p => !p.2)).map Prod.fst)
      ((M.filter (fun p => !p.2)).map Prod.fst).length x).isSome = true := by
  intro M
  induction M using List.reverseRecOn with
  | nil => intro x _ h; simp [accArr, reloadOf] at h
  | append_singleton M e ih =>
    intro x hps h
    obtain ⟨j, b⟩ := e
    have hl1 : (M.map Prod.fst).length = M.length := List.length_map _
    have hsrc : (M ++ [(j, b)]).map Prod.fst = M.map Prod.fst ++ [j] := by simp
    have tr : ∀ y', scanExit slotArr [j] 1 x = some y' → ∀ p j', M[p]? = some (j', true) →
        ∀ y, scanExit slotArr ((M.map Prod.fst).drop (p + 1)) (M.length - (p + 1)) y' = some y →
        PassThru slotArr j' y := by
      intro y' hy' p j' hp y hy
      have hlt : p < M.length := (List.getElem?_eq_some_iff.mp hp).1
      refine hps p j' (by rw [List.getElem?_append_left hlt]; exact hp) y ?_
      have hd : ((M ++ [(j, b)]).map Prod.fst).drop (p + 1) =
          (M.map Prod.fst).drop (p + 1) ++ [j] := by
        rw [hsrc, List.drop_append_of_le_length (by omega)]
      have hn : (M ++ [(j, b)]).length - (p + 1) =
          ((M.map Prod.fst).drop (p + 1)).length + 1 := by simp; omega
      rw [hd, hn, scanExit_snoc, hy']
      rwa [List.length_drop, hl1]
    rw [hsrc] at h
    unfold accArr at h
    rw [List.length_append, List.length_singleton, ← hl1, reloadOf_snoc] at h
    cases b with
    | true =>
      have hkept : ((M ++ [(j, true)]).filter (fun p => !p.2)).map Prod.fst =
          (M.filter (fun p => !p.2)).map Prod.fst := by simp [List.filter_append]
      rw [hkept]
      obtain ⟨hs | hs, hr⟩ := hps M.length j (by simp) x (by simp [scanExit])
      · simp only [hs] at h
        exact ih x (tr x hs) (by unfold accArr; rwa [hl1] at h)
      · simp only [hs, hr] at h; simp at h
    | false =>
      have hkept : ((M ++ [(j, false)]).filter (fun p => !p.2)).map Prod.fst =
          (M.filter (fun p => !p.2)).map Prod.fst ++ [j] := by simp [List.filter_append]
      rw [hkept]
      unfold accArr
      rw [List.length_append, List.length_singleton, reloadOf_snoc]
      cases hs : scanExit slotArr [j] 1 x with
      | some y' =>
        simp only [hs] at h ⊢
        exact ih y' (tr y' hs) (by unfold accArr; rwa [hl1] at h)
      | none => simp only [hs] at h ⊢; exact h

/-- **Deleting instructions the scans pass through.** Let `M` mark a body in the class such
    that the reload scan of a base of every kept instruction passes every deleted instruction in
    front of it. Then the kept instructions form a body in the class. -/
theorem physImgB_kept_of_passThru {M : List (Linstr × Bool)}
    (h : physImgB slotArr (M.map Prod.fst) = true)
    (hps : ∀ m i, M[m]? = some (i, false) → ∀ x,
      (∃ ds o y ss, i.li_i = .Lopn ds o (.arrIdx x y 8 :: ss)) →
      ∀ p j, p < m → M[p]? = some (j, true) → ∀ y,
        scanExit slotArr (((M.map Prod.fst).take m).drop (p + 1)) (m - (p + 1)) x = some y →
        PassThru slotArr j y) :
    physImgB slotArr ((M.filter (fun p => !p.2)).map Prod.fst) = true := by
  refine physImgB_kept_of_prefix h fun M₁ M₂ i hM x hx ha => ?_
  subst hM
  have hl1 : (M₁.map Prod.fst).length = M₁.length := List.length_map _
  have hs : (M₁ ++ (i, false) :: M₂).map Prod.fst =
      M₁.map Prod.fst ++ i :: M₂.map Prod.fst := by
    simp
  refine accArr_kept_of_passThru M₁ x (fun p j hp y hy => ?_) ha
  have hlt : p < M₁.length := (List.getElem?_eq_some_iff.mp hp).1
  refine hps M₁.length i (by simp) x hx p j hlt
    (by rw [List.getElem?_append_left hlt]; exact hp) y ?_
  rw [hs, List.take_left' hl1]; exact hy

/-- A deleted instruction that is no move into `y` is passed by the scan for `y`. -/
theorem passThru_of_not_movInto {j : Linstr} {y : String}
    (hj : ∀ d s, slotMov? j.li_i = some (d, s) → d ≠ y) : PassThru slotArr j y :=
  scanStep_of_not_movInto hj

/-- The carried name of a scan of a concatenation: the scan of the front part for the name the
    scan of the back part carries. -/
theorem scanExit_append (slotArr : String → Option (String × Nat)) (a c : Lcmd) :
    ∀ (n : Nat) (x : String), scanExit slotArr (a ++ c) (a.length + n) x =
      (scanExit slotArr c n x).bind (scanExit slotArr a a.length)
  | 0, x => by simpa [scanExit] using scanExit_append_left slotArr a c a.length x le_rfl
  | n + 1, x => by
    have ih := scanExit_append slotArr a c n
    have hg : (a ++ c)[a.length + n]? = c[n]? := by
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    rw [show a.length + (n + 1) = (a.length + n) + 1 from rfl]
    simp only [scanExit, hg]
    cases c[n]? with
    | none => rfl
    | some j =>
      simp only
      cases slotMov? j.li_i with
      | some p =>
        obtain ⟨d, q⟩ := p
        simp only
        split_ifs <;> first | exact ih _ | rfl
      | none =>
        simp only
        cases j.li_i with
        | Lopn ds o ss =>
          simp only
          split_ifs
          · rfl
          · exact ih _
        | _ => rfl

/-- What one instruction does to the carried name: a move into it hands on a general-purpose
    source that is no array slot, and otherwise the name is kept by an operation that has no
    register destination naming it. -/
theorem scanExit_one_cases {j : Linstr} {y' y : String}
    (h : scanExit slotArr [j] 1 y' = some y) :
    (∃ q, slotMov? j.li_i = some (y', q) ∧ y = q ∧ (slotArr q).isNone = true ∧
        gpNameB q = true) ∨
      (y = y' ∧ ∃ ds o ss, j.li_i = .Lopn ds o ss ∧ ∀ q, LOperand.reg q ∈ ds → q ≠ y') := by
  simp only [scanExit, List.getElem?_cons_zero] at h
  cases hm : slotMov? j.li_i with
  | some p =>
    obtain ⟨d, q⟩ := p
    rw [hm] at h
    simp only at h
    by_cases h1 : d = y'
    · subst h1
      rw [if_pos rfl] at h
      split_ifs at h with h2
      simp only [Bool.and_eq_true] at h2
      simp only [Option.some.injEq] at h
      subst h
      exact Or.inl ⟨q, rfl, rfl, h2.1, h2.2⟩
    · rw [if_neg h1] at h
      split_ifs at h
      simp only [Option.some.injEq] at h
      subst h
      right
      refine ⟨rfl, ?_⟩
      rcases PhysImgFold.slotMov?_shape hm with he | he <;>
        exact ⟨_, _, _, he, fun q' hq' => by simp at hq'; rw [hq']; exact h1⟩
  | none =>
    rw [hm] at h
    simp only at h
    cases hj : j.li_i with
    | Lopn ds o ss =>
      rw [hj] at h
      simp only at h
      split_ifs at h with h1
      cases h
      right
      refine ⟨rfl, ds, o, ss, rfl, fun q hq hqy => ?_⟩
      subst hqy
      exact h1 (List.any_eq_true.mpr ⟨_, hq, by simp [dstHitB]⟩)
    | _ => rw [hj] at h; cases h

/-! ## 9. The dead-move elimination of `copyPropagateBody` -/

section DeadElim

open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate

/-- The decision of `deadElimStep` at `i` with the live set `live` behind it: a recognized
    self-copy or a recognized move whose destination is not live is deleted. -/
def deDrop (i : Linstr) (live : List String) : Bool :=
  match i.li_i with
  | .Lopn _ opn _ =>
      isRecognizedOpn opn &&
        (match moveShape i with
          | some (d, src, w) => (w == 64 && src == LOperand.reg d) || !(live.contains d)
          | none => false)
  | _ => false

/-- The live set that the backward fold of `deadElimBody` computes in front of a body. -/
def deLive (b : Lcmd) : List String := (b.foldr deadElimStep (physGPs, [])).1

/-- The marks of `deadElimBody`: each instruction with the flag that the pass deletes it. -/
def deMarks : Lcmd → List (Linstr × Bool)
  | [] => []
  | i :: is => (i, deDrop i (deLive is)) :: deMarks is

theorem deadElimStep_cases (i : Linstr) (live : List String) (acc : Lcmd) :
    deadElimStep i (live, acc) =
      if deDrop i live then (live, acc) else ((deadElimStep i (live, [])).1, i :: acc) := by
  cases hi : i.li_i with
  | Lopn ds opn srcs =>
    by_cases hrec : isRecognizedOpn opn = true
    · cases hcs : moveShape i with
      | none =>
        have hd : deDrop i live = false := by simp [deDrop, hi, hrec, hcs]
        rw [if_neg (by simp [hd]), deadElimStep_keep_none live acc hi hrec hcs,
          deadElimStep_keep_none live [] hi hrec hcs]
      | some q =>
        obtain ⟨d, src, ww⟩ := q
        by_cases hdr : ((ww == 64 && src == LOperand.reg d) || !(live.contains d)) = true
        · have hd : deDrop i live = true := by simp only [deDrop, hi, hrec, hcs]; simpa using hdr
          rw [if_pos hd, deadElimStep_drop live acc hi hrec hcs hdr]
        · have hdr' : ((ww == 64 && src == LOperand.reg d) || !(live.contains d)) = false := by
            simpa using hdr
          have hd : deDrop i live = false := by simp only [deDrop, hi, hrec, hcs]; simpa using hdr'
          rw [if_neg (by simp [hd]), deadElimStep_keep_some live acc hi hrec hcs hdr',
            deadElimStep_keep_some live [] hi hrec hcs hdr']
    · have hb : ∀ dsts opn' srcs', i.li_i = .Lopn dsts opn' srcs' →
          isRecognizedOpn opn' = false := by
        intro dsts opn' srcs' he; rw [hi] at he; cases he; simpa using hrec
      have hd : deDrop i live = false := by simp [deDrop, hi, hrec]
      rw [if_neg (by simp [hd]), deadElimStep_barrier i live acc hb,
        deadElimStep_barrier i live [] hb]
  | _ =>
    have hb : ∀ dsts opn' srcs', i.li_i = .Lopn dsts opn' srcs' →
        isRecognizedOpn opn' = false := by
      intro dsts opn' srcs' he; rw [hi] at he; cases he
    have hd : deDrop i live = false := by simp [deDrop, hi]
    rw [if_neg (by simp [hd]), deadElimStep_barrier i live acc hb,
      deadElimStep_barrier i live [] hb]

theorem deFoldr : ∀ b : Lcmd, b.foldr deadElimStep (physGPs, []) =
    (deLive b, ((deMarks b).filter (fun p => !p.2)).map Prod.fst)
  | [] => rfl
  | i :: is => by
    have ih := deFoldr is
    have e1 : (i :: is).foldr deadElimStep (physGPs, []) =
        deadElimStep i (deLive is, ((deMarks is).filter (fun p => !p.2)).map Prod.fst) := by
      rw [List.foldr_cons, ih]
    rw [show deLive (i :: is) = _ from congrArg Prod.fst e1, e1, deadElimStep_cases]
    simp only [deMarks]
    split <;> simp_all

theorem deMarks_fst : ∀ b : Lcmd, (deMarks b).map Prod.fst = b
  | [] => rfl
  | i :: is => by simp [deMarks, deMarks_fst is]

theorem deadElimBody_eq (b : Lcmd) :
    deadElimBody b = ((deMarks b).filter (fun p => !p.2)).map Prod.fst := by
  rw [deadElimBody, deFoldr]

theorem deLive_cons (i : Linstr) (is : Lcmd) :
    deLive (i :: is) =
      if deDrop i (deLive is) then deLive is else (deadElimStep i (deLive is, [])).1 := by
  unfold deLive
  rw [List.foldr_cons, deFoldr is, deadElimStep_cases]
  split <;> rfl

theorem deLive_nil : deLive [] = physGPs := rfl

theorem deMarks_getElem? : ∀ (b : Lcmd) (p : Nat) (j : Linstr) (t : Bool),
    (deMarks b)[p]? = some (j, t) → b[p]? = some j ∧ t = deDrop j (deLive (b.drop (p + 1)))
  | [], _, _, _, h => by simp [deMarks] at h
  | i :: is, 0, j, t, h => by
    simp only [deMarks, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | i :: is, p + 1, j, t, h => by
    simp only [deMarks, List.getElem?_cons_succ] at h
    simpa using deMarks_getElem? is p j t h

theorem contains_physGPs {y : String} (h : isPhysGP y = true) : physGPs.contains y = true := h

theorem mem_of_fullDefsOf {ds : List LOperand} {opn y : String}
    (h : (fullDefsOf ds opn).contains y = true) : LOperand.reg y ∈ ds := by
  unfold fullDefsOf at h
  split_ifs at h
  · simp only [regDefsOf, List.contains_iff_mem, List.mem_filterMap] at h
    obtain ⟨o, ho, he⟩ := h
    cases o with
    | reg n =>
      simp only at he
      split_ifs at he
      cases he
      exact ho
    | _ => cases he
  · simp at h

/-- **One backward step of the live set.** Behind an instruction that the pass keeps, a
    general-purpose name that the reload scan carries in front of the instruction is live,
    when the name the scan carries behind it is live. -/
theorem deLive_step {i : Linstr} {live : List String} (hk : deDrop i live = false)
    {y' y : String} (hy : scanExit slotArr [i] 1 y' = some y) (hgp : isPhysGP y = true)
    (hlive : isPhysGP y' = true → live.contains y' = true) :
    (deadElimStep i (live, [])).1.contains y = true := by
  have hb : (∀ dsts opn srcs, i.li_i = .Lopn dsts opn srcs → isRecognizedOpn opn = false) →
      (deadElimStep i (live, [])).1.contains y = true := fun h => by
    rw [deadElimStep_barrier i live [] h]; exact contains_physGPs hgp
  cases hi : i.li_i with
  | Lopn ds opn srcs =>
    by_cases hrec : isRecognizedOpn opn = true
    · have hkeep : (deadElimStep i (live, [])).1 =
          addRegs (live.filter fun r => !((fullDefsOf ds opn).contains r))
            (instrUses ds opn srcs) := by
        cases hcs : moveShape i with
        | none => rw [deadElimStep_keep_none live [] hi hrec hcs]
        | some q =>
          obtain ⟨d, src, ww⟩ := q
          have hdr : ((ww == 64 && src == LOperand.reg d) || !(live.contains d)) = false := by
            simpa [deDrop, hi, hrec, hcs] using hk
          rw [deadElimStep_keep_some live [] hi hrec hcs hdr]
      rw [hkeep]
      rcases scanExit_one_cases hy with ⟨q, hm, rfl, -, -⟩ | ⟨rfl, ds', o', ss', hi', hne⟩
      · refine contains_addRegs_right _ _ (contains_instrUses_of_src (o := .reg y) ?_ ?_)
        · rcases PhysImgFold.slotMov?_shape hm with he | he <;>
            · rw [hi] at he; cases he; simp
        · simp [operandReads, nameReads, hgp]
      · rw [hi] at hi'
        cases hi'
        refine contains_addRegs_left _ _ ?_
        simp only [List.contains_iff_mem, List.mem_filter, Bool.not_eq_true'] at ⊢
        refine ⟨by simpa using hlive hgp, ?_⟩
        cases hc : (fullDefsOf ds opn).contains y
        · rfl
        · exact absurd rfl (hne y (mem_of_fullDefsOf hc))
    · exact hb fun dsts opn' srcs' he => by rw [hi] at he; cases he; simpa using hrec
  | _ => exact hb fun dsts opn' srcs' he => by rw [hi] at he; cases he

/-- The base of an indexed access is live in front of it. -/
theorem deLive_acc {i : Linstr} {live : List String} {ds : List LOperand} {o x z : String}
    {ss : List LOperand} (hi : i.li_i = .Lopn ds o (.arrIdx x z 8 :: ss))
    (hgp : isPhysGP x = true) : (deadElimStep i (live, [])).1.contains x = true := by
  by_cases hrec : isRecognizedOpn o = true
  · have hcs : moveShape i = none := by
      unfold moveShape; rw [hi]
      split
      · rename_i heq; cases heq; simp [isFactSrc]
      · rfl
    rw [deadElimStep_keep_none live [] hi hrec hcs]
    refine contains_addRegs_right _ _ (contains_instrUses_of_src (o := .arrIdx x z 8)
      (by simp) ?_)
    simp [operandReads, hgp]
  · rw [deadElimStep_barrier i live [] (fun dsts opn' srcs' he => by
      rw [hi] at he; cases he; simpa using hrec)]
    exact contains_physGPs hgp

/-- A deleted instruction is no access. -/
theorem deDrop_not_acc {i : Linstr} {live : List String} {ds : List LOperand} {o x z : String}
    {ss : List LOperand} (hi : i.li_i = .Lopn ds o (.arrIdx x z 8 :: ss)) :
    deDrop i live = false := by
  have hcs : moveShape i = none := by
    unfold moveShape; rw [hi]
    split
    · rename_i heq; cases heq; simp [isFactSrc]
    · rfl
  simp [deDrop, hi, hcs]

theorem take_drop_cons {W : Lcmd} {m k : Nat} (hk : k < m) (hkW : k < W.length) :
    (W.take m).drop k = W[k] :: (W.take m).drop (k + 1) := by
  rw [List.drop_eq_getElem_cons (by simp; omega)]
  simp

/-- **The carried names are live.** Every general-purpose name that the reload scan of the base
    `x` of an access at position `m` of `A ++ b ++ C` carries to a position `k` of the segment
    `b` is in the live set that `deadElimBody` computes there. -/
theorem deLive_claim {A b C : Lcmd} {m : Nat} {i : Linstr} {ds : List LOperand} {o x z : String}
    {ss : List LOperand} (hm : (A ++ b ++ C)[m]? = some i)
    (hi : i.li_i = .Lopn ds o (.arrIdx x z 8 :: ss)) :
    ∀ t k, k + t = min m (A.length + b.length) → A.length ≤ k → ∀ y,
      scanExit slotArr (((A ++ b ++ C).take m).drop k) (m - k) x = some y →
      isPhysGP y = true → (deLive (b.drop (k - A.length))).contains y = true
  | 0, k, hk, hA, y, hy, hgp => by
    have hmW : m < (A ++ b ++ C).length := (List.getElem?_eq_some_iff.mp hm).1
    by_cases hmK : m < A.length + b.length
    · have hkm : k = m := by omega
      subst hkm
      simp only [Nat.sub_self, scanExit, Option.some.injEq] at hy
      subst hy
      have hb : b[k - A.length]? = some i := by
        rw [List.append_assoc, List.getElem?_append_right hA,
          List.getElem?_append_left (by omega)] at hm
        exact hm
      rw [List.drop_eq_getElem_cons (by omega), deLive_cons]
      have hbi : b[k - A.length] = i := by
        rw [List.getElem?_eq_getElem (by omega)] at hb; exact Option.some.inj hb
      rw [hbi, if_neg (by simp [deDrop_not_acc hi])]
      exact deLive_acc hi hgp
    · have hkK : k = A.length + b.length := by omega
      subst hkK
      rw [show A.length + b.length - A.length = b.length by omega, List.drop_length,
        deLive_nil]
      exact contains_physGPs hgp
  | t + 1, k, hk, hA, y, hy, hgp => by
    have hmW : m < (A ++ b ++ C).length := (List.getElem?_eq_some_iff.mp hm).1
    have hkm : k < m := by omega
    have hkK : k < A.length + b.length := by omega
    have hkW : k < (A ++ b ++ C).length := by omega
    have hjb : (A ++ b ++ C)[k] = b[k - A.length]'(by omega) := by
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega)]
    rw [take_drop_cons hkm hkW, show m - k = [(A ++ b ++ C)[k]].length + (m - (k + 1)) by
        simp; omega, show (A ++ b ++ C)[k] :: ((A ++ b ++ C).take m).drop (k + 1) =
        [(A ++ b ++ C)[k]] ++ ((A ++ b ++ C).take m).drop (k + 1) from rfl,
      scanExit_append] at hy
    cases hy' : scanExit slotArr (((A ++ b ++ C).take m).drop (k + 1)) (m - (k + 1)) x with
    | none => rw [hy'] at hy; cases hy
    | some y' =>
      rw [hy'] at hy
      simp only [Option.bind_some, List.length_singleton] at hy
      have ih := fun hg => deLive_claim hm hi t (k + 1) (by omega) (by omega) y' hy' hg
      rw [show k + 1 - A.length = k - A.length + 1 by omega] at ih
      rw [List.drop_eq_getElem_cons (by omega), deLive_cons]
      rw [hjb] at hy
      generalize hj : b[k - A.length]'(by omega) = j at hy ⊢
      split
      · rename_i hdrop
        rcases scanExit_one_cases hy with ⟨q, hmv, rfl, -, -⟩ | ⟨rfl, -⟩
        · cases hji : j.li_i with
          | Lopn ds' opn srcs =>
            simp only [deDrop, hji, Bool.and_eq_true] at hdrop
            obtain ⟨-, hdrop⟩ := hdrop
            cases hcs : moveShape j with
            | none => simp [hcs] at hdrop
            | some q' =>
              obtain ⟨d, src, ww⟩ := q'
              obtain ⟨opn', hj', hd, -, -⟩ := moveShape_inv hcs
              have hsh := PhysImgFold.slotMov?_shape hmv
              rw [hj'] at hsh
              have hdy : d = y' ∧ src = .reg y := by
                rcases hsh with he | he <;> (cases he; exact ⟨rfl, rfl⟩)
              obtain ⟨rfl, rfl⟩ := hdy
              simp only [hcs, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
                LOperand.reg.injEq, Bool.not_eq_true'] at hdrop
              rcases hdrop with ⟨-, rfl⟩ | hnl
              · exact ih hgp
              · rw [ih hd] at hnl; cases hnl
          | _ => simp [deDrop, hji] at hdrop
        · exact ih hgp
      · rename_i hkeep
        exact deLive_step (by simpa using hkeep) hy hgp ih

/-- A general-purpose name is no array slot when every array slot is a frame slot. -/
theorem slotArr_physGP (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    {d : String} (hd : isPhysGP d = true) : slotArr d = none := by
  cases h : slotArr d with
  | none => rfl
  | some _ =>
    have h1 := hq d (by simp [h])
    rw [PhysImgFold.isPhysGP_eq_gpNameB] at hd
    rw [(PhysImgFold.gpNameB_prefix hd).1] at h1
    cases h1

/-- A position of the marks of a segment inside a context that the marks delete. -/
theorem ctxMarks_true {A C : Lcmd} {Mb : List (Linstr × Bool)} {p : Nat} {j : Linstr}
    (hp : (A.map (fun i => (i, false)) ++ Mb ++ C.map (fun i => (i, false)))[p]? =
      some (j, true)) :
    ∃ p', p = A.length + p' ∧ Mb[p']? = some (j, true) := by
  rw [List.append_assoc] at hp
  rcases Nat.lt_or_ge p A.length with hlt | hge
  · rw [List.getElem?_append_left (by simpa using hlt)] at hp
    simp at hp
  obtain ⟨p', rfl⟩ : ∃ p', p = A.length + p' := ⟨p - A.length, by omega⟩
  rw [List.getElem?_append_right (by simp), List.length_map, Nat.add_sub_cancel_left] at hp
  rcases Nat.lt_or_ge p' Mb.length with hlt | hge
  · rw [List.getElem?_append_left hlt] at hp
    exact ⟨p', rfl, hp⟩
  · rw [List.getElem?_append_right hge] at hp
    simp at hp

/-- **The dead-move elimination keeps the image class inside a context**, when every array
    slot is a frame slot `qsave.R`. -/
theorem physImgB_deadElimBody_ctx
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {A b C : Lcmd}
    (h : physImgB slotArr (A ++ b ++ C) = true) :
    physImgB slotArr (A ++ deadElimBody b ++ C) = true := by
  have hM : (A.map (fun i => (i, false)) ++ deMarks b ++ C.map (fun i => (i, false))).map
      Prod.fst = A ++ b ++ C := by
    simp [List.map_map, Function.comp_def, deMarks_fst]
  have hK : ((A.map (fun i => (i, false)) ++ deMarks b ++ C.map (fun i => (i, false))).filter
      (fun p => !p.2)).map Prod.fst = A ++ deadElimBody b ++ C := by
    simp [List.filter_append, List.filter_map, Function.comp_def, List.map_map,
      deadElimBody_eq]
  rw [← hK]
  refine physImgB_kept_of_passThru (by rw [hM]; exact h) ?_
  intro m i hmi x hx p j hpm hpj y hy
  rw [hM] at hy
  have hW : (A ++ b ++ C)[m]? = some i := by
    rw [← hM, List.getElem?_map, hmi]; rfl
  obtain ⟨p', rfl, hp'⟩ := ctxMarks_true hpj
  obtain ⟨hbj, hdrop⟩ := deMarks_getElem? b p' j true hp'
  have hpb : p' < b.length := (List.getElem?_eq_some_iff.mp hbj).1
  obtain ⟨ds, o, z, ss, hxi⟩ := hx
  have hlive := fun hg => deLive_claim (slotArr := slotArr) hW hxi
    (min m (A.length + b.length) - (A.length + p' + 1)) (A.length + p' + 1) (by omega)
    (by omega) y hy hg
  rw [show A.length + p' + 1 - A.length = p' + 1 by omega] at hlive
  cases hji : j.li_i with
  | Lopn ds' opn srcs =>
    simp only [deDrop, hji] at hdrop
    cases hcs : moveShape j with
    | none => simp [hcs] at hdrop
    | some q' =>
      obtain ⟨d, src, ww⟩ := q'
      obtain ⟨opn', hj', hd, -, -⟩ := moveShape_inv hcs
      simp only [hcs] at hdrop
      by_cases hyd : y = d
      · subst hyd
        have hsd : slotArr y = none := slotArr_physGP hq hd
        have hcond := hdrop.symm
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
        rcases hcond.2 with ⟨-, rfl⟩ | hnl
        · cases hm : slotMov? j.li_i with
          | some p =>
            obtain ⟨d', s⟩ := p
            have hsh := PhysImgFold.slotMov?_shape hm
            rw [hj'] at hsh
            have hds : d' = y ∧ s = y := by
              rcases hsh with he | he <;> (cases he; exact ⟨rfl, rfl⟩)
            rw [hds.1, hds.2] at hm
            have hg : gpNameB y = true := by rwa [← PhysImgFold.isPhysGP_eq_gpNameB]
            refine ⟨Or.inl ?_, ?_⟩
            · simp only [scanExit, List.getElem?_cons_zero]; rw [hm]; simp [hsd, hg]
            · simp only [reloadOf, List.getElem?_cons_zero]; rw [hm]; simp [hsd, hg]
          | none =>
            refine ⟨Or.inr ?_, ?_⟩
            · simp only [scanExit, List.getElem?_cons_zero]; rw [hm, hj']; simp [dstHitB]
            · simp only [reloadOf, List.getElem?_cons_zero]; rw [hm, hj']; simp [dstHitB]
        · rw [hlive hd] at hnl; cases hnl
      · refine passThru_of_not_movInto fun d' s hm => ?_
        rw [hj'] at hm
        rw [slotMov?_single hm]
        exact Ne.symm hyd
  | _ => simp [deDrop, hji] at hdrop

end DeadElim

/-! ## 10. The move propagation of `copyPropagateBody` -/

section Propagate

open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate
open CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgFold (DomOn domOn_step dstOk_single)

/-- One step of `propagateAux`: the output instruction and the facts behind it. -/
def propStep (facts : List MoveFact) (i : Linstr) : Linstr × List MoveFact :=
  match i.li_i with
  | .Lopn dsts opn srcs =>
      if isRecognizedOpn opn then
        let dstSelf : Option String :=
          match dsts with
          | [.reg d] => if isPhysGP d then some d else none
          | _ => none
        let allowImm := isImmFoldable opn && dstSelf.isSome
        let srcs' := srcs.map (rewriteOperand facts (effWidth opn) allowImm dstSelf)
        let i' : Linstr := { i with li_i := .Lopn dsts opn srcs' }
        let facts₁ := (regDefsOf dsts).foldl killFacts facts
        let facts₂ :=
          match moveShape i' with
          | some (d, src, w) =>
              if src == LOperand.reg d then facts₁ else (d, src, w) :: facts₁
          | none => facts₁
        (i', facts₂)
      else (i, [])
  | _ => (i, [])

theorem propagateAux_cons (facts : List MoveFact) (i : Linstr) (rest : Lcmd) :
    propagateAux facts (i :: rest) =
      (propStep facts i).1 :: propagateAux (propStep facts i).2 rest := by
  unfold propStep
  cases hi : i.li_i with
  | Lopn dsts opn srcs =>
    simp only [propagateAux, hi]
    split <;> rfl
  | _ => simp only [propagateAux, hi]

/-- A source operand that `rewriteOperand` changes is a general-purpose name other than the
    destination, replaced by the source of a fact for it. -/
theorem rewriteOperand_cases (facts : List MoveFact) (w : Nat) (ai : Bool)
    (ds : Option String) (o : LOperand) :
    rewriteOperand facts w ai ds o = o ∨ ∃ u v fw, o = .reg u ∧ (u, v, fw) ∈ facts ∧
      isPhysGP u = true ∧ (ai || !isImmOperand v) = true ∧
      rewriteOperand facts w ai ds o = v := by
  cases o with
  | reg u =>
    simp only [rewriteOperand]
    split_ifs with h1
    · cases hl : lookupFact facts u with
      | none => left; rfl
      | some p =>
        obtain ⟨v, fw⟩ := p
        simp only
        split_ifs with h2
        · simp only [Bool.and_eq_true] at h1 h2
          exact Or.inr ⟨u, v, fw, rfl, lookupFact_mem hl, h1.1, h2.2, rfl⟩
        · left; rfl
    · left; rfl
  | _ => left; rfl

/-- The scan of `u` in the input resolves to an array slot only where the scan of the fact
    source `v` in the output resolves to it; an immediate source resolves nothing. -/
def FactDom (slotArr : String → Option (String × Nat)) (W W' : Lcmd) (k : Nat) (u : String)
    (v : LOperand) : Prop :=
  ∀ q, reloadOf slotArr W k u = some q → (slotArr q).isSome = true →
    match v with
    | .reg v' => reloadOf slotArr W' k v' = some q
    | _ => False

/-- The invariant of `propagateAux` at position `N` after the prefix `P`: the scan of the output
    dominates that of the input, and every fact `u ↦ v` names a general-purpose `u` written by
    an instruction of `P`, a fact source `v` (an immediate one only behind an instruction of `P`
    that is no move), and carries the scan of `u` to `v`. -/
def PropInv (slotArr : String → Option (String × Nat)) (W W' P : Lcmd) (N : Nat)
    (facts : List MoveFact) : Prop :=
  DomOn slotArr (fun _ => True) (fun y => reloadOf slotArr W N y)
      (fun y => reloadOf slotArr W' N y) ∧
    ∀ f ∈ facts, isPhysGP f.1 = true ∧ isFactSrc f.2.1 = true ∧
      (∃ j ∈ P, ∃ o ss, j.li_i = .Lopn [.reg f.1] o ss) ∧
      (isImmOperand f.2.1 = true → ∃ j ∈ P, slotMov? j.li_i = none) ∧
      FactDom slotArr W W' N f.1 f.2.1

theorem isImmFoldable_storeidx : isImmFoldable "STOREIDX" = false := by decide +kernel

theorem cellParts?_physGP {v : String} (h : isPhysGP v = true) : cellParts? v = none := by
  rw [PhysImgFold.isPhysGP_eq_gpNameB] at h
  simp [cellParts?, (PhysImgFold.gpNameB_prefix h).2]

/-- A move of `slotMov?` with its source replaced by a name that is no cell name is a move into
    the same destination. -/
theorem slotMov?_resrc {d o u v : String}
    (h : slotMov? (.Lopn [.reg d] o [.reg u]) = some (d, u)) (hv : cellParts? v = none) :
    slotMov? (.Lopn [.reg d] o [.reg v]) = some (d, v) := by
  simp only [slotMov?] at h ⊢
  split_ifs at h ⊢ with h1 h2 h3 <;> simp_all

/-- The facts behind a step that keep their name and source. -/
theorem mem_facts₁ {facts : List MoveFact} {d : String} {f : MoveFact}
    (hall : ∀ f ∈ facts, isPhysGP f.1 = true ∧ isFactSrc f.2.1 = true)
    (h : f ∈ (regDefsOf [LOperand.reg d]).foldl killFacts facts) :
    f ∈ facts ∧ f.1 ≠ d ∧ factSrcNames f.2.1 d = false := by
  rw [regDefsOf_singleton] at h
  by_cases hd : isPhysGP d = true
  · simp only [hd, if_true, List.foldl_cons, List.foldl_nil] at h
    exact mem_killFacts h
  · simp only [hd, Bool.false_eq_true, if_false, List.foldl_nil] at h
    have hd' : isPhysGP d = false := by simpa using hd
    obtain ⟨h1, h2⟩ := hall f h
    refine ⟨h, fun he => ?_, factSrcNames_of_isFactSrc h2 hd'⟩
    rw [he, hd'] at h1; cases h1

section PropStep

variable {W W' : Lcmd} {N : Nat} {i : Linstr} {d o : String} {ss : List LOperand}

/-- **One step of `propagateAux` keeps the invariant**, and the output instruction is the input,
    an instruction with no access and no array-slot destination, or an indexed store with
    another stored register; a move of the input stays a move into the same name unless an
    instruction in front of it is no move. -/
theorem propInv_step {P : Lcmd} {facts : List MoveFact}
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    (hW : W[N]? = some i) (hW' : W'[N]? = some (propStep facts i).1)
    (hj : i.li_i = .Lopn [.reg d] o ss) (hPW : ∀ j ∈ P, j ∈ W.take N)
    (hwb : slotWriteB slotArr W N i.li_i = true) (hacc : accOkB slotArr W N i.li_i = true)
    (hinv : PropInv slotArr W W' P N facts) :
    PropInv slotArr W W' (P ++ [i]) (N + 1) (propStep facts i).2 ∧
      ((propStep facts i).1 = i ∨
        (isAccB (propStep facts i).1.li_i = false ∧ DstOk slotArr (propStep facts i).1.li_i) ∨
        ∃ ds o b0 j0 v v', i.li_i = .Lopn ds o [.arrIdx b0 j0 8, .reg v] ∧
          (propStep facts i).1.li_i = .Lopn ds o [.arrIdx b0 j0 8, .reg v']) ∧
      ((∀ d' s, slotMov? i.li_i = some (d', s) →
          ∃ s', slotMov? (propStep facts i).1.li_i = some (d', s')) ∨
        ∃ j ∈ P, slotMov? j.li_i = none) := by
  obtain ⟨hdom, hall⟩ := hinv
  have hall' : ∀ f ∈ facts, isPhysGP f.1 = true ∧ isFactSrc f.2.1 = true :=
    fun f hf => ⟨(hall f hf).1, (hall f hf).2.1⟩
  have hmono : ∀ f ∈ facts, ∃ j ∈ P ++ [i], ∃ o ss, j.li_i = .Lopn [.reg f.1] o ss := by
    intro f hf
    obtain ⟨j, hjP, o', ss', hj'⟩ := (hall f hf).2.2.1
    exact ⟨j, List.mem_append_left _ hjP, o', ss', hj'⟩
  have hmonoI : ∀ f ∈ facts, isImmOperand f.2.1 = true → ∃ j ∈ P ++ [i], slotMov? j.li_i = none :=
    by
    intro f hf hi
    obtain ⟨j, hjP, hj'⟩ := (hall f hf).2.2.2.1 hi
    exact ⟨j, List.mem_append_left _ hjP, hj'⟩
  by_cases hrec : isRecognizedOpn o = true
  swap
  · have hst : propStep facts i = (i, []) := by simp [propStep, hj, hrec]
    rw [hst] at hW' ⊢
    refine ⟨⟨fun x _ q hf hq' => ?_, fun f hf => by simp at hf⟩, Or.inl rfl, Or.inl
      fun d' s h => ⟨s, h⟩⟩
    simp only at hf ⊢
    rw [PhysImgFold.reloadOf_succ_eq slotArr hW] at hf
    rw [PhysImgFold.reloadOf_succ_eq slotArr hW']
    exact domOn_step (fun _ _ => trivial) hdom i x trivial q hf hq'
  obtain ⟨rw, ai, hrwc, hai, hps1, hps2⟩ : ∃ (rw : LOperand → LOperand) (ai : Bool),
      (∀ o', rw o' = o' ∨ ∃ u v fw, o' = .reg u ∧ (u, v, fw) ∈ facts ∧ isPhysGP u = true ∧
        (ai || !isImmOperand v) = true ∧ rw o' = v) ∧
      (o = "STOREIDX" → ai = false) ∧
      (propStep facts i).1 = ⟨i.li_ii, .Lopn [.reg d] o (ss.map rw)⟩ ∧
      (propStep facts i).2 =
        (match moveShape (⟨i.li_ii, .Lopn [.reg d] o (ss.map rw)⟩ : Linstr) with
          | some (d', src, w) =>
              if src == LOperand.reg d' then (regDefsOf [.reg d]).foldl killFacts facts
              else (d', src, w) :: (regDefsOf [.reg d]).foldl killFacts facts
          | none => (regDefsOf [.reg d]).foldl killFacts facts) :=
    ⟨rewriteOperand facts (effWidth o)
        (isImmFoldable o && (if isPhysGP d = true then some d else none).isSome)
        (if isPhysGP d = true then some d else none),
      isImmFoldable o && (if isPhysGP d = true then some d else none).isSome,
      fun o' => rewriteOperand_cases _ _ _ _ o',
      fun h => by subst h; simp [isImmFoldable_storeidx],
      by simp only [propStep, hj, hrec, if_true], by simp only [propStep, hj, hrec, if_true]⟩
  have hj' : (propStep facts i).1.li_i = .Lopn [.reg d] o (ss.map rw) := by rw [hps1]
  -- a fact source for a name that a fact rewrites
  have hfact : ∀ u, rw (.reg u) ≠ .reg u → ∃ fw, (u, rw (.reg u), fw) ∈ facts ∧
      isPhysGP u = true ∧ (ai || !isImmOperand (rw (.reg u))) = true := by
    intro u hne
    rcases hrwc (.reg u) with h | ⟨u', v, fw, he, hm, hp, hai', hv⟩
    · exact absurd h hne
    · cases he; rw [hv]; exact ⟨fw, hm, hp, hai'⟩
  by_cases hsd : slotArr d = none
  · have hsdn : (slotArr d).isNone = true := by simp [hsd]
    -- the scan of the destination behind the step
    have hdomd : ∀ q, reloadOf slotArr W (N + 1) d = some q → (slotArr q).isSome = true →
        reloadOf slotArr W' (N + 1) d = some q := by
      intro q hf hq'
      cases hm : slotMov? i.li_i with
      | none => rw [reloadOf_succ_noMov hW hj hm] at hf; cases hf
      | some p =>
        obtain ⟨d', u0⟩ := p
        have hd' : d' = d := by rw [hj] at hm; exact slotMov?_single hm
        subst hd'
        have hss : ss = [.reg u0] := by
          rcases PhysImgFold.slotMov?_shape hm with he | he <;> (rw [hj] at he; cases he; rfl)
        subst hss
        rw [reloadOf_succ_mov hW hm] at hf
        by_cases hu : rw (.reg u0) = .reg u0
        · have hm' : slotMov? (propStep facts i).1.li_i = some (d', u0) := by
            rw [hj']; simp only [List.map_cons, List.map_nil, hu]; rw [← hj]; exact hm
          rw [reloadOf_succ_mov hW' hm']
          exact movDom_of_dom hdom u0 q hf hq'
        · obtain ⟨fw, hmf, hpu, -⟩ := hfact u0 hu
          have hFD := (hall _ hmf).2.2.2.2
          have hcu : ((slotArr u0).isNone && gpNameB u0) = true := by
            simp [slotArr_physGP hq hpu, ← PhysImgFold.isPhysGP_eq_gpNameB, hpu]
          unfold movScan at hf
          rw [if_pos hcu] at hf
          have := hFD q hf hq'
          generalize hv : rw (.reg u0) = v at this
          cases v with
          | reg v' =>
            have hpv : isPhysGP v' = true := by
              have := (hall _ hmf).2.1; rw [hv] at this; exact this
            have hm' : slotMov? (propStep facts i).1.li_i = some (d', v') := by
              rw [hj']; simp only [List.map_cons, List.map_nil, hv]
              rw [hj] at hm
              exact slotMov?_resrc hm (cellParts?_physGP hpv)
            rw [reloadOf_succ_mov hW' hm']
            unfold movScan
            rw [if_pos (by simp [slotArr_physGP hq hpv, ← PhysImgFold.isPhysGP_eq_gpNameB, hpv])]
            exact this
          | _ => exact this.elim
    -- the facts behind the step
    have hfacts : ∀ f ∈ (propStep facts i).2, isPhysGP f.1 = true ∧ isFactSrc f.2.1 = true ∧
        (∃ j ∈ P ++ [i], ∃ o ss, j.li_i = .Lopn [.reg f.1] o ss) ∧
        (isImmOperand f.2.1 = true → ∃ j ∈ P ++ [i], slotMov? j.li_i = none) ∧
        FactDom slotArr W W' (N + 1) f.1 f.2.1 := by
      have hsurv : ∀ f ∈ (regDefsOf [.reg d]).foldl killFacts facts,
          isPhysGP f.1 = true ∧ isFactSrc f.2.1 = true ∧
          (∃ j ∈ P ++ [i], ∃ o ss, j.li_i = .Lopn [.reg f.1] o ss) ∧
          (isImmOperand f.2.1 = true → ∃ j ∈ P ++ [i], slotMov? j.li_i = none) ∧
          FactDom slotArr W W' (N + 1) f.1 f.2.1 := by
        intro f hf
        obtain ⟨hmf, hne, hsn⟩ := mem_facts₁ hall' hf
        refine ⟨(hall f hmf).1, (hall f hmf).2.1, hmono f hmf, hmonoI f hmf, fun q hF hq' => ?_⟩
        rw [reloadOf_succ_ne hW hj hne hsdn] at hF
        have := (hall f hmf).2.2.2.2 q hF hq'
        generalize f.2.1 = v at this hsn ⊢
        cases v with
        | reg v' =>
          have hv' : v' ≠ d := by simpa [factSrcNames] using hsn
          simp only at this ⊢
          rw [reloadOf_succ_ne hW' hj' hv' hsdn]
          exact this
        | _ => exact this.elim
      rw [hps2]
      intro f hf
      split at hf
      · rename_i d' src w hms
        split at hf
        · exact hsurv f hf
        · rcases List.mem_cons.mp hf with rfl | hf
          · rename_i hsrc
            obtain ⟨opn', hsh, hpd, hfs, -⟩ := moveShape_inv hms
            simp only [LinstrR.Lopn.injEq, List.cons.injEq, LOperand.reg.injEq, and_true] at hsh
            obtain ⟨rfl, -, hsrcs⟩ := hsh
            obtain ⟨s0, rfl, hs0⟩ : ∃ s0, ss = [s0] ∧ rw s0 = src := by
              cases ss with
              | nil => simp at hsrcs
              | cons s0 t =>
                cases t with
                | nil => simp at hsrcs; exact ⟨s0, rfl, hsrcs⟩
                | cons _ _ => simp at hsrcs
            refine ⟨hpd, hfs, ⟨i, by simp, o, [s0], hj⟩, fun himm => ?_, fun q hF hq' => ?_⟩
            · cases hm : slotMov? i.li_i with
              | none => exact ⟨i, by simp, hm⟩
              | some p =>
                obtain ⟨d'', u0⟩ := p
                have hs0' : s0 = .reg u0 := by
                  rcases PhysImgFold.slotMov?_shape hm with he | he <;>
                    (rw [hj] at he; cases he; rfl)
                subst hs0'
                have hu : rw (.reg u0) ≠ .reg u0 := by
                  intro he; rw [he] at hs0; subst hs0; simp [isImmOperand] at himm
                obtain ⟨fw, hmf, -, -⟩ := hfact u0 hu
                rw [hs0] at hmf
                exact hmonoI _ hmf himm
            · cases hm : slotMov? i.li_i with
              | none => rw [reloadOf_succ_noMov hW hj hm] at hF; cases hF
              | some p =>
                obtain ⟨d'', u0⟩ := p
                have hd'' : d'' = d := by rw [hj] at hm; exact slotMov?_single hm
                subst hd''
                have hs0' : s0 = .reg u0 := by
                  rcases PhysImgFold.slotMov?_shape hm with he | he <;>
                    (rw [hj] at he; cases he; rfl)
                subst hs0'
                rw [reloadOf_succ_mov hW hm] at hF
                have hpu : isPhysGP u0 = true := by
                  by_cases hu : rw (.reg u0) = .reg u0
                  · rw [hu] at hs0; subst hs0; exact hfs
                  · obtain ⟨_, _, hp, _⟩ := hfact u0 hu
                    exact hp
                unfold movScan at hF
                rw [if_pos (by simp [slotArr_physGP hq hpu, ← PhysImgFold.isPhysGP_eq_gpNameB,
                  hpu])] at hF
                have hdomu : ∃ v', src = .reg v' ∧ reloadOf slotArr W' N v' = some q := by
                  by_cases hu : rw (.reg u0) = .reg u0
                  · rw [hu] at hs0
                    exact ⟨u0, hs0.symm, hdom u0 trivial q hF hq'⟩
                  · obtain ⟨fw, hmf, -, -⟩ := hfact u0 hu
                    rw [hs0] at hmf
                    have := (hall _ hmf).2.2.2.2 q hF hq'
                    revert this
                    cases src with
                    | reg v' => exact fun h => ⟨v', rfl, h⟩
                    | _ => exact False.elim
                obtain ⟨v', hsv, hv⟩ := hdomu
                rw [hsv] at hsrc ⊢
                have hv' : v' ≠ d'' := by
                  intro he; rw [he] at hsrc; simp at hsrc
                simp only
                rw [reloadOf_succ_ne hW' hj' hv' hsdn]
                exact hv
          · exact hsurv f hf
      · exact hsurv f hf
    refine ⟨⟨fun x _ q hf hq' => ?_, hfacts⟩, ?_, ?_⟩
    · simp only at hf ⊢
      by_cases hx : x = d
      · subst hx; exact hdomd q hf hq'
      · exact dom_succ_ne hW hW' hj hj' hdom hx hf hq'
    · by_cases hmap : ss.map rw = ss
      · left; rw [hps1, hmap, ← hj]
      · right
        by_cases hna : isAccB (propStep facts i).1.li_i = false
        · exact Or.inl ⟨hna, by rw [hj']; exact dstOk_single hsd⟩
        · right
          rw [hj'] at hna
          simp only [isAccB, Bool.or_eq_false_iff, beq_eq_false_iff_ne, not_and_or,
            not_not] at hna
          rw [hj] at hacc
          rcases hna with rfl | rfl
          · exfalso
            simp only [accOkB, if_true] at hacc
            split at hacc
            · rename_i heq
              simp only [LinstrR.Lopn.injEq] at heq
              obtain ⟨-, -, rfl⟩ := heq
              refine hmap ?_
              simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
              rcases hrwc (.arrIdx _ _ 8) with h | ⟨_, _, _, h, _⟩
              · exact h
              · cases h
            · cases hacc
          · simp only [accOkB, show ("STOREIDX" = "LOADIDX") = False from by decide,
              if_false, if_true] at hacc
            split at hacc
            · rename_i b0 j0 v
              have hrv : ∃ v', rw (.reg v) = .reg v' := by
                rcases hrwc (.reg v) with h | ⟨u, w0, fw, he, hm, -, hai', h⟩
                · exact ⟨v, h⟩
                · rw [hai rfl] at hai'
                  have hfs := (hall _ hm).2.1
                  cases w0 with
                  | reg v' => exact ⟨v', h⟩
                  | imm _ => simp [isImmOperand] at hai'
                  | arr _ _ => simp [isFactSrc] at hfs
                  | arrIdx _ _ _ => simp [isFactSrc] at hfs
              obtain ⟨v', hv'⟩ := hrv
              have ha : rw (.arrIdx b0 j0 8) = .arrIdx b0 j0 8 := by
                rcases hrwc (.arrIdx b0 j0 8) with h | ⟨_, _, _, h, _⟩
                · exact h
                · cases h
              exact ⟨[.reg d], "STOREIDX", b0, j0, v, v', hj, by
                rw [hj']; simp [ha, hv']⟩
            · cases hacc
    · cases hm : slotMov? i.li_i with
      | none => exact Or.inl fun d' s h => by cases h
      | some p =>
        obtain ⟨d', u0⟩ := p
        have hd' : d' = d := by rw [hj] at hm; exact slotMov?_single hm
        subst hd'
        have hss : ss = [.reg u0] := by
          rcases PhysImgFold.slotMov?_shape hm with he | he <;> (rw [hj] at he; cases he; rfl)
        subst hss
        by_cases hu : rw (.reg u0) = .reg u0
        · refine Or.inl fun d'' s h => ⟨u0, ?_⟩
          cases h
          rw [hj']; simp only [List.map_cons, List.map_nil, hu]; rw [← hj]; exact hm
        · obtain ⟨fw, hmf, -, -⟩ := hfact u0 hu
          generalize hv : rw (.reg u0) = v at hmf
          cases v with
          | reg v' =>
            refine Or.inl fun d'' s h => ⟨v', ?_⟩
            cases h
            have hpv : isPhysGP v' = true := (hall _ hmf).2.1
            rw [hj']; simp only [List.map_cons, List.map_nil, hv]
            rw [hj] at hm
            exact slotMov?_resrc hm (cellParts?_physGP hpv)
          | imm n =>
            obtain ⟨j, hjP, hjm⟩ := (hall _ hmf).2.2.2.1 rfl
            exact Or.inr ⟨j, hjP, hjm⟩
          | arr _ _ => have := (hall _ hmf).2.1; simp [isFactSrc] at this
          | arrIdx _ _ _ => have := (hall _ hmf).2.1; simp [isFactSrc] at this
  · -- a save `qsave.R ← R`: no fact names `R`, so the step keeps the instruction
    have hss : ∃ R, slotMov? i.li_i = some (d, R) ∧ entryRegB W N R = true ∧ ss = [.reg R] := by
      rw [hj] at hwb
      simp only [slotWriteB, List.all_cons, List.all_nil, Bool.and_true, Bool.or_eq_true] at hwb
      rcases hwb with h | h
      · exact absurd (by simpa using h) hsd
      · cases hm : slotMov? (.Lopn [.reg d] o ss) with
        | none => rw [hm] at h; cases h
        | some p =>
          obtain ⟨q', R⟩ := p
          rw [hm] at h
          simp only [Bool.and_eq_true] at h
          have hq' : q' = d := slotMov?_single hm
          subst hq'
          refine ⟨R, by rw [hj]; exact hm, h.2, ?_⟩
          rcases PhysImgFold.slotMov?_shape hm with he | he <;> (cases he; rfl)
    obtain ⟨R, hmR, hent, rfl⟩ := hss
    have hR : rw (.reg R) = .reg R := by
      by_contra hne
      obtain ⟨fw, hmf, -, -⟩ := hfact R hne
      obtain ⟨j, hjP, o', ss', hj''⟩ := (hall _ hmf).2.2.1
      have := List.all_eq_true.mp hent j (hPW j hjP)
      cases hm : slotMov? j.li_i with
      | none => rw [hm] at this; cases this
      | some p =>
        obtain ⟨d', s⟩ := p
        rw [hm] at this
        rw [hj''] at hm
        have := slotMov?_single hm
        subst this
        simp at this
    have hi' : (propStep facts i).1 = i := by
      rw [hps1]; simp only [List.map_cons, List.map_nil, hR]; rw [← hj]
    have hpd : isPhysGP d = false := by
      cases h : isPhysGP d
      · rfl
      · exact absurd (slotArr_physGP hq h) hsd
    have hfa : (propStep facts i).2 = facts := by
      have e : (⟨i.li_ii, .Lopn [.reg d] o (List.map rw [.reg R])⟩ : Linstr) = i := by
        simp only [List.map_cons, List.map_nil, hR]; rw [← hj]
      rw [hps2, e]
      have hms : moveShape i = none := by
        cases h : moveShape i with
        | none => rfl
        | some p =>
          obtain ⟨d', src, w⟩ := p
          obtain ⟨opn', hsh, hpd', -, -⟩ := moveShape_inv h
          rw [hj] at hsh
          cases hsh
          rw [hpd] at hpd'; cases hpd'
      simp [hms, regDefsOf_singleton, hpd]
    have hW'' : W'[N]? = some i := by rw [hW', hi']
    rw [hfa, hi']
    refine ⟨⟨fun x _ q hf hq' => ?_, fun f hf => ⟨(hall f hf).1, (hall f hf).2.1, hmono f hf,
      hmonoI f hf, fun q hF hq' => ?_⟩⟩, Or.inl rfl, Or.inl fun d' s h => ⟨s, h⟩⟩
    · simp only at hf ⊢
      rw [PhysImgFold.reloadOf_succ_eq slotArr hW] at hf
      rw [PhysImgFold.reloadOf_succ_eq slotArr hW'']
      exact domOn_step (fun _ _ => trivial) hdom i x trivial q hf hq'
    · exfalso
      have hne : f.1 ≠ d := by
        intro he; rw [← he, (hall f hf).1] at hpd; cases hpd
      rw [reloadOf_succ_single hW hj hne, if_neg (by simpa using hsd)] at hF
      cases hF

end PropStep

theorem propagateAux_length : ∀ (facts : List MoveFact) (b : Lcmd),
    (propagateAux facts b).length = b.length
  | _, [] => rfl
  | facts, i :: is => by
    rw [propagateAux_cons]; simp [propagateAux_length _ is]

/-- The positions of `propagateAux` over the rest `rest` of the segment `b = P ++ rest` of
    `A ++ b ++ C`: the scan of the output dominates that of the input, each output instruction
    is the input one, one with no access and no array-slot destination, or an indexed store of
    another register, and a move stays a move into the same name unless an instruction of the
    segment in front of it is no move. -/
theorem prop_main {A b C : Lcmd}
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true)
    (h : physImgB slotArr (A ++ b ++ C) = true) :
    ∀ (rest P Q : Lcmd) (facts : List MoveFact), b = P ++ rest → Q.length = P.length →
      propagateAux [] b = Q ++ propagateAux facts rest → (∀ j ∈ rest, instrModeled j = true) →
      PropInv slotArr (A ++ b ++ C) (A ++ propagateAux [] b ++ C) P (A.length + P.length) facts →
      (∀ p, p ≤ rest.length → DomOn slotArr (fun _ => True)
        (fun y => reloadOf slotArr (A ++ b ++ C) (A.length + P.length + p) y)
        (fun y => reloadOf slotArr (A ++ propagateAux [] b ++ C) (A.length + P.length + p) y)) ∧
      (∀ (p : Nat) (i i' : Linstr), rest[p]? = some i → (propagateAux facts rest)[p]? = some i' →
        (i' = i ∨ (isAccB i'.li_i = false ∧ DstOk slotArr i'.li_i) ∨
          ∃ ds o b0 j0 v v', i.li_i = .Lopn ds o [.arrIdx b0 j0 8, .reg v] ∧
            i'.li_i = .Lopn ds o [.arrIdx b0 j0 8, .reg v']) ∧
        ((∀ d s, slotMov? i.li_i = some (d, s) → ∃ s', slotMov? i'.li_i = some (d, s')) ∨
          ∃ j ∈ P ++ rest.take p, slotMov? j.li_i = none))
  | [], _, _, _, _, _, _, _, hinv => by
    refine ⟨fun p hp => ?_, fun p _ _ hp => by simp at hp⟩
    simp only [List.length_nil, Nat.le_zero] at hp
    subst hp
    exact hinv.1
  | i :: is, P, Q, facts, hb, hQ, hout, hmod, hinv => by
    obtain ⟨d, o, ss, hj⟩ := instrModeled_shape (hmod i (by simp))
    have hW : (A ++ b ++ C)[A.length + P.length]? = some i := by
      rw [hb, List.append_assoc, List.getElem?_append_right (by omega),
        show A.length + P.length - A.length = P.length by omega, List.append_assoc,
        List.getElem?_append_right le_rfl, Nat.sub_self]
      rfl
    have hW' : (A ++ propagateAux [] b ++ C)[A.length + P.length]? =
        some (propStep facts i).1 := by
      rw [hout, propagateAux_cons, List.append_assoc, List.getElem?_append_right (by omega),
        show A.length + P.length - A.length = P.length by omega, List.append_assoc,
        List.getElem?_append_right (by omega), ← hQ, Nat.sub_self]
      rfl
    have hPW : ∀ j ∈ P, j ∈ (A ++ b ++ C).take (A.length + P.length) := by
      intro j hj
      rw [hb, List.append_assoc, List.take_append, List.take_of_length_le (by omega),
        show A.length + P.length - A.length = P.length by omega, List.append_assoc,
        List.take_append, List.take_of_length_le le_rfl]
      simp [hj]
    obtain ⟨h1, h2⟩ := PhysImgFold.physImgB_getElem h hW
    obtain ⟨hinv', hpt, hent⟩ := propInv_step hq hW hW' hj hPW h2 h1 hinv
    have ih := prop_main hq h is (P ++ [i]) (Q ++ [(propStep facts i).1])
      (propStep facts i).2 (by simp [hb]) (by simp [hQ]) (by rw [hout, propagateAux_cons]; simp)
      (fun j hj => hmod j (by simp [hj])) (by simpa [Nat.add_assoc] using hinv')
    refine ⟨fun p hp => ?_, fun p j j' hp hp' => ?_⟩
    · cases p with
      | zero => simpa using hinv.1
      | succ p =>
        have := ih.1 p (by simp at hp; omega)
        simp only [List.length_append, List.length_singleton] at this
        rwa [show A.length + P.length + (p + 1) = A.length + (P.length + 1) + p by omega]
    · cases p with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, propagateAux_cons] at hp hp'
        subst hp hp'
        exact ⟨hpt, hent.imp id fun ⟨j, hjP, hjm⟩ => ⟨j, by simp [hjP], hjm⟩⟩
      | succ p =>
        simp only [List.getElem?_cons_succ, propagateAux_cons] at hp hp'
        obtain ⟨h1, h2⟩ := ih.2 p j j' hp hp'
        exact ⟨h1, h2.imp id fun ⟨j, hjP, hjm⟩ => ⟨j, by simpa using hjP, hjm⟩⟩

/-- **The move propagation keeps the image class inside a context**, on a modeled segment, when
    every array slot is a frame slot `qsave.R`. -/
theorem physImgB_propagateAux_ctx
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {A b C : Lcmd}
    (h : physImgB slotArr (A ++ b ++ C) = true) (hmod : bodyAllModeled b = true) :
    physImgB slotArr (A ++ propagateAux [] b ++ C) = true := by
  have hm := prop_main (A := A) (C := C) hq h b [] [] [] rfl rfl rfl
    (fun j hj => List.all_eq_true.mp hmod j hj)
    ⟨fun x _ q hf _ => by
      simp only [List.length_nil, Nat.add_zero] at hf ⊢
      rw [List.append_assoc, reloadOf_append_left _ _ _ _ _ le_rfl] at hf
      rw [List.append_assoc, reloadOf_append_left _ _ _ _ _ le_rfl]
      exact hf, fun _ hf => by simp at hf⟩
  have hlen : (propagateAux [] b).length = b.length := propagateAux_length [] b
  have hpos : ∀ (k : Nat) (i i' : Linstr), (A ++ b ++ C)[k]? = some i →
      (A ++ propagateAux [] b ++ C)[k]? = some i' →
      (i' = i ∨ (isAccB i'.li_i = false ∧ DstOk slotArr i'.li_i) ∨
        ∃ ds o b0 j0 v v', i.li_i = .Lopn ds o [.arrIdx b0 j0 8, .reg v] ∧
          i'.li_i = .Lopn ds o [.arrIdx b0 j0 8, .reg v']) ∧
      ((∀ d s, slotMov? i.li_i = some (d, s) → ∃ s', slotMov? i'.li_i = some (d, s')) ∨
        ∃ (p : Nat) (j : Linstr), p < k ∧ (A ++ b ++ C)[p]? = some j ∧
          slotMov? j.li_i = none) := by
    intro k i i' hk hk'
    rcases Nat.lt_or_ge k A.length with hA | hA
    · rw [List.append_assoc, List.getElem?_append_left hA] at hk hk'
      rw [hk] at hk'; cases hk'; exact ⟨Or.inl rfl, Or.inl fun d s hs => ⟨s, hs⟩⟩
    obtain ⟨p, rfl⟩ : ∃ p, k = A.length + p := ⟨k - A.length, by omega⟩
    have hk0 := hk
    rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      at hk hk'
    rcases Nat.lt_or_ge p b.length with hb | hb
    · rw [List.getElem?_append_left hb] at hk
      rw [List.getElem?_append_left (by omega)] at hk'
      obtain ⟨h1, h2⟩ := hm.2 p i i' hk hk'
      refine ⟨h1, h2.imp id fun ⟨j, hjP, hjm⟩ => ?_⟩
      simp only [List.nil_append] at hjP
      obtain ⟨p', hp', hpj⟩ := List.getElem_of_mem hjP
      simp only [List.length_take] at hp'
      refine ⟨A.length + p', j, by omega, ?_, hjm⟩
      rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        List.getElem?_append_left (by omega), ← hpj, List.getElem_take]
      exact List.getElem?_eq_getElem _
    · rw [List.getElem?_append_right hb] at hk
      rw [List.getElem?_append_right (by omega), hlen] at hk'
      rw [hk] at hk'; cases hk'; exact ⟨Or.inl rfl, Or.inl fun d s hs => ⟨s, hs⟩⟩
  refine physImgB_of_dom (S := fun _ => True) h (by simp [hlen]) (fun k => ?_)
    (fun k i i' hk hk' => (hpos k i i' hk hk').1)
    (fun _ _ _ _ _ _ _ _ _ => trivial)
    (fun k i i' hk hk' => (hpos k i i' hk hk').2)
  rcases Nat.lt_or_ge k (A.length + b.length) with hk | hk
  · rcases Nat.lt_or_ge k A.length with hA | hA
    · intro x _ q hf _
      simp only at hf ⊢
      rw [List.append_assoc, reloadOf_append_left _ _ _ _ _ hA.le] at hf
      rw [List.append_assoc, reloadOf_append_left _ _ _ _ _ hA.le]
      exact hf
    · have := hm.1 (k - A.length) (by simp; omega)
      simpa [show A.length + (k - A.length) = k by omega] using this
  · have h0 := hm.1 b.length (by simp)
    simp only [List.length_nil, Nat.add_zero] at h0
    have := domOn_reloadOf_common (fun _ _ => trivial) h0 (fun k hk' => by
      rw [List.append_assoc, List.append_assoc, List.getElem?_append_right (by omega),
        List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
        List.getElem?_append_right (by omega), hlen]) (k - (A.length + b.length))
    simpa [show A.length + b.length + (k - (A.length + b.length)) = k by omega] using this

/-- **`copyPropagateBody` keeps the image class inside a context**, on a modeled segment, when
    every array slot is a frame slot `qsave.R`. -/
theorem physImgB_copyPropagateBody_ctx
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {A b C : Lcmd}
    (h : physImgB slotArr (A ++ b ++ C) = true) (hmod : bodyAllModeled b = true) :
    physImgB slotArr (A ++ copyPropagateBody b ++ C) = true :=
  physImgB_deadElimBody_ctx hq (physImgB_propagateAux_ctx hq h hmod)

/-- **`copyPropagateBody` keeps the image class** on a modeled body, when every array slot is a
    frame slot `qsave.R`. -/
theorem physImgB_copyPropagateBody
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {b : Lcmd}
    (h : physImgB slotArr b = true) (hmod : bodyAllModeled b = true) :
    physImgB slotArr (copyPropagateBody b) = true := by
  simpa using physImgB_copyPropagateBody_ctx (A := []) (C := []) hq (by simpa using h) hmod

end Propagate

/-! ## 11. The basic-block optimiser `optimizeBasicBlocks` -/

section Blocks

open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogOptPipeline
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdReloadElim (reloadElimBody reloadElimBody_sublist)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LcmdCopyPropagate (copyPropagateBody)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogScheduler (scheduleBody scheduleBody_perm)
open CatCrypt.Crypto.Optimizer.LoadCSE (loadCSE)

/-- **The side condition of a modeled run.** The side conditions of `elimReloads`,
    `reloadElimBody` and `loadCSE` on the bodies they read. -/
def optSideB (slotArr : String → Option (String × Nat)) (seg : Lcmd) : Bool :=
  !bodyAllModeled seg ||
    (elimSideB slotArr seg && reloadPairSideB slotArr (elimReloads seg) &&
      loadSideB slotArr
        (copyPropagateBody (scheduleBody (reloadElimBody (elimReloads seg)))))

/-- **`optRunBody` keeps the image class inside a context**, under `optSideB` and when every
    array slot is a frame slot `qsave.R`. -/
theorem physImgB_optRunBody_ctx
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {A b C : Lcmd}
    (h : physImgB slotArr (A ++ b ++ C) = true) (hside : optSideB slotArr b = true) :
    physImgB slotArr (A ++ optRunBody b ++ C) = true := by
  unfold optRunBody
  split
  · rename_i hmod
    simp only [optSideB, hmod, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hside
    obtain ⟨⟨he, hr⟩, hl⟩ := hside
    have h1 := physImgB_elimReloads_ctx h he
    have h2 := physImgB_reloadElimBody_ctx h1 hr
    have h3 := physImgB_scheduleBody_ctx hq h2
    have hm3 : bodyAllModeled (scheduleBody (reloadElimBody (elimReloads b))) = true := by
      refine List.all_eq_true.mpr fun j hj => ?_
      have hj' := (scheduleBody_perm _).subset hj
      exact List.all_eq_true.mp hmod j
        ((elimReloads_sublist b).subset ((reloadElimBody_sublist _).subset hj'))
    have h4 := physImgB_copyPropagateBody_ctx hq h3 hm3
    exact physImgB_loadCSE_ctx h4 hl
  · exact h

/-- The class of a body cut into segments, each rewritten in its context. -/
theorem physImgB_segments_ctx (g : Lcmd → Lcmd) (P : Lcmd → Prop)
    (hg : ∀ (A seg C : Lcmd), P seg → physImgB slotArr (A ++ seg ++ C) = true →
      physImgB slotArr (A ++ g seg ++ C) = true) :
    ∀ (segs : List Lcmd) (A C : Lcmd), (∀ seg ∈ segs, P seg) →
      physImgB slotArr (A ++ segs.flatten ++ C) = true →
      physImgB slotArr (A ++ (segs.map g).flatten ++ C) = true
  | [], _, _, _, h => by simpa using h
  | seg :: rest, A, C, hP, h => by
    have h1 := hg A seg (rest.flatten ++ C) (hP seg (by simp)) (by simpa using h)
    have := physImgB_segments_ctx g P hg rest (A ++ g seg) C (fun s hs => hP s (by simp [hs]))
      (by simpa using h1)
    simpa using this

/-- **The basic-block optimiser keeps the image class.** When every array slot is a frame slot
    `qsave.R` and every run of the segmentation satisfies `optSideB`, `optimizeBasicBlocks`
    keeps `physImgB`. -/
theorem physImgB_optimizeBasicBlocks
    (hq : ∀ q, (slotArr q).isSome = true → hasPrefix q "qsave." = true) {body : Lcmd}
    (h : physImgB slotArr body = true)
    (hside : (splitStraightRuns body).all (optSideB slotArr) = true) :
    physImgB slotArr (optimizeBasicBlocks body) = true := by
  have := physImgB_segments_ctx (slotArr := slotArr)
    (fun seg => if bodyIsStraightLine seg then optRunBody seg else seg)
    (fun seg => optSideB slotArr seg = true)
    (fun A seg C hs hb => by
      split
      · exact physImgB_optRunBody_ctx hq hb hs
      · exact hb)
    (splitStraightRuns body) [] [] (fun s hs => List.all_eq_true.mp hside s hs)
    (by simpa [splitStraightRuns_flatten] using h)
  simpa [optimizeBasicBlocks] using this

end Blocks

end CatCrypt.Crypto.SecureCompilation.X86Backend.PhysImgOpt
