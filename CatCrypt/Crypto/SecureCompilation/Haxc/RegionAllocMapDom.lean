/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapLive

@[expose] public section

set_option autoImplicit false

/-!
# The domain facts of the merge conditions at the allocation certificate

The merge conditions `mergeSep_regionLprogC` hold under hypotheses on the program, on the
layout and on the allocation. This module proves the hypotheses that are facts of the domain
of the region route: they hold for every program that passes `regionExportableB` and has no
`call`.

## Main results

* `nfCtx_length`: the context of the direct route has one variable per parameter.
* `physLiveItems_length_le`: the allocation has at most one live item per name of its body,
  and one more.
* `exportR_symReads`, `exportR_cmpReads`: the export has no symbol-base load, and every
  compare of the export reads its destination.
* `shapeB_regionAllocBody`, `bodyStraightCall_of_shapeB`: the certified body issues no call
  and has no vector operation, so it is no straight-line call body.
* `allocName_not_vec`: under a size bound the allocation names no vector register.
* `namesNE_regionAllocBody`, `empty_not_mem_bodyNames`: the empty name is no name of the
  certified body.
* `regionAllocBody_dom`, `mergeSep_regionLprogC_dom`: the merge conditions at the
  allocation with these hypotheses discharged.
* `layoutOkB`, `layoutOkB_sound`: the layout conditions on the result and parameter registers
  and on the result buffer, as one Boolean check on the layout.
* `hRA_of_regionResultB`: the result register condition from the gate check `regionResultB`.
* `mergeSep_regionLprogC_layout`: the merge conditions at the export names `exportReg` with
  the register conditions discharged by `layoutOkB`.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapDom

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames defNames regDefs)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.TwoAddrLegalize (x86Data
  x86Data_zeroTripGuard x86Data_loopGuard)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment (opMemB)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ToLprogFaithfulRAInterference (LiveAt)
open RegionAllocMapComplete RegionExportDefInit RegionAllocMapAlign RegionAllocMapClose
  RegionAllocMapLive

/-! ## 1. The context of the direct route -/

/-- **The context of the direct route has one variable per parameter of the layout.** -/
theorem nfCtx_length (σ : AbiLayout) : (nfCtx σ).length = σ.args.length := by
  simp [nfCtx, CryptoToJasminCom.mapCtx, Hax.ImpToNF.entryCtx, NFToRoute.abiEntry,
    Hax.NFToCat.abiParamsArr]

/-! ## 2. The live items of the allocation -/

theorem foldl_max_le (b : Nat) :
    ∀ (l : List Nat) (init : Nat), init ≤ b → (∀ x ∈ l, x ≤ b) → l.foldl Nat.max init ≤ b
  | [], _, h, _ => h
  | x :: l, init, h, hl => by
      rw [List.foldl_cons]
      exact foldl_max_le b l _ (Nat.max_le.mpr ⟨h, hl x List.mem_cons_self⟩)
        fun y hy => hl y (List.mem_cons_of_mem _ hy)

/-- **The allocation has at most one live item per name of its body, and one more**: the
    slots of the trace are the ranks `nameSlot` of the names of the body, at most the number
    of the names, and the slot `0` of an instruction without a register destination. -/
theorem physLiveItems_length_le (B : Lcmd) :
    (physLiveItems (bodyTraceOut B [])).length ≤ (bodyNames B).length + 1 := by
  have htr : bodyTraceOut B [] = bodyTrace B := by
    simp [bodyTraceOut, outStoreSlots]
  rw [htr]
  have hu : physUniverse (bodyTrace B) ≤ (bodyNames B).length + 1 := by
    unfold physUniverse
    refine Nat.succ_le_succ (foldl_max_le _ _ _ (Nat.zero_le _) fun x hx => ?_)
    obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
    simp only [bodyTrace, List.mem_map] at he
    obtain ⟨⟨d, s⟩, -, rfl⟩ := he
    have hs : ∀ n, nameSlot B n ≤ (bodyNames B).length := fun n => List.idxOf_le_length
    simp only [PhysEvent.touched, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨n, -, rfl⟩
    · cases d with
      | none => exact Nat.zero_le _
      | some n => exact hs n
    · exact hs n
  simp only [physLiveItems, physLiveData, kernelMergeSort_eq, List.length_mergeSort]
  exact (List.length_filterMap_le _ _).trans (by simpa using hu)

/-! ## 3. The mnemonics of the export -/

/-- A mnemonic of the allocator input that is neither a call shadow nor a vector operation:
    it does not begin with `CALL`, and without its width tag it does not begin with `V`. -/
def MnemB (o : String) : Prop :=
  hasPrefix o "CALL" = false ∧ hasPrefix (stripWidthTag o) "V" = false

/-- The shape of an instruction of the allocator input: it is no call, and the mnemonic of
    an operation satisfies `MnemB`. -/
def ShapeB (w : LinstrR) : Prop :=
  (∀ a b, w ≠ .Lcall a b) ∧ ∀ ds o ss, w = .Lopn ds o ss → MnemB o

/-- The mnemonic facts of an instruction of the export: it is no symbol-base load, a
    compare `cmpArgs?` reads every name it writes, and its shape is `ShapeB`. -/
def MnemDom (i : LinstrRM) : Prop :=
  symReads i = [] ∧ ((JasminLsemMemFlagGuard.cmpArgs? i).isSome = true →
    ∀ x ∈ defNames i.1, x ∈ useNames i.1) ∧ ShapeB i.1

/-- A mnemonic other than `LOADSYM` and the 64-bit `CMP` that satisfies `MnemB`. -/
def MnemOK (o : String) : Prop := o ≠ "LOADSYM" ∧ o ≠ withWidthTag 64 "CMP" ∧ MnemB o

theorem shapeB_lopn {ds : List LOperand} {o : String} {ss : List LOperand} (h : MnemB o) :
    ShapeB (.Lopn ds o ss) := by
  refine ⟨fun _ _ e => ?_, fun _ _ _ e => ?_⟩
  · cases e
  · cases e
    exact h

theorem shapeB_nonLopn {w : LinstrR} (h : ∀ ds o ss, w ≠ .Lopn ds o ss)
    (hc : ∀ a b, w ≠ .Lcall a b) : ShapeB w :=
  ⟨hc, fun _ _ _ e => absurd e (h _ _ _)⟩

theorem mnemDom_lopn {ds : List LOperand} {o : String} {ss : List LOperand} {t : MemTag}
    (h : MnemOK o) : MnemDom (.Lopn ds o ss, t) := by
  refine ⟨by simp [symReads, h.1], fun hc => ?_, shapeB_lopn h.2.2⟩
  exfalso
  simp only [JasminLsemMemFlagGuard.cmpArgs?] at hc
  split at hc
  · rename_i heq
    simp only [LinstrR.Lopn.injEq] at heq
    obtain ⟨-, rfl, -⟩ := heq
    simp [h.2.1] at hc
  · simp at hc

theorem mnemDom_nonLopn {i : LinstrRM} (h : ∀ ds o ss, i.1 ≠ .Lopn ds o ss)
    (hl : ∀ a b, i.1 ≠ .Lcall a b) : MnemDom i := by
  refine ⟨?_, fun hc => ?_, shapeB_nonLopn h hl⟩
  · unfold symReads
    split
    · rename_i heq; exact absurd heq (h _ _ _)
    · rfl
  · exfalso
    simp only [JasminLsemMemFlagGuard.cmpArgs?] at hc
    split at hc
    · rename_i heq; exact h _ _ _ heq
    · simp at hc

theorem mnemOK_withWidthTag {w : Nat} {m : String}
    (h1 : w ≠ 64 → m ++ "^" ++ toString w ≠ "LOADSYM" ∧ m ++ "^" ++ toString w ≠ "CMP:64" ∧
      MnemB (m ++ "^" ++ toString w))
    (h2 : m ++ ":64" ≠ "LOADSYM" ∧ m ++ ":64" ≠ "CMP:64" ∧ MnemB (m ++ ":64")) :
    MnemOK (withWidthTag w m) := by
  have hc : withWidthTag 64 "CMP" = "CMP:64" := by decide
  unfold MnemOK
  rw [hc]
  unfold withWidthTag
  split
  · exact h2
  · rename_i hw
    exact h1 hw

/-- A character list that begins with `CALL` after a body, with a tail beginning with
    `:` or `^`, has the body begin with `CALL`. -/
theorem call_prefix_of_append {l T : List Char} (hT : T.head? = some ':' ∨ T.head? = some '^')
    (h : ['C', 'A', 'L', 'L'] <+: l ++ T) : ['C', 'A', 'L', 'L'] <+: l := by
  obtain ⟨u, hu⟩ := h
  rcases T with _ | ⟨t, T⟩
  · simp at hT
  simp only [List.head?_cons, Option.some.injEq] at hT
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, r⟩⟩⟩⟩ <;>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at hu
  all_goals grind

/-- A tagged mnemonic begins with `CALL` only if its body does. -/
theorem hasPrefix_withWidthTag_CALL (w : Nat) {m : String} (h : hasPrefix m "CALL" = false) :
    hasPrefix (withWidthTag w m) "CALL" = false := by
  have hC : "CALL".toList = ['C', 'A', 'L', 'L'] := by decide
  unfold hasPrefix at h ⊢
  rw [hC] at h ⊢
  rw [Bool.eq_false_iff] at h ⊢
  intro hp
  apply h
  rw [List.isPrefixOf_iff_prefix] at hp ⊢
  by_cases hw : w = 64
  · subst hw
    rw [toList_withWidthTag_64] at hp
    exact call_prefix_of_append (by simp) hp
  · rw [toList_withWidthTag_of_ne hw] at hp
    exact call_prefix_of_append (by simp) hp

/-- A mnemonic body without a width-tag separator, other than `CMP`, beginning neither
    with `CALL` nor with `V`, gives a tagged mnemonic satisfying `MnemOK` at every width. -/
theorem mnemOK_withWidthTag_of_tagSepFree {w : Nat} {m : String} (hm : tagSepFree m = true)
    (hcmp : m ≠ "CMP") (hC : hasPrefix m "CALL" = false) (hV : hasPrefix m "V" = false) :
    MnemOK (withWidthTag w m) := by
  refine ⟨withWidthTag_ne_of_tagSepFree _ _ (by decide +kernel), fun e => hcmp ?_,
    hasPrefix_withWidthTag_CALL w hC, ?_⟩
  · have := congrArg stripWidthTag e
    rwa [stripWidthTag_withWidthTag _ hm,
      stripWidthTag_withWidthTag _ (by decide +kernel : tagSepFree "CMP" = true)] at this
  · rw [stripWidthTag_withWidthTag _ hm]
    exact hV

theorem mnemDom_movI (dst : String) (src : LOperand) : MnemDom (movI dst src) :=
  mnemDom_lopn (by unfold MnemOK MnemB withWidthTag; decide)

theorem mnemDom_labelI (l : LLabel) : MnemDom (labelI l) :=
  mnemDom_nonLopn (fun _ _ _ e => by cases e) (fun _ _ e => by cases e)

theorem mnemDom_cmpGuard (c : String) :
    MnemDom (guardI (.Lopn [.reg c] (withWidthTag 64 "CMP") [.reg c, .imm 0])) := by
  refine ⟨by simp [symReads, guardI, withWidthTag], fun _ x hx => ?_,
    shapeB_lopn (by unfold MnemB withWidthTag; decide)⟩
  simpa [guardI, defNames, useNames, JasminLsemExportRewrites.opNames] using hx

theorem mnemDom_x86Guards :
    (∀ c t e, ∀ i ∈ (x86Data.zeroTripGuard c t e).map guardI, MnemDom i) ∧
      ∀ c t, ∀ i ∈ (x86Data.loopGuard c t).map guardI, MnemDom i := by
  constructor
  · intro c t e i hi
    rw [x86Data_zeroTripGuard] at hi
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact mnemDom_cmpGuard c
    · exact mnemDom_nonLopn (fun _ _ _ e => by cases e) (fun _ _ e => by cases e)
  · intro c t i hi
    rw [x86Data_loopGuard] at hi
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact mnemDom_cmpGuard c
    · exact mnemDom_nonLopn (fun _ _ _ e => by cases e) (fun _ _ e => by cases e)

theorem mnemDom_seedMoves (car : List String) (ops : List LOperand) :
    ∀ i ∈ seedMoves car ops, MnemDom i := by
  intro i hi
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
  exact mnemDom_movI _ _

theorem mnemDom_parMoves (D : Nat) (tgts : List String) (ops : List LOperand) :
    ∀ i ∈ parMoves D tgts ops, MnemDom i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi <;> obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi <;>
    exact mnemDom_movI _ _

theorem mnemDom_arrMoves (z t : String) (mv : List ArrMove) :
    ∀ i ∈ arrMoves z t mv, MnemDom i := by
  intro i hi
  obtain ⟨a, -, hi⟩ := List.mem_flatMap.mp hi
  simp only [arrMove, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact mnemDom_lopn (by unfold MnemOK MnemB withWidthTag; decide)

theorem mnemDom_typedMoves (z t : String) (tp : List (JasminTy × String × String)) :
    ∀ i ∈ typedMoves z t tp, MnemDom i := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact mnemDom_arrMoves _ _ _ i hi
  · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hi
    exact mnemDom_movI _ _

theorem mnemDom_arrParMoves (z t : String) (D : Nat) (mv : List ArrMove) :
    ∀ i ∈ arrParMoves z t D mv, MnemDom i := by
  intro i hi
  unfold arrParMoves at hi
  split at hi
  · exact mnemDom_arrMoves _ _ _ i hi
  · rcases List.mem_append.mp hi with hi | hi <;> exact mnemDom_arrMoves _ _ _ i hi

theorem mnemDom_advanceOps (idx ctr : String) : ∀ i ∈ advanceOps idx ctr, MnemDom i := by
  intro i hi
  simp only [advanceOps, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> exact mnemDom_lopn (by unfold MnemOK MnemB withWidthTag; decide)

theorem mnemDom_flagWord (r z : String) (op : LOperand) :
    ∀ i ∈ flagWord x86Data r z op, MnemDom i := by
  intro i hi
  unfold flagWord at hi
  split at hi
  · rw [show x86Data.selectMnemonic = some "CMOV" from rfl] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact mnemDom_movI _ _
    · exact mnemDom_movI _ _
    · exact mnemDom_lopn (by unfold MnemOK MnemB withWidthTag; decide)
  · rw [List.mem_singleton.mp hi]
    exact mnemDom_movI _ _

theorem mnemDom_ifResMoves (rs : List JasminTy) (d D : Nat) (ops : List LOperand) :
    ∀ i ∈ ifResMoves rs d D ops, MnemDom i := by
  intro i hi
  unfold ifResMoves at hi
  rcases List.mem_append.mp hi with hi | hi
  · split at hi
    · cases hi
    · rcases List.mem_cons.mp hi with rfl | hi
      · exact mnemDom_movI _ _
      · exact mnemDom_arrParMoves _ _ _ _ i hi
  · exact mnemDom_parMoves _ _ _ i hi

theorem dropLast3_cons (c : Char) (l : List Char) (hl : 3 ≤ l.length) :
    (c :: l).dropLast.dropLast.dropLast = c :: l.dropLast.dropLast.dropLast := by
  have h1 : l ≠ [] := List.ne_nil_of_length_pos (by omega)
  have h2 : l.dropLast ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
  have h3 : l.dropLast.dropLast ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
  rw [List.dropLast_cons_of_ne_nil h1, List.dropLast_cons_of_ne_nil h2,
    List.dropLast_cons_of_ne_nil h3]

/-- A mnemonic of at least four characters whose first character is neither `C` nor `V`
    satisfies `MnemB`. -/
theorem mnemB_of_head {x : String} {c : Char} {v : List Char} (hx : x.toList = c :: v)
    (hv : 3 ≤ v.length) (hc : c ≠ 'C' ∧ c ≠ 'V') : MnemB x := by
  refine ⟨?_, ?_⟩
  · rw [hasPrefix, hx, show "CALL".toList = ['C', 'A', 'L', 'L'] from by decide]
    simp [List.isPrefixOf, Ne.symm hc.1]
  · have hV : "V".toList = ['V'] := by decide
    unfold stripWidthTag
    split
    · simp only [hasPrefix, String.toList_ofList, hx, hV, List.takeWhile_cons]
      split <;> simp [List.isPrefixOf, Ne.symm hc.2]
    split
    · simp only [hasPrefix, String.toList_ofList, hx, dropLast3_cons c v hv, hV]
      simp [List.isPrefixOf, Ne.symm hc.2]
    · simp only [hasPrefix, hx, hV]
      simp [List.isPrefixOf, Ne.symm hc.2]

theorem mnemOK_shift (s : String) (c : Char) (u : List Char) (hs : s.toList = c :: u)
    (hu : 3 ≤ u.length) (hc : c ≠ 'L' ∧ c ≠ 'C' ∧ c ≠ 'V') (w n : Nat) :
    MnemOK (withWidthTag w (s ++ toString n)) := by
  have key : ∀ x : String, (∃ v, x.toList = c :: v ∧ 3 ≤ v.length) →
      x ≠ "LOADSYM" ∧ x ≠ "CMP:64" ∧ MnemB x := by
    rintro x ⟨v, hv, hl⟩
    refine ⟨fun e => hc.1 ?_, fun e => hc.2.1 ?_, mnemB_of_head hv hl hc.2⟩ <;> subst e
    · simpa using (List.cons.inj (hv.symm.trans
        (by decide : "LOADSYM".toList = 'L' :: "OADSYM".toList))).1
    · simpa using (List.cons.inj (hv.symm.trans
        (by decide : "CMP:64".toList = 'C' :: "MP:64".toList))).1
  refine mnemOK_withWidthTag
    (fun _ => key _ ⟨u ++ (toString n).toList ++ '^' :: (toString w).toList, ?_,
      by simp; omega⟩)
    (key _ ⟨u ++ (toString n).toList ++ ":64".toList, ?_, by simp; omega⟩)
  · simp [hs]
  · rw [String.toList_append, String.toList_append, hs]; rfl

/-- **An operation of the stack-memory fragment exports with a mnemonic other than
    `LOADSYM` and the 64-bit `CMP`.** -/
theorem mnemOK_opToLinstrR {op : JasminOp} (hop : opMemB op = true) (dst : String)
    (srcs : List LOperand) : ∃ ds o ss, opToLinstrR op dst srcs = .Lopn ds o ss ∧ MnemOK o := by
  cases op <;> simp only [opMemB, Bool.false_eq_true] at hop <;> simp only [opToLinstrR]
  all_goals (try split) <;> (try split) <;> refine ⟨_, _, _, rfl, ?_⟩
  all_goals first
    | (unfold MnemOK MnemB withWidthTag; split <;> decide)
    | exact mnemOK_withWidthTag_of_tagSepFree (by decide +kernel) (by decide)
        (by decide +kernel) (by decide +kernel)
    | (rename_i b _; cases b <;> exact mnemOK_withWidthTag_of_tagSepFree (by decide +kernel)
        (by decide) (by decide +kernel) (by decide +kernel))
    | (rename_i c _ _; cases c <;> exact mnemOK_withWidthTag_of_tagSepFree (by decide +kernel)
        (by decide) (by decide +kernel) (by decide +kernel))
    | exact mnemOK_shift _ 'S' _ rfl (by decide) (by decide) _ _
    | exact mnemOK_shift _ 'R' _ rfl (by decide) (by decide) _ _
    | (unfold MnemOK MnemB castWMnem; repeat' split
       all_goals decide)

theorem mnemDom_bindOps (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (hop : opMemB e.op = true) (d : Nat) :
    ∀ i ∈ bindOps nArgs e d, MnemDom i := by
  have hO : ∀ (dst : String) (srcs : List LOperand) (tag : MemTag),
      MnemDom (opToLinstrR e.op dst srcs, tag) := by
    intro dst srcs tag
    obtain ⟨ds, o, ss, he, ho⟩ := mnemOK_opToLinstrR hop dst srcs
    rw [he]
    exact mnemDom_lopn ho
  intro i hi
  simp only [bindOps, straightOpsMem, List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  split <;> try exact hO _ _ _
  split
  all_goals first
    | exact hO _ _ _
    | exact mnemDom_lopn (mnemOK_withWidthTag_of_tagSepFree (by decide +kernel) (by decide)
        (by decide +kernel) (by decide +kernel))

theorem forArrFrame_mnemDom (d n : Nat) (cs : List JasminTy) (initOps : List LOperand)
    (countOp : LOperand) (bodyC : List LinstrRM) (bodyOps : List LOperand) (bodyD : Nat)
    (hb : ∀ i ∈ bodyC, MnemDom i) :
    ∀ i ∈ forArrFrame d n cs initOps countOp bodyC bodyOps bodyD x86Data, MnemDom i := by
  intro i hi
  simp only [forArrFrame, List.mem_append, List.mem_cons] at hi
  rcases hi with rfl | hi | hi | hi | rfl | hi | rfl | hi | hi | hi | hi | rfl | rfl | hi
  · exact mnemDom_movI _ _
  · exact mnemDom_typedMoves _ _ _ i hi
  · exact mnemDom_seedMoves _ _ i hi
  · exact mnemDom_x86Guards.1 _ n _ i hi
  · exact mnemDom_labelI _
  · exact hb i hi
  · exact mnemDom_movI _ _
  · exact mnemDom_arrParMoves _ _ _ _ i hi
  · exact mnemDom_parMoves _ _ _ i hi
  · exact mnemDom_advanceOps _ _ i hi
  · exact mnemDom_x86Guards.2 _ _ i hi
  · exact mnemDom_labelI _
  · exact mnemDom_movI _ _
  · exact mnemDom_typedMoves _ _ _ i hi

theorem whileFrame_mnemDom (d n nCar : Nat) (initOps : List LOperand) (bodyC : List LinstrRM)
    (flagOp : LOperand) (bodyOps : List LOperand) (bodyD : Nat) (hb : ∀ i ∈ bodyC, MnemDom i) :
    ∀ i ∈ whileFrame d n nCar initOps bodyC flagOp bodyOps bodyD x86Data, MnemDom i := by
  intro i hi
  simp only [whileFrame, List.mem_append, List.mem_cons] at hi
  rcases hi with hi | rfl | hi | hi | hi | hi
  · exact mnemDom_seedMoves _ _ i hi
  · exact mnemDom_labelI _
  · exact hb i hi
  · exact mnemDom_flagWord _ _ _ i hi
  · exact mnemDom_parMoves _ _ _ i hi
  · exact mnemDom_x86Guards.2 _ _ i hi

theorem ifFrame_mnemDom (fn : String) (d n : Nat) (rs : List JasminTy) (condOp : LOperand)
    (thnC : List LinstrRM) (thnOps : List LOperand) (thnD : Nat) (elsC : List LinstrRM)
    (elsOps : List LOperand) (elsD : Nat) (ht : ∀ i ∈ thnC, MnemDom i)
    (he : ∀ i ∈ elsC, MnemDom i) :
    ∀ i ∈ ifFrame fn d n rs condOp thnC thnOps thnD elsC elsOps elsD x86Data, MnemDom i := by
  intro i hi
  simp only [ifFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with hi | hi | rfl | hi | hi | rfl | hi | rfl | hi | hi | rfl
  · exact mnemDom_flagWord _ _ _ i hi
  · exact mnemDom_x86Guards.1 _ n _ i hi
  · exact mnemDom_labelI _
  · exact ht i hi
  · exact mnemDom_ifResMoves _ _ _ _ i hi
  · exact mnemDom_movI _ _
  · exact mnemDom_x86Guards.2 _ _ i hi
  · exact mnemDom_labelI _
  · exact he i hi
  · exact mnemDom_ifResMoves _ _ _ _ i hi
  · exact mnemDom_labelI _

/-- **The mnemonic facts of the export**: every instruction of the export on x86 of a program
    without `call` that passes `regionExportableB` has `MnemDom`. -/
theorem exportR_mnemDom (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) :
    ∀ (d n : Nat) (r : Exported), exportR nArgs fn p d n x86Data = some r →
      ∀ i ∈ r.code, MnemDom i := by
  induction p with
  | ret vs =>
      intro d n r h i hi
      simp only [exportR, Option.some.injEq] at h
      subst h
      cases hi
  | var e k ih =>
      simp only [regionExportableB, Bool.and_eq_true] at hp
      simp only [NFProg.callFree] at hc
      intro d n r h i hi
      simp only [exportR, Option.map_eq_some_iff] at h
      obtain ⟨rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact mnemDom_bindOps nArgs e hp.1 d i hi
      · exact ih hp.2 hc _ _ _ hk i hi
  | forLoop count inits body k ihb ihk =>
      simp only [regionExportableB, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact forArrFrame_mnemDom _ _ _ _ _ _ _ _ (ihb hp.1 hc.1 _ _ _ hb) i hi
      · exact ihk hp.2 hc.2 _ _ _ hk i hi
  | ifThenElse cond thn els k iht ihe ihk =>
      simp only [regionExportableB, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨t, ht, e, he, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact ifFrame_mnemDom _ _ _ _ _ _ _ _ _ _ _ (iht hp.1.1 hc.1.1 _ _ _ ht)
          (ihe hp.1.2 hc.1.2 _ _ _ he) i hi
      · exact ihk hp.2 hc.2 _ _ _ hk i hi
  | whileLoop inits body k ihb ihk =>
      simp only [regionExportableB, Bool.and_eq_true] at hp
      simp only [NFProg.callFree, Bool.and_eq_true] at hc
      intro d n r h i hi
      simp only [exportR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨b, hb, rk, hk, rfl⟩ := h
      rcases List.mem_append.mp hi with hi | hi
      · exact whileFrame_mnemDom _ _ _ _ _ _ _ _ (ihb hp.1.2 hc.1 _ _ _ hb) i hi
      · exact ihk hp.2 hc.2 _ _ _ hk i hi
  | call f args k ih =>
      simp [NFProg.callFree] at hc

/-- **The export has no symbol-base load** (the hypothesis `hsym` of
    `entry_regionLprogC`): `LOADSYM` comes only from a reserved `extCall`, which
    `regionExportableB` excludes. -/
theorem exportR_symReads (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {d n : Nat} {r : Exported}
    (h : exportR nArgs fn p d n x86Data = some r) : ∀ i ∈ r.code, symReads i = [] :=
  fun i hi => (exportR_mnemDom nArgs fn p hp hc d n r h i hi).1

/-- **Every compare of the export reads its destination** (the hypothesis `hcmp` of
    `entry_regionLprogC`): the 64-bit `CMP` of the export are the guards
    `CMP:64 [r] [r, #0]`, and a comparison of the source exports as `SETcc`. -/
theorem exportR_cmpReads (nArgs : Nat) (fn : String) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hc : p.callFree = true) {d n : Nat} {r : Exported}
    (h : exportR nArgs fn p d n x86Data = some r) :
    ∀ i ∈ r.code, (JasminLsemMemFlagGuard.cmpArgs? i).isSome = true →
      ∀ x ∈ defNames i.1, x ∈ useNames i.1 :=
  fun i hi => (exportR_mnemDom nArgs fn p hp hc d n r h i hi).2.1

/-! ## 4. The shape of the allocator input -/

theorem hasPrefix_false_of_append {o p : String} (s : String) (h : hasPrefix o p = false) :
    hasPrefix o (p ++ s) = false := by
  unfold hasPrefix at h ⊢
  rw [Bool.eq_false_iff] at h ⊢
  intro h'
  apply h
  rw [List.isPrefixOf_iff_prefix] at h' ⊢
  rw [String.toList_append] at h'
  exact (List.prefix_append _ _).trans h'

theorem shadowCall?_of_mnemB {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : MnemB o) : LprogIsa.shadowCall? (.Lopn ds o ss) = none := by
  have h5 : "CALL:".toList.isPrefixOf o.toList = false :=
    hasPrefix_false_of_append ":" h.1
  unfold LprogIsa.shadowCall?
  split
  · rename_i heq
    simp only [LinstrR.Lopn.injEq] at heq
    obtain ⟨-, rfl, -⟩ := heq
    rw [ite_eq_right (by rw [h5]; exact Bool.false_ne_true)]
  · rfl

/-- The renaming of the array positions keeps the shape of an instruction. -/
theorem shapeB_renArr (σ : String → String) {i : LinstrRM} (h : ShapeB i.1) :
    ShapeB (X86Backend.ImageCoalesceCfg.renArr σ i).1 := by
  obtain ⟨w, t⟩ := i
  cases w with
  | Lopn ds o ss =>
      have ho : MnemB o := h.2 ds o ss rfl
      unfold X86Backend.ImageCoalesceCfg.renArr
      split
      all_goals first
        | (simp only [X86Backend.ImageCoalesceCfg.renCallW, shadowCall?_of_mnemB ho]; exact h)
        | (simp only [X86Backend.ImageCoalesceCfg.renLoad, X86Backend.ImageCoalesceCfg.renStore,
             X86Backend.ImageCoalesceCfg.renZero, X86Backend.ImageCoalesceCfg.renStoreImm]
           repeat' split
           all_goals first
             | exact shapeB_lopn ho
             | (rename_i heq _
                simp only [LinstrR.Lopn.injEq] at heq
                obtain ⟨-, rfl, -⟩ := heq
                exact shapeB_lopn ho))
  | _ =>
      unfold X86Backend.ImageCoalesceCfg.renArr
      split <;> exact h

theorem mnemB_livepin : MnemB "LIVEPIN" := by unfold MnemB; decide

theorem shapeB_backEdgePins {C : List LinstrRM} (h : ∀ i ∈ C, ShapeB i.1) :
    ∀ i ∈ backEdgePins C, ShapeB i.1 := by
  have hpin : ∀ T k l, ∀ i ∈ backEdgePin T C k l, ShapeB i.1 := by
    intro T k l i hi
    unfold backEdgePin at hi
    dsimp only at hi
    split at hi
    · split at hi
      · rw [List.mem_singleton.mp hi]
        exact shapeB_lopn mnemB_livepin
      · cases hi
    · cases hi
  intro i hi
  obtain ⟨⟨j, k⟩, hjk, hi⟩ := List.mem_flatMap.mp hi
  have hj : j ∈ C := List.fst_mem_of_mem_zipIdx hjk
  dsimp only at hi
  split at hi
  all_goals first
    | (rw [List.mem_singleton.mp hi]; exact h j hj)
    | (rcases List.mem_append.mp hi with hi | hi
       · exact hpin _ _ _ i hi
       · rw [List.mem_singleton.mp hi]; exact h j hj)

theorem shapeB_resCopyCode (src D : String) (m : Nat) :
    ∀ i ∈ resCopyCode src D m, ShapeB i.1 := by
  intro i hi
  obtain ⟨j, -, hi⟩ := List.mem_flatMap.mp hi
  simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact shapeB_lopn (by unfold MnemB withWidthTag; decide)
  · exact shapeB_lopn (by unfold MnemB; decide)
  · exact shapeB_lopn (by unfold MnemB; decide)

theorem shapeB_regionLprogCopy (a : AbiNames) (ts : List JasminTy) (code : List LinstrRM)
    (res : List LOperand) : ∀ i ∈ regionLprogCopy a none ts code res, ShapeB i.1 := by
  intro i hi
  unfold regionLprogCopy at hi
  split at hi
  · split at hi
    · exact shapeB_resCopyCode _ _ _ i hi
    · cases hi
  · cases hi

/-- **The code given to the allocation has the shape `ShapeB`** when the code it is made of
    has it. -/
theorem shapeB_regionAllocCode {C : List LinstrRM} {rr : Option (String × String)}
    (h : ∀ i ∈ C, ShapeB i.1) : ∀ i ∈ regionAllocCode C [] rr, ShapeB i.1 := by
  refine shapeB_backEdgePins fun i hi => ?_
  rcases mem_pinSelfMoves hi with hi | ⟨t, a, z, sc, w, n, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    exact shapeB_renArr _ (h j hj)
  · exact shapeB_lopn mnemB_livepin
  · exact shapeB_lopn mnemB_livepin

theorem expandCallShadows_of_shapeB {body : Lcmd} (h : ∀ i ∈ body, ShapeB i.li_i)
    (outs : List String) : expandCallShadows body outs = body := by
  unfold expandCallShadows
  refine (List.flatMap_congr fun i hi => ?_).trans (List.flatMap_singleton' body)
  dsimp only
  split
  · rename_i dst opn argOps heq
    have ho : MnemB opn := (h i hi).2 _ _ _ heq
    have h1 : hasPrefix opn "CALLN:" = false := hasPrefix_false_of_append "N:" ho.1
    have h2 : hasPrefix opn "CALL:" = false := hasPrefix_false_of_append ":" ho.1
    have h3 : parseCallW opn = none := by
      unfold parseCallW
      rw [show "CALLNW:" = "CALL" ++ "NW:" from by decide,
        show "CALLW:" = "CALL" ++ "W:" from by decide,
        hasPrefix_false_of_append _ ho.1, hasPrefix_false_of_append _ ho.1]
      rfl
    rw [h3]
    simp [h1, h2]
  · rfl

theorem shapeB_canonicalizeMemrefThread {body : Lcmd} (h : ∀ i ∈ body, ShapeB i.li_i) :
    ∀ i ∈ canonicalizeMemrefThread body, ShapeB i.li_i := by
  intro i hi
  unfold canonicalizeMemrefThread at hi
  dsimp only at hi
  split at hi
  · exact h i hi
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    split
    · rename_i ds o ss heq
      exact shapeB_lopn ((h j hj).2 ds o ss heq)
    · exact h j hj

theorem shapeB_livepin (ss : List LOperand) (ii : Nat) :
    ShapeB (⟨ii, .Lopn [.reg "%livepin"] "LIVEPIN" ss⟩ : Linstr).li_i :=
  shapeB_lopn mnemB_livepin

/-- **The body the allocation certifies has the shape `ShapeB`** when the export has it. -/
theorem shapeB_regionAllocBody (a : AbiNames) (nArgs : Nat) (ts : List JasminTy)
    (r : Exported) (hr : ∀ i ∈ r.code, ShapeB i.1) :
    ∀ i ∈ regionAllocBody a nArgs ts r, ShapeB i.li_i := by
  have hac : ∀ i ∈ regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res) []
      (resAliasOf none (some a.outArg) ts r.res), ShapeB i.1 := by
    refine shapeB_regionAllocCode fun i hi => ?_
    rcases List.mem_append.mp hi with hi | hi
    · exact hr i hi
    · exact shapeB_regionLprogCopy a ts r.code r.res i hi
  have hbody : ∀ i ∈ (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res)
      [] (resAliasOf none (some a.outArg) ts r.res)).map (fun i => (⟨0, i.1⟩ : Linstr))
        ++ [⟨0, .Lret⟩], ShapeB i.li_i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact hac j hj
    · rw [List.mem_singleton.mp hi]
      exact shapeB_nonLopn (fun _ _ _ e => by cases e) (fun _ _ e => by cases e)
  intro i hi
  unfold regionAllocBody at hi
  split at hi
  · rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · rw [List.mem_singleton.mp hi]; exact shapeB_livepin _ _
      · rw [expandCallShadows_of_shapeB hbody] at hi
        exact shapeB_canonicalizeMemrefThread hbody i hi
    · unfold resLivePin at hi
      split at hi
      · split at hi
        · rw [List.mem_singleton.mp hi]; exact shapeB_livepin _ _
        · cases hi
      · cases hi
  · rcases List.mem_append.mp hi with hi | hi
    · split at hi
      · rw [List.mem_singleton.mp hi]; exact shapeB_livepin _ _
      · cases hi
    · refine shapeB_canonicalizeMemrefThread (fun j hj => ?_) i hi
      rcases List.mem_append.mp hj with hj | hj
      · unfold arrBasePins at hj
        dsimp only at hj
        split at hj
        · cases hj
        · rw [List.mem_singleton.mp hj]; exact shapeB_livepin _ _
      · exact hbody j hj

/-- A body of instructions of the shape `ShapeB` issues no call. -/
theorem bodyHasCall_of_shapeB {B : Lcmd} (h : ∀ i ∈ B, ShapeB i.li_i) : bodyHasCall B = false := by
  rw [bodyHasCall, List.any_eq_false]
  intro i hi
  split
  · rename_i a b heq; exact absurd heq ((h i hi).1 a b)
  · exact Bool.false_ne_true

/-- **A body of instructions of the shape `ShapeB` is no straight-line call body.** -/
theorem bodyStraightCall_of_shapeB {B : Lcmd} (h : ∀ i ∈ B, ShapeB i.li_i) :
    bodyStraightCall B = false := by
  rw [bodyStraightCall, bodyHasCall_of_shapeB h, Bool.false_and]

/-- A body of instructions of the shape `ShapeB` classifies every slot general-purpose. -/
theorem bodyVecSlots_of_shapeB {B : Lcmd} (h : ∀ i ∈ B, ShapeB i.li_i) :
    bodyVecSlots B = Array.replicate ((bodyNames B).length + 1) false := by
  refine X86Backend.PhysAbiShape.bodyVecSlots_noVec B (List.all_eq_true.mpr fun i hi => ?_)
  split
  · rename_i ds o ss heq
    rw [((h i hi).2 ds o ss heq).2]
    rfl
  · rfl

/-! ## 5. The allocation names no vector register -/

/-- A physical index below `vectorBase` names no vector register: it names a register of the
    allocation pool or a spill `k.N`. -/
theorem physRegName_not_vec {p : Nat} (hp : p < vectorBase) : physRegName p ∉ vectorRegNames := by
  have hX : ∀ x ∈ vectorRegNames, x.toList.head? = some 'X' := by decide
  unfold physRegName
  rw [ite_eq_right (by omega)]
  split
  · rename_i r hr
    have hm : r ∈ gpRegNames := List.mem_of_getElem? hr
    revert hm
    generalize r = r
    intro hm
    have hg : ∀ x ∈ gpRegNames, x ∉ vectorRegNames := by decide
    exact hg r hm
  · intro hm
    have := hX _ hm
    rw [String.toList_append, show "k.".toList = ['k', '.'] from by decide] at this
    simp at this

/-- **The table of the allocation stays below `vectorBase`** at every slot of a name of the
    body, for a body of the shape `ShapeB` whose names leave room for one stack cell each: the
    general-purpose scan places a live slot below `vectorBase` (`gpHalf_lt_vectorBase`), the
    vector scan has no item, and every other slot keeps its own index. -/
theorem physMapTabled_regionAllocTbl_lt {B : Lcmd} (hB : ∀ i ∈ B, ShapeB i.li_i)
    (hsize : numGPRegs + (bodyNames B).length + 1 ≤ vectorBase) {s : Nat}
    (hs : s ≤ (bodyNames B).length) : physMapTabled (regionAllocTbl B) s < vectorBase := by
  have hfit : numGPRegs + (physLiveItems (bodyTraceOut B [])).length ≤ vectorBase := by
    have := physLiveItems_length_le B
    omega
  have hvec : bodyVecSlots B = Array.replicate ((bodyNames B).length + 1) false :=
    bodyVecSlots_of_shapeB hB
  have hvh : X86Backend.ToLprogFaithfulRAInterference.vecHalf (bodyTraceOut B []) (bodyVecSlots B) [] = [] := by
    rw [hvec]
    unfold X86Backend.ToLprogFaithfulRAInterference.vecHalf
    rw [List.filter_eq_nil_iff.mpr (fun it _ => by
      simp only [slotIsVec, Array.getElem?_replicate]
      split <;> simp)]
    rfl
  unfold regionAllocTbl straightCallComposeTable
  rw [bodyStraightCall_of_shapeB hB, ite_eq_right Bool.false_ne_true, physTableOut,
    X86Backend.PhysAbiShape.physTableClassed_eq]
  unfold physMapTabled
  rw [List.getElem?_toArray]
  by_cases hu : s < physUniverse (bodyTraceOut B [])
  · rw [List.getElem?_map, List.getElem?_range hu, Option.map_some, Option.getD_some]
    split
    · rename_i q ph hq
      have hm := List.mem_of_find?_eq_some hq
      rw [X86Backend.ToLprogFaithfulRAInterference.physAssignClassed_eq, hvh, List.map_nil,
        List.append_nil] at hm
      exact X86Backend.ToLprogFaithfulRAInterference.gpHalf_lt_vectorBase hfit _ hm
    · omega
  · rw [List.getElem?_eq_none (by simpa using hu)]
    simp only [Option.getD_none]
    omega

/-- **The allocation names no vector register** (the hypothesis `hvec` of
    `entry_regionLprogC`, for every name): on a body of the shape `ShapeB`, without a call,
    the allocation renders the table entry of the slot of a name, which is below `vectorBase`
    under the size bound, as a general-purpose register or a spill. -/
theorem allocName_not_vec {B : Lcmd} (hB : ∀ i ∈ B, ShapeB i.li_i)
    (hsize : numGPRegs + (bodyNames B).length + 1 ≤ vectorBase) (n : String) :
    allocName B (regionAllocTbl B) n ∉ vectorRegNames := by
  unfold allocName
  rw [bodyHasCall_of_shapeB hB, ite_eq_right Bool.false_ne_true]
  exact physRegName_not_vec (physMapTabled_regionAllocTbl_lt hB hsize List.idxOf_le_length)

/-! ## 6. The names of the allocator input are not empty -/

open JasminLsemExportRewrites (instrNames opNames)

/-- Every register name an instruction mentions is not the empty name. -/
def NamesNE (w : LinstrR) : Prop := ∀ x ∈ instrNames w, x ≠ ""

theorem argName_ne_empty (j : Nat) : argName j ≠ "" := by
  intro h
  have := congrArg String.length h
  simp [argName] at this

theorem namesNE_lopn {ds : List LOperand} {o : String} {ss : List LOperand}
    (h : ∀ x ∈ ds.flatMap opNames ++ ss.flatMap opNames, x ≠ "") :
    NamesNE (.Lopn ds o ss) := by
  intro x hx
  simp only [instrNames, List.flatMap_append] at hx
  exact h x hx

/-- **The names of a body are names its instructions mention.** -/
theorem mem_instrNames_of_mem_bodyNames {B : Lcmd} {x : String} (hx : x ∈ bodyNames B) :
    ∃ i ∈ B, x ∈ instrNames i.li_i := by
  rw [bodyNames, List.mem_eraseDups] at hx
  obtain ⟨⟨d, s⟩, hds, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨i, hi, he⟩ := List.mem_filterMap.mp hds
  refine ⟨i, hi, ?_⟩
  revert he
  unfold linstrRegNames
  split
  · rename_i dsts opn srcs heq
    rw [heq]
    intro he
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [instrNames, List.flatMap_append, List.mem_append]
    rcases List.mem_append.mp hx with hx | hx
    · left
      cases dsts with
      | nil => simp at hx
      | cons o os =>
          simp only [List.head?_cons, Option.bind_some] at hx
          cases o <;> simp_all [LOperand.regName?, opNames]
    · right
      obtain ⟨o, ho, hx⟩ := List.mem_flatMap.mp hx
      refine List.mem_flatMap.mpr ⟨o, ho, ?_⟩
      cases o <;> simp_all [LOperand.srcRegNames, opNames]
  · intro he; cases he

/-- **The names of the export are not empty**: a name an instruction of the export writes is
    an export register name, and a name it reads is written on every path to it or is an
    argument name, since the export has no symbol-base load. -/
theorem exportR_namesNE (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true) (hc : p.callFree = true)
    {r : Exported} (h : exportR Γ.length fn p Γ.length 0 x86Data = some r) :
    ∀ i ∈ r.code, NamesNE i.1 := by
  obtain ⟨D, hC, -⟩ := exportR_cert fn p h
  have hreach := (exportR_fwdReach Γ.length fn p h).1
  have hdef := exportR_defNames Γ.length fn p _ _ r h
  have hsym := exportR_symReads Γ.length fn p hp hc h
  intro i hi x hx
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hi
  have hkl : k < r.code.length := (List.getElem?_eq_some_iff.mp hk).1
  cases hw : i.1 with
  | Lopn ds o ss =>
      rw [hw] at hx
      simp only [instrNames, List.flatMap_append, List.mem_append] at hx
      rcases hx with hx | hx
      · exact (hdef i hi x (by rw [hw]; exact hx)).ne_empty
      · rcases hC.use k i hk x (by rw [hw]; exact hx) with hD | hE
        · obtain ⟨ks, hks⟩ := (hreach k hkl.le).path
          obtain ⟨j, -, i', hj, hx'⟩ := hC.written hks x hD
          exact (hdef i' (List.mem_of_getElem? hj) x hx').ne_empty
        · rcases hE with ⟨j, -, rfl⟩ | ⟨i', hi', hx'⟩
          · exact argName_ne_empty j
          · rw [hsym i' hi'] at hx'
            cases hx'
  | _ => rw [hw] at hx; simp [instrNames] at hx

/-- A renaming that sends no name other than the empty name to the empty name. -/
def RenNE (σ : String → String) : Prop := ∀ x, x ≠ "" → σ x ≠ ""

/-- Every name of `w'` is a name of `w` or the image under `σ` of a name of `w`. -/
def Under (σ : String → String) (w w' : LinstrR) : Prop :=
  ∀ x ∈ instrNames w', x ∈ instrNames w ∨ ∃ y ∈ instrNames w, x = σ y

theorem namesNE_of_under {σ : String → String} (hσ : RenNE σ) {w w' : LinstrR}
    (h : NamesNE w) (hu : Under σ w w') : NamesNE w' := by
  intro x hx
  rcases hu x hx with hx | ⟨y, hy, rfl⟩
  · exact h x hx
  · exact hσ y (h y hy)

theorem under_renLoad (σ : String → String) (w : LinstrR) :
    Under σ w (X86Backend.ImageCoalesceCfg.renLoad σ w) := by
  unfold X86Backend.ImageCoalesceCfg.renLoad
  split
  · split
    · intro x hx
      simp only [instrNames, opNames, List.cons_append, List.nil_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false,
        exists_eq_or_imp, exists_eq_left] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    · exact fun x hx => Or.inl hx
  · exact fun x hx => Or.inl hx

theorem under_renStore (σ : String → String) (w : LinstrR) :
    Under σ w (X86Backend.ImageCoalesceCfg.renStore σ w) := by
  unfold X86Backend.ImageCoalesceCfg.renStore
  split
  · split
    · intro x hx
      simp only [instrNames, opNames, List.cons_append, List.nil_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false,
        exists_eq_or_imp, exists_eq_left] at hx ⊢
      rcases hx with rfl | rfl | rfl | rfl <;> simp
    · exact fun x hx => Or.inl hx
  · exact fun x hx => Or.inl hx

theorem under_renStoreImm (σ : String → String) (w : LinstrR) :
    Under σ w (X86Backend.ImageCoalesceCfg.renStoreImm σ w) := by
  unfold X86Backend.ImageCoalesceCfg.renStoreImm
  split
  · split
    · intro x hx
      simp only [instrNames, opNames, List.cons_append, List.nil_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false,
        exists_eq_or_imp, exists_eq_left] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> simp
    · exact fun x hx => Or.inl hx
  · exact fun x hx => Or.inl hx

theorem under_renOpA (σ : String → String) (o : LOperand) :
    ∀ x ∈ opNames (X86Backend.ImageCoalesceCfg.renOpA σ o),
      x ∈ opNames o ∨ ∃ y ∈ opNames o, x = σ y := by
  intro x hx
  cases o <;> simp [X86Backend.ImageCoalesceCfg.renOpA, opNames] at hx ⊢ <;>
    rcases hx with rfl | rfl <;> simp

theorem under_renZero (σ : String → String) (w : LinstrR) :
    Under σ w (X86Backend.ImageCoalesceCfg.renZero σ w) := by
  unfold X86Backend.ImageCoalesceCfg.renZero
  split
  · split
    · rename_i d opn ss _
      intro x hx
      simp only [instrNames, List.cons_append, List.nil_append, List.flatMap_cons,
        List.mem_append, List.flatMap_map] at hx
      rcases hx with hx | hx
      · simp only [opNames, List.mem_singleton] at hx
        subst hx
        exact Or.inr ⟨d, by simp [instrNames, opNames], rfl⟩
      · obtain ⟨o, ho, hx⟩ := List.mem_flatMap.mp hx
        have hm : ∀ y ∈ opNames o, y ∈ instrNames (.Lopn [.reg d] opn ss) := fun y hy => by
          simp only [instrNames, List.cons_append, List.flatMap_cons, List.mem_append]
          exact Or.inr (List.mem_flatMap.mpr ⟨o, ho, hy⟩)
        rcases under_renOpA σ o x hx with h | ⟨y, hy, rfl⟩
        · exact Or.inl (hm x h)
        · exact Or.inr ⟨y, hm y hy, rfl⟩
    · exact fun x hx => Or.inl hx
  · exact fun x hx => Or.inl hx

/-- The renaming of the array positions keeps the names of an instruction of the shape
    `ShapeB` not empty under a renaming `RenNE`. -/
theorem namesNE_renArr {σ : String → String} (hσ : RenNE σ) {i : LinstrRM} (hs : ShapeB i.1)
    (h : NamesNE i.1) : NamesNE (X86Backend.ImageCoalesceCfg.renArr σ i).1 := by
  obtain ⟨w, t⟩ := i
  cases w with
  | Lopn ds o ss =>
      have ho : MnemB o := hs.2 ds o ss rfl
      unfold X86Backend.ImageCoalesceCfg.renArr
      split
      all_goals first
        | (simp only [X86Backend.ImageCoalesceCfg.renCallW, shadowCall?_of_mnemB ho]; exact h)
        | exact namesNE_of_under hσ h (under_renLoad σ _)
        | exact namesNE_of_under hσ h (under_renStore σ _)
        | exact namesNE_of_under hσ h (under_renZero σ _)
        | exact namesNE_of_under hσ h (under_renStoreImm σ _)
  | _ =>
      unfold X86Backend.ImageCoalesceCfg.renArr
      split <;> exact h

theorem shadowCall?_of_shapeB {w : LinstrR} (h : ShapeB w) : LprogIsa.shadowCall? w = none := by
  cases w with
  | Lopn ds o ss => exact shadowCall?_of_mnemB (h.2 ds o ss rfl)
  | _ => rfl

theorem base_mem_instrNames {dst opn base idx : String} {sc : Nat} {rest : List LOperand} :
    base ∈ instrNames (.Lopn [.reg dst] opn (.arrIdx base idx sc :: rest)) := by
  simp [instrNames, opNames]

/-- **The coalescing renaming sends no name to the empty name**: on code of the shape
    `ShapeB` whose names are not empty, the alias table sends the destination of a store
    (indexed or constant-index) to the image of its base. -/
theorem renNE_aliasTab (outs : List (String × Nat)) {C : List LinstrRM}
    (hC : ∀ i ∈ C, ShapeB i.1 ∧ NamesNE i.1) :
    RenNE (canonMemrefName (X86Backend.ImageStraightRoute.aliasTab outs C)) := by
  suffices h : ∀ (L : List LinstrRM) (m : Std.HashMap String String),
      (∀ i ∈ L, ShapeB i.1 ∧ NamesNE i.1) → RenNE (canonMemrefName m) →
        RenNE (canonMemrefName (L.foldl (X86Backend.ImageStraightRoute.aliasStepO outs) m)) from
    h C {} hC fun x hx => by simpa [canonMemrefName] using hx
  intro L
  induction L with
  | nil => exact fun _ _ hm => hm
  | cons i L ih =>
    intro m hL hm
    rw [List.foldl_cons]
    refine ih _ (fun j hj => hL j (List.mem_cons_of_mem _ hj)) ?_
    obtain ⟨hs, hn⟩ := hL i List.mem_cons_self
    unfold X86Backend.ImageStraightRoute.aliasStepO
    rw [shadowCall?_of_shapeB hs]
    dsimp only
    split
    · next dst opn base _ _ rest heq =>
      have hb : base ≠ "" := hn base (by rw [heq]; exact base_mem_instrNames)
      split_ifs
      · intro x hx
        unfold canonMemrefName
        rw [Std.HashMap.getD_insert]
        split
        · exact hm base hb
        · exact hm x hx
      · exact hm
    · next dst opn base rest heq =>
      have hb : base ≠ "" := hn base (by rw [heq]; simp [instrNames, opNames])
      split_ifs
      · intro x hx
        unfold canonMemrefName
        rw [Std.HashMap.getD_insert]
        split
        · exact hm base hb
        · exact hm x hx
      · exact hm
    · exact hm

/-- **The store-thread alias map sends no name to the empty name** on a body whose names are
    not empty. -/
theorem renNE_arrChainAlias {body : Lcmd} (h : ∀ i ∈ body, NamesNE i.li_i) :
    RenNE (canonMemrefName (arrChainAlias body)) := by
  have key : ∀ (L : Lcmd) (l : List (String × String)), (∀ i ∈ L, NamesNE i.li_i) →
      (∀ x, x ≠ "" → (l.lookup x).getD x ≠ "") →
        ∀ x, x ≠ "" → ((L.foldl X86Backend.PhysAbiShape.aliasStepL l).lookup x).getD x ≠ "" := by
    intro L
    induction L with
    | nil => exact fun _ _ hl => hl
    | cons i L ih =>
      intro l hL hl
      rw [List.foldl_cons]
      refine ih _ (fun j hj => hL j (List.mem_cons_of_mem _ hj)) ?_
      have hn := hL i List.mem_cons_self
      unfold X86Backend.PhysAbiShape.aliasStepL
      split
      · next dst opn base _ _ rest heq =>
        have hb : base ≠ "" := hn base (by rw [heq]; exact base_mem_instrNames)
        split_ifs
        · intro x hx
          simp only [List.lookup]
          split
          · exact hl base hb
          · exact hl x hx
        · exact hl
      · exact hl
  intro x hx
  unfold canonMemrefName
  rw [(X86Backend.PhysAbiShape.arrChainAlias_spec body).1 x]
  exact key body [] h (fun y hy => by simpa using hy) x hx

theorem opNames_canonMemrefOperand (m : Std.HashMap String String) (o : LOperand) :
    opNames (canonMemrefOperand m o) = (opNames o).map (canonMemrefName m) := by
  cases o <;> rfl

/-- The store-thread canonicalization keeps the names of a body not empty. -/
theorem namesNE_canonicalizeMemrefThread {body : Lcmd} (h : ∀ i ∈ body, NamesNE i.li_i) :
    ∀ i ∈ canonicalizeMemrefThread body, NamesNE i.li_i := by
  have hm := renNE_arrChainAlias h
  intro i hi
  unfold canonicalizeMemrefThread at hi
  dsimp only at hi
  split at hi
  · exact h i hi
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    split
    · rename_i ds o ss heq
      have hn := h j hj
      rw [heq] at hn
      intro x hx
      simp only [instrNames, List.flatMap_append, List.flatMap_map,
        opNames_canonMemrefOperand, List.mem_append, List.mem_flatMap, List.mem_map] at hx
      rcases hx with ⟨a, ha, y, hy, rfl⟩ | ⟨a, ha, y, hy, rfl⟩
      · exact hm y (hn y (List.mem_flatMap.mpr ⟨a, List.mem_append_left _ ha, hy⟩))
      · exact hm y (hn y (List.mem_flatMap.mpr ⟨a, List.mem_append_right _ ha, hy⟩))
    · exact h j hj

theorem regReads_sub_instrNames {w : LinstrR} {x : String} (hx : x ∈ regReads w) :
    x ∈ instrNames w := by
  cases w with
  | Lopn ds o ss =>
      simp only [regReads, List.mem_append, List.mem_flatMap] at hx
      simp only [instrNames, List.mem_flatMap, List.mem_append]
      rcases hx with ⟨a, ha, hx⟩ | ⟨a, ha, hx⟩
      · refine ⟨a, Or.inr ha, ?_⟩
        cases a <;> simp_all [opNames]
      · refine ⟨a, Or.inl ha, ?_⟩
        cases a <;> simp_all [opNames]
  | _ => simp [regReads] at hx

/-- The names a list of instructions reads before it writes them are read names. -/
theorem mem_regExposed {is : List LinstrR} {x : String} (hx : x ∈ regExposed is) :
    ∃ i ∈ is, x ∈ regReads i := by
  have key : ∀ (L : List LinstrR) (acc : List String × List String),
      (∀ y ∈ acc.1, ∃ i ∈ is, y ∈ regReads i) → (∀ i ∈ L, i ∈ is) →
      ∀ y ∈ (L.foldl (fun (acc : List String × List String) i =>
        (acc.1 ++ ((regReads i).filter fun x => !acc.2.contains x && !acc.1.contains x).eraseDups,
          acc.2 ++ regWrites i)) acc).1, ∃ i ∈ is, y ∈ regReads i := by
    intro L
    induction L with
    | nil => exact fun _ h _ => h
    | cons i L ih =>
      intro acc hacc hL
      rw [List.foldl_cons]
      refine ih _ (fun y hy => ?_) (fun j hj => hL j (List.mem_cons_of_mem _ hj))
      rcases List.mem_append.mp hy with hy | hy
      · exact hacc y hy
      · rw [List.mem_eraseDups] at hy
        exact ⟨i, hL i List.mem_cons_self, (List.mem_filter.mp hy).1⟩
  exact key is ([], []) (fun _ h => by cases h) (fun _ h => h) x hx

/-- The names of the register liveness table without names read after the code are names
    the code reads. -/
theorem mem_useNames_of_liveRegTab {C : List LinstrRM} {p : Nat} {y : String}
    (hy : y ∈ tabAt (liveRegTab C []) p) : ∃ i ∈ C, y ∈ useNames i.1 := by
  have h := mem_liveRegTab_iff.mp hy
  clear hy
  induction h with
  | read hi hu => exact ⟨_, List.mem_of_getElem? hi, hu⟩
  | next _ _ _ _ ih => exact ih
  | jump _ _ _ _ ih => exact ih
  | out h => cases h

theorem useNames_sub_instrNames {w : LinstrR} {x : String} (hx : x ∈ useNames w) :
    x ∈ instrNames w := by
  cases w with
  | Lopn ds o ss =>
      simp only [useNames, List.mem_flatMap] at hx
      obtain ⟨a, ha, hx⟩ := hx
      exact List.mem_flatMap.mpr ⟨a, List.mem_append_right _ ha, hx⟩
  | _ => simp [useNames] at hx

theorem livepin_ne_empty : "%livepin" ≠ "" := by decide

theorem namesNE_livepinOps {ss : List LOperand} (h : ∀ o ∈ ss, ∀ x ∈ opNames o, x ≠ "") :
    NamesNE (.Lopn [.reg "%livepin"] "LIVEPIN" ss) := by
  intro x hx
  obtain ⟨o, ho, hx⟩ := List.mem_flatMap.mp hx
  rcases List.mem_append.mp ho with ho | ho
  · rw [List.mem_singleton.mp ho] at hx
    rw [show x = "%livepin" from List.mem_singleton.mp hx]
    exact livepin_ne_empty
  · exact h o ho x hx

theorem namesNE_livepin {ns : List String} (h : ∀ x ∈ ns, x ≠ "") :
    NamesNE (.Lopn [.reg "%livepin"] "LIVEPIN" (ns.map LOperand.reg)) := by
  refine namesNE_livepinOps fun o ho x hx => ?_
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ho
  rw [show x = y from List.mem_singleton.mp hx]
  exact h y hy

/-- The liveness instructions at the back edges keep the names of the code not empty. -/
theorem namesNE_backEdgePins {C : List LinstrRM} (h : ∀ i ∈ C, NamesNE i.1) :
    ∀ i ∈ backEdgePins C, NamesNE i.1 := by
  have hpin : ∀ k l, ∀ i ∈ backEdgePin (liveRegTab C []) C k l, NamesNE i.1 := by
    intro k l i hi
    unfold backEdgePin at hi
    dsimp only at hi
    split at hi
    · rename_i p _
      split at hi
      · rw [List.mem_singleton.mp hi]
        refine namesNE_livepin fun x hx => ?_
        unfold backEdgePinNames at hx
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨w, hw, hx⟩ := mem_regExposed hx
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hw
          exact h j (List.mem_of_mem_drop (List.mem_of_mem_take hj)) x
            (regReads_sub_instrNames hx)
        · obtain ⟨j, hj, hx⟩ := mem_useNames_of_liveRegTab (List.mem_filter.mp hx).1
          exact h j hj x (useNames_sub_instrNames hx)
      · cases hi
    · cases hi
  intro i hi
  obtain ⟨⟨j, k⟩, hjk, hi⟩ := List.mem_flatMap.mp hi
  have hj : j ∈ C := List.fst_mem_of_mem_zipIdx hjk
  dsimp only at hi
  split at hi
  all_goals first
    | (rw [List.mem_singleton.mp hi]; exact h j hj)
    | (rcases List.mem_append.mp hi with hi | hi
       · exact hpin _ _ i hi
       · rw [List.mem_singleton.mp hi]; exact h j hj)

theorem copyName_ne_empty {D : String} (hD : D ≠ "") (j : Nat) : copyName D j ≠ "" := by
  unfold copyName
  split
  · exact hD
  · intro h
    have := congrArg String.length h
    simp at this

theorem namesNE_resCopyCode {src D : String} (hs : src ≠ "") (hD : D ≠ "") (m : Nat) :
    ∀ i ∈ resCopyCode src D m, NamesNE i.1 := by
  intro i hi
  obtain ⟨j, -, hi⟩ := List.mem_flatMap.mp hi
  simp only [resCopyStep, List.mem_cons, List.not_mem_nil, or_false] at hi
  have hi1 : copyIdx ≠ "" := by decide
  have hi2 : copyTmp ≠ "" := by decide
  rcases hi with rfl | rfl | rfl <;> intro x hx <;>
    simp only [movImmI, movI, instrNames, opNames, List.cons_append, List.nil_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
  · rcases hx with rfl; exact hi1
  · rcases hx with rfl | rfl | rfl
    · exact hi2
    · exact hs
    · exact hi1
  · rcases hx with rfl | rfl | rfl | rfl
    · exact copyName_ne_empty hD _
    · exact copyName_ne_empty hD _
    · exact hi1
    · exact hi2

/-- The array result copy keeps names not empty when every returned operand is a register
    with a name that is not empty. -/
theorem namesNE_regionLprogCopy (a : AbiNames) (ts : List JasminTy) (code : List LinstrRM)
    {res : List LOperand} (hres : ∀ o ∈ res, ∃ x, o = .reg x ∧ x ≠ "") :
    ∀ i ∈ regionLprogCopy a none ts code res, NamesNE i.1 := by
  intro i hi
  unfold regionLprogCopy at hi
  split at hi
  · rename_i t
    split at hi
    · rename_i src D m hc
      unfold resCopyOf at hc
      split at hc
      · rename_i w m' op
        split_ifs at hc with hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        obtain ⟨x, hx, hne⟩ := hres op (List.mem_singleton_self op)
        subst hx
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcond
        exact namesNE_resCopyCode hne hcond.1.1.1.2 _ i hi
      · cases hc
    · cases hi
  · cases hi

/-- **The coalescing renaming at a result alias sends no name to the empty name** when the
    result buffer of the alias is not empty: the renaming is `renNE_aliasTab`'s renaming
    followed by the renaming of the result root to the result buffer. -/
theorem renNE_resAliasTab (outs : List (String × Nat)) {rr : Option (String × String)}
    {C : List LinstrRM} (hC : ∀ i ∈ C, ShapeB i.1 ∧ NamesNE i.1)
    (hrr : ∀ D src, rr = some (D, src) → D ≠ "") :
    RenNE (canonMemrefName (resAliasTab outs rr C)) := by
  have h0 := renNE_aliasTab outs hC
  cases rr with
  | none => exact h0
  | some p =>
    obtain ⟨D, src⟩ := p
    intro x hx
    show X86Backend.ImageStraightRoute.chainAliasRes outs D src C x ≠ ""
    rw [X86Backend.ImageStraightRoute.chainAliasRes_apply]
    split
    · split_ifs
      · exact hrr D src rfl
      · exact h0 x hx
    · exact h0 x hx

/-- The result buffer of the result alias of a region export is not empty. -/
theorem resAliasOf_ne_empty {callee : Option CalleeTab} {D? : Option String}
    {ts : List JasminTy} {res : List LOperand} :
    ∀ D src, resAliasOf callee D? ts res = some (D, src) → D ≠ "" := by
  intro D src h
  unfold resAliasOf at h
  split at h
  · split_ifs at h with hD
    cases h
    exact hD
  · cases h

/-- The code given to the allocation keeps the names not empty. -/
theorem namesNE_regionAllocCode {C : List LinstrRM} {rr : Option (String × String)}
    (hC : ∀ i ∈ C, ShapeB i.1 ∧ NamesNE i.1) (hrr : ∀ D src, rr = some (D, src) → D ≠ "") :
    ∀ i ∈ regionAllocCode C [] rr, NamesNE i.1 := by
  refine namesNE_backEdgePins fun i hi => ?_
  rcases mem_pinSelfMoves hi with hp | ⟨t, a, z, sc, w, n, ⟨hp, rfl⟩ | ⟨hp, rfl⟩⟩
  all_goals
    obtain ⟨j, hj, hje⟩ := List.mem_map.mp hp
    have hne := namesNE_renArr (renNE_resAliasTab [] hC hrr) (hC j hj).1 (hC j hj).2
    rw [hje] at hne
  · exact hne
  · intro x hx
    simp only [selfPinLoad, instrNames, List.cons_append, List.nil_append, List.flatMap_cons,
      List.flatMap_nil, opNames, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl
    all_goals exact hne _ (by simp [instrNames, opNames])
  · intro x hx
    simp only [selfPinStore, instrNames, List.cons_append, List.nil_append, List.flatMap_cons,
      List.flatMap_nil, opNames, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact livepin_ne_empty
    all_goals exact hne _ (by simp [instrNames, opNames])

/-- The names the liveness instruction at entry reads are argument names. -/
theorem entryPinNames_ne_empty (a : AbiNames) (C : List LinstrRM) :
    ∀ x ∈ entryPinNames a C, x ≠ "" := by
  intro x hx
  unfold entryPinNames at hx
  dsimp only at hx
  rcases List.mem_append.mp hx with hx | hx
  · split at hx
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      obtain ⟨nm, -, hnm⟩ := List.mem_filterMap.mp hq
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hnm
      have := List.find?_some hq'
      simp only [beq_iff_eq] at this
      rw [← this]
      exact argName_ne_empty _
    · cases hx
  · obtain ⟨j, -, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hx).1
    exact argName_ne_empty j

/-- **The names of the body the allocation certifies are not empty** when the export has
    the shape `ShapeB`, its names are not empty and its returned operands are registers with
    names that are not empty. -/
theorem namesNE_regionAllocBody (a : AbiNames) (nArgs : Nat) (ts : List JasminTy)
    (r : Exported) (hr : ∀ i ∈ r.code, ShapeB i.1 ∧ NamesNE i.1)
    (hres : ∀ o ∈ r.res, ∃ x, o = .reg x ∧ x ≠ "") :
    ∀ i ∈ regionAllocBody a nArgs ts r, NamesNE i.li_i := by
  have hC : ∀ i ∈ r.code ++ regionLprogCopy a none ts r.code r.res, ShapeB i.1 ∧ NamesNE i.1 := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hr i hi
    · exact ⟨shapeB_regionLprogCopy a ts r.code r.res i hi,
        namesNE_regionLprogCopy a ts r.code hres i hi⟩
  have hac := namesNE_regionAllocCode (rr := resAliasOf none (some a.outArg) ts r.res) hC
    resAliasOf_ne_empty
  have hsac := shapeB_regionAllocCode (rr := resAliasOf none (some a.outArg) ts r.res)
    fun i hi => (hC i hi).1
  have hbody : ∀ i ∈ (regionAllocCode (r.code ++ regionLprogCopy a none ts r.code r.res)
      [] (resAliasOf none (some a.outArg) ts r.res)).map (fun i => (⟨0, i.1⟩ : Linstr))
        ++ [⟨0, .Lret⟩], NamesNE i.li_i ∧ ShapeB i.li_i := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact ⟨hac j hj, hsac j hj⟩
    · rw [List.mem_singleton.mp hi]
      exact ⟨fun x hx => by simp [instrNames] at hx,
        shapeB_nonLopn (fun _ _ _ e => by cases e) (fun _ _ e => by cases e)⟩
  have hargs : ∀ n, ∀ o ∈ (List.range n).map (fun j => (.reg (argName j) : LOperand)),
      ∀ x ∈ opNames o, x ≠ "" := by
    intro n o ho x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp ho
    rw [show x = argName j from List.mem_singleton.mp hx]
    exact argName_ne_empty j
  intro i hi
  unfold regionAllocBody at hi
  split at hi
  · rcases List.mem_append.mp hi with hi | hi
    · rcases List.mem_append.mp hi with hi | hi
      · rw [List.mem_singleton.mp hi]; exact namesNE_livepinOps (hargs _)
      · rw [expandCallShadows_of_shapeB fun j hj => (hbody j hj).2] at hi
        exact namesNE_canonicalizeMemrefThread (fun j hj => (hbody j hj).1) i hi
    · unfold resLivePin at hi
      split at hi
      · split at hi
        · rename_i rn hrn
          rw [List.mem_singleton.mp hi]
          refine namesNE_livepin (ns := [rn]) fun x hx => ?_
          rw [List.mem_singleton.mp hx]
          obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (List.mem_of_mem_head? hrn)
          obtain ⟨y, rfl, hy⟩ := hres o ho
          exact hy
        · cases hi
      · cases hi
  · rcases List.mem_append.mp hi with hi | hi
    · split at hi
      · rw [List.mem_singleton.mp hi]; exact namesNE_livepinOps (hargs _)
      · cases hi
    · refine namesNE_canonicalizeMemrefThread (fun j hj => ?_) i hi
      rcases List.mem_append.mp hj with hj | hj
      · unfold arrBasePins at hj
        dsimp only at hj
        split at hj
        · cases hj
        · rw [List.mem_singleton.mp hj]
          exact namesNE_livepin (entryPinNames_ne_empty a _)
      · exact (hbody j hj).1

/-- **The empty name is no name of a body whose names are not empty.** -/
theorem empty_not_mem_bodyNames {B : Lcmd} (h : ∀ i ∈ B, NamesNE i.li_i) : "" ∉ bodyNames B := by
  intro hm
  obtain ⟨i, hi, hx⟩ := mem_instrNames_of_mem_bodyNames hm
  exact h i hi "" hx rfl

/-! ## 7. The domain facts at the allocation -/

/-- The returned operands of the export are registers with names that are not empty. -/
theorem exportR_res_ne (fn : String) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) {r : Exported}
    (h : exportR Γ.length fn p Γ.length 0 x86Data = some r) :
    ∀ o ∈ r.res, ∃ x, o = .reg x ∧ x ≠ "" := by
  intro o ho
  obtain ⟨x, rfl, hx⟩ := (exportR_blk Γ.length fn p Γ.length 0 r h le_rfl).1 o ho
  refine ⟨x, rfl, ?_⟩
  rcases hx with ⟨j, -, rfl⟩ | ⟨j, -, -, rfl⟩
  · exact argName_ne_empty j
  · exact (exportRegName_regName j).ne_empty

/-- **The domain facts of the body the allocation certifies**: at the export `r` of a program
    without `call` that passes `regionExportableB`, the body `B := regionAllocBody a Γ.length
    ts r` does not name the empty name, is no straight-line call body, and under the size
    bound `numGPRegs + |bodyNames B| + 1 ≤ vectorBase` its allocation names no vector
    register and meets the bound `hfit` of the linear scan. -/
theorem regionAllocBody_dom (a : AbiNames) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (p : NFProg jasminDialect Γ ts) (hp : regionExportableB p = true)
    (hcf : p.callFree = true) {r : Exported}
    (hr : exportR Γ.length a.fname p Γ.length 0 x86Data = some r) :
    "" ∉ bodyNames (regionAllocBody a Γ.length ts r)
      ∧ bodyStraightCall (regionAllocBody a Γ.length ts r) = false
      ∧ (numGPRegs + (bodyNames (regionAllocBody a Γ.length ts r)).length + 1 ≤ vectorBase →
          (∀ n, allocName (regionAllocBody a Γ.length ts r)
            (regionAllocTbl (regionAllocBody a Γ.length ts r)) n ∉ vectorRegNames)
          ∧ numGPRegs + (physLiveItems (bodyTraceOut (regionAllocBody a Γ.length ts r)
            [])).length ≤ vectorBase) := by
  have hshape : ∀ i ∈ r.code, ShapeB i.1 :=
    fun i hi => (exportR_mnemDom Γ.length a.fname p hp hcf _ _ r hr i hi).2.2
  have hB := shapeB_regionAllocBody a Γ.length ts r hshape
  refine ⟨empty_not_mem_bodyNames (namesNE_regionAllocBody a Γ.length ts r
    (fun i hi => ⟨hshape i hi, exportR_namesNE a.fname p hp hcf hr i hi⟩)
    (exportR_res_ne a.fname p hr)), bodyStraightCall_of_shapeB hB, fun hsize => ⟨?_, ?_⟩⟩
  · exact allocName_not_vec hB hsize
  · have := physLiveItems_length_le (regionAllocBody a Γ.length ts r)
    omega

/-- **The merge conditions at the allocation with the domain facts discharged**
    (`mergeSep_regionLprogC_dom`): `mergeSep_regionLprogC` over the context `nfCtx σ` of the
    direct route, at a program without `call` that passes `regionExportableB`, where the
    hypotheses that are facts of the domain of the region route are proved: the empty name
    is no name of the certified body (`regionAllocBody_dom`), the layout has `Γ.length`
    parameters (`nfCtx_length`), the allocation names no vector register
    (`allocName_not_vec`), the export has no symbol-base load (`exportR_symReads`), every
    compare of the export reads its destination (`exportR_cmpReads`) and the body is no
    straight-line call body. The hypotheses left are the layout conditions on the result and
    parameter registers, the result types `[t]` of the program, the size bound
    `numGPRegs + |bodyNames B| + 1 ≤ vectorBase`, and the two conditions on the live ranges
    of the certified body. -/
theorem mergeSep_regionLprogC_dom (a : AbiNames) (σ : AbiLayout) {ts : List JasminTy}
    (p : NFProg jasminDialect (nfCtx σ) ts) (hp : regionExportableB p = true)
    (hcf : p.callFree = true) (ex : List String) {P : Lprog}
    {cert : List (String × String)} (hP : regionLprogC a p none ex = some (P, cert)) :
    ∃ r, exportR (nfCtx σ).length a.fname p (nfCtx σ).length 0 x86Data = some r
      ∧ ∀ (nm : String → String) (body : Lcmd) (t : JasminTy),
        let B := regionAllocBody a (nfCtx σ).length ts r
        let d := regionCoParts σ nm body t r.code r.res cert none
        let K : String → Prop := fun n => n ∈ allocCertNames B
          ∧ certMergeKeep σ d.arrs (crossNames (d.pre ++ d.ren)) n = true
        (∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true) →
        (∀ q ∈ σ.args, isHwRegName (nm q.reg) = true) →
        ts = [t] →
        numGPRegs + (bodyNames B).length + 1 ≤ vectorBase →
        (∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
          ∀ y ∈ tabAt d.live (k + 1), ∀ x ∈ regDefs i, y ≠ x → K y → K x →
            ∃ pos, LiveAt (bodyTraceOut B []) pos (nameSlot B y)
              ∧ LiveAt (bodyTraceOut B []) pos (nameSlot B x)) →
        (∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
          ∀ y ∈ tabAt d.live (k + 1), ∀ x ∈ regDefs i, ¬ PlainName y → K x →
            y ≠ allocName B (regionAllocTbl B) x) →
        MergeSep d := by
  obtain ⟨r, hr, hM⟩ := mergeSep_regionLprogC a p hp hcf ex hP
  refine ⟨r, hr, ?_⟩
  intro nm body t B d K hRA hArg hts hsize hcov hnp
  obtain ⟨h0, hsc, hfit⟩ := regionAllocBody_dom a p hp hcf hr
  obtain ⟨hvec, hfit⟩ := hfit hsize
  exact hM σ nm body t h0 hRA hArg (nfCtx_length σ).le (fun n _ => hvec n)
    (exportR_symReads _ _ p hp hcf hr) (exportR_cmpReads _ _ p hp hcf hr) hts hfit hsc hcov hnp

/-! ## 8. The layout conditions -/

/-- A general-purpose name of a printed body is a hardware register name. -/
theorem isHwRegName_of_gpOk {x : String} (h : X86Backend.DecodePrinted.gpOk x = true) :
    isHwRegName x = true := by
  have hsub : ∀ y ∈ X86Backend.DecodePrinted.gpList, y ∈ hwRegNames := by decide
  exact List.contains_iff_mem.mpr (hsub x (List.contains_iff_mem.mp h))

/-- **The result register condition from the gate**: when the returned operands pass
    `regionResultB`, the export name of a result register of the layout is a hardware
    register name. -/
theorem hRA_of_regionResultB {σ : AbiLayout} {nm : String → String} {body : Lcmd}
    {t : JasminTy} {res : List LOperand} (h : regionResultB σ nm body t res = true) :
    ∀ RA, σ.result = .reg RA → isHwRegName (nm RA) = true := by
  intro RA hRA
  unfold regionResultB at h
  rw [hRA] at h
  split at h
  · simp at h
  · split at h
    · rename_i RA' _ heq
      cases heq
      simp only [Bool.and_eq_true] at h
      exact isHwRegName_of_gpOk h.1.1.2
    · simp at h
  · simp at h

/-- **The layout conditions of the region route** on the layout `σ` under the export names
    `exportReg`: the export name of a result register and of every parameter register is a
    hardware register name, and the array of the result buffer `regionResBuf σ exportReg` is
    the output array of the export names `nfAbiNames` of the direct route. -/
def layoutOkB (σ : AbiLayout) : Bool :=
  (match σ.result with
    | .reg RA => isHwRegName (exportReg RA)
    | _ => true)
  && σ.args.all (fun q => isHwRegName (exportReg q.reg))
  && (regionResBuf σ exportReg).map Prod.fst == (nfOutIdx σ).map argName

/-- **The soundness of `layoutOkB`**: the result register condition, the parameter register
    condition, and the agreement of the result buffer with the output array of
    `nfAbiNames fn σ`. -/
theorem layoutOkB_sound {σ : AbiLayout} (h : layoutOkB σ = true) :
    (∀ RA, σ.result = .reg RA → isHwRegName (exportReg RA) = true)
      ∧ (∀ q ∈ σ.args, isHwRegName (exportReg q.reg) = true)
      ∧ ∀ (fn D : String) (n : Nat), regionResBuf σ exportReg = some (D, n) →
          D = (nfAbiNames fn σ).outArg := by
  unfold layoutOkB at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hres, hargs⟩, hbuf⟩ := h
  refine ⟨fun RA hRA => ?_, hargs, fun fn D n hD => ?_⟩
  · rw [hRA] at hres; exact hres
  · rw [hD] at hbuf
    simp only [nfAbiNames, ← hbuf, Option.map_some, Option.getD_some]

/-- The System V layout of `mpn_and_n` on arrays of `4` words (the fields of `andAbi4`) meets
    the layout conditions. -/
theorem layoutOkB_andN :
    layoutOkB
      { args := [⟨"rp", "%rdi", .words 4⟩, ⟨"up", "%rsi", .words 4⟩, ⟨"vp", "%rdx", .words 4⟩,
          ⟨"n", "%rcx", .scalar⟩]
        consts := [], result := .words "%rdi" 4, bounds := [("%rcx", 4)], frameLo := -256,
        frameHi := -8 } = true := by
  simp [layoutOkB, regionResBuf, X86Backend.ImageAddrRoute.slotArrOf, nfOutIdx, exportReg,
    isHwRegName, hwRegNames, JasminLsemAddrImage.slotOfReg, gpRegNames, List.findIdx?,
    List.findIdx?.go]

/-- The System V layout of `ltu` (the fields of `ltuAbi`) meets the layout conditions. -/
theorem layoutOkB_ltu :
    layoutOkB
      { args := [⟨"x", "%rdi", .scalar⟩, ⟨"y", "%rsi", .scalar⟩]
        consts := [("ONES", .int (2 ^ 64 - 1))], result := .reg "%rax", bounds := [],
        frameLo := -256, frameHi := -8 } = true := by
  simp [layoutOkB, regionResBuf, nfOutIdx, exportReg, isHwRegName, hwRegNames, gpRegNames]

/-- **The merge conditions at the allocation under the layout conditions**
    (`mergeSep_regionLprogC_layout`): `mergeSep_regionLprogC_dom` at the export names
    `exportReg`, with the conditions on the result and parameter registers discharged by
    `layoutOkB σ`. The hypotheses left are the result types `[t]` of the program, the size
    bound, and the two conditions on the live ranges of the certified body. -/
theorem mergeSep_regionLprogC_layout (a : AbiNames) (σ : AbiLayout) {ts : List JasminTy}
    (p : NFProg jasminDialect (nfCtx σ) ts) (hp : regionExportableB p = true)
    (hcf : p.callFree = true) (ex : List String) {P : Lprog}
    {cert : List (String × String)} (hP : regionLprogC a p none ex = some (P, cert))
    (hσ : layoutOkB σ = true) :
    ∃ r, exportR (nfCtx σ).length a.fname p (nfCtx σ).length 0 x86Data = some r
      ∧ ∀ (body : Lcmd) (t : JasminTy),
        let B := regionAllocBody a (nfCtx σ).length ts r
        let d := regionCoParts σ exportReg body t r.code r.res cert none
        let K : String → Prop := fun n => n ∈ allocCertNames B
          ∧ certMergeKeep σ d.arrs (crossNames (d.pre ++ d.ren)) n = true
        ts = [t] →
        numGPRegs + (bodyNames B).length + 1 ≤ vectorBase →
        (∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
          ∀ y ∈ tabAt d.live (k + 1), ∀ x ∈ regDefs i, y ≠ x → K y → K x →
            ∃ pos, LiveAt (bodyTraceOut B []) pos (nameSlot B y)
              ∧ LiveAt (bodyTraceOut B []) pos (nameSlot B x)) →
        (∀ (k : Nat) (i : LinstrRM), d.pre.length ≤ k → (d.pre ++ d.ren)[k]? = some i →
          ∀ y ∈ tabAt d.live (k + 1), ∀ x ∈ regDefs i, ¬ PlainName y → K x →
            y ≠ allocName B (regionAllocTbl B) x) →
        MergeSep d := by
  obtain ⟨r, hr, hM⟩ := mergeSep_regionLprogC_dom a σ p hp hcf ex hP
  obtain ⟨hRA, hArg, -⟩ := layoutOkB_sound hσ
  exact ⟨r, hr, fun body t => hM exportReg body t hRA hArg⟩

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapDom
