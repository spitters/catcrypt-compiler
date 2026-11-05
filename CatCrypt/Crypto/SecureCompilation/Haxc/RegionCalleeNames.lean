/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapPins
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegComplete

@[expose] public section

set_option autoImplicit false

/-!
# The names of the liveness table at the entries of the segments of a calling body

The entry sets of the segments of a calling body are read off the register liveness table
`liveRegTab` (`insTab`), and the checks of the segments compare the names of these sets at
the exits (`CalleeSegCheck.segOutsAt`). The merge of the allocation certificate is restricted
to the names `crossNames`: the names some piece of `callPieces` of a block reads as a register
before it writes it (`regExposed`). This module proves that at the start of a piece, the
start of a block or the position after a shadow instruction of a call, every name of the
liveness table is a name read after the body, an array name of the body (`arrNames`), or a
name of `crossNames`. This is the first part of the location condition C3 of the
completeness of the checks of a calling body.

The statement holds under two conditions on the instructions, which the reference of a
region export meets (`ReadCover`, `WriteCover`): a name an instruction reads as an operand
name (`useNames`) and not as a register (`regReads`) is the array it reads (`arrUse?`), and a
register destination (`regWrites`) is a name the liveness table kills (`regDefs`), a name the
instruction also reads, or the array it writes (`arrDefs`). The first condition fails at an
indexed operand outside a load and a store, the load-effective-address
`LEA d, [b + x · sc]` among them, whose base is read as a register and is not a name of
`regReads`; the second fails at a compare `CMP d, [a, b]` whose destination is no source. In
the region export, an indexed operand occurs only in the load `LOADIDX` and the store
`STOREIDX` with the memory tags `.load` and `.store`, and every compare is `CMP r, [r, 0]`.

Section 4 bounds the entry live sets of the checks of the segments by the same table (step
S2 of that completeness): on a reference of the shape `RefShape`, the live names the checker
finds at the entry of a cut program lie in `insTab`, so the entry inclusion of the checks adds
no refusal there.

## Main definitions

* `PieceStart`: the start of a block or the position after a shadow instruction of a call.
* `ReadCover`, `WriteCover`: the conditions on the instructions.
* `RefShape`: the shape of an instruction of a reference: conditional jumps on the zero flag,
  operations with one register destination or widening multiplies after a write of their
  implicit source.
* `mulxReads`, `liveTabX`: the implicit source of a widening multiply, and the liveness table
  extended by it.

## Main results

* `callPieces_head`, `callPieces_tail`: the piece of `callPieces` that starts at the start of
  a list or after a shadow instruction.
* `mem_regExposed`: a name read before it is written is a name of `regExposed`.
* `mem_crossNames_of_exposed`: a name read before it is written from the start of a piece is a
  name of `crossNames`.
* `mem_crossNames_of_liveRegTab`: at the start of a piece, a name of the liveness table is a
  name read after the body, an array name or a name of `crossNames`.
* `mem_crossNames_of_liveRegTab_ren`: the same for a body renamed by a map of names, through
  `RegionAllocMapPins.pLiveR_renRM`: a name of the liveness table of the renamed body is the
  image of such a name of the body.
* `tabClosed_liveTabX`: on a reference of the shape `RefShape`, the liveness table with the
  implicit source of each widening multiply is closed along the body.
* `livePost_cutAt`: that table along the cut positions is a post-fixpoint of `liveRound` on
  every cut program.
* `entry_live_sub_insTab`: the live names the checker finds at the entry of a cut program lie
  in `insTab`.
* `ownedCheckMCIn_insTab`, `calleeSegB_insTab_iff`: the entry inclusion adds no refusal at
  `insTab`; `calleeSegB` at `insTab` is the check with the entry inclusion removed.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.RegionCalleeNames

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop (findLabelMem)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRegAlloc (useNames regDefs arrUse?
  arrDefs jumpLabel?)
open CatCrypt.Crypto.SecureCompilation.X86Backend.AllocCheck.LcmdCFG
open RegionAllocMapComplete

/-! ## 1. Pieces -/

/-- An instruction is a shadow instruction of a call. -/
def IsShadow (i : LinstrRM) : Prop := (LprogIsa.shadowCall? i.1).isSome = true

theorem callPieces_ne_nil (l : List LinstrRM) : callPieces l ≠ [] := by
  cases l with
  | nil => simp [callPieces]
  | cons i t =>
      unfold callPieces
      rw [List.foldr_cons]
      split
      · simp
      · split <;> simp

/-- The pieces of a list with a first instruction: a shadow instruction is a piece of its
    own, and any other instruction starts the first piece of the rest. -/
theorem callPieces_cons (i : LinstrRM) (t : List LinstrRM) :
    ∃ p ps, callPieces t = p :: ps ∧ callPieces (i :: t) =
      if (LprogIsa.shadowCall? i.1).isSome then [i] :: p :: ps else (i :: p) :: ps := by
  obtain ⟨p, ps, hp⟩ := List.exists_cons_of_ne_nil (callPieces_ne_nil t)
  refine ⟨p, ps, hp, ?_⟩
  unfold callPieces at hp ⊢
  rw [List.foldr_cons, hp]

/-- **The first piece**: it holds the instructions of the list up to the first shadow
    instruction, that one included. -/
theorem callPieces_head : ∀ (l : List LinstrRM) (j : Nat) (hj : j < l.length),
    (∀ m (h : m < j), ¬ IsShadow (l[m]'(by omega))) →
    ∃ p ps, callPieces l = p :: ps ∧ ∀ t, t ≤ j → p[t]? = l[t]?
  | [], j, hj, _ => absurd hj (by simp)
  | i :: tl, j, hj, hs => by
      obtain ⟨p, ps, hp, hc⟩ := callPieces_cons i tl
      by_cases hi : (LprogIsa.shadowCall? i.1).isSome = true
      · have hj0 : j = 0 := by
          rcases Nat.eq_zero_or_pos j with h | h
          · exact h
          · exact absurd hi (hs 0 h)
        subst hj0
        refine ⟨[i], p :: ps, by rw [hc, ite_eq_left hi], fun t ht => ?_⟩
        rw [Nat.le_zero.mp ht]
        rfl
      · refine ⟨i :: p, ps, by rw [hc, ite_eq_right hi], fun t ht => ?_⟩
        cases t with
        | zero => rfl
        | succ t =>
            simp only [List.getElem?_cons_succ]
            have hj1 : j - 1 < tl.length := by simp at hj; omega
            obtain ⟨p', ps', hp', hm⟩ := callPieces_head tl (j - 1) hj1
              (fun m hm => by
                have := hs (m + 1) (by omega)
                simpa using this)
            rw [hp] at hp'
            obtain ⟨rfl, rfl⟩ := List.cons.inj hp'
            exact hm t (by omega)

/-- **A later piece**: the instructions after a shadow instruction, up to the next one,
    form a piece other than the first. -/
theorem callPieces_tail : ∀ (l : List LinstrRM) (k j : Nat) (hk : 0 < k) (hkl : k ≤ l.length),
    IsShadow (l[k - 1]'(by omega)) → k ≤ j → ∀ (hj : j < l.length),
    (∀ m (h : m < j), k ≤ m → ¬ IsShadow (l[m]'(by omega))) →
    ∃ P ∈ (callPieces l).tail, ∀ t, t ≤ j - k → P[t]? = l[k + t]?
  | [], _, _, _, hkl, _, _, hj, _ => absurd hj (by simp)
  | i :: tl, k, j, hk, hkl, hsh, hkj, hj, hs => by
      obtain ⟨p, ps, hp, hc⟩ := callPieces_cons i tl
      by_cases hk1 : k = 1
      · subst hk1
        have hi : (LprogIsa.shadowCall? i.1).isSome = true := by simpa [IsShadow] using hsh
        have hj1 : j - 1 < tl.length := by simp at hj; omega
        obtain ⟨p', ps', hp', hm⟩ := callPieces_head tl (j - 1) hj1
          (fun m hm => by
            have := hs (m + 1) (by omega) (by omega)
            simpa using this)
        refine ⟨p', ?_, fun t ht => ?_⟩
        · rw [hp] at hp'
          obtain ⟨rfl, rfl⟩ := List.cons.inj hp'
          rw [hc, ite_eq_left hi, List.tail_cons]
          exact List.mem_cons_self
        · rw [Nat.add_comm, List.getElem?_cons_succ]
          exact hm t (by omega)
      · have hsh' : IsShadow (tl[k - 1 - 1]'(by simp at hkl; omega)) := by
          have e : (i :: tl)[k - 1]'(by omega) = tl[k - 1 - 1]'(by simp at hkl; omega) := by
            rw [List.getElem_cons]
            split
            · omega
            · rfl
          rw [← e]
          exact hsh
        obtain ⟨P, hP, hm⟩ := callPieces_tail tl (k - 1) (j - 1) (by omega)
          (by simp at hkl; omega) hsh' (by omega) (by simp at hj; omega)
          (fun m hm hkm => by
            have := hs (m + 1) (by omega) (by omega)
            simpa using this)
        refine ⟨P, ?_, fun t ht => ?_⟩
        · rw [hp] at hP
          by_cases hi : (LprogIsa.shadowCall? i.1).isSome = true
          · rw [hc, ite_eq_left hi, List.tail_cons]
            exact List.mem_cons_of_mem _ hP
          · rw [hc, ite_eq_right hi, List.tail_cons]
            exact hP
        · rw [hm t (by omega), show k + t = (k - 1 + t) + 1 by omega, List.getElem?_cons_succ]

/-! ## 2. Names read before they are written -/

/-- The step of `regExposed`. -/
private def expStep (acc : List String × List String) (i : LinstrR) :
    List String × List String :=
  (acc.1 ++ ((regReads i).filter fun x => !acc.2.contains x && !acc.1.contains x).eraseDups,
    acc.2 ++ regWrites i)

private theorem regExposed_eq (is : List LinstrR) :
    regExposed is = (is.foldl expStep ([], [])).1 := rfl

private theorem foldl_expStep_mono : ∀ (is : List LinstrR) (acc : List String × List String)
    {y : String}, y ∈ acc.1 → y ∈ (is.foldl expStep acc).1
  | [], _, _, h => h
  | i :: is, acc, y, h => foldl_expStep_mono is _ (by simp [expStep, h])

private theorem foldl_expStep_mem : ∀ (is : List LinstrR) (acc : List String × List String)
    {y : String} (t : Nat) (ht : t < is.length), y ∈ regReads is[t] →
    (∀ m (h : m < t), y ∉ regWrites (is[m]'(by omega))) → y ∉ acc.2 →
    y ∈ (is.foldl expStep acc).1
  | [], _, _, _, ht, _, _, _ => absurd ht (by simp)
  | i :: is, acc, y, t, ht, hr, hw, ha => by
      simp only [List.foldl_cons]
      cases t with
      | zero =>
          refine foldl_expStep_mono is _ ?_
          by_cases hy : y ∈ acc.1
          · simp [expStep, hy]
          · simp only [expStep, List.mem_append, List.mem_eraseDups, List.mem_filter,
              Bool.and_eq_true, Bool.not_eq_true']
            exact Or.inr ⟨by simpa using hr, by simpa using ha, by simpa using hy⟩
      | succ t =>
          refine foldl_expStep_mem is _ t (by simp at ht; omega) (by simpa using hr)
            (fun m hm => by simpa using hw (m + 1) (by omega)) ?_
          simp only [expStep, List.mem_append, not_or]
          exact ⟨ha, by simpa using hw 0 (by omega)⟩

/-- **A name read before it is written is a name of `regExposed`.** -/
theorem mem_regExposed {is : List LinstrR} {y : String} (t : Nat) (ht : t < is.length)
    (hr : y ∈ regReads is[t]) (hw : ∀ m (h : m < t), y ∉ regWrites (is[m]'(by omega))) :
    y ∈ regExposed is := by
  rw [regExposed_eq]
  exact foldl_expStep_mem is _ t ht hr hw (by simp)

/-! ## 3. Blocks and the starts of pieces -/

section Blocks

variable {B : List LinstrRM} {G : CFG}

/-- **The start of a piece** of `callPieces` of a block of the graph `G` of `B`: the start of
    a block, or the position after a shadow instruction of a call. -/
def PieceStart (B : List LinstrRM) (G : CFG) (k : Nat) : Prop :=
  (∃ b, b < G.blocks.size ∧ (G.blk b).start = k) ∨
    ∃ p i, k = p + 1 ∧ B[p]? = some i ∧ IsShadow i

/-- **A name read before it is written from the position `k` on**, within the piece of `k`:
    the instruction at some `j ≥ k` reads it as a register, no instruction at a position from
    `k` to before `j` writes it as a register, and no piece starts after `k` up to `j`. -/
def Exposed (B : List LinstrRM) (G : CFG) (k : Nat) (y : String) : Prop :=
  ∃ j i, k ≤ j ∧ B[j]? = some i ∧ y ∈ regReads i.1 ∧
    (∀ m, k < m → m ≤ j → ¬ PieceStart B G m) ∧
    ∀ m i', k ≤ m → m < j → B[m]? = some i' → y ∉ regWrites i'.1

/-- Every position of the body lies in a block of its graph. -/
theorem exists_block (hG : cfgOf (B.map Prod.fst) = some G) {pc : Nat} (h : pc < B.length) :
    ∃ b, b < G.blocks.size ∧ (G.blk b).start ≤ pc ∧ pc < (G.blk b).stop := by
  have hw := cfgOf_wf hG
  simp only [wf, blockOfOk, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, List.size_toArray, List.length_map] at hw
  obtain ⟨⟨⟨⟨-, -⟩, -, hb⟩, -⟩, -⟩ := hw
  exact ⟨_, (hb pc h).1.1, (hb pc h).1.2, (hb pc h).2⟩

/-- The position where a block ends is the start of the next block, or the end of the
    body. -/
theorem stop_eq_start_succ (hG : cfgOf (B.map Prod.fst) = some G) {b : Nat}
    (hb : b < G.blocks.size) (hs : (G.blk b).stop < B.length) :
    b + 1 < G.blocks.size ∧ (G.blk (b + 1)).start = (G.blk b).stop := by
  have hf := (blockFacts hG hb).stop_eq
  simp only [CFG.nextStart, CFG.next, List.length_map] at hf
  split at hf
  · rename_i k' hk
    split at hk
    · rename_i h1
      cases hk
      exact ⟨h1, hf.symm⟩
    · cases hk
  · rename_i hk
    split at hk
    · cases hk
    · omega

/-- The instructions of block `b` of `B`, as `crossNames` reads them. -/
def blockInstrs (B : List LinstrRM) (G : CFG) (b : Nat) : List LinstrRM :=
  (B.drop (G.blk b).start).take ((G.blk b).stop - (G.blk b).start)

theorem blockInstrs_getElem? {b x : Nat} (hx : x < (G.blk b).stop - (G.blk b).start) :
    (blockInstrs B G b)[x]? = B[(G.blk b).start + x]? := by
  simp [blockInstrs, hx, List.getElem?_drop]

/-- **The piece of the block from a start of a piece**: from a position `k` of the block `b`
    that is the start of the block or follows a shadow instruction of the block, up to a
    position `j` of the block with no shadow instruction from `k` to before `j`, the
    instructions are those of a piece of `callPieces` of the block. -/
theorem piece_of_block (hG : cfgOf (B.map Prod.fst) = some G) {b k j : Nat}
    (hb : b < G.blocks.size) (hks : (G.blk b).start ≤ k) (hkj : k ≤ j)
    (hjs : j < (G.blk b).stop)
    (hk : k = (G.blk b).start ∨ ∃ i, B[k - 1]? = some i ∧ IsShadow i ∧ (G.blk b).start < k)
    (hsh : ∀ m i, k ≤ m → m < j → B[m]? = some i → ¬ IsShadow i) :
    ∃ P ∈ callPieces (blockInstrs B G b), ∀ t, t ≤ j - k → P[t]? = B[k + t]? := by
  have hle := (blockFacts hG hb).le
  simp only [List.length_map] at hle
  set s := (G.blk b).start with hs
  set l := blockInstrs B G b with hl
  have hlen : l.length = (G.blk b).stop - s := by
    simp only [hl, blockInstrs, List.length_take, List.length_drop]
    omega
  have hget : ∀ x (h : x < l.length), l[x] = B[s + x]'(by omega) := by
    intro x h
    have e := blockInstrs_getElem? (B := B) (G := G) (b := b) (x := x) (by omega)
    rw [← hl, List.getElem?_eq_getElem h, List.getElem?_eq_getElem (by omega)] at e
    exact Option.some.inj e
  have hns : ∀ m (h : m < j - s), k - s ≤ m → ¬ IsShadow (l[m]'(by omega)) := by
    intro m hm hkm
    rw [hget m (by omega)]
    exact hsh (s + m) _ (by omega) (by omega) (List.getElem?_eq_getElem _)
  rcases hk with hk | ⟨i, hi, hish, hlt⟩
  · obtain ⟨p, ps, hcp, hm⟩ := callPieces_head l (j - s) (by omega)
      (fun m hm => hns m hm (by omega))
    refine ⟨p, by rw [hcp]; exact List.mem_cons_self, fun t ht => ?_⟩
    rw [hm t (by omega), blockInstrs_getElem? (by omega), hk]
  · obtain ⟨P, hP, hm⟩ := callPieces_tail l (k - s) (j - s) (by omega) (by omega)
      (by
        rw [hget _ (by omega)]
        have e : B[s + (k - s - 1)]? = some i := by
          rw [show s + (k - s - 1) = k - 1 by omega]; exact hi
        rw [List.getElem?_eq_getElem (by omega)] at e
        rw [Option.some.inj e]
        exact hish)
      (by omega) (by omega) (fun m hm hkm => hns m hm hkm)
    refine ⟨P, List.mem_of_mem_tail hP, fun t ht => ?_⟩
    rw [hm t (by omega), blockInstrs_getElem? (by omega),
      show s + (k - s + t) = k + t by omega]

/-- **A name read before it is written from the start of a piece is a name of
    `crossNames`.** -/
theorem mem_crossNames_of_exposed (hG : cfgOf (B.map Prod.fst) = some G) {k : Nat}
    {y : String} (hk : PieceStart B G k) (he : Exposed B G k y) : y ∈ crossNames B := by
  obtain ⟨j, i, hkj, hj, hr, hnp, hw⟩ := he
  have hjl : j < B.length := (List.getElem?_eq_some_iff.mp hj).1
  -- no shadow instruction from `k` to before `j`
  have hsh : ∀ m i', k ≤ m → m < j → B[m]? = some i' → ¬ IsShadow i' :=
    fun m i' hkm hmj hm hs => hnp (m + 1) (by omega) (by omega) (Or.inr ⟨m, i', rfl, hm, hs⟩)
  -- `j` lies in the block whose start is a start of a piece at or before `k`
  have hblock : ∀ b, b < G.blocks.size → (G.blk b).start ≤ k → k < (G.blk b).stop →
      j < (G.blk b).stop := by
    intro b hb hbs hbk
    by_contra hc
    have hstop : (G.blk b).stop < B.length := by omega
    obtain ⟨hb1, he1⟩ := stop_eq_start_succ hG hb hstop
    have hlt := (blockFacts hG hb).lt
    exact hnp (G.blk b).stop hbk (by omega) (Or.inl ⟨b + 1, hb1, he1⟩)
  have hfin : ∀ b, b < G.blocks.size → (G.blk b).start ≤ k → k ≤ j → j < (G.blk b).stop →
      (k = (G.blk b).start ∨ ∃ i, B[k - 1]? = some i ∧ IsShadow i ∧ (G.blk b).start < k) →
      y ∈ crossNames B := by
    intro b hb hbs hkj' hjs hk'
    obtain ⟨P, hP, hm⟩ := piece_of_block hG hb hbs hkj' hjs hk' hsh
    have hPj : P[j - k]? = some i := by rw [hm _ le_rfl, show k + (j - k) = j by omega]; exact hj
    have hlen : j - k < P.length := (List.getElem?_eq_some_iff.mp hPj).1
    have hexp : y ∈ regExposed (P.map Prod.fst) := by
      refine mem_regExposed (j - k) (by simpa using hlen) ?_ (fun m hmt => ?_)
      · rw [List.getElem_map]
        rw [List.getElem?_eq_getElem hlen, Option.some_inj] at hPj
        rw [hPj]
        exact hr
      · rw [List.getElem_map]
        have hm' := hm m (by omega)
        rw [List.getElem?_eq_getElem (by omega)] at hm'
        exact hw (k + m) _ (by omega) (by omega) hm'.symm
    unfold crossNames
    rw [hG]
    simp only [List.mem_eraseDups, List.mem_flatMap, List.mem_range]
    exact ⟨b, hb, P, hP, hexp⟩
  rcases hk with ⟨b, hb, hbk⟩ | ⟨p, ip, rfl, hp, hps⟩
  · have hlt := (blockFacts hG hb).lt
    exact hfin b hb (by omega) hkj (hblock b hb (by omega) (by omega)) (Or.inl hbk.symm)
  · have hpl : p < B.length := (List.getElem?_eq_some_iff.mp hp).1
    obtain ⟨b, hb, hbs, hbp⟩ := exists_block hG hpl
    rcases Nat.lt_or_ge (p + 1) (G.blk b).stop with h | h
    · exact hfin b hb (by omega) hkj (hblock b hb (by omega) (by omega))
        (Or.inr ⟨ip, by simpa using hp, hps, by omega⟩)
    · have hstop : (G.blk b).stop < B.length := by omega
      obtain ⟨hb1, he1⟩ := stop_eq_start_succ hG hb hstop
      have hlt := (blockFacts hG hb1).lt
      exact hfin (b + 1) hb1 (by omega) hkj (hblock (b + 1) hb1 (by omega) (by omega))
        (Or.inl (by omega))

end Blocks

/-! ## 4. The names of the liveness table -/

/-- **The reads of an instruction are registers or its array**: a name of an operand of the
    sources is read as a register (`regReads`) or is the array the instruction reads
    (`arrUse?`). It fails at an indexed operand outside a load and a store. -/
def ReadCover (i : LinstrRM) : Prop :=
  ∀ y ∈ useNames i.1, y ∈ regReads i.1 ∨ arrUse? i = some y

/-- **The register destinations of an instruction are killed, read or its array**: a
    register destination (`regWrites`) is a name of `regDefs`, a name the instruction reads as
    a register, or the array it writes (`arrDefs`). It fails at a compare whose destination
    is no source. -/
def WriteCover (i : LinstrRM) : Prop :=
  ∀ y ∈ regWrites i.1, y ∈ regDefs i ∨ y ∈ regReads i.1 ∨ y ∈ arrDefs i

section Live

variable {B : List LinstrRM} {G : CFG} {outs : List String}

theorem mem_arrNames_of_use {i : LinstrRM} (hi : i ∈ B) {y : String} (h : arrUse? i = some y) :
    y ∈ arrNames B := by
  simp only [arrNames, List.mem_eraseDups, List.mem_flatMap, List.mem_append,
    Option.mem_toList]
  exact ⟨i, hi, Or.inl h⟩

theorem mem_arrNames_of_def {i : LinstrRM} (hi : i ∈ B) {y : String} (h : y ∈ arrDefs i) :
    y ∈ arrNames B := by
  simp only [arrNames, List.mem_eraseDups, List.mem_flatMap, List.mem_append]
  exact ⟨i, hi, Or.inr h⟩

/-- The target of a jump of the body is the start of a block. -/
theorem pieceStart_of_jump (hG : cfgOf (B.map Prod.fst) = some G) {k : Nat} {i : LinstrRM}
    (hi : B[k]? = some i) {l : LLabel} (hl : jumpLabel? i.1 = some l) {p : Nat}
    (hp : findLabelMem l B = some p) : PieceStart B G p := by
  have hkl : k < B.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨b, hb, hbs, hbk⟩ := exists_block hG hkl
  have hf := blockFacts hG hb
  have hterm : isTermR i.1 = true := by
    revert hl
    cases i.1 <;> simp [jumpLabel?, isTermR]
  have hlast : k + 1 = (G.blk b).stop := by
    by_contra hc
    have := hf.inner k i.1 hbs (by omega) (by simp [hi])
    rw [hterm] at this
    exact Bool.noConfusion this
  have hT := hf.term
  rw [show (G.blk b).stop - 1 = k by omega, List.getElem?_map, hi, Option.map_some] at hT
  rcases termOk_spec hT with ⟨nx, -, hnt, -⟩ | ⟨t, x, l', -, hx, ht, hfl⟩ |
      ⟨t, nx, c, l', -, hx, ht, hfl, -⟩ | ⟨-, hx⟩
  · rw [hterm] at hnt
    exact Bool.noConfusion hnt
  · rw [hx] at hl
    simp only [jumpLabel?, Option.some.injEq] at hl
    subst hl
    unfold findLabelMem at hp
    rw [hp] at hfl
    exact Or.inl ⟨t, ht, (Option.some.inj hfl).symm⟩
  · rw [hx] at hl
    simp only [jumpLabel?, Option.some.injEq] at hl
    subst hl
    unfold findLabelMem at hp
    rw [hp] at hfl
    exact Or.inl ⟨t, ht, (Option.some.inj hfl).symm⟩
  · rw [hx] at hl
    simp [jumpLabel?] at hl

/-- **The live names of a body**: a name live at a position is a name read after the body,
    an array name of the body, a name of `crossNames`, or a name read before it is written
    from that position on within its piece. -/
theorem pLiveR_cases (hG : cfgOf (B.map Prod.fst) = some G) (hR : ∀ i ∈ B, ReadCover i)
    (hW : ∀ i ∈ B, WriteCover i) {k : Nat} {y : String} (h : PLiveR B outs k y) :
    y ∈ outs ∨ y ∈ arrNames B ∨ y ∈ crossNames B ∨ Exposed B G k y := by
  induction h with
  | @read k i y hi hy =>
      have hmem : i ∈ B := List.mem_of_getElem? hi
      rcases hR i hmem y hy with h | h
      · exact Or.inr (Or.inr (Or.inr ⟨k, i, le_rfl, hi, h, fun m h1 h2 => by omega,
          fun m _ h1 h2 => by omega⟩))
      · exact Or.inr (Or.inl (mem_arrNames_of_use hmem h))
  | @next k i y hi hg hd _ ih =>
      have hmem : i ∈ B := List.mem_of_getElem? hi
      rcases ih with h | h | h | ⟨j, i', hkj, hj, hr, hnp, hw⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      by_cases hps : PieceStart B G (k + 1)
      · exact Or.inr (Or.inr (Or.inl (mem_crossNames_of_exposed hG hps
          ⟨j, i', hkj, hj, hr, hnp, hw⟩)))
      by_cases hwk : y ∈ regWrites i.1
      · rcases hW i hmem y hwk with hd' | hr' | ha
        · exfalso
          obtain ⟨w, tag⟩ := i
          cases w with
          | Lopn ds o ss => exact hd ds o ss rfl hd'
          | _ => simp [regWrites] at hwk
        · exact Or.inr (Or.inr (Or.inr ⟨k, i, le_rfl, hi, hr', fun m h1 h2 => by omega,
            fun m _ h1 h2 => by omega⟩))
        · exact Or.inr (Or.inl (mem_arrNames_of_def hmem ha))
      · refine Or.inr (Or.inr (Or.inr ⟨j, i', by omega, hj, hr, fun m h1 h2 => ?_,
          fun m i'' h1 h2 hm => ?_⟩))
        · rcases Nat.lt_or_ge (k + 1) m with h3 | h3
          · exact hnp m h3 h2
          · rw [show m = k + 1 by omega]
            exact hps
        · rcases Nat.lt_or_ge k m with h3 | h3
          · exact hw m i'' (by omega) h2 hm
          · rw [show m = k by omega, hi] at hm
            cases hm
            exact hwk
  | @jump k i l p y hi hl hp _ ih =>
      rcases ih with h | h | h | ⟨j, i', hkj, hj, hr, hnp, hw⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      by_cases hps : PieceStart B G (p + 1)
      · exact Or.inr (Or.inr (Or.inl (mem_crossNames_of_exposed hG hps
          ⟨j, i', hkj, hj, hr, hnp, hw⟩)))
      have hp0 := pieceStart_of_jump hG hi hl hp
      have hlab : ∀ i'', B[p]? = some i'' → regWrites i''.1 = [] := by
        intro i'' hi''
        unfold findLabelMem at hp
        obtain ⟨w, hw', hlw⟩ := JasminLsemLabeled.findLabel_sound l _ p hp
        rw [List.getElem?_map, hi'', Option.map_some, Option.some.injEq] at hw'
        rw [hw']
        revert hlw
        cases w <;> simp [JasminLsemLabeled.isLabel, regWrites]
      refine Or.inr (Or.inr (Or.inl (mem_crossNames_of_exposed hG hp0
        ⟨j, i', by omega, hj, hr, fun m h1 h2 => ?_, fun m i'' h1 h2 hm => ?_⟩)))
      · rcases Nat.lt_or_ge (p + 1) m with h3 | h3
        · exact hnp m h3 h2
        · rw [show m = p + 1 by omega]
          exact hps
      · rcases Nat.lt_or_ge p m with h3 | h3
        · exact hw m i'' (by omega) h2 hm
        · rw [show m = p by omega] at hm
          rw [hlab i'' hm]
          simp
  | @out y hy => exact Or.inl hy

/-- **At the start of a piece, a name of the liveness table is a name read after the body,
    an array name or a name of `crossNames`**, for a body whose instructions meet `ReadCover`
    and `WriteCover`. The entries of the segments of a calling body are such starts: the
    entry of the body and the position after each shadow instruction of a call. -/
theorem mem_crossNames_of_liveRegTab (hG : cfgOf (B.map Prod.fst) = some G)
    (hR : ∀ i ∈ B, ReadCover i) (hW : ∀ i ∈ B, WriteCover i) {k : Nat} (hk : PieceStart B G k)
    {y : String} (hy : y ∈ tabAt (liveRegTab B outs) k) :
    y ∈ outs ∨ y ∈ arrNames B ∨ y ∈ crossNames B := by
  rcases pLiveR_cases hG hR hW (mem_liveRegTab_iff.mp hy) with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inr (mem_crossNames_of_exposed hG hk h))

/-- **The names of the liveness table of a renamed body**: at the start of a piece of `L`, a
    name of the liveness table of `L` renamed by `τ`, with the names `O` read after it, is the
    image under `τ` of a name of `O0`, of an array name of `L` or of a name of
    `crossNames L`, when every name of `O` is the image of a name of `O0`. -/
theorem mem_crossNames_of_liveRegTab_ren {L : List LinstrRM} {τ : String → String}
    {O O0 : List String} (hO : ∀ z ∈ O, ∃ z0 ∈ O0, τ z0 = z)
    (hG : cfgOf (L.map Prod.fst) = some G) (hR : ∀ i ∈ L, ReadCover i)
    (hW : ∀ i ∈ L, WriteCover i) {k : Nat} (hk : PieceStart L G k) {y : String}
    (hy : y ∈ tabAt (liveRegTab (L.map (JasminLsemExportTransfer.renRM τ)) O) k) :
    ∃ z, τ z = y ∧ (z ∈ O0 ∨ z ∈ arrNames L ∨ z ∈ crossNames L) := by
  obtain ⟨z, hz, hl⟩ := RegionAllocMapPins.pLiveR_renRM hO (mem_liveRegTab_iff.mp hy)
  exact ⟨z, hz, mem_crossNames_of_liveRegTab hG hR hW hk (mem_liveRegTab_iff.mpr hl)⟩

end Live

/-! ## 4. The entry sets of the liveness table bound the live sets of the segments

On a reference of the shape `RefShape` (the export shape `CoShape`, or a widening multiply
after a write of its implicit source), the liveness table `liveRegTab B outs`, extended at
each widening multiply by its implicit source `mulxSrc` (`liveTabX`), is closed along the
body (`tabClosed_liveTabX`): the symbolic step reads within the names the instruction reads
and writes within `regDefs` (`SymFootprint.symStep_readsIn`,
`SymFootprint.symStep_readsIn_mulx`), which is the transfer of the table. The extension is
empty at the entries of the segments, so along the cut programs the table at the entry of a
segment is the entry set `insTab B outs e`, and the observed names of an exit are names of
the table at the exit (`segOutsAt_sub`). Hence the live names the checker finds at the entry
of a segment lie in `insTab B outs e` (`entry_live_sub_insTab`), and the entry inclusion of
`ownedCheckMCIn` adds no refusal at `insTab` (`ownedCheckMCIn_insTab`,
`calleeSegB_insTab_iff`). -/

section Entry

open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVChecked (ownedCheckMCIn runsOfC
  startC CFact)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegComplete
open CatCrypt.Crypto.SecureCompilation.X86Backend.SymFootprint (OneDst MulxShape)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard (wideArgs? mulxSrc)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogCallCut (cutAt stopPos entryPos sites)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLabeled (isLabel)
open CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSegCheck (segOutsAt shadowAt regsOf
  calleeSegB siteMap)

variable {B : List LinstrRM} {outs : List String}

private theorem mem_defNames_of_mem_regDefs (i : LinstrRM) :
    ∀ y ∈ regDefs i, y ∈ JasminLsemExportRegAlloc.defNames i.1 := by
  intro y hy
  unfold regDefs JasminLsemExportRegAlloc.memRegDefs at hy
  split_ifs at hy <;> simp_all

theorem shadowCall?_eq_some {w : LinstrR} {dst f : String} {srcs : List LOperand}
    (h : LprogIsa.shadowCall? w = some (dst, f, srcs)) :
    ∃ opn, w = .Lopn [.reg dst] opn srcs := by
  unfold LprogIsa.shadowCall? at h
  split at h
  · split at h
    · cases h
      exact ⟨_, rfl⟩
    · cases h
  · cases h

theorem mem_opNames_of_regName {o : LOperand} {y : String} (h : o.regName? = some y) :
    y ∈ JasminLsemExportRewrites.opNames o := by
  cases o <;> simp_all [LOperand.regName?, JasminLsemExportRewrites.opNames]

/-- **The shape of the instruction `i` at position `q` of a reference `B`**: a conditional
    jump on the zero flag, and an operation with one register destination or a widening
    multiply whose predecessor is no shadow instruction of a call and writes the implicit
    source `mulxSrc`. -/
def RefShape (B : List LinstrRM) (q : Nat) (i : LinstrRM) : Prop :=
  (∀ c l, i.1 = .Lcond c l → c = .reg "Z" ∨ c = .reg "NZ") ∧
    (OneDst i ∨ ∃ lo hi b, MulxShape i lo hi b ∧
      ∃ p i', q = p + 1 ∧ B[p]? = some i' ∧ LprogIsa.shadowCall? i'.1 = none ∧
        mulxSrc ∈ regDefs i')

/-- An instruction of the export shape has the shape of a reference at every position. -/
theorem refShape_of_coShape {q : Nat} {i : LinstrRM} (h : CoShape i) : RefShape B q i :=
  ⟨h.2.1, Or.inl h.2.2⟩

/-- An instruction with a successful symbolic step is no unconditional jump. -/
theorem not_goto_of_symStep {i : LinstrRM} {ss s : SSt} {gs : List SG}
    (h : symStep i ss = .ok s gs) : ∀ x, i.1 ≠ .Lgoto x := by
  intro x hx
  obtain ⟨w, tag⟩ := i
  simp only at hx
  subst hx
  simp [symStep, JasminLsemMemFlagGuard.cmpArgs?, JasminLsemMemFlagGuard.movRegArgs?,
    JasminLsemMemFlagGuard.flagCondCC?] at h

/-- The implicit source of a widening multiply. -/
def mulxReads (i : LinstrRM) : List String :=
  match wideArgs? i with
  | some (.mulx _ _ _) => [mulxSrc]
  | _ => []

theorem mulxReads_cases (i : LinstrRM) :
    mulxReads i = [] ∨ (∃ lo hi b, MulxShape i lo hi b) ∧ mulxReads i = [mulxSrc] := by
  unfold mulxReads
  split
  · rename_i lo hi b h
    exact Or.inr ⟨⟨lo, hi, b, X86Backend.SymFootprint.mulxShape_of_wideArgs h⟩, rfl⟩
  · exact Or.inl rfl

theorem mulxReads_oneDst {i : LinstrRM} (h : OneDst i) : mulxReads i = [] := by
  rcases mulxReads_cases i with h1 | ⟨⟨lo, hi, b, opn, he, -⟩, -⟩
  · exact h1
  · obtain ⟨x, hx⟩ := h _ _ _ he
    cases hx

theorem mulxReads_not_lopn {i : LinstrRM} (h : ∀ ds o ss, i.1 ≠ .Lopn ds o ss) :
    mulxReads i = [] := by
  rcases mulxReads_cases i with h1 | ⟨⟨lo, hi, b, opn, he, -⟩, -⟩
  · exact h1
  · exact absurd he (h _ _ _)

theorem regDefs_not_lopn {i : LinstrRM} (h : ∀ ds o ss, i.1 ≠ .Lopn ds o ss) :
    regDefs i = [] := by
  refine List.eq_nil_iff_forall_not_mem.mpr fun y hy => ?_
  have := mem_defNames_of_mem_regDefs i y hy
  obtain ⟨w, tag⟩ := i
  cases w <;> simp_all [JasminLsemExportRegAlloc.defNames]

/-- The liveness table of `B` with the implicit source of the widening multiply at each of
    its positions. -/
def liveTabX (B : List LinstrRM) (outs : List String) (q : Nat) : List String :=
  tabAt (liveRegTab B outs) q ++ ((B[q]?).map mulxReads).getD []

theorem mem_liveTabX {q : Nat} {y : String} :
    y ∈ liveTabX B outs q ↔
      y ∈ tabAt (liveRegTab B outs) q ∨ ∃ i, B[q]? = some i ∧ y ∈ mulxReads i := by
  unfold liveTabX
  cases B[q]? <;> simp

/-- **The names live at a label are live after it.** -/
theorem pLiveR_label {p : Nat} {j : LinstrRM} {l : LLabel} (hj : B[p]? = some j)
    (hl : isLabel l j.1 = true) {y : String} (h : PLiveR B outs p y) :
    PLiveR B outs (p + 1) y := by
  obtain ⟨w, tag⟩ := j
  cases w <;> simp only [isLabel, Bool.false_eq_true] at hl
  cases h with
  | read hi hy =>
      rw [hj, Option.some.injEq] at hi
      subst hi
      simp [useNames] at hy
  | next hi _ _ h' => exact h'
  | jump hi hl' _ _ =>
      rw [hj, Option.some.injEq] at hi
      subst hi
      simp [jumpLabel?] at hl'
  | out _ => simp at hj

/-- The predecessor of a widening multiply writes its implicit source. -/
theorem mulx_pred (hB : ∀ q i, B[q]? = some i → RefShape B q i) {q : Nat} {i : LinstrRM}
    (hi : B[q]? = some i) {y : String} (hy : y ∈ mulxReads i) :
    y = mulxSrc ∧ ∃ p i', q = p + 1 ∧ B[p]? = some i' ∧ LprogIsa.shadowCall? i'.1 = none ∧
      mulxSrc ∈ regDefs i' := by
  rcases (hB q i hi).2 with h1 | ⟨lo, hi', b, hm, hp⟩
  · rw [mulxReads_oneDst h1] at hy
    cases hy
  · rcases mulxReads_cases i with h2 | ⟨-, h2⟩
    · rw [h2] at hy; cases hy
    · rw [h2, List.mem_singleton] at hy
      exact ⟨hy, hp⟩

/-- **The liveness table, with the implicit sources of the widening multiplies, is closed
    along a reference of the shape `RefShape`.** -/
theorem tabClosed_liveTabX (hB : ∀ q i, B[q]? = some i → RefShape B q i) :
    TabClosed B outs (liveTabX B outs) := by
  -- a name of the table after a position that the instruction there does not write
  have hnext : ∀ q i r, B[q]? = some i → (∀ x, i.1 ≠ .Lgoto x) →
      r ∈ liveTabX B outs (q + 1) → r ∉ regDefs i →
      r ∈ tabAt (liveRegTab B outs) q ∨ r = mulxSrc := by
    intro q i r hi hg hr hd
    rcases mem_liveTabX.mp hr with hr | ⟨i1, hi1, hr⟩
    · exact Or.inl (mem_liveRegTab_iff.mpr
        (.next hi hg (fun _ _ _ _ => hd) (mem_liveRegTab_iff.mp hr)))
    · obtain ⟨rfl, p, i', hp, hi', -, hd'⟩ := mulx_pred hB hi1 hr
      exact Or.inr rfl
  refine ⟨fun q i hi E X ss s gs hs hX => ?_, fun q i l p hi hl hp y hy => ?_,
    fun q c l tag hi => ?_, fun y hy => ?_⟩
  · rcases (hB q i hi).2 with h1 | ⟨lo, hi', b, hm, -⟩
    · refine X86Backend.SymFootprint.symStep_readsIn h1 hs (hX.mono fun r hr => ?_)
      refine mem_liveTabX.mpr (Or.inl ?_)
      rcases hr with hr | ⟨hr1, hr2⟩
      · exact mem_liveRegTab_iff.mpr (.read hi hr)
      · rcases mem_liveTabX.mp hr1 with hr1 | ⟨i1, hi1, hr1⟩
        · exact mem_liveRegTab_iff.mpr
            (.next hi (not_goto_of_symStep hs) (fun _ _ _ _ => hr2)
              (mem_liveRegTab_iff.mp hr1))
        · obtain ⟨rfl, p, i', hp, hi', -, hd'⟩ := mulx_pred hB hi1 hr1
          obtain rfl : p = q := by omega
          rw [hi, Option.some.injEq] at hi'
          subst hi'
          exact absurd hd' hr2
    · have hmx : mulxSrc ∈ liveTabX B outs q := by
        refine mem_liveTabX.mpr (Or.inr ⟨i, hi, ?_⟩)
        rcases mulxReads_cases i with h2 | ⟨-, h2⟩
        · unfold mulxReads at h2
          obtain ⟨opn, he, ho⟩ := hm
          obtain ⟨w, tag⟩ := i
          simp only at he
          subst he
          simp [wideArgs?, ho] at h2
        · rw [h2]; exact List.mem_singleton_self _
      refine X86Backend.SymFootprint.symStep_readsIn_mulx hm hs (hX.mono fun r hr => ?_)
      rcases hr with hr | rfl | ⟨hr1, hr2⟩
      · exact mem_liveTabX.mpr (Or.inl (mem_liveRegTab_iff.mpr (.read hi hr)))
      · exact hmx
      · rcases hnext q i r hi (not_goto_of_symStep hs) hr1 hr2 with h3 | rfl
        · exact mem_liveTabX.mpr (Or.inl h3)
        · exact hmx
  · obtain ⟨k, hk, hkl⟩ := JasminLsemLabeled.findLabel_sound l _ p hp
    rw [List.getElem?_map] at hk
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp hk
    rcases mem_liveTabX.mp hy with hy | ⟨i1, hi1, hy⟩
    · exact mem_liveTabX.mpr (Or.inl (mem_liveRegTab_iff.mpr
        (.jump hi hl hp (pLiveR_label hj hkl (mem_liveRegTab_iff.mp hy)))))
    · rw [hj, Option.some.injEq] at hi1
      subst hi1
      rw [mulxReads_not_lopn fun ds o ss he => by rw [he] at hkl; simp [isLabel] at hkl] at hy
      cases hy
  · have hc := hB q _ hi
    refine ⟨?_, fun y hy => ?_⟩
    · rcases hc.1 c l rfl with rfl | rfl <;> rfl
    · rcases mem_liveTabX.mp hy with hy' | ⟨i1, hi1, hy'⟩
      · exact mem_liveTabX.mpr (Or.inl (mem_liveRegTab_iff.mpr (.next hi
          (fun _ e => by cases e) (fun _ _ _ e => by cases e) (mem_liveRegTab_iff.mp hy'))))
      · obtain ⟨-, p, i', hp, hi', -, hd'⟩ := mulx_pred hB hi1 hy'
        obtain rfl : p = q := by omega
        rw [hi, Option.some.injEq] at hi'
        subst hi'
        rw [regDefs_not_lopn (fun _ _ _ e => by cases e)] at hd'
        cases hd'
  · exact mem_liveTabX.mpr (Or.inl (mem_liveRegTab_iff.mpr (.out hy)))

/-- **The observed names of an exit are names of the liveness table at the exit**: the names
    read after the body at its end, and at a shadow instruction its register operands and the
    names of the table after it other than its destination. -/
theorem segOutsAt_sub {x : Option Nat} :
    ∀ y ∈ segOutsAt B (insTab B outs) outs x, y ∈ tabAt (liveRegTab B outs) (stopPos B x) := by
  intro y hy
  cases x with
  | none => exact mem_liveRegTab_iff.mpr (.out hy)
  | some p =>
      simp only [segOutsAt] at hy
      split at hy
      · rename_i dst f srcs hsh
        simp only [shadowAt] at hsh
        cases hi : B[p]? with
        | none => rw [hi] at hsh; cases hsh
        | some i =>
            rw [hi, Option.bind_some] at hsh
            obtain ⟨opn, he⟩ := shadowCall?_eq_some hsh
            rw [mem_liveRegTab_iff]
            simp only [List.mem_append, List.mem_filter, bne_iff_ne, ne_eq] at hy
            rcases hy with hy | ⟨hy1, hy2⟩
            · refine .read hi ?_
              rw [he]
              simp only [regsOf, List.mem_filterMap] at hy
              obtain ⟨o, ho, hoy⟩ := hy
              exact List.mem_flatMap.mpr ⟨o, ho, mem_opNames_of_regName hoy⟩
            · refine .next hi (fun z => by rw [he]; exact fun e => by cases e)
                (fun _ _ _ _ hd => hy2 ?_) (mem_liveRegTab_iff.mp hy1)
              have := mem_defNames_of_mem_regDefs i y hd
              rw [he] at this
              simpa [JasminLsemExportRegAlloc.defNames, JasminLsemExportRewrites.opNames]
                using this
      · simp at hy

/-- At the entry of a segment, the extended table is the liveness table. -/
theorem liveTabX_entry (hB : ∀ q i, B[q]? = some i → RefShape B q i) {e : Option Nat}
    (he : SiteOk B e) : ∀ y ∈ liveTabX B outs (entryPos e), y ∈ insTab B outs e := by
  intro y hy
  rcases mem_liveTabX.mp hy with hy | ⟨i, hi, hy⟩
  · exact hy
  · exfalso
    obtain ⟨-, p, i', hp, hi', hsh, -⟩ := mulx_pred hB hi hy
    cases e with
    | none => simp [entryPos] at hp
    | some p0 =>
        obtain rfl : p0 = p := by simpa [entryPos] using hp
        obtain ⟨i'', hi'', hsh'⟩ := he p0 rfl
        rw [hi', Option.some.injEq] at hi''
        subst hi''
        exact hsh' hsh

theorem tabClosed_cutAt_ref {fn : String} {fin : LLabel} {e x : Option Nat}
    (hB : ∀ q i, B[q]? = some i → RefShape B q i)
    (hfin : FinFree fin B)
    (huniq : LabelsOnce B)
    (he : SiteOk B e) (hx : SiteOk B x) :
    TabClosed (cutAt fn fin B e x) (segOutsAt B (insTab B outs) outs x)
      (cutTab B (liveTabX B outs) (segOutsAt B (insTab B outs) outs x) e) :=
  tabClosed_cutAt he hx hfin huniq (tabClosed_liveTabX hB)
    (fun y hy => mem_liveTabX.mpr (Or.inl (segOutsAt_sub y hy)))

/-- **The table along the cut positions is a post-fixpoint of `liveRound` on a cut
    program.** For a reference `B` of the shape `RefShape` with labels declared once and no
    use of the label `fin`, an entry `e` and an exit `x` that are the end of the body or
    shadow instructions of calls, the extended liveness table `liveTabX B outs` read along
    `cutBack B e`, at the starts of the blocks of the cut program and with the flags live,
    covers what every block needs given it, for shared runs whose image guards are among
    their reference guards at every block that does not return. -/
theorem livePost_cutAt {fn : String} {fin : LLabel} {e x : Option Nat}
    (hB : ∀ q i, B[q]? = some i → RefShape B q i) (hfin : FinFree fin B)
    (huniq : LabelsOnce B) (he : SiteOk B e) (hx : SiteOk B x) {C' : List LinstrRM}
    {G G' : CFG} (hG : cfgOf ((cutAt fn fin B e x).map Prod.fst) = some G)
    {F F' : Nat → List CFact}
    (hgd : ∀ k r, (runsOfC F F' (cutAt fn fin B e x) C' G G' symStep)[k]? = some r →
      (G.blk k).term ≠ .ret → GuardsIn r) :
    LivePost (segOutsAt B (insTab B outs) outs x) (cutAt fn fin B e x) G
      (runsOfC F F' (cutAt fn fin B e x) C' G G' symStep)
      (tabLive G (cutTab B (liveTabX B outs) (segOutsAt B (insTab B outs) outs x) e)) :=
  livePost_tab hG (tabClosed_cutAt_ref hB hfin huniq he hx) hgd

/-- **The live names at the entry of a cut program lie in the entry set of the liveness
    table.** For a reference `B` of the shape `RefShape` with labels declared once and no use
    of the label `fin`, an entry `e` and an exit `x` that are the end of the body or shadow
    instructions of calls, and the observed names `segOutsAt B (insTab B outs) outs x`, the
    names that the live-set iteration of the checker finds live at the entry of the cut
    program `cutAt fn fin B e x` are names of `insTab B outs e`. The image enters through one
    assumption, `hgd`: at every block that does not return, the normalised image guards are
    among the normalised reference guards. -/
theorem entry_live_sub_insTab {fn : String} {fin : LLabel} {e x : Option Nat}
    (hB : ∀ q i, B[q]? = some i → RefShape B q i)
    (hfin : FinFree fin B)
    (huniq : LabelsOnce B)
    (he : SiteOk B e) (hx : SiteOk B x) {C' : List LinstrRM} {G G' : CFG}
    (hG : cfgOf ((cutAt fn fin B e x).map Prod.fst) = some G) {F F' : Nat → List CFact}
    (hgd : ∀ k r, (runsOfC F F' (cutAt fn fin B e x) C' G G' symStep)[k]? = some r →
      (G.blk k).term ≠ .ret → GuardsIn r) (n : Nat) :
    ∀ v ∈ ((liveIter (segOutsAt B (insTab B outs) outs x) (cutAt fn fin B e x) G
      (runsOfC F F' (cutAt fn fin B e x) C' G G' symStep) n
      (Array.replicate G.blocks.size ([], false))).getD 0 ([], false)).1,
        v ∈ insTab B outs e := by
  intro v hv
  have hne : cutAt fn fin B e x ≠ [] := by
    intro h0
    have := cutAt_length fn fin B x he
    rw [h0] at this
    simp at this
  have := liveIter_entry_sub hG hne (tabClosed_cutAt_ref hB hfin huniq he hx) hgd n v hv
  unfold cutTab at this
  rw [ite_eq_left (Nat.zero_le _), cutBack_zero B he] at this
  exact liveTabX_entry hB he v this

/-- **The entry inclusion adds no refusal at the entry sets of the liveness table.** Under
    the hypotheses of `entry_live_sub_insTab` on `B`, a cut program pair that
    `ownedCheckMCIn` accepts at some entry set is accepted at `insTab B outs e`. -/
theorem ownedCheckMCIn_insTab {fn : String} {fin : LLabel} {e x : Option Nat}
    {ins : List String} {C' : List LinstrRM} (hB : ∀ q i, B[q]? = some i → RefShape B q i)
    (hfin : FinFree fin B)
    (huniq : LabelsOnce B)
    (he : SiteOk B e) (hx : SiteOk B x)
    (h : ownedCheckMCIn ins (segOutsAt B (insTab B outs) outs x) (cutAt fn fin B e x) C' =
      true) :
    ownedCheckMCIn (insTab B outs e) (segOutsAt B (insTab B outs) outs x)
      (cutAt fn fin B e x) C' = true := by
  refine ownedCheckMCIn_of_tab (tabClosed_cutAt_ref hB hfin huniq he hx) (fun v hv => ?_) h
  unfold cutTab at hv
  rw [ite_eq_left (Nat.zero_le _), cutBack_zero B he] at hv
  exact liveTabX_entry hB he v hv

theorem siteOk_of_mem {T : LprogIsa.ProcTable} {e : Option Nat}
    (h : e ∈ none :: (sites T B).map some) : SiteOk B e := by
  intro p hp
  subst hp
  simp only [List.mem_cons, reduceCtorEq, List.mem_map, Option.some.injEq, exists_eq_right,
    false_or, sites, List.mem_filter, List.mem_range] at h
  obtain ⟨hp, hany⟩ := h
  rw [List.getElem?_eq_getElem hp] at hany ⊢
  refine ⟨_, rfl, fun hn => ?_⟩
  simp [LprogCallCut.isProcB, LprogIsa.procCall?, hn] at hany

/-- **The checks of the segments at the entry sets of the liveness table are the checks
    with the entry inclusion removed.** For a reference `ref` of the shape `RefShape` with
    labels declared once and no use of the label `fin`, `calleeSegB` at `insTab ref outs`
    holds exactly when its two conditions on the shadow instructions hold and every cut
    program pair is accepted by `ownedCheckMCIn` at some entry set, with the observed names
    of `insTab ref outs`. -/
theorem calleeSegB_insTab_iff {T : LprogIsa.ProcTable} {fn : String} {fin : LLabel}
    {ref img : List LinstrRM} (hB : ∀ q i, ref[q]? = some i → RefShape ref q i)
    (hfin : FinFree fin ref)
    (huniq : LabelsOnce ref) :
    calleeSegB T fn fin (insTab ref outs) outs ref img = true ↔
      ((sites T ref).map (shadowAt ref) == (sites T img).map (shadowAt img) &&
        (sites T ref).all (fun p =>
          (shadowAt ref p).all fun q => q.2.2 == (regsOf q.2.2).map LOperand.reg)) = true ∧
      ∀ e ∈ none :: (sites T ref).map some, ∀ x ∈ none :: (sites T ref).map some,
        ∃ ins, ownedCheckMCIn ins (segOutsAt ref (insTab ref outs) outs x)
          (cutAt fn fin ref e x)
          (cutAt fn fin img (siteMap T ref img e) (siteMap T ref img x)) = true := by
  unfold calleeSegB
  simp only [Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun e he x hx => ⟨_, h2 e he x hx⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun e he x hx => ?_⟩
    obtain ⟨ins, hi⟩ := h2 e he x hx
    exact ownedCheckMCIn_insTab hB hfin huniq (siteOk_of_mem he) (siteOk_of_mem hx) hi

/-- The label `freshLabel A` is neither declared nor named by a jump in a body `B` of
    instructions of `A` whose jumps name labels declared in `B`. -/
theorem freshLabel_free {A : List LinstrRM} (hsub : ∀ i ∈ B, i ∈ A)
    (hdecl : ∀ i ∈ B, ∀ l, jumpLabel? i.1 = some l → ∃ j ∈ B, isLabel l j.1 = true) :
    FinFree (freshLabel A) B := by
  intro i hi
  refine ⟨?_, fun hj => ?_⟩
  · cases hl : isLabel (freshLabel A) i.1 with
    | false => rfl
    | true => exact absurd (lt_freshLabel (hsub i hi) hl) (lt_irrefl _)
  · obtain ⟨j, hj, hl⟩ := hdecl i hi _ hj
    exact absurd (lt_freshLabel (hsub j hj) hl) (lt_irrefl _)

end Entry

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionCalleeNames
