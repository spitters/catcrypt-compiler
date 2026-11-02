/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionAllocMapPins

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

## Main definitions

* `PieceStart`: the start of a block or the position after a shadow instruction of a call.
* `ReadCover`, `WriteCover`: the conditions on the instructions.

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

end CatCrypt.Crypto.SecureCompilation.Haxc.RegionCalleeNames
