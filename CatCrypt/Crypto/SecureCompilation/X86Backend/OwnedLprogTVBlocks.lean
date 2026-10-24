/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTVDeadImm

/-!
# Completeness of the value checker for bodies with several blocks

`OwnedLprogTVComplete` and `OwnedLprogTVDeadImm` prove that `OwnedLprogTV.ownedCheckM` accepts
two-address legalisation and dead-immediate elimination on straight-line bodies. This module
lifts both to bodies with labels, jumps and branches.

## Method

A pass is described item by item: item `a` of the source has the instruction `src a` and the
chunk `f a` in the rewritten body, which is `M.flatMap f`. The pass preserves control
(`ExpandOk`) when it keeps every terminator and label as it is, turns every other instruction
into straight-line instructions, and keeps a non-empty chunk at every leader. The leaders of the
rewritten body are then the positions of the chunks of the source leaders
(`ExpandOk.leaderStarts_expand`), labels sit at the positions of their chunks
(`findLabel_expand`), the block index of a block start is its block (`blockIndex_spec`), and
`build` constructs every block of the rewritten body as the image of the source block
(`ExpandOk.blockAt`). Validation carries over block by block, so `cfgOf` accepts the rewritten
body with the same blocks and terminators (`ExpandOk.cfgOf`).

The check of one block with any terminator passes for agreeing runs (`blockOkR_eqv`), given
live sets that cover what the block needs. The live sets `ownedCheckM` computes cover these
needs when they form a post-fixpoint of `liveRound` (`LivePost`). The iteration reaches one
within its budget of `4 · nb + 64` rounds when some post-fixpoint has size below the budget
(`liveIter_post`): every round that does not stop adds a name or a flag, and the iterates stay
below every post-fixpoint. A bound in the number of blocks alone does not hold: a loop that
moves `n` registers one place down needs `n` rounds.

## Main definitions

* `needAt`, `LivePost`, `liveSize`: the needs of a block, post-fixpoints, and their size.
* `termFits`, `isFallT`: the last instruction of a block against its terminator.
* `xpos`, `ExpandOk`, `shiftB`: positions in an expanded body, control-preserving expansions,
  and the image of a block.
* `blockAt`, `targetOf`, `stopOf`, `nxOf`: the blocks `build` constructs.
* `LiveConv`, `liveConvB`: the live sets `ownedCheckM` computes form a post-fixpoint.

## Main results

* `liveIter_post`: convergence of the live-set iteration below a small post-fixpoint.
* `blockOkR_eqv`: the check of one block with any terminator.
* `ownedCheckM_of_blockRes`: agreeing runs of every block pass `ownedCheckM`.
* `ExpandOk.cfgOf`: the graph of a control-preserving expansion.
* `ownedCheckM_complete_of_blockwise`: completeness of `ownedCheckM` for a control-preserving
  pass from agreement block by block.
* `twoAddr_ownedCheckM_complete_blocks`, `dropOk_ownedCheckM_complete_blocks`: completeness for
  two-address legalisation and dead-immediate elimination on bodies with several blocks.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open AllocCheck.LcmdCFG

/-! ## 1. Convergence of the live-set iteration -/

section Live

theorem foldl_join_ext : ∀ (l acc : List String), acc.Nodup →
    (l.foldl (fun a v => if a.contains v then a else a ++ [v]) acc).Nodup ∧
      ∃ e, l.foldl (fun a v => if a.contains v then a else a ++ [v]) acc = acc ++ e
  | [], acc, h => ⟨h, [], by simp⟩
  | a :: l, acc, h => by
      simp only [List.foldl_cons]
      have h1 : (if acc.contains a then acc else acc ++ [a]).Nodup := by
        split
        · exact h
        · rename_i ha
          refine List.nodup_append.mpr ⟨h, List.nodup_singleton a, ?_⟩
          intro x hx y hy
          simp only [List.mem_singleton] at hy
          subst hy
          rintro rfl
          simp [hx] at ha
      obtain ⟨hn, e, he⟩ := foldl_join_ext l _ h1
      refine ⟨hn, ?_⟩
      by_cases hc : acc.contains a = true
      · rw [ite_eq_left hc] at he
        exact ⟨e, by rw [ite_eq_left hc]; exact he⟩
      · rw [ite_eq_right hc] at he
        exact ⟨a :: e, by rw [ite_eq_right hc, he]; simp⟩

theorem foldl_join_mem : ∀ (l acc : List String) (v : String),
    v ∈ l.foldl (fun a v => if a.contains v then a else a ++ [v]) acc → v ∈ acc ∨ v ∈ l
  | [], acc, v, h => Or.inl h
  | a :: l, acc, v, h => by
      simp only [List.foldl_cons] at h
      rcases foldl_join_mem l _ v h with h | h
      · split at h
        · exact Or.inl h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl h
          · simp only [List.mem_singleton] at h
            subst h
            exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem joinLive_ext (n m : List String × Bool) (h : n.1.Nodup) :
    (joinLive n m).1.Nodup ∧ (∃ e, (joinLive n m).1 = n.1 ++ e) ∧
      (joinLive n m).2 = (n.2 || m.2) :=
  ⟨(foldl_join_ext m.1 n.1 h).1, (foldl_join_ext m.1 n.1 h).2, rfl⟩

theorem LiveCov.joinLive {P n m : List String × Bool} (hn : LiveCov P n) (hm : LiveCov P m) :
    LiveCov P (joinLive n m) := by
  refine ⟨fun v hv => ?_, fun h => ?_⟩
  · rcases foldl_join_mem m.1 n.1 v hv with h | h
    · exact hn.1 v h
    · exact hm.1 v h
  · simp only [OwnedLprogTV.joinLive, Bool.or_eq_true] at h
    rcases h with h | h
    · exact hn.2 h
    · exact hm.2 h

theorem LiveCov.trans {a b c : List String × Bool} (h1 : LiveCov a b) (h2 : LiveCov b c) :
    LiveCov a c :=
  ⟨fun v hv => h1.1 v (h2.1 v hv), fun h => h1.2 (h2.2 h)⟩

theorem LiveCov.refl (a : List String × Bool) : LiveCov a a := ⟨fun _ h => h, id⟩

theorem LiveCov.nil (a : List String × Bool) : LiveCov a ([], false) :=
  ⟨fun _ h => by simp at h, fun h => by simp at h⟩

/-- **The needed live set is monotone in the live sets of the successors.** -/
theorem blockNeed_mono {outs : List String} {L L' : Nat → List String × Bool} (T : Term)
    (R : Tbl × SOut × SOut) (B : List LinstrRM) (b : Block)
    (h : ∀ j, LiveCov (L' j) (L j)) :
    LiveCov (blockNeed outs L' T R B b) (blockNeed outs L T R B b) := by
  unfold blockNeed
  split
  · exact LiveCov.refl _
  · split
    · refine ⟨fun v hv => ?_, fun hv => ?_⟩
      · simp only [List.mem_append, List.mem_flatMap] at hv ⊢
        rcases hv with ((((hv | hv) | ⟨j, hj, hv⟩) | hv) | hv)
        · exact Or.inl (Or.inl (Or.inl (Or.inl hv)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr hv)))
        · refine Or.inl (Or.inl (Or.inr ⟨j, hj, ?_⟩))
          rcases hv with ⟨r, hr, hv⟩ | hv
          · exact Or.inl ⟨r, (h j).1 r hr, hv⟩
          · refine Or.inr ?_
            split at hv
            · rename_i hf
              rw [ite_eq_left ((h j).2 hf)]
              exact hv
            · cases hv
        · exact Or.inl (Or.inr hv)
        · exact Or.inr hv
      · simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true] at hv ⊢
        rcases hv with ((((hv | hv) | ⟨j, hj, hv⟩) | hv) | hv)
        · exact Or.inl (Or.inl (Or.inl (Or.inl hv)))
        · exact Or.inl (Or.inl (Or.inl (Or.inr hv)))
        · refine Or.inl (Or.inl (Or.inr ⟨j, hj, ?_⟩))
          rcases hv with ⟨r, hr, hv⟩ | ⟨hf, hv⟩
          · exact Or.inl ⟨r, (h j).1 r hr, hv⟩
          · exact Or.inr ⟨(h j).2 hf, hv⟩
        · exact Or.inl (Or.inr hv)
        · exact Or.inr hv
    · exact LiveCov.refl _

/-- The live set block `k` of `G` needs, from its shared runs in `R`, given the live sets `L`
    (the second argument of `joinLive` in `liveRound`). -/
def needAt (outs : List String) (B : List LinstrRM) (G : CFG) (R : Array (Tbl × SOut × SOut))
    (L : Array (List String × Bool)) (k : Nat) : List String × Bool :=
  match R[k]? with
  | some r => blockNeed outs (fun j => L.getD j ([], false)) (G.blk k).term r B (G.blk k)
  | none => ([], false)

/-- The live sets `P` cover the live sets `L` at every block. -/
def LiveLe (L P : Array (List String × Bool)) : Prop :=
  ∀ k, LiveCov (P.getD k ([], false)) (L.getD k ([], false))

/-- The live sets `P` cover, at every block of `G`, what the block needs given `P`: `P` is a
    post-fixpoint of `liveRound`. -/
def LivePost (outs : List String) (B : List LinstrRM) (G : CFG)
    (R : Array (Tbl × SOut × SOut)) (P : Array (List String × Bool)) : Prop :=
  ∀ k, k < G.blocks.size → LiveCov (P.getD k ([], false)) (needAt outs B G R P k)

/-- The weight of a live set: its number of names, plus one when the flags are live. -/
def liveWeight (p : List String × Bool) : Nat := p.1.length + p.2.toNat

/-- The total weight of the live sets of the first `n` blocks. -/
def livePot (n : Nat) (L : Array (List String × Bool)) : Nat :=
  ((List.range n).map fun k => liveWeight (L.getD k ([], false))).sum

/-- The total size of the live sets of the first `n` blocks, counting the flags of each
    block once. -/
def liveSize (n : Nat) (P : Array (List String × Bool)) : Nat :=
  ((List.range n).map fun k => (P.getD k ([], false)).1.length + 1).sum

theorem sum_map_le_of_le {l : List Nat} {a b : Nat → Nat} (h : ∀ i ∈ l, a i ≤ b i) :
    (l.map a).sum ≤ (l.map b).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.map_cons, List.sum_cons]
      have h1 := h x (List.mem_cons_self ..)
      have h2 := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
      omega

theorem sum_map_lt_of_le {l : List Nat} {a b : Nat → Nat} (h : ∀ i ∈ l, a i ≤ b i) {x : Nat}
    (hx : x ∈ l) (hlt : a x < b x) : (l.map a).sum < (l.map b).sum := by
  induction l with
  | nil => cases hx
  | cons y l ih =>
      simp only [List.map_cons, List.sum_cons]
      have hl : (l.map a).sum ≤ (l.map b).sum :=
        sum_map_le_of_le (fun i hi => h i (List.mem_cons_of_mem _ hi))
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · have h1 := h y (List.mem_cons_self ..)
        have h2 := ih (fun i hi => h i (List.mem_cons_of_mem _ hi)) hx
        omega

theorem liveRound_size (outs : List String) (B : List LinstrRM) (G : CFG)
    (R : Array (Tbl × SOut × SOut)) (L : Array (List String × Bool)) :
    (liveRound outs B G R L).size = G.blocks.size := by
  simp [liveRound]

theorem liveRound_getD (outs : List String) (B : List LinstrRM) (G : CFG)
    (R : Array (Tbl × SOut × SOut)) (L : Array (List String × Bool)) {k : Nat}
    (hk : k < G.blocks.size) :
    (liveRound outs B G R L).getD k ([], false) =
      joinLive (L.getD k ([], false)) (needAt outs B G R L k) := by
  simp [liveRound, needAt, Array.getD, hk]; rfl

theorem liveRound_getD_ge (outs : List String) (B : List LinstrRM) (G : CFG)
    (R : Array (Tbl × SOut × SOut)) (L : Array (List String × Bool)) {k : Nat}
    (hk : G.blocks.size ≤ k) : (liveRound outs B G R L).getD k ([], false) = ([], false) := by
  simp [liveRound, Array.getD, Nat.not_lt.mpr hk]

theorem needAt_mono (outs : List String) (B : List LinstrRM) (G : CFG)
    (R : Array (Tbl × SOut × SOut)) {L P : Array (List String × Bool)} (h : LiveLe L P)
    (k : Nat) : LiveCov (needAt outs B G R P k) (needAt outs B G R L k) := by
  unfold needAt
  split
  · exact blockNeed_mono _ _ _ _ h
  · exact LiveCov.refl _

theorem livePot_le {n : Nat} {L P : Array (List String × Bool)}
    (hN : ∀ k, (L.getD k ([], false)).1.Nodup) (h : LiveLe L P) : livePot n L ≤ liveSize n P := by
  refine sum_map_le_of_le fun k _ => ?_
  have hl := (List.subperm_of_subset (hN k) (h k).1).length_le
  have hb := Bool.toNat_le (L.getD k ([], false)).2
  unfold liveWeight
  omega

theorem liveCov_of_weight {n m : List String × Bool} (hn : n.1.Nodup)
    (h : ((joinLive n m).1.length, (joinLive n m).2) = (n.1.length, n.2)) : LiveCov n m := by
  obtain ⟨-, ⟨e, he⟩, h2⟩ := joinLive_ext n m hn
  simp only [Prod.mk.injEq] at h
  have he' : e = [] := by
    have := h.1
    rw [he, List.length_append] at this
    exact List.length_eq_zero_iff.mp (by omega)
  have hj : joinLive n m = n := by
    rw [Prod.ext_iff]
    exact ⟨by rw [he, he', List.append_nil], h.2⟩
  rw [← hj]
  exact joinLive_cov n m

theorem liveWeight_le_join (n m : List String × Bool) (hn : n.1.Nodup) :
    liveWeight n ≤ liveWeight (joinLive n m) := by
  obtain ⟨-, ⟨e, he⟩, h2⟩ := joinLive_ext n m hn
  unfold liveWeight
  rw [he, h2, List.length_append]
  have : n.2.toNat ≤ (n.2 || m.2).toNat := by cases n.2 <;> cases m.2 <;> decide
  omega

theorem liveWeight_lt_join (n m : List String × Bool) (hn : n.1.Nodup)
    (h : ((joinLive n m).1.length, (joinLive n m).2) ≠ (n.1.length, n.2)) :
    liveWeight n < liveWeight (joinLive n m) := by
  obtain ⟨-, ⟨e, he⟩, h2⟩ := joinLive_ext n m hn
  unfold liveWeight
  rw [he, h2, List.length_append] at h ⊢
  cases e with
  | nil =>
      cases hn2 : n.2 <;> cases hm2 : m.2 <;> simp_all
  | cons x e =>
      cases n.2 <;> cases m.2 <;> simp

/-- **The live-set iteration ends at a post-fixpoint** when it starts below a post-fixpoint
    `P` and its budget exceeds the size of `P` less the weight it starts from. -/
theorem liveIter_post_aux (outs : List String) (B : List LinstrRM) (G : CFG)
    (R : Array (Tbl × SOut × SOut)) {P : Array (List String × Bool)}
    (hP : LivePost outs B G R P) : ∀ (n : Nat) (L : Array (List String × Bool)),
      L.size = G.blocks.size → (∀ k, (L.getD k ([], false)).1.Nodup) → LiveLe L P →
      liveSize G.blocks.size P < livePot G.blocks.size L + n →
      LivePost outs B G R (liveIter outs B G R n L)
  | 0, L, _, hN, hL, hb => absurd hb (by have := livePot_le (n := G.blocks.size) hN hL; omega)
  | n + 1, L, hs, hN, hL, hb => by
      have hs' := liveRound_size outs B G R L
      have hget : ∀ k, k < G.blocks.size →
          ((liveRound outs B G R L).map (fun p => (p.1.length, p.2)))[k]? =
            some (((liveRound outs B G R L).getD k ([], false)).1.length,
              ((liveRound outs B G R L).getD k ([], false)).2) := by
        intro k hk
        simp [Array.getD, hk, hs']
      have hget' : ∀ k, k < G.blocks.size →
          (L.map (fun p => (p.1.length, p.2)))[k]? =
            some ((L.getD k ([], false)).1.length, (L.getD k ([], false)).2) := by
        intro k hk
        simp [Array.getD, hk, hs]
      rw [liveIter]
      split
      · rename_i heq
        have heq' := beq_iff_eq.mp heq
        intro k hk
        have e1 := congrArg (·[k]?) heq'
        simp only [hget k hk, hget' k hk, Option.some.injEq] at e1
        rw [liveRound_getD outs B G R L hk] at e1
        exact liveCov_of_weight (hN k) e1
      · rename_i hne
        have hex : ∃ k, k < G.blocks.size ∧
            (((liveRound outs B G R L).getD k ([], false)).1.length,
              ((liveRound outs B G R L).getD k ([], false)).2) ≠
              ((L.getD k ([], false)).1.length, (L.getD k ([], false)).2) := by
          refine Classical.byContradiction fun hc => hne ?_
          simp only [not_exists, not_and, Decidable.not_not] at hc
          refine beq_iff_eq.mpr (Array.ext_getElem? fun k => ?_)
          by_cases hk : k < G.blocks.size
          · rw [hget k hk, hget' k hk, hc k hk]
          · simp [hs, hs', hk]
        obtain ⟨k0, hk0, hne0⟩ := hex
        refine liveIter_post_aux outs B G R hP n _ hs' (fun k => ?_) (fun k => ?_) ?_
        · by_cases hk : k < G.blocks.size
          · rw [liveRound_getD outs B G R L hk]
            exact (joinLive_ext _ _ (hN k)).1
          · rw [liveRound_getD_ge outs B G R L (Nat.not_lt.mp hk)]
            exact List.nodup_nil
        · by_cases hk : k < G.blocks.size
          · rw [liveRound_getD outs B G R L hk]
            exact (hL k).joinLive ((hP k hk).trans (needAt_mono outs B G R hL k))
          · rw [liveRound_getD_ge outs B G R L (Nat.not_lt.mp hk)]
            exact LiveCov.nil _
        · have hlt : livePot G.blocks.size L < livePot G.blocks.size (liveRound outs B G R L) := by
            refine sum_map_lt_of_le (fun k hk => ?_) (List.mem_range.mpr hk0) ?_
            · rw [liveRound_getD outs B G R L (List.mem_range.mp hk)]
              exact liveWeight_le_join _ _ (hN k)
            · rw [liveRound_getD outs B G R L hk0] at hne0 ⊢
              exact liveWeight_lt_join _ _ (hN k0) hne0
          omega

/-- **Convergence of the live-set iteration.** If some post-fixpoint `P` of `liveRound` has
    size below the budget `4 · nb + 64` of `ownedCheckM`, the live sets `ownedCheckM` computes
    form a post-fixpoint. -/
theorem liveIter_post (outs : List String) (B : List LinstrRM) (G : CFG)
    (R : Array (Tbl × SOut × SOut)) {P : Array (List String × Bool)}
    (hP : LivePost outs B G R P) (hsz : liveSize G.blocks.size P < 4 * G.blocks.size + 64) :
    LivePost outs B G R (liveIter outs B G R (4 * G.blocks.size + 64)
      (Array.replicate G.blocks.size ([], false))) := by
  refine liveIter_post_aux outs B G R hP _ _ (by simp) (fun k => ?_) (fun k => ?_) ?_
  · by_cases hk : k < G.blocks.size <;> simp [Array.getD, hk]
  · have : (Array.replicate G.blocks.size (([] : List String), false)).getD k ([], false) =
        ([], false) := by
      by_cases hk : k < G.blocks.size <;> simp [Array.getD, hk]
    rw [this]
    exact LiveCov.nil _
  · omega

end Live

/-! ## 2. The check of one block with any terminator -/

section BlockCheck

/-- The last instruction `x` of a block is the instruction its terminator `T` names: a
    non-terminator for a falling block, a jump for `goto`, a branch for `cond`. -/
def termFits : Term → Option LinstrRM → Bool
  | .fall _, some p => !isTermR p.1
  | .fall _, none => true
  | .goto _, some (.Lgoto _, _) => true
  | .cond _ _, some (.Lcond _ _, _) => true
  | .ret, _ => true
  | _, _ => false

/-- A falling terminator. -/
def isFallT : Term → Bool
  | .fall _ => true
  | _ => false

/-- What a live set `n` covering the needs of a block (`blockNeed`) gives for the checks of
    `blockOkR`. -/
theorem okIn_of_need {outs : List String} {L : Nat → List String × Bool} {T : Term}
    {B : List LinstrRM} {b : Block} {T1 : Tbl} {s s' : SSt} {g g' : List SG}
    {n : List String × Bool} (hT : T ≠ .ret)
    (hL : LiveCov n (blockNeed outs L T (T1, .ok s g, .ok s' g') B b)) :
    (∀ x ∈ normGT T1.ents g', okIn n (x.varsT T1.ents) (x.readsFT T1.ents) = true) ∧
    (∀ c l τ, B[b.stop - 1]? = some (.Lcond c l, τ) → (∃ t nx, T = .cond t nx) →
      okIn n ((symDec s c).varsT T1.ents) ((symDec s c).readsInitT T1.ents) = true) ∧
    (∀ j ∈ T.succs, ∀ r ∈ (L j).1,
      okIn n ((s.regs r).varsT T1.ents) ((s.regs r).readsFT T1.ents) = true) ∧
    (∀ j ∈ T.succs, (L j).2 = true →
      okIn n (s.zf.varsT T1.ents) (s.zf.readsInitT T1.ents) = true ∧
      okIn n (s.cf.varsT T1.ents) (s.cf.readsFT T1.ents) = true ∧
      okIn n (s.of.varsT T1.ents) (s.of.readsFT T1.ents) = true) ∧
    (T.halts = true → ∀ r ∈ outs,
      okIn n ((s.regs r).varsT T1.ents) ((s.regs r).readsFT T1.ents) = true) ∧
    (∀ q ∈ s.awr ++ s'.awr,
      okIn n ((s.arrs q).varsT T1.ents) ((s.arrs q).readsFT T1.ents) = true) := by
  unfold blockNeed at hL
  split at hL
  · exact absurd rfl hT
  dsimp only at hL
  refine ⟨fun x hx => okIn_of_live hL (fun v hv => ?_) (fun h => ?_), fun c l τ hc ⟨t, nx, ht⟩ =>
    okIn_of_live hL (fun v hv => ?_) (fun h => ?_), fun j hj r hr =>
    okIn_of_live hL (fun v hv => ?_) (fun h => ?_), fun j hj hf =>
    ⟨okIn_of_live hL (fun v hv => ?_) (fun h => ?_), okIn_of_live hL (fun v hv => ?_)
      (fun h => ?_), okIn_of_live hL (fun v hv => ?_) (fun h => ?_)⟩, fun hh r hr =>
    okIn_of_live hL (fun v hv => ?_) (fun h => ?_), fun q hq =>
    okIn_of_live hL (fun v hv => ?_) (fun h => ?_)⟩
  all_goals first
    | (subst ht; simp only [hc]) | skip
  all_goals simp only [List.mem_append, List.mem_flatMap, Bool.or_eq_true, List.any_eq_true,
    Bool.and_eq_true, Option.map_some, Option.getD_some]
  · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨x, hx, hv⟩)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨x, hx, h⟩)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr hv)))
  · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  · exact Or.inl (Or.inl (Or.inr ⟨j, hj, Or.inl ⟨r, hr, hv⟩⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨j, hj, Or.inl ⟨r, hr, h⟩⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨j, hj, Or.inr (by simp [hf, hv])⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨j, hj, Or.inr ⟨hf, by simp [h]⟩⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨j, hj, Or.inr (by simp [hf, hv])⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨j, hj, Or.inr ⟨hf, by simp [h]⟩⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨j, hj, Or.inr (by simp [hf, hv])⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨j, hj, Or.inr ⟨hf, by simp [h]⟩⟩))
  · exact Or.inl (Or.inr (by simp [hh]; exact ⟨r, hr, hv⟩))
  · exact Or.inl (Or.inr ⟨hh, r, hr, h⟩)
  · exact Or.inr ⟨q, by simpa using hq, hv⟩
  · exact Or.inr ⟨q, by simpa using hq, h⟩

theorem symDec_eqv {s s' : SSt} (e : s.Eqv s') (c : LOperand) : symDec s c = symDec s' c := by
  unfold symDec
  rw [e.1, e.2.2.1]

theorem symDec_refsLt {n : Nat} {s : SSt} (h : s.RefsLt n) (c : LOperand) :
    (symDec s c).refsLt n = true := by
  unfold symDec
  split
  · exact h.2.2.1
  · split
    · exact h.1 _
    · rfl
    · rfl

/-- **The check of one block.** Two runs of a block with states that agree on every word,
    equal guards, words reading only entries of the table, a live set covering what the block
    needs, a last instruction fitting the terminator, and the same last instruction in both
    bodies unless the block falls through, pass `blockOkR`. -/
theorem blockOkR_eqv {outs : List String} {L : Nat → List String × Bool} {k : Nat} {T : Term}
    {B B' : List LinstrRM} {b b' : Block} {T1 : Tbl} {s s' : SSt} {g : List SG}
    (e : s.Eqv s') (hI : s.Inv T1.ents.size) (hg : ∀ x ∈ g, x.refsLt T1.ents.size = true)
    (hE : TBnd T1.ents)
    (hL : LiveCov (L k) (blockNeed outs L T (T1, .ok s g, .ok s' g) B b))
    (hfit : termFits T B[b.stop - 1]? = true)
    (hlast : isFallT T = false → B'[b'.stop - 1]? = B[b.stop - 1]?) :
    blockOkR outs L k T (T1, .ok s g, .ok s' g) B B' b b' = true := by
  by_cases hT : T = .ret
  · subst hT; rfl
  obtain ⟨hNg, hNd, hNr, hNf, hNh, hNa⟩ := okIn_of_need hT hL
  have hblk : blockOkR outs L k T (T1, .ok s g, .ok s' g) B B' b b' =
      (guardsT T1.ents (L k) g g &&
        termAgreeT T1.ents T (L k) s s' B[b.stop - 1]? B'[b'.stop - 1]? &&
        exitAgreeT T1.ents outs L (L k) T s s' g g) := by
    unfold blockOkR
    split
    · exact absurd rfl hT
    · rfl
  rw [hblk]
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [guardsT, Bool.and_eq_true, List.all_eq_true, List.mem_append]
    refine ⟨fun x hx => hx.elim (hg x) (hg x), fun x hx => ⟨by simpa using hx, ?_⟩⟩
    simp only [okInGT, Bool.and_eq_true]
    obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.mp hx
    exact ⟨SG.normT_refsLt hE (hg y hy) x hxy, hNg x hx⟩
  · cases T with
    | fall nx =>
        cases hb : B[b.stop - 1]? with
        | none => simp [termAgreeT]
        | some p =>
            rw [hb] at hfit
            obtain ⟨x, τ⟩ := p
            cases x <;> simp_all [termAgreeT, termFits, isTermR]
    | goto t =>
        rw [hlast rfl]
        cases hb : B[b.stop - 1]? with
        | none => rw [hb] at hfit; cases hfit
        | some p =>
            rw [hb] at hfit
            obtain ⟨x, τ⟩ := p
            cases x <;> simp_all [termAgreeT, termFits]
    | cond t nx =>
        rw [hlast rfl]
        cases hb : B[b.stop - 1]? with
        | none => rw [hb] at hfit; cases hfit
        | some p =>
            rw [hb] at hfit
            obtain ⟨x, τ⟩ := p
            cases x with
            | Lcond c l =>
                simp only [termAgreeT, okInDT, Bool.and_eq_true, beq_iff_eq]
                exact ⟨symDec_eqv e c, symDec_refsLt hI.1 c, hNd c l τ hb ⟨t, nx, rfl⟩⟩
            | _ => simp [termFits] at hfit
    | ret => exact absurd rfl hT
  · obtain ⟨hr, ha, hz, hc, ho⟩ := e
    simp only [exitAgreeT, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', beq_iff_eq]
    refine ⟨⟨fun j hj => ⟨fun r hr' => ⟨congrFun hr r, ?_⟩, ?_⟩, ?_⟩, fun q hq =>
      arrAgreeT_of_eq (congrFun ha q) ?_⟩
    · simp only [okInT, Bool.and_eq_true]
      exact ⟨hI.1.1 r, hNr j hj r hr'⟩
    · cases hf : (L j).2
      · exact Or.inl rfl
      · obtain ⟨h1, h2, h3⟩ := hNf j hj hf
        refine Or.inr ⟨⟨⟨⟨⟨hz, ?_⟩, hc⟩, ?_⟩, ho⟩, ?_⟩
        · simp only [okInFT, Bool.and_eq_true]; exact ⟨hI.1.2.2.1, h1⟩
        · simp only [okInT, Bool.and_eq_true]; exact ⟨hI.1.2.2.2.1, h2⟩
        · simp only [okInT, Bool.and_eq_true]; exact ⟨hI.1.2.2.2.2, h3⟩
    · cases hh : T.halts
      · exact Or.inl rfl
      · refine Or.inr fun r hr' => ⟨congrFun hr r, ?_⟩
        simp only [okInT, Bool.and_eq_true]
        exact ⟨hI.1.1 r, hNh hh r hr'⟩
    · simp only [okInAT, Bool.and_eq_true]
      exact ⟨hI.1.2.1 q, hNa q (by simpa using hq)⟩

/-- The last instruction of every block of a graph `cfgOf` accepts fits its terminator. -/
theorem termFits_of_cfgOf {B : List LinstrRM} {G : CFG} (hG : cfgOf (B.map Prod.fst) = some G)
    {k : Nat} (hk : k < G.blocks.size) : termFits (G.blk k).term B[(G.blk k).stop - 1]? = true := by
  have h := (blockFacts hG hk).term
  rw [List.getElem?_map] at h
  generalize (G.blk k).term = T at h ⊢
  cases hb : B[(G.blk k).stop - 1]? with
  | none => rw [hb] at h; cases T <;> simp_all [termOk]
  | some p =>
      rw [hb] at h
      obtain ⟨x, τ⟩ := p
      cases T <;> cases x <;> simp_all [termOk, termFits]

end BlockCheck

/-! ## 3. Completeness from agreement block by block -/

/-- **Completeness from agreeing block runs.** Two non-empty bodies whose graphs have the
    same number of blocks and the same terminators, the same last instruction at every block
    that does not fall through, whose block runs agree over the shared table (`Res`) and lie
    inside the fragment, pass `ownedCheckM` when the live sets it computes form a
    post-fixpoint (`LivePost`; `liveIter_post` gives one from a small post-fixpoint). -/
theorem ownedCheckM_of_blockRes (outs : List String) {B B' : List LinstrRM} {G G' : CFG}
    (hG : cfgOf (B.map Prod.fst) = some G) (hG' : cfgOf (B'.map Prod.fst) = some G')
    (hne : B ≠ []) (hne' : B' ≠ []) (hsz : G'.blocks.size = G.blocks.size)
    (hterm : ∀ k, k < G.blocks.size → (G'.blk k).term = (G.blk k).term)
    (hlast : ∀ k, k < G.blocks.size → isFallT (G.blk k).term = false →
      B'[(G'.blk k).stop - 1]? = B[(G.blk k).stop - 1]?)
    (hres : ∀ k, k < G.blocks.size → (G.blk k).term ≠ .ret →
      Res (tRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start Tbl.empty).1
        (tRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start Tbl.empty).2
        (tRun (bodyAt B' (G'.blk k) (G.blk k).term) SSt.start
          (tRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start Tbl.empty).1))
    (hunk : ∀ k, k < G.blocks.size → (G.blk k).term ≠ .ret →
      (tRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start Tbl.empty).2 ≠ .unk)
    (hlive : LivePost outs B G (runsOf B B' G G') (liveIter outs B G (runsOf B B' G G')
      (4 * G.blocks.size + 64) (Array.replicate G.blocks.size ([], false)))) :
    ownedCheckM outs B B' = true := by
  unfold ownedCheckM
  rw [hG, hG']
  dsimp only
  generalize liveIter outs B G (runsOf B B' G G') (4 * G.blocks.size + 64)
    (Array.replicate G.blocks.size ([], false)) = L at hlive
  simp only [ownedCheckWithR, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨by simpa using hne, by simpa using hne'⟩, by simp [hsz]⟩, fun k hk => ⟨?_, ?_⟩⟩
  · simp [hterm k hk]
  have hR : (runsOf B B' G G')[k]? =
      some (blockRuns B B' (G.blk k) (G'.blk k) (G.blk k).term) := by
    simp [runsOf, hk]
  rw [hR]
  dsimp only
  have hL := hlive k hk
  unfold needAt at hL
  rw [hR] at hL
  dsimp only at hL
  by_cases hT : (G.blk k).term = .ret
  · unfold blockOkR
    split
    · rfl
    · rename_i h; exact absurd hT h
  have hres' := hres k hk hT
  have hunk' := hunk k hk hT
  unfold blockRuns at hL ⊢
  dsimp only at hL ⊢
  generalize hp : tRun (bodyAt B (G.blk k) (G.blk k).term) SSt.start Tbl.empty = p at hres' hunk' hL ⊢
  obtain ⟨T1, o⟩ := p
  cases o with
  | unk => exact absurd rfl hunk'
  | fail =>
      unfold blockOkR
      split
      · rfl
      · rfl
  | ok s g =>
      dsimp only at hres' hL ⊢
      generalize hq : tRun (bodyAt B' (G'.blk k) (G.blk k).term) SSt.start T1 = q at hres' hL ⊢
      obtain ⟨Q, o'⟩ := q
      cases o' with
      | ok s' g' =>
          obtain ⟨hQ, e, rfl⟩ := hres'
          subst hQ
          have hinv := tRun_inv _ SSt.start Tbl.empty SSt.inv_start hp
          have hE : TBnd Q.ents := by
            have := tRun_valid (bodyAt B (G.blk k) (G.blk k).term) SSt.start Tbl.empty tValid_empty
            rw [hp] at this
            exact this.2
          exact blockOkR_eqv e hinv.1 hinv.2 hE hL (termFits_of_cfgOf hG hk) (hlast k hk)
      | fail => simp [Res] at hres'
      | unk => simp [Res] at hres'

/-! ## 4. Positions in an expanded body -/

section Xpos

variable {α γ : Type}

/-- The index in `M.flatMap g` where the chunk of entry `pc` of `M` starts. -/
def xpos (g : α → List γ) (M : List α) (pc : Nat) : Nat := ((M.take pc).flatMap g).length

theorem xpos_zero (g : α → List γ) (M : List α) : xpos g M 0 = 0 := by simp [xpos]

theorem xpos_nil (g : α → List γ) (pc : Nat) : xpos g [] pc = 0 := by simp [xpos]

theorem xpos_cons_succ (g : α → List γ) (a : α) (M : List α) (pc : Nat) :
    xpos g (a :: M) (pc + 1) = (g a).length + xpos g M pc := by
  simp [xpos]

theorem xpos_succ (g : α → List γ) {M : List α} {pc : Nat} (h : pc < M.length) :
    xpos g M (pc + 1) = xpos g M pc + (g M[pc]).length := by
  simp only [xpos, List.take_succ_eq_append_getElem h, List.flatMap_append, List.length_append]
  simp

theorem xpos_of_le (g : α → List γ) {M : List α} {pc : Nat} (h : M.length ≤ pc) :
    xpos g M pc = (M.flatMap g).length := by
  simp [xpos, List.take_of_length_le h]

theorem xpos_mono (g : α → List γ) (M : List α) {a b : Nat} (h : a ≤ b) :
    xpos g M a ≤ xpos g M b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [xpos, List.take_add, List.flatMap_append, List.length_append]
  omega

theorem xpos_le (g : α → List γ) (M : List α) (pc : Nat) :
    xpos g M pc ≤ (M.flatMap g).length := by
  rw [← xpos_of_le g (le_refl M.length)]
  rcases Nat.le_total pc M.length with h | h
  · exact xpos_mono g M h
  · rw [xpos_of_le g h, xpos_of_le g (le_refl _)]

theorem getElem?_xpos (g : α → List γ) {M : List α} {pc i : Nat} (h : pc < M.length) :
    (M.flatMap g)[xpos g M pc + i]? = if i < (g M[pc]).length then (g M[pc])[i]? else
      (M.flatMap g)[xpos g M (pc + 1) + (i - (g M[pc]).length)]? := by
  have hM : M = M.take pc ++ M[pc] :: M.drop (pc + 1) := by
    simp [List.getElem_cons_drop]
  have e1 : M.flatMap g = (M.take pc).flatMap g ++ (g M[pc] ++ (M.drop (pc + 1)).flatMap g) := by
    rw [← List.flatMap_cons, ← List.flatMap_append]
    exact congrArg _ hM
  have hx := xpos_succ g h
  unfold xpos at hx ⊢
  rw [e1, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  split
  · rw [List.getElem?_append_left (by omega)]
  · rename_i hi
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
      List.getElem?_append_right (by rw [hx]; omega)]
    congr 1
    rw [hx]
    omega

theorem getElem?_xpos_lt (g : α → List γ) {M : List α} {pc i : Nat} (h : pc < M.length)
    (hi : i < (g M[pc]).length) : (M.flatMap g)[xpos g M pc + i]? = (g M[pc])[i]? := by
  rw [getElem?_xpos g h, ite_eq_left hi]

theorem exists_xpos (g : α → List γ) : ∀ (M : List α) {p : Nat}, p < (M.flatMap g).length →
    ∃ pc, pc < M.length ∧ xpos g M pc ≤ p ∧ p < xpos g M (pc + 1)
  | [], p, hp => by simp at hp
  | a :: M, p, hp => by
      by_cases ha : p < (g a).length
      · exact ⟨0, by simp, by simp [xpos_zero], by simp [xpos_cons_succ, xpos_zero, ha]⟩
      · have hp' : p - (g a).length < (M.flatMap g).length := by
          simp only [List.flatMap_cons, List.length_append] at hp
          omega
        obtain ⟨pc, h1, h2, h3⟩ := exists_xpos g M hp'
        refine ⟨pc + 1, by simp; omega, ?_, ?_⟩
        · rw [xpos_cons_succ]; omega
        · rw [xpos_cons_succ]; omega

/-- The slice of an expanded body between the chunks of `a` and `b` is the expansion of the
    slice of the source between `a` and `b`. -/
theorem flatMap_slice (g : α → List γ) (M : List α) {a b : Nat} (hab : a ≤ b) :
    ((M.flatMap g).drop (xpos g M a)).take (xpos g M b - xpos g M a) =
      ((M.drop a).take (b - a)).flatMap g := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  have e : M.flatMap g = (M.take a).flatMap g ++ (M.drop a).flatMap g := by
    rw [← List.flatMap_append, List.take_append_drop]
  have e2 : (M.drop a).flatMap g =
      ((M.drop a).take d).flatMap g ++ ((M.drop a).drop d).flatMap g := by
    rw [← List.flatMap_append, List.take_append_drop]
  simp only [xpos, List.take_add, List.flatMap_append, List.length_append, Nat.add_sub_cancel_left]
  rw [e, List.drop_left, e2, List.take_left]

theorem xpos_lt_succ (g : α → List γ) {M : List α} {pc : Nat} (h : pc < M.length)
    (hne : g M[pc] ≠ []) : xpos g M pc < xpos g M (pc + 1) := by
  rw [xpos_succ g h]
  have := List.length_pos_iff.mpr hne
  omega

/-- Every index of `M.flatMap g` lies in the chunk of one entry of `M`. -/
theorem getElem?_flatMap_chunk (g : α → List γ) {M : List α} {p : Nat}
    (hp : p < (M.flatMap g).length) : ∃ pc, ∃ h : pc < M.length, xpos g M pc ≤ p ∧
      p - xpos g M pc < (g M[pc]).length ∧ xpos g M (pc + 1) = xpos g M pc + (g M[pc]).length ∧
      (M.flatMap g)[p]? = (g M[pc])[p - xpos g M pc]? := by
  obtain ⟨pc, h1, h2, h3⟩ := exists_xpos g M hp
  have hs := xpos_succ g h1
  refine ⟨pc, h1, h2, by omega, hs, ?_⟩
  have := getElem?_xpos_lt g h1 (i := p - xpos g M pc) (by omega)
  rwa [Nat.add_sub_cancel' h2] at this

end Xpos

/-! ## 5. Leaders of an expanded body -/

section Leaders

variable {α : Type}

/-- A control-preserving expansion of the body `M.map s` into `M.flatMap g`: a terminator or
    label is kept as it is, every other instruction becomes straight-line instructions, and
    the instruction at every leader keeps a non-empty chunk. -/
def ExpandOk (s : α → LinstrR) (g : α → List LinstrR) (M : List α) : Prop :=
  (∀ a ∈ M, (isTermR (s a) || isLabelR (s a)) = true → g a = [s a]) ∧
  (∀ a ∈ M, (isTermR (s a) || isLabelR (s a)) = false → ∀ y ∈ g a, straightR y = true) ∧
  (∀ pc (h : pc < M.length), isLeader (M.map s).toArray pc = true → g M[pc] ≠ [])

variable {s : α → LinstrR} {g : α → List LinstrR} {M : List α}

theorem ExpandOk.ctl (hE : ExpandOk s g M) {pc : Nat} (h : pc < M.length) {i : Nat}
    {y : LinstrR} (hy : (g M[pc])[i]? = some y) (hc : (isTermR y || isLabelR y) = true) :
    i = 0 ∧ y = s M[pc] ∧ g M[pc] = [s M[pc]] := by
  have hm : M[pc] ∈ M := List.getElem_mem h
  cases hk : (isTermR (s M[pc]) || isLabelR (s M[pc]))
  · have := hE.2.1 _ hm hk y (List.mem_of_getElem? hy)
    simp only [straightR, Bool.and_eq_true, Bool.not_eq_true'] at this
    simp [this.1.1, this.1.2] at hc
  · have hg := hE.1 _ hm hk
    rw [hg] at hy
    cases i with
    | zero => simp at hy; exact ⟨rfl, hy.symm, hg⟩
    | succ i => simp at hy

theorem isLeader_toArray (l : List LinstrR) (pc : Nat) :
    isLeader l.toArray pc = (pc == 0 || (l[pc]?.any isLabelR) ||
      (match pc with
       | 0 => false
       | p + 1 => l[p]?.any isTermR)) := by
  unfold isLeader
  simp only [List.getElem?_toArray]
  rfl

theorem ExpandOk.leader_xpos (hE : ExpandOk s g M) {pc : Nat} (h : pc < M.length)
    (hL : isLeader (M.map s).toArray pc = true) :
    isLeader (M.flatMap g).toArray (xpos g M pc) = true := by
  rw [isLeader_toArray] at hL ⊢
  simp only [Bool.or_eq_true, beq_iff_eq] at hL ⊢
  rcases hL with (h0 | hl) | ht
  · subst h0; exact Or.inl (Or.inl (xpos_zero g M))
  · simp only [List.getElem?_map, List.getElem?_eq_getElem h, Option.map_some,
      Option.any_some] at hl
    have hg := hE.1 _ (List.getElem_mem h) (by simp [hl])
    refine Or.inl (Or.inr ?_)
    have := getElem?_xpos_lt g h (i := 0) (by rw [hg]; simp)
    rw [Nat.add_zero] at this
    rw [this, hg]
    simpa using hl
  · cases pc with
    | zero => cases ht
    | succ p =>
        have hp : p < M.length := by omega
        simp only [List.getElem?_map, List.getElem?_eq_getElem hp, Option.map_some,
          Option.any_some] at ht
        have hg := hE.1 _ (List.getElem_mem hp) (by simp [ht])
        have hx := xpos_succ g hp
        rw [hg, List.length_singleton] at hx
        refine Or.inr ?_
        rw [hx]
        have := getElem?_xpos_lt g hp (i := 0) (by rw [hg]; simp)
        rw [Nat.add_zero] at this
        show ((M.flatMap g)[xpos g M p]?.any isTermR) = true
        rw [this, hg]
        simpa using ht

theorem ExpandOk.xpos_lt (hE : ExpandOk s g M) {pc : Nat} (h : pc < M.length)
    (hL : isLeader (M.map s).toArray pc = true) : xpos g M pc < (M.flatMap g).length :=
  Nat.lt_of_lt_of_le (xpos_lt_succ g h (hE.2.2 pc h hL)) (xpos_le g M _)

theorem ExpandOk.leader_of_xpos (hE : ExpandOk s g M) {p : Nat}
    (hp : p < (M.flatMap g).length) (hL : isLeader (M.flatMap g).toArray p = true) :
    ∃ pc, pc < M.length ∧ isLeader (M.map s).toArray pc = true ∧ xpos g M pc = p := by
  have hM : 0 < M.length := by
    rcases M with _ | _
    · simp at hp
    · simp
  rw [isLeader_toArray] at hL
  simp only [Bool.or_eq_true, beq_iff_eq] at hL
  rcases hL with (h0 | hl) | ht
  · subst h0
    exact ⟨0, hM, by rw [isLeader_toArray]; simp, xpos_zero g M⟩
  · obtain ⟨pc, h, h1, h2, h3, h4⟩ := getElem?_flatMap_chunk g hp
    cases hy : (g M[pc])[p - xpos g M pc]? with
    | none => simp [h4, hy] at hl
    | some y =>
        rw [h4, hy] at hl
        simp only [Option.any_some] at hl
        obtain ⟨hi, rfl, -⟩ := hE.ctl h hy (by simp [hl])
        refine ⟨pc, h, ?_, by omega⟩
        rw [isLeader_toArray]
        simp [List.getElem?_eq_getElem h, hl]
  · cases p with
    | zero => cases ht
    | succ q =>
        have hq : q < (M.flatMap g).length := by omega
        obtain ⟨pc, h, h1, h2, h3, h4⟩ := getElem?_flatMap_chunk g hq
        cases hy : (g M[pc])[q - xpos g M pc]? with
        | none => simp [h4, hy] at ht
        | some y =>
            simp only [h4, hy, Option.any_some] at ht
            obtain ⟨hi, rfl, hg⟩ := hE.ctl h hy (by simp [ht])
            rw [hg, List.length_singleton] at h3
            have hq' : xpos g M (pc + 1) = q + 1 := by omega
            have hpc1 : pc + 1 < M.length := by
              refine Nat.lt_of_le_of_ne h fun he => ?_
              rw [he, xpos_of_le g (le_refl _)] at hq'
              omega
            refine ⟨pc + 1, hpc1, ?_, hq'⟩
            rw [isLeader_toArray]
            simp [List.getElem?_eq_getElem h, ht]

theorem foldl_push_filter (P : Nat → Bool) : ∀ (l : List Nat) (acc : Array Nat),
    l.foldl (fun b a => if P a = true then b.push a else b) acc = acc ++ (l.filter P).toArray
  | [], acc => by simp
  | a :: l, acc => by
      simp only [List.foldl_cons, List.filter_cons]
      rw [foldl_push_filter P l]
      split <;> simp

/-- The leaders of a body in increasing order. -/
theorem leaderStarts_eq (w : Array LinstrR) :
    leaderStarts w = ((List.range w.size).filter (isLeader w)).toArray := by
  unfold leaderStarts
  simp only [Id.run]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  have hb : (fun pc (s : Array Nat) => if isLeader w pc = true then
      (pure (ForInStep.yield (s.push pc)) : Id (ForInStep (Array Nat)))
      else pure (ForInStep.yield s)) =
      fun pc s => pure (ForInStep.yield (if isLeader w pc = true then s.push pc else s)) := by
    funext pc s
    split <;> rfl
  rw [hb, forIn_id_yield, foldl_push_filter]
  simp [Std.Legacy.Range.size, List.range_eq_range']

theorem eq_of_lt_sorted : ∀ (l1 l2 : List Nat), l1.Pairwise (· < ·) → l2.Pairwise (· < ·) →
    (∀ x, x ∈ l1 ↔ x ∈ l2) → l1 = l2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr (List.mem_cons_self ..)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).mp (List.mem_cons_self ..)) (by simp)
  | a :: t1, b :: t2, h1, h2, h => by
      rw [List.pairwise_cons] at h1 h2
      have ha := (h a).mp (List.mem_cons_self ..)
      have hb := (h b).mpr (List.mem_cons_self ..)
      have hab : a = b := by
        rcases List.mem_cons.mp ha with e | ha
        · exact e
        · rcases List.mem_cons.mp hb with e | hb
          · exact e.symm
          · have := h1.1 b hb; have := h2.1 a ha; omega
      subst hab
      rw [eq_of_lt_sorted t1 t2 h1.2 h2.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩]
      · have := h1.1 x hx
        rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with e | e
        · omega
        · exact e
      · have := h2.1 x hx
        rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with e | e
        · omega
        · exact e

variable {s : α → LinstrR} {g : α → List LinstrR} {M : List α}

theorem ExpandOk.xpos_strict (hE : ExpandOk s g M) {a b : Nat} (ha : a < M.length)
    (hL : isLeader (M.map s).toArray a = true) (hab : a < b) : xpos g M a < xpos g M b :=
  Nat.lt_of_lt_of_le (xpos_lt_succ g ha (hE.2.2 a ha hL)) (xpos_mono g M hab)

/-- **The leaders of an expanded body** are the positions of the leaders of the source. -/
theorem ExpandOk.leaderStarts_expand (hE : ExpandOk s g M) :
    AllocCheck.LcmdCFG.leaderStarts (M.flatMap g).toArray =
      (AllocCheck.LcmdCFG.leaderStarts (M.map s).toArray).map (xpos g M) := by
  rw [leaderStarts_eq, leaderStarts_eq, List.map_toArray]
  congr 1
  refine eq_of_lt_sorted _ _ ((List.pairwise_lt_range).filter _) ?_ fun x => ?_
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ ((List.pairwise_lt_range).filter _)
    intro a b ha _ hab
    simp only [List.mem_filter, List.mem_range, List.size_toArray, List.length_map] at ha
    exact hE.xpos_strict ha.1 ha.2 hab
  · simp only [List.mem_filter, List.mem_range, List.size_toArray, List.length_map,
      List.mem_map]
    constructor
    · rintro ⟨hx, hL⟩
      obtain ⟨pc, h, hl, rfl⟩ := hE.leader_of_xpos hx hL
      exact ⟨pc, ⟨h, hl⟩, rfl⟩
    · rintro ⟨pc, ⟨h, hl⟩, rfl⟩
      exact ⟨hE.xpos_lt h hl, hE.leader_xpos h hl⟩

end Leaders

/-! ## 6. The block index -/

section BlockIndex

/-- The block `b` may hold index `pc - 1` for the block starts `S`: every start after the
    first up to `b` lies before `pc`, and the start after `b` does not. -/
def BIx (S : Array Nat) (pc b : Nat) : Prop :=
  (∀ i, 1 ≤ i → i ≤ b → i < S.size ∧ S[i]! < pc) ∧ (b + 1 < S.size → pc ≤ S[b + 1]!)

theorem bIx_zero (S : Array Nat) : BIx S 0 0 :=
  ⟨fun i h1 h2 => by omega, fun _ => Nat.zero_le _⟩

theorem bIx_step {S : Array Nat} (hS : ∀ i j, i < j → j < S.size → S[i]! < S[j]!) {pc b : Nat}
    (h : BIx S pc b) :
    BIx S (pc + 1) (if (decide (b + 1 < S.size) && S[b + 1]! == pc) = true then b + 1 else b) := by
  obtain ⟨h1, h2⟩ := h
  split
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    refine ⟨fun i hi1 hi2 => ?_, fun hb => ?_⟩
    · rcases Nat.lt_or_ge i (b + 1) with hi | hi
      · have := h1 i hi1 (by omega); exact ⟨this.1, by omega⟩
      · have : i = b + 1 := by omega
        subst this; exact ⟨hc.1, by omega⟩
    · have := hS (b + 1) (b + 1 + 1) (by omega) hb
      omega
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and] at hc
    refine ⟨fun i hi1 hi2 => ?_, fun hb => ?_⟩
    · have := h1 i hi1 hi2; exact ⟨this.1, by omega⟩
    · have := h2 hb; have := hc hb; omega

theorem blockIndex_loop {S : Array Nat} (hS : ∀ i j, i < j → j < S.size → S[i]! < S[j]!) :
    ∀ (k pc : Nat) (out : Array Nat) (b : Nat), BIx S pc b → out.size = pc →
      (∀ q, q < pc → BIx S (q + 1) out[q]!) →
      let r := (List.range' pc k).foldl (fun s pc =>
        if (decide (s.2 + 1 < S.size) && S[s.2 + 1]! == pc) = true then
          (s.1.push (s.2 + 1), s.2 + 1) else (s.1.push s.2, s.2)) (out, b)
      r.1.size = pc + k ∧ ∀ q, q < pc + k → BIx S (q + 1) r.1[q]!
  | 0, pc, out, b, _, hs, ho => by simpa [hs] using ho
  | k + 1, pc, out, b, hb, hs, ho => by
      simp only [List.range'_succ, List.foldl_cons]
      have hstep := bIx_step hS hb
      have key : (if (decide ((out, b).2 + 1 < S.size) && S[(out, b).2 + 1]! == pc) = true then
          ((out, b).1.push ((out, b).2 + 1), (out, b).2 + 1) else
          ((out, b).1.push (out, b).2, (out, b).2)) =
          (out.push (if (decide (b + 1 < S.size) && S[b + 1]! == pc) = true then b + 1 else b),
            if (decide (b + 1 < S.size) && S[b + 1]! == pc) = true then b + 1 else b) := by
        dsimp only
        split <;> rfl
      rw [key]
      generalize (if (decide (b + 1 < S.size) && S[b + 1]! == pc) = true then b + 1 else b) = x
        at hstep ⊢
      subst hs
      have ih := blockIndex_loop hS k (out.size + 1) (out.push x) x hstep
        (by rw [Array.size_push])
        (fun q hq => by
          rcases Nat.lt_or_ge q out.size with h | h
          · rw [getElem!_pos (out.push x) q (by simp; omega), Array.getElem_push_lt h,
              ← getElem!_pos out q h]
            exact ho q h
          · have : q = out.size := by omega
            subst this
            rw [getElem!_pos (out.push x) out.size (by simp), Array.getElem_push_eq]
            exact hstep)
      exact ⟨by rw [ih.1]; omega, fun q hq => ih.2 q (by omega)⟩

/-- **The block index.** For strictly increasing block starts, the block index of `pc`
    is the block whose start lies at or before `pc` and whose successor starts after
    `pc`. -/
theorem blockIndex_spec {S : Array Nat} (hS : ∀ i j, i < j → j < S.size → S[i]! < S[j]!)
    (n : Nat) : (blockIndex n S).size = n ∧ ∀ q, q < n → BIx S (q + 1) (blockIndex n S)[q]! := by
  unfold blockIndex
  simp only [Id.run]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  have hb : (fun (pc : Nat) (s : Array Nat × Nat) =>
      if (decide (s.2 + 1 < S.size) && S[s.2 + 1]! == pc) = true
      then (pure (ForInStep.yield (s.1.push (s.2 + 1), s.2 + 1)) : Id (ForInStep (Array Nat × Nat)))
      else pure (ForInStep.yield (s.1.push s.2, s.2))) =
      fun pc s => pure (ForInStep.yield
        (if (decide (s.2 + 1 < S.size) && S[s.2 + 1]! == pc) = true
          then (s.1.push (s.2 + 1), s.2 + 1) else (s.1.push s.2, s.2))) := by
    funext pc s
    split <;> rfl
  rw [hb, forIn_id_yield]
  have := blockIndex_loop hS n 0 (Array.mkEmpty n) 0 (bIx_zero S) (by simp) (fun q hq => by omega)
  simp only [Nat.zero_add] at this
  have hr : [:n].size = n := by simp [Std.Legacy.Range.size]
  rw [hr]
  exact this

end BlockIndex

/-! ## 7. Label positions -/

section Labels

theorem forIn_id_of_yield {α β : Type} {l : List α} {init : β} {f : α → β → Id (ForInStep β)}
    {g : β → α → β} (h : ∀ a b, f a b = pure (ForInStep.yield (g b a))) :
    forIn (m := Id) l init f = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.forIn_cons, h a init]; exact ih

/-- One step of `firstLabelPcs`. -/
def flStep (s : Std.HashMap LLabel Nat × Nat) (i : LinstrR) : Std.HashMap LLabel Nat × Nat :=
  match i with
  | .Llabel _ l => if (!s.1.contains l) = true then (s.1.insert l s.2, s.2 + 1) else (s.1, s.2 + 1)
  | _ => (s.1, s.2 + 1)

theorem option_map_add_succ (X : Option Nat) (p : Nat) :
    X.map (· + (p + 1)) = (X.map (· + 1)).map (· + p) := by
  cases X <;> simp; omega

theorem flStep_foldl (l : LLabel) : ∀ (xs : List LinstrR) (m : Std.HashMap LLabel Nat) (p : Nat),
    (xs.foldl flStep (m, p)).1[l]? = m[l]?.or ((xs.findIdx? (JasminLsemLabeled.isLabel l)).map
      (· + p))
  | [], m, p => by simp
  | x :: xs, m, p => by
      simp only [List.foldl_cons, List.findIdx?_cons]
      cases x with
      | Llabel k l' =>
          show (List.foldl flStep (if (!m.contains l') = true then (m.insert l' p, p + 1)
            else (m, p + 1)) xs).1[l]? = _
          by_cases hc : m.contains l' = true
          · rw [ite_eq_right (by simp [hc]), flStep_foldl l xs m (p + 1)]
            by_cases hl : l = l'
            · subst hl
              obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
                (by rwa [Std.HashMap.contains_eq_isSome_getElem?] at hc)
              rw [hv]
              rfl
            · have : JasminLsemLabeled.isLabel l (.Llabel k l') = false := by
                show (l == l') = false
                simp [hl]
              rw [ite_eq_right (by simp [this]), option_map_add_succ]
          · rw [ite_eq_left (by simpa using hc), flStep_foldl l xs _ (p + 1)]
            by_cases hl : l = l'
            · subst hl
              have hn : m[l]? = none := by
                rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
                simpa using hc
              have hl : JasminLsemLabeled.isLabel l (.Llabel k l) = true := by
                show (l == l) = true
                simp
              rw [Std.HashMap.getElem?_insert_self, hn, ite_eq_left hl]
              simp only [Option.some_or, Option.none_or, Option.map_some, Nat.zero_add]
            · have : JasminLsemLabeled.isLabel l (.Llabel k l') = false := by
                show (l == l') = false
                simp [hl]
              have hb : ¬ (l' = l) := fun h => hl h.symm
              rw [ite_eq_right (by simp [this]), option_map_add_succ]
              simp only [Std.HashMap.getElem?_insert, beq_iff_eq, hb, ite_false]
      | _ =>
          show (List.foldl flStep (m, p + 1) xs).1[l]? = _
          rw [flStep_foldl l xs m (p + 1)]
          rw [ite_eq_right (fun h => by cases h), option_map_add_succ]

/-- **Label positions.** `firstLabelPcs` sends a label to the index `findLabel` returns. -/
theorem firstLabelPcs_eq (w : Array LinstrR) (l : LLabel) :
    (firstLabelPcs w)[l]? = JasminLsemLabeled.findLabel l w.toList := by
  unfold firstLabelPcs
  simp only [Id.run]
  rw [← Array.forIn_toList]
  rw [forIn_id_of_yield (g := flStep) (fun i s => ?_)]
  · show (w.toList.foldl flStep (∅, 0)).1[l]? = _
    rw [flStep_foldl, Std.HashMap.getElem?_empty, Option.none_or]
    unfold JasminLsemLabeled.findLabel
    cases List.findIdx? (JasminLsemLabeled.isLabel l) w.toList <;> rfl
  · cases i with
    | Llabel k l' =>
        change (if (!s.1.contains l') = true then
            (pure (ForInStep.yield (s.1.insert l' s.2, s.2 + 1)) :
              Id (ForInStep (Std.HashMap LLabel Nat × Nat)))
          else pure (ForInStep.yield (s.1, s.2 + 1))) =
          pure (ForInStep.yield (if (!s.1.contains l') = true then
            (s.1.insert l' s.2, s.2 + 1) else (s.1, s.2 + 1)))
        cases (!s.1.contains l') <;> rfl
    | _ => rfl

theorem forIn_label_filter
    {f : LinstrR → Option Bool × Std.HashSet LLabel → Id (ForInStep (Option Bool × Std.HashSet LLabel))}
    (h1 : ∀ i S, isLabelR i = false → f i (none, S) = pure (.yield (none, S)))
    (h2 : ∀ i S, isLabelR i = true →
      (∃ v, f i (none, S) = pure (.done v)) ∨ ∃ S', f i (none, S) = pure (.yield (none, S'))) :
    ∀ (l : List LinstrR) (S : Std.HashSet LLabel),
      forIn (m := Id) l (none, S) f = forIn (m := Id) (l.filter isLabelR) (none, S) f
  | [], _ => rfl
  | a :: l, S => by
      rw [List.filter_cons]
      cases ha : isLabelR a
      · rw [ite_eq_right (by simp), List.forIn_cons, h1 a S ha]
        exact forIn_label_filter h1 h2 l S
      · rw [ite_eq_left rfl, List.forIn_cons, List.forIn_cons]
        rcases h2 a S ha with ⟨v, hv⟩ | ⟨S', hS⟩
        · rw [hv]; rfl
        · rw [hS]
          exact forIn_label_filter h1 h2 l S'

/-- `hasDupLabel` reads only the labels of a body. -/
theorem hasDupLabel_filter (l : List LinstrR) :
    hasDupLabel l.toArray = hasDupLabel (l.filter isLabelR).toArray := by
  unfold hasDupLabel
  simp only [Id.run]
  rw [← Array.forIn_toList, ← Array.forIn_toList]
  rw [forIn_label_filter (fun i S hi => ?_) (fun i S hi => ?_) l ∅]
  · cases i <;> first | rfl | simp [isLabelR] at hi
  · cases i <;> simp only [isLabelR, Bool.false_eq_true] at hi
    simp only
    split
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩

variable {α : Type} {s : α → LinstrR} {g : α → List LinstrR}

theorem findIdx?_append_of_none {β : Type} (p : β → Bool) :
    ∀ (l1 l2 : List β), (∀ x ∈ l1, p x = false) →
      (l1 ++ l2).findIdx? p = (l2.findIdx? p).map (· + l1.length)
  | [], l2, _ => by simp
  | a :: l1, l2, h => by
      rw [List.cons_append, List.findIdx?_cons, ite_eq_right (by simp [h a (List.mem_cons_self ..)]),
        findIdx?_append_of_none p l1 l2 (fun x hx => h x (List.mem_cons_of_mem _ hx))]
      cases l2.findIdx? p <;> simp; omega

/-- **Labels of an expanded body.** -/
theorem findLabel_expand (lb : LLabel) : ∀ (M : List α),
    (∀ a ∈ M, (isTermR (s a) || isLabelR (s a)) = true → g a = [s a]) →
    (∀ a ∈ M, (isTermR (s a) || isLabelR (s a)) = false → ∀ y ∈ g a, straightR y = true) →
    JasminLsemLabeled.findLabel lb (M.flatMap g) =
      (JasminLsemLabeled.findLabel lb (M.map s)).map (xpos g M)
  | [], _, _ => by simp [JasminLsemLabeled.findLabel]
  | a :: M, h1, h2 => by
      have ih := findLabel_expand lb M (fun b hb => h1 b (List.mem_cons_of_mem _ hb))
        (fun b hb => h2 b (List.mem_cons_of_mem _ hb))
      unfold JasminLsemLabeled.findLabel at ih ⊢
      rw [List.flatMap_cons, List.map_cons, List.findIdx?_cons]
      cases hc : (isTermR (s a) || isLabelR (s a))
      · have hl : JasminLsemLabeled.isLabel lb (s a) = false := by
          simp only [Bool.or_eq_false_iff] at hc
          cases h : s a <;> simp_all [JasminLsemLabeled.isLabel, isLabelR]
        rw [ite_eq_right (by simp [hl]), findIdx?_append_of_none _ _ _ (fun y hy => by
          have := h2 a (List.mem_cons_self ..) hc y hy
          simp only [straightR, Bool.and_eq_true, Bool.not_eq_true'] at this
          cases y <;> simp_all [JasminLsemLabeled.isLabel, isLabelR]), ih]
        cases (M.map s).findIdx? (JasminLsemLabeled.isLabel lb) <;> simp [xpos_cons_succ]
        omega
      · rw [h1 a (List.mem_cons_self ..) hc, List.singleton_append, List.findIdx?_cons, ih]
        split
        · simp [xpos_zero]
        · cases (M.map s).findIdx? (JasminLsemLabeled.isLabel lb) <;> simp [xpos_cons_succ, h1 a (List.mem_cons_self ..) hc]
          omega

theorem filter_label_expand : ∀ (M : List α),
    (∀ a ∈ M, (isTermR (s a) || isLabelR (s a)) = true → g a = [s a]) →
    (∀ a ∈ M, (isTermR (s a) || isLabelR (s a)) = false → ∀ y ∈ g a, straightR y = true) →
    (M.flatMap g).filter isLabelR = (M.map s).filter isLabelR
  | [], _, _ => rfl
  | a :: M, h1, h2 => by
      have ih := filter_label_expand M (fun b hb => h1 b (List.mem_cons_of_mem _ hb))
        (fun b hb => h2 b (List.mem_cons_of_mem _ hb))
      rw [List.flatMap_cons, List.filter_append, ih, List.map_cons, List.filter_cons]
      cases hc : (isTermR (s a) || isLabelR (s a))
      · have hl : isLabelR (s a) = false := by simp_all
        rw [ite_eq_right (by simp [hl])]
        have : (g a).filter isLabelR = [] := List.filter_eq_nil_iff.mpr fun y hy => by
          have := h2 a (List.mem_cons_self ..) hc y hy
          simp only [straightR, Bool.and_eq_true, Bool.not_eq_true'] at this
          simp [this.1.2]
        rw [this, List.nil_append]
      · rw [h1 a (List.mem_cons_self ..) hc]
        cases hl : isLabelR (s a) <;> simp [hl]

end Labels

/-! ## 8. The construction of the graph -/

section Build

/-- The terminator `build` gives a block whose last instruction is `o`, for the label
    targets `target` and the fall-through block `nx`. -/
def termOfLast (target : LLabel → Option Nat) (nx : Option Nat) : Option LinstrR → Option Term
  | some (.Lgoto (_, l)) => (target l).map Term.goto
  | some (.Lcond _ l) => (target l).map fun t => Term.cond t nx
  | some .Lret => some .ret
  | _ => some (.fall nx)

theorem termOfLast_fall {target : LLabel → Option Nat} {nx : Option Nat} {x : LinstrR}
    (hx : isTermR x = false) : termOfLast target nx (some x) = some (.fall nx) := by
  cases x <;> first | rfl | cases hx

/-- The block a jump to label `l` targets in the graph `build` constructs for `w`. -/
def targetOf (w : Array LinstrR) (l : LLabel) : Option Nat :=
  (firstLabelPcs w)[l]?.bind fun pc => (blockIndex w.size (leaderStarts w))[pc]?

/-- The end of block `k` for the block starts `S` of a body of `n` instructions. -/
def stopOf (S : Array Nat) (n k : Nat) : Nat := if k + 1 < S.size then S[k + 1]! else n

/-- The fall-through block of block `k` for the block starts `S`. -/
def nxOf (S : Array Nat) (k : Nat) : Option Nat := if k + 1 < S.size then some (k + 1) else none

/-- Block `k` of the graph `build` constructs for the body `w`, or `none` when its last
    instruction jumps to an absent label. -/
def blockAt (w : Array LinstrR) (k : Nat) : Option Block :=
  (termOfLast (targetOf w) (nxOf (leaderStarts w) k)
      w[stopOf (leaderStarts w) w.size k - 1]?).map
    fun term => { start := (leaderStarts w)[k]!, stop := stopOf (leaderStarts w) w.size k, term }

theorem forIn_option_push {β : Type} (g : Nat → Option β) :
    ∀ (l : List Nat) (acc : Array β) (f : Nat → Array β → Option (ForInStep (Array β))),
      (∀ k s, f k s = (g k).map fun b => .yield (s.push b)) →
      forIn l acc f = (l.mapM g).map fun bs => acc ++ bs.toArray
  | [], acc, f, _ => by simp
  | a :: l, acc, f, h => by
      rw [List.forIn_cons, h a acc, List.mapM_cons]
      cases g a with
      | none => rfl
      | some b =>
          simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
          show forIn l (acc.push b) f = _
          rw [forIn_option_push g l (acc.push b) f h]
          cases l.mapM g <;> simp

theorem mapM_some {β γ : Type} (g : β → Option γ) :
    ∀ (l : List β) (bs : List γ), l.mapM g = some bs →
      bs.length = l.length ∧ ∀ i (h : i < l.length) (h' : i < bs.length), g l[i] = some bs[i]
  | [], bs, h => by simp at h; subst h; simp
  | a :: l, bs, h => by
      rw [List.mapM_cons] at h
      cases ha : g a with
      | none => simp [ha] at h
      | some b =>
          cases hl : l.mapM g with
          | none => simp [ha, hl] at h
          | some cs =>
              simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq] at h
              subst h
              obtain ⟨h1, h2⟩ := mapM_some g l cs hl
              refine ⟨by simp [h1], fun i hi hi' => ?_⟩
              cases i with
              | zero => simpa using ha
              | succ i => simpa using h2 i (by simpa using hi) (by simpa using hi')

theorem mapM_congr_map {β γ δ : Type} (g : β → Option γ) (g' : β → Option δ) (φ : γ → δ) :
    ∀ (l : List β), (∀ a ∈ l, g' a = (g a).map φ) → l.mapM g' = (l.mapM g).map (List.map φ)
  | [], _ => by simp
  | a :: l, h => by
      rw [List.mapM_cons, List.mapM_cons, h a (List.mem_cons_self ..),
        mapM_congr_map g g' φ l (fun b hb => h b (List.mem_cons_of_mem _ hb))]
      cases g a <;> cases l.mapM g <;> simp

/-- The graph `build` constructs: its blocks are `blockAt`. -/
theorem build_blocks {w : Array LinstrR} {G : CFG} (h : build w = some G) :
    ((List.range (leaderStarts w).size).mapM (blockAt w)).map List.toArray = some G.blocks ∧
      G.blockOf = blockIndex w.size (leaderStarts w) := by
  unfold build at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  rw [forIn_option_push (blockAt w) _ _ _ (fun k s => ?_)] at h
  · have hr : List.range' 0 [:(leaderStarts w).size].size = List.range (leaderStarts w).size := by
      generalize (leaderStarts w).size = n
      simp [Std.Legacy.Range.size, List.range_eq_range']
    rw [hr] at h
    cases hm : (List.range (leaderStarts w).size).mapM (blockAt w) with
    | none => simp [hm] at h
    | some bs =>
        simp only [hm, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
        obtain ⟨ps, -, hps⟩ := Option.bind_eq_some_iff.mp h
        simp only [Option.pure_def, Option.some.injEq] at hps
        subst hps
        simp [Array.mkEmpty]
  · clear h
    unfold blockAt targetOf stopOf nxOf
    generalize w[(if k + 1 < (leaderStarts w).size then (leaderStarts w)[k + 1]! else w.size) - 1]?
      = o
    rcases o with _ | x
    · rfl
    · cases x with
      | Lgoto p =>
          obtain ⟨a, l⟩ := p
          dsimp only [termOfLast]
          cases ((firstLabelPcs w)[l]?.bind fun pc => (blockIndex w.size (leaderStarts w))[pc]?) <;>
            rfl
      | Lcond c l =>
          dsimp only [termOfLast]
          cases ((firstLabelPcs w)[l]?.bind fun pc => (blockIndex w.size (leaderStarts w))[pc]?) <;>
            rfl
      | _ => rfl

theorem forIn_option_some {α β : Type} :
    ∀ (l : List α) (init : β) (f : α → β → Option (ForInStep β)),
      (∀ a b, ∃ r, f a b = some (.yield r)) → ∃ r, forIn l init f = some r
  | [], init, _, _ => ⟨init, rfl⟩
  | a :: l, init, f, h => by
      obtain ⟨r, hr⟩ := h a init
      rw [List.forIn_cons, hr]
      exact forIn_option_some l r f h

theorem bind_mk {P : Option (Array (List Nat))} (hP : ∃ r, P = some r) (bl : Array Block)
    (bo : Array Nat) :
    ∃ G : CFG, (P >>= fun ps => pure ({ blocks := bl, blockOf := bo, preds := ps } : CFG)) =
      some G ∧ G.blocks = bl ∧ G.blockOf = bo := by
  obtain ⟨r, rfl⟩ := hP
  exact ⟨_, rfl, rfl, rfl⟩

/-- `build` succeeds when every block does. -/
theorem build_of_blocks {w : Array LinstrR} {bs : List Block}
    (hm : (List.range (leaderStarts w).size).mapM (blockAt w) = some bs) :
    ∃ G, build w = some G ∧ G.blocks = bs.toArray ∧
      G.blockOf = blockIndex w.size (leaderStarts w) := by
  unfold build
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [forIn_option_push (blockAt w) _ _ _ (fun k s => ?_)]
  · have hr : List.range' 0 [:(leaderStarts w).size].size = List.range (leaderStarts w).size := by
      generalize (leaderStarts w).size = n
      simp [Std.Legacy.Range.size, List.range_eq_range']
    rw [hr, hm]
    simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
    refine Exists.imp (fun G h => ⟨h.1, by rw [h.2.1]; simp [Array.mkEmpty], h.2.2⟩)
      (bind_mk ?_ _ _)
    refine forIn_option_some _ _ _ fun a b => ?_
    obtain ⟨r, hr⟩ := forIn_option_some
      (((Array.mkEmpty (leaderStarts w).size ++ bs.toArray).getD a default).term.succs) b
      (fun (x : Nat) (y : Array (List Nat)) =>
        (pure (ForInStep.yield (y.modify x (· ++ [a]))) : Option _))
      (fun x y => ⟨_, rfl⟩)
    exact ⟨r, by rw [hr]; rfl⟩
  · clear hm
    unfold blockAt targetOf stopOf nxOf
    generalize w[(if k + 1 < (leaderStarts w).size then (leaderStarts w)[k + 1]! else w.size) - 1]?
      = o
    rcases o with _ | x
    · rfl
    · cases x with
      | Lgoto p =>
          obtain ⟨a, l⟩ := p
          dsimp only [termOfLast]
          cases ((firstLabelPcs w)[l]?.bind fun pc => (blockIndex w.size (leaderStarts w))[pc]?) <;>
            rfl
      | Lcond c l =>
          dsimp only [termOfLast]
          cases ((firstLabelPcs w)[l]?.bind fun pc => (blockIndex w.size (leaderStarts w))[pc]?) <;>
            rfl
      | _ => rfl

theorem getElem!_toArray_eq {l : List Nat} {i : Nat} (h : i < l.length) :
    l.toArray[i]! = l[i] := by
  rw [getElem!_pos l.toArray i (by simpa using h)]
  simp

theorem leaderStarts_strict (w : Array LinstrR) :
    ∀ i j, i < j → j < (leaderStarts w).size →
      (leaderStarts w)[i]! < (leaderStarts w)[j]! := by
  intro i j hij hj
  rw [leaderStarts_eq] at hj ⊢
  simp only [List.size_toArray] at hj
  rw [getElem!_toArray_eq (by omega), getElem!_toArray_eq hj]
  exact List.pairwise_iff_getElem.mp ((List.pairwise_lt_range).filter _) i j (by omega) hj hij

theorem leaderStarts_mono (w : Array LinstrR) {i j : Nat} (hij : i ≤ j)
    (hj : j < (leaderStarts w).size) : (leaderStarts w)[i]! ≤ (leaderStarts w)[j]! := by
  rcases Nat.eq_or_lt_of_le hij with rfl | h
  · exact le_refl _
  · exact Nat.le_of_lt (leaderStarts_strict w i j h hj)

theorem leaderStarts_get (w : Array LinstrR) {k : Nat} (hk : k < (leaderStarts w).size) :
    (leaderStarts w)[k]! < w.size ∧ isLeader w (leaderStarts w)[k]! = true := by
  rw [leaderStarts_eq] at hk ⊢
  simp only [List.size_toArray] at hk
  rw [getElem!_toArray_eq hk]
  have := List.getElem_mem hk
  simp only [List.mem_filter, List.mem_range] at this
  exact this

theorem leaderStarts_of_leader (w : Array LinstrR) {q : Nat} (hq : q < w.size)
    (hl : isLeader w q = true) : ∃ j, j < (leaderStarts w).size ∧ (leaderStarts w)[j]! = q := by
  have hm : q ∈ (List.range w.size).filter (isLeader w) := by simp [hq, hl]
  obtain ⟨j, hj, he⟩ := List.getElem_of_mem hm
  refine ⟨j, by rw [leaderStarts_eq]; simpa using hj, ?_⟩
  rw [leaderStarts_eq, getElem!_toArray_eq hj, he]

theorem leaderStarts_zero (w : Array LinstrR) (hn : 0 < w.size) :
    0 < (leaderStarts w).size ∧ (leaderStarts w)[0]! = 0 := by
  obtain ⟨j, hj, he⟩ := leaderStarts_of_leader w hn (by unfold isLeader; simp)
  refine ⟨by omega, ?_⟩
  have := leaderStarts_mono w (Nat.zero_le j) hj
  omega

theorem stopOf_spec (w : Array LinstrR) {k : Nat} (hk : k < (leaderStarts w).size) :
    (leaderStarts w)[k]! < stopOf (leaderStarts w) w.size k ∧
      stopOf (leaderStarts w) w.size k ≤ w.size ∧
      ∀ q, (leaderStarts w)[k]! < q → q < stopOf (leaderStarts w) w.size k →
        isLeader w q = false := by
  have hg := leaderStarts_get w hk
  unfold stopOf
  split
  · rename_i h1
    have h2 := leaderStarts_strict w k (k + 1) (by omega) h1
    have h3 := (leaderStarts_get w h1).1
    refine ⟨h2, by omega, fun q hq1 hq2 => ?_⟩
    cases hl : isLeader w q
    · rfl
    · obtain ⟨j, hj, rfl⟩ := leaderStarts_of_leader w (by omega) hl
      rcases Nat.lt_or_ge k j with hkj | hkj
      · have := leaderStarts_mono w (show k + 1 ≤ j by omega) hj
        omega
      · have := leaderStarts_mono w hkj hk
        omega
  · rename_i h1
    refine ⟨hg.1, le_refl _, fun q hq1 hq2 => ?_⟩
    cases hl : isLeader w q
    · rfl
    · obtain ⟨j, hj, rfl⟩ := leaderStarts_of_leader w hq2 hl
      have hkj : j ≤ k := by omega
      have := leaderStarts_mono w hkj hk
      omega

end Build

/-! ## 9. The graph of an expanded body -/

section Expand

variable {α : Type} {s : α → LinstrR} {g : α → List LinstrR} {M : List α}

/-- The image of a block under an expansion. -/
def shiftB (g : α → List LinstrR) (M : List α) (b : Block) : Block :=
  { start := xpos g M b.start, stop := xpos g M b.stop, term := b.term }

theorem ExpandOk.lastInstr (hE : ExpandOk s g M) {k : Nat}
    (hk : k < (leaderStarts (M.map s).toArray).size) :
    (M.flatMap g)[xpos g M (stopOf (leaderStarts (M.map s).toArray) M.length k) - 1]? =
        (M.map s)[stopOf (leaderStarts (M.map s).toArray) M.length k - 1]? ∨
      ∃ x y, (M.map s)[stopOf (leaderStarts (M.map s).toArray) M.length k - 1]? = some x ∧
        (M.flatMap g)[xpos g M (stopOf (leaderStarts (M.map s).toArray) M.length k) - 1]? =
          some y ∧ isTermR x = false ∧ isTermR y = false := by
  obtain ⟨h1, h2, h3⟩ := stopOf_spec (M.map s).toArray hk
  obtain ⟨hlt, hL⟩ := leaderStarts_get (M.map s).toArray hk
  simp only [List.size_toArray, List.length_map] at h1 h2 h3 hlt
  generalize stopOf (leaderStarts (M.map s).toArray) M.length k = stop at h1 h2 h3 ⊢
  generalize (leaderStarts (M.map s).toArray)[k]! = st at h1 h2 h3 hlt hL
  have hpc : stop - 1 < M.length := by omega
  have hx : (M.map s)[stop - 1]? = some (s M[stop - 1]) := by simp [hpc]
  have hstop : stop = stop - 1 + 1 := by omega
  cases hc : (isTermR (s M[stop - 1]) || isLabelR (s M[stop - 1]))
  · have hst := hE.xpos_strict (by omega) hL h1
    have hp : xpos g M stop - 1 < (M.flatMap g).length := by
      have := xpos_le g M stop; omega
    obtain ⟨pc, hpcM, e1, e2, e3, e4⟩ := getElem?_flatMap_chunk g hp
    cases hy : (g M[pc])[xpos g M stop - 1 - xpos g M pc]? with
    | none => rw [List.getElem?_eq_none_iff] at hy; omega
    | some y =>
          refine Or.inr ⟨_, y, hx, by rw [e4, hy], ?_, ?_⟩
          · simp only [Bool.or_eq_false_iff] at hc; exact hc.1
          · cases hty : isTermR y
            · rfl
            · exfalso
              obtain ⟨hi, rfl, hgc⟩ := hE.ctl hpcM hy (by simp [hty])
              rw [hgc, List.length_singleton] at e3
              have hpcs : pc < stop := by
                by_contra hcon
                have := xpos_mono g M (Nat.le_of_not_lt hcon)
                omega
              have hne : pc ≠ stop - 1 := by
                rintro rfl
                simp [hty] at hc
              have hsp : st < pc + 1 := by
                by_contra hcon
                have := xpos_mono g M (Nat.le_of_not_lt hcon)
                omega
              have := h3 (pc + 1) hsp (by omega)
              rw [isLeader_toArray] at this
              simp [List.getElem?_eq_getElem hpcM, hty] at this
  · left
    have hg := hE.1 _ (List.getElem_mem hpc) hc
    have e := xpos_succ g hpc
    rw [hg, List.length_singleton, ← hstop] at e
    rw [e, Nat.add_sub_cancel, hx]
    have := getElem?_xpos_lt g hpc (i := 0) (by rw [hg]; simp)
    rw [Nat.add_zero] at this
    rw [this, hg]
    rfl

theorem bIx_unique {S : Array Nat} (hS : ∀ i j, i < j → j < S.size → S[i]! < S[j]!) {j b : Nat}
    (hj : j < S.size) (h : BIx S (S[j]! + 1) b) : b = j := by
  obtain ⟨h1, h2⟩ := h
  rcases Nat.lt_trichotomy b j with hb | hb | hb
  · have := h2 (by omega)
    rcases Nat.eq_or_lt_of_le (show b + 1 ≤ j by omega) with e | e
    · rw [e] at this; omega
    · have := hS (b + 1) j e hj; omega
  · exact hb
  · have := (h1 b (by omega) (le_refl _))
    have := hS j b hb this.1
    omega

theorem blockIndex_at_start (w : Array LinstrR) {j : Nat} (hj : j < (leaderStarts w).size) :
    (blockIndex w.size (leaderStarts w))[(leaderStarts w)[j]!]? = some j := by
  obtain ⟨hsz, hspec⟩ := blockIndex_spec (leaderStarts_strict w) w.size
  have hlt := (leaderStarts_get w hj).1
  have hb := bIx_unique (leaderStarts_strict w) hj (hspec _ hlt)
  rw [Array.getElem?_eq_getElem (by omega), ← getElem!_pos _ _ (by omega), hb]

theorem getElem!_map_nat {S : Array Nat} {f : Nat → Nat} {k : Nat} (hk : k < S.size) :
    (S.map f)[k]! = f S[k]! := by
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_map, getElem!_pos S k hk]

theorem ExpandOk.target (hE : ExpandOk s g M) (l : LLabel) :
    targetOf (M.flatMap g).toArray l = targetOf (M.map s).toArray l := by
  unfold targetOf
  rw [firstLabelPcs_eq, firstLabelPcs_eq, List.toList_toArray, List.toList_toArray,
    findLabel_expand l M hE.1 hE.2.1]
  cases hf : JasminLsemLabeled.findLabel l (M.map s) with
  | none => rfl
  | some pc =>
      simp only [Option.map_some, Option.bind_some]
      obtain ⟨x, hx, hl⟩ := JasminLsemLabeled.findLabel_sound l _ pc hf
      have hpc : pc < (M.map s).length := (List.getElem?_eq_some_iff.mp hx).1
      have hL : isLeader (M.map s).toArray pc = true := by
        rw [isLeader_toArray, hx]
        cases x <;> simp_all [JasminLsemLabeled.isLabel, isLabelR]
      obtain ⟨j, hj, rfl⟩ := leaderStarts_of_leader _ (by simpa using hpc) hL
      rw [blockIndex_at_start _ hj]
      have hS' := hE.leaderStarts_expand
      have hj' : j < (leaderStarts (M.flatMap g).toArray).size := by rw [hS']; simpa using hj
      have := blockIndex_at_start (M.flatMap g).toArray hj'
      rw [hS', getElem!_map_nat hj] at this
      rwa [hS']

theorem termOfLast_congr {target : LLabel → Option Nat} {nx : Option Nat}
    {o o' : Option LinstrR}
    (h : o' = o ∨ ∃ x y, o = some x ∧ o' = some y ∧ isTermR x = false ∧ isTermR y = false) :
    termOfLast target nx o' = termOfLast target nx o := by
  rcases h with rfl | ⟨x, y, rfl, rfl, hx, hy⟩
  · rfl
  · rw [termOfLast_fall hx, termOfLast_fall hy]

/-- **The blocks of an expanded body** are the images of the blocks of the source. -/
theorem ExpandOk.blockAt (hE : ExpandOk s g M) {k : Nat}
    (hk : k < (leaderStarts (M.map s).toArray).size) :
    OwnedLprogTV.blockAt (M.flatMap g).toArray k =
      (OwnedLprogTV.blockAt (M.map s).toArray k).map (shiftB g M) := by
  have hS' := hE.leaderStarts_expand
  have ht : targetOf (M.flatMap g).toArray = targetOf (M.map s).toArray := funext hE.target
  have hstop : stopOf (leaderStarts (M.flatMap g).toArray) (M.flatMap g).toArray.size k =
      xpos g M (stopOf (leaderStarts (M.map s).toArray) M.length k) := by
    rw [hS']
    unfold stopOf
    simp only [Array.size_map]
    split
    · rename_i h; exact getElem!_map_nat h
    · simp [xpos_of_le g (le_refl _)]
  have hnx : nxOf (leaderStarts (M.flatMap g).toArray) k = nxOf (leaderStarts (M.map s).toArray) k := by
    rw [hS']; simp [nxOf]
  have hst : (leaderStarts (M.flatMap g).toArray)[k]! = xpos g M (leaderStarts (M.map s).toArray)[k]! := by
    rw [hS']; exact getElem!_map_nat hk
  unfold OwnedLprogTV.blockAt
  rw [ht, hnx, hstop, hst, List.getElem?_toArray, List.getElem?_toArray,
    termOfLast_congr (hE.lastInstr hk)]
  simp only [List.size_toArray, List.length_map]
  cases termOfLast (targetOf (M.map s).toArray) (nxOf (leaderStarts (M.map s).toArray) k)
    (M.map s)[stopOf (leaderStarts (M.map s).toArray) M.length k - 1]? <;> rfl

end Expand

/-! ## 10. Validation of the graph of an expanded body -/

section Valid

theorem blockAt_some {w : Array LinstrR} {k : Nat} {b : Block} (h : blockAt w k = some b) :
    b.start = (leaderStarts w)[k]! ∧ b.stop = stopOf (leaderStarts w) w.size k := by
  unfold blockAt at h
  cases ht : termOfLast (targetOf w) (nxOf (leaderStarts w) k)
    w[stopOf (leaderStarts w) w.size k - 1]? with
  | none => rw [ht] at h; cases h
  | some T => rw [ht] at h; cases h; exact ⟨rfl, rfl⟩

theorem build_blk {w : Array LinstrR} {G : CFG} (h : build w = some G) :
    G.blocks.size = (leaderStarts w).size ∧
      ∀ k, k < G.blocks.size → blockAt w k = some (G.blk k) := by
  obtain ⟨hb, -⟩ := build_blocks h
  cases hm : (List.range (leaderStarts w).size).mapM (blockAt w) with
  | none => rw [hm] at hb; cases hb
  | some bs =>
      rw [hm] at hb
      simp only [Option.map_some, Option.some.injEq] at hb
      obtain ⟨hl, hall⟩ := mapM_some _ _ _ hm
      have hsz : G.blocks.size = (leaderStarts w).size := by rw [← hb]; simp [hl]
      refine ⟨hsz, fun k hk => ?_⟩
      have := hall k (by simp; omega) (by rw [hl]; simp; omega)
      simp only [List.getElem_range] at this
      rw [this]
      congr 1
      simp [CFG.blk, ← hb, Array.getD, show k < bs.length by rw [hl]; simp; omega]

/-- The graph `build` constructs sends every index to a block containing it. -/
theorem blockOfOk_of_build {w : Array LinstrR} {G : CFG} (h : build w = some G) :
    blockOfOk w G = true := by
  obtain ⟨-, hbo⟩ := build_blocks h
  obtain ⟨hsz, hblk⟩ := build_blk h
  obtain ⟨hs, hspec⟩ := blockIndex_spec (leaderStarts_strict w) w.size
  simp only [blockOfOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨by rw [hbo, hs], fun pc hpc => ?_⟩
  obtain ⟨hn0, hz⟩ := leaderStarts_zero w (by omega)
  have hb : G.blockOf.getD pc 0 = (blockIndex w.size (leaderStarts w))[pc]! := by
    rw [hbo, Array.getD, dite_eq_left (by omega), getElem!_pos _ _ (by omega)]
    rfl
  rw [hb]
  generalize hbv : (blockIndex w.size (leaderStarts w))[pc]! = b
  have hB := hspec pc hpc
  rw [hbv] at hB
  obtain ⟨h1, h2⟩ := hB
  have hbn : b < (leaderStarts w).size := by
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · exact hn0
    · exact (h1 b hb0 (le_refl _)).1
  obtain ⟨e1, e2⟩ := blockAt_some (hblk b (by omega))
  refine ⟨⟨by omega, ?_⟩, ?_⟩
  · rw [e1]
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · rw [hz]; exact Nat.zero_le _
    · have := (h1 b hb0 (le_refl _)).2; omega
  · rw [e2]
    unfold stopOf
    split
    · rename_i hb1; have := h2 hb1; omega
    · exact hpc

variable {α : Type} {s : α → LinstrR} {g : α → List LinstrR} {M : List α}

theorem termOk_expand {G G' : CFG} {k : Nat} {T : Term} {o o' : Option LinstrR}
    (hsz : G'.blocks.size = G.blocks.size)
    (hblk : ∀ t, t < G.blocks.size → (G'.blk t).start = xpos g M (G.blk t).start)
    (hfind : ∀ l, JasminLsemLabeled.findLabel l (M.flatMap g) =
      (JasminLsemLabeled.findLabel l (M.map s)).map (xpos g M))
    (h : termOk (M.map s) G k T o = true)
    (ho : o' = o ∨ ∃ x y, o = some x ∧ o' = some y ∧ isTermR x = false ∧ isTermR y = false) :
    termOk (M.flatMap g) G' k T o' = true := by
  have hnext : G'.next k = G.next k := by simp [CFG.next, hsz]
  rcases ho with rfl | ⟨x, y, rfl, rfl, hx, hy⟩
  · unfold termOk at h ⊢
    split at h <;> (try simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢)
    all_goals first
      | exact ⟨by omega, by rw [hfind, h.2, Option.map_some, hblk _ h.1]⟩
      | exact ⟨⟨by omega, by rw [hfind, h.1.2, Option.map_some, hblk _ h.1.1]⟩,
          by rw [hnext]; exact h.2⟩
      | exact ⟨h.1, by rw [hnext]; exact h.2⟩
      | exact absurd h (by simp)
  · cases T with
    | fall nx =>
        simp only [termOk, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h ⊢
        exact ⟨hy, by rw [hnext]; exact h.2⟩
    | goto t => cases x <;> simp_all [termOk, isTermR]
    | cond t nx => cases x <;> simp_all [termOk, isTermR]
    | ret => cases x <;> simp_all [termOk, isTermR]

theorem ExpandOk.inner (hE : ExpandOk s g M) {st stp : Nat}
    (hin : ∀ pc i, st ≤ pc → pc + 1 < stp → (M.map s)[pc]? = some i → isTermR i = false)
    {p : Nat} (hp1 : xpos g M st ≤ p) (hp2 : p + 1 < xpos g M stp) {y : LinstrR}
    (hy : (M.flatMap g)[p]? = some y) : isTermR y = false := by
  have hp : p < (M.flatMap g).length := (List.getElem?_eq_some_iff.mp hy).1
  obtain ⟨pc, hpc, e1, e2, e3, e4⟩ := getElem?_flatMap_chunk g hp
  rw [e4] at hy
  cases hty : isTermR y
  · rfl
  · obtain ⟨hi, rfl, hgc⟩ := hE.ctl hpc hy (by simp [hty])
    rw [hgc, List.length_singleton] at e3
    have h1 : st ≤ pc := by
      by_contra hc
      have := xpos_mono g M (show pc + 1 ≤ st by omega)
      omega
    have h2 : pc + 1 < stp := by
      by_contra hc
      have := xpos_mono g M (show stp ≤ pc + 1 by omega)
      omega
    have := hin pc (s M[pc]) h1 h2 (by simp [hpc])
    rw [hty] at this
    cases this

/-- **The graph of an expanded body.** If `cfgOf` accepts a body, it accepts every
    control-preserving expansion of it (`ExpandOk`), with the same number of blocks, the same
    terminators, and each block moved to the positions of its chunks. -/
theorem ExpandOk.cfgOf (hE : ExpandOk s g M) {G : CFG}
    (hG : AllocCheck.LcmdCFG.cfgOf (M.map s) = some G) :
    ∃ G', AllocCheck.LcmdCFG.cfgOf (M.flatMap g) = some G' ∧
      G'.blocks = G.blocks.map (shiftB g M) := by
  have hw := cfgOf_wf hG
  have hbG : build (M.map s).toArray = some G := by
    unfold AllocCheck.LcmdCFG.cfgOf at hG
    dsimp only at hG
    split at hG
    · rename_i G0 hb; split at hG
      · cases hG; exact hb
      · cases hG
    · cases hG
  obtain ⟨hszG, hblkG⟩ := build_blk hbG
  obtain ⟨hbs, -⟩ := build_blocks hbG
  have hS' := hE.leaderStarts_expand
  have hnb : (leaderStarts (M.flatMap g).toArray).size = (leaderStarts (M.map s).toArray).size := by
    rw [hS', Array.size_map]
  cases hm : (List.range (leaderStarts (M.map s).toArray).size).mapM
      (OwnedLprogTV.blockAt (M.map s).toArray) with
  | none => rw [hm] at hbs; cases hbs
  | some bs =>
      rw [hm] at hbs
      simp only [Option.map_some, Option.some.injEq] at hbs
      have hm' : (List.range (leaderStarts (M.flatMap g).toArray).size).mapM
          (OwnedLprogTV.blockAt (M.flatMap g).toArray) = some (bs.map (shiftB g M)) := by
        rw [hnb, mapM_congr_map _ _ (shiftB g M) _ (fun k hk => hE.blockAt (List.mem_range.mp hk)),
          hm]
        rfl
      obtain ⟨G', hb', hbl', -⟩ := build_of_blocks hm'
      have hGb : G'.blocks = G.blocks.map (shiftB g M) := by rw [hbl', ← hbs]; simp
      refine ⟨G', ?_, hGb⟩
      have hsz : G'.blocks.size = G.blocks.size := by rw [hGb, Array.size_map]
      have hblk : ∀ t, t < G.blocks.size → G'.blk t = shiftB g M (G.blk t) := by
        intro t ht
        simp [CFG.blk, hGb, Array.getD, ht]
      have hfind := fun l => findLabel_expand (s := s) (g := g) l M hE.1 hE.2.1
      unfold AllocCheck.LcmdCFG.cfgOf
      dsimp only
      rw [hb']
      dsimp only
      rw [ite_eq_left]
      simp only [wf, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hw ⊢
      obtain ⟨⟨⟨⟨h0, hbk⟩, -⟩, hbar⟩, hdup⟩ := hw
      refine ⟨⟨⟨⟨?_, fun k hk => ?_⟩, blockOfOk_of_build hb'⟩, ?_⟩, ?_⟩
      · rw [hsz]
        split
        · rename_i h00
          rw [ite_eq_left h00] at h0
          simp only [decide_eq_true_eq, List.size_toArray, List.length_map] at h0 ⊢
          have hM : M = [] := List.length_eq_zero_iff.mp h0
          subst hM; rfl
        · rename_i h00
          rw [ite_eq_right h00] at h0
          simp only [decide_eq_true_eq] at h0 ⊢
          rw [hblk 0 (by omega)]
          simp [shiftB, h0, xpos_zero]
      · rw [hsz] at hk
        have hF := blockFacts hG hk
        obtain ⟨e1, e2⟩ := blockAt_some (hblkG k hk)
        have hkS : k < (leaderStarts (M.map s).toArray).size := by omega
        have hL := (leaderStarts_get _ hkS).2
        have hlt := (leaderStarts_get _ hkS).1
        simp only [List.size_toArray, List.length_map] at e2 hlt
        unfold AllocCheck.LcmdCFG.blockOk
        rw [hblk k hk]
        simp only [shiftB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
          List.mem_range'_1, List.size_toArray, Bool.not_eq_true']
        refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, fun p hp => ?_⟩, ?_⟩
        · apply decide_eq_true
          have h := hE.xpos_strict (by simpa using hlt) hL (show _ < (G.blk k).stop by
            rw [← e1]; exact hF.lt)
          rwa [← e1] at h
        · exact xpos_le g M _
        · have hs := hF.stop_eq
          simp only [List.length_map] at hs
          unfold CFG.nextStart at hs ⊢
          have hnx : G'.next k = G.next k := by simp [CFG.next, hsz]
          rw [hnx, hs]
          split
          · rename_i k' hk'
            have : k' < G.blocks.size := by
              unfold CFG.next at hk'; split at hk' <;> simp_all
            rw [hblk k' this]; rfl
          · exact xpos_of_le g (le_refl _)
        · cases hy : (M.flatMap g).toArray[p]? with
          | none => rfl
          | some y =>
              rw [List.getElem?_toArray] at hy
              simp only [Option.any_some]
              have := hE.inner (st := (G.blk k).start) (stp := (G.blk k).stop)
                (fun pc i h1 h2 h3 => hF.inner pc i h1 h2 h3) (by omega) (by omega) hy
              simp [this]
        · have hlast := hE.lastInstr hkS
          rw [← e2] at hlast
          rw [List.getElem?_toArray]
          exact termOk_expand hsz (fun t ht => by rw [hblk t ht]; rfl) hfind hF.term hlast
      · have hbar' : ∀ a ∈ M, isBarredR (s a) = false := by simpa using hbar
        simp only [List.any_toArray, List.any_eq_false, Bool.not_eq_true]
        intro y hy
        obtain ⟨a, ha, hya⟩ := List.mem_flatMap.mp hy
        cases hc : (isTermR (s a) || isLabelR (s a))
        · have := hE.2.1 a ha hc y hya
          simp only [straightR, Bool.and_eq_true, Bool.not_eq_true'] at this
          exact this.2
        · rw [hE.1 a ha hc, List.mem_singleton] at hya
          subst hya
          exact hbar' a ha
      · rw [hasDupLabel_filter, filter_label_expand M hE.1 hE.2.1, ← hasDupLabel_filter]
        exact hdup

theorem cfgOf_not_barred {wl : List LinstrR} {G : CFG}
    (hG : AllocCheck.LcmdCFG.cfgOf wl = some G) : ∀ x ∈ wl, isBarredR x = false := by
  have hw := cfgOf_wf hG
  simp only [wf, Bool.and_eq_true, Bool.not_eq_true'] at hw
  have := hw.1.2
  simpa using this

end Valid

/-! ## 11. Completeness for control-preserving passes -/

section Complete

/-- The live sets `ownedCheckM` computes for two bodies form a post-fixpoint. -/
def LiveConv (outs : List String) (B B' : List LinstrRM) : Prop :=
  ∀ G G', cfgOf (B.map Prod.fst) = some G → cfgOf (B'.map Prod.fst) = some G' →
    LivePost outs B G (runsOf B B' G G') (liveIter outs B G (runsOf B B' G G')
      (4 * G.blocks.size + 64) (Array.replicate G.blocks.size ([], false)))

/-- `LiveCov` as a decision. -/
def liveCovB (n m : List String × Bool) : Bool := m.1.all (n.1.contains ·) && (!m.2 || n.2)

theorem liveCovB_spec {n m : List String × Bool} (h : liveCovB n m = true) : LiveCov n m := by
  simp only [liveCovB, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1, fun hm => h.2.resolve_left (by simp [hm])⟩

/-- `LiveConv` as a decision. -/
def liveConvB (outs : List String) (B B' : List LinstrRM) : Bool :=
  match cfgOf (B.map Prod.fst), cfgOf (B'.map Prod.fst) with
  | some G, some G' =>
      let R := runsOf B B' G G'
      let L := liveIter outs B G R (4 * G.blocks.size + 64)
        (Array.replicate G.blocks.size ([], false))
      (List.range G.blocks.size).all fun k => liveCovB (L.getD k ([], false)) (needAt outs B G R L k)
  | _, _ => false

theorem liveConvB_spec {outs : List String} {B B' : List LinstrRM}
    (h : liveConvB outs B B' = true) : LiveConv outs B B' := by
  intro G G' hG hG' k hk
  unfold liveConvB at h
  rw [hG, hG'] at h
  simp only [List.all_eq_true, List.mem_range] at h
  exact liveCovB_spec (h k hk)

theorem termOk_nonfall {wl : List LinstrR} {G : CFG} {k : Nat} {T : Term} {x : LinstrR}
    (h : termOk wl G k T (some x) = true) (hT : isFallT T = false) : isTermR x = true := by
  cases T <;> cases x <;> simp_all [termOk, isTermR, isFallT]

theorem xpos_map_fst {α : Type} (f : α → List LinstrRM) (M : List α) (pc : Nat) :
    xpos (fun a => (f a).map Prod.fst) M pc = xpos f M pc := by
  simp [xpos, List.length_flatMap]

variable {α : Type}

/-- **Completeness for a control-preserving pass, block by block.** Let `M` be the items of
    a body, `src a` the source instruction of an item and `f a` its chunk in the rewritten body.
    When the chunks keep terminators and labels as they are, turn every other instruction into
    straight-line instructions and keep a non-empty chunk at every leader, `cfgOf` accepts the
    source, the runs of every block agree over the shared table (`Res`) and lie inside the
    fragment, and the live sets `ownedCheckM` computes form a post-fixpoint, `ownedCheckM`
    accepts the source against the rewritten body. -/
theorem ownedCheckM_complete_of_blockwise (outs : List String) (src : α → LinstrRM)
    (f : α → List LinstrRM) (M : List α)
    (hctl : ∀ a ∈ M, (isTermR (src a).1 || isLabelR (src a).1) = true → f a = [src a])
    (hstr : ∀ a ∈ M, (isTermR (src a).1 || isLabelR (src a).1) = false →
      ∀ y ∈ f a, straightR y.1 = true)
    (hlead : ∀ pc (h : pc < M.length),
      isLeader (M.map fun a => (src a).1).toArray pc = true → f M[pc] ≠ [])
    {G : CFG} (hG : cfgOf ((M.map src).map Prod.fst) = some G) (hne : M ≠ [])
    (hres : ∀ k, k < G.blocks.size → (G.blk k).term ≠ .ret →
      Res (tRun (((M.drop (G.blk k).start).take
          (bstopOf (G.blk k).term (G.blk k) - (G.blk k).start)).map src) SSt.start Tbl.empty).1
        (tRun (((M.drop (G.blk k).start).take
          (bstopOf (G.blk k).term (G.blk k) - (G.blk k).start)).map src) SSt.start Tbl.empty).2
        (tRun (((M.drop (G.blk k).start).take
          (bstopOf (G.blk k).term (G.blk k) - (G.blk k).start)).flatMap f) SSt.start
          (tRun (((M.drop (G.blk k).start).take
            (bstopOf (G.blk k).term (G.blk k) - (G.blk k).start)).map src) SSt.start
            Tbl.empty).1) ∧
      (tRun (((M.drop (G.blk k).start).take
          (bstopOf (G.blk k).term (G.blk k) - (G.blk k).start)).map src) SSt.start
          Tbl.empty).2 ≠ .unk)
    (hlive : LiveConv outs (M.map src) (M.flatMap f)) :
    ownedCheckM outs (M.map src) (M.flatMap f) = true := by
  set s : α → LinstrR := fun a => (src a).1 with hs_def
  set g : α → List LinstrR := fun a => (f a).map Prod.fst with hg_def
  have hBs : (M.map src).map Prod.fst = M.map s := by simp [hs_def]
  have hBg : (M.flatMap f).map Prod.fst = M.flatMap g := by simp [hg_def, List.map_flatMap]
  have hE : ExpandOk s g M := by
    refine ⟨fun a ha hc => by
        show (f a).map Prod.fst = [(src a).1]
        rw [hctl a ha hc]; rfl, fun a ha hc y hy => ?_,
      fun pc h hL => by simpa [hg_def] using hlead pc h hL⟩
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    exact hstr a ha hc z hz
  rw [hBs] at hG
  obtain ⟨G', hG', hGb⟩ := hE.cfgOf hG
  have hxp : ∀ pc, xpos g M pc = xpos f M pc := xpos_map_fst f M
  have hsz : G'.blocks.size = G.blocks.size := by rw [hGb, Array.size_map]
  have hblk : ∀ k, k < G.blocks.size → G'.blk k = shiftB g M (G.blk k) := by
    intro k hk
    simp [CFG.blk, hGb, Array.getD, hk]
  have hM0 : 0 < M.length := List.length_pos_iff.mpr hne
  have hF : ∀ k, k < G.blocks.size → BlockFacts (M.map s) G k := fun k hk => blockFacts hG hk
  have hnf : ∀ k, k < G.blocks.size → isFallT (G.blk k).term = false →
      ∃ h : (G.blk k).stop - 1 < M.length, isTermR (s M[(G.blk k).stop - 1]) = true := by
    intro k hk hT
    have ht := (hF k hk).term
    have hle := (hF k hk).le
    have hlt := (hF k hk).lt
    simp only [List.length_map] at hle
    have hp : (G.blk k).stop - 1 < M.length := by omega
    refine ⟨hp, ?_⟩
    rw [List.getElem?_map, List.getElem?_eq_getElem hp, Option.map_some] at ht
    exact termOk_nonfall ht hT
  have hsucc : ∀ k, k < G.blocks.size → isFallT (G.blk k).term = false →
      xpos f M (G.blk k).stop = xpos f M ((G.blk k).stop - 1) + 1 := by
    intro k hk hT
    obtain ⟨hp, ht⟩ := hnf k hk hT
    have hc : (isTermR (src M[(G.blk k).stop - 1]).1 ||
        isLabelR (src M[(G.blk k).stop - 1]).1) = true := by simp [hs_def] at ht; simp [ht]
    have e := xpos_succ f hp
    rw [hctl _ (List.getElem_mem hp) hc, List.length_singleton,
      Nat.sub_add_cancel (by have := (hF k hk).lt; omega)] at e
    exact e
  have hbstop : ∀ (T : Term) (b : Block), bstopOf T b = if isFallT T then b.stop else b.stop - 1 := by
    intro T b; cases T <;> rfl
  have hbody : ∀ k, k < G.blocks.size →
      bodyAt (M.map src) (G.blk k) (G.blk k).term =
        ((M.drop (G.blk k).start).take
          (bstopOf (G.blk k).term (G.blk k) - (G.blk k).start)).map src ∧
      bodyAt (M.flatMap f) (G'.blk k) (G.blk k).term =
        ((M.drop (G.blk k).start).take
          (bstopOf (G.blk k).term (G.blk k) - (G.blk k).start)).flatMap f := by
    intro k hk
    refine ⟨by simp [bodyAt, List.map_drop, List.map_take], ?_⟩
    have hlt := (hF k hk).lt
    have e : bstopOf (G.blk k).term (G'.blk k) = xpos f M (bstopOf (G.blk k).term (G.blk k)) := by
      rw [hblk k hk, hbstop, hbstop]
      cases hT : isFallT (G.blk k).term
      · simp only [Bool.false_eq_true, ↓reduceIte, shiftB]
        rw [hxp, hsucc k hk hT, Nat.add_sub_cancel]
      · simp [shiftB, hxp]
    have hle : (G.blk k).start ≤ bstopOf (G.blk k).term (G.blk k) := by
      rw [hbstop]; split <;> omega
    unfold bodyAt
    rw [e, hblk k hk]
    show ((M.flatMap f).drop (xpos g M (G.blk k).start)).take
      (xpos f M (bstopOf (G.blk k).term (G.blk k)) - xpos g M (G.blk k).start) = _
    rw [hxp]
    exact flatMap_slice f M hle
  refine ownedCheckM_of_blockRes outs (G := G) (G' := G') (by rw [hBs]; exact hG)
    (by rw [hBg]; exact hG') (by simpa using hne) ?_ hsz
    (fun k hk => by rw [hblk k hk]; rfl) ?_ ?_ ?_ ?_
  · intro h
    have h0 := hlead 0 hM0 (by rw [isLeader_toArray]; simp)
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
    have : f M[0] = [] := List.flatMap_eq_nil_iff.mp h _ (List.getElem_mem hM0)
    exact h0 this
  · intro k hk hT
    obtain ⟨hp, ht⟩ := hnf k hk hT
    rw [hblk k hk]
    show (M.flatMap f)[xpos g M (G.blk k).stop - 1]? = _
    rw [hxp, hsucc k hk hT, Nat.add_sub_cancel]
    have hc : (isTermR (src M[(G.blk k).stop - 1]).1 ||
        isLabelR (src M[(G.blk k).stop - 1]).1) = true := by simp [hs_def] at ht; simp [ht]
    have := getElem?_xpos_lt f hp (i := 0) (by rw [hctl _ (List.getElem_mem hp) hc]; simp)
    rw [Nat.add_zero] at this
    rw [this, hctl _ (List.getElem_mem hp) hc]
    simp [hp]
  · intro k hk hT
    rw [(hbody k hk).1, (hbody k hk).2]
    exact (hres k hk hT).1
  · intro k hk hT
    rw [(hbody k hk).1]
    exact (hres k hk hT).2
  · exact hlive G G' (by rw [hBs]; exact hG) (by rw [hBg]; exact hG')

end Complete

/-! ## 12. Two-address legalisation and dead immediate moves on bodies with several blocks -/

section Passes

theorem tiedOk_of_ctl {x : LinstrR} (h : (isTermR x || isLabelR x) = true) :
    TwoAddrLegalize.tiedOk x = true := by
  cases x <;> simp_all [isTermR, isLabelR, TwoAddrLegalize.tiedOk]

theorem straightR_of_not_ctl {x : LinstrR} (h : (isTermR x || isLabelR x) = false)
    (hb : isBarredR x = false) : straightR x = true := by
  simp only [Bool.or_eq_false_iff] at h
  simp [straightR, h.1, h.2, hb]

/-- **Completeness of the value checker for two-address legalisation, any number of
    blocks.** For a non-empty body whose graph `cfgOf` accepts, whose instructions satisfy
    `twoAddrWF`, whose block runs lie inside the described fragment, and for which the live
    sets `ownedCheckM` computes form a post-fixpoint, `ownedCheckM` accepts the body against
    its legalisation `TwoAddrLegalize.twoAddrBody`. -/
theorem twoAddr_ownedCheckM_complete_blocks (outs : List String) {tg : LinstrR → MemTag}
    (htg : TagFirstSrc tg) (body : Lcmd) (hne : body ≠ [])
    (hwf : ∀ i ∈ body, twoAddrWF i.li_i = true) {G : CFG}
    (hG : cfgOf ((typeBody tg body).map Prod.fst) = some G)
    (hfrag : ∀ k, k < G.blocks.size → (G.blk k).term ≠ .ret →
      symRun (bodyAt (typeBody tg body) (G.blk k) (G.blk k).term) SSt.start ≠ .unk)
    (hlive : LiveConv outs (typeBody tg body) (typeBody tg (TwoAddrLegalize.twoAddrBody body))) :
    ownedCheckM outs (typeBody tg body) (typeBody tg (TwoAddrLegalize.twoAddrBody body)) =
      true := by
  rw [twoAddrBody_typed tg body hwf] at hlive ⊢
  set M := typeBody tg body with hM
  have hB : ∀ p ∈ M, twoAddrWF p.1 = true ∧ p.2 = tg p.1 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    exact ⟨hwf i hi, rfl⟩
  have hbar := cfgOf_not_barred hG
  have hmap : M.map (fun p => p) = M := List.map_id' M
  have h := ownedCheckM_complete_of_blockwise outs (fun p => p) (twoAddrChunk tg) M
    (fun p hp hc => by simp [twoAddrChunk, tiedOk_of_ctl hc])
    (fun p hp hc => twoAddrChunk_straight tg
      (straightR_of_not_ctl hc (hbar _ (List.mem_map_of_mem hp))))
    (fun pc h _ => twoAddrChunk_ne_nil tg _) (by rw [hmap]; exact hG)
    (by simpa [hM, typeBody] using hne) (fun k hk hT => ⟨?_, ?_⟩) (by rw [hmap]; exact hlive)
  · rwa [hmap] at h
  · rw [List.map_id']
    refine tRun_lock (twoAddrChunk tg) _ (fun p hp => ?_) SSt.start SSt.start Tbl.empty _
      (SSt.Eqv.refl _) SSt.inv_start (Tbl.Sub.refl _)
    obtain ⟨hw, hτ⟩ := hB p (List.mem_of_mem_drop (List.mem_of_mem_take hp))
    obtain ⟨x, τ'⟩ := p
    simp only at hτ
    subst hτ
    exact chunk_twoAddr htg hw
  · rw [List.map_id', ne_eq, tRun_unk_iff]
    exact hfrag k hk hT

/-- The unmarked instructions of a marked body are its expansion that drops the marked ones. -/
theorem keptOf_eq_flatMap (B : List (LinstrRM × Bool)) :
    keptOf B = B.flatMap fun p => if p.2 then [] else [p.1] := by
  induction B with
  | nil => rfl
  | cons p B ih =>
      obtain ⟨i, b⟩ := p
      cases b <;> simp [keptOf] at ih ⊢ <;> exact ih

/-- **Completeness of the value checker for dropping dead immediate moves, any number of
    blocks.** For a non-empty marked body whose graph `cfgOf` accepts, whose marked
    instructions are straight-line instructions off the leaders, whose marks are dead immediate
    moves within every block (`dropOk`), whose block runs lie inside the fragment, and for
    which the live sets `ownedCheckM` computes form a post-fixpoint, `ownedCheckM` accepts the
    body against its unmarked instructions. -/
theorem dropOk_ownedCheckM_complete_blocks (outs : List String) (B : List (LinstrRM × Bool))
    (hne : B ≠ []) (hmk : ∀ p ∈ B, p.2 = true → straightR p.1.1 = true)
    (hlead : ∀ pc (h : pc < B.length),
      isLeader (B.map fun p => p.1.1).toArray pc = true → B[pc].2 = false)
    {G : CFG} (hG : cfgOf ((srcOf B).map Prod.fst) = some G)
    (hok : ∀ k, k < G.blocks.size → (G.blk k).term ≠ .ret →
      dropOk [] ((B.drop (G.blk k).start).take
        (bstopOf (G.blk k).term (G.blk k) - (G.blk k).start)) = true)
    (hfrag : ∀ k, k < G.blocks.size → (G.blk k).term ≠ .ret →
      symRun (bodyAt (srcOf B) (G.blk k) (G.blk k).term) SSt.start ≠ .unk)
    (hlive : LiveConv outs (srcOf B) (keptOf B)) :
    ownedCheckM outs (srcOf B) (keptOf B) = true := by
  have hsrc : srcOf B = B.map Prod.fst := rfl
  rw [hsrc] at hG hfrag hlive ⊢
  have hbar := cfgOf_not_barred hG
  rw [keptOf_eq_flatMap] at hlive ⊢
  have key := ownedCheckM_complete_of_blockwise (α := LinstrRM × Bool) outs Prod.fst
    (fun p => if p.2 then [] else [p.1]) B (G := G)
  have h1 : ∀ p ∈ B, (isTermR p.1.1 || isLabelR p.1.1) = true →
      (if p.2 then [] else [p.1]) = [p.1] := by
    intro p hp hc
    cases hb : p.2
    · rfl
    · have := hmk p hp hb
      simp only [straightR, Bool.and_eq_true, Bool.not_eq_true'] at this
      simp [this.1.1, this.1.2] at hc
  have h2 : ∀ p ∈ B, (isTermR p.1.1 || isLabelR p.1.1) = false →
      ∀ y ∈ (if p.2 then [] else [p.1]), straightR y.1 = true := by
    intro p hp hc y hy
    cases hb : p.2
    · rw [hb, ite_eq_right (by simp), List.mem_singleton] at hy
      subst hy
      exact straightR_of_not_ctl hc (hbar _ (List.mem_map_of_mem (List.mem_map_of_mem hp)))
    · rw [hb, ite_eq_left rfl] at hy; cases hy
  have h3 : ∀ pc (h : pc < B.length), isLeader (B.map fun p => p.1.1).toArray pc = true →
      (if B[pc].2 then [] else [B[pc].1]) ≠ [] := by
    intro pc h hL
    rw [hlead pc h hL]
    simp
  have h4 : ∀ k, k < G.blocks.size → (G.blk k).term ≠ .ret →
      Res (tRun (((B.drop (G.blk k).start).take
          (bstopOf (G.blk k).term (G.blk k) - (G.blk k).start)).map Prod.fst) SSt.start Tbl.empty).1
        (tRun (((B.drop (G.blk k).start).take
          (bstopOf (G.blk k).term (G.blk k) - (G.blk k).start)).map Prod.fst) SSt.start Tbl.empty).2
        (tRun (((B.drop (G.blk k).start).take
          (bstopOf (G.blk k).term (G.blk k) - (G.blk k).start)).flatMap
            (fun p => if p.2 then [] else [p.1])) SSt.start
          (tRun (((B.drop (G.blk k).start).take
            (bstopOf (G.blk k).term (G.blk k) - (G.blk k).start)).map Prod.fst) SSt.start
            Tbl.empty).1) ∧
      (tRun (((B.drop (G.blk k).start).take
          (bstopOf (G.blk k).term (G.blk k) - (G.blk k).start)).map Prod.fst) SSt.start
          Tbl.empty).2 ≠ .unk := by
    intro k hk hT
    refine ⟨?_, ?_⟩
    · rw [← keptOf_eq_flatMap]
      exact tRun_drop _ [] SSt.start SSt.start Tbl.empty _ (hok k hk hT)
        ⟨SSt.Same.refl _, fun _ _ => rfl⟩ SSt.inv_start (Tbl.Sub.refl _)
    · have := hfrag k hk hT
      rw [ne_eq, ← tRun_unk_iff] at this
      unfold bodyAt at this
      rwa [← List.map_drop, ← List.map_take] at this
  exact key h1 h2 h3 hG hne h4 hlive

end Passes

end CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
