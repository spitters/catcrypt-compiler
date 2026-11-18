/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Blake2
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Keccak
public import CatCrypt.Crypto.Jasmin.ChaCha20Block
public import CatCrypt.Crypto.Jasmin.ChaCha20QRSpecEq

/-!
# The ChaCha20 block function as a `jasminDialect` template

The ChaCha20 block function of RFC 8439 §2.3, `ChaCha20Block.chachaBlock`, as a straight-line
program of `jasminDialect` generated through the compiler of `HashTemplate.StraightLine` on
32-bit words. The program reads the sixteen words of the input state from one stack array,
binds the 80 quarter-rounds of the ten double rounds as let-bound word expressions (addition,
`xor`, and the left rotations by `16`, `12`, `8`, `7` as right rotations by `16`, `20`, `24`,
`25`), binds the sixteen words of the feed-forward, and stores them by register index into a
second stack array, the output array, which the program does not read. This is the form that
`compileRegion` accepts (`HashTemplate/AGENTS.md`), with the arguments of the narrow-width
kernel record of `HashTemplate/NarrowKernel`.

The positions of the eight quarter-rounds of a double round are those of the eight applications
of `G` in a BLAKE2 round, `blake2Quad`: the four columns, then the four diagonals.

## Main definitions

* `qrUpd`: the quarter-round at four positions of a state, as an update of the four positions.
* `chachaQrLets`, `chachaDRLets`, `chachaCoreLets`, `chachaLets`: the symbolic quarter-round,
  double round, ten double rounds, and block with its store list.
* `chachaInCtxt`, `chachaBlockBody`: the input context and the program.

## Main results

* `chachaBlockBody_value`: the program returns `ChaCha20Block.chachaBlock` of its input array,
  whatever the contents of the output array.
* `chachaBlockBody_events`: the program emits the same events at every two valuations, at
  leakage parameters with no variable-time operation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplate (LeakFixed)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open CatCrypt.Crypto.Jasmin.ChaCha20QR (quarterRound)
open CatCrypt.Crypto.SecureCompilation.CompileFromHaxChachaTie (rotL32_eq_rotateRight)
open CatCrypt.Crypto.Jasmin.ChaCha20Block (quarterRoundAt doubleRound chachaCore chachaBlock
  ChaChaState)
open Ctxt (Var Valuation)

/-! ## 1. The reference -/

/-- The quarter-round of RFC 8439 §2.1 at the positions `a`, `b`, `c`, `d` of the state `v`, as
    the update `upd4` of the four positions. -/
def qrUpd (v : Fin 16 → BitVec 32) (a b c d : Fin 16) : Fin 16 → BitVec 32 :=
  let r := quarterRound (v a) (v b) (v c) (v d)
  upd4 v a b c d r.1 r.2.1 r.2.2.1 r.2.2.2

/-- At four distinct positions the quarter-round `quarterRoundAt` is `qrUpd`. -/
theorem quarterRoundAt_eq_qrUpd (v : Fin 16 → BitVec 32) (a b c d : Fin 16) (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    quarterRoundAt v a b c d = qrUpd v a b c d := by
  funext i
  simp only [quarterRoundAt, qrUpd, upd4, ChaChaState.update, Function.update]
  grind

/-- A double round is the eight quarter-rounds at the positions `blake2Quad`. -/
theorem doubleRound_eq_foldl (v : ChaChaState) :
    doubleRound v = (List.finRange 8).foldl (fun v k => quarterRoundAt v (blake2Quad k).1
      (blake2Quad k).2.1 (blake2Quad k).2.2.1 (blake2Quad k).2.2.2) v := by
  rfl

/-! ## 2. The symbolic block function -/

/-- The quarter-round on the words numbered `st a`, `st b`, `st c`, `st d`: binds the eight
    intermediate words and returns the numbers of the new state. -/
def chachaQrLets (st : Fin 16 → Nat) (a b c d : Fin 16) (s : LetSt 32) :
    (Fin 16 → Nat) × LetSt 32 :=
  let (a1, s) := s.push (.bin .add (.var (st a)) (.var (st b)))
  let (d1, s) := s.push (.rotr 16 (.bin .xor (.var (st d)) (.var a1)))
  let (c1, s) := s.push (.bin .add (.var (st c)) (.var d1))
  let (b1, s) := s.push (.rotr 20 (.bin .xor (.var (st b)) (.var c1)))
  let (a2, s) := s.push (.bin .add (.var a1) (.var b1))
  let (d2, s) := s.push (.rotr 24 (.bin .xor (.var d1) (.var a2)))
  let (c2, s) := s.push (.bin .add (.var c1) (.var d2))
  let (b2, s) := s.push (.rotr 25 (.bin .xor (.var b1) (.var c2)))
  (upd4 st a b c d a2 b2 c2 d2, s)

/-- The double round on the state numbered `q.1`: the quarter-rounds at the positions
    `blake2Quad`. -/
def chachaDRLets (q : (Fin 16 → Nat) × LetSt 32) : (Fin 16 → Nat) × LetSt 32 :=
  (List.finRange 8).foldl (fun q k => chachaQrLets q.1 (blake2Quad k).1 (blake2Quad k).2.1
    (blake2Quad k).2.2.1 (blake2Quad k).2.2.2 q.2) q

/-- The ten double rounds on the input words numbered `0, …, 15`, with the let-bound words
    from the word numbered `16`. -/
def chachaCoreLets : (Fin 16 → Nat) × LetSt 32 :=
  (List.range 10).foldl (fun q _ => chachaDRLets q) (fun i => i.val, ⟨16, []⟩)

/-- The feed-forward word of the index `i`: the word numbered `st i` plus the input word
    numbered `i`. -/
def chachaFeedE (st : Fin 16 → Nat) (i : Fin 16) : WExp 32 :=
  .bin .add (.var (st i)) (.var i.val)

/-- **The symbolic ChaCha20 block function**: the store list, the index `i` receiving the
    feed-forward word of `i`, and the let-list of the ten double rounds and the feed-forward
    words. -/
def chachaLets : List (Nat × Nat) × LetSt 32 :=
  ((List.finRange 16).map fun i => (i.val, chachaCoreLets.2.next + i.val),
    keccakTPushAll (List.ofFn (chachaFeedE chachaCoreLets.1)) chachaCoreLets.2)

/-! ## 3. The program -/

/-- The input context of the block function: the input array of the sixteen state words and
    the output array of sixteen words. -/
abbrev chachaInCtxt : Ctxt jasminDialect := [.stackArr 32 16, .stackArr 32 16]

/-- **The ChaCha20 block function as a `jasminDialect` program**: the loads of the sixteen
    words of the input array as the words numbered `0, …, 15`, the compiled symbolic block
    function `chachaLets` from the word numbered `16`, and the stores of the sixteen output
    words into the output array at register indices. -/
def chachaBlockBody : Com jasminDialect chachaInCtxt (.stackArr 32 16) :=
  genLoad Var.here 0 fun ρ0 v0 =>
  genLoads (List.range' 1 15) (ρ0 _ .here) 1 (fun _ => v0) fun ρ1 env1 =>
  genLetsR chachaLets.2.rev.reverse 16 env1 fun ρ2 env2 =>
  genStoresIdx chachaLets.1 (ρ2 _ (ρ1 _ (ρ0 _ (.there .here)))) env2

/-! ## 4. Values -/

/-- The state numbered `q.1` in the let-list `q.2` holds the values `v`. -/
def ChaChaInv (ρ : Nat → BitVec 32) (q : (Fin 16 → Nat) × LetSt 32) (v : Fin 16 → BitVec 32) :
    Prop :=
  q.2.Good 16 ∧ (∀ i, q.1 i < q.2.next) ∧ (fun i => q.2.val 16 ρ (q.1 i)) = v

/-- One symbolic quarter-round evaluates to `qrUpd`. -/
theorem chachaQrLets_spec (ρ : Nat → BitVec 32) (st : Fin 16 → Nat) (a b c d : Fin 16)
    (s : LetSt 32) (hs : s.Good 16) (hst : ∀ i, st i < s.next) :
    ChaChaInv ρ (chachaQrLets st a b c d s) (qrUpd (fun i => s.val 16 ρ (st i)) a b c d) := by
  have hval := LetSt.val_extend ρ hs
  have hg := hs
  unfold LetSt.Good at hg
  simp only [ChaChaInv, chachaQrLets, LetSt.push]
  refine ⟨?_, ?_, ?_⟩
  · unfold LetSt.Good
    simp only [List.length_cons, hg]
    omega
  · intro i
    have := hst i
    unfold upd4
    split_ifs <;> omega
  · rw [show ∀ m (e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ : WExp 32),
      (⟨m, e₁ :: e₂ :: e₃ :: e₄ :: e₅ :: e₆ :: e₇ :: e₈ :: s.rev⟩ : LetSt 32) =
        ⟨m, [e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈] ++ s.rev⟩ from fun _ _ _ _ _ _ _ _ _ => rfl, hval,
      upd4_comp]
    have hne : ∀ j, j < s.next → j ≠ s.next ∧ j ≠ s.next + 1 ∧ j ≠ s.next + 1 + 1 ∧
        j ≠ s.next + 1 + 1 + 1 ∧ j ≠ s.next + 1 + 1 + 1 + 1 ∧
        j ≠ s.next + 1 + 1 + 1 + 1 + 1 ∧ j ≠ s.next + 1 + 1 + 1 + 1 + 1 + 1 ∧
        j ≠ s.next + 1 + 1 + 1 + 1 + 1 + 1 + 1 := fun j hj => by omega
    have hst' := fun i => hne (st i) (hst i)
    unfold qrUpd quarterRound
    congr 1
    · funext i
      simp [evalLets, hst']
    all_goals simp (config := {zetaDelta := true}) [evalLets, WExp.eval, JasminBinOp.apply,
      hst', Nat.add_assoc, rotL32_eq_rotateRight]

/-- A symbolic double round evaluates to `doubleRound`. -/
theorem chachaDRLets_spec (ρ : Nat → BitVec 32) (q : (Fin 16 → Nat) × LetSt 32)
    (v : Fin 16 → BitVec 32) (hq : ChaChaInv ρ q v) :
    ChaChaInv ρ (chachaDRLets q) (doubleRound v) := by
  rw [doubleRound_eq_foldl]
  unfold chachaDRLets
  refine List.foldl_rel hq fun k _ q v hq => ?_
  obtain ⟨hg, hlt, hv⟩ := hq
  have hd : (blake2Quad k).1 ≠ (blake2Quad k).2.1 ∧ (blake2Quad k).1 ≠ (blake2Quad k).2.2.1 ∧
      (blake2Quad k).1 ≠ (blake2Quad k).2.2.2 ∧ (blake2Quad k).2.1 ≠ (blake2Quad k).2.2.1 ∧
      (blake2Quad k).2.1 ≠ (blake2Quad k).2.2.2 ∧
      (blake2Quad k).2.2.1 ≠ (blake2Quad k).2.2.2 := by
    revert k; decide
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hd
  have key := chachaQrLets_spec ρ q.1 (blake2Quad k).1 (blake2Quad k).2.1
    (blake2Quad k).2.2.1 (blake2Quad k).2.2.2 q.2 hg hlt
  rw [hv] at key
  rw [quarterRoundAt_eq_qrUpd _ _ _ _ _ h1 h2 h3 h4 h5 h6]
  exact key

/-- The symbolic ten double rounds evaluate to `chachaCore` at input values agreeing with the
    state `S` below the word numbered `16`. -/
theorem chachaCoreLets_spec (S : Fin 16 → BitVec 32) (ρ : Nat → BitVec 32)
    (hρ : ∀ i (h : i < 16), ρ i = S ⟨i, h⟩) :
    ChaChaInv ρ chachaCoreLets (chachaCore S) := by
  have key : ∀ n, ChaChaInv ρ ((List.range n).foldl (fun q _ => chachaDRLets q)
      ((fun i => i.val, ⟨16, []⟩) : (Fin 16 → Nat) × LetSt 32)) (doubleRound^[n] S) := by
    intro n
    induction n with
    | zero =>
        refine ⟨rfl, fun i => i.isLt, ?_⟩
        funext i
        exact hρ i.val i.isLt
    | succ n ih =>
        rw [List.range_succ, List.foldl_append, Function.iterate_succ_apply']
        exact chachaDRLets_spec ρ _ _ ih
  exact key 10

/-- The symbolic block function from input values agreeing with the state `S` below the word
    numbered `16`: the word numbered `chachaCoreLets.2.next + i` is the word `i` of
    `chachaBlock S`. -/
theorem chachaLets_spec (S : Fin 16 → BitVec 32) (ρ : Nat → BitVec 32)
    (hρ : ∀ i (h : i < 16), ρ i = S ⟨i, h⟩) (i : Fin 16) :
    chachaLets.2.val 16 ρ (chachaCoreLets.2.next + i.val) = chachaBlock S i := by
  obtain ⟨hg, hlt, hv⟩ := chachaCoreLets_spec S ρ hρ
  have h16 : 16 ≤ chachaCoreLets.2.next := by unfold LetSt.Good at hg; omega
  obtain ⟨-, -, -, hf⟩ := keccakTPushOfFn_spec (chachaFeedE chachaCoreLets.1) chachaCoreLets.2 hg
    (fun j => ⟨hlt j, by have := j.isLt; simp only [keccakTVarsLt]; omega⟩) ρ
  simp only [chachaLets]
  rw [hf i]
  simp only [chachaFeedE, WExp.eval, JasminBinOp.apply]
  rw [congrFun hv i, LetSt.val, evalLets_of_lt _ _ _ _ i.isLt, hρ i.val i.isLt]
  rfl

/-- **The value of the ChaCha20 template**: at the input array `S` of the sixteen state words
    and any contents `O` of the output array, the program returns the block function
    `ChaCha20Block.chachaBlock S` of RFC 8439 §2.3. -/
theorem chachaBlockBody_value (S O : Fin 16 → BitVec 32) :
    chachaBlockBody.denote (.cons S (.cons O .nil)) = chachaBlock S := by
  have hA : ∀ i (h : i < 16), stackGet S (BitVec.ofNat 64 i).toNat = S ⟨i, h⟩ := fun i h => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact stackGet_id S ⟨i, h⟩
  have hL : ∀ p ∈ chachaLets.1, p.1 < 2 ^ 64 := by
    intro p hp
    simp only [chachaLets, List.mem_map, List.mem_finRange, true_and] at hp
    obtain ⟨j, rfl⟩ := hp
    have := j.isLt
    simp only
    omega
  unfold chachaBlockBody
  refine genLoad_denote _ 0 _ _ S rfl _ fun ρ0 V0 v0 hρ0 hv0 => ?_
  refine genLoads_denote _ _ 1 _ _ V0 S (hρ0 _ _) (fun _ => stackGet S (BitVec.ofNat 64 0).toNat)
    (fun _ => hv0) _ fun ρ1 V1 env1 hρ1 henv1 => ?_
  refine genLetsR_denote _ 16 env1 _ V1 _ henv1 _ fun ρ2 V2 env2 hρ2 henv2 => ?_
  refine (genStoresIdx_denote chachaLets.1 (ρ2 _ (ρ1 _ (ρ0 _ (.there .here)))) env2 V2 O
    ((hρ2 _ _).trans ((hρ1 _ _).trans (hρ0 _ _))) _ henv2 hL).trans ?_
  have hagree : ∀ i (h : i < 16), loadVals S (fun _ => stackGet S (BitVec.ofNat 64 0).toNat) 1
      (List.range' 1 15) i = S ⟨i, h⟩ := by
    intro i hi
    rw [loadVals_apply]
    by_cases h0 : i = 0
    · subst h0
      rw [ite_eq_right (by omega)]
      exact hA 0 (by omega)
    · rw [ite_eq_left (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
        List.getElem_range', show 1 + 1 * (i - 1) = i by omega]
      exact hA i hi
  have hv := chachaLets_spec S _ hagree
  simp only [chachaLets]
  rw [keccakTFoldlStores (List.finRange 16) (fun j => chachaCoreLets.2.next + j.val)]
  funext i
  simp only [List.mem_finRange, ite_true]
  exact hv i

/-! ## 5. Events -/

/-- **The events of the ChaCha20 template are fixed**: at leakage parameters with no
    variable-time operation, the program emits the same events at every two valuations. -/
theorem chachaBlockBody_events (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none) :
    LeakFixed (jLeakModel Pj) chachaBlockBody := by
  unfold chachaBlockBody
  exact genLoad_fixed Pj hV _ _ _ fun _ _ => genLoads_fixed Pj hV _ _ _ _ _ fun _ _ =>
    genLetsR_fixed Pj hV _ _ _ _ fun _ _ => genStoresIdx_fixed Pj hV _ _ _

end CatCrypt.Crypto.SecureCompilation.HashTemplate
