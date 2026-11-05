/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.HashTemplate.StraightLine
public import CatCrypt.Crypto.Primitives.BLAKE2s
public import CatCrypt.Crypto.Primitives.SHA512

/-!
# The BLAKE2 compression function as a `jasminDialect` template

BLAKE2b and BLAKE2s (RFC 7693) share one compression function `F`, parametric in the word
width, the round count, the four rotation amounts of the mixing function `G`, the
initialisation vector and the message permutation `σ`. A record `Blake2Params` collects these
parameters, and `blake2CompressBody P` is the compression function at `P` as a straight-line
program of `jasminDialect`, generated from `P` through the compiler of
`HashTemplate.StraightLine`.

The program reads the eight chaining words, the sixteen message words, and the three words
`t0`, `t1` (the low and high halves of the offset counter) and `f0` (the finalisation flag
word, all ones at the last block) from three stack arrays, and returns the eight new chaining
words in a fresh stack array. Its operations are word addition, `xor`, rotation by an
immediate, constants, and the constant-index loads and stores; it has no data-dependent
control flow.

The reference `Blake2Params.blake2CompressRef` is the function `F` of RFC 7693 §3.2 on `BitVec`
words, with `G` of §3.1. At `blake2sP` it agrees with `Primitives.BLAKE2s.blake2sCompress`;
there is no BLAKE2b compression elsewhere in the workspace, and `blake2CompressRef` is the
specification at `blake2bP`.

## Main definitions

* `Blake2Params`: the parameters of the BLAKE2 compression function.
* `Blake2Params.blake2CompressRef`: the compression function `F` of RFC 7693 §3.2.
* `blake2Lets`: the symbolic compression, a list of let-bound word expressions.
* `blake2Tail`: the compiled symbolic compression and the stores.
* `blake2CompressBody`: the compression function as a `jasminDialect` program.
* `blake2bP`, `blake2sP`: BLAKE2b and BLAKE2s.
* `blake2InCtxtP`, `blake2InWords`, `blake2CompressBodyP`: the compression function with the
  chaining and message words in one input array, the counter and flag words in registers,
  and the new chaining words stored by register index into a separate output array, the form
  `compileRegion` accepts.

## Main results

* `blake2CompressBody_value`: the program denotes `blake2CompressRef`.
* `blake2CompressBody_events`: the program emits the same events at every two valuations.
* `blake2CompressBody_blake2s`: agreement with `Primitives.BLAKE2s.blake2sCompress`.
* `blake2CompressBodyP_value`, `blake2CompressBodyP_events`: the same two statements for
  `blake2CompressBodyP`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplate (LeakFixed)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open Ctxt (Var Valuation)

/-! ## 1. Parameters -/

/-- **The parameters of the BLAKE2 compression function** (RFC 7693 §2.1, §2.6, §2.7): the
    word width, the round count, the rotation amounts `R1`, …, `R4` of `G`, the
    initialisation vector and the message permutation `σ` of each round modulo `10`. -/
structure Blake2Params where
  /-- The word width. -/
  w : Nat
  /-- The word width is `32` or `64`. -/
  hw : w = 32 ∨ w = 64
  /-- The round count. -/
  rounds : Nat
  /-- The first rotation amount of `G`. -/
  R1 : Nat
  /-- The second rotation amount of `G`. -/
  R2 : Nat
  /-- The third rotation amount of `G`. -/
  R3 : Nat
  /-- The fourth rotation amount of `G`. -/
  R4 : Nat
  /-- The initialisation vector. -/
  IV : Fin 8 → BitVec w
  /-- The message permutation of the round `r` is `sigma (r mod 10)`. -/
  sigma : Fin 10 → Fin 16 → Fin 16

/-- The update of the positions `a`, `b`, `c`, `d` of a state of sixteen entries. -/
def upd4 {α : Type} (v : Fin 16 → α) (a b c d : Fin 16) (xa xb xc xd : α) : Fin 16 → α :=
  fun i => if i = a then xa else if i = b then xb else if i = c then xc
    else if i = d then xd else v i

theorem upd4_comp {α β : Type} (f : α → β) (v : Fin 16 → α) (a b c d : Fin 16)
    (xa xb xc xd : α) :
    (fun i => f (upd4 v a b c d xa xb xc xd i)) =
      upd4 (fun i => f (v i)) a b c d (f xa) (f xb) (f xc) (f xd) := by
  funext i; unfold upd4; split_ifs <;> rfl

/-- The positions `(a, b, c, d)` of the `k`-th application of `G` in a round: the four
    columns, then the four diagonals of the `4 × 4` state (RFC 7693 §3.2). -/
def blake2Quad : Fin 8 → Fin 16 × Fin 16 × Fin 16 × Fin 16 :=
  ![(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15),
    (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13), (3, 4, 9, 14)]

/-! ## 2. The reference compression function -/

namespace Blake2Params

/-- The mixing function `G` of RFC 7693 §3.1 on the positions `a`, `b`, `c`, `d` of the state
    `v`, with the message words `x` and `y`. -/
def mixRef (P : Blake2Params) (v : Fin 16 → BitVec P.w) (a b c d : Fin 16)
    (x y : BitVec P.w) : Fin 16 → BitVec P.w :=
  let a1 := v a + v b + x
  let d1 := (v d ^^^ a1).rotateRight P.R1
  let c1 := v c + d1
  let b1 := (v b ^^^ c1).rotateRight P.R2
  let a2 := a1 + b1 + y
  let d2 := (d1 ^^^ a2).rotateRight P.R3
  let c2 := c1 + d2
  let b2 := (b1 ^^^ c2).rotateRight P.R4
  upd4 v a b c d a2 b2 c2 d2

/-- The indices of the two message words of the `k`-th application of `G` in the round `r`:
    `σ[r mod 10][2k]` and `σ[r mod 10][2k + 1]`. -/
def msgIdx (P : Blake2Params) (r : Nat) (k : Fin 8) : Fin 16 × Fin 16 :=
  (P.sigma ⟨r % 10, Nat.mod_lt _ (by decide)⟩ ⟨2 * k.val, by omega⟩,
    P.sigma ⟨r % 10, Nat.mod_lt _ (by decide)⟩ ⟨2 * k.val + 1, by omega⟩)

/-- The round `r` on the state `v` with the message words `M`: the eight applications of `G`. -/
def blake2RoundRef (P : Blake2Params) (M : Fin 16 → BitVec P.w) (v : Fin 16 → BitVec P.w)
    (r : Nat) : Fin 16 → BitVec P.w :=
  (List.finRange 8).foldl (fun v k => P.mixRef v (blake2Quad k).1 (blake2Quad k).2.1
    (blake2Quad k).2.2.1 (blake2Quad k).2.2.2 (M (P.msgIdx r k).1) (M (P.msgIdx r k).2)) v

/-- The initial state of the compression: the chaining words, then the initialisation vector
    with the counter words `t0`, `t1` and the flag word `f0` added by `xor` at the positions
    `12`, `13`, `14`. -/
def initRef (P : Blake2Params) (H : Fin 8 → BitVec P.w) (t0 t1 f0 : BitVec P.w) :
    Fin 16 → BitVec P.w :=
  ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, P.IV 0, P.IV 1, P.IV 2, P.IV 3,
    P.IV 4 ^^^ t0, P.IV 5 ^^^ t1, P.IV 6 ^^^ f0, P.IV 7]

/-- **The BLAKE2 compression function** `F` at `P` (RFC 7693 §3.2): the rounds over the
    initial state, then `H i ⊕ v i ⊕ v (i + 8)`. -/
def blake2CompressRef (P : Blake2Params) (H : Fin 8 → BitVec P.w) (M : Fin 16 → BitVec P.w)
    (t0 t1 f0 : BitVec P.w) : Fin 8 → BitVec P.w :=
  let v := (List.range P.rounds).foldl (P.blake2RoundRef M) (P.initRef H t0 t1 f0)
  fun i => H i ^^^ v ⟨i.val, by omega⟩ ^^^ v ⟨i.val + 8, by omega⟩

end Blake2Params

/-! ## 3. The symbolic BLAKE2 compression -/

/-- `G` on the words numbered `st a`, `st b`, `st c`, `st d`, with the message words numbered
    `x` and `y`: binds the eight intermediate words and returns the numbers of the new state. -/
def blake2MixLets (P : Blake2Params) (st : Fin 16 → Nat) (a b c d : Fin 16) (x y : Nat)
    (s : LetSt P.w) : (Fin 16 → Nat) × LetSt P.w :=
  let (a1, s) := s.push (.bin .add (.bin .add (.var (st a)) (.var (st b))) (.var x))
  let (d1, s) := s.push (.rotr P.R1 (.bin .xor (.var (st d)) (.var a1)))
  let (c1, s) := s.push (.bin .add (.var (st c)) (.var d1))
  let (b1, s) := s.push (.rotr P.R2 (.bin .xor (.var (st b)) (.var c1)))
  let (a2, s) := s.push (.bin .add (.bin .add (.var a1) (.var b1)) (.var y))
  let (d2, s) := s.push (.rotr P.R3 (.bin .xor (.var d1) (.var a2)))
  let (c2, s) := s.push (.bin .add (.var c1) (.var d2))
  let (b2, s) := s.push (.rotr P.R4 (.bin .xor (.var b1) (.var c2)))
  (upd4 st a b c d a2 b2 c2 d2, s)

/-- The round `r` on the state numbered `q.1`; the message word `M j` is numbered `8 + j`. -/
def blake2RoundLets (P : Blake2Params) (q : (Fin 16 → Nat) × LetSt P.w) (r : Nat) :
    (Fin 16 → Nat) × LetSt P.w :=
  (List.finRange 8).foldl (fun q k => blake2MixLets P q.1 (blake2Quad k).1 (blake2Quad k).2.1
    (blake2Quad k).2.2.1 (blake2Quad k).2.2.2 (8 + (P.msgIdx r k).1.val)
    (8 + (P.msgIdx r k).2.val) q.2) q

/-- The initial state: the chaining words numbered `0, …, 7`, and the eight words of the
    initialisation vector bound as the words numbered `27, …, 34`, the counter and flag words
    numbered `24`, `25`, `26`. -/
def blake2InitLets (P : Blake2Params) : (Fin 16 → Nat) × LetSt P.w :=
  (![0, 1, 2, 3, 4, 5, 6, 7, 27, 28, 29, 30, 31, 32, 33, 34],
    ⟨35, [.const (P.IV 7), .bin .xor (.const (P.IV 6)) (.var 26),
      .bin .xor (.const (P.IV 5)) (.var 25), .bin .xor (.const (P.IV 4)) (.var 24),
      .const (P.IV 3), .const (P.IV 2), .const (P.IV 1), .const (P.IV 0)]⟩)

/-- The finalisation: binds `H i ⊕ v i ⊕ v (i + 8)` for each listed `i`, the chaining word
    `H i` numbered `i`, and returns the pairs of `i` and the number of its word. -/
def blake2FeedLets (P : Blake2Params) (st : Fin 16 → Nat) :
    List (Fin 8) → LetSt P.w → List (Nat × Nat) × LetSt P.w
  | [], s => ([], s)
  | i :: is, s =>
      let (o, s) := s.push (.bin .xor (.bin .xor (.var i.val) (.var (st ⟨i.val, by omega⟩)))
        (.var (st ⟨i.val + 8, by omega⟩)))
      let (outs, s) := blake2FeedLets P st is s
      ((i.val, o) :: outs, s)

/-- **The symbolic BLAKE2 compression** at `P`: the chaining words `H 0, …, H 7` are the
    words numbered `0, …, 7`, the message words `M 0, …, M 15` the words numbered `8, …, 23`,
    and `t0`, `t1`, `f0` the words numbered `24`, `25`, `26`; the result is the store list of
    the new chaining words and the let-bound expressions, from the word numbered `27`. -/
def blake2Lets (P : Blake2Params) : List (Nat × Nat) × LetSt P.w :=
  let q := (List.range P.rounds).foldl (blake2RoundLets P) (blake2InitLets P)
  blake2FeedLets P q.1 (List.finRange 8) q.2

/-- The values of the input words: `H i` numbered `i`, `M j` numbered `8 + j` and `T k`
    numbered `24 + k`. -/
def blake2Inputs {w : Nat} (H : Fin 8 → BitVec w) (M : Fin 16 → BitVec w)
    (T : Fin 3 → BitVec w) (i : Nat) : BitVec w :=
  if h : i < 8 then H ⟨i, h⟩ else if h' : i - 8 < 16 then M ⟨i - 8, h'⟩
  else if h'' : i - 24 < 3 then T ⟨i - 24, h''⟩ else 0

/-! ## 4. The program -/

/-- The input context of the compression: the chaining words, the message words, and the
    counter and flag words `t0`, `t1`, `f0`, as stack arrays. -/
abbrev blake2InCtxt (w : Nat) : Ctxt jasminDialect :=
  [.stackArr w 8, .stackArr w 16, .stackArr w 3]

/-- The last stage of the compression at the variables `env` of the numbered input words: the
    compiled symbolic compression `blake2Lets P` from the word numbered `27`, and the stores of
    the eight new chaining words into a fresh array. -/
def blake2Tail (P : Blake2Params) {Γ : Ctxt jasminDialect} (env : Nat → Var Γ (.reg P.w)) :
    Com jasminDialect Γ (.stackArr P.w 8) :=
  genLets (blake2Lets P).2.rev.reverse 27 env fun env4 =>
  .var ⟨.stackZero P.w 8, rfl, .nil⟩ (genStores (blake2Lets P).1 .here (fun i => (env4 i).there))

/-- **The BLAKE2 compression function at `P` as a `jasminDialect` program**: the loads of the
    eight chaining words, the sixteen message words and the three counter and flag words, and
    the stage `blake2Tail`. -/
def blake2CompressBody (P : Blake2Params) :
    Com jasminDialect (blake2InCtxt P.w) (.stackArr P.w 8) :=
  genLoad (Var.here) 0 fun ρ0 v0 =>
  genLoads (List.range' 1 7) (ρ0 _ .here) 1 (fun _ => v0) fun ρ1 env1 =>
  genLoads (List.range 16) (ρ1 _ (ρ0 _ (.there .here))) 8 env1 fun ρ2 env2 =>
  genLoads (List.range 3) (ρ2 _ (ρ1 _ (ρ0 _ (.there (.there .here))))) 24 env2 fun _ env3 =>
  blake2Tail P env3

/-! ## 5. BLAKE2b and BLAKE2s (RFC 7693) -/

/-- BLAKE2b: 64-bit words, 12 rounds, rotations `32, 24, 16, 63` (RFC 7693 §2.1). The
    initialisation vector is the initial hash value of SHA-512 (§2.6), that of
    `Primitives.SHA512`; the message permutation is the table of §2.7, that of
    `Primitives.BLAKE2s`. -/
def blake2bP : Blake2Params where
  w := 64
  hw := Or.inr rfl
  rounds := 12
  R1 := 32
  R2 := 24
  R3 := 16
  R4 := 63
  IV := fun i => (Primitives.SHA512.h0Vec[i]).toBitVec
  sigma := Primitives.BLAKE2s.sigma

/-- BLAKE2s: 32-bit words, 10 rounds, rotations `16, 12, 8, 7` (RFC 7693 §2.1). The
    initialisation vector and the message permutation are those of `Primitives.BLAKE2s`. -/
def blake2sP : Blake2Params where
  w := 32
  hw := Or.inl rfl
  rounds := 10
  R1 := 16
  R2 := 12
  R3 := 8
  R4 := 7
  IV := fun i => (Primitives.BLAKE2s.iv i).toBitVec
  sigma := Primitives.BLAKE2s.sigma

/-! ## 6. The values of the symbolic compression -/

/-- The state numbered `q.1` in the let-list `q.2` holds the values `v`. -/
def Blake2Inv (P : Blake2Params) (ρ : Nat → BitVec P.w) (q : (Fin 16 → Nat) × LetSt P.w)
    (v : Fin 16 → BitVec P.w) : Prop :=
  q.2.Good 27 ∧ (∀ i, q.1 i < q.2.next) ∧ (fun i => q.2.val 27 ρ (q.1 i)) = v

/-- One symbolic application of `G` evaluates to `mixRef`. -/
theorem blake2MixLets_spec (P : Blake2Params) (ρ : Nat → BitVec P.w) (st : Fin 16 → Nat)
    (a b c d : Fin 16) (x y : Nat) (s : LetSt P.w) (hs : s.Good 27)
    (hst : ∀ i, st i < s.next) (hy : y < s.next) :
    Blake2Inv P ρ (blake2MixLets P st a b c d x y s)
      (P.mixRef (fun i => s.val 27 ρ (st i)) a b c d (s.val 27 ρ x) (s.val 27 ρ y)) := by
  have hval := LetSt.val_extend ρ hs
  have hg := hs
  unfold LetSt.Good at hg
  simp only [Blake2Inv, blake2MixLets, LetSt.push]
  refine ⟨?_, ?_, ?_⟩
  · unfold LetSt.Good
    simp only [List.length_cons, hg]
    omega
  · intro i
    have := hst i
    unfold upd4
    split_ifs <;> omega
  · rw [show ∀ m (e₁ e₂ e₃ e₄ e₅ e₆ e₇ e₈ : WExp P.w),
      (⟨m, e₁ :: e₂ :: e₃ :: e₄ :: e₅ :: e₆ :: e₇ :: e₈ :: s.rev⟩ : LetSt P.w) =
        ⟨m, [e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈] ++ s.rev⟩ from fun _ _ _ _ _ _ _ _ _ => rfl, hval,
      upd4_comp]
    have hne : ∀ j, j < s.next → j ≠ s.next ∧ j ≠ s.next + 1 ∧ j ≠ s.next + 1 + 1 ∧
        j ≠ s.next + 1 + 1 + 1 ∧ j ≠ s.next + 1 + 1 + 1 + 1 ∧
        j ≠ s.next + 1 + 1 + 1 + 1 + 1 ∧ j ≠ s.next + 1 + 1 + 1 + 1 + 1 + 1 ∧
        j ≠ s.next + 1 + 1 + 1 + 1 + 1 + 1 + 1 := fun j hj => by omega
    have hy' := hne y hy
    have hst' := fun i => hne (st i) (hst i)
    unfold Blake2Params.mixRef
    congr 1
    · funext i
      simp [evalLets, hst']
    all_goals simp (config := {zetaDelta := true}) [evalLets, WExp.eval, JasminBinOp.apply,
      hst', hy', Nat.add_assoc]

/-- A symbolic round evaluates to `blake2RoundRef`. -/
theorem blake2RoundLets_spec (P : Blake2Params) (ρ : Nat → BitVec P.w)
    (M : Fin 16 → BitVec P.w) (hM : ∀ j : Fin 16, ρ (8 + j.val) = M j) (r : Nat)
    (q : (Fin 16 → Nat) × LetSt P.w) (v : Fin 16 → BitVec P.w) (hq : Blake2Inv P ρ q v) :
    Blake2Inv P ρ (blake2RoundLets P q r) (P.blake2RoundRef M v r) := by
  unfold blake2RoundLets Blake2Params.blake2RoundRef
  refine List.foldl_rel hq fun k _ q v hq => ?_
  obtain ⟨hg, hlt, hv⟩ := hq
  have h27 : 27 ≤ q.2.next := by unfold LetSt.Good at hg; omega
  have hin : ∀ j : Fin 16, q.2.val 27 ρ (8 + j.val) = M j := fun j =>
    (evalLets_of_lt _ _ _ _ (by omega)).trans (hM j)
  have key := blake2MixLets_spec P ρ q.1 (blake2Quad k).1 (blake2Quad k).2.1
    (blake2Quad k).2.2.1 (blake2Quad k).2.2.2 (8 + (P.msgIdx r k).1.val)
    (8 + (P.msgIdx r k).2.val) q.2 hg hlt (by omega)
  rw [hv, hin, hin] at key
  exact key

/-- The symbolic initial state evaluates to `initRef`. -/
theorem blake2InitLets_spec (P : Blake2Params) (H : Fin 8 → BitVec P.w)
    (M : Fin 16 → BitVec P.w) (T : Fin 3 → BitVec P.w) (ρ : Nat → BitVec P.w)
    (hρ : ∀ i < 27, ρ i = blake2Inputs H M T i) :
    Blake2Inv P ρ (blake2InitLets P) (P.initRef H (T 0) (T 1) (T 2)) := by
  refine ⟨rfl, fun i => by fin_cases i <;> simp [blake2InitLets], ?_⟩
  funext i
  fin_cases i <;>
    simp [blake2InitLets, LetSt.val, evalLets, WExp.eval, JasminBinOp.apply,
      Blake2Params.initRef, hρ, blake2Inputs]

/-- The finalisation binds, at position `k`, the `xor` of the chaining word numbered `is[k]`
    and the state words `st is[k]` and `st (is[k] + 8)`. -/
theorem blake2FeedLets_spec (P : Blake2Params) (ρ : Nat → BitVec P.w) (st : Fin 16 → Nat) :
    ∀ (is : List (Fin 8)) (s : LetSt P.w), s.Good 27 → (∀ i, st i < s.next) →
      s.Ext (blake2FeedLets P st is s).2 ∧ (blake2FeedLets P st is s).1.length = is.length ∧
      ∀ k (hk : k < is.length),
        (blake2FeedLets P st is s).1.getD k (0, 0) = (is[k].val, s.next + k) ∧
        (blake2FeedLets P st is s).2.val 27 ρ (s.next + k) =
          s.val 27 ρ is[k].val ^^^ s.val 27 ρ (st ⟨is[k].val, by omega⟩) ^^^
            s.val 27 ρ (st ⟨is[k].val + 8, by omega⟩) := by
  intro is
  induction is with
  | nil => intro s _ _; exact ⟨LetSt.Ext.refl s, rfl, fun k hk => absurd hk (by simp)⟩
  | cons i is ih =>
      intro s hs hst
      have h27 : 27 ≤ s.next := by unfold LetSt.Good at hs; omega
      let e : WExp P.w := .bin .xor (.bin .xor (.var i.val) (.var (st ⟨i.val, by omega⟩)))
        (.var (st ⟨i.val + 8, by omega⟩))
      have hg := LetSt.push_good e hs
      have hv := LetSt.push_val e hs ρ
      have he := LetSt.Ext.push e s
      have hnext : (s.push e).2.next = s.next + 1 := rfl
      obtain ⟨e1, l1, f1⟩ := ih _ hg (fun j => by have := hst j; omega)
      simp only [blake2FeedLets]
      refine ⟨he.trans e1, by simp only [List.length_cons]; exact congrArg (· + 1) l1,
        fun k hk => ?_⟩
      cases k with
      | zero =>
          refine ⟨rfl, ?_⟩
          rw [e1.val_eq hg ρ _ (by omega), hv]
          simp [e, WExp.eval, JasminBinOp.apply]
      | succ k =>
          have hk' : k < is.length := by simp at hk; omega
          obtain ⟨f1a, f1b⟩ := f1 k hk'
          refine ⟨by simpa [hnext, Nat.add_assoc, Nat.add_comm 1 k] using f1a, ?_⟩
          rw [show s.next + (k + 1) = (s.push e).2.next + k by omega, f1b, hv]
          have h1 : (is[k].val : Nat) ≠ s.next := by have := is[k].isLt; omega
          have h2 : st ⟨is[k].val, by omega⟩ ≠ s.next := Nat.ne_of_lt (hst _)
          have h3 : st ⟨is[k].val + 8, by omega⟩ ≠ s.next := Nat.ne_of_lt (hst _)
          simp [h1, h2, h3]

/-- The symbolic compression from input values agreeing with the chaining, message, counter
    and flag words below the word numbered `27`: the stores write the indices `0, …, 7`, and
    the word stored at the index `i` is `blake2CompressRef P H M (T 0) (T 1) (T 2) i`. -/
theorem blake2Lets_spec (P : Blake2Params) (H : Fin 8 → BitVec P.w)
    (M : Fin 16 → BitVec P.w) (T : Fin 3 → BitVec P.w) (ρ : Nat → BitVec P.w)
    (hρ : ∀ i < 27, ρ i = blake2Inputs H M T i) :
    (blake2Lets P).1.length = 8 ∧ (∀ k < 8, ((blake2Lets P).1.getD k (0, 0)).1 = k) ∧
      (fun i : Fin 8 => evalLets ρ 27 (blake2Lets P).2.rev.reverse
        ((blake2Lets P).1.getD i.val (0, 0)).2) = P.blake2CompressRef H M (T 0) (T 1) (T 2) := by
  have hM : ∀ j : Fin 16, ρ (8 + j.val) = M j := fun j => by
    rw [hρ _ (by omega)]
    simp [blake2Inputs]
  obtain ⟨g, b, v⟩ := List.foldl_rel (l := List.range P.rounds) (r := Blake2Inv P ρ)
    (blake2InitLets_spec P H M T ρ hρ)
    fun r _ q v hq => blake2RoundLets_spec P ρ M hM r q v hq
  obtain ⟨_, l', f'⟩ := blake2FeedLets_spec P ρ _ (List.finRange 8) _ g b
  simp only [blake2Lets]
  refine ⟨by simpa using l', fun k hk => ?_, ?_⟩
  · rw [(f' k (by simpa using hk)).1]
    simp
  · funext i
    obtain ⟨f1, f2⟩ := f' i.val (by simp)
    rw [f1]
    show LetSt.val 27 ρ _ _ = _
    rw [f2, LetSt.val, evalLets_of_lt _ _ _ _ (by simp; omega), hρ _ (by simp; omega)]
    simp only [Blake2Params.blake2CompressRef, ← v]
    simp [blake2Inputs, LetSt.val]

/-! ## 7. Statements -/

/-- The stage `blake2Tail` at variables holding values that agree with the chaining, message,
    counter and flag words below the word numbered `27` returns the reference compression. -/
theorem blake2Tail_value (P : Blake2Params) (H : Fin 8 → BitVec P.w)
    (M : Fin 16 → BitVec P.w) (T : Fin 3 → BitVec P.w) {Γ : Ctxt jasminDialect}
    (env : Nat → Var Γ (.reg P.w)) (V : Valuation Γ) (ρv : Nat → BitVec P.w)
    (henv : ∀ i, (env i).lookup V = ρv i) (hρ : ∀ i < 27, ρv i = blake2Inputs H M T i) :
    (blake2Tail P env).denote V = P.blake2CompressRef H M (T 0) (T 1) (T 2) := by
  unfold blake2Tail
  refine genLets_denote _ 27 env _ V ρv henv _ fun V4 env4 henv4 => ?_
  refine (genStores_denote (blake2Lets P).1 .here (fun i => (env4 i).there)
    (Ctxt.Valuation.extend V4 (JasminTy.default (.stackArr P.w 8))) _ rfl _
    (fun i => henv4 i)).trans ?_
  obtain ⟨hl, hk, hv⟩ := blake2Lets_spec P H M T _ hρ
  rw [foldl_stores8 _ hl hk]
  exact hv

/-- The stage `blake2Tail` has fixed events at leakage parameters with no variable-time
    operation. -/
theorem blake2Tail_fixed (P : Blake2Params) (Pj : JLeakParams)
    (hV : ∀ op, Pj.opVT op = none) {Γ : Ctxt jasminDialect} (env : Nat → Var Γ (.reg P.w)) :
    LeakFixed (jLeakModel Pj) (blake2Tail P env) := by
  unfold blake2Tail
  exact genLets_fixed Pj hV _ _ _ _ fun _ =>
    leakFixed_var_quiet Pj _ _ (by simp [Dialects.JasminComLLeak.jKind, hV])
      (genStores_fixed Pj hV _ _ _)

/-- The words numbered below `24` after the loads of the chaining and message words: the
    chaining word `H i` numbered `i` and the message word `M j` numbered `8 + j`. -/
theorem blake2LoadVals_lt24 (P : Blake2Params) (H : Fin 8 → BitVec P.w)
    (M : Fin 16 → BitVec P.w) (T : Fin 3 → BitVec P.w) (i : Nat) (hi : i < 24) :
    loadVals M (loadVals H (fun _ => stackGet H (BitVec.ofNat 64 0).toNat) 1
      (List.range' 1 7)) 8 (List.range 16) i = blake2Inputs H M T i := by
  have hget : ∀ {m : Nat} (A : Fin m → BitVec P.w) i (h : i < m) (_ : m ≤ 16),
      stackGet A (BitVec.ofNat 64 i).toNat = A ⟨i, h⟩ := fun A i h _ => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact stackGet_id A ⟨i, h⟩
  rw [loadVals_apply, loadVals_apply]
  by_cases h8 : i < 8
  · rw [ite_eq_right (by omega)]
    simp only [blake2Inputs, h8, dite_eq_left]
    by_cases h0 : i = 0
    · subst h0
      rw [ite_eq_right (by omega)]
      exact hget H 0 (by omega) (by omega)
    · rw [ite_eq_left (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
        List.getElem_range', show 1 + 1 * (i - 1) = i by omega]
      exact hget H i h8 (by omega)
  · rw [ite_eq_left (by simp; omega)]
    simp only [blake2Inputs, h8, dite_eq_right, not_false_eq_true, show i - 8 < 16 by omega,
      dite_eq_left]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_range]
    exact hget M _ _ le_rfl

/-- **The value of the BLAKE2 template**: at the chaining words `H`, the message words `M` and
    the counter and flag words `T = (t0, t1, f0)`, the program returns the reference
    compression `blake2CompressRef P H M t0 t1 f0`. -/
theorem blake2CompressBody_value (P : Blake2Params) (H : Fin 8 → BitVec P.w)
    (M : Fin 16 → BitVec P.w) (T : Fin 3 → BitVec P.w) :
    (blake2CompressBody P).denote (.cons H (.cons M (.cons T .nil))) =
      P.blake2CompressRef H M (T 0) (T 1) (T 2) := by
  unfold blake2CompressBody
  refine genLoad_denote _ 0 _ _ H rfl _ fun ρ0 V0 v0 hρ0 hv0 => ?_
  refine genLoads_denote _ _ 1 _ _ V0 H (hρ0 _ _) (fun _ => stackGet H (BitVec.ofNat 64 0).toNat)
    (fun _ => hv0) _ fun ρ1 V1 env1 hρ1 henv1 => ?_
  refine genLoads_denote _ _ 8 env1 _ V1 M ((hρ1 _ _).trans (hρ0 _ _)) _ henv1 _
    fun ρ2 V2 env2 hρ2 henv2 => ?_
  refine genLoads_denote _ _ 24 env2 _ V2 T (((hρ2 _ _).trans (hρ1 _ _)).trans (hρ0 _ _)) _
    henv2 _ fun _ V3 env3 _ henv3 => ?_
  refine blake2Tail_value P H M T env3 V3 _ henv3 fun i hi => ?_
  rw [loadVals_apply]
  by_cases h24 : i < 24
  · rw [ite_eq_right (by omega)]
    exact blake2LoadVals_lt24 P H M T i h24
  · rw [ite_eq_left (by simp; omega)]
    simp only [blake2Inputs, show ¬ i < 8 by omega, dite_eq_right, not_false_eq_true,
      show ¬ i - 8 < 16 by omega, show i - 24 < 3 by omega, dite_eq_left]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_range, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    exact stackGet_id T ⟨i - 24, by omega⟩

/-- **The events of the BLAKE2 template are fixed**: at leakage parameters with no
    variable-time operation, the program emits the same events at every two valuations. -/
theorem blake2CompressBody_events (P : Blake2Params) (Pj : JLeakParams)
    (hV : ∀ op, Pj.opVT op = none) : LeakFixed (jLeakModel Pj) (blake2CompressBody P) := by
  unfold blake2CompressBody
  exact genLoad_fixed Pj hV _ _ _ fun _ _ => genLoads_fixed Pj hV _ _ _ _ _ fun _ _ =>
    genLoads_fixed Pj hV _ _ _ _ _ fun _ _ => genLoads_fixed Pj hV _ _ _ _ _ fun _ _ =>
      blake2Tail_fixed P Pj hV _

/-! ### BLAKE2s -/

theorem blake2s_rotr16 (x : UInt32) :
    (Primitives.BLAKE2s.rotr x 16).toBitVec = x.toBitVec.rotateRight 16 := by
  simp [Primitives.BLAKE2s.rotr, BitVec.rotateRight_def]

theorem blake2s_rotr12 (x : UInt32) :
    (Primitives.BLAKE2s.rotr x 12).toBitVec = x.toBitVec.rotateRight 12 := by
  simp [Primitives.BLAKE2s.rotr, BitVec.rotateRight_def]

theorem blake2s_rotr8 (x : UInt32) :
    (Primitives.BLAKE2s.rotr x 8).toBitVec = x.toBitVec.rotateRight 8 := by
  simp [Primitives.BLAKE2s.rotr, BitVec.rotateRight_def]

theorem blake2s_rotr7 (x : UInt32) :
    (Primitives.BLAKE2s.rotr x 7).toBitVec = x.toBitVec.rotateRight 7 := by
  simp [Primitives.BLAKE2s.rotr, BitVec.rotateRight_def]

/-- The mixing function `mixG` of `Primitives.BLAKE2s` at four distinct positions is `mixRef`
    at `blake2sP` on the words. -/
theorem blake2s_mixG (v : Vector UInt32 16) (a b c d : Fin 16) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (x y : UInt32) :
    (fun i : Fin 16 => (Primitives.BLAKE2s.mixG v a b c d x y)[i].toBitVec) =
      blake2sP.mixRef (fun i => v[i].toBitVec) a b c d x.toBitVec y.toBitVec := by
  funext i
  have hab' : a.val ≠ b.val := Fin.val_ne_of_ne hab
  have hac' : a.val ≠ c.val := Fin.val_ne_of_ne hac
  have had' : a.val ≠ d.val := Fin.val_ne_of_ne had
  have hbc' : b.val ≠ c.val := Fin.val_ne_of_ne hbc
  have hbd' : b.val ≠ d.val := Fin.val_ne_of_ne hbd
  have hcd' : c.val ≠ d.val := Fin.val_ne_of_ne hcd
  simp only [Primitives.BLAKE2s.mixG, Fin.getElem_fin, Vector.getElem_set_self,
    Vector.getElem_set_ne _ _ hab',
    Vector.getElem_set_ne _ _ hac', Vector.getElem_set_ne _ _ had',
    Vector.getElem_set_ne _ _ hbc', Vector.getElem_set_ne _ _ hbd',
    Vector.getElem_set_ne _ _ hcd', Vector.getElem_set_ne _ _ hab'.symm,
    Vector.getElem_set_ne _ _ hac'.symm, Vector.getElem_set_ne _ _ had'.symm,
    Vector.getElem_set_ne _ _ hbc'.symm, Vector.getElem_set_ne _ _ hbd'.symm,
    Vector.getElem_set_ne _ _ hcd'.symm]
  simp only [Blake2Params.mixRef, upd4, Vector.getElem_set, Fin.val_inj]
  split_ifs <;> subst_vars <;>
    simp_all only [ne_eq, not_true_eq_false, UInt32.toBitVec_add, UInt32.toBitVec_xor,
      blake2s_rotr16, blake2s_rotr12, blake2s_rotr8, blake2s_rotr7] <;> rfl

/-- A round of `Primitives.BLAKE2s` is `blake2RoundRef` at `blake2sP` on the words. -/
theorem blake2s_round (v : Vector UInt32 16) (m : Fin 16 → UInt32) (r : Fin 10) :
    (fun i : Fin 16 => (Primitives.BLAKE2s.blake2sRound v m r)[i].toBitVec) =
      blake2sP.blake2RoundRef (fun j => (m j).toBitVec) (fun i => v[i].toBitVec) r.val := by
  unfold Primitives.BLAKE2s.blake2sRound
  simp (disch := decide) only [blake2s_mixG]
  have hr : (⟨r.val % 10, Nat.mod_lt _ (by decide)⟩ : Fin 10) = r :=
    Fin.ext (Nat.mod_eq_of_lt r.isLt)
  simp only [Blake2Params.blake2RoundRef, Blake2Params.msgIdx, hr]
  rfl

/-- The initial state of `Primitives.BLAKE2s.blake2sCompress` is `initRef` at `blake2sP` with
    the counter halves and the flag word. -/
theorem blake2s_init (h : Fin 8 → UInt32) (t : UInt64) (f : Bool) :
    (fun i : Fin 16 =>
      (let v0 : Vector UInt32 16 := Vector.ofFn fun (i : Fin 16) =>
          if h8 : i.val < 8 then h ⟨i.val, h8⟩ else Primitives.BLAKE2s.iv ⟨i.val - 8, by omega⟩
        let v0 := v0.set 12 (v0[12] ^^^ t.toUInt32)
        let v0 := v0.set 13 (v0[13] ^^^ (t >>> (32 : UInt64)).toUInt32)
        let v0 := if f then v0.set 14 (v0[14] ^^^ 0xFFFFFFFF) else v0
        v0)[i].toBitVec) =
      blake2sP.initRef (fun i => (h i).toBitVec) t.toUInt32.toBitVec
        (t >>> (32 : UInt64)).toUInt32.toBitVec (if f then 0xFFFFFFFF#32 else 0#32) := by
  funext i
  cases f <;> fin_cases i <;>
    simp [Blake2Params.initRef, blake2sP, Primitives.BLAKE2s.iv] <;>
    first | rfl | (symm; exact BitVec.xor_zero)

/-- **The template at BLAKE2s is the in-tree BLAKE2s compression**
    `Primitives.BLAKE2s.blake2sCompress` on the words of the state and of the block, with the
    low and high halves of the counter `t` and the flag word of `f`. -/
theorem blake2CompressBody_blake2s (h : Fin 8 → UInt32) (m : Fin 16 → UInt32) (t : UInt64)
    (f : Bool) :
    (blake2CompressBody blake2sP).denote
        (.cons (fun i => (h i).toBitVec) (.cons (fun j => (m j).toBitVec)
          (.cons ![t.toUInt32.toBitVec, (t >>> (32 : UInt64)).toUInt32.toBitVec,
            if f then 0xFFFFFFFF#32 else 0#32] .nil))) =
      fun i => (Primitives.BLAKE2s.blake2sCompress h m t f i).toBitVec := by
  refine (blake2CompressBody_value blake2sP _ _ _).trans ?_
  have key := fin_foldl_inv (fun k (v : Vector UInt32 16) => (fun i : Fin 16 => v[i].toBitVec) =
      (List.range k).foldl (blake2sP.blake2RoundRef (fun j => (m j).toBitVec))
        (blake2sP.initRef (fun i => (h i).toBitVec) t.toUInt32.toBitVec
          (t >>> (32 : UInt64)).toUInt32.toBitVec (if f then 0xFFFFFFFF#32 else 0#32)))
    (fun v r => Primitives.BLAKE2s.blake2sRound v m r) _ (blake2s_init h t f) ?_
  · funext i
    unfold Primitives.BLAKE2s.blake2sCompress
    refine Eq.trans ?_ (UInt32.toBitVec_xor _ _).symm
    refine Eq.trans ?_ (congrArg (· ^^^ _) (UInt32.toBitVec_xor _ _).symm)
    exact congrArg₂ (fun a b => (h i).toBitVec ^^^ a ^^^ b)
      (congrFun key ⟨i.val, by omega⟩).symm (congrFun key ⟨i.val + 8, by omega⟩).symm
  · intro j v hv
    rw [List.range_succ, List.foldl_append, ← hv]
    exact blake2s_round v m j

/-! ## 8. One input array and a separate output array -/

/-- The input context of the compression with one input array: the chaining words and the
    message words in one array of `24` words, the registers `t0`, `t1`, `f0`, and the output
    array of `8` words. -/
abbrev blake2InCtxtP (w : Nat) : Ctxt jasminDialect :=
  [.stackArr w 24, .reg w, .reg w, .reg w, .stackArr w 8]

/-- The input array of the compression: the chaining word `H i` at the index `i` and the
    message word `M j` at the index `8 + j`. -/
def blake2InWords {w : Nat} (H : Fin 8 → BitVec w) (M : Fin 16 → BitVec w) :
    Fin 24 → BitVec w :=
  fun i => if h : i.val < 8 then H ⟨i.val, h⟩ else M ⟨i.val - 8, by omega⟩

/-- The last stage of the compression at the variables `env` of the numbered input words and
    the output array `oarr`: the compiled symbolic compression `blake2Lets P` from the word
    numbered `27`, and the stores of the eight new chaining words into `oarr` at register
    indices. -/
def blake2TailP (P : Blake2Params) {Γ : Ctxt jasminDialect} (env : Nat → Var Γ (.reg P.w))
    (oarr : Var Γ (.stackArr P.w 8)) : Com jasminDialect Γ (.stackArr P.w 8) :=
  genLetsR (blake2Lets P).2.rev.reverse 27 env fun ρ env4 =>
    genStoresIdx (blake2Lets P).1 (ρ _ oarr) env4

/-- **The BLAKE2 compression function at `P` with one input array and an output array**: the
    loads of the `24` words of the input array as the words numbered `0, …, 23`, the
    registers `t0`, `t1`, `f0` as the words numbered `24`, `25`, `26`, and the stage
    `blake2TailP` with the output array, which the program does not read. -/
def blake2CompressBodyP (P : Blake2Params) :
    Com jasminDialect (blake2InCtxtP P.w) (.stackArr P.w 8) :=
  genLoads (List.range 24) Var.here 0 (fun _ => .there .here) fun ρ env =>
  blake2TailP P (fun i =>
    if i = 24 then ρ _ (.there .here)
    else if i = 25 then ρ _ (.there (.there .here))
    else if i = 26 then ρ _ (.there (.there (.there .here)))
    else env i) (ρ _ (.there (.there (.there (.there .here)))))

/-- The stage `blake2TailP` at variables holding values that agree with the chaining,
    message, counter and flag words below the word numbered `27` returns the reference
    compression, whatever the contents of the output array. -/
theorem blake2TailP_value (P : Blake2Params) (H : Fin 8 → BitVec P.w)
    (M : Fin 16 → BitVec P.w) (T : Fin 3 → BitVec P.w) {Γ : Ctxt jasminDialect}
    (env : Nat → Var Γ (.reg P.w)) (oarr : Var Γ (.stackArr P.w 8)) (V : Valuation Γ)
    (ρv : Nat → BitVec P.w)
    (henv : ∀ i, (env i).lookup V = ρv i) (hρ : ∀ i < 27, ρv i = blake2Inputs H M T i) :
    (blake2TailP P env oarr).denote V = P.blake2CompressRef H M (T 0) (T 1) (T 2) := by
  unfold blake2TailP
  refine genLetsR_denote _ 27 env _ V ρv henv _ fun ρ V4 env4 hρ4 henv4 => ?_
  obtain ⟨hl, hk, hv⟩ := blake2Lets_spec P H M T _ hρ
  have hL : ∀ p ∈ (blake2Lets P).1, p.1 < 2 ^ 64 := by
    intro p hp
    obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.mp hp
    have h := hk k (by omega)
    rw [List.getD_eq_getElem _ _ hk'] at h
    omega
  refine (genStoresIdx_denote (blake2Lets P).1 (ρ _ oarr) env4 V4 _ (hρ4 _ oarr) _
    (fun i => henv4 i) hL).trans ?_
  rw [foldl_stores8 _ hl hk]
  exact hv

/-- The stage `blake2TailP` has fixed events at leakage parameters with no variable-time
    operation. -/
theorem blake2TailP_fixed (P : Blake2Params) (Pj : JLeakParams)
    (hV : ∀ op, Pj.opVT op = none) {Γ : Ctxt jasminDialect} (env : Nat → Var Γ (.reg P.w))
    (oarr : Var Γ (.stackArr P.w 8)) :
    LeakFixed (jLeakModel Pj) (blake2TailP P env oarr) := by
  unfold blake2TailP
  exact genLetsR_fixed Pj hV _ _ _ _ fun _ _ => genStoresIdx_fixed Pj hV _ _ _

/-- The words numbered below `24` after the loads of the input array `blake2InWords H M`:
    the chaining word `H i` numbered `i` and the message word `M j` numbered `8 + j`. -/
theorem blake2LoadValsP_lt24 (P : Blake2Params) (H : Fin 8 → BitVec P.w)
    (M : Fin 16 → BitVec P.w) (T : Fin 3 → BitVec P.w) (ρ0 : Nat → BitVec P.w) (i : Nat)
    (hi : i < 24) :
    loadVals (blake2InWords H M) ρ0 0 (List.range 24) i = blake2Inputs H M T i := by
  rw [loadVals_apply, ite_eq_left (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
    List.getElem_range, Nat.sub_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    show i = ((⟨i, hi⟩ : Fin 24) : Nat) from rfl, stackGet_id]
  by_cases h8 : i < 8
  · simp [blake2InWords, blake2Inputs, h8]
  · simp [blake2InWords, blake2Inputs, h8, show i - 8 < 16 by omega]

/-- **The value of the BLAKE2 template with one input array and an output array**: at the
    input array `blake2InWords H M` of the chaining words `H` and the message words `M`, the
    registers `t0`, `t1`, `f0` and any contents `O` of the output array, the program returns
    the reference compression `blake2CompressRef P H M t0 t1 f0`. -/
theorem blake2CompressBodyP_value (P : Blake2Params) (H : Fin 8 → BitVec P.w)
    (M : Fin 16 → BitVec P.w) (t0 t1 f0 : BitVec P.w) (O : Fin 8 → BitVec P.w) :
    (blake2CompressBodyP P).denote
        (.cons (blake2InWords H M) (.cons t0 (.cons t1 (.cons f0 (.cons O .nil))))) =
      P.blake2CompressRef H M t0 t1 f0 := by
  unfold blake2CompressBodyP
  refine genLoads_denote _ _ 0 _ _ _ (blake2InWords H M) rfl (fun _ => t0) (fun _ => rfl) _
    fun ρ V2 env2 hρ henv2 => ?_
  refine blake2TailP_value P H M ![t0, t1, f0] _ _ V2 (fun i =>
    if i = 24 then t0 else if i = 25 then t1 else if i = 26 then f0
    else loadVals (blake2InWords H M) (fun _ => t0) 0 (List.range 24) i) ?_ ?_
  · intro i
    split_ifs
    · exact hρ _ _
    · exact hρ _ _
    · exact hρ _ _
    · exact henv2 i
  · intro i hi
    by_cases h24 : i < 24
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      exact blake2LoadValsP_lt24 P H M _ _ i h24
    · rcases (show i = 24 ∨ i = 25 ∨ i = 26 by omega) with rfl | rfl | rfl <;>
        simp [blake2Inputs]

/-- **The events of the BLAKE2 template with one input array and an output array are
    fixed**: at leakage parameters with no variable-time operation, the program emits the same
    events at every two valuations. -/
theorem blake2CompressBodyP_events (P : Blake2Params) (Pj : JLeakParams)
    (hV : ∀ op, Pj.opVT op = none) : LeakFixed (jLeakModel Pj) (blake2CompressBodyP P) := by
  unfold blake2CompressBodyP
  exact genLoads_fixed Pj hV _ _ _ _ _ fun _ _ => blake2TailP_fixed P Pj hV _ _

end CatCrypt.Crypto.SecureCompilation.HashTemplate
