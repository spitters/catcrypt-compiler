/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.HashTemplate.StraightLine
public import CatCrypt.Crypto.Primitives.Keccak

/-!
# The Keccak-f[1600] permutation as a `jasminDialect` template

`keccakFBody` is the permutation Keccak-f[1600] of FIPS 202 as a straight-line program of
`jasminDialect`, generated through the compiler of `HashTemplate.StraightLine`. The program
reads the 25 lanes of the state from one stack array of 64-bit words, the lane `(x, y)` at the
index `5 * y + x` (the lane order of FIPS 202 §3.1.2 and of
`Primitives.Keccak.bytesToState`), and returns the 25 lanes of the permuted state in a fresh
stack array in the same order. Its operations are `xor`, `andn` (the `not`-`and` of `χ`),
rotation by an immediate, constants, and the constant-index loads and stores; it has no
data-dependent control flow.

The symbolic round `keccakTRoundLets` binds the five column parities of `θ`, the five words
`D[x]`, the 25 lanes after `θ` and `ρ` (a lane with rotation offset `0` is not rotated), the
25 lanes after `χ` read through the renumbering `π`, and the lane `(0, 0)` after `ι`. A left
rotation by `k` is the right rotation by `64 - k`.

## Main definitions

* `keccakTPushAll`: the binding of a list of word expressions in one step.
* `keccakTRoundLets`: one symbolic round.
* `keccakFLets`: the symbolic permutation, 24 rounds.
* `keccakFBody`: the permutation as a `jasminDialect` program.
* `keccakTOfArr`, `keccakTToArr`: the state of an array of 25 lanes and back.

## Main statements

* `keccakTRoundLets_spec`: a symbolic round evaluates to `Primitives.Keccak.keccakRound`.
* `keccakFBody_value`: the program denotes `Primitives.Keccak.keccakF`.
* `keccakFBody_events`: the program emits the same events at every two valuations.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplate (LeakFixed)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open Ctxt (Var Valuation)

/-! ## 1. Binding a list of independent word expressions -/

/-- Every word numbered in the expression is below `n`. -/
def keccakTVarsLt {w : Nat} (n : Nat) : WExp w → Prop
  | .var i => i < n
  | .const _ => True
  | .bin _ a b => keccakTVarsLt n a ∧ keccakTVarsLt n b
  | .rotr _ a => keccakTVarsLt n a
  | .shr _ a => keccakTVarsLt n a

theorem keccakTVarsLt_mono {w : Nat} {n m : Nat} (h : n ≤ m) (e : WExp w)
    (he : keccakTVarsLt n e) : keccakTVarsLt m e := by
  (fun_induction keccakTVarsLt n e) <;> grind only [keccakTVarsLt]

/-- An expression over the words below `n` has the same value at two valuations agreeing
    below `n`. -/
theorem keccakTVarsLt_eval {w : Nat} {n : Nat} (e : WExp w) (he : keccakTVarsLt n e)
    (ρ ρ' : Nat → BitVec w) (hρ : ∀ j < n, ρ j = ρ' j) : e.eval ρ = e.eval ρ' := by
  induction e with
  | var i => exact hρ i he
  | const x => rfl
  | bin op a b iha ihb => simp only [WExp.eval, iha he.1, ihb he.2]
  | rotr k a iha => simp only [WExp.eval, iha he]
  | shr k a iha => simp only [WExp.eval, iha he]

/-- A let-list of expressions over the words below its first binding binds, at the position
    `k`, the value of its `k`-th expression at the input values. -/
theorem keccakTEvalLets_indep {w : Nat} (es : List (WExp w)) :
    ∀ (ρ : Nat → BitVec w) (n : Nat), (∀ e ∈ es, keccakTVarsLt n e) →
      ∀ k (hk : k < es.length), evalLets ρ n es (n + k) = es[k].eval ρ := by
  induction es with
  | nil => intro _ _ _ k hk; simp at hk
  | cons e es ih =>
      intro ρ n hes k hk
      simp only [evalLets]
      cases k with
      | zero =>
          rw [Nat.add_zero, evalLets_of_lt _ _ _ _ (by omega)]
          simp
      | succ k =>
          rw [show n + (k + 1) = (n + 1) + k by omega,
            ih _ _ (fun e' he' => keccakTVarsLt_mono (by omega) e'
              (hes e' (List.mem_cons_of_mem _ he'))) k (by simp at hk; omega)]
          simp only [List.getElem_cons_succ]
          exact keccakTVarsLt_eval _ (hes _ (List.mem_cons_of_mem _ (List.getElem_mem _))) _ _
            (fun j hj => by simp [Nat.ne_of_lt hj])

/-- The binding of the expressions `es`, in list order, after the let-list `s`. -/
def keccakTPushAll {w : Nat} (es : List (WExp w)) (s : LetSt w) : LetSt w :=
  ⟨s.next + es.length, es.reverse ++ s.rev⟩

/-- The binding of the expressions `f 0, …, f (n - 1)` over the words below `s.next`: the
    expression `f i` binds the word numbered `s.next + i` to its value at `s`, and the words
    below `s.next` are unchanged. -/
theorem keccakTPushOfFn_spec {w b n : Nat} (f : Fin n → WExp w) (s : LetSt w) (hs : s.Good b)
    (hf : ∀ i, keccakTVarsLt s.next (f i)) (ρ : Nat → BitVec w) :
    (keccakTPushAll (List.ofFn f) s).Good b ∧
      (keccakTPushAll (List.ofFn f) s).next = s.next + n ∧
      (∀ j < s.next, (keccakTPushAll (List.ofFn f) s).val b ρ j = s.val b ρ j) ∧
      ∀ i : Fin n, (keccakTPushAll (List.ofFn f) s).val b ρ (s.next + i.val) =
        (f i).eval (s.val b ρ) := by
  have hval : ∀ j, (keccakTPushAll (List.ofFn f) s).val b ρ j =
      evalLets (s.val b ρ) s.next (List.ofFn f) j := by
    intro j
    have := LetSt.val_extend ρ hs (s.next + (List.ofFn f).length) (List.ofFn f).reverse
    simp only [List.reverse_reverse] at this
    exact congrFun this j
  refine ⟨?_, by simp [keccakTPushAll], fun j hj => ?_, fun i => ?_⟩
  · unfold LetSt.Good at hs ⊢
    simp [keccakTPushAll, hs]
    omega
  · rw [hval]
    exact evalLets_of_lt _ _ _ _ hj
  · rw [hval, keccakTEvalLets_indep _ _ _ (fun e he => ?_) i.val (by simp)]
    · simp
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
      exact hf j

/-! ## 2. The symbolic round -/

/-- A left rotation by `k`: the right rotation by `64 - k`, and no operation at `k = 0`. -/
def keccakTRotl (k : Nat) (e : WExp 64) : WExp 64 :=
  if k = 0 then e else .rotr (64 - k) e

theorem keccakTRotl_eval (k : Nat) (hk : k < 64) (e : WExp 64) (ρ : Nat → BitVec 64) :
    (keccakTRotl k e).eval ρ = (e.eval ρ).rotateLeft k := by
  by_cases h0 : k = 0 <;> simp only [keccakTRotl, h0, ite_true, ite_false, WExp.eval,
    BitVec.rotateLeft_def, BitVec.rotateRight_def]
  · simp [BitVec.ushiftRight_eq_zero]
  · rw [Nat.mod_eq_of_lt (by omega : 64 - k < 64), Nat.mod_eq_of_lt hk,
      show 64 - (64 - k) = k by omega, BitVec.or_comm]

theorem keccakTRotl_varsLt (k n : Nat) (e : WExp 64) (he : keccakTVarsLt n e) :
    keccakTVarsLt n (keccakTRotl k e) := by
  grind only [keccakTRotl, keccakTVarsLt]

/-- The column `x` of the lane index `i = 5 * y + x`. -/
def keccakTX (i : Fin 25) : Fin 5 := ⟨i.val % 5, by omega⟩

/-- The row `y` of the lane index `i = 5 * y + x`. -/
def keccakTY (i : Fin 25) : Fin 5 := ⟨i.val / 5, by omega⟩

/-- The column parity `C[x]` of `θ` on the lanes numbered `st`. -/
def keccakTColE (st : Fin 5 → Fin 5 → Nat) (x : Fin 5) : WExp 64 :=
  .bin .xor (.bin .xor (.bin .xor (.bin .xor (.var (st x 0)) (.var (st x 1))) (.var (st x 2)))
    (.var (st x 3))) (.var (st x 4))

/-- The word `D[x] = C[x - 1] ⊕ rotl(C[x + 1], 1)` of `θ`, the parity `C[x]` numbered
    `c + x`. -/
def keccakTDE (c : Nat) (x : Fin 5) : WExp 64 :=
  .bin .xor (.var (c + (x.val + 4) % 5)) (keccakTRotl 1 (.var (c + (x.val + 1) % 5)))

/-- The lane of index `i` after `θ` and `ρ`, the lane `(x, y)` numbered `st x y` and the word
    `D[x]` numbered `d + x`. -/
def keccakTThetaRhoE (st : Fin 5 → Fin 5 → Nat) (d : Nat) (i : Fin 25) : WExp 64 :=
  keccakTRotl (Primitives.Keccak.rotOffset (keccakTX i) (keccakTY i))
    (.bin .xor (.var (st (keccakTX i) (keccakTY i))) (.var (d + (keccakTX i).val)))

/-- The lane of index `i` after `χ`, the lane `(x, y)` numbered `p x y`. -/
def keccakTChiE (p : Fin 5 → Fin 5 → Nat) (i : Fin 25) : WExp 64 :=
  .bin .xor (.var (p (keccakTX i) (keccakTY i)))
    (.bin .andn (.var (p ⟨((keccakTX i).val + 1) % 5, by omega⟩ (keccakTY i)))
      (.var (p ⟨((keccakTX i).val + 2) % 5, by omega⟩ (keccakTY i))))

/-- **One symbolic Keccak round** with the round constant `rc` on the lanes numbered `st`:
    binds the column parities, the words `D`, the lanes after `θ` and `ρ`, the lanes after `π`
    and `χ`, and the lane `(0, 0)` after `ι`; returns the numbers of the new lanes. -/
def keccakTRoundLets (rc : BitVec 64) (st : Fin 5 → Fin 5 → Nat) (s : LetSt 64) :
    (Fin 5 → Fin 5 → Nat) × LetSt 64 :=
  let s1 := keccakTPushAll (List.ofFn (keccakTColE st)) s
  let s2 := keccakTPushAll (List.ofFn (keccakTDE s.next)) s1
  let s3 := keccakTPushAll (List.ofFn (keccakTThetaRhoE st s1.next)) s2
  let p : Fin 5 → Fin 5 → Nat := fun x y => s2.next + 5 * x.val + (x.val + 3 * y.val) % 5
  let s4 := keccakTPushAll (List.ofFn (keccakTChiE p)) s3
  let s5 := (s4.push (.bin .xor (.var s3.next) (.const rc))).2
  (fun x y => if x.val = 0 ∧ y.val = 0 then s4.next else s3.next + 5 * y.val + x.val, s5)

/-- The numbering of the input lanes: the lane `(x, y)` is the word numbered `5 * y + x`. -/
def keccakTInit : Fin 5 → Fin 5 → Nat := fun x y => 5 * y.val + x.val

/-- **The symbolic Keccak-f[1600] permutation**: the 24 rounds from the input lanes, the lane
    `(x, y)` the word numbered `5 * y + x`, with the let-bound words from the word numbered
    `25`; returns the numbers of the output lanes and the let-list. -/
def keccakFLets : (Fin 5 → Fin 5 → Nat) × LetSt 64 :=
  (List.finRange 24).foldl
    (fun q r => keccakTRoundLets (Primitives.Keccak.roundConstant r.val) q.1 q.2)
    (keccakTInit, ⟨25, []⟩)

/-! ## 3. The program -/

/-- The store list of the output lanes: the index `i` receives the lane
    `(keccakTX i, keccakTY i)` numbered by `st`. -/
def keccakTOuts (st : Fin 5 → Fin 5 → Nat) : List (Nat × Nat) :=
  (List.finRange 25).map fun i => (i.val, st (keccakTX i) (keccakTY i))

/-- **The Keccak-f[1600] permutation as a `jasminDialect` program**: the loads of the 25 input
    lanes, the compiled symbolic permutation `keccakFLets`, and the stores of the 25 output
    lanes into a fresh array; the lane `(x, y)` is at the index `5 * y + x`. -/
def keccakFBody : Com jasminDialect [.stackArr 64 25] (.stackArr 64 25) :=
  let L := keccakFLets
  genLoad (Var.here) 0 fun ρ0 v0 =>
  genLoads (List.range' 1 24) (ρ0 _ .here) 1 (fun _ => v0) fun _ env1 =>
  genLets L.2.rev.reverse 25 env1 fun env2 =>
  .var ⟨.stackZero 64 25, rfl, .nil⟩
    (genStores (keccakTOuts L.1) .here (fun i => (env2 i).there))

/-! ## 4. Values -/

/-- The Keccak state of an array of 25 lanes, the lane `(x, y)` at the index `5 * y + x`. -/
def keccakTOfArr (A : Fin 25 → BitVec 64) : Primitives.Keccak.KState :=
  fun x y => A ⟨5 * y.val + x.val, by omega⟩

/-- The array of 25 lanes of a Keccak state, the lane `(x, y)` at the index `5 * y + x`. -/
def keccakTToArr (a : Primitives.Keccak.KState) : Fin 25 → BitVec 64 :=
  fun i => a (keccakTX i) (keccakTY i)

/-- The lanes numbered `q.1` in the let-list `q.2` hold the state `v`. -/
def KeccakTInv (ρ : Nat → BitVec 64) (q : (Fin 5 → Fin 5 → Nat) × LetSt 64)
    (v : Primitives.Keccak.KState) : Prop :=
  q.2.Good 25 ∧ (∀ x y, q.1 x y < q.2.next) ∧ ∀ x y, q.2.val 25 ρ (q.1 x y) = v x y

theorem keccakTRotOffset_lt (x y : Fin 5) : Primitives.Keccak.rotOffset x y < 64 := by
  unfold Primitives.Keccak.rotOffset
  exact Nat.mod_lt _ (by omega)

/-- **A symbolic round evaluates to `Primitives.Keccak.keccakRound`**, at every round
    constant. -/
theorem keccakTRoundLets_spec (ρ : Nat → BitVec 64) (rc : BitVec 64)
    (q : (Fin 5 → Fin 5 → Nat) × LetSt 64) (v : Primitives.Keccak.KState)
    (hq : KeccakTInv ρ q v) :
    KeccakTInv ρ (keccakTRoundLets rc q.1 q.2) (Primitives.Keccak.keccakRound v rc) := by
  obtain ⟨st, s0⟩ := q
  obtain ⟨hg, hlt, hv⟩ := hq
  simp only at hg hlt hv
  -- θ: the column parities
  obtain ⟨g1, n1, p1, v1⟩ := keccakTPushOfFn_spec (keccakTColE st) s0 hg
    (fun x => by simp [keccakTColE, keccakTVarsLt, hlt]) ρ
  generalize hs1 : keccakTPushAll (List.ofFn (keccakTColE st)) s0 = s1 at g1 n1 p1 v1
  let C : Fin 5 → BitVec 64 := fun x => v x 0 ^^^ v x 1 ^^^ v x 2 ^^^ v x 3 ^^^ v x 4
  have hC : ∀ x : Fin 5, s1.val 25 ρ (s0.next + x.val) = C x := by
    intro x
    rw [v1 x]
    simp only [keccakTColE, WExp.eval, JasminBinOp.apply, hv, C]
  -- θ: the words `D`
  obtain ⟨g2, n2, p2, v2⟩ := keccakTPushOfFn_spec (keccakTDE s0.next) s1 g1
    (fun x => ⟨by simp only [keccakTVarsLt]; omega,
      keccakTRotl_varsLt _ _ _ (by simp only [keccakTVarsLt]; omega)⟩) ρ
  generalize hs2 : keccakTPushAll (List.ofFn (keccakTDE s0.next)) s1 = s2 at g2 n2 p2 v2
  let D : Fin 5 → BitVec 64 := fun x =>
    C ⟨(x.val + 4) % 5, by omega⟩ ^^^ (C ⟨(x.val + 1) % 5, by omega⟩).rotateLeft 1
  have hC' : ∀ k (h : k < 5), s1.val 25 ρ (s0.next + k) = C ⟨k, h⟩ := fun k h => hC ⟨k, h⟩
  have hD : ∀ x : Fin 5, s2.val 25 ρ (s1.next + x.val) = D x := by
    intro x
    rw [v2 x]
    simp only [keccakTDE, WExp.eval, JasminBinOp.apply, keccakTRotl_eval 1 (by omega)]
    rw [hC' ((x.val + 4) % 5) (by omega), hC' ((x.val + 1) % 5) (by omega)]
  have hD' : ∀ k (h : k < 5), s2.val 25 ρ (s1.next + k) = D ⟨k, h⟩ := fun k h => hD ⟨k, h⟩
  -- θ and ρ
  obtain ⟨g3, n3, p3, v3⟩ := keccakTPushOfFn_spec (keccakTThetaRhoE st s1.next) s2 g2
    (fun i => keccakTRotl_varsLt _ _ _
      ⟨by simp only [keccakTVarsLt]; have := hlt (keccakTX i) (keccakTY i); omega,
        by simp only [keccakTVarsLt]; have := (keccakTX i).isLt; omega⟩) ρ
  generalize hs3 : keccakTPushAll (List.ofFn (keccakTThetaRhoE st s1.next)) s2 = s3
    at g3 n3 p3 v3
  let p : Fin 5 → Fin 5 → Nat := fun x y => s2.next + 5 * x.val + (x.val + 3 * y.val) % 5
  have hB : ∀ x y : Fin 5, s3.val 25 ρ (p x y) =
      Primitives.Keccak.pi (Primitives.Keccak.rho (Primitives.Keccak.theta v)) x y := by
    intro x y
    have hi : 5 * x.val + (x.val + 3 * y.val) % 5 < 25 := by omega
    have e := v3 ⟨5 * x.val + (x.val + 3 * y.val) % 5, hi⟩
    have eX : keccakTX ⟨5 * x.val + (x.val + 3 * y.val) % 5, hi⟩ =
        ⟨(x.val + 3 * y.val) % 5, by omega⟩ := Fin.ext (by simp only [keccakTX]; omega)
    have eY : keccakTY ⟨5 * x.val + (x.val + 3 * y.val) % 5, hi⟩ = x :=
      Fin.ext (by simp only [keccakTY]; omega)
    simp only [keccakTThetaRhoE, eX, eY] at e
    simp only [p]
    rw [Nat.add_assoc, e, keccakTRotl_eval _ (keccakTRotOffset_lt _ _)]
    have hst := hlt ⟨(x.val + 3 * y.val) % 5, by omega⟩ x
    simp only [WExp.eval, JasminBinOp.apply]
    rw [p2 _ (by omega), p1 _ hst, hv, hD' _ (by omega)]
    unfold Primitives.Keccak.pi Primitives.Keccak.rho Primitives.Keccak.theta
    rfl
  -- π and χ
  obtain ⟨g4, n4, p4, v4⟩ := keccakTPushOfFn_spec (keccakTChiE p) s3 g3
    (fun i => ⟨by simp only [keccakTVarsLt, p]; omega,
      by simp only [keccakTVarsLt, p]; omega, by simp only [keccakTVarsLt, p]; omega⟩) ρ
  generalize hs4 : keccakTPushAll (List.ofFn (keccakTChiE p)) s3 = s4 at g4 n4 p4 v4
  have hH : ∀ x y : Fin 5, s4.val 25 ρ (s3.next + 5 * y.val + x.val) =
      Primitives.Keccak.chi
        (Primitives.Keccak.pi (Primitives.Keccak.rho (Primitives.Keccak.theta v))) x y := by
    intro x y
    have hi : 5 * y.val + x.val < 25 := by omega
    have e := v4 ⟨5 * y.val + x.val, hi⟩
    have eX : keccakTX ⟨5 * y.val + x.val, hi⟩ = x := Fin.ext (by simp only [keccakTX]; omega)
    have eY : keccakTY ⟨5 * y.val + x.val, hi⟩ = y := Fin.ext (by simp only [keccakTY]; omega)
    simp only [keccakTChiE, eX, eY] at e
    rw [Nat.add_assoc, e]
    simp only [WExp.eval, JasminBinOp.apply, hB]
    unfold Primitives.Keccak.chi
    rfl
  -- ι
  have hround : keccakTRoundLets rc st s0 =
      (fun x y => if x.val = 0 ∧ y.val = 0 then s4.next else s3.next + 5 * y.val + x.val,
        (s4.push (.bin .xor (.var s3.next) (.const rc))).2) := by
    subst hs1 hs2 hs3 hs4
    rfl
  rw [hround]
  have hH0 : s4.val 25 ρ s3.next = Primitives.Keccak.chi
      (Primitives.Keccak.pi (Primitives.Keccak.rho (Primitives.Keccak.theta v))) 0 0 := by
    simpa using hH 0 0
  have hv5 := LetSt.push_val (.bin .xor (.var s3.next) (.const rc)) g4 ρ
  refine ⟨LetSt.push_good _ g4, fun x y => ?_, fun x y => ?_⟩
  · show (if x.val = 0 ∧ y.val = 0 then s4.next else s3.next + 5 * y.val + x.val) < s4.next + 1
    split <;> omega
  · simp only [hv5]
    unfold Primitives.Keccak.keccakRound Primitives.Keccak.iota
    by_cases h : x.val = 0 ∧ y.val = 0
    · have hx : x = 0 := Fin.ext h.1
      have hy : y = 0 := Fin.ext h.2
      subst hx hy
      simp [WExp.eval, JasminBinOp.apply, hH0]
    · rw [ite_eq_right h, ite_eq_right (by omega), hH]
      simp only [Bool.and_eq_true, beq_iff_eq, h, ite_false]

/-- The symbolic permutation evaluates to `Primitives.Keccak.keccakF` at input values
    agreeing with the array `A` below the word numbered `25`. -/
theorem keccakFLets_spec (A : Fin 25 → BitVec 64) (ρ : Nat → BitVec 64)
    (hρ : ∀ i (h : i < 25), ρ i = A ⟨i, h⟩) :
    KeccakTInv ρ keccakFLets (Primitives.Keccak.keccakF (keccakTOfArr A)) := by
  unfold keccakFLets Primitives.Keccak.keccakF
  rw [Fin.foldl_eq_finRange_foldl]
  refine List.foldl_rel ?_ fun r _ q v hq => keccakTRoundLets_spec ρ _ q v hq
  refine ⟨rfl, fun x y => ?_, fun x y => ?_⟩
  · show 5 * y.val + x.val < 25
    omega
  · exact hρ (5 * y.val + x.val) (by omega)

/-- A store at an index `j : Fin m` updates the entry `j`. -/
theorem keccakTStackSet_fin {w m : Nat} (A : Fin m → BitVec w) (j : Fin m) (v : BitVec w) :
    stackSet A j.val v = fun i => if i = j then v else A i := by
  cases m with
  | zero => exact j.elim0
  | succ m =>
      funext i
      simp [stackSet, Nat.mod_eq_of_lt j.isLt]

/-- Stores of the words `g j` at the indices `j` of a list of indices write `g j` at each
    listed index. -/
theorem keccakTFoldlStores {w m : Nat} (l : List (Fin m)) (g : Fin m → Nat)
    (ρv : Nat → BitVec w) (A : Fin m → BitVec w) :
    (l.map fun j => (j.val, g j)).foldl (fun A p => stackSet A p.1 (ρv p.2)) A =
      fun i => if i ∈ l then ρv (g i) else A i := by
  induction l generalizing A with
  | nil => funext i; simp
  | cons j l ih =>
      simp only [List.map_cons, List.foldl_cons, ih, keccakTStackSet_fin]
      funext i
      by_cases hi : i ∈ l <;> by_cases hij : i = j <;> simp_all

/-- **The value of the Keccak template**: at the lanes `A`, the lane `(x, y)` at the index
    `5 * y + x`, the program returns the lanes of `Primitives.Keccak.keccakF` in the same
    order. -/
theorem keccakFBody_value (A : Fin 25 → BitVec 64) :
    keccakFBody.denote (.cons A .nil) =
      keccakTToArr (Primitives.Keccak.keccakF (keccakTOfArr A)) := by
  have hA : ∀ i (h : i < 25), stackGet A (BitVec.ofNat 64 i).toNat = A ⟨i, h⟩ := fun i h => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact stackGet_id A ⟨i, h⟩
  unfold keccakFBody
  refine genLoad_denote _ 0 _ _ A rfl _ fun ρ0 V0 v0 hρ0 hv0 => ?_
  refine genLoads_denote _ _ 1 _ _ V0 A (hρ0 _ _) (fun _ => stackGet A (BitVec.ofNat 64 0).toNat)
    (fun _ => hv0) _ fun _ V1 env1 _ henv1 => ?_
  refine genLets_denote _ 25 env1 _ V1 _ henv1 _ fun V2 env2 henv2 => ?_
  refine (genStores_denote (keccakTOuts keccakFLets.1) .here (fun i => (env2 i).there)
    (Ctxt.Valuation.extend V2 (JasminTy.default (.stackArr 64 25))) _ rfl _
    (fun i => henv2 i)).trans ?_
  have hagree : ∀ i (h : i < 25), loadVals A (fun _ => stackGet A (BitVec.ofNat 64 0).toNat) 1
      (List.range' 1 24) i = A ⟨i, h⟩ := by
    intro i hi
    rw [loadVals_apply]
    by_cases h0 : i = 0
    · subst h0
      rw [ite_eq_right (by omega)]
      exact hA 0 (by omega)
    · rw [ite_eq_left (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
        List.getElem_range', show 1 + 1 * (i - 1) = i by omega]
      exact hA i hi
  obtain ⟨-, -, hv⟩ := keccakFLets_spec A _ hagree
  unfold keccakTOuts
  rw [keccakTFoldlStores]
  funext i
  simp only [List.mem_finRange, ite_true]
  rw [keccakTToArr, ← hv, LetSt.val]

/-- **The events of the Keccak template are fixed**: at leakage parameters with no
    variable-time operation, the program emits the same events at every two valuations. -/
theorem keccakFBody_events (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none) :
    LeakFixed (jLeakModel Pj) keccakFBody := by
  unfold keccakFBody
  exact genLoad_fixed Pj hV _ _ _ fun _ _ => genLoads_fixed Pj hV _ _ _ _ _ fun _ _ =>
    genLets_fixed Pj hV _ _ _ _ fun _ =>
      leakFixed_var_quiet Pj _ _ (by simp [Dialects.JasminComLLeak.jKind, hV])
        (genStores_fixed Pj hV _ _ _)

end CatCrypt.Crypto.SecureCompilation.HashTemplate
