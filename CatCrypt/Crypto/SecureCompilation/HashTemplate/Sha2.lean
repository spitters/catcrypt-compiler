/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.HashTemplate.StraightLine
public import CatCrypt.Crypto.Primitives.SHA256
public import CatCrypt.Crypto.Primitives.SHA512

/-!
# The SHA-2 compression function as a `jasminDialect` template

The six SHA-2 hash functions of FIPS 180-4 (SHA-224, SHA-256, SHA-384, SHA-512,
SHA-512/224 and SHA-512/256) share one compression function, parametric in the word width,
the round count, the rotation and shift amounts of `Σ0`, `Σ1`, `σ0`, `σ1`, and the round
constants; the initial hash value is the only further parameter of the hash. A record
`Sha2FamilyParams` collects these parameters, and `sha2CompressBody P` is the compression function
at `P` as a straight-line program of `jasminDialect`, generated from `P` by recursion over the
rounds. The six standards are six values of `Sha2FamilyParams` and share the one template.

The program reads the eight chaining words and the sixteen message words from two stack
arrays, and returns the eight new chaining words in a fresh stack array. Its operations are
word addition, rotation and shift by an immediate, `xor`, `and`, `andn` (the `not`-`and` of
`Ch`), constants, and the constant-index loads and stores of the two arrays; it has no
data-dependent control flow.

The program is generated in two stages. The first is symbolic: `sha2Lets P` is a list of
let-bound word expressions `WExp` over numbered words, with the message schedule interleaved
with the rounds. The second, `genLets` of `HashTemplate.StraightLine`, compiles a list of word
expressions to a straight-line `Com` in continuation-passing style over the context
extensions; it is independent of SHA-2.

## Main definitions

* `Sha2FamilyParams`, `Sha2Amounts`: the parameters of the SHA-2 compression function.
* `Sha2FamilyParams.sha2CompressRef`: the FIPS 180-4 compression function at the parameters, on
  `BitVec` words.
* `sha2Lets`: the symbolic SHA-2 compression.
* `sha2CompressBody`: the compression function as a `jasminDialect` program.
* `sha2CompressBodyP`, `sha2InWords`: the compression function with one input array of the
  chaining and message words and an output array that it does not read.
* `sha224P`, `sha256P`, `sha384P`, `sha512P`, `sha512t224P`, `sha512t256P`: the six standards.

## Main results

* `sha2Lets_eval`: the symbolic compression evaluates to `sha2CompressRef`.
* `sha2CompressBody_value`: the program denotes `sha2CompressRef`.
* `sha2CompressBody_events`: the program emits the same events at every two valuations.
* `sha2CompressBodyP_value`, `sha2CompressBodyP_events`: the same for `sha2CompressBodyP`.
* `sha2CompressBody_sha256`, `sha2CompressBody_sha512`: agreement with the compression
  functions `Primitives.SHA256.compress` and `Primitives.SHA512.compress`.
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

/-- The three amounts of one of the functions `Σ0`, `Σ1`, `σ0`, `σ1`: two rotations and a
    third rotation (for `Σ0`, `Σ1`) or a right shift (for `σ0`, `σ1`). -/
structure Sha2Amounts where
  /-- The first rotation amount. -/
  r1 : Nat
  /-- The second rotation amount. -/
  r2 : Nat
  /-- The third rotation amount, or the shift amount. -/
  r3 : Nat
  deriving DecidableEq, Repr

/-- **The parameters of the SHA-2 compression function** (FIPS 180-4 §4.1.2, §4.1.3, §4.2,
    §5.3): the word width, the round count, the amounts of `Σ0`, `Σ1`, `σ0`, `σ1`, the round
    constants and the initial hash value. The shift amounts of `σ0`, `σ1` are below the word
    width. -/
structure Sha2FamilyParams where
  /-- The word width. -/
  w : Nat
  /-- The word width is `32` or `64`. -/
  hw : w = 32 ∨ w = 64
  /-- The round count. -/
  rounds : Nat
  /-- The amounts of `Σ0`. -/
  bigSigma0 : Sha2Amounts
  /-- The amounts of `Σ1`. -/
  bigSigma1 : Sha2Amounts
  /-- The amounts of `σ0`. -/
  smallSigma0 : Sha2Amounts
  /-- The amounts of `σ1`. -/
  smallSigma1 : Sha2Amounts
  /-- The round constants. -/
  K : List (BitVec w)
  /-- One round constant per round. -/
  hK : K.length = rounds
  /-- The initial hash value. -/
  H0 : Fin 8 → BitVec w
  /-- The shift amounts of `σ0` and `σ1` are below the word width. -/
  hshr : smallSigma0.r3 < w ∧ smallSigma1.r3 < w

/-! ## 2. The reference compression function -/

namespace Sha2FamilyParams

/-- `Σ` of FIPS 180-4: the `xor` of three rotations. -/
def bigS {w : Nat} (a : Sha2Amounts) (x : BitVec w) : BitVec w :=
  x.rotateRight a.r1 ^^^ x.rotateRight a.r2 ^^^ x.rotateRight a.r3

/-- `σ` of FIPS 180-4: the `xor` of two rotations and a right shift. -/
def smallS {w : Nat} (a : Sha2Amounts) (x : BitVec w) : BitVec w :=
  x.rotateRight a.r1 ^^^ x.rotateRight a.r2 ^^^ (x >>> a.r3)

/-- `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)`. -/
def ch {w : Nat} (x y z : BitVec w) : BitVec w := (x &&& y) ^^^ (~~~x &&& z)

/-- `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`. -/
def maj {w : Nat} (x y z : BitVec w) : BitVec w := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- The message schedule word `W t` of the message words `M`: `M t` for `t < 16`, and
    `σ1(W (t-2)) + W (t-7) + σ0(W (t-15)) + W (t-16)` otherwise. -/
def schedule (P : Sha2FamilyParams) (M : Fin 16 → BitVec P.w) (t : Nat) : BitVec P.w :=
  if h : t < 16 then M ⟨t, h⟩
  else
    smallS P.smallSigma1 (schedule P M (t - 2)) + schedule P M (t - 7) +
      smallS P.smallSigma0 (schedule P M (t - 15)) + schedule P M (t - 16)
termination_by t
decreasing_by all_goals omega

/-- One round of the compression on the working words `a, …, h` with the round constant `kt`
    and the schedule word `wt`. -/
def sha2RoundRef (P : Sha2FamilyParams) (s : Fin 8 → BitVec P.w) (kt wt : BitVec P.w) :
    Fin 8 → BitVec P.w :=
  let t1 := s 7 + bigS P.bigSigma1 (s 4) + ch (s 4) (s 5) (s 6) + kt + wt
  let t2 := bigS P.bigSigma0 (s 0) + maj (s 0) (s 1) (s 2)
  ![t1 + t2, s 0, s 1, s 2, s 3 + t1, s 4, s 5, s 6]

/-- **The SHA-2 compression function** at `P` (FIPS 180-4 §6.2.2, §6.4.2): the rounds over the
    chaining words `H` and the schedule of the message words `M`, then the word-wise sum with
    `H`. -/
def sha2CompressRef (P : Sha2FamilyParams) (H : Fin 8 → BitVec P.w) (M : Fin 16 → BitVec P.w) :
    Fin 8 → BitVec P.w :=
  let fin := (List.range P.rounds).foldl
    (fun s t => sha2RoundRef P s (P.K.getD t 0) (schedule P M t)) H
  fun i => H i + fin i

end Sha2FamilyParams

/-! ## 3. The symbolic SHA-2 compression -/

/-- `Σ` on the word numbered `x`. -/
def bigSigmaE {w : Nat} (a : Sha2Amounts) (x : Nat) : WExp w :=
  .bin .xor (.bin .xor (.rotr a.r1 (.var x)) (.rotr a.r2 (.var x))) (.rotr a.r3 (.var x))

/-- `σ` on the word numbered `x`. -/
def smallSigmaE {w : Nat} (a : Sha2Amounts) (x : Nat) : WExp w :=
  .bin .xor (.bin .xor (.rotr a.r1 (.var x)) (.rotr a.r2 (.var x))) (.shr a.r3 (.var x))

/-- `Ch` on the words numbered `x`, `y`, `z`, with `andn` for `¬x ∧ z`. -/
def chE {w : Nat} (x y z : Nat) : WExp w :=
  .bin .xor (.bin .and (.var x) (.var y)) (.bin .andn (.var x) (.var z))

/-- `Maj` on the words numbered `x`, `y`, `z`. -/
def majE {w : Nat} (x y z : Nat) : WExp w :=
  .bin .xor (.bin .xor (.bin .and (.var x) (.var y)) (.bin .and (.var x) (.var z)))
    (.bin .and (.var y) (.var z))

/-- `T1 = h + Σ1(e) + Ch(e, f, g) + K t + W t` on the working words numbered `st`. -/
def t1E (P : Sha2FamilyParams) (st : Fin 8 → Nat) (kt : BitVec P.w) (wt : Nat) : WExp P.w :=
  .bin .add
    (.bin .add (.bin .add (.bin .add (.var (st 7)) (bigSigmaE P.bigSigma1 (st 4)))
      (chE (st 4) (st 5) (st 6))) (.const kt))
    (.var wt)

/-- `T2 = Σ0(a) + Maj(a, b, c)` on the working words numbered `st`. -/
def t2E (P : Sha2FamilyParams) (st : Fin 8 → Nat) : WExp P.w :=
  .bin .add (bigSigmaE P.bigSigma0 (st 0)) (majE (st 0) (st 1) (st 2))

/-- The schedule word `W t = σ1(W (t-2)) + W (t-7) + σ0(W (t-15)) + W (t-16)`, the words
    `W j` numbered `ws.getD j 0`. -/
def schedE (P : Sha2FamilyParams) (ws : List Nat) (t : Nat) : WExp P.w :=
  .bin .add
    (.bin .add (.bin .add (smallSigmaE P.smallSigma1 (ws.getD (t - 2) 0))
      (.var (ws.getD (t - 7) 0))) (smallSigmaE P.smallSigma0 (ws.getD (t - 15) 0)))
    (.var (ws.getD (t - 16) 0))

/-- One round on the working words numbered `st`, with the round constant `kt` and the
    schedule word numbered `wt`: binds `T1`, `T2`, the new `e` and the new `a`, and returns
    the numbers of the new working words. -/
def roundLets (P : Sha2FamilyParams) (kt : BitVec P.w) (wt : Nat) (st : Fin 8 → Nat)
    (s : LetSt P.w) : (Fin 8 → Nat) × LetSt P.w :=
  let (t1, s) := s.push (t1E P st kt wt)
  let (t2, s) := s.push (t2E P st)
  let (e', s) := s.push (.bin .add (.var (st 3)) (.var t1))
  let (a', s) := s.push (.bin .add (.var t1) (.var t2))
  (![a', st 0, st 1, st 2, e', st 4, st 5, st 6], s)

/-- `r` rounds from the round `t`, the schedule word of a round `t ≥ 16` bound before the
    round; `ws` numbers the schedule words `W 0, …, W (t-1)`. -/
def roundsLets (P : Sha2FamilyParams) : Nat → Nat → (Fin 8 → Nat) → List Nat → LetSt P.w →
    (Fin 8 → Nat) × LetSt P.w
  | 0, _, st, _, s => (st, s)
  | r + 1, t, st, ws, s =>
      let (ws, s) :=
        if t < 16 then (ws, s)
        else
          let (i, s) := s.push (schedE P ws t)
          (ws ++ [i], s)
      let (st, s) := roundLets P (P.K.getD t 0) (ws.getD t 0) st s
      roundsLets P r (t + 1) st ws s

/-- The feed-forward: binds `H i + st i` for each listed `i`, the chaining word `H i` numbered
    `i`, and returns the pairs of `i` and the number of its sum. -/
def feedLets (P : Sha2FamilyParams) (st : Fin 8 → Nat) :
    List (Fin 8) → LetSt P.w → List (Nat × Nat) × LetSt P.w
  | [], s => ([], s)
  | i :: is, s =>
      let (o, s) := s.push (.bin .add (.var i.val) (.var (st i)))
      let (outs, s) := feedLets P st is s
      ((i.val, o) :: outs, s)

/-- **The symbolic SHA-2 compression** at `P`: the chaining words `H 0, …, H 7` are the words
    numbered `0, …, 7` and the message words `M 0, …, M 15` the words numbered `8, …, 23`; the
    result is the store list of the new chaining words and the let-bound expressions, from the
    word numbered `24`. -/
def sha2Lets (P : Sha2FamilyParams) : List (Nat × Nat) × LetSt P.w :=
  let (st, s) := roundsLets P P.rounds 0 (fun i => i.val) ((List.range 16).map (· + 8)) ⟨24, []⟩
  feedLets P st (List.finRange 8) s

/-- The values of the input words: `H i` numbered `i` and `M j` numbered `8 + j`. -/
def sha2Inputs {w : Nat} (H : Fin 8 → BitVec w) (M : Fin 16 → BitVec w) (i : Nat) : BitVec w :=
  if h : i < 8 then H ⟨i, h⟩ else if h' : i - 8 < 16 then M ⟨i - 8, h'⟩ else 0

/-! ## 4. The program -/

/-- The input context of the compression: the chaining words, then the message words, as
    stack arrays. -/
abbrev sha2InCtxt (w : Nat) : Ctxt jasminDialect := [.stackArr w 8, .stackArr w 16]

/-- **The SHA-2 compression function at `P` as a `jasminDialect` program**: the loads of the
    eight chaining words and the sixteen message words, the compiled symbolic compression
    `sha2Lets P`, and the stores of the eight new chaining words into a fresh array. -/
def sha2CompressBody (P : Sha2FamilyParams) :
    Com jasminDialect (sha2InCtxt P.w) (.stackArr P.w 8) :=
  let L := sha2Lets P
  genLoad (Var.here) 0 fun ρ0 v0 =>
  genLoads (List.range' 1 7) (ρ0 _ .here) 1 (fun _ => v0) fun ρ1 env1 =>
  genLoads (List.range 16) (ρ1 _ (ρ0 _ (.there .here))) 8 env1 fun _ env2 =>
  genLets L.2.rev.reverse 24 env2 fun env3 =>
  .var ⟨.stackZero P.w 8, rfl, .nil⟩ (genStores L.1 .here (fun i => (env3 i).there))

/-! ## 5. The six standards (FIPS 180-4) -/

/-- SHA-256: 32-bit words, 64 rounds (FIPS 180-4 §4.1.2, §4.2.2, §5.3.3). The round
    constants and the initial hash value are those of `Primitives.SHA256`. -/
def sha256P : Sha2FamilyParams where
  w := 32
  hw := Or.inl rfl
  rounds := 64
  bigSigma0 := ⟨2, 13, 22⟩
  bigSigma1 := ⟨6, 11, 25⟩
  smallSigma0 := ⟨7, 18, 3⟩
  smallSigma1 := ⟨17, 19, 10⟩
  K := Primitives.SHA256.kData.toList.map UInt32.toBitVec
  hK := by simp
  H0 := fun i => (Primitives.SHA256.h0Vec[i]).toBitVec
  hshr := by decide

/-- SHA-224: the compression of SHA-256 with the initial hash value of FIPS 180-4 §5.3.2. -/
def sha224P : Sha2FamilyParams :=
  { sha256P with
    H0 := ![0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939,
            0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4] }

/-- SHA-512: 64-bit words, 80 rounds (FIPS 180-4 §4.1.3, §4.2.3, §5.3.5). The round
    constants and the initial hash value are those of `Primitives.SHA512`. -/
def sha512P : Sha2FamilyParams where
  w := 64
  hw := Or.inr rfl
  rounds := 80
  bigSigma0 := ⟨28, 34, 39⟩
  bigSigma1 := ⟨14, 18, 41⟩
  smallSigma0 := ⟨1, 8, 7⟩
  smallSigma1 := ⟨19, 61, 6⟩
  K := Primitives.SHA512.kData.toList.map UInt64.toBitVec
  hK := by simp
  H0 := fun i => (Primitives.SHA512.h0Vec[i]).toBitVec
  hshr := by decide

/-- SHA-384: the compression of SHA-512 with the initial hash value of FIPS 180-4 §5.3.4. -/
def sha384P : Sha2FamilyParams :=
  { sha512P with
    H0 := ![0xcbbb9d5dc1059ed8, 0x629a292a367cd507, 0x9159015a3070dd17, 0x152fecd8f70e5939,
            0x67332667ffc00b31, 0x8eb44a8768581511, 0xdb0c2e0d64f98fa7, 0x47b5481dbefa4fa4] }

/-- SHA-512/224: the compression of SHA-512 with the initial hash value of FIPS 180-4
    §5.3.6.1. -/
def sha512t224P : Sha2FamilyParams :=
  { sha512P with
    H0 := ![0x8c3d37c819544da2, 0x73e1996689dcd4d6, 0x1dfab7ae32ff9c82, 0x679dd514582f9fcf,
            0x0f6d2b697bd44da8, 0x77e36f7304c48942, 0x3f9d85a86a1d36c8, 0x1112e6ad91d692a1] }

/-- SHA-512/256: the compression of SHA-512 with the initial hash value of FIPS 180-4
    §5.3.6.2. -/
def sha512t256P : Sha2FamilyParams :=
  { sha512P with
    H0 := ![0x22312194fc2bf72c,0x9f555fa3c84c64c2, 0x2393b86b6f53b151, 0x963877195940eabd,
            0x96283ee2a88effe3, 0xbe5e1e2553863992, 0x2b0199fc2c85b8aa, 0x0eb72ddc81c52ca2] }

/-! ## 6. The values of the symbolic compression -/

/-- `Σ` on a word evaluates to `bigS`. -/
theorem bigSigmaE_eval {w : Nat} (a : Sha2Amounts) (x : Nat) (ρ : Nat → BitVec w) :
    (bigSigmaE a x : WExp w).eval ρ = Sha2FamilyParams.bigS a (ρ x) := by
  simp [bigSigmaE, WExp.eval, JasminBinOp.apply, Sha2FamilyParams.bigS]

/-- `σ` on a word evaluates to `smallS` at a shift amount below the word width. -/
theorem smallSigmaE_eval {w : Nat} (a : Sha2Amounts) (ha : a.r3 < w) (x : Nat)
    (ρ : Nat → BitVec w) :
    (smallSigmaE a x : WExp w).eval ρ = Sha2FamilyParams.smallS a (ρ x) := by
  simp [smallSigmaE, WExp.eval, JasminBinOp.apply, Sha2FamilyParams.smallS, shiftMask_of_lt ha]

theorem t1E_eval (P : Sha2FamilyParams) (st : Fin 8 → Nat) (kt : BitVec P.w) (wt : Nat)
    (ρ : Nat → BitVec P.w) :
    (t1E P st kt wt).eval ρ = ρ (st 7) + Sha2FamilyParams.bigS P.bigSigma1 (ρ (st 4)) +
      Sha2FamilyParams.ch (ρ (st 4)) (ρ (st 5)) (ρ (st 6)) + kt + ρ wt := by
  simp [t1E, WExp.eval, JasminBinOp.apply, bigSigmaE_eval, chE, Sha2FamilyParams.ch]

theorem t2E_eval (P : Sha2FamilyParams) (st : Fin 8 → Nat) (ρ : Nat → BitVec P.w) :
    (t2E P st).eval ρ = Sha2FamilyParams.bigS P.bigSigma0 (ρ (st 0)) +
      Sha2FamilyParams.maj (ρ (st 0)) (ρ (st 1)) (ρ (st 2)) := by
  simp [t2E, WExp.eval, JasminBinOp.apply, bigSigmaE_eval, majE, Sha2FamilyParams.maj]

/-- The schedule expression evaluates to the schedule recursion. -/
theorem schedE_eval (P : Sha2FamilyParams) (ws : List Nat) (t : Nat) (ρ : Nat → BitVec P.w) :
    (schedE P ws t).eval ρ = Sha2FamilyParams.smallS P.smallSigma1 (ρ (ws.getD (t - 2) 0)) +
      ρ (ws.getD (t - 7) 0) + Sha2FamilyParams.smallS P.smallSigma0 (ρ (ws.getD (t - 15) 0)) +
      ρ (ws.getD (t - 16) 0) := by
  simp [schedE, WExp.eval, JasminBinOp.apply, smallSigmaE_eval _ P.hshr.1,
    smallSigmaE_eval _ P.hshr.2]

/-- One symbolic round evaluates to `sha2RoundRef`. -/
theorem roundLets_spec (P : Sha2FamilyParams) (ρ : Nat → BitVec P.w) (kt : BitVec P.w) (wt : Nat)
    (st : Fin 8 → Nat) (s : LetSt P.w) (hs : s.Good 24) (hst : ∀ i, st i < s.next) :
    (roundLets P kt wt st s).2.Good 24 ∧ s.Ext (roundLets P kt wt st s).2 ∧
      (∀ i, (roundLets P kt wt st s).1 i < (roundLets P kt wt st s).2.next) ∧
      (fun i => (roundLets P kt wt st s).2.val 24 ρ ((roundLets P kt wt st s).1 i)) =
        Sha2FamilyParams.sha2RoundRef P (fun i => s.val 24 ρ (st i)) kt (s.val 24 ρ wt) := by
  have hne : ∀ i, st i ≠ s.next ∧ st i ≠ s.next + 1 ∧ st i ≠ s.next + 1 + 1 ∧
      st i ≠ s.next + 1 + 1 + 1 := fun i => by
    have := hst i; omega
  have hval := LetSt.val_extend ρ hs
  have hg := hs
  unfold LetSt.Good at hg
  simp only [roundLets, LetSt.push]
  refine ⟨?_, ⟨[_, _, _, _], rfl⟩, ?_, ?_⟩
  · unfold LetSt.Good
    simp only [List.length_cons, hg]
    omega
  · intro i
    have h0 := hst 0; have h1 := hst 1; have h2 := hst 2; have h4 := hst 4
    have h5 := hst 5; have h6 := hst 6
    fin_cases i <;> simp <;> omega
  · rw [show ∀ m (a b c d : WExp P.w), (⟨m, a :: b :: c :: d :: s.rev⟩ : LetSt P.w) =
      ⟨m, [a, b, c, d] ++ s.rev⟩ from fun _ _ _ _ _ => rfl, hval]
    funext i
    fin_cases i <;>
      simp [evalLets, Sha2FamilyParams.sha2RoundRef, t1E_eval, t2E_eval, hne, WExp.eval,
        JasminBinOp.apply, show s.next ≠ s.next + 1 + 1 by omega]

/-- The symbolic rounds evaluate to the rounds of `sha2CompressRef`. -/
theorem roundsLets_spec (P : Sha2FamilyParams) (ρ : Nat → BitVec P.w) (H : Fin 8 → BitVec P.w)
    (M : Fin 16 → BitVec P.w) :
    ∀ (r t : Nat) (st : Fin 8 → Nat) (ws : List Nat) (s : LetSt P.w), s.Good 24 →
      (∀ i, st i < s.next) → ws.length = max 16 t →
      (∀ j (hj : j < ws.length), ws[j] < s.next ∧ s.val 24 ρ ws[j] = P.schedule M j) →
      (fun i => s.val 24 ρ (st i)) = (List.range t).foldl
        (fun s t => Sha2FamilyParams.sha2RoundRef P s (P.K.getD t 0) (P.schedule M t)) H →
      (roundsLets P r t st ws s).2.Good 24 ∧ s.Ext (roundsLets P r t st ws s).2 ∧
        (∀ i, (roundsLets P r t st ws s).1 i < (roundsLets P r t st ws s).2.next) ∧
        (fun i => (roundsLets P r t st ws s).2.val 24 ρ ((roundsLets P r t st ws s).1 i)) =
          (List.range (t + r)).foldl
            (fun s t => Sha2FamilyParams.sha2RoundRef P s (P.K.getD t 0) (P.schedule M t)) H := by
  intro r
  induction r with
  | zero =>
      intro t st ws s hs hst _ _ hfold
      exact ⟨hs, LetSt.Ext.refl s, hst, by simpa [roundsLets] using hfold⟩
  | succ r ih =>
      intro t st ws s hs hst hlen hws hfold
      have key : ∀ (ws₁ : List Nat) (s₁ : LetSt P.w), s₁.Good 24 → s.Ext s₁ →
          (∀ i, st i < s₁.next) → ws₁.length = max 16 (t + 1) →
          (∀ j (hj : j < ws₁.length), ws₁[j] < s₁.next ∧
            s₁.val 24 ρ ws₁[j] = P.schedule M j) →
          (fun i => s₁.val 24 ρ (st i)) = (List.range t).foldl
            (fun s t => Sha2FamilyParams.sha2RoundRef P s (P.K.getD t 0) (P.schedule M t)) H →
          let q := roundLets P (P.K.getD t 0) (ws₁.getD t 0) st s₁
          (roundsLets P r (t + 1) q.1 ws₁ q.2).2.Good 24 ∧
            s.Ext (roundsLets P r (t + 1) q.1 ws₁ q.2).2 ∧
            (∀ i, (roundsLets P r (t + 1) q.1 ws₁ q.2).1 i <
              (roundsLets P r (t + 1) q.1 ws₁ q.2).2.next) ∧
            (fun i => (roundsLets P r (t + 1) q.1 ws₁ q.2).2.val 24 ρ
              ((roundsLets P r (t + 1) q.1 ws₁ q.2).1 i)) =
              (List.range (t + (r + 1))).foldl
                (fun s t => Sha2FamilyParams.sha2RoundRef P s (P.K.getD t 0) (P.schedule M t)) H := by
        intro ws₁ s₁ hs₁ he₁ hst₁ hlen₁ hws₁ hfold₁ q
        have htl : t < ws₁.length := by omega
        have hwt : ws₁.getD t 0 = ws₁[t] := by simp [List.getD_eq_getElem?_getD, htl]
        obtain ⟨g2, e2, b2, v2⟩ := roundLets_spec P ρ (P.K.getD t 0) (ws₁.getD t 0) st s₁ hs₁
          hst₁
        have hle : s₁.next ≤ q.2.next := e2.next_le hs₁ g2
        obtain ⟨g, e, b, v⟩ := ih (t + 1) q.1 ws₁ q.2 g2 b2 hlen₁
          (fun j hj => ⟨by have := (hws₁ j hj).1; omega,
            (e2.val_eq hs₁ ρ _ (hws₁ j hj).1).trans (hws₁ j hj).2⟩)
          (by
            rw [v2, hfold₁, hwt, (hws₁ t htl).2, List.range_succ, List.foldl_append]
            rfl)
        refine ⟨g, he₁.trans (e2.trans e), b, ?_⟩
        rw [v, show t + 1 + r = t + (r + 1) by omega]
      by_cases ht : t < 16
      · simp only [roundsLets, ht, ite_true]
        exact key ws s hs (LetSt.Ext.refl s) hst (by omega) hws hfold
      · simp only [roundsLets, ht, ite_false]
        have hlt : ws.length = t := by omega
        have hg := LetSt.push_good (schedE P ws t) hs
        have hv := LetSt.push_val (schedE P ws t) hs ρ
        have he := LetSt.Ext.push (schedE P ws t) s
        have hget : ∀ j < t, s.val 24 ρ (ws.getD j 0) = P.schedule M j := fun j hj => by
          rw [List.getD_eq_getElem _ _ (by omega)]
          exact (hws j (by omega)).2
        refine key (ws ++ [s.next]) (s.push (schedE P ws t)).2 hg he
          (fun i => by have := hst i; simp only [LetSt.push]; omega)
          (by simp only [List.length_append, List.length_singleton]; omega) ?_ ?_
        · intro j hj
          simp only [List.length_append, List.length_singleton] at hj
          by_cases hjt : j < ws.length
          · rw [List.getElem_append_left hjt]
            refine ⟨by have := (hws j hjt).1; simp only [LetSt.push]; omega, ?_⟩
            rw [he.val_eq hs ρ _ (hws j hjt).1]
            exact (hws j hjt).2
          · have hj' : j = t := by omega
            subst hj'
            rw [List.getElem_append_right (by omega)]
            simp only [hlt, Nat.sub_self, List.getElem_singleton]
            refine ⟨by simp only [LetSt.push]; omega, ?_⟩
            rw [hv]
            simp only [ite_true]
            rw [schedE_eval]
            conv_rhs => rw [Sha2FamilyParams.schedule, dite_eq_right ht]
            rw [hget _ (by omega), hget _ (by omega), hget _ (by omega), hget _ (by omega)]
        · funext i
          rw [he.val_eq hs ρ _ (hst i)]
          exact congrFun hfold i

/-- The feed-forward binds, at position `k`, the sum of the chaining word numbered `is[k]`
    and the working word `st is[k]`. -/
theorem feedLets_spec (P : Sha2FamilyParams) (ρ : Nat → BitVec P.w) (st : Fin 8 → Nat) :
    ∀ (is : List (Fin 8)) (s : LetSt P.w), s.Good 24 → (∀ i, st i < s.next) →
      s.Ext (feedLets P st is s).2 ∧ (feedLets P st is s).1.length = is.length ∧
      ∀ k (hk : k < is.length), (feedLets P st is s).1.getD k (0, 0) = (is[k].val, s.next + k) ∧
        (feedLets P st is s).2.val 24 ρ (s.next + k) =
          s.val 24 ρ is[k].val + s.val 24 ρ (st is[k]) := by
  intro is
  induction is with
  | nil => intro s _ _; exact ⟨LetSt.Ext.refl s, rfl, fun k hk => absurd hk (by simp)⟩
  | cons i is ih =>
      intro s hs hst
      have h24 : 24 ≤ s.next := by unfold LetSt.Good at hs; omega
      have hg := LetSt.push_good (.bin .add (.var i.val) (.var (st i))) hs
      have hv := LetSt.push_val (.bin .add (.var i.val) (.var (st i))) hs ρ
      have he := LetSt.Ext.push (.bin .add (.var i.val) (.var (st i))) s
      have hnext : (s.push (.bin .add (.var i.val) (.var (st i)))).2.next = s.next + 1 := rfl
      obtain ⟨e1, l1, f1⟩ := ih _ hg (fun j => by have := hst j; omega)
      simp only [feedLets]
      refine ⟨he.trans e1, by simp [l1], fun k hk => ?_⟩
      cases k with
      | zero =>
          refine ⟨rfl, ?_⟩
          rw [e1.val_eq hg ρ _ (by omega), hv]
          simp [WExp.eval, JasminBinOp.apply]
      | succ k =>
          have hk' : k < is.length := by simp at hk; omega
          obtain ⟨f1a, f1b⟩ := f1 k hk'
          refine ⟨by simpa [hnext, Nat.add_assoc, Nat.add_comm 1 k] using f1a, ?_⟩
          rw [show s.next + (k + 1) = (s.push (.bin .add (.var i.val) (.var (st i)))).2.next + k
            by omega, f1b, hv]
          have h1 : (is[k].val : Nat) ≠ s.next := by have := is[k].isLt; omega
          have h2 : st is[k] ≠ s.next := Nat.ne_of_lt (hst _)
          simp [h1, h2]

/-- The symbolic compression from input values agreeing with the chaining and message words
    below the word numbered `24`: the stores write the indices `0, …, 7`, and the word stored
    at the index `i` is `sha2CompressRef P H M i`. -/
theorem sha2Lets_spec (P : Sha2FamilyParams) (H : Fin 8 → BitVec P.w) (M : Fin 16 → BitVec P.w)
    (ρ : Nat → BitVec P.w) (hρ : ∀ i < 24, ρ i = sha2Inputs H M i) :
    (sha2Lets P).1.length = 8 ∧ (∀ k < 8, ((sha2Lets P).1.getD k (0, 0)).1 = k) ∧
      (fun i : Fin 8 => evalLets ρ 24 (sha2Lets P).2.rev.reverse
        ((sha2Lets P).1.getD i.val (0, 0)).2) = P.sha2CompressRef H M := by
  have hs0 : (⟨24, []⟩ : LetSt P.w).Good 24 := rfl
  have hv0 : (⟨24, []⟩ : LetSt P.w).val 24 ρ = ρ := rfl
  obtain ⟨g, e, b, v⟩ := roundsLets_spec P ρ H M P.rounds 0 (fun i => i.val)
    ((List.range 16).map (· + 8)) ⟨24, []⟩ hs0 (fun i => by have := i.isLt; simp; omega)
    (by simp)
    (fun j hj => by
      simp only [List.length_map, List.length_range] at hj
      simp only [List.getElem_map, List.getElem_range, hv0]
      refine ⟨by omega, ?_⟩
      rw [hρ _ (by omega), Sha2FamilyParams.schedule]
      simp [sha2Inputs, hj, show ¬ j + 8 < 8 by omega])
    (by funext i; simp [hv0, hρ _ (by have := i.isLt; omega : i.val < 24), sha2Inputs])
  obtain ⟨e', l', f'⟩ := feedLets_spec P ρ _ (List.finRange 8) _ g b
  simp only [sha2Lets]
  refine ⟨by simpa using l', fun k hk => ?_, ?_⟩
  · rw [(f' k (by simpa using hk)).1]
    simp
  · funext i
    obtain ⟨f1, f2⟩ := f' i.val (by simp)
    rw [f1]
    show LetSt.val 24 ρ _ _ = _
    rw [f2, e.val_eq hs0 ρ _ (by simp; omega), hv0, hρ _ (by omega), congrFun v]
    simp [Sha2FamilyParams.sha2CompressRef, sha2Inputs]

/-! ## 7. Statements -/

/-- The symbolic compression evaluates to the reference compression: the word stored at the
    index `i` is `sha2CompressRef P H M i`. -/
theorem sha2Lets_eval (P : Sha2FamilyParams) (H : Fin 8 → BitVec P.w) (M : Fin 16 → BitVec P.w) :
    (fun i : Fin 8 => evalLets (sha2Inputs H M) 24 (sha2Lets P).2.rev.reverse
      ((sha2Lets P).1.getD i.val (0, 0)).2) = P.sha2CompressRef H M :=
  (sha2Lets_spec P H M _ fun _ _ => rfl).2.2

/-- **The value of the SHA-2 template**: at the chaining words `H` and the message words `M`,
    the program returns the reference compression `sha2CompressRef P H M`. -/
theorem sha2CompressBody_value (P : Sha2FamilyParams) (H : Fin 8 → BitVec P.w)
    (M : Fin 16 → BitVec P.w) :
    (sha2CompressBody P).denote (.cons H (.cons M .nil)) = P.sha2CompressRef H M := by
  have hH : ∀ i (h : i < 8), stackGet H (BitVec.ofNat 64 i).toNat = H ⟨i, h⟩ := fun i h => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact stackGet_id H ⟨i, h⟩
  have hM : ∀ i (h : i < 16), stackGet M (BitVec.ofNat 64 i).toNat = M ⟨i, h⟩ := fun i h => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact stackGet_id M ⟨i, h⟩
  unfold sha2CompressBody
  refine genLoad_denote _ 0 _ _ H rfl _ fun ρ0 V0 v0 hρ0 hv0 => ?_
  refine genLoads_denote _ _ 1 _ _ V0 H (hρ0 _ _) (fun _ => stackGet H (BitVec.ofNat 64 0).toNat)
    (fun _ => hv0) _ fun ρ1 V1 env1 hρ1 henv1 => ?_
  refine genLoads_denote _ _ 8 env1 _ V1 M ((hρ1 _ _).trans (hρ0 _ _)) _ henv1 _
    fun _ V2 env2 _ henv2 => ?_
  refine genLets_denote _ 24 env2 _ V2 _ henv2 _ fun V3 env3 henv3 => ?_
  refine (genStores_denote (sha2Lets P).1 .here (fun i => (env3 i).there)
    (Ctxt.Valuation.extend V3 (JasminTy.default (.stackArr P.w 8))) _ rfl _
    (fun i => henv3 i)).trans ?_
  have hagree : ∀ i < 24, loadVals M (loadVals H (fun _ => stackGet H (BitVec.ofNat 64 0).toNat)
      1 (List.range' 1 7)) 8 (List.range 16) i = sha2Inputs H M i := by
    intro i hi
    rw [loadVals_apply, loadVals_apply]
    by_cases h8 : i < 8
    · rw [ite_eq_right (by omega)]
      simp only [sha2Inputs, h8, dite_eq_left]
      by_cases h0 : i = 0
      · subst h0
        rw [ite_eq_right (by omega)]
        exact hH 0 (by omega)
      · rw [ite_eq_left (by simp; omega)]
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_range']
        rw [show 1 + 1 * (i - 1) = i by omega]
        exact hH i h8
    · rw [ite_eq_left (by simp; omega)]
      simp only [sha2Inputs, h8, dite_eq_right, not_false_eq_true, show i - 8 < 16 by omega, dite_eq_left]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_range]
      exact hM _ _
  obtain ⟨hl, hk, hv⟩ := sha2Lets_spec P H M _ hagree
  rw [foldl_stores8 _ hl hk]
  exact hv

/-- **The events of the SHA-2 template are fixed**: at leakage parameters with no
    variable-time operation, the program emits the same events at every two valuations. -/
theorem sha2CompressBody_events (P : Sha2FamilyParams) (Pj : JLeakParams)
    (hV : ∀ op, Pj.opVT op = none) : LeakFixed (jLeakModel Pj) (sha2CompressBody P) := by
  unfold sha2CompressBody
  exact genLoad_fixed Pj hV _ _ _ fun _ _ => genLoads_fixed Pj hV _ _ _ _ _ fun _ _ =>
    genLoads_fixed Pj hV _ _ _ _ _ fun _ _ => genLets_fixed Pj hV _ _ _ _ fun _ =>
      leakFixed_var_quiet Pj _ _ (by simp [Dialects.JasminComLLeak.jKind, hV])
        (genStores_fixed Pj hV _ _ _)

/-- The sixteen big-endian message words of a SHA-256 block, the first sixteen words of its
    message schedule. -/
def sha256BlockWords (block : Fin 64 → UInt8) : Fin 16 → BitVec 32 :=
  fun j => (Primitives.SHA256.messageSchedule block ⟨j.val, by omega⟩).toBitVec

/-- The sixteen big-endian message words of a SHA-512 block, the first sixteen words of its
    message schedule. -/
def sha512BlockWords (block : Fin 128 → UInt8) : Fin 16 → BitVec 64 :=
  fun j => (Primitives.SHA512.messageSchedule block ⟨j.val, by omega⟩).toBitVec

/-- The schedule word `W t` for `t < 16` is the message word `M t`. -/
theorem Sha2FamilyParams.schedule_lt (P : Sha2FamilyParams) (M : Fin 16 → BitVec P.w) (t : Nat)
    (h : t < 16) : P.schedule M t = M ⟨t, h⟩ := by
  rw [Sha2FamilyParams.schedule, dite_eq_left h]

/-- The schedule word `W t` for `t ≥ 16` is the schedule recursion. -/
theorem Sha2FamilyParams.schedule_ge (P : Sha2FamilyParams) (M : Fin 16 → BitVec P.w) (t : Nat)
    (h : 16 ≤ t) : P.schedule M t =
      Sha2FamilyParams.smallS P.smallSigma1 (P.schedule M (t - 2)) + P.schedule M (t - 7) +
        Sha2FamilyParams.smallS P.smallSigma0 (P.schedule M (t - 15)) + P.schedule M (t - 16) := by
  rw [Sha2FamilyParams.schedule, dite_eq_right (by omega)]

/-! ### SHA-256 -/

theorem sha256_bigSigma0 (x : UInt32) :
    (Primitives.SHA256.bigSigma0 x).toBitVec = Sha2FamilyParams.bigS ⟨2, 13, 22⟩ x.toBitVec := by
  simp [Primitives.SHA256.bigSigma0, Primitives.SHA256.rotr, Sha2FamilyParams.bigS,
    BitVec.rotateRight_def]

theorem sha256_bigSigma1 (x : UInt32) :
    (Primitives.SHA256.bigSigma1 x).toBitVec = Sha2FamilyParams.bigS ⟨6, 11, 25⟩ x.toBitVec := by
  simp [Primitives.SHA256.bigSigma1, Primitives.SHA256.rotr, Sha2FamilyParams.bigS,
    BitVec.rotateRight_def]

theorem sha256_smallSigma0 (x : UInt32) :
    (Primitives.SHA256.smallSigma0 x).toBitVec = Sha2FamilyParams.smallS ⟨7, 18, 3⟩ x.toBitVec := by
  simp [Primitives.SHA256.smallSigma0, Primitives.SHA256.rotr, Sha2FamilyParams.smallS,
    BitVec.rotateRight_def]

theorem sha256_smallSigma1 (x : UInt32) :
    (Primitives.SHA256.smallSigma1 x).toBitVec = Sha2FamilyParams.smallS ⟨17, 19, 10⟩ x.toBitVec := by
  simp [Primitives.SHA256.smallSigma1, Primitives.SHA256.rotr, Sha2FamilyParams.smallS,
    BitVec.rotateRight_def]

/-- A round of `Primitives.SHA256` is `sha2RoundRef` at `sha256P` on the words. -/
theorem sha256_round (v : Vector UInt32 8) (wt kt : UInt32) :
    (fun i : Fin 8 => (Primitives.SHA256.compressRoundVec v wt kt)[i].toBitVec) =
      Sha2FamilyParams.sha2RoundRef sha256P (fun i => v[i].toBitVec) kt.toBitVec wt.toBitVec := by
  funext i
  fin_cases i <;>
    simp [Primitives.SHA256.compressRoundVec, Sha2FamilyParams.sha2RoundRef, sha256_bigSigma0,
      sha256_bigSigma1, Primitives.SHA256.ch, Primitives.SHA256.maj, Sha2FamilyParams.ch,
      Sha2FamilyParams.maj, show sha256P.bigSigma0 = ⟨2, 13, 22⟩ from rfl,
      show sha256P.bigSigma1 = ⟨6, 11, 25⟩ from rfl] <;> rfl

/-- The round constants of `Primitives.SHA256` are those of `sha256P`. -/
theorem sha256_kConst (t : Nat) :
    (Primitives.SHA256.kConst t).toBitVec = sha256P.K.getD t 0 := by
  simp [Primitives.SHA256.kConst, sha256P, List.getD_eq_getElem?_getD,
    Array.getD_eq_getD_getElem?]

/-- The schedule steps of `Primitives.SHA256.messageSchedule` leave the first sixteen words
    and compute the schedule recursion of `sha256P` on them. -/
theorem sha256_schedule_foldl (w0 : Vector UInt32 64)
    (f : Vector UInt32 64 → Fin 48 → Vector UInt32 64)
    (hf : ∀ w (j : Fin 48), f w j = w.set (j.val + 16)
      (Primitives.SHA256.smallSigma1 w[j.val + 14] + w[j.val + 9] +
        Primitives.SHA256.smallSigma0 w[j.val + 1] + w[j.val]) (by omega)) :
    (∀ t (h : t < 16), (Fin.foldl 48 f w0)[t] = w0[t]) ∧
      ∀ t (h : t < 64), ((Fin.foldl 48 f w0)[t]).toBitVec =
        sha256P.schedule (fun j => (w0[j.val]'(by omega)).toBitVec) t := by
  have key := fin_foldl_inv (fun k (v : Vector UInt32 64) => (∀ t (h : t < 16), v[t] = w0[t]) ∧
      ∀ t (h : t < 16 + k) (h' : t < 64), (v[t]).toBitVec =
        sha256P.schedule (fun j => (w0[j.val]'(by omega)).toBitVec) t) f w0
    ⟨fun _ _ => rfl, fun t h _ => (Sha2FamilyParams.schedule_lt sha256P
      (fun j => (w0[j.val]'(by omega)).toBitVec) t (by omega)).symm⟩ ?_
  · exact ⟨key.1, fun t h => key.2 t (by omega) h⟩
  · rintro j v ⟨h1, h2⟩
    rw [hf]
    refine ⟨fun t ht => ?_, fun t ht ht' => ?_⟩
    · rw [Vector.getElem_set_ne _ _ (by omega)]
      exact h1 t ht
    · by_cases hj : t = j.val + 16
      · subst hj
        rw [Vector.getElem_set_self]
        refine Eq.trans ?_ (Sha2FamilyParams.schedule_ge sha256P _ (j.val + 16) (by omega)).symm
        simp only [UInt32.toBitVec_add, sha256_smallSigma0, sha256_smallSigma1,
          show j.val + 16 - 2 = j.val + 14 by omega, show j.val + 16 - 7 = j.val + 9 by omega,
          show j.val + 16 - 15 = j.val + 1 by omega, show j.val + 16 - 16 = j.val by omega]
        rw [h2 _ (by omega) (by omega), h2 _ (by omega) (by omega), h2 _ (by omega) (by omega),
          h2 _ (by omega) (by omega)]
        rfl
      · rw [Vector.getElem_set_ne _ _ (by omega)]
        exact h2 t (by omega) ht'

/-- The message schedule of `Primitives.SHA256` is the schedule of `sha256P` on the first
    sixteen words. -/
theorem sha256_schedule (block : Fin 64 → UInt8) (t : Fin 64) :
    (Primitives.SHA256.messageSchedule block t).toBitVec =
      sha256P.schedule (sha256BlockWords block) t.val := by
  unfold sha256BlockWords Primitives.SHA256.messageSchedule
  obtain ⟨h1, h2⟩ := sha256_schedule_foldl _ _ (fun _ _ => rfl)
  refine (h2 t.val t.isLt).trans ?_
  exact congrArg (fun M => sha256P.schedule M t.val)
    (funext fun j => congrArg UInt32.toBitVec (h1 j.val j.isLt).symm)

/-- **The template at SHA-256 is the in-tree SHA-256 compression** `Primitives.SHA256.compress`
    on the words of the state and of the block. -/
theorem sha2CompressBody_sha256 (H : Fin 8 → UInt32) (block : Fin 64 → UInt8) :
    (sha2CompressBody sha256P).denote
        (.cons (fun i => (H i).toBitVec) (.cons (sha256BlockWords block) .nil)) =
      fun i => (Primitives.SHA256.compress H block i).toBitVec := by
  refine (sha2CompressBody_value sha256P (fun i => (H i).toBitVec)
    (sha256BlockWords block)).trans ?_
  have key := fin_foldl_inv (fun k (v : Vector UInt32 8) => (fun i : Fin 8 => v[i].toBitVec) =
      (List.range k).foldl (fun s t => Sha2FamilyParams.sha2RoundRef sha256P s (sha256P.K.getD t 0)
        (sha256P.schedule (sha256BlockWords block) t)) (fun i => (H i).toBitVec))
    (fun s (t : Fin 64) => Primitives.SHA256.compressRoundVec s
      (Primitives.SHA256.messageSchedule block t) (Primitives.SHA256.kConst t.val))
    (Vector.ofFn H) (funext fun i => show (Vector.ofFn H)[i].toBitVec = (H i).toBitVec by simp)
    ?_
  · funext i
    unfold Sha2FamilyParams.sha2CompressRef Primitives.SHA256.compress
    rw [UInt32.toBitVec_add]
    exact congrArg _ (congrFun key i).symm
  · intro j v hv
    rw [List.range_succ]
    refine Eq.trans ?_ (List.foldl_append ..).symm
    refine Eq.trans ?_ (congrArg (fun s => List.foldl _ s [j.val]) hv)
    refine (sha256_round _ _ _).trans ?_
    exact congrArg₂ (Sha2FamilyParams.sha2RoundRef sha256P _) (sha256_kConst j.val) (sha256_schedule block j)

/-! ### SHA-512 -/

theorem sha512_bigSigma0 (x : UInt64) :
    (Primitives.SHA512.bigSigma0 x).toBitVec = Sha2FamilyParams.bigS ⟨28, 34, 39⟩ x.toBitVec := by
  simp [Primitives.SHA512.bigSigma0, Primitives.SHA512.rotr, Sha2FamilyParams.bigS,
    BitVec.rotateRight_def]

theorem sha512_bigSigma1 (x : UInt64) :
    (Primitives.SHA512.bigSigma1 x).toBitVec = Sha2FamilyParams.bigS ⟨14, 18, 41⟩ x.toBitVec := by
  simp [Primitives.SHA512.bigSigma1, Primitives.SHA512.rotr, Sha2FamilyParams.bigS,
    BitVec.rotateRight_def]

theorem sha512_smallSigma0 (x : UInt64) :
    (Primitives.SHA512.smallSigma0 x).toBitVec = Sha2FamilyParams.smallS ⟨1, 8, 7⟩ x.toBitVec := by
  simp [Primitives.SHA512.smallSigma0, Primitives.SHA512.rotr, Sha2FamilyParams.smallS,
    BitVec.rotateRight_def]

theorem sha512_smallSigma1 (x : UInt64) :
    (Primitives.SHA512.smallSigma1 x).toBitVec = Sha2FamilyParams.smallS ⟨19, 61, 6⟩ x.toBitVec := by
  simp [Primitives.SHA512.smallSigma1, Primitives.SHA512.rotr, Sha2FamilyParams.smallS,
    BitVec.rotateRight_def]

/-- A round of `Primitives.SHA512` is `sha2RoundRef` at `sha512P` on the words. -/
theorem sha512_round (v : Vector UInt64 8) (wt kt : UInt64) :
    (fun i : Fin 8 => (Primitives.SHA512.compressRoundVec v wt kt)[i].toBitVec) =
      Sha2FamilyParams.sha2RoundRef sha512P (fun i => v[i].toBitVec) kt.toBitVec wt.toBitVec := by
  funext i
  fin_cases i <;>
    simp [Primitives.SHA512.compressRoundVec, Sha2FamilyParams.sha2RoundRef, sha512_bigSigma0,
      sha512_bigSigma1, Primitives.SHA512.ch, Primitives.SHA512.maj, Sha2FamilyParams.ch,
      Sha2FamilyParams.maj, show sha512P.bigSigma0 = ⟨28, 34, 39⟩ from rfl,
      show sha512P.bigSigma1 = ⟨14, 18, 41⟩ from rfl] <;> rfl

/-- The round constants of `Primitives.SHA512` are those of `sha512P`. -/
theorem sha512_kConst (t : Nat) :
    (Primitives.SHA512.kConst t).toBitVec = sha512P.K.getD t 0 := by
  simp [Primitives.SHA512.kConst, sha512P, List.getD_eq_getElem?_getD,
    Array.getD_eq_getD_getElem?]

/-- The schedule steps of `Primitives.SHA512.messageSchedule` leave the first sixteen words
    and compute the schedule recursion of `sha512P` on them. -/
theorem sha512_schedule_foldl (w0 : Vector UInt64 80)
    (f : Vector UInt64 80 → Fin 64 → Vector UInt64 80)
    (hf : ∀ w (j : Fin 64), f w j = w.set (j.val + 16)
      (Primitives.SHA512.smallSigma1 w[j.val + 14] + w[j.val + 9] +
        Primitives.SHA512.smallSigma0 w[j.val + 1] + w[j.val]) (by omega)) :
    (∀ t (h : t < 16), (Fin.foldl 64 f w0)[t] = w0[t]) ∧
      ∀ t (h : t < 80), ((Fin.foldl 64 f w0)[t]).toBitVec =
        sha512P.schedule (fun j => (w0[j.val]'(by omega)).toBitVec) t := by
  have key := fin_foldl_inv (fun k (v : Vector UInt64 80) => (∀ t (h : t < 16), v[t] = w0[t]) ∧
      ∀ t (h : t < 16 + k) (h' : t < 80), (v[t]).toBitVec =
        sha512P.schedule (fun j => (w0[j.val]'(by omega)).toBitVec) t) f w0
    ⟨fun _ _ => rfl, fun t h _ => (Sha2FamilyParams.schedule_lt sha512P
      (fun j => (w0[j.val]'(by omega)).toBitVec) t (by omega)).symm⟩ ?_
  · exact ⟨key.1, fun t h => key.2 t (by omega) h⟩
  · rintro j v ⟨h1, h2⟩
    rw [hf]
    refine ⟨fun t ht => ?_, fun t ht ht' => ?_⟩
    · rw [Vector.getElem_set_ne _ _ (by omega)]
      exact h1 t ht
    · by_cases hj : t = j.val + 16
      · subst hj
        rw [Vector.getElem_set_self]
        refine Eq.trans ?_ (Sha2FamilyParams.schedule_ge sha512P _ (j.val + 16) (by omega)).symm
        simp only [UInt64.toBitVec_add, sha512_smallSigma0, sha512_smallSigma1,
          show j.val + 16 - 2 = j.val + 14 by omega, show j.val + 16 - 7 = j.val + 9 by omega,
          show j.val + 16 - 15 = j.val + 1 by omega, show j.val + 16 - 16 = j.val by omega]
        rw [h2 _ (by omega) (by omega), h2 _ (by omega) (by omega), h2 _ (by omega) (by omega),
          h2 _ (by omega) (by omega)]
        rfl
      · rw [Vector.getElem_set_ne _ _ (by omega)]
        exact h2 t (by omega) ht'

/-- The message schedule of `Primitives.SHA512` is the schedule of `sha512P` on the first
    sixteen words. -/
theorem sha512_schedule (block : Fin 128 → UInt8) (t : Fin 80) :
    (Primitives.SHA512.messageSchedule block t).toBitVec =
      sha512P.schedule (sha512BlockWords block) t.val := by
  unfold sha512BlockWords Primitives.SHA512.messageSchedule
  obtain ⟨h1, h2⟩ := sha512_schedule_foldl _ _ (fun _ _ => rfl)
  refine (h2 t.val t.isLt).trans ?_
  exact congrArg (fun M => sha512P.schedule M t.val)
    (funext fun j => congrArg UInt64.toBitVec (h1 j.val j.isLt).symm)

/-- The template at SHA-512 is the in-tree SHA-512 compression `Primitives.SHA512.compress`
    on the words of the state and of the block. -/
theorem sha2CompressBody_sha512 (H : Fin 8 → UInt64) (block : Fin 128 → UInt8) :
    (sha2CompressBody sha512P).denote
        (.cons (fun i => (H i).toBitVec) (.cons (sha512BlockWords block) .nil)) =
      fun i => (Primitives.SHA512.compress H block i).toBitVec := by
  refine (sha2CompressBody_value sha512P (fun i => (H i).toBitVec)
    (sha512BlockWords block)).trans ?_
  have key := fin_foldl_inv (fun k (v : Vector UInt64 8) => (fun i : Fin 8 => v[i].toBitVec) =
      (List.range k).foldl (fun s t => Sha2FamilyParams.sha2RoundRef sha512P s (sha512P.K.getD t 0)
        (sha512P.schedule (sha512BlockWords block) t)) (fun i => (H i).toBitVec))
    (fun s (t : Fin 80) => Primitives.SHA512.compressRoundVec s
      (Primitives.SHA512.messageSchedule block t) (Primitives.SHA512.kConst t.val))
    (Vector.ofFn H) (funext fun i => show (Vector.ofFn H)[i].toBitVec = (H i).toBitVec by simp)
    ?_
  · funext i
    unfold Sha2FamilyParams.sha2CompressRef Primitives.SHA512.compress
    rw [UInt64.toBitVec_add]
    exact congrArg _ (congrFun key i).symm
  · intro j v hv
    rw [List.range_succ]
    refine Eq.trans ?_ (List.foldl_append ..).symm
    refine Eq.trans ?_ (congrArg (fun s => List.foldl _ s [j.val]) hv)
    refine (sha512_round _ _ _).trans ?_
    exact congrArg₂ (Sha2FamilyParams.sha2RoundRef sha512P _) (sha512_kConst j.val) (sha512_schedule block j)

/-! ## 8. One input array and a separate output array -/

/-- The input context of the compression with one input array: the chaining words and the
    message words in one array of `24` words, and the output array of `8` words. -/
abbrev sha2InCtxtP (w : Nat) : Ctxt jasminDialect := [.stackArr w 24, .stackArr w 8]

/-- The input array of the compression: the chaining word `H i` at the index `i` and the
    message word `M j` at the index `8 + j`. -/
def sha2InWords {w : Nat} (H : Fin 8 → BitVec w) (M : Fin 16 → BitVec w) : Fin 24 → BitVec w :=
  fun i => if h : i.val < 8 then H ⟨i.val, h⟩ else M ⟨i.val - 8, by omega⟩

/-- **The SHA-2 compression function at `P` with one input array and an output array**: the
    loads of the `24` words of the input array as the words numbered `0, …, 23`, the compiled
    symbolic compression `sha2Lets P` from the word numbered `24`, and the stores of the eight
    new chaining words into the output array at register indices. The program does not read
    the output array. -/
def sha2CompressBodyP (P : Sha2FamilyParams) :
    Com jasminDialect (sha2InCtxtP P.w) (.stackArr P.w 8) :=
  genLoad Var.here 0 fun ρ0 v0 =>
  genLoads (List.range' 1 23) (ρ0 _ .here) 1 (fun _ => v0) fun ρ1 env1 =>
  genLetsR (sha2Lets P).2.rev.reverse 24 env1 fun ρ3 env3 =>
  genStoresIdx (sha2Lets P).1 (ρ3 _ (ρ1 _ (ρ0 _ (.there .here)))) env3

/-- The word at the index `i < 24` of the input array `sha2InWords H M` is the input word
    numbered `i`. -/
theorem sha2InWords_stackGet {w : Nat} (H : Fin 8 → BitVec w) (M : Fin 16 → BitVec w) (i : Nat)
    (hi : i < 24) : stackGet (sha2InWords H M) (BitVec.ofNat 64 i).toNat = sha2Inputs H M i := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    show i = ((⟨i, hi⟩ : Fin 24) : Nat) from rfl, stackGet_id]
  by_cases h8 : i < 8
  · simp [sha2InWords, sha2Inputs, h8]
  · simp [sha2InWords, sha2Inputs, h8, show i - 8 < 16 by omega]

/-- The words numbered below `24` after the loads of the input array `sha2InWords H M`: the
    chaining word `H i` numbered `i` and the message word `M j` numbered `8 + j`. -/
theorem sha2LoadValsP_lt24 {w : Nat} (H : Fin 8 → BitVec w) (M : Fin 16 → BitVec w) (i : Nat)
    (hi : i < 24) :
    loadVals (sha2InWords H M) (fun _ => stackGet (sha2InWords H M) (BitVec.ofNat 64 0).toNat) 1
      (List.range' 1 23) i = sha2Inputs H M i := by
  rw [loadVals_apply]
  by_cases h0 : i = 0
  · subst h0
    rw [ite_eq_right (by omega)]
    exact sha2InWords_stackGet H M 0 (by omega)
  · rw [ite_eq_left (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega), List.getElem_range',
      show 1 + 1 * (i - 1) = i by omega]
    exact sha2InWords_stackGet H M i hi

/-- **The value of the SHA-2 template with one input array and an output array**: at the
    input array `sha2InWords H M` of the chaining words `H` and the message words `M`, and any
    contents `O` of the output array, the program returns the reference compression
    `sha2CompressRef P H M`. -/
theorem sha2CompressBodyP_value (P : Sha2FamilyParams) (H : Fin 8 → BitVec P.w)
    (M : Fin 16 → BitVec P.w) (O : Fin 8 → BitVec P.w) :
    (sha2CompressBodyP P).denote (.cons (sha2InWords H M) (.cons O .nil)) =
      P.sha2CompressRef H M := by
  unfold sha2CompressBodyP
  refine genLoad_denote _ 0 _ _ (sha2InWords H M) rfl _ fun ρ0 V0 v0 hρ0 hv0 => ?_
  refine genLoads_denote _ _ 1 _ _ V0 (sha2InWords H M) (hρ0 _ _)
    (fun _ => stackGet (sha2InWords H M) (BitVec.ofNat 64 0).toNat) (fun _ => hv0) _
    fun ρ1 V1 env1 hρ1 henv1 => ?_
  refine genLetsR_denote _ 24 env1 _ V1 _ henv1 _ fun ρ3 V3 env3 hρ3 henv3 => ?_
  obtain ⟨hl, hk, hv⟩ := sha2Lets_spec P H M _ (sha2LoadValsP_lt24 H M)
  have hL : ∀ p ∈ (sha2Lets P).1, p.1 < 2 ^ 64 := by
    intro p hp
    obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.mp hp
    have h := hk k (by omega)
    rw [List.getD_eq_getElem _ _ hk'] at h
    omega
  refine (genStoresIdx_denote (sha2Lets P).1 _ env3 V3 O ?_ _ (fun i => henv3 i) hL).trans ?_
  · exact (hρ3 _ _).trans ((hρ1 _ _).trans (hρ0 _ _))
  · rw [foldl_stores8 _ hl hk]
    exact hv

/-- **The events of the SHA-2 template with one input array and an output array are
    fixed**: at leakage parameters with no variable-time operation, the program emits the same
    events at every two valuations. -/
theorem sha2CompressBodyP_events (P : Sha2FamilyParams) (Pj : JLeakParams)
    (hV : ∀ op, Pj.opVT op = none) : LeakFixed (jLeakModel Pj) (sha2CompressBodyP P) := by
  unfold sha2CompressBodyP
  exact genLoad_fixed Pj hV _ _ _ fun _ _ => genLoads_fixed Pj hV _ _ _ _ _ fun _ _ =>
    genLetsR_fixed Pj hV _ _ _ _ fun _ _ => genStoresIdx_fixed Pj hV _ _ _

end CatCrypt.Crypto.SecureCompilation.HashTemplate
