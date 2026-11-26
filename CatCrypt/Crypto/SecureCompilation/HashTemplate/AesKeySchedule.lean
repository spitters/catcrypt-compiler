/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.HashTemplate.AesBitslice

/-!
# The bitsliced AES key schedule as let-bound word expressions

Builders of let-lists of `HashTemplate.StraightLine` over bit planes, one word per bit, lane
`l` of every word belonging to block `l`, and the AES key expansion (FIPS 197, §5.2) for a key
of `nk` words built from them.

The key schedule is computed on planes, once for all lanes: the key planes hold, in lane `l`,
the key of lane `l`, and the schedule computes in each lane the round keys of that lane's key.
A key shared by all blocks is the case of broadcast key planes. Byte `y` of the expanded key
occupies the eight words `kx (8 y + b)`; `SubWord` is four copies of the S-box circuit
`aesSboxGates`, `RotWord` is a renaming of words, and each word of a new key word is one
exclusive or of the words of the earlier key words it depends on, with a word of all ones for
the bits of `Rcon`.

## Main definitions

* `aesLane`, `AesHolds`: lane `l` of a word of a let-list under construction.
* `aesSboxB`, `aesSboxesB`: S-box circuits appended to a let-list.
* `aesXorsB`: exclusive ors of listed words appended to a let-list.
* `AesKsSt`, `aesKsStep`, `aesKsRun`: the key expansion on planes.
* `aesRoundB`: an AES round on planes appended to a let-list, the S-box circuits on the
  sixteen bytes and one exclusive or per output plane (`AesBitslice.aesOutWires`), at state
  and round-key words given by number.

## Main results

* `aesSboxesB_spec`, `aesXorsB_spec`: the lane values of the appended words.
* `aesKsRun_spec`: in each lane `l`, the words `kx (8 y + b)` hold the bits of byte `y` of
  `AES.keyExpansion nk key`, `key` the key of lane `l`, for every `nk > 0`.
* `aesRoundB_spec`: in each lane, the output words of an appended round hold the round (or the
  final round) of the state and the round key held by the input words.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Primitives

variable {w : Nat}

/-! ## 1. Lane values of a let-list under construction -/

/-- Lane `l` of the word numbered `i` after the let-list `s`, its first binding the word
    numbered `N`, from the values `ρ` of the input words. -/
def aesLane (N : Nat) (ρ : Nat → BitVec w) (l : Nat) (s : LetSt w) (i : Nat) : Bool :=
  (s.val N ρ i).getLsbD l

/-- The word numbered `i` is numbered below the next word of `s` and holds `v` at lane `l`. -/
def AesHolds (N : Nat) (ρ : Nat → BitVec w) (l : Nat) (s : LetSt w) (i : Nat) (v : Bool) :
    Prop :=
  i < s.next ∧ aesLane N ρ l s i = v

/-- An extension of a let-list keeps the lane values of its words. -/
theorem AesHolds.ext {N : Nat} {ρ : Nat → BitVec w} {l : Nat} {s s' : LetSt w}
    (hs : s.Good N) (hs' : s'.Good N) (h : s.Ext s') {i : Nat} {v : Bool}
    (hi : AesHolds N ρ l s i v) : AesHolds N ρ l s' i v :=
  ⟨Nat.lt_of_lt_of_le hi.1 (h.next_le hs hs'), by
    unfold aesLane
    rw [h.val_eq hs ρ i hi.1]
    exact hi.2⟩

/-- The input words keep their values: lane `l` of the word numbered `i < N` is lane `l` of
    `ρ i`. -/
theorem aesHolds_input {N : Nat} (ρ : Nat → BitVec w) (l : Nat) {s : LetSt w}
    (hs : s.Good N) (i : Nat) (hi : i < N) : AesHolds N ρ l s i ((ρ i).getLsbD l) := by
  refine ⟨by unfold LetSt.Good at hs; omega, ?_⟩
  unfold aesLane LetSt.val
  rw [evalLets_of_lt _ _ _ _ hi]

/-! ## 2. S-box circuits -/

/-- The S-box circuit on the byte of the words `ins 0, …, ins 7` appended to `s`: its gates
    bind the words numbered from `s.next`. -/
def aesSboxB (ins : Nat → Nat) (s : LetSt w) : LetSt w :=
  ⟨s.next + 128, (aesSboxGates.map (AesGate.toWExp w (relocWire ins s.next))).reverse ++ s.rev⟩

/-- The word of bit `b` of the S-box value of a circuit whose gates bind the words from
    `base`. -/
def aesSboxOutW (base b : Nat) : Nat := base + (aesSboxOut b - 8)

/-- The unfolding of the next word of `aesSboxB`: the circuit binds 128 words. -/
theorem aesSboxB_next (ins : Nat → Nat) (s : LetSt w) : (aesSboxB ins s).next = s.next + 128 :=
  rfl

/-- An appended S-box circuit extends the let-list. -/
theorem aesSboxB_ext (ins : Nat → Nat) (s : LetSt w) : s.Ext (aesSboxB ins s) := ⟨_, rfl⟩

/-- An appended S-box circuit keeps the numbering of the let-list. -/
theorem aesSboxB_good {N : Nat} (ins : Nat → Nat) {s : LetSt w} (hs : s.Good N) :
    (aesSboxB ins s).Good N := by
  unfold LetSt.Good at *
  simp only [aesSboxB, List.length_append, List.length_reverse, List.length_map,
    aesSboxGates_length, hs]
  omega

/-- **The S-box circuit in each lane**: where the words `ins i` hold at lane `l` the bits of
    the byte `x`, the output words of the appended circuit hold the bits of `sbox x`. -/
theorem aesSboxB_spec {N : Nat} {ρ : Nat → BitVec w} {l : Nat} (hl : l < w) {s : LetSt w}
    (hs : s.Good N) (ins : Nat → Nat) (x : UInt8)
    (hx : ∀ i < 8, AesHolds N ρ l s (ins i) (x.toBitVec.getLsbD i)) (b : Nat) (hb : b < 8) :
    AesHolds N ρ l (aesSboxB ins s) (aesSboxOutW s.next b)
      ((AES128.sbox x).toBitVec.getLsbD b) := by
  have hob : 8 ≤ aesSboxOut b ∧ aesSboxOut b < 136 := by
    simp only [aesSboxOut, bpS]
    omega
  refine ⟨by simp only [aesSboxB_next, aesSboxOutW]; omega, ?_⟩
  have hr : aesSboxOutW s.next b = relocWire ins s.next (aesSboxOut b) := by
    simp only [relocWire, aesSboxOutW, show ¬aesSboxOut b < 8 by omega, ite_false]
  unfold aesLane
  rw [show aesSboxB ins s = ⟨s.next + 128, _ ++ s.rev⟩ from rfl, LetSt.val_extend ρ hs,
    List.reverse_reverse, hr,
    evalLets_reloc_getLsbD w aesSboxGates aesSboxGates_wf ins s.next (fun i hi => (hx i hi).1)
      _ l hl _ (by rw [aesSboxGates_length]; omega), ← aesSboxGates_byte x b hb]
  have hf : (fun i : Fin 8 => (s.val N ρ (ins i.val)).getLsbD l) =
      fun i : Fin 8 => x.toBitVec.getLsbD i.val := funext fun i => (hx i.val i.isLt).2
  rw [hf]

/-- The S-box circuits on the bytes of the words `F k 0, …, F k 7` for `k < n`, appended to
    `s` in order. -/
def aesSboxesB (F : Nat → Nat → Nat) : Nat → LetSt w → LetSt w
  | 0, s => s
  | n + 1, s => aesSboxB (F n) (aesSboxesB F n s)

/-- The `n` circuits of `aesSboxesB` bind `128 n` words. -/
theorem aesSboxesB_next (F : Nat → Nat → Nat) :
    ∀ (n : Nat) (s : LetSt w), (aesSboxesB F n s).next = s.next + 128 * n
  | 0, _ => rfl
  | n + 1, s => by
      simp only [aesSboxesB, aesSboxB_next, aesSboxesB_next F n s]
      ring

/-- Appended S-box circuits extend the let-list. -/
theorem aesSboxesB_ext (F : Nat → Nat → Nat) :
    ∀ (n : Nat) (s : LetSt w), s.Ext (aesSboxesB F n s)
  | 0, s => LetSt.Ext.refl s
  | n + 1, s => (aesSboxesB_ext F n s).trans (aesSboxB_ext _ _)

/-- Appended S-box circuits keep the numbering of the let-list. -/
theorem aesSboxesB_good {N : Nat} (F : Nat → Nat → Nat) :
    ∀ (n : Nat) {s : LetSt w}, s.Good N → (aesSboxesB F n s).Good N
  | 0, _, hs => hs
  | n + 1, _, hs => aesSboxB_good _ (aesSboxesB_good F n hs)

/-- **The S-box circuits in each lane**: where the words `F k i` hold at lane `l` the bits of
    the bytes `X k`, the output words of circuit `k` hold the bits of `sbox (X k)`. -/
theorem aesSboxesB_spec {N : Nat} {ρ : Nat → BitVec w} {l : Nat} (hl : l < w)
    (F : Nat → Nat → Nat) (X : Nat → UInt8) :
    ∀ (n : Nat) {s : LetSt w}, s.Good N →
      (∀ k < n, ∀ i < 8, AesHolds N ρ l s (F k i) ((X k).toBitVec.getLsbD i)) →
      ∀ k < n, ∀ b < 8, AesHolds N ρ l (aesSboxesB F n s) (aesSboxOutW (s.next + 128 * k) b)
        ((AES128.sbox (X k)).toBitVec.getLsbD b)
  | 0, _, _, _, k, hk, _, _ => absurd hk (Nat.not_lt_zero k)
  | n + 1, s, hs, hx, k, hk, b, hb => by
      have hsn := aesSboxesB_good F n hs
      have hext := aesSboxesB_ext F n s
      by_cases hkn : k < n
      · exact (aesSboxesB_spec hl F X n hs (fun k' hk' => hx k' (by omega)) k hkn b hb).ext
          hsn (aesSboxB_good _ hsn) (aesSboxB_ext _ _)
      · obtain rfl : k = n := by omega
        have h := aesSboxB_spec hl hsn (F k) (X k)
          (fun i hi => (hx k (by omega) i hi).ext hs hsn hext) b hb
        rwa [aesSboxesB_next] at h

/-! ## 3. Exclusive ors -/

/-- The exclusive ors `xorAll (G k)` for `k < n`, appended to `s` in order. -/
def aesXorsB (G : Nat → List Nat) : Nat → LetSt w → LetSt w
  | 0, s => s
  | n + 1, s => (LetSt.push (xorAll (G n)) (aesXorsB G n s)).2

/-- The `n` exclusive ors of `aesXorsB` bind `n` words. -/
theorem aesXorsB_next (G : Nat → List Nat) :
    ∀ (n : Nat) (s : LetSt w), (aesXorsB G n s).next = s.next + n
  | 0, _ => rfl
  | n + 1, s => by
      simp only [aesXorsB, LetSt.push, aesXorsB_next G n s]
      omega

/-- Appended exclusive ors extend the let-list. -/
theorem aesXorsB_ext (G : Nat → List Nat) :
    ∀ (n : Nat) (s : LetSt w), s.Ext (aesXorsB G n s)
  | 0, s => LetSt.Ext.refl s
  | n + 1, s => (aesXorsB_ext G n s).trans (LetSt.Ext.push _ _)

/-- Appended exclusive ors keep the numbering of the let-list. -/
theorem aesXorsB_good {N : Nat} (G : Nat → List Nat) :
    ∀ (n : Nat) {s : LetSt w}, s.Good N → (aesXorsB G n s).Good N
  | 0, _, hs => hs
  | n + 1, _, hs => LetSt.push_good _ (aesXorsB_good G n hs)

/-- Folds of exclusive ors agree at functions that agree on the list. -/
theorem aes_foldr_xor_congr (L : List Nat) (f g : Nat → Bool) (h : ∀ i ∈ L, f i = g i) :
    L.foldr (fun i acc => f i ^^ acc) false = L.foldr (fun i acc => g i ^^ acc) false := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      simp only [List.foldr_cons, h a List.mem_cons_self,
        ih fun i hi => h i (List.mem_cons_of_mem _ hi)]

/-- **The exclusive ors in each lane**: where the listed words hold at lane `l` the values
    `V`, the word numbered `s.next + k` holds the exclusive or of the values of `G k`. -/
theorem aesXorsB_spec {N : Nat} {ρ : Nat → BitVec w} {l : Nat} (hl : l < w)
    (G : Nat → List Nat) (V : Nat → Bool) :
    ∀ (n : Nat) {s : LetSt w}, s.Good N → (∀ k < n, ∀ i ∈ G k, AesHolds N ρ l s i (V i)) →
      ∀ k < n, AesHolds N ρ l (aesXorsB G n s) (s.next + k)
        ((G k).foldr (fun i acc => V i ^^ acc) false)
  | 0, _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, s, hs, hx, k, hk => by
      have hsn := aesXorsB_good G n hs
      have hext := aesXorsB_ext G n s
      by_cases hkn : k < n
      · exact (aesXorsB_spec hl G V n hs (fun k' hk' => hx k' (by omega)) k hkn).ext hsn
          (LetSt.push_good _ hsn) (LetSt.Ext.push _ _)
      · obtain rfl : k = n := by omega
        refine ⟨by simp only [aesXorsB, LetSt.push, aesXorsB_next]; omega, ?_⟩
        unfold aesLane
        simp only [aesXorsB]
        rw [LetSt.push_val _ hsn, aesXorsB_next]
        simp only [ite_true]
        rw [xorAll_eval_getLsbD _ l hl]
        exact aes_foldr_xor_congr _ _ _ fun i hi => ((hx k (by omega) i hi).ext hs hsn hext).2

/-! ## 4. The key expansion on planes -/

/-- The key expansion under construction: the let-list and the words `kx (8 y + b)` of bit `b`
    of byte `y` of the expanded key. -/
structure AesKsSt (w : Nat) where
  /-- The let-list. -/
  st : LetSt w
  /-- The word of each bit of the expanded key. -/
  kx : Nat → Nat

/-- The new key word `j`: its 32 bits the exclusive ors of the words `pnkW x` of word `j - nk`,
    the words `tempW x` of the temporary word, and the word `ones` where `rc x` holds, appended
    to `s1`. -/
def aesKsFinish (j ones : Nat) (pnkW tempW : Nat → Nat) (rc : Nat → Bool) (kx : Nat → Nat)
    (s1 : LetSt w) : AesKsSt w :=
  ⟨aesXorsB (fun x => [pnkW x, tempW x] ++ (if rc x then [ones] else [])) 32 s1,
    fun y => if 32 * j ≤ y ∧ y < 32 * j + 32 then s1.next + (y - 32 * j) else kx y⟩

/-- **Step `t` of the key expansion on planes**: the key word `j = t + nk`, from the words of
    word `j - 1` (through `RotWord`, `SubWord` and `Rcon` when `nk` divides `j`, through
    `SubWord` when `nk > 6` and `j ≡ 4 (mod nk)`) and of word `j - nk`; `ones` is a word of all
    ones. -/
def aesKsStep (nk ones : Nat) (a : AesKsSt w) (t : Nat) : AesKsSt w :=
  if (t + nk) % nk == 0 then
    aesKsFinish (t + nk) ones (fun x => a.kx (32 * t + x))
      (fun x => aesSboxOutW (a.st.next + 128 * (x / 8)) (x % 8))
      (fun x => x / 8 == 0 && (AES128.rcon ((t + nk) / nk - 1)).toBitVec.getLsbD (x % 8)) a.kx
      (aesSboxesB (fun i b => a.kx (32 * (t + nk - 1) + 8 * ((i + 1) % 4) + b)) 4 a.st)
  else if 6 < nk ∧ (t + nk) % nk = 4 then
    aesKsFinish (t + nk) ones (fun x => a.kx (32 * t + x))
      (fun x => aesSboxOutW (a.st.next + 128 * (x / 8)) (x % 8)) (fun _ => false) a.kx
      (aesSboxesB (fun i b => a.kx (32 * (t + nk - 1) + 8 * i + b)) 4 a.st)
  else
    aesKsFinish (t + nk) ones (fun x => a.kx (32 * t + x))
      (fun x => a.kx (32 * (t + nk - 1) + x)) (fun _ => false) a.kx a.st

/-- **The key expansion on planes**: the steps for the key words `nk, …, 4 (nk + 7) - 1`. -/
def aesKsRun (nk ones : Nat) (a : AesKsSt w) : AesKsSt w :=
  Fin.foldl (4 * (nk + 7) - nk) (fun a (wi : Fin (4 * (nk + 7) - nk)) => aesKsStep nk ones a wi.val)
    a

/-! ## 5. The key expansion in each lane -/

/-- Byte `y` of a vector, `0` past its end. -/
def aesVb {n : Nat} (v : Vector UInt8 n) (y : Nat) : UInt8 :=
  if h : y < n then v.get ⟨y, h⟩ else 0

/-- Four writes at consecutive indices from `base`. -/
theorem aes_fold4_vb {n : Nat} (base : Nat) (nw : Fin 4 → UInt8)
    (h : ∀ bi : Fin 4, base + bi.val < n) (v : Vector UInt8 n) (y : Nat) :
    aesVb (Fin.foldl 4 (fun e (bi : Fin 4) => e.set (base + bi.val) (nw bi) (h bi)) v) y =
      if h' : base ≤ y ∧ y < base + 4 then nw ⟨y - base, by omega⟩ else aesVb v y := by
  unfold aesVb
  simp only [Fin.foldl_succ_last, Fin.foldl_zero]
  split <;> split <;> grind [Vector.get, Vector.toArray_set, Fin.val_castSucc]

/-- Two folds over the same indices keep an invariant of their pairs of values. -/
theorem aes_fin_foldl_inv2 {α β : Type} (Q : Nat → α → β → Prop) :
    ∀ {n : Nat} (f : α → Fin n → α) (g : β → Fin n → β) (x : α) (y : β), Q 0 x y →
      (∀ (i : Fin n) a b, Q i.val a b → Q (i.val + 1) (f a i) (g b i)) →
        Q n (Fin.foldl n f x) (Fin.foldl n g y)
  | 0, _, _, _, _, h0, _ => by simpa using h0
  | n + 1, f, g, x, y, h0, hs => by
      rw [Fin.foldl_succ_last, Fin.foldl_succ_last]
      exact hs (Fin.last n) _ _
        (aes_fin_foldl_inv2 Q (fun a i => f a i.castSucc) (fun b i => g b i.castSucc) x y h0
          fun i a b h => hs i.castSucc a b h)

/-- The invariant of the key expansion after `t` steps: the let-list extends `s0`, the word
    `ones` holds all ones, and the words of the key words below `nk + t` hold the bytes of
    `v`. -/
def AesKsInv (N : Nat) (ρ : Nat → BitVec w) (l nk ones : Nat) (s0 : LetSt w) (t : Nat)
    (v : Vector UInt8 (16 * (nk + 7))) (a : AesKsSt w) : Prop :=
  a.st.Good N ∧ s0.Ext a.st ∧ AesHolds N ρ l a.st ones true ∧
    ∀ y < 4 * (nk + t), ∀ b < 8,
      AesHolds N ρ l a.st (a.kx (8 * y + b)) ((aesVb v y).toBitVec.getLsbD b)

/-- **The new key word in each lane**: where the words `pnkW x`, `tempW x` and `ones` hold at
    lane `l` the values `P x`, `T x` and `true`, bit `x` of the new key word holds
    `P x ^^ (T x ^^ rc x)`. -/
theorem aesKsFinish_spec {N : Nat} {ρ : Nat → BitVec w} {l : Nat} (hl : l < w)
    (j ones : Nat) (pnkW tempW : Nat → Nat) (rc : Nat → Bool) (kx : Nat → Nat) {s1 : LetSt w}
    (hs : s1.Good N) (P T : Nat → Bool) (hones : AesHolds N ρ l s1 ones true)
    (hp : ∀ x < 32, AesHolds N ρ l s1 (pnkW x) (P x))
    (ht : ∀ x < 32, AesHolds N ρ l s1 (tempW x) (T x)) :
    (aesKsFinish j ones pnkW tempW rc kx s1).st.Good N ∧
      s1.Ext (aesKsFinish j ones pnkW tempW rc kx s1).st ∧
      ∀ x < 32, AesHolds N ρ l (aesKsFinish j ones pnkW tempW rc kx s1).st
        ((aesKsFinish j ones pnkW tempW rc kx s1).kx (32 * j + x)) (P x ^^ (T x ^^ rc x)) := by
  refine ⟨aesXorsB_good _ 32 hs, aesXorsB_ext _ 32 s1, fun x hx => ?_⟩
  have hmem : ∀ k < 32, ∀ i ∈ [pnkW k, tempW k] ++ (if rc k then [ones] else []),
      AesHolds N ρ l s1 i (aesLane N ρ l s1 i) := by
    intro k hk i hi
    refine ⟨?_, rfl⟩
    have := (hp k hk).1
    have := (ht k hk).1
    have := hones.1
    split at hi <;> simp only [List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hi <;> omega
  have h := aesXorsB_spec hl (fun x => [pnkW x, tempW x] ++ (if rc x then [ones] else []))
    (aesLane N ρ l s1) 32 hs hmem x hx
  have hkx : (aesKsFinish j ones pnkW tempW rc kx s1).kx (32 * j + x) = s1.next + x := by
    simp only [aesKsFinish, show 32 * j ≤ 32 * j + x ∧ 32 * j + x < 32 * j + 32 by omega,
      and_self, ite_true]
    omega
  rw [hkx]
  refine ⟨h.1, h.2.trans ?_⟩
  cases rc x <;> simp [(hp x hx).2, (ht x hx).2, hones.2]

/-- **A step of the key expansion keeps the invariant**, given the let-list `s1` that
    computes the temporary word `tw` in the words `tempW` (its bits `T x ^^ rc x`) and the
    vector `v'` of the step. -/
theorem aesKsFinish_inv {N : Nat} {ρ : Nat → BitVec w} {l : Nat} (hl : l < w)
    {nk ones t : Nat} (hnk : 0 < nk) {s0 : LetSt w} {v v' : Vector UInt8 (16 * (nk + 7))}
    {a : AesKsSt w} (hQ : AesKsInv N ρ l nk ones s0 t v a) {s1 : LetSt w} (hs1 : s1.Good N)
    (hext : a.st.Ext s1) (tempW : Nat → Nat) (rc : Nat → Bool) (T : Nat → Bool)
    (ht : ∀ x < 32, AesHolds N ρ l s1 (tempW x) (T x)) (tw : Nat → UInt8)
    (hT : ∀ x < 32, (tw (x / 8)).toBitVec.getLsbD (x % 8) = (T x ^^ rc x))
    (hv' : ∀ y, aesVb v' y = if 4 * (t + nk) ≤ y ∧ y < 4 * (t + nk) + 4 then
      aesVb v (4 * t + (y - 4 * (t + nk))) ^^^ tw (y - 4 * (t + nk)) else aesVb v y) :
    AesKsInv N ρ l nk ones s0 (t + 1) v'
      (aesKsFinish (t + nk) ones (fun x => a.kx (32 * t + x)) tempW rc a.kx s1) := by
  obtain ⟨hg, hE, hones, hkx⟩ := hQ
  have hP : ∀ x < 32, AesHolds N ρ l s1 (a.kx (32 * t + x))
      ((aesVb v (4 * t + x / 8)).toBitVec.getLsbD (x % 8)) := by
    intro x hx
    have h := hkx (4 * t + x / 8) (by omega) (x % 8) (by omega)
    rw [show 8 * (4 * t + x / 8) + x % 8 = 32 * t + x by omega] at h
    exact h.ext hg hs1 hext
  obtain ⟨hg2, hE2, hnew⟩ := aesKsFinish_spec hl (t + nk) ones _ tempW rc a.kx hs1 _ T
    (hones.ext hg hs1 hext) hP ht
  refine ⟨hg2, hE.trans (hext.trans hE2), (hones.ext hg hs1 hext).ext hs1 hg2 hE2,
    fun y hy b hb => ?_⟩
  rw [hv' y]
  by_cases hyr : 4 * (t + nk) ≤ y ∧ y < 4 * (t + nk) + 4
  · simp only [hyr, and_self, ite_true]
    have hx := hnew (8 * (y - 4 * (t + nk)) + b) (by omega)
    have hx8 : (8 * (y - 4 * (t + nk)) + b) / 8 = y - 4 * (t + nk) := by omega
    have hxm : (8 * (y - 4 * (t + nk)) + b) % 8 = b := by omega
    rw [← hT _ (by omega), hx8, hxm] at hx
    rw [show 8 * y + b = 32 * (t + nk) + (8 * (y - 4 * (t + nk)) + b) by omega]
    simpa only [UInt8.toBitVec_xor, BitVec.getLsbD_xor] using hx
  · have hy' : y < 4 * (nk + t) := by omega
    have hk : (aesKsFinish (t + nk) ones (fun x => a.kx (32 * t + x)) tempW rc a.kx s1).kx
        (8 * y + b) = a.kx (8 * y + b) := by
      simp only [aesKsFinish]
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
    rw [hk, ite_eq_right_iff.mpr (fun h => absurd h hyr)]
    exact (hkx y hy' b hb).ext hg hg2 (hext.trans hE2)

/-- **The key expansion on planes in each lane**: where the words `a0.kx (8 y + b)` of the
    key bytes and the word `ones` hold at lane `l` the bits of the key `key` and `true`, the
    words `kx (8 y + b)` after `aesKsRun` hold the bits of byte `y` of the expanded key. -/
theorem aesKsRun_spec {N : Nat} {ρ : Nat → BitVec w} {l : Nat} (hl : l < w) (nk ones : Nat)
    (hnk : 0 < nk) (key : Fin (4 * nk) → UInt8) (a0 : AesKsSt w) (hg0 : a0.st.Good N)
    (hones : AesHolds N ρ l a0.st ones true)
    (hkey : ∀ y (hy : y < 4 * nk), ∀ b < 8,
      AesHolds N ρ l a0.st (a0.kx (8 * y + b)) ((key ⟨y, hy⟩).toBitVec.getLsbD b)) :
    (aesKsRun nk ones a0).st.Good N ∧ a0.st.Ext (aesKsRun nk ones a0).st ∧
      AesHolds N ρ l (aesKsRun nk ones a0).st ones true ∧
      ∀ y (hy : y < 16 * (nk + 7)), ∀ b < 8,
        AesHolds N ρ l (aesKsRun nk ones a0).st ((aesKsRun nk ones a0).kx (8 * y + b))
          ((AES.keyExpansion nk key ⟨y, hy⟩).toBitVec.getLsbD b) := by
  suffices h : AesKsInv N ρ l nk ones a0.st (4 * (nk + 7) - nk) (AES.keyExpansionVec nk key)
      (aesKsRun nk ones a0) by
    refine ⟨h.1, h.2.1, h.2.2.1, fun y hy b hb => ?_⟩
    have h' := h.2.2.2 y (by omega) b hb
    simpa only [aesVb, hy, dite_true, AES.keyExpansion] using h'
  unfold AES.keyExpansionVec aesKsRun
  dsimp only
  apply aes_fin_foldl_inv2 (fun t v a => AesKsInv N ρ l nk ones a0.st t v a)
  · refine ⟨hg0, LetSt.Ext.refl _, hones, fun y hy b hb => ?_⟩
    have h := hkey y (by omega) b hb
    have hy4 : y < 4 * nk := by omega
    simpa [aesVb, Vector.get, show y < 16 * (nk + 7) by omega, hy4, Fin.cast] using h
  · intro i v a hQ
    have hit := i.isLt
    have hprev : ∀ k < 4, ∀ ii < 8, AesHolds N ρ l a.st
        (a.kx (32 * (i.val + nk - 1) + 8 * k + ii))
        ((aesVb v (4 * (i.val + nk - 1) + k)).toBitVec.getLsbD ii) := by
      intro k hk ii hii
      have h := hQ.2.2.2 (4 * (i.val + nk - 1) + k) (by omega) ii hii
      rwa [show 8 * (4 * (i.val + nk - 1) + k) + ii = 32 * (i.val + nk - 1) + 8 * k + ii by
        omega] at h
    unfold aesKsStep
    by_cases c1 : (i.val + nk) % nk = 0
    · have c1' : ((i.val + nk) % nk == 0) = true := by simp [c1]
      simp only [c1', ite_true]
      refine aesKsFinish_inv hl hnk hQ (aesSboxesB_good _ 4 hQ.1) (aesSboxesB_ext _ 4 _) _ _
        (fun x => (AES128.sbox (aesVb v (4 * (i.val + nk - 1) + (x / 8 + 1) % 4))).toBitVec.getLsbD
          (x % 8)) (fun x hx => ?_)
        (fun k => if k = 0 then AES128.sbox (aesVb v (4 * (i.val + nk - 1) + (k + 1) % 4)) ^^^
            AES128.rcon ((i.val + nk) / nk - 1)
          else AES128.sbox (aesVb v (4 * (i.val + nk - 1) + (k + 1) % 4)))
        (fun x hx => ?_) (fun y => ?_)
      · exact aesSboxesB_spec hl _ (fun k => aesVb v (4 * (i.val + nk - 1) + (k + 1) % 4)) 4
          hQ.1 (fun k _ ii hii => hprev _ (by omega) ii hii) (x / 8) (by omega) (x % 8) (by omega)
      · by_cases hx0 : x / 8 = 0
        · simp [hx0, UInt8.toBitVec_xor]
        · have hx0' : (x / 8 == 0) = false := by simpa using hx0
          simp [hx0, hx0']
      · rw [aes_fold4_vb]
        by_cases hyr : 4 * (i.val + nk) ≤ y ∧ y < 4 * (i.val + nk) + 4
        · have e1 : 4 * i.val + (y - 4 * (i.val + nk)) < 16 * (nk + 7) := by omega
          have e2 : 4 * (i.val + nk - 1) + (y - 4 * (i.val + nk) + 1) % 4 < 16 * (nk + 7) := by
            omega
          simp [hyr, AES.getWord, AES128.subWord, AES128.rotWord, aesVb, e1, e2]
        · simp [hyr]
    · have c1' : ((i.val + nk) % nk == 0) = false := by simpa using c1
      by_cases c2 : 6 < nk ∧ (i.val + nk) % nk = 4
      · simp only [c2, and_self, ite_true, show (4 == 0) = false from rfl, Bool.false_eq_true,
          ite_false]
        refine aesKsFinish_inv hl hnk hQ (aesSboxesB_good _ 4 hQ.1) (aesSboxesB_ext _ 4 _) _ _
          (fun x => (AES128.sbox (aesVb v (4 * (i.val + nk - 1) + x / 8))).toBitVec.getLsbD
            (x % 8)) (fun x hx => ?_)
          (fun k => AES128.sbox (aesVb v (4 * (i.val + nk - 1) + k))) (fun x hx => ?_) (fun y => ?_)
        · exact aesSboxesB_spec hl _ (fun k => aesVb v (4 * (i.val + nk - 1) + k)) 4
            hQ.1 (fun k hk ii hii => hprev k hk ii hii) (x / 8) (by omega) (x % 8) (by omega)
        · simp
        · rw [aes_fold4_vb]
          by_cases hyr : 4 * (i.val + nk) ≤ y ∧ y < 4 * (i.val + nk) + 4
          · have e1 : 4 * i.val + (y - 4 * (i.val + nk)) < 16 * (nk + 7) := by omega
            have e2 : 4 * (i.val + nk - 1) + (y - 4 * (i.val + nk)) < 16 * (nk + 7) := by omega
            simp [hyr, AES.getWord, AES128.subWord, aesVb, e1, e2]
          · simp [hyr]
      · simp only [c1', c2, Bool.false_eq_true, ite_false]
        refine aesKsFinish_inv hl hnk hQ hQ.1 (LetSt.Ext.refl _) _ _
          (fun x => (aesVb v (4 * (i.val + nk - 1) + x / 8)).toBitVec.getLsbD (x % 8))
          (fun x hx => ?_) (fun k => aesVb v (4 * (i.val + nk - 1) + k)) (fun x hx => ?_)
          (fun y => ?_)
        · have h := hprev (x / 8) (by omega) (x % 8) (by omega)
          rwa [show 32 * (i.val + nk - 1) + 8 * (x / 8) + x % 8 = 32 * (i.val + nk - 1) + x by
            omega] at h
        · simp
        · rw [aes_fold4_vb]
          by_cases hyr : 4 * (i.val + nk) ≤ y ∧ y < 4 * (i.val + nk) + 4
          · have e1 : 4 * i.val + (y - 4 * (i.val + nk)) < 16 * (nk + 7) := by omega
            have e2 : 4 * (i.val + nk - 1) + (y - 4 * (i.val + nk)) < 16 * (nk + 7) := by omega
            simp [hyr, AES.getWord, aesVb, e1, e2]
          · simp [hyr]

/-! ## 6. A round on planes -/

/-- Byte `k` of a state, `0` past its end. -/
def aesSb (S : AES128.State) (k : Nat) : UInt8 := if h : k < 16 then S ⟨k, h⟩ else 0

/-- The planes of the states `S` and `K` on one-lane words: plane `p < 128` holds bit `p % 8`
    of byte `p / 8` of `S`, plane `128 + q` bit `q % 8` of byte `q / 8` of `K`. -/
def aesPlanes1 (S K : AES128.State) (i : Nat) : BitVec 1 :=
  BitVec.ofBool (if i < 128 then (aesSb S (i / 8)).toBitVec.getLsbD (i % 8)
    else (aesSb K ((i - 128) / 8)).toBitVec.getLsbD ((i - 128) % 8))

/-- The bytes of the one-lane planes of `S` and `K` are the bytes of `S` and `K`. -/
theorem aesByteAt_planes1 (S K : AES128.State) (k : Nat) (hk : k < 16) :
    aesByteAt (aesPlanes1 S K) 0 0 k = aesSb S k ∧
      aesByteAt (aesPlanes1 S K) 128 0 k = aesSb K k := by
  constructor <;>
  · apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    rw [aesByteAt_getLsbD _ _ _ _ _ hb]
    have e1 : (8 * k + b) / 8 = k := by omega
    have e2 : (8 * k + b) % 8 = b := by omega
    simp [aesPlanes1, e1, e2, show 8 * k + b < 128 by omega,
      show ¬128 + 8 * k + b < 128 by omega, show 128 + 8 * k + b - 128 = 8 * k + b by omega]

/-- The states of the one-lane planes of `S` and `K` are `S` and `K`. -/
theorem aesUnpack_planes1 (S K : AES128.State) :
    aesUnpack (aesPlanes1 S K) 0 0 = S ∧ aesUnpack (aesPlanes1 S K) 128 0 = K := by
  constructor <;>
  · funext k
    simp only [aesUnpack, (aesByteAt_planes1 S K k.val k.isLt).1,
      (aesByteAt_planes1 S K k.val k.isLt).2, aesSb, k.isLt, dite_true]

/-- **The output planes of a round on bits**: at wire values `V` holding the bits of the S-box
    values of the state `S` and the bits of the round key `K`, the exclusive or of the words of
    the output plane `p` is bit `p % 8` of byte `p / 8` of the round. -/
theorem aesOutWires_state (final : Bool) (S K : AES128.State) (V : Nat → Bool)
    (hsub : ∀ k < 16, ∀ b < 8,
      V (aesSubWire k b) = (AES128.sbox (aesSb S k)).toBitVec.getLsbD b)
    (hkey : ∀ q < 128, V (128 + q) = (aesSb K (q / 8)).toBitVec.getLsbD (q % 8)) (p : Nat)
    (hp : p < 128) :
    (aesOutWires final p).foldr (fun i acc => V i ^^ acc) false =
      (aesSb (aesRoundSpec final S K) (p / 8)).toBitVec.getLsbD (p % 8) := by
  have h := aesOutWires_bits final (aesPlanes1 S K) 0 V
    (fun k hk b hb => by rw [hsub k hk b hb, (aesByteAt_planes1 S K k hk).1])
    (fun q hq => by simp [hkey q hq, aesPlanes1]) p hp
  rw [(aesUnpack_planes1 S K).1, (aesUnpack_planes1 S K).2] at h
  rw [h]
  simp [aesSb, show p / 8 < 16 by omega]

/-- The word read by the abstract word `n` of `aesOutWires`: the round-key word `kw (n - 128)`
    below `256`, the S-box word of a round whose S-box circuits bind the words from `B`
    otherwise. -/
def aesRoundWire (kw : Nat → Nat) (B n : Nat) : Nat :=
  if n < 256 then kw (n - 128) else B + (n - 256)

/-- **A round appended to a let-list**: the S-box circuits on the bytes of the state words
    `sw`, then the output planes, at the round-key words `kw`; the final round when `final`
    holds. Output plane `p` binds the word numbered `s.next + 2048 + p`. -/
def aesRoundB (final : Bool) (sw kw : Nat → Nat) (s : LetSt w) : LetSt w :=
  aesXorsB (fun p => (aesOutWires final p).map (aesRoundWire kw s.next)) 128
    (aesSboxesB (fun k i => sw (8 * k + i)) 16 s)

/-- The words of `aesOutWires` are numbered from `128`. -/
theorem aesOutWires_ge (final : Bool) (p : Nat) : ∀ i ∈ aesOutWires final p, 128 ≤ i := by
  intro i hi
  have : ∀ k b, 256 ≤ aesSubWire k b := fun k b => by unfold aesSubWire; omega
  unfold aesOutWires at hi
  split at hi <;> simp [xtimeSrc] at hi <;> grind

/-- **A round on planes in each lane**: where the state words `sw` and the round-key words
    `kw` hold at lane `l` the bits of `S` and `K`, the output planes of the appended round hold
    the bits of the round. -/
theorem aesRoundB_spec {N : Nat} {ρ : Nat → BitVec w} {l : Nat} (hl : l < w) (final : Bool)
    (sw kw : Nat → Nat) (S K : AES128.State) {s : LetSt w} (hs : s.Good N)
    (hsw : ∀ p < 128, AesHolds N ρ l s (sw p) ((aesSb S (p / 8)).toBitVec.getLsbD (p % 8)))
    (hkw : ∀ p < 128, AesHolds N ρ l s (kw p) ((aesSb K (p / 8)).toBitVec.getLsbD (p % 8))) :
    (aesRoundB final sw kw s).Good N ∧ s.Ext (aesRoundB final sw kw s) ∧
      ∀ p < 128, AesHolds N ρ l (aesRoundB final sw kw s) (s.next + 2048 + p)
        ((aesSb (aesRoundSpec final S K) (p / 8)).toBitVec.getLsbD (p % 8)) := by
  have hs1 := aesSboxesB_good (fun k i => sw (8 * k + i)) 16 hs
  have hext1 := aesSboxesB_ext (fun k i => sw (8 * k + i)) 16 s
  have hn1 := aesSboxesB_next (fun k i => sw (8 * k + i)) 16 s
  have hsb := aesSboxesB_spec hl (fun k i => sw (8 * k + i)) (aesSb S) 16 hs
    (fun k hk i hi => by
      have h := hsw (8 * k + i) (by omega)
      rwa [show (8 * k + i) / 8 = k by omega, show (8 * k + i) % 8 = i by omega] at h)
  have hmem : ∀ p < 128, ∀ i ∈ (aesOutWires final p).map (aesRoundWire kw s.next),
      AesHolds N ρ l (aesSboxesB (fun k i => sw (8 * k + i)) 16 s) i
        (aesLane N ρ l (aesSboxesB (fun k i => sw (8 * k + i)) 16 s) i) := by
    intro p hp i hi
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hi
    have h1 := aesOutWires_lt final p hp n hn
    have h2 := aesOutWires_ge final p n hn
    refine ⟨?_, rfl⟩
    unfold aesRoundWire
    split
    · exact ((hkw (n - 128) (by omega)).ext hs hs1 hext1).1
    · omega
  refine ⟨aesXorsB_good _ 128 hs1, hext1.trans (aesXorsB_ext _ 128 _), fun p hp => ?_⟩
  have h := aesXorsB_spec hl _ _ 128 hs1 hmem p hp
  rw [hn1, show s.next + 128 * 16 + p = s.next + 2048 + p by omega, List.foldr_map] at h
  refine ⟨h.1, h.2.trans (aesOutWires_state final S K _ (fun k hk b hb => ?_)
    (fun q hq => ?_) p hp)⟩
  · have hw : aesRoundWire kw s.next (aesSubWire k b) = aesSboxOutW (s.next + 128 * k) b := by
      unfold aesRoundWire aesSubWire aesSboxOutW
      rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
      omega
    rw [hw]
    exact (hsb k hk b hb).2
  · have hw : aesRoundWire kw s.next (128 + q) = kw q := by
      unfold aesRoundWire
      simp [show 128 + q < 256 by omega]
    rw [hw]
    exact ((hkw q hq).ext hs hs1 hext1).2

end CatCrypt.Crypto.SecureCompilation.HashTemplate
