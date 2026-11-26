/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.HashTemplate.AesKeySchedule

/-!
# The bitsliced AES cipher as a constant-time `jasminDialect` template

AES encryption (FIPS 197, §5.1) under a key of `nk` words, for every `nk > 0` and in
particular AES-128, AES-192 and AES-256 (`nk = 4, 6, 8`), on `w` blocks at once, as a
straight-line program of `jasminDialect` on `w`-bit words generated through the compiler of
`HashTemplate.StraightLine`.

The layout is that of `HashTemplate.AesBitslice`, one word per bit. The input array holds the
128 planes of the blocks (plane `8 k + b` holds bit `b` of byte `k` of every block, lane `l`
belonging to block `l`) and then the `32 nk` planes of the keys (plane `128 + 8 k + b` holds
bit `b` of key byte `k`, lane `l` the key of block `l`). The program computes the key schedule
of `HashTemplate.AesKeySchedule` once on the key planes, for all lanes together; a key shared
by all blocks is the case of broadcast key planes, every lane of a key plane equal. It then
computes the initial `AddRoundKey`, the `nk + 5` rounds and the final round on the state
planes, and stores the 128 planes of the ciphertexts by register index into the output array,
which it does not read. It has no branch and no memory access at an index that depends on its
inputs.

## Main definitions

* `aesEncN nk`: the number `128 + 32 nk` of input planes.
* `aesEncB`: the let-list of the cipher and the words of the ciphertext planes.
* `aesEncBody`: the program.

## Main results

* `aesEncB_spec`: in each lane, the ciphertext words hold the planes of `AES.encrypt`.
* `aesEncBody_value`: the program returns, in every lane, the planes of
  `AES.encrypt nk key block` at that lane's key and block, whatever the contents of the output
  array; `aesEncBody_value_aes128`, `_aes192`, `_aes256` at `nk = 4, 6, 8`.
* `aesEncBody_events`: the program emits the same events at every two valuations, at leakage
  parameters with no variable-time operation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.HashTemplate

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.Primitives
open CatCrypt.Crypto.SecureCompilation.Algebraic.ModArithLimbTemplate (LeakFixed)
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak (JLeakParams jLeakModel)
open Ctxt (Var Valuation)

variable {w : Nat}

/-! ## 1. The cipher on planes -/

/-- The number of input planes of the cipher: the 128 state planes and the `32 nk` key
    planes. -/
def aesEncN (nk : Nat) : Nat := 128 + 32 * nk

/-- The key expansion before its steps: the word numbered `aesEncN nk`, all ones, bound after
    the input words, and the key planes `128 + y` as the words of the key bytes. -/
def aesKs0 (w nk : Nat) : AesKsSt w :=
  ⟨(LetSt.push (.const (BitVec.allOnes w)) ⟨aesEncN nk, []⟩).2, fun y => 128 + y⟩

/-- The key expansion of the cipher on planes. -/
def aesEncKs (w nk : Nat) : AesKsSt w := aesKsRun nk (aesEncN nk) (aesKs0 w nk)

/-- The cipher under construction: the let-list and the words of the state planes. -/
structure AesEncSt (w : Nat) where
  /-- The let-list. -/
  st : LetSt w
  /-- The word of each state plane. -/
  sw : Nat → Nat

/-- The initial `AddRoundKey` appended to `s`: the exclusive ors of the input state planes and
    the key words `kx`. -/
def aesArkB (kx : Nat → Nat) (s : LetSt w) : AesEncSt w :=
  ⟨aesXorsB (fun p => [p, kx p]) 128 s, fun p => s.next + p⟩

/-- A round appended to the cipher under construction, at the round-key words `kw`. -/
def aesRoundStepB (final : Bool) (kw : Nat → Nat) (a : AesEncSt w) : AesEncSt w :=
  ⟨aesRoundB final a.sw kw a.st, fun p => a.st.next + 2048 + p⟩

/-- **The bitsliced cipher on planes** for a key of `nk` words: the key expansion, the initial
    `AddRoundKey`, the `nk + 5` rounds and the final round. -/
def aesEncB (w nk : Nat) : AesEncSt w :=
  let ks := aesEncKs w nk
  aesRoundStepB true (fun q => ks.kx (128 * (nk + 6) + q))
    (Fin.foldl (nk + 5) (fun a (r : Fin (nk + 5)) =>
        aesRoundStepB false (fun q => ks.kx (128 * (r.val + 1) + q)) a)
      (aesArkB ks.kx ks.st))

/-! ## 2. The cipher on planes in each lane -/

/-- The invariant of the rounds: the let-list extends `s0` and the state words hold the bytes
    of `v`. -/
def AesEncInv (N : Nat) (ρ : Nat → BitVec w) (l : Nat) (s0 : LetSt w) (v : Vector UInt8 16)
    (a : AesEncSt w) : Prop :=
  a.st.Good N ∧ s0.Ext a.st ∧
    ∀ p < 128, AesHolds N ρ l a.st (a.sw p) ((aesSb v.get (p / 8)).toBitVec.getLsbD (p % 8))

/-- Reading the vector of the values of `f` is `f`. -/
theorem aes_vector_get_ofFn {n : Nat} (f : Fin n → UInt8) : (Vector.ofFn f).get = f := by
  funext i
  simp [Vector.get, Fin.cast]

/-- The initial `AddRoundKey` establishes the invariant. -/
theorem aesArkB_inv {N : Nat} {ρ : Nat → BitVec w} {l : Nat} (hl : l < w) (kx : Nat → Nat)
    {s : LetSt w} (hs : s.Good N) (blk rk : AES128.State)
    (hblk : ∀ p < 128, AesHolds N ρ l s p ((aesSb blk (p / 8)).toBitVec.getLsbD (p % 8)))
    (hrk : ∀ p < 128, AesHolds N ρ l s (kx p) ((aesSb rk (p / 8)).toBitVec.getLsbD (p % 8))) :
    AesEncInv N ρ l s (Vector.ofFn (AES128.addRoundKey blk rk)) (aesArkB kx s) := by
  refine ⟨aesXorsB_good _ 128 hs, aesXorsB_ext _ 128 s, fun p hp => ?_⟩
  have h := aesXorsB_spec hl (fun p => [p, kx p]) (aesLane N ρ l s) 128 hs
    (fun k hk i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi <;> rw [hi]
      · exact ⟨(hblk k hk).1, rfl⟩
      · exact ⟨(hrk k hk).1, rfl⟩) p hp
  refine ⟨h.1, h.2.trans ?_⟩
  have hp8 : p / 8 < 16 := by omega
  simp [(hblk p hp).2, (hrk p hp).2, aesSb, hp8, aes_vector_get_ofFn, AES128.addRoundKey]

/-- A round keeps the invariant. -/
theorem aesRoundStepB_inv {N : Nat} {ρ : Nat → BitVec w} {l : Nat} (hl : l < w) (final : Bool)
    (kw : Nat → Nat) {s0 : LetSt w} {v : Vector UInt8 16} {a : AesEncSt w}
    (hs0 : s0.Good N) (hQ : AesEncInv N ρ l s0 v a) (K : AES128.State)
    (hkw : ∀ p < 128, AesHolds N ρ l s0 (kw p) ((aesSb K (p / 8)).toBitVec.getLsbD (p % 8))) :
    AesEncInv N ρ l s0 (Vector.ofFn (aesRoundSpec final v.get K)) (aesRoundStepB final kw a) := by
  obtain ⟨hg, hE, hsw⟩ := hQ
  obtain ⟨hg2, hE2, h⟩ := aesRoundB_spec hl final a.sw kw v.get K hg hsw
    fun p hp => (hkw p hp).ext hs0 hg hE
  refine ⟨hg2, hE.trans hE2, fun p hp => ?_⟩
  rw [aes_vector_get_ofFn]
  exact h p hp

/-- The key of lane `l` in the key planes of the input words `ρ`. -/
def aesKeyAt (ρ : Nat → BitVec w) (l nk : Nat) : Fin (4 * nk) → UInt8 :=
  fun k => aesByteAt ρ 128 l k.val

/-- **The bitsliced cipher on planes in each lane**: lane `l` of the ciphertext words holds the
    planes of `AES.encrypt nk` at the key and the block of lane `l`. -/
theorem aesEncB_spec {ρ : Nat → BitVec w} {l : Nat} (hl : l < w) (nk : Nat) (hnk : 0 < nk) :
    (aesEncB w nk).st.Good (aesEncN nk) ∧ ∀ p < 128,
      AesHolds (aesEncN nk) ρ l (aesEncB w nk).st ((aesEncB w nk).sw p)
        ((aesSb (AES.encrypt nk (aesKeyAt ρ l nk) (aesUnpack ρ 0 l)) (p / 8)).toBitVec.getLsbD
          (p % 8)) := by
  have hge : LetSt.Good (aesEncN nk) (⟨aesEncN nk, []⟩ : LetSt w) := rfl
  have hg0 : (aesKs0 w nk).st.Good (aesEncN nk) := LetSt.push_good _ hge
  have hones : AesHolds (aesEncN nk) ρ l (aesKs0 w nk).st (aesEncN nk) true := by
    refine ⟨by simp [aesKs0, LetSt.push], ?_⟩
    unfold aesLane aesKs0
    rw [LetSt.push_val _ hge]
    simp [WExp.eval, hl]
  have hkey : ∀ y (hy : y < 4 * nk), ∀ b < 8, AesHolds (aesEncN nk) ρ l (aesKs0 w nk).st
      ((aesKs0 w nk).kx (8 * y + b)) ((aesKeyAt ρ l nk ⟨y, hy⟩).toBitVec.getLsbD b) := by
    intro y hy b hb
    change AesHolds _ ρ l _ (128 + (8 * y + b)) ((aesByteAt ρ 128 l y).toBitVec.getLsbD b)
    rw [aesByteAt_getLsbD _ _ _ _ _ hb, ← Nat.add_assoc]
    exact aesHolds_input ρ l hg0 _ (by unfold aesEncN; omega)
  obtain ⟨hgK, hEK, -, hK⟩ := aesKsRun_spec hl nk (aesEncN nk) hnk (aesKeyAt ρ l nk)
    (aesKs0 w nk) hg0 hones hkey
  have hrk : ∀ r (hr : r < nk + 7), ∀ p < 128, AesHolds (aesEncN nk) ρ l (aesEncKs w nk).st
      ((aesEncKs w nk).kx (128 * r + p))
      ((aesSb (AES.roundKey (AES.keyExpansionVec nk (aesKeyAt ρ l nk)).get ⟨r, hr⟩) (p / 8)
        ).toBitVec.getLsbD (p % 8)) := by
    intro r hr p hp
    have h := hK (16 * r + p / 8) (by omega) (p % 8) (by omega)
    rw [show 8 * (16 * r + p / 8) + p % 8 = 128 * r + p by omega] at h
    simpa [aesSb, show p / 8 < 16 by omega, AES.roundKey, AES.keyExpansion, aesEncKs] using h
  have hblk : ∀ p < 128, AesHolds (aesEncN nk) ρ l (aesEncKs w nk).st p
      ((aesSb (aesUnpack ρ 0 l) (p / 8)).toBitVec.getLsbD (p % 8)) := by
    intro p hp
    have h := aesHolds_input ρ l hgK p (by unfold aesEncN; omega)
    simpa [aesSb, show p / 8 < 16 by omega, aesUnpack,
      aesByteAt_getLsbD _ _ _ _ _ (show p % 8 < 8 by omega),
      show 8 * (p / 8) + p % 8 = p by omega, aesEncKs] using h
  unfold AES.encrypt AES.encryptVec aesEncB
  dsimp only
  refine (fun h => ⟨h.1, h.2.2⟩) (aesRoundStepB_inv hl true _ (s0 := (aesEncKs w nk).st) hgK
    ?_ _ (hrk (nk + 6) (by omega)))
  apply aes_fin_foldl_inv2 (fun _ v a => AesEncInv (aesEncN nk) ρ l (aesEncKs w nk).st v a)
  · refine aesArkB_inv hl _ hgK _ _ hblk fun p hp => ?_
    have h := hrk 0 (by omega) p hp
    rw [Nat.mul_zero, Nat.zero_add] at h
    exact h
  · intro r v a hQ
    exact aesRoundStepB_inv hl false _ hgK hQ _ (hrk (r.val + 1) (by omega))

/-! ## 3. The program -/

/-- The input context of the cipher: the input array of the 128 state planes and the `32 nk`
    key planes, and the output array of the 128 planes of the ciphertexts. -/
abbrev aesEncCtxt (w nk : Nat) : Ctxt jasminDialect :=
  [.stackArr w (aesEncN nk), .stackArr w 128]

/-- The let-bound word expressions of the cipher, binding the words from `aesEncN nk`. -/
def aesEncLets (w nk : Nat) : List (WExp w) := (aesEncB w nk).st.rev.reverse

/-- The stores of the ciphertext planes: the word of plane `p` at the index `p`. -/
def aesEncStores (w nk : Nat) : List (Nat × Nat) :=
  (List.range 128).map fun p => (p, (aesEncB w nk).sw p)

/-- **The bitsliced AES cipher as a `jasminDialect` program** for a key of `nk` words: the
    loads of the input array as the words numbered `0, …, aesEncN nk - 1`, the compiled
    let-list of the cipher, and the stores of the 128 ciphertext planes into the output array
    at register indices. -/
def aesEncBody (w nk : Nat) : Com jasminDialect (aesEncCtxt w nk) (.stackArr w 128) :=
  genLoad Var.here 0 fun ρ0 v0 =>
  genLoads (List.range' 1 (aesEncN nk - 1)) (ρ0 _ .here) 1 (fun _ => v0) fun ρ1 env1 =>
  genLetsR (aesEncLets w nk) (aesEncN nk) env1 fun ρ2 env2 =>
  genStoresIdx (aesEncStores w nk) (ρ2 _ (ρ1 _ (ρ0 _ (.there .here)))) env2

/-! ## 4. Values and events -/

/-- The stores of the words `h p` at the indices `p < 128`. -/
theorem aesStoresMap_foldl {w : Nat} (h : Nat → Nat) (g : Nat → BitVec w)
    (O : Fin 128 → BitVec w) :
    ((List.range 128).map fun p => (p, h p)).foldl (fun A q => stackSet A q.1 (g q.2)) O =
      fun p => g (h p.val) := by
  have key : ∀ m ≤ 128, ((List.range m).map fun p => (p, h p)).foldl
      (fun A q => stackSet A q.1 (g q.2)) O =
        fun p : Fin 128 => if p.val < m then g (h p.val) else O p := by
    intro m
    induction m with
    | zero => intro _; funext p; simp
    | succ m ih =>
        intro hm
        rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
        simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
        rw [show m = (⟨m, by omega⟩ : Fin 128).val from rfl, stackSet_fin]
        funext p
        by_cases hp : p = ⟨m, by omega⟩
        · subst hp; simp
        · have : p.val ≠ m := fun h' => hp (Fin.ext h')
          simp only [hp, ite_false]
          grind
  rw [key 128 le_rfl]
  funext p
  simp

/-- **The value of the bitsliced AES cipher**: at the input array `S` of the state planes and
    the key planes and any contents `O` of the output array, the program returns the planes of
    `AES.encrypt nk` of each of the `w` blocks under the key of its lane. -/
theorem aesEncBody_value (w nk : Nat) (hnk : 0 < nk) (hN : aesEncN nk ≤ 2 ^ 64)
    (S : Fin (aesEncN nk) → BitVec w) (O : Fin 128 → BitVec w) :
    (aesEncBody w nk).denote (.cons S (.cons O .nil)) =
      aesPack w fun j =>
        AES.encrypt nk (aesKeyAt (stackGet S) j nk) (aesUnpack (stackGet S) 0 j) := by
  have hL : ∀ q ∈ aesEncStores w nk, q.1 < 2 ^ 64 := by
    intro q hq
    simp only [aesEncStores, List.mem_map, List.mem_range] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    simp only
    omega
  unfold aesEncBody
  refine genLoad_denote _ 0 _ _ S rfl _ fun ρ0 V0 v0 hρ0 hv0 => ?_
  refine genLoads_denote _ _ 1 _ _ V0 S (hρ0 _ _) (fun _ => stackGet S (BitVec.ofNat 64 0).toNat)
    (fun _ => hv0) _ fun ρ1 V1 env1 hρ1 henv1 => ?_
  refine genLetsR_denote _ _ env1 _ V1 _ henv1 _ fun ρ2 V2 env2 hρ2 henv2 => ?_
  refine (genStoresIdx_denote _ (ρ2 _ (ρ1 _ (ρ0 _ (.there .here)))) env2 V2 O
    ((hρ2 _ _).trans ((hρ1 _ _).trans (hρ0 _ _))) _ henv2 hL).trans ?_
  rw [aesEncStores, aesStoresMap_foldl]
  set ρ := loadVals S (fun _ => stackGet S (BitVec.ofNat 64 0).toNat) 1
    (List.range' 1 (aesEncN nk - 1)) with hρdef
  have hagree : ∀ i < aesEncN nk, ρ i = stackGet S i := by
    intro i hi
    rw [hρdef, loadVals_apply]
    by_cases h0 : i = 0
    · subst h0
      rw [ite_eq_right (by omega)]
      simp
    · rw [ite_eq_left (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
        List.getElem_range', show 1 + 1 * (i - 1) = i by omega, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
  have hbyte : ∀ off j k, off + 8 * k + 8 ≤ aesEncN nk →
      aesByteAt ρ off j k = aesByteAt (stackGet S) off j k := by
    intro off j k hk
    simp only [aesByteAt]
    exact congrArg UInt8.ofBitVec
      (aesLanes_congr 8 _ _ fun b hb => by rw [hagree _ (by omega)])
  have hun : ∀ j, aesUnpack ρ 0 j = aesUnpack (stackGet S) 0 j := by
    intro j
    funext k
    exact hbyte 0 j k.val (by unfold aesEncN; omega)
  have hkey : ∀ j, aesKeyAt ρ j nk = aesKeyAt (stackGet S) j nk := by
    intro j
    funext k
    exact hbyte 128 j k.val (by unfold aesEncN; omega)
  funext p
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ((aesEncB_spec (ρ := ρ) hj nk hnk).2 p.val p.isLt).2
  unfold aesLane LetSt.val at h
  rw [aesPack, aesLanes_getLsbD _ _ _ hj, ← hun j, ← hkey j]
  rw [aesEncLets] at *
  simpa [aesSb, show p.val / 8 < 16 by omega] using h

/-- **The value of the bitsliced AES-128 cipher**: in every lane, the planes of `AES.aes128`
    at that lane's key and block. -/
theorem aesEncBody_value_aes128 (w : Nat) (S : Fin (aesEncN 4) → BitVec w)
    (O : Fin 128 → BitVec w) :
    (aesEncBody w 4).denote (.cons S (.cons O .nil)) =
      aesPack w fun j => AES.aes128 (aesKeyAt (stackGet S) j 4) (aesUnpack (stackGet S) 0 j) :=
  aesEncBody_value w 4 (by decide) (by simp [aesEncN]) S O

/-- **The value of the bitsliced AES-192 cipher**: in every lane, the planes of `AES.aes192`
    at that lane's key and block. -/
theorem aesEncBody_value_aes192 (w : Nat) (S : Fin (aesEncN 6) → BitVec w)
    (O : Fin 128 → BitVec w) :
    (aesEncBody w 6).denote (.cons S (.cons O .nil)) =
      aesPack w fun j => AES.aes192 (aesKeyAt (stackGet S) j 6) (aesUnpack (stackGet S) 0 j) :=
  aesEncBody_value w 6 (by decide) (by simp [aesEncN]) S O

/-- **The value of the bitsliced AES-256 cipher**: in every lane, the planes of `AES.aes256`
    at that lane's key and block. -/
theorem aesEncBody_value_aes256 (w : Nat) (S : Fin (aesEncN 8) → BitVec w)
    (O : Fin 128 → BitVec w) :
    (aesEncBody w 8).denote (.cons S (.cons O .nil)) =
      aesPack w fun j => AES.aes256 (aesKeyAt (stackGet S) j 8) (aesUnpack (stackGet S) 0 j) :=
  aesEncBody_value w 8 (by decide) (by simp [aesEncN]) S O

/-- **The events of the bitsliced AES cipher are fixed**: at leakage parameters with no
    variable-time operation, the program emits the same events at every two valuations. -/
theorem aesEncBody_events (Pj : JLeakParams) (hV : ∀ op, Pj.opVT op = none) (w nk : Nat) :
    LeakFixed (jLeakModel Pj) (aesEncBody w nk) := by
  unfold aesEncBody
  exact genLoad_fixed Pj hV _ _ _ fun _ _ => genLoads_fixed Pj hV _ _ _ _ _ fun _ _ =>
    genLetsR_fixed Pj hV _ _ _ _ fun _ _ => genStoresIdx_fixed Pj hV _ _ _

end CatCrypt.Crypto.SecureCompilation.HashTemplate
