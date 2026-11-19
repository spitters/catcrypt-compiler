/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
public import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveLoweringJacobian
public import CatCrypt.Crypto.SecureCompilation.MontgomeryLadderGeneric
public import CatCrypt.Crypto.SecureCompilation.VIR.NFProgJasmin

/-!
# The Montgomery ladder as a template over a field record

The X25519 Montgomery ladder (RFC 7748 §5) as straight-line `jasminDialect` kernels generated
from a field record `lo : LimbBlocks n` (the per-operation blocks that `fieldComOf` lowers
through; instances at Solinas, Montgomery and unsaturated limbs), in the manner of fiat-crypto's
ladder over its synthesised field functions. The kernels act on one word array holding the
ladder state `(u, x2, z2, x3, z3, t)`, six field elements of `n` limbs each; the field
operations are the blocks of the record, inlined, and the conditional swap by a secret bit is
word code (`m = 0 - b`, `d = m & (x ^ y)`, `x ^= d`, `y ^= d`).

| kernel | context | value |
|---|---|---|
| `initBody` | `u` (`n` words), out (`6n`) | `initF u = (u, 1, 0, u, 1, 1)` |
| `stepBody` | state (`6n`), bit word, out (`6n`) | `ladderStepF a24 b`: swap, add, swap |
| `sqBody` | state, out | `sqF`: `t ← t²` |
| `sqmBody` | state, out | `sqmF`: `t ← t² · z2` |
| `finBody` | state, out (`n` words) | `finF = x2 · t` |

## Main definitions

* `LadderState`, `cswapF`, `daddF`, `ladderStepF`, `initF`, `sqF`, `sqmF`, `finF`: the ladder
  over `ZMod p`; `daddF` is the double-and-add of RFC 7748 with the constant `a24`
  (`121665` for Curve25519), operation for operation as `feDoubleAndAdd`.
* `encW`: the state encoding, the limbs of the six elements in one array of `6n` words.
* `storeLimbsK`, `storeChunks`, `storeHoms`: stores of limb registers with a continuation.
* `cswapLimbs`: the word-mask conditional swap of two limb vectors.
* `daddProg`, `sqProg`, `sqmProg`, `finProg`, `initProg`: the field programs of the kernels.
* `initBody`, `stepBody`, `sqBody`, `sqmBody`, `finBody`: the kernel bodies over `lo`.
* `mselK`, `maskK`, `ldK`, `wordSelK`, `scalarBitK`: the scalar bit of an iteration read
  without a computed index: the four scalar words loaded at literal indices, word
  `(254 - i) >> 6` selected by the word masks of its two bits (`sel4W`), then shifted. A shift
  by a constant (`shrConstK`) is the immediate shift `shrImm`, and no instruction by `0`.
* `ladderThen`, `ladderLoopBody`: over the packed input `[k; u]`, `bitStepAt` (the scalar
  bit `scalarBitAt` by `scalarBitK`, then `stepBodyAt`) in a counted loop of `255`
  iterations on the carried state array, with a continuation or as a kernel.
* `Slot`, `FOp`, `ChainOp`, `chainF`, `invChain`: chains of squarings and products between
  the slots of the state; `invChain` is the ref10 / fiat-crypto chain of `z2 ^ (2^255 - 21)`
  (`254` squarings, `11` products).
* `chainThen`: a chain on the state array, each field operation a straight-line block of
  `lo` and each run of squarings a counted loop of `sqBodyAt` with a literal trip count.
* `x25519Body`: one kernel over `[k; u]`, a state array and an output array of `n` words:
  the ladder loop, the inversion chain of `z2`, and `x2 · t` into the output array.

## Main results

* `daddF_eq_xDouble_xDiffAdd`: the double-and-add is `xDouble` and `xDiffAdd` of
  `MontgomeryLadderGeneric`, at the constant `a24 + 1`.
* `initBody_value`, `stepBody_value`, `sqBody_value`, `sqmBody_value`, `finBody_value`: for
  every record `lo` with a block square at an encoding `enc`, every predicate `Good` that
  holds of the operations used and every `a24`, each body maps the array `encW s` to
  `encW (f s)` for its `ZMod p` function `f`, whatever the output array held on entry
  (`initBody` maps the `n` limbs of `u`, `finBody` returns the `n` limbs of `x2 · t`).
* `ladderLoopBody_value`: at a packed input whose words from index `4` are the limbs of `u`,
  the loop kernel returns the encoding of the fold of `ladderStepF` over the `255` bits
  `scalarBitAt K i` from `initF u`.
* `chainF_invChain`: `invChain` keeps `x2` and computes `z2 ^ (2^255 - 21)` into `t`;
  `pow_invExp_eq_inv`: at the prime `p = 2^255 - 19` this power is `z2⁻¹`.
* `chainThen_denote`: a chain on an array holding `encW s` gives `encW (chainF ops s)`.
* `x25519Body_value`, `x25519Body_value_inv`: the X25519 kernel returns the `n` limbs of
  `x2 · z2 ^ (2^255 - 21)` of the ladder state `ladderOut a24 K u`, which is `x2 · z2⁻¹` at
  the prime `2^255 - 19`.
* `scalarBitAt_eq_testBit`: for `i ≤ 254`, `scalarBitAt K i` is bit `(254 - i) % 64` of word
  `(254 - i) / 64` of `K`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CurveTemplate.MontLadder

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.BlockLoweringCPS
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (w64 MC lk bindK
  bindK_denote eBin eBin_denote Pres Pres.id Pres.comp)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 renaming eConst → wConst
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (Rn)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect.JacLower (vAt eAdd eSub eMul eSq)
open CatCrypt.Crypto.SecureCompilation.MontgomeryLadderGeneric (xDouble xDiffAdd)

/-! ## 1. The ladder over `ZMod p` -/

/-- The state of the ladder: the base coordinate `u`, the two projective points `(x2 : z2)`,
    `(x3 : z3)`, and the accumulator `t` of the inversion. -/
structure LadderState (p : Nat) where
  /-- The base coordinate. -/
  u : ZMod p
  /-- The `X` coordinate of the first point. -/
  x2 : ZMod p
  /-- The `Z` coordinate of the first point. -/
  z2 : ZMod p
  /-- The `X` coordinate of the second point. -/
  x3 : ZMod p
  /-- The `Z` coordinate of the second point. -/
  z3 : ZMod p
  /-- The accumulator of the inversion. -/
  t : ZMod p

variable {p : Nat}

/-- The conditional swap of the two points by the bit `b`. -/
def cswapF (b : Bool) (s : LadderState p) : LadderState p :=
  if b then { s with x2 := s.x3, z2 := s.z3, x3 := s.x2, z3 := s.z2 } else s

/-- The double-and-add of RFC 7748 §5 with the constant `a24`: `(x2 : z2)` is doubled and
    `(x3 : z3)` becomes the sum of the two points, whose difference has the coordinate `u`. -/
def daddF (a24 : ZMod p) (s : LadderState p) : LadderState p :=
  let a := s.x2 + s.z2
  let b := s.x2 - s.z2
  let aa := a * a
  let bb := b * b
  let e := aa - bb
  let c := s.x3 + s.z3
  let d := s.x3 - s.z3
  let da := d * a
  let cb := c * b
  { s with
    x2 := aa * bb
    z2 := e * (aa + a24 * e)
    x3 := (da + cb) * (da + cb)
    z3 := s.u * ((da - cb) * (da - cb)) }

/-- One step of the ladder at the bit `b`: swap, double-and-add, swap back. -/
def ladderStepF (a24 : ZMod p) (b : Bool) (s : LadderState p) : LadderState p :=
  cswapF b (daddF a24 (cswapF b s))

/-- The initial state at the base coordinate `u`: the points `(1 : 0)` and `(u : 1)`, and the
    accumulator `1`. -/
def initF (u : ZMod p) : LadderState p := ⟨u, 1, 0, u, 1, 1⟩

/-- One squaring of the accumulator. -/
def sqF (s : LadderState p) : LadderState p := { s with t := s.t * s.t }

/-- One squaring of the accumulator followed by a product with `z2`. -/
def sqmF (s : LadderState p) : LadderState p := { s with t := s.t * s.t * s.z2 }

/-- The output `x2 · t`. -/
def finF (s : LadderState p) : ZMod p := s.x2 * s.t

/-- **The double-and-add is the x-only doubling and differential addition** of
    `MontgomeryLadderGeneric` at the constant `a24 + 1`: the first point is doubled, and the
    second is the sum of the two points with difference `(u : 1)`. -/
theorem daddF_eq_xDouble_xDiffAdd [Fact p.Prime] (a24 : ZMod p) (s : LadderState p) :
    ((daddF a24 s).x2, (daddF a24 s).z2) = xDouble (a24 + 1) s.x2 s.z2 ∧
      ((daddF a24 s).x3, (daddF a24 s).z3) = xDiffAdd s.x3 s.z3 s.x2 s.z2 s.u 1 := by
  simp only [daddF, xDouble, xDiffAdd, Prod.mk.injEq]
  refine ⟨⟨by ring, by ring⟩, by ring, by ring⟩

/-! ## 2. Stores with a continuation, and the state encoding -/

section Stores

variable {N : Nat}

/-- The stores of the limbs `h` into the array `o` from index `j`; the continuation receives
    the renaming of the context and the stored array. -/
def storeLimbsK {bs : List JasminTy} : {Δ : Ctxt jasminDialect} → (m j : Nat) →
    Var Δ (arrTy N) → Ctxt.Hom (Rn m) Δ →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Var Δ' (arrTy N) → MC Δ' bs) → MC Δ bs
  | _, 0, _, o, _, k => k (fun v => v) o
  | _, m + 1, j, o, h, k =>
      bindK (wConst j) fun r₁ i =>
      bindK (eStore (r₁ o) i (r₁ (h .here))) fun r₂ o' =>
      storeLimbsK m (j + 1) o' (fun w => r₂ (r₁ (h (.there w)))) fun r₃ o'' =>
        k (fun v => r₃ (r₂ (r₁ v))) o''

/-- The stores of `storeLimbsK` write the limbs `h` into `o` from index `j` (`storeVal`). -/
theorem storeLimbsK_denote {bs : List JasminTy} (hN : N < 2 ^ 64) :
    ∀ {Δ : Ctxt jasminDialect} (m j : Nat) (o : Var Δ (arrTy N)) (h : Ctxt.Hom (Rn m) Δ)
      (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Var Δ' (arrTy N) → MC Δ' bs)
      (W : Valuation Δ) (G : ListDenote bs), j + m ≤ N →
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (o' : Var Δ' (arrTy N))
          (W' : Valuation Δ'), Pres r W W' →
          o'.lookup W' = storeVal (o.lookup W) j (pullV h W) → (k r o').denote W' = G) →
      (storeLimbsK m j o h k).denote W = G
  | _, 0, _, o, _, _, W, _, _, hk => hk (fun v => v) o W (Pres.id W) rfl
  | _, m + 1, j, o, h, k, W, G, hjm, hk => by
      refine bindK_denote _ _ W G fun r₁ i W₁ h₁ hi => ?_
      refine bindK_denote _ _ W₁ G fun r₂ o' W₂ h₂ ho => ?_
      refine storeLimbsK_denote hN m (j + 1) o' _ _ W₂ G (by omega)
        fun r₃ o'' W₃ h₃ ho'' => hk _ o'' W₃ (Pres.comp (Pres.comp h₁ h₂) h₃) ?_
      have e : (eStore (r₁ o) i (r₁ (h .here))).denote W₁
          = stackSet ((r₁ o).lookup W₁) (i.lookup W₁).toNat ((r₁ (h .here)).lookup W₁) := rfl
      have e₀ : (i.lookup W₁).toNat = j := by
        rw [hi]
        exact (BitVec.toNat_ofNat j 64).trans (Nat.mod_eq_of_lt (by omega))
      rw [ho'', ho, e, e₀, h₁ o, h₁ (h .here),
        pullV_comp_pres h₂ (fun w => r₁ (h (.there w))),
        pullV_comp_pres h₁ (fun w => h (.there w))]
      rfl

/-- The array `o` with the chunks `Ls` of `n` words written from index `j` on. -/
def storeChunks (n : Nat) (o : Fin N → BitVec 64) (j : Nat) :
    List (ListDenote (Rn n)) → Fin N → BitVec 64
  | [] => o
  | L :: Ls => storeChunks n (storeVal o j L) (j + n) Ls

/-- A word written at an index is read back at that index. -/
theorem stackGet_stackSet_self (o : Fin N → BitVec 64) (j : Nat) (x : BitVec 64)
    (hj : j < N) : stackGet (stackSet o j x) j = x := by
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  simp only [stackGet, stackSet, ite_true]

/-- The words written by `storeVal` do not depend on the array written to. -/
theorem storeVal_get_indep (i : Nat) :
    ∀ {m : Nat} (j : Nat) (L : ListDenote (Rn m)) (o o' : Fin N → BitVec 64), j ≤ i →
      i < j + m → j + m ≤ N → stackGet (storeVal o j L) i = stackGet (storeVal o' j L) i
  | 0, _, _, _, _, _, _, _ => by omega
  | m + 1, j, .cons x L, o, o', hji, him, hjm => by
      change stackGet (storeVal (stackSet o j x) (j + 1) L) i
        = stackGet (storeVal (stackSet o' j x) (j + 1) L) i
      rcases Nat.eq_or_lt_of_le hji with rfl | hlt
      · rw [storeVal_get_lt _ _ _ L (by omega) (by omega),
          storeVal_get_lt _ _ _ L (by omega) (by omega),
          stackGet_stackSet_self _ _ _ (by omega), stackGet_stackSet_self _ _ _ (by omega)]
      · exact storeVal_get_indep i (j + 1) L _ _ (by omega) (by omega) (by omega)

/-- Arrays that agree on `m` words from index `j` have the same limbs there. -/
theorem arrLimbs_congr (A B : Fin N → BitVec 64) :
    ∀ (m j : Nat), (∀ i, j ≤ i → i < j + m → stackGet A i = stackGet B i) →
      arrLimbs A m j = arrLimbs B m j
  | 0, _, _ => rfl
  | m + 1, j, h => by
      change (HVector.cons (stackGet A j) (arrLimbs A m (j + 1)) : ListDenote (Rn (m + 1)))
        = (HVector.cons (stackGet B j) (arrLimbs B m (j + 1)) : ListDenote (Rn (m + 1)))
      rw [h j (by omega) (by omega),
        arrLimbs_congr A B m (j + 1) fun i h₁ h₂ => h i (by omega) (by omega)]

/-- The words below the first written index keep their value. -/
theorem storeChunks_get_lt (n i : Nat) :
    ∀ (Ls : List (ListDenote (Rn n))) (o : Fin N → BitVec 64) (j : Nat), i < j →
      j + n * Ls.length ≤ N → stackGet (storeChunks n o j Ls) i = stackGet o i
  | [], _, _, _, _ => rfl
  | L :: Ls, o, j, hij, hjN => by
      have hl : n * (L :: Ls).length = n + n * Ls.length := by
        simp only [List.length_cons, Nat.mul_succ]; omega
      change stackGet (storeChunks n (storeVal o j L) (j + n) Ls) i = _
      rw [storeChunks_get_lt n i Ls _ (j + n) (by omega) (by omega)]
      exact storeVal_get_lt o i j L hij (by omega)

/-- The written words do not depend on the array written to. -/
theorem storeChunks_get_indep (n i : Nat) :
    ∀ (Ls : List (ListDenote (Rn n))) (o o' : Fin N → BitVec 64) (j : Nat), j ≤ i →
      i < j + n * Ls.length → j + n * Ls.length ≤ N →
      stackGet (storeChunks n o j Ls) i = stackGet (storeChunks n o' j Ls) i
  | [], _, _, _, _, h, _ => by simp at h; omega
  | L :: Ls, o, o', j, hji, hiL, hjN => by
      have hl : n * (L :: Ls).length = n + n * Ls.length := by
        simp only [List.length_cons, Nat.mul_succ]; omega
      change stackGet (storeChunks n (storeVal o j L) (j + n) Ls) i
        = stackGet (storeChunks n (storeVal o' j L) (j + n) Ls) i
      by_cases hin : i < j + n
      · rw [storeChunks_get_lt n i Ls _ (j + n) hin (by omega),
          storeChunks_get_lt n i Ls _ (j + n) hin (by omega)]
        exact storeVal_get_indep i j L o o' hji hin (by omega)
      · exact storeChunks_get_indep n i Ls _ _ (j + n) (by omega) (by omega) (by omega)

/-- **Chunks that fill the array determine it**: the stored array does not depend on the
    array written to. -/
theorem storeChunks_full (n : Nat) (Ls : List (ListDenote (Rn n))) (o o' : Fin N → BitVec 64)
    (hN : n * Ls.length = N) : storeChunks n o 0 Ls = storeChunks n o' 0 Ls := by
  funext k
  rw [← stackGet_id (storeChunks n o 0 Ls) k, ← stackGet_id (storeChunks n o' 0 Ls) k]
  exact storeChunks_get_indep n k Ls o o' 0 (Nat.zero_le _) (by omega) (by omega)

/-- The chunk `k` of the stored array is the `k`-th chunk written. -/
theorem arrLimbs_storeChunks (n : Nat) :
    ∀ (Ls : List (ListDenote (Rn n))) (o : Fin N → BitVec 64) (j k i : Nat)
      (hk : k < Ls.length), i = j + k * n → j + n * Ls.length ≤ N →
      arrLimbs (storeChunks n o j Ls) n i = Ls[k]
  | [], _, _, _, _, hk, _, _ => by simp at hk
  | L :: Ls, o, j, 0, i, _, hi, hjN => by
      have hl : n * (L :: Ls).length = n + n * Ls.length := by
        simp only [List.length_cons, Nat.mul_succ]; omega
      subst hi
      change arrLimbs (storeChunks n (storeVal o j L) (j + n) Ls) n (j + 0 * n) = L
      rw [Nat.zero_mul, Nat.add_zero,
        arrLimbs_congr _ (storeVal o j L) n j fun i _ h₂ =>
          storeChunks_get_lt n i Ls _ (j + n) h₂ (by omega)]
      exact arrLimbs_storeVal o j L (by omega)
  | L :: Ls, o, j, k + 1, i, hk, hi, hjN => by
      have hl : n * (L :: Ls).length = n + n * Ls.length := by
        simp only [List.length_cons, Nat.mul_succ]; omega
      exact arrLimbs_storeChunks n Ls (storeVal o j L) (j + n) k i
        (by simp at hk; omega) (by rw [hi, Nat.succ_mul]; omega) (by omega)

/-- A limb vector: a renaming of `Rn n` onto `n` word variables of `Δ`. -/
structure LimbVec (n : Nat) (Δ : Ctxt jasminDialect) where
  /-- The renaming. -/
  hom : Ctxt.Hom (Rn n) Δ

/-- The stores of the limb vectors `hs`, renamed by `ρ`, into the array `o` from index `j`,
    chunk after chunk, returning the last array. -/
def storeHoms {n : Nat} {Δ₀ : Ctxt jasminDialect} : {Δ : Ctxt jasminDialect} → (j : Nat) →
    Ctxt.Hom Δ₀ Δ → Var Δ (arrTy N) → List (LimbVec n Δ₀) → MC Δ [arrTy N]
  | _, _, _, o, [] => .ret (.cons o .nil)
  | _, j, ρ, o, h :: hs =>
      storeLimbsK n j o (fun w => ρ (h.hom w)) fun r o' =>
        storeHoms (j + n) (fun v => r (ρ v)) o' hs

/-- The stores of `storeHoms` write the chunks of the limb vectors (`storeChunks`). -/
theorem storeHoms_denote {n : Nat} {Δ₀ : Ctxt jasminDialect} (hN : N < 2 ^ 64) :
    ∀ (hs : List (LimbVec n Δ₀)) {Δ : Ctxt jasminDialect} (j : Nat)
      (ρ : Ctxt.Hom Δ₀ Δ) (o : Var Δ (arrTy N)) (W : Valuation Δ),
      j + n * hs.length ≤ N →
      (storeHoms j ρ o hs).denote W
        = .cons (storeChunks n (o.lookup W) j
            (hs.map fun h => pullV (fun w => ρ (h.hom w)) W)) .nil
  | [], _, _, _, _, _, _ => rfl
  | h :: hs, _, j, ρ, o, W, hjN => by
      have hl : n * (h :: hs).length = n + n * hs.length := by
        simp only [List.length_cons, Nat.mul_succ]; omega
      refine storeLimbsK_denote hN n j o _ _ W _ (by omega) fun r o' W' hr ho' => ?_
      rw [storeHoms_denote hN hs (j + n) _ o' W' (by omega), ho']
      simp only [List.map_cons]
      rw [List.map_congr_left fun (h' : LimbVec n Δ₀) _ =>
        pullV_comp_pres hr (fun w => ρ (h'.hom w))]
      rfl

end Stores

/-- **The state encoding**: the limbs `E` of `u, x2, z2, x3, z3, t`, in this order, in one
    array of `6n` words. -/
def encW {n : Nat} (E : ZMod p → ListDenote (Rn n)) (s : LadderState p) :
    Fin (6 * n) → BitVec 64 :=
  storeChunks n (fun _ => 0) 0 [E s.u, E s.x2, E s.z2, E s.x3, E s.z3, E s.t]

/-! ## 3. The conditional swap -/

/-- The swap mask of the bit `b`: all ones at `true`, zero at `false`. -/
def maskW (b : Bool) : BitVec 64 := 0 - BitVec.ofNat 64 b.toNat

/-- The masked swap of one word, first output. -/
theorem cswap_word_fst (b : Bool) (x y : BitVec 64) :
    x ^^^ (maskW b &&& (x ^^^ y)) = if b then y else x := by
  cases b
  · simp [maskW]
  · rw [show maskW true = BitVec.allOnes 64 from rfl, BitVec.allOnes_and, ← BitVec.xor_assoc,
      BitVec.xor_self, BitVec.zero_xor]
    rfl

/-- The masked swap of one word, second output. -/
theorem cswap_word_snd (b : Bool) (x y : BitVec 64) :
    y ^^^ (maskW b &&& (x ^^^ y)) = if b then x else y := by
  cases b
  · simp [maskW]
  · rw [show maskW true = BitVec.allOnes 64 from rfl, BitVec.allOnes_and, BitVec.xor_comm x y,
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    rfl

/-- The word-mask conditional swap of the limb vectors `hx`, `hy` by the mask `c`, limb by
    limb: `d = c & (x ^ y)`, `x' = x ^ d`, `y' = y ^ d`; the continuation receives the
    renaming of the context and the two new limb vectors. -/
def cswapLimbs {bs : List JasminTy} : {Δ : Ctxt jasminDialect} → (m : Nat) → Var Δ w64 →
    Ctxt.Hom (Rn m) Δ → Ctxt.Hom (Rn m) Δ →
    (∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Hom (Rn m) Δ' → Ctxt.Hom (Rn m) Δ' →
      MC Δ' bs) → MC Δ bs
  | _, 0, _, hx, hy, k => k (fun v => v) hx hy
  | _, m + 1, c, hx, hy, k =>
      bindK (eBin .xor (hx .here) (hy .here)) fun r₁ e =>
      bindK (eBin .and (r₁ c) e) fun r₂ d =>
      bindK (eBin .xor (r₂ (r₁ (hx .here))) d) fun r₃ x' =>
      bindK (eBin .xor (r₃ (r₂ (r₁ (hy .here)))) (r₃ d)) fun r₄ y' =>
      cswapLimbs m (r₄ (r₃ (r₂ (r₁ c)))) (fun w => r₄ (r₃ (r₂ (r₁ (hx (.there w))))))
        (fun w => r₄ (r₃ (r₂ (r₁ (hy (.there w)))))) fun r₅ hx' hy' =>
        k (fun v => r₅ (r₄ (r₃ (r₂ (r₁ v))))) (consHom (r₅ (r₄ x')) hx') (consHom (r₅ y') hy')

/-- At the mask `maskW b`, `cswapLimbs` swaps the two limb vectors when `b` holds and keeps
    them otherwise. -/
theorem cswapLimbs_denote {bs : List JasminTy} (b : Bool) :
    ∀ {Δ : Ctxt jasminDialect} (m : Nat) (c : Var Δ w64) (hx hy : Ctxt.Hom (Rn m) Δ)
      (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Hom (Rn m) Δ' →
        Ctxt.Hom (Rn m) Δ' → MC Δ' bs)
      (W : Valuation Δ) (G : ListDenote bs), c.lookup W = maskW b →
      (∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (hx' hy' : Ctxt.Hom (Rn m) Δ')
          (W' : Valuation Δ'), Pres r W W' →
          pullV hx' W' = (if b then pullV hy W else pullV hx W) →
          pullV hy' W' = (if b then pullV hx W else pullV hy W) → (k r hx' hy').denote W' = G) →
      (cswapLimbs m c hx hy k).denote W = G
  | _, 0, _, hx, hy, _, W, _, _, hk => hk (fun v => v) hx hy W (Pres.id W)
      (by cases b <;> rfl) (by cases b <;> rfl)
  | _, m + 1, c, hx, hy, k, W, G, hc, hk => by
      refine bindK_denote _ _ W G fun r₁ e W₁ h₁ he => ?_
      refine bindK_denote _ _ W₁ G fun r₂ d W₂ h₂ hd => ?_
      refine bindK_denote _ _ W₂ G fun r₃ x' W₃ h₃ hx'v => ?_
      refine bindK_denote _ _ W₃ G fun r₄ y' W₄ h₄ hy'v => ?_
      have h₁₄ : Pres (fun v => r₄ (r₃ (r₂ (r₁ v)))) W W₄ :=
        Pres.comp (Pres.comp (Pres.comp h₁ h₂) h₃) h₄
      have hd' : lk d W₂ = maskW b &&& (lk (hx .here) W ^^^ lk (hy .here) W) :=
        hd.trans (congrArg₂ (fun a b : BitVec 64 => a &&& b) ((h₁ c).trans hc) he)
      have e2 : pullV (fun w => r₄ (r₃ (r₂ (r₁ (hx (.there w)))))) W₄
          = pullV (fun w => hx (.there w)) W := pullV_comp_pres h₁₄ (fun w => hx (.there w))
      have e3 : pullV (fun w => r₄ (r₃ (r₂ (r₁ (hy (.there w)))))) W₄
          = pullV (fun w => hy (.there w)) W := pullV_comp_pres h₁₄ (fun w => hy (.there w))
      refine cswapLimbs_denote b m _ _ _ _ W₄ G ((h₁₄ c).trans hc)
        fun r₅ hx' hy' W₅ h₅ hhx hhy => hk _ _ _ W₅ (Pres.comp h₁₄ h₅) ?_ ?_
      · have ex : lk (r₅ (r₄ x')) W₅ = lk (hx .here) W ^^^ (maskW b &&&
            (lk (hx .here) W ^^^ lk (hy .here) W)) :=
          (h₅ _).trans ((h₄ _).trans (hx'v.trans
            (congrArg₂ (fun a b : BitVec 64 => a ^^^ b) ((h₂ _).trans (h₁ _)) hd')))
        change (HVector.cons (lk (r₅ (r₄ x')) W₅) (pullV hx' W₅) : ListDenote (Rn (m + 1))) = _
        rw [ex, cswap_word_fst, hhx]
        cases b
        · exact congrArg (HVector.cons _) e2
        · exact congrArg (HVector.cons _) e3
      · have ey : lk (r₅ y') W₅ = lk (hy .here) W ^^^ (maskW b &&&
            (lk (hx .here) W ^^^ lk (hy .here) W)) :=
          (h₅ _).trans (hy'v.trans (congrArg₂ (fun a b : BitVec 64 => a ^^^ b)
            ((h₃ _).trans ((h₂ _).trans (h₁ _))) ((h₃ d).trans hd')))
        change (HVector.cons (lk (r₅ y') W₅) (pullV hy' W₅) : ListDenote (Rn (m + 1))) = _
        rw [ey, cswap_word_snd, hhy]
        cases b
        · exact congrArg (HVector.cons _) e3
        · exact congrArg (HVector.cons _) e2

/-! ## 4. The field programs -/

/-- The context of `k` field elements at `p`. -/
abbrev fctx (p k : Nat) : Ctxt fieldDialect := List.replicate k (FieldTy.fp p)

/-- **The double-and-add as a field program** over `x2, z2, x3, z3, u` (the first at the
    head), returning `x2', z2', x3', z3'`: four additions or subtractions on the inputs, two
    squarings, the products `da`, `cb`, their sum squared, their difference squared times `u`,
    `aa · bb`, the constant `a24`, and `e · (aa + a24 · e)`. -/
def daddProg (p : Nat) (a24 : ZMod p) : MultiReturnCom fieldDialect (fctx p 5) (fctx p 4) :=
  .var (eAdd (vAt p 0) (vAt p 1)) <|
  .var (eSub (vAt p 1) (vAt p 2)) <|
  .var (eSq (vAt p 1)) <|
  .var (eSq (vAt p 1)) <|
  .var (eSub (vAt p 1) (vAt p 0)) <|
  .var (eAdd (vAt p 7) (vAt p 8)) <|
  .var (eSub (vAt p 8) (vAt p 9)) <|
  .var (eMul (vAt p 0) (vAt p 6)) <|
  .var (eMul (vAt p 2) (vAt p 6)) <|
  .var (eAdd (vAt p 1) (vAt p 0)) <|
  .var (eSq (vAt p 0)) <|
  .var (eSub (vAt p 3) (vAt p 2)) <|
  .var (eSq (vAt p 0)) <|
  .var (eMul (vAt p 17) (vAt p 0)) <|
  .var (eMul (vAt p 11) (vAt p 10)) <|
  .var (EllipticCurveDialect.JacLower.eConst a24) <|
  .var (eMul (vAt p 0) (vAt p 11)) <|
  .var (eAdd (vAt p 14) (vAt p 0)) <|
  .var (eMul (vAt p 13) (vAt p 0)) <|
  .ret (.cons (vAt p 4) (.cons (vAt p 0) (.cons (vAt p 8) (.cons (vAt p 5) .nil))))

/-- The valuation of `x2, z2, x3, z3, u` of a state. -/
def daddIn (s : LadderState p) : Valuation (fctx p 5) :=
  .cons s.x2 (.cons s.z2 (.cons s.x3 (.cons s.z3 (.cons s.u .nil))))

/-- The valuation of `x2, z2, x3, z3` of a state. -/
def daddOut (s : LadderState p) : Valuation (fctx p 4) :=
  .cons s.x2 (.cons s.z2 (.cons s.x3 (.cons s.z3 .nil)))

/-- The denotation of `daddProg`, computed by unfolding: the double-and-add `daddF`. -/
theorem daddProg_denote (a24 : ZMod p) (s : LadderState p) :
    (daddProg p a24).denote (daddIn s) = daddOut (daddF a24 s) := rfl

/-- The squaring of the accumulator, over `t`. -/
def sqProg (p : Nat) : MultiReturnCom fieldDialect (fctx p 1) (fctx p 1) :=
  .var (eSq (vAt p 0)) <| .ret (.cons (vAt p 0) .nil)

/-- The squaring of the accumulator and the product with `z2`, over `t, z2`. -/
def sqmProg (p : Nat) : MultiReturnCom fieldDialect (fctx p 2) (fctx p 1) :=
  .var (eSq (vAt p 0)) <| .var (eMul (vAt p 0) (vAt p 2)) <| .ret (.cons (vAt p 0) .nil)

/-- The product `x2 · t`, over `x2, t`. -/
def finProg (p : Nat) : MultiReturnCom fieldDialect (fctx p 2) (fctx p 1) :=
  .var (eMul (vAt p 0) (vAt p 1)) <| .ret (.cons (vAt p 0) .nil)

/-- The constants `1` and `0`. -/
def initProg (p : Nat) : MultiReturnCom fieldDialect [] (fctx p 2) :=
  .var (EllipticCurveDialect.JacLower.eConst 1) <|
  .var (EllipticCurveDialect.JacLower.eConst 0) <|
  .ret (.cons (vAt p 1) (.cons (vAt p 0) .nil))

/-- The denotation of `sqProg`, computed by unfolding. -/
theorem sqProg_denote (x : ZMod p) :
    (sqProg p).denote (.cons x .nil) = .cons (x * x) .nil := rfl

/-- The denotation of `sqmProg`, computed by unfolding. -/
theorem sqmProg_denote (x z : ZMod p) :
    (sqmProg p).denote (.cons x (.cons z .nil)) = .cons (x * x * z) .nil := rfl

/-- The denotation of `finProg`, computed by unfolding. -/
theorem finProg_denote (x y : ZMod p) :
    (finProg p).denote (.cons x (.cons y .nil)) = .cons (x * y) .nil := rfl

/-- The denotation of `initProg`, computed by unfolding. -/
theorem initProg_denote :
    (initProg p).denote .nil = .cons (1 : ZMod p) (.cons (0 : ZMod p) .nil) := rfl

section Coverage

variable (Good : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}, Expr fieldDialect Γ t → Prop)
  (hA : ∀ {Γ : Ctxt fieldDialect} (a b : Var Γ (FieldTy.fp p)), Good (eAdd a b))
  (hS : ∀ {Γ : Ctxt fieldDialect} (a b : Var Γ (FieldTy.fp p)), Good (eSub a b))
  (hM : ∀ {Γ : Ctxt fieldDialect} (a b : Var Γ (FieldTy.fp p)), Good (eMul a b))
  (hQ : ∀ {Γ : Ctxt fieldDialect} (a : Var Γ (FieldTy.fp p)), Good (eSq a))
  (hC : ∀ {Γ : Ctxt fieldDialect} (c : ZMod p),
    Good (EllipticCurveDialect.JacLower.eConst (Γ := Γ) c))

include hA hS hM hQ hC in
/-- Every binding of `daddProg` satisfies `Good`. -/
theorem daddProg_covered (a24 : ZMod p) : CoveredM Good (daddProg p a24) :=
  ⟨hA _ _, hS _ _, hQ _, hQ _, hS _ _, hA _ _, hS _ _, hM _ _, hM _ _, hA _ _, hQ _, hS _ _,
    hQ _, hM _ _, hM _ _, hC _, hM _ _, hA _ _, hM _ _, trivial⟩

include hQ in
/-- Every binding of `sqProg` satisfies `Good`. -/
theorem sqProg_covered : CoveredM Good (sqProg p) := ⟨hQ _, trivial⟩

include hM hQ in
/-- Every binding of `sqmProg` satisfies `Good`. -/
theorem sqmProg_covered : CoveredM Good (sqmProg p) := ⟨hQ _, hM _ _, trivial⟩

include hM in
/-- Every binding of `finProg` satisfies `Good`. -/
theorem finProg_covered : CoveredM Good (finProg p) := ⟨hM _ _, trivial⟩

include hC in
/-- Every binding of `initProg` satisfies `Good`. -/
theorem initProg_covered : CoveredM Good (initProg p) := ⟨hC _, hC _, trivial⟩

end Coverage

/-! ## 5. Limb states: loads, stores and the swap -/

/-- The limb vectors of the six elements of a ladder state in a context. -/
structure LimbSt (n : Nat) (Δ : Ctxt jasminDialect) where
  /-- The limbs of `u`. -/
  u : Ctxt.Hom (Rn n) Δ
  /-- The limbs of `x2`. -/
  x2 : Ctxt.Hom (Rn n) Δ
  /-- The limbs of `z2`. -/
  z2 : Ctxt.Hom (Rn n) Δ
  /-- The limbs of `x3`. -/
  x3 : Ctxt.Hom (Rn n) Δ
  /-- The limbs of `z3`. -/
  z3 : Ctxt.Hom (Rn n) Δ
  /-- The limbs of `t`. -/
  t : Ctxt.Hom (Rn n) Δ

namespace LimbSt

variable {n : Nat}

/-- The limb vectors renamed by `r`. -/
def map {Δ Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (h : LimbSt n Δ) : LimbSt n Δ' :=
  ⟨fun v => r (h.u v), fun v => r (h.x2 v), fun v => r (h.z2 v), fun v => r (h.x3 v),
    fun v => r (h.z3 v), fun v => r (h.t v)⟩

/-- The six limb vectors, in the order of `encW`. -/
def list {Δ : Ctxt jasminDialect} (h : LimbSt n Δ) : List (LimbVec n Δ) :=
  [⟨h.u⟩, ⟨h.x2⟩, ⟨h.z2⟩, ⟨h.x3⟩, ⟨h.z3⟩, ⟨h.t⟩]

/-- The limb vectors hold the limbs `E` of the elements of `s` at `W`. -/
def Holds {Δ : Ctxt jasminDialect} (E : ZMod p → ListDenote (Rn n)) (h : LimbSt n Δ)
    (W : Valuation Δ) (s : LadderState p) : Prop :=
  pullV h.u W = E s.u ∧ pullV h.x2 W = E s.x2 ∧ pullV h.z2 W = E s.z2 ∧
    pullV h.x3 W = E s.x3 ∧ pullV h.z3 W = E s.z3 ∧ pullV h.t W = E s.t

/-- A renaming that keeps every value keeps the encoding. -/
theorem Holds.map {Δ Δ' : Ctxt jasminDialect} {E : ZMod p → ListDenote (Rn n)}
    {h : LimbSt n Δ} {W : Valuation Δ} {s : LadderState p} (hh : h.Holds E W s)
    {r : Ctxt.Hom Δ Δ'} {W' : Valuation Δ'} (hr : Pres r W W') : (h.map r).Holds E W' s :=
  ⟨(pullV_comp_pres hr h.u).trans hh.1, (pullV_comp_pres hr h.x2).trans hh.2.1,
    (pullV_comp_pres hr h.z2).trans hh.2.2.1, (pullV_comp_pres hr h.x3).trans hh.2.2.2.1,
    (pullV_comp_pres hr h.z3).trans hh.2.2.2.2.1, (pullV_comp_pres hr h.t).trans hh.2.2.2.2.2⟩

end LimbSt

section States

variable {n : Nat}

/-- The loads of the six elements of the state array `a`. -/
def loadSt {bs : List JasminTy} {Δ : Ctxt jasminDialect} (a : Var Δ (arrTy (6 * n)))
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → LimbSt n Δ' → MC Δ' bs) : MC Δ bs :=
  loadLimbs n 0 a fun r₀ h₀ =>
  loadLimbs n n (r₀ a) fun r₁ h₁ =>
  loadLimbs n (2 * n) (r₁ (r₀ a)) fun r₂ h₂ =>
  loadLimbs n (3 * n) (r₂ (r₁ (r₀ a))) fun r₃ h₃ =>
  loadLimbs n (4 * n) (r₃ (r₂ (r₁ (r₀ a)))) fun r₄ h₄ =>
  loadLimbs n (5 * n) (r₄ (r₃ (r₂ (r₁ (r₀ a))))) fun r₅ h₅ =>
  k (fun v => r₅ (r₄ (r₃ (r₂ (r₁ (r₀ v))))))
    ⟨fun v => r₅ (r₄ (r₃ (r₂ (r₁ (h₀ v))))), fun v => r₅ (r₄ (r₃ (r₂ (h₁ v)))),
      fun v => r₅ (r₄ (r₃ (h₂ v))), fun v => r₅ (r₄ (h₃ v)), fun v => r₅ (h₄ v), h₅⟩

/-- The chunk `k` of `encW E s`. -/
theorem arrLimbs_encW (E : ZMod p → ListDenote (Rn n)) (s : LadderState p) (k : Nat)
    (hk : k < 6) :
    arrLimbs (encW E s) n (k * n) = [E s.u, E s.x2, E s.z2, E s.x3, E s.z3, E s.t][k] :=
  arrLimbs_storeChunks n _ _ 0 k _ (by simpa using hk) (by omega) (by simp; omega)

/-- The loads of `encW E s` give a limb state that holds `s`. -/
theorem loadSt_denote {bs : List JasminTy} (E : ZMod p → ListDenote (Rn n))
    (hn : 6 * n < 2 ^ 64) {Δ : Ctxt jasminDialect} (a : Var Δ (arrTy (6 * n)))
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → LimbSt n Δ' → MC Δ' bs)
    (W : Valuation Δ) (G : ListDenote bs) (s : LadderState p) (ha : a.lookup W = encW E s)
    (hk : ∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (h : LimbSt n Δ')
      (W' : Valuation Δ'), Pres r W W' → h.Holds E W' s → (k r h).denote W' = G) :
    (loadSt a k).denote W = G := by
  refine loadLimbs_denote n 0 a _ W G (by omega) fun r₀ h₀ W₀ p₀ e₀ => ?_
  refine loadLimbs_denote n n _ _ W₀ G (by omega) fun r₁ h₁ W₁ p₁ e₁ => ?_
  refine loadLimbs_denote n (2 * n) _ _ W₁ G (by omega) fun r₂ h₂ W₂ p₂ e₂ => ?_
  refine loadLimbs_denote n (3 * n) _ _ W₂ G (by omega) fun r₃ h₃ W₃ p₃ e₃ => ?_
  refine loadLimbs_denote n (4 * n) _ _ W₃ G (by omega) fun r₄ h₄ W₄ p₄ e₄ => ?_
  refine loadLimbs_denote n (5 * n) _ _ W₄ G (by omega) fun r₅ h₅ W₅ p₅ e₅ => ?_
  have q₅ : Pres r₅ W₄ W₅ := p₅
  have q₄ : Pres (fun v => r₅ (r₄ v)) W₃ W₅ := Pres.comp p₄ p₅
  have q₃ : Pres (fun v => r₅ (r₄ (r₃ v))) W₂ W₅ := Pres.comp p₃ q₄
  have q₂ : Pres (fun v => r₅ (r₄ (r₃ (r₂ v)))) W₁ W₅ := Pres.comp p₂ q₃
  have q₁ : Pres (fun v => r₅ (r₄ (r₃ (r₂ (r₁ v))))) W₀ W₅ := Pres.comp p₁ q₂
  refine hk _ _ W₅ (Pres.comp p₀ q₁) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (pullV_comp_pres q₁ h₀).trans (e₀.trans ?_)
    rw [ha]; exact (congrArg _ (Nat.zero_mul n).symm).trans (arrLimbs_encW E s 0 (by omega))
  · refine (pullV_comp_pres q₂ h₁).trans (e₁.trans ?_)
    rw [p₀ a, ha]; exact (congrArg _ (Nat.one_mul n).symm).trans (arrLimbs_encW E s 1 (by omega))
  · refine (pullV_comp_pres q₃ h₂).trans (e₂.trans ?_)
    rw [p₁ _, p₀ a, ha]; exact arrLimbs_encW E s 2 (by omega)
  · refine (pullV_comp_pres q₄ h₃).trans (e₃.trans ?_)
    rw [p₂ _, p₁ _, p₀ a, ha]; exact arrLimbs_encW E s 3 (by omega)
  · refine (pullV_comp_pres q₅ h₄).trans (e₄.trans ?_)
    rw [p₃ _, p₂ _, p₁ _, p₀ a, ha]; exact arrLimbs_encW E s 4 (by omega)
  · refine e₅.trans ?_
    rw [p₄ _, p₃ _, p₂ _, p₁ _, p₀ a, ha]; exact arrLimbs_encW E s 5 (by omega)

/-- The stores of the six limb vectors into the state array `o`. -/
def storeSt {Δ : Ctxt jasminDialect} (o : Var Δ (arrTy (6 * n))) (h : LimbSt n Δ) :
    MC Δ [arrTy (6 * n)] :=
  storeHoms 0 (fun v => v) o h.list

/-- The stores of a limb state that holds `s` return `encW E s`, whatever the array written
    to held. -/
theorem storeSt_denote (E : ZMod p → ListDenote (Rn n)) (hn : 6 * n < 2 ^ 64)
    {Δ : Ctxt jasminDialect} (o : Var Δ (arrTy (6 * n))) (h : LimbSt n Δ) (W : Valuation Δ)
    (s : LadderState p) (hh : h.Holds E W s) :
    (storeSt o h).denote W = .cons (encW E s) .nil := by
  rw [storeSt, storeHoms_denote hn h.list 0 _ o W (by simp [LimbSt.list]; omega)]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hh
  change (HVector.cons (storeChunks n (o.lookup W) 0
    [pullV h.u W, pullV h.x2 W, pullV h.z2 W, pullV h.x3 W, pullV h.z3 W, pullV h.t W]) .nil :
      ListDenote [arrTy (6 * n)]) = _
  rw [h1, h2, h3, h4, h5, h6, encW,
    storeChunks_full n _ (o.lookup W) (fun _ => 0) (by simp; omega)]

/-- The conditional swap of the two points of a limb state by the mask `c`. -/
def cswapSt {bs : List JasminTy} {Δ : Ctxt jasminDialect} (c : Var Δ w64) (h : LimbSt n Δ)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → LimbSt n Δ' → MC Δ' bs) : MC Δ bs :=
  cswapLimbs n c h.x2 h.x3 fun r₁ x2 x3 =>
  cswapLimbs n (r₁ c) (fun v => r₁ (h.z2 v)) (fun v => r₁ (h.z3 v)) fun r₂ z2 z3 =>
  k (fun v => r₂ (r₁ v))
    ⟨fun v => r₂ (r₁ (h.u v)), fun v => r₂ (x2 v), z2, fun v => r₂ (x3 v), z3,
      fun v => r₂ (r₁ (h.t v))⟩

/-- At the mask `maskW b`, `cswapSt` maps a limb state of `s` to one of `cswapF b s`. -/
theorem cswapSt_denote {bs : List JasminTy} (E : ZMod p → ListDenote (Rn n)) (b : Bool)
    {Δ : Ctxt jasminDialect} (c : Var Δ w64) (h : LimbSt n Δ)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → LimbSt n Δ' → MC Δ' bs)
    (W : Valuation Δ) (G : ListDenote bs) (s : LadderState p) (hc : c.lookup W = maskW b)
    (hh : h.Holds E W s)
    (hk : ∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (h' : LimbSt n Δ')
      (W' : Valuation Δ'), Pres r W W' → h'.Holds E W' (cswapF b s) → (k r h').denote W' = G) :
    (cswapSt c h k).denote W = G := by
  obtain ⟨hu, hx2, hz2, hx3, hz3, ht⟩ := hh
  refine cswapLimbs_denote b n c h.x2 h.x3 _ W G hc fun r₁ x2 x3 W₁ p₁ ex2 ex3 => ?_
  refine cswapLimbs_denote b n _ _ _ _ W₁ G ((p₁ c).trans hc)
    fun r₂ z2 z3 W₂ p₂ ez2 ez3 => ?_
  have q : Pres (fun v => r₂ (r₁ v)) W W₂ := Pres.comp p₁ p₂
  have fz2 := pullV_comp_pres p₁ h.z2
  have fz3 := pullV_comp_pres p₁ h.z3
  refine hk _ _ W₂ q ⟨(pullV_comp_pres q h.u).trans ?_,
    (pullV_comp_pres p₂ x2).trans (ex2.trans ?_), ez2.trans ?_,
    (pullV_comp_pres p₂ x3).trans (ex3.trans ?_), ez3.trans ?_,
    (pullV_comp_pres q h.t).trans ?_⟩ <;> cases b
  · exact hu
  · exact hu
  · exact hx2
  · exact hx3
  · exact fz2.trans hz2
  · exact fz3.trans hz3
  · exact hx3
  · exact hx2
  · exact fz3.trans hz3
  · exact fz2.trans hz2
  · exact ht
  · exact ht

/-- The empty renaming. -/
def nilHom {Δ : Ctxt jasminDialect} : Ctxt.Hom ([] : Ctxt jasminDialect) Δ := fun v => nomatch v

/-- The first `n` variables of a renaming of `Rn n ++ ys`. -/
def hdHom {ys Δ : Ctxt jasminDialect} (H : Ctxt.Hom (Rn n ++ ys) Δ) : Ctxt.Hom (Rn n) Δ :=
  fun w => H (inlHom ys w)

/-- The variables after the first `n` of a renaming of `Rn n ++ ys`. -/
def tlHom {ys Δ : Ctxt jasminDialect} (H : Ctxt.Hom (Rn n ++ ys) Δ) : Ctxt.Hom ys Δ :=
  fun w => H (inrHom (Rn n) w)

/-- The pullback along `hdHom` is the left part. -/
theorem pullV_hdHom {ys Δ : Ctxt jasminDialect} (H : Ctxt.Hom (Rn n ++ ys) Δ)
    (W : Valuation Δ) (A : Valuation (Rn n)) (B : Valuation ys)
    (hH : pullV H W = hvAppend A B) : pullV (hdHom H) W = A := by
  unfold hdHom
  rw [pullV_comp (fun w => inlHom ys w) H, hH, pullV_inlHom]

/-- The pullback along `tlHom` is the right part. -/
theorem pullV_tlHom {ys Δ : Ctxt jasminDialect} (H : Ctxt.Hom (Rn n ++ ys) Δ)
    (W : Valuation Δ) (A : Valuation (Rn n)) (B : Valuation ys)
    (hH : pullV H W = hvAppend A B) : pullV (tlHom H) W = B := by
  unfold tlHom
  rw [pullV_comp (fun w => inrHom (Rn n) w) H, hH, pullV_inrHom]

end States

/-! ## 6. The field steps over a record -/

section FieldSteps

variable {n : Nat} (lo : LimbBlocks n)

/-- The limbs of an element of `ZMod p` under the encoding `enc` of the record. -/
abbrev encF (enc : (loweringOf lo).Enc) (p : Nat) : ZMod p → ListDenote (Rn n) :=
  fun x => enc (t := FieldTy.fp p) x

/-- The double-and-add on a limb state: the lowering of `daddProg` by the blocks of `lo`. -/
def daddSt (a24 : ZMod p) {bs : List JasminTy} {Δ : Ctxt jasminDialect} (h : LimbSt n Δ)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → LimbSt n Δ' → MC Δ' bs) : MC Δ bs :=
  (loweringOf lo).lowerRM (Γ := fctx p 5) (ts := fctx p 4)
    (appendHom h.x2 (appendHom h.z2 (appendHom h.x3 (appendHom h.z3 (appendHom h.u nilHom)))))
    (daddProg p a24) fun r vs =>
    k r ⟨fun v => r (h.u v), hdHom (hvToHom vs), hdHom (tlHom (hvToHom vs)),
      hdHom (tlHom (tlHom (hvToHom vs))), hdHom (tlHom (tlHom (tlHom (hvToHom vs)))),
      fun v => r (h.t v)⟩

/-- The squaring of the accumulator on a limb state. -/
def sqSt {bs : List JasminTy} {Δ : Ctxt jasminDialect} (h : LimbSt n Δ)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → LimbSt n Δ' → MC Δ' bs) : MC Δ bs :=
  (loweringOf lo).lowerRM (Γ := fctx p 1) (ts := fctx p 1) (appendHom h.t nilHom) (sqProg p)
    fun r vs => k r { h.map r with t := hdHom (hvToHom vs) }

/-- The squaring of the accumulator and the product with `z2` on a limb state. -/
def sqmSt {bs : List JasminTy} {Δ : Ctxt jasminDialect} (h : LimbSt n Δ)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → LimbSt n Δ' → MC Δ' bs) : MC Δ bs :=
  (loweringOf lo).lowerRM (Γ := fctx p 2) (ts := fctx p 1)
    (appendHom h.t (appendHom h.z2 nilHom)) (sqmProg p)
    fun r vs => k r { h.map r with t := hdHom (hvToHom vs) }

/-- The product `x2 · t` of a limb state. -/
def finSt {bs : List JasminTy} {Δ : Ctxt jasminDialect} (h : LimbSt n Δ)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Hom (Rn n) Δ' → MC Δ' bs) :
    MC Δ bs :=
  (loweringOf lo).lowerRM (Γ := fctx p 2) (ts := fctx p 1)
    (appendHom h.x2 (appendHom h.t nilHom)) (finProg p) fun r vs => k r (hdHom (hvToHom vs))

/-- The initial limb state at the limbs `hu` of the base coordinate. -/
def initSt {bs : List JasminTy} {Δ : Ctxt jasminDialect} (hu : Ctxt.Hom (Rn n) Δ)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → LimbSt n Δ' → MC Δ' bs) : MC Δ bs :=
  (loweringOf lo).lowerRM (Γ := []) (ts := fctx p 2) nilHom (initProg p) fun r vs =>
    k r ⟨fun v => r (hu v), hdHom (hvToHom vs), hdHom (tlHom (hvToHom vs)), fun v => r (hu v),
      hdHom (hvToHom vs), hdHom (hvToHom vs)⟩

variable (enc : (loweringOf lo).Enc)
  (Good : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}, Expr fieldDialect Γ t → Prop)
  (hsq : (loweringOf lo).BlockSquare enc Good)

include hsq

/-- Under the block square, `daddSt` maps a limb state of `s` to one of `daddF a24 s`. -/
theorem daddSt_denote (a24 : ZMod p) (hcov : CoveredM Good (daddProg p a24))
    {bs : List JasminTy} {Δ : Ctxt jasminDialect} (h : LimbSt n Δ)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → LimbSt n Δ' → MC Δ' bs)
    (W : Valuation Δ) (G : ListDenote bs) (s : LadderState p)
    (hh : h.Holds (encF lo enc p) W s)
    (hk : ∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (h' : LimbSt n Δ')
      (W' : Valuation Δ'), Pres r W W' → h'.Holds (encF lo enc p) W' (daddF a24 s) →
      (k r h').denote W' = G) :
    (daddSt lo a24 h k).denote W = G := by
  obtain ⟨hu, hx2, hz2, hx3, hz3, ht⟩ := hh
  refine (loweringOf lo).lowerRM_denote_on enc Good hsq _ (daddProg p a24) _ W (daddIn s) G
    hcov ?_ fun r vs W' hr hvs => ?_
  · rw [pullV_appendHom, pullV_appendHom, pullV_appendHom, pullV_appendHom, pullV_appendHom,
      hx2, hz2, hx3, hz3, hu]
    rfl
  · rw [daddProg_denote] at hvs
    have hH := (pullV_hvToHom W' vs).trans hvs
    have h1 := pullV_tlHom _ W' _ _ hH
    have h2 := pullV_tlHom _ W' _ _ h1
    have h3 := pullV_tlHom _ W' _ _ h2
    exact hk r _ W' hr ⟨(pullV_comp_pres hr h.u).trans hu, pullV_hdHom _ W' _ _ hH,
      pullV_hdHom _ W' _ _ h1, pullV_hdHom _ W' _ _ h2, pullV_hdHom _ W' _ _ h3,
      (pullV_comp_pres hr h.t).trans ht⟩

/-- Under the block square, `sqSt` maps a limb state of `s` to one of `sqF s`. -/
theorem sqSt_denote (hcov : CoveredM Good (sqProg p))
    {bs : List JasminTy} {Δ : Ctxt jasminDialect} (h : LimbSt n Δ)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → LimbSt n Δ' → MC Δ' bs)
    (W : Valuation Δ) (G : ListDenote bs) (s : LadderState p)
    (hh : h.Holds (encF lo enc p) W s)
    (hk : ∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (h' : LimbSt n Δ')
      (W' : Valuation Δ'), Pres r W W' → h'.Holds (encF lo enc p) W' (sqF s) →
      (k r h').denote W' = G) :
    (sqSt lo (p := p) h k).denote W = G := by
  refine (loweringOf lo).lowerRM_denote_on enc Good hsq _ (sqProg p) _ W (.cons s.t .nil) G
    hcov ?_ fun r vs W' hr hvs => ?_
  · rw [pullV_appendHom, hh.2.2.2.2.2]
    rfl
  · rw [sqProg_denote] at hvs
    have hm := hh.map hr
    exact hk r _ W' hr ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1,
      pullV_hdHom _ W' _ _ ((pullV_hvToHom W' vs).trans hvs)⟩

/-- Under the block square, `sqmSt` maps a limb state of `s` to one of `sqmF s`. -/
theorem sqmSt_denote (hcov : CoveredM Good (sqmProg p))
    {bs : List JasminTy} {Δ : Ctxt jasminDialect} (h : LimbSt n Δ)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → LimbSt n Δ' → MC Δ' bs)
    (W : Valuation Δ) (G : ListDenote bs) (s : LadderState p)
    (hh : h.Holds (encF lo enc p) W s)
    (hk : ∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (h' : LimbSt n Δ')
      (W' : Valuation Δ'), Pres r W W' → h'.Holds (encF lo enc p) W' (sqmF s) →
      (k r h').denote W' = G) :
    (sqmSt lo (p := p) h k).denote W = G := by
  refine (loweringOf lo).lowerRM_denote_on enc Good hsq _ (sqmProg p) _ W
    (.cons s.t (.cons s.z2 .nil)) G hcov ?_ fun r vs W' hr hvs => ?_
  · rw [pullV_appendHom, pullV_appendHom, hh.2.2.2.2.2, hh.2.2.1]
    rfl
  · rw [sqmProg_denote] at hvs
    have hm := hh.map hr
    exact hk r _ W' hr ⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1,
      pullV_hdHom _ W' _ _ ((pullV_hvToHom W' vs).trans hvs)⟩

/-- Under the block square, `finSt` gives the limbs of `finF s`. -/
theorem finSt_denote (hcov : CoveredM Good (finProg p))
    {bs : List JasminTy} {Δ : Ctxt jasminDialect} (h : LimbSt n Δ)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → Ctxt.Hom (Rn n) Δ' → MC Δ' bs)
    (W : Valuation Δ) (G : ListDenote bs) (s : LadderState p)
    (hh : h.Holds (encF lo enc p) W s)
    (hk : ∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (x : Ctxt.Hom (Rn n) Δ')
      (W' : Valuation Δ'), Pres r W W' → pullV x W' = encF lo enc p (finF s) →
      (k r x).denote W' = G) :
    (finSt lo (p := p) h k).denote W = G := by
  refine (loweringOf lo).lowerRM_denote_on enc Good hsq _ (finProg p) _ W
    (.cons s.x2 (.cons s.t .nil)) G hcov ?_ fun r vs W' hr hvs => ?_
  · rw [pullV_appendHom, pullV_appendHom, hh.2.1, hh.2.2.2.2.2]
    rfl
  · rw [finProg_denote] at hvs
    exact hk r _ W' hr (pullV_hdHom _ W' _ _ ((pullV_hvToHom W' vs).trans hvs))

/-- Under the block square, `initSt` gives a limb state of `initF u`. -/
theorem initSt_denote (hcov : CoveredM Good (initProg p))
    {bs : List JasminTy} {Δ : Ctxt jasminDialect} (hu : Ctxt.Hom (Rn n) Δ)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → LimbSt n Δ' → MC Δ' bs)
    (W : Valuation Δ) (G : ListDenote bs) (u : ZMod p)
    (hhu : pullV hu W = encF lo enc p u)
    (hk : ∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (h' : LimbSt n Δ')
      (W' : Valuation Δ'), Pres r W W' → h'.Holds (encF lo enc p) W' (initF u) →
      (k r h').denote W' = G) :
    (initSt lo (p := p) hu k).denote W = G := by
  refine (loweringOf lo).lowerRM_denote_on enc Good hsq _ (initProg p) _ W .nil G
    hcov rfl fun r vs W' hr hvs => ?_
  rw [initProg_denote] at hvs
  have hH := (pullV_hvToHom W' vs).trans hvs
  have h1 := pullV_hdHom _ W' _ _ hH
  have h0 := pullV_hdHom _ W' _ _ (pullV_tlHom _ W' _ _ hH)
  have hU := (pullV_comp_pres hr hu).trans hhu
  exact hk r _ W' hr ⟨hU, h1, h0, hU, h1, h1⟩

end FieldSteps

/-! ## 7. The kernel bodies -/

section Bodies

variable {n : Nat} (lo : LimbBlocks n)

/-- The limbs of one element in an array of `n` words. -/
def encN (E : ZMod p → ListDenote (Rn n)) (x : ZMod p) : Fin n → BitVec 64 :=
  storeChunks n (fun _ => 0) 0 [E x]

/-- **The ladder step at the variables `w`, `b`, `o`**: the loads of the state array `w`, the
    mask `0 - b`, the swap, the double-and-add of `lo` at `a24`, the swap back, and the stores
    into `o`. -/
def stepBodyAt (a24 : ZMod p) {Δ : Ctxt jasminDialect} (w : Var Δ (arrTy (6 * n)))
    (b : Var Δ w64) (o : Var Δ (arrTy (6 * n))) : MC Δ [arrTy (6 * n)] :=
  loadSt w fun r₀ h₀ =>
  bindK (wConst 0) fun r₁ z =>
  bindK (eBin .sub z (r₁ (r₀ b))) fun r₂ c =>
  cswapSt c ((h₀.map r₁).map r₂) fun r₃ h₁ =>
  daddSt lo a24 h₁ fun r₄ h₂ =>
  cswapSt (r₄ (r₃ c)) h₂ fun r₅ h₃ =>
  storeSt (r₅ (r₄ (r₃ (r₂ (r₁ (r₀ o)))))) h₃

/-- The squaring of the accumulator at the variables `w`, `o`. -/
def sqBodyAt {Δ : Ctxt jasminDialect} (w o : Var Δ (arrTy (6 * n))) : MC Δ [arrTy (6 * n)] :=
  loadSt w fun r₀ h₀ => sqSt lo (p := p) h₀ fun r₁ h₁ => storeSt (r₁ (r₀ o)) h₁

/-- The squaring and product with `z2` of the accumulator at the variables `w`, `o`. -/
def sqmBodyAt {Δ : Ctxt jasminDialect} (w o : Var Δ (arrTy (6 * n))) : MC Δ [arrTy (6 * n)] :=
  loadSt w fun r₀ h₀ => sqmSt lo (p := p) h₀ fun r₁ h₁ => storeSt (r₁ (r₀ o)) h₁

/-- The output `x2 · t` at the variables `w`, `o`. -/
def finBodyAt {Δ : Ctxt jasminDialect} (w : Var Δ (arrTy (6 * n))) (o : Var Δ (arrTy n)) :
    MC Δ [arrTy n] :=
  loadSt w fun r₀ h₀ => finSt lo (p := p) h₀ fun r₁ x =>
    storeHoms 0 (fun v => v) (r₁ (r₀ o)) [⟨x⟩]

/-- The initial state at the variables `ua` (an array holding the `n` words of the base
    coordinate from index `j`) and `o`. -/
def initBodyAt {M : Nat} (j : Nat) {Δ : Ctxt jasminDialect} (ua : Var Δ (arrTy M))
    (o : Var Δ (arrTy (6 * n))) : MC Δ [arrTy (6 * n)] :=
  loadLimbs n j ua fun r₀ hu => initSt lo (p := p) hu fun r₁ h => storeSt (r₁ (r₀ o)) h

/-- The context of the step kernel: the state array, the bit word and the output array. -/
abbrev stepCtx (n : Nat) : Ctxt jasminDialect := [arrTy (6 * n), w64, arrTy (6 * n)]

/-- The context of the squaring kernels: the state array and the output array. -/
abbrev stCtx (n : Nat) : Ctxt jasminDialect := [arrTy (6 * n), arrTy (6 * n)]

/-- The context of the output kernel: the state array and the output array of `n` words. -/
abbrev finCtx (n : Nat) : Ctxt jasminDialect := [arrTy (6 * n), arrTy n]

/-- The context of the initial kernel: the base coordinate and the output state array. -/
abbrev initCtx (n : Nat) : Ctxt jasminDialect := [arrTy n, arrTy (6 * n)]

/-- **The step kernel body** over the record `lo` at the constant `a24`. -/
def stepBody (a24 : ZMod p) : MC (stepCtx n) [arrTy (6 * n)] :=
  stepBodyAt lo a24 .here (.there .here) (.there (.there .here))

/-- **The squaring kernel body** over the record `lo`. -/
def sqBody (p : Nat) : MC (stCtx n) [arrTy (6 * n)] :=
  sqBodyAt lo (p := p) .here (.there .here)

/-- **The squaring-and-product kernel body** over the record `lo`. -/
def sqmBody (p : Nat) : MC (stCtx n) [arrTy (6 * n)] :=
  sqmBodyAt lo (p := p) .here (.there .here)

/-- **The output kernel body** over the record `lo`. -/
def finBody (p : Nat) : MC (finCtx n) [arrTy n] :=
  finBodyAt lo (p := p) .here (.there .here)

/-- **The initial kernel body** over the record `lo`. -/
def initBody (p : Nat) : MC (initCtx n) [arrTy (6 * n)] :=
  initBodyAt lo (p := p) 0 .here (.there .here)

variable (enc : (loweringOf lo).Enc)
  (Good : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}, Expr fieldDialect Γ t → Prop)
  (hsq : (loweringOf lo).BlockSquare enc Good)
  (hA : ∀ {Γ : Ctxt fieldDialect} (a b : Var Γ (FieldTy.fp p)), Good (eAdd a b))
  (hS : ∀ {Γ : Ctxt fieldDialect} (a b : Var Γ (FieldTy.fp p)), Good (eSub a b))
  (hM : ∀ {Γ : Ctxt fieldDialect} (a b : Var Γ (FieldTy.fp p)), Good (eMul a b))
  (hQ : ∀ {Γ : Ctxt fieldDialect} (a : Var Γ (FieldTy.fp p)), Good (eSq a))
  (hC : ∀ {Γ : Ctxt fieldDialect} (c : ZMod p),
    Good (EllipticCurveDialect.JacLower.eConst (Γ := Γ) c))
  (hn : 6 * n < 2 ^ 64)

include hsq hA hS hM hQ hC hn in
/-- The ladder step at variables holding `encW s` and the bit word of `bit` returns
    `encW (ladderStepF a24 bit s)`. -/
theorem stepBodyAt_value (a24 : ZMod p) {Δ : Ctxt jasminDialect} (w : Var Δ (arrTy (6 * n)))
    (b : Var Δ w64) (o : Var Δ (arrTy (6 * n))) (W : Valuation Δ) (s : LadderState p)
    (bit : Bool) (hw : w.lookup W = encW (encF lo enc p) s)
    (hb : b.lookup W = BitVec.ofNat 64 bit.toNat) :
    (stepBodyAt lo a24 w b o).denote W
      = .cons (encW (encF lo enc p) (ladderStepF a24 bit s)) .nil := by
  refine loadSt_denote _ hn w _ W _ s hw fun r₀ h₀ W₀ p₀ hh₀ => ?_
  refine bindK_denote _ _ W₀ _ fun r₁ z W₁ p₁ hz => ?_
  refine bindK_denote _ _ W₁ _ fun r₂ c W₂ p₂ hc => ?_
  have hm : c.lookup W₂ = maskW bit :=
    hc.trans (congrArg₂ (fun x y : BitVec 64 => x - y) hz ((p₁ _).trans ((p₀ b).trans hb)))
  refine cswapSt_denote _ bit c _ _ W₂ _ s hm ((hh₀.map p₁).map p₂)
    fun r₃ h₁ W₃ p₃ hh₁ => ?_
  refine daddSt_denote lo enc Good hsq a24 (daddProg_covered Good hA hS hM hQ hC a24) h₁ _ W₃ _
    _ hh₁ fun r₄ h₂ W₄ p₄ hh₂ => ?_
  refine cswapSt_denote _ bit _ h₂ _ W₄ _ _ ((p₄ _).trans ((p₃ c).trans hm)) hh₂
    fun r₅ h₃ W₅ p₅ hh₃ => ?_
  exact storeSt_denote _ hn _ h₃ W₅ _ hh₃

include hsq hQ hn in
/-- The squaring at a variable holding `encW s` returns `encW (sqF s)`. -/
theorem sqBodyAt_value {Δ : Ctxt jasminDialect} (w o : Var Δ (arrTy (6 * n)))
    (W : Valuation Δ) (s : LadderState p) (hw : w.lookup W = encW (encF lo enc p) s) :
    (sqBodyAt lo (p := p) w o).denote W = .cons (encW (encF lo enc p) (sqF s)) .nil := by
  refine loadSt_denote _ hn w _ W _ s hw fun r₀ h₀ W₀ p₀ hh₀ => ?_
  refine sqSt_denote lo enc Good hsq (sqProg_covered Good hQ) h₀ _ W₀ _ s hh₀
    fun r₁ h₁ W₁ p₁ hh₁ => ?_
  exact storeSt_denote _ hn _ h₁ W₁ _ hh₁

include hsq hM hQ hn in
/-- The squaring and product at a variable holding `encW s` returns `encW (sqmF s)`. -/
theorem sqmBodyAt_value {Δ : Ctxt jasminDialect} (w o : Var Δ (arrTy (6 * n)))
    (W : Valuation Δ) (s : LadderState p) (hw : w.lookup W = encW (encF lo enc p) s) :
    (sqmBodyAt lo (p := p) w o).denote W = .cons (encW (encF lo enc p) (sqmF s)) .nil := by
  refine loadSt_denote _ hn w _ W _ s hw fun r₀ h₀ W₀ p₀ hh₀ => ?_
  refine sqmSt_denote lo enc Good hsq (sqmProg_covered Good hM hQ) h₀ _ W₀ _ s hh₀
    fun r₁ h₁ W₁ p₁ hh₁ => ?_
  exact storeSt_denote _ hn _ h₁ W₁ _ hh₁

include hsq hM hn in
/-- The output at a variable holding `encW s` returns the limbs of `finF s`. -/
theorem finBodyAt_value {Δ : Ctxt jasminDialect} (w : Var Δ (arrTy (6 * n)))
    (o : Var Δ (arrTy n)) (W : Valuation Δ) (s : LadderState p)
    (hw : w.lookup W = encW (encF lo enc p) s) :
    (finBodyAt lo (p := p) w o).denote W = .cons (encN (encF lo enc p) (finF s)) .nil := by
  refine loadSt_denote _ hn w _ W _ s hw fun r₀ h₀ W₀ p₀ hh₀ => ?_
  refine finSt_denote lo enc Good hsq (finProg_covered Good hM) h₀ _ W₀ _ s hh₀
    fun r₁ x W₁ p₁ hx => ?_
  rw [storeHoms_denote (by omega) [⟨x⟩] 0 _ _ W₁ (by simp)]
  change (HVector.cons (storeChunks n _ 0 [pullV x W₁]) .nil : ListDenote [arrTy n]) = _
  rw [hx, encN, storeChunks_full n _ _ (fun _ => 0) (by simp)]

include hsq hC hn in
/-- The initial kernel at an array holding the limbs of `u` from index `j` returns
    `encW (initF u)`. -/
theorem initBodyAt_value {M : Nat} (j : Nat) (hj : j + n < 2 ^ 64) {Δ : Ctxt jasminDialect}
    (ua : Var Δ (arrTy M)) (o : Var Δ (arrTy (6 * n))) (W : Valuation Δ) (u : ZMod p)
    (hu : arrLimbs (ua.lookup W) n j = encF lo enc p u) :
    (initBodyAt lo (p := p) j ua o).denote W = .cons (encW (encF lo enc p) (initF u)) .nil := by
  refine loadLimbs_denote n j ua _ W _ hj fun r₀ h₀ W₀ p₀ e₀ => ?_
  refine initSt_denote lo enc Good hsq (initProg_covered Good hC) h₀ _ W₀ _ u (e₀.trans hu)
    fun r₁ h₁ W₁ p₁ hh₁ => ?_
  exact storeSt_denote _ hn _ h₁ W₁ _ hh₁

include hsq hA hS hM hQ hC hn in
/-- **Value of the step kernel**: at the state array `encW s`, the bit word `b` and any
    output array, the body returns `encW (ladderStepF a24 b s)`. -/
theorem stepBody_value (a24 : ZMod p) (s : LadderState p) (b : Bool)
    (O : Fin (6 * n) → BitVec 64) :
    (stepBody lo a24).denote (.cons (encW (encF lo enc p) s)
        (.cons (BitVec.ofNat 64 b.toNat) (.cons O .nil)))
      = .cons (encW (encF lo enc p) (ladderStepF a24 b s)) .nil :=
  stepBodyAt_value lo enc Good hsq hA hS hM hQ hC hn a24 _ _ _ _ s b rfl rfl

include hsq hQ hn in
/-- **Value of the squaring kernel**: `encW s` to `encW (sqF s)`. -/
theorem sqBody_value (s : LadderState p) (O : Fin (6 * n) → BitVec 64) :
    (sqBody lo p).denote (.cons (encW (encF lo enc p) s) (.cons O .nil))
      = .cons (encW (encF lo enc p) (sqF s)) .nil :=
  sqBodyAt_value lo enc Good hsq hQ hn _ _ _ s rfl

include hsq hM hQ hn in
/-- **Value of the squaring-and-product kernel**: `encW s` to `encW (sqmF s)`. -/
theorem sqmBody_value (s : LadderState p) (O : Fin (6 * n) → BitVec 64) :
    (sqmBody lo p).denote (.cons (encW (encF lo enc p) s) (.cons O .nil))
      = .cons (encW (encF lo enc p) (sqmF s)) .nil :=
  sqmBodyAt_value lo enc Good hsq hM hQ hn _ _ _ s rfl

include hsq hM hn in
/-- **Value of the output kernel**: `encW s` to the `n` limbs of `finF s = x2 · t`. -/
theorem finBody_value (s : LadderState p) (O : Fin n → BitVec 64) :
    (finBody lo p).denote (.cons (encW (encF lo enc p) s) (.cons O .nil))
      = .cons (encN (encF lo enc p) (finF s)) .nil :=
  finBodyAt_value lo enc Good hsq hM hn _ _ _ s rfl

include hsq hC hn in
/-- **Value of the initial kernel**: the `n` limbs of `u` to `encW (initF u)`. -/
theorem initBody_value (u : ZMod p) (O : Fin (6 * n) → BitVec 64) :
    (initBody lo p).denote (.cons (encN (encF lo enc p) u) (.cons O .nil))
      = .cons (encW (encF lo enc p) (initF u)) .nil :=
  initBodyAt_value lo enc Good hsq hC hn 0 (by omega) _ _ _ u
    (arrLimbs_storeChunks n _ _ 0 0 0 (by simp) (by omega) (by simp))

end Bodies

/-! ## 8. The ladder loop over a packed input -/

section Loop

/-- A multi-result straight-line program followed by a structured program that receives the
    renaming of the context and the result variables. -/
def nfThen {us : List JasminTy} : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} → MC Γ ts →
    (∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → HVector (fun t => Var Δ t) ts →
      NFProg jasminDialect Δ us) → NFProg jasminDialect Γ us
  | _, _, .ret vs, K => K (fun v => v) vs
  | _, _, .var e m, K => .var e (nfThen m fun r vs => K (fun v => r (.there v)) vs)

/-- `nfThen m K` denotes its continuation at the values of `m`. -/
theorem nfThen_denote {us : List JasminTy} (fuel : Nat) :
    ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (m : MC Γ ts)
      (K : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → HVector (fun t => Var Δ t) ts →
        NFProg jasminDialect Δ us)
      (W : Valuation Γ) (R : Option (ListDenote us)),
      (∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (vs : HVector (fun t => Var Δ t) ts)
          (W' : Valuation Δ), Pres r W W' → MultiReturnCom.lookupVars vs W' = m.denote W →
          (K r vs).denote fuel W' = R) →
      (nfThen m K).denote fuel W = R
  | _, _, .ret vs, _, W, _, hK => hK _ vs W (Pres.id W) rfl
  | _, _, .var e m, K, W, R, hK => by
      change (NFProg.var e (nfThen m fun r vs => K (fun v => r (.there v)) vs)).denote fuel W = R
      rw [NFProg.denote_var, Expr.denoteM_option_eq_some]
      exact nfThen_denote fuel m _ _ R fun r vs W' hr hv =>
        hK _ vs W' (fun v => hr (.there v)) hv

variable {n : Nat}

/-- The index `254 - i` of the scalar bit of iteration `i`. -/
def bitIdxW (i : Nat) : BitVec 64 := BitVec.ofNat 64 254 - BitVec.ofNat 64 i

/-- The scalar word holding the bit of iteration `i`: word `(254 - i) >> 6` of `K`. -/
def bitWordW {M : Nat} (K : Fin M → BitVec 64) (i : Nat) : BitVec 64 :=
  stackGet K (JasminBinOp.apply .shr (bitIdxW i) (BitVec.ofNat 64 6)).toNat

/-- The word-mask select of `x` and `y` by the mask `m`: `x ^ (m & (x ^ y))`. -/
def mselW (m x y : BitVec 64) : BitVec 64 := x ^^^ (m &&& (x ^^^ y))

/-- The mask of bit `s` of the word `v`: `0 - ((v >> s) & 1)`. -/
def bitMaskW (v : BitVec 64) (s : Nat) : BitVec 64 :=
  BitVec.ofNat 64 0 - (JasminBinOp.apply .shr v (BitVec.ofNat 64 s) &&& BitVec.ofNat 64 1)

/-- The word of index `q` among `w0`, `w1`, `w2`, `w3`, selected by the masks of the two low
    bits of `q`. -/
def sel4W (w0 w1 w2 w3 q : BitVec 64) : BitVec 64 :=
  mselW (bitMaskW q 1) (mselW (bitMaskW q 0) w0 w1) (mselW (bitMaskW q 0) w2 w3)

/-- The scalar word of iteration `i` read without a computed index: the words `0`, `1`, `2`,
    `3` of `K`, of which word `(254 - i) >> 6` is selected by masks. -/
def bitSelW {M : Nat} (K : Fin M → BitVec 64) (i : Nat) : BitVec 64 :=
  sel4W (stackGet K 0) (stackGet K 1) (stackGet K 2) (stackGet K 3)
    (JasminBinOp.apply .shr (bitIdxW i) (BitVec.ofNat 64 6))

/-- The scalar word of iteration `i` shifted right by `(254 - i) & 63`. -/
def bitShW {M : Nat} (K : Fin M → BitVec 64) (i : Nat) : BitVec 64 :=
  JasminBinOp.apply .shr (bitSelW K i) (bitIdxW i &&& BitVec.ofNat 64 63)

/-- **The scalar bit of iteration `i`**: bit `(254 - i) & 63` of the word `bitSelW K i`, the
    mask selection of word `(254 - i) >> 6` among the scalar words `0..3` of `K`. -/
def scalarBitAt {M : Nat} (K : Fin M → BitVec 64) (i : Nat) : Bool := (bitShW K i).getLsbD 0

/-- The low bit of a word as a word. -/
theorem and_one_eq (x : BitVec 64) :
    x &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (x.getLsbD 0).toNat := by
  cases hx : x.getLsbD 0 <;> ext i <;> simp <;> grind

/-- The mask of bit `s` of `v` is the swap mask of that bit. -/
theorem bitMaskW_eq (v : BitVec 64) (s : Nat) :
    bitMaskW v s = maskW ((JasminBinOp.apply .shr v (BitVec.ofNat 64 s)).getLsbD 0) := by
  rw [bitMaskW, and_one_eq]
  rfl

/-- The word-mask select by the swap mask of `b` is `y` at `true` and `x` at `false`. -/
theorem mselW_maskW (b : Bool) (x y : BitVec 64) :
    mselW (maskW b) x y = if b then y else x :=
  cswap_word_fst b x y

/-- At an index below `4`, the mask selection `sel4W` is the word at that index. -/
theorem sel4W_eq (w0 w1 w2 w3 q : BitVec 64) (hq : q.toNat < 4) :
    sel4W w0 w1 w2 w3 q = [w0, w1, w2, w3].getD q.toNat 0 := by
  have hq' : q = BitVec.ofNat 64 q.toNat := by simp
  generalize q.toNat = a at hq hq'
  subst hq'
  interval_cases a <;>
    simp only [sel4W, bitMaskW_eq, mselW_maskW] <;> rfl

/-- For `i ≤ 254`, the bit index `bitIdxW i` is `254 - i`. -/
theorem bitIdxW_toNat (i : Nat) (hi : i ≤ 254) : (bitIdxW i).toNat = 254 - i := by
  simp [bitIdxW, BitVec.toNat_sub]
  omega

/-- For `i ≤ 254`, the word index `(254 - i) >> 6` is `(254 - i) / 64`. -/
theorem bitQW_toNat (i : Nat) (hi : i ≤ 254) :
    (JasminBinOp.apply .shr (bitIdxW i) (BitVec.ofNat 64 6)).toNat = (254 - i) / 64 := by
  simp [JasminBinOp.apply, shiftMask, bitIdxW_toNat i hi, Nat.shiftRight_eq_div_pow]

/-- For `i ≤ 254`, the mask selection `bitSelW` is the word `(254 - i) >> 6` of `K`. -/
theorem bitSelW_eq_bitWordW {M : Nat} (K : Fin M → BitVec 64) (i : Nat) (hi : i ≤ 254) :
    bitSelW K i = bitWordW K i := by
  have hq := bitQW_toNat i hi
  rw [bitSelW, bitWordW, sel4W_eq _ _ _ _ _ (by omega), hq]
  have : (254 - i) / 64 < 4 := by omega
  generalize (254 - i) / 64 = a at this
  interval_cases a <;> rfl

/-- For `i ≤ 254`, the scalar bit of iteration `i` is bit `(254 - i) % 64` of word
    `(254 - i) / 64` of the scalar words `K`. -/
theorem scalarBitAt_eq_testBit {M : Nat} (K : Fin M → BitVec 64) (i : Nat) (hi : i ≤ 254) :
    scalarBitAt K i = (stackGet K ((254 - i) / 64)).toNat.testBit ((254 - i) % 64) := by
  rw [scalarBitAt, bitShW, bitSelW_eq_bitWordW K i hi, bitWordW, bitQW_toNat i hi]
  simp only [JasminBinOp.apply, shiftMask, ↓reduceIte, BitVec.toNat_and, bitIdxW_toNat i hi,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.ofNat_pos, BitVec.getLsbD_eq_getElem,
    BitVec.getElem_ushiftRight, add_zero, ← BitVec.testBit_toNat]
  rw [show 254 - i &&& 63 = (254 - i) % 64 from Nat.and_two_pow_sub_one_eq_mod _ 6,
    Nat.mod_mod]

variable (lo : LimbBlocks n)

section Select

variable {ts : List JasminTy} {Γ : Ctxt jasminDialect}

/-- The word-mask select `x ^ (m & (x ^ y))`; the continuation receives the renaming and the
    result. -/
def mselK (m x y : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ w64 → MC Δ ts) : MC Γ ts :=
  bindK (eBin .xor x y) fun r₁ d =>
  bindK (eBin .and (r₁ m) d) fun r₂ e =>
  bindK (eBin .xor (r₂ (r₁ x)) e) fun r₃ z =>
  k (fun v => r₃ (r₂ (r₁ v))) z

/-- `mselK m x y k` passes the value `mselW m x y` to its continuation. -/
theorem mselK_denote (m x y : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ w64 → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (z : Var Δ w64) (W' : Valuation Δ),
      Pres r W W' → lk z W' = mselW (lk m W) (lk x W) (lk y W) → (k r z).denote W' = G) :
    (mselK m x y k).denote W = G := by
  refine bindK_denote _ _ W _ fun r₁ d W₁ p₁ h₁ => ?_
  refine bindK_denote _ _ W₁ _ fun r₂ e W₂ p₂ h₂ => ?_
  refine bindK_denote _ _ W₂ _ fun r₃ z W₃ p₃ h₃ => ?_
  have ee : lk e W₂ = lk m W &&& (lk x W ^^^ lk y W) :=
    h₂.trans (congrArg₂ (fun a b : BitVec 64 => a &&& b) (p₁ m) h₁)
  exact hk _ z W₃ (Pres.comp (Pres.comp p₁ p₂) p₃)
    (h₃.trans (congrArg₂ (fun a b : BitVec 64 => a ^^^ b) ((p₂ (r₁ x)).trans (p₁ x)) ee))

/-- The expression `shrImm 64 s` on `v`: the right shift of `v` by the immediate count `s`. -/
def eShrImm (s : Nat) (v : Var Γ w64) : Expr jasminDialect Γ w64 :=
  { op := .shrImm 64 s, retTy_eq := rfl, args := .cons v .nil }

/-- The right shift of `v` by the constant `s`: no instruction at `s = 0`, the immediate shift
    `shrImm 64 s` otherwise; the continuation receives the renaming and the shifted word. -/
def shrConstK (v : Var Γ w64) (s : Nat)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ w64 → MC Δ ts) : MC Γ ts :=
  match s with
  | 0 => k (fun x => x) v
  | s + 1 => bindK (eShrImm (s + 1) v) k

/-- `shrConstK v s k` passes the value `v >> s` to its continuation. -/
theorem shrConstK_denote (v : Var Γ w64) (s : Nat)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ w64 → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (z : Var Δ w64) (W' : Valuation Δ),
      Pres r W W' → lk z W' = JasminBinOp.apply .shr (lk v W) (BitVec.ofNat 64 s) →
        (k r z).denote W' = G) :
    (shrConstK v s k).denote W = G := by
  cases s with
  | zero => exact hk _ v W (Pres.id W) (by simp [JasminBinOp.apply])
  | succ s =>
    refine bindK_denote _ _ W _ fun r z W' p h => hk r z W' p (h.trans ?_)
    change lk v W >>> shiftMask 64 (s + 1) = _
    simp [JasminBinOp.apply, Nat.mod_mod_of_dvd]

/-- The mask `0 - ((v >> s) & 1)` of bit `s` of `v`, with the shift read by `shrConstK`; the
    continuation receives the renaming and the mask. -/
def maskK (v : Var Γ w64) (s : Nat)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ w64 → MC Δ ts) : MC Γ ts :=
  shrConstK v s fun r₂ t =>
  bindK (wConst 1) fun r₃ one =>
  bindK (eBin .and (r₃ t) one) fun r₄ b =>
  bindK (wConst 0) fun r₅ z =>
  bindK (eBin .sub z (r₅ b)) fun r₆ m =>
  k (fun x => r₆ (r₅ (r₄ (r₃ (r₂ x))))) m

/-- `maskK v s k` passes the value `bitMaskW v s` to its continuation. -/
theorem maskK_denote (v : Var Γ w64) (s : Nat)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ w64 → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (z : Var Δ w64) (W' : Valuation Δ),
      Pres r W W' → lk z W' = bitMaskW (lk v W) s → (k r z).denote W' = G) :
    (maskK v s k).denote W = G := by
  refine shrConstK_denote _ _ _ W _ fun r₂ t W₂ p₂ et => ?_
  refine bindK_denote _ _ W₂ _ fun r₃ one W₃ p₃ h₃ => ?_
  refine bindK_denote _ _ W₃ _ fun r₄ b W₄ p₄ h₄ => ?_
  refine bindK_denote _ _ W₄ _ fun r₅ z W₅ p₅ h₅ => ?_
  refine bindK_denote _ _ W₅ _ fun r₆ m W₆ p₆ h₆ => ?_
  have eb : lk b W₄
      = JasminBinOp.apply .shr (lk v W) (BitVec.ofNat 64 s) &&& BitVec.ofNat 64 1 :=
    h₄.trans (congrArg₂ (fun a b : BitVec 64 => a &&& b) ((p₃ t).trans et) h₃)
  exact hk _ m W₆
    (Pres.comp (Pres.comp (Pres.comp (Pres.comp p₂ p₃) p₄) p₅) p₆)
    (h₆.trans (congrArg₂ (fun a b : BitVec 64 => a - b) h₅ ((p₅ b).trans eb)))

/-- The load of word `j` of the array `pk` at the literal index `j`; the continuation receives
    the renaming and the word. -/
def ldK {M : Nat} (pk : Var Γ (arrTy M)) (j : Nat)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ w64 → MC Δ ts) : MC Γ ts :=
  bindK (wConst j) fun r₁ c =>
  bindK (eLoad (r₁ pk) c) fun r₂ w =>
  k (fun x => r₂ (r₁ x)) w

/-- `ldK pk j k` passes word `j` of `pk` to its continuation. -/
theorem ldK_denote {M : Nat} (pk : Var Γ (arrTy M)) (j : Nat)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ w64 → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (z : Var Δ w64) (W' : Valuation Δ),
      Pres r W W' → lk z W' = stackGet (pk.lookup W) (BitVec.ofNat 64 j).toNat →
        (k r z).denote W' = G) :
    (ldK pk j k).denote W = G := by
  refine bindK_denote _ _ W _ fun r₁ c W₁ p₁ h₁ => ?_
  refine bindK_denote _ _ W₁ _ fun r₂ w W₂ p₂ h₂ => ?_
  exact hk _ w W₂ (Pres.comp p₁ p₂)
    (h₂.trans (congrArg₂ (fun (a : Fin M → BitVec 64) (b : BitVec 64) => stackGet a b.toNat)
      (p₁ pk) h₁))

/-- The mask selection `sel4W` of word `q` among the words `0..3` of `pk`, read at literal
    indices; the continuation receives the renaming and the word. -/
def wordSelK {M : Nat} (pk : Var Γ (arrTy M)) (q : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ w64 → MC Δ ts) : MC Γ ts :=
  ldK pk 0 fun r₁ w0 =>
  ldK (r₁ pk) 1 fun r₂ w1 =>
  ldK (r₂ (r₁ pk)) 2 fun r₃ w2 =>
  ldK (r₃ (r₂ (r₁ pk))) 3 fun r₄ w3 =>
  maskK (r₄ (r₃ (r₂ (r₁ q)))) 0 fun r₅ m0 =>
  maskK (r₅ (r₄ (r₃ (r₂ (r₁ q))))) 1 fun r₆ m1 =>
  mselK (r₆ m0) (r₆ (r₅ (r₄ (r₃ (r₂ w0))))) (r₆ (r₅ (r₄ (r₃ w1)))) fun r₇ lo =>
  mselK (r₇ (r₆ m0)) (r₇ (r₆ (r₅ (r₄ w2)))) (r₇ (r₆ (r₅ w3))) fun r₈ hi =>
  mselK (r₈ (r₇ m1)) (r₈ lo) hi fun r₉ z =>
  k (fun x => r₉ (r₈ (r₇ (r₆ (r₅ (r₄ (r₃ (r₂ (r₁ x))))))))) z

/-- `wordSelK pk q k` passes `sel4W` of the words `0..3` of `pk` at `q` to its
    continuation. -/
theorem wordSelK_denote {M : Nat} (pk : Var Γ (arrTy M)) (q : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ w64 → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (K : Fin M → BitVec 64) (hpk : pk.lookup W = K)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (z : Var Δ w64) (W' : Valuation Δ),
      Pres r W W' →
        lk z W' = sel4W (stackGet K 0) (stackGet K 1) (stackGet K 2) (stackGet K 3) (lk q W) →
        (k r z).denote W' = G) :
    (wordSelK pk q k).denote W = G := by
  refine ldK_denote _ _ _ W _ fun r₁ w0 W₁ p₁ h₁ => ?_
  refine ldK_denote _ _ _ W₁ _ fun r₂ w1 W₂ p₂ h₂ => ?_
  refine ldK_denote _ _ _ W₂ _ fun r₃ w2 W₃ p₃ h₃ => ?_
  refine ldK_denote _ _ _ W₃ _ fun r₄ w3 W₄ p₄ h₄ => ?_
  refine maskK_denote _ _ _ W₄ _ fun r₅ m0 W₅ p₅ h₅ => ?_
  refine maskK_denote _ _ _ W₅ _ fun r₆ m1 W₆ p₆ h₆ => ?_
  refine mselK_denote _ _ _ _ W₆ _ fun r₇ lo W₇ p₇ h₇ => ?_
  refine mselK_denote _ _ _ _ W₇ _ fun r₈ hi W₈ p₈ h₈ => ?_
  refine mselK_denote _ _ _ _ W₈ _ fun r₉ z W₉ p₉ h₉ => ?_
  have k1 : (r₁ pk).lookup W₁ = K := (p₁ pk).trans hpk
  have k2 : (r₂ (r₁ pk)).lookup W₂ = K := (p₂ _).trans k1
  have k3 : (r₃ (r₂ (r₁ pk))).lookup W₃ = K := (p₃ _).trans k2
  have e0 : lk (r₆ (r₅ (r₄ (r₃ (r₂ w0))))) W₆ = stackGet K 0 :=
    (p₆ _).trans ((p₅ _).trans ((p₄ _).trans ((p₃ _).trans ((p₂ w0).trans
      (h₁.trans (congrArg (fun a => stackGet a (BitVec.ofNat 64 0).toNat) hpk))))))
  have e1 : lk (r₆ (r₅ (r₄ (r₃ w1)))) W₆ = stackGet K 1 :=
    (p₆ _).trans ((p₅ _).trans ((p₄ _).trans ((p₃ w1).trans
      (h₂.trans (congrArg (fun a => stackGet a (BitVec.ofNat 64 1).toNat) k1)))))
  have e2 : lk (r₇ (r₆ (r₅ (r₄ w2)))) W₇ = stackGet K 2 :=
    (p₇ _).trans ((p₆ _).trans ((p₅ _).trans ((p₄ w2).trans
      (h₃.trans (congrArg (fun a => stackGet a (BitVec.ofNat 64 2).toNat) k2)))))
  have e3 : lk (r₇ (r₆ (r₅ w3))) W₇ = stackGet K 3 :=
    (p₇ _).trans ((p₆ _).trans ((p₅ w3).trans
      (h₄.trans (congrArg (fun a => stackGet a (BitVec.ofNat 64 3).toNat) k3))))
  have em0 : lk m0 W₅ = bitMaskW (lk q W) 0 :=
    h₅.trans (congrArg (fun a => bitMaskW a 0)
      ((p₄ _).trans ((p₃ _).trans ((p₂ _).trans (p₁ q)))))
  have em1 : lk m1 W₆ = bitMaskW (lk q W) 1 :=
    h₆.trans (congrArg (fun a => bitMaskW a 1)
      ((p₅ _).trans ((p₄ _).trans ((p₃ _).trans ((p₂ _).trans (p₁ q))))))
  have elo : lk lo W₇ = mselW (bitMaskW (lk q W) 0) (stackGet K 0) (stackGet K 1) :=
    h₇.trans (congr (congr (congrArg mselW ((p₆ m0).trans em0)) e0) e1)
  have ehi : lk hi W₈ = mselW (bitMaskW (lk q W) 0) (stackGet K 2) (stackGet K 3) :=
    h₈.trans (congr (congr (congrArg mselW ((p₇ _).trans ((p₆ m0).trans em0))) e2) e3)
  have ez : lk z W₉ = mselW (bitMaskW (lk q W) 1)
      (mselW (bitMaskW (lk q W) 0) (stackGet K 0) (stackGet K 1))
      (mselW (bitMaskW (lk q W) 0) (stackGet K 2) (stackGet K 3)) :=
    h₉.trans (congr (congr (congrArg mselW ((p₈ _).trans ((p₇ m1).trans em1)))
      ((p₈ lo).trans elo)) ehi)
  exact hk _ z W₉
    (Pres.comp (Pres.comp (Pres.comp (Pres.comp (Pres.comp (Pres.comp (Pres.comp
      (Pres.comp p₁ p₂) p₃) p₄) p₅) p₆) p₇) p₈) p₉) ez

/-- The scalar bit of iteration `i` as a word, read from the packed input `pk` without a
    computed index; the continuation receives the renaming and the bit word. -/
def scalarBitK {M : Nat} (pk : Var Γ (arrTy M)) (i : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ w64 → MC Δ ts) : MC Γ ts :=
  bindK (wConst 254) fun r₁ c =>
  bindK (eBin .sub c (r₁ i)) fun r₂ j =>
  shrConstK j 6 fun r₄ q =>
  wordSelK (r₄ (r₂ (r₁ pk))) q fun r₅ word =>
  bindK (wConst 63) fun r₆ m =>
  bindK (eBin .and (r₆ (r₅ (r₄ j))) m) fun r₇ sh =>
  bindK (eBin .shr (r₇ (r₆ word)) sh) fun r₈ x =>
  bindK (wConst 1) fun r₉ one =>
  bindK (eBin .and (r₉ x) one) fun r₁₀ bw =>
  k (fun v => r₁₀ (r₉ (r₈ (r₇ (r₆ (r₅ (r₄ (r₂ (r₁ v))))))))) bw

/-- `scalarBitK pk i k` passes the bit `scalarBitAt K iv` as a word to its continuation. -/
theorem scalarBitK_denote {M : Nat} (pk : Var Γ (arrTy M)) (i : Var Γ w64)
    (k : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ w64 → MC Δ ts)
    (W : Valuation Γ) (G : ListDenote ts) (K : Fin M → BitVec 64) (iv : Nat)
    (hpk : pk.lookup W = K) (hi : i.lookup W = BitVec.ofNat 64 iv)
    (hk : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (z : Var Δ w64) (W' : Valuation Δ),
      Pres r W W' → lk z W' = BitVec.ofNat 64 (scalarBitAt K iv).toNat →
        (k r z).denote W' = G) :
    (scalarBitK pk i k).denote W = G := by
  refine bindK_denote _ _ W _ fun r₁ c W₁ p₁ h₁ => ?_
  refine bindK_denote _ _ W₁ _ fun r₂ j W₂ p₂ h₂ => ?_
  have ej : lk j W₂ = bitIdxW iv :=
    h₂.trans (congrArg₂ (fun a b : BitVec 64 => a - b) h₁ ((p₁ i).trans hi))
  refine shrConstK_denote _ _ _ W₂ _ fun r₄ q W₄ p₄ h₄ => ?_
  have eq_ : lk q W₄ = JasminBinOp.apply .shr (bitIdxW iv) (BitVec.ofNat 64 6) :=
    h₄.trans (congrArg (fun a : BitVec 64 => JasminBinOp.apply .shr a (BitVec.ofNat 64 6)) ej)
  have epk : (r₄ (r₂ (r₁ pk))).lookup W₄ = K :=
    ((p₄ (r₂ (r₁ pk))).trans ((p₂ (r₁ pk)).trans (p₁ pk))).trans hpk
  refine wordSelK_denote _ _ _ W₄ _ K epk fun r₅ word W₅ p₅ h₅ => ?_
  have eword : lk word W₅ = bitSelW K iv := h₅.trans (congrArg _ eq_)
  refine bindK_denote _ _ W₅ _ fun r₆ m W₆ p₆ h₆ => ?_
  refine bindK_denote _ _ W₆ _ fun r₇ sh W₇ p₇ h₇ => ?_
  refine bindK_denote _ _ W₇ _ fun r₈ x W₈ p₈ h₈ => ?_
  refine bindK_denote _ _ W₈ _ fun r₉ one W₉ p₉ h₉ => ?_
  refine bindK_denote _ _ W₉ _ fun r₁₀ bw W₁₀ p₁₀ h₁₀ => ?_
  have esh : lk sh W₇ = bitIdxW iv &&& BitVec.ofNat 64 63 :=
    h₇.trans (congrArg₂ (fun a b : BitVec 64 => a &&& b)
      ((p₆ (r₅ (r₄ j))).trans ((p₅ (r₄ j)).trans ((p₄ j).trans ej))) h₆)
  have ex : lk x W₈ = bitShW K iv :=
    h₈.trans (congrArg₂ (fun a b : BitVec 64 => JasminBinOp.apply .shr a b)
      ((p₇ (r₆ word)).trans ((p₆ word).trans eword)) esh)
  have ebw : lk bw W₁₀ = BitVec.ofNat 64 (scalarBitAt K iv).toNat :=
    (h₁₀.trans (congrArg₂ (fun a b : BitVec 64 => a &&& b) ((p₉ x).trans ex) h₉)).trans
      (and_one_eq _)
  exact hk _ bw W₁₀ (Pres.comp (Pres.comp (Pres.comp (Pres.comp (Pres.comp (Pres.comp
    (Pres.comp (Pres.comp p₁ p₂) p₄) p₅) p₆) p₇) p₈) p₉) p₁₀) ebw

end Select

/-- **One iteration of the loop** at the packed input `pk`, the loop index `i` and the state
    `w`: the bit `scalarBitAt` of iteration `i`, read from `pk` by `scalarBitK` (loads at
    literal indices and a mask selection), and the ladder step `stepBodyAt` at that bit, with
    `w` as its output array. -/
def bitStepAt (a24 : ZMod p) {M : Nat} {Δ : Ctxt jasminDialect} (pk : Var Δ (arrTy M))
    (i : Var Δ w64) (w : Var Δ (arrTy (6 * n))) : MC Δ [arrTy (6 * n)] :=
  scalarBitK pk i fun r bw => stepBodyAt lo a24 (r w) bw (r w)

/-- **The ladder loop with a continuation** at the packed input `pk` (`4` scalar words, then
    the `n` words of the base coordinate) and the array `o`: the initial state from `u` into
    `o`, then a counted loop of `255` iterations whose body is `bitStepAt` on the carried state
    array; the continuation receives the renaming of the context and the final state array. -/
def ladderThen (a24 : ZMod p) {us : List JasminTy} {Γ : Ctxt jasminDialect}
    (pk : Var Γ (arrTy (4 + n))) (o : Var Γ (arrTy (6 * n)))
    (K : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ (arrTy (6 * n)) →
      NFProg jasminDialect Δ us) : NFProg jasminDialect Γ us :=
  nfThen (initBodyAt lo (p := p) 4 pk o) fun r vs =>
    .var (wConst 255) <|
    .forLoop .here (.cons vs.head.there .nil)
      (NFProg.ofCom (bitStepAt lo a24 (.there (.there (.there (r pk)))) (.there .here) .here
        |>.toComHead))
      (K (fun v => (r v).there.there) .here)

/-- **The ladder loop kernel** over the packed input `[k; u]` and an output array: `ladderThen`
    returning the final state array. -/
def ladderLoopBody (a24 : ZMod p) :
    NFProg jasminDialect [arrTy (4 + n), arrTy (6 * n)] [arrTy (6 * n)] :=
  ladderThen lo a24 .here (.there .here) fun _ w => .ret (.cons w .nil)

/-- The ladder state after the `255` steps at the bits `scalarBitAt K i` from `initF u`. -/
def ladderOut (a24 : ZMod p) {M : Nat} (K : Fin M → BitVec 64) (u : ZMod p) : LadderState p :=
  (List.range 255).foldl (fun s i => ladderStepF a24 (scalarBitAt K i) s) (initF u)

/-- A fold in `Option` of a step that maps the encoding of a state to the encoding of `F` at
    that state is `some` of the encoding of the pure fold of `F`. -/
theorem foldlM_encW {α : Type} (E : ZMod p → ListDenote (Rn n))
    (f : ListDenote [arrTy (6 * n)] → α → Option (ListDenote [arrTy (6 * n)]))
    (F : LadderState p → α → LadderState p)
    (hf : ∀ s i, f (HVector.cons (encW E s) .nil) i
      = some (HVector.cons (encW E (F s i)) .nil : ListDenote [arrTy (6 * n)])) :
    ∀ (l : List α) (s : LadderState p),
      List.foldlM (m := Option) f (HVector.cons (encW E s) .nil : ListDenote [arrTy (6 * n)]) l
        = some (HVector.cons (encW E (l.foldl F s)) .nil : ListDenote [arrTy (6 * n)])
  | [], _ => rfl
  | i :: l, s => by
      rw [List.foldlM_cons, hf]
      exact foldlM_encW E f F hf l (F s i)

variable (enc : (loweringOf lo).Enc)
  (Good : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}, Expr fieldDialect Γ t → Prop)
  (hsq : (loweringOf lo).BlockSquare enc Good)
  (hA : ∀ {Γ : Ctxt fieldDialect} (a b : Var Γ (FieldTy.fp p)), Good (eAdd a b))
  (hS : ∀ {Γ : Ctxt fieldDialect} (a b : Var Γ (FieldTy.fp p)), Good (eSub a b))
  (hM : ∀ {Γ : Ctxt fieldDialect} (a b : Var Γ (FieldTy.fp p)), Good (eMul a b))
  (hQ : ∀ {Γ : Ctxt fieldDialect} (a : Var Γ (FieldTy.fp p)), Good (eSq a))
  (hC : ∀ {Γ : Ctxt fieldDialect} (c : ZMod p),
    Good (EllipticCurveDialect.JacLower.eConst (Γ := Γ) c))
  (hn : 6 * n < 2 ^ 64)

include hsq hA hS hM hQ hC hn in
/-- One loop iteration at the packed input `K`, the index `iv` and the state `encW s`
    returns `encW (ladderStepF a24 (scalarBitAt K iv) s)`. -/
theorem bitStepAt_value (a24 : ZMod p) {M : Nat} {Δ : Ctxt jasminDialect}
    (pk : Var Δ (arrTy M)) (i : Var Δ w64) (w : Var Δ (arrTy (6 * n))) (W : Valuation Δ)
    (K : Fin M → BitVec 64) (iv : Nat) (s : LadderState p) (hpk : pk.lookup W = K)
    (hi : i.lookup W = BitVec.ofNat 64 iv) (hw : w.lookup W = encW (encF lo enc p) s) :
    (bitStepAt lo a24 pk i w).denote W
      = .cons (encW (encF lo enc p) (ladderStepF a24 (scalarBitAt K iv) s)) .nil := by
  refine scalarBitK_denote pk i _ W _ K iv hpk hi fun r bw W' pr hbw => ?_
  exact stepBodyAt_value lo enc Good hsq hA hS hM hQ hC hn a24 _ _ _ W' s _
    ((pr w).trans hw) hbw

include hsq hA hS hM hQ hC hn in
/-- At a packed input `K` whose words from index `4` are the limbs of `u`, `ladderThen`
    denotes its continuation at an array holding `encW (ladderOut a24 K u)`. -/
theorem ladderThen_denote (a24 : ZMod p) (fuel : Nat) {us : List JasminTy}
    {Γ : Ctxt jasminDialect} (pk : Var Γ (arrTy (4 + n))) (o : Var Γ (arrTy (6 * n)))
    (Kc : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ (arrTy (6 * n)) →
      NFProg jasminDialect Δ us)
    (W : Valuation Γ) (R : Option (ListDenote us)) (K : Fin (4 + n) → BitVec 64) (u : ZMod p)
    (hpk : pk.lookup W = K) (hu : arrLimbs K n 4 = encF lo enc p u)
    (hK : ∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (w : Var Δ (arrTy (6 * n)))
      (W' : Valuation Δ), Pres r W W' →
      w.lookup W' = encW (encF lo enc p) (ladderOut a24 K u) → (Kc r w).denote fuel W' = R) :
    (ladderThen lo a24 pk o Kc).denote fuel W = R := by
  refine nfThen_denote fuel _ _ _ _ fun r vs W' hr hv => ?_
  rw [initBodyAt_value lo enc Good hsq hC hn 4 (by omega) pk o W u (by rw [hpk]; exact hu)]
    at hv
  cases vs with
  | cons w rest =>
    cases rest
    injection hv with _ _ hw _
    change (NFProg.var (wConst 255) (NFProg.forLoop .here (.cons w.there .nil) _ _)).denote fuel W'
      = _
    rw [NFProg.denote_var, Expr.denoteM_option_eq_some]
    simp only [Option.bind_eq_bind, Option.bind_some, NFProg.denote_forLoop]
    have hcount : HasWord64.toNat (d := jasminDialect)
        (Var.here.lookup (W'.extend ((wConst 255).denote W' : BitVec 64))) = 255 := rfl
    have hinit : Expr.lookupArgs (HVector.cons w.there .nil)
        (W'.extend ((wConst 255).denote W' : BitVec 64))
        = (HVector.cons (encW (encF lo enc p) (initF u)) .nil : ListDenote [arrTy (6 * n)]) :=
      congrArg (fun a => (HVector.cons a .nil : ListDenote [arrTy (6 * n)])) hw
    rw [hcount, hinit, foldlM_encW (encF lo enc p) _
      (fun s i => ladderStepF a24 (scalarBitAt K i) s) ?hf, Option.bind_some]
    · exact hK _ _ _ (fun v => hr v) rfl
    intro s i
    have hb := bitStepAt_value lo enc Good hsq hA hS hM hQ hC hn a24
      ((r pk).there.there.there) (Var.there Var.here) Var.here
      (hvAppend (HVector.cons (encW (encF lo enc p) s) .nil)
        (HVector.cons (HasWord64.ofNat (d := jasminDialect) i)
          (W'.extend ((wConst 255).denote W' : BitVec 64))))
      K i s (by exact (hr pk).trans hpk) rfl rfl
    rw [NFProg.denote_ofCom, MultiReturnCom.toComHead_denote, hb]
    rfl

include hsq hA hS hM hQ hC hn in
/-- **Value of the ladder loop kernel**: at a packed input `K` whose words from index `4` are
    the limbs of `u`, the loop returns the encoding of the `255`-step fold of `ladderStepF` at
    the bits `scalarBitAt K i` from `initF u`. -/
theorem ladderLoopBody_value (a24 : ZMod p) (fuel : Nat) (K : Fin (4 + n) → BitVec 64)
    (O : Fin (6 * n) → BitVec 64) (u : ZMod p) (hu : arrLimbs K n 4 = encF lo enc p u) :
    (ladderLoopBody lo a24).denote fuel (.cons K (.cons O .nil))
      = some (.cons (encW (encF lo enc p) ((List.range 255).foldl
          (fun s i => ladderStepF a24 (scalarBitAt K i) s) (initF u))) .nil) :=
  ladderThen_denote lo enc Good hsq hA hS hM hQ hC hn a24 fuel .here (.there .here) _ _ _ K u
    rfl hu fun _ w W' _ hw => by
      rw [NFProg.denote_ret]
      exact congrArg (fun a => some (HVector.cons a .nil : ListDenote [arrTy (6 * n)])) hw

end Loop

/-! ## 9. The inversion chain over `ZMod p` -/

/-- A slot of the ladder state. -/
inductive Slot
  /-- The slot of `u`. -/
  | u
  /-- The slot of `x2`. -/
  | x2
  /-- The slot of `z2`. -/
  | z2
  /-- The slot of `x3`. -/
  | x3
  /-- The slot of `z3`. -/
  | z3
  /-- The slot of `t`. -/
  | t
  deriving DecidableEq

/-- The element of a ladder state at a slot. -/
def LadderState.get (s : LadderState p) : Slot → ZMod p
  | .u => s.u
  | .x2 => s.x2
  | .z2 => s.z2
  | .x3 => s.x3
  | .z3 => s.z3
  | .t => s.t

/-- The ladder state with the element at a slot replaced by `v`. -/
def LadderState.set (s : LadderState p) : Slot → ZMod p → LadderState p
  | .u, v => { s with u := v }
  | .x2, v => { s with x2 := v }
  | .z2, v => { s with z2 := v }
  | .x3, v => { s with x3 := v }
  | .z3, v => { s with z3 := v }
  | .t, v => { s with t := v }

/-- A field operation between slots: a squaring or a product into a destination slot. -/
inductive FOp
  /-- `d ← a²`. -/
  | sq (a d : Slot)
  /-- `d ← a · b`. -/
  | mul (a b d : Slot)

/-- An operation of an inversion chain: a field operation between slots, or `k` squarings of
    the accumulator `t` in a counted loop. -/
inductive ChainOp
  /-- A field operation between slots. -/
  | op (o : FOp)
  /-- `t ← t ^ (2 ^ k)` by `k` squarings. -/
  | sqn (k : Nat)

/-- The field operation over `ZMod p`. -/
def FOp.apply (o : FOp) (s : LadderState p) : LadderState p :=
  match o with
  | .sq a d => s.set d (s.get a * s.get a)
  | .mul a b d => s.set d (s.get a * s.get b)

/-- The chain operation over `ZMod p`. -/
def ChainOp.apply : ChainOp → LadderState p → LadderState p
  | .op o, s => o.apply s
  | .sqn k, s => { s with t := s.t ^ 2 ^ k }

/-- A chain of operations over `ZMod p`, applied from the left. -/
def chainF (ops : List ChainOp) (s : LadderState p) : LadderState p :=
  ops.foldl (fun s o => o.apply s) s

/-- **The inversion chain of `2^255 - 19`** (ref10 `fe_invert`, fiat-crypto): `z2 ^ (2^255 - 21)`
    into `t`, by runs of `1, 2, 1, 5, 10, 20, 10, 50, 100, 50, 5` squarings and `11` products,
    with `u`, `x3`, `z3`, `t` as temporaries and `x2`, `z2` kept. -/
def invChain : List ChainOp :=
  [.op (.sq .z2 .u), .op (.sq .u .t), .sqn 1, .op (.mul .t .z2 .x3), .op (.mul .x3 .u .z3),
    .op (.sq .z3 .t), .op (.mul .t .x3 .u),
    .op (.sq .u .t), .sqn 4, .op (.mul .t .u .x3),
    .op (.sq .x3 .t), .sqn 9, .op (.mul .t .x3 .u),
    .op (.sq .u .t), .sqn 19, .op (.mul .t .u .t),
    .sqn 10, .op (.mul .t .x3 .u),
    .op (.sq .u .t), .sqn 49, .op (.mul .t .u .x3),
    .op (.sq .x3 .t), .sqn 99, .op (.mul .t .x3 .t),
    .sqn 50, .op (.mul .t .u .t),
    .sqn 5, .op (.mul .t .z3 .t)]

/-- `k` squarings of the accumulator raise it to the power `2 ^ k`. -/
theorem foldl_sqF (k : Nat) (s : LadderState p) :
    (List.range k).foldl (fun s _ => sqF s) s = { s with t := s.t ^ 2 ^ k } := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, sqF, pow_succ 2 k, pow_mul, sq]

/-- **The inversion chain computes `z2 ^ (2^255 - 21)`** into `t` and keeps `x2`. -/
theorem chainF_invChain (s : LadderState p) :
    (chainF invChain s).x2 = s.x2 ∧ (chainF invChain s).t = s.z2 ^ (2 ^ 255 - 21) := by
  have he : (2 : ℕ) ^ 255 - 21 =
      57896044618658097711785492504343953926634992332820282019728792003956564819947 := by
    norm_num
  simp only [chainF, invChain, List.foldl_cons, List.foldl_nil, ChainOp.apply, FOp.apply,
    LadderState.get, LadderState.set, he]
  exact ⟨trivial, by ring⟩

/-- At a prime `p = 2^255 - 19`, `z ^ (2^255 - 21)` is `z⁻¹` (and `0` at `z = 0`). -/
theorem pow_invExp_eq_inv (hp : p = 2 ^ 255 - 19) [Fact p.Prime] (z : ZMod p) :
    z ^ (2 ^ 255 - 21) = z⁻¹ := by
  have he : (2 : ℕ) ^ 255 - 21 = p - 2 := by subst hp; norm_num
  rw [he]
  rcases eq_or_ne z 0 with rfl | hz
  · rw [inv_zero, zero_pow (by subst hp; norm_num)]
  · apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, show p - 2 + 1 = p - 1 by subst hp; norm_num]
    exact ZMod.pow_card_sub_one_eq_one hz

/-! ## 10. The inversion chain and the X25519 kernel over a record -/

namespace LimbSt

variable {n : Nat}

/-- The limb vector of a slot. -/
def get {Δ : Ctxt jasminDialect} (h : LimbSt n Δ) : Slot → Ctxt.Hom (Rn n) Δ
  | .u => h.u
  | .x2 => h.x2
  | .z2 => h.z2
  | .x3 => h.x3
  | .z3 => h.z3
  | .t => h.t

/-- The limb state with the limb vector of a slot replaced by `x`. -/
def set {Δ : Ctxt jasminDialect} (h : LimbSt n Δ) : Slot → Ctxt.Hom (Rn n) Δ → LimbSt n Δ
  | .u, x => { h with u := x }
  | .x2, x => { h with x2 := x }
  | .z2, x => { h with z2 := x }
  | .x3, x => { h with x3 := x }
  | .z3, x => { h with z3 := x }
  | .t, x => { h with t := x }

/-- A limb state of `s` holds the limbs of `s.get i` at the slot `i`. -/
theorem Holds.get {Δ : Ctxt jasminDialect} {E : ZMod p → ListDenote (Rn n)} {h : LimbSt n Δ}
    {W : Valuation Δ} {s : LadderState p} (hh : h.Holds E W s) (i : Slot) :
    pullV (h.get i) W = E (s.get i) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hh
  cases i <;> assumption

/-- Replacing the limbs of a slot by limbs of `v` gives a limb state of `s.set i v`. -/
theorem Holds.set {Δ : Ctxt jasminDialect} {E : ZMod p → ListDenote (Rn n)} {h : LimbSt n Δ}
    {W : Valuation Δ} {s : LadderState p} (hh : h.Holds E W s) (i : Slot)
    {x : Ctxt.Hom (Rn n) Δ} {v : ZMod p} (hx : pullV x W = E v) :
    (h.set i x).Holds E W (s.set i v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hh
  cases i
  exacts [⟨hx, h2, h3, h4, h5, h6⟩, ⟨h1, hx, h3, h4, h5, h6⟩, ⟨h1, h2, hx, h4, h5, h6⟩,
    ⟨h1, h2, h3, hx, h5, h6⟩, ⟨h1, h2, h3, h4, hx, h6⟩, ⟨h1, h2, h3, h4, h5, hx⟩]

end LimbSt

section Chain

variable {n : Nat} (lo : LimbBlocks n)

/-- A field operation between slots on a limb state: the lowering of `sqProg` or `finProg` by
    the blocks of `lo` at the source slots, stored as the limbs of the destination slot. -/
def fopSt (o : FOp) {bs : List JasminTy} {Δ : Ctxt jasminDialect} (h : LimbSt n Δ)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → LimbSt n Δ' → MC Δ' bs) : MC Δ bs :=
  match o with
  | .sq a d => (loweringOf lo).lowerRM (Γ := fctx p 1) (ts := fctx p 1)
      (appendHom (h.get a) nilHom) (sqProg p) fun r vs =>
        k r ((h.map r).set d (hdHom (hvToHom vs)))
  | .mul a b d => (loweringOf lo).lowerRM (Γ := fctx p 2) (ts := fctx p 1)
      (appendHom (h.get a) (appendHom (h.get b) nilHom)) (finProg p) fun r vs =>
        k r ((h.map r).set d (hdHom (hvToHom vs)))

/-- A field operation between slots at the variables `w`, `o`: the loads of the state array,
    `fopSt`, the stores into `o`. -/
def fopBodyAt (o : FOp) {Δ : Ctxt jasminDialect} (w o' : Var Δ (arrTy (6 * n))) :
    MC Δ [arrTy (6 * n)] :=
  loadSt w fun r₀ h₀ => fopSt lo (p := p) o h₀ fun r₁ h₁ => storeSt (r₁ (r₀ o')) h₁

/-- **A chain on the state array `w` with a continuation**: a field operation is `fopBodyAt`
    in place; `sqn k` is a counted loop of `k` trips of `sqBodyAt` on the carried state array,
    with the trip count a literal. The continuation receives the renaming of the context and
    the final state array. -/
def chainThen {us : List JasminTy} : (ops : List ChainOp) → {Γ : Ctxt jasminDialect} →
    Var Γ (arrTy (6 * n)) →
    (∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ (arrTy (6 * n)) →
      NFProg jasminDialect Δ us) → NFProg jasminDialect Γ us
  | [], _, w, K => K (fun v => v) w
  | .op o :: ops, _, w, K =>
    nfThen (fopBodyAt lo (p := p) o w w) fun r vs =>
      chainThen ops vs.head fun r' w' => K (fun v => r' (r v)) w'
  | .sqn k :: ops, _, w, K =>
    .var (wConst k) <|
    .forLoop .here (.cons w.there .nil)
      (NFProg.ofCom (sqBodyAt lo (p := p) .here .here |>.toComHead))
      (chainThen ops .here fun r' w' => K (fun v => r' v.there.there) w')

/-- The context of the X25519 kernel: the packed input `[k; u]`, the state array and the output
    array of `n` words. -/
abbrev x25519Ctx (n : Nat) : Ctxt jasminDialect := [arrTy (4 + n), arrTy (6 * n), arrTy n]

/-- **The X25519 kernel body** over the record `lo` at the constant `a24`: the ladder loop
    `ladderThen` on the state array, the inversion chain `invChain` of `z2` into `t`, and the
    output `x2 · t` into the output array. -/
def x25519Body (a24 : ZMod p) : NFProg jasminDialect (x25519Ctx n) [arrTy n] :=
  ladderThen lo a24 .here (.there .here) fun r w =>
  chainThen lo (p := p) invChain w fun r' w' =>
  nfThen (finBodyAt lo (p := p) w' (r' (r (.there (.there .here))))) fun _ vs => .ret vs

/-- The chain of the two-array X25519 kernel: `invChain`, then the product `x2 · t` into `t`. -/
def x25519Chain : List ChainOp := invChain ++ [.op (.mul .x2 .t .t)]

/-- The ladder state returned by the two-array X25519 kernel: `x25519Chain` applied to the
    ladder state `ladderOut a24 K u`. -/
def x25519Out (a24 : ZMod p) {M : Nat} (K : Fin M → BitVec 64) (u : ZMod p) : LadderState p :=
  chainF x25519Chain (ladderOut a24 K u)

/-- **The two-array X25519 kernel body** over the record `lo` at the constant `a24`, with the
    parameters of `ladderLoopBody`: the ladder loop `ladderThen` on the state array, then the
    chain `x25519Chain` (the inversion chain of `z2` into `t` and the product `x2 · t` into
    `t`) in place, returning the state array. -/
def x25519Body2 (a24 : ZMod p) :
    NFProg jasminDialect [arrTy (4 + n), arrTy (6 * n)] [arrTy (6 * n)] :=
  ladderThen lo a24 .here (.there .here) fun _ w =>
  chainThen lo (p := p) x25519Chain w fun _ w' => .ret (.cons w' .nil)

/-- The slot `t` of `x25519Out a24 K u` is `x2 · z2 ^ (2^255 - 21)` of `ladderOut a24 K u`. -/
theorem x25519Out_get_t (a24 : ZMod p) {M : Nat} (K : Fin M → BitVec 64) (u : ZMod p) :
    (x25519Out a24 K u).get .t
      = (ladderOut a24 K u).x2 * (ladderOut a24 K u).z2 ^ (2 ^ 255 - 21) := by
  obtain ⟨h1, h2⟩ := chainF_invChain (ladderOut a24 K u)
  change (chainF invChain (ladderOut a24 K u)).x2 * (chainF invChain (ladderOut a24 K u)).t = _
  rw [h1, h2]

variable (enc : (loweringOf lo).Enc)
  (Good : ∀ {Γ : Ctxt fieldDialect} {t : FieldTy}, Expr fieldDialect Γ t → Prop)
  (hsq : (loweringOf lo).BlockSquare enc Good)
  (hA : ∀ {Γ : Ctxt fieldDialect} (a b : Var Γ (FieldTy.fp p)), Good (eAdd a b))
  (hS : ∀ {Γ : Ctxt fieldDialect} (a b : Var Γ (FieldTy.fp p)), Good (eSub a b))
  (hM : ∀ {Γ : Ctxt fieldDialect} (a b : Var Γ (FieldTy.fp p)), Good (eMul a b))
  (hQ : ∀ {Γ : Ctxt fieldDialect} (a : Var Γ (FieldTy.fp p)), Good (eSq a))
  (hC : ∀ {Γ : Ctxt fieldDialect} (c : ZMod p),
    Good (EllipticCurveDialect.JacLower.eConst (Γ := Γ) c))
  (hn : 6 * n < 2 ^ 64)

include hsq hM hQ in
/-- Under the block square, `fopSt o` maps a limb state of `s` to one of `o.apply s`. -/
theorem fopSt_denote (o : FOp) {bs : List JasminTy} {Δ : Ctxt jasminDialect} (h : LimbSt n Δ)
    (k : ∀ {Δ' : Ctxt jasminDialect}, Ctxt.Hom Δ Δ' → LimbSt n Δ' → MC Δ' bs)
    (W : Valuation Δ) (G : ListDenote bs) (s : LadderState p)
    (hh : h.Holds (encF lo enc p) W s)
    (hk : ∀ {Δ' : Ctxt jasminDialect} (r : Ctxt.Hom Δ Δ') (h' : LimbSt n Δ')
      (W' : Valuation Δ'), Pres r W W' → h'.Holds (encF lo enc p) W' (o.apply s) →
      (k r h').denote W' = G) :
    (fopSt lo (p := p) o h k).denote W = G := by
  cases o with
  | sq a d =>
    rw [fopSt]
    refine (loweringOf lo).lowerRM_denote_on enc Good hsq _ (sqProg p) _ W
      (.cons (s.get a) .nil) G (sqProg_covered Good hQ) ?_ fun r vs W' hr hvs => ?_
    · rw [pullV_appendHom, hh.get a]
      rfl
    · rw [sqProg_denote] at hvs
      exact hk r _ W' hr
        ((hh.map hr).set d (pullV_hdHom _ W' _ _ ((pullV_hvToHom W' vs).trans hvs)))
  | mul a b d =>
    rw [fopSt]
    refine (loweringOf lo).lowerRM_denote_on enc Good hsq _ (finProg p) _ W
      (.cons (s.get a) (.cons (s.get b) .nil)) G (finProg_covered Good hM) ?_
      fun r vs W' hr hvs => ?_
    · rw [pullV_appendHom, pullV_appendHom, hh.get a, hh.get b]
      rfl
    · rw [finProg_denote] at hvs
      exact hk r _ W' hr
        ((hh.map hr).set d (pullV_hdHom _ W' _ _ ((pullV_hvToHom W' vs).trans hvs)))

include hsq hM hQ hn in
/-- A field operation at a variable holding `encW s` returns `encW (o.apply s)`. -/
theorem fopBodyAt_value (o : FOp) {Δ : Ctxt jasminDialect} (w o' : Var Δ (arrTy (6 * n)))
    (W : Valuation Δ) (s : LadderState p) (hw : w.lookup W = encW (encF lo enc p) s) :
    (fopBodyAt lo (p := p) o w o').denote W = .cons (encW (encF lo enc p) (o.apply s)) .nil := by
  refine loadSt_denote _ hn w _ W _ s hw fun r₀ h₀ W₀ p₀ hh₀ => ?_
  refine fopSt_denote lo enc Good hsq hM hQ o h₀ _ W₀ _ s hh₀ fun r₁ h₁ W₁ p₁ hh₁ => ?_
  exact storeSt_denote _ hn _ h₁ W₁ _ hh₁

include hsq hM hQ hn in
/-- **A chain on an array holding `encW s`** denotes its continuation at an array holding
    `encW (chainF ops s)`, when every loop count of the chain is below `2 ^ 64`. -/
theorem chainThen_denote (fuel : Nat) {us : List JasminTy} :
    ∀ (ops : List ChainOp) {Γ : Ctxt jasminDialect} (w : Var Γ (arrTy (6 * n)))
      (Kc : ∀ {Δ : Ctxt jasminDialect}, Ctxt.Hom Γ Δ → Var Δ (arrTy (6 * n)) →
        NFProg jasminDialect Δ us)
      (W : Valuation Γ) (R : Option (ListDenote us)) (s : LadderState p),
      (∀ k, ChainOp.sqn k ∈ ops → k < 2 ^ 64) →
      w.lookup W = encW (encF lo enc p) s →
      (∀ {Δ : Ctxt jasminDialect} (r : Ctxt.Hom Γ Δ) (w' : Var Δ (arrTy (6 * n)))
        (W' : Valuation Δ), Pres r W W' →
        w'.lookup W' = encW (encF lo enc p) (chainF ops s) → (Kc r w').denote fuel W' = R) →
      (chainThen lo (p := p) ops w Kc).denote fuel W = R
  | [], _, w, _, W, _, _, _, hw, hK => hK (fun v => v) w W (Pres.id W) hw
  | .op o :: ops, _, w, Kc, W, R, s, hops, hw, hK => by
    refine nfThen_denote fuel _ _ _ _ fun r vs W' hr hv => ?_
    rw [fopBodyAt_value lo enc Good hsq hM hQ hn o w w W s hw] at hv
    cases vs with
    | cons w' rest =>
      cases rest
      injection hv with _ _ hw' _
      exact chainThen_denote fuel ops w' _ W' R (o.apply s)
        (fun k hk => hops k (List.mem_cons_of_mem _ hk)) hw'
        fun r' w'' W'' hr' hw'' => hK _ w'' W'' (Pres.comp hr hr') hw''
  | .sqn k :: ops, _, w, Kc, W, R, s, hops, hw, hK => by
    have hk : k < 2 ^ 64 := hops k List.mem_cons_self
    change (NFProg.var (wConst k) (NFProg.forLoop .here (.cons w.there .nil) _ _)).denote fuel W
      = R
    rw [NFProg.denote_var, Expr.denoteM_option_eq_some]
    simp only [Option.bind_eq_bind, Option.bind_some, NFProg.denote_forLoop]
    have hcount : HasWord64.toNat (d := jasminDialect)
        (Var.here.lookup (W.extend ((wConst k).denote W : BitVec 64))) = k := by
      change (BitVec.ofNat 64 k).toNat = k
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hk
    have hinit : Expr.lookupArgs (HVector.cons w.there .nil)
        (W.extend ((wConst k).denote W : BitVec 64))
        = (HVector.cons (encW (encF lo enc p) s) .nil : ListDenote [arrTy (6 * n)]) :=
      congrArg (fun a => (HVector.cons a .nil : ListDenote [arrTy (6 * n)])) hw
    rw [hcount, hinit, foldlM_encW (encF lo enc p) _ (fun s _ => sqF s) ?hf, foldl_sqF,
      Option.bind_some]
    · exact chainThen_denote fuel ops .here _ _ R _
        (fun k' hk' => hops k' (List.mem_cons_of_mem _ hk')) rfl
        fun r' w'' W'' hr' hw'' => hK _ w'' W'' (fun v => hr' v.there.there) hw''
    intro s' i
    have hb := sqBodyAt_value lo enc Good hsq hQ hn Var.here Var.here
      (hvAppend (HVector.cons (encW (encF lo enc p) s') .nil)
        (HVector.cons (HasWord64.ofNat (d := jasminDialect) i)
          (W.extend ((wConst k).denote W : BitVec 64)))) s' rfl
    rw [NFProg.denote_ofCom, MultiReturnCom.toComHead_denote, hb]
    rfl

/-- Every loop count of `invChain` is below `2 ^ 64`. -/
theorem invChain_counts : ∀ k, ChainOp.sqn k ∈ invChain → k < 2 ^ 64 := by
  intro k hk
  simp only [invChain, List.mem_cons, reduceCtorEq, ChainOp.sqn.injEq, false_or,
    List.not_mem_nil, or_false] at hk
  omega

/-- Every loop count of `x25519Chain` is below `2 ^ 64`. -/
theorem x25519Chain_counts : ∀ k, ChainOp.sqn k ∈ x25519Chain → k < 2 ^ 64 := by
  intro k hk
  rw [x25519Chain, List.mem_append] at hk
  rcases hk with hk | hk
  · exact invChain_counts k hk
  · simp at hk

include hsq hA hS hM hQ hC hn in
/-- **Value of the X25519 kernel**: at a packed input `K` whose words from index `4` are the
    limbs of `u`, any state array and any output array, the kernel returns the `n` limbs of
    `x2 · z2 ^ (2^255 - 21)` of the ladder state `ladderOut a24 K u`. -/
theorem x25519Body_value (a24 : ZMod p) (fuel : Nat) (K : Fin (4 + n) → BitVec 64)
    (O : Fin (6 * n) → BitVec 64) (Out : Fin n → BitVec 64) (u : ZMod p)
    (hu : arrLimbs K n 4 = encF lo enc p u) :
    (x25519Body lo a24).denote fuel (.cons K (.cons O (.cons Out .nil)))
      = some (.cons (encN (encF lo enc p)
          ((ladderOut a24 K u).x2 * (ladderOut a24 K u).z2 ^ (2 ^ 255 - 21))) .nil) := by
  refine ladderThen_denote lo enc Good hsq hA hS hM hQ hC hn a24 fuel .here (.there .here) _ _ _
    K u rfl hu fun r w W' hr hw => ?_
  refine chainThen_denote lo enc Good hsq hM hQ hn fuel invChain w _ W' _ _ invChain_counts hw
    fun r' w' W'' hr' hw' => ?_
  refine nfThen_denote fuel _ _ _ _ fun _ vs W₃ _ hv => ?_
  rw [finBodyAt_value lo enc Good hsq hM hn w' _ W'' _ hw', finF, (chainF_invChain _).1,
    (chainF_invChain _).2] at hv
  rw [NFProg.denote_ret, ← hv, lookupVars_eq_lookupArgs]

include hsq hA hS hM hQ hC hn in
/-- **Value of the X25519 kernel at `p = 2^255 - 19`**: the kernel returns the `n` limbs of
    `x2 · z2⁻¹` of the ladder state `ladderOut a24 K u` (`0` at `z2 = 0`, as RFC 7748). -/
theorem x25519Body_value_inv (hp : p = 2 ^ 255 - 19) [Fact p.Prime] (a24 : ZMod p) (fuel : Nat)
    (K : Fin (4 + n) → BitVec 64) (O : Fin (6 * n) → BitVec 64) (Out : Fin n → BitVec 64)
    (u : ZMod p) (hu : arrLimbs K n 4 = encF lo enc p u) :
    (x25519Body lo a24).denote fuel (.cons K (.cons O (.cons Out .nil)))
      = some (.cons (encN (encF lo enc p)
          ((ladderOut a24 K u).x2 * (ladderOut a24 K u).z2⁻¹)) .nil) := by
  rw [x25519Body_value lo enc Good hsq hA hS hM hQ hC hn a24 fuel K O Out u hu,
    pow_invExp_eq_inv hp]

include hsq hA hS hM hQ hC hn in
/-- **Value of the two-array X25519 kernel**: at a packed input `K` whose words from index `4`
    are the limbs of `u` and any state array, the kernel returns the state array `encW` of
    `x25519Out a24 K u`, whose slot `t` (words `5n .. 6n - 1`) is
    `x2 · z2 ^ (2^255 - 21)` of the ladder state `ladderOut a24 K u`. -/
theorem x25519Body2_value (a24 : ZMod p) (fuel : Nat) (K : Fin (4 + n) → BitVec 64)
    (O : Fin (6 * n) → BitVec 64) (u : ZMod p) (hu : arrLimbs K n 4 = encF lo enc p u) :
    (x25519Body2 lo a24).denote fuel (.cons K (.cons O .nil))
      = some (.cons (encW (encF lo enc p) (x25519Out a24 K u)) .nil) ∧
    (x25519Out a24 K u).get .t
      = (ladderOut a24 K u).x2 * (ladderOut a24 K u).z2 ^ (2 ^ 255 - 21) := by
  refine ⟨?_, x25519Out_get_t a24 K u⟩
  refine ladderThen_denote lo enc Good hsq hA hS hM hQ hC hn a24 fuel .here (.there .here) _ _ _
    K u rfl hu fun _ w W' _ hw => ?_
  refine chainThen_denote lo enc Good hsq hM hQ hn fuel x25519Chain w _ W' _ _
    x25519Chain_counts hw fun _ w' _ _ hw' => ?_
  rw [NFProg.denote_ret]
  exact congrArg (fun a => some (HVector.cons a .nil : ListDenote [arrTy (6 * n)])) hw'

include hsq hA hS hM hQ hC hn in
/-- **Value of the two-array X25519 kernel at `p = 2^255 - 19`**: the kernel returns the state
    array `encW` of `x25519Out a24 K u`, whose slot `t` is `x2 · z2⁻¹` of the ladder state
    `ladderOut a24 K u` (`0` at `z2 = 0`, as RFC 7748). -/
theorem x25519Body2_value_inv (hp : p = 2 ^ 255 - 19) [Fact p.Prime] (a24 : ZMod p)
    (fuel : Nat) (K : Fin (4 + n) → BitVec 64) (O : Fin (6 * n) → BitVec 64) (u : ZMod p)
    (hu : arrLimbs K n 4 = encF lo enc p u) :
    (x25519Body2 lo a24).denote fuel (.cons K (.cons O .nil))
      = some (.cons (encW (encF lo enc p) (x25519Out a24 K u)) .nil) ∧
    (x25519Out a24 K u).get .t = (ladderOut a24 K u).x2 * (ladderOut a24 K u).z2⁻¹ := by
  rw [← pow_invExp_eq_inv hp]
  exact x25519Body2_value lo enc Good hsq hA hS hM hQ hC hn a24 fuel K O u hu

end Chain

end CatCrypt.Crypto.SecureCompilation.CurveTemplate.MontLadder
