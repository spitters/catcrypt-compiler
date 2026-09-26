/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalarDenote
public import CatCrypt.Crypto.Jasmin.Ed25519Spec

/-!
# Bulletproofs inner-product-argument prover orchestration

The Bulletproofs prover's hot path is the inner-product-argument (IPA)
reduction. Each round splits the witness `a` and the generators `G` into low
and high halves, computes the cross commitments `L = ⟨a_lo, G_hi⟩` and
`R = ⟨a_hi, G_lo⟩`, derives the Fiat–Shamir challenge `x = H(L, R)`, and folds

```
  a' = x · a_lo + x⁻¹ · a_hi        G' = x⁻¹ · G_lo + x · G_hi
```

halving the length. After `log₂ n` rounds the witness is one scalar, which the
prover sends together with the initial commitment `P = ⟨a, G⟩` and the pairs
`(L, R)`. The witness fold is the fold `x · lo + x⁻¹ · hi` of the Bulletproofs
paper, and with this generator fold `⟨a', G'⟩ = x² L + ⟨a, G⟩ + x⁻² R`.

## Contents

* §1 `ipaProve` — the prover over any field `F`, additive group `G`, scalar
  action `smul : F → G → G` and challenge function `H : G → G → F`, for
  vectors of length `2 ^ k`.
* §2 The leaf functions `ipa_commit`, `ipa_cross_L`, `ipa_cross_R`,
  `ipa_squeeze`, `ipa_fold_wit`, `ipa_fold_gen`, `ipa_final` (definitions),
  their `@[rust_cmd_pattern]` registrations, and the `n = 8` orchestration
  `ipaProverLean8`, with `ipaProverLean8_eq_ipaProve`.
* §3 The wire encoding: an `IpaCodec` packs a scalar and a group element into
  four 64-bit limbs each, with decode ∘ encode the identity. A naming
  `nm : IpaLeafNames` gives each leaf call (`IpaLeaf`) its `LowCT` name;
  `ipaLeafOracleN nm` is the leaf oracle that decodes the arguments of a leaf
  call, applies the leaf and encodes the result, and `ipaLeafOracle` is its
  instance at the Bulletproofs names `bulletproofsIpaNames`.
* §4 `ipaProverBodyN nm`, the `LowCT` body of the `n = 8` prover that the front
  lowers, `ipaProverBody8` at the Bulletproofs names, and `ipaProver8Reified`.
* §5 `ipaProverBodyN_computes`: for every naming whose call names denote their
  leaves, and every codec, scalar action, challenge function and input, the
  body run under `semScalarL` at `ipaLeafOracleN nm` leaves the encodings of
  `ipaProve … 3 a g` in the slots `P`, `L0`–`R2` and `__result`.
  `ipaProverBodyN_denote` carries this through `translateDialectControl` to the
  denotation of the emitted `Com`; `ipaProverBody8_computes` and
  `ipaProverBody8_denote` are the Bulletproofs instances. `Halo2IPAProverReflect`
  instantiates the same statements at the Pallas group.
* §6 The instance at the edwards25519 group `EdPt` with scalars `ZMod L`
  and the action `lsmul`: `ed25519IpaCodec` encodes a scalar as its
  little-endian 32-byte residue and a point in the RFC 8032 compressed form,
  and `ipaProverBody8_computes_ed25519` is §5 at this codec.

The challenge function `H` and the scalar action are parameters: the
statement holds for every `H`, and the action on `EdPt` is `lsmul`.

## References

* Bünz, Bootle, Boneh, Poelstra, Wuille, Maxwell — *Bulletproofs: Short Proofs
  for Confidential Transactions and More*, IEEE S&P 2018.
* `CatCrypt/Crypto/SecureCompilation/Dialects/TranslateDialectScalarDenote.lean`
  (`semScalarL`, `translateDialectControl_denoteWith`).
* `CatCrypt/Crypto/Jasmin/Ed25519Spec.lean` (`lsmul`, `ed_decompress_spec`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.BulletproofsIPA

/-! ## 1. Specification -/

section Spec

variable {F G : Type} [Field F] [AddCommGroup G]

/-- The inner product `⟨a, g⟩ = Σᵢ aᵢ · gᵢ` of a scalar vector and a group vector. -/
def ipaInner (smul : F → G → G) {n : ℕ} (a : Fin n → F) (g : Fin n → G) : G :=
  ∑ i, smul (a i) (g i)

/-- The first half `v₀ … v_{n-1}` of a vector of length `2n`. -/
def loHalf {α : Type} {n : ℕ} (v : Fin (2 * n) → α) : Fin n → α :=
  fun i => v ⟨i.1, by have := i.2; omega⟩

/-- The second half `v_n … v_{2n-1}` of a vector of length `2n`. -/
def hiHalf {α : Type} {n : ℕ} (v : Fin (2 * n) → α) : Fin n → α :=
  fun i => v ⟨n + i.1, by have := i.2; omega⟩

/-- The witness fold `x · a_lo + x⁻¹ · a_hi`. -/
def foldWit {n : ℕ} (a : Fin (2 * n) → F) (x : F) : Fin n → F :=
  fun i => x * loHalf a i + x⁻¹ * hiHalf a i

/-- The generator fold `x⁻¹ · G_lo + x · G_hi`. -/
def foldGen (smul : F → G → G) {n : ℕ} (g : Fin (2 * n) → G) (x : F) : Fin n → G :=
  fun i => smul x⁻¹ (loHalf g i) + smul x (hiHalf g i)

/-- A vector of length `2 ^ (k + 1)` read as a vector of length `2 · 2 ^ k`. -/
def halve {α : Type} {k : ℕ} (v : Fin (2 ^ (k + 1)) → α) : Fin (2 * 2 ^ k) → α :=
  fun i => v (Fin.cast (Nat.pow_succ' (m := 2) (n := k)).symm i)

/-- An IPA proof: the initial commitment, the `(L, R)` pair of each round, and
    the final witness scalar. -/
structure IpaProof (F G : Type) where
  /-- The commitment `P = ⟨a, G⟩`. -/
  commitment : G
  /-- The cross commitments `(L, R)` of each round, first round first. -/
  rounds : List (G × G)
  /-- The length-one witness after the last fold. -/
  final : F

/-- The `k` rounds of the IPA reduction on vectors of length `2 ^ k`: the list of
    `(L, R)` pairs and the final witness scalar. -/
def ipaRounds (smul : F → G → G) (H : G → G → F) :
    (k : ℕ) → (Fin (2 ^ k) → F) → (Fin (2 ^ k) → G) → List (G × G) × F
  | 0, a, _ => ([], a ⟨0, by simp⟩)
  | k + 1, a, g =>
      let L := ipaInner smul (loHalf (halve a)) (hiHalf (halve g))
      let R := ipaInner smul (hiHalf (halve a)) (loHalf (halve g))
      let x := H L R
      let r := ipaRounds smul H k (foldWit (halve a) x) (foldGen smul (halve g) x)
      ((L, R) :: r.1, r.2)

/-- The Bulletproofs IPA prover on a witness and generators of length `2 ^ k`. -/
def ipaProve (smul : F → G → G) (H : G → G → F) (k : ℕ)
    (a : Fin (2 ^ k) → F) (g : Fin (2 ^ k) → G) : IpaProof F G :=
  { commitment := ipaInner smul a g
    rounds := (ipaRounds smul H k a g).1
    final := (ipaRounds smul H k a g).2 }

end Spec

end CatCrypt.Crypto.Jasmin.BulletproofsIPA

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.BulletproofsIPA

/-! ## 2. Leaves and the `n = 8` orchestration

Each leaf is one step of `ipaRounds`. The `LowCT` leaf names carry the vector
width a call acts on (`ipa_cross_L_8`, `ipa_fold_wit_4`, …). -/

/-- Initial commitment `P = ⟨a, G⟩`. -/
def ipa_commit {F G : Type} [Field F] [AddCommGroup G] (smul : F → G → G) {n : ℕ}
    (a : Fin n → F) (g : Fin n → G) : G :=
  ipaInner smul a g

/-- Left cross commitment `L = ⟨a_lo, G_hi⟩`. -/
def ipa_cross_L {F G : Type} [Field F] [AddCommGroup G] (smul : F → G → G) {n : ℕ}
    (a : Fin (2 * n) → F) (g : Fin (2 * n) → G) : G :=
  ipaInner smul (loHalf a) (hiHalf g)

/-- Right cross commitment `R = ⟨a_hi, G_lo⟩`. -/
def ipa_cross_R {F G : Type} [Field F] [AddCommGroup G] (smul : F → G → G) {n : ℕ}
    (a : Fin (2 * n) → F) (g : Fin (2 * n) → G) : G :=
  ipaInner smul (hiHalf a) (loHalf g)

/-- Fiat–Shamir challenge `H(L, R)`. -/
def ipa_squeeze {F G : Type} (H : G → G → F) (L R : G) : F := H L R

/-- Witness fold `x · a_lo + x⁻¹ · a_hi`, halving the length. -/
def ipa_fold_wit {F : Type} [Field F] {n : ℕ} (a : Fin (2 * n) → F) (x : F) : Fin n → F :=
  foldWit a x

/-- Generator fold `x⁻¹ · G_lo + x · G_hi`, halving the length. -/
def ipa_fold_gen {F G : Type} [Field F] [AddCommGroup G] (smul : F → G → G) {n : ℕ}
    (g : Fin (2 * n) → G) (x : F) : Fin n → G :=
  foldGen smul g x

/-- Final prover scalar of a length-one witness. -/
def ipa_final {F : Type} (a : Fin 1 → F) : F := a 0

@[rust_cmd_pattern]
def ipaCommit8Pattern : LowCTPattern where
  name := "ipa_commit_8"; fnHead := ``ipa_commit; arity := 2; towerType := .TBytes 32

@[rust_cmd_pattern]
def ipaCrossL8Pattern : LowCTPattern where
  name := "ipa_cross_L_8"; fnHead := ``ipa_cross_L; arity := 2; towerType := .TBytes 32

@[rust_cmd_pattern]
def ipaCrossR8Pattern : LowCTPattern where
  name := "ipa_cross_R_8"; fnHead := ``ipa_cross_R; arity := 2; towerType := .TBytes 32

@[rust_cmd_pattern]
def ipaSqueezePattern : LowCTPattern where
  name := "ipa_squeeze"; fnHead := ``ipa_squeeze; arity := 2; towerType := .TBytes 32

@[rust_cmd_pattern]
def ipaFoldWit4Pattern : LowCTPattern where
  name := "ipa_fold_wit_4"; fnHead := ``ipa_fold_wit; arity := 2; towerType := .TBytes 128

@[rust_cmd_pattern]
def ipaFoldGen4Pattern : LowCTPattern where
  name := "ipa_fold_gen_4"; fnHead := ``ipa_fold_gen; arity := 2; towerType := .TBytes 128

@[rust_cmd_pattern]
def ipaFinalPattern : LowCTPattern where
  name := "ipa_final"; fnHead := ``ipa_final; arity := 1; towerType := .TBytes 32

/-- The `n = 8` (three-round) IPA prover as a sequence of leaf calls, in the
    order of `ipaProverBody8`. -/
def ipaProverLean8 {F G : Type} [Field F] [AddCommGroup G] (smul : F → G → G)
    (H : G → G → F) (a : Fin 8 → F) (g : Fin 8 → G) : IpaProof F G :=
  let P := ipa_commit smul a g
  -- round 0 : 8 → 4
  let L0 := ipa_cross_L smul (n := 4) a g
  let R0 := ipa_cross_R smul (n := 4) a g
  let u0 := ipa_squeeze H L0 R0
  let a1 := ipa_fold_wit (n := 4) a u0
  let G1 := ipa_fold_gen smul (n := 4) g u0
  -- round 1 : 4 → 2
  let L1 := ipa_cross_L smul (n := 2) a1 G1
  let R1 := ipa_cross_R smul (n := 2) a1 G1
  let u1 := ipa_squeeze H L1 R1
  let a2 := ipa_fold_wit (n := 2) a1 u1
  let G2 := ipa_fold_gen smul (n := 2) G1 u1
  -- round 2 : 2 → 1
  let L2 := ipa_cross_L smul (n := 1) a2 G2
  let R2 := ipa_cross_R smul (n := 1) a2 G2
  let u2 := ipa_squeeze H L2 R2
  let a3 := ipa_fold_wit (n := 1) a2 u2
  { commitment := P, rounds := [(L0, R0), (L1, R1), (L2, R2)], final := ipa_final a3 }

/-- The leaf orchestration is the prover `ipaProve` at `k = 3`. -/
theorem ipaProverLean8_eq_ipaProve {F G : Type} [Field F] [AddCommGroup G]
    (smul : F → G → G) (H : G → G → F) (a : Fin 8 → F) (g : Fin 8 → G) :
    ipaProverLean8 smul H a g = ipaProve smul H 3 a g := rfl

end CatCrypt.Crypto.Jasmin.LowCTReflect

namespace CatCrypt.Crypto.Jasmin.BulletproofsIPA

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle
open CatCrypt.Crypto.Jasmin.LowCTReflect

/-! ## 3. Wire encoding and the leaf oracle

A scalar and a group element each occupy four 64-bit limbs (32 bytes). A vector
of `n` elements occupies `4n` limbs, element `j` in limbs `4j … 4j + 3`. -/

/-- Four 64-bit limbs. -/
abbrev Limbs4 : Type := Fin 4 → BitVec 64

/-- An encoding of scalars and group elements as four limbs, with decode ∘ encode
    the identity on both. -/
structure IpaCodec (F G : Type) where
  /-- Scalar encoding. -/
  encF : F → Limbs4
  /-- Scalar decoding. -/
  decF : Limbs4 → F
  /-- Group-element encoding. -/
  encG : G → Limbs4
  /-- Group-element decoding. -/
  decG : Limbs4 → G
  decF_encF : ∀ x, decF (encF x) = x
  decG_encG : ∀ P, decG (encG P) = P

/-- The limbs of a typed value: limb `i` of a `memref n` for `i < n`, and `0`
    elsewhere. -/
def slotLimbs : ((t : CryptoTy) × ⟦t⟧) → ℕ → BitVec 64
  | ⟨.memref n, v⟩, i => if h : i < n then v ⟨i, h⟩ else 0
  | _, _ => 0

/-- The value of type `t` holding the limb stream `s`: its first `n` limbs for
    `memref n`, and the default value for any other type. -/
def slotOf : (t : CryptoTy) → (ℕ → BitVec 64) → ⟦t⟧
  | .memref _, s => fun i => s i.1
  | t, _ => CryptoTy.default t

/-- The limb stream of one encoded element. -/
def elemStream (e : Limbs4) : ℕ → BitVec 64 :=
  fun i => if h : i < 4 then e ⟨i, h⟩ else 0

/-- The limb stream of an encoded vector: limb `i` is limb `i % 4` of element `i / 4`. -/
def vecStream {α : Type} {n : ℕ} (enc : α → Limbs4) (v : Fin n → α) : ℕ → BitVec 64 :=
  fun i => if h : i / 4 < n then enc (v ⟨i / 4, h⟩) ⟨i % 4, Nat.mod_lt _ (by decide)⟩ else 0

/-- The four limbs of element `j` of a stream. -/
def streamElem (s : ℕ → BitVec 64) (j : ℕ) : Limbs4 := fun i => s (4 * j + i.1)

/-- The vector of length `n` decoded from a stream. -/
def decVec {α : Type} {n : ℕ} (dec : Limbs4 → α) (s : ℕ → BitVec 64) : Fin n → α :=
  fun j => dec (streamElem s j.1)

theorem streamElem_elem (m : ℕ) (e : Limbs4) (hm : 4 ≤ m) :
    streamElem (slotLimbs ⟨.memref m, slotOf (.memref m) (elemStream e)⟩) 0 = e := by
  funext i
  have := i.2
  simp only [streamElem, slotLimbs, slotOf, elemStream, Nat.mul_zero, Nat.zero_add,
    dif_pos (show i.1 < m by omega), dif_pos i.2]

theorem decVec_vec {α : Type} {n : ℕ} (m : ℕ) (enc : α → Limbs4) (dec : Limbs4 → α)
    (hrt : ∀ x, dec (enc x) = x) (v : Fin n → α) (hm : 4 * n ≤ m) :
    decVec (n := n) dec (slotLimbs ⟨.memref m, slotOf (.memref m) (vecStream enc v)⟩) = v := by
  funext j
  have hj := j.2
  have hs : streamElem (slotLimbs ⟨.memref m, slotOf (.memref m) (vecStream enc v)⟩) j.1
      = enc (v j) := by
    funext i
    have hi := i.2
    have h1 : 4 * j.1 + i.1 < m := by omega
    have h2 : (4 * j.1 + i.1) / 4 < n := by omega
    simp only [streamElem, slotLimbs, slotOf, vecStream, dif_pos h1, dif_pos h2]
    congr 2
    · exact Fin.ext (by simp only; omega)
    · omega
  simp only [decVec, hs, hrt]

theorem decVec_vecF {F G : Type} (C : IpaCodec F G) {n : ℕ} (m : ℕ) (v : Fin n → F)
    (hm : 4 * n ≤ m) :
    decVec (n := n) C.decF (slotLimbs ⟨.memref m, slotOf (.memref m) (vecStream C.encF v)⟩)
      = v :=
  decVec_vec m C.encF C.decF C.decF_encF v hm

theorem decVec_vecG {F G : Type} (C : IpaCodec F G) {n : ℕ} (m : ℕ) (v : Fin n → G)
    (hm : 4 * n ≤ m) :
    decVec (n := n) C.decG (slotLimbs ⟨.memref m, slotOf (.memref m) (vecStream C.encG v)⟩)
      = v :=
  decVec_vec m C.encG C.decG C.decG_encG v hm

variable {F G : Type} [Field F] [AddCommGroup G]

/-- The limb stream of argument `j` of a leaf call. -/
def ipaArg (args : List ((t : CryptoTy) × ⟦t⟧)) (j : ℕ) : ℕ → BitVec 64 :=
  match args[j]? with
  | some p => slotLimbs p
  | none => fun _ => 0

/-- The leaf calls of the `n = 8` prover, by role and vector width: the cross
    commitments by the width they read, the folds by the width they write. -/
inductive IpaLeaf where
  | commit8
  | crossL8
  | crossR8
  | crossL4
  | crossR4
  | crossL2
  | crossR2
  | squeeze
  | foldWit4
  | foldWit2
  | foldWit1
  | foldGen4
  | foldGen2
  | final
  deriving DecidableEq

/-- Every leaf call, in body order. -/
def IpaLeaf.all : List IpaLeaf :=
  [.commit8, .crossL8, .crossR8, .crossL4, .crossR4, .crossL2, .crossR2, .squeeze,
    .foldWit4, .foldWit2, .foldWit1, .foldGen4, .foldGen2, .final]

/-- A naming of the leaf calls: the `LowCT` call name of each leaf. -/
abbrev IpaLeafNames : Type := IpaLeaf → String

/-- The leaf a call name denotes under the naming `nm`: the first leaf in
    `IpaLeaf.all` with that name, and `none` if no leaf has it. -/
def IpaLeafNames.leafOf (nm : IpaLeafNames) (name : String) : Option IpaLeaf :=
  IpaLeaf.all.find? (fun l => decide (nm l = name))

/-- The call names of the Bulletproofs leaves. -/
def bulletproofsIpaNames : IpaLeafNames
  | .commit8 => "ipa_commit_8"
  | .crossL8 => "ipa_cross_L_8"
  | .crossR8 => "ipa_cross_R_8"
  | .crossL4 => "ipa_cross_L_4"
  | .crossR4 => "ipa_cross_R_4"
  | .crossL2 => "ipa_cross_L_2"
  | .crossR2 => "ipa_cross_R_2"
  | .squeeze => "ipa_squeeze"
  | .foldWit4 => "ipa_fold_wit_4"
  | .foldWit2 => "ipa_fold_wit_2"
  | .foldWit1 => "ipa_fold_wit_1"
  | .foldGen4 => "ipa_fold_gen_4"
  | .foldGen2 => "ipa_fold_gen_2"
  | .final => "ipa_final"

theorem bulletproofsIpaNames_leafOf (l : IpaLeaf) :
    bulletproofsIpaNames.leafOf (bulletproofsIpaNames l) = some l := by
  cases l <;> simp [IpaLeafNames.leafOf, IpaLeaf.all, bulletproofsIpaNames]

/-- The result stream of the leaf `l` on the argument streams `s0`, `s1`: decode
    the arguments at the widths of `l`, apply the leaf, encode. -/
def ipaLeafStreamOf (C : IpaCodec F G) (smul : F → G → G) (H : G → G → F) :
    IpaLeaf → (ℕ → BitVec 64) → (ℕ → BitVec 64) → ℕ → BitVec 64
  | .commit8, s0, s1 =>
    elemStream (C.encG (ipa_commit smul (decVec (n := 8) C.decF s0) (decVec (n := 8) C.decG s1)))
  | .crossL8, s0, s1 =>
    elemStream (C.encG (ipa_cross_L smul (n := 4)
      (decVec (n := 8) C.decF s0) (decVec (n := 8) C.decG s1)))
  | .crossR8, s0, s1 =>
    elemStream (C.encG (ipa_cross_R smul (n := 4)
      (decVec (n := 8) C.decF s0) (decVec (n := 8) C.decG s1)))
  | .crossL4, s0, s1 =>
    elemStream (C.encG (ipa_cross_L smul (n := 2)
      (decVec (n := 4) C.decF s0) (decVec (n := 4) C.decG s1)))
  | .crossR4, s0, s1 =>
    elemStream (C.encG (ipa_cross_R smul (n := 2)
      (decVec (n := 4) C.decF s0) (decVec (n := 4) C.decG s1)))
  | .crossL2, s0, s1 =>
    elemStream (C.encG (ipa_cross_L smul (n := 1)
      (decVec (n := 2) C.decF s0) (decVec (n := 2) C.decG s1)))
  | .crossR2, s0, s1 =>
    elemStream (C.encG (ipa_cross_R smul (n := 1)
      (decVec (n := 2) C.decF s0) (decVec (n := 2) C.decG s1)))
  | .squeeze, s0, s1 =>
    elemStream (C.encF (ipa_squeeze H (C.decG (streamElem s0 0)) (C.decG (streamElem s1 0))))
  | .foldWit4, s0, s1 =>
    vecStream C.encF (ipa_fold_wit (n := 4) (decVec (n := 8) C.decF s0) (C.decF (streamElem s1 0)))
  | .foldWit2, s0, s1 =>
    vecStream C.encF (ipa_fold_wit (n := 2) (decVec (n := 4) C.decF s0) (C.decF (streamElem s1 0)))
  | .foldWit1, s0, s1 =>
    vecStream C.encF (ipa_fold_wit (n := 1) (decVec (n := 2) C.decF s0) (C.decF (streamElem s1 0)))
  | .foldGen4, s0, s1 =>
    vecStream C.encG (ipa_fold_gen smul (n := 4)
      (decVec (n := 8) C.decG s0) (C.decF (streamElem s1 0)))
  | .foldGen2, s0, s1 =>
    vecStream C.encG (ipa_fold_gen smul (n := 2)
      (decVec (n := 4) C.decG s0) (C.decF (streamElem s1 0)))
  | .final, s0, _ =>
    elemStream (C.encF (ipa_final (decVec (n := 1) C.decF s0)))

/-- The result stream of the call `name` under the naming `nm`: the stream of the
    leaf `name` denotes, and `0` when it denotes none. -/
def ipaLeafStreamN (nm : IpaLeafNames) (C : IpaCodec F G) (smul : F → G → G) (H : G → G → F)
    (name : String) (s0 s1 : ℕ → BitVec 64) : ℕ → BitVec 64 :=
  match nm.leafOf name with
  | some l => ipaLeafStreamOf C smul H l s0 s1
  | none => fun _ => 0

/-- The leaf oracle of the IPA leaves under the naming `nm` and the codec `C`. -/
def ipaLeafOracleN (nm : IpaLeafNames) (C : IpaCodec F G) (smul : F → G → G)
    (H : G → G → F) : SemLeafSpec :=
  fun name retTy args =>
    slotOf retTy (ipaLeafStreamN nm C smul H name (ipaArg args 0) (ipaArg args 1))

/-- The result stream of the Bulletproofs leaf `name` on the argument streams `s0`,
    `s1`. -/
def ipaLeafStream (C : IpaCodec F G) (smul : F → G → G) (H : G → G → F) (name : String)
    (s0 s1 : ℕ → BitVec 64) : ℕ → BitVec 64 :=
  ipaLeafStreamN bulletproofsIpaNames C smul H name s0 s1

/-- The leaf oracle of the Bulletproofs leaves under the codec `C`. -/
def ipaLeafOracle (C : IpaCodec F G) (smul : F → G → G) (H : G → G → F) : SemLeafSpec :=
  ipaLeafOracleN bulletproofsIpaNames C smul H

/-- The environment entry holding the encoding of a group element. -/
def ptSlot (C : IpaCodec F G) (P : G) : Option ((t : CryptoTy) × ⟦t⟧) :=
  some ⟨.memref 4, slotOf (.memref 4) (elemStream (C.encG P))⟩

/-- The environment entry holding the encoding of a scalar. -/
def scSlot (C : IpaCodec F G) (x : F) : Option ((t : CryptoTy) × ⟦t⟧) :=
  some ⟨.memref 4, slotOf (.memref 4) (elemStream (C.encF x))⟩

end CatCrypt.Crypto.Jasmin.BulletproofsIPA

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-! ## 4. The `LowCT` body -/

/-- Wire type of a witness vector of length `N` (32 bytes per scalar). -/
def ipaWitnessTowerType (N : Nat) : TowerType := .TBytes (32 * N)
/-- Wire type of a generator vector of length `N` (32 bytes per point). -/
def ipaGenTowerType (N : Nat) : TowerType := .TBytes (32 * N)
/-- Wire type of a commitment point. -/
def ipaPointTowerType : TowerType := .TBytes 32
/-- Wire type of a challenge or final scalar. -/
def ipaScalarTowerType : TowerType := .TBytes 32

/-- The located slot named `n` of wire type `t`. -/
def locBulletproofsIPA (n : String) (t : TowerType) : Located := { locVar := n, locSrc := t }

/-- Body of the `n = 8` (three-round) IPA prover with the leaf calls named by
    `nm`, in the call sequence of `ipaProverLean8`. The slots `a1`/`G1`,
    `a2`/`G2`, `a3` have the lengths 4, 2 and 1 of the round outputs. -/
def ipaProverBodyN (nm : BulletproofsIPA.IpaLeafNames) : LowCT :=
  let a_l   := locBulletproofsIPA "a"        (ipaWitnessTowerType 8)
  let G_l   := locBulletproofsIPA "G"        (ipaGenTowerType 8)
  let P_l   := locBulletproofsIPA "P"        ipaPointTowerType
  let L0_l  := locBulletproofsIPA "L0"       ipaPointTowerType
  let R0_l  := locBulletproofsIPA "R0"       ipaPointTowerType
  let u0_l  := locBulletproofsIPA "u0"       ipaScalarTowerType
  let a1_l  := locBulletproofsIPA "a1"       (ipaWitnessTowerType 4)
  let G1_l  := locBulletproofsIPA "G1"       (ipaGenTowerType 4)
  let L1_l  := locBulletproofsIPA "L1"       ipaPointTowerType
  let R1_l  := locBulletproofsIPA "R1"       ipaPointTowerType
  let u1_l  := locBulletproofsIPA "u1"       ipaScalarTowerType
  let a2_l  := locBulletproofsIPA "a2"       (ipaWitnessTowerType 2)
  let G2_l  := locBulletproofsIPA "G2"       (ipaGenTowerType 2)
  let L2_l  := locBulletproofsIPA "L2"       ipaPointTowerType
  let R2_l  := locBulletproofsIPA "R2"       ipaPointTowerType
  let u2_l  := locBulletproofsIPA "u2"       ipaScalarTowerType
  let a3_l  := locBulletproofsIPA "a3"       (ipaWitnessTowerType 1)
  let res_l := locBulletproofsIPA "__result" ipaScalarTowerType
  .RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq
  (.RSeq (.RSeq (.RSeq (.RSeq (.RSeq .RSkip
    (.RCall (nm .commit8)  P_l   [a_l, G_l]))
    (.RCall (nm .crossL8)  L0_l  [a_l, G_l]))
    (.RCall (nm .crossR8)  R0_l  [a_l, G_l]))
    (.RCall (nm .squeeze)  u0_l  [L0_l, R0_l]))
    (.RCall (nm .foldWit4) a1_l  [a_l, u0_l]))
    (.RCall (nm .foldGen4) G1_l  [G_l, u0_l]))
    (.RCall (nm .crossL4)  L1_l  [a1_l, G1_l]))
    (.RCall (nm .crossR4)  R1_l  [a1_l, G1_l]))
    (.RCall (nm .squeeze)  u1_l  [L1_l, R1_l]))
    (.RCall (nm .foldWit2) a2_l  [a1_l, u1_l]))
    (.RCall (nm .foldGen2) G2_l  [G1_l, u1_l]))
    (.RCall (nm .crossL2)  L2_l  [a2_l, G2_l]))
    (.RCall (nm .crossR2)  R2_l  [a2_l, G2_l]))
    (.RCall (nm .squeeze)  u2_l  [L2_l, R2_l]))
    (.RCall (nm .foldWit1) a3_l  [a2_l, u2_l]))
    (.RCall (nm .final)    res_l [a3_l])

/-- Body of the `n = 8` Bulletproofs IPA prover: `ipaProverBodyN` at the
    Bulletproofs leaf names `ipa_commit_8`, `ipa_cross_L_8`, …, `ipa_final`. -/
def ipaProverBody8 : LowCT := ipaProverBodyN BulletproofsIPA.bulletproofsIpaNames

/-- `ReifiedFunc` bundle for the `n = 8` Bulletproofs IPA prover. -/
def ipaProver8Reified : ReifiedFunc :=
  { args    := [("a", ipaWitnessTowerType 8), ("G", ipaGenTowerType 8)]
    body    := ipaProverBody8
    retName := "__result" }

end CatCrypt.Crypto.Jasmin.LowCTReflect

namespace CatCrypt.Crypto.Jasmin.BulletproofsIPA

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.LeafOracleScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.Jasmin.LowCTReflect

/-! ## 5. The body computes the prover -/

variable {F G : Type} [Field F] [AddCommGroup G]

theorem envUpd_same (env : SEnvScalar) (n : String) {t : CryptoTy} (v : ⟦t⟧) :
    env.upd n v n = some ⟨t, v⟩ := by
  simp [SEnvScalar.upd]

theorem envUpd_other (env : SEnvScalar) (n m : String) {t : CryptoTy} (v : ⟦t⟧) (h : m ≠ n) :
    env.upd n v m = env m := by
  simp [SEnvScalar.upd, h]

/-- One leaf call into a slot of wire type other than `.TFp`, appended to a
    program: the destination holds the leaf value on the arguments read before the
    call, and every other name is unchanged. -/
theorem semScalarL_seq_call (ls : SemLeafSpec) {c : CatCrypt.Crypto.Jasmin.LowCT.LowCT}
    {env e : SEnvScalar} (h : semScalarL ls c env = some e) (f : String)
    (x : String) (t : CatCrypt.Crypto.Jasmin.LowCT.TowerType)
    (args : List CatCrypt.Crypto.Jasmin.LowCT.Located) (ht : t ≠ .TFp := by decide) :
    ∃ e', semScalarL ls (.RSeq c (.RCall f (locBulletproofsIPA x t) args)) env = some e' ∧
      e' x = some ⟨encodeTy t, ls f (encodeTy t) (argVals e (locNames args))⟩ ∧
      ∀ m, m ≠ x → e' m = e m :=
  ⟨_, by simp only [semScalarL, h, Option.bind_some, locBulletproofsIPA,
      CatCrypt.Crypto.Jasmin.LowCT.Located.locDst, inlineRCallVal_of_ne_TFp ls f ht],
    envUpd_same _ _ _, fun m hm => envUpd_other _ _ _ _ hm⟩

/-- The slots of an environment holding the encoding of an `n = 8` proof: `P`,
    the pairs `(L0, R0)`, `(L1, R1)`, `(L2, R2)`, and `__result`. -/
def ipaTranscriptSlots8 (C : IpaCodec F G) (π : IpaProof F G) (env : SEnvScalar) : Prop :=
  env "P" = ptSlot C π.commitment ∧
    π.rounds.map (fun lr => (ptSlot C lr.1, ptSlot C lr.2))
      = [(env "L0", env "R0"), (env "L1", env "R1"), (env "L2", env "R2")] ∧
    env "__result" = scSlot C π.final

/-- Evaluates a leaf-call fact: normalizes the wire types, reads the argument
    slots from the local hypotheses, and applies the leaf oracle. -/
local macro "ipa_eval_at " h:ident : tactic => `(tactic| (
  dsimp only [locBulletproofsIPA, ipaWitnessTowerType, ipaGenTowerType, ipaPointTowerType,
    ipaScalarTowerType, CatCrypt.Crypto.Jasmin.LowCT.Located.locDst, encodeTy, locNames,
    List.map, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv] at $h:ident
  simp (config := { decide := true }) only [argVals, List.filterMap_cons,
    List.filterMap_nil, ipaLeafOracleN, ipaArg, List.getElem?_cons_zero,
    List.getElem?_cons_succ, ipaLeafStreamN, ipaLeafStreamOf, decVec_vecF,
    decVec_vecG, streamElem_elem, IpaCodec.decF_encF, IpaCodec.decG_encG, ne_eq,
    not_false_eq_true, *] at $h:ident))

/-- For every naming `nm` under which each leaf's call name denotes that leaf, and
    every codec, scalar action, challenge function, witness `a` and generators `g`
    of length 8, running `ipaProverBodyN nm` at the leaf oracle `ipaLeafOracleN nm`
    from an environment holding the encodings of `a` and `g` leaves the encoding of
    `ipaProve smul H 3 a g` in the transcript slots. -/
theorem ipaProverBodyN_computes (nm : IpaLeafNames) (hnm : ∀ l, nm.leafOf (nm l) = some l)
    (C : IpaCodec F G) (smul : F → G → G) (H : G → G → F)
    (a : Fin 8 → F) (g : Fin 8 → G) (env : SEnvScalar)
    (ha : env "a" = some ⟨.memref 32, slotOf (.memref 32) (vecStream C.encF a)⟩)
    (hg : env "G" = some ⟨.memref 32, slotOf (.memref 32) (vecStream C.encG g)⟩) :
    ∃ env', semScalarL (ipaLeafOracleN nm C smul H) (ipaProverBodyN nm) env = some env' ∧
      ipaTranscriptSlots8 C (ipaProve smul H 3 a g) env' := by
  rw [← ipaProverLean8_eq_ipaProve]
  have h0 : semScalarL (ipaLeafOracleN nm C smul H) .RSkip env = some env := rfl
  obtain ⟨e1, h1, v1, f1⟩ := semScalarL_seq_call _ h0 (nm .commit8) "P" ipaPointTowerType
    [locBulletproofsIPA "a" (ipaWitnessTowerType 8), locBulletproofsIPA "G" (ipaGenTowerType 8)]
  ipa_eval_at v1
  obtain ⟨e2, h2, v2, f2⟩ := semScalarL_seq_call _ h1 (nm .crossL8) "L0" ipaPointTowerType
    [locBulletproofsIPA "a" (ipaWitnessTowerType 8), locBulletproofsIPA "G" (ipaGenTowerType 8)]
  ipa_eval_at v2
  obtain ⟨e3, h3, v3, f3⟩ := semScalarL_seq_call _ h2 (nm .crossR8) "R0" ipaPointTowerType
    [locBulletproofsIPA "a" (ipaWitnessTowerType 8), locBulletproofsIPA "G" (ipaGenTowerType 8)]
  ipa_eval_at v3
  obtain ⟨e4, h4, v4, f4⟩ := semScalarL_seq_call _ h3 (nm .squeeze) "u0" ipaScalarTowerType
    [locBulletproofsIPA "L0" ipaPointTowerType, locBulletproofsIPA "R0" ipaPointTowerType]
  ipa_eval_at v4
  obtain ⟨e5, h5, v5, f5⟩ := semScalarL_seq_call _ h4 (nm .foldWit4) "a1"
    (ipaWitnessTowerType 4)
    [locBulletproofsIPA "a" (ipaWitnessTowerType 8), locBulletproofsIPA "u0" ipaScalarTowerType]
  ipa_eval_at v5
  obtain ⟨e6, h6, v6, f6⟩ := semScalarL_seq_call _ h5 (nm .foldGen4) "G1" (ipaGenTowerType 4)
    [locBulletproofsIPA "G" (ipaGenTowerType 8), locBulletproofsIPA "u0" ipaScalarTowerType]
  ipa_eval_at v6
  obtain ⟨e7, h7, v7, f7⟩ := semScalarL_seq_call _ h6 (nm .crossL4) "L1" ipaPointTowerType
    [locBulletproofsIPA "a1" (ipaWitnessTowerType 4), locBulletproofsIPA "G1" (ipaGenTowerType 4)]
  ipa_eval_at v7
  obtain ⟨e8, h8, v8, f8⟩ := semScalarL_seq_call _ h7 (nm .crossR4) "R1" ipaPointTowerType
    [locBulletproofsIPA "a1" (ipaWitnessTowerType 4), locBulletproofsIPA "G1" (ipaGenTowerType 4)]
  ipa_eval_at v8
  obtain ⟨e9, h9, v9, f9⟩ := semScalarL_seq_call _ h8 (nm .squeeze) "u1" ipaScalarTowerType
    [locBulletproofsIPA "L1" ipaPointTowerType, locBulletproofsIPA "R1" ipaPointTowerType]
  ipa_eval_at v9
  obtain ⟨e10, h10, v10, f10⟩ := semScalarL_seq_call _ h9 (nm .foldWit2) "a2"
    (ipaWitnessTowerType 2)
    [locBulletproofsIPA "a1" (ipaWitnessTowerType 4), locBulletproofsIPA "u1" ipaScalarTowerType]
  ipa_eval_at v10
  obtain ⟨e11, h11, v11, f11⟩ := semScalarL_seq_call _ h10 (nm .foldGen2) "G2"
    (ipaGenTowerType 2)
    [locBulletproofsIPA "G1" (ipaGenTowerType 4), locBulletproofsIPA "u1" ipaScalarTowerType]
  ipa_eval_at v11
  obtain ⟨e12, h12, v12, f12⟩ := semScalarL_seq_call _ h11 (nm .crossL2) "L2" ipaPointTowerType
    [locBulletproofsIPA "a2" (ipaWitnessTowerType 2), locBulletproofsIPA "G2" (ipaGenTowerType 2)]
  ipa_eval_at v12
  obtain ⟨e13, h13, v13, f13⟩ := semScalarL_seq_call _ h12 (nm .crossR2) "R2" ipaPointTowerType
    [locBulletproofsIPA "a2" (ipaWitnessTowerType 2), locBulletproofsIPA "G2" (ipaGenTowerType 2)]
  ipa_eval_at v13
  obtain ⟨e14, h14, v14, f14⟩ := semScalarL_seq_call _ h13 (nm .squeeze) "u2" ipaScalarTowerType
    [locBulletproofsIPA "L2" ipaPointTowerType, locBulletproofsIPA "R2" ipaPointTowerType]
  ipa_eval_at v14
  obtain ⟨e15, h15, v15, f15⟩ := semScalarL_seq_call _ h14 (nm .foldWit1) "a3"
    (ipaWitnessTowerType 1)
    [locBulletproofsIPA "a2" (ipaWitnessTowerType 2), locBulletproofsIPA "u2" ipaScalarTowerType]
  ipa_eval_at v15
  obtain ⟨e16, h16, v16, f16⟩ := semScalarL_seq_call _ h15 (nm .final) "__result"
    ipaScalarTowerType [locBulletproofsIPA "a3" (ipaWitnessTowerType 1)]
  ipa_eval_at v16
  refine ⟨e16, h16, ?_⟩
  simp (config := { decide := true }) only [ipaTranscriptSlots8, ipaProverLean8, List.map,
    ptSlot, scSlot, ne_eq, *]

/-- `ipaProverBody8_computes`: `ipaProverBodyN_computes` at the Bulletproofs leaf
    names. -/
theorem ipaProverBody8_computes (C : IpaCodec F G) (smul : F → G → G) (H : G → G → F)
    (a : Fin 8 → F) (g : Fin 8 → G) (env : SEnvScalar)
    (ha : env "a" = some ⟨.memref 32, slotOf (.memref 32) (vecStream C.encF a)⟩)
    (hg : env "G" = some ⟨.memref 32, slotOf (.memref 32) (vecStream C.encG g)⟩) :
    ∃ env', semScalarL (ipaLeafOracle C smul H) ipaProverBody8 env = some env' ∧
      ipaTranscriptSlots8 C (ipaProve smul H 3 a g) env' :=
  ipaProverBodyN_computes bulletproofsIpaNames bulletproofsIpaNames_leafOf C smul H a g env ha hg

/-- `ipaProverBodyN nm` lies in the straight-line fragment the scalar front covers. -/
theorem ipaProverBodyN_covered (nm : IpaLeafNames) : IsCoveredS (ipaProverBodyN nm) := by
  unfold ipaProverBodyN
  repeat constructor

/-- `ipaProverBody8` lies in the straight-line fragment the scalar front covers. -/
theorem ipaProverBody8_covered : IsCoveredS ipaProverBody8 :=
  ipaProverBodyN_covered bulletproofsIpaNames

/-- The emitted `Com` of `ipaProverBodyN nm`: whenever `translateDialectControl`
    translates the body from a valuation consistent with an environment holding
    the encodings of `a` and `g`, the translated `Com` denotes, at the leaf
    oracle `ipaLeafOracleN nm`, a valuation consistent with an environment holding
    the encoding of `ipaProve smul H 3 a g`. -/
theorem ipaProverBodyN_denote (nm : IpaLeafNames) (hnm : ∀ l, nm.leafOf (nm l) = some l)
    (C : IpaCodec F G) (smul : F → G → G) (H : G → G → F)
    (a : Fin 8 → F) (g : Fin 8 → G) {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := CatCryptDialect.catCryptDialect) Γ) (env : SEnvScalar)
    (o : DTransOut Γ) (hc : ConsistentS vm V env)
    (htr : translateDialectControl vm (ipaProverBodyN nm) = some o)
    (ha : env "a" = some ⟨.memref 32, slotOf (.memref 32) (vecStream C.encF a)⟩)
    (hg : env "G" = some ⟨.memref 32, slotOf (.memref 32) (vecStream C.encG g)⟩) :
    ∃ (env' : SEnvScalar) (V' : Ctxt.Valuation (d := CatCryptDialect.catCryptDialect) o.Γ'),
      ConsistentS o.vm V' env' ∧ ipaTranscriptSlots8 C (ipaProve smul H 3 a g) env' ∧
      ∀ {t : CryptoTy} (tail : Com CatCryptDialect.catCryptDialect o.Γ' t),
        ∃ com, o.cont tail = some com ∧
          @Com.denote CatCryptDialect.catCryptDialect _ _
              (catCryptDenoteWith (ipaLeafOracleN nm C smul H)) _ _ com V
            = @Com.denote CatCryptDialect.catCryptDialect _ _
              (catCryptDenoteWith (ipaLeafOracleN nm C smul H)) _ _ tail V' := by
  obtain ⟨env', hsem, hslots⟩ := ipaProverBodyN_computes nm hnm C smul H a g env ha hg
  obtain ⟨V', hc', hden⟩ := translateDialectControl_denoteWith (ipaLeafOracleN nm C smul H)
    (ipaProverBodyN_covered nm) vm V env env' o hc htr hsem
  exact ⟨env', V', hc', hslots, hden⟩

/-- The emitted `Com` of `ipaProverBody8`: `ipaProverBodyN_denote` at the
    Bulletproofs leaf names. -/
theorem ipaProverBody8_denote (C : IpaCodec F G) (smul : F → G → G) (H : G → G → F)
    (a : Fin 8 → F) (g : Fin 8 → G) {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := CatCryptDialect.catCryptDialect) Γ) (env : SEnvScalar)
    (o : DTransOut Γ) (hc : ConsistentS vm V env)
    (htr : translateDialectControl vm ipaProverBody8 = some o)
    (ha : env "a" = some ⟨.memref 32, slotOf (.memref 32) (vecStream C.encF a)⟩)
    (hg : env "G" = some ⟨.memref 32, slotOf (.memref 32) (vecStream C.encG g)⟩) :
    ∃ (env' : SEnvScalar) (V' : Ctxt.Valuation (d := CatCryptDialect.catCryptDialect) o.Γ'),
      ConsistentS o.vm V' env' ∧ ipaTranscriptSlots8 C (ipaProve smul H 3 a g) env' ∧
      ∀ {t : CryptoTy} (tail : Com CatCryptDialect.catCryptDialect o.Γ' t),
        ∃ com, o.cont tail = some com ∧
          @Com.denote CatCryptDialect.catCryptDialect _ _
              (catCryptDenoteWith (ipaLeafOracle C smul H)) _ _ com V
            = @Com.denote CatCryptDialect.catCryptDialect _ _
              (catCryptDenoteWith (ipaLeafOracle C smul H)) _ _ tail V' :=
  ipaProverBodyN_denote bulletproofsIpaNames bulletproofsIpaNames_leafOf C smul H a g vm V env o
    hc htr ha hg

end CatCrypt.Crypto.Jasmin.BulletproofsIPA

namespace CatCrypt.Crypto.Jasmin.BulletproofsIPA

open CatCrypt.Util (P25519)
open CatCrypt.Crypto.Jasmin.Ed25519Spec (L lsmul xParity ed_compress_spec ed_decompress_spec
  compress_decompress_well_defined)
open CatCrypt.Crypto.Jasmin.Ed25519Group (EdPt)
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.LeafOracleScalar
open CatCrypt.Crypto.Jasmin.LowCTReflect

/-! ## 6. The edwards25519 instance -/

/-- The little-endian 64-bit limbs of `v`. -/
def natLimbs (v : ℕ) : Limbs4 := fun i => BitVec.ofNat 64 (v / 2 ^ (64 * i.1))

/-- The natural number with little-endian 64-bit limbs `w`. -/
def limbsNat (w : Limbs4) : ℕ :=
  (w 0).toNat + (w 1).toNat * 2 ^ 64 + (w 2).toNat * 2 ^ 128 + (w 3).toNat * 2 ^ 192

theorem limbsNat_natLimbs (v : ℕ) (hv : v < 2 ^ 256) : limbsNat (natLimbs v) = v := by
  simp only [limbsNat, natLimbs, BitVec.toNat_ofNat, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  omega

/-- A scalar of `ZMod L` as the limbs of its residue. -/
def edScalarEnc (x : ZMod L) : Limbs4 := natLimbs x.val

/-- The scalar with residue `limbsNat w` modulo `L`. -/
def edScalarDec (w : Limbs4) : ZMod L := (limbsNat w : ZMod L)

theorem L_lt_two_pow_256 : L < 2 ^ 256 := by unfold L; norm_num

theorem edScalarDec_enc (x : ZMod L) : edScalarDec (edScalarEnc x) = x := by
  rw [edScalarDec, edScalarEnc, limbsNat_natLimbs _ (lt_trans (ZMod.val_lt x) L_lt_two_pow_256),
    ZMod.natCast_zmod_val]

/-- The RFC 8032 encoding of a point: the residue of `y` in bits 0–254 and the
    parity of `x` in bit 255. -/
def edPointEnc (P : EdPt) : Limbs4 :=
  natLimbs (P.y.val + 2 ^ 255 * (if xParity P.x then 1 else 0))

/-- The RFC 8032 decoding of a point, and `0` when no point has the encoding. -/
noncomputable def edPointDec (w : Limbs4) : EdPt :=
  (ed_decompress_spec ((limbsNat w % 2 ^ 255 : ℕ) : ZMod P25519)
    (decide (limbsNat w / 2 ^ 255 = 1))).getD 0

theorem edPointDec_enc (P : EdPt) : edPointDec (edPointEnc P) = P := by
  have hy : P.y.val < 2 ^ 255 := lt_of_lt_of_le (ZMod.val_lt P.y) (by unfold P25519; norm_num)
  have hlt : P.y.val + 2 ^ 255 * (if xParity P.x then 1 else 0) < 2 ^ 256 := by
    split_ifs <;> omega
  rw [edPointDec, edPointEnc, limbsNat_natLimbs _ hlt]
  have h1 : (P.y.val + 2 ^ 255 * (if xParity P.x then 1 else 0)) % 2 ^ 255 = P.y.val := by
    split_ifs <;> omega
  have h2 : decide ((P.y.val + 2 ^ 255 * (if xParity P.x then 1 else 0)) / 2 ^ 255 = 1)
      = xParity P.x := by
    split_ifs with h <;> simp [h] <;> omega
  rw [h1, h2, ZMod.natCast_zmod_val]
  have := compress_decompress_well_defined P
  simp only [ed_compress_spec] at this
  rw [this, Option.getD_some]

/-- The edwards25519 codec: scalars of `ZMod L` as 32-byte residues, points in
    the RFC 8032 compressed encoding. -/
noncomputable def ed25519IpaCodec : IpaCodec (ZMod L) EdPt where
  encF := edScalarEnc
  decF := edScalarDec
  encG := edPointEnc
  decG := edPointDec
  decF_encF := edScalarDec_enc
  decG_encG := edPointDec_enc

/-- `ipaProverBody8_computes` over the edwards25519 group with scalars `ZMod L`
    acting by `lsmul`, for every challenge function `H`. -/
theorem ipaProverBody8_computes_ed25519 (H : EdPt → EdPt → ZMod L)
    (a : Fin 8 → ZMod L) (g : Fin 8 → EdPt) (env : SEnvScalar)
    (ha : env "a" = some ⟨.memref 32, slotOf (.memref 32) (vecStream edScalarEnc a)⟩)
    (hg : env "G" = some ⟨.memref 32, slotOf (.memref 32) (vecStream edPointEnc g)⟩) :
    ∃ env', semScalarL (ipaLeafOracle ed25519IpaCodec lsmul H) ipaProverBody8 env = some env' ∧
      ipaTranscriptSlots8 ed25519IpaCodec (ipaProve lsmul H 3 a g) env' :=
  ipaProverBody8_computes ed25519IpaCodec lsmul H a g env ha hg

end CatCrypt.Crypto.Jasmin.BulletproofsIPA
