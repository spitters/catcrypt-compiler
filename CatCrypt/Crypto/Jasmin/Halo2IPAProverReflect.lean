/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.Jasmin.LowCTReflect
public import CatCrypt.Crypto.Jasmin.BulletproofsIPAReflect
public import CatCrypt.Crypto.Pairing.PastaGroupEmit

/-!
# Halo2 inner-product-argument prover orchestration over Pallas

The `n = 8` (three-round) inner-product-argument prover of
`BulletproofsIPAReflect`, instantiated at the Pallas group of the Pasta cycle:
points of `y² = x³ + 5` over `ZMod pallasQ` (Mathlib's
`WeierstrassCurve.Affine.Point`), scalars in the Pallas scalar field
`ZMod vestaQ` acting by `x • P = x.val • P`, and the leaf calls named
`halo2_commit_8`, `halo2_ipa_L_8`, …, `halo2_ipa_open`.

## Contents

* §1 The Pallas point group `PallasPt`, the scalar action `pallasSmul`, and the
  Halo2 leaves `halo2_commit`, `halo2_ipa_L`, `halo2_ipa_R`, `halo2_squeeze`,
  `halo2_fold_coeffs`, `halo2_fold_gens`, `halo2_ipa_open` (the leaves of
  `BulletproofsIPAReflect` at `pallasSmul`), their `@[rust_cmd_pattern]`
  registrations, and `halo2IPAProverLean8 = ipaProve pallasSmul H 3`.
* §2 The wire codec `pallasIpaCodec`: a scalar as the 32-byte little-endian
  residue; a point as the 32-byte little-endian `x` residue with the parity of
  `y` in bit 255 and the identity as all zeros (the `pasta_curves` compressed
  encoding). The encoding is injective (`pallasPtNat_injective`: no point has
  `x = 0`, since `5` is not a square modulo `pallasQ`), and the decoding inverts
  it.
* §3 `halo2IPAProverBody8 = ipaProverBodyN halo2IpaNames`, the `LowCT` body the
  front lowers, and `halo2IPAProver8Reified`.
* §4 `halo2IPAProverBody8_computes`: for every challenge function `H` and all
  `a`, `G`, the body run under `semScalarL` at the leaf oracle leaves the
  encodings of `ipaProve pallasSmul H 3 a G` in the transcript slots;
  `halo2IPAProverBody8_denote` carries this to the emitted `Com`.
* §5 The group operations of the prover against the emitted Pasta kernels of
  `PastaGroupEmit`: `pallasSmul_emitted` (the emitted double-and-add over the
  bits of `x.val` represents `pallasSmul x A`); the group addition is
  `PastaGroupEmit.pallas_emittedAdd_projRep`.

## Where the Halo2 IPA differs

The body is the a/G-only reduction of `ipaProve`. The `create_proof` of
`halo2_proofs` (`poly/ipa/commitment/prover.rs`) opens a polynomial `p` at a
point `x₃` and differs in five places, none of which the body contains:

* a blinding polynomial `s` with `s(x₃) = 0` is committed first and the prover
  folds `p' = p − p(x₃) + ξ·s` for a challenge `ξ`;
* a second vector `b = (1, x₃, x₃², …)` is folded alongside, and each cross
  commitment carries the term `[z · ⟨p'_hi, b_lo⟩] U` (resp. `⟨p'_lo, b_hi⟩`) on
  the extra generator `U`, with `z` a transcript challenge;
* each cross commitment carries a blinding term `[r] W` on the generator `W`, and
  the prover sends the accumulated blind `f` with the final scalar;
* the cross commitments pair the halves the other way round
  (`L = ⟨p'_hi, G_lo⟩`, `R = ⟨p'_lo, G_hi⟩`) and the folds are
  `p' ← p'_lo + u⁻¹ p'_hi`, `b ← b_lo + u b_hi`, `G ← G_lo + u G_hi`, against
  `ipaProve`'s `x · a_lo + x⁻¹ · a_hi` and `x⁻¹ · G_lo + x · G_hi`;
* the challenge `u` is squeezed from the running transcript, where `ipaProve`
  takes a function `H` of the round's `(L, R)` alone.

## References

* Bowe, Grigg, Hopwood — *Recursive Proof Composition without a Trusted Setup*,
  2019.
* `CatCrypt/Crypto/Jasmin/BulletproofsIPAReflect.lean` (`ipaProve`,
  `ipaProverBodyN_computes`, `ipaProverBodyN_denote`).
* `CatCrypt/Crypto/Pairing/PastaGroupEmit.lean` (`emittedSmul_projRep`,
  `pallas_emittedAdd_projRep`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.Halo2IPA

open CatCrypt.Crypto.Pairing.PastaCompleteAdd
open CatCrypt.Crypto.SecureCompilation.RelationalFront (pallasQ vestaQ)
open scoped CatCrypt.Crypto.Pairing.PastaCompleteAdd
open CatCrypt.Crypto.Jasmin.BulletproofsIPA
open CatCrypt.Crypto.Jasmin.LowCTReflect (ipa_commit ipa_cross_L ipa_cross_R ipa_squeeze
  ipa_fold_wit ipa_fold_gen ipa_final)

/-! ## 1. The Pallas group, the scalar action and the leaves -/

/-- The points of Pallas, `y² = x³ + 5` over `ZMod pallasQ`. -/
abbrev PallasPt : Type := (w0 (5 : ZMod pallasQ)).toAffine.Point

/-- The Pallas scalar field, the base field `ZMod vestaQ` of Vesta. -/
abbrev PallasScalar : Type := ZMod vestaQ

/-- The scalar action `x • P = x.val • P` of `ZMod vestaQ` on Pallas points. -/
def pallasSmul (x : PallasScalar) (P : PallasPt) : PallasPt := x.val • P

/-- Witness commitment `⟨a, G⟩`. -/
def halo2_commit {n : ℕ} (a : Fin n → PallasScalar) (g : Fin n → PallasPt) : PallasPt :=
  ipa_commit pallasSmul a g

/-- Left cross commitment of an IPA round. -/
def halo2_ipa_L {n : ℕ} (a : Fin (2 * n) → PallasScalar) (g : Fin (2 * n) → PallasPt) :
    PallasPt :=
  ipa_cross_L pallasSmul a g

/-- Right cross commitment of an IPA round. -/
def halo2_ipa_R {n : ℕ} (a : Fin (2 * n) → PallasScalar) (g : Fin (2 * n) → PallasPt) :
    PallasPt :=
  ipa_cross_R pallasSmul a g

/-- Fiat–Shamir challenge `H(L, R)`. -/
def halo2_squeeze (H : PallasPt → PallasPt → PallasScalar) (L R : PallasPt) : PallasScalar :=
  ipa_squeeze H L R

/-- Fold of the coefficient vector by the challenge, halving its length. -/
def halo2_fold_coeffs {n : ℕ} (a : Fin (2 * n) → PallasScalar) (x : PallasScalar) :
    Fin n → PallasScalar :=
  ipa_fold_wit a x

/-- Fold of the generator vector by the challenge, halving its length. -/
def halo2_fold_gens {n : ℕ} (g : Fin (2 * n) → PallasPt) (x : PallasScalar) :
    Fin n → PallasPt :=
  ipa_fold_gen pallasSmul g x

/-- Final opening scalar of a length-one coefficient vector. -/
def halo2_ipa_open (a : Fin 1 → PallasScalar) : PallasScalar := ipa_final a

end CatCrypt.Crypto.Jasmin.Halo2IPA

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.Halo2IPA

@[rust_cmd_pattern]
def halo2Commit8Pattern : LowCTPattern where
  name := "halo2_commit_8"; fnHead := ``halo2_commit; arity := 2; towerType := .TBytes 32

@[rust_cmd_pattern]
def halo2IpaL8Pattern : LowCTPattern where
  name := "halo2_ipa_L_8"; fnHead := ``halo2_ipa_L; arity := 2; towerType := .TBytes 32

@[rust_cmd_pattern]
def halo2IpaR8Pattern : LowCTPattern where
  name := "halo2_ipa_R_8"; fnHead := ``halo2_ipa_R; arity := 2; towerType := .TBytes 32

@[rust_cmd_pattern]
def halo2SqueezePattern : LowCTPattern where
  name := "halo2_squeeze"; fnHead := ``halo2_squeeze; arity := 2; towerType := .TBytes 32

@[rust_cmd_pattern]
def halo2FoldCoeffs4Pattern : LowCTPattern where
  name := "halo2_fold_coeffs_4"; fnHead := ``halo2_fold_coeffs; arity := 2
  towerType := .TBytes 128

@[rust_cmd_pattern]
def halo2FoldGens4Pattern : LowCTPattern where
  name := "halo2_fold_gens_4"; fnHead := ``halo2_fold_gens; arity := 2; towerType := .TBytes 128

@[rust_cmd_pattern]
def halo2IpaOpenPattern : LowCTPattern where
  name := "halo2_ipa_open"; fnHead := ``halo2_ipa_open; arity := 1; towerType := .TBytes 32

end CatCrypt.Crypto.Jasmin.LowCTReflect

namespace CatCrypt.Crypto.Jasmin.Halo2IPA

open CatCrypt.Crypto.Pairing.PastaCompleteAdd
open CatCrypt.Crypto.SecureCompilation.RelationalFront (pallasQ vestaQ)
open scoped CatCrypt.Crypto.Pairing.PastaCompleteAdd
open CatCrypt.Crypto.Jasmin.BulletproofsIPA

/-- The `n = 8` (three-round) Halo2 IPA prover as a sequence of leaf calls, in the
    order of `halo2IPAProverBody8`. -/
def halo2IPAProverLean8 (H : PallasPt → PallasPt → PallasScalar)
    (a : Fin 8 → PallasScalar) (g : Fin 8 → PallasPt) : IpaProof PallasScalar PallasPt :=
  let P := halo2_commit a g
  -- round 0 : 8 → 4
  let L0 := halo2_ipa_L (n := 4) a g
  let R0 := halo2_ipa_R (n := 4) a g
  let u0 := halo2_squeeze H L0 R0
  let a1 := halo2_fold_coeffs (n := 4) a u0
  let G1 := halo2_fold_gens (n := 4) g u0
  -- round 1 : 4 → 2
  let L1 := halo2_ipa_L (n := 2) a1 G1
  let R1 := halo2_ipa_R (n := 2) a1 G1
  let u1 := halo2_squeeze H L1 R1
  let a2 := halo2_fold_coeffs (n := 2) a1 u1
  let G2 := halo2_fold_gens (n := 2) G1 u1
  -- round 2 : 2 → 1
  let L2 := halo2_ipa_L (n := 1) a2 G2
  let R2 := halo2_ipa_R (n := 1) a2 G2
  let u2 := halo2_squeeze H L2 R2
  let a3 := halo2_fold_coeffs (n := 1) a2 u2
  { commitment := P, rounds := [(L0, R0), (L1, R1), (L2, R2)], final := halo2_ipa_open a3 }

/-- The Halo2 leaf orchestration is the prover `ipaProve` at `k = 3` over Pallas. -/
theorem halo2IPAProverLean8_eq_ipaProve (H : PallasPt → PallasPt → PallasScalar)
    (a : Fin 8 → PallasScalar) (g : Fin 8 → PallasPt) :
    halo2IPAProverLean8 H a g = ipaProve pallasSmul H 3 a g := rfl

/-! ## 2. The wire codec -/

theorem pallasQ_lt : pallasQ < 2 ^ 255 := by unfold pallasQ; norm_num

theorem pallasQ_odd : pallasQ % 2 = 1 := by unfold pallasQ; norm_num

theorem vestaQ_lt : vestaQ < 2 ^ 256 := by unfold vestaQ; norm_num

theorem pallasQ_natCast_zmod_five : ((pallasQ : ℕ) : ZMod 5) = 2 := by
  rw [← ZMod.natCast_mod, show pallasQ % 5 = 2 by unfold pallasQ; norm_num]; rfl

theorem two_not_square_zmod_five : ¬ IsSquare (2 : ZMod 5) := by
  rintro ⟨r, hr⟩
  fin_cases r <;> revert hr <;> decide

/-- `5` is not a square modulo `pallasQ`, by quadratic reciprocity: `5 ≡ 1 (mod 4)`
    and `pallasQ ≡ 2 (mod 5)`. -/
theorem five_not_square_pallas : ¬ IsSquare (5 : ZMod pallasQ) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := pallasQ)
    (by norm_num) (by unfold pallasQ; norm_num)
  intro h5
  have := h.mpr (by exact_mod_cast h5)
  rw [pallasQ_natCast_zmod_five] at this
  exact two_not_square_zmod_five this

/-- No Pallas point has `x = 0`. -/
theorem pallas_x_ne_zero {x y : ZMod pallasQ}
    (h : (w0 (5 : ZMod pallasQ)).toAffine.Nonsingular x y) : x ≠ 0 := by
  intro hx
  have he := w0_equation h
  rw [hx] at he
  refine five_not_square_pallas ⟨y, ?_⟩
  rw [← sq, he]; ring

/-- The encoding of a point as a number below `2 ^ 256`: `0` for the identity, and
    `x + 2 ^ 255 · (y mod 2)` on the residues of an affine point `(x, y)`. -/
def pallasPtNat : PallasPt → ℕ
  | .zero => 0
  | .some (x := x) (y := y) _ => x.val + 2 ^ 255 * (if y.val % 2 = 1 then 1 else 0)

theorem pallasPtNat_lt (P : PallasPt) : pallasPtNat P < 2 ^ 256 := by
  have hq := pallasQ_lt
  cases P with
  | zero => simp only [pallasPtNat]; norm_num
  | some x y h =>
    have hx := ZMod.val_lt x
    simp only [pallasPtNat]
    split_ifs <;> omega

theorem pallasPtNat_ne_zero {x y : ZMod pallasQ}
    (h : (w0 (5 : ZMod pallasQ)).toAffine.Nonsingular x y) : pallasPtNat (.some x y h) ≠ 0 := by
  have hx : x.val ≠ 0 := fun h0 => pallas_x_ne_zero h ((ZMod.val_eq_zero x).mp h0)
  simp only [pallasPtNat]
  omega

/-- Two Pallas points with the same `x` and the same parity of `y` are equal. -/
theorem pallas_y_eq_of_parity {x y1 y2 : ZMod pallasQ}
    (h1 : (w0 (5 : ZMod pallasQ)).toAffine.Nonsingular x y1)
    (h2 : (w0 (5 : ZMod pallasQ)).toAffine.Nonsingular x y2)
    (hpar : y1.val % 2 = y2.val % 2) : y1 = y2 := by
  have e1 := w0_equation h1
  have e2 := w0_equation h2
  have hsq : (y1 - y2) * (y1 + y2) = 0 := by linear_combination e1 - e2
  rcases mul_eq_zero.mp hsq with h | h
  · exact sub_eq_zero.mp h
  · have hy : y1 = -y2 := eq_neg_of_add_eq_zero_left h
    by_cases hy2 : y2 = 0
    · rw [hy, hy2, neg_zero]
    · exfalso
      have hodd := pallasQ_odd
      have hlt := ZMod.val_lt y2
      rw [hy, ZMod.neg_val, ite_eq_right hy2] at hpar
      omega

theorem pallasPtNat_injective : Function.Injective pallasPtNat := by
  intro P Q hPQ
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y h => exact absurd hPQ.symm (pallasPtNat_ne_zero h)
  | some x1 y1 h1 =>
    cases Q with
    | zero => exact absurd hPQ (pallasPtNat_ne_zero h1)
    | some x2 y2 h2 =>
      have hq := pallasQ_lt
      have hx1 := ZMod.val_lt x1
      have hx2 := ZMod.val_lt x2
      simp only [pallasPtNat] at hPQ
      have hxv : x1.val = x2.val := by split_ifs at hPQ <;> omega
      have hpar : y1.val % 2 = y2.val % 2 := by split_ifs at hPQ <;> omega
      obtain rfl : x1 = x2 := ZMod.val_injective _ hxv
      obtain rfl := pallas_y_eq_of_parity h1 h2 hpar
      rfl

open Classical in
/-- The point whose encoding is `limbsNat w`, and the identity when no point has it. -/
noncomputable def pallasPtDec (w : Limbs4) : PallasPt :=
  if h : ∃ P, pallasPtNat P = limbsNat w then Classical.choose h else 0

theorem pallasPtDec_enc (P : PallasPt) : pallasPtDec (natLimbs (pallasPtNat P)) = P := by
  have hex : ∃ Q, pallasPtNat Q = limbsNat (natLimbs (pallasPtNat P)) :=
    ⟨P, (limbsNat_natLimbs _ (pallasPtNat_lt P)).symm⟩
  rw [pallasPtDec, dite_eq_left hex]
  apply pallasPtNat_injective
  rw [Classical.choose_spec hex, limbsNat_natLimbs _ (pallasPtNat_lt P)]

theorem pallasScalarDec_enc (x : PallasScalar) :
    ((limbsNat (natLimbs x.val) : ℕ) : PallasScalar) = x := by
  rw [limbsNat_natLimbs _ (lt_trans (ZMod.val_lt x) vestaQ_lt), ZMod.natCast_zmod_val]

/-- The Pallas codec: a scalar as its 32-byte little-endian residue, a point in the
    compressed encoding `pallasPtNat`. -/
noncomputable def pallasIpaCodec : IpaCodec PallasScalar PallasPt where
  encF x := natLimbs x.val
  decF w := (limbsNat w : PallasScalar)
  encG P := natLimbs (pallasPtNat P)
  decG := pallasPtDec
  decF_encF := pallasScalarDec_enc
  decG_encG := pallasPtDec_enc

/-! ## 3. The `LowCT` body -/

/-- The call names of the Halo2 leaves. -/
def halo2IpaNames : IpaLeafNames
  | .commit8 => "halo2_commit_8"
  | .crossL8 => "halo2_ipa_L_8"
  | .crossR8 => "halo2_ipa_R_8"
  | .crossL4 => "halo2_ipa_L_4"
  | .crossR4 => "halo2_ipa_R_4"
  | .crossL2 => "halo2_ipa_L_2"
  | .crossR2 => "halo2_ipa_R_2"
  | .squeeze => "halo2_squeeze"
  | .foldWit4 => "halo2_fold_coeffs_4"
  | .foldWit2 => "halo2_fold_coeffs_2"
  | .foldWit1 => "halo2_fold_coeffs_1"
  | .foldGen4 => "halo2_fold_gens_4"
  | .foldGen2 => "halo2_fold_gens_2"
  | .final => "halo2_ipa_open"

theorem halo2IpaNames_leafOf (l : IpaLeaf) :
    halo2IpaNames.leafOf (halo2IpaNames l) = some l := by
  cases l <;> simp [IpaLeafNames.leafOf, IpaLeaf.all, halo2IpaNames]

end CatCrypt.Crypto.Jasmin.Halo2IPA

namespace CatCrypt.Crypto.Jasmin.LowCTReflect

open CatCrypt.Crypto.Jasmin.LowCT

/-- Body of the `n = 8` Halo2 IPA prover: `ipaProverBodyN` at the Halo2 leaf names. -/
def halo2IPAProverBody8 : LowCT := ipaProverBodyN Halo2IPA.halo2IpaNames

/-- `ReifiedFunc` bundle for the `n = 8` Halo2 IPA prover. -/
def halo2IPAProver8Reified : ReifiedFunc :=
  { args    := [("a", ipaWitnessTowerType 8), ("G", ipaGenTowerType 8)]
    body    := halo2IPAProverBody8
    retName := "__result" }

end CatCrypt.Crypto.Jasmin.LowCTReflect

namespace CatCrypt.Crypto.Jasmin.Halo2IPA

open CatCrypt.Crypto.Pairing.PastaCompleteAdd
open CatCrypt.Crypto.Pairing.PastaGroupEmit
open CatCrypt.Crypto.SecureCompilation.RelationalFront (pallasQ vestaQ)
open scoped CatCrypt.Crypto.Pairing.PastaCompleteAdd
open CatCrypt.Crypto.Jasmin.BulletproofsIPA
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptLeafOracle
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.LeafOracleScalar
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.Jasmin.LowCTReflect

/-! ## 4. The body computes the prover -/

/-- The leaf oracle of the Halo2 leaves over Pallas, for the challenge function `H`. -/
noncomputable def halo2LeafOracle (H : PallasPt → PallasPt → PallasScalar) : SemLeafSpec :=
  ipaLeafOracleN halo2IpaNames pallasIpaCodec pallasSmul H

/-- For every challenge function `H`, coefficient vector `a` and generators `g` of
    length 8, running `halo2IPAProverBody8` at `halo2LeafOracle H` from an
    environment holding the encodings of `a` and `g` leaves the encoding of
    `ipaProve pallasSmul H 3 a g` in the transcript slots. -/
theorem halo2IPAProverBody8_computes (H : PallasPt → PallasPt → PallasScalar)
    (a : Fin 8 → PallasScalar) (g : Fin 8 → PallasPt) (env : SEnvScalar)
    (ha : env "a" = some ⟨.memref 32, slotOf (.memref 32) (vecStream pallasIpaCodec.encF a)⟩)
    (hg : env "G" = some ⟨.memref 32, slotOf (.memref 32) (vecStream pallasIpaCodec.encG g)⟩) :
    ∃ env', semScalarL (halo2LeafOracle H) halo2IPAProverBody8 env = some env' ∧
      ipaTranscriptSlots8 pallasIpaCodec (ipaProve pallasSmul H 3 a g) env' :=
  ipaProverBodyN_computes halo2IpaNames halo2IpaNames_leafOf pallasIpaCodec pallasSmul H a g
    env ha hg

/-- The emitted `Com` of `halo2IPAProverBody8`: whenever `translateDialectControl`
    translates the body from a valuation consistent with an environment holding the
    encodings of `a` and `g`, the translated `Com` denotes, at `halo2LeafOracle H`,
    a valuation consistent with an environment holding the encoding of
    `ipaProve pallasSmul H 3 a g`. -/
theorem halo2IPAProverBody8_denote (H : PallasPt → PallasPt → PallasScalar)
    (a : Fin 8 → PallasScalar) (g : Fin 8 → PallasPt) {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := CatCryptDialect.catCryptDialect) Γ) (env : SEnvScalar)
    (o : DTransOut Γ) (hc : ConsistentS vm V env)
    (htr : translateDialectControl vm halo2IPAProverBody8 = some o)
    (ha : env "a" = some ⟨.memref 32, slotOf (.memref 32) (vecStream pallasIpaCodec.encF a)⟩)
    (hg : env "G" = some ⟨.memref 32, slotOf (.memref 32) (vecStream pallasIpaCodec.encG g)⟩) :
    ∃ (env' : SEnvScalar) (V' : Ctxt.Valuation (d := CatCryptDialect.catCryptDialect) o.Γ'),
      ConsistentS o.vm V' env' ∧
      ipaTranscriptSlots8 pallasIpaCodec (ipaProve pallasSmul H 3 a g) env' ∧
      ∀ {t : CryptoTy} (tail : Com CatCryptDialect.catCryptDialect o.Γ' t),
        ∃ com, o.cont tail = some com ∧
          @Com.denote CatCryptDialect.catCryptDialect _ _
              (catCryptDenoteWith (halo2LeafOracle H)) _ _ com V
            = @Com.denote CatCryptDialect.catCryptDialect _ _
              (catCryptDenoteWith (halo2LeafOracle H)) _ _ tail V' :=
  ipaProverBodyN_denote halo2IpaNames halo2IpaNames_leafOf pallasIpaCodec pallasSmul H a g vm V
    env o hc htr ha hg

/-! ## 5. The group operations against the emitted Pasta kernels -/

/-- The most-significant-first binary digits of `n`. -/
def natBitsMsb (n : ℕ) : List Bool := (Nat.digits 2 n).reverse.map (fun d => decide (d = 1))

theorem bitsVal_natBitsMsb (n : ℕ) : bitsVal (natBitsMsb n) = n := by
  have key : ∀ L : List ℕ, (∀ d ∈ L, d < 2) →
      (L.reverse.map (fun d => decide (d = 1))).foldl
        (fun n bit => 2 * n + if bit then 1 else 0) 0 = Nat.ofDigits 2 L := by
    intro L hL
    induction L with
    | nil => rfl
    | cons d L ih =>
      rw [List.reverse_cons, List.map_append, List.foldl_append,
        ih (fun e he => hL e (List.mem_cons_of_mem _ he))]
      have hd := hL d List.mem_cons_self
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, Nat.ofDigits_cons]
      rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl
      · simp
      · simp; ring
  rw [bitsVal, natBitsMsb, key _ (fun d hd => Nat.digits_lt_base (by norm_num) hd),
    Nat.ofDigits_digits]

/-- The scalar action of the prover is the emitted scalar multiplication: when `O`
    represents the identity and `P` represents `A`, the emitted double-and-add over
    the bits of `x.val`, under the Pallas field-leaf oracle for the canonical field
    arithmetic, represents `pallasSmul x A`. -/
theorem pallasSmul_emitted (x : PallasScalar) {O P : WireTriple} {A : PallasPt}
    (hO : ProjRep0 5 (map3 (canonDec pallasQ) O) 0)
    (hP : ProjRep0 5 (map3 (canonDec pallasQ) P) A) :
    ProjRep0 5 (map3 (canonDec pallasQ)
      (emittedSmul pallasLeaves (pallasFieldOracle (canonOps pallasQ)) O P (natBitsMsb x.val)))
      (pallasSmul x A) := by
  have h := emittedSmul_projRep pallas_cubic_no_root pallasQ_two_ne_zero
    (pallasFieldOracle_agrees _) (canonOps_realize pallasQ_le) hO hP (natBitsMsb x.val)
  rwa [bitsVal_natBitsMsb] at h

end CatCrypt.Crypto.Jasmin.Halo2IPA
