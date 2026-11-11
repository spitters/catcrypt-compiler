/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

/-!
# The field domain at the frame range and the region length of the gate

The field domain `fieldDomB` accepts a field expression with `k` operands of `n` words under a
layout that `fieldAbiB` reads field by field: the parameters, the result, and empty constants,
bounds, public words and widths. It leaves the frame range `frameLo`, `frameHi` of the layout
free, and its expressions have `n < 2 ^ 64` words. The later conjuncts of the region gate read
both. The frame check `frameOkB` asks that every frame word of the printed body and the
red-zone word `cmovRedZone` lie in `[frameLo, frameHi]` below the frame, so a layout with the
parameters of `fieldAbi k n` and the frame range `[0, 0]` is refused at the red-zone conjunct
whatever the body. The entry check `entryB` asks that each region of the layout has at most
`2 ^ 61` words (`rsOK`), and the cell names check `cellNamesRB` that each cell array has fewer
than `2 ^ 60` words (`slotsOkB`); a region of `n ≥ 2 ^ 60` words is refused at one of them.

The domain `fieldDomB'` is `fieldDomB` with two further conditions: the frame range of the
layout is that of `fieldAbi k n`, from `-4096` to `-8` bytes below the entry stack pointer, and
`n < 2 ^ 60`. With the frame range fixed, every field of the layout is fixed, so the layout of
a member is `fieldAbi k n` itself (`fieldDomB'_layout`). Every member of `fieldDomB'` is a
member of `fieldDomB` (`fieldDomB_of_fieldDomB'`), so each stage lemma proved on `fieldDomB`
holds on `fieldDomB'`.

## Main definitions

* `fieldFrameB` — the frame range of the layout is that of `fieldAbi k n`.
* `fieldDomB'` — the field domain at the frame range of `fieldAbi k n` and `n < 2 ^ 60`.

## Main results

* `fieldDomB_of_fieldDomB'` — a member of `fieldDomB'` is a member of `fieldDomB`.
* `fieldDomB'_layout` — the layout of a member is `fieldAbi k n`, at `n < 2 ^ 60`.
* `fieldDomB'_of_fieldDomB` — a member of `fieldDomB` under `fieldAbi k n` at `n < 2 ^ 60`
  is a member of `fieldDomB'`.
* `<row>_fieldDom'` — the twenty field rows of `LeanFrontFields` are members.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete

open CatCrypt.Crypto.SecureCompilation.Haxc.FieldRoute (fieldAbi)

/-- The frame range of the layout `σ` is that of `fieldAbi k n`. -/
def fieldFrameB (σ : AbiLayout) (k n : Nat) : Bool :=
  σ.frameLo == (fieldAbi k n).frameLo && σ.frameHi == (fieldAbi k n).frameHi

/-- **The field domain at the frame range and the region length of the gate**: a field
    expression (`fieldDomE`) with `k` distinct operands of `n < 2 ^ 60` words, under a layout
    that is `fieldAbi k n` field by field (`fieldAbiB`) and has its frame range
    (`fieldFrameB`). -/
def fieldDomB' (e : _root_.Hax.TExpr) (σ : AbiLayout) : Bool :=
  match fieldDomE e with
  | some (k, n) => fieldAbiB σ k n && fieldFrameB σ k n && decide (n < 2 ^ 60)
  | none => false

/-- **A member of `fieldDomB'` is a member of `fieldDomB`.** -/
theorem fieldDomB_of_fieldDomB' {e : _root_.Hax.TExpr} {σ : AbiLayout}
    (h : fieldDomB' e σ = true) : fieldDomB e σ = true := by
  unfold fieldDomB' at h
  unfold fieldDomB
  split at h
  · rename_i k n hE
    rw [hE]
    simp only [Bool.and_eq_true] at h
    exact h.1.1
  · cases h

/-- The layout `fieldAbi k n` has the frame range of `fieldAbi k n`. -/
theorem fieldFrameB_fieldAbi (k n : Nat) : fieldFrameB (fieldAbi k n) k n = true := by
  simp [fieldFrameB]

/-- A layout that `fieldAbiB` reads as `fieldAbi k n` and that has its frame range is
    `fieldAbi k n`. -/
theorem eq_fieldAbi_of_fieldAbiB {σ : AbiLayout} {k n : Nat} (ha : fieldAbiB σ k n = true)
    (hf : fieldFrameB σ k n = true) : σ = fieldAbi k n := by
  obtain ⟨args, consts, result, bounds, lo, hi, pub, wid⟩ := σ
  simp only [fieldAbiB, fieldFrameB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.isEmpty_iff] at ha hf
  obtain ⟨⟨⟨⟨⟨hargs, hc⟩, hr⟩, hb⟩, hp⟩, hw⟩ := ha
  obtain ⟨hlo, hhi⟩ := hf
  have hres : result = .words "%rdi" n := by
    cases result <;> simp_all [resultWords?]
  subst hargs hc hres hb hp hw hlo hhi
  rfl

/-- **The layout of a member of `fieldDomB'` is `fieldAbi k n`**, for the numbers `k` of
    operands and `n < 2 ^ 60` of words of its field expression. -/
theorem fieldDomB'_layout {e : _root_.Hax.TExpr} {σ : AbiLayout} (h : fieldDomB' e σ = true) :
    ∃ k n, fieldDomE e = some (k, n) ∧ σ = fieldAbi k n ∧ n < 2 ^ 60 := by
  unfold fieldDomB' at h
  split at h
  · rename_i k n hE
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨k, n, hE, eq_fieldAbi_of_fieldAbiB h.1.1 h.1.2, h.2⟩
  · cases h

/-- A field expression with `k` operands of `n < 2 ^ 60` words is in `fieldDomB'` under
    `fieldAbi k n`. -/
theorem fieldDomB'_fieldAbi {e : _root_.Hax.TExpr} {k n : Nat} (h : fieldDomE e = some (k, n))
    (hn : n < 2 ^ 60) : fieldDomB' e (fieldAbi k n) = true := by
  simp only [fieldDomB', h, fieldAbiB_fieldAbi, fieldFrameB_fieldAbi, hn, decide_true,
    Bool.and_self]

/-- **A member of `fieldDomB` under `fieldAbi k n` at `n < 2 ^ 60` is a member of
    `fieldDomB'`.** -/
theorem fieldDomB'_of_fieldDomB {e : _root_.Hax.TExpr} {k n : Nat}
    (h : fieldDomB e (fieldAbi k n) = true) (hn : n < 2 ^ 60) :
    fieldDomB' e (fieldAbi k n) = true := by
  unfold fieldDomB at h
  split at h
  · rename_i k' n' hE
    have hargs := (Bool.and_eq_true _ _ ▸ (Bool.and_eq_true _ _ ▸
      (Bool.and_eq_true _ _ ▸ (Bool.and_eq_true _ _ ▸ (Bool.and_eq_true _ _ ▸ h).1).1).1).1).1
    have he : (fieldAbi k n).args = (fieldAbi k' n').args := of_decide_eq_true hargs
    have hlen := congrArg List.length he
    simp only [fieldAbi, List.length_map, List.length_range, Nat.add_right_cancel_iff] at hlen
    subst hlen
    have h0 := congrArg (fun l => l[0]?.map AbiArg.kind) he
    simp only [fieldAbi, List.getElem?_map, List.getElem?_range (Nat.succ_pos k),
      Option.map_some, Option.some.injEq, ArgKind.words.injEq] at h0
    subst h0
    exact fieldDomB'_fieldAbi hE hn
  · cases h

/-! ## The field rows of `LeanFrontFields` -/

section Rows

open CatCrypt.Crypto.SecureCompilation.Haxc.LeanFrontFields

/-- The product at the P-256 base prime is in `fieldDomB'`. -/
theorem p256Mul_fieldDom' : fieldDomB' p256MulTE (fieldAbi 2 4) = true :=
  fieldDomB'_of_fieldDomB p256Mul_fieldDom (by norm_num)

/-- The square at the P-256 base prime is in `fieldDomB'`. -/
theorem p256Sqr_fieldDom' : fieldDomB' p256SqrTE (fieldAbi 1 4) = true :=
  fieldDomB'_of_fieldDomB p256Sqr_fieldDom (by norm_num)

/-- The sum at the P-256 base prime is in `fieldDomB'`. -/
theorem p256Add_fieldDom' : fieldDomB' p256AddTE (fieldAbi 2 4) = true :=
  fieldDomB'_of_fieldDomB p256Add_fieldDom (by norm_num)

/-- The difference at the P-256 base prime is in `fieldDomB'`. -/
theorem p256Sub_fieldDom' : fieldDomB' p256SubTE (fieldAbi 2 4) = true :=
  fieldDomB'_of_fieldDomB p256Sub_fieldDom (by norm_num)

/-- The product at the secp256k1 base prime is in `fieldDomB'`. -/
theorem secp256k1Mul_fieldDom' : fieldDomB' secp256k1MulTE (fieldAbi 2 4) = true :=
  fieldDomB'_of_fieldDomB secp256k1Mul_fieldDom (by norm_num)

/-- The square at the secp256k1 base prime is in `fieldDomB'`. -/
theorem secp256k1Sqr_fieldDom' : fieldDomB' secp256k1SqrTE (fieldAbi 1 4) = true :=
  fieldDomB'_of_fieldDomB secp256k1Sqr_fieldDom (by norm_num)

/-- The sum at the secp256k1 base prime is in `fieldDomB'`. -/
theorem secp256k1Add_fieldDom' : fieldDomB' secp256k1AddTE (fieldAbi 2 4) = true :=
  fieldDomB'_of_fieldDomB secp256k1Add_fieldDom (by norm_num)

/-- The difference at the secp256k1 base prime is in `fieldDomB'`. -/
theorem secp256k1Sub_fieldDom' : fieldDomB' secp256k1SubTE (fieldAbi 2 4) = true :=
  fieldDomB'_of_fieldDomB secp256k1Sub_fieldDom (by norm_num)

/-- The product at the P-384 base prime is in `fieldDomB'`. -/
theorem p384Mul_fieldDom' : fieldDomB' p384MulTE (fieldAbi 2 6) = true :=
  fieldDomB'_of_fieldDomB p384Mul_fieldDom (by norm_num)

/-- The square at the P-384 base prime is in `fieldDomB'`. -/
theorem p384Sqr_fieldDom' : fieldDomB' p384SqrTE (fieldAbi 1 6) = true :=
  fieldDomB'_of_fieldDomB p384Sqr_fieldDom (by norm_num)

/-- The sum at the P-384 base prime is in `fieldDomB'`. -/
theorem p384Add_fieldDom' : fieldDomB' p384AddTE (fieldAbi 2 6) = true :=
  fieldDomB'_of_fieldDomB p384Add_fieldDom (by norm_num)

/-- The difference at the P-384 base prime is in `fieldDomB'`. -/
theorem p384Sub_fieldDom' : fieldDomB' p384SubTE (fieldAbi 2 6) = true :=
  fieldDomB'_of_fieldDomB p384Sub_fieldDom (by norm_num)

/-- The product at the BN254 base prime is in `fieldDomB'`. -/
theorem bn254Mul_fieldDom' : fieldDomB' bn254MulTE (fieldAbi 2 4) = true :=
  fieldDomB'_of_fieldDomB bn254Mul_fieldDom (by norm_num)

/-- The square at the BN254 base prime is in `fieldDomB'`. -/
theorem bn254Sqr_fieldDom' : fieldDomB' bn254SqrTE (fieldAbi 1 4) = true :=
  fieldDomB'_of_fieldDomB bn254Sqr_fieldDom (by norm_num)

/-- The sum at the BN254 base prime is in `fieldDomB'`. -/
theorem bn254Add_fieldDom' : fieldDomB' bn254AddTE (fieldAbi 2 4) = true :=
  fieldDomB'_of_fieldDomB bn254Add_fieldDom (by norm_num)

/-- The difference at the BN254 base prime is in `fieldDomB'`. -/
theorem bn254Sub_fieldDom' : fieldDomB' bn254SubTE (fieldAbi 2 4) = true :=
  fieldDomB'_of_fieldDomB bn254Sub_fieldDom (by norm_num)

/-- The product at the BLS12-381 base prime is in `fieldDomB'`. -/
theorem bls12381Mul_fieldDom' : fieldDomB' bls12381MulTE (fieldAbi 2 6) = true :=
  fieldDomB'_of_fieldDomB bls12381Mul_fieldDom (by norm_num)

/-- The square at the BLS12-381 base prime is in `fieldDomB'`. -/
theorem bls12381Sqr_fieldDom' : fieldDomB' bls12381SqrTE (fieldAbi 1 6) = true :=
  fieldDomB'_of_fieldDomB bls12381Sqr_fieldDom (by norm_num)

/-- The sum at the BLS12-381 base prime is in `fieldDomB'`. -/
theorem bls12381Add_fieldDom' : fieldDomB' bls12381AddTE (fieldAbi 2 6) = true :=
  fieldDomB'_of_fieldDomB bls12381Add_fieldDom (by norm_num)

/-- The difference at the BLS12-381 base prime is in `fieldDomB'`. -/
theorem bls12381Sub_fieldDom' : fieldDomB' bls12381SubTE (fieldAbi 2 6) = true :=
  fieldDomB'_of_fieldDomB bls12381Sub_fieldDom (by norm_num)

end Rows

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldDomComplete
