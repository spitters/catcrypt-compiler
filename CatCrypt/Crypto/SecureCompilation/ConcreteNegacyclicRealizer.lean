/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.ConcreteNttRealizer
public import CatCrypt.Crypto.SecureCompilation.NegacyclicEmitRealization
public import CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttInstances

/-!
# A CONCRETE NEGACYCLIC NTT-multiply realizer: round-trip-verified encoding, KAT-free

This is the **negacyclic** counterpart of `ConcreteNttRealizer.lean` (the cyclic
better-than-KAT for ML-KEM).  The negacyclic seam (`NegacyclicEmitRealization`)
discharges the ML-DSA NTT-multiply realization down to a leaf-realization
predicate (`NttNegaKernelRealizes`) that, at the ML-DSA parameters, is an
externally-checked **KAT** hypothesis ("the emitted negacyclic kernel's leaf
bytes decode to the negacyclic convolution"); its non-vacuity witness
(`nttNegaKernelRealizes_canonical`) exhibits a concrete `LeafSpec` only
**parametrically** over an abstract `encode`/`decode` pair with a *hypothesised*
section.

This module makes that section **concrete and proved** for ML-DSA, so the
negacyclic realization holds **unconditionally** for a spec-computing realizer.

## The 3-byte codec — ML-DSA's modulus does not fit in 2 bytes

`ConcreteNttRealizer`'s codec lays out **two** little-endian bytes per
coefficient, sufficient whenever `q < 2^16`.  That assumption is **false** for
ML-DSA: `q = 8380417 ≈ 2^23`, so two bytes cannot hold a coefficient.  ML-DSA
coefficients need **three** bytes (`8380417 < 2^24`), matching the compiler's own
storage width `(TPolyMod 8380417 256).storageBytes = 256 · 3 = 768`
(`⌈(log₂ q + 1)/8⌉ = ⌈23/8⌉ = 3` bytes per coefficient).  We therefore define a
fresh **three**-bytes-per-coefficient codec `encodeP3`/`decodeP3` (little-endian:
bytes `3i`, `3i+1`, `3i+2`) and prove its round-trip `decodeP3_encodeP3` for all
inputs whenever `q < 2^24`, mirroring `ConcreteNttRealizer.decodeP_encodeP` with
three bytes and `omega`.

## What this proves and what it does NOT

* **Proved (unconditional Lean theorem):** there is a *concrete* negacyclic leaf
  realizer (`negaConvLeafSpecP3`) and a *concrete*, round-trip-verified 3-byte
  encoding (`encodeP3`/`decodeP3`, `decodeP3_encodeP3`) under which the full
  negacyclic NTT-multiply realization holds for **all** inputs — strictly
  stronger than *assuming* a KAT, because the byte-level
  decode-equals-negacyclic-convolution fact is a theorem here, not a test vector.
* **NOT proved (the remaining residual):** that the *jasmin-emitted machine
  bytes* of the real `ntt_poly_mul_8380417_256` kernel equal this realizer.
  That equality — actual emitted assembly ≡ `negaConvLeafSpecP3` — is the
  owned-machine-code route and is a separate follow-up.  This file removes the
  *encoding* KAT (`decode ∘ encode = id`); it does **not** remove the
  *machine-code* obligation.

## References
* NIST FIPS 204 (ML-DSA)
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.ConcreteNegacyclicRealizer

open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.NegacyclicEmitRealization
open CatCrypt.Crypto.Optimizer.Lattice.NTTMultiplyCorrectGeneric
open CatCrypt.Crypto.Optimizer.Lattice.NegacyclicTransformGeneric
open CatCrypt.Crypto.Optimizer.Lattice.NegacyclicMultiplyCorrect
open CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttInstances
open CatCrypt.Crypto.Optimizer.Lattice.ConcreteNttRoots

/-! ## §1  The concrete, round-trip-verified 3-byte encoding over `.TPolyMod q n`

`RustVal (.TPolyMod q n) = JArray (.TPolyMod q n).storageBytes`, a byte
array.  For `q < 2^24` each coefficient fits in three bytes; we lay them out
little-endian, three bytes per coefficient.  The decode reads the three bytes
back as a `ZMod q`.  The round-trip is a per-coefficient `Nat`-arithmetic fact. -/

/-- Byte width per coefficient used by our concrete ML-DSA layout: three bytes
    (little-endian), sufficient whenever `q < 2^24`. -/
def coeffBytes3 : ℕ := 3

/-- The concrete carrier for a length-`n` coefficient vector mod `q`:
    `n` coefficients laid out three bytes each, little-endian.  This is a *real*
    `Fin (n * 3) → BitVec 8` byte array. -/
abbrev PolyBytes3 (n : ℕ) : Type := Fin (n * coeffBytes3) → BitVec 8

/-- Encode a coefficient vector into `n·3` little-endian bytes: byte `3i` is the
    low byte of `(x i).val`, byte `3i+1` the middle byte, byte `3i+2` the high
    byte. -/
def encodeP3 {q n : ℕ} [NeZero q] (x : Fin n → ZMod q) : PolyBytes3 n :=
  fun b =>
    let i : ℕ := b.val / coeffBytes3
    let lane : ℕ := b.val % coeffBytes3
    if h : i < n then
      let v : ℕ := (x ⟨i, h⟩).val
      if lane = 0 then BitVec.ofNat 8 (v % 256)
      else if lane = 1 then BitVec.ofNat 8 ((v / 256) % 256)
      else BitVec.ofNat 8 (v / 65536)
    else 0

/-- Decode `n·3` little-endian bytes back into a coefficient vector:
    `coeff i = byte(3i) + 256 · byte(3i+1) + 65536 · byte(3i+2)  (mod q)`. -/
def decodeP3 {q n : ℕ} [NeZero q] (a : PolyBytes3 n) : Fin n → ZMod q :=
  fun i =>
    let lo : ℕ := (a ⟨i.val * coeffBytes3, by
      have hlt := i.isLt; unfold coeffBytes3; omega⟩).toNat
    let mid : ℕ := (a ⟨i.val * coeffBytes3 + 1, by
      have hlt := i.isLt; unfold coeffBytes3; omega⟩).toNat
    let hi : ℕ := (a ⟨i.val * coeffBytes3 + 2, by
      have hlt := i.isLt; unfold coeffBytes3; omega⟩).toNat
    ((lo + 256 * mid + 65536 * hi : ℕ) : ZMod q)

/-- **The verified round-trip (the crux).**  For any modulus `q < 2^24`, decoding
    the concrete little-endian 3-byte encoding of a coefficient vector returns the
    vector unchanged — for **all** inputs.  This is the byte-level fact a KAT would
    merely *assert*; here it is a theorem. -/
theorem decodeP3_encodeP3 {q n : ℕ} [NeZero q] (hq : q < 16777216)
    (x : Fin n → ZMod q) : decodeP3 (encodeP3 x) = x := by
  funext i
  have hval : (x i).val < 16777216 := lt_of_lt_of_le (ZMod.val_lt (x i)) (le_of_lt hq)
  simp only [decodeP3]
  -- The low byte: lane 0, value `(x i).val % 256`.
  have hlo : (encodeP3 x ⟨i.val * coeffBytes3, by have := i.isLt; unfold coeffBytes3; omega⟩).toNat
      = (x i).val % 256 := by
    simp only [encodeP3]
    have hi' : i.val * coeffBytes3 / coeffBytes3 = i.val := by
      unfold coeffBytes3; omega
    have hlane : i.val * coeffBytes3 % coeffBytes3 = 0 := by
      unfold coeffBytes3; omega
    rw [hi', hlane]
    rw [dif_pos i.isLt, if_pos rfl, Fin.eta, BitVec.toNat_ofNat]
    have : (x i).val % 256 < 256 := Nat.mod_lt _ (by decide)
    omega
  -- The middle byte: lane 1, value `((x i).val / 256) % 256`.
  have hmid : (encodeP3 x ⟨i.val * coeffBytes3 + 1, by have := i.isLt; unfold coeffBytes3; omega⟩).toNat
      = ((x i).val / 256) % 256 := by
    simp only [encodeP3]
    have hi' : (i.val * coeffBytes3 + 1) / coeffBytes3 = i.val := by
      unfold coeffBytes3; omega
    have hlane : (i.val * coeffBytes3 + 1) % coeffBytes3 = 1 := by
      unfold coeffBytes3; omega
    rw [hi', hlane]
    rw [dif_pos i.isLt, if_neg (by decide : (1 : ℕ) ≠ 0), if_pos rfl, Fin.eta, BitVec.toNat_ofNat]
    have : ((x i).val / 256) % 256 < 256 := Nat.mod_lt _ (by decide)
    omega
  -- The high byte: lane 2, value `(x i).val / 65536`.
  have hhi : (encodeP3 x ⟨i.val * coeffBytes3 + 2, by have := i.isLt; unfold coeffBytes3; omega⟩).toNat
      = (x i).val / 65536 := by
    simp only [encodeP3]
    have hi' : (i.val * coeffBytes3 + 2) / coeffBytes3 = i.val := by
      unfold coeffBytes3; omega
    have hlane : (i.val * coeffBytes3 + 2) % coeffBytes3 = 2 := by
      unfold coeffBytes3; omega
    rw [hi', hlane]
    rw [dif_pos i.isLt, if_neg (by decide : (2 : ℕ) ≠ 0), if_neg (by decide : (2 : ℕ) ≠ 1),
      Fin.eta, BitVec.toNat_ofNat]
    have : (x i).val / 65536 < 256 := by omega
    omega
  rw [hlo, hmid, hhi]
  have hrecon :
      (x i).val % 256 + 256 * (((x i).val / 256) % 256) + 65536 * ((x i).val / 65536)
        = (x i).val := by omega
  rw [hrecon, ZMod.natCast_val, ZMod.cast_id]

/-! ## §2  Negacyclic realization predicates over the `.TPolyMod q n` carrier

The negacyclic seam's `NttNegaKernelRealizes`/`NttNegaEmitRealizes` hardcode the
`.TFp` carrier (48 bytes), which is far too small for an honest round-trip on
ML-DSA's `Fin 256 → ZMod 8380417` vector (a faithful injection needs
`≥ 256 · 23 = 5888` bits, while `.TFp` has `384`).  As in `ConcreteNttRealizer`,
we re-state the two predicates over `RustVal (.TPolyMod q n)` — the carrier the
compiler actually uses for ML-DSA polynomials, with `768` bytes of room — and
re-run the identical commuting-square discharge.  Only the carrier TowerType
differs; the negacyclic-multiply math (`nttNegaMul_eq_negaConv`) is reused
verbatim. -/

/-- The `.TPolyMod`-carrier negacyclic kernel-realization predicate: the
    leaf-call value decodes to the length-`n` **negacyclic convolution**.
    Identical in shape to `NegacyclicEmitRealization.NttNegaKernelRealizes`, but
    over the `.TPolyMod q n` byte carrier. -/
def NttNegaKernelRealizesP (q n : ℕ) [NeZero q] [NeZero n] [Fact (Nat.Prime q)] (ψ : ZMod q)
    (decode : RustVal (.TPolyMod q n) → (Fin n → ZMod q))
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal (.TPolyMod q n)),
    decode
        (leafSpec.call leaf (.TPolyMod q n) [.TPolyMod q n, .TPolyMod q n] oldDest
          [⟨.TPolyMod q n, aVal⟩, ⟨.TPolyMod q n, bVal⟩])
      = negaConv ψ (decode aVal) (decode bVal)

/-- The `.TPolyMod`-carrier full negacyclic NTT-multiply realization predicate:
    the leaf-call value decodes to `nttNegaMul ψ …`. -/
def NttNegaEmitRealizesP (q n : ℕ) [NeZero q] [NeZero n] [Fact (Nat.Prime q)] (ψ : ZMod q)
    (decode : RustVal (.TPolyMod q n) → (Fin n → ZMod q))
    (leaf : String) (leafSpec : LeafSpec) : Prop :=
  ∀ (aVal bVal oldDest : RustVal (.TPolyMod q n)),
    decode
        (leafSpec.call leaf (.TPolyMod q n) [.TPolyMod q n, .TPolyMod q n] oldDest
          [⟨.TPolyMod q n, aVal⟩, ⟨.TPolyMod q n, bVal⟩])
      = nttNegaMul ψ (decode aVal) (decode bVal)

/-- **Commuting-square discharge over `.TPolyMod`.**  Identical to
    `nttNegaEmitRealizes_of_negaConv`, re-run on the `.TPolyMod` carrier: a
    primitive `n`-th root `ω = ψ²` with `(n : ZMod q) ≠ 0` rewrites
    `nttNegaMul = negaConv` (the proven `nttNegaMul_eq_negaConv`), lifting the
    kernel realization to the full negacyclic NTT-multiply realization. -/
theorem nttNegaEmitRealizesP_of_negaConv {q n : ℕ} [NeZero q] [NeZero n]
    [Fact (Nat.Prime q)] {ψ : ZMod q}
    (decode : RustVal (.TPolyMod q n) → (Fin n → ZMod q))
    (leaf : String) (leafSpec : LeafSpec)
    (hω : IsPrimitiveRoot (ψ ^ 2) n) (hn : (n : ZMod q) ≠ 0)
    (hker : NttNegaKernelRealizesP q n ψ decode leaf leafSpec) :
    NttNegaEmitRealizesP q n ψ decode leaf leafSpec := by
  intro aVal bVal oldDest
  rw [hker aVal bVal oldDest, nttNegaMul_eq_negaConv hω hn]

/-! ## §3  The concrete, spec-computing negacyclic realizer (no abstract section)

`negaConvLeafSpecP3` is the canonical negacyclic realizer wired to the
**concrete** `encodeP3`/`decodeP3` of §1: at the NTT leaf it decodes both
polynomial arguments, computes their negacyclic convolution `negaConv ψ`, and
re-encodes; off-leaf it returns `oldDest`.  Because the round-trip
`decodeP3_encodeP3` is a *theorem*, `NttNegaKernelRealizesP` holds
**unconditionally** — there is no `hsection` hypothesis to assume.

`hwidth : (.TPolyMod q n).storageBytes = n * coeffBytes3` makes `RustVal
(.TPolyMod q n)` equal to `PolyBytes3 n`, letting the byte-level
`encodeP3`/`decodeP3` serve as the carrier codec.  For ML-DSA (`q = 8380417`,
`n = 256`) it holds by `decide` (`storageBytes = 256 · 3 = 768`). -/

/-- The decoder on the `.TPolyMod q n` carrier, obtained from the byte-level
    `decodeP3` through the width equality `hwidth`. -/
def decodeTPoly3 {q n : ℕ} [NeZero q]
    (hwidth : (TowerType.TPolyMod q n).storageBytes = n * coeffBytes3)
    (a : RustVal (.TPolyMod q n)) : Fin n → ZMod q :=
  decodeP3 (cast (congrArg CatCrypt.Crypto.Jasmin.JArray hwidth) a)

/-- The encoder on the `.TPolyMod q n` carrier, obtained from the byte-level
    `encodeP3` through the width equality `hwidth`. -/
def encodeTPoly3 {q n : ℕ} [NeZero q]
    (hwidth : (TowerType.TPolyMod q n).storageBytes = n * coeffBytes3)
    (x : Fin n → ZMod q) : RustVal (.TPolyMod q n) :=
  cast (congrArg CatCrypt.Crypto.Jasmin.JArray hwidth.symm) (encodeP3 x)

/-- Round-trip on the carrier: `decodeTPoly3 ∘ encodeTPoly3 = id`, inherited from
    `decodeP3_encodeP3` by transporting along `hwidth`. -/
theorem decodeTPoly3_encodeTPoly3 {q n : ℕ} [NeZero q] (hq : q < 16777216)
    (hwidth : (TowerType.TPolyMod q n).storageBytes = n * coeffBytes3)
    (x : Fin n → ZMod q) : decodeTPoly3 hwidth (encodeTPoly3 hwidth x) = x := by
  unfold decodeTPoly3 encodeTPoly3
  exact (congrArg decodeP3 (cast_cast _ _ _)).trans (decodeP3_encodeP3 hq x)

/-- The concrete negacyclic-convolution `CallSpec` over the `.TPolyMod q n`
    carrier, wired to the round-trip-verified `encodeTPoly3`/`decodeTPoly3`. -/
noncomputable def negaConvCallSpecP3 {q n : ℕ} [NeZero q] [NeZero n] [Fact (Nat.Prime q)] (ψ : ZMod q)
    (hwidth : (TowerType.TPolyMod q n).storageBytes = n * coeffBytes3)
    (leaf : String) : CallSpec :=
  fun fname _dt _argTs oldDest args =>
    if fname = leaf then
      let pick : (Σ t : TowerType, RustVal t) → (Fin n → ZMod q) := fun a =>
        if ht : a.1 = TowerType.TPolyMod q n then decodeTPoly3 hwidth (ht ▸ a.2) else 0
      match args with
      | a :: b :: _ =>
          if hd : _dt = TowerType.TPolyMod q n then
            hd ▸ encodeTPoly3 hwidth (negaConv ψ (pick a) (pick b))
          else oldDest
      | _ => oldDest
    else oldDest

/-- The concrete negacyclic realizer `LeafSpec`. -/
noncomputable def negaConvLeafSpecP3 {q n : ℕ} [NeZero q] [NeZero n] [Fact (Nat.Prime q)] (ψ : ZMod q)
    (hwidth : (TowerType.TPolyMod q n).storageBytes = n * coeffBytes3)
    (leaf : String) (limbStore : LimbStoreSpec) : LeafSpec :=
  { call := negaConvCallSpecP3 ψ hwidth leaf, limbStore := limbStore }

/-- **Unconditional negacyclic kernel realization (no KAT, no abstract section).**
    The concrete realizer `negaConvLeafSpecP3` decodes its leaf-call value to the
    negacyclic convolution for **every** input — proved by the round-trip
    `decodeTPoly3_encodeTPoly3` (valid for `q < 2^24`), not assumed via a test
    vector. -/
theorem nttNegaKernelRealizesP3_concrete {q n : ℕ} [NeZero q] [NeZero n]
    [Fact (Nat.Prime q)] (ψ : ZMod q) (hq : q < 16777216)
    (hwidth : (TowerType.TPolyMod q n).storageBytes = n * coeffBytes3)
    (leaf : String) (limbStore : LimbStoreSpec) :
    NttNegaKernelRealizesP q n ψ (decodeTPoly3 hwidth) leaf
      (negaConvLeafSpecP3 ψ hwidth leaf limbStore) := by
  intro aVal bVal oldDest
  show decodeTPoly3 hwidth (negaConvCallSpecP3 ψ hwidth leaf leaf (.TPolyMod q n)
      [.TPolyMod q n, .TPolyMod q n] oldDest
      [⟨.TPolyMod q n, aVal⟩, ⟨.TPolyMod q n, bVal⟩])
    = negaConv ψ (decodeTPoly3 hwidth aVal) (decodeTPoly3 hwidth bVal)
  simp only [negaConvCallSpecP3, ite_true, dite_true]
  rw [decodeTPoly3_encodeTPoly3 hq]

/-! ## §4  The unconditional ML-DSA negacyclic realization (the deliverable)

Instantiating §3 at the ML-DSA parameters (`q = 8380417`, `n = 256`, twist root
`ψ = 1753`, inner root `ω = ψ² = 1753²`) and discharging the commuting square
with the **proven** `isPrimitiveRoot_1753sq_256` and `n_ne_zero_8380417` gives the
full negacyclic NTT-multiply realization with **no** KAT and **no** abstract
section hypothesis — the realization is proved for all inputs of the concrete,
spec-computing realizer with its round-trip-verified 3-byte encoding. -/

/-- **ML-DSA negacyclic NTT-multiply realization — UNCONDITIONAL.**  For the
    concrete realizer `negaConvLeafSpecP3 1753 …` and the concrete,
    round-trip-verified 3-byte `decodeP3`/`encodeP3` encoding, the full negacyclic
    NTT-multiply realization `NttNegaEmitRealizesP 8380417 256 1753 …` holds for
    every input.  No KAT hypothesis and no abstract `decode ∘ encode = id`
    assumption remain: the byte-level decode-equals-negacyclic-convolution fact is
    the theorem `decodeP3_encodeP3`, and the twist·cyclic·untwist =
    negacyclic-convolution fact is the proven `isPrimitiveRoot_1753sq_256` +
    `n_ne_zero_8380417` via the commuting square.

    What is **not** proved here: that the jasmin-emitted machine bytes of the real
    `ntt_poly_mul_8380417_256` kernel equal `negaConvLeafSpecP3` (the
    owned-machine-code route — a separate follow-up). -/
theorem mldsa_nttNegaEmitRealizes_concrete (limbStore : LimbStoreSpec) :
    NttNegaEmitRealizesP 8380417 256 (1753 : ZMod 8380417)
      (decodeTPoly3 (q := 8380417) (n := 256) (by decide))
      "ntt_poly_mul_8380417_256"
      (negaConvLeafSpecP3 (q := 8380417) (n := 256) (1753 : ZMod 8380417) (by decide)
        "ntt_poly_mul_8380417_256" limbStore) :=
  nttNegaEmitRealizesP_of_negaConv (decodeTPoly3 (q := 8380417) (n := 256) (by decide))
    "ntt_poly_mul_8380417_256" _
    isPrimitiveRoot_1753sq_256 n_ne_zero_8380417
    (nttNegaKernelRealizesP3_concrete (1753 : ZMod 8380417) (by decide) (by decide)
      "ntt_poly_mul_8380417_256" limbStore)

end CatCrypt.Crypto.SecureCompilation.ConcreteNegacyclicRealizer
